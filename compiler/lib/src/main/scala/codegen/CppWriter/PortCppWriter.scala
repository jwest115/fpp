package fpp.compiler.codegen

import fpp.compiler.analysis._
import fpp.compiler.ast._
import fpp.compiler.util._

case class PortCppWriter (
  s: CppWriterState,
  aNode: Ast.Annotated[AstNode[Ast.DefPort]]
) extends CppWriterLineUtils {

  private val node = aNode._2

  private val data = node.data

  private val symbol = Symbol.Port(aNode)

  private val name = s.getName(symbol)

  private val fileName = ComputeCppFiles.FileNames.getPort(name)

  private val namespaceIdentList = s.getNamespaceIdentList(symbol)

  private val strCppWriter = StringCppWriter(s)

  private val strNamespace = PortCppWriter.getPortStringNamespace(name)

  private val params = data.params

  // Map from param name to param type
  private val paramTypeMap = params.map((_, node, _) => {
    (node.data.name, s.a.typeMap(node.data.typeName.id))
  }).toMap

  // List of tuples (name, type) for each string param
  private val strParamList = paramTypeMap.map((n, t) => t match {
    case t: Type.String => Some((n, t))
    case _ => None
  }).filter(_.isDefined).map(_.get).toList

  // Map from string size to list of names of string of that size
  private val strNameMap = strParamList.groupBy((_, t) => {
    strCppWriter.getSize(t)
  }).map((size, l) => (size, l.map(_._1)))

  // List of tuples (name, C++ type, kind) for each param
  private val paramList = params.map((_, node, _) => {
    val n = node.data.name
    val k = node.data.kind

    (n, writeCppTypeName(paramTypeMap(n), s, List(strNamespace)), k)
  })

  // Port params as CppDoc Function Params
  private val functionParams: List[CppDoc.Function.Param] =
    writeFormalParamList(params, s, List(strNamespace))

  /** Return type as a C++ type */
  val returnType: String = data.returnType match {
      case Some(node) => writeCppTypeName(
        s.a.typeMap(node.id),
        s,
        List(strNamespace)
      )
      case None => "void"
    }

  private def writeIncludeDirectives: List[String] = {
    val Right(a) = UsedSymbols.defPortAnnotatedNode(s.a, aNode)
    s.writeIncludeDirectives(a.usedSymbolSet)
  }

  def write: CppDoc = {
    val includeGuard = s.includeGuardFromQualifiedName(symbol, fileName)
    CppWriter.createCppDoc(
      s"$name port",
      fileName,
      includeGuard,
      getMembers,
      s.toolName
    )
  }

  private def getMembers: List[CppDoc.Member] = {
    val hppIncludes = getHppIncludes
    val cppIncludes = getCppIncludes
    val annotation = AnnotationCppWriter.asStringOpt(aNode) match {
      case Some(value) => s"\n$value"
      case None => ""
    }
    val portBufferClass = data.returnType match {
      case Some(_) => Nil
      case None => List(
        CppDoc.Member.Lines(
          CppDoc.Lines(
            Line.blank :: wrapInAnonymousNamespace(getPortBufferClass),
            CppDoc.Lines.Cpp
          )
        )
      )
    }
    val classes = List(
      getStringClasses,
      getStringTypedefs,
      portBufferClass,
      List(
        CppDoc.Member.Class(
          CppDoc.Class(
            Some(s"Input $name port" + annotation),
            PortCppWriter.inputPortName(name),
            Some("public Fw::InputPortBase"),
            getInputPortClassMembers
          )
        ),
        CppDoc.Member.Class(
          CppDoc.Class(
            Some(s"Output $name port" + annotation),
            PortCppWriter.outputPortName(name),
            Some("public Fw::OutputPortBase"),
            getOutputPortClassMembers
          )
        ),
      )
    ).flatten
    List(
      List(hppIncludes, cppIncludes),
      CppWriter.wrapInNamespaces(namespaceIdentList, classes)
    ).flatten
  }

  private def getHppIncludes: CppDoc.Member = {
    val systemHeaders = List(
      "cstdio",
      "cstring",
    ).map(CppWriter.systemHeaderString).map(line)
    val serializableHeader = data.returnType match {
      case Some(_) => Nil
      case None => List("Fw/Types/Serializable.hpp")
    }
    val standardHeaders = (
      List(
        "FpConfig.hpp",
        "Fw/Comp/PassiveComponentBase.hpp",
        "Fw/Port/InputPortBase.hpp",
        "Fw/Port/OutputPortBase.hpp",
        "Fw/Types/StringType.hpp",
      ) ++ serializableHeader
    ).map(CppWriter.headerString)
    val symbolHeaders = writeIncludeDirectives
    val userHeaders = (standardHeaders ++ symbolHeaders).sorted.map(line)
    CppWriter.linesMember(
      List(
        Line.blank :: systemHeaders,
        Line.blank :: userHeaders
      ).flatten
    )
  }

  private def getCppIncludes: CppDoc.Member = {
    val userHeaders = List(
      "Fw/Types/Assert.hpp",
      "Fw/Types/StringUtils.hpp",
      s"${s.getRelativePath(fileName).toString}.hpp"
    ).sorted.map(CppWriter.headerString).map(line)
    CppWriter.linesMember(
      Line.blank :: userHeaders,
      CppDoc.Lines.Cpp
    )
  }

  private def getStringTypedefs: List[CppDoc.Member] = {
    if strParamList.isEmpty then Nil
    else List(
      CppDoc.Member.Lines(
        CppDoc.Lines(
          List(
            CppDocWriter.writeBannerComment(
              "String types for backwards compatibility"
            ),
            Line.blank ::
              strNameMap.flatMap((size, l) => {
                l.map(strName => line(
                  s"typedef ${
                    strCppWriter.getQualifiedClassName(size, List(strNamespace))
                  } ${strName}String;"
                ))
              }).toList
          ).flatten
        )
      )
    )
  }

  private def getStringClasses: List[CppDoc.Member] = {
    val strTypes = paramTypeMap.map((_, t) => t match {
      case t: Type.String => Some(t)
      case _ => None
    }).filter(_.isDefined).map(_.get).toList
    strTypes match {
      case Nil => Nil
      case l => CppWriter.wrapInNamespaces(
        List(strNamespace),
        strCppWriter.write(l)
      )
    }
  }

  private def getPortBufferClass: List[Line] = {
    val privateMemberVariables =
      if params.isEmpty then Nil
      else
        CppDocHppWriter.writeAccessTag("private") ++
          lines(s"\nU8 m_buff[${PortCppWriter.inputPortName(name)}::SERIALIZED_SIZE];")
    val buffAddr =
      if params.isEmpty then "nullptr" else "m_buff"

    List(
      CppDocWriter.writeBannerComment("Port buffer class"),
      Line.blank :: lines(s"class ${name}PortBuffer : public Fw::SerializeBufferBase {"),
      List(
        CppDocHppWriter.writeAccessTag("public"),
        Line.blank :: lines(
          s"""|NATIVE_UINT_TYPE getBuffCapacity() const {
              |  return ${PortCppWriter.inputPortName(name)}::SERIALIZED_SIZE;
              |}
              |
              |U8* getBuffAddr() {
              |  return $buffAddr;
              |}
              |
              |const U8* getBuffAddr() const {
              |  return $buffAddr;
              |}
              |"""
        ),
        privateMemberVariables
      ).flatten.map(indentIn).map(indentIn),
      Line.blank :: lines("};"),
      List(Line.blank)
    ).flatten
  }

  private def getInputPortClassMembers: List[CppDoc.Class.Member] = {
    List(
      getInputPortConstantMembers,
      getInputPortTypeMembers,
      getInputPortFunctionMembers,
      getInputPortVariableMembers
    ).flatten
  }

  private def getInputPortConstantMembers: List[CppDoc.Class.Member] = {
    List(
      CppDoc.Class.Member.Lines(
        CppDoc.Lines(
          List(
            CppDocHppWriter.writeAccessTag("public"),
            CppDocWriter.writeBannerComment("Constants"),
            addBlankPrefix(
              wrapInEnum(
                List(
                  lines("//! The size of the serial representations of the port arguments"),
                  if params.isEmpty then
                    lines("SERIALIZED_SIZE = 0")
                  else
                    line("SERIALIZED_SIZE =") ::
                      lines(paramList.map((n, tn, _) =>
                        s.getSerializedSizeExpr(paramTypeMap(n), tn)
                      ).mkString(" +\n")).map(indentIn)
                ).flatten
              )
            )
          ).flatten
        )
      )
    )
  }

  private def getInputPortTypeMembers: List[CppDoc.Class.Member] = {
    val compFuncParams = 
      line("Fw::PassiveComponentBase* callComp,") ::
        (if params.isEmpty then
          lines("NATIVE_INT_TYPE portNum")
        else
          line("NATIVE_INT_TYPE portNum,") ::
            lines(params.map(p => {
              s"${writeFormalParam(p._2.data, s, List(strNamespace))} ${p._2.data.name}"
            }).mkString(",\n")))

    List(
      CppDoc.Class.Member.Lines(
        CppDoc.Lines(
          List(
            CppDocHppWriter.writeAccessTag("public"),
            CppDocWriter.writeBannerComment("Types"),
            Line.blank :: lines("//! The port callback function type"),
            lines(s"typedef $returnType (*CompFuncPtr)("),
            compFuncParams.map(indentIn),
            lines(");")
          ).flatten
        )
      )
    )
  }

  private def getInputPortFunctionMembers: List[CppDoc.Class.Member] = {
    val paramNames = paramList.map((n, _, _) => s", $n").mkString("")
    val invokeSerialBody = data.returnType match {
      case Some(_) => lines(
        """|// For ports with a return type, invokeSerial is not used
           |(void) _buffer;
           |
           |FW_ASSERT(0);
           |return Fw::FW_SERIALIZE_OK;
           |"""
      )
      case None =>
        (if params.isEmpty then line("(void) _buffer;")
        else line("Fw::SerializeStatus _status;")) ::
          lines(
            """|
               |#if FW_PORT_SERIALIZATION == 1
               |this->trace();
               |#endif
               |
               |FW_ASSERT(this->m_comp);
               |FW_ASSERT(this->m_func);
               |"""
          ) ++
          paramList.flatMap((n, tn, _) => {
            lines(
              s"""|
                  |$tn $n;
                  |_status = _buffer.deserialize($n);
                  |if (_status != Fw::FW_SERIALIZE_OK) {
                  |  return _status;
                  |}
                  |"""
            )
          }) ++
          lines(
            s"""|
                |this->m_func(this->m_comp, this->m_portNum${paramNames});
                |
                |return Fw::FW_SERIALIZE_OK;
                |"""
          )
    }

    List(
      CppDoc.Class.Member.Lines(
        CppDoc.Lines(
          CppDocHppWriter.writeAccessTag("public")
        )
      ),
      CppDoc.Class.Member.Lines(
        CppDoc.Lines(
          CppDocWriter.writeBannerComment("Input Port Member functions"),
          CppDoc.Lines.Both
        )
      ),
      CppDoc.Class.Member.Constructor(
        CppDoc.Class.Constructor(
          Some("Constructor"),
          Nil,
          List("Fw::InputPortBase()", "m_func(nullptr)"),
          Nil
        )
      ),
      CppDoc.Class.Member.Function(
        CppDoc.Function(
          Some("Initialization function"),
          "init",
          Nil,
          CppDoc.Type("void"),
          lines("Fw::InputPortBase::init();")
        )
      ),
      CppDoc.Class.Member.Function(
        CppDoc.Function(
          Some("Register a component"),
          "addCallComp",
          List(
            CppDoc.Function.Param(
              CppDoc.Type("Fw::PassiveComponentBase*"),
              "callComp",
              Some("The containing component")
            ),
            CppDoc.Function.Param(
              CppDoc.Type("CompFuncPtr"),
              "funcPtr",
              Some("The port callback function")
            )
          ),
          CppDoc.Type("void"),
          lines(
            """|FW_ASSERT(callComp);
               |FW_ASSERT(funcPtr);
               |
               |this->m_comp = callComp;
               |this->m_func = funcPtr;
               |this->m_connObj = callComp;
               |"""
          )
        )
      ),
      CppDoc.Class.Member.Function(
        CppDoc.Function(
          Some("Invoke a port interface"),
          "invoke",
          functionParams,
          CppDoc.Type(returnType),
          lines(
            s"""|#if FW_PORT_TRACING == 1
                |this->trace();
                |#endif
                |
                |FW_ASSERT(this->m_comp);
                |FW_ASSERT(this->m_func);
                |
                |return this->m_func(this->m_comp, this->m_portNum${paramNames});
                |"""
          )
        )
      ),
      CppDoc.Class.Member.Lines(
        CppDoc.Lines(
          CppDocHppWriter.writeAccessTag("private")
        )
      ),
    ) ++
      wrapClassMembersInIfDirective(
        "\n#if FW_PORT_SERIALIZATION == 1",
        List(
          CppDoc.Class.Member.Function(
            CppDoc.Function(
              Some("Invoke the port with serialized arguments"),
              "invokeSerial",
              List(
                CppDoc.Function.Param(
                  CppDoc.Type("Fw::SerializeBufferBase&"),
                  "_buffer"
                )
              ),
              CppDoc.Type("Fw::SerializeStatus"),
              invokeSerialBody
            )
          )
        ),
      )
  }

  private def getInputPortVariableMembers: List[CppDoc.Class.Member] = {
    List(
      CppDoc.Class.Member.Lines(
        CppDoc.Lines(
          List(
            CppDocHppWriter.writeAccessTag("private"),
            CppDocWriter.writeBannerComment("Member variables"),
            Line.blank :: lines("//! The pointer to the port callback function"),
            lines("CompFuncPtr m_func;")
          ).flatten
        )
      )
    )
  }

  private def getOutputPortClassMembers: List[CppDoc.Class.Member] = {
    List(
      getOutputPortFunctionMembers,
      getOutputPortVariableMembers
    ).flatten
  }

  private def getOutputPortFunctionMembers: List[CppDoc.Class.Member] = {
    val paramNames = paramList.map(_._1).mkString(", ")
    val invokeBody = data.returnType match {
      case Some(_) => lines(
        s"return this->m_port->invoke($paramNames);"
      )
      case None => lines(
        s"""|if (this->m_port) {
            |  this->m_port->invoke($paramNames);
            |#if FW_PORT_SERIALIZATION
            |} else if (this->m_serPort) {
            |  Fw::SerializeStatus _status;
            |  ${name}PortBuffer _buffer;
            |"""
      ) ++
        paramList.flatMap((n, _, _) => {
          lines(
            s"""|
                |  _status = _buffer.serialize($n);
                |  FW_ASSERT(_status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(_status));
                |"""
          )
        }) ++
        lines(
         """|
            |  _status = this->m_serPort->invokeSerial(_buffer);
            |  FW_ASSERT(_status == Fw::FW_SERIALIZE_OK, static_cast<FwAssertArgType>(_status));
            |}
            |#else
            |}
            |#endif
            |"""
        )
    }

    List(
      CppDoc.Class.Member.Lines(
        CppDoc.Lines(
          CppDocHppWriter.writeAccessTag("public")
        )
      ),
      CppDoc.Class.Member.Lines(
        CppDoc.Lines(
          CppDocWriter.writeBannerComment("Output Port Member functions"),
          CppDoc.Lines.Both
        )
      ),
      CppDoc.Class.Member.Constructor(
        CppDoc.Class.Constructor(
          Some("Constructor"),
          Nil,
          List("Fw::OutputPortBase()", "m_port(nullptr)"),
          Nil
        )
      ),
      CppDoc.Class.Member.Function(
        CppDoc.Function(
          Some("Initialization function"),
          "init",
          Nil,
          CppDoc.Type("void"),
          lines("Fw::OutputPortBase::init();")
        )
      ),
      CppDoc.Class.Member.Function(
        CppDoc.Function(
          Some("Register an input port"),
          "addCallPort",
          List(
            CppDoc.Function.Param(
              CppDoc.Type(s"${PortCppWriter.inputPortName(name)}*"),
              "callPort",
              Some("The input port")
            )
          ),
          CppDoc.Type("void"),
          lines(
            """|FW_ASSERT(callPort);
               |
               |this->m_port = callPort;
               |this->m_connObj = callPort;
               |
               |#if FW_PORT_SERIALIZATION == 1
               |this->m_serPort = nullptr;
               |#endif
               |"""
          )
        )
      ),
      CppDoc.Class.Member.Function(
        CppDoc.Function(
          Some("Invoke a port interface"),
          "invoke",
          functionParams,
          CppDoc.Type(returnType),
          lines(
            s"""|#if FW_PORT_TRACING == 1
                |this->trace();
                |#endif
                |
                |#if FW_PORT_SERIALIZATION
                |FW_ASSERT(this->m_port || this->m_serPort);
                |#else
                |FW_ASSERT(this->m_port);
                |#endif
                |
                |"""
          ) ++
            invokeBody
        )
      )
    )
  }

  private def getOutputPortVariableMembers: List[CppDoc.Class.Member] = {
    List(
      CppDoc.Class.Member.Lines(
        CppDoc.Lines(
          List(
            CppDocHppWriter.writeAccessTag("private"),
            CppDocWriter.writeBannerComment("Member variables"),
            Line.blank :: lines("//! The pointer to the input port"),
            lines(s"${PortCppWriter.inputPortName(name)}* m_port;")
          ).flatten
        )
      )
    )
  }

}

object PortCppWriter {

  private def inputPortName(name: String) = s"Input${name}Port"

  private def outputPortName(name: String) = s"Output${name}Port"

  /** Get the name of a port type */
  def getPortName(name: String, direction: PortInstance.Direction): String =
    direction match {
      case PortInstance.Direction.Input => inputPortName(name)
      case PortInstance.Direction.Output => outputPortName(name)
    }

  /** Get the name of the port string class namespace */
  def getPortStringNamespace(name: String): String = s"${name}PortStrings"

  /** Get the names of port namespaces as a list */
  def getPortNamespaces(name: String): List[String] = List(getPortStringNamespace(name))

}
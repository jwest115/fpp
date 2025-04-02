package fpp.compiler.codegen

import fpp.compiler.analysis._
import fpp.compiler.ast._
import fpp.compiler.codegen._

/** Writes out C++ for component parameters */
case class ComponentParameters (
  s: CppWriterState,
  aNode: Ast.Annotated[AstNode[Ast.DefComponent]]
) extends ComponentCppWriterUtils(s, aNode) {

  def getConstantMembers: List[CppDoc.Class.Member] = {
    if !hasParameters then Nil
    else List(
      linesClassMember(
        List(
          Line.blank :: lines(s"//! Parameter IDs"),
          wrapInEnum(
            sortedParams.flatMap((id, param) =>
              writeEnumConstant(
                paramIdConstantName(param.getName),
                id,
                AnnotationCppWriter.asStringOpt(param.aNode),
                CppWriterUtils.Hex
              )
            )
          )
        ).flatten
      )
    )
  }

  def getPublicFunctionMembers: List[CppDoc.Class.Member] = {
    if !hasParameters then Nil
    else getLoadFunction
  }

  def getProtectedFunctionMembers: List[CppDoc.Class.Member] = {
    if !hasParameters then Nil
    else List(
      getHookFunctions,
      getGetterFunctions
    ).flatten
  }

  def getPrivateFunctionMembers: List[CppDoc.Class.Member] = {
    if !hasParameters then Nil
    else List(
      getSetters,
      getSaveFunctions
    ).flatten
  }

  def getVariableMembers: List[CppDoc.Class.Member] = {
    if !hasParameters then Nil
    else List(
      addAccessTagAndComment(
        "PRIVATE",
        "Parameter validity flags",
        sortedParams.map((_, param) =>
          linesClassMember(
            lines(
              s"""|
                  |//! True if ${param.getName} was successfully received
                  |Fw::ParamValid ${paramValidityFlagName(param.getName)};
                  |"""
            )
          )
        ),
        CppDoc.Lines.Hpp
      ),
      addAccessTagAndComment(
        "PRIVATE",
        "Parameter variables",
        sortedParams.map((_, param) => {
          val paramType = writeParamType(param.paramType, "Fw::ParamString")
          val paramVarName = paramVariableName(param.getName)
          linesClassMember(
            List.concat(
              addSeparatedPreComment(
                s"Parameter ${param.getName}",
                AnnotationCppWriter.asStringOpt(param.aNode)
              ),
              lines(s"$paramType $paramVarName;")
            )
          )
        }),
        CppDoc.Lines.Hpp
      ),
      guardedList (hasExternalParameters) (
        List(
          addAccessTagAndComment(
            "PRIVATE",
            "Parameter delegates",
            List(
              linesClassMember(
                lines(
                  s"""|
                      |//! Delegate to serialize/deserialize an externally stored parameter
                      |Fw::ParamExternalDelegate* paramDelegate;
                      |"""
                )
              )
            )
          )
        )
      ).flatten
    ).flatten
  }

  private def getLoadFunction: List[CppDoc.Class.Member] = {
    addAccessTagAndComment(
      "public",
      "Parameter loading",
      List(
        functionClassMember(
          Some(
            s"""|\\brief Load the parameters from a parameter source
                |
                |Connect the parameter first
                |"""
          ),
          "loadParameters",
          Nil,
          CppDoc.Type("void"),
          intersperseBlankLines(
            List(
              lines(
                s"""|Fw::ParamBuffer buff;
                    |Fw::SerializeStatus stat = Fw::FW_SERIALIZE_OK;
                    |FW_ASSERT(this->${portVariableName(prmGetPort.get)}[0].isConnected());
                    |
                    |FwPrmIdType _id;
                    |"""
              ),
              intersperseBlankLines(
                sortedParams.map { case (_, param) =>
                  val deserializationCode = {
                    if (param.isExternal) {
                      List(
                        lines(
                          s"""|
                              |// Call the delegate deserialize function for ${paramVariableName(param.getName)}
                              |this->paramDelegate->deserializeParam(_id, buff);
                              |"""
                        )
                      )
                    } else {
                      List(
                        lines(
                          s"""|// Deserialize value
                              |this->m_paramLock.lock();
                              |
                              |// If there was a deserialization issue, mark it invalid
                              |"""
                        ),
                        wrapInIfElse(
                          s"this->${paramValidityFlagName(param.getName)} == Fw::ParamValid::VALID",
                          line(s"stat = buff.deserialize(this->${paramVariableName(param.getName)});") ::
                            wrapInIf(
                              "stat != Fw::FW_SERIALIZE_OK",
                              param.default match {
                                case Some(value) => lines(
                                  s"""|this->${paramValidityFlagName(param.getName)} = Fw::ParamValid::DEFAULT;
                                      |// Set default value
                                      |this->${paramVariableName(param.getName)} = ${ValueCppWriter.write(s, value)};
                                      |"""
                                )
                                case None => lines(
                                  s"this->${paramValidityFlagName(param.getName)} = Fw::ParamValid::INVALID;"
                                )
                              }
                            ),
                          param.default match {
                            case Some(value) => lines(
                              s"""|// Set default value
                                  |this->${paramValidityFlagName(param.getName)} = Fw::ParamValid::DEFAULT;
                                  |this->${paramVariableName(param.getName)} = ${ValueCppWriter.write(s, value)};
                                  |"""
                            )
                            case None => lines("// No default")
                          }
                        ),
                        Line.blank :: lines("this->m_paramLock.unLock();")
                      )
                    }
                  }

                  List.concat(
                    lines(
                      s"""|_id = this->getIdBase() + ${paramIdConstantName(param.getName)};
                          |
                          |// Get parameter ${param.getName}
                          |this->${paramValidityFlagName(param.getName)} =
                          |  this->${portVariableName(prmGetPort.get)}[0].invoke(
                          |    _id,
                          |    buff
                          |  );
                          |
                          |"""
                    ) ++
                    deserializationCode.flatten
                  )
                }
              ),
              lines(
                """|// Call notifier
                   |this->parametersLoaded();
                   |"""
              )
            )
          )
        )
      )
    )
  }

  private def getHookFunctions: List[CppDoc.Class.Member] = {
    addAccessTagAndComment(
      "PROTECTED",
      "Parameter update hook",
      List(
        functionClassMember(
          Some(
            s"""|\\brief Called whenever a parameter is updated
                |
                |This function does nothing by default. You may override it.
                |"""
          ),
          "parameterUpdated",
          List(
            CppDoc.Function.Param(
              CppDoc.Type("FwPrmIdType"),
              "id",
              Some("The parameter ID")
            )
          ),
          CppDoc.Type("void"),
          lines("// Do nothing by default"),
          CppDoc.Function.Virtual
        ),
        linesClassMember(
          CppDocWriter.writeBannerComment(
            "Parameter load hook"
          )
        ),
        functionClassMember(
          Some(
            s"""|\\brief Called whenever parameters are loaded
                |
                |This function does nothing by default. You may override it.
                |"""
          ),
          "parametersLoaded",
          Nil,
          CppDoc.Type("void"),
          lines("// Do nothing by default"),
          CppDoc.Function.Virtual
        )
      )
    )
  }

  private def getGetterFunctions: List[CppDoc.Class.Member] = {
    addAccessTagAndComment(
      "PROTECTED",
      "Parameter get functions",
      sortedParams.map((_, param) =>
        functionClassMember(
          Some(
            addSeparatedString(
              s"Get parameter ${param.getName}\n\n\\return The parameter value",
              AnnotationCppWriter.asStringOpt(param.aNode)
            )
          ),
          paramGetterName(param.getName),
          List(
            CppDoc.Function.Param(
              CppDoc.Type("Fw::ParamValid&"),
              "valid",
              Some("Whether the parameter is valid")
            )
          ),
          CppDoc.Type(writeParamType(param.paramType, "Fw::ParamString")),
          lines(
            s"""|${writeParamType(param.paramType, "Fw::ParamString")} _local;
                |this->m_paramLock.lock();
                |valid = this->${paramValidityFlagName(param.getName)};
                |_local = this->${paramVariableName(param.getName)};
                |this->m_paramLock.unLock();
                |return _local;
                |"""
          )
        )
      )
    )
  }

  private def getSetters: List[CppDoc.Class.Member] = {
    addAccessTagAndComment(
      "PRIVATE",
      "Parameter set functions",
      sortedParams.map((_, param) =>
        functionClassMember(
          Some(
            s"""|Set parameter ${param.getName}
                |
                |\\return The command response
                |"""
          ),
          paramHandlerName(param.getName, Command.Param.Set),
          List(
            CppDoc.Function.Param(
              CppDoc.Type("Fw::SerializeBufferBase&"),
              "val",
              Some("The serialization buffer")
            ),
          ),
          CppDoc.Type("Fw::CmdResponse"),
          if (param.isExternal) {
            lines(
              s"""|FwPrmIdType _id;
                  |_id = this->getIdBase() + ${paramIdConstantName(param.getName)};
                  |
                  |// Call the delegate serialize function for ${paramVariableName(param.getName)}
                  |Fw::SerializeStatus _stat;
                  |_stat = this->paramDelegate->deserializeParam(_id, dynamic_cast<Fw::ParamBuffer&>(val));
                  |if (_stat != Fw::FW_SERIALIZE_OK) {
                  |  return Fw::CmdResponse::VALIDATION_ERROR;
                  |}
                  |
                  |// Call notifier
                  |this->parameterUpdated(${paramIdConstantName(param.getName)});
                  |return Fw::CmdResponse::OK;
                  |"""
            )
          } else {
            lines(
              s"""|${writeParamType(param.paramType, "Fw::ParamString")} _local_val;
                  |Fw::SerializeStatus _stat = val.deserialize(_local_val);
                  |if (_stat != Fw::FW_SERIALIZE_OK) {
                  |  return Fw::CmdResponse::VALIDATION_ERROR;
                  |}
                  |
                  |// Assign value only if successfully deserialized
                  |this->m_paramLock.lock();
                  |this->${paramVariableName(param.getName)} = _local_val;
                  |this->${paramValidityFlagName(param.getName)} = Fw::ParamValid::VALID;
                  |this->m_paramLock.unLock();
                  |
                  |// Call notifier
                  |this->parameterUpdated(${paramIdConstantName(param.getName)});
                  |return Fw::CmdResponse::OK;
                  |"""
            )
          }
        )
      )
    )
  }

  private def getSaveFunctions: List[CppDoc.Class.Member] = {
    addAccessTagAndComment(
      "PRIVATE",
      "Parameter save functions",
      sortedParams.map((_, param) =>
        functionClassMember(
          Some(
            s"""|Save parameter ${param.getName}
                |
                |\\return The command response
                |"""
          ),
          paramHandlerName(param.getName, Command.Param.Save),
          Nil,
          CppDoc.Type("Fw::CmdResponse"),
          List.concat(
            wrapInIf(
              s"this->${portVariableName(prmSetPort.get)}[0].isConnected()",
              if (param.isExternal) {
                lines(
                  s"""|FwPrmIdType _id;
                      |_id = this->getIdBase() + ${paramIdConstantName(param.getName)};
                      |
                      |Fw::ParamBuffer saveBuff;
                      |Fw::SerializeStatus stat = this->paramDelegate->serializeParam(_id, saveBuff);
                      |if (stat != Fw::FW_SERIALIZE_OK) {
                      |  return Fw::CmdResponse::VALIDATION_ERROR;
                      |}
                      |
                      |// Save the parameter
                      |this->${portVariableName(prmSetPort.get)}[0].invoke(
                      |  _id,
                      |  saveBuff
                      |);
                      |
                      |return Fw::CmdResponse::OK;
                      |"""
                )
              } else {
                lines(
                  s"""|Fw::ParamBuffer saveBuff;
                      |this->m_paramLock.lock();
                      |
                      |Fw::SerializeStatus stat = saveBuff.serialize(${paramVariableName(param.getName)});
                      |
                      |this->m_paramLock.unLock();
                      |if (stat != Fw::FW_SERIALIZE_OK) {
                      |  return Fw::CmdResponse::VALIDATION_ERROR;
                      |}
                      |
                      |FwPrmIdType id = 0;
                      |id = this->getIdBase() + ${paramIdConstantName(param.getName)};
                      |
                      |// Save the parameter
                      |this->${portVariableName(prmSetPort.get)}[0].invoke(
                      |  id,
                      |  saveBuff
                      |);
                      |
                      |return Fw::CmdResponse::OK;
                      |"""
                )
              }
            ),
            Line.blank :: lines("return Fw::CmdResponse::EXECUTION_ERROR;")
          )
        )
      )
    )
  }

  private def paramGetterName(name: String) =
    s"paramGet_$name"

  private def paramVariableName(name: String) =
    s"m_$name"

}

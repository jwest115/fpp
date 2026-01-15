package fpp.compiler.analysis

import fpp.compiler.ast._
import fpp.compiler.util._

/** Compute the values of constants symbols and expressions */
object EvalConstantExprs extends UseAnalyzer {

  override def constantUse(a: Analysis, node: AstNode[Ast.Expr], use: Name.Qualified) = {
    val symbol = a.useDefMap(node.id)
    for {
      a <- symbol match {
        case Symbol.EnumConstant(node) => defEnumConstantAnnotatedNode(a, node)
        case Symbol.Constant(node) => defConstantAnnotatedNode(a, node)
        case _ => throw InternalError(s"invalid constant use symbol ${symbol} (${symbol.getClass.getName()})")
      }
    } yield {
      val v = a.valueMap(symbol.getNodeId)
      a.assignValue(node -> v)
    }
  }

  override def defConstantAnnotatedNode(a: Analysis, aNode: Ast.Annotated[AstNode[Ast.DefConstant]]) = {
    val (_, node,_) = aNode
    if (!a.valueMap.contains(node.id)) {
      val data = node.data
      for (a <- super.defConstantAnnotatedNode(a, aNode))
        yield {
          val v = a.valueMap(data.value.id)
          a.assignValue(node -> v)
        }
    }
    else Right(a)
  }

  override def defEnumAnnotatedNode(a: Analysis, aNode: Ast.Annotated[AstNode[Ast.DefEnum]]) = {
    def checkForDuplicateValue(
      a: Analysis,
      ids: List[AstNode.Id],
      values: Map[Value,AstNode.Id]
    ): Result.Result[Unit] = ids match {
      case Nil => Right(())
      case id :: tail => {
        val v = Analysis.convertValueToType(a.valueMap(id), Type.Integer)
        values.get(v) match {
          case None => checkForDuplicateValue(a, tail, values + (v -> id))
          case Some(prevId) => {
            val loc = Locations.get(id)
            val prevLoc = Locations.get(prevId)
            Left(SemanticError.DuplicateEnumValue(v.toString, loc, prevLoc))
          }
        }
      }
    }
    for {
      a <- super.defEnumAnnotatedNode(a, aNode)
      _ <- checkForDuplicateValue(a, aNode._2.data.constants.map(_._2.id), Map())
    } yield a
  }

  override def defEnumConstantAnnotatedNode(a: Analysis, aNode: Ast.Annotated[AstNode[Ast.DefEnumConstant]]) = {
    val (_, node, _) = aNode
    if (!a.valueMap.contains(node.id)) {
      node.data.value match {
        case Some(e) => 
          for (a <- super.defEnumConstantAnnotatedNode(a, aNode))
            yield {
              val intValue = Analysis.convertValueToType(a.valueMap(e.id), Type.Integer) match {
                case Value.Integer(intValue) => intValue
                case _ => throw InternalError("conversion to Integer type should yield Integer value")
              }
              val enumType = a.typeMap(node.id) match {
                case enumType : Type.Enum => enumType
                case _ => throw InternalError("type of enum constant definition should be enum type")
              }
              val value = (node.data.name, intValue)
              val enumValue = Value.EnumConstant(value, enumType)
              a.assignValue(node -> enumValue)
            }
        case None => throw InternalError("implied enum constants should already be evaluated")
      }
    }
    else Right(a)
  }

  override def exprArrayNode(a: Analysis, node: AstNode[Ast.Expr], e: Ast.ExprArray) =
    for (a <- super.exprArrayNode(a, node, e))
      yield {
        val eltType = a.typeMap(node.id) match {
          case Type.AnonArray(_, eltType) => eltType
          case _ => throw InternalError("element type of array expression should be AnonArray")
        }
        def f(node: AstNode[Ast.Expr]) = {
          val v = a.valueMap(node.id)
          Analysis.convertValueToType(v, eltType)
        }
        val elts = e.elts.map(f)
        val v = Value.AnonArray(elts)
        a.assignValue(node -> v)
      }

  override def exprArraySubscriptNode(a: Analysis, node: AstNode[Ast.Expr], e: Ast.ExprArraySubscript) = {
    for {
      a <- super.exprNode(a, e.e1)
      a <- super.exprNode(a, e.e2)

      elements <- {
        a.valueMap(e.e1.id) match {
          case Value.AnonArray(elements) => Right(elements)
          case Value.Array(Value.AnonArray(elements), _) => Right(elements)
          case _ => throw InternalError("expected array value")
        }
      }

      index <- {
        a.valueMap(e.e2.id) match {
          case Value.PrimitiveInt(value, _) => Right(value)
          case Value.Integer(value) => Right(value)
          case _ => throw InternalError("type of index should be an integer type")
        }
      }

      // Check if the index is in bounds
      _ <- {
        if index < 0
        then Left(SemanticError.InvalidIntValue(
          Locations.get(e.e2.id),
          index,
          "value may not be negative"
        ))
        else if index >= elements.length
        then Left(SemanticError.InvalidIntValue(
          Locations.get(e.e2.id),
          index,
          s"index value is not in the range [0, ${elements.length-1}]"
        ))
        else Right(None)
      }
    } yield a.assignValue(node -> elements(index.toInt))
  }

  override def exprBinopNode(a: Analysis, node: AstNode[Ast.Expr], e: Ast.ExprBinop) =
    for {
      a <- super.exprBinopNode(a, node, e)
      v <- e.op match {
            case Ast.Binop.Add => Right(a.add(e.e1.id, e.e2.id))
            case Ast.Binop.Div => a.div(e.e1.id, e.e2.id)
            case Ast.Binop.Mul => Right(a.mul(e.e1.id, e.e2.id))
            case Ast.Binop.Sub => Right(a.sub(e.e1.id, e.e2.id))
          }
    } yield a.assignValue(node -> v)

  override def exprLiteralBoolNode(a: Analysis, node: AstNode[Ast.Expr], e: Ast.ExprLiteralBool) = {
    val b = e.value match {
      case Ast.LiteralBool.True => true
      case Ast.LiteralBool.False => false
    }
    val v = Value.Boolean(b)
    Right(a.assignValue(node -> v))
  }


  override def exprLiteralFloatNode(a: Analysis, node: AstNode[Ast.Expr], e: Ast.ExprLiteralFloat) = {
    val v = Value.Float(e.value.toDouble, Type.Float.F64)
    Right(a.assignValue(node -> v))
  }

  override def exprLiteralIntNode(a: Analysis, node: AstNode[Ast.Expr], e: Ast.ExprLiteralInt) = {
    val bigInt = if e.value.length > 2 then e.value.substring(0, 2) match {
      case "0x" | "0X" => BigInt(e.value.substring(2, e.value.length), 16)
      case _ => BigInt(e.value)
    } else BigInt(e.value)

    Right(a.assignValue(node -> Value.Integer(bigInt)))
  }
  
  override def exprLiteralStringNode(a: Analysis, node: AstNode[Ast.Expr], e: Ast.ExprLiteralString) = {
    val v = Value.String(e.value)
    Right(a.assignValue(node -> v))
  }

  override def exprParenNode(a: Analysis, node: AstNode[Ast.Expr], e: Ast.ExprParen) = {
    for (a <- super.exprParenNode(a, node, e))
      yield a.assignValue(node -> a.valueMap(e.e.id))
  }

  override def exprSizeOfNode(a: Analysis, node: AstNode[Ast.Expr], e: Ast.ExprSizeOf) = {
    def computeTypeSize(t: Type): Result.Result[BigInt] = {
      t match
        case Type.PrimitiveInt(kind) =>
          kind match
            case Type.PrimitiveInt.I8 => Right(1)
            case Type.PrimitiveInt.I16 => Right(2)
            case Type.PrimitiveInt.I32 => Right(4)
            case Type.PrimitiveInt.I64 => Right(8)
            case Type.PrimitiveInt.U8 => Right(1)
            case Type.PrimitiveInt.U16 => Right(2)
            case Type.PrimitiveInt.U32 => Right(4)
            case Type.PrimitiveInt.U64 => Right(8)
        case Type.Integer => Right(8) // arbitrary width integer
        case Type.Float(kind) => 
          kind match
            case Type.Float.F32 => Right(4)
            case Type.Float.F64 => Right(8)
        case Type.Boolean => Right(1)
        case Type.String(size) => {
          size match {
            case Some(AstNode(Ast.ExprLiteralInt(s), _)) => Right(BigInt(s))
            case _ => Right(80) // 80 default taken from CppWriterState
          }
        }
        case t: Type.AliasType =>
          computeTypeSize(t.getUnderlyingType)
        case t: Type.Array => {
          val arraySize = t.getArraySize match {
            case Some(as) => BigInt(as)
            case _ => BigInt(11111111) // temp
          }
          for {
            arrayTypeSize <- computeTypeSize(t.anonArray.eltType)
          } yield {
            arrayTypeSize * arraySize
          }
        }
        case Type.Enum(_, repType, _) => computeTypeSize(repType)
        case Type.Struct(_, anonStruct, _, _, _) => {
          anonStruct.members.values.foldLeft(
            Right(BigInt(0)): Result.Result[BigInt]
          ) { (accE, t) =>
            for {
              acc  <- accE
              size <- computeTypeSize(t)
            } yield acc + size
          }
        }

        // placeholder int until I add error 
        case _ => Right(11111111)
    }

    def finalizeTypeDefs(a: Analysis, t: Type): Result.Result[(Analysis)] = {
      t match {
        case Type.Array(aNode, _, _, _) => FinalizeTypeDefs.defArrayAnnotatedNode(a, aNode)
        case Type.AliasType(aNode, _) => FinalizeTypeDefs.defAliasTypeAnnotatedNode(a, aNode)
        case Type.Enum(aNode, _, _) => FinalizeTypeDefs.defEnumAnnotatedNode(a, aNode)
        case Type.Struct(aNode, _, _, _, _) => FinalizeTypeDefs.defStructAnnotatedNode(a, aNode)
        case _ => Right(a)
      }
    }

    e.typeName.data match {
      case Ast.TypeNameQualIdent(_) => {
        a.typeMap.get(e.typeName.id) match {
          case Some(t) => {
            for {
              a2 <- finalizeTypeDefs(a, t)
              typeDefId <- {
                  t.getDefNodeId match {
                    case Some(id) => Right(id)
                    case _ => Right(-1) // temp
                  }
              }
              size <- computeTypeSize(a2.typeMap(typeDefId))
            } yield a2.assignValue(node -> Value.Integer(size))
          }
          case None => {
            Right(a) // temp
          }
        }
      }
      case _ => {
        a.typeMap.get(e.typeName.id) match {
          case Some(t) => {
            for {
              size <- computeTypeSize(t)
            } yield a.assignValue(node -> Value.Integer(size))
          }
          case None => {
            Right(a) // temp
          }
        }
      }
    }
  }

  override def exprStructNode(a: Analysis, node: AstNode[Ast.Expr], e: Ast.ExprStruct) =
    for (a <- super.exprStructNode(a, node, e))
      yield {
        def visitor(members: Value.Struct.Members, node: AstNode[Ast.StructMember]): Value.Struct.Members = {
          val data = node.data
          val v = a.valueMap(data.value.id)
          members + (data.name -> v)
        }
        val empty: Value.Struct.Members = Map()
        val members = e.members.foldLeft(empty)(visitor)
        val v = Value.AnonStruct(members)
        a.assignValue(node -> v)
      }

  override def exprUnopNode(a: Analysis, node: AstNode[Ast.Expr], e: Ast.ExprUnop) = {
    for (a <- super.exprUnopNode(a, node, e))
      yield {
        val v = a.neg(e.e.id)
        a.assignValue(node -> v)
      }
  }

  override def exprDotNode(a: Analysis, node: AstNode[Ast.Expr], e: Ast.ExprDot) = {
    for {
      // Ensure that the parent selector has a type
      a <- super.exprDotNode(a, node, e)

      // Get the value of the selected member
      v <- {
        if (a.valueMap.contains(node.id)) {
          // If the entire dot expression was already resolved by
          // a constantUse, the value will already be in this map
          Right(a.valueMap(node.id))
        } else {
          // The value is not already resolved, this is some sort of
          // member selection.
          a.valueMap(e.e.id) match {
            case Value.AnonStruct(members) =>
              Right(members(e.id.data))
            case Value.Struct(v, ty) =>
              Right(v.members(e.id.data))
            case x => Left(SemanticError.InvalidTypeForMemberSelection(
              e.id.data,
              Locations.get(e.id.id),
              x.getType.toString(),
            ))
          }
        }
      }
    } yield {
      a.assignValue(node -> v)
    }
  }
}

package fpp.compiler.analysis

import fpp.compiler.ast._
import fpp.compiler.util._

/** Match uses to their definitions */
object CheckUses extends UseAnalyzer {

  val helpers = CheckUsesHelpers(
    (a: Analysis) => a.nestedScope,
    (a: Analysis, ns: NestedScope) => a.copy(nestedScope = ns),
    (a: Analysis) => a.symbolScopeMap,
    (a: Analysis) => a.useDefMap,
    (a: Analysis, udm: Map[AstNode.Id, Symbol]) => a.copy(useDefMap = udm)
  )

  override def componentInstanceUse(a: Analysis, node: AstNode[Ast.QualIdent], use: Name.Qualified) =
    helpers.visitQualIdentNode (NameGroup.ComponentInstance) (a, node)

  override def componentUse(a: Analysis, node: AstNode[Ast.QualIdent], use: Name.Qualified) =
    helpers.visitQualIdentNode (NameGroup.Component) (a, node)

  override def stateMachineUse(a: Analysis, node: AstNode[Ast.QualIdent], use: Name.Qualified) =
    helpers.visitQualIdentNode (NameGroup.StateMachine) (a, node)

  override def constantUse(a: Analysis, node: AstNode[Ast.Expr], use: Name.Qualified) = {
    def visitExprNode(a: Analysis, node: AstNode[Ast.Expr]): Result = {
      def visitExprIdent(a: Analysis, node: AstNode[Ast.Expr], name: Name.Unqualified) = {
        val mapping = a.nestedScope.get (NameGroup.Value) _
        for (symbol <- helpers.getSymbolForName(mapping)(node.id, name)) yield {
          val useDefMap = a.useDefMap + (node.id -> symbol)
          a.copy(useDefMap = useDefMap)
        }
      }
      def visitExprDot(a: Analysis, node: AstNode[Ast.Expr], e: AstNode[Ast.Expr], id: AstNode[String]) = {
        for {
          a <- visitExprNode(a, e)
          scope <- {
            val symbol = a.useDefMap(e.id)
            a.symbolScopeMap.get(symbol) match {
              case Some(scope) => Right(scope)
              case None => Left(SemanticError.InvalidSymbol(
                symbol.getUnqualifiedName,
                Locations.get(node.id),
                "not a qualifier",
                symbol.getLoc
              ))
            }
          }
          symbol <- {
            val mapping = scope.get (NameGroup.Value) _
            helpers.getSymbolForName(mapping)(id.id, id.data)
          }
        } yield {
          val useDefMap = a.useDefMap + (node.id -> symbol)
          a.copy(useDefMap = useDefMap)
        }
      }
      val data = node.data
      data match {
        case Ast.ExprIdent(name) => visitExprIdent(a, node, name)
        case Ast.ExprDot(e, id) => visitExprDot(a, node, e, id)
        case _ => throw InternalError("constant use should be qualified identifier")
      }
    }
    visitExprNode(a, node)
  }

  override def defComponentAnnotatedNode(a: Analysis, aNode: Ast.Annotated[AstNode[Ast.DefComponent]]) = {
    val (_, node, _) = aNode
    val data = node.data
    for {
      a <- {
        val symbol = Symbol.Component(aNode)
        val scope = a.symbolScopeMap(symbol)
        val newNestedScope = a.nestedScope.push(scope)
        val a1 = a.copy(nestedScope = newNestedScope)
        super.defComponentAnnotatedNode(a1, aNode)
      }
    } yield a.copy(nestedScope = a.nestedScope.pop)
  }

  override def defEnumAnnotatedNode(a: Analysis, node: Ast.Annotated[AstNode[Ast.DefEnum]]) = {
    val (_, node1, _) = node
    val data = node1.data
    for {
      a <- opt(typeNameNode)(a, data.typeName)
      a <- {
        val symbol = Symbol.Enum(node)
        val scope = a.symbolScopeMap(symbol)
        val newNestedScope = a.nestedScope.push(scope)
        val a1 = a.copy(nestedScope = newNestedScope)
        visitList(a1, data.constants, defEnumConstantAnnotatedNode)
      }
      a <- opt(exprNode)(a, data.default)
    } yield a.copy(nestedScope = a.nestedScope.pop)
  }

  override def defModuleAnnotatedNode(
    a: Analysis,
    aNode: Ast.Annotated[AstNode[Ast.DefModule]]
  ) = {
    val node = aNode._2
    val Ast.DefModule(name, members) = node.data
    for {
      symbol <- {
        val mapping = a.nestedScope.get (NameGroup.Value) _
        helpers.getSymbolForName(mapping)(node.id, name)
      }
      a <- {
        val scope = a.symbolScopeMap(symbol)
        val newNestedScope = a.nestedScope.push(scope)
        val a1 = a.copy(nestedScope = newNestedScope)
        visitList(a1, members, matchModuleMember)
      }
    }
    yield a.copy(nestedScope = a.nestedScope.pop)
  }

  override def defTopologyAnnotatedNode(a: Analysis, node: Ast.Annotated[AstNode[Ast.DefTopology]]) = {
    a.dictionaryNeeded match {
      case true => {
        val impliedAliasTypeUses = List(
          List("FwChanIdType"),
          List("FwDpIdType"),
          List("FwDpPriorityType"),  
          List("FwEventIdType"), 
          List("FwOpcodeType"), 
          List("FwPacketDescriptorType"), 
          List("FwSizeType"),
          List("FwTimeBaseStoreType"),
          List("FwTimeContextStoreType"),
          List("FwTlmPacketizeIdType")
        )
        val impliedEnumUses = List(
          List("Fw", "DpState"),
          List("Fw", "DpCfg", "ProcType")
        )
        val impliedConstantUses = List(
          List("Fw", "DpCfg", "CONTAINER_USER_DATA_SIZE")
        )
        val (_, node1, _) = node
        def checkImpliedUses(
          impliedUses: List[List[String]], 
          id: AstNode.Id,
          typeName: String,
          ng: NameGroup
        ): Result.Result[Set[Symbol]] = {
          Result.foldLeft (impliedUses) (Set[Symbol]()) ((s, identList) => {
            val nodeList = identList.map(AstNode.create(_, node1.id))
            val qualIdent = Ast.QualIdent.fromNodeList(nodeList)
            val impliedUse = AstNode.create(qualIdent, node1.id)
            for {
              symbol <- impliedUse.data match {
                case Ast.QualIdent.Unqualified(name) =>
                  Result.annotateResult(
                    helpers.getSymbolForName(a.nestedScope.get (ng) _)(id, name), 
                    s"when constructing a dictionary, the $typeName $name must be defined"
                  )
                case Ast.QualIdent.Qualified(qualifier, name) =>
                  Result.annotateResult(
                    helpers.getSymbolForQualifiedName (ng) (a, node1.id, qualifier, name),
                    s"when constructing a dictionary, the $typeName ${identList.mkString(".")} must be defined"
                  )
              }
            } yield s + symbol
          })
        }

        for {
          s1 <- checkImpliedUses(impliedAliasTypeUses, node1.id, "alias", NameGroup.Type)
          s2 <- checkImpliedUses(impliedEnumUses, node1.id, "enum", NameGroup.Type)
          s3 <- checkImpliedUses(impliedConstantUses, node1.id, "constant", NameGroup.Value)
          a <- super.defTopologyAnnotatedNode(a, node)
        } yield a.copy(
            dictionaryIntegerSymbolSet = a.dictionaryIntegerSymbolSet ++ s1,
            dictionaryEnumSymbolSet = a.dictionaryEnumSymbolSet ++ s2,
            dictionaryConstantSymbolSet = a.dictionaryConstantSymbolSet ++ s3
          )
      }
      case false => super.defTopologyAnnotatedNode(a, node)
    }
  }

  override def portUse(a: Analysis, node: AstNode[Ast.QualIdent], use: Name.Qualified) =
    helpers.visitQualIdentNode (NameGroup.Port) (a, node)

  override def topologyUse(a: Analysis, node: AstNode[Ast.QualIdent], use: Name.Qualified) =
    helpers.visitQualIdentNode (NameGroup.Topology) (a, node)

  override def typeUse(a: Analysis, node: AstNode[Ast.TypeName], use: Name.Qualified) = {
    val data = node.data
    data match {
      case Ast.TypeNameQualIdent(qualIdentNode) => for {
        a <- helpers.visitQualIdentNode (NameGroup.Type) (a, qualIdentNode)
      } yield {
        val symbol = a.useDefMap(qualIdentNode.id)
        a.copy(useDefMap = a.useDefMap + (node.id -> symbol))
      }
      case _ => throw InternalError("type use should be qualified identifier")
    }
  }

}

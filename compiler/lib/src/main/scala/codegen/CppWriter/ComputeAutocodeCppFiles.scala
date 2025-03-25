package fpp.compiler.codegen

import fpp.compiler.analysis._
import fpp.compiler.ast._
import fpp.compiler.util._

object ComputeAutocodeCppFiles extends ComputeCppFiles {

  override def defComponentAnnotatedNode(
    s: State,
    aNode: Ast.Annotated[AstNode[Ast.DefComponent]]
  ) = {
    val node = aNode._2
    val data = node.data
    val name = s.getName(Symbol.Component(aNode))
    val loc = Locations.get(node.id)
    for {
      s <- addMappings(s, ComputeCppFiles.FileNames.getComponent(name), Some(loc))
      s <- visitList (s, data.members, matchComponentMember)
    }
    yield s
  }

  override def defConstantAnnotatedNode(
    s: State,
    aNode: Ast.Annotated[AstNode[Ast.DefConstant]]
  ) = addMappings(s, ComputeCppFiles.FileNames.getConstants, None)

  override def defAliasTypeAnnotatedNode(
    s: State,
    aNode: Ast.Annotated[AstNode[Ast.DefAliasType]]
  ) = {
    val node = aNode._2
    val name = s.getName(Symbol.AliasType(aNode))
    val loc = Locations.get(node.id)
    val fileName = ComputeCppFiles.FileNames.getAliasType(name)
    addHppMapping(s, fileName, Some(loc), "hpp")
  }

  override def defArrayAnnotatedNode(
    s: State,
    aNode: Ast.Annotated[AstNode[Ast.DefArray]]
  ) = {
    val node = aNode._2
    val name = s.getName(Symbol.Array(aNode))
    val loc = Locations.get(node.id)
    addMappings(s, ComputeCppFiles.FileNames.getArray(name), Some(loc))
  }

  override def defEnumAnnotatedNode(
    s: State,
    aNode: Ast.Annotated[AstNode[Ast.DefEnum]]
  ) = {
    val node = aNode._2
    val name = s.getName(Symbol.Enum(aNode))
    val loc = Locations.get(node.id)
    addMappings(s, ComputeCppFiles.FileNames.getEnum(name), Some(loc))
  }

  override def defModuleAnnotatedNode(
    s: State,
    aNode: Ast.Annotated[AstNode[Ast.DefModule]]
  ) = {
    val node = aNode._2
    val data = node.data
    visitList(s, data.members, matchModuleMember)
  }

  override def defStateMachineAnnotatedNode(
    s: State,
    aNode: Ast.Annotated[AstNode[Ast.DefStateMachine]]
  ) = aNode._2.data.members match {
    case Some(_) =>
      val name = s.getName(Symbol.StateMachine(aNode))
      val loc = Locations.get(aNode._2.id)
      addMappings(
        s,
        ComputeCppFiles.FileNames.getStateMachine(
          name,
          StateMachine.Kind.Internal
        ),
        Some(loc)
      )
    case None => Right(s)
  }

  override def defStructAnnotatedNode(
    s: State,
    aNode: Ast.Annotated[AstNode[Ast.DefStruct]]
  ) = {
    val node = aNode._2
    val name = s.getName(Symbol.Struct(aNode))
    val loc = Locations.get(node.id)
    addMappings(s, ComputeCppFiles.FileNames.getStruct(name), Some(loc))
  }

  override def defPortAnnotatedNode(
    s: State,
    aNode: Ast.Annotated[AstNode[Ast.DefPort]]
  ) = {
    val node = aNode._2
    val name = s.getName(Symbol.Port(aNode))
    val loc = Locations.get(node.id)
    addMappings(s, ComputeCppFiles.FileNames.getPort(name), Some(loc))
  }

  override def defTopologyAnnotatedNode(
    s: State,
    aNode: Ast.Annotated[AstNode[Ast.DefTopology]]
  ) = {
    val node = aNode._2
    val data = node.data
    val name = data.name
    val loc = Locations.get(node.id)
    val a = s.a.copy(parentSymbol = Some(Symbol.Topology(aNode)))
    val s1 = s.copy(a = a)
    for {
      s <- addMappings(s1, ComputeCppFiles.FileNames.getTopology(name), Some(loc))
      s <- visitList (s, data.members, matchTopologyMember)
    }
    yield s
  }

  override def specTlmPacketSetAnnotatedNode(
    s: State,
    aNode: Ast.Annotated[AstNode[Ast.SpecTlmPacketSet]]
  ) = {
    val node = aNode._2
    val loc = Locations.get(node.id)
    val topSymbol = s.a.parentSymbol.get
    val name = s"${topSymbol.getUnqualifiedName}_${node.data.name}"
    addMappings(s, ComputeCppFiles.FileNames.getTlmPacketSet(name), Some(loc))
  }

}

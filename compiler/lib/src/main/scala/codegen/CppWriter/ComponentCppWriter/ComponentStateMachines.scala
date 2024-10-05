package fpp.compiler.codegen

import fpp.compiler.analysis._
import fpp.compiler.ast._
import fpp.compiler.codegen._

case class ComponentStateMachines(
  s: CppWriterState,
  aNode: Ast.Annotated[AstNode[Ast.DefComponent]]
) extends ComponentCppWriterUtils(s, aNode) {

  val externalStateMachineWriter = ComponentExternalStateMachines(s, aNode)

  def getConstantMembers: List[CppDoc.Class.Member] = {
    lazy val enumLines = smInstancesByName.map(
      (name, _) => line(s"$name,")
    )
    lazy val memberLines = List.concat(
      CppDocWriter.writeDoxygenComment("State machine identifiers"),
      wrapInEnumClass("SmId", enumLines, Some("FwEnumStoreType"))
    )
    lazy val lcm = linesClassMember(memberLines)
    guardedList (hasStateMachineInstances) (List(lcm))
  }

  def getFunctionMembers: List[CppDoc.Class.Member] = List.concat(
    getOverflowHooks,
    externalStateMachineWriter.getFunctionMembers
  )

  def getVariableMembers: List[CppDoc.Class.Member] = getSmInstanceMembers

  /** Writes the dispatch cases, if any, for state machine instances */
  def writeDispatchCases: List[Line] = externalStateMachineWriter.writeDispatchCase

  private def getSmInstanceMember(
    name: Name.Unqualified,
    smi: StateMachineInstance
  ): CppDoc.Class.Member = {
    val typeName = s.writeSymbol(smi.symbol)
    linesClassMember(
      Line.blank ::
      lines(
        s"""|//! State machine $name
            |$typeName m_stateMachine_$name;"""
      )
    )
  }

  private def getSmInstanceMembers: List[CppDoc.Class.Member] = addAccessTagAndComment(
    "PRIVATE",
    s"State machine instances",
    smInstancesByName.map(getSmInstanceMember),
    CppDoc.Lines.Hpp
  )

  private def getOverflowHooks: List[CppDoc.Class.Member] =
    addAccessTagAndComment(
      "PROTECTED",
      """|Overflow hooks for state machine instances
         |
         |When sending a signal to a state machine instance, if
         |the queue overflows and the instance is marked with 'hook' behavior,
         |the corresponding function here is called.""",
      stateMachineInstances.filter(_.queueFull == Ast.QueueFull.Hook).map(
        smi => getVirtualOverflowHook(
          smi.getName,
          MessageType.StateMachine,
          ComponentExternalStateMachines.signalParams(s, smi.symbol)
        )
      ),
      CppDoc.Lines.Hpp
    )

}

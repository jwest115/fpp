package fpp.compiler.analysis

import fpp.compiler.ast._
import fpp.compiler.util._

/** Analyze transition expressions */
trait TransitionExprAnalyzer
  extends StateMachineAnalysisVisitor
  with StateAnalyzer
{

  // ----------------------------------------------------------------------
  // Interface methods to override
  // Each of these methods is called when a corresponding transition
  // expression is visited
  // ----------------------------------------------------------------------

  /** A transition expression in an external state transition */
  def stateTransitionExpr(
    sma: StateMachineAnalysis,
    aNode: Ast.Annotated[AstNode[Ast.SpecStateTransition]],
    exprNode: AstNode[Ast.TransitionExpr]
  ): Result = default(sma)

  /** A transition expression in an initial transition */
  def initialTransitionExpr(
    sma: StateMachineAnalysis,
    aNode: Ast.Annotated[AstNode[Ast.SpecInitialTransition]],
    exprNode: AstNode[Ast.TransitionExpr]
  ): Result = default(sma)

  /** The pair of transition expressions in a junction */
  def junctionTransitionExprPair(
    sma: StateMachineAnalysis,
    junction: StateMachineSymbol.Choice,
    ifExprNode: AstNode[Ast.TransitionExpr],
    elseExprNode: AstNode[Ast.TransitionExpr]
  ): Result = for {
    sma <- junctionTransitionExpr(sma, junction, ifExprNode)
    sma <- junctionTransitionExpr(sma, junction, elseExprNode)
  } yield sma

  /** A transition expression in a junction */
  def junctionTransitionExpr(
    sma: StateMachineAnalysis,
    junction: StateMachineSymbol.Choice,
    exprNode: AstNode[Ast.TransitionExpr]
  ): Result = default(sma)

  // ----------------------------------------------------------------------
  // Implementation using StateMachineAnalysisVisitor
  // ----------------------------------------------------------------------

  override def defChoiceAnnotatedNode(
    sma: StateMachineAnalysis,
    aNode: Ast.Annotated[AstNode[Ast.DefChoice]]
  ) = {
    val data = aNode._2.data
    junctionTransitionExprPair(
      sma,
      StateMachineSymbol.Choice(aNode),
      data.ifTransition,
      data.elseTransition
    )
  }

  override def defStateAnnotatedNode(
    sma: StateMachineAnalysis,
    aNode: Ast.Annotated[AstNode[Ast.DefState]]
  ) = {
    val parentState = sma.parentState
    for {
      sma <- super.defStateAnnotatedNode(
        sma.copy(parentState = Some(StateMachineSymbol.State(aNode))),
        aNode
      )
    } yield sma.copy(parentState = parentState)
  }

  override def specInitialTransitionAnnotatedNode(
    sma: StateMachineAnalysis,
    aNode: Ast.Annotated[AstNode[Ast.SpecInitialTransition]]
  ) = {
    val transition = aNode._2.data.transition
    initialTransitionExpr(sma, aNode, transition)
  }

  override def specStateTransitionAnnotatedNode(
    sma: StateMachineAnalysis,
    aNode: Ast.Annotated[AstNode[Ast.SpecStateTransition]]
  ) = {
    val data = aNode._2.data
    data.transitionOrDo match {
      case Ast.TransitionOrDo.Transition(transition) =>
        stateTransitionExpr(sma, aNode, transition)
      case _ => Right(sma)
    }
  }

}

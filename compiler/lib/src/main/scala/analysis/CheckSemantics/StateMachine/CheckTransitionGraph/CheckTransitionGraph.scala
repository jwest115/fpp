package fpp.compiler.analysis

import fpp.compiler.ast._
import fpp.compiler.util._

/** Compute and check the transition graph */
object CheckTransitionGraph {

  def defStateMachineAnnotatedNode(
    sma: StateMachineAnalysis,
    aNode: Ast.Annotated[AstNode[Ast.DefStateMachine]]
  ): Result.Result[StateMachineAnalysis] = {
    for {
      sma <- ConstructTransitionGraph.defStateMachineAnnotatedNode(sma, aNode)
      _ <- CheckTGReachability.stateMachineAnalysis(sma)
      _ <- CheckJunctionCycles.stateMachineAnalysis(sma)
      // TODO: Construct the reverse transition graph
    }
    yield sma
  }

}
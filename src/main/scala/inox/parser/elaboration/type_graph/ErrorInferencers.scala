package inox.parser.elaboration.type_graph

import inox.parser.elaboration.SimpleTypes

import scala.util.parsing.input.Position

trait ErrorInferencers {
  self: PathFinders with ErrorReasons with ErrorReasonSearch with GraphStructure with SimpleTypes=>

  import Nodes._

  abstract class ErrorInference(val paths: Seq[GraphPath]) {


    def infer(): Set[Reason] = {
      val cand = candidates()
      val algo = algorithm(cand)


      val results = algo.findOptimal()

      results
    }

    /**
      * @return A set of entities that the inference is performed on
      */
    def candidates(): Set[Entity]

    /**
      * @param candidates
      * Basic elements of possible explanations
      * @return Return an instance of heuristic search algorithm to use
      */
    def algorithm(candidates: Set[Entity]): HeuristicSearchAlgorithm

  }

  class TypeReasonInference(paths: Seq[GraphPath], val nodes: Set[Node]) extends ErrorInference(paths) {

    private var satisfiableCounts: Map[Position, Int] = Map.empty

    for (node <- nodes) {
      satisfiableCounts = satisfiableCounts + (node.pos -> node.satisfiableCount())
    }

    /**
      * @return A set of entities that the inference is performed on
      */
    override def candidates(): Set[Entity] = {
      var candidates: Set[Entity] = Set.empty

      for (path <- paths) {
        for (node <- path.pathNodes()) {
          node match {
            // ignore Unknowns
            case n: TypeNode => n.tpe match {
              case _ : SimpleTypes.Unknown => ()
              case _ => candidates = candidates + TypeEntity(node.pos, satisfiableCounts(node.pos))
            }
            case _ => candidates = candidates + TypeEntity(node.pos, satisfiableCounts(node.pos))
          }
        }
      }

      candidates
    }

    /**
      * @param candidates
      * Basic elements of possible explanations
      * @return Return an instance of heuristic search algorithm to use
      */
    override def algorithm(candidates: Set[Entity]): HeuristicSearchAlgorithm = {
      new ExplanationFinder(candidates.toArray, paths.toList, 4)
    }
  }


  class MinCutFinder (unsatisfiablePaths: List[GraphPath], candidates: Array[Entity], suboptimal: Int)
    extends ExplanationFinder(candidates, unsatisfiablePaths, suboptimal, 1, 0) {
  }
}
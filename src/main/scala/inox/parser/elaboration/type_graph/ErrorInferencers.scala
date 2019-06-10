package inox.parser.elaboration.type_graph

import inox.parser.elaboration.SimpleTypes

trait ErrorInferencers {
  self: PathFinders with ErrorReasons with ErrorReasonSearch with GraphStructure with SimpleTypes with Elements =>

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
    def candidates(): Traversable[Entity]

    /**
      * @param candidates
      * Basic elements of possible explanations
      * @return Return an instance of heuristic search algorithm to use
      */
    def algorithm(candidates: Traversable[Entity]): HeuristicSearchAlgorithm

  }

  class TypeReasonInference(paths: Seq[GraphPath], val nodes: Set[Node]) extends ErrorInference(paths) {

    private var satisfiableCounts: Map[Element, Int] = Map.empty

    for (node <- nodes) {
      satisfiableCounts = satisfiableCounts + (node.element -> node.satisfiableCount())
    }

    /**
      * @return A set of entities that the inference is performed on
      */
    override def candidates(): Traversable[Entity] = {
      paths.flatMap(path => List(TypeEntity(path.firstInPath().element, satisfiableCounts(path.firstInPath().element)),
        TypeEntity(path.lastInPath().element, satisfiableCounts(path.lastInPath().element)))).toSet
    }

    /**
      * @param candidates
      * Basic elements of possible explanations
      * @return Return an instance of heuristic search algorithm to use
      */
    override def algorithm(candidates: Traversable[Entity]): HeuristicSearchAlgorithm = {
      new ExplanationFinder(candidates.toArray, paths.toList, 4)
    }
  }
}

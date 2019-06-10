package inox.parser.elaboration.type_graph

import inox.parser.ElaborationErrors
import inox.parser.elaboration.{Constraints, SimpleTypes}

trait TypeGraphAnalysis extends GraphStructure
  with ErrorReasons
  with ErrorInferencers
  with PathFinders
  with ErrorReasonSearch
  with Elements {
  self: SimpleTypes with Constraints with ElaborationErrors =>


  class ConstraintGraphAnalysis(val graph: Graph) {

    private val pathFinder = new ShortestPathFinder(graph)

    def testConsistency(start: Node, end: Node, hops: List[Edge], finder: PathFinder): Option[GraphPath] = {

      if (start.isTrivialEnd || end.isTrivialEnd)
        return None

      val path = new GraphPath(hops.toArray, finder)

      if (path.isInformative) {
        if (path.isUnsatisfiable) {
          Some(path)
        } else {
          if (path.isValidPath || path.isSatisfiablePath) {
            path.incrementSatisfiable()
          }
          None
        }
      } else
        None
    }

    def generateErrorPaths(): List[GraphPath] = {
      var unsatisfiable: List[GraphPath] = List()


      for (start <- graph.nodes) {
        for (end <- graph.nodes) {
          if (pathFinder.hasLeqEdge(start, end)) {
            // skolem check is not needed
            val hops: List[Edge] = pathFinder.getPath(start, end)
            testConsistency(start, end, hops, pathFinder).foreach(path => unsatisfiable = path :: unsatisfiable
            )
          }

          if (pathFinder.hasCombineEdge(start, end)) {
            val hops: List[Edge] = pathFinder.getPath(start, end)
            testConsistency(start, end, hops, pathFinder).foreach(path => unsatisfiable = path :: unsatisfiable)
          }
        }
      }

      unsatisfiable
    }

    def generateUnsatisfiablePairs(element: Element): Set[Element] = {
      var pairs: Set[Element] = Set.empty

      assert(graph.elementNodeMap.keySet contains element)

      val node = graph.elementNodeMap(element)


      for (other <- graph.nodes) {
        if (pathFinder.hasLeqEdge(node, other)) {
          val hops: List[Edge] = pathFinder.getPath(node, other)
          testConsistency(node, other, hops, pathFinder).foreach(_ => pairs = pairs + other.element)
        }
        if (pathFinder.hasLeqEdge(other, node)) {
          val hops: List[Edge] = pathFinder.getPath(other, node)
          testConsistency(other, node, hops, pathFinder).foreach(_ => pairs = pairs + other.element)
        }
      }

      pairs
    }
  }


  class GraphDiagnosis(val graph: Graph) {

    private val constraintGraphAnalysis: ConstraintGraphAnalysis = new ConstraintGraphAnalysis(graph)

    def numberOfUnsatisfiablePaths(): Int = {
      constraintGraphAnalysis.generateErrorPaths().size
    }

    def getUnsatisfiablePaths(): Seq[GraphPath] = {
      constraintGraphAnalysis.generateErrorPaths()
    }

    def getUnsatisfiablePairs(element: Element): Set[Element] = {
      constraintGraphAnalysis.generateUnsatisfiablePairs(element)
    }


    def getSuggestions(unsatisfiablePaths: Seq[GraphPath]): Reason = {
      var result: List[Reason] = List()

      result = result ++ new TypeReasonInference(unsatisfiablePaths, graph.nodes).infer()

      val sorted = result.sortBy(res => res.weight)
      sorted.head
    }
  }


  object GraphDiagnosis {
    def getInstance(goal: Seq[Constraint]): GraphDiagnosis = {
      val graph = constructSeq(goal)
      new GraphDiagnosis(graph)
    }
  }

}

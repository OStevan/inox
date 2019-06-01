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


  class ConstraintGraphAnalysis {


    private def getPathFinder(graph: Graph): PathFinder = {
      new ShortestPathFinder(graph)
    }

    def testConsistency(start: Node, end: Node, hops: List[Edge], finder: PathFinder): List[GraphPath] = {

      if (start.isTrivialEnd || end.isTrivialEnd)
        return List()

      val path = new GraphPath(hops.toArray, finder)

      if (path.isInformative) {
        if (path.isUnsatisfiable) {
          path.markCause()
          List(path)
        } else {
          if (path.isValidPath) {
            path.incSatisfiableCount()
          } else if (path.isSatisfiablePath) {
            path.incSatisfiableCount()
            // here is where expansion is should be done
          }
          List()
        }
      } else
        List()
    }

    def generateErrorPaths(graph: Graph): List[GraphPath] = {
      var unsatisfiable: List[GraphPath] = List()

      val finder = getPathFinder(graph)

      var testedPaths: List[(Node, Node)] = List.empty


      for (start <- graph.nodes) {
        for (end <- graph.nodes) {
          if (finder.hasLeqEdge(start, end)) {
            // skolem check is not needed
            val hops: List[Edge] = finder.getPath(start, end)
            testedPaths = (start, end) :: testedPaths
            unsatisfiable = unsatisfiable ++ testConsistency(start, end, hops, finder)
          }
        }
      }

      unsatisfiable
    }
  }


  class GraphDiagnosis(val graph: Graph) {

    private val constraintGraphAnalysis: ConstraintGraphAnalysis = new ConstraintGraphAnalysis

    def numberOfUnsatisfiablePaths(): Int = {
      constraintGraphAnalysis.generateErrorPaths(graph).size
    }

    def getUnsatisfiablePaths(): Seq[GraphPath] = {
      constraintGraphAnalysis.generateErrorPaths(graph)
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

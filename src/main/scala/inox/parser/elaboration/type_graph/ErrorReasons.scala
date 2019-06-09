package inox.parser.elaboration.type_graph

import inox.parser.ElaborationErrors
import inox.parser.elaboration.SimpleTypes
import scala.util.parsing.input.Position

trait ErrorReasons {
  self: PathFinders with SimpleTypes with ElaborationErrors with Elements with TypeGraphAnalysis =>

  /**
    * Result of type graph error diagnosis, this should be mapped to an exception which can be used by rest of
    * the Inox
    *
    * @param entities which provide this explanation
    * @param weight   calculated weight of this reason
    */
  case class Reason(entities: Set[Entity], weight: Double) extends Comparable[Reason] {
    override def compareTo(other: Reason): Int = weight.compareTo(other.weight)

    def toErrorMessage(diagnosis: GraphDiagnosis): String = ("graph: Invalid assigned types" :: entities.map(_.toErrorMessage(diagnosis)).toList).mkString("\n")
  }


  /**
    * Basic unit of error reporting, expressions, etc.
    */
  abstract class Entity(val pos: Position, val satisfiablePathsCount: Int) {

    def explainsPath(path: GraphPath): Boolean

    def toErrorMessage(diagnosis: GraphDiagnosis): String
  }

  /**
    * Gives reasons why assigned types are incorrect, entity is represented as a type assigned at a certain position
    */
  case class TypeEntity(element: Element, satisfiableCount: Int) extends Entity(element.position, satisfiableCount) {

    override def explainsPath(path: GraphPath): Boolean = {
      path.pathNodes().exists(node => node.element == element)
    }

    override def toErrorMessage(diagnosis: GraphDiagnosis): String = {
      val unsatisfiablePaths = diagnosis.getUnsatisfiablePairs(element)
      withPosition(element.typeInformation + " is in conflict with other expected types\n")(element.position) + "\n" +
        unsatisfiablePaths.map(elem => withPosition(elem.typeInformation + " is a conflicting type")(elem.position)).mkString("\n")
    }
  }

}

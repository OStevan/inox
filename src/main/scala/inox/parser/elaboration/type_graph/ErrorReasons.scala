package inox.parser.elaboration.type_graph

import scala.util.parsing.input.Position

trait ErrorReasons { self: PathFinders =>

  /**
    * Result of type graph error diagnosis, this should be mapped to an exception which can be used by rest of
    * the Inox
    * @param entities which provide this explanation
    * @param weight calculated weight of this reason
    */
  case class Reason (entities: Set[Entity], weight: Double) extends Comparable[Reason]{
    override def compareTo(other: Reason): Int = weight.compareTo(other.weight)
  }


  /**
    * Basic unit of error reporting, expressions, missing hypothesis.
    */
  abstract class Entity (val satisfiablePathsCount: Int) {

    /**
      * Checks if this entity gives a reason why an error happened, in case of expressions it should appear on a path
      * and in case of a missing hypothesis it removes an error on a path.
      * @param path represents and unsatisfiable path between two nodes for which we are searching for an explanation
      * @return flag if it in fact explains the reason why the path is unsatisfiable
      */
    def explainsPath(path: GraphPath): Boolean

    override def equals(obj: Any): Boolean
  }

  /**
    * Gives reasons why assigned types are incorrect, entity is represented as a type assigned at a certain position
    */
  case class TypeEntity(position: Position, satisfiableCount: Int) extends Entity(satisfiableCount) {


    /**
      * Checks if this entity gives a valid reason why the expression is not satisfiable
      *
      * @param path represents and unsatisfiable path between two nodes for which we are searching for an explanation
      * @return flag if it in fact explains the reason why the path is unsatisfiable
      */
    override def explainsPath(path: GraphPath): Boolean = {
      path.pathNodes().exists(node => node.pos == position)
    }
  }

}

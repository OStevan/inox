package inox.parser.elaboration.type_graph

import inox.parser.elaboration.{Constraints, SimpleTypes}

import scala.util.parsing.input.Position

trait Elements {
  self: SimpleTypes with Constraints =>

  /**
    * Encapsulates type classes and types for easier graph manipulation, uses also underlying position of types and classes
    */
  trait Element {
    def position: Position = this match {
      case element: TypeElement => element.tpe.pos
      case element: TypeClassElement => element.pos
    }

    def compatibleConstructors(entity: Element): Boolean = (this, entity) match {
      case (_: TypeClassElement, _) => false
      case (_, _: TypeClassElement) => false
      case (from: TypeElement, to: TypeElement) => (from.tpe, to.tpe) match {
        case (_: SimpleTypes.BagType, _: SimpleTypes.BagType) => true
        case (_: SimpleTypes.SetType, _: SimpleTypes.SetType) => true
        case (_: SimpleTypes.MapType, _: SimpleTypes.MapType) => true
        case (_: SimpleTypes.TupleType, _: SimpleTypes.TupleType) => true
        case (SimpleTypes.FunctionType(firstFroms, _), SimpleTypes.FunctionType(secondFroms, _)) if firstFroms.length == secondFroms.length =>
          true
        case (SimpleTypes.ADTType(_, firstArgs), SimpleTypes.ADTType(_, secondArgs)) if firstArgs.length == secondArgs.length =>
          true
        case _ => false
      }
    }

    def accept(other: Element): Boolean = (this, other) match {
      case (first: TypeClassElement, second: TypeElement) => first.typeClass.accepts(second.tpe).isInstanceOf[Some[Seq[Constraint]]]
      case (first: TypeClassElement, second: TypeClassElement) =>
        //TODO check with Romain
        false
      case _ => false
    }


    /**
      * Checks if the two entities are equivalent with respect to type information
      *
      * @param entity to compare with
      * @return equality flag
      */
    def informationEquality(entity: Element): Boolean = (this, entity) match {
      case (first: TypeElement, second: TypeElement) => first.tpe == second.tpe
      case (first: TypeClassElement, second: TypeClassElement) => first.typeClass == second.typeClass
      case _ => false
    }

    def isTrivialEnd: Boolean


    /**
      * Checks if the entity has type variables, TODO check the implementation again for this
      *
      * @return
      */
    def hasVars: Boolean

    override def equals(obj: Any): Boolean
  }

  /**
    * Provides Entity implementation for Inox interpolation types
    *
    * @param tpe of the entity
    */
  case class TypeElement(tpe: SimpleTypes.Type) extends Element {
    override def equals(obj: Any): Boolean = obj match {
      case other: TypeElement => (tpe, other.tpe) match {
        case (first: SimpleTypes.Unknown, second: SimpleTypes.Unknown) => first == second
        case _ => tpe == other.tpe && position == other.position
      }
      case _ => false
    }

    override def hasVars: Boolean = tpe.unknowns.isEmpty

    override def isTrivialEnd: Boolean = tpe match {
      case _: SimpleTypes.Unknown => true
      case _ => false

    }
  }

  /**
    * Provides Entity implementation for Inox type classes
    *
    * @param typeClass of the entity
    * @param pos       where this entity is found in the source
    */
  case class TypeClassElement(typeClass: TypeClasses.TypeClass, pos: Position) extends Element {
    override def equals(obj: Any): Boolean = obj match {
      case other: TypeClassElement => other.typeClass == typeClass && other.pos == pos
      case _ => false
    }

    /**
      * Checks if the entity has type variables, TODO check the implementation again for this
      *
      * @return
      */
    override def hasVars: Boolean = false

    override def isTrivialEnd: Boolean = false
  }

}

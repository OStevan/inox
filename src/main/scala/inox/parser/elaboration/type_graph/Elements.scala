package inox.parser.elaboration.type_graph

import inox.parser.elaboration.{Constraints, SimpleTypes}

import scala.collection.immutable.Queue
import scala.util.parsing.input.Position

trait Elements {
  self: SimpleTypes with Constraints =>

  /**
    * Encapsulates type classes and types for easier graph manipulation, uses also underlying position of types and classes
    */
  trait Element {

    implicit class Crossable[X](xs: Traversable[X]) {
      def cross[Y](ys: Traversable[Y]): Traversable[(X, Y)] = for {x <- xs; y <- ys } yield (x, y)
    }

    def isConstructor: Boolean

    def replace(original: Element, substitution: Element): Traversable[Element]

    private def replace(types: Seq[SimpleTypes.Type], original: SimpleTypes.Type, substitution: SimpleTypes.Type): Traversable[Seq[SimpleTypes.Type]] = types match {
      case Seq(head, tail @ _*) =>
        val res = replace(tail, original, substitution)
        val temp = replace(head, original, substitution)
        (temp cross res).map(pair => pair._2.+:(pair._1))

      case Seq(elem) => List(replace(elem, original, substitution).toSeq)
      case _ => List()
    }

    protected def replace(tpe: SimpleTypes.Type, original: SimpleTypes.Type, substitution: SimpleTypes.Type): Traversable[SimpleTypes.Type] = tpe match {
      case SimpleTypes.BagType(elem) =>
        replace(elem, original, substitution).map(tpe => SimpleTypes.SetType(tpe).withPos(tpe.pos))
      case SimpleTypes.SetType(elem) =>
        replace(elem, original, substitution).map(tpe => SimpleTypes.SetType(tpe).withPos(tpe.pos))
      case SimpleTypes.MapType(from, to) =>
        (replace(from, original, substitution) cross replace(to, original, substitution)).map(pair => SimpleTypes.MapType(pair._1, pair._2).withPos(tpe.pos))
      case SimpleTypes.FunctionType(froms, to) =>
        (replace(froms, original, substitution) cross replace(to, original, substitution)).map(pair => SimpleTypes.FunctionType(pair._1, pair._2).withPos(tpe.pos))
      case SimpleTypes.TupleType(elems) =>
        replace(elems, original, substitution).map(res => SimpleTypes.TupleType(res))
      case SimpleTypes.ADTType(ident, args) =>
        replace(args, original, substitution).map(res => SimpleTypes.ADTType(ident, res).withPos(tpe.pos))
      case _ if tpe == original => Queue(original, substitution)
      case _ => Queue(original)
    }

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

    override def isConstructor: Boolean = tpe match {
      case _: SimpleTypes.TupleType | _: SimpleTypes.FunctionType | _: SimpleTypes.ADTType | _: SimpleTypes.BagType
           | _: SimpleTypes.SetType | _: SimpleTypes.BagType => true
      case _ => false
    }

    override def replace(original: Element, substitution: Element): Traversable[Element] = (original, substitution) match {
      case (first: TypeElement, second: TypeElement) => tpe match {
        case _: SimpleTypes.TupleType | _: SimpleTypes.ADTType | _: SimpleTypes.FunctionType | _: SimpleTypes.BagType
             | _: SimpleTypes.SetType | _: SimpleTypes.MapType => replace(tpe, first.tpe, second.tpe).map(tpe => TypeElement(tpe))
        case _ => assert(false, "Should not try to replace on simple types")
          List()
      }
      case _ => assert(false, "Substitutions with type classes should never happen")
        List()
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

    override def isConstructor: Boolean = false

    override def replace(original: Element, substitution: Element): List[Element] = {
      assert(false, "Replacing on type classes should never happen")
      List()
    }
  }

}

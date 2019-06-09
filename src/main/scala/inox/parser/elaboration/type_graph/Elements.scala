package inox.parser.elaboration.type_graph

import inox.parser.elaboration.{Constraints, SimpleTypes}

import scala.collection.immutable.Queue
import scala.util.parsing.input.{NoPosition, Position}

trait Elements {
  self: SimpleTypes with Constraints =>

  /**
    * Encapsulates type classes and types for easier graph manipulation, uses also underlying position of types and classes
    */
  trait Element {

    def typeInformation: String


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
        replace(elems, original, substitution).map(res => SimpleTypes.TupleType(res).withPos(tpe.pos))
      case SimpleTypes.ADTType(ident, args) =>
        replace(args, original, substitution).map(res => SimpleTypes.ADTType(ident, res).withPos(tpe.pos))
      case _ if tpe == original => Queue(original, substitution)
      case _ => Queue(original)
    }

    def position: Position = this match {
      case element: TypeElement =>
//        assert(element.tpe.pos != NoPosition, "Some type dos not have a position")
        element.tpe.pos
      case element: TypeClassElement =>
//        assert(element.pos != NoPosition, "Some type class dos not have a position")
        element.pos
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

    protected def accept(first: SimpleTypes.Type, second: SimpleTypes.Type): Boolean = (first, second) match {
      case (u1: SimpleTypes.Unknown, _) => true
      case (_, u2: SimpleTypes.Unknown) => true
      case (SimpleTypes.UnitType(), SimpleTypes.UnitType()) => true
      case (SimpleTypes.IntegerType(), SimpleTypes.IntegerType()) => true
      case (SimpleTypes.BitVectorType(signed1, size1), SimpleTypes.BitVectorType(signed2, size2)) if signed1 == signed2 && size1 == size2 => true
      case (SimpleTypes.BooleanType(), SimpleTypes.BooleanType()) => true
      case (SimpleTypes.StringType(), SimpleTypes.StringType()) => true
      case (SimpleTypes.CharType(), SimpleTypes.CharType()) => true
      case (SimpleTypes.RealType(), SimpleTypes.RealType()) => true
      case (SimpleTypes.FunctionType(fs1, t1), SimpleTypes.FunctionType(fs2, t2)) if fs1.size == fs2.size => {
        fs1.zip(fs2).forall(pair => accept(pair._1, pair._2)) && accept(t1, t2)
      }
      case (SimpleTypes.TupleType(es1), SimpleTypes.TupleType(es2)) if es1.size == es2.size =>
        es1.zip(es2).forall(pair => accept(pair._1, pair._2))
      case (SimpleTypes.MapType(f1, t1), SimpleTypes.MapType(f2, t2)) => {
        accept(f1, f2) && accept(t1, t2)
      }
      case (SimpleTypes.SetType(e1), SimpleTypes.SetType(e2)) => accept(e1, e2)
      case (SimpleTypes.BagType(e1), SimpleTypes.BagType(e2)) => accept(e1, e2)
      case (SimpleTypes.ADTType(i1, as1), SimpleTypes.ADTType(i2, as2)) if i1 == i2 && as1.size == as2.size =>
        as1.zip(as2).forall(pair => accept(pair._1, pair._2))
      case (SimpleTypes.TypeParameter(i1), SimpleTypes.TypeParameter(i2)) if i1 == i2 => true
      case _ => false
    }

    def accept(other: Element): Boolean = (this, other) match {
      case (first: TypeClassElement, second: TypeElement) => first.typeClass.accepts(second.tpe).isInstanceOf[Some[Seq[Constraint]]]
      case (_: TypeClassElement, _: TypeClassElement) =>
        false
      case (first: TypeElement, second: TypeElement) => accept(first.tpe, second.tpe)
      case _ => false
    }

    def intersect(other: Element): Boolean = (this, other) match {
      case (TypeClassElement(first, _), TypeClassElement(second, _)) =>
        // add dummy type for intersection check
        first.combine(second)(SimpleTypes.Unknown.fresh).isInstanceOf[Some[Seq[Constraint]]]
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

    override def hasVars: Boolean = tpe.unknowns.nonEmpty

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
        case _ =>
          // ignore replacements for simple types
          List()
      }
      case _ =>
        // ignore replacements with type classes
        List()
    }

    override def typeInformation: String = "Type " + tpe.toString
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
      // ignore replacing on type classes
      List()
    }

    override def typeInformation: String = "Type class " + typeClass.toString
  }

}

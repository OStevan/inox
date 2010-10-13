package purescala

object TypeTrees {
  import Common._
  import Trees._
  import Definitions._

  trait Typed {
    self =>

    private var _type: Option[TypeTree] = None

    def getType: TypeTree = _type match {
      case None => Untyped
      case Some(t) => t
    }

    def setType(tt: TypeTree): self.type = _type match {
      case None => _type = Some(tt); this
      case Some(o) if o != tt => scala.Predef.error("Resetting type information.")
      case _ => this
    }
  }

  trait FixedType extends Typed {
    self =>

    val fixedType: TypeTree
    override def getType: TypeTree = fixedType
    override def setType(tt2: TypeTree) : self.type = this
  }
    

  sealed abstract class TypeTree {
    override def toString: String = PrettyPrinter(this)
  }

  def leastUpperBound(t1: TypeTree, t2: TypeTree): TypeTree = (t1,t2) match {
    case (c1: ClassType, c2: ClassType) => {
      import scala.collection.immutable.Set
      var c: ClassTypeDef = c1.classDef
      var visited: Set[ClassTypeDef] = Set(c)

      while(c.parent.isDefined) {
        c = c.parent.get
        visited = visited ++ Set(c)
      }

      c = c2.classDef
      var found: Option[ClassTypeDef] = if(visited.contains(c)) {
        Some(c)
      } else {
        None
      }

      while(found.isEmpty && c.parent.isDefined) {
        c = c.parent.get
        if(visited.contains(c))
          found = Some(c)
      }

      if(found.isEmpty) {
        scala.Predef.error("Asking for lub of unrelated class types : " + t1 + " and " + t2)
      } else {
        classDefToClassType(found.get)
      }
    }

    case (o1, o2) if (o1 == o2) => o1
    case (o1,NoType) => o1
    case (NoType,o2) => o2
    case (o1,AnyType) => AnyType
    case (AnyType,o2) => AnyType

    case _ => scala.Predef.error("Asking for lub of unrelated types: " + t1 + " and " + t2)
  }

  // returns the number of distinct values that inhabit a type
  sealed abstract class TypeSize
  case class FiniteSize(size: Int) extends TypeSize
  case object InfiniteSize extends TypeSize

  def domainSize(typeTree: TypeTree) : TypeSize = typeTree match {
    case Untyped => FiniteSize(0)
    case AnyType => InfiniteSize
    case NoType => FiniteSize(0)
    case BooleanType => FiniteSize(2)
    case Int32Type => InfiniteSize
    case ListType(_) => InfiniteSize
    case TupleType(bases) => {
      val baseSizes = bases.map(domainSize(_))
      baseSizes.find(_ == InfiniteSize) match {
        case Some(_) => InfiniteSize
        case None => FiniteSize(baseSizes.map(_.asInstanceOf[FiniteSize].size).reduceLeft(_ * _))
      }
    }
    case SetType(base) => domainSize(base) match {
      case InfiniteSize => InfiniteSize
      case FiniteSize(n) => FiniteSize(scala.math.pow(2, n).toInt)
    }
    case MultisetType(_) => InfiniteSize
    case MapType(from,to) => (domainSize(from),domainSize(to)) match {
      case (InfiniteSize,_) => InfiniteSize
      case (_,InfiniteSize) => InfiniteSize
      case (FiniteSize(n),FiniteSize(m)) => FiniteSize(scala.math.pow(m+1, n).toInt)
    }
    case OptionType(base) => domainSize(base) match {
      case InfiniteSize => InfiniteSize
      case FiniteSize(n) => FiniteSize(n+1)
    }
    case c: ClassType => InfiniteSize
  }

  case object Untyped extends TypeTree
  case object AnyType extends TypeTree
  case object NoType extends TypeTree // This is the type of errors (ie. subtype of anything)
  case object BooleanType extends TypeTree
  case object Int32Type extends TypeTree

  case class ListType(base: TypeTree) extends TypeTree
  case class TupleType(bases: Seq[TypeTree]) extends TypeTree { lazy val dimension: Int = bases.length }
  case class SetType(base: TypeTree) extends TypeTree
  case class MultisetType(base: TypeTree) extends TypeTree
  case class MapType(from: TypeTree, to: TypeTree) extends TypeTree
  case class OptionType(base: TypeTree) extends TypeTree

  sealed abstract class ClassType extends TypeTree {
    val classDef: ClassTypeDef
    val id: Identifier = classDef.id
  }
  case class AbstractClassType(classDef: AbstractClassDef) extends ClassType
  case class CaseClassType(classDef: CaseClassDef) extends ClassType

  def classDefToClassType(cd: ClassTypeDef): ClassType = cd match {
    case a: AbstractClassDef => AbstractClassType(a)
    case c: CaseClassDef => CaseClassType(c)
  }
}

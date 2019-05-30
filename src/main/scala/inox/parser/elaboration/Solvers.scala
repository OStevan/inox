package inox
package parser
package elaboration

import inox.parser.elaboration.type_graph.TypeGraphAnalysis

import scala.util.parsing.input.Position

trait Solvers { self: Constraints with SimpleTypes with IRs with ElaborationErrors with TypeGraphAnalysis =>

  import SimpleTypes._
  import TypeClasses._
  import Constraints._

  def solve(constraints: Seq[Constraint]): Either[ErrorMessage, Unifier] = {

    case class UnificationError(message: Seq[Position] => ErrorMessage, positions: Seq[Position]) extends Exception(message(positions))

    var unknowns: Set[Unknown] = Set()
    var remaining: Seq[Constraint] = constraints
    var typeClasses: Map[Unknown, TypeClass] = Map()
    var unifier: Unifier = Unifier.empty

    def unify(unknown: Unknown, value: Type) {

      typeClasses.get(unknown).foreach { tc =>
        remaining :+= HasClass(value, tc)
      }
      typeClasses -= unknown

      val singleton = Unifier(unknown -> value)

      typeClasses = singleton(typeClasses)
      remaining = singleton(remaining)

      unknowns -= unknown

      unifier += (unknown -> value)
    }

    def handle(constraint: Constraint): Unit = constraint match {
      case Exists(tpe) => tpe match {
        case u: Unknown => unknowns += u
        case _ => remaining ++= tpe.unknowns.map(Exists(_))
      }
      case Equals(tpe1, tpe2) => (tpe1, tpe2) match {
        case (u1: Unknown, u2: Unknown) => if (u1 != u2) unify(u1, u2) else unknowns += u1
        case (u1: Unknown, _) => if (!tpe2.contains(u1)) unify(u1, tpe2) else throw UnificationError(unificationImpossible(tpe1, tpe2), Seq(tpe1.pos, tpe2.pos))
        case (_, u2: Unknown) => if (!tpe1.contains(u2)) unify(u2, tpe1) else throw UnificationError(unificationImpossible(tpe1, tpe2), Seq(tpe1.pos, tpe2.pos))
        case (UnitType(), UnitType()) => ()
        case (IntegerType(), IntegerType()) => ()
        case (BitVectorType(signed1, size1), BitVectorType(signed2, size2)) if signed1 == signed2 && size1 == size2 => ()
        case (BooleanType(), BooleanType()) => ()
        case (StringType(), StringType()) => ()
        case (CharType(), CharType()) => ()
        case (RealType(), RealType()) => ()
        case (FunctionType(fs1, t1), FunctionType(fs2, t2)) if fs1.size == fs2.size => {
          remaining ++= fs1.zip(fs2).map { case (f1, f2) => Equals(f1, f2) }
          remaining :+= Equals(t1, t2)
        }
        case (TupleType(es1), TupleType(es2)) if es1.size == es2.size =>
          remaining ++= es1.zip(es2).map { case (e1, e2) => Equals(e1, e2) }
        case (MapType(f1, t1), MapType(f2, t2)) => {
          remaining :+= Equals(f1, f2)
          remaining :+= Equals(t1, t2)
        }
        case (SetType(e1), SetType(e2)) => remaining :+= Equals(e1, e2)
        case (BagType(e1), BagType(e2)) => remaining :+= Equals(e1, e2)
        case (ADTType(i1, as1), ADTType(i2, as2)) if i1 == i2 && as1.size == as2.size =>
          remaining ++= as1.zip(as2).map { case (a1, a2) => Equals(a1, a2) }
        case (TypeParameter(i1), TypeParameter(i2)) if i1 == i2 => ()
        case _ => throw UnificationError(unificationImpossible(tpe1, tpe2), Seq(tpe1.pos, tpe2.pos))
      }
      case HasClass(tpe, tc) => tpe match {
        case u: Unknown => {
          unknowns += u
          typeClasses.get(u) match {
            case None => typeClasses += (u -> tc)
            case Some(tc2) => tc.combine(tc2)(tpe) match {
              case None => throw UnificationError(incompatibleTypeClasses(tc, tc2), Seq(tpe.pos))
              case Some(cs) => {
                typeClasses -= u
                remaining ++= cs
              }
            }
          }
        }
        case _ => tc.accepts(tpe) match {
          case None => throw UnificationError(notMemberOfTypeClasses(tpe, tc), Seq(tpe.pos))
          case Some(cs) => remaining ++= cs
        }
      }
    }

    try {
      while (unknowns.nonEmpty || remaining.nonEmpty) {

        while (remaining.nonEmpty) {
          val constraint = remaining.head
          remaining = remaining.tail

          handle(constraint)
        }

        if (unknowns.nonEmpty) {
          val defaults = typeClasses.collect {
            case (u, Integral) => u -> IntegerType()
            case (u, Numeric) => u -> IntegerType()
          }.toSeq

          defaults.foreach {
            case (u, t) => remaining :+= Equals(u, t)
          }

          if (defaults.isEmpty) {
            throw UnificationError(ambiguousTypes, unknowns.toSeq.map(_.pos))
          }
        }
      }

      Right(unifier)
    }
    catch {
      case UnificationError(error, positions) =>
        val diagnosis = GraphDiagnosis.getInstance(constraints)

        try {
          val reasons = diagnosis.getSuggestions(diagnosis.getUnsatisfiablePaths())
          Left(reasons.toErrorMessage())
        } catch {
          case e: Exception =>
            Left(error(positions))
        } finally {
          Left(error(positions))
        }

    }
  }
}
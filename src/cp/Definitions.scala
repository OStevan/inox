package cp

object Definitions {
  import Constraints._

  class spec extends StaticAnnotation

  final class NotImplementedException extends Exception

  final class UnsatisfiableConstraintException extends Exception
  final class UnknownConstraintException extends Exception

  sealed class Optimizable(val property : Boolean) {
    def maximizing(expr : Any) = {
      property
    }

    def minimizing(expr : Any) = {
      property
    }
  }

  implicit def any2Optimizable(x : Boolean) : Optimizable = new Optimizable(x)

  implicit def pred2cons1[A](pred : A => Boolean) : Constraint1[A] = throw new NotImplementedException
  implicit def pred2cons2[A,B](pred : (A,B) => Boolean) : Constraint2[A,B] = throw new NotImplementedException

  def choose[A](constraint : Constraint1[A]) : A = {
    throw new NotImplementedException()
  }

  def choose[A,B](constraint : Constraint2[A,B]) : (A,B) = {
    throw new NotImplementedException()
  }

  def choose[A,B,C](pred : (A,B,C) => Boolean) : (A,B,C) = {
    throw new NotImplementedException()
  }

  def choose[A,B,C,D](pred : (A,B,C,D) => Boolean) : (A,B,C,D) = {
    throw new NotImplementedException()
  }

  def choose[A,B,C,D,E](pred : (A,B,C,D,E) => Boolean) : (A,B,C,D,E) = {
    throw new NotImplementedException()
  }

  def choose[A,B,C,D,E,F](pred : (A,B,C,D,E,F) => Boolean) : (A,B,C,D,E,F) = {
    throw new NotImplementedException()
  }

  def choose[A,B,C,D,E,F,G](pred : (A,B,C,D,E,F,G) => Boolean) : (A,B,C,D,E,F,G) = {
    throw new NotImplementedException()
  }

  def choose[A,B,C,D,E,F,G,H](pred : (A,B,C,D,E,F,G,H) => Boolean) : (A,B,C,D,E,F,G,H) = {
    throw new NotImplementedException()
  }

  def choose[A,B,C,D,E,F,G,H,I](pred : (A,B,C,D,E,F,G,H,I) => Boolean) : (A,B,C,D,E,F,G,H,I) = {
    throw new NotImplementedException()
  }

  def choose[A,B,C,D,E,F,G,H,I,J](pred : (A,B,C,D,E,F,G,H,I,J) => Boolean) : (A,B,C,D,E,F,G,H,I,J) = {
    throw new NotImplementedException()
  }

  def find[A](pred : A => Boolean) : Option[A] = {
    throw new NotImplementedException()
  }

  def find[A,B](pred : (A,B) => Boolean) : Option[(A,B)] = {
    throw new NotImplementedException()
  }

  def find[A,B,C](pred : (A,B,C) => Boolean) : Option[(A,B,C)] = {
    throw new NotImplementedException()
  }

  def find[A,B,C,D](pred : (A,B,C,D) => Boolean) : Option[(A,B,C,D)] = {
    throw new NotImplementedException()
  }

  def find[A,B,C,D,E](pred : (A,B,C,D,E) => Boolean) : Option[(A,B,C,D,E)] = {
    throw new NotImplementedException()
  }

  def find[A,B,C,D,E,F](pred : (A,B,C,D,E,F) => Boolean) : Option[(A,B,C,D,E,F)] = {
    throw new NotImplementedException()
  }

  def find[A,B,C,D,E,F,G](pred : (A,B,C,D,E,F,G) => Boolean) : Option[(A,B,C,D,E,F,G)] = {
    throw new NotImplementedException()
  }

  def find[A,B,C,D,E,F,G,H](pred : (A,B,C,D,E,F,G,H) => Boolean) : Option[(A,B,C,D,E,F,G,H)] = {
    throw new NotImplementedException()
  }

  def find[A,B,C,D,E,F,G,H,I](pred : (A,B,C,D,E,F,G,H,I) => Boolean) : Option[(A,B,C,D,E,F,G,H,I)] = {
    throw new NotImplementedException()
  }

  def find[A,B,C,D,E,F,G,H,I,J](pred : (A,B,C,D,E,F,G,H,I,J) => Boolean) : Option[(A,B,C,D,E,F,G,H,I,J)] = {
    throw new NotImplementedException()
  }

  def findAll[A](pred : A => Boolean) : Iterator[A] = {
    throw new NotImplementedException()
  }

  def findAll[A,B](pred : (A,B) => Boolean) : Iterator[(A,B)] = {
    throw new NotImplementedException()
  }

  def findAll[A,B,C](pred : (A,B,C) => Boolean) : Iterator[(A,B,C)] = {
    throw new NotImplementedException()
  }

  def findAll[A,B,C,D](pred : (A,B,C,D) => Boolean) : Iterator[(A,B,C,D)] = {
    throw new NotImplementedException()
  }

  def findAll[A,B,C,D,E](pred : (A,B,C,D,E) => Boolean) : Iterator[(A,B,C,D,E)] = {
    throw new NotImplementedException()
  }

  def findAll[A,B,C,D,E,F](pred : (A,B,C,D,E,F) => Boolean) : Iterator[(A,B,C,D,E,F)] = {
    throw new NotImplementedException()
  }

  def findAll[A,B,C,D,E,F,G](pred : (A,B,C,D,E,F,G) => Boolean) : Iterator[(A,B,C,D,E,F,G)] = {
    throw new NotImplementedException()
  }

  def findAll[A,B,C,D,E,F,G,H](pred : (A,B,C,D,E,F,G,H) => Boolean) : Iterator[(A,B,C,D,E,F,G,H)] = {
    throw new NotImplementedException()
  }

  def findAll[A,B,C,D,E,F,G,H,I](pred : (A,B,C,D,E,F,G,H,I) => Boolean) : Iterator[(A,B,C,D,E,F,G,H,I)] = {
    throw new NotImplementedException()
  }

  def findAll[A,B,C,D,E,F,G,H,I,J](pred : (A,B,C,D,E,F,G,H,I,J) => Boolean) : Iterator[(A,B,C,D,E,F,G,H,I,J)] = {
    throw new NotImplementedException()
  }

  def distinct[A](args: A*) : Boolean = {
    args.toList.distinct.size == args.size
  }

}

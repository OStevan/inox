package inox.parser.graph_tests

import inox.parser.InterpolatorException
import org.scalatest.FunSuite

class ConstructorTests extends FunSuite {

  import inox.trees._
  import runTimeInterpolator._

  implicit val symbols = NoSymbols

    test("lambda type detected as wrong") {
      try {
        fd"def rep(n: Int): Int => Int = if (n == 0) lambda (x: Char) => x else lambda (x: Int) => x"
        fail("No errors detected, while there should be one")
      } catch {
        case InterpolatorException(text) =>
          assert(text.contains("graph"))
          println(text)
      }
    }

  test("Type of parameter and return type is wrong") {
    try {
      p"""
          def testFunction(a: Int, b: String, c: Char) = a

          def main(): Char = {
            let a = 1;
            let b = `b`;
            let c = `c`;
            testFunction(a, b, c)
          }
       """
      fail("There should be an error")
    } catch {
      case InterpolatorException(text) =>
        assert(text.contains("graph"))
        println(text)
    }
  }

  test("Type of a parameter is wrong") {
    try {
      p"""
          def testFunction(a: Int, b: String, c: Char) = a

          def main(): Char = {
            let a = 1;
            let b = `b`;
            let c = `c`;
            testFunction(a, b, c)
          }
       """
      fail("There should be an error")
    } catch {
      case InterpolatorException(text) =>
        assert(text.contains("graph"))
        println(text)
    }
  }

  test("ADT wrong type") {
    try {
      p"""
          type List[A] = Cons(head: A, tail: List[A]) | Nil()

          def size(xs: List[Int]): Integer =
          if (xs is Cons) 1 + size(xs.tail) else 0

          def main() = {
            let list = Cons(1, Cons('b', Nil()));
            size(list)
          }
        """
      fail("There should be an error")
    } catch {
      case InterpolatorException(text) =>
        assert(text.contains("graph"))
        println(text)
    }
  }

}
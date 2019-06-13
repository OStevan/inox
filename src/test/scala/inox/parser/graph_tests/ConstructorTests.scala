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

          def main(): Int = {
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

  test("Type of a argument is wrong") {
    try {
      p"""
          def testFunction(a: Int, b: String, c: Char) = a

          def main(): Int = {
            let a = 1;
            let b = `b`;
            let c = `c`;
            let d = 'blabla';
            let e = testFunction(a, b, c);
            testFunction(a, d, c)
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


  test("two distinct errors") {
    try {
      p"""
          type List[A] = Cons(head: A, tail: List[A]) | Nil()

          def insert(value: Int, list: List[Int]) = {
              if (list is Cons) {
                  if ('value' > list.head)
                    Cons(list.head, insert(value, list.tail))
                  else
                    Cons(value, list)
              } else
                Cons(value, list)
          }

          def sort(list: List[Int]) = {
            if (list is Cons) {
              insert(list.head, sort(list.tail))
            } else
              Nil()
          }

          def main() = {
            let list = Cons(2, Cons(3, Cons(-10, Cons(1, Cons(`a`, Cons(1000, Nil()))))));
            sort(list)
          }
        """
      fail("No errors detected, while there should be one")
    } catch {
      case InterpolatorException(text) =>
        assert(text.contains("graph"), text)
        println(text)
    }
  }

  test("conflict between type classes") {
    try {
      e"""
         (1)._1
       """
      fail("No errors detected, while there should be one")
    } catch {
      case InterpolatorException(text) =>
        assert(text.contains("graph"), text)
        println(text)
    }
  }

  test("conflict on constructors with") {
    try {
      e"""
         let x = 1;
         let y = Set(x);
         let z = Bag('stevan' -> 1);
         setUnion(y, z)
       """
      fail("No errors detected, while there should be one")
    } catch {
      case InterpolatorException(text) =>
        assert(text.contains("graph"), text)
        println(text)
    }
  }

  test("Type parameter test") {
    try {
      p"""
         def test[A](a: A): Int = a
       """
      fail("No errors detected, while there should be one")
    } catch {
      case InterpolatorException(text) =>
        assert(text.contains("graph"), text)
        println(text)
    }
  }

  test("error far apart") {
    try {
      p"""
         type List[A] = Cons(head: A, tail: List[A]) | Nil()

         def makeList[T](size: Int, generator: (() => T)): List[T] = {
             if (size == 0) Nil()
             else Cons(generator(), makeList(size - 1, generator))
         }

         def merge[T](first: List[T], second: List[T], selector:((List[T], List[T]) => (List[T], List[T]))): List[T] = {
             let result = selector(first, second);
             if (result._1 is Cons) Cons(result._1.head, merge(result._1.tail, result._2, selector))
             else result._2
         }

         def filter[T](list: List[T], test: ((T) => Boolean)) = {
             if (list is Nil) Nil()
             else
                 if (test(list.head)) Cons(test(list.head), filter(list.tail, test))
                 else filter(list.tail, test)
         }

         def sum(list: List[Int]) = {
             if (list is Nil) 0
             else list.head + sum(list.tail)
         }

          def main() = {
              let selector = lambda (first: List[Int], second: List[Int]) => {
                if (first is Nil) (second, first)
                else
                    if (second is Nil) (first, second)
                    else {
                        if (first.head > second.head) (first, second)
                        else (second, first)
                    }
              };
              let x = (x: Int) => x > 2;
              // imagine random
              let random = () => 6;
              let first = makeList[Int](100, random);
              let second = makeList[Int](200, random);
              let merged = merge[Int](first, second, selector);
              let filtered = filter(merged, x);
              let summed = sum(filtered);
              summed
          }
       """
      fail("No errors detected, while there should be one")
    } catch {
      case InterpolatorException(text) =>
        assert(text.contains("graph"), text)
        println(text)
    }
  }
}
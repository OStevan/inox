package inox.parser.graph_tests

import inox.parser.InterpolatorException
import org.scalatest.FunSuite

class ConstructorTests extends FunSuite {

  import inox.trees._
  import runTimeInterpolator._

  implicit val symbols = NoSymbols

   test("lambda type detected as wrong") {
     try {
       fd"def rep(n: Int): Int => Int = if (n == 0) lambda (x) => 'bla' else lambda (x: Char) => x"
       fail("No errors detected, while there should be one")
     } catch {
       case InterpolatorException(text) =>
         assert(text.contains("graph"))
         println(text)
     }
   }

}
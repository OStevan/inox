package inox.parser.graph_tests

import inox.parser.InterpolatorException
import org.scalatest.FunSuite

class SimpleTests extends FunSuite {

  import inox.trees._
  import runTimeInterpolator._
  implicit val symbols = NoSymbols

 test("conflict with user assigned type") {
   try {
     e"""let x: Int = 'bla';
        length(x)"""
     fail("No errors detected, while there should be one")
   } catch {
     case InterpolatorException(text) =>
       assert(text.contains("graph"))
       println(text)
   }
 }

  test("conflict in generated constraints") {
    try {
      e"""let x = 1;
        length(x)"""
      fail("No errors detected, while there should be one")
    } catch {
      case InterpolatorException(text) =>
        assert(text.contains("graph"))
        println(text)
    }
  }

  test("if expression branch result type conflicts") {
    try {
      e"""
         if (4>3) 0 else 'conflict'
       """
      fail("No errors detected, while there should be one")
    } catch {
      case InterpolatorException(text) =>
        assert(text.contains("graph"))
        println(text)
    }
  }

  test("user specified type changes the result of the above test") {
    try {
      e"""
         let x: String = if (4>3) 0 else 'conflict';
         x
       """
      fail("No errors detected, while there should be one")
    } catch {
      case InterpolatorException(text) =>
        assert(text.contains("graph"), text)
        println(text)
    }
  }

  test("type error based on the most likely case") {
    try {
      e"""
         let x = if (4>3) 0 else 'conflict';
         length(x)
       """
      fail("No errors detected, while there should be one")
    } catch {
      case InterpolatorException(text) =>
        assert(text.contains("graph"), text)
        println(text)
    }
  }
}

/* Copyright 2009-2016 EPFL, Lausanne */

package inox.utils

import scala.collection.mutable.Stack
import scala.collection.mutable.Builder
import scala.collection.mutable.ArrayBuffer
import scala.collection.{Iterable, IterableLike}

class IncrementalSeq[A] extends IncrementalState
                        with Iterable[A]
                        with IterableLike[A, Seq[A]]
                        with Builder[A, IncrementalSeq[A]] {

  private[this] val stack = new Stack[ArrayBuffer[A]]()
  stack.push(new ArrayBuffer())

  def clear() : Unit = {
    stack.clear()
    stack.push(new ArrayBuffer())
  }

  def reset(): Unit = {
    clear()
  }

  def push(): Unit = {
    stack.push(stack.head.clone)
  }

  def pop(): Unit = {
    stack.pop()
  }

  def iterator = stack.flatten.iterator
  def +=(e: A) = { stack.head += e; this }
  def -=(e: A) = { stack.head -= e; this }

  override def newBuilder = new scala.collection.mutable.ArrayBuffer()
  def result = this
}

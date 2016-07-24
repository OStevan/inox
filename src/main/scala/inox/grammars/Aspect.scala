/* Copyright 2009-2015 EPFL, Lausanne */

package inox
package grammars

/**
 * An Aspect applies to a label, and attaches information to it.
 *
 * For instance, the "size" aspect provides information about the size of
 * expressions the label represents, (displayed as |5|).
 *
 * Int|5| is thus a Label "Int" with aspect "Sized(5)". The applyTo method of
 * the aspect can filter/modify/generate sub-productions:
 * If the grammar contains a Int -> Int + Int production, then
 * Int|5| will generate productions by doing: |5|.applyTo(Int + Int),
 * which itself returns:
 *   - Int|1| + Int|3|
 *   - Int|3| + Int|1|
 *   - Int|2| + Int|2|
 *
 */

trait Aspects { self: GrammarsUniverse =>
  import program._
  import trees._

  trait Aspect extends Printable {
    final type Production = ProductionRule[Label, Expr]

    def applyTo(l: Label, ps: Seq[Production])(implicit ctx: InoxContext): Seq[Production]
  }
}

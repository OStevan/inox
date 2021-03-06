/* Copyright 2009-2018 EPFL, Lausanne */

package inox
package solvers
package combinators

trait PortfolioSolverFactory extends SolverFactory { self =>

  type S = PortfolioSolver with TimeoutSolver { val program: self.program.type }
  type SF <: SolverFactory { val program: self.program.type }

  val sfs: Seq[SF]

  def getNewSolver(): S = new {
    val program: self.program.type = self.program
    val solvers = sfs map (_.getNewSolver())
    val context = solvers.head.context
  } with PortfolioSolver with TimeoutSolver

  // Assumes s is a P/Solver with the correct subsolver types
  override def reclaim(s: S) = s perform {
    sfs.zip(s.solvers).foreach { case (sf, s) =>
      sf.reclaim(s.asInstanceOf[sf.S])
    }
  }

  val name = sfs.map(_.name).mkString("Pfolio(", ",", ")")
}

object PortfolioSolverFactory {
  def apply(p: Program)
           (factories: Seq[SolverFactory { val program: p.type; type S <: TimeoutSolver }]):
            PortfolioSolverFactory { val program: p.type; type S <: TimeoutSolver } = new {
    val program: p.type = p
    val sfs = factories
  } with PortfolioSolverFactory {
    type SF = SolverFactory { val program: p.type; type S <: TimeoutSolver }
  }
}

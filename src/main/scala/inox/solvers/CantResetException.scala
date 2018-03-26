/* Copyright 2009-2018 EPFL, Lausanne */

package inox.solvers

class CantResetException(s: AbstractSolver) extends Exception(s"Unable to reset solver $s")

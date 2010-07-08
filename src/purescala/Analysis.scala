package purescala

import Common._
import Definitions._
import Trees._
import TypeTrees._
import Extensions._

class Analysis(val program: Program) {
  // we always use the global reporter for this class
  val reporter = Settings.reporter
  // ...but not always for the extensions
  val extensionsReporter =
    if(Settings.quietExtensions) {
      Settings.quietReporter
    } else {
      Settings.reporter
    }

  // these extensions are always loaded, unless specified otherwise
  val defaultExtensions: Seq[Extension] =
    if(Settings.runDefaultExtensions) {
      (new Z3Solver(extensionsReporter)) :: Nil
    } else {
      Nil
    }

  // we load additional extensions
  val moreExtensions: Seq[Extension] = loadAll(extensionsReporter)
  if(!moreExtensions.isEmpty) {
    reporter.info("The following extensions are loaded:\n" + moreExtensions.toList.map(_.description).mkString("  ", "\n  ", ""))
  }
  // ...and split the final list between solvers and analysers
  val extensions: Seq[Extension] = defaultExtensions ++ moreExtensions
  val analysisExtensions: Seq[Analyser] = extensions.filter(_.isInstanceOf[Analyser]).map(_.asInstanceOf[Analyser])
  val solverExtensions: Seq[Solver] = extensions.filter(_.isInstanceOf[Solver]).map(_.asInstanceOf[Solver])

  // Calling this method will run all analyses on the program passed at
  // construction time. If at least one solver is loaded, verification
  // conditions are generated and passed to all solvers. Otherwise, only the
  // Analysis extensions are run on the program.
  def analyse : Unit = {
    if(solverExtensions.size > 0) {
      reporter.info("Running verification condition generation...")
      checkVerificationConditions
    } 

    analysisExtensions.foreach(ae => {
      reporter.info("Running analysis from extension: " + ae.description)
      ae.analyse(program)
    })
  }

  def checkVerificationConditions : Unit = {
    solverExtensions.foreach(_.setProgram(program))

    // Analysis should check that:
    //  - all the postconditions are implied by preconds. + body
    //  - all callsites satisfy the preconditions
    //  - all matches are exhaustive
    // In the future:
    //  - catamorphisms are catamorphisms (poss. with surjectivity conds.)
    //  - injective functions are injective
    //  - all global invariants are satisfied 
    for(funDef <- program.definedFunctions) if (Settings.functionsToAnalyse.isEmpty || Settings.functionsToAnalyse.contains(funDef.id.name)) {
      if(funDef.body.isDefined) {
        // val vc = postconditionVC(funDef)
        // slightly more costly:
        val vc = simplifyLets(postconditionVC(funDef))
        if(vc != BooleanLiteral(true)) {
          reporter.info("Verification condition (post) for ==== " + funDef.id + " ====")
          reporter.info(vc)
          // reporter.info("Negated:")
          // reporter.info(negate(vc))
          // reporter.info("Negated, expanded:")
          // val exp = expandLets(negate(vc))
          // reporter.info(exp)

          // try all solvers until one returns a meaningful answer
          solverExtensions.find(se => {
            reporter.info("Trying with solver: " + se.shortDescription)
            se.solve(vc) match {
              case None => false
              case Some(true) => reporter.info("==== VALID ===="); true
              case Some(false) => reporter.error("==== INVALID ===="); true
            }
          }) match {
            case None => reporter.warning("No solver could prove or disprove the verification condition.")
            case _ => 
          } 
        }
      } else {
        if(funDef.postcondition.isDefined) {
          reporter.warning(funDef, "Could not verify postcondition: function implementation is unknown.")
        }
      }
    } 
  }

  def postconditionVC(functionDefinition: FunDef) : Expr = {
    assert(functionDefinition.body.isDefined)
    val prec = functionDefinition.precondition
    val post = functionDefinition.postcondition
    val body = functionDefinition.body.get

    if(post.isEmpty) {
      BooleanLiteral(true)
    } else {
      val resFresh = FreshIdentifier("result", true).setType(body.getType)
      val bodyAndPost = Let(resFresh, body, replace(Map(ResultVariable() -> Variable(resFresh)), post.get))
      val withPrec = if(prec.isEmpty) {
        bodyAndPost
      } else {
        Implies(prec.get, bodyAndPost)
      }

      import Analysis._
      val (newExpr0, sideExprs0) = unrollRecursiveFunctions(program, withPrec, Settings.unrollingLevel)
      val expr0 = Implies(And(sideExprs0), newExpr0)
      val (newExpr1, sideExprs1) = rewriteSimplePatternMatching(expr0)
      val expr1 = Implies(And(sideExprs1), newExpr1)
      val (newExpr2, sideExprs2) = inlineFunctionsAndContracts(program, expr1)
      Implies(And(sideExprs2), newExpr2)
    }
  }

}

object Analysis {
  def inlineFunctionsAndContracts(program: Program, expr: Expr) : (Expr, Seq[Expr]) = {
    var extras : List[Expr] = Nil

    val isFunCall: Function[Expr,Boolean] = _.isInstanceOf[FunctionInvocation]
    def applyToCall(e: Expr) : Expr = e match {
      case f @ FunctionInvocation(fd, args) => {
        val fArgsAsVars: List[Variable] = fd.args.map(_.toVariable).toList
        val fParamsAsLetVars: List[Identifier] = fd.args.map(a => FreshIdentifier("arg", true).setType(a.tpe)).toList
        val fParamsAsLetVarVars = fParamsAsLetVars.map(Variable(_))
  
        def mkBigLet(ex: Expr) : Expr = (fParamsAsLetVars zip args).foldRight(ex)((iap, e) => {
          Let(iap._1, iap._2, e)
        })

        val substMap = Map[Expr,Expr]((fArgsAsVars zip fParamsAsLetVarVars) : _*)
        if(fd.hasPostcondition) {
          val newVar = Variable(FreshIdentifier("call", true)).setType(fd.returnType)
          extras = mkBigLet(And(
            replace(substMap + (ResultVariable() -> newVar), fd.postcondition.get),
            Equals(newVar, FunctionInvocation(fd, fParamsAsLetVarVars).setType(fd.returnType))
          )) :: extras
          newVar
        } else if(fd.hasImplementation && !program.isRecursive(fd)) { // means we can inline at least one level...
          mkBigLet(replace(substMap, fd.body.get))
        } else { // we can't do much for calls to recursive functions or to functions with no bodies
          f 
        }
      }
      case o => o
    }

    (searchAndApply(isFunCall, applyToCall, expr), extras.reverse)
  }

  def unrollRecursiveFunctions(program: Program, expression: Expr, times: Int) : (Expr,Seq[Expr]) = {
    var extras : List[Expr] = Nil

    def urf(expr: Expr, left: Int) : Expr = {
      def isRecursiveCall(e: Expr) = e match {
        case f @ FunctionInvocation(fd, _) if fd.hasImplementation && program.isRecursive(fd) => true
        case _ => false
      }
      def unrollCall(t: Int)(e: Expr) = e match {
        case f @ FunctionInvocation(fd, args) if fd.hasImplementation && program.isRecursive(fd) => {
          val newLetIDs = fd.args.map(a => FreshIdentifier(a.id.name, true).setType(a.tpe))
          val newLetVars = newLetIDs.map(Variable(_))
          val substs: Map[Expr,Expr] = Map((fd.args.map(_.toVariable) zip newLetVars) :_*)
          val bodyWithLetVars: Expr = replace(substs, fd.body.get)
          if(fd.hasPostcondition) {
            val post = fd.postcondition.get
            val newVar = Variable(FreshIdentifier("call", true)).setType(fd.returnType)
            val newExtra1 = Equals(newVar, bodyWithLetVars)
            val newExtra2 = replace(substs + (ResultVariable() -> newVar), post)
            val bigLet = (newLetIDs zip args).foldLeft(And(newExtra1, newExtra2))((e,p) => Let(p._1, p._2, e))
            extras = bigLet :: extras
            newVar
          } else {
            val bigLet = (newLetIDs zip args).foldLeft(bodyWithLetVars)((e,p) => Let(p._1, p._2, e))
            urf(bigLet, t-1)
          }
        }
        case o => o
      }

      if(left > 0)
        searchAndApply(isRecursiveCall, unrollCall(left), expr, false)
      else
        expr
    }

    val finalE = urf(expression, times)
    (finalE, extras.reverse)
  }

  // Rewrites pattern matching expressions where the cases simply correspond to
  // the list of constructors
  def rewriteSimplePatternMatching(expr: Expr) : (Expr, Seq[Expr]) = {
    var extras : List[Expr] = Nil

    def isPMExpr(e: Expr) : Boolean = {
      e.isInstanceOf[MatchExpr]
    }

    def rewritePM(e: Expr) : Expr = e.asInstanceOf[MatchExpr] match {
      case SimplePatternMatching(scrutinee, classType, casesInfo) => {
        val newVar = Variable(FreshIdentifier("pm", true)).setType(e.getType)
        val scrutAsLetID = FreshIdentifier("scrut", true).setType(scrutinee.getType)
        val lle : List[(Variable,List[Expr])] = casesInfo.map(cseInfo => {
          val (ccd, newPID, argIDs, rhs) = cseInfo
          val newPVar = Variable(newPID)
          val argVars = argIDs.map(Variable(_))
          val (rewrittenRHS, moreExtras) = rewriteSimplePatternMatching(rhs)
          (newPVar, List(Equals(newPVar, CaseClass(ccd, argVars)), Implies(Equals(Variable(scrutAsLetID), newPVar), Equals(newVar, rewrittenRHS))) ::: moreExtras.toList)
        }).toList
        val (newPVars, newExtras) = lle.unzip
        extras = Let(scrutAsLetID, scrutinee, And(Or(newPVars.map(Equals(Variable(scrutAsLetID), _))), And(newExtras.flatten))) :: extras
        newVar
      }
      case _ => e
    }
    
    val cleanerTree = searchAndApply(isPMExpr, rewritePM, expr) 
    (cleanerTree, extras.reverse)
  }

  object SimplePatternMatching {
    // (scrutinee, classtypedef, list((caseclassdef, variable, list(variable), rhs)))
    def unapply(e: MatchExpr) : Option[(Expr,ClassType,Seq[(CaseClassDef,Identifier,Seq[Identifier],Expr)])] = {
      val MatchExpr(scrutinee, cases) = e
      val sType = scrutinee.getType

      if(sType.isInstanceOf[AbstractClassType]) {
        val cCD = sType.asInstanceOf[AbstractClassType].classDef
        if(cases.size == cCD.knownChildren.size && cases.forall(!_.hasGuard)) {
          var seen = Set.empty[ClassTypeDef]
          
          var lle : List[(CaseClassDef,Identifier,List[Identifier],Expr)] = Nil
          for(cse <- cases) {
            cse match {
              case SimpleCase(CaseClassPattern(binder, ccd, subPats), rhs) if subPats.forall(_.isInstanceOf[WildcardPattern]) => {
                seen = seen + ccd

                val patID : Identifier = if(binder.isDefined) {
                  binder.get
                } else {
                  FreshIdentifier("cse", true).setType(CaseClassType(ccd))
                }

                val argIDs : List[Identifier] = (ccd.fields zip subPats.map(_.asInstanceOf[WildcardPattern])).map(p => if(p._2.binder.isDefined) {
                  p._2.binder.get
                } else {
                  FreshIdentifier("pat", true).setType(p._1.tpe)
                }).toList

                lle = (ccd, patID, argIDs, rhs) :: lle
              }
              case _ => ;
            }
          }
          lle = lle.reverse

          if(seen.size == cases.size) {
            Some((scrutinee, sType.asInstanceOf[AbstractClassType], lle))
          } else {
            None
          }
        } else {
          None
        }
      } else {
        val cCD = sType.asInstanceOf[CaseClassType].classDef
        if(cases.size == 1 && !cases(0).hasGuard) {
          val SimpleCase(pat,rhs) = cases(0).asInstanceOf[SimpleCase]
          pat match {
            case CaseClassPattern(binder, ccd, subPats) if (ccd == cCD && subPats.forall(_.isInstanceOf[WildcardPattern])) => {
              val patID : Identifier = if(binder.isDefined) {
                binder.get
              } else {
                FreshIdentifier("cse", true).setType(CaseClassType(ccd))
              }

              val argIDs : List[Identifier] = (ccd.fields zip subPats.map(_.asInstanceOf[WildcardPattern])).map(p => if(p._2.binder.isDefined) {
                p._2.binder.get
              } else {
                FreshIdentifier("pat", true).setType(p._1.tpe)
              }).toList

              Some((scrutinee, CaseClassType(cCD), List((cCD, patID, argIDs, rhs))))
            }
            case _ => None
          }
        } else {
          None
        }
      }
    }
  }
}

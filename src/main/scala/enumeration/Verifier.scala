package enumeration

import ast.{ASTNode}
import sygus.{Example, SMTProcess, SygusFileTask}

trait Verifier {
  def verify(prog: ASTNode, task: SygusFileTask): Option[Example]
}

class SMTVerifier(filename: String) extends Verifier {
  val source = scala.io.Source.fromFile(filename)
  val (smtOut, funcArgs, solution) = SMTProcess.toSMT(source.mkString)

  def verify(prog: ASTNode, task: SygusFileTask): Option[Example] = {
    val query = SMTProcess.getquery(prog.code, smtOut)
    val solverOut = SMTProcess.invokeCVC(query.stripMargin, SMTProcess.cvc4_Smt)
    if (solverOut.head == "sat")
    then Some(SMTProcess.getCEx(task, funcArgs, solverOut, solution))
    else None
  }
}

class PBEVanillaVerifier extends Verifier {
  def verify(prog: ASTNode, task: SygusFileTask): Option[Example] = {
    val badExamples = task.examples
      .zip(prog.values)
      .filter((exp, act) => exp.output != act)
      .map((exp, act) => exp)
    badExamples match
      case head :: next => Some(head)
      case Nil          => None
  }
}

class PBECegisVerifier(var cexBank: List[Example]) extends Verifier {
  def verify(prog: ASTNode, task: SygusFileTask): Option[Example] = {
    val (unsat, cex, newCexBank) = SMTProcess.getEx(task, cexBank, prog)
    cexBank = newCexBank
    if (unsat)
    then None
    else Some(cex)
  }
}

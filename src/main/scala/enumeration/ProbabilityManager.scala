package enumeration

import ast.*
import sygus.{SygusFileTask}
import enumeration.{ProbUpdate}

trait ProbabilityManager {
  def scoreProg(prog: ASTNode): Double
  def update(prog: ASTNode, task: SygusFileTask): Unit
  def lowerBoundProb(): Double
}

class ConstantProbManager (val prob: Double) extends ProbabilityManager {
  def scoreProg(prog: ASTNode): Double = prob 
  def update(prog: ASTNode, task: SygusFileTask): Unit = {}

  def lowerBoundProb(): Double = prob 
}

class ProbeProbManager(val task: SygusFileTask) extends ProbabilityManager {
  ProbUpdate.probMap = ProbUpdate.createProbMap(task.vocab)
  def scoreProg(prog: ASTNode): Double = {
    prog match {
      case (
        _: StringLiteral 
        | _: StringVariable
        | _: IntLiteral 
        | _: IntVariable
        | _: BoolLiteral 
        | _: BoolVariable
        | _: BVLiteral 
        | _: BVVariable
        ) => ProbUpdate.probMap((prog.getClass, Some(prog.code)))
      case _ => ProbUpdate.probMap((prog.getClass, None))
    }
  }

  def update(prog: ASTNode, task: SygusFileTask): Unit = {
    val examplesPassed = task.fitExs(prog)
    ProbUpdate.cache += (prog.code -> examplesPassed.toList.length)
    ProbUpdate.readjustCosts(task)
  }

  def lowerBoundProb(): Double = ProbUpdate.probMap.values.min // Could make more fine grained
}

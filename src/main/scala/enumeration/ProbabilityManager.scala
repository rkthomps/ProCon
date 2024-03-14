package enumeration

import ast.*
import sygus.{SygusFileTask}
import enumeration.{ProbUpdate}
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

trait ProbabilityManager {
  def scoreProg(prog: ASTNode): Double

  // Update probabilities and determine if we need to reset enumeration
  def update(prog: WeightedProgram, task: SygusFileTask): Boolean

  // Reset Enumeration
  def reset(task: SygusFileTask): Unit

  // Get the lowest possible probability
  def lowerBoundProb(nodeType: Class[? <: ASTNode]): Double
}

class ConstantProbManager(val prob: Double) extends ProbabilityManager {
  def scoreProg(prog: ASTNode): Double = prob
  def update(prog: WeightedProgram, task: SygusFileTask): Boolean = false
  def lowerBoundProb(nodeType: Class[? <: ASTNode]): Double = prob

  def reset(task: SygusFileTask): Unit = {}
}

class ProbeProbManager(val task: SygusFileTask, val batchSize: Int)
    extends ProbabilityManager {
  var uniformVal =
    1.0 / (task.vocab.leavesMakers.length + task.vocab.nodeMakers.length)
  val exampleSets = mutable.HashSet[Set[Any]]()
  val goodPastPrograms = ArrayBuffer[WeightedProgram]()
  // val batch = ArrayBuffer[WeightedProgram]()
  var maxCovered = 0 
  var probMap = ProbUpdate.createProbMap(task.vocab)
  // val curBatch: ArrayBuffer[WeightedProgram] = ArrayBuffer()
  def scoreProg(prog: ASTNode): Double = {
    prog match {
      case (
            _: StringLiteral | _: StringVariable | _: IntLiteral |
            _: IntVariable | _: BoolLiteral | _: BoolVariable | _: BVLiteral |
            _: BVVariable
          ) =>
        probMap((prog.getClass, Some(prog.code)))
      case _ => probMap((prog.getClass, None))
    }
  }

  def reset(task: SygusFileTask): Unit = {
     probMap = ProbUpdate.createProbMap(task.vocab)
     computeProbMap(task)
  }
  
  def computeProbMap(task: SygusFileTask): Unit = {
    for (prog <- goodPastPrograms) {
      val exampleFit = task.fit(prog.program)
      val (numFit, totalExamples) = exampleFit
      val fit: Double = (numFit.toFloat) / totalExamples

      val changed: Set[(Class[_], Option[Any])] =
        ProbUpdate.getAllNodeTypes(prog.program)

      for (changedNode <- changed) {
        val update = math.pow(uniformVal, (1 - fit))
        //val update = math.pow(probMap(changedNode), (1 - fit))
        if (probMap(changedNode) < update) {
          probMap += (changedNode -> update)
        }
      }
    }

    val probSum = probMap.map((_, v) => v).sum
    probMap = probMap.map((k, v) => (k -> v / probSum))
  }


  def update(prog: WeightedProgram, task: SygusFileTask): Boolean = {
    val exampleFit = task.fitExs(prog.program)
    if (!exampleSets.exists(eSet => exampleFit.subsetOf(eSet))) {
      exampleSets.add(exampleFit)
      goodPastPrograms += prog
      reset(task)
      true
    } else {
      false
    }
  }

  def lowerBoundProb(nodeType: Class[? <: ASTNode]): Double =
    probMap.filter((k, _) => k._1 == nodeType).map((_, v) => v).min
}

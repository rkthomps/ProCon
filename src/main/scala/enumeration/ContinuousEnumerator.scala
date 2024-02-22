package enumeration
import ast.{ASTNode, VocabFactory, VocabMaker, Types}
import sygus.SygusFileTask
import scala.collection.mutable.PriorityQueue
import scala.collection.mutable.Queue
import scala.collection.mutable.ArrayBuffer
import scala.annotation.meta.getter

case class WeightedProgram(
    val weight: Double,
    val program: ASTNode
) extends Ordered[WeightedProgram] {

  def compare(that: WeightedProgram): Int = {
    val weightCompare = -1 * this.weight.compare(that.weight)
    if (weightCompare == 0) {
      return -1 * this.program.hashCode().compare(that.program.hashCode())
    }
    return weightCompare 
  }
}

case class RuleEnumeratorResult(
    val weightedProgram: WeightedProgram,
    val subtermWeight: Double
)

case class SubtermCandidate(
    indices: List[Int],
    programs: List[ASTNode],
    weightSum: Double
) extends Ordered[SubtermCandidate] {
  def compare(that: SubtermCandidate): Int = {
    val weightCompare = -1 * this.weightSum.compare(that.weightSum)
    if (weightCompare == 0) {
      return -1 * this.indices.hashCode().compare(that.indices.hashCode())
    }
    return weightCompare
  }
}

class RuleEnumerator(
    val rule: VocabMaker,
    val probFn: ASTNode => Double,
    val contexts: List[Map[String, Any]]
) {

  val childQueues = rule.childTypes.map(_ => ArrayBuffer[WeightedProgram]())
  val candidateQueue = {
    val terminalCandidate = getTerminalCandidate()
    terminalCandidate match
      case None                   => PriorityQueue.empty[SubtermCandidate]
      case Some(subtermCandidate) => PriorityQueue(subtermCandidate)
  }

  def getTerminalCandidate(): Option[SubtermCandidate] = {
    if (rule.childTypes.length == 0)
    then Some(SubtermCandidate(List[Int](), List[ASTNode](), 0.0))
    else None
  }

  def getStartIndices(qIndex: Int, qLen: Int, numChildren: Int): List[Int] = {
    val prefix = List.fill(qIndex)(0)
    val suffix = List.fill(numChildren - qIndex - 1)(0)
    return prefix ++ (qLen - 1 :: suffix)
  }

  def getSubtermCandidate(
      subtermIndices: List[Int]
  ): Option[SubtermCandidate] = {
    if (subtermIndices.zip(childQueues).forall((i, q) => i < q.length))
    then {
      val weightedPrograms = subtermIndices.zip(childQueues).map((i, q) => q(i))
      val programs = weightedPrograms.map(_.program)
      val subtermWeight = weightedPrograms.map(_.weight).sum
      Some(SubtermCandidate(subtermIndices, programs, subtermWeight))
    } else None
  }

  def recieveProgram(newProgram: WeightedProgram): Unit = {
    for (((q, cType), i) <- childQueues.zip(rule.childTypes).zipWithIndex) {
      if (cType.equals(newProgram.program.nodeType)) {
        q += newProgram
        val zeros = List.fill(rule.childTypes.length)(0)
        val insertIndices = zeros.zipWithIndex.map((el, idx) =>
          if idx == i then q.length - 1 else el
        )
        val newCandidate = getSubtermCandidate(insertIndices)
        if (newCandidate.isDefined) {
          candidateQueue += newCandidate.get
        }
      }
    }
  }

  def tickAtIdx(l: List[Int], idx: Int): List[Int] = {
    l.zipWithIndex.map((el, i) => if i == idx then el + 1 else el)
  }

  def getNextCandidateIndices(curIndices: List[Int]): List[List[Int]] = {
    curIndices.zipWithIndex.map((_, i) => tickAtIdx(curIndices, i))
  }

  def nextProgram(): Option[RuleEnumeratorResult] = {
    if (candidateQueue.length == 0)
    then None
    else {
      val nextCandidate = candidateQueue.dequeue()
      for (nextIndices <- getNextCandidateIndices(nextCandidate.indices)) {
        val nextCandidate = getSubtermCandidate(nextIndices)
        if (nextCandidate.isDefined) {
          candidateQueue += nextCandidate.get
        }
      }
      val candidateProgram = rule.apply(nextCandidate.programs, contexts)
      val candidateWeight =
        -1 * math.log(probFn(candidateProgram)) + nextCandidate.weightSum
      Some(
        RuleEnumeratorResult(
          WeightedProgram(candidateWeight, candidateProgram),
          nextCandidate.weightSum
        )
      )
    }
  }
}

class ContinuousEnumerator(
    val vocab: VocabFactory,
    val oeManager: OEValuesManager,
    var task: SygusFileTask,
    val contexts: List[Map[String, Any]],
    val probFn: ASTNode => Double,
) extends Iterator[ASTNode] {

  // Queue of Complete, but overlooked programs.
  val candidateQueue = PriorityQueue.empty[WeightedProgram]
  val subtermGenerators =
    vocab.nodeMakers.map(m => RuleEnumerator(m, probFn, contexts)) ++ 
    vocab.leavesMakers.map(m => RuleEnumerator(m, probFn, contexts))
  loadQueue()

  override def hasNext: Boolean = 0 < candidateQueue.length

  override def next(): ASTNode = {
    val nextProg = candidateQueue.dequeue()
    for (g <- subtermGenerators) {
      g.recieveProgram(nextProg)
    }
    loadQueue()
    nextProg.program
  }

  def loadQueue(): Unit = {
    var bestCandidate: Option[WeightedProgram] =
      if (0 < candidateQueue.length)
      then Some(candidateQueue.head)
      else None
    for (subtermGen <- subtermGenerators) {
      var curCandidate = subtermGen.nextProgram()
      if (curCandidate.isDefined) {
        candidateQueue += curCandidate.get.weightedProgram
      }
      while (isConsiderable(curCandidate, bestCandidate)) {
        bestCandidate = Some(candidateQueue.head)
        curCandidate = subtermGen.nextProgram()
        if (curCandidate.isDefined) {
          candidateQueue += curCandidate.get.weightedProgram
        }
      }
    }
  }

  def isConsiderable(
      scrutinee: Option[RuleEnumeratorResult],
      curBest: Option[WeightedProgram]
  ): Boolean = {
    scrutinee match
      case None => false 
      case Some(scrutineeProg) =>
        curBest match
          case None => false
          case Some(bestProg) =>
            if (scrutineeProg.subtermWeight < bestProg.weight)
            then true 
            else false 
  }
}

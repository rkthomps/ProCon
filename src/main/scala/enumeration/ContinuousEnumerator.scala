package enumeration
import ast.{ASTNode, VocabFactory, VocabMaker, Types}
import enumeration.{Verifier, SMTVerifier, PBEVanillaVerifier, PBECegisVerifier, ProbabilityManager}
import scala.collection.mutable.PriorityQueue
import scala.collection.mutable.Queue
import scala.collection.mutable.ArrayBuffer
import scala.annotation.meta.getter
import sygus.{Example, SMTProcess, SygusFileTask}
import scala.collection.mutable

var fitsMap = mutable.Map[(Class[_], Option[Any]), Double]()

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
    val probManager: ProbabilityManager,
    val contexts: List[Map[String, Any]]
) {
  val childQueues = rule.childTypes.map(_ => ArrayBuffer[WeightedProgram]())
  val explored = mutable.HashSet[List[Int]]()
  val candidateQueue = {
    val terminalCandidate = getTerminalCandidate()
    terminalCandidate match
      case None                   => PriorityQueue.empty[SubtermCandidate]
      case Some(subtermCandidate) => {
        explored += subtermCandidate.indices
        PriorityQueue(subtermCandidate)
      }
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
          explored += insertIndices
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
        if (nextCandidate.isDefined && !explored.contains(nextIndices)) {
          candidateQueue += nextCandidate.get
          explored += nextIndices
        }
      }
      try {
        val candidateProgram = rule.apply(nextCandidate.programs, contexts)
        val candidateWeight =
          -1 * math.log(probManager.scoreProg(candidateProgram)) + nextCandidate.weightSum
        Some(
          RuleEnumeratorResult(
            WeightedProgram(candidateWeight, candidateProgram),
            nextCandidate.weightSum
          )
        )
      } catch {
        case e: ArithmeticException => None
      }
    }
  }
}

class ContinuousEnumerator(
    val filename: String,
    val vocab: VocabFactory,
    val oeManager: OEValuesManager,
    var task: SygusFileTask,
    var contexts: List[Map[String, Any]],
    val cegis: Boolean,
    val probManager: ProbabilityManager,
    val timeout: Int,
) extends Iterator[ASTNode] {

  // Queue of Complete, but overlooked programs.
  var candidateQueue = PriorityQueue.empty[WeightedProgram]
  var subtermGenerators =
    vocab.nodeMakers.map(m => RuleEnumerator(m, probManager, contexts)) ++
      vocab.leavesMakers.map(m => RuleEnumerator(m, probManager, contexts))
  val startTime = System.currentTimeMillis()

  val verifier = getVerifier()
  loadQueue()
  println("Initial q len " + candidateQueue.length)

  def restartEnumeration(): Unit = {
    oeManager.clear()
    fitsMap.clear()
    subtermGenerators =
      vocab.nodeMakers.map(m => RuleEnumerator(m, probManager, contexts)) ++
        vocab.leavesMakers.map(m => RuleEnumerator(m, probManager, contexts))
    candidateQueue = PriorityQueue.empty[WeightedProgram]
    loadQueue()
  }

  def getVerifier(): Verifier = {
    if task.isPBE
        then if cegis 
          then {
            val pbeCegisVerifier = PBECegisVerifier(task.examples)
            task.examples = List[Example]()
            contexts = task.examples.map(_.input).toList
            pbeCegisVerifier
          }
          else PBEVanillaVerifier()
        else SMTVerifier(filename)
  }

  override def hasNext: Boolean = 0 < candidateQueue.length

  override def next(): ASTNode = {
    var curProg = dequeueProgram()
    var curTime = System.currentTimeMillis()

    var numEnumerated = 1
    while (!isSolutionCandidate(curProg.program)) {
      //println(curProg.program.code + "Weight " + curProg.weight)
      curProg = dequeueProgram()
      numEnumerated += 1
      if (timeout < ((curTime - startTime) / 1e3) && (20 < numEnumerated)) {
        throw TimeoutException("Enumeration ran out of time.")
      }
      curTime = System.currentTimeMillis()
    }
    println(curProg.program.code + "; " + curProg.weight)
    val cexOption = verifier.verify(curProg.program, task)
    cexOption match
      case None => {
        curProg.program.unsat = true
        curProg.program
      }
      case Some(counterExample) => {
        task = task.updateContext(counterExample)
        contexts = task.examples.map(_.input).toList
        fitsMap = ProbUpdate.update(fitsMap, ArrayBuffer(curProg.program), task)
        restartEnumeration()
        curProg.program
      }
  }

  def dequeueProgram(): WeightedProgram = {
    var nextProg = candidateQueue.dequeue()
    while (0 < nextProg.program.values.length && !oeManager.isRepresentative(nextProg.program)) {
      loadQueue()
      nextProg = candidateQueue.dequeue()
    }
    loadQueue()
    
    for (g <- subtermGenerators) {
      g.recieveProgram(nextProg)
    }
    nextProg
  }

  def isSolutionCandidate(program: ASTNode): Boolean = {
    if (program.nodeType == task.functionReturnType)
      then task.examples.zip(program.values).map((exp, act) => exp.output == act).forall(identity)
      else false
  }


  def loadQueue(): Unit = {
    var bestCandidate: Option[WeightedProgram] =
      if (0 < candidateQueue.length)
      then Some(candidateQueue.head)
      else None
    for (subtermGen <- subtermGenerators) {
      var curCandidate = subtermGen.nextProgram()
      val toQueue = queueable(curCandidate) 
      if (toQueue.isDefined) {
        candidateQueue += toQueue.get
      }
      while (isConsiderable(curCandidate, bestCandidate)) {
        bestCandidate = Some(candidateQueue.head)
        curCandidate = subtermGen.nextProgram()
        val toQueue = queueable(curCandidate)
        if (toQueue.isDefined) {
          candidateQueue += toQueue.get
        }
      }
    }
  }

  def queueable(
      candidate: Option[RuleEnumeratorResult]
  ): Option[WeightedProgram] = {
    candidate match
      case None => None
      case Some(ruleEnumResult) => {
        if (oeManager.checkRepresentative(ruleEnumResult.weightedProgram.program))
          then Some(ruleEnumResult.weightedProgram)
          else None
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
          case Some(bestProg) => {
            val minPossibleWeight = -1 * math.log(probManager.lowerBoundProb())
            if (scrutineeProg.subtermWeight + minPossibleWeight < bestProg.weight)
            then true
            else false
          }
  }
}

class TimeoutException (val s: String) extends Exception(s) {}

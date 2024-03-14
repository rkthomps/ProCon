
import collection.JavaConverters._

import org.antlr.v4.runtime.{BufferedTokenStream, CharStreams}
import org.scalatestplus.junit.JUnitSuite
import org.junit.Assert._
import org.junit.Test

import ast.{ASTNode, Types}
import sygus.{SyGuSLexer, SyGuSParser, SygusFileTask}
import scala.compiletime.ops.boolean
import ast.Types.Bool
import ast.VocabMaker
import scala.collection.mutable.ArrayBuffer
import enumeration.ContinuousEnumerator
import enumeration.{Enumerator, InputsValuesManager, OEValuesManager, ConstantProbManager, ProbeProbManager}

class ContEnumTests extends JUnitSuite {
    // Assertions about scala vocab.
    @Test def testAssertions: Unit = {
        val grammar =
        """((ntInt Int (input))
            | (ntBool Bool (false))
            | (ntInt Int (0 1 (+ ntInt ntInt))
            | (ntBool Bool ((<= ntInt ntInt)))
            | (ntString String ((int.to.str ntInt))))
        """.stripMargin
        val parser = new SyGuSParser(new BufferedTokenStream(new SyGuSLexer(CharStreams.fromString(grammar))))
        val grammarDef = parser.grammarDef()
        val nonTerminals = grammarDef.groupedRuleList().asScala.map{nonTerminal =>
        nonTerminal.Symbol().getSymbol.getText -> Types.withName(nonTerminal.sort().getText)
        }.toMap
        val vocab = ast.VocabFactory(
        grammarDef.groupedRuleList().asScala.flatMap{nonTerminal => nonTerminal.gTerm().asScala.map(vocabElem =>
            SygusFileTask.makeVocabMaker(vocabElem, Types.withName(nonTerminal.sort().getText),nonTerminals))}.toList
        )
        assertTrue(vocab.leavesMakers.iterator.forall(l => l.arity == 0))
        assertTrue(vocab.nodeMakers.iterator.forall(l => 0 < l.arity))

        val arityMatchesChildren = (i: VocabMaker) => i.arity == i.childTypes.length 
        assertTrue(vocab.leavesMakers.forall(arityMatchesChildren))
        assertTrue(vocab.nodeMakers.forall(arityMatchesChildren))
    }

    @Test def testContEnum: Unit = {
        //val testFile = "src/test/benchmarks/easy/easy1.sl"
        //val testFile = "src/test/benchmarks/easy/easy2.sl"
        //val testFile = "src/test/benchmarks/easy/easy3.sl"
        //val testFile = "src/test/benchmarks/string/phone-5.sl"
        //val testFile = "src/test/benchmarks/string/stackoverflow10.sl"
        val testFile = "src/test/benchmarks/string/stackoverflow3.sl"
        //val testFile = "src/test/benchmarks/hackers-delight/hd-18.sl"
        val fileContents = scala.io.Source.fromFile(testFile).mkString
        val task = new SygusFileTask(fileContents)

        val oeManager = InputsValuesManager()
        val context = task.examples.map(_.input).toList
        //val probManager = ConstantProbManager(0.1)
        val probManager = ProbeProbManager(task, 1024) 
        val enumerator = new ContinuousEnumerator(testFile, task.vocab, oeManager, task, context, false, probManager, 20)

        var prevWeight = -1.0
        //var weight = enumerator.candidateQueue.head.weight
        var curProg = enumerator.next()
        while (!curProg.unsat && enumerator.hasNext) {
            curProg = enumerator.next()
        }
        if (curProg.unsat) {
            println("FOUND!!!")
            println(curProg.code)
        }
    }
}

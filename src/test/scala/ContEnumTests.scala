
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
import enumeration.{Enumerator, InputsValuesManager, OEValuesManager}


class DumbTest extends JUnitSuite {
    // Figure out how to write a test
    @Test def testOnePlusOne: Unit = {
        val j = 1
        val k = 1
        val l = j + k
        assertEquals(l, 2)
    }


    // My own assertions about scala vocab.
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
        val grammar =
         """|(set-logic SLIA)
            |(synth-fun f ((name String)) String
            |    ((Start String (ntString))
            |     (ntString String (name " " "."
            |(str.++ ntString ntString)
            |(str.replace ntString ntString ntString)
            |(str.at ntString ntInt)
            |(int.to.str ntInt)
            |(ite ntBool ntString ntString)
            |(str.substr ntString ntInt ntInt)
            |))
            |      (ntInt Int (0 1 2
            |(+ ntInt ntInt)
            |(- ntInt ntInt)
            |(str.len ntString)
            |(str.to.int ntString)
            |(str.indexof ntString ntString ntInt)
            |))
            |(ntBool Bool (true false
            |(= ntInt ntInt)
            |(str.prefixof ntString ntString)
            |(str.suffixof ntString ntString)
            |(str.contains ntString ntString)
            |))
            |))
            |(constraint (= (f "Nancy FreeHafer") "N.F."))
            |(constraint (= (f "Andrew Cencici") "A.C."))
            |(constraint (= (f "Jan Kotas") "J.K."))
            |(constraint (= (f "Mariya Sergienko") "M.S."))
            |
            |(check-synth)
          """.stripMargin
        val task = new SygusFileTask(grammar)

        val oeManager = new OEValuesManager {
            override def isRepresentative(program: ASTNode): Boolean = true
            override def clear(): Unit = {}
        }
        val context = task.examples.map(_.input).toList
        val enumerator = new ContinuousEnumerator(task.vocab, oeManager, task, context, _=>0.01)

        var prevWeight = -1.0
        var weight = enumerator.candidateQueue.head.weight
        for (prog <- enumerator.take(25)) {
            assert(prevWeight <= weight)
            println(weight + " " + prog.code)
            prevWeight = weight
            weight = enumerator.candidateQueue.head.weight
        }

    }
}

package keencompiler

import Parser.{Failure, Success, TokenCursor}

import scala.scalajs.js.JSApp
import scala.scalajs.js.annotation.JSExport

@JSExport
object Main extends JSApp {

    @JSExport
    def compile(program : String) : String = {
        val tokens = Tokenizer.tokenize(program)
        val cursor = TokenCursor(tokens, 3)
        val builder = new StringBuilder()
        Parser.parseProgram(cursor) match {
            case Success(parsed) =>
                //new TypeCheck().checkProgram(parsed)
                new Emitter({ s => builder.append(s); () }).emitProgram(parsed)
            case failure : Failure => throw failure
        }
        builder.toString()
    }

    def main() : Unit = {

    }

}

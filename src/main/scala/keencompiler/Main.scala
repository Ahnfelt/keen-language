package keencompiler

import Parser.{Failure, Success, TokenCursor}

import scala.scalajs.js.JSApp
import scala.scalajs.js.annotation.JSExport

@JSExport
object Main extends JSApp {

    @JSExport
    def compile(fullModuleName : String, program : String) : String = {
        val tokens = Tokenizer.tokenize(program)
        val cursor = TokenCursor(tokens, 3)
        val builder = new StringBuilder()
        Parser.parseProgram(fullModuleName, cursor) match {
            case Success(module) =>
                new TypeInference().checkProgram(module)
                new Emitter({ s => builder.append(s); () }).emitProgram(module)
            case failure : Failure => throw failure
        }
        builder.toString()
    }

    def main() : Unit = {

    }

}

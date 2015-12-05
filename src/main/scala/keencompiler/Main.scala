package keencompiler

import keencompiler.Parser.{Module, Failure, Success, TokenCursor}

import scala.scalajs.js
import scala.scalajs.js.JSApp
import scala.scalajs.js.annotation.JSExport

@JSExport
object Main extends JSApp {

    @JSExport
    def compile(fullModuleName : String, program : String) : String = {
        val builder = new StringBuilder()

        var seenModules = Map[String, Module]()

        def loadModule(moduleName : String, source : String) : Module = {
            val tokens = Tokenizer.tokenize(source)
            val cursor = TokenCursor(tokens, 3)
            Parser.parseModule(moduleName, cursor) match {
                case Success(module) =>
                    for(i <- module.importedModules if !seenModules.contains(moduleName)) { // TODO: Check cyclic dependencies
                        // TODO: This is such a hack. Make it asynchronous, less stringly typed and less insecure.
                        val escapedImportName = i.moduleName // TODO
                        val importSourceNullable = js.eval("""
                            var request = new XMLHttpRequest();
                            request.open('GET', '""" + escapedImportName + """' + '?' + new Date().getTime(), false);
                            request.send(null);
                            if(request.status === 200) {
                                request.responseText
                            } else {
                                null
                            }
                        """)
                        val importSource = Option(importSourceNullable.asInstanceOf[String]).getOrElse(throw new RuntimeException("Module not found: " + i.moduleName))
                        val loadedModule = loadModule(i.moduleName, importSource)
                        seenModules += (i.moduleName -> loadedModule)
                    }
                    new TypeInference(moduleName).checkModule(module, seenModules)
                    new Emitter({ s => builder.append(s); () }).emitModule(module)
                    Parser.qualifyModule(module)
                case failure : Failure => throw failure
            }
        }

        loadModule(fullModuleName, program)
        builder.toString()
    }

    @JSExport
    def f5() : Unit = {
        js.eval("""
            (function() {
                var done = false;
                try {
                    var compiled = keencompiler.Main().compile('_', "#import Main = 'keen/Main.keen'\nMain.main()");
                    done = true;
                    eval.call(window, compiled);
                } finally {
                    if(!done) window.onerror = function(e) {
                        var typePrefix = 'Uncaught java.lang.RuntimeException: ';
                        if(e.indexOf(typePrefix) == 0) e = e.slice(typePrefix.length);
                        var parsePrefix = 'Uncaught keencompiler.Parser$Failure: ';
                        if(e.indexOf(parsePrefix) == 0) e = e.slice(parsePrefix.length);
                        document.body.style.color = '#ff0000';
                        document.body.style.padding = '20px';
                        document.body.style.fontSize = '20px';
                        document.body.textContent = e;
                    };
                }
            })();
        """)
    }

    @JSExport
    override def main() : Unit = {}
}

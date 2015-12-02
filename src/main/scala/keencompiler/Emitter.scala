package keencompiler

import keencompiler.Parser._
import keencompiler.Tokenizer._

import scala.collection.mutable.ListBuffer

class Emitter(emit : String => Unit) {

    val reserved = """
        abstract	arguments	boolean	break	byte
        case	catch	char	class*	const
        continue	debugger	default	delete	do
        double	else	enum*	eval	export*
        extends*	false	final	finally	float
        for	function	goto	if	implements
        import*	in	instanceof	int	interface
        let	long	native	new	null
        package	private	protected	public	return
        short	static	super*	switch	synchronized
        this	throw	throws	transient	true
        try	typeof	var	void	volatile
        while	with	yield
    """.split("[^a-z]+").map(_.trim).filter(_.nonEmpty).toSet

    def mangle(name : String) = {
        if(reserved(name)) name + "_" else name
    }

    def mangleLabelDefinition(name : String) = {
        if(reserved(name)) escapeString(name) else name
    }

    def mangleLabelUsage(name : String) = {
        if(reserved(name) || !name.matches("[a-zA-Z][a-zA-Z0-9]*")) "[" + escapeString(name) + "]" else "." + name
    }

    def escapeString(value : String) = {
        "\"" + value + "\""
    }

    def emitPatternCondition(pattern : Pattern, path : String) : String = {
        val bindings = ListBuffer[String]()
        var emitted = false
        def and() = if(emitted) emit(" && ") else emitted = true
        def condition(pattern: Pattern, path : String) : Unit = pattern match {
            case WildcardPattern() =>
            case VariablePattern(name) =>
                bindings += "var " + mangle(name) + " = " + path + ";\n"
            case ConstructorPattern("True", List()) => // TODO: Better check
                and(); emit(path);
            case ConstructorPattern("False", List()) => // TODO: Better check
                and(); emit("!"); emit(path);
            case ConstructorPattern(name, fields) =>
                and(); emit(path); emit("._ == "); emit(escapeString(name))
                for(((label, p), i) <- fields.zipWithIndex) {
                    condition(p, path + mangleLabelUsage(label))
                }
            case ExtractPattern(name, alias) =>
                and(); emit(path); emit("._ == "); emit(escapeString(name))
                for(a <- alias) bindings += "var " + mangle(a) + " = " + path + ";\n"
            case RecordPattern(fields) =>
                for((label, p) <- fields) {
                    condition(p, path + mangleLabelUsage(label))
                }
            case ArrayPattern(elements) =>
                and(); emit(path); emit(".length == "); emit(elements.length.toString)
                for((element, i) <- elements.zipWithIndex) {
                    condition(element, path + "[" + i + "]")
                }
            case StringPattern(value) => and(); emit(path); emit(" == "); emit(escapeString(value))
            case IntegerPattern(value) => and(); emit(path); emit(" == "); emit(value.toString)
        }
        condition(pattern, path)
        if(!emitted) emit("true")
        bindings.mkString
    }

    def emitStatements(statements : List[Statement]) = {
        if(statements.nonEmpty) {
            for(s <- statements.init) emitStatement(s)
            statements.last match {
                case TermStatement(Record(List())) => // OK
                case TermStatement(term) => emit("return "); emitTerm(term)
                case statement => emitStatement(statement)
            }
        }
    }

    def emitTerm(term : Term) : Unit = {
        term match {
            case Variable(name) => emit(mangle(name))
            case Lambda(List((patterns, statements))) if patterns.forall(_.isInstanceOf[VariablePattern]) =>
                emit("(function(")
                for((VariablePattern(x), i) <- patterns.zipWithIndex) {
                    if(i != 0) emit(", ")
                    emit(mangle(x))
                }
                emit(") {\n")
                emitStatements(statements)
                emit("\n})")
            case Lambda(cases) =>
                emit("function(")
                for(i <- cases.head._1.indices) {
                    if(i != 0) emit(", ")
                    emit("_" + i)
                }
                emit(") {\n")
                for(((patterns, statements), i) <- cases.zipWithIndex) {
                    if(i != 0) emit(" else ")
                    emit("if(")
                    var bindings = ""
                    for((pattern, n) <- patterns.zipWithIndex) {
                        if(n != 0) emit(" && ")
                        bindings += emitPatternCondition(pattern, "_" + n)
                    }
                    emit(") {\n")
                    emit(bindings)
                    emitStatements(statements)
                    emit("\n}")
                }
                emit(" else {\n")
                emit("throw 'No match:'" + cases.head._1.indices.map(" + ' ' + _" + _).mkString)
                emit("\n}")
                emit("\n}")
            case Constructor("True", List()) => emit("true") // TODO: Better check
            case Constructor("False", List()) => emit("false") // TODO: Better check
            case Constructor(name, fields) =>
                emit("{_: ")
                emit(escapeString(name))
                for((label, p) <- fields) {
                    emit(", ")
                    emit(mangleLabelDefinition(label))
                    emit(": ")
                    emitTerm(p)
                }
                emit("}")
            case Call(function, List(Record(List()))) =>
                emitTerm(function)
                emit("()")
            case Call(function, parameters) =>
                emitTerm(function)
                emit("(")
                for((p, i) <- parameters.zipWithIndex) {
                    if(i != 0) emit(", ")
                    emitTerm(p)
                }
                emit(")")
            case Field(record, label) =>
                emitTerm(record)
                emit(mangleLabelUsage(label))
            case Record(List()) =>
                emit("(void 0)")
            case Record(fields) =>
                emit("{")
                for(((label, value), i) <- fields.zipWithIndex) {
                    if(i != 0) emit(", ")
                    emit(mangleLabelDefinition(label))
                    emit(": ")
                    emitTerm(value)
                }
                emit("}")
            case ArrayLiteral(elements) =>
                emit("[")
                for((element, i) <- elements.zipWithIndex) {
                    if(i != 0) emit(", ")
                    emitTerm(element)
                }
                emit("]")
            case JsCode(js) =>
                emit(js)
            case StringLiteral(value) =>
                emit(escapeString(value))
            case IntegerLiteral(value) =>
                emit(value.toString)
            case UnaryOperator(Bang(), operand) =>
                emit("(!")
                emitTerm(operand)
                emit(")")
            case UnaryOperator(Minus(), operand) =>
                emit("(-")
                emitTerm(operand)
                emit(")")
            case BinaryOperator(operator, left, right) =>
                emit("(")
                emitTerm(left)
                emit(" " + (operator match {
                    case Minus() => "-"
                    case Plus() => "+"
                    case DotDot() => "+"
                    case Slash() => "/"
                    case Star() => "*"
                    case AndAnd() => "&&"
                    case OrOr() => "||"
                    case LessThan() => "<"
                    case LessThanOrEqual() => "<="
                    case GreaterThan() => ">"
                    case GreaterThanOrEqual() => ">="
                    case NotEqualTo() => "!="
                    case EqualTo() => "=="
                }) + " ")
                emitTerm(right)
                emit(")")
        }
    }

    def emitStatement(statement : Statement) : Unit = {
        statement match {
            case SumTypeStatement(name, parameters, constructors) =>
                emit("// " + statement + "\n")
            case VariableStatement(name, ofType, value) =>
                for(t <- ofType) emit("// : " + t + "\n")
                emit("var " + mangle(name) + " = ")
                emitTerm(value)
                emit(";\n")
            case AssignStatement(term, operator, value) =>
                emitTerm(term)
                emit(" ")
                operator match {
                    case Equals() => emit("=")
                    case MinusEquals() => emit("-=")
                    case PlusEquals() => emit("+=")
                    case StarEquals() => emit("*=")
                }
                emit(" ")
                emitTerm(value)
                emit(";\n")
            case TermStatement(term) =>
                emitTerm(term)
                emit(";\n")
        }
    }

    def emitModule(module : Module) : Unit = {
        emit("(function(_global) {\n")
        for(m <- module.importedModules) {
            emit("var " + m.alias + " = _global.keen.modules" + mangleLabelUsage(m.moduleName) + ";\n")
        }
        for(s <- module.statements) emitStatement(s)
        emit("if(_global.keen == null) _global.keen = {modules: {}};\n")
        emit("_global.keen.modules" + mangleLabelUsage(module.fullName) + " = {\n")
        var first = true
        for(s <- module.exportedVariables) {
            if(!first) emit(",\n")
            emit(mangleLabelDefinition(s.name) + ": " + mangle(s.name))
            first = false
        }
        emit("\n};\n")
        emit("})(this);\n")
    }

    def main(args: Array[String]) {
        val tokens = tokenize(p2)
        val cursor = TokenCursor(tokens, 3)
        parseModule("ahnfelt/keen-base:source/Base.keen", cursor) match {
            case Success(program) => emitModule(program)
            case failure : Failure => throw failure
        }
        Thread.sleep(100)
    }

    val p2 = """
        js := (print = {|x| window.console.log(x)})
        each := {|array| {|body| array.forEach(body)}}
        each [1, 2, 3] {|i|
            js.print(i)
        }
    """

}

package keencompiler

import keencompiler.Tokenizer.{Position, Token}

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

object Parser {

    // Constraint kinds: t1 =:= t2, t1.l : t2
    // Using + etc. generates: t1.+ : t1 -> t1, which is only satisfiable by t1 = Float or t1 = Int.
    // Polymorphic fields, eg. t1.f : Int -> Int, t1.f : String -> String is reduced to t1.f : forall a. a -> a

    case class Module(
        fullName : String,
        exportedVariables : List[VariableStatement],
        exportedTypes : List[SumTypeStatement],
        statements : List[Statement]
    )

    sealed abstract class Type(var position : Position = null)
    case class FunctionType(parameters : List[Type], returns : Type) extends Type {
        override def toString = {
            val parametersString = parameters match {
                case List(p : FunctionType) => "(" + p.toString + ")"
                case List(p) => p.toString
                case _ => "(" + parameters.map(_.toString).mkString(", ") + ")"
            }
            parametersString + " -> " + returns.toString
        }
    }
    case class RigidType(name : String) extends Type { override def toString = name }
    case class NonRigidType(name : String) extends Type { override def toString = name }
    case class ConstantType(name : String, parameters : List[Type]) extends Type {
        override def toString = {
            val parametersString = parameters match { case List() => ""; case _ => "<" + parameters.map(_.toString).mkString(", ") + ">" }
            name + parametersString
        }
    }
    case class RecordType(fields : List[(String, Type)]) extends Type {
        override def toString = {
            "(" +
            (for((label, t) <- fields) yield label + " : " + t).mkString(", ") +
            ")"
        }
    }

    case class ConstructorDefinition(name : String, fields : List[(String, Type)])

    sealed abstract class Statement(var position : Position = null)
    case class SumTypeStatement(name : String, parameters : List[String], constructors : List[(String, List[(String, Scheme)])]) extends Statement
    case class VariableStatement(name : String, scheme : Option[Scheme], value : Term) extends Statement
    case class AssignStatement(term : Term, operator : Token, value : Term) extends Statement
    case class TermStatement(term : Term) extends Statement

    case class FieldConstraint(label : String, fieldType : Type)

    case class Scheme(parameters : List[String], fieldConstraints : List[(String, FieldConstraint)], generalType : Type) {
        override def toString : String = {
            generalType.toString +
                fieldConstraints.map { case (k, v) => " & " + k + "." + v.label + " : " + v.fieldType }.mkString
        }
    }

    sealed abstract class Pattern(var position : Position = null)
    case class WildcardPattern() extends Pattern
    case class VariablePattern(name : String) extends Pattern
    case class ExtractPattern(name : String, alias : Option[String]) extends Pattern
    case class ConstructorPattern(name : String, fields : List[(String, Pattern)]) extends Pattern
    case class RecordPattern(fields : List[(String, Pattern)]) extends Pattern
    case class ArrayPattern(elements : List[Pattern]) extends Pattern
    case class StringPattern(value : String) extends Pattern
    case class IntegerPattern(value : Long) extends Pattern

    sealed abstract class Term(var position : Position = null)
    case class Variable(name : String) extends Term
    case class Lambda(cases : List[(List[Pattern], List[Statement])]) extends Term
    case class Call(function : Term, parameters : List[Term]) extends Term
    case class Constructor(name : String, fields : List[(String, Term)]) extends Term
    case class Field(record : Term, label : String) extends Term
    case class Record(fields : List[(String, Term)]) extends Term
    case class ArrayLiteral(elements : List[Term]) extends Term
    case class StringLiteral(value : String) extends Term
    case class IntegerLiteral(value : Long) extends Term
    case class JsCode(js : String) extends Term
    case class UnaryOperator(operator : Token, operand : Term) extends Term
    case class BinaryOperator(operator : Token, left : Term, right : Term) extends Term

    case class TokenCursor(var tokens : Array[Token], var offset : Int) {
        def next() : Token = {
            val token = tokens(offset)
            offset += 1
            token
        }
        def previousLookBehind() : Token = {
            tokens(offset - 2)
        }
        def lookBehind() : Token = {
            tokens(offset - 1)
        }
        def lookAhead() : Token = {
            tokens(offset)
        }
        def nextLookAhead() : Token = {
            tokens(offset + 1)
        }
        def nextNextLookAhead() : Token = {
            tokens(offset + 2)
        }
    }

    sealed trait Result[+A]
    case class Failure(message : String, token : Option[Token]) extends RuntimeException(message + token.map(x => " at " + x.position + ", got: " + x).getOrElse("")) with Result[Nothing]
    case class Success[+A](value : A) extends Result[A]

    def require[A](either : Result[A]) = either match {
        case Success(result) => result
        case failure : Failure => throw failure
    }

    import Tokenizer._



    def leftAssociative(cursor : TokenCursor, descent : TokenCursor => Result[Term], operators : Token*) : Result[Term] = {
        val initial = require(descent(cursor))
        val list = ListBuffer[(Token, Term)]()
        while(operators.contains(cursor.lookAhead())) {
            val operator = cursor.next()
            val term = require(descent(cursor))
            list += (operator -> term)
        }
        Success(list.foldLeft(initial){ case (a, (o, b)) => BinaryOperator(o, a, b) })
    }

    def parsePatterns(cursor : TokenCursor) : Result[List[Pattern]] = {
        val initialPattern = require(parsePattern(cursor))
        val patterns = ListBuffer(initialPattern)
        while(cursor.lookAhead() == Comma()) {
            cursor.next()
            patterns += require(parsePattern(cursor))
        }
        Success(patterns.toList)
    }

    def parseRecordPattern(cursor : TokenCursor, skipLeftParenthesis : Boolean = false) : Result[RecordPattern] = {
        if(!skipLeftParenthesis && cursor.next() != LeftRound()) throw new Failure("Record must start with left parenthesis: '('", Some(cursor.lookBehind()))
        if(cursor.lookAhead() == RightRound()) {
            cursor.next()
            return Success(RecordPattern(List()))
        }
        (cursor.next(), cursor.next()) match {
            case (Lower(initialLabel), Equals()) =>
                val initial = require(parsePattern(cursor))
                val list = ListBuffer[(String, Pattern)](initialLabel -> initial)
                while (cursor.lookAhead() == Comma()) {
                    cursor.next()
                    val label = cursor.next() match {
                        case Lower(x) => x
                        case _ => return Failure("Expected label", Some(cursor.lookBehind()))
                    }
                    cursor.next() match {
                        case Equals() =>
                        case _ => return Failure("Expected equals sign: '='", Some(cursor.lookBehind()))
                    }
                    val pattern = require(parsePattern(cursor))
                    list += (label -> pattern)
                }
                if(cursor.next() != RightRound()) return Failure("Expected right parenthesis: ')'", Some(cursor.lookBehind()))
                Success(RecordPattern(list.toList))
            case _ =>
                throw new Failure("Expected record pattern", Some(cursor.lookBehind()))
        }
    }

    def parsePattern(cursor : TokenCursor) : Result[Pattern] = {
        (cursor.next(), cursor.lookAhead()) match {
            case (Upper(name), Lower(alias)) =>
                cursor.next()
                Success(ExtractPattern(name, Some(alias)))
            case (Upper(name), Underscore()) =>
                cursor.next()
                Success(ExtractPattern(name, None))
            case (Upper(name), LeftRound()) =>
                val record = if(cursor.lookAhead() == LeftRound()) require(parseRecordPattern(cursor)) else RecordPattern(List())
                Success(ConstructorPattern(name, record.fields))
            case (Upper(name), _) =>
                Success(ConstructorPattern(name, List()))
            case (LeftSquare(), _) =>
                if(cursor.lookAhead() == RightSquare()) {
                    cursor.next()
                    Success(ArrayPattern(List()))
                } else {
                    cursor.next()
                    val patterns = require(parsePatterns(cursor))
                    if(cursor.next() != RightSquare()) return Failure("Expected right bracket: ']'", Some(cursor.lookBehind()))
                    Success(ArrayPattern(patterns))
                }
            case (LeftRound(), _) =>
                if(cursor.lookAhead() == RightRound()) { cursor.next(); return Success(RecordPattern(List())) }
                (cursor.lookAhead(), cursor.nextLookAhead()) match {
                    case (Lower(initialLabel), Equals()) => parseRecordPattern(cursor, skipLeftParenthesis = true)
                    case _ =>
                        val pattern = parsePattern(cursor)
                        if(cursor.next() != RightRound()) return Failure("Expected right parenthesis: ')'", Some(cursor.lookBehind()))
                        pattern
                }
            case (Underscore(), _) => Success(WildcardPattern())
            case (Lower(name), _) => Success(VariablePattern(name))
            case (StringValue(value), _) => Success(StringPattern(value))
            case (IntegerValue(value), _) => Success(IntegerPattern(value))
            case (_, _) => Failure("Expected pattern", Some(cursor.lookBehind()))
        }
    }

    def parseLambda(cursor : TokenCursor) : Result[Term] = {
        if(cursor.next() != LeftCurly()) return Failure("Expected {...}", Some(cursor.lookBehind()))
        if(cursor.lookAhead() != Pipe()) {
            val statements = require(parseStatements(cursor))
            if(cursor.next() != RightCurly()) return Failure("Expected (...)", Some(cursor.lookBehind()))
            return Success(Lambda(List(List() -> statements)))
        }
        val list = ListBuffer[(List[Pattern], List[Statement])]()
        while(cursor.lookAhead() == Pipe()) {
            cursor.next()
            val patterns = require(parsePatterns(cursor))
            if(cursor.next() != Pipe()) return Failure("Expected pipe: '|'", Some(cursor.lookBehind()))
            val statements = require(parseStatements(cursor))
            list += (patterns.toList -> statements)
        }
        if(cursor.next() != RightCurly()) return Failure("Expected (...)", Some(cursor.lookBehind()))
        Success(Lambda(list.toList))
    }

    def parseArray(cursor : TokenCursor) : Result[Term] = {
        if(cursor.next() != LeftSquare()) return Failure("Expected [...]", Some(cursor.lookBehind()))
        if(cursor.lookAhead() == RightSquare()) {
            cursor.next()
            return Success(ArrayLiteral(List[Term]()))
        }
        val initial = require(parseTerm(cursor))
        val list = ListBuffer(initial)
        while(cursor.lookAhead() == Comma()) {
            cursor.next()
            val term = require(parseTerm(cursor))
            list += term
        }
        if(cursor.next() != RightSquare()) return Failure("Expected [...]", Some(cursor.lookBehind()))
        Success(ArrayLiteral(list.toList))
    }

    def parseRecord(cursor : TokenCursor, skipLeftParenthesis : Boolean = false) : Result[Record] = {
        if(!skipLeftParenthesis && cursor.next() != LeftRound()) throw new Failure("Record must start with left parenthesis: '('", Some(cursor.lookBehind()))
        if(cursor.lookAhead() == RightRound()) {
            cursor.next()
            return Success(Record(List()))
        }
        (cursor.next(), cursor.next()) match {
            case (Lower(initialLabel), Equals()) =>
                val initial = require(parseTerm(cursor))
                val list = ListBuffer[(String, Term)](initialLabel -> initial)
                while(cursor.lookAhead() == Comma()) {
                    cursor.next()
                    val label = cursor.next() match {
                        case Lower(x) => x
                        case _ => return Failure("Expected label", Some(cursor.lookBehind()))
                    }
                    cursor.next() match {
                        case Equals() =>
                        case _ => return Failure("Expected equals sign: '='", Some(cursor.lookBehind()))
                    }
                    val term = require(parseTerm(cursor))
                    list += (label -> term)
                }
                if(cursor.next() != RightRound()) return Failure("Expected right parenthesis: ')'", Some(cursor.lookBehind()))
                Success(Record(list.toList))
            case _ =>
                throw new Failure("Record expected", Some(cursor.previousLookBehind()))
        }
    }

    def parseParenthesis(cursor : TokenCursor) : Result[List[Term]] = {
        if(cursor.next() != LeftRound()) return Failure("Expected (...)", Some(cursor.lookBehind()))
        if(cursor.lookAhead() == RightRound()) { cursor.next(); return Success(List(Record(List()))) }
        (cursor.lookAhead(), cursor.nextLookAhead()) match {
            case (Lower(initialLabel), Equals()) => Success(List(require(parseRecord(cursor, skipLeftParenthesis = true))))
            case _ =>
                val initial = require(parseTerm(cursor))
                val list = ListBuffer[Term](initial)
                while(cursor.lookAhead() == Comma()) {
                    cursor.next()
                    val term = require(parseTerm(cursor))
                    list += term
                }
                if(cursor.next() != RightRound()) return Failure("Expected right parenthesis: ')'", Some(cursor.lookBehind()))
                Success(list.toList)
        }
    }

    def parseBrackets(cursor : TokenCursor) : Result[List[Term]] = {
        if(cursor.lookAhead() == LeftRound()) parseParenthesis(cursor)
        else if(cursor.lookAhead() == LeftSquare()) Success(List(require(parseArray(cursor))))
        else if(cursor.lookAhead() == LeftCurly()) Success(List(require(parseLambda(cursor))))
        else Failure("Expected (...), [...] or {...}", Some(cursor.lookAhead()))
    }

    def parseAtomic(cursor : TokenCursor) : Result[Term] = {
        cursor.lookAhead() match {
            case JsSnippet(js) => cursor.next(); Success(JsCode(js))
            case Lower(name) => cursor.next(); Success(Variable(name))
            case Upper(name) =>
                cursor.next()
                val parameters = if(cursor.lookAhead() == LeftRound()) require(parseRecord(cursor)) else Record(List())
                Success(Constructor(name, parameters.fields))
            case IntegerValue(value) => cursor.next(); Success(IntegerLiteral(value))
            case StringValue(value) => cursor.next(); Success(StringLiteral(value))
            case _ => require(parseBrackets(cursor)) match {
                case List(value) => Success(value)
                case _ => Failure("Unexpected parameter list", Some(cursor.lookAhead()))
            }
        }
    }

    def parseDots(cursor : TokenCursor) : Result[Term] = {
        val initial = require(parseAtomic(cursor))
        val list = ListBuffer[String]()
        while(cursor.lookAhead() == Dot()) {
            cursor.next()
            cursor.next() match {
                case Lower(name) => list += name
                case _ => return Failure("Expected field label", Some(cursor.lookBehind()))
            }
        }
        Success(list.foldLeft(initial){ case (a, b) => Field(a, b) })
    }

    def parseCall(cursor : TokenCursor) : Result[Term] = {
        val initial = require(parseDots(cursor))
        val list = ListBuffer[List[Term]]()
        while(cursor.lookAhead() == LeftRound() || cursor.lookAhead() == LeftSquare() || cursor.lookAhead() == LeftCurly()) {
            val term = require(parseBrackets(cursor))
            list += term
        }
        Success(list.foldLeft(initial){ case (a, b) => Call(a, b) })
    }

    def parseNegation(cursor : TokenCursor) : Result[Term] = {
        if(cursor.lookAhead() != Minus() && cursor.lookAhead() != Bang()) return parseCall(cursor)
        val operator = cursor.next()
        val term = require(parseCall(cursor))
        Success(UnaryOperator(operator, term))
    }

    def parseProduct(cursor : TokenCursor) : Result[Term] = leftAssociative(cursor, parseNegation, Star(), Slash())
    def parseSum(cursor : TokenCursor) : Result[Term] = leftAssociative(cursor, parseProduct, Plus(), Minus(), DotDot())
    def parseRelation(cursor : TokenCursor) : Result[Term] = leftAssociative(cursor, parseSum, EqualTo(), NotEqualTo(), LessThan(), LessThanOrEqual(), GreaterThan(), GreaterThanOrEqual())
    def parseAndOr(cursor : TokenCursor) : Result[Term] = leftAssociative(cursor, parseRelation, AndAnd(), OrOr())

    def parseTerm(cursor : TokenCursor) : Result[Term] = parseAndOr(cursor)

    def parseRecordType(cursor : TokenCursor, skipLeftParenthesis : Boolean = false) : Result[RecordType] = {
        if(!skipLeftParenthesis && cursor.next() != LeftRound()) throw new Failure("Record must start with left parenthesis: '('", Some(cursor.lookBehind()))
        if(cursor.lookAhead() == RightRound()) {
            cursor.next()
            return Success(RecordType(List()))
        }
        (cursor.next(), cursor.next()) match {
            case (Lower(initialLabel), Colon()) =>
                val initial = require(parseType(cursor))
                val list = ListBuffer[(String, Type)](initialLabel -> initial)
                while(cursor.lookAhead() == Comma()) {
                    cursor.next()
                    val label = cursor.next() match {
                        case Lower(x) => x
                        case _ => return Failure("Expected label", Some(cursor.lookBehind()))
                    }
                    cursor.next() match {
                        case Colon() =>
                        case _ => return Failure("Expected colon: ':'", Some(cursor.lookBehind()))
                    }
                    val term = require(parseType(cursor))
                    list += (label -> term)
                }
                if(cursor.next() != RightRound()) return Failure("Expected right parenthesis: ')'", Some(cursor.lookBehind()))
                Success(RecordType(list.toList))
            case _ =>
                throw new Failure("Expected record pattern", Some(cursor.previousLookBehind()))
        }
    }

    def parseParenthesisType(cursor : TokenCursor) : Result[List[Type]] = {
        if(cursor.next() != LeftRound()) return Failure("Expected (...)", Some(cursor.lookBehind()))
        if(cursor.lookAhead() == RightRound()) { cursor.next(); return Success(List(RecordType(List()))) }
        (cursor.lookAhead(), cursor.nextLookAhead()) match {
            case (Lower(initialLabel), Colon()) => Success(List(require(parseRecordType(cursor, skipLeftParenthesis = true))))
            case _ =>
                val initial = require(parseType(cursor))
                val list = ListBuffer[Type](initial)
                while(cursor.lookAhead() == Comma()) {
                    cursor.next()
                    val term = require(parseType(cursor))
                    list += term
                }
                if(cursor.next() != RightRound()) return Failure("Expected right parenthesis: ')'", Some(cursor.lookBehind()))
                Success(list.toList)
        }
    }

    def parseConstantType(cursor : TokenCursor) : Result[ConstantType] = {
        val name = cursor.next() match {
            case Upper(x) => x
            case _ => return Failure("Expected type constructor", Some(cursor.lookBehind()))
        }
        if(cursor.lookAhead() == LessThan()) {
            cursor.next()
            val parameter = require(parseType(cursor))
            val parameters = ListBuffer[Type](parameter)
            while(cursor.lookAhead() == Comma()) {
                cursor.next()
                parameters += require(parseType(cursor))
            }
            if(cursor.next() != GreaterThan()) throw new Failure("Expected '>'", Some(cursor.lookBehind()))
            Success(ConstantType(name, parameters.toList))
        } else {
            Success(ConstantType(name, List()))
        }
    }

    def parseConstructorDefinition(cursor : TokenCursor) : Result[ConstructorDefinition] = {
        val name = cursor.next() match {
            case Upper(x) => x
            case _ => return Failure("Expected type constructor", Some(cursor.lookBehind()))
        }
        if(cursor.lookAhead() != LeftRound()) {
            Success(ConstructorDefinition(name, List()))
        } else {
            val record = require(parseRecordType(cursor))
            Success(ConstructorDefinition(name, record.fields))
        }
    }

    def parseAtomicType(cursor : TokenCursor) : Result[List[Type]] = {
        cursor.lookAhead() match {
            case LeftRound() => parseParenthesisType(cursor)
            case Upper(_) => Success(List(require(parseConstantType(cursor))))
            case Lower(name) => cursor.next(); Success(List(RigidType(name)))
        }
    }

    def parseFunctionType(cursor : TokenCursor) : Result[Type] = {
        val parameters = require(parseAtomicType(cursor))
        if(cursor.lookAhead() != ArrowRight()) {
            if(parameters.length != 1) throw new Failure("Unexpected parameter list", Some(cursor.lookAhead()))
            return Success(parameters.head)
        }
        cursor.next()
        val returns = require(parseFunctionType(cursor))
        Success(FunctionType(parameters, returns))
    }

    def parseType(cursor : TokenCursor) : Result[Type] = parseFunctionType(cursor)

    def parseScheme(cursor : TokenCursor) : Result[Scheme] = {
        def free(inType : Type) : Set[String] = inType match {
            case FunctionType(parameters, returns) => parameters.flatMap(free).toSet ++ free(returns)
            case RigidType(name) => Set(name)
            case NonRigidType(name) => throw new RuntimeException("Unexpected non-rigid type in type annotation: " + name)
            case ConstantType(name, parameters) => parameters.flatMap(free).toSet
            case RecordType(fields) => fields.flatMap(f => free(f._2)).toSet
        }
        val generalType = require(parseType(cursor))
        var typeParameters = free(generalType)
        val fieldConstraints = ListBuffer[(String, FieldConstraint)]()
        while(cursor.lookAhead() == Ampersand()) {
            cursor.next()
            val record = cursor.next() match {
                case Lower(text) => text
                case _ => throw new Failure("Expected a lowercase type parameter", Some(cursor.lookBehind()))
            }
            if(cursor.next() != Dot()) throw new Failure("Expected a dot", Some(cursor.lookBehind()))
            val label = cursor.next() match {
                case Lower(text) => text
                case _ => throw new Failure("Expected a lowercase field", Some(cursor.lookBehind()))
            }
            if(cursor.next() != Colon()) throw new Failure("Expected a colon", Some(cursor.lookBehind()))
            val fieldType = require(parseType(cursor))
            typeParameters ++= (Set(record) ++ free(fieldType))
            fieldConstraints += (record -> FieldConstraint(label, fieldType))
        }
        Success(Scheme(typeParameters.toList.sorted, fieldConstraints.toList, generalType))
    }

    def parseSumTypeStatement(cursor : TokenCursor) : Result[SumTypeStatement] = {
        cursor.next() match {
            case Upper(name) =>
                val parameters = cursor.next() match {
                    case Colon() => List[String]()
                    case LessThan() =>
                        def nextParameter() = cursor.next() match {
                            case Lower(x) => x
                            case _ => throw new Failure("Expected a lowercase type parameter", Some(cursor.lookBehind()))
                        }
                        val initial = nextParameter()
                        val list = ListBuffer(initial)
                        while(cursor.lookAhead() == Comma()) {
                            cursor.next()
                            list += nextParameter()
                        }
                        if(cursor.next() != GreaterThan()) throw new Failure("Expected '>'", Some(cursor.lookBehind()))
                        if(cursor.next() != Colon()) throw new Failure("Expected ':'", Some(cursor.lookBehind()))
                        list.toList
                }
                if(cursor.next() != Equals()) throw new Failure("Expected '='", Some(cursor.lookBehind()))
                if(cursor.next() != LeftSquare()) throw new Failure("Expected '['", Some(cursor.lookBehind()))
                val constructors = ListBuffer[ConstructorDefinition]()
                if(cursor.lookAhead() != RightSquare()) {
                    constructors += require(parseConstructorDefinition(cursor))
                    while(cursor.lookAhead() == Comma()) {
                        cursor.next()
                        constructors += require(parseConstructorDefinition(cursor))
                    }
                }
                if(cursor.next() != RightSquare()) throw new Failure("Expected ']'", Some(cursor.lookBehind()))
                Success(SumTypeStatement(name, parameters, constructors.toList.map(t => t.name -> t.fields.map(f => f._1 -> Scheme(List(), List(), f._2)))))
            case _ =>
                Failure("Expected identifier followed by :", Some(cursor.lookBehind()))
        }
    }

    def parseVariableStatement(cursor : TokenCursor) : Result[VariableStatement] = {
        (cursor.next(), cursor.next()) match {
            case (Lower(name), Colon()) =>
                val scheme = if(cursor.lookAhead() != Equals()) Some(require(parseScheme(cursor))) else None
                if(cursor.next() != Equals()) throw new Failure("Expected '='", Some(cursor.lookBehind()))
                val value = require(parseTerm(cursor))
                Success(VariableStatement(name, scheme, value))
            case _ =>
                Failure("Expected identifier followed by :", Some(cursor.previousLookBehind()))
        }
    }

    def parseAssignStatement(cursor : TokenCursor) : Result[AssignStatement] = {
        val name = cursor.next() match {
            case Lower(x) => x
            case _ => throw new Failure("Expected an identifier followed by '='", Some(cursor.lookBehind()))
        }
        val o = cursor.next()
        if(!(o == Equals() || o == MinusEquals() || o == PlusEquals() || o == StarEquals())) throw new Failure("Expected an assignment operator, eg. '='", Some(cursor.lookBehind()))
        val value = require(parseTerm(cursor))
        Success(AssignStatement(Variable(name), o, value))
    }

    def parseStatement(cursor : TokenCursor) : Result[Statement] = {
        (cursor.lookAhead(), cursor.nextLookAhead(), cursor.nextNextLookAhead()) match {
            case (Upper(_), token, _) if token == LessThan() || token == Colon() => parseSumTypeStatement(cursor)
            case (Lower(_), Colon(), _) => parseVariableStatement(cursor)
            case (Lower(_), o, _) if o == Equals() || o == MinusEquals() || o == PlusEquals() || o == StarEquals() => parseAssignStatement(cursor)
            case (Sharp(_), _, _) => // Treat imports etc. as single line comments for now
                while(cursor.lookAhead() != LineBreak() && cursor.lookAhead() != OutsideFile()) cursor.next()
                cursor.next()
                parseStatement(cursor)
            case _ => Success(TermStatement(require(parseTerm(cursor))))
        }
    }

    def parseStatements(cursor : TokenCursor) : Result[List[Statement]] = {
        if(Seq(OutsideFile(), RightCurly(), Pipe()).contains(cursor.lookAhead())) return Success(List())
        val initial = require(parseStatement(cursor))
        val list = ListBuffer[Statement](initial)
        while(cursor.lookAhead() == LineBreak() || cursor.lookAhead() == SemiColon()) {
            cursor.next()
            val statement = require(parseStatement(cursor))
            list += statement
        }
        Success(list.toList)
    }

    def parseExport(cursor : TokenCursor) : (List[String], List[String], List[String]) = {
        val exportedVariables = ListBuffer[String]()
        val concreteTypes = ListBuffer[String]()
        val abstractTypes = ListBuffer[String]()
        def parseTypeExport(name : String) = {
            if(cursor.lookAhead() == LeftSquare()) {
                cursor.next()
                if(cursor.next() != RightSquare()) throw Failure("Expected right bracket: ]", Some(cursor.lookBehind()))
                abstractTypes += name
            } else {
                concreteTypes += name
            }
        }
        while(cursor.lookAhead().isInstanceOf[Sharp]) cursor.next() match {
            case Sharp("export") =>
                cursor.next() match {
                    case Lower(name) => exportedVariables += name
                    case Upper(name) => parseTypeExport(name)
                    case _ => throw Failure("Expected export symbol", Some(cursor.lookBehind()))
                }
                while(cursor.lookAhead() == Comma()) {
                    cursor.next()
                    cursor.next() match {
                        case Lower(name) => exportedVariables += name
                        case Upper(name) => parseTypeExport(name)
                        case _ => throw Failure("Expected export symbol", Some(cursor.lookBehind()))
                    }
                }
                val next = cursor.next()
                if(next != LineBreak() && next != OutsideFile()) throw Failure("Expected line break or comma", Some(next))
            case Sharp(keyword) =>
                throw Failure("Unknown keyword", Some(cursor.lookBehind()))
        }
        (exportedVariables.toList, concreteTypes.toList, abstractTypes.toList)
    }

    def parseProgram(fullModuleName : String, cursor : TokenCursor) : Result[Module] = {
        val exportedVariables = mutable.HashSet[String]()
        val concreteTypes = mutable.HashSet[String]()
        val abstractTypes = mutable.HashSet[String]()
        while(cursor.lookAhead().isInstanceOf[Sharp]) cursor.lookAhead() match {
            case Sharp("export") =>
                val (newExported, newConcrete, newAbstract) = parseExport(cursor)
                exportedVariables ++= newExported
                concreteTypes ++= newConcrete
                abstractTypes ++= newAbstract
            case Sharp(keyword) => throw Failure("Unknown keyword", Some(cursor.lookAhead()))
        }
        parseStatements(cursor) match {
            case failure : Failure => failure
            case _ if cursor.lookAhead() != OutsideFile() => Failure("Expected end of file", Some(cursor.lookAhead()))
            case Success(statements) =>
                val definedExportedVariables = statements.collect {
                    case s : VariableStatement if exportedVariables(s.name) => s
                }
                val definedExportedTypes = statements.collect {
                    case s : SumTypeStatement if concreteTypes.contains(s.name) => s
                    case s : SumTypeStatement if abstractTypes.contains(s.name) => s.copy(constructors = List())
                }
                val missingVariables = exportedVariables -- definedExportedVariables.map(_.name)
                if(missingVariables.nonEmpty) throw Failure("The following symbols were exported, but have no definition: " + missingVariables.mkString(","), None)
                val missingTypes = (concreteTypes ++ abstractTypes) -- definedExportedTypes.map(_.name)
                if(missingTypes.nonEmpty) throw Failure("The following types were exported, but have no definition: " + missingTypes.mkString(","), None)
                Success(Module(
                    fullName = fullModuleName,
                    exportedVariables = definedExportedVariables,
                    exportedTypes = definedExportedTypes,
                    statements = statements
                ))
        }
    }


    def main(args: Array[String]) {
        val tokens = tokenize(p0)
        val cursor = TokenCursor(tokens, 3)
        println(parseProgram("ahnfelt/keen-base:source/Base.keen", cursor))
    }

    val p0 = """
        fac := {
            |1| 1
            |i| i * fac(i - 1)
        }
    """
}

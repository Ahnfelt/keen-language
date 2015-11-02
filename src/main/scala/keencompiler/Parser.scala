package keencompiler

import Tokenizer.Token

import scala.collection.mutable.ListBuffer

object Parser {

    // Constraint kinds: t1 =:= t2, t1.l : t2
    // Using + etc. generates: t1.+ : t1 -> t1, which is only satisfiable by t1 = Float or t1 = Int.
    // Polymorphic fields, eg. t1.f : Int -> Int, t1.f : String -> String is reduced to t1.f : forall a. a -> a

    sealed abstract class Type
    case class FunctionType(parameters : List[Type], returns : Type) extends Type
    case class VariableType(name : String) extends Type
    case class ConstructorType(name : String, fields : List[(String, Type)]) extends Type
    case class ConstantType(name : String, parameters : List[Type]) extends Type
    case class RecordType(fields : List[(String, Type)]) extends Type

    sealed abstract class Statement
    case class SumTypeStatement(name : String, parameters : List[String], constructors : List[(String, List[(String, Type)])]) extends Statement
    case class VariableStatement(constructor : Option[String], name : String, ofType : Option[Type], value : Term) extends Statement
    case class AssignStatement(term : Term, operator : Token, value : Term) extends Statement
    case class TermStatement(term : Term) extends Statement

    sealed abstract class Pattern
    case object WildcardPattern extends Pattern
    case class VariablePattern(name : String) extends Pattern
    case class ExtractPattern(name : String, alias : Option[String]) extends Pattern
    case class ConstructorPattern(name : String, fields : List[(String, Pattern)]) extends Pattern
    case class RecordPattern(fields : List[(String, Pattern)]) extends Pattern
    case class ArrayPattern(elements : List[Pattern]) extends Pattern
    case class StringPattern(value : String) extends Pattern
    case class IntegerPattern(value : Long) extends Pattern

    sealed abstract class Term
    case class Variable(name : String) extends Term
    case class Lambda(cases : List[(List[Pattern], List[Statement])]) extends Term
    case class Call(function : Term, parameters : List[Term]) extends Term
    case class Constructor(name : String, fields : List[(String, Term)]) extends Term
    case class Field(record : Term, label : String) extends Term
    case class Record(fields : List[(String, Term)]) extends Term
    case class ArrayLiteral(elements : List[Term]) extends Term
    case class StringLiteral(value : String) extends Term
    case class IntegerLiteral(value : Long) extends Term
    case class UnaryOperator(operator : Token, operand : Term) extends Term
    case class BinaryOperator(operator : Token, left : Term, right : Term) extends Term

    case class TokenCursor(var tokens : Array[Token], var offset : Int) {
        def next() : Token = {
            val token = tokens(offset)
            offset += 1
            token
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
    case class Failure(message : String) extends RuntimeException(message) with Result[Nothing]
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
        while(cursor.lookAhead() == Comma) {
            cursor.next()
            patterns += require(parsePattern(cursor))
        }
        Success(patterns.toList)
    }

    def parseRecordPattern(cursor : TokenCursor, skipLeftParenthesis : Boolean = false) : Result[RecordPattern] = {
        if(!skipLeftParenthesis && cursor.next() != LeftRound) throw new RuntimeException("Record must start with left parenthesis: '('")
        if(cursor.lookAhead() == RightRound) {
            cursor.next()
            return Success(RecordPattern(List()))
        }
        (cursor.next(), cursor.next()) match {
            case (Lower(initialLabel), Equals) =>
                val initial = require(parsePattern(cursor))
                val list = ListBuffer[(String, Pattern)](initialLabel -> initial)
                while (cursor.lookAhead() == Comma) {
                    cursor.next()
                    val label = cursor.next() match {
                        case Lower(x) => x
                        case _ => return Failure("Expected label")
                    }
                    cursor.next() match {
                        case Equals =>
                        case _ => return Failure("Expected equals sign: '='")
                    }
                    val pattern = require(parsePattern(cursor))
                    list += (label -> pattern)
                }
                if (cursor.next() != RightRound) return Failure("Expected right parenthesis: ')'")
                Success(RecordPattern(list.toList))
            case _ =>
                throw new RuntimeException("Expected record pattern.")
        }
    }

    def parsePattern(cursor : TokenCursor) : Result[Pattern] = {
        (cursor.next(), cursor.lookAhead()) match {
            case (Upper(name), Lower(alias)) =>
                cursor.next()
                Success(ExtractPattern(name, Some(alias)))
            case (Upper(name), Underscore) =>
                cursor.next()
                Success(ExtractPattern(name, None))
            case (Upper(name), LeftRound) =>
                val record = if(cursor.lookAhead() == LeftRound) require(parseRecordPattern(cursor)) else RecordPattern(List())
                Success(ConstructorPattern(name, record.fields))
            case (Upper(name), _) =>
                Success(ConstructorPattern(name, List()))
            case (LeftSquare, _) =>
                if(cursor.lookAhead() == RightSquare) {
                    cursor.next()
                    Success(ArrayPattern(List()))
                } else {
                    cursor.next()
                    val patterns = require(parsePatterns(cursor))
                    if(cursor.next() != RightSquare) return Failure("Expected right bracket: ']'")
                    Success(ArrayPattern(patterns))
                }
            case (LeftRound, _) =>
                if(cursor.lookAhead() == RightRound) { cursor.next(); return Success(RecordPattern(List())) }
                (cursor.lookAhead(), cursor.nextLookAhead()) match {
                    case (Lower(initialLabel), Equals) => parseRecordPattern(cursor, skipLeftParenthesis = true)
                    case _ =>
                        val pattern = parsePattern(cursor)
                        if(cursor.next() != RightRound) return Failure("Expected right parenthesis: ')'")
                        pattern
                }
            case (Underscore, _) => Success(WildcardPattern)
            case (Lower(name), _) => Success(VariablePattern(name))
            case (StringValue(value), _) => Success(StringPattern(value))
            case (IntegerValue(value), _) => Success(IntegerPattern(value))
            case (_, _) => Failure("Expected pattern")
        }
    }

    def parseLambda(cursor : TokenCursor) : Result[Term] = {
        if(cursor.next() != LeftCurly) return Failure("Expected {...}")
        if(cursor.lookAhead() != Pipe) {
            val statements = require(parseStatements(cursor))
            if(cursor.next() != RightCurly) return Failure("Expected (...)")
            return Success(Lambda(List(List() -> statements)))
        }
        val list = ListBuffer[(List[Pattern], List[Statement])]()
        while(cursor.lookAhead() == Pipe) {
            cursor.next()
            val patterns = require(parsePatterns(cursor))
            if(cursor.next() != Pipe) return Failure("Expected pipe: '|'")
            val statements = require(parseStatements(cursor))
            list += (patterns.toList -> statements)
        }
        if(cursor.next() != RightCurly) return Failure("Expected (...)")
        Success(Lambda(list.toList))
    }

    def parseArray(cursor : TokenCursor) : Result[Term] = {
        if(cursor.next() != LeftSquare) return Failure("Expected [...]")
        if(cursor.lookAhead() == RightSquare) {
            cursor.next()
            return Success(ArrayLiteral(List[Term]()))
        }
        val initial = require(parseTerm(cursor))
        val list = ListBuffer(initial)
        while(cursor.lookAhead() == Comma) {
            cursor.next()
            val term = require(parseTerm(cursor))
            list += term
        }
        if(cursor.next() != RightSquare) return Failure("Expected [...]")
        Success(ArrayLiteral(list.toList))
    }

    def parseRecord(cursor : TokenCursor, skipLeftParenthesis : Boolean = false) : Result[Record] = {
        if(!skipLeftParenthesis && cursor.next() != LeftRound) throw new RuntimeException("Record must start with left parenthesis: '('")
        if(cursor.lookAhead() == RightRound) {
            cursor.next()
            return Success(Record(List()))
        }
        (cursor.next(), cursor.next()) match {
            case (Lower(initialLabel), Equals) =>
                val initial = require(parseTerm(cursor))
                val list = ListBuffer[(String, Term)](initialLabel -> initial)
                while(cursor.lookAhead() == Comma) {
                    cursor.next()
                    val label = cursor.next() match {
                        case Lower(x) => x
                        case _ => return Failure("Expected label")
                    }
                    cursor.next() match {
                        case Equals =>
                        case _ => return Failure("Expected equals sign: '='")
                    }
                    val term = require(parseTerm(cursor))
                    list += (label -> term)
                }
                if(cursor.next() != RightRound) return Failure("Expected right parenthesis: ')'")
                Success(Record(list.toList))
            case _ =>
                throw new RuntimeException("Record expected")
        }
    }

    def parseParenthesis(cursor : TokenCursor) : Result[List[Term]] = {
        if(cursor.next() != LeftRound) return Failure("Expected (...)")
        if(cursor.lookAhead() == RightRound) { cursor.next(); return Success(List(Record(List()))) }
        (cursor.lookAhead(), cursor.nextLookAhead()) match {
            case (Lower(initialLabel), Equals) => Success(List(require(parseRecord(cursor, skipLeftParenthesis = true))))
            case _ =>
                val initial = require(parseTerm(cursor))
                val list = ListBuffer[Term](initial)
                while(cursor.lookAhead() == Comma) {
                    cursor.next()
                    val term = require(parseTerm(cursor))
                    list += term
                }
                if(cursor.next() != RightRound) return Failure("Expected right parenthesis: ')'")
                Success(list.toList)
        }
    }

    def parseBrackets(cursor : TokenCursor) : Result[List[Term]] = {
        if(cursor.lookAhead() == LeftRound) parseParenthesis(cursor)
        else if(cursor.lookAhead() == LeftSquare) Success(List(require(parseArray(cursor))))
        else if(cursor.lookAhead() == LeftCurly) Success(List(require(parseLambda(cursor))))
        else Failure("Expected (...), [...] or {...}")
    }

    def parseAtomic(cursor : TokenCursor) : Result[Term] = {
        cursor.lookAhead() match {
            case Lower(name) => cursor.next(); Success(Variable(name))
            case Upper(name) =>
                cursor.next()
                val parameters = if(cursor.lookAhead() == LeftRound) require(parseRecord(cursor)) else Record(List())
                Success(Constructor(name, parameters.fields))
            case IntegerValue(value) => cursor.next(); Success(IntegerLiteral(value))
            case StringValue(value) => cursor.next(); Success(StringLiteral(value))
            case _ => require(parseBrackets(cursor)) match {
                case List(value) => Success(value)
                case _ => Failure("Unexpected parameter list")
            }
        }
    }

    def parseDots(cursor : TokenCursor) : Result[Term] = {
        val initial = require(parseAtomic(cursor))
        val list = ListBuffer[String]()
        while(cursor.lookAhead() == Dot) {
            cursor.next()
            cursor.next() match {
                case Lower(name) => list += name
                case _ => return Failure("Expected field label")
            }
        }
        Success(list.foldLeft(initial){ case (a, b) => Field(a, b) })
    }

    def parseCall(cursor : TokenCursor) : Result[Term] = {
        val initial = require(parseDots(cursor))
        val list = ListBuffer[List[Term]]()
        while(cursor.lookAhead() == LeftRound || cursor.lookAhead() == LeftSquare || cursor.lookAhead() == LeftCurly) {
            val term = require(parseBrackets(cursor))
            list += term
        }
        Success(list.foldLeft(initial){ case (a, b) => Call(a, b) })
    }

    def parseNegation(cursor : TokenCursor) : Result[Term] = {
        if(cursor.lookAhead() != Minus && cursor.lookAhead() != Bang) return parseCall(cursor)
        val operator = cursor.next()
        val term = require(parseCall(cursor))
        Success(UnaryOperator(operator, term))
    }

    def parseProduct(cursor : TokenCursor) : Result[Term] = leftAssociative(cursor, parseNegation, Star, Slash)
    def parseSum(cursor : TokenCursor) : Result[Term] = leftAssociative(cursor, parseProduct, Plus, Minus)
    def parseRelation(cursor : TokenCursor) : Result[Term] = leftAssociative(cursor, parseSum, EqualTo, NotEqualTo, LessThan, LessThanOrEqual, GreaterThan, GreaterThanOrEqual)
    def parseAndOr(cursor : TokenCursor) : Result[Term] = leftAssociative(cursor, parseRelation, AndAnd, OrOr)

    def parseTerm(cursor : TokenCursor) : Result[Term] = parseAndOr(cursor)

    def parseRecordType(cursor : TokenCursor, skipLeftParenthesis : Boolean = false) : Result[RecordType] = {
        if(!skipLeftParenthesis && cursor.next() != LeftRound) throw new RuntimeException("Record must start with left parenthesis: '('")
        if(cursor.lookAhead() == RightRound) {
            cursor.next()
            return Success(RecordType(List()))
        }
        (cursor.next(), cursor.next()) match {
            case (Lower(initialLabel), Colon) =>
                val initial = require(parseType(cursor))
                val list = ListBuffer[(String, Type)](initialLabel -> initial)
                while(cursor.lookAhead() == Comma) {
                    cursor.next()
                    val label = cursor.next() match {
                        case Lower(x) => x
                        case _ => return Failure("Expected label")
                    }
                    cursor.next() match {
                        case Colon =>
                        case _ => return Failure("Expected colon: ':'")
                    }
                    val term = require(parseType(cursor))
                    list += (label -> term)
                }
                if(cursor.next() != RightRound) return Failure("Expected right parenthesis: ')'")
                Success(RecordType(list.toList))
            case _ =>
                throw new RuntimeException("Expected record pattern.")
        }
    }

    def parseParenthesisType(cursor : TokenCursor) : Result[List[Type]] = {
        if(cursor.next() != LeftRound) return Failure("Expected (...)")
        if(cursor.lookAhead() == RightRound) { cursor.next(); return Success(List(RecordType(List()))) }
        (cursor.lookAhead(), cursor.nextLookAhead()) match {
            case (Lower(initialLabel), Colon) => Success(List(require(parseRecordType(cursor, skipLeftParenthesis = true))))
            case _ =>
                val initial = require(parseType(cursor))
                val list = ListBuffer[Type](initial)
                while(cursor.lookAhead() == Comma) {
                    cursor.next()
                    val term = require(parseType(cursor))
                    list += term
                }
                if(cursor.next() != RightRound) return Failure("Expected right parenthesis: ')'")
                Success(list.toList)
        }
    }

    def parseConstantType(cursor : TokenCursor) : Result[ConstantType] = {
        val name = cursor.next() match {
            case Upper(x) => x
            case _ => return Failure("Expected type constructor")
        }
        if(cursor.lookAhead() == LessThan) {
            cursor.next()
            val parameter = require(parseType(cursor))
            val parameters = ListBuffer[Type](parameter)
            while(cursor.lookAhead() == Comma) {
                cursor.next()
                parameters += require(parseType(cursor))
            }
            if(cursor.next() != GreaterThan) throw new RuntimeException("Expected '>'.")
            Success(ConstantType(name, parameters.toList))
        } else {
            Success(ConstantType(name, List()))
        }
    }

    def parseConstructorType(cursor : TokenCursor) : Result[ConstructorType] = {
        val name = cursor.next() match {
            case Upper(x) => x
            case _ => return Failure("Expected type constructor")
        }
        if(cursor.lookAhead() != LeftRound) {
            Success(ConstructorType(name, List()))
        } else {
            val record = require(parseRecordType(cursor))
            Success(ConstructorType(name, record.fields))
        }
    }

    def parseAtomicType(cursor : TokenCursor) : Result[List[Type]] = {
        cursor.lookAhead() match {
            case LeftRound => parseParenthesisType(cursor)
            case Upper(_) => Success(List(require(parseConstantType(cursor))))
            case Lower(name) => cursor.next(); Success(List(VariableType(name)))
        }
    }

    def parseFunctionType(cursor : TokenCursor) : Result[Type] = {
        val parameters = require(parseAtomicType(cursor))
        if(cursor.lookAhead() != ArrowRight) {
            if(parameters.length != 1) throw new RuntimeException("Unexpected parameter list.")
            return Success(parameters.head)
        }
        cursor.next()
        val returns = require(parseFunctionType(cursor))
        Success(FunctionType(parameters, returns))
    }

    def parseType(cursor : TokenCursor) : Result[Type] = parseFunctionType(cursor)

    def parseSumTypeStatement(cursor : TokenCursor) : Result[SumTypeStatement] = {
        cursor.next() match {
            case Upper(name) =>
                val parameters = cursor.next() match {
                    case Colon => List[String]()
                    case LessThan =>
                        def nextParameter() = cursor.next() match {
                            case Upper(x) => x
                            case _ => throw new RuntimeException("Expected an uppercase type parameter")
                        }
                        val initial = nextParameter()
                        val list = ListBuffer(initial)
                        while(cursor.lookAhead() == Comma) {
                            cursor.next()
                            list += nextParameter()
                        }
                        if(cursor.next() != GreaterThan) throw new RuntimeException("Expected '>'")
                        if(cursor.next() != Colon) throw new RuntimeException("Expected ':'")
                        list.toList
                }
                if(cursor.next() != Equals) throw new RuntimeException("Expected '='")
                if(cursor.next() != LeftSquare) throw new RuntimeException("Expected '['")
                val constructors = ListBuffer[ConstructorType]()
                if(cursor.lookAhead() != RightSquare) {
                    constructors += require(parseConstructorType(cursor))
                    while(cursor.lookAhead() == Comma) {
                        cursor.next()
                        constructors += require(parseConstructorType(cursor))
                    }
                }
                if(cursor.next() != RightSquare) throw new RuntimeException("Expected ']'")
                Success(SumTypeStatement(name, parameters, constructors.toList.map(t => t.name -> t.fields)))
            case _ =>
                Failure("Expected identifier followed by :")
        }
    }

    def parseVariableStatement(cursor : TokenCursor) : Result[VariableStatement] = {
        (cursor.next(), cursor.next()) match {
            case (Lower(name), Colon) =>
                val valueType = if(cursor.lookAhead() != Equals) Some(require(parseType(cursor))) else None
                if(cursor.next() != Equals) throw new RuntimeException("Expected '='")
                val value = require(parseTerm(cursor))
                Success(VariableStatement(None, name, valueType, value))
            case (Upper(constructor), Lower(name)) =>
                if(cursor.next() != Colon) throw new RuntimeException("Expected ':'")
                val valueType = if(cursor.lookAhead() != Equals) Some(require(parseType(cursor))) else None
                if(cursor.next() != Equals) throw new RuntimeException("Expected '='")
                val value = require(parseTerm(cursor))
                Success(VariableStatement(Some(constructor), name, valueType, value))
            case _ =>
                Failure("Expected identifier followed by :")
        }
    }

    def parseAssignStatement(cursor : TokenCursor) : Result[AssignStatement] = {
        val name = cursor.next() match {
            case Lower(x) => x
            case _ => throw new RuntimeException("Expected an identifier followed by '='")
        }
        val o = cursor.next()
        if(!(o == Equals || o == MinusEquals || o == PlusEquals || o == StarEquals)) throw new RuntimeException("Expected an assignment operator, eg. '='")
        val value = require(parseTerm(cursor))
        Success(AssignStatement(Variable(name), o, value))
    }

    def parseStatement(cursor : TokenCursor) : Result[Statement] = {
        (cursor.lookAhead(), cursor.nextLookAhead(), cursor.nextNextLookAhead()) match {
            case (Upper(_), token, _) if token == LessThan || token == Colon => parseSumTypeStatement(cursor)
            case (Upper(_), Lower(_), Colon) => parseVariableStatement(cursor)
            case (Lower(_), Colon, _) => parseVariableStatement(cursor)
            case (Lower(_), o, _) if o == Equals || o == MinusEquals || o == PlusEquals || o == StarEquals => parseAssignStatement(cursor)
            case (Sharp(_), _, _) => // Treat imports etc. as single line comments for now
                while(cursor.lookAhead() != LineBreak && cursor.lookAhead() != OutsideFile) cursor.next()
                cursor.next()
                parseStatement(cursor)
            case _ => Success(TermStatement(require(parseTerm(cursor))))
        }
    }

    def parseStatements(cursor : TokenCursor) : Result[List[Statement]] = {
        if(Seq(OutsideFile, RightCurly, Pipe).contains(cursor.lookAhead())) return Success(List())
        val initial = require(parseStatement(cursor))
        val list = ListBuffer[Statement](initial)
        while(cursor.lookAhead() == LineBreak || cursor.lookAhead() == SemiColon) {
            cursor.next()
            val statement = require(parseStatement(cursor))
            list += statement
        }
        Success(list.toList)
    }

    def parseProgram(cursor : TokenCursor) : Result[List[Statement]] = {
        parseStatements(cursor) match {
            case failure : Failure => failure
            case _ if cursor.lookAhead() != OutsideFile => Failure("Expected end of file")
            case success => success
        }
    }


    def main(args: Array[String]) {
        val tokens = tokenize(p0)
        val cursor = TokenCursor(tokens, 3)
        println(parseProgram(cursor))
    }

    val p0 = """
        fac := {
            |1| 1
            |i| i * fac(i - 1)
        }
    """
}

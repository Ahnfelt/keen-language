package keencompiler

import keencompiler.Parser._

import scala.collection.mutable
import TypeCheck._

class TypeCheck {

    val variables = new Variables()
    val sumTypes = new SumTypes()

    def instantiate()

    def checkTerm(expected : Type, term : Term) = (expected, term) match {
        case (_, Variable(name)) => variables.get(name) match {
            case None => throw new RuntimeException("Undefined variable: " + name)
            case Some(scheme) =>
                // TODO: replace forall with "rigid" fresh variables
                if(expected != scheme.generalType) throw new RuntimeException("Expected type: " + expected + ", but got: " + scheme.generalType)
        }
        case (FunctionType(parameters, returns), Lambda(cases)) =>

        case (_, Call(function, parameters)) =>
        case (_, Constructor(name, fields)) =>
        case (_, Field(record, label)) =>
        case (RecordType(expectedFields), Record(fields)) =>
        case (_, ArrayLiteral(elements)) =>
        case (_, StringLiteral(value)) =>
        case (_, IntegerLiteral(value)) =>
        case (_, UnaryOperator(operator, operand)) =>
        case (_, BinaryOperator(operator, left, right)) =>
        case (_, _) =>
            throw new RuntimeException("Expected type: " + expected + ", but encountered: " + term)
    }

    def checkAssign(statement : AssignStatement) = {
    }

    def checkDefinition(statement : VariableStatement) = {
        // statement.constructor is not checked yet
        statement.ofType match {
            case Some(t) => checkTerm(t, statement.value)
            case None =>
        }
    }

    def checkSumTypeDefinition(statement : SumTypeStatement) = {
        if(sumTypes.get(statement.name).isDefined) throw new RuntimeException("Type already defined: " + statement.name)
        sumTypes.set(statement.name, statement)
    }

    def checkStatements(statements : List[Statement]) = {
        for(statement <- statements) statement match {
            case s : SumTypeStatement => checkSumTypeDefinition(s)
            case s : VariableStatement => checkDefinition(s)
            case s : AssignStatement => checkAssign(s)
            case TermStatement(term) => checkTerm(RecordType(List()), term)
        }
    }

    def checkProgram(program : List[Statement]) = {
        checkStatements(program)
    }

}

object TypeCheck {

    case class Scheme(parameters : List[String], generalType : Type)

    class Variables(map : mutable.HashMap[String, Scheme] = mutable.HashMap()) {
        def get(variable : String) : Option[Scheme] = map.get(variable)
        def set(variable : String, scheme : Scheme) = map.put(variable, scheme)
        def copy = new Variables(mutable.HashMap(map.toSeq : _*))
    }

    class SumTypes(map : mutable.HashMap[String, SumTypeStatement] = mutable.HashMap()) {
        def get(name : String) : Option[SumTypeStatement] = map.get(name)
        def set(name : String, statement : SumTypeStatement) = map.put(name, statement)
        def copy = new SumTypes(mutable.HashMap(map.toSeq : _*))
    }
}

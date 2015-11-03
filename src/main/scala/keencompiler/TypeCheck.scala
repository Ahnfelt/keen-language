package keencompiler

import keencompiler.Parser._

import scala.collection.mutable
import TypeCheck._

class TypeCheck {

    var variables = new Variables()
    var sumTypes = new SumTypes()

    def checkPattern(expected : Type, pattern : Pattern) : Unit = (expected, pattern) match {
        case (_, WildcardPattern) => // OK
        case (_, VariablePattern(name : String)) =>
            variables.set(name, Scheme(List(), expected))
        case (ConstantType(typeName, typeParameters), ExtractPattern(name : String, alias : Option[String])) =>
            sumTypes.get(typeName) match {
                case None => throw new RuntimeException("No constructor: " + name + ", of non-sum-type: " + expected)
                case Some(SumTypeStatement(_, expectedTypeParameters, constructors)) =>
                    constructors.find(_._1 == name) match {
                        case None => throw new RuntimeException("Unknown constructor: " + name + ", of type: " + typeName)
                        case Some((_, expectedFields)) =>
                            val extractedType = RecordType(expectedFields)
                            for(x <- alias) variables.set(x, Scheme(List(), extractedType))
                    }
            }
        case (ConstantType(typeName, typeParameters), ConstructorPattern(name : String, fields : List[(String, Pattern)])) =>
            sumTypes.get(typeName) match {
                case None => throw new RuntimeException("No constructor: " + name + ", of non-sum-type: " + expected)
                case Some(SumTypeStatement(_, expectedTypeParameters, constructors)) =>
                    constructors.find(_._1 == name) match {
                        case None => throw new RuntimeException("Unknown constructor: " + name + ", of type: " + typeName)
                        case Some((_, expectedFields)) =>
                            for(field <- fields) expectedFields.find(_._1 == field._1) match {
                                case None => throw new RuntimeException("Unknown field: " + field._1 + ", for constructor: " + name)
                                case Some((_, expectedType)) => checkPattern(expectedType, field._2)
                            }
                            if(expectedFields.length > fields.length) {
                                throw new RuntimeException("Missing fields: " + (expectedFields.map(_._1).toSet - fields.map(_._1)).mkString(", ") + ", for constructor: " + name)
                            }
                    }
            }
        case (RecordType(expectedFields), RecordPattern(fields : List[(String, Pattern)])) =>
            for(field <- fields) expectedFields.find(_._1 == field._1) match {
                case None => throw new RuntimeException("Unknown field: " + field._1)
                case Some((_, expectedType)) => checkPattern(expectedType, field._2)
            }
            if(expectedFields.length > fields.length) {
                throw new RuntimeException("Missing fields: " + (expectedFields.map(_._1).toSet - fields.map(_._1)).mkString(", "))
            }
        case (ConstantType("Array", List(elementType)), ArrayPattern(elements : List[Pattern])) =>
            for(element <- elements) checkPattern(elementType, element)
        case (ConstantType("String", List()), StringPattern(value : String)) => // OK
        case (ConstantType("Int", List()), IntegerPattern(value : Long)) => // OK
        case (_, _) =>
            throw new RuntimeException("Expected type: " + expected + ", but encountered: " + pattern)
    }

    def checkTerm(expected : Type, term : Term) : Unit = (expected, term) match {
        case (_, Variable(name)) => variables.get(name) match {
            case None => throw new RuntimeException("Undefined variable: " + name)
            case Some(scheme) =>
                // TODO: replace forall with "rigid" fresh variables
                if(expected != scheme.generalType) throw new RuntimeException("Expected type: " + expected + ", but got: " + scheme.generalType)
        }
        case (FunctionType(parameters, returns), Lambda(cases)) =>
            for((patterns, statements) <- cases) {
                if(parameters.length != patterns.length) throw new RuntimeException("Expected " + parameters.length + " patterns, but got " + patterns.length)
                val oldVariables = variables.copy
                // TODO: Check that variables do not occur twice in each case
                for((pattern, expectedType) <- patterns zip parameters) checkPattern(expectedType, pattern)
                checkStatements(returns, statements)
                variables = oldVariables
            }
        case (_, Call(Variable(name), parameters)) => // add support for all function terms
            variables.get(name) match {
                case None => throw new RuntimeException("Unknown variable: " + name)
                case Some(expectedScheme) =>
                    val functionType = expectedScheme.generalType // TODO
                    functionType match {
                        case FunctionType(parameterTypes, returnType) =>
                            for((t, p) <- parameterTypes zip parameters) checkTerm(t, p)
                            if(parameterTypes.length != parameters.length) throw new RuntimeException("Expected " + parameterTypes.length + " parameters, but got " + parameters.length)
                            if(expected != returnType) throw new RuntimeException("Expected type: " + expected + ", but got: " + returnType)
                        case _ => throw new RuntimeException("Can't call a non-function type: " + functionType)
                    }
            }
        case (ConstantType(typeName, typeParameters), Constructor(name, fields)) =>
            sumTypes.get(typeName) match {
                case None => throw new RuntimeException("No constructor: " + name + ", of non-sum-type: " + expected)
                case Some(SumTypeStatement(_, expectedTypeParameters, constructors)) =>
                    constructors.find(_._1 == name) match {
                        case None => throw new RuntimeException("Unknown constructor: " + name + ", of type: " + typeName)
                        case Some((_, expectedFields)) =>
                            for(field <- fields) expectedFields.find(_._1 == field._1) match {
                                case None => throw new RuntimeException("Unknown field: " + field._1 + ", for constructor: " + name)
                                case Some((_, expectedType)) => checkTerm(expectedType, field._2)
                            }
                            if(expectedFields.length > fields.length) {
                                throw new RuntimeException("Missing fields: " + (expectedFields.map(_._1).toSet - fields.map(_._1)).mkString(", ") + ", for constructor: " + name)
                            }
                    }
            }
        case (_, Field(Variable(name), label)) => // add support for all record terms
            variables.get(name) match {
                case None => throw new RuntimeException("Unknown variable: " + name)
                case Some(expectedScheme) =>
                    val recordType = expectedScheme.generalType // TODO
                    recordType match {
                        case RecordType(expectedFields) =>
                            expectedFields.find(_._1 == label) match {
                                case None => throw new RuntimeException("Unknown field: " + label)
                                case Some((_, actualType)) =>
                                    if(expected != actualType) throw new RuntimeException("Expected type: " + expected + ", but got: " + actualType)
                            }
                        case _ => throw new RuntimeException("Can't access field '" + label + "' of non-record type: " + recordType)
                    }
            }
        case (RecordType(expectedFields), Record(fields)) =>
            for(field <- fields) expectedFields.find(_._1 == field._1) match {
                case None => throw new RuntimeException("Unknown field: " + field._1)
                case Some((_, expectedType)) => checkTerm(expectedType, field._2)
            }
            if(expectedFields.length > fields.length) {
                throw new RuntimeException("Missing fields: " + (expectedFields.map(_._1).toSet - fields.map(_._1)).mkString(", "))
            }
        case (ConstantType("Array", List(elementType)), ArrayLiteral(elements)) => // the expected type is unqualified
            for(element <- elements) checkTerm(elementType, element)
        case (ConstantType("String", List()), StringLiteral(value)) => // OK
        case (ConstantType("Int", List()), IntegerLiteral(value)) => // OK
        case (ConstantType("Bool", List()), UnaryOperator(Tokenizer.Bang, operand)) =>
            checkTerm(ConstantType("Bool", List()), operand)
        case (ConstantType("Int", List()), UnaryOperator(Tokenizer.Minus, operand)) =>
            checkTerm(ConstantType("Int", List()), operand)
        case (ConstantType("Int", List()), BinaryOperator(token, left, right)) if Seq(Tokenizer.Minus, Tokenizer.Plus, Tokenizer.Star, Tokenizer.Slash).contains(token) =>
            checkTerm(ConstantType("Int", List()), left)
            checkTerm(ConstantType("Int", List()), right)
        case (ConstantType("Bool", List()), BinaryOperator(token, left, right)) if Seq(Tokenizer.AndAnd, Tokenizer.OrOr).contains(token) =>
            checkTerm(ConstantType("Bool", List()), left)
            checkTerm(ConstantType("Bool", List()), right)
        case (ConstantType("Bool", List()), BinaryOperator(token, left, right)) =>
            checkTerm(ConstantType("Int", List()), left)
            checkTerm(ConstantType("Int", List()), right)
        case (_, _) =>
            throw new RuntimeException("Expected type: " + expected + ", but encountered: " + term)
    }

    def checkAssign(statement : AssignStatement) = {
        statement.term match {
            case Variable(name) => variables.get(name) match {
                case None => throw new RuntimeException("Unknown variable: " + name)
                case Some(scheme) =>
                    val expectedType = scheme.generalType // TODO
                    checkTerm(expectedType, statement.value)
            }
            case _ => throw new RuntimeException("Can only assign to a variable, but got: " + statement.term)
        }
    }

    def checkDefinition(statement : VariableStatement) = {
        statement.constructor match {
            case None =>
            case Some(constructorName) => // TODO
        }
        statement.ofType match {
            case None => throw new RuntimeException("Missing type annotation for variable: " + statement.name)
            case Some(t) => checkTerm(t, statement.value)
        }
    }

    def checkSumTypeDefinition(statement : SumTypeStatement) = {
        // TODO: Check that the types used in constructor parameters are defined
        if(sumTypes.get(statement.name).isDefined) throw new RuntimeException("Type already defined: " + statement.name)
        sumTypes.set(statement.name, statement)
    }

    def checkStatements(expectedType : Type, statements : List[Statement]) = {
        for((statement, i) <- statements.zipWithIndex) statement match {
            case sumTypeStatement : SumTypeStatement =>
                checkSumTypeDefinition(sumTypeStatement)
            case definition : VariableStatement =>
                // Prepare environment for mutual recursion
                if(i == 0 || (statements(i - 1) match { case VariableStatement(_, _, _, _ : Lambda) => false; case _ => true })) {
                    val recursive = statements.drop(i).map {
                        case s : VariableStatement => Some(s).filter(_.value.isInstanceOf[Lambda])
                        case _ => None
                    }.takeWhile(_.isDefined).map(_.get)
                    for(VariableStatement(_, recursiveName, recursiveType, _) <- recursive) {
                        recursiveType match {
                            case None => throw new RuntimeException("Missing type annotation for variable: " + recursiveName)
                            case Some(t) => variables.set(recursiveName, Scheme(List(), t))
                        }
                    }
                }
                checkDefinition(definition)
                if(!definition.value.isInstanceOf[Lambda]) {
                    variables.set(definition.name, Scheme(List(), definition.ofType.get))
                }
            case assign : AssignStatement =>
                checkAssign(assign)
            case TermStatement(term) =>
                val expected = if(i + 1 == statements.length) expectedType else RecordType(List())
                checkTerm(expected, term)
        }
        statements.lastOption match {
            case Some(TermStatement(_)) => // OK
            case _ if expectedType == RecordType(List()) => // OK
            case statement => throw new RuntimeException("Expected type: " + expectedType + ", but got: " + statement)
        }
    }

    def checkProgram(program : List[Statement]) = {
        checkStatements(RecordType(List()), program)
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

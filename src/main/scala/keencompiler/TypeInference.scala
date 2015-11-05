package keencompiler

import keencompiler.Parser._
import keencompiler.TypeInference._

import scala.collection.mutable

class TypeInference {

    var typeVariables = new TypeVariables()
    var variables = new Variables()
    var extracts = new Extracts()
    var sumTypes = new SumTypes()

    def checkPattern(pattern : Pattern) : Type = pattern match {
        // TODO: Check exhaustiveness
        case WildcardPattern => NonRigidType(typeVariables.fresh())
        case VariablePattern(name) =>
            val resultType = NonRigidType(typeVariables.fresh())
            variables.set(name, Scheme(List(), resultType))
            resultType
        case ExtractPattern(constructorName, alias) =>
            sumTypes.getByConstructor(constructorName) match {
                case None => throw new RuntimeException("Unknown constructor: " + constructorName)
                case Some(SumTypeStatement(typeName, expectedTypeParameters, constructors)) =>
                    constructors.find(_._1 == constructorName) match {
                        case None => throw new RuntimeException("Unknown constructor: " + constructorName + ", of type: " + typeName)
                        case Some((_, expectedFields)) =>
                            val extractedType = ConstantType(typeName, expectedTypeParameters.map(_ => NonRigidType(typeVariables.fresh())))
                            for(x <- alias) {
                                variables.set(x, Scheme(List(), extractedType))
                                extracts.set(x, constructorName)
                            }
                            extractedType
                    }
            }
        case ConstructorPattern(name, fields) =>
            sumTypes.getByConstructor(name) match {
                case None => throw new RuntimeException("Unknown constructor: " + name)
                case Some(SumTypeStatement(typeName, expectedTypeParameters, constructors)) =>
                    constructors.find(_._1 == name) match {
                        case None => throw new RuntimeException("Unknown constructor: " + name + ", of type: " + typeName)
                        case Some((_, expectedFields)) =>
                            val freshParameters = expectedTypeParameters.map(x => x -> typeVariables.fresh())
                            val constantType = ConstantType(typeName, freshParameters.map(t => NonRigidType(t._2)))
                            for(field <- fields) expectedFields.find(_._1 == field._1) match {
                                case None => throw new RuntimeException("Unknown field: " + field._1 + ", for constructor: " + name)
                                case Some((_, scheme)) =>
                                    val fieldType = instantiate(Scheme(expectedTypeParameters, instantiate(scheme)), Some(freshParameters.toMap))
                                    val resultType = checkPattern(field._2)
                                    unify(fieldType, resultType)
                            }
                            if(expectedFields.length > fields.length) {
                                throw new RuntimeException("Missing fields: " + (expectedFields.map(_._1).toSet -- fields.map(_._1)).mkString(", ") + ", for constructor: " + name)
                            }
                            constantType
                    }
            }
        case RecordPattern(fields) =>
            // TODO: Check duplicate fields in record
            val fieldTypes = for((label, pattern) <- fields) yield label -> checkPattern(pattern)
            RecordType(fieldTypes)
        case ArrayPattern(elements) =>
            val elementType = NonRigidType(typeVariables.fresh())
            for(element <- elements) unify(elementType, checkPattern(element))
            ConstantType("Array", List(elementType))
        case StringPattern(value) => ConstantType("String", List())
        case IntegerPattern(value) => ConstantType("Int", List())
    }

    def checkTerm(term : Term) : Type = term match {
        case Variable(name) => variables.get(name) match {
            case None => throw new RuntimeException("Unknown variable: " + name)
            case Some(scheme) => instantiate(scheme)
        }
        case Lambda(cases) =>
            val skipPatterns = cases.head._1.isEmpty
            val firstPatterns = if(cases.head._1.isEmpty) cases.head._1 else List(RecordPattern(List()))
            val parameterTypes = firstPatterns.map(_ => NonRigidType(typeVariables.fresh()))
            val returnType = NonRigidType(typeVariables.fresh())
            val functionType = FunctionType(parameterTypes, returnType)
            for((patterns, statements) <- cases) {
                val (oldVariables, oldExtracts) = (variables.copy, extracts.copy)
                // TODO: Check that variables do not occur twice in each case
                if(!skipPatterns) {
                    if(firstPatterns.length != patterns.length) throw new RuntimeException("Expected " + firstPatterns.length + " patterns, but got " + patterns.length)
                    for((pattern, expectedType) <- patterns zip parameterTypes) {
                        val patternType = checkPattern(pattern)
                        unify(expectedType, patternType)
                    }
                }
                val resultType = checkStatements(statements)
                unify(returnType, resultType)
                variables = oldVariables
                extracts = oldExtracts
            }
            functionType
        case Call(function, parameters) =>
            val parameterTypes = parameters.map(_ => NonRigidType(typeVariables.fresh()))
            val returnType = NonRigidType(typeVariables.fresh())
            val functionType = FunctionType(parameterTypes, returnType)
            unify(functionType, checkTerm(function))
            for((p, t) <- parameters zip parameterTypes) unify(t, checkTerm(p))
            returnType
        case Constructor(name, fields) =>
            sumTypes.getByConstructor(name) match {
                case None => throw new RuntimeException("Unknown constructor: " + name)
                case Some(SumTypeStatement(typeName, expectedTypeParameters, constructors)) =>
                    constructors.find(_._1 == name) match {
                        case None => throw new RuntimeException("Unknown constructor: " + name + ", of type: " + typeName)
                        case Some((_, expectedFields)) =>
                            val freshParameters = expectedTypeParameters.map(x => x -> typeVariables.fresh())
                            for(field <- fields) expectedFields.find(_._1 == field._1) match {
                                case None => throw new RuntimeException("Unknown field: " + field._1 + ", for constructor: " + name)
                                case Some((_, scheme)) =>
                                    val resultType = checkTerm(field._2)
                                    val oldTypeVariables = typeVariables.copy
                                    unify(instantiate(Scheme(expectedTypeParameters, scheme.generalType), Some(freshParameters.toMap)), resultType)
                                    typeVariables = oldTypeVariables
                                    val fieldType = instantiate(Scheme(expectedTypeParameters, instantiate(scheme)), Some(freshParameters.toMap))
                                    unify(fieldType, resultType)
                            }
                            if(expectedFields.length > fields.length) {
                                throw new RuntimeException("Missing fields: " + (expectedFields.map(_._1).toSet -- fields.map(_._1)).mkString(", ") + ", for constructor: " + name)
                            }
                            ConstantType(typeName, freshParameters.map(t => NonRigidType(t._2)))
                    }
            }
        case Field(record, label) =>
            val recordType = expand(checkTerm(record))
            recordType match {
                case ConstantType(name, parameters) =>
                    sumTypes.get(name) match {
                        case None => throw new RuntimeException("Inferred non-existent type: " + recordType)
                        case Some(statement) =>
                            val extract = record match {
                                case Variable(x) => extracts.get(x) match {
                                    case None => None
                                    case Some(constructorName) => statement.constructors.find(_._1 == constructorName) match {
                                        case None => None
                                        case Some(c) => Some(c)
                                    }
                                }
                                case _ => None
                            }
                            val constructor = extract.getOrElse(statement.constructors match {
                                case List(c) => c
                                case _ => throw new RuntimeException("Can only access field ." + label + " of sum types with a single constructor, but got " + recordType)
                            })
                            constructor._2.find(_._1 == label) match {
                                case None => throw new RuntimeException("No such field: ." + label + ", of " + recordType)
                                case Some((_, scheme)) => instantiate(scheme)
                            }
                    }
                case RecordType(fields) =>
                    fields.find(_._1 == label) match {
                        case None => throw new RuntimeException("No such field: ." + label)
                        case Some((_, t)) => t
                    }
                case NonRigidType(name) => throw new RuntimeException("Type annotation needed for _ in: _." + label)
                case _ => throw new RuntimeException("Not a record type: " + recordType)
            }
        case Record(fields) =>
            // TODO: Check duplicate fields in record
            val fieldTypes = for((label, term) <- fields) yield label -> checkTerm(term)
            RecordType(fieldTypes)
        case ArrayLiteral(elements) =>
            val elementType = NonRigidType(typeVariables.fresh())
            for(term <- elements) unify(elementType, checkTerm(term))
            ConstantType("Array", List(elementType))
        case StringLiteral(value) =>
            ConstantType("String", List())
        case IntegerLiteral(value) =>
            ConstantType("Int", List())
        case UnaryOperator(Tokenizer.Bang, operand) =>
            unify(ConstantType("Bool", List()), checkTerm(operand))
            ConstantType("Bool", List())
        case UnaryOperator(Tokenizer.Minus, operand) =>
            unify(ConstantType("Int", List()), checkTerm(operand))
            ConstantType("Int", List())
        case BinaryOperator(token, left, right) if Seq(Tokenizer.Minus, Tokenizer.Plus, Tokenizer.Star, Tokenizer.Slash).contains(token) =>
            unify(ConstantType("Int", List()), checkTerm(left))
            unify(ConstantType("Int", List()), checkTerm(right))
            ConstantType("Int", List())
        case BinaryOperator(token, left, right) if Seq(Tokenizer.AndAnd, Tokenizer.OrOr).contains(token) =>
            unify(ConstantType("Bool", List()), checkTerm(left))
            unify(ConstantType("Bool", List()), checkTerm(right))
            ConstantType("Bool", List())
        case BinaryOperator(token, left, right) =>
            unify(ConstantType("Int", List()), checkTerm(left))
            unify(ConstantType("Int", List()), checkTerm(right))
            ConstantType("Bool", List())
    }


    def checkAssign(statement : AssignStatement) : Type = {
        statement.term match {
            case Variable(name) => variables.get(name) match {
                case None => throw new RuntimeException("Unknown variable: " + name)
                case Some(scheme) =>
                    if(scheme.parameters.nonEmpty) {
                        throw new RuntimeException("Can't assign to a variable with polymorphic type: " + name)
                    }
                    val expectedType = instantiate(scheme)
                    val resultType = checkTerm(statement.value)
                    unify(expectedType, resultType)
                    RecordType(List())
            }
            case _ => throw new RuntimeException("Can only assign to a variable, but got: " + statement.term)
        }
    }

    def checkSumTypeDefinition(statement : SumTypeStatement) = {
        // TODO: Check that the types used in constructor parameters are defined
        if(sumTypes.get(statement.name).isDefined) throw new RuntimeException("Type already defined: " + statement.name)
        def createFieldSchemes(fields : List[(String, Scheme)]) : List[(String, Scheme)] = {
            for((label, wrongScheme) <- fields) yield {
                val free = freeRigid(wrongScheme.generalType) -- statement.parameters
                label -> wrongScheme.copy(parameters = free.toList)
            }
        }
        sumTypes.set(statement.name, statement.copy(constructors = statement.constructors.map(c => c._1 -> createFieldSchemes(c._2))))
    }

    def checkDefinition(statement : VariableStatement) : Unit = {
        val valueType = checkTerm(statement.value)
        statement.ofType match {
            case Some(t) =>
                val oldTypeVariables = typeVariables.copy
                unify(t, valueType)
                typeVariables = oldTypeVariables
            case None =>
                val scheme = generalize(valueType)
                println("Inferred " + statement.name + " : " + scheme)
                // Overwrites the monomorphic binding used inside the recursion
                if(statement.value.isInstanceOf[Lambda]) {
                    variables.set(statement.name, scheme)
                } else {
                    // Value restriction
                    variables.set(statement.name, Scheme(List(), instantiate(scheme)))
                }

        }
    }

    def checkStatements(statements : List[Statement]) : Type = {
        for((statement, i) <- statements.zipWithIndex) statement match {
            case sumTypeStatement : SumTypeStatement =>
                checkSumTypeDefinition(sumTypeStatement)
                RecordType(List())
            case definition : VariableStatement =>
                // Prepare environment for mutual recursion
                if(i == 0 || (statements(i - 1) match { case VariableStatement(_, _, _ : Lambda) => false; case _ => true })) {
                    val recursive = statements.drop(i).map {
                        case s : VariableStatement => Some(s).filter(_.value.isInstanceOf[Lambda])
                        case _ => None
                    }.takeWhile(_.isDefined).map(_.get)
                    for(VariableStatement(recursiveName, recursiveType, _) <- recursive) {
                        recursiveType match {
                            case None =>
                                variables.set(recursiveName, Scheme(List(), NonRigidType(typeVariables.fresh())))
                            case Some(t) =>
                                variables.set(recursiveName, Scheme(freeRigid(t).toList, t))
                        }
                    }
                }
                checkDefinition(definition)
                if(!definition.value.isInstanceOf[Lambda] && definition.ofType.isDefined) {
                    variables.set(definition.name, Scheme(freeRigid(definition.ofType.get).toList, definition.ofType.get))
                }
            case assign : AssignStatement =>
                checkAssign(assign)
            case TermStatement(term) =>
                val resultType = checkTerm(term)
                if(i + 1 == statements.length) return resultType
        }
        RecordType(List())
    }

    def checkProgram(program : List[Statement]) : Unit = {
        val resultType = checkStatements(program)
        unify(RecordType(List()), resultType)
    }

    def unify(expected : Type, actual : Type) : Unit = (expected, actual) match {
        case (RigidType(name1), RigidType(name2)) =>
            if(name1 != name2) throw new RuntimeException("User-defined type variables mismatch, expected: " + name1 + ", got: " + name2)
        case (NonRigidType(name1), NonRigidType(name2)) if name1 == name2 => // OK
        case (NonRigidType(name1), t2) =>
            typeVariables.get(name1) match {
                case None =>
                    if(freeNonRigid(t2).contains(name1)) {
                        expand(t2) match {
                            case NonRigidType(name2) if name1 == name2 => // OK
                            case _ => throw new RuntimeException("Unification loop: " + name1 + " = " + expand(t2))
                        }
                    }
                    typeVariables.set(name1, t2)
                case Some(t1) =>
                    unify(t1, t2)
            }
        case (t1, NonRigidType(name2)) =>
            typeVariables.get(name2) match {
                case None =>
                    if(freeNonRigid(t1).contains(name2)) {
                        expand(t1) match {
                            case NonRigidType(name1) if name1 == name2 => // OK
                            case _ => throw new RuntimeException("Unification loop: " + name2 + " = " + expand(t1))
                        }
                    }
                    typeVariables.set(name2, t1)
                case Some(t2) =>
                    unify(t1, t2)
            }
        case (FunctionType(parameters1, returns1), FunctionType(parameters2, returns2)) =>
            val ps1 = if(parameters1.isEmpty) List(RecordType(List())) else parameters1
            val ps2 = if(parameters2.isEmpty) List(RecordType(List())) else parameters2
            if(ps1.length != ps2.length) throw new RuntimeException("Unification expected " + ps1.length + " arguments, but got " + ps2.length)
            for((p1, p2) <- ps1 zip ps2) unify(p1, p2)
            unify(returns1, returns2)
        case (ConstantType(name1, parameters1), ConstantType(name2, parameters2)) =>
            if(name1 != name2) throw new RuntimeException("Unification expected " + name1 + ", but got " + name2)
            if(parameters1.length != parameters2.length) throw new RuntimeException("Unification expected " + parameters1.length + " type parameters to " + name1 + ", but got " + parameters2.length)
            for((p1, p2) <- parameters1 zip parameters2) unify(p1, p2)
        case (RecordType(fields1), RecordType(fields2)) =>
            if(fields1.length > fields2.length) throw new RuntimeException("Unification expected fields: " + (fields1.map(_._1).toSet - fields2.map(_._1)).mkString(", "))
            if(fields1.length < fields2.length) throw new RuntimeException("Unification unexpected fields: " + (fields2.map(_._1).toSet - fields1.map(_._1)).mkString(", "))
            val (sorted1, sorted2) = (fields1.sortBy(_._1), fields2.sortBy(_._1))
            for((field1, field2) <- sorted1 zip sorted2) {
                if(field1._1 != field2._1) throw new RuntimeException("Unification expected field: " + field1._1 + ", but got: " + field2._1)
                unify(field1._2, field2._2)
            }
        case _ => throw new RuntimeException("Unification expected " + expand(expected) + ", but got " + expand(actual))
    }

    def environmentFreeNonRigid() : Set[String] = {
        for {
            (variableName, variableScheme) <- variables.all
            // We don't need to instantiate, because we only look at non-rigid type variables
            expanded = expand(variableScheme.generalType)
            s <- freeNonRigid(expanded)
        } yield s
    }.toSet

    def freeNonRigid(inType : Type) : Set[String] = inType match {
        case FunctionType(parameters, returns) => parameters.flatMap(freeNonRigid).toSet ++ freeNonRigid(returns)
        case RigidType(name) => Set()
        case NonRigidType(name) => typeVariables.get(name) match {
            case None => Set(name)
            case Some(t) => freeNonRigid(t)
        }
        case ConstantType(name, parameters) => parameters.flatMap(freeNonRigid).toSet
        case RecordType(fields) => fields.flatMap(f => freeNonRigid(f._2)).toSet
    }

    def freeRigid(inType : Type) : Set[String] = inType match {
        case FunctionType(parameters, returns) => parameters.flatMap(freeRigid).toSet ++ freeRigid(returns)
        case RigidType(name) => Set(name)
        case NonRigidType(name) => typeVariables.get(name) match {
            case None => Set()
            case Some(t) => freeRigid(t)
        }
        case ConstantType(name, parameters) => parameters.flatMap(freeRigid).toSet
        case RecordType(fields) => fields.flatMap(f => freeRigid(f._2)).toSet
    }

    def expand(inType : Type) : Type = inType match {
        case FunctionType(parameters, returns) => FunctionType(parameters.map(expand), expand(returns))
        case RigidType(name) => RigidType(name)
        case NonRigidType(name) => typeVariables.get(name) match {
            case None => NonRigidType(name)
            case Some(t) => expand(t)
        }
        case ConstantType(name, parameters) => ConstantType(name, parameters.map(expand))
        case RecordType(fields) => RecordType(fields.map(field => field._1 -> expand(field._2)))
    }

    def instantiate(scheme : Scheme, fresh : Option[Map[String, String]] = None) : Type = {
        if(scheme.parameters.isEmpty) return scheme.generalType
        val mapping = fresh.getOrElse(scheme.parameters.map(_ -> typeVariables.fresh())).toMap
        def go(t : Type) : Type = t match {
            case FunctionType(parameters, returns) => FunctionType(parameters.map(go), go(returns))
            case RigidType(name) =>
                mapping.get(name) match {
                    case None => t
                    case Some(typeVariableName) => NonRigidType(typeVariableName)
                }
            case ConstantType(name, parameters) => ConstantType(name, parameters.map(go))
            case RecordType(fields) => RecordType(fields.map { case (label, fieldType) => (label, go(fieldType)) })
            case NonRigidType(name) => typeVariables.get(name) match {
                case None => NonRigidType(name)
                case Some(typeLookedUp) => go(typeLookedUp)
            }
        }
        go(scheme.generalType)
    }

    def generalize(inferredType : Type) : Scheme = {
        val typeParameters = (freeNonRigid(inferredType) -- environmentFreeNonRigid()).toList.map(_ -> typeVariables.fresh()).toMap
        def go(t : Type) : Type = t match {
            case FunctionType(parameters, returns) => FunctionType(parameters.map(go), go(returns))
            case RigidType(name) => RigidType(name)
            case NonRigidType(name) => NonRigidType(name)
                typeParameters.get(name) match {
                    case None => NonRigidType(name)
                    case Some(typeVariableName) => RigidType(typeVariableName)
                }
            case ConstantType(name, parameters) => ConstantType(name, parameters.map(go))
            case RecordType(fields) => RecordType(fields.map { case (label, fieldType) => (label, go(fieldType)) })
        }
        val generalType = go(expand(inferredType))
        Scheme(typeParameters.values.toList, generalType)
    }
}

object TypeInference {

    case class Scheme(parameters : List[String], generalType : Type)

    class Variables(map : mutable.HashMap[String, Scheme] = mutable.HashMap()) {
        def get(variable : String) : Option[Scheme] = map.get(variable)
        def set(variable : String, scheme : Scheme) = map.put(variable, scheme)
        def copy = new Variables(mutable.HashMap(map.toSeq : _*))
        def all : List[(String, Scheme)] = map.toList
    }

    class Extracts(map : mutable.HashMap[String, String] = mutable.HashMap()) {
        def get(variable : String) : Option[String] = map.get(variable)
        def set(variable : String, constructor : String) = map.put(variable, constructor)
        def copy = new Extracts(mutable.HashMap(map.toSeq : _*))
    }

    class SumTypes(map : mutable.HashMap[String, SumTypeStatement] = mutable.HashMap()) {
        def get(name : String) : Option[SumTypeStatement] = map.get(name)
        def set(name : String, statement : SumTypeStatement) = map.put(name, statement)
        def copy = new SumTypes(mutable.HashMap(map.toSeq : _*))
        def getByConstructor(name : String) : Option[SumTypeStatement] = map.find(_._2.constructors.exists(_._1 == name)).map(_._2)
    }

    class TypeVariables(map : mutable.HashMap[String, Type] = mutable.HashMap()) {
        def get(name : String) : Option[Type] = map.get(name)
        def set(name : String, statement : Type) = map.put(name, statement)
        def copy = new TypeVariables(mutable.HashMap(map.toSeq : _*))
        def fresh() : String = {
            val name = "_" + nextTypeVariable
            nextTypeVariable += 1
            name
        }
    }

    private var nextTypeVariable = 0

}

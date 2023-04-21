package org.stella.typecheck

import org.syntax.stella.Absyn.*
import org.syntax.stella.PrettyPrinter

class TypeError(message: String) : Exception(message)

var globalContext = mutableMapOf<String, Type>();

object TypeCheck {
    fun typeCheckProgram(program: Program?) {
        when (program) {
            is AProgram ->
                for (decl in program.listdecl_) {
                    when (decl) {
                        is DeclFun -> {
                            typeCheckFunctionDeclaration(decl)
                        }
                    }
                }
        }
    }
}

// Typechecks the contents of a function declaration against it's declared types
// after adding it to the global scope
fun typeCheckFunctionDeclaration(decl: DeclFun) {
    val context = mutableMapOf<String, Type>()

    var returnType = when (decl.returntype_) {
        is SomeReturnType -> {
            decl.returntype_.type_
        }

        else -> throw TypeError("A function declaration must specify its return type.")
    }

    for (paramDecl in decl.listparamdecl_) {
        var params = parseParamDecl(paramDecl)
        context += params

        var paramType: Type? = null
        for (value in params.values)
            paramType = value

        // Add function signature to global context
        var functionType = constructTypeFun(paramType, returnType)
        globalContext[decl.stellaident_] = functionType
    }

    val returnExpr = decl.expr_

    typeCheckExpression(returnExpr, returnType, context)
}

// Writes the given parameter declarations into a map to act as the function's local scope later on
fun parseParamDecl(paramDecl: ParamDecl): Map<String, Type> = when (paramDecl) {
    is AParamDecl -> mapOf(paramDecl.stellaident_ to paramDecl.type_)
    else -> mapOf()
}

// Typechecks a given expression against the provided expectedType using the given local/global scopes
// Fails if the actual type does not match the one given
// When given null as expectedType
// it simply returns the inferred type of the expression (assuming no TypeErrors happen further down the line)
// The same thing goes for all the typeCheck functions
fun typeCheckExpression(expr: Expr, expectedType: Type?, context: MutableMap<String, Type>): Type? = when (expr) {
    is Var -> typeCheckVar(expr, expectedType, context)
    is Tuple -> typeCheckTuple(expr, expectedType, context)
    is DotTuple -> typeCheckDotTuple(expr, expectedType, context)
    is Record -> typeCheckRecord(expr, expectedType, context)
    is DotRecord -> typeCheckDotRecord(expr, expectedType, context)
    is ConstTrue -> typeCheckBool(expectedType)
    is ConstFalse -> typeCheckBool(expectedType)
    is ConstInt -> typeCheckInt(expr, expectedType)
    is ConstUnit -> typeCheckUnit(expectedType)
    is Succ -> typeCheckSucc(expr, expectedType, context)
    is If -> typeCheckIf(expr, expectedType, context)
    is Match -> typeCheckMatch(expr, expectedType, context)
    is Inl -> typeCheckInl(expr, expectedType, context)
    is Inr -> typeCheckInr(expr, expectedType, context)
    is NatRec -> typeCheckNatRec(expr, expectedType, context)
    is IsZero -> typeCheckIsZero(expr, expectedType, context)
    is Abstraction -> typeCheckAbstraction(expr, expectedType, context)
    is Application -> typeCheckApplication(expr, expectedType, context)
    is Sequence -> typeCheckSequence(expr, expectedType, context)
    is Panic -> typeCheckPanic(expr, expectedType, context)
    is Ref -> typeCheckRef(expr, expectedType, context)
    is Deref -> typeCheckDeref(expr, expectedType, context)
    is Assign -> typeCheckAssign(expr, expectedType, context)
    is Let -> typeCheckLetBinding(expr, expectedType, context)
    is TypeCast -> typeCheckTypeCast(expr, expectedType, context)
    else -> null
}

fun compareWithSubtyping(subType: Type?, superType: Type?): Boolean {
    // TODO: implement type casting to use TypeTop
    if (superType is TypeTop)
        return true

    if (subType is TypeBottom)
        return true

    // guaranteed no null types will reach this point, they will be handled prior to being compared
    if (subType!!::class != superType!!::class)
        return false

    // type itself will not be null, but it might be a sum type containing null
    if (compareNullSafe(subType, superType))
        return true

    return when (subType) {
        is TypeFun -> isFunSubtypeOf(subType!!, superType!! as TypeFun)
        is TypeRecord -> isRecordSubtypeOf(subType!!, superType!! as TypeRecord)
        else -> false
    }
}

// Given 2 types, compares them taking into account null values
fun compareNullSafe(type1: Type?, type2: Type?): Boolean {
    if (type1 is TypeSum && type2 is TypeSum) {
        return (compareNullSafe(type1.type_1, type2.type_1) && compareNullSafe(type1.type_2, type2.type_2))
    }

    if (type1 is TypeSum)
        return type2 == null

    if (type2 is TypeSum)
        return type1 == null

    if (type1 == null || type2 == null)
        return true

    return type1 == type2
}

fun isFunSubtypeOf(subType: TypeFun, superType: TypeFun): Boolean {
    return (compareWithSubtyping(subType.type_, superType.type_) && compareWithSubtyping(
        superType.listtype_[0],
        subType.listtype_[0]
    ))
}

fun isRecordSubtypeOf(subType: TypeRecord, superType: TypeRecord): Boolean {
    // TODO: Check if for subtyping records, each field needs to be the exact same as its peer or a subtype of it

    var superRecordFieldTypes: MutableMap<String, Type> = mutableMapOf<String, Type>()

    for (recordFieldType in superType.listrecordfieldtype_)
        when (recordFieldType) {
            is ARecordFieldType ->
                superRecordFieldTypes += mapOf(recordFieldType.stellaident_ to recordFieldType.type_)
        }

    for (recordFieldType in subType.listrecordfieldtype_)
        when (recordFieldType) {
            is ARecordFieldType -> {
                val subFieldKey = recordFieldType.stellaident_
                val subFieldValue = recordFieldType.type_

                if (superRecordFieldTypes.containsKey(subFieldKey)) {
                    if (superRecordFieldTypes[subFieldKey] != subFieldValue)
                        return false

                    superRecordFieldTypes.remove(subFieldKey)
                }
            }
        }

    return superRecordFieldTypes.isEmpty()
}

// Given a list of types, tries to find a most general type such that it is a super type to all
// other elements of the list
// Returns the most general type is successful, otherwise returns null
fun isHomogenousListType(listTypes: MutableList<Type?>): Type? {
    var mostGeneralType = listTypes.elementAt(0)

    for (type in listTypes.filterIndexed { index, _ -> index > 0 })
        if (!compareWithSubtyping(type, mostGeneralType))
            if (compareWithSubtyping(mostGeneralType, type))
                mostGeneralType = type
            else
                return null

    return mostGeneralType
}

fun typeCheckTypeCast(castExpr: TypeCast, expectedType: Type?, context: MutableMap<String, Type>): Type? {
    val exprType = typeCheckExpression(castExpr.expr_, null, context)

    //TODO: Do we allow casting no matter what (no hierarchy)?

    if (expectedType == null)
        return castExpr.type_

    if (!compareWithSubtyping(castExpr.type_, expectedType))
        throw TypeError(
            "Expected type ${PrettyPrinter.print(expectedType)}\n" +
                    "Instead found type ${PrettyPrinter.print(castExpr.type_)}"
        )

    return castExpr.type_

}

fun typeCheckLetBinding(letExpr: Let, expectedType: Type?, outerContext: MutableMap<String, Type>): Type? {
    var innerContext = mutableMapOf<String, Type>()

    // Creating local scope
    innerContext += parseListPatternBinding(letExpr.listpatternbinding_, outerContext)

    // Adding previous scope to new scope
    // Shadowing occurs naturally here as in the old values get overwritten
    innerContext = (outerContext + innerContext) as MutableMap<String, Type>

    val innerExprType = typeCheckExpression(letExpr.expr_, expectedType, innerContext)

    return innerExprType
}

fun typeCheckAssign(expr: Assign, expectedType: Type?, context: MutableMap<String, Type>): Type? {

    val leftExpressionType = typeCheckExpression(expr.expr_1, null, context)
    val rightExpressionType = typeCheckExpression(expr.expr_2, null, context)

    when (leftExpressionType) {
        is TypeRef -> {
            if (!compareWithSubtyping(rightExpressionType, leftExpressionType.type_))
                throw TypeError(
                    "Expected type ${PrettyPrinter.print(leftExpressionType.type_)}\n" +
                            "Instead found ${PrettyPrinter.print(rightExpressionType)}\n" +
                            "In expression ${PrettyPrinter.print(expr)}"
                )

            if (expectedType == null)
                return TypeUnit()

            if (expectedType !is TypeUnit)
                throw TypeError(
                    "Expected type ${PrettyPrinter.print(expectedType)}\n" +
                            "Instead found ${PrettyPrinter.print(TypeUnit())}\n" +
                            "In expression ${PrettyPrinter.print(expr)}"
                )

            return TypeUnit()
        }

        else -> throw TypeError("Cannot assign a value to a non-reference ${PrettyPrinter.print(expr.expr_1)}")
    }
}

fun typeCheckDeref(expr: Deref, expectedType: Type?, context: MutableMap<String, Type>): Type? {
    val innerExprType = typeCheckExpression(expr.expr_, null, context)

    when (innerExprType) {
        is TypeRef -> {
            val dereferencedType = innerExprType.type_

            if (expectedType == null)
                return dereferencedType

            if (!compareWithSubtyping(dereferencedType, expectedType))
                throw TypeError(
                    "Expected type ${PrettyPrinter.print(expectedType)}\n" +
                            "Instead found type ${PrettyPrinter.print(innerExprType)}\n" +
                            "In expression ${PrettyPrinter.print(expr)}"
                )

            return dereferencedType
        }

        else -> throw TypeError(
            "Cannot dereference an expression ${PrettyPrinter.print(expr.expr_)}\n" +
                    "of a non-reference type ${PrettyPrinter.print(innerExprType)}"
        )
    }
}

fun typeCheckRef(expr: Ref, expectedType: Type?, context: MutableMap<String, Type>): Type? {
    val innerExprType = typeCheckExpression(expr.expr_, null, context)
    val refType = TypeRef(innerExprType)

    if (expectedType == null)
        return refType

    if (!compareWithSubtyping(refType, expectedType))
        throw TypeError(
            "Expected type ${PrettyPrinter.print(expectedType)}\n" +
                    "Instead found type ${PrettyPrinter.print(refType)}\n" +
                    "In expression ${PrettyPrinter.print(expr)}"
        )

    return refType
}

fun typeCheckPanic(expr: Panic, expectedType: Type?, context: MutableMap<String, Type>): Type? {
    if (expectedType == null)
        throw TypeError("Illegal expression ${PrettyPrinter.print(expr)}")

    return expectedType
}

fun typeCheckSequence(expr: Sequence, expectedType: Type?, context: MutableMap<String, Type>): Type? {
    // Throw error if first branch is not TypeUnit
    typeCheckExpression(expr.expr_1, TypeUnit(), context)

    // Check second branch type against expectedType or return it if expectedType is null
    val secondBranchReturnType = typeCheckExpression(expr.expr_2, null, context)

    if (expectedType == null)
        return secondBranchReturnType

    if (!compareWithSubtyping(secondBranchReturnType, expectedType))
        throw TypeError(
            "Expected type ${PrettyPrinter.print(expectedType)}\n" +
                    "Instead found type ${PrettyPrinter.print(secondBranchReturnType)}\n" +
                    "In expression ${PrettyPrinter.print(expr.expr_2)}"
        )

    return secondBranchReturnType
}

fun typeCheckApplication(expr: Application, expectedType: Type?, context: MutableMap<String, Type>): Type? {
    when (val functionType = typeCheckExpression(expr.expr_, null, context)) {
        is TypeFun -> {
            val firstArgExpectedType = functionType.listtype_[0]
            val applicationReturnType = functionType.type_

            // typecheck first arg actual and expected types
            typeCheckExpression(expr.listexpr_[0], firstArgExpectedType, context)

            if (expectedType == null)
                return applicationReturnType

            if (!compareWithSubtyping(applicationReturnType, expectedType))
                throw TypeError(
                    "Expected type ${PrettyPrinter.print(expectedType)}\n" +
                            "Instead found ${PrettyPrinter.print(applicationReturnType)}\n" +
                            "in expression ${PrettyPrinter.print(expr)}"
                )

            return applicationReturnType
        }

        else -> {
            throw TypeError(
                "${PrettyPrinter.print(expr.expr_)} cannot " +
                        "be applied to ${PrettyPrinter.print(expr.listexpr_[0])}\n" +
                        "${PrettyPrinter.print(expr.expr_)} is not a function."
            )
        }
    }
}

fun typeCheckNatRec(natRec: NatRec, expectedType: Type?, context: MutableMap<String, Type>): Type? {
    typeCheckExpression(natRec.expr_1, TypeNat(), context)
    val secondExprType = typeCheckExpression(natRec.expr_2, null, context)
    val thirdExprType = typeCheckExpression(natRec.expr_3, null, context)

    // Constructing the expected type of NatRec given its arguments
    val innerReturnType = constructTypeFun(secondExprType, secondExprType)
    val thirdExprExpectedType = constructTypeFun(TypeNat(), innerReturnType)

    if (!compareWithSubtyping(thirdExprType, thirdExprExpectedType)) {
        throw TypeError(
            "Expected Third argument of Nat::rec to be of type" +
                    "fn(Nat) -> (fn(${PrettyPrinter.print(secondExprType)}) -> ${PrettyPrinter.print(secondExprType)})\n" +
                    "Found argument of type ${PrettyPrinter.print(thirdExprType)}"
        )
    }

    return secondExprType
}

fun typeCheckVar(variable: Var, expectedType: Type?, context: MutableMap<String, Type>): Type? {
    val variableName = variable.stellaident_

    // Try to find the variable in local scope
    // otherwise it's a function declaration
    val variableType: Type? = if (variableName in context.keys) {
        context[variableName]
    }
    // get it from global scope
    else {
        globalContext[variableName]
    }

    if (expectedType == null) {
        return variableType
    }

    // Throw error if variable type in context does not match return type
    if (!compareWithSubtyping(variableType, expectedType))
        throw TypeError(
            "Expected ${PrettyPrinter.print(variable)} " +
                    "to be of type ${PrettyPrinter.print(expectedType)}\n" +
                    "Instead assigned value of type ${PrettyPrinter.print(variableType)}\n"
        )

    return variableType
}

fun typeCheckRecord(record: Record, expectedType: Type?, context: MutableMap<String, Type>): Type? {
    val typeOfRecord = constructTypeRecord(record.listbinding_, context)

    if (expectedType == null)
        return typeOfRecord

    when (expectedType) {
        is TypeRecord -> {

            if (!compareWithSubtyping(typeOfRecord, expectedType)) {
                throw TypeError(
                    "Expected type ${PrettyPrinter.print(expectedType)}" +
                            "Instead found type ${PrettyPrinter.print(typeOfRecord)}" +
                            "In Expression ${PrettyPrinter.print(record)}"
                )
            } else
                return typeOfRecord
        }

        else -> throw TypeError(
            "Expected type ${PrettyPrinter.print(expectedType)}" +
                    "Instead found type Record"
        )
    }
}

fun typeCheckTuple(tuple: Tuple, expectedType: Type?, context: MutableMap<String, Type>): Type? {
    val typeOfTuple = constructTypeTuple(tuple.listexpr_, context)

    if (expectedType == null)
        return typeOfTuple

    when (expectedType) {
        is TypeTuple -> {
            if (!compareWithSubtyping(typeOfTuple, expectedType)) {
                throw TypeError(
                    "Expected type ${PrettyPrinter.print(expectedType)}" +
                            "Instead found type ${PrettyPrinter.print(typeOfTuple)}" +
                            "In Expression ${PrettyPrinter.print(tuple)}"
                )
            } else
                return typeOfTuple
        }

        else -> throw TypeError(
            "Expected type ${PrettyPrinter.print(expectedType)}" +
                    "Instead found type Tuple"
        )
    }

}

fun typeCheckDotRecord(dotRecord: DotRecord, expectedType: Type?, context: MutableMap<String, Type>): Type? {
    val exprType = typeCheckExpression(dotRecord.expr_, null, context)

    when (exprType) {
        is TypeRecord -> {

            val dotRecordFieldAccessed = dotRecord.stellaident_

            // Check that expectedType is the same type as the one accessed in the record
            val typeAccessed = accessRecord(dotRecord, dotRecordFieldAccessed, exprType)

            if (expectedType == null)
                return typeAccessed

            if (!compareWithSubtyping(typeAccessed, expectedType)) {
                throw TypeError(
                    "Expected expression of type ${PrettyPrinter.print(expectedType)}\n" +
                            "Instead found expression of type ${PrettyPrinter.print(typeAccessed)}\n" +
                            "In ${PrettyPrinter.print(dotRecord)}"
                )
            }

            return typeAccessed
        }
        // Throw error if trying to access non-record expression
        else -> throw TypeError(
            "Expected an expression of type Record\n" +
                    "Instead found and expression of type ${PrettyPrinter.print(exprType)}"
        )
    }
}

fun typeCheckDotTuple(dotTuple: DotTuple, expectedType: Type?, context: MutableMap<String, Type>): Type? {
    val exprType = typeCheckExpression(dotTuple.expr_, null, context)

    when (exprType) {
        is TypeTuple -> {

            // Throw error if index is 0 or out of range
            // Cast here because type has already been checked
            val dotTupleIndex = dotTuple.integer_

            if (dotTupleIndex == 0)
                throw TypeError("Illegal access to index 0 in tuple ${PrettyPrinter.print(dotTuple.expr_)}")

            val tupleSize = exprType.listtype_.size

            if (dotTupleIndex > tupleSize) {
                throw TypeError(
                    "Unexpected access to index $dotTupleIndex in a tuple ${PrettyPrinter.print(dotTuple.expr_)}\n" +
                            "of size $tupleSize"
                )
            }

            // Check that expectedType is the same type as the one accessed in the tuple
            val typeAccessed = exprType.listtype_[dotTupleIndex - 1]

            if (expectedType == null)
                return typeAccessed

            if (!compareWithSubtyping(typeAccessed, expectedType)) {
                throw TypeError(
                    "Expected expression of type ${PrettyPrinter.print(expectedType)}\n" +
                            "Instead found expression of type ${PrettyPrinter.print(typeAccessed)}\n" +
                            "In ${PrettyPrinter.print(dotTuple)}"
                )
            }

            return typeAccessed
        }
        // Throw error if trying to access non-tuple expression
        else -> throw TypeError(
            "Expected an expression of type Tuple\n" +
                    "Instead found and expression of type ${PrettyPrinter.print(exprType)}"
        )
    }

}

fun typeCheckMatch(match: Match, expectedType: Type?, context: MutableMap<String, Type>): Type? {
    val exprType = typeCheckExpression(match.expr_, null, context)

    return when (exprType) {
        is TypeSum -> {
            val numExpr = match.listmatchcase_.size

            // Throw error if 0 branches
            if (numExpr == 0)
                throw TypeError("Illegal empty matching in expression ${PrettyPrinter.print(match)}")

            // Throw error if inl or inr are missing
            if (!checkInrInl(match.listmatchcase_))
                throw TypeError("Non-exhaustive pattern matches in expression ${PrettyPrinter.print(match)}")

            // Typecheck branches
            var branchTypes = mutableListOf<Type?>()
            for (case in match.listmatchcase_) {
                when (case) {
                    is AMatchCase -> {

                        val varTypeTuple = extractPatternVar(case.pattern_, exprType)
                        val caseContext = mapOf(varTypeTuple.first to varTypeTuple.second)
                        var innerContext = (context + caseContext) as MutableMap<String, Type>

                        val branchType = typeCheckExpression(case.expr_, expectedType, innerContext)

                        branchTypes.add(branchType)
                    }
                }
            }

            val mostGeneralType = isHomogenousListType(branchTypes)

            if (mostGeneralType == null) {
                throw TypeError(
                    "Type ${PrettyPrinter.print(branchTypes.elementAt(1))} does not match" +
                            "Type ${PrettyPrinter.print(branchTypes.elementAt(0))}"
                )
            } else
                mostGeneralType
        }

        else -> null
    }
}

fun extractPatternVar(pattern: Pattern, curType: Type?): Pair<String, Type?> = when (curType) {
    is TypeSum -> when (pattern) {
        is PatternInl -> extractPatternVar(pattern.pattern_, curType.type_1)
        is PatternInr -> extractPatternVar(pattern.pattern_, curType.type_2)
        is PatternVar -> Pair(pattern.stellaident_, curType)
        // TODO: Add other matchable types
        else -> Pair("", null)
    }

    else -> {
        when (pattern) {
            is PatternVar -> Pair(pattern.stellaident_, curType)

            else ->
                throw TypeError(
                    "Attempt to pattern match on non-viable type ${PrettyPrinter.print(curType)}\n" +
                            "In pattern ${PrettyPrinter.print(pattern)}"
                )
        }
    }
}


fun typeCheckInl(expr: Inl, expectedType: Type?, context: MutableMap<String, Type>): Type? {
    if (expectedType == null) {
        return TypeSum(typeCheckExpression(expr.expr_, null, context), null)
    }

    var innerExprType = typeCheckExpression(expr.expr_, null, context)

    when (expectedType) {
        is TypeSum -> {
            if (expectedType.type_1 == null) {
                return TypeSum(innerExprType, expectedType.type_2)
            }

            if (!compareWithSubtyping(innerExprType, expectedType.type_1))
                throw TypeError(
                    "Expected type ${PrettyPrinter.print(expectedType.type_1)}\n" +
                            "in sum type ${PrettyPrinter.print(expectedType)}\n" +
                            "Instead found type ${PrettyPrinter.print(innerExprType)}"
                )

            return innerExprType
        }

        else -> throw TypeError(
            "Expected sum type\n" +
                    "Instead found type ${PrettyPrinter.print(innerExprType)}"
        )
    }
}

fun typeCheckInr(expr: Inr, expectedType: Type?, context: MutableMap<String, Type>): Type? {
    if (expectedType == null) {
        return TypeSum(null, typeCheckExpression(expr.expr_, null, context))
    }

    var innerExprType = typeCheckExpression(expr.expr_, null, context)

    when (expectedType) {
        is TypeSum -> {
            if (expectedType.type_2 == null) {
                return TypeSum(expectedType.type_1, innerExprType)
            }

            if (!compareWithSubtyping(innerExprType, expectedType.type_2))
                throw TypeError(
                    "Expected type ${PrettyPrinter.print(expectedType.type_2)}\n" +
                            "in sum type ${PrettyPrinter.print(expectedType)}\n" +
                            "Instead found type ${PrettyPrinter.print(innerExprType)}"
                )

            return innerExprType
        }

        else -> throw TypeError(
            "Expected sum type\n" +
                    "Instead found type ${PrettyPrinter.print(innerExprType)}"
        )
    }
}

fun typeCheckBool(expectedType: Type?): Type? {

    if (expectedType == null)
        return TypeBool()

    when (expectedType) {
        // Throw error is return type is not Bool
        is TypeBool -> return TypeBool()
        else -> throw TypeError(
            "Expected type ${PrettyPrinter.print(expectedType)}\n" +
                    "Instead found type ${PrettyPrinter.print(TypeBool())}"
        )
    }
}

fun typeCheckInt(intVal: ConstInt, expectedType: Type?): Type? {
    if (expectedType == null)
        return TypeNat()

    val int = intVal.integer_

    // Throw error if number is not 0 or return type is not Nat
    if (int != 0 || expectedType !is TypeNat)
        throw TypeError(
            "Expected type ${PrettyPrinter.print(expectedType)}\n" +
                    "Instead found type ${PrettyPrinter.print(TypeNat())}"
        )

    return TypeNat()
}

fun typeCheckUnit(expectedType: Type?): Type? {
    if (expectedType == null)
        return TypeUnit()

    if (expectedType !is TypeUnit)
        throw TypeError("Expected type ${PrettyPrinter.print(expectedType)}\n")

    return TypeUnit()
}

fun typeCheckSucc(succExpr: Succ, expectedType: Type?, context: MutableMap<String, Type>): Type? {

    if (expectedType == null)
        return typeCheckExpression(succExpr.expr_, TypeNat(), context)

    // Throw error if return type is not Nat
    when (expectedType) {
        !is TypeNat -> throw TypeError(
            "Expected type ${PrettyPrinter.print(expectedType)}\n" +
                    "Instead found argument of type Nat"
        )

    }

    val succContent = succExpr.expr_

    val succContentType = typeCheckExpression(succContent, TypeNat(), context)

    return succContentType
}

fun typeCheckIsZero(isZeroExpr: IsZero, expectedType: Type?, context: MutableMap<String, Type>): Type? {

    if (expectedType == null)
        return typeCheckExpression(isZeroExpr.expr_, TypeBool(), context)

    // Throw error if return type is not Bool
    when (expectedType) {
        !is TypeBool -> throw TypeError(
            "Declared return type ${PrettyPrinter.print(expectedType)}\n" +
                    "does not match actual type Bool."
        )
    }

    val isZeroContent = isZeroExpr.expr_

    val isZeroContentType = typeCheckExpression(isZeroContent, TypeNat(), context)

    return isZeroContentType
}

fun typeCheckIf(ifExpr: If, expectedType: Type?, context: MutableMap<String, Type>): Type? {
    val condition = ifExpr.expr_1
    val firstBranch = ifExpr.expr_2
    val secondBranch = ifExpr.expr_3

    // Throw error if condition is not Bool
    typeCheckExpression(condition, TypeBool(), context)

    // Throw error if any of the 2 branches do not match the return type of the entire construct
    val firstBranchType = typeCheckExpression(firstBranch, expectedType, context)
    val secondBranchType = typeCheckExpression(secondBranch, expectedType, context)

    val mostGeneralType = isHomogenousListType(mutableListOf(firstBranchType, secondBranchType))
        ?: throw TypeError(
            "Branches of If statement must be of the same type.\n" +
                    "Found ${PrettyPrinter.print(firstBranchType)} and ${PrettyPrinter.print(secondBranchType)}"
        )

    // Throw error if inferred types of the 2 branches do not match

    return mostGeneralType
}

fun typeCheckAbstraction(abstraction: Abstraction, expectedType: Type?, outerContext: MutableMap<String, Type>): Type? {
    var innerContext = mutableMapOf<String, Type>()

    // Creating local scope
    for (paramDecl in abstraction.listparamdecl_) {
        innerContext += parseParamDecl(paramDecl)
    }

    // Adding previous scope to new scope
    // Shadowing occurs naturally here as in the old values get overwritten
    innerContext = (outerContext + innerContext) as MutableMap<String, Type>

    val innerExpr = abstraction.expr_
    val firstParam = abstraction.listparamdecl_[0] as AParamDecl

    // Returning inferred type of the Abstraction in case expectedType is null
    if (expectedType == null) {
        val returnType = typeCheckExpression(innerExpr, null, innerContext)
        return constructTypeFun(firstParam.type_, returnType)
    }

    var actualReturnType: Type?

    when (expectedType) {
        is TypeFun -> {
            typeCheckFirstParam(firstParam.type_, expectedType.listtype_[0])
            actualReturnType = typeCheckExpression(innerExpr, expectedType.type_, innerContext)

            if (!compareWithSubtyping(actualReturnType, expectedType.type_))
                throw TypeError(
                    "Type ${PrettyPrinter.print(expectedType)}\n" +
                            "does not match type of given abstraction ${PrettyPrinter.print(abstraction)}\n"
                )
        }

        else -> throw TypeError(
            "Type ${PrettyPrinter.print(expectedType)}\n" +
                    "does not match type of given abstraction ${PrettyPrinter.print(abstraction)}\n"
        )
    }

    return constructTypeFun(firstParam.type_, actualReturnType)
}

// Typechecking the first parameter of an application given it's expected and actual types
fun typeCheckFirstParam(firstParamType: Type?, expectedType: Type?) {
    if (!compareWithSubtyping(firstParamType, expectedType)) {
        throw TypeError(
            "Type ${PrettyPrinter.print(firstParamType)}\n" +
                    "does not match declared type ${PrettyPrinter.print(expectedType)}"
        )
    }
}

// Given ListMatchCase of a match expression verifies that the list contains
// at least one Inr and at least one Inl cases
fun checkInrInl(cases: ListMatchCase): Boolean {
    var inl = false
    var inr = false
    for (expr in cases) {
        when (expr) {
            is AMatchCase ->
                when (expr.pattern_) {
                    is PatternInl -> inl = true
                    is PatternInr -> inr = true
                }
        }
    }

    return inl && inr
}

// Given a DotRecord, the field accessed and its ListRecordFieldType
// Determines whether the access is legal, and returns the type of the accessed field
fun accessRecord(dotRecord: DotRecord, fieldAccessed: String, recordType: TypeRecord): Type? {

    val recordListRecordFieldType = recordType.listrecordfieldtype_

    for (recordFieldType in recordListRecordFieldType)
        when (recordFieldType) {
            is ARecordFieldType ->
                if (recordFieldType.stellaident_ == fieldAccessed)
                    return recordFieldType.type_
        }

    throw TypeError(
        "Unexpected access to field $fieldAccessed\n" +
                "In a record of type ${PrettyPrinter.print(recordType)}\n" +
                "In the expression ${PrettyPrinter.print(dotRecord)}"
    )
}

// Given a
fun parseListPatternBinding(
    listPatternBinding: ListPatternBinding,
    context: MutableMap<String, Type>
): MutableMap<String, Type> {
    var mapPatternBinding = mutableMapOf<String, Type>()

    for (patternBinding in listPatternBinding)
        when (patternBinding) {
            is APatternBinding -> {
                var pattern = patternBinding.pattern_
                when (pattern) {
                    is PatternVar -> mapPatternBinding[pattern.stellaident_] =
                        typeCheckExpression(patternBinding.expr_, null, context)!!
                }
            }
        }

    return mapPatternBinding
}

// Constructs a TypeFun given the type of its argument and its return type
fun constructTypeFun(argType: Type?, returnType: Type?): TypeFun {
    val argListType = ListType()
    argListType.add(argType)

    return TypeFun(argListType, returnType)
}

// Constructs a TypeTuple given its list of expressions and the current context
fun constructTypeTuple(tupleExpressions: ListExpr, context: MutableMap<String, Type>): TypeTuple {
    val exprListType = ListType()

    for (expr in tupleExpressions) {
        exprListType.add(typeCheckExpression(expr, null, context))
    }

    return TypeTuple(exprListType)
}

// Constructs a TypeRecord given its list of bindings and the current context
fun constructTypeRecord(recordListBinding: ListBinding, context: MutableMap<String, Type>): TypeRecord {
    val recordListRecordFieldType = ListRecordFieldType()

    for (binding in recordListBinding) {
        when (binding) {
            is ABinding -> {
                // Add name of the field and its type to the list of record field types
                recordListRecordFieldType.add(
                    ARecordFieldType(
                        binding.stellaident_,
                        typeCheckExpression(binding.expr_, null, context)
                    )
                )
            }
        }
    }

    return TypeRecord(recordListRecordFieldType)
}

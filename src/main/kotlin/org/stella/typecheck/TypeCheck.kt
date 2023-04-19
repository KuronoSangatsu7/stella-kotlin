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

// Typechecks a given expression against the provided typeToMatch using the given local/global scopes
// Fails if the actual type does not match the one given
// When given null as typeToMatch
// it simply returns the inferred type of the expression (assuming no TypeErrors happen further down the line)
// The same thing goes for all the typeCheck functions
fun typeCheckExpression(expr: Expr, typeToMatch: Type?, context: MutableMap<String, Type>): Type? = when (expr) {
    is Var -> typeCheckVar(expr, typeToMatch, context)
    is Tuple -> typeCheckTuple(expr, typeToMatch, context)
    is DotTuple -> typeCheckDotTuple(expr, typeToMatch, context)
    is ConstTrue -> typeCheckBool(typeToMatch)
    is ConstFalse -> typeCheckBool(typeToMatch)
    is ConstInt -> typeCheckInt(expr, typeToMatch)
    is ConstUnit -> typeCheckUnit(typeToMatch)
    is Succ -> typeCheckSucc(expr, typeToMatch, context)
    is If -> typeCheckIf(expr, typeToMatch, context)
    is Match -> typeCheckMatch(expr, typeToMatch, context)
    is Inl -> typeCheckInl(expr, typeToMatch, context)
    is Inr -> typeCheckInr(expr, typeToMatch, context)
    is NatRec -> typeCheckNatRec(expr, typeToMatch, context)
    is IsZero -> typeCheckIsZero(expr, typeToMatch, context)
    is Abstraction -> typeCheckAbstraction(expr, typeToMatch, context)
    is Application -> typeCheckApplication(expr, typeToMatch, context)
    is Sequence -> typeCheckSequence(expr, typeToMatch, context)
    else -> null
}

fun typeCheckSequence(expr: Sequence, typeToMatch: Type?, context: MutableMap<String, Type>): Type? {
    //TODO: make sure you dont need to check the one-branch case, most likely not

    // Throw error if first branch is not TypeUnit
    typeCheckExpression(expr.expr_1, TypeUnit(), context)

    // Check second branch type against typeToMatch or return it if typeToMatch is null
    val secondBranchReturnType = typeCheckExpression(expr.expr_2, typeToMatch, context)

    if (typeToMatch == null)
        return secondBranchReturnType

    if (typeToMatch != secondBranchReturnType)
        throw TypeError("Expected type ${PrettyPrinter.print(typeToMatch)}\n" +
                "Instead found type ${PrettyPrinter.print(secondBranchReturnType)}\n" +
                "In expression ${PrettyPrinter.print(expr.expr_2)}")

    return secondBranchReturnType
}

fun typeCheckApplication(expr: Application, typeToMatch: Type?, context: MutableMap<String, Type>): Type? {
    when (val functionType = typeCheckExpression(expr.expr_, null, context)) {
        is TypeFun -> {
            val firstArgExpectedType = functionType.listtype_[0]
            val applicationReturnType = functionType.type_
            typeCheckExpression(expr.listexpr_[0], firstArgExpectedType, context)

            if (typeToMatch == null)
                return applicationReturnType

            if (applicationReturnType != typeToMatch)
                throw TypeError("Expected type ${PrettyPrinter.print(typeToMatch)}\n" +
                        "Instead found ${PrettyPrinter.print(applicationReturnType)}\n" +
                        "in expression ${PrettyPrinter.print(expr)}")

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

fun typeCheckNatRec(natRec: NatRec, typeToMatch: Type?, context: MutableMap<String, Type>): Type? {
    typeCheckExpression(natRec.expr_1, TypeNat(), context)
    val secondExprType = typeCheckExpression(natRec.expr_2, null, context)
    val thirdExprType = typeCheckExpression(natRec.expr_3, null, context)

    // Constructing the expected type of NatRec given its arguments
    val innerReturnType = constructTypeFun(secondExprType, secondExprType)
    val thirdExprExpectedType = constructTypeFun(TypeNat(), innerReturnType)

    if (thirdExprType != thirdExprExpectedType) {
        throw TypeError(
            "Expected Third argument of Nat::rec to be of type" +
                    "fn(Nat) -> (fn(${PrettyPrinter.print(secondExprType)}) -> ${PrettyPrinter.print(secondExprType)})\n" +
                    "Found argument of type ${PrettyPrinter.print(thirdExprType)}"
        )
    }

    return secondExprType
}

fun typeCheckVar(variable: Var, typeToMatch: Type?, context: MutableMap<String, Type>): Type? {
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

    if (typeToMatch == null) {
        return variableType
    }

    // Throw error if variable type in context does not match return type
    if (variableType != typeToMatch)
        throw TypeError(
            "Expected ${PrettyPrinter.print(variable)} " +
                    "to be of type ${PrettyPrinter.print(typeToMatch)}\n" +
                    "Instead assigned value of type ${PrettyPrinter.print(variableType)}\n"
        )

    return variableType
}

fun typeCheckTuple(tuple: Tuple, typeToMatch: Type?, context: MutableMap<String, Type>): Type? {
    val typeOfTuple = constructTypeTuple(tuple.listexpr_, context)

    if (typeToMatch == null) {
        return typeOfTuple
    }

    when (typeToMatch) {
        is TypeTuple -> {
            if (typeOfTuple != typeToMatch) {
                throw TypeError(
                    "Expected type ${PrettyPrinter.print(typeToMatch)}" +
                            "Instead found type ${PrettyPrinter.print(typeOfTuple)}" +
                            "In Expression ${PrettyPrinter.print(tuple)}"
                )
            } else
                return typeOfTuple
        }

        else -> throw TypeError(
            "Expected type ${PrettyPrinter.print(typeToMatch)}" +
                    "Instead found type Tuple"
        )
    }

}

fun typeCheckDotTuple(dotTuple: DotTuple, typeToMatch: Type?, context: MutableMap<String, Type>): Type? {
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

            // Check that typeToMatch is the same type as the one accessed in the tuple
            val typeAccessed = exprType.listtype_[dotTupleIndex - 1]

            if (typeToMatch == null)
                return typeAccessed

            if (typeToMatch != typeAccessed) {
                throw TypeError(
                    "Expected expression of type ${PrettyPrinter.print(typeToMatch)}\n" +
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

fun typeCheckMatch(match: Match, typeToMatch: Type?, context: MutableMap<String, Type>): Type? {
    val exprType = typeCheckExpression(match.expr_, null, context)
    // TODO: Handle null
    when (exprType) {
        is TypeSum -> {
            val numExpr = match.listmatchcase_.size

            // Throw error if 0 branches
            if (numExpr == 0)
                throw TypeError("Illegal empty matching in expression ${PrettyPrinter.print(match)}")

            // Throw error if inl or inr are missing
            if (!checkInrInl(match.listmatchcase_))
                throw TypeError("Non-exhaustive pattern matches in expression ${PrettyPrinter.print(match)}")

            // Typecheck branches
            var branchTypes = mutableSetOf<Type?>()
            for (case in match.listmatchcase_) {
                when (case) {
                    is AMatchCase -> {

                        val varTypeTuple = extractPatternVar(case.pattern_, exprType)
                        val caseContext = mapOf(varTypeTuple.first to varTypeTuple.second)
                        var innerContext = (context + caseContext) as MutableMap<String, Type>

                        val branchType = typeCheckExpression(case.expr_, typeToMatch, innerContext)

                        branchTypes.add(branchType)
                    }
                }
            }

            if(branchTypes.size > 1) {
                   throw TypeError("Type ${PrettyPrinter.print(branchTypes.elementAt(1))} does not match" +
                           "Type ${PrettyPrinter.print(branchTypes.elementAt(0))}")
            }

            else
                return branchTypes.elementAt(0)
        }

    }

    return TypeBool()
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


fun typeCheckInl(expr: Inl, typeToMatch: Type?, context: MutableMap<String, Type>): Type? {
    if (typeToMatch == null) {
        return TypeSum(typeCheckExpression(expr.expr_, null, context), null)
    }

    var innerExprType = typeCheckExpression(expr.expr_, null, context)

    when (typeToMatch) {
        is TypeSum -> {
            if (typeToMatch.type_1 == null) {
                return TypeSum(innerExprType, typeToMatch.type_2)
            }

            if (!compareNullSafe(innerExprType, typeToMatch.type_1))
                throw TypeError(
                    "Expected type ${PrettyPrinter.print(typeToMatch.type_1)}\n" +
                            "in sum type ${PrettyPrinter.print(typeToMatch)}\n" +
                            "Instead found type ${PrettyPrinter.print(innerExprType)}"
                )

            return typeToMatch
        }

        else -> throw TypeError(
            "Expected sum type\n" +
                    "Instead found type ${PrettyPrinter.print(innerExprType)}"
        )
    }
}

fun typeCheckInr(expr: Inr, typeToMatch: Type?, context: MutableMap<String, Type>): Type? {
    if (typeToMatch == null) {
        return TypeSum(null, typeCheckExpression(expr.expr_, null, context))
    }

    var innerExprType = typeCheckExpression(expr.expr_, null, context)

    when (typeToMatch) {
        is TypeSum -> {
            if (typeToMatch.type_2 == null) {
                return TypeSum(typeToMatch.type_1, innerExprType)
            }

            if (!compareNullSafe(innerExprType, typeToMatch.type_2))
                throw TypeError(
                    "Expected type ${PrettyPrinter.print(typeToMatch.type_2)}\n" +
                            "in sum type ${PrettyPrinter.print(typeToMatch)}\n" +
                            "Instead found type ${PrettyPrinter.print(innerExprType)}"
                )

            return typeToMatch
        }

        else -> throw TypeError(
            "Expected sum type\n" +
                    "Instead found type ${PrettyPrinter.print(innerExprType)}"
        )
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

fun typeCheckBool(typeToMatch: Type?): Type? {

    if (typeToMatch == null)
        return TypeBool()

    when (typeToMatch) {
        // Throw error is return type is not Bool
        is TypeBool -> return TypeBool()
        else -> throw TypeError(
            "Expected type ${PrettyPrinter.print(typeToMatch)}\n" +
                    "Instead found argument of type Bool"
        )
    }
}

fun typeCheckInt(intVal: ConstInt, typeToMatch: Type?): Type? {
    if (typeToMatch == null)
        return TypeNat()

    val int = intVal.integer_

    // Throw error if number is not 0 or return type is not Nat
    if (int != 0 || typeToMatch !is TypeNat)
        throw TypeError("Expected type ${PrettyPrinter.print(typeToMatch)}\n")

    return TypeNat()
}

fun typeCheckUnit(typeToMatch: Type?): Type? {
    if (typeToMatch == null)
        return TypeUnit()

    if (typeToMatch !is TypeUnit)
        throw TypeError("Expected type ${PrettyPrinter.print(typeToMatch)}\n")

    return TypeUnit()
}

fun typeCheckSucc(succExpr: Succ, typeToMatch: Type?, context: MutableMap<String, Type>): Type? {

    if (typeToMatch == null)
        return typeCheckExpression(succExpr.expr_, TypeNat(), context)

    // Throw error if return type is not Nat
    when (typeToMatch) {
        !is TypeNat -> throw TypeError(
            "Expected type ${PrettyPrinter.print(typeToMatch)}\n" +
                    "Instead found argument of type Nat"
        )

    }

    val succContent = succExpr.expr_

    val succContentType = typeCheckExpression(succContent, TypeNat(), context)

    return succContentType
}

fun typeCheckIsZero(isZeroExpr: IsZero, typeToMatch: Type?, context: MutableMap<String, Type>): Type? {

    if (typeToMatch == null)
        return typeCheckExpression(isZeroExpr.expr_, TypeBool(), context)

    // Throw error if return type is not Bool
    when (typeToMatch) {
        !is TypeBool -> throw TypeError(
            "Declared return type ${PrettyPrinter.print(typeToMatch)}\n" +
                    "does not match actual type Bool."
        )
    }

    val isZeroContent = isZeroExpr.expr_

    val isZeroContentType = typeCheckExpression(isZeroContent, TypeNat(), context)

    return isZeroContentType
}

fun typeCheckIf(ifExpr: If, typeToMatch: Type?, context: MutableMap<String, Type>): Type? {
    val condition = ifExpr.expr_1
    val firstBranch = ifExpr.expr_2
    val secondBranch = ifExpr.expr_3

    // Throw error if condition is not Bool
    typeCheckExpression(condition, TypeBool(), context)

    // Throw error if any of the 2 branches do not match the return type of the entire construct
    val firstBranchType = typeCheckExpression(firstBranch, typeToMatch, context)
    val secondBranchType = typeCheckExpression(secondBranch, typeToMatch, context)

    // Throw error if inferred types of the 2 branches do not match
    if (firstBranchType != secondBranchType)
        throw TypeError(
            "Branches of If statement must be of the same type.\n" +
                    "Found ${PrettyPrinter.print(firstBranchType)} and ${PrettyPrinter.print(secondBranchType)}"
        )

    return firstBranchType
}

fun typeCheckAbstraction(abstraction: Abstraction, typeToMatch: Type?, outerContext: MutableMap<String, Type>): Type? {
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

    // Returning inferred type of the Abstraction in case typeToMatch is null
    if (typeToMatch == null) {
        val returnType = typeCheckExpression(innerExpr, null, innerContext)
        return constructTypeFun(firstParam.type_, returnType)
    }

    when (typeToMatch) {
        is TypeFun -> {
            typeCheckFirstParam(firstParam.type_, typeToMatch.listtype_[0])
            typeCheckExpression(innerExpr, typeToMatch.type_, innerContext)
        }

        else -> throw TypeError(
            "Type ${PrettyPrinter.print(typeToMatch)}\n" +
                    "does not match type of given abstraction ${PrettyPrinter.print(abstraction)}\n"
        )
    }

    return typeToMatch
}

// Typechecking the first parameter of an application given it's expected and actual types
fun typeCheckFirstParam(firstParamType: Type?, typeToMatch: Type?) {
    if (firstParamType != typeToMatch) {
        throw TypeError(
            "Type ${PrettyPrinter.print(firstParamType)}\n" +
                    "does not match declared type ${PrettyPrinter.print(typeToMatch)}"
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

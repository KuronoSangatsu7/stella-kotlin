package org.stella.typecheck
import org.syntax.stella.Absyn.*
import org.syntax.stella.PrettyPrinter
import java.util.LinkedList

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

fun typeCheckFunctionDeclaration(decl: DeclFun) {
    val context = mutableMapOf<String, Type>()

    var returnType = when (decl.returntype_) {
        is SomeReturnType -> {decl.returntype_.type_ }
        else -> throw TypeError("A function declaration must specify its return type.")
    }

    for (paramDecl in decl.listparamdecl_) {
        var params = parseParamDecl(paramDecl)
        context += params

        var paramType: Type? = null
        for (value in params.values)
            paramType = value

        // Add func signature to global context
        // Forced the assignment here because I know for a fact the function will have one arg with a type

        var functionType = constructTypeFun(paramType, returnType)

        globalContext[decl.stellaident_] = functionType
    }

//    val callerType = decl.returntype_
//
//    if (getExpressionType(decl.expr_, context) != callerType) {
//        throw TypeError("Ksmk")
//    }

    val returnExpr = decl.expr_
    typeCheckExpression(returnExpr, returnType, context)
}

fun parseParamDecl(paramDecl: ParamDecl): Map<String, Type> = when (paramDecl) {
    // TODO: handle case where parameter is function? do i really need to?
    is AParamDecl -> mapOf(paramDecl.stellaident_ to paramDecl.type_)
    else -> mapOf()
}

fun typeCheckExpression(expr: Expr, typeToMatch: Type?, context: MutableMap<String, Type>): Type? = when (expr) {
    is Var -> typeCheckVar(expr, typeToMatch, context)
    is ConstTrue -> typeCheckBool(typeToMatch)
    is ConstFalse -> typeCheckBool(typeToMatch)
    is ConstInt -> typeCheckInt(expr.integer_, typeToMatch)
    is Succ -> typeCheckSucc(expr, typeToMatch, context)
    is If -> typeCheckIf(expr, typeToMatch, context)
    is NatRec -> null
    is IsZero -> typeCheckIsZero(expr, typeToMatch, context)
    is Abstraction -> typeCheckAbstraction(expr, typeToMatch, context)
    is Application -> typeCheckApplication(expr, typeToMatch, context)
    else -> null
}


fun typeCheckApplication(expr: Application, typeToMatch: Type?, context: MutableMap<String, Type>): Type? {
    when (val functionType = typeCheckExpression(expr.expr_, null, context)) {
        is TypeFun -> {
            val firstArgExpectedType = functionType.listtype_[0]
            val applicationReturnType = functionType.type_
            val firstArgType = typeCheckExpression(expr.listexpr_[0], firstArgExpectedType, context)
            if (firstArgType != firstArgExpectedType) {
                throw TypeError("Expected argument of type ${PrettyPrinter.print(firstArgExpectedType)}" +
                        "Found ${PrettyPrinter.print(firstArgType)}" +
                        "In Application ${PrettyPrinter.print(expr)}")
            }

            return applicationReturnType
        }

        else -> {
            throw TypeError("ksmk")
        }
    }
}

fun typeCheckNatRec(natRec: NatRec, typeToMatch: Type?, context: MutableMap<String, Type>): Type? {
    typeCheckExpression(natRec.expr_1, TypeNat(), context)
    val secondExprType = typeCheckExpression(natRec.expr_2, null, context)
    val thirdExprType = typeCheckExpression(natRec.expr_3, null, context)

    val innerReturnType = constructTypeFun(secondExprType, secondExprType)
    val thirdExprExpectedType = constructTypeFun(TypeNat(), innerReturnType)

    if (thirdExprType != thirdExprExpectedType) {
        throw TypeError("NatRec done fucked up")
    }

    return secondExprType
}

fun typeCheckVar(variable: Var, typeToMatch: Type?, context: MutableMap<String, Type>): Type? {
    //TODO: What is NoReturnType? return type of anon function probably
    val variableName = variable.stellaident_
    val variableType: Type?

    // Try to find the variable in context otherwise it's a function declaration then get it from global context

    if (variableName in context.keys) {
        variableType = context[variableName]
    }

    else {
        variableType = globalContext[variableName]
    }

    if (typeToMatch == null) {
        return variableType
    }

    // Throw error if variable type in context does not match return type
    if (variableType != typeToMatch)
        throw TypeError("ksmk return type ${PrettyPrinter.print(typeToMatch)} " +
                "does not match actual type ${PrettyPrinter.print(variableType)}.")

    return variableType
}

fun typeCheckBool(typeToMatch: Type?): Type? = when (typeToMatch) {
    // Throw error is return type is not Bool
    !is TypeBool -> throw TypeError("Declared return type ${PrettyPrinter.print(typeToMatch)} " +
                "does not match actual type Bool.")
    else -> TypeBool()
}
fun typeCheckInt(intVal: Int, typeToMatch: Type?): Type? {
    //TODO: What is type of an int num?

    // Throw error if number is not 0 or return type is not Nat
    if(intVal != 0 || typeToMatch !is TypeNat)
        throw TypeError("Declared return type ${PrettyPrinter.print(typeToMatch)} does not match actual type.")

    return TypeNat()
}

fun typeCheckSucc(succExpr:Succ, typeToMatch: Type?, context: MutableMap<String, Type>): Type? {
    // Throw error if return type is not Nat
    when (typeToMatch) {
        !is TypeNat -> throw TypeError("Declared return type ${PrettyPrinter.print(typeToMatch)} " +
                "does not match actual type Nat.")

    }

    // Throw error if content is not one of
    when (val succContent = succExpr.expr_) {
        // Succ
        is Succ -> typeCheckSucc(succContent, typeToMatch, context)
        // 0
        is ConstInt -> typeCheckInt(succContent.integer_, typeToMatch)
        // a variable of type Nat
        is Var -> typeCheckVar(succContent, typeToMatch, context)

        else -> throw TypeError("An argument of Succ must be of type Nat, " +
                "but provided argument ${PrettyPrinter.print(succContent)}")
    }

    return TypeNat()
}

fun typeCheckIsZero(isZeroExpr: IsZero, typeToMatch: Type?, context: MutableMap<String, Type>): Type? {
    // Throw error if return type is not Bool
    when (typeToMatch) {
        !is TypeBool -> throw TypeError("Declared return type ${PrettyPrinter.print(typeToMatch)} " +
                "does not match actual type Bool.")
    }

    // Throw error if content is not one of
    when (val isZeroContent = isZeroExpr.expr_) {
        // Succ
        is Succ -> typeCheckSucc(isZeroContent, TypeNat(), context)
        //0
        is ConstInt -> typeCheckInt(isZeroContent.integer_, TypeNat())
        // a variable of type Nat
        is Var -> typeCheckVar(isZeroContent, TypeNat(), context)

        else -> throw TypeError("An argument of IsZero must be of type Nat, " +
                "but provided argument ${PrettyPrinter.print(isZeroContent)}")
    }

    return TypeBool()
}

fun typeCheckIf(ifExpr: If, typeToMatch: Type?, context: MutableMap<String, Type>): Type? {
    val condition = ifExpr.expr_1
    val firstBranch = ifExpr.expr_2
    val secondBranch = ifExpr.expr_3

    // Throw error if condition is not Bool
    typeCheckExpression(condition, TypeBool(), context)

    // Throw error if any of the 2 branches do not match the return type of the entire construct
    typeCheckExpression(firstBranch, typeToMatch, context)
    typeCheckExpression(secondBranch, typeToMatch, context)

    return typeToMatch
}

fun typeCheckAbstraction(abstraction: Abstraction, typeToMatch: Type?, outerContext: MutableMap<String, Type>): Type? {
    var innerContext = mutableMapOf<String, Type>()

    for (paramDecl in abstraction.listparamdecl_) {
        innerContext += parseParamDecl(paramDecl)
    }

    innerContext = (outerContext + innerContext) as MutableMap<String, Type>

    val innerExpr = abstraction.expr_
    val firstParam = abstraction.listparamdecl_[0] as AParamDecl

    if (typeToMatch == null) {
        return typeCheckExpression(innerExpr, null, innerContext)
    }

    when (typeToMatch) {
        is TypeFun -> {
            typeCheckFirstParam(firstParam.type_, typeToMatch.listtype_[0])
            typeCheckExpression(innerExpr, typeToMatch.type_, innerContext)
        }

        else -> throw TypeError("Type ${PrettyPrinter.print(typeToMatch)} " +
                "does not match type of given Abstraction")
    }

    return typeToMatch
}

fun typeCheckFirstParam(firstParamType: Type?, typeToMatch: Type?) {
    if (firstParamType != typeToMatch) {
        throw TypeError("Type ${PrettyPrinter.print(firstParamType)} " +
                "does not match declared type ${PrettyPrinter.print(typeToMatch)}")
    }
}

fun constructTypeFun(argType: Type?, returnType: Type?): Type {
    val argListType = ListType()
    argListType.add(argType)

    return TypeFun(argListType, returnType)
}
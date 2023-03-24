package org.stella.typecheck
import org.syntax.stella.Absyn.*

class TypeError(message: String) : Exception(message)

object TypeCheck {
    @Throws(Exception::class)
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
        is SomeReturnType -> decl.returntype_.type_
        else -> throw TypeError("A function declaration must specify its return type.")
    }

    for (paramDecl in decl.listparamdecl_) {
        context += parseParamDecl(paramDecl)
    }

    val returnExpr = decl.expr_
    typeCheckExpression(returnExpr, returnType, context)
}

fun typeCheckExpression(expr: Expr, typeToMatch: Type?, context: MutableMap<String, Type>) {
    when (expr) {
        is Var -> typeCheckVar(expr, typeToMatch, context)
        is ConstTrue -> typeCheckBool(typeToMatch)
        is ConstFalse -> typeCheckBool(typeToMatch)
        is ConstInt -> typeCheckInt(expr.integer_, typeToMatch)
        is Succ -> typeCheckSucc(expr, typeToMatch, context)
        is If -> typeCheckIf(expr, typeToMatch, context)
        is NatRec -> null //TODO: dis might be hard i tink later
        is IsZero -> typeCheckIsZero(expr, typeToMatch, context)
        is Abstraction -> expr.listparamdecl_ //TODO: dis recursive but i need a new function
    }
}

fun parseParamDecl(paramDecl: ParamDecl): Map<String, Type> = when (paramDecl) {
    is AParamDecl -> mapOf(paramDecl.stellaident_ to paramDecl.type_)
    else -> mapOf()
}
fun typeCheckVar(variable: Var, typeToMatch: Type?, context: MutableMap<String, Type>) {
    //TODO: What is NoReturnType?
    val variableName = variable.stellaident_
    val variableType = context[variableName]

    // Throw error if variable type in context does not match return type
    if (variableType != typeToMatch)
        throw TypeError("Declared return type $typeToMatch doesn't match actual type $variableType.")
}

fun typeCheckBool(typeToMatch: Type?): Nothing? = when (typeToMatch) {
    // Throw error is return type is not Bool
        !is TypeBool -> throw TypeError("Declared return type $typeToMatch doesn't match actual type Bool.")
        else -> null
    }
fun typeCheckInt(intVal: Int, typeToMatch: Type?) {
    //TODO: What is type of an int num?

    // Throw error if number is not 0 or return type is not Nat
    if(intVal != 0 || typeToMatch !is TypeNat)
        throw TypeError("Declared return type $typeToMatch doesn't match actual type .")
}

fun typeCheckSucc(succExpr:Succ, typeToMatch: Type?, context: MutableMap<String, Type>) {
    // Throw error if return type is not Nat
    when (typeToMatch) {
        !is TypeNat -> throw TypeError("Declared return type $typeToMatch doesn't match actual type Nat.")
    }

    // Throw error if content is not one of
    when (val succContent = succExpr.expr_) {
        // Succ
        is Succ -> typeCheckSucc(succContent, typeToMatch, context)
        // 0
        is ConstInt -> typeCheckInt(succContent.integer_, typeToMatch)
        // a variable of type Nat
        is Var -> typeCheckVar(succContent, typeToMatch, context)

        else -> throw TypeError("An argument of Succ must be of type Nat, but provided argument with type ${succContent.toString()}")
    }
}

fun typeCheckIsZero(isZeroExpr: IsZero, typeToMatch: Type?, context: MutableMap<String, Type>) {
    // Throw error if return type is not Bool
    when (typeToMatch) {
        !is TypeBool -> throw TypeError("Declared return type $typeToMatch doesn't match actual type Bool.")
    }

    // Throw error if content is not one of
    when (val isZeroContent = isZeroExpr.expr_) {
        // Succ
        is Succ -> typeCheckSucc(isZeroContent, TypeNat(), context)
        //0
        is ConstInt -> typeCheckInt(isZeroContent.integer_, TypeNat())
        // a variable of type Nat
        is Var -> typeCheckVar(isZeroContent, TypeNat(), context)

        else -> throw TypeError("An argument of IsZero must be of type Nat, but provided argument with type ${isZeroContent.toString()}")
    }
}

fun typeCheckIf(ifExpr: If, typeToMatch: Type?, context: MutableMap<String, Type>) {
    val condition = ifExpr.expr_1
    val firstBranch = ifExpr.expr_2
    val secondBranch = ifExpr.expr_3

    // Throw error if condition is not Bool
    typeCheckExpression(condition, TypeBool(), context)

    // Throw error if any of the 2 branches do not match the return type of the entire construct
    typeCheckExpression(firstBranch, typeToMatch, context)
    typeCheckExpression(secondBranch, typeToMatch, context)
}

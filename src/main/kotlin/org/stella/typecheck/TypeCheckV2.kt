package org.stella.typecheck

import org.syntax.stella.Absyn.*

fun getExpressionType(expr: Expr, context: MutableMap<String, Type>) : Type? =
    when (expr) {
        is Var -> context[expr.stellaident_]
        is ConstTrue -> TypeBool()
        is ConstFalse -> TypeBool()
        is ConstInt -> {
            typeCheckInt(expr.integer_, TypeNat())
            TypeNat()
        }

        is Succ -> {
            typeCheckSucc(expr, TypeNat(), context)
            TypeNat()
        }

        is If -> {
            val condition = expr.expr_1
            val firstBranch = expr.expr_2
            val secondBranch = expr.expr_3

            if (getExpressionType(condition, context) != TypeBool()) {
                throw TypeError("ksmk")
            }

            val firstBranchType = getExpressionType(firstBranch, context)
            val secondBranchType = getExpressionType(secondBranch, context)

            if (firstBranchType != secondBranchType) {
                throw TypeError("ksmk")
            }

            firstBranchType
        }

        is NatRec -> {
            //TODO
            TypeNat()
        }

        is IsZero -> {
            typeCheckIsZero(expr, TypeBool(), context)
            TypeBool()
        }

        is Abstraction -> {
            getAbstractionType(expr, context)
        }

        is Application -> {
            getApplicationType(expr, context)
        }

        else -> null
    }

fun getRightBranchType(expr: Expr, context: MutableMap<String, Type>): Type? {
    return getExpressionType(expr,  context)
}

fun getApplicationType(expr: Application, context: MutableMap<String, Type>): Type? {
    val rightBranchType = getRightBranchType(expr.listexpr_[0], context)

    when (expr.expr_) {
        is Var -> {
            if (rightBranchType != globalContext[expr.expr_.stellaident_]?.first) {
                throw TypeError("ksmk")
            }

            else
                return globalContext[expr.expr_.stellaident_]?.second
        }

        is Application -> {
            return getApplicationType(expr.expr_, context)
        }

        else -> return null
    }
}
fun getAbstractionType(abstraction: Abstraction, outerContext: MutableMap<String, Type>): Type? {
    var innerContext = mutableMapOf<String, Type>()

    for (paramDecl in abstraction.listparamdecl_) {
        innerContext += parseParamDecl(paramDecl)
    }

    innerContext = (outerContext + innerContext) as MutableMap<String, Type>

    val returnType = getExpressionType(abstraction.expr_, innerContext)

    val arg = abstraction.listparamdecl_[0] as AParamDecl

    return null
}

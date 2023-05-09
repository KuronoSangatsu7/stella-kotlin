package org.stella.typecheck

import org.syntax.stella.Absyn.*
import org.syntax.stella.Absyn.Annotation
import org.syntax.stella.PrettyPrinter

class TypeError(message: String) : Exception(message)

@Suppress("UNUSED")
fun debug(arg: Any?) {
    val className = Throwable().stackTrace[1].className
    val methodName = Throwable().stackTrace[1].methodName

    val output = try {
        when (arg) {
            is Annotation -> PrettyPrinter.print(arg)
            is Binding -> PrettyPrinter.print(arg)
            is Decl -> PrettyPrinter.print(arg)
            is Expr -> PrettyPrinter.print(arg)
            is ExprData -> PrettyPrinter.print(arg)
            is Extension -> PrettyPrinter.print(arg)
            is LabelledPattern -> PrettyPrinter.print(arg)
            is LanguageDecl -> PrettyPrinter.print(arg)
            is ListAnnotation -> PrettyPrinter.print(arg)
            is ListBinding -> PrettyPrinter.print(arg)
            is ListDecl -> PrettyPrinter.print(arg)
            is ListExpr -> PrettyPrinter.print(arg)
            is ListExtension -> PrettyPrinter.print(arg)
            is ListExtensionName -> PrettyPrinter.print(arg)
            is ListLabelledPattern -> PrettyPrinter.print(arg)
            is ListLocalDecl -> PrettyPrinter.print(arg)
            is ListMatchCase -> PrettyPrinter.print(arg)
            is ListParamDecl -> PrettyPrinter.print(arg)
            is ListPattern -> PrettyPrinter.print(arg)
            is ListPatternBinding -> PrettyPrinter.print(arg)
            is ListRecordFieldType -> PrettyPrinter.print(arg)
            is ListStellaIdent -> PrettyPrinter.print(arg)
            is ListType -> PrettyPrinter.print(arg)
            is ListVariantFieldType -> PrettyPrinter.print(arg)
            is LocalDecl -> PrettyPrinter.print(arg)
            is MatchCase -> PrettyPrinter.print(arg)
            is OptionalTyping -> PrettyPrinter.print(arg)
            is ParamDecl -> PrettyPrinter.print(arg)
            is Pattern -> PrettyPrinter.print(arg)
            is PatternBinding -> PrettyPrinter.print(arg)
            is PatternData -> PrettyPrinter.print(arg)
            is Program -> PrettyPrinter.print(arg)
            is RecordFieldType -> PrettyPrinter.print(arg)
            is ReturnType -> PrettyPrinter.print(arg)
            is ThrowType -> PrettyPrinter.print(arg)
            is Type -> PrettyPrinter.print(arg)
            is Typing -> PrettyPrinter.print(arg)
            is VariantFieldType -> PrettyPrinter.print(arg)
            else -> arg
        }
    } catch (e: Exception) {
        print(arg)
    }

    println("DEBUGGING FROM $className.$methodName:")
    println(output)
}

class GlobalContext {
    private var functionTypes: MutableMap<String, Type> = mutableMapOf()
    private var functionGenericTypes: MutableMap<String, List<String>> = mutableMapOf()

    fun appendFunction(funcIdent: String, funcType: Type) {
        this.functionTypes += mapOf(funcIdent to funcType)
    }

    fun appendFunctionGenerics(funcIdent: String, generics: List<String>) {
        this.functionGenericTypes += mapOf(funcIdent to generics)
    }

    fun getFunctionType(funcIdent: String): Type? {
        return this.functionTypes.getOrDefault(funcIdent, null)
    }

    fun getFunctionGenerics(funcIdent: String): List<String> {
        return this.functionGenericTypes.getOrDefault(funcIdent, listOf())
    }
}

@Suppress("UNUSED")
class Context {
    private var variables: MutableMap<String, Type> = mutableMapOf()
    private var availableGenericTypes: MutableList<String> = mutableListOf()

    constructor()

    constructor(initialVariables: Map<String, Type>) {
        this.variables += initialVariables
    }

    constructor(initialAvailableTypes: List<String>) {
        this.availableGenericTypes.addAll(initialAvailableTypes)
    }

    constructor(oldContext: Context) {
        this.variables = oldContext.variables
        this.availableGenericTypes = oldContext.availableGenericTypes
    }

    fun appendVariables(newVariables: Map<String, Type>) {
        this.variables += newVariables
    }

    fun appendTypes(newTypes: List<String>) {
        this.availableGenericTypes.addAll(newTypes)
    }

    fun getVariableType(varIdent: String): Type? {
        return this.variables[varIdent]
    }

    fun hasType(typeIdent: String): Boolean {
        return (typeIdent in this.availableGenericTypes)
    }

    fun hasVariable(varIdent: String): Boolean {
        return (varIdent in this.variables.keys)
    }
}

class TypeCheck {
    private var globalContext = GlobalContext()
    fun typeCheckProgram(program: Program?) {
        when (program) {
            is AProgram ->
                for (decl in program.listdecl_) {
                    when (decl) {
                        is DeclFun -> typeCheckFunctionDeclaration(decl)
                        is DeclFunGeneric -> typeCheckGenericFunctionDeclaration(decl)
                    }
                }
        }
    }

    // Typechecks the contents of a function declaration against it's declared types
    // after adding it to the global scope
    private fun typeCheckFunctionDeclaration(decl: DeclFun) {
        typeCheckFunction(decl.returntype_, decl.listparamdecl_, decl.stellaident_, decl.expr_, Context())
    }

    private fun typeCheckGenericFunctionDeclaration(decl: DeclFunGeneric) {
        val genericTypeContext = mutableListOf<String>()
        // add generic types to context
        for (ident in decl.liststellaident_)
            genericTypeContext.add(ident)

        val context = Context(genericTypeContext)
        globalContext.appendFunctionGenerics(decl.stellaident_, genericTypeContext)

        typeCheckFunction(decl.returntype_, decl.listparamdecl_, decl.stellaident_, decl.expr_, context)
    }

    private fun typeCheckFunction(
        returnType: ReturnType,
        paramList: ListParamDecl,
        funcIdent: String,
        returnExpr: Expr,
        context: Context
    ) {
        val variableContext = mutableMapOf<String, Type>()
        val expectedReturnType = when (returnType) {
            is SomeReturnType -> {
                returnType.type_
            }

            else -> throw TypeError("A function declaration must specify its return type.")
        }

        // Will never throw here with valid input
        if (!isValidType(expectedReturnType, context))
            throw TypeError("Unexpected Type Error")

        for (paramDecl in paramList) {
            val params = parseParamDecl(paramDecl, context)
            variableContext += params

            var paramType: Type? = null
            for (value in params.values)
                paramType = value

            // Add function signature to global context
            val functionType = constructTypeFun(paramType, expectedReturnType)
            globalContext.appendFunction(funcIdent, functionType)
        }

        context.appendVariables(variableContext)

        val actualReturnType = typeCheckExpression(returnExpr, expectedReturnType, context)

        if (!compareWithSubtyping(actualReturnType, expectedReturnType))
            throw TypeError(
                "Expected type ${PrettyPrinter.print(expectedReturnType)}" +
                        "Instead found type ${PrettyPrinter.print(actualReturnType)}" +
                        "In Expression ${PrettyPrinter.print(returnExpr)}"
            )
    }

    // Writes the given parameter declarations into a map to act as the function's local scope later on
    private fun parseParamDecl(paramDecl: ParamDecl, context: Context): Map<String, Type> = when (paramDecl) {
        is AParamDecl -> {
            if (isValidType(paramDecl.type_, context))
                mapOf(paramDecl.stellaident_ to paramDecl.type_)

            // Will never reach else branch with valid input
            else
                mapOf()
            //throw TypeError("Unexpected Type Error")
        }

        else -> mapOf()
    }

    // a function, that, given a type and context, validates that the given types does not use any
    // Undefined TypeVar
    private fun isValidType(givenType: Type?, context: Context): Boolean = when (givenType) {
        // TODO: Other types could be supported here
        is TypeFun ->
            isValidType(givenType.listtype_[0], context) && isValidType(givenType.type_, context)

        is TypeSum ->
            isValidType(givenType.type_1, context) &&
                    isValidType(givenType.type_2, context)

        is TypeTuple -> givenType.listtype_.map { element ->
            isValidType(
                element,
                context
            )
        }.all { it }

        is TypeRecord -> givenType.listrecordfieldtype_.map { element ->
            when (element) {
                is ARecordFieldType ->
                    isValidType(element.type_, context)

                else -> false
            }
        }.all { it }

        is TypeBool -> true
        is TypeNat -> true
        is TypeUnit -> true
        is TypeTop -> true
        is TypeBottom -> true
        is TypeRef -> isValidType(givenType.type_, context)
        is TypeVar ->
            if (context.hasType(givenType.stellaident_))
                true
            else
                throw TypeError("unknown type alias ${givenType.stellaident_}")

        is TypeForAll -> {
            context.appendTypes(givenType.liststellaident_)
            isValidType(givenType.type_, context)
        }

        else -> false
    }

    // Typechecks a given expression against the provided expectedType using the given local/global scopes
    // Fails if the actual type does not match the one given
    // When given null as expectedType
    // it simply returns the inferred type of the expression (assuming no TypeErrors happen further down the line)
    // The same thing goes for all the typeCheck functions
    private fun typeCheckExpression(expr: Expr, expectedType: Type?, context: Context): Type? = when (expr) {
        is Var -> typeCheckVar(expr, expectedType, context)
        is Tuple -> typeCheckTuple(expr, expectedType, context)
        is DotTuple -> typeCheckDotTuple(expr, expectedType, context)
        is Record -> typeCheckRecord(expr, expectedType, context)
        is DotRecord -> typeCheckDotRecord(expr, expectedType, context)
        is ConstTrue -> typeCheckBool(expectedType)
        is ConstFalse -> typeCheckBool(expectedType)
        is ConstInt -> typeCheckInt(expectedType)
        is ConstUnit -> typeCheckUnit(expectedType)
        is Succ -> typeCheckSucc(expr, expectedType, context)
        is Pred -> typeCheckPred(expr, expectedType, context)
        is If -> typeCheckIf(expr, expectedType, context)
        is Match -> typeCheckMatch(expr, expectedType, context)
        is Inl -> typeCheckInl(expr, expectedType, context)
        is Inr -> typeCheckInr(expr, expectedType, context)
        is NatRec -> typeCheckNatRec(expr, expectedType, context)
        is IsZero -> typeCheckIsZero(expr, expectedType, context)
        is Abstraction -> typeCheckAbstraction(expr, expectedType, context)
        is TypeAbstraction -> typeCheckTypeAbstraction(expr, context)
        is Application -> typeCheckApplication(expr, expectedType, context)
        is TypeApplication -> typeCheckTypeApplication(expr, context)
        is Sequence -> typeCheckSequence(expr, expectedType, context)
        is Panic -> typeCheckPanic(expr, expectedType)
        is Ref -> typeCheckRef(expr, expectedType, context)
        is Deref -> typeCheckDeref(expr, expectedType, context)
        is Assign -> typeCheckAssign(expr, expectedType, context)
        is Let -> typeCheckLetBinding(expr, expectedType, context)
        is TypeCast -> typeCheckTypeCast(expr, expectedType, context)
        is Add -> typeCheckAdd(expr, expectedType, context)
        is Subtract -> typeCheckSubtract(expr, expectedType, context)
        is Multiply -> typeCheckMultiply(expr, expectedType, context)
        is Divide -> typeCheckDivide(expr, expectedType, context)
        is LessThan -> typeCheckLessThan(expr, expectedType, context)
        is LessThanOrEqual -> typeCheckLessThanOrEqual(expr, expectedType, context)
        is GreaterThan -> typeCheckGreaterThan(expr, expectedType, context)
        is GreaterThanOrEqual -> typeCheckGreaterThanOrEqual(expr, expectedType, context)
        is Equal -> typeCheckEqual(expr, expectedType, context)
        is NotEqual -> typeCheckNotEqual(expr, expectedType, context)
        else -> null
    }

    // Given any arbitrary Type, a variable identifier, and a new type to apply
    // Replaces all occurrences of the variable within the given type to the new type
    private fun replaceVarType(
        originalType: Type?,
        varIdent: String,
        varType: Type?,
        depth: Int = 0,
        swappedBefore: Boolean = false
    ): Type? =
        when (originalType) {
            // TODO: Other types could be supported here
            is TypeFun -> constructTypeFun(
                replaceVarType(originalType.listtype_[0], varIdent, varType, depth),
                replaceVarType(originalType.type_, varIdent, varType, depth)
            )

            is TypeSum -> TypeSum(
                replaceVarType(originalType.type_1, varIdent, varType, depth),
                replaceVarType(originalType.type_2, varIdent, varType, depth)
            )

            is TypeTuple -> TypeTuple(ListType().apply {
                addAll(originalType.listtype_.map { element ->
                    replaceVarType(
                        element,
                        varIdent,
                        varType,
                        depth
                    )
                })
            })

            is TypeRecord -> TypeRecord(ListRecordFieldType().apply {
                addAll(originalType.listrecordfieldtype_.map { element ->
                    when (element) {
                        is ARecordFieldType -> ARecordFieldType(
                            element.stellaident_,
                            replaceVarType(element.type_, varIdent, varType, depth)
                        )

                        else -> null
                    }
                })
            })

            is TypeBool -> TypeBool()
            is TypeNat -> TypeNat()
            is TypeUnit -> TypeUnit()
            is TypeTop -> TypeTop()
            is TypeBottom -> TypeBottom()
            is TypeRef -> TypeRef(replaceVarType(originalType.type_, varIdent, varType, depth))
            is TypeVar -> if (originalType.stellaident_ == varIdent) varType else originalType

            is TypeForAll -> {

                if (varIdent in originalType.liststellaident_ && swappedBefore)
                    originalType
                else if (varType is TypeVar && varType.stellaident_ in originalType.liststellaident_) {
                    val newVarIdent = varType.stellaident_ + depth.toString()
                    val oldVarIdent = varType.stellaident_
                    val oldListStellaIdent = originalType.liststellaident_

                    val newListStellaIdent = oldListStellaIdent.map {
                        if (it == oldVarIdent) newVarIdent else it
                    }.toCollection(ListStellaIdent())

                    var ret = TypeForAll(
                        newListStellaIdent,
                        replaceVarType(
                            originalType.type_,
                            oldVarIdent,
                            TypeVar(newVarIdent),
                            depth + 1,
                            swappedBefore = true
                        )
                    )
                    ret = TypeForAll(
                        ret.liststellaident_,
                        replaceVarType(ret.type_, varIdent, varType, depth + 1, swappedBefore = true)
                    )
                    ret
                } else
                    TypeForAll(
                        originalType.liststellaident_,
                        replaceVarType(originalType.type_, varIdent, varType, depth, swappedBefore = true)
                    )
            }

            else -> null
        }

    private fun compareWithSubtyping(subType: Type?, superType: Type?): Boolean {
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
            is TypeFun -> isFunSubtypeOf(subType, superType as TypeFun)
            is TypeRecord -> isRecordSubtypeOf(subType, superType as TypeRecord)
            else -> false
        }
    }

    // Given 2 types, compares them taking into account null values
    private fun compareNullSafe(type1: Type?, type2: Type?): Boolean {
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

    private fun isFunSubtypeOf(subType: TypeFun, superType: TypeFun): Boolean {
        return (compareWithSubtyping(subType.type_, superType.type_) && compareWithSubtyping(
            superType.listtype_[0],
            subType.listtype_[0]
        ))
    }

    private fun isRecordSubtypeOf(subType: TypeRecord, superType: TypeRecord): Boolean {
        // TODO: Check if for subtyping records, each field needs to be the exact same as its peer or a subtype of it

        val superRecordFieldTypes: MutableMap<String, Type> = mutableMapOf()

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
    private fun getMostGeneralType(listTypes: MutableList<Type?>): Type? {
        var mostGeneralType = listTypes.elementAt(0)

        for (type in listTypes.filterIndexed { index, _ -> index > 0 })
            if (!compareWithSubtyping(type, mostGeneralType))
                if (compareWithSubtyping(mostGeneralType, type))
                    mostGeneralType = type
                else
                    return null

        return mostGeneralType
    }

    // Performs typechcking for operators, both arithmetic and comparison
    private fun typeCheckNatOperators(
        operatorType: String,
        leftExpr: Expr,
        rightExpr: Expr,
        expectedType: Type?,
        context: Context
    ): Type {
        typeCheckExpression(leftExpr, TypeNat(), context)
        typeCheckExpression(rightExpr, TypeNat(), context)

        if (expectedType == null)
            return if (operatorType == "comp")
                TypeBool()
            else
                TypeNat()
        if (operatorType == "comp") {
            if (expectedType !is TypeBool)
                throw TypeError(
                    "Expected type ${PrettyPrinter.print(expectedType)}\n" +
                            "Instead found type ${PrettyPrinter.print(TypeBool())}"
                )
        } else
            if (expectedType !is TypeNat)
                throw TypeError(
                    "Expected type ${PrettyPrinter.print(expectedType)}\n" +
                            "Instead found type ${PrettyPrinter.print(TypeNat())}"
                )

        return if (operatorType == "comp")
            TypeBool()
        else
            TypeNat()
    }

    private fun typeCheckNotEqual(compExpr: NotEqual, expectedType: Type?, context: Context): Type {
        return typeCheckNatOperators("comp", compExpr.expr_1, compExpr.expr_2, expectedType, context)
    }

    private fun typeCheckEqual(compExpr: Equal, expectedType: Type?, context: Context): Type {
        return typeCheckNatOperators("comp", compExpr.expr_1, compExpr.expr_2, expectedType, context)
    }

    private fun typeCheckGreaterThanOrEqual(
        compExpr: GreaterThanOrEqual,
        expectedType: Type?,
        context: Context
    ): Type {
        return typeCheckNatOperators("comp", compExpr.expr_1, compExpr.expr_2, expectedType, context)
    }

    private fun typeCheckGreaterThan(compExpr: GreaterThan, expectedType: Type?, context: Context): Type {
        return typeCheckNatOperators("comp", compExpr.expr_1, compExpr.expr_2, expectedType, context)
    }

    private fun typeCheckLessThanOrEqual(compExpr: LessThanOrEqual, expectedType: Type?, context: Context): Type {
        return typeCheckNatOperators("comp", compExpr.expr_1, compExpr.expr_2, expectedType, context)
    }

    private fun typeCheckLessThan(compExpr: LessThan, expectedType: Type?, context: Context): Type {
        return typeCheckNatOperators("comp", compExpr.expr_1, compExpr.expr_2, expectedType, context)
    }

    private fun typeCheckDivide(divideExpr: Divide, expectedType: Type?, context: Context): Type {
        return typeCheckNatOperators("div", divideExpr.expr_1, divideExpr.expr_2, expectedType, context)
    }

    private fun typeCheckMultiply(multiplyExpr: Multiply, expectedType: Type?, context: Context): Type {
        return typeCheckNatOperators("mul", multiplyExpr.expr_1, multiplyExpr.expr_2, expectedType, context)
    }

    private fun typeCheckSubtract(subtractExpr: Subtract, expectedType: Type?, context: Context): Type {
        return typeCheckNatOperators("sub", subtractExpr.expr_1, subtractExpr.expr_2, expectedType, context)
    }

    private fun typeCheckAdd(addExpr: Add, expectedType: Type?, context: Context): Type {
        return typeCheckNatOperators("add", addExpr.expr_1, addExpr.expr_2, expectedType, context)
    }

    private fun typeCheckTypeCast(castExpr: TypeCast, expectedType: Type?, context: Context): Type? {
        val exprType = typeCheckExpression(castExpr.expr_, null, context)
        //TODO: Do we allow casting no matter what (no hierarchy)?

        if (expectedType == null)
            return castExpr.type_

        if (!compareWithSubtyping(exprType, castExpr.type_))
            throw TypeError(
                "Cannot cast ${PrettyPrinter.print(exprType)}\n" +
                        "to type ${PrettyPrinter.print(castExpr.type_)}"
            )

        if (!compareWithSubtyping(castExpr.type_, expectedType))
            throw TypeError(
                "Expected type ${PrettyPrinter.print(expectedType)}\n" +
                        "Instead found type ${PrettyPrinter.print(castExpr.type_)}"
            )

        return castExpr.type_

    }

    private fun typeCheckLetBinding(letExpr: Let, expectedType: Type?, outerContext: Context): Type? {
        val innerVariableContext = mutableMapOf<String, Type>()

        // Creating local scope
        innerVariableContext += parseListPatternBinding(letExpr.listpatternbinding_, outerContext)

        // Adding previous scope to new scope
        // Shadowing occurs naturally here as in the old values get overwritten
        val innerContext = Context(outerContext)
        innerContext.appendVariables(innerVariableContext)

        return typeCheckExpression(letExpr.expr_, expectedType, innerContext)
    }

    private fun typeCheckAssign(expr: Assign, expectedType: Type?, context: Context): Type {

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

    private fun typeCheckDeref(expr: Deref, expectedType: Type?, context: Context): Type? {

        when (val innerExprType = typeCheckExpression(expr.expr_, null, context)) {
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

    private fun typeCheckRef(expr: Ref, expectedType: Type?, context: Context): Type {
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

    private fun typeCheckPanic(expr: Panic, expectedType: Type?): Type {
        if (expectedType == null)
            throw TypeError("Illegal expression ${PrettyPrinter.print(expr)}")

        return expectedType
    }

    private fun typeCheckSequence(expr: Sequence, expectedType: Type?, context: Context): Type? {
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

    private fun typeCheckTypeApplication(expr: TypeApplication, context: Context): Type? {
        when (val exprType = typeCheckExpression(expr.expr_, null, context)) {
            is TypeForAll -> {
                val appliedTypes = expr.listtype_
                val typeVars = exprType.liststellaident_

                if (appliedTypes.size != typeVars.size)
                    throw TypeError(
                        "Expected ${typeVars.size} type parameters\n" +
                                "Instead found ${appliedTypes.size} type parameters\n" +
                                "In the type application ${PrettyPrinter.print(expr)}"
                    )

                @Suppress("USELESS_CAST") var returnType = exprType as TypeForAll
                for (typePair in typeVars.zip(appliedTypes))
                // replaceVarType is guaranteed to return TypeForAll when passed a TypeForAll
                    returnType = replaceVarType(returnType, typePair.first, typePair.second) as TypeForAll
                // Unwrap Forall type after replacement of variables
                return returnType.type_
            }
        }

        return null
    }

    private fun typeCheckApplication(expr: Application, expectedType: Type?, context: Context): Type? {
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

            else -> throw TypeError(
                "${PrettyPrinter.print(expr.listexpr_[0])} cannot " +
                        "be applied to ${PrettyPrinter.print(expr.expr_)} \n" +
                        "${PrettyPrinter.print(expr.expr_)} is not a function."
            )
        }
    }

    private fun typeCheckNatRec(natRec: NatRec, expectedType: Type?, context: Context): Type? {
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

        if (!compareWithSubtyping(secondExprType, expectedType))
            throw TypeError(
                "Expected type ${PrettyPrinter.print(expectedType)}" +
                        "Instead found type ${PrettyPrinter.print(secondExprType)}" +
                        "In Expression ${PrettyPrinter.print(natRec)}"
            )

        return secondExprType
    }

    private fun typeCheckVar(variable: Var, expectedType: Type?, context: Context): Type? {
        val variableName = variable.stellaident_

        // Try to find the variable in local scope
        // otherwise it's a function declaration
        val variableType: Type? = if (context.hasVariable(variableName)) {
            context.getVariableType(variableName)
        }
        // get it from global scope
        else {

            var funType = globalContext.getFunctionType(variableName)
            val funGenerics = globalContext.getFunctionGenerics(variableName)

            if (funGenerics.isEmpty())
                funType
            // Wrap the types of generic functions with Forall
            else {
                funType = TypeForAll(ListStellaIdent().apply { addAll(funGenerics) }, funType)
                funType
            }
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

    private fun typeCheckRecord(record: Record, expectedType: Type?, context: Context): Type {
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

    private fun typeCheckTuple(tuple: Tuple, expectedType: Type?, context: Context): Type {
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

    private fun typeCheckDotRecord(dotRecord: DotRecord, expectedType: Type?, context: Context): Type? {

        when (val exprType = typeCheckExpression(dotRecord.expr_, null, context)) {
            is TypeRecord -> {

                val dotRecordFieldAccessed = dotRecord.stellaident_

                // Check that expectedType is the same type as the one accessed in the record
                val typeAccessed = accessRecord(dotRecord, dotRecordFieldAccessed, exprType)

                return accessItem(dotRecord, typeAccessed, expectedType)
            }
            // Throw error if trying to access non-record expression
            else -> throw TypeError(
                "Expected an expression of type Record\n" +
                        "Instead found and expression of type ${PrettyPrinter.print(exprType)}"
            )
        }
    }

    private fun typeCheckDotTuple(dotTuple: DotTuple, expectedType: Type?, context: Context): Type? {

        when (val exprType = typeCheckExpression(dotTuple.expr_, null, context)) {
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

                return accessItem(dotTuple, typeAccessed, expectedType)
            }
            // Throw error if trying to access non-tuple expression
            else -> throw TypeError(
                "Expected an expression of type Tuple\n" +
                        "Instead found and expression of type ${PrettyPrinter.print(exprType)}"
            )
        }

    }

    private fun accessItem(expr: Expr, typeAccessed: Type?, expectedType: Type?): Type? {
        if (expectedType == null)
            return typeAccessed

        if (!compareWithSubtyping(typeAccessed, expectedType)) {
            throw TypeError(
                "Expected expression of type ${PrettyPrinter.print(expectedType)}\n" +
                        "Instead found expression of type ${PrettyPrinter.print(typeAccessed)}\n" +
                        "In ${PrettyPrinter.print(expr)}"
            )
        }

        return typeAccessed
    }

    private fun typeCheckMatch(match: Match, expectedType: Type?, context: Context): Type? {

        return when (val exprType = typeCheckExpression(match.expr_, null, context)) {
            is TypeSum -> {
                val numExpr = match.listmatchcase_.size

                // Throw error if 0 branches
                if (numExpr == 0)
                    throw TypeError("Illegal empty matching in expression ${PrettyPrinter.print(match)}")

                // Throw error if inl or inr are missing
                if (!checkInrInl(match.listmatchcase_))
                    throw TypeError("Non-exhaustive pattern matches in expression ${PrettyPrinter.print(match)}")

                // Typecheck branches
                val branchTypes = mutableListOf<Type?>()
                for (case in match.listmatchcase_) {
                    when (case) {
                        is AMatchCase -> {

                            val varTypeTuple = extractPatternVar(case.pattern_, exprType)
                            @Suppress("UNCHECKED_CAST") val caseVariableContext =
                                mapOf(varTypeTuple.first to varTypeTuple.second) as Map<String, Type>
                            val innerContext = Context(context)
                            innerContext.appendVariables(caseVariableContext)

                            val branchType = typeCheckExpression(case.expr_, expectedType, innerContext)

                            branchTypes.add(branchType)
                        }
                    }
                }

                getMostGeneralType(branchTypes)
                    ?: throw TypeError(
                        "Type ${PrettyPrinter.print(branchTypes.elementAt(1))} does not match" +
                                "Type ${PrettyPrinter.print(branchTypes.elementAt(0))}"
                    )
            }

            else -> null
        }
    }

    private fun extractPatternVar(pattern: Pattern, curType: Type?): Pair<String, Type?> = when (curType) {
        is TypeSum -> when (pattern) {
            is PatternInl -> extractPatternVar(pattern.pattern_, curType.type_1)
            is PatternInr -> extractPatternVar(pattern.pattern_, curType.type_2)
            is PatternVar -> Pair(pattern.stellaident_, curType)
            // TODO: Other matchable types could be added here
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


    private fun typeCheckInl(expr: Inl, expectedType: Type?, context: Context): Type? {
        if (expectedType == null) {
            return TypeSum(typeCheckExpression(expr.expr_, null, context), null)
        }

        val innerExprType = typeCheckExpression(expr.expr_, null, context)

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

    private fun typeCheckInr(expr: Inr, expectedType: Type?, context: Context): Type? {
        if (expectedType == null) {
            return TypeSum(null, typeCheckExpression(expr.expr_, null, context))
        }

        val innerExprType = typeCheckExpression(expr.expr_, null, context)

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

    private fun typeCheckBool(expectedType: Type?): Type {

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

    private fun typeCheckInt(expectedType: Type?): Type {
        if (expectedType == null)
            return TypeNat()

        // Throw error if number is not 0 or return type is not Nat
        if (expectedType !is TypeNat)
            throw TypeError(
                "Expected type ${PrettyPrinter.print(expectedType)}\n" +
                        "Instead found type ${PrettyPrinter.print(TypeNat())}"
            )

        return TypeNat()
    }

    private fun typeCheckUnit(expectedType: Type?): Type {
        if (expectedType == null)
            return TypeUnit()

        if (expectedType !is TypeUnit)
            throw TypeError("Expected type ${PrettyPrinter.print(expectedType)}\n")

        return TypeUnit()
    }

    private fun typeCheckNatFunction(expr: Expr, expectedType: Type?, context: Context): Type? {
        if (expectedType == null)
            return typeCheckExpression(expr, TypeNat(), context)

        when (expectedType) {
            !is TypeNat -> throw TypeError(
                "Expected type ${PrettyPrinter.print(expectedType)}\n" +
                        "Instead found argument of type Nat"
            )

        }

        return typeCheckExpression(expr, TypeNat(), context)
    }

    private fun typeCheckSucc(succExpr: Succ, expectedType: Type?, context: Context): Type? {
        return typeCheckNatFunction(succExpr.expr_, expectedType, context)
    }

    private fun typeCheckPred(predExpr: Pred, expectedType: Type?, context: Context): Type? {
        return typeCheckNatFunction(predExpr.expr_, expectedType, context)
    }

    private fun typeCheckIsZero(isZeroExpr: IsZero, expectedType: Type?, context: Context): Type? {

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

        return typeCheckExpression(isZeroContent, TypeNat(), context)
    }

    private fun typeCheckIf(ifExpr: If, expectedType: Type?, context: Context): Type {
        val condition = ifExpr.expr_1
        val firstBranch = ifExpr.expr_2
        val secondBranch = ifExpr.expr_3

        // Throw error if condition is not Bool
        typeCheckExpression(condition, TypeBool(), context)

        // Throw error if any of the 2 branches do not match the return type of the entire construct
        val firstBranchType = typeCheckExpression(firstBranch, expectedType, context)
        val secondBranchType = typeCheckExpression(secondBranch, expectedType, context)

        // Throw error if inferred types of the 2 branches do not match

        return getMostGeneralType(mutableListOf(firstBranchType, secondBranchType))
            ?: throw TypeError(
                "Branches of If statement must be of the same type.\n" +
                        "Found ${PrettyPrinter.print(firstBranchType)} and ${PrettyPrinter.print(secondBranchType)}"
            )
    }

    private fun typeCheckTypeAbstraction(
        typeAbstraction: TypeAbstraction,
        outerContext: Context
    ): Type {
        val genericTypes = typeAbstraction.liststellaident_
        val innerGenerics = mutableListOf<String>()
        for (generic in genericTypes)
            innerGenerics.add(generic)

        val innerContext = Context(outerContext)
        innerContext.appendTypes(innerGenerics)

        val exprType = typeCheckExpression(typeAbstraction.expr_, null, innerContext)

        // Wrap inner type with Forall
        return TypeForAll(genericTypes, exprType)
    }

    private fun typeCheckAbstraction(abstraction: Abstraction, expectedType: Type?, outerContext: Context): Type {
        val innerVariableContext = mutableMapOf<String, Type>()

        // Creating local scope
        for (paramDecl in abstraction.listparamdecl_) {
            innerVariableContext += parseParamDecl(paramDecl, outerContext)
        }

        // Adding previous scope to new scope
        // Shadowing occurs naturally here as in the old values get overwritten
        val innerContext = Context(outerContext)
        innerContext.appendVariables(innerVariableContext)

        val innerExpr = abstraction.expr_
        val firstParam = abstraction.listparamdecl_[0] as AParamDecl

        // Returning inferred type of the Abstraction in case expectedType is null
        if (expectedType == null) {
            val returnType = typeCheckExpression(innerExpr, null, innerContext)
            return constructTypeFun(firstParam.type_, returnType)
        }

        val actualReturnType: Type?

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

    // Typechecks the first parameter of an application given it's expected and actual types
    private fun typeCheckFirstParam(firstParamType: Type?, expectedType: Type?) {
        if (!compareWithSubtyping(firstParamType, expectedType)) {
            throw TypeError(
                "Type ${PrettyPrinter.print(firstParamType)}\n" +
                        "does not match declared type ${PrettyPrinter.print(expectedType)}"
            )
        }
    }

    // Given ListMatchCase of a match expression verifies that the list contains
    // at least one Inr and at least one Inl cases
    private fun checkInrInl(cases: ListMatchCase): Boolean {
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
    private fun accessRecord(dotRecord: DotRecord, fieldAccessed: String, recordType: TypeRecord): Type? {

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

    // Given a ListPatternBinding, parses it into a map and returns the result
    private fun parseListPatternBinding(
        listPatternBinding: ListPatternBinding,
        context: Context
    ): MutableMap<String, Type> {
        val mapPatternBinding = mutableMapOf<String, Type>()

        for (patternBinding in listPatternBinding)
            when (patternBinding) {
                is APatternBinding -> {
                    when (val pattern = patternBinding.pattern_) {
                        is PatternVar -> mapPatternBinding[pattern.stellaident_] =
                            typeCheckExpression(patternBinding.expr_, null, context)!!
                    }
                }
            }

        return mapPatternBinding
    }

    // Constructs a TypeFun given the type of its argument and its return type
    private fun constructTypeFun(argType: Type?, returnType: Type?): TypeFun {
        val argListType = ListType()
        argListType.add(argType)

        return TypeFun(argListType, returnType)
    }

    // Constructs a TypeTuple given its list of expressions and the current context
    private fun constructTypeTuple(tupleExpressions: ListExpr, context: Context): TypeTuple {
        val exprListType = ListType()

        for (expr in tupleExpressions) {
            exprListType.add(typeCheckExpression(expr, null, context))
        }

        return TypeTuple(exprListType)
    }

    // Constructs a TypeRecord given its list of bindings and the current context
    private fun constructTypeRecord(recordListBinding: ListBinding, context: Context): TypeRecord {
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

}

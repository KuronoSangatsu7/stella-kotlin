// File generated by the BNF Converter (bnfc 2.9.4.1).

package org.syntax.stella;

/** Abstract Visitor */

public class AbstractVisitor<R,A> implements AllVisitor<R,A> {
    /* Program */
    public R visit(org.syntax.stella.Absyn.AProgram p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.Program p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* LanguageDecl */
    public R visit(org.syntax.stella.Absyn.LanguageCore p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.LanguageDecl p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Extension */
    public R visit(org.syntax.stella.Absyn.AnExtension p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.Extension p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Decl */
    public R visit(org.syntax.stella.Absyn.DeclFun p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.DeclTypeAlias p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.DeclExceptionType p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.DeclExceptionVariant p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.Decl p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* LocalDecl */
    public R visit(org.syntax.stella.Absyn.ALocalDecl p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.LocalDecl p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Annotation */
    public R visit(org.syntax.stella.Absyn.InlineAnnotation p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.Annotation p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* ParamDecl */
    public R visit(org.syntax.stella.Absyn.AParamDecl p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.ParamDecl p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* ReturnType */
    public R visit(org.syntax.stella.Absyn.NoReturnType p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.SomeReturnType p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.ReturnType p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* ThrowType */
    public R visit(org.syntax.stella.Absyn.NoThrowType p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.SomeThrowType p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.ThrowType p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Type */
    public R visit(org.syntax.stella.Absyn.TypeFun p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.TypeRec p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.TypeSum p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.TypeTuple p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.TypeRecord p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.TypeVariant p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.TypeList p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.TypeBool p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.TypeNat p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.TypeUnit p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.TypeTop p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.TypeBottom p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.TypeRef p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.TypeVar p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.Type p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* MatchCase */
    public R visit(org.syntax.stella.Absyn.AMatchCase p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.MatchCase p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* OptionalTyping */
    public R visit(org.syntax.stella.Absyn.NoTyping p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.SomeTyping p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.OptionalTyping p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* PatternData */
    public R visit(org.syntax.stella.Absyn.NoPatternData p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.SomePatternData p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.PatternData p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* ExprData */
    public R visit(org.syntax.stella.Absyn.NoExprData p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.SomeExprData p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.ExprData p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Pattern */
    public R visit(org.syntax.stella.Absyn.PatternVariant p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.PatternInl p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.PatternInr p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.PatternTuple p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.PatternRecord p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.PatternList p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.PatternCons p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.PatternFalse p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.PatternTrue p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.PatternUnit p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.PatternInt p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.PatternSucc p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.PatternVar p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.Pattern p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* LabelledPattern */
    public R visit(org.syntax.stella.Absyn.ALabelledPattern p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.LabelledPattern p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Binding */
    public R visit(org.syntax.stella.Absyn.ABinding p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.Binding p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Expr */
    public R visit(org.syntax.stella.Absyn.Sequence p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Let p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.LetRec p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Assign p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.If p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.LessThan p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.LessThanOrEqual p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.GreaterThan p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.GreaterThanOrEqual p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Equal p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.NotEqual p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.TypeAsc p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.TypeCast p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Abstraction p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Variant p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Match p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.List p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Add p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Subtract p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.LogicOr p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Multiply p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Divide p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.LogicAnd p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Ref p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Deref p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Application p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.DotRecord p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.DotTuple p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Tuple p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Record p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.ConsList p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Head p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.IsEmpty p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Tail p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Panic p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Throw p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.TryCatch p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.TryWith p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Inl p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Inr p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Succ p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.LogicNot p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Pred p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.IsZero p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Fix p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.NatRec p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Fold p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Unfold p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.ConstTrue p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.ConstFalse p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.ConstUnit p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.ConstInt p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.ConstMemory p, A arg) { return visitDefault(p, arg); }
    public R visit(org.syntax.stella.Absyn.Var p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.Expr p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* PatternBinding */
    public R visit(org.syntax.stella.Absyn.APatternBinding p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.PatternBinding p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* VariantFieldType */
    public R visit(org.syntax.stella.Absyn.AVariantFieldType p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.VariantFieldType p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* RecordFieldType */
    public R visit(org.syntax.stella.Absyn.ARecordFieldType p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.RecordFieldType p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }
    /* Typing */
    public R visit(org.syntax.stella.Absyn.ATyping p, A arg) { return visitDefault(p, arg); }
    public R visitDefault(org.syntax.stella.Absyn.Typing p, A arg) {
      throw new IllegalArgumentException(this.getClass().getName() + ": " + p);
    }

}

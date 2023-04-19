// File generated by the BNF Converter (bnfc 2.9.4.1).

package org.syntax.stella.Absyn;

public class Match  extends Expr {
  public final Expr expr_;
  public final ListMatchCase listmatchcase_;
  public int line_num, col_num, offset;
  public Match(Expr p1, ListMatchCase p2) { expr_ = p1; listmatchcase_ = p2; }

  public <R,A> R accept(org.syntax.stella.Absyn.Expr.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof org.syntax.stella.Absyn.Match) {
      org.syntax.stella.Absyn.Match x = (org.syntax.stella.Absyn.Match)o;
      return this.expr_.equals(x.expr_) && this.listmatchcase_.equals(x.listmatchcase_);
    }
    return false;
  }

  public int hashCode() {
    return 37*(this.expr_.hashCode())+this.listmatchcase_.hashCode();
  }


}

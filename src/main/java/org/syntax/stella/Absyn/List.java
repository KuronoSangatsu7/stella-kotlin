// File generated by the BNF Converter (bnfc 2.9.4.1).

package org.syntax.stella.Absyn;

public class List  extends Expr {
  public final ListExpr listexpr_;
  public int line_num, col_num, offset;
  public List(ListExpr p1) { listexpr_ = p1; }

  public <R,A> R accept(org.syntax.stella.Absyn.Expr.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof org.syntax.stella.Absyn.List) {
      org.syntax.stella.Absyn.List x = (org.syntax.stella.Absyn.List)o;
      return this.listexpr_.equals(x.listexpr_);
    }
    return false;
  }

  public int hashCode() {
    return this.listexpr_.hashCode();
  }


}

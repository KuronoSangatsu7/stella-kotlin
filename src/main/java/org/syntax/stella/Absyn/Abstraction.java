// File generated by the BNF Converter (bnfc 2.9.4.1).

package org.syntax.stella.Absyn;

public class Abstraction  extends Expr {
  public final ListParamDecl listparamdecl_;
  public final Expr expr_;
  public int line_num, col_num, offset;
  public Abstraction(ListParamDecl p1, Expr p2) { listparamdecl_ = p1; expr_ = p2; }

  public <R,A> R accept(Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(Object o) {
    if (this == o) return true;
    if (o instanceof Abstraction) {
      Abstraction x = (Abstraction)o;
      return this.listparamdecl_.equals(x.listparamdecl_) && this.expr_.equals(x.expr_);
    }
    return false;
  }

  public int hashCode() {
    return 37*(this.listparamdecl_.hashCode())+this.expr_.hashCode();
  }


}

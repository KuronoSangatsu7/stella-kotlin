// File generated by the BNF Converter (bnfc 2.9.4.1).

package org.syntax.stella.Absyn;

public class ConstMemory  extends Expr {
  public final String memoryaddress_;
  public int line_num, col_num, offset;
  public ConstMemory(String p1) { memoryaddress_ = p1; }

  public <R,A> R accept(org.syntax.stella.Absyn.Expr.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof org.syntax.stella.Absyn.ConstMemory) {
      org.syntax.stella.Absyn.ConstMemory x = (org.syntax.stella.Absyn.ConstMemory)o;
      return this.memoryaddress_.equals(x.memoryaddress_);
    }
    return false;
  }

  public int hashCode() {
    return this.memoryaddress_.hashCode();
  }


}

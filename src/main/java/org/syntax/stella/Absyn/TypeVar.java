// File generated by the BNF Converter (bnfc 2.9.4.1).

package org.syntax.stella.Absyn;

public class TypeVar  extends Type {
  public final String stellaident_;
  public int line_num, col_num, offset;
  public TypeVar(String p1) { stellaident_ = p1; }

  public <R,A> R accept(org.syntax.stella.Absyn.Type.Visitor<R,A> v, A arg) { return v.visit(this, arg); }

  public boolean equals(java.lang.Object o) {
    if (this == o) return true;
    if (o instanceof org.syntax.stella.Absyn.TypeVar) {
      org.syntax.stella.Absyn.TypeVar x = (org.syntax.stella.Absyn.TypeVar)o;
      return this.stellaident_.equals(x.stellaident_);
    }
    return false;
  }

  public int hashCode() {
    return this.stellaident_.hashCode();
  }


}

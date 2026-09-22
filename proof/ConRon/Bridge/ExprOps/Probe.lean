import ConRon.Bridge.Specs
set_option autoImplicit false
open ConLeche ConRon.Arena ConRon.Bridge Std.Do
#check @List.getElem?_reverse
#check @List.reverse_append
#check @List.take_append_drop
#check @List.length_reverse
#check @List.length_drop
#check @List.getElem?_append_left
#check @eidxCopyUpto.induct
#check @Expr.bvarBound
#check @Expr.instantiateList
#check @Expr.instPisAtLift
#check @Expr.lowerBVars_of_bvarBound_le
#check @Expr.instantiate1Lift_of_bvarBound_le
#check @Expr.bvarBRaw_exact
#check @ConRon.Arena.lastEidx
#check @Frontend.denoteEList
example (l : List Nat) (i : Nat) : l.reverse[i]? = l[l.length - 1 - i]? := by
  exact?

import ConRon.Bridge.Grouping.Core3

namespace ConRon.Bridge.Grouping

set_option mvcgen.warning false

open ConRon.Arena Std.Do

@[spec] theorem inferLamsOut_keeps (k : EStore) (p : Pins) {mode d stk n cur prevPw} :
    ⦃fun s => ⌜Inv k p s⌝⦄ inferLamsOut mode d stk n cur prevPw ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  fun_induction inferLamsOut mode d stk n cur prevPw
  all_goals keeps_step

#keeps inferLamsLeafCheck inferLamsLeaf
#keeps_ind inferLams 4

@[spec] theorem inferPisOut_keeps (k : EStore) (p : Pins) {mode stk n v pv} :
    ⦃fun s => ⌜Inv k p s⌝⦄ inferPisOut mode stk n v pv ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  fun_induction inferPisOut mode stk n v pv
  all_goals keeps_step

#keeps inferPisLeaf
#keeps_ind inferPis 4
#keeps inferLam inferForall

@[spec] theorem inferSpine_keeps (k : EStore) (p : Pins) {mode r fe depth ty acc args i}
    (hr : FnsKeep r) :
    ⦃fun s => ⌜Inv k p s⌝⦄ inferSpine mode r fe depth ty acc args i ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  fun_induction inferSpine mode r fe depth ty acc args i
  all_goals keeps_step

#keeps inferApp

@[spec] theorem inferSpineIO_keeps (k : EStore) (p : Pins) {mode r fe depth ty acc args i}
    (hr : FnsKeep r) :
    ⦃fun s => ⌜Inv k p s⌝⦄ inferSpineIO mode r fe depth ty acc args i ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  fun_induction inferSpineIO mode r fe depth ty acc args i
  all_goals keeps_step

#keeps inferAppIOAt inferBody inferBodyIO

end ConRon.Bridge.Grouping

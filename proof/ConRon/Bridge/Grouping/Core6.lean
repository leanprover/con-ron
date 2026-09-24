import ConRon.Bridge.Grouping.Defeq

namespace ConRon.Bridge.Grouping

set_option mvcgen.warning false

open ConRon.Arena Std.Do

#erase_foreign_specs

#keeps isPropType annotPwPi annotPwLam

@[scoped spec] theorem annotateBindersOut_keeps (k : EStore) (p : Pins) {isLam d pw? stk n cur} :
    ⦃fun s => ⌜Inv k p s⌝⦄ annotateBindersOut isLam d pw? stk n cur ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  induction n generalizing pw? cur with
  | zero => rw [annotateBindersOut]; keeps_step
  | succ n ih => rw [annotateBindersOut]; simp only [Nat.add_sub_cancel]; keeps_step

#keeps annotatePisLeaf
#keeps_ind annotatePis 3
#keeps annotateLamsLeaf
#keeps_ind annotateLams 3
#keeps annotateBinder annotateBody whnfCoreSet whnfSet inferSet inferIOSet annotSet defeqSet

/-- **The knot keeps the invariant**, at every fuel. -/
theorem coreKnot_keeps (mode : ConLeche.CheckMode) (fe : IFEnv) :
    ∀ n, FnsKeep (coreKnot mode fe id n) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp only [coreKnot] <;> keeps_step
  | succ n ih =>
    have hio := ih.ioView
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp only [coreKnot, id] <;> keeps_step

@[scoped spec] theorem inferTypeCore_keeps (k : EStore) (p : Pins) {mode fe fuel depth e} :
    ⦃fun s => ⌜Inv k p s⌝⦄ inferTypeCore mode fe fuel depth e ⦃⇓? _r s => ⌜Inv k p s⌝⦄ :=
  (coreKnot_keeps mode fe fuel).infer k p _ _

@[scoped spec] theorem isDefEqCore_keeps (k : EStore) (p : Pins) {mode fe fuel depth a b} :
    ⦃fun s => ⌜Inv k p s⌝⦄ isDefEqCore mode fe fuel depth a b ⦃⇓? _r s => ⌜Inv k p s⌝⦄ :=
  (coreKnot_keeps mode fe fuel).defeq k p _ _ _

@[scoped spec] theorem annotateCore_keeps (k : EStore) (p : Pins) {mode fe fuel depth e} :
    ⦃fun s => ⌜Inv k p s⌝⦄ annotateCore mode fe fuel depth e ⦃⇓? _r s => ⌜Inv k p s⌝⦄ :=
  (coreKnot_keeps mode fe fuel).annotate k p _ _

@[scoped spec] theorem ensureSortCore_keeps (k : EStore) (p : Pins) {mode fe fuel depth e} :
    ⦃fun s => ⌜Inv k p s⌝⦄ ensureSortCore mode fe fuel depth e ⦃⇓? _r s => ⌜Inv k p s⌝⦄ :=
  ensureSort_keeps k p (coreKnot_keeps mode fe fuel)

end ConRon.Bridge.Grouping

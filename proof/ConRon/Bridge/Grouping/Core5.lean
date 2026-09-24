import ConRon.Bridge.Grouping.Core4

namespace ConRon.Bridge.Grouping

set_option mvcgen.warning false

open ConRon.Arena Std.Do

#erase_foreign_specs

#keeps boolTrueShortcut defeqSpine defeqNoFvars defeqPeelDone defeqPeelLeaf
/-- con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep — one level of
`defeqPeel` over a continuation, verbatim (`Bridge/Core/Arms/DefeqPeel.lean`'s
`peelStep`): the structural recursion's equation lemmas time out, so the two
unfoldings are stated by `delta` and `rfl`. -/
def peelStepG (mode : ConLeche.CheckMode) (r : CoreFnsA) (d : Nat) (peel : Nat)
    (cont : EIdx → EIdx → Nat → Array EIdx → Bool → Bool → AM Bool)
    (a b : EIdx) (k : Nat) (fvs : Array EIdx) (mism mismLam : Bool) :
    AM Bool := do
  let ta := a.tag
  if a == b then defeqPeelDone mism mismLam
  else if peel = 0 || ta != b.tag || !(ETag.isBind ta) then
    defeqPeelLeaf r d a b k fvs mism mismLam
  else
    match ← viewBindI a with
    | none => failDanglingE
    | some (da, ba, ma) =>
      match ← viewBindI b with
      | none => failDanglingE
      | some (db, bb, mb) => do
        let sameDom := da == db
        let t1 ← instantiateListFast coreWalkFuel da fvs 0
        let t2 ← if sameDom then pure t1
                 else instantiateListFast coreWalkFuel db fvs 0
        let dq ← if sameDom then pure true else r.defeq (d + k) t1 t2
        if !dq then pure false
        else do
          let fv ← internFVarE (d + k) t2
          let mm := mode.verifiedChecks && !(ma == mb)
          let m2 := mism || mm
          let ml2 := if mm then ta == ETag.lam else mismLam
          cont ba bb (k + 1) (fvs.push fv) m2 ml2

theorem defeqPeel_succ_eqG (mode : ConLeche.CheckMode) (r : CoreFnsA) (d p : Nat)
    (a b : EIdx) (k : Nat) (fvs : Array EIdx) (mism ml : Bool) :
    defeqPeel mode r d (p + 1) a b k fvs mism ml =
      peelStepG mode r d (p + 1) (defeqPeel mode r d p) a b k fvs mism ml := by
  delta defeqPeel peelStepG
  exact rfl

theorem defeqPeel_zero_eqG (mode : ConLeche.CheckMode) (r : CoreFnsA) (d : Nat)
    (a b : EIdx) (k : Nat) (fvs : Array EIdx) (mism ml : Bool) :
    defeqPeel mode r d 0 a b k fvs mism ml =
      peelStepG mode r d 0 (defeqPeelLeaf r d) a b k fvs mism ml := by
  delta defeqPeel peelStepG
  exact rfl

@[scoped spec] theorem peelStepG_keeps (k : EStore) (p : Pins) {mode r d peel}
    {cont : EIdx → EIdx → Nat → Array EIdx → Bool → Bool → AM Bool}
    {a b kk fvs mism mismLam} (hr : FnsKeep r)
    (hc : ∀ a b kk fvs mism mismLam,
      ⦃fun s => ⌜Inv k p s⌝⦄ cont a b kk fvs mism mismLam ⦃⇓? _r s => ⌜Inv k p s⌝⦄) :
    ⦃fun s => ⌜Inv k p s⌝⦄ peelStepG mode r d peel cont a b kk fvs mism mismLam
    ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  keeps_step peelStepG

@[scoped spec] theorem defeqPeel_keeps (k : EStore) (p : Pins) {mode r d} (peel : Nat)
    {a b kk fvs mism mismLam} (hr : FnsKeep r) :
    ⦃fun s => ⌜Inv k p s⌝⦄ defeqPeel mode r d peel a b kk fvs mism mismLam
    ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  induction peel generalizing a b kk fvs mism mismLam with
  | zero =>
    rw [defeqPeel_zero_eqG]
    exact peelStepG_keeps k p hr (fun _ _ _ _ _ _ => defeqPeelLeaf_keeps k p hr)
  | succ n ih =>
    rw [defeqPeel_succ_eqG]
    exact peelStepG_keeps k p hr (fun _ _ _ _ _ _ => ih)

#keeps defeqBinders

end ConRon.Bridge.Grouping

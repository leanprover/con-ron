import ConRon.Bridge.Grouping.Core2

namespace ConRon.Bridge.Grouping

set_option mvcgen.warning false

open ConRon.Arena Std.Do

#erase_foreign_specs

theorem whnfApp_betaPeel_keeps (k : EStore) (p : Pins) {mode : ConLeche.CheckMode} {r : CoreFnsA}
    {fe : IFEnv} {depth : Nat} (args nodes : Array EIdx) (hr : FnsKeep r) :
    (∀ (v hd : EIdx) (vargs : Array EIdx) (same : Bool) (i : Nat), ⦃fun s => ⌜Inv k p s⌝⦄
        whnfApp mode r fe depth v hd vargs same args nodes i ⦃⇓? _r s => ⌜Inv k p s⌝⦄) ∧
    (∀ (t : EIdx) (acc : Array EIdx) (i : Nat), ⦃fun s => ⌜Inv k p s⌝⦄
        betaPeel mode r fe depth t acc args nodes i ⦃⇓? _r s => ⌜Inv k p s⌝⦄) := by
  refine whnfApp.mutual_induct args nodes
    (motive1 := fun (v hd : EIdx) (vargs : Array EIdx) (same : Bool) (i : Nat) => ⦃fun s => ⌜Inv k p s⌝⦄
        whnfApp mode r fe depth v hd vargs same args nodes i ⦃⇓? _r s => ⌜Inv k p s⌝⦄)
    (motive2 := fun (t : EIdx) (acc : Array EIdx) (i : Nat) => ⦃fun s => ⌜Inv k p s⌝⦄
        betaPeel mode r fe depth t acc args nodes i ⦃⇓? _r s => ⌜Inv k p s⌝⦄)
    ?_ ?_ ?_ ?_ ?_ ?_
  all_goals (intros; first | rw [whnfApp] | rw [betaPeel]) <;> keeps_step

@[scoped spec] theorem whnfApp_keeps (k : EStore) (p : Pins) {mode r fe depth v hd vargs same args nodes i}
    (hr : FnsKeep r) : ⦃fun s => ⌜Inv k p s⌝⦄
        whnfApp mode r fe depth v hd vargs same args nodes i ⦃⇓? _r s => ⌜Inv k p s⌝⦄ :=
  (whnfApp_betaPeel_keeps k p args nodes hr).1 _ _ _ _ _

@[scoped spec] theorem betaPeel_keeps (k : EStore) (p : Pins) {mode r fe depth t acc args nodes i}
    (hr : FnsKeep r) : ⦃fun s => ⌜Inv k p s⌝⦄
        betaPeel mode r fe depth t acc args nodes i ⦃⇓? _r s => ⌜Inv k p s⌝⦄ :=
  (whnfApp_betaPeel_keeps k p args nodes hr).2 _ _ _

#keeps IProjEntry.typeAt projCert projCertAt whnfCoreBody

@[scoped spec] theorem whnfStep_keeps (k : EStore) (p : Pins) {r : CoreFnsA} {fe depth}
    {kk : EIdx → AM EIdx} {e : EIdx} (hr : FnsKeep r)
    (hk : ∀ e, ⦃fun s => ⌜Inv k p s⌝⦄ kk e ⦃⇓? _r s => ⌜Inv k p s⌝⦄) :
    ⦃fun s => ⌜Inv k p s⌝⦄ whnfStep r fe depth kk e ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  keeps_step whnfStep

@[scoped spec] theorem whnfLoop_keeps (k : EStore) (p : Pins) {r : CoreFnsA} {fe depth}
    (n : Nat) (e : EIdx) (hr : FnsKeep r) :
    ⦃fun s => ⌜Inv k p s⌝⦄ whnfLoop r fe depth n e ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  induction n generalizing e with
  | zero => keeps_step whnfLoop
  | succ n ih => exact whnfStep_keeps k p hr ih

#keeps whnfBody ensureSort inferLamResult

end ConRon.Bridge.Grouping

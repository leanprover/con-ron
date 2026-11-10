/-
# `ConRon.Bridge.Core.Walks.Eta` — the structure-η certificate's sub-walks

`structEtaCertWith` (`Walks/Stuck.lean`) and the η rescue of `majorToCtor`
read the fabricated projections; the walk is here, an equation with
con-leche's function of the same name:

| walk | twin | con-leche |
|---|---|---|
| `etaProjs_spec` | `Arena/Core.lean` (`projNodesGo`) | `Kernel/CoreDefs.lean:712-716` |

con-leche writes the projections as `(List.range nF).map`; the twin's counted
recursion (DESIGN §3.4) is proved against a named walk with one equation per
step (`projsFrom`), which is con-leche's at slot 0 (`etaProjs_eq`).  Every proof is `sym only
[bridge_grind, …] => vcgen […] <;> finish`, the recursion's induction
hypothesis in the `vcgen` list.
-/
module

import ConRon.Bridge.Core.Walks.Nat
import ConRon.Bridge.Core.Walks.Proj
public import ConLeche.Verify.Shift
import ConRon.Bridge.Specs
import ConRon.Bridge.GrindAttr
public import ConRon.Bridge.StateOK
public import ConRon.Arena.Core

public section

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {eager : Bool} {env : Env} {fe : IFEnv}

/-! ## 1. Small facts about the denotations -/

/-- con-leche: none — two denoting name-handle lists are equal exactly when
their denotations are (the store interns names injectively). -/
theorem denoteNList_eq_iff {st : EStore} (hwf : StoreWF st)
    {as bs : List NIdx} {xs ys : List ConLeche.Name}
    (ha : Frontend.denoteNList st.ns as = some xs)
    (hb : Frontend.denoteNList st.ns bs = some ys) : as = bs ↔ xs = ys := by
  constructor
  · rintro rfl; exact Option.some.inj (ha.symm.trans hb)
  · rintro rfl; exact denoteNList_inj hwf as bs xs ha hb

/-! ## The projection-table lookup -/

/-! ## 2. The fabricated projections -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:730-736 etaProjs — the
projections `j, j+1, …` for `n` slots, one equation per step. -/
def projsFrom (Tn : ConLeche.Name) (y : Expr) : Nat → Nat → List Expr
  | 0, _ => []
  | n + 1, j => .proj Tn j y :: projsFrom Tn y n (j + 1)
attribute [bridge_grind =] projsFrom

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:723-724 etaProjs — the function
is the projections from slot 0. -/
@[bridge_grind =] theorem etaProjs_eq (Tn : ConLeche.Name) (y : Expr) (nF : Nat) :
    ConLeche.etaProjs Tn y nF = projsFrom Tn y nF 0 := by
  rw [ConLeche.etaProjs, List.range_eq_range']
  generalize 0 = j
  induction nF generalizing j with
  | zero => rfl
  | succ n ih => rw [List.range'_succ, List.map_cons, ih]; rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:730-736 etaProjs — **THEOREM 1
for the `.proj` half**, the counted recursion `projNodesGo`. -/
theorem projNodesGo_specA (T : NIdx) (b : EIdx) (Tn : ConLeche.Name) (y : Expr) :
    ∀ (n j : Nat) (s₀ : AState), CheckOK eager env fe s₀ →
      denoteN s₀.store.ns T = some Tn → denoteE s₀.store b = some y →
      ⦃fun s => s = s₀⦄ ConRon.Arena.projNodesGo T b n j
      ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          Frontend.denoteEList s'.store r = some (projsFrom Tn y n j); ⊤⦄ := by
  intro n
  induction n with
  | zero =>
    intro j s₀ hok _ _
    sym only [bridge_grind] => vcgen [ConRon.Arena.projNodesGo] <;> finish
  | succ n ih =>
    intro j s₀ hok hT hb
    sym only [bridge_grind] =>
      vcgen [ConRon.Arena.projNodesGo, internE_specC (eager := eager) (env := env) (fe := fe),
        ih] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:723-724 etaProjs — **THEOREM 1
for `etaProjs`**: the handles the twin fabricates denote con-leche's list. -/
theorem etaProjs_spec (s₀ : AState) (T : NIdx) (b : EIdx) (nF : Nat)
    (Tn : ConLeche.Name) (y : Expr)
    (hok : CheckOK eager env fe s₀) (hT : denoteN s₀.store.ns T = some Tn)
    (hb : denoteE s₀.store b = some y) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.etaProjs T b nF
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Frontend.denoteEList s'.store r =
          some (ConLeche.etaProjs Tn y nF); ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.etaProjs,
      projNodesGo_specA (eager := eager) (env := env) (fe := fe) (Tn := Tn) (y := y)] <;> finish

/-- con-leche: none — the fabricated projections are well-scoped wherever
the stuck side is. -/
theorem etaProjs_WScoped {d : Nat} {Tn : ConLeche.Name} {y : Expr} {nF : Nat}
    (hwy : Expr.WScoped d y) :
    ∀ p ∈ ConLeche.etaProjs Tn y nF, Expr.WScoped d p := by
  intro p hp
  unfold ConLeche.etaProjs at hp
  simp only [List.mem_map] at hp
  obtain ⟨k, _, rfl⟩ := hp
  simp only [Expr.WScoped]; exact hwy

/-! ## 3. The axiom census -/

section Census

#print axioms denoteNList_inj
#print axioms projNodesGo_specA
#print axioms etaProjs_spec
#print axioms etaProjs_WScoped

end Census

end ConRon.Bridge.Core

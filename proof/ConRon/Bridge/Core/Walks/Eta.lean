/-
# `ConRon.Bridge.Core.Walks.Eta` — the structure-η certificate's sub-walks

`structEtaCertWith` (`Walks/Stuck.lean`) and the η rescue of `majorToCtor`
read two walks; they are here, each an equation with con-leche's function of
the same name:

| walk | twin | con-leche |
|---|---|---|
| `towerSlotsAll_spec` | `Arena/Core.lean` (`towerSlotsAllGo`) | `Kernel/CoreDefs.lean` |
| `etaProjs_spec` | `Arena/Core.lean` (`projNodesGo`) | `Kernel/CoreDefs.lean:723` |

con-leche writes the slot walk as `(List.range nF).all`/`.map`; the twin's
counted recursions (DESIGN §3.4) are proved against named walks with one
equation per step (`towerSlotsFrom`, `projsFrom`), which are con-leche's at
slot 0 (`towerSlotsAll_eq`, `etaProjs_eq`).  Every proof is `sym only
[bridge_grind, …] => vcgen […] <;> finish`, the recursion's induction
hypothesis in the `vcgen` list.
-/
import ConRon.Bridge.Core.Walks.StrCtor
import ConRon.Bridge.Core.Walks.StrLit

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

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

/-- con-leche: none — an optional projection-table entry is found exactly
when its denotation is. -/
theorem isSome_of_denoteProjEntryO {st : EStore} {o : Option IProjEntry}
    {o' : Option ProjEntry} (h : denoteProjEntryO st o = some o') : o.isSome = o'.isSome := by
  cases o with
  | none => simp only [denoteProjEntryO, Option.some.injEq] at h; subst h; rfl
  | some e =>
    simp only [denoteProjEntryO, Option.map_eq_some_iff] at h
    obtain ⟨p, _, rfl⟩ := h; rfl
grind_pattern [bridge_grind] isSome_of_denoteProjEntryO => denoteProjEntryO st o, some o' where
  guard denoteProjEntryO st o = some o'

/-! ## 2. The slot walk -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:713-714 towerSlotsAll — the
slots `j, j+1, …` for `n` slots, one equation per step. -/
def towerSlotsFrom (env : Env) (Tn : ConLeche.Name) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, j => (env.findProj? Tn j).isSome && towerSlotsFrom env Tn n (j + 1)
attribute [bridge_grind =] towerSlotsFrom

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:713-714 towerSlotsAll — the
function is the slot walk from slot 0. -/
@[bridge_grind =] theorem towerSlotsAll_eq (Tn : ConLeche.Name) (nF : Nat) :
    ConLeche.towerSlotsAll env Tn nF = towerSlotsFrom env Tn nF 0 := by
  rw [ConLeche.towerSlotsAll, List.range_eq_range']
  generalize 0 = j
  induction nF generalizing j with
  | zero => rfl
  | succ n ih => rw [List.range'_succ, List.all_cons, ih]; rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:713-714 towerSlotsAll — **THEOREM
1 for the counted recursion `towerSlotsAllGo`**, at its running index: a slot
is a table entry in the arena exactly where it is in the environment
(`findProjAt`). -/
theorem towerSlotsAllGo_eq {s : AState} (T : NIdx) (Tn : ConLeche.Name)
    (hok : CheckOK mode env fe s) (hT : denoteN s.store.ns T = some Tn) :
    ∀ (n j : Nat), ConRon.Arena.towerSlotsAllGo fe T n j = towerSlotsFrom env Tn n j := by
  intro n
  induction n with
  | zero => intro j; rfl
  | succ n ih =>
    intro j
    have h := findProjAt (i := j) hok hT
    simp only [ConRon.Arena.towerSlotsAllGo, towerSlotsFrom, ← ih (j + 1)]
    cases hp : fe.findProj? T j with
    | none =>
      rw [hp] at h
      simp only [denoteProjEntryO, Option.some.injEq] at h
      rw [← h]; rfl
    | some e =>
      rw [hp] at h
      simp only [denoteProjEntryO, Option.map_eq_some_iff] at h
      obtain ⟨p, -, hpe⟩ := h
      rw [← hpe]; rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:713-714 towerSlotsAll — the slot
walk at a handle's denotation, keyed by the arena's call alone (`IndexAt`'s
shape). -/
def TowerAt (env : Env) (fe : IFEnv) (T : NIdx) (nF : Nat) : Option ConLeche.Name → Prop
  | some Tn => ConRon.Arena.towerSlotsAll fe T nF = towerSlotsFrom env Tn nF 0
  | none => True

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:713-714 towerSlotsAll — **THEOREM
1 for `towerSlotsAll`**: an equation with con-leche's slot walk. -/
theorem towerSlotsAllAt {s : AState} (hok : CheckOK mode env fe s) (T : NIdx) (nF : Nat) :
    TowerAt env fe T nF (denoteN s.store.ns T) := by
  cases hT : denoteN s.store.ns T with
  | none => trivial
  | some Tn => exact towerSlotsAllGo_eq T Tn hok hT nF 0
grind_pattern [bridge_grind] towerSlotsAllAt =>
  CheckOK mode env fe s, ConRon.Arena.towerSlotsAll fe T nF

/-- con-leche: none — `TowerAt` at a denoting handle. -/
theorem TowerAt.some {T : NIdx} {nF : Nat} {Tn : ConLeche.Name}
    (H : TowerAt env fe T nF (some Tn)) :
    ConRon.Arena.towerSlotsAll fe T nF = towerSlotsFrom env Tn nF 0 := H
grind_pattern [bridge_grind] TowerAt.some => TowerAt env fe T nF (some Tn)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:713-714 towerSlotsAll — the same,
with con-leche's function on the right. -/
theorem towerSlotsAll_spec {s : AState} (T : NIdx) (Tn : ConLeche.Name)
    (nF : Nat) (hok : CheckOK mode env fe s)
    (hT : denoteN s.store.ns T = some Tn) :
    ConRon.Arena.towerSlotsAll fe T nF = ConLeche.towerSlotsAll env Tn nF := by
  rw [towerSlotsAll_eq]; exact towerSlotsAllGo_eq T Tn hok hT nF 0

/-! ## 3. The fabricated projections -/

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
    ∀ (n j : Nat) (s₀ : AState), CheckOK mode env fe s₀ →
      denoteN s₀.store.ns T = some Tn → denoteE s₀.store b = some y →
      ⦃fun s => s = s₀⦄ ConRon.Arena.projNodesGo T b n j
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
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
      vcgen [ConRon.Arena.projNodesGo, internE_specC (mode := mode) (env := env) (fe := fe),
        ih] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:723-724 etaProjs — **THEOREM 1
for `etaProjs`**: the handles the twin fabricates denote con-leche's list. -/
theorem etaProjs_spec (s₀ : AState) (T : NIdx) (b : EIdx) (nF : Nat)
    (Tn : ConLeche.Name) (y : Expr)
    (hok : CheckOK mode env fe s₀) (hT : denoteN s₀.store.ns T = some Tn)
    (hb : denoteE s₀.store b = some y) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.etaProjs T b nF
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Frontend.denoteEList s'.store r =
          some (ConLeche.etaProjs Tn y nF); ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.etaProjs,
      projNodesGo_specA (mode := mode) (env := env) (fe := fe) (Tn := Tn) (y := y)] <;> finish

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

/-! ## 4. The axiom census -/

section Census

#print axioms denoteNList_inj
#print axioms towerSlotsAll_spec
#print axioms towerSlotsAllGo_eq
#print axioms towerSlotsAllAt
#print axioms projNodesGo_specA
#print axioms etaProjs_spec
#print axioms etaProjs_WScoped

end Census

end ConRon.Bridge.Core

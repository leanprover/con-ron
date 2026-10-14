/-
# `ConRon.Bridge.Core.Walks.IotaLeaves` — the state-only readers under `iotaRec`

The readers the stuck-major rescue and the ι step consult, each an equation
with con-leche's function.  The walks that call the knot are
`Walks/IotaMajor.lean` and `Walks/Iota.lean`.

Every proof is `sym only [bridge_grind, …] => vcgen [f, callee specs…] <;>
finish`.  What makes them `grind`-shaped: each con-leche function as ONE
equation over tags and projections (`isCtorApp_eq`, `litToCtorIfNat_eq`,
`andRescueSlots_eq` over the named slot walk `andSlotsFrom`), a twin's nested
`match` one constructor deep (`litToCtorIfNat_split`), and the callees with
`∀`-shaped posts restated as named answers (`leafGuard_specA`,
`findProj?_specP`, `IProjEntry.fireOk_specA`).
-/
import ConRon.Bridge.Core.Walks.Stuck
import ConRon.Bridge.Core.Walks.ProjLit
import ConRon.Bridge.ExprOps.Guards
import ConRon.Bridge.ExprOps.Ranges

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## Vocabulary candidates (for Bridge/Grind.lean) -/

/-- con-leche: none — the pin table's `And` slot (`pinNames_eq_*`'s shape). -/
@[bridge_grind =] theorem pinNames_eq_andName : pinNames[PIN_AND]? = some ConLeche.andName :=
  rfl

/-! ## 1. State-only readers -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:46-53 isCtorApp — the reader as
ONE equation over the head's tag, its constant name and the environment's
constructor projection. -/
theorem isCtorApp_eq (x : Expr) :
    ConLeche.isCtorApp env x =
      (exprTag x.getAppFn == ETag.const && cCtor? (env.find? (exprConstName x.getAppFn))) := by
  simp only [ConLeche.isCtorApp]
  cases x.getAppFn <;> rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:46-53 isCtorApp — **THEOREM 1
for `isCtorApp`**: an equation with con-leche's reader. -/
theorem isCtorApp_spec (s₀ : AState) (a : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.isCtorApp fe a
    ⦃fun r s' => s' = s₀ ∧ r = ConLeche.isCtorApp env x; ⊤⦄ := by
  sym only [bridge_grind, isCtorApp_eq] =>
    vcgen [ConRon.Arena.isCtorApp, ExprOps.getAppFn_spec] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:197-200 natLitToConstructor —
**THEOREM 1 for `natLitToConstructor`**: `Nat.zero`, or `Nat.succ` applied to
the predecessor literal. -/
theorem natLitToConstructor_spec (s₀ : AState) (n : Nat)
    (hok : CheckOK mode env fe s₀) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natLitToConstructor n
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteE s'.store r = some (ConLeche.natLitToConstructor n); ⊤⦄ := by
  sym only [bridge_grind, ConLeche.natLitToConstructor, hok.pins] =>
    vcgen [ConRon.Arena.natLitToConstructor, ConRon.Arena.pinNatZero, ConRon.Arena.pinNatSucc,
      pinAt_specE, constE_specA (mode := mode) (env := env) (fe := fe),
      internE_specC (mode := mode) (env := env) (fe := fe)] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:264-268 litToCtorIfNat — the
function as ONE equation over the tag and the literal projection
(`litNat?`, `Core/Walks/Nat.lean`). -/
theorem litToCtorIfNat_eq (x : Expr) : ConLeche.litToCtorIfNat env x =
    if exprTag x = ETag.lit ∧ (litNat? (exprLit x)).isSome ∧
        ConLeche.natLitSupported env = true then
      ConLeche.natLitToConstructor ((litNat? (exprLit x)).getD 0)
    else x := by
  cases x with
  | lit l => cases l <;> simp [ConLeche.litToCtorIfNat, exprTag, exprLit, litNat?]
  | _ => simp [ConLeche.litToCtorIfNat, exprTag, ETag.lit, ETag.bvar, ETag.fvar,
      ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.proj]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:264-268 litToCtorIfNat — the
twin with its literal arm one constructor deep (`litNat?` reads the literal),
so that `vcgen`'s fall-through conditions are flat
(`_tmp/corpus/vcgen-grind/nested-ctor-fallthrough-hyp.lean`). -/
theorem litToCtorIfNat_split (h : EIdx) : ConRon.Arena.litToCtorIfNat fe h =
    (if h.tag == ETag.lit then do
      match ← view h with
      | .lit l =>
        match litNat? l with
        | some n => do if ← ConRon.Arena.natLitSupported fe then
            ConRon.Arena.natLitToConstructor n else pure h
        | none => pure h
      | _ => pure h
    else pure h) := by
  simp only [ConRon.Arena.litToCtorIfNat]
  split
  · congr; funext v
    cases v with
    | lit l => cases l <;> rfl
    | _ => rfl
  · rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:264-268 litToCtorIfNat —
**THEOREM 1 for `litToCtorIfNat`**: a supported `Nat` literal one layer. -/
theorem litToCtorIfNat_spec (s₀ : AState) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store h = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.litToCtorIfNat fe h
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteE s'.store r = some (ConLeche.litToCtorIfNat env x); ⊤⦄ := by
  sym only [bridge_grind, litToCtorIfNat_eq, Option.getD_some] =>
    vcgen [litToCtorIfNat_split, natLitSupported_spec (mode := mode) (env := env) (fe := fe),
      natLitToConstructor_spec (mode := mode) (env := env) (fe := fe)] <;> finish

/-- con-leche: none — a denoted capability record keeps the stored `sortZ`. -/
theorem denoteCaps_sortZ {st : EStore} {c : IIndCaps} {dc : IndCaps}
    (h : Frontend.denoteCaps st c = some dc) : dc.sortZ = c.sortZ := by
  simp only [Frontend.denoteCaps] at h
  split at h
  · cases h; rfl
  · simp at h

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:93-95 capsNeverZero —
**THEOREM 1 for `capsNeverZero`**. -/
theorem capsNeverZero_spec (s₀ : AState) (lps : List NIdx) (us : LsIdx)
    (icaps : IIndCaps) (ks : List ConLeche.Name) (vs : List Level)
    (caps : IndCaps) (hok : CheckOK mode env fe s₀)
    (hks : Frontend.denoteNList s₀.store.ns lps = some ks)
    (hvs : denoteLs s₀.store.lss us = some vs)
    (hcaps : Frontend.denoteCaps s₀.store icaps = some caps) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.capsNeverZero lps us icaps
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.capsNeverZero ks vs caps; ⊤⦄ := by
  sym only [bridge_grind, ConLeche.capsNeverZero, denoteCaps_sortZ hcaps] =>
    vcgen [ConRon.Arena.capsNeverZero, readNamesM_specC (mode := mode) (env := env) (fe := fe),
      readLevelsM_specC (mode := mode) (env := env) (fe := fe)] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean looseBVarsBounded —
`ExprOps/Ranges.lean`'s `looseBVarsBoundedFast_spec` at the tier's invariant
(`CheckOK.mono`). -/
theorem looseBVarsBoundedFast_specC (fuel k : Nat) (s₀ : AState) (e : EIdx)
    (hok : CheckOK mode env fe s₀) (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => s = s₀⦄ looseBVarsBoundedFast fuel k e
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins ∧
        RelV (Expr.looseBVarsBounded k) s₀.store e r; ⊤⦄ :=
  triple_mono (ExprOps.looseBVarsBoundedFast_spec fuel k s₀ e hok.state hden)
    (fun _ _ ⟨hst, hc, hp, hr⟩ =>
      ⟨hok.mono (by rw [stateOK_eq, hst]; exact hok.state.wf)
        (by rw [hst]; exact Ext.refl _) hc hp, hst, hp, hr⟩)

/-- con-leche: none — the leaf guard's answer at the base's denotation (a
named predicate on the denotation term). -/
def LeafAns (st : EStore) (fab : EIdx) (r : Bool) : Option Expr → Prop
  | some eb => RelV (ExprOps.leavesSubSpec (Expr.fvarLeaves eb)) st fab r
  | none => True

/-- con-leche: none — `LeafAns` at a denoting base. -/
@[bridge_grind =] theorem LeafAns.some_eq (st : EStore) (fab : EIdx) (r : Bool) (eb : Expr) :
    LeafAns st fab r (some eb) = RelV (ExprOps.leavesSubSpec (Expr.fvarLeaves eb)) st fab r :=
  rfl

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1264-1268 leafGuard —
`ExprOps/Guards.lean`'s `leafGuard_spec` in answer shape (`LeafAns`: no `∀`
for `grind` to instantiate). -/
theorem leafGuard_specA (fuel : Nat) (s₀ : AState) (fab base : EIdx)
    (hok : StateOK s₀) (hfab : (denoteE s₀.store fab).isSome = true)
    (hbase : (denoteE s₀.store base).isSome = true) :
    ⦃fun s => s = s₀⦄ leafGuard fuel fab base
    ⦃fun r s' => s' = s₀ ∧ LeafAns s₀.store fab r (denoteE s₀.store base); ⊤⦄ :=
  triple_mono (ExprOps.leafGuard_spec fuel s₀ fab base hok hfab hbase)
    (fun r _ ⟨hs, hr⟩ => ⟨hs, by
      cases hb : denoteE s₀.store base with
      | none => trivial
      | some eb => exact hr eb hb⟩)

/-- con-leche: ConLeche/Kernel/Core.lean:586-588 majorToCtor (the scope
guard) — **THEOREM 1 for `fabScopeOk`**: the executed tier's three memoised
walks decide con-leche's syntactic guard. -/
theorem fabScopeOk_spec (s₀ : AState) (d : Nat) (fab major : EIdx)
    (ef em : Expr) (hok : CheckOK mode env fe s₀)
    (hf : denoteE s₀.store fab = some ef) (hm : denoteE s₀.store major = some em) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.fabScopeOk d fab major
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧
        r = (ef.wscopedB d && ef.looseBVarsBounded 0 &&
          ef.fvarLeaves.all (fun l => em.fvarLeaves.contains l)); ⊤⦄ := by
  sym only [bridge_grind, ExprOps.leavesSubSpec] =>
    vcgen [ConRon.Arena.fabScopeOk, ExprOps.wscopedBFast_spec,
      looseBVarsBoundedFast_specC (mode := mode) (env := env) (fe := fe),
      leafGuard_specA] <;> finish

/-- con-leche: none — the denotation of an appended handle list. -/
theorem denoteEList_appendI {st : EStore} :
    ∀ {as bs : List EIdx} {xs ys : List Expr},
      Frontend.denoteEList st as = some xs →
      Frontend.denoteEList st bs = some ys →
      Frontend.denoteEList st (as ++ bs) = some (xs ++ ys)
  | [], bs, xs, ys, ha, hb => by
    simp only [Frontend.denoteEList, Option.some.injEq] at ha
    subst ha; simpa using hb
  | a :: as, bs, xs, ys, ha, hb => by
    obtain ⟨x, xs', hx, hxs, rfl⟩ := denoteEList_cons_inv ha
    simp only [List.cons_append, Frontend.denoteEList, hx,
      denoteEList_appendI hxs hb]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:741-743 etaFabArgsE — **THEOREM
1 for `etaFabArgsE`**: the η rescue's fabricated argument spine, the type's
arguments then `etaProjs` (`Walks/Eta.lean`'s `etaProjs_spec`). -/
theorem etaFabArgsE_spec (s₀ : AState) (T : NIdx)
    (targs : List EIdx) (major : EIdx) (nF : Nat) (Tn : ConLeche.Name)
    (ts : List Expr) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hT : denoteN s₀.store.ns T = some Tn)
    (hts : Frontend.denoteEList s₀.store targs = some ts)
    (hx : denoteE s₀.store major = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.etaFabArgsE T targs major nF
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Frontend.denoteEList s'.store r =
          some (ConLeche.etaFabArgsE Tn ts x nF); ⊤⦄ := by
  sym only [bridge_grind, ConLeche.etaFabArgsE, denoteEList_append_eq] =>
    vcgen [ConRon.Arena.etaFabArgsE,
      etaProjs_spec (mode := mode) (env := env) (fe := fe) (Tn := Tn) (y := x)] <;>
      finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:789-795 andRescueSlotsOf — one
slot's test at the environment's answer (the body of the `all`). -/
def andSlotOk (cn : ConLeche.Name) (nP : Nat) (ls : List Level) :
    Option ProjEntry → Bool
  | some e => e.ctor == cn && e.numParams == nP && e.numFields == 2 && e.fireOk ls
  | none => false
attribute [bridge_grind =] andSlotOk

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:789-795 andRescueSlotsOf — the
slots `j, j+1, …` for `n` slots, one equation per step. -/
def andSlotsFrom (env : Env) (cn : ConLeche.Name) (nP : Nat) (ls : List Level) :
    Nat → Nat → Bool
  | 0, _ => true
  | n + 1, j => andSlotOk cn nP ls (env.findProj? ConLeche.andName j) &&
      andSlotsFrom env cn nP ls n (j + 1)
attribute [bridge_grind =] andSlotsFrom

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:796-799 andRescueSlots — the
function is the two slots from slot 0. -/
@[bridge_grind =] theorem andRescueSlots_eq (cn : ConLeche.Name) (nP : Nat)
    (ls : List Level) :
    ConLeche.andRescueSlots env cn nP ls = andSlotsFrom env cn nP ls 2 0 := by
  simp only [ConLeche.andRescueSlots, ConLeche.andRescueSlotsOf, andSlotsFrom, List.range,
    List.range.loop, List.all_cons, List.all_nil, Bool.and_true]
  cases env.findProj? ConLeche.andName 0 <;> cases env.findProj? ConLeche.andName 1 <;> rfl

section AndSlots

/-! The slot test compares the entry's constructor handle with the rescue's:
the name handles as `idxOfName` (`Bridge/Grind.lean` §6), for this walk only. -/

local grind_pattern [bridge_grind] nameIdx => denoteN st.ns n
local grind_pattern [bridge_grind] NameIdx.some => NameIdx st n (some nm)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:796-809 andRescueSlotsOf — the
two-slot walk, from slot `j` for `n` slots (answer `andSlotsFrom`). -/
theorem andRescueSlotsGo_specA (ctor : NIdx) (nP : Nat) (ust : LsIdx)
    (cn : ConLeche.Name) (ls : List Level) (an : NIdx) :
    ∀ (n j : Nat) (s₀ : AState), CheckOK mode env fe s₀ →
      denoteN s₀.store.ns an = some ConLeche.andName →
      denoteN s₀.store.ns ctor = some cn → denoteLs s₀.store.lss ust = some ls →
      ⦃fun s => s = s₀⦄ ConRon.Arena.andRescueSlotsGo fe an ctor nP ust n j
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ r = andSlotsFrom env cn nP ls n j; ⊤⦄ := by
  intro n
  induction n with
  | zero =>
    intro j s₀ hok _ _ _
    sym only [bridge_grind] => vcgen [ConRon.Arena.andRescueSlotsGo] <;> finish
  | succ n ih =>
    intro j s₀ hok han hc hus
    sym only [bridge_grind, Option.getD_some] =>
      vcgen [ConRon.Arena.andRescueSlotsGo,
        findProj?_specP (mode := mode) (env := env) (fe := fe) (Tn := ConLeche.andName),
        IProjEntry.fireOk_specA (mode := mode) (env := env) (fe := fe), ih] <;>
        finish

end AndSlots

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:796-813 andRescueSlots —
**THEOREM 1 for `andRescueSlots`**: the pinned `And`'s two slots, ready to
fire. -/
theorem andRescueSlots_spec (s₀ : AState) (ctor : NIdx) (nP : Nat)
    (ust : LsIdx) (cn : ConLeche.Name) (ls : List Level)
    (hok : CheckOK mode env fe s₀) (hc : denoteN s₀.store.ns ctor = some cn)
    (hus : denoteLs s₀.store.lss ust = some ls) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.andRescueSlots fe ctor nP ust
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.andRescueSlots env cn nP ls; ⊤⦄ := by
  sym only [bridge_grind, hok.pins] =>
    vcgen [ConRon.Arena.andRescueSlots, ConRon.Arena.pinAnd, pinAt_specE,
      andRescueSlotsGo_specA (mode := mode) (env := env) (fe := fe) (cn := cn) (ls := ls)] <;>
      finish

/-- con-leche: none — a denoted rule's fields. -/
theorem rule_denote {st : EStore} {rl : IRecRule} {rl' : RecRule}
    (h : Frontend.denoteRule st rl = some rl') :
    rl'.ctorParams = rl.ctorParams ∧ rl'.nfields = rl.nfields ∧
      denoteN st.ns rl.ctor = some rl'.ctor ∧ denoteE st rl.rhs = some rl'.rhs ∧
      Frontend.denoteFire st rl.fire = some rl'.fire ∧
      rl'.k = rl.k ∧ rl'.eta = rl.eta := by
  simp only [Frontend.denoteRule] at h
  split at h
  · rename_i c f r hc hf hr
    cases h
    exact ⟨rfl, rfl, hc, hr, hf, rfl, rfl⟩
  · simp at h

end ConRon.Bridge.Core

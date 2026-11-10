/-
# `ConRon.Bridge.Core.Walks.IotaLeaves` — the state-only readers under `iotaRec`

The readers the stuck-major rescue and the ι step consult, each an equation
with con-leche's function.  The walks that call the knot are
`Walks/IotaMajor.lean` and `Walks/Iota.lean`.

Every proof is `sym only [bridge_grind, …] => vcgen [f, callee specs…] <;>
finish`.  What makes them `grind`-shaped: each con-leche function as ONE
equation over tags and projections (`isCtorApp_eq`, `litToCtorIfNat_eq`,
`andRescueSlots_eq` over the named slot walk `andSlotsFrom`, `formerResSort_eq`,
`ctorFamily_eq`), a twin's nested `match` one constructor deep
(`litToCtorIfNat_split`), and the callees with `∀`-shaped posts restated as
named answers (`leafGuard_specA`, `projAnsAt`, `FamAns`).
-/
module

import ConRon.Bridge.Core.Walks.ProjLit
public import ConRon.Bridge.ExprOps.Guards
import ConRon.Bridge.ExprOps.Ranges
import ConRon.Bridge.Core.Walks.Eta
import ConRon.Bridge.Core.Walks.Nat
import ConRon.Bridge.Core.Walks.Proj
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.Core.Walks.StrLit
import ConRon.Bridge.ExprOps.Spine
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Specs
public import ConRon.Bridge.Grind
import ConRon.Bridge.GrindAttr
public import ConRon.Arena.Core

public section

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {eager : Bool} {env : Env} {fe : IFEnv}

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
    (hok : CheckOK eager env fe s₀) (hda : denoteE s₀.store a = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.isCtorApp fe a
    ⦃fun r s' => s' = s₀ ∧ r = ConLeche.isCtorApp env x; ⊤⦄ := by
  sym only [bridge_grind, isCtorApp_eq] =>
    vcgen [ConRon.Arena.isCtorApp, ExprOps.getAppFn_spec] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:197-200 natLitToConstructor —
**THEOREM 1 for `natLitToConstructor`**: `Nat.zero`, or `Nat.succ` applied to
the predecessor literal. -/
theorem natLitToConstructor_spec (s₀ : AState) (n : Nat)
    (hok : CheckOK eager env fe s₀) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.natLitToConstructor n
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteE s'.store r = some (ConLeche.natLitToConstructor n); ⊤⦄ := by
  sym only [bridge_grind, ConLeche.natLitToConstructor, hok.pins] =>
    vcgen [ConRon.Arena.natLitToConstructor, ConRon.Arena.pinNatZero, ConRon.Arena.pinNatSucc,
      pinAt_specE, constE_specA (eager := eager) (env := env) (fe := fe),
      internE_specC (eager := eager) (env := env) (fe := fe)] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:264-268 litToCtorIfNat — the
function as ONE equation over the tag and the literal projection
(`litNat?`, `Core/Walks/Nat.lean`). -/
theorem litToCtorIfNat_eq (x : Expr) : ConLeche.litToCtorIfNat env x =
    if exprTag x = ETag.lit ∧ (litNat? (exprLit x)).isSome ∧
        ConLeche.natLitStored env = true then
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
        | some n => do if ← ConRon.Arena.natLitStored fe then
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
    (hok : CheckOK eager env fe s₀) (hda : denoteE s₀.store h = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.litToCtorIfNat fe h
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteE s'.store r = some (ConLeche.litToCtorIfNat env x); ⊤⦄ := by
  sym only [bridge_grind, litToCtorIfNat_eq, Option.getD_some] =>
    vcgen [litToCtorIfNat_split, natLitStored_spec (eager := eager) (env := env) (fe := fe),
      natLitToConstructor_spec (eager := eager) (env := env) (fe := fe)] <;> finish

/-! ## 2. The family's sort, read off its stored type -/

/-- con-leche: none — the denotation of an OPTIONAL level handle (`denoteEO`'s
shape). -/
@[expose] def denoteLO (st : EStore) : Option LIdx → Option (Option Level)
  | none => some none
  | some j => (denoteL st.ls j).map some

/-- con-leche: none — `denoteLO` at `none`. -/
@[bridge_grind =] theorem denoteLO_none (st : EStore) : denoteLO st none = some none := rfl

/-- con-leche: none — `denoteLO` at a handle. -/
@[bridge_grind =] theorem denoteLO_some (st : EStore) (j : LIdx) :
    denoteLO st (some j) = (denoteL st.ls j).map some := rfl

/-- con-leche: none — a denoted constant record's three fields. -/
@[bridge_grind →] theorem denoteCV_fields {st : EStore} {v : IConstantVal} {c : ConstantVal}
    (h : Frontend.denoteCV st v = some c) :
    denoteN st.ns v.name = some c.name ∧
      Frontend.denoteNList st.ns v.levelParams = some c.levelParams ∧
      denoteE st v.type = some c.type := denoteCV_inv h

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:59-65 formerResSort — the function
as ONE equation over the result's tag and sort projection. -/
theorem formerResSort_eq (ty : Expr) : ConLeche.formerResSort ty =
    if exprTag ty.piResult = ETag.sort then some (exprSort ty.piResult) else none := by
  simp only [ConLeche.formerResSort]
  cases ty.piResult <;> simp [exprTag, exprSort, ETag.sort, ETag.bvar, ETag.fvar,
    ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:59-65 formerResSort — **THEOREM 1
for `formerResSort`**: the sort the stored type ends in. -/
theorem formerResSort_spec (s₀ : AState) (ty : EIdx) (tyP : Expr)
    (hok : CheckOK eager env fe s₀) (hty : denoteE s₀.store ty = some tyP) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.formerResSort ty
    ⦃fun r s' => s' = s₀ ∧ r.isSome = (ConLeche.formerResSort tyP).isSome ∧
        denoteLO s₀.store r = some (ConLeche.formerResSort tyP); ⊤⦄ := by
  sym only [bridge_grind, formerResSort_eq] =>
    vcgen [ConRon.Arena.formerResSort, ExprOps.piResult_spec] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:67-69 formerDefHeaded — the function
as ONE equation over the result's tag. -/
theorem formerDefHeaded_eq (cv : ConstantVal) :
    ConLeche.formerDefHeaded cv = !(ConLeche.formerResSort cv.type).isSome := by
  simp only [ConLeche.formerDefHeaded]
  cases ConLeche.formerResSort cv.type <;> rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:67-69 formerDefHeaded — **THEOREM 1
for `formerDefHeaded`**. -/
theorem formerDefHeaded_spec (s₀ : AState) (cv : IConstantVal) (cvP : ConstantVal)
    (hok : CheckOK eager env fe s₀) (hcv : Frontend.denoteCV s₀.store cv = some cvP) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.formerDefHeaded cv
    ⦃fun r s' => s' = s₀ ∧ r = ConLeche.formerDefHeaded cvP; ⊤⦄ := by
  sym only [bridge_grind, formerDefHeaded_eq] =>
    vcgen [ConRon.Arena.formerDefHeaded,
      formerResSort_spec (eager := eager) (env := env) (fe := fe) (tyP := cvP.type)] <;> finish

/-- con-leche: none — `readLevelM` at the tier's invariant. -/
theorem readLevelM_specC (s₀ : AState) (h : LIdx) (hok : CheckOK eager env fe s₀) :
    ⦃fun s => s = s₀⦄ readLevelM h
    ⦃fun u s' => CheckOK eager env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins ∧
        denoteL s₀.store.ls h = some u; ⊤⦄ :=
  triple_mono (readLevelM_spec s₀ h hok.caches.readL)
    (fun _ _ ⟨hst, hm, hp, hc, hd, hL⟩ => ⟨CheckOK.ofReadL hok hst hm hp hc hL, hst, hp, hd⟩)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:71-77 formerZ — **THEOREM 1 for
`formerZ`**: the zero-ness datum of the sort the stored type ends in. -/
theorem formerZ_spec (s₀ : AState) (cv : IConstantVal) (cvP : ConstantVal)
    (hok : CheckOK eager env fe s₀) (hcv : Frontend.denoteCV s₀.store cv = some cvP) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.formerZ cv
    ⦃fun r s' => CheckOK eager env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins ∧
        r = ConLeche.formerZ cvP; ⊤⦄ := by
  sym only [bridge_grind, ConLeche.formerZ, formerResSort_eq] =>
    vcgen [ConRon.Arena.formerZ,
      formerResSort_spec (eager := eager) (env := env) (fe := fe) (tyP := cvP.type),
      readLevelM_specC (eager := eager) (env := env) (fe := fe)] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:79-87 formerNeverZero — **THEOREM 1
for `formerNeverZero`**. -/
theorem formerNeverZero_spec (s₀ : AState) (cv : IConstantVal) (cvP : ConstantVal)
    (us : LsIdx) (ls : List Level)
    (hok : CheckOK eager env fe s₀) (hcv : Frontend.denoteCV s₀.store cv = some cvP)
    (hus : denoteLs s₀.store.lss us = some ls) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.formerNeverZero cv us
    ⦃fun r s' => CheckOK eager env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins ∧
        r = ConLeche.formerNeverZero cvP ls; ⊤⦄ := by
  sym only [bridge_grind, ConLeche.formerNeverZero] =>
    vcgen [ConRon.Arena.formerNeverZero,
      formerZ_spec (eager := eager) (env := env) (fe := fe) (cvP := cvP),
      readNamesM_specC (eager := eager) (env := env) (fe := fe),
      readLevelsM_specC (eager := eager) (env := env) (fe := fe)] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:89-98 ctorFamily — the index's
answer against the environment's: a miss is a miss, a hit's two halves denote. -/
@[expose] def FamAns (st : EStore) : Option (IConstantVal × IIndCaps) →
    Option (ConstantVal × IndCaps) → Prop
  | none, o => o = none
  | some (cv, caps), some (cvP, capsP) =>
      Frontend.denoteCV st cv = some cvP ∧ Frontend.denoteCaps st caps = some capsP
  | some _, none => False

/-- con-leche: none — `FamAns` at a miss. -/
@[bridge_grind =] theorem FamAns.none_eq (st : EStore) (o : Option (ConstantVal × IndCaps)) :
    FamAns st none o = (o = none) := rfl

/-- con-leche: none — `FamAns` at two hits. -/
@[bridge_grind =] theorem FamAns.some_eq (st : EStore) (cv : IConstantVal) (caps : IIndCaps)
    (cvP : ConstantVal) (capsP : IndCaps) :
    FamAns st (some (cv, caps)) (some (cvP, capsP)) =
      (Frontend.denoteCV st cv = some cvP ∧ Frontend.denoteCaps st caps = some capsP) := rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:89-98 ctorFamily — the function as
ONE equation over the result head's tag, its name and the lookup's projections. -/
theorem ctorFamily_eq (find? : ConLeche.Name → Option ConstantInfo) (cvj : ConstantVal) :
    ConLeche.ctorFamily find? cvj =
      if exprTag cvj.type.piResult.getAppFn = ETag.const ∧
          cInd? (find? (exprConstName cvj.type.piResult.getAppFn)) = true then
        some (cIndVal (find? (exprConstName cvj.type.piResult.getAppFn)),
          cIndCaps (find? (exprConstName cvj.type.piResult.getAppFn)))
      else none := by
  simp only [ConLeche.ctorFamily]
  generalize cvj.type.piResult.getAppFn = g
  cases g <;> simp only [exprTag, exprConstName] <;> try rfl
  rename_i T _
  cases h : find? T with
  | none => simp [cInd?]
  | some ci => cases ci <;> simp [cInd?, cIndVal, cIndCaps]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:89-98 ctorFamily — **THEOREM 1 for
`ctorFamily`**: the family the constructor's type concludes in.  The family's
name arrives through four derived steps (the type, its `piResult`, its head,
the head view's name), hence `ematch := 8`. -/
theorem ctorFamily_spec (s₀ : AState) (cvj : IConstantVal) (cvjP : ConstantVal)
    (hok : CheckOK eager env fe s₀) (hcv : Frontend.denoteCV s₀.store cvj = some cvjP) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.ctorFamily fe cvj
    ⦃fun r s' => s' = s₀ ∧ FamAns s₀.store r (ConLeche.ctorFamily env.find? cvjP); ⊤⦄ := by
  sym only [bridge_grind, ctorFamily_eq] =>
    vcgen [ConRon.Arena.ctorFamily, ExprOps.piResult_spec, ExprOps.getAppFn_spec,
      viewConstName_spec] <;> finish (ematch := 12) (gen := 12)

/-- con-leche: ConLeche/Kernel/ExprOps.lean looseBVarsBounded —
`ExprOps/Ranges.lean`'s `looseBVarsBoundedFast_spec` at the tier's invariant
(`CheckOK.mono`). -/
theorem looseBVarsBoundedFast_specC (fuel k : Nat) (s₀ : AState) (e : EIdx)
    (hok : CheckOK eager env fe s₀) (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => s = s₀⦄ looseBVarsBoundedFast fuel k e
    ⦃fun r s' => CheckOK eager env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins ∧
        RelV (Expr.looseBVarsBounded k) s₀.store e r; ⊤⦄ :=
  triple_mono (ExprOps.looseBVarsBoundedFast_spec fuel k s₀ e hok.state hden)
    (fun _ _ ⟨hst, hc, hp, hr⟩ =>
      ⟨hok.mono (by rw [stateOK_eq, hst]; exact hok.state.wf)
        (by rw [hst]; exact Ext.refl _) hc hp, hst, hp, hr⟩)

/-- con-leche: none — the leaf guard's answer at the base's denotation (a
named predicate on the denotation term). -/
@[expose] def LeafAns (st : EStore) (fab : EIdx) (r : Bool) : Option Expr → Prop
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
    (ef em : Expr) (hok : CheckOK eager env fe s₀)
    (hf : denoteE s₀.store fab = some ef) (hm : denoteE s₀.store major = some em) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.fabScopeOk d fab major
    ⦃fun r s' => CheckOK eager env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧
        r = (ef.wscopedB d && ef.looseBVarsBounded 0 &&
          ef.fvarLeaves.all (fun l => em.fvarLeaves.contains l)); ⊤⦄ := by
  sym only [bridge_grind, ExprOps.leavesSubSpec] =>
    vcgen [ConRon.Arena.fabScopeOk, ExprOps.wscopedBFast_spec,
      looseBVarsBoundedFast_specC (eager := eager) (env := env) (fe := fe),
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
    (hok : CheckOK eager env fe s₀) (hT : denoteN s₀.store.ns T = some Tn)
    (hts : Frontend.denoteEList s₀.store targs = some ts)
    (hx : denoteE s₀.store major = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.etaFabArgsE T targs major nF
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Frontend.denoteEList s'.store r =
          some (ConLeche.etaFabArgsE Tn ts x nF); ⊤⦄ := by
  sym only [bridge_grind, ConLeche.etaFabArgsE, denoteEList_append_eq] =>
    vcgen [ConRon.Arena.etaFabArgsE,
      etaProjs_spec (eager := eager) (env := env) (fe := fe) (Tn := Tn) (y := x)] <;>
      finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1105-1115 andRescueSlotsOf — one
slot's test at the environment's answer (the body of the `all`). -/
def andSlotOk (cn : ConLeche.Name) (nP : Nat) : Option ProjEntry → Bool
  | some e => e.ctor == cn && e.numParams == nP && e.numFields == 2
  | none => false
attribute [bridge_grind =] andSlotOk

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1105-1115 andRescueSlotsOf — the
slots `j, j+1, …` for `n` slots, one equation per step. -/
def andSlotsFrom (env : Env) (cn : ConLeche.Name) (nP : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, j => andSlotOk cn nP (env.findProj? ConLeche.andName j) &&
      andSlotsFrom env cn nP n (j + 1)
attribute [bridge_grind =] andSlotsFrom

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1117-1119 andRescueSlots — the
function is the two slots from slot 0. -/
@[bridge_grind =] theorem andRescueSlots_eq (cn : ConLeche.Name) (nP : Nat) :
    ConLeche.andRescueSlots env cn nP = andSlotsFrom env cn nP 2 0 := by
  simp only [ConLeche.andRescueSlots, ConLeche.andRescueSlotsOf, andSlotsFrom, List.range,
    List.range.loop, List.all_cons, List.all_nil, Bool.and_true]
  cases env.findProj? ConLeche.andName 0 <;> cases env.findProj? ConLeche.andName 1 <;> rfl

section AndSlots

/-! The slot test compares the entry's constructor handle with the rescue's:
the name handles as `idxOfName` (`Bridge/Grind.lean` §6), for this walk only. -/

local grind_pattern [bridge_grind] nameIdx => denoteN st.ns n
local grind_pattern [bridge_grind] NameIdx.some => NameIdx st n (some nm)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1105-1115 andRescueSlotsOf — the
two-slot walk, from slot `j` for `n` slots, is `andSlotsFrom` (a pure walk:
an equation). -/
theorem andRescueSlotsGo_eq (ctor : NIdx) (nP : Nat) (cn : ConLeche.Name) (an : NIdx)
    (s : AState) (hok : CheckOK eager env fe s)
    (han : denoteN s.store.ns an = some ConLeche.andName)
    (hc : denoteN s.store.ns ctor = some cn) :
    ∀ n j, ConRon.Arena.andRescueSlotsGo fe an ctor nP n j = andSlotsFrom env cn nP n j := by
  intro n
  induction n with
  | zero => intro j; rfl
  | succ n ih =>
    intro j
    have hpa := projAnsAt (i := j) hok han
    obtain ⟨rk, hrk⟩ := hok.state.wf
    simp only [ConRon.Arena.andRescueSlotsGo, andSlotsFrom, ih]
    cases hp : fe.findProj? an j with
    | none =>
      rw [hp] at hpa
      simp only [ProjAns] at hpa
      rw [hpa]; rfl
    | some e =>
      rw [hp] at hpa
      obtain ⟨hden, hsome⟩ := hpa
      obtain ⟨p, hpo⟩ := Option.isSome_iff_exists.mp hsome
      rw [hpo] at hden ⊢
      obtain ⟨_, _, hct, _, _, hnp, hnf⟩ := denoteProjEntry_inv hden
      have hctr : (e.ctor == ctor) = (p.ctor == cn) := by
        by_cases h : p.ctor = cn
        · subst h; simp [denoteN_inj hrk.nsWF hct hc]
        · have : e.ctor ≠ ctor := fun h' => h (by subst h'; exact Option.some.inj (hct.symm.trans hc))
          rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]
      simp only [andSlotOk, hctr, hnp, hnf]
      split <;> simp_all

end AndSlots

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1117-1119 andRescueSlots —
**THEOREM 1 for `andRescueSlots`**: the pinned `And`'s two slots, ready to
fire. -/
theorem andRescueSlots_spec (s₀ : AState) (ctor : NIdx) (nP : Nat) (cn : ConLeche.Name)
    (hok : CheckOK eager env fe s₀) (hc : denoteN s₀.store.ns ctor = some cn) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.andRescueSlots fe ctor nP
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.andRescueSlots env cn nP; ⊤⦄ := by
  have hgo := andRescueSlotsGo_eq (eager := eager) (env := env) (fe := fe) ctor nP cn
  sym only [bridge_grind, hok.pins] =>
    vcgen [ConRon.Arena.andRescueSlots, ConRon.Arena.pinAnd, pinAt_specE] <;> finish

/-- con-leche: none — a denoted capability record's fields. -/
theorem denoteCaps_fields {st : EStore} {c : IIndCaps} {dc : IndCaps}
    (h : Frontend.denoteCaps st c = some dc) :
    dc.eta = c.eta ∧ dc.nparams = c.nparams ∧ dc.nIdx = c.nIdx := by
  simp only [Frontend.denoteCaps] at h
  split at h
  · cases h; exact ⟨rfl, rfl, rfl⟩
  · simp at h

/-- con-leche: none — two denoting name-handle lists compare as their
denotations. -/
theorem denoteNList_beq {st : EStore} (hwf : StoreWF st) {as bs : List NIdx}
    {xs ys : List ConLeche.Name} (ha : Frontend.denoteNList st.ns as = some xs)
    (hb : Frontend.denoteNList st.ns bs = some ys) : (as == bs) = (xs == ys) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact denoteNList_eq_iff hwf ha hb

/-- con-leche: none — two denoting name handles compare as their names. -/
theorem denoteN_beq {st : EStore} (hwf : StoreWF st) {a b : NIdx}
    {x y : ConLeche.Name} (ha : denoteN st.ns a = some x) (hb : denoteN st.ns b = some y) :
    (a == b) = (x == y) := by
  obtain ⟨rk, hrk⟩ := hwf
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro rfl; exact Option.some.inj (ha.symm.trans hb)
  · rintro rfl; exact denoteN_inj hrk.nsWF ha hb

/-- con-leche: none — the twin's optional projection table against con-leche's:
both absent, or the twin's denoting con-leche's. -/
@[expose] def TblAns (st : EStore) : Option IProjTable → Option ProjTable → Prop
  | none, none => True
  | some t, some p => Frontend.denoteProjTable st t = some p
  | _, _ => False

/-- con-leche: none — `TblAns` at an absent table. -/
@[bridge_grind =] theorem TblAns.none_eq (st : EStore) (o : Option ProjTable) :
    TblAns st none o = (o = none) := by
  cases o <;> simp [TblAns]

/-- con-leche: none — `TblAns` at a present table. -/
@[bridge_grind =] theorem TblAns.some_eq (st : EStore) (t : IProjTable) (o : Option ProjTable) :
    TblAns st (some t) o = (∃ p, o = some p ∧ Frontend.denoteProjTable st t = some p) := by
  cases o <;> simp [TblAns]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:923-941 etaRescueTable? — **THEOREM
1 for `etaRescueTable?`**: the cited `&&` chain at the denotations, the table
it answers with denoting con-leche's. -/
theorem etaRescueTable?_spec (s₀ : AState) (tbl? : Option IProjTable) (tblP? : Option ProjTable)
    (ctor : NIdx) (cn : ConLeche.Name)
    (cvj cvT : IConstantVal) (cvjP cvTP : ConstantVal) (caps : IIndCaps) (capsP : IndCaps)
    (hok : CheckOK eager env fe s₀) (ht : TblAns s₀.store tbl? tblP?)
    (hc : denoteN s₀.store.ns ctor = some cn)
    (hcvj : Frontend.denoteCV s₀.store cvj = some cvjP)
    (hcvT : Frontend.denoteCV s₀.store cvT = some cvTP)
    (hcaps : Frontend.denoteCaps s₀.store caps = some capsP) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.etaRescueTable? tbl? ctor cvj cvT caps
    ⦃fun r s' => s' = s₀ ∧
        TblAns s₀.store r (ConLeche.etaRescueTable? tblP? cn cvjP cvTP capsP); ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨he, -⟩ := denoteCaps_fields hcaps
  obtain ⟨-, hlj, -⟩ := denoteCV_inv hcvj
  obtain ⟨-, hlT, -⟩ := denoteCV_inv hcvT
  have h2 := denoteNList_beq hwf hlj hlT
  unfold ConRon.Arena.etaRescueTable?
  match tbl?, tblP?, ht with
  | none, none, _ =>
    exact triple_pureS ⟨rfl, trivial⟩
  | some t, some p, hp =>
    simp only [TblAns] at hp
    have h1 := denoteN_beq hwf (denoteProjTable_ctor hp) hc
    dsimp only
    rw [h1, h2, ← he]
    by_cases hg : (capsP.eta && p.ctor == cn && cvjP.levelParams == cvTP.levelParams) = true
    · rw [ite_eq_left hg]
      unfold ConRon.Arena.pinAndIntro
      refine triple_seq (pinAt_specE s₀ _ hok.pins) ?_
      rintro ai s1 ⟨rfl, hai⟩
      have hai' : denoteN s1.store.ns ai = some ConLeche.andIntroName := by rw [hai]; rfl
      have h3 := denoteN_beq hwf hc hai'
      simp only [ConLeche.etaRescueTable?, hg, Bool.true_and, bne]
      by_cases hq : (ctor == ai) = true
      · have hq' : (cn == ConLeche.andIntroName) = true := h3 ▸ hq
        simp only [hq, Bool.not_true, Bool.false_eq_true, ite_false, hq']
        exact triple_pureS ⟨rfl, trivial⟩
      · have hq' : (cn == ConLeche.andIntroName) = false := by
          rw [← h3]; simpa using hq
        have hq2 : (ctor == ai) = false := by simpa using hq
        simp only [hq2, Bool.not_false, ite_true, hq']
        exact triple_pureS ⟨rfl, hp⟩
    · rw [ite_eq_right hg]
      refine triple_pureS ⟨rfl, ?_⟩
      simp only [ConLeche.etaRescueTable?]
      simp only [Bool.not_eq_true] at hg
      rw [hg]; trivial

/-- con-leche: none — a denoted rule's fields. -/
theorem rule_denote {st : EStore} {rl : IRecRule} {rl' : RecRule}
    (h : Frontend.denoteRule st rl = some rl') :
    rl'.nfields = rl.nfields ∧
      denoteN st.ns rl.ctor = some rl'.ctor ∧ denoteE st rl.rhs = some rl'.rhs ∧
      Frontend.denoteFire st rl.fire = some rl'.fire := by
  simp only [Frontend.denoteRule] at h
  split at h
  · rename_i c f r hc hf hr
    cases h
    exact ⟨rfl, hc, hr, hf⟩
  · simp at h

end ConRon.Bridge.Core

/-
# `ConRon.Bridge.Core.Walks.IotaMajor` — the ι major's preparation

`litMajorToCtor`, the stuck-major rescue `majorToCtor` (K, η, the pinned
`And`) and `prepareMajor`, which runs them in the official kernel's order
(lean4#15351): the η rescue is uncertified, K and `And` check the fabricated
constructor's type and, at the verified mode, proof irrelevance.

Every walk is `sym only [bridge_grind, …] => vcgen [f, callee specs…] <;>
finish`.  The knot slots and the callees are in answer shape
(`Core/Knot.lean`'s `KnotSpec.whnfS`/`inferIOS`/`defeqS`): a subject's
denotation goes in as the term `denoteE s₀.store i` (`DenWS`), the answer
comes out as a named predicate on the denotation terms (`SlotAns`, which is
`SlotRes` at the answer's denotation, `PairAns`, `ScopeAns`, …), the pure
run's fuel inside a `RunE`/`Runs` atom, never an `∃` in a post.  The
pure side is con-leche's text at its exits: one `Runs` lemma per exit of a
named fuelled op (`mtcKOp`, `mtcEtaOp`, `mtcAndOp`, `majorToCtorOp`,
`litMajorOp`, `prepOp`), which merges the callees' fuels with con-leche's
monotonicity lemmas.  The twin's three rescue blocks are named programs
(`majorKA`, `majorEtaA`, `majorAndA`, `majorToCtor_one` by `rfl`), and the
two literal matches run on equations one constructor deep
(`litMajorToCtor_split`, `isStrLit_split`).
-/
module

import ConRon.Bridge.Core.Walks.IotaLeaves
public import ConRon.Bridge.Core.Walks.Former
public import ConRon.Bridge.Core.Walks.Stuck
import ConRon.Bridge.Core.Walks.Eta
import ConRon.Bridge.Core.Walks.StrLit
import ConRon.Bridge.Core.Walks.StrCtor
import ConRon.Bridge.ExprOps.Subst
import ConRon.Bridge.Core.Walks.Spine
import ConRon.Bridge.Core.Walks.Mono
import ConRon.Bridge.Core.Memo
import ConLeche.Verify.InferLemmas
import ConRon.Bridge.Specs
import ConRon.Bridge.GrindAttr
import ConRon.Bridge.Core.Walks.ProjLit -- shake: keep (its `grind_pattern [bridge_grind] strLitToConstructor_WScoped`; shake records the lemma, not the pattern)

public section

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {eager : Bool} {env : Env} {fe : IFEnv}

local grind_pattern [bridge_grind] nidx_eq_of_denote => StoreWF st, denoteN st.ns a, denoteN st.ns b where
  guard denoteN st.ns a = denoteN st.ns b
  a =/= b

/-! ## The fuel-free answers

The knot slots' and the walks' answers with the pure run's fuel inside a
`RunE`/`Runs` atom: a slot's `SimE` (`Core/Knot.lean`'s `SlotAns` at a
denoting subject) is `SlotRes` at the answer's denotation term, a walk's
`SimEOp` is `OutE` there — no `∃` reaches `grind`. -/

/-- a fuelled pure run reaches `v` at some fuel -/
def Runs {α : Type} (P : Nat → CheckM α) (v : α) : Prop := ∃ F, P F = .ok v

/-- a knot slot's pure run at a subject reaches `v` -/
def RunE (op : Nat → Nat → Expr → CheckM Expr) (d : Nat) (e v : Expr) : Prop :=
  ∃ F, op F d e = .ok v

/-- a knot slot's result at the answer's denotation: well scoped, and the
pure run's value -/
@[expose] def SlotRes (op : Nat → Nat → Expr → CheckM Expr) (d : Nat) (e : Expr) : Option Expr → Prop
  | some v => Expr.WScoped d v ∧ RunE op d e v
  | none => False

/-- con-leche: none — `SlotRes` at a denoting answer. -/
@[bridge_grind =] theorem SlotRes.some_eq (op : Nat → Nat → Expr → CheckM Expr) (d : Nat)
    (e v : Expr) : SlotRes op d e (some v) = (Expr.WScoped d v ∧ RunE op d e v) := rfl

/-- con-leche: none — a knot slot's answer denotes. -/
theorem SlotRes.isSome {op : Nat → Nat → Expr → CheckM Expr} {d : Nat} {e : Expr}
    {o : Option Expr} (h : SlotRes op d e o) : o.isSome = true := by
  cases o with
  | none => exact h.elim
  | some _ => rfl
grind_pattern [bridge_grind] SlotRes.isSome => SlotRes op d e o

/-- con-leche: none — a slot's `SimE` answer IS `SlotRes` at the answer's
denotation term. -/
@[bridge_grind =] theorem simE_eq_slotRes (op : Nat → Nat → Expr → CheckM Expr) (d : Nat)
    (e : Expr) (st : EStore) (r : EIdx) : SimE op d e st r = SlotRes op d e (denoteE st r) := by
  unfold SimE; cases denoteE st r <;> simp [SlotRes, RunE]

/-- a walk's answer at its result denotation -/
@[expose] def OutE (P : Nat → CheckM Expr) (d : Nat) : Option Expr → Prop
  | some v => Expr.WScoped d v ∧ Runs P v
  | none => False

/-- con-leche: none — `OutE` at a denoting answer. -/
@[bridge_grind =] theorem OutE.some_eq (P : Nat → CheckM Expr) (d : Nat) (v : Expr) :
    OutE P d (some v) = (Expr.WScoped d v ∧ Runs P v) := rfl

/-- con-leche: none — a walk's answer denotes. -/
theorem OutE.isSome {P : Nat → CheckM Expr} {d : Nat} {o : Option Expr} (h : OutE P d o) :
    o.isSome = true := by
  cases o with
  | none => exact h.elim
  | some _ => rfl
grind_pattern [bridge_grind] OutE.isSome => OutE P d o

/-- con-leche: none — `SimEOp` IS `OutE` at the answer's denotation term. -/
@[bridge_grind =] theorem simEOp_eq (P : Nat → CheckM Expr) (d : Nat) (st : EStore) (r : EIdx) :
    SimEOp P d st r = OutE P d (denoteE st r) := by
  unfold SimEOp; cases h : denoteE st r <;> simp [OutE, Runs]

/-- the fabricated spine's scope check -/
def scopeOkFn (d : Nat) (ef em : Expr) : Bool :=
  ef.wscopedB d && ef.looseBVarsBounded 0 && ef.fvarLeaves.all (fun l => em.fvarLeaves.contains l)

/-- con-leche: none — `fabScopeOk`'s answer at two optional subjects. -/
@[expose] def ScopeAns (d : Nat) (r : Bool) : Option Expr → Option Expr → Prop
  | some ef, some em => r = scopeOkFn d ef em
  | _, _ => True

/-- con-leche: none — `ScopeAns` at two denoting subjects. -/
@[bridge_grind =] theorem ScopeAns.some_eq (d : Nat) (r : Bool) (ef em : Expr) :
    ScopeAns d r (some ef) (some em) = (r = scopeOkFn d ef em) := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — `fabScopeOk_spec` in answer shape. -/
theorem fabScopeOk_specS (s₀ : AState) (d : Nat) (fab major : EIdx)
    (hok : CheckOK eager env fe s₀)
    (hf : (denoteE s₀.store fab).isSome = true) (hm : (denoteE s₀.store major).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.fabScopeOk d fab major
    ⦃fun r s' => CheckOK eager env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins ∧
        ScopeAns d r (denoteE s₀.store fab) (denoteE s₀.store major); ⊤⦄ := by
  obtain ⟨ef, hef⟩ := Option.isSome_iff_exists.mp hf
  obtain ⟨em, hem⟩ := Option.isSome_iff_exists.mp hm
  rw [hef, hem]
  exact fabScopeOk_spec s₀ d fab major ef em hok hef hem

/-- con-leche: none — a fabrication that passes the scope check is well-scoped. -/
theorem scopeOk_wscoped {d : Nat} {ef em : Expr} (h : scopeOkFn d ef em = true) :
    Expr.WScoped d ef := by
  simp only [scopeOkFn, Bool.and_eq_true] at h
  exact Expr.WScoped.of_wscopedB h.1.1
grind_pattern [bridge_grind] scopeOk_wscoped => scopeOkFn d ef em

/-- con-leche: none — a prefix of a handle list denotes the prefix of its denotation. -/
theorem denoteEList_take_rel (st : EStore) (hs : List EIdx) (n : Nat) :
    MapRel (List.take n) (Frontend.denoteEList st hs) (Frontend.denoteEList st (hs.take n)) := by
  cases h : Frontend.denoteEList st hs with
  | none => trivial
  | some xs => exact ExprOps.denoteEList_take n hs xs h
grind_pattern [bridge_grind] denoteEList_take_rel => Frontend.denoteEList st (hs.take n)

/-- con-leche: none — a suffix of a handle list denotes the suffix of its denotation. -/
theorem denoteEList_drop_rel (st : EStore) (hs : List EIdx) (n : Nat) :
    MapRel (List.drop n) (Frontend.denoteEList st hs) (Frontend.denoteEList st (hs.drop n)) := by
  cases h : Frontend.denoteEList st hs with
  | none => trivial
  | some xs => exact ExprOps.denoteEList_drop _ _ _ h
grind_pattern [bridge_grind] denoteEList_drop_rel => Frontend.denoteEList st (hs.drop n)

/-! ## The pure side: con-leche's text at its exits -/

/-- con-leche: ConLeche/Kernel/Core.lean:728-740 litMajorToCtor — every
major but a string literal takes the `Nat` conversion. -/
theorem litMajorToCtorFueled_nstr {F d : Nat} {x : Expr}
    (hx : ∀ str, x ≠ .lit (.strVal str)) :
    ConLeche.litMajorToCtorFueled mode eager env F d x =
      .ok (ConLeche.litToCtorIfNat env x) := by
  cases x with
  | lit l =>
    cases l with
    | strVal str => exact absurd rfl (hx str)
    | natVal n => rfl
  | _ => rfl

/-! ### `majorToCtor`'s pure side, one function per rescue branch

con-leche's `majorToCtor` at `pureFns mode eager env F`, past the shared prefix
(not a constructor application, a single rule, its constructor's inductive),
split into the three branches — each a copy of the con-leche text that
`majorToCtorFueled_pre` ties to the original by `rfl`, so the copies cannot
drift. -/

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the K branch. -/
@[expose] def mtcK (mode : CheckMode) (eager : Bool) (env : Env) (F d : Nat) (rl : RecRule)
    (cvj : ConstantVal) (cnP : Nat) (T : ConLeche.Name) (major : Expr) :
    CheckM Expr :=
  (ConLeche.pureFns mode eager env F).inferIO d major >>= fun tm =>
  (ConLeche.pureFns mode eager env F).whnf d tm >>= fun tmaj =>
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ cvj.levelParams.length = ust.length then
      if cnP ≤ tmaj.getAppArgs.length then
        let fab := Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)
        if fab.wscopedB d && fab.looseBVarsBounded 0 &&
            fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) then
          (ConLeche.pureFns mode eager env F).inferIO d fab >>= fun tfab =>
          (ConLeche.pureFns mode eager env F).defeq d tmaj tfab >>= fun rd =>
          if rd then
            (if mode.verifiedChecks then
              ConLeche.proofIrrel (ConLeche.pureFns mode eager env F) d fab major
            else pure true) >>= fun r => if r then pure fab else pure major
          else pure major
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- con-leche: ConLeche/Kernel/Core.lean:513-675 majorToCtor — the η branch
(no certificate on the fabricated spine, con-leche's task #342 L11b; the
never-zero test at the use, `formerNeverZeroAt`). -/
@[expose] def mtcEta (mode : CheckMode) (eager : Bool) (env : Env) (F d : Nat) (cvT : ConstantVal)
    (caps : IndCaps) (tbl : ProjTable) (T : ConLeche.Name) (major : Expr) : CheckM Expr :=
  (ConLeche.pureFns mode eager env F).inferIO d major >>= fun tm =>
  (ConLeche.pureFns mode eager env F).whnf d tm >>= fun tmaj =>
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ tmaj.getAppArgs.length = tbl.numParams ∧
        ust.length = cvT.levelParams.length then
      formerNeverZeroAt (ConLeche.pureFns mode eager env F).whnf cvT caps ust >>= fun nz =>
      if nz then
        let fab := Expr.mkAppN (.const tbl.ctor ust)
          (ConLeche.etaFabArgsE T tmaj.getAppArgs major tbl.numFields)
        if fab.wscopedB d && fab.looseBVarsBounded 0 &&
            fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) then
          pure fab
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the pinned
`And` branch. -/
@[expose] def mtcAnd (mode : CheckMode) (eager : Bool) (env : Env) (F d : Nat) (rl : RecRule)
    (cvj : ConstantVal) (cnP : Nat) (T : ConLeche.Name) (major : Expr) :
    CheckM Expr :=
  (ConLeche.pureFns mode eager env F).inferIO d major >>= fun tm =>
  (ConLeche.pureFns mode eager env F).whnf d tm >>= fun tmaj =>
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ tmaj.getAppArgs.length = cnP ∧
        cvj.levelParams.length = ust.length ∧
        ConLeche.andRescueSlots env rl.ctor cnP = true then
      let fab := Expr.mkAppN (.const rl.ctor ust)
        (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major])
      if fab.wscopedB d && fab.looseBVarsBounded 0 &&
          fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) then
        (ConLeche.pureFns mode eager env F).inferIO d fab >>= fun tfab =>
        (ConLeche.pureFns mode eager env F).defeq d tmaj tfab >>= fun rd =>
        if rd then
          (if mode.verifiedChecks then
            ConLeche.proofIrrel (ConLeche.pureFns mode eager env F) d fab major
          else pure true) >>= fun r => if r then pure fab else pure major
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor — the prefix:
past it, the three branches. -/
theorem majorToCtorFueled_pre {F d : Nat} {cn : ConLeche.Name} {isK : Bool} {rl : RecRule}
    {x : Expr} {cvj cvT : ConstantVal} {cnP cnF : Nat} {T : ConLeche.Name}
    {lus : List Level} {caps : IndCaps}
    (hnc : ConLeche.isCtorApp env x = false)
    (hfj : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hpr : cvj.type.piResult.getAppFn = .const T lus)
    (hfT : env.find? T = some (.indInfo cvT caps)) :
    ConLeche.majorToCtorFueled mode eager env F d cn isK [rl] x =
      if isK = true then mtcK mode eager env F d rl cvj cnP T x
      else match ConLeche.etaRescueTable? (env.findTable? T) rl.ctor cvj cvT caps with
      | some tbl => mtcEta mode eager env F d cvT caps tbl T x
      | none => if T = ConLeche.andName then mtcAnd mode eager env F d rl cvj cnP T x
        else pure x := by
  simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc, hfj, hpr,
    hfT, Bool.false_eq_true, ite_false]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor — a constructor
application stays. -/
theorem majorToCtorFueled_ctor {F d : Nat} {cn : ConLeche.Name} {isK : Bool}
    {rules : List RecRule} {x : Expr} (h : ConLeche.isCtorApp env x = true) :
    ConLeche.majorToCtorFueled mode eager env F d cn isK rules x = .ok x := by
  simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, h, ite_true]; rfl

/-- con-leche: ConLeche/Kernel/Core.lean:782-834 prepareMajor — at a
K-flagged recursor whose rescue produced a constructor application: the
literal conversion of the rescued major. -/
theorem prepareMajorFueled_k {F d : Nat} {cn : ConLeche.Name}
    {isK : Bool} {rules' : List RecRule} {x m1 m3 : Expr}
    (hk : isK = true)
    (h1 : ConLeche.majorToCtorFueled mode eager env F d cn isK rules' x = .ok m1)
    (hc : ConLeche.isCtorApp env m1 = true)
    (h3 : ConLeche.litMajorToCtorFueled mode eager env F d m1 = .ok m3) :
    ConLeche.prepareMajorFueled mode eager env F d cn isK rules' x = .ok m3 := by
  subst hk
  have e1 : ConLeche.majorToCtor mode (ConLeche.pureFns mode eager env F) env d cn
      true rules' x = .ok m1 := h1
  have e3 : ConLeche.litMajorToCtor (ConLeche.pureFns mode eager env F) env d m1 =
      .ok m3 := h3
  simp only [ConLeche.prepareMajorFueled, ConLeche.prepareMajor, ite_true,
    e1, hc, e3, bind, Except.bind]

/-- con-leche: ConLeche/Kernel/Core.lean:782-834 prepareMajor — at a
K-flagged recursor whose rescue did not produce a constructor application:
the major as the rescue left it (con-leche task #334). -/
theorem prepareMajorFueled_kStuck {F d : Nat} {cn : ConLeche.Name}
    {isK : Bool} {rules' : List RecRule} {x m1 : Expr}
    (hk : isK = true)
    (h1 : ConLeche.majorToCtorFueled mode eager env F d cn isK rules' x = .ok m1)
    (hc : ConLeche.isCtorApp env m1 = false) :
    ConLeche.prepareMajorFueled mode eager env F d cn isK rules' x = .ok m1 := by
  subst hk
  have e1 : ConLeche.majorToCtor mode (ConLeche.pureFns mode eager env F) env d cn
      true rules' x = .ok m1 := h1
  simp only [ConLeche.prepareMajorFueled, ConLeche.prepareMajor, ite_true,
    e1, hc, Bool.false_eq_true, ite_false, bind, Except.bind]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:751-769 prepareMajor — elsewhere,
the structure rescues on the major AS FOUND (lean4#15351; a `String` literal
skips them) produced a constructor application: that is the major. -/
theorem prepareMajorFueled_nkCtor {F d : Nat} {cn : ConLeche.Name}
    {isK : Bool} {rules' : List RecRule} {x mE : Expr}
    (hk : isK = false)
    (h0 : (if x.isStrLit then .ok x
      else ConLeche.majorToCtorFueled mode eager env F d cn isK rules' x : CheckM Expr)
        = .ok mE)
    (hc : ConLeche.isCtorApp env mE = true) :
    ConLeche.prepareMajorFueled mode eager env F d cn isK rules' x = .ok mE := by
  subst hk
  simp only [ConLeche.prepareMajorFueled, ConLeche.prepareMajor,
    Bool.false_eq_true, ite_false]
  cases hs : x.isStrLit
  · simp only [hs, Bool.false_eq_true, ite_false] at h0
    have e0 : ConLeche.majorToCtor mode (ConLeche.pureFns mode eager env F) env d cn
        false rules' x = .ok mE := h0
    simp only [Bool.false_eq_true, ite_false, e0, hc, ite_true, bind,
      Except.bind]
    rfl
  · simp only [hs, ite_true] at h0
    cases h0
    simp only [ite_true, hc, bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:751-769 prepareMajor — elsewhere,
no constructor yet: `whnf`, the literal conversion, then the rescues once
more on the reduct. -/
theorem prepareMajorFueled_nk {F d : Nat} {cn : ConLeche.Name}
    {isK : Bool} {rules' : List RecRule} {x mE m1 m2 m3 : Expr}
    (hk : isK = false)
    (h0 : (if x.isStrLit then .ok x
      else ConLeche.majorToCtorFueled mode eager env F d cn isK rules' x : CheckM Expr)
        = .ok mE)
    (hc : ConLeche.isCtorApp env mE = false)
    (h1 : ConLeche.whnf mode eager env F d mE = .ok m1)
    (h2 : ConLeche.litMajorToCtorFueled mode eager env F d m1 = .ok m2)
    (h3 : ConLeche.majorToCtorFueled mode eager env F d cn isK rules' m2 = .ok m3) :
    ConLeche.prepareMajorFueled mode eager env F d cn isK rules' x = .ok m3 := by
  subst hk
  have e1 : (ConLeche.pureFns mode eager env F).whnf d mE = .ok m1 := h1
  have e2 : ConLeche.litMajorToCtor (ConLeche.pureFns mode eager env F) env d m1 =
      .ok m2 := h2
  have e3 : ConLeche.majorToCtor mode (ConLeche.pureFns mode eager env F) env d cn
      false rules' m2 = .ok m3 := h3
  simp only [ConLeche.prepareMajorFueled, ConLeche.prepareMajor,
    Bool.false_eq_true, ite_false]
  cases hs : x.isStrLit
  · simp only [hs, Bool.false_eq_true, ite_false] at h0
    have e0 : ConLeche.majorToCtor mode (ConLeche.pureFns mode eager env F) env d cn
        false rules' x = .ok mE := h0
    simp only [Bool.false_eq_true, ite_false, e0, hc, e1, e2, e3, bind,
      Except.bind]
  · simp only [hs, ite_true] at h0
    cases h0
    simp only [ite_true, hc, Bool.false_eq_true, ite_false, e1, e2, e3, bind,
      Except.bind, pure, Except.pure]

/-! ## `majorToCtor`: the arena's three rescue blocks as named programs -/

/-- the twin's K rescue block (`majorToCtor`'s `isK` arm) -/
@[expose] def majorKA (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (rl : IRecRule)
    (cvj : IConstantVal) (cnP : Nat) (T : NIdx) (major : EIdx) : AM EIdx := do
  let tmaj ← r.whnf depth (← r.inferIO depth major)
  let hh ← getAppFn coreWalkFuel tmaj
  if hh.tag == ETag.const then
    match ← view hh with
    | .const T' ust => do
      let ustl ← viewLs ust
      if T' = T ∧ cvj.levelParams.length = ustl.length then do
        let targs ← getAppArgs coreWalkFuel tmaj
        if cnP ≤ targs.length then do
          let hd ← internE (.const rl.ctor ust)
          let fab ← mkAppN hd (targs.take cnP)
          if ← fabScopeOk depth fab major then do
            if ← r.defeq depth tmaj (← r.inferIO depth fab) then do
              let irK ←
                if mode.verifiedChecks then ConRon.Arena.proofIrrel r fe depth fab major
                else pure true
              if irK then pure fab else pure major
            else pure major
          else pure major
        else pure major
      else pure major
    | _ => pure major
  else pure major

/-- the twin's η rescue block (`majorToCtor`'s `etaRescueTable?` arm) -/
@[expose] def majorEtaA (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (cvT : IConstantVal) (caps : IIndCaps)
    (tbl : IProjTable) (T : NIdx) (major : EIdx) : AM EIdx := do
  let tmaj ← r.whnf depth (← r.inferIO depth major)
  let hh ← getAppFn coreWalkFuel tmaj
  if hh.tag == ETag.const then
    match ← view hh with
    | .const T' ust => do
      let ustl ← viewLs ust
      let targs ← getAppArgs coreWalkFuel tmaj
      if T' = T ∧ targs.length = tbl.numParams ∧
          ustl.length = cvT.levelParams.length then do
        if ← formerNeverZeroAt r cvT caps ust then do
          let fabArgs ← etaFabArgsE T targs major tbl.numFields
          let hd ← internE (.const tbl.ctor ust)
          let fab ← mkAppN hd fabArgs
          if ← fabScopeOk depth fab major then pure fab
          else pure major
        else pure major
      else pure major
    | _ => pure major
  else pure major

/-- the twin's `And` rescue block (`majorToCtor`'s pinned-`And` arm) -/
@[expose] def majorAndA (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (rl : IRecRule)
    (cvj : IConstantVal) (cnP : Nat) (T : NIdx) (major : EIdx) : AM EIdx := do
  let tmaj ← r.whnf depth (← r.inferIO depth major)
  let hh ← getAppFn coreWalkFuel tmaj
  if hh.tag == ETag.const then
    match ← view hh with
    | .const T' ust => do
      match ← viewLsLen ust with
      | none => failDanglingLs
      | some ustl =>
      let targs ← getAppArgs coreWalkFuel tmaj
      let ars ← andRescueSlots fe rl.ctor cnP
      if T' = T ∧ targs.length = cnP ∧
          cvj.levelParams.length = ustl ∧ ars = true then do
        let p0 ← internE (.proj T 0 major)
        let p1 ← internE (.proj T 1 major)
        let fabArgs := targs ++ [p0, p1]
        let hd ← internE (.const rl.ctor ust)
        let fab ← mkAppN hd fabArgs
        if ← fabScopeOk depth fab major then do
          if ← r.defeq depth tmaj (← r.inferIO depth fab) then do
            let irA ←
              if mode.verifiedChecks then ConRon.Arena.proofIrrel r fe depth fab major
              else pure true
            if irA then pure fab else pure major
          else pure major
        else pure major
      else pure major
    | _ => pure major
  else pure major

/-- the twin's `majorToCtor` at a single rule, its three rescues named -/
theorem majorToCtor_one (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (c : NIdx) (isK : Bool) (rl : IRecRule) (major : EIdx) :
    ConRon.Arena.majorToCtor mode r fe depth c isK [rl] major = (do
      if ← isCtorApp fe major then pure major else
      match fe.find? rl.ctor with
      | some (.ctorInfo cvj cnP _cnF) => do
        let hh ← getAppFn coreWalkFuel (← piResult coreWalkFuel cvj.type)
        if hh.tag == ETag.const then
          match ← view hh with
          | .const T _ =>
            match fe.find? T with
            | some (.indInfo cvT caps) =>
              if isK = true then majorKA mode r fe depth rl cvj cnP T major
              else do
                match ← etaRescueTable? (fe.findTable? T) rl.ctor cvj cvT caps with
                | some tbl => majorEtaA r fe depth cvT caps tbl T major
                | none => do
                  let an ← pinAnd
                  if T = an then majorAndA mode r fe depth rl cvj cnP T major
                  else pure major
            | _ => pure major
          | _ => pure major
        else pure major
      | _ => pure major) := rfl

/-! ## The K rescue -/

/-- `mtcK` past its two knot calls, as a function of the head-normalised type -/
@[expose] def mtcKT (mode : CheckMode) (eager : Bool) (env : Env) (F d : Nat) (rl : RecRule)
    (cvj : ConstantVal) (cnP : Nat) (T : ConLeche.Name) (major tmaj : Expr) :
    CheckM Expr :=
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ cvj.levelParams.length = ust.length then
      if cnP ≤ tmaj.getAppArgs.length then
        let fab := Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)
        if fab.wscopedB d && fab.looseBVarsBounded 0 &&
            fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) then
          (ConLeche.pureFns mode eager env F).inferIO d fab >>= fun tfab =>
          (ConLeche.pureFns mode eager env F).defeq d tmaj tfab >>= fun rd =>
          if rd then
            (if mode.verifiedChecks then
              ConLeche.proofIrrel (ConLeche.pureFns mode eager env F) d fab major
            else pure true) >>= fun r => if r then pure fab else pure major
          else pure major
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the K branch: its two
knot calls, then `mtcKT`. -/
theorem mtcK_eq (mode : CheckMode) (eager : Bool) (env : Env) (F d : Nat) (rl : RecRule)
    (cvj : ConstantVal) (cnP : Nat) (T : ConLeche.Name) (major : Expr) :
    mtcK mode eager env F d rl cvj cnP T major =
      ((ConLeche.pureFns mode eager env F).inferIO d major >>= fun tm =>
       (ConLeche.pureFns mode eager env F).whnf d tm >>= fun tmaj =>
       mtcKT mode eager env F d rl cvj cnP T major tmaj) := rfl

/-- the K fabrication -/
def kFab (rl : RecRule) (cnP : Nat) (tmaj : Expr) : Expr :=
  Expr.mkAppN (.const rl.ctor (exprConstLevels tmaj.getAppFn)) (tmaj.getAppArgs.take cnP)

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the K branch, as a fuelled run. -/
def mtcKOp (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (rl : RecRule) (cvj : ConstantVal)
    (cnP : Nat) (T : ConLeche.Name) (x : Expr) : Nat → CheckM Expr :=
  fun F => mtcK mode eager env F d rl cvj cnP T x

/-- the run of `mtcK` through its prefix: the tail at one merged fuel -/
theorem mtcK_runs {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj v : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode eager env) d x tm)
    (h2 : RunE (ConLeche.whnf mode eager env) d tm tmaj)
    (h3 : ∃ F₀, ∀ F, F₀ ≤ F → mtcKT mode eager env F d rl cvj cnP T x tmaj = .ok v) :
    Runs (mtcKOp mode eager env d rl cvj cnP T x) v := by
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  obtain ⟨F3, hF3⟩ := h3
  refine ⟨max F1 (max F2 F3), ?_⟩
  have e1 : (ConLeche.pureFns mode eager env (max F1 (max F2 F3))).inferIO d x = .ok tm :=
    ConLeche.inferTypeIO_mono (by omega) hF1
  have e2 : (ConLeche.pureFns mode eager env (max F1 (max F2 F3))).whnf d tm = .ok tmaj :=
    ConLeche.whnf_mono (by omega) hF2
  simp only [mtcKOp, mtcK_eq, e1, e2, bind, Except.bind]
  exact hF3 _ (by omega)

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the K branch: the type's
head is not a constant. -/
theorem mtcK_nohead {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode eager env) d x tm)
    (h2 : RunE (ConLeche.whnf mode eager env) d tm tmaj)
    (hg : (exprTag tmaj.getAppFn == ETag.const) = false) :
    Runs (mtcKOp mode eager env d rl cvj cnP T x) x := by
  refine mtcK_runs h1 h2 ⟨0, fun F _ => ?_⟩
  unfold mtcKT
  generalize tmaj.getAppFn = g at hg ⊢
  cases g <;> first | rfl | (simp [exprTag] at hg)
grind_pattern [bridge_grind] mtcK_nohead =>
  mtcKOp mode eager env d rl cvj cnP T x, RunE (ConLeche.inferTypeIO mode eager env) d x tm,
    RunE (ConLeche.whnf mode eager env) d tm tmaj

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the K branch past a
constant head, its guards named. -/
theorem mtcKT_const {F d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tmaj : Expr}
    (hg : exprTag tmaj.getAppFn = ETag.const) :
    mtcKT mode eager env F d rl cvj cnP T x tmaj =
      if exprConstName tmaj.getAppFn = T ∧
          cvj.levelParams.length = (exprConstLevels tmaj.getAppFn).length then
        if cnP ≤ tmaj.getAppArgs.length then
          if scopeOkFn d (kFab rl cnP tmaj) x then
            (ConLeche.pureFns mode eager env F).inferIO d (kFab rl cnP tmaj) >>= fun tfab =>
            (ConLeche.pureFns mode eager env F).defeq d tmaj tfab >>= fun rd =>
            if rd then
              (if mode.verifiedChecks then
                ConLeche.proofIrrel (ConLeche.pureFns mode eager env F) d (kFab rl cnP tmaj) x
              else pure true) >>= fun r => if r then pure (kFab rl cnP tmaj) else pure x
            else pure x
          else pure x
        else pure x
      else pure x := by
  unfold mtcKT kFab scopeOkFn
  generalize tmaj.getAppFn = g at hg ⊢
  cases g <;> first | rfl | exact absurd hg (by simp only [exprTag]; decide)

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the K branch: a guard or
the scope check fails. -/
theorem mtcK_guard {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode eager env) d x tm)
    (h2 : RunE (ConLeche.whnf mode eager env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hc : ¬ (exprConstName tmaj.getAppFn = T ∧
          cvj.levelParams.length = (exprConstLevels tmaj.getAppFn).length ∧
          cnP ≤ tmaj.getAppArgs.length ∧ scopeOkFn d (kFab rl cnP tmaj) x = true)) :
    Runs (mtcKOp mode eager env d rl cvj cnP T x) x := by
  refine mtcK_runs h1 h2 ⟨0, fun F _ => ?_⟩
  rw [mtcKT_const hg]
  by_cases a : exprConstName tmaj.getAppFn = T ∧
      cvj.levelParams.length = (exprConstLevels tmaj.getAppFn).length
  · rw [ite_eq_left a]
    by_cases b : cnP ≤ tmaj.getAppArgs.length
    · rw [ite_eq_left b]
      have c : scopeOkFn d (kFab rl cnP tmaj) x = false := by
        cases h : scopeOkFn d (kFab rl cnP tmaj) x
        · rfl
        · exact absurd ⟨a.1, a.2, b, h⟩ hc
      rw [c]; rfl
    · rw [ite_eq_right b]; rfl
  · rw [ite_eq_right a]; rfl
grind_pattern [bridge_grind] mtcK_guard =>
  mtcKOp mode eager env d rl cvj cnP T x, RunE (ConLeche.inferTypeIO mode eager env) d x tm,
    RunE (ConLeche.whnf mode eager env) d tm tmaj

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the K branch past its
guards, as a function of the two verdicts. -/
theorem mtcK_fireR {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj tf : Expr} {b5 b6 : Bool}
    (h1 : RunE (ConLeche.inferTypeIO .verified eager env) d x tm)
    (h2 : RunE (ConLeche.whnf .verified eager env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hc : exprConstName tmaj.getAppFn = T ∧
          cvj.levelParams.length = (exprConstLevels tmaj.getAppFn).length ∧
          cnP ≤ tmaj.getAppArgs.length ∧ scopeOkFn d (kFab rl cnP tmaj) x = true)
    (h4 : RunE (ConLeche.inferTypeIO .verified eager env) d (kFab rl cnP tmaj) tf)
    (h5 : SimV (ConLeche.isDefEqCore .verified eager env) d tmaj tf b5)
    (h6 : b5 = true → PIrrelE .verified eager env d (kFab rl cnP tmaj) x b6) :
    Runs (mtcKOp .verified eager env d rl cvj cnP T x) (if b5 && b6 then kFab rl cnP tmaj else x) := by
  obtain ⟨F4, hF4⟩ := h4
  obtain ⟨F5, hF5⟩ := h5
  have h6' : ∃ F6, b5 = true →
      ConLeche.proofIrrelFueled .verified eager env F6 d (kFab rl cnP tmaj) x = .ok b6 := by
    cases b5
    · exact ⟨0, nofun⟩
    · obtain ⟨F6, hF6⟩ := h6 rfl; exact ⟨F6, fun _ => hF6⟩
  obtain ⟨F6, hF6⟩ := h6'
  refine mtcK_runs h1 h2 ⟨max F4 (max F5 F6), fun F hF => ?_⟩
  obtain ⟨ha, hb, hb', hs⟩ := hc
  rw [mtcKT_const hg, ite_eq_left ⟨ha, hb⟩, ite_eq_left hb', ite_eq_left hs]
  have e4 : (ConLeche.pureFns .verified eager env F).inferIO d (kFab rl cnP tmaj) = .ok tf :=
    ConLeche.inferTypeIO_mono (by omega) hF4
  have e5 : (ConLeche.pureFns .verified eager env F).defeq d tmaj tf = .ok b5 :=
    ConLeche.isDefEqCore_mono (by omega) hF5
  simp only [e4, e5, bind, Except.bind]
  cases b5
  · rfl
  · have e6 : ConLeche.proofIrrel (ConLeche.pureFns .verified eager env F) d (kFab rl cnP tmaj) x = .ok b6 :=
      proofIrrelFueled_mono (by omega) (hF6 rfl)
    simp only [ite_true, CheckMode.verifiedChecks, e6]
    cases b6 <;> rfl

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the K branch: the
fabrication's type is not the major's. -/
theorem mtcK_df {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj tf : Expr}
    (h1 : RunE (ConLeche.inferTypeIO .verified eager env) d x tm)
    (h2 : RunE (ConLeche.whnf .verified eager env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hc : exprConstName tmaj.getAppFn = T ∧
          cvj.levelParams.length = (exprConstLevels tmaj.getAppFn).length ∧
          cnP ≤ tmaj.getAppArgs.length ∧ scopeOkFn d (kFab rl cnP tmaj) x = true)
    (h4 : RunE (ConLeche.inferTypeIO .verified eager env) d (kFab rl cnP tmaj) tf)
    (h5 : SimV (ConLeche.isDefEqCore .verified eager env) d tmaj tf false) :
    Runs (mtcKOp .verified eager env d rl cvj cnP T x) x :=
  mtcK_fireR (b6 := false) h1 h2 hg hc h4 h5 nofun
grind_pattern [bridge_grind] mtcK_df =>
  mtcKOp .verified eager env d rl cvj cnP T x, RunE (ConLeche.whnf .verified eager env) d tm tmaj,
    SimV (ConLeche.isDefEqCore .verified eager env) d tmaj tf false

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the K branch: the type
check passed, proof irrelevance decides. -/
theorem mtcK_pi {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj tf : Expr} {b6 : Bool}
    (h1 : RunE (ConLeche.inferTypeIO .verified eager env) d x tm)
    (h2 : RunE (ConLeche.whnf .verified eager env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hc : exprConstName tmaj.getAppFn = T ∧
          cvj.levelParams.length = (exprConstLevels tmaj.getAppFn).length ∧
          cnP ≤ tmaj.getAppArgs.length ∧ scopeOkFn d (kFab rl cnP tmaj) x = true)
    (h4 : RunE (ConLeche.inferTypeIO .verified eager env) d (kFab rl cnP tmaj) tf)
    (h5 : SimV (ConLeche.isDefEqCore .verified eager env) d tmaj tf true)
    (h6 : PIrrelE .verified eager env d (kFab rl cnP tmaj) x b6) :
    Runs (mtcKOp .verified eager env d rl cvj cnP T x) (if b6 then kFab rl cnP tmaj else x) := by
  have := mtcK_fireR (b5 := true) h1 h2 hg hc h4 h5 (fun _ => h6)
  simpa using this
grind_pattern [bridge_grind] mtcK_pi =>
  mtcKOp .verified eager env d rl cvj cnP T x, RunE (ConLeche.whnf .verified eager env) d tm tmaj,
    SimV (ConLeche.isDefEqCore .verified eager env) d tmaj tf true,
    PIrrelE .verified eager env d (kFab rl cnP tmaj) x b6

/-- con-leche: ConLeche/Kernel/Core.lean:571-617 majorToCtor — **the K rescue**
(`to_cnstr_when_K`): the parameters-only constructor application fabricated
from the major's type, certified by the type check and, at the verified mode,
proof irrelevance.  The answer arrives through the twelve states of the
block, each a transport step for the denotations it carries, hence
`gen := 16`. -/
theorem majorK_spec {fuel : Nat}
    (hsim : KnotSpec eager env fe fuel)
    (s₁ : AState) (d : Nat) (rl : IRecRule) (rl' : RecRule) (major : EIdx)
    (x : Expr) (icvj : IConstantVal) (dcvj : ConstantVal) (cnP : Nat)
    (T : NIdx) (Tn : ConLeche.Name)
    (hok : CheckOK eager env fe s₁) (hrl' : Frontend.denoteRule s₁.store rl = some rl')
    (hmaj : denoteE s₁.store major = some x) (hw : Expr.WScoped d x)
    (hdcvj : Frontend.denoteCV s₁.store icvj = some dcvj)
    (hT : denoteN s₁.store.ns T = some Tn) :
    ⦃fun s => s = s₁⦄
      majorKA .verified (coreKnot .verified eager fe id fuel) fe d rl icvj cnP T major
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₁.store s'.store ∧
        s'.pins = s₁.pins ∧
        SimEOp (mtcKOp .verified eager env d rl' dcvj cnP Tn x) d s'.store r; ⊤⦄ := by
  have hrc := (rule_denote hrl').2.1
  sym (gen := 16) only [bridge_grind, kFab, ← viewOK_const, CheckMode.verifiedChecks] =>
    vcgen [majorKA, hsim.inferIOS, hsim.whnfS, ExprOps.getAppFn_spec, ExprOps.getAppArgs_spec,
      internE_specC (eager := eager) (env := env) (fe := fe),
      mkAppN_specC (eager := eager) (env := env) (fe := fe),
      fabScopeOk_specS (eager := eager) (env := env) (fe := fe), hsim.defeqS,
      proofIrrel_specA hsim] <;> finish

/-! ## The η rescue -/

/-- con-leche: ConLeche/Kernel/Core.lean:612-700 majorToCtor — the η branch past its two
knot calls. -/
@[expose] def mtcEtaT (mode : CheckMode) (eager : Bool) (env : Env) (F d : Nat) (cvT : ConstantVal)
    (caps : IndCaps) (tbl : ProjTable) (T : ConLeche.Name) (major tmaj : Expr) : CheckM Expr :=
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ tmaj.getAppArgs.length = tbl.numParams ∧
        ust.length = cvT.levelParams.length then
      formerNeverZeroAt (ConLeche.pureFns mode eager env F).whnf cvT caps ust >>= fun nz =>
      if nz then
        let fab := Expr.mkAppN (.const tbl.ctor ust)
          (ConLeche.etaFabArgsE T tmaj.getAppArgs major tbl.numFields)
        if fab.wscopedB d && fab.looseBVarsBounded 0 &&
            fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) then
          pure fab
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- con-leche: ConLeche/Kernel/Core.lean:612-700 majorToCtor — the η branch: its two
knot calls, then `mtcEtaT`. -/
theorem mtcEta_eq (mode : CheckMode) (eager : Bool) (env : Env) (F d : Nat) (cvT : ConstantVal)
    (caps : IndCaps) (tbl : ProjTable) (T : ConLeche.Name) (major : Expr) :
    mtcEta mode eager env F d cvT caps tbl T major =
      ((ConLeche.pureFns mode eager env F).inferIO d major >>= fun tm =>
       (ConLeche.pureFns mode eager env F).whnf d tm >>= fun tmaj =>
       mtcEtaT mode eager env F d cvT caps tbl T major tmaj) := rfl

/-- the η fabrication: the table's constructor at the major type's levels -/
def etaFab (tbl : ProjTable) (T : ConLeche.Name) (x tmaj : Expr) : Expr :=
  Expr.mkAppN (.const tbl.ctor (exprConstLevels tmaj.getAppFn))
    (ConLeche.etaFabArgsE T tmaj.getAppArgs x tbl.numFields)

/-- the η rescue's syntactic guards, at the head-normalised type -/
def etaGuardOk (cvT : ConstantVal) (tbl : ProjTable) (T : ConLeche.Name)
    (tmaj : Expr) : Bool :=
  exprConstName tmaj.getAppFn == T && tmaj.getAppArgs.length == tbl.numParams &&
    (exprConstLevels tmaj.getAppFn).length == cvT.levelParams.length

/-- con-leche: ConLeche/Kernel/Core.lean:612-700 majorToCtor — the η branch, as a fuelled run. -/
def mtcEtaOp (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (cvT : ConstantVal) (caps : IndCaps)
    (tbl : ProjTable) (T : ConLeche.Name) (x : Expr) : Nat → CheckM Expr :=
  fun F => mtcEta mode eager env F d cvT caps tbl T x

/-- con-leche: ConLeche/Kernel/Core.lean:612-700 majorToCtor — the η branch through its
prefix: the tail at one merged fuel. -/
theorem mtcEta_runs {d : Nat} {cvT : ConstantVal} {caps : IndCaps} {tbl : ProjTable}
    {T : ConLeche.Name} {x tm tmaj v : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode eager env) d x tm)
    (h2 : RunE (ConLeche.whnf mode eager env) d tm tmaj)
    (h3 : ∃ F₀, ∀ F, F₀ ≤ F → mtcEtaT mode eager env F d cvT caps tbl T x tmaj = .ok v) :
    Runs (mtcEtaOp mode eager env d cvT caps tbl T x) v := by
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  obtain ⟨F3, hF3⟩ := h3
  refine ⟨max F1 (max F2 F3), ?_⟩
  have e1 : (ConLeche.pureFns mode eager env (max F1 (max F2 F3))).inferIO d x = .ok tm :=
    ConLeche.inferTypeIO_mono (by omega) hF1
  have e2 : (ConLeche.pureFns mode eager env (max F1 (max F2 F3))).whnf d tm = .ok tmaj :=
    ConLeche.whnf_mono (by omega) hF2
  simp only [mtcEtaOp, mtcEta_eq, e1, e2, bind, Except.bind]
  exact hF3 _ (by omega)

/-- con-leche: ConLeche/Kernel/Core.lean:612-700 majorToCtor — the η branch past a
constant head, its guards named. -/
theorem mtcEtaT_const {F d : Nat} {cvT : ConstantVal} {caps : IndCaps} {tbl : ProjTable}
    {T : ConLeche.Name} {x tmaj : Expr} (hg : exprTag tmaj.getAppFn = ETag.const) :
    mtcEtaT mode eager env F d cvT caps tbl T x tmaj =
      if etaGuardOk cvT tbl T tmaj then
        formerNeverZeroAt (ConLeche.pureFns mode eager env F).whnf cvT caps
            (exprConstLevels tmaj.getAppFn) >>= fun nz =>
        if nz then
          (if scopeOkFn d (etaFab tbl T x tmaj) x then pure (etaFab tbl T x tmaj) else pure x)
        else pure x
      else pure x := by
  unfold mtcEtaT etaGuardOk etaFab scopeOkFn
  generalize tmaj.getAppFn = g at hg ⊢
  cases g <;> first
    | exact absurd hg (by simp only [exprTag]; decide)
    | skip
  rename_i T' ust
  simp only [exprConstName, exprConstLevels]
  by_cases h1 : T' = T ∧ tmaj.getAppArgs.length = tbl.numParams ∧
      ust.length = cvT.levelParams.length
  · rw [ite_eq_left h1]
    obtain ⟨a, b, c⟩ := h1
    subst a
    simp only [beq_self_eq_true, b, c, Bool.true_and, ite_true]
  · rw [ite_eq_right h1]
    have hb : (T' == T && tmaj.getAppArgs.length == tbl.numParams &&
        ust.length == cvT.levelParams.length) = false :=
      Bool.eq_false_iff.mpr fun h => h1 (by
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact ⟨h.1.1, h.1.2, h.2⟩)
    simp only [hb, Bool.false_eq_true, ite_false]

/-- con-leche: ConLeche/Kernel/Core.lean:612-700 majorToCtor — the η branch, no constant
head: the major stays. -/
theorem mtcEta_nohead {d : Nat} {cvT : ConstantVal} {caps : IndCaps} {tbl : ProjTable}
    {T : ConLeche.Name} {x tm tmaj : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode eager env) d x tm)
    (h2 : RunE (ConLeche.whnf mode eager env) d tm tmaj)
    (hg : (exprTag tmaj.getAppFn == ETag.const) = false) :
    Runs (mtcEtaOp mode eager env d cvT caps tbl T x) x := by
  refine mtcEta_runs h1 h2 ⟨0, fun F _ => ?_⟩
  unfold mtcEtaT
  generalize tmaj.getAppFn = g at hg ⊢
  cases g <;> first | rfl | (simp [exprTag] at hg)
grind_pattern [bridge_grind] mtcEta_nohead =>
  mtcEtaOp mode eager env d cvT caps tbl T x, RunE (ConLeche.inferTypeIO mode eager env) d x tm,
    RunE (ConLeche.whnf mode eager env) d tm tmaj

/-- con-leche: ConLeche/Kernel/Core.lean:612-700 majorToCtor — the η branch, a guard
fails: the major stays. -/
theorem mtcEta_guard {d : Nat} {cvT : ConstantVal} {caps : IndCaps} {tbl : ProjTable}
    {T : ConLeche.Name} {x tm tmaj : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode eager env) d x tm)
    (h2 : RunE (ConLeche.whnf mode eager env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hn : etaGuardOk cvT tbl T tmaj = false) :
    Runs (mtcEtaOp mode eager env d cvT caps tbl T x) x := by
  refine mtcEta_runs h1 h2 ⟨0, fun F _ => ?_⟩
  rw [mtcEtaT_const hg, hn]; rfl
grind_pattern [bridge_grind] mtcEta_guard =>
  mtcEtaOp mode eager env d cvT caps tbl T x, RunE (ConLeche.inferTypeIO mode eager env) d x tm,
    RunE (ConLeche.whnf mode eager env) d tm tmaj

/-- con-leche: ConLeche/Kernel/Core.lean:612-700 majorToCtor — the η branch past its
guards: the never-zero test decides, then the scope check. -/
theorem mtcEta_nz {d : Nat} {cvT : ConstantVal} {caps : IndCaps} {tbl : ProjTable}
    {T : ConLeche.Name} {x tm tmaj : Expr} {b : Bool}
    (h1 : RunE (ConLeche.inferTypeIO .verified eager env) d x tm)
    (h2 : RunE (ConLeche.whnf .verified eager env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hc : etaGuardOk cvT tbl T tmaj = true)
    (hb : NZ eager env cvT caps (exprConstLevels tmaj.getAppFn) b) :
    Runs (mtcEtaOp .verified eager env d cvT caps tbl T x)
      (if b && scopeOkFn d (etaFab tbl T x tmaj) x then etaFab tbl T x tmaj else x) := by
  obtain ⟨F3, hF3⟩ := hb
  refine mtcEta_runs h1 h2 ⟨F3, fun F hF => ?_⟩
  rw [mtcEtaT_const hg, hc]
  simp only [ite_true, formerNeverZeroAtFueled_mono hF hF3, bind, Except.bind]
  cases b <;> cases scopeOkFn d (etaFab tbl T x tmaj) x <;> rfl
grind_pattern [bridge_grind] mtcEta_nz =>
  mtcEtaOp .verified eager env d cvT caps tbl T x, RunE (ConLeche.whnf .verified eager env) d tm tmaj,
    NZ eager env cvT caps (exprConstLevels tmaj.getAppFn) b

/-- con-leche's η spine arguments at a fixed family, major and field count -/
def etaArgsFn (T : ConLeche.Name) (x : Expr) (nF : Nat) (ts : List Expr) : List Expr :=
  ConLeche.etaFabArgsE T ts x nF

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:739-743 etaFabArgsE — `etaFabArgsE_spec` at
whatever the type's arguments denote. -/
theorem etaFabArgsE_specS (s₀ : AState) (T : NIdx) (targs : List EIdx) (major : EIdx) (nF : Nat)
    (Tn : ConLeche.Name) (x : Expr)
    (hok : CheckOK eager env fe s₀) (hT : denoteN s₀.store.ns T = some Tn)
    (hts : (Frontend.denoteEList s₀.store targs).isSome = true)
    (hx : denoteE s₀.store major = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.etaFabArgsE T targs major nF
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        MapRel (etaArgsFn Tn x nF) (Frontend.denoteEList s₀.store targs)
          (Frontend.denoteEList s'.store r); ⊤⦄ := by
  obtain ⟨ts, h1⟩ := Option.isSome_iff_exists.mp hts
  rw [h1]
  exact etaFabArgsE_spec s₀ T targs major nF Tn ts x hok hT h1 hx

section EtaExt

/-! The family record and its capabilities are read at the block's first state
and handed to the never-zero test at its tenth: their denotations transport. -/

/-- con-leche: none — `denoteCV_ext` as an equation. -/
theorem denoteCV_ext_eq {st st' : EStore} {cv : IConstantVal} (hx : Ext st st')
    (h : (Frontend.denoteCV st cv).isSome = true) :
    Frontend.denoteCV st' cv = Frontend.denoteCV st cv := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  rw [hc, denoteCV_ext hc hx]
local grind_pattern [bridge_grind] denoteCV_ext_eq => Frontend.denoteCV st cv, Ext st st'

/-- con-leche: none — `denoteCaps_ext` as an equation. -/
theorem denoteCaps_ext_eq {st st' : EStore} {c : IIndCaps} (hx : Ext st st')
    (h : (Frontend.denoteCaps st c).isSome = true) :
    Frontend.denoteCaps st' c = Frontend.denoteCaps st c := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h
  rw [hd, denoteCaps_ext hd hx]
local grind_pattern [bridge_grind] denoteCaps_ext_eq => Frontend.denoteCaps st c, Ext st st'

/-- con-leche: ConLeche/Kernel/Core.lean:612-700 majorToCtor — **the η rescue**
(`to_cnstr_when_structure`): the never-zero test at the use's levels
(`formerNeverZeroAt`, a knot walk), at a closed stored family; the constructor
and the counts are the family's projection table's.  The answer arrives through
the twelve states of the block, each a transport step for the denotations it
carries, hence `gen := 16`. -/
theorem majorEta_spec {fuel : Nat}
    (hsim : KnotSpec eager env fe fuel)
    (s₁ : AState) (d : Nat) (major : EIdx) (x : Expr)
    (icvT : IConstantVal) (dcvT : ConstantVal) (icaps : IIndCaps)
    (dcaps : IndCaps) (itbl : IProjTable) (dtbl : ProjTable) (T : NIdx) (Tn : ConLeche.Name)
    (hok : CheckOK eager env fe s₁)
    (hmaj : denoteE s₁.store major = some x) (hw : Expr.WScoped d x)
    (hdcvT : Frontend.denoteCV s₁.store icvT = some dcvT)
    (hcaps : Frontend.denoteCaps s₁.store icaps = some dcaps)
    (htbl : Frontend.denoteProjTable s₁.store itbl = some dtbl)
    (hT : denoteN s₁.store.ns T = some Tn) (hcl : dcvT.type.hasFvar = false) :
    ⦃fun s => s = s₁⦄
      majorEtaA (coreKnot .verified eager fe id fuel) fe d icvT icaps itbl T major
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₁.store s'.store ∧
        s'.pins = s₁.pins ∧
        SimEOp (mtcEtaOp .verified eager env d dcvT dcaps dtbl Tn x) d s'.store r; ⊤⦄ := by
  obtain ⟨hnF, hnP⟩ := denoteProjTable_fields htbl
  have hctor := denoteProjTable_ctor htbl
  sym (gen := 16) only [bridge_grind, etaFab, etaGuardOk, etaArgsFn, ← viewOK_const] =>
    vcgen [majorEtaA, hsim.inferIOS, hsim.whnfS, ExprOps.getAppFn_spec, ExprOps.getAppArgs_spec,
      formerNeverZeroAt_specA hsim (cvTP := dcvT) (capsP := dcaps),
      etaFabArgsE_specS (eager := eager) (env := env) (fe := fe) (Tn := Tn) (x := x),
      internE_specC (eager := eager) (env := env) (fe := fe),
      mkAppN_specC (eager := eager) (env := env) (fe := fe),
      fabScopeOk_specS (eager := eager) (env := env) (fe := fe)] <;> finish

/-- con-leche: none — the η rescue's answer at the twin table's optional
denotation (the answer shape `majorToCtor_spec`'s `grind` reads). -/
@[expose] def EtaAns (eager : Bool) (env : Env) (d : Nat) (cvT : ConstantVal) (caps : IndCaps)
    (T : ConLeche.Name) (x : Expr) (st : EStore) (r : EIdx) : Option ProjTable → Prop
  | some tbl => SimEOp (mtcEtaOp .verified eager env d cvT caps tbl T x) d st r
  | none => True

/-- con-leche: none — `EtaAns` at a denoting table. -/
@[bridge_grind =] theorem EtaAns.some_eq (d : Nat) (cvT : ConstantVal) (caps : IndCaps)
    (T : ConLeche.Name) (x : Expr) (st : EStore) (r : EIdx) (tbl : ProjTable) :
    EtaAns eager env d cvT caps T x st r (some tbl) =
      SimEOp (mtcEtaOp .verified eager env d cvT caps tbl T x) d st r := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:612-700 majorToCtor — `majorEta_spec` at the
twin table's denotation. -/
theorem majorEta_specA {fuel : Nat}
    (hsim : KnotSpec eager env fe fuel)
    (s₁ : AState) (d : Nat) (major : EIdx) (x : Expr)
    (icvT : IConstantVal) (dcvT : ConstantVal) (icaps : IIndCaps)
    (dcaps : IndCaps) (itbl : IProjTable) (T : NIdx) (Tn : ConLeche.Name)
    (hok : CheckOK eager env fe s₁)
    (hmaj : denoteE s₁.store major = some x) (hw : Expr.WScoped d x)
    (hdcvT : Frontend.denoteCV s₁.store icvT = some dcvT)
    (hcaps : Frontend.denoteCaps s₁.store icaps = some dcaps)
    (htbl : (Frontend.denoteProjTable s₁.store itbl).isSome = true)
    (hT : denoteN s₁.store.ns T = some Tn) (hcl : dcvT.type.hasFvar = false) :
    ⦃fun s => s = s₁⦄
      majorEtaA (coreKnot .verified eager fe id fuel) fe d icvT icaps itbl T major
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₁.store s'.store ∧
        s'.pins = s₁.pins ∧
        EtaAns eager env d dcvT dcaps Tn x s'.store r
          (Frontend.denoteProjTable s₁.store itbl); ⊤⦄ := by
  obtain ⟨dtbl, hd⟩ := Option.isSome_iff_exists.mp htbl
  rw [hd]
  exact majorEta_spec hsim s₁ d major x icvT dcvT icaps dcaps itbl dtbl T Tn hok hmaj hw
    hdcvT hcaps hd hT hcl

end EtaExt

/-! ## The `And` rescue -/

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the `And` branch past its
two knot calls. -/
@[expose] def mtcAndT (mode : CheckMode) (eager : Bool) (env : Env) (F d : Nat) (rl : RecRule)
    (cvj : ConstantVal) (cnP : Nat) (T : ConLeche.Name) (major tmaj : Expr) :
    CheckM Expr :=
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ tmaj.getAppArgs.length = cnP ∧
        cvj.levelParams.length = ust.length ∧
        ConLeche.andRescueSlots env rl.ctor cnP = true then
      let fab := Expr.mkAppN (.const rl.ctor ust)
        (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major])
      if fab.wscopedB d && fab.looseBVarsBounded 0 &&
          fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) then
        (ConLeche.pureFns mode eager env F).inferIO d fab >>= fun tfab =>
        (ConLeche.pureFns mode eager env F).defeq d tmaj tfab >>= fun rd =>
        if rd then
          (if mode.verifiedChecks then
            ConLeche.proofIrrel (ConLeche.pureFns mode eager env F) d fab major
          else pure true) >>= fun r => if r then pure fab else pure major
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the `And` branch: its two
knot calls, then `mtcAndT`. -/
theorem mtcAnd_eq (mode : CheckMode) (eager : Bool) (env : Env) (F d : Nat) (rl : RecRule)
    (cvj : ConstantVal) (cnP : Nat) (T : ConLeche.Name) (major : Expr) :
    mtcAnd mode eager env F d rl cvj cnP T major =
      ((ConLeche.pureFns mode eager env F).inferIO d major >>= fun tm =>
       (ConLeche.pureFns mode eager env F).whnf d tm >>= fun tmaj =>
       mtcAndT mode eager env F d rl cvj cnP T major tmaj) := rfl

/-- the `And` fabrication -/
def andFab (rl : RecRule) (T : ConLeche.Name) (x tmaj : Expr) : Expr :=
  Expr.mkAppN (.const rl.ctor (exprConstLevels tmaj.getAppFn))
    (tmaj.getAppArgs ++ [.proj T 0 x, .proj T 1 x])

/-- the `And` rescue's syntactic guards and scope check -/
def andRescueOk (env : Env) (d : Nat) (rl : RecRule) (cvj : ConstantVal) (cnP : Nat)
    (T : ConLeche.Name) (x tmaj : Expr) : Bool :=
  exprConstName tmaj.getAppFn == T && tmaj.getAppArgs.length == cnP &&
    cvj.levelParams.length == (exprConstLevels tmaj.getAppFn).length &&
    ConLeche.andRescueSlots env rl.ctor cnP &&
    scopeOkFn d (andFab rl T x tmaj) x

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the `And` branch, as a
fuelled run. -/
def mtcAndOp (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (rl : RecRule) (cvj : ConstantVal)
    (cnP : Nat) (T : ConLeche.Name) (x : Expr) : Nat → CheckM Expr :=
  fun F => mtcAnd mode eager env F d rl cvj cnP T x

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the `And` branch through
its prefix: the tail at one merged fuel. -/
theorem mtcAnd_runs {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj v : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode eager env) d x tm)
    (h2 : RunE (ConLeche.whnf mode eager env) d tm tmaj)
    (h3 : ∃ F₀, ∀ F, F₀ ≤ F → mtcAndT mode eager env F d rl cvj cnP T x tmaj = .ok v) :
    Runs (mtcAndOp mode eager env d rl cvj cnP T x) v := by
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  obtain ⟨F3, hF3⟩ := h3
  refine ⟨max F1 (max F2 F3), ?_⟩
  have e1 : (ConLeche.pureFns mode eager env (max F1 (max F2 F3))).inferIO d x = .ok tm :=
    ConLeche.inferTypeIO_mono (by omega) hF1
  have e2 : (ConLeche.pureFns mode eager env (max F1 (max F2 F3))).whnf d tm = .ok tmaj :=
    ConLeche.whnf_mono (by omega) hF2
  simp only [mtcAndOp, mtcAnd_eq, e1, e2, bind, Except.bind]
  exact hF3 _ (by omega)

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the `And` branch past a
constant head, its guards named. -/
theorem mtcAndT_const {F d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tmaj : Expr}
    (hg : exprTag tmaj.getAppFn = ETag.const) :
    mtcAndT mode eager env F d rl cvj cnP T x tmaj =
      if andRescueOk env d rl cvj cnP T x tmaj then
        (ConLeche.pureFns mode eager env F).inferIO d (andFab rl T x tmaj) >>= fun tfab =>
        (ConLeche.pureFns mode eager env F).defeq d tmaj tfab >>= fun rd =>
        if rd then
          (if mode.verifiedChecks then
            ConLeche.proofIrrel (ConLeche.pureFns mode eager env F) d (andFab rl T x tmaj) x
          else pure true) >>= fun r => if r then pure (andFab rl T x tmaj) else pure x
        else pure x
      else pure x := by
  unfold mtcAndT andRescueOk andFab scopeOkFn
  generalize tmaj.getAppFn = g at hg ⊢
  cases g <;> first
    | exact absurd hg (by simp only [exprTag]; decide)
    | skip
  rename_i T' ust
  simp only [exprConstName, exprConstLevels]
  by_cases h1 : T' = T ∧ tmaj.getAppArgs.length = cnP ∧ cvj.levelParams.length = ust.length ∧
      ConLeche.andRescueSlots env rl.ctor cnP = true
  · rw [ite_eq_left h1]
    obtain ⟨a, b, c, e⟩ := h1
    subst a b
    simp only [beq_self_eq_true, c, e, Bool.true_and]
  · rw [ite_eq_right h1]
    have hb : (T' == T && tmaj.getAppArgs.length == cnP &&
        cvj.levelParams.length == ust.length &&
        ConLeche.andRescueSlots env rl.ctor cnP) = false :=
      Bool.eq_false_iff.mpr fun h => h1 (by
        simp only [Bool.and_eq_true, beq_iff_eq] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩)
    simp only [hb, Bool.false_and, Bool.false_eq_true, ite_false]

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the `And` branch: the
type's head is not a constant. -/
theorem mtcAnd_nohead {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode eager env) d x tm)
    (h2 : RunE (ConLeche.whnf mode eager env) d tm tmaj)
    (hg : (exprTag tmaj.getAppFn == ETag.const) = false) :
    Runs (mtcAndOp mode eager env d rl cvj cnP T x) x := by
  refine mtcAnd_runs h1 h2 ⟨0, fun F _ => ?_⟩
  unfold mtcAndT
  generalize tmaj.getAppFn = g at hg ⊢
  cases g <;> first | rfl | (simp [exprTag] at hg)
grind_pattern [bridge_grind] mtcAnd_nohead =>
  mtcAndOp mode eager env d rl cvj cnP T x, RunE (ConLeche.inferTypeIO mode eager env) d x tm,
    RunE (ConLeche.whnf mode eager env) d tm tmaj

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the `And` branch: a guard
or the scope check fails. -/
theorem mtcAnd_guard {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj : Expr}
    (h1 : RunE (ConLeche.inferTypeIO mode eager env) d x tm)
    (h2 : RunE (ConLeche.whnf mode eager env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hc : andRescueOk env d rl cvj cnP T x tmaj = false) :
    Runs (mtcAndOp mode eager env d rl cvj cnP T x) x := by
  refine mtcAnd_runs h1 h2 ⟨0, fun F _ => ?_⟩
  rw [mtcAndT_const hg, hc]; rfl
grind_pattern [bridge_grind] mtcAnd_guard =>
  mtcAndOp mode eager env d rl cvj cnP T x, RunE (ConLeche.inferTypeIO mode eager env) d x tm,
    RunE (ConLeche.whnf mode eager env) d tm tmaj

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the `And` branch past its
guards, as a function of the two verdicts. -/
theorem mtcAnd_fireR {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj tf : Expr} {b5 b6 : Bool}
    (h1 : RunE (ConLeche.inferTypeIO .verified eager env) d x tm)
    (h2 : RunE (ConLeche.whnf .verified eager env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hc : andRescueOk env d rl cvj cnP T x tmaj = true)
    (h4 : RunE (ConLeche.inferTypeIO .verified eager env) d (andFab rl T x tmaj) tf)
    (h5 : SimV (ConLeche.isDefEqCore .verified eager env) d tmaj tf b5)
    (h6 : b5 = true → PIrrelE .verified eager env d (andFab rl T x tmaj) x b6) :
    Runs (mtcAndOp .verified eager env d rl cvj cnP T x) (if b5 && b6 then andFab rl T x tmaj else x) := by
  obtain ⟨F4, hF4⟩ := h4
  obtain ⟨F5, hF5⟩ := h5
  have h6' : ∃ F6, b5 = true →
      ConLeche.proofIrrelFueled .verified eager env F6 d (andFab rl T x tmaj) x = .ok b6 := by
    cases b5
    · exact ⟨0, nofun⟩
    · obtain ⟨F6, hF6⟩ := h6 rfl; exact ⟨F6, fun _ => hF6⟩
  obtain ⟨F6, hF6⟩ := h6'
  refine mtcAnd_runs h1 h2 ⟨max F4 (max F5 F6), fun F hF => ?_⟩
  rw [mtcAndT_const hg, hc]
  have e4 : (ConLeche.pureFns .verified eager env F).inferIO d (andFab rl T x tmaj) = .ok tf :=
    ConLeche.inferTypeIO_mono (by omega) hF4
  have e5 : (ConLeche.pureFns .verified eager env F).defeq d tmaj tf = .ok b5 :=
    ConLeche.isDefEqCore_mono (by omega) hF5
  simp only [e4, e5, bind, Except.bind, ite_true]
  cases b5
  · rfl
  · have e6 : ConLeche.proofIrrel (ConLeche.pureFns .verified eager env F) d (andFab rl T x tmaj) x =
        .ok b6 := proofIrrelFueled_mono (by omega) (hF6 rfl)
    simp only [ite_true, CheckMode.verifiedChecks, e6]
    cases b6 <;> rfl

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the `And` branch: the
fabrication's type is not the major's. -/
theorem mtcAnd_df {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj tf : Expr}
    (h1 : RunE (ConLeche.inferTypeIO .verified eager env) d x tm)
    (h2 : RunE (ConLeche.whnf .verified eager env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hc : andRescueOk env d rl cvj cnP T x tmaj = true)
    (h4 : RunE (ConLeche.inferTypeIO .verified eager env) d (andFab rl T x tmaj) tf)
    (h5 : SimV (ConLeche.isDefEqCore .verified eager env) d tmaj tf false) :
    Runs (mtcAndOp .verified eager env d rl cvj cnP T x) x :=
  mtcAnd_fireR (b6 := false) h1 h2 hg hc h4 h5 nofun
grind_pattern [bridge_grind] mtcAnd_df =>
  mtcAndOp .verified eager env d rl cvj cnP T x, RunE (ConLeche.whnf .verified eager env) d tm tmaj,
    SimV (ConLeche.isDefEqCore .verified eager env) d tmaj tf false

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the `And` branch: the
type check passed, proof irrelevance decides. -/
theorem mtcAnd_pi {d : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat}
    {T : ConLeche.Name} {x tm tmaj tf : Expr} {b6 : Bool}
    (h1 : RunE (ConLeche.inferTypeIO .verified eager env) d x tm)
    (h2 : RunE (ConLeche.whnf .verified eager env) d tm tmaj)
    (hg : exprTag tmaj.getAppFn = ETag.const)
    (hc : andRescueOk env d rl cvj cnP T x tmaj = true)
    (h4 : RunE (ConLeche.inferTypeIO .verified eager env) d (andFab rl T x tmaj) tf)
    (h5 : SimV (ConLeche.isDefEqCore .verified eager env) d tmaj tf true)
    (h6 : PIrrelE .verified eager env d (andFab rl T x tmaj) x b6) :
    Runs (mtcAndOp .verified eager env d rl cvj cnP T x) (if b6 then andFab rl T x tmaj else x) := by
  have := mtcAnd_fireR (b5 := true) h1 h2 hg hc h4 h5 (fun _ => h6)
  simpa using this
grind_pattern [bridge_grind] mtcAnd_pi =>
  mtcAndOp .verified eager env d rl cvj cnP T x, RunE (ConLeche.whnf .verified eager env) d tm tmaj,
    SimV (ConLeche.isDefEqCore .verified eager env) d tmaj tf true,
    PIrrelE .verified eager env d (andFab rl T x tmaj) x b6

/-- con-leche: ConLeche/Kernel/Core.lean:659-721 majorToCtor — **the pinned `And`
rescue**, certified the K branch's way. Sixteen states, hence `gen := 16`.
`opt2_isSome_of_eq_some` is erased here: the fabrication's denotation is an
`opt2` chain (`Expr.const`, the `++`, the two `List.cons` cells) restated at each
later state, so the rule fires on every cell at every state and each `isSome` it
derives opens a fresh witness (`denote_some_of_isSome`,
`denoteEList_some_of_isSome`) for a denotation the callees' posts already name;
it proves nothing this walk needs and makes its search 2.5× as expensive. -/
theorem majorAnd_spec {fuel : Nat}
    (hsim : KnotSpec eager env fe fuel)
    (s₁ : AState) (d : Nat) (rl : IRecRule) (rl' : RecRule) (major : EIdx)
    (x : Expr) (icvj : IConstantVal) (dcvj : ConstantVal) (cnP : Nat)
    (T : NIdx) (Tn : ConLeche.Name)
    (hok : CheckOK eager env fe s₁) (hrl' : Frontend.denoteRule s₁.store rl = some rl')
    (hmaj : denoteE s₁.store major = some x) (hw : Expr.WScoped d x)
    (hdcvj : Frontend.denoteCV s₁.store icvj = some dcvj)
    (hT : denoteN s₁.store.ns T = some Tn) :
    ⦃fun s => s = s₁⦄
      majorAndA .verified (coreKnot .verified eager fe id fuel) fe d rl icvj cnP T major
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₁.store s'.store ∧
        s'.pins = s₁.pins ∧
        SimEOp (mtcAndOp .verified eager env d rl' dcvj cnP Tn x) d s'.store r; ⊤⦄ := by
  have hrc := (rule_denote hrl').2.1
  sym (gen := 16) only [bridge_grind, -opt2_isSome_of_eq_some, andFab, andRescueOk, CheckMode.verifiedChecks,
      denoteEList_append_eq, ← viewOK_const] =>
    vcgen [majorAndA, hsim.inferIOS, hsim.whnfS, ExprOps.getAppFn_spec, ExprOps.getAppArgs_spec,
      andRescueSlots_spec (eager := eager) (env := env) (fe := fe) (cn := rl'.ctor),
      internE_specC (eager := eager) (env := env) (fe := fe),
      mkAppN_specC (eager := eager) (env := env) (fe := fe),
      fabScopeOk_specS (eager := eager) (env := env) (fe := fe), hsim.defeqS,
      proofIrrel_specA hsim] <;> finish

/-! ## `litMajorToCtor` -/

/-- the twin's `litMajorToCtor` with its literal match one constructor deep -/
theorem litMajorToCtor_split (r : CoreFnsA) (d : Nat) (h : EIdx) :
    ConRon.Arena.litMajorToCtor r fe d h =
      (if h.tag == ETag.lit then do
        let v ← view h
        if (litStr? (nodeLit v)).isSome && v.tagOf == ETag.lit then do
          if ← strLitStored fe then do
            let c ← strLitToConstructor ((litStr? (nodeLit v)).getD "")
            r.whnf d c
          else pure h
        else litToCtorIfNat fe h
      else litToCtorIfNat fe h) := by
  unfold ConRon.Arena.litMajorToCtor
  split
  · congr 1; funext v
    cases v <;> try rfl
    rename_i l; cases l <;> rfl
  · rfl

/-- con-leche: ConLeche/Kernel/Core.lean:728-740 litMajorToCtor — as a fuelled run. -/
def litMajorOp (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (x : Expr) : Nat → CheckM Expr :=
  fun F => ConLeche.litMajorToCtorFueled mode eager env F d x

/-- con-leche: ConLeche/Kernel/Core.lean:728-740 litMajorToCtor — every major but a
string literal takes the `Nat` conversion. -/
theorem litMajor_nstr {d : Nat} {x : Expr} (h : x.isStrLit = false) :
    Runs (litMajorOp mode eager env d x) (ConLeche.litToCtorIfNat env x) :=
  ⟨0, litMajorToCtorFueled_nstr (fun s hs => by subst hs; cases h)⟩
grind_pattern [bridge_grind] litMajor_nstr => litMajorOp mode eager env d x

/-- con-leche: ConLeche/Kernel/Core.lean:728-740 litMajorToCtor — an unsupported string
literal stays. -/
theorem litMajor_unsup {d : Nat} {x : Expr} (h : x.isStrLit = true)
    (hs : ConLeche.strLitStored env = false) : Runs (litMajorOp mode eager env d x) x := by
  refine ⟨0, ?_⟩
  cases x with
  | lit l => cases l with
    | strVal s => simp [litMajorOp, ConLeche.litMajorToCtorFueled, ConLeche.litMajorToCtor, hs]; rfl
    | natVal => cases h
  | _ => cases h
grind_pattern [bridge_grind] litMajor_unsup => litMajorOp mode eager env d x

/-- con-leche: ConLeche/Kernel/Core.lean:728-740 litMajorToCtor — a supported string
literal, reduced. -/
theorem litMajor_str {d : Nat} {x v : Expr} (h : x.isStrLit = true)
    (hs : ConLeche.strLitStored env = true)
    (hw : RunE (ConLeche.whnf mode eager env) d
      (ConLeche.strLitToConstructor ((litStr? (exprLit x)).getD "")) v) :
    Runs (litMajorOp mode eager env d x) v := by
  obtain ⟨F, hF⟩ := hw
  refine ⟨F, ?_⟩
  cases x with
  | lit l => cases l with
    | strVal s =>
      simp only [litMajorOp, ConLeche.litMajorToCtorFueled, ConLeche.litMajorToCtor, hs, ite_true]
      exact hF
    | natVal => cases h
  | _ => cases h
grind_pattern [bridge_grind] litMajor_str =>
  litMajorOp mode eager env d x,
  RunE (ConLeche.whnf mode eager env) d (ConLeche.strLitToConstructor ((litStr? (exprLit x)).getD "")) v

/-- con-leche: ConLeche/Kernel/Core.lean:728-740 litMajorToCtor — **THEOREM 1 for
`litMajorToCtor`**: a `Nat` literal one layer, a supported `String` literal to its
reduced constructor form. -/
theorem litMajorToCtor_spec {fuel : Nat} (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (d : Nat) (h : EIdx) (x : Expr)
    (hok : CheckOK eager env fe s₀) (hden : denoteE s₀.store h = some x)
    (hw : Expr.WScoped d x) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.litMajorToCtor (coreKnot .verified eager fe id fuel) fe d h
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ SimEOp (litMajorOp .verified eager env d x) d s'.store r; ⊤⦄ := by
  sym only [bridge_grind, isStrLit_eq, Option.getD_some, ConLeche.litToCtorIfNat_WScoped] =>
    vcgen [litMajorToCtor_split, strLitStored_spec (eager := eager) (env := env) (fe := fe),
      strLitToConstructor_spec (eager := eager) (env := env) (fe := fe), hsim.whnfS,
      litToCtorIfNat_spec (x := x)] <;> finish

/-! ## `majorToCtor`'s pure side -/

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — as a fuelled run. -/
def majorToCtorOp (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (cn : ConLeche.Name)
    (isK : Bool) (rules : List RecRule) (x : Expr) : Nat → CheckM Expr :=
  fun F => ConLeche.majorToCtorFueled mode eager env F d cn isK rules x

/-- the constructor's family name, read off its stored type -/
def mtcFam (env : Env) (rl : RecRule) : ConLeche.Name :=
  exprConstName (cCtorVal (env.find? rl.ctor)).type.piResult.getAppFn

/-- the η rescue's table: the family's projection table, if the rule's
constructor is its η constructor (`etaRescueTable?`) -/
def mtcTbl (env : Env) (rl : RecRule) : Option ProjTable :=
  ConLeche.etaRescueTable? (env.findTable? (mtcFam env rl)) rl.ctor (cCtorVal (env.find? rl.ctor))
    (cIndVal (env.find? (mtcFam env rl))) (cIndCaps (env.find? (mtcFam env rl)))

/-- the prefix every rescue shares: a stored constructor whose type ends in
a stored inductive -/
def mtcPrefixOk (env : Env) (rl : RecRule) : Bool :=
  cCtor? (env.find? rl.ctor) &&
    exprTag (cCtorVal (env.find? rl.ctor)).type.piResult.getAppFn == ETag.const &&
    cInd? (env.find? (mtcFam env rl))

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — at a single rule that is
not a constructor application, the prefix and the three branches as one equation over
the lookups' projections. -/
theorem majorToCtorFueled_one {F d : Nat} {cn : ConLeche.Name} {isK : Bool} {rl : RecRule} {x : Expr}
    (hnc : ConLeche.isCtorApp env x = false) :
    ConLeche.majorToCtorFueled mode eager env F d cn isK [rl] x =
      if mtcPrefixOk env rl then
        if isK = true then
          mtcK mode eager env F d rl (cCtorVal (env.find? rl.ctor)) (cCtorNP (env.find? rl.ctor))
            (mtcFam env rl) x
        else match mtcTbl env rl with
        | some tbl =>
          mtcEta mode eager env F d (cIndVal (env.find? (mtcFam env rl)))
            (cIndCaps (env.find? (mtcFam env rl))) tbl (mtcFam env rl) x
        | none =>
          if mtcFam env rl = ConLeche.andName then
            mtcAnd mode eager env F d rl (cCtorVal (env.find? rl.ctor)) (cCtorNP (env.find? rl.ctor))
              (mtcFam env rl) x
          else .ok x
      else .ok x := by
  unfold mtcPrefixOk mtcTbl mtcFam
  cases hf : env.find? rl.ctor with
  | none =>
    simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc, hf, cCtor?,
      Bool.false_eq_true, ite_false, Bool.false_and]; rfl
  | some ci =>
    cases ci with
    | ctorInfo cvj cnP cnF =>
      simp only [cCtor?, cCtorVal, cCtorNP, Bool.true_and]
      generalize hg : cvj.type.piResult.getAppFn = g
      cases g with
      | const T us =>
        simp only [exprTag, exprConstName, beq_self_eq_true, Bool.true_and]
        cases hT : env.find? T with
        | none =>
          simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc, hf, hg, hT, cInd?,
            Bool.false_eq_true, ite_false]; rfl
        | some ti =>
          cases ti with
          | indInfo cvT caps =>
            have := majorToCtorFueled_pre (F := F) (d := d) (cn := cn) (isK := isK) (mode := mode) (eager := eager) hnc hf hg hT
            simp only [cInd?, cIndVal, cIndCaps, ite_true]
            rw [this]; rfl
          | _ =>
            simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc, hf, hg, hT, cInd?,
              Bool.false_eq_true, ite_false]; rfl
      | _ =>
        simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc, hf, hg]
        first | rfl | (simp only [exprTag]; rfl)
    | _ =>
      simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, hnc, hf, cCtor?,
        Bool.false_eq_true, ite_false, Bool.false_and]; rfl

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — a constructor application stays. -/
theorem mtc_isCtor {d : Nat} {cn : ConLeche.Name} {isK : Bool} {rules : List RecRule} {x : Expr}
    (h : ConLeche.isCtorApp env x = true) : Runs (majorToCtorOp mode eager env d cn isK rules x) x :=
  ⟨0, majorToCtorFueled_ctor (mode := mode) (eager := eager) (cn := cn) (rules := rules) (d := d) h⟩
grind_pattern [bridge_grind] mtc_isCtor => majorToCtorOp mode eager env d cn isK rules x

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — no rule: the major stays. -/
theorem mtc_nil {d : Nat} {cn : ConLeche.Name} {isK : Bool} {x : Expr}
    (h : ConLeche.isCtorApp env x = false) : Runs (majorToCtorOp mode eager env d cn isK [] x) x :=
  ⟨0, by
    show ConLeche.majorToCtorFueled mode eager env 0 d cn isK [] x = .ok x
    simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, h, Bool.false_eq_true,
      ite_false]; rfl⟩
grind_pattern [bridge_grind] mtc_nil => majorToCtorOp mode eager env d cn isK [] x

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — several rules: the major stays. -/
theorem mtc_many {d : Nat} {cn : ConLeche.Name} {isK : Bool} {a b : RecRule} {cs : List RecRule} {x : Expr}
    (h : ConLeche.isCtorApp env x = false) :
    Runs (majorToCtorOp mode eager env d cn isK (a :: b :: cs) x) x :=
  ⟨0, by
    show ConLeche.majorToCtorFueled mode eager env 0 d cn isK (a :: b :: cs) x = .ok x
    simp only [ConLeche.majorToCtorFueled, ConLeche.majorToCtor, h, Bool.false_eq_true,
      ite_false]; rfl⟩
grind_pattern [bridge_grind] mtc_many => majorToCtorOp mode eager env d cn isK (a :: b :: cs) x

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the prefix fails: the major stays. -/
theorem mtc_skip {d : Nat} {cn : ConLeche.Name} {isK : Bool} {rl : RecRule} {x : Expr}
    (h : ConLeche.isCtorApp env x = false) (hp : mtcPrefixOk env rl = false) :
    Runs (majorToCtorOp mode eager env d cn isK [rl] x) x :=
  ⟨0, by simp only [majorToCtorOp, majorToCtorFueled_one h, hp, Bool.false_eq_true, ite_false]⟩
grind_pattern [bridge_grind] mtc_skip => majorToCtorOp mode eager env d cn isK [rl] x

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — the K rescue's answer. -/
theorem mtc_K {d : Nat} {cn : ConLeche.Name} {isK : Bool} {rl : RecRule} {x v : Expr}
    (h : ConLeche.isCtorApp env x = false) (hp : mtcPrefixOk env rl = true) (hk : isK = true)
    (H : Runs (mtcKOp mode eager env d rl (cCtorVal (env.find? rl.ctor)) (cCtorNP (env.find? rl.ctor))
      (mtcFam env rl) x) v) :
    Runs (majorToCtorOp mode eager env d cn isK [rl] x) v :=
  let ⟨F, hF⟩ := H
  ⟨F, by simp only [majorToCtorOp, majorToCtorFueled_one h, hp, hk, ite_true]; exact hF⟩
grind_pattern [bridge_grind] mtc_K => majorToCtorOp mode eager env d cn isK [rl] x,
  Runs (mtcKOp mode eager env d rl (cCtorVal (env.find? rl.ctor)) (cCtorNP (env.find? rl.ctor))
      (mtcFam env rl) x) v

/-- con-leche: ConLeche/Kernel/Core.lean:612-700 majorToCtor — the η rescue's answer. -/
theorem mtc_Eta {d : Nat} {cn : ConLeche.Name} {isK : Bool} {rl : RecRule} {x v : Expr}
    {tbl : ProjTable}
    (h : ConLeche.isCtorApp env x = false) (hp : mtcPrefixOk env rl = true) (hk : isK = false)
    (he : mtcTbl env rl = some tbl)
    (H : Runs (mtcEtaOp mode eager env d (cIndVal (env.find? (mtcFam env rl)))
      (cIndCaps (env.find? (mtcFam env rl))) tbl (mtcFam env rl) x) v) :
    Runs (majorToCtorOp mode eager env d cn isK [rl] x) v :=
  let ⟨F, hF⟩ := H
  ⟨F, by simp only [majorToCtorOp, majorToCtorFueled_one h, hp, hk, he, ite_true,
    Bool.false_eq_true, ite_false]; exact hF⟩
grind_pattern [bridge_grind] mtc_Eta => majorToCtorOp mode eager env d cn isK [rl] x,
  Runs (mtcEtaOp mode eager env d (cIndVal (env.find? (mtcFam env rl)))
      (cIndCaps (env.find? (mtcFam env rl))) tbl (mtcFam env rl) x) v

/-- con-leche: ConLeche/Kernel/Core.lean:612-700 majorToCtor — the `And` rescue's answer. -/
theorem mtc_And {d : Nat} {cn : ConLeche.Name} {isK : Bool} {rl : RecRule} {x v : Expr}
    (h : ConLeche.isCtorApp env x = false) (hp : mtcPrefixOk env rl = true) (hk : isK = false)
    (he : mtcTbl env rl = none) (hT : mtcFam env rl = ConLeche.andName)
    (H : Runs (mtcAndOp mode eager env d rl (cCtorVal (env.find? rl.ctor)) (cCtorNP (env.find? rl.ctor))
      (mtcFam env rl) x) v) :
    Runs (majorToCtorOp mode eager env d cn isK [rl] x) v :=
  let ⟨F, hF⟩ := H
  ⟨F, by simp only [majorToCtorOp, majorToCtorFueled_one h, hp, hk, he, ite_true,
    Bool.false_eq_true, ite_false]; rw [ite_eq_left hT]; exact hF⟩
grind_pattern [bridge_grind] mtc_And => majorToCtorOp mode eager env d cn isK [rl] x,
  Runs (mtcAndOp mode eager env d rl (cCtorVal (env.find? rl.ctor)) (cCtorNP (env.find? rl.ctor))
      (mtcFam env rl) x) v

/-- con-leche: ConLeche/Kernel/Core.lean:612-700 majorToCtor — no rescue applies: the
major stays. -/
theorem mtc_none {d : Nat} {cn : ConLeche.Name} {isK : Bool} {rl : RecRule} {x : Expr}
    (h : ConLeche.isCtorApp env x = false) (hp : mtcPrefixOk env rl = true) (hk : isK = false)
    (he : mtcTbl env rl = none) (hT : ¬ mtcFam env rl = ConLeche.andName) :
    Runs (majorToCtorOp mode eager env d cn isK [rl] x) x :=
  ⟨0, by simp only [majorToCtorOp, majorToCtorFueled_one h, hp, hk, he, ite_true,
    Bool.false_eq_true, ite_false]; rw [ite_eq_right hT]⟩
grind_pattern [bridge_grind] mtc_none => majorToCtorOp mode eager env d cn isK [rl] x

/-- con-leche: ConLeche/Kernel/FEnv.lean:248-254 findTable? — the table lookups,
side by side, as `TblAns` (`findTable?_at`). -/
theorem findTable?_tblAns {s : AState} {T : NIdx} {Tn : ConLeche.Name}
    (hck : CheckOK eager env fe s) (hT : denoteN s.store.ns T = some Tn) :
    TblAns s.store (fe.findTable? T) (env.findTable? Tn) := by
  obtain ⟨hhit, hmiss⟩ := findTable?_at hck hT
  cases h : fe.findTable? T with
  | none => rw [hmiss h]; trivial
  | some t =>
    obtain ⟨pt, hpt, he, -⟩ := hhit t h
    rw [he]; exact hpt
grind_pattern [bridge_grind] findTable?_tblAns =>
  CheckOK eager env fe s, TblAns s.store (fe.findTable? T) (env.findTable? Tn) where
  guard denoteN s.store.ns T = some Tn

/-- con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor — **THEOREM 1 for
`majorToCtor`**: K, η and the pinned `And`.  The rule list is split structurally; at a
single rule the twin's three blocks are the named `majorKA`/`majorEtaA`/`majorAndA`
(`majorToCtor_one`), the global projection equations with a wildcard arm are erased
(each one a case split) for the per-constructor ones, and the rescues' answers arrive
through ten states, hence `gen := 10`. -/
theorem majorToCtor_spec {fuel : Nat}
    (hsim : KnotSpec eager env fe fuel) (henv : EnvWF env)
    (s₀ : AState) (d : Nat) (c : NIdx) (isK : Bool) (rules : List IRecRule) (major : EIdx)
    (cn : ConLeche.Name) (rules' : List RecRule) (x : Expr)
    (hok : CheckOK eager env fe s₀)
    (hr : Frontend.denoteRules s₀.store rules = some rules')
    (hden : denoteE s₀.store major = some x) (hw : Expr.WScoped d x) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.majorToCtor .verified (coreKnot .verified eager fe id fuel) fe d c isK rules major
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ SimEOp (majorToCtorOp .verified eager env d cn isK rules' x) d s'.store r; ⊤⦄ := by
  match rules, rules', hr with
  | [], rules', hr =>
    obtain rfl : rules' = [] := by simpa [Frontend.denoteRules] using hr.symm
    sym only [bridge_grind] =>
      vcgen [ConRon.Arena.majorToCtor, isCtorApp_spec (eager := eager) (env := env) (x := x)] <;> finish
  | [rl], rules', hr =>
    obtain ⟨rl', hrl', rfl⟩ : ∃ rl', Frontend.denoteRule s₀.store rl = some rl' ∧
        rules' = [rl'] := by
      simp only [Frontend.denoteRules] at hr
      split at hr
      · rename_i y ys hy hys
        simp only [Option.some.injEq] at hys
        subst hys
        cases hr
        exact ⟨y, hy, rfl⟩
      · simp at hr
    obtain ⟨_, hrlc, _, _⟩ := rule_denote hrl'
    have hcl := indVal_closed henv (mtcFam env rl')
    sym (gen := 10) only [bridge_grind, mtcPrefixOk, mtcFam, mtcTbl] =>
      vcgen [majorToCtor_one, isCtorApp_spec (eager := eager) (env := env) (x := x), ExprOps.piResult_spec,
        ExprOps.getAppFn_spec, ConRon.Arena.pinAnd, pinAt_specE,
        etaRescueTable?_spec (eager := eager) (env := env) (fe := fe) (cn := rl'.ctor)
          (tblP? := env.findTable? (mtcFam env rl'))
          (cvjP := cCtorVal (env.find? rl'.ctor)) (cvTP := cIndVal (env.find? (mtcFam env rl')))
          (capsP := cIndCaps (env.find? (mtcFam env rl'))),
        majorK_spec hsim (rl' := rl') (x := x) (dcvj := cCtorVal (env.find? rl'.ctor))
          (Tn := mtcFam env rl'),
        majorEta_specA hsim (x := x) (dcvT := cIndVal (env.find? (mtcFam env rl')))
          (dcaps := cIndCaps (env.find? (mtcFam env rl'))) (Tn := mtcFam env rl'),
        majorAnd_spec hsim (rl' := rl') (x := x) (dcvj := cCtorVal (env.find? rl'.ctor))
          (Tn := mtcFam env rl')] <;> finish
  | r1 :: r2 :: rs, rules', hr =>
    obtain ⟨a, b, cs, rfl⟩ : ∃ a b cs, rules' = a :: b :: cs := by
      have hl := denoteRules_len hr
      match rules', hl with
      | a :: b :: cs, _ => exact ⟨a, b, cs, rfl⟩
    sym only [bridge_grind] =>
      vcgen [ConRon.Arena.majorToCtor, isCtorApp_spec (eager := eager) (env := env) (x := x)] <;> finish

/-! ## `isStrLit` -/

/-- the twin's `isStrLit` with its literal match one constructor deep -/
theorem isStrLit_split (h : EIdx) :
    ConRon.Arena.isStrLit h =
      (if h.tag == ETag.lit then do
        match ← viewLit h with
        | none => failDanglingE
        | some l => pure (litStr? l).isSome
      else pure false) := by
  unfold ConRon.Arena.isStrLit
  split
  · congr 1; funext o
    cases o with
    | none => rfl
    | some l => cases l <;> rfl
  · rfl

/-- con-leche: ConLeche/Kernel/Core.lean:687-691 Expr.isStrLit — **THEOREM 1 for the
twin's `isStrLit`**: a read-only test that agrees with the denotation's. -/
theorem isStrLit_spec (s₀ : AState) (h : EIdx) (x : Expr)
    (hok : CheckOK eager env fe s₀) (hden : denoteE s₀.store h = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.isStrLit h
    ⦃fun b s' => s' = s₀ ∧ b = x.isStrLit; ⊤⦄ := by
  sym only [bridge_grind, isStrLit_eq] =>
    vcgen [isStrLit_split, ConRon.Arena.viewLit] <;> finish

/-! ## `prepareMajor` -/

/-- `majorToCtor`'s answer at an optional subject -/
@[expose] def MtcAns (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (cn : ConLeche.Name)
    (isK : Bool) (rules : List RecRule)
    (st : EStore) (r : EIdx) : Option Expr → Prop
  | some x => SimEOp (majorToCtorOp mode eager env d cn isK rules x) d st r
  | none => True

/-- con-leche: none — `MtcAns` at a denoting subject. -/
@[bridge_grind =] theorem MtcAns.some_eq (d : Nat) (cn : ConLeche.Name) (isK : Bool) (rules : List RecRule)
    (st : EStore) (r : EIdx) (x : Expr) :
    MtcAns mode eager env d cn isK rules st r (some x) = SimEOp (majorToCtorOp mode eager env d cn isK rules x) d st r :=
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:513-662 majorToCtor — `majorToCtor_spec` in
answer shape. -/
theorem majorToCtor_specS {fuel : Nat}
    (hsim : KnotSpec eager env fe fuel) (henv : EnvWF env)
    (s₀ : AState) (d : Nat) (c : NIdx) (isK : Bool) (rules : List IRecRule) (major : EIdx)
    (cn : ConLeche.Name) (rules' : List RecRule)
    (hok : CheckOK eager env fe s₀)
    (hr : Frontend.denoteRules s₀.store rules = some rules')
    (hw : DenWS d (denoteE s₀.store major)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.majorToCtor .verified (coreKnot .verified eager fe id fuel) fe d c isK rules major
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ MtcAns .verified eager env d cn isK rules' s'.store r (denoteE s₀.store major); ⊤⦄ := by
  cases hd : denoteE s₀.store major with
  | none => rw [hd] at hw; exact hw.elim
  | some x =>
    rw [hd] at hw
    exact majorToCtor_spec hsim henv s₀ d c isK rules major cn rules' x hok hr hd hw

/-- `litMajorToCtor`'s answer at an optional subject -/
@[expose] def LitAns (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (st : EStore) (r : EIdx) :
    Option Expr → Prop
  | some x => SimEOp (litMajorOp mode eager env d x) d st r
  | none => True

/-- con-leche: none — `LitAns` at a denoting subject. -/
@[bridge_grind =] theorem LitAns.some_eq (d : Nat) (st : EStore) (r : EIdx) (x : Expr) :
    LitAns mode eager env d st r (some x) = SimEOp (litMajorOp mode eager env d x) d st r := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:728-740 litMajorToCtor — `litMajorToCtor_spec`
in answer shape. -/
theorem litMajorToCtor_specS {fuel : Nat} (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (d : Nat) (h : EIdx) (hok : CheckOK eager env fe s₀)
    (hw : DenWS d (denoteE s₀.store h)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.litMajorToCtor (coreKnot .verified eager fe id fuel) fe d h
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ LitAns .verified eager env d s'.store r (denoteE s₀.store h); ⊤⦄ := by
  cases hd : denoteE s₀.store h with
  | none => rw [hd] at hw; exact hw.elim
  | some x =>
    rw [hd] at hw
    exact litMajorToCtor_spec hsim s₀ d h x hok hd hw

/-- con-leche: ConLeche/Kernel/CoreDefs.lean isCtorApp — `isCtorApp_spec` at whatever
the handle denotes. -/
theorem isCtorApp_specS (s₀ : AState) (a : EIdx) (hok : CheckOK eager env fe s₀)
    (hda : (denoteE s₀.store a).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.isCtorApp fe a
    ⦃fun r s' => s' = s₀ ∧ MapRelV (ConLeche.isCtorApp env) (denoteE s₀.store a) r; ⊤⦄ := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hda
  rw [hx]
  exact isCtorApp_spec s₀ a x hok hx

/-- con-leche: ConLeche/Kernel/Core.lean:751-834 prepareMajor — as a fuelled run. -/
@[expose] def prepOp (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (cn : ConLeche.Name)
    (isK : Bool) (rules : List RecRule)
    (x : Expr) : Nat → CheckM Expr :=
  fun F => ConLeche.prepareMajorFueled mode eager env F d cn isK rules x

/-- con-leche: ConLeche/Kernel/Core.lean:751-834 prepareMajor — K: the rescue produced a
constructor application, its literal converted. -/
theorem prep_k {d : Nat} {cn : ConLeche.Name} {isK : Bool} {rules : List RecRule} {x m1 m3 : Expr}
    (hk : isK = true)
    (h1 : Runs (majorToCtorOp mode eager env d cn isK rules x) m1)
    (hc : ConLeche.isCtorApp env m1 = true) (h3 : Runs (litMajorOp mode eager env d m1) m3) :
    Runs (prepOp mode eager env d cn isK rules x) m3 :=
  let ⟨F1, hF1⟩ := h1
  let ⟨F3, hF3⟩ := h3
  ⟨max F1 F3, prepareMajorFueled_k hk (majorToCtorFueled_mono (Nat.le_max_left _ _) hF1) hc
    (litMajorToCtorFueled_mono (Nat.le_max_right _ _) hF3)⟩
grind_pattern [bridge_grind] prep_k => prepOp mode eager env d cn isK rules x,
  Runs (majorToCtorOp mode eager env d cn isK rules x) m1, Runs (litMajorOp mode eager env d m1) m3

/-- con-leche: ConLeche/Kernel/Core.lean:751-834 prepareMajor — K: the rescue produced
no constructor application. -/
theorem prep_kStuck {d : Nat} {cn : ConLeche.Name} {isK : Bool} {rules : List RecRule} {x m1 : Expr}
    (hk : isK = true)
    (h1 : Runs (majorToCtorOp mode eager env d cn isK rules x) m1)
    (hc : ConLeche.isCtorApp env m1 = false) :
    Runs (prepOp mode eager env d cn isK rules x) m1 :=
  let ⟨F1, hF1⟩ := h1
  ⟨F1, prepareMajorFueled_kStuck hk hF1 hc⟩
grind_pattern [bridge_grind] prep_kStuck => prepOp mode eager env d cn isK rules x,
  Runs (majorToCtorOp mode eager env d cn isK rules x) m1

/-- the major as the structure rescues on it as found leave it (a `String`
literal skips them) -/
def PrepE (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (cn : ConLeche.Name)
    (isK : Bool) (rules : List RecRule)
    (x mE : Expr) : Prop :=
  ∃ F, (if x.isStrLit then .ok x
    else ConLeche.majorToCtorFueled mode eager env F d cn isK rules x : CheckM Expr) = .ok mE

/-- con-leche: ConLeche/Kernel/Core.lean:751-834 prepareMajor — a `String` literal skips
the first rescue attempt. -/
theorem prepE_str {d : Nat} {cn : ConLeche.Name} {isK : Bool} {rules : List RecRule} {x : Expr}
    (h : x.isStrLit = true) : PrepE mode eager env d cn isK rules x x := ⟨0, by simp [h]⟩
grind_pattern [bridge_grind] prepE_str => prepOp mode eager env d cn isK rules x

/-- con-leche: ConLeche/Kernel/Core.lean:751-834 prepareMajor — elsewhere the first
rescue attempt runs on the major as found. -/
theorem prepE_mtc {d : Nat} {cn : ConLeche.Name} {isK : Bool} {rules : List RecRule} {x mE : Expr}
    (h : x.isStrLit = false) (h1 : Runs (majorToCtorOp mode eager env d cn isK rules x) mE) :
    PrepE mode eager env d cn isK rules x mE :=
  let ⟨F, hF⟩ := h1
  ⟨F, by simp only [h, Bool.false_eq_true, ite_false]; exact hF⟩
grind_pattern [bridge_grind] prepE_mtc => prepOp mode eager env d cn isK rules x,
  Runs (majorToCtorOp mode eager env d cn isK rules x) mE

/-- con-leche: ConLeche/Kernel/Core.lean:751-834 prepareMajor — elsewhere: the first
attempt produced a constructor application. -/
theorem prep_nkCtor {d : Nat} {cn : ConLeche.Name} {isK : Bool} {rules : List RecRule} {x mE : Expr}
    (hk : isK = false) (hE : PrepE mode eager env d cn isK rules x mE)
    (hc : ConLeche.isCtorApp env mE = true) :
    Runs (prepOp mode eager env d cn isK rules x) mE :=
  let ⟨F, hF⟩ := hE
  ⟨F, prepareMajorFueled_nkCtor hk hF hc⟩
grind_pattern [bridge_grind] prep_nkCtor => prepOp mode eager env d cn isK rules x, PrepE mode eager env d cn isK rules x mE

/-- con-leche: ConLeche/Kernel/Core.lean:751-834 prepareMajor — elsewhere: `whnf`, the
literal conversion and the rescues once more. -/
theorem prep_nk {d : Nat} {cn : ConLeche.Name} {isK : Bool} {rules : List RecRule} {x mE m1 m2 m3 : Expr}
    (hk : isK = false) (hE : PrepE mode eager env d cn isK rules x mE)
    (hc : ConLeche.isCtorApp env mE = false)
    (h1 : RunE (ConLeche.whnf mode eager env) d mE m1)
    (h2 : Runs (litMajorOp mode eager env d m1) m2)
    (h3 : Runs (majorToCtorOp mode eager env d cn isK rules m2) m3) :
    Runs (prepOp mode eager env d cn isK rules x) m3 := by
  obtain ⟨F0, hF0⟩ := hE
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  obtain ⟨F3, hF3⟩ := h3
  refine ⟨max F0 (max F1 (max F2 F3)), prepareMajorFueled_nk hk ?_ hc
    (ConLeche.whnf_mono (by omega) hF1) (litMajorToCtorFueled_mono (by omega) hF2)
    (majorToCtorFueled_mono (by omega) hF3)⟩
  cases hs : x.isStrLit
  · simp only [hs, Bool.false_eq_true, ite_false] at hF0 ⊢
    exact majorToCtorFueled_mono (by omega) hF0
  · simp only [hs, ite_true] at hF0 ⊢
    exact hF0
grind_pattern [bridge_grind] prep_nk => prepOp mode eager env d cn isK rules x, PrepE mode eager env d cn isK rules x mE,
  RunE (ConLeche.whnf mode eager env) d mE m1, Runs (litMajorOp mode eager env d m1) m2,
  Runs (majorToCtorOp mode eager env d cn isK rules m2) m3

/-- con-leche: ConLeche/Kernel/Core.lean:751-769 prepareMajor — **THEOREM 1 for
`prepareMajor`**.  The non-K path's answer arrives through four walks whose answers are
each other's subjects, hence `gen := 16`. -/
theorem prepareMajor_spec {fuel : Nat}
    (hsim : KnotSpec eager env fe fuel) (henv : EnvWF env)
    (s₀ : AState) (d : Nat) (c : NIdx) (isK : Bool) (rules : List IRecRule) (major : EIdx)
    (cn : ConLeche.Name) (rules' : List RecRule) (x : Expr)
    (hok : CheckOK eager env fe s₀)
    (hr : Frontend.denoteRules s₀.store rules = some rules')
    (hden : denoteE s₀.store major = some x) (hw : Expr.WScoped d x) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.prepareMajor .verified (coreKnot .verified eager fe id fuel) fe d c isK rules major
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ SimEOp (prepOp .verified eager env d cn isK rules' x) d s'.store r; ⊤⦄ := by
  sym (gen := 16) only [bridge_grind] =>
    vcgen [ConRon.Arena.prepareMajor, majorToCtor_specS hsim henv (cn := cn) (rules' := rules'),
      isCtorApp_specS (eager := eager) (env := env), isStrLit_spec (eager := eager) (env := env) (fe := fe) (x := x),
      litMajorToCtor_specS hsim, hsim.whnfS] <;> finish


end ConRon.Bridge.Core

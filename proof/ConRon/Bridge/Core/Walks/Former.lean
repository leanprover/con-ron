/-
# `ConRon.Bridge.Core.Walks.Former` — the walk to a family's sort, at use

con-leche task #480 computes a family's sort where it is asked
(`ConLeche/Kernel/Core.lean:462-511`): `formerSortLoop` walks `n` binders of
the instantiated stored type down by the knot's `whnf`, `formerNeverZeroAt`
reads the answer (or the stored type's own sort, `formerNeverZero`), and the ι
case split asks it at the rule's comparand levels (`iotaCase3At`).  The
projection guard's sort (`projGuardSort`) is the same walk with another
reading.  This module is Theorem 1 for those four.

Each answer is a named predicate over the denotation term (`SortLoopAns`,
`NZAns`, `C3Ans`, `GuardSortAns`), with the pure side's exits as `grind`
lemmas over the head-normal form's projections (`fsl_zero`, `fsl_pi`, …),
the fuel merged by `Walks/Mono.lean`'s `…Fueled_mono`.
-/
module

public import ConRon.Bridge.Core.Walks.IotaLeaves
import ConRon.Bridge.Core.Walks.PropRead
import ConRon.Bridge.Core.Walks.Spine
import ConRon.Bridge.Core.Walks.Nat
public import ConRon.Bridge.Core.Walks.Mono
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.ExprOps.Owed
import ConRon.Bridge.Core.Memo
public import ConRon.Bridge.Core.Knot
public import ConRon.Bridge.Grind
import ConRon.Bridge.Specs
import ConLeche.Verify.InstLevels
import ConRon.Bridge.GrindAttr

public section

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {eager : Bool} {env : Env} {fe : IFEnv}

/-! ## 1. `formerSortLoop` -/

/-- con-leche: none — an `fvar` node's denotation at its annotation's (the arm
of `denoteEView` that would otherwise reach `grind` as an `Option.map`). -/
@[expose] def optFVar (k : Nat) : Option Expr → Option Expr
  | some t => some (.fvar k t)
  | none => none

/-- con-leche: none — `optFVar` at a present annotation. -/
@[bridge_grind =] theorem optFVar_some (k : Nat) (t : Expr) :
    optFVar k (some t) = some (.fvar k t) := rfl

/-- con-leche: none — `denoteEView` at an `fvar` view. -/
@[bridge_grind =] theorem denoteEView_fvar_eq (st : EStore) (k : Nat) (ty : EIdx) :
    denoteEView st (.fvar k ty) = optFVar k (denoteE st ty) := by
  simp only [denoteEView]; cases denoteE st ty <;> rfl

grind_pattern [bridge_grind] viewOK_fvar => st.ViewOK (.fvar k ty)

/-- con-leche: none — `instantiate1`'s answer at two optional subjects. -/
@[expose] def Inst1Rel : Option Expr → Option Expr → Option Expr → Prop
  | some w, some b, o => o = some (b.instantiate1 w)
  | _, _, _ => True

/-- con-leche: none — `Inst1Rel` at two denoting subjects. -/
@[bridge_grind =] theorem Inst1Rel.some_eq (w b : Expr) (o : Option Expr) :
    Inst1Rel (some w) (some b) o = (o = some (b.instantiate1 w)) := rfl

/-- con-leche: ConLeche/Kernel/ExprOps.lean:176-178 instantiate1Fast — the
substitution's answer as `Inst1Rel` on the three denotation terms. -/
theorem instantiate1Fast_specR (s₀ : AState) (b w : EIdx) (hok : CheckOK eager env fe s₀)
    (hdb : (denoteE s₀.store b).isSome = true) (hdw : (denoteE s₀.store w).isSome = true) :
    ⦃fun s => s = s₀⦄ instantiate1Fast coreWalkFuel b w 0
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ Inst1Rel (denoteE s₀.store w) (denoteE s₀.store b) (denoteE s'.store r); ⊤⦄ := by
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp hdb
  obtain ⟨W, hW⟩ := Option.isSome_iff_exists.mp hdw
  rw [hB, hW]
  exact instantiate1Fast_ok_spec s₀ b w B W hok hB hW

/-- con-leche: ConLeche/Kernel/Core.lean:462-473 formerSortLoop — **the walk's
answer at a subject**: the level handle denotes what the pure walk answers at
some fuel. -/
@[expose] def SortLoop (eager : Bool) (env : Env) (d n : Nat) (x : Expr) (st : EStore)
    (r : Option LIdx) : Prop :=
  ∃ v, denoteLO st r = some v ∧
    ∃ F, formerSortLoop (pureFns .verified eager env F).whnf d n x = .ok v

/-- con-leche: none — `SortLoop` at an optional subject (the walk's answer
shape: the subject's denotation is a term). -/
@[expose] def SortLoopAns (eager : Bool) (env : Env) (d n : Nat) (st : EStore)
    (r : Option LIdx) : Option Expr → Prop
  | some x => SortLoop eager env d n x st r
  | none => True

/-- con-leche: none — `SortLoopAns` at a denoting subject. -/
@[bridge_grind =] theorem SortLoopAns.some_eq (d n : Nat) (st : EStore) (r : Option LIdx)
    (x : Expr) : SortLoopAns eager env d n st r (some x) = SortLoop eager env d n x st r := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:462-473 formerSortLoop — the last
binder: the head-normal form is a sort, or the walk answers `none`. -/
theorem fsl_zero {F d : Nat} {x w : Expr} {st : EStore} {r : Option LIdx}
    (hw : ConLeche.whnf .verified eager env F d x = .ok w)
    (hr : denoteLO st r =
      some (if exprTag w = ETag.sort then some (exprSort w) else none)) :
    SortLoop eager env d 0 x st r := by
  refine ⟨_, hr, F, ?_⟩
  have e1 : (pureFns .verified eager env F).whnf d x = .ok w := hw
  simp only [ConLeche.formerSortLoop, e1, bind, Except.bind]
  cases w <;> rfl
grind_pattern [bridge_grind] fsl_zero =>
  SortLoop eager env d 0 x st r, ConLeche.whnf .verified eager env F d x, exprTag w

/-- con-leche: ConLeche/Kernel/Core.lean:462-473 formerSortLoop — a binder to
open, but the head-normal form is not a `∀`. -/
theorem fsl_nopi {F d n : Nat} {x w : Expr} {st : EStore}
    (hw : ConLeche.whnf .verified eager env F d x = .ok w)
    (ht : exprTag w ≠ ETag.forallE) :
    SortLoop eager env d (n + 1) x st none := by
  refine ⟨none, rfl, F, ?_⟩
  have e1 : (pureFns .verified eager env F).whnf d x = .ok w := hw
  simp only [ConLeche.formerSortLoop, e1, bind, Except.bind]
  cases w <;> first | rfl | exact absurd rfl ht
grind_pattern [bridge_grind] fsl_nopi =>
  SortLoop eager env d (n + 1) x st none, ConLeche.whnf .verified eager env F d x, exprTag w

/-- con-leche: ConLeche/Kernel/Core.lean:462-473 formerSortLoop — a `∀`: the
walk continues one binder down at the opened body. -/
theorem fsl_pi {F d n : Nat} {x w : Expr} {st : EStore} {r : Option LIdx}
    (hw : ConLeche.whnf .verified eager env F d x = .ok w)
    (ht : exprTag w = ETag.forallE)
    (hr : SortLoop eager env (d + 1) n
      ((exprBody w).instantiate1 (.fvar d (exprBinderType w))) st r) :
    SortLoop eager env d (n + 1) x st r := by
  obtain ⟨v, hv, F₂, hF₂⟩ := hr
  refine ⟨v, hv, F + F₂, ?_⟩
  have e1 : (pureFns .verified eager env (F + F₂)).whnf d x = .ok w :=
    ConLeche.whnf_mono (by omega) hw
  rw [exprTag_forallE ht] at e1
  simp only [ConLeche.formerSortLoop, e1, bind, Except.bind]
  exact formerSortLoopFueled_mono (by omega) hF₂
grind_pattern [bridge_grind] fsl_pi =>
  SortLoop eager env d (n + 1) x st r, ConLeche.whnf .verified eager env F d x,
  SortLoop eager env (d + 1) n ((exprBody w).instantiate1 (.fvar d (exprBinderType w))) st r

/-- con-leche: ConLeche/Verify/Shift.lean:220 WScoped.instantiate1 — a `∀`'s
body, opened at the next free variable, is scoped one deeper. -/
theorem wscoped_open_body {d : Nat} {w : Expr} (h : Expr.WScoped d w)
    (ht : exprTag w = ETag.forallE) :
    Expr.WScoped (d + 1) ((exprBody w).instantiate1 (.fvar d (exprBinderType w))) := by
  rw [exprTag_forallE ht] at h
  simp only [Expr.WScoped] at h
  exact Expr.WScoped.instantiate1 h.1 0 h.2
grind_pattern [bridge_grind] wscoped_open_body => Expr.WScoped d w, exprTag w

/-- con-leche: ConLeche/Kernel/Core.lean:462-473 formerSortLoop
con-leche: ConLeche/Cached/CoreC.lean:424-437 formerSortLoopI — **THEOREM 1 for
`formerSortLoop`**: `n` binders down by the knot's `whnf`, then a sort. -/
theorem formerSortLoop_spec {fuel : Nat} (hsim : KnotSpec eager env fe fuel) :
    ∀ (n d : Nat) (s₀ : AState) (e : EIdx), CheckOK eager env fe s₀ →
      DenWS d (denoteE s₀.store e) →
      ⦃fun s => s = s₀⦄
        ConRon.Arena.formerSortLoop (coreKnot .verified eager fe id fuel) d n e
      ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
          SortLoopAns eager env d n s'.store r (denoteE s₀.store e); ⊤⦄ := by
  intro n
  induction n with
  | zero =>
    intro d s₀ e hok hw
    cases hd : denoteE s₀.store e with
    | none => rw [hd] at hw; exact hw.elim
    | some x =>
    rw [hd] at hw
    sym only [bridge_grind] =>
      vcgen [ConRon.Arena.formerSortLoop, KnotSpec.whnfS hsim] <;> finish
  | succ n ih =>
    intro d s₀ e hok hw
    cases hd : denoteE s₀.store e with
    | none => rw [hd] at hw; exact hw.elim
    | some x =>
    rw [hd] at hw
    sym only [bridge_grind] =>
      vcgen [ConRon.Arena.formerSortLoop, KnotSpec.whnfS hsim,
        internE_specC (eager := eager) (env := env) (fe := fe),
        instantiate1Fast_specR (eager := eager) (env := env) (fe := fe), ih] <;>
        -- `gen := 16`: the opened body is four derived steps from the head-normal form (its
        -- view, the fvar's denotation, the substitution, the recursive call's subject)
        finish (gen := 16)

/-! ## 2. `formerNeverZeroAt` -/

/-- con-leche: none — `instLPFast` at the tier's invariant (`CheckOK.ofInstLP`). -/
theorem instLPFast_specC (s₀ : AState) (ks : List NIdx) (us : LsIdx) (e : EIdx)
    (ksv : List ConLeche.Name) (usv : List Level) (x : Expr)
    (hok : CheckOK eager env fe s₀) (hks : Frontend.denoteNList s₀.store.ns ks = some ksv)
    (hus : denoteLs s₀.store.lss us = some usv) (he : denoteE s₀.store e = some x) :
    ⦃fun s => s = s₀⦄ instLPFast coreWalkFuel ks us e
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        denoteE s'.store r = some (x.instantiateLevelParams ksv usv); ⊤⦄ :=
  triple_mono (ExprOps.instLPFast_spec coreWalkFuel s₀ ks us e ksv usv hok.state
      hok.caches.readN hok.caches.readL hok.caches.readLs hks hus (by rw [he]; rfl))
    (fun _ _ ⟨hst, hx, hL, hLs, hN, hc, hp, _, hr⟩ =>
      ⟨CheckOK.ofInstLP hok hst hx hL hLs hN hc hp, hx, hp, hr x he⟩)

/-- con-leche: ConLeche/Verify/Shift.lean:264 WScoped.of_not_hasFvar — a closed
stored type, level-instantiated, is scoped at depth `0`. -/
theorem wscoped_instLP_closed {ty : Expr} {ks : List ConLeche.Name} {vs : List Level}
    (h : ty.hasFvar = false) : Expr.WScoped 0 (ty.instantiateLevelParams ks vs) :=
  Expr.WScoped.of_not_hasFvar (by rw [Expr.hasFvar_instantiateLevelParams]; exact h)
grind_pattern [bridge_grind] wscoped_instLP_closed =>
  Expr.WScoped 0 (ty.instantiateLevelParams ks vs), ty.hasFvar

/-- con-leche: ConLeche/Kernel/Core.lean:475-488 formerNeverZeroAt — **the
test's answer**: the pure test answers `b` at some fuel. -/
@[expose] def NZ (eager : Bool) (env : Env) (cvT : ConstantVal) (caps : IndCaps)
    (us : List Level) (b : Bool) : Prop :=
  ∃ F, formerNeverZeroAt (pureFns .verified eager env F).whnf cvT caps us = .ok b

/-- con-leche: ConLeche/Kernel/Core.lean:475-488 formerNeverZeroAt — a stored
type that ends in a sort is read directly. -/
theorem nz_stored {cvT : ConstantVal} {caps : IndCaps} {us : List Level}
    (h : (ConLeche.formerResSort cvT.type).isSome = true) :
    NZ eager env cvT caps us (ConLeche.formerNeverZero cvT us) := by
  refine ⟨0, ?_⟩
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h
  simp only [ConLeche.formerNeverZeroAt, hs]; rfl
grind_pattern [bridge_grind] nz_stored =>
  NZ eager env cvT caps us (ConLeche.formerNeverZero cvT us)

/-- con-leche: ConLeche/Kernel/Core.lean:475-488 formerNeverZeroAt — any other
is walked to a sort at the use's levels, and the sort read. -/
theorem nz_walk {cvT : ConstantVal} {caps : IndCaps} {us : List Level} {st : EStore}
    {j : LIdx} {l : Level}
    (h : (ConLeche.formerResSort cvT.type).isSome = false)
    (hw : SortLoop eager env 0 (caps.nparams + caps.nIdx)
      (cvT.type.instantiateLevelParams cvT.levelParams us) st (some j))
    (hl : denoteL st.ls j = some l) :
    NZ eager env cvT caps us (Level.zeronessOf l).isNever := by
  obtain ⟨v, hv, F, hF⟩ := hw
  simp only [denoteLO, hl, Option.map_some, Option.some.injEq] at hv
  subst hv
  refine ⟨F, ?_⟩
  have hn : ConLeche.formerResSort cvT.type = none := by
    cases h' : ConLeche.formerResSort cvT.type <;> simp_all
  simp only [ConLeche.formerNeverZeroAt, hn, hF, bind, Except.bind]; rfl
grind_pattern [bridge_grind] nz_walk =>
  NZ eager env cvT caps us (Level.zeronessOf l).isNever,
  SortLoop eager env 0 (caps.nparams + caps.nIdx)
    (cvT.type.instantiateLevelParams cvT.levelParams us) st (some j), denoteL st.ls j

/-- con-leche: ConLeche/Kernel/Core.lean:475-488 formerNeverZeroAt — the walk
reached no sort: the conservative `false`. -/
theorem nz_none {cvT : ConstantVal} {caps : IndCaps} {us : List Level} {st : EStore}
    (h : (ConLeche.formerResSort cvT.type).isSome = false)
    (hw : SortLoop eager env 0 (caps.nparams + caps.nIdx)
      (cvT.type.instantiateLevelParams cvT.levelParams us) st none) :
    NZ eager env cvT caps us false := by
  obtain ⟨v, hv, F, hF⟩ := hw
  simp only [denoteLO, Option.some.injEq] at hv
  subst hv
  refine ⟨F, ?_⟩
  have hn : ConLeche.formerResSort cvT.type = none := by
    cases h' : ConLeche.formerResSort cvT.type <;> simp_all
  simp only [ConLeche.formerNeverZeroAt, hn, hF, bind, Except.bind]; rfl
grind_pattern [bridge_grind] nz_none =>
  NZ eager env cvT caps us false,
  SortLoop eager env 0 (caps.nparams + caps.nIdx)
    (cvT.type.instantiateLevelParams cvT.levelParams us) st none

/-- con-leche: ConLeche/Kernel/Core.lean:475-488 formerNeverZeroAt
con-leche: ConLeche/Cached/CoreC.lean:439-449 formerNeverZeroI — **THEOREM 1 for
`formerNeverZeroAt`**: a family's sort never zero at the levels `us`, at a
closed stored type. -/
theorem formerNeverZeroAt_spec {fuel : Nat} (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (cvT : IConstantVal) (cvTP : ConstantVal) (caps : IIndCaps)
    (capsP : IndCaps) (us : LsIdx) (ls : List Level)
    (hok : CheckOK eager env fe s₀) (hcv : Frontend.denoteCV s₀.store cvT = some cvTP)
    (hcaps : Frontend.denoteCaps s₀.store caps = some capsP)
    (hus : denoteLs s₀.store.lss us = some ls) (hcl : cvTP.type.hasFvar = false) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.formerNeverZeroAt (coreKnot .verified eager fe id fuel) cvT caps us
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        NZ eager env cvTP capsP ls r; ⊤⦄ := by
  obtain ⟨-, hlps, hty⟩ := denoteCV_inv hcv
  obtain ⟨-, hnp, hni⟩ := denoteCaps_fields hcaps
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.formerNeverZeroAt,
      formerResSort_spec (eager := eager) (env := env) (fe := fe) (tyP := cvTP.type),
      formerNeverZero_spec (eager := eager) (env := env) (fe := fe) (cvP := cvTP) (ls := ls),
      instLPFast_specC (eager := eager) (env := env) (fe := fe) (ksv := cvTP.levelParams)
        (usv := ls) (x := cvTP.type),
      formerSortLoop_spec hsim, readLevelM_specC (eager := eager) (env := env) (fe := fe)] <;>
      finish (gen := 16)

/-- con-leche: ConLeche/Verify/EnvWF.lean:102 ConstWF — a stored inductive's
type is closed (and the default record's, where there is none). -/
theorem indVal_closed (henv : EnvWF env) (T : ConLeche.Name) :
    (cIndVal (env.find? T)).type.hasFvar = false := by
  cases hf : env.find? T with
  | none => rfl
  | some ci =>
    cases ci <;> try rfl
    exact (henv.consts _ (Env.find?_mem hf)).1

/-! ## 3. `iotaCase3At` -/

/-- con-leche: ConLeche/Verify/EnvWF.lean:102 ConstWF — the family stored at a
constructor's `induct` has a closed stored type (and the default record, where
there is none, a closed type too). -/
theorem ctorFamily_closed (henv : EnvWF env) (induct : ConLeche.Name) :
    ((ConLeche.ctorFamily env.find? induct).getD default).1.type.hasFvar = false := by
  rw [ctorFamily_eq]
  split
  · rename_i hi
    simp only [Option.getD_some]
    cases hf : env.find? induct with
    | none => rw [hf] at hi; cases hi
    | some ci =>
      rw [hf] at hi
      cases ci <;> simp only [cInd?, Bool.false_eq_true] at hi
      exact (henv.consts _ (Env.find?_mem hf)).1
  · rfl
grind_pattern [bridge_grind] ctorFamily_closed =>
  EnvWF env, ConLeche.ctorFamily env.find? induct

/-- con-leche: none — `FamAns` at the index's hit: the environment's answer is
the pair of its own components, which the hit's halves denote. -/
theorem FamAns.some_inv {st : EStore} {cv : IConstantVal} {caps : IIndCaps}
    {o : Option (ConstantVal × IndCaps)} (h : FamAns st (some (cv, caps)) o) :
    o = some ((o.getD default).1, (o.getD default).2) ∧
      Frontend.denoteCV st cv = some (o.getD default).1 ∧
      Frontend.denoteCaps st caps = some (o.getD default).2 := by
  cases o with
  | none => exact h.elim
  | some p => exact ⟨rfl, h⟩
grind_pattern [bridge_grind] FamAns.some_inv => FamAns st (some (cv, caps)) o

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:978-990 iotaNoCert — **THEOREM 1 for
`iotaNoCert`**: pure on both sides, one lookup at the stored family name, an
equation. -/
theorem iotaNoCert_eq {s : AState} (hok : CheckOK eager env fe s) {induct : NIdx}
    {inductP : ConLeche.Name} (hT : denoteN s.store.ns induct = some inductP)
    (isK : Bool) (n : Nat) :
    ConRon.Arena.iotaNoCert fe isK induct n = ConLeche.iotaNoCert env.find? isK inductP n := by
  have hfam := ctorFamily_rel hok hT
  have e : ConRon.Arena.iotaNoCert fe isK induct n =
      (isK || match ConRon.Arena.ctorFamily fe induct with
        | some (cvT, caps) => caps.neverZero && cvT.levelParams.length == n
        | none => false) := by
    unfold ConRon.Arena.iotaNoCert ConRon.Arena.ctorFamily
    cases isK
    · simp only [Bool.false_eq_true, ite_false, Bool.false_or]
      cases fe.find? induct with
      | none => rfl
      | some ci => cases ci <;> rfl
    · rfl
  rw [e]
  unfold ConLeche.iotaNoCert
  congr 1
  generalize ConRon.Arena.ctorFamily fe induct = a at hfam
  generalize ConLeche.ctorFamily env.find? inductP = b at hfam
  match a, b, hfam with
  | none, _, h => rw [FamAns.none_eq] at h; subst h; rfl
  | some (cv, caps), some (cvP, capsP), ⟨hcv, hcaps⟩ =>
    simp only
    rw [denoteCaps_neverZero hcaps, denoteNList_len (denoteCV_levelParams hcv)]
  | some _, none, h => exact h.elim

/-- con-leche: ConLeche/Kernel/Core.lean:562-583 iotaCase3At — **the case
split's answer**: the pure split answers `b` at some fuel. -/
@[expose] def C3 (eager : Bool) (env : Env) (isK : Bool) (induct : ConLeche.Name)
    (us : List Level) (b : Bool) : Prop :=
  ∃ F, iotaCase3At (pureFns .verified eager env F).whnf env.find? isK induct us = .ok b

/-- con-leche: ConLeche/Kernel/Core.lean:562-583 iotaCase3At — a K recursor is
never case 3. -/
theorem c3_K {induct : ConLeche.Name} {us : List Level} : C3 eager env true induct us false :=
  ⟨0, rfl⟩
grind_pattern [bridge_grind] c3_K => C3 eager env true induct us false

/-- con-leche: ConLeche/Kernel/Core.lean:562-583 iotaCase3At — no stored family:
case 3. -/
theorem c3_nofam {induct : ConLeche.Name} {us : List Level}
    (h : ConLeche.ctorFamily env.find? induct = none) : C3 eager env false induct us true :=
  ⟨0, by simp only [ConLeche.iotaCase3At, h, Bool.false_eq_true, ite_false]; rfl⟩
grind_pattern [bridge_grind] c3_nofam =>
  C3 eager env false induct us true, ConLeche.ctorFamily env.find? induct

/-- con-leche: ConLeche/Kernel/Core.lean:562-583 iotaCase3At — the family's
level parameters do not match the comparands: case 3. -/
theorem c3_len {induct : ConLeche.Name} {us : List Level}
    (h : (ConLeche.ctorFamily env.find? induct).isSome = true)
    (hl : ((ConLeche.ctorFamily env.find? induct).getD default).1.levelParams.length ≠
      us.length) : C3 eager env false induct us true := by
  obtain ⟨⟨cvT, caps⟩, hc⟩ := Option.isSome_iff_exists.mp h
  rw [hc] at hl
  exact ⟨0, by simp only [ConLeche.iotaCase3At, hc, Bool.false_eq_true, ite_false, beq_iff_eq,
    Option.getD_some] at hl ⊢; simp only [hl, ite_false]; rfl⟩
grind_pattern [bridge_grind] c3_len =>
  C3 eager env false induct us true, ConLeche.ctorFamily env.find? induct

/-- con-leche: ConLeche/Kernel/Core.lean:562-583 iotaCase3At — case 3 exactly
where the family's sort may be zero at the comparands. -/
theorem c3_nz {induct : ConLeche.Name} {us : List Level} {b : Bool}
    (h : (ConLeche.ctorFamily env.find? induct).isSome = true)
    (hl : ((ConLeche.ctorFamily env.find? induct).getD default).1.levelParams.length =
      us.length)
    (hb : NZ eager env ((ConLeche.ctorFamily env.find? induct).getD default).1
      ((ConLeche.ctorFamily env.find? induct).getD default).2 us b) :
    C3 eager env false induct us !b := by
  obtain ⟨⟨cvT, caps⟩, hc⟩ := Option.isSome_iff_exists.mp h
  rw [hc] at hl hb
  obtain ⟨F, hF⟩ := hb
  exact ⟨F, by simp only [Option.getD_some] at hl hF; simp only [ConLeche.iotaCase3At, hc,
    Bool.false_eq_true, ite_false, hl, beq_self_eq_true, ite_true, hF, bind, Except.bind]; rfl⟩
grind_pattern [bridge_grind] c3_nz =>
  C3 eager env false induct us !b,
  NZ eager env ((ConLeche.ctorFamily env.find? induct).getD default).1
    ((ConLeche.ctorFamily env.find? induct).getD default).2 us b

/-- con-leche: ConLeche/Kernel/Core.lean:562-583 iotaCase3At
con-leche: ConLeche/Cached/CoreC.lean:794-805 iotaCase3I — **THEOREM 1 for
`iotaCase3At`**: the ι case split at the comparand levels, the family read at
the constructor's stored `induct`. -/
theorem iotaCase3At_spec {fuel : Nat} (hsim : KnotSpec eager env fe fuel)
    (henv : EnvWF env) (s₀ : AState) (isK : Bool) (induct : NIdx) (inductP : ConLeche.Name)
    (us : LsIdx) (ls : List Level)
    (hok : CheckOK eager env fe s₀) (hT : denoteN s₀.store.ns induct = some inductP)
    (hus : denoteLs s₀.store.lss us = some ls) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.iotaCase3At (coreKnot .verified eager fe id fuel) fe isK induct us
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        C3 eager env isK inductP ls r; ⊤⦄ := by
  have hlen := viewLen_of_denoteLs hus
  have hfam := ctorFamily_rel hok hT
  have hcl := ctorFamily_closed henv inductP
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.iotaCase3At,
      formerNeverZeroAt_spec hsim
        (cvTP := ((ConLeche.ctorFamily env.find? inductP).getD default).1)
        (capsP := ((ConLeche.ctorFamily env.find? inductP).getD default).2) (ls := ls)] <;>
      finish (gen := 16)

/-- con-leche: ConLeche/Kernel/Core.lean:594-599 familyNeverZeroAt — **the
family's never-zero answer**: the pure test answers `b` at some fuel. -/
@[expose] def FNZ (eager : Bool) (env : Env) (cvT : ConstantVal) (caps : IndCaps)
    (us : List Level) (b : Bool) : Prop :=
  ∃ F, familyNeverZeroAt (pureFns .verified eager env F).whnf cvT caps us = .ok b

/-- con-leche: ConLeche/Kernel/Core.lean:594-599 familyNeverZeroAt — the stored
fact answers `true`. -/
theorem fnz_stored {cvT : ConstantVal} {caps : IndCaps} {us : List Level}
    (h : caps.neverZero = true) : FNZ eager env cvT caps us true :=
  ⟨0, by simp only [ConLeche.familyNeverZeroAt, h, ite_true]; rfl⟩
grind_pattern [bridge_grind] fnz_stored => FNZ eager env cvT caps us true

/-- con-leche: ConLeche/Kernel/Core.lean:594-599 familyNeverZeroAt — no stored
fact: the test where it is asked. -/
theorem fnz_use {cvT : ConstantVal} {caps : IndCaps} {us : List Level} {b : Bool}
    (h : caps.neverZero = false) (hb : NZ eager env cvT caps us b) :
    FNZ eager env cvT caps us b :=
  let ⟨F, hF⟩ := hb
  ⟨F, by simp only [ConLeche.familyNeverZeroAt, h, Bool.false_eq_true, ite_false]; exact hF⟩
grind_pattern [bridge_grind] fnz_use => FNZ eager env cvT caps us b, NZ eager env cvT caps us b

/-- con-leche: ConLeche/Kernel/Core.lean:594-599 familyNeverZeroAt
con-leche: ConLeche/Cached/CoreC.lean:788-792 familyNeverZeroI — **THEOREM 1 for
`familyNeverZeroAt`**: the stored fact first, else `formerNeverZeroAt`. -/
theorem familyNeverZeroAt_spec {fuel : Nat} (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (cvT : IConstantVal) (cvTP : ConstantVal) (caps : IIndCaps)
    (capsP : IndCaps) (us : LsIdx) (ls : List Level)
    (hok : CheckOK eager env fe s₀) (hcv : Frontend.denoteCV s₀.store cvT = some cvTP)
    (hcaps : Frontend.denoteCaps s₀.store caps = some capsP)
    (hus : denoteLs s₀.store.lss us = some ls) (hcl : cvTP.type.hasFvar = false) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.familyNeverZeroAt (coreKnot .verified eager fe id fuel) cvT caps us
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        FNZ eager env cvTP capsP ls r; ⊤⦄ := by
  have hnz := denoteCaps_neverZero hcaps
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.familyNeverZeroAt,
      formerNeverZeroAt_spec hsim (cvTP := cvTP) (capsP := capsP) (ls := ls)] <;> finish

/-- con-leche: none — `FNZ` at an optional level list. -/
@[expose] def FNZA (eager : Bool) (env : Env) (cvT : ConstantVal) (caps : IndCaps) (b : Bool) :
    Option (List Level) → Prop
  | some us => FNZ eager env cvT caps us b
  | none => True

/-- con-leche: none — `FNZA` at a denoting list. -/
@[bridge_grind =] theorem FNZA.some_eq (cvT : ConstantVal) (caps : IndCaps) (b : Bool)
    (us : List Level) : FNZA eager env cvT caps b (some us) = FNZ eager env cvT caps us b := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:594-599 familyNeverZeroAt —
`familyNeverZeroAt_spec` at whatever the level list denotes. -/
theorem familyNeverZeroAt_specA {fuel : Nat} (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (cvT : IConstantVal) (cvTP : ConstantVal) (caps : IIndCaps)
    (capsP : IndCaps) (us : LsIdx)
    (hok : CheckOK eager env fe s₀) (hcv : Frontend.denoteCV s₀.store cvT = some cvTP)
    (hcaps : Frontend.denoteCaps s₀.store caps = some capsP)
    (hus : (denoteLs s₀.store.lss us).isSome = true) (hcl : cvTP.type.hasFvar = false) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.familyNeverZeroAt (coreKnot .verified eager fe id fuel) cvT caps us
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        FNZA eager env cvTP capsP r (denoteLs s₀.store.lss us); ⊤⦄ := by
  obtain ⟨ls, hls⟩ := Option.isSome_iff_exists.mp hus
  rw [hls]
  exact familyNeverZeroAt_spec hsim s₀ cvT cvTP caps capsP us ls hok hcv hcaps hls hcl

/-! ## 4. `projGuardSort` -/

/-- con-leche: ConLeche/Kernel/Core.lean:1088-1104 projGuardSort — **the guard
sort's answer**: the pure walk answers `o` at some fuel. -/
@[expose] def GS (eager : Bool) (env : Env) (cvT : ConstantVal) (caps : IndCaps)
    (us : List Level) (o : Option Level) : Prop :=
  ∃ F, projGuardSort (pureFns .verified eager env F).whnf cvT caps us = .ok o

/-- con-leche: ConLeche/Kernel/Core.lean:1088-1104 projGuardSort — a stored type
that ends in a sort answers at once. -/
theorem gs_stored {cvT : ConstantVal} {caps : IndCaps} {us : List Level} {st : EStore}
    {j : LIdx} {sl : Level} {o : Option Level}
    (h : denoteLO st (some j) = some (ConLeche.formerResSort cvT.type))
    (hl : denoteL st.ls j = some sl)
    (ho : o = if sl.isAlwaysZero then some .zero else none) :
    GS eager env cvT caps us o := by
  have hs : ConLeche.formerResSort cvT.type = some sl := by
    simp only [denoteLO, hl, Option.map_some, Option.some.injEq] at h; exact h.symm
  exact ⟨0, by simp only [ConLeche.projGuardSort, hs, ho]; rfl⟩
grind_pattern [bridge_grind] gs_stored =>
  GS eager env cvT caps us o, denoteLO st (some j), ConLeche.formerResSort cvT.type,
  denoteL st.ls j, Level.isAlwaysZero sl

/-- con-leche: ConLeche/Kernel/Core.lean:1088-1104 projGuardSort — any other is
walked to its sort at the use's levels. -/
theorem gs_walk {cvT : ConstantVal} {caps : IndCaps} {us : List Level} {st : EStore}
    {j : LIdx} {sl : Level} {o : Option Level}
    (h : (ConLeche.formerResSort cvT.type).isSome = false)
    (hw : SortLoop eager env 0 (caps.nparams + caps.nIdx)
      (cvT.type.instantiateLevelParams cvT.levelParams us) st (some j))
    (hl : denoteL st.ls j = some sl)
    (ho : o = if (Level.zeronessOf sl).isNever then none else some sl) :
    GS eager env cvT caps us o := by
  obtain ⟨v, hv, F, hF⟩ := hw
  simp only [denoteLO, hl, Option.map_some, Option.some.injEq] at hv
  subst hv
  refine ⟨F, ?_⟩
  have hn : ConLeche.formerResSort cvT.type = none := by
    cases h' : ConLeche.formerResSort cvT.type <;> simp_all
  simp only [ConLeche.projGuardSort, hn, hF, bind, Except.bind, ho]; rfl
grind_pattern [bridge_grind] gs_walk =>
  GS eager env cvT caps us o,
  SortLoop eager env 0 (caps.nparams + caps.nIdx)
    (cvT.type.instantiateLevelParams cvT.levelParams us) st (some j), denoteL st.ls j,
  Level.zeronessOf sl

/-- con-leche: ConLeche/Kernel/Core.lean:1088-1104 projGuardSort
con-leche: ConLeche/Cached/CoreC.lean:966-976 projGuardSortI — **THEOREM 1 for
`projGuardSort`**: the sort a projection's rows answer to, at a closed stored
type. -/
theorem projGuardSort_spec {fuel : Nat} (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (cvT : IConstantVal) (cvTP : ConstantVal) (caps : IIndCaps)
    (capsP : IndCaps) (us : LsIdx) (ls : List Level)
    (hok : CheckOK eager env fe s₀) (hcv : Frontend.denoteCV s₀.store cvT = some cvTP)
    (hcaps : Frontend.denoteCaps s₀.store caps = some capsP)
    (hus : denoteLs s₀.store.lss us = some ls) (hcl : cvTP.type.hasFvar = false) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.projGuardSort (coreKnot .verified eager fe id fuel) cvT caps us
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        GS eager env cvTP capsP ls r; ⊤⦄ := by
  obtain ⟨-, hlps, hty⟩ := denoteCV_inv hcv
  obtain ⟨-, hnp, hni⟩ := denoteCaps_fields hcaps
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.projGuardSort,
      formerResSort_spec (eager := eager) (env := env) (fe := fe) (tyP := cvTP.type),
      instLPFast_specC (eager := eager) (env := env) (fe := fe) (ksv := cvTP.levelParams)
        (usv := ls) (x := cvTP.type),
      formerSortLoop_spec hsim, readLevelM_specC (eager := eager) (env := env) (fe := fe)] <;>
      finish (gen := 16)

end ConRon.Bridge.Core

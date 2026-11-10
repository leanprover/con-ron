/-
# `ConRon.Bridge.Core.Walks.Stuck` — the stuck fallback, `stuckIrrel`

`stuckIrrel` is the `defeq` body's fallback at two structurally distinct
stuck terms — structure-η in both directions, then unit-likeness, then proof
irrelevance — and every congruence failure of `defeqStuck` ends in it.

| walk | twin | con-leche | proof |
|---|---|---|---|
| `stuckIrrel_specA` | `Arena/Core.lean` `stuckIrrel` | `Kernel/Core.lean` `stuckIrrel` | `vcgen`/`grind` over the four exits (`StuckE.*`) |
| `structEtaCert_specA` | `structEtaCert` | `structEtaCert` | `vcgen`/`grind`, exits `EtaCertE.with`/`.none`/`.partial` |
| `structEtaCertWith_spec` | `structEtaCertWith` | `structEtaCertWith` | staged over the twin's program order (`triple_seq`), exits `structEtaCertWith_exits` |
| `etaCtorPartial_spec` | `etaCtorPartial` | `CoreDefs.lean` `etaCtorPartial` | staged, `etaPartialFam` |
| `structEtaExpand_specA` | `structEtaExpand` | `structEtaExpand` | induction on the missing arguments, `vcgen`/`grind`, exits `ExpandE.*` |
| `structUnitCert_specA` | `structUnitCert` | `structUnitCert` | `vcgen`/`grind`, guard `unitSideOk`, exits `UnitCertE.*` |
| `unitLikeLoop_spec` | `unitLikeLoop` | `unitLikeLoop` | induction on the budget, the field loop (`unitLikeFields_spec`) and the shape (`unitLikeShape_spec`, staged) inside |
| `proofIrrel_specA` | `proofIrrel` | `proofIrrel` | `vcgen`/`grind`, exits `PIrrelE.*` |
| `etaCtorShape_spec` | `etaCtorShape` | `CoreDefs.lean` `etaCtorShape` | `vcgen`/`grind`, `etaCtorShape_eq` |

**The answer shape.**  Each child answers about its subjects' DENOTATIONS
(`PairAns P (denoteE s₀.store a) (denoteE s₀.store b) r`, preconditions
`DenWS`), so that a caller never names a denotation; `P` is a named
predicate (`EtaCertE`, `UnitCertE`, `PIrrelE`: `SimBOp` at the pure call,
the `fun` hidden from `grind`).  A chain of knot calls is one named run
keyed by its handles (`SortRun`, `TyRun`, `TyRunH`), and each exit of the
pure side is a lemma over those runs, the fuel merge inside it.

**Two restrictions, and why.**  (2) `EnvWF env`, on `structUnitCert` /
`structEtaCert` and so on `stuckIrrel`: the unit-like loop opens the field
telescope of an instantiated STORED constructor type, and its scope needs it
closed — con-leche's `const_ty_hasFvar`, whose hypothesis is `EnvWF`.
(1)  The twin gates the type-former telescope certificate of
`structUnitCert` (and the two certificate families of `structEtaCertWith`)
on `mode.certs` — the EXECUTED core's `Cached/CoreC.lean:437/440/508` —
where con-leche's spec body runs it unconditionally.  At `mode.certs =
false` the twin answers `true` where the spec may answer `false`, so the
statements are at `.verified`, as every body theorem of this tier is
(`certs_of_verifiedChecks`, con-leche's `Verify/BetaGate.lean:126`).
-/
module

import ConRon.Bridge.Core.Walks.Reserved
import ConRon.Bridge.Core.Walks.Eta
import ConRon.Bridge.Core.Walks.Former
import ConRon.Bridge.Core.Walks.StrLit
import ConRon.Bridge.ExprOps.Walks
public import ConRon.Bridge.Core.Walks.Nat
import ConRon.Bridge.Core.Walks.Proj
import ConRon.Bridge.Core.Walks.Spine
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.Core.Walks.Owed
import ConRon.Bridge.Core.Walks.Mono
import ConRon.Bridge.Core.Memo
import ConLeche.Verify.InferLemmas
public import ConLeche.Verify.EnvWF
import ConRon.Bridge.Specs
import ConRon.Bridge.GrindAttr

public section

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {eager : Bool} {env : Env} {fe : IFEnv}

/-! ## The index at an inductive, and the children's answers -/

grind_pattern [bridge_grind] DenWS.isSome => DenWS d o


/-! ### The children's answers, named -/

/-- con-leche: ConLeche/Kernel/Core.lean:413-425 structEtaCert — its answer at
two subjects. -/
def EtaCertE (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (x y : Expr) (r : Bool) : Prop :=
  SimBOp (fun F => ConLeche.structEtaCertFueled mode eager env F d x y) r

/-- con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith — its
answer at the two subjects and the stuck side's whnf'd type. -/
def EtaWithE (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (x y w : Expr) (r : Bool) : Prop :=
  SimBOp (fun F => ConLeche.structEtaCertWithFueled mode eager env F d x y w) r

/-- con-leche: ConLeche/Kernel/Core.lean:431-455 structUnitCert — its answer. -/
def UnitCertE (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (x y : Expr) (r : Bool) : Prop :=
  SimBOp (fun F => ConLeche.structUnitCertFueled mode eager env F d x y) r

/-- con-leche: ConLeche/Kernel/Core.lean:298-312 proofIrrel — its answer. -/
@[expose] def PIrrelE (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (x y : Expr) (r : Bool) : Prop :=
  SimBOp (fun F => ConLeche.proofIrrelFueled mode eager env F d x y) r

/-- con-leche: ConLeche/Kernel/Core.lean:487-492 stuckIrrel — its answer. -/
def StuckE (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (x y : Expr) (r : Bool) : Prop :=
  SimBOp (fun F => ConLeche.stuckIrrelFueled mode eager env F d x y) r

/-! ## 1. Index and rule-list facts -/

/-- con-leche: none — an index that holds no inductive at a name maps to an
environment that holds none there either. -/
theorem optCI_ind_none {st : EStore} {oc : Option IConstantInfo}
    {oc' : Option ConstantInfo} (hrel : OptCI st oc oc')
    (hnot : ∀ v caps, oc ≠ some (.indInfo v caps)) :
    ∀ cv caps, oc' ≠ some (.indInfo cv caps) := by
  intro cv caps h
  subst h
  cases oc with
  | none => simp only [OptCI] at hrel; cases hrel
  | some ci =>
    obtain ⟨c, hci, hc⟩ := hrel
    cases hc
    obtain ⟨v, caps', rfl⟩ := (denoteCI_ind_iff hci).mpr ⟨cv, caps, rfl⟩
    exact hnot v caps' rfl

/-- con-leche: none — a denoting rule list has the same length. -/
theorem denoteRules_len {st : EStore} :
    ∀ {rs : List IRecRule} {rules : List RecRule},
      Frontend.denoteRules st rs = some rules → rules.length = rs.length
  | [], rules, h => by
    simp only [Frontend.denoteRules] at h; cases h; rfl
  | r :: rs, rules, h => by
    unfold Frontend.denoteRules at h
    split at h
    · rename_i x xs _ hxs
      cases h
      simp [denoteRules_len hxs]
    · simp at h

/-! ### `proofIrrel`'s pure side at its exits -/

/-- con-leche: ConLeche/Kernel/Core.lean:327-341 proofIrrel — the first side's
type's type is not a sort. -/
theorem proofIrrel_nosort_a {F d : Nat} {x y ta tta w : Expr}
    (h1 : ConLeche.inferTypeIO mode eager env F d x = .ok ta)
    (h3 : ConLeche.inferTypeIO mode eager env F d ta = .ok tta)
    (h4 : ConLeche.whnf mode eager env F d tta = .ok w)
    (hw : ∀ l, w ≠ .sort l) :
    ConLeche.proofIrrelFueled mode eager env F d x y = .ok false := by
  have e1 : (ConLeche.pureFns mode eager env F).inferIO d x = .ok ta := h1
  have e3 : (ConLeche.pureFns mode eager env F).inferIO d ta = .ok tta := h3
  have e4 : (ConLeche.pureFns mode eager env F).whnf d tta = .ok w := h4
  simp only [ConLeche.proofIrrelFueled, ConLeche.proofIrrel, e1, e3, e4,
    bind, Except.bind]
  try (cases w <;> first | rfl | exact absurd rfl (hw _))

/-- con-leche: ConLeche/Kernel/Core.lean:327-341 proofIrrel — the first side
is a sort, the second side's type's type is not. -/
theorem proofIrrel_nosort_b {F d : Nat} {x y ta tta tb ttb w : Expr}
    {uT : Level} {okA : Bool}
    (h1 : ConLeche.inferTypeIO mode eager env F d x = .ok ta)
    (h3 : ConLeche.inferTypeIO mode eager env F d ta = .ok tta)
    (h4 : ConLeche.whnf mode eager env F d tta = .ok (.sort uT))
    (h5 : Level.isEquiv uT Level.zero = some okA)
    (h6 : ConLeche.inferTypeIO mode eager env F d y = .ok tb)
    (h7 : ConLeche.inferTypeIO mode eager env F d tb = .ok ttb)
    (h8 : ConLeche.whnf mode eager env F d ttb = .ok w)
    (hw : ∀ l, w ≠ .sort l) :
    ConLeche.proofIrrelFueled mode eager env F d x y = .ok false := by
  have e1 : (ConLeche.pureFns mode eager env F).inferIO d x = .ok ta := h1
  have e3 : (ConLeche.pureFns mode eager env F).inferIO d ta = .ok tta := h3
  have e4 : (ConLeche.pureFns mode eager env F).whnf d tta = .ok (.sort uT) := h4
  have e6 : (ConLeche.pureFns mode eager env F).inferIO d y = .ok tb := h6
  have e7 : (ConLeche.pureFns mode eager env F).inferIO d tb = .ok ttb := h7
  have e8 : (ConLeche.pureFns mode eager env F).whnf d ttb = .ok w := h8
  simp only [ConLeche.proofIrrelFueled, ConLeche.proofIrrel, e1, e3, e4,
    bind, Except.bind, ConLeche.liftFueled, h5, e6, e7, e8, pure, Except.pure]
  try (cases w <;> first | rfl | exact absurd rfl (hw _))

/-- con-leche: ConLeche/Kernel/Core.lean:327-341 proofIrrel — both sides'
types' types are sorts: the verdict is the two level comparisons. -/
theorem proofIrrel_sorts {F d : Nat} {x y ta tta tb ttb : Expr}
    {uT vT : Level} {okA okB : Bool}
    (h1 : ConLeche.inferTypeIO mode eager env F d x = .ok ta)
    (h3 : ConLeche.inferTypeIO mode eager env F d ta = .ok tta)
    (h4 : ConLeche.whnf mode eager env F d tta = .ok (.sort uT))
    (h5 : Level.isEquiv uT Level.zero = some okA)
    (h6 : ConLeche.inferTypeIO mode eager env F d y = .ok tb)
    (h7 : ConLeche.inferTypeIO mode eager env F d tb = .ok ttb)
    (h8 : ConLeche.whnf mode eager env F d ttb = .ok (.sort vT))
    (h9 : Level.isEquiv vT Level.zero = some okB) :
    ConLeche.proofIrrelFueled mode eager env F d x y = .ok (okA && okB) := by
  have e1 : (ConLeche.pureFns mode eager env F).inferIO d x = .ok ta := h1
  have e3 : (ConLeche.pureFns mode eager env F).inferIO d ta = .ok tta := h3
  have e4 : (ConLeche.pureFns mode eager env F).whnf d tta = .ok (.sort uT) := h4
  have e6 : (ConLeche.pureFns mode eager env F).inferIO d y = .ok tb := h6
  have e7 : (ConLeche.pureFns mode eager env F).inferIO d tb = .ok ttb := h7
  have e8 : (ConLeche.pureFns mode eager env F).whnf d ttb = .ok (.sort vT) := h8
  simp only [ConLeche.proofIrrelFueled, ConLeche.proofIrrel, e1, e3, e4,
    bind, Except.bind, ConLeche.liftFueled, h5, h9, e6, e7, e8, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:152-154 liftFueled — the fuel
guard of a level comparison: a `some` passes its value through, a `none`
fails (and `; ⊤` claims nothing of a failure). -/
theorem liftFueled_spec {α : Type} (s₀ : AState) (what : String)
    (o : Option α) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.liftFueled what o
    ⦃fun a s' => s' = s₀ ∧ o = some a; ⊤⦄ := by
  cases o with
  | none => exact triple_fail
  | some a =>
    vcgen [ConRon.Arena.liftFueled] with finish

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames —
the reserved list in triple form: `Walks/Reserved.lean`'s
`reservedBasisNames_runC` (a copy of `Bridge/Checker/Names.lean`'s) (the pin-table read `pinReserved`) read through
`AM.triple_of_run_at`. -/
theorem reservedBasisNames_spec (s₀ : AState) (hok : CheckOK eager env fe s₀) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.reservedBasisNames
    ⦃fun hs s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Frontend.denoteNList s'.store.ns hs =
          some ConLeche.reservedBasisNames; ⊤⦄ :=
  AM.triple_of_run_at fun hs s' hr => by
    obtain ⟨hps, hd⟩ := reservedBasisNames_runC hok.state.wf hok.pins hr
    refine ⟨hok.mono ⟨hps.wf⟩ hps.ext hps.caches hps.pins, hps.ext, hps.pins, ?_⟩
    show Frontend.denoteNList s'.store.ns hs = some reservedBasisNameValues
    exact denoteNL_toListC _ _ hd

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the index's HIT half at
an inductive. -/
theorem env_ind_of_index {s : AState} (hok : CheckOK eager env fe s)
    {T : NIdx} {Tn : ConLeche.Name} {icv : IConstantVal} {icaps : IIndCaps}
    (hn : denoteN s.store.ns T = some Tn)
    (hfd : fe.find? T = some (.indInfo icv icaps)) :
    ∃ dcv dcaps, Frontend.denoteCV s.store icv = some dcv ∧
      Frontend.denoteCaps s.store icaps = some dcaps ∧
      env.find? Tn = some (.indInfo dcv dcaps) := by
  obtain ⟨nm', cc, hn', hci, hfind⟩ := hok.ienv.hit T _ hfd
  obtain rfl := Option.some.inj (hn'.symm.trans hn)
  simp only [Frontend.denoteCI] at hci
  split at hci
  · rename_i dcv dcaps hdcv hdcaps
    cases hci
    exact ⟨dcv, dcaps, hdcv, hdcaps, hfind⟩
  · simp at hci

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the MISS half at an
inductive. -/
theorem env_not_ind_of_index {s : AState} (hok : CheckOK eager env fe s)
    {T : NIdx} {Tn : ConLeche.Name} (hn : denoteN s.store.ns T = some Tn)
    (hnd : ∀ v caps, fe.find? T ≠ some (.indInfo v caps)) :
    ∀ cv caps, env.find? Tn ≠ some (.indInfo cv caps) :=
  optCI_ind_none (optCI_find hok hn) hnd

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:731-737 etaCtorShape — the reader
as ONE equation over the head's tag, its constant name and the environment's
constructor projections. -/
theorem etaCtorShape_eq (x : Expr) :
    ConLeche.etaCtorShape env x =
      (exprTag x.getAppFn == ETag.const && cCtor? (env.find? (exprConstName x.getAppFn)) &&
        x.getAppArgs.length == cCtorNP (env.find? (exprConstName x.getAppFn)) +
          cCtorNF (env.find? (exprConstName x.getAppFn))) := by
  simp only [ConLeche.etaCtorShape]
  cases x.getAppFn with
  | const c us =>
    simp only [exprTag, exprConstName, beq_self_eq_true, Bool.true_and]
    generalize env.find? c = o
    match o with
    | some (.ctorInfo _ _ _) => rfl
    | some (.axiomInfo _) | some (.thmInfo _) | some (.indInfo _ _)
    | some (.defnInfo _ _ _) | some (.recInfo _ _ _ _ _) | none => rfl
  | _ => rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:738-749 etaCtorShape — **THEOREM
1 for `etaCtorShape`**, the constructor-shape test `structEtaCert` runs
FIRST (the divergence audit's D13): an equation with con-leche's reader. -/
theorem etaCtorShape_spec (s₀ : AState) (a : EIdx) (x : Expr)
    (hok : CheckOK eager env fe s₀) (hda : denoteE s₀.store a = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.etaCtorShape fe a
    ⦃fun r s' => s' = s₀ ∧ r = ConLeche.etaCtorShape env x; ⊤⦄ := by
  sym only [bridge_grind, etaCtorShape_eq] =>
    vcgen [ConRon.Arena.etaCtorShape, ExprOps.getAppFn_spec, ExprOps.getAppArgs_spec] <;>
      finish

/-! ### `structEtaCertWith`'s pure side at its exits -/

/-- con-leche: none — a `pure` is a triple for any postcondition its value
and the unchanged state satisfy. -/
theorem triple_pureC {α : Type} {s₀ : AState} {a : α}
    {Q : α → AState → Prop} (h : Q a s₀) :
    ⦃fun s => s = s₀⦄ (pure a : AM α) ⦃fun r s => Q r s; ⊤⦄ :=
  AM.triple_of_run_at fun r s' hr => by
    simp only [pure, StateT.pure, Except.pure] at hr
    cases hr
    exact h

/-- con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith — the
candidate's head is not a constant. -/
theorem structEtaCertWith_nohead {F d : Nat} {x y w : Expr}
    (hh : ∀ c us, x.getAppFn ≠ .const c us) :
    ConLeche.structEtaCertWithFueled mode eager env F d x y w = .ok false := by
  simp only [ConLeche.structEtaCertWithFueled, ConLeche.structEtaCertWith]
  first
    | rfl
    | (split
       · rename_i c us heq; exact absurd heq (hh c us)
       · rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith — the
head is not a stored constructor. -/
theorem structEtaCertWith_noctor {F d : Nat} {x y w : Expr} {c : Name}
    {us : List Level} (hh : x.getAppFn = .const c us)
    (hf : ∀ cv nP nF, env.find? c ≠ some (.ctorInfo cv nP nF)) :
    ConLeche.structEtaCertWithFueled mode eager env F d x y w = .ok false := by
  simp only [ConLeche.structEtaCertWithFueled, ConLeche.structEtaCertWith, hh]
  first
    | rfl
    | (split
       · rename_i cv nP nF heq; exact absurd heq (hf cv nP nF)
       · rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith — the
constructor is not applied to exactly its parameters and fields. -/
theorem structEtaCertWith_len {F d : Nat} {x y w : Expr} {c : Name}
    {us : List Level} {cvc : ConstantVal} {cnP cnF : Nat}
    (hh : x.getAppFn = .const c us)
    (hf : env.find? c = some (.ctorInfo cvc cnP cnF))
    (hlen : ¬ x.getAppArgs.length = cnP + cnF) :
    ConLeche.structEtaCertWithFueled mode eager env F d x y w = .ok false := by
  simp only [ConLeche.structEtaCertWithFueled, ConLeche.structEtaCertWith, hh, hf]
  rw [ite_eq_right hlen]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith — the
stuck side's type's head is not a constant. -/
theorem structEtaCertWith_nohead_w {F d : Nat} {x y w : Expr} {c : Name}
    {us : List Level} {cvc : ConstantVal} {cnP cnF : Nat}
    (hh : x.getAppFn = .const c us)
    (hf : env.find? c = some (.ctorInfo cvc cnP cnF))
    (hlen : x.getAppArgs.length = cnP + cnF)
    (hw : ∀ T us', w.getAppFn ≠ .const T us') :
    ConLeche.structEtaCertWithFueled mode eager env F d x y w = .ok false := by
  simp only [ConLeche.structEtaCertWithFueled, ConLeche.structEtaCertWith, hh, hf]
  rw [ite_eq_left hlen]
  first
    | rfl
    | (split
       · rename_i T us' heq; exact absurd heq (hw T us')
       · rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith — that
head is not a stored inductive. -/
theorem structEtaCertWith_noind {F d : Nat} {x y w : Expr} {c T : Name}
    {us us' : List Level} {cvc : ConstantVal} {cnP cnF : Nat}
    (hh : x.getAppFn = .const c us)
    (hf : env.find? c = some (.ctorInfo cvc cnP cnF))
    (hlen : x.getAppArgs.length = cnP + cnF)
    (hw : w.getAppFn = .const T us')
    (hfT : ∀ cv caps, env.find? T ≠ some (.indInfo cv caps)) :
    ConLeche.structEtaCertWithFueled mode eager env F d x y w = .ok false := by
  simp only [ConLeche.structEtaCertWithFueled, ConLeche.structEtaCertWith, hh, hf,
    hw]
  rw [ite_eq_left hlen]
  first
    | rfl
    | (split
       · rename_i cv caps heq; exact absurd heq (hfT cv caps)
       · rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:334-372 structEtaCertWith — that
inductive has no projection table. -/
theorem structEtaCertWith_notbl {F d : Nat} {x y w : Expr} {c T : Name}
    {us us' : List Level} {cvc cvT : ConstantVal} {cnP cnF : Nat}
    {caps : IndCaps}
    (hh : x.getAppFn = .const c us)
    (hf : env.find? c = some (.ctorInfo cvc cnP cnF))
    (hlen : x.getAppArgs.length = cnP + cnF)
    (hw : w.getAppFn = .const T us')
    (hfT : env.find? T = some (.indInfo cvT caps))
    (ht : env.findTable? T = none) :
    ConLeche.structEtaCertWithFueled mode eager env F d x y w = .ok false := by
  simp only [ConLeche.structEtaCertWithFueled, ConLeche.structEtaCertWith, hh, hf,
    hw, hfT, ht]
  rw [ite_eq_left hlen]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:334-372 structEtaCertWith — the
structure-η guard, as con-leche states it: the constructor and the counts are
the family's projection table's. -/
def EtaGuard (w : Expr) (c : Name) (us' : List Level)
    (cvc cvT : ConstantVal) (caps : IndCaps) (tbl : ProjTable) : Prop :=
  caps.eta = true ∧ tbl.ctor = c ∧
    w.getAppArgs.length = tbl.numParams ∧
    us'.length = cvT.levelParams.length ∧
    cvc.levelParams = cvT.levelParams

/-- con-leche: ConLeche/Kernel/Core.lean:334-372 structEtaCertWith — the
guard fails. -/
theorem structEtaCertWith_guard {F d : Nat} {x y w : Expr} {c T : Name}
    {us us' : List Level} {cvc cvT : ConstantVal} {cnP cnF : Nat}
    {caps : IndCaps} {tbl : ProjTable}
    (hh : x.getAppFn = .const c us)
    (hf : env.find? c = some (.ctorInfo cvc cnP cnF))
    (hlen : x.getAppArgs.length = cnP + cnF)
    (hw : w.getAppFn = .const T us')
    (hfT : env.find? T = some (.indInfo cvT caps))
    (ht : env.findTable? T = some tbl)
    (hg : ¬ EtaGuard w c us' cvc cvT caps tbl) :
    ConLeche.structEtaCertWithFueled mode eager env F d x y w = .ok false := by
  simp only [ConLeche.structEtaCertWithFueled, ConLeche.structEtaCertWith, hh, hf,
    hw, hfT, ht]
  unfold EtaGuard at hg
  rw [ite_eq_left hlen, ite_eq_right hg]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:334-372 structEtaCertWith — past
the guard: the level comparison and the two spine comparisons, verbatim (no
certificate on the type application, con-leche's task #342 L11b). -/
theorem structEtaCertWith_tail {F d : Nat} {x y w : Expr} {c T : Name}
    {us us' : List Level} {cvc cvT : ConstantVal} {cnP cnF : Nat}
    {caps : IndCaps} {tbl : ProjTable}
    (hh : x.getAppFn = .const c us)
    (hf : env.find? c = some (.ctorInfo cvc cnP cnF))
    (hlen : x.getAppArgs.length = cnP + cnF)
    (hw : w.getAppFn = .const T us')
    (hfT : env.find? T = some (.indInfo cvT caps))
    (ht : env.findTable? T = some tbl)
    (hg : EtaGuard w c us' cvc cvT caps tbl) :
    ConLeche.structEtaCertWithFueled mode eager env F d x y w =
      (do
        if ← ConLeche.liftFueled "level comparison"
            (Level.isEquivList us us') then
          if ← ConLeche.defEqListFueled mode eager env F d
              (x.getAppArgs.take tbl.numParams) w.getAppArgs then
            ConLeche.defEqListFueled mode eager env F d
              (x.getAppArgs.drop tbl.numParams)
              (ConLeche.etaProjs T y tbl.numFields)
          else pure false
        else pure false : CheckM Bool) := by
  simp only [ConLeche.structEtaCertWithFueled, ConLeche.structEtaCertWith, hh, hf,
    hw, hfT, ht]
  unfold EtaGuard at hg
  rw [ite_eq_left hlen, ite_eq_left hg]

/-- con-leche: ConLeche/Kernel/Core.lean:334-372 structEtaCertWith — the
tail's exits, each stated at the facts the twin's stages name. -/
theorem structEtaCertWith_exits {F d : Nat} {x y w : Expr} {c T : Name}
    {us us' : List Level} {cvc cvT : ConstantVal} {cnP cnF : Nat}
    {caps : IndCaps} {tbl : ProjTable}
    (hh : x.getAppFn = .const c us)
    (hf : env.find? c = some (.ctorInfo cvc cnP cnF))
    (hlen : x.getAppArgs.length = cnP + cnF)
    (hw : w.getAppFn = .const T us')
    (hfT : env.find? T = some (.indInfo cvT caps))
    (ht : env.findTable? T = some tbl)
    (hg : EtaGuard w c us' cvc cvT caps tbl) :
    (Level.isEquivList us us' = some false →
      ConLeche.structEtaCertWithFueled mode eager env F d x y w = .ok false) ∧
    (Level.isEquivList us us' = some true →
      ∀ dq, ConLeche.defEqListFueled mode eager env F d
        (x.getAppArgs.take tbl.numParams) w.getAppArgs = .ok dq →
      (dq = false →
        ConLeche.structEtaCertWithFueled mode eager env F d x y w = .ok false) ∧
      (dq = true → ∀ r, ConLeche.defEqListFueled mode eager env F d
          (x.getAppArgs.drop tbl.numParams)
          (ConLeche.etaProjs T y tbl.numFields) = .ok r →
        ConLeche.structEtaCertWithFueled mode eager env F d x y w = .ok r)) := by
  rw [structEtaCertWith_tail hh hf hlen hw hfT ht hg]
  refine ⟨fun hl => ?_, fun hl dq hdq => ⟨fun hd => ?_, fun hd r hr => ?_⟩⟩
  all_goals subst_vars
  all_goals clear hg hh hf hlen hw hfT ht
  all_goals simp_all only [ConLeche.liftFueled, pure, Except.pure, bind,
    Except.bind, ite_true, Bool.false_eq_true, ite_false]

/-- con-leche: none — **a conditional, staged**: a triple for each branch,
under the branch's hypothesis, is a triple for the `if`.  (`split` on a
staged goal whose program is a hundred lines long runs `simp` over all of
it; this is the same step with nothing to simplify.) -/
theorem triple_ite {α : Type} {c : Prop} [Decidable c] {x y : AM α}
    {s₀ : AState} {Q : α → AState → Prop}
    (h1 : c → ⦃fun s => s = s₀⦄ x ⦃fun a s => Q a s; ⊤⦄)
    (h2 : ¬ c → ⦃fun s => s = s₀⦄ y ⦃fun a s => Q a s; ⊤⦄) :
    ⦃fun s => s = s₀⦄ (if c then x else y) ⦃fun a s => Q a s; ⊤⦄ := by
  by_cases hc : c
  · rw [ite_eq_left hc]; exact h1 hc
  · rw [ite_eq_right hc]; exact h2 hc

/-- con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith — **THEOREM
1 for `structEtaCertWith`**, the structure-η certificate against a GIVEN
weak-head-normal type `wtb` of the stuck side.

Staged over the twin's program order: `getAppFn` / `getAppArgs` at both
sides, the index at the constructor and the type former
(`env_ctor_of_index`, `env_ind_of_index`), the family's projection table
(`findTable?_at`), `viewLsLen`, the guard (`EtaGuard`, identified by name
injectivity), `lvlsEq?_spec` + `liftFueled_spec`, the parameters
(`defEqList_spec`) and the fields (`etaProjs_spec`, `defEqList_spec`).  The
pure side is `structEtaCertWith_exits`, one statement per exit over
`structEtaCertWith_tail`. -/
theorem structEtaCertWith_spec {fuel : Nat}
    (_henv : ConLeche.EnvWF env) (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (d : Nat) (a b wtb : EIdx) (x y w : Expr)
    (hok : CheckOK eager env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y) (hdw : denoteE s₀.store wtb = some w)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y)
    (hww : Expr.WScoped d w) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.structEtaCertWith (coreKnot .verified eager fe id fuel) fe d a b wtb
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.structEtaCertWithFueled .verified eager env F d x y w)
          r; ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨rk, hrk⟩ := hok.state.wf
  unfold ConRon.Arena.structEtaCertWith
  -- stage 1: the candidate's head
  refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ a hok.state
    (by rw [hda]; rfl)) ?_
  rintro hd s1 ⟨hs1, hrelF⟩
  subst s1
  have hdd : denoteE s₀.store hd = some x.getAppFn := hrelF x hda
  obtain ⟨vh, hvh⟩ := denoteE_view hdd
  refine tag_view_bind_triple hvh ?_
    (fun hne => by cases vh <;> first | rfl | exact absurd rfl hne)
  cases vh
  case const c us =>
    obtain ⟨cn, ls, hgf, hcn, hus⟩ := denote_const_inv hwf hvh hdd
    dsimp only
    split
    next icvc cnP cnF hfdc =>
      obtain ⟨dcvc, hdcvc, hfindc⟩ := env_ctor_of_index hok hcn hfdc
      -- stage 2: its arguments
      refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s₀ a hok.state
        (by rw [hda]; rfl)) ?_
      rintro aargs s2 ⟨hs2, hrelA⟩
      subst s2
      have haargs : Frontend.denoteEList s₀.store aargs = some x.getAppArgs :=
        hrelA x hda
      have hlenEq : x.getAppArgs.length = aargs.length := denoteEList_len haargs
      by_cases hlenT : aargs.length = cnP + cnF
      · rw [ite_eq_left hlenT]
        have hlenP : x.getAppArgs.length = cnP + cnF := hlenEq ▸ hlenT
        -- stage 3: the stuck side's type's head
        refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ wtb hok.state
          (by rw [hdw]; rfl)) ?_
        rintro hw' s3 ⟨hs3, hrelW⟩
        subst s3
        have hdw' : denoteE s₀.store hw' = some w.getAppFn := hrelW w hdw
        obtain ⟨vw, hvw⟩ := denoteE_view hdw'
        refine tag_view_bind_triple hvw ?_
          (fun hne => by cases vw <;> first | rfl | exact absurd rfl hne)
        cases vw
        case const T us' =>
          obtain ⟨Tn, ls', hgw, hTn, hus'⟩ := denote_const_inv hwf hvw hdw'
          dsimp only
          split
          next icvT icaps hfdT =>
            obtain ⟨dcvT, dcaps, hdcvT, hdcaps, hfindT⟩ :=
              env_ind_of_index hok hTn hfdT
            have hcapsE : dcaps.eta = icaps.eta := by
              simp only [Frontend.denoteCaps] at hdcaps
              split at hdcaps
              · exact (Option.some.inj hdcaps) ▸ rfl
              · simp at hdcaps
            -- stage 4: the family's projection table
            obtain ⟨htHit, htMiss⟩ := findTable?_at hok hTn
            cases htb : fe.findTable? T with
            | none =>
              dsimp only
              exact triple_pureC ⟨hok, Ext.refl _, rfl, 0,
                structEtaCertWith_notbl hgf hfindc hlenP hgw hfindT (htMiss htb)⟩
            | some tbl =>
            obtain ⟨pt, hpt, hfindTb, -⟩ := htHit tbl htb
            obtain ⟨hnF, hnP⟩ := denoteProjTable_fields hpt
            have hptc := denoteProjTable_ctor hpt
            dsimp only
            -- stage 5: the type's arguments, the levels
            refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s₀ wtb
              hok.state (by rw [hdw]; rfl)) ?_
            rintro targs s4 ⟨hs4, hrelT⟩
            subst s4
            have htargs : Frontend.denoteEList s₀.store targs = some w.getAppArgs :=
              hrelT w hdw
            refine triple_seq (viewLsLen_spec s₀ us') ?_
            rintro ol s6 ⟨hs6, hol⟩
            subst s6
            rw [viewLen_of_denoteLs hus'] at hol
            subst hol
            dsimp only
            have hx07 : Ext s₀.store s₀.store := Ext.refl _
            have hp07 : s₀.pins = s₀.pins := rfl
            obtain ⟨_, hlpsC, _⟩ := denoteCV_inv hdcvc
            obtain ⟨_, hlpsT, _⟩ := denoteCV_inv hdcvT
            have hctr : tbl.ctor = c ↔ pt.ctor = cn :=
              ⟨fun h => by subst h; exact Option.some.inj (hptc.symm.trans hcn),
               fun h => by subst h; exact denoteN_inj hrk.nsWF hptc hcn⟩
            have hguard : (icaps.eta = true ∧ tbl.ctor = c ∧
                targs.length = tbl.numParams ∧
                ls'.length = icvT.levelParams.length ∧
                icvc.levelParams = icvT.levelParams) ↔
                EtaGuard w cn ls' dcvc dcvT dcaps pt := by
              unfold EtaGuard
              rw [hctr, hcapsE, ← denoteEList_len htargs, denoteNList_len hlpsT,
                denoteNList_eq_iff hwf hlpsC hlpsT, hnP]
            have hwx : ∀ z ∈ x.getAppArgs, Expr.WScoped d z :=
              Expr.WScoped.getAppArgs hwa
            have hwtargs : ∀ z ∈ w.getAppArgs, Expr.WScoped d z :=
              Expr.WScoped.getAppArgs hww
            refine triple_ite (fun hgT => ?_) (fun hgF => ?_)
            · have hgP := hguard.mp hgT
              have hEx := fun F => structEtaCertWith_exits (mode := .verified) (eager := eager) (F := F)
                (d := d) (y := y) hgf hfindc hlenP hgw hfindT hfindTb hgP
              rw [← hnP, ← hnF]
              -- stage 6: the two level lists
              refine triple_seq (lvlsEq?_spec s₀ us us' hok) ?_
              rintro q s8 ⟨hok8, hst8, hp8, lus, lvs, hlus, hlvs, hq⟩
              rw [denoteLs_ext hus hx07] at hlus
              rw [denoteLs_ext hus' hx07] at hlvs
              obtain rfl := Option.some.inj hlus
              obtain rfl := Option.some.inj hlvs
              refine triple_seq (liftFueled_spec s8 _ q) ?_
              rintro okL s9 ⟨hs9, hokL⟩
              subst s9
              have hlv : Level.isEquivList ls ls' = some okL := hq ▸ hokL
              have hx08 : Ext s₀.store s8.store := by rw [hst8]; exact hx07
              have hp08 : s8.pins = s₀.pins := hp8.trans hp07
              refine triple_ite (fun hokT => ?_) (fun hokF => ?_)
              · have hokL' : okL = true := hokT
                subst hokL'
                -- stage 7: the parameters agree
                have haargs8 := denoteEList_ext hx08 _ _
                  (ExprOps.denoteEList_take pt.numParams aargs _ haargs)
                refine triple_seq (defEqList_spec hsim s8 d
                  (aargs.take pt.numParams) targs _ _ hok8 haargs8
                  (denoteEList_ext hx08 _ _ htargs)
                  (fun z hz => hwx z (List.mem_of_mem_take hz)) hwtargs) ?_
                rintro dq s10 ⟨hok10, hx10, hp10, F3, hF3⟩
                have hx010 := hx08.trans hx10
                have hp010 : s10.pins = s₀.pins := hp10.trans hp08
                refine triple_ite (fun hdT => ?_) (fun hdF => ?_)
                · have hdq : dq = true := hdT
                  subst hdq
                  -- stage 8: the fabricated fields agree
                  refine triple_seq (etaProjs_spec s10 T b pt.numFields Tn y
                    hok10 (denoteN_ext hTn hx010) (denote_ext hdb hx010)) ?_
                  rintro projs s11 ⟨hok11, hx11, hp11, hprojs⟩
                  have hx011 := hx010.trans hx11
                  refine triple_mono (defEqList_spec hsim s11 d
                    (aargs.drop pt.numParams) projs _ _ hok11
                    (denoteEList_ext hx011 _ _
                      (ExprOps.denoteEList_drop pt.numParams aargs _ haargs))
                    hprojs (fun z hz => hwx z (List.mem_of_mem_drop hz))
                    (etaProjs_WScoped hwb)) ?_
                  rintro r s12 ⟨hok12, hx12, hp12, F5, hF5⟩
                  refine ⟨hok12, hx011.trans hx12,
                    hp12.trans (hp11.trans hp010), F3 + F5, ?_⟩
                  exact (((hEx (F3 + F5)).2 hlv true
                    (defEqListFueled_mono (by omega) hF3)).2 rfl r
                    (defEqListFueled_mono (by omega) hF5))
                · have hdq : dq = false := by simpa using hdF
                  subst hdq
                  exact triple_pureC ⟨hok10, hx010, hp010, F3,
                    (((hEx F3).2 hlv false hF3).1 rfl)⟩
              · have hokL' : okL = false := by simpa using hokF
                subst hokL'
                exact triple_pureC ⟨hok8, hx08, hp08, 0, (hEx 0).1 hlv⟩
            · exact triple_pureC ⟨hok, hx07, hp07, 0,
                structEtaCertWith_guard hgf hfindc hlenP hgw hfindT hfindTb
                  (fun h => hgF (hguard.mpr h))⟩
          next hnd =>
            have hnf := env_not_ind_of_index hok hTn (fun v c h => hnd v c h)
            have hres : ConLeche.structEtaCertWithFueled .verified eager env 0 d x y w =
                .ok false := structEtaCertWith_noind hgf hfindc hlenP hgw hnf
            exact triple_pureC ⟨hok, Ext.refl _, rfl, 0, hres⟩
        all_goals
          have hres : ConLeche.structEtaCertWithFueled .verified eager env 0 d x y w =
              .ok false := structEtaCertWith_nohead_w hgf hfindc hlenP
                (denote_not_const hwf hvw hdw' (by intro c us h; cases h))
          dsimp only
          exact triple_pureC ⟨hok, Ext.refl _, rfl, 0, hres⟩
      · rw [ite_eq_right hlenT]
        have hres : ConLeche.structEtaCertWithFueled .verified eager env 0 d x y w =
            .ok false := structEtaCertWith_len hgf hfindc (by rw [hlenEq]; exact hlenT)
        exact triple_pureC ⟨hok, Ext.refl _, rfl, 0, hres⟩
    next hnd =>
      have hnc := env_not_ctor_of_index hok hcn (fun v p q h => hnd v p q h)
      have hres : ConLeche.structEtaCertWithFueled .verified eager env 0 d x y w =
          .ok false := structEtaCertWith_noctor hgf hnc
      exact triple_pureC ⟨hok, Ext.refl _, rfl, 0, hres⟩
  all_goals
    have hres : ConLeche.structEtaCertWithFueled .verified eager env 0 d x y w =
        .ok false := structEtaCertWith_nohead
          (denote_not_const hwf hvh hdd (by intro c us h; cases h))
    dsimp only
    exact triple_pureC ⟨hok, Ext.refl _, rfl, 0, hres⟩

/-! ## 2. The three children -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:738-749 etaCtorShape —
`etaCtorShape_spec` at whatever the handle denotes. -/
theorem etaCtorShape_specA (s₀ : AState) (a : EIdx)
    (hok : CheckOK eager env fe s₀) (hda : (denoteE s₀.store a).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.etaCtorShape fe a
    ⦃fun r s' => s' = s₀ ∧ (denoteE s₀.store a).map (ConLeche.etaCtorShape env) = some r; ⊤⦄ := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hda
  refine triple_mono (etaCtorShape_spec s₀ a x hok hx) ?_
  rintro r s' ⟨h1, h2⟩
  exact ⟨h1, by rw [hx, h2]; rfl⟩

/-- con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith —
`structEtaCertWith_spec` in answer shape. -/
theorem structEtaCertWith_specA {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (d : Nat) (a b wtb : EIdx) (hok : CheckOK eager env fe s₀)
    (hda : DenWS d (denoteE s₀.store a)) (hdb : DenWS d (denoteE s₀.store b))
    (hdw : DenWS d (denoteE s₀.store wtb)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.structEtaCertWith (coreKnot .verified eager fe id fuel) fe d a b wtb
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        TripleAns (EtaWithE .verified eager env d) (denoteE s₀.store a) (denoteE s₀.store b)
          (denoteE s₀.store wtb) r; ⊤⦄ := by
  cases ha : denoteE s₀.store a with
  | none => rw [ha] at hda; exact hda.elim
  | some x =>
  cases hb : denoteE s₀.store b with
  | none => rw [hb] at hdb; exact hdb.elim
  | some y =>
  cases hw : denoteE s₀.store wtb with
  | none => rw [hw] at hdw; exact hdw.elim
  | some w =>
  rw [ha] at hda; rw [hb] at hdb; rw [hw] at hdw
  exact structEtaCertWith_spec henv hsim s₀ d a b wtb x y w hok ha hb hw hda hdb hdw

/-! ### `structEtaCert`: the full and the partial application -/

/-- con-leche: ConLeche/Kernel/Core.lean:374-395 structEtaFull — its answer at
two subjects. -/
def FullE (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (x y : Expr) (r : Bool) : Prop :=
  SimBOp (fun F => ConLeche.structEtaFullFueled mode eager env F d x y) r

/-- con-leche: ConLeche/Kernel/Core.lean:397-409 structEtaExpand — its answer
at `k` missing arguments, two subjects and the constructor side's type. -/
def ExpandE (mode : CheckMode) (eager : Bool) (env : Env) (k d : Nat) (x y t : Expr) (r : Bool) :
    Prop :=
  SimBOp (fun F => ConLeche.structEtaExpandFueled mode eager env F k d x y t) r

/-- con-leche: ConLeche/Kernel/Core.lean:411-429 structEtaCert — the
partial-constructor arm's answer at `k` missing arguments. -/
def PartE (mode : CheckMode) (eager : Bool) (env : Env) (k d : Nat) (x y : Expr) (r : Bool) : Prop :=
  SimBOp (fun F => (if !y.ioNeutral then pure false else do
    let ta ← (ConLeche.pureFns mode eager env F).inferIO d x
    let tb ← (ConLeche.pureFns mode eager env F).inferIO d y
    if ← (ConLeche.pureFns mode eager env F).defeq d tb ta then
      ConLeche.structEtaExpandFueled mode eager env F k d x y ta
    else pure false : CheckM Bool)) r

/-- con-leche: ConLeche/Kernel/Core.lean:374-395 structEtaFull — the shape
test fails. -/
@[bridge_grind ←] theorem FullE.shape {d : Nat} {x y : Expr}
    (h : ConLeche.etaCtorShape env x = false) : FullE mode eager env d x y false :=
  ⟨0, by simp only [ConLeche.structEtaFullFueled, ConLeche.structEtaFull, h,
    Bool.false_eq_true, ite_false]; rfl⟩

/-- con-leche: ConLeche/Kernel/Core.lean:374-395 structEtaFull — the shape
fits: the certificate against `y`'s whnf'd io-grade type. -/
theorem FullE.with {d F1 F2 : Nat} {x y v1 v2 : Expr} {r : Bool}
    (h : ConLeche.etaCtorShape env x = true)
    (h1 : ConLeche.inferTypeIO mode eager env F1 d y = .ok v1)
    (h2 : ConLeche.whnf mode eager env F2 d v1 = .ok v2)
    (h3 : EtaWithE mode eager env d x y v2 r) : FullE mode eager env d x y r := by
  obtain ⟨F3, hF3⟩ := h3
  refine ⟨F1 + F2 + F3, ?_⟩
  have e1 : (ConLeche.pureFns mode eager env (F1 + F2 + F3)).inferIO d y = .ok v1 :=
    ConLeche.inferTypeIO_mono (by omega) h1
  have e2 : (ConLeche.pureFns mode eager env (F1 + F2 + F3)).whnf d v1 = .ok v2 :=
    ConLeche.whnf_mono (by omega) h2
  have e3 := structEtaCertWithFueled_mono (show F3 ≤ F1 + F2 + F3 by omega) hF3
  simp only [ConLeche.structEtaFullFueled, ConLeche.structEtaFull, h, ite_true, e1, e2,
    bind, Except.bind]
  exact e3
grind_pattern [bridge_grind] FullE.with =>
  FullE mode eager env d x y r, ConLeche.inferTypeIO mode eager env F1 d y,
  ConLeche.whnf mode eager env F2 d v1, EtaWithE mode eager env d x y v2 r

/-- con-leche: ConLeche/Kernel/Core.lean:411-429 structEtaCert — the shape
fits: `structEtaFull`'s body. -/
theorem EtaCertE.with {d F1 F2 : Nat} {x y v1 v2 : Expr} {r : Bool}
    (h : ConLeche.etaCtorShape env x = true)
    (h1 : ConLeche.inferTypeIO mode eager env F1 d y = .ok v1)
    (h2 : ConLeche.whnf mode eager env F2 d v1 = .ok v2)
    (h3 : EtaWithE mode eager env d x y v2 r) : EtaCertE mode eager env d x y r := by
  obtain ⟨F, hF⟩ := FullE.with h h1 h2 h3
  refine ⟨F, ?_⟩
  simp only [ConLeche.structEtaCertFueled, ConLeche.structEtaCert, h, ite_true]
  exact hF
grind_pattern [bridge_grind] EtaCertE.with =>
  EtaCertE mode eager env d x y r, ConLeche.inferTypeIO mode eager env F1 d y,
  ConLeche.whnf mode eager env F2 d v1, EtaWithE mode eager env d x y v2 r

/-- con-leche: ConLeche/Kernel/Core.lean:411-429 structEtaCert — neither a
full nor a partial η constructor. -/
@[bridge_grind ←] theorem EtaCertE.none {d : Nat} {x y : Expr}
    (h : ConLeche.etaCtorShape env x = false) (hp : ConLeche.etaCtorPartial env x = none) :
    EtaCertE mode eager env d x y false :=
  ⟨0, by simp only [ConLeche.structEtaCertFueled, ConLeche.structEtaCert, h, hp,
    Bool.false_eq_true, ite_false]; rfl⟩

/-- con-leche: ConLeche/Kernel/Core.lean:411-429 structEtaCert — a partially
applied η constructor, `k` arguments short. -/
@[bridge_grind ←] theorem EtaCertE.partial {d k : Nat} {x y : Expr} {r : Bool}
    (h : ConLeche.etaCtorShape env x = false) (hp : ConLeche.etaCtorPartial env x = some k)
    (hr : PartE mode eager env k d x y r) : EtaCertE mode eager env d x y r := by
  obtain ⟨F, hF⟩ := hr
  exact ⟨F, by simp only [ConLeche.structEtaCertFueled, ConLeche.structEtaCert, h, hp,
    Bool.false_eq_true, ite_false]; exact hF⟩

/-- con-leche: ConLeche/Kernel/Core.lean:411-429 structEtaCert — the other
side is not neutral. -/
@[bridge_grind ←] theorem PartE.notNeutral {k d : Nat} {x y : Expr}
    (hn : y.ioNeutral = false) : PartE mode eager env k d x y false :=
  ⟨0, by simp only [hn, Bool.not_false, ite_true]; rfl⟩

/-- con-leche: ConLeche/Kernel/Core.lean:411-429 structEtaCert — the two
io-grade types differ. -/
theorem PartE.nodefeq {k d F1 F2 : Nat} {x y vx vy : Expr}
    (hn : y.ioNeutral = true)
    (h1 : ConLeche.inferTypeIO mode eager env F1 d x = .ok vx)
    (h2 : ConLeche.inferTypeIO mode eager env F2 d y = .ok vy)
    (hq : SimV (ConLeche.isDefEqCore mode eager env) d vy vx false) :
    PartE mode eager env k d x y false := by
  obtain ⟨F3, hF3⟩ := hq
  refine ⟨F1 + F2 + F3, ?_⟩
  have e1 : (ConLeche.pureFns mode eager env (F1 + F2 + F3)).inferIO d x = .ok vx :=
    ConLeche.inferTypeIO_mono (by omega) h1
  have e2 : (ConLeche.pureFns mode eager env (F1 + F2 + F3)).inferIO d y = .ok vy :=
    ConLeche.inferTypeIO_mono (by omega) h2
  have e3 : (ConLeche.pureFns mode eager env (F1 + F2 + F3)).defeq d vy vx = .ok false :=
    ConLeche.isDefEqCore_mono (by omega) hF3
  simp only [hn, Bool.not_true, Bool.false_eq_true, ite_false, e1, e2, e3, bind, Except.bind]
  rfl
grind_pattern [bridge_grind] PartE.nodefeq =>
  PartE mode eager env k d x y false, ConLeche.inferTypeIO mode eager env F1 d x,
  ConLeche.inferTypeIO mode eager env F2 d y, SimV (ConLeche.isDefEqCore mode eager env) d vy vx false

/-- con-leche: ConLeche/Kernel/Core.lean:411-429 structEtaCert — the two
io-grade types agree: the η-expansion decides. -/
theorem PartE.expand {k d F1 F2 : Nat} {x y vx vy : Expr} {r : Bool}
    (hn : y.ioNeutral = true)
    (h1 : ConLeche.inferTypeIO mode eager env F1 d x = .ok vx)
    (h2 : ConLeche.inferTypeIO mode eager env F2 d y = .ok vy)
    (hq : SimV (ConLeche.isDefEqCore mode eager env) d vy vx true)
    (he : ExpandE mode eager env k d x y vx r) :
    PartE mode eager env k d x y r := by
  obtain ⟨F3, hF3⟩ := hq
  obtain ⟨F4, hF4⟩ := he
  refine ⟨F1 + F2 + F3 + F4, ?_⟩
  have e1 : (ConLeche.pureFns mode eager env (F1 + F2 + F3 + F4)).inferIO d x = .ok vx :=
    ConLeche.inferTypeIO_mono (by omega) h1
  have e2 : (ConLeche.pureFns mode eager env (F1 + F2 + F3 + F4)).inferIO d y = .ok vy :=
    ConLeche.inferTypeIO_mono (by omega) h2
  have e3 : (ConLeche.pureFns mode eager env (F1 + F2 + F3 + F4)).defeq d vy vx = .ok true :=
    ConLeche.isDefEqCore_mono (by omega) hF3
  simp only [hn, Bool.not_true, Bool.false_eq_true, ite_false, e1, e2, e3, bind, Except.bind,
    ite_true]
  exact structEtaExpandFueled_mono (by omega) hF4
grind_pattern [bridge_grind] PartE.expand =>
  PartE mode eager env k d x y r, ConLeche.inferTypeIO mode eager env F1 d x,
  ConLeche.inferTypeIO mode eager env F2 d y, SimV (ConLeche.isDefEqCore mode eager env) d vy vx true,
  ExpandE mode eager env k d x y vx r

/-- con-leche: ConLeche/Kernel/Core.lean:397-409 structEtaExpand — no argument
missing: structure η at the full application. -/
@[bridge_grind ←] theorem ExpandE.zero {d : Nat} {x y t : Expr} {r : Bool}
    (h : FullE mode eager env d x y r) : ExpandE mode eager env 0 d x y t r := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, by simp only [ConLeche.structEtaExpandFueled, ConLeche.structEtaExpand]; exact hF⟩

/-- con-leche: ConLeche/Kernel/Core.lean:397-409 structEtaExpand — an argument
missing but the type is no `∀`. -/
theorem ExpandE.nopi {k d : Nat} {x y t : Expr}
    (ht : exprTag t ≠ ETag.forallE) : ExpandE mode eager env (k + 1) d x y t false := by
  refine ⟨0, ?_⟩
  simp only [ConLeche.structEtaExpandFueled]
  cases t <;> first | rfl | (simp only [ConLeche.structEtaExpand]; rfl) | exact absurd rfl ht
grind_pattern [bridge_grind] ExpandE.nopi =>
  ExpandE mode eager env (k + 1) d x y t false, exprTag t

/-- con-leche: ConLeche/Kernel/Core.lean:397-409 structEtaExpand — a `∀`: both
sides applied to the next free variable, one binder down. -/
theorem ExpandE.pi {k d : Nat} {x y t : Expr} {r : Bool}
    (ht : exprTag t = ETag.forallE)
    (hr : ExpandE mode eager env k (d + 1) (.app x (.fvar d (exprBinderType t)))
      (.app y (.fvar d (exprBinderType t)))
      ((exprBody t).instantiate1 (.fvar d (exprBinderType t))) r) :
    ExpandE mode eager env (k + 1) d x y t r := by
  obtain ⟨F, hF⟩ := hr
  refine ⟨F, ?_⟩
  rw [exprTag_forallE ht]
  simp only [ConLeche.structEtaExpandFueled, ConLeche.structEtaExpand]
  exact hF
grind_pattern [bridge_grind] ExpandE.pi =>
  ExpandE mode eager env (k + 1) d x y t r,
  ExpandE mode eager env k (d + 1) (.app x (.fvar d (exprBinderType t)))
    (.app y (.fvar d (exprBinderType t)))
    ((exprBody t).instantiate1 (.fvar d (exprBinderType t))) r

/-- con-leche: ConLeche/Verify/Shift.lean:220 WScoped — a subject applied to
the next free variable (at a `∀`'s domain) is scoped one deeper. -/
theorem wscoped_app_fvar {d : Nat} {x t : Expr} (hx : Expr.WScoped d x)
    (ht : Expr.WScoped d t) (htag : exprTag t = ETag.forallE) :
    Expr.WScoped (d + 1) (.app x (.fvar d (exprBinderType t))) := by
  rw [exprTag_forallE htag] at ht
  simp only [Expr.WScoped] at ht ⊢
  exact ⟨Expr.WScoped.mono (by omega) hx, by omega, ht.1⟩
grind_pattern [bridge_grind] wscoped_app_fvar =>
  Expr.WScoped d x, Expr.WScoped d t, Expr.app x (.fvar d (exprBinderType t))

/-! ### The twin's walks -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:731-757 etaCtorPartial — the
family half: the family a constructor's type ends in is a stored η family
whose projection table's constructor is `c`. -/
@[expose] def etaPartialFam (env : Env) (c : Name) (ty : Expr) : Bool :=
  match ty.piResult.getAppFn with
  | .const T _ =>
    match env.find? T with
    | some (.indInfo _ caps) =>
      match env.findTable? T with
      | some tbl => caps.eta && tbl.ctor == c
      | none => false
    | _ => false
  | _ => false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:731-757 etaCtorPartial — the
reader through its family half. -/
theorem etaCtorPartial_eq (x : Expr) :
    ConLeche.etaCtorPartial env x =
      match x.getAppFn with
      | .const c _ =>
        match env.find? c with
        | some (.ctorInfo cvc cnP cnF) =>
          if x.getAppArgs.length < cnP + cnF then
            if etaPartialFam env c cvc.type then some (cnP + cnF - x.getAppArgs.length)
            else none
          else none
        | _ => none
      | _ => none := by
  simp only [ConLeche.etaCtorPartial, etaPartialFam]
  split
  · rename_i c us
    split
    · rename_i cvc cnP cnF _
      split
      · split
        · rename_i T _ _
          split
          · rename_i cvT caps _
            split
            · rename_i tbl _
              by_cases hg : caps.eta = true ∧ tbl.ctor = c
              · rw [if_pos hg]; simp [hg.1, hg.2]
              · rw [if_neg hg]
                have : (caps.eta && tbl.ctor == c) = false := by
                  cases h1 : caps.eta <;> simp_all
                simp [this]
            · simp
          · simp
        · simp
      · rfl
    · rfl
  · rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:731-757 etaCtorPartial
con-leche: ConLeche/Cached/StateC.lean:97-118 etaCtorPartialC — **THEOREM 1
for the family half of `etaCtorPartial`**: read-only, an equation with
`etaPartialFam`. -/
theorem etaCtorPartialFam_spec (s₀ : AState) (c : NIdx) (cn : Name) (ty : EIdx) (tyE : Expr)
    (hok : CheckOK eager env fe s₀) (hc : denoteN s₀.store.ns c = some cn)
    (hty : denoteE s₀.store ty = some tyE) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.etaCtorPartialFam fe c ty
    ⦃fun r s' => s' = s₀ ∧ r = etaPartialFam env cn tyE; ⊤⦄ := by
  have hwf := hok.state.wf
  unfold ConRon.Arena.etaCtorPartialFam
  refine triple_seq (ExprOps.piResult_spec coreWalkFuel s₀ ty hok.state (by rw [hty]; rfl)) ?_
  rintro pr s1 ⟨rfl, hrelP⟩
  have hpr : denoteE s1.store pr = some tyE.piResult := hrelP tyE hty
  refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s1 pr hok.state (by rw [hpr]; rfl)) ?_
  rintro hd s2 ⟨rfl, hrelF⟩
  have hdd : denoteE s2.store hd = some tyE.piResult.getAppFn := hrelF _ hpr
  obtain ⟨vh, hvh⟩ := denoteE_view hdd
  refine tag_view_bind_triple hvh ?_
    (fun hne => by cases vh <;> first | rfl | exact absurd rfl hne)
  unfold etaPartialFam
  cases vh
  case const T us =>
    obtain ⟨Tn, ls, hgf, hTn, -⟩ := denote_const_inv hwf hvh hdd
    rw [hgf]
    dsimp only
    split
    next icvT icaps hfdT =>
      obtain ⟨dcvT, dcaps, -, hdcaps, hfindT⟩ := env_ind_of_index hok hTn hfdT
      rw [hfindT]
      dsimp only
      have hcapsE : dcaps.eta = icaps.eta := by
        simp only [Frontend.denoteCaps] at hdcaps
        split at hdcaps
        · exact (Option.some.inj hdcaps) ▸ rfl
        · simp at hdcaps
      obtain ⟨htHit, htMiss⟩ := findTable?_at hok hTn
      cases htb : fe.findTable? T with
      | none =>
        rw [htMiss htb]
        exact triple_pureS ⟨rfl, rfl⟩
      | some tbl =>
        obtain ⟨pt, hpt, hfindTb, -⟩ := htHit tbl htb
        rw [hfindTb]
        dsimp only
        rw [hcapsE]
        cases hce : dcaps.eta
        · exact triple_pureS ⟨rfl, rfl⟩
        · refine triple_pureS ⟨rfl, ?_⟩
          rw [denoteN_beq hwf (denoteProjTable_ctor hpt) hc]; rfl
    next hnd =>
      have hnf := env_not_ind_of_index hok hTn (fun v c h => hnd v c h)
      refine triple_pureS ⟨rfl, ?_⟩
      generalize henv : env.find? Tn = o
      match o, henv with
      | some (.indInfo cv caps), henv => exact absurd henv (hnf cv caps)
      | some (.axiomInfo _), _ | some (.thmInfo _), _ | some (.ctorInfo _ _ _), _
      | some (.defnInfo _ _ _), _ | some (.recInfo _ _ _ _ _), _ | none, _ => rfl
  all_goals
    dsimp only
    refine triple_pureS ⟨rfl, ?_⟩
    have hnc := denote_not_const hwf hvh hdd (by intro c us h; cases h)
    generalize tyE.piResult.getAppFn = g at hnc ⊢
    cases g <;> first | rfl | exact absurd rfl (hnc _ _)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:731-757 etaCtorPartial
con-leche: ConLeche/Cached/StateC.lean:97-118 etaCtorPartialC — **THEOREM 1
for `etaCtorPartial`**: read-only, an equation with con-leche's reader. -/
theorem etaCtorPartial_spec (s₀ : AState) (a : EIdx) (x : Expr)
    (hok : CheckOK eager env fe s₀) (hda : denoteE s₀.store a = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.etaCtorPartial fe a
    ⦃fun r s' => s' = s₀ ∧ r = ConLeche.etaCtorPartial env x; ⊤⦄ := by
  have hwf := hok.state.wf
  rw [etaCtorPartial_eq]
  unfold ConRon.Arena.etaCtorPartial
  refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ a hok.state (by rw [hda]; rfl)) ?_
  rintro hd s1 ⟨rfl, hrelF⟩
  have hdd : denoteE s1.store hd = some x.getAppFn := hrelF x hda
  obtain ⟨vh, hvh⟩ := denoteE_view hdd
  refine tag_view_bind_triple hvh ?_
    (fun hne => by cases vh <;> first | rfl | exact absurd rfl hne)
  cases vh
  case const c us =>
    obtain ⟨cn, ls, hgf, hcn, -⟩ := denote_const_inv hwf hvh hdd
    rw [hgf]
    dsimp only
    split
    next icvc cnP cnF hfdc =>
      obtain ⟨dcvc, hdcvc, hfindc⟩ := env_ctor_of_index hok hcn hfdc
      rw [hfindc]
      dsimp only
      refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s1 a hok.state
        (by rw [hda]; rfl)) ?_
      rintro aargs s2 ⟨rfl, hrelA⟩
      have haargs : Frontend.denoteEList s2.store aargs = some x.getAppArgs := hrelA x hda
      have hlenEq : x.getAppArgs.length = aargs.length := denoteEList_len haargs
      rw [hlenEq]
      by_cases hlt : aargs.length < cnP + cnF
      · rw [if_pos hlt, if_pos hlt]
        obtain ⟨-, -, hty⟩ := denoteCV_inv hdcvc
        refine triple_seq (etaCtorPartialFam_spec s2 c cn icvc.type dcvc.type hok hcn hty) ?_
        rintro b s3 ⟨rfl, rfl⟩
        by_cases hb : etaPartialFam env cn dcvc.type = true
        · rw [if_pos hb, if_pos hb]; exact triple_pureS ⟨rfl, rfl⟩
        · rw [if_neg hb, if_neg hb]; exact triple_pureS ⟨rfl, rfl⟩
      · rw [if_neg hlt, if_neg hlt]; exact triple_pureS ⟨rfl, rfl⟩
    next hnd =>
      have hnc := env_not_ctor_of_index hok hcn (fun v p q h => hnd v p q h)
      refine triple_pureS ⟨rfl, ?_⟩
      generalize henv : env.find? cn = o
      match o, henv with
      | some (.ctorInfo cv p q), henv => exact absurd henv (hnc cv p q)
      | some (.axiomInfo _), _ | some (.thmInfo _), _ | some (.indInfo _ _), _
      | some (.defnInfo _ _ _), _ | some (.recInfo _ _ _ _ _), _ | none, _ => rfl
  all_goals
    dsimp only
    refine triple_pureS ⟨rfl, ?_⟩
    have hnc := denote_not_const hwf hvh hdd (by intro c us h; cases h)
    generalize x.getAppFn = g at hnc ⊢
    cases g <;> first | rfl | exact absurd rfl (hnc _ _)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:731-757 etaCtorPartial —
`etaCtorPartial_spec` at whatever the handle denotes. -/
theorem etaCtorPartial_specA (s₀ : AState) (a : EIdx)
    (hok : CheckOK eager env fe s₀) (hda : (denoteE s₀.store a).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.etaCtorPartial fe a
    ⦃fun r s' => s' = s₀ ∧ (denoteE s₀.store a).map (ConLeche.etaCtorPartial env) = some r; ⊤⦄ := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hda
  refine triple_mono (etaCtorPartial_spec s₀ a x hok hx) ?_
  rintro r s' ⟨h1, h2⟩
  exact ⟨h1, by rw [hx, h2]; rfl⟩

/-- con-leche: ConLeche/Kernel/Core.lean:374-395 structEtaFull
con-leche: ConLeche/Cached/CoreC.lean:365-374 structEtaFullI — **THEOREM 1 for
`structEtaFull`**, in answer shape (`PairAns` of `FullE`): the shape gate, then
`b`'s io-grade type, head-normalised, and the certificate against it. -/
theorem structEtaFull_specA {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (hok : CheckOK eager env fe s₀)
    (hda : DenWS d (denoteE s₀.store a)) (hdb : DenWS d (denoteE s₀.store b)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.structEtaFull (coreKnot .verified eager fe id fuel) fe d a b
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        PairAns (FullE .verified eager env d) (denoteE s₀.store a) (denoteE s₀.store b) r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.structEtaFull, ConRon.Arena.structEtaFullAt,
      etaCtorShape_specA (eager := eager) (env := env) (fe := fe),
      KnotSpec.inferIOS hsim, KnotSpec.whnfS hsim, structEtaCertWith_specA henv hsim] <;>
      finish

/-- con-leche: ConLeche/Kernel/Core.lean:397-409 structEtaExpand
con-leche: ConLeche/Cached/CoreC.lean:376-384 structEtaExpandI — **THEOREM 1
for `structEtaExpand`**, in answer shape: both sides applied to the next free
variable along the constructor side's type, `k` binders deep. -/
theorem structEtaExpand_specA {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec eager env fe fuel) :
    ∀ (k d : Nat) (s₀ : AState) (a b ta : EIdx), CheckOK eager env fe s₀ →
      DenWS d (denoteE s₀.store a) → DenWS d (denoteE s₀.store b) →
      DenWS d (denoteE s₀.store ta) →
      ⦃fun s => s = s₀⦄
        ConRon.Arena.structEtaExpand (coreKnot .verified eager fe id fuel) fe k d a b ta
      ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
          TripleAns (ExpandE .verified eager env k d) (denoteE s₀.store a) (denoteE s₀.store b)
            (denoteE s₀.store ta) r; ⊤⦄ := by
  intro k
  induction k with
  | zero =>
    intro d s₀ a b ta hok hda hdb hdt
    sym only [bridge_grind] =>
      vcgen [ConRon.Arena.structEtaExpand, structEtaFull_specA henv hsim] <;> finish
  | succ k ih =>
    intro d s₀ a b ta hok hda hdb hdt
    sym only [bridge_grind] =>
      vcgen [ConRon.Arena.structEtaExpand,
        internE_specC (eager := eager) (env := env) (fe := fe),
        instantiate1Fast_specR (eager := eager) (env := env) (fe := fe), ih] <;>
        -- `gen := 16`: the opened type and the two applied sides are derived from
        -- the type's view, the fvar's denotation and the substitution (as
        -- `formerSortLoop_spec`)
        finish (gen := 16)

/-- con-leche: ConLeche/Kernel/Core.lean:411-429 structEtaCert
con-leche: ConLeche/Cached/CoreC.lean:386-398 structEtaCertI — **THEOREM 1 for
the partial-constructor arm**, in answer shape (`PairAns` of `PartE`): the
other side neutral, the two io-grade types compared, then the η-expansion. -/
theorem structEtaCertPartial_specA {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (d k : Nat) (a b : EIdx) (hok : CheckOK eager env fe s₀)
    (hda : DenWS d (denoteE s₀.store a)) (hdb : DenWS d (denoteE s₀.store b)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.structEtaCertPartial (coreKnot .verified eager fe id fuel) fe d k a b
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        PairAns (PartE .verified eager env k d) (denoteE s₀.store a) (denoteE s₀.store b) r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.structEtaCertPartial,
      ioNeutral_specA (eager := eager) (env := env) (fe := fe),
      KnotSpec.inferIOS hsim, KnotSpec.defeqS hsim,
      structEtaExpand_specA henv hsim] <;> finish

/-- con-leche: ConLeche/Kernel/Core.lean:411-429 structEtaCert
con-leche: ConLeche/Cached/CoreC.lean:386-398 structEtaCertI — the walk in
answer shape (`PairAns` of `EtaCertE`): the full application
(`structEtaFull`'s body past the shape gate) or the partial one. -/
theorem structEtaCert_specA {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (hok : CheckOK eager env fe s₀)
    (hda : DenWS d (denoteE s₀.store a)) (hdb : DenWS d (denoteE s₀.store b)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.structEtaCert (coreKnot .verified eager fe id fuel) fe d a b
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        PairAns (EtaCertE .verified eager env d) (denoteE s₀.store a) (denoteE s₀.store b) r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.structEtaCert, ConRon.Arena.structEtaFullAt,
      etaCtorShape_specA (eager := eager) (env := env) (fe := fe),
      etaCtorPartial_specA (eager := eager) (env := env) (fe := fe),
      KnotSpec.inferIOS hsim, KnotSpec.whnfS hsim, structEtaCertWith_specA henv hsim,
      structEtaCertPartial_specA henv hsim] <;>
      finish

/-! ### Unit-likeness: `isPropType`, `unitLikeShape`, the loop, `structUnitCert` -/

/-- con-leche: ConLeche/Kernel/Core.lean:486-503 structUnitCert — one side's
io-grade type, head-normalised to `w`, at one fuel. -/
def TyRun (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (x w : Expr) : Prop :=
  ∃ F t, ConLeche.inferTypeIO mode eager env F d x = .ok t ∧ ConLeche.whnf mode eager env F d t = .ok w

/-- con-leche: ConLeche/Kernel/Core.lean:486-503 structUnitCert — the two slot
answers of one side, chained by their handles, are its run. -/
theorem TyRun.mk {d : Nat} {x w : Expr} {st₁ st₂ : EStore} {ta wta : EIdx}
    (h1 : SimE (ConLeche.inferTypeIO mode eager env) d x st₁ ta)
    (h2 : SlotAns (ConLeche.whnf mode eager env) d st₂ wta (denoteE st₁ ta)) (hd : denoteE st₂ wta = some w) :
    TyRun mode eager env d x w := by
  obtain ⟨v1, hv1, _, F1, hF1⟩ := h1
  rw [hv1] at h2
  obtain ⟨v2, hv2, _, F2, hF2⟩ := h2
  rw [hv2] at hd; cases hd
  exact ⟨F1 + F2, v1, ConLeche.inferTypeIO_mono (by omega) hF1,
    ConLeche.whnf_mono (by omega) hF2⟩
grind_pattern [bridge_grind] TyRun.mk =>
  SimE (ConLeche.inferTypeIO mode eager env) d x st₁ ta, SlotAns (ConLeche.whnf mode eager env) d st₂ wta (denoteE st₁ ta),
  some w where
  guard denoteE st₂ wta = some w

/-- con-leche: ConLeche/Kernel/Core.lean:486-503 structUnitCert — a side's run,
answered by the handle `h` at the store `st`. -/
def TyRunH (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (y : Expr) (st : EStore) (h : EIdx) :
    Prop :=
  ∃ w, denoteE st h = some w ∧ TyRun mode eager env d y w

/-- con-leche: ConLeche/Kernel/Core.lean:486-503 structUnitCert — the two slot
answers of a side, chained by their handles. -/
theorem TyRunH.mk {d : Nat} {y : Expr} {st₁ st₂ : EStore} {tb wtb : EIdx}
    (h1 : SimE (ConLeche.inferTypeIO mode eager env) d y st₁ tb)
    (h2 : SlotAns (ConLeche.whnf mode eager env) d st₂ wtb (denoteE st₁ tb)) : TyRunH mode eager env d y st₂ wtb := by
  obtain ⟨v1, hv1, _, F1, hF1⟩ := h1
  rw [hv1] at h2
  obtain ⟨v2, hv2, _, F2, hF2⟩ := h2
  exact ⟨v2, hv2, F1 + F2, v1, ConLeche.inferTypeIO_mono (by omega) hF1,
    ConLeche.whnf_mono (by omega) hF2⟩
grind_pattern [bridge_grind] TyRunH.mk =>
  SimE (ConLeche.inferTypeIO mode eager env) d y st₁ tb, SlotAns (ConLeche.whnf mode eager env) d st₂ wtb (denoteE st₁ tb)

/-- con-leche: none — a `Bool` answer about one optional subject (`PairAns`'s
shape at one subject). -/
@[expose] def OneAns (P : Expr → Bool → Prop) : Option Expr → Bool → Prop
  | some x, r => P x r
  | none, _ => True

/-- con-leche: none — `OneAns` at a denoting subject. -/
@[bridge_grind =] theorem OneAns.some_eq (P : Expr → Bool → Prop) (x : Expr) (r : Bool) :
    OneAns P (some x) r = P x r := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:431-436 isPropType — its answer. -/
def PropE (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (x : Expr) (r : Bool) : Prop :=
  SimBOp (fun F => ConLeche.isPropTypeFueled mode eager env F d x) r

/-- con-leche: ConLeche/Kernel/Core.lean:431-436 isPropType — the type's type
is no sort. -/
theorem PropE.nosort {d : Nat} {x : Expr} {st : EStore} {hh : EIdx} {r : Bool}
    (hr : r = false) (hs : TyRunH mode eager env d x st hh) (hwf : StoreWF st)
    (ht : (hh.tag == ETag.sort) = false) : PropE mode eager env d x r := by
  obtain ⟨w, hd, F, t, h1, h2⟩ := hs
  subst hr
  have hn : ∀ l, w ≠ .sort l := by
    intro l hl; subst hl
    have htg := tag_of_denote hwf hd
    simp only [exprTag] at htg
    rw [htg] at ht
    simp at ht
  refine ⟨F, ?_⟩
  have e1 : (ConLeche.pureFns mode eager env F).inferIO d x = .ok t := h1
  have e2 : (ConLeche.pureFns mode eager env F).whnf d t = .ok w := h2
  simp only [ConLeche.isPropTypeFueled, ConLeche.isPropType, e1, e2, bind, Except.bind]
  cases w <;> first | rfl | exact absurd rfl (hn _)
grind_pattern [bridge_grind] PropE.nosort => PropE mode eager env d x r, TyRunH mode eager env d x st hh

/-- con-leche: ConLeche/Kernel/Core.lean:431-436 isPropType — the type's type
is a sort: the verdict is its comparison with `Prop`. -/
theorem PropE.sort {d : Nat} {x : Expr} {st : EStore} {hh : EIdx} {u z : LIdx} {ok : Bool}
    (hs : TyRunH mode eager env d x st hh) (hwf : StoreWF st)
    (hv : st.view hh = some (.sort u)) (hz : denoteL st.ls z = some Level.zero)
    (hq : opt2 Level.isEquiv (denoteL st.ls u) (denoteL st.ls z) = some (some ok)) :
    PropE mode eager env d x ok := by
  obtain ⟨w, hd, F, t, h1, h2⟩ := hs
  obtain ⟨l, rfl, hl⟩ := denote_sort_inv hwf hv hd
  rw [hl, hz] at hq
  refine ⟨F, ?_⟩
  have e1 : (ConLeche.pureFns mode eager env F).inferIO d x = .ok t := h1
  have e2 : (ConLeche.pureFns mode eager env F).whnf d t = .ok (.sort l) := h2
  simp only [ConLeche.isPropTypeFueled, ConLeche.isPropType, e1, e2, bind, Except.bind]
  simp only [opt2, Option.some.injEq] at hq
  simp [ConLeche.liftFueled, hq]; rfl
grind_pattern [bridge_grind] PropE.sort =>
  TyRunH mode eager env d x st hh, ENodeView.sort u,
  opt2 Level.isEquiv (denoteL st.ls u) (denoteL st.ls z), some ok where
  guard st.view hh = some (.sort u)
  guard opt2 Level.isEquiv (denoteL st.ls u) (denoteL st.ls z) = some (some ok)

/-- con-leche: ConLeche/Kernel/Core.lean:431-436 isPropType
con-leche: ConLeche/Cached/CoreC.lean:400-408 isPropTypeI — **THEOREM 1 for
`isPropType`**, in answer shape: the io-grade type, head-normalised, the zero
pin, `lvlEq?` and `liftFueled`. -/
theorem isPropType_specA {fuel : Nat} (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (d : Nat) (a : EIdx) (hok : CheckOK eager env fe s₀)
    (hda : DenWS d (denoteE s₀.store a)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.isPropType (coreKnot .verified eager fe id fuel) d a
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        OneAns (PropE .verified eager env d) (denoteE s₀.store a) r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.isPropType, ConRon.Arena.zeroLevel, KnotSpec.inferIOS hsim,
      KnotSpec.whnfS hsim, pinZeroLevel_spec, lvlEq?_specA (eager := eager) (env := env) (fe := fe),
      liftFueled_spec] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:759-794 unitLikeShape — the
reader's last stage, at the table's constructor `tc`, the instance's levels
`ls` and arguments `xs`. -/
@[expose] def shapeAt (env : Env) (tc : Name) (ls : List Level) (nP nF : Nat) (xs : List Expr) :
    Option (Expr × Nat) :=
  match env.find? tc with
  | some (.ctorInfo cvC _ _) =>
    (ConLeche.unitFieldTele (cvC.type.instantiateLevelParams cvC.levelParams ls) nP xs).map
      fun tele => (tele, nF)
  | _ => none

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:767-794 unitLikeShape — the
reader through its last stage. -/
theorem unitLikeShape_eq (w : Expr) :
    ConLeche.unitLikeShape env w =
      match w.getAppFn with
      | .const S us =>
        match env.find? S with
        | some (.indInfo cvS caps) =>
          if caps.eta = true ∧ us.length = cvS.levelParams.length then
            match env.findTable? S with
            | some tbl =>
              if w.getAppArgs.length = tbl.numParams then
                shapeAt env tbl.ctor us tbl.numParams tbl.numFields w.getAppArgs
              else none
            | none => none
          else none
        | _ => none
      | _ => none := by
  simp only [ConLeche.unitLikeShape, shapeAt]

/-- con-leche: none — the twin's shape answer against con-leche's: both absent,
or both present at the same count with the telescope handle denoting. -/
@[expose] def ShapeAns (st : EStore) : Option (EIdx × Nat) → Option (Expr × Nat) → Prop
  | none, none => True
  | some (h, n), some (t, m) => denoteE st h = some t ∧ n = m
  | _, _ => False

/-- con-leche: none — `ShapeAns` survives the arena's growth. -/
theorem ShapeAns.ext {st st' : EStore} {r : Option (EIdx × Nat)} {o : Option (Expr × Nat)}
    (h : ShapeAns st r o) (hx : Ext st st') : ShapeAns st' r o := by
  match r, o, h with
  | none, none, _ => trivial
  | some (_, _), some (_, _), ⟨hd, hn⟩ => exact ⟨denote_ext hd hx, hn⟩

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:767-794 unitLikeShape
con-leche: ConLeche/Cached/CoreC.lean:424-445 unitLikeShapeF — **THEOREM 1
for the reader's last stage**: the table's constructor, stored, its type at
the instance's levels, the parameters peeled and instantiated in one pass. -/
theorem unitLikeShapeAt_spec (s₀ : AState) (us : LsIdx) (targs : List EIdx) (tctor : NIdx)
    (nP nF : Nat) (ls : List Level) (xs : List Expr) (tc : Name)
    (hok : CheckOK eager env fe s₀) (hus : denoteLs s₀.store.lss us = some ls)
    (hargs : Frontend.denoteEList s₀.store targs = some xs)
    (htc : denoteN s₀.store.ns tctor = some tc) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.unitLikeShapeAt fe us targs tctor nP nF
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        ShapeAns s'.store r (shapeAt env tc ls nP nF xs); ⊤⦄ := by
  unfold ConRon.Arena.unitLikeShapeAt shapeAt
  cases hf : fe.find? tctor with
  | none =>
    rw [IFEnvOK.miss hok.state hok.ienv htc hf]
    exact triple_pureS ⟨hok, Ext.refl _, rfl, trivial⟩
  | some ci =>
  cases ci
  case ctorInfo icvc cnP cnF =>
    obtain ⟨dcvc, hdcvc, hfindc⟩ := env_ctor_of_index hok htc hf
    rw [hfindc]
    dsimp only
    obtain ⟨-, hlps, hty⟩ := denoteCV_inv hdcvc
    refine triple_seq (instLPFast_specC s₀ icvc.levelParams us icvc.type _ ls _ hok hlps hus hty) ?_
    rintro cty s1 ⟨hok1, hx1, hp1, hcty⟩
    refine triple_seq (peelPis_spec s1 hok1.state.wf nP cty _ hcty) ?_
    rintro ob s2 ⟨rfl, hob⟩
    simp only [ConLeche.unitFieldTele]
    cases ob with
    | none =>
      simp only [denoteEO, Option.some.injEq] at hob
      rw [← hob]
      exact triple_pureS ⟨hok1, hx1, hp1, trivial⟩
    | some body =>
      simp only [denoteEO, Option.map_eq_some_iff] at hob
      obtain ⟨B, hB, hpeel⟩ := hob
      rw [← hpeel]
      dsimp only
      have hvec : ExprOps.InstLVec s1.store targs.toArray xs.reverse := by
        unfold ExprOps.InstLVec
        rw [List.reverse_reverse, Array.toList_toArray]
        exact denoteEList_ext hx1 _ _ hargs
      refine triple_seq (instantiateListFast_specC coreWalkFuel s1 body targs.toArray 0
        xs.reverse hok1 hvec (by rw [hB]; rfl)) ?_
      rintro tele s3 ⟨hok3, hx3, hp3, hrel⟩
      refine triple_pureS ⟨hok3, hx1.trans hx3, hp3.trans hp1, ?_⟩
      exact ⟨hrel B hB, rfl⟩
  all_goals
    rename_i hci
    have hnc := env_not_ctor_of_index hok htc (fun v p q h => by rw [hf] at h; cases h)
    refine triple_pureS ⟨hok, Ext.refl _, rfl, ?_⟩
    generalize henv : env.find? tc = o
    match o, henv with
    | some (.ctorInfo cv p q), henv => exact absurd henv (hnc cv p q)
    | some (.axiomInfo _), _ | some (.thmInfo _), _ | some (.indInfo _ _), _
    | some (.defnInfo _ _ _), _ | some (.recInfo _ _ _ _ _), _ | none, _ => trivial

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:767-794 unitLikeShape
con-leche: ConLeche/Cached/CoreC.lean:424-445 unitLikeShapeF — **THEOREM 1
for `unitLikeShape`**: the instance's head family, stored, η at its levels,
its projection table at the instance's parameter count, then the last stage
(`unitLikeShapeAt_spec`). -/
theorem unitLikeShape_spec (s₀ : AState) (w : EIdx) (W : Expr)
    (hok : CheckOK eager env fe s₀) (hdw : denoteE s₀.store w = some W) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.unitLikeShape fe w
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        ShapeAns s'.store r (ConLeche.unitLikeShape env W); ⊤⦄ := by
  have hwf := hok.state.wf
  obtain ⟨rk, hrk⟩ := hok.state.wf
  rw [unitLikeShape_eq]
  unfold ConRon.Arena.unitLikeShape
  refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ w hok.state (by rw [hdw]; rfl)) ?_
  rintro hd s1 ⟨rfl, hrelF⟩
  have hdd : denoteE s1.store hd = some W.getAppFn := hrelF W hdw
  obtain ⟨vh, hvh⟩ := denoteE_view hdd
  refine tag_view_bind_triple hvh ?_
    (fun hne => by cases vh <;> first | rfl | exact absurd rfl hne)
  cases vh
  case const S us =>
    obtain ⟨Sn, ls, hgf, hSn, hus⟩ := denote_const_inv hwf hvh hdd
    rw [hgf]
    dsimp only
    split
    next icvS icaps hfdS =>
      obtain ⟨dcvS, dcaps, hdcvS, hdcaps, hfindS⟩ := env_ind_of_index hok hSn hfdS
      rw [hfindS]
      dsimp only
      have hcapsE : dcaps.eta = icaps.eta := by
        simp only [Frontend.denoteCaps] at hdcaps
        split at hdcaps
        · exact (Option.some.inj hdcaps) ▸ rfl
        · simp at hdcaps
      obtain ⟨-, hlpsS, -⟩ := denoteCV_inv hdcvS
      refine triple_seq (viewLsLen_spec s1 us) ?_
      rintro ol s2 ⟨rfl, hol⟩
      rw [viewLen_of_denoteLs hus] at hol
      subst hol
      dsimp only
      have hg : (icaps.eta = true ∧ ls.length = icvS.levelParams.length) ↔
          (dcaps.eta = true ∧ ls.length = dcvS.levelParams.length) := by
        rw [hcapsE, denoteNList_len hlpsS]
      by_cases hgT : icaps.eta = true ∧ ls.length = icvS.levelParams.length
      · rw [if_pos hgT, if_pos (hg.mp hgT)]
        obtain ⟨htHit, htMiss⟩ := findTable?_at hok hSn
        cases htb : fe.findTable? S with
        | none =>
          rw [htMiss htb]
          exact triple_pureS ⟨hok, Ext.refl _, rfl, trivial⟩
        | some tbl =>
          obtain ⟨pt, hpt, hfindTb, -⟩ := htHit tbl htb
          rw [hfindTb]
          obtain ⟨hnF, hnP⟩ := denoteProjTable_fields hpt
          have hptc := denoteProjTable_ctor hpt
          dsimp only
          refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s2 w hok.state
            (by rw [hdw]; rfl)) ?_
          rintro targs s3 ⟨rfl, hrelA⟩
          have htargs : Frontend.denoteEList s3.store targs = some W.getAppArgs := hrelA W hdw
          have hlenEq : W.getAppArgs.length = targs.length := denoteEList_len htargs
          rw [hlenEq, hnP]
          by_cases hlen : targs.length = tbl.numParams
          · rw [if_pos hlen, if_pos hlen, hnF]
            exact unitLikeShapeAt_spec s3 us targs tbl.ctor tbl.numParams tbl.numFields ls
              W.getAppArgs pt.ctor hok hus htargs hptc
          · rw [if_neg hlen, if_neg hlen]
            exact triple_pureS ⟨hok, Ext.refl _, rfl, trivial⟩
      · rw [if_neg hgT, if_neg (fun h => hgT (hg.mpr h))]
        exact triple_pureS ⟨hok, Ext.refl _, rfl, trivial⟩
    next hnd =>
      have hnf := env_not_ind_of_index hok hSn (fun v c h => hnd v c h)
      refine triple_pureS ⟨hok, Ext.refl _, rfl, ?_⟩
      generalize henv : env.find? Sn = o
      match o, henv with
      | some (.indInfo cv caps), henv => exact absurd henv (hnf cv caps)
      | some (.axiomInfo _), _ | some (.thmInfo _), _ | some (.ctorInfo _ _ _), _
      | some (.defnInfo _ _ _), _ | some (.recInfo _ _ _ _ _), _ | none, _ => trivial
  all_goals
    dsimp only
    refine triple_pureS ⟨hok, Ext.refl _, rfl, ?_⟩
    have hnc := denote_not_const hwf hvh hdd (by intro c us h; cases h)
    generalize W.getAppFn = g at hnc ⊢
    cases g <;> first | trivial | exact absurd rfl (hnc _ _)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:767-794 unitLikeShape — an
instance's field telescope is scoped as the instance is: the stored
constructor's type is closed (`const_ty_hasFvar`), the parameters scoped
(`unitFieldTele_WScoped`). -/
theorem unitLikeShape_WScoped (henv : ConLeche.EnvWF env) {d : Nat} {w tele : Expr} {n : Nat}
    (hw : Expr.WScoped d w) (h : ConLeche.unitLikeShape env w = some (tele, n)) :
    Expr.WScoped d tele := by
  obtain ⟨S, us, cvS, caps, tbl, cvC, nPc, nFc, -, -, -, -, -, -, hfC, -, ht⟩ :=
    ConLeche.unitLikeShape_some h
  exact ConLeche.unitFieldTele_WScoped (const_ty_hasFvar henv hfC us)
    (fun a ha => Expr.WScoped.getAppArgs hw a ha) ht

/-- con-leche: ConLeche/Kernel/Core.lean:472-484 unitLikeLoop — its answer at
the budget `m`. -/
def LoopE (eager : Bool) (env : Env) (m d : Nat) (x : Expr) (r : Bool) : Prop :=
  SimBOp (fun F => ConLeche.unitLikeLoopFueled .verified eager env F m d x) r

/-- con-leche: ConLeche/Kernel/Core.lean:438-453 unitLikeFields — its answer,
the loop at the budget `m` for its `ul`. -/
def FieldsE (eager : Bool) (env : Env) (m n d : Nat) (t : Expr) (r : Bool) : Prop :=
  SimBOp (fun F => ConLeche.unitLikeFields (ConLeche.pureFns .verified eager env F)
    (ConLeche.unitLikeLoopFueled .verified eager env F m) n d t) r

/-- con-leche: ConLeche/Kernel/Core.lean:438-453 unitLikeFields — no field
left. -/
@[bridge_grind ←] theorem FieldsE.zero {m d : Nat} {t : Expr} : FieldsE eager env m 0 d t true :=
  ⟨0, rfl⟩

/-- con-leche: ConLeche/Kernel/Core.lean:438-453 unitLikeFields — a field left
but the telescope is no `∀`. -/
theorem FieldsE.nopi {m n d : Nat} {t : Expr} (ht : exprTag t ≠ ETag.forallE) :
    FieldsE eager env m (n + 1) d t false := by
  refine ⟨0, ?_⟩
  cases t <;> first | rfl | (simp only [ConLeche.unitLikeFields]; rfl) | exact absurd rfl ht
grind_pattern [bridge_grind] FieldsE.nopi => FieldsE eager env m (n + 1) d t false, exprTag t

/-- con-leche: ConLeche/Kernel/Core.lean:438-453 unitLikeFields — the field is a
proposition: the next one, at the opened telescope. -/
theorem FieldsE.prop {m n d : Nat} {t : Expr} {r : Bool} (ht : exprTag t = ETag.forallE)
    (hp : PropE .verified eager env d (exprBinderType t) true)
    (hr : FieldsE eager env m n (d + 1) ((exprBody t).instantiate1 (.fvar d (exprBinderType t))) r) :
    FieldsE eager env m (n + 1) d t r := by
  obtain ⟨F1, hF1⟩ := hp
  obtain ⟨F2, hF2⟩ := hr
  refine ⟨F1 + F2, ?_⟩
  have e1 : ConLeche.isPropType (ConLeche.pureFns .verified eager env (F1 + F2)) d
      (exprBinderType t) = .ok true := isPropTypeFueled_mono (by omega) hF1
  rw [exprTag_forallE ht]
  simp only [ConLeche.unitLikeFields, e1, bind, Except.bind, ite_true]
  exact unitLikeFieldsFueled_mono (by omega) hF2
grind_pattern [bridge_grind] FieldsE.prop =>
  FieldsE eager env m (n + 1) d t r, PropE .verified eager env d (exprBinderType t) true,
  FieldsE eager env m n (d + 1) ((exprBody t).instantiate1 (.fvar d (exprBinderType t))) r

/-- con-leche: ConLeche/Kernel/Core.lean:438-453 unitLikeFields — the field is
no proposition but unit-like: the next one, at the opened telescope. -/
theorem FieldsE.ul {m n d : Nat} {t : Expr} {r : Bool} (ht : exprTag t = ETag.forallE)
    (hp : PropE .verified eager env d (exprBinderType t) false)
    (hu : LoopE eager env m d (exprBinderType t) true)
    (hr : FieldsE eager env m n (d + 1) ((exprBody t).instantiate1 (.fvar d (exprBinderType t))) r) :
    FieldsE eager env m (n + 1) d t r := by
  obtain ⟨F1, hF1⟩ := hp
  obtain ⟨F2, hF2⟩ := hu
  obtain ⟨F3, hF3⟩ := hr
  refine ⟨F1 + F2 + F3, ?_⟩
  have e1 : ConLeche.isPropType (ConLeche.pureFns .verified eager env (F1 + F2 + F3)) d
      (exprBinderType t) = .ok false := isPropTypeFueled_mono (by omega) hF1
  have e2 : ConLeche.unitLikeLoopFueled .verified eager env (F1 + F2 + F3) m d
      (exprBinderType t) = .ok true := unitLikeLoopFueled_mono (by omega) hF2
  rw [exprTag_forallE ht]
  simp only [ConLeche.unitLikeFields, e1, e2, bind, Except.bind, ite_true,
    Bool.false_eq_true, ite_false]
  exact unitLikeFieldsFueled_mono (by omega) hF3
grind_pattern [bridge_grind] FieldsE.ul =>
  FieldsE eager env m (n + 1) d t r, PropE .verified eager env d (exprBinderType t) false,
  LoopE eager env m d (exprBinderType t) true,
  FieldsE eager env m n (d + 1) ((exprBody t).instantiate1 (.fvar d (exprBinderType t))) r

/-- con-leche: ConLeche/Kernel/Core.lean:438-453 unitLikeFields — the field is
neither. -/
theorem FieldsE.no {m n d : Nat} {t : Expr} (ht : exprTag t = ETag.forallE)
    (hp : PropE .verified eager env d (exprBinderType t) false)
    (hu : LoopE eager env m d (exprBinderType t) false) :
    FieldsE eager env m (n + 1) d t false := by
  obtain ⟨F1, hF1⟩ := hp
  obtain ⟨F2, hF2⟩ := hu
  refine ⟨F1 + F2, ?_⟩
  have e1 : ConLeche.isPropType (ConLeche.pureFns .verified eager env (F1 + F2)) d
      (exprBinderType t) = .ok false := isPropTypeFueled_mono (by omega) hF1
  have e2 : ConLeche.unitLikeLoopFueled .verified eager env (F1 + F2) m d
      (exprBinderType t) = .ok false := unitLikeLoopFueled_mono (by omega) hF2
  rw [exprTag_forallE ht]
  simp only [ConLeche.unitLikeFields, e1, e2, bind, Except.bind,
    Bool.false_eq_true, ite_false]
  rfl
grind_pattern [bridge_grind] FieldsE.no =>
  FieldsE eager env m (n + 1) d t false, PropE .verified eager env d (exprBinderType t) false,
  LoopE eager env m d (exprBinderType t) false

/-- con-leche: ConLeche/Kernel/Core.lean:472-484 unitLikeLoop — the budget is
spent: not unit-like. -/
@[bridge_grind ←] theorem LoopE.zero {d : Nat} {x : Expr} : LoopE eager env 0 d x false :=
  ⟨0, rfl⟩

/-- con-leche: ConLeche/Kernel/Core.lean:472-484 unitLikeLoop — a `∀`: its
codomain, opened at the next free variable. -/
theorem LoopE.pi {F m d : Nat} {x w : Expr} {r : Bool}
    (hw : ConLeche.whnf .verified eager env F d x = .ok w) (ht : exprTag w = ETag.forallE)
    (hr : LoopE eager env m (d + 1) ((exprBody w).instantiate1 (.fvar d (exprBinderType w))) r) :
    LoopE eager env (m + 1) d x r := by
  obtain ⟨F₂, hF₂⟩ := hr
  refine ⟨F + F₂, ?_⟩
  have e1 : (ConLeche.pureFns .verified eager env (F + F₂)).whnf d x = .ok w :=
    ConLeche.whnf_mono (by omega) hw
  rw [exprTag_forallE ht] at e1
  simp only [ConLeche.unitLikeLoopFueled, ConLeche.unitLikeLoop, e1, bind, Except.bind]
  exact unitLikeLoopFueled_mono (by omega) hF₂
grind_pattern [bridge_grind] LoopE.pi =>
  LoopE eager env (m + 1) d x r, ConLeche.whnf .verified eager env F d x,
  LoopE eager env m (d + 1) ((exprBody w).instantiate1 (.fvar d (exprBinderType w))) r

/-- con-leche: ConLeche/Kernel/Core.lean:460-470 unitLikeStruct — its answer,
the loop at the budget `m` for its `ul`. -/
def StructE (eager : Bool) (env : Env) (m d : Nat) (w : Expr) (r : Bool) : Prop :=
  SimBOp (fun F => ConLeche.unitLikeStruct (ConLeche.pureFns .verified eager env F)
    (ConLeche.unitLikeLoopFueled .verified eager env F m) env d w) r

/-- con-leche: ConLeche/Kernel/Core.lean:472-484 unitLikeLoop — no `∀`: the
structure arm decides. -/
theorem LoopE.struct {F m d : Nat} {x w : Expr} {r : Bool}
    (hw : ConLeche.whnf .verified eager env F d x = .ok w) (ht : exprTag w ≠ ETag.forallE)
    (hs : StructE eager env m d w r) :
    LoopE eager env (m + 1) d x r := by
  obtain ⟨F₂, hF₂⟩ := hs
  refine ⟨F + F₂, ?_⟩
  have e1 : (ConLeche.pureFns .verified eager env (F + F₂)).whnf d x = .ok w :=
    ConLeche.whnf_mono (by omega) hw
  have e2 : ConLeche.unitLikeStruct (ConLeche.pureFns .verified eager env (F + F₂))
      (ConLeche.unitLikeLoop (ConLeche.pureFns .verified eager env (F + F₂)) env m) env d w
      = .ok r :=
    unitLikeStructFueled_mono (show F₂ ≤ F + F₂ by omega) hF₂
  simp only [ConLeche.unitLikeLoopFueled, ConLeche.unitLikeLoop, e1, bind, Except.bind]
  cases w <;> first | exact e2 | exact absurd rfl ht
grind_pattern [bridge_grind] LoopE.struct =>
  LoopE eager env (m + 1) d x r, ConLeche.whnf .verified eager env F d x, StructE eager env m d w r

/-- con-leche: ConLeche/Kernel/Core.lean:472-484 unitLikeLoop — the twin's loop
statement at the budget `m`. -/
def UnitLoopSpec (eager : Bool) (env : Env) (fe : IFEnv) (fuel m : Nat) : Prop :=
  ∀ (d : Nat) (s₀ : AState) (t : EIdx), CheckOK eager env fe s₀ →
    DenWS d (denoteE s₀.store t) →
    ⦃fun s => s = s₀⦄
      ConRon.Arena.unitLikeLoop (coreKnot .verified eager fe id fuel) fe m d t
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        OneAns (LoopE eager env m d) (denoteE s₀.store t) r; ⊤⦄

/-- con-leche: ConLeche/Kernel/Core.lean:438-453 unitLikeFields
con-leche: ConLeche/Cached/CoreC.lean:410-422 unitLikeFieldsI — **THEOREM 1
for `unitLikeFields`** at the loop's budget `m`, given the loop there: each
field a proposition (`isPropType_specA`) or unit-like (the loop), opened at
the next free variable. -/
theorem unitLikeFields_spec {fuel m : Nat} (hsim : KnotSpec eager env fe fuel)
    (hl : UnitLoopSpec eager env fe fuel m) :
    ∀ (n d : Nat) (s₀ : AState) (t : EIdx), CheckOK eager env fe s₀ →
      DenWS d (denoteE s₀.store t) →
      ⦃fun s => s = s₀⦄
        ConRon.Arena.unitLikeFields (coreKnot .verified eager fe id fuel)
          (ConRon.Arena.unitLikeLoop (coreKnot .verified eager fe id fuel) fe m) n d t
      ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
          OneAns (FieldsE eager env m n d) (denoteE s₀.store t) r; ⊤⦄ := by
  unfold UnitLoopSpec at hl
  intro n
  induction n with
  | zero =>
    intro d s₀ t hok hw
    sym only [bridge_grind] => vcgen [ConRon.Arena.unitLikeFields] <;> finish
  | succ n ih =>
    intro d s₀ t hok hw
    sym only [bridge_grind] =>
      vcgen [ConRon.Arena.unitLikeFields, isPropType_specA hsim, hl,
        internE_specC (eager := eager) (env := env) (fe := fe),
        instantiate1Fast_specR (eager := eager) (env := env) (fe := fe), ih] <;>
        -- `gen := 16`: the opened telescope is four derived steps from its view
        -- (as `formerSortLoop_spec`)
        finish (gen := 16)

/-- con-leche: ConLeche/Kernel/Core.lean:460-470 unitLikeStruct
con-leche: ConLeche/Cached/CoreC.lean:447-452 unitLikeStructI — **THEOREM 1
for `unitLikeStruct`** at the loop's budget `m`: the instance's shape
(`unitLikeShape_spec`), then its fields (`unitLikeFields_spec`). -/
theorem unitLikeStruct_spec {fuel m : Nat} (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec eager env fe fuel) (hl : UnitLoopSpec eager env fe fuel m)
    (d : Nat) (s₀ : AState) (w : EIdx) (hok : CheckOK eager env fe s₀)
    (hw : DenWS d (denoteE s₀.store w)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.unitLikeStruct (coreKnot .verified eager fe id fuel)
        (ConRon.Arena.unitLikeLoop (coreKnot .verified eager fe id fuel) fe m) fe d w
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        OneAns (StructE eager env m d) (denoteE s₀.store w) r; ⊤⦄ := by
  have hfl := unitLikeFields_spec hsim hl
  cases hd : denoteE s₀.store w with
  | none => rw [hd] at hw; exact hw.elim
  | some W =>
  rw [hd] at hw
  unfold ConRon.Arena.unitLikeStruct
  refine triple_seq (unitLikeShape_spec s₀ w W hok hd) ?_
  rintro o s1 ⟨hok1, hx1, hp1, hsh⟩
  generalize hso : ConLeche.unitLikeShape env W = so at hsh
  match o, so, hsh with
  | none, none, _ =>
    refine triple_pureS ⟨hok1, hx1, hp1, ?_⟩
    rw [OneAns.some_eq]
    exact ⟨0, by simp only [ConLeche.unitLikeStruct, hso]; rfl⟩
  | some (th, n), some (tele, n'), ⟨hdt, hn⟩ =>
    subst hn
    dsimp only
    have hwt : Expr.WScoped d tele := unitLikeShape_WScoped henv hw hso
    refine triple_mono (hfl n d s1 th hok1 (by rw [hdt]; exact hwt)) ?_
    rintro r s2 ⟨hok2, hx2, hp2, hr⟩
    rw [hdt, OneAns.some_eq] at hr
    refine ⟨hok2, hx1.trans hx2, hp2.trans hp1, ?_⟩
    rw [OneAns.some_eq]
    obtain ⟨F, hF⟩ := hr
    exact ⟨F, by simp only [ConLeche.unitLikeStruct, hso]; exact hF⟩

/-- con-leche: ConLeche/Kernel/Core.lean:472-484 unitLikeLoop
con-leche: ConLeche/Cached/CoreC.lean:454-463 unitLikeLoopI — **THEOREM 1 for
`unitLikeLoop`**: the head normal form's `∀`s opened one by one, then the
structure arm (`unitLikeStruct_spec`, one budget down). -/
theorem unitLikeLoop_spec {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec eager env fe fuel) : ∀ m, UnitLoopSpec eager env fe fuel m := by
  intro m
  induction m with
  | zero =>
    intro d s₀ t hok hw
    sym only [bridge_grind] => vcgen [ConRon.Arena.unitLikeLoop] <;> finish
  | succ m ih =>
    have hst := unitLikeStruct_spec henv hsim ih
    unfold UnitLoopSpec at ih
    intro d s₀ t hok hw
    sym only [bridge_grind] =>
      vcgen [ConRon.Arena.unitLikeLoop, KnotSpec.whnfS hsim,
        internE_specC (eager := eager) (env := env) (fe := fe),
        instantiate1Fast_specR (eager := eager) (env := env) (fe := fe), ih, hst] <;>
        -- `gen := 16`: the opened codomain is four derived steps from the head-normal
        -- form (as `formerSortLoop_spec`)
        finish (gen := 16)

/-- con-leche: ConLeche/Kernel/Core.lean:458 unitLikeFuel — the twin's budget is
con-leche's. -/
theorem unitLikeFuel_eq : ConRon.Arena.unitLikeFuel = ConLeche.unitLikeFuel := by
  unfold ConRon.Arena.unitLikeFuel ConLeche.unitLikeFuel; rfl

/-- con-leche: ConLeche/Kernel/Core.lean:486-503 structUnitCert — its first
side's guard: a side whose type is a `∀` must be neutral. -/
@[expose] def unitSideOk (w x : Expr) : Bool := !(w.isForallE && !x.ioNeutral)

/-- con-leche: ConLeche/Kernel/Core.lean:486-503 structUnitCert — the first
side's guard fails. -/
theorem UnitCertE.guardA {d : Nat} {x y w : Expr} {r : Bool} (hr : r = false)
    (hs : TyRun mode eager env d x w) (hg : unitSideOk w x = false) :
    UnitCertE mode eager env d x y r := by
  obtain ⟨F, t, h1, h2⟩ := hs
  subst hr
  have e1 : (ConLeche.pureFns mode eager env F).inferIO d x = .ok t := h1
  have e2 : (ConLeche.pureFns mode eager env F).whnf d t = .ok w := h2
  have hg' : (w.isForallE && !x.ioNeutral) = true := by simpa [unitSideOk] using hg
  exact ⟨F, by simp only [ConLeche.structUnitCertFueled, ConLeche.structUnitCert, e1, e2,
    bind, Except.bind, hg', ite_true]; rfl⟩
grind_pattern [bridge_grind] UnitCertE.guardA =>
  UnitCertE mode eager env d x y r, TyRun mode eager env d x w, unitSideOk w x

/-- con-leche: ConLeche/Kernel/Core.lean:486-503 structUnitCert — the first
side's type is not unit-like. -/
theorem UnitCertE.notUnit {d : Nat} {x y w : Expr} {r : Bool} (hr : r = false)
    (hs : TyRun .verified eager env d x w) (hg : unitSideOk w x = true)
    (hu : LoopE eager env ConLeche.unitLikeFuel d w false) :
    UnitCertE .verified eager env d x y r := by
  obtain ⟨F1, t, h1, h2⟩ := hs
  obtain ⟨F2, hF2⟩ := hu
  subst hr
  have e1 : (ConLeche.pureFns .verified eager env (F1 + F2)).inferIO d x = .ok t :=
    ConLeche.inferTypeIO_mono (by omega) h1
  have e2 : (ConLeche.pureFns .verified eager env (F1 + F2)).whnf d t = .ok w :=
    ConLeche.whnf_mono (by omega) h2
  have e3 : ConLeche.unitLikeLoop (ConLeche.pureFns .verified eager env (F1 + F2)) env
      ConLeche.unitLikeFuel d w = .ok false := unitLikeLoopFueled_mono (by omega) hF2
  have hg' : (w.isForallE && !x.ioNeutral) = false := by simpa [unitSideOk] using hg
  exact ⟨F1 + F2, by simp only [ConLeche.structUnitCertFueled, ConLeche.structUnitCert, e1, e2,
    e3, bind, Except.bind, hg', Bool.false_eq_true, ite_false]; rfl⟩
grind_pattern [bridge_grind] UnitCertE.notUnit =>
  UnitCertE .verified eager env d x y r, TyRun .verified eager env d x w,
  LoopE eager env ConLeche.unitLikeFuel d w false

/-- con-leche: ConLeche/Kernel/Core.lean:486-503 structUnitCert — unit-like,
but the second side's guard fails. -/
theorem UnitCertE.guardB {d : Nat} {x y w w2 : Expr} {r : Bool} (hr : r = false)
    (hs : TyRun .verified eager env d x w) (hg : unitSideOk w x = true)
    (hu : LoopE eager env ConLeche.unitLikeFuel d w true)
    (hs2 : TyRun .verified eager env d y w2) (hg2 : unitSideOk w2 y = false) :
    UnitCertE .verified eager env d x y r := by
  obtain ⟨F1, t, h1, h2⟩ := hs
  obtain ⟨F2, hF2⟩ := hu
  obtain ⟨F3, t2, h3, h4⟩ := hs2
  subst hr
  have e1 : (ConLeche.pureFns .verified eager env (F1 + F2 + F3)).inferIO d x = .ok t :=
    ConLeche.inferTypeIO_mono (by omega) h1
  have e2 : (ConLeche.pureFns .verified eager env (F1 + F2 + F3)).whnf d t = .ok w :=
    ConLeche.whnf_mono (by omega) h2
  have e3 : ConLeche.unitLikeLoop (ConLeche.pureFns .verified eager env (F1 + F2 + F3)) env
      ConLeche.unitLikeFuel d w = .ok true := unitLikeLoopFueled_mono (by omega) hF2
  have e4 : (ConLeche.pureFns .verified eager env (F1 + F2 + F3)).inferIO d y = .ok t2 :=
    ConLeche.inferTypeIO_mono (by omega) h3
  have e5 : (ConLeche.pureFns .verified eager env (F1 + F2 + F3)).whnf d t2 = .ok w2 :=
    ConLeche.whnf_mono (by omega) h4
  have hg' : (w.isForallE && !x.ioNeutral) = false := by simpa [unitSideOk] using hg
  have hg2' : (w2.isForallE && !y.ioNeutral) = true := by simpa [unitSideOk] using hg2
  exact ⟨F1 + F2 + F3, by simp only [ConLeche.structUnitCertFueled, ConLeche.structUnitCert,
    e1, e2, e3, e4, e5, bind, Except.bind, hg', hg2', Bool.false_eq_true, ite_false,
    ite_true]; rfl⟩
grind_pattern [bridge_grind] UnitCertE.guardB =>
  UnitCertE .verified eager env d x y r, TyRun .verified eager env d x w,
  LoopE eager env ConLeche.unitLikeFuel d w true, TyRun .verified eager env d y w2,
  unitSideOk w2 y

/-- con-leche: ConLeche/Kernel/Core.lean:486-503 structUnitCert — unit-like,
both guards pass: the two types are compared. -/
theorem UnitCertE.defeq {d : Nat} {x y w w2 : Expr} {r : Bool}
    (hs : TyRun .verified eager env d x w) (hg : unitSideOk w x = true)
    (hu : LoopE eager env ConLeche.unitLikeFuel d w true)
    (hs2 : TyRun .verified eager env d y w2) (hg2 : unitSideOk w2 y = true)
    (hq : SimV (ConLeche.isDefEqCore .verified eager env) d w w2 r) :
    UnitCertE .verified eager env d x y r := by
  obtain ⟨F1, t, h1, h2⟩ := hs
  obtain ⟨F2, hF2⟩ := hu
  obtain ⟨F3, t2, h3, h4⟩ := hs2
  obtain ⟨F4, hF4⟩ := hq
  have e1 : (ConLeche.pureFns .verified eager env (F1 + F2 + F3 + F4)).inferIO d x = .ok t :=
    ConLeche.inferTypeIO_mono (by omega) h1
  have e2 : (ConLeche.pureFns .verified eager env (F1 + F2 + F3 + F4)).whnf d t = .ok w :=
    ConLeche.whnf_mono (by omega) h2
  have e3 : ConLeche.unitLikeLoop (ConLeche.pureFns .verified eager env (F1 + F2 + F3 + F4))
      env ConLeche.unitLikeFuel d w = .ok true := unitLikeLoopFueled_mono (by omega) hF2
  have e4 : (ConLeche.pureFns .verified eager env (F1 + F2 + F3 + F4)).inferIO d y = .ok t2 :=
    ConLeche.inferTypeIO_mono (by omega) h3
  have e5 : (ConLeche.pureFns .verified eager env (F1 + F2 + F3 + F4)).whnf d t2 = .ok w2 :=
    ConLeche.whnf_mono (by omega) h4
  have e6 : (ConLeche.pureFns .verified eager env (F1 + F2 + F3 + F4)).defeq d w w2 = .ok r :=
    ConLeche.isDefEqCore_mono (by omega) hF4
  have hg' : (w.isForallE && !x.ioNeutral) = false := by simpa [unitSideOk] using hg
  have hg2' : (w2.isForallE && !y.ioNeutral) = false := by simpa [unitSideOk] using hg2
  exact ⟨F1 + F2 + F3 + F4, by simp only [ConLeche.structUnitCertFueled, ConLeche.structUnitCert,
    e1, e2, e3, e4, e5, e6, bind, Except.bind, hg', hg2', Bool.false_eq_true, ite_false,
    ite_true]⟩
grind_pattern [bridge_grind] UnitCertE.defeq =>
  UnitCertE .verified eager env d x y r, TyRun .verified eager env d x w,
  LoopE eager env ConLeche.unitLikeFuel d w true, TyRun .verified eager env d y w2,
  SimV (ConLeche.isDefEqCore .verified eager env) d w w2 r

/-- con-leche: none — `unitSideOk` at a handle's denotation, read off the
handle's tag (`ExprOps.isForallE_rel`). -/
theorem unitSideOk_eq {st : EStore} (hwf : StoreWF st) {h : EIdx} {w x : Expr}
    (hd : denoteE st h = some w) : unitSideOk w x = !(isForallE h && !x.ioNeutral) := by
  unfold unitSideOk
  rw [ExprOps.isForallE_rel hwf hd]
grind_pattern [bridge_grind] unitSideOk_eq => unitSideOk w x, denoteE st h, StoreWF st where
  guard denoteE st h = some w

/-- con-leche: ConLeche/Kernel/Core.lean:486-503 structUnitCert
con-leche: ConLeche/Cached/CoreC.lean:465-476 structUnitCertI — **THEOREM 1
for `structUnitCert`**, in answer shape (`PairAns` of `UnitCertE`): each
side's io-grade type, head-normalised, its neutrality guard (`ioNeutral`), the
unit-like loop at con-leche's budget, and the knot's `defeq`. -/
theorem structUnitCert_specA {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (hok : CheckOK eager env fe s₀)
    (hda : DenWS d (denoteE s₀.store a)) (hdb : DenWS d (denoteE s₀.store b)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.structUnitCert (coreKnot .verified eager fe id fuel) fe d a b
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        PairAns (UnitCertE .verified eager env d) (denoteE s₀.store a) (denoteE s₀.store b) r; ⊤⦄ := by
  have hloop := unitLikeLoop_spec henv hsim ConRon.Arena.unitLikeFuel
  unfold UnitLoopSpec at hloop
  rw [unitLikeFuel_eq] at hloop
  unfold ConRon.Arena.structUnitCert
  rw [unitLikeFuel_eq]
  sym only [bridge_grind] =>
    vcgen [KnotSpec.inferIOS hsim, KnotSpec.whnfS hsim,
      ioNeutral_specA (eager := eager) (env := env) (fe := fe), hloop,
      KnotSpec.defeqS hsim] <;> finish

/-! ### `proofIrrel` in answer shape -/

/-- con-leche: ConLeche/Kernel/Core.lean:298-312 proofIrrel — one side's run
up to its sort: the io-grade type of `x`, its io-grade type, head-normalised,
at one fuel, answered by the handle `hh` at the store `st`. -/
def SortRun (mode : CheckMode) (eager : Bool) (env : Env) (d : Nat) (x : Expr) (st : EStore) (hh : EIdx) :
    Prop :=
  ∃ F ta tta w, ConLeche.inferTypeIO mode eager env F d x = .ok ta ∧
    ConLeche.inferTypeIO mode eager env F d ta = .ok tta ∧ ConLeche.whnf mode eager env F d tta = .ok w ∧
    denoteE st hh = some w

/-- con-leche: ConLeche/Kernel/Core.lean:298-312 proofIrrel — the three slot
answers of one side, chained by their handles, are its run. -/
theorem SortRun.mk {d : Nat} {x : Expr} {st₁ st₂ st₃ : EStore} {ta tta hh : EIdx}
    (h1 : SimE (ConLeche.inferTypeIO mode eager env) d x st₁ ta)
    (h2 : SlotAns (ConLeche.inferTypeIO mode eager env) d st₂ tta (denoteE st₁ ta))
    (h3 : SlotAns (ConLeche.whnf mode eager env) d st₃ hh (denoteE st₂ tta)) : SortRun mode eager env d x st₃ hh := by
  obtain ⟨v1, hv1, _, F1, hF1⟩ := h1
  rw [hv1] at h2
  obtain ⟨v2, hv2, _, F2, hF2⟩ := h2
  rw [hv2] at h3
  obtain ⟨v3, hv3, _, F3, hF3⟩ := h3
  exact ⟨F1 + F2 + F3, v1, v2, v3, ConLeche.inferTypeIO_mono (by omega) hF1,
    ConLeche.inferTypeIO_mono (by omega) hF2, ConLeche.whnf_mono (by omega) hF3, hv3⟩
grind_pattern [bridge_grind] SortRun.mk =>
  SimE (ConLeche.inferTypeIO mode eager env) d x st₁ ta, SlotAns (ConLeche.inferTypeIO mode eager env) d st₂ tta (denoteE st₁ ta),
  SlotAns (ConLeche.whnf mode eager env) d st₃ hh (denoteE st₂ tta)

/-- con-leche: none — a run's answer is a sort at its view's level, or not a
sort at all (`denote_sort_inv`, `denote_not_sort`). -/
theorem SortRun.view {d : Nat} {x : Expr} {st : EStore} {hh : EIdx}
    (hs : SortRun mode eager env d x st hh) (hwf : StoreWF st) :
    ∃ F ta tta w, ConLeche.inferTypeIO mode eager env F d x = .ok ta ∧
      ConLeche.inferTypeIO mode eager env F d ta = .ok tta ∧ ConLeche.whnf mode eager env F d tta = .ok w ∧
      (hh.tag = ETag.sort → ∃ u l, st.view hh = some (.sort u) ∧
        denoteL st.ls u = some l ∧ w = .sort l) ∧
      (hh.tag ≠ ETag.sort → ∀ l, w ≠ .sort l) := by
  obtain ⟨F, ta, tta, w, h1, h2, h3, hd⟩ := hs
  refine ⟨F, ta, tta, w, h1, h2, h3, fun ht => ?_, fun ht l hl => ?_⟩
  · obtain ⟨v, hv⟩ := denoteE_view hd
    have ht' : v.tagOf = ETag.sort := by rw [← EStore.tagOf_of_view hv]; exact ht
    rw [ENodeView.tagOf_sort ht'] at hv
    obtain ⟨l, rfl, hl⟩ := denote_sort_inv hwf hv hd
    exact ⟨_, l, hv, hl, rfl⟩
  · subst hl
    exact ht (by rw [tag_of_denote hwf hd]; rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:298-312 proofIrrel — `x`'s side is
not a sort. -/
theorem PIrrelE.nosort_a {d : Nat} {x y : Expr} {st : EStore} {hh : EIdx} {r : Bool}
    (hr : r = false) (hs : SortRun mode eager env d x st hh) (hwf : StoreWF st)
    (ht : (hh.tag == ETag.sort) = false) : PIrrelE mode eager env d x y r := by
  obtain ⟨F, ta, tta, w, h1, h3, h4, _, hn⟩ := hs.view hwf
  subst hr
  exact ⟨F, proofIrrel_nosort_a h1 h3 h4 (hn (by simpa using ht))⟩
grind_pattern [bridge_grind] PIrrelE.nosort_a =>
  PIrrelE mode eager env d x y r, SortRun mode eager env d x st hh

/-- con-leche: ConLeche/Kernel/Core.lean:298-312 proofIrrel — `x`'s side is
a sort whose level compares (`okA`), `y`'s is not a sort. -/
theorem PIrrelE.nosort_b {d : Nat} {x y : Expr} {st st2 : EStore} {hh hh2 : EIdx}
    {u z : LIdx} {okA r : Bool} (hr : r = false)
    (hs : SortRun mode eager env d x st hh) (hwf : StoreWF st)
    (hv : st.view hh = some (.sort u)) (hz : denoteL st.ls z = some Level.zero)
    (hq : opt2 Level.isEquiv (denoteL st.ls u) (denoteL st.ls z) = some (some okA))
    (hs2 : SortRun mode eager env d y st2 hh2) (hwf2 : StoreWF st2)
    (ht2 : (hh2.tag == ETag.sort) = false) : PIrrelE mode eager env d x y r := by
  obtain ⟨F1, ta, tta, w, h1, h3, h4, hsrt, _⟩ := hs.view hwf
  obtain ⟨F2, tb, ttb, w2, h6, h7, h8, _, hn⟩ := hs2.view hwf2
  obtain ⟨u', l, hv', hl, rfl⟩ := hsrt (EStore.tagOf_of_view hv)
  rw [hv] at hv'; cases hv'
  rw [hl, hz] at hq
  subst hr
  exact ⟨F1 + F2, proofIrrel_nosort_b (ConLeche.inferTypeIO_mono (by omega) h1)
    (ConLeche.inferTypeIO_mono (by omega) h3) (ConLeche.whnf_mono (by omega) h4)
    (Option.some.inj hq)
    (ConLeche.inferTypeIO_mono (by omega) h6) (ConLeche.inferTypeIO_mono (by omega) h7)
    (ConLeche.whnf_mono (by omega) h8) (hn (by simpa using ht2))⟩
grind_pattern [bridge_grind] PIrrelE.nosort_b =>
  PIrrelE mode eager env d x y r, SortRun mode eager env d x st hh, SortRun mode eager env d y st2 hh2,
  ENodeView.sort u, opt2 Level.isEquiv (denoteL st.ls u) (denoteL st.ls z), some okA where
  guard st.view hh = some (.sort u)
  guard opt2 Level.isEquiv (denoteL st.ls u) (denoteL st.ls z) = some (some okA)

/-- con-leche: ConLeche/Kernel/Core.lean:298-312 proofIrrel — both sides are
sorts: the verdict is the two level comparisons. -/
theorem PIrrelE.sorts {d : Nat} {x y : Expr} {st st2 : EStore} {hh hh2 : EIdx}
    {u u2 z z2 : LIdx} {okA okB : Bool}
    (hs : SortRun mode eager env d x st hh) (hwf : StoreWF st)
    (hv : st.view hh = some (.sort u)) (hz : denoteL st.ls z = some Level.zero)
    (hq : opt2 Level.isEquiv (denoteL st.ls u) (denoteL st.ls z) = some (some okA))
    (hs2 : SortRun mode eager env d y st2 hh2) (hwf2 : StoreWF st2)
    (hv2 : st2.view hh2 = some (.sort u2)) (hz2 : denoteL st2.ls z2 = some Level.zero)
    (hq2 : opt2 Level.isEquiv (denoteL st2.ls u2) (denoteL st2.ls z2) = some (some okB)) :
    PIrrelE mode eager env d x y (okA && okB) := by
  obtain ⟨F1, ta, tta, w, h1, h3, h4, hsrt, _⟩ := hs.view hwf
  obtain ⟨F2, tb, ttb, w2, h6, h7, h8, hsrt2, _⟩ := hs2.view hwf2
  obtain ⟨u', l, hv', hl, rfl⟩ := hsrt (EStore.tagOf_of_view hv)
  obtain ⟨u2', l2, hv2', hl2, rfl⟩ := hsrt2 (EStore.tagOf_of_view hv2)
  rw [hv] at hv'; cases hv'
  rw [hv2] at hv2'; cases hv2'
  rw [hl, hz] at hq
  rw [hl2, hz2] at hq2
  exact ⟨F1 + F2, proofIrrel_sorts (ConLeche.inferTypeIO_mono (by omega) h1)
    (ConLeche.inferTypeIO_mono (by omega) h3) (ConLeche.whnf_mono (by omega) h4)
    (Option.some.inj hq)
    (ConLeche.inferTypeIO_mono (by omega) h6) (ConLeche.inferTypeIO_mono (by omega) h7)
    (ConLeche.whnf_mono (by omega) h8) (Option.some.inj hq2)⟩
grind_pattern [bridge_grind] PIrrelE.sorts =>
  SortRun mode eager env d x st hh, SortRun mode eager env d y st2 hh2,
  opt2 Level.isEquiv (denoteL st.ls u) (denoteL st.ls z), some okA,
  opt2 Level.isEquiv (denoteL st2.ls u2) (denoteL st2.ls z2), some okB where
  guard opt2 Level.isEquiv (denoteL st.ls u) (denoteL st.ls z) = some (some okA)
  guard opt2 Level.isEquiv (denoteL st2.ls u2) (denoteL st2.ls z2) = some (some okB)

/-- con-leche: ConLeche/Kernel/Core.lean:327-341 proofIrrel — the walk in
answer shape (`PairAns` of `PIrrelE`): `inferIO`/`whnf` twice per side, the
zero pin, `lvlEq?` and `liftFueled`, over the three exits above. -/
theorem proofIrrel_specA {fuel : Nat} (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (hok : CheckOK eager env fe s₀)
    (hda : DenWS d (denoteE s₀.store a)) (hdb : DenWS d (denoteE s₀.store b)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.proofIrrel (coreKnot .verified eager fe id fuel) fe d a b
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        PairAns (PIrrelE .verified eager env d) (denoteE s₀.store a) (denoteE s₀.store b) r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.proofIrrel, ConRon.Arena.zeroLevel, KnotSpec.inferIOS hsim,
      KnotSpec.whnfS hsim, pinZeroLevel_spec, lvlEq?_specA (eager := eager) (env := env) (fe := fe),
      liftFueled_spec] <;> finish

/-! ## 2. The pure side: `stuckIrrel` at its four exits -/

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — the first η
direction certifies. -/
theorem stuckIrrelFueled_eta1 {F d : Nat} {x y : Expr}
    (h : ConLeche.structEtaCertFueled mode eager env F d x y = .ok true) :
    ConLeche.stuckIrrelFueled mode eager env F d x y = .ok true := by
  have h' : ConLeche.structEtaCert (ConLeche.pureFns mode eager env F) env d x y
      = .ok true := h
  simp only [ConLeche.stuckIrrelFueled, ConLeche.stuckIrrel, h', bind,
    Except.bind, ite_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — the second η
direction certifies. -/
theorem stuckIrrelFueled_eta2 {F d : Nat} {x y : Expr}
    (h1 : ConLeche.structEtaCertFueled mode eager env F d x y = .ok false)
    (h2 : ConLeche.structEtaCertFueled mode eager env F d y x = .ok true) :
    ConLeche.stuckIrrelFueled mode eager env F d x y = .ok true := by
  have h1' : ConLeche.structEtaCert (ConLeche.pureFns mode eager env F) env d x y
      = .ok false := h1
  have h2' : ConLeche.structEtaCert (ConLeche.pureFns mode eager env F) env d y x
      = .ok true := h2
  simp only [ConLeche.stuckIrrelFueled, ConLeche.stuckIrrel, h1', h2', bind,
    Except.bind, Bool.false_eq_true, ite_false, ite_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — unit-likeness
certifies. -/
theorem stuckIrrelFueled_unit {F d : Nat} {x y : Expr}
    (h1 : ConLeche.structEtaCertFueled mode eager env F d x y = .ok false)
    (h2 : ConLeche.structEtaCertFueled mode eager env F d y x = .ok false)
    (h3 : ConLeche.structUnitCertFueled mode eager env F d x y = .ok true) :
    ConLeche.stuckIrrelFueled mode eager env F d x y = .ok true := by
  have h1' : ConLeche.structEtaCert (ConLeche.pureFns mode eager env F) env d x y
      = .ok false := h1
  have h2' : ConLeche.structEtaCert (ConLeche.pureFns mode eager env F) env d y x
      = .ok false := h2
  have h3' : ConLeche.structUnitCert (ConLeche.pureFns mode eager env F) env d x y
      = .ok true := h3
  simp only [ConLeche.stuckIrrelFueled, ConLeche.stuckIrrel, h1', h2', h3',
    bind, Except.bind, Bool.false_eq_true, ite_false, ite_true, pure,
    Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — none of the
three certifies, so proof irrelevance decides. -/
theorem stuckIrrelFueled_proof {F d : Nat} {x y : Expr} {r : Bool}
    (h1 : ConLeche.structEtaCertFueled mode eager env F d x y = .ok false)
    (h2 : ConLeche.structEtaCertFueled mode eager env F d y x = .ok false)
    (h3 : ConLeche.structUnitCertFueled mode eager env F d x y = .ok false)
    (h4 : ConLeche.proofIrrelFueled mode eager env F d x y = .ok r) :
    ConLeche.stuckIrrelFueled mode eager env F d x y = .ok r := by
  have h1' : ConLeche.structEtaCert (ConLeche.pureFns mode eager env F) env d x y
      = .ok false := h1
  have h2' : ConLeche.structEtaCert (ConLeche.pureFns mode eager env F) env d y x
      = .ok false := h2
  have h3' : ConLeche.structUnitCert (ConLeche.pureFns mode eager env F) env d x y
      = .ok false := h3
  have h4' : ConLeche.proofIrrel (ConLeche.pureFns mode eager env F) d x y
      = .ok r := h4
  simp only [ConLeche.stuckIrrelFueled, ConLeche.stuckIrrel, h1', h2', h3',
    h4', bind, Except.bind, Bool.false_eq_true, ite_false]

/-! ## 3. The walk

`stuckIrrel`'s four exits as `grind` lemmas over the children's named
answers (the fuel merge inside each), and the children in answer shape at
their subjects' denotations (`PairAns`). -/

/-- con-leche: ConLeche/Kernel/Core.lean:487-492 stuckIrrel — the first η
direction certifies. -/
@[bridge_grind ←] theorem StuckE.eta1 {d : Nat} {x y : Expr}
    (h : EtaCertE mode eager env d x y true) : StuckE mode eager env d x y true := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, stuckIrrelFueled_eta1 hF⟩

/-- con-leche: ConLeche/Kernel/Core.lean:487-492 stuckIrrel — the second η
direction certifies. -/
@[bridge_grind ←] theorem StuckE.eta2 {d : Nat} {x y : Expr}
    (h1 : EtaCertE mode eager env d x y false) (h2 : EtaCertE mode eager env d y x true) :
    StuckE mode eager env d x y true := by
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  exact ⟨max F1 F2, stuckIrrelFueled_eta2
    (structEtaCertFueled_mono (Nat.le_max_left _ _) hF1)
    (structEtaCertFueled_mono (Nat.le_max_right _ _) hF2)⟩

/-- con-leche: ConLeche/Kernel/Core.lean:487-492 stuckIrrel — unit-likeness
certifies. -/
@[bridge_grind ←] theorem StuckE.unit {d : Nat} {x y : Expr}
    (h1 : EtaCertE mode eager env d x y false) (h2 : EtaCertE mode eager env d y x false)
    (h3 : UnitCertE mode eager env d x y true) : StuckE mode eager env d x y true := by
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  obtain ⟨F3, hF3⟩ := h3
  exact ⟨F1 + F2 + F3, stuckIrrelFueled_unit
    (structEtaCertFueled_mono (by omega) hF1) (structEtaCertFueled_mono (by omega) hF2)
    (structUnitCertFueled_mono (by omega) hF3)⟩

/-- con-leche: ConLeche/Kernel/Core.lean:487-492 stuckIrrel — none of the
three certifies, so proof irrelevance decides. -/
@[bridge_grind ←] theorem StuckE.proof {d : Nat} {x y : Expr} {r : Bool}
    (h1 : EtaCertE mode eager env d x y false) (h2 : EtaCertE mode eager env d y x false)
    (h3 : UnitCertE mode eager env d x y false) (h4 : PIrrelE mode eager env d x y r) :
    StuckE mode eager env d x y r := by
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  obtain ⟨F3, hF3⟩ := h3
  obtain ⟨F4, hF4⟩ := h4
  exact ⟨F1 + F2 + F3 + F4, stuckIrrelFueled_proof
    (structEtaCertFueled_mono (by omega) hF1) (structEtaCertFueled_mono (by omega) hF2)
    (structUnitCertFueled_mono (by omega) hF3) (proofIrrelFueled_mono (by omega) hF4)⟩

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — the walk in
answer shape (`StuckE`). -/
theorem stuckIrrel_specA {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK eager env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.stuckIrrel (coreKnot .verified eager fe id fuel) fe d a b
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ StuckE .verified eager env d x y r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.stuckIrrel, structEtaCert_specA henv hsim,
      structUnitCert_specA henv hsim, proofIrrel_specA hsim] <;> finish

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — **THEOREM 1 for
`stuckIrrel`**, the fallback at two stuck terms: structure-η in both
directions, then the unit certificate, then proof irrelevance
(`stuckIrrel_specA`; `StuckE` is `SimBOp` at the pure call). -/
theorem stuckIrrel_spec {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec eager env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK eager env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.stuckIrrel (coreKnot .verified eager fe id fuel) fe d a b
    ⦃fun r s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.stuckIrrelFueled .verified eager env F d x y) r; ⊤⦄ :=
  stuckIrrel_specA henv hsim s₀ d a b x y hok hda hdb hwa hwb

/-! ## 4. The axiom census -/

section Census

#print axioms liftFueled_spec
#print axioms proofIrrel_sorts
#print axioms proofIrrel_specA
#print axioms reservedBasisNames_spec
#print axioms env_ind_of_index
#print axioms structUnitCert_specA
#print axioms etaCtorShape_spec
#print axioms structEtaCertWith_tail
#print axioms structEtaCertWith_exits
#print axioms structEtaCertWith_spec
#print axioms structEtaCert_specA
#print axioms stuckIrrelFueled_eta1
#print axioms stuckIrrelFueled_eta2
#print axioms stuckIrrelFueled_unit
#print axioms stuckIrrelFueled_proof
#print axioms stuckIrrel_specA
#print axioms stuckIrrel_spec

end Census

end ConRon.Bridge.Core

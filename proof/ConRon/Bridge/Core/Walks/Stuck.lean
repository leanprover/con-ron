/-
# `ConRon.Bridge.Core.Walks.Stuck` — the stuck fallback, `stuckIrrel`

Task #97-P3-Core round 5.  `stuckIrrel` is the `defeq` body's fallback at two
structurally distinct stuck terms — structure-η in both directions, then
unit-likeness, then proof irrelevance — and every congruence failure of
`defeqStuck` (the old `defeqStep` before task #109) ends in it.  Round 4 left it in `Walks/Owed.lean` as one
statement over a tower; this module skeletonises the tower top-down:

| walk | twin | con-leche | status |
|---|---|---|---|
| `stuckIrrel_spec` | `Arena/Core.lean:1564` | `Kernel/Core.lean:532-542` | **proved** from the three below |
| `structEtaCert_spec` | `:1502` | `:450-473` | **proved** from `etaCtorShape_spec` (closed) and `structEtaCertWith_spec` (`:1416` / `:376-448`, **CLOSED** round 6, over `Walks/Eta.lean`) |
| `structUnitCert_spec` | `:1513` | `:475-503` | **CLOSED** |
| `proofIrrel_spec` | `:1310` | `:327-341` | **CLOSED** |

**Two preconditions added, and why.**  (2) `EnvWF env`, on
`structUnitCert_spec`/`structEtaCert_spec` and so on `stuckIrrel_spec`: the
family certificate runs `iotaCerts` on an instantiated STORED type, and
`iotaCerts_spec` needs it well-scoped — con-leche's `const_ty_hasFvar`,
whose hypothesis is `EnvWF`.  (1)  The twin gates the type-former
telescope certificate of `structUnitCert` (and the two certificate families
of `structEtaCertWith`) on `mode.certs` — the EXECUTED core's
`Cached/CoreC.lean:437/440/508` — where con-leche's spec body runs it
unconditionally.  At `mode.certs = false` the twin answers `true` where the
spec may answer `false`, so the published `stuckIrrel_spec` was **false at
the trusted mode**.  It now takes `hμ : mode.verifiedChecks = true`, which
is what every body theorem of this tier already has in hand
(`certs_of_verifiedChecks`, con-leche's `Verify/BetaGate.lean:126`).
-/
import ConRon.Bridge.Core.Walks.PropRead
import ConRon.Bridge.Core.Walks.Reserved
import ConRon.Bridge.Core.Walks.Eta
import ConRon.Bridge.ExprOps.Walks

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## Vocabulary candidates (for Bridge/Grind.lean) -/

/-- con-leche: none — a `DenWS` precondition: the subject denotes. -/
theorem DenWS.isSome {d : Nat} {o : Option Expr} (h : DenWS d o) : o.isSome = true := by
  cases o with
  | none => exact h.elim
  | some _ => rfl
grind_pattern [bridge_grind] DenWS.isSome => DenWS d o

/-- con-leche: none — a `Bool` answer about two optional subjects, as a named
predicate `P` on their denotations (`P` a partial application, never a
`fun`). -/
def PairAns (P : Expr → Expr → Bool → Prop) : Option Expr → Option Expr → Bool → Prop
  | some x, some y, r => P x y r
  | _, _, _ => True

/-- con-leche: none — `PairAns` at denoting subjects. -/
@[bridge_grind =] theorem PairAns.some_eq (P : Expr → Expr → Bool → Prop) (x y : Expr)
    (r : Bool) : PairAns P (some x) (some y) r = P x y r := rfl

/-- con-leche: none — a `SimBOp` triple at denoting subjects is a `PairAns`
triple at their denotations (the answer-shape restatement of a two-subject
`Bool` walk). -/
theorem pairAns_of_spec {m : AM Bool} {P : Expr → Expr → Bool → Prop} {s₀ : AState}
    {a b : EIdx} {d : Nat}
    (hda : DenWS d (denoteE s₀.store a)) (hdb : DenWS d (denoteE s₀.store b))
    (h : ∀ x y, denoteE s₀.store a = some x → denoteE s₀.store b = some y →
      Expr.WScoped d x → Expr.WScoped d y →
      ⦃fun s => s = s₀⦄ m
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ P x y r; ⊤⦄) :
    ⦃fun s => s = s₀⦄ m
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ PairAns P (denoteE s₀.store a) (denoteE s₀.store b) r; ⊤⦄ := by
  cases ha : denoteE s₀.store a with
  | none => rw [ha] at hda; exact hda.elim
  | some x =>
  cases hb : denoteE s₀.store b with
  | none => rw [hb] at hdb; exact hdb.elim
  | some y =>
  rw [ha] at hda; rw [hb] at hdb
  exact h x y ha hb hda hdb

/-- con-leche: none — the `inferIO` slot's answer at an optional subject
(`WhnfAns`'s shape, `Core/Walks/Nat.lean`). -/
def InferIOAns (mode : CheckMode) (env : Env) (d : Nat) (st : EStore) (r : EIdx) :
    Option Expr → Prop
  | some e => SimE (ConLeche.inferTypeIO mode env) d e st r
  | none => True

/-- con-leche: none — `InferIOAns` at a denoting subject. -/
theorem InferIOAns.some {d : Nat} {st : EStore} {r : EIdx} {e : Expr}
    (H : InferIOAns mode env d st r (some e)) : SimE (ConLeche.inferTypeIO mode env) d e st r :=
  H
grind_pattern [bridge_grind] InferIOAns.some => InferIOAns mode env d st r (some e)

/-- con-leche: ConLeche/Verify/Cached/DiscC1.lean:70 ssimC_zero — the
`inferIO` slot in answer shape (`KnotSpec.whnfA`'s). -/
theorem KnotSpec.inferIOA {f : Nat} (hsim : KnotSpec mode env fe f)
    (s₀ : AState) (d : Nat) (i : EIdx) (hok : CheckOK mode env fe s₀)
    (hw : DenWS d (denoteE s₀.store i)) :
    ⦃fun s => s = s₀⦄ (coreKnot mode fe id f).inferIO d i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ InferIOAns mode env d s'.store r (denoteE s₀.store i); ⊤⦄ := by
  cases hd : denoteE s₀.store i with
  | none => rw [hd] at hw; exact hw.elim
  | some e =>
    rw [hd] at hw
    exact triple_mono (hsim.inferIO s₀ d i e hok hd hw) (fun _ _ h => h)

/-- con-leche: none — a `Bool` answer about three optional subjects, as a
named predicate on their denotations. -/
def TripleAns (P : Expr → Expr → Expr → Bool → Prop) :
    Option Expr → Option Expr → Option Expr → Bool → Prop
  | some x, some y, some w, r => P x y w r
  | _, _, _, _ => True

/-- con-leche: none — `TripleAns` at denoting subjects. -/
@[bridge_grind =] theorem TripleAns.some_eq (P : Expr → Expr → Expr → Bool → Prop)
    (x y w : Expr) (r : Bool) : TripleAns P (some x) (some y) (some w) r = P x y w r := rfl

/-! ### The children's answers, named -/

/-- con-leche: ConLeche/Kernel/Core.lean:413-425 structEtaCert — its answer at
two subjects. -/
def EtaCertE (mode : CheckMode) (env : Env) (d : Nat) (x y : Expr) (r : Bool) : Prop :=
  SimBOp (fun F => ConLeche.structEtaCertFueled mode env F d x y) r

/-- con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith — its
answer at the two subjects and the stuck side's whnf'd type. -/
def EtaWithE (mode : CheckMode) (env : Env) (d : Nat) (x y w : Expr) (r : Bool) : Prop :=
  SimBOp (fun F => ConLeche.structEtaCertWithFueled mode env F d x y w) r

/-- con-leche: ConLeche/Kernel/Core.lean:431-455 structUnitCert — its answer. -/
def UnitCertE (mode : CheckMode) (env : Env) (d : Nat) (x y : Expr) (r : Bool) : Prop :=
  SimBOp (fun F => ConLeche.structUnitCertFueled mode env F d x y) r

/-- con-leche: ConLeche/Kernel/Core.lean:298-312 proofIrrel — its answer. -/
def PIrrelE (mode : CheckMode) (env : Env) (d : Nat) (x y : Expr) (r : Bool) : Prop :=
  SimBOp (fun F => ConLeche.proofIrrelFueled mode env F d x y) r

/-- con-leche: ConLeche/Kernel/Core.lean:487-492 stuckIrrel — its answer. -/
def StuckE (mode : CheckMode) (env : Env) (d : Nat) (x y : Expr) (r : Bool) : Prop :=
  SimBOp (fun F => ConLeche.stuckIrrelFueled mode env F d x y) r

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
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h3 : ConLeche.inferTypeIO mode env F d ta = .ok tta)
    (h4 : ConLeche.whnf mode env F d tta = .ok w)
    (hw : ∀ l, w ≠ .sort l) :
    ConLeche.proofIrrelFueled mode env F d x y = .ok false := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e3 : (ConLeche.pureFns mode env F).inferIO d ta = .ok tta := h3
  have e4 : (ConLeche.pureFns mode env F).whnf d tta = .ok w := h4
  simp only [ConLeche.proofIrrelFueled, ConLeche.proofIrrel, e1, e3, e4,
    bind, Except.bind]
  try (cases w <;> first | rfl | exact absurd rfl (hw _))

/-- con-leche: ConLeche/Kernel/Core.lean:327-341 proofIrrel — the first side
is a sort, the second side's type's type is not. -/
theorem proofIrrel_nosort_b {F d : Nat} {x y ta tta tb ttb w : Expr}
    {uT : Level} {okA : Bool}
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h3 : ConLeche.inferTypeIO mode env F d ta = .ok tta)
    (h4 : ConLeche.whnf mode env F d tta = .ok (.sort uT))
    (h5 : Level.isEquiv uT Level.zero = some okA)
    (h6 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h7 : ConLeche.inferTypeIO mode env F d tb = .ok ttb)
    (h8 : ConLeche.whnf mode env F d ttb = .ok w)
    (hw : ∀ l, w ≠ .sort l) :
    ConLeche.proofIrrelFueled mode env F d x y = .ok false := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e3 : (ConLeche.pureFns mode env F).inferIO d ta = .ok tta := h3
  have e4 : (ConLeche.pureFns mode env F).whnf d tta = .ok (.sort uT) := h4
  have e6 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h6
  have e7 : (ConLeche.pureFns mode env F).inferIO d tb = .ok ttb := h7
  have e8 : (ConLeche.pureFns mode env F).whnf d ttb = .ok w := h8
  simp only [ConLeche.proofIrrelFueled, ConLeche.proofIrrel, e1, e3, e4,
    bind, Except.bind, ConLeche.liftFueled, h5, e6, e7, e8, pure, Except.pure]
  try (cases w <;> first | rfl | exact absurd rfl (hw _))

/-- con-leche: ConLeche/Kernel/Core.lean:327-341 proofIrrel — both sides'
types' types are sorts: the verdict is the two level comparisons. -/
theorem proofIrrel_sorts {F d : Nat} {x y ta tta tb ttb : Expr}
    {uT vT : Level} {okA okB : Bool}
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h3 : ConLeche.inferTypeIO mode env F d ta = .ok tta)
    (h4 : ConLeche.whnf mode env F d tta = .ok (.sort uT))
    (h5 : Level.isEquiv uT Level.zero = some okA)
    (h6 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h7 : ConLeche.inferTypeIO mode env F d tb = .ok ttb)
    (h8 : ConLeche.whnf mode env F d ttb = .ok (.sort vT))
    (h9 : Level.isEquiv vT Level.zero = some okB) :
    ConLeche.proofIrrelFueled mode env F d x y = .ok (okA && okB) := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e3 : (ConLeche.pureFns mode env F).inferIO d ta = .ok tta := h3
  have e4 : (ConLeche.pureFns mode env F).whnf d tta = .ok (.sort uT) := h4
  have e6 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h6
  have e7 : (ConLeche.pureFns mode env F).inferIO d tb = .ok ttb := h7
  have e8 : (ConLeche.pureFns mode env F).whnf d ttb = .ok (.sort vT) := h8
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
theorem reservedBasisNames_spec (s₀ : AState) (hok : CheckOK mode env fe s₀) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.reservedBasisNames
    ⦃fun hs s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
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
theorem env_ind_of_index {s : AState} (hok : CheckOK mode env fe s)
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
theorem env_not_ind_of_index {s : AState} (hok : CheckOK mode env fe s)
    {T : NIdx} {Tn : ConLeche.Name} (hn : denoteN s.store.ns T = some Tn)
    (hnd : ∀ v caps, fe.find? T ≠ some (.indInfo v caps)) :
    ∀ cv caps, env.find? Tn ≠ some (.indInfo cv caps) :=
  optCI_ind_none (optCI_find hok hn) hnd

/-! ### `structUnitCert`'s pure side at its exits -/

/-- con-leche: ConLeche/Kernel/Core.lean:475-503 structUnitCert — the type's
head is not a constant. -/
theorem structUnitCert_nohead {F d : Nat} {x y ta wta : Expr}
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h2 : ConLeche.whnf mode env F d ta = .ok wta)
    (hh : ∀ c us, wta.getAppFn ≠ .const c us) :
    ConLeche.structUnitCertFueled mode env F d x y = .ok false := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d ta = .ok wta := h2
  simp only [ConLeche.structUnitCertFueled, ConLeche.structUnitCert, e1, e2,
    bind, Except.bind]
  first
    | rfl
    | (split
       · rename_i c us heq; exact absurd heq (hh c us)
       · rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:475-503 structUnitCert — the head is
not a stored inductive. -/
theorem structUnitCert_noind {F d : Nat} {x y ta wta : Expr} {T : Name}
    {us : List Level}
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h2 : ConLeche.whnf mode env F d ta = .ok wta)
    (hh : wta.getAppFn = .const T us)
    (hf : ∀ cv caps, env.find? T ≠ some (.indInfo cv caps)) :
    ConLeche.structUnitCertFueled mode env F d x y = .ok false := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d ta = .ok wta := h2
  simp only [ConLeche.structUnitCertFueled, ConLeche.structUnitCert, e1, e2,
    hh, bind, Except.bind]
  first
    | rfl
    | (split
       · rename_i cv caps heq; exact absurd heq (hf cv caps)
       · rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:475-503 structUnitCert — the family
is not unit-like at this application. -/
theorem structUnitCert_guard {F d : Nat} {x y ta wta : Expr} {T : Name}
    {us : List Level} {cvT : ConstantVal} {caps : IndCaps}
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h2 : ConLeche.whnf mode env F d ta = .ok wta)
    (hh : wta.getAppFn = .const T us)
    (hf : env.find? T = some (.indInfo cvT caps))
    (hg : ¬ (caps.unitlike = true ∧ ConLeche.reservedBasisNames.contains T = false ∧
      wta.getAppArgs.length = caps.unitParams ∧
      us.length = cvT.levelParams.length)) :
    ConLeche.structUnitCertFueled mode env F d x y = .ok false := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d ta = .ok wta := h2
  simp only [ConLeche.structUnitCertFueled, ConLeche.structUnitCert, e1, e2,
    hh, hf, bind, Except.bind]
  rw [ite_eq_right hg]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:475-503 structUnitCert — the two
types are compared (a ∀ is never a family's application, con-leche's task
#342 L18; no certificate on the type application, L11b). -/
theorem structUnitCert_cmp {F d : Nat} {x y ta wta tb wtb : Expr} {T : Name}
    {us : List Level} {cvT : ConstantVal} {caps : IndCaps} {r : Bool}
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h2 : ConLeche.whnf mode env F d ta = .ok wta)
    (hh : wta.getAppFn = .const T us)
    (hf : env.find? T = some (.indInfo cvT caps))
    (hg : caps.unitlike = true ∧ ConLeche.reservedBasisNames.contains T = false ∧
      wta.getAppArgs.length = caps.unitParams ∧
      us.length = cvT.levelParams.length)
    (h3 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h4 : ConLeche.whnf mode env F d tb = .ok wtb)
    (h5 : (if wtb.isForallE then pure false
      else ConLeche.isDefEqCore mode env F d wta wtb : CheckM Bool) = .ok r) :
    ConLeche.structUnitCertFueled mode env F d x y = .ok r := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d ta = .ok wta := h2
  have e3 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h3
  have e4 : (ConLeche.pureFns mode env F).whnf d tb = .ok wtb := h4
  simp only [ConLeche.structUnitCertFueled, ConLeche.structUnitCert, e1, e2,
    hh, hf, bind, Except.bind]
  rw [ite_eq_left hg]
  simp only [e3, e4]
  exact h5

/-- con-leche: none — an environment constructor's parameter count. -/
def cCtorNP : Option ConstantInfo → Nat | some (.ctorInfo _ n _) => n | _ => 0
/-- con-leche: none — an environment constructor's field count. -/
def cCtorNF : Option ConstantInfo → Nat | some (.ctorInfo _ _ n) => n | _ => 0
attribute [bridge_grind =] cCtorNP cCtorNF

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the index at a constructor
name handle: its parameter and field counts are the environment's. -/
def CtorCountsAt (env : Env) (fe : IFEnv) (c : NIdx) : Option ConLeche.Name → Prop
  | some nm => iCtor? (fe.find? c) = true →
      cCtorNP (env.find? nm) = iCtorNP (fe.find? c) ∧ cCtorNF (env.find? nm) = iCtorNF (fe.find? c)
  | none => True

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — `env_ctor_of_index`'s
counts, at every lookup the program makes. -/
theorem ctorCountsAt {s : AState} (hok : CheckOK mode env fe s) (c : NIdx) :
    CtorCountsAt env fe c (denoteN s.store.ns c) := by
  cases hn : denoteN s.store.ns c with
  | none => trivial
  | some nm =>
    intro hc
    obtain ⟨_, _, hfind⟩ := env_ctor_of_index hok hn (iCtor?_eta hc)
    rw [hfind]; exact ⟨rfl, rfl⟩
grind_pattern [bridge_grind] ctorCountsAt => CheckOK mode env fe s, fe.find? c

/-- con-leche: none — `CtorCountsAt` at a denoting handle. -/
theorem CtorCountsAt.some {c : NIdx} {nm : ConLeche.Name}
    (H : CtorCountsAt env fe c (some nm)) : iCtor? (fe.find? c) = true →
      cCtorNP (env.find? nm) = iCtorNP (fe.find? c) ∧
        cCtorNF (env.find? nm) = iCtorNF (fe.find? c) := H
grind_pattern [bridge_grind] CtorCountsAt.some => CtorCountsAt env fe c (some nm)

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
    | some (.defnInfo _ _ _) | some (.recInfo _ _ _ _) | some (.projInfo _) | none => rfl
  | _ => rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:738-749 etaCtorShape — **THEOREM
1 for `etaCtorShape`**, the constructor-shape test `structEtaCert` runs
FIRST (the divergence audit's D13): an equation with con-leche's reader. -/
theorem etaCtorShape_spec (s₀ : AState) (a : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x) :
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
    ConLeche.structEtaCertWithFueled mode env F d x y w = .ok false := by
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
    ConLeche.structEtaCertWithFueled mode env F d x y w = .ok false := by
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
    ConLeche.structEtaCertWithFueled mode env F d x y w = .ok false := by
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
    ConLeche.structEtaCertWithFueled mode env F d x y w = .ok false := by
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
    ConLeche.structEtaCertWithFueled mode env F d x y w = .ok false := by
  simp only [ConLeche.structEtaCertWithFueled, ConLeche.structEtaCertWith, hh, hf,
    hw]
  rw [ite_eq_left hlen]
  first
    | rfl
    | (split
       · rename_i cv caps heq; exact absurd heq (hfT cv caps)
       · rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith — the
structure-η guard, as con-leche states it. -/
def EtaGuard (env : Env) (w : Expr) (c T : Name) (us' : List Level)
    (cvc cvT : ConstantVal) (caps : IndCaps) : Prop :=
  caps.eta = true ∧ caps.etaCtor = c ∧
    ConLeche.reservedBasisNames.contains T = false ∧
    ConLeche.reservedBasisNames.contains c = false ∧
    w.getAppArgs.length = caps.etaParams ∧
    us'.length = cvT.levelParams.length ∧
    cvc.levelParams = cvT.levelParams ∧
    ConLeche.towerSlotsAll env T caps.etaFields = true

/-- con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith — the
guard fails. -/
theorem structEtaCertWith_guard {F d : Nat} {x y w : Expr} {c T : Name}
    {us us' : List Level} {cvc cvT : ConstantVal} {cnP cnF : Nat}
    {caps : IndCaps}
    (hh : x.getAppFn = .const c us)
    (hf : env.find? c = some (.ctorInfo cvc cnP cnF))
    (hlen : x.getAppArgs.length = cnP + cnF)
    (hw : w.getAppFn = .const T us')
    (hfT : env.find? T = some (.indInfo cvT caps))
    (hg : ¬ EtaGuard env w c T us' cvc cvT caps) :
    ConLeche.structEtaCertWithFueled mode env F d x y w = .ok false := by
  simp only [ConLeche.structEtaCertWithFueled, ConLeche.structEtaCertWith, hh, hf,
    hw, hfT]
  unfold EtaGuard at hg
  rw [ite_eq_left hlen, ite_eq_right hg]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:360-404 structEtaCertWith — past
the guard: the level comparison and the two spine comparisons, verbatim (no
certificate on the type application, con-leche's task #342 L11b). -/
theorem structEtaCertWith_tail {F d : Nat} {x y w : Expr} {c T : Name}
    {us us' : List Level} {cvc cvT : ConstantVal} {cnP cnF : Nat}
    {caps : IndCaps}
    (hh : x.getAppFn = .const c us)
    (hf : env.find? c = some (.ctorInfo cvc cnP cnF))
    (hlen : x.getAppArgs.length = cnP + cnF)
    (hw : w.getAppFn = .const T us')
    (hfT : env.find? T = some (.indInfo cvT caps))
    (hg : EtaGuard env w c T us' cvc cvT caps) :
    ConLeche.structEtaCertWithFueled mode env F d x y w =
      (do
        if ← ConLeche.liftFueled "level comparison"
            (Level.isEquivList us us') then
          if ← ConLeche.defEqListFueled mode env F d
              (x.getAppArgs.take caps.etaParams) w.getAppArgs then
            ConLeche.defEqListFueled mode env F d
              (x.getAppArgs.drop caps.etaParams)
              (ConLeche.etaProjs T y caps.etaFields)
          else pure false
        else pure false : CheckM Bool) := by
  simp only [ConLeche.structEtaCertWithFueled, ConLeche.structEtaCertWith, hh, hf,
    hw, hfT]
  unfold EtaGuard at hg
  rw [ite_eq_left hlen, ite_eq_left hg]

/-- con-leche: ConLeche/Kernel/Core.lean:360-404 structEtaCertWith — the
tail's exits, each stated at the facts the twin's stages name. -/
theorem structEtaCertWith_exits {F d : Nat} {x y w : Expr} {c T : Name}
    {us us' : List Level} {cvc cvT : ConstantVal} {cnP cnF : Nat}
    {caps : IndCaps}
    (hh : x.getAppFn = .const c us)
    (hf : env.find? c = some (.ctorInfo cvc cnP cnF))
    (hlen : x.getAppArgs.length = cnP + cnF)
    (hw : w.getAppFn = .const T us')
    (hfT : env.find? T = some (.indInfo cvT caps))
    (hg : EtaGuard env w c T us' cvc cvT caps) :
    (Level.isEquivList us us' = some false →
      ConLeche.structEtaCertWithFueled mode env F d x y w = .ok false) ∧
    (Level.isEquivList us us' = some true →
      ∀ dq, ConLeche.defEqListFueled mode env F d
        (x.getAppArgs.take caps.etaParams) w.getAppArgs = .ok dq →
      (dq = false →
        ConLeche.structEtaCertWithFueled mode env F d x y w = .ok false) ∧
      (dq = true → ∀ r, ConLeche.defEqListFueled mode env F d
          (x.getAppArgs.drop caps.etaParams)
          (ConLeche.etaProjs T y caps.etaFields) = .ok r →
        ConLeche.structEtaCertWithFueled mode env F d x y w = .ok r)) := by
  rw [structEtaCertWith_tail hh hf hlen hw hfT hg]
  refine ⟨fun hl => ?_, fun hl dq hdq => ⟨fun hd => ?_, fun hd r hr => ?_⟩⟩
  all_goals subst_vars
  all_goals clear hg hh hf hlen hw hfT
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

**CLOSED** (round 6), staged over the twin's program order: `getAppFn` /
`getAppArgs` at both sides, the index at the constructor and the type former
(`env_ctor_of_index`, `env_ind_of_index`), `reservedBasisNames_spec`,
`viewLsLen`, the slot discipline (`Walks/Eta.lean`'s `towerSlotsAll_spec` /
`recSlotsAll_spec`), the guard (`EtaGuard`, identified by name injectivity
and `denoteNList_containsC`), `lvlsEq?_spec` + `liftFueled_spec`, the
family certificate (`constTyAt_spec` + `iotaCerts_spec`, where `hμ` is
spent), the per-slot certificates (`structEtaProjCerts_spec`), the
parameters (`defEqList_spec`), the TT-lane synthetic spine (`constTyAt_spec`,
`etaProjs_spec`, `iotaCerts_spec`) and the fields (`etaProjs_spec`,
`defEqList_spec`).  The pure side is `structEtaCertWith_exits`, one
statement per exit over `structEtaCertWith_tail`. -/
theorem structEtaCertWith_spec {fuel : Nat} (_hμ : mode.verifiedChecks = true)
    (_henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b wtb : EIdx) (x y w : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y) (hdw : denoteE s₀.store wtb = some w)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y)
    (hww : Expr.WScoped d w) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.structEtaCertWith (coreKnot mode fe id fuel) fe d a b wtb
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.structEtaCertWithFueled mode env F d x y w)
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
            have hcapsD : ∃ ct als cts, denoteN s₀.store.ns icaps.etaCtor = some ct ∧
                dcaps = ⟨icaps.eta, ct, icaps.etaParams, icaps.etaFields,
                  icaps.unitlike, icaps.unitParams, icaps.ruleK, icaps.sortZ,
                  als, icaps.nparams, cts⟩ := by
              simp only [Frontend.denoteCaps] at hdcaps
              split at hdcaps
              · rename_i ct als cts hct _ _
                exact ⟨ct, als, cts, hct, (Option.some.inj hdcaps).symm⟩
              · simp at hdcaps
            obtain ⟨ct, als, cts, hct, rfl⟩ := hcapsD
            -- stage 4: the type's arguments, the reserved names, the levels
            refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s₀ wtb
              hok.state (by rw [hdw]; rfl)) ?_
            rintro targs s4 ⟨hs4, hrelT⟩
            subst s4
            have htargs : Frontend.denoteEList s₀.store targs = some w.getAppArgs :=
              hrelT w hdw
            refine triple_seq (reservedBasisNames_spec s₀ hok) ?_
            rintro res s5 ⟨hok5, hx5, hp5, hres⟩
            have hwf5 := hok5.state.wf
            refine triple_seq (viewLsLen_spec s5 us') ?_
            rintro ol s6 ⟨hs6, hol⟩
            subst s6
            rw [viewLen_of_denoteLs (denoteLs_ext hus' hx5)] at hol
            subst hol
            dsimp only
            -- stage 5: the slot discipline
            refine triple_seq (towerSlotsAll_spec s5 T Tn icaps.etaFields hok5
              (denoteN_ext hTn hx5)) ?_
            rintro slots s7 ⟨hok7, hx6, hp6, hslots⟩
            have hx07 : Ext s₀.store s7.store := hx5.trans hx6
            have hp07 : s7.pins = s₀.pins := hp6.trans hp5
            obtain ⟨_, hlpsC, _⟩ := denoteCV_inv hdcvc
            obtain ⟨_, hlpsT, _⟩ := denoteCV_inv hdcvT
            have hctr : icaps.etaCtor = c ↔ ct = cn :=
              ⟨fun h => by subst h; exact Option.some.inj (hct.symm.trans hcn),
               fun h => by subst h; exact denoteN_inj hrk.nsWF hct hcn⟩
            have hguard : (icaps.eta = true ∧ icaps.etaCtor = c ∧
                res.contains T = false ∧ res.contains c = false ∧
                targs.length = icaps.etaParams ∧
                ls'.length = icvT.levelParams.length ∧
                icvc.levelParams = icvT.levelParams ∧ slots = true) ↔
                EtaGuard env w cn Tn ls' dcvc dcvT
                  ⟨icaps.eta, ct, icaps.etaParams, icaps.etaFields,
                    icaps.unitlike, icaps.unitParams, icaps.ruleK, icaps.sortZ,
                    als, icaps.nparams, cts⟩ := by
              unfold EtaGuard
              rw [hctr, denoteNList_containsC hwf5 res _ hres T Tn
                  (denoteN_ext hTn hx5),
                denoteNList_containsC hwf5 res _ hres c cn (denoteN_ext hcn hx5),
                ← denoteEList_len htargs, denoteNList_len hlpsT,
                denoteNList_eq_iff hwf hlpsC hlpsT, hslots]
            have hwx : ∀ z ∈ x.getAppArgs, Expr.WScoped d z :=
              Expr.WScoped.getAppArgs hwa
            have hwtargs : ∀ z ∈ w.getAppArgs, Expr.WScoped d z :=
              Expr.WScoped.getAppArgs hww
            refine triple_ite (fun hgT => ?_) (fun hgF => ?_)
            · have hgP := hguard.mp hgT
              have hEx := fun F => structEtaCertWith_exits (mode := mode) (F := F)
                (d := d) (y := y) hgf hfindc hlenP hgw hfindT hgP
              -- stage 6: the two level lists
              refine triple_seq (lvlsEq?_spec s7 us us' hok7) ?_
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
                  (ExprOps.denoteEList_take icaps.etaParams aargs _ haargs)
                refine triple_seq (defEqList_spec hsim s8 d
                  (aargs.take icaps.etaParams) targs _ _ hok8 haargs8
                  (denoteEList_ext hx08 _ _ htargs)
                  (fun z hz => hwx z (List.mem_of_mem_take hz)) hwtargs) ?_
                rintro dq s10 ⟨hok10, hx10, hp10, F3, hF3⟩
                have hx010 := hx08.trans hx10
                have hp010 : s10.pins = s₀.pins := hp10.trans hp08
                refine triple_ite (fun hdT => ?_) (fun hdF => ?_)
                · have hdq : dq = true := hdT
                  subst hdq
                  -- stage 8: the fabricated fields agree
                  refine triple_seq (etaProjs_spec s10 T b icaps.etaFields Tn y
                    hok10 (denoteN_ext hTn hx010) (denote_ext hdb hx010)) ?_
                  rintro projs s11 ⟨hok11, hx11, hp11, hprojs⟩
                  have hx011 := hx010.trans hx11
                  refine triple_mono (defEqList_spec hsim s11 d
                    (aargs.drop icaps.etaParams) projs _ _ hok11
                    (denoteEList_ext hx011 _ _
                      (ExprOps.denoteEList_drop icaps.etaParams aargs _ haargs))
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
            · exact triple_pureC ⟨hok7, hx07, hp07, 0,
                structEtaCertWith_guard hgf hfindc hlenP hgw hfindT
                  (fun h => hgF (hguard.mpr h))⟩
          next hnd =>
            have hnf := env_not_ind_of_index hok hTn (fun v c h => hnd v c h)
            have hres : ConLeche.structEtaCertWithFueled mode env 0 d x y w =
                .ok false := structEtaCertWith_noind hgf hfindc hlenP hgw hnf
            exact triple_pureC ⟨hok, Ext.refl _, rfl, 0, hres⟩
        all_goals
          have hres : ConLeche.structEtaCertWithFueled mode env 0 d x y w =
              .ok false := structEtaCertWith_nohead_w hgf hfindc hlenP
                (denote_not_const hwf hvw hdw' (by intro c us h; cases h))
          dsimp only
          exact triple_pureC ⟨hok, Ext.refl _, rfl, 0, hres⟩
      · rw [ite_eq_right hlenT]
        have hres : ConLeche.structEtaCertWithFueled mode env 0 d x y w =
            .ok false := structEtaCertWith_len hgf hfindc (by rw [hlenEq]; exact hlenT)
        exact triple_pureC ⟨hok, Ext.refl _, rfl, 0, hres⟩
    next hnd =>
      have hnc := env_not_ctor_of_index hok hcn (fun v p q h => hnd v p q h)
      have hres : ConLeche.structEtaCertWithFueled mode env 0 d x y w =
          .ok false := structEtaCertWith_noctor hgf hnc
      exact triple_pureC ⟨hok, Ext.refl _, rfl, 0, hres⟩
  all_goals
    have hres : ConLeche.structEtaCertWithFueled mode env 0 d x y w =
        .ok false := structEtaCertWith_nohead
          (denote_not_const hwf hvh hdd (by intro c us h; cases h))
    dsimp only
    exact triple_pureC ⟨hok, Ext.refl _, rfl, 0, hres⟩

/-! ## 2. The three children -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:738-749 etaCtorShape —
`etaCtorShape_spec` at whatever the handle denotes. -/
theorem etaCtorShape_specA (s₀ : AState) (a : EIdx)
    (hok : CheckOK mode env fe s₀) (hda : (denoteE s₀.store a).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.etaCtorShape fe a
    ⦃fun r s' => s' = s₀ ∧ (denoteE s₀.store a).map (ConLeche.etaCtorShape env) = some r; ⊤⦄ := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hda
  refine triple_mono (etaCtorShape_spec s₀ a x hok hx) ?_
  rintro r s' ⟨h1, h2⟩
  exact ⟨h1, by rw [hx, h2]; rfl⟩

/-- con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith —
`structEtaCertWith_spec` in answer shape. -/
theorem structEtaCertWith_specA {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b wtb : EIdx) (hok : CheckOK mode env fe s₀)
    (hda : DenWS d (denoteE s₀.store a)) (hdb : DenWS d (denoteE s₀.store b))
    (hdw : DenWS d (denoteE s₀.store wtb)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.structEtaCertWith (coreKnot mode fe id fuel) fe d a b wtb
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        TripleAns (EtaWithE mode env d) (denoteE s₀.store a) (denoteE s₀.store b)
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
  exact structEtaCertWith_spec hμ henv hsim s₀ d a b wtb x y w hok ha hb hw hda hdb hdw

/-- con-leche: ConLeche/Kernel/Core.lean:413-425 structEtaCert — the shape
test fails. -/
@[bridge_grind ←] theorem EtaCertE.shape {d : Nat} {x y : Expr}
    (h : ConLeche.etaCtorShape env x = false) : EtaCertE mode env d x y false :=
  ⟨0, by simp only [ConLeche.structEtaCertFueled, ConLeche.structEtaCert, h,
    Bool.false_eq_true, ite_false]; rfl⟩

/-- con-leche: ConLeche/Kernel/Core.lean:413-425 structEtaCert — the shape
fits: the certificate against `y`'s whnf'd io-grade type. -/
theorem EtaCertE.with {d F1 F2 : Nat} {x y v1 v2 : Expr} {r : Bool}
    (h : ConLeche.etaCtorShape env x = true)
    (h1 : ConLeche.inferTypeIO mode env F1 d y = .ok v1)
    (h2 : ConLeche.whnf mode env F2 d v1 = .ok v2)
    (h3 : EtaWithE mode env d x y v2 r) : EtaCertE mode env d x y r := by
  obtain ⟨F3, hF3⟩ := h3
  refine ⟨F1 + F2 + F3, ?_⟩
  have e1 : (ConLeche.pureFns mode env (F1 + F2 + F3)).inferIO d y = .ok v1 :=
    ConLeche.inferTypeIO_mono (by omega) h1
  have e2 : (ConLeche.pureFns mode env (F1 + F2 + F3)).whnf d v1 = .ok v2 :=
    ConLeche.whnf_mono (by omega) h2
  have e3 := structEtaCertWithFueled_mono (show F3 ≤ F1 + F2 + F3 by omega) hF3
  simp only [ConLeche.structEtaCertFueled, ConLeche.structEtaCert, h, ite_true, e1, e2,
    bind, Except.bind]
  exact e3
grind_pattern [bridge_grind] EtaCertE.with =>
  EtaCertE mode env d x y r, ConLeche.inferTypeIO mode env F1 d y,
  ConLeche.whnf mode env F2 d v1, EtaWithE mode env d x y v2 r

/-- con-leche: ConLeche/Kernel/Core.lean:450-473 structEtaCert — the walk in
answer shape (`PairAns` of `EtaCertE`). -/
theorem structEtaCert_specA {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (hok : CheckOK mode env fe s₀)
    (hda : DenWS d (denoteE s₀.store a)) (hdb : DenWS d (denoteE s₀.store b)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.structEtaCert (coreKnot mode fe id fuel) fe d a b
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        PairAns (EtaCertE mode env d) (denoteE s₀.store a) (denoteE s₀.store b) r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.structEtaCert, etaCtorShape_specA (mode := mode) (env := env) (fe := fe),
      KnotSpec.inferIOA hsim, KnotSpec.whnfA hsim, structEtaCertWith_specA hμ henv hsim] <;>
      finish

/-- con-leche: ConLeche/Kernel/Core.lean:450-473 structEtaCert — **THEOREM 1
for `structEtaCert`**: structural η certification of a fully applied
constructor `a` against a stuck `b` of an η-capable stored structure
(`structEtaCert_specA`). -/
theorem structEtaCert_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.structEtaCert (coreKnot mode fe id fuel) fe d a b
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.structEtaCertFueled mode env F d x y) r; ⊤⦄ :=
  triple_mono (structEtaCert_specA hμ henv hsim s₀ d a b hok (by rw [hda]; exact hwa)
    (by rw [hdb]; exact hwb)) (fun _ _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, by
      rw [hda, hdb] at h4; exact h4⟩)

/-- con-leche: ConLeche/Kernel/Core.lean:475-503 structUnitCert — **THEOREM 1
for `structUnitCert`**: `a` and `b` inhabit the same stored unit-like family.

**CLOSED** (round 5), staged: two `inferIO`/`whnf` pairs, `getAppFn` and
the head's `view`, the index (`env_ind_of_index`), `getAppArgs`,
`reservedBasisNames_spec` (the Checker tier's run lemma, read as a triple),
`viewLsLen`, the guard (`denoteNList_contains` for the reserved test),
`KnotSpec.defeq`, `constTyAt_spec` and `iotaCerts_spec`.  The `mode.certs`
gate is where `hμ` is spent, and **`EnvWF env` is a second added
precondition**: `iotaCerts_spec` needs the instantiated stored type
well-scoped, which is con-leche's `const_ty_hasFvar` — whose hypothesis is
`EnvWF` (the same repair round 4 made to `projCert_spec`). -/
theorem structUnitCert_spec {fuel : Nat} (_hμ : mode.verifiedChecks = true)
    (_henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.structUnitCert (coreKnot mode fe id fuel) fe d a b
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.structUnitCertFueled mode env F d x y) r; ⊤⦄ := by
  unfold ConRon.Arena.structUnitCert
  -- stage 1: `a`'s io-grade type, head-normalised
  refine triple_seq (hsim.inferIO s₀ d a x hok hda hwa) ?_
  rintro ta s1 ⟨hok1, hx1, hp1, vta, hvta, hwvta, F1, hF1⟩
  refine triple_seq (hsim.whnf s1 d ta vta hok1 hvta hwvta) ?_
  rintro wta s2 ⟨hok2, hx2, hp2, vwta, hvwta, hwvwta, F2, hF2⟩
  have hx02 : Ext s₀.store s2.store := hx1.trans hx2
  have hp02 : s2.pins = s₀.pins := hp2.trans hp1
  have hwf2 := hok2.state.wf
  have hA : ∀ G, max F1 F2 ≤ G →
      ConLeche.inferTypeIO mode env G d x = .ok vta := fun G hle =>
    ConLeche.inferTypeIO_mono (Nat.le_trans (Nat.le_max_left _ _) hle) hF1
  have hB : ∀ G, max F1 F2 ≤ G → ConLeche.whnf mode env G d vta = .ok vwta :=
    fun G hle => ConLeche.whnf_mono (Nat.le_trans (Nat.le_max_right _ _) hle) hF2
  -- stage 2: its head
  refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s2 wta hok2.state
    (by rw [hvwta]; rfl)) ?_
  rintro hd s3 ⟨hs3, hrelF⟩
  subst s3
  have hdd : denoteE s2.store hd = some vwta.getAppFn := hrelF vwta hvwta
  obtain ⟨vh, hvh⟩ := denoteE_view hdd
  refine tag_view_bind_triple hvh ?_
    (fun hne => by cases vh <;> first | rfl | exact absurd rfl hne)
  cases vh
  case const T us =>
    obtain ⟨Tn, ls, hgf, hTn, hus⟩ := denote_const_inv hwf2 hvh hdd
    dsimp only
    split
    next icv icaps hfd =>
      obtain ⟨dcv, dcaps, hdcv, hdcaps, hfind⟩ := env_ind_of_index hok2 hTn hfd
      -- stage 3: the type's arguments, the reserved names, the level count
      refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s2 wta hok2.state
        (by rw [hvwta]; rfl)) ?_
      rintro targs s4 ⟨hs4, hrelA⟩
      subst s4
      have hargs : Frontend.denoteEList s2.store targs = some vwta.getAppArgs :=
        hrelA vwta hvwta
      refine triple_seq (reservedBasisNames_spec s2 hok2) ?_
      rintro res s5 ⟨hok5, hx5, hp5, hres⟩
      have hwf5 := hok5.state.wf
      refine triple_seq (viewLsLen_spec s5 us) ?_
      rintro ol s6 ⟨hs6, hol⟩
      subst s6
      rw [viewLen_of_denoteLs (denoteLs_ext hus hx5)] at hol
      subst hol
      dsimp only
      obtain ⟨_hnm, hlps, _hty⟩ := denoteCV_inv hdcv
      have hcaps : dcaps.unitlike = icaps.unitlike ∧
          dcaps.unitParams = icaps.unitParams := by
        simp only [Frontend.denoteCaps] at hdcaps
        split at hdcaps
        · cases hdcaps; exact ⟨rfl, rfl⟩
        · simp at hdcaps
      have hguard : (icaps.unitlike = true ∧ res.contains T = false ∧
          targs.length = icaps.unitParams ∧
          ls.length = icv.levelParams.length) ↔
          (dcaps.unitlike = true ∧
            ConLeche.reservedBasisNames.contains Tn = false ∧
            vwta.getAppArgs.length = dcaps.unitParams ∧
            ls.length = dcv.levelParams.length) := by
        rw [denoteNList_containsC hwf5 res _ hres T Tn (denoteN_ext hTn hx5),
          hcaps.1, hcaps.2, ← denoteEList_len hargs, denoteNList_len hlps]
      split
      next hg =>
        have hgP := hguard.mp hg
        have hx05 := hx02.trans hx5
        have hp05 : s5.pins = s₀.pins := hp5.trans hp02
        -- stage 4: `b`'s io-grade type, head-normalised
        refine triple_seq (hsim.inferIO s5 d b y hok5 (denote_ext hdb hx05)
          hwb) ?_
        rintro tb s6 ⟨hok6, hx6, hp6, vtb, hvtb, hwvtb, F3, hF3⟩
        refine triple_seq (hsim.whnf s6 d tb vtb hok6 hvtb hwvtb) ?_
        rintro wtb s7 ⟨hok7, hx7, hp7, vwtb, hvwtb, hwvwtb, F4, hF4⟩
        have hx07 := hx05.trans (hx6.trans hx7)
        have hp07 : s7.pins = s₀.pins := hp7.trans (hp6.trans hp05)
        have hG : ∀ G, F1 + F2 + F3 + F4 ≤ G →
            ConLeche.inferTypeIO mode env G d x = .ok vta ∧
            ConLeche.whnf mode env G d vta = .ok vwta ∧
            ConLeche.inferTypeIO mode env G d y = .ok vtb ∧
            ConLeche.whnf mode env G d vtb = .ok vwtb := fun G hle =>
          ⟨hA G (by omega), hB G (by omega),
            ConLeche.inferTypeIO_mono (by omega) hF3,
            ConLeche.whnf_mono (by omega) hF4⟩
        have hfa := ExprOps.isForallE_rel hok7.state.wf hvwtb
        split
        next hfT =>
          refine triple_pureC ⟨hok7, hx07, hp07, F1 + F2 + F3 + F4, ?_⟩
          obtain ⟨g1, g2, g3, g4⟩ := hG _ (Nat.le_refl _)
          refine structUnitCert_cmp g1 g2 hgf hfind hgP g3 g4 ?_
          rw [← hfa, hfT]; rfl
        next hfF =>
          refine triple_mono (hsim.defeq s7 d wta wtb vwta vwtb hok7
            (denote_ext hvwta (hx5.trans (hx6.trans hx7))) hvwtb hwvwta
            hwvwtb) ?_
          rintro r s8 ⟨hok8, hx8, hp8, F5, hF5⟩
          refine ⟨hok8, hx07.trans hx8, hp8.trans hp07,
            F1 + F2 + F3 + F4 + F5, ?_⟩
          obtain ⟨g1, g2, g3, g4⟩ := hG (F1 + F2 + F3 + F4 + F5) (by omega)
          refine structUnitCert_cmp g1 g2 hgf hfind hgP g3 g4 ?_
          have hnf : vwtb.isForallE = false := by
            rw [← hfa]; simpa using hfF
          rw [hnf]
          exact ConLeche.isDefEqCore_mono (by omega) hF5
      next hg =>
        vcgen
        bridge_peel; subst_vars
        exact ⟨hok5, hx02.trans hx5, hp5.trans hp02, max F1 F2,
          structUnitCert_guard (hA _ (Nat.le_refl _)) (hB _ (Nat.le_refl _))
            hgf hfind (fun h => hg (hguard.mpr h))⟩
    next hnd =>
      have hnf := env_not_ind_of_index hok2 hTn (fun v c h => hnd v c h)
      vcgen
      bridge_peel; subst_vars
      exact ⟨hok2, hx02, hp02, max F1 F2,
        structUnitCert_noind (hA _ (Nat.le_refl _)) (hB _ (Nat.le_refl _)) hgf
          hnf⟩
  all_goals
    dsimp only
    vcgen
    bridge_peel; subst_vars
    exact ⟨hok2, hx02, hp02, max F1 F2,
      structUnitCert_nohead (hA _ (Nat.le_refl _)) (hB _ (Nat.le_refl _))
        (denote_not_const hwf2 hvh hdd (by intro c us h; cases h))⟩

/-! ### `proofIrrel` in answer shape -/

/-- con-leche: ConLeche/Kernel/Level.lean Level.isEquiv — `lvlEq?_spec`
with its answer as ONE equation over the two denotations (`opt2`). -/
theorem lvlEq?_specA (s₀ : AState) (u v : LIdx) (hok : CheckOK mode env fe s₀) :
    ⦃fun s => s = s₀⦄ lvlEq? u v
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins ∧
        opt2 Level.isEquiv (denoteL s₀.store.ls u) (denoteL s₀.store.ls v) = some r; ⊤⦄ :=
  triple_mono (lvlEq?_spec s₀ u v hok) (fun _ _ ⟨h1, h2, h3, lu, lv, hu, hv, hr⟩ =>
    ⟨h1, h2, h3, by rw [hu, hv, hr]; rfl⟩)

/-- con-leche: ConLeche/Kernel/Core.lean:298-312 proofIrrel — one side's run
up to its sort: the io-grade type of `x`, its io-grade type, head-normalised,
at one fuel, answered by the handle `hh` at the store `st`. -/
def SortRun (mode : CheckMode) (env : Env) (d : Nat) (x : Expr) (st : EStore) (hh : EIdx) :
    Prop :=
  ∃ F ta tta w, ConLeche.inferTypeIO mode env F d x = .ok ta ∧
    ConLeche.inferTypeIO mode env F d ta = .ok tta ∧ ConLeche.whnf mode env F d tta = .ok w ∧
    denoteE st hh = some w

/-- con-leche: ConLeche/Kernel/Core.lean:298-312 proofIrrel — the three slot
answers of one side, chained by their handles, are its run. -/
theorem SortRun.mk {d : Nat} {x : Expr} {st₁ st₂ st₃ : EStore} {ta tta hh : EIdx}
    (h1 : SimE (ConLeche.inferTypeIO mode env) d x st₁ ta)
    (h2 : InferIOAns mode env d st₂ tta (denoteE st₁ ta))
    (h3 : WhnfAns mode env d st₃ hh (denoteE st₂ tta)) : SortRun mode env d x st₃ hh := by
  obtain ⟨v1, hv1, _, F1, hF1⟩ := h1
  rw [hv1] at h2
  obtain ⟨v2, hv2, _, F2, hF2⟩ := h2
  rw [hv2] at h3
  obtain ⟨v3, hv3, _, F3, hF3⟩ := h3
  exact ⟨F1 + F2 + F3, v1, v2, v3, ConLeche.inferTypeIO_mono (by omega) hF1,
    ConLeche.inferTypeIO_mono (by omega) hF2, ConLeche.whnf_mono (by omega) hF3, hv3⟩
grind_pattern [bridge_grind] SortRun.mk =>
  SimE (ConLeche.inferTypeIO mode env) d x st₁ ta, InferIOAns mode env d st₂ tta (denoteE st₁ ta),
  WhnfAns mode env d st₃ hh (denoteE st₂ tta)

/-- con-leche: none — a run's answer is a sort at its view's level, or not a
sort at all (`denote_sort_inv`, `denote_not_sort`). -/
theorem SortRun.view {d : Nat} {x : Expr} {st : EStore} {hh : EIdx}
    (hs : SortRun mode env d x st hh) (hwf : StoreWF st) :
    ∃ F ta tta w, ConLeche.inferTypeIO mode env F d x = .ok ta ∧
      ConLeche.inferTypeIO mode env F d ta = .ok tta ∧ ConLeche.whnf mode env F d tta = .ok w ∧
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
    (hr : r = false) (hs : SortRun mode env d x st hh) (hwf : StoreWF st)
    (ht : (hh.tag == ETag.sort) = false) : PIrrelE mode env d x y r := by
  obtain ⟨F, ta, tta, w, h1, h3, h4, _, hn⟩ := hs.view hwf
  subst hr
  exact ⟨F, proofIrrel_nosort_a h1 h3 h4 (hn (by simpa using ht))⟩
grind_pattern [bridge_grind] PIrrelE.nosort_a =>
  PIrrelE mode env d x y r, SortRun mode env d x st hh

/-- con-leche: ConLeche/Kernel/Core.lean:298-312 proofIrrel — `x`'s side is
a sort whose level compares (`okA`), `y`'s is not a sort. -/
theorem PIrrelE.nosort_b {d : Nat} {x y : Expr} {st st2 : EStore} {hh hh2 : EIdx}
    {u z : LIdx} {okA r : Bool} (hr : r = false)
    (hs : SortRun mode env d x st hh) (hwf : StoreWF st)
    (hv : st.view hh = some (.sort u)) (hz : denoteL st.ls z = some Level.zero)
    (hq : opt2 Level.isEquiv (denoteL st.ls u) (denoteL st.ls z) = some (some okA))
    (hs2 : SortRun mode env d y st2 hh2) (hwf2 : StoreWF st2)
    (ht2 : (hh2.tag == ETag.sort) = false) : PIrrelE mode env d x y r := by
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
  PIrrelE mode env d x y r, SortRun mode env d x st hh, SortRun mode env d y st2 hh2,
  ENodeView.sort u, opt2 Level.isEquiv (denoteL st.ls u) (denoteL st.ls z), some okA where
  guard st.view hh = some (.sort u)
  guard opt2 Level.isEquiv (denoteL st.ls u) (denoteL st.ls z) = some (some okA)

/-- con-leche: ConLeche/Kernel/Core.lean:298-312 proofIrrel — both sides are
sorts: the verdict is the two level comparisons. -/
theorem PIrrelE.sorts {d : Nat} {x y : Expr} {st st2 : EStore} {hh hh2 : EIdx}
    {u u2 z z2 : LIdx} {okA okB : Bool}
    (hs : SortRun mode env d x st hh) (hwf : StoreWF st)
    (hv : st.view hh = some (.sort u)) (hz : denoteL st.ls z = some Level.zero)
    (hq : opt2 Level.isEquiv (denoteL st.ls u) (denoteL st.ls z) = some (some okA))
    (hs2 : SortRun mode env d y st2 hh2) (hwf2 : StoreWF st2)
    (hv2 : st2.view hh2 = some (.sort u2)) (hz2 : denoteL st2.ls z2 = some Level.zero)
    (hq2 : opt2 Level.isEquiv (denoteL st2.ls u2) (denoteL st2.ls z2) = some (some okB)) :
    PIrrelE mode env d x y (okA && okB) := by
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
  SortRun mode env d x st hh, SortRun mode env d y st2 hh2,
  opt2 Level.isEquiv (denoteL st.ls u) (denoteL st.ls z), some okA,
  opt2 Level.isEquiv (denoteL st2.ls u2) (denoteL st2.ls z2), some okB where
  guard opt2 Level.isEquiv (denoteL st.ls u) (denoteL st.ls z) = some (some okA)
  guard opt2 Level.isEquiv (denoteL st2.ls u2) (denoteL st2.ls z2) = some (some okB)

/-- con-leche: ConLeche/Kernel/Core.lean:327-341 proofIrrel — the walk in
answer shape (`PairAns` of `PIrrelE`): `inferIO`/`whnf` twice per side, the
zero pin, `lvlEq?` and `liftFueled`, over the three exits above. -/
theorem proofIrrel_specA {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (hok : CheckOK mode env fe s₀)
    (hda : DenWS d (denoteE s₀.store a)) (hdb : DenWS d (denoteE s₀.store b)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.proofIrrel (coreKnot mode fe id fuel) fe d a b
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        PairAns (PIrrelE mode env d) (denoteE s₀.store a) (denoteE s₀.store b) r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.proofIrrel, ConRon.Arena.zeroLevel, KnotSpec.inferIOA hsim,
      KnotSpec.whnfA hsim, pinZeroLevel_spec, lvlEq?_specA (mode := mode) (env := env) (fe := fe),
      liftFueled_spec] <;> finish

/-- con-leche: ConLeche/Kernel/Core.lean:327-341 proofIrrel — **THEOREM 1 for
`proofIrrel`**: the stuck fallback's proof irrelevance — both types' sorts
`Prop` (`proofIrrel_specA`). -/
theorem proofIrrel_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.proofIrrel (coreKnot mode fe id fuel) fe d a b
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.proofIrrelFueled mode env F d x y) r; ⊤⦄ :=
  triple_mono (proofIrrel_specA hsim s₀ d a b hok (by rw [hda]; exact hwa)
    (by rw [hdb]; exact hwb)) (fun _ _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, by
      rw [hda, hdb] at h4; exact h4⟩)

/-! ## 2. The pure side: `stuckIrrel` at its four exits -/

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — the first η
direction certifies. -/
theorem stuckIrrelFueled_eta1 {F d : Nat} {x y : Expr}
    (h : ConLeche.structEtaCertFueled mode env F d x y = .ok true) :
    ConLeche.stuckIrrelFueled mode env F d x y = .ok true := by
  have h' : ConLeche.structEtaCert (ConLeche.pureFns mode env F) env d x y
      = .ok true := h
  simp only [ConLeche.stuckIrrelFueled, ConLeche.stuckIrrel, h', bind,
    Except.bind, ite_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — the second η
direction certifies. -/
theorem stuckIrrelFueled_eta2 {F d : Nat} {x y : Expr}
    (h1 : ConLeche.structEtaCertFueled mode env F d x y = .ok false)
    (h2 : ConLeche.structEtaCertFueled mode env F d y x = .ok true) :
    ConLeche.stuckIrrelFueled mode env F d x y = .ok true := by
  have h1' : ConLeche.structEtaCert (ConLeche.pureFns mode env F) env d x y
      = .ok false := h1
  have h2' : ConLeche.structEtaCert (ConLeche.pureFns mode env F) env d y x
      = .ok true := h2
  simp only [ConLeche.stuckIrrelFueled, ConLeche.stuckIrrel, h1', h2', bind,
    Except.bind, Bool.false_eq_true, ite_false, ite_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — unit-likeness
certifies. -/
theorem stuckIrrelFueled_unit {F d : Nat} {x y : Expr}
    (h1 : ConLeche.structEtaCertFueled mode env F d x y = .ok false)
    (h2 : ConLeche.structEtaCertFueled mode env F d y x = .ok false)
    (h3 : ConLeche.structUnitCertFueled mode env F d x y = .ok true) :
    ConLeche.stuckIrrelFueled mode env F d x y = .ok true := by
  have h1' : ConLeche.structEtaCert (ConLeche.pureFns mode env F) env d x y
      = .ok false := h1
  have h2' : ConLeche.structEtaCert (ConLeche.pureFns mode env F) env d y x
      = .ok false := h2
  have h3' : ConLeche.structUnitCert (ConLeche.pureFns mode env F) env d x y
      = .ok true := h3
  simp only [ConLeche.stuckIrrelFueled, ConLeche.stuckIrrel, h1', h2', h3',
    bind, Except.bind, Bool.false_eq_true, ite_false, ite_true, pure,
    Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — none of the
three certifies, so proof irrelevance decides. -/
theorem stuckIrrelFueled_proof {F d : Nat} {x y : Expr} {r : Bool}
    (h1 : ConLeche.structEtaCertFueled mode env F d x y = .ok false)
    (h2 : ConLeche.structEtaCertFueled mode env F d y x = .ok false)
    (h3 : ConLeche.structUnitCertFueled mode env F d x y = .ok false)
    (h4 : ConLeche.proofIrrelFueled mode env F d x y = .ok r) :
    ConLeche.stuckIrrelFueled mode env F d x y = .ok r := by
  have h1' : ConLeche.structEtaCert (ConLeche.pureFns mode env F) env d x y
      = .ok false := h1
  have h2' : ConLeche.structEtaCert (ConLeche.pureFns mode env F) env d y x
      = .ok false := h2
  have h3' : ConLeche.structUnitCert (ConLeche.pureFns mode env F) env d x y
      = .ok false := h3
  have h4' : ConLeche.proofIrrel (ConLeche.pureFns mode env F) d x y
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
    (h : EtaCertE mode env d x y true) : StuckE mode env d x y true := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, stuckIrrelFueled_eta1 hF⟩

/-- con-leche: ConLeche/Kernel/Core.lean:487-492 stuckIrrel — the second η
direction certifies. -/
@[bridge_grind ←] theorem StuckE.eta2 {d : Nat} {x y : Expr}
    (h1 : EtaCertE mode env d x y false) (h2 : EtaCertE mode env d y x true) :
    StuckE mode env d x y true := by
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  exact ⟨max F1 F2, stuckIrrelFueled_eta2
    (structEtaCertFueled_mono (Nat.le_max_left _ _) hF1)
    (structEtaCertFueled_mono (Nat.le_max_right _ _) hF2)⟩

/-- con-leche: ConLeche/Kernel/Core.lean:487-492 stuckIrrel — unit-likeness
certifies. -/
@[bridge_grind ←] theorem StuckE.unit {d : Nat} {x y : Expr}
    (h1 : EtaCertE mode env d x y false) (h2 : EtaCertE mode env d y x false)
    (h3 : UnitCertE mode env d x y true) : StuckE mode env d x y true := by
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  obtain ⟨F3, hF3⟩ := h3
  exact ⟨F1 + F2 + F3, stuckIrrelFueled_unit
    (structEtaCertFueled_mono (by omega) hF1) (structEtaCertFueled_mono (by omega) hF2)
    (structUnitCertFueled_mono (by omega) hF3)⟩

/-- con-leche: ConLeche/Kernel/Core.lean:487-492 stuckIrrel — none of the
three certifies, so proof irrelevance decides. -/
@[bridge_grind ←] theorem StuckE.proof {d : Nat} {x y : Expr} {r : Bool}
    (h1 : EtaCertE mode env d x y false) (h2 : EtaCertE mode env d y x false)
    (h3 : UnitCertE mode env d x y false) (h4 : PIrrelE mode env d x y r) :
    StuckE mode env d x y r := by
  obtain ⟨F1, hF1⟩ := h1
  obtain ⟨F2, hF2⟩ := h2
  obtain ⟨F3, hF3⟩ := h3
  obtain ⟨F4, hF4⟩ := h4
  exact ⟨F1 + F2 + F3 + F4, stuckIrrelFueled_proof
    (structEtaCertFueled_mono (by omega) hF1) (structEtaCertFueled_mono (by omega) hF2)
    (structUnitCertFueled_mono (by omega) hF3) (proofIrrelFueled_mono (by omega) hF4)⟩

/-- con-leche: ConLeche/Kernel/Core.lean:431-455 structUnitCert —
`structUnitCert_spec` in answer shape. -/
theorem structUnitCert_specA {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (hok : CheckOK mode env fe s₀)
    (hda : DenWS d (denoteE s₀.store a)) (hdb : DenWS d (denoteE s₀.store b)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.structUnitCert (coreKnot mode fe id fuel) fe d a b
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        PairAns (UnitCertE mode env d) (denoteE s₀.store a) (denoteE s₀.store b) r; ⊤⦄ :=
  pairAns_of_spec hda hdb fun x y ha hb hwa hwb =>
    structUnitCert_spec hμ henv hsim s₀ d a b x y hok ha hb hwa hwb

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — the walk in
answer shape (`StuckE`). -/
theorem stuckIrrel_specA {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.stuckIrrel (coreKnot mode fe id fuel) fe d a b
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ StuckE mode env d x y r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.stuckIrrel, structEtaCert_specA hμ henv hsim,
      structUnitCert_specA hμ henv hsim, proofIrrel_specA hsim] <;> finish

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — **THEOREM 1 for
`stuckIrrel`**, the fallback at two stuck terms: structure-η in both
directions, then the unit certificate, then proof irrelevance
(`stuckIrrel_specA`; `StuckE` is `SimBOp` at the pure call).  The
precondition `hμ` is the module note's. -/
theorem stuckIrrel_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.stuckIrrel (coreKnot mode fe id fuel) fe d a b
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.stuckIrrelFueled mode env F d x y) r; ⊤⦄ :=
  stuckIrrel_specA hμ henv hsim s₀ d a b x y hok hda hdb hwa hwb

/-! ## 4. The axiom census -/

section Census

#print axioms liftFueled_spec
#print axioms proofIrrel_sorts
#print axioms proofIrrel_specA
#print axioms proofIrrel_spec
#print axioms reservedBasisNames_spec
#print axioms env_ind_of_index
#print axioms structUnitCert_cmp
#print axioms structUnitCert_spec
#print axioms etaCtorShape_spec
#print axioms structEtaCertWith_tail
#print axioms structEtaCertWith_exits
#print axioms structEtaCertWith_spec
#print axioms structEtaCert_specA
#print axioms structEtaCert_spec
#print axioms stuckIrrelFueled_eta1
#print axioms stuckIrrelFueled_eta2
#print axioms stuckIrrelFueled_unit
#print axioms stuckIrrelFueled_proof
/-! No `sorryAx` since round 6: `structEtaCertWith_spec` closed. -/
#print axioms stuckIrrel_specA
#print axioms stuckIrrel_spec

end Census

end ConRon.Bridge.Core

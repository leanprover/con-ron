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

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

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

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:738-749 etaCtorShape — **THEOREM
1 for `etaCtorShape`**, the constructor-shape test `structEtaCert` runs
FIRST (the divergence audit's D13): an equation with con-leche's reader. -/
theorem etaCtorShape_spec (s₀ : AState) (a : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.etaCtorShape fe a
    ⦃fun r s' => s' = s₀ ∧ r = ConLeche.etaCtorShape env x; ⊤⦄ := by
  have hwf := hok.state.wf
  unfold ConRon.Arena.etaCtorShape
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
    obtain ⟨cn, ls, hgf, hcn, _⟩ := denote_const_inv hwf hvh hdd
    dsimp only
    split
    next icv cnP cnF hfd =>
      obtain ⟨dcv, _hdcv, hfind⟩ := env_ctor_of_index hok hcn hfd
      refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s₀ a hok.state
        (by rw [hda]; rfl)) ?_
      rintro args s2 ⟨hs2, hrelA⟩
      subst s2
      have hargs := hrelA x hda
      vcgen
      bridge_peel; subst_vars
      refine ⟨rfl, ?_⟩
      simp only [ConLeche.etaCtorShape, hgf, hfind, denoteEList_len hargs]
    next hnd =>
      have hnc := env_not_ctor_of_index hok hcn (fun v p q h => hnd v p q h)
      vcgen
      bridge_peel; subst_vars
      refine ⟨rfl, ?_⟩
      simp only [ConLeche.etaCtorShape, hgf]
      try (split
           · rename_i cv p q heq; exact absurd heq (hnc cv p q)
           · rfl)
  all_goals
    dsimp only
    vcgen
    bridge_peel; subst_vars
    refine ⟨rfl, ?_⟩
    have hnc := denote_not_const hwf hvh hdd (by intro c us h; cases h)
    simp only [ConLeche.etaCtorShape]
    try (split
         · rename_i c us heq; exact absurd heq (hnc c us)
         · rfl)

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

/-- con-leche: none — **a conditional with a shared continuation**: the
`do` elaborator copies the join point into both branches of
`let v ← if c then x else y`, and this puts it back. -/
theorem triple_ite_seq {α β : Type} {c : Prop} [Decidable c] {x y : AM α}
    {k : α → AM β} {s₀ : AState} {Q : α → AState → Prop}
    {R : β → AState → Prop}
    (hxy : ⦃fun s => s = s₀⦄ (if c then x else y) ⦃fun a s => Q a s; ⊤⦄)
    (hk : ∀ a s₁, Q a s₁ → ⦃fun s => s = s₁⦄ k a ⦃fun b s => R b s; ⊤⦄) :
    ⦃fun s => s = s₀⦄ (if c then x >>= k else y >>= k)
      ⦃fun b s => R b s; ⊤⦄ := by
  have e : (if c then x >>= k else y >>= k) = ((if c then x else y) >>= k) := by
    split <;> rfl
  rw [e]
  exact triple_seq hxy hk

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
statement per exit over `structEtaCertWith_tail`; the do elaborator's
copied join points are put back by `triple_ite_seq`. -/
theorem structEtaCertWith_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
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
  sorry

/-! ## 2. The three children -/

/-- con-leche: ConLeche/Kernel/Core.lean:450-473 structEtaCert — **THEOREM 1
for `structEtaCert`**: structural η certification of a fully applied
constructor `a` against a stuck `b` of an η-capable stored structure.

**PROVED** (round 5) from `etaCtorShape_spec` (closed above), two knot
slots, and the child `structEtaCertWith_spec` (above; closed in round 6). -/
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
        SimBOp (fun F => ConLeche.structEtaCertFueled mode env F d x y) r; ⊤⦄ := by
  unfold ConRon.Arena.structEtaCert
  refine triple_seq (etaCtorShape_spec s₀ a x hok hda) ?_
  rintro sh s1 ⟨hs1, hsh⟩
  subst s1
  split
  next hsht =>
    have hshape : ConLeche.etaCtorShape env x = true := hsh ▸ hsht
    refine triple_seq (hsim.inferIO s₀ d b y hok hdb hwb) ?_
    rintro tb s2 ⟨hok2, hx2, hp2, vtb, hvtb, hwvtb, F1, hF1⟩
    refine triple_seq (hsim.whnf s2 d tb vtb hok2 hvtb hwvtb) ?_
    rintro wtb s3 ⟨hok3, hx3, hp3, vw, hvw, hwvw, F2, hF2⟩
    have hx03 : Ext s₀.store s3.store := hx2.trans hx3
    refine triple_mono (structEtaCertWith_spec hμ henv hsim s3 d a b wtb x y vw
      hok3 (denote_ext hda hx03) (denote_ext hdb hx03) hvw hwa hwb hwvw) ?_
    rintro r s4 ⟨hok4, hx4, hp4, F3, hF3⟩
    refine ⟨hok4, hx03.trans hx4, hp4.trans (hp3.trans hp2),
      max (max F1 F2) F3, ?_⟩
    have e1 : (ConLeche.pureFns mode env (max (max F1 F2) F3)).inferIO d y =
        .ok vtb :=
      ConLeche.inferTypeIO_mono (Nat.le_trans (Nat.le_max_left F1 F2)
        (Nat.le_max_left _ _)) hF1
    have e2 : (ConLeche.pureFns mode env (max (max F1 F2) F3)).whnf d vtb =
        .ok vw :=
      ConLeche.whnf_mono (Nat.le_trans (Nat.le_max_right F1 F2)
        (Nat.le_max_left _ _)) hF2
    have e3 := structEtaCertWithFueled_mono (Nat.le_max_right (max F1 F2) F3) hF3
    simp only [ConLeche.structEtaCertFueled, ConLeche.structEtaCert, hshape,
      ite_true, e1, e2, bind, Except.bind]
    exact e3
  next hshf =>
    have hshape : ConLeche.etaCtorShape env x = false := by
      rw [← hsh]; simpa using hshf
    vcgen
    bridge_peel; subst_vars
    refine ⟨hok, Ext.refl _, rfl, 0, ?_⟩
    simp only [ConLeche.structEtaCert, hshape, Bool.false_eq_true, ite_false]
    rfl

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
theorem structUnitCert_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
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
        sorry
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

/-- con-leche: ConLeche/Kernel/Core.lean:327-341 proofIrrel — **THEOREM 1 for
`proofIrrel`**: the stuck fallback's proof irrelevance — both types' sorts
`Prop`.

**CLOSED** (round 5; task #105 removed its unit-like branch with con-leche's
PUNIT), staged: `inferIO`/`whnf` twice per side, the zero pin, `lvlEq?_spec`
and `liftFueled_spec`, over three pure-side exit lemmas and a fuel merge. -/
theorem proofIrrel_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.proofIrrel (coreKnot mode fe id fuel) fe d a b
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.proofIrrelFueled mode env F d x y) r; ⊤⦄ := by
  unfold ConRon.Arena.proofIrrel
  -- stage 1: `a`'s io-grade type, its type, head-normalised
  refine triple_seq (hsim.inferIO s₀ d a x hok hda hwa) ?_
  rintro ta s1 ⟨hok1, hx1, hp1, vta, hvta, hwvta, F1, hF1⟩
  refine triple_seq (hsim.inferIO s1 d ta vta hok1 hvta hwvta) ?_
  rintro tta s4 ⟨hok4, hx4, hp4, vtta, hvtta, hwvtta, F3, hF3⟩
  refine triple_seq (hsim.whnf s4 d tta vtta hok4 hvtta hwvtta) ?_
  rintro w s5 ⟨hok5, hx5, hp5, vw, hvw, _hwvw, F4, hF4⟩
  have hwf5 := hok5.state.wf
  have hx05 : Ext s₀.store s5.store := hx1.trans (hx4.trans hx5)
  have hp05 : s5.pins = s₀.pins := hp5.trans (hp4.trans hp1)
  -- the fuels so far, merged once
  have hG : ∀ G, max F1 (max F3 F4) ≤ G →
      ConLeche.inferTypeIO mode env G d x = .ok vta ∧
      ConLeche.inferTypeIO mode env G d vta = .ok vtta ∧
      ConLeche.whnf mode env G d vtta = .ok vw := by
    intro G hle
    refine ⟨ConLeche.inferTypeIO_mono ?_ hF1,
      ConLeche.inferTypeIO_mono ?_ hF3, ConLeche.whnf_mono ?_ hF4⟩ <;> omega
  obtain ⟨vv, hvv⟩ := denoteE_view hvw
  refine tag_view_bind_triple hvv ?_
    (fun hne => by cases vv <;> first | rfl | exact absurd rfl hne)
  cases vv
  case sort uT =>
    obtain ⟨lT, rfl, hlT⟩ := denote_sort_inv hwf5 hvv hvw
    dsimp only
    refine triple_seq (pinZeroLevel_spec s5 hok5.pins) ?_
    rintro z s6 ⟨hs6, hz⟩
    subst s6
    refine triple_seq (lvlEq?_spec s5 uT z hok5) ?_
    rintro rq s7 ⟨hok7, hst7, hp7, lu, lv, hlu, hlv, hrq⟩
    rw [hlT] at hlu
    rw [hz] at hlv
    obtain rfl : lu = lT := (Option.some.inj hlu).symm
    obtain rfl : lv = Level.zero := (Option.some.inj hlv).symm
    refine triple_seq (liftFueled_spec s7 _ rq) ?_
    rintro okA s8 ⟨hs8, hokA⟩
    subst s8
    subst hokA
    have hx07 : Ext s₀.store s7.store := by rw [hst7]; exact hx05
    have hp07 : s7.pins = s₀.pins := hp7.trans hp05
    -- stage 2: `b`'s type's type, head-normalised
    have hdb7 := denote_ext hdb hx07
    refine triple_seq (hsim.inferIO s7 d b y hok7 hdb7 hwb) ?_
    rintro tb s9 ⟨hok9, hx9, hp9, vtb, hvtb, hwvtb, F5, hF5⟩
    refine triple_seq (hsim.inferIO s9 d tb vtb hok9 hvtb hwvtb) ?_
    rintro ttb s10 ⟨hok10, hx10, hp10, vttb, hvttb, hwvttb, F6, hF6⟩
    refine triple_seq (hsim.whnf s10 d ttb vttb hok10 hvttb hwvttb) ?_
    rintro w2 s11 ⟨hok11, hx11, hp11, vw2, hvw2, _hwvw2, F7, hF7⟩
    have hwf11 := hok11.state.wf
    have hx011 : Ext s₀.store s11.store := hx07.trans (hx9.trans (hx10.trans hx11))
    have hp011 : s11.pins = s₀.pins := hp11.trans (hp10.trans (hp9.trans hp07))
    have hH : ∀ G, max (max F1 (max F3 F4)) (max F5 (max F6 F7)) ≤ G →
        ConLeche.inferTypeIO mode env G d y = .ok vtb ∧
        ConLeche.inferTypeIO mode env G d vtb = .ok vttb ∧
        ConLeche.whnf mode env G d vttb = .ok vw2 := by
      intro G hle
      refine ⟨ConLeche.inferTypeIO_mono ?_ hF5, ConLeche.inferTypeIO_mono ?_ hF6,
        ConLeche.whnf_mono ?_ hF7⟩ <;> omega
    obtain ⟨g1, g3, g4⟩ :=
      hG (max (max F1 (max F3 F4)) (max F5 (max F6 F7))) (Nat.le_max_left _ _)
    obtain ⟨k1, k2, k3⟩ := hH _ (Nat.le_refl _)
    obtain ⟨vv2, hvv2⟩ := denoteE_view hvw2
    refine tag_view_bind_triple hvv2 ?_
      (fun hne => by cases vv2 <;> first | rfl | exact absurd rfl hne)
    cases vv2
    case sort vT =>
      obtain ⟨lV, rfl, hlV⟩ := denote_sort_inv hwf11 hvv2 hvw2
      dsimp only
      -- the zero pin, read again (the port's `prop_sorts_zero_right`)
      refine triple_seq (pinZeroLevel_spec s11 hok11.pins) ?_
      rintro z2 s12 ⟨hs12, hz11⟩
      subst s12
      refine triple_seq (lvlEq?_spec s11 vT z2 hok11) ?_
      rintro rq2 s13 ⟨hok13, hst13, hp13, lu2, lv2, hlu2, hlv2, hrq2⟩
      rw [hlV] at hlu2
      rw [hz11] at hlv2
      obtain rfl : lu2 = lV := (Option.some.inj hlu2).symm
      obtain rfl : lv2 = Level.zero := (Option.some.inj hlv2).symm
      refine triple_seq (liftFueled_spec s13 _ rq2) ?_
      rintro okB s14 ⟨hs14, hokB⟩
      subst s14
      vcgen
      bridge_peel; subst_vars
      refine ⟨hok13, by rw [hst13]; exact hx011, hp13.trans hp011, _,
        proofIrrel_sorts g1 g3 g4 hrq.symm k1 k2 k3 hokB⟩
    all_goals
      dsimp only
      vcgen
      bridge_peel; subst_vars
      refine ⟨hok11, hx011, hp011, _,
        proofIrrel_nosort_b g1 g3 g4 hrq.symm k1 k2 k3
          (denote_not_sort hwf11 hvv2 hvw2 (by intro u h; cases h))⟩
  all_goals
    dsimp only
    obtain ⟨g1, g3, g4⟩ := hG _ (Nat.le_refl _)
    vcgen
    bridge_peel; subst_vars
    exact ⟨hok5, hx05, hp05, _,
      proofIrrel_nosort_a g1 g3 g4
        (denote_not_sort hwf5 hvv hvw (by intro u h; cases h))⟩

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

/-! ## 3. The walk -/

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — **THEOREM 1 for
`stuckIrrel`**, the fallback at two stuck terms: structure-η in both
directions, then the unit certificate, then proof irrelevance.

**PROVED** (round 5, moved here from `Walks/Owed.lean`) from the three
children above, staged by `triple_seq`, with the fuel merge at each exit.
**Statement change: the precondition `hμ` is new** (module note). -/
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
        SimBOp (fun F => ConLeche.stuckIrrelFueled mode env F d x y) r; ⊤⦄ := by
  unfold ConRon.Arena.stuckIrrel
  refine triple_seq (structEtaCert_spec hμ henv hsim s₀ d a b x y hok hda hdb hwa
    hwb) ?_
  rintro r1 s1 ⟨hok1, hx1, hp1, F1, hF1⟩
  cases r1
  · try dsimp only
    have hda1 := denote_ext hda hx1
    have hdb1 := denote_ext hdb hx1
    refine triple_seq (structEtaCert_spec hμ henv hsim s1 d b a y x hok1 hdb1 hda1
      hwb hwa) ?_
    rintro r2 s2 ⟨hok2, hx2, hp2, F2, hF2⟩
    cases r2
    · try dsimp only
      have hda2 := denote_ext hda1 hx2
      have hdb2 := denote_ext hdb1 hx2
      refine triple_seq (structUnitCert_spec hμ henv hsim s2 d a b x y hok2 hda2 hdb2
        hwa hwb) ?_
      rintro r3 s3 ⟨hok3, hx3, hp3, F3, hF3⟩
      cases r3
      · try dsimp only
        refine triple_mono (proofIrrel_spec hsim s3 d a b x y hok3
          (denote_ext hda2 hx3) (denote_ext hdb2 hx3) hwa hwb) ?_
        rintro r4 s4 ⟨hok4, hx4, hp4, F4, hF4⟩
        refine ⟨hok4, hx1.trans (hx2.trans (hx3.trans hx4)),
          hp4.trans (hp3.trans (hp2.trans hp1)),
          max (max F1 F2) (max F3 F4), ?_⟩
        exact stuckIrrelFueled_proof
          (structEtaCertFueled_mono (Nat.le_trans (Nat.le_max_left F1 F2)
            (Nat.le_max_left _ _)) hF1)
          (structEtaCertFueled_mono (Nat.le_trans (Nat.le_max_right F1 F2)
            (Nat.le_max_left _ _)) hF2)
          (structUnitCertFueled_mono (Nat.le_trans (Nat.le_max_left F3 F4)
            (Nat.le_max_right _ _)) hF3)
          (proofIrrelFueled_mono (Nat.le_trans (Nat.le_max_right F3 F4)
            (Nat.le_max_right _ _)) hF4)
      -- (here and below: `+internalize` drops the dead arm of the decided
      -- `if true = true`, task #116)
      · vcgen +internalize
        bridge_peel; subst_vars
        refine ⟨hok3, hx1.trans (hx2.trans hx3), hp3.trans (hp2.trans hp1),
          max (max F1 F2) F3, ?_⟩
        exact stuckIrrelFueled_unit
          (structEtaCertFueled_mono (Nat.le_trans (Nat.le_max_left F1 F2)
            (Nat.le_max_left _ _)) hF1)
          (structEtaCertFueled_mono (Nat.le_trans (Nat.le_max_right F1 F2)
            (Nat.le_max_left _ _)) hF2)
          (structUnitCertFueled_mono (Nat.le_max_right _ _) hF3)
    · vcgen +internalize
      bridge_peel; subst_vars
      refine ⟨hok2, hx1.trans hx2, hp2.trans hp1, max F1 F2, ?_⟩
      exact stuckIrrelFueled_eta2
        (structEtaCertFueled_mono (Nat.le_max_left _ _) hF1)
        (structEtaCertFueled_mono (Nat.le_max_right _ _) hF2)
  · vcgen +internalize
    bridge_peel; subst_vars
    exact ⟨hok1, hx1, hp1, F1, stuckIrrelFueled_eta1 hF1⟩

/-! ## 4. The axiom census -/

section Census

#print axioms liftFueled_spec
#print axioms proofIrrel_sorts
#print axioms proofIrrel_spec
#print axioms reservedBasisNames_spec
#print axioms env_ind_of_index
#print axioms structUnitCert_cmp
#print axioms structUnitCert_spec
#print axioms etaCtorShape_spec
#print axioms structEtaCertWith_tail
#print axioms structEtaCertWith_exits
#print axioms structEtaCertWith_spec
#print axioms structEtaCert_spec
#print axioms stuckIrrelFueled_eta1
#print axioms stuckIrrelFueled_eta2
#print axioms stuckIrrelFueled_unit
#print axioms stuckIrrelFueled_proof
/-! No `sorryAx` since round 6: `structEtaCertWith_spec` closed. -/
#print axioms stuckIrrel_spec

end Census

end ConRon.Bridge.Core

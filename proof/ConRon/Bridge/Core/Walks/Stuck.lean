/-
# `ConRon.Bridge.Core.Walks.Stuck` — the stuck fallback, `stuckIrrel`

Task #97-P3-Core round 5.  `stuckIrrel` is the `defeq` body's fallback at two
structurally distinct stuck terms — structure-η in both directions, then
unit-likeness, then proof irrelevance — and every congruence failure of
`defeqStep` ends in it.  Round 4 left it in `Walks/Owed.lean` as one
statement over a tower; this module skeletonises the tower top-down:

| walk | twin | con-leche | status |
|---|---|---|---|
| `stuckIrrel_spec` | `Arena/Core.lean:1564` | `Kernel/Core.lean:532-542` | **proved** from the three below |
| `structEtaCert_spec` | `:1502` | `:450-473` | **proved** from `etaCtorShape_spec` (closed) and `structEtaCertWith_spec` (`:1416` / `:376-448`, OPEN) |
| `structUnitCert_spec` | `:1513` | `:475-503` | **CLOSED** |
| `proofIrrel_spec` | `:1265` | `:284-305` | **CLOSED**, over `isUnitLikeTy_spec` (new) |

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

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. `isUnitLikeTy`, the one state-only reader under `proofIrrel` -/

/-- con-leche: none — an indexed inductive is an environment inductive. -/
theorem optCI_ind_some {st : EStore} {oc' : Option ConstantInfo}
    {v : IConstantVal} {caps : IIndCaps}
    (hrel : OptCI st (some (.indInfo v caps)) oc') :
    ∃ cv caps', oc' = some (.indInfo cv caps') := by
  obtain ⟨c, hci, rfl⟩ := hrel
  simp only [Frontend.denoteCI] at hci
  split at hci
  · cases hci; exact ⟨_, _, rfl⟩
  · simp at hci

/-- con-leche: none — and nothing else the index holds is. -/
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

/-- con-leche: none — a denoting single-rule list is a single rule with the
same field count. -/
theorem denoteRules_single {st : EStore} {r : IRecRule}
    {rules : List RecRule} (h : Frontend.denoteRules st [r] = some rules) :
    ∃ r', rules = [r'] ∧ r'.nfields = r.nfields := by
  simp only [Frontend.denoteRules] at h
  split at h
  · rename_i x xs hx hxs
    cases hxs; cases h
    simp only [Frontend.denoteRule] at hx
    split at hx
    · cases hx; exact ⟨_, rfl, rfl⟩
    · simp at hx
  · simp at h

/-- con-leche: none — an indexed one-rule recursor is an environment one-rule
recursor with the same counts. -/
theorem optCI_rec1_some {st : EStore} {oc' : Option ConstantInfo}
    {v : IConstantVal} {mI rP : Nat} {r : IRecRule}
    (hrel : OptCI st (some (.recInfo v mI rP [r])) oc') :
    ∃ cv r', oc' = some (.recInfo cv mI rP [r']) ∧ r'.nfields = r.nfields := by
  obtain ⟨c, hci, rfl⟩ := hrel
  simp only [Frontend.denoteCI] at hci
  split at hci
  · rename_i cv rules _ hrules
    cases hci
    obtain ⟨r', rfl, hnf⟩ := denoteRules_single hrules
    exact ⟨cv, r', rfl, hnf⟩
  · simp at hci

/-- con-leche: none — and nothing else the index holds is. -/
theorem optCI_rec1_none {st : EStore} {oc : Option IConstantInfo}
    {oc' : Option ConstantInfo} (hrel : OptCI st oc oc')
    (hnot : ∀ v mI rP r, oc ≠ some (.recInfo v mI rP [r])) :
    ∀ cv mI rP r', oc' ≠ some (.recInfo cv mI rP [r']) := by
  intro cv mI rP r' h
  subst h
  cases oc with
  | none => simp only [OptCI] at hrel; cases hrel
  | some ci =>
    obtain ⟨c, hci, hc⟩ := hrel
    cases hc
    cases ci <;> simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hci
    case recInfo v mI' rP' rs =>
      split at hci
      · rename_i cv' rules _ hrules
        cases hci
        match rs, hrules with
        | [], hr => simp only [Frontend.denoteRules] at hr; cases hr
        | [r], _ => exact hnot v mI rP r rfl
        | _ :: _ :: _, hr =>
          have hl := denoteRules_len hr
          simp at hl
      · simp at hci
    all_goals first
      | (obtain ⟨_, _, h⟩ := hci; cases h)
      | (split at hci
         · cases hci
         · simp at hci)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:124-134 isUnitLikeTy —
**THEOREM 1 for `isUnitLikeTy`**: an equation with con-leche's reader.  The
`PUnit` head test is handle equality against the pin (`denoteN_inj`), the two
index lookups are `OptCI`. -/
theorem isUnitLikeTy_spec (s₀ : AState) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.isUnitLikeTy fe h
    ⦃⇓? b s' => ⌜s' = s₀ ∧ b = ConLeche.isUnitLikeTy env x⌝⦄ := by
  have hwf := hok.state.wf
  obtain ⟨rk, hrk⟩ := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hden
  refine tag_view_bind_triple hv ?_
    (fun hne => by cases v <;> first | rfl | exact absurd rfl hne)
  cases v
  case const c us =>
    obtain ⟨cn, ls, rfl, hcn, _⟩ := denote_const_inv hwf hv hden
    dsimp only
    refine triple_seq (pinAt_spec s₀ PIN_PUNIT hok.pins) ?_
    rintro pu s1 ⟨hs1, hpu⟩
    subst s1
    have hpuN : denoteN s₀.store.ns pu = some ConLeche.punitName := hpu _ rfl
    by_cases hc : c = pu
    · subst hc
      have hcn' : cn = ConLeche.punitName :=
        Option.some.inj (hcn.symm.trans hpuN)
      subst hcn'
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
      have hrelI := optCI_find hok hpuN
      split
      · rename_i v caps heq
        rw [heq] at hrelI
        obtain ⟨cv, caps', hI⟩ := optCI_ind_some hrelI
        refine triple_seq (pinAt_spec s₀ PIN_PUNIT_REC hok.pins) ?_
        rintro pr s2 ⟨hs2, hpr⟩
        subst s2
        have hprN : denoteN s₀.store.ns pr = some ConLeche.punitRecName :=
          hpr _ rfl
        have hrelR := optCI_find hok hprN
        split
        · rename_i v' mI rP r heq'
          rw [heq'] at hrelR
          obtain ⟨cv', r', hR, hnf⟩ := optCI_rec1_some hrelR
          mvcgen
          bridge_peel; subst_vars
          refine ⟨rfl, ?_⟩
          simp [ConLeche.isUnitLikeTy, hI, hR, hnf]
        · rename_i hnot
          have hR := optCI_rec1_none hrelR (fun v mI rP r h => hnot v mI rP r h)
          mvcgen
          bridge_peel; subst_vars
          refine ⟨rfl, ?_⟩
          cases hfr : env.find? ConLeche.punitRecName with
          | none => simp [ConLeche.isUnitLikeTy, hI, hfr]
          | some ci =>
            cases ci
            case recInfo cv mI rP rules =>
              match rules, hfr with
              | [], hfr => simp [ConLeche.isUnitLikeTy, hI, hfr]
              | [r'], hfr => exact absurd hfr (hR cv mI rP r')
              | _ :: _ :: _, hfr => simp [ConLeche.isUnitLikeTy, hI, hfr]
            all_goals simp [ConLeche.isUnitLikeTy, hI, hfr]
      · rename_i hnot
        have hI := optCI_ind_none hrelI (fun v caps h => hnot v caps h)
        mvcgen
        bridge_peel; subst_vars
        refine ⟨rfl, ?_⟩
        cases hfi : env.find? ConLeche.punitName with
        | none => simp [ConLeche.isUnitLikeTy, hfi]
        | some ci =>
          cases ci
          case indInfo cv caps => exact absurd hfi (hI cv caps)
          all_goals simp [ConLeche.isUnitLikeTy, hfi]
    · have hne : cn ≠ ConLeche.punitName := by
        intro h
        exact hc (denoteN_inj hrk.nsWF hcn (h ▸ hpuN))
      have hb : (c != pu) = true := by simpa using hc
      simp only [hb, if_true]
      mvcgen
      bridge_peel; subst_vars
      exact ⟨rfl, by simp [ConLeche.isUnitLikeTy, hne]⟩
  all_goals
    have hnc := denote_not_const hwf hv hden (by intro c us h; cases h)
    mvcgen
    bridge_peel; subst_vars
    refine ⟨rfl, ?_⟩
    cases x <;> simp_all [ConLeche.isUnitLikeTy]

/-! ### `proofIrrel`'s pure side at its exits -/

/-- con-leche: ConLeche/Kernel/Core.lean:284-305 proofIrrel — both types
reduce to unit-like families (the second test's verdict is the answer). -/
theorem proofIrrel_unit {F d : Nat} {x y ta wta tb wtb : Expr} {u2 : Bool}
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h2 : ConLeche.whnf mode env F d ta = .ok wta)
    (hu1 : ConLeche.isUnitLikeTy env wta = true)
    (h3 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h4 : ConLeche.whnf mode env F d tb = .ok wtb)
    (hu2 : ConLeche.isUnitLikeTy env wtb = u2) :
    ConLeche.proofIrrelFueled mode env F d x y = .ok u2 := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d ta = .ok wta := h2
  have e3 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h3
  have e4 : (ConLeche.pureFns mode env F).whnf d tb = .ok wtb := h4
  subst hu2
  cases hu : ConLeche.isUnitLikeTy env wtb <;>
    simp [ConLeche.proofIrrelFueled, ConLeche.proofIrrel, e1, e2, e3, e4, hu1,
      hu, bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:284-305 proofIrrel — not unit-like,
and the first side's type's type is not a sort. -/
theorem proofIrrel_nosort_a {F d : Nat} {x y ta wta tta w : Expr}
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h2 : ConLeche.whnf mode env F d ta = .ok wta)
    (hu1 : ConLeche.isUnitLikeTy env wta = false)
    (h3 : ConLeche.inferTypeIO mode env F d ta = .ok tta)
    (h4 : ConLeche.whnf mode env F d tta = .ok w)
    (hw : ∀ l, w ≠ .sort l) :
    ConLeche.proofIrrelFueled mode env F d x y = .ok false := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d ta = .ok wta := h2
  have e3 : (ConLeche.pureFns mode env F).inferIO d ta = .ok tta := h3
  have e4 : (ConLeche.pureFns mode env F).whnf d tta = .ok w := h4
  simp only [ConLeche.proofIrrelFueled, ConLeche.proofIrrel, e1, e2, e3, e4,
    hu1, Bool.false_eq_true, if_false, bind, Except.bind]
  try (cases w <;> first | rfl | exact absurd rfl (hw _))

/-- con-leche: ConLeche/Kernel/Core.lean:284-305 proofIrrel — the first side
is a sort, the second side's type's type is not. -/
theorem proofIrrel_nosort_b {F d : Nat} {x y ta wta tta tb ttb w : Expr}
    {uT : Level} {okA : Bool}
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h2 : ConLeche.whnf mode env F d ta = .ok wta)
    (hu1 : ConLeche.isUnitLikeTy env wta = false)
    (h3 : ConLeche.inferTypeIO mode env F d ta = .ok tta)
    (h4 : ConLeche.whnf mode env F d tta = .ok (.sort uT))
    (h5 : Level.isEquiv uT Level.zero = some okA)
    (h6 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h7 : ConLeche.inferTypeIO mode env F d tb = .ok ttb)
    (h8 : ConLeche.whnf mode env F d ttb = .ok w)
    (hw : ∀ l, w ≠ .sort l) :
    ConLeche.proofIrrelFueled mode env F d x y = .ok false := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d ta = .ok wta := h2
  have e3 : (ConLeche.pureFns mode env F).inferIO d ta = .ok tta := h3
  have e4 : (ConLeche.pureFns mode env F).whnf d tta = .ok (.sort uT) := h4
  have e6 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h6
  have e7 : (ConLeche.pureFns mode env F).inferIO d tb = .ok ttb := h7
  have e8 : (ConLeche.pureFns mode env F).whnf d ttb = .ok w := h8
  simp only [ConLeche.proofIrrelFueled, ConLeche.proofIrrel, e1, e2, e3, e4,
    hu1, Bool.false_eq_true, if_false, bind, Except.bind, ConLeche.liftFueled,
    h5, e6, e7, e8, pure, Except.pure]
  try (cases w <;> first | rfl | exact absurd rfl (hw _))

/-- con-leche: ConLeche/Kernel/Core.lean:284-305 proofIrrel — both sides'
types' types are sorts: the verdict is the two level comparisons. -/
theorem proofIrrel_sorts {F d : Nat} {x y ta wta tta tb ttb : Expr}
    {uT vT : Level} {okA okB : Bool}
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h2 : ConLeche.whnf mode env F d ta = .ok wta)
    (hu1 : ConLeche.isUnitLikeTy env wta = false)
    (h3 : ConLeche.inferTypeIO mode env F d ta = .ok tta)
    (h4 : ConLeche.whnf mode env F d tta = .ok (.sort uT))
    (h5 : Level.isEquiv uT Level.zero = some okA)
    (h6 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h7 : ConLeche.inferTypeIO mode env F d tb = .ok ttb)
    (h8 : ConLeche.whnf mode env F d ttb = .ok (.sort vT))
    (h9 : Level.isEquiv vT Level.zero = some okB) :
    ConLeche.proofIrrelFueled mode env F d x y = .ok (okA && okB) := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d ta = .ok wta := h2
  have e3 : (ConLeche.pureFns mode env F).inferIO d ta = .ok tta := h3
  have e4 : (ConLeche.pureFns mode env F).whnf d tta = .ok (.sort uT) := h4
  have e6 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h6
  have e7 : (ConLeche.pureFns mode env F).inferIO d tb = .ok ttb := h7
  have e8 : (ConLeche.pureFns mode env F).whnf d ttb = .ok (.sort vT) := h8
  simp only [ConLeche.proofIrrelFueled, ConLeche.proofIrrel, e1, e2, e3, e4,
    hu1, Bool.false_eq_true, if_false, bind, Except.bind, ConLeche.liftFueled,
    h5, h9, e6, e7, e8, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:152-154 liftFueled — the fuel
guard of a level comparison: a `some` passes its value through, a `none`
fails (and `⇓?` claims nothing of a failure). -/
theorem liftFueled_spec {α : Type} (s₀ : AState) (what : String)
    (o : Option α) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.liftFueled what o
    ⦃⇓? a s' => ⌜s' = s₀ ∧ o = some a⌝⦄ := by
  cases o with
  | none => exact triple_fail
  | some a =>
    mvcgen [ConRon.Arena.liftFueled]

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames —
the reserved list in triple form: `Walks/Reserved.lean`'s
`reservedBasisNames_runC` (a copy of `Bridge/Checker/Names.lean`'s) (six pin reads, thirteen name interns) read through
`triple_of_run`. -/
theorem reservedBasisNames_spec (s₀ : AState) (hok : CheckOK mode env fe s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.reservedBasisNames
    ⦃⇓? hs s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Frontend.denoteNList s'.store.ns hs =
          some ConLeche.reservedBasisNames⌝⦄ :=
  triple_of_run fun hs s' hr => by
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
  rw [if_neg hg]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:475-503 structUnitCert — the two
types are compared, and the verdict is the family certificate's (or `false`
when they differ). -/
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
    (h5 : (do
      if ← ConLeche.isDefEqCore mode env F d wta wtb then
        ConLeche.iotaCertsFueled mode env F d false
          (cvT.type.instantiateLevelParams cvT.levelParams us) wta.getAppArgs
      else pure false : CheckM Bool) = .ok r) :
    ConLeche.structUnitCertFueled mode env F d x y = .ok r := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d ta = .ok wta := h2
  have e3 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h3
  have e4 : (ConLeche.pureFns mode env F).whnf d tb = .ok wtb := h4
  simp only [ConLeche.structUnitCertFueled, ConLeche.structUnitCert, e1, e2,
    hh, hf, bind, Except.bind]
  rw [if_pos hg]
  simp only [e3, e4, bind, Except.bind]
  exact h5

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:738-749 etaCtorShape — **THEOREM
1 for `etaCtorShape`**, the constructor-shape test `structEtaCert` runs
FIRST (the divergence audit's D13): an equation with con-leche's reader. -/
theorem etaCtorShape_spec (s₀ : AState) (a : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.etaCtorShape fe a
    ⦃⇓? r s' => ⌜s' = s₀ ∧ r = ConLeche.etaCtorShape env x⌝⦄ := by
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
      mvcgen
      bridge_peel; subst_vars
      refine ⟨rfl, ?_⟩
      simp only [ConLeche.etaCtorShape, hgf, hfind, denoteEList_len hargs]
    next hnd =>
      have hnc := env_not_ctor_of_index hok hcn (fun v p q h => hnd v p q h)
      mvcgen
      bridge_peel; subst_vars
      refine ⟨rfl, ?_⟩
      simp only [ConLeche.etaCtorShape, hgf]
      try (split
           · rename_i cv p q heq; exact absurd heq (hnc cv p q)
           · rfl)
  all_goals
    dsimp only
    mvcgen
    bridge_peel; subst_vars
    refine ⟨rfl, ?_⟩
    have hnc := denote_not_const hwf hvh hdd (by intro c us h; cases h)
    simp only [ConLeche.etaCtorShape]
    try (split
         · rename_i c us heq; exact absurd heq (hnc c us)
         · rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith — **THEOREM
1 for `structEtaCertWith`**, the structure-η certificate against a GIVEN
weak-head-normal type `wtb` of the stuck side.

**OPEN** — the round's next item under `stuckIrrel`: seventy lines over
`getAppFn`/`getAppArgs` (twice), the index at the constructor and at the
type former, `reservedBasisNames_spec`, `viewLsLen`, `towerSlotsAll` /
`recSlotsAll` (two counted recursions over `IFEnv.findProj?_spec` /
`projFnName`), `lvlsEq?_spec`, `liftFueled_spec`, `constTyAt_spec` +
`iotaCerts_spec` (the family certificate, gated on `mode.certs`),
`structEtaProjCerts` (a `List Nat` recursion over `projFnName`, `stripPis`,
`constTyAt`, `iotaCerts`), `defEqList_spec` twice, and `etaProjs`
(`projNodesGo`/`projAppsGo` over `internE`/`mkAppN`) under the TT gate. -/
theorem structEtaCertWith_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b wtb : EIdx) (x y w : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y) (hdw : denoteE s₀.store wtb = some w)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y)
    (hww : Expr.WScoped d w) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.structEtaCertWith mode (coreKnot mode fe id fuel) fe d a b wtb
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.structEtaCertWithFueled mode env F d x y w)
          r⌝⦄ := by
  sorry

/-! ## 2. The three children -/

/-- con-leche: ConLeche/Kernel/Core.lean:450-473 structEtaCert — **THEOREM 1
for `structEtaCert`**: structural η certification of a fully applied
constructor `a` against a stuck `b` of an η-capable stored structure.

**PROVED** (round 5) from `etaCtorShape_spec` (closed above), two knot
slots, and the child `structEtaCertWith_spec` (OPEN, above). -/
theorem structEtaCert_spec {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.structEtaCert mode (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.structEtaCertFueled mode env F d x y) r⌝⦄ := by
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
      if_true, e1, e2, bind, Except.bind]
    exact e3
  next hshf =>
    have hshape : ConLeche.etaCtorShape env x = false := by
      rw [← hsh]; simpa using hshf
    mvcgen
    bridge_peel; subst_vars
    refine ⟨hok, Ext.refl _, rfl, 0, ?_⟩
    simp only [ConLeche.structEtaCertFueled, ConLeche.structEtaCert, hshape,
      Bool.false_eq_true, if_false]
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
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.structUnitCert mode (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.structUnitCertFueled mode env F d x y) r⌝⦄ := by
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
        have hx05 : Ext s₀.store s5.store := hx02.trans hx5
        have hp05 : s5.pins = s₀.pins := hp5.trans hp02
        -- stage 4: `b`'s io-grade type, head-normalised
        refine triple_seq (hsim.inferIO s5 d b y hok5 (denote_ext hdb hx05)
          hwb) ?_
        rintro tb s7 ⟨hok7, hx7, hp7, vtb, hvtb, hwvtb, F3, hF3⟩
        refine triple_seq (hsim.whnf s7 d tb vtb hok7 hvtb hwvtb) ?_
        rintro wtb s8 ⟨hok8, hx8, hp8, vwtb, hvwtb, hwvwtb, F4, hF4⟩
        have hx58 : Ext s5.store s8.store := hx7.trans hx8
        -- stage 5: the two types compared
        refine triple_seq (hsim.defeq s8 d wta wtb vwta vwtb hok8
          (denote_ext hvwta (hx5.trans hx58)) hvwtb hwvwta hwvwtb) ?_
        rintro dq s9 ⟨hok9, hx9, hp9, F5, hF5⟩
        have hx09 : Ext s₀.store s9.store := hx05.trans (hx58.trans hx9)
        have hp09 : s9.pins = s₀.pins := hp9.trans (hp8.trans (hp7.trans hp05))
        have hmax : ∀ G, max (max F1 F2) (max (max F3 F4) F5) ≤ G →
            ConLeche.inferTypeIO mode env G d y = .ok vtb ∧
            ConLeche.whnf mode env G d vtb = .ok vwtb ∧
            ConLeche.isDefEqCore mode env G d vwta vwtb = .ok dq := by
          intro G hle
          refine ⟨ConLeche.inferTypeIO_mono ?_ hF3, ConLeche.whnf_mono ?_ hF4,
            ConLeche.isDefEqCore_mono ?_ hF5⟩ <;> omega
        cases dq
        · -- the types differ
          obtain ⟨m1, m2, m3⟩ := hmax _ (Nat.le_refl _)
          have hres : ∃ F, ConLeche.structUnitCertFueled mode env F d x y =
              .ok false := ⟨_, structUnitCert_cmp
            (hA _ (Nat.le_max_left _ _)) (hB _ (Nat.le_max_left _ _)) hgf hfind
            hgP m1 m2 (by
              simp only [m3, bind, Except.bind, Bool.false_eq_true, if_false]
              rfl)⟩
          mvcgen
          bridge_peel; subst_vars
          exact ⟨hok9, hx09, hp09, hres⟩
        · -- the types agree: the family certificate, at the verified mode
          simp only [ConLeche.certs_of_verifiedChecks hμ, if_true]
          have hx59 : Ext s5.store s9.store := hx58.trans hx9
          have hx29 : Ext s2.store s9.store := hx5.trans hx59
          have hname : dcv.name = Tn := env_find_name hfind
          have hcv9 := denoteCV_ext hdcv hx29
          refine triple_seq (constTyAt_spec s9 icv us Tn ls (.indInfo dcv dcaps)
            hok9 (by rw [denoteCV_name hcv9, hname]) (denoteLs_ext hus hx29)
            hfind hcv9) ?_
          rintro ty s10 ⟨hok10, hx10, hp10, hty⟩
          have hwty : Expr.WScoped d
              (dcv.type.instantiateLevelParams dcv.levelParams ls) :=
            Expr.WScoped.of_not_hasFvar (ConLeche.const_ty_hasFvar henv hfind ls)
          have hwargs : ∀ z ∈ vwta.getAppArgs, Expr.WScoped d z :=
            Expr.WScoped.getAppArgs hwvwta
          have hargs10 := denoteEList_ext (hx29.trans hx10) _ _ hargs
          refine triple_mono (iotaCerts_spec hsim d false ty targs s10 hok10
            ⟨_, _, hty, hwty, hargs10, hwargs⟩) ?_
          rintro r s11 ⟨hok11, hx11, hp11, hr⟩
          obtain ⟨F6, hF6⟩ := hr _ _ hty hargs10
          obtain ⟨m1, m2, m3⟩ := hmax (max (max (max F1 F2) (max (max F3 F4) F5)) F6)
            (Nat.le_max_left _ _)
          refine ⟨hok11, hx09.trans (hx10.trans hx11),
            hp11.trans (hp10.trans hp09), _, structUnitCert_cmp
            (hA _ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)))
            (hB _ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)))
            hgf hfind hgP m1 m2 ?_⟩
          simp only [m3, bind, Except.bind, if_true]
          exact iotaCertsFueled_mono (Nat.le_max_right _ _) hF6
      next hg =>
        mvcgen
        bridge_peel; subst_vars
        exact ⟨hok5, hx02.trans hx5, hp5.trans hp02, max F1 F2,
          structUnitCert_guard (hA _ (Nat.le_refl _)) (hB _ (Nat.le_refl _))
            hgf hfind (fun h => hg (hguard.mpr h))⟩
    next hnd =>
      have hnf := env_not_ind_of_index hok2 hTn (fun v c h => hnd v c h)
      mvcgen
      bridge_peel; subst_vars
      exact ⟨hok2, hx02, hp02, max F1 F2,
        structUnitCert_noind (hA _ (Nat.le_refl _)) (hB _ (Nat.le_refl _)) hgf
          hnf⟩
  all_goals
    dsimp only
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok2, hx02, hp02, max F1 F2,
      structUnitCert_nohead (hA _ (Nat.le_refl _)) (hB _ (Nat.le_refl _))
        (denote_not_const hwf2 hvh hdd (by intro c us h; cases h))⟩

/-- con-leche: ConLeche/Kernel/Core.lean:284-305 proofIrrel — **THEOREM 1 for
`proofIrrel`**: the stuck fallback's proof irrelevance — both unit-like, or
both types' sorts `Prop`.

**CLOSED** (round 5), staged: `isUnitLikeTy_spec` (§1) at both types, then
`propIrrel`'s slow arm — `inferIO`/`whnf` twice per side, the zero pin,
`lvlEq?_spec` and `liftFueled_spec` — over four pure-side exit lemmas and a
seven-way fuel merge. -/
theorem proofIrrel_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.proofIrrel (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.proofIrrelFueled mode env F d x y) r⌝⦄ := by
  unfold ConRon.Arena.proofIrrel
  -- stage 1: `a`'s io-grade type, and its head normal form
  refine triple_seq (hsim.inferIO s₀ d a x hok hda hwa) ?_
  rintro ta s1 ⟨hok1, hx1, hp1, vta, hvta, hwvta, F1, hF1⟩
  refine triple_seq (hsim.whnf s1 d ta vta hok1 hvta hwvta) ?_
  rintro wta s2 ⟨hok2, hx2, hp2, vwta, hvwta, _hwwta, F2, hF2⟩
  -- stage 2: is it unit-like?
  refine triple_seq (isUnitLikeTy_spec s2 wta vwta hok2 hvwta) ?_
  rintro u1 s3 ⟨hs3, hu1⟩
  subst s3
  have hx02 : Ext s₀.store s2.store := hx1.trans hx2
  have hp02 : s2.pins = s₀.pins := hp2.trans hp1
  have hdb2 := denote_ext hdb hx02
  split
  next hu1t =>
    -- both unit-like?
    have hU1 : ConLeche.isUnitLikeTy env vwta = true := hu1 ▸ hu1t
    refine triple_seq (hsim.inferIO s2 d b y hok2 hdb2 hwb) ?_
    rintro tb s4 ⟨hok4, hx4, hp4, vtb, hvtb, hwvtb, F3, hF3⟩
    refine triple_seq (hsim.whnf s4 d tb vtb hok4 hvtb hwvtb) ?_
    rintro wtb s5 ⟨hok5, hx5, hp5, vwtb, hvwtb, _hwwtb, F4, hF4⟩
    refine triple_seq (isUnitLikeTy_spec s5 wtb vwtb hok5 hvwtb) ?_
    rintro u2 s6 ⟨hs6, hu2⟩
    subst s6
    have hfin : ∀ (v : Bool), ConLeche.isUnitLikeTy env vwtb = v →
        ∃ F, ConLeche.proofIrrelFueled mode env F d x y = .ok v := by
      intro v hv
      refine ⟨max (max F1 F2) (max F3 F4), proofIrrel_unit
        (ConLeche.inferTypeIO_mono (Nat.le_trans (Nat.le_max_left F1 F2)
          (Nat.le_max_left _ _)) hF1)
        (ConLeche.whnf_mono (Nat.le_trans (Nat.le_max_right F1 F2)
          (Nat.le_max_left _ _)) hF2) hU1
        (ConLeche.inferTypeIO_mono (Nat.le_trans (Nat.le_max_left F3 F4)
          (Nat.le_max_right _ _)) hF3)
        (ConLeche.whnf_mono (Nat.le_trans (Nat.le_max_right F3 F4)
          (Nat.le_max_right _ _)) hF4) hv⟩
    split
    next hu2t =>
      mvcgen
      bridge_peel; subst_vars
      exact ⟨hok5, hx02.trans (hx4.trans hx5), hp5.trans (hp4.trans hp02),
        hfin true (by simpa using hu2t)⟩
    next hu2f =>
      mvcgen
      bridge_peel; subst_vars
      exact ⟨hok5, hx02.trans (hx4.trans hx5), hp5.trans (hp4.trans hp02),
        hfin false (by simpa using hu2f)⟩
  next hu1f =>
    have hU1 : ConLeche.isUnitLikeTy env vwta = false := by
      rw [← hu1]; simpa using hu1f
    -- stage 3: `a`'s type's type, head-normalised
    refine triple_seq (hsim.inferIO s2 d ta vta hok2 (denote_ext hvta hx2)
      hwvta) ?_
    rintro tta s4 ⟨hok4, hx4, hp4, vtta, hvtta, hwvtta, F3, hF3⟩
    refine triple_seq (hsim.whnf s4 d tta vtta hok4 hvtta hwvtta) ?_
    rintro w s5 ⟨hok5, hx5, hp5, vw, hvw, _hwvw, F4, hF4⟩
    have hwf5 := hok5.state.wf
    have hx05 : Ext s₀.store s5.store := hx02.trans (hx4.trans hx5)
    have hp05 : s5.pins = s₀.pins := hp5.trans (hp4.trans hp02)
    -- the fuels so far, merged once
    have hG : ∀ G, max (max F1 F2) (max F3 F4) ≤ G →
        ConLeche.inferTypeIO mode env G d x = .ok vta ∧
        ConLeche.whnf mode env G d vta = .ok vwta ∧
        ConLeche.inferTypeIO mode env G d vta = .ok vtta ∧
        ConLeche.whnf mode env G d vtta = .ok vw := by
      intro G hle
      refine ⟨ConLeche.inferTypeIO_mono ?_ hF1, ConLeche.whnf_mono ?_ hF2,
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
      -- stage 4: `b`'s type's type, head-normalised
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
      have hH : ∀ G, max (max (max F1 F2) (max F3 F4)) (max F5 (max F6 F7)) ≤ G →
          ConLeche.inferTypeIO mode env G d y = .ok vtb ∧
          ConLeche.inferTypeIO mode env G d vtb = .ok vttb ∧
          ConLeche.whnf mode env G d vttb = .ok vw2 := by
        intro G hle
        refine ⟨ConLeche.inferTypeIO_mono ?_ hF5, ConLeche.inferTypeIO_mono ?_ hF6,
          ConLeche.whnf_mono ?_ hF7⟩ <;> omega
      obtain ⟨g1, g2, g3, g4⟩ :=
        hG (max (max (max F1 F2) (max F3 F4)) (max F5 (max F6 F7)))
          (Nat.le_max_left _ _)
      obtain ⟨k1, k2, k3⟩ := hH _ (Nat.le_refl _)
      obtain ⟨vv2, hvv2⟩ := denoteE_view hvw2
      refine tag_view_bind_triple hvv2 ?_
        (fun hne => by cases vv2 <;> first | rfl | exact absurd rfl hne)
      cases vv2
      case sort vT =>
        obtain ⟨lV, rfl, hlV⟩ := denote_sort_inv hwf11 hvv2 hvw2
        dsimp only
        have hz11 : denoteL s11.store.ls z = some Level.zero :=
          denoteL_ext hz (by rw [← hst7]; exact hx9.trans (hx10.trans hx11))
        refine triple_seq (lvlEq?_spec s11 vT z hok11) ?_
        rintro rq2 s13 ⟨hok13, hst13, hp13, lu2, lv2, hlu2, hlv2, hrq2⟩
        rw [hlV] at hlu2
        rw [hz11] at hlv2
        obtain rfl : lu2 = lV := (Option.some.inj hlu2).symm
        obtain rfl : lv2 = Level.zero := (Option.some.inj hlv2).symm
        refine triple_seq (liftFueled_spec s13 _ rq2) ?_
        rintro okB s14 ⟨hs14, hokB⟩
        subst s14
        mvcgen
        bridge_peel; subst_vars
        refine ⟨hok13, by rw [hst13]; exact hx011, hp13.trans hp011, _,
          proofIrrel_sorts g1 g2 hU1 g3 g4 hrq.symm k1 k2 k3 hokB⟩
      all_goals
        dsimp only
        mvcgen
        bridge_peel; subst_vars
        refine ⟨hok11, hx011, hp011, _,
          proofIrrel_nosort_b g1 g2 hU1 g3 g4 hrq.symm k1 k2 k3
            (denote_not_sort hwf11 hvv2 hvw2 (by intro u h; cases h))⟩
    all_goals
      dsimp only
      obtain ⟨g1, g2, g3, g4⟩ := hG _ (Nat.le_refl _)
      mvcgen
      bridge_peel; subst_vars
      exact ⟨hok5, hx05, hp05, _,
        proofIrrel_nosort_a g1 g2 hU1 g3 g4
          (denote_not_sort hwf5 hvv hvw (by intro u h; cases h))⟩

/-! ## 2. The pure side: `stuckIrrel` at its four exits -/

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — the first η
direction certifies. -/
theorem stuckIrrelFueled_eta1 {F d : Nat} {x y : Expr}
    (h : ConLeche.structEtaCertFueled mode env F d x y = .ok true) :
    ConLeche.stuckIrrelFueled mode env F d x y = .ok true := by
  have h' : ConLeche.structEtaCert mode (ConLeche.pureFns mode env F) env d x y
      = .ok true := h
  simp only [ConLeche.stuckIrrelFueled, ConLeche.stuckIrrel, h', bind,
    Except.bind, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — the second η
direction certifies. -/
theorem stuckIrrelFueled_eta2 {F d : Nat} {x y : Expr}
    (h1 : ConLeche.structEtaCertFueled mode env F d x y = .ok false)
    (h2 : ConLeche.structEtaCertFueled mode env F d y x = .ok true) :
    ConLeche.stuckIrrelFueled mode env F d x y = .ok true := by
  have h1' : ConLeche.structEtaCert mode (ConLeche.pureFns mode env F) env d x y
      = .ok false := h1
  have h2' : ConLeche.structEtaCert mode (ConLeche.pureFns mode env F) env d y x
      = .ok true := h2
  simp only [ConLeche.stuckIrrelFueled, ConLeche.stuckIrrel, h1', h2', bind,
    Except.bind, Bool.false_eq_true, if_false, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — unit-likeness
certifies. -/
theorem stuckIrrelFueled_unit {F d : Nat} {x y : Expr}
    (h1 : ConLeche.structEtaCertFueled mode env F d x y = .ok false)
    (h2 : ConLeche.structEtaCertFueled mode env F d y x = .ok false)
    (h3 : ConLeche.structUnitCertFueled mode env F d x y = .ok true) :
    ConLeche.stuckIrrelFueled mode env F d x y = .ok true := by
  have h1' : ConLeche.structEtaCert mode (ConLeche.pureFns mode env F) env d x y
      = .ok false := h1
  have h2' : ConLeche.structEtaCert mode (ConLeche.pureFns mode env F) env d y x
      = .ok false := h2
  have h3' : ConLeche.structUnitCert (ConLeche.pureFns mode env F) env d x y
      = .ok true := h3
  simp only [ConLeche.stuckIrrelFueled, ConLeche.stuckIrrel, h1', h2', h3',
    bind, Except.bind, Bool.false_eq_true, if_false, if_true, pure,
    Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — none of the
three certifies, so proof irrelevance decides. -/
theorem stuckIrrelFueled_proof {F d : Nat} {x y : Expr} {r : Bool}
    (h1 : ConLeche.structEtaCertFueled mode env F d x y = .ok false)
    (h2 : ConLeche.structEtaCertFueled mode env F d y x = .ok false)
    (h3 : ConLeche.structUnitCertFueled mode env F d x y = .ok false)
    (h4 : ConLeche.proofIrrelFueled mode env F d x y = .ok r) :
    ConLeche.stuckIrrelFueled mode env F d x y = .ok r := by
  have h1' : ConLeche.structEtaCert mode (ConLeche.pureFns mode env F) env d x y
      = .ok false := h1
  have h2' : ConLeche.structEtaCert mode (ConLeche.pureFns mode env F) env d y x
      = .ok false := h2
  have h3' : ConLeche.structUnitCert (ConLeche.pureFns mode env F) env d x y
      = .ok false := h3
  have h4' : ConLeche.proofIrrel (ConLeche.pureFns mode env F) env d x y
      = .ok r := h4
  simp only [ConLeche.stuckIrrelFueled, ConLeche.stuckIrrel, h1', h2', h3',
    h4', bind, Except.bind, Bool.false_eq_true, if_false]

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
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.stuckIrrelFueled mode env F d x y) r⌝⦄ := by
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
      · try dsimp only
        mvcgen
        bridge_peel; subst_vars
        refine ⟨hok3, hx1.trans (hx2.trans hx3), hp3.trans (hp2.trans hp1),
          max (max F1 F2) F3, ?_⟩
        exact stuckIrrelFueled_unit
          (structEtaCertFueled_mono (Nat.le_trans (Nat.le_max_left F1 F2)
            (Nat.le_max_left _ _)) hF1)
          (structEtaCertFueled_mono (Nat.le_trans (Nat.le_max_right F1 F2)
            (Nat.le_max_left _ _)) hF2)
          (structUnitCertFueled_mono (Nat.le_max_right _ _) hF3)
    · try dsimp only
      mvcgen
      bridge_peel; subst_vars
      refine ⟨hok2, hx1.trans hx2, hp2.trans hp1, max F1 F2, ?_⟩
      exact stuckIrrelFueled_eta2
        (structEtaCertFueled_mono (Nat.le_max_left _ _) hF1)
        (structEtaCertFueled_mono (Nat.le_max_right _ _) hF2)
  · try dsimp only
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok1, hx1, hp1, F1, stuckIrrelFueled_eta1 hF1⟩

/-! ## 4. The axiom census -/

section Census

#print axioms optCI_ind_some
#print axioms optCI_rec1_none
#print axioms isUnitLikeTy_spec
#print axioms liftFueled_spec
#print axioms proofIrrel_unit
#print axioms proofIrrel_sorts
#print axioms proofIrrel_spec
#print axioms reservedBasisNames_spec
#print axioms env_ind_of_index
#print axioms structUnitCert_cmp
#print axioms structUnitCert_spec
#print axioms etaCtorShape_spec
#print axioms structEtaCert_spec
#print axioms stuckIrrelFueled_eta1
#print axioms stuckIrrelFueled_eta2
#print axioms stuckIrrelFueled_unit
#print axioms stuckIrrelFueled_proof
/-! `sorryAx` expected on the three children and, through them, on
`stuckIrrel_spec`. -/
#print axioms stuckIrrel_spec

end Census

end ConRon.Bridge.Core

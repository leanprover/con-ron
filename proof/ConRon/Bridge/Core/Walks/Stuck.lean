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
| `structEtaCert_spec` | `:1502` | `:450-473` | **proved** from `etaCtorShape_spec` (closed) and `structEtaCertWith_spec` (`:1416` / `:376-448`, **CLOSED** round 6, over `Walks/Eta.lean`) |
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
import ConRon.Bridge.Core.Walks.Eta

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
  refine view_bind_triple hv ?_
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
`reservedBasisNames_runC` (a copy of `Bridge/Checker/Names.lean`'s) (the pin-table read `pinReserved`) read through
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
  refine view_bind_triple hvh ?_
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

/-! ### `structEtaCertWith`'s pure side at its exits -/

/-- con-leche: none — a `pure` is a triple for any postcondition its value
and the unchanged state satisfy. -/
theorem triple_pureC {α : Type} {s₀ : AState} {a : α}
    {Q : α → AState → Prop} (h : Q a s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ (pure a : AM α) ⦃⇓? r s => ⌜Q r s⌝⦄ :=
  triple_of_run fun r s' hr => by
    simp only [StateT.run, pure, StateT.pure, Except.pure] at hr
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
  rw [if_neg hlen]
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
  rw [if_pos hlen]
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
  rw [if_pos hlen]
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
    (ConLeche.towerSlotsAll env T caps.etaFields ||
      ConLeche.recSlotsAll env T caps.etaFields) = true

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
  rw [if_pos hlen, if_neg hg]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith — past
the guard: the level comparison and the four certificates, verbatim. -/
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
          if ← ConLeche.iotaCertsFueled mode env F d false
              (cvT.type.instantiateLevelParams cvT.levelParams us')
              w.getAppArgs then
            if ← (if ConLeche.towerSlotsAll env T caps.etaFields then pure true
                else ConLeche.structEtaProjCertsFueled mode env F d T us'
                  w.getAppArgs y cvT.levelParams
                  (List.range caps.etaFields)) then
              if ← ConLeche.defEqListFueled mode env F d
                  (x.getAppArgs.take caps.etaParams) w.getAppArgs then
                if ← (if mode.ttChecks then
                    ConLeche.iotaCertsFueled mode env F d false
                      (cvc.type.instantiateLevelParams cvc.levelParams us)
                      (w.getAppArgs ++ ConLeche.etaProjs env T us'
                        w.getAppArgs y caps.etaFields)
                  else pure true) then
                  ConLeche.defEqListFueled mode env F d
                    (x.getAppArgs.drop caps.etaParams)
                    (ConLeche.etaProjs env T us' w.getAppArgs y caps.etaFields)
                else pure false
              else pure false
            else pure false
          else pure false
        else pure false : CheckM Bool) := by
  simp only [ConLeche.structEtaCertWithFueled, ConLeche.structEtaCertWith, hh, hf,
    hw, hfT]
  unfold EtaGuard at hg
  rw [if_pos hlen, if_pos hg]

/-- con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith — the
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
      ConLeche.iotaCertsFueled mode env F d false
        (cvT.type.instantiateLevelParams cvT.levelParams us') w.getAppArgs
        = .ok false →
      ConLeche.structEtaCertWithFueled mode env F d x y w = .ok false) ∧
    (Level.isEquivList us us' = some true →
      ConLeche.iotaCertsFueled mode env F d false
        (cvT.type.instantiateLevelParams cvT.levelParams us') w.getAppArgs
        = .ok true →
      ∀ pc, (if ConLeche.towerSlotsAll env T caps.etaFields then pure true
          else ConLeche.structEtaProjCertsFueled mode env F d T us'
            w.getAppArgs y cvT.levelParams (List.range caps.etaFields) :
            CheckM Bool) = .ok pc →
      (pc = false →
        ConLeche.structEtaCertWithFueled mode env F d x y w = .ok false) ∧
      (pc = true →
        ∀ dq, ConLeche.defEqListFueled mode env F d
          (x.getAppArgs.take caps.etaParams) w.getAppArgs = .ok dq →
        (dq = false →
          ConLeche.structEtaCertWithFueled mode env F d x y w = .ok false) ∧
        (dq = true →
          ∀ tt, (if mode.ttChecks then
              ConLeche.iotaCertsFueled mode env F d false
                (cvc.type.instantiateLevelParams cvc.levelParams us)
                (w.getAppArgs ++ ConLeche.etaProjs env T us' w.getAppArgs y
                  caps.etaFields)
            else pure true : CheckM Bool) = .ok tt →
          (tt = false →
            ConLeche.structEtaCertWithFueled mode env F d x y w = .ok false) ∧
          (tt = true → ∀ r, ConLeche.defEqListFueled mode env F d
              (x.getAppArgs.drop caps.etaParams)
              (ConLeche.etaProjs env T us' w.getAppArgs y caps.etaFields)
              = .ok r →
            ConLeche.structEtaCertWithFueled mode env F d x y w = .ok r)))) := by
  rw [structEtaCertWith_tail hh hf hlen hw hfT hg]
  refine ⟨fun hl => ?_, fun hl h1 => ?_, fun hl h1 pc hpc => ⟨fun hp => ?_,
    fun hp dq hdq => ⟨fun hd => ?_, fun hd tt htt => ⟨fun ht => ?_,
      fun ht r hr => ?_⟩⟩⟩⟩
  all_goals subst_vars
  all_goals clear hg hh hf hlen hw hfT
  all_goals simp_all only [ConLeche.liftFueled, pure, Except.pure, bind,
    Except.bind, if_true, Bool.false_eq_true, if_false]

/-- con-leche: none — **a conditional, staged**: a triple for each branch,
under the branch's hypothesis, is a triple for the `if`.  (`split` on a
staged goal whose program is a hundred lines long runs `simp` over all of
it; this is the same step with nothing to simplify.) -/
theorem triple_ite {α : Type} {c : Prop} [Decidable c] {x y : AM α}
    {s₀ : AState} {Q : α → AState → Prop}
    (h1 : c → ⦃fun s => ⌜s = s₀⌝⦄ x ⦃⇓? a s => ⌜Q a s⌝⦄)
    (h2 : ¬ c → ⦃fun s => ⌜s = s₀⌝⦄ y ⦃⇓? a s => ⌜Q a s⌝⦄) :
    ⦃fun s => ⌜s = s₀⌝⦄ (if c then x else y) ⦃⇓? a s => ⌜Q a s⌝⦄ := by
  by_cases hc : c
  · rw [if_pos hc]; exact h1 hc
  · rw [if_neg hc]; exact h2 hc

/-- con-leche: none — **a conditional with a shared continuation**: the
`do` elaborator copies the join point into both branches of
`let v ← if c then x else y`, and this puts it back. -/
theorem triple_ite_seq {α β : Type} {c : Prop} [Decidable c] {x y : AM α}
    {k : α → AM β} {s₀ : AState} {Q : α → AState → Prop}
    {R : β → AState → Prop}
    (hxy : ⦃fun s => ⌜s = s₀⌝⦄ (if c then x else y) ⦃⇓? a s => ⌜Q a s⌝⦄)
    (hk : ∀ a s₁, Q a s₁ → ⦃fun s => ⌜s = s₁⌝⦄ k a ⦃⇓? b s => ⌜R b s⌝⦄) :
    ⦃fun s => ⌜s = s₀⌝⦄ (if c then x >>= k else y >>= k)
      ⦃⇓? b s => ⌜R b s⌝⦄ := by
  have e : (if c then x >>= k else y >>= k) = ((if c then x else y) >>= k) := by
    split <;> rfl
  rw [e]
  exact triple_seq hxy hk

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — the merge at
the per-slot certificates' conditional. -/
theorem pcIte_mono {F F' : Nat} (hle : F ≤ F') {d : Nat} {Tn : Name}
    {ls : List Level} {xs : List Expr} {y : Expr} {lps : List Name}
    {nF : Nat} {c r : Bool}
    (h : (if c = true then pure true else
      ConLeche.structEtaProjCertsFueled mode env F d Tn ls xs y lps
        (List.range nF) : CheckM Bool) = .ok r) :
    (if c = true then pure true else
      ConLeche.structEtaProjCertsFueled mode env F' d Tn ls xs y lps
        (List.range nF) : CheckM Bool) = .ok r := by
  cases c
  · simp only [Bool.false_eq_true, if_false] at h ⊢
    exact structEtaProjCertsFueled_mono hle h
  · simp only [if_true] at h ⊢; exact h

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
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.structEtaCertWith mode (coreKnot mode fe id fuel) fe d a b wtb
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.structEtaCertWithFueled mode env F d x y w)
          r⌝⦄ := by
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
  refine view_bind_triple hvh ?_
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
      · rw [if_pos hlenT]
        have hlenP : x.getAppArgs.length = cnP + cnF := hlenEq ▸ hlenT
        -- stage 3: the stuck side's type's head
        refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ wtb hok.state
          (by rw [hdw]; rfl)) ?_
        rintro hw' s3 ⟨hs3, hrelW⟩
        subst s3
        have hdw' : denoteE s₀.store hw' = some w.getAppFn := hrelW w hdw
        obtain ⟨vw, hvw⟩ := denoteE_view hdw'
        refine view_bind_triple hvw ?_
        cases vw
        case const T us' =>
          obtain ⟨Tn, ls', hgw, hTn, hus'⟩ := denote_const_inv hwf hvw hdw'
          dsimp only
          split
          next icvT icaps hfdT =>
            obtain ⟨dcvT, dcaps, hdcvT, hdcaps, hfindT⟩ :=
              env_ind_of_index hok hTn hfdT
            have hcapsD : ∃ ct, denoteN s₀.store.ns icaps.etaCtor = some ct ∧
                dcaps = ⟨icaps.eta, ct, icaps.etaParams, icaps.etaFields,
                  icaps.unitlike, icaps.unitParams, icaps.ruleK, icaps.sortZ⟩ := by
              simp only [Frontend.denoteCaps] at hdcaps
              split at hdcaps
              · rename_i ct hct; exact ⟨ct, hct, (Option.some.inj hdcaps).symm⟩
              · simp at hdcaps
            obtain ⟨ct, hct, rfl⟩ := hcapsD
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
            rintro tw s6 ⟨hok6, hx6, hp6, htw⟩
            refine triple_ite_seq (Q := fun slots s => CheckOK mode env fe s ∧
              Ext s6.store s.store ∧ s.pins = s6.pins ∧
              slots = (ConLeche.towerSlotsAll env Tn icaps.etaFields ||
                ConLeche.recSlotsAll env Tn icaps.etaFields)) ?_ ?_
            · refine triple_ite (fun htt => ?_) (fun htf => ?_)
              · refine triple_pureC ⟨hok6, Ext.refl _, rfl, ?_⟩
                have : ConLeche.towerSlotsAll env Tn icaps.etaFields = true :=
                  htw ▸ htt
                rw [this, Bool.true_or]
              · refine triple_mono (recSlotsAll_spec s6 T Tn icaps.etaFields hok6
                  (denoteN_ext hTn (hx5.trans hx6))) ?_
                rintro r s' ⟨h1, h2, h3, h4⟩
                refine ⟨h1, h2, h3, ?_⟩
                have : ConLeche.towerSlotsAll env Tn icaps.etaFields = false := by
                  rw [← htw]; simpa using htf
                rw [h4, this, Bool.false_or]
            rintro slots s7 ⟨hok7, hx7, hp7, hslots⟩
            have hx07 : Ext s₀.store s7.store := hx5.trans (hx6.trans hx7)
            have hp07 : s7.pins = s₀.pins := hp7.trans (hp6.trans hp5)
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
                    icaps.unitlike, icaps.unitParams, icaps.ruleK, icaps.sortZ⟩ := by
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
                have hc := ConLeche.certs_of_verifiedChecks hμ
                refine triple_ite (fun _ => ?_) (fun hnc => absurd hc hnc)
                -- stage 7: the type former's telescope certificate
                have hcv8 := denoteCV_ext hdcvT hx08
                have hnameT : dcvT.name = Tn := env_find_name hfindT
                refine triple_seq (constTyAt_spec s8 icvT us' Tn ls' _ hok8
                  (by rw [denoteCV_name hcv8, hnameT]) (denoteLs_ext hus' hx08)
                  hfindT hcv8) ?_
                rintro ty s10 ⟨hok10, hx10, hp10, hty⟩
                have hx010 := hx08.trans hx10
                have htargs10 := denoteEList_ext hx010 _ _ htargs
                refine triple_seq (iotaCerts_spec hsim d false ty targs s10 hok10
                  ⟨_, _, hty, Expr.WScoped.of_not_hasFvar
                    (ConLeche.const_ty_hasFvar henv hfindT ls'), htargs10,
                    hwtargs⟩) ?_
                rintro fam s11 ⟨hok11, hx11, hp11, hfam⟩
                obtain ⟨F1, hF1⟩ := hfam _ _ hty htargs10
                have hx011 := hx010.trans hx11
                have hp011 : s11.pins = s₀.pins := hp11.trans (hp10.trans hp08)
                refine triple_ite (fun hfT' => ?_) (fun hfF => ?_)
                · have hfam' : fam = true := hfT'
                  subst hfam'
                  -- stage 8: the per-slot certificates
                  refine triple_seq (towerSlotsAll_spec s11 T Tn icaps.etaFields
                    hok11 (denoteN_ext hTn hx011)) ?_
                  rintro tw2 s12 ⟨hok12, hx12, hp12, htw2⟩
                  refine triple_ite (fun hnc => absurd hnc (by simp [hc]))
                    (fun _ => ?_)
                  have hx012 := hx011.trans hx12
                  refine triple_ite_seq (Q := fun pc s => CheckOK mode env fe s ∧
                    Ext s12.store s.store ∧ s.pins = s12.pins ∧
                    SimBOp (fun F => (if ConLeche.towerSlotsAll env Tn
                        icaps.etaFields then pure true
                      else ConLeche.structEtaProjCertsFueled mode env F d Tn ls'
                        w.getAppArgs y dcvT.levelParams
                        (List.range icaps.etaFields) : CheckM Bool)) pc) ?_ ?_
                  · refine triple_ite (fun htt => ?_) (fun htf => ?_)
                    · have ht : ConLeche.towerSlotsAll env Tn icaps.etaFields =
                          true := htw2 ▸ htt
                      exact triple_pureC ⟨hok12, Ext.refl _, rfl, 0,
                        by dsimp only; rw [if_pos ht]; rfl⟩
                    · have ht : ConLeche.towerSlotsAll env Tn icaps.etaFields =
                          false := by rw [← htw2]; simpa using htf
                      refine triple_mono (structEtaProjCerts_spec henv hsim d T us'
                        targs b icvT.levelParams Tn ls' w.getAppArgs y
                        dcvT.levelParams hwtargs hwb (List.range icaps.etaFields)
                        s12 hok12 (denoteN_ext hTn hx012) (denoteLs_ext hus' hx012)
                        (denoteEList_ext hx012 _ _ htargs) (denote_ext hdb hx012)
                        (denoteNList_ext hx012.lss.ls.ns _ _ hlpsT)) ?_
                      rintro r s' ⟨h1, h2, h3, F, hF⟩
                      exact ⟨h1, h2, h3, F, by
                        dsimp only; rw [if_neg (by simp [ht])]; exact hF⟩
                  rintro pc s13 ⟨hok13, hx13, hp13, F2, hF2⟩
                  have hx013 := hx012.trans hx13
                  have hp013 : s13.pins = s₀.pins :=
                    hp13.trans (hp12.trans hp011)
                  refine triple_ite (fun hpT => ?_) (fun hpF => ?_)
                  · have hpc : pc = true := hpT
                    subst hpc
                    -- stage 9: the parameters agree
                    have haargs13 := denoteEList_ext hx013 _ _
                      (ExprOps.denoteEList_take icaps.etaParams aargs _ haargs)
                    refine triple_seq (defEqList_spec hsim s13 d
                      (aargs.take icaps.etaParams) targs _ _ hok13 haargs13
                      (denoteEList_ext hx013 _ _ htargs)
                      (fun z hz => hwx z (List.mem_of_mem_take hz)) hwtargs) ?_
                    rintro dq s14 ⟨hok14, hx14, hp14, F3, hF3⟩
                    have hx014 := hx013.trans hx14
                    have hp014 : s14.pins = s₀.pins := hp14.trans hp013
                    refine triple_ite (fun hdT => ?_) (fun hdF => ?_)
                    · have hdq : dq = true := hdT
                      subst hdq
                      -- stage 11: the fabricated fields agree
                      have hfin : ∀ (s15 : AState) (G0 : Nat),
                          CheckOK mode env fe s15 → Ext s₀.store s15.store →
                          s15.pins = s₀.pins →
                          (∀ G, G0 ≤ G → (if mode.ttChecks then
                              ConLeche.iotaCertsFueled mode env G d false
                                (dcvc.type.instantiateLevelParams dcvc.levelParams
                                  ls)
                                (w.getAppArgs ++ ConLeche.etaProjs env Tn ls'
                                  w.getAppArgs y icaps.etaFields)
                            else pure true : CheckM Bool) = .ok true) →
                          ⦃fun s => ⌜s = s15⌝⦄
                            (do
                              let projs ← ConRon.Arena.etaProjs fe T us' targs b
                                icaps.etaFields
                              ConRon.Arena.defEqList (coreKnot mode fe id fuel) fe d
                                (aargs.drop icaps.etaParams) projs)
                          ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧
                            Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
                            SimBOp (fun F => ConLeche.structEtaCertWithFueled mode
                              env F d x y w) r⌝⦄ := by
                        intro s15 G0 hok15 hx015 hp015 hG0
                        refine triple_seq (etaProjs_spec s15 T us' targs b
                          icaps.etaFields Tn ls' w.getAppArgs y hok15
                          (denoteN_ext hTn hx015) (denoteLs_ext hus' hx015)
                          (denoteEList_ext hx015 _ _ htargs)
                          (denote_ext hdb hx015)) ?_
                        rintro projs s16 ⟨hok16, hx16, hp16, hprojs⟩
                        have hx016 := hx015.trans hx16
                        refine triple_mono (defEqList_spec hsim s16 d
                          (aargs.drop icaps.etaParams) projs _ _ hok16
                          (denoteEList_ext hx016 _ _
                            (ExprOps.denoteEList_drop icaps.etaParams aargs _
                              haargs))
                          hprojs (fun z hz => hwx z (List.mem_of_mem_drop hz))
                          (etaProjs_WScoped hwtargs hwb)) ?_
                        rintro r s17 ⟨hok17, hx17, hp17, F5, hF5⟩
                        refine ⟨hok17, hx016.trans hx17,
                          hp17.trans (hp16.trans hp015), F1 + F2 + F3 + G0 + F5, ?_⟩
                        exact (((((hEx (F1 + F2 + F3 + G0 + F5)).2.2 hlv
                          (iotaCertsFueled_mono (by omega) hF1) true
                          (pcIte_mono (by omega) hF2)).2 rfl true
                          (defEqListFueled_mono (by omega) hF3)).2 rfl true
                          (hG0 _ (by omega))).2 rfl r
                          (defEqListFueled_mono (by omega) hF5))
                      refine triple_ite (fun httT => ?_) (fun httF => ?_)
                      · -- stage 10: the synthetic-spine certificate (TT lane)
                        have hcv14 := denoteCV_ext hdcvc hx014
                        have hnameC : dcvc.name = cn := env_find_name hfindc
                        refine triple_seq (constTyAt_spec s14 icvc us cn ls _ hok14
                          (by rw [denoteCV_name hcv14, hnameC])
                          (denoteLs_ext hus hx014) hfindc hcv14) ?_
                        rintro tyC s15 ⟨hok15, hx15, hp15, htyC⟩
                        have hx015 := hx014.trans hx15
                        refine triple_seq (etaProjs_spec s15 T us' targs b
                          icaps.etaFields Tn ls' w.getAppArgs y hok15
                          (denoteN_ext hTn hx015) (denoteLs_ext hus' hx015)
                          (denoteEList_ext hx015 _ _ htargs)
                          (denote_ext hdb hx015)) ?_
                        rintro projs s16 ⟨hok16, hx16, hp16, hprojs⟩
                        have hx016 := hx015.trans hx16
                        have happ := denoteEList_appendC targs projs _ _
                          (denoteEList_ext hx016 _ _ htargs) hprojs
                        have hwapp : ∀ z ∈ w.getAppArgs ++ ConLeche.etaProjs env Tn
                            ls' w.getAppArgs y icaps.etaFields,
                            Expr.WScoped d z := by
                          intro z hz
                          rcases List.mem_append.mp hz with hz | hz
                          · exact hwtargs z hz
                          · exact etaProjs_WScoped hwtargs hwb z hz
                        have htyC16 := denote_ext htyC hx16
                        refine triple_seq (iotaCerts_spec hsim d false tyC
                          (targs ++ projs) s16 hok16
                          ⟨_, _, htyC16, Expr.WScoped.of_not_hasFvar
                            (ConLeche.const_ty_hasFvar henv hfindc ls), happ,
                            hwapp⟩) ?_
                        rintro ttb s17 ⟨hok17, hx17, hp17, httb⟩
                        obtain ⟨F4, hF4⟩ := httb _ _ htyC16 happ
                        have hx017 := hx016.trans hx17
                        have hp017 : s17.pins = s₀.pins :=
                          hp17.trans (hp16.trans (hp15.trans hp014))
                        have hF4' : ∀ G, F4 ≤ G → (if mode.ttChecks then
                            ConLeche.iotaCertsFueled mode env G d false
                              (dcvc.type.instantiateLevelParams dcvc.levelParams ls)
                              (w.getAppArgs ++ ConLeche.etaProjs env Tn ls'
                                w.getAppArgs y icaps.etaFields)
                          else pure true : CheckM Bool) = .ok ttb := fun G hle => by
                          rw [if_pos httT]; exact iotaCertsFueled_mono hle hF4
                        refine triple_ite (fun htbT => ?_) (fun htbF => ?_)
                        · have htb : ttb = true := htbT
                          subst htb
                          exact hfin s17 F4 hok17 hx017 hp017 hF4'
                        · have htb : ttb = false := by simpa using htbF
                          subst htb
                          exact triple_pureC ⟨hok17, hx017, hp017,
                            F1 + F2 + F3 + F4,
                            (((((hEx (F1 + F2 + F3 + F4)).2.2 hlv
                              (iotaCertsFueled_mono (by omega) hF1) true
                              (pcIte_mono (by omega) hF2)).2 rfl true
                              (defEqListFueled_mono (by omega) hF3)).2 rfl false
                              (hF4' _ (by omega))).1 rfl)⟩
                      · refine triple_seq (triple_pureC
                          (Q := fun (r : Bool) s => r = true ∧ s = s14)
                          ⟨rfl, rfl⟩) ?_
                        rintro ttb s' ⟨rfl, hs'⟩
                        subst s'
                        refine triple_ite (fun _ => ?_) (fun h => absurd rfl h)
                        exact hfin s14 0 hok14 hx014 hp014
                          (fun G _ => by rw [if_neg httF]; rfl)
                    · have hdq : dq = false := by simpa using hdF
                      subst hdq
                      exact triple_pureC ⟨hok14, hx014, hp014, F1 + F2 + F3,
                        ((((hEx (F1 + F2 + F3)).2.2 hlv
                          (iotaCertsFueled_mono (by omega) hF1) true
                          (pcIte_mono (by omega) hF2)).2 rfl false
                          (defEqListFueled_mono (by omega) hF3)).1 rfl)⟩
                  · have hpc : pc = false := by simpa using hpF
                    subst hpc
                    exact triple_pureC ⟨hok13, hx013, hp013, F1 + F2,
                      (((hEx (F1 + F2)).2.2 hlv
                        (iotaCertsFueled_mono (by omega) hF1) false
                        (pcIte_mono (by omega) hF2)).1 rfl)⟩
                · have hfam' : fam = false := by simpa using hfF
                  subst hfam'
                  exact triple_pureC ⟨hok11, hx011, hp011, F1,
                    (hEx F1).2.1 hlv hF1⟩
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
            mvcgen
            bridge_peel; subst_vars
            exact ⟨hok, Ext.refl _, rfl, 0, hres⟩
        all_goals
          have hres : ConLeche.structEtaCertWithFueled mode env 0 d x y w =
              .ok false := structEtaCertWith_nohead_w hgf hfindc hlenP
                (denote_not_const hwf hvw hdw' (by intro c us h; cases h))
          dsimp only
          mvcgen
          bridge_peel; subst_vars
          exact ⟨hok, Ext.refl _, rfl, 0, hres⟩
      · rw [if_neg hlenT]
        have hres : ConLeche.structEtaCertWithFueled mode env 0 d x y w =
            .ok false := structEtaCertWith_len hgf hfindc (by rw [hlenEq]; exact hlenT)
        mvcgen
        bridge_peel; subst_vars
        exact ⟨hok, Ext.refl _, rfl, 0, hres⟩
    next hnd =>
      have hnc := env_not_ctor_of_index hok hcn (fun v p q h => hnd v p q h)
      have hres : ConLeche.structEtaCertWithFueled mode env 0 d x y w =
          .ok false := structEtaCertWith_noctor hgf hnc
      mvcgen
      bridge_peel; subst_vars
      exact ⟨hok, Ext.refl _, rfl, 0, hres⟩
  all_goals
    have hres : ConLeche.structEtaCertWithFueled mode env 0 d x y w =
        .ok false := structEtaCertWith_nohead
          (denote_not_const hwf hvh hdd (by intro c us h; cases h))
    dsimp only
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, 0, hres⟩

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
  refine view_bind_triple hvh ?_
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
    refine view_bind_triple hvv ?_
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
      refine view_bind_triple hvv2 ?_
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

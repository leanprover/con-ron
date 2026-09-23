/-
# `ConRon.Bridge.Core.Walks.InferSpine` — the batched application spine

Task #97-P3-Core round 6.  The twin's `.app` clauses of `inferBody` and
`inferBodyIO` are `inferApp`/`inferAppIOAt`: the head is inferred ONCE and
the argument vector is walked by `inferSpine`/`inferSpineIO`, con-leche's own
cached-tier clauses (`Cached/CoreC.lean:1011-1091`, task #97-P6-9).  The
identification with the chained clause is con-leche's:
`Verify/BetaSpine.lean`'s `inferSpine_sound` (1566) and `inferSpineIO_sound`
(2041), stated over the PURE mirrors `ConLeche.inferSpine` /
`ConLeche.inferSpineIO`.  What this module owes is the carry: the twin's
handle-level walk denotes the pure mirror at `pureFns … F`, for some `F`
(`inferSpine_go`, `inferSpineIO_go`), which is con-leche's own
`Verify/Cached/DiscC4.lean:808 inferSpineC_sim` at this tier.

The invariant is con-leche's: the pending telescope `ty` under the push-order
accumulator `acc` denotes `tyx` under `ws`, and `tyx.instantiateList ws` is
well-scoped.
-/
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.Core.Walks.Proj
import ConLeche.Verify.BetaSpine

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. Store facts -/

/-- con-leche: none — a `viewBind` read at a handle tagged `.forallE` is the
handle's `view`. -/
theorem view_of_viewBind_forallE {st : EStore} {i ty b : EIdx}
    {m : BinderMeta} (htg : (i.tag == ETag.forallE) = true)
    (h : st.viewBind i = some (ty, b, m)) :
    st.view i = some (.forallE ty b m) := by
  have htg' : i.tag = ETag.forallE := by simpa using htg
  have hb : ETag.isBind i.tag = true := by rw [htg']; decide
  unfold EStore.view
  rw [if_pos hb, h]
  simp only [eBindView, htg']
  simp [ETag.lam, ETag.forallE]

/-- con-leche: none — a handle whose tag is not `.forallE` denotes no `∀`. -/
theorem denote_not_forallE_of_tagB {st : EStore} (hwf : StoreWF st)
    {h : EIdx} {e : Expr} (he : denoteE st h = some e)
    (htag : ¬ (h.tag == ETag.forallE) = true) :
    ∀ p q m, e ≠ .forallE p q m := by
  obtain ⟨v, hv⟩ := denoteE_view he
  refine denote_not_forallE hwf hv he ?_
  rintro a b m rfl
  exact htag (by rw [EStore.tagOf_of_view hv]; rfl)

/-- con-leche: ConLeche/Kernel/Core.lean:1216 inferBody (`e.getAppFn` /
`e.getAppArgs`) — `headAndArgs` at an application handle: the spine's head
and its argument vector. -/
theorem headAndArgs_app_spec (s₀ : AState) (e : EIdx) (x : Expr)
    (hok : StateOK s₀) (hden : denoteE s₀.store e = some x)
    (htag : (e.tag == ETag.app) = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ headAndArgs e
    ⦃⇓? r s' => ⌜s' = s₀ ∧ denoteE s₀.store r.1 = some x.getAppFn ∧
        Frontend.denoteEList s₀.store r.2.toList = some x.getAppArgs⌝⦄ := by
  unfold headAndArgs
  rw [if_pos htag]
  refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ e hok
    (by rw [hden]; rfl)) ?_
  rintro hd s1 ⟨hs1, hrelF⟩
  subst s1
  refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s₀ e hok
    (by rw [hden]; rfl)) ?_
  rintro va s2 ⟨hs2, hrelA⟩
  subst s2
  mvcgen
  bridge_peel; subst_vars
  exact ⟨rfl, hrelF x hden, by simpa using hrelA x hden⟩

/-! ## 2. The pure mirror's steps -/

/-- con-leche: ConLeche/Verify/BetaSpine.lean:1293 inferSpine_pi — the
syntactic-`∀` step, certificate passed. -/
theorem inferSpine_pi_step {F d : Nat} {dom body x ta : Expr}
    {mt : BinderMeta} {ws xs : List Expr}
    (hi : ConLeche.inferTypeCore mode env F d x = .ok ta)
    (hd : ConLeche.isDefEqCore mode env F d ta (dom.instantiateList ws)
      = .ok true) :
    ConLeche.inferSpine (pureFns mode env F) d (.forallE dom body mt) ws
        (x :: xs) =
      ConLeche.inferSpine (pureFns mode env F) d body (x :: ws) xs := by
  have e1 : (pureFns mode env F).infer d x = .ok ta := hi
  have e2 : (pureFns mode env F).defeq d ta (dom.instantiateList ws)
      = .ok true := hd
  rw [ConLeche.inferSpine_pi]
  unfold ConLeche.inferSpinePi
  simp [e1, e2, bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Verify/BetaSpine.lean:1300 inferSpine_ne_pi — the
normalise-and-retry step, certificate passed. -/
theorem inferSpine_whnf_step {F d : Nat} {ty dom body x ta : Expr}
    {mt : BinderMeta} {ws xs : List Expr}
    (hne : ∀ p q m, ty ≠ .forallE p q m)
    (hw : ConLeche.whnf mode env F d (ty.instantiateList ws)
      = .ok (.forallE dom body mt))
    (hi : ConLeche.inferTypeCore mode env F d x = .ok ta)
    (hd : ConLeche.isDefEqCore mode env F d ta dom = .ok true) :
    ConLeche.inferSpine (pureFns mode env F) d ty ws (x :: xs) =
      ConLeche.inferSpine (pureFns mode env F) d body [x] xs := by
  have e0 : (pureFns mode env F).whnf d (ty.instantiateList ws)
      = .ok (.forallE dom body mt) := hw
  have e1 : (pureFns mode env F).infer d x = .ok ta := hi
  have e2 : (pureFns mode env F).defeq d ta dom = .ok true := hd
  rw [ConLeche.inferSpine_ne_pi _ _ hne]
  unfold ConLeche.inferSpineWhnf
  simp [e0, e1, e2, bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Verify/BetaSpine.lean:1698 inferSpineIO_pi — the
syntactic-`∀` step at a licensed (`never`) binder: no certificate. -/
theorem inferSpineIO_pi_skip {F d : Nat} {dom body x : Expr}
    {mt : BinderMeta} {ws xs : List Expr} (hn : mt.pw.isNever = true) :
    ConLeche.inferSpineIO (pureFns mode env F) d (.forallE dom body mt) ws
        (x :: xs) =
      ConLeche.inferSpineIO (pureFns mode env F) d body (x :: ws) xs := by
  rw [ConLeche.inferSpineIO_pi]
  unfold ConLeche.inferSpineIOPi
  simp [hn]

/-- con-leche: ConLeche/Verify/BetaSpine.lean:1698 inferSpineIO_pi — the
syntactic-`∀` step, certificate run and passed. -/
theorem inferSpineIO_pi_cert {F d : Nat} {dom body x ta : Expr}
    {mt : BinderMeta} {ws xs : List Expr} (hn : mt.pw.isNever = false)
    (hi : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (hd : ConLeche.isDefEqCore mode env F d ta (dom.instantiateList ws)
      = .ok true) :
    ConLeche.inferSpineIO (pureFns mode env F) d (.forallE dom body mt) ws
        (x :: xs) =
      ConLeche.inferSpineIO (pureFns mode env F) d body (x :: ws) xs := by
  have e1 : (pureFns mode env F).inferIO d x = .ok ta := hi
  have e2 : (pureFns mode env F).defeq d ta (dom.instantiateList ws)
      = .ok true := hd
  rw [ConLeche.inferSpineIO_pi]
  unfold ConLeche.inferSpineIOPi
  simp [hn, e1, e2, bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Verify/BetaSpine.lean:1705 inferSpineIO_ne_pi — the
normalise-and-retry step at a licensed binder. -/
theorem inferSpineIO_whnf_skip {F d : Nat} {ty dom body x : Expr}
    {mt : BinderMeta} {ws xs : List Expr}
    (hne : ∀ p q m, ty ≠ .forallE p q m)
    (hw : ConLeche.whnf mode env F d (ty.instantiateList ws)
      = .ok (.forallE dom body mt))
    (hn : mt.pw.isNever = true) :
    ConLeche.inferSpineIO (pureFns mode env F) d ty ws (x :: xs) =
      ConLeche.inferSpineIO (pureFns mode env F) d body [x] xs := by
  have e0 : (pureFns mode env F).whnf d (ty.instantiateList ws)
      = .ok (.forallE dom body mt) := hw
  rw [ConLeche.inferSpineIO_ne_pi _ _ hne]
  unfold ConLeche.inferSpineIOWhnf
  simp [e0, hn, bind, Except.bind]

/-- con-leche: ConLeche/Verify/BetaSpine.lean:1705 inferSpineIO_ne_pi — the
normalise-and-retry step, certificate run and passed. -/
theorem inferSpineIO_whnf_cert {F d : Nat} {ty dom body x ta : Expr}
    {mt : BinderMeta} {ws xs : List Expr}
    (hne : ∀ p q m, ty ≠ .forallE p q m)
    (hw : ConLeche.whnf mode env F d (ty.instantiateList ws)
      = .ok (.forallE dom body mt))
    (hn : mt.pw.isNever = false)
    (hi : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (hd : ConLeche.isDefEqCore mode env F d ta dom = .ok true) :
    ConLeche.inferSpineIO (pureFns mode env F) d ty ws (x :: xs) =
      ConLeche.inferSpineIO (pureFns mode env F) d body [x] xs := by
  have e0 : (pureFns mode env F).whnf d (ty.instantiateList ws)
      = .ok (.forallE dom body mt) := hw
  have e1 : (pureFns mode env F).inferIO d x = .ok ta := hi
  have e2 : (pureFns mode env F).defeq d ta dom = .ok true := hd
  rw [ConLeche.inferSpineIO_ne_pi _ _ hne]
  unfold ConLeche.inferSpineIOWhnf
  simp [e0, e1, e2, hn, bind, Except.bind, pure, Except.pure]

/-- con-leche: none — the one-slot accumulator `#[a]`. -/
theorem InstLVec.single {st : EStore} {a : EIdx} {x : Expr}
    (hx : denoteE st a = some x) : ExprOps.InstLVec st #[a] [x] :=
  InstLVec.push (InstLVec.empty st) hx

/-! ## 3. The full-grade spine walk -/

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean:808 inferSpineC_sim —
**the carry of `inferSpine`**: the twin's walk at the push-order
accumulator `acc` and the cursor `i` denotes con-leche's pure mirror
`ConLeche.inferSpine` at some fuel, on the pending telescope `tyx`, the
pending substitution `ws` and the remaining arguments `xs`.  Induction on
the arguments left. -/
theorem inferSpine_go {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (d : Nat) (args : Array EIdx) :
    ∀ (k : Nat) (ty : EIdx) (acc : Array EIdx) (i : Nat) (s₀ : AState)
      (tyx : Expr) (ws xs : List Expr),
      args.size - i = k → CheckOK mode env fe s₀ →
      denoteE s₀.store ty = some tyx → ExprOps.InstLVec s₀.store acc ws →
      Expr.WScoped d (tyx.instantiateList ws) →
      Frontend.denoteEList s₀.store (args.toList.drop i) = some xs →
      (∀ x ∈ xs, Expr.WScoped d x) →
      ⦃fun s => ⌜s = s₀⌝⦄
        ConRon.Arena.inferSpine mode (coreKnot mode fe id fuel) fe d ty acc
          args i
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          ∃ v, denoteE s'.store r = some v ∧ Expr.WScoped d v ∧
            ∃ F, ConLeche.inferSpine (pureFns mode env F) d tyx ws xs
              = .ok v⌝⦄ := by
  intro k
  induction k with
  | zero =>
    intro ty acc i s₀ tyx ws xs hk hok hty hacc hwty hxs _hwxs
    have hi : ¬ i < args.size := by omega
    rw [ConRon.Arena.inferSpine, dif_neg hi]
    have hnil : xs = [] := by
      have h0 : args.toList.drop i = [] :=
        List.drop_eq_nil_of_le (by simp; omega)
      rw [h0] at hxs
      exact denoteEList_nil_inv hxs
    subst hnil
    refine triple_mono (ExprOps.instantiateListFast_spec coreWalkFuel s₀ ty
      acc 0 ws hok.state hacc (by rw [hty]; rfl)) ?_
    rintro r s' ⟨hst, hx, _, hc, hp, _, hrel⟩
    refine ⟨hok.mono hst hx hc hp, hx, hp, _, hrel _ hty, hwty, 0, ?_⟩
    rw [ConLeche.inferSpine_nil]; rfl
  | succ k ih =>
    intro ty acc i s₀ tyx ws xs hk hok hty hacc hwty hxs hwxs
    have hi : i < args.size := by omega
    rw [ConRon.Arena.inferSpine, dif_pos hi]
    obtain ⟨x, xs', rfl, hx, hxs'⟩ := denoteEList_drop_cons hi hxs
    have hwx : Expr.WScoped d x := hwxs x (by simp)
    have hwxs' : ∀ z ∈ xs', Expr.WScoped d z :=
      fun z hz => hwxs z (by simp [hz])
    have hwf := hok.state.wf
    split
    · -- the syntactic `∀`: open the domain under the pending substitution
      rename_i htag
      refine triple_seq (viewBind_spec s₀ ty) ?_
      rintro ob s1 ⟨hs1, hob⟩
      subst s1; subst hob
      split
      · exact triple_failDanglingE
      · rename_i dom body mt hvb
        have hv := view_of_viewBind_forallE htag hvb
        obtain ⟨edom, ebody, rfl, hdd, hdb⟩ := denote_forallE_inv hwf hv hty
        simp only [instantiateList_forallE, Expr.WScoped] at hwty
        refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀
          dom acc 0 ws hok.state hacc (by rw [hdd]; rfl)) ?_
        rintro dom2 s2 ⟨hst2, hx2, _, hc2, hp2, _, hrel2⟩
        have hok2 := hok.mono hst2 hx2 hc2 hp2
        have hd2 : denoteE s2.store dom2 = some (edom.instantiateList ws) :=
          hrel2 _ hdd
        refine triple_seq (hsim.infer s2 d args[i] x hok2 (denote_ext hx hx2)
          hwx) ?_
        rintro ta s3 ⟨hok3, hx3, hp3, vta, hvta, hwvta, F1, hF1⟩
        refine triple_seq (hsim.defeq s3 d ta dom2 vta _ hok3 hvta
          (denote_ext hd2 hx3) hwvta hwty.1) ?_
        rintro b s4 ⟨hok4, hx4, hp4, F2, hF2⟩
        split
        · exact triple_fail
        · rename_i hb
          have hb' : b = true := by simpa using hb
          subst hb'
          have hx04 : Ext s₀.store s4.store := (hx2.trans hx3).trans hx4
          refine triple_mono (ih body (acc.push args[i]) (i + 1) s4 ebody
            (x :: ws) xs' (by omega) hok4 (denote_ext hdb hx04)
            (InstLVec.push (hacc.ext hx04) (denote_ext hx hx04)) ?_
            (denoteEList_ext hx04 _ _ hxs') hwxs') ?_
          · rw [ConLeche.Expr.instantiateList_cons]
            exact Expr.WScoped.instantiate1_gen hwx 0 hwty.2
          · rintro r s5 ⟨hok5, hx5, hp5, v, hv, hwv, F3, hF3⟩
            refine ⟨hok5, hx04.trans hx5, by rw [hp5, hp4, hp3, hp2], v, hv,
              hwv, max (max F1 F2) F3, ?_⟩
            rw [inferSpine_pi_step
              (ConLeche.inferTypeCore_mono (by omega) hF1)
              (ConLeche.isDefEqCore_mono (by omega) hF2)]
            exact ConLeche.inferSpine_mono (by omega) hF3
    · -- not syntactically a `∀`: flush, normalise, retry
      rename_i htag
      have hne := denote_not_forallE_of_tagB hwf hty htag
      refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀
        ty acc 0 ws hok.state hacc (by rw [hty]; rfl)) ?_
      rintro ty2 s2 ⟨hst2, hx2, _, hc2, hp2, _, hrel2⟩
      have hok2 := hok.mono hst2 hx2 hc2 hp2
      refine triple_seq (hsim.whnf s2 d ty2 _ hok2 (hrel2 _ hty) hwty) ?_
      rintro w s3 ⟨hok3, hx3, hp3, vw, hvw, hwvw, F1, hF1⟩
      split
      · rename_i htw
        refine triple_seq (viewBind_spec s3 w) ?_
        rintro ob s3' ⟨hs3, hob⟩
        subst s3'; subst hob
        split
        · exact triple_failDanglingE
        · rename_i dom body mt hvb
          have hv := view_of_viewBind_forallE htw hvb
          obtain ⟨edom, ebody, rfl, hdd, hdb⟩ :=
            denote_forallE_inv hok3.state.wf hv hvw
          have hwdb : Expr.WScoped d edom ∧ Expr.WScoped d ebody := by
            simpa only [Expr.WScoped] using hwvw
          refine triple_seq (hsim.infer s3 d args[i] x hok3
            (denote_ext hx (hx2.trans hx3)) hwx) ?_
          rintro ta s4 ⟨hok4, hx4, hp4, vta, hvta, hwvta, F2, hF2⟩
          refine triple_seq (hsim.defeq s4 d ta dom vta edom hok4 hvta
            (denote_ext hdd hx4) hwvta hwdb.1) ?_
          rintro b s5 ⟨hok5, hx5, hp5, F3, hF3⟩
          split
          · exact triple_fail
          · rename_i hb
            have hb' : b = true := by simpa using hb
            subst hb'
            have hx05 : Ext s₀.store s5.store :=
              ((hx2.trans hx3).trans hx4).trans hx5
            refine triple_mono (ih body #[args[i]] (i + 1) s5 ebody [x] xs'
              (by omega) hok5 (denote_ext hdb (hx4.trans hx5))
              (InstLVec.single (denote_ext hx hx05)) ?_
              (denoteEList_ext hx05 _ _ hxs') hwxs') ?_
            · rw [ConLeche.instList_single]
              exact Expr.WScoped.instantiate1_gen hwx 0 hwdb.2
            · rintro r s6 ⟨hok6, hx6, hp6, v, hv, hwv, F4, hF4⟩
              refine ⟨hok6, hx05.trans hx6, by rw [hp6, hp5, hp4, hp3, hp2],
                v, hv, hwv, max (max F1 F2) (max F3 F4), ?_⟩
              rw [inferSpine_whnf_step hne
                (ConLeche.whnf_mono (by omega) hF1)
                (ConLeche.inferTypeCore_mono (by omega) hF2)
                (ConLeche.isDefEqCore_mono (by omega) hF3)]
              exact ConLeche.inferSpine_mono (by omega) hF4
      · exact triple_fail

/-! ## 4. The io-grade spine walk -/

/-- con-leche: ConLeche/Verify/BetaGate.lean:143 ioSkip_of_verifiedChecks —
the twin's licence test at a verified mode is the datum's `isNever`. -/
theorem ioSkip_eq (hμ : mode.verifiedChecks = true) (pw : PropWhen) :
    mode.ioSkip pw = pw.isNever :=
  ConLeche.ioSkip_of_verifiedChecks hμ

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean inferSpineIOC_sim — **the
carry of `inferSpineIO`**, `inferSpine_go` at the io grade: the record is
`CoreFnsA.ioView` of the knot, so the per-argument inference is the io slot,
and the licence test is the binder's datum alone (`hμ`). -/
theorem inferSpineIO_go {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) (d : Nat) (args : Array EIdx) :
    ∀ (k : Nat) (ty : EIdx) (acc : Array EIdx) (i : Nat) (s₀ : AState)
      (tyx : Expr) (ws xs : List Expr),
      args.size - i = k → CheckOK mode env fe s₀ →
      denoteE s₀.store ty = some tyx → ExprOps.InstLVec s₀.store acc ws →
      Expr.WScoped d (tyx.instantiateList ws) →
      Frontend.denoteEList s₀.store (args.toList.drop i) = some xs →
      (∀ x ∈ xs, Expr.WScoped d x) →
      ⦃fun s => ⌜s = s₀⌝⦄
        ConRon.Arena.inferSpineIO mode
          (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe d ty acc args i
      ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          ∃ v, denoteE s'.store r = some v ∧ Expr.WScoped d v ∧
            ∃ F, ConLeche.inferSpineIO (pureFns mode env F) d tyx ws xs
              = .ok v⌝⦄ := by
  intro k
  induction k with
  | zero =>
    intro ty acc i s₀ tyx ws xs hk hok hty hacc hwty hxs _hwxs
    have hi : ¬ i < args.size := by omega
    rw [ConRon.Arena.inferSpineIO, dif_neg hi]
    have hnil : xs = [] := by
      have h0 : args.toList.drop i = [] :=
        List.drop_eq_nil_of_le (by simp; omega)
      rw [h0] at hxs
      exact denoteEList_nil_inv hxs
    subst hnil
    refine triple_mono (ExprOps.instantiateListFast_spec coreWalkFuel s₀ ty
      acc 0 ws hok.state hacc (by rw [hty]; rfl)) ?_
    rintro r s' ⟨hst, hx, _, hc, hp, _, hrel⟩
    refine ⟨hok.mono hst hx hc hp, hx, hp, _, hrel _ hty, hwty, 0, ?_⟩
    rw [ConLeche.inferSpineIO_nil]; rfl
  | succ k ih =>
    intro ty acc i s₀ tyx ws xs hk hok hty hacc hwty hxs hwxs
    have hi : i < args.size := by omega
    rw [ConRon.Arena.inferSpineIO, dif_pos hi]
    obtain ⟨x, xs', rfl, hx, hxs'⟩ := denoteEList_drop_cons hi hxs
    have hwx : Expr.WScoped d x := hwxs x (by simp)
    have hwxs' : ∀ z ∈ xs', Expr.WScoped d z :=
      fun z hz => hwxs z (by simp [hz])
    have hwf := hok.state.wf
    split
    · -- the syntactic `∀`
      rename_i htag
      refine triple_seq (viewBind_spec s₀ ty) ?_
      rintro ob s1 ⟨hs1, hob⟩
      subst s1; subst hob
      split
      · exact triple_failDanglingE
      · rename_i dom body mt hvb
        have hv := view_of_viewBind_forallE htag hvb
        obtain ⟨edom, ebody, rfl, hdd, hdb⟩ := denote_forallE_inv hwf hv hty
        simp only [instantiateList_forallE, Expr.WScoped] at hwty
        have hwnext : Expr.WScoped d (ebody.instantiateList (x :: ws)) := by
          rw [ConLeche.Expr.instantiateList_cons]
          exact Expr.WScoped.instantiate1_gen hwx 0 hwty.2
        cases hn : mt.pw.isNever
        · -- the certificate runs
          have hsk : mode.ioSkip mt.pw = false := by rw [ioSkip_eq hμ, hn]
          simp only [hsk, Bool.false_eq_true, if_false, bind_assoc]
          refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀
            dom acc 0 ws hok.state hacc (by rw [hdd]; rfl)) ?_
          rintro dom2 s2 ⟨hst2, hx2, _, hc2, hp2, _, hrel2⟩
          have hok2 := hok.mono hst2 hx2 hc2 hp2
          have hd2 : denoteE s2.store dom2 = some (edom.instantiateList ws) :=
            hrel2 _ hdd
          refine triple_seq (hsim.inferIO s2 d args[i] x hok2
            (denote_ext hx hx2) hwx) ?_
          rintro ta s3 ⟨hok3, hx3, hp3, vta, hvta, hwvta, F1, hF1⟩
          refine triple_seq (hsim.defeq s3 d ta dom2 vta _ hok3 hvta
            (denote_ext hd2 hx3) hwvta hwty.1) ?_
          rintro b s4 ⟨hok4, hx4, hp4, F2, hF2⟩
          split
          · exact triple_fail
          · rename_i hb
            have hb' : b = true := by simpa using hb
            subst hb'
            have hx04 : Ext s₀.store s4.store := (hx2.trans hx3).trans hx4
            refine triple_mono (ih body (acc.push args[i]) (i + 1) s4 ebody
              (x :: ws) xs' (by omega) hok4 (denote_ext hdb hx04)
              (InstLVec.push (hacc.ext hx04) (denote_ext hx hx04)) hwnext
              (denoteEList_ext hx04 _ _ hxs') hwxs') ?_
            rintro r s5 ⟨hok5, hx5, hp5, v, hv, hwv, F3, hF3⟩
            refine ⟨hok5, hx04.trans hx5, by rw [hp5, hp4, hp3, hp2], v, hv,
              hwv, max (max F1 F2) F3, ?_⟩
            rw [inferSpineIO_pi_cert hn
              (ConLeche.inferTypeIO_mono (by omega) hF1)
              (ConLeche.isDefEqCore_mono (by omega) hF2)]
            exact ConLeche.inferSpineIO_mono (by omega) hF3
        · -- licensed: no certificate
          have hsk : mode.ioSkip mt.pw = true := by rw [ioSkip_eq hμ, hn]
          simp only [hsk, if_true, pure_bind, Bool.not_true,
            Bool.false_eq_true, if_false]
          refine triple_mono (ih body (acc.push args[i]) (i + 1) s₀ ebody
            (x :: ws) xs' (by omega) hok hdb (InstLVec.push hacc hx) hwnext
            hxs' hwxs') ?_
          rintro r s5 ⟨hok5, hx5, hp5, v, hv, hwv, F3, hF3⟩
          refine ⟨hok5, hx5, hp5, v, hv, hwv, F3, ?_⟩
          rw [inferSpineIO_pi_skip hn]
          exact hF3
    · -- not syntactically a `∀`: flush, normalise, retry
      rename_i htag
      have hne := denote_not_forallE_of_tagB hwf hty htag
      refine triple_seq (ExprOps.instantiateListFast_spec coreWalkFuel s₀
        ty acc 0 ws hok.state hacc (by rw [hty]; rfl)) ?_
      rintro ty2 s2 ⟨hst2, hx2, _, hc2, hp2, _, hrel2⟩
      have hok2 := hok.mono hst2 hx2 hc2 hp2
      refine triple_seq (hsim.whnf s2 d ty2 _ hok2 (hrel2 _ hty) hwty) ?_
      rintro w s3 ⟨hok3, hx3, hp3, vw, hvw, hwvw, F1, hF1⟩
      split
      · rename_i htw
        refine triple_seq (viewBind_spec s3 w) ?_
        rintro ob s3' ⟨hs3, hob⟩
        subst s3'; subst hob
        split
        · exact triple_failDanglingE
        · rename_i dom body mt hvb
          have hv := view_of_viewBind_forallE htw hvb
          obtain ⟨edom, ebody, rfl, hdd, hdb⟩ :=
            denote_forallE_inv hok3.state.wf hv hvw
          have hwdb : Expr.WScoped d edom ∧ Expr.WScoped d ebody := by
            simpa only [Expr.WScoped] using hwvw
          have hwnext : Expr.WScoped d (ebody.instantiateList [x]) := by
            rw [ConLeche.instList_single]
            exact Expr.WScoped.instantiate1_gen hwx 0 hwdb.2
          have hx03 : Ext s₀.store s3.store := hx2.trans hx3
          cases hn : mt.pw.isNever
          · have hsk : mode.ioSkip mt.pw = false := by rw [ioSkip_eq hμ, hn]
            simp only [hsk, Bool.false_eq_true, if_false, bind_assoc]
            refine triple_seq (hsim.inferIO s3 d args[i] x hok3
              (denote_ext hx hx03) hwx) ?_
            rintro ta s4 ⟨hok4, hx4, hp4, vta, hvta, hwvta, F2, hF2⟩
            refine triple_seq (hsim.defeq s4 d ta dom vta edom hok4 hvta
              (denote_ext hdd hx4) hwvta hwdb.1) ?_
            rintro b s5 ⟨hok5, hx5, hp5, F3, hF3⟩
            split
            · exact triple_fail
            · rename_i hb
              have hb' : b = true := by simpa using hb
              subst hb'
              have hx05 : Ext s₀.store s5.store := (hx03.trans hx4).trans hx5
              refine triple_mono (ih body #[args[i]] (i + 1) s5 ebody [x] xs'
                (by omega) hok5 (denote_ext hdb (hx4.trans hx5))
                (InstLVec.single (denote_ext hx hx05)) hwnext
                (denoteEList_ext hx05 _ _ hxs') hwxs') ?_
              rintro r s6 ⟨hok6, hx6, hp6, v, hv, hwv, F4, hF4⟩
              refine ⟨hok6, hx05.trans hx6, by rw [hp6, hp5, hp4, hp3, hp2],
                v, hv, hwv, max (max F1 F2) (max F3 F4), ?_⟩
              rw [inferSpineIO_whnf_cert hne
                (ConLeche.whnf_mono (by omega) hF1) hn
                (ConLeche.inferTypeIO_mono (by omega) hF2)
                (ConLeche.isDefEqCore_mono (by omega) hF3)]
              exact ConLeche.inferSpineIO_mono (by omega) hF4
          · have hsk : mode.ioSkip mt.pw = true := by rw [ioSkip_eq hμ, hn]
            simp only [hsk, if_true, pure_bind, Bool.not_true,
              Bool.false_eq_true, if_false]
            refine triple_mono (ih body #[args[i]] (i + 1) s3 ebody [x] xs'
              (by omega) hok3 hdb (InstLVec.single (denote_ext hx hx03))
              hwnext (denoteEList_ext hx03 _ _ hxs') hwxs') ?_
            rintro r s6 ⟨hok6, hx6, hp6, v, hv, hwv, F4, hF4⟩
            refine ⟨hok6, hx03.trans hx6, by rw [hp6, hp3, hp2],
              v, hv, hwv, max F1 F4, ?_⟩
            rw [inferSpineIO_whnf_skip hne
              (ConLeche.whnf_mono (by omega) hF1) hn]
            exact ConLeche.inferSpineIO_mono (by omega) hF4
      · exact triple_fail

/-! ## Census — every theorem of the module at the three standard axioms -/

section Census
#print axioms view_of_viewBind_forallE
#print axioms denote_not_forallE_of_tagB
#print axioms headAndArgs_app_spec
#print axioms inferSpine_pi_step
#print axioms inferSpine_whnf_step
#print axioms inferSpineIO_pi_skip
#print axioms inferSpineIO_pi_cert
#print axioms inferSpineIO_whnf_skip
#print axioms inferSpineIO_whnf_cert
#print axioms inferSpine_go
#print axioms inferSpineIO_go
end Census

end ConRon.Bridge.Core

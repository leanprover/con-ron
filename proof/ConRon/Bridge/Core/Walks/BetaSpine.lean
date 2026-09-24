/-
# `ConRon.Bridge.Core.Walks.BetaSpine` — the batched β spine's carry

Task #97-P3-Core round 6 (lane `whnfapp`).  The twin's `whnfCoreBody` `.app`
clause is con-leche's CACHED-tier clause (`Cached/CoreC.lean:942-996
whnfCoreStepI`, over `whnfAppI`/`betaPeelI`), not the chained spec clause.
con-leche proves the `Expr`-level identification of that batched walk with
the chained one (`Verify/BetaSpine.lean`: the pure mirrors `whnfApp` /
`betaPeel` and `whnfApp_sound`).  What this module owes is the **carry**: the
twin's handle-level `whnfApp` / `betaPeel` denote the mirrors at
`pureFns mode env F`, with `whnfCore` as the continuation.

| walk | twin | con-leche mirror |
|---|---|---|
| `getAppSpine_spec` | `Arena/Core.lean:2070-2084` | `getAppFn`/`getAppArgs` + the spine's nodes |
| `headAndArgs_spec` | `:2089` | `getAppFn`/`getAppArgs` |
| `internAppRebuilt_spec` | `:2062` | `.app` |
| `whnfApp_carry` / `betaPeel_carry` | `:2154` / `:2201` | `Verify/BetaSpine.lean` `whnfApp` / `betaPeel` |

The iota step inside the spine is `iotaRecAt` at the spine the walk already
holds; its rule `iotaRecAt_spec` is stated here as a named child (§2) — the
`iotaRec` tower's own entry point, which `iotaRec_spec` (`Walks/Owed.lean`)
is `getAppFn`/`getAppArgs` over.
-/
import ConRon.Bridge.Core.Walks.PropRead
import ConRon.Bridge.Core.Walks.StrCtor
import ConLeche.Verify.BetaSpine
import ConRon.Bridge.Core.Walks.Iota

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. The read-only spine walks -/

/-- con-leche: none — a handle whose tag is `lam` and which denotes, is a
`viewBind` of the λ it denotes. -/
theorem viewBind_of_lam_tag {st : EStore} (hwf : StoreWF st) {v : EIdx}
    {V : Expr} (htg : v.tag = ETag.lam) (hd : denoteE st v = some V) :
    ∃ ty body mb Ty Body, st.viewBind v = some (ty, body, mb) ∧
      V = .lam Ty Body mb ∧ denoteE st ty = some Ty ∧
      denoteE st body = some Body := by
  obtain ⟨w, hw⟩ := denoteE_view hd
  have htw := EStore.tagOf_of_view hw
  cases w with
  | lam ty b m =>
    obtain ⟨et, eb, rfl, h1, h2⟩ := denote_lam_inv hwf hw hd
    have hb : ETag.isBind v.tag = true := by rw [htg]; decide
    refine ⟨ty, b, m, et, eb, ?_, rfl, h1, h2⟩
    simp only [EStore.view, hb, if_true] at hw
    cases hvb : st.viewBind v with
    | none => rw [hvb] at hw; simp at hw
    | some p =>
      obtain ⟨ty', b', m'⟩ := p
      rw [hvb] at hw
      simp only [eBindView, htg, beq_self_eq_true, if_true,
        Option.some.injEq, ENodeView.lam.injEq] at hw
      obtain ⟨rfl, rfl, rfl⟩ := hw
      rfl
  | _ => rw [htg] at htw; simp [ENodeView.tagOf] at htw <;> contradiction

/-- con-leche: none — `denoteEList` is functional in its store argument's
extension (a convenience over `denoteEList_ext`). -/
theorem denoteEList_ext' {st st' : EStore} (hx : Ext st st') {rs : List EIdx}
    {xs : List Expr} (h : Frontend.denoteEList st rs = some xs) :
    Frontend.denoteEList st' rs = some xs :=
  denoteEList_ext hx _ _ h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:915-923 getAppFn/getAppArgs — the
answer of the arena's one-walk spine read: the head, the argument vector,
and the spine's own `.app` nodes, node `j` denoting the prefix applied to
`j + 1` arguments. -/
def SpineOK (st : EStore) (E : Expr) (r : EIdx × Array EIdx × Array EIdx) :
    Prop :=
  denoteE st r.1 = some E.getAppFn ∧
  Frontend.denoteEList st r.2.1.toList = some E.getAppArgs ∧
  r.2.2.size = r.2.1.size ∧
  ∀ j (hj : j < r.2.2.size),
    denoteE st r.2.2[j] = some (Expr.mkAppN E.getAppFn (E.getAppArgs.take (j + 1)))

/-- con-leche: ConLeche/Kernel/ExprOps.lean:915-923 getAppFn/getAppArgs —
**THEOREM 1 for `getAppSpineGo`**: read-only, and the answer is `SpineOK`. -/
theorem getAppSpineGo_spec : ∀ (fuel : Nat) (s₀ : AState) (h : EIdx)
    (E : Expr), StateOK s₀ → denoteE s₀.store h = some E →
    ⦃fun s => ⌜s = s₀⌝⦄ getAppSpineGo fuel h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ SpineOK s₀.store E r⌝⦄
  | 0, s₀, h, E, _, _ => by
    rw [getAppSpineGo]; exact triple_fail
  | fuel + 1, s₀, h, E, hok, hd => by
    rw [getAppSpineGo]
    by_cases htg : (h.tag == ETag.app) = true
    · rw [if_pos htg]
      refine triple_seq (viewApp_spec s₀ h) ?_
      rintro o s1 ⟨hs1, rfl⟩
      subst s1
      cases hva : s₀.store.viewApp h with
      | none => exact triple_failDanglingE
      | some p =>
        obtain ⟨f, a⟩ := p
        dsimp only
        have hview := view_of_viewApp_tag htg hva
        obtain ⟨Ef, Ea, rfl, hf, ha⟩ := denote_app_inv hok.wf hview hd
        refine triple_seq (getAppSpineGo_spec fuel s₀ f Ef hok hf) ?_
        rintro t s2 ⟨hs2, ht1, ht2, ht3, ht4⟩
        subst s2
        mvcgen
        subst_vars
        refine ⟨rfl, ?_, ?_, ?_, ?_⟩
        · simpa [Expr.getAppFn] using ht1
        · simp only [Array.toList_push, Expr.getAppArgs]
          exact ExprOps.denoteEList_snoc ha _ _ ht2
        · simp [ht3]
        · intro j hj
          have hlen := ExprOps.denoteEList_length _ _ ht2
          simp only [Array.length_toList] at hlen
          simp only [Array.size_push] at hj
          simp only [Expr.getAppFn, Expr.getAppArgs]
          by_cases hjl : j < t.2.2.size
          · rw [Array.getElem_push_lt hjl, ht4 j hjl,
              List.take_append_of_le_length (by omega)]
          · have hje : j = t.2.2.size := by omega
            subst hje
            rw [Array.getElem_push_eq, List.take_of_length_le (by simp; omega),
              Expr.mkAppN_append_one, Expr.mkAppN_getApp]
            exact hd
    · rw [if_neg htg]
      mvcgen
      subst_vars
      have hna : ∀ x y, E ≠ Expr.app x y := by
        obtain ⟨w, hw⟩ := denoteE_view hd
        refine denote_not_app hok.wf hw hd ?_
        intro f a hfa; subst hfa
        exact htg (by rw [EStore.tagOf_of_view hw]; rfl)
      refine ⟨rfl, ?_, ?_, rfl, ?_⟩
      · simpa [ExprOps.getAppFn_of_not_app hna] using hd
      · simp [ExprOps.getAppArgs_of_not_app hna, Frontend.denoteEList]
      · intro j hj; simp at hj

/-- con-leche: ConLeche/Kernel/ExprOps.lean:915-923 getAppFn — the entry. -/
theorem getAppSpine_spec (fuel : Nat) (s₀ : AState) (h : EIdx) (E : Expr)
    (hok : StateOK s₀) (hd : denoteE s₀.store h = some E) :
    ⦃fun s => ⌜s = s₀⌝⦄ getAppSpine fuel h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ SpineOK s₀.store E r⌝⦄ :=
  getAppSpineGo_spec fuel s₀ h E hok hd

/-- con-leche: ConLeche/Kernel/ExprOps.lean:915-923 getAppFn/getAppArgs —
**THEOREM 1 for `headAndArgs`**: read-only; the head and the argument vector
of a reduct. -/
theorem headAndArgs_spec (s₀ : AState) (v : EIdx) (V : Expr)
    (hok : StateOK s₀) (hd : denoteE s₀.store v = some V) :
    ⦃fun s => ⌜s = s₀⌝⦄ headAndArgs v
    ⦃⇓? r s' => ⌜s' = s₀ ∧ denoteE s₀.store r.1 = some V.getAppFn ∧
        Frontend.denoteEList s₀.store r.2.toList = some V.getAppArgs⌝⦄ := by
  unfold headAndArgs
  by_cases htg : (v.tag == ETag.app) = true
  · rw [if_pos htg]
    refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ v hok
      (by rw [hd]; rfl)) ?_
    rintro hh s1 ⟨hs1, hr1⟩
    subst s1
    refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s₀ v hok
      (by rw [hd]; rfl)) ?_
    rintro va s2 ⟨hs2, hr2⟩
    subst s2
    mvcgen
    subst_vars
    exact ⟨rfl, hr1 V hd, by simpa using hr2 V hd⟩
  · rw [if_neg htg]
    mvcgen
    subst_vars
    have hna : ∀ x y, V ≠ Expr.app x y := by
      obtain ⟨w, hw⟩ := denoteE_view hd
      refine denote_not_app hok.wf hw hd ?_
      intro f a hfa; subst hfa
      exact htg (by rw [EStore.tagOf_of_view hw]; rfl)
    exact ⟨rfl, by simpa [ExprOps.getAppFn_of_not_app hna] using hd,
      by simp [ExprOps.getAppArgs_of_not_app hna, Frontend.denoteEList]⟩

/-- con-leche: none — **THEOREM 1 for `internAppRebuilt`**: the upward
cutoff hands back the spine's own node when the caller vouches for it
(`same`), else interns the application; either way the answer denotes
`.app F A`. -/
theorem internAppRebuilt_spec (s₀ : AState) (node : EIdx) (same : Bool)
    (f a : EIdx) (F A : Expr) (hok : CheckOK mode env fe s₀)
    (hf : denoteE s₀.store f = some F) (ha : denoteE s₀.store a = some A)
    (hsame : same = true → denoteE s₀.store node = some (.app F A)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internAppRebuilt node same f a
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ denoteE s'.store r = some (.app F A)⌝⦄ := by
  unfold internAppRebuilt
  cases same with
  | true =>
    simp only [if_true]
    mvcgen
    subst_vars
    exact ⟨hok, Ext.refl _, rfl, by simpa using hsame⟩
  | false =>
    simp only [Bool.false_eq_true, if_false]
    refine triple_mono (internE_ok_spec s₀ (.app f a) hok
      (viewOK_app (by rw [hf]; rfl) (by rw [ha]; rfl))) ?_
    rintro r s' ⟨hck, hx, hp, hr⟩
    refine ⟨hck, hx, hp, ?_⟩
    rw [hr]
    simp [denoteEView, denote_ext hf hx, denote_ext ha hx]

/-! ## 2. The iota step at a held spine

`whnfApp` asks for one ι step at every non-λ reduction step of the spine it
is walking, through `iotaRecAt` at the head and the argument vector it
already holds (task #97-P6-9's hoist).  `iotaRec` is `getAppFn`/`getAppArgs`
over the same entry, so `iotaRecAt_spec` below is the `iotaRec` tower's own
entry rule; `iotaRec_spec` (`Walks/Owed.lean`) cannot stand in for it,
because its two spine reads are fuelled walks whose success at the spine
`whnfApp` holds is not provable (a `⇓?` triple claims nothing when they
throw). -/

/-! `iotaRecAt_spec` is `Walks/Iota.lean`'s (the `iota` lane of round 6,
CLOSED there): the held head is not an application (`hnapp`, a spine head) and
the count is the whole vector (`hn`), both discharged at the call below. -/

/-- con-leche: ConLeche/Verify/BetaSpine.lean:224 iotaRec_head_not_const —
**the iota step `whnfApp` runs at a non-λ head**: `iotaRecAt` when the
spine's head handle is a constant, else `none` off the tag (con-leche's
`iotaArityOk` guard), against con-leche's `iotaRec` at `.app V A`. -/
theorem whnfApp_iotaStep_spec {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hμ : mode.verifiedChecks = true) (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (hd a : EIdx) (vargs : Array EIdx) (V A : Expr)
    (hok : CheckOK mode env fe s₀)
    (hdh : denoteE s₀.store hd = some V.getAppFn)
    (hdv : Frontend.denoteEList s₀.store vargs.toList = some V.getAppArgs)
    (hda : denoteE s₀.store a = some A)
    (hw : Expr.WScoped d (.app V A)) :
    ⦃fun s => ⌜s = s₀⌝⦄
      (if hd.tag == ETag.const then
        ConRon.Arena.iotaRecAt mode (coreKnot mode fe id fuel) fe d hd
          (vargs.push a) (vargs.push a).size
      else pure none : AM (Option EIdx))
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimOOp (fun F => ConLeche.iotaRecFueled mode env F d (.app V A)) d
          s'.store r⌝⦄ := by
  have happ : Expr.mkAppN V.getAppFn (V.getAppArgs ++ [A]) = .app V A := by
    rw [Expr.mkAppN_append_one, Expr.mkAppN_getApp]
  by_cases htc : (hd.tag == ETag.const) = true
  · rw [if_pos htc]
    have hdx : Frontend.denoteEList s₀.store (vargs.push a).toList =
        some (V.getAppArgs ++ [A]) := by
      simp only [Array.toList_push]
      exact ExprOps.denoteEList_snoc hda _ _ hdv
    have h := iotaRecAt_spec hμ henv hsim s₀ d hd (vargs.push a) (vargs.push a).size
      V.getAppFn (V.getAppArgs ++ [A]) hok hdh
      (fun f a => ConLeche.Expr.getAppFn_not_app V f a) rfl hdx (by rw [happ]; exact hw)
    rw [happ] at h
    exact h
  · rw [if_neg htc]
    mvcgen
    subst_vars
    have hnc : ∀ c us, (Expr.app V A).getAppFn ≠ .const c us := by
      obtain ⟨w, hw'⟩ := denoteE_view hdh
      have h1 := denote_not_const hok.state.wf hw' hdh (by
        intro c us hcu; subst hcu
        exact htc (by rw [EStore.tagOf_of_view hw']; rfl))
      intro c us hcu
      exact h1 c us (by simpa [Expr.getAppFn] using hcu)
    refine ⟨hok, Ext.refl _, rfl, none, rfl,
      ⟨fun (x : Expr) (hx : (none : Option Expr) = some x) => by simp at hx,
        0, ?_⟩⟩
    exact ConLeche.iotaRec_head_not_const _ env d hnc

/-! ## 3. The pure mirrors at the pure knot

con-leche's `whnfApp`/`betaPeel` (`Verify/BetaSpine.lean:84-150`) at
`pureFns mode env F`, with the continuation `whnfCore mode env F d` — the
instance `whnfApp_sound` consumes.  One equation per clause, and the fuel
monotonicity through con-leche's `whnfApp_mono`/`betaPeel_mono`. -/

/-- con-leche: ConLeche/Verify/BetaSpine.lean:84 whnfApp — at the pure knot. -/
abbrev mWA (mode : CheckMode) (env : Env) (F d : Nat) (V : Expr)
    (xs : List Expr) : CheckM Expr :=
  ConLeche.whnfApp mode (ConLeche.pureFns mode env F) env d
    (ConLeche.whnfCore mode env F d) V xs

/-- con-leche: ConLeche/Verify/BetaSpine.lean:113 betaPeel — at the pure
knot. -/
abbrev mBP (mode : CheckMode) (env : Env) (F d : Nat) (t : Expr)
    (acc xs : List Expr) : CheckM Expr :=
  ConLeche.betaPeel mode (ConLeche.pureFns mode env F) env d
    (ConLeche.whnfCore mode env F d) t acc xs

/-- con-leche: ConLeche/Verify/BetaSpine.lean:422 whnfApp_mono. -/
theorem mWA_mono {F F' d : Nat} {V r : Expr} {xs : List Expr} (hle : F ≤ F')
    (h : mWA mode env F d V xs = .ok r) : mWA mode env F' d V xs = .ok r :=
  ConLeche.whnfApp_mono ((ConLeche.fueledFns mode env).whnfCore d) _ _
    (fun _ => rfl) (fun _ => rfl) hle h

/-- con-leche: ConLeche/Verify/BetaSpine.lean:432 betaPeel_mono. -/
theorem mBP_mono {F F' d : Nat} {t r : Expr} {acc xs : List Expr}
    (hle : F ≤ F') (h : mBP mode env F d t acc xs = .ok r) :
    mBP mode env F' d t acc xs = .ok r :=
  ConLeche.betaPeel_mono ((ConLeche.fueledFns mode env).whnfCore d) _ _
    (fun _ => rfl) (fun _ => rfl) hle h

/-- con-leche: ConLeche/Verify/BetaSpine.lean:160 whnfApp_nil. -/
theorem mWA_nil {F d : Nat} {V : Expr} : mWA mode env F d V [] = .ok V := by
  simp only [mWA, ConLeche.whnfApp_nil]; rfl

/-- con-leche: ConLeche/Verify/BetaSpine.lean:165 whnfApp_lam — the gated
skip. -/
theorem mWA_lam_skip {F d : Nat} {ty b a : Expr} {mb : BinderMeta}
    {rest : List Expr} (hg : ConLeche.betaGateFires mode mb.pw = true) :
    mWA mode env F d (.lam ty b mb) (a :: rest) = mBP mode env F d b [a] rest := by
  simp only [mWA, mBP, ConLeche.whnfApp_lam, ConLeche.whnfAppLam, hg, if_true]

/-- con-leche: ConLeche/Verify/BetaSpine.lean:165 whnfApp_lam — the
certified β. -/
theorem mWA_lam_cert {F d : Nat} {ty b a ta : Expr} {mb : BinderMeta}
    {rest : List Expr} (hg : ConLeche.betaGateFires mode mb.pw = false)
    (hio : ConLeche.inferTypeIO mode env F d a = .ok ta)
    (hdq : ConLeche.isDefEqCore mode env F d ta ty = .ok true) :
    mWA mode env F d (.lam ty b mb) (a :: rest) = mBP mode env F d b [a] rest := by
  simp only [mWA, mBP, ConLeche.whnfApp_lam, ConLeche.whnfAppLam, hg,
    Bool.false_eq_true, if_false, ConLeche.inferTypeIO_def, hio,
    ConLeche.defeq_def, hdq, bind, Except.bind, if_true]

/-- con-leche: ConLeche/Verify/BetaSpine.lean:165 whnfApp_lam — the
certificate fails: the redex is stuck. -/
theorem mWA_lam_fail {F d : Nat} {ty b a ta : Expr} {mb : BinderMeta}
    {rest : List Expr} (hg : ConLeche.betaGateFires mode mb.pw = false)
    (hio : ConLeche.inferTypeIO mode env F d a = .ok ta)
    (hdq : ConLeche.isDefEqCore mode env F d ta ty = .ok false) :
    mWA mode env F d (.lam ty b mb) (a :: rest) =
      .ok (Expr.mkAppN (.app (.lam ty b mb) a) rest) := by
  simp only [mWA, ConLeche.whnfApp_lam, ConLeche.whnfAppLam, hg,
    Bool.false_eq_true, if_false, ConLeche.inferTypeIO_def, hio,
    ConLeche.defeq_def, hdq, bind, Except.bind]
  rfl

/-- con-leche: ConLeche/Verify/BetaSpine.lean:173 whnfApp_ne_lam — ι fires. -/
theorem mWA_iota_some {F d : Nat} {V a e2 v2 : Expr} {rest : List Expr}
    (hV : ∀ ty b mb, V ≠ .lam ty b mb)
    (hi : ConLeche.iotaRecFueled mode env F d (.app V a) = .ok (some e2))
    (hk : ConLeche.whnfCore mode env F d e2 = .ok v2) :
    mWA mode env F d V (a :: rest) = mWA mode env F d v2 rest := by
  simp only [mWA, ConLeche.whnfApp_ne_lam _ _ _ _ hV, ConLeche.whnfAppIota]
  simp only [ConLeche.iotaRecFueled] at hi
  simp only [hi, hk, bind, Except.bind]

/-- con-leche: ConLeche/Verify/BetaSpine.lean:173 whnfApp_ne_lam — ι does
not fire: one more stuck application. -/
theorem mWA_iota_none {F d : Nat} {V a : Expr} {rest : List Expr}
    (hV : ∀ ty b mb, V ≠ .lam ty b mb)
    (hi : ConLeche.iotaRecFueled mode env F d (.app V a) = .ok none) :
    mWA mode env F d V (a :: rest) = mWA mode env F d (.app V a) rest := by
  simp only [mWA, ConLeche.whnfApp_ne_lam _ _ _ _ hV, ConLeche.whnfAppIota]
  simp only [ConLeche.iotaRecFueled] at hi
  simp only [hi, bind, Except.bind]

/-- con-leche: ConLeche/Verify/BetaSpine.lean:196 betaPeel_nil. -/
theorem mBP_nil {F d : Nat} {t : Expr} {acc : List Expr} :
    mBP mode env F d t acc [] =
      ConLeche.whnfCore mode env F d (t.instantiateList acc) := by
  simp only [mBP, ConLeche.betaPeel_nil]

/-- con-leche: ConLeche/Verify/BetaSpine.lean:215 betaPeel_lam — the gated
skip. -/
theorem mBP_lam_skip {F d : Nat} {ty b a : Expr} {mb : BinderMeta}
    {acc rest : List Expr} (hg : ConLeche.betaGateFires mode mb.pw = true) :
    mBP mode env F d (.lam ty b mb) acc (a :: rest) =
      mBP mode env F d b (a :: acc) rest := by
  simp only [mBP, ConLeche.betaPeel_lam, ConLeche.betaPeelLam, hg, if_true]

/-- con-leche: ConLeche/Verify/BetaSpine.lean:215 betaPeel_lam — the
certified binder. -/
theorem mBP_lam_cert {F d : Nat} {ty b a ta : Expr} {mb : BinderMeta}
    {acc rest : List Expr} (hg : ConLeche.betaGateFires mode mb.pw = false)
    (hio : ConLeche.inferTypeIO mode env F d a = .ok ta)
    (hdq : ConLeche.isDefEqCore mode env F d ta (ty.instantiateList acc) =
      .ok true) :
    mBP mode env F d (.lam ty b mb) acc (a :: rest) =
      mBP mode env F d b (a :: acc) rest := by
  simp only [mBP, ConLeche.betaPeel_lam, ConLeche.betaPeelLam, hg,
    Bool.false_eq_true, if_false, ConLeche.inferTypeIO_def, hio,
    ConLeche.defeq_def, hdq, bind, Except.bind, if_true]

/-- con-leche: ConLeche/Verify/BetaSpine.lean:215 betaPeel_lam — the
certificate fails. -/
theorem mBP_lam_fail {F d : Nat} {ty b a ta : Expr} {mb : BinderMeta}
    {acc rest : List Expr} (hg : ConLeche.betaGateFires mode mb.pw = false)
    (hio : ConLeche.inferTypeIO mode env F d a = .ok ta)
    (hdq : ConLeche.isDefEqCore mode env F d ta (ty.instantiateList acc) =
      .ok false) :
    mBP mode env F d (.lam ty b mb) acc (a :: rest) =
      .ok (Expr.mkAppN (.app ((Expr.lam ty b mb).instantiateList acc) a)
        rest) := by
  simp only [mBP, ConLeche.betaPeel_lam, ConLeche.betaPeelLam, hg,
    Bool.false_eq_true, if_false, ConLeche.inferTypeIO_def, hio,
    ConLeche.defeq_def, hdq, bind, Except.bind]
  rfl

/-- con-leche: ConLeche/Verify/BetaSpine.lean:185 betaPeel_ne_lam. -/
theorem mBP_nonlam {F d : Nat} {t a v : Expr} {acc rest : List Expr}
    (ht : ∀ ty b mb, t ≠ .lam ty b mb)
    (hk : ConLeche.whnfCore mode env F d (t.instantiateList acc) = .ok v) :
    mBP mode env F d t acc (a :: rest) = mWA mode env F d v (a :: rest) := by
  simp only [mBP, mWA, ConLeche.betaPeel_ne_lam _ _ _ _ ht, hk, bind,
    Except.bind]

/-- con-leche: ConLeche/Kernel/Env.lean:174 CheckMode.betaSkip — at a mode
running the verified checks, the executed core's β read is the spec's
gate. -/
theorem betaSkip_eq_fires (hμ : mode.verifiedChecks = true) (pw : PropWhen) :
    mode.betaSkip pw = ConLeche.betaGateFires mode pw := by
  simp [CheckMode.betaSkip, ConLeche.betaGateFires,
    ConLeche.certs_of_verifiedChecks hμ]

/-! ## 4. The carry: the twin's spine walk denotes the mirrors

A strong induction on `args.size - i`, proving both walks at each measure:
`whnfApp` at `k` calls `betaPeel` and itself at `k - 1`, and `betaPeel` at
`k` calls `whnfApp` at the SAME cursor (the peeled group ended at a non-λ)
and itself at `k - 1` — con-leche's lexicographic measure
`(args.length, 0/1)`, with the `whnfApp` half proved first at each `k`.

The spine's context — the argument vector, its denotation, and the spine's
own nodes — is fixed across the induction (`SpineCtx`); the `same` flag's
contract is that the current value IS the original spine's prefix, so the
node the spine already has is the application the reduction rebuilds. -/

/-- con-leche: none — the fixed data of one batched spine walk, at a store:
the argument vector denotes `xs` (each well-scoped) and node `j` denotes the
original head applied to the first `j + 1` arguments. -/
def SpineCtx (d : Nat) (args nodes : Array EIdx) (H0 : Expr) (xs : List Expr)
    (st : EStore) : Prop :=
  Frontend.denoteEList st args.toList = some xs ∧ (∀ x ∈ xs, Expr.WScoped d x) ∧
  nodes.size = args.size ∧
  ∀ j (hj : j < nodes.size),
    denoteE st nodes[j] = some (Expr.mkAppN H0 (xs.take (j + 1)))

theorem SpineCtx.ext {d : Nat} {args nodes : Array EIdx} {H0 : Expr}
    {xs : List Expr} {st st' : EStore} (h : SpineCtx d args nodes H0 xs st)
    (hx : Ext st st') : SpineCtx d args nodes H0 xs st' :=
  ⟨denoteEList_ext' hx h.1, h.2.1, h.2.2.1,
    fun j hj => denote_ext (h.2.2.2 j hj) hx⟩

/-- con-leche: ConLeche/Verify/BetaSpine.lean:84 whnfApp — the carry's
postcondition at `whnfApp`. -/
def WAPost (mode : CheckMode) (env : Env) (fe : IFEnv) (d : Nat) (s₀ : AState)
    (V : Expr) (rest : List Expr) (r : EIdx) (s' : AState) : Prop :=
  CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
  ∃ v', denoteE s'.store r = some v' ∧ Expr.WScoped d v' ∧
    ∃ F, mWA mode env F d V rest = .ok v'

/-- con-leche: ConLeche/Verify/BetaSpine.lean:113 betaPeel — the carry's
postcondition at `betaPeel`. -/
def BPPost (mode : CheckMode) (env : Env) (fe : IFEnv) (d : Nat) (s₀ : AState)
    (T : Expr) (ws rest : List Expr) (r : EIdx) (s' : AState) : Prop :=
  CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
  ∃ v', denoteE s'.store r = some v' ∧ Expr.WScoped d v' ∧
    ∃ F, mBP mode env F d T ws rest = .ok v'

/-- con-leche: ConLeche/Verify/BetaSpine.lean:84 whnfApp — the `whnfApp` half
of the carry at measure `k`. -/
def WACarry (mode : CheckMode) (env : Env) (fe : IFEnv) (fuel d : Nat)
    (args nodes : Array EIdx) (H0 : Expr) (xs : List Expr) (k : Nat) : Prop :=
  ∀ (v hd : EIdx) (vargs : Array EIdx) (same : Bool) (i : Nat) (s₀ : AState)
    (V : Expr), args.size - i = k → CheckOK mode env fe s₀ →
    SpineCtx d args nodes H0 xs s₀.store →
    denoteE s₀.store v = some V → Expr.WScoped d V →
    denoteE s₀.store hd = some V.getAppFn →
    Frontend.denoteEList s₀.store vargs.toList = some V.getAppArgs →
    (same = true → V = Expr.mkAppN H0 (xs.take i)) →
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.whnfApp mode (coreKnot mode fe id fuel) fe d v hd vargs same
        args nodes i
    ⦃⇓? r s' => ⌜WAPost mode env fe d s₀ V (xs.drop i) r s'⌝⦄

/-- con-leche: ConLeche/Verify/BetaSpine.lean:113 betaPeel — the `betaPeel`
half of the carry at measure `k`. -/
def BPCarry (mode : CheckMode) (env : Env) (fe : IFEnv) (fuel d : Nat)
    (args nodes : Array EIdx) (H0 : Expr) (xs : List Expr) (k : Nat) : Prop :=
  ∀ (t : EIdx) (acc : Array EIdx) (i : Nat) (s₀ : AState) (T : Expr)
    (ws : List Expr), args.size - i = k → CheckOK mode env fe s₀ →
    SpineCtx d args nodes H0 xs s₀.store →
    denoteE s₀.store t = some T → ExprOps.InstLVec s₀.store acc ws →
    Expr.WScoped d (T.instantiateList ws) →
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.betaPeel mode (coreKnot mode fe id fuel) fe d t acc args
        nodes i
    ⦃⇓? r s' => ⌜BPPost mode env fe d s₀ T ws (xs.drop i) r s'⌝⦄

/-- con-leche: none — the spine's node at the cursor denotes the prefix
applied to the cursor's argument, which is the application the reduction
rebuilds when the value is still the original prefix (`same`). -/
theorem SpineCtx.node {d : Nat} {args nodes : Array EIdx} {H0 : Expr}
    {xs : List Expr} {st : EStore} (h : SpineCtx d args nodes H0 xs st)
    {i : Nat} (hi : i < args.size) {A : Expr} {rest : List Expr}
    (hdrop : xs.drop i = A :: rest) :
    denoteE st nodes[i]! =
      some (.app (Expr.mkAppN H0 (xs.take i)) A) := by
  have hin : i < nodes.size := by rw [h.2.2.1]; exact hi
  rw [getElem!_pos nodes i hin, h.2.2.2 i hin, List.take_add_one]
  have hget : xs[i]? = some A := by
    rw [← List.head?_drop, hdrop]; rfl
  rw [hget]
  simp [Expr.mkAppN_append_one]

/-- con-leche: ConLeche/Verify/Shift.lean:115 WScoped — at an application. -/
theorem wscoped_app {d : Nat} {f a : Expr} (hf : Expr.WScoped d f)
    (ha : Expr.WScoped d a) : Expr.WScoped d (.app f a) := by
  simp only [Expr.WScoped]; exact ⟨hf, ha⟩

/-- con-leche: none — the `do` elaborator pushes a continuation into both
arms of an `if`; this folds it back out. -/
theorem ite_bind_fold {α β : Type} (c : Prop) [Decidable c] (x y : AM α)
    (f : α → AM β) :
    (if c then x >>= f else y >>= f) = (if c then x else y) >>= f := by
  split <;> rfl

/-- con-leche: none — the suffix after the cursor. -/
theorem drop_succ_of_drop {xs rest : List Expr} {i : Nat} {A : Expr}
    (hdrop : xs.drop i = A :: rest) : xs.drop (i + 1) = rest := by
  have := congrArg List.tail hdrop
  simpa [List.tail_drop] using this

/-- con-leche: none — the argument at the cursor, and the suffix, are
members of the spine's arguments. -/
theorem mem_of_drop {xs rest : List Expr} {i : Nat} {A : Expr}
    (hdrop : xs.drop i = A :: rest) : A ∈ xs ∧ ∀ x ∈ rest, x ∈ xs := by
  refine ⟨List.mem_of_mem_drop (i := i) (by rw [hdrop]; simp),
    fun x hx => List.mem_of_mem_drop (i := i) (by rw [hdrop]; simp [hx])⟩

/-- con-leche: ConLeche/Verify/BetaSpine.lean:84 whnfApp — the `whnfApp` step
of the carry: from both halves below `k`. -/
theorem whnfApp_carry_step {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hμ : mode.verifiedChecks = true) (hsim : KnotSpec mode env fe fuel)
    (d : Nat) (args nodes : Array EIdx) (H0 : Expr) (xs : List Expr) (k : Nat)
    (ihW : ∀ k' < k, WACarry mode env fe fuel d args nodes H0 xs k')
    (ihB : ∀ k' < k, BPCarry mode env fe fuel d args nodes H0 xs k') :
    WACarry mode env fe fuel d args nodes H0 xs k := by
  intro v hd vargs same i s₀ V hk hok hctx hdv hwV hdh hdva hsame
  have hwf := hok.state.wf
  rw [ConRon.Arena.whnfApp]
  by_cases hi : i < args.size
  · rw [dif_pos hi]
    obtain ⟨A, rest, hdrop, hdA, hrestD⟩ := denoteEList_drop_cons hi
      (ExprOps.denoteEList_drop i _ _ hctx.1)
    have hdrop' : xs.drop i = A :: rest := hdrop
    have hdrop1 := drop_succ_of_drop hdrop'
    obtain ⟨hAmem, hrestmem⟩ := mem_of_drop hdrop'
    have hwA : Expr.WScoped d A := hctx.2.1 A hAmem
    have hwrest : ∀ x ∈ rest, Expr.WScoped d x :=
      fun x hx => hctx.2.1 x (hrestmem x hx)
    by_cases htl : (v.tag == ETag.lam) = true
    · simp only [htl, if_true]
      obtain ⟨ty, body, mb, Ty, Body, hvb, rfl, hty, hbody⟩ :=
        viewBind_of_lam_tag hwf (by simpa using htl) hdv
      have hwTB : Expr.WScoped d Ty ∧ Expr.WScoped d Body := by
        simpa only [Expr.WScoped] using hwV
      refine triple_seq (viewBind_spec s₀ v) ?_
      rintro o s1 ⟨hs1, rfl⟩
      subst s1
      rw [hvb]
      dsimp only
      rw [betaSkip_eq_fires hμ]
      have hvec : ExprOps.InstLVec s₀.store #[args[i]] [A] := by
        unfold ExprOps.InstLVec
        simp [Frontend.denoteEList, hdA]
      have hwB1 : Expr.WScoped d (Body.instantiateList [A]) := by
        rw [ConLeche.instList_single]
        exact Expr.WScoped.instantiate1_gen hwA 0 hwTB.2
      by_cases hg : ConLeche.betaGateFires mode mb.pw = true
      · rw [if_pos hg]
        refine triple_mono (ihB (k - 1) (by omega) body #[args[i]] (i + 1) s₀
          Body [A] (by omega) hok hctx hbody hvec hwB1) ?_
        rintro r s' ⟨hck, hx, hp, v', hdv', hwv', F, hF⟩
        refine ⟨hck, hx, hp, v', hdv', hwv', F, ?_⟩
        rw [hdrop', mWA_lam_skip hg, ← hdrop1]
        exact hF
      · rw [if_neg hg]
        have hg' : ConLeche.betaGateFires mode mb.pw = false :=
          Bool.eq_false_iff.mpr hg
        refine triple_seq (hsim.inferIO s₀ d args[i] A hok hdA hwA) ?_
        rintro ta s2 ⟨hok2, hx2, hp2, TA, hdta, hwta, F1, hF1⟩
        refine triple_seq (hsim.defeq s2 d ta ty TA Ty hok2 hdta
          (denote_ext hty hx2) hwta hwTB.1) ?_
        rintro b s3 ⟨hok3, hx3, hp3, F2, hF2⟩
        have hx03 : Ext s₀.store s3.store := hx2.trans hx3
        cases b with
        | true =>
          simp only [if_true]
          refine triple_mono (ihB (k - 1) (by omega) body #[args[i]] (i + 1) s3
            Body [A] (by omega) hok3 (hctx.ext hx03) (denote_ext hbody hx03)
            (hvec.ext hx03) hwB1) ?_
          rintro r s' ⟨hck, hx, hp, v', hdv', hwv', F3, hF3⟩
          refine ⟨hck, hx03.trans hx, by rw [hp, hp3, hp2], v', hdv', hwv',
            F1 + F2 + F3, ?_⟩
          rw [hdrop', mWA_lam_cert hg'
            (ConLeche.inferTypeIO_mono (by omega) hF1)
            (ConLeche.isDefEqCore_mono (by omega) hF2), ← hdrop1]
          exact mBP_mono (by omega) hF3
        | false =>
          simp only [Bool.false_eq_true, if_false]
          refine triple_seq (internAppRebuilt_spec s3 nodes[i]! same v args[i]
            (.lam Ty Body mb) A hok3 (denote_ext hdv hx03)
            (denote_ext hdA hx03) (fun hs => by
              rw [(hctx.ext hx03).node hi hdrop', ← hsame hs])) ?_
          rintro fa s4 ⟨hok4, hx4, hp4, hdfa⟩
          have hx04 : Ext s₀.store s4.store := hx03.trans hx4
          have hrest4 : Frontend.denoteEList s4.store
              (args.toList.drop (i + 1)) = some rest :=
            denoteEList_ext' hx04 hrestD
          refine triple_mono (ExprOps.mkAppNFrom_spec _ s4 fa args (i + 1) rfl
            hok4.state (by rw [hdfa]; rfl) (by rw [hrest4]; rfl)) ?_
          rintro r s5 ⟨hst5, hx5, _, _, hc5, hp5, hrel⟩
          refine ⟨hok4.mono hst5 hx5 hc5 hp5, hx04.trans hx5,
            by rw [hp5, hp4, hp3, hp2], _, hrel _ _ hdfa hrest4,
            Expr.WScoped.mkAppN (wscoped_app hwV hwA) hwrest, F1 + F2, ?_⟩
          rw [hdrop']
          exact mWA_lam_fail hg' (ConLeche.inferTypeIO_mono (by omega) hF1)
            (ConLeche.isDefEqCore_mono (by omega) hF2)
    · simp only [htl, Bool.false_eq_true, if_false]
      have hnl : ∀ ty b mb, V ≠ .lam ty b mb := by
        obtain ⟨w, hw⟩ := denoteE_view hdv
        refine denote_not_lam hwf hw hdv ?_
        intro ty b m hwm; subst hwm
        exact htl (by rw [EStore.tagOf_of_view hw]; rfl)
      refine triple_seq (internAppRebuilt_spec s₀ nodes[i]! same v args[i]
        V A hok hdv hdA (fun hs => by
          rw [hctx.node hi hdrop', ← hsame hs])) ?_
      rintro ap s1 ⟨hok1, hx1, hp1, hdap⟩
      rw [ite_bind_fold]
      refine triple_seq (whnfApp_iotaStep_spec henv hμ hsim s1 d hd args[i]
        vargs V A hok1 (denote_ext hdh hx1) (denoteEList_ext' hx1 hdva)
        (denote_ext hdA hx1) (wscoped_app hwV hwA)) ?_
      rintro step s2 ⟨hok2, hx2, hp2, ov, hov, hwov, F1, hF1⟩
      have hx02 : Ext s₀.store s2.store := hx1.trans hx2
      have hdh' : denoteE s2.store hd = some (Expr.app V A).getAppFn := by
        simpa [Expr.getAppFn] using denote_ext hdh hx02
      have hdva' : Frontend.denoteEList s2.store (vargs.push args[i]).toList =
          some (Expr.app V A).getAppArgs := by
        simp only [Array.toList_push, Expr.getAppArgs]
        exact ExprOps.denoteEList_snoc (denote_ext hdA hx02) _ _
          (denoteEList_ext' hx02 hdva)
      cases step with
      | none =>
        simp only [denoteEO, Option.some.injEq] at hov
        subst hov
        dsimp only
        have hsame2 : (ap == nodes[i]!) = true →
            Expr.app V A = Expr.mkAppN H0 (xs.take (i + 1)) := by
          intro hbeq
          have heq : ap = nodes[i]! := beq_iff_eq.mp hbeq
          have h1 := denote_ext hdap hx2
          rw [heq, (hctx.ext hx02).node hi hdrop'] at h1
          rw [List.take_add_one]
          have hget : xs[i]? = some A := by
            rw [← List.head?_drop, hdrop']; rfl
          rw [hget]
          simp only [Option.toList_some, Expr.mkAppN_append_one]
          exact (Option.some.inj h1).symm
        refine triple_mono (ihW (k - 1) (by omega) ap hd (vargs.push args[i])
          (ap == nodes[i]!) (i + 1) s2 (.app V A) (by omega) hok2
          (hctx.ext hx02) (denote_ext hdap hx2) (wscoped_app hwV hwA) hdh' hdva'
          hsame2) ?_
        rintro r s' ⟨hck, hx, hp, v', hdv', hwv', F2, hF2⟩
        refine ⟨hck, hx02.trans hx, by rw [hp, hp2, hp1], v', hdv', hwv',
          F1 + F2, ?_⟩
        rw [hdrop', mWA_iota_none hnl (ConLeche.iotaRec_mono (by omega) hF1),
          ← hdrop1]
        exact mWA_mono (by omega) hF2
      | some e2 =>
        simp only [denoteEO, Option.map_eq_some_iff] at hov
        obtain ⟨E2, hdE2, rfl⟩ := hov
        have hwE2 := hwov E2 rfl
        dsimp only
        refine triple_seq (hsim.whnfCore s2 d e2 E2 hok2 hdE2 hwE2) ?_
        rintro v2 s3 ⟨hok3, hx3, hp3, V2, hdv2, hwv2, F2, hF2⟩
        refine triple_seq (headAndArgs_spec s3 v2 V2 hok3.state hdv2) ?_
        rintro hv s4 ⟨hs4, hh1, hh2⟩
        subst s4
        have hx03 : Ext s₀.store s3.store := hx02.trans hx3
        refine triple_mono (ihW (k - 1) (by omega) v2 hv.1 hv.2 false (i + 1)
          s3 V2 (by omega) hok3 (hctx.ext hx03) hdv2 hwv2 hh1 hh2
          (by simp)) ?_
        rintro r s' ⟨hck, hx, hp, v', hdv', hwv', F3, hF3⟩
        refine ⟨hck, hx03.trans hx, by rw [hp, hp3, hp2, hp1], v', hdv', hwv',
          F1 + F2 + F3, ?_⟩
        rw [hdrop', mWA_iota_some hnl (ConLeche.iotaRec_mono (by omega) hF1)
          (ConLeche.whnfCore_mono (by omega) hF2), ← hdrop1]
        exact mWA_mono (by omega) hF3
  · rw [dif_neg hi]
    mvcgen
    subst_vars
    have hlen := ExprOps.denoteEList_length _ _ hctx.1
    simp only [Array.length_toList] at hlen
    have hnil : xs.drop i = [] := List.drop_eq_nil_of_le (by omega)
    exact ⟨hok, Ext.refl _, rfl, V, hdv, hwV, 0, by rw [hnil]; exact mWA_nil⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:371-373 instantiateListFast —
`instantiateListFast_spec` at the tier's invariant: `CheckOK` survives and the
answer denotes the pure substitution. -/
theorem instantiateListFast_ok_spec (s₀ : AState) (e : EIdx) (acc : Array EIdx)
    (E : Expr) (ws : List Expr) (hok : CheckOK mode env fe s₀)
    (hde : denoteE s₀.store e = some E) (hvec : ExprOps.InstLVec s₀.store acc ws) :
    ⦃fun s => ⌜s = s₀⌝⦄ instantiateListFast coreWalkFuel e acc 0
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ denoteE s'.store r = some (E.instantiateList ws)⌝⦄ :=
  triple_mono (ExprOps.instantiateListFast_spec coreWalkFuel s₀ e acc 0 ws
      hok.state hvec (by rw [hde]; rfl))
    (fun _ _ ⟨hst, hx, _, hc, hp, _, hrel⟩ =>
      ⟨hok.mono hst hx hc hp, hx, hp, hrel E hde⟩)

/-- con-leche: ConLeche/Verify/BetaSpine.lean:113 betaPeel — the `betaPeel`
step of the carry: from the `whnfApp` half at the SAME measure and the
`betaPeel` half below it. -/
theorem betaPeel_carry_step {fuel : Nat} (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel)
    (d : Nat) (args nodes : Array EIdx) (H0 : Expr) (xs : List Expr) (k : Nat)
    (hW : WACarry mode env fe fuel d args nodes H0 xs k)
    (ihB : ∀ k' < k, BPCarry mode env fe fuel d args nodes H0 xs k') :
    BPCarry mode env fe fuel d args nodes H0 xs k := by
  intro t acc i s₀ T ws hk hok hctx hdt hacc hwT
  have hwf := hok.state.wf
  rw [ConRon.Arena.betaPeel]
  by_cases hi : i < args.size
  · rw [dif_pos hi]
    obtain ⟨A, rest, hdrop, hdA, hrestD⟩ := denoteEList_drop_cons hi
      (ExprOps.denoteEList_drop i _ _ hctx.1)
    have hdrop' : xs.drop i = A :: rest := hdrop
    have hdrop1 := drop_succ_of_drop hdrop'
    obtain ⟨hAmem, hrestmem⟩ := mem_of_drop hdrop'
    have hwA : Expr.WScoped d A := hctx.2.1 A hAmem
    have hwrest : ∀ x ∈ rest, Expr.WScoped d x :=
      fun x hx => hctx.2.1 x (hrestmem x hx)
    by_cases htl : (t.tag == ETag.lam) = true
    · simp only [htl, if_true]
      obtain ⟨ty, body, mb, Ty, Body, hvb, rfl, hty, hbody⟩ :=
        viewBind_of_lam_tag hwf (by simpa using htl) hdt
      have hwTB : Expr.WScoped d (Ty.instantiateList ws) ∧
          Expr.WScoped d (Body.instantiateList ws 1) := by
        rw [ConLeche.instList_lam] at hwT
        simpa only [Expr.WScoped] using hwT
      have hwB1 : Expr.WScoped d (Body.instantiateList (A :: ws)) := by
        rw [ConLeche.instList_cons0]
        exact Expr.WScoped.instantiate1_gen hwA 0 hwTB.2
      refine triple_seq (viewBind_spec s₀ t) ?_
      rintro o s1 ⟨hs1, rfl⟩
      subst s1
      rw [hvb]
      dsimp only
      rw [betaSkip_eq_fires hμ]
      by_cases hg : ConLeche.betaGateFires mode mb.pw = true
      · rw [if_pos hg]
        refine triple_mono (ihB (k - 1) (by omega) body (acc.push args[i])
          (i + 1) s₀ Body (A :: ws) (by omega) hok hctx hbody
          (InstLVec.push hacc hdA) hwB1) ?_
        rintro r s' ⟨hck, hx, hp, v', hdv', hwv', F, hF⟩
        refine ⟨hck, hx, hp, v', hdv', hwv', F, ?_⟩
        rw [hdrop', mBP_lam_skip hg, ← hdrop1]
        exact hF
      · rw [if_neg hg]
        have hg' : ConLeche.betaGateFires mode mb.pw = false :=
          Bool.eq_false_iff.mpr hg
        refine triple_seq (instantiateListFast_ok_spec s₀ ty acc Ty ws hok hty
          hacc) ?_
        rintro ty2 s2 ⟨hok2, hx2, hp2, hdty2⟩
        refine triple_seq (hsim.inferIO s2 d args[i] A hok2
          (denote_ext hdA hx2) hwA) ?_
        rintro ta s3 ⟨hok3, hx3, hp3, TA, hdta, hwta, F1, hF1⟩
        refine triple_seq (hsim.defeq s3 d ta ty2 TA (Ty.instantiateList ws)
          hok3 hdta (denote_ext hdty2 hx3) hwta hwTB.1) ?_
        rintro b s4 ⟨hok4, hx4, hp4, F2, hF2⟩
        have hx04 : Ext s₀.store s4.store := (hx2.trans hx3).trans hx4
        cases b with
        | true =>
          simp only [if_true]
          refine triple_mono (ihB (k - 1) (by omega) body (acc.push args[i])
            (i + 1) s4 Body (A :: ws) (by omega) hok4 (hctx.ext hx04)
            (denote_ext hbody hx04) ((InstLVec.push hacc hdA).ext hx04)
            hwB1) ?_
          rintro r s' ⟨hck, hx, hp, v', hdv', hwv', F3, hF3⟩
          refine ⟨hck, hx04.trans hx, by rw [hp, hp4, hp3, hp2], v', hdv', hwv',
            F1 + F2 + F3, ?_⟩
          rw [hdrop', mBP_lam_cert hg'
            (ConLeche.inferTypeIO_mono (by omega) hF1)
            (ConLeche.isDefEqCore_mono (by omega) hF2), ← hdrop1]
          exact mBP_mono (by omega) hF3
        | false =>
          simp only [Bool.false_eq_true, if_false]
          refine triple_seq (instantiateListFast_ok_spec s4 t acc
            (.lam Ty Body mb) ws hok4 (denote_ext hdt hx04)
            (hacc.ext hx04)) ?_
          rintro f2 s5 ⟨hok5, hx5, hp5, hdf2⟩
          have hx05 : Ext s₀.store s5.store := hx04.trans hx5
          refine triple_seq (internE_ok_spec s5 (.app f2 args[i]) hok5
            (viewOK_app (by rw [hdf2]; rfl)
              (by rw [denote_ext hdA hx05]; rfl))) ?_
          rintro fa s6 ⟨hok6, hx6, hp6, hdfa⟩
          have hx06 : Ext s₀.store s6.store := hx05.trans hx6
          have hdfa' : denoteE s6.store fa = some (.app
              ((Expr.lam Ty Body mb).instantiateList ws) A) := by
            rw [hdfa]
            simp [denoteEView, denote_ext hdf2 hx6, denote_ext hdA hx06]
          have hrest6 : Frontend.denoteEList s6.store
              (args.toList.drop (i + 1)) = some rest :=
            denoteEList_ext' hx06 hrestD
          refine triple_mono (ExprOps.mkAppNFrom_spec _ s6 fa args (i + 1) rfl
            hok6.state (by rw [hdfa']; rfl) (by rw [hrest6]; rfl)) ?_
          rintro r s7 ⟨hst7, hx7, _, _, hc7, hp7, hrel⟩
          refine ⟨hok6.mono hst7 hx7 hc7 hp7, hx06.trans hx7,
            by rw [hp7, hp6, hp5, hp4, hp3, hp2], _, hrel _ _ hdfa' hrest6,
            Expr.WScoped.mkAppN (wscoped_app hwT hwA) hwrest, F1 + F2, ?_⟩
          rw [hdrop']
          exact mBP_lam_fail hg' (ConLeche.inferTypeIO_mono (by omega) hF1)
            (ConLeche.isDefEqCore_mono (by omega) hF2)
    · simp only [htl, Bool.false_eq_true, if_false]
      have hnl : ∀ ty b mb, T ≠ .lam ty b mb := by
        obtain ⟨w, hw⟩ := denoteE_view hdt
        refine denote_not_lam hwf hw hdt ?_
        intro ty b m hwm; subst hwm
        exact htl (by rw [EStore.tagOf_of_view hw]; rfl)
      refine triple_seq (instantiateListFast_ok_spec s₀ t acc T ws hok hdt
        hacc) ?_
      rintro e2 s1 ⟨hok1, hx1, hp1, hde2⟩
      refine triple_seq (hsim.whnfCore s1 d e2 _ hok1 hde2 hwT) ?_
      rintro v2 s2 ⟨hok2, hx2, hp2, V2, hdv2, hwv2, F1, hF1⟩
      refine triple_seq (headAndArgs_spec s2 v2 V2 hok2.state hdv2) ?_
      rintro hv s3 ⟨hs3, hh1, hh2⟩
      subst s3
      have hx02 : Ext s₀.store s2.store := hx1.trans hx2
      refine triple_mono (hW v2 hv.1 hv.2 false i s2 V2 hk hok2 (hctx.ext hx02)
        hdv2 hwv2 hh1 hh2 (by simp)) ?_
      rintro r s' ⟨hck, hx, hp, v', hdv', hwv', F2, hF2⟩
      refine ⟨hck, hx02.trans hx, by rw [hp, hp2, hp1], v', hdv', hwv',
        F1 + F2, ?_⟩
      rw [hdrop', mBP_nonlam hnl (ConLeche.whnfCore_mono (by omega) hF1),
        ← hdrop']
      exact mWA_mono (by omega) hF2
  · rw [dif_neg hi]
    have hlen := ExprOps.denoteEList_length _ _ hctx.1
    simp only [Array.length_toList] at hlen
    have hnil : xs.drop i = [] := List.drop_eq_nil_of_le (by omega)
    refine triple_seq (instantiateListFast_ok_spec s₀ t acc T ws hok hdt
      hacc) ?_
    rintro e2 s1 ⟨hok1, hx1, hp1, hde2⟩
    refine triple_mono (hsim.whnfCore s1 d e2 _ hok1 hde2 hwT) ?_
    rintro r s' ⟨hck, hx, hp, v', hdv', hwv', F, hF⟩
    refine ⟨hck, hx1.trans hx, by rw [hp, hp1], v', hdv', hwv', F, ?_⟩
    rw [hnil, mBP_nil]
    exact hF

/-- con-leche: ConLeche/Verify/BetaSpine.lean:84-150 whnfApp/betaPeel — **the
carry, both halves at every measure**. -/
theorem spine_carry {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hμ : mode.verifiedChecks = true) (hsim : KnotSpec mode env fe fuel)
    (d : Nat) (args nodes : Array EIdx) (H0 : Expr) (xs : List Expr) :
    ∀ k, WACarry mode env fe fuel d args nodes H0 xs k ∧
      BPCarry mode env fe fuel d args nodes H0 xs k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  have hW := whnfApp_carry_step henv hμ hsim d args nodes H0 xs k
    (fun k' hk' => (ih k' hk').1) (fun k' hk' => (ih k' hk').2)
  exact ⟨hW, betaPeel_carry_step hμ hsim d args nodes H0 xs k hW
    (fun k' hk' => (ih k' hk').2)⟩

section Census

#print axioms viewBind_of_lam_tag
#print axioms getAppSpine_spec
#print axioms headAndArgs_spec
#print axioms internAppRebuilt_spec
#print axioms mWA_mono
#print axioms mBP_mono
#print axioms mWA_lam_cert
#print axioms mWA_iota_some
#print axioms mBP_lam_fail
#print axioms mBP_nonlam
#print axioms betaSkip_eq_fires
#print axioms instantiateListFast_ok_spec
/-! `sorryAx` was expected on exactly `iotaRecAt_spec` (§2) and on what
reaches it while §2 was open; it is closed since, and these print the three
standard axioms. -/
#print axioms iotaRecAt_spec
#print axioms whnfApp_iotaStep_spec
#print axioms whnfApp_carry_step
#print axioms betaPeel_carry_step
#print axioms spine_carry

end Census

end ConRon.Bridge.Core

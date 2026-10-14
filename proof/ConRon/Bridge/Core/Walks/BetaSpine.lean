/-
# `ConRon.Bridge.Core.Walks.BetaSpine` — the batched β spine's carry

The twin's `whnfCoreBody` `.app`
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
holds; its rule `iotaRecAt_spec` (`Walks/Iota.lean`, see §2) is the
`iotaRec` tower's own entry point, which `iotaRec_spec` (`Walks/Owed.lean`)
is `getAppFn`/`getAppArgs` over.
-/
import ConRon.Bridge.Core.Walks.PropRead
import ConRon.Bridge.Core.Walks.StrCtor
import ConLeche.Verify.BetaSpine
import ConRon.Bridge.Core.Walks.Iota

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv} {c : Bool}

/-! ## 1. The read-only spine walks -/

/-- con-leche: none — a handle whose tag is `lam` and which denotes, is a
`viewBind` of the λ it denotes. -/
theorem viewBind_of_lam_tag {st : EStore} (hwf : StoreWF st) {v : EIdx}
    {V : Expr} (htg : v.tag = ETag.lam) (hd : denoteE st v = some V) :
    ∃ ty body Ty Body, st.viewBind v = some (ty, body) ∧
      V = .lam Ty Body ∧ denoteE st ty = some Ty ∧
      denoteE st body = some Body := by
  obtain ⟨w, hw⟩ := denoteE_view hd
  have htw := EStore.tagOf_of_view hw
  cases w with
  | lam ty b =>
    obtain ⟨et, eb, rfl, h1, h2⟩ := denote_lam_inv hwf hw hd
    refine ⟨ty, b, et, eb, ?_, rfl, h1, h2⟩
    exact viewBind_of_view_lam hw
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
    ⦃fun s => s = s₀⦄ getAppSpineGo fuel h
    ⦃fun r s' => s' = s₀ ∧ SpineOK s₀.store E r; ⊤⦄
  | 0, s₀, h, E, _, _ => by
    rw [getAppSpineGo]; exact triple_fail
  | fuel + 1, s₀, h, E, hok, hd => by
    rw [getAppSpineGo]
    by_cases htg : (h.tag == ETag.app) = true
    · rw [ite_eq_left htg]
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
        vcgen
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
    · rw [ite_eq_right htg]
      vcgen
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
    ⦃fun s => s = s₀⦄ getAppSpine fuel h
    ⦃fun r s' => s' = s₀ ∧ SpineOK s₀.store E r; ⊤⦄ :=
  getAppSpineGo_spec fuel s₀ h E hok hd

/-- con-leche: ConLeche/Kernel/ExprOps.lean:915-923 getAppFn/getAppArgs —
**THEOREM 1 for `headAndArgs`**: read-only; the head and the argument vector
of a reduct. -/
theorem headAndArgs_spec (s₀ : AState) (v : EIdx) (V : Expr)
    (hok : StateOK s₀) (hd : denoteE s₀.store v = some V) :
    ⦃fun s => s = s₀⦄ headAndArgs v
    ⦃fun r s' => s' = s₀ ∧ denoteE s₀.store r.1 = some V.getAppFn ∧
        Frontend.denoteEList s₀.store r.2.toList = some V.getAppArgs; ⊤⦄ := by
  unfold headAndArgs
  by_cases htg : (v.tag == ETag.app) = true
  · rw [ite_eq_left htg]
    refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ v hok
      (by rw [hd]; rfl)) ?_
    rintro hh s1 ⟨hs1, hr1⟩
    subst s1
    refine triple_seq (ExprOps.getAppArgs_spec coreWalkFuel s₀ v hok
      (by rw [hd]; rfl)) ?_
    rintro va s2 ⟨hs2, hr2⟩
    subst s2
    vcgen
    subst_vars
    exact ⟨rfl, hr1 V hd, by simpa using hr2 V hd⟩
  · rw [ite_eq_right htg]
    vcgen
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
    ⦃fun s => s = s₀⦄ internAppRebuilt node same f a
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ denoteE s'.store r = some (.app F A); ⊤⦄ := by
  unfold internAppRebuilt
  cases same with
  | true =>
    vcgen +internalize
    subst_vars
    exact ⟨hok, Ext.refl _, rfl, by simpa using hsame⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    refine triple_mono (internE_ok_spec s₀ (.app f a) hok
      (viewOK_app (by rw [hf]; rfl) (by rw [ha]; rfl))) ?_
    rintro r s' ⟨hck, hx, hp, hr⟩
    refine ⟨hck, hx, hp, ?_⟩
    rw [hr]
    simp [denoteEView, denote_ext hf hx, denote_ext ha hx]

/-! ## 2. The iota step at a held spine

`whnfApp` asks for one ι step at every non-λ reduction step of the spine it
is walking, through `iotaRecAt` at the head and the argument vector it
already holds (DESIGN `### Task #97-P6-9`'s hoist).  `iotaRec` is `getAppFn`/`getAppArgs`
over the same entry, so `iotaRecAt_spec` below is the `iotaRec` tower's own
entry rule; `iotaRec_spec` (`Walks/Owed.lean`) cannot stand in for it,
because its two spine reads are fuelled walks whose success at the spine
`whnfApp` holds is not provable (a partial-correctness triple claims nothing when they
throw). -/

/-! `iotaRecAt_spec` is `Walks/Iota.lean`'s: the held head is not an application
(`hnapp`, a spine head) and the count is the whole vector (`hn`), both
discharged at the call below. -/


/-- con-leche: ConLeche/Model/Inductives/TargetCallWalk.lean:198
getAppFn_ne_app — a spine head is never an application (a local copy: the
cited module sits deep in the model tier). -/
theorem getAppFn_not_app : ∀ (e f a : Expr), e.getAppFn ≠ .app f a := by
  intro e
  induction e with
  | app g b ihg ihb => intro f a; exact ihg f a
  | _ => intro f a h; exact nomatch h

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
    ⦃fun s => s = s₀⦄
      (if hd.tag == ETag.const then
        ConRon.Arena.iotaRecAt mode (coreKnot mode fe id fuel) fe d hd
          (vargs.push a) (vargs.push a).size
      else pure none : AM (Option EIdx))
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimOOp (fun F => ConLeche.iotaRecFueled mode env F d (.app V A)) d
          s'.store r; ⊤⦄ := by
  have happ : Expr.mkAppN V.getAppFn (V.getAppArgs ++ [A]) = .app V A := by
    rw [Expr.mkAppN_append_one, Expr.mkAppN_getApp]
  by_cases htc : (hd.tag == ETag.const) = true
  · rw [ite_eq_left htc]
    have hdx : Frontend.denoteEList s₀.store (vargs.push a).toList =
        some (V.getAppArgs ++ [A]) := by
      simp only [Array.toList_push]
      exact ExprOps.denoteEList_snoc hda _ _ hdv
    have h := iotaRecAt_spec hμ henv hsim s₀ d hd (vargs.push a) (vargs.push a).size
      V.getAppFn (V.getAppArgs ++ [A]) hok hdh
      (fun f a => getAppFn_not_app V f a) rfl hdx (by rw [happ]; exact hw)
    rw [happ] at h
    exact h
  · rw [ite_eq_right htc]
    vcgen
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
    exact iotaRecFueled_nohead hnc

/-! ## 3. The pure mirrors at the pure knot

con-leche's step-returning `whnfAppW`/`betaPeelW` (`Verify/BetaSpine.lean`)
at `pureFns mode env F`: the batched walks (con-leche's task #342 R2)
RETURN their continuation (`WhnfStep.cont`), so the carry targets the `W`
mirrors and the loop (`Arms/WhnfCore.lean`) runs `whnfCoreLoopM` over them.
One equation per clause, and the fuel monotonicity through the mirrors'
`_atF` equations and the `FueledM` bundle. -/

/-- con-leche: ConLeche/Verify/BetaSpine.lean:202 whnfAppW — at the pure
knot. -/
abbrev mWA (mode : CheckMode) (env : Env) (F d : Nat) (V : Expr)
    (xs : List Expr) : CheckM ConLeche.WhnfStep :=
  ConLeche.whnfAppW mode (ConLeche.pureFns mode env F) env d V xs

/-- con-leche: ConLeche/Verify/BetaSpine.lean:220 betaPeelW — at the pure
knot. -/
abbrev mBP (mode : CheckMode) (env : Env) (F d : Nat) (t : Expr)
    (acc xs : List Expr) : CheckM ConLeche.WhnfStep :=
  ConLeche.betaPeelW mode (ConLeche.pureFns mode env F) env d t acc xs

/-- con-leche: ConLeche/Verify/BetaSpine.lean:411 whnfAppW_atF — fuel
monotonicity. -/
theorem mWA_mono {F F' d : Nat} {V : Expr} {xs : List Expr}
    {r : ConLeche.WhnfStep} (hle : F ≤ F') (h : mWA mode env F d V xs = .ok r) :
    mWA mode env F' d V xs = .ok r := by
  simp only [mWA] at h ⊢
  rw [← ConLeche.whnfAppW_atF] at h ⊢
  exact (ConLeche.whnfAppW mode (ConLeche.fueledFns mode env) env d V xs).property hle h

/-- con-leche: ConLeche/Verify/BetaSpine.lean:236 whnfAppW_nil. -/
theorem mWA_nil {F d : Nat} {V : Expr} : mWA mode env F d V [] = .ok (.done V) := by
  simp only [mWA, ConLeche.whnfAppW_nil]; rfl

/-- con-leche: ConLeche/Verify/BetaSpine.lean:240 whnfAppW_lam — uniform β
(con-leche's task #342 S0: no certificate). -/
theorem mWA_lam {F d : Nat} {ty b a : Expr} {rest : List Expr} :
    mWA mode env F d (.lam ty b) (a :: rest) = mBP mode env F d b [a] rest := by
  simp only [mWA, mBP, ConLeche.whnfAppW_lam]

/-- con-leche: ConLeche/Verify/BetaSpine.lean:246 whnfAppW_ne_lam — ι fires. -/
theorem mWA_iota_some {F d : Nat} {V a e2 : Expr} {rest : List Expr}
    (hV : ∀ ty b, V ≠ .lam ty b)
    (hi : ConLeche.iotaRecFueled mode env F d (.app V a) = .ok (some e2)) :
    mWA mode env F d V (a :: rest) = .ok (.cont (Expr.mkAppN e2 rest)) := by
  simp only [mWA, ConLeche.whnfAppW_ne_lam _ _ _ hV]
  simp only [ConLeche.iotaRecFueled] at hi
  simp only [hi, bind, Except.bind]; rfl

/-- con-leche: ConLeche/Verify/BetaSpine.lean:246 whnfAppW_ne_lam — ι does
not fire: one more stuck application. -/
theorem mWA_iota_none {F d : Nat} {V a : Expr} {rest : List Expr}
    (hV : ∀ ty b, V ≠ .lam ty b)
    (hi : ConLeche.iotaRecFueled mode env F d (.app V a) = .ok none) :
    mWA mode env F d V (a :: rest) = mWA mode env F d (.app V a) rest := by
  simp only [mWA, ConLeche.whnfAppW_ne_lam _ _ _ hV]
  simp only [ConLeche.iotaRecFueled] at hi
  simp only [hi, bind, Except.bind]

/-- con-leche: ConLeche/Verify/BetaSpine.lean:258 betaPeelW_nil. -/
theorem mBP_nil {F d : Nat} {t : Expr} {acc : List Expr} :
    mBP mode env F d t acc [] = .ok (.cont (t.instantiateList acc)) := by
  simp only [mBP, ConLeche.betaPeelW_nil]; rfl

/-- con-leche: ConLeche/Verify/BetaSpine.lean:263 betaPeelW_lam. -/
theorem mBP_lam {F d : Nat} {ty b a : Expr} {acc rest : List Expr} :
    mBP mode env F d (.lam ty b) acc (a :: rest) = mBP mode env F d b (a :: acc) rest := by
  simp only [mBP, ConLeche.betaPeelW_lam]

/-- con-leche: ConLeche/Verify/BetaSpine.lean:269 betaPeelW_ne_lam. -/
theorem mBP_nonlam {F d : Nat} {t a : Expr} {acc rest : List Expr}
    (ht : ∀ ty b, t ≠ .lam ty b) :
    mBP mode env F d t acc (a :: rest) =
      .ok (.cont (Expr.mkAppN (t.instantiateList acc) (a :: rest))) := by
  simp only [mBP, ConLeche.betaPeelW_ne_lam _ _ _ ht]; rfl

/-! ## 4. The carry: the twin's spine walk denotes the mirrors

The twin's `betaPeel` does not call `whnfApp` (a finished peel RETURNS its
reduct), so the carry is two plain inductions on `args.size - i`: `betaPeel`
first, then `whnfApp`, which calls `betaPeel` at a λ head.  The answer is a
`WhnfStep` over handles, read back by `denoteStep`. -/

/-- con-leche: ConLeche/Verify/BetaSpine.lean:197 WhnfStep — the readback of
a twin step outcome. -/
def denoteStep (st : EStore) : ConRon.Arena.WhnfStep → Option ConLeche.WhnfStep
  | .done h => (denoteE st h).map .done
  | .cont h => (denoteE st h).map .cont

/-- con-leche: none — a step outcome whose term is well scoped at `d`. -/
def StepWS (d : Nat) : ConLeche.WhnfStep → Prop
  | .done e => Expr.WScoped d e
  | .cont e => Expr.WScoped d e

/-- con-leche: ConLeche/Verify/BetaSpine.lean:202 whnfAppW — the carry's
postcondition at a step-returning walk whose pure side is `P`. -/
def StepPost (mode : CheckMode) (env : Env) (fe : IFEnv) (d : Nat) (s₀ : AState)
    (P : Nat → CheckM ConLeche.WhnfStep) (r : ConRon.Arena.WhnfStep) (s' : AState) :
    Prop :=
  CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
  ∃ R, denoteStep s'.store r = some R ∧ StepWS d R ∧ ∃ F, P F = .ok R

/-- con-leche: none — the argument vector of one batched spine walk, at a
store: it denotes `xs`, each well scoped. -/
def ArgsCtx (d : Nat) (args : Array EIdx) (xs : List Expr) (st : EStore) : Prop :=
  Frontend.denoteEList st args.toList = some xs ∧ ∀ x ∈ xs, Expr.WScoped d x

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

/-- con-leche: ConLeche/Kernel/ExprOps.lean:371-373 instantiateListFast —
`instantiateListFast_spec` at the tier's invariant: `CheckOK` survives and the
answer denotes the pure substitution. -/
theorem instantiateListFast_ok_spec (s₀ : AState) (e : EIdx) (acc : Array EIdx)
    (E : Expr) (ws : List Expr) (hok : CheckOK mode env fe s₀)
    (hde : denoteE s₀.store e = some E) (hvec : ExprOps.InstLVec s₀.store acc ws) :
    ⦃fun s => s = s₀⦄ instantiateListFast coreWalkFuel e acc 0
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ denoteE s'.store r = some (E.instantiateList ws); ⊤⦄ :=
  triple_mono (ExprOps.instantiateListFast_spec coreWalkFuel s₀ e acc 0 ws
      hok.state hvec (by rw [hde]; rfl))
    (fun _ _ ⟨hst, hx, hc, hp, _, hrel⟩ =>
      ⟨hok.mono hst hx hc hp, hx, hp, hrel E hde⟩)

/-- con-leche: ConLeche/Verify/BetaSpine.lean:220 betaPeelW — **the
`betaPeel` carry**, by induction on `args.size - i`. -/
theorem betaPeel_carry (d : Nat) (args : Array EIdx) (xs : List Expr) :
    ∀ (k : Nat) (t : EIdx) (acc : Array EIdx) (i : Nat) (s₀ : AState) (T : Expr)
      (ws : List Expr), args.size - i = k → CheckOK mode env fe s₀ →
      ArgsCtx d args xs s₀.store →
      denoteE s₀.store t = some T → ExprOps.InstLVec s₀.store acc ws →
      Expr.WScoped d (T.instantiateList ws) →
      ⦃fun s => s = s₀⦄ ConRon.Arena.betaPeel t acc args i
      ⦃fun r s' => StepPost mode env fe d s₀
          (fun F => mBP mode env F d T ws (xs.drop i)) r s'; ⊤⦄ := by
  intro k
  induction k with
  | zero =>
    intro t acc i s₀ T ws hk hok hctx hdt hacc hwT
    have hlen := ExprOps.denoteEList_length _ _ hctx.1
    simp only [Array.length_toList] at hlen
    have hnil : xs.drop i = [] := List.drop_eq_nil_of_le (by omega)
    rw [ConRon.Arena.betaPeel, dite_eq_right (by omega)]
    refine triple_seq (instantiateListFast_ok_spec s₀ t acc T ws hok hdt hacc) ?_
    rintro e2 s1 ⟨hok1, hx1, hp1, hde2⟩
    vcgen
    subst_vars
    refine ⟨hok1, hx1, hp1, .cont (T.instantiateList ws),
      by simp [denoteStep, hde2], hwT, 0, ?_⟩
    rw [hnil]; exact mBP_nil
  | succ k ih =>
    intro t acc i s₀ T ws hk hok hctx hdt hacc hwT
    have hwf := hok.state.wf
    have hi : i < args.size := by omega
    rw [ConRon.Arena.betaPeel, dite_eq_left hi]
    obtain ⟨A, rest, hdrop, hdA, hrestD⟩ := denoteEList_drop_cons hi
      (ExprOps.denoteEList_drop i _ _ hctx.1)
    have hdrop' : xs.drop i = A :: rest := hdrop
    have hdrop1 := drop_succ_of_drop hdrop'
    obtain ⟨hAmem, hrestmem⟩ := mem_of_drop hdrop'
    have hwA : Expr.WScoped d A := hctx.2 A hAmem
    have hwrest : ∀ x ∈ rest, Expr.WScoped d x :=
      fun x hx => hctx.2 x (hrestmem x hx)
    by_cases htl : (t.tag == ETag.lam) = true
    · simp only [htl, ite_true]
      obtain ⟨ty, body, Ty, Body, hvb, rfl, hty, hbody⟩ :=
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
      refine triple_mono (ih body (acc.push args[i]) (i + 1) s₀ Body (A :: ws)
        (by omega) hok hctx hbody (InstLVec.push hacc hdA) hwB1) ?_
      rintro r s' ⟨hck, hx, hp, R, hdR, hwR, F, hF⟩
      refine ⟨hck, hx, hp, R, hdR, hwR, F, ?_⟩
      dsimp only at hF ⊢
      rw [hdrop', mBP_lam, ← hdrop1]
      exact hF
    · simp only [htl, Bool.false_eq_true, ite_false]
      have hnl : ∀ ty b, T ≠ .lam ty b := by
        obtain ⟨w, hw⟩ := denoteE_view hdt
        refine denote_not_lam hwf hw hdt ?_
        intro ty b hwm; subst hwm
        exact htl (by rw [EStore.tagOf_of_view hw]; rfl)
      refine triple_seq (instantiateListFast_ok_spec s₀ t acc T ws hok hdt
        hacc) ?_
      rintro e2 s1 ⟨hok1, hx1, hp1, hde2⟩
      have hrest1 : Frontend.denoteEList s1.store (args.toList.drop i) =
          some (A :: rest) := denoteEList_ext' hx1 (by
            rw [← hdrop']; exact ExprOps.denoteEList_drop i _ _ hctx.1)
      refine triple_seq (ExprOps.mkAppNFrom_spec _ s1 e2 args i rfl
        hok1.state (by rw [hde2]; rfl) (by rw [hrest1]; rfl)) ?_
      rintro r s2 ⟨hst2, hx2, _, hc2, hp2, hrel⟩
      have hpost : StepPost mode env fe d s₀
          (fun F => mBP mode env F d T ws (xs.drop i)) (.cont r) s2 := by
        refine ⟨hok1.mono hst2 hx2 hc2 hp2, hx1.trans hx2, by rw [hp2, hp1],
          .cont (Expr.mkAppN (T.instantiateList ws) (A :: rest)),
          by simp [denoteStep, hrel _ _ hde2 hrest1],
          Expr.WScoped.mkAppN hwT (by
            intro x hx; rcases List.mem_cons.mp hx with rfl | hx
            · exact hwA
            · exact hwrest x hx), 0, ?_⟩
        dsimp only
        rw [hdrop']
        exact mBP_nonlam hnl
      vcgen
      subst_vars
      exact hpost

/-- con-leche: ConLeche/Verify/BetaSpine.lean:202 whnfAppW — **the `whnfApp`
carry**, by induction on `args.size - i`, over `betaPeel_carry` at a λ head
and the held-spine ι step (`whnfApp_iotaStep_spec`) at any other. -/
theorem whnfApp_carry {fuel : Nat} (henv : ConLeche.EnvWF env)
    (hμ : mode.verifiedChecks = true) (hsim : KnotSpec mode env fe fuel)
    (d : Nat) (args nodes : Array EIdx) (H0 : Expr) (xs : List Expr) :
    ∀ (k : Nat) (v hd : EIdx) (vargs : Array EIdx) (same : Bool) (i : Nat)
      (s₀ : AState) (V : Expr), args.size - i = k → CheckOK mode env fe s₀ →
      SpineCtx d args nodes H0 xs s₀.store →
      denoteE s₀.store v = some V → Expr.WScoped d V →
      denoteE s₀.store hd = some V.getAppFn →
      Frontend.denoteEList s₀.store vargs.toList = some V.getAppArgs →
      (same = true → V = Expr.mkAppN H0 (xs.take i)) →
      ⦃fun s => s = s₀⦄
        ConRon.Arena.whnfApp mode (coreKnot mode fe id fuel) fe d v hd vargs same
          args nodes i
      ⦃fun r s' => StepPost mode env fe d s₀
          (fun F => mWA mode env F d V (xs.drop i)) r s'; ⊤⦄ := by
  intro k
  induction k with
  | zero =>
    intro v hd vargs same i s₀ V hk hok hctx hdv hwV hdh hdva hsame
    have hlen := ExprOps.denoteEList_length _ _ hctx.1
    simp only [Array.length_toList] at hlen
    have hnil : xs.drop i = [] := List.drop_eq_nil_of_le (by omega)
    rw [ConRon.Arena.whnfApp, dite_eq_right (by omega)]
    vcgen
    subst_vars
    exact ⟨hok, Ext.refl _, rfl, .done V, by simp [denoteStep, hdv], hwV, 0,
      by rw [hnil]; exact mWA_nil⟩
  | succ k ih =>
    intro v hd vargs same i s₀ V hk hok hctx hdv hwV hdh hdva hsame
    have hwf := hok.state.wf
    have hi : i < args.size := by omega
    rw [ConRon.Arena.whnfApp, dite_eq_left hi]
    obtain ⟨A, rest, hdrop, hdA, hrestD⟩ := denoteEList_drop_cons hi
      (ExprOps.denoteEList_drop i _ _ hctx.1)
    have hdrop' : xs.drop i = A :: rest := hdrop
    have hdrop1 := drop_succ_of_drop hdrop'
    obtain ⟨hAmem, hrestmem⟩ := mem_of_drop hdrop'
    have hwA : Expr.WScoped d A := hctx.2.1 A hAmem
    have hwrest : ∀ x ∈ rest, Expr.WScoped d x :=
      fun x hx => hctx.2.1 x (hrestmem x hx)
    by_cases htl : (v.tag == ETag.lam) = true
    · simp only [htl, ite_true]
      obtain ⟨ty, body, Ty, Body, hvb, rfl, hty, hbody⟩ :=
        viewBind_of_lam_tag hwf (by simpa using htl) hdv
      have hwTB : Expr.WScoped d Ty ∧ Expr.WScoped d Body := by
        simpa only [Expr.WScoped] using hwV
      refine triple_seq (viewBind_spec s₀ v) ?_
      rintro o s1 ⟨hs1, rfl⟩
      subst s1
      rw [hvb]
      dsimp only
      have hvec : ExprOps.InstLVec s₀.store #[args[i]] [A] := by
        unfold ExprOps.InstLVec
        simp [Frontend.denoteEList, hdA]
      have hwB1 : Expr.WScoped d (Body.instantiateList [A]) := by
        rw [ConLeche.instList_single]
        exact Expr.WScoped.instantiate1_gen hwA 0 hwTB.2
      refine triple_mono (betaPeel_carry d args xs _ body #[args[i]] (i + 1) s₀
        Body [A] rfl hok ⟨hctx.1, hctx.2.1⟩ hbody hvec hwB1) ?_
      rintro r s' ⟨hck, hx, hp, R, hdR, hwR, F, hF⟩
      refine ⟨hck, hx, hp, R, hdR, hwR, F, ?_⟩
      dsimp only at hF ⊢
      rw [hdrop', mWA_lam, ← hdrop1]
      exact hF
    · simp only [htl, Bool.false_eq_true, ite_false]
      have hnl : ∀ ty b, V ≠ .lam ty b := by
        obtain ⟨w, hw⟩ := denoteE_view hdv
        refine denote_not_lam hwf hw hdv ?_
        intro ty b hwm; subst hwm
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
      cases step with
      | none =>
        simp only [denoteEO, Option.some.injEq] at hov
        subst hov
        dsimp only
        have hdh' : denoteE s2.store hd = some (Expr.app V A).getAppFn := by
          simpa [Expr.getAppFn] using denote_ext hdh hx02
        have hdva' : Frontend.denoteEList s2.store (vargs.push args[i]).toList =
            some (Expr.app V A).getAppArgs := by
          simp only [Array.toList_push, Expr.getAppArgs]
          exact ExprOps.denoteEList_snoc (denote_ext hdA hx02) _ _
            (denoteEList_ext' hx02 hdva)
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
        refine triple_mono (ih ap hd (vargs.push args[i]) (ap == nodes[i]!)
          (i + 1) s2 (.app V A) (by omega) hok2 (hctx.ext hx02)
          (denote_ext hdap hx2) (wscoped_app hwV hwA) hdh' hdva' hsame2) ?_
        rintro r s' ⟨hck, hx, hp, R, hdR, hwR, F2, hF2⟩
        refine ⟨hck, hx02.trans hx, by rw [hp, hp2, hp1], R, hdR, hwR,
          F1 + F2, ?_⟩
        dsimp only at hF2 ⊢
        rw [hdrop', mWA_iota_none hnl (ConLeche.iotaRec_mono (by omega) hF1),
          ← hdrop1]
        exact mWA_mono (by omega) hF2
      | some e2 =>
        simp only [denoteEO, Option.map_eq_some_iff] at hov
        obtain ⟨E2, hdE2, rfl⟩ := hov
        have hwE2 := hwov E2 rfl
        dsimp only
        have hrest2 : Frontend.denoteEList s2.store
            (args.toList.drop (i + 1)) = some rest :=
          denoteEList_ext' hx02 hrestD
        refine triple_seq (ExprOps.mkAppNFrom_spec _ s2 e2 args (i + 1) rfl
          hok2.state (by rw [hdE2]; rfl) (by rw [hrest2]; rfl)) ?_
        rintro r s3 ⟨hst3, hx3, _, hc3, hp3, hrel⟩
        have hpost : StepPost mode env fe d s₀
            (fun F => mWA mode env F d V (xs.drop i)) (.cont r) s3 := by
          refine ⟨hok2.mono hst3 hx3 hc3 hp3, hx02.trans hx3,
            by rw [hp3, hp2, hp1], .cont (Expr.mkAppN E2 rest),
            by simp [denoteStep, hrel _ _ hdE2 hrest2],
            Expr.WScoped.mkAppN hwE2 hwrest, F1, ?_⟩
          dsimp only
          rw [hdrop']
          exact mWA_iota_some hnl hF1
        vcgen
        subst_vars
        exact hpost

section Census

#print axioms viewBind_of_lam_tag
#print axioms getAppSpine_spec
#print axioms headAndArgs_spec
#print axioms internAppRebuilt_spec
#print axioms mWA_mono
#print axioms mWA_iota_some
#print axioms mBP_nonlam
#print axioms instantiateListFast_ok_spec
#print axioms whnfApp_iotaStep_spec
#print axioms betaPeel_carry
#print axioms whnfApp_carry

end Census

end ConRon.Bridge.Core

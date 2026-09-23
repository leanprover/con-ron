/-
# `ConRon.Bridge.Core.Walks.PropRead` — the head-symbol prop-ness readers

Task #97-P3-Core round 5, sub-lane PropRead.  `Arena/PropRead.lean` is nine
state-only readers (`peelNeverPis`, `numArgs`, `residualPW`, `headTypePW`,
`typeSortPW`, `headProofPW`, `proofPW`, `notProofFast`, `isProofFast`), and
round 4 (§5) priced it as `Walks/Nat.lean`'s row: no knot, no fuel on the
pure side, each an EQUATION with the con-leche function of the same name at
`find? := env.find?`.  This module is that, then the three walks of
`Walks/Owed.lean` that waited on it (`propIrrel`, `annotPwPi`,
`annotPwLam`).

## The shape

* **The three view-only readers** (`peelNeverPis`, `numArgs`, `residualPW`)
  leave the state alone: `s' = s₀`.
* **The four that read a constant's stored type** (`headTypePW`,
  `typeSortPW`, `headProofPW`, `proofPW`) and the two arms above them may
  run `readNamesM` / `readLevelsM`, which move the two readback memos — so
  their postcondition is `CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
  s'.pins = s₀.pins`, the frame `Walks/Frame.lean`'s `ReadbackFrame`
  delivers.  The store EQUATION is stronger than `Ext` and is what these
  readers actually satisfy (nothing is interned: `toConstantVal` is pure off
  a projection table, and the tower guard keeps the readers off that arm).
* **Every reader is stated in ANSWER shape** (∃ denotation in, ∀ out) as
  well as in published shape: each one is reached, inside this file or from
  a caller, through another call's answer (`getAppFn`'s head, `peelNeverPis`'s
  residual, `toConstantVal`'s stored type, the knot's `annotate` /
  `whnfCore` answers).  The published forms are four lines over the primed
  ones.  None carries well-scopedness: the readers look at head shape only.

## The index lookup

`fe.find? I` against `env.find? nm` is `Walks/Nat.lean`'s `OptCI` /
`optCI_find`; a hit's `isTowerEntry` is the denotation's
(`denoteCI_isTowerEntry`), and off the tower the arena's monadic
`toConstantVal` is pure and denotes con-leche's (`toConstantVal_nt_spec`).
The has-parameters cutoff (task #97-P6-10) is con-leche's own
`Level.substPW_eq_self`.
-/
import ConRon.Bridge.Core.Walks.Nat

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. Facts the readers need and no tier had -/

/-- con-leche: none — the denotation keeps a constant's tower-ness. -/
theorem denoteCI_isTowerEntry {st : EStore} {ci : IConstantInfo}
    {c : ConstantInfo} (h : Frontend.denoteCI st ci = some c) :
    ci.isTowerEntry = c.isTowerEntry := by
  cases ci <;> simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
  all_goals first
    | (obtain ⟨_, _, rfl⟩ := h; rfl)
    | (split at h
       · cases h; rfl
       · simp at h)

/-- con-leche: ConLeche/Kernel/Env.lean:639-642 ConstantInfo.toConstantVal —
off the tower the arena's `toConstantVal` is pure, and its record denotes
con-leche's `toConstantVal` of whatever the constant denotes.  Answer shape:
the constant comes out of the index. -/
theorem toConstantVal_nt_spec (s₀ : AState) (ci : IConstantInfo)
    (ht : ci.isTowerEntry = false) :
    ⦃fun s => ⌜s = s₀⌝⦄ ci.toConstantVal
    ⦃⇓? v s' => ⌜s' = s₀ ∧ ∀ c, Frontend.denoteCI s₀.store ci = some c →
        Frontend.denoteCV s₀.store v = some c.toConstantVal⌝⦄ := by
  cases ci with
  | projInfo t => simp [IConstantInfo.isTowerEntry] at ht
  | axiomInfo v =>
    mvcgen [IConstantInfo.toConstantVal]
    bridge_peel; subst_vars
    refine ⟨rfl, fun c hc => ?_⟩
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc
    obtain ⟨cv, hcv, rfl⟩ := hc; exact hcv
  | ctorInfo v nP nF =>
    mvcgen [IConstantInfo.toConstantVal]
    bridge_peel; subst_vars
    refine ⟨rfl, fun c hc => ?_⟩
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc
    obtain ⟨cv, hcv, rfl⟩ := hc; exact hcv
  | defnInfo v e hint =>
    mvcgen [IConstantInfo.toConstantVal]
    bridge_peel; subst_vars
    refine ⟨rfl, fun c hc => ?_⟩
    obtain ⟨cv, x, hcv, _, rfl⟩ := denoteCI_defnInfo_inv hc; exact hcv
  | thmInfo v e =>
    mvcgen [IConstantInfo.toConstantVal]
    bridge_peel; subst_vars
    refine ⟨rfl, fun c hc => ?_⟩
    simp only [Frontend.denoteCI] at hc
    split at hc
    · rename_i cv x hcv _; cases hc; exact hcv
    · simp at hc
  | indInfo v caps =>
    mvcgen [IConstantInfo.toConstantVal]
    bridge_peel; subst_vars
    refine ⟨rfl, fun c hc => ?_⟩
    simp only [Frontend.denoteCI] at hc
    split at hc
    · rename_i cv x hcv _; cases hc; exact hcv
    · simp at hc
  | recInfo v mI rP rs =>
    mvcgen [IConstantInfo.toConstantVal]
    bridge_peel; subst_vars
    refine ⟨rfl, fun c hc => ?_⟩
    simp only [Frontend.denoteCI] at hc
    split at hc
    · rename_i cv x hcv _; cases hc; exact hcv
    · simp at hc

/-- con-leche: none — a handle whose view is not a `.sort` denotes no sort. -/
theorem denote_not_sort {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} {v : ENodeView} (hv : st.view h = some v)
    (he : denoteE st h = some e)
    (hne : ∀ u, v = .sort u → False) : ∀ l, e ≠ .sort l := by
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv he]; simp
  | fvar k t => obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv he; simp
  | sort u => exact absurd rfl (hne u)
  | const n us => obtain ⟨_, _, rfl, _, _⟩ := denote_const_inv hwf hv he; simp
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv he; simp
  | lam ty b m => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; simp
  | forallE ty b m =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv he; simp
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv he; simp
  | lit l => rw [denote_lit_inv hwf hv he]; simp
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv he; simp

/-- con-leche: none — a handle whose view is not a `.lam` denotes no λ. -/
theorem denote_not_lam {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} {v : ENodeView} (hv : st.view h = some v)
    (he : denoteE st h = some e)
    (hne : ∀ ty b m, v = .lam ty b m → False) : ∀ p q m, e ≠ .lam p q m := by
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv he]; simp
  | fvar k t => obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv he; simp
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv he; simp
  | const n us => obtain ⟨_, _, rfl, _, _⟩ := denote_const_inv hwf hv he; simp
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv he; simp
  | lam ty b m => exact absurd rfl (hne ty b m)
  | forallE ty b m =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv he; simp
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv he; simp
  | lit l => rw [denote_lit_inv hwf hv he]; simp
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv he; simp

/-- con-leche: none — a handle whose view is none of `.app` denotes no
application. -/
theorem denote_not_app' {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} {v : ENodeView} (hv : st.view h = some v)
    (he : denoteE st h = some e)
    (hne : ∀ f a, v = .app f a → False) : ∀ p q, e ≠ .app p q := by
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv he]; simp
  | fvar k t => obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv he; simp
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv he; simp
  | const n us => obtain ⟨_, _, rfl, _, _⟩ := denote_const_inv hwf hv he; simp
  | app f a => exact absurd rfl (hne f a)
  | lam ty b m => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; simp
  | forallE ty b m =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv he; simp
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv he; simp
  | lit l => rw [denote_lit_inv hwf hv he]; simp
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv he; simp

/-- con-leche: none — `denoteEO` at a present handle. -/
theorem denoteEO_some_inv {st : EStore} {h : EIdx} {ox : Option Expr}
    (hd : denoteEO st (some h) = some ox) :
    ∃ x, ox = some x ∧ denoteE st h = some x := by
  simp only [denoteEO, Option.map_eq_some_iff] at hd
  obtain ⟨x, hx, rfl⟩ := hd
  exact ⟨x, rfl, hx⟩

/-- con-leche: none — `denoteEO` at an absent handle. -/
theorem denoteEO_none_inv {st : EStore} {ox : Option Expr}
    (hd : denoteEO st none = some ox) : ox = none := by
  simp only [denoteEO] at hd; exact (Option.some.inj hd).symm

/-- con-leche: none — a handle whose view is not an `.fvar` denotes no
free variable. -/
theorem denote_not_fvar {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} {v : ENodeView} (hv : st.view h = some v)
    (he : denoteE st h = some e)
    (hne : ∀ k t, v = .fvar k t → False) : ∀ k t, e ≠ .fvar k t := by
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv he]; simp
  | fvar k t => exact absurd rfl (hne k t)
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv he; simp
  | const n us => obtain ⟨_, _, rfl, _, _⟩ := denote_const_inv hwf hv he; simp
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv he; simp
  | lam ty b m => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; simp
  | forallE ty b m =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv he; simp
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv he; simp
  | lit l => rw [denote_lit_inv hwf hv he]; simp
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv he; simp

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the constant arm of both
head readers, set up once**: a `.const` view under a denoted handle, an index
HIT, and the stored record off the tower.  Everything the two readers compare
against con-leche's arm is here: the name's environment entry, its
tower-ness, the level count, and the stored type's and level parameters'
denotations. -/
theorem const_hit {s : AState} (hok : CheckOK mode env fe s) {h : EIdx}
    {I : NIdx} {us : LsIdx} {ci : IConstantInfo} {v : IConstantVal} {x : Expr}
    (hview : s.store.view h = some (.const I us))
    (hfd : fe.find? I = some ci)
    (hcv : ∀ c, Frontend.denoteCI s.store ci = some c →
      Frontend.denoteCV s.store v = some c.toConstantVal)
    (hx : denoteE s.store h = some x) :
    ∃ nm ls c, x = .const nm ls ∧ denoteLs s.store.lss us = some ls ∧
      env.find? nm = some c ∧ ci.isTowerEntry = c.isTowerEntry ∧
      Frontend.denoteNList s.store.ns v.levelParams =
        some c.toConstantVal.levelParams ∧
      denoteE s.store v.type = some c.toConstantVal.type ∧
      c.toConstantVal.levelParams.length = v.levelParams.length ∧
      s.store.lss.viewLen us = some ls.length := by
  obtain ⟨nm, ls, rfl, hn, hls⟩ := denote_const_inv hok.state.wf hview hx
  have hrel := optCI_find hok hn
  rw [hfd] at hrel
  obtain ⟨c, hci, hfind⟩ := hrel
  obtain ⟨_, hlps, hty⟩ := denoteCV_inv (hcv c hci)
  exact ⟨nm, ls, c, rfl, hls, hfind, denoteCI_isTowerEntry hci, hlps, hty,
    denoteNList_len hlps, viewLen_of_denoteLs hls⟩

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the constant arm at an
index HIT on a tower entry, before `toConstantVal` runs. -/
theorem const_tower {s : AState} (hok : CheckOK mode env fe s) {h : EIdx}
    {I : NIdx} {us : LsIdx} {ci : IConstantInfo} {x : Expr}
    (hview : s.store.view h = some (.const I us))
    (hfd : fe.find? I = some ci)
    (hx : denoteE s.store h = some x) :
    ∃ nm ls c, x = .const nm ls ∧ env.find? nm = some c ∧
      ci.isTowerEntry = c.isTowerEntry := by
  obtain ⟨nm, ls, rfl, hn, _⟩ := denote_const_inv hok.state.wf hview hx
  have hrel := optCI_find hok hn
  rw [hfd] at hrel
  obtain ⟨c, hci, hfind⟩ := hrel
  exact ⟨nm, ls, c, rfl, hfind, denoteCI_isTowerEntry hci⟩

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the constant arm at an
index MISS. -/
theorem const_miss {s : AState} (hok : CheckOK mode env fe s) {h : EIdx}
    {I : NIdx} {us : LsIdx} {x : Expr}
    (hview : s.store.view h = some (.const I us))
    (hfd : fe.find? I = none)
    (hx : denoteE s.store h = some x) :
    ∃ nm ls, x = .const nm ls ∧ env.find? nm = none := by
  obtain ⟨nm, ls, rfl, hn, _⟩ := denote_const_inv hok.state.wf hview hx
  have hrel := optCI_find hok hn
  rw [hfd] at hrel
  exact ⟨nm, ls, rfl, hrel⟩

/-! ### con-leche's two head readers at their exits -/

/-- con-leche: ConLeche/Kernel/PropRead.lean:73-90 headTypePW — a constant
head the environment answers off the tower at the right level count. -/
theorem headTypePW_const_hit {find? : ConLeche.Name → Option ConstantInfo}
    {nm : ConLeche.Name} {ls : List Level} {n : Nat} {c : ConstantInfo}
    (hf : find? nm = some c) (ht : c.isTowerEntry = false)
    (hl : ls.length = c.toConstantVal.levelParams.length) :
    ConLeche.headTypePW find? (.const nm ls) n =
      (ConLeche.residualPW (c.toConstantVal.type.peelNeverPis n)).map
        (Level.substPW c.toConstantVal.levelParams ls) := by
  simp only [ConLeche.headTypePW, hf, ht, hl, Bool.false_eq_true, if_false,
    if_true]

/-- con-leche: ConLeche/Kernel/PropRead.lean:73-90 headTypePW — every other
constant head declines. -/
theorem headTypePW_const_none {find? : ConLeche.Name → Option ConstantInfo}
    {nm : ConLeche.Name} {ls : List Level} {n : Nat}
    (h : find? nm = none ∨ ∃ c, find? nm = some c ∧
      (c.isTowerEntry = true ∨ ls.length ≠ c.toConstantVal.levelParams.length)) :
    ConLeche.headTypePW find? (.const nm ls) n = none := by
  rcases h with hf | ⟨c, hf, ht | hl⟩
  · simp only [ConLeche.headTypePW, hf]
  · simp only [ConLeche.headTypePW, hf, ht, if_true]
  · simp only [ConLeche.headTypePW, hf, hl, if_false]; split <;> rfl

/-- con-leche: ConLeche/Kernel/PropRead.lean:105-122 headProofPW — a constant
head the environment answers off the tower at the right level count. -/
theorem headProofPW_const_hit {find? : ConLeche.Name → Option ConstantInfo}
    {nm : ConLeche.Name} {ls : List Level} {c : ConstantInfo}
    (hf : find? nm = some c) (ht : c.isTowerEntry = false)
    (hl : ls.length = c.toConstantVal.levelParams.length) :
    ConLeche.headProofPW find? (.const nm ls) =
      (ConLeche.typeSortPW find? c.toConstantVal.type).map
        (Level.substPW c.toConstantVal.levelParams ls) := by
  simp only [ConLeche.headProofPW, hf, ht, hl, Bool.false_eq_true, if_false,
    if_true]

/-- con-leche: ConLeche/Kernel/PropRead.lean:105-122 headProofPW — every
other constant head declines. -/
theorem headProofPW_const_none {find? : ConLeche.Name → Option ConstantInfo}
    {nm : ConLeche.Name} {ls : List Level}
    (h : find? nm = none ∨ ∃ c, find? nm = some c ∧
      (c.isTowerEntry = true ∨ ls.length ≠ c.toConstantVal.levelParams.length)) :
    ConLeche.headProofPW find? (.const nm ls) = none := by
  rcases h with hf | ⟨c, hf, ht | hl⟩
  · simp only [ConLeche.headProofPW, hf]
  · simp only [ConLeche.headProofPW, hf, ht, if_true]
  · simp only [ConLeche.headProofPW, hf, hl, if_false]; split <;> rfl

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2439-2449 Level.substPW_eq_self —
**the has-parameters cutoff** of the arena's two head readers (task
#97-P6-10): on a parameter-free datum the substitution is the identity, so
answering `pw` without the two readbacks is con-leche's `map`. -/
theorem substPW_cutoff {ks : List ConLeche.Name} {vs : List Level}
    {pw : PropWhen} (h : (!pw.hasParams) = true) :
    Level.substPW ks vs pw = pw :=
  Level.substPW_eq_self (by simpa using h)

/-! ## 2. The three view-only readers -/

/-- con-leche: ConLeche/Kernel/PropRead.lean:44-56 Expr.peelNeverPis —
**THEOREM 1 for `peelNeverPis`**, in answer shape (the subject is a stored
type or a declared fvar type, both reached through another read).
Structural on `k` on both sides. -/
theorem peelNeverPis_spec' (k : Nat) : ∀ (s₀ : AState) (h : EIdx),
    CheckOK mode env fe s₀ → (∃ x, denoteE s₀.store h = some x) →
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.peelNeverPis k h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ ∀ x, denoteE s₀.store h = some x →
        denoteEO s₀.store r = some (x.peelNeverPis k)⌝⦄ := by
  induction k with
  | zero =>
    intro s₀ h _ _
    mvcgen [ConRon.Arena.peelNeverPis]
    bridge_peel; subst_vars
    refine ⟨rfl, fun x hx => ?_⟩
    simp only [denoteEO, hx, Option.map_some, Expr.peelNeverPis]
  | succ k ih =>
    intro s₀ h hok hpre
    obtain ⟨x₀, hx₀⟩ := hpre
    mvcgen [ConRon.Arena.peelNeverPis, ih]
    all_goals (bridge_peel; subst_vars)
    case vc2 => intro s hs _; subst hs; exact hok
    case vc3 =>
      intro s hs hview; subst hs
      obtain ⟨_, eb, _, _, hb⟩ := denote_forallE_inv hok.state.wf hview hx₀
      exact ⟨eb, hb⟩
    case vc1 =>
      rename_i ty b m hnev s0 r s1 hview
      intro hs hr; subst hs
      refine ⟨rfl, fun x hx => ?_⟩
      obtain ⟨et, eb, rfl, _, hb⟩ := denote_forallE_inv hok.state.wf hview hx
      rw [hr eb hb]
      simp only [Expr.peelNeverPis, hnev, if_true]
    case vc4 =>
      rename_i ty b m hnev s0 hview
      refine ⟨rfl, fun x hx => ?_⟩
      obtain ⟨et, eb, rfl, _, hb⟩ := denote_forallE_inv hok.state.wf hview hx
      simp [denoteEO, Expr.peelNeverPis, hnev]
    case vc5 =>
      rename_i v hnf s0 hview
      refine ⟨rfl, fun x hx => ?_⟩
      have hne := denote_not_forallE hok.state.wf hview hx hnf
      simp only [denoteEO]
      cases x <;> first | rfl | exact absurd rfl (hne _ _ _)

/-- con-leche: ConLeche/Kernel/PropRead.lean:44-56 Expr.peelNeverPis —
**THEOREM 1 for `peelNeverPis`**, published shape. -/
theorem peelNeverPis_spec (k : Nat) (s₀ : AState) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.peelNeverPis k h
    ⦃⇓? r s' => ⌜s' = s₀ ∧
        denoteEO s₀.store r = some (x.peelNeverPis k)⌝⦄ := by
  have hb := peelNeverPis_spec' (mode := mode) (env := env) (fe := fe) k s₀ h
    hok ⟨x, hden⟩
  mvcgen [hb]
  intro h1 h2
  exact ⟨h1, h2 x hden⟩

/-- con-leche: ConLeche/Kernel/PropRead.lean:58-61 Expr.numArgs — **THEOREM 1
for `numArgs`**, in answer shape.  The arena's walk is fueled and FAILS at
fuel `0`; `⇓?` claims nothing of a failure, so the equation is unconditional
on success. -/
theorem numArgs_spec' (fuel : Nat) : ∀ (s₀ : AState) (h : EIdx),
    CheckOK mode env fe s₀ → (∃ x, denoteE s₀.store h = some x) →
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.numArgs fuel h
    ⦃⇓? n s' => ⌜s' = s₀ ∧ ∀ x, denoteE s₀.store h = some x →
        n = x.numArgs⌝⦄ := by
  induction fuel with
  | zero =>
    intro s₀ h _ _
    mvcgen [ConRon.Arena.numArgs]
    all_goals (bridge_peel; subst_vars)
    intro hf; exact hf.elim
  | succ fuel ih =>
    intro s₀ h hok hpre
    obtain ⟨x₀, hx₀⟩ := hpre
    mvcgen [ConRon.Arena.numArgs, ih]
    all_goals (bridge_peel; subst_vars)
    case vc1.a => exact hok
    case vc2.a =>
      rename_i f a s0 hview
      obtain ⟨ef, _, _, hf, _⟩ := denote_app_inv hok.state.wf hview hx₀
      exact ⟨ef, hf⟩
    case vc3 =>
      rename_i f a r s0 hr hview
      refine ⟨rfl, fun x hx => ?_⟩
      obtain ⟨ef, ea, rfl, hf, _⟩ := denote_app_inv hok.state.wf hview hx
      rw [hr ef hf]; rfl
    case vc4 =>
      rename_i v hna s0 hview
      refine ⟨rfl, fun x hx => ?_⟩
      have hne := denote_not_app' hok.state.wf hview hx hna
      cases x <;> first | rfl | exact absurd rfl (hne _ _)

/-- con-leche: ConLeche/Kernel/PropRead.lean:65-71 residualPW — **THEOREM 1
for `residualPW`**, in answer shape (the residual is `peelNeverPis`'s
answer).  The level is read back with `readLevel`, which leaves the state
alone. -/
theorem residualPW_spec' (s₀ : AState) (r : Option EIdx)
    (hok : CheckOK mode env fe s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.residualPW r
    ⦃⇓? pw s' => ⌜s' = s₀ ∧ ∀ ox, denoteEO s₀.store r = some ox →
        pw = ConLeche.residualPW ox⌝⦄ := by
  mvcgen [ConRon.Arena.residualPW]
  all_goals (bridge_peel; subst_vars)
  case vc1 =>
    rename_i h u l s0 hl hview
    refine ⟨rfl, fun ox hox => ?_⟩
    obtain ⟨x, rfl, hx⟩ := denoteEO_some_inv hox
    obtain ⟨l', rfl, hl'⟩ := denote_sort_inv hok.state.wf hview hx
    rw [hl] at hl'; cases hl'; rfl
  case vc2 =>
    rename_i h v hns s0 hview
    refine ⟨rfl, fun ox hox => ?_⟩
    obtain ⟨x, rfl, hx⟩ := denoteEO_some_inv hox
    have hne := denote_not_sort hok.state.wf hview hx hns
    cases x <;> first | rfl | exact absurd rfl (hne _)
  case vc3 =>
    refine ⟨rfl, fun ox hox => ?_⟩
    rw [denoteEO_none_inv hox]; rfl

/-- con-leche: ConLeche/Kernel/PropRead.lean:65-71 residualPW — published
shape. -/
theorem residualPW_spec (s₀ : AState) (r : Option EIdx) (ox : Option Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteEO s₀.store r = some ox) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.residualPW r
    ⦃⇓? pw s' => ⌜s' = s₀ ∧ pw = ConLeche.residualPW ox⌝⦄ := by
  have hb := residualPW_spec' (mode := mode) (env := env) (fe := fe) s₀ r hok
  mvcgen [hb]
  intro h1 h2
  exact ⟨h1, h2 ox hden⟩

/-- con-leche: ConLeche/Kernel/PropRead.lean:58-61 Expr.numArgs — published
shape. -/
theorem numArgs_spec (fuel : Nat) (s₀ : AState) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.numArgs fuel h
    ⦃⇓? n s' => ⌜s' = s₀ ∧ n = x.numArgs⌝⦄ := by
  have hb := numArgs_spec' (mode := mode) (env := env) (fe := fe) fuel s₀ h
    hok ⟨x, hden⟩
  mvcgen [hb]
  intro h1 h2
  exact ⟨h1, h2 x hden⟩

/-! ## 3. The head readers -/

/-- con-leche: ConLeche/Kernel/PropRead.lean:73-90 headTypePW — **THEOREM 1
for `headTypePW`**, in answer shape (the head is `getAppFn`'s answer). -/
theorem headTypePW_spec' (s₀ : AState) (h : EIdx) (n : Nat)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store h = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.headTypePW fe h n
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store h = some x →
        r = ConLeche.headTypePW env.find? x n⌝⦄ := by
  obtain ⟨x₀, hx₀⟩ := hpre
  have hpeel := fun (s : AState) (k : Nat) (e : EIdx) =>
    peelNeverPis_spec' (mode := mode) (env := env) (fe := fe) k s e
  have hres := fun (s : AState) (r : Option EIdx) =>
    residualPW_spec' (mode := mode) (env := env) (fe := fe) s r
  have htcv := toConstantVal_nt_spec
  mvcgen [ConRon.Arena.headTypePW, hpeel, hres, htcv]
  all_goals (bridge_peel; subst_vars)
  -- the callees' preconditions
  case vc2.ht => rename_i I us ci hfd htow s0 hview; simpa using htow
  case vc3 => intro hf; exact hf.elim
  case vc4.a => exact hok
  case vc5.a =>
    rename_i I us ci hfd htow v s0 hcv hview hlen
    obtain ⟨_, _, _, _, _, _, _, _, hty, _⟩ := const_hit hok hview hfd hcv hx₀
    exact ⟨_, hty⟩
  case vc6.hok => exact hok
  case vc8.hc => exact hok.caches.readN
  case vc9.hc =>
    rename_i I us ci hfd htow v r pw hhp s0 ks s1 hst hm hp hc hks hN hres
      hpeel hcv hview hlen
    exact (CheckOK.ofReadbackFrame hok
      (ReadbackFrame.ofReadN hst hm hp hc hN)).caches.readLs
  case vc14.a => exact hok
  case vc15.a =>
    rename_i idx ty s0 hview
    obtain ⟨t, _, ht⟩ := denote_fvar_inv hok.state.wf hview hx₀
    exact ⟨t, ht⟩
  case vc17 => intro s hs _; subst hs; exact hok
  -- a tower entry declines on both sides
  case vc1 =>
    rename_i I us ci hfd htow s0 hview
    refine ⟨hok, rfl, rfl, fun x hx => ?_⟩
    obtain ⟨nm, ls, c, rfl, hf, ht⟩ := const_tower hok hview hfd hx
    exact (headTypePW_const_none (Or.inr ⟨c, hf, Or.inl (ht ▸ htow)⟩)).symm
  -- the cutoff: a parameter-free datum is answered without the readbacks
  case vc7 =>
    rename_i I us ci hfd htow v r pw hhp s0 hres hpeel hcv hview hlen
    refine ⟨hok, rfl, rfl, fun x hx => ?_⟩
    obtain ⟨nm, ls, c, rfl, _, hf, ht, _, hty, hll, hvl⟩ :=
      const_hit hok hview hfd hcv hx
    rw [hvl] at hlen
    have hl : ls.length = c.toConstantVal.levelParams.length := by
      rw [hll]; exact (Option.some.inj hlen).symm
    rw [headTypePW_const_hit hf (by rw [← ht]; simpa using htow) hl,
      ← hres _ (hpeel _ hty), Option.map_some, substPW_cutoff hhp]
  -- the datum names parameters: both readbacks, then con-leche's `map`
  case vc10 =>
    rename_i I us ci hfd htow v r pw hhp s0 ks s1 vs s2 hst1 hst2 hm1 hm2 hp1
      hp2 hc1 hc2 hks hN hvs hLs hres hpeel hcv hview hlen
    have hf1 := ReadbackFrame.ofReadN hst1 hm1 hp1 hc1 hN
    have hf2 := ReadbackFrame.ofReadLs hst2 hm2 hp2 hc2 hLs
    have hf := hf1.trans hf2
    refine ⟨CheckOK.ofReadbackFrame hok hf, hf.store, hf.pins,
      fun x hx => ?_⟩
    obtain ⟨nm, ls, c, rfl, hls, hf', ht, hlps, hty, hll, hvl⟩ :=
      const_hit hok hview hfd hcv hx
    rw [hvl] at hlen
    have hl : ls.length = c.toConstantVal.levelParams.length := by
      rw [hll]; exact (Option.some.inj hlen).symm
    rw [hlps] at hks
    rw [hst1, hls] at hvs
    obtain rfl := Option.some.inj hks
    obtain rfl := Option.some.inj hvs
    rw [headTypePW_const_hit hf' (by rw [← ht]; simpa using htow) hl,
      ← hres _ (hpeel _ hty), Option.map_some]
  -- the residual is not a sort
  case vc11 =>
    rename_i I us ci hfd htow v r s0 hres hpeel hcv hview hlen
    refine ⟨hok, rfl, rfl, fun x hx => ?_⟩
    obtain ⟨nm, ls, c, rfl, _, hf, ht, _, hty, hll, hvl⟩ :=
      const_hit hok hview hfd hcv hx
    rw [hvl] at hlen
    have hl : ls.length = c.toConstantVal.levelParams.length := by
      rw [hll]; exact (Option.some.inj hlen).symm
    rw [headTypePW_const_hit hf (by rw [← ht]; simpa using htow) hl,
      ← hres _ (hpeel _ hty), Option.map_none]
  -- the level count does not match
  case vc12 =>
    rename_i I us ci hfd htow v usl hne s0 hlen hcv hview
    refine ⟨hok, rfl, rfl, fun x hx => ?_⟩
    obtain ⟨nm, ls, c, rfl, _, hf, _, _, _, hll, hvl⟩ :=
      const_hit hok hview hfd hcv hx
    rw [hvl] at hlen
    obtain rfl := Option.some.inj hlen
    exact (headTypePW_const_none
      (Or.inr ⟨c, hf, Or.inr (by rw [hll]; exact hne)⟩)).symm
  -- an index miss
  case vc13 =>
    rename_i I us hfd s0 hview
    refine ⟨hok, rfl, rfl, fun x hx => ?_⟩
    obtain ⟨nm, ls, rfl, hf⟩ := const_miss hok hview hfd hx
    exact (headTypePW_const_none (Or.inl hf)).symm
  -- an fvar head reads its declared type
  case vc16 =>
    rename_i idx ty r0 s1 r s0 hpeel hview
    intro hs hres; subst hs
    refine ⟨hok, rfl, rfl, fun x hx => ?_⟩
    obtain ⟨t, rfl, ht⟩ := denote_fvar_inv hok.state.wf hview hx
    rw [hres _ (hpeel t ht)]; rfl
  -- any other head declines
  case vc18 =>
    rename_i v hnc hnf s0 hview
    refine ⟨hok, rfl, rfl, fun x hx => ?_⟩
    have h1 := denote_not_const hok.state.wf hview hx
      (fun c us he => hnc c us he)
    have h2 := denote_not_fvar hok.state.wf hview hx hnf
    cases x <;> first | rfl | exact absurd rfl (h1 _ _) | exact absurd rfl (h2 _ _)

/-- con-leche: ConLeche/Kernel/PropRead.lean:73-90 headTypePW — published
shape. -/
theorem headTypePW_spec (s₀ : AState) (h : EIdx) (n : Nat) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.headTypePW fe h n
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.headTypePW env.find? x n⌝⦄ := by
  have hb := headTypePW_spec' (mode := mode) (env := env) (fe := fe) s₀ h n
    hok ⟨x, hden⟩
  mvcgen [hb]
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4 x hden⟩

/-- con-leche: ConLeche/Kernel/PropRead.lean:92-103 typeSortPW — the last
arm: neither a ∀ nor a sort reads its head. -/
theorem typeSortPW_other {find? : ConLeche.Name → Option ConstantInfo}
    {x : Expr} (hf : ∀ p q m, x ≠ .forallE p q m) (hs : ∀ l, x ≠ .sort l) :
    ConLeche.typeSortPW find? x =
      ConLeche.headTypePW find? x.getAppFn x.numArgs := by
  cases x <;> first
    | rfl
    | exact absurd rfl (hf _ _ _)
    | exact absurd rfl (hs _)

/-- con-leche: ConLeche/Kernel/PropRead.lean:92-103 typeSortPW — **THEOREM 1
for `typeSortPW`**, in answer shape: `annotPwPi` calls it on the knot's
`annotate` answer and `headProofPW` on a stored type. -/
theorem typeSortPW_spec' (fuel : Nat) (s₀ : AState) (T : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store T = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.typeSortPW fe fuel T
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store T = some x →
        r = ConLeche.typeSortPW env.find? x⌝⦄ := by
  obtain ⟨x₀, hx₀⟩ := hpre
  have hfn := ExprOps.getAppFn_spec fuel
  have hna := fun (s : AState) (e : EIdx) =>
    numArgs_spec' (mode := mode) (env := env) (fe := fe) fuel s e
  have hht := fun (s : AState) (e : EIdx) (n : Nat) =>
    headTypePW_spec' (mode := mode) (env := env) (fe := fe) s e n
  mvcgen [ConRon.Arena.typeSortPW, hfn, hna, hht]
  all_goals (bridge_peel; subst_vars)
  case vc3.a => exact hok.state
  case vc4.a => rw [hx₀]; rfl
  case vc5.a => exact hok
  case vc6.a => exact ⟨x₀, hx₀⟩
  case vc8 => intro s hs _; subst hs; exact hok
  case vc9 =>
    rename_i v hnf hns fn s0 n hfn' hview
    intro s hs _; subst hs
    exact ⟨_, hfn' x₀ hx₀⟩
  case vc1 =>
    rename_i ty b m s0 hview
    refine ⟨hok, rfl, rfl, fun x hx => ?_⟩
    obtain ⟨_, _, rfl, _, _⟩ := denote_forallE_inv hok.state.wf hview hx
    rfl
  case vc2 =>
    rename_i u s0 hview
    refine ⟨hok, rfl, rfl, fun x hx => ?_⟩
    obtain ⟨_, rfl, _⟩ := denote_sort_inv hok.state.wf hview hx
    rfl
  case vc7 =>
    rename_i v hnf hns fn n s1 r s0 hn hfn' hview
    intro hck hst hp hr
    refine ⟨hck, hst, hp, fun x hx => ?_⟩
    rw [typeSortPW_other (denote_not_forallE hok.state.wf hview hx hnf)
      (denote_not_sort hok.state.wf hview hx hns), hr _ (hfn' x hx), hn x hx]

/-- con-leche: ConLeche/Kernel/PropRead.lean:92-103 typeSortPW — published
shape. -/
theorem typeSortPW_spec (fuel : Nat) (s₀ : AState) (T : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store T = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.typeSortPW fe fuel T
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.typeSortPW env.find? x⌝⦄ := by
  have hb := typeSortPW_spec' (mode := mode) (env := env) (fe := fe) fuel s₀ T
    hok ⟨x, hden⟩
  mvcgen [hb]
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4 x hden⟩

/-- con-leche: ConLeche/Kernel/PropRead.lean:105-122 headProofPW — **THEOREM 1
for `headProofPW`**, in answer shape (the head is `getAppFn`'s answer). -/
theorem headProofPW_spec' (fuel : Nat) (s₀ : AState) (h : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store h = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.headProofPW fe fuel h
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store h = some x →
        r = ConLeche.headProofPW env.find? x⌝⦄ := by
  obtain ⟨x₀, hx₀⟩ := hpre
  have hts := fun (s : AState) (e : EIdx) =>
    typeSortPW_spec' (mode := mode) (env := env) (fe := fe) fuel s e
  have htcv := toConstantVal_nt_spec
  mvcgen [ConRon.Arena.headProofPW, hts, htcv]
  all_goals (bridge_peel; subst_vars)
  -- the callees' preconditions
  case vc2.ht => rename_i c us ci hfd htow s0 hview; simpa using htow
  case vc3 => intro hf; exact hf.elim
  case vc4.hok => exact hok
  case vc5.hpre =>
    rename_i c us ci hfd htow v s0 hcv hview hlen
    obtain ⟨_, _, _, _, _, _, _, _, hty, _⟩ := const_hit hok hview hfd hcv hx₀
    exact ⟨_, hty⟩
  case vc7.hc =>
    rename_i c us ci hfd htow v s1 pw hhp s0 hck hst hp hts hcv hview hlen
    exact hck.caches.readN
  case vc8.hc =>
    rename_i c us ci hfd htow v s2 pw hhp s1 ks s0 hck1 hst01 hst12 hm01 hp12
      hts hp01 hc01 hks hN hcv hview hlen
    exact (CheckOK.ofReadbackFrame hck1
      (ReadbackFrame.ofReadN hst01 hm01 hp01 hc01 hN)).caches.readLs
  case vc14 => intro s hs _; subst hs; exact hok
  case vc15 =>
    intro s hs hview; subst hs
    obtain ⟨t, _, ht⟩ := denote_fvar_inv hok.state.wf hview hx₀
    exact ⟨t, ht⟩
  -- a tower entry declines on both sides
  case vc1 =>
    rename_i c us ci hfd htow s0 hview
    refine ⟨hok, rfl, rfl, fun x hx => ?_⟩
    obtain ⟨nm, ls, c', rfl, hf, ht⟩ := const_tower hok hview hfd hx
    exact (headProofPW_const_none (Or.inr ⟨c', hf, Or.inl (ht ▸ htow)⟩)).symm
  -- the cutoff
  case vc6 =>
    rename_i c us ci hfd htow v s1 pw hhp s0 hck hst hp hts hcv hview hlen
    refine ⟨hck, hst, hp, fun x hx => ?_⟩
    obtain ⟨nm, ls, c', rfl, _, hf, ht, _, hty, hll, hvl⟩ :=
      const_hit hok hview hfd hcv hx
    rw [hvl] at hlen
    have hl : ls.length = c'.toConstantVal.levelParams.length := by
      rw [hll]; exact (Option.some.inj hlen).symm
    rw [headProofPW_const_hit hf (by rw [← ht]; simpa using htow) hl,
      ← hts _ hty, Option.map_some, substPW_cutoff hhp]
  -- both readbacks
  case vc9 =>
    rename_i c us ci hfd htow v s3 pw hhp s2 ks s1 vs s0 hck2 hst12 hst01
      hst23 hm12 hm01 hp23 hts hp12 hp01 hc12 hc01 hks hN hvs hLs hcv hview
      hlen
    have hf1 := ReadbackFrame.ofReadN hst12 hm12 hp12 hc12 hN
    have hf2 := ReadbackFrame.ofReadLs hst01 hm01 hp01 hc01 hLs
    have hf := hf1.trans hf2
    refine ⟨CheckOK.ofReadbackFrame hck2 hf, hf.store.trans hst23,
      hf.pins.trans hp23, fun x hx => ?_⟩
    obtain ⟨nm, ls, c', rfl, hls, hf', ht, hlps, hty, hll, hvl⟩ :=
      const_hit hok hview hfd hcv hx
    rw [hvl] at hlen
    have hl : ls.length = c'.toConstantVal.levelParams.length := by
      rw [hll]; exact (Option.some.inj hlen).symm
    rw [hst23, hlps] at hks
    rw [hst12, hst23, hls] at hvs
    obtain rfl := Option.some.inj hks
    obtain rfl := Option.some.inj hvs
    rw [headProofPW_const_hit hf' (by rw [← ht]; simpa using htow) hl,
      ← hts _ hty, Option.map_some]
  -- the stored type's datum is unknown
  case vc10 =>
    rename_i c us ci hfd htow v s1 s0 hck hst hp hts hcv hview hlen
    refine ⟨hck, hst, hp, fun x hx => ?_⟩
    obtain ⟨nm, ls, c', rfl, _, hf, ht, _, hty, hll, hvl⟩ :=
      const_hit hok hview hfd hcv hx
    rw [hvl] at hlen
    have hl : ls.length = c'.toConstantVal.levelParams.length := by
      rw [hll]; exact (Option.some.inj hlen).symm
    rw [headProofPW_const_hit hf (by rw [← ht]; simpa using htow) hl,
      ← hts _ hty, Option.map_none]
  -- the level count does not match
  case vc11 =>
    rename_i c us ci hfd htow v usl hne s0 hlen hcv hview
    refine ⟨hok, rfl, rfl, fun x hx => ?_⟩
    obtain ⟨nm, ls, c', rfl, _, hf, _, _, _, hll, hvl⟩ :=
      const_hit hok hview hfd hcv hx
    rw [hvl] at hlen
    obtain rfl := Option.some.inj hlen
    exact (headProofPW_const_none
      (Or.inr ⟨c', hf, Or.inr (by rw [hll]; exact hne)⟩)).symm
  -- an index miss
  case vc12 =>
    rename_i c us hfd s0 hview
    refine ⟨hok, rfl, rfl, fun x hx => ?_⟩
    obtain ⟨nm, ls, rfl, hf⟩ := const_miss hok hview hfd hx
    exact (headProofPW_const_none (Or.inl hf)).symm
  -- an fvar head reads its declared type
  case vc13 =>
    rename_i idx ty s1 r s0 hview
    intro hck hst hp hts
    refine ⟨hck, hst, hp, fun x hx => ?_⟩
    obtain ⟨t, rfl, ht⟩ := denote_fvar_inv hok.state.wf hview hx
    exact hts t ht
  -- sorts, ∀s and literals are never proofs
  case vc16 =>
    rename_i u s0 hview
    refine ⟨hok, rfl, rfl, fun x hx => ?_⟩
    obtain ⟨_, rfl, _⟩ := denote_sort_inv hok.state.wf hview hx; rfl
  case vc17 =>
    rename_i ty b m s0 hview
    refine ⟨hok, rfl, rfl, fun x hx => ?_⟩
    obtain ⟨_, _, rfl, _, _⟩ := denote_forallE_inv hok.state.wf hview hx; rfl
  case vc18 =>
    rename_i l s0 hview
    refine ⟨hok, rfl, rfl, fun x hx => ?_⟩
    rw [denote_lit_inv hok.state.wf hview hx]; rfl
  -- any other head declines
  case vc19 =>
    rename_i v h1 h2 h3 h4 h5 s0 hview
    refine ⟨hok, rfl, rfl, fun x hx => ?_⟩
    have hwf := hok.state.wf
    cases v with
    | bvar i => rw [denote_bvar_inv hwf hview hx]; rfl
    | fvar k t => exact absurd rfl (h2 k t)
    | sort u => exact absurd rfl (h3 u)
    | const c us => exact absurd rfl (h1 c us)
    | app f a => obtain ⟨_, _, rfl, _, _⟩ := denote_app_inv hwf hview hx; rfl
    | lam ty b m => obtain ⟨_, _, rfl, _, _⟩ := denote_lam_inv hwf hview hx; rfl
    | forallE ty b m => exact absurd rfl (h4 ty b m)
    | letE ty w b =>
      obtain ⟨_, _, _, rfl, _, _, _⟩ := denote_letE_inv hwf hview hx; rfl
    | lit l => exact absurd rfl (h5 l)
    | proj n i sub =>
      obtain ⟨_, _, rfl, _, _⟩ := denote_proj_inv hwf hview hx; rfl

/-- con-leche: ConLeche/Kernel/PropRead.lean:105-122 headProofPW — published
shape. -/
theorem headProofPW_spec (fuel : Nat) (s₀ : AState) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.headProofPW fe fuel h
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.headProofPW env.find? x⌝⦄ := by
  have hb := headProofPW_spec' (mode := mode) (env := env) (fe := fe) fuel s₀ h
    hok ⟨x, hden⟩
  mvcgen [hb]
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4 x hden⟩

/-- con-leche: ConLeche/Kernel/PropRead.lean:124-134 proofPW — the last arm:
anything but a λ reads its head. -/
theorem proofPW_other {find? : ConLeche.Name → Option ConstantInfo}
    {x : Expr} (hl : ∀ p q m, x ≠ .lam p q m) :
    ConLeche.proofPW find? x = ConLeche.headProofPW find? x.getAppFn := by
  cases x <;> first
    | rfl
    | exact absurd rfl (hl _ _ _)

/-- con-leche: ConLeche/Kernel/PropRead.lean:124-134 proofPW — **THEOREM 1
for `proofPW`**, in answer shape: `annotPwLam` calls it on the knot's
`annotate` answer, and `notProofFast` / `isProofFast` on `propIrrel`'s
subjects. -/
theorem proofPW_spec' (fuel : Nat) (s₀ : AState) (a : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store a = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.proofPW fe fuel a
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store a = some x →
        r = ConLeche.proofPW env.find? x⌝⦄ := by
  obtain ⟨x₀, hx₀⟩ := hpre
  have hfn := ExprOps.getAppFn_spec fuel
  have hhp := fun (s : AState) (e : EIdx) =>
    headProofPW_spec' (mode := mode) (env := env) (fe := fe) fuel s e
  mvcgen [ConRon.Arena.proofPW, hfn, hhp]
  all_goals (bridge_peel; subst_vars)
  case vc2.a => exact hok.state
  case vc3.a => rw [hx₀]; rfl
  case vc5 => intro s hs _; subst hs; exact hok
  case vc6 =>
    intro s hs hrel; subst hs
    exact ⟨_, hrel x₀ hx₀⟩
  case vc1 =>
    rename_i ty b m s0 hview
    refine ⟨hok, rfl, rfl, fun x hx => ?_⟩
    obtain ⟨_, _, rfl, _, _⟩ := denote_lam_inv hok.state.wf hview hx
    rfl
  case vc4 =>
    rename_i v hnl fn s1 r s0 hfn' hview
    intro hck hst hp hr
    refine ⟨hck, hst, hp, fun x hx => ?_⟩
    rw [proofPW_other (denote_not_lam hok.state.wf hview hx hnl),
      hr _ (hfn' x hx)]

/-- con-leche: ConLeche/Kernel/PropRead.lean:124-134 proofPW — published
shape. -/
theorem proofPW_spec (fuel : Nat) (s₀ : AState) (a : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store a = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.proofPW fe fuel a
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.proofPW env.find? x⌝⦄ := by
  have hb := proofPW_spec' (mode := mode) (env := env) (fe := fe) fuel s₀ a
    hok ⟨x, hden⟩
  mvcgen [hb]
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4 x hden⟩

/-! ## 4. The two arms

Both decide a GUARD of `propIrrel`, so each states BOTH Bool outcomes: the
answer is an equation with con-leche's `Bool`, which is the negative half as
much as the positive one. -/

/-- con-leche: ConLeche/Kernel/PropRead.lean:141-146 notProofFast — **THEOREM
1 for `notProofFast`**, in answer shape (`propIrrel` calls it on its two
subjects, which callers reach through `whnfCore` answers). -/
theorem notProofFast_spec' (fuel : Nat) (s₀ : AState) (a : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store a = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.notProofFast fe fuel a
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store a = some x →
        b = ConLeche.notProofFast env.find? x⌝⦄ := by
  have hb := proofPW_spec' (mode := mode) (env := env) (fe := fe) fuel s₀ a
    hok hpre
  mvcgen [ConRon.Arena.notProofFast, hb]
  all_goals (bridge_peel; subst_vars)
  all_goals
    (rename_i hr
     refine ⟨‹_›, ‹_›, ‹_›, fun x hx => ?_⟩
     simp only [ConLeche.notProofFast, ← hr x hx])

/-- con-leche: ConLeche/Kernel/PropRead.lean:141-146 notProofFast — published
shape. -/
theorem notProofFast_spec (fuel : Nat) (s₀ : AState) (a : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store a = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.notProofFast fe fuel a
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.notProofFast env.find? x⌝⦄ := by
  have hb := notProofFast_spec' (mode := mode) (env := env) (fe := fe) fuel s₀
    a hok ⟨x, hden⟩
  mvcgen [hb]
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4 x hden⟩

/-- con-leche: ConLeche/Kernel/PropRead.lean:148-153 isProofFast — **THEOREM
1 for `isProofFast`**, in answer shape. -/
theorem isProofFast_spec' (fuel : Nat) (s₀ : AState) (a : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store a = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.isProofFast fe fuel a
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store a = some x →
        b = ConLeche.isProofFast env.find? x⌝⦄ := by
  have hb := proofPW_spec' (mode := mode) (env := env) (fe := fe) fuel s₀ a
    hok hpre
  mvcgen [ConRon.Arena.isProofFast, hb]
  all_goals (bridge_peel; subst_vars)
  all_goals
    (rename_i hr
     refine ⟨‹_›, ‹_›, ‹_›, fun x hx => ?_⟩
     simp only [ConLeche.isProofFast, ← hr x hx])

/-- con-leche: ConLeche/Kernel/PropRead.lean:148-153 isProofFast — published
shape. -/
theorem isProofFast_spec (fuel : Nat) (s₀ : AState) (a : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store a = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.isProofFast fe fuel a
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.isProofFast env.find? x⌝⦄ := by
  have hb := isProofFast_spec' (mode := mode) (env := env) (fe := fe) fuel s₀
    a hok ⟨x, hden⟩
  mvcgen [hb]
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4 x hden⟩

/-! ## 5. The three walks that waited on the readers

`Walks/Owed.lean`'s `annotPwPi`, `annotPwLam` and `propIrrel`, moved here
(round 5): each is a reader of §3–4 first and the knot's answer-shape slots
(`Bridge/Core/Knot.lean`) after, and the `ensureSort` in the annotation pair
is why they cannot sit in `Owed.lean` (`Walks/Spine.lean`'s module note). -/

/-! ### The pure sides at their exits -/

/-- con-leche: ConLeche/Kernel/Core.lean:1746-1777 annotPwPi — the reader
answers, at any fuel. -/
theorem annotPwPi_fast {F d : Nat} {x : Expr} {pw : PropWhen}
    (h : ConLeche.typeSortPW env.find? x = some pw) :
    ConLeche.annotPwPi (ConLeche.pureFns mode env F) env d x = .ok pw := by
  simp only [ConLeche.annotPwPi, h, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1746-1777 annotPwPi — the reader
declines: one io inference and a sort. -/
theorem annotPwPi_of_steps {F d : Nat} {x ti : Expr} {l : Level}
    (h0 : ConLeche.typeSortPW env.find? x = none)
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ti)
    (h2 : ConLeche.whnf mode env F d ti = .ok (.sort l)) :
    ConLeche.annotPwPi (ConLeche.pureFns mode env F) env d x =
      .ok (Level.zeronessOf l) := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ti := h1
  have e2 : (ConLeche.pureFns mode env F).whnf d ti = .ok (.sort l) := h2
  simp only [ConLeche.annotPwPi, ConLeche.ensureSort, h0, e1, e2, bind,
    Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1779-1793 annotPwLam — the reader
answers, at any fuel. -/
theorem annotPwLam_fast {F d : Nat} {x : Expr} {pw : PropWhen}
    (h : ConLeche.proofPW env.find? x = some pw) :
    ConLeche.annotPwLam (ConLeche.pureFns mode env F) env d x = .ok pw := by
  simp only [ConLeche.annotPwLam, h, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1779-1793 annotPwLam — the reader
declines: two io inferences and a sort. -/
theorem annotPwLam_of_steps {F d : Nat} {x bt btt : Expr} {l : Level}
    (h0 : ConLeche.proofPW env.find? x = none)
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok bt)
    (h2 : ConLeche.inferTypeIO mode env F d bt = .ok btt)
    (h3 : ConLeche.whnf mode env F d btt = .ok (.sort l)) :
    ConLeche.annotPwLam (ConLeche.pureFns mode env F) env d x =
      .ok (Level.zeronessOf l) := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok bt := h1
  have e2 : (ConLeche.pureFns mode env F).inferIO d bt = .ok btt := h2
  have e3 : (ConLeche.pureFns mode env F).whnf d btt = .ok (.sort l) := h3
  simp only [ConLeche.annotPwLam, ConLeche.ensureSort, h0, e1, e2, e3, bind,
    Except.bind, pure, Except.pure]

/-! ### `annotPwPi` and `annotPwLam` -/

/-- con-leche: ConLeche/Kernel/Core.lean:1746-1777 annotPwPi — **THEOREM 1
for `annotPwPi`**: the `PropWhen` datum a ∀ binder is stamped with.
**CLOSED** (round 5, moved from `Walks/Owed.lean`, statement unchanged):
`typeSortPW_spec'`, then — when the reader declines — `KnotSpec.inferIO'`,
`ensureSort`'s `KnotSpec.whnf'` and the level readback. -/
theorem annotPwPi_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (body' : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store body' = some x)
    (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.annotPwPi (coreKnot mode fe id fuel) fe d body'
    ⦃⇓? pw s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimVOp
          (fun F => ConLeche.annotPwPi (ConLeche.pureFns mode env F) env d x)
          pw⌝⦄ := by
  have hts := typeSortPW_spec' (mode := mode) (env := env) (fe := fe)
    coreWalkFuel s₀ body' hok ⟨x, hden⟩
  have hi := hsim.inferIO'
  have hn := hsim.whnf'
  mvcgen [ConRon.Arena.annotPwPi, ConRon.Arena.ensureSort, hts, hi, hn]
  all_goals (bridge_peel; subst_vars)
  -- the reader answers
  case vc2 =>
    rename_i s1 pw s0 hck hst hp hts'
    exact ⟨hck, by rw [hst]; exact Ext.refl _, hp, 0,
      annotPwPi_fast (hts' x hden).symm⟩
  -- the callees' preconditions
  case vc3.hok => rename_i s1 s0 hck _ _ _; exact hck
  case vc4.hdw =>
    rename_i s1 s0 _ hst _ _
    exact ⟨x, by rw [hst]; exact hden, hw⟩
  case vc5.hok => rename_i s2 s1 r s0 _ hck0 _ _ _ _ _ _; exact hck0
  case vc6.hdw =>
    rename_i s2 s1 ti s0 _ _ _ _ hsio hst _ _
    exact SimE.exists_denote (hsio x (by rw [hst]; exact hden))
  case vc7.hc =>
    rename_i s3 s2 ti s1 w u s0 _ _ _ _ _ _ _ _ hck0 _ _ _ _
    exact hck0.caches.readL
  -- the reader declines: infer, reduce to a sort, read the level back
  case vc8 =>
    rename_i s4 s3 ti s2 w u s1 l s0 hck3 hck2 hst01 hx32 hm01 hp23 hsio hp01
      hc01 hl hL hst34 hp34 hts' hck1 hview hx21 hp12 hsw
    have hf := ReadbackFrame.ofReadL hst01 hm01 hp01 hc01 hL
    have hx43 : Ext s4.store s3.store := by rw [hst34]; exact Ext.refl _
    refine ⟨CheckOK.ofReadbackFrame hck1 hf,
      ((hx43.trans hx32).trans hx21).trans hf.ext,
      hf.pins.trans (hp12.trans (hp23.trans hp34)), ?_⟩
    obtain ⟨ti', hti', _, F1, hF1⟩ := hsio x (by rw [hst34]; exact hden)
    obtain ⟨w', hw', _, F2, hF2⟩ := hsw ti' hti'
    obtain ⟨l', rfl, hl'⟩ := denote_sort_inv hck1.state.wf hview hw'
    rw [hl] at hl'; cases hl'
    exact ⟨max F1 F2, annotPwPi_of_steps (hts' x hden).symm
      (ConLeche.inferTypeIO_mono (Nat.le_max_left _ _) hF1)
      (ConLeche.whnf_mono (Nat.le_max_right _ _) hF2)⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1779-1793 annotPwLam — **THEOREM 1
for `annotPwLam`**: the same at a λ binder.  **CLOSED** (round 5, moved from
`Walks/Owed.lean`, statement unchanged): `proofPW_spec'`, then — when the
reader declines — two `KnotSpec.inferIO'`, `ensureSort`'s `KnotSpec.whnf'`
and the level readback. -/
theorem annotPwLam_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (body' : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store body' = some x)
    (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.annotPwLam (coreKnot mode fe id fuel) fe d body'
    ⦃⇓? pw s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimVOp
          (fun F => ConLeche.annotPwLam (ConLeche.pureFns mode env F) env d x)
          pw⌝⦄ := by
  have hpp := proofPW_spec' (mode := mode) (env := env) (fe := fe)
    coreWalkFuel s₀ body' hok ⟨x, hden⟩
  have hi := hsim.inferIO'
  have hn := hsim.whnf'
  mvcgen [ConRon.Arena.annotPwLam, ConRon.Arena.ensureSort, hpp, hi, hn]
  all_goals (bridge_peel; subst_vars)
  -- the reader answers
  case vc2 =>
    rename_i s1 pw s0 hck hst hp hpp'
    exact ⟨hck, by rw [hst]; exact Ext.refl _, hp, 0,
      annotPwLam_fast (hpp' x hden).symm⟩
  -- the callees' preconditions
  case vc3.hok => rename_i s1 s0 hck _ _ _; exact hck
  case vc4.hdw =>
    rename_i s1 s0 _ hst _ _
    exact ⟨x, by rw [hst]; exact hden, hw⟩
  case vc5.hok => rename_i s2 s1 r s0 _ hck0 _ _ _ _ _ _; exact hck0
  case vc6.hdw =>
    rename_i s2 s1 bt s0 _ _ _ _ hsio hst _ _
    exact SimE.exists_denote (hsio x (by rw [hst]; exact hden))
  case vc7.hok =>
    rename_i s3 s2 bt s1 btt s0 _ _ hck0 _ _ _ _ _ _ _ _ _
    exact hck0
  case vc8.hdw =>
    rename_i s3 s2 bt s1 btt s0 _ _ _ _ _ _ hsio1 _ hsio2 hst _ _
    obtain ⟨bt', hbt', _, _⟩ := hsio1 x (by rw [hst]; exact hden)
    exact SimE.exists_denote (hsio2 bt' hbt')
  case vc9.hc =>
    rename_i s4 s3 bt s2 btt s1 w u s0 _ _ _ _ _ _ _ _ _ _ _ _ hck0 _ _ _ _
    exact hck0.caches.readL
  -- the reader declines: two io inferences, a sort, the level read back
  case vc10 =>
    rename_i s5 s4 bt s3 btt s2 w u s1 l s0 hck4 hck3 hck2 hst01 hx43 hx32 hm01
      hp34 hsio1 hp23 hsio2 hp01 hc01 hl hL hst45 hp45 hpp' hck1 hview hx21
      hp12 hsw
    have hf := ReadbackFrame.ofReadL hst01 hm01 hp01 hc01 hL
    have hx54 : Ext s5.store s4.store := by rw [hst45]; exact Ext.refl _
    refine ⟨CheckOK.ofReadbackFrame hck1 hf,
      (((hx54.trans hx43).trans hx32).trans hx21).trans hf.ext,
      hf.pins.trans (hp12.trans (hp23.trans (hp34.trans hp45))), ?_⟩
    obtain ⟨bt', hbt', _, F1, hF1⟩ := hsio1 x (by rw [hst45]; exact hden)
    obtain ⟨btt', hbtt', _, F2, hF2⟩ := hsio2 bt' hbt'
    obtain ⟨w', hw', _, F3, hF3⟩ := hsw btt' hbtt'
    obtain ⟨l', rfl, hl'⟩ := denote_sort_inv hck1.state.wf hview hw'
    rw [hl] at hl'; cases hl'
    exact ⟨max F1 (max F2 F3), annotPwLam_of_steps (hpp' x hden).symm
      (ConLeche.inferTypeIO_mono (Nat.le_max_left _ _) hF1)
      (ConLeche.inferTypeIO_mono
        (Nat.le_trans (Nat.le_max_left F2 F3) (Nat.le_max_right F1 _)) hF2)
      (ConLeche.whnf_mono
        (Nat.le_trans (Nat.le_max_right F2 F3) (Nat.le_max_right F1 _)) hF3)⟩

/-! ### `propIrrel`'s pure side at its five exits -/

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — the "not a
proof" arm refuses, at any fuel. -/
theorem propIrrel_no {F d : Nat} {x y : Expr}
    (h : (ConLeche.notProofFast env.find? x ||
      ConLeche.notProofFast env.find? y) = true) :
    ConLeche.propIrrelFueled mode env F d x y = .ok false := by
  simp only [ConLeche.propIrrelFueled, ConLeche.propIrrel, h, if_true, pure,
    Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — the "yes" arm
(the squash-regime licence), at any fuel. -/
theorem propIrrel_yes {F d : Nat} {x y : Expr}
    (hn : (ConLeche.notProofFast env.find? x ||
      ConLeche.notProofFast env.find? y) = false)
    (h : (ConLeche.isProofFast env.find? x &&
      ConLeche.isProofFast env.find? y) = true) :
    ConLeche.propIrrelFueled mode env F d x y = .ok true := by
  simp only [ConLeche.propIrrelFueled, ConLeche.propIrrel, hn, h,
    Bool.false_eq_true, if_false, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — the slow path:
the first subject's type's type does not reduce to a sort. -/
theorem propIrrel_slow_a {F d : Nat} {x y ta tta w : Expr}
    (hn : (ConLeche.notProofFast env.find? x ||
      ConLeche.notProofFast env.find? y) = false)
    (hi : (ConLeche.isProofFast env.find? x &&
      ConLeche.isProofFast env.find? y) = false)
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h2 : ConLeche.inferTypeIO mode env F d ta = .ok tta)
    (h3 : ConLeche.whnf mode env F d tta = .ok w)
    (hw : ∀ l, w ≠ .sort l) :
    ConLeche.propIrrelFueled mode env F d x y = .ok false := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).inferIO d ta = .ok tta := h2
  have e3 : (ConLeche.pureFns mode env F).whnf d tta = .ok w := h3
  simp only [ConLeche.propIrrelFueled, ConLeche.propIrrel, hn, hi,
    Bool.false_eq_true, if_false, e1, e2, e3, bind, Except.bind]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — the slow path:
the first subject's side is a sort, the second's type's type does not reduce
to one. -/
theorem propIrrel_slow_b {F d : Nat} {x y ta tta tb ttb w : Expr} {uT : Level}
    {okA : Bool}
    (hn : (ConLeche.notProofFast env.find? x ||
      ConLeche.notProofFast env.find? y) = false)
    (hi : (ConLeche.isProofFast env.find? x &&
      ConLeche.isProofFast env.find? y) = false)
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h2 : ConLeche.inferTypeIO mode env F d ta = .ok tta)
    (h3 : ConLeche.whnf mode env F d tta = .ok (.sort uT))
    (h4 : Level.isEquiv uT Level.zero = some okA)
    (h5 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h6 : ConLeche.inferTypeIO mode env F d tb = .ok ttb)
    (h7 : ConLeche.whnf mode env F d ttb = .ok w)
    (hw : ∀ l, w ≠ .sort l) :
    ConLeche.propIrrelFueled mode env F d x y = .ok false := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).inferIO d ta = .ok tta := h2
  have e3 : (ConLeche.pureFns mode env F).whnf d tta = .ok (.sort uT) := h3
  have e5 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h5
  have e6 : (ConLeche.pureFns mode env F).inferIO d tb = .ok ttb := h6
  have e7 : (ConLeche.pureFns mode env F).whnf d ttb = .ok w := h7
  simp only [ConLeche.propIrrelFueled, ConLeche.propIrrel, hn, hi,
    Bool.false_eq_true, if_false, e1, e2, e3, e5, e6, e7, ConLeche.liftFueled,
    h4, bind, Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — the slow path
to its end: both sides are sorts, and the verdict is the two level
comparisons' conjunction. -/
theorem propIrrel_slow {F d : Nat} {x y ta tta tb ttb : Expr} {uT vT : Level}
    {okA okB : Bool}
    (hn : (ConLeche.notProofFast env.find? x ||
      ConLeche.notProofFast env.find? y) = false)
    (hi : (ConLeche.isProofFast env.find? x &&
      ConLeche.isProofFast env.find? y) = false)
    (h1 : ConLeche.inferTypeIO mode env F d x = .ok ta)
    (h2 : ConLeche.inferTypeIO mode env F d ta = .ok tta)
    (h3 : ConLeche.whnf mode env F d tta = .ok (.sort uT))
    (h4 : Level.isEquiv uT Level.zero = some okA)
    (h5 : ConLeche.inferTypeIO mode env F d y = .ok tb)
    (h6 : ConLeche.inferTypeIO mode env F d tb = .ok ttb)
    (h7 : ConLeche.whnf mode env F d ttb = .ok (.sort vT))
    (h8 : Level.isEquiv vT Level.zero = some okB) :
    ConLeche.propIrrelFueled mode env F d x y = .ok (okA && okB) := by
  have e1 : (ConLeche.pureFns mode env F).inferIO d x = .ok ta := h1
  have e2 : (ConLeche.pureFns mode env F).inferIO d ta = .ok tta := h2
  have e3 : (ConLeche.pureFns mode env F).whnf d tta = .ok (.sort uT) := h3
  have e5 : (ConLeche.pureFns mode env F).inferIO d y = .ok tb := h5
  have e6 : (ConLeche.pureFns mode env F).inferIO d tb = .ok ttb := h6
  have e7 : (ConLeche.pureFns mode env F).whnf d ttb = .ok (.sort vT) := h7
  simp only [ConLeche.propIrrelFueled, ConLeche.propIrrel, hn, hi,
    Bool.false_eq_true, if_false, e1, e2, e3, e5, e6, e7, ConLeche.liftFueled,
    h4, h8, bind, Except.bind, pure, Except.pure]

/-! ### `propIrrel` -/

/-- con-leche: none — a state whose store did not move is an extension of
the one before it; the readers' store equations feed the knot's `Ext`
chain through this. -/
theorem ext_of_store_eq {s t : AState} (h : t.store = s.store) :
    Ext s.store t.store := by
  rw [h]; exact Ext.refl _

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — **THEOREM 1 for
`propIrrel`**, the hoisted proof-irrelevance test.  **CLOSED** (round 5,
moved from `Walks/Owed.lean`, statement unchanged): the two fast arms are
`notProofFast_spec'` / `isProofFast_spec'` at both subjects — equations, so
both Bool outcomes of each guard transfer — and the slow path is
`KnotSpec.inferIO'` twice and `KnotSpec.whnf'` once per side, the zero pin
and `lvlEq?_spec`, over a six-way fuel merge. -/
theorem propIrrel_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.propIrrel (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.propIrrelFueled mode env F d x y) r⌝⦄ := by
  have hnp := fun (s : AState) (e : EIdx) =>
    notProofFast_spec' (mode := mode) (env := env) (fe := fe) coreWalkFuel s e
  have hip := fun (s : AState) (e : EIdx) =>
    isProofFast_spec' (mode := mode) (env := env) (fe := fe) coreWalkFuel s e
  have hi := hsim.inferIO'
  have hn := hsim.whnf'
  mvcgen [ConRon.Arena.propIrrel, ConRon.Arena.zeroLevel,
    ConRon.Arena.liftFueled, hnp, hip, hi, hn, lvlEq?_spec]
  all_goals (bridge_peel; subst_vars)
  -- the callees' `CheckOK` and pin preconditions
  case vc1.hok | vc3.hok | vc6.hok | vc8.hok | vc11.hok | vc13.hok | vc15.hok
    | vc21.hok | vc22.hok | vc24.hok | vc26.hok | vc31.hok => assumption
  case vc17.hp =>
    rename_i s7 r6 s6 r5 hg1 s5 r4 s4 r3 hg0 s3 r2 s2 r1 s1 r0 u0 s0 hck_s6
      hck_s5 hck_s4 hck_s3 hck_s2 hck_s1 hst_s6_s7 hst_s5_s6 hst_s4_s5
      hst_s3_s4 hx_s3_s2 hx_s2_s1 hp_s6_s7 hnp_a hp_s5_s6 hnp_b hp_s4_s5 hip_a
      hp_s3_s4 hip_b hp_s2_s3 hio_a hp_s1_s2 hio_r2 hck_s0 hvs_r0 hx_s1_s0
      hp_s0_s1 hwh_r1
    exact hck_s0.pins
  -- the two subjects' denotations, carried to the state each call runs in
  case vc2.hpre => exact ⟨x, hda⟩
  case vc4.hpre =>
    rename_i s1 r0 s0 hck_s0 hst_s0_s1 hp_s0_s1 hnp_a
    exact ⟨y, by rw [hst_s0_s1]; exact hdb⟩
  case vc7.hpre =>
    rename_i s2 r1 s1 r0 hg0 s0 hck_s1 hck_s0 hst_s1_s2 hst_s0_s1 hp_s1_s2
      hnp_a hp_s0_s1 hnp_b
    exact ⟨x, by rw [hst_s0_s1, hst_s1_s2]; exact hda⟩
  case vc9.hpre =>
    rename_i s3 r2 s2 r1 hg0 s1 r0 s0 hck_s2 hck_s1 hck_s0 hst_s2_s3 hst_s1_s2
      hst_s0_s1 hp_s2_s3 hnp_a hp_s1_s2 hnp_b hp_s0_s1 hip_a
    exact ⟨y, by rw [hst_s0_s1, hst_s1_s2, hst_s2_s3]; exact hdb⟩
  case vc12.hdw =>
    rename_i s4 r3 s3 r2 hg1 s2 r1 s1 r0 hg0 s0 hck_s3 hck_s2 hck_s1 hck_s0
      hst_s3_s4 hst_s2_s3 hst_s1_s2 hst_s0_s1 hp_s3_s4 hnp_a hp_s2_s3 hnp_b
      hp_s1_s2 hip_a hp_s0_s1 hip_b
    exact ⟨x, by rw [hst_s0_s1, hst_s1_s2, hst_s2_s3, hst_s3_s4]; exact hda,
      hwa⟩
  case vc14.hdw =>
    rename_i s5 r4 s4 r3 hg1 s3 r2 s2 r1 hg0 s1 r0 s0 hck_s4 hck_s3 hck_s2
      hck_s1 hck_s0 hst_s4_s5 hst_s3_s4 hst_s2_s3 hst_s1_s2 hx_s1_s0 hp_s4_s5
      hnp_a hp_s3_s4 hnp_b hp_s2_s3 hip_a hp_s1_s2 hip_b hp_s0_s1 hio_a
    exact SimE.exists_denote (hio_a x
      (by rw [hst_s1_s2, hst_s2_s3, hst_s3_s4, hst_s4_s5]; exact hda))
  case vc16.hdw =>
    rename_i s6 r5 s5 r4 hg1 s4 r3 s3 r2 hg0 s2 r1 s1 r0 s0 hck_s5 hck_s4
      hck_s3 hck_s2 hck_s1 hck_s0 hst_s5_s6 hst_s4_s5 hst_s3_s4 hst_s2_s3
      hx_s2_s1 hx_s1_s0 hp_s5_s6 hnp_a hp_s4_s5 hnp_b hp_s3_s4 hip_a hp_s2_s3
      hip_b hp_s1_s2 hio_a hp_s0_s1 hio_r1
    obtain ⟨ta, hta, _, _⟩ := hio_a x
      (by rw [hst_s2_s3, hst_s3_s4, hst_s4_s5, hst_s5_s6]; exact hda)
    exact SimE.exists_denote (hio_r1 ta hta)
  case vc23.hdw =>
    rename_i s8 r7 s7 r6 hg1 s6 r5 s5 r4 hg0 s4 r3 s3 r2 s2 r1 u0 r0 s1 s0 a0
      hck_s7 hck_s6 hck_s5 hck_s4 hck_s3 hck_s2 hck_s0 hst_s7_s8 hst_s6_s7
      hst_s5_s6 hst_s4_s5 hx_s4_s3 hx_s3_s2 hst_s0_s1 hp_s7_s8 hnp_a hp_s6_s7
      hnp_b hp_s5_s6 hip_a hp_s4_s5 hip_b hp_s3_s4 hio_a hp_s2_s3 hio_r3
      hp_s0_s1 hz_r0 hck_s1 hvs_r1 hx_s2_s1 hp_s1_s2 hwh_r2 heq_u0
    have hx : Ext s8.store s0.store :=
      ((((((ext_of_store_eq hst_s7_s8).trans (ext_of_store_eq hst_s6_s7)).trans
        (ext_of_store_eq hst_s5_s6)).trans (ext_of_store_eq hst_s4_s5)).trans
        ((hx_s4_s3.trans hx_s3_s2).trans hx_s2_s1)).trans
        (ext_of_store_eq hst_s0_s1))
    exact ⟨y, denote_ext hdb hx, hwb⟩
  case vc25.hdw =>
    rename_i s9 r8 s8 r7 hg1 s7 r6 s6 r5 hg0 s5 r4 s4 r3 s3 r2 u0 r1 s2 s1 a0
      r0 s0 hck_s8 hck_s7 hck_s6 hck_s5 hck_s4 hck_s3 hck_s1 hck_s0 hst_s8_s9
      hst_s7_s8 hst_s6_s7 hst_s5_s6 hx_s5_s4 hx_s4_s3 hst_s1_s2 hx_s1_s0
      hp_s8_s9 hnp_a hp_s7_s8 hnp_b hp_s6_s7 hip_a hp_s5_s6 hip_b hp_s4_s5
      hio_a hp_s3_s4 hio_r4 hp_s1_s2 hp_s0_s1 hio_b hz_r1 hck_s2 hvs_r2
      hx_s3_s2 hp_s2_s3 hwh_r3 heq_u0
    have hx : Ext s9.store s1.store :=
      ((((((ext_of_store_eq hst_s8_s9).trans (ext_of_store_eq hst_s7_s8)).trans
        (ext_of_store_eq hst_s6_s7)).trans (ext_of_store_eq hst_s5_s6)).trans
        ((hx_s5_s4.trans hx_s4_s3).trans hx_s3_s2)).trans
        (ext_of_store_eq hst_s1_s2))
    exact SimE.exists_denote (hio_b y (denote_ext hdb hx))
  case vc27.hdw =>
    rename_i s10 r9 s9 r8 hg1 s8 r7 s7 r6 hg0 s6 r5 s5 r4 s4 r3 u0 r2 s3 s2 a0
      r1 s1 r0 s0 hck_s9 hck_s8 hck_s7 hck_s6 hck_s5 hck_s4 hck_s2 hck_s1
      hck_s0 hst_s9_s10 hst_s8_s9 hst_s7_s8 hst_s6_s7 hx_s6_s5 hx_s5_s4
      hst_s2_s3 hx_s2_s1 hx_s1_s0 hp_s9_s10 hnp_a hp_s8_s9 hnp_b hp_s7_s8
      hip_a hp_s6_s7 hip_b hp_s5_s6 hio_a hp_s4_s5 hio_r5 hp_s2_s3 hp_s1_s2
      hio_b hp_s0_s1 hio_r1 hz_r2 hck_s3 hvs_r3 hx_s4_s3 hp_s3_s4 hwh_r4 heq_u0
    have hx : Ext s10.store s2.store :=
      ((((((ext_of_store_eq hst_s9_s10).trans (ext_of_store_eq hst_s8_s9)).trans
        (ext_of_store_eq hst_s7_s8)).trans (ext_of_store_eq hst_s6_s7)).trans
        ((hx_s6_s5.trans hx_s5_s4).trans hx_s4_s3)).trans
        (ext_of_store_eq hst_s2_s3))
    obtain ⟨tb, htb, _, _⟩ := hio_b y (denote_ext hdb hx)
    exact SimE.exists_denote (hio_r1 tb htb)
  -- the "not a proof" arm refuses
  case vc5 =>
    rename_i s2 r1 s1 r0 hg0 s0 hck_s1 hck_s0 hst_s1_s2 hst_s0_s1 hp_s1_s2
      hnp_a hp_s0_s1 hnp_b
    refine ⟨hck_s0, ext_of_store_eq (hst_s0_s1.trans hst_s1_s2),
      hp_s0_s1.trans hp_s1_s2, 0, propIrrel_no ?_⟩
    rw [hnp_a x hda, hnp_b y (by rw [hst_s1_s2]; exact hdb)] at hg0
    exact hg0
  -- the "yes" arm licenses
  case vc10 =>
    rename_i s4 r3 s3 r2 hg1 s2 r1 s1 r0 hg0 s0 hck_s3 hck_s2 hck_s1 hck_s0
      hst_s3_s4 hst_s2_s3 hst_s1_s2 hst_s0_s1 hp_s3_s4 hnp_a hp_s2_s3 hnp_b
      hp_s1_s2 hip_a hp_s0_s1 hip_b
    refine ⟨hck_s0, ext_of_store_eq
        (hst_s0_s1.trans (hst_s1_s2.trans (hst_s2_s3.trans hst_s3_s4))),
      hp_s0_s1.trans (hp_s1_s2.trans (hp_s2_s3.trans hp_s3_s4)), 0,
      propIrrel_yes ?_ ?_⟩
    · rw [hnp_a x hda, hnp_b y (by rw [hst_s3_s4]; exact hdb)] at hg1
      simpa using hg1
    · rw [hip_a x (by rw [hst_s2_s3, hst_s3_s4]; exact hda),
        hip_b y (by rw [hst_s1_s2, hst_s2_s3, hst_s3_s4]; exact hdb)] at hg0
      exact hg0
  -- the slow path to its end: both sides are sorts
  case vc32 =>
    rename_i s12 r10 s11 r9 hg1 s10 r8 s9 r7 hg0 s8 r6 s7 r5 s6 r4 u1 r3 s5 s4
      a1 r2 s3 r1 s2 r0 u0 s1 s0 a0 hck_s11 hck_s10 hck_s9 hck_s8 hck_s7
      hck_s6 hck_s4 hck_s3 hck_s2 hck_s0 hst_s11_s12 hst_s10_s11 hst_s9_s10
      hst_s8_s9 hx_s8_s7 hx_s7_s6 hst_s4_s5 hx_s4_s3 hx_s3_s2 hst_s0_s1
      hp_s11_s12 hnp_a hp_s10_s11 hnp_b hp_s9_s10 hip_a hp_s8_s9 hip_b hp_s7_s8
      hio_a hp_s6_s7 hio_r6 hp_s4_s5 hp_s3_s4 hio_b hp_s2_s3 hio_r2 hp_s0_s1
      hz_r3 hck_s5 hvs_r4 hx_s6_s5 hp_s5_s6 hwh_r5 heq_u1 hck_s1 hvs_r0
      hx_s2_s1 hp_s1_s2 hwh_r1 heq_u0
    have hx128 : Ext s12.store s8.store :=
      (((ext_of_store_eq hst_s11_s12).trans (ext_of_store_eq hst_s10_s11)).trans
        (ext_of_store_eq hst_s9_s10)).trans (ext_of_store_eq hst_s8_s9)
    have hx84 : Ext s8.store s4.store :=
      ((hx_s8_s7.trans hx_s7_s6).trans hx_s6_s5).trans
        (ext_of_store_eq hst_s4_s5)
    have hx40 : Ext s4.store s0.store :=
      ((hx_s4_s3.trans hx_s3_s2).trans hx_s2_s1).trans
        (ext_of_store_eq hst_s0_s1)
    refine ⟨hck_s0, (hx128.trans hx84).trans hx40,
      hp_s0_s1.trans (hp_s1_s2.trans (hp_s2_s3.trans (hp_s3_s4.trans
        (hp_s4_s5.trans (hp_s5_s6.trans (hp_s6_s7.trans (hp_s7_s8.trans
        (hp_s8_s9.trans (hp_s9_s10.trans (hp_s10_s11.trans
        hp_s11_s12)))))))))), ?_⟩
    -- the first side
    obtain ⟨ta, hta, _, F1, hF1⟩ := hio_a x (denote_ext hda hx128)
    obtain ⟨tta, htta, _, F2, hF2⟩ := hio_r6 ta hta
    obtain ⟨w, hw, _, F3, hF3⟩ := hwh_r5 tta htta
    obtain ⟨uT, rfl, huT⟩ := denote_sort_inv hck_s5.state.wf hvs_r4 hw
    obtain ⟨lu, lv, hlu, hlv, hA⟩ := heq_u1
    rw [huT] at hlu; rw [hz_r3] at hlv
    cases hlu; cases hlv
    -- the second side
    obtain ⟨tb, htb, _, F4, hF4⟩ := hio_b y (denote_ext hdb (hx128.trans hx84))
    obtain ⟨ttb, httb, _, F5, hF5⟩ := hio_r2 tb htb
    obtain ⟨w2, hw2, _, F6, hF6⟩ := hwh_r1 ttb httb
    obtain ⟨vT, rfl, hvT⟩ := denote_sort_inv hck_s1.state.wf hvs_r0 hw2
    obtain ⟨lu', lv', hlu', hlv', hB⟩ := heq_u0
    have hz1 : denoteL s1.store.ls r3 = some Level.zero :=
      denoteL_ext hz_r3 (((ext_of_store_eq hst_s4_s5).trans hx_s4_s3).trans
        (hx_s3_s2.trans hx_s2_s1))
    rw [hvT] at hlu'; rw [hz1] at hlv'
    cases hlu'; cases hlv'
    -- the two guards declined
    rw [hnp_a x hda, hnp_b y (by rw [hst_s11_s12]; exact hdb)] at hg1
    rw [hip_a x (by rw [hst_s10_s11, hst_s11_s12]; exact hda),
      hip_b y (by rw [hst_s9_s10, hst_s10_s11, hst_s11_s12]; exact hdb)] at hg0
    refine ⟨F1 + F2 + F3 + F4 + F5 + F6, propIrrel_slow (by simpa using hg1)
      (by simpa using hg0)
      (ConLeche.inferTypeIO_mono (by omega) hF1)
      (ConLeche.inferTypeIO_mono (by omega) hF2)
      (ConLeche.whnf_mono (by omega) hF3) hA.symm
      (ConLeche.inferTypeIO_mono (by omega) hF4)
      (ConLeche.inferTypeIO_mono (by omega) hF5)
      (ConLeche.whnf_mono (by omega) hF6) hB.symm⟩
  -- the second side's type's type is not a sort
  case vc34 =>
    rename_i s11 r10 s10 r9 hg1 s9 r8 s8 r7 hg0 s7 r6 s6 r5 s5 r4 u0 r3 s4 s3
      a0 r2 s2 r1 s1 r0 x1 hnv0 s0 hck_s10 hck_s9 hck_s8 hck_s7 hck_s6 hck_s5
      hck_s3 hck_s2 hck_s1 hst_s10_s11 hst_s9_s10 hst_s8_s9 hst_s7_s8 hx_s7_s6
      hx_s6_s5 hst_s3_s4 hx_s3_s2 hx_s2_s1 hp_s10_s11 hnp_a hp_s9_s10 hnp_b
      hp_s8_s9 hip_a hp_s7_s8 hip_b hp_s6_s7 hio_a hp_s5_s6 hio_r6 hp_s3_s4
      hp_s2_s3 hio_b hp_s1_s2 hio_r2 hz_r3 hck_s4 hvs_r4 hx_s5_s4 hp_s4_s5
      hwh_r5 heq_u0 hck_s0 hv_r0 hx_s1_s0 hp_s0_s1 hwh_r1
    have hx117 : Ext s11.store s7.store :=
      (((ext_of_store_eq hst_s10_s11).trans (ext_of_store_eq hst_s9_s10)).trans
        (ext_of_store_eq hst_s8_s9)).trans (ext_of_store_eq hst_s7_s8)
    have hx73 : Ext s7.store s3.store :=
      ((hx_s7_s6.trans hx_s6_s5).trans hx_s5_s4).trans
        (ext_of_store_eq hst_s3_s4)
    have hx30 : Ext s3.store s0.store :=
      (hx_s3_s2.trans hx_s2_s1).trans hx_s1_s0
    refine ⟨hck_s0, (hx117.trans hx73).trans hx30,
      hp_s0_s1.trans (hp_s1_s2.trans (hp_s2_s3.trans (hp_s3_s4.trans
        (hp_s4_s5.trans (hp_s5_s6.trans (hp_s6_s7.trans (hp_s7_s8.trans
        (hp_s8_s9.trans (hp_s9_s10.trans hp_s10_s11))))))))), ?_⟩
    obtain ⟨ta, hta, _, F1, hF1⟩ := hio_a x (denote_ext hda hx117)
    obtain ⟨tta, htta, _, F2, hF2⟩ := hio_r6 ta hta
    obtain ⟨w, hw, _, F3, hF3⟩ := hwh_r5 tta htta
    obtain ⟨uT, rfl, huT⟩ := denote_sort_inv hck_s4.state.wf hvs_r4 hw
    obtain ⟨lu, lv, hlu, hlv, hA⟩ := heq_u0
    rw [huT] at hlu; rw [hz_r3] at hlv
    cases hlu; cases hlv
    obtain ⟨tb, htb, _, F4, hF4⟩ := hio_b y (denote_ext hdb (hx117.trans hx73))
    obtain ⟨ttb, httb, _, F5, hF5⟩ := hio_r2 tb htb
    obtain ⟨w2, hw2, _, F6, hF6⟩ := hwh_r1 ttb httb
    have hns := denote_not_sort hck_s0.state.wf hv_r0 hw2 hnv0
    rw [hnp_a x hda, hnp_b y (by rw [hst_s10_s11]; exact hdb)] at hg1
    rw [hip_a x (by rw [hst_s9_s10, hst_s10_s11]; exact hda),
      hip_b y (by rw [hst_s8_s9, hst_s9_s10, hst_s10_s11]; exact hdb)] at hg0
    exact ⟨F1 + F2 + F3 + F4 + F5 + F6, propIrrel_slow_b (by simpa using hg1)
      (by simpa using hg0)
      (ConLeche.inferTypeIO_mono (by omega) hF1)
      (ConLeche.inferTypeIO_mono (by omega) hF2)
      (ConLeche.whnf_mono (by omega) hF3) hA.symm
      (ConLeche.inferTypeIO_mono (by omega) hF4)
      (ConLeche.inferTypeIO_mono (by omega) hF5)
      (ConLeche.whnf_mono (by omega) hF6) hns⟩
  -- the first side's type's type is not a sort
  case vc48 =>
    rename_i s7 r6 s6 r5 hg1 s5 r4 s4 r3 hg0 s3 r2 s2 r1 s1 r0 x1 hnv0 s0
      hck_s6 hck_s5 hck_s4 hck_s3 hck_s2 hck_s1 hst_s6_s7 hst_s5_s6 hst_s4_s5
      hst_s3_s4 hx_s3_s2 hx_s2_s1 hp_s6_s7 hnp_a hp_s5_s6 hnp_b hp_s4_s5 hip_a
      hp_s3_s4 hip_b hp_s2_s3 hio_a hp_s1_s2 hio_r2 hck_s0 hv_r0 hx_s1_s0
      hp_s0_s1 hwh_r1
    have hx73 : Ext s7.store s3.store :=
      (((ext_of_store_eq hst_s6_s7).trans (ext_of_store_eq hst_s5_s6)).trans
        (ext_of_store_eq hst_s4_s5)).trans (ext_of_store_eq hst_s3_s4)
    refine ⟨hck_s0, hx73.trans ((hx_s3_s2.trans hx_s2_s1).trans hx_s1_s0),
      hp_s0_s1.trans (hp_s1_s2.trans (hp_s2_s3.trans (hp_s3_s4.trans
        (hp_s4_s5.trans (hp_s5_s6.trans hp_s6_s7))))), ?_⟩
    obtain ⟨ta, hta, _, F1, hF1⟩ := hio_a x (denote_ext hda hx73)
    obtain ⟨tta, htta, _, F2, hF2⟩ := hio_r2 ta hta
    obtain ⟨w, hw, _, F3, hF3⟩ := hwh_r1 tta htta
    have hns := denote_not_sort hck_s0.state.wf hv_r0 hw hnv0
    rw [hnp_a x hda, hnp_b y (by rw [hst_s6_s7]; exact hdb)] at hg1
    rw [hip_a x (by rw [hst_s5_s6, hst_s6_s7]; exact hda),
      hip_b y (by rw [hst_s4_s5, hst_s5_s6, hst_s6_s7]; exact hdb)] at hg0
    exact ⟨F1 + F2 + F3, propIrrel_slow_a (by simpa using hg1)
      (by simpa using hg0)
      (ConLeche.inferTypeIO_mono (by omega) hF1)
      (ConLeche.inferTypeIO_mono (by omega) hF2)
      (ConLeche.whnf_mono (by omega) hF3) hns⟩

/-! ### The three in ANSWER shape

`annotateBody`'s binder arms reach `annotPwPi` / `annotPwLam` through the
knot's `annotate` answer, and `defeqStep` reaches `propIrrel` through
`whnfCore` answers, so by round 3's rule each subject's denotation goes in as
an existential and comes out as a universal.  Four lines each over the
published statements. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1746-1777 annotPwPi — answer
shape. -/
theorem annotPwPi_spec' {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (body' : EIdx) (hok : CheckOK mode env fe s₀)
    (hdw : ∃ x, denoteE s₀.store body' = some x ∧ Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.annotPwPi (coreKnot mode fe id fuel) fe d body'
    ⦃⇓? pw s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store body' = some x →
        SimVOp
          (fun F => ConLeche.annotPwPi (ConLeche.pureFns mode env F) env d x)
          pw⌝⦄ := by
  obtain ⟨x, hx, hw⟩ := hdw
  have hb := annotPwPi_spec hsim s₀ d body' x hok hx hw
  mvcgen [hb]
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, fun x' hx' => by
    obtain rfl := Option.some.inj (hx'.symm.trans hx); exact h4⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1779-1793 annotPwLam — answer
shape. -/
theorem annotPwLam_spec' {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (body' : EIdx) (hok : CheckOK mode env fe s₀)
    (hdw : ∃ x, denoteE s₀.store body' = some x ∧ Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.annotPwLam (coreKnot mode fe id fuel) fe d body'
    ⦃⇓? pw s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store body' = some x →
        SimVOp
          (fun F => ConLeche.annotPwLam (ConLeche.pureFns mode env F) env d x)
          pw⌝⦄ := by
  obtain ⟨x, hx, hw⟩ := hdw
  have hb := annotPwLam_spec hsim s₀ d body' x hok hx hw
  mvcgen [hb]
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, fun x' hx' => by
    obtain rfl := Option.some.inj (hx'.symm.trans hx); exact h4⟩

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — answer shape. -/
theorem propIrrel_spec' {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (hok : CheckOK mode env fe s₀)
    (hda : ∃ x, denoteE s₀.store a = some x ∧ Expr.WScoped d x)
    (hdb : ∃ y, denoteE s₀.store b = some y ∧ Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.propIrrel (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∀ x y, denoteE s₀.store a = some x →
        denoteE s₀.store b = some y →
        SimBOp (fun F => ConLeche.propIrrelFueled mode env F d x y) r⌝⦄ := by
  obtain ⟨x, hx, hwx⟩ := hda
  obtain ⟨y, hy, hwy⟩ := hdb
  have hb := propIrrel_spec hsim s₀ d a b x y hok hx hy hwx hwy
  mvcgen [hb]
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, fun x' y' hx' hy' => by
    obtain rfl := Option.some.inj (hx'.symm.trans hx)
    obtain rfl := Option.some.inj (hy'.symm.trans hy)
    exact h4⟩

/-! ## 6. The axiom census -/

section Census

#print axioms denoteCI_isTowerEntry
#print axioms toConstantVal_nt_spec
#print axioms denote_not_sort
#print axioms denote_not_lam
#print axioms denote_not_app'
#print axioms denote_not_fvar
#print axioms denoteEO_some_inv
#print axioms const_hit
#print axioms headTypePW_const_hit
#print axioms headProofPW_const_hit
#print axioms substPW_cutoff
/-! **The nine readers**, answer shape then published shape. -/
#print axioms peelNeverPis_spec'
#print axioms peelNeverPis_spec
#print axioms numArgs_spec'
#print axioms numArgs_spec
#print axioms residualPW_spec'
#print axioms residualPW_spec
#print axioms headTypePW_spec'
#print axioms headTypePW_spec
#print axioms typeSortPW_spec'
#print axioms typeSortPW_spec
#print axioms headProofPW_spec'
#print axioms headProofPW_spec
#print axioms proofPW_spec'
#print axioms proofPW_spec
#print axioms notProofFast_spec'
#print axioms notProofFast_spec
#print axioms isProofFast_spec'
#print axioms isProofFast_spec
/-! **The three walks that waited on them.** -/
#print axioms annotPwPi_of_steps
#print axioms annotPwLam_of_steps
#print axioms propIrrel_slow
#print axioms annotPwPi_spec
#print axioms annotPwPi_spec'
#print axioms annotPwLam_spec
#print axioms annotPwLam_spec'
#print axioms propIrrel_spec
#print axioms propIrrel_spec'

end Census

end ConRon.Bridge.Core

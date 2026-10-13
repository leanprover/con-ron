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
import ConRon.Bridge.Core.Walks.Proj
import ConRon.Bridge.Frame

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

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
    ⦃fun s => s = s₀⦄ ci.toConstantVal
    ⦃fun v s' => s' = s₀ ∧ ∀ c, Frontend.denoteCI s₀.store ci = some c →
        Frontend.denoteCV s₀.store v = some c.toConstantVal; ⊤⦄ := by
  cases ci with
  | projInfo t => simp [IConstantInfo.isTowerEntry] at ht
  | axiomInfo v =>
    vcgen [IConstantInfo.toConstantVal]
    bridge_peel; subst_vars
    refine ⟨rfl, fun c hc => ?_⟩
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc
    obtain ⟨cv, hcv, rfl⟩ := hc; exact hcv
  | ctorInfo v nP nF =>
    vcgen [IConstantInfo.toConstantVal]
    bridge_peel; subst_vars
    refine ⟨rfl, fun c hc => ?_⟩
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc
    obtain ⟨cv, hcv, rfl⟩ := hc; exact hcv
  | defnInfo v e hint =>
    vcgen [IConstantInfo.toConstantVal]
    bridge_peel; subst_vars
    refine ⟨rfl, fun c hc => ?_⟩
    obtain ⟨cv, x, hcv, _, rfl⟩ := denoteCI_defnInfo_inv hc; exact hcv
  | thmInfo v =>
    vcgen [IConstantInfo.toConstantVal]
    bridge_peel; subst_vars
    refine ⟨rfl, fun c hc => ?_⟩
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc
    obtain ⟨cv, hcv, rfl⟩ := hc; exact hcv
  | indInfo v caps =>
    vcgen [IConstantInfo.toConstantVal]
    bridge_peel; subst_vars
    refine ⟨rfl, fun c hc => ?_⟩
    simp only [Frontend.denoteCI] at hc
    split at hc
    · rename_i cv x hcv _; cases hc; exact hcv
    · simp at hc
  | recInfo v mI rP rs =>
    vcgen [IConstantInfo.toConstantVal]
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
  | lam ty b => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; simp
  | forallE ty b =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv he; simp
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv he; simp
  | lit l => rw [denote_lit_inv hwf hv he]; simp
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv he; simp

/-- con-leche: none — a handle whose view is not a `.lam` denotes no λ. -/
theorem denote_not_lam {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} {v : ENodeView} (hv : st.view h = some v)
    (he : denoteE st h = some e)
    (hne : ∀ ty b, v = .lam ty b → False) : ∀ p q, e ≠ .lam p q := by
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv he]; simp
  | fvar k t => obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv he; simp
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv he; simp
  | const n us => obtain ⟨_, _, rfl, _, _⟩ := denote_const_inv hwf hv he; simp
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv he; simp
  | lam ty b => exact absurd rfl (hne ty b)
  | forallE ty b =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv he; simp
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv he; simp
  | lit l => rw [denote_lit_inv hwf hv he]; simp
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv he; simp

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the constant arm's index
hit**, in the shape the forward step instantiates (task #120): the name's
environment entry, the record it denotes, and its tower-ness. -/
theorem const_entry {s : AState} (hok : CheckOK mode env fe s) {I : NIdx}
    {nm : ConLeche.Name} {ci : IConstantInfo} (hn : denoteN s.store.ns I = some nm)
    (hfd : fe.find? I = some ci) :
    ∃ c, env.find? nm = some c ∧ Frontend.denoteCI s.store ci = some c ∧
      c.isTowerEntry = ci.isTowerEntry := by
  have hrel := optCI_find hok hn
  rw [hfd] at hrel
  obtain ⟨c, hci, hfind⟩ := hrel
  exact ⟨c, hfind, hci, (denoteCI_isTowerEntry hci).symm⟩

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the constant arm's index
miss. -/
theorem const_entry_none {s : AState} (hok : CheckOK mode env fe s) {I : NIdx}
    {nm : ConLeche.Name} (hn : denoteN s.store.ns I = some nm)
    (hfd : fe.find? I = none) : env.find? nm = none := by
  have hrel := optCI_find hok hn
  rw [hfd] at hrel
  exact hrel

/-- con-leche: none — the level-list LENGTH the twin read off a denoting
handle is the denotation's. -/
theorem viewLen_eq {st : EStore} {us : LsIdx} {a : Nat} {ls : List Level}
    (h : some a = st.lss.viewLen us) (hd : denoteLs st.lss us = some ls) :
    a = ls.length := by
  rw [viewLen_of_denoteLs hd] at h; exact Option.some.inj h

/-- con-leche: ConLeche/Kernel/PropRead.lean:107-131 headTypePW — a head that
is not a constant, an fvar or a `bvar` reads nothing. -/
theorem headTypePW_other {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {v : ENodeView} {x : Expr} (hv : st.view h = some v) (hx : denoteE st h = some x)
    (h1 : ∀ I us, v ≠ .const I us) (h2 : ∀ k ty, v ≠ .fvar k ty)
    (h3 : ∀ i, v ≠ .bvar i) :
    ∀ (f : ConLeche.Name → Option ConstantInfo) (r : Expr) (d n : Nat),
      ConLeche.headTypePW f r d x n = none := by
  intro f r d n
  cases v with
  | const I us => exact absurd rfl (h1 I us)
  | fvar k ty => exact absurd rfl (h2 k ty)
  | bvar i => exact absurd rfl (h3 i)
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv hx; rfl
  | lit l => rw [denote_lit_inv hwf hv hx]; rfl
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv hx; rfl
  | lam ty b => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv hx; rfl
  | forallE ty b => obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv hx; rfl
  | letE ty w b => obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv hx; rfl
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv hx; rfl

/-! ### con-leche's two head readers at their exits -/

/-- con-leche: ConLeche/Kernel/Level.lean:203-205 Level.substPW — **the
cutoff** of the arena's `substPWAt` (task #97-P6-10): a datum that names no
parameter (`never`, or `ifAllZero []`) is its own substitution, so answering
`pw` without the two readbacks is con-leche's `map`. -/
theorem substPW_cutoff {ks : List ConLeche.Name} {vs : List Level}
    {pw : PropWhen} (h : ∀ a as, pw ≠ .ifAllZero (a :: as)) :
    Level.substPW ks vs pw = pw := by
  cases pw with
  | never => rfl
  | ifAllZero ps =>
    cases ps with
    | nil => rfl
    | cons a as => exact absurd rfl (h a as)

/-- con-leche: none — **a `pure` exit** at a pinned state. -/
theorem triple_pureR {α : Type} {s₀ : AState} {v : α}
    {Q : α → AState → Prop} (h : Q v s₀) :
    ⦃fun s => s = s₀⦄ (pure v : AM α) ⦃fun r s => Q r s; ⊤⦄ := by
  vcgen
  subst_vars; exact h

/-- con-leche: none — the head-NAME projection of a `const` node, against
`view`. -/
theorem view_of_viewConstName {st : EStore} {i : EIdx} {n : NIdx}
    (htg : i.tag = ETag.const) (h : st.viewConstName i = some n) :
    ∃ us, st.view i = some (.const n us) := by
  have key : ∀ t : ETables, t.getConstName i = some n →
      ∃ us, t.get i = some (.const n us) := by
    intro t ht
    simp only [ETables.getConstName, Option.map_eq_some_iff] at ht
    obtain ⟨r, hr, rfl⟩ := ht
    exact ⟨r.us, ETables.get_of_getConst htg (by simp [ETables.getConst, hr])⟩
  simp only [EStore.viewConstName, EStore.persGetConstName] at h
  simp only [EStore.view]
  by_cases hp : i.isPersistent = true
  · rw [ite_eq_left hp] at h ⊢; exact key _ h
  · simp only [Bool.not_eq_true] at hp
    rw [hp] at h ⊢
    simp only [Bool.false_eq_true, ite_false] at h ⊢
    by_cases hon : st.scratchOn = true
    · rw [ite_eq_left hon] at h ⊢; exact key _ h
    · simp only [Bool.not_eq_true] at hon
      rw [hon] at h; simp at h

/-- con-leche: none — `viewConstName` reads the store and moves nothing. -/
theorem viewConstName_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => s = s₀⦄ viewConstName h
    ⦃fun r s' => s' = s₀ ∧ r = s₀.store.viewConstName h; ⊤⦄ := by
  vcgen [viewConstName] with finish

/-- con-leche: none — a denoting handle list read at an index with a
denoting default. -/
theorem denoteEList_getD {st : EStore} :
    ∀ {hs : List EIdx} {xs : List Expr}, Frontend.denoteEList st hs = some xs →
      ∀ (i : Nat) (e : EIdx) (x : Expr), denoteE st e = some x →
        denoteE st (hs.getD i e) = some (xs.getD i x)
  | [], xs, h, i, e, x, hx => by rw [denoteEList_nil_inv h]; simpa using hx
  | a :: as, xs, h, i, e, x, hx => by
    obtain ⟨y, ys, hy, hys, rfl⟩ := denoteEList_cons_inv h
    cases i with
    | zero => simpa using hy
    | succ i => simpa using denoteEList_getD hys i e x hx

/-- con-leche: none — the `else` arm of a tag-first twin (task #97-P5-Core
round 6): a denoting handle whose tag is not `t` views to a node that is not a
`t` node. -/
theorem view_not_of_tagB {st : EStore} {h : EIdx} {e : Expr}
    (he : denoteE st h = some e) {t : UInt32} (ht : ¬ (h.tag == t) = true) :
    ∃ v, st.view h = some v ∧ v.tagOf ≠ t := by
  obtain ⟨v, hv⟩ := denoteE_view he
  exact ⟨v, hv, view_tagOf_ne hv ht⟩

/-! ## 2. The view-only readers

`peelPis` is `Walks/Proj.lean`'s `peelPis_spec` (the recursor's and the
projection certificate's arity read it too). -/

/-- con-leche: ConLeche/Kernel/PropRead.lean:50-54 Expr.binderDom — **THEOREM
1 for `binderDom`**, in answer shape.  Read-only, structural on `k`. -/
theorem binderDom_spec' (k : Nat) : ∀ (s₀ : AState) (h : EIdx),
    CheckOK mode env fe s₀ →
    ⦃fun s => s = s₀⦄ ConRon.Arena.binderDom k h
    ⦃fun r s' => s' = s₀ ∧ ∀ x, denoteE s₀.store h = some x →
        denoteEO s₀.store r = some (x.binderDom k); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ h hok
    vcgen [ConRon.Arena.binderDom]
    all_goals (bridge_peel; subst_vars)
    bridge_auto [view_of_viewBind_forallE'] unfolding [Expr.binderDom, denoteEO,
      Option.map_some]
  | succ k ih =>
    intro s₀ h hok
    vcgen [ConRon.Arena.binderDom, ih]
    all_goals (bridge_peel; subst_vars)
    bridge_auto [view_of_viewBind_forallE'] unfolding [Expr.binderDom, denoteEO,
      Option.map_some]

/-- con-leche: ConLeche/Kernel/PropRead.lean:58-61 Expr.numArgs — **THEOREM 1
for `numArgs`**, in answer shape.  The arena's walk is fueled and FAILS at
fuel `0`; `; ⊤` claims nothing of a failure, so the equation is unconditional
on success. -/
theorem numArgs_spec' (fuel : Nat) : ∀ (s₀ : AState) (h : EIdx),
    CheckOK mode env fe s₀ → (∃ x, denoteE s₀.store h = some x) →
    ⦃fun s => s = s₀⦄ ConRon.Arena.numArgs fuel h
    ⦃fun n s' => s' = s₀ ∧ ∀ x, denoteE s₀.store h = some x →
        n = x.numArgs; ⊤⦄ := by
  induction fuel with
  | zero =>
    intro s₀ h _ _
    vcgen [ConRon.Arena.numArgs]
  | succ fuel ih =>
    intro s₀ h hok hpre
    obtain ⟨x₀, hx₀⟩ := hpre
    vcgen [ConRon.Arena.numArgs, ih]
    all_goals (bridge_peel; subst_vars)
    bridge_auto unfolding [Expr.numArgs]

/-- con-leche: ConLeche/Kernel/PropRead.lean:65-71 residualPW — **THEOREM 1
for `residualPW`**, in answer shape (the residual is `peelNeverPis`'s
answer).  The level is read back with `readLevel`, which leaves the state
alone. -/
theorem residualPW_spec' (s₀ : AState) (r : Option EIdx)
    (hok : CheckOK mode env fe s₀) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.residualPW r
    ⦃fun pw s' => s' = s₀ ∧ ∀ ox, denoteEO s₀.store r = some ox →
        ConLeche.residualPW ox = pw; ⊤⦄ := by
  vcgen [ConRon.Arena.residualPW]
  all_goals (bridge_peel; subst_vars)
  bridge_auto unfolding [ConLeche.residualPW]

/-! ## 2b. The identity-like wrappers (con-leche's task #342) -/

/-- con-leche: none — `view_of_viewBind_lam` at the twin's tag test and in
`vcgen`'s orientation (task #120). -/
theorem view_of_viewBind_lam' {st : EStore} {i ty b : EIdx}
    (htg : (i.tag == ETag.lam) = true) (h : some (ty, b) = st.viewBind i) :
    st.view i = some (.lam ty b) :=
  view_of_viewBind_lam (by simpa using htg) h.symm

/-- con-leche: ConLeche/Kernel/PropRead.lean:73-79 lamProj? — **THEOREM 1 for
`lamProj?`**.  Read-only; the arena's walk is fueled and fails at fuel `0`. -/
theorem lamProj?_spec' (fuel : Nat) : ∀ (k : Nat) (s₀ : AState) (h : EIdx),
    CheckOK mode env fe s₀ →
    ⦃fun s => s = s₀⦄ ConRon.Arena.lamProj? fuel k h
    ⦃fun r s' => s' = s₀ ∧ ∀ x, denoteE s₀.store h = some x →
        ConLeche.lamProj? k x = r; ⊤⦄ := by
  induction fuel with
  | zero =>
    intro k s₀ h _
    rw [ConRon.Arena.lamProj?]
    exact triple_fail
  | succ fuel ih =>
    intro k s₀ h hok
    vcgen [ConRon.Arena.lamProj?, ih]
    all_goals (bridge_peel; subst_vars)
    bridge_auto [view_of_viewBind_lam', denote_bvar_inv] unfolding [ConLeche.lamProj?]

/-- con-leche: none — `view_of_viewConstName` at the twin's tag test and in
`vcgen`'s orientation (task #120: a forward rule for `bridge_auto`). -/
theorem view_of_viewConstName' {st : EStore} {i : EIdx} {n : NIdx}
    (htg : (i.tag == ETag.const) = true) (h : some n = st.viewConstName i) :
    ∃ us, st.view i = some (.const n us) :=
  view_of_viewConstName (by simpa using htg) h.symm

/-- con-leche: none — `denoteEList_getD` with the index universal, so that a
forward step can state it once for every index. -/
theorem denoteEList_getD' {st : EStore} {hs : List EIdx} {xs : List Expr}
    {e : EIdx} {x : Expr} (h : Frontend.denoteEList st hs = some xs)
    (hx : denoteE st e = some x) :
    ∀ i, denoteE st (hs.getD i e) = some (xs.getD i x) :=
  fun i => denoteEList_getD h i e x hx

/-- con-leche: ConLeche/Kernel/PropRead.lean:81-97 unwrapIdDefs — the head is
not a constant: nothing to unwrap. -/
theorem unwrapIdDefs_not_const {find? : ConLeche.Name → Option ConstantInfo}
    {n : Nat} {x : Expr} (h : ∀ c us, x.getAppFn ≠ .const c us) :
    ConLeche.unwrapIdDefs find? (n + 1) x = x := by
  rw [ConLeche.unwrapIdDefs]
  split
  next c us heq => exact absurd heq (h c us)
  next => rfl

/-- con-leche: ConLeche/Kernel/PropRead.lean:81-97 unwrapIdDefs — the head
constant is not a stored definition. -/
theorem unwrapIdDefs_not_defn {find? : ConLeche.Name → Option ConstantInfo}
    {n : Nat} {x : Expr} {nm : ConLeche.Name} {ls : List Level}
    (hgf : x.getAppFn = .const nm ls)
    (h : ∀ cv val hint, find? nm ≠ some (.defnInfo cv val hint)) :
    ConLeche.unwrapIdDefs find? (n + 1) x = x := by
  rw [ConLeche.unwrapIdDefs, hgf]
  dsimp only
  split
  next cv v hint heq => exact absurd heq (h cv v hint)
  next => rfl

/-- con-leche: ConLeche/Kernel/PropRead.lean:81-97 unwrapIdDefs — **THEOREM
1 for `unwrapIdDefs`**, in answer shape: the answer denotes con-leche's
unwrapping at the environment's lookup. -/
theorem unwrapIdDefs_spec' (fuel : Nat) : ∀ (n : Nat) (s₀ : AState) (e : EIdx),
    CheckOK mode env fe s₀ → (∃ x, denoteE s₀.store e = some x) →
    ⦃fun s => s = s₀⦄ ConRon.Arena.unwrapIdDefs fe fuel n e
    ⦃fun r s' => s' = s₀ ∧ ∀ x, denoteE s₀.store e = some x →
        denoteE s₀.store r = some (ConLeche.unwrapIdDefs env.find? n x); ⊤⦄ := by
  intro n
  induction n with
  | zero =>
    intro s₀ e _ _
    rw [ConRon.Arena.unwrapIdDefs]
    exact triple_pureR ⟨rfl, fun x hx => by rw [hx]; rfl⟩
  | succ n ih =>
    intro s₀ e hok hpre
    obtain ⟨x₀, hx₀⟩ := hpre
    vcgen [ConRon.Arena.unwrapIdDefs, ExprOps.getAppFn_spec fuel, viewConstName_spec,
      lamProj?_spec' (mode := mode) (env := env) (fe := fe) fuel,
      ExprOps.getAppArgs_spec fuel, ih]
    all_goals (bridge_peel; subst_vars)
    bridge_auto [view_of_viewConstName', denote_const_inv, denoteEList_getD', env_defn_of_index,
      env_not_defn_of_index, denote_not_const_of_tag, denoteEList_len]
      unfolding [ConLeche.unwrapIdDefs, unwrapIdDefs_not_const, unwrapIdDefs_not_defn,
        ite_true, ite_false, Bool.false_eq_true]

/-- con-leche: ConLeche/Kernel/PropRead.lean:99-105 peelPisW — not a `∀`
itself, but a `∀` once its identity-like wrappers are unwrapped (task #120:
the step as a rewrite rule for `bridge_auto`). -/
theorem peelPisW_succ_unwrap {f : ConLeche.Name → Option ConstantInfo} {k : Nat}
    {x : Expr} (ht : (exprTag x == ETag.forallE) = true → False)
    (_hu : (exprTag (ConLeche.unwrapIdDefs f 4 x) == ETag.forallE) = true) :
    ConLeche.peelPisW f (k + 1) x =
      match ConLeche.unwrapIdDefs f 4 x with
      | .forallE _ b => ConLeche.peelPisW f k b
      | _ => none := by
  cases x <;> first | (exact absurd rfl ht) | rfl

/-- con-leche: ConLeche/Kernel/PropRead.lean:99-105 peelPisW — no `∀`
either way: no peel. -/
theorem peelPisW_succ_none {f : ConLeche.Name → Option ConstantInfo} {k : Nat}
    {x : Expr} (ht : (exprTag x == ETag.forallE) = true → False)
    (hu : (exprTag (ConLeche.unwrapIdDefs f 4 x) == ETag.forallE) = true → False) :
    ConLeche.peelPisW f (k + 1) x = none := by
  cases x <;> first | (exact absurd rfl ht) | skip
  all_goals
    simp only [ConLeche.peelPisW]
    split <;> first | rfl | (next h => rw [h] at hu; exact absurd rfl hu)

/-- con-leche: ConLeche/Kernel/PropRead.lean:99-105 peelPisW — **THEOREM 1
for `peelPisW`**, in answer shape. -/
theorem peelPisW_spec' (fuel : Nat) : ∀ (k : Nat) (s₀ : AState) (e : EIdx),
    CheckOK mode env fe s₀ → (∃ x, denoteE s₀.store e = some x) →
    ⦃fun s => s = s₀⦄ ConRon.Arena.peelPisW fe fuel k e
    ⦃fun r s' => s' = s₀ ∧ ∀ x, denoteE s₀.store e = some x →
        denoteEO s₀.store r = some (ConLeche.peelPisW env.find? k x); ⊤⦄ := by
  intro k
  induction k with
  | zero =>
    intro s₀ e hok hpre
    obtain ⟨x₀, hx₀⟩ := hpre
    vcgen [ConRon.Arena.peelPisW, unwrapIdDefs_spec' (mode := mode) (env := env) (fe := fe)]
    all_goals (bridge_peel; subst_vars)
    bridge_auto unfolding [ConLeche.peelPisW, denoteEO, Option.map_some]
  | succ k ih =>
    intro s₀ e hok hpre
    obtain ⟨x₀, hx₀⟩ := hpre
    vcgen [ConRon.Arena.peelPisW, unwrapIdDefs_spec' (mode := mode) (env := env) (fe := fe), ih]
    all_goals (bridge_peel; subst_vars)
    bridge_auto [view_of_viewBind_forallE'] unfolding [denoteEO.eq_1, peelPisW_succ_unwrap,
      peelPisW_succ_none, ConLeche.peelPisW.eq_2, exprTag, beq_self_eq_true]

/-! ## 3. The head readers -/

/-- con-leche: ConLeche/Kernel/Level.lean substPW — **THEOREM 1 for
`substPWAt`**: `Level.substPW` at a stored constant's level parameters and a
use's universe arguments, with the cutoff hoisted over the readbacks. -/
theorem substPWAt_spec' (s₀ : AState) (lps : List NIdx) (us : LsIdx)
    (pw : PropWhen) (hok : CheckOK mode env fe s₀)
    (hks : ∃ ks, Frontend.denoteNList s₀.store.ns lps = some ks)
    (hvs : ∃ vs, denoteLs s₀.store.lss us = some vs) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.substPWAt lps us pw
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ ∀ ks vs, Frontend.denoteNList s₀.store.ns lps = some ks →
          denoteLs s₀.store.lss us = some vs → r = some (Level.substPW ks vs pw); ⊤⦄ := by
  obtain ⟨ks, hks⟩ := hks
  obtain ⟨vs, hvs⟩ := hvs
  vcgen [ConRon.Arena.substPWAt]
  all_goals (bridge_peel; subst_vars)
  bridge_auto [CheckOK.ofReadbackFrame, ReadbackFrame.ofReadN, ReadbackFrame.ofReadLs,
    CheckOK.caches, CacheOK.readN, CacheOK.readLs]
  -- no level parameter to substitute: `substPW` is the identity
  vc_arm (h : ∀ a as, _ ≠ PropWhen.ifAllZero (a :: as)) => rw [substPW_cutoff h]

/-- con-leche: ConLeche/Kernel/PropRead.lean:112-131 headTypePW — **THEOREM 1
for `headTypePW`**, in answer shape (the head is `getAppFn`'s answer; the
telescope root is the type the walk started at). -/
theorem headTypePW_spec' (fuel : Nat) (s₀ : AState) (root : EIdx) (d : Nat)
    (h : EIdx) (n : Nat) (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store h = some x)
    (hroot : ∃ rx, denoteE s₀.store root = some rx) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.headTypePW fe fuel root d h n
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ ∀ rx x, denoteE s₀.store root = some rx →
        denoteE s₀.store h = some x →
        r = ConLeche.headTypePW env.find? rx d x n; ⊤⦄ := by
  obtain ⟨x₀, hx₀⟩ := hpre
  obtain ⟨rx₀, hrx₀⟩ := hroot
  vcgen [ConRon.Arena.headTypePW, toConstantVal_nt_spec,
    peelPisW_spec' (mode := mode) (env := env) (fe := fe) fuel,
    residualPW_spec' (mode := mode) (env := env) (fe := fe),
    substPWAt_spec' (mode := mode) (env := env) (fe := fe),
    binderDom_spec' (mode := mode) (env := env) (fe := fe)]
  all_goals (bridge_peel; subst_vars)
  bridge_auto [const_entry, const_entry_none, denoteCV_inv, denote_bvar_inv,
    Bool.eq_false_of_ne_true, viewLen_eq, denoteNList_len, headTypePW_other]
    unfolding [ConLeche.headTypePW.eq_1, ConLeche.headTypePW.eq_2, ConLeche.headTypePW.eq_3,
      Option.map_some, Option.map_none, ite_true, ite_false, Bool.false_eq_true]

/-- con-leche: ConLeche/Kernel/PropRead.lean:136-140 typeSortPWGo — **THEOREM
1 for `typeSortPWGo`**, by induction on the fuel. -/
theorem typeSortPWGo_spec' (root : EIdx) (fuel : Nat) : ∀ (s₀ : AState)
    (R : EIdx) (d : Nat), CheckOK mode env fe s₀ →
    (∃ x, denoteE s₀.store R = some x) →
    (∃ rx, denoteE s₀.store root = some rx) →
    ⦃fun s => s = s₀⦄ ConRon.Arena.typeSortPWGo fe root fuel R d
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ ∀ rx x, denoteE s₀.store root = some rx →
        denoteE s₀.store R = some x →
        r = ConLeche.typeSortPWGo env.find? rx x d; ⊤⦄ := by
  induction fuel with
  | zero =>
    intro s₀ R d _ _ _
    rw [ConRon.Arena.typeSortPWGo]
    exact triple_fail
  | succ fuel ih =>
    intro s₀ R d hok hpre hroot
    obtain ⟨x₀, hx₀⟩ := hpre
    vcgen [ConRon.Arena.typeSortPWGo, ExprOps.getAppFn_spec fuel,
      numArgs_spec' (mode := mode) (env := env) (fe := fe) fuel,
      headTypePW_spec' (mode := mode) (env := env) (fe := fe) fuel, ih]
    all_goals (bridge_peel; subst_vars)
    bridge_auto [view_of_viewBind_forallE'] unfolding [ConLeche.typeSortPWGo]

/-- con-leche: ConLeche/Kernel/PropRead.lean:148-150 typeSortPW — **THEOREM 1
for `typeSortPW`**, in answer shape. -/
theorem typeSortPW_spec' (fuel : Nat) (s₀ : AState) (T : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store T = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.typeSortPW fe fuel T
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store T = some x →
        ConLeche.typeSortPW env.find? x = r; ⊤⦄ := by
  vcgen [ConRon.Arena.typeSortPW, typeSortPWGo_spec' (mode := mode) (env := env) (fe := fe)]
  all_goals (bridge_peel; subst_vars)
  bridge_auto unfolding [ConLeche.typeSortPW]

/-- con-leche: ConLeche/Kernel/FEnv.lean:91-95 FEnv.findProj? —
`IFEnv.findProj?_spec` in answer shape (task #120: the structure name's
denotation in as an existential, out as a universal, and the answer as a
`match`, so `vcgen`'s split on it hands each arm its own fact). -/
theorem findProj?_specA (s₀ : AState) (T : NIdx) (i : Nat)
    (hok : CheckOK mode env fe s₀) (hT : ∃ Tn, denoteN s₀.store.ns T = some Tn) :
    ⦃fun s => s = s₀⦄ fe.findProj? T i
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∀ Tn, denoteN s₀.store.ns T = some Tn →
          match r with
          | some e => ∃ p, denoteProjEntry s'.store e = some p ∧
              env.findProj? Tn i = some p
          | none => env.findProj? Tn i = none; ⊤⦄ := by
  obtain ⟨Tn, hTn⟩ := hT
  refine triple_mono (IFEnv.findProj?_spec s₀ T i Tn hok hTn) ?_
  rintro r s' ⟨hck, hx, _, _, hp, hsome, hnone⟩
  refine ⟨hck, hx, hp, fun Tn' hTn' => ?_⟩
  obtain rfl := Option.some.inj (hTn'.symm.trans hTn)
  cases r with
  | some e => exact hsome e rfl
  | none => exact hnone rfl

/-- con-leche: ConLeche/Kernel/PropRead.lean:156-183 headProofPW — the
projection arm through `Env.findProj?` (the table's name, the find, the
field-count test, the entry), as a rewrite rule. -/
theorem headProofPW_proj {S : ConLeche.Name} {i : Nat} {e : Expr} :
    ConLeche.headProofPW env.find? (.proj S i e) =
      match env.findProj? S i with
      | some p =>
        (match ConLeche.typeSortPW env.find? p.body with
          | some pw => if pw.isNever then some pw else none
          | none => none)
      | none => none := by
  simp only [ConLeche.headProofPW, ConLeche.Env.findProj?]
  cases hf : env.find? (ConLeche.projTableName S) with
  | none => rfl
  | some ci =>
    cases ci with
    | projInfo tbl =>
      by_cases hi : i < tbl.numFields
      · simp only [hi, ite_true]; rfl
      · simp only [hi, ite_false]
    | _ => rfl

/-- con-leche: ConLeche/Kernel/PropRead.lean:156-183 headProofPW — a head
that is none of the six read declines. -/
theorem headProofPW_other {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {v : ENodeView} {x : Expr} (hv : st.view h = some v) (hx : denoteE st h = some x)
    (h1 : ∀ c us, v ≠ .const c us) (h2 : ∀ k ty, v ≠ .fvar k ty)
    (h3 : ∀ u, v ≠ .sort u) (h4 : ∀ ty b, v ≠ .forallE ty b)
    (h5 : ∀ l, v ≠ .lit l) (h6 : ∀ S i sub, v ≠ .proj S i sub) :
    ∀ (f : ConLeche.Name → Option ConstantInfo), ConLeche.headProofPW f x = none := by
  intro f
  cases v with
  | const c us => exact absurd rfl (h1 c us)
  | fvar k ty => exact absurd rfl (h2 k ty)
  | sort u => exact absurd rfl (h3 u)
  | forallE ty b => exact absurd rfl (h4 ty b)
  | lit l => exact absurd rfl (h5 l)
  | proj S i sub => exact absurd rfl (h6 S i sub)
  | bvar i => rw [denote_bvar_inv hwf hv hx]; rfl
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv hx; rfl
  | lam ty b => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv hx; rfl
  | letE ty w b => obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv hx; rfl

/-- con-leche: ConLeche/Kernel/PropRead.lean:156-183 headProofPW — **THEOREM 1
for `headProofPW`**, in answer shape. -/
theorem headProofPW_spec' (fuel : Nat) (s₀ : AState) (h : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store h = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.headProofPW fe fuel h
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store h = some x →
        r = ConLeche.headProofPW env.find? x; ⊤⦄ := by
  obtain ⟨x₀, hx₀⟩ := hpre
  vcgen [ConRon.Arena.headProofPW, toConstantVal_nt_spec,
    typeSortPW_spec' (mode := mode) (env := env) (fe := fe) fuel,
    substPWAt_spec' (mode := mode) (env := env) (fe := fe),
    findProj?_specA (mode := mode) (env := env) (fe := fe)]
  all_goals (bridge_peel; subst_vars)
  bridge_auto [const_entry, const_entry_none, denoteCV_inv, Bool.eq_false_of_ne_true,
    viewLen_eq, denoteNList_len, headProofPW_other, denoteProjEntry_inv, denote_lit_inv]
    unfolding [ConLeche.headProofPW.eq_1, ConLeche.headProofPW.eq_2,
      ConLeche.headProofPW.eq_3, ConLeche.headProofPW.eq_4, ConLeche.headProofPW.eq_5,
      headProofPW_proj, Option.map_some, Option.map_none, ite_true, ite_false,
      Bool.false_eq_true]

/-- con-leche: ConLeche/Kernel/PropRead.lean:124-134 proofPW — **THEOREM 1
for `proofPW`**, in answer shape: `annotPwLam` calls it on the knot's
`annotate` answer, and `notProofFast` / `isProofFast` on `propIrrel`'s
subjects. -/
theorem proofPW_spec' (fuel : Nat) (s₀ : AState) (a : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store a = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.proofPW fe fuel a
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store a = some x →
        ConLeche.proofPW env.find? x = r; ⊤⦄ := by
  induction fuel generalizing s₀ a with
  | zero =>
    rw [ConRon.Arena.proofPW]
    exact triple_fail
  | succ fuel ih =>
    obtain ⟨x₀, hx₀⟩ := hpre
    vcgen [ConRon.Arena.proofPW, headProofPW_spec' (mode := mode) (env := env) (fe := fe) fuel,
      ih]
    all_goals (bridge_peel; subst_vars)
    bridge_auto [view_of_viewBind_lam'] unfolding [ConLeche.proofPW]

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
    ⦃fun s => s = s₀⦄ ConRon.Arena.notProofFast fe fuel a
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store a = some x →
        b = ConLeche.notProofFast env.find? x; ⊤⦄ := by
  vcgen [ConRon.Arena.notProofFast, proofPW_spec' (mode := mode) (env := env) (fe := fe) fuel]
  all_goals (bridge_peel; subst_vars)
  bridge_auto unfolding [ConLeche.notProofFast]

/-- con-leche: ConLeche/Kernel/PropRead.lean:148-153 isProofFast — **THEOREM
1 for `isProofFast`**, in answer shape. -/
theorem isProofFast_spec' (fuel : Nat) (s₀ : AState) (a : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store a = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.isProofFast fe fuel a
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store a = some x →
        b = ConLeche.isProofFast env.find? x; ⊤⦄ := by
  vcgen [ConRon.Arena.isProofFast, proofPW_spec' (mode := mode) (env := env) (fe := fe) fuel]
  all_goals (bridge_peel; subst_vars)
  bridge_auto unfolding [ConLeche.isProofFast]

/-! ### `propIrrel`'s pure side at its five exits -/

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — the "not a
proof" arm refuses, at any fuel. -/
theorem propIrrel_no {F d : Nat} {x y : Expr}
    (h : (ConLeche.notProofFast env.find? x ||
      ConLeche.notProofFast env.find? y) = true) :
    ConLeche.propIrrelFueled mode env F d x y = .ok false := by
  simp only [ConLeche.propIrrelFueled, ConLeche.propIrrel, h, ite_true, pure,
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
    Bool.false_eq_true, ite_false, ite_true, pure, Except.pure]

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
    Bool.false_eq_true, ite_false, e1, e2, e3, bind, Except.bind]
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
    Bool.false_eq_true, ite_false, e1, e2, e3, e5, e6, e7, ConLeche.liftFueled,
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
    Bool.false_eq_true, ite_false, e1, e2, e3, e5, e6, e7, ConLeche.liftFueled,
    h4, h8, bind, Except.bind, pure, Except.pure]

/-! ### `propIrrel` -/

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — **THEOREM 1 for
`propIrrel`**, the hoisted proof-irrelevance test.  **CLOSED** (round 5,
moved from `Walks/Owed.lean`, statement unchanged): the two fast arms are
`notProofFast_spec'` / `isProofFast_spec'` at both subjects — equations, so
both Bool outcomes of each guard transfer — and the slow path is
the `inferIO` slot twice and `KnotSpec.whnf'` once per side, the zero pin
and `lvlEq?_spec`, over a six-way fuel merge. -/
theorem propIrrel_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.propIrrel (coreKnot mode fe id fuel) fe d a b
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.propIrrelFueled mode env F d x y) r; ⊤⦄ := by
  have hwf := hok.state.wf
  unfold ConRon.Arena.propIrrel
  -- the two fast arms
  refine triple_seq (notProofFast_spec' coreWalkFuel s₀ a hok ⟨x, hda⟩) ?_
  rintro na s1 ⟨hok1, hx1, hp1, hna⟩
  refine triple_seq (notProofFast_spec' coreWalkFuel s1 b hok1
    ⟨y, denote_ext hdb hx1⟩) ?_
  rintro nb s2 ⟨hok2, hx2, hp2, hnb⟩
  have hx02 := hx1.trans hx2
  have hp02 : s2.pins = s₀.pins := hp2.trans hp1
  have hN : (na || nb) = (ConLeche.notProofFast env.find? x ||
      ConLeche.notProofFast env.find? y) := by
    rw [hna x hda, hnb y (denote_ext hdb hx1)]
  by_cases hNT : (na || nb) = true
  · rw [ite_eq_left hNT]
    exact triple_pureR ⟨hok2, hx02, hp02, 0, propIrrel_no (hN ▸ hNT)⟩
  rw [ite_eq_right hNT]
  have hNF : (ConLeche.notProofFast env.find? x ||
      ConLeche.notProofFast env.find? y) = false := by
    rw [← hN]; simpa using hNT
  refine triple_seq (isProofFast_spec' coreWalkFuel s2 a hok2
    ⟨x, denote_ext hda hx02⟩) ?_
  rintro ia s3 ⟨hok3, hx3, hp3, hia⟩
  refine triple_seq (isProofFast_spec' coreWalkFuel s3 b hok3
    ⟨y, denote_ext hdb (hx02.trans hx3)⟩) ?_
  rintro ib s4 ⟨hok4, hx4, hp4, hib⟩
  have hx04 := (hx02.trans hx3).trans hx4
  have hp04 : s4.pins = s₀.pins := hp4.trans (hp3.trans hp02)
  have hI : (ia && ib) = (ConLeche.isProofFast env.find? x &&
      ConLeche.isProofFast env.find? y) := by
    rw [hia x (denote_ext hda hx02), hib y (denote_ext hdb (hx02.trans hx3))]
  by_cases hIT : (ia && ib) = true
  · rw [ite_eq_left hIT]
    exact triple_pureR ⟨hok4, hx04, hp04, 0, propIrrel_yes hNF (hI ▸ hIT)⟩
  rw [ite_eq_right hIT]
  have hIF : (ConLeche.isProofFast env.find? x &&
      ConLeche.isProofFast env.find? y) = false := by
    rw [← hI]; simpa using hIT
  -- the slow path: the first side's type's type
  refine triple_seq (hsim.inferIO s4 d a x hok4 (denote_ext hda hx04) hwa) ?_
  rintro ta s5 ⟨hok5, hx5, hp5, vta, hvta, hwvta, F1, hF1⟩
  refine triple_seq (hsim.inferIO s5 d ta vta hok5 hvta hwvta) ?_
  rintro tta s6 ⟨hok6, hx6, hp6, vtta, hvtta, hwvtta, F2, hF2⟩
  refine triple_seq (hsim.whnf s6 d tta vtta hok6 hvtta hwvtta) ?_
  rintro hh s7 ⟨hok7, hx7, hp7, vw, hvw, _, F3, hF3⟩
  have hx07 := ((hx04.trans hx5).trans hx6).trans hx7
  have hp07 : s7.pins = s₀.pins := hp7.trans (hp6.trans (hp5.trans hp04))
  obtain ⟨vv, hvv⟩ := denoteE_view hvw
  refine tag_view_bind_triple_else hvv ?_ (fun hne => ?_)
  rotate_left
  · -- not a sort
    have hns := denote_not_sort hok7.state.wf hvv hvw
      (fun u hh => hne (by rw [hh]; rfl))
    exact triple_pureR ⟨hok7, hx07, hp07, F1 + F2 + F3, propIrrel_slow_a hNF hIF
      (ConLeche.inferTypeIO_mono (by omega) hF1)
      (ConLeche.inferTypeIO_mono (by omega) hF2)
      (ConLeche.whnf_mono (by omega) hF3) hns⟩
  cases vv
  case sort uT =>
    obtain ⟨lT, rfl, hlT⟩ := denote_sort_inv hok7.state.wf hvv hvw
    dsimp only
    unfold ConRon.Arena.zeroLevel
    refine triple_seq (pinZeroLevel_spec s7 hok7.pins) ?_
    rintro z s8 ⟨hs8, hz⟩
    subst s8
    refine triple_seq (lvlEq?_spec s7 uT z hok7) ?_
    rintro q s9 ⟨hok9, hst9, hp9, lu, lv, hlu, hlv, hq⟩
    rw [hlT] at hlu; rw [hz] at hlv
    obtain rfl := Option.some.inj hlu
    obtain rfl := Option.some.inj hlv
    cases q with
    | none =>
      simp only [ConRon.Arena.liftFueled]
      exact triple_seq (Q := fun _ _ => False) triple_fail (fun _ _ h => h.elim)
    | some okA =>
      simp only [ConRon.Arena.liftFueled, pure_bind]
      have hx09 : Ext s₀.store s9.store := hx07.trans (by rw [hst9]; exact Ext.refl _)
      have hp09 : s9.pins = s₀.pins := hp9.trans hp07
      -- the second side
      refine triple_seq (hsim.inferIO s9 d b y hok9 (denote_ext hdb hx09) hwb) ?_
      rintro tb s10 ⟨hok10, hx10, hp10, vtb, hvtb, hwvtb, F4, hF4⟩
      refine triple_seq (hsim.inferIO s10 d tb vtb hok10 hvtb hwvtb) ?_
      rintro ttb s11 ⟨hok11, hx11, hp11, vttb, hvttb, hwvttb, F5, hF5⟩
      refine triple_seq (hsim.whnf s11 d ttb vttb hok11 hvttb hwvttb) ?_
      rintro hh2 s12 ⟨hok12, hx12, hp12, vw2, hvw2, _, F6, hF6⟩
      have hx012 := ((hx09.trans hx10).trans hx11).trans hx12
      have hp012 : s12.pins = s₀.pins := hp12.trans (hp11.trans (hp10.trans hp09))
      obtain ⟨vv2, hvv2⟩ := denoteE_view hvw2
      refine tag_view_bind_triple_else hvv2 ?_ (fun hne => ?_)
      rotate_left
      · have hns := denote_not_sort hok12.state.wf hvv2 hvw2
          (fun u hh => hne (by rw [hh]; rfl))
        exact triple_pureR ⟨hok12, hx012, hp012, F1 + F2 + F3 + F4 + F5 + F6,
          propIrrel_slow_b hNF hIF
            (ConLeche.inferTypeIO_mono (by omega) hF1)
            (ConLeche.inferTypeIO_mono (by omega) hF2)
            (ConLeche.whnf_mono (by omega) hF3) hq.symm
            (ConLeche.inferTypeIO_mono (by omega) hF4)
            (ConLeche.inferTypeIO_mono (by omega) hF5)
            (ConLeche.whnf_mono (by omega) hF6) hns⟩
      cases vv2
      case sort vT =>
        obtain ⟨lV, rfl, hlV⟩ := denote_sort_inv hok12.state.wf hvv2 hvw2
        dsimp only
        refine triple_seq (pinZeroLevel_spec s12 hok12.pins) ?_
        rintro z2 s13 ⟨hs13, hz2⟩
        subst s13
        refine triple_seq (lvlEq?_spec s12 vT z2 hok12) ?_
        rintro q2 s14 ⟨hok14, hst14, hp14, lu2, lv2, hlu2, hlv2, hq2⟩
        rw [hlV] at hlu2; rw [hz2] at hlv2
        obtain rfl := Option.some.inj hlu2
        obtain rfl := Option.some.inj hlv2
        cases q2 with
        | none =>
          exact triple_seq (Q := fun _ _ => False) triple_fail (fun _ _ h => h.elim)
        | some okB =>
          simp only [pure_bind]
          exact triple_pureR ⟨hok14,
            hx012.trans (by rw [hst14]; exact Ext.refl _), hp14.trans hp012,
            F1 + F2 + F3 + F4 + F5 + F6, propIrrel_slow hNF hIF
              (ConLeche.inferTypeIO_mono (by omega) hF1)
              (ConLeche.inferTypeIO_mono (by omega) hF2)
              (ConLeche.whnf_mono (by omega) hF3) hq.symm
              (ConLeche.inferTypeIO_mono (by omega) hF4)
              (ConLeche.inferTypeIO_mono (by omega) hF5)
              (ConLeche.whnf_mono (by omega) hF6) hq2.symm⟩
      all_goals
        dsimp only
        exact triple_pureR ⟨hok12, hx012, hp012, F1 + F2 + F3 + F4 + F5 + F6,
          propIrrel_slow_b hNF hIF
            (ConLeche.inferTypeIO_mono (by omega) hF1)
            (ConLeche.inferTypeIO_mono (by omega) hF2)
            (ConLeche.whnf_mono (by omega) hF3) hq.symm
            (ConLeche.inferTypeIO_mono (by omega) hF4)
            (ConLeche.inferTypeIO_mono (by omega) hF5)
            (ConLeche.whnf_mono (by omega) hF6)
            (denote_not_sort hok12.state.wf hvv2 hvw2 (fun _ h => nomatch h))⟩
  all_goals
    dsimp only
    exact triple_pureR ⟨hok7, hx07, hp07, F1 + F2 + F3, propIrrel_slow_a hNF hIF
      (ConLeche.inferTypeIO_mono (by omega) hF1)
      (ConLeche.inferTypeIO_mono (by omega) hF2)
      (ConLeche.whnf_mono (by omega) hF3)
      (denote_not_sort hok7.state.wf hvv hvw (fun _ h => nomatch h))⟩

/-! ## 6. The axiom census -/

section Census

#print axioms denoteCI_isTowerEntry
#print axioms toConstantVal_nt_spec
#print axioms denote_not_sort
#print axioms denote_not_lam
#print axioms denoteEO_some_inv
#print axioms substPW_cutoff
/-! **The readers**, answer shape then published shape. -/
#print axioms binderDom_spec'
#print axioms numArgs_spec'
#print axioms residualPW_spec'
#print axioms lamProj?_spec'
#print axioms unwrapIdDefs_spec'
#print axioms peelPisW_spec'
#print axioms substPWAt_spec'
#print axioms headTypePW_spec'
#print axioms typeSortPWGo_spec'
#print axioms typeSortPW_spec'
#print axioms headProofPW_spec'
#print axioms proofPW_spec'
#print axioms notProofFast_spec'
#print axioms isProofFast_spec'
/-! **The walk that waited on them.** -/
#print axioms propIrrel_slow
#print axioms propIrrel_spec

end Census

end ConRon.Bridge.Core

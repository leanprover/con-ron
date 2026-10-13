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
  | lam ty b => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; simp
  | forallE ty b =>
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
  | lam ty b => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; simp
  | forallE ty b =>
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
    {root : Expr} {d : Nat}
    {nm : ConLeche.Name} {ls : List Level} {n : Nat} {c : ConstantInfo}
    (hf : find? nm = some c) (ht : c.isTowerEntry = false)
    (hl : ls.length = c.toConstantVal.levelParams.length) :
    ConLeche.headTypePW find? root d (.const nm ls) n =
      (ConLeche.residualPW (ConLeche.peelPisW find? n c.toConstantVal.type)).map
        (Level.substPW c.toConstantVal.levelParams ls) := by
  simp only [ConLeche.headTypePW, hf, ht, hl, Bool.false_eq_true, ite_false,
    ite_true]

/-- con-leche: ConLeche/Kernel/PropRead.lean:73-90 headTypePW — every other
constant head declines. -/
theorem headTypePW_const_none {find? : ConLeche.Name → Option ConstantInfo}
    {root : Expr} {d : Nat}
    {nm : ConLeche.Name} {ls : List Level} {n : Nat}
    (h : find? nm = none ∨ ∃ c, find? nm = some c ∧
      (c.isTowerEntry = true ∨ ls.length ≠ c.toConstantVal.levelParams.length)) :
    ConLeche.headTypePW find? root d (.const nm ls) n = none := by
  rcases h with hf | ⟨c, hf, ht | hl⟩
  · simp only [ConLeche.headTypePW, hf]
  · simp only [ConLeche.headTypePW, hf, ht, ite_true]
  · simp only [ConLeche.headTypePW, hf, hl, ite_false]; split <;> rfl

/-- con-leche: ConLeche/Kernel/PropRead.lean:105-122 headProofPW — a constant
head the environment answers off the tower at the right level count. -/
theorem headProofPW_const_hit {find? : ConLeche.Name → Option ConstantInfo}
    {nm : ConLeche.Name} {ls : List Level} {c : ConstantInfo}
    (hf : find? nm = some c) (ht : c.isTowerEntry = false)
    (hl : ls.length = c.toConstantVal.levelParams.length) :
    ConLeche.headProofPW find? (.const nm ls) =
      (ConLeche.typeSortPW find? c.toConstantVal.type).map
        (Level.substPW c.toConstantVal.levelParams ls) := by
  simp only [ConLeche.headProofPW, hf, ht, hl, Bool.false_eq_true, ite_false,
    ite_true]

/-- con-leche: ConLeche/Kernel/PropRead.lean:105-122 headProofPW — every
other constant head declines. -/
theorem headProofPW_const_none {find? : ConLeche.Name → Option ConstantInfo}
    {nm : ConLeche.Name} {ls : List Level}
    (h : find? nm = none ∨ ∃ c, find? nm = some c ∧
      (c.isTowerEntry = true ∨ ls.length ≠ c.toConstantVal.levelParams.length)) :
    ConLeche.headProofPW find? (.const nm ls) = none := by
  rcases h with hf | ⟨c, hf, ht | hl⟩
  · simp only [ConLeche.headProofPW, hf]
  · simp only [ConLeche.headProofPW, hf, ht, ite_true]
  · simp only [ConLeche.headProofPW, hf, hl, ite_false]; split <;> rfl

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

/-- con-leche: none — **the constructor tag of a denotation**: the four tag
bits of a handle are the tag of the expression it denotes. -/
def exprTag : Expr → UInt32
  | .bvar _ => ETag.bvar
  | .fvar _ _ => ETag.fvar
  | .sort _ => ETag.sort
  | .const _ _ => ETag.const
  | .app _ _ => ETag.app
  | .lam _ _ => ETag.lam
  | .forallE _ _ => ETag.forallE
  | .letE _ _ _ => ETag.letE
  | .lit _ => ETag.lit
  | .proj _ _ _ => ETag.proj

/-- con-leche: none — DESIGN §8.3: a handle's tag is its denotation's. -/
theorem tag_of_denote {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr}
    (hd : denoteE st h = some e) : h.tag = exprTag e := by
  obtain ⟨v, hv⟩ := denoteE_view hd
  rw [EStore.tagOf_of_view hv]
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv hd]; rfl
  | fvar k t => obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv hd; rfl
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv hd; rfl
  | const n us => obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hv hd; rfl
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv hd; rfl
  | lam ty b => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv hd; rfl
  | forallE ty b =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv hd; rfl
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv hd; rfl
  | lit l => rw [denote_lit_inv hwf hv hd]; rfl
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv hd; rfl


/-- con-leche: none — a denoting handle's view and its denotation carry one
tag. -/
theorem denote_tag_eq {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {v : ENodeView} {x : Expr} (hv : st.view h = some v)
    (hx : denoteE st h = some x) : v.tagOf = exprTag x :=
  (EStore.tagOf_of_view hv).symm.trans (tag_of_denote hwf hx)

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
    rw [ConRon.Arena.binderDom]
    by_cases htg : (h.tag == ETag.forallE) = true
    · rw [ite_eq_left htg]
      refine triple_seq (viewBind_spec s₀ h) ?_
      rintro ob s1 ⟨hs1, hob⟩
      subst s1; subst hob
      cases hvb : s₀.store.viewBind h with
      | none => exact triple_failDanglingE
      | some p =>
        obtain ⟨A, b⟩ := p
        dsimp only
        refine triple_pureR ⟨rfl, fun x hx => ?_⟩
        obtain ⟨et, eb, rfl, hA, _⟩ := denote_forallE_inv hok.state.wf
          (view_of_viewBind_forallE (by simpa using htg) hvb) hx
        simp [denoteEO, hA, Expr.binderDom]
    · rw [ite_eq_right htg]
      refine triple_pureR ⟨rfl, fun x hx => ?_⟩
      rw [tag_of_denote hok.state.wf hx] at htg
      cases x <;> simp_all [exprTag, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Expr.binderDom, denoteEO]
  | succ k ih =>
    intro s₀ h hok
    rw [ConRon.Arena.binderDom]
    by_cases htg : (h.tag == ETag.forallE) = true
    · rw [ite_eq_left htg]
      refine triple_seq (viewBind_spec s₀ h) ?_
      rintro ob s1 ⟨hs1, hob⟩
      subst s1; subst hob
      cases hvb : s₀.store.viewBind h with
      | none => exact triple_failDanglingE
      | some p =>
        obtain ⟨A, b⟩ := p
        dsimp only
        refine triple_mono (ih s₀ b hok) ?_
        rintro r s' ⟨rfl, hr⟩
        refine ⟨rfl, fun x hx => ?_⟩
        obtain ⟨et, eb, rfl, _, hb⟩ := denote_forallE_inv hok.state.wf
          (view_of_viewBind_forallE (by simpa using htg) hvb) hx
        rw [hr eb hb]; rfl
    · rw [ite_eq_right htg]
      refine triple_pureR ⟨rfl, fun x hx => ?_⟩
      rw [tag_of_denote hok.state.wf hx] at htg
      cases x <;> simp_all [exprTag, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, Expr.binderDom, denoteEO]

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
    -- tag first, then the `app` projection (task #97-P5-Core round 6)
    case vc2 => exact hok
    case vc3 =>
      rename_i htg s0 f a hv
      obtain ⟨ef, _, _, hf, _⟩ := denote_app_inv hok.state.wf
        (view_of_viewApp_tag htg hv.symm) hx₀
      exact ⟨ef, hf⟩
    case vc1 =>
      rename_i htg f a s0 hr hv
      refine ⟨rfl, fun x hx => ?_⟩
      obtain ⟨ef, ea, rfl, hf, _⟩ := denote_app_inv hok.state.wf
        (view_of_viewApp_tag htg hv.symm) hx
      rw [hr ef hf]; rfl
    case vc4 =>
      rename_i s0 hnt
      refine ⟨rfl, fun x hx => ?_⟩
      obtain ⟨v, hview, hne⟩ := view_not_of_tagB hx hnt
      have hna := denote_not_app' hok.state.wf hview hx
        (fun f a hh => hne (by rw [hh]; rfl))
      cases x <;> first | rfl | exact absurd rfl (hna _ _)

/-- con-leche: ConLeche/Kernel/PropRead.lean:65-71 residualPW — **THEOREM 1
for `residualPW`**, in answer shape (the residual is `peelNeverPis`'s
answer).  The level is read back with `readLevel`, which leaves the state
alone. -/
theorem residualPW_spec' (s₀ : AState) (r : Option EIdx)
    (hok : CheckOK mode env fe s₀) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.residualPW r
    ⦃fun pw s' => s' = s₀ ∧ ∀ ox, denoteEO s₀.store r = some ox →
        pw = ConLeche.residualPW ox; ⊤⦄ := by
  vcgen [ConRon.Arena.residualPW]
  all_goals (bridge_peel; subst_vars)
  -- tag first, then the `sort` projection (task #97-P5-Core round 6)
  case vc1 =>
    rename_i h htg u s0 hl hv
    refine ⟨rfl, fun ox hox => ?_⟩
    obtain ⟨x, rfl, hx⟩ := denoteEO_some_inv hox
    obtain ⟨l', rfl, hl'⟩ := denote_sort_inv hok.state.wf
      (view_of_viewSort_tag htg hv.symm) hx
    rw [hl] at hl'; cases hl'; rfl
  case vc2 =>
    rename_i s0 h hnt
    refine ⟨rfl, fun ox hox => ?_⟩
    obtain ⟨x, rfl, hx⟩ := denoteEO_some_inv hox
    obtain ⟨v, hview, hne⟩ := view_not_of_tagB hx hnt
    have hns := denote_not_sort hok.state.wf hview hx
      (fun u hh => hne (by rw [hh]; rfl))
    cases x <;> first | rfl | exact absurd rfl (hns _)
  case vc3 =>
    refine ⟨rfl, fun ox hox => ?_⟩
    rw [denoteEO_none_inv hox]; rfl

/-! ## 2b. The identity-like wrappers (con-leche's task #342) -/

/-- con-leche: ConLeche/Kernel/PropRead.lean:73-79 lamProj? — **THEOREM 1 for
`lamProj?`**.  Read-only; the arena's walk is fueled and fails at fuel `0`. -/
theorem lamProj?_spec' (fuel : Nat) : ∀ (k : Nat) (s₀ : AState) (h : EIdx),
    CheckOK mode env fe s₀ →
    ⦃fun s => s = s₀⦄ ConRon.Arena.lamProj? fuel k h
    ⦃fun r s' => s' = s₀ ∧ ∀ x, denoteE s₀.store h = some x →
        r = ConLeche.lamProj? k x; ⊤⦄ := by
  induction fuel with
  | zero =>
    intro k s₀ h _
    rw [ConRon.Arena.lamProj?]
    exact triple_fail
  | succ fuel ih =>
    intro k s₀ h hok
    rw [ConRon.Arena.lamProj?]
    by_cases htl : (h.tag == ETag.lam) = true
    · rw [ite_eq_left htl]
      refine triple_seq (viewBind_spec s₀ h) ?_
      rintro ob s1 ⟨hs1, hob⟩
      subst s1; subst hob
      cases hvb : s₀.store.viewBind h with
      | none => exact triple_failDanglingE
      | some p =>
        obtain ⟨A, b⟩ := p
        dsimp only
        refine triple_mono (ih (k + 1) s₀ b hok) ?_
        rintro r s' ⟨rfl, hr⟩
        refine ⟨rfl, fun x hx => ?_⟩
        obtain ⟨et, eb, rfl, _, hb⟩ := denote_lam_inv hok.state.wf
          (view_of_viewBind_lam (by simpa using htl) hvb) hx
        rw [hr eb hb]; rfl
    · rw [ite_eq_right htl]
      by_cases htb : (h.tag == ETag.bvar) = true
      · rw [ite_eq_left htb]
        refine triple_seq (viewBVar_spec s₀ h) ?_
        rintro ob s1 ⟨hs1, hob⟩
        subst s1; subst hob
        cases hvb : s₀.store.viewBVar h with
        | none => exact triple_failDanglingE
        | some j =>
          dsimp only
          refine triple_pureR ⟨rfl, fun x hx => ?_⟩
          rw [denote_bvar_inv hok.state.wf (view_of_viewBVar_tag htb hvb) hx]
          rfl
      · rw [ite_eq_right htb]
        refine triple_pureR ⟨rfl, fun x hx => ?_⟩
        rw [tag_of_denote hok.state.wf hx] at htl htb
        cases x <;> simp_all [exprTag, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, ConLeche.lamProj?]

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
    have hwf := hok.state.wf
    rw [ConRon.Arena.unwrapIdDefs]
    refine triple_seq (ExprOps.getAppFn_spec fuel s₀ e hok.state
      (by rw [hx₀]; rfl)) ?_
    rintro hh s1 ⟨hs1, hrelF⟩
    subst s1
    have hdd : denoteE s₀.store hh = some x₀.getAppFn := hrelF x₀ hx₀
    -- the answer `e` itself, when the head declines
    have hkeep : ∀ (c : Expr → Prop), (∀ x, denoteE s₀.store e = some x →
        ConLeche.unwrapIdDefs env.find? (n + 1) x = x) →
        ⦃fun s => s = s₀⦄ (pure e : AM EIdx)
        ⦃fun r s' => s' = s₀ ∧ ∀ x, denoteE s₀.store e = some x →
          denoteE s₀.store r = some (ConLeche.unwrapIdDefs env.find? (n + 1)
            x); ⊤⦄ := by
      intro _ h
      exact triple_pureR ⟨rfl, fun x hx => by rw [h x hx, hx]⟩
    by_cases htc : (hh.tag == ETag.const) = true
    · rw [ite_eq_left htc]
      refine triple_seq (viewConstName_spec s₀ hh) ?_
      rintro oc s2 ⟨hs2, hoc⟩
      subst s2; subst hoc
      cases hvc : s₀.store.viewConstName hh with
      | none => exact triple_failDanglingE
      | some c =>
        dsimp only
        obtain ⟨us, hview⟩ := view_of_viewConstName (by simpa using htc) hvc
        obtain ⟨nm, ls, hgf, hn, _⟩ := denote_const_inv hwf hview hdd
        have hgf' : ∀ x, denoteE s₀.store e = some x →
            x.getAppFn = .const nm ls := fun x hx => by
          obtain rfl := Option.some.inj (hx.symm.trans hx₀); exact hgf
        have hopt := optCI_find hok hn
        cases hfd : fe.find? c with
        | none =>
          rw [hfd] at hopt
          refine hkeep (fun _ => True) (fun x hx => ?_)
          simp only [ConLeche.unwrapIdDefs, hgf' x hx]
          rw [show env.find? nm = none from hopt]
        | some ci =>
          rw [hfd] at hopt
          obtain ⟨c', hci, hfind⟩ := hopt
          cases ci
          case defnInfo cv v hint =>
            obtain ⟨dcv, vx, _, hv, rfl⟩ := denoteCI_defnInfo_inv hci
            dsimp only
            refine triple_seq (lamProj?_spec' fuel 0 s₀ v hok) ?_
            rintro op s3 ⟨hs3, hop⟩
            subst s3
            have hop' := hop vx hv
            subst hop'
            cases hlp : ConLeche.lamProj? 0 vx with
            | none =>
              dsimp only
              refine hkeep (fun _ => True) (fun x hx => ?_)
              simp only [ConLeche.unwrapIdDefs, hgf' x hx, hfind, hlp]
            | some kj =>
              obtain ⟨k, j⟩ := kj
              dsimp only
              refine triple_seq (ExprOps.getAppArgs_spec fuel s₀ e hok.state
                (by rw [hx₀]; rfl)) ?_
              rintro args s4 ⟨hs4, hrelA⟩
              subst s4
              have hargs : Frontend.denoteEList s₀.store args =
                  some x₀.getAppArgs := hrelA x₀ hx₀
              have hlen : x₀.getAppArgs.length = args.length :=
                denoteEList_len hargs
              by_cases hg : (decide (k ≤ args.length) && args.length == k) = true
              · rw [ite_eq_left hg]
                have hd := denoteEList_getD hargs (k - 1 - j) e x₀ hx₀
                refine triple_mono (ih s₀ (args.getD (k - 1 - j) e) hok
                  ⟨_, hd⟩) ?_
                rintro r s' ⟨rfl, hr⟩
                refine ⟨rfl, fun x hx => ?_⟩
                obtain rfl := Option.some.inj (hx.symm.trans hx₀)
                rw [hr _ hd]
                have hg' : (decide (k ≤ x.getAppArgs.length) &&
                    x.getAppArgs.length == k) = true := by rw [hlen]; exact hg
                simp only [ConLeche.unwrapIdDefs, hgf, hfind, hlp, hg', ite_true]
              · rw [ite_eq_right hg]
                refine hkeep (fun _ => True) (fun x hx => ?_)
                obtain rfl := Option.some.inj (hx.symm.trans hx₀)
                have hg' : ¬ (decide (k ≤ x.getAppArgs.length) &&
                    x.getAppArgs.length == k) = true := by rw [hlen]; exact hg
                simp only [ConLeche.unwrapIdDefs, hgf, hfind, hlp]
                rw [ite_eq_right hg']
          all_goals
            dsimp only
            refine hkeep (fun _ => True) (fun x hx => ?_)
            have hnd : ∀ cv vx hint, c' ≠ .defnInfo cv vx hint := by
              rintro cv vx hint rfl
              simp only [Frontend.denoteCI] at hci
              first | (simp at hci) | (split at hci <;> simp_all)
            simp only [ConLeche.unwrapIdDefs, hgf' x hx, hfind]
            cases c' <;> first | rfl | exact absurd rfl (hnd _ _ _)
    · rw [ite_eq_right htc]
      refine hkeep (fun _ => True) (fun x hx => ?_)
      obtain rfl := Option.some.inj (hx.symm.trans hx₀)
      have hne := htc
      rw [tag_of_denote hwf hdd] at hne
      simp only [ConLeche.unwrapIdDefs]
      split
      · rename_i c us' heq
        rw [heq] at hne; simp [exprTag] at hne
      · rfl

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
    rw [ConRon.Arena.peelPisW]
    refine triple_seq (unwrapIdDefs_spec' fuel 4 s₀ e hok hpre) ?_
    rintro u s1 ⟨hs1, hu⟩
    subst s1
    refine triple_pureR ⟨rfl, fun x hx => ?_⟩
    simp [denoteEO, hu x hx, ConLeche.peelPisW]
  | succ k ih =>
    intro s₀ e hok hpre
    obtain ⟨x₀, hx₀⟩ := hpre
    have hwf := hok.state.wf
    rw [ConRon.Arena.peelPisW]
    by_cases htg : (e.tag == ETag.forallE) = true
    · rw [ite_eq_left htg]
      refine triple_seq (viewBind_spec s₀ e) ?_
      rintro ob s1 ⟨hs1, hob⟩
      subst s1; subst hob
      cases hvb : s₀.store.viewBind e with
      | none => exact triple_failDanglingE
      | some p =>
        obtain ⟨A, b⟩ := p
        dsimp only
        have hv := view_of_viewBind_forallE (by simpa using htg) hvb
        obtain ⟨_, eb₀, _, _, hb₀⟩ := denote_forallE_inv hwf hv hx₀
        refine triple_mono (ih s₀ b hok ⟨eb₀, hb₀⟩) ?_
        rintro r s' ⟨rfl, hr⟩
        refine ⟨rfl, fun x hx => ?_⟩
        obtain ⟨et, eb, rfl, _, hb⟩ := denote_forallE_inv hwf hv hx
        rw [hr eb hb]; rfl
    · rw [ite_eq_right htg]
      have hnf : ∀ x, denoteE s₀.store e = some x →
          ConLeche.peelPisW env.find? (k + 1) x =
            match ConLeche.unwrapIdDefs env.find? 4 x with
            | .forallE _ b => ConLeche.peelPisW env.find? k b
            | _ => none := by
        intro x hx
        have htg' := htg
        rw [tag_of_denote hwf hx] at htg'
        cases x <;> (try simp [exprTag] at htg') <;> first | rfl | simp [ConLeche.peelPisW]
      refine triple_seq (unwrapIdDefs_spec' fuel 4 s₀ e hok ⟨x₀, hx₀⟩) ?_
      rintro u s1 ⟨hs1, hu⟩
      subst s1
      have hu₀ := hu x₀ hx₀
      by_cases htu : (u.tag == ETag.forallE) = true
      · rw [ite_eq_left htu]
        refine triple_seq (viewBind_spec s₀ u) ?_
        rintro ob s1 ⟨hs1, hob⟩
        subst s1; subst hob
        cases hvb : s₀.store.viewBind u with
        | none => exact triple_failDanglingE
        | some p =>
          obtain ⟨A, b⟩ := p
          dsimp only
          have hv := view_of_viewBind_forallE (by simpa using htu) hvb
          obtain ⟨_, eb₀, _, _, hb₀⟩ := denote_forallE_inv hwf hv hu₀
          refine triple_mono (ih s₀ b hok ⟨eb₀, hb₀⟩) ?_
          rintro r s' ⟨rfl, hr⟩
          refine ⟨rfl, fun x hx => ?_⟩
          obtain rfl := Option.some.inj (hx.symm.trans hx₀)
          obtain ⟨et, eb, heq, _, hb⟩ := denote_forallE_inv hwf hv hu₀
          rw [hnf _ hx₀, heq, hr eb hb]
      · rw [ite_eq_right htu]
        refine triple_pureR ⟨rfl, fun x hx => ?_⟩
        rw [hnf _ hx]
        have hux := hu x hx
        have htu' := htu
        rw [tag_of_denote hwf hux] at htu'
        generalize ConLeche.unwrapIdDefs env.find? 4 x = U at htu' ⊢
        cases U <;> simp_all [exprTag, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, denoteEO]

/-! ## 3. The head readers -/

/-- con-leche: ConLeche/Kernel/Level.lean substPW — **THEOREM 1 for
`substPWAt`**: `Level.substPW` at a stored constant's level parameters and a
use's universe arguments, with the cutoff hoisted over the readbacks. -/
theorem substPWAt_spec' (s₀ : AState) (lps : List NIdx) (us : LsIdx)
    (pw : PropWhen) (ks : List ConLeche.Name) (vs : List Level)
    (hok : CheckOK mode env fe s₀)
    (hks : Frontend.denoteNList s₀.store.ns lps = some ks)
    (hvs : denoteLs s₀.store.lss us = some vs) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.substPWAt lps us pw
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ r = some (Level.substPW ks vs pw); ⊤⦄ := by
  unfold ConRon.Arena.substPWAt
  split
  · refine triple_seq (readNamesM_spec s₀ lps hok.caches.readN) ?_
    rintro ks' s1 ⟨hst1, hm1, hp1, hc1, hks1, hN1⟩
    have hf1 := ReadbackFrame.ofReadN hst1 hm1 hp1 hc1 hN1
    have hok1 := CheckOK.ofReadbackFrame hok hf1
    refine triple_seq (readLevelsM_spec s1 us hok1.caches.readLs) ?_
    rintro vs' s2 ⟨hst2, hm2, hp2, hc2, hvs2, hLs2⟩
    have hf2 := ReadbackFrame.ofReadLs hst2 hm2 hp2 hc2 hLs2
    rw [hks] at hks1
    rw [hst1, hvs] at hvs2
    obtain rfl := Option.some.inj hks1
    obtain rfl := Option.some.inj hvs2
    exact triple_pureR ⟨CheckOK.ofReadbackFrame hok (hf1.trans hf2),
      (hf1.trans hf2).store, (hf1.trans hf2).pins, rfl⟩
  · rename_i hne
    exact triple_pureR ⟨hok, rfl, rfl, by
      rw [substPW_cutoff (fun a as h => hne a as h)]⟩

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
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hx₀
  have hvt := denote_tag_eq hwf hv hx₀
  unfold ConRon.Arena.headTypePW
  refine view_bind_triple hv ?_
  -- the residual of a denoting type handle
  have tail : ∀ (T : EIdx) (tx : Expr), denoteE s₀.store T = some tx →
      ⦃fun s => s = s₀⦄ (do
        let res ← ConRon.Arena.peelPisW fe fuel n T
        ConRon.Arena.residualPW res)
      ⦃fun r s' => s' = s₀ ∧
        r = ConLeche.residualPW (ConLeche.peelPisW env.find? n tx); ⊤⦄ := by
    intro T tx hT
    refine triple_seq (peelPisW_spec' fuel n s₀ T hok ⟨tx, hT⟩) ?_
    rintro res s1 ⟨hs1, hres⟩
    subst s1
    refine triple_mono (residualPW_spec' s₀ res hok) ?_
    rintro r s' ⟨rfl, hr⟩
    exact ⟨rfl, hr _ (hres tx hT)⟩
  cases v
  case const I us =>
    dsimp only
    cases hfd : fe.find? I with
    | none =>
      dsimp only
      exact triple_pureR ⟨hok, rfl, rfl, fun rx x _ hx => by
        obtain ⟨nm, ls, rfl, hf⟩ := const_miss hok hv hfd hx
        exact (headTypePW_const_none (Or.inl hf)).symm⟩
    | some ci =>
      dsimp only
      by_cases htow : ci.isTowerEntry = true
      · rw [ite_eq_left htow]
        exact triple_pureR ⟨hok, rfl, rfl, fun rx x _ hx => by
          obtain ⟨nm, ls, c, rfl, hf, ht⟩ := const_tower hok hv hfd hx
          exact (headTypePW_const_none
            (Or.inr ⟨c, hf, Or.inl (ht ▸ htow)⟩)).symm⟩
      · rw [ite_eq_right htow]
        have htow' : ci.isTowerEntry = false := by simpa using htow
        refine triple_seq (toConstantVal_nt_spec s₀ ci htow') ?_
        rintro cv s1 ⟨hs1, hcv⟩
        subst s1
        obtain ⟨nm, ls, c, rfl, hls, hf, ht, hlps, hty, hll, hvl⟩ :=
          const_hit hok hv hfd hcv hx₀
        have hct : c.isTowerEntry = false := by rw [← ht]; exact htow'
        refine triple_seq (viewLsLen_spec s₀ us) ?_
        rintro ol s2 ⟨hs2, hol⟩
        subst s2
        rw [hvl] at hol
        subst hol
        dsimp only
        by_cases hlen : ls.length = cv.levelParams.length
        · rw [ite_eq_left hlen]
          have hl : ls.length = c.toConstantVal.levelParams.length := by
            rw [hll]; exact hlen
          refine triple_seq (peelPisW_spec' fuel n s₀ cv.type hok ⟨_, hty⟩) ?_
          rintro res s3 ⟨hs3, hres⟩
          subst s3
          refine triple_seq (residualPW_spec' s₀ res hok) ?_
          rintro opw s4 ⟨hs4, hopw⟩
          subst s4
          have hpw := hopw _ (hres _ hty)
          cases opw with
          | none =>
            exact triple_pureR ⟨hok, rfl, rfl, fun rx x _ hx => by
              obtain rfl := Option.some.inj (hx.symm.trans hx₀)
              rw [headTypePW_const_hit hf hct hl, ← hpw]; rfl⟩
          | some pw =>
            refine triple_mono (substPWAt_spec' s₀ cv.levelParams us pw _ _ hok
              hlps hls) ?_
            rintro r s' ⟨hok', hst', hp', rfl⟩
            exact ⟨hok', hst', hp', fun rx x _ hx => by
              obtain rfl := Option.some.inj (hx.symm.trans hx₀)
              rw [headTypePW_const_hit hf hct hl, ← hpw]; rfl⟩
        · rw [ite_eq_right hlen]
          exact triple_pureR ⟨hok, rfl, rfl, fun rx x _ hx => by
            obtain rfl := Option.some.inj (hx.symm.trans hx₀)
            exact (headTypePW_const_none
              (Or.inr ⟨c, hf, Or.inr (by rw [hll]; exact hlen)⟩)).symm⟩
  case fvar k ty =>
    dsimp only
    obtain ⟨t, rfl, ht⟩ := denote_fvar_inv hwf hv hx₀
    refine triple_mono (tail ty t ht) ?_
    rintro r s' ⟨rfl, hr⟩
    exact ⟨hok, rfl, rfl, fun rx x _ hx => by
      obtain rfl := Option.some.inj (hx.symm.trans hx₀)
      rw [hr]; rfl⟩
  case bvar i =>
    dsimp only
    rw [denote_bvar_inv hwf hv hx₀] at hx₀
    by_cases hid : i < d
    · rw [ite_eq_left hid]
      refine triple_seq (binderDom_spec' (d - 1 - i) s₀ root hok) ?_
      rintro oD s1 ⟨hs1, hoD⟩
      subst s1
      have hD := hoD rx₀ hrx₀
      cases oD with
      | none =>
        exact triple_pureR ⟨hok, rfl, rfl, fun rx x hr hx => by
          obtain rfl := Option.some.inj (hx.symm.trans hx₀)
          obtain rfl := Option.some.inj (hr.symm.trans hrx₀)
          have hn : rx.binderDom (d - 1 - i) = none := by
            simpa [denoteEO] using hD.symm
          simp [ConLeche.headTypePW, hid, hn]⟩
      | some D =>
        obtain ⟨Dx, hDx, hDd⟩ := denoteEO_some_inv hD
        refine triple_mono (tail D Dx hDd) ?_
        rintro r s' ⟨rfl, hr⟩
        exact ⟨hok, rfl, rfl, fun rx x hrr hx => by
          obtain rfl := Option.some.inj (hx.symm.trans hx₀)
          obtain rfl := Option.some.inj (hrr.symm.trans hrx₀)
          rw [hr]; simp [ConLeche.headTypePW, hid, hDx]⟩
    · rw [ite_eq_right hid]
      exact triple_pureR ⟨hok, rfl, rfl, fun rx x _ hx => by
        obtain rfl := Option.some.inj (hx.symm.trans hx₀)
        simp [ConLeche.headTypePW, hid]⟩
  all_goals
    dsimp only
    exact triple_pureR ⟨hok, rfl, rfl, fun rx x _ hx => by
      obtain rfl := Option.some.inj (hx.symm.trans hx₀)
      cases x <;> simp_all [exprTag, ENodeView.tagOf, ConLeche.headTypePW,
        ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, ETag.letE, ETag.lit, ETag.proj]⟩

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
    have hwf := hok.state.wf
    rw [ConRon.Arena.typeSortPWGo]
    by_cases htf : (R.tag == ETag.forallE) = true
    · rw [ite_eq_left htf]
      refine triple_seq (viewBind_spec s₀ R) ?_
      rintro ob s1 ⟨hs1, hob⟩
      subst s1; subst hob
      cases hvb : s₀.store.viewBind R with
      | none => exact triple_failDanglingE
      | some p =>
        obtain ⟨A, b⟩ := p
        dsimp only
        have hv := view_of_viewBind_forallE (by simpa using htf) hvb
        obtain ⟨_, eb₀, _, _, hb₀⟩ := denote_forallE_inv hwf hv hx₀
        refine triple_mono (ih s₀ b (d + 1) hok ⟨eb₀, hb₀⟩ hroot) ?_
        rintro r s' ⟨hok', hst', hp', hr⟩
        refine ⟨hok', hst', hp', fun rx x hrx hx => ?_⟩
        obtain ⟨et, eb, rfl, _, hb⟩ := denote_forallE_inv hwf hv hx
        rw [hr rx eb hrx hb]; rfl
    · rw [ite_eq_right htf]
      by_cases hts : (R.tag == ETag.sort) = true
      · rw [ite_eq_left hts]
        exact triple_pureR ⟨hok, rfl, rfl, fun rx x _ hx => by
          have hts' := hts
          rw [tag_of_denote hwf hx] at hts'
          cases x <;> simp_all [exprTag, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, ConLeche.typeSortPWGo]⟩
      · rw [ite_eq_right hts]
        refine triple_seq (ExprOps.getAppFn_spec fuel s₀ R hok.state
          (by rw [hx₀]; rfl)) ?_
        rintro fn s1 ⟨hs1, hrelF⟩
        subst s1
        refine triple_seq (numArgs_spec' fuel s₀ R hok ⟨x₀, hx₀⟩) ?_
        rintro k s2 ⟨hs2, hk⟩
        subst s2
        refine triple_mono (headTypePW_spec' fuel s₀ root d fn k hok
          ⟨_, hrelF x₀ hx₀⟩ hroot) ?_
        rintro r s' ⟨hok', hst', hp', hr⟩
        refine ⟨hok', hst', hp', fun rx x hrx hx => ?_⟩
        rw [hr rx _ hrx (hrelF x hx), hk x hx]
        have htf' := htf
        have hts' := hts
        rw [tag_of_denote hwf hx] at htf' hts'
        cases x <;> simp_all [exprTag, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, ConLeche.typeSortPWGo]

/-- con-leche: ConLeche/Kernel/PropRead.lean:148-150 typeSortPW — **THEOREM 1
for `typeSortPW`**, in answer shape. -/
theorem typeSortPW_spec' (fuel : Nat) (s₀ : AState) (T : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store T = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.typeSortPW fe fuel T
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store T = some x →
        r = ConLeche.typeSortPW env.find? x; ⊤⦄ := by
  unfold ConRon.Arena.typeSortPW
  refine triple_mono (typeSortPWGo_spec' T fuel s₀ T 0 hok hpre hpre) ?_
  rintro r s' ⟨hok', hst', hp', hr⟩
  exact ⟨hok', hst', hp', fun x hx => hr x x hx hx⟩

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
  have hwf := hok.state.wf
  obtain ⟨v, hv⟩ := denoteE_view hx₀
  have hvt := denote_tag_eq hwf hv hx₀
  have hext : ∀ {t : AState}, t.store = s₀.store → Ext s₀.store t.store :=
    fun h => by rw [h]; exact Ext.refl _
  unfold ConRon.Arena.headProofPW
  refine view_bind_triple hv ?_
  cases v
  case const I us =>
    dsimp only
    cases hfd : fe.find? I with
    | none =>
      dsimp only
      exact triple_pureR ⟨hok, Ext.refl _, rfl, fun x hx => by
        obtain ⟨nm, ls, rfl, hf⟩ := const_miss hok hv hfd hx
        exact (headProofPW_const_none (Or.inl hf)).symm⟩
    | some ci =>
      dsimp only
      by_cases htow : ci.isTowerEntry = true
      · rw [ite_eq_left htow]
        exact triple_pureR ⟨hok, Ext.refl _, rfl, fun x hx => by
          obtain ⟨nm, ls, c, rfl, hf, ht⟩ := const_tower hok hv hfd hx
          exact (headProofPW_const_none
            (Or.inr ⟨c, hf, Or.inl (ht ▸ htow)⟩)).symm⟩
      · rw [ite_eq_right htow]
        have htow' : ci.isTowerEntry = false := by simpa using htow
        refine triple_seq (toConstantVal_nt_spec s₀ ci htow') ?_
        rintro cv s1 ⟨hs1, hcv⟩
        subst s1
        obtain ⟨nm, ls, c, rfl, hls, hf, ht, hlps, hty, hll, hvl⟩ :=
          const_hit hok hv hfd hcv hx₀
        have hct : c.isTowerEntry = false := by rw [← ht]; exact htow'
        refine triple_seq (viewLsLen_spec s₀ us) ?_
        rintro ol s2 ⟨hs2, hol⟩
        subst s2
        rw [hvl] at hol
        subst hol
        dsimp only
        by_cases hlen : ls.length = cv.levelParams.length
        · rw [ite_eq_left hlen]
          have hl : ls.length = c.toConstantVal.levelParams.length := by
            rw [hll]; exact hlen
          refine triple_seq (typeSortPW_spec' fuel s₀ cv.type hok ⟨_, hty⟩) ?_
          rintro opw s3 ⟨hok3, hst3, hp3, hopw⟩
          have hpw := hopw _ hty
          cases opw with
          | none =>
            exact triple_pureR ⟨hok3, hext hst3, hp3, fun x hx => by
              obtain rfl := Option.some.inj (hx.symm.trans hx₀)
              rw [headProofPW_const_hit hf hct hl, ← hpw]; rfl⟩
          | some pw =>
            refine triple_mono (substPWAt_spec' s3 cv.levelParams us pw _ _ hok3
              (by rw [hst3]; exact hlps) (by rw [hst3]; exact hls)) ?_
            rintro r s' ⟨hok', hst', hp', rfl⟩
            exact ⟨hok', hext (hst'.trans hst3), hp'.trans hp3, fun x hx => by
              obtain rfl := Option.some.inj (hx.symm.trans hx₀)
              rw [headProofPW_const_hit hf hct hl, ← hpw]; rfl⟩
        · rw [ite_eq_right hlen]
          exact triple_pureR ⟨hok, Ext.refl _, rfl, fun x hx => by
            obtain rfl := Option.some.inj (hx.symm.trans hx₀)
            exact (headProofPW_const_none
              (Or.inr ⟨c, hf, Or.inr (by rw [hll]; exact hlen)⟩)).symm⟩
  case fvar k ty =>
    dsimp only
    obtain ⟨t, rfl, ht⟩ := denote_fvar_inv hwf hv hx₀
    refine triple_mono (typeSortPW_spec' fuel s₀ ty hok ⟨t, ht⟩) ?_
    rintro r s' ⟨hok', hst', hp', hr⟩
    exact ⟨hok', hext hst', hp', fun x hx => by
      obtain rfl := Option.some.inj (hx.symm.trans hx₀)
      rw [hr t ht]; rfl⟩
  case proj S i sub =>
    dsimp only
    obtain ⟨Sn, es, rfl, hS, _⟩ := denote_proj_inv hwf hv hx₀
    refine triple_seq (IFEnv.findProj?_spec s₀ S i Sn hok hS) ?_
    rintro r s1 ⟨hok1, hx1, _, _, hp1, hsome, hnone⟩
    have hred : ConLeche.headProofPW env.find? (.proj Sn i es) =
        match env.findProj? Sn i with
        | some p =>
          (match ConLeche.typeSortPW env.find? p.body with
            | some pw => if pw.isNever then some pw else none
            | none => none)
        | none => none := by
      simp only [ConLeche.headProofPW, ConLeche.Env.findProj?]
      cases hf : env.find? (ConLeche.projTableName Sn) with
      | none => rfl
      | some ci =>
        cases ci with
        | projInfo tbl =>
          by_cases hi : i < tbl.numFields
          · simp only [hi, ite_true]; rfl
          · simp only [hi, ite_false]
        | _ => rfl
    cases r with
    | none =>
      exact triple_pureR ⟨hok1, hx1, hp1, fun x hx => by
        obtain rfl := Option.some.inj (hx.symm.trans hx₀)
        rw [hred, hnone rfl]⟩
    | some e =>
      obtain ⟨p, hpe, hfp⟩ := hsome e rfl
      obtain ⟨_, _, _, hbody, _⟩ := denoteProjEntry_inv hpe
      dsimp only
      refine triple_seq (typeSortPW_spec' fuel s1 e.body hok1 ⟨_, hbody⟩) ?_
      rintro opw s2 ⟨hok2, hst2, hp2, hopw⟩
      have hpw := hopw _ hbody
      have hx02 : Ext s₀.store s2.store :=
        hx1.trans (by rw [hst2]; exact Ext.refl _)
      cases opw with
      | none =>
        exact triple_pureR ⟨hok2, hx02, hp2.trans hp1, fun x hx => by
          obtain rfl := Option.some.inj (hx.symm.trans hx₀)
          rw [hred, hfp]; simp only; rw [← hpw]⟩
      | some pw =>
        exact triple_pureR ⟨hok2, hx02, hp2.trans hp1, fun x hx => by
          obtain rfl := Option.some.inj (hx.symm.trans hx₀)
          rw [hred, hfp]; simp only; rw [← hpw]⟩
  all_goals
    dsimp only
    exact triple_pureR ⟨hok, Ext.refl _, rfl, fun x hx => by
      obtain rfl := Option.some.inj (hx.symm.trans hx₀)
      cases x <;> simp_all [exprTag, ENodeView.tagOf, ConLeche.headProofPW,
        ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, ETag.letE, ETag.lit, ETag.proj]⟩

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
        r = ConLeche.proofPW env.find? x; ⊤⦄ := by
  induction fuel generalizing s₀ a with
  | zero =>
    rw [ConRon.Arena.proofPW]
    exact triple_fail
  | succ fuel ih =>
    obtain ⟨x₀, hx₀⟩ := hpre
    have hwf := hok.state.wf
    rw [ConRon.Arena.proofPW]
    by_cases hl : (a.tag == ETag.lam) = true
    · rw [ite_eq_left hl]
      refine triple_seq (viewBind_spec s₀ a) ?_
      rintro ob s1 ⟨hs1, hob⟩
      subst s1; subst hob
      cases hvb : s₀.store.viewBind a with
      | none => exact triple_failDanglingE
      | some p =>
        obtain ⟨A, b⟩ := p
        dsimp only
        have hv := view_of_viewBind_lam (by simpa using hl) hvb
        obtain ⟨_, eb₀, _, _, hb₀⟩ := denote_lam_inv hwf hv hx₀
        refine triple_mono (ih s₀ b hok ⟨eb₀, hb₀⟩) ?_
        rintro r s' ⟨hok', hx', hp', hr⟩
        refine ⟨hok', hx', hp', fun x hx => ?_⟩
        obtain ⟨et, eb, rfl, _, hb⟩ := denote_lam_inv hwf hv hx
        rw [hr eb hb]; rfl
    rw [ite_eq_right hl]
    by_cases hlt : (a.tag == ETag.letE) = true
    · rw [ite_eq_left hlt]
      refine triple_seq (viewLet_spec s₀ a) ?_
      rintro ob s1 ⟨hs1, hob⟩
      subst s1; subst hob
      cases hvb : s₀.store.viewLet a with
      | none => exact triple_failDanglingE
      | some p =>
        obtain ⟨T, w, b⟩ := p
        dsimp only
        have hv := view_of_viewLet_tag hlt hvb
        obtain ⟨_, _, eb₀, _, _, _, hb₀⟩ := denote_letE_inv hwf hv hx₀
        refine triple_mono (ih s₀ b hok ⟨eb₀, hb₀⟩) ?_
        rintro r s' ⟨hok', hx', hp', hr⟩
        refine ⟨hok', hx', hp', fun x hx => ?_⟩
        obtain ⟨et, ew, eb, rfl, _, _, hb⟩ := denote_letE_inv hwf hv hx
        rw [hr eb hb]; rfl
    rw [ite_eq_right hlt]
    by_cases hap : (a.tag == ETag.app) = true
    · rw [ite_eq_left hap]
      refine triple_seq (viewApp_spec s₀ a) ?_
      rintro ob s1 ⟨hs1, hob⟩
      subst s1; subst hob
      cases hvb : s₀.store.viewApp a with
      | none => exact triple_failDanglingE
      | some p =>
        obtain ⟨f, g⟩ := p
        dsimp only
        have hv := view_of_viewApp_tag hap hvb
        obtain ⟨ef₀, _, _, hf₀, _⟩ := denote_app_inv hwf hv hx₀
        refine triple_mono (ih s₀ f hok ⟨ef₀, hf₀⟩) ?_
        rintro r s' ⟨hok', hx', hp', hr⟩
        refine ⟨hok', hx', hp', fun x hx => ?_⟩
        obtain ⟨ef, ea, rfl, hf, _⟩ := denote_app_inv hwf hv hx
        rw [hr ef hf]; rfl
    rw [ite_eq_right hap]
    refine triple_mono (headProofPW_spec' fuel s₀ a hok ⟨x₀, hx₀⟩) ?_
    rintro r s' ⟨hok', hx', hp', hr⟩
    refine ⟨hok', hx', hp', fun x hx => ?_⟩
    rw [hr x hx]
    have hl' := hl
    have hlt' := hlt
    have hap' := hap
    rw [tag_of_denote hwf hx] at hl' hlt' hap'
    cases x <;> simp_all [exprTag, ConLeche.proofPW,
      ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam,
        ETag.forallE, ETag.letE, ETag.lit, ETag.proj]

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
  unfold ConRon.Arena.notProofFast
  refine triple_seq (proofPW_spec' fuel s₀ a hok hpre) ?_
  rintro r s1 ⟨hok1, hx1, hp1, hr⟩
  cases r with
  | none =>
    exact triple_pureR ⟨hok1, hx1, hp1, fun x hx => by
      simp only [ConLeche.notProofFast, ← hr x hx]⟩
  | some pw =>
    exact triple_pureR ⟨hok1, hx1, hp1, fun x hx => by
      simp only [ConLeche.notProofFast, ← hr x hx]⟩

/-- con-leche: ConLeche/Kernel/PropRead.lean:148-153 isProofFast — **THEOREM
1 for `isProofFast`**, in answer shape. -/
theorem isProofFast_spec' (fuel : Nat) (s₀ : AState) (a : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store a = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.isProofFast fe fuel a
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store a = some x →
        b = ConLeche.isProofFast env.find? x; ⊤⦄ := by
  unfold ConRon.Arena.isProofFast
  refine triple_seq (proofPW_spec' fuel s₀ a hok hpre) ?_
  rintro r s1 ⟨hok1, hx1, hp1, hr⟩
  cases r with
  | none =>
    exact triple_pureR ⟨hok1, hx1, hp1, fun x hx => by
      simp only [ConLeche.isProofFast, ← hr x hx]⟩
  | some pw =>
    exact triple_pureR ⟨hok1, hx1, hp1, fun x hx => by
      simp only [ConLeche.isProofFast, ← hr x hx]⟩

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
#print axioms denote_not_app'
#print axioms denote_not_fvar
#print axioms denoteEO_some_inv
#print axioms const_hit
#print axioms headTypePW_const_hit
#print axioms headProofPW_const_hit
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

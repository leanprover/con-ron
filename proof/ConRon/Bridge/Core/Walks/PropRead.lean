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
      cases x <;> simp_all [exprTag, Expr.binderDom, denoteEO]
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
      cases x <;> simp_all [exprTag, Expr.binderDom, denoteEO]

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
        cases x <;> simp_all [exprTag, ConLeche.lamProj?]

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
        cases U <;> simp_all [exprTag, denoteEO]

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
  sorry

/-- con-leche: ConLeche/Kernel/PropRead.lean:112-131 headTypePW — **THEOREM 1
for `headTypePW`**, in answer shape (the head is `getAppFn`'s answer; the
telescope root is the type the walk started at). -/
theorem headTypePW_spec' (fuel : Nat) (s₀ : AState) (root : EIdx) (d : Nat)
    (h : EIdx) (n : Nat) (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store h = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.headTypePW fe fuel root d h n
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ ∀ rx x, denoteE s₀.store root = some rx →
        denoteE s₀.store h = some x →
        r = ConLeche.headTypePW env.find? rx d x n; ⊤⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/PropRead.lean:136-140 typeSortPWGo — **THEOREM
1 for `typeSortPWGo`**, by induction on the fuel. -/
theorem typeSortPWGo_spec' (root : EIdx) (fuel : Nat) : ∀ (s₀ : AState)
    (R : EIdx) (d : Nat), CheckOK mode env fe s₀ →
    (∃ x, denoteE s₀.store R = some x) →
    ⦃fun s => s = s₀⦄ ConRon.Arena.typeSortPWGo fe root fuel R d
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ ∀ rx x, denoteE s₀.store root = some rx →
        denoteE s₀.store R = some x →
        r = ConLeche.typeSortPWGo env.find? rx x d; ⊤⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/PropRead.lean:148-150 typeSortPW — **THEOREM 1
for `typeSortPW`**, in answer shape. -/
theorem typeSortPW_spec' (fuel : Nat) (s₀ : AState) (T : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store T = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.typeSortPW fe fuel T
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store T = some x →
        r = ConLeche.typeSortPW env.find? x; ⊤⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/PropRead.lean:156-183 headProofPW — **THEOREM 1
for `headProofPW`**, in answer shape. -/
theorem headProofPW_spec' (fuel : Nat) (s₀ : AState) (h : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store h = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.headProofPW fe fuel h
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store h = some x →
        r = ConLeche.headProofPW env.find? x; ⊤⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/PropRead.lean:124-134 proofPW — **THEOREM 1
for `proofPW`**, in answer shape: `annotPwLam` calls it on the knot's
`annotate` answer, and `notProofFast` / `isProofFast` on `propIrrel`'s
subjects. -/
theorem proofPW_spec' (fuel : Nat) (s₀ : AState) (a : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store a = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.proofPW fe fuel a
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store a = some x →
        r = ConLeche.proofPW env.find? x; ⊤⦄ := by
  sorry

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
    ⦃fun b s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store a = some x →
        b = ConLeche.notProofFast env.find? x; ⊤⦄ := by
  have hb := proofPW_spec' (mode := mode) (env := env) (fe := fe) fuel s₀ a
    hok hpre
  vcgen [ConRon.Arena.notProofFast, hb]
  all_goals (bridge_peel; subst_vars)
  all_goals clear_tag_hyps
  all_goals
    (rename_i hr
     refine ⟨‹_›, ‹_›, ‹_›, fun x hx => ?_⟩
     simp only [ConLeche.notProofFast, ← hr x hx])

/-- con-leche: ConLeche/Kernel/PropRead.lean:148-153 isProofFast — **THEOREM
1 for `isProofFast`**, in answer shape. -/
theorem isProofFast_spec' (fuel : Nat) (s₀ : AState) (a : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ x, denoteE s₀.store a = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.isProofFast fe fuel a
    ⦃fun b s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ ∀ x, denoteE s₀.store a = some x →
        b = ConLeche.isProofFast env.find? x; ⊤⦄ := by
  have hb := proofPW_spec' (mode := mode) (env := env) (fe := fe) fuel s₀ a
    hok hpre
  vcgen [ConRon.Arena.isProofFast, hb]
  all_goals (bridge_peel; subst_vars)
  all_goals clear_tag_hyps
  all_goals
    (rename_i hr
     refine ⟨‹_›, ‹_›, ‹_›, fun x hx => ?_⟩
     simp only [ConLeche.isProofFast, ← hr x hx])

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
  have hnp := fun (s : AState) (e : EIdx) =>
    notProofFast_spec' (mode := mode) (env := env) (fe := fe) coreWalkFuel s e
  have hip := fun (s : AState) (e : EIdx) =>
    isProofFast_spec' (mode := mode) (env := env) (fe := fe) coreWalkFuel s e
  have hi := hsim.inferIO'
  have hn := hsim.whnf'
  vcgen [ConRon.Arena.propIrrel, ConRon.Arena.zeroLevel,
    ConRon.Arena.liftFueled, hnp, hip, hi, hn,
    lvlEq?_spec (mode := mode) (env := env) (fe := fe)]
  all_goals (bridge_peel; subst_vars)
  all_goals clear_tag_hyps
  -- the callees' `CheckOK` and pin preconditions
  case vc4 | vc8 | vc10 | vc12 | vc14 | vc18 | vc20 | vc22 | vc24 | vc26 | vc28
    | vc30 => assumption
  -- the two zero pins' (the port's `prop_sorts_zero_right` re-reads it)
  case vc5 | vc15 => exact CheckOK.pins (by assumption)
  -- the two subjects' denotations, carried to the state each call runs in
  case vc31 => exact ⟨x, hda⟩
  case vc29 =>
    rename_i _ hst_s0_s1 _ _
    exact ⟨y, by rw [hst_s0_s1]; exact hdb⟩
  case vc27 =>
    rename_i hst_s0_s1 hst_s1_s2 _ _ _ _
    exact ⟨x, by rw [hst_s1_s2, hst_s0_s1]; exact hda⟩
  case vc25 =>
    rename_i s3 r2 s2 r1 s1 hg0 r0 s0 hck_s2 hck_s1 hck_s0 hst_s2_s3 hst_s1_s2 hst_s0_s1
      hp_s2_s3 hnp_a hp_s1_s2 hnp_b hp_s0_s1 hip_a
    exact ⟨y, by rw [hst_s0_s1, hst_s1_s2, hst_s2_s3]; exact hdb⟩
  case vc23 =>
    rename_i s4 r3 s3 r2 s2 hg1 r1 s1 r0 s0 hg0 hck_s3 hck_s2 hck_s1 hck_s0 hst_s3_s4
      hst_s2_s3 hst_s1_s2 hst_s0_s1 hp_s3_s4 hnp_a hp_s2_s3 hnp_b hp_s1_s2 hip_a hp_s0_s1
      hip_b
    exact ⟨x, by rw [hst_s0_s1, hst_s1_s2, hst_s2_s3, hst_s3_s4]; exact hda,
      hwa⟩
  case vc21 =>
    rename_i s5 r4 s4 r3 s3 hg1 r2 s2 r1 s1 hg0 s0 hck_s4 hck_s3 hck_s2 hck_s1 hck_s0
      hst_s4_s5 hst_s3_s4 hst_s2_s3 hst_s1_s2 hx_s1_s0 hp_s4_s5 hnp_a hp_s3_s4 hnp_b
      hp_s2_s3 hip_a hp_s1_s2 hip_b hp_s0_s1 hio_a
    exact SimE.exists_denote (hio_a x
      (by rw [hst_s1_s2, hst_s2_s3, hst_s3_s4, hst_s4_s5]; exact hda))
  case vc19 =>
    rename_i s6 r5 s5 r4 s4 hg1 r3 s3 r2 s2 hg0 s1 r0 s0 hck_s5 hck_s4 hck_s3 hck_s2 hck_s1
      hck_s0 hst_s5_s6 hst_s4_s5 hst_s3_s4 hst_s2_s3 hx_s2_s1 hx_s1_s0 hp_s5_s6 hnp_a
      hp_s4_s5 hnp_b hp_s3_s4 hip_a hp_s2_s3 hip_b hp_s1_s2 hio_a hp_s0_s1 hio_r1
    obtain ⟨ta, hta, _, _⟩ := hio_a x
      (by rw [hst_s2_s3, hst_s3_s4, hst_s4_s5, hst_s5_s6]; exact hda)
    exact SimE.exists_denote (hio_r1 ta hta)
  case vc13 =>
    rename_i s8 r7 s7 r6 s6 hg1 r5 s5 r4 s4 hg0 s3 r2 s2 u0 s1 s0 hck_s7 hck_s6 hck_s5
      hck_s4 hck_s3 hck_s2 hck_s0 hst_s7_s8 hst_s6_s7 hst_s5_s6 hst_s4_s5 hx_s4_s3 hx_s3_s2
      hst_s0_s1 hp_s7_s8 hnp_a hp_s6_s7 hnp_b hp_s5_s6 hip_a hp_s4_s5 hip_b hp_s3_s4 hio_a
      hp_s2_s3 hio_r3 hp_s0_s1 hz_r0 hck_s1 hx_s2_s1 hp_s1_s2 hwh_r2 hvs_r1 heq_u0
    have hx : Ext s8.store s0.store :=
      ((((((ext_of_store_eq hst_s7_s8).trans (ext_of_store_eq hst_s6_s7)).trans
        (ext_of_store_eq hst_s5_s6)).trans (ext_of_store_eq hst_s4_s5)).trans
        ((hx_s4_s3.trans hx_s3_s2).trans hx_s2_s1)).trans
        (ext_of_store_eq hst_s0_s1))
    exact ⟨y, denote_ext hdb hx, hwb⟩
  case vc11 =>
    rename_i s9 r8 s8 r7 s7 hg1 r6 s6 r5 s5 hg0 s4 r3 s3 u0 s2 s1 s0 hck_s8 hck_s7 hck_s6
      hck_s5 hck_s4 hck_s3 hck_s1 hck_s0 hst_s8_s9 hst_s7_s8 hst_s6_s7 hst_s5_s6 hx_s5_s4
      hx_s4_s3 hst_s1_s2 hx_s1_s0 hp_s8_s9 hnp_a hp_s7_s8 hnp_b hp_s6_s7 hip_a hp_s5_s6
      hip_b hp_s4_s5 hio_a hp_s3_s4 hio_r4 hp_s1_s2 hp_s0_s1 hio_b hz_r1 hck_s2 hx_s3_s2
      hp_s2_s3 hwh_r3 hvs_r2 heq_u0
    have hx : Ext s9.store s1.store :=
      ((((((ext_of_store_eq hst_s8_s9).trans (ext_of_store_eq hst_s7_s8)).trans
        (ext_of_store_eq hst_s6_s7)).trans (ext_of_store_eq hst_s5_s6)).trans
        ((hx_s5_s4.trans hx_s4_s3).trans hx_s3_s2)).trans
        (ext_of_store_eq hst_s1_s2))
    exact SimE.exists_denote (hio_b y (denote_ext hdb hx))
  case vc9 =>
    rename_i s10 r9 s9 r8 s8 hg1 r7 s7 r6 s6 hg0 s5 r4 s4 u0 s3 s2 s1 r0 s0 hck_s9 hck_s8
      hck_s7 hck_s6 hck_s5 hck_s4 hck_s2 hck_s1 hck_s0 hst_s9_s10 hst_s8_s9 hst_s7_s8
      hst_s6_s7 hx_s6_s5 hx_s5_s4 hst_s2_s3 hx_s2_s1 hx_s1_s0 hp_s9_s10 hnp_a hp_s8_s9 hnp_b
      hp_s7_s8 hip_a hp_s6_s7 hip_b hp_s5_s6 hio_a hp_s4_s5 hio_r5 hp_s2_s3 hp_s1_s2 hio_b
      hp_s0_s1 hio_r1 hz_r2 hck_s3 hx_s4_s3 hp_s3_s4 hwh_r4 hvs_r3 heq_u0
    have hx : Ext s10.store s2.store :=
      ((((((ext_of_store_eq hst_s9_s10).trans (ext_of_store_eq hst_s8_s9)).trans
        (ext_of_store_eq hst_s7_s8)).trans (ext_of_store_eq hst_s6_s7)).trans
        ((hx_s6_s5.trans hx_s5_s4).trans hx_s4_s3)).trans
        (ext_of_store_eq hst_s2_s3))
    obtain ⟨tb, htb, _, _⟩ := hio_b y (denote_ext hdb hx)
    exact SimE.exists_denote (hio_r1 tb htb)
  -- the "not a proof" arm refuses
  case vc1 =>
    rename_i s2 r1 s1 r0 s0 hg0 hck_s1 hck_s0 hst_s1_s2 hst_s0_s1 hp_s1_s2 hnp_a hp_s0_s1
      hnp_b
    refine ⟨hck_s0, ext_of_store_eq (hst_s0_s1.trans hst_s1_s2),
      hp_s0_s1.trans hp_s1_s2, 0, propIrrel_no ?_⟩
    rw [hnp_a x hda, hnp_b y (by rw [hst_s1_s2]; exact hdb)] at hg0
    exact hg0
  -- the "yes" arm licenses
  case vc2 =>
    rename_i s4 r3 s3 r2 s2 hg1 r1 s1 r0 s0 hg0 hck_s3 hck_s2 hck_s1 hck_s0 hst_s3_s4
      hst_s2_s3 hst_s1_s2 hst_s0_s1 hp_s3_s4 hnp_a hp_s2_s3 hnp_b hp_s1_s2 hip_a hp_s0_s1
      hip_b
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
  case vc3 =>
    rename_i s12 r10 s11 r9 s10 hg1 r8 s9 r7 s8 hg0 s7 r5 s6 r4 u1 r3 s5 s4 s3 r1 s2 u0 s1
      s0 hck_s11 hck_s10 hck_s9 hck_s8 hck_s7 hck_s6 hck_s4 hck_s3 hck_s2 hck_s0 hst_s11_s12
      hst_s10_s11 hst_s9_s10 hst_s8_s9 hx_s8_s7 hx_s7_s6 hst_s4_s5 hx_s4_s3 hx_s3_s2
      hst_s0_s1 hp_s11_s12 hnp_a hp_s10_s11 hnp_b hp_s9_s10 hip_a hp_s8_s9 hip_b hp_s7_s8
      hio_a hp_s6_s7 hio_r6 hp_s4_s5 hp_s3_s4 hio_b hp_s2_s3 hio_r2 hp_s0_s1 hz_r3 hck_s5
      hx_s6_s5 hp_s5_s6 hwh_r5 hvs_r4 heq_u1 hz2 hck_s1 hx_s2_s1 hp_s1_s2 hwh_r1 hvs_r0
      heq_u0
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
    rw [hvT] at hlu'; rw [hz2] at hlv'
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
  case vc6 =>
    rename_i s11 r10 s10 r9 s9 hg1 r8 s8 r7 s7 hg0 s6 r5 s5 r4 u0 s4 s3 s2 r1 s1 s0 x1 hnv0
      hck_s10 hck_s9 hck_s8 hck_s7 hck_s6 hck_s5 hck_s3 hck_s2 hck_s1 hst_s10_s11 hst_s9_s10
      hst_s8_s9 hst_s7_s8 hx_s7_s6 hx_s6_s5 hst_s3_s4 hx_s3_s2 hx_s2_s1 hp_s10_s11 hnp_a
      hp_s9_s10 hnp_b hp_s8_s9 hip_a hp_s7_s8 hip_b hp_s6_s7 hio_a hp_s5_s6 hio_r6 hp_s3_s4
      hp_s2_s3 hio_b hp_s1_s2 hio_r2 hz_r3 hck_s4 hx_s5_s4 hp_s4_s5 hwh_r5 hvs_r4 heq_u0
      hck_s0 hx_s1_s0 hp_s0_s1 hwh_r1 hv_r0
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
  -- round 4: the tag-first twin's `else` arm (the whnf answer does not carry
  -- the `sort` TAG; its view comes back from its denotation)
  case vc7 =>
    rename_i s11 r10 s10 r9 s9 hg1 r8 s8 r7 s7 hg0 s6 r5 s5 r4 u0 s4 s3 s2 r1 s1 s0 htag
      hck_s10 hck_s9 hck_s8 hck_s7 hck_s6 hck_s5 hck_s3 hck_s2 hck_s1 hck_s0 hst_s10_s11
      hst_s9_s10 hst_s8_s9 hst_s7_s8 hx_s7_s6 hx_s6_s5 hst_s3_s4 hx_s3_s2 hx_s2_s1 hx_s1_s0
      hp_s10_s11 hnp_a hp_s9_s10 hnp_b hp_s8_s9 hip_a hp_s7_s8 hip_b hp_s6_s7 hio_a hp_s5_s6
      hio_r6 hp_s3_s4 hp_s2_s3 hio_b hp_s1_s2 hio_r2 hp_s0_s1 hwh_r1 hz_r3 hck_s4 hx_s5_s4
      hp_s4_s5 hwh_r5 hvs_r4 heq_u0
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
    obtain ⟨vv, hvv⟩ := denoteE_view hw2
    have hns := denote_not_sort hck_s0.state.wf hvv hw2 (fun u hh => view_tagOf_ne hvv (t := ETag.sort) htag (by rw [hh]; rfl))
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
  case vc16 =>
    rename_i s7 r6 s6 r5 s5 hg1 r4 s4 r3 s3 hg0 s2 r1 s1 s0 x1 hnv0 hck_s6 hck_s5 hck_s4
      hck_s3 hck_s2 hck_s1 hst_s6_s7 hst_s5_s6 hst_s4_s5 hst_s3_s4 hx_s3_s2 hx_s2_s1
      hp_s6_s7 hnp_a hp_s5_s6 hnp_b hp_s4_s5 hip_a hp_s3_s4 hip_b hp_s2_s3 hio_a hp_s1_s2
      hio_r2 hck_s0 hx_s1_s0 hp_s0_s1 hwh_r1 hv_r0
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
  -- round 4: the tag-first twin's `else` arm (the whnf answer does not carry
  -- the `sort` TAG; its view comes back from its denotation)
  case vc17 =>
    rename_i s7 r6 s6 r5 s5 hg1 r4 s4 r3 s3 hg0 s2 r1 s1 s0 htag hck_s6 hck_s5 hck_s4 hck_s3
      hck_s2 hck_s1 hck_s0 hst_s6_s7 hst_s5_s6 hst_s4_s5 hst_s3_s4 hx_s3_s2 hx_s2_s1
      hx_s1_s0 hp_s6_s7 hnp_a hp_s5_s6 hnp_b hp_s4_s5 hip_a hp_s3_s4 hip_b hp_s2_s3 hio_a
      hp_s1_s2 hio_r2 hp_s0_s1 hwh_r1
    have hx73 : Ext s7.store s3.store :=
      (((ext_of_store_eq hst_s6_s7).trans (ext_of_store_eq hst_s5_s6)).trans
        (ext_of_store_eq hst_s4_s5)).trans (ext_of_store_eq hst_s3_s4)
    refine ⟨hck_s0, hx73.trans ((hx_s3_s2.trans hx_s2_s1).trans hx_s1_s0),
      hp_s0_s1.trans (hp_s1_s2.trans (hp_s2_s3.trans (hp_s3_s4.trans
        (hp_s4_s5.trans (hp_s5_s6.trans hp_s6_s7))))), ?_⟩
    obtain ⟨ta, hta, _, F1, hF1⟩ := hio_a x (denote_ext hda hx73)
    obtain ⟨tta, htta, _, F2, hF2⟩ := hio_r2 ta hta
    obtain ⟨w, hw, _, F3, hF3⟩ := hwh_r1 tta htta
    obtain ⟨vv, hvv⟩ := denoteE_view hw
    have hns := denote_not_sort hck_s0.state.wf hvv hw (fun u hh => view_tagOf_ne hvv (t := ETag.sort) htag (by rw [hh]; rfl))
    rw [hnp_a x hda, hnp_b y (by rw [hst_s6_s7]; exact hdb)] at hg1
    rw [hip_a x (by rw [hst_s5_s6, hst_s6_s7]; exact hda),
      hip_b y (by rw [hst_s4_s5, hst_s5_s6, hst_s6_s7]; exact hdb)] at hg0
    exact ⟨F1 + F2 + F3, propIrrel_slow_a (by simpa using hg1)
      (by simpa using hg0)
      (ConLeche.inferTypeIO_mono (by omega) hF1)
      (ConLeche.inferTypeIO_mono (by omega) hF2)
      (ConLeche.whnf_mono (by omega) hF3) hns⟩

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

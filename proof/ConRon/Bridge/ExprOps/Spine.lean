/-
# `ConRon.Bridge.ExprOps.Spine` — Theorem 1 for the spine and telescope twins

DESIGN §8.2's Theorem 1 at the twins of `Arena/ExprOps.lean` that
walk an APPLICATION SPINE or a BINDER TELESCOPE rather than the handle DAG:
`getAppFn`, `getAppArgs`, `mkAppN`, `mkAppNFrom`, `stripLams`, `stripPis`,
`piResult`, `fvarTypeD` and `instSpine`.

## What makes this group different from `ExprOps/Inst1`

1. **None of them takes a memo, and half take no fuel.**  The
   recursion is structural on a binder count (`stripPis`), on an
   argument list (`mkAppN`, `instSpine`) or on a `Nat` cursor
   (`mkAppNFrom`), so the theorems are plain inductions over
   that argument and not fuel inductions, and the postcondition frames no
   memo table at all.  The six READ-ONLY twins (`getAppFn`, `getAppArgs`,
   `stripLams`, `stripPis`, `piResult`, `fvarTypeD`) intern nothing, so their
   postcondition is `s' = s₀` and the answer relation's two stores coincide.
2. **One of them is arena-only.**  `mkAppNFrom` applies a PUSH-ORDER `Array`
   from a cursor.  Its doc comment says `con-leche: none` and its theorem is
   exactly the fact its callers consume: `mkAppNFrom`'s pure function is
   `mkAppN`'s at the dropped prefix, so `mkAppN_spec` composes with it.

## The proofs

Every theorem is `sym only [bridge_grind, …] => vcgen [f, callee specs…] <;>
finish`, inside the induction its recursion needs.  `grind` sees the
tag-first arm's projection read as a `DenoteView` fact on the subject
(`Bridge/Grind.lean` §6), the subject's denotation as its constructor at its
projections (the tag-guarded `exprTag_*` etas), the answer relations as
`MapRel`/`MapRel2` equations, and each con-leche function this group compares
against as equations over tags and projections (§3 below): its constructor
clause, and its catch-all as one equation keyed on the function and the tag.

## The answer relations

`Bridge/Rel.lean` has the shapes the DAG walks need; this group needs two
more, declared here because they are this group's result types:

* `RelBP` — an `Option (List EIdx × EIdx)` answer (`stripLams`, `stripPis`);
* `RelEA` — an answer with an argument LIST as a second subject (`mkAppN`,
  `mkAppNFrom`, `instSpine`).

Everything else reuses `Rel.lean`: `RelE` for `getAppFn`, `piResult` and
`fvarTypeD`, and `RelEL` for `getAppArgs`.

## The axiom check

**Nothing in this file is unproved.**  `#print axioms` at the end reports
`[propext, Classical.choice, Quot.sound]` for every twin.
-/
import ConRon.Bridge.ExprOps.Inst1

/-! ## Vocabulary candidates (for Bridge/Grind.lean) -/

namespace ConRon.Bridge

open ConLeche ConRon.Arena

/-- con-leche: none — **an answer relation at two optional subjects**: whatever
the subjects `oa`, `ob` denote, the answer `o` denotes their image under `g`
(`MapRel` with a second subject). -/
def MapRel2 {α β γ : Type} (g : α → β → γ) : Option α → Option β → Option γ → Prop
  | some a, some b, o => o = some (g a b)
  | _, _, _ => True

/-- con-leche: none — `MapRel2` at two denoting subjects, as an equation. -/
@[bridge_grind =] theorem MapRel2.some_eq {α β γ : Type} (g : α → β → γ) (a : α) (b : β)
    (o : Option γ) : MapRel2 g (some a) (some b) o = (o = some (g a b)) := rfl

/-- con-leche: none — the `fvar` type projection read means the index
projection reads too (one row of the `fvar` array). -/
theorem viewFVarIdx_of_viewFVarTy {st : EStore} {i ty : EIdx}
    (h : st.viewFVarTy i = some ty) : ∃ k, st.viewFVarIdx i = some k := by
  unfold EStore.viewFVarTy at h
  unfold EStore.viewFVarIdx EStore.persGetFVarIdx
  unfold EStore.persGetFVarTy at h
  split at h
  · simp only [ETables.getFVarTy, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, -⟩ := h
    exact ⟨r.idx, by simp [*, ETables.getFVarIdx]⟩
  · split at h
    · simp only [ETables.getFVarTy, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, -⟩ := h
      exact ⟨r.idx, by simp [*, ETables.getFVarIdx]⟩
    · cases h

/-- con-leche: none — the `fvar` TYPE projection read under its tag gives the
view (`view_of_viewFVarIdx`'s twin), guarded at that read. -/
theorem view_of_viewFVarTy {st : EStore} {i ty : EIdx}
    (htg : i.tag = ETag.fvar) (h : st.viewFVarTy i = some ty) :
    ∃ k, st.view i = some (.fvar k ty) := by
  obtain ⟨k, hk⟩ := viewFVarIdx_of_viewFVarTy h
  exact ⟨k, view_of_viewFVar htg hk h⟩
grind_pattern [bridge_grind] view_of_viewFVarTy => st.viewFVarTy i, some ty where
  guard st.viewFVarTy i = some ty

/-- con-leche: none — a handle list extended at the END denotes its
denotation's `concat`. -/
@[bridge_grind =] theorem denoteEList_concat_eq (st : EStore) (a : EIdx) :
    ∀ rs : List EIdx, Frontend.denoteEList st (rs ++ [a]) =
      opt2 List.concat (Frontend.denoteEList st rs) (denoteE st a)
  | [] => by
    simp only [List.nil_append, Frontend.denoteEList, opt2]
    cases denoteE st a <;> rfl
  | j :: js => by
    simp only [List.cons_append, Frontend.denoteEList, denoteEList_concat_eq st a js, opt2]
    cases denoteE st j <;> cases Frontend.denoteEList st js <;> cases denoteE st a <;> rfl

attribute [bridge_grind =] List.concat_eq_append

end ConRon.Bridge

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

/-! ## 1. The answer relations this group adds

Modelled on `Bridge/Rel.lean`'s `RelEO`: an `Option`-valued answer gets a
`denote…` function that turns the handle side into `Option (Option …)`, so
that the relation has `RelE`'s shape exactly.  For `grind` each relation is
an equation to `MapRel` (`MapRel2`) on the denotation terms, registered
locally. -/

/-- con-leche: none — the denotation of a BINDER list: the domains, handle by
handle (a binder carries its type and nothing else). -/
def denoteBL (st : EStore) : List EIdx → Option (List Expr)
  | [] => some []
  | t :: bs =>
    match denoteE st t, denoteBL st bs with
    | some x, some xs => some (x :: xs)
    | _, _ => none

/-- con-leche: none — the denotation of `stripLams`' result shape. -/
def denoteBP (st : EStore) : Option (List EIdx × EIdx) →
    Option (Option (List Expr × Expr))
  | none => some none
  | some (bs, e) =>
    match denoteBL st bs, denoteE st e with
    | some xs, some x => some (some (xs, x))
    | _, _ => none

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — the answer relation at
`stripLams`/`stripPis`' result shape. -/
def RelBP (f : Expr → Option (List Expr × Expr))
    (st : EStore) (c : EIdx) (st' : EStore)
    (r : Option (List EIdx × EIdx)) : Prop :=
  ∀ e, denoteE st c = some e → denoteBP st' r = some (f e)

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — the answer relation with
an argument LIST as a second subject (`mkAppN`, `mkAppNFrom`, `instSpine`).
The list is quantified inside the relation, as `RelE` quantifies the first
subject: a recursion that carries the list forward cannot take its
denotation as a named `List Expr` in the precondition (the recursive call's
side goal would carry a metavariable). -/
def RelEA (F : Expr → List Expr → Expr) (st : EStore) (c : EIdx)
    (args : List EIdx) (st' : EStore) (r : EIdx) : Prop :=
  ∀ e es, denoteE st c = some e → Frontend.denoteEList st args = some es →
    denoteE st' r = some (F e es)

/-- con-leche: none — `RelBP` IS `MapRel` on the subject's denotation and the
answer's. -/
theorem relBP_eq_mapRel (f : Expr → Option (List Expr × Expr)) (st : EStore)
    (c : EIdx) (st' : EStore) (r : Option (List EIdx × EIdx)) :
    RelBP f st c st' r = MapRel f (denoteE st c) (denoteBP st' r) :=
  forall_eq_mapRel _ _ _

/-- con-leche: none — `RelEA` IS `MapRel2` on the two subjects' denotations
and the answer's. -/
theorem relEA_eq_mapRel2 (F : Expr → List Expr → Expr) (st : EStore)
    (c : EIdx) (args : List EIdx) (st' : EStore) (r : EIdx) :
    RelEA F st c args st' r =
      MapRel2 F (denoteE st c) (Frontend.denoteEList st args) (denoteE st' r) := by
  unfold RelEA
  cases denoteE st c <;> cases Frontend.denoteEList st args <;> simp [MapRel2]

attribute [local bridge_grind =] relBP_eq_mapRel relEA_eq_mapRel2

/-! ### `denoteBP` as equations

A peel's answer is built binder by binder, so its denotation is stated the
same way: the empty peel at a body, and one binder consed onto a peel.  The
pure sides are named functions (`bpNil`, `bpCons`, `consB`), so that no `fun`
reaches `grind`. -/

/-- con-leche: none — a peel's answer with one more binder in front. -/
def consB (ty : Expr) (p : List Expr × Expr) : List Expr × Expr := (ty :: p.1, p.2)

/-- con-leche: none — the empty peel at a body. -/
def bpNil (x : Expr) : Option (List Expr × Expr) := some ([], x)

/-- con-leche: none — an optional peel with one more binder in front. -/
def bpCons (x : Expr) (o : Option (List Expr × Expr)) : Option (List Expr × Expr) :=
  o.map (consB x)

/-- con-leche: none — the failed peel denotes `none`. -/
theorem denoteBP_none_eq (st : EStore) : denoteBP st none = some none := rfl

/-- con-leche: none — the empty peel at a body. -/
theorem denoteBP_nil_eq (st : EStore) (h : EIdx) :
    denoteBP st (some ([], h)) = (denoteE st h).map bpNil := by
  simp only [denoteBP, denoteBL]
  cases denoteE st h <;> rfl

/-- con-leche: none — one binder consed onto a peel. -/
theorem denoteBP_cons_eq (st : EStore) (t : EIdx) (bs : List EIdx) (e : EIdx) :
    denoteBP st (some (t :: bs, e)) =
      opt2 bpCons (denoteE st t) (denoteBP st (some (bs, e))) := by
  simp only [denoteBP, denoteBL, opt2, bpCons]
  cases denoteE st t <;> cases denoteBL st bs <;> cases denoteE st e <;> rfl

attribute [local bridge_grind =] bpNil bpCons denoteBP_none_eq denoteBP_nil_eq
  denoteBP_cons_eq

/-! ## 2. Handle lists -/

/-- con-leche: none — a denoting handle list denotes head and tail. -/
theorem denoteEList_cons_isSome {st : EStore} {a : EIdx}
    {as : List EIdx}
    (h : (Frontend.denoteEList st (a :: as)).isSome = true) :
    (denoteE st a).isSome = true ∧
      (Frontend.denoteEList st as).isSome = true := by
  simp only [Frontend.denoteEList] at h
  cases ha : denoteE st a with
  | none => rw [ha] at h; simp at h
  | some x =>
    cases has : Frontend.denoteEList st as with
    | none => rw [ha, has] at h; simp at h
    | some xs => exact ⟨rfl, rfl⟩

/-- con-leche: none — a handle list's denotation, extended by one at the END.
`getAppArgs` answers `as ++ [a]` (outermost last). -/
theorem denoteEList_snoc {st : EStore} {a : EIdx} {ea : Expr}
    (ha : denoteE st a = some ea) :
    ∀ (rs : List EIdx) (xs : List Expr),
      Frontend.denoteEList st rs = some xs →
        Frontend.denoteEList st (rs ++ [a]) = some (xs ++ [ea]) := by
  intro rs xs h
  simp only [denoteEList_concat_eq, h, ha, opt2, List.concat_eq_append]

/-! ## 3. The con-leche functions as equations

Each function this group compares against, as `grind` needs it: the
constructor clause (`Expr.getAppFn.eq_1`, …, passed to `sym`) and the
catch-all as one equation keyed on the function AND the tag term, so that it
fires only where the walk has tested the tag.  The two peels and `fvarTypeD`,
whose recursion (if any) is on a count, are one equation over the tag and the
projections each (`peelPis_succ_eq`'s shape, `Core/Walks/Proj.lean`). -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:793-796 getAppFn — the
fallthrough clause, as a lemma. -/
theorem getAppFn_of_not_app {e : Expr} (h : ∀ x y, e ≠ Expr.app x y) :
    Expr.getAppFn e = e := by
  cases e with
  | app f a => exact absurd rfl (h f a)
  | _ => simp [Expr.getAppFn]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:798-801 getAppArgs — the same for
`getAppArgs`. -/
theorem getAppArgs_of_not_app {e : Expr} (h : ∀ x y, e ≠ Expr.app x y) :
    Expr.getAppArgs e = [] := by
  cases e with
  | app f a => exact absurd rfl (h f a)
  | _ => simp [Expr.getAppArgs]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:793-796 getAppFn — the catch-all
at a tag that is not `app`. -/
theorem getAppFn_leaf {e : Expr} (h : ¬ exprTag e = ETag.app) : Expr.getAppFn e = e := by
  cases e <;> simp_all [exprTag, Expr.getAppFn]
local grind_pattern [bridge_grind] getAppFn_leaf => Expr.getAppFn e, exprTag e

/-- con-leche: ConLeche/Kernel/ExprOps.lean:798-801 getAppArgs — the
catch-all at a tag that is not `app`. -/
theorem getAppArgs_leaf {e : Expr} (h : ¬ exprTag e = ETag.app) :
    Expr.getAppArgs e = [] := by
  cases e <;> simp_all [exprTag, Expr.getAppArgs]
local grind_pattern [bridge_grind] getAppArgs_leaf => Expr.getAppArgs e, exprTag e

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1164-1168 piResult — the
catch-all at a tag that is not `forallE`. -/
theorem piResult_leaf {e : Expr} (h : ¬ exprTag e = ETag.forallE) :
    Expr.piResult e = e := by
  cases e <;> simp_all [exprTag, Expr.piResult]
local grind_pattern [bridge_grind] piResult_leaf => Expr.piResult e, exprTag e

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1298-1303 fvarTypeD — as ONE
equation over the tag and the type projection. -/
theorem fvarTypeD_eq (e : Expr) :
    Expr.fvarTypeD e = if exprTag e = ETag.fvar then exprFVarType e else e := by
  cases e <;> simp [Expr.fvarTypeD, exprTag, exprFVarType, ETag.forallE, ETag.bvar, ETag.fvar,
    ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.letE, ETag.lit, ETag.proj]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1156-1162 stripPis — the
successor clause as ONE equation over the tag and the binder projections. -/
theorem stripPis_succ_eq (k : Nat) (e : Expr) :
    Expr.stripPis (k + 1) e = if exprTag e = ETag.forallE then
      (Expr.stripPis k (exprBody e)).map (consB (exprBinderType e)) else none := by
  cases e <;> simp [Expr.stripPis, exprTag, exprBody, exprBinderType, ETag.forallE,
    ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.letE, ETag.lit,
    ETag.proj] <;> rfl

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1148-1154 stripLams — the same at
a λ binder. -/
theorem stripLams_succ_eq (k : Nat) (e : Expr) :
    Expr.stripLams (k + 1) e = if exprTag e = ETag.lam then
      (Expr.stripLams k (exprBody e)).map (consB (exprBinderType e)) else none := by
  cases e <;> simp [Expr.stripLams, exprTag, exprBody, exprBinderType, ETag.forallE,
    ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.letE, ETag.lit,
    ETag.proj] <;> rfl

/-! ## 4. The application spine -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:793-796 getAppFn — **THEOREM 1**
for `getAppFn`.  Read-only: the walk peels `app` nodes and answers a handle
it was already holding, so the store is unchanged and the answer relation's
two stores coincide. -/
theorem getAppFn_spec : ∀ (fuel : Nat) (s₀ : AState) (h : EIdx),
    StateOK s₀ → (denoteE s₀.store h).isSome = true →
    ⦃fun s => s = s₀⦄ getAppFn fuel h
    ⦃fun r s' => s' = s₀ ∧ RelE Expr.getAppFn s₀.store h s₀.store r; ⊤⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro s₀ h _ _
    sym only [bridge_grind] => vcgen [getAppFn] <;> finish
  | succ fuel ih =>
    intro s₀ h hok hden
    sym only [bridge_grind, Expr.getAppFn.eq_1] => vcgen [getAppFn, ih] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:798-801 getAppArgs — **THEOREM 1**
for `getAppArgs`.  Read-only, and the one twin of this group whose answer is
a LIST of handles, so `RelEL` is the relation. -/
theorem getAppArgs_spec : ∀ (fuel : Nat) (s₀ : AState) (h : EIdx),
    StateOK s₀ → (denoteE s₀.store h).isSome = true →
    ⦃fun s => s = s₀⦄ getAppArgs fuel h
    ⦃fun rs s' => s' = s₀ ∧ RelEL Expr.getAppArgs s₀.store h s₀.store rs; ⊤⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro s₀ h _ _
    sym only [bridge_grind] => vcgen [getAppArgs] <;> finish
  | succ fuel ih =>
    intro s₀ h hok hden
    sym only [bridge_grind, Expr.getAppArgs.eq_1] => vcgen [getAppArgs, ih] <;> finish

/-! ## 5. The read-only telescope walks -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1164-1168 piResult — **THEOREM 1**
for `piResult`: the body of a syntactic `∀`-telescope.  Read-only. -/
theorem piResult_spec : ∀ (fuel : Nat) (s₀ : AState) (h : EIdx),
    StateOK s₀ → (denoteE s₀.store h).isSome = true →
    ⦃fun s => s = s₀⦄ piResult fuel h
    ⦃fun r s' => s' = s₀ ∧ RelE Expr.piResult s₀.store h s₀.store r; ⊤⦄ := by
  intro fuel
  induction fuel with
  | zero =>
    intro s₀ h _ _
    sym only [bridge_grind] => vcgen [piResult] <;> finish
  | succ fuel ih =>
    intro s₀ h hok hden
    sym only [bridge_grind, Expr.piResult.eq_1] => vcgen [piResult, ih] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1298-1303 fvarTypeD — **THEOREM 1**
for `fvarTypeD`: the type annotation of a free-variable leaf, the expression
itself otherwise.  No fuel and no recursion at all. -/
theorem fvarTypeD_spec (s₀ : AState) (h : EIdx) (hok : StateOK s₀)
    (hden : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => s = s₀⦄ fvarTypeD h
    ⦃fun r s' => s' = s₀ ∧ RelE Expr.fvarTypeD s₀.store h s₀.store r; ⊤⦄ := by
  sym only [bridge_grind, fvarTypeD_eq] => vcgen [fvarTypeD] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1156-1162 stripPis — **THEOREM 1**
for `stripPis`: strip `k` leading `∀`s.  Structural on `k`, so the induction
is on `k` and there is no fuel; read-only, so the answer relation's two
stores coincide. -/
theorem stripPis_spec : ∀ (k : Nat) (s₀ : AState) (h : EIdx),
    StateOK s₀ → (denoteE s₀.store h).isSome = true →
    ⦃fun s => s = s₀⦄ stripPis k h
    ⦃fun r s' => s' = s₀ ∧ RelBP (Expr.stripPis k) s₀.store h s₀.store r; ⊤⦄ := by
  intro k
  induction k with
  | zero =>
    intro s₀ h hok hden
    sym only [bridge_grind, Expr.stripPis.eq_1] => vcgen [stripPis] <;> finish
  | succ k ih =>
    intro s₀ h hok hden
    sym only [bridge_grind, stripPis_succ_eq] => vcgen [stripPis, ih] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1148-1154 stripLams —
**THEOREM 1** for `stripLams`, `stripPis`' λ twin. -/
theorem stripLams_spec : ∀ (k : Nat) (s₀ : AState) (h : EIdx),
    StateOK s₀ → (denoteE s₀.store h).isSome = true →
    ⦃fun s => s = s₀⦄ stripLams k h
    ⦃fun r s' => s' = s₀ ∧
        RelBP (Expr.stripLams k) s₀.store h s₀.store r; ⊤⦄ := by
  intro k
  induction k with
  | zero =>
    intro s₀ h hok hden
    sym only [bridge_grind, Expr.stripLams.eq_1] => vcgen [stripLams] <;> finish
  | succ k ih =>
    intro s₀ h hok hden
    sym only [bridge_grind, stripLams_succ_eq] => vcgen [stripLams, ih] <;> finish

/-! ## 6. The two argument folds

These two intern, so their postcondition carries `Ext` and the four frame
equations.  None of them takes a memo: `internE`'s own spec frames
`s'.memos = s₀.memos`, so `MemoOK` never appears. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:803-806 mkAppN — **THEOREM 1**
for `mkAppN`: apply to a list of arguments.  Structural on the list, so the
induction is on the list and there is no fuel. -/
theorem mkAppN_spec : ∀ (args : List EIdx) (s₀ : AState) (f : EIdx),
    StateOK s₀ → (denoteE s₀.store f).isSome = true →
    (Frontend.denoteEList s₀.store args).isSome = true →
    ⦃fun s => s = s₀⦄ mkAppN f args
    ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧ s'.memos = s₀.memos ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        RelEA Expr.mkAppN s₀.store f args s'.store r; ⊤⦄ := by
  intro args
  induction args with
  | nil =>
    intro s₀ f hok hf hargs
    sym only [bridge_grind, Expr.mkAppN] => vcgen [mkAppN] <;> finish
  | cons a as ih =>
    intro s₀ f hok hf hargs
    sym only [bridge_grind, Expr.mkAppN, denoteEView] => vcgen [mkAppN, ih] <;> finish

/-- con-leche: none — `mkAppNFrom`'s two clauses, spelled out.  The walk's
recursion is on a cursor (`termination_by`), not on a constructor pattern, so
unfolding it by name does not stop at one step; these two equations unfold
it exactly once. -/
theorem mkAppNFrom_lt {f : EIdx} {args : Array EIdx} {i : Nat}
    (h : i < args.size) :
    mkAppNFrom f args i =
      (do let g ← internAppE f args[i]; mkAppNFrom g args (i + 1)) := by
  rw [mkAppNFrom]
  simp only [h, dite_eq_left]

/-- con-leche: none — and the exhausted clause. -/
theorem mkAppNFrom_ge {f : EIdx} {args : Array EIdx} {i : Nat}
    (h : ¬ i < args.size) : mkAppNFrom f args i = pure f := by
  rw [mkAppNFrom]
  simp only [h, reduceDIte]

/-- con-leche: none — `mkAppNFrom f args i` is `mkAppN` at the arguments from
`i` on: the push-order `Array` accumulator read with a cursor instead of
copied.  **Stated so that `mkAppN_spec` composes**: the answer relation is the
SAME `RelEA Expr.mkAppN`, at the DROPPED handle list, so a caller that has
`mkAppN`'s theorem has this one.  The recursion is on `args.size - i`, so the
induction is on that difference; each step names the dropped list's head
and unfolds the walk once before `sym`. -/
theorem mkAppNFrom_spec : ∀ (n : Nat) (s₀ : AState) (f : EIdx)
    (args : Array EIdx) (i : Nat), args.size - i = n → StateOK s₀ →
    (denoteE s₀.store f).isSome = true →
    (Frontend.denoteEList s₀.store (args.toList.drop i)).isSome = true →
    ⦃fun s => s = s₀⦄ mkAppNFrom f args i
    ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧ s'.memos = s₀.memos ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        RelEA Expr.mkAppN s₀.store f (args.toList.drop i) s'.store r; ⊤⦄ := by
  intro n
  induction n with
  | zero =>
    intro s₀ f args i hn hok hf hargs
    have hd : args.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [hd] at hargs ⊢
    rw [mkAppNFrom_ge (by omega)]
    sym only [bridge_grind, Expr.mkAppN] => vcgen <;> finish
  | succ n ih =>
    intro s₀ f args i hn hok hf hargs
    by_cases hi : i < args.size
    · have hd : args.toList.drop i = args[i] :: args.toList.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons (by simp; omega)]
        simp
      rw [hd] at hargs ⊢
      rw [mkAppNFrom_lt hi]
      sym only [bridge_grind, Expr.mkAppN, denoteEView] => vcgen [ih] <;> finish
    · have hd : args.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
      rw [hd] at hargs ⊢
      rw [mkAppNFrom_ge hi]
      sym only [bridge_grind, Expr.mkAppN] => vcgen <;> finish

/-! ## 7. The fold of `instantiate1`

`instSpine` calls `instantiate1Fast`, whose Theorem 1 is `ExprOps/Inst1`'s
`instantiate1Fast_spec`.  Two things about consuming it:

* it takes the substituted term `ve` EXPLICITLY, so the head argument's
  denotation is named before `sym` and the spec is passed instantiated at it;
* it frames `caches` and `pins` but NOT `memos` (it drops its own per-call
  table, `s'.memos.inst1C = ∅`), so `instSpine`'s postcondition frames
  `caches` and `pins` only.  That is the honest frame: a caller that needs
  `MemoOK` of another table must re-establish it, and `MemoOK.of_empty` is
  what makes that free for the dropped one. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1305-1313 instSpine —
**THEOREM 1** for `instSpine`: instantiate a telescope-context expression at
an argument spine, `bvar t` first and descending.  Structural on the argument
list; the fuel is the one `instantiate1Fast` needs. -/
theorem instSpine_spec (fuel : Nat) : ∀ (as : List EIdx) (s₀ : AState)
    (t : Nat) (e : EIdx), StateOK s₀ → (denoteE s₀.store e).isSome = true →
    (Frontend.denoteEList s₀.store as).isSome = true →
    ⦃fun s => s = s₀⦄ instSpine fuel as t e
    ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        RelEA (fun x xs => Expr.instSpine xs t x) s₀.store e as s'.store r; ⊤⦄ := by
  intro as
  induction as with
  | nil =>
    intro s₀ t e hok hden hargs
    sym only [bridge_grind, Expr.instSpine] => vcgen [instSpine] <;> finish
  | cons a as ih =>
    intro s₀ t e hok hden hargs
    obtain ⟨ea, hea⟩ := Option.isSome_iff_exists.mp (denoteEList_cons_isSome hargs).1
    sym only [bridge_grind, Expr.instSpine] =>
      vcgen [instSpine, ih, instantiate1Fast_spec fuel (v := a) (ve := ea)] <;> finish

/-! ## The axiom check

DESIGN §8.2 asks for it on every closed theorem of the tier. -/

#print axioms getAppFn_spec
#print axioms getAppArgs_spec
#print axioms mkAppN_spec
#print axioms mkAppNFrom_spec
#print axioms stripLams_spec
#print axioms stripPis_spec
#print axioms piResult_spec
#print axioms fvarTypeD_spec
#print axioms instSpine_spec
#print axioms denoteEList_snoc

end ConRon.Bridge.ExprOps

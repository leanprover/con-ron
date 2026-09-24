/-
# `ConRon.Bridge.ExprOps.Guards` — Theorem 1 for the two memoized guards

DESIGN §8.2's Theorem 1 at the four twins of `Arena/ExprOps.lean` that are
`Cached/ExprOpsC.lean`'s memoized DAG walks: `wscopedBGo` (`:833`),
`wscopedBFast` (`:868`), `leavesSubGo` (`:923`) and `leafGuard` (`:962`).
Companion of `ExprOps/Leaves.lean`, whose `denoteLeaves`, `leafMem_spec`,
`MemoVDOK` and cutoff licence it uses, and of `ExprOps/Walks.lean` and
`ExprOps/Ranges.lean`.

## What is stated against what

Both walks' clause-for-clause counterparts upstream are
`Cached/ExprOpsC.lean`'s `wscopedBP` and `leavesSubP`, and the bridge does not
import con-leche's `Cached` tier (DESIGN §8.2: "after the rewrite nothing in
con-ron references con-leche's `Cached` tier").  So each is stated against the
**Kernel-tier** function it computes:

* `wscopedBGo` / `wscopedBFast` against `Expr.wscopedB d` — which is what
  `wscopedBP_spec` proves of `wscopedBP` upstream, and is exactly
  `ExprOps/Walks.lean`'s `wscopedB_spec` with a memo and a cutoff added;
* `leavesSubGo` / `leafGuard` against `leavesSubSpec` below, which is
  `Kernel/Core.lean:586`'s own spelling of the guard
  (`fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l)`).  Its ten
  equations are `leavesSubP` clause for clause — that is what makes the arms
  of `leavesSubGo_spec` the same one-line `bridge_vcs` as `Walks.lean`'s.

## The three memos' invariants

All three memos are ARGUMENTS and not `AState` fields, so none is one of
`Bridge/StateOK.lean`'s thirteen and each is a hypothesis of its walk's
`Spec` record, in StateOK's own shape (`∀ k v, tbl[k]? = some v → …`):

* `wscopedBGo`'s key carries the cursor — `Leaves.lean`'s `MemoVDOK`;
* `leavesSubGo`'s key is the node alone, but its VALUE depends on the base
  leaf list, which is a list of HANDLES.  That is the wrinkle of this file:
  the invariant, and the answer relation, are quantified over the base list's
  DENOTATION rather than taking it as a parameter (`LSubAt`, `LSubMemoA`
  below), because a parameter would hand `mvcgen` the side goal
  `denoteLeaves s.store bl = some ?bl'` with a metavariable in it — task
  #97s template rule 4, and `leafGuard` is where it bites (its base list is
  *computed* by `fvarLeavesFast`).  The two `to_`/`of_` bridging lemmas below
  turn `LSubAt` into `Bridge/Rel.lean`'s plain `RelV` and back, so all the
  per-arm reasoning still happens at `RelV` where `Walks.lean`'s recipe
  works unchanged.

## Elaboration

`leavesSubSpec`'s ten equations are `@[grind =]`, and with them the closer
takes every arm of both walks.  Nothing in this file needs a `next =>` block.
-/
import ConRon.Bridge.ExprOps.Leaves

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

attribute [-grind] RelE.ext RelE.of_ext RelE.retarget

/-! ## 1. `wscopedBGo` and `wscopedBFast` — `ExprOps.lean:833`, `:868`

`Walks.lean`'s `wscopedB` with three additions, all of them con-leche's own
(`Cached/ExprOpsC.lean`'s `wscopedBXP` / `wscopedBC`): the fvar-range cutoff
at the head, the memo probe, and the insert on the way out. -/

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1029-1088 wscopedBXP — the memo's
invariant: every recorded verdict is `Expr.wscopedB` at the key's own cursor.
`MemoVDOK` at `wscopedB`, as an `abbrev` fixing the pure function, which is
`Bridge/StateOK.lean`'s own shape for its thirteen tables (task #97b finding
2: the only metavariable `mspec` then leaves is first-order). -/
abbrev WScopedMemoA (tbl : Std.HashMap (EIdx × Nat) Bool) (st : EStore) :
    Prop :=
  MemoVDOK (fun d e => Expr.wscopedB d e) tbl st

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1013-1015 wscopedBP_cut — the
CUTOFF's licence, as the answer relation: an `fvar`-free term is in scope at
every depth.

**Not `@[grind →]`, and the cursor is EXPLICIT**: `d` occurs only in the
conclusion, so a forward rule has no pattern for it (`grind` reports *failed
to find patterns in the antecedents of the theorem*).  Passed to the closer
in `bridge_vcs`'s list instead, with `d` explicit so that the instance is
determined by the goal — the same shape `leavesSub_cut_of_derived` below
needs for its base list, and the second half of this file's `leafMem`
finding. -/
theorem wscopedB_cut_of_derived {st : EStore} (hwf : StoreWF st)
    {h : EIdx} (d : Nat) (h0 : (fvarOfData (st.derived h)).toNat = 0) :
    RelV (Expr.wscopedB d) st h true := by
  intro e he
  exact (wscopedB_of_hasFvar e d (hasFvar_false_of_derived hwf he h0)).symm

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `wscopedBGo`'s recursion. -/
structure WScopedBGoSpec (rec : Std.HashMap (EIdx × Nat) Bool → Nat → EIdx →
    AM (Bool × Std.HashMap (EIdx × Nat) Bool)) : Prop where
  run : ∀ (s₁ : AState) (tbl : Std.HashMap (EIdx × Nat) Bool) (d : Nat)
      (c : EIdx), StateOK s₁ → WScopedMemoA tbl s₁.store →
      (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec tbl d c
    ⦃⇓? p s' => ⌜s' = s₁ ∧ WScopedMemoA p.2 s₁.store ∧
        RelV (Expr.wscopedB d) s₁.store c p.1⌝⦄

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1029-1088 wscopedBXP — **THEOREM
1 for the memoized `wscopedB`**, at one level of the recursion. -/
theorem wscopedBGo_spec :
    ∀ fuel, WScopedBGoSpec (fun tbl => wscopedBGo tbl fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ tbl d h _ _ _
    mvcgen [wscopedBGo_zero]
    all_goals bridge_vcs [Expr.wscopedB, RelV, MemoVDOK.insert,
      MemoVDOK.of_empty, wscopedB_cut_of_derived]
  | succ fuel ih =>
    constructor
    intro s₀ tbl d h hok hm hden
    have hrec := ih.run
    mvcgen [wscopedBGo_succ, wscopedBGoArmApp, wscopedBGoArmBind, wscopedBGoArmLet, hrec]
    all_goals bridge_vcs [Expr.wscopedB, RelV, MemoVDOK.insert,
      MemoVDOK.of_empty, wscopedB_cut_of_derived]

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1090-1095 wscopedBC — **THEOREM 1
for `wscopedBFast`**: one memoized DAG walk from the empty memo. -/
theorem wscopedBFast_spec (fuel d : Nat) (s₀ : AState) (h : EIdx)
    (hok : StateOK s₀) (hden : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ wscopedBFast fuel d h
    ⦃⇓? r s' => ⌜s' = s₀ ∧ RelV (Expr.wscopedB d) s₀.store h r⌝⦄ := by
  have hr := (wscopedBGo_spec fuel).run
  mvcgen [wscopedBFast, hr]
  all_goals bridge_vcs [RelV, MemoVDOK.of_empty]

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1090-1095 wscopedBC — the run
form. -/
theorem wscopedBFast_run {fuel d : Nat} {s₀ s' : AState} {h : EIdx} {r : Bool}
    (hok : StateOK s₀) (hden : (denoteE s₀.store h).isSome = true)
    (hrun : (wscopedBFast fuel d h).run s₀ = Except.ok (r, s')) :
    s' = s₀ ∧ RelV (Expr.wscopedB d) s₀.store h r :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    (wscopedBFast_spec fuel d s₀ h hok hden)

/-! ## 2. The leaf-subset test's pure specification

`Kernel/Core.lean:586`'s own guard expression, and the ten equations that make
it `Cached/ExprOpsC.lean`'s `leavesSubP` clause for clause. -/

/-- con-leche: ConLeche/Kernel/Core.lean:586-588 majorToCtor — **the leaf
guard's pure specification**: every reachable `fvar` leaf of `e` is in `bl`.
`Cached/ExprOpsC.lean:1167-1185`'s `leavesSubP` is this function with the
range cutoff inlined; the equations below are the two against each other. -/
def leavesSubSpec (bl : List (Nat × Expr)) (e : Expr) : Bool :=
  (Expr.fvarLeaves e).all (fun l => bl.contains l)

@[grind =] theorem leavesSubSpec_bvar {bl : List (Nat × Expr)} {i : Nat} :
    leavesSubSpec bl (.bvar i) = true := by
  simp [leavesSubSpec, Expr.fvarLeaves]

@[grind =] theorem leavesSubSpec_sort {bl : List (Nat × Expr)} {u : Level} :
    leavesSubSpec bl (.sort u) = true := by
  simp [leavesSubSpec, Expr.fvarLeaves]

@[grind =] theorem leavesSubSpec_const {bl : List (Nat × Expr)}
    {n : ConLeche.Name} {us : List Level} :
    leavesSubSpec bl (.const n us) = true := by
  simp [leavesSubSpec, Expr.fvarLeaves]

@[grind =] theorem leavesSubSpec_lit {bl : List (Nat × Expr)}
    {l : ConLeche.Literal} : leavesSubSpec bl (.lit l) = true := by
  simp [leavesSubSpec, Expr.fvarLeaves]

@[grind =] theorem leavesSubSpec_fvar {bl : List (Nat × Expr)} {i : Nat}
    {t : Expr} :
    leavesSubSpec bl (.fvar i t) =
      (bl.contains (i, t) && leavesSubSpec bl t) := by
  simp [leavesSubSpec, Expr.fvarLeaves]

@[grind =] theorem leavesSubSpec_app {bl : List (Nat × Expr)} {f a : Expr} :
    leavesSubSpec bl (.app f a) =
      (leavesSubSpec bl f && leavesSubSpec bl a) := by
  simp [leavesSubSpec, Expr.fvarLeaves]

@[grind =] theorem leavesSubSpec_lam {bl : List (Nat × Expr)} {ty b : Expr}
    {m : BinderMeta} :
    leavesSubSpec bl (.lam ty b m) =
      (leavesSubSpec bl ty && leavesSubSpec bl b) := by
  simp [leavesSubSpec, Expr.fvarLeaves]

@[grind =] theorem leavesSubSpec_forallE {bl : List (Nat × Expr)}
    {ty b : Expr} {m : BinderMeta} :
    leavesSubSpec bl (.forallE ty b m) =
      (leavesSubSpec bl ty && leavesSubSpec bl b) := by
  simp [leavesSubSpec, Expr.fvarLeaves]

@[grind =] theorem leavesSubSpec_letE {bl : List (Nat × Expr)}
    {ty v b : Expr} :
    leavesSubSpec bl (.letE ty v b) =
      (leavesSubSpec bl ty && leavesSubSpec bl v && leavesSubSpec bl b) := by
  simp [leavesSubSpec, Expr.fvarLeaves, Bool.and_assoc]

@[grind =] theorem leavesSubSpec_proj {bl : List (Nat × Expr)}
    {n : ConLeche.Name} {i : Nat} {s : Expr} :
    leavesSubSpec bl (.proj n i s) = leavesSubSpec bl s := by
  simp [leavesSubSpec, Expr.fvarLeaves]

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1187-1189 leavesSubP_cut — the
CUTOFF's licence: an `fvar`-free term has no leaf, hence is a leaf-subset of
anything. -/
theorem leavesSub_cut_of_derived {st : EStore} (hwf : StoreWF st) {h : EIdx}
    (bl : List (Nat × Expr)) (h0 : (fvarOfData (st.derived h)).toNat = 0) :
    RelV (leavesSubSpec bl) st h true := by
  intro e he
  simp only [leavesSubSpec,
    fvarLeaves_nil_of_hasFvar e (hasFvar_false_of_derived hwf he h0),
    List.all_nil]

/-- con-leche: none — the guard asks only about MEMBERSHIP in the base list,
so two base lists with the same elements give the same verdict.  This is what
lets `leafGuard` consume `fvarLeavesFast`'s membership-only specification
(`Leaves.lean`'s `LeavesEq`). -/
theorem leavesSubSpec_congr {bl bl' : List (Nat × Expr)}
    (h : ∀ x, x ∈ bl ↔ x ∈ bl') (e : Expr) :
    leavesSubSpec bl e = leavesSubSpec bl' e := by
  simp only [leavesSubSpec]
  refine List.all_congr rfl (fun a => ?_)
  simp only [List.contains_eq_mem, decide_eq_decide]
  exact h a

/-! ## 3. `leavesSubGo` — `ExprOps.lean:923`

The fabrication-side leaf-subset test, memoized on the node.  The base list
is a list of HANDLES, so both the answer relation and the memo invariant
quantify its DENOTATION rather than naming it — template rule 4, see the
module doc. -/

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1197-1256 leavesSubXP — the
answer relation at a base list of HANDLES: whatever that list denotes, the
verdict is the pure guard's. -/
def LSubAt (bl : List (Nat × EIdx)) (st : EStore) (c : EIdx) (r : Bool) :
    Prop :=
  ∀ bl', denoteLeaves st bl = some bl' → RelV (leavesSubSpec bl') st c r

/-- con-leche: none — `LSubAt` from `RelV` at the base list's denotation. -/
@[grind →] theorem LSubAt.of_relV {bl : List (Nat × EIdx)} {st : EStore}
    {c : EIdx} {r : Bool} {bl' : List (Nat × Expr)}
    (hbl : denoteLeaves st bl = some bl')
    (h : RelV (leavesSubSpec bl') st c r) : LSubAt bl st c r := by
  intro bl2 hbl2
  rw [hbl] at hbl2
  obtain rfl := Option.some.inj hbl2
  exact h

/-- con-leche: none — and back, so that every per-arm step happens at
`Bridge/Rel.lean`'s plain `RelV`. -/
@[grind →] theorem LSubAt.to_relV {bl : List (Nat × EIdx)} {st : EStore}
    {c : EIdx} {r : Bool} {bl' : List (Nat × Expr)} (h : LSubAt bl st c r)
    (hbl : denoteLeaves st bl = some bl') :
    RelV (leavesSubSpec bl') st c r := h bl' hbl

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1197-1256 leavesSubXP — the
memo's invariant, at the base list's denotation.  `Bridge/StateOK.lean`'s
generic `MemoVOK` behind the same quantifier as `LSubAt`. -/
def LSubMemoA (bl : List (Nat × EIdx)) (tbl : Std.HashMap EIdx Bool)
    (st : EStore) : Prop :=
  ∀ bl', denoteLeaves st bl = some bl' → MemoVOK (leavesSubSpec bl') tbl st

/-- con-leche: none — a dropped table satisfies the invariant. -/
theorem LSubMemoA.of_empty {bl : List (Nat × EIdx)}
    {tbl : Std.HashMap EIdx Bool} {st : EStore} (h : tbl = ∅) :
    LSubMemoA bl tbl st := fun _ _ => MemoVOK.of_empty h

/-- con-leche: none — `LSubMemoA` from `MemoVOK`. -/
@[grind →] theorem LSubMemoA.of_memoVOK {bl : List (Nat × EIdx)}
    {tbl : Std.HashMap EIdx Bool} {st : EStore} {bl' : List (Nat × Expr)}
    (hbl : denoteLeaves st bl = some bl')
    (h : MemoVOK (leavesSubSpec bl') tbl st) : LSubMemoA bl tbl st := by
  intro bl2 hbl2
  rw [hbl] at hbl2
  obtain rfl := Option.some.inj hbl2
  exact h

/-- con-leche: none — and back. -/
@[grind →] theorem LSubMemoA.to_memoVOK {bl : List (Nat × EIdx)}
    {tbl : Std.HashMap EIdx Bool} {st : EStore} {bl' : List (Nat × Expr)}
    (h : LSubMemoA bl tbl st) (hbl : denoteLeaves st bl = some bl') :
    MemoVOK (leavesSubSpec bl') tbl st := h bl' hbl

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `leavesSubGo`'s recursion. -/
structure LeavesSubGoSpec (bl : List (Nat × EIdx))
    (rec : Std.HashMap EIdx Bool → EIdx →
      AM (Bool × Std.HashMap EIdx Bool)) : Prop where
  run : ∀ (s₁ : AState) (tbl : Std.HashMap EIdx Bool) (c : EIdx),
      StateOK s₁ → (denoteLeaves s₁.store bl).isSome = true →
      LSubMemoA bl tbl s₁.store → (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec tbl c
    ⦃⇓? p s' => ⌜s' = s₁ ∧ LSubMemoA bl p.2 s₁.store ∧
        LSubAt bl s₁.store c p.1⌝⦄

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1197-1256 leavesSubXP —
**THEOREM 1 for `leavesSubGo`**, at one level of the recursion. -/
theorem leavesSubGo_spec (bl : List (Nat × EIdx)) :
    ∀ fuel, LeavesSubGoSpec bl (fun tbl => leavesSubGo bl tbl fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ tbl h _ _ _ _
    mvcgen [leavesSubGo_zero]
    all_goals bridge_vcs [RelV, LSubAt, LSubMemoA]
  | succ fuel ih =>
    constructor
    intro s₀ tbl h hok hbl hm hden
    have hrec := ih.run
    mvcgen [leavesSubGo_succ, leavesSubArmApp, leavesSubArmBind, leavesSubArmLet, hrec]
    all_goals bridge_vcs [RelV, leavesSub_cut_of_derived]

/-! ## 4. `leafGuard` — `ExprOps.lean:962`

The fabrication leaf guard, and the only twin of group C that composes two
others: the range cutoff, then `base`'s leaf list, then ONE walk of `fab`
against it — never building `fab`'s own list, and never running `Core.lean`'s
quadratic `fvarLeavesSubset`.  Theorem 1 is stated at
`Kernel/Core.lean:586`'s own guard expression, which is what makes
`leavesSubSpec_congr` load-bearing: what `fvarLeavesFast` delivers is a list
with `Expr.fvarLeaves ebase`'s MEMBERS, not that list. -/

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1264-1268 leafGuard — the
guard's answer relation, with `base`'s denotation quantified inside (template
rule 4). -/
def LeafGuardAt (st : EStore) (fab base : EIdx) (r : Bool) : Prop :=
  ∀ eb, denoteE st base = some eb →
    RelV (leavesSubSpec (Expr.fvarLeaves eb)) st fab r

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1264-1268 leafGuard — **THEOREM
1 for `leafGuard`**.  Complete except for the `fvarLeavesGo` gray clause it
inherits through `Leaves.lean`'s `fvarLeavesFast_spec`. -/
theorem leafGuard_spec (fuel : Nat) (s₀ : AState) (fab base : EIdx)
    (hok : StateOK s₀) (hfab : (denoteE s₀.store fab).isSome = true)
    (hbase : (denoteE s₀.store base).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ leafGuard fuel fab base
    ⦃⇓? r s' => ⌜s' = s₀ ∧ LeafGuardAt s₀.store fab base r⌝⦄ := by
  have hfl := fvarLeavesFast_spec fuel
  have hls := fun bl => (leavesSubGo_spec bl fuel).run
  mvcgen [leafGuard, hfl, hls]
  all_goals bridge_vcs [LeafGuardAt, LSubAt, LSubMemoA, LeavesEq, RelV,
    MemoVOK.of_empty, LSubMemoA.of_empty, leavesSubSpec_congr,
    leavesSub_cut_of_derived, denoteLeaves_nil]

/-! ## The axiom check -/

#print axioms wscopedB_cut_of_derived
#print axioms wscopedBGo_spec
#print axioms wscopedBFast_spec
#print axioms leavesSub_cut_of_derived
#print axioms leavesSubSpec_congr
#print axioms leavesSubGo_spec
#print axioms leafGuard_spec

end ConRon.Bridge.ExprOps

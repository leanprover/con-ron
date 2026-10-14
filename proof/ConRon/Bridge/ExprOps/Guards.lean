/-
# `ConRon.Bridge.ExprOps.Guards` — Theorem 1 for the two memoized guards

DESIGN §8.2's Theorem 1 at the four twins of `Arena/ExprOps.lean` that are
`Cached/ExprOpsC.lean`'s memoized DAG walks: `wscopedBGo` (`:833`),
`wscopedBFast` (`:868`), `leavesSubGo` (`:923`) and `leafGuard` (`:962`).
Companion of `ExprOps/Leaves.lean`, whose `denoteLeaves`, `leafMem_spec`,
`MemoVDOK`, `LeavesEq` and cutoff licence it uses, and of
`ExprOps/Ranges.lean`.

## What is stated against what

Both walks' clause-for-clause counterparts upstream are
`Cached/ExprOpsC.lean`'s `wscopedBP` and `leavesSubP`, and the bridge does not
import con-leche's `Cached` tier (DESIGN §8.2: "after the rewrite nothing in
con-ron references con-leche's `Cached` tier").  So each is stated against the
**Kernel-tier** function it computes:

* `wscopedBGo` / `wscopedBFast` against `Expr.wscopedB d` — which is what
  `wscopedBP_spec` proves of `wscopedBP` upstream;
* `leavesSubGo` / `leafGuard` against `leavesSubSpec` below, which is
  `Kernel/Core.lean:586`'s own spelling of the guard
  (`fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l)`).  Its ten
  equations, one per constructor, are `leavesSubP` clause for clause.

## The three memos' invariants

All three memos are ARGUMENTS and not `AState` fields, so none is one of
`Bridge/StateOK.lean`'s thirteen and each is a hypothesis of its walk's
`Spec` record, in StateOK's own shape (`∀ k v, tbl[k]? = some v → …`):

* `wscopedBGo`'s key carries the cursor — `Leaves.lean`'s `MemoVDOK`;
* `leavesSubGo`'s key is the node alone, but its VALUE depends on the base
  leaf list, which is a list of HANDLES.  That is the wrinkle of this file:
  the invariant, and the answer relation, are quantified over the base list's
  DENOTATION rather than taking it as a parameter (`LSubAt`, `LSubMemoA`
  below), because a parameter would be one the program does not determine,
  which the verification-condition generator cannot instantiate — and
  `leafGuard` *computes* its base list (`fvarLeavesFast`).  For `grind`, each
  of the two is an equation to a named predicate on that denotation term
  (`LSubO`, `LSubMemoO`, `Bridge/Grind.lean` §3's `MapRelV` shape), which at
  `some` is `Bridge/Rel.lean`'s plain `RelV` (resp. `MemoVOK`).

## The proofs

Every proof is `sym only [bridge_grind, …] => vcgen [f, callee specs…] <;>
finish`.  `grind` reads a viewed node's children from `Bridge/Grind.lean`'s
`DenoteView` facts and its constructor from the view's tag, and then the
step is congruence closure through the pure function's per-constructor
equations (`Expr.wscopedB`'s own, `leavesSubSpec_*`).  The cutoffs, the memo
hit, insert and dropped table, `leafMem`'s verdict (`LeafMemO`) and
`leafGuard`'s composition (`LeafGuardAt.of_lSubAt`) are lemmas keyed by the
terms the verification conditions have.
-/
import ConRon.Bridge.ExprOps.Leaves

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

/-! ## Vocabulary candidates (for Bridge/Grind.lean)

The memo invariants this module's walks carry, in `Bridge/Grind.lean` §5's
shape: the hit at a probe the program matched, the insert at the update's
table term, the dropped table, each guarded so that it fires there only.
`MemoVDOK` (`ExprOps/Leaves.lean`) is the cursor-keyed one; `MemoVOK`'s three
are `ExprOps/Ranges.lean`'s candidates again, registered locally here because
the two modules do not import each other. -/

grind_pattern [bridge_grind] MemoVDOK.get => MemoVDOK f tbl st, tbl[k]?, some v where
  guard tbl[k]? = some v

grind_pattern [bridge_grind] MemoVDOK.insert => MemoVDOK f tbl' st, tbl.insert k v where
  guard tbl' = tbl.insert k v

grind_pattern [bridge_grind] MemoVDOK.of_empty => MemoVDOK f tbl st where
  guard tbl = ∅

local grind_pattern [bridge_grind] MemoVOK.get => MemoVOK f tbl st, tbl[k]?, some v where
  guard tbl[k]? = some v

local grind_pattern [bridge_grind] MemoVOK.insert => MemoVOK f tbl' st, tbl.insert k v where
  guard tbl' = tbl.insert k v

local grind_pattern [bridge_grind] MemoVOK.of_empty => MemoVOK f tbl st where
  guard tbl = ∅

/-! ## 1. `wscopedBGo` and `wscopedBFast` — `ExprOps.lean:833`, `:868`

The scope walk `Expr.wscopedB` with three additions, all of them con-leche's own
(`Cached/ExprOpsC.lean`'s `wscopedBXP` / `wscopedBC`): the fvar-range cutoff
at the head, the memo probe, and the insert on the way out. -/

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1029-1088 wscopedBXP — the memo's
invariant: every recorded verdict is `Expr.wscopedB` at the key's own cursor.
`MemoVDOK` at `wscopedB`, as an `abbrev` fixing the pure function, which is
`Bridge/StateOK.lean`'s own shape for its thirteen tables. -/
abbrev WScopedMemoA (tbl : Std.HashMap (EIdx × Nat) Bool) (st : EStore) :
    Prop :=
  MemoVDOK Expr.wscopedB tbl st

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1013-1015 wscopedBP_cut — the
CUTOFF's licence, as the answer relation: an `fvar`-free term is in scope at
every depth.  The cursor occurs only in the conclusion, so the lemma is keyed
by the answer it licenses. -/
theorem wscopedB_cut_of_derived {st : EStore} (hwf : StoreWF st)
    {h : EIdx} (d : Nat) (h0 : (fvarOfData (st.derived h)).toNat = 0) :
    RelV (Expr.wscopedB d) st h true := by
  intro e he
  exact (wscopedB_of_hasFvar e d (hasFvar_false_of_derived hwf he h0)).symm
grind_pattern [bridge_grind] wscopedB_cut_of_derived => RelV (Expr.wscopedB d) st h true

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `wscopedBGo`'s recursion. -/
structure WScopedBGoSpec (rec : Std.HashMap (EIdx × Nat) Bool → Nat → EIdx →
    AM (Bool × Std.HashMap (EIdx × Nat) Bool)) : Prop where
  run : ∀ (s₁ : AState) (tbl : Std.HashMap (EIdx × Nat) Bool) (d : Nat)
      (c : EIdx), StateOK s₁ → WScopedMemoA tbl s₁.store →
      (denoteE s₁.store c).isSome = true →
    ⦃fun s => s = s₁⦄ rec tbl d c
    ⦃fun p s' => s' = s₁ ∧ WScopedMemoA p.2 s₁.store ∧
        RelV (Expr.wscopedB d) s₁.store c p.1; ⊤⦄

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1029-1088 wscopedBXP — **THEOREM
1 for the memoized `wscopedB`**, at one level of the recursion. -/
theorem wscopedBGo_spec :
    ∀ fuel, WScopedBGoSpec (fun tbl => wscopedBGo tbl fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ tbl d h _ _ _
    sym only [bridge_grind] => vcgen [wscopedBGo_zero] <;> finish
  | succ fuel ih =>
    constructor
    intro s₀ tbl d h hok hm hden
    sym only [bridge_grind, Expr.wscopedB] =>
      vcgen [wscopedBGo_succ, wscopedBGoArmApp, wscopedBGoArmBind, wscopedBGoArmLet,
        ih.run] <;> finish

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1090-1095 wscopedBC — **THEOREM 1
for `wscopedBFast`**: one memoized DAG walk from the empty memo. -/
theorem wscopedBFast_spec (fuel d : Nat) (s₀ : AState) (h : EIdx)
    (hok : StateOK s₀) (hden : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => s = s₀⦄ wscopedBFast fuel d h
    ⦃fun r s' => s' = s₀ ∧ RelV (Expr.wscopedB d) s₀.store h r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [wscopedBFast, (wscopedBGo_spec fuel).run] <;> finish

/-! ## 2. The leaf-subset test's pure specification

`Kernel/Core.lean:586`'s own guard expression, and the ten equations that make
it `Cached/ExprOpsC.lean`'s `leavesSubP` clause for clause. -/

/-- con-leche: ConLeche/Kernel/Core.lean:586-588 majorToCtor — **the leaf
guard's pure specification**: every reachable `fvar` leaf of `e` is in `bl`.
`Cached/ExprOpsC.lean:1167-1185`'s `leavesSubP` is this function with the
range cutoff inlined; the equations below are the two against each other. -/
def leavesSubSpec (bl : List (Nat × Expr)) (e : Expr) : Bool :=
  (Expr.fvarLeaves e).all (fun l => bl.contains l)

@[bridge_grind =] theorem leavesSubSpec_bvar {bl : List (Nat × Expr)} {i : Nat} :
    leavesSubSpec bl (.bvar i) = true := by
  simp [leavesSubSpec, Expr.fvarLeaves]

@[bridge_grind =] theorem leavesSubSpec_sort {bl : List (Nat × Expr)} {u : Level} :
    leavesSubSpec bl (.sort u) = true := by
  simp [leavesSubSpec, Expr.fvarLeaves]

@[bridge_grind =] theorem leavesSubSpec_const {bl : List (Nat × Expr)}
    {n : ConLeche.Name} {us : List Level} :
    leavesSubSpec bl (.const n us) = true := by
  simp [leavesSubSpec, Expr.fvarLeaves]

@[bridge_grind =] theorem leavesSubSpec_lit {bl : List (Nat × Expr)}
    {l : ConLeche.Literal} : leavesSubSpec bl (.lit l) = true := by
  simp [leavesSubSpec, Expr.fvarLeaves]

@[bridge_grind =] theorem leavesSubSpec_fvar {bl : List (Nat × Expr)} {i : Nat}
    {t : Expr} :
    leavesSubSpec bl (.fvar i t) =
      (bl.contains (i, t) && leavesSubSpec bl t) := by
  simp [leavesSubSpec, Expr.fvarLeaves]

@[bridge_grind =] theorem leavesSubSpec_app {bl : List (Nat × Expr)} {f a : Expr} :
    leavesSubSpec bl (.app f a) =
      (leavesSubSpec bl f && leavesSubSpec bl a) := by
  simp [leavesSubSpec, Expr.fvarLeaves]

@[bridge_grind =] theorem leavesSubSpec_lam {bl : List (Nat × Expr)} {ty b : Expr} :
    leavesSubSpec bl (.lam ty b) =
      (leavesSubSpec bl ty && leavesSubSpec bl b) := by
  simp [leavesSubSpec, Expr.fvarLeaves]

@[bridge_grind =] theorem leavesSubSpec_forallE {bl : List (Nat × Expr)}
    {ty b : Expr} :
    leavesSubSpec bl (.forallE ty b) =
      (leavesSubSpec bl ty && leavesSubSpec bl b) := by
  simp [leavesSubSpec, Expr.fvarLeaves]

@[bridge_grind =] theorem leavesSubSpec_letE {bl : List (Nat × Expr)}
    {ty v b : Expr} :
    leavesSubSpec bl (.letE ty v b) =
      (leavesSubSpec bl ty && leavesSubSpec bl v && leavesSubSpec bl b) := by
  simp [leavesSubSpec, Expr.fvarLeaves, Bool.and_assoc]

@[bridge_grind =] theorem leavesSubSpec_proj {bl : List (Nat × Expr)}
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
quantify its DENOTATION rather than naming it — see the module doc. -/

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1197-1256 leavesSubXP — the
answer relation at a base list of HANDLES: whatever that list denotes, the
verdict is the pure guard's. -/
def LSubAt (bl : List (Nat × EIdx)) (st : EStore) (c : EIdx) (r : Bool) :
    Prop :=
  ∀ bl', denoteLeaves st bl = some bl' → RelV (leavesSubSpec bl') st c r

/-- con-leche: none — `LSubAt`'s answer at the base list's optional
denotation, as a named predicate (`Bridge/Grind.lean` §3's `MapRelV` shape):
the verdict is the pure guard's at whatever the base list denotes. -/
def LSubO (st : EStore) (c : EIdx) (r : Bool) : Option (List (Nat × Expr)) → Prop
  | some bl' => RelV (leavesSubSpec bl') st c r
  | none => True

/-- con-leche: none — `LSubAt` IS `LSubO` at the base list's denotation. -/
@[bridge_grind =] theorem lSubAt_eq (bl : List (Nat × EIdx)) (st : EStore) (c : EIdx)
    (r : Bool) : LSubAt bl st c r = LSubO st c r (denoteLeaves st bl) := by
  unfold LSubAt
  cases denoteLeaves st bl <;> simp [LSubO]

/-- con-leche: none — `LSubO` at a denoting base list. -/
@[bridge_grind =] theorem LSubO.some_eq (st : EStore) (c : EIdx) (r : Bool)
    (bl' : List (Nat × Expr)) : LSubO st c r (some bl') = RelV (leavesSubSpec bl') st c r :=
  rfl

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1187-1189 leavesSubP_cut — the
cutoff at a base list of handles, keyed by the answer it licenses. -/
theorem LSubAt.cut {st : EStore} (hwf : StoreWF st) (bl : List (Nat × EIdx)) {h : EIdx}
    (h0 : (fvarOfData (st.derived h)).toNat = 0) : LSubAt bl st h true :=
  fun bl' _ => leavesSub_cut_of_derived hwf bl' h0
grind_pattern [bridge_grind] LSubAt.cut => LSubAt bl st h true

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1197-1256 leavesSubXP — the
memo's invariant, at the base list's denotation.  `Bridge/StateOK.lean`'s
generic `MemoVOK` behind the same quantifier as `LSubAt`. -/
def LSubMemoA (bl : List (Nat × EIdx)) (tbl : Std.HashMap EIdx Bool)
    (st : EStore) : Prop :=
  ∀ bl', denoteLeaves st bl = some bl' → MemoVOK (leavesSubSpec bl') tbl st

/-- con-leche: none — `LSubMemoA` at the base list's optional denotation. -/
def LSubMemoO (tbl : Std.HashMap EIdx Bool) (st : EStore) :
    Option (List (Nat × Expr)) → Prop
  | some bl' => MemoVOK (leavesSubSpec bl') tbl st
  | none => True

/-- con-leche: none — `LSubMemoA` IS `LSubMemoO` at the base list's
denotation. -/
@[bridge_grind =] theorem lSubMemoA_eq (bl : List (Nat × EIdx)) (tbl : Std.HashMap EIdx Bool)
    (st : EStore) : LSubMemoA bl tbl st = LSubMemoO tbl st (denoteLeaves st bl) := by
  unfold LSubMemoA
  cases denoteLeaves st bl <;> simp [LSubMemoO]

/-- con-leche: none — `LSubMemoO` at a denoting base list. -/
@[bridge_grind =] theorem LSubMemoO.some_eq (tbl : Std.HashMap EIdx Bool) (st : EStore)
    (bl' : List (Nat × Expr)) :
    LSubMemoO tbl st (some bl') = MemoVOK (leavesSubSpec bl') tbl st := rfl

/-- con-leche: none — a base list known only to denote denotes SOMETHING (the
witness `LSubO.some_eq` and `LSubMemoO.some_eq` fire on). -/
@[bridge_grind →] theorem denoteLeaves_some_of_isSome {st : EStore} {bl : List (Nat × EIdx)}
    (h : (denoteLeaves st bl).isSome = true) : ∃ bl', denoteLeaves st bl = some bl' :=
  Option.isSome_iff_exists.mp h

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1157-1162 leafMem — `leafMem`'s
verdict at the base list's and the annotation's optional denotations. -/
def LeafMemO (bl : List (Nat × EIdx)) (idx : Nat) (ty : EIdx) :
    Option (List (Nat × Expr)) → Option Expr → Prop
  | some bl', some t => leafMem bl idx ty = bl'.contains (idx, t)
  | _, _ => True

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1157-1162 leafMem — `leafMem_spec`
at every test the walk makes, keyed by the test and the two denotations. -/
theorem leafMemO {st : EStore} (hwf : StoreWF st) (bl : List (Nat × EIdx)) (idx : Nat)
    (ty : EIdx) : LeafMemO bl idx ty (denoteLeaves st bl) (denoteE st ty) := by
  cases hb : denoteLeaves st bl with
  | none => trivial
  | some bl' =>
    cases ht : denoteE st ty with
    | none => trivial
    | some t => exact leafMem_spec hwf bl bl' hb idx ty t ht
grind_pattern [bridge_grind] leafMemO => leafMem bl idx ty, denoteLeaves st bl, denoteE st ty

/-- con-leche: none — `LeafMemO` at two denotations. -/
@[bridge_grind =] theorem LeafMemO.some_eq (bl : List (Nat × EIdx)) (idx : Nat) (ty : EIdx)
    (bl' : List (Nat × Expr)) (t : Expr) :
    LeafMemO bl idx ty (some bl') (some t) = (leafMem bl idx ty = bl'.contains (idx, t)) :=
  rfl

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `leavesSubGo`'s recursion. -/
structure LeavesSubGoSpec (bl : List (Nat × EIdx))
    (rec : Std.HashMap EIdx Bool → EIdx →
      AM (Bool × Std.HashMap EIdx Bool)) : Prop where
  run : ∀ (s₁ : AState) (tbl : Std.HashMap EIdx Bool) (c : EIdx),
      StateOK s₁ → (denoteLeaves s₁.store bl).isSome = true →
      LSubMemoA bl tbl s₁.store → (denoteE s₁.store c).isSome = true →
    ⦃fun s => s = s₁⦄ rec tbl c
    ⦃fun p s' => s' = s₁ ∧ LSubMemoA bl p.2 s₁.store ∧
        LSubAt bl s₁.store c p.1; ⊤⦄

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1197-1256 leavesSubXP —
**THEOREM 1 for `leavesSubGo`**, at one level of the recursion. -/
theorem leavesSubGo_spec (bl : List (Nat × EIdx)) :
    ∀ fuel, LeavesSubGoSpec bl (fun tbl => leavesSubGo bl tbl fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ tbl h _ _ _ _
    sym only [bridge_grind] => vcgen [leavesSubGo_zero] <;> finish
  | succ fuel ih =>
    constructor
    intro s₀ tbl h hok hbl hm hden
    sym only [bridge_grind] =>
      vcgen [leavesSubGo_succ, leavesSubArmApp, leavesSubArmBind, leavesSubArmLet,
        ih.run] <;> finish

/-! ## 4. `leafGuard` — `ExprOps.lean:962`

The fabrication leaf guard, and the only twin of group C that composes two
others: the range cutoff, then `base`'s leaf list, then ONE walk of `fab`
against it — never building `fab`'s own list, and never running `Core.lean`'s
quadratic `fvarLeavesSubset`.  Theorem 1 is stated at
`Kernel/Core.lean:586`'s own guard expression, which is what makes
`leavesSubSpec_congr` load-bearing: what `fvarLeavesFast` delivers is a list
with `Expr.fvarLeaves ebase`'s MEMBERS, not that list. -/

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1264-1268 leafGuard — the
guard's answer relation, with `base`'s denotation quantified inside. -/
def LeafGuardAt (st : EStore) (fab base : EIdx) (r : Bool) : Prop :=
  ∀ eb, denoteE st base = some eb →
    RelV (leavesSubSpec (Expr.fvarLeaves eb)) st fab r

/-- con-leche: none — `LeafGuardAt`'s answer at `base`'s optional
denotation. -/
def LeafGuardO (st : EStore) (fab : EIdx) (r : Bool) : Option Expr → Prop
  | some eb => RelV (leavesSubSpec (Expr.fvarLeaves eb)) st fab r
  | none => True

/-- con-leche: none — `LeafGuardAt` IS `LeafGuardO` at `base`'s denotation. -/
@[bridge_grind =] theorem leafGuardAt_eq (st : EStore) (fab base : EIdx) (r : Bool) :
    LeafGuardAt st fab base r = LeafGuardO st fab r (denoteE st base) := by
  unfold LeafGuardAt
  cases denoteE st base <;> simp [LeafGuardO]

/-- con-leche: none — `LeafGuardO` at a denoting `base`. -/
@[bridge_grind =] theorem LeafGuardO.some_eq (st : EStore) (fab : EIdx) (r : Bool)
    (eb : Expr) :
    LeafGuardO st fab r (some eb) = RelV (leavesSubSpec (Expr.fvarLeaves eb)) st fab r :=
  rfl

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1264-1268 leafGuard — the
cutoff: an `fvar`-free fabrication passes. -/
theorem LeafGuardAt.cut {st : EStore} (hwf : StoreWF st) {fab : EIdx} (base : EIdx)
    (h0 : (fvarOfData (st.derived fab)).toNat = 0) : LeafGuardAt st fab base true :=
  fun eb _ => leavesSub_cut_of_derived hwf (Expr.fvarLeaves eb) h0
grind_pattern [bridge_grind] LeafGuardAt.cut => LeafGuardAt st fab base true

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1264-1268 leafGuard — **the
composition**: the walk's verdict against a list with `base`'s leaves as its
MEMBERS is the guard's (`leavesSubSpec_congr`), keyed by the walk's answer and
the leaf list's. -/
theorem LeafGuardAt.of_lSubAt {st : EStore} {fab base : EIdx} {rs : List (Nat × EIdx)}
    {r : Bool} (hl : LeavesEq st [] base rs) (hrs : (denoteLeaves st rs).isSome = true)
    (hs : LSubAt rs st fab r) : LeafGuardAt st fab base r := by
  intro eb heb
  obtain ⟨bl', hbl'⟩ := Option.isSome_iff_exists.mp hrs
  intro e he
  rw [hs bl' hbl' e he]
  refine leavesSubSpec_congr (fun x => ?_) e
  have := hl eb [] bl' heb rfl hbl' x
  simpa using this
grind_pattern [bridge_grind] LeafGuardAt.of_lSubAt => LSubAt rs st fab r, LeavesEq st [] base rs

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1264-1268 leafGuard — **THEOREM
1 for `leafGuard`**.  Complete except for the `fvarLeavesGo` gray clause it
inherits through `Leaves.lean`'s `fvarLeavesFast_spec`. -/
theorem leafGuard_spec (fuel : Nat) (s₀ : AState) (fab base : EIdx)
    (hok : StateOK s₀) (hfab : (denoteE s₀.store fab).isSome = true)
    (hbase : (denoteE s₀.store base).isSome = true) :
    ⦃fun s => s = s₀⦄ leafGuard fuel fab base
    ⦃fun r s' => s' = s₀ ∧ LeafGuardAt s₀.store fab base r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [leafGuard, fvarLeavesFast_spec fuel, fun bl => (leavesSubGo_spec bl fuel).run] <;>
      finish

/-! ## The axiom check -/

#print axioms wscopedB_cut_of_derived
#print axioms wscopedBGo_spec
#print axioms wscopedBFast_spec
#print axioms leavesSub_cut_of_derived
#print axioms leavesSubSpec_congr
#print axioms leavesSubGo_spec
#print axioms leafGuard_spec

end ConRon.Bridge.ExprOps

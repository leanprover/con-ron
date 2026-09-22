/-
# `ConRon.Arena.ExprOps` — the `ExprOps` twins (DESIGN.md §8.6 P2b)

`ConLeche/Kernel/ExprOps.lean`, clause for clause, over handles: 70 (T)
declarations of the census (`Arena/CENSUS.md`, "P2b — the `ExprOps` twins,
with memo"), written in the Rust-shaped style of DESIGN §8.4 — no `for`, no
`mut`, no closures, no `partial`, explicit recursion with fuel where
con-leche recurses structurally on `Expr`, detach before update at every
mutation, one `def` per intended Rust function.

## The four rules this module is written by

1. **`view` where con-leche matched, `intern` where it built, handle equality
   where it compared** (§8.3).  A leaf arm that con-leche writes as
   `| .fvar idx ty => .fvar idx ty` is `pure h` here: the node is already in
   the store and `denoteE` is injective, so rebuilding it would be the same
   handle.

2. **Fuel.**  A handle DAG has no structural order the elaborator can see, so
   every walk over the DAG takes an explicit `fuel : Nat` and `fail`s when it
   runs out.  Exhaustion is a failure and Theorem 1 will claim nothing on
   failure (con-leche's `SimAt` shape), so the fuel is invisible above this
   module.  A recursion that is structural on something else — a `Nat` binder
   count (`stripPis`), a `List` of arguments (`mkAppN`), a transient `Level`
   tree (`internLevel`) — takes no fuel.

3. **The memo lives in the state** (§8.3 "Caches").  con-leche threads it as
   an argument-and-result pair (`instantiate1Go v memo e d`); here it is a
   field of `AState`, keyed `(EIdx, cursor)` as nanoda keys it, and dropped
   at the top-level entry — which is why the substituted term is not in the
   key.  Each `…Fast` entry is con-leche's `(…Go v {} e d).1`: clear, walk,
   clear.

4. **One `def` per intended Rust function, and nothing that is not one.**
   Task #97s round 2 asks (B) to be written with one `def` per CONSTRUCTOR
   ARM, because that is what makes the later `mvcgen` proofs elaborate in
   seconds instead of minutes.  It cannot be done the way the spike does it —
   the spike passes the dispatcher to each arm as a function ARGUMENT, and a
   closure is exactly what DESIGN §3.4 forbids in code Aeneas must translate.
   The arms are therefore inlined here, which is also con-leche's own shape
   (one function per walk, all ten arms inside it).  When P3 splits them the
   split must be a `mutual` block whose arms call the dispatcher by name, not
   a function passed in; it is mechanical, and the memo probes mark where the
   cuts go.

## The cutoffs (§8.3 lesson 20)

Every traversal that con-leche cuts off on a derived field cuts off here on
the same one, read in `O(1)` off the derived column instead of recomputed:

| walk | cutoff | con-leche's licence |
|---|---|---|
| `instantiate1Go` | `bvarBRaw < satRange && bvarBRaw ≤ d` | `bvarBRaw_exact` + task #97s's `instantiate1_of_bvarBound_le` |
| `abstract1Go` | `fvarB ≤ d` | `abstract1_of_fvarRange_le` |
| `lowerBVarsGo` | `bvarB ≤ c + amount` | `lowerBVars_of_bvarBound_le` |
| `instantiate1LiftGo` | `bvarB ≤ d` | `instantiate1Lift_of_bvarBound_le` |
| `instLPGo` | `hasLP = false` | `Expr.instantiateLevelParams_eq_self` |
| `instantiateList`, `instantiateListGo` | `bvarBRaw < satRange && bvarBRaw ≤ d` | DERIVED, below |
| `liftLooseBVarsGo` | `bvarBRaw < satRange && bvarBRaw ≤ c` | DERIVED, below |

`instantiate1Go`'s is one of three cutoffs con-leche does NOT have (its
`instantiate1Go` walks unconditionally); DESIGN §8.3 asks for it by name and
task #97s proved its licence, so the arena takes it.  `resetMeta` and
`renameConsts` have no cutoff in con-leche and none here — neither reads a
derived field that decides them.

**The two derived cutoffs (task #97f, P2f).**  `instantiateList` and
`liftLooseBVars` have no cutoff in con-leche either, and task #97b left them
without one because "a cutoff the original does not have needs its licence
proved".  P2f's gate is what forced the question: `tests/e2e/proj_share.ndjson`
does not finish without them, with 18 % of its cycles in `instantiateList`.
The licence is elementary and is written out here for P3 to discharge as two
`Expr`-level lemmas (the shape of `ExprOps.lean`'s own
`lowerBVars_of_bvarBound_le`, which is the SAME argument at a different
offset):

  * `looseBVarsBounded d e → instantiateList e vs d = e`.  Induction on `e`.
    The only clause that is not the congruence is `.bvar j`, and
    `looseBVarsBounded d (.bvar j)` is `j < d`, which takes the `if j < d`
    branch — `.bvar j` unchanged.  Under a binder the hypothesis weakens
    from `d` to `d + 1`, which is what the recursive call passes.
  * `looseBVarsBounded c e → liftLooseBVars e c amount = e`.  Identically:
    `.bvar j` with `j < c` fails `j ≥ c` and is returned unchanged.

`looseBVarsBounded k e` is `e.bvarBound ≤ k`, and the store's derived word is
con-leche's own `Expr.data` (§8.3), so `bvarBRaw < satRange` is exactly the
side condition under which the packed field IS `e.bvarBound` — the same guard
`instantiate1Go` carries, and the reason neither cutoff needs the saturated
branch's memoized recomputation (`bvarB`, which is defined below these walks
anyway).  Both cutoffs are therefore DENOTATION-PRESERVING: on a handle they
answer, the walk they replace returns that same handle, because the rebuild
of an unchanged node is the node (`denoteE` is injective, so `intern` of a
node's own view is that node).

The pure `instantiateList` carries the cutoff too, not only the memoized
`instantiateListGo`: its `.bvar` arm recurses into the REPLACEMENT
`vs[j - d]` with a shorter list and no memo, and con-leche's own note says
that on the `bvar`-closed replacements every checker call site passes, that
recursion is the identity.  With the cutoff it *is* one `O(1)` test instead
of a full traversal of the replacement, which is where `proj_share`'s 18 %
lived.

## Levels are read back, not twinned (§8.3 lesson 4)

`instLPGo` is the only twin that touches a level ALGORITHM.  It reads the
substitution back out of the store once, at the top-level entry, runs
con-leche's own `Level.subst` / `Level.substPW` on the transient trees, and
re-interns the result.  `Level.hasParam` and `Expr.hasLevelParam` are not
walks at all here: both are exactly the derived bit the store already carries.
-/
import ConRon.Arena.Monad

namespace ConRon.Arena

open ConLeche

/-! ## The UPWARD cutoff of a substituting walk (task #97-P6-5, lever 2)

**A rebuilt spine whose children did not change is the same node.**  `h`
decodes to a view whose children the walk has just rewritten; if every
rewritten child is the child it started from, then the view handed here IS the
view `h` decodes to, and `intern` would answer `h` — the store is hash-consed,
`denoteE` is injective, and §8.3's cross-tier rule ("a scratch entry never
duplicates a persistent one") makes the answer `h` and not some twin of `h` in
the other tier.  So the test replaces a cons-table probe with one word
comparison per child.

It is applied ONLY to the walks whose downward cutoff is inexact, which is
where it can fire at all: `abstract1Go` (the cutoff is `fvarB ≤ d`, and the arm
abstracts the index `= d`), `abstractRangeGo`, `instLPGo` (the cutoff is the
`hasLP` bit, and a substitution touching none of the parameters present is the
identity), `resetMetaGo` (no downward cutoff at all) and `renameConstsGo`.
`instantiate1Go`, `instantiateListGo`, `liftLooseBVarsGo`, `lowerBVarsGo` and
`instantiate1LiftGo` are NOT given it: their cutoff is `bvarB ≤ d` against a
field that is EXACT below saturation, so past the cutoff a loose `bvar` at or
above `d` really is present and really does move. -/

/-- con-leche: none — `internE` with task #97-P6-5's upward cutoff. -/
@[inline] def internRebuilt (h : EIdx) (same : Bool) (v : ENodeView) : AM EIdx :=
  if same then pure h else internE v

/-- con-leche: none — `internRebuilt` at the `bvar` arm's FIELDS (task
#97-P6-15): the view is never built. -/
@[inline] def internRebuiltBVar (h : EIdx) (same : Bool) (i : Nat) : AM EIdx :=
  if same then pure h else internBVarE i
/-- con-leche: none — `internRebuilt` at the `fvar` arm's fields. -/
@[inline] def internRebuiltFVar (h : EIdx) (same : Bool) (idx : Nat) (ty : EIdx) :
    AM EIdx := if same then pure h else internFVarE idx ty
/-- con-leche: none — `internRebuilt` at the `sort` arm's fields. -/
@[inline] def internRebuiltSort (h : EIdx) (same : Bool) (u : LIdx) : AM EIdx :=
  if same then pure h else internSortE u
/-- con-leche: none — `internRebuilt` at the `const` arm's fields. -/
@[inline] def internRebuiltConst (h : EIdx) (same : Bool) (n : NIdx) (us : LsIdx) :
    AM EIdx := if same then pure h else internConstE n us
/-- con-leche: none — `internRebuilt` at the `app` arm's fields. -/
@[inline] def internRebuiltApp (h : EIdx) (same : Bool) (f a : EIdx) : AM EIdx :=
  if same then pure h else internAppE f a
/-- con-leche: none — `internRebuilt` at the `lam` arm's fields. -/
@[inline] def internRebuiltLam (h : EIdx) (same : Bool) (ty b : EIdx)
    (m : ConLeche.BinderMeta) : AM EIdx :=
  if same then pure h else internLamE ty b m
/-- con-leche: none — `internRebuilt` at the `forallE` arm's fields. -/
@[inline] def internRebuiltForallE (h : EIdx) (same : Bool) (ty b : EIdx)
    (m : ConLeche.BinderMeta) : AM EIdx :=
  if same then pure h else internForallEE ty b m
/-- con-leche: none — `internRebuilt` at the `letE` arm's fields. -/
@[inline] def internRebuiltLetE (h : EIdx) (same : Bool) (ty val b : EIdx) :
    AM EIdx := if same then pure h else internLetEE ty val b
/-- con-leche: none — `internRebuilt` at the `lit` arm's fields. -/
@[inline] def internRebuiltLit (h : EIdx) (same : Bool) (l : ConLeche.Literal) :
    AM EIdx := if same then pure h else internLitE l
/-- con-leche: none — `internRebuilt` at the `proj` arm's fields. -/
@[inline] def internRebuiltProj (h : EIdx) (same : Bool) (n : NIdx) (i : Nat)
    (e : EIdx) : AM EIdx := if same then pure h else internProjE n i e

/-- con-leche: none — `internRebuilt`'s two binder arms at a tag the caller
carries (`eBindView`'s own choice), for the walks whose binder clause is
shared between `lam` and `forallE`. -/
@[inline] def internRebuiltBind (h : EIdx) (same : Bool) (tag : UInt32)
    (ty b : EIdx) (m : ConLeche.BinderMeta) : AM EIdx :=
  if same then pure h
  else if tag == ETag.lam then internLamE ty b m else internForallEE ty b m

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta —
`internRebuiltBind` at a binder datum the walk is CARRYING ACROSS rather than
changing (task #97-P6-16): a substituting walk takes a binder apart and puts
it back with the same datum, and since the datum is interned the round trip
carries its `BMIdx` and never decodes it. -/
@[inline] def internRebuiltBindI (h : EIdx) (same : Bool) (tag : UInt32)
    (ty b : EIdx) (mi : BMIdx) : AM EIdx :=
  if same then pure h else internBindIE tag ty b mi

/-! ## Handle vectors, built by `Array.push`

The maintainer's ruling (DESIGN §8.6, before §8.7): *a `List` accumulator
built by `::` in the Lean twin, mirrored as an insert-at-front on a `Vec`, is
quadratic and silly.  The twin uses `Array` with `Array.push` and the Rust
`Vec::push` — idiomatic in both tiers, the same denotation as the reversed
list — and reads the accumulator from the end where the algorithm consumed the
list's head.*  So the substituting walks' argument vectors are `Array EIdx` in
PUSH order: con-leche's `vs[j - d]`, the innermost binder's argument first, is
this array's entry `j - d` FROM THE END. -/

/-- con-leche: none — copy `xs[i], …, xs[k-1]` onto `out`, in order. -/
def eidxCopyUpto (xs : Array EIdx) (k i : Nat) (out : Array EIdx) : Array EIdx :=
  if h : i < k ∧ i < xs.size then
    eidxCopyUpto xs k (i + 1) (out.push xs[i])
  else out
termination_by k - i
decreasing_by omega

/-- con-leche: none — the `O(1)` cutoff of a bulk instantiation, off the
handle's own derived word: a node whose loose-bvar bound is exact and at most
`d` is its own instantiation (DESIGN §8.3 lesson 20; task #97f's deviation,
denotation-preserving by `looseBVarsBounded d e → instantiateList e vs d = e`). -/
@[inline] def instListCutoff (h : EIdx) (d : Nat) : AM Bool := do
  let bRaw := (bvarOfData (← derivedE h)).toNat
  pure (bRaw < satRange && bRaw ≤ d)

/-- con-leche: none — `xs.take k` over a push-order `Array EIdx`. -/
def takeEidx (xs : Array EIdx) (k : Nat) : Array EIdx := eidxCopyUpto xs k 0 #[]

/-- con-leche: none — the LAST `k` entries of a push-order array, which is
`List.take k` on the list it denotes (the reverse of the array). -/
def lastEidx (xs : Array EIdx) (k : Nat) : Array EIdx :=
  eidxCopyUpto xs xs.size (if k < xs.size then xs.size - k else 0) #[]

/-! ## `instantiate1` — `ExprOps.lean:29-45`, `:80-116`, `:182-184`

One twin for all three: the pure walk is the specification, `instantiate1Go`
is what executes, and the arena has one function — with the memo and the
derived-word cutoff.

**The tag dispatch** (tasks #97-P6-10 and #97-P6-13, and the maintainer's own
ruling before DESIGN §8.7): a clause that is one constructor plus a
fallthrough tests the handle's own tag word BEFORE reading the store, and then
uses the constructor's PROJECTION rather than the whole view.  It is the same
clause: a handle in a well-formed store carries the tag of its own view
(`StoreWF`'s `intern`/`push` clause), and the two forms differ only on a
DANGLING handle, where the `else` arm answers `h` and `view` would fail — a
state the checker never builds and `StoreWF` excludes.

**The memo probe before the node read**: two reads of the state commute. -/

/-! ### The arms, split (DESIGN §8.6's ruling of 2026-09-22)

The coordinator's ruling after task #97-P3-0: the Lean twin splits every
multi-arm body into one `def` per constructor arm inside a `mutual` block,
the dispatcher calling the arms by name (no closures — DESIGN §3.4).  The
Rust keeps its inline arms; the refinement maps one Rust function onto the
twin's dispatcher-plus-arms, the same denotation, a twin-ledger row of the
"shape" kind.  The measured reason is Theorem 1's elaboration: 72 s on this
one inline body (task #97-P3-0's §4) against a few seconds per arm.

**Where the cut goes**: at the memo probe (task #97b).  Each arm owns its
probe, its projection, its recursion, its rebuild and its insert; the
dispatcher is the cutoff, the tag chain and nothing else.  The measure is the
lexicographic `(fuel, tag)` task #97b predicted — the dispatcher at tag `0`
calls an arm at `fuel - 1`, and an arm at tag `1` calls the dispatcher at its
own fuel.  A leaf arm whose whole body is `pure h` has nothing to split and
stays in the dispatcher. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the
`bvar` arm.  It does not recurse, so it sits outside the `mutual` block:
`i = d` answers the substituted handle, `i > d` interns the lowered index,
`i < d` answers the handle itself. -/
def instantiate1ArmBVar (v : EIdx) (h : EIdx) (d : Nat) : AM EIdx := do
  match ← viewBVar h with
  | none => failDanglingE
  | some i =>
    if i = d then pure v
    else if i > d then internBVarE (i - 1)
    else pure h

mutual

/-- con-leche: ConLeche/Kernel/ExprOps.lean:29-45 instantiate1
con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go
Replace `bvar d` by `v`, lowering loose `bvar`s above `d` by one.  The
derived-word cutoff comes first (`bvarB ≤ d`, read off the packed word in
`O(1)`); the five leaf kinds answer without touching the memo; everything
else hands off to its arm, which probes the memo, runs the body one level
down and inserts.

`else .bvar i` is `pure h`: the node is already interned and `denoteE` is
injective, so rebuilding it yields the same handle. -/
def instantiate1Go (v : EIdx) (fuel : Nat) (h : EIdx) (d : Nat) : AM EIdx :=
  match fuel with
  | 0 => fail (.internal "fuel exhausted: instantiate1")
  | fuel + 1 => do
    let der ← derivedE h
    let b := (bvarOfData der).toNat
    if b < satRange && b ≤ d then
      pure h
    else
      let tg := h.tag
      if tg == ETag.app then instantiate1ArmApp v fuel h d
      else if ETag.isBind tg then instantiate1ArmBind v fuel h d
      else if tg == ETag.bvar then instantiate1ArmBVar v h d
      else if tg == ETag.letE then instantiate1ArmLet v fuel h d
      else if tg == ETag.proj then instantiate1ArmProj v fuel h d
      else pure h
termination_by (fuel, 0)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the `app`
arm: probe, project, recurse into both children, rebuild, insert. -/
def instantiate1ArmApp (v : EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    AM EIdx := do
  match ← inst1Get (h, d) with
  | some r => pure r
  | none =>
    match ← viewApp h with
    | none => failDanglingE
    | some (f, a) => do
      let f' ← instantiate1Go v fuel f d
      let a' ← instantiate1Go v fuel a d
      let r ← internAppE f' a'
      inst1Set (h, d) r
      pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the
binder arm, `lam` and `forallE` in one exactly as the tag dispatch tests them
(`ETag.isBind`); the datum travels as a HANDLE (task #97-P6-16). -/
def instantiate1ArmBind (v : EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    AM EIdx := do
  match ← inst1Get (h, d) with
  | some r => pure r
  | none =>
    match ← viewBindI h with
    | none => failDanglingE
    | some (ty, body, m) => do
      let t ← instantiate1Go v fuel ty d
      let b' ← instantiate1Go v fuel body (d + 1)
      let r ← internBindIE h.tag t b' m
      inst1Set (h, d) r
      pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the
`letE` arm; the body descends at `d + 1`. -/
def instantiate1ArmLet (v : EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    AM EIdx := do
  match ← inst1Get (h, d) with
  | some r => pure r
  | none =>
    match ← viewLet h with
    | none => failDanglingE
    | some (ty, val, body) => do
      let t ← instantiate1Go v fuel ty d
      let w ← instantiate1Go v fuel val d
      let b' ← instantiate1Go v fuel body (d + 1)
      let r ← internLetEE t w b'
      inst1Set (h, d) r
      pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the
`proj` arm. -/
def instantiate1ArmProj (v : EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    AM EIdx := do
  match ← inst1Get (h, d) with
  | some r => pure r
  | none =>
    match ← viewProj h with
    | none => failDanglingE
    | some (n, i, sub) => do
      let u ← instantiate1Go v fuel sub d
      let r ← internProjE n i u
      inst1Set (h, d) r
      pure r
termination_by (fuel, 1)

end

/-- con-leche: none — `instantiate1Go`'s clause at fuel `0`, as an equation
lemma.  Template rule 9 (DESIGN, task #97-P3-0 §4): a walk whose measure is
`termination_by` rather than a constructor pattern needs its clauses as
lemmas, or `mvcgen [f]` rewrites the recursive call forever. -/
theorem instantiate1Go_zero (v h : EIdx) (d : Nat) :
    instantiate1Go v 0 h d =
      fail (.internal "fuel exhausted: instantiate1") := by
  rw [instantiate1Go]

/-- con-leche: none — `instantiate1Go`'s clause at `fuel + 1` (template rule
9): the cutoff, then the tag chain, then the arms by name. -/
theorem instantiate1Go_succ (v : EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    instantiate1Go v (fuel + 1) h d = (do
      let der ← derivedE h
      let b := (bvarOfData der).toNat
      if b < satRange && b ≤ d then
        pure h
      else
        let tg := h.tag
        if tg == ETag.app then instantiate1ArmApp v fuel h d
        else if ETag.isBind tg then instantiate1ArmBind v fuel h d
        else if tg == ETag.bvar then instantiate1ArmBVar v h d
        else if tg == ETag.letE then instantiate1ArmLet v fuel h d
        else if tg == ETag.proj then instantiate1ArmProj v fuel h d
        else pure h) := by
  rw [instantiate1Go]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast — the
top-level entry: `(instantiate1Go v {} e d).1`, i.e. the memo is fresh before
and dropped after, because it depends on the substituted term. -/
def instantiate1Fast (fuel : Nat) (e v : EIdx) (d : Nat := 0) : AM EIdx := do
  inst1Clear
  let r ← instantiate1Go v fuel e d
  inst1Clear
  pure r

/-! ## `instantiateList` — `ExprOps.lean:191-235`, `:267-303`, `:371-373`

**Two** twins, not one: `instantiateListGo`'s `bvar` arm calls the PURE
`instantiateList` (`ExprOps.lean:288`), because that arm recurses into the
replacement with a *shorter* list and the memo is keyed for the outer one. -/

mutual

/-- con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList — the
unmemoized bulk instantiation.  con-leche's termination measure is
`(vs.length, sizeOf e)`; the arena's single fuel counter decreases on both
kinds of recursive call, which is the same order flattened.  This is the
DISPATCHER; the arms are split per DESIGN §8.6's ruling of 2026-09-22.

DEVIATION (task #97f): the derived-word cutoff `bvarBRaw < satRange &&
bvarBRaw ≤ d`, which con-leche does not have.  Denotation-preserving by
`looseBVarsBounded d e → instantiateList e vs d = e` (the module note above
states the induction; P3 discharges it).  It is what makes the `.bvar` arm's
recursion into a `bvar`-closed replacement `O(1)` instead of a traversal. -/
def instantiateList (vs : Array EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    AM EIdx :=
  match fuel with
  | 0 => fail (.internal "fuel exhausted: instantiateList")
  | fuel + 1 => do
    if ← instListCutoff h d then
      pure h
    else
      let tg := h.tag
      if tg == ETag.app then instListArmApp vs fuel h d
      else if ETag.isBind tg then instListArmBind vs fuel h d
      else if tg == ETag.letE then instListArmLet vs fuel h d
      else if tg == ETag.proj then instListArmProj vs fuel h d
      else if tg == ETag.bvar then instListArmBVar vs fuel h d
      else pure h
termination_by (fuel, 0)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList — the
`app` arm. -/
def instListArmApp (vs : Array EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    AM EIdx := do
  match ← viewApp h with
  | none => failDanglingE
  | some (f, a) => do
    let f' ← instantiateList vs fuel f d
    let a' ← instantiateList vs fuel a d
    internAppE f' a'
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList — the
binder arm. -/
def instListArmBind (vs : Array EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    AM EIdx := do
  match ← viewBindI h with
  | none => failDanglingE
  | some (ty, body, m) => do
    let t ← instantiateList vs fuel ty d
    let b ← instantiateList vs fuel body (d + 1)
    internBindIE h.tag t b m
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList — the
`letE` arm. -/
def instListArmLet (vs : Array EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    AM EIdx := do
  match ← viewLet h with
  | none => failDanglingE
  | some (ty, val, body) => do
    let t ← instantiateList vs fuel ty d
    let w ← instantiateList vs fuel val d
    let b ← instantiateList vs fuel body (d + 1)
    internLetEE t w b
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList — the
`proj` arm. -/
def instListArmProj (vs : Array EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    AM EIdx := do
  match ← viewProj h with
  | none => failDanglingE
  | some (n, i, sub) => do
    let u ← instantiateList vs fuel sub d
    internProjE n i u
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList — the
`bvar` arm, which is the one that recurses with a SHORTER argument vector. -/
def instListArmBVar (vs : Array EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    AM EIdx := do
  match ← viewBVar h with
  | none => failDanglingE
  | some j =>
    if j < d then pure h
    else if hlt : j - d < vs.size then
      -- **`vs` is in PUSH order** (task #97-P6-15): con-leche's `vs[j - d]`,
      -- the innermost binder's argument first, is this array's entry `j - d`
      -- FROM THE END.  The two are the same list; only the direction the
      -- accumulator grows changed.
      let vi := vs[vs.size - 1 - (j - d)]'(by omega)
      -- **The cutoff hoisted over the prefix copy** (task #97-P6-9).  The
      -- recursion into the replacement is con-leche's own
      -- `instantiateList vs[j-d] (vs.take (j-d)) d`, and its own note says it
      -- is the identity on `bvar`-closed replacements (every checker call
      -- site) — which is exactly what `instListCutoff` decides, in `O(1)` off
      -- the handle's derived word.  Testing it BEFORE the prefix copy is the
      -- same value, by the cutoff's own equation
      -- `looseBVarsBounded d e → instantiateList e vs d = e`.
      if ← instListCutoff vi d then pure vi
      else instantiateList (lastEidx vs (j - d)) fuel vi d
    else internBVarE (j - vs.size)
termination_by (fuel, 1)

end

/-- con-leche: none — `instantiateList`'s clause at fuel `0` (template rule
9, DESIGN task #97-P3-0 §4). -/
theorem instantiateList_zero (vs : Array EIdx) (h : EIdx) (d : Nat) :
    instantiateList vs 0 h d =
      fail (.internal "fuel exhausted: instantiateList") := by
  rw [instantiateList]

/-- con-leche: none — `instantiateList`'s clause at `fuel + 1` (template rule
9). -/
theorem instantiateList_succ (vs : Array EIdx) (fuel : Nat) (h : EIdx)
    (d : Nat) :
    instantiateList vs (fuel + 1) h d = (do
      if ← instListCutoff h d then
        pure h
      else
        let tg := h.tag
        if tg == ETag.app then instListArmApp vs fuel h d
        else if ETag.isBind tg then instListArmBind vs fuel h d
        else if tg == ETag.letE then instListArmLet vs fuel h d
        else if tg == ETag.proj then instListArmProj vs fuel h d
        else if tg == ETag.bvar then instListArmBVar vs fuel h d
        else pure h) := by
  rw [instantiateList]
mutual

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
memoized bulk instantiation.  The `bvar` arm delegates to the pure walk
above, exactly as con-leche's does — so it is called by name and is not one
of this block's arms.  This is the DISPATCHER; the arms are split per DESIGN
§8.6's ruling of 2026-09-22.

DEVIATION (task #97f): the same derived-word cutoff as the pure walk, with
the same licence. -/
def instantiateListGo (vs : Array EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    AM EIdx :=
  match fuel with
  | 0 => fail (.internal "fuel exhausted: instantiateList")
  | fuel + 1 => do
    if ← instListCutoff h d then
      pure h
    else
      let tg := h.tag
      if tg == ETag.app then instListGoArmApp vs fuel h d
      else if ETag.isBind tg then instListGoArmBind vs fuel h d
      else if tg == ETag.letE then instListGoArmLet vs fuel h d
      else if tg == ETag.proj then instListGoArmProj vs fuel h d
      else if tg == ETag.bvar then instantiateList vs fuel h d
      else pure h
termination_by (fuel, 0)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
`app` arm. -/
def instListGoArmApp (vs : Array EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    AM EIdx := do
  match ← instLGet (h, d) with
  | some r => pure r
  | none =>
    match ← viewApp h with
    | none => failDanglingE
    | some (f, a) => do
      let f' ← instantiateListGo vs fuel f d
      let a' ← instantiateListGo vs fuel a d
      let r ← internAppE f' a'
      instLSet (h, d) r
      pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
binder arm. -/
def instListGoArmBind (vs : Array EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    AM EIdx := do
  match ← instLGet (h, d) with
  | some r => pure r
  | none =>
    match ← viewBindI h with
    | none => failDanglingE
    | some (ty, body, m) => do
      let t ← instantiateListGo vs fuel ty d
      let b ← instantiateListGo vs fuel body (d + 1)
      let r ← internBindIE h.tag t b m
      instLSet (h, d) r
      pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
`letE` arm. -/
def instListGoArmLet (vs : Array EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    AM EIdx := do
  match ← instLGet (h, d) with
  | some r => pure r
  | none =>
    match ← viewLet h with
    | none => failDanglingE
    | some (ty, val, body) => do
      let t ← instantiateListGo vs fuel ty d
      let w ← instantiateListGo vs fuel val d
      let b ← instantiateListGo vs fuel body (d + 1)
      let r ← internLetEE t w b
      instLSet (h, d) r
      pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
`proj` arm. -/
def instListGoArmProj (vs : Array EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    AM EIdx := do
  match ← instLGet (h, d) with
  | some r => pure r
  | none =>
    match ← viewProj h with
    | none => failDanglingE
    | some (n, i, sub) => do
      let u ← instantiateListGo vs fuel sub d
      let r ← internProjE n i u
      instLSet (h, d) r
      pure r
termination_by (fuel, 1)

end

/-- con-leche: none — `instantiateListGo`'s clause at fuel `0` (template rule
9). -/
theorem instantiateListGo_zero (vs : Array EIdx) (h : EIdx) (d : Nat) :
    instantiateListGo vs 0 h d =
      fail (.internal "fuel exhausted: instantiateList") := by
  rw [instantiateListGo]

/-- con-leche: none — `instantiateListGo`'s clause at `fuel + 1` (template
rule 9). -/
theorem instantiateListGo_succ (vs : Array EIdx) (fuel : Nat) (h : EIdx)
    (d : Nat) :
    instantiateListGo vs (fuel + 1) h d = (do
      if ← instListCutoff h d then
        pure h
      else
        let tg := h.tag
        if tg == ETag.app then instListGoArmApp vs fuel h d
        else if ETag.isBind tg then instListGoArmBind vs fuel h d
        else if tg == ETag.letE then instListGoArmLet vs fuel h d
        else if tg == ETag.proj then instListGoArmProj vs fuel h d
        else if tg == ETag.bvar then instantiateList vs fuel h d
        else pure h) := by
  rw [instantiateListGo]
/-- con-leche: ConLeche/Kernel/ExprOps.lean:371-373 instantiateListFast — the
top-level entry. -/
def instantiateListFast (fuel : Nat) (e : EIdx) (vs : Array EIdx) (d : Nat := 0) :
    AM EIdx := do
  instLClear
  let r ← instantiateListGo vs fuel e d
  instLClear
  pure r

/-! ## `liftLooseBVars` — `ExprOps.lean:380-400`, `:430-466`, `:532-534` -/

mutual

/-- con-leche: ConLeche/Kernel/ExprOps.lean:380-400 liftLooseBVars
con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo
Bump every loose bound variable `≥ cutoff` by `amount`.  This is the
DISPATCHER (arms split per DESIGN §8.6's ruling of 2026-09-22).  A leaf arm
whose whole body is `pure h` has nothing to split and stays here; every arm
with a memo probe is a `def` of its own, and takes the children the
dispatcher's `view` already projected — a second store read per node is what
the split must NOT cost.

DEVIATION (task #97f): the derived-word cutoff `bvarBRaw < satRange &&
bvarBRaw ≤ c`, which con-leche does not have.  Denotation-preserving by
`looseBVarsBounded c e → liftLooseBVars e c amount = e` (the module note
above states the induction; P3 discharges it). -/
def liftLooseBVarsGo (amount : Nat) (fuel : Nat) (h : EIdx) (c : Nat) :
    AM EIdx :=
  match fuel with
  | 0 => fail (.internal "fuel exhausted: liftLooseBVars")
  | fuel + 1 => do
    let bRaw := (bvarOfData (← derivedE h)).toNat
    if bRaw < satRange && bRaw ≤ c then
      pure h
    else
    match ← view h with
    | .bvar i => if i ≥ c then internE (.bvar (i + amount)) else pure h
    | .fvar _ _ => pure h
    | .sort _ => pure h
    | .const _ _ => pure h
    | .lit _ => pure h
    | .app a b => liftArmApp amount fuel h c a b
    | .lam ty body m => liftArmLam amount fuel h c ty body m
    | .forallE ty body m => liftArmForallE amount fuel h c ty body m
    | .letE ty val body => liftArmLet amount fuel h c ty val body
    | .proj n i sub => liftArmProj amount fuel h c n i sub
termination_by (fuel, 0)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo — the
`app` arm. -/
def liftArmApp (amount fuel : Nat) (h : EIdx) (c : Nat) (a b : EIdx) :
    AM EIdx := do
  match ← liftGet (h, c) with
  | some r => pure r
  | none => do
    let a' ← liftLooseBVarsGo amount fuel a c
    let b' ← liftLooseBVarsGo amount fuel b c
    let r ← internE (.app a' b')
    liftSet (h, c) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo — the
`lam` arm; the body descends at `c + 1`. -/
def liftArmLam (amount fuel : Nat) (h : EIdx) (c : Nat) (ty body : EIdx)
    (m : ConLeche.BinderMeta) : AM EIdx := do
  match ← liftGet (h, c) with
  | some r => pure r
  | none => do
    let t ← liftLooseBVarsGo amount fuel ty c
    let b ← liftLooseBVarsGo amount fuel body (c + 1)
    let r ← internE (.lam t b m)
    liftSet (h, c) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo — the
`forallE` arm. -/
def liftArmForallE (amount fuel : Nat) (h : EIdx) (c : Nat) (ty body : EIdx)
    (m : ConLeche.BinderMeta) : AM EIdx := do
  match ← liftGet (h, c) with
  | some r => pure r
  | none => do
    let t ← liftLooseBVarsGo amount fuel ty c
    let b ← liftLooseBVarsGo amount fuel body (c + 1)
    let r ← internE (.forallE t b m)
    liftSet (h, c) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo — the
`letE` arm. -/
def liftArmLet (amount fuel : Nat) (h : EIdx) (c : Nat) (ty val body : EIdx) :
    AM EIdx := do
  match ← liftGet (h, c) with
  | some r => pure r
  | none => do
    let t ← liftLooseBVarsGo amount fuel ty c
    let w ← liftLooseBVarsGo amount fuel val c
    let b ← liftLooseBVarsGo amount fuel body (c + 1)
    let r ← internE (.letE t w b)
    liftSet (h, c) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo — the
`proj` arm. -/
def liftArmProj (amount fuel : Nat) (h : EIdx) (c : Nat) (n : NIdx) (i : Nat)
    (sub : EIdx) : AM EIdx := do
  match ← liftGet (h, c) with
  | some r => pure r
  | none => do
    let u ← liftLooseBVarsGo amount fuel sub c
    let r ← internE (.proj n i u)
    liftSet (h, c) r
    pure r
termination_by (fuel, 1)

end

/-- con-leche: none — `liftLooseBVarsGo`'s clause at fuel `0` (template rule
9). -/
theorem liftLooseBVarsGo_zero (amount : Nat) (h : EIdx) (c : Nat) :
    liftLooseBVarsGo amount 0 h c =
      fail (.internal "fuel exhausted: liftLooseBVars") := by
  rw [liftLooseBVarsGo]

/-- con-leche: none — `liftLooseBVarsGo`'s clause at `fuel + 1` (template
rule 9). -/
theorem liftLooseBVarsGo_succ (amount fuel : Nat) (h : EIdx) (c : Nat) :
    liftLooseBVarsGo amount (fuel + 1) h c = (do
      let bRaw := (bvarOfData (← derivedE h)).toNat
      if bRaw < satRange && bRaw ≤ c then
        pure h
      else
      match ← view h with
      | .bvar i => if i ≥ c then internE (.bvar (i + amount)) else pure h
      | .fvar _ _ => pure h
      | .sort _ => pure h
      | .const _ _ => pure h
      | .lit _ => pure h
      | .app a b => liftArmApp amount fuel h c a b
      | .lam ty body m => liftArmLam amount fuel h c ty body m
      | .forallE ty body m => liftArmForallE amount fuel h c ty body m
      | .letE ty val body => liftArmLet amount fuel h c ty val body
      | .proj n i sub => liftArmProj amount fuel h c n i sub) := by
  rw [liftLooseBVarsGo]
/-- con-leche: ConLeche/Kernel/ExprOps.lean:532-534 liftLooseBVarsFast — the
top-level entry. -/
def liftLooseBVarsFast (fuel amount c : Nat) (e : EIdx) : AM EIdx := do
  liftClear
  let r ← liftLooseBVarsGo amount fuel e c
  liftClear
  pure r

/-! ## `resetMeta` — `ExprOps.lean:552-559`, `:579-615`, `:687-688`

The memo has no cursor in con-leche; the arena keys it at `0` so that every
handle-valued memo has one shape (see `Memos`). -/

mutual

/-- con-leche: ConLeche/Kernel/ExprOps.lean:552-559 resetMeta
con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo
Reset every binder's prop-ness datum to the parse placeholder; the `fvar`
annotation is descended into.  The dispatcher (arms split per DESIGN §8.6's
ruling of 2026-09-22); the four leaf arms are `pure h` and stay here. -/
def resetMetaGo (fuel : Nat) (h : EIdx) : AM EIdx :=
  match fuel with
  | 0 => fail (.internal "fuel exhausted: resetMeta")
  | fuel + 1 => do
    match ← view h with
    | .bvar _ => pure h
    | .sort _ => pure h
    | .const _ _ => pure h
    | .lit _ => pure h
    | .fvar i ty => resetArmFVar fuel h i ty
    | .app f a => resetArmApp fuel h f a
    | .lam ty body m0 => resetArmLam fuel h ty body m0
    | .forallE ty body m0 => resetArmForallE fuel h ty body m0
    | .letE ty val body => resetArmLet fuel h ty val body
    | .proj n i sub => resetArmProj fuel h n i sub
termination_by (fuel, 0)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo — the `fvar`
arm: the annotation is descended into. -/
def resetArmFVar (fuel : Nat) (h : EIdx) (i : Nat) (ty : EIdx) : AM EIdx := do
  match ← resetGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← resetMetaGo fuel ty
    let r ← internRebuiltFVar h (t == ty) i t
    resetSet (h, 0) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo — the `app`
arm. -/
def resetArmApp (fuel : Nat) (h : EIdx) (f a : EIdx) : AM EIdx := do
  match ← resetGet (h, 0) with
  | some r => pure r
  | none => do
    let f' ← resetMetaGo fuel f
    let a' ← resetMetaGo fuel a
    let r ← internRebuiltApp h (f' == f && a' == a) f' a'
    resetSet (h, 0) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo — the `lam`
arm: this is where the datum is reset to the parse placeholder. -/
def resetArmLam (fuel : Nat) (h : EIdx) (ty body : EIdx)
    (m0 : ConLeche.BinderMeta) : AM EIdx := do
  match ← resetGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← resetMetaGo fuel ty
    let b ← resetMetaGo fuel body
    let m2 : ConLeche.BinderMeta := ⟨.never⟩
    let r ← internRebuiltLam h (t == ty && b == body && m2 == m0) t b m2
    resetSet (h, 0) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo — the
`forallE` arm. -/
def resetArmForallE (fuel : Nat) (h : EIdx) (ty body : EIdx)
    (m0 : ConLeche.BinderMeta) : AM EIdx := do
  match ← resetGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← resetMetaGo fuel ty
    let b ← resetMetaGo fuel body
    let m2 : ConLeche.BinderMeta := ⟨.never⟩
    let r ← internRebuiltForallE h (t == ty && b == body && m2 == m0) t b m2
    resetSet (h, 0) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo — the `letE`
arm. -/
def resetArmLet (fuel : Nat) (h : EIdx) (ty val body : EIdx) : AM EIdx := do
  match ← resetGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← resetMetaGo fuel ty
    let w ← resetMetaGo fuel val
    let b ← resetMetaGo fuel body
    let r ← internRebuiltLetE h (t == ty && w == val && b == body) t w b
    resetSet (h, 0) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo — the `proj`
arm. -/
def resetArmProj (fuel : Nat) (h : EIdx) (n : NIdx) (i : Nat) (sub : EIdx) :
    AM EIdx := do
  match ← resetGet (h, 0) with
  | some r => pure r
  | none => do
    let u ← resetMetaGo fuel sub
    let r ← internRebuiltProj h (u == sub) n i u
    resetSet (h, 0) r
    pure r
termination_by (fuel, 1)

end

/-- con-leche: none — `resetMetaGo`'s clause at fuel `0` (template rule 9). -/
theorem resetMetaGo_zero (h : EIdx) :
    resetMetaGo 0 h = fail (.internal "fuel exhausted: resetMeta") := by
  rw [resetMetaGo]

/-- con-leche: none — `resetMetaGo`'s clause at `fuel + 1` (template rule
9). -/
theorem resetMetaGo_succ (fuel : Nat) (h : EIdx) :
    resetMetaGo (fuel + 1) h = (do
      match ← view h with
      | .bvar _ => pure h
      | .sort _ => pure h
      | .const _ _ => pure h
      | .lit _ => pure h
      | .fvar i ty => resetArmFVar fuel h i ty
      | .app f a => resetArmApp fuel h f a
      | .lam ty body m0 => resetArmLam fuel h ty body m0
      | .forallE ty body m0 => resetArmForallE fuel h ty body m0
      | .letE ty val body => resetArmLet fuel h ty val body
      | .proj n i sub => resetArmProj fuel h n i sub) := by
  rw [resetMetaGo]
/-- con-leche: ConLeche/Kernel/ExprOps.lean:687-688 resetMetaFast — the
top-level entry. -/
def resetMetaFast (fuel : Nat) (e : EIdx) : AM EIdx := do
  resetClear
  let r ← resetMetaGo fuel e
  resetClear
  pure r

/-! ## The measures and the scope predicates -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:741-748 sizeB — node count with
`fvar` a leaf (its annotated type ignored): the termination measure for
recursion into instantiated binder bodies. -/
def sizeB : Nat → EIdx → AM Nat
  | 0, _ => fail (.internal "fuel exhausted: sizeB")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lit _ => pure 1
    | .app f a => do
      let x ← sizeB fuel f
      let y ← sizeB fuel a
      pure (x + y + 1)
    | .lam ty body _ | .forallE ty body _ => do
      let x ← sizeB fuel ty
      let y ← sizeB fuel body
      pure (x + y + 1)
    | .letE ty val body => do
      let x ← sizeB fuel ty
      let y ← sizeB fuel val
      let z ← sizeB fuel body
      pure (x + y + z + 1)
    | .proj _ _ sub => do
      let x ← sizeB fuel sub
      pure (x + 1)

mutual

/-- con-leche: ConLeche/Kernel/ExprOps.lean:778-808 abstractRange — bulk
abstraction: close `k` binders in one traversal.  Unmemoized in con-leche and
unmemoized here.  The dispatcher (arms split per DESIGN §8.6's ruling of
2026-09-22); the four leaf arms and the `fvar` arm are single expressions and
stay here. -/
def abstractRange (fuel : Nat) (h : EIdx) (d k c : Nat) : AM EIdx :=
  match fuel with
  | 0 => fail (.internal "fuel exhausted: abstractRange")
  | fuel + 1 => do
    match ← view h with
    | .bvar _ => pure h
    | .fvar idx _ =>
      if d ≤ idx ∧ idx < d + k then internE (.bvar (c + (d + k - 1 - idx)))
      else pure h
    | .sort _ => pure h
    | .const _ _ => pure h
    | .lit _ => pure h
    | .app f a => absRangeArmApp fuel f a d k c
    | .lam ty body m => absRangeArmLam fuel ty body m d k c
    | .forallE ty body m => absRangeArmForallE fuel ty body m d k c
    | .letE ty val body => absRangeArmLet fuel ty val body d k c
    | .proj n i sub => absRangeArmProj fuel n i sub d k c
termination_by (fuel, 0)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:778-808 abstractRange — the `app`
arm. -/
def absRangeArmApp (fuel : Nat) (f a : EIdx) (d k c : Nat) : AM EIdx := do
  let f' ← abstractRange fuel f d k c
  let a' ← abstractRange fuel a d k c
  internE (.app f' a')
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:778-808 abstractRange — the `lam`
arm. -/
def absRangeArmLam (fuel : Nat) (ty body : EIdx) (m : ConLeche.BinderMeta)
    (d k c : Nat) : AM EIdx := do
  let t ← abstractRange fuel ty d k c
  let b ← abstractRange fuel body d k (c + 1)
  internE (.lam t b m)
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:778-808 abstractRange — the
`forallE` arm. -/
def absRangeArmForallE (fuel : Nat) (ty body : EIdx) (m : ConLeche.BinderMeta)
    (d k c : Nat) : AM EIdx := do
  let t ← abstractRange fuel ty d k c
  let b ← abstractRange fuel body d k (c + 1)
  internE (.forallE t b m)
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:778-808 abstractRange — the
`letE` arm. -/
def absRangeArmLet (fuel : Nat) (ty val body : EIdx) (d k c : Nat) :
    AM EIdx := do
  let t ← abstractRange fuel ty d k c
  let w ← abstractRange fuel val d k c
  let b ← abstractRange fuel body d k (c + 1)
  internE (.letE t w b)
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:778-808 abstractRange — the
`proj` arm. -/
def absRangeArmProj (fuel : Nat) (n : NIdx) (i : Nat) (sub : EIdx)
    (d k c : Nat) : AM EIdx := do
  let u ← abstractRange fuel sub d k c
  internE (.proj n i u)
termination_by (fuel, 1)

end

/-- con-leche: none — `abstractRange`'s clause at fuel `0` (template rule
9). -/
theorem abstractRange_zero (h : EIdx) (d k c : Nat) :
    abstractRange 0 h d k c =
      fail (.internal "fuel exhausted: abstractRange") := by
  rw [abstractRange]

/-- con-leche: none — `abstractRange`'s clause at `fuel + 1` (template rule
9). -/
theorem abstractRange_succ (fuel : Nat) (h : EIdx) (d k c : Nat) :
    abstractRange (fuel + 1) h d k c = (do
      match ← view h with
      | .bvar _ => pure h
      | .fvar idx _ =>
        if d ≤ idx ∧ idx < d + k then internE (.bvar (c + (d + k - 1 - idx)))
        else pure h
      | .sort _ => pure h
      | .const _ _ => pure h
      | .lit _ => pure h
      | .app f a => absRangeArmApp fuel f a d k c
      | .lam ty body m => absRangeArmLam fuel ty body m d k c
      | .forallE ty body m => absRangeArmForallE fuel ty body m d k c
      | .letE ty val body => absRangeArmLet fuel ty val body d k c
      | .proj n i sub => absRangeArmProj fuel n i sub d k c) := by
  rw [abstractRange]
/-- con-leche: ConLeche/Kernel/ExprOps.lean:810-819 sizeF — full node count,
`fvar` annotations included. -/
def sizeF : Nat → EIdx → AM Nat
  | 0, _ => fail (.internal "fuel exhausted: sizeF")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ | .sort _ | .const _ _ | .lit _ => pure 1
    | .fvar _ ty => do
      let x ← sizeF fuel ty
      pure (x + 1)
    | .app f a => do
      let x ← sizeF fuel f
      let y ← sizeF fuel a
      pure (x + y + 1)
    | .lam ty body _ | .forallE ty body _ => do
      let x ← sizeF fuel ty
      let y ← sizeF fuel body
      pure (x + y + 1)
    | .letE ty val body => do
      let x ← sizeF fuel ty
      let y ← sizeF fuel val
      let z ← sizeF fuel body
      pure (x + y + z + 1)
    | .proj _ _ sub => do
      let x ← sizeF fuel sub
      pure (x + 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:821-833 fvarLeaves — all reachable
`fvar` leaves, hereditarily through their annotations. -/
def fvarLeaves : Nat → EIdx → AM (List (Nat × EIdx))
  | 0, _ => fail (.internal "fuel exhausted: fvarLeaves")
  | fuel + 1, h => do
    match ← view h with
    | .fvar idx ty => do
      let rest ← fvarLeaves fuel ty
      pure ((idx, ty) :: rest)
    | .app f a => do
      let x ← fvarLeaves fuel f
      let y ← fvarLeaves fuel a
      pure (x ++ y)
    | .lam ty b _ | .forallE ty b _ => do
      let x ← fvarLeaves fuel ty
      let y ← fvarLeaves fuel b
      pure (x ++ y)
    | .letE t v b => do
      let x ← fvarLeaves fuel t
      let y ← fvarLeaves fuel v
      let z ← fvarLeaves fuel b
      pure (x ++ y ++ z)
    | .proj _ _ sub => fvarLeaves fuel sub
    | .bvar _ | .sort _ | .const _ _ | .lit _ => pure []

/-- con-leche: ConLeche/Kernel/ExprOps.lean:835-861 wscopedB — the scope
check: every reachable `fvar` index is below `d`, hereditarily through
annotations.  con-leche's `&&` is short-circuiting, and so is the explicit
`if` chain here. -/
def wscopedB : Nat → Nat → EIdx → AM Bool
  | 0, _, _ => fail (.internal "fuel exhausted: wscopedB")
  | fuel + 1, d, h => do
    match ← view h with
    | .fvar idx ty =>
      if idx < d then wscopedB fuel idx ty else pure false
    | .app f a => do
      let x ← wscopedB fuel d f
      if x then wscopedB fuel d a else pure false
    | .lam ty body _ => do
      let x ← wscopedB fuel d ty
      if x then wscopedB fuel d body else pure false
    | .forallE ty body _ => do
      let x ← wscopedB fuel d ty
      if x then wscopedB fuel d body else pure false
    | .letE ty val body => do
      let x ← wscopedB fuel d ty
      if x then
        let y ← wscopedB fuel d val
        if y then wscopedB fuel d body else pure false
      else pure false
    | .proj _ _ sub => wscopedB fuel d sub
    | .bvar _ | .sort _ | .const _ _ | .lit _ => pure true

/-! ## The scope queries, MEMOIZED — `Cached/ExprOpsC.lean:997-1268`

The three walks above (`fvarLeaves`, `wscopedB`, and `Core.lean`'s leaf-subset
test) are `Kernel/ExprOps.lean`'s, and over an arena they are the wrong ones.
con-leche runs them on `Expr` TREES, where a walk is linear in the term; (B)
runs them on a hash-consed DAG, where an unmemoized walk is linear in the
term's *unfolding* — which is what hash-consing exists to avoid.  con-leche's
EXECUTED tier knows this and carries `wscopedBGoC` ("one memoized DAG walk"),
`fvarLeavesGoC` (a `seen` set) and `leavesSubGo` (task #86's leaf guard, which
never builds the fabrication's leaf list at all); task #97d's twin took the
spec tier's and lost all three.  Measured (task #97g): on `core.ndjson`'s
first 27 920 declarations the unmemoized `fabScopeOk` was **43.9 % of the
cycles**, with `fvarLeaves` 2.6 % and `wscopedB` 1.6 % beside it.

Each memo is threaded as an argument-and-result pair rather than put in
`Memos`, which is con-leche's own spelling and the one `Frontend/ProjRec.lean`
already uses for its `seen` set: the tables are per-CALL and two of the three
depend on data that is not in the key (`leavesSubGo`'s base list), so a
state-carried table would need a clear at every entry anyway.

The `fvarB == 0` short-circuit at the head of each is con-leche's, and it is
the RAW packed field: on the saturated branch the field is `satRange ≠ 0`, so
the test simply does not fire and the walk proceeds — no recomputation.

**Where these citations point since con-leche `78ded4b6` (task #97-catchup).**
Upstream's tasks #313–#319 rewrote every traversal memo in its CACHED tier:
one walk became three declarations — `<name>P`, the memo-free plain descent
that is the specification; `enter<X>P`, the child step, which makes the cutoff
and the compound test and reads `withExclusive`; and `<name>XP`, the walk that
carries its own proof over an ADDRESS key.  `wscopedBGoC` is now `wscopedBXP`
and `leavesSubGo` is now `leavesSubXP`, and that is the whole of what this bump
costs these twins: **no arm of any walk below changed**, compared clause for
clause against upstream's new `wscopedBP` / `leavesSubP`.  The cutoff that
upstream moved out into `wscopedBC` / `leavesSubC` is still made at the head of
each recursive call here, exactly as `enterWSP` / `enterLSub` make it, so the
computation is the same one.

**And nothing of #319's `withExclusive` gate is owed to this twin.**  That
idiom is the CACHED tier's: it asks whether an `Expr` node's reference count
is one and skips the memo when it is, because a node with a single parent
cannot be reached twice.  The arena has no reference counts — a term is an
`EIdx` into a per-constructor array, shared by construction — so the question
has no answer here, and the memo policy of DESIGN §8.3 (per-call tables,
handle keys, a cutoff off the derived word) is the arena's own and unchanged.
`crates/con-ron-core`'s `ron::node::is_exclusive` (hole #23, task #98) is the
`Expr`-tier port's answer to the same upstream change; the arena tier has and
needs none. -/

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1029-1088 wscopedBXP — the
memoized scope walk.  `fvar` annotations are descended (at the annotation's
own index, not `d`), so the cached fvar range does not decide it and the memo
key carries `d`. -/
def wscopedBGo : Std.HashMap (EIdx × Nat) Bool → Nat → Nat → EIdx →
    AM (Bool × Std.HashMap (EIdx × Nat) Bool)
  | _, 0, _, _ => fail (.internal "fuel exhausted: wscopedBGo")
  | memo, fuel + 1, d, h => do
    if (fvarOfData (← derivedE h)).toNat == 0 then pure (true, memo)
    else
      match memo[(h, d)]? with
      | some r => pure (r, memo)
      | none => do
        let (r, memo') ←
          match ← view h with
          | .bvar _ | .sort _ | .const _ _ | .lit _ => pure (true, memo)
          | .fvar idx ty =>
            if idx < d then wscopedBGo memo fuel idx ty
            else pure (false, memo)
          | .app f a => do
            let (rf, memo) ← wscopedBGo memo fuel d f
            if rf then wscopedBGo memo fuel d a else pure (false, memo)
          | .lam ty body _ => do
            let (rt, memo) ← wscopedBGo memo fuel d ty
            if rt then wscopedBGo memo fuel d body else pure (false, memo)
          | .forallE ty body _ => do
            let (rt, memo) ← wscopedBGo memo fuel d ty
            if rt then wscopedBGo memo fuel d body else pure (false, memo)
          | .letE ty val body => do
            let (rt, memo) ← wscopedBGo memo fuel d ty
            if rt then do
              let (rv, memo) ← wscopedBGo memo fuel d val
              if rv then wscopedBGo memo fuel d body else pure (false, memo)
            else pure (false, memo)
          | .proj _ _ sub => wscopedBGo memo fuel d sub
        pure (r, memo'.insert (h, d) r)

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1090-1095 wscopedBC — the executed
`wscopedB`: one memoized DAG walk from the empty memo. -/
def wscopedBFast (fuel d : Nat) (h : EIdx) : AM Bool := do
  let p ← wscopedBGo ∅ fuel d h
  pure p.1

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1130-1152 fvarLeavesGoC — the
reachable `fvar` leaves, accumulated with a `seen` set so a shared subterm is
walked once.  The accumulation order is con-leche's (its `acc` is consed on
the way in), and the result is used only as a membership base. -/
def fvarLeavesGo : List (Nat × EIdx) → Std.HashMap EIdx Unit → Nat → EIdx →
    AM (List (Nat × EIdx) × Std.HashMap EIdx Unit)
  | _, _, 0, _ => fail (.internal "fuel exhausted: fvarLeavesGo")
  | acc, seen, fuel + 1, h => do
    if (fvarOfData (← derivedE h)).toNat == 0 then pure (acc, seen)
    else
      match seen[h]? with
      | some _ => pure (acc, seen)
      | none => do
        let seen := seen.insert h ()
        match ← view h with
        | .bvar _ | .sort _ | .const _ _ | .lit _ => pure (acc, seen)
        | .fvar idx ty => fvarLeavesGo ((idx, ty) :: acc) seen fuel ty
        | .app f a => do
          let (acc, seen) ← fvarLeavesGo acc seen fuel f
          fvarLeavesGo acc seen fuel a
        | .lam ty body _ => do
          let (acc, seen) ← fvarLeavesGo acc seen fuel ty
          fvarLeavesGo acc seen fuel body
        | .forallE ty body _ => do
          let (acc, seen) ← fvarLeavesGo acc seen fuel ty
          fvarLeavesGo acc seen fuel body
        | .letE ty val body => do
          let (acc, seen) ← fvarLeavesGo acc seen fuel ty
          let (acc, seen) ← fvarLeavesGo acc seen fuel val
          fvarLeavesGo acc seen fuel body
        | .proj _ _ sub => fvarLeavesGo acc seen fuel sub

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1154-1155 fvarLeavesC — the
executed `fvarLeaves`. -/
def fvarLeavesFast (fuel : Nat) (h : EIdx) : AM (List (Nat × EIdx)) := do
  let p ← fvarLeavesGo [] ∅ fuel h
  pure p.1

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1159-1162 leafMem — is `(idx, ty)`
in the base leaf list?  con-leche compares the annotation with `Expr.beq`;
over handles it is handle equality, which is the same test (`denoteE` is
injective, DESIGN §8.3). -/
def leafMem : List (Nat × EIdx) → Nat → EIdx → Bool
  | [], _, _ => false
  | (i, t) :: rest, idx, ty =>
    (i == idx && t == ty) || leafMem rest idx ty

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1197-1256 leavesSubXP — the
fabrication-side leaf-subset test: every reachable `fvar` leaf of the walked
term is one of `bl`.  Memoized on the node, because `bl` is fixed for the
call. -/
def leavesSubGo : List (Nat × EIdx) → Std.HashMap EIdx Bool → Nat → EIdx →
    AM (Bool × Std.HashMap EIdx Bool)
  | _, _, 0, _ => fail (.internal "fuel exhausted: leavesSubGo")
  | bl, memo, fuel + 1, h => do
    if (fvarOfData (← derivedE h)).toNat == 0 then pure (true, memo)
    else
      match memo[h]? with
      | some r => pure (r, memo)
      | none => do
        let (r, memo') ←
          match ← view h with
          | .bvar _ | .sort _ | .const _ _ | .lit _ => pure (true, memo)
          | .fvar idx ty =>
            if leafMem bl idx ty then leavesSubGo bl memo fuel ty
            else pure (false, memo)
          | .app f a => do
            let (rf, memo) ← leavesSubGo bl memo fuel f
            if rf then leavesSubGo bl memo fuel a else pure (false, memo)
          | .lam ty body _ => do
            let (rt, memo) ← leavesSubGo bl memo fuel ty
            if rt then leavesSubGo bl memo fuel body else pure (false, memo)
          | .forallE ty body _ => do
            let (rt, memo) ← leavesSubGo bl memo fuel ty
            if rt then leavesSubGo bl memo fuel body else pure (false, memo)
          | .letE ty val body => do
            let (rt, memo) ← leavesSubGo bl memo fuel ty
            if rt then do
              let (rv, memo) ← leavesSubGo bl memo fuel val
              if rv then leavesSubGo bl memo fuel body else pure (false, memo)
            else pure (false, memo)
          | .proj _ _ sub => leavesSubGo bl memo fuel sub
        pure (r, memo'.insert h r)

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1264-1268 leafGuard — **the
fabrication leaf guard**: every `fvar` leaf of `fab` is a leaf of `base`.
Short-circuits on an `fvar`-free fabrication off the packed range, and
otherwise walks `fab` ONCE against `base`'s leaf list — never building
`fab`'s own list, and never running `Core.lean`'s quadratic
`fvarLeavesSubset`. -/
def leafGuard (fuel : Nat) (fab base : EIdx) : AM Bool := do
  if (fvarOfData (← derivedE fab)).toNat == 0 then pure true
  else do
    let bl ← fvarLeavesFast fuel base
    let p ← leavesSubGo bl ∅ fuel fab
    pure p.1

/-- con-leche: ConLeche/Kernel/ExprOps.lean:863-877 looseBVarsBounded — the
pure walk.  It is the SPECIFICATION; what executes is the `O(1)` field read
`looseBVarsBoundedFast` below, exactly as in con-leche (the `@[csimp]`
pair). -/
def looseBVarsBounded : Nat → Nat → EIdx → AM Bool
  | 0, _, _ => fail (.internal "fuel exhausted: looseBVarsBounded")
  | fuel + 1, k, h => do
    match ← view h with
    | .bvar i => pure (i < k)
    | .fvar _ _ => pure true
    | .sort _ | .const _ _ | .lit _ => pure true
    | .app f a => do
      let x ← looseBVarsBounded fuel k f
      if x then looseBVarsBounded fuel k a else pure false
    | .lam ty body _ | .forallE ty body _ => do
      let x ← looseBVarsBounded fuel k ty
      if x then looseBVarsBounded fuel (k + 1) body else pure false
    | .letE ty val body => do
      let x ← looseBVarsBounded fuel k ty
      if x then
        let y ← looseBVarsBounded fuel k val
        if y then looseBVarsBounded fuel (k + 1) body else pure false
      else pure false
    | .proj _ _ sub => looseBVarsBounded fuel k sub

/-! ## The one-node readers

Each is a single `view` and a test: no recursion, no fuel. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:879-885 isLam — is the expression
a λ? -/
def isLam (h : EIdx) : AM Bool := do
  match ← view h with
  | .lam _ _ _ => pure true
  | _ => pure false

/-- con-leche: ConLeche/Kernel/ExprOps.lean:887-894 lamPw — a λ node's
prop-ness annotation, `none` off λs.  `PropWhen` is a value and not a term,
so it crosses the signature unchanged. -/
def lamPw (h : EIdx) : AM (Option PropWhen) := do
  match ← view h with
  | .lam _ _ m => pure (some m.pw)
  | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:896-902 forallPw — the ∀ twin of
`lamPw`. -/
def forallPw (h : EIdx) : AM (Option PropWhen) := do
  match ← view h with
  | .forallE _ _ m => pure (some m.pw)
  | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:904-913 hasFvar — the pure walk;
what executes is `hasFvarFast` below (the fvar-range field read). -/
def hasFvar : Nat → EIdx → AM Bool
  | 0, _ => fail (.internal "fuel exhausted: hasFvar")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ | .sort _ | .const _ _ | .lit _ => pure false
    | .fvar _ _ => pure true
    | .app f a => do
      let x ← hasFvar fuel f
      if x then pure true else hasFvar fuel a
    | .lam ty body _ | .forallE ty body _ => do
      let x ← hasFvar fuel ty
      if x then pure true else hasFvar fuel body
    | .letE ty val body => do
      let x ← hasFvar fuel ty
      if x then pure true else do
        let y ← hasFvar fuel val
        if y then pure true else hasFvar fuel body
    | .proj _ _ sub => hasFvar fuel sub

/-! ## Application spines -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:915-918 getAppFn — the head of an
application spine. -/
def getAppFn : Nat → EIdx → AM EIdx
  | 0, _ => fail (.internal "fuel exhausted: getAppFn")
  | fuel + 1, h => do
    if h.tag == ETag.app then
      match ← viewApp h with
      | none => failDanglingE
      | some (f, _) => getAppFn fuel f
    else pure h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:920-923 getAppArgs — the arguments
of an application spine, outermost last. -/
def getAppArgs : Nat → EIdx → AM (List EIdx)
  | 0, _ => fail (.internal "fuel exhausted: getAppArgs")
  | fuel + 1, h => do
    if h.tag == ETag.app then
      match ← viewApp h with
      | none => failDanglingE
      | some (f, a) => do
        let as ← getAppArgs fuel f
        pure (as ++ [a])
    else pure []

/-- con-leche: ConLeche/Kernel/ExprOps.lean:925-928 mkAppN — apply to a list
of arguments.  Structural on the list, so no fuel. -/
def mkAppN (f : EIdx) : List EIdx → AM EIdx
  | [] => pure f
  | a :: as => do
    let g ← internE (.app f a)
    mkAppN g as

/-- con-leche: ConLeche/Kernel/ExprOps.lean:925-928 mkAppN — apply to the
entries of a push-order array from `i` on, which is what the batched β and the
spine walks hold.  §3.4's standing `List`-as-cursor deviation, at an
`Array`. -/
def mkAppNFrom (f : EIdx) (args : Array EIdx) (i : Nat) : AM EIdx := do
  if h : i < args.size then do
    let g ← internAppE f args[i]
    mkAppNFrom g args (i + 1)
  else pure f
termination_by args.size - i
decreasing_by omega

/-! ## `renameConsts` — `ExprOps.lean:930-956`, `:999-1036`, `:1109-1111`

The renaming is a function on NAME HANDLES, not on names: the census's
mechanical column says so, and it is what the call site (the modeled-block
contract, which compares a block's types against their `_model` counterparts)
can supply.  It is the module's one higher-order argument, and it is
con-leche's own (`renameConsts (f : Name → Name)`); what the Rust passes
there is P2d's to decide. -/

mutual

/-- con-leche: ConLeche/Kernel/ExprOps.lean:930-956 renameConsts
con-leche: ConLeche/Kernel/ExprOps.lean:1001-1038 renameConstsGo
Rename constants throughout; levels, binders and `proj` struct names
untouched (task #175 wiring W5).  The `const` arm is a leaf here as it is in
con-leche — it rebuilds one node and does not recurse — so it is not
memoized, and it stays in the dispatcher with the three other leaves.  The
memoized arms are split per DESIGN §8.6's ruling of 2026-09-22. -/
def renameConstsGo (f : NIdx → NIdx) (fuel : Nat) (h : EIdx) : AM EIdx :=
  match fuel with
  | 0 => fail (.internal "fuel exhausted: renameConsts")
  | fuel + 1 => do
    match ← view h with
    | .bvar _ => pure h
    | .sort _ => pure h
    | .lit _ => pure h
    | .const n us => do
      let n' := f n
      internRebuiltConst h (n' == n) n' us
    | .fvar i ty => renameArmFVar f fuel h i ty
    | .app a b => renameArmApp f fuel h a b
    | .lam ty body m => renameArmLam f fuel h ty body m
    | .forallE ty body m => renameArmForallE f fuel h ty body m
    | .letE ty val body => renameArmLet f fuel h ty val body
    | .proj n i sub => renameArmProj f fuel h n i sub
termination_by (fuel, 0)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1001-1038 renameConstsGo — the
`fvar` arm. -/
def renameArmFVar (f : NIdx → NIdx) (fuel : Nat) (h : EIdx) (i : Nat)
    (ty : EIdx) : AM EIdx := do
  match ← renameGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← renameConstsGo f fuel ty
    let r ← internRebuiltFVar h (t == ty) i t
    renameSet (h, 0) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1001-1038 renameConstsGo — the
`app` arm. -/
def renameArmApp (f : NIdx → NIdx) (fuel : Nat) (h : EIdx) (a b : EIdx) :
    AM EIdx := do
  match ← renameGet (h, 0) with
  | some r => pure r
  | none => do
    let a' ← renameConstsGo f fuel a
    let b' ← renameConstsGo f fuel b
    let r ← internRebuiltApp h (a' == a && b' == b) a' b'
    renameSet (h, 0) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1001-1038 renameConstsGo — the
`lam` arm. -/
def renameArmLam (f : NIdx → NIdx) (fuel : Nat) (h : EIdx) (ty body : EIdx)
    (m : ConLeche.BinderMeta) : AM EIdx := do
  match ← renameGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← renameConstsGo f fuel ty
    let b ← renameConstsGo f fuel body
    let r ← internRebuiltLam h (t == ty && b == body) t b m
    renameSet (h, 0) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1001-1038 renameConstsGo — the
`forallE` arm. -/
def renameArmForallE (f : NIdx → NIdx) (fuel : Nat) (h : EIdx)
    (ty body : EIdx) (m : ConLeche.BinderMeta) : AM EIdx := do
  match ← renameGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← renameConstsGo f fuel ty
    let b ← renameConstsGo f fuel body
    let r ← internRebuiltForallE h (t == ty && b == body) t b m
    renameSet (h, 0) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1001-1038 renameConstsGo — the
`letE` arm. -/
def renameArmLet (f : NIdx → NIdx) (fuel : Nat) (h : EIdx)
    (ty val body : EIdx) : AM EIdx := do
  match ← renameGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← renameConstsGo f fuel ty
    let w ← renameConstsGo f fuel val
    let b ← renameConstsGo f fuel body
    let r ← internRebuiltLetE h (t == ty && w == val && b == body) t w b
    renameSet (h, 0) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1001-1038 renameConstsGo — the
`proj` arm. -/
def renameArmProj (f : NIdx → NIdx) (fuel : Nat) (h : EIdx) (n : NIdx)
    (i : Nat) (sub : EIdx) : AM EIdx := do
  match ← renameGet (h, 0) with
  | some r => pure r
  | none => do
    let u ← renameConstsGo f fuel sub
    let r ← internRebuiltProj h (u == sub) n i u
    renameSet (h, 0) r
    pure r
termination_by (fuel, 1)

end

/-- con-leche: none — `renameConstsGo`'s clause at fuel `0` (template rule
9). -/
theorem renameConstsGo_zero (f : NIdx → NIdx) (h : EIdx) :
    renameConstsGo f 0 h = fail (.internal "fuel exhausted: renameConsts") := by
  rw [renameConstsGo]

/-- con-leche: none — `renameConstsGo`'s clause at `fuel + 1` (template rule
9). -/
theorem renameConstsGo_succ (f : NIdx → NIdx) (fuel : Nat) (h : EIdx) :
    renameConstsGo f (fuel + 1) h = (do
      match ← view h with
      | .bvar _ => pure h
      | .sort _ => pure h
      | .lit _ => pure h
      | .const n us => do
        let n' := f n
        internRebuiltConst h (n' == n) n' us
      | .fvar i ty => renameArmFVar f fuel h i ty
      | .app a b => renameArmApp f fuel h a b
      | .lam ty body m => renameArmLam f fuel h ty body m
      | .forallE ty body m => renameArmForallE f fuel h ty body m
      | .letE ty val body => renameArmLet f fuel h ty val body
      | .proj n i sub => renameArmProj f fuel h n i sub) := by
  rw [renameConstsGo]
/-- con-leche: ConLeche/Kernel/ExprOps.lean:1111-1113 renameConstsFast — the
top-level entry. -/
def renameConstsFast (fuel : Nat) (f : NIdx → NIdx) (e : EIdx) : AM EIdx := do
  renameClear
  let r ← renameConstsGo f fuel e
  renameClear
  pure r

/-! ## Telescopes -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1120-1126 stripLams — strip `k`
leading λs.  The recursion is structural on `k`, so no fuel. -/
def stripLams : Nat → EIdx → AM (Option (List (EIdx × BinderMeta) × EIdx))
  | 0, h => pure (some ([], h))
  | k + 1, h => do
    match ← view h with
    | .lam ty b m => do
      match ← stripLams k b with
      | some p => pure (some ((ty, m) :: p.1, p.2))
      | none => pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1128-1134 stripPis — strip `k`
leading `∀`s. -/
def stripPis : Nat → EIdx → AM (Option (List (EIdx × BinderMeta) × EIdx))
  | 0, h => pure (some ([], h))
  | k + 1, h => do
    match ← view h with
    | .forallE ty b m => do
      match ← stripPis k b with
      | some p => pure (some ((ty, m) :: p.1, p.2))
      | none => pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1136-1140 piResult — the body of a
syntactic `∀`-telescope. -/
def piResult : Nat → EIdx → AM EIdx
  | 0, _ => fail (.internal "fuel exhausted: piResult")
  | fuel + 1, h => do
    match ← view h with
    | .forallE _ b _ => piResult fuel b
    | _ => pure h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1142-1146 instPis — instantiate a
`∀`-telescope with arguments, in order.  Structural on the argument list; the
fuel is the one `instantiate1Fast` needs. -/
def instPis (fuel : Nat) : EIdx → List EIdx → AM (Option EIdx)
  | e, [] => pure (some e)
  | h, a :: as => do
    match ← view h with
    | .forallE _ body _ => do
      let b ← instantiate1Fast fuel body a 0
      instPis fuel b as
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1148-1156 instPisAt — instantiate
the leading `∀`-binders at the given arguments, returning each binder's
domain with the fully instantiated residual.  con-leche's `Option.map` over a
pure body becomes an explicit `match`: the body is monadic here. -/
def instPisAt (fuel : Nat) : List EIdx → EIdx → AM (Option (List EIdx × EIdx))
  | [], e => pure (some ([], e))
  | a :: as, h => do
    match ← view h with
    | .forallE dom body _ => do
      let b ← instantiate1Fast fuel body a 0
      match ← instPisAt fuel as b with
      | some p => pure (some (dom :: p.1, p.2))
      | none => pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1158-1164 instLamsAt — `instPisAt`
for λ-binders. -/
def instLamsAt (fuel : Nat) : List EIdx → EIdx → AM (Option (List EIdx × EIdx))
  | [], e => pure (some ([], e))
  | a :: as, h => do
    match ← view h with
    | .lam dom body _ => do
      let b ← instantiate1Fast fuel body a 0
      match ← instLamsAt fuel as b with
      | some p => pure (some (dom :: p.1, p.2))
      | none => pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1181-1190 instPisAtFGo — the core
of `instPisAtF`: `acc` holds the pending substitutions, innermost binder
first. -/
def instPisAtFGo (fuel : Nat) :
    Array EIdx → List EIdx → EIdx → AM (Option (List EIdx × EIdx))
  | acc, [], e => do
    let r ← instantiateListFast fuel e acc 0
    pure (some ([], r))
  | acc, a :: as, h => do
    match ← view h with
    | .forallE dom body _ => do
      match ← instPisAtFGo fuel (acc.push a) as body with
      | some p => do
        let d ← instantiateListFast fuel dom acc 0
        pure (some (d :: p.1, p.2))
      | none => pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1192-1196 instPisAtF — one-pass
`instPisAt`. -/
def instPisAtF (fuel : Nat) (args : List EIdx) (e : EIdx) :
    AM (Option (List EIdx × EIdx)) := do
  match ← instPisAtFGo fuel #[] args e with
  | some r => pure (some r)
  | none => instPisAt fuel args e

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1198-1204 instLamsAtFGo — the λ
counterpart of `instPisAtFGo`. -/
def instLamsAtFGo (fuel : Nat) :
    Array EIdx → List EIdx → EIdx → AM (Option (List EIdx × EIdx))
  | acc, [], e => do
    let r ← instantiateListFast fuel e acc 0
    pure (some ([], r))
  | acc, a :: as, h => do
    match ← view h with
    | .lam dom body _ => do
      match ← instLamsAtFGo fuel (acc.push a) as body with
      | some p => do
        let d ← instantiateListFast fuel dom acc 0
        pure (some (d :: p.1, p.2))
      | none => pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1206-1210 instLamsAtF — one-pass
`instLamsAt`. -/
def instLamsAtF (fuel : Nat) (args : List EIdx) (e : EIdx) :
    AM (Option (List EIdx × EIdx)) := do
  match ← instLamsAtFGo fuel #[] args e with
  | some r => pure (some r)
  | none => instLamsAt fuel args e

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1212-1217 fvarTypeD — the type
annotation of a free-variable leaf (the expression itself otherwise). -/
def fvarTypeD (h : EIdx) : AM EIdx := do
  match ← view h with
  | .fvar _ ty => pure ty
  | _ => pure h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1219-1227 instSpine — instantiate
a telescope-context expression at an argument spine. -/
def instSpine (fuel : Nat) : List EIdx → Nat → EIdx → AM EIdx
  | [], _, e => pure e
  | a :: as, t, e => do
    let e' ← instantiate1Fast fuel e a t
    instSpine fuel as (t - 1) e'

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1229-1244 recRulePlain — the
comparand `(List.range cnP).map (fun k => Expr.bvar (mI - 1 - k))`, interned.
Structural on the count, so no fuel. -/
def bvarRange (mI : Nat) : Nat → Nat → AM (List EIdx)
  | 0, _ => pure []
  | n + 1, k => do
    let b ← internE (.bvar (mI - 1 - k))
    let rest ← bvarRange mI n (k + 1)
    pure (b :: rest)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1229-1244 recRulePlain — a
recursor rule is canonical when its constructor's parameters are exactly the
recursor's own leading arguments.  The `==` on the argument prefix is index
equality (the `==` inventory's line 1240): exactness makes it the structural
comparison con-leche writes. -/
def recRulePlain (fuel : Nat) (recTy : EIdx) (mI rP cnP : Nat) : AM Bool := do
  if !(decide (cnP ≤ rP) && decide (rP ≤ mI)) then
    pure false
  else
    match ← stripPis mI recTy with
    | some p => do
      match ← view p.2 with
      | .forallE dom _ _ => do
        let args ← getAppArgs fuel dom
        let want ← bvarRange mI cnP 0
        pure (args.take cnP == want)
      | _ => pure false
    | none => pure false

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1246-1261 pisToLams — convert the
first `k` `∀`-binders into λ-binders over a body; the copied binder metadata
keeps only the display info, so the result carries the parse placeholder and
every consumer must annotate it. -/
def pisToLams : Nat → EIdx → EIdx → AM (Option EIdx)
  | 0, _, body => pure (some body)
  | k + 1, h, body => do
    match ← view h with
    | .forallE ty rest _ => do
      match ← pisToLams k rest body with
      | some b => do
        let r ← internE (.lam ty b ⟨.never⟩)
        pure (some r)
      | none => pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1263-1269 replacePiBody — replace
the body under the first `k` `∀`-binders, domains and prop-ness data kept. -/
def replacePiBody : Nat → EIdx → EIdx → AM (Option EIdx)
  | 0, _, b => pure (some b)
  | k + 1, h, b => do
    match ← view h with
    | .forallE ty rest m => do
      match ← replacePiBody k rest b with
      | some r => do
        let x ← internE (.forallE ty r ⟨m.pw⟩)
        pure (some x)
      | none => pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1271-1274 piArity — the length of
the leading `∀`-telescope. -/
def piArity : Nat → EIdx → AM Nat
  | 0, _ => fail (.internal "fuel exhausted: piArity")
  | fuel + 1, h => do
    match ← view h with
    | .forallE _ b _ => do
      let n ← piArity fuel b
      pure (n + 1)
    | _ => pure 0

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1276-1280 resultSort — the result
sort at the end of a `∀`-telescope. -/
def resultSort : Nat → EIdx → AM (Option LIdx)
  | 0, _ => fail (.internal "fuel exhausted: resultSort")
  | fuel + 1, h => do
    match ← view h with
    | .forallE _ b _ => resultSort fuel b
    | .sort u => pure (some u)
    | _ => pure none

/-! ## The packed range fields and their saturated-branch recomputations

`ExprOps.lean:1293-1303`, `:1312-1323`, `:1368-1425`, `:1427-1439`.  The
arena reads both ranges in `O(1)` off the derived column; only on the
saturated branch (a bound at or above `satRange = 32767`) does it walk, and
that walk is memoized exactly as con-leche's is. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1295-1305 Expr.bvarBound
con-leche: ConLeche/Kernel/ExprOps.lean:1370-1394 bvarBoundGo
The memoized exact loose-bvar bound.  con-leche's `bvarBound` is the pure
specification and `bvarBoundGo` the memoized walk; the arena has one
function.  The memo is probed for every node, leaves included, as con-leche
probes it. -/
def bvarBoundGo : Nat → EIdx → AM Nat
  | 0, _ => fail (.internal "fuel exhausted: bvarBound")
  | fuel + 1, h => do
    match ← bvarBGet h with
    | some r => pure r
    | none => do
      let r ← (do
        match ← view h with
        | .bvar i => pure (i + 1)
        | .fvar _ _ | .sort _ | .const _ _ | .lit _ => pure 0
        | .app f a => do
          let x ← bvarBoundGo fuel f
          let y ← bvarBoundGo fuel a
          pure (max x y)
        | .lam ty body _ | .forallE ty body _ => do
          let x ← bvarBoundGo fuel ty
          let y ← bvarBoundGo fuel body
          pure (max x (y - 1))
        | .letE ty val body => do
          let x ← bvarBoundGo fuel ty
          let y ← bvarBoundGo fuel val
          let z ← bvarBoundGo fuel body
          pure (max (max x y) (z - 1))
        | .proj _ _ sub => bvarBoundGo fuel sub)
      bvarBSet h r
      pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1396-1397 bvarBoundMemo — the
top-level entry of the memoized walk. -/
def bvarBoundMemo (fuel : Nat) (e : EIdx) : AM Nat := do
  bvarBClear
  let r ← bvarBoundGo fuel e
  bvarBClear
  pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1314-1325 Expr.fvarRange
con-leche: ConLeche/Kernel/ExprOps.lean:1399-1424 fvarRangeGo
The memoized exact fvar range (`fvar` annotations are not descended into,
matching the abstraction traversals). -/
def fvarRangeGo : Nat → EIdx → AM Nat
  | 0, _ => fail (.internal "fuel exhausted: fvarRange")
  | fuel + 1, h => do
    match ← fvarBGet h with
    | some r => pure r
    | none => do
      let r ← (do
        match ← view h with
        | .fvar idx _ => pure (idx + 1)
        | .bvar _ | .sort _ | .const _ _ | .lit _ => pure 0
        | .app f a => do
          let x ← fvarRangeGo fuel f
          let y ← fvarRangeGo fuel a
          pure (max x y)
        | .lam ty body _ | .forallE ty body _ => do
          let x ← fvarRangeGo fuel ty
          let y ← fvarRangeGo fuel body
          pure (max x y)
        | .letE ty val body => do
          let x ← fvarRangeGo fuel ty
          let y ← fvarRangeGo fuel val
          let z ← fvarRangeGo fuel body
          pure (max (max x y) z)
        | .proj _ _ sub => fvarRangeGo fuel sub)
      fvarBSet h r
      pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1426-1427 fvarRangeMemo — the
top-level entry of the memoized walk. -/
def fvarRangeMemo (fuel : Nat) (e : EIdx) : AM Nat := do
  fvarBClear
  let r ← fvarRangeGo fuel e
  fvarBClear
  pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1429-1434 bvarB — **the
loose-bvar bound the checker reads**: the packed field, or — on the saturated
branch alone — the exact memoized recomputation.  `==` on `Nat`, so the `==`
inventory's line 1432 is not a handle comparison. -/
def bvarB (fuel : Nat) (e : EIdx) : AM Nat := do
  let der ← derivedE e
  let r := (bvarOfData der).toNat
  if r == satRange then bvarBoundMemo fuel e else pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1436-1441 fvarB — **the fvar range
the checker reads**: the packed field, or the exact memoized recomputation on
the saturated branch. -/
def fvarB (fuel : Nat) (e : EIdx) : AM Nat := do
  let der ← derivedE e
  let r := (fvarOfData der).toNat
  if r == satRange then fvarRangeMemo fuel e else pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1709-1710 hasFvarFast — the
executed `hasFvar`: the fvar-range field read. -/
def hasFvarFast (fuel : Nat) (e : EIdx) : AM Bool := do
  let r ← fvarB fuel e
  pure (r != 0)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1718-1719 looseBVarsBoundedFast —
the executed `looseBVarsBounded`: the loose-bvar field read. -/
def looseBVarsBoundedFast (fuel k : Nat) (e : EIdx) : AM Bool := do
  let r ← bvarB fuel e
  pure (decide (r ≤ k))

/-! ## `abstract1` — `ExprOps.lean:760-776`, `:1789-1833`, `:1927-1929`

The fvar-range cutoff comes first: a node whose whole subtree mentions no
`fvar` at or above `d` is its own abstraction. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the
`fvar` arm.  It does not recurse, so it sits outside the `mutual` block. -/
def abstract1ArmFVar (d : Nat) (h : EIdx) (k : Nat) : AM EIdx := do
  match ← viewFVarIdx h with
  | none => failDanglingE
  | some idx => if idx = d then internBVarE k else pure h

mutual

/-- con-leche: ConLeche/Kernel/ExprOps.lean:760-776 abstract1
con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go
Close a binder body: replace `fvar d …` leaves by `bvar k`, bumping `k` under
binders.  `fvar` annotations are not descended into.  The dispatcher (arms
split per DESIGN §8.6's ruling of 2026-09-22). -/
def abstract1Go (d : Nat) (fuel : Nat) (h : EIdx) (k : Nat) : AM EIdx :=
  match fuel with
  | 0 => fail (.internal "fuel exhausted: abstract1")
  | fuel + 1 => do
    let fb ← fvarB fuel h
    if fb ≤ d then
      pure h
    else
      let tg := h.tag
      if tg == ETag.app then abstract1ArmApp d fuel h k
      else if ETag.isBind tg then abstract1ArmBind d fuel h k
      else if tg == ETag.fvar then abstract1ArmFVar d h k
      else if tg == ETag.letE then abstract1ArmLet d fuel h k
      else if tg == ETag.proj then abstract1ArmProj d fuel h k
      else pure h
termination_by (fuel, 0)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the `app`
arm. -/
def abstract1ArmApp (d : Nat) (fuel : Nat) (h : EIdx) (k : Nat) : AM EIdx := do
  match ← abs1Get (h, k) with
  | some r => pure r
  | none =>
    match ← viewApp h with
    | none => failDanglingE
    | some (f, a) => do
      let f' ← abstract1Go d fuel f k
      let a' ← abstract1Go d fuel a k
      let r ← internRebuiltApp h (f' == f && a' == a) f' a'
      abs1Set (h, k) r
      pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the
binder arm; the body descends at `k + 1`. -/
def abstract1ArmBind (d : Nat) (fuel : Nat) (h : EIdx) (k : Nat) :
    AM EIdx := do
  match ← abs1Get (h, k) with
  | some r => pure r
  | none =>
    match ← viewBindI h with
    | none => failDanglingE
    | some (ty, body, m) => do
      let t ← abstract1Go d fuel ty k
      let b ← abstract1Go d fuel body (k + 1)
      let r ← internRebuiltBindI h (t == ty && b == body) h.tag t b m
      abs1Set (h, k) r
      pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the
`letE` arm. -/
def abstract1ArmLet (d : Nat) (fuel : Nat) (h : EIdx) (k : Nat) : AM EIdx := do
  match ← abs1Get (h, k) with
  | some r => pure r
  | none =>
    match ← viewLet h with
    | none => failDanglingE
    | some (ty, val, body) => do
      let t ← abstract1Go d fuel ty k
      let w ← abstract1Go d fuel val k
      let b ← abstract1Go d fuel body (k + 1)
      let r ← internRebuiltLetE h (t == ty && w == val && b == body) t w b
      abs1Set (h, k) r
      pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the
`proj` arm. -/
def abstract1ArmProj (d : Nat) (fuel : Nat) (h : EIdx) (k : Nat) :
    AM EIdx := do
  match ← abs1Get (h, k) with
  | some r => pure r
  | none =>
    match ← viewProj h with
    | none => failDanglingE
    | some (n, i, sub) => do
      let u ← abstract1Go d fuel sub k
      let r ← internRebuiltProj h (u == sub) n i u
      abs1Set (h, k) r
      pure r
termination_by (fuel, 1)

end

/-- con-leche: none — `abstract1Go`'s clause at fuel `0` (template rule 9). -/
theorem abstract1Go_zero (d : Nat) (h : EIdx) (k : Nat) :
    abstract1Go d 0 h k = fail (.internal "fuel exhausted: abstract1") := by
  rw [abstract1Go]

/-- con-leche: none — `abstract1Go`'s clause at `fuel + 1` (template rule
9). -/
theorem abstract1Go_succ (d : Nat) (fuel : Nat) (h : EIdx) (k : Nat) :
    abstract1Go d (fuel + 1) h k = (do
      let fb ← fvarB fuel h
      if fb ≤ d then
        pure h
      else
        let tg := h.tag
        if tg == ETag.app then abstract1ArmApp d fuel h k
        else if ETag.isBind tg then abstract1ArmBind d fuel h k
        else if tg == ETag.fvar then abstract1ArmFVar d h k
        else if tg == ETag.letE then abstract1ArmLet d fuel h k
        else if tg == ETag.proj then abstract1ArmProj d fuel h k
        else pure h) := by
  rw [abstract1Go]
/-- con-leche: ConLeche/Kernel/ExprOps.lean:1929-1931 abstract1Fast — the
top-level entry. -/
def abstract1Fast (fuel : Nat) (e : EIdx) (d : Nat) (k : Nat := 0) : AM EIdx := do
  abs1Clear
  let r ← abstract1Go d fuel e k
  abs1Clear
  pure r

/-! ## `abstractRange`, the EXECUTED form — `Cached/ExprOpsC.lean:684-755`

`abstractRange` above (in "The measures and the scope predicates") is
con-leche's `Kernel/ExprOps.lean:791` SPEC: a bare structural descent.  The
cached tier's `abstractRangeC` is the one the checker runs, and it is the same
three devices `abstract1Go` already has — the `fvarB ≤ d` cutoff at the node
(`abstractRangeP`'s first line, `enterAbsRP`), the per-call memo keyed by
`(node, cursor)` (`abstractRangeXP`'s `MemoXP`), and the `k = 0` identity that
skips the traversal outright (`abstractRangeC`'s own first clause).

Task #97-P6-11 is what needed it: the annotation's binder-telescope loop calls
`abstractRange` once per binder domain and once at the leaf, so the bare
descent became the hottest walk of the run.

The memo table is `abstract1`'s (`abs1C`).  The two walks never nest — both are
leaf walks over the store, calling nothing but `fvarB`, `view` and `intern` —
and each entry point clears the table before and after itself, so within one
call the key `(h, c)` determines the result at the call's own fixed `d` and
`k`.  That is a table IDENTITY, not a clause. -/

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:715-746 abstractRangeXP — the
`fvar` arm, which does not recurse and so sits outside the `mutual` block. -/
def absRangeArmFVar (d k : Nat) (h : EIdx) (c : Nat) : AM EIdx := do
  match ← viewFVarIdx h with
  | none => failDanglingE
  | some idx =>
    if d ≤ idx && idx < d + k then internBVarE (c + (d + k - 1 - idx))
    else pure h

mutual

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:684-700 abstractRangeP
con-leche: ConLeche/Cached/ExprOpsC.lean:715-746 abstractRangeXP
The memoized `abstractRange` walk: close the `k` free variables
`d … d + k - 1` into `bvar`s at cursor `c`, innermost binder to the lowest
index.  The dispatcher (arms split per DESIGN §8.6's ruling of
2026-09-22). -/
def abstractRangeGo (d k : Nat) (fuel : Nat) (h : EIdx) (c : Nat) : AM EIdx :=
  match fuel with
  | 0 => fail (.internal "fuel exhausted: abstractRange")
  | fuel + 1 => do
    let fb ← fvarB fuel h
    if fb ≤ d then
      pure h
    else
      let tg := h.tag
      if tg == ETag.app then absRangeGoArmApp d k fuel h c
      else if ETag.isBind tg then absRangeGoArmBind d k fuel h c
      else if tg == ETag.fvar then absRangeArmFVar d k h c
      else if tg == ETag.letE then absRangeGoArmLet d k fuel h c
      else if tg == ETag.proj then absRangeGoArmProj d k fuel h c
      else pure h
termination_by (fuel, 0)

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:715-746 abstractRangeXP — the
`app` arm. -/
def absRangeGoArmApp (d k : Nat) (fuel : Nat) (h : EIdx) (c : Nat) :
    AM EIdx := do
  match ← abs1Get (h, c) with
  | some r => pure r
  | none =>
    match ← viewApp h with
    | none => failDanglingE
    | some (f, a) => do
      let f' ← abstractRangeGo d k fuel f c
      let a' ← abstractRangeGo d k fuel a c
      let r ← internRebuiltApp h (f' == f && a' == a) f' a'
      abs1Set (h, c) r
      pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:715-746 abstractRangeXP — the
binder arm; the body descends at `c + 1`. -/
def absRangeGoArmBind (d k : Nat) (fuel : Nat) (h : EIdx) (c : Nat) :
    AM EIdx := do
  match ← abs1Get (h, c) with
  | some r => pure r
  | none =>
    match ← viewBindI h with
    | none => failDanglingE
    | some (ty, body, m) => do
      let t ← abstractRangeGo d k fuel ty c
      let b ← abstractRangeGo d k fuel body (c + 1)
      let r ← internRebuiltBindI h (t == ty && b == body) h.tag t b m
      abs1Set (h, c) r
      pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:715-746 abstractRangeXP — the
`letE` arm. -/
def absRangeGoArmLet (d k : Nat) (fuel : Nat) (h : EIdx) (c : Nat) :
    AM EIdx := do
  match ← abs1Get (h, c) with
  | some r => pure r
  | none =>
    match ← viewLet h with
    | none => failDanglingE
    | some (ty, val, body) => do
      let t ← abstractRangeGo d k fuel ty c
      let w ← abstractRangeGo d k fuel val c
      let b ← abstractRangeGo d k fuel body (c + 1)
      let r ← internRebuiltLetE h (t == ty && w == val && b == body) t w b
      abs1Set (h, c) r
      pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:715-746 abstractRangeXP — the
`proj` arm. -/
def absRangeGoArmProj (d k : Nat) (fuel : Nat) (h : EIdx) (c : Nat) :
    AM EIdx := do
  match ← abs1Get (h, c) with
  | some r => pure r
  | none =>
    match ← viewProj h with
    | none => failDanglingE
    | some (n, i, sub) => do
      let u ← abstractRangeGo d k fuel sub c
      let r ← internRebuiltProj h (u == sub) n i u
      abs1Set (h, c) r
      pure r
termination_by (fuel, 1)

end

/-- con-leche: none — `abstractRangeGo`'s clause at fuel `0` (template rule
9). -/
theorem abstractRangeGo_zero (d k : Nat) (h : EIdx) (c : Nat) :
    abstractRangeGo d k 0 h c =
      fail (.internal "fuel exhausted: abstractRange") := by
  rw [abstractRangeGo]

/-- con-leche: none — `abstractRangeGo`'s clause at `fuel + 1` (template rule
9). -/
theorem abstractRangeGo_succ (d k : Nat) (fuel : Nat) (h : EIdx) (c : Nat) :
    abstractRangeGo d k (fuel + 1) h c = (do
      let fb ← fvarB fuel h
      if fb ≤ d then
        pure h
      else
        let tg := h.tag
        if tg == ETag.app then absRangeGoArmApp d k fuel h c
        else if ETag.isBind tg then absRangeGoArmBind d k fuel h c
        else if tg == ETag.fvar then absRangeArmFVar d k h c
        else if tg == ETag.letE then absRangeGoArmLet d k fuel h c
        else if tg == ETag.proj then absRangeGoArmProj d k fuel h c
        else pure h) := by
  rw [abstractRangeGo]
/-- con-leche: ConLeche/Cached/ExprOpsC.lean:748-755 abstractRangeC — the
top-level entry of the executed `abstractRange`: `k = 0` is the identity and
skips the traversal (con-leche's own clause, and what makes the annotation
telescope's OUTERMOST binder domain cost nothing), then the per-call memo is
cleared around the walk exactly as `abstract1Fast` clears it. -/
def abstractRangeFast (fuel : Nat) (e : EIdx) (d k c : Nat) : AM EIdx := do
  if k = 0 then pure e
  else do
    abs1Clear
    let r ← abstractRangeGo d k fuel e c
    abs1Clear
    pure r

/-! ## `lowerBVars` — `ExprOps.lean:694-716`, `:2012-2049`, `:2144-2146` -/

mutual

/-- con-leche: ConLeche/Kernel/ExprOps.lean:694-716 lowerBVars
con-leche: ConLeche/Kernel/ExprOps.lean:2014-2051 lowerBVarsGo
Lower every loose bound variable `≥ cutoff + amount` by `amount`, with
con-leche's own `bvarB ≤ c + amount` cutoff.  The dispatcher (arms split per
DESIGN §8.6's ruling of 2026-09-22); the four leaf arms are `pure h` and stay
here, and so does the `bvar` arm, which is one `if` and no memo. -/
def lowerBVarsGo (amount : Nat) (fuel : Nat) (h : EIdx) (c : Nat) : AM EIdx :=
  match fuel with
  | 0 => fail (.internal "fuel exhausted: lowerBVars")
  | fuel + 1 => do
    let bb ← bvarB fuel h
    if bb ≤ c + amount then
      pure h
    else
      match ← view h with
      | .bvar i => if i ≥ c + amount then internE (.bvar (i - amount)) else pure h
      | .fvar _ _ => pure h
      | .sort _ => pure h
      | .const _ _ => pure h
      | .lit _ => pure h
      | .app f a => lowerArmApp amount fuel h c f a
      | .lam ty body m => lowerArmLam amount fuel h c ty body m
      | .forallE ty body m => lowerArmForallE amount fuel h c ty body m
      | .letE ty val body => lowerArmLet amount fuel h c ty val body
      | .proj n i sub => lowerArmProj amount fuel h c n i sub
termination_by (fuel, 0)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2014-2051 lowerBVarsGo — the
`app` arm. -/
def lowerArmApp (amount fuel : Nat) (h : EIdx) (c : Nat) (f a : EIdx) :
    AM EIdx := do
  match ← lowerGet (h, c) with
  | some r => pure r
  | none => do
    let f' ← lowerBVarsGo amount fuel f c
    let a' ← lowerBVarsGo amount fuel a c
    let r ← internE (.app f' a')
    lowerSet (h, c) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2014-2051 lowerBVarsGo — the
`lam` arm. -/
def lowerArmLam (amount fuel : Nat) (h : EIdx) (c : Nat) (ty body : EIdx)
    (m : ConLeche.BinderMeta) : AM EIdx := do
  match ← lowerGet (h, c) with
  | some r => pure r
  | none => do
    let t ← lowerBVarsGo amount fuel ty c
    let b ← lowerBVarsGo amount fuel body (c + 1)
    let r ← internE (.lam t b m)
    lowerSet (h, c) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2014-2051 lowerBVarsGo — the
`forallE` arm. -/
def lowerArmForallE (amount fuel : Nat) (h : EIdx) (c : Nat) (ty body : EIdx)
    (m : ConLeche.BinderMeta) : AM EIdx := do
  match ← lowerGet (h, c) with
  | some r => pure r
  | none => do
    let t ← lowerBVarsGo amount fuel ty c
    let b ← lowerBVarsGo amount fuel body (c + 1)
    let r ← internE (.forallE t b m)
    lowerSet (h, c) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2014-2051 lowerBVarsGo — the
`letE` arm. -/
def lowerArmLet (amount fuel : Nat) (h : EIdx) (c : Nat) (ty val body : EIdx) :
    AM EIdx := do
  match ← lowerGet (h, c) with
  | some r => pure r
  | none => do
    let t ← lowerBVarsGo amount fuel ty c
    let w ← lowerBVarsGo amount fuel val c
    let b ← lowerBVarsGo amount fuel body (c + 1)
    let r ← internE (.letE t w b)
    lowerSet (h, c) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2014-2051 lowerBVarsGo — the
`proj` arm. -/
def lowerArmProj (amount fuel : Nat) (h : EIdx) (c : Nat) (n : NIdx) (i : Nat)
    (sub : EIdx) : AM EIdx := do
  match ← lowerGet (h, c) with
  | some r => pure r
  | none => do
    let u ← lowerBVarsGo amount fuel sub c
    let r ← internE (.proj n i u)
    lowerSet (h, c) r
    pure r
termination_by (fuel, 1)

end

/-- con-leche: none — `lowerBVarsGo`'s clause at fuel `0` (template rule 9). -/
theorem lowerBVarsGo_zero (amount : Nat) (h : EIdx) (c : Nat) :
    lowerBVarsGo amount 0 h c =
      fail (.internal "fuel exhausted: lowerBVars") := by
  rw [lowerBVarsGo]

/-- con-leche: none — `lowerBVarsGo`'s clause at `fuel + 1` (template rule
9). -/
theorem lowerBVarsGo_succ (amount fuel : Nat) (h : EIdx) (c : Nat) :
    lowerBVarsGo amount (fuel + 1) h c = (do
      let bb ← bvarB fuel h
      if bb ≤ c + amount then
        pure h
      else
        match ← view h with
        | .bvar i => if i ≥ c + amount then internE (.bvar (i - amount)) else pure h
        | .fvar _ _ => pure h
        | .sort _ => pure h
        | .const _ _ => pure h
        | .lit _ => pure h
        | .app f a => lowerArmApp amount fuel h c f a
        | .lam ty body m => lowerArmLam amount fuel h c ty body m
        | .forallE ty body m => lowerArmForallE amount fuel h c ty body m
        | .letE ty val body => lowerArmLet amount fuel h c ty val body
        | .proj n i sub => lowerArmProj amount fuel h c n i sub) := by
  rw [lowerBVarsGo]
/-- con-leche: ConLeche/Kernel/ExprOps.lean:2146-2148 lowerBVarsFast — the
top-level entry. -/
def lowerBVarsFast (fuel amount c : Nat) (e : EIdx) : AM EIdx := do
  lowerClear
  let r ← lowerBVarsGo amount fuel e c
  lowerClear
  pure r

/-! ## `instantiate1Lift` — `ExprOps.lean:718-739`, `:2222-2261`, `:2356-2358`

The general capture-avoiding substitution: unlike `instantiate1`, the
replacement's own loose `bvar`s are lifted past the binders crossed on the
way, which is what makes it usable on let-values.  It is the module's one
NESTED walk — its `bvar` arm runs `liftLooseBVars`, which is why the two have
separate memo tables. -/

mutual

/-- con-leche: ConLeche/Kernel/ExprOps.lean:718-739 instantiate1Lift
con-leche: ConLeche/Kernel/ExprOps.lean:2224-2263 instantiate1LiftGo
Replace `bvar d` by `v`, lifting `v`'s loose `bvar`s past the binders crossed
on the way, with con-leche's own `bvarB ≤ d` cutoff.  The dispatcher (arms
split per DESIGN §8.6's ruling of 2026-09-22); the `bvar` arm — the NESTED
one, which runs `liftLooseBVars` — has no memo probe and stays here. -/
def instantiate1LiftGo (v : EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    AM EIdx :=
  match fuel with
  | 0 => fail (.internal "fuel exhausted: instantiate1Lift")
  | fuel + 1 => do
    let bb ← bvarB fuel h
    if bb ≤ d then
      pure h
    else
      match ← view h with
      | .bvar i =>
        if i = d then liftLooseBVarsFast fuel d 0 v
        else if i > d then internE (.bvar (i - 1))
        else pure h
      | .fvar _ _ => pure h
      | .sort _ => pure h
      | .const _ _ => pure h
      | .lit _ => pure h
      | .app f a => inst1LiftArmApp v fuel h d f a
      | .lam ty body m => inst1LiftArmLam v fuel h d ty body m
      | .forallE ty body m => inst1LiftArmForallE v fuel h d ty body m
      | .letE ty val body => inst1LiftArmLet v fuel h d ty val body
      | .proj n i sub => inst1LiftArmProj v fuel h d n i sub
termination_by (fuel, 0)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2224-2263 instantiate1LiftGo —
the `app` arm. -/
def inst1LiftArmApp (v : EIdx) (fuel : Nat) (h : EIdx) (d : Nat) (f a : EIdx) :
    AM EIdx := do
  match ← inst1LGet (h, d) with
  | some r => pure r
  | none => do
    let f' ← instantiate1LiftGo v fuel f d
    let a' ← instantiate1LiftGo v fuel a d
    let r ← internE (.app f' a')
    inst1LSet (h, d) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2224-2263 instantiate1LiftGo —
the `lam` arm. -/
def inst1LiftArmLam (v : EIdx) (fuel : Nat) (h : EIdx) (d : Nat)
    (ty body : EIdx) (m : ConLeche.BinderMeta) : AM EIdx := do
  match ← inst1LGet (h, d) with
  | some r => pure r
  | none => do
    let t ← instantiate1LiftGo v fuel ty d
    let b ← instantiate1LiftGo v fuel body (d + 1)
    let r ← internE (.lam t b m)
    inst1LSet (h, d) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2224-2263 instantiate1LiftGo —
the `forallE` arm. -/
def inst1LiftArmForallE (v : EIdx) (fuel : Nat) (h : EIdx) (d : Nat)
    (ty body : EIdx) (m : ConLeche.BinderMeta) : AM EIdx := do
  match ← inst1LGet (h, d) with
  | some r => pure r
  | none => do
    let t ← instantiate1LiftGo v fuel ty d
    let b ← instantiate1LiftGo v fuel body (d + 1)
    let r ← internE (.forallE t b m)
    inst1LSet (h, d) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2224-2263 instantiate1LiftGo —
the `letE` arm. -/
def inst1LiftArmLet (v : EIdx) (fuel : Nat) (h : EIdx) (d : Nat)
    (ty val body : EIdx) : AM EIdx := do
  match ← inst1LGet (h, d) with
  | some r => pure r
  | none => do
    let t ← instantiate1LiftGo v fuel ty d
    let w ← instantiate1LiftGo v fuel val d
    let b ← instantiate1LiftGo v fuel body (d + 1)
    let r ← internE (.letE t w b)
    inst1LSet (h, d) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2224-2263 instantiate1LiftGo —
the `proj` arm. -/
def inst1LiftArmProj (v : EIdx) (fuel : Nat) (h : EIdx) (d : Nat) (n : NIdx)
    (i : Nat) (sub : EIdx) : AM EIdx := do
  match ← inst1LGet (h, d) with
  | some r => pure r
  | none => do
    let u ← instantiate1LiftGo v fuel sub d
    let r ← internE (.proj n i u)
    inst1LSet (h, d) r
    pure r
termination_by (fuel, 1)

end

/-- con-leche: none — `instantiate1LiftGo`'s clause at fuel `0` (template
rule 9). -/
theorem instantiate1LiftGo_zero (v h : EIdx) (d : Nat) :
    instantiate1LiftGo v 0 h d =
      fail (.internal "fuel exhausted: instantiate1Lift") := by
  rw [instantiate1LiftGo]

/-- con-leche: none — `instantiate1LiftGo`'s clause at `fuel + 1` (template
rule 9). -/
theorem instantiate1LiftGo_succ (v : EIdx) (fuel : Nat) (h : EIdx) (d : Nat) :
    instantiate1LiftGo v (fuel + 1) h d = (do
      let bb ← bvarB fuel h
      if bb ≤ d then
        pure h
      else
        match ← view h with
        | .bvar i =>
          if i = d then liftLooseBVarsFast fuel d 0 v
          else if i > d then internE (.bvar (i - 1))
          else pure h
        | .fvar _ _ => pure h
        | .sort _ => pure h
        | .const _ _ => pure h
        | .lit _ => pure h
        | .app f a => inst1LiftArmApp v fuel h d f a
        | .lam ty body m => inst1LiftArmLam v fuel h d ty body m
        | .forallE ty body m => inst1LiftArmForallE v fuel h d ty body m
        | .letE ty val body => inst1LiftArmLet v fuel h d ty val body
        | .proj n i sub => inst1LiftArmProj v fuel h d n i sub) := by
  rw [instantiate1LiftGo]
/-- con-leche: ConLeche/Kernel/ExprOps.lean:2358-2360 instantiate1LiftFast —
the top-level entry. -/
def instantiate1LiftFast (fuel : Nat) (e v : EIdx) (d : Nat := 0) : AM EIdx := do
  inst1LClear
  let r ← instantiate1LiftGo v fuel e d
  inst1LClear
  pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2367-2380 instPisAtLift —
instantiate the leading `∀`-binders at *open* arguments. -/
def instPisAtLift (fuel : Nat) : List EIdx → EIdx → AM (Option EIdx)
  | [], e => pure (some e)
  | a :: as, h => do
    match ← view h with
    | .forallE _ body _ => do
      let b ← instantiate1LiftFast fuel body a 0
      instPisAtLift fuel as b
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2384-2390 exprPtrBEq — structural
expression equality with a physical-equality shortcut.  In the arena it IS
index equality: `denoteE` is injective (`denoteE_inj`, task #97a), so two
handles denote one term exactly when they are the same handle, and the
pointer test and the structural test collapse into one machine-word
comparison.  No state is read, so this twin takes no monad — the census's
mechanical `AM Bool` is too crude here, as it says of every derived-word
predicate. -/
def exprPtrBEq (a b : EIdx) : Bool := a == b

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2401-2408 Level.hasParam — whether
a level mentions any parameter.  con-leche walks the level; the arena reads
the bit the level store already carries (`LDer.hasParam`, exact by
`LStore.derived_exact`), which is DESIGN §8.3's level-substitution cutoff in
`O(1)`. -/
def LIdx.hasParam (h : LIdx) : AM Bool := do
  let d ← derivedL h
  pure d.hasParam

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2422-2437 Expr.hasLevelParam —
whether an expression mentions any level parameter.  Again a field read: this
is exactly the `hasLP` bit of the packed derived word, and `Expr.hasLP_eq` is
con-leche's own proof that the two agree. -/
def EIdx.hasLevelParam (h : EIdx) : AM Bool := do
  let der ← derivedE h
  pure (lpOfData der)

/-! ## `instantiateLevelParams` — `ExprOps.lean:2564-2603`, `:2718-2720`

**The one twin that touches a level algorithm** (DESIGN §8.3 lesson 4).  The
substitution's names and levels are read back ONCE, at the entry, and the
walk then runs con-leche's own `Level.subst` and `Level.substPW` on transient
trees and re-interns the result.  The twin's `ks`/`us` are therefore
`List Name` and `List Level`, not `List NIdx` and `LsIdx` as the census's
mechanical column has them — that column's rule stops where lesson 4
starts. -/

/-- con-leche: ConLeche/Kernel/Level.lean:26-37 subst — `vs.map (Level.subst
ks us)` as explicit recursion.  con-leche writes the `.map`; a closure is
what DESIGN §3.4 forbids in code Aeneas must translate, and §3.4's own rule
for a `List` recursion is a helper, so the twin has one. -/
def substLevelList (ks : List ConLeche.Name) (us : List Level) :
    List Level → List Level
  | [] => []
  | u :: rest => Level.subst ks us u :: substLevelList ks us rest

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo — the
LEVEL-handle substitution behind a per-call memo (task #97-P6-13).
`instLPGo`'s `.sort` arm reads a level back, runs `Level.subst` and re-interns
once per OCCURRENCE; keyed on the level handle alone, the whole of that is one
probe.  The key omits `ks`/`us` for the reason DESIGN §8.3 gives for
`instantiate`/`abstract`/`instantiateLevelParams`: the table is cleared at
every top-level call (`instLPClear`), so within one call the two vectors are
constants. -/
def substLMemoAt (ks : List ConLeche.Name) (us : List Level) (u : LIdx) : AM LIdx := do
  match ← instLPLGet u with
  | some r => pure r
  | none => do
    let l ← readLevelM u
    let hl ← internLevel (Level.subst ks us l)
    instLPLSet u hl
    pure hl

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo — the same
at a universe-argument LIST handle, for the `.const` arm. -/
def substLsMemoAt (ks : List ConLeche.Name) (us : List Level) (vs : LsIdx) :
    AM LsIdx := do
  match ← instLPLsGet vs with
  | some r => pure r
  | none => do
    let ls ← readLevelsM vs
    let vs' ← internLevels (substLevelList ks us ls)
    instLPLsSet vs vs'
    pure vs'

mutual

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo —
substitute level parameters throughout an expression, with con-leche's own
`hasLP = false` cutoff (the whole subtree is level-parameter free, so the
substitution is the identity on it).  `.sort` and `.const` read their levels
back, run `Level.subst` on the transient trees and re-intern; nothing else in
this module touches a level.  The dispatcher (arms split per DESIGN §8.6's
ruling of 2026-09-22); the two LEVEL arms have no memo probe of their own and
stay here, beside the two leaves. -/
def instLPGo (ks : List ConLeche.Name) (us : List Level) (fuel : Nat)
    (h : EIdx) : AM EIdx :=
  match fuel with
  | 0 => fail (.internal "fuel exhausted: instantiateLevelParams")
  | fuel + 1 => do
    let der ← derivedE h
    if !(lpOfData der) then
      pure h
    else
      match ← view h with
      | .bvar _ => pure h
      | .lit _ => pure h
      | .sort u => do
        let hl ← substLMemoAt ks us u
        internRebuiltSort h (hl == u) hl
      | .const n vs => do
        let vs' ← substLsMemoAt ks us vs
        internRebuiltConst h (vs' == vs) n vs'
      | .fvar i ty => instLPArmFVar ks us fuel h i ty
      | .app f a => instLPArmApp ks us fuel h f a
      | .lam ty body m => instLPArmLam ks us fuel h ty body m
      | .forallE ty body m => instLPArmForallE ks us fuel h ty body m
      | .letE ty val body => instLPArmLet ks us fuel h ty val body
      | .proj n i sub => instLPArmProj ks us fuel h n i sub
termination_by (fuel, 0)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo — the
`fvar` arm. -/
def instLPArmFVar (ks : List ConLeche.Name) (us : List Level) (fuel : Nat)
    (h : EIdx) (i : Nat) (ty : EIdx) : AM EIdx := do
  match ← instLPGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← instLPGo ks us fuel ty
    let r ← internRebuiltFVar h (t == ty) i t
    instLPSet (h, 0) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo — the
`app` arm. -/
def instLPArmApp (ks : List ConLeche.Name) (us : List Level) (fuel : Nat)
    (h : EIdx) (f a : EIdx) : AM EIdx := do
  match ← instLPGet (h, 0) with
  | some r => pure r
  | none => do
    let f' ← instLPGo ks us fuel f
    let a' ← instLPGo ks us fuel a
    let r ← internRebuiltApp h (f' == f && a' == a) f' a'
    instLPSet (h, 0) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo — the
`lam` arm; the binder's prop-ness datum is substituted too. -/
def instLPArmLam (ks : List ConLeche.Name) (us : List Level) (fuel : Nat)
    (h : EIdx) (ty body : EIdx) (m : ConLeche.BinderMeta) : AM EIdx := do
  match ← instLPGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← instLPGo ks us fuel ty
    let b ← instLPGo ks us fuel body
    let m2 : ConLeche.BinderMeta := ⟨Level.substPW ks us m.pw⟩
    let r ← internRebuiltLam h (t == ty && b == body && m2 == m) t b m2
    instLPSet (h, 0) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo — the
`forallE` arm. -/
def instLPArmForallE (ks : List ConLeche.Name) (us : List Level) (fuel : Nat)
    (h : EIdx) (ty body : EIdx) (m : ConLeche.BinderMeta) : AM EIdx := do
  match ← instLPGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← instLPGo ks us fuel ty
    let b ← instLPGo ks us fuel body
    let m2 : ConLeche.BinderMeta := ⟨Level.substPW ks us m.pw⟩
    let r ← internRebuiltForallE h (t == ty && b == body && m2 == m) t b m2
    instLPSet (h, 0) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo — the
`letE` arm. -/
def instLPArmLet (ks : List ConLeche.Name) (us : List Level) (fuel : Nat)
    (h : EIdx) (ty val body : EIdx) : AM EIdx := do
  match ← instLPGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← instLPGo ks us fuel ty
    let w ← instLPGo ks us fuel val
    let b ← instLPGo ks us fuel body
    let r ← internRebuiltLetE h (t == ty && w == val && b == body) t w b
    instLPSet (h, 0) r
    pure r
termination_by (fuel, 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo — the
`proj` arm. -/
def instLPArmProj (ks : List ConLeche.Name) (us : List Level) (fuel : Nat)
    (h : EIdx) (n : NIdx) (i : Nat) (sub : EIdx) : AM EIdx := do
  match ← instLPGet (h, 0) with
  | some r => pure r
  | none => do
    let u' ← instLPGo ks us fuel sub
    let r ← internRebuiltProj h (u' == sub) n i u'
    instLPSet (h, 0) r
    pure r
termination_by (fuel, 1)

end

/-- con-leche: none — `instLPGo`'s clause at fuel `0` (template rule 9). -/
theorem instLPGo_zero (ks : List ConLeche.Name) (us : List Level) (h : EIdx) :
    instLPGo ks us 0 h =
      fail (.internal "fuel exhausted: instantiateLevelParams") := by
  rw [instLPGo]

/-- con-leche: none — `instLPGo`'s clause at `fuel + 1` (template rule 9). -/
theorem instLPGo_succ (ks : List ConLeche.Name) (us : List Level) (fuel : Nat)
    (h : EIdx) :
    instLPGo ks us (fuel + 1) h = (do
      let der ← derivedE h
      if !(lpOfData der) then
        pure h
      else
        match ← view h with
        | .bvar _ => pure h
        | .lit _ => pure h
        | .sort u => do
          let hl ← substLMemoAt ks us u
          internRebuiltSort h (hl == u) hl
        | .const n vs => do
          let vs' ← substLsMemoAt ks us vs
          internRebuiltConst h (vs' == vs) n vs'
        | .fvar i ty => instLPArmFVar ks us fuel h i ty
        | .app f a => instLPArmApp ks us fuel h f a
        | .lam ty body m => instLPArmLam ks us fuel h ty body m
        | .forallE ty body m => instLPArmForallE ks us fuel h ty body m
        | .letE ty val body => instLPArmLet ks us fuel h ty val body
        | .proj n i sub => instLPArmProj ks us fuel h n i sub) := by
  rw [instLPGo]
/-- con-leche: ConLeche/Kernel/ExprOps.lean:2720-2722 Expr.instLPFast — the
top-level entry: read the substitution back out of the store once, walk, drop
the memo. -/
def instLPFast (fuel : Nat) (ks : List NIdx) (us : LsIdx) (e : EIdx) : AM EIdx := do
  -- **The cutoff hoisted over the readback** (task #97-P6-10), the shape task
  -- #97-P6-9's item 5 has at `instantiateList`'s `.bvar` clause.  `instLPGo`'s
  -- own first act is `hasLP e = false → e`, and the walk is the only consumer
  -- of `ksP`/`usP`; so on a level-parameter-free term both readbacks are
  -- computed and dropped.  Deciding the cutoff FIRST is the same value by the
  -- walk's own equation, in `O(1)` off the derived word.
  if !(lpOfData (← derivedE e)) then pure e
  else do
    let ksP ← readNamesM ks
    let usP ← readLevelsM us
    instLPClear
    let r ← instLPGo ksP usP fuel e
    instLPClear
    pure r

end ConRon.Arena

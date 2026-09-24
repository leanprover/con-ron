/-
# `ConRon.Arena.Monad` — the monad, the state and the store primitives of (B)

DESIGN.md §8.4: "the monad is `AM := StateT AState (Except CheckError)` and
nothing else — no `IO`, no `partial`, no typeclass-polymorphic bodies".

This module is the seam between the *frozen* store API of task #97a
(`Arena/{Handle,Store,Denote,WF,WFProofs}.lean`) and every twin above it.
It adds no store lemma of its own; what it adds is

* `AState` — the `EStore` plus the eleven per-call memo tables the `ExprOps`
  twins need (DESIGN §8.3 "Caches": keyed by `(EIdx, offset)` as nanoda does,
  cleared at every top-level entry, so the substitution vector is never in the
  key), grouped in one `Memos` record so that a spec theorem states what a
  call touched in ONE equation instead of eleven;
* `fail` — **the one named failure primitive** (task #97s's template rule 7: a
  bare `throw` in `StateT σ (Except ε)` leaves `mvcgen` with universe
  metavariables and no spec applies);
* `view` / `derivedE` / `internE` and their name-, level- and level-list
  counterparts, each written the way the Rust will be (detach before update,
  DESIGN §8.4 lesson 14), with **the capacity test at the wrapper**: DESIGN
  §8.3's "the Rust raises `Native` at the limit, the Lean `throw`s the same
  kind" — which is what keeps `EStore.intern` total and discharges
  `EStore.intern_spec`'s `capOK` hypothesis from a branch condition;
* `readLevel` / `readLevels` / `internLevel` / `internLevels` — DESIGN §8.3's
  "intern the representation, not the algorithm" (lesson 4).  A level
  operation runs on a transient `ConLeche.Level` tree read back out of the
  store and the result is re-interned; the readback IS `denoteL`, so the
  readback's spec theorem is an equation and not a simulation.

`Main.lean` carries its own copy of `CheckError` (it predates this library and
imports nothing from it); the two are the same constructors and P2d merges
them when the driver is wired to the checker.
-/
import ConRon.Arena.WFProofs
import ConRon.Arena.CoreState
import ConLeche.Kernel.Level

namespace ConRon.Arena

open ConLeche

/-! ## The error -/

/-- con-leche: ConLeche/Kernel/Core.lean:53-72 CheckError — the checker's
error, verbatim (census class (P)), plus the fourth constructor the arena
needs: DESIGN §8.3's handle word runs out at 2^27 nodes per constructor per
tier and the checker `throw`s `native` there, exactly as the Rust port's
`Native` does.  A `native` claims nothing about the input, so the bridge
claims nothing about a run that raises one. -/
inductive CheckError where
  | notImplemented (what : String)
  | invalid (what : String)
  | internal (msg : String)
  | native (what : String)
  deriving Repr, DecidableEq, Inhabited

/-! ## The per-call memo tables -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:60-62 Inst1MemoInv — the memo
tables of the `ExprOps` twins, in one record.

con-leche threads each memo as an explicit argument-and-result pair
(`instantiate1Go v memo e d : Expr × Std.HashMap …`); the arena carries them
in the state, which is what the census's twin column means by "the `…Go`
family loses the pair and the `AM` carries it".  Eleven tables, one per
con-leche `…Go`, because the walks NEST — `instantiate1Lift`'s `bvar` arm
calls `liftLooseBVars`, so a single shared table would answer one walk with
the other's answers.

The nine handle-valued tables are keyed `(EIdx × Nat)`: the node and the
traversal cursor, which is what the answer depends on once the substituted
term is fixed (nanoda's trick, DESIGN §8.3 "Caches").  Three of con-leche's
walks have no cursor (`resetMetaGo`, `renameConstsGo`, `instLPGo` key on the
node alone); the arena keys them at cursor `0` so that every handle-valued
memo has ONE invariant and one insert lemma.  The two `Nat`-valued tables are
the saturated-branch recomputations of the packed range fields. -/
structure Memos where
  /-- `instantiate1` (`ExprOps.lean:80-116`). -/
  inst1C : Std.HashMap (EIdx × Nat) EIdx
  /-- `instantiateList` (`ExprOps.lean:267-303`). -/
  instLC : Std.HashMap (EIdx × Nat) EIdx
  /-- `liftLooseBVars` (`ExprOps.lean:430-466`). -/
  liftC : Std.HashMap (EIdx × Nat) EIdx
  /-- `resetMeta` (`ExprOps.lean:579-615`), at cursor `0`. -/
  resetC : Std.HashMap (EIdx × Nat) EIdx
  /-- `renameConsts` (`ExprOps.lean:999-1036`), at cursor `0`. -/
  renameC : Std.HashMap (EIdx × Nat) EIdx
  /-- `abstract1` (`ExprOps.lean:1789-1833`). -/
  abs1C : Std.HashMap (EIdx × Nat) EIdx
  /-- `lowerBVars` (`ExprOps.lean:2012-2049`). -/
  lowerC : Std.HashMap (EIdx × Nat) EIdx
  /-- `instantiate1Lift` (`ExprOps.lean:2222-2261`). -/
  inst1LC : Std.HashMap (EIdx × Nat) EIdx
  /-- `instantiateLevelParams` (`ExprOps.lean:2564-2603`), at cursor `0`. -/
  instLPC : Std.HashMap (EIdx × Nat) EIdx
  /-- `bvarBound` (`ExprOps.lean:1368-1392`). -/
  bvarBC : Std.HashMap EIdx Nat
  /-- `fvarRange` (`ExprOps.lean:1397-1422`). -/
  fvarBC : Std.HashMap EIdx Nat
  /-- `instantiateLevelParams`' LEVEL-handle substitution, a per-call memo of
  `instLPGo`'s own level work (task #97-P6-13).  The key omits `ks`/`us` for
  the reason DESIGN §8.3 gives for the three walks above: the table is cleared
  at every top-level call (`instLPClear`), so within one call the two vectors
  are constants. -/
  instLPLC : Std.HashMap LIdx LIdx
  /-- The same at a universe-argument LIST handle, for the `.const` arm. -/
  instLPLsC : Std.HashMap LsIdx LsIdx

/-- con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast — every
walk starts from the empty memo (`(instantiate1Go v {} e d).1`), so this is
what a top-level entry installs. -/
def Memos.empty : Memos := ⟨∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅⟩

instance : Inhabited Memos := ⟨Memos.empty⟩

/-! ## The state and the monad -/

/-- con-leche: ConLeche/Cached/StateC.lean:127-156 CState — the checker state of
(B) as P2b needs it: the arena and the per-call memo tables.  P2c extends it
with the per-declaration caches (`whnfCore`, `whnf`, the three infer grades,
`defeq`) and the environment index. -/
structure AState where
  store : EStore
  memos : Memos
  /-- The per-DECLARATION caches (task #97c, `Arena/CoreState.lean`): the
  five entry-point memos, the `defeq` verdict table, the two level-verdict
  tables and the three lazy instantiated-constant tables.  A record of its
  own beside `memos`, because the per-call clear and the per-declaration
  drop are different operations on different lifetimes. -/
  caches : Caches
  /-- The PIN TABLE (task #97-P6-4a, `Arena/CoreState.lean`): the reserved
  constant names interned once at the driver.  Empty until `internAllPins`
  fills it, which is what makes an early read a stop rather than a wrong
  answer. -/
  pins : Pins

/-- con-leche: ConLeche/Cached/StateC.lean:164-166 CheckCM
con-leche: ConLeche/Kernel/Core.lean:80 CheckM
The one monad of (B)
(DESIGN §8.4: "`AM := StateT AState (Except CheckError)` and nothing
else"). -/
abbrev AM := StateT AState (Except CheckError)

/-- con-leche: none — the initial state over a given arena. -/
def AState.init (st : EStore) : AState := ⟨st, .empty, .empty, .empty⟩

/-- con-leche: ConLeche/Kernel/Core.lean:53-72 CheckError — **the one failure
primitive of (B)** (task #97s template rule 7).  Written as a bare `throw`,
the `MonadExceptOf` instance path through `StateT` leaves `mvcgen` with
universe metavariables (`Spec.throw_Except.{?u, ?u, 0}`) and no spec applies;
behind this `def`, one `@[spec]` theorem covers every failure site. -/
def fail {α : Type} (e : CheckError) : AM α := throwThe CheckError e

/-! ## The expression store's primitives -/

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — decode a handle.  A
dangling handle is an internal error: the checker never builds one, and the
bridge claims nothing on failure. -/
@[inline] def view (h : EIdx) : AM ENodeView := do
  let s ← get
  match s.store.view h with
  | some v => pure v
  | none => fail (.internal "arena: dangling expression handle")

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — the packed derived
word of a handle (the `data` computed field, lines 357-402), read in `O(1)`
off the derived column. -/
@[inline] def derivedE (h : EIdx) : AM UInt64 := do
  let s ← get
  pure (s.store.derived h)

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — hash-cons a
binder DATUM, the Rust's `EStore::intern_bm` clause for clause (task
#97-T2-LOCKSTEP D6): the persistent probe, the scratch probe when the scratch
tier is open, and the capacity test only where the datum is APPENDED — on the
datum miss, at the tier the append goes to (`EStore.capOKBM`).  The probe is
`EStore.findBM`, the same one `internBM` makes; on a hit the store does not
move.  (The Rust's `shared_on` / `M_FROZEN` arm is a `Native`, which claims
nothing, and has no twin — task #97-P5-Unfreeze.) -/
def internBME (m : ConLeche.BinderMeta) : AM BMIdx := do
  let s ← get
  match s.store.findBM m with
  | some i => pure i
  | none =>
    let nbm := if s.store.scratchOn then s.store.scr.bmSize else s.store.pers.bmSize
    if nbm < Idx.idxCap then
      let st := s.store
      let s := { s with store := EStore.empty }
      let (st, i) := st.internBM m
      set { s with store := st }
      pure i
    else
      fail (.native "arena: expression constructor array full")

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — `internE` at the
`lam` constructor with the binder datum already a HANDLE (task #97-P6-16).
The capacity test is `internE`'s own, at the binder array.

**PROBE FIRST**, as `internE` does (task #97-P5-1's finding 9; at this family
task #97-P5-3 round 3's **finding 15**, fixed at task #97-P5-Twin): the Rust's
`intern_lam_i` probes `pers.lams` and then `scr.lams` and tests `Tbl::full`
only where it is about to APPEND, so on a cons HIT at a full `lams` array it
answers `Ok`.  A datum handle needs no room of its own on either path — it is
already interned, it is the cons key — so the only test left is the node
array's, on the miss, **at the tier the append goes to**, which is the
`if scratchOn` the Rust's own `if self.scratch_on` branch makes.  (The test
used to be a conjunction over both tiers, which declined on the strength of a
tier the append never touches.)  The probe is `EStore.findBindI`, the same one
`internBindI` makes; on a hit the store does not move and the handle is the
one the cons table already holds. -/
def internLamIE (ty b : EIdx) (mi : BMIdx) : AM EIdx := do
  let s ← get
  match s.store.findBindI ETag.lam ty b mi with
  | some h => pure h
  | none =>
    let n := if s.store.scratchOn then s.store.scr.bindSizeOf ETag.lam
             else s.store.pers.bindSizeOf ETag.lam
    if n < Idx.idxCap then
      let st := s.store
      let s := { s with store := EStore.empty }
      let (st, h) := st.internLamI ty b mi
      set { s with store := st }
      pure h
    else
      fail (.native "arena: expression constructor array full")

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — `internE` at the
`forallE` constructor with the binder datum already a HANDLE.  Probe first,
for `internLamIE`'s reason and at the other array. -/
def internForallEIE (ty b : EIdx) (mi : BMIdx) : AM EIdx := do
  let s ← get
  match s.store.findBindI ETag.forallE ty b mi with
  | some h => pure h
  | none =>
    let n := if s.store.scratchOn then s.store.scr.bindSizeOf ETag.forallE
             else s.store.pers.bindSizeOf ETag.forallE
    if n < Idx.idxCap then
      let st := s.store
      let s := { s with store := EStore.empty }
      let (st, h) := st.internForallEI ty b mi
      set { s with store := st }
      pure h
    else
      fail (.native "arena: expression constructor array full")

/-- con-leche: none — hash-cons a NON-binder expression node: the eight arms of
the Rust's `EStore::intern` other than `intern_lam` / `intern_forall_e`
(`intern_bvar` … `intern_proj`).  DESIGN §8.3: "the Rust raises `Native` at
the limit, the Lean `throw`s the same kind" — the capacity test lives HERE, at
the monadic wrapper, so that `EStore.intern` stays total and
`EStore.intern_spec`'s `capOK` hypothesis is discharged by this branch.

**PROBE FIRST** (task #97-P5-1's finding 9, fixed in the twin at #97-P3-1):
the Rust tests `Tbl::full` only where it is about to APPEND — inside the
cons-table miss path — so on a cons HIT at a full constructor array it answers
`Ok`.  The probe is `EStore.find?`, the same one `intern` makes; on a hit the
store does not move and the handle is the one the cons table already holds
(`EStore.view_of_find`).  A non-binder view names no datum, so the datum array
is not part of the test. -/
def internNodeE (v : ENodeView) : AM EIdx := do
  let s ← get
  match s.store.find? v with
  | some h => pure h
  | none =>
    let n := if s.store.scratchOn then s.store.scr.sizeOf v else s.store.pers.sizeOf v
    if n < Idx.idxCap then
      let st := s.store
      let s := { s with store := EStore.empty }
      let (st, h) := st.intern v
      set { s with store := st }
      pure h
    else
      fail (.native "arena: expression constructor array full")

/-- con-leche: none — hash-cons an expression node: the Rust's
`EStore::intern`, a dispatch on the view.

**The two BINDER arms are the Rust's `intern_lam` / `intern_forall_e`, step for
step** (task #97-T2-LOCKSTEP D6): the datum first (`internBME`, the port's
`intern_bm`, whose capacity test is on the datum miss only), then the binder
node at the datum HANDLE that step answered (`internLamIE` /
`internForallEIE`, the port's `intern_lam_i` / `intern_forall_e_i`: the node
probe at that handle, the node array's test on the node miss only, the derived
word read off the datum's stored row).  The twin used to probe `find?` over
the whole view, test BOTH arrays on the miss and then run `EStore.intern`,
which recomputes the derived word from the datum's VALUE — equal to the port at
a `StoreWF` store (`Refine2/Specs.lean`'s `intern_lam_eq`), but not in
lockstep: on a datum miss it tested the node array where the port first probes
at the fresh handle, and it read the derived word off `m` where the port reads
the stored row.  The eight other arms are `internNodeE`. -/
def internE (v : ENodeView) : AM EIdx :=
  match v with
  | .lam ty b m => do
    let mi ← internBME m
    internLamIE ty b mi
  | .forallE ty b m => do
    let mi ← internBME m
    internForallEIE ty b mi
  | .bvar i => internNodeE (.bvar i)
  | .fvar idx ty => internNodeE (.fvar idx ty)
  | .sort u => internNodeE (.sort u)
  | .const n us => internNodeE (.const n us)
  | .app f a => internNodeE (.app f a)
  | .letE ty val b => internNodeE (.letE ty val b)
  | .lit l => internNodeE (.lit l)
  | .proj n i e => internNodeE (.proj n i e)

/-! ### The dangling-handle declines, named once

DESIGN §8.4's "one named `fail`" rule at the two handle kinds whose
PROJECTIONS answer `Option`: a projection that has already decided the tag
returns the field and nothing else, and the caller spells the decline with
`view`'s own error.  Naming them keeps the thirteen projections' callers from
inventing thirteen messages (task #97-P6-10; `#[cold]` on the Rust side, which
Charon does not read). -/

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `none` arm of
`view`, spelled once. -/
def failDanglingE {α : Type} : AM α :=
  fail (.internal "arena: dangling expression handle")

/-- con-leche: ConLeche/Kernel/Expr.lean:41-54 Level — the `none` arm of
`viewLs`, spelled once. -/
def failDanglingLs {α : Type} : AM α :=
  fail (.internal "arena: dangling level-list handle")

/-! ### The per-constructor PROJECTIONS of `view` (tasks #97-P6-10, #97-P6-13)

A walk that has already read the tag off the handle word wants one
constructor's fields and nothing else; going through `view` would decode a
whole `ENodeView` and dispatch on the tag a second time.  Each projection is
`EStore`'s own under a state read, and each answers `Option` rather than
failing, so that the caller spells `view`'s decline itself. -/

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `app` projection. -/
@[inline] def viewApp (h : EIdx) : AM (Option (EIdx × EIdx)) := do
  let s ← get; pure (s.store.viewApp h)

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `bvar` projection. -/
@[inline] def viewBVar (h : EIdx) : AM (Option Nat) := do
  let s ← get; pure (s.store.viewBVar h)

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `sort` projection. -/
@[inline] def viewSort (h : EIdx) : AM (Option LIdx) := do
  let s ← get; pure (s.store.viewSort h)

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `const` projection. -/
@[inline] def viewConst (h : EIdx) : AM (Option (NIdx × LsIdx)) := do
  let s ← get; pure (s.store.viewConst h)

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the head NAME of a
`const` node; the level arguments are left in the store. -/
@[inline] def viewConstName (h : EIdx) : AM (Option NIdx) := do
  let s ← get; pure (s.store.viewConstName h)

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `fvar` index. -/
@[inline] def viewFVarIdx (h : EIdx) : AM (Option Nat) := do
  let s ← get; pure (s.store.viewFVarIdx h)

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `fvar` binder
type. -/
@[inline] def viewFVarTy (h : EIdx) : AM (Option EIdx) := do
  let s ← get; pure (s.store.viewFVarTy h)

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `lit` projection. -/
@[inline] def viewLit (h : EIdx) : AM (Option ConLeche.Literal) := do
  let s ← get; pure (s.store.viewLit h)

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the binder projection,
with the datum decoded. -/
@[inline] def viewBind (h : EIdx) : AM (Option (EIdx × EIdx × ConLeche.BinderMeta)) := do
  let s ← get; pure (s.store.viewBind h)

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the binder
projection that stops at the datum's HANDLE (task #97-P6-16): a walk that
takes a binder apart and puts it back never looks inside the datum. -/
@[inline] def viewBindI (h : EIdx) : AM (Option (EIdx × EIdx × BMIdx)) := do
  let s ← get; pure (s.store.viewBindI h)

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — decode a binder
datum handle. -/
@[inline] def viewBM (mi : BMIdx) : AM (Option ConLeche.BinderMeta) := do
  let s ← get; pure (s.store.viewBM mi)

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `letE`
projection. -/
@[inline] def viewLet (h : EIdx) : AM (Option (EIdx × EIdx × EIdx)) := do
  let s ← get; pure (s.store.viewLet h)

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — the `proj`
projection. -/
@[inline] def viewProj (h : EIdx) : AM (Option (NIdx × Nat × EIdx)) := do
  let s ← get; pure (s.store.viewProj h)

/-! ### `internE`'s clauses, one entry per constructor (task #97-P6-15)

`internE` takes an `ENodeView`, so every caller BUILT one; these entries take
the arm's own fields, so the view is never built at all.  Same store
operation, same capacity test, same `Native` decline — the equation the bridge
owes is `internCE (fields) = internE (.C fields)`, `rfl`. -/

/-- con-leche: none — `internE` at the `bvar` constructor. -/
@[inline] def internBVarE (i : Nat) : AM EIdx := internE (.bvar i)
/-- con-leche: none — `internE` at the `fvar` constructor. -/
@[inline] def internFVarE (idx : Nat) (ty : EIdx) : AM EIdx := internE (.fvar idx ty)
/-- con-leche: none — `internE` at the `sort` constructor. -/
@[inline] def internSortE (u : LIdx) : AM EIdx := internE (.sort u)
/-- con-leche: none — `internE` at the `const` constructor. -/
@[inline] def internConstE (n : NIdx) (us : LsIdx) : AM EIdx := internE (.const n us)
/-- con-leche: none — `internE` at the `app` constructor. -/
@[inline] def internAppE (f a : EIdx) : AM EIdx := internE (.app f a)
/-- con-leche: none — `internE` at the `lam` constructor. -/
@[inline] def internLamE (ty b : EIdx) (m : ConLeche.BinderMeta) : AM EIdx :=
  internE (.lam ty b m)
/-- con-leche: none — `internE` at the `forallE` constructor. -/
@[inline] def internForallEE (ty b : EIdx) (m : ConLeche.BinderMeta) : AM EIdx :=
  internE (.forallE ty b m)
/-- con-leche: none — `internE` at the `letE` constructor. -/
@[inline] def internLetEE (ty val b : EIdx) : AM EIdx := internE (.letE ty val b)
/-- con-leche: none — `internE` at the `lit` constructor. -/
@[inline] def internLitE (l : ConLeche.Literal) : AM EIdx := internE (.lit l)
/-- con-leche: none — `internE` at the `proj` constructor. -/
@[inline] def internProjE (n : NIdx) (i : Nat) (e : EIdx) : AM EIdx :=
  internE (.proj n i e)

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the two binder
arms at a tag the caller carries and a datum it holds as a handle: the shape
the rebuilding walks want, where `eBindView` + `internE` stood. -/
@[inline] def internBindIE (tag : UInt32) (ty b : EIdx) (mi : BMIdx) : AM EIdx :=
  if tag == ETag.lam then internLamIE ty b mi else internForallEIE ty b mi

/-! ## The name store's primitives -/

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — decode a name handle. -/
@[inline] def viewN (h : NIdx) : AM NNodeView := do
  let s ← get
  match s.store.ns.view h with
  | some v => pure v
  | none => fail (.internal "arena: dangling name handle")

/-- con-leche: none — hash-cons a name node, through the nesting. -/
def internNNode (v : NNodeView) : AM NIdx := do
  let s ← get
  let ns := s.store.ns
  -- **Probe first** (task #97-P5-1's finding 9), as `internE` does.
  match ns.find? v with
  | some h => pure h
  | none =>
    let n := if ns.scratchOn then ns.scr.sizeOf v else ns.pers.sizeOf v
    if n < Idx.idxCap then
      let st := s.store
      let s := { s with store := EStore.empty }
      let (st, h) := st.internName v
      set { s with store := st }
      pure h
    else
      fail (.native "arena: name constructor array full")

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — read a name back out of
the store as a transient `ConLeche.Name`.  Names are compared by handle
throughout the checker (DESIGN §8.3), so this is the error-text and
level-substitution path only, and the readback IS the denotation. -/
def readName (h : NIdx) : AM ConLeche.Name := do
  let s ← get
  match denoteN s.store.ns h with
  | some x => pure x
  | none => fail (.internal "arena: dangling name handle")

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — read a LIST of name
handles back.  `ks.mapM readName` would do it with a closure, which DESIGN
§3.4 forbids in code Aeneas must translate; §3.4's rule for a `List`
recursion is a helper, so this is one. -/
def readNames : List NIdx → AM (List ConLeche.Name)
  | [] => pure []
  | h :: hs => do
    let x ← readName h
    let xs ← readNames hs
    pure (x :: xs)

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — intern a transient
name.  Structural on `Name`, so no fuel: the tree is a value, not a DAG. -/
def internName : ConLeche.Name → AM NIdx
  | .anonymous => internNNode .anonymous
  | .str p s => do
    let hp ← internName p
    internNNode (.str hp s)
  | .num p n => do
    let hp ← internName p
    internNNode (.num hp n)

/-! ## The level store's primitives -/

/-- con-leche: ConLeche/Kernel/Expr.lean:41-54 Level — decode a level
handle. -/
@[inline] def viewL (h : LIdx) : AM LNodeView := do
  let s ← get
  match s.store.ls.view h with
  | some v => pure v
  | none => fail (.internal "arena: dangling level handle")

/-- con-leche: ConLeche/Kernel/Expr.lean:41-54 Level — the level's derived
pair (its 32-bit hash and its `hasParam` bit, the computed field at lines
47-53), read in `O(1)`. -/
@[inline] def derivedL (h : LIdx) : AM LDer := do
  let s ← get
  pure (s.store.lder h)

/-- con-leche: none — hash-cons a level node, through the nesting. -/
def internLNode (v : LNodeView) : AM LIdx := do
  let s ← get
  let ls := s.store.ls
  -- **Probe first** (task #97-P5-1's finding 9), as `internE` does.
  match ls.find? v with
  | some h => pure h
  | none =>
    let n := if ls.scratchOn then ls.scr.sizeOf v else ls.pers.sizeOf v
    if n < Idx.idxCap then
      let st := s.store
      let s := { s with store := EStore.empty }
      let (st, h) := st.internLevel v
      set { s with store := st }
      pure h
    else
      fail (.native "arena: level constructor array full")

/-- con-leche: ConLeche/Kernel/Level.lean:26-37 subst — **the readback**
(DESIGN §8.3 lesson 4, "intern the representation, not the algorithm"): a
level ALGORITHM runs on a transient `ConLeche.Level` tree read out of the
store, never on handles.  The readback is `denoteL` itself, so the spec
theorem for this primitive is an equation and not a simulation. -/
def readLevel (h : LIdx) : AM Level := do
  let s ← get
  match denoteL s.store.ls h with
  | some l => pure l
  | none => fail (.internal "arena: dangling level handle")

/-- con-leche: ConLeche/Kernel/Expr.lean:41-54 Level — intern a transient
level tree.  Structural on `Level`, so no fuel. -/
def internLevel : Level → AM LIdx
  | .zero => internLNode .zero
  | .succ u => do
    let hu ← internLevel u
    internLNode (.succ hu)
  | .max u v => do
    let hu ← internLevel u
    let hv ← internLevel v
    internLNode (.max hu hv)
  | .imax u v => do
    let hu ← internLevel u
    let hv ← internLevel v
    internLNode (.imax hu hv)
  | .param n => do
    let hn ← internName n
    internLNode (.param hn)

/-! ## The level-list store's primitives -/

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — decode a
universe-argument list handle (the `const` node's second field, line 347). -/
@[inline] def viewLs (h : LsIdx) : AM LsNodeView := do
  let s ← get
  match s.store.lss.view h with
  | some v => pure v
  | none => fail (.internal "arena: dangling level-list handle")

/-- con-leche: none — hash-cons a universe-argument list. -/
def internLsNode (v : LsNodeView) : AM LsIdx := do
  let s ← get
  let lss := s.store.lss
  -- **Probe first** (task #97-P5-1's finding 9), as `internE` does.
  match lss.find? v with
  | some h => pure h
  | none =>
    let n := if lss.scratchOn then lss.scr.sizeOf v else lss.pers.sizeOf v
    if n < Idx.idxCap then
      let st := s.store
      let s := { s with store := EStore.empty }
      let (st, h) := st.internLevels v
      set { s with store := st }
      pure h
    else
      fail (.native "arena: level-list array full")

/-- con-leche: ConLeche/Kernel/Level.lean:26-37 subst — read a universe
argument list back as transient `Level` trees. -/
def readLevels (h : LsIdx) : AM (List Level) := do
  let s ← get
  match denoteLs s.store.lss h with
  | some us => pure us
  | none => fail (.internal "arena: dangling level-list handle")

/-- con-leche: none — intern a list of transient levels, one handle each. -/
def internLevelList : List Level → AM (List LIdx)
  | [] => pure []
  | u :: us => do
    let hu ← internLevel u
    let hus ← internLevelList us
    pure (hu :: hus)

/-- con-leche: none — intern a list of transient levels and hash-cons the
list node. -/
def internLevels (us : List Level) : AM LsIdx := do
  let hs ← internLevelList us
  internLsNode hs

/-- con-leche: ConLeche/Kernel/Expr.lean:41-54 Level — the LENGTH projection
of `viewLs` (task #97-P6-10): the callers that only compare a
universe-argument list's length with a declaration's level-parameter count
want this, and it reads the record's own length. -/
@[inline] def viewLsLen (h : LsIdx) : AM (Option Nat) := do
  let s ← get; pure (s.store.lss.viewLen h)

/-! ## The readback memo (task #97-P6-13)

DESIGN §8.3's "memoised readback per declaration", which nothing had built.
`readLevel` / `readName` / `readLevels` rebuild a transient tree node by node
out of the store every time they are asked, and the checker asks per
OCCURRENCE: `instLPGo`'s `.sort` and `.const` arms, `Level.isEquiv`'s two
misses, `proofPW`'s substitution and the recursor's comparands.  The
denotation of a handle is a function of the handle and of the tier it names,
so a row is valid for exactly as long as the other eleven cache tables are —
the per-declaration bracket flushes the caches and drops the tier in one
operation, which is what makes a stale row impossible.

The obligation is a MEMO obligation and not a new algorithm: `denoteL`,
`denoteN` and `denoteLs` are functions of the store, so a hit answers with the
row the miss stored. -/

/-- con-leche: ConLeche/Kernel/Level.lean:26-37 subst — the memoised
`readLevel`. -/
def readLevelM (h : LIdx) : AM Level := do
  let s ← get
  match s.caches.readLC[h]? with
  | some l => pure l
  | none =>
    match denoteL s.store.ls h with
    | none => fail (.internal "arena: dangling level handle")
    | some l =>
      let mp := s.caches.readLC
      let s := { s with caches := { s.caches with readLC := ∅ } }
      set { s with caches := { s.caches with readLC := mp.insert h l } }
      pure l

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — the memoised
`readName`. -/
def readNameM (h : NIdx) : AM ConLeche.Name := do
  let s ← get
  match s.caches.readNC[h]? with
  | some x => pure x
  | none =>
    match denoteN s.store.ns h with
    | none => fail (.internal "arena: dangling name handle")
    | some x =>
      let mp := s.caches.readNC
      let s := { s with caches := { s.caches with readNC := ∅ } }
      set { s with caches := { s.caches with readNC := mp.insert h x } }
      pure x

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — the memoised
`readNames`.  The recursion is on the list, as `readNames`' is; the Rust's
`_from` cursor companion is §3.4's standing `List`-as-`Vec` deviation. -/
def readNamesM : List NIdx → AM (List ConLeche.Name)
  | [] => pure []
  | h :: hs => do
    let x ← readNameM h
    let xs ← readNamesM hs
    pure (x :: xs)

/-- con-leche: ConLeche/Kernel/Level.lean:26-37 subst — the memoised
`readLevels`. -/
def readLevelsM (h : LsIdx) : AM (List Level) := do
  let s ← get
  match s.caches.readLsC[h]? with
  | some us => pure us
  | none =>
    match denoteLs s.store.lss h with
    | none => failDanglingLs
    | some us =>
      let mp := s.caches.readLsC
      let s := { s with caches := { s.caches with readLsC := ∅ } }
      set { s with caches := { s.caches with readLsC := mp.insert h us } }
      pure us

/-! ## Interning into the PERSISTENT tier (the promotion's primitives)

DESIGN §8.3, "Phase A runs in the scratch tier too, with promotion".  Four
monadic twins of `internE` / `internNNode` / `internLNode` / `internLsNode`
that append to the PERSISTENT tier whatever tier the store is in, over
`Arena/Store.lean`'s `internPersistent` family.  The capacity test is the same
one at the same place, against the persistent array; the error is the same
`Native` kind.  `Arena/Promote.lean` is the only caller.
-/

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — arena
infrastructure; the binder datum's promote-intern, with the Rust's
`intern_bm_persistent` capacity test where it makes it: on the persistent
datum MISS only.  (The Rust's `shared_on` / `M_FROZEN` arm before it is a
`Native`, which claims nothing, and has no twin — task #97-P5-Unfreeze.) -/
def internBMPersistentE (m : ConLeche.BinderMeta) : AM BMIdx := do
  let s ← get
  match s.store.persFindBM m with
  | some i => pure i
  | none =>
    if s.store.pers.bmSize < Idx.idxCap then
      let st := s.store
      let s := { s with store := EStore.empty }
      let (st, i) := st.internBMPersistent m
      set { s with store := st }
      pure i
    else
      fail (.native "arena: expression constructor array full")

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — arena
infrastructure; the datum a view names, made persistent: the Rust's
`intern_bm_of_view_persistent`.  A non-binder view names no datum. -/
def internBMOfViewPersistentE (v : ENodeView) : AM BMIdx :=
  match v with
  | .lam _ _ m => internBMPersistentE m
  | .forallE _ _ m => internBMPersistentE m
  | _ => pure (Idx.ofWord 0)

/-- con-leche: none — arena infrastructure; hash-cons an expression node into
the persistent tier.

**In the Rust's order** (task #97-T2-LOCKSTEP, audit D3): the DATUM first,
with its own capacity test on its own miss path only
(`internBMOfViewPersistentE`); then the node probe at the persistent tier with
the datum handle that step answered; then the NODE array's test, on the node
miss only (task #97-P5-1's finding 9); then the append.  The wrapper used to
probe `persFind?` and test `bmSize` on every binder-node miss, so at a full
datum array a new binder node over an EXISTING datum threw `native` where the
port answers `Ok` — the corner task #97-P5-Twin round 2 closed in `internE`.
`EStore.internPersistent` is still the composition of the two store halves
(`EStore.internPersistent_eq_at`). -/
def internPersistentE (v : ENodeView) : AM EIdx := do
  let mi ← internBMOfViewPersistentE v
  let s ← get
  match s.store.pers.find? v mi with
  | some h => pure h
  | none =>
    if s.store.pers.sizeOf v < Idx.idxCap then
      let st := s.store
      let s := { s with store := EStore.empty }
      let (st, h) := st.internPersistentAt v mi
      set { s with store := st }
      pure h
    else
      fail (.native "arena: expression constructor array full")

/-- con-leche: none — arena infrastructure; hash-cons a name node into the
persistent tier, through the nesting. -/
def internPersistentN (v : NNodeView) : AM NIdx := do
  let s ← get
  match s.store.ns.pers.find? v with
  | some h => pure h
  | none =>
  if s.store.ns.pers.sizeOf v < Idx.idxCap then
    let st := s.store
    let s := { s with store := EStore.empty }
    let (st, h) := st.internNamePersistent v
    set { s with store := st }
    pure h
  else
    fail (.native "arena: name constructor array full")

/-- con-leche: none — arena infrastructure; hash-cons a level node into the
persistent tier, through the nesting. -/
def internPersistentL (v : LNodeView) : AM LIdx := do
  let s ← get
  match s.store.ls.pers.find? v with
  | some h => pure h
  | none =>
  if s.store.ls.pers.sizeOf v < Idx.idxCap then
    let st := s.store
    let s := { s with store := EStore.empty }
    let (st, h) := st.internLevelPersistent v
    set { s with store := st }
    pure h
  else
    fail (.native "arena: level constructor array full")

/-- con-leche: none — arena infrastructure; hash-cons a universe-argument list
into the persistent tier, through the nesting. -/
def internPersistentLs (v : LsNodeView) : AM LsIdx := do
  let s ← get
  match s.store.lss.pers.find? v with
  | some h => pure h
  | none =>
  if s.store.lss.pers.sizeOf v < Idx.idxCap then
    let st := s.store
    let s := { s with store := EStore.empty }
    let (st, h) := st.internLevelsPersistent v
    set { s with store := st }
    pure h
  else
    fail (.native "arena: level-list array full")

/-! ## The memo tables, one probe/record/drop triple per walk

Nine handle-valued tables and two `Nat`-valued ones.  Every record detaches
the table before the update (DESIGN §8.4 lesson 14) and every drop sets the
`Memos` field to `∅`; both are `@[noinline]` for the same reason the store's
mutations are (lesson 15). -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — probe the
`instantiate1` memo. -/
@[inline] def inst1Get (k : EIdx × Nat) : AM (Option EIdx) := do
  let s ← get; pure s.memos.inst1C[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — record an
`instantiate1` answer (detach before update). -/
@[noinline] def inst1Set (k : EIdx × Nat) (r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.memos.inst1C
  let s := { s with memos := { s.memos with inst1C := ∅ } }
  set { s with memos := { s.memos with inst1C := mp.insert k r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast — the
memo is "dropped after each call, since it also depends on `v`". -/
@[noinline] def inst1Clear : AM Unit := do
  let s ← get
  set { s with memos := { s.memos with inst1C := ∅ } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — probe
the `instantiateList` memo. -/
@[inline] def instLGet (k : EIdx × Nat) : AM (Option EIdx) := do
  let s ← get; pure s.memos.instLC[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — record
an `instantiateList` answer. -/
@[noinline] def instLSet (k : EIdx × Nat) (r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.memos.instLC
  let s := { s with memos := { s.memos with instLC := ∅ } }
  set { s with memos := { s.memos with instLC := mp.insert k r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:371-373 instantiateListFast — drop
the `instantiateList` memo (it depends on `vs`). -/
@[noinline] def instLClear : AM Unit := do
  let s ← get
  set { s with memos := { s.memos with instLC := ∅ } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo — probe
the `liftLooseBVars` memo. -/
@[inline] def liftGet (k : EIdx × Nat) : AM (Option EIdx) := do
  let s ← get; pure s.memos.liftC[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo — record
a `liftLooseBVars` answer. -/
@[noinline] def liftSet (k : EIdx × Nat) (r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.memos.liftC
  let s := { s with memos := { s.memos with liftC := ∅ } }
  set { s with memos := { s.memos with liftC := mp.insert k r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:532-534 liftLooseBVarsFast — drop
the `liftLooseBVars` memo (it depends on `amount`). -/
@[noinline] def liftClear : AM Unit := do
  let s ← get
  set { s with memos := { s.memos with liftC := ∅ } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo — probe the
`resetMeta` memo. -/
@[inline] def resetGet (k : EIdx × Nat) : AM (Option EIdx) := do
  let s ← get; pure s.memos.resetC[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo — record a
`resetMeta` answer. -/
@[noinline] def resetSet (k : EIdx × Nat) (r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.memos.resetC
  let s := { s with memos := { s.memos with resetC := ∅ } }
  set { s with memos := { s.memos with resetC := mp.insert k r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:687-688 resetMetaFast — drop the
`resetMeta` memo. -/
@[noinline] def resetClear : AM Unit := do
  let s ← get
  set { s with memos := { s.memos with resetC := ∅ } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1001-1038 renameConstsGo — probe
the `renameConsts` memo. -/
@[inline] def renameGet (k : EIdx × Nat) : AM (Option EIdx) := do
  let s ← get; pure s.memos.renameC[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1001-1038 renameConstsGo — record a
`renameConsts` answer. -/
@[noinline] def renameSet (k : EIdx × Nat) (r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.memos.renameC
  let s := { s with memos := { s.memos with renameC := ∅ } }
  set { s with memos := { s.memos with renameC := mp.insert k r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1111-1113 renameConstsFast — drop
the `renameConsts` memo (it depends on the renaming). -/
@[noinline] def renameClear : AM Unit := do
  let s ← get
  set { s with memos := { s.memos with renameC := ∅ } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — probe the
`abstract1` memo. -/
@[inline] def abs1Get (k : EIdx × Nat) : AM (Option EIdx) := do
  let s ← get; pure s.memos.abs1C[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — record an
`abstract1` answer. -/
@[noinline] def abs1Set (k : EIdx × Nat) (r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.memos.abs1C
  let s := { s with memos := { s.memos with abs1C := ∅ } }
  set { s with memos := { s.memos with abs1C := mp.insert k r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1929-1931 abstract1Fast — drop the
`abstract1` memo (it depends on `d`). -/
@[noinline] def abs1Clear : AM Unit := do
  let s ← get
  set { s with memos := { s.memos with abs1C := ∅ } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2014-2051 lowerBVarsGo — probe the
`lowerBVars` memo. -/
@[inline] def lowerGet (k : EIdx × Nat) : AM (Option EIdx) := do
  let s ← get; pure s.memos.lowerC[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2014-2051 lowerBVarsGo — record a
`lowerBVars` answer. -/
@[noinline] def lowerSet (k : EIdx × Nat) (r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.memos.lowerC
  let s := { s with memos := { s.memos with lowerC := ∅ } }
  set { s with memos := { s.memos with lowerC := mp.insert k r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2146-2148 lowerBVarsFast — drop
the `lowerBVars` memo (it depends on `amount`). -/
@[noinline] def lowerClear : AM Unit := do
  let s ← get
  set { s with memos := { s.memos with lowerC := ∅ } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2224-2263 instantiate1LiftGo —
probe the `instantiate1Lift` memo. -/
@[inline] def inst1LGet (k : EIdx × Nat) : AM (Option EIdx) := do
  let s ← get; pure s.memos.inst1LC[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2224-2263 instantiate1LiftGo —
record an `instantiate1Lift` answer. -/
@[noinline] def inst1LSet (k : EIdx × Nat) (r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.memos.inst1LC
  let s := { s with memos := { s.memos with inst1LC := ∅ } }
  set { s with memos := { s.memos with inst1LC := mp.insert k r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2358-2360 instantiate1LiftFast —
drop the `instantiate1Lift` memo (it depends on `v`). -/
@[noinline] def inst1LClear : AM Unit := do
  let s ← get
  set { s with memos := { s.memos with inst1LC := ∅ } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo — probe
the level-substitution memo. -/
@[inline] def instLPGet (k : EIdx × Nat) : AM (Option EIdx) := do
  let s ← get; pure s.memos.instLPC[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo — record a
level-substitution answer. -/
@[noinline] def instLPSet (k : EIdx × Nat) (r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.memos.instLPC
  let s := { s with memos := { s.memos with instLPC := ∅ } }
  set { s with memos := { s.memos with instLPC := mp.insert k r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2720-2722 Expr.instLPFast — drop
the level-substitution memo (it depends on `ks` and `us`). -/
@[noinline] def instLPClear : AM Unit := do
  let s ← get
  set { s with memos :=
    { s.memos with instLPC := ∅, instLPLC := ∅, instLPLsC := ∅ } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo — probe the
level-handle substitution memo (task #97-P6-13). -/
@[inline] def instLPLGet (h : LIdx) : AM (Option LIdx) := do
  let s ← get; pure s.memos.instLPLC[h]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo — record a
level-handle substitution. -/
@[noinline] def instLPLSet (h : LIdx) (r : LIdx) : AM Unit := do
  let s ← get
  let mp := s.memos.instLPLC
  let s := { s with memos := { s.memos with instLPLC := ∅ } }
  set { s with memos := { s.memos with instLPLC := mp.insert h r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo — probe the
level-LIST substitution memo. -/
@[inline] def instLPLsGet (h : LsIdx) : AM (Option LsIdx) := do
  let s ← get; pure s.memos.instLPLsC[h]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo — record a
level-LIST substitution. -/
@[noinline] def instLPLsSet (h : LsIdx) (r : LsIdx) : AM Unit := do
  let s ← get
  let mp := s.memos.instLPLsC
  let s := { s with memos := { s.memos with instLPLsC := ∅ } }
  set { s with memos := { s.memos with instLPLsC := mp.insert h r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1370-1394 bvarBoundGo — probe the
loose-bvar-bound memo. -/
@[inline] def bvarBGet (k : EIdx) : AM (Option Nat) := do
  let s ← get; pure s.memos.bvarBC[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1370-1394 bvarBoundGo — record a
loose-bvar bound. -/
@[noinline] def bvarBSet (k : EIdx) (r : Nat) : AM Unit := do
  let s ← get
  let mp := s.memos.bvarBC
  let s := { s with memos := { s.memos with bvarBC := ∅ } }
  set { s with memos := { s.memos with bvarBC := mp.insert k r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1396-1397 bvarBoundMemo — drop the
loose-bvar-bound memo. -/
@[noinline] def bvarBClear : AM Unit := do
  let s ← get
  set { s with memos := { s.memos with bvarBC := ∅ } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1399-1424 fvarRangeGo — probe the
fvar-range memo. -/
@[inline] def fvarBGet (k : EIdx) : AM (Option Nat) := do
  let s ← get; pure s.memos.fvarBC[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1399-1424 fvarRangeGo — record an
fvar range. -/
@[noinline] def fvarBSet (k : EIdx) (r : Nat) : AM Unit := do
  let s ← get
  let mp := s.memos.fvarBC
  let s := { s with memos := { s.memos with fvarBC := ∅ } }
  set { s with memos := { s.memos with fvarBC := mp.insert k r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1426-1427 fvarRangeMemo — drop the
fvar-range memo. -/
@[noinline] def fvarBClear : AM Unit := do
  let s ← get
  set { s with memos := { s.memos with fvarBC := ∅ } }

end ConRon.Arena

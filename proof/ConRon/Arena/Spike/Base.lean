/-
# The P2s spike: the monad, the state and the store primitives

DESIGN.md §8.6's `P2s SPIKE`.  This library is **not** imported by
`ConRon.Arena`: it is a throw-away twin of three functions
(`instantiate1`, one `whnfCore` arm, one memo wrapper), written exactly as
§8.4 says the real (B) must be written, so that the proof idioms can be
priced before P2b–P2d start at scale.

The monad is §8.4's, verbatim: `AM := StateT AState (Except CheckError)` and
nothing else.  `AState` holds the `EStore` of task #97a plus the two memo
tables the three subjects need.

Everything here is stated against the *frozen* store API of task #97a
(`ConRon/Arena/{Handle,Store,Denote,WF,WFProofs}.lean`); this module adds no
store lemma of its own.
-/
import ConRon.Arena
import ConLeche.Kernel.Core
import ConLeche.Kernel.ExprOps
import Std.Tactic.Do

namespace ConRon.Arena.Spike

open ConLeche Std.Do

set_option mvcgen.warning false

/-! ## The state and the monad -/

/-- con-leche: ConLeche/Cached/CoreC.lean:120 CState — the checker state of
(B), cut down to what the three spike subjects touch: the arena, the
per-call `instantiate1` memo (keyed by node *and* cursor, as con-leche's
`Inst1MemoInv` is: `ConLeche/Kernel/ExprOps.lean:62`) and the
per-declaration `whnfCore` memo (keyed by the handle alone — lesson 8). -/
structure AState where
  store : EStore
  inst1C : Std.HashMap (EIdx × Nat) EIdx
  whnfCoreC : Std.HashMap EIdx EIdx

/-- con-leche: ConLeche/Cached/CoreC.lean:170 CheckCM — the one monad of (B)
(DESIGN §8.4: "`AM := StateT AState (Except CheckError)` and nothing else"). -/
abbrev AM := StateT AState (Except CheckError)

/-- con-leche: none — the empty spike state. -/
def AState.init (st : EStore) : AState := ⟨st, ∅, ∅⟩

/-- con-leche: ConLeche/Kernel/Core.lean:62 CheckError — **the one failure
primitive of (B)**, and a finding of its own: written as a bare `throw`, the
`MonadExceptOf` instance path through `StateT` leaves `mvcgen` with universe
metavariables (`Spec.throw_Except.{?u, ?u, 0}`) and no spec applies.  Behind
this `def`, one `@[spec]` theorem (`fail_spec`, `Specs.lean`) covers every
failure site in the checker. -/
def fail {α : Type} (e : CheckError) : AM α := throwThe CheckError e

/-! ## The store primitives, as monadic operations

Three of them, and they are the whole seam between (B) and the store layer:
`view` decodes a handle, `internE` hash-conses a node, `derivedE` reads the
packed derived word.  Each is written the way the Rust will be (detach before
update, DESIGN §8.4 lesson 14). -/

/-- con-leche: ConLeche/Cached/CoreC.lean:— — decode a handle.  A dangling
handle is an internal error: the checker never builds one, and the bridge
claims nothing on failure. -/
def view (h : EIdx) : AM ENodeView := do
  let s ← get
  match s.store.view h with
  | some v => pure v
  | none => fail (.internal "arena: dangling expression handle")

/-- con-leche: ConLeche/Kernel/Expr.lean:356-402 Expr.data — the packed
derived word of a handle. -/
def derivedE (h : EIdx) : AM UInt64 := do
  let s ← get
  pure (s.store.derived h)

/-- con-leche: none — hash-cons a node.  DESIGN §8.3: "the Rust raises
`Native` at the limit, the Lean `throw`s the same kind" — the capacity test
lives *here*, at the monadic wrapper, so that `EStore.intern` stays total and
`EStore.intern_spec`'s `capOK` hypothesis is discharged by this branch. -/
def internE (v : ENodeView) : AM EIdx := do
  let s ← get
  let n := if s.store.scratchOn then s.store.scr.sizeOf v else s.store.pers.sizeOf v
  if n < Idx.idxCap then
    let st := s.store
    let s := { s with store := EStore.empty }
    let (st, h) := st.intern v
    set { s with store := st }
    pure h
  else
    fail (.internal "arena: constructor array full")

/-! ## The two memo tables -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:81 instantiate1Go — probe the
`instantiate1` memo. -/
def inst1Get (k : EIdx × Nat) : AM (Option EIdx) := do
  let s ← get
  pure s.inst1C[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:116 instantiate1Go — record an
`instantiate1` answer (detach before update). -/
def inst1Set (k : EIdx × Nat) (r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.inst1C
  let s := { s with inst1C := ∅ }
  set { s with inst1C := mp.insert k r }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:56 instantiate1Go — the memo is
"dropped after each call, since it also depends on `v`". -/
def inst1Clear : AM Unit := do
  let s ← get
  set { s with inst1C := ∅ }

/-- con-leche: ConLeche/Cached/CoreC.lean:1880 memoEI — probe the `whnfCore`
memo (keyed by the handle alone; lesson 8). -/
def whnfCoreGet (h : EIdx) : AM (Option EIdx) := do
  let s ← get
  pure s.whnfCoreC[h]?

/-- con-leche: ConLeche/Cached/CoreC.lean:1885 memoEI — record a `whnfCore`
answer (detach before update). -/
def whnfCoreSet (h r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.whnfCoreC
  let s := { s with whnfCoreC := ∅ }
  set { s with whnfCoreC := mp.insert h r }

end ConRon.Arena.Spike

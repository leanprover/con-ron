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
import ConLeche.Kernel.Level

namespace ConRon.Arena

open ConLeche

/-! ## The error -/

/-- con-leche: ConLeche/Kernel/Core.lean:47-66 CheckError — the checker's
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

/-- con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast — every
walk starts from the empty memo (`(instantiate1Go v {} e d).1`), so this is
what a top-level entry installs. -/
def Memos.empty : Memos := ⟨∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅⟩

instance : Inhabited Memos := ⟨Memos.empty⟩

/-! ## The state and the monad -/

/-- con-leche: ConLeche/Cached/StateC.lean:127-156 CState — the checker state of
(B) as P2b needs it: the arena and the per-call memo tables.  P2c extends it
with the per-declaration caches (`whnfCore`, `whnf`, the three infer grades,
`defeq`) and the environment index. -/
structure AState where
  store : EStore
  memos : Memos

/-- con-leche: ConLeche/Cached/StateC.lean:164-166 CheckCM — the one monad of (B)
(DESIGN §8.4: "`AM := StateT AState (Except CheckError)` and nothing
else"). -/
abbrev AM := StateT AState (Except CheckError)

/-- con-leche: none — the initial state over a given arena. -/
def AState.init (st : EStore) : AState := ⟨st, .empty⟩

/-- con-leche: ConLeche/Kernel/Core.lean:47-66 CheckError — **the one failure
primitive of (B)** (task #97s template rule 7).  Written as a bare `throw`,
the `MonadExceptOf` instance path through `StateT` leaves `mvcgen` with
universe metavariables (`Spec.throw_Except.{?u, ?u, 0}`) and no spec applies;
behind this `def`, one `@[spec]` theorem covers every failure site. -/
def fail {α : Type} (e : CheckError) : AM α := throwThe CheckError e

/-! ## The expression store's primitives -/

/-- con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr — decode a handle.  A
dangling handle is an internal error: the checker never builds one, and the
bridge claims nothing on failure. -/
def view (h : EIdx) : AM ENodeView := do
  let s ← get
  match s.store.view h with
  | some v => pure v
  | none => fail (.internal "arena: dangling expression handle")

/-- con-leche: ConLeche/Kernel/Expr.lean:343-402 Expr — the packed derived
word of a handle (the `data` computed field, lines 357-402), read in `O(1)`
off the derived column. -/
def derivedE (h : EIdx) : AM UInt64 := do
  let s ← get
  pure (s.store.derived h)

/-- con-leche: none — hash-cons an expression node.  DESIGN §8.3: "the Rust
raises `Native` at the limit, the Lean `throw`s the same kind" — the capacity
test lives HERE, at the monadic wrapper, so that `EStore.intern` stays total
and `EStore.intern_spec`'s `capOK` hypothesis is discharged by this branch. -/
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
    fail (.native "arena: expression constructor array full")

/-! ## The name store's primitives -/

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — decode a name handle. -/
def viewN (h : NIdx) : AM NNodeView := do
  let s ← get
  match s.store.ns.view h with
  | some v => pure v
  | none => fail (.internal "arena: dangling name handle")

/-- con-leche: none — hash-cons a name node, through the nesting. -/
def internNNode (v : NNodeView) : AM NIdx := do
  let s ← get
  let ns := s.store.ns
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

/-- con-leche: ConLeche/Kernel/Expr.lean:40-53 Level — decode a level
handle. -/
def viewL (h : LIdx) : AM LNodeView := do
  let s ← get
  match s.store.ls.view h with
  | some v => pure v
  | none => fail (.internal "arena: dangling level handle")

/-- con-leche: ConLeche/Kernel/Expr.lean:40-53 Level — the level's derived
pair (its 32-bit hash and its `hasParam` bit, the computed field at lines
47-53), read in `O(1)`. -/
def derivedL (h : LIdx) : AM LDer := do
  let s ← get
  pure (s.store.lder h)

/-- con-leche: none — hash-cons a level node, through the nesting. -/
def internLNode (v : LNodeView) : AM LIdx := do
  let s ← get
  let ls := s.store.ls
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

/-- con-leche: ConLeche/Kernel/Expr.lean:40-53 Level — intern a transient
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

/-- con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr — decode a
universe-argument list handle (the `const` node's second field, line 347). -/
def viewLs (h : LsIdx) : AM LsNodeView := do
  let s ← get
  match s.store.lss.view h with
  | some v => pure v
  | none => fail (.internal "arena: dangling level-list handle")

/-- con-leche: none — hash-cons a universe-argument list. -/
def internLsNode (v : LsNodeView) : AM LsIdx := do
  let s ← get
  let lss := s.store.lss
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

/-! ## The memo tables, one probe/record/drop triple per walk

Nine handle-valued tables and two `Nat`-valued ones.  Every record detaches
the table before the update (DESIGN §8.4 lesson 14) and every drop sets the
`Memos` field to `∅`; both are `@[noinline]` for the same reason the store's
mutations are (lesson 15). -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — probe the
`instantiate1` memo. -/
def inst1Get (k : EIdx × Nat) : AM (Option EIdx) := do
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
def instLGet (k : EIdx × Nat) : AM (Option EIdx) := do
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
def liftGet (k : EIdx × Nat) : AM (Option EIdx) := do
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
def resetGet (k : EIdx × Nat) : AM (Option EIdx) := do
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

/-- con-leche: ConLeche/Kernel/ExprOps.lean:999-1036 renameConstsGo — probe
the `renameConsts` memo. -/
def renameGet (k : EIdx × Nat) : AM (Option EIdx) := do
  let s ← get; pure s.memos.renameC[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:999-1036 renameConstsGo — record a
`renameConsts` answer. -/
@[noinline] def renameSet (k : EIdx × Nat) (r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.memos.renameC
  let s := { s with memos := { s.memos with renameC := ∅ } }
  set { s with memos := { s.memos with renameC := mp.insert k r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1109-1111 renameConstsFast — drop
the `renameConsts` memo (it depends on the renaming). -/
@[noinline] def renameClear : AM Unit := do
  let s ← get
  set { s with memos := { s.memos with renameC := ∅ } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1789-1833 abstract1Go — probe the
`abstract1` memo. -/
def abs1Get (k : EIdx × Nat) : AM (Option EIdx) := do
  let s ← get; pure s.memos.abs1C[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1789-1833 abstract1Go — record an
`abstract1` answer. -/
@[noinline] def abs1Set (k : EIdx × Nat) (r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.memos.abs1C
  let s := { s with memos := { s.memos with abs1C := ∅ } }
  set { s with memos := { s.memos with abs1C := mp.insert k r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1927-1929 abstract1Fast — drop the
`abstract1` memo (it depends on `d`). -/
@[noinline] def abs1Clear : AM Unit := do
  let s ← get
  set { s with memos := { s.memos with abs1C := ∅ } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2012-2049 lowerBVarsGo — probe the
`lowerBVars` memo. -/
def lowerGet (k : EIdx × Nat) : AM (Option EIdx) := do
  let s ← get; pure s.memos.lowerC[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2012-2049 lowerBVarsGo — record a
`lowerBVars` answer. -/
@[noinline] def lowerSet (k : EIdx × Nat) (r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.memos.lowerC
  let s := { s with memos := { s.memos with lowerC := ∅ } }
  set { s with memos := { s.memos with lowerC := mp.insert k r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2144-2146 lowerBVarsFast — drop
the `lowerBVars` memo (it depends on `amount`). -/
@[noinline] def lowerClear : AM Unit := do
  let s ← get
  set { s with memos := { s.memos with lowerC := ∅ } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2222-2261 instantiate1LiftGo —
probe the `instantiate1Lift` memo. -/
def inst1LGet (k : EIdx × Nat) : AM (Option EIdx) := do
  let s ← get; pure s.memos.inst1LC[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2222-2261 instantiate1LiftGo —
record an `instantiate1Lift` answer. -/
@[noinline] def inst1LSet (k : EIdx × Nat) (r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.memos.inst1LC
  let s := { s with memos := { s.memos with inst1LC := ∅ } }
  set { s with memos := { s.memos with inst1LC := mp.insert k r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2356-2358 instantiate1LiftFast —
drop the `instantiate1Lift` memo (it depends on `v`). -/
@[noinline] def inst1LClear : AM Unit := do
  let s ← get
  set { s with memos := { s.memos with inst1LC := ∅ } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2564-2603 Expr.instLPGo — probe
the level-substitution memo. -/
def instLPGet (k : EIdx × Nat) : AM (Option EIdx) := do
  let s ← get; pure s.memos.instLPC[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2564-2603 Expr.instLPGo — record a
level-substitution answer. -/
@[noinline] def instLPSet (k : EIdx × Nat) (r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.memos.instLPC
  let s := { s with memos := { s.memos with instLPC := ∅ } }
  set { s with memos := { s.memos with instLPC := mp.insert k r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2718-2720 Expr.instLPFast — drop
the level-substitution memo (it depends on `ks` and `us`). -/
@[noinline] def instLPClear : AM Unit := do
  let s ← get
  set { s with memos := { s.memos with instLPC := ∅ } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1368-1392 bvarBoundGo — probe the
loose-bvar-bound memo. -/
def bvarBGet (k : EIdx) : AM (Option Nat) := do
  let s ← get; pure s.memos.bvarBC[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1368-1392 bvarBoundGo — record a
loose-bvar bound. -/
@[noinline] def bvarBSet (k : EIdx) (r : Nat) : AM Unit := do
  let s ← get
  let mp := s.memos.bvarBC
  let s := { s with memos := { s.memos with bvarBC := ∅ } }
  set { s with memos := { s.memos with bvarBC := mp.insert k r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1394-1395 bvarBoundMemo — drop the
loose-bvar-bound memo. -/
@[noinline] def bvarBClear : AM Unit := do
  let s ← get
  set { s with memos := { s.memos with bvarBC := ∅ } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1397-1422 fvarRangeGo — probe the
fvar-range memo. -/
def fvarBGet (k : EIdx) : AM (Option Nat) := do
  let s ← get; pure s.memos.fvarBC[k]?

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1397-1422 fvarRangeGo — record an
fvar range. -/
@[noinline] def fvarBSet (k : EIdx) (r : Nat) : AM Unit := do
  let s ← get
  let mp := s.memos.fvarBC
  let s := { s with memos := { s.memos with fvarBC := ∅ } }
  set { s with memos := { s.memos with fvarBC := mp.insert k r } }

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1424-1425 fvarRangeMemo — drop the
fvar-range memo. -/
@[noinline] def fvarBClear : AM Unit := do
  let s ← get
  set { s with memos := { s.memos with fvarBC := ∅ } }

end ConRon.Arena

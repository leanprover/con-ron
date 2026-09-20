/-
# `ConRon.Arena.Frontend.NatOpGround` — hoisting a pinned `Nat` operation's
stream-certified ground (task #97d, DESIGN §8.6 P2e part 2 item 2)

The twin of `ConLeche/Frontend/NatOpGround.lean`, over handles.  It is the
second half of con-leche's order-insensitivity fix, beside the built-in
prelude: a pin-certified operation's certificate statements are spelled over
the STRUCTURAL `Nat` operations (`natOpDeps`), the install guard
`divModEnvGuard` requires those stored, and they are not in the operation's
own dependency closure — so an export that orders declarations by a DFS from
arbitrary roots declines at the install unless the parsed stream is
REORDERED.

Task #97e part 1 shipped the identity (`Arena/Frontend/Prepare.lean`'s
`hoistNatOpGround` placeholder) because the pass needs the kernel's
`natOpNames`/`natDivModNames`/`natOpDeps`, which arrived with the pins at
P2c/P2d.  This module is the real thing, and `Prepare.lean` now calls it.

## The shape, and what changed

* `usedConstsGo`'s `Std.HashSet Expr` becomes a `Std.HashSet EIdx` and the
  structural match a `view`, so the visited set is DESIGN §8.3's identity
  hash and a shared subterm costs one probe;
* the two `for`/`mut` loops of `hoistTargets` are explicit tail recursions
  (DESIGN §8.4 lesson 16: never `for`/`mut` over a large linear state, and
  the record array IS the stream), and the inner worklist's `while` is a
  fuelled recursion over an explicit stack;
* `applyHoist`'s comparator stays a function value.  It is a SORT's
  comparator, which `List.mergeSort` and Rust's `sort_by` both take, and it
  closes over the target table rather than over the records; there is no
  version of a sort that does not take one.
* the pass is a no-op — the array returned as it is, no sort — on every
  stream whose ground precedes its operations (the toolchain's own export
  order: `init-full`, Mathlib), so it costs one name-index build and nothing
  else there.
-/
import ConRon.Arena.Core

namespace ConRon.Arena.Frontend

open ConLeche
open ConRon.Arena

/-! ## The constants a record references -/

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:54-77 usedConstsGo — the
constants an expression DAG references, each node visited once.  con-leche's
`Std.HashSet Expr` (pointer-first equality, computed hash) is a
`Std.HashSet EIdx` here, whose hash IS the handle word. -/
def usedConstsGo (seen : Std.HashSet EIdx) (acc : Array NIdx) :
    Nat → EIdx → AM (Std.HashSet EIdx × Array NIdx)
  | 0, _ => fail (.internal "fuel exhausted: usedConsts")
  | fuel + 1, e => do
    if seen.contains e then pure (seen, acc) else do
      let seen := seen.insert e
      match ← view e with
      | .const n _ => pure (seen, acc.push n)
      | .app f a => do
        let (seen, acc) ← usedConstsGo seen acc fuel f
        usedConstsGo seen acc fuel a
      | .lam ty b _ | .forallE ty b _ => do
        let (seen, acc) ← usedConstsGo seen acc fuel ty
        usedConstsGo seen acc fuel b
      | .letE ty v b => do
        let (seen, acc) ← usedConstsGo seen acc fuel ty
        let (seen, acc) ← usedConstsGo seen acc fuel v
        usedConstsGo seen acc fuel b
      | .proj sn _ x => usedConstsGo seen (acc.push sn) fuel x
      | .fvar _ ty => usedConstsGo seen acc fuel ty
      | _ => pure (seen, acc)

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:79-95 Declaration.usedConsts
— an inductive block's members, folded over ONE visited set: the type of each
member and, for a recursor, every rule's right-hand side.  con-leche writes
it as a `List.foldl` with a closure; DESIGN §3.4's rule for a `List` fold is
a named recursion. -/
def usedConstsRules (seen : Std.HashSet EIdx) (acc : Array NIdx) :
    List IRecRule → AM (Std.HashSet EIdx × Array NIdx)
  | [] => pure (seen, acc)
  | r :: rs => do
    let (seen, acc) ← usedConstsGo seen acc coreWalkFuel r.rhs
    usedConstsRules seen acc rs

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:79-95 Declaration.usedConsts
— the block walk. -/
def usedConstsBlock (seen : Std.HashSet EIdx) (acc : Array NIdx) :
    List IConstantInfo → AM (Std.HashSet EIdx × Array NIdx)
  | [] => pure (seen, acc)
  | ci :: cs => do
    let ty := (← ci.toConstantVal).type
    let (seen, acc) ← usedConstsGo seen acc coreWalkFuel ty
    let (seen, acc) ← match ci with
      | .recInfo _ _ _ rules => usedConstsRules seen acc rules
      | _ => pure (seen, acc)
    usedConstsBlock seen acc cs

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:79-95 Declaration.usedConsts
— the constants a parsed record references (types, values, recursor rule
right-hand sides; a basis block references nothing the stream declares). -/
def IDeclaration.usedConsts : IDeclaration → AM (Array NIdx)
  | .axiomDecl cv => do pure (← usedConstsGo ∅ #[] coreWalkFuel cv.type).2
  | .defnDecl cv v _ | .thmDecl cv v | .opaqueDecl cv v => do
    let (seen, acc) ← usedConstsGo ∅ #[] coreWalkFuel cv.type
    pure (← usedConstsGo seen acc coreWalkFuel v).2
  | .indDecl block _ => do pure (← usedConstsBlock ∅ #[] block).2
  | .basisDecl _ | .quotDecl .. => pure #[]

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:97-104 isNatOpRecord — the
pinned `Nat` operation records whose ground the pass serves: the
pin-certified WF operations and the structural ones. -/
def isNatOpRecord : IDeclaration → AM (Option NIdx)
  | .defnDecl cv .. => do
    if (← natDivModNames).contains cv.name || (← natOpNames).contains cv.name then
      pure (some cv.name)
    else pure none
  | _ => pure none

/-! ## Which records must move, and how far -/

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets — the
name index's inner loop: the FIRST record declaring a name wins (a duplicate
is rejected by the fold anyway). -/
def insertNames (idx : Std.HashMap NIdx Nat) (i : Nat) :
    List NIdx → Std.HashMap NIdx Nat
  | [] => idx
  | n :: ns =>
    insertNames (if idx.contains n then idx else idx.insert n i) i ns

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets — name
↦ the index of the record declaring it.  con-leche's `for i in [0:ds.size]`
over a stream of millions is DESIGN §8.4 lesson 16's "large linear state", so
the loop is explicit tail recursion. -/
def nameIndex (ds : Array IDeclaration) (idx : Std.HashMap NIdx Nat) (k : Nat) :
    Std.HashMap NIdx Nat :=
  if h : k < ds.size then
    nameIndex ds (insertNames idx k ds[k].names) (k + 1)
  else idx
  termination_by ds.size - k

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets — the
worklist: the closure of `j` within the records after `i`, each reached
record marked as having to precede `i`.  con-leche's `while h : stack.size >
0` is a fuelled recursion over an explicit stack here; the fuel is
`ds.size + 1` per pushed record, which is above any reachable depth because a
record is inserted into `target` at a strictly smaller `i` each time it is
revisited. -/
def hoistClosure (ds : Array IDeclaration) (idx : Std.HashMap NIdx Nat) (i : Nat) :
    Nat → Std.HashMap Nat Nat → List Nat → AM (Std.HashMap Nat Nat)
  | 0, target, _ => pure target
  | _ + 1, target, [] => pure target
  | fuel + 1, target, k :: stack => do
    match target[k]? with
    | some t =>
      if t ≤ i then hoistClosure ds idx i fuel target stack
      else hoistClosure ds idx i fuel (target.insert k i) (← pushDeps k stack)
    | none => hoistClosure ds idx i fuel (target.insert k i) (← pushDeps k stack)
where
  /-- con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets —
  push record `k`'s own dependencies that lie after `i`. -/
  pushDeps (k : Nat) (stack : List Nat) : AM (List Nat) := do
    if h : k < ds.size then do
      let ns ← IDeclaration.usedConsts ds[k]
      pure (pushOne ns.toList stack)
    else pure stack
  /-- con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets —
  the inner `for n in ds[k]!.usedConsts` loop. -/
  pushOne : List NIdx → List Nat → List Nat
    | [], stack => stack
    | n :: ns, stack =>
      match idx[n]? with
      | some m => pushOne ns (if m > i then m :: stack else stack)
      | none => pushOne ns stack

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets — the
outer `for i in [0:ds.size]` loop: for every pinned-operation record, every
ground of its `natOpDeps` declared LATER pulls its own closure forward. -/
def hoistTargetsGo (ds : Array IDeclaration) (idx : Std.HashMap NIdx Nat)
    (target : Std.HashMap Nat Nat) (i : Nat) : AM (Std.HashMap Nat Nat) :=
  if h : i < ds.size then do
    match ← isNatOpRecord ds[i] with
    | none => hoistTargetsGo ds idx target (i + 1)
    | some c => do
      let deps ← natOpDeps c
      let target ← hoistDeps ds idx target i deps
      hoistTargetsGo ds idx target (i + 1)
  else pure target
  termination_by ds.size - i
where
  /-- con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets —
  the inner `for g in natOpDeps c` loop. -/
  hoistDeps (ds : Array IDeclaration) (idx : Std.HashMap NIdx Nat)
      (target : Std.HashMap Nat Nat) (i : Nat) : List NIdx →
      AM (Std.HashMap Nat Nat)
    | [] => pure target
    | g :: gs => do
      match idx[g]? with
      | some j =>
        if j > i then do
          let target ← hoistClosure ds idx i (ds.size * ds.size + 1) target [j]
          hoistDeps ds idx target i gs
        else hoistDeps ds idx target i gs
      | none => hoistDeps ds idx target i gs

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets — the
map from a record's index to the earliest pinned-operation index it must
precede.  Empty — and then the hoist is the identity — on every stream whose
ground precedes its operations. -/
def hoistTargets (ds : Array IDeclaration) : AM (Std.HashMap Nat Nat) :=
  hoistTargetsGo ds (nameIndex ds ∅ 0) ∅ 0

/-! ## The reorder -/

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist — a
moved record sorts at its target, just ahead of the operation record there
(key `(t, 0, k)` against the operation's `(t, 1, t)`); everything else keeps
its position (`(k, 1, k)`).  Moved records with the same target keep their
relative order, which is dependency order. -/
def hoistKey (target : Std.HashMap Nat Nat) (k : Nat) : Nat × Nat × Nat :=
  match target[k]? with
  | some t => (t, 0, k)
  | none => (k, 1, k)

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist — the
strict order on those keys. -/
def hoistLt (target : Std.HashMap Nat Nat) (a b : Nat) : Bool :=
  let ka := hoistKey target a
  let kb := hoistKey target b
  ka.1 < kb.1 ||
    (ka.1 == kb.1 && (ka.2.1 < kb.2.1 || (ka.2.1 == kb.2.1 && ka.2.2 < kb.2.2)))

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist — the
names of the records that moved, in index order. -/
def movedNames (ds : Array IDeclaration) (target : Std.HashMap Nat Nat)
    (acc : Array NIdx) (k : Nat) : Array NIdx :=
  if h : k < ds.size then
    movedNames ds target
      (if target.contains k then acc ++ ds[k].names.toArray else acc) (k + 1)
  else acc
  termination_by ds.size - k

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist — the
records in the sorted order.  `List.mergeSort` and not `Array.qsort` for
con-leche's own reason: the result is a PERMUTATION of the input, which is a
property the prepared list's shape lemma states.  The keys are pairwise
distinct (each carries its own index), so the order is the same one `qsort`
produced. -/
def reorder (ds : Array IDeclaration) (order : List Nat) : Array IDeclaration :=
  order.foldl (fun acc k => acc ++ (ds[k]?.toArray)) #[]

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:138-162 applyHoist — **the
reorder**: the sorted record array and the names of the records moved. -/
def applyHoist (ds : Array IDeclaration) (target : Std.HashMap Nat Nat) :
    Array IDeclaration × Array NIdx :=
  let order := (List.range ds.size).mergeSort (fun a b => !hoistLt target b a)
  (reorder ds order, movedNames ds target #[] 0)

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:164-169 hoistNatOpGround —
**the hoist.**  Returns the reordered records and the names of the records
moved (empty, and the array untouched, when no operation's ground is declared
after it). -/
def hoistNatOpGround (ds : Array IDeclaration) :
    AM (Array IDeclaration × Array NIdx) := do
  let target ← hoistTargets ds
  if target.isEmpty then pure (ds, #[]) else pure (applyHoist ds target)

end ConRon.Arena.Frontend

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
worklist's `continue` test: record `k` already precedes `i`. -/
def hoistDone (target : Std.HashMap Nat Nat) (k i : Nat) : Bool :=
  match target[k]? with
  | some t => decide (t ≤ i)
  | none => false

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets — the
worklist's pops that `continue`: the entries on top of the stack whose record
already precedes `i`, dropped.  Structural on the stack, so they cost no
fuel. -/
def hoistDropDone (target : Std.HashMap Nat Nat) (i : Nat) : List Nat → List Nat
  | [] => []
  | k :: stack => if hoistDone target k i then hoistDropDone target i stack else k :: stack

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets — the
worklist: the closure of `j` within the records after `i`, each reached
record marked as having to precede `i`.  con-leche's `while h : stack.size >
0` is a fuelled recursion over an explicit stack here.

**The fuel counts PROCESSED records, not pops** (task #97-P3-Frontend round
8).  A pop whose record already precedes `i` is `hoistDropDone`'s, structural
on the stack; only a pop that marks a record spends fuel.  A marked record is
done for the rest of the call (its target becomes `i`, and a target only ever
moves to the current `i`), so with every stack entry and every name-index value
below `ds.size` a call processes at most `ds.size` records, and the fuel
`ds.size` the caller passes is never exhausted: `hoistClosure_fuel_succ` below.
Fuel 0 on a record still to process is a `fail`, never a truncated answer
(round 7's finding 2: the fuel used to count pops, and one record pushes one
entry per reference, duplicates included, so pops are not bounded by the
number of records and `pure target` at fuel 0 cut the closure short). -/
def hoistClosure (ds : Array IDeclaration) (idx : Std.HashMap NIdx Nat) (i : Nat) :
    Nat → Std.HashMap Nat Nat → List Nat → AM (Std.HashMap Nat Nat)
  | fuel, target, stack =>
    match hoistDropDone target i stack with
    | [] => pure target
    | k :: stack =>
      match fuel with
      | 0 => fail (.internal "fuel exhausted: hoistClosure")
      | fuel + 1 => do
        hoistClosure ds idx i fuel (target.insert k i) (← pushDeps k stack)
where
  /-- con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets —
  push record `k`'s own dependencies that lie after `i`. -/
  pushDeps (k : Nat) (stack : List Nat) : AM (List Nat) := do
    if h : k < ds.size then do
      let ns ← IDeclaration.usedConsts ds[k]
      pure (pushOne k ns.toList stack)
    else pure stack
  /-- con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets —
  the inner `for n in ds[k]!.usedConsts` loop, with con-leche's (and the
  port's) `m != k`. -/
  pushOne (k : Nat) : List NIdx → List Nat → List Nat
    | [], stack => stack
    | n :: ns, stack =>
      match idx[n]? with
      | some m => pushOne k ns (if m > i && m != k then m :: stack else stack)
      | none => pushOne k ns stack

/-! ## The worklist's fuel is sufficient

The twin's fuel is a proof device, and the unfuelled port (`hoist_close`) and
con-leche's `while` must not be able to tell it is there.  The measure is the
number of records below `ds.size` not yet at `i` (`hoistPending`): every
fuelled step marks one of them, so a fuel at least that large is never
exhausted, and one more unit of fuel changes nothing.  The caller passes
`ds.size`, which bounds `hoistPending` outright. -/

/-- con-leche: none — the records below `n` not yet marked as preceding `i`:
the worklist's measure. -/
def hoistPending (n : Nat) (target : Std.HashMap Nat Nat) (i : Nat) : Nat :=
  (List.range n).countP (fun k => !hoistDone target k i)

/-- con-leche: none — a strictly smaller predicate, lower somewhere on the
list, counts strictly less. -/
theorem countP_lt_of_le {α : Type} {p q : α → Bool} {k : α} :
    ∀ {l : List α}, (∀ x ∈ l, q x = true → p x = true) → k ∈ l → p k = true →
      q k = false → l.countP q < l.countP p
  | [], _, hk, _, _ => by simp at hk
  | a :: l, hle, hk, hp, hq => by
    simp only [List.countP_cons]
    have hmono : l.countP q ≤ l.countP p :=
      List.countP_mono_left (fun x hx => hle x (List.mem_cons_of_mem a hx))
    rcases List.mem_cons.mp hk with rfl | hk'
    · simp [hp, hq]; omega
    · have := countP_lt_of_le (fun x hx => hle x (List.mem_cons_of_mem a hx)) hk' hp hq
      have ha := hle a List.mem_cons_self
      cases hqa : q a <;> cases hpa : p a <;> simp_all <;> omega

/-- con-leche: none — `hoistDropDone` drops a prefix. -/
theorem hoistDropDone_sub (target : Std.HashMap Nat Nat) (i : Nat) :
    ∀ {stack : List Nat} {x : Nat}, x ∈ hoistDropDone target i stack → x ∈ stack
  | [], _, h => by simp [hoistDropDone] at h
  | k :: stack, x, h => by
    unfold hoistDropDone at h
    split at h
    · exact List.mem_cons_of_mem k (hoistDropDone_sub target i h)
    · exact h

/-- con-leche: none — what `hoistDropDone` leaves on top is still to do. -/
theorem hoistDropDone_head (target : Std.HashMap Nat Nat) (i : Nat) :
    ∀ {stack rest : List Nat} {k : Nat}, hoistDropDone target i stack = k :: rest →
      hoistDone target k i = false
  | [], _, _, h => by simp [hoistDropDone] at h
  | k' :: stack, rest, k, h => by
    unfold hoistDropDone at h
    split at h
    · exact hoistDropDone_head target i h
    · rename_i hn
      obtain ⟨rfl, -⟩ := List.cons.inj h
      simpa using hn

/-- con-leche: none — marking a pending record below `n` lowers the measure. -/
theorem hoistPending_insert {n : Nat} {target : Std.HashMap Nat Nat} {i k : Nat}
    (hk : k < n) (hnd : hoistDone target k i = false) :
    hoistPending n (target.insert k i) i < hoistPending n target i := by
  unfold hoistPending
  refine countP_lt_of_le (k := k) ?_ (List.mem_range.mpr hk) (by simp [hnd]) ?_
  · intro x _ hx
    by_cases hxk : k = x
    · subst hxk; simp [hnd]
    · simpa [hoistDone, Std.HashMap.getElem?_insert, hxk] using hx
  · simp [hoistDone]

/-- con-leche: none — `pushOne` pushes name-index values only. -/
theorem hoistClosure_pushOne_lt {ds : Array IDeclaration} {idx : Std.HashMap NIdx Nat}
    {i : Nat} (hidx : ∀ (n : NIdx) m, idx[n]? = some m → m < ds.size) (k : Nat) :
    ∀ (ns : List NIdx) (stack : List Nat), (∀ x ∈ stack, x < ds.size) →
      ∀ x ∈ hoistClosure.pushOne idx i k ns stack, x < ds.size
  | [], stack, hs => by simpa [hoistClosure.pushOne] using hs
  | n :: ns, stack, hs => by
    unfold hoistClosure.pushOne
    split
    · rename_i m hm
      refine hoistClosure_pushOne_lt hidx k ns _ ?_
      split
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hidx n x hm
        · exact hs x hx
      · exact hs
    · exact hoistClosure_pushOne_lt hidx k ns stack hs

/-- con-leche: ConLeche/Frontend/NatOpGround.lean:106-136 hoistTargets —
**the twin's fuel is sufficient**: with every stack entry and every name-index
value below `ds.size`, a fuel at least the pending count answers exactly what
one more unit of fuel answers.  So the fuel-0 `fail` is unreachable from the
caller's `ds.size`, and the fuelled worklist is the unfuelled loop. -/
theorem hoistClosure_fuel_succ {ds : Array IDeclaration} {idx : Std.HashMap NIdx Nat}
    {i : Nat} (hidx : ∀ (n : NIdx) m, idx[n]? = some m → m < ds.size) :
    ∀ (fuel : Nat) (target : Std.HashMap Nat Nat) (stack : List Nat),
      (∀ x ∈ stack, x < ds.size) → hoistPending ds.size target i ≤ fuel →
      hoistClosure ds idx i (fuel + 1) target stack
        = hoistClosure ds idx i fuel target stack := by
  intro fuel
  induction fuel with
  | zero =>
    intro target stack hs hp
    conv => lhs; rw [hoistClosure]
    conv => rhs; rw [hoistClosure]
    split
    · rfl
    · rename_i k rest hdrop
      have hk := hs k (hoistDropDone_sub target i (by rw [hdrop]; exact List.mem_cons_self))
      have := hoistPending_insert hk (hoistDropDone_head target i hdrop)
      omega
  | succ f ih =>
    intro target stack hs hp
    conv => lhs; rw [hoistClosure]
    conv => rhs; rw [hoistClosure]
    split
    · rfl
    · rename_i k rest hdrop
      have hk := hs k (hoistDropDone_sub target i (by rw [hdrop]; exact List.mem_cons_self))
      have hlt := hoistPending_insert hk (hoistDropDone_head target i hdrop)
      have hrest : ∀ x ∈ rest, x < ds.size := fun x hx =>
        hs x (hoistDropDone_sub target i (by rw [hdrop]; exact List.mem_cons_of_mem k hx))
      simp only []
      unfold hoistClosure.pushDeps
      by_cases hkd : k < ds.size
      · simp only [dif_pos hkd, bind_assoc, pure_bind]
        congr 1; funext ns
        exact ih _ _ (hoistClosure_pushOne_lt hidx k _ rest hrest) (by omega)
      · simp only [dif_neg hkd, pure_bind]
        exact ih _ _ hrest (by omega)

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
          let target ← hoistClosure ds idx i ds.size target [j]
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

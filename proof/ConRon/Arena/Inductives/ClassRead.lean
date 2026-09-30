/-
# `ConRon.Arena.Inductives.ClassRead` — the generated recursor stage's PRE-PASS
(DESIGN.md §8, task #105)

`ConLeche/Kernel/Inductives/ClassRead.lean` over handles (UNVERIFIED in
con-leche's sense: soundness never depends on it): read the classes (one per
motive), the prefix layout (motives, minor premises and their inductive
hypotheses) and every recursor's class off the stream's raw recursor types,
syntactically, checking nothing.  The Rust twin is
`arena::inductives::class_read`.

**The deviations** (the Rust's, item for item):

* **`classRead`'s `nPc : Name → Nat` is specialised** to its one
  instantiation, `classNPcOf p fe`: the twin takes the block's shape and the
  formers' environment.
* **`classNPcOf` lives HERE, not in `GenRec`** where con-leche (and the Rust,
  `arena::inductives::gen_rec::class_n_pc_of`) put it: `GenRec` imports this
  module and Lean modules cannot be cyclic, so the one function the pre-pass
  calls from there is placed ahead of its reader.
* **`openPisAtFvars` is `openPisAtFvarsF`**, the one-pass form con-leche
  swaps in by `@[csimp]`.
* **A pure reading computed twice is computed once** (`classReadMinor`'s
  `fvarTypeD.piResult` per field).
* **`ClassRead.classes` and `ClassRead.motiveSlot` take the slot list**, as
  the Rust does (its callers pass `&g.slots`), not the record.
* **The `.fvar p _ := e.getAppFn` reading is one function, `fvarHead`**, the
  Rust's `fvar_head`, since it is spelled four times; the per-slot reading of
  `classReadSlots` is `classReadSlot` and `recs.mapM` of `classRead` is
  `classReadRecCls`, the Rust's own split.
-/
import ConRon.Arena.Inductives.BlockParts

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:37-43 ClassKey
A class: an inductive at the levels `lvls` (interned) and the parameters
`ds`. -/
structure ClassKey where
  ind : NIdx
  lvls : LsIdx
  ds : List EIdx
  deriving Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:45-53 ClassSlot
One binder of the recursors' shared prefix after the parameters: a motive (its
class), or a minor premise (the class ordinal it concludes at, the constructor
it builds, its inductive hypotheses `(field, class)`). -/
inductive ClassSlot where
  /-- a motive; its class -/
  | motive (key : ClassKey)
  /-- a minor premise -/
  | minor (cls : Nat) (ctor : NIdx) (ihs : List (Nat × Nat))
  deriving Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:55-61 ClassRead
What the pre-pass read: the prefix after the parameters, and per recursor the
class its conclusion eliminates. -/
structure ClassRead where
  slots : List ClassSlot
  recCls : List Nat
  deriving Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:65-67 ClassRead.classes
The classes (the motives' keys), in prefix order.  Takes the slot list (module
note). -/
def ClassRead.classes (slots : List ClassSlot) : List ClassKey :=
  slots.filterMap fun
    | .motive k => some k
    | .minor _ _ _ => none

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:69-73 ClassRead.motiveSlot
The prefix position (after the parameters) of class `c`'s motive.  Takes the
slot list (module note). -/
def ClassRead.motiveSlot (slots : List ClassSlot) (c : Nat) : Option Nat :=
  let ms := (List.range slots.length).filter fun s =>
    match slots[s]? with
    | some (.motive _) => true
    | _ => false
  ms[c]?

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:77-80 classOfMotiveVar
The motive ordinal of the prefix variable `fvar p` (`nP ≤ p`), when that binder
is a motive. -/
def classOfMotiveVar (nP : Nat) (motPos : List Nat) (p : Nat) : Option Nat :=
  if nP ≤ p then motPos.findIdx? (· == p - nP) else none

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:82-105 classReadMinor
The `fvar` head of an application, its index (`none` at any other head) —
the cited `.fvar p _ := e.getAppFn` (module note). -/
def fvarHead (e : EIdx) : AM (Option Nat) := do
  let hd ← getAppFn coreWalkFuel e
  if hd.tag == ETag.fvar then
    match ← viewFVarIdx hd with
    | none => failDanglingE
    | some p => pure (some p)
  else pure none

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:82-105 classReadMinor
**Read one minor premise's type `dom`**, opened at depth `d`: its conclusion is
a motive (the class), its last argument a constructor application (the
constructor), and its inductive hypotheses — every opened binder whose type's
conclusion is a motive applied to a field `f` of the minor (`d ≤ f`), giving
`(f - d, t)` (the Rust's `class_read_ih`/`class_read_ihs`, a `filterMapM`). -/
def classReadMinor (nP : Nat) (motPos : List Nat) (d : Nat) (dom : EIdx) :
    AM (Option ClassSlot) := do
  let (bs, _) ← piBinders coreWalkFuel dom
  match ← openPisAtFvarsF bs.length dom d with
  | none => pure none
  | some (fvs, concl) =>
    match ← fvarHead concl with
    | none => pure none
    | some p =>
      match classOfMotiveVar nP motPos p with
      | none => pure none
      | some c => do
        let args ← getAppArgs coreWalkFuel concl
        match args.getLast? with
        | none => pure none
        | some last => do
          let hd ← getAppFn coreWalkFuel last
          if hd.tag == ETag.const then
            match ← viewConst hd with
            | none => failDanglingE
            | some (cn, _) => do
              let ihs ← fvs.filterMapM fun x => do
                let ty ← fvarTypeD x
                let r ← piResult coreWalkFuel ty
                match ← fvarHead r with
                | none => pure none
                | some p2 =>
                  match classOfMotiveVar nP motPos p2 with
                  | none => pure none
                  | some t => do
                    let rargs ← getAppArgs coreWalkFuel r
                    match rargs.getLast? with
                    | none => pure none
                    | some a =>
                      match ← fvarHead a with
                      | none => pure none
                      | some f => pure (if d ≤ f then some (f - d, t) else none)
              pure (some (.minor c cn ihs))
          else pure none

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:486-492 classNPcOf
An inductive's parameter count as the pre-pass reads it: the block's at a
member, the stored `IndCaps`' otherwise (`0` at no inductive).  Placed here,
not in `GenRec` (module note). -/
def classNPcOf (p : BlockShape) (fe : IFEnv) (i : NIdx) : Nat :=
  if p.memberNames.contains i then p.nP
  else
    match fe.find? i with
    | some (.indInfo _ caps) => caps.nparams
    | _ => 0

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:107-124 classReadSlots
One prefix binder's domain read as a motive (its telescope ends in a sort: the
class is its last binder's domain, at the class's parameter count) or as a
minor premise. -/
def classReadSlot (p : BlockShape) (fe : IFEnv) (np : Nat) (motPos : List Nat) (d : Nat)
    (dom : EIdx) : AM (Option ClassSlot) := do
  let r ← piResult coreWalkFuel dom
  if r.tag == ETag.sort then do
    let (bs, _) ← piBinders coreWalkFuel dom
    match bs.getLast? with
    | none => pure none
    | some (mdom, _) => do
      let hd ← getAppFn coreWalkFuel mdom
      if hd.tag == ETag.const then
        match ← viewConst hd with
        | none => failDanglingE
        | some (iName, us) => do
          let args ← getAppArgs coreWalkFuel mdom
          let n := classNPcOf p fe iName
          pure (some (.motive ⟨iName, us, args.take n⟩))
      else pure none
  else classReadMinor np motPos d dom

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:107-124 classReadSlots
Read the prefix binders `n` of a recursor type opened at the parameters (`e`,
depth `d`), classifying each as a motive or a minor premise; each binder
opened at `d` before the next is read.  `none` off the shape.  `nPc` is
`classNPcOf p fe` (module note). -/
def classReadSlots (p : BlockShape) (fe : IFEnv) (np : Nat) :
    Nat → List Nat → Nat → EIdx → AM (Option (List ClassSlot))
  | 0, _, _, _ => pure (some [])
  | n + 1, motPos, d, e => do
    if e.tag == ETag.forallE then
      match ← viewBind e with
      | none => failDanglingE
      | some (dom, body, _) =>
        match ← classReadSlot p fe np motPos d dom with
        | none => pure none
        | some slot => do
          let motPos' := match slot with
            | .motive _ => motPos ++ [d - np]
            | .minor _ _ _ => motPos
          let fv ← internFVarE d dom
          let b2 ← instantiate1Fast coreWalkFuel body fv 0
          match ← classReadSlots p fe np n motPos' (d + 1) b2 with
          | none => pure none
          | some rest => pure (some (slot :: rest))
    else pure none

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:126-140 classRead
`recs.mapM fun rc => …` — every recursor's class off its conclusion
`motive_c ı⃗ t`; `none` off the shape. -/
def classReadRecCls (nP : Nat) (motPos : List Nat) : List RecShape → AM (Option (List Nat))
  | [] => pure (some [])
  | rc :: rest => do
    match ← openPisAtFvarsF (rc.mI + 1) rc.cvR.type 0 with
    | none => pure none
    | some (_, concl) =>
      match ← fvarHead concl with
      | none => pure none
      | some p =>
        match classOfMotiveVar nP motPos p with
        | none => pure none
        | some c =>
          match ← classReadRecCls nP motPos rest with
          | none => pure none
          | some cs => pure (some (c :: cs))

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:126-140 classRead
**The pre-pass**: the prefix layout off the FIRST recursor's type, and every
recursor's class off its conclusion.  `none` when the family is not of the
generated shape.  `nPc` is `classNPcOf p fe` (module note). -/
def classRead (p : BlockShape) (fe : IFEnv) (nP : Nat) (recs : List RecShape) :
    AM (Option ClassRead) := do
  match recs with
  | [] => pure none
  | rc0 :: _ =>
    match ← openPisAtFvarsF nP rc0.cvR.type 0 with
    | none => pure none
    | some (_, body) =>
      match ← classReadSlots p fe nP (rc0.rP - nP) [] nP body with
      | none => pure none
      | some slots =>
        let motPos := (List.range slots.length).filter fun s =>
          match slots[s]? with
          | some (.motive _) => true
          | _ => false
        match ← classReadRecCls nP motPos recs with
        | none => pure none
        | some recCls => pure (some ⟨slots, recCls⟩)

end ConRon.Arena

/-
# `ConRon.Arena.Frontend.Olean.Emit` — the merged constants in lean4export's order (task #142)

The twin of `olean/emit.rs`.  The record stream is upstream's own syntax
(`Scan/Types.lean`'s `DeclRec`).  A `Work` item names constants instead of holding
them, as in the Rust: the merge does not change during the walk.  The walk takes fuel
(`Closure.lean`'s note).
-/
module

public import ConRon.Arena.Frontend.Olean.Merge

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend
open ConLeche.Frontend.Olean (CEntryF CKindF closureFuel)

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:23-28 Work
One step of the emission walk. -/
inductive Work where
  | visit (n : NIdx)
  | one (n : NIdx)
  | quot (cs : List NIdx)
  | block (tys ctors recs : List NIdx)

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:30-36 Emit
The emitter's output: the record stream in the stream reader's syntax. -/
structure Emit where
  visited : Std.HashSet NIdx := {}
  names : Array NIdx := #[]
  exprs : Array EIdx := #[]
  out : Array DeclRec := #[]

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:42-45 Emit.name -/
def Emit.name (st : Emit) (n : NIdx) : Emit × Nat :=
  let { visited, names, exprs, out } := st
  let i := names.size
  ({ visited, names := names.push n, exprs, out }, i)

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:47-50 Emit.expr -/
def Emit.expr (st : Emit) (e : EIdx) : Emit × Nat :=
  let { visited, names, exprs, out } := st
  let i := exprs.size
  ({ visited, names, exprs := exprs.push e, out }, i)

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:52-54 Emit.push -/
def Emit.push (st : Emit) (d : DeclRec) : Emit :=
  let { visited, names, exprs, out } := st
  { visited, names, exprs, out := out.push d }

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:56-58 Emit.mark -/
def Emit.mark (st : Emit) (n : NIdx) : Emit :=
  let { visited, names, exprs, out } := st
  { visited := visited.insert n, names, exprs, out }

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:67-70 Emit.names' -/
def Emit.names' (st : Emit) (ns : List NIdx) : Emit × List Nat :=
  let (st, acc) := ns.foldl (fun (st, acc) p =>
    let (st, i) := st.name p; (st, acc.push i)) (st, #[])
  (st, acc.toList)

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:60-65 Emit.cv -/
def Emit.cv (st : Emit) (c : CEntry) : Emit × CVRec :=
  let (st, n) := st.name c.c.name
  let (st, lps) := st.names' c.c.levelParams
  let (st, t) := st.expr c.c.type
  (st, ⟨n, lps, t⟩)

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:72-84 Emit.one
**One constant's record.** -/
def Emit.one (st : Emit) (c : CEntry) : Emit :=
  let (st, cv) := st.cv c
  match c.c.kind with
  | .ax u => st.push (.ax cv u)
  | .defn v h s => let (st, i) := st.expr v; st.push (.defn cv i h s)
  | .thm v _ => let (st, i) := st.expr v; st.push (.thm cv i)
  | .opaq v u => let (st, i) := st.expr v; st.push (.opaq cv i u)
  | .quot k => st.push (.quot cv k)
  | _ => st

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:86-95 Emit.tyStep
One inductive type of a block's record. -/
def Emit.tyStep (x : Emit × Array IndTypeRec) (c : CEntry) : Emit × Array IndTypeRec :=
  let (st, acc) := x
  match c.c.kind with
  | .induct np ni _ cs nn ir iu irf =>
    let (st, cv) := st.cv c
    let (st, cs) := st.names' cs
    (st, acc.push { cv, ctors := cs, isRec := ir, isReflexive := irf, isUnsafe := iu,
                    numIndices := ni, numNested := nn, numParams := np : IndTypeRec })
  | _ => (st, acc)

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:97-106 Emit.ctorStep
One constructor of a block's record. -/
def Emit.ctorStep (x : Emit × Array IndCtorRec) (c : CEntry) : Emit × Array IndCtorRec :=
  let (st, acc) := x
  match c.c.kind with
  | .ctor ind cidx np nf iu =>
    let (st, cv) := st.cv c
    let (st, ii) := st.name ind
    (st, acc.push { cv, isUnsafe := iu, numFields := nf, numParams := np,
                    cidx := some cidx, induct := some ii : IndCtorRec })
  | _ => (st, acc)

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:108-114 Emit.ruleStep
One rule of a recursor's record. -/
def Emit.ruleStep (x : Emit × Array RuleRec) (r : NIdx × Nat × EIdx) : Emit × Array RuleRec :=
  let (st, acc) := x
  let (cn, nf, rhs) := r
  let (st, ci) := st.name cn
  let (st, ri) := st.expr rhs
  (st, acc.push ({ ctor := ci, nfields := nf, rhs := ri } : RuleRec))

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:116-125 Emit.recStep
One recursor of a block's record. -/
def Emit.recStep (x : Emit × Array IndRecRec) (c : CEntry) : Emit × Array IndRecRec :=
  let (st, acc) := x
  match c.c.kind with
  | .recur _ np ni nmo nmi rules k iu =>
    let (st, cv) := st.cv c
    let (st, rr) := rules.foldl Emit.ruleStep (st, #[])
    (st, acc.push { cv, isUnsafe := iu, k, numIndices := ni, numMinors := nmi,
                    numMotives := nmo, numParams := np, rules := rr.toList : IndRecRec })
  | _ => (st, acc)

/-- con-leche: none — `mg.get` over a list of names, the constants stored -/
def entriesOf (mg : Merged) (ns : List NIdx) : List CEntry := ns.filterMap mg.get

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:127-132 Emit.block
**An inductive block's record**: lean4export's `inductive` object. -/
def Emit.block (st : Emit) (mg : Merged) (tys ctors recs : List NIdx) : Emit :=
  let (st, ts) := (entriesOf mg tys).foldl Emit.tyStep (st, #[])
  let (st, cts) := (entriesOf mg ctors).foldl Emit.ctorStep (st, #[])
  let (st, rs) := (entriesOf mg recs).foldl Emit.recStep (st, #[])
  st.push (.ind ts.toList cts.toList rs.toList)

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:265-266 blockTys
The constants of an inductive block's members: those of `all` stored. -/
def blockTys (mg : Merged) (all : List NIdx) : List NIdx := all.filter fun n => mg.map.contains n

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:268-272 blockCtors
The constructors of a block's members. -/
def blockCtors (mg : Merged) (tys : List NIdx) : List NIdx :=
  tys.flatMap fun t => match mg.get t with
    | some c => match c.c.kind with
      | .induct _ _ _ cs _ _ _ _ => blockTys mg cs
      | _ => []
    | none => []

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:274-276 blockRecs
The recursors of a block. -/
def blockRecs (mg : Merged) (recMap : Std.HashMap NIdx (Array NIdx)) (n : NIdx) : List NIdx :=
  blockTys mg ((recMap[n]?).getD #[]).toList

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:278-280 quotNames
The quotient package's names. -/
def quotNames (pk : OleanPins) : List NIdx := [pk.nQuot, pk.nQuotMk, pk.nQuotLift, pk.nQuotInd]

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:282-283 quotConstants
The quotient package's constants. -/
def quotConstants (pk : OleanPins) (mg : Merged) : List NIdx := blockTys mg (quotNames pk)

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:285-286 Work.usesOf
Visits of what some constants mention. -/
def Work.usesOf (mg : Merged) (cs : List NIdx) : List Work :=
  (entriesOf mg cs).flatMap fun c => c.uses.toList.map Work.visit

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:288-289 Work.visits
Visits of some names. -/
def Work.visits (ns : List NIdx) : List Work := ns.map Work.visit

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:291-292 Emit.ones
Some constants' records. -/
def Emit.ones (st : Emit) (mg : Merged) (cs : List NIdx) : Emit := (entriesOf mg cs).foldl Emit.one st

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:294-338 emitLoop
**The emission walk** (lean4export's `dumpConstant`, iterative): `visit n` emits `n`'s
record after its dependencies. -/
def emitLoop (pk : OleanPins) (mg : Merged) (recMap : Std.HashMap NIdx (Array NIdx)) :
    Nat → List Work → Emit → AM Emit
  | _, [], st => pure st
  | 0, _ :: _, _ => outOfFuel
  | fuel + 1, .one n :: rest, st => emitLoop pk mg recMap fuel rest (st.ones mg [n])
  | fuel + 1, .quot cs :: rest, st => emitLoop pk mg recMap fuel rest (st.ones mg cs)
  | fuel + 1, .block ts cs rs :: rest, st => emitLoop pk mg recMap fuel rest (st.block mg ts cs rs)
  | fuel + 1, .visit n :: rest, st =>
    if st.visited.contains n then emitLoop pk mg recMap fuel rest st else
    match mg.get n with
    | none => emitLoop pk mg recMap fuel rest st
    | some c =>
      if c.skipped then emitLoop pk mg recMap fuel rest st else
      let st := st.mark n
      match c.c.kind with
      | .ax _ | .defn .. | .thm .. | .opaq .. =>
        emitLoop pk mg recMap fuel (Work.usesOf mg [n] ++ Work.one n :: rest) st
      | .quot _ =>
        let qs := quotConstants pk mg
        let st := qs.foldl Emit.mark st
        emitLoop pk mg recMap fuel (Work.visit pk.nEq :: Work.quot qs :: rest) st
      | .ctor ind .. => emitLoop pk mg recMap fuel (Work.visit ind :: rest) st
      | .recur all .. => emitLoop pk mg recMap fuel (Work.visits all ++ rest) st
      | .induct _ _ all _ _ _ _ _ =>
        let tys := blockTys mg all
        let ctors := blockCtors mg tys
        let recs := blockRecs mg recMap n
        let st := (tys ++ ctors ++ recs).foldl Emit.mark st
        emitLoop pk mg recMap fuel (Work.usesOf mg (tys ++ ctors ++ recs) ++ Work.block tys ctors recs :: rest) st

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:340-345 recMapAdd
A recursor under one member of its block. -/
def recMapAdd (n : NIdx) (m : Std.HashMap NIdx (Array NIdx)) (i : NIdx) :
    Std.HashMap NIdx (Array NIdx) :=
  m.alter i fun
    | none => some #[n]
    | some a => some (if a.contains n then a else a.push n)

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:347-352 recMapStep
A constant's name under each member of its block, if it is a recursor. -/
def recMapStep (mg : Merged) (m : Std.HashMap NIdx (Array NIdx)) (n : NIdx) :
    Std.HashMap NIdx (Array NIdx) :=
  match (mg.get n).map (·.c.kind) with
  | some (CKindF.recur all ..) => all.foldl (recMapAdd n) m
  | _ => m

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:354-355 recMapOf
The recursors of every member of a block. -/
def recMapOf (mg : Merged) : Std.HashMap NIdx (Array NIdx) := mg.order.foldl (recMapStep mg) {}

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:357-359 emitAll
**The record stream of the merged closure**, from the given constants. -/
def emitAll (pk : OleanPins) (mg : Merged) (roots : Array NIdx) : AM Emit :=
  emitLoop pk mg (recMapOf mg) closureFuel (roots.toList.map .visit) {}

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:363-376 blockMemberOk
A block member `x` of the inductive type `n`, whose block is `all`. -/
def blockMemberOk (mg : Merged) (n : NIdx) (all : List NIdx) (sk : Bool) (x : NIdx) : AM Unit := do
  let bad (what : String) : AM Unit := do
    fail (.internal s!"the inductive data of {← readName n}: its block member {← readName x} {what}")
  match mg.get x with
  | none => bad "is not stored"
  | some m =>
    match m.c.kind with
    | .induct _ _ all' .. =>
      if all' == all then
        if m.skipped == sk then pure () else bad "is safe or unsafe where the type is not"
      else bad "names another block"
    | _ => bad "is not an inductive type"

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:378-390 blockCtorOk
A listed constructor `x` of the inductive type `n`. -/
def blockCtorOk (mg : Merged) (n : NIdx) (sk : Bool) (x : NIdx) : AM Unit := do
  let bad (what : String) : AM Unit := do
    fail (.internal s!"the inductive data of {← readName n}: its constructor {← readName x} {what}")
  match mg.get x with
  | none => bad "is not stored"
  | some m =>
    match m.c.kind with
    | .ctor ind .. =>
      if ind == n then
        if m.skipped == sk then pure () else bad "is safe or unsafe where the type is not"
      else bad "names another type"
    | _ => bad "is not a constructor"

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:392-438 blockStep
**One stored constant's part in its block.** -/
def blockStep (pk : OleanPins) (mg : Merged) (n : NIdx) : AM Unit := do
  let bad (what : String) : AM Unit := do
    fail (.internal s!"the inductive data of {← readName n}: {what}")
  match mg.get n with
  | none => pure ()
  | some c =>
    match c.c.kind with
    | .induct _ _ all cs .. =>
      if all.contains n then
        all.forM (blockMemberOk mg n all c.skipped)
        cs.forM (blockCtorOk mg n c.skipped)
      else bad "its block does not list it"
    | .ctor ind .. =>
      match mg.get ind with
      | none => bad s!"its type {← readName ind} is not stored"
      | some t =>
        match t.c.kind with
        | .induct _ _ _ cs .. =>
          if cs.contains n then pure () else bad s!"its type {← readName ind} does not list it"
        | _ => bad s!"its type {← readName ind} is not an inductive type"
    | .recur all .. =>
      match all with
      | [] => bad "the recursor names no block"
      | t :: _ =>
        match mg.get t with
        | none => bad s!"the recursor's block member {← readName t} is not stored"
        | some m =>
          match m.c.kind with
          | .induct _ _ all' .. =>
            if all' == all then
              if m.skipped == c.skipped then pure ()
              else bad s!"the recursor is safe or unsafe where {← readName t} is not"
            else bad s!"the recursor's block is not {← readName t}'s"
          | _ => bad s!"the recursor's block member {← readName t} is not an inductive type"
    | .quot _ =>
      if (quotNames pk).contains n then
        if (entriesOf mg (quotConstants pk mg)).all (·.c.kind.tag == 4) then pure ()
        else bad "the quotient package holds a constant of another kind"
      else bad "a quotient constant outside the quotient package"
    | _ => pure ()

/-- con-leche: ConLeche/Frontend/Olean/Emit.lean:440-441 blocksOk
`blockStep` for every stored constant, before the walk. -/
def blocksOk (pk : OleanPins) (mg : Merged) : AM Unit := mg.order.toList.forM (blockStep pk mg)

end ConRon.Arena.Frontend.Olean

/-
# `ConRon.Arena.Frontend.Olean.Spec` — what the reader computes (task #142)

The twin of `crates/con-ron-core/src/frontend/olean/spec.rs`, over
`ConLeche/Frontend/Olean/Spec.lean`.

**What is imported and not twinned.**  Everything of upstream's reader that holds
no `Name`, `Level` or `Expr` is byte reading or plain data, so a twin would be a
copy, the reason `Scan/Fast.lean` is imported (`Arena/Frontend/ExportC.lean`'s
note):

* all of `Olean/Region.lean`, which reads bytes;
* of `Olean/Spec.lean`: `CKindF`, `CEntryF`, their `mapM`s, `ImportF`, `natF`,
  `nameList`, `hintsSkel`, `ruleSkel`, `kindSkel`, `constSkel`, `importSkel`,
  `ModSkel`, `moduleSkel`: the skeletons hold pointers and numbers.

What is twinned is what holds a value: the node functions, here **interning**, as
the stream parser's entries do.  A read fails as upstream's does (`none`) or with
the store's capacity decline (`AM`'s `fail`), so a read is `AM (Option α)`.

`sub : (c : Nat) → c < g → Option α` is the record `Sub`, one per memo; the
proof `c < g` has no use here, since a memo read does not recurse.  `nameAt`
recurses, so it spells the `Name` node out, as the Rust does.
-/
module

public import ConLeche.Frontend.Olean.Spec
public import ConRon.Arena.Frontend.ExportC

@[expose] public section

namespace ConRon.Arena.Frontend.Olean

open ConLeche
open ConLeche.Frontend
open ConLeche.Frontend.Olean (Region CEntryF CKindF ImportF ModSkel)

/-- con-leche: none — con-leche's `CheckError` in the arena's, which has one
constructor more -/
def toArenaError : ConLeche.CheckError → CheckError
  | .notImplemented w => .notImplemented w
  | .invalid w => .invalid w
  | .internal w => .internal w

/-- con-leche: none — the handles the reader needs in advance: the nullary
constructors and the names it spells (`mkN`). -/
structure OleanPins where
  anon : NIdx
  zero : LIdx
  nil : LsIdx
  nNat : NIdx
  nCharOfNat : NIdx
  nStringOfList : NIdx
  nEq : NIdx
  nQuot : NIdx
  nQuotMk : NIdx
  nQuotLift : NIdx
  nQuotInd : NIdx
  deriving Inhabited

/-- con-leche: ConLeche/Frontend/Olean/Lazy.lean:42-43 mkN
The reader's known handles, interned once, before any file is read. -/
def oleanPins : AM OleanPins := do
  let anon ← internNNode .anonymous
  let zero ← internLNode .zero
  let nil ← internLsNode []
  let nNat ← internNNode (.str anon "Nat")
  let nChar ← internNNode (.str anon "Char")
  let nCharOfNat ← internNNode (.str nChar "ofNat")
  let nString ← internNNode (.str anon "String")
  let nStringOfList ← internNNode (.str nString "ofList")
  let nEq ← internNNode (.str anon "Eq")
  let nQuot ← internNNode (.str anon "Quot")
  let nQuotMk ← internNNode (.str nQuot "mk")
  let nQuotLift ← internNNode (.str nQuot "lift")
  let nQuotInd ← internNNode (.str nQuot "ind")
  pure { anon, zero, nil, nNat, nCharOfNat, nStringOfList, nEq, nQuot, nQuotMk, nQuotLift, nQuotInd }

/-- con-leche: none — the Rust's saturation point: a `Nat` of the file that does
not fit a machine word, or is its largest value, is the `native` decline where it
goes on to be used. -/
def wordMax : Nat := 2 ^ 64 - 1

/-- con-leche: none — a `Nat` where a term is built from it: `wordMax` and up is
the `native` decline (the Rust's `spec::nat_word`). -/
@[inline] def natWord (k : Nat) : AM Nat :=
  if wordMax ≤ k then fail (.native "a number in an .olean file does not fit a machine word")
  else pure k

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:111-125 nameNode
The `sub` arguments of the node functions: a value of a recursive type at a
location below the object being read. -/
structure Sub where
  name : Nat → Option NIdx
  level : Nat → Option LIdx
  levels : Nat → Option LsIdx
  expr : Nat → Option EIdx

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:73-78 Region.nameIn -/
@[inline] def nameIn (pk : OleanPins) (r : Region) (g : Nat) (v : UInt64) (sub : Sub) :
    Option NIdx :=
  if v == 1 then some pk.anon
  else match r.down g v with
    | some c => sub.name c
    | none => none

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:80-85 Region.levelIn -/
@[inline] def levelIn (pk : OleanPins) (r : Region) (g : Nat) (v : UInt64) (sub : Sub) :
    Option LIdx :=
  if v == 1 then some pk.zero
  else match r.down g v with
    | some c => sub.level c
    | none => none

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:87-92 Region.levelsIn -/
@[inline] def levelsIn (pk : OleanPins) (r : Region) (g : Nat) (v : UInt64) (sub : Sub) :
    Option LsIdx :=
  if v == 1 then some pk.nil
  else match r.down g v with
    | some c => sub.levels c
    | none => none

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:94-98 Region.exprIn -/
@[inline] def exprIn (r : Region) (g : Nat) (v : UInt64) (sub : Sub) : Option EIdx :=
  match r.down g v with
  | some c => sub.expr c
  | none => none

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:111-125 nameNode
The two arms of a `Name` node after its parent: the component, and the intern. -/
def nameTail (r : Region) (g : Nat) (t : Nat) (p : NIdx) : AM (Option NIdx) := do
  if t == 1 then
    match r.strP g (r.fld g 1) with
    | none => pure none
    | some s => pure (some (← internNNode (.str p s)))
  else
    match r.natP g (r.fld g 1) with
    | none => pure none
    | some i => pure (some (← internNNode (.num p (← natWord i))))

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:111-125 nameNode
**A `Name` object** at `g`, interned. -/
def nameNode (pk : OleanPins) (r : Region) (g : Nat) (sub : Sub) : AM (Option NIdx) := do
  if r.fits g then
    let t := r.tag g
    if (t == 1 || t == 2) && r.nobjs g == 2 then
      match nameIn pk r g (r.fld g 0) sub with
      | none => pure none
      | some p => nameTail r g t p
    else pure none
  else pure none

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:127-148 levelNode
**A `Level` object** at `g`, interned (`mvar` is malformed input). -/
def levelNode (pk : OleanPins) (r : Region) (g : Nat) (sub : Sub) : AM (Option LIdx) := do
  if r.fits g then
    match r.tag g, r.nobjs g with
    | 0, 0 => pure (some pk.zero)
    | 1, 1 =>
      match levelIn pk r g (r.fld g 0) sub with
      | none => pure none
      | some u => pure (some (← internLNode (.succ u)))
    | 2, 2 =>
      match levelIn pk r g (r.fld g 0) sub, levelIn pk r g (r.fld g 1) sub with
      | some u, some v => pure (some (← internLNode (.max u v)))
      | _, _ => pure none
    | 3, 2 =>
      match levelIn pk r g (r.fld g 0) sub, levelIn pk r g (r.fld g 1) sub with
      | some u, some v => pure (some (← internLNode (.imax u v)))
      | _, _ => pure none
    | 4, 1 =>
      match nameIn pk r g (r.fld g 0) sub with
      | none => pure none
      | some n => pure (some (← internLNode (.param n)))
    | _, _ => pure none
  else pure none

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:150-160 levelsNode
`u :: us` over handles. -/
def levelsCons (u : LIdx) (us : LsIdx) : AM (Option LsIdx) := do
  let rest ← viewLs us
  pure (some (← internLsNode (u :: rest)))

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:150-160 levelsNode
**A `List Level` cell** at `g`: `u :: us` as one interned list. -/
def levelsNode (pk : OleanPins) (r : Region) (g : Nat) (sub : Sub) : AM (Option LsIdx) := do
  if r.fits g then
    if r.tag g == 1 && r.nobjs g == 2 then
      match levelIn pk r g (r.fld g 0) sub, levelsIn pk r g (r.fld g 1) sub with
      | some u, some us => levelsCons u us
      | _, _ => pure none
    else pure none
  else pure none

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:100-107 Region.litP
**A `Literal`** the object at `g` holds, as con-leche's: a literal is a value of
the store. -/
def litP (r : Region) (g : Nat) (v : UInt64) : Option Literal := r.litP g v

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:162-206 exprNode
**An `Expr` object** at `g`, interned.  Metadata is transparent: an `mdata` node
IS its body. -/
def exprNode (pk : OleanPins) (r : Region) (g : Nat) (sub : Sub) : AM (Option EIdx) := do
  if r.fits g then
    match r.tag g, r.nobjs g with
    | 0, 1 =>
      match r.natP g (r.fld g 0) with
      | none => pure none
      | some i => pure (some (← internE (.bvar (← natWord i))))
    | 3, 1 =>
      match levelIn pk r g (r.fld g 0) sub with
      | none => pure none
      | some u => pure (some (← internE (.sort u)))
    | 4, 2 =>
      match nameIn pk r g (r.fld g 0) sub, levelsIn pk r g (r.fld g 1) sub with
      | some n, some us => pure (some (← internE (.const n us)))
      | _, _ => pure none
    | 5, 2 =>
      match exprIn r g (r.fld g 0) sub, exprIn r g (r.fld g 1) sub with
      | some f, some a => pure (some (← internE (.app f a)))
      | _, _ => pure none
    | 6, 3 =>
      match exprIn r g (r.fld g 1) sub, exprIn r g (r.fld g 2) sub with
      | some t, some b => pure (some (← internE (.lam t b)))
      | _, _ => pure none
    | 7, 3 =>
      match exprIn r g (r.fld g 1) sub, exprIn r g (r.fld g 2) sub with
      | some t, some b => pure (some (← internE (.forallE t b)))
      | _, _ => pure none
    | 8, 4 =>
      match exprIn r g (r.fld g 1) sub, exprIn r g (r.fld g 2) sub, exprIn r g (r.fld g 3) sub with
      | some t, some v, some b => pure (some (← internE (.letE t v b)))
      | _, _, _ => pure none
    | 9, 1 =>
      match litP r g (r.fld g 0) with
      | none => pure none
      | some l => pure (some (← internE (.lit l)))
    | 10, 2 => pure (exprIn r g (r.fld g 1) sub)
    | 11, 3 =>
      match nameIn pk r g (r.fld g 0) sub with
      | none => pure none
      | some s =>
        match r.natP g (r.fld g 1) with
        | none => pure none
        | some i =>
          let i ← natWord i
          match exprIn r g (r.fld g 2) sub with
          | none => pure none
          | some x => pure (some (← internE (.proj s i x)))
    | _, _ => pure none
  else pure none

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:210-213 nameAt
**The `Name` stored at location `g`**, interned: a `Name` is a chain, so this is
linear, and it is the one read of the specification that executes. -/
def nameAt (pk : OleanPins) (r : Region) (g : Nat) : AM (Option NIdx) := do
  if r.fits g then
    let t := r.tag g
    if (t == 1 || t == 2) && r.nobjs g == 2 then
      let v := r.fld g 0
      if v == 1 then nameTail r g t pk.anon
      else
        match h : r.down g v with
        | none => pure none
        | some c =>
          have : c < g := Region.down_lt h
          match ← nameAt pk r c with
          | none => pure none
          | some p => nameTail r g t p
    else pure none
  else pure none
termination_by g

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:231-236 nameP
The `Name` a pointer stands for. -/
def nameP (pk : OleanPins) (r : Region) (v : UInt64) : AM (Option NIdx) :=
  if v == 1 then pure (some pk.anon)
  else match r.loc v with
    | some c => nameAt pk r c
    | none => pure none

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:274-296 CKindF.mapM
The `fn` and `fe` of `CEntryF.mapM`: what a pointer of a skeleton stands for. -/
structure PtrRead where
  rdName : UInt64 → AM (Option NIdx)
  rdExpr : UInt64 → AM (Option EIdx)

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:298-305 CEntryF.mapM
Read every name and expression of a constant: upstream's `mapM`, at `OptionT AM`. -/
def entryMap (rd : PtrRead) (c : CEntryF UInt64 UInt64) : AM (Option (CEntryF NIdx EIdx)) :=
  (c.mapM (m := OptionT AM) (fun v => OptionT.mk (rd.rdName v)) (fun v => OptionT.mk (rd.rdExpr v))).run

/-- con-leche: none — the numbers a skeleton holds fit a word (the Rust's
`spec::skel_fits`): `wordMax` and up is the `native` decline. -/
def skelFits {N E : Type} (c : CEntryF N E) : AM Unit := do
  let big : Nat → Bool := fun k => wordMax ≤ k
  let bad : Bool :=
    match c.kind with
    | .induct np ni _ _ nn .. => big np || big ni || big nn
    | .ctor _ ci np nf _ => big ci || big np || big nf
    | .recur _ np ni nmo nmi rules .. =>
      big np || big ni || big nmo || big nmi || rules.any fun x => big x.2.1
    | _ => false
  if bad then
    let _ ← natWord wordMax
    pure ()

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:403-404 ImportRec
An `import`, its name read. -/
abbrev ImportRec := ImportF NIdx

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:435-440 ModDecoded
What the reader takes of a module: the flag, the imports and the constants. -/
structure ModDecoded where
  isModule : Bool
  imports : Array ImportRec
  constants : Array (CEntryF NIdx EIdx)

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:447-457 constNamesGo
`constNamesOk`'s walk over the two arrays: `seen` the names before. -/
def constNamesGo (pk : OleanPins) (r : Region) :
    List Nat → List Nat → Std.HashSet NIdx → AM Bool
  | [], [], _ => pure true
  | n :: ns, c :: cs, seen => do
    match Olean.constSkel r c with
    | none => pure false
    | some sk =>
      match ← nameAt pk r n with
      | none => pure false
      | some a =>
        let sameObject : Bool := r.loc sk.name == some n
        let sameName : Bool ←
          if sameObject then pure true
          else
            match ← nameP pk r sk.name with
            | none => pure false
            | some b => pure (b == a)
        if !sameName then pure false
        else
          let (b, seen) := seen.containsThenInsert a
          if b then pure false else constNamesGo pk r ns cs seen
  | _, _, _ => pure false

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:459-479 constNamesOk
**A part's name table agrees with its constants**: as many entries, entry `i` the
name of constant `i`, no name twice. -/
def constNamesOk (pk : OleanPins) (r : Region) (root : UInt64) : AM Bool :=
  match r.loc root with
  | none => pure false
  | some g =>
    if r.isCtor g 0 5 then
      match r.objArray g (r.fld g 1), r.objArray g (r.fld g 2) with
      | some ns, some cs =>
        if ns.size == cs.size then
          constNamesGo pk r ns.toList cs.toList (Std.HashSet.emptyWithCapacity ns.size)
        else pure false
      | _, _ => pure false
    else pure false

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:492-493 CEntryF.stmt
A stored constant's statement over handles. -/
structure StmtRec where
  name : NIdx
  levelParams : List NIdx
  type : EIdx
  deriving BEq

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:492-493 CEntryF.stmt
A stored constant's statement. -/
def entryStmt (c : CEntryF NIdx EIdx) : StmtRec := ⟨c.name, c.levelParams, c.type⟩

end ConRon.Arena.Frontend.Olean

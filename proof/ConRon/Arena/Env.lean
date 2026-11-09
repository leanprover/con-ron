/-
# `ConRon.Arena.Env` — the declaration layer over handles (DESIGN.md §8, task #97e)

con-leche's `ConLeche/Kernel/Env.lean` declares the types the frontend
assembles and the fold consumes: `ConstantVal`, `RecRule`, `IndCaps`,
`ProjTable`, `ProjEntry`, `ConstantInfo` and `Declaration`.  Each of them is
DESIGN §8's census class **(T)** — not because it computes anything, but
because it *carries a term*: a `ConstantVal` holds an `Expr` and a `Name`, a
`RecRule` an `Expr`, a `ProjTable` an `Array Expr` and a `List Level`.

This module is the field-for-field mirror of those types with

    Expr ↦ EIdx      Name ↦ NIdx      Level ↦ LIdx      List Level ↦ List LIdx

and nothing else changed: the same constructors in the same order, the same
fields with the same names and the same defaults, the same `deriving` clauses.
The `I` prefix is the only renaming (`IDeclaration`, `IConstantInfo`, …), and
it exists so that a module may `open ConLeche` and still name both.

**What is NOT twinned, and why.**  Three of con-leche's types in that file
carry no term at all and are census class **(P)**: `ReducibilityHint`,
`BasisKind` and `QuotKind` are imported from con-leche and used as they are —
DESIGN §8.7's ruling ((B) imports con-leche's representation-free types rather
than copying them).

**The projection tables are their own component** (con-leche task #362):
`IEnv` is `{consts, tables}` and `IFEnv` keys the tables by their structure's
name, as con-leche's `Env`/`FEnv`.  A table is not a constant, so
`IConstantInfo.name` and `IConstantInfo.toConstantVal` are projections.

**The environment.**  `IEnv` is con-leche's association list, `IFEnv` its
`ConLeche/Kernel/FEnv.lean` index at `NIdx` keys over a frozen base layer
(`IFBase`, the stream's index: `Arena/StreamIndex.lean`).  The guard twins
that read them (`natLitStoredF` and its siblings) are `Arena/Core.lean`'s.
-/
module

public import ConRon.Arena.Monad
public import ConLeche.Kernel.Env

@[expose] public section

namespace ConRon.Arena

open ConLeche

/-! ## The constant's common data -/

/-- con-leche: ConLeche/Kernel/Env.lean:83-88 ConstantVal — data common to
all constants, with the name and the type as handles. -/
structure IConstantVal where
  name : NIdx
  levelParams : List NIdx
  type : EIdx
  deriving DecidableEq, Repr, Inhabited

/-! ## Recursor rules -/

/-- con-leche: ConLeche/Kernel/Env.lean:90-122 RecRuleFire — how a stored
recursor rule fires.  `.nested`'s and `.levels`'s lists become handle lists;
the parse writes the placeholder `.plain`. -/
inductive IRecRuleFire where
  | plain
  | nested (lvls : List LIdx) (pins : List EIdx)
  | levels (lvls : List LIdx)
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Env.lean:124-139 RecRule — one iota rule of a
recursor: the record's three fields and `fire`, read off the recursor's record
(the parse placeholder `.plain`), exactly as con-leche's. -/
structure IRecRule where
  ctor : NIdx
  nfields : Nat
  fire : IRecRuleFire
  rhs : EIdx
  deriving DecidableEq, Repr, Inhabited

/-! ## Inductive capabilities -/

/-- con-leche: ConLeche/Kernel/Env.lean:184-221 IndCaps — the definitional
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove Env.IIndCaps_bridge, then delete this line
capabilities of a stored inductive type that its block alone decides.
`etaCtor` is a handle. -/
structure IIndCaps where
  eta : Bool := false
  /-- con-leche's default is `.anonymous`; the handle's is the zero word.
  Neither is a name the field ever *denotes*: con-leche's own doc says the
  field is "meaningful only when `eta`", and the install writes it then. -/
  etaCtor : NIdx := default
  etaParams : Nat := 0
  etaFields : Nat := 0
  unitlike : Bool := false
  unitParams : Nat := 0
  /-- Official's `all`: the block's members, itself included, as handles. -/
  all : List NIdx := []
  /-- Official's `inductive_val.nparams`. -/
  nparams : Nat := 0
  /-- Official's `inductive_val.nindices`, read off the block's recursor record. -/
  nIdx : Nat := 0
  /-- Official's `inductive_val.cnstrs`, in declaration order, as handles. -/
  ctors : List NIdx := []
  deriving DecidableEq, Repr, Inhabited

/-! ## Projection tables -/

/-- con-leche: ConLeche/Kernel/Env.lean:223-259 ProjTable — one structure's
projection table, every term field a handle; stored in the environment's
table component (`IEnv.tables`), keyed on `structName`. -/
structure IProjTable where
  structName : NIdx
  levelParams : List NIdx
  numParams : Nat
  ctor : NIdx
  numFields : Nat
  bodies : Array EIdx
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Env.lean:261-274 ProjEntry — the per-field view
of a projection table. -/
structure IProjEntry where
  structName : NIdx
  idx : Nat
  levelParams : List NIdx
  numParams : Nat
  ctor : NIdx
  numFields : Nat
  body : EIdx
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Env.lean:276-280 ProjTable.entry — the view at
field `i`.  con-leche's `default` expression becomes the `Inhabited` handle: a
table is only read at `i < numFields`, where the default is not reachable. -/
def IProjTable.entry (tbl : IProjTable) (i : Nat) : IProjEntry :=
  ⟨tbl.structName, i, tbl.levelParams, tbl.numParams, tbl.ctor, tbl.numFields,
    tbl.bodies.getD i default⟩

/-! ## Stored constants -/

/-- con-leche: ConLeche/Kernel/Env.lean:282-301 ConstantInfo — the information
stored about an accepted constant, over handles.  A theorem is stored by its
statement only (con-leche task #329 THMVAL); a recursor carries its record's K
flag (`isK`). -/
inductive IConstantInfo where
  | axiomInfo (val : IConstantVal)
  | defnInfo (val : IConstantVal) (value : EIdx) (hint : ReducibilityHint)
  | thmInfo (val : IConstantVal)
  | indInfo (val : IConstantVal) (caps : IIndCaps)
  | ctorInfo (val : IConstantVal) (numParams numFields : Nat)
  | recInfo (val : IConstantVal) (majorIdx rulePrefix : Nat) (isK : Bool)
      (rules : List IRecRule)
  deriving DecidableEq, Repr, Inhabited

/-! ## Declaration records -/

/-- con-leche: ConLeche/Kernel/Env.lean:321-357 Declaration — a declaration
presented to the checker, over handles.  Six constructors, con-leche's own
order. -/
inductive IDeclaration where
  | axiomDecl (val : IConstantVal)
  | defnDecl (val : IConstantVal) (value : EIdx) (hint : ReducibilityHint)
  | thmDecl (val : IConstantVal) (value : EIdx)
  | opaqueDecl (val : IConstantVal) (value : EIdx)
  | indDecl (block : List IConstantInfo) (numParams : Nat)
  | quotDecl (kind : QuotKind) (val : IConstantVal)
  deriving DecidableEq, Repr, Inhabited

/-! ## Reading a stored constant -/

/-- con-leche: ConLeche/Kernel/Env.lean:416-418 ConstantInfo.toConstantVal —
the constant's common data. -/
def IConstantInfo.toConstantVal : IConstantInfo → IConstantVal
  | .axiomInfo v | .defnInfo v _ _ | .thmInfo v => v
  | .indInfo v _ | .ctorInfo v _ _ | .recInfo v _ _ _ _ => v

/-- con-leche: ConLeche/Kernel/Env.lean:420 name — the constant's
name: the environment index's key. -/
def IConstantInfo.name : IConstantInfo → NIdx
  | .axiomInfo v | .defnInfo v _ _ | .thmInfo v => v.name
  | .indInfo v _ | .ctorInfo v _ _ | .recInfo v _ _ _ _ => v.name

/-- con-leche: ConLeche/Kernel/Env.lean:426-433 Declaration.names — the names a
declaration record declares; `preparePrelude`'s lookup and the ground hoist's
name index read it. -/
def IDeclaration.names : IDeclaration → List NIdx
  | .axiomDecl cv | .defnDecl cv .. | .thmDecl cv .. | .opaqueDecl cv .. => [cv.name]
  | .quotDecl _ cv => [cv.name]
  | .indDecl block _ => block.map (·.name)

/-! ## The environment -/

/-- con-leche: ConLeche/Kernel/Env.lean:437-449 Env — the global environment:
the constants accepted so far and the structures' projection tables, each list
newest first.  Names are unique (the checker rejects duplicates), so the order
is irrelevant for lookup; so are the tables' structure names.  The tables are
not constants: no `.const` names one, `.proj` nodes alone read them, keyed on
the structure's name (`IFEnv.findTable?`). -/
structure IEnv where
  consts : List IConstantInfo
  tables : List IProjTable
  deriving Inhabited

/-- con-leche: ConLeche/Kernel/Env.lean:453-454 Env.empty — the empty
environment; the starting point of every checker run. -/
def IEnv.empty : IEnv := ⟨[], []⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:27-39 FBase — **a frozen lookup layer**:
the index of a whole stream, built once before any record is checked and never
written again (`Arena/StreamIndex.lean`).  An entry `n ↦ (c, ci)` says that the
first constant named `n` in the stream is `ci`, at counter `c`; an entry
`T ↦ (r, t)` that the first table of `T` is `t`, of record `r`.  A view below a
record reads the entries below its first counter `below` and its position
`belowRec` only. -/
structure IFBase where
  idx : Std.HashMap NIdx (Nat × IConstantInfo) := {}
  tbls : Std.HashMap NIdx (Nat × IProjTable) := {}
  below : Nat := 0
  belowRec : Nat := 0

/-- con-leche: ConLeche/Kernel/FEnv.lean:41-45 FBase.find? — the base layer's
lookup: a visible entry's constant. -/
def IFBase.find? (b : IFBase) (n : NIdx) : Option IConstantInfo :=
  match b.idx[n]? with
  | some (c, ci) => if c < b.below then some ci else none
  | none => none

/-- con-leche: ConLeche/Kernel/FEnv.lean:47-51 FBase.findTable? — the base
layer's table lookup: a visible entry's table. -/
def IFBase.findTable? (b : IFBase) (T : NIdx) : Option IProjTable :=
  match b.tbls[T]? with
  | some (r, t) => if r < b.belowRec then some t else none
  | none => none

/-- con-leche: ConLeche/Kernel/FEnv.lean:55-76 FEnv — the environment with its
`O(1)` index (DESIGN §8.3 lesson 13) over the frozen layer of a stream's index
(`base`).  `tbls` is the table map, keyed on the structure's name.  con-leche's
overlay (`ovl`) is not twinned: the port pushes and pops in place
(`IFEnv.popTemp`). -/
structure IFEnv where
  env : IEnv
  idx : Std.HashMap NIdx IConstantInfo
  base : IFBase
  tbls : Std.HashMap NIdx IProjTable

/-- con-leche: ConLeche/Kernel/FEnv.lean:78-84 mkIdxGo — the index build, from
the back: the newest (front) constant is inserted last and wins, exactly as
`List.find?` takes the first match. -/
def mkIFEnvGo : List IConstantInfo → Std.HashMap NIdx IConstantInfo
  | [] => ∅
  | ci :: cs => (mkIFEnvGo cs).insert ci.name ci

/-- con-leche: ConLeche/Kernel/FEnv.lean:86-90 mkTblsGo — the table map's
build, from the back: the newest (front) table is inserted last and wins,
exactly as `List.find?` takes the first. -/
def mkIFEnvTblsGo : List IProjTable → Std.HashMap NIdx IProjTable
  | [] => ∅
  | t :: ts => (mkIFEnvTblsGo ts).insert t.structName t

/-- con-leche: ConLeche/Kernel/FEnv.lean:92-94 mkFEnv — build the indexes of
`env`, over the empty base. -/
def mkIFEnv (env : IEnv) : IFEnv :=
  ⟨env, mkIFEnvGo env.consts, {}, mkIFEnvTblsGo env.tables⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:98-105 FEnv.lookup — the index, then the
frozen layer.  A job's own index is empty until its record pushes, and the
lookups are hot, so an empty index is not hashed into. -/
def IFEnv.lookup (fe : IFEnv) (n : NIdx) : Option IConstantInfo :=
  if fe.idx.isEmpty then fe.base.find? n
  else
    match fe.idx[n]? with
    | some ci => some ci
    | none => fe.base.find? n

/-- con-leche: ConLeche/Kernel/FEnv.lean:118-128 FEnv.find? — indexed lookup: the
own layer, and on a miss the frozen base.  No overlay (the structure's note). -/
def IFEnv.find? (fe : IFEnv) (n : NIdx) : Option IConstantInfo :=
  fe.lookup n

/-- con-leche: ConLeche/Kernel/FEnv.lean:130-134 FEnv.push — the index of the
cons-extended environment; the base and the tables are untouched. -/
def IFEnv.push (fe : IFEnv) (ci : IConstantInfo) : IFEnv :=
  ⟨⟨ci :: fe.env.consts, fe.env.tables⟩, fe.idx.insert ci.name ci, fe.base, fe.tbls⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:136-141 FEnv.pushTable — **install a
projection table**: the table component extended, the constant index
untouched. -/
def IFEnv.pushTable (fe : IFEnv) (t : IProjTable) : IFEnv :=
  ⟨⟨fe.env.consts, t :: fe.env.tables⟩, fe.idx, fe.base, fe.tbls.insert t.structName t⟩

/-- con-leche: none — **the inverse of a temporary push** (the port's
`env::ifenv_pop_temp`, task #97-P6-5 lever 5, in place of con-leche's
`FEnv.overlay`): the pushed constant dropped and the index row under its name put
back as it was before the push (`prev`, the raw row read with `idx[n]?` before
it). -/
def IFEnv.popTemp (fe : IFEnv) (n : NIdx) (prev : Option IConstantInfo) : IFEnv :=
  ⟨⟨fe.env.consts.tail, fe.env.tables⟩,
   (match prev with
    | some r => fe.idx.insert n r
    | none => fe.idx.erase n),
   fe.base, fe.tbls⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:168-173 FEnv.rawTable? — the table map's
lookup, ungated: a miss falls through to the base layer. -/
def IFEnv.rawTable? (fe : IFEnv) (T : NIdx) : Option IProjTable :=
  match fe.tbls[T]? with
  | some t => some t
  | none => fe.base.findTable? T

/-- con-leche: ConLeche/Kernel/FEnv.lean:175-179 FEnv.findTable? — **the table
lookup**: `T`'s table, visible exactly where the constant `T` is. -/
def IFEnv.findTable? (fe : IFEnv) (T : NIdx) : Option IProjTable :=
  if (fe.find? T).isSome then fe.rawTable? T else none

/-- con-leche: ConLeche/Kernel/FEnv.lean:181-185 FEnv.findProj? — indexed
projection-table lookup: the structure's table, viewed at field `i`. -/
def IFEnv.findProj? (fe : IFEnv) (T : NIdx) (i : Nat) : Option IProjEntry :=
  match fe.findTable? T with
  | some tbl => if i < tbl.numFields then some (tbl.entry i) else none
  | none => none

/-! ## The syntactic Π-telescope -/

/-- con-leche: ConLeche/Kernel/Env.lean:363-377 Expr.piSortTeleLen? — the length
of a syntactic Π-telescope ending in a SORT.  A spine walk, so the fuel is the
store's node count; con-leche's structural recursion is the same walk with the
node read through `view`. -/
def piSortTeleLen? : Nat → EIdx → AM (Option Nat)
  | 0, _ => fail (.internal "fuel exhausted: piSortTeleLen?")
  | fuel + 1, h => do
    match ← view h with
    | .forallE _ body => pure ((← piSortTeleLen? fuel body).map (· + 1))
    | .sort _ => pure (some 0)
    | _ => pure none

end ConRon.Arena

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
than copying them).  So is `PropWhen`, which `IndCaps.sortZ` carries: it holds
`ConLeche.Name`s, and since task #342 upstream it is a plain `never |
ifAllZero (List Name)` datum that only `capsNeverZero` and the ι case split
read (`isNever`), so a handle twin of it would buy nothing.

**The projection tables are their own component** (con-leche task #362):
`IEnv` is `{consts, tables}` and `IFEnv` keys the tables by their structure's
name, as con-leche's `Env`/`FEnv`.  A table is not a constant, so
`IConstantInfo.name` and `IConstantInfo.toConstantVal` are projections.

**The environment.**  `IEnv` is con-leche's association list, `IFEnv` its
`ConLeche/Kernel/FEnv.lean` index at `NIdx` keys — the two shapes P2c
programs against.  What is deliberately NOT here is the *choice* between them
or any of the guard twins that read them (`natLitSupportedF` and its
siblings): those are P2c's, and they read constants this module has no twin
of yet.
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
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Env.IRecRuleFire_bridge, then delete this line
recursor rule fires.  `.nested`'s level and pin lists become handle lists;
the parse writes the placeholder `.plain`. -/
inductive IRecRuleFire where
  | plain
  | nested (lvls : List LIdx) (pins : List EIdx)
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Env.lean:124-139 RecRule — one iota rule of a
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Env.IRecRule_bridge, then delete this line
recursor.  `ctorParams`, `fire`, `k` and `eta` are install-computed and carry
the parse placeholders `0`/`.plain`/`false`, exactly as con-leche's do. -/
structure IRecRule where
  ctor : NIdx
  nfields : Nat
  ctorParams : Nat
  fire : IRecRuleFire
  rhs : EIdx
  k : Bool := false
  eta : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-! ## Inductive capabilities -/

/-- con-leche: ConLeche/Kernel/Env.lean:184-232 IndCaps — the definitional
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Env.IIndCaps_bridge, then delete this line
capabilities of a stored inductive type.  `etaCtor` is a handle; `sortZ` stays
con-leche's `PropWhen` (see the module note). -/
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
  ruleK : Bool := false
  sortZ : PropWhen := .ifAllZero []
  /-- Official's `all`: the block's members, itself included, as handles. -/
  all : List NIdx := []
  /-- Official's `inductive_val.nparams`. -/
  nparams : Nat := 0
  /-- Official's `inductive_val.cnstrs`, in declaration order, as handles. -/
  ctors : List NIdx := []
  deriving DecidableEq, Repr, Inhabited

/-! ## Projection tables -/

/-- con-leche: ConLeche/Kernel/Env.lean:234-270 ProjTable — one structure's
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Env.IProjTable_bridge, then delete this line
projection table, every term field a handle; stored in the environment's
table component (`IEnv.tables`), keyed on `structName`. -/
structure IProjTable where
  structName : NIdx
  levelParams : List NIdx
  numParams : Nat
  ctor : NIdx
  numFields : Nat
  structSort : LIdx
  bodies : Array EIdx
  guards : List LIdx
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Env.lean:272-285 ProjEntry — the per-field view
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Env.IProjEntry_bridge, then delete this line
of a projection table. -/
structure IProjEntry where
  structName : NIdx
  idx : Nat
  levelParams : List NIdx
  numParams : Nat
  ctor : NIdx
  numFields : Nat
  body : EIdx
  fieldSort : LIdx
  structSort : LIdx
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Env.lean:287-291 ProjTable.entry — the view at
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Env.IProjTable.entry_bridge, then delete this line
field `i`.  con-leche's `default` expression and its `.zero` guard level become
the `Inhabited` handle of each kind: a table is only read at `i < numFields`,
where neither default is reachable. -/
def IProjTable.entry (tbl : IProjTable) (i : Nat) : IProjEntry :=
  ⟨tbl.structName, i, tbl.levelParams, tbl.numParams, tbl.ctor, tbl.numFields,
    tbl.bodies.getD i default, tbl.guards.getD i default, tbl.structSort⟩

/-! ## Stored constants -/

/-- con-leche: ConLeche/Kernel/Env.lean:293-312 ConstantInfo — the information
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Env.IConstantInfo_bridge, then delete this line
stored about an accepted constant, over handles.  A theorem is stored by its
statement only (con-leche task #329 THMVAL). -/
inductive IConstantInfo where
  | axiomInfo (val : IConstantVal)
  | defnInfo (val : IConstantVal) (value : EIdx) (hint : ReducibilityHint)
  | thmInfo (val : IConstantVal)
  | indInfo (val : IConstantVal) (caps : IIndCaps)
  | ctorInfo (val : IConstantVal) (numParams numFields : Nat)
  | recInfo (val : IConstantVal) (majorIdx rulePrefix : Nat) (rules : List IRecRule)
  deriving DecidableEq, Repr, Inhabited

/-! ## Declaration records -/

/-- con-leche: ConLeche/Kernel/Env.lean:332-368 Declaration — a declaration
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Env.IDeclaration_bridge, then delete this line
presented to the checker, over handles.  Seven constructors, con-leche's own
order; the frontend produces every one but `basisDecl`, which is the fold's own
record for "install the pinned basis block". -/
inductive IDeclaration where
  | axiomDecl (val : IConstantVal)
  | defnDecl (val : IConstantVal) (value : EIdx) (hint : ReducibilityHint)
  | thmDecl (val : IConstantVal) (value : EIdx)
  | opaqueDecl (val : IConstantVal) (value : EIdx)
  | basisDecl (kind : BasisKind)
  | indDecl (block : List IConstantInfo) (numParams : Nat)
  | quotDecl (kind : QuotKind) (val : IConstantVal)
  deriving DecidableEq, Repr, Inhabited

/-! ## Reading a stored constant -/

/-- con-leche: ConLeche/Kernel/Env.lean:427-429 ConstantInfo.toConstantVal —
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Env.IConstantInfo.toConstantVal_bridge, then delete this line
the constant's common data. -/
def IConstantInfo.toConstantVal : IConstantInfo → IConstantVal
  | .axiomInfo v | .defnInfo v _ _ | .thmInfo v => v
  | .indInfo v _ | .ctorInfo v _ _ | .recInfo v _ _ _ => v

/-- con-leche: ConLeche/Kernel/Env.lean:431 name — the constant's
name: the environment index's key. -/
def IConstantInfo.name : IConstantInfo → NIdx
  | .axiomInfo v | .defnInfo v _ _ | .thmInfo v => v.name
  | .indInfo v _ | .ctorInfo v _ _ | .recInfo v _ _ _ => v.name

/-- con-leche: ConLeche/Kernel/Env.lean:437-444 Declaration.names — the names a
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Env.IDeclaration.names_bridge, then delete this line
declaration record declares; `preparePrelude`'s lookup and the ground hoist's
name index read it. -/
def IDeclaration.names : IDeclaration → List NIdx
  | .axiomDecl cv | .defnDecl cv .. | .thmDecl cv .. | .opaqueDecl cv .. => [cv.name]
  | .quotDecl _ cv => [cv.name]
  | .indDecl block _ => block.map (·.name)
  | .basisDecl _ => []

/-! ## The environment -/

/-- con-leche: ConLeche/Kernel/Env.lean:448-460 Env — the global environment:
the constants accepted so far and the structures' projection tables, each list
newest first.  Names are unique (the checker rejects duplicates), so the order
is irrelevant for lookup; so are the tables' structure names.  The tables are
not constants: no `.const` names one, `.proj` nodes alone read them, keyed on
the structure's name (`IFEnv.findTable?`). -/
structure IEnv where
  consts : List IConstantInfo
  tables : List IProjTable
  deriving Inhabited

/-- con-leche: ConLeche/Kernel/Env.lean:464-465 Env.empty — the empty
environment; the starting point of every checker run. -/
def IEnv.empty : IEnv := ⟨[], []⟩

/-- con-leche: ConLeche/Kernel/Env.lean:467-468 Env.find? — the linear lookup.
A name comparison is a handle comparison, which is sound because `denoteN` is
injective (task #97a's `denoteN_inj`; DESIGN §8.3 makes exactness a soundness
obligation for exactly this reason). -/
def IEnv.find? (env : IEnv) (n : NIdx) : Option IConstantInfo :=
  env.consts.find? (·.name == n)

/-- con-leche: ConLeche/Kernel/FEnv.lean:55-76 FEnv — the environment with its
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Env.IFEnv_bridge, then delete this line
`O(1)` index (DESIGN §8.3 lesson 13).  Entries with counter `< visibleBelow`
are visible; `visibleBelow` doubles as the next counter `push` hands out.
`tbls` is the table map, keyed on the structure's name; it has no counter, a
table being visible exactly where its structure is (`findTable?`). -/
structure IFEnv where
  env : IEnv
  idx : Std.HashMap NIdx (Nat × IConstantInfo)
  visibleBelow : Nat
  tbls : Std.HashMap NIdx IProjTable

/-- con-leche: ConLeche/Kernel/FEnv.lean:138-147 mkFEnvGo — the index build, from
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Env.mkIFEnvGo_bridge, then delete this line
the back: the newest (front) constant is inserted last and wins, exactly as
`List.find?` takes the first match. -/
def mkIFEnvGo : List IConstantInfo → Nat × Std.HashMap NIdx (Nat × IConstantInfo)
  | [] => (0, ∅)
  | ci :: cs =>
    let p := mkIFEnvGo cs
    (p.1 + 1, p.2.insert ci.name (p.1, ci))

/-- con-leche: ConLeche/Kernel/FEnv.lean:86-90 mkTblsGo — the table map's
build, from the back: the newest (front) table is inserted last and wins,
exactly as `List.find?` takes the first. -/
def mkIFEnvTblsGo : List IProjTable → Std.HashMap NIdx IProjTable
  | [] => ∅
  | t :: ts => (mkIFEnvTblsGo ts).insert t.structName t

/-- con-leche: ConLeche/Kernel/FEnv.lean:92-94 mkFEnv — build the indexes of
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Env.mkIFEnv_bridge, then delete this line
`env`, with nothing hidden. -/
def mkIFEnv (env : IEnv) : IFEnv :=
  let p := mkIFEnvGo env.consts
  ⟨env, p.2, p.1, mkIFEnvTblsGo env.tables⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:118-128 FEnv.find? — indexed lookup,
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Env.IFEnv.find?_bridge, then delete this line
bounded by the visibility counter. -/
def IFEnv.find? (fe : IFEnv) (n : NIdx) : Option IConstantInfo :=
  match fe.idx[n]? with
  | some (c, ci) => if c < fe.visibleBelow then some ci else none
  | none => none

/-- con-leche: ConLeche/Kernel/FEnv.lean:184-187 FEnv.restrictTo — restrict the
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Env.IFEnv.restrictTo_bridge, then delete this line
view to the first `k` installed constants; `O(1)`, a field update. -/
def IFEnv.restrictTo (fe : IFEnv) (k : Nat) : IFEnv :=
  { fe with visibleBelow := k }

/-- con-leche: ConLeche/Kernel/FEnv.lean:130-134 FEnv.push — the index of the
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Env.IFEnv.push_bridge, then delete this line
cons-extended environment: the new entry gets the next installation counter and
the visibility bound advances with it; the tables are untouched. -/
def IFEnv.push (fe : IFEnv) (ci : IConstantInfo) : IFEnv :=
  ⟨⟨ci :: fe.env.consts, fe.env.tables⟩, fe.idx.insert ci.name (fe.visibleBelow, ci),
   fe.visibleBelow + 1, fe.tbls⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:136-141 pushTable — **install a
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Env.IFEnv.pushTable_bridge, then delete this line
projection table**: the table component extended, the constant index
untouched. -/
def IFEnv.pushTable (fe : IFEnv) (t : IProjTable) : IFEnv :=
  ⟨⟨fe.env.consts, t :: fe.env.tables⟩, fe.idx, fe.visibleBelow,
   fe.tbls.insert t.structName t⟩

/-- con-leche: none — **the inverse of a temporary push** (the port's
`env::ifenv_pop_temp`, task #97-P6-5 lever 5): the pushed constant dropped, the
index row under its name put back as it was before the push (`prev`, the raw
row read with `idx[n]?` before it), and the visibility bound restored. -/
def IFEnv.popTemp (fe : IFEnv) (n : NIdx) (prev : Option (Nat × IConstantInfo)) : IFEnv :=
  ⟨⟨fe.env.consts.tail, fe.env.tables⟩,
   (match prev with
    | some r => fe.idx.insert n r
    | none => fe.idx.erase n),
   fe.visibleBelow - 1, fe.tbls⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:156-161 rawTable? — the table map's
lookup, ungated.  con-leche falls through to the base layer on a miss; the
twin has none (as `IFEnv.find?`), so a miss is `none`. -/
def IFEnv.rawTable? (fe : IFEnv) (T : NIdx) : Option IProjTable :=
  fe.tbls[T]?

/-- con-leche: ConLeche/Kernel/FEnv.lean:163-167 findTable? — **the table
lookup**: `T`'s table, visible exactly where the constant `T` is, so a prefix
view (`restrictTo`) hides a table by hiding its structure. -/
def IFEnv.findTable? (fe : IFEnv) (T : NIdx) : Option IProjTable :=
  if (fe.find? T).isSome then fe.rawTable? T else none

/-- con-leche: ConLeche/Kernel/FEnv.lean:169-173 FEnv.findProj? — indexed
projection-table lookup: the structure's table, viewed at field `i`. -/
def IFEnv.findProj? (fe : IFEnv) (T : NIdx) (i : Nat) : Option IProjEntry :=
  match fe.findTable? T with
  | some tbl => if i < tbl.numFields then some (tbl.entry i) else none
  | none => none

/-! ## The syntactic Π-telescope -/

/-- con-leche: ConLeche/Kernel/Env.lean:374-388 Expr.piSortTeleLen? — the length
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

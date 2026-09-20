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
`ConLeche.Name`s, but task #97a already put con-leche's `BinderMeta` — hence
`PropWhen` — inside the store's `lam`/`forallE` node (`Arena/Store.lean`'s
`ENodeView.lam`), so a `PropWhen` over real names is what the arena's own
representation uses and a handle twin of it would be a second spelling of the
same datum.

**The one added field, and why.**  `IProjTable` carries a `tableName : NIdx`
con-leche's `ProjTable` does not.  con-leche COMPUTES the reserved name
(`ConstantInfo.toConstantVal`'s `.projInfo` arm is `projTableName
tbl.structName`); over handles, computing a name means INTERNING it, i.e.
touching the store — and `ConstantInfo.name` must stay pure, because it is the
key of the environment index (DESIGN §8.3 lesson 13: `HashMap NIdx
IConstantInfo` with an unconditional `find? = denoteEnv.find?` spec) and the
predicate `Env.find?`, `FEnv`'s index build and `preparePrelude`'s record
lookup all run it in a loop.  So the handle the install interned is KEPT, as
hash-consing always keeps the handle it interned, and `IProjTable.tableName`
is by construction `projTableName structName`.  A table is the only
`IConstantInfo` whose name is not already a field of its `IConstantVal`.

`IConstantInfo.toConstantVal` and `.type` are still `AM`: the `.projInfo` arm
builds the closed dummy type `Sort 1`, which has to be interned.  So is
`IDeclaration.name`, whose `.basisDecl`/`.indDecl` fall-through is
`.anonymous`.  Both are off the hot path; `IConstantInfo.name` and
`IDeclaration.names`, which are on it, are pure.

**The environment.**  `IEnv` is con-leche's association list, `IFEnv` its
`ConLeche/Kernel/FEnv.lean` index at `NIdx` keys — the two shapes P2c
programs against.  What is deliberately NOT here is the *choice* between them
or any of the guard twins that read them (`natLitSupportedF` and its
siblings): those are P2c's, and they read constants this module has no twin
of yet.
-/
import ConRon.Arena.Monad
import ConLeche.Kernel.Env

namespace ConRon.Arena

open ConLeche

/-! ## The constant's common data -/

/-- con-leche: ConLeche/Kernel/Env.lean:186-191 ConstantVal — data common to
all constants, with the name and the type as handles. -/
structure IConstantVal where
  name : NIdx
  levelParams : List NIdx
  type : EIdx
  deriving DecidableEq, Repr, Inhabited

/-! ## Recursor rules -/

/-- con-leche: ConLeche/Kernel/Env.lean:193-237 RecRuleFire — how a stored
recursor rule may fire.  `.nested`'s level and pin lists become handle lists;
the parse writes the placeholder `.inert` and never the other two. -/
inductive IRecRuleFire where
  | inert
  | plain
  | nested (lvls : List LIdx) (pins : List EIdx)
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Env.lean:239-282 RecRule — one iota rule of a
recursor.  `ctorParams`, `fire`, `k`, `eta` and `paramsBlind` are
install-computed and carry the parse placeholders `0`/`.inert`/`false`, exactly
as con-leche's do. -/
structure IRecRule where
  ctor : NIdx
  nfields : Nat
  ctorParams : Nat
  fire : IRecRuleFire
  rhs : EIdx
  k : Bool := false
  eta : Bool := false
  paramsBlind : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Env.lean:284-291 RecRule.compareParams — whether
the iota step compares this rule's parameter comparands. -/
def IRecRule.compareParams (rl : IRecRule) : Bool :=
  match rl.fire with
  | .plain => !rl.paramsBlind
  | _ => true

/-! ## Inductive capabilities -/

/-- con-leche: ConLeche/Kernel/Env.lean:347-374 IndCaps — the definitional
capabilities of a stored inductive type.  `etaCtor` is a handle; `sortZ` stays
con-leche's `PropWhen`, which is the datum the store's own binder metadata
already carries (see the module note). -/
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
  deriving DecidableEq, Repr, Inhabited

/-! ## Projection tables -/

/-- con-leche: ConLeche/Kernel/Env.lean:376-431 ProjTable — one structure's
projection table, every term field a handle. -/
structure IProjTable where
  structName : NIdx
  /-- **The one field con-leche's `ProjTable` does not have**: the reserved
  name `projTableName structName` the table is stored under, kept rather than
  recomputed so that `IConstantInfo.name` — the environment index's key — is
  pure.  See the module note. -/
  tableName : NIdx
  levelParams : List NIdx
  numParams : Nat
  ctor : NIdx
  numFields : Nat
  structSort : LIdx
  bodies : Array EIdx
  guards : List LIdx
  off : Nat
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Env.lean:433-452 ProjEntry — the per-field view
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
  off : Nat
  deriving DecidableEq, Repr, Inhabited

/-- con-leche: ConLeche/Kernel/Env.lean:454-458 ProjTable.entry — the view at
field `i`.  con-leche's `default` expression and its `.zero` guard level become
the `Inhabited` handle of each kind: a table is only read at `i < numFields`,
where neither default is reachable. -/
def IProjTable.entry (tbl : IProjTable) (i : Nat) : IProjEntry :=
  ⟨tbl.structName, i, tbl.levelParams, tbl.numParams, tbl.ctor, tbl.numFields,
    tbl.bodies.getD i default, tbl.guards.getD i default, tbl.structSort, tbl.off⟩

/-! ## Stored constants -/

/-- con-leche: ConLeche/Kernel/Env.lean:460-486 ConstantInfo — the information
stored about an accepted constant, over handles. -/
inductive IConstantInfo where
  | axiomInfo (val : IConstantVal)
  | defnInfo (val : IConstantVal) (value : EIdx) (hint : ReducibilityHint)
  | thmInfo (val : IConstantVal) (value : EIdx)
  | indInfo (val : IConstantVal) (caps : IIndCaps)
  | ctorInfo (val : IConstantVal) (numParams numFields : Nat)
  | recInfo (val : IConstantVal) (majorIdx rulePrefix : Nat) (rules : List IRecRule)
  | projInfo (tbl : IProjTable)
  deriving DecidableEq, Repr, Inhabited

/-! ## Declaration records -/

/-- con-leche: ConLeche/Kernel/Env.lean:506-560 Declaration — a declaration
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

/-! ## The reserved names -/

/-- con-leche: ConLeche/Kernel/Env.lean:623-629 projFnName — the public
projection-*function* name for field `i` of structure `T`.  Building a name
means interning it, so the twin is monadic. -/
def projFnName (T : NIdx) (i : Nat) : AM NIdx := do
  let s ← internNNode (.str T "proj")
  internNNode (.num s i)

/-- con-leche: ConLeche/Kernel/Env.lean:631-635 projTableName — the reserved
name of structure `T`'s projection table. -/
def projTableName (T : NIdx) : AM NIdx := do
  let s ← internNNode (.str T "projTable")
  internNNode (.num s 0)

/-! ## Reading a stored constant -/

/-- con-leche: ConLeche/Kernel/Env.lean:639-642 ConstantInfo.toConstantVal —
the constant's common data.  The `.projInfo` arm BUILDS the reserved table name
and the closed dummy type `Sort 1`, which over handles means interning them:
that is the one reason this projection is monadic (see the module note). -/
def IConstantInfo.toConstantVal : IConstantInfo → AM IConstantVal
  | .axiomInfo v | .defnInfo v _ _ | .thmInfo v _ => pure v
  | .indInfo v _ | .ctorInfo v _ _ | .recInfo v _ _ _ => pure v
  | .projInfo tbl => do
    let z ← internLNode .zero
    let one ← internLNode (.succ z)
    let ty ← internE (.sort one)
    pure ⟨tbl.tableName, tbl.levelParams, ty⟩

/-- con-leche: ConLeche/Kernel/Env.lean:637-655 ConstantInfo — the constant's
name, `ConstantInfo.name` at line 644.  PURE, unlike `toConstantVal`: it is
the environment index's key, and `IProjTable.tableName` is the stored handle
that makes it so (see the module note). -/
def IConstantInfo.name : IConstantInfo → NIdx
  | .axiomInfo v | .defnInfo v _ _ | .thmInfo v _ => v.name
  | .indInfo v _ | .ctorInfo v _ _ | .recInfo v _ _ _ => v.name
  | .projInfo tbl => tbl.tableName

/-- con-leche: ConLeche/Kernel/Env.lean:646-651 ConstantInfo.isTowerEntry — a
projection table is a table, not a term. -/
def IConstantInfo.isTowerEntry : IConstantInfo → Bool
  | .projInfo _ => true
  | _ => false

/-- con-leche: ConLeche/Kernel/Env.lean:653 ConstantInfo.type — the constant's
declared type. -/
def IConstantInfo.type (c : IConstantInfo) : AM EIdx := do
  pure (← c.toConstantVal).type

/-- con-leche: ConLeche/Kernel/Env.lean:562-570 Declaration — the name of a
non-basis declaration, `Declaration.name` at lines 565-568.  con-leche's
`.anonymous` fall-through is the interned anonymous name here. -/
def IDeclaration.name : IDeclaration → AM NIdx
  | .axiomDecl v | .defnDecl v .. | .thmDecl v .. | .opaqueDecl v .. => pure v.name
  | .quotDecl _ v => pure v.name
  | .basisDecl _ | .indDecl _ _ => internNNode .anonymous

/-- con-leche: ConLeche/Kernel/Env.lean:659-670 Declaration.names — the names a
declaration record declares; `preparePrelude`'s lookup and the ground hoist's
name index read it. -/
def IDeclaration.names : IDeclaration → List NIdx
  | .axiomDecl cv | .defnDecl cv .. | .thmDecl cv .. | .opaqueDecl cv .. => [cv.name]
  | .quotDecl _ cv => [cv.name]
  | .indDecl block _ => block.map (·.name)
  | .basisDecl _ => []

/-! ## The environment -/

/-- con-leche: ConLeche/Kernel/Env.lean:674-679 Env — the global environment:
the list of constants accepted so far, newest first.  Names are unique (the
checker rejects duplicates), so the order is irrelevant for lookup. -/
structure IEnv where
  consts : List IConstantInfo
  deriving Inhabited

/-- con-leche: ConLeche/Kernel/Env.lean:683-684 Env.empty — the empty
environment; the starting point of every checker run. -/
def IEnv.empty : IEnv := ⟨[]⟩

/-- con-leche: ConLeche/Kernel/Env.lean:686-687 Env.find? — the linear lookup.
A name comparison is a handle comparison, which is sound because `denoteN` is
injective (task #97a's `denoteN_inj`; DESIGN §8.3 makes exactness a soundness
obligation for exactly this reason). -/
def IEnv.find? (env : IEnv) (n : NIdx) : Option IConstantInfo :=
  env.consts.find? (·.name == n)

/-- con-leche: ConLeche/Kernel/Env.lean:689-695 Env.findProj? — the
projection-table entry for field `i` of `T`: the structure's table
(`projTableName T`), viewed at field `i`.  Monadic only because the reserved
name has to be interned to be looked up. -/
def IEnv.findProj? (env : IEnv) (T : NIdx) (i : Nat) : AM (Option IProjEntry) := do
  match env.find? (← projTableName T) with
  | some (.projInfo tbl) => pure (if i < tbl.numFields then some (tbl.entry i) else none)
  | _ => pure none

/-- con-leche: ConLeche/Kernel/FEnv.lean:29-49 FEnv — the environment with its
`O(1)` index (DESIGN §8.3 lesson 13).  Entries with counter `< visibleBelow`
are visible; `visibleBelow` doubles as the next counter `push` hands out. -/
structure IFEnv where
  env : IEnv
  idx : Std.HashMap NIdx (Nat × IConstantInfo)
  visibleBelow : Nat

/-- con-leche: ConLeche/Kernel/FEnv.lean:51-60 mkFEnvGo — the index build, from
the back: the newest (front) constant is inserted last and wins, exactly as
`List.find?` takes the first match. -/
def mkIFEnvGo : List IConstantInfo → Nat × Std.HashMap NIdx (Nat × IConstantInfo)
  | [] => (0, ∅)
  | ci :: cs =>
    let p := mkIFEnvGo cs
    (p.1 + 1, p.2.insert ci.name (p.1, ci))

/-- con-leche: ConLeche/Kernel/FEnv.lean:62-66 mkFEnv — build the index of
`env`, with nothing hidden. -/
def mkIFEnv (env : IEnv) : IFEnv :=
  let p := mkIFEnvGo env.consts
  ⟨env, p.2, p.1⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:70-75 FEnv.find? — indexed lookup,
bounded by the visibility counter. -/
def IFEnv.find? (fe : IFEnv) (n : NIdx) : Option IConstantInfo :=
  match fe.idx[n]? with
  | some (c, ci) => if c < fe.visibleBelow then some ci else none
  | none => none

/-- con-leche: ConLeche/Kernel/FEnv.lean:77-80 FEnv.restrictTo — restrict the
view to the first `k` installed constants; `O(1)`, a field update. -/
def IFEnv.restrictTo (fe : IFEnv) (k : Nat) : IFEnv :=
  { fe with visibleBelow := k }

/-- con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push — the index of the
cons-extended environment: the new entry gets the next installation counter and
the visibility bound advances with it. -/
def IFEnv.push (fe : IFEnv) (ci : IConstantInfo) : IFEnv :=
  ⟨⟨ci :: fe.env.consts⟩, fe.idx.insert ci.name (fe.visibleBelow, ci),
   fe.visibleBelow + 1⟩

/-- con-leche: ConLeche/Kernel/FEnv.lean:91-95 FEnv.findProj? — indexed
projection-table lookup. -/
def IFEnv.findProj? (fe : IFEnv) (T : NIdx) (i : Nat) : AM (Option IProjEntry) := do
  match fe.find? (← projTableName T) with
  | some (.projInfo tbl) => pure (if i < tbl.numFields then some (tbl.entry i) else none)
  | _ => pure none

/-! ## The syntactic Π-telescope -/

/-- con-leche: ConLeche/Kernel/Env.lean:572-586 Expr.piSortTeleLen? — the length
of a syntactic Π-telescope ending in a SORT.  A spine walk, so the fuel is the
store's node count; con-leche's structural recursion is the same walk with the
node read through `view`. -/
def piSortTeleLen? : Nat → EIdx → AM (Option Nat)
  | 0, _ => fail (.internal "fuel exhausted: piSortTeleLen?")
  | fuel + 1, h => do
    match ← view h with
    | .forallE _ body _ => pure ((← piSortTeleLen? fuel body).map (· + 1))
    | .sort _ => pure (some 0)
    | _ => pure none

end ConRon.Arena

/-
# `ConRon.Arena.Frontend.ExportC` — the export parser INTO THE STORE
(DESIGN.md §8.3 "Parsing", task #97e)

con-leche's `ConLeche/Frontend/ExportC.lean`, clause for clause, with one
change: **no `Expr` is ever built**.  Where con-leche's parse state keeps
`IdTable Expr` / `IdTable Level` / `IdTable Name` of *values*, this one keeps
`IdTable EIdx` / `IdTable LIdx` / `IdTable NIdx` of **handles** into the
persistent tier of the `EStore` the `AM` state carries; a table hit is the
same shared node it is there, by handle rather than by reference, so the
export's own sharing is preserved exactly (DESIGN §8.3, con-leche's lesson 25).

**The scanner is NOT twinned.**  `ConLeche/Frontend/Scan/{Types,Fast}.lean`
is imported and used as it is.  Its records — `LineRec`, `NameRec`,
`LevelRec`, `ExprRec`, `CVRec`, `RuleRec`, `IndTypeRec`, `IndCtorRec`,
`IndRecRec`, `DeclRec`, `HintsRec` — are the dialect's *syntax*, in
stream indices, with nothing resolved: there is no `Expr`, `Name` or `Level`
anywhere in that file, and `Scan/Fast.lean` mentions `ExprRec` and never
`ConLeche.Expr`.  A twin of a byte recogniser that produces
representation-free records would be a copy, not a port, so `scanLineFwd` is
reused verbatim; `IdTable` (the dense-plus-sparse stream-index table, also in
`Scan/Types.lean`) is reused at `NIdx`/`LIdx`/`EIdx` for the same reason —
DESIGN §8.3 calls the parse table "an `Array EIdx` from export index to
handle", and `IdTable`'s dense prefix IS that array, with the sparse overflow
con-leche needs for the hand-written fixtures whose indices have gaps.
`scanLineSpec` and the `@[csimp]` equality of `Scan/Equiv.lean` are NOT
imported: con-leche calls the naive reference and lets the compiler
substitute; (B) calls `scanLineFwd`, which is what both binaries run, and
avoids a 1 800-line proof dependency for nothing.

**No smart constructor is needed, and none is missing.**  con-leche's
`Expr.mkApp`/`mkSort`/… (`ConLeche/Cached/ExprNodes.lean:106-126`) are
`@[inline]` identity wrappers — `mkApp f a = .app f a` by `rfl` — since its
task #172 B3a made the derived fields `@[computed_field]`s the *compiler*
maintains.  They therefore reject nothing and validate nothing: the ONLY work
they used to do is computing the packed derived word, which the arena's
`EStore.intern` does at intern time from the children's derived columns (task
#97a's `derOfView`, `Expr.data`'s formula verbatim).  So the exhaustive answer
to "what do con-leche's smart constructors reject that this parse must
reject too" is **nothing**, and the exhaustive list of places the parse relies
on `Expr.data` is: the `Hashable`/`BEq` instances behind its `Std.HashMap`
keys — which the store replaces with handle identity — and nothing else.  The
checks the parse DOES make are all its own and are all here: the rebinding
test, `validateIndD`'s block consistency checks, and the safety/kind
recognisers.

**Every inductive block is pushed as one `IndDecl`**, unconditionally; the
uniform installer (`Arena/Inductives/**`) does the rest.

**The builders read the state directly.**  Since con-leche task #329 its
builders (`nameOfF`, `levelOfF`, `exprOfF`, `cvOfF`, `ruleOfF`,
`validateIndF`, `indBlockOfF`, `declOfF`) take the three table lookups as
parameters (`Lk`), so that its rounds parse can run them over a window's
partly built tables, and `processLineCoreD` is `declOf` then `pushDecl`.  The
serial parse hands them the state's own tables (`StateD.lk`), which is what
this twin reads: the same computation under the twin's own names
(`getDeclD`, `parseCVD`, `parseRuleD`, `validateIndD`,
`installIndD`), each citing the builder it mirrors.

**The `M`/line-number collapse** is described in `Arena/Frontend/Types.lean`:
index errors are `fail (.internal …)` with con-leche's own text and no line
number; a scan error and a record verdict keep theirs, since those are values.
-/
module

public import ConRon.Arena.Frontend.Types
public import ConLeche.Frontend.Scan.Fast
public import ConLeche.Kernel.Level
public import ConRon.Arena.Env

@[expose] public section

namespace ConRon.Arena.Frontend

open ConLeche
open ConLeche.Frontend

/-! ## Fuel

Every walk over the store's DAG takes an explicit `Nat` (DESIGN §8.4).  The
store's own node count bounds every path in it — a child is always interned
before its parent — so this is the one fuel source the frontend needs. -/

/-- con-leche: none — the fuel every DAG walk of the frontend is run at: the
store's node count, which bounds the length of any path through it because a
child is interned before its parent.  con-leche's walks are structural on
`Expr` and need none. -/
def storeFuel : AM Nat := do
  let s ← get
  pure (s.store.nodeCount + 1)

/-! ## The direct parse state -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:56-60 StateD — the direct parse
state: stream-index-keyed tables of HANDLES (a table hit is the same shared
node, named by its handle) and the parsed declarations as `IDeclaration`.
Every field the modeller and the projection rewrite used is gone with them
(task #105).

`names` and `levels` have no default: index 0 of each is the format's implicit
`Name.anonymous` / `Level.zero`, and over handles that means the handle those
two nodes were interned at, which only `StateD.init` can know. -/
structure StateD where
  names : IdTable NIdx
  levels : IdTable LIdx
  exprs : IdTable EIdx := {}
  decls : Array IDeclaration := #[]

/-- con-leche: ConLeche/Frontend/ExportC.lean:66-70 pushDecl — one parsed
record, appended: the decoder keeps the file's records in the file's order.
What used to sit here — the constants-and-heights bookkeeping the in-process
modeller read (`noteDecl`) — is gone with the modeller: `pushDecl` is a plain
state update now. -/
def pushDecl (st : StateD) (d : IDeclaration) : AM StateD :=
  pure { st with decls := st.decls.push d }

/-- con-leche: ConLeche/Frontend/ExportC.lean:72-75 StateD.name — the name
table read. -/
def StateD.name (st : StateD) (i : Nat) : AM NIdx :=
  match st.names.get? i with
  | some n => pure n
  | none => fail (.internal s!"undefined name index {i}")

/-- con-leche: ConLeche/Frontend/ExportC.lean:77-80 StateD.level — the level
table read. -/
def StateD.level (st : StateD) (i : Nat) : AM LIdx :=
  match st.levels.get? i with
  | some l => pure l
  | none => fail (.internal s!"undefined level index {i}")

/-- con-leche: ConLeche/Frontend/ExportC.lean:82-85 StateD.expr — the
expression table read. -/
def StateD.expr (st : StateD) (i : Nat) : AM EIdx :=
  match st.exprs.get? i with
  | some e => pure e
  | none => fail (.internal s!"undefined expr index {i}")

/-- con-leche: ConLeche/Frontend/ExportC.lean:82-85 StateD.expr —
declaration-level expression lookup: the table read.  (The frontend tree-size
budget that used to sit here was retired at con-leche's task #215.) -/
def getDeclD (st : StateD) (i : Nat) : AM EIdx :=
  st.expr i

/-! ## The rebinding test -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:174-176 reboundError — the
rebinding error, named once. -/
def reboundError (what : String) (i : Nat) : String :=
  s!"{what} index {i} is already bound"

/-- con-leche: ConLeche/Frontend/ExportC.lean:178-187 StateD.freshName — the
name test, on a BORROWED state (con-leche measured a 17 % parse-phase
instruction increase when an owned read let the compiler deconstruct the state
before the test). -/
@[noinline] def StateD.freshName (st : @& StateD) (i : Nat) : AM Unit :=
  if st.names.bound i then fail (.internal (reboundError "name" i)) else pure ()

/-- con-leche: ConLeche/Frontend/ExportC.lean:188-189 StateD.freshLevel — the
level test, on a borrowed state. -/
@[noinline] def StateD.freshLevel (st : @& StateD) (i : Nat) : AM Unit :=
  if st.levels.bound i then fail (.internal (reboundError "level" i)) else pure ()

/-- con-leche: ConLeche/Frontend/ExportC.lean:190-191 StateD.freshExpr — the
expression test, on a borrowed state. -/
@[noinline] def StateD.freshExpr (st : @& StateD) (i : Nat) : AM Unit :=
  if st.exprs.bound i then fail (.internal (reboundError "expression" i)) else pure ()

/-! ## Table entries -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:195-199 parseNameEntryD — a
name-table entry: the node is INTERNED and the table records its handle. -/
def parseNameEntryD (st : StateD) (i : Nat) : NameRec → AM StateD
  | .str pre s => do
    let p ← st.name pre
    st.freshName i
    let h ← internNNode (.str p s)
    pure { st with names := st.names.insert i h }
  | .num pre n => do
    let p ← st.name pre
    st.freshName i
    let h ← internNNode (.num p n)
    pure { st with names := st.names.insert i h }

/-- con-leche: ConLeche/Frontend/ExportC.lean:201-205 parseLevelEntryD — a
level-table entry, interned. -/
def parseLevelEntryD (st : StateD) (i : Nat) (r : LevelRec) : AM StateD := do
  st.freshLevel i
  let l ← match r with
    | .succ u => do internLNode (.succ (← st.level u))
    | .max a b => do internLNode (.max (← st.level a) (← st.level b))
    | .imax a b => do internLNode (.imax (← st.level a) (← st.level b))
    | .param n => do internLNode (.param (← st.name n))
  pure { st with levels := st.levels.insert i l }

/-- con-leche: ConLeche/Frontend/ExportC.lean:207-211 parseExprEntryD — an
expression-table entry: the node is interned from the children's HANDLES, and
the packed derived word `Expr.data` computes is computed by `intern` out of
the children's derived columns (task #97a's `EStore.derOfView`).  Binder names
are display data the official kernel's equality and hash ignore; ours are
anonymous on every parsed binder, so handle equality is α-equivalence
downstream, exactly as `==` is in con-leche.

A `const` node's universe arguments are interned as ONE level-list node
(`LsIdx`), which is what keeps the `const` node two words (DESIGN §8.3). -/
def parseExprEntryD (st : StateD) (i : Nat) (r : ExprRec) : AM StateD := do
  st.freshExpr i
  let e ← match r with
    | .bvar k => internE (.bvar k)
    | .sort u => do internE (.sort (← st.level u))
    | .const n us => do
      let nm ← st.name n
      let ls ← us.mapM st.level
      let lsh ← internLsNode ls
      internE (.const nm lsh)
    | .app f a => do internE (.app (← st.expr f) (← st.expr a))
    | .lam ty bd => do
      internE (.lam (← st.expr ty) (← st.expr bd))
    | .forallE ty bd => do
      internE (.forallE (← st.expr ty) (← st.expr bd))
    | .letE ty vl bd => do
      internE (.letE (← st.expr ty) (← st.expr vl) (← st.expr bd))
    | .proj tn ix s => do
      internE (.proj (← st.name tn) ix (← st.expr s))
    | .natVal n => internE (.lit (.natVal n))
    | .strVal s => internE (.lit (.strVal s))
  pure { st with exprs := st.exprs.insert i e }

/-! ## Declaration records -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:215-221 cvOfF — a
declaration's common data; the type stays a handle. -/
def parseCVD (st : StateD) (cv : CVRec) : AM IConstantVal := do
  let name ← st.name cv.name
  let ty ← getDeclD st cv.type
  pure { name := name
         levelParams := ← cv.levelParams.mapM st.name
         type := ty }

/-- con-leche: ConLeche/Frontend/ExportC.lean:223-229 indPiTeleLen — the
syntactic Π-telescope length of a declared type: official counts a
constructor's binders by walking `is_pi` without reducing, and the count past
the parameters is the `numFields` of the constructor it generates. -/
def indPiTeleLen : Nat → EIdx → AM Nat
  | 0, _ => fail (.internal "fuel exhausted: indPiTeleLen")
  | fuel + 1, h => do
    match ← view h with
    | .forallE _ b => pure ((← indPiTeleLen fuel b) + 1)
    | _ => pure 0

/-- con-leche: ConLeche/Frontend/ExportC.lean:231-233 ruleOfF — one recursor
rule of an inductive record, resolved.  The install-computed fields carry
con-leche's own parse placeholders. -/
def parseRuleD (st : StateD) (ru : RuleRec) : AM IRecRule := do
  pure (IRecRule.mk (← st.name ru.ctor) ru.nfields .plain (← getDeclD st ru.rhs))

/-- con-leche: ConLeche/Frontend/ExportC.lean:235-371 validateIndF — an
inductive record, VALIDATED: the half of the record's processing that reads
the state and changes nothing.  Every guard, every verdict and every message
is con-leche's; what changed is that a name comparison is a handle comparison
(sound because `denoteN` is injective — task #97a's `denoteN_inj`, DESIGN
§8.3's exactness obligation) and that a structural read of a type is a
`view`.

The two `for`/`mut` loops are con-leche's own; they run over a block's records
— a handful — and not over the linear store, so DESIGN §8.4's "explicit tail
recursion" rule (lesson 16, about large linear state) does not bite.  The Rust
writes them as `for` loops too. -/
def validateIndD (st : @& StateD) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) : AM (RecordVerdict ⊕ (List IndCtorRec × Nat)) := do
  -- an `unsafe inductive` is DECLINED, not an error
  if tys.any (·.isUnsafe) then
    return .inl (.declined "unsafe inductive declaration")
  -- THE DECLARED PARAMETER COUNT: well defined for the block exactly when its
  -- type records AGREE on it
  let nPs := tys.map (·.numParams)
  let nPd := nPs.head?.getD 0
  unless nPs.all (· == nPd) do
    return .inl (.declined "inductive block whose type records disagree on numParams")
  -- THE BLOCK'S REDUNDANT FIELDS: consistency checks between the stream's own
  -- fields, whose verdict is `.invalid` — the fold never sees such a block
  let tyNames ← tys.mapM fun t => st.name t.cv.name
  let tyTypes ← tys.mapM fun t => getDeclD st t.cv.type
  let listed ← tys.mapM fun t => t.ctors.mapM st.name
  let ctorNames ← cts.mapM fun c => st.name c.cv.name
  let flat := listed.flatten
  unless flat.Nodup do
    return .inl (.invalid "duplicate constructor name in an inductive type's ctors")
  unless flat.length == cts.length do
    return .inl (.invalid s!"the inductive block lists {flat.length} constructors \
      and carries {cts.length} constructor records")
  let ctorIx : Std.HashMap NIdx Nat :=
    (ctorNames.foldl (fun (mi : Std.HashMap NIdx Nat × Nat) n =>
      (mi.1.insert n mi.2, mi.2 + 1)) ({}, 0)).1
  let ctsA := cts.toArray
  let fuel ← storeFuel
  -- the constructors IN THE BLOCK'S OWN ORDER, `types[].ctors` in type order
  let mut ordered : Array IndCtorRec := #[]
  for tn in tyNames.zip listed do
    let (T, ns) := tn
    let mut j := 0
    for n in ns do
      let some k := ctorIx[n]? | return .inl (.invalid s!"No such constructor {← readName n}")
      let some c := ctsA[k]? | return .inl (.invalid s!"No such constructor {← readName n}")
      if let some ci := c.cidx then
        unless ci == j do
          return .inl (.invalid s!"constructor {← readName n} declares cidx {ci}; it is \
            constructor {j} of {← readName T}")
      if let some iw := c.induct then
        let iwn ← st.name iw
        unless iwn == T do
          return .inl (.invalid s!"constructor {← readName n} declares induct \
            {← readName iwn}; it is a constructor of {← readName T}")
      -- `numFields`: official counts the constructor's own Π binders without
      -- reducing and stores the count past the parameters
      let cty ← getDeclD st c.cv.type
      let tele ← indPiTeleLen fuel cty
      unless nPd + c.numFields == tele do
        return .inl (.invalid s!"constructor {← readName n} declares {c.numFields} \
          fields at {nPd} parameters; its type has {tele} binders")
      ordered := ordered.push c
      j := j + 1
  let cts := ordered.toList
  -- the recursor records: the counts the GENERATED recursor carries.  NOT at a
  -- NESTED block.
  let nested := tys.any (·.numNested != 0)
  let nTypes := tys.length
  let nCtors := cts.length
  for r in (if nested then [] else rcs) do
    let rn ← st.name r.cv.name
    unless r.numParams == nPd do
      return .inl (.invalid s!"recursor {← readName rn} declares {r.numParams} \
        parameters; the block declares {nPd}")
    unless r.numMotives == nTypes do
      return .inl (.invalid s!"recursor {← readName rn} declares {r.numMotives} \
        motives; the block has {nTypes} inductive types")
    unless r.numMinors == nCtors do
      return .inl (.invalid s!"recursor {← readName rn} declares {r.numMinors} \
        minor premises; the block has {nCtors} constructors")
    -- `numIndices` of `T.rec` is what is left of `T`'s own telescope once the
    -- parameters are peeled
    match ← viewN rn with
    | .str T "rec" =>
      for tt in tyNames.zip tyTypes do
        if tt.1 == T then
          match ← piSortTeleLen? fuel tt.2 with
          | some n =>
            unless nPd + r.numIndices == n do
              return .inl (.invalid s!"recursor {← readName rn} declares \
                {r.numIndices} indices; {← readName T} has {n - nPd} at {nPd} parameters")
          | none => pure ()
    | _ => pure ()
  return .inr (cts, nPd)

/-- con-leche: ConLeche/Frontend/ExportC.lean:373-390 indBlockOfF — an
inductive record, INSTALLED: the block's constants, pushed as one `IndDecl`.
Every change to the state a validated inductive record makes is here.

con-leche's own `installIndD` used to build the projection-owner table and run
the in-process modeller here (`registerProjOwners`, `InModel.generate` through
the `wants`/`inModel` gate); the uniform installer (task #105,
`Arena/Inductives/**`, the kernel lane's) replaces both, so the parser has
nothing left to do but push the block.

**EVERY BLOCK IS AN `indDecl`**: the fold recognises a pinned block by its
members' names (`basisNameHit`) and its check compares it with the pin. -/
def installIndD (st : StateD) (tys : List IndTypeRec)
    (cts : List IndCtorRec) (rcs : List IndRecRec) (nPd : Nat) :
    AM StateD := do
  let types ← tys.mapM fun t => do
    pure (IConstantInfo.indInfo (← parseCVD st t.cv) {})
  let ctors ← cts.mapM fun c => do
    pure (IConstantInfo.ctorInfo (← parseCVD st c.cv) c.numParams c.numFields)
  let recs ← rcs.mapM fun r => do
    let rules ← r.rules.mapM (parseRuleD st)
    pure (IConstantInfo.recInfo (← parseCVD st r.cv)
      (r.numParams + r.numMotives + r.numMinors + r.numIndices)
      (r.numParams + r.numMotives + r.numMinors) r.k rules)
  let block := types ++ ctors ++ recs
  pushDecl st (.indDecl block nPd)

/-- con-leche: ConLeche/Frontend/ExportC.lean:450-455 processLineCoreD — the
record's own semantics: the declaration kinds, producing `IDeclaration`
records.  Every branch, guard and error string is con-leche's; the
projection-function rewrite that used to run in the `.defn`/`.thm` arms is
gone with the modeller (task #105), so every arm now pushes the record it
parsed, unconditionally. -/
def processLineCoreD (st : StateD) (d : DeclRec) :
    AM (StateD ⊕ RecordVerdict) := do
  match d with
  | .ax cvr isUnsafe =>
    let cvp ← parseCVD st cvr
    if isUnsafe then
      return .inr (.declined "unsafe axiom")
    -- `Quot.sound` is the FOLD's: the axiom record is forwarded like any other
    return .inl (← pushDecl st (.axiomDecl cvp))
  | .defn cvr value hints safety =>
    let cvp ← parseCVD st cvr
    match safety with
    | "safe" =>
      let vl ← getDeclD st value
      let h : ReducibilityHint := match hints with
        | .«abbrev» => .«abbrev»
        | .«opaque» => .«opaque»
        | .regular n => .regular n
      return .inl (← pushDecl st (.defnDecl cvp vl h))
    | s => return .inr (.declined s!"definition with safety {Display.str s}")
  | .thm cvr value =>
    let cvp ← parseCVD st cvr
    let vl ← getDeclD st value
    return .inl (← pushDecl st (.thmDecl cvp vl))
  | .opaq cvr value isUnsafe =>
    let cvp ← parseCVD st cvr
    if isUnsafe then
      return .inr (.declined "unsafe opaque declaration")
    let vl ← getDeclD st value
    return .inl (← pushDecl st (.opaqueDecl cvp vl))
  | .quot cvr kind =>
    -- ONE RECORD PER `#QUOT` LINE: the constant as the file declares it, at
    -- the kind the file declares it at
    let cv ← parseCVD st cvr
    let qk ← match kind with
      | "type" => pure QuotKind.type
      | "ctor" => pure QuotKind.ctor
      | "lift" => pure QuotKind.lift
      | "ind" => pure QuotKind.ind
      | k => fail (.internal s!"unknown quotient kind {Display.str k}")
    return .inl (← pushDecl st (.quotDecl qk cv))
  | .ind tys cts rcs =>
    match ← validateIndD st tys cts rcs with
    | .inl v => pure (.inr v)
    | .inr (cts, nPd) => pure (.inl (← installIndD st tys cts rcs nPd))

/-- con-leche: ConLeche/Frontend/ExportC.lean:457-464 applyDeclD — a
declaration record.  `sorryAx` is the FOLD's: the parse forwards every
declaration record, the `sorryAx` axiom record included. -/
def applyDeclD (st : StateD) (d : DeclRec) :
    AM (StateD ⊕ RecordVerdict) :=
  processLineCoreD st d

/-- con-leche: ConLeche/Frontend/ExportC.lean:466-477 applyRecord — one record
applied to the parse state.  The scanned record is con-leche's own
(`Scan/Fast.lean`, reused); what this does with it is resolve the indices and
INTERN the nodes.  The header and a blank line change nothing (where they may
stand is `applyLine`'s). -/
def applyRecord (st : StateD) (r : LineRec) :
    AM (StateD ⊕ RecordVerdict) :=
  match r with
  | .expr i e => do pure (.inl (← parseExprEntryD st i e))
  | .name i n => do pure (.inl (← parseNameEntryD st i n))
  | .level i l => do pure (.inl (← parseLevelEntryD st i l))
  | .decl d => applyDeclD st d
  | .header => pure (.inl st)
  | .blank => pure (.inl st)

/-- con-leche: ConLeche/Frontend/ExportC.lean:479-487 LineRec.placed — where a
line may stand: the format's first line is its `meta` header (`first`), and
every later line is a record — the header only first, every other record never
first, a blank line nowhere. -/
def lineRecPlaced (first : Bool) : LineRec → Bool
  | .header => first
  | .blank => false
  | _ => !first

/-- con-leche: ConLeche/Frontend/ExportC.lean:489-493 LineRec.misplaced — what a
line that stands where it may not is told. -/
def lineRecMisplaced : LineRec → String
  | .header => "a meta line after the first line"
  | .blank => "a blank line"
  | _ => "the first line is not the meta header"

/-- con-leche: ConLeche/Frontend/ExportC.lean:495-499 applyLine — THE SEMANTIC
LAYER: one scanned line, after `lineNo` lines, applied to the parse state if it
stands where it may. -/
def applyLine (st : StateD) (r : LineRec) (lineNo : Nat) :
    AM (StateD ⊕ RecordVerdict) :=
  if lineRecPlaced (lineNo == 0) r then applyRecord st r
  else fail (.internal (lineRecMisplaced r))

/-! ## The line feed and the drivers -/

/-- con-leche: ConLeche/Frontend/ExportC.lean:503-507 ParseResultD — the direct
parse result: the declarations over handles.  No arena conversion: the handles
already point into the persistent tier the fold will read.  con-leche's
receipts (the projection rewrites, the modelled blocks, the generated-record
counts) are gone with the modeller (task #105). -/
structure ParseResultD where
  /-- the FILE's declaration records, in the file's order -/
  decls : Array IDeclaration

/-- con-leche: ConLeche/Frontend/ExportC.lean:509-511 StateD.init — the initial
parse state.  Over handles it is monadic: index 0 of the name table is the
format's implicit `Name.anonymous` and index 0 of the level table its
`Level.zero`, and those are the handles those two nodes intern at — in the
PERSISTENT tier, which is the tier the whole parse appends to (`scratchOn` is
`false` on `EStore.empty` and the parse never enables the scratch one). -/
def StateD.init : AM StateD := do
  let n0 ← internNNode .anonymous
  let l0 ← internLNode .zero
  pure { names := IdTable.singleton n0, levels := IdTable.singleton l0 }

/-- con-leche: ConLeche/Frontend/ExportC.lean:527-528 ParseResultD.ofState —
the result: the file's records, in the file's order. -/
def ParseResultD.ofState (st : StateD) : ParseResultD :=
  ⟨st.decls⟩

/-- con-leche: ConLeche/Frontend/ExportC.lean:531-542 applyFinalLine — scan and
apply the LAST line of a stream, the one no newline ends, after `lineNo` lines.
A syntactic failure is reported at its offset in the line.  con-leche calls `scanLineSpec` and lets
`@[csimp]` substitute `scanLineFwd`; this calls `scanLineFwd`, which is what
both binaries execute. -/
def applyFinalLine (st : StateD) (b : @& ByteArray) (i : USize)
    (lineNo : Nat) : AM (Except (CheckError × Nat) StateD) := do
  match scanLineFwd b i with
  | .err e => pure (.error (.internal (ScanErr.render ⟨e.offset - i.toNat, e.what⟩), lineNo + 1))
  | .ok r _ =>
    match ← applyLine st r lineNo with
    | .inr v => pure (.error (v.toError, lineNo + 1))
    | .inl st => pure (.ok st)

/-- con-leche: ConLeche/Frontend/ExportC.lean:544-578 feedChunk — every
COMPLETE line of the chunk from `i`, applied in order: the state, the line
count, and where the incomplete tail begins.  A line the chunk cut in half is
told from a malformed one by whether the rest of the chunk holds a newline at
all.  The loop's advance is the line, and the line reader never returns a
position at or before its own start, so the remaining byte count is the
termination measure. -/
def feedChunk (st : StateD) (b : @& ByteArray) (i : USize)
    (lineNo : Nat) : AM (Except (CheckError × Nat) (StateD × Nat × USize)) :=
  if _h : i < b.usize then
    match scanLineFwd b i with
    | .err e =>
      if newlineFrom b i then
        pure (.error (.internal (ScanErr.render ⟨e.offset - i.toNat, e.what⟩), lineNo + 1))
      else pure (.ok (st, lineNo, i))
    | .ok r j =>
      -- `0` is the recogniser's "the buffer ended before a newline did": these
      -- bytes are an incomplete tail, not a line.  (A `USize` numeral must be
      -- COMPARED, not matched.)
      if j == 0 then pure (.ok (st, lineNo, i))
      else do
        match ← applyLine st r lineNo with
        | .inr v => pure (.error (v.toError, lineNo + 1))
        | .inl st =>
          if _hj : i < j then feedChunk st b j (lineNo + 1)
          else pure (.error (.internal "the line scanner made no progress", lineNo + 1))
  else pure (.ok (st, lineNo, i))
termination_by b.size - i.toNat
decreasing_by
  exact Nat.sub_lt_sub_left (usizeInBounds b i _h) (USize.lt_iff_toNat_lt.mp _hj)

/-- con-leche: ConLeche/Frontend/ExportC.lean:580-581 chunkSize — how many
bytes the streaming driver asks for at a time. -/
def chunkSize : USize := 4 * 1024 * 1024

/-- con-leche: ConLeche/Frontend/ExportC.lean:583-591 sizeError — THE SIZE
GUARD: the byte reader addresses its buffer by machine word, so an input of
`USize.size` bytes or more is refused before any of it is read. -/
def sizeError : CheckError × Nat :=
  (.notImplemented s!"an input of {USize.size} bytes or more", 0)

/-- con-leche: ConLeche/Frontend/ExportC.lean:593-605 parseBytes — wholesale
direct parse of a byte buffer: the whole input fed at once, then the last
line.  The specification the streaming parse is proved equal to. -/
def parseBytes (b : ByteArray) : AM (Except (CheckError × Nat) ParseResultD) := do
  if b.size ≥ USize.size then return .error sizeError
  match ← feedChunk (← StateD.init) b 0 0 with
  | .error e => pure (.error e)
  | .ok (st, lineNo, tail) =>
    if tail < b.usize then
      match ← applyFinalLine st b tail lineNo with
      | .error e => pure (.error e)
      | .ok st => pure (.ok (.ofState st))
    else
      pure (.ok (.ofState st))

/-- con-leche: ConLeche/Frontend/ExportC.lean:625-635 chunkStep — one chunk of
the stream, applied: the carried incomplete tail is put in front of the new
bytes, every complete line of the buffer is fed, and the new incomplete tail is
cut off for the next chunk. -/
def chunkStep (st : StateD) (carry : ByteArray) (lineNo total : Nat)
    (buf0 : ByteArray) :
    AM (Except (CheckError × Nat) (StateD × ByteArray × Nat × Nat)) := do
  if total + buf0.size ≥ USize.size then return .error sizeError
  let buf := if carry.isEmpty then buf0 else carry ++ buf0
  match ← feedChunk st buf 0 lineNo with
  | .error e => pure (.error e)
  | .ok (st, lineNo, tail) =>
    pure (.ok (st, buf.extract tail.toNat buf.size, lineNo, total + buf0.size))

/-- con-leche: ConLeche/Frontend/ExportC.lean:635-642 chunkFinish — the end of
the stream: the carried tail, if any, is its last line. -/
def chunkFinish (st : StateD) (carry : ByteArray) (lineNo : Nat) :
    AM (Except (CheckError × Nat) ParseResultD) := do
  if carry.isEmpty then return .ok (.ofState st)
  match ← applyFinalLine st carry 0 lineNo with
  | .error e => pure (.error e)
  | .ok st => pure (.ok (.ofState st))

/-- con-leche: ConLeche/Frontend/ExportC.lean:650-669 parseChunks — THE
STREAMING PARSE, PURELY: `chunkStep` folded over a list of chunks,
`chunkFinish` at its end — what the driver's read loop does with the chunks its
handle hands out, minus the reads.  The list is folded whole: an empty chunk
contributes nothing and the fold goes on.

con-leche's `where go` is a top-level `parseChunksGo` here, because the arena's
Rust twin is a loop of its own and a `where` clause has no name to cite. -/
def parseChunksGo (st : StateD) (carry : ByteArray) (lineNo total : Nat) :
    List ByteArray → AM (Except (CheckError × Nat) ParseResultD)
  | [] => chunkFinish st carry lineNo
  | c :: cs => do
    match ← chunkStep st carry lineNo total c with
    | .error e => pure (.error e)
    | .ok (st, carry, lineNo, total) => parseChunksGo st carry lineNo total cs

/-- con-leche: ConLeche/Frontend/ExportC.lean:650-669 parseChunks — the
streaming parse's entry point: the initial state, then `parseChunksGo` above. -/
def parseChunks (chunks : List ByteArray) : AM (Except (CheckError × Nat) ParseResultD) := do
  parseChunksGo (← StateD.init) .empty 0 0 chunks

/-- con-leche: none — the line number folded into the message.  con-leche
reports a parse failure as `(CheckError, lineNo)` and `Main.lean` prints the
pair; `Arena/Main.lean`'s seam is `Except CheckError Nat` and has no position
channel, so the number goes into the text instead.  The KIND — hence the exit
code — is untouched. -/
def atLine : CheckError → Nat → CheckError
  | .notImplemented w, n => .notImplemented s!"{w} (line {n})"
  | .invalid w, n => .invalid s!"{w} (line {n})"
  | .internal w, n => .internal s!"{w} (line {n})"
  | .native w, n => .native s!"{w} (line {n})"

end ConRon.Arena.Frontend

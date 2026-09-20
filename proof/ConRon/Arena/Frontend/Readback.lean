/-
# `ConRon.Arena.Frontend.Readback` — the declaration layer's denotation, and
its inverse (DESIGN.md §8.2, task #97e part 2)

`Arena/Denote.lean` reads a *term* handle back as the con-leche value it
stands for (`denoteE`, `denoteN`, `denoteL`, `denoteLs`).  This module lifts
that, field for field, to the declaration layer `Arena/Env.lean` mirrors —
`IConstantVal ↦ ConstantVal`, `IRecRule ↦ RecRule`, `IIndCaps ↦ IndCaps`,
`IProjTable ↦ ProjTable`, `IConstantInfo ↦ ConstantInfo`, `IDeclaration ↦
Declaration` — and adds the **opposite** direction, which interns a transient
con-leche value into the store.

**Why both directions exist, and what they are for.**  DESIGN §8.2's parser
tier is the exactness statement `denoteDecls (Arena.parse chunks) =
parseChunks chunks`, whose left-hand side is exactly `denoteDecls` below: the
denotation is the *specification side* of the frontend, written here once so
that P3 states it rather than inventing it.  The intern direction is what a
**delegation at a seam** needs: DESIGN §8.2 puts the in-process modeller
outside the verified surface, and the cheapest exact instantiation of that
seam is con-leche's own generator run on the block's denotation, with its
generated records interned back (`Arena/Frontend/InModel.lean`).  The same
pair serves `ProjRec`'s two block recognisers until P2d twins them.

**BOTH directions are MEMOISED, and the memo is not an optimisation.**  A
handle DAG's denotation is a `ConLeche.Expr` whose subterms are shared by
Lean's own pointers — that is what con-leche's parse builds and what its
functions are fast on — and `Arena/Denote.lean`'s `denoteE` recurses at each
child independently, so it re-denotes a shared subterm once per occurrence and
UNFOLDS the DAG.  On con-leche's own `tests/e2e/tower_struct.ndjson`, whose
expression table doubles at every second entry, that is `2^60` nodes and the
readback does not finish.  `denoteEGo` below threads a `Std.HashMap EIdx Expr`
and rebuilds each node once, so the value it returns is `denoteE`'s — the same
`Expr` — held with the same sharing con-leche's parse gives it.
(`denoteEShared st h = denoteE st h` is the exactness obligation this owes P3;
the two differ only in how many times the tree is built.)  The intern
direction carries the mirror memo, for the mirror reason.

**The readback is bounded by its callers, too.**  Nothing here runs over the
stream: `readCIList` is called on ONE inductive block at a time — a type
former, its constructors and its recursors — and `internDecl` on the records
one block's model generates.  A walk over the persistent tier is never a
readback; it is a `view` walk (`Arena/ExprOps.lean` does them all).

**`internExpr` carries a memo, and it must.**  A handle DAG denotes to a
`ConLeche.Expr` *tree* whose subterms are shared by Lean's own pointers, and
re-interning it structurally would walk each shared subterm once per
occurrence.  The memo is a `Std.HashMap ConLeche.Expr EIdx` — con-leche's
`Expr` carries its hash in its computed `data` word and its `BEq` has the
physical-equality shortcut, so a probe is `O(1)` on a shared subterm — and it
is threaded explicitly rather than put in `AState`, because it lives for one
block and `Memos` is DESIGN §8.4's per-call record.

**The name lookup is PURE** (`nameHandle?`).  A con-leche `Name` is mapped to
its handle by probing the name store's cons table, which is `NStore.find?` and
needs no monad.  A name the store has never interned has no handle — and no
declaration, since every declared name was interned when it was parsed — so
`none` is the right answer and not a failure.  That is what lets the
delegation build con-leche's own `Name → …` context functions, which are
plain functions and cannot be monadic.
-/
import ConRon.Arena.Env

namespace ConRon.Arena.Frontend

open ConLeche
open ConRon.Arena

/-! ## The pure name lookup -/

/-- con-leche: none — the handle a transient `Name` was interned at, by
probing the name store's cons table at each component; `none` when the store
has never seen it (then no declaration carries it either, `denoteN` being
injective).  Pure, so con-leche's `Name`-keyed context functions can be built
from it. -/
def nameHandle? (st : NStore) : ConLeche.Name → Option NIdx
  | .anonymous => st.find? .anonymous
  | .str p s =>
    match nameHandle? st p with
    | some hp => st.find? (.str hp s)
    | none => none
  | .num p n =>
    match nameHandle? st p with
    | some hp => st.find? (.num hp n)
    | none => none

/-! ## The denotation of the declaration layer

One function per `Arena/Env.lean` type, field for field.  `none` is a dangling
handle, which the checker never builds; the monadic wrappers below turn it
into the `internal` error every other dangling read raises. -/

/-- con-leche: none — the denotation of a name-handle list. -/
def denoteNList (st : NStore) : List NIdx → Option (List ConLeche.Name)
  | [] => some []
  | h :: hs =>
    match denoteN st h, denoteNList st hs with
    | some x, some xs => some (x :: xs)
    | _, _ => none

/-- con-leche: none — the denotation of an expression-handle list. -/
def denoteEList (st : EStore) : List EIdx → Option (List Expr)
  | [] => some []
  | h :: hs =>
    match denoteE st h, denoteEList st hs with
    | some x, some xs => some (x :: xs)
    | _, _ => none

/-- con-leche: none — the denotation of an expression-handle array. -/
def denoteEArray (st : EStore) (hs : Array EIdx) : Option (Array Expr) :=
  match denoteEList st hs.toList with
  | some xs => some xs.toArray
  | none => none

/-- con-leche: none — the denotation of a `ConstantVal` over handles
(`Arena/Env.lean`'s `IConstantVal`). -/
def denoteCV (st : EStore) (cv : IConstantVal) : Option ConstantVal :=
  match denoteN st.ns cv.name, denoteNList st.ns cv.levelParams,
        denoteE st cv.type with
  | some n, some lps, some ty => some ⟨n, lps, ty⟩
  | _, _, _ => none

/-- con-leche: none — the denotation of a recursor rule's firing mode. -/
def denoteFire (st : EStore) : IRecRuleFire → Option RecRuleFire
  | .inert => some .inert
  | .plain => some .plain
  | .nested lvls pins =>
    match denoteLList st.ls lvls, denoteEList st pins with
    | some ls, some ps => some (.nested ls ps)
    | _, _ => none

/-- con-leche: none — the denotation of one recursor rule. -/
def denoteRule (st : EStore) (rl : IRecRule) : Option RecRule :=
  match denoteN st.ns rl.ctor, denoteFire st rl.fire, denoteE st rl.rhs with
  | some c, some f, some r =>
    some ⟨c, rl.nfields, rl.ctorParams, f, r, rl.k, rl.eta, rl.paramsBlind⟩
  | _, _, _ => none

/-- con-leche: none — the denotation of a rule list. -/
def denoteRules (st : EStore) : List IRecRule → Option (List RecRule)
  | [] => some []
  | r :: rs =>
    match denoteRule st r, denoteRules st rs with
    | some x, some xs => some (x :: xs)
    | _, _ => none

/-- con-leche: none — the denotation of an inductive's capabilities.  `sortZ`
is con-leche's own `PropWhen` on both sides (`Arena/Env.lean`'s note: the
store's binder metadata already carries one). -/
def denoteCaps (st : EStore) (c : IIndCaps) : Option IndCaps :=
  match denoteN st.ns c.etaCtor with
  | some ct =>
    some ⟨c.eta, ct, c.etaParams, c.etaFields, c.unitlike, c.unitParams,
          c.ruleK, c.sortZ⟩
  | none => none

/-- con-leche: none — the denotation of a projection table.  `tableName` has
no counterpart: con-leche recomputes it (`Arena/Env.lean`'s one-added-field
note), so the denotation simply drops it. -/
def denoteProjTable (st : EStore) (t : IProjTable) : Option ProjTable :=
  match denoteN st.ns t.structName, denoteNList st.ns t.levelParams,
        denoteN st.ns t.ctor with
  | some sn, some lps, some c =>
    match denoteL st.ls t.structSort, denoteEArray st t.bodies,
          denoteLList st.ls t.guards with
    | some ss, some bs, some gs =>
      some ⟨sn, lps, t.numParams, c, t.numFields, ss, bs, gs, t.off⟩
    | _, _, _ => none
  | _, _, _ => none

/-- con-leche: none — the denotation of a stored constant. -/
def denoteCI (st : EStore) : IConstantInfo → Option ConstantInfo
  | .axiomInfo v => (denoteCV st v).map .axiomInfo
  | .defnInfo v e h =>
    match denoteCV st v, denoteE st e with
    | some cv, some x => some (.defnInfo cv x h)
    | _, _ => none
  | .thmInfo v e =>
    match denoteCV st v, denoteE st e with
    | some cv, some x => some (.thmInfo cv x)
    | _, _ => none
  | .indInfo v c =>
    match denoteCV st v, denoteCaps st c with
    | some cv, some caps => some (.indInfo cv caps)
    | _, _ => none
  | .ctorInfo v nP nF => (denoteCV st v).map (fun cv => .ctorInfo cv nP nF)
  | .recInfo v mI rP rs =>
    match denoteCV st v, denoteRules st rs with
    | some cv, some rules => some (.recInfo cv mI rP rules)
    | _, _ => none
  | .projInfo t => (denoteProjTable st t).map .projInfo

/-- con-leche: none — the denotation of a block's constants. -/
def denoteCIList (st : EStore) : List IConstantInfo → Option (List ConstantInfo)
  | [] => some []
  | c :: cs =>
    match denoteCI st c, denoteCIList st cs with
    | some x, some xs => some (x :: xs)
    | _, _ => none

/-- con-leche: none — the denotation of a declaration record.  **This is the
left-hand side of DESIGN §8.2's parser-tier statement** `denoteDecls
(Arena.parse chunks) = parseChunks chunks`. -/
def denoteDecl (st : EStore) : IDeclaration → Option Declaration
  | .axiomDecl v => (denoteCV st v).map .axiomDecl
  | .defnDecl v e h =>
    match denoteCV st v, denoteE st e with
    | some cv, some x => some (.defnDecl cv x h)
    | _, _ => none
  | .thmDecl v e =>
    match denoteCV st v, denoteE st e with
    | some cv, some x => some (.thmDecl cv x)
    | _, _ => none
  | .opaqueDecl v e =>
    match denoteCV st v, denoteE st e with
    | some cv, some x => some (.opaqueDecl cv x)
    | _, _ => none
  | .basisDecl k => some (.basisDecl k)
  | .indDecl block nP =>
    (denoteCIList st block).map (fun b => .indDecl b nP)
  | .quotDecl k v => (denoteCV st v).map (.quotDecl k)

/-! ## The denotation, MEMOISED — what is actually executed

The `denote*` family above is the SPECIFICATION: one equation per field, with
no state, which is the shape P3 states the parser tier in.  What the
delegations below run is this family, which threads a `Std.HashMap EIdx Expr`
so that a shared subterm is rebuilt once.  It is pure — `EStore.view` is — so
it can still be handed to con-leche's own `Name → … → Expr` context functions,
which are plain functions and could not take a monad.  See the module note for
why the memo is load-bearing rather than a speed-up. -/

/-- con-leche: none — the readback memo: the `Expr` each handle denotes, so
that the denotation of a DAG is built with the sharing the DAG has. -/
abbrev DMemo := Std.HashMap EIdx Expr

/-- con-leche: none — `denoteE` with the memo: the same value, built once per
node.  The fuel bounds the DAG's DEPTH (a memo hit returns at once), which the
store's node count bounds. -/
def denoteEGo (st : EStore) (m : DMemo) : Nat -> EIdx -> Option (DMemo × Expr)
  | 0, _ => none
  | fuel + 1, h =>
    match m[h]? with
    | some e => some (m, e)
    | none =>
      match st.view h with
      | none => none
      | some (.bvar k) => let e := Expr.bvar k; some (m.insert h e, e)
      | some (.lit l) => let e := Expr.lit l; some (m.insert h e, e)
      | some (.sort u) =>
        match denoteL st.ls u with
        | some l => let e := Expr.sort l; some (m.insert h e, e)
        | none => none
      | some (.const n us) =>
        match denoteN st.ns n, denoteLs st.lss us with
        | some nm, some ls => let e := Expr.const nm ls; some (m.insert h e, e)
        | _, _ => none
      | some (.fvar k ty) =>
        match denoteEGo st m fuel ty with
        | some (m, t) => let e := Expr.fvar k t; some (m.insert h e, e)
        | none => none
      | some (.app f a) =>
        match denoteEGo st m fuel f with
        | some (m, ef) =>
          match denoteEGo st m fuel a with
          | some (m, ea) => let e := Expr.app ef ea; some (m.insert h e, e)
          | none => none
        | none => none
      | some (.lam ty b bi) =>
        match denoteEGo st m fuel ty with
        | some (m, et) =>
          match denoteEGo st m fuel b with
          | some (m, eb) => let e := Expr.lam et eb bi; some (m.insert h e, e)
          | none => none
        | none => none
      | some (.forallE ty b bi) =>
        match denoteEGo st m fuel ty with
        | some (m, et) =>
          match denoteEGo st m fuel b with
          | some (m, eb) => let e := Expr.forallE et eb bi; some (m.insert h e, e)
          | none => none
        | none => none
      | some (.letE ty v b) =>
        match denoteEGo st m fuel ty with
        | some (m, et) =>
          match denoteEGo st m fuel v with
          | some (m, ev) =>
            match denoteEGo st m fuel b with
            | some (m, eb) => let e := Expr.letE et ev eb; some (m.insert h e, e)
            | none => none
          | none => none
        | none => none
      | some (.proj n i sub) =>
        match denoteN st.ns n, denoteEGo st m fuel sub with
        | some nm, some (m, es) => let e := Expr.proj nm i es; some (m.insert h e, e)
        | _, _ => none

/-- con-leche: none — `denoteE` at a fresh memo: the value of `denoteE`, held
with the DAG's own sharing. -/
def denoteEShared (st : EStore) (h : EIdx) : Option Expr :=
  match denoteEGo st (∅ : DMemo) (st.nodeCount + 1) h with
  | some (_, e) => some e
  | none => none

/-- con-leche: none — the memoised denotation of an expression-handle list. -/
def denoteEListGo (st : EStore) (m : DMemo) :
    List EIdx -> Option (DMemo × List Expr)
  | [] => some (m, [])
  | h :: hs =>
    match denoteEGo st m (st.nodeCount + 1) h with
    | some (m, e) =>
      match denoteEListGo st m hs with
      | some (m, es) => some (m, e :: es)
      | none => none
    | none => none

/-- con-leche: none — the memoised denotation of a `ConstantVal`. -/
def denoteCVGo (st : EStore) (m : DMemo) (cv : IConstantVal) :
    Option (DMemo × ConstantVal) :=
  match denoteN st.ns cv.name, denoteNList st.ns cv.levelParams,
        denoteEGo st m (st.nodeCount + 1) cv.type with
  | some n, some lps, some (m, ty) => some (m, ⟨n, lps, ty⟩)
  | _, _, _ => none

/-- con-leche: none — the memoised denotation of a rule's firing mode. -/
def denoteFireGo (st : EStore) (m : DMemo) :
    IRecRuleFire -> Option (DMemo × RecRuleFire)
  | .inert => some (m, .inert)
  | .plain => some (m, .plain)
  | .nested lvls pins =>
    match denoteLList st.ls lvls, denoteEListGo st m pins with
    | some ls, some (m, ps) => some (m, .nested ls ps)
    | _, _ => none

/-- con-leche: none — the memoised denotation of one recursor rule. -/
def denoteRuleGo (st : EStore) (m : DMemo) (rl : IRecRule) :
    Option (DMemo × RecRule) :=
  match denoteN st.ns rl.ctor, denoteFireGo st m rl.fire with
  | some c, some (m, f) =>
    match denoteEGo st m (st.nodeCount + 1) rl.rhs with
    | some (m, r) =>
      some (m, ⟨c, rl.nfields, rl.ctorParams, f, r, rl.k, rl.eta, rl.paramsBlind⟩)
    | none => none
  | _, _ => none

/-- con-leche: none — the memoised denotation of a rule list. -/
def denoteRulesGo (st : EStore) (m : DMemo) :
    List IRecRule -> Option (DMemo × List RecRule)
  | [] => some (m, [])
  | r :: rs =>
    match denoteRuleGo st m r with
    | some (m, x) =>
      match denoteRulesGo st m rs with
      | some (m, xs) => some (m, x :: xs)
      | none => none
    | none => none

/-- con-leche: none — the memoised denotation of a projection table. -/
def denoteProjTableGo (st : EStore) (m : DMemo) (t : IProjTable) :
    Option (DMemo × ProjTable) :=
  match denoteN st.ns t.structName, denoteNList st.ns t.levelParams,
        denoteN st.ns t.ctor with
  | some sn, some lps, some c =>
    match denoteL st.ls t.structSort, denoteEListGo st m t.bodies.toList,
          denoteLList st.ls t.guards with
    | some ss, some (m, bs), some gs =>
      some (m, ⟨sn, lps, t.numParams, c, t.numFields, ss, bs.toArray, gs, t.off⟩)
    | _, _, _ => none
  | _, _, _ => none

/-- con-leche: none — the memoised denotation of a stored constant. -/
def denoteCIGo (st : EStore) (m : DMemo) :
    IConstantInfo -> Option (DMemo × ConstantInfo)
  | .axiomInfo v =>
    match denoteCVGo st m v with
    | some (m, cv) => some (m, .axiomInfo cv)
    | none => none
  | .defnInfo v e h =>
    match denoteCVGo st m v with
    | some (m, cv) =>
      match denoteEGo st m (st.nodeCount + 1) e with
      | some (m, x) => some (m, .defnInfo cv x h)
      | none => none
    | none => none
  | .thmInfo v e =>
    match denoteCVGo st m v with
    | some (m, cv) =>
      match denoteEGo st m (st.nodeCount + 1) e with
      | some (m, x) => some (m, .thmInfo cv x)
      | none => none
    | none => none
  | .indInfo v c =>
    match denoteCVGo st m v, denoteCaps st c with
    | some (m, cv), some caps => some (m, .indInfo cv caps)
    | _, _ => none
  | .ctorInfo v nP nF =>
    match denoteCVGo st m v with
    | some (m, cv) => some (m, .ctorInfo cv nP nF)
    | none => none
  | .recInfo v mI rP rs =>
    match denoteCVGo st m v with
    | some (m, cv) =>
      match denoteRulesGo st m rs with
      | some (m, rules) => some (m, .recInfo cv mI rP rules)
      | none => none
    | none => none
  | .projInfo t =>
    match denoteProjTableGo st m t with
    | some (m, tbl) => some (m, .projInfo tbl)
    | none => none

/-- con-leche: none — the memoised denotation of a block's constants, at ONE
memo, so that the sharing BETWEEN a block's type, constructor and recursor
types survives too. -/
def denoteCIListGo (st : EStore) (m : DMemo) :
    List IConstantInfo -> Option (DMemo × List ConstantInfo)
  | [] => some (m, [])
  | c :: cs =>
    match denoteCIGo st m c with
    | some (m, x) =>
      match denoteCIListGo st m cs with
      | some (m, xs) => some (m, x :: xs)
      | none => none
    | none => none

/-! ## The monadic readbacks

`fail (.internal …)` on a dangling handle, as `view` and `readName` do. -/

/-- con-leche: none — read an expression handle back as a transient `Expr`.
DESIGN §8.3 forbids the CHECKER an `Expr`; this is the seam's readback, whose
callers are named in the module note. -/
def readExpr (h : EIdx) : AM Expr := do
  let s ← get
  match denoteEShared s.store h with
  | some e => pure e
  | none => fail (.internal "arena: dangling expression handle")

/-- con-leche: none — read a block's constants back as transient
`ConstantInfo`s (one block at a time; see the module note). -/
def readCIList (cs : List IConstantInfo) : AM (List ConstantInfo) := do
  let s ← get
  match denoteCIListGo s.store ∅ cs with
  | some (_, x) => pure x
  | none => fail (.internal "arena: dangling handle in a block's constants")

/-! ## The intern direction

A transient con-leche value into the store.  `internExpr` carries the memo the
module note explains; everything above it threads that memo so that one
block's model is interned with one table. -/

/-- con-leche: none — the expression-intern memo: the handle each transient
subterm was interned at.  Keyed on `ConLeche.Expr`, whose `Hashable` reads the
cached `data` word and whose `BEq` shortcuts on pointer equality, so a shared
subterm costs one probe. -/
abbrev EMemo := Std.HashMap Expr EIdx

/-- con-leche: none — intern a transient expression tree, memoised on the
subterms already interned.  Structural on `Expr`, so no fuel: the argument is
a value, not a DAG.  The memo is probed only at the four compound
constructors; a leaf is one `internE`, and the store's own cons table already
answers a repeat of it in `O(1)`.  (The `e@(…)` shape is con-leche's own, at
`ConLeche/Frontend/ProjRec.lean:182-225`'s `occursConstGo`.) -/
def internExprGo (m : EMemo) : Expr → AM (EMemo × EIdx)
  | .bvar i => do pure (m, ← internE (.bvar i))
  | .sort u => do
    let hu ← internLevel u
    pure (m, ← internE (.sort hu))
  | .const n us => do
    let hn ← internName n
    let hus ← internLevels us
    pure (m, ← internE (.const hn hus))
  | .lit l => do pure (m, ← internE (.lit l))
  | e@(.fvar i ty) => do
    match m[e]? with
    | some h => pure (m, h)
    | none => do
      let (m, t) ← internExprGo m ty
      let h ← internE (.fvar i t)
      pure (m.insert e h, h)
  | e@(.app f a) => do
    match m[e]? with
    | some h => pure (m, h)
    | none => do
      let (m, hf) ← internExprGo m f
      let (m, ha) ← internExprGo m a
      let h ← internE (.app hf ha)
      pure (m.insert e h, h)
  | e@(.lam ty b bi) => do
    match m[e]? with
    | some h => pure (m, h)
    | none => do
      let (m, ht) ← internExprGo m ty
      let (m, hb) ← internExprGo m b
      let h ← internE (.lam ht hb bi)
      pure (m.insert e h, h)
  | e@(.forallE ty b bi) => do
    match m[e]? with
    | some h => pure (m, h)
    | none => do
      let (m, ht) ← internExprGo m ty
      let (m, hb) ← internExprGo m b
      let h ← internE (.forallE ht hb bi)
      pure (m.insert e h, h)
  | e@(.letE ty v b) => do
    match m[e]? with
    | some h => pure (m, h)
    | none => do
      let (m, ht) ← internExprGo m ty
      let (m, hv) ← internExprGo m v
      let (m, hb) ← internExprGo m b
      let h ← internE (.letE ht hv hb)
      pure (m.insert e h, h)
  | e@(.proj n i sub) => do
    match m[e]? with
    | some h => pure (m, h)
    | none => do
      let (m, hs) ← internExprGo m sub
      let hn ← internName n
      let h ← internE (.proj hn i hs)
      pure (m.insert e h, h)

/-- con-leche: none — intern a transient expression at a fresh memo. -/
def internExpr (e : Expr) : AM EIdx := do
  pure (← internExprGo (∅ : EMemo) e).2

/-- con-leche: none — intern a list of transient expressions. -/
def internExprList (m : EMemo) : List Expr → AM (EMemo × List EIdx)
  | [] => pure (m, [])
  | e :: es => do
    let (m, h) ← internExprGo m e
    let (m, hs) ← internExprList m es
    pure (m, h :: hs)

/-- con-leche: none — intern a list of transient names. -/
def internNameList : List ConLeche.Name → AM (List NIdx)
  | [] => pure []
  | n :: ns => do
    let h ← internName n
    let hs ← internNameList ns
    pure (h :: hs)

/-- con-leche: none — intern a `ConstantVal`. -/
def internCV (m : EMemo) (cv : ConstantVal) : AM (EMemo × IConstantVal) := do
  let n ← internName cv.name
  let lps ← internNameList cv.levelParams
  let (m, ty) ← internExprGo m cv.type
  pure (m, ⟨n, lps, ty⟩)

/-- con-leche: none — intern a recursor rule's firing mode. -/
def internFire (m : EMemo) : RecRuleFire → AM (EMemo × IRecRuleFire)
  | .inert => pure (m, .inert)
  | .plain => pure (m, .plain)
  | .nested lvls pins => do
    let hls ← internLevelList lvls
    let (m, hps) ← internExprList m pins
    pure (m, .nested hls hps)

/-- con-leche: none — intern one recursor rule. -/
def internRule (m : EMemo) (rl : RecRule) : AM (EMemo × IRecRule) := do
  let c ← internName rl.ctor
  let (m, f) ← internFire m rl.fire
  let (m, r) ← internExprGo m rl.rhs
  pure (m, ⟨c, rl.nfields, rl.ctorParams, f, r, rl.k, rl.eta, rl.paramsBlind⟩)

/-- con-leche: none — intern a rule list. -/
def internRules (m : EMemo) : List RecRule → AM (EMemo × List IRecRule)
  | [] => pure (m, [])
  | r :: rs => do
    let (m, h) ← internRule m r
    let (m, hs) ← internRules m rs
    pure (m, h :: hs)

/-- con-leche: none — intern an inductive's capabilities. -/
def internCaps (c : IndCaps) : AM IIndCaps := do
  let ct ← internName c.etaCtor
  pure ⟨c.eta, ct, c.etaParams, c.etaFields, c.unitlike, c.unitParams,
        c.ruleK, c.sortZ⟩

/-- con-leche: none — intern a projection table.  `tableName` is the field
`Arena/Env.lean` adds: the reserved name, interned here so that
`IConstantInfo.name` stays pure. -/
def internProjTable (m : EMemo) (t : ProjTable) : AM (EMemo × IProjTable) := do
  let sn ← internName t.structName
  let tn ← projTableName sn
  let lps ← internNameList t.levelParams
  let c ← internName t.ctor
  let ss ← internLevel t.structSort
  let (m, bs) ← internExprList m t.bodies.toList
  let gs ← internLevelList t.guards
  pure (m, ⟨sn, tn, lps, t.numParams, c, t.numFields, ss, bs.toArray, gs, t.off⟩)

/-- con-leche: none — intern a stored constant. -/
def internCI (m : EMemo) : ConstantInfo → AM (EMemo × IConstantInfo)
  | .axiomInfo v => do
    let (m, cv) ← internCV m v
    pure (m, .axiomInfo cv)
  | .defnInfo v e h => do
    let (m, cv) ← internCV m v
    let (m, x) ← internExprGo m e
    pure (m, .defnInfo cv x h)
  | .thmInfo v e => do
    let (m, cv) ← internCV m v
    let (m, x) ← internExprGo m e
    pure (m, .thmInfo cv x)
  | .indInfo v c => do
    let (m, cv) ← internCV m v
    let caps ← internCaps c
    pure (m, .indInfo cv caps)
  | .ctorInfo v nP nF => do
    let (m, cv) ← internCV m v
    pure (m, .ctorInfo cv nP nF)
  | .recInfo v mI rP rs => do
    let (m, cv) ← internCV m v
    let (m, rules) ← internRules m rs
    pure (m, .recInfo cv mI rP rules)
  | .projInfo t => do
    let (m, tbl) ← internProjTable m t
    pure (m, .projInfo tbl)

/-- con-leche: none — intern a block's constants. -/
def internCIList (m : EMemo) : List ConstantInfo → AM (EMemo × List IConstantInfo)
  | [] => pure (m, [])
  | c :: cs => do
    let (m, h) ← internCI m c
    let (m, hs) ← internCIList m cs
    pure (m, h :: hs)

/-- con-leche: none — intern a declaration record: the inverse of `denoteDecl`
above, and what the modeller seam's delegation pushes back into the persistent
tier. -/
def internDecl (m : EMemo) : Declaration → AM (EMemo × IDeclaration)
  | .axiomDecl v => do
    let (m, cv) ← internCV m v
    pure (m, .axiomDecl cv)
  | .defnDecl v e h => do
    let (m, cv) ← internCV m v
    let (m, x) ← internExprGo m e
    pure (m, .defnDecl cv x h)
  | .thmDecl v e => do
    let (m, cv) ← internCV m v
    let (m, x) ← internExprGo m e
    pure (m, .thmDecl cv x)
  | .opaqueDecl v e => do
    let (m, cv) ← internCV m v
    let (m, x) ← internExprGo m e
    pure (m, .opaqueDecl cv x)
  | .basisDecl k => pure (m, .basisDecl k)
  | .indDecl block nP => do
    let (m, b) ← internCIList m block
    pure (m, .indDecl b nP)
  | .quotDecl k v => do
    let (m, cv) ← internCV m v
    pure (m, .quotDecl k cv)

/-- con-leche: none — intern a list of declaration records at one memo. -/
def internDecls (m : EMemo) : List Declaration → AM (EMemo × List IDeclaration)
  | [] => pure (m, [])
  | d :: ds => do
    let (m, h) ← internDecl m d
    let (m, hs) ← internDecls m ds
    pure (m, h :: hs)

end ConRon.Arena.Frontend

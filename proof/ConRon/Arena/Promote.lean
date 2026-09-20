/-
# `ConRon.Arena.Promote` — the scratch → persistent copy (DESIGN.md §8.3, task #97-P6-2)

DESIGN §8.3, "**Phase A runs in the scratch tier too, with promotion**":

> The install phase (annotate the type and the value, infer, defeq) was
> interning every intermediate into the persistent tier — on `Init` 5.06 M
> permanent nodes on top of the parse's 6.14 M (+82 %) […].  The arena's
> answer is con-leche #64's: phase A opens the scratch tier like phase B, and
> the two handles it must keep (the annotated type, the annotated value) are
> **promoted** — a memoised structural copy scratch → persistent […] before
> the tier is dropped.  Persistent handles are promoted to themselves.

This module is that copy, at all four handle kinds and lifted to
`Arena/Env.lean`'s declaration layer, plus `promoteNew` — the entry the fold
calls, which promotes a step's NEWLY INSTALLED constants in place.

## What it is

`view` the node, promote its children, `intern` the result into the
PERSISTENT tier (`Arena/Store.lean`'s `internPersistent` family, whose section
note carries the WF obligations).  Three properties make it cheap and make it
right:

* **a persistent handle promotes to itself**, by one tier-bit test
  (`Idx.isPersistent`) and no store access at all.  Most of an annotated term
  IS the parsed term — `annotate` rebuilds only the spine it changes — so the
  walk stops at the first persistent node on every branch;
* **the memo makes it `O(result)`** and not `O(unfolding)`: the subject is a
  hash-consed DAG, and an unmemoised structural copy of a DAG is the mistake
  task #97g's item 5 found three times over.  The memo is per DECLARATION — a
  scratch handle means nothing once the tier is dropped — and it is threaded
  as an argument-and-result pair, which is `Arena/ExprOps.lean`'s spelling for
  the same thing and a moved `ron::HashMap` returned in the Rust;
* **`internPersistent` probes the persistent cons table first**, so promoting
  a node twice is a probe and nothing more, and a node the parse already
  interned is found rather than copied.

## What it is NOT

It is not a garbage collector and it does not compact: the scratch tier is
dropped whole by `dropScratch`, which is what actually reclaims.  Promotion
only decides what crosses the boundary — exactly the handles the environment
keeps, and the phase-A record phase B will check.

`denote (promote h) = denote h` is the exactness lemma P3 owes; it is an
induction on the recursion below, with `EStore.internPersistent`'s `consP` and
`derExact` at each node.
-/
import ConRon.Arena.CheckerSplit

namespace ConRon.Arena

open ConLeche

/-! ## The memo -/

/-- con-leche: none — arena infrastructure; the promotion's memo: the
persistent handle each promoted scratch handle was copied to, one table per
handle kind.  Threaded as an argument-and-result pair (see the module note),
fresh at every declaration. -/
structure PMemo where
  /-- expression handles -/
  eM : Std.HashMap EIdx EIdx
  /-- name handles -/
  nM : Std.HashMap NIdx NIdx
  /-- level handles -/
  lM : Std.HashMap LIdx LIdx
  /-- universe-argument-list handles -/
  lsM : Std.HashMap LsIdx LsIdx

/-- con-leche: none — arena infrastructure; the empty promotion memo, which is
what every declaration's promotion starts from. -/
def PMemo.empty : PMemo := ⟨∅, ∅, ∅, ∅⟩

instance : Inhabited PMemo := ⟨PMemo.empty⟩

/-! ## The four handle kinds -/

/-- con-leche: none — arena infrastructure; promote a NAME handle.  A name's
children are names, so the recursion is the prefix chain and the fuel is the
store's own bound (`Arena/Core.lean`'s `coreWalkFuel`, DESIGN §8.4 lesson
7). -/
def promoteN (m : PMemo) : Nat → NIdx → AM (PMemo × NIdx)
  | 0, _ => fail (.internal "fuel exhausted: promoteN")
  | fuel + 1, h => do
    if h.isPersistent then pure (m, h)
    else
      match m.nM[h]? with
      | some r => pure (m, r)
      | none => do
        let (m, r) ←
          match ← viewN h with
          | .anonymous => do pure (m, ← internPersistentN .anonymous)
          | .str p s => do
            let (m, p) ← promoteN m fuel p
            pure (m, ← internPersistentN (.str p s))
          | .num p n => do
            let (m, p) ← promoteN m fuel p
            pure (m, ← internPersistentN (.num p n))
        pure ({ m with nM := m.nM.insert h r }, r)

/-- con-leche: none — arena infrastructure; promote a LEVEL handle. -/
def promoteL (m : PMemo) : Nat → LIdx → AM (PMemo × LIdx)
  | 0, _ => fail (.internal "fuel exhausted: promoteL")
  | fuel + 1, h => do
    if h.isPersistent then pure (m, h)
    else
      match m.lM[h]? with
      | some r => pure (m, r)
      | none => do
        let (m, r) ←
          match ← viewL h with
          | .zero => do pure (m, ← internPersistentL .zero)
          | .succ u => do
            let (m, u) ← promoteL m fuel u
            pure (m, ← internPersistentL (.succ u))
          | .max u v => do
            let (m, u) ← promoteL m fuel u
            let (m, v) ← promoteL m fuel v
            pure (m, ← internPersistentL (.max u v))
          | .imax u v => do
            let (m, u) ← promoteL m fuel u
            let (m, v) ← promoteL m fuel v
            pure (m, ← internPersistentL (.imax u v))
          | .param n => do
            let (m, n) ← promoteN m fuel n
            pure (m, ← internPersistentL (.param n))
        pure ({ m with lM := m.lM.insert h r }, r)

/-- con-leche: none — arena infrastructure; promote the levels of a
universe-argument list. -/
def promoteLList (m : PMemo) (fuel : Nat) : List LIdx → AM (PMemo × List LIdx)
  | [] => pure (m, [])
  | u :: us => do
    let (m, u) ← promoteL m fuel u
    let (m, us) ← promoteLList m fuel us
    pure (m, u :: us)

/-- con-leche: none — arena infrastructure; promote a universe-argument LIST
handle. -/
def promoteLs (m : PMemo) (fuel : Nat) (h : LsIdx) : AM (PMemo × LsIdx) := do
  if h.isPersistent then pure (m, h)
  else
    match m.lsM[h]? with
    | some r => pure (m, r)
    | none => do
      let (m, us) ← promoteLList m fuel (← viewLs h)
      let r ← internPersistentLs us
      pure ({ m with lsM := m.lsM.insert h r }, r)

/-- con-leche: none — arena infrastructure; **promote an EXPRESSION handle**:
the structural copy of DESIGN §8.3, memoised on the node.  Ten clauses, the
store's ten constructors, each promoting its own children first — `BinderMeta`
and `Literal` are values and carry no handle (DESIGN §8.3), so they cross
unchanged. -/
def promoteE (m : PMemo) : Nat → EIdx → AM (PMemo × EIdx)
  | 0, _ => fail (.internal "fuel exhausted: promoteE")
  | fuel + 1, h => do
    if h.isPersistent then pure (m, h)
    else
      match m.eM[h]? with
      | some r => pure (m, r)
      | none => do
        let (m, r) ←
          match ← view h with
          | .bvar i => do pure (m, ← internPersistentE (.bvar i))
          | .fvar idx ty => do
            let (m, ty) ← promoteE m fuel ty
            pure (m, ← internPersistentE (.fvar idx ty))
          | .sort u => do
            let (m, u) ← promoteL m fuel u
            pure (m, ← internPersistentE (.sort u))
          | .const n us => do
            let (m, n) ← promoteN m fuel n
            let (m, us) ← promoteLs m fuel us
            pure (m, ← internPersistentE (.const n us))
          | .app f a => do
            let (m, f) ← promoteE m fuel f
            let (m, a) ← promoteE m fuel a
            pure (m, ← internPersistentE (.app f a))
          | .lam ty body bm => do
            let (m, ty) ← promoteE m fuel ty
            let (m, body) ← promoteE m fuel body
            pure (m, ← internPersistentE (.lam ty body bm))
          | .forallE ty body bm => do
            let (m, ty) ← promoteE m fuel ty
            let (m, body) ← promoteE m fuel body
            pure (m, ← internPersistentE (.forallE ty body bm))
          | .letE ty val body => do
            let (m, ty) ← promoteE m fuel ty
            let (m, val) ← promoteE m fuel val
            let (m, body) ← promoteE m fuel body
            pure (m, ← internPersistentE (.letE ty val body))
          | .lit l => do pure (m, ← internPersistentE (.lit l))
          | .proj n i e => do
            let (m, n) ← promoteN m fuel n
            let (m, e) ← promoteE m fuel e
            pure (m, ← internPersistentE (.proj n i e))
        pure ({ m with eM := m.eM.insert h r }, r)

/-! ## The lists -/

/-- con-leche: none — arena infrastructure; promote a list of name handles. -/
def promoteNList (m : PMemo) (fuel : Nat) : List NIdx → AM (PMemo × List NIdx)
  | [] => pure (m, [])
  | n :: ns => do
    let (m, n) ← promoteN m fuel n
    let (m, ns) ← promoteNList m fuel ns
    pure (m, n :: ns)

/-- con-leche: none — arena infrastructure; promote a list of expression
handles at ONE memo, so a block's sharing survives the copy. -/
def promoteEList (m : PMemo) (fuel : Nat) : List EIdx → AM (PMemo × List EIdx)
  | [] => pure (m, [])
  | e :: es => do
    let (m, e) ← promoteE m fuel e
    let (m, es) ← promoteEList m fuel es
    pure (m, e :: es)

/-! ## The declaration layer

`Arena/Env.lean`'s record, field for field: every `EIdx`, `NIdx`, `LIdx` and
`List LIdx` in it is promoted, and every `Nat`, `Bool`, `ReducibilityHint`,
`PropWhen` and `BinderMeta` crosses unchanged (they carry no handle — DESIGN
§8.7's ruling that (B) imports con-leche's representation-free types).  The
shape is `Arena/Frontend/Readback.lean`'s intern direction, which walks the
same record for the same reason. -/

/-- con-leche: none — arena infrastructure; promote a `ConstantVal`. -/
def promoteCV (m : PMemo) (fuel : Nat) (cv : IConstantVal) :
    AM (PMemo × IConstantVal) := do
  let (m, n) ← promoteN m fuel cv.name
  let (m, lps) ← promoteNList m fuel cv.levelParams
  let (m, ty) ← promoteE m fuel cv.type
  pure (m, ⟨n, lps, ty⟩)

/-- con-leche: none — arena infrastructure; promote a rule's firing mode. -/
def promoteFire (m : PMemo) (fuel : Nat) :
    IRecRuleFire → AM (PMemo × IRecRuleFire)
  | .inert => pure (m, .inert)
  | .plain => pure (m, .plain)
  | .nested lvls pins => do
    let (m, lvls) ← promoteLList m fuel lvls
    let (m, pins) ← promoteEList m fuel pins
    pure (m, .nested lvls pins)

/-- con-leche: none — arena infrastructure; promote one recursor rule. -/
def promoteRule (m : PMemo) (fuel : Nat) (rl : IRecRule) :
    AM (PMemo × IRecRule) := do
  let (m, c) ← promoteN m fuel rl.ctor
  let (m, f) ← promoteFire m fuel rl.fire
  let (m, r) ← promoteE m fuel rl.rhs
  pure (m, ⟨c, rl.nfields, rl.ctorParams, f, r, rl.k, rl.eta, rl.paramsBlind⟩)

/-- con-leche: none — arena infrastructure; promote a rule list. -/
def promoteRules (m : PMemo) (fuel : Nat) :
    List IRecRule → AM (PMemo × List IRecRule)
  | [] => pure (m, [])
  | r :: rs => do
    let (m, r) ← promoteRule m fuel r
    let (m, rs) ← promoteRules m fuel rs
    pure (m, r :: rs)

/-- con-leche: none — arena infrastructure; promote an inductive's
capabilities.  `sortZ` is a `PropWhen` over con-leche `Name`s and carries no
handle. -/
def promoteCaps (m : PMemo) (fuel : Nat) (c : IIndCaps) :
    AM (PMemo × IIndCaps) := do
  let (m, ct) ← promoteN m fuel c.etaCtor
  pure (m, { c with etaCtor := ct })

/-- con-leche: none — arena infrastructure; promote a projection table,
`tableName` included (it is a stored handle, not a recomputed name —
`Arena/Env.lean`'s one added field). -/
def promoteProjTable (m : PMemo) (fuel : Nat) (t : IProjTable) :
    AM (PMemo × IProjTable) := do
  let (m, sn) ← promoteN m fuel t.structName
  let (m, tn) ← promoteN m fuel t.tableName
  let (m, lps) ← promoteNList m fuel t.levelParams
  let (m, c) ← promoteN m fuel t.ctor
  let (m, ss) ← promoteL m fuel t.structSort
  let (m, bs) ← promoteEList m fuel t.bodies.toList
  let (m, gs) ← promoteLList m fuel t.guards
  pure (m, ⟨sn, tn, lps, t.numParams, c, t.numFields, ss, bs.toArray, gs, t.off⟩)

/-- con-leche: none — arena infrastructure; **promote a stored constant** —
the seven `IConstantInfo` constructors, which is what "the handles the
environment keeps" means. -/
def promoteCI (m : PMemo) (fuel : Nat) :
    IConstantInfo → AM (PMemo × IConstantInfo)
  | .axiomInfo v => do
    let (m, cv) ← promoteCV m fuel v
    pure (m, .axiomInfo cv)
  | .defnInfo v e h => do
    let (m, cv) ← promoteCV m fuel v
    let (m, x) ← promoteE m fuel e
    pure (m, .defnInfo cv x h)
  | .thmInfo v e => do
    let (m, cv) ← promoteCV m fuel v
    let (m, x) ← promoteE m fuel e
    pure (m, .thmInfo cv x)
  | .indInfo v c => do
    let (m, cv) ← promoteCV m fuel v
    let (m, caps) ← promoteCaps m fuel c
    pure (m, .indInfo cv caps)
  | .ctorInfo v nP nF => do
    let (m, cv) ← promoteCV m fuel v
    pure (m, .ctorInfo cv nP nF)
  | .recInfo v mI rP rs => do
    let (m, cv) ← promoteCV m fuel v
    let (m, rules) ← promoteRules m fuel rs
    pure (m, .recInfo cv mI rP rules)
  | .projInfo t => do
    let (m, tbl) ← promoteProjTable m fuel t
    pure (m, .projInfo tbl)

/-- con-leche: none — arena infrastructure; promote a block's constants at ONE
memo, so that the sharing between a block's members survives. -/
def promoteCIList (m : PMemo) (fuel : Nat) :
    List IConstantInfo → AM (PMemo × List IConstantInfo)
  | [] => pure (m, [])
  | c :: cs => do
    let (m, c) ← promoteCI m fuel c
    let (m, cs) ← promoteCIList m fuel cs
    pure (m, c :: cs)

/-- con-leche: none — arena infrastructure; promote a declaration record.  Not
on the fold's path — the records arrive from the parse and are persistent —
and written because the layer is twinned whole (`Arena/Frontend/Readback.lean`
has the same seven clauses for the intern direction). -/
def promoteDecl (m : PMemo) (fuel : Nat) :
    IDeclaration → AM (PMemo × IDeclaration)
  | .axiomDecl v => do
    let (m, cv) ← promoteCV m fuel v
    pure (m, .axiomDecl cv)
  | .defnDecl v e h => do
    let (m, cv) ← promoteCV m fuel v
    let (m, x) ← promoteE m fuel e
    pure (m, .defnDecl cv x h)
  | .thmDecl v e => do
    let (m, cv) ← promoteCV m fuel v
    let (m, x) ← promoteE m fuel e
    pure (m, .thmDecl cv x)
  | .opaqueDecl v e => do
    let (m, cv) ← promoteCV m fuel v
    let (m, x) ← promoteE m fuel e
    pure (m, .opaqueDecl cv x)
  | .basisDecl k => pure (m, .basisDecl k)
  | .indDecl block nP => do
    let (m, b) ← promoteCIList m fuel block
    pure (m, .indDecl b nP)
  | .quotDecl k v => do
    let (m, cv) ← promoteCV m fuel v
    pure (m, .quotDecl k cv)

/-- con-leche: none — arena infrastructure; promote the datum that crosses the
install/check seam (`Arena/CheckerSplit.lean`'s `ValueGroup`).  An `opaque`'s
value is NOT in the environment — only the pending record holds it — so the
seam is promoted beside the environment and at the SAME memo. -/
def promoteVG (m : PMemo) (fuel : Nat) (g : ValueGroup) :
    AM (PMemo × ValueGroup) := do
  let (m, cvA) ← promoteCV m fuel g.cvA
  let (m, jv) ← promoteE m fuel g.jv
  pure (m, ⟨g.kind, cvA, jv⟩)

/-! ## The fold's entry: a step's newly installed constants -/

/-- con-leche: none — arena infrastructure; forget the index rows of the
constants a step installed.  They are keyed by the constant's name handle,
which the promotion may MOVE (a name first interned inside the scratch tier is
a scratch handle), and a stale row under a scratch key is not merely useless:
`dropScratch` hands that word back to the next declaration, and `IFEnv.find?`
would answer a different constant under it. -/
def eraseInstalled (idx : Std.HashMap NIdx (Nat × IConstantInfo)) :
    List IConstantInfo → Std.HashMap NIdx (Nat × IConstantInfo)
  | [] => idx
  | ci :: cs => eraseInstalled (idx.erase ci.name) cs

/-- con-leche: none — arena infrastructure; re-index the promoted constants at
the installation counters they were pushed with.  The list is NEWEST FIRST, as
`IEnv.consts` is, so the counters run down from `c`. -/
def indexPromoted (idx : Std.HashMap NIdx (Nat × IConstantInfo)) (c : Nat) :
    List IConstantInfo → Std.HashMap NIdx (Nat × IConstantInfo)
  | [] => idx
  | ci :: cs => indexPromoted (idx.insert ci.name (c - 1, ci)) (c - 1) cs

/-- con-leche: none — arena infrastructure; **the phase-A bracket's promotion
half**: the `k` constants the step just installed, copied into the persistent
tier and re-indexed, everything below them untouched.

`k` is `fe.visibleBelow - n₀` for the counter `n₀` read BEFORE the step: every
install route in (B) grows the environment by `IFEnv.push` alone
(`Arena/Checker.lean`, `Arena/DeclCheck.lean`, `Arena/Inductives/*`), so the
`k` newest entries of `fe.env.consts` are exactly the step's, and the
provisional self-environments the recursor installs build (`provisionRecs`'s
`feSelf`, `checkNativeRec`'s `feR`) are discarded by their own callers and
never reach here. -/
def promoteNew (m : PMemo) (fuel k : Nat) (fe : IFEnv) : AM (PMemo × IFEnv) := do
  if k == 0 then pure (m, fe)
  else
    let ⟨⟨consts⟩, idx, vb⟩ := fe
    let installed := consts.take k
    let below := consts.drop k
    let idx := eraseInstalled idx installed
    let (m, installed) ← promoteCIList m fuel installed
    let idx := indexPromoted idx vb installed
    pure (m, ⟨⟨installed ++ below⟩, idx, vb⟩)

end ConRon.Arena

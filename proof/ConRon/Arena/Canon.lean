/-
# `ConRon.Arena.Canon` — the level-parameter canonical form, over handles

The twin of `ConLeche/Kernel/Canon.lean`: the canonical form a stream's block
is matched against a pinned basis block up to, and the lockstep comparisons
built on it.

## The `canon` / `canonEqFast` collapse

con-leche carries each comparison TWICE — a SPECIFICATION that builds
`ConstantInfo.canon` of both sides and compares the results, and a `…Fast`
twin that descends both sides together — joined by `@[csimp]`, so the
executed comparison is the lockstep one and the proofs read the spec.  (The
reason is task #226: `canonExpr` rebuilds every node, so the specification is
`O(tree)` on a DAG-shared stream term and `tests/e2e/tower_axiom.ndjson`
exhausts memory on it.)

The arena has ONE function per algorithm — task #97b's rule for con-leche's
`…Go`/`…Fast` triples — and it is the LOCKSTEP one, because that is what both
binaries execute.  Each twin therefore carries a `con-leche:` line per
collapsed declaration.  Note that the arena would not need the trick for the
reason con-leche does (its store is a DAG and `canonExpr` over handles would
be memoizable), but it does need the *verdict*, and the lockstep walk is
bounded by the PIN's tree size on every input, which is the property the
comparison's callers rely on.

## The renaming is two lists, not a function

con-leche's `canonNameMap ps : Name → Name` sends the `i`-th level parameter
to `.num .anonymous i`.  Over handles "building a name" means INTERNING one,
so the map cannot be an `NIdx → NIdx` function value computed on demand — and
DESIGN §3.4 forbids passing a function value at all.  So the numbered names
are interned ONCE, by `canonNames`, and the renaming is the pure
two-list lookup `canonNameMap ps cs`: `ps` the constant's own parameter
handles, `cs` the interned numerals.  One `cs` serves both sides of every
comparison, because each comparison tests the two parameter lists for equal
LENGTH before it looks at a term, and `canonNames` depends on the length
alone.
-/
import ConRon.Arena.Core

namespace ConRon.Arena

open ConLeche

/-! ## The renaming -/

/-- con-leche: ConLeche/Kernel/Canon.lean:67-73 canonNameMap — the `n`
numbered names `⟨0⟩ … ⟨n-1⟩` the canonical form renames a constant's level
parameters to, interned.  The `Nat` recursion counts UP so the list comes out
in index order; no fuel, because it is structural on the count. -/
def canonNamesGo (i n : Nat) : AM (List NIdx) :=
  match n with
  | 0 => pure []
  | n + 1 => do
    let a ← internNNode .anonymous
    let h ← internNNode (.num a i)
    let hs ← canonNamesGo (i + 1) n
    pure (h :: hs)

/-- con-leche: ConLeche/Kernel/Canon.lean:67-73 canonNameMap — the numbered
names for a level-parameter list of length `n`. -/
def canonNames (n : Nat) : AM (List NIdx) := canonNamesGo 0 n

/-- con-leche: ConLeche/Kernel/Canon.lean:67-73 canonNameMap — the renaming a
constant's own parameter list induces: the `i`-th parameter becomes the `i`-th
numbered name, anything else is left alone.  PURE (the numerals are already
interned), and a plain function of two lists rather than a function VALUE
(DESIGN §3.4). -/
def canonNameMap (ps cs : List NIdx) (n : NIdx) : NIdx :=
  match ps.findIdx? (fun p => p == n) with
  | some i => cs.getD i n
  | none => n

/-! ## Levels -/

/-- con-leche: ConLeche/Kernel/Canon.lean:27-34 canonLevel
con-leche: ConLeche/Kernel/Canon.lean:126-146 canonExprEqFast
`canonLevel ps u == canonLevel ps' v`, decided in lockstep on the two level
handles.  `canonLevel` preserves every node's constructor (it rewrites only
the `.param` leaf), so the two canonical forms are equal iff the originals
agree constructor by constructor down to their leaves. -/
def canonLevelEq (ps ps' cs : List NIdx) : Nat → LIdx → LIdx → AM Bool
  | 0, _, _ => fail (.internal "fuel exhausted: canonLevelEq")
  | fuel + 1, u, v => do
    match ← viewL u, ← viewL v with
    | .zero, .zero => pure true
    | .succ a, .succ b => canonLevelEq ps ps' cs fuel a b
    | .max a b, .max a' b' =>
      if ← canonLevelEq ps ps' cs fuel a a' then
        canonLevelEq ps ps' cs fuel b b'
      else pure false
    | .imax a b, .imax a' b' =>
      if ← canonLevelEq ps ps' cs fuel a a' then
        canonLevelEq ps ps' cs fuel b b'
      else pure false
    | .param n, .param n' =>
      pure (canonNameMap ps cs n == canonNameMap ps' cs n')
    | _, _ => pure false

/-- con-leche: ConLeche/Kernel/Canon.lean:126-146 canonExprEqFast — the
`.const` clause's `us.map (canonLevel m) == us'.map (canonLevel m')`, at two
universe-argument lists read out of the level-list store. -/
def canonLevelListEq (ps ps' cs : List NIdx) (fuel : Nat) :
    List LIdx → List LIdx → AM Bool
  | [], [] => pure true
  | u :: us, v :: vs => do
    if ← canonLevelEq ps ps' cs fuel u v then
      canonLevelListEq ps ps' cs fuel us vs
    else pure false
  | _, _ => pure false

/-- con-leche: ConLeche/Kernel/Canon.lean:126-146 canonExprEqFast — the same
at two interned universe-argument LIST handles. -/
def canonLevelsEq (ps ps' cs : List NIdx) (fuel : Nat) (us vs : LsIdx) :
    AM Bool := do
  canonLevelListEq ps ps' cs fuel (← viewLs us) (← viewLs vs)

/-! ## Terms -/

/-- con-leche: ConLeche/Kernel/Canon.lean:36-65 canonExpr
con-leche: ConLeche/Kernel/Canon.lean:126-146 canonExprEqFast
**The agreement for expressions**, in lockstep on two handles.  `canonExpr`
preserves every node's constructor (it rewrites only levels, and resets the
binder metadata to the same constant on both sides), so the two canonical
forms are equal iff the originals agree constructor by constructor down to
their leaves — which is what this descent tests.

The binder metadata is NOT compared, exactly as con-leche's clause does not:
`canonExpr` writes `⟨.never⟩` on both sides. -/
def canonExprEq (ps ps' cs : List NIdx) : Nat → EIdx → EIdx → AM Bool
  | 0, _, _ => fail (.internal "fuel exhausted: canonExprEq")
  | fuel + 1, a, b => do
    match ← view a, ← view b with
    | .bvar i, .bvar j => pure (i == j)
    | .fvar i t, .fvar j t' =>
      if i == j then canonExprEq ps ps' cs fuel t t' else pure false
    | .sort u, .sort v => canonLevelEq ps ps' cs fuel u v
    | .const n us, .const n' us' =>
      if n == n' then canonLevelsEq ps ps' cs fuel us us' else pure false
    | .app f x, .app f' x' =>
      if ← canonExprEq ps ps' cs fuel f f' then
        canonExprEq ps ps' cs fuel x x'
      else pure false
    | .lam t bd _, .lam t' bd' _ =>
      if ← canonExprEq ps ps' cs fuel t t' then
        canonExprEq ps ps' cs fuel bd bd'
      else pure false
    | .forallE t bd _, .forallE t' bd' _ =>
      if ← canonExprEq ps ps' cs fuel t t' then
        canonExprEq ps ps' cs fuel bd bd'
      else pure false
    | .letE t v bd, .letE t' v' bd' =>
      if ← canonExprEq ps ps' cs fuel t t' then
        if ← canonExprEq ps ps' cs fuel v v' then
          canonExprEq ps ps' cs fuel bd bd'
        else pure false
      else pure false
    | .lit l, .lit l' => pure (l == l')
    | .proj s i e, .proj s' i' e' =>
      if s == s' && i == i' then canonExprEq ps ps' cs fuel e e'
      else pure false
    | _, _ => pure false

/-! ## Constants -/

/-- con-leche: ConLeche/Kernel/Canon.lean:75-80 ConstantVal.canon
con-leche: ConLeche/Kernel/Canon.lean:195-199 ConstantVal.canonEq
con-leche: ConLeche/Kernel/Canon.lean:201-206 ConstantVal.canonEqFast
Two constants have the same canonical common data.  The numbered
level-parameter lists are equal exactly when they are equally long, which is
why the length test stands in for comparing them — and why ONE `canonNames`
serves both sides. -/
def IConstantVal.canonEq (cv cv' : IConstantVal) : AM Bool := do
  if cv.name == cv'.name && cv.levelParams.length == cv'.levelParams.length then do
    let cs ← canonNames cv.levelParams.length
    canonExprEq cv.levelParams cv'.levelParams cs coreWalkFuel cv.type cv'.type
  else pure false

/-- con-leche: ConLeche/Kernel/Canon.lean:224-231 canonRulesEqFast — rule
lists compared through the canonical form of each rule's right-hand side.
con-leche compares the other fields by rebuilding both rules at the common
`rhs := .bvar 0`; over handles the same predicate is the record comparison at
the common `rhs := default`, which interns nothing. -/
def canonRulesEq (ps ps' cs : List NIdx) (fuel : Nat) :
    List IRecRule → List IRecRule → AM Bool
  | [], [] => pure true
  | r :: rs, r' :: rs' => do
    if { r with rhs := default } == { r' with rhs := default } then
      if ← canonExprEq ps ps' cs fuel r.rhs r'.rhs then
        canonRulesEq ps ps' cs fuel rs rs'
      else pure false
    else pure false
  | _, _ => pure false

/-- con-leche: ConLeche/Kernel/Canon.lean:82-97 ConstantInfo.canon
con-leche: ConLeche/Kernel/Canon.lean:250-252 ConstantInfo.canonEq
con-leche: ConLeche/Kernel/Canon.lean:254-273 ConstantInfo.canonEqFast
Two stored constants have the same canonical form.  `.indInfo`'s capabilities
are not compared (`canon` resets both to `{}`), and a projection table is
compared as it stands (`canon` is the identity there — a table never occurs in
parsed input). -/
def IConstantInfo.canonEq : IConstantInfo → IConstantInfo → AM Bool
  | .axiomInfo cv, .axiomInfo cv' => cv.canonEq cv'
  | .defnInfo cv v h, .defnInfo cv' v' h' => do
    if h == h' then  -- hints first, as the port: `canonEq` interns (lane Checker Canon)
      if ← cv.canonEq cv' then do
        let cs ← canonNames cv.levelParams.length
        canonExprEq cv.levelParams cv'.levelParams cs coreWalkFuel v v'
      else pure false
    else pure false
  | .thmInfo cv v, .thmInfo cv' v' => do
    if ← cv.canonEq cv' then do
      let cs ← canonNames cv.levelParams.length
      canonExprEq cv.levelParams cv'.levelParams cs coreWalkFuel v v'
    else pure false
  | .indInfo cv _, .indInfo cv' _ => cv.canonEq cv'
  | .ctorInfo cv nP nF, .ctorInfo cv' nP' nF' => do
    if nP == nP' && nF == nF' then cv.canonEq cv' else pure false
  | .recInfo cv mI rP rules, .recInfo cv' mI' rP' rules' => do
    if mI == mI' && rP == rP' then do
      if ← cv.canonEq cv' then do
        let cs ← canonNames cv.levelParams.length
        canonRulesEq cv.levelParams cv'.levelParams cs coreWalkFuel rules rules'
      else pure false
    else pure false
  | .projInfo t, .projInfo t' => pure (t == t')
  | _, _ => pure false

/-- con-leche: ConLeche/Kernel/Canon.lean:289-292 canonEqList
con-leche: ConLeche/Kernel/Canon.lean:294-298 canonEqListFast
Two blocks are the same, member for member, up to the canonical form. -/
def canonEqList : List IConstantInfo → List IConstantInfo → AM Bool
  | [], [] => pure true
  | x :: xs, y :: ys => do
    if ← x.canonEq y then canonEqList xs ys else pure false
  | _, _ => pure false

end ConRon.Arena

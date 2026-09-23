/-
# `ConRon.Arena.Core` — the checker core of (B), over handles

The twin of `ConLeche/Kernel/Core.lean`, clause for clause: the six bodies
(`whnfCore`, `whnf`, `infer`, `inferIO`, `defeq`, `annotate`), the helpers
they call, and the knot `coreKnot` that ties them at fuel through the
record `CoreFnsA`.  `ConLeche/Kernel/TypeChecker.lean`'s seven fueled
entry points are at the bottom of this module, beside the knot they call
(deviation 5 below).

Everything here is DESIGN §8.4's "Rust-shaped Lean": one `def` per
intended Rust function, the monad is `AM` and nothing else, fuel is an
explicit `Nat`, and the arms are INLINE — P2b's reversal (task #97b, "The
arms are INLINE, and that is a deliberate reversal") holds for this module
too, because the alternative passes the dispatcher to each arm as a
function argument and a closure is what DESIGN §3.4 forbids.

## The six systematic deviations from con-leche's clause structure

1. **`env : Env` becomes `fe : IFEnv`.**  con-leche's kernel tier reads a
   linear association list and its `Cached` tier reads the index
   (`ConLeche/Cached/CoreC.lean` takes `fe : FEnv` throughout); the arena
   has ONE environment type, the index, because DESIGN §8.3's lesson 13
   makes `find?` the only read of the environment.  Consequently every
   `…Of`/`…F` PAIR of con-leche declarations — `natLitSupported` /
   `natLitSupportedF`, `natOpGuard` / `natOpGuardF`, `natOpStored` /
   `natOpStoredF`, `towerSlotsAll` / `towerSlotsAllF`, `recSlotsAll` /
   `recSlotsAllF`, `andRescueSlotsOf` / `andRescueSlots` /
   `andRescueSlotsF`, `recRuleKOf`, `recRuleEtaOf`, `recRuleBits`,
   `projFnRule`, `strLitSupported` / `strLitSupportedF` — collapses into
   ONE twin, which carries a `con-leche:` line per collapsed declaration.
   That is P2b's own rule for the `…Go`/`…Fast` triples, applied to the
   lookup abstraction instead of to the memo.
2. **Every structural match on a term is a `view`**, so a pure `Expr → α`
   is an `EIdx → AM α` and a walk takes an explicit `fuel : Nat`
   (`coreWalkFuel` below).  Recursions that are structural on something
   else — a binder count, an argument list, a `Nat` — take none, exactly
   as con-leche's do.
3. **Reserved names are INTERNED, not compared structurally**
   (`pin` below).  `natName`, `punitName`, … are `AM NIdx` and every
   comparison against them is handle equality, which DESIGN §8.3 licenses:
   `denoteN` is injective, so index inequality IS structural inequality.
4. **Levels are read back, not twinned** (DESIGN §8.3, lesson 4):
   `Level.isEquiv`, `Level.subst`, `Level.substPW`, `Level.zeronessOf` and
   `Level.isNeverZero` are con-leche's own, run on transient
   `ConLeche.Level` trees, with the two VERDICTS cached on the handles
   (`lvlEq?`, `lvlsEq?`).
5. **One knot, the memoized one.**  con-leche has three (`coreKnot` at
   `id`, `Cached.coreKnotI` with the memos, `coreKnotGated`); the arena's
   `coreKnot` carries the memo probes in its own slots, exactly as the
   Rust port has one knot (DESIGN §3.1, `kernel/type_checker.rs`'s module
   note).  `TypeChecker.lean`'s entries therefore live here.
6. **The memo probes are INLINE in the knot's slots**, not a higher-order
   `memoEI`: con-leche's spelling passes a getter and a setter lambda per
   table, and two closures per slot is what §3.4 rules out.  The BODIES
   stay pure of memo logic, which is the property that matters.

## The caches this module installs

`Arena/CoreState.lean` holds the record; the probes are here.  Five
entry-point memos keyed on the node alone (the depth is not in the key —
a handle carries its own typing context, DESIGN §8.3), `defeq` on the
ordered pair with the verdict, the two level-verdict tables, and the three
lazy instantiated-constant tables that replace every
`cv.type.instantiateLevelParams cv.levelParams us` in the checker.
-/
import ConRon.Arena.PropRead
import ConRon.Arena.Pins
import ConLeche.Kernel.Basis.Names

namespace ConRon.Arena

open ConLeche

/-! ## Fuel for the store walks

DESIGN §8.4 asks for fuel as an explicit `Nat`.  The walks below are over
the handle DAG, so any bound above the store's node count is unreachable;
one top-level `def` (lesson 7: `Nat` literals behind a `def`) keeps the
Rust a `const u64` and keeps the elaborator from unfolding a literal into
every comparison.  `4 000 000 000` is above the representable node count
(2^27 per constructor per tier, ten constructors, two tiers) and below
`2^63`, so it is one machine word. -/

/-- con-leche: none — the fuel every store walk in this module runs at;
see the section note. -/
def coreWalkFuel : Nat := 4000000000

/-! ## Reserved names, interned

DESIGN §8.3, "Exactness": names are compared for INEQUALITY throughout the
checker, and a handle comparison is that comparison because `denoteN` is
injective.  So a reserved name is interned once and compared by word.
Interning a name already in the store is a cons-table probe and appends
nothing; a reserved name absent from the store interns into whatever tier
is live and compares equal to nothing, which is the right answer and goes
with the tier.

**The `Pins` record is in the state since task #97-P6-4a** (`Arena/Pins.lean`,
`Arena/CoreState.lean`'s `Pins`): every reserved name is interned ONCE at the
driver and each of these clauses is now a field read.  Task #97c's
initialisation-order hazard — a pin read before it is filled compares against
the zero word — is killed by the table being an `Array` rather than a record
of fields: an unfilled table is EMPTY, so `pinAt` takes its bounds branch and
stops.  `pin` itself survives for the names that are NOT reserved (the
recursor and projection-function names the modeller builds). -/

/-- con-leche: none — intern a reserved `ConLeche.Name` and hand back its
handle.  The one place the arena turns a name VALUE into a name HANDLE
outside the parser. -/
@[inline] def pin (n : ConLeche.Name) : AM NIdx := internName n

/-- con-leche: none — the empty universe-argument list, off the pin table.
`us == emptyLevels` is con-leche's pattern `.const _ []`. -/
def emptyLevels : AM LsIdx := pinEmptyLevels

/-- con-leche: none — the level `0`, off the pin table: the comparand of every
`Level.isEquiv u .zero` in this module. -/
def zeroLevel : AM LIdx := pinZeroLevel

/-- con-leche: none — the expression `Sort 1` (`.sort (.succ .zero)`), off the
pin table: the pinned type of `Nat`, `String`, `Char` and `Bool`. -/
def sortOne : AM EIdx := pinSortOne

/-- con-leche: none — a level-monomorphic constant `.const n []`,
interned. -/
def constE (n : NIdx) : AM EIdx := do
  let us ← emptyLevels
  internE (.const n us)

/-! ## The level verdicts, cached

DESIGN §8.3: the level ALGORITHM runs on transient trees; what is cached
is the VERDICT, keyed on the handles.  Both tables are per-declaration and
both are dropped by `Caches.dropScratchEntries`. -/

/-- con-leche: ConLeche/Kernel/Level.lean:158-163 isEquiv — `Level.isEquiv`
at two level HANDLES, with the verdict cached on the pair.  `none` is
con-leche's fuel exhaustion and is never cached. -/
def lvlEq? (u v : LIdx) : AM (Option Bool) := do
  let s ← get
  match s.caches.lvlEqC[(u, v)]? with
  | some r => pure (some r)
  | none => do
    let lu ← readLevelM u
    let lv ← readLevelM v
    match Level.isEquiv lu lv with
    | some r => do
      let s ← get
      let mp := s.caches.lvlEqC
      let mp := if mp.size < cacheCap then mp else ∅
      let s := { s with caches := { s.caches with lvlEqC := ∅ } }
      set { s with caches := { s.caches with lvlEqC := mp.insert (u, v) r } }
      pure (some r)
    | none => pure none

/-- con-leche: ConLeche/Kernel/Level.lean:165-172 isEquivList — pairwise
`Level.isEquiv` at two universe-argument LIST handles, cached on the
pair. -/
def lvlsEq? (us vs : LsIdx) : AM (Option Bool) := do
  let s ← get
  match s.caches.lvlsEqC[(us, vs)]? with
  | some r => pure (some r)
  | none => do
    let lu ← readLevelsM us
    let lv ← readLevelsM vs
    match Level.isEquivList lu lv with
    | some r => do
      let s ← get
      let mp := s.caches.lvlsEqC
      let mp := if mp.size < cacheCap then mp else ∅
      let s := { s with caches := { s.caches with lvlsEqC := ∅ } }
      set { s with caches := { s.caches with lvlsEqC := mp.insert (us, vs) r } }
      pure (some r)
    | none => pure none

/-! ## The lazy instantiated-constant caches (DESIGN §8.3, con-leche's
arena task #26)

Every `cv.type.instantiateLevelParams cv.levelParams us` in the checker is
one of the three below.  The key is the name and the universe-argument
list — never the instantiated term, which is the point: the instantiation
is what the cache avoids computing. -/

/-- con-leche: none — a stored constant's TYPE at a universe
instantiation, memoized on `(name, levels)`.  DESIGN §8.3's
"instantiated-constant cache", `constTyAt`. -/
def constTyAt (cv : IConstantVal) (us : LsIdx) : AM EIdx := do
  let s ← get
  match s.caches.constTyC[(cv.name, us)]? with
  | some r => pure r
  | none => do
    let r ← instLPFast coreWalkFuel cv.levelParams us cv.type
    let s ← get
    let mp := s.caches.constTyC
    let mp := if mp.size < cacheCap then mp else ∅
    let s := { s with caches := { s.caches with constTyC := ∅ } }
    set { s with caches := { s.caches with constTyC := mp.insert (cv.name, us) r } }
    pure r

/-- con-leche: none — a stored definition's VALUE at a universe
instantiation, memoized on `(name, levels)` (DESIGN §8.3, `constValAt`).
The delta step's only expensive half. -/
def constValAt (n : NIdx) (lps : List NIdx) (value : EIdx) (us : LsIdx) :
    AM EIdx := do
  let s ← get
  match s.caches.constValC[(n, us)]? with
  | some r => pure r
  | none => do
    let r ← instLPFast coreWalkFuel lps us value
    let s ← get
    let mp := s.caches.constValC
    let mp := if mp.size < cacheCap then mp else ∅
    let s := { s with caches := { s.caches with constValC := ∅ } }
    set { s with caches := { s.caches with constValC := mp.insert (n, us) r } }
    pure r

/-- con-leche: none — an iota rule's right-hand side at the recursor's
universe instantiation, memoized on `(recursor, rule constructor, levels)`
— the three data that determine it (DESIGN §8.3, `ruleRhsAt`). -/
def ruleRhsAt (recName ctor : NIdx) (lps : List NIdx) (rhs : EIdx)
    (us : LsIdx) : AM EIdx := do
  let s ← get
  match s.caches.ruleRhsC[(recName, ctor, us)]? with
  | some r => pure r
  | none => do
    let r ← instLPFast coreWalkFuel lps us rhs
    let s ← get
    let mp := s.caches.ruleRhsC
    let mp := if mp.size < cacheCap then mp else ∅
    let s := { s with caches := { s.caches with ruleRhsC := ∅ } }
    set { s with caches :=
      { s.caches with ruleRhsC := mp.insert (recName, ctor, us) r } }
    pure r

/-! ## The error -/

/-- con-leche: ConLeche/Kernel/Core.lean:82-102 unknownConstError — **the
verdict at a constant the environment does not know**: `sorryAx` is a
positively detected unsupported feature and DECLINES, every other
unresolved name is a malformed stream and REJECTS.

**No readback for the message** (task #97-P5-Core round 4's audit): the name
used to be read back with `readNameM` for the text, which the port does not do
— its message drops the interpolation (§3.1) — so at a dangling name handle
the twin failed `internal` where the port answers `Invalid`, and on a live one
it wrote `readNC`, a cache the port's run leaves alone.  Messages are never
compared (DESIGN §3.1), so the text is constant. -/
def unknownConstError (n : NIdx) : AM CheckError := do
  let sa ← pinSorryAx
  if n == sa then pure (.notImplemented "use of the sorryAx axiom")
  else pure (.invalid "unknown constant")

/-! ## The record of mutually recursive entry points -/

/-- con-leche: ConLeche/Kernel/Core.lean:104-130 CoreFns — the record of
mutually recursive core entry points, over handles.  con-leche is
polymorphic in the monad; the arena is at `AM` and nothing else (DESIGN
§8.4), so the `m` parameter is gone and the name carries an `A`. -/
structure CoreFnsA where
  whnfCore : Nat → EIdx → AM EIdx
  whnf : Nat → EIdx → AM EIdx
  infer : Nat → EIdx → AM EIdx
  defeq : Nat → EIdx → EIdx → AM Bool
  annotate : Nat → EIdx → AM EIdx
  /-- Type inference at the **infer-only grade** (con-leche's task #170):
  the entry every *internal* inference call site uses. -/
  inferIO : Nat → EIdx → AM EIdx

/-- con-leche: ConLeche/Kernel/Core.lean:132-138 CoreFns.ioView — the
**io-grade view** of a core record: the record whose full-grade `infer`
slot is the io slot, so a body written against `r.infer` recurses at the io
grade when handed `r.ioView`. -/
def CoreFnsA.ioView (r : CoreFnsA) : CoreFnsA :=
  { r with infer := r.inferIO }

/-! ## The bodies' small helpers -/

/-- con-leche: ConLeche/Kernel/Core.lean:151-154 liftFueled — lift a
fuel-style partial result; `none` is an internal error. -/
def liftFueled {α : Type} (what : String) : Option α → AM α
  | some a => pure a
  | none => fail (.internal s!"fuel exhausted: {what}")

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:41-44 projModelName — the
model-side name of field `i`'s projection for `T`. -/
def projModelName (T : NIdx) (i : Nat) : AM NIdx := do
  let m ← internNNode (.str T "_model")
  internNNode (.str m ("proj_" ++ toString i))

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:46-53 isCtorApp — is the
expression headed by a stored constructor? -/
def isCtorApp (fe : IFEnv) (e : EIdx) : AM Bool := do
  let h ← getAppFn coreWalkFuel e
  if h.tag == ETag.const then
    match ← view h with
    | .const c _ =>
      match fe.find? c with
      | some (.ctorInfo _ _ _) => pure true
      | _ => pure false
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:55-62 piResultIsProp — does the
syntactic pi telescope end in a (normalized) `Prop`? -/
def piResultIsProp (e : EIdx) : AM Bool := do
  let h ← piResult coreWalkFuel e
  if h.tag == ETag.sort then
    match ← view h with
    | .sort u => do
      let z ← zeroLevel
      pure ((← lvlEq? u z) == some true)
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:64-72 piResultZ — **the
result-sort zero-ness datum of an inductive's type** (`IndCaps.sortZ`). -/
def piResultZ (e : EIdx) : AM PropWhen := do
  let h ← piResult coreWalkFuel e
  if h.tag == ETag.sort then
    match ← view h with
    | .sort u => do
      let l ← readLevelM u
      pure (Level.zeronessOf l)
    | _ => pure (.ifAllZero [])
  else pure (.ifAllZero [])

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:74-82 piResultNeverZero — is the
result sort of a stored inductive's type, instantiated at the given levels,
provably nonzero (official `is_never_zero`)? -/
def piResultNeverZero (lps : List NIdx) (us : LsIdx) (e : EIdx) : AM Bool := do
  let h ← piResult coreWalkFuel e
  if h.tag == ETag.sort then
    match ← view h with
    | .sort u => do
      let ks ← readNamesM lps
      let vs ← readLevelsM us
      let l ← readLevelM u
      pure (Level.subst ks vs l).isNeverZero
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:84-95 capsNeverZero — the same
question read off the STORED datum, which is what the checker runs. -/
def capsNeverZero (lps : List NIdx) (us : LsIdx) (caps : IIndCaps) :
    AM Bool := do
  let ks ← readNamesM lps
  let vs ← readLevelsM us
  pure (Level.substPW ks vs caps.sortZ).isNever

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:97-134 isUnitLikeTy — is this
(whnf'd) type expression a unit-like inductive type?  con-leche's task #161
item C1: the head-name comparison against `PUnit` comes FIRST and
short-circuits after one comparison at every other head. -/
def isUnitLikeTy (fe : IFEnv) (h : EIdx) : AM Bool := do
  if h.tag == ETag.const then
    match ← view h with
    | .const c _ => do
      let pu ← pinPUnit
      if c != pu then pure false
      else
        match fe.find? pu with
        | some (.indInfo _ _) => do
          let pr ← pinPUnitRec
          match fe.find? pr with
          | some (.recInfo _ mI rP [r]) => pure (mI == rP && r.nfields == 0)
          | _ => pure false
        | _ => pure false
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:136-155 unfoldDefinition — unfold
the (application of a) definition at the head, one step.  The stored value
is instantiated through `constValAt`, so a constant unfolded twice at the
same levels pays the substitution once. -/
def unfoldDefinition (fe : IFEnv) (e : EIdx) : AM (Option EIdx) := do
  let hh ← getAppFn coreWalkFuel e
  if hh.tag == ETag.const then
    match ← view hh with
    | .const n us =>
      match fe.find? n with
      | some (.defnInfo cv value _) => do
        let usl ← viewLs us
        if usl.length = cv.levelParams.length then do
          let v ← constValAt n cv.levelParams value us
          let args ← getAppArgs coreWalkFuel e
          let r ← mkAppN v args
          pure (some r)
        else pure none
      | _ => pure none
    | _ => pure none
  else pure none

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:157-170 unfoldableHead — may the
delta step unfold `e`'s head (the official kernel's `is_delta`)?  The
DECISION, taken before the unfolding is materialized. -/
def unfoldableHead (fe : IFEnv) (e : EIdx) : AM Bool := do
  let hh ← getAppFn coreWalkFuel e
  if hh.tag == ETag.const then
    match ← view hh with
    | .const n us =>
      match fe.find? n with
      | some (.defnInfo cv _ _) => do
        match ← viewLsLen us with
        | none => failDanglingLs
        | some usl =>
        pure (usl == cv.levelParams.length)
      | _ => pure false
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:172-181 headHint — the
reducibility hint of the constant at the head of `e`. -/
def headHint (fe : IFEnv) (e : EIdx) : AM ReducibilityHint := do
  let hh ← getAppFn coreWalkFuel e
  if hh.tag == ETag.const then
    match ← view hh with
    | .const n _ =>
      match fe.find? n with
      | some (.defnInfo _ _ hint) => pure hint
      | _ => pure .opaque
    | _ => pure .opaque
  else pure .opaque

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:183-192 sameConstHeads — are `a`
and `b` applications of the *same* constant (the lazy delta same-head
short-circuit)?  Both sides must actually be applications. -/
def sameConstHeads (a b : EIdx) : AM Bool := do
  if a.tag == ETag.app then
    match ← view a with
    | .app f₁ _ =>
      if b.tag == ETag.app then
        match ← view b with
        | .app f₂ _ => do
          let hh ← getAppFn coreWalkFuel f₁
          if hh.tag == ETag.const then
            match ← view hh with
            | .const n₁ _ =>
              let hh ← getAppFn coreWalkFuel f₂
              if hh.tag == ETag.const then
                match ← view hh with
                | .const n₂ _ => pure (n₁ == n₂)
                | _ => pure false
              else pure false
            | _ => pure false
          else pure false
        | _ => pure false
      else pure false
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:194-200 natLitToConstructor — the
constructor form of a `Nat` literal, one layer. -/
def natLitToConstructor (n : Nat) : AM EIdx := do
  match n with
  | 0 => do
    let z ← pinNatZero
    constE z
  | k + 1 => do
    let s ← pinNatSucc
    let sc ← constE s
    let l ← internE (.lit (.natVal k))
    internE (.app sc l)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:202-206 natIndOk — the stored `Nat`
declaration has the expected shape. -/
def natIndOk : Option IConstantInfo → AM Bool
  | some (.indInfo cv _) => do
    let s1 ← sortOne
    pure (cv.levelParams.isEmpty && cv.type == s1)
  | _ => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:208-212 natZeroOk — the stored
`Nat.zero` declaration has the expected shape. -/
def natZeroOk : Option IConstantInfo → AM Bool
  | some (.ctorInfo cv _ _) => do
    let nt ← pinNat
    let nc ← constE nt
    pure (cv.levelParams.isEmpty && cv.type == nc)
  | _ => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:214-223 natSuccOk — the stored
`Nat.succ` declaration has the expected (annotated) shape. -/
def natSuccOk : Option IConstantInfo → AM Bool
  | some (.ctorInfo cv _ _) => do
    if !cv.levelParams.isEmpty then pure false else do
      let nt ← pinNat
      let nc ← constE nt
      if cv.type.tag == ETag.forallE then
        match ← view cv.type with
        | .forallE dom body _mb => pure (dom == nc && body == nc)
        | _ => pure false
      else pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:225-233 natLitSupported
con-leche: ConLeche/Kernel/FEnv.lean:116-119 natLitSupportedF
Whether the environment supports `Nat` literals.  One twin for con-leche's
two spellings (deviation 1). -/
def natLitSupported (fe : IFEnv) : AM Bool := do
  let nt ← pinNat
  if !(← natIndOk (fe.find? nt)) then pure false else do
    let nz ← pinNatZero
    if !(← natZeroOk (fe.find? nz)) then pure false else do
      let ns ← pinNatSucc
      natSuccOk (fe.find? ns)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:235-260 Expr.constsResolve — do all
constants referenced in `e` (including inside `fvar` type annotations)
resolve in `fe`?  A full walk over the term, hence fuel; unlike the
checker's hot walks it is run once per declaration and carries no memo, as
con-leche's does not. -/
def constsResolve (fe : IFEnv) : Nat → EIdx → AM Bool
  | 0, _ => fail (.internal "fuel exhausted: constsResolve")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ | .sort _ => pure true
    | .lit (.natVal _) => do
      let nt ← pinNat
      let nz ← pinNatZero
      let ns ← pinNatSucc
      pure ((fe.find? nt).isSome && (fe.find? nz).isSome &&
        (fe.find? ns).isSome)
    | .lit (.strVal _) => do
      let nt ← pinNat
      let nz ← pinNatZero
      let ns ← pinNatSucc
      let st ← pinString
      let sl ← pinStringOfList
      let li ← pinList
      let ln ← pinListNil
      let lc ← pinListCons
      let ch ← pinChar
      let co ← pinCharOfNat
      pure ((fe.find? nt).isSome && (fe.find? nz).isSome &&
        (fe.find? ns).isSome && (fe.find? st).isSome &&
        (fe.find? sl).isSome && (fe.find? li).isSome &&
        (fe.find? ln).isSome && (fe.find? lc).isSome &&
        (fe.find? ch).isSome && (fe.find? co).isSome)
    | .const n _ => pure (fe.find? n).isSome
    | .fvar _ ty => constsResolve fe fuel ty
    | .app f a => do
      let x ← constsResolve fe fuel f
      if x then constsResolve fe fuel a else pure false
    | .lam ty body _ | .forallE ty body _ => do
      let x ← constsResolve fe fuel ty
      if x then constsResolve fe fuel body else pure false
    | .letE ty val body => do
      let x ← constsResolve fe fuel ty
      if !x then pure false else do
        let y ← constsResolve fe fuel val
        if y then constsResolve fe fuel body else pure false
    | .proj s _ sub => do
      if (fe.find? s).isSome then constsResolve fe fuel sub else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:262-267 litToCtorIfNat — convert a
`Nat`-literal major premise to constructor form, one layer. -/
def litToCtorIfNat (fe : IFEnv) (h : EIdx) : AM EIdx := do
  if h.tag == ETag.lit then
    match ← view h with
    | .lit (.natVal n) => do
      if ← natLitSupported fe then natLitToConstructor n else pure h
    | _ => pure h
  else pure h

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:269-274 rawNatLit? — a `Nat`
literal reading of a whnf'd expression (the official kernel's
`rawNatLitExt?`). -/
def rawNatLit? (h : EIdx) : AM (Option Nat) := do
  match ← view h with
  | .lit (.natVal n) => pure (some n)
  | .const c us => do
    let e ← emptyLevels
    let nz ← pinNatZero
    pure (if c == nz && us == e then some 0 else none)
  | _ => pure none

/-! ## String literals -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:288-299 strLitToConstructor — the
`List.cons` spine of a string literal's constructor form.  con-leche writes
`s.toList.foldr (init := nil) fun c e => …`; DESIGN §3.4 turns the closure
into this explicit recursion over the character list (P2b's closure audit,
same rule). -/
def strLitConsSpine (cons ofNat nilE : EIdx) : List Char → AM EIdx
  | [] => pure nilE
  | c :: cs => do
    let rest ← strLitConsSpine cons ofNat nilE cs
    let lit ← internE (.lit (.natVal c.toNat))
    let ch ← internE (.app ofNat lit)
    let f ← internE (.app cons ch)
    internE (.app f rest)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:288-299 strLitToConstructor — the
constructor form of a `String` literal: `String.ofList (List.cons.{0} Char
(Char.ofNat (lit c₁)) (… (List.nil.{0} Char)))`. -/
def strLitToConstructor (s : String) : AM EIdx := do
  let z ← zeroLevel
  let zs ← internLsNode [z]
  let chN ← pinChar
  let chC ← constE chN
  let lnN ← pinListNil
  let ln ← internE (.const lnN zs)
  let nilE ← internE (.app ln chC)
  let lcN ← pinListCons
  let lc ← internE (.const lcN zs)
  let cons ← internE (.app lc chC)
  let coN ← pinCharOfNat
  let ofNat ← constE coN
  let spine ← strLitConsSpine cons ofNat nilE s.toList
  let slN ← pinStringOfList
  let sl ← constE slN
  internE (.app sl spine)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:301-307 stringTyOk — the stored
`String` declaration has the expected shape. -/
def stringTyOk : Option IConstantInfo → AM Bool
  | some ci => do
    let cv ← ci.toConstantVal
    let s1 ← sortOne
    pure (cv.levelParams.isEmpty && cv.type == s1)
  | none => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:309-315 charTyOk — the stored
`Char` declaration has the expected shape. -/
def charTyOk : Option IConstantInfo → AM Bool
  | some ci => do
    let cv ← ci.toConstantVal
    let s1 ← sortOne
    pure (cv.levelParams.isEmpty && cv.type == s1)
  | none => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:317-328 listTyOk — the stored
`List` declaration has the expected (annotated) shape `List.{p} : Type p →
Type p`. -/
def listTyOk : Option IConstantInfo → AM Bool
  | some ci => do
    let cv ← ci.toConstantVal
    match cv.levelParams with
    | [p] => do
      let pl ← internLNode (.param p)
      let sp ← internLNode (.succ pl)
      let sort ← internE (.sort sp)
      if cv.type.tag == ETag.forallE then
        match ← view cv.type with
        | .forallE d b _mb => pure (d == sort && b == sort)
        | _ => pure false
      else pure false
    | _ => pure false
  | none => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:330-341 listNilTyOk — the stored
`List.nil` declaration has the expected (annotated) shape. -/
def listNilTyOk : Option IConstantInfo → AM Bool
  | some ci => do
    let cv ← ci.toConstantVal
    match cv.levelParams with
    | [p] => do
      let pl ← internLNode (.param p)
      let sp ← internLNode (.succ pl)
      let sort ← internE (.sort sp)
      let ps ← internLsNode [pl]
      let li ← pinList
      if cv.type.tag == ETag.forallE then
        match ← view cv.type with
        | .forallE d b _mb => do
          if d != sort then pure false else
          if b.tag == ETag.app then
            match ← view b with
            | .app f a =>
              if f.tag == ETag.const then
                match ← view f with
                | .const l1 us1 =>
                  if a.tag == ETag.bvar then
                    match ← view a with
                    | .bvar 0 => pure (l1 == li && us1 == ps)
                    | _ => pure false
                  else pure false
                | _ => pure false
              else pure false
            | _ => pure false
          else pure false
        | _ => pure false
      else pure false
    | _ => pure false
  | none => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:343-360 listConsTyOk — the stored
`List.cons` declaration has the expected (annotated) shape. -/
def listConsTyOk : Option IConstantInfo → AM Bool
  | some ci => do
    let cv ← ci.toConstantVal
    match cv.levelParams with
    | [p] => do
      let pl ← internLNode (.param p)
      let sp ← internLNode (.succ pl)
      let sort ← internE (.sort sp)
      let ps ← internLsNode [pl]
      let li ← pinList
      let b0 ← internE (.bvar 0)
      let b1 ← internE (.bvar 1)
      let b2 ← internE (.bvar 2)
      let l1 ← internE (.const li ps)
      let dom3 ← internE (.app l1 b1)
      let cod3 ← internE (.app l1 b2)
      if cv.type.tag == ETag.forallE then
        match ← view cv.type with
        | .forallE d1 r1 _mb1 => do
          if d1 != sort then pure false else
          if r1.tag == ETag.forallE then
            match ← view r1 with
            | .forallE d2 r2 _mb2 => do
              if d2 != b0 then pure false else
              if r2.tag == ETag.forallE then
                match ← view r2 with
                | .forallE d3 c3 _mb3 => pure (d3 == dom3 && c3 == cod3)
                | _ => pure false
              else pure false
            | _ => pure false
          else pure false
        | _ => pure false
      else pure false
    | _ => pure false
  | none => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:362-371 charOfNatTyOk — the stored
`Char.ofNat` declaration has the expected (annotated) shape `Nat → Char`. -/
def charOfNatTyOk : Option IConstantInfo → AM Bool
  | some ci => do
    let cv ← ci.toConstantVal
    if !cv.levelParams.isEmpty then pure false else do
      let nt ← pinNat
      let nc ← constE nt
      let ch ← pinChar
      let cc ← constE ch
      if cv.type.tag == ETag.forallE then
        match ← view cv.type with
        | .forallE d b _mb => pure (d == nc && b == cc)
        | _ => pure false
      else pure false
  | none => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:373-383 stringOfListTyOk — the
stored `String.ofList` declaration has the expected (annotated) shape
`List.{0} Char → String`. -/
def stringOfListTyOk : Option IConstantInfo → AM Bool
  | some ci => do
    let cv ← ci.toConstantVal
    if !cv.levelParams.isEmpty then pure false else do
      let z ← zeroLevel
      let zs ← internLsNode [z]
      let li ← pinList
      let lc ← internE (.const li zs)
      let ch ← pinChar
      let cc ← constE ch
      let dom ← internE (.app lc cc)
      let st ← pinString
      let sc ← constE st
      if cv.type.tag == ETag.forallE then
        match ← view cv.type with
        | .forallE d b _mb => pure (d == dom && b == sc)
        | _ => pure false
      else pure false
  | none => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:385-403 strLitSupported
con-leche: ConLeche/Kernel/FEnv.lean:121-130 strLitSupportedF
Whether the environment supports `String` literals: the `Nat` literal guard
plus the seven string-support declarations at exactly the expected types. -/
def strLitSupported (fe : IFEnv) : AM Bool := do
  if !(← natLitSupported fe) then pure false else do
    let st ← pinString
    if !(← stringTyOk (fe.find? st)) then pure false else do
      let sl ← pinStringOfList
      if !(← stringOfListTyOk (fe.find? sl)) then pure false else do
        let li ← pinList
        if !(← listTyOk (fe.find? li)) then pure false else do
          let ln ← pinListNil
          if !(← listNilTyOk (fe.find? ln)) then pure false else do
            let lc ← pinListCons
            if !(← listConsTyOk (fe.find? lc)) then pure false else do
              let ch ← pinChar
              if !(← charTyOk (fe.find? ch)) then pure false else do
                let co ← pinCharOfNat
                charOfNatTyOk (fe.find? co)


/-! ## Structural-`Nat` literal acceleration

con-leche's certified fast path (`Core.lean:514-863`): an operation
participates only when its defining recurrence equations hold by
definitional equality — checked once, at install, so *presence in the store
is the certificate*.  The sixteen reserved names are interned here exactly
as the literal guards' are. -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:433 natPredName -/
def natPredName : AM NIdx := pinNatPred
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:434 natAddName -/
def natAddName : AM NIdx := pinNatAdd
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:435 natSubName -/
def natSubName : AM NIdx := pinNatSub
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:436 natMulName -/
def natMulName : AM NIdx := pinNatMul
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:437 natPowName -/
def natPowName : AM NIdx := pinNatPow
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:438 natBeqName -/
def natBeqName : AM NIdx := pinNatBeq
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:439 natBleName -/
def natBleName : AM NIdx := pinNatBle
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:440 natDivName -/
def natDivName : AM NIdx := pinNatDiv
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:441 natModName -/
def natModName : AM NIdx := pinNatMod
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:442 natGcdName -/
def natGcdName : AM NIdx := pinNatGcd
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:443 natLandName -/
def natLandName : AM NIdx := pinNatLand
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:444 natLorName -/
def natLorName : AM NIdx := pinNatLor
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:445 natXorName -/
def natXorName : AM NIdx := pinNatXor
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:446 natShiftLeftName -/
def natShiftLeftName : AM NIdx := pinNatShiftLeft
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:447 natShiftRightName -/
def natShiftRightName : AM NIdx := pinNatShiftRight
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:448 boolName -/
def boolName : AM NIdx := pinBool
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:449 boolTrueName -/
def boolTrueName : AM NIdx := pinBoolTrue
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:450 boolFalseName -/
def boolFalseName : AM NIdx := pinBoolFalse

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:452-457 Expr.isBoolTrue — is `e` the
constant `Bool.true` (the official kernel's `is_constant(e, Bool.true)`):
the name, no universe levels. -/
def isBoolTrue (h : EIdx) : AM Bool := do
  if h.tag == ETag.const then
    match ← view h with
    | .const c us => do
      let el ← emptyLevels
      if us != el then pure false else do
        let bt ← boolTrueName
        pure (c == bt)
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:459-471 Expr.quickPair — the pairs
official's `quick_is_def_eq` decides by itself: two sorts, two literals, two
∀s, two λs.

**The one place the arena compares TAGS and not handles.**  con-leche's
clause is a four-arm structural match that reads only the two constructors;
DESIGN §8.3 makes index inequality structural inequality, so the twin of a
match on the CONSTRUCTOR is a comparison of the handle's four tag bits —
`Idx.tag`, no `view`, no state, no monad.  Comparing the handles themselves
would be the twin of `a == b`, which is a different (and wrong)
predicate. -/
def quickPair (a b : EIdx) : Bool :=
  (a.tag == ETag.sort && b.tag == ETag.sort) ||
  (a.tag == ETag.lit && b.tag == ETag.lit) ||
  (a.tag == ETag.forallE && b.tag == ETag.forallE) ||
  (a.tag == ETag.lam && b.tag == ETag.lam)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:473-481 natOpNames — the certified
structural-`Nat` operations. -/
def natOpNames : AM (List NIdx) := do
  let a ← natPredName; let b ← natAddName; let c ← natSubName
  let d ← natMulName; let e ← natPowName; let f ← natBeqName
  let g ← natBleName
  pure [a, b, c, d, e, f, g]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:483-498 natDivModNames — the
WF-recursive operations with a *pinned-declaration* certified fast path. -/
def natDivModNames : AM (List NIdx) := do
  let a ← natDivName; let b ← natModName; let c ← natGcdName
  let d ← natLandName; let e ← natLorName; let f ← natXorName
  let g ← natShiftLeftName; let h ← natShiftRightName
  pure [a, b, c, d, e, f, g, h]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:500-523 natOpDeps — the operations
(transitively) involved in `c`'s recurrences. -/
def natOpDeps (c : NIdx) : AM (List NIdx) := do
  let pr ← natPredName; let ad ← natAddName; let su ← natSubName
  let mu ← natMulName; let po ← natPowName; let be ← natBeqName
  let bl ← natBleName; let di ← natDivName; let mo ← natModName
  let gc ← natGcdName; let la ← natLandName; let lo ← natLorName
  let xo ← natXorName; let sl ← natShiftLeftName; let sr ← natShiftRightName
  if c == pr then pure [pr]
  else if c == ad then pure [ad]
  else if c == su then pure [pr, su]
  else if c == mu then pure [ad, mu]
  else if c == po then pure [ad, mu, po]
  else if c == be then pure [be]
  else if c == bl then pure [bl]
  else if c == di then pure [pr, su, bl, di]
  else if c == mo then pure [pr, su, bl, mo]
  else if c == gc then pure [bl, mo, gc]
  else if c == la then pure [ad, mu, bl, di, mo, la]
  else if c == lo then pure [ad, su, mu, bl, di, mo, lo]
  else if c == xo then pure [ad, mu, bl, di, mo, xo]
  else if c == sl then pure [su, mu, bl, sl]
  else if c == sr then pure [su, bl, di, sr]
  else pure []

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations — `ap1 n a`,
one of the equation builder's three local lambdas.  DESIGN §3.4 forbids the
closure, so each is a named `def`. -/
def natAp1 (n : NIdx) (a : EIdx) : AM EIdx := do
  let f ← constE n
  internE (.app f a)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations — `ap2 n a b`. -/
def natAp2 (n : NIdx) (a b : EIdx) : AM EIdx := do
  let f ← natAp1 n a
  internE (.app f b)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations — the
defining recurrence equations of a structural-`Nat` operation, over
constructor forms with free variables `d`, `d + 1` (binder-free, so the
equation sides carry no annotations). -/
def natOpEquations (d : Nat) (c : NIdx) : AM (List (EIdx × EIdx)) := do
  let nN ← pinNat
  let natTy ← constE nN
  let x ← internE (.fvar d natTy)
  let y ← internE (.fvar (d + 1) natTy)
  let zN ← pinNatZero
  let z ← constE zN
  let sN ← pinNatSucc
  let sx ← natAp1 sN x
  let sy ← natAp1 sN y
  let bT ← constE (← boolTrueName)
  let bF ← constE (← boolFalseName)
  let pr ← natPredName; let ad ← natAddName; let su ← natSubName
  let mu ← natMulName; let po ← natPowName; let be ← natBeqName
  let bl ← natBleName
  if c == pr then do
    let l1 ← natAp1 c z
    let l2 ← natAp1 c sx
    pure [(l1, z), (l2, x)]
  else if c == ad then do
    let l1 ← natAp2 c x z
    let l2 ← natAp2 c x sy
    let r2 ← natAp1 sN (← natAp2 c x y)
    pure [(l1, x), (l2, r2)]
  else if c == su then do
    let l1 ← natAp2 c x z
    let l2 ← natAp2 c x sy
    let r2 ← natAp1 pr (← natAp2 c x y)
    pure [(l1, x), (l2, r2)]
  else if c == mu then do
    let l1 ← natAp2 c x z
    let l2 ← natAp2 c x sy
    let r2 ← natAp2 ad (← natAp2 c x y) x
    pure [(l1, z), (l2, r2)]
  else if c == po then do
    let l1 ← natAp2 c x z
    let sz ← natAp1 sN z
    let l2 ← natAp2 c x sy
    let r2 ← natAp2 mu (← natAp2 c x y) x
    pure [(l1, sz), (l2, r2)]
  else if c == be then do
    let l1 ← natAp2 c z z
    let l2 ← natAp2 c z sy
    let l3 ← natAp2 c sx z
    let l4 ← natAp2 c sx sy
    let r4 ← natAp2 c x y
    pure [(l1, bT), (l2, bF), (l3, bF), (l4, r4)]
  else if c == bl then do
    let l1 ← natAp2 c z y
    let l2 ← natAp2 c sx z
    let l3 ← natAp2 c sx sy
    let r3 ← natAp2 c x y
    pure [(l1, bT), (l2, bF), (l3, r3)]
  else pure []

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:556-582 natOpResult — the reduct of
op `c` on literal arguments (`pred` ignores the second slot).  `ron::Nat` is
con-leche's `Nat` here, and a literal is a `Literal` value in a `lit`
node. -/
def natOpResult (c : NIdx) (a b : Nat) : AM (Option EIdx) := do
  let pr ← natPredName; let ad ← natAddName; let su ← natSubName
  let mu ← natMulName; let po ← natPowName; let be ← natBeqName
  let bl ← natBleName; let di ← natDivName; let mo ← natModName
  let gc ← natGcdName; let la ← natLandName; let lo ← natLorName
  let xo ← natXorName; let sl ← natShiftLeftName; let sr ← natShiftRightName
  if c == pr then do let x ← internE (.lit (.natVal (a - 1))); pure (some x)
  else if c == ad then do let x ← internE (.lit (.natVal (a + b))); pure (some x)
  else if c == su then do let x ← internE (.lit (.natVal (a - b))); pure (some x)
  else if c == mu then do let x ← internE (.lit (.natVal (a * b))); pure (some x)
  else if c == po then
    -- the divergence audit's S2: official `reduce_pow` refuses exponents
    -- above `ReducePowMaxExp = 1 << 24` and lets `Nat.pow` unfold instead
    if b > 16777216 then pure none
    else do let x ← internE (.lit (.natVal (a ^ b))); pure (some x)
  else if c == di then do let x ← internE (.lit (.natVal (a / b))); pure (some x)
  else if c == mo then do let x ← internE (.lit (.natVal (a % b))); pure (some x)
  else if c == gc then do
    let x ← internE (.lit (.natVal (Nat.gcd a b))); pure (some x)
  else if c == la then do
    let x ← internE (.lit (.natVal (Nat.land a b))); pure (some x)
  else if c == lo then do
    let x ← internE (.lit (.natVal (Nat.lor a b))); pure (some x)
  else if c == xo then do
    let x ← internE (.lit (.natVal (Nat.xor a b))); pure (some x)
  else if c == sl then do
    let x ← internE (.lit (.natVal (Nat.shiftLeft a b))); pure (some x)
  else if c == sr then do
    let x ← internE (.lit (.natVal (Nat.shiftRight a b))); pure (some x)
  else if c == be then do
    let n ← if a = b then boolTrueName else boolFalseName
    let x ← constE n
    pure (some x)
  else if c == bl then do
    let n ← if a <= b then boolTrueName else boolFalseName
    let x ← constE n
    pure (some x)
  else pure none

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:584-600 natOpGuard — the dependency
half of the guard.  con-leche writes `(natOpDeps c).all (fun n => …)`;
DESIGN §3.4's rule for a `List` walk is a named helper, so this is one. -/
def natOpDepsStored (fe : IFEnv) : List NIdx → AM Bool
  | [] => pure true
  | n :: ns =>
    match fe.find? n with
    | some (.defnInfo cv _ _) =>
      if cv.levelParams.isEmpty then natOpDepsStored fe ns else pure false
    | _ => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:584-600 natOpGuard
con-leche: ConLeche/Kernel/FEnv.lean:132-145 natOpGuardF
Stored-constant guards for op `c`: the `Nat` basis, every dependency stored
as a definition, and (for the `Bool`-valued ops and the `ble`-guarded
`div`/`mod`) the `Bool` constructors stored. -/
def natOpGuard (fe : IFEnv) (c : NIdx) : AM Bool := do
  if !(← natLitSupported fe) then pure false else do
    let deps ← natOpDeps c
    if !(← natOpDepsStored fe deps) then pure false else do
      let be ← natBeqName
      let bl ← natBleName
      let dm ← natDivModNames
      if c == be || c == bl || dm.contains c then do
        let bt ← boolTrueName
        let okT ←
          match fe.find? bt with
          | some ci => do let cv ← ci.toConstantVal; pure cv.levelParams.isEmpty
          | none => pure false
        if !okT then pure false else do
          let bf ← boolFalseName
          match fe.find? bf with
          | some ci => do let cv ← ci.toConstantVal; pure cv.levelParams.isEmpty
          | none => pure false
      else pure true

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:602-612 natOpWfNames — the
pin-certified WF-recursive `Nat` operations, as a *safety net*. -/
def natOpWfNames : AM (List NIdx) := do
  let a ← natDivName; let b ← natModName; let c ← natGcdName
  let d ← natLandName; let e ← natLorName; let f ← natXorName
  let g ← natShiftLeftName; let h ← natShiftRightName
  pure [a, b, c, d, e, f, g, h]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:614-620 Expr.substConst0 —
substitute the level-monomorphic constant `n` by `r` through an application
spine (the equation sides are binder-free, so only `app` recurses). -/
def substConst0 (n : NIdx) (r : EIdx) : Nat → EIdx → AM EIdx
  | 0, _ => fail (.internal "fuel exhausted: substConst0")
  | fuel + 1, h => do
    match ← view h with
    | .const c us => do
      let el ← emptyLevels
      if c == n && us == el then pure r else pure h
    | .app f a => do
      let f' ← substConst0 n r fuel f
      let a' ← substConst0 n r fuel a
      internE (.app f' a')
    | _ => pure h

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:622-638 Expr.substConstAll —
substitute the level-monomorphic constant `n` by the *closed* term `r`
everywhere, including under binders.  `fvar` annotations are not entered. -/
def substConstAll (n : NIdx) (r : EIdx) : Nat → EIdx → AM EIdx
  | 0, _ => fail (.internal "fuel exhausted: substConstAll")
  | fuel + 1, h => do
    match ← view h with
    | .const c us => do
      let el ← emptyLevels
      if c == n && us == el then pure r else pure h
    | .app f a => do
      let f' ← substConstAll n r fuel f
      let a' ← substConstAll n r fuel a
      internE (.app f' a')
    | .lam ty b mb => do
      let ty' ← substConstAll n r fuel ty
      let b' ← substConstAll n r fuel b
      internE (.lam ty' b' mb)
    | .forallE ty b mb => do
      let ty' ← substConstAll n r fuel ty
      let b' ← substConstAll n r fuel b
      internE (.forallE ty' b' mb)
    | .letE ty v b => do
      let ty' ← substConstAll n r fuel ty
      let v' ← substConstAll n r fuel v
      let b' ← substConstAll n r fuel b
      internE (.letE ty' v' b')
    | .proj s i e => do
      let e' ← substConstAll n r fuel e
      internE (.proj s i e')
    | _ => pure h

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:640-650 natOpCod — the pinned
codomain of a structural-`Nat` operation: `Bool` for the comparisons, `Nat`
otherwise. -/
def natOpCod (fe : IFEnv) (c : NIdx) (e : EIdx) : AM Bool := do
  let be ← natBeqName
  let bl ← natBleName
  if c == be || c == bl then do
    let bn ← boolName
    let bc ← constE bn
    if e != bc then pure false else
      match fe.find? bn with
      | some ci => do
        let cv ← ci.toConstantVal
        let s1 ← sortOne
        pure (cv.levelParams.isEmpty && cv.type == s1)
      | none => pure false
  else do
    let nn ← pinNat
    let nc ← constE nn
    pure (e == nc)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:652-667 natOpTyPinned — the pinned
type of a certified `Nat` operation: `Nat → Nat` for the unary `pred`,
`Nat → Nat → Nat` for the arithmetic operations, `Nat → Nat → Bool` for the
comparisons. -/
def natOpTyPinned (fe : IFEnv) (c : NIdx) (ty : EIdx) : AM Bool := do
  let nn ← pinNat
  let nc ← constE nn
  let pr ← natPredName
  if c == pr then do
    if ty.tag == ETag.forallE then
      match ← view ty with
      | .forallE dom body _mb =>
        if dom == nc then natOpCod fe c body else pure false
      | _ => pure false
    else pure false
  else do
    if ty.tag == ETag.forallE then
      match ← view ty with
      | .forallE dom rest _mb => do
        if rest.tag == ETag.forallE then
          match ← view rest with
          | .forallE dom2 body _mb2 =>
            if dom == nc && dom2 == nc then natOpCod fe c body else pure false
          | _ => pure false
        else pure false
      | _ => pure false
    else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:669-675 natOpStoredOk — op `n` is
stored as a level-monomorphic definition with the pinned type. -/
def natOpStoredOk (fe : IFEnv) (n : NIdx) : AM Bool := do
  match fe.find? n with
  | some (.defnInfo cv _ _) =>
    if cv.levelParams.isEmpty then natOpTyPinned fe n cv.type else pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:677-700 natOpStored
con-leche: ConLeche/Kernel/FEnv.lean:147-151 natOpStoredF
**The reduction-time test for a certified `Nat` operation** (con-leche's
task #161 item B3): is `c` stored as a definition at all?  The full
`natOpGuard` is carried by the install fold invariant. -/
def natOpStored (fe : IFEnv) (c : NIdx) : AM Bool := do
  match fe.find? c with
  | some (.defnInfo _ _ _) => pure true
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — the binary
literal acceleration's name test.  con-leche writes a fourteen-way disjunction
inline; over handles the comparands have to be interned first, so the
chain is its own `def` and the caller reads one `Bool`. -/
def natBinOpName (c : NIdx) : AM Bool := do
  let ad ← natAddName; let su ← natSubName; let mu ← natMulName
  let po ← natPowName; let be ← natBeqName; let bl ← natBleName
  let di ← natDivName; let mo ← natModName; let gc ← natGcdName
  let la ← natLandName; let lo ← natLorName; let xo ← natXorName
  let sl ← natShiftLeftName; let sr ← natShiftRightName
  pure (c == ad || c == su || c == mu || c == po || c == be || c == bl ||
    c == di || c == mo || c == gc || c == la || c == lo || c == xo ||
    c == sl || c == sr)

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — literal
acceleration (the official kernel's `reduceNat`, run in the `whnf` loop
*before* delta-unfolding).  The divergence audit's D15 is preserved: the
FIRST argument is head-normalised and, unless it is a literal, the step
fails WITHOUT touching the second. -/
def reduceNat (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e : EIdx) :
    AM (Option EIdx) := do
  if e.tag == ETag.app then
    match ← view e with
    | .app f b => do
      match ← view f with
      | .const c us => do
        -- con-leche's `.app (.const c []) a`: `b` is its `a`
        let el ← emptyLevels
        if us != el then pure none else do
          let ns ← pinNatSucc
          if c == ns && (← natLitSupported fe) then do
            match ← rawNatLit? (← r.whnf depth b) with
            | some n => do
              let x ← internE (.lit (.natVal (n + 1)))
              pure (some x)
            | none => pure none
          else pure none
      | .app g a => do
        -- con-leche's `.app (.app (.const c []) a) b`
        if g.tag == ETag.const then
          match ← view g with
          | .const c us => do
            let el ← emptyLevels
            if us != el then pure none else do
              if (← natBinOpName c) && (← natOpStored fe c) then do
                match ← rawNatLit? (← r.whnf depth a) with
                | some n₁ => do
                  match ← rawNatLit? (← r.whnf depth b) with
                  | some n₂ => natOpResult c n₁ n₂
                  | none => pure none
                | none => pure none
              else do
                let wf ← natOpWfNames
                if wf.contains c && (← natLitSupported fe) then do
                  match ← rawNatLit? (← r.whnf depth a) with
                  | some _ => do
                    match ← rawNatLit? (← r.whnf depth b) with
                    | some _ => do
                      -- no readback for the message: the port has none
                      -- (round 4's audit)
                      fail (.notImplemented "native Nat computation on literals")
                    | none => pure none
                  | none => pure none
                else pure none
          | _ => pure none
        else pure none
      | _ => pure none
    | _ => pure none
  else pure none


/-! ## The certification helpers

con-leche's `Core.lean`:865-1310.  Every one of these recurses structurally
on a LIST (an argument spine, a slot index list), so none of them takes
fuel; what they call into the store does. -/

/-- con-leche: ConLeche/Cached/CoreC.lean:168-193 iotaCertsIAux — certify a
spine against a recursor telescope: each argument's inferred type is defeq to
the corresponding (instantiated) domain.  **The ι-slot licence**: at a
*licensed* walk (`lic = true`) a slot whose ∀-binder datum is `.never` is
skipped.

**Batched** (task #97-P6-9), which is con-leche's own CACHED-tier clause: the
chained spec runs one `instantiate1` per slot down the telescope; this carries
the pending substitutions in an accumulator and opens each domain in ONE
`instantiateList`.  The equation the bridge cites is
`Verify/Cached/DiscC1.lean:131 iotaCertsCAux_sim` — `iotaCertsIAux ty acc args`
simulates `iotaCerts (ty.instantiateList acc) args`.

The accumulator is an `Array` in PUSH order (task #97-P6-15). -/
def iotaCertsAux (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (lic : Bool)
    (h : EIdx) (acc : Array EIdx) (args : Array EIdx) (i : Nat) : AM Bool := do
  if hi : i < args.size then do
    match ← view h with
    | .forallE ty body mb => do
      let arg := args[i]
      if lic && mb.pw.isNever then
        iotaCertsAux r fe depth lic body (acc.push arg) args (i + 1)
      else do
        let ty2 ← instantiateListFast coreWalkFuel ty acc 0
        -- con-leche's task #172 B4: the spine certificate's inference at
        -- the io grade
        let ta ← r.inferIO depth arg
        if ← r.defeq depth ta ty2 then
          iotaCertsAux r fe depth lic body (acc.push arg) args (i + 1)
        else pure false
    | .bvar _ => do
      -- The telescope ran out of syntactic binders with a pending
      -- substitution: flush it and look again.  This is `iotaCertsIAux`'s own
      -- re-entry clause and is why the measure is lexicographic.
      if acc.size = 0 then pure false
      else do
        let ty2 ← instantiateListFast coreWalkFuel h acc 0
        iotaCertsAux r fe depth lic ty2 #[] args i
    | _ => pure false
  else pure true
termination_by (args.size - i, acc.size)

/-- con-leche: ConLeche/Kernel/Core.lean:210-243 iotaCerts — the
empty-accumulator entry of `iotaCertsAux`. -/
def iotaCerts (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (lic : Bool)
    (h : EIdx) (args : List EIdx) : AM Bool :=
  iotaCertsAux r fe depth lic h #[] args.toArray 0

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:702-707 piResidual — peel a
∀-telescope along an argument list. -/
def piResidual : EIdx → List EIdx → AM (Option EIdx)
  | e, [] => pure (some e)
  | h, a :: as => do
    if h.tag == ETag.forallE then
      match ← view h with
      | .forallE _ b _ => do
        let b' ← instantiate1Fast coreWalkFuel b a 0
        piResidual b' as
      | _ => pure none
    else pure none

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — pairwise
definitional equality of two spines. -/
def defEqList (r : CoreFnsA) (fe : IFEnv) (depth : Nat) :
    List EIdx → List EIdx → AM Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if ← r.defeq depth a b then defEqList r fe depth as bs else pure false
  | _, _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:256-272 iotaIndexOk — the
canonical-index comparison of a firing ι redex. -/
def iotaIndexOk (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (mI rP cnP : Nat)
    (tyCtor : EIdx) (margs idx : List EIdx) : AM Bool :=
  if mI = rP then pure true
  else do
    match ← piResidual tyCtor margs with
    | some residual => do
      let args ← getAppArgs coreWalkFuel residual
      defEqList r fe depth (args.drop cnP) idx
    | none => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:274-305 proofIrrel — proof
irrelevance certification: both sides' types whnf to the basis unit type,
or both sides' types' *sorts* are `Prop`. -/
def proofIrrel (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    AM Bool := do
  -- con-leche's task #172 B4: every inference here is at the io grade
  let ta ← r.inferIO depth a
  if ← isUnitLikeTy fe (← r.whnf depth ta) then do
    let tb ← r.inferIO depth b
    if ← isUnitLikeTy fe (← r.whnf depth tb) then pure true else pure false
  else do
    let hh ← r.whnf depth (← r.inferIO depth ta)
    if hh.tag == ETag.sort then
      match ← view hh with
      | .sort uT => do
        let z ← zeroLevel
        let okA ← liftFueled "level comparison" (← lvlEq? uT z)
        let tb ← r.inferIO depth b
        let hh ← r.whnf depth (← r.inferIO depth tb)
        if hh.tag == ETag.sort then
          match ← view hh with
          | .sort vT => do
            let okB ← liftFueled "level comparison" (← lvlEq? vT z)
            pure (okA && okB)
          | _ => pure false
        else pure false
      | _ => pure false
    else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — **the hoisted
proof-irrelevance test** (con-leche's task #168, Option U): the `Prop`
branch of `proofIrrel` alone, with the head-symbol readers deciding both
fast arms before any inference. -/
def propIrrel (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    AM Bool := do
  if (← notProofFast fe coreWalkFuel a) || (← notProofFast fe coreWalkFuel b) then
    pure false
  else if (← isProofFast fe coreWalkFuel a) && (← isProofFast fe coreWalkFuel b) then
    -- the yes arm (con-leche's task #168 stage 3): the squash-regime licence
    pure true
  else do
    let ta ← r.inferIO depth a
    let hh ← r.whnf depth (← r.inferIO depth ta)
    if hh.tag == ETag.sort then
      match ← view hh with
      | .sort uT => do
        let z ← zeroLevel
        let okA ← liftFueled "level comparison" (← lvlEq? uT z)
        let tb ← r.inferIO depth b
        let hh ← r.whnf depth (← r.inferIO depth tb)
        if hh.tag == ETag.sort then
          match ← view hh with
          | .sort vT => do
            let okB ← liftFueled "level comparison" (← lvlEq? vT z)
            pure (okA && okB)
          | _ => pure false
        else pure false
      | _ => pure false
    else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:351-374 structEtaProjCerts — the
per-projection telescope certificates of a structural eta certification at a
**projection-function** slot family. -/
def structEtaProjCerts (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (T : NIdx)
    (us' : LsIdx) (targs : List EIdx) (b : EIdx) (lpsT : List NIdx) :
    List Nat → AM Bool
  | [] => pure true
  | i :: rest => do
    match fe.find? (← projFnName T i) with
    | some (.recInfo cvp _ _ _) => do
      let peeled ← stripPis (targs.length + 1) cvp.type
      if cvp.levelParams = lpsT ∧ peeled.isSome = true then do
        let ty ← constTyAt cvp us'
        if ← iotaCerts r fe depth false ty (targs ++ [b]) then
          structEtaProjCerts r fe depth T us' targs b lpsT rest
        else pure false
      else pure false
    | _ => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:709-714 towerSlotsAll — the slot
walk.  con-leche writes `(List.range nF).all fun j => …`; DESIGN §3.4's rule
turns the closure into a counted recursion. -/
def towerSlotsAllGo (fe : IFEnv) (T : NIdx) : Nat → Nat → AM Bool
  | 0, _ => pure true
  | n + 1, j => do
    if (← fe.findProj? T j).isSome then towerSlotsAllGo fe T n (j + 1)
    else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:709-714 towerSlotsAll
con-leche: ConLeche/Kernel/FEnv.lean:97-99 FEnv.towerSlotsAllF
Are all `nF` projection slots of `T` table entries? -/
def towerSlotsAll (fe : IFEnv) (T : NIdx) (nF : Nat) : AM Bool :=
  towerSlotsAllGo fe T nF 0

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:716-724 recSlotsAll — the
projection-function slot walk, as a counted recursion. -/
def recSlotsAllGo (fe : IFEnv) (T : NIdx) : Nat → Nat → AM Bool
  | 0, _ => pure true
  | n + 1, j => do
    match fe.find? (← projFnName T j) with
    | some (.recInfo _ _ _ _) => recSlotsAllGo fe T n (j + 1)
    | _ => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:716-724 recSlotsAll
con-leche: ConLeche/Kernel/FEnv.lean:105-110 FEnv.recSlotsAllF
Are all `nF` projection slots of `T` recursor-backed projection
functions? -/
def recSlotsAll (fe : IFEnv) (T : NIdx) (nF : Nat) : AM Bool :=
  recSlotsAllGo fe T nF 0

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:726-736 etaProjs — the `.proj`
half of the fabricated projections, as a counted recursion. -/
def projNodesGo (T : NIdx) (b : EIdx) : Nat → Nat → AM (List EIdx)
  | 0, _ => pure []
  | n + 1, j => do
    let p ← internE (.proj T j b)
    let rest ← projNodesGo T b n (j + 1)
    pure (p :: rest)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:726-736 etaProjs — the
projection-function half, as a counted recursion. -/
def projAppsGo (T : NIdx) (us : LsIdx) (targs : List EIdx) (b : EIdx) :
    Nat → Nat → AM (List EIdx)
  | 0, _ => pure []
  | n + 1, j => do
    let f ← internE (.const (← projFnName T j) us)
    let p ← mkAppN f (targs ++ [b])
    let rest ← projAppsGo T us targs b n (j + 1)
    pure (p :: rest)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:726-736 etaProjs — the fabricated
projections of a structure-eta spine: `.proj T j b` nodes when every slot has
a table entry, else the modeled path's projection-function applications. -/
def etaProjs (fe : IFEnv) (T : NIdx) (us : LsIdx) (targs : List EIdx)
    (b : EIdx) (nF : Nat) : AM (List EIdx) := do
  if ← towerSlotsAll fe T nF then projNodesGo T b nF 0
  else projAppsGo T us targs b nF 0

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames —
the names reserved for the pinned basis blocks, interned.  `contains` is
then handle equality, as everywhere else in this module. -/
def reservedBasisNames : AM (List NIdx) := do
  let a ← pinEq
  let b ← pin ConLeche.eqReflName
  let c ← pin (ConLeche.eqName.str "rec")
  let d ← pinNat
  let e ← pinNatZero
  let f ← pinNatSucc
  let g ← pin (ConLeche.natName.str "rec")
  let h ← pinPUnit
  let i ← pin ConLeche.punitUnitName
  let j ← pin (ConLeche.punitName.str "rec")
  let k ← pin ConLeche.emptyName
  let l ← pin (ConLeche.emptyName.str "rec")
  let m ← pin ConLeche.falseName
  let n ← pin (ConLeche.falseName.str "rec")
  let o ← pin ConLeche.quotName
  let p ← pin ConLeche.quotMkName
  let q ← pin ConLeche.quotLiftName
  let s ← pin ConLeche.quotIndName
  let t ← pinQuotSound
  pure [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, s, t]

/-- con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith — the
structure-eta certificate against a *given* weak-head-normal type of the
stuck side. -/
def structEtaCertWith (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv)
    (depth : Nat) (a b wtb : EIdx) : AM Bool := do
  let hh ← getAppFn coreWalkFuel a
  if hh.tag == ETag.const then
    match ← view hh with
    | .const c us =>
      match fe.find? c with
      | some (.ctorInfo cvc cnP cnF) => do
        let aargs ← getAppArgs coreWalkFuel a
        if aargs.length = cnP + cnF then do
          let hh ← getAppFn coreWalkFuel wtb
          if hh.tag == ETag.const then
            match ← view hh with
            | .const T us' =>
              match fe.find? T with
              | some (.indInfo cvT caps) => do
                let targs ← getAppArgs coreWalkFuel wtb
                let reserved ← reservedBasisNames
                match ← viewLsLen us' with
                | none => failDanglingLs
                | some uslen =>
                let slots ←
                  if ← towerSlotsAll fe T caps.etaFields then pure true
                  else recSlotsAll fe T caps.etaFields
                if caps.eta = true ∧ caps.etaCtor = c ∧
                    reserved.contains T = false ∧ reserved.contains c = false ∧
                    targs.length = caps.etaParams ∧
                    uslen = cvT.levelParams.length ∧
                    cvc.levelParams = cvT.levelParams ∧ slots = true then do
                  if ← liftFueled "level comparison" (← lvlsEq? us us') then do
                    -- the type-former telescope certificate and the per-slot
                    -- ones are certificate FAMILIES (official's
                    -- `try_eta_struct_core` runs neither), so `mode.certs` gates
                    -- them both: `Cached/CoreC.lean:437` and `:440`
                    let famT ←
                      if mode.certs then
                        iotaCerts r fe depth false (← constTyAt cvT us') targs
                      else pure true
                    if famT then do
                      -- the per-slot certificates are the projection-function
                      -- kind's; a tabled family has none
                      let percerts ←
                        if !mode.certs then pure true
                        else if ← towerSlotsAll fe T caps.etaFields then pure true
                        else
                          structEtaProjCerts r fe depth T us' targs b
                            cvT.levelParams (List.range caps.etaFields)
                      if percerts then do
                        if ← defEqList r fe depth (aargs.take caps.etaParams) targs then do
                          -- synthetic-spine certification (con-leche's task
                          -- #137); a TT-lane check, skipped unless
                          -- `mode.ttChecks`
                          let tt ←
                            if mode.ttChecks then do
                              let tyC ← constTyAt cvc us
                              let projs ← etaProjs fe T us' targs b caps.etaFields
                              iotaCerts r fe depth false tyC (targs ++ projs)
                            else pure true
                          if tt then do
                            let projs ← etaProjs fe T us' targs b caps.etaFields
                            defEqList r fe depth (aargs.drop caps.etaParams) projs
                          else pure false
                        else pure false
                      else pure false
                    else pure false
                  else pure false
                else pure false
              | _ => pure false
            | _ => pure false
          else pure false
        else pure false
      | _ => pure false
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:738-749 etaCtorShape — the
constructor shape official's `try_eta_struct_core` tests before inferring
anything: the candidate's head is a stored constructor applied to exactly
its parameters and fields. -/
def etaCtorShape (fe : IFEnv) (a : EIdx) : AM Bool := do
  let hh ← getAppFn coreWalkFuel a
  if hh.tag == ETag.const then
    match ← view hh with
    | .const c _ =>
      match fe.find? c with
      | some (.ctorInfo _ cnP cnF) => do
        let args ← getAppArgs coreWalkFuel a
        pure (args.length == cnP + cnF)
      | _ => pure false
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:450-473 structEtaCert —
structural eta certification for a stored eta-capable structure.  The
constructor-shape test comes FIRST (the divergence audit's D13). -/
def structEtaCert (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv)
    (depth : Nat) (a b : EIdx) : AM Bool := do
  if ← etaCtorShape fe a then do
    let tb ← r.inferIO depth b
    let wtb ← r.whnf depth tb
    structEtaCertWith mode r fe depth a b wtb
  else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:475-503 structUnitCert —
unit-likeness certification: `a` and `b` inhabit the same stored unit-like
family. -/
def structUnitCert (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv)
    (depth : Nat) (a b : EIdx) : AM Bool := do
  let ta ← r.inferIO depth a
  let wta ← r.whnf depth ta
  let hh ← getAppFn coreWalkFuel wta
  if hh.tag == ETag.const then
    match ← view hh with
    | .const T us' =>
      match fe.find? T with
      | some (.indInfo cvT caps) => do
        let targs ← getAppArgs coreWalkFuel wta
        let reserved ← reservedBasisNames
        match ← viewLsLen us' with
        | none => failDanglingLs
        | some uslen =>
        if caps.unitlike = true ∧ reserved.contains T = false ∧
            targs.length = caps.unitParams ∧
            uslen = cvT.levelParams.length then do
          let tb ← r.inferIO depth b
          let wtb ← r.whnf depth tb
          if ← r.defeq depth wta wtb then do
            -- the type-former telescope certificate is a certificate FAMILY
            -- (official's `is_def_eq_unit_like` stops at the defeq above), so
            -- `mode.certs` gates it: `Cached/CoreC.lean:508`
            if mode.certs then
              iotaCerts r fe depth false (← constTyAt cvT us') targs
            else pure true
          else pure false
        else pure false
      | _ => pure false
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:505-530 etaCert — eta
certification for a one-sided λ against a stuck term `b`. -/
def etaCert (mode : CheckMode) (r : CoreFnsA) (_fe : IFEnv) (depth : Nat)
    (ty₁ body₁ : EIdx) (m₁ : BinderMeta) (b : EIdx) : AM Bool := do
  let tb ← r.inferIO depth b
  let hh ← r.whnf depth tb
  if hh.tag == ETag.forallE then
    match ← view hh with
    | .forallE ty₂ _ m₂ => do
      if ← r.defeq depth ty₂ ty₁ then do
        let fv ← internE (.fvar depth ty₁)
        let lhs ← instantiate1Fast coreWalkFuel body₁ fv 0
        let rhs ← internE (.app b fv)
        if !(← r.defeq (depth + 1) lhs rhs) then pure false else do
          if mode.verifiedChecks && !(m₁.pw == m₂.pw) then
            fail (.notImplemented "sort-annotation mismatch (eta)")
          else pure true
      else pure false
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — the fallback
for structurally distinct stuck terms: structural eta in either direction,
unit-likeness, else proof irrelevance. -/
def stuckIrrel (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (a b : EIdx) : AM Bool := do
  if ← structEtaCert mode r fe depth a b then pure true
  else if ← structEtaCert mode r fe depth b a then pure true
  else if ← structUnitCert mode r fe depth a b then pure true
  else proofIrrel r fe depth a b

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:751-759 etaFabArgs — the
eta-rescue fabrication's argument spine: the reduced type's arguments
followed by the installed projection functions applied to the stuck
major. -/
def etaFabArgs (T : NIdx) (ust : LsIdx) (targs : List EIdx) (major : EIdx)
    (nF : Nat) : AM (List EIdx) := do
  let ps ← projAppsGo T ust targs major nF 0
  pure (targs ++ ps)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:761-766 etaFabArgsE —
`etaFabArgs` at the entry kind: the projections are `etaProjs`'. -/
def etaFabArgsE (fe : IFEnv) (T : NIdx) (ust : LsIdx) (targs : List EIdx)
    (major : EIdx) (nF : Nat) : AM (List EIdx) := do
  let ps ← etaProjs fe T ust targs major nF
  pure (targs ++ ps)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:768-794 ProjEntry.fireOk — **the
tower-fire guard**: at a `Prop`-declared structure the field's guard level
must be a proposition at this instantiation; at every other family the rule
fires unconditionally. -/
def IProjEntry.fireOk (entry : IProjEntry) (us : LsIdx) : AM Bool := do
  let z ← zeroLevel
  if !((← lvlEq? entry.structSort z) == some true) then pure true
  else do
    let ks ← readNamesM entry.levelParams
    let vs ← readLevelsM us
    let fs ← readLevelM entry.fieldSort
    pure (Level.isEquiv (Level.subst ks vs fs) .zero == some true)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:796-809 andRescueSlotsOf — the
two-slot walk, as a counted recursion (con-leche's `(List.range 2).all`). -/
def andRescueSlotsGo (fe : IFEnv) (an ctor : NIdx) (nP : Nat) (ust : LsIdx) :
    Nat → Nat → AM Bool
  | 0, _ => pure true
  | n + 1, j => do
    match ← fe.findProj? an j with
    | some e => do
      if e.ctor == ctor && e.numParams == nP && e.numFields == 2 &&
          (← e.fireOk ust) then
        andRescueSlotsGo fe an ctor nP ust n (j + 1)
      else pure false
    | none => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:796-809 andRescueSlotsOf
con-leche: ConLeche/Kernel/CoreDefs.lean:811-813 andRescueSlots
con-leche: ConLeche/Kernel/FEnv.lean:101-103 FEnv.andRescueSlotsF
**The pinned `And`'s projection slots, ready to fire.**  One twin for
con-leche's three spellings (deviation 1). -/
def andRescueSlots (fe : IFEnv) (ctor : NIdx) (nP : Nat) (ust : LsIdx) :
    AM Bool := do
  let an ← pinAnd
  andRescueSlotsGo fe an ctor nP ust 2 0


/-! ## The stuck-major rescue and the ι step

con-leche's `Core.lean`:1311-1832. -/

/-- con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor — the
fabrication's fvar-leaf containment, `fab.fvarLeaves.all (fun l =>
major.fvarLeaves.contains l)`, as a named recursion (DESIGN §3.4). -/
def fvarLeavesSubset : List (Nat × EIdx) → List (Nat × EIdx) → Bool
  | [], _ => true
  | l :: ls, ms => ms.contains l && fvarLeavesSubset ls ms

/-- con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
con-leche: ConLeche/Cached/CoreC.lean:544-569 majorToCtorI — the scope guard
the three rescue branches share (cf. `annotateProjElim`): the fabricated major
is well-scoped, closed under loose bvars, and mentions no free variable the
stuck major does not.

**The three tests are the EXECUTED tier's** (task #97g).  `Kernel/Core.lean`
spells the last one `fab.fvarLeaves.all (fun l => major.fvarLeaves.contains
l)`, and task #97d twinned that literally: two unmemoized DAG walks and a
quadratic list containment, which on `core.ndjson` was 43.9 % of the whole
run's cycles.  `Cached/CoreC.lean` runs `wscopedBC`, `looseBVarsBounded` off
the packed field and `leafGuard` instead — the same predicate, one memoized
walk each — and those are what (B) runs now.  `fvarLeavesSubset` below stays
as the specification of what `leafGuard` decides. -/
def fabScopeOk (depth : Nat) (fab major : EIdx) : AM Bool := do
  if !(← wscopedBFast coreWalkFuel depth fab) then pure false
  else if !(← looseBVarsBoundedFast coreWalkFuel 0 fab) then pure false
  else leafGuard coreWalkFuel fab major

/-- con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor — **the
stuck-major rescue** (`to_cnstr_when_K` and `to_cnstr_when_structure`): a
recursor's major premise that does not whnf to a constructor application may
still be *replaced* by one — K-flagged, η-capable, or the pinned `And`.  An
uncertified major stays put. -/
def majorToCtor (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (_recName : NIdx) (rules : List IRecRule) (major : EIdx) : AM EIdx := do
  -- cheap syntactic gates before any inference
  if ← isCtorApp fe major then pure major else
  match rules with
  | [rl] =>
    match fe.find? rl.ctor with
    | some (.ctorInfo cvj cnP _cnF) => do
      let hh ← getAppFn coreWalkFuel (← piResult coreWalkFuel cvj.type)
      if hh.tag == ETag.const then
        match ← view hh with
        | .const T _ =>
          match fe.find? T with
          | some (.indInfo cvT caps) => do
            if rl.k = true then do
              -- io grade (lean4lean `toCtorWhenK`'s `inferType`)
              let tmaj ← r.whnf depth (← r.inferIO depth major)
              let hh ← getAppFn coreWalkFuel tmaj
              if hh.tag == ETag.const then
                match ← view hh with
                | .const T' ust => do
                  let ustl ← viewLs ust
                  if T' = T ∧ cvj.levelParams.length = ustl.length then do
                    let targs ← getAppArgs coreWalkFuel tmaj
                    if cnP ≤ targs.length then do
                      let hd ← internE (.const rl.ctor ust)
                      let fab ← mkAppN hd (targs.take cnP)
                      if ← fabScopeOk depth fab major then do
                        -- synthetic-spine certification (con-leche's task #71):
                        -- a certificate FAMILY, gated on `mode.certs`
                        -- (`Cached/CoreC.lean:576`)
                        let famK ←
                          if mode.certs then
                            iotaCerts r fe depth false (← constTyAt cvj ust)
                              (targs.take cnP)
                          else pure true
                        if famK then do
                          -- the official `to_cnstr_when_K` type check, both modes
                          if ← r.defeq depth tmaj (← r.inferIO depth fab) then do
                            -- `proofIrrel` is the soundness certificate here
                            -- (official stops at the type check): a family, gated
                            -- (`Cached/CoreC.lean:588`)
                            let irK ←
                              if mode.certs then proofIrrel r fe depth fab major
                              else pure true
                            if irK then pure fab else pure major
                          else pure major
                        else pure major
                      else pure major
                    else pure major
                  else pure major
                | _ => pure major
              else pure major
            else if rl.eta = true then do
              let tmaj ← r.whnf depth (← r.inferIO depth major)
              let hh ← getAppFn coreWalkFuel tmaj
              if hh.tag == ETag.const then
                match ← view hh with
                | .const T' ust => do
                  let ustl ← viewLs ust
                  let targs ← getAppArgs coreWalkFuel tmaj
                  -- the *instantiated* non-Prop test (con-leche's task #61)
                  let nz ← capsNeverZero cvT.levelParams ust caps
                  if T' = T ∧ targs.length = caps.etaParams ∧
                      ustl.length = cvT.levelParams.length ∧ nz = true then do
                    let fabArgs ← etaFabArgsE fe T ust targs major caps.etaFields
                    let hd ← internE (.const caps.etaCtor ust)
                    let fab ← mkAppN hd fabArgs
                    if ← fabScopeOk depth fab major then do
                      -- the synthetic-spine certificate, a family
                      -- (`Cached/CoreC.lean:621`)
                      let famE ←
                        if mode.certs then
                          iotaCerts r fe depth false (← constTyAt cvj ust) fabArgs
                        else pure true
                      if famE then do
                        if ← structEtaCertWith mode r fe depth fab major tmaj then
                          pure fab
                        -- 0-field rescue for the pinned basis `PUnit`
                        else if caps.etaFields = 0 then do
                          if ← proofIrrel r fe depth fab major then pure fab
                          else pure major
                        else pure major
                      else pure major
                    else pure major
                  else pure major
                | _ => pure major
              else pure major
            else do
              let an ← pinAnd
              if T = an then do
                -- THE `And`-ONLY η RESCUE (user ruling: `And` and nothing else)
                let tmaj ← r.whnf depth (← r.inferIO depth major)
                let hh ← getAppFn coreWalkFuel tmaj
                if hh.tag == ETag.const then
                  match ← view hh with
                  | .const T' ust => do
                    match ← viewLsLen ust with
                    | none => failDanglingLs
                    | some ustl =>
                    let targs ← getAppArgs coreWalkFuel tmaj
                    let ars ← andRescueSlots fe rl.ctor cnP ust
                    if T' = T ∧ targs.length = cnP ∧
                        cvj.levelParams.length = ustl ∧ ars = true then do
                      let p0 ← internE (.proj T 0 major)
                      let p1 ← internE (.proj T 1 major)
                      let fabArgs := targs ++ [p0, p1]
                      let hd ← internE (.const rl.ctor ust)
                      let fab ← mkAppN hd fabArgs
                      if ← fabScopeOk depth fab major then do
                        -- the synthetic-spine certificate and the irrelevance
                        -- one, both families (`Cached/CoreC.lean:654`, `:658`)
                        let famA ←
                          if mode.certs then
                            iotaCerts r fe depth false (← constTyAt cvj ust) fabArgs
                          else pure true
                        if famA then do
                          if ← r.defeq depth tmaj (← r.inferIO depth fab) then do
                            let irA ←
                              if mode.certs then proofIrrel r fe depth fab major
                              else pure true
                            if irA then pure fab else pure major
                          else pure major
                        else pure major
                      else pure major
                    else pure major
                  | _ => pure major
                else pure major
              else pure major
          | _ => pure major
        | _ => pure major
      else pure major
    | _ => pure major
  | _ => pure major

/-- con-leche: ConLeche/Kernel/Core.lean:728-740 litMajorToCtor — convert a
literal major premise to constructor form: a `Nat` literal one layer, a
`String` literal to its *reduced* constructor form. -/
def litMajorToCtor (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (h : EIdx) :
    AM EIdx := do
  if h.tag == ETag.lit then
    match ← view h with
    | .lit (.strVal s) => do
      if ← strLitSupported fe then do
        let c ← strLitToConstructor s
        r.whnf depth c
      else pure h
    | _ => litToCtorIfNat fe h
  else litToCtorIfNat fe h

/-- con-leche: ConLeche/Kernel/Core.lean:742-756 projLitToCtor — convert a
string-literal projection scrutinee to its *reduced* constructor form. -/
def projLitToCtor (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (h : EIdx) :
    AM EIdx := do
  if h.tag == ETag.lit then
    match ← view h with
    | .lit (.strVal s) => do
      if ← strLitSupported fe then do
        let c ← strLitToConstructor s
        r.whnf depth c
      else pure h
    | _ => pure h
  else pure h

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:815-830 recRuleKOf — **the K bit
at install** (`RecRule.k`): the rule's constructor has no fields and belongs
to an inductive stored with the K capability. -/
def recRuleKOf (fe : IFEnv) (ctor : NIdx) : AM Bool := do
  match fe.find? ctor with
  | some (.ctorInfo cvj _ cnF) => do
    let hh ← getAppFn coreWalkFuel (← piResult coreWalkFuel cvj.type)
    if hh.tag == ETag.const then
      match ← view hh with
      | .const T _ =>
        match fe.find? T with
        | some (.indInfo _ caps) => pure (caps.ruleK && cnF == 0)
        | _ => pure false
      | _ => pure false
    else pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:832-858 recRuleEtaOf — **the
η-rescue bit at install** (`RecRule.eta`).  `Name.isProjFnShape` is a
predicate on a `ConLeche.Name`, so the recursor's name is read back for it —
an install-time path, never a reduction-time one. -/
def recRuleEtaOf (fe : IFEnv) (recName ctor : NIdx) : AM Bool := do
  match fe.find? ctor with
  | some (.ctorInfo cvj _ _) => do
    let hh ← getAppFn coreWalkFuel (← piResult coreWalkFuel cvj.type)
    if hh.tag == ETag.const then
      match ← view hh with
      | .const T _ =>
        match fe.find? T with
        | some (.indInfo cvT caps) => do
          let rn ← readNameM recName
          pure (caps.eta && caps.etaCtor == ctor && !Name.isProjFnShape rn &&
            cvj.levelParams == cvT.levelParams)
        | _ => pure false
      | _ => pure false
    else pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:860-870 recRuleBits — **stamp a
rule's two rescue bits at install** — the one place the K and η-rescue
conditions are decided. -/
def recRuleBits (fe : IFEnv) (recName : NIdx) (rl : IRecRule) : AM IRecRule := do
  let k ← recRuleKOf fe rl.ctor
  let eta ← recRuleEtaOf fe recName rl.ctor
  pure { rl with k := k, eta := eta }

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:909-921 projFnRule — **the stored
rule of an installed projection function**: the degenerate recursor's single
rule, with the two rescue bits stamped by `recRuleBits`. -/
def projFnRule (fe : IFEnv) (T ctorName : NIdx) (pty : EIdx) (nP nF i : Nat)
    (rhsA : EIdx) : AM IRecRule := do
  let plain ← recRulePlain coreWalkFuel pty nP nP nP
  let nm ← projFnName T i
  recRuleBits fe nm
    { ctor := ctorName, nfields := nF, ctorParams := nP,
      fire := if plain then .plain else .inert,
      rhs := rhsA, paramsBlind := false }

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:939-946 recRuleK — is a recursor
K-flagged?  The stored bit of its single rule; pure, as con-leche's is. -/
def recRuleK (rules : List IRecRule) : Bool :=
  match rules with
  | [rl] => rl.k
  | _ => false

/-- con-leche: ConLeche/Kernel/Core.lean:758-795 prepareMajor — the major
premise's preparation before a rule fires, in the official kernel's order:
at a K-flagged recursor the K rescue runs on the **raw** major, elsewhere the
major is head-normalized first. -/
def prepareMajor (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (recName : NIdx) (rules : List IRecRule) (major : EIdx) : AM EIdx := do
  if recRuleK rules then do
    let majorK ← majorToCtor mode r fe depth recName rules major
    let major₀ ← r.whnf depth majorK
    litMajorToCtor r fe depth major₀
  else do
    let major₀ ← r.whnf depth major
    let major₁ ← litMajorToCtor r fe depth major₀
    majorToCtor mode r fe depth recName rules major₁

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:948-968 recFireComparands — the
nested rule's stored level comparands, substituted and re-interned
(`lvls.map (Level.subst lps us)` as a named recursion). -/
def substLevelsAt (ks : List ConLeche.Name) (vs : List Level) :
    List LIdx → AM (List LIdx)
  | [] => pure []
  | u :: us => do
    let l ← readLevelM u
    let h ← internLevel (Level.subst ks vs l)
    let rest ← substLevelsAt ks vs us
    pure (h :: rest)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:948-968 recFireComparands — the
canonical rule's level comparands, `cvjLps.map fun p => Level.subst lps us
(.param p)`, as a named recursion. -/
def substParamLevels (ks : List ConLeche.Name) (vs : List Level) :
    List NIdx → AM (List LIdx)
  | [] => pure []
  | p :: ps => do
    let pn ← readNameM p
    let h ← internLevel (Level.subst ks vs (.param pn))
    let rest ← substParamLevels ks vs ps
    pure (h :: rest)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:948-968 recFireComparands — the
nested rule's stored parameter pins, level-instantiated and instantiated at
the recursor's leading-argument spine, as a named recursion. -/
def instSpinePins (lps : List NIdx) (us : LsIdx) (args : List EIdx) (rP : Nat) :
    List EIdx → AM (List EIdx)
  | [] => pure []
  | p :: ps => do
    let q ← instLPFast coreWalkFuel lps us p
    let s ← instSpine coreWalkFuel (args.take rP) (rP - 1) q
    let rest ← instSpinePins lps us args rP ps
    pure (s :: rest)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:948-968 recFireComparands — the
level and constructor-parameter comparands a firing rule's checks compare the
major's constructor levels and parameters against. -/
def recFireComparands (rl : IRecRule) (lps : List NIdx) (us : LsIdx)
    (cvjLps : List NIdx) (args : List EIdx) (rP : Nat) :
    AM (LsIdx × List EIdx) := do
  match rl.fire with
  | .nested lvls pins => do
    let ks ← readNamesM lps
    let vs ← readLevelsM us
    let ls ← substLevelsAt ks vs lvls
    let lsh ← internLsNode ls
    let ps ← instSpinePins lps us args rP pins
    pure (lsh, ps)
  | _ => do
    let ks ← readNamesM lps
    let vs ← readLevelsM us
    let ls ← substParamLevels ks vs cvjLps
    let lsh ← internLsNode ls
    pure (lsh, args.take rl.ctorParams)

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — the rule lookup
`rules.find? (fun r' => r'.ctor == cj)`, as a named recursion (DESIGN
§3.4). -/
def findRule : List IRecRule → NIdx → Option IRecRule
  | [], _ => none
  | rl :: rs, c => if rl.ctor == c then some rl else findRule rs c

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — **one iota step at
a spine the caller already holds** (task #97-P6-9's hoist).  `iotaRec`'s own
first two steps are `getAppFn` and `getAppArgs`, and the batched β asks for an
iota step at every reduction step of a spine it is already walking: this entry
takes the head and the argument vector instead of re-walking them, which is
`getAppFn (mkAppN h as) = h` and `getAppArgsC (mkAppN h as) = as` — the
equation the bridge owes and the only thing OWED here that is not con-leche's
own clause.

The arity conjunct is moved in FRONT of the level-list read and of the
recursor's value copies (task #97-P6-10): both sides of `n = mI + 1` are pure
tests of the same conjunction and this one is `O(1)`.  con-leche's own
`iotaArityOk` is the same guard inside its `whnfAppI`. -/
def iotaRecAt (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (hd : EIdx) (sargs : Array EIdx) (n : Nat) : AM (Option EIdx) := do
  if hd.tag == ETag.const then
    match ← viewConst hd with
    | none => failDanglingE
    | some (c, us) =>
      match fe.find? c with
      | some (.recInfo cv mI rP rules) => do
        if n ≠ mI + 1 then pure none
        else do
        let args := (takeEidx sargs n).toList
        match ← viewLsLen us with
        | none => failDanglingLs
        | some usl =>
        -- checker change #9: the recursor's level arity, guarded as
        -- `unfoldDefinition` guards it
        if args.length = mI + 1 ∧ usl = cv.levelParams.length then do
          let b0 ← internE (.bvar 0)
          let major ← prepareMajor mode r fe depth c rules (args.getD mI b0)
          let hh ← getAppFn coreWalkFuel major
          if hh.tag == ETag.const then
            match ← view hh with
            | .const cj usj =>
              match fe.find? cj with
              | some (.ctorInfo cvj _ _) =>
                match findRule rules cj with
                | some rl => do
                  let margs ← getAppArgs coreWalkFuel major
                  if margs.length = rl.ctorParams + rl.nfields then do
                    -- a matched *inert* rule is a positive detection of an
                    -- unsupported feature
                    if rl.fire = .inert then
                      fail (.notImplemented
                        "iota reduction over a nested auxiliary recursor rule")
                    else do
                      let cmp ← recFireComparands rl cv.levelParams us
                        cvj.levelParams args rP
                      if ← liftFueled "level comparison" (← lvlsEq? usj cmp.1) then do
                        -- the parameter comparison is verdict-relevant for a
                        -- nested rule (the comparands ARE the pins) and for a
                        -- projection-function rule, and a certificate family for
                        -- every other plain rule: `Cached/CoreC.lean:797`'s
                        -- `certUnlessI` with exactly that `keep`
                        let pOk ←
                          if rl.compareParams then do
                            let keep ←
                              match rl.fire with
                              | .nested _ _ => pure true
                              | _ => do pure (Name.isProjFnShape (← readNameM c))
                            if mode.certs || keep then
                              defEqList r fe depth (margs.take rl.ctorParams) cmp.2
                            else pure true
                          else pure true
                        if pOk then do
                          -- ONE certificate family: the two *licensed* telescope
                          -- runs and the canonical-index comparison.  Nothing
                          -- here is read outside the family, so the whole block
                          -- is what `.trusted` omits, the two type lookups
                          -- included (`Cached/CoreC.lean:814`)
                          let fam ←
                            if mode.certs then do
                              let tyR ← constTyAt cv us
                              if ← iotaCerts r fe depth mode.betaGate tyR
                                  (args.take mI ++ [major]) then do
                                let tyC ← constTyAt cvj usj
                                if ← iotaCerts r fe depth mode.betaGate tyC margs then
                                  iotaIndexOk r fe depth mI rP rl.ctorParams tyC
                                    margs ((args.take mI).drop rP)
                                else pure false
                              else pure false
                            else pure true
                          if fam then do
                            let rhs ← ruleRhsAt c rl.ctor cv.levelParams rl.rhs us
                            let x ← mkAppN rhs
                              (args.take rP ++ margs.drop rl.ctorParams)
                            pure (some x)
                          else pure none
                        else pure none
                      else pure none
                  else pure none
                | none => pure none
              | _ => pure none
            | _ => pure none
          else pure none
        else pure none
      | _ => pure none
  else pure none

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — **one iota
step**: the expression is a stored recursor applied to exactly its telescope,
the major premise whnfs to a fully applied constructor with a matching rule,
and the spine is certified against the recursor's own (pinned, annotated)
type.  The walk-it-yourself entry of `iotaRecAt`. -/
def iotaRec (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (e : EIdx) : AM (Option EIdx) := do
  let hd ← getAppFn coreWalkFuel e
  let args ← getAppArgs coreWalkFuel e
  iotaRecAt mode r fe depth hd args.toArray args.length

/-! ## The application spine, the batched β, and the two stuck tags

DESIGN §8.6 item 9 (`whnfAppI` / `betaPeelI`) and item 7 (the stuck tags). -/

/-- con-leche: none — `internE` with task #97-P6-5's upward cutoff at the
`.app` node the reduction rebuilds: applying one more argument to a spine
whose head did not move is the node the spine already has. -/
@[inline] def internAppRebuilt (h : EIdx) (same : Bool) (f a : EIdx) : AM EIdx :=
  if same then pure h else internE (.app f a)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:915-918 getAppFn
con-leche: ConLeche/Kernel/ExprOps.lean:920-923 getAppArgs
The head, the argument vector AND the spine's own `.app` NODES, in ONE walk —
the third result is the arena's own and is what carries `internAppRebuilt`'s
`same` (the node the reduction may hand back unchanged). -/
def getAppSpineGo : Nat → EIdx → AM (EIdx × Array EIdx × Array EIdx)
  | 0, _ => fail (.internal "fuel exhausted: getAppSpine")
  | fuel + 1, h => do
    if h.tag == ETag.app then
      match ← viewApp h with
      | none => failDanglingE
      | some (f, a) => do
        let t ← getAppSpineGo fuel f
        pure (t.1, t.2.1.push a, t.2.2.push h)
    else pure (h, #[], #[])

/-- con-leche: ConLeche/Kernel/ExprOps.lean:915-923 getAppFn — the spine walk's
entry. -/
def getAppSpine (fuel : Nat) (h : EIdx) : AM (EIdx × Array EIdx × Array EIdx) :=
  getAppSpineGo fuel h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:915-923 getAppFn — the head and the
argument vector of a reduct, which is what `whnfApp` re-enters on.  A
non-application is its own head with no arguments. -/
def headAndArgs (v : EIdx) : AM (EIdx × Array EIdx) := do
  if v.tag == ETag.app then do
    let hd ← getAppFn coreWalkFuel v
    let va ← getAppArgs coreWalkFuel v
    pure (hd, va.toArray)
  else pure (v, #[])

/-- con-leche: ConLeche/Kernel/Core.lean:963-1052 whnfCoreBody — **the head
kinds `whnfCoreBody` returns unchanged, off the handle's TAG** (task
#97-P6-7's lever 2): `sort`, `fvar`, `forallE`, `lam`, `const` and `lit` are
the body's own first six clauses, and a handle carries the tag of its own view
on a well-formed store, so the memo probe and the node read are both skipped.
The obligation is `whnfCoreBody e = pure e` for the six tags. -/
@[inline] def whnfCoreStuckTag (e : EIdx) : Bool :=
  let t := e.tag
  if t == ETag.app then false
  else if t == ETag.proj then false
  else if t == ETag.letE then false
  else if t == ETag.bvar then false
  else true

/-- con-leche: ConLeche/Kernel/Core.lean:1097-1099 whnfBody — **the head kinds
`whnfBody` returns unchanged**, the same lever one rung up: `sort`, `fvar`,
`lam`, `forallE` and `lit`.  The obligation adds `reduceNat e = none` (its
`match` is on `.app`) and `unfoldDefinition e = none` (`getAppFn` of a
non-`app` is the node itself and the `match` is on `.const`). -/
@[inline] def whnfStuckTag (e : EIdx) : Bool :=
  let t := e.tag
  if t == ETag.sort then true
  else if t == ETag.fvar then true
  else if t == ETag.lam then true
  else if t == ETag.forallE then true
  else if t == ETag.lit then true
  else false

/-- con-leche: ConLeche/Kernel/Core.lean:963-1052 whnfCoreBody — the STUCK
application step: rebuild the node (or hand back the one the spine already
has, task #97-P6-7's lever 4) and try one iota step on it.  The gated lane's
`.app` clause is its only caller since the batched β landed. -/
def whnfCoreStuckApp (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (h : EIdx) (same : Bool) (fp a : EIdx) : AM EIdx := do
  let ap ← internAppRebuilt h same fp a
  match ← iotaRec mode r fe depth ap with
  | some e2 => r.whnfCore depth e2
  | none => pure ap

/-! ### The batched β spine

con-leche's own CACHED-tier clauses (`Cached/CoreC.lean:857-900 whnfAppI` and
`:902-938 betaPeelI`), whose identification with the chained spec bodies
con-leche proves in `Verify/BetaSpine.lean` (`whnfApp_sound:900`,
`betaPeel_snoc:722`) over `Expr.instantiateList_cons`.  The spec-shaped clause
they replace re-entered the knot once per argument; these peel a consecutive
run of λ binders into ONE `instantiateList` walk.

The accumulator is an `Array` in PUSH order (task #97-P6-15's clause change),
which `instantiateList` reads from the end — the same list con-leche's `::`
chain builds, the other way round. -/

mutual

/-- con-leche: ConLeche/Cached/CoreC.lean:857-900 whnfAppI — walk the spine's
arguments, applying each to the head's reduct: a λ head opens a peel group, a
stuck head applies the argument and tries one iota step at the spine the walk
already holds. -/
def whnfApp (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (v hd : EIdx) (vargs : Array EIdx) (same : Bool)
    (args nodes : Array EIdx) (i : Nat) : AM EIdx := do
  if hi : i < args.size then do
    let a := args[i]
    let node := nodes[i]!
    if v.tag == ETag.lam then
      match ← viewBind v with
      | none => failDanglingE
      | some (ty, body, mb) => do
        -- **THE β SITE'S GATE**: the EXECUTED core reads `CheckMode.betaSkip`
        -- (`Cached/CoreC.lean:876`/`:918`).
        if mode.betaSkip mb.pw then
          betaPeel mode r fe depth body #[a] args nodes (i + 1)
        else do
          -- con-leche's task #172 B4: the certificate's inference runs at the
          -- io grade.
          let ta ← r.inferIO depth a
          if ← r.defeq depth ta ty then
            betaPeel mode r fe depth body #[a] args nodes (i + 1)
          else do
            -- The certificate failed: the redex is stuck.  ι cannot fire under
            -- a λ head, so the rest is re-applied without another ι attempt.
            let fa ← internAppRebuilt node same v a
            mkAppNFrom fa args (i + 1)
    else do
      let ap ← internAppRebuilt node same v a
      let same2 := ap == node
      let va := vargs.push a
      let step ←
        if hd.tag == ETag.const then iotaRecAt mode r fe depth hd va va.size
        -- `iotaRec`'s own first two steps are `getAppFn` and a `.const` match,
        -- so a spine whose head is anything else answers `none` from every
        -- prefix: con-leche's `iotaArityOk` guard, off the handle's tag.
        else pure none
      match step with
      | none => whnfApp mode r fe depth ap hd va same2 args nodes (i + 1)
      | some e2 => do
        let v2 ← r.whnfCore depth e2
        let hv ← headAndArgs v2
        whnfApp mode r fe depth v2 hv.1 hv.2 false args nodes (i + 1)
  else pure v
termination_by (args.size - i, 0)

/-- con-leche: ConLeche/Cached/CoreC.lean:902-938 betaPeelI — peel a
consecutive run of λ binders, collecting their arguments, and substitute the
whole run in ONE `instantiateList`. -/
def betaPeel (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (t : EIdx) (acc : Array EIdx) (args nodes : Array EIdx) (i : Nat) :
    AM EIdx := do
  if hi : i < args.size then do
    let a := args[i]
    if t.tag == ETag.lam then
      match ← viewBind t with
      | none => failDanglingE
      | some (ty, body, mb) => do
        if mode.betaSkip mb.pw then
          betaPeel mode r fe depth body (acc.push a) args nodes (i + 1)
        else do
          let ty2 ← instantiateListFast coreWalkFuel ty acc 0
          let ta ← r.inferIO depth a
          if ← r.defeq depth ta ty2 then
            betaPeel mode r fe depth body (acc.push a) args nodes (i + 1)
          else do
            let f2 ← instantiateListFast coreWalkFuel t acc 0
            let fa ← internE (.app f2 a)
            mkAppNFrom fa args (i + 1)
    else do
      let e2 ← instantiateListFast coreWalkFuel t acc 0
      let v2 ← r.whnfCore depth e2
      -- The peeled group is over and the spine is not: re-enter `whnfApp` at
      -- the SAME argument.  A β has happened, so the accumulated head is no
      -- longer the original prefix and the upward cutoff is OFF.
      let hv ← headAndArgs v2
      whnfApp mode r fe depth v2 hv.1 hv.2 false args nodes i
  else do
    let e2 ← instantiateListFast coreWalkFuel t acc 0
    r.whnfCore depth e2
termination_by (args.size - i, 1)

end

/-! ## The projection certificate and the reduction bodies

con-leche's `Core.lean`:1834-2074. -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:970-979 ProjEntry.typeAt — **the
type of a `.proj` node at a tower-backed entry**: the stored body,
level-instantiated at the subject type's levels, with the subject type's
arguments and the subject substituted for its `numParams + 1` loose
variables in ONE traversal. -/
def IProjEntry.typeAt (entry : IProjEntry) (us : LsIdx) (targs : List EIdx)
    (pe : EIdx) : AM EIdx := do
  let b ← instLPFast coreWalkFuel entry.levelParams us entry.body
  -- push order (task #97-P6-15): `pe :: targs.reverse` as a list is
  -- `targs ++ [pe]` as a push-order array, which is what the accumulator
  -- ruling makes every substituting site look like.
  instantiateListFast coreWalkFuel b (targs.toArray.push pe) 0

/-- con-leche: ConLeche/Kernel/Core.lean:912-947 projCert — **the
structural projection's certificate**: the redex `proj_i (C p⃗ x⃗)` fires only
after its constructor spine is certified against `C`'s stored type at the
redex's own levels. -/
def projCert (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (lic : Bool)
    (c : NIdx) (us : LsIdx) (args : List EIdx) : AM Bool := do
  match fe.find? c with
  | some (.ctorInfo cvC _ _) => do
    let ty ← constTyAt cvC us
    iotaCerts r fe depth lic ty args
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:949-961 projCertAt — **the fire
certificate as the mode runs it**: the P core certifies the constructor
spine; the parity core is the official kernel's, which certifies nothing. -/
def projCertAt (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (verified lic : Bool)
    (c : NIdx) (us : LsIdx) (args : List EIdx) : AM Bool :=
  if verified then projCert r fe depth lic c us args else pure true

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:981-1013 betaGateFires — **THE β
SITE'S GATE**, the SPEC's form: at `mode.betaGate` a λ-binder whose
*validated* annotation datum is `.never` licenses skipping the certificate.
Mode-and-datum only, so it is decidable before the certificate would have
started.

It has **no reader here**, for the reason `whnfCoreLoopFuel` has none: the β
site of the twin runs `CheckMode.betaSkip`, which is what
`Cached/CoreC.lean:876` and `:918` — the EXECUTED core, the one this module
twins — read, and which is `betaGateFires` weakened by
`!mode.certs` (the β certificate is a certificate FAMILY, skipped wholesale at
`.trusted`).  The two agree at `.verified`, the mode the bridge is stated at;
task #97f's `--trusted` sweep is what made the difference matter.  Twinned so
P3 has the spec's subject by name. -/
@[inline] def betaGateFires (mode : CheckMode) (pw : PropWhen) : Bool :=
  mode.betaGate && pw.isNever

/-- con-leche: ConLeche/Kernel/Core.lean:963-1052 whnfCoreBody — the
head-normalization body: beta (with the per-redex argument certificate),
iota (with the stuck-major machinery) and the projection rule — but **no
delta**.  Values return themselves, which over handles is the handle itself:
hash-consing makes `.sort u` interned from a `.sort u` view the same
node. -/
def whnfCoreBody (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) :
    Nat → EIdx → AM EIdx :=
  fun depth e => do
    match ← view e with
    | .sort _ | .fvar _ _ | .forallE _ _ _ | .lam _ _ _ | .const _ _
    | .lit _ => pure e
    -- **The batched β spine** (task #97-P6-9), con-leche's
    -- `Cached/CoreC.lean:942-996 whnfCoreStepI`'s own `.app` clause: the
    -- spine's head is normalized once and the whole argument vector is run
    -- through `whnfApp`, which batches a consecutive run of λ binders into
    -- ONE `instantiateList` walk.  The spec-shaped clause this replaces
    -- re-entered the knot per argument.
    | .app _ _ => do
      let sp ← getAppSpine coreWalkFuel e
      let v ← r.whnfCore depth sp.1
      let same := v == sp.1
      let hv ← headAndArgs v
      whnfApp mode r fe depth v hv.1 hv.2 same sp.2.1 sp.2.2 0
    | .proj sn i pe => do
      let e0 ← r.whnf depth pe
      -- a string-literal scrutinee first expands to its reduced
      -- constructor form
      let e' ← projLitToCtor r fe depth e0
      match ← fe.findProj? sn i with
      | some entry => do
        let hh ← getAppFn coreWalkFuel e'
        if hh.tag == ETag.const then
          match ← view hh with
          | .const c us => do
            let args ← getAppArgs coreWalkFuel e'
            match ← viewLsLen us with
            | none => failDanglingLs
            | some usl =>
            let fok ← entry.fireOk us
            if c = entry.ctor ∧ i < entry.numFields ∧
                args.length = entry.numParams + entry.numFields ∧
                usl = entry.levelParams.length ∧ fok = true then do
              let b0 ← internE (.bvar 0)
              let arg := args.getD (entry.numParams + i) b0
              if ← projCertAt r fe depth mode.verifiedChecks mode.betaGate c us
                  args then
                r.whnfCore depth arg
              else internE (.proj sn i e')
            else internE (.proj sn i e')
          | _ => internE (.proj sn i e')
        else internE (.proj sn i e')
      | none => internE (.proj sn i e')
    | .letE _ _ _ =>
      -- **Unreachable by construction** (con-leche's task #241): annotate
      -- output is let-free
      fail (.internal "whnfCore: `let` in an annotated expression")
    | .bvar _ =>
      fail (.notImplemented "whnf beyond the supported fragment")

/-- con-leche: ConLeche/Kernel/Core.lean:1054-1062 whnfCoreLoopFuel — step
budget of the `whnfCore` head-normalization loop.  The arena's
`whnfCoreBody` is con-leche's SPEC shape — beta, iota and projection steps
chained through the knot, not iterated in a local loop — so this budget has
no reader here yet; it is twinned because the executed loop
(`Cached/CoreC.lean`'s `whnfCoreLoopI`) is what P2g will measure against,
and its budget must be the same number. -/
def whnfCoreLoopFuel : Nat := 1000000

/-- con-leche: ConLeche/Kernel/Core.lean:1064-1071 whnfLoopFuel — step budget
of the `whnf` reduction loop (lean4lean's `FuelConfig.whnf`, same value).
Literal-acceleration and delta steps are *iteration*, not recursion. -/
def whnfLoopFuel : Nat := 100000

/-- con-leche: ConLeche/Kernel/Core.lean:1073-1088 whnfStep — one iteration
of the reduction loop: head-normalize, try literal acceleration, unfold one
definition — and hand the reduct to the loop's continuation `k`. -/
def whnfStep (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (k : EIdx → AM EIdx)
    (e : EIdx) : AM EIdx := do
  let e₁ ← r.whnfCore depth e
  match ← reduceNat r fe depth e₁ with
  | some e₂ => k e₂
  | none =>
    match ← unfoldDefinition fe e₁ with
    | some e₂ => k e₂
    | none => pure e₁

/-- con-leche: ConLeche/Kernel/Core.lean:1090-1095 whnfLoop — the reduction
loop: iterate `whnfStep` on its own step budget, so the whole chain costs one
knot level however many steps it takes. -/
def whnfLoop (r : CoreFnsA) (fe : IFEnv) (depth : Nat) : Nat → EIdx → AM EIdx
  | 0, _ => fail (.internal "fuel exhausted: whnf loop")
  | n + 1, e => whnfStep r fe depth (whnfLoop r fe depth n) e

/-- con-leche: ConLeche/Kernel/Core.lean:1097-1099 whnfBody — the reduction
loop's body: run `whnfLoop` at its own step budget. -/
def whnfBody (r : CoreFnsA) (fe : IFEnv) : Nat → EIdx → AM EIdx :=
  fun depth e => whnfLoop r fe depth whnfLoopFuel e

/-- con-leche: ConLeche/Kernel/Core.lean:1101-1107 ensureSort — ensure `e`
(the type of some expression) is a sort, returning its level. -/
def ensureSort (r : CoreFnsA) (_fe : IFEnv) (depth : Nat) (e : EIdx) :
    AM LIdx := do
  let hh ← r.whnf depth e
  if hh.tag == ETag.sort then
    match ← view hh with
    | .sort u => pure u
    | _ => fail (.invalid "expected a sort")
  else fail (.invalid "expected a sort")

/-- con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody — the λ clause's
result, `.forallE ty (bt.abstract1 depth) mb`.  con-leche writes it once at
the end of a clause with three exits; the arena names it, so the three exits
share one spelling and no arm is duplicated (DESIGN §8.4's Rust shape). -/
def inferLamResult (ty bt : EIdx) (depth : Nat) (mb : BinderMeta) : AM EIdx := do
  let ab ← abstract1Fast coreWalkFuel bt depth 0
  internE (.forallE ty ab mb)

/-! ### The binder telescopes

DESIGN §8.6 items 11 and 12.  con-leche's cached tier keeps four
binder-telescope loops that its PURE tier writes as per-binder chains, and
`ConLeche/Verify/BinderLoop.lean` proves all four sound against the chained
bodies; `Verify/Cached/BinderLoopC.lean` relates the cached spelling to those
pure mirrors walk by walk.  A loop peels the whole chain, opens every domain
against the free variables it has introduced in ONE `instantiateList`, and
rebuilds outward with `abstractRange` — where the chain paid one
`instantiate1` per binder per domain and one `abstract1` per binder on the way
out.

The stack is an `Array` pushed outermost-first and consumed by a count
counting down, where con-leche conses a `List` innermost-first and consumes
its head: the same entries in the same order, and `stk[j]`'s index IS
con-leche's `j`.  `fvs` is a push-order `Array` read by `instantiateList` from
the end, which is the same convention the batched β already uses. -/

/-- con-leche: ConLeche/Cached/StateC.lean:168-172 peelFuel — the telescope
loops' own step budget.  con-leche's note says the peel fuel is semantically
transparent: on exhaustion the leaf phase hands the residual chain back to the
knot, which is the chained spec's next step. -/
def peelFuel : Nat := 16777216

/-- con-leche: ConLeche/Cached/CoreC.lean:1142-1160 inferLamsOutI — the λ
loop's OUTWARD rebuild: `abstractRange` closes each stored domain over the `j`
free variables below it and the ∀ node is rebuilt, innermost binder first.
The task-#161 chain check rides with it: a binder's datum must equal the datum
of the binder inside it. -/
def inferLamsOut (mode : CheckMode) (d : Nat) (stk : Array (EIdx × BinderMeta))
    (n : Nat) (cur : EIdx) (prevPw : PropWhen) : AM EIdx := do
  if n = 0 then pure cur
  else do
    let j := n - 1
    let e := stk[j]!
    if mode.verifiedChecks && !(e.2.pw == prevPw) then
      fail (.notImplemented "sort-annotation mismatch (lam-cod-chain)")
    else do
      let tyAbs ← abstractRangeFast coreWalkFuel e.1 d j 0
      let nd ← internForallEE tyAbs cur e.2
      inferLamsOut mode d stk j nd e.2.pw
termination_by n

/-- con-leche: ConLeche/Cached/CoreC.lean:1162-1206 inferLamsLeafI — the
statement the λ leaf runs when the body carries no datum of its own: the
codomain-sort computation of con-leche's task #152, named so that the leaf's
common tail is written once. -/
def inferLamsLeafCheck (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (d k : Nat)
    (stk : Array (EIdx × BinderMeta)) (bt : EIdx) : AM Unit := do
  if !mode.verifiedChecks then pure ()
  else do
    let btt ← r.inferIO (d + k) bt
    let vb ← ensureSort r fe (d + k) btt
    let n := stk.size
    if n = 0 then pure ()
    else do
      let lvb ← readLevelM vb
      if Level.zeronessOf lvb == stk[n - 1]!.2.pw then pure ()
      else fail (.notImplemented "sort-annotation mismatch (lam-cod-leaf)")

/-- con-leche: ConLeche/Cached/CoreC.lean:1162-1206 inferLamsLeafI — the λ
loop's LEAF: open the residual body against every free variable at once,
infer it, run the datum check the chain ran at the innermost binder, and hand
the outward rebuild its starting point. -/
def inferLamsLeaf (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (d : Nat)
    (t : EIdx) (k : Nat) (fvs : Array EIdx) (stk : Array (EIdx × BinderMeta)) :
    AM EIdx := do
  let ob ← instantiateListFast coreWalkFuel t fvs 0
  let bt ← r.infer (d + k) ob
  let lpw ← lamPw t
  match lpw with
  | some _ => pure ()
  | none => inferLamsLeafCheck mode r fe d k stk bt
  let n := stk.size
  let prevPw :=
    match lpw with
    | some pw => pw
    | none => if n = 0 then .never else stk[n - 1]!.2.pw
  let cur ← abstractRangeFast coreWalkFuel bt d k 0
  inferLamsOut mode d stk n cur prevPw

/-- con-leche: ConLeche/Cached/CoreC.lean:1208-1228 inferLamsI — the
λ-telescope inference loop: peel a consecutive run of λ binders, opening each
domain against the free variables introduced so far and checking that it is a
type, then hand the residual to the leaf. -/
def inferLams (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (d : Nat) :
    Nat → EIdx → Nat → Array EIdx → Array (EIdx × BinderMeta) → AM EIdx
  | 0, t, k, fvs, stk => inferLamsLeaf mode r fe d t k fvs stk
  | peel + 1, t, k, fvs, stk => do
    -- The peel's test is a tag read off the handle word and the binder
    -- PROJECTION (task #97-P6-10).
    if t.tag != ETag.lam then inferLamsLeaf mode r fe d t k fvs stk
    else
      match ← viewBind t with
      | none => failDanglingE
      | some (ty, body, mb) => do
        let tyo ← instantiateListFast coreWalkFuel ty fvs 0
        let tty ← r.infer (d + k) tyo
        let w ← r.whnf (d + k) tty
        -- The codomain sort's LEVEL is not used — the `.lam` case wants only
        -- that the type's whnf IS a sort, which the handle's own tag says —
        -- but the port's loop does read the node (`view_sort`, failing
        -- `internal` at a dangling sort-tagged handle), where its first
        -- binder (`inferLam`) does not.  The twin reads it too (task
        -- #97-P5-Core round 4's audit), so the two decline alike.
        if w.tag == ETag.sort then do
          match ← viewSort w with
          | none => failDanglingE
          | some _ => do
            let fv ← internFVarE (d + k) tyo
            inferLams mode r fe d peel body (k + 1) (fvs.push fv) (stk.push (tyo, mb))
        else fail (.invalid "expected a sort")

/-- con-leche: ConLeche/Cached/CoreC.lean:1230-1254 inferPisOutI — the ∀
loop's outward `imax` fold, with the **THREADED** zero-ness datum: the leaf
reads its sort's zero-ness ONCE, and `Level.zeronessOf (imax u v) =
Level.zeronessOf v` makes it invariant under the fold, so the chain's one
`readLevel` per binder becomes one per telescope (con-leche's task #272). -/
def inferPisOut (mode : CheckMode) (stk : Array (LIdx × PropWhen)) (n : Nat)
    (v : LIdx) (pv : PropWhen) : AM LIdx := do
  if n = 0 then pure v
  else do
    let j := n - 1
    let e := stk[j]!
    if mode.verifiedChecks && !(pv == e.2) then
      fail (.notImplemented "sort-annotation mismatch (forall-cod)")
    else do
      let v2 ← internLNode (.imax e.1 v)
      inferPisOut mode stk j v2 pv
termination_by n

/-- con-leche: ConLeche/Cached/CoreC.lean:1256-1267 inferPisLeafI — the ∀
loop's LEAF: open the residual codomain against every free variable at once,
infer its sort, read the zero-ness once and fold `imax` outward. -/
def inferPisLeaf (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (d : Nat)
    (t : EIdx) (k : Nat) (fvs : Array EIdx) (stk : Array (LIdx × PropWhen)) :
    AM EIdx := do
  let ob ← instantiateListFast coreWalkFuel t fvs 0
  let bt ← r.infer (d + k) ob
  let v ← ensureSort r fe (d + k) bt
  let lv ← readLevelM v
  let pv := Level.zeronessOf lv
  let iv ← inferPisOut mode stk stk.size v pv
  internSortE iv

/-- con-leche: ConLeche/Cached/CoreC.lean:1269-1290 inferPisI — the
∀-telescope inference loop, `inferLams`' twin: peel the chain, open each
domain in bulk, and stack the binder's SORT (for the `imax` fold) beside its
datum (for the chain check). -/
def inferPis (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (d : Nat) :
    Nat → EIdx → Nat → Array EIdx → Array (LIdx × PropWhen) → AM EIdx
  | 0, t, k, fvs, stk => inferPisLeaf mode r fe d t k fvs stk
  | peel + 1, t, k, fvs, stk => do
    if t.tag != ETag.forallE then inferPisLeaf mode r fe d t k fvs stk
    else
      match ← viewBind t with
      | none => failDanglingE
      | some (ty, body, mb) => do
        let tyo ← instantiateListFast coreWalkFuel ty fvs 0
        let tty ← r.infer (d + k) tyo
        let w ← r.whnf (d + k) tty
        if w.tag == ETag.sort then
          match ← viewSort w with
          | none => failDanglingE
          | some u => do
            let fv ← internFVarE (d + k) tyo
            inferPis mode r fe d peel body (k + 1) (fvs.push fv) (stk.push (u, mb.pw))
        else fail (.invalid "expected a sort")

/-- con-leche: ConLeche/Cached/CoreC.lean:1292-1389 inferBodyI — the `.lam`
clause: the binder's own domain is checked to be a type here (which is why the
loop starts at `k = 1` with one free variable and a one-entry stack), and the
rest of the λ-chain is peeled by `inferLams`. -/
def inferLam (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (ty body : EIdx) (mb : BinderMeta) : AM EIdx := do
  let tty ← r.infer depth ty
  let w ← r.whnf depth tty
  if w.tag == ETag.sort then do
    let fv ← internFVarE depth ty
    inferLams mode r fe depth peelFuel body 1 #[fv] #[(ty, mb)]
  else fail (.invalid "expected a sort")

/-- con-leche: ConLeche/Cached/CoreC.lean:1292-1389 inferBodyI — the
`.forallE` clause, `inferLam`'s twin. -/
def inferForall (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (ty body : EIdx) (mb : BinderMeta) : AM EIdx := do
  let tty ← r.infer depth ty
  let w ← r.whnf depth tty
  if w.tag == ETag.sort then
    match ← viewSort w with
    | none => failDanglingE
    | some u => do
      let fv ← internFVarE depth ty
      inferPis mode r fe depth peelFuel body 1 #[fv] #[(u, mb.pw)]
  else fail (.invalid "expected a sort")

/-! ### The application spine's inference

con-leche's own CACHED-tier clauses `Cached/CoreC.lean:1011-1042 inferSpineI`
and `:1044-1091 inferSpineIOI` (task #97-P6-9).  The spec-shaped `.app` clause
infers the type of every PREFIX of the spine and `whnf`s it, which is `O(n²)`
node work down a long application; these walk the head's type once and carry
the pending substitutions in an accumulator, opening each domain in ONE
`instantiateList`.  The bridge cites `Verify/BetaSpine.lean:1566
inferSpine_sound` and `:1576 inferSpine_sound_body`.

The `whnf` re-entry at a non-∀ head is where the chained clause's own `whnf`
sits, and it RESETS the accumulator, because the reduct is already the opened
type. -/

/-- con-leche: ConLeche/Cached/CoreC.lean:1011-1042 inferSpineI — walk the
head's type down the argument vector at the FULL grade. -/
def inferSpine (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (ty : EIdx) (acc : Array EIdx) (args : Array EIdx) (i : Nat) : AM EIdx := do
  if hi : i < args.size then do
    let a := args[i]
    if ty.tag == ETag.forallE then
      match ← viewBind ty with
      | none => failDanglingE
      | some (dom, body, _) => do
        let dom2 ← instantiateListFast coreWalkFuel dom acc 0
        let ta ← r.infer depth a
        if !(← r.defeq depth ta dom2) then
          fail (.invalid "application type mismatch")
        else inferSpine mode r fe depth body (acc.push a) args (i + 1)
    else do
      let ty2 ← instantiateListFast coreWalkFuel ty acc 0
      let w ← r.whnf depth ty2
      if w.tag == ETag.forallE then
        match ← viewBind w with
        | none => failDanglingE
        | some (dom, body, _) => do
          let ta ← r.infer depth a
          if !(← r.defeq depth ta dom) then
            fail (.invalid "application type mismatch")
          else inferSpine mode r fe depth body #[a] args (i + 1)
      else fail (.invalid "function expected")
  else instantiateListFast coreWalkFuel ty acc 0
termination_by args.size - i

/-- con-leche: ConLeche/Cached/CoreC.lean:1292-1389 inferBodyI — the `.app`
clause: the head is inferred ONCE and the whole argument vector is run through
`inferSpine`. -/
def inferApp (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (e : EIdx) : AM EIdx := do
  let hv ← headAndArgs e
  let tf ← r.infer depth hv.1
  inferSpine mode r fe depth tf #[] hv.2 0

/-- con-leche: ConLeche/Cached/CoreC.lean:1044-1091 inferSpineIOI — the io
lane's spine walk: `inferSpine` with the per-argument certificate skipped when
the ∀'s validated annotation licenses it (`CheckMode.ioSkip`). -/
def inferSpineIO (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (ty : EIdx) (acc : Array EIdx) (args : Array EIdx) (i : Nat) : AM EIdx := do
  if hi : i < args.size then do
    let a := args[i]
    if ty.tag == ETag.forallE then
      match ← viewBind ty with
      | none => failDanglingE
      | some (dom, body, mt) => do
        let cert ←
          if mode.ioSkip mt.pw then pure true
          else do
            let dom2 ← instantiateListFast coreWalkFuel dom acc 0
            let ta ← r.infer depth a
            r.defeq depth ta dom2
        if !cert then fail (.invalid "application type mismatch")
        else inferSpineIO mode r fe depth body (acc.push a) args (i + 1)
    else do
      let ty2 ← instantiateListFast coreWalkFuel ty acc 0
      let w ← r.whnf depth ty2
      if w.tag == ETag.forallE then
        match ← viewBind w with
        | none => failDanglingE
        | some (dom, body, mt) => do
          let cert ←
            if mode.ioSkip mt.pw then pure true
            else do
              let ta ← r.infer depth a
              r.defeq depth ta dom
          if !cert then fail (.invalid "application type mismatch")
          else inferSpineIO mode r fe depth body #[a] args (i + 1)
      else fail (.invalid "function expected")
  else instantiateListFast coreWalkFuel ty acc 0
termination_by args.size - i

/-- con-leche: ConLeche/Cached/CoreC.lean:1391-1448 inferBodyIOI — the io
lane's `.app` clause. -/
def inferAppIOAt (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (e : EIdx) : AM EIdx := do
  let hv ← headAndArgs e
  let tf ← r.infer depth hv.1
  inferSpineIO mode r fe depth tf #[] hv.2 0

/-- con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody — the inference
body.  The `.const` clause reads the stored type through `constTyAt`, so a
constant inferred twice at the same levels pays the level substitution
once. -/
def inferBody (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) :
    Nat → EIdx → AM EIdx :=
  fun depth e => do
    match ← view e with
    | .sort u => do
      let su ← internLNode (.succ u)
      internE (.sort su)
    | .fvar idx ty =>
      -- scope check at the leaf of a traversal that happens anyway
      if idx < depth then pure ty
      else fail (.invalid "free variable out of scope")
    | .const n us => do
      match fe.find? n with
      | none => do
        let err ← unknownConstError n
        fail err
      | some ci => do
        -- a projection table is not a term (con-leche's task #175 W4c)
        if ci.isTowerEntry then do
          -- no readback for the message: the port has none (round 4's audit)
          fail (.invalid "projection table entry used as a constant")
        else do
          let cv ← ci.toConstantVal
          let usl ← viewLs us
          if usl.length != cv.levelParams.length then do
            fail (.invalid "incorrect number of universe levels")
          else constTyAt cv us
    | .lit (.natVal _) => do
      if ← natLitSupported fe then do
        let nn ← pinNat
        constE nn
      else fail (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      if ← strLitSupported fe then do
        let sn ← pinString
        constE sn
      else fail (.notImplemented
        "string literals before the String support declarations")
    -- **The binder-telescope loops** (task #97-P6-12), con-leche's own
    -- `Cached/CoreC.lean:1292-1389 inferBodyI`: the whole chain is peeled and
    -- opened in bulk rather than one binder at a time through the knot.
    | .forallE ty body mb => inferForall mode r fe depth ty body mb
    | .lam ty body mb => inferLam mode r fe depth ty body mb
    -- **The batched spine** (task #97-P6-9), con-leche's own
    -- `Cached/CoreC.lean:1292-1389 inferBodyI`.
    | .app _ _ => inferApp mode r fe depth e
    | .proj sn i pe => do
      let te ← r.whnf depth (← r.infer depth pe)
      let hh ← getAppFn coreWalkFuel te
      if hh.tag == ETag.const then
        match ← view hh with
        | .const T us => do
          match ← fe.findProj? T i with
          | some entry => do
            let targs ← getAppArgs coreWalkFuel te
            match ← viewLsLen us with
            | none => failDanglingLs
            | some usl =>
            -- con-leche's task #175 wiring W5: the node's struct name must be
            -- the subject type's head
            if T = sn ∧ targs.length = entry.numParams ∧
                usl = entry.levelParams.length then do
              let z ← zeroLevel
              if (← lvlEq? entry.structSort z) == some true then do
                let ks ← readNamesM entry.levelParams
                let vs ← readLevelsM us
                let fs ← readLevelM entry.fieldSort
                if !(Level.isEquiv (Level.subst ks vs fs) .zero == some true) then
                  fail (.invalid
                    "projection from a propositional structure must be a proposition")
                else entry.typeAt us targs pe
              else entry.typeAt us targs pe
            else fail (.notImplemented "projection without a native entry")
          | none => fail (.notImplemented "projection without a native entry")
        | _ => fail (.notImplemented "projection without a native entry")
      else fail (.notImplemented "projection without a native entry")
    | .letE _ _ _ =>
      fail (.internal "inferType: `let` in an annotated expression")
    | .bvar _ =>
      fail (.notImplemented "inferType beyond the supported fragment")

/-- con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO — **the io
inference body**: `inferBody` with two clauses changed — no domain-sort run
at the λ (official's `infer_lambda` skips it at `infer_only`), and the
application rule's per-argument certificate skipped when the ∀'s validated
annotation licenses it. -/
def inferBodyIO (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) :
    Nat → EIdx → AM EIdx :=
  fun depth e => do
    match ← view e with
    | .sort u => do
      let su ← internLNode (.succ u)
      internE (.sort su)
    | .fvar idx ty =>
      if idx < depth then pure ty
      else fail (.invalid "free variable out of scope")
    | .const n us => do
      match fe.find? n with
      | none => do
        let err ← unknownConstError n
        fail err
      | some ci => do
        if ci.isTowerEntry then do
          -- no readback for the message: the port has none (round 4's audit)
          fail (.invalid "projection table entry used as a constant")
        else do
          let cv ← ci.toConstantVal
          match ← viewLsLen us with
          | none => failDanglingLs
          | some usl =>
          if usl != cv.levelParams.length then do
            fail (.invalid "incorrect number of universe levels")
          else constTyAt cv us
    | .lit (.natVal _) => do
      if ← natLitSupported fe then do
        let nn ← pinNat
        constE nn
      else fail (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      if ← strLitSupported fe then do
        let sn ← pinString
        constE sn
      else fail (.notImplemented
        "string literals before the String support declarations")
    | .forallE ty body mb => do
      let hh ← r.whnf depth (← r.infer depth ty)
      if hh.tag == ETag.sort then
        match ← view hh with
        | .sort u => do
          let fv ← internE (.fvar depth ty)
          let ob ← instantiate1Fast coreWalkFuel body fv 0
          let v ← ensureSort r fe (depth + 1) (← r.infer (depth + 1) ob)
          let ok ←
            if mode.verifiedChecks then do
              let lv ← readLevelM v
              pure (Level.zeronessOf lv == mb.pw)
            else pure true
          if !ok then
            fail (.notImplemented "sort-annotation mismatch (forall-cod)")
          else do
            let iu ← internLNode (.imax u v)
            internE (.sort iu)
        | _ => fail (.invalid "expected a sort")
      else fail (.invalid "expected a sort")
    | .lam ty body mb => do
      -- con-leche's task #168 stage 2: no domain-sort run at the io grade
      let fv ← internE (.fvar depth ty)
      let ob ← instantiate1Fast coreWalkFuel body fv 0
      let bt ← r.infer (depth + 1) ob
      if mode.verifiedChecks then do
        match ← lamPw body with
        | some pwI =>
          if !(mb.pw == pwI) then
            fail (.notImplemented "sort-annotation mismatch (lam-cod-chain)")
          else inferLamResult ty bt depth mb
        | none => do
          let btt ← r.infer (depth + 1) bt
          let vb ← ensureSort r fe (depth + 1) btt
          let lvb ← readLevelM vb
          if !(Level.zeronessOf lvb == mb.pw) then
            fail (.notImplemented "sort-annotation mismatch (lam-cod-leaf)")
          else inferLamResult ty bt depth mb
      else inferLamResult ty bt depth mb
    -- **The batched spine at the io grade** (task #97-P6-9), con-leche's own
    -- `Cached/CoreC.lean:1391-1448 inferBodyIOI`.  **THE io SITE** is inside
    -- `inferSpineIO`: at a ∀ whose datum is `never` the certificate is dead
    -- weight; the read is the DATUM ALONE (the licence ruling of
    -- 2026-09-06), never the mode.
    | .app _ _ => inferAppIOAt mode r fe depth e
    | .proj sn i pe => do
      let te ← r.whnf depth (← r.infer depth pe)
      let hh ← getAppFn coreWalkFuel te
      if hh.tag == ETag.const then
        match ← view hh with
        | .const T us => do
          match ← fe.findProj? T i with
          | some entry => do
            let targs ← getAppArgs coreWalkFuel te
            match ← viewLsLen us with
            | none => failDanglingLs
            | some usl =>
            if T = sn ∧ targs.length = entry.numParams ∧
                usl = entry.levelParams.length then do
              let z ← zeroLevel
              if (← lvlEq? entry.structSort z) == some true then do
                let ks ← readNamesM entry.levelParams
                let vs ← readLevelsM us
                let fs ← readLevelM entry.fieldSort
                if !(Level.isEquiv (Level.subst ks vs fs) .zero == some true) then
                  fail (.invalid
                    "projection from a propositional structure must be a proposition")
                else entry.typeAt us targs pe
              else entry.typeAt us targs pe
            else fail (.notImplemented "projection without a native entry")
          | none => fail (.notImplemented "projection without a native entry")
        | _ => fail (.notImplemented "projection without a native entry")
      else fail (.notImplemented "projection without a native entry")
    | .letE _ _ _ =>
      fail (.internal "inferType: `let` in an annotated expression")
    | .bvar _ =>
      fail (.notImplemented "inferType beyond the supported fragment")


/-! ## Definitional equality

con-leche's `Core.lean`:2373-2697. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1406-1418 boolTrueShortcut — **the
eq-true shortcut** (the divergence audit's E2): the left side is fully
head-normalised and the verdict is `true` iff the reduct is `Bool.true`. -/
def boolTrueShortcut (r : CoreFnsA) (depth : Nat) (a : EIdx) : AM Bool := do
  let w ← r.whnf depth a
  isBoolTrue w

/-- con-leche: ConLeche/Kernel/Core.lean:1420-1439 defeqSpine —
levels-and-spine congruence for two applications of the *same* stored
constant (the lazy delta same-head short-circuit, official's
`try_eq_const_app`). -/
def defeqSpine (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    AM Bool := do
  let hh ← getAppFn coreWalkFuel a
  if hh.tag == ETag.const then
    match ← view hh with
    | .const n us =>
      let hh ← getAppFn coreWalkFuel b
      if hh.tag == ETag.const then
        match ← view hh with
        | .const n' us' => do
          let aa ← getAppArgs coreWalkFuel a
          let bb ← getAppArgs coreWalkFuel b
          if n = n' ∧ aa.length = bb.length then
            match ← lvlsEq? us us' with
            | some true => defEqList r fe depth aa bb
            | _ => pure false
          else pure false
        | _ => pure false
      else pure false
    | _ => pure false
  else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep — the
literal-acceleration guard: *both* sides free of free variables, mirroring
the official kernel's `lazy_delta_reduction`.  The arena reads the `O(1)`
eager per-node fvar range where the specification walks. -/
def defeqNoFvars (a b : EIdx) : AM Bool := do
  if ← hasFvarFast coreWalkFuel a then pure false
  else do
    let y ← hasFvarFast coreWalkFuel b
    pure !y

/-! ### The batched defeq binder descent

DESIGN §8.6 item 14, and **the one lever of the P6 campaign that is the
PORT's own algorithm** rather than a clause copied from con-leche's cached
tier: `Cached/CoreC.lean:1456-1623 defeqStepI` keeps its `.forallE`/`.lam`
arms chained, so there is nothing upstream to mirror and the bridge owes its
own identification lemma.  Licensed by the maintainer's ruling before
DESIGN §8.7 ("do it here — with its own identification lemma against the pure
tier's chained arms owed by the bridge (P3)"). -/

/-- con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep — the peel's
OUTWARD step, the arm's trailing annotation test: the chain tests the binder
data on the way out, innermost binder first, and only once the body's
comparison has returned `true`.  The loop carries the INNERMOST mismatching
level in two scalars (`mism`, with `mismLam` for the message that level would
raise) and raises it here. -/
def defeqPeelDone (mism mismLam : Bool) : AM Bool :=
  if mism then
    if mismLam then fail (.notImplemented "sort-annotation mismatch (defeq-lam)")
    else fail (.notImplemented "sort-annotation mismatch (defeq-forall)")
  else pure true

/-- con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep — the batched
descent's LEAF: open both residuals ONCE against the whole `fvs` and hand the
pair back to the knot, which is the chain's own next step. -/
def defeqPeelLeaf (r : CoreFnsA) (d : Nat) (a b : EIdx) (k : Nat)
    (fvs : Array EIdx) (mism mismLam : Bool) : AM Bool := do
  let o1 ← instantiateListFast coreWalkFuel a fvs 0
  let o2 ← instantiateListFast coreWalkFuel b fvs 0
  if !(← r.defeq (d + k) o1 o2) then pure false
  else defeqPeelDone mism mismLam

/-- con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep — **the batched
defeq binder descent**.

`a` and `b` are the two RAW bodies of the binders peeled so far — never
opened — `fvs` holds the `k` free variables the peel has introduced, innermost
first, and `d + k` is the depth the next binder sits at.  While both handles
carry the SAME binder tag the loop peels one more level: each domain is opened
against the accumulated `fvs` in ONE `instantiateList`, the two opened domains
are compared with the knot exactly where the chain compares them, the fresh
`fvar (d + k) ty₂'` is pushed, and the two raw bodies go round again.

**The identification the bridge owes** — *batched descent = the pure chain*,
on every input, by `Expr.instantiateList_cons` (`Verify/InstList.lean:54-117`)
and the per-binder domain check.  Its four parts, which are what makes the
loop's guard what it is:

1. *The opens agree.*  The chain's `k`-fold `instantiate1` of a domain at
   cursors `k-1, …, 0` is one `instantiateList` against the same free
   variables at cursor 0 — con-leche's `instantiateList_cons`, the equation
   tasks #97-P6-9, -11 and -12 already cite.  The same equation identifies the
   leaf's single open with the chain's last one.
2. *The chain really reaches this arm at every peeled level.*  At level `j`
   the chain runs a WHOLE `defeqStep` on the opened pair, so the peel is sound
   only because every earlier arm is a no-op on a pair of same-kind binder
   nodes: `whnfCore` is the identity on `.forallE` and `.lam` (its first four
   clauses), `isBoolTrue` is `false` off any non-`.const`, the hoisted proof
   irrelevance is skipped because `quickPair` holds of two `∀`s and of two
   `λ`s, `reduceNat` is `none` off any non-`.app`, and `unfoldableHead` is
   `false` on both sides because `getAppFn` of a binder is the binder — so
   lazy delta falls straight through to the structural stage and its binder
   arm.  The guard peels only when both handles carry the same binder tag, and
   stopping EARLIER is always safe: the leaf hands the pair to the knot, which
   is the chain's own next step.
3. *A failure lands at the same binder.*  The domain comparison at level `j`
   runs before the descent past `j`, in the chain's order, so a domain that is
   not defeq returns the same `false` (and an erroring domain the same error)
   at the same `k` the chain returns it at.  The annotation-data check is the
   other way round — see `defeqPeelDone`.  Deeper mismatches, past the peel,
   are raised inside that call, before this one looks at its own flag, which is
   again the chain's order.
4. *The caches see less, and that is all.*  The chain probes and writes the
   `defeq` memo at each of the `k` intermediate opened pairs; the batch never
   builds those pairs, so it neither probes nor writes them.  A probe that
   would have hit returns the memo's stored verdict, which is the verdict of
   recomputing it (the memo's own soundness obligation, unchanged here), so the
   result is the same; a write that does not happen only turns a later hit into
   a later miss.  The one asymmetry that is NOT a cache: the batch spends one
   unit of knot fuel where the chain spends `k`, so it can return a verdict
   where the chain runs out.  Fuel exhaustion is an `Internal` error and never
   a verdict, and the bridge's statement is existential in the fuel (`∃ F`), so
   this is the same latitude `peelFuel` itself has.

The stack the chain would hold is two scalars because the only per-level datum
the outward pass needs is that innermost mismatch; the domains and the binder
kinds are not revisited.

Two equality short-circuits ride with it, and both are `defeqStep`'s own first
arm one level up: the peel returns at `a == b` (the chain opens these two
residuals against the same free variables and hands the pair to the knot,
whose `a == b` test then decides `true`), and the domain's knot call is
skipped when the two RAW domains are the same handle. -/
def defeqPeel (mode : CheckMode) (r : CoreFnsA) (d : Nat) :
    Nat → EIdx → EIdx → Nat → Array EIdx → Bool → Bool → AM Bool
  | peel, a, b, k, fvs, mism, mismLam => do
    -- The peel's test is a tag read off the two handle words (the ruling
    -- before §8.7) and the binder PROJECTION (task #97-P6-10).
    let ta := a.tag
    if a == b then defeqPeelDone mism mismLam
    else if peel = 0 || ta != b.tag || !(ETag.isBind ta) then
      defeqPeelLeaf r d a b k fvs mism mismLam
    else
      match ← viewBindI a with
      | none => failDanglingE
      | some (da, ba, ma) =>
        match ← viewBindI b with
        | none => failDanglingE
        | some (db, bb, mb) => do
          -- The domains are the same walk of the same input when the two RAW
          -- domains are the same handle, and the chain's own `a == b` arm
          -- decides them `true`; one open, no knot call.
          let sameDom := da == db
          let t1 ← instantiateListFast coreWalkFuel da fvs 0
          let t2 ← if sameDom then pure t1
                   else instantiateListFast coreWalkFuel db fvs 0
          let dq ← if sameDom then pure true else r.defeq (d + k) t1 t2
          if !dq then pure false
          else do
            let fv ← internFVarE (d + k) t2
            -- The annotation test is the datum HANDLES (task #97-P6-16): the
            -- binder datum is interned, so `BMIdx` equality IS `PropWhen`
            -- equality — the cons table's own exactness — and the
            -- innermost-first order of the chain's test is unchanged.
            let mm := mode.verifiedChecks && !(ma == mb)
            let m2 := mism || mm
            let ml2 := if mm then ta == ETag.lam else mismLam
            match peel with
            | 0 => defeqPeelLeaf r d ba bb (k + 1) (fvs.push fv) m2 ml2
            | p + 1 => defeqPeel mode r d p ba bb (k + 1) (fvs.push fv) m2 ml2

/-- con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep — `defeqStep`'s
`.forallE`/`.lam` binder-congruence arm: con-leche's clause for the FIRST
binder (the domains are compared and the fresh free variable is made), then
the batched descent for the rest of the two telescopes. -/
def defeqBinders (mode : CheckMode) (r : CoreFnsA) (depth : Nat)
    (ty1 body1 : EIdx) (m1 : BinderMeta) (ty2 body2 : EIdx) (m2 : BinderMeta)
    (isLam : Bool) : AM Bool := do
  if !(← r.defeq depth ty1 ty2) then pure false
  else do
    let fv ← internFVarE depth ty2
    let mm := mode.verifiedChecks && !(m1.pw == m2.pw)
    let ml := if mm then isLam else false
    defeqPeel mode r depth peelFuel body1 body2 1 #[fv] mm ml

/-- con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep — the
definitional-equality body: syntactic fast path, head normalization of both
sides (**no delta**), proof irrelevance, then the *lazy delta* strategy of
real kernels.  Each literal-acceleration and unfolding step is one
**iteration of this loop**, handed to `k`. -/
def defeqStep (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (k : Bool → EIdx → EIdx → AM Bool) (pi : Bool) (a b : EIdx) : AM Bool := do
  -- syntactic fast path (the references' most-hit branch)
  if a == b then pure true else do
  -- the eq-true shortcut (E2): right side `Bool.true`, left side fvar-free,
  -- at an entry only
  let sc ←
    if pi && (← isBoolTrue b) && !(← hasFvarFast coreWalkFuel a) then
      boolTrueShortcut r depth a
    else pure false
  if sc then pure true else do
  let a' ← r.whnfCore depth a
  let b' ← r.whnfCore depth b
  if a' == b' then pure true else do
  -- proof irrelevance, hoisted before lazy delta exactly as in the official
  -- kernel; once per `is_def_eq_core` entry (D3), and never on a pair
  -- official's `quick_is_def_eq` decides itself (D4)
  let pir ←
    if pi && !(quickPair a' b') then propIrrel r fe depth a' b'
    else pure false
  if pir then pure true else do
  let nf ← defeqNoFvars a' b'
  match ← (if nf then reduceNat r fe depth a' else pure none) with
  | some a₂ => k true a₂ b'
  | none =>
  match ← (if nf then reduceNat r fe depth b' else pure none) with
  | some b₂ => k true a' b₂
  | none => do
  -- Lazy delta, **decision before materialization**
  let ua ← unfoldableHead fe a'
  let ub ← unfoldableHead fe b'
  match ua, ub with
  | true, false =>
    match ← unfoldDefinition fe a' with
    | some a₂ => k false a₂ b'
    | none => pure false
  | false, true =>
    match ← unfoldDefinition fe b' with
    | some b₂ => k false a' b₂
    | none => pure false
  | true, true => do
    let ha ← headHint fe a'
    let hb ← headHint fe b'
    if ReducibilityHint.lt hb ha then
      match ← unfoldDefinition fe a' with
      | some a₂ => k false a₂ b'
      | none => pure false
    else if ReducibilityHint.lt ha hb then
      match ← unfoldDefinition fe b' with
      | some b₂ => k false a' b₂
      | none => pure false
    else if ReducibilityHint.sameRegular ha hb && (← sameConstHeads a' b') then do
      -- same constant at equal *regular* hints: cheap congruence first
      if ← defeqSpine r fe depth a' b' then pure true
      else
        match ← unfoldDefinition fe a', ← unfoldDefinition fe b' with
        | some a₂, some b₂ => k false a₂ b₂
        | _, _ => pure false
    else
      match ← unfoldDefinition fe a', ← unfoldDefinition fe b' with
      | some a₂, some b₂ => k false a₂ b₂
      | _, _ => pure false
  | false, false =>
    match ← view a', ← view b' with
    | .sort u, .sort v => liftFueled "level comparison" (← lvlEq? u v)
    | .lit l₁, .lit l₂ => pure (l₁ == l₂)
    -- a packed literal against a constructor form: compare shape-directed
    | .lit (.natVal n), .const c us => do
      let el ← emptyLevels
      let nz ← pinNatZero
      if c = nz ∧ us = el then pure (n == 0)
      else stuckIrrel mode r fe depth a' b'
    | .const c us, .lit (.natVal n) => do
      let el ← emptyLevels
      let nz ← pinNatZero
      if c = nz ∧ us = el then pure (n == 0)
      else stuckIrrel mode r fe depth a' b'
    | .lit (.natVal nn), .app f x => do
      match nn with
      | k' + 1 => do
        if f.tag == ETag.const then
          match ← view f with
          | .const c us => do
            let el ← emptyLevels
            let ns ← pinNatSucc
            if c = ns ∧ us = el then do
              let l ← internE (.lit (.natVal k'))
              r.defeq depth l x
            else stuckIrrel mode r fe depth a' b'
          | _ => stuckIrrel mode r fe depth a' b'
        else stuckIrrel mode r fe depth a' b'
      | _ => stuckIrrel mode r fe depth a' b'
    | .app f x, .lit (.natVal nn) => do
      match nn with
      | k' + 1 => do
        if f.tag == ETag.const then
          match ← view f with
          | .const c us => do
            let el ← emptyLevels
            let ns ← pinNatSucc
            if c = ns ∧ us = el then do
              let l ← internE (.lit (.natVal k'))
              r.defeq depth x l
            else stuckIrrel mode r fe depth a' b'
          | _ => stuckIrrel mode r fe depth a' b'
        else stuckIrrel mode r fe depth a' b'
      | _ => stuckIrrel mode r fe depth a' b'
    -- a string literal against a unary `String.ofList` application
    | .lit (.strVal st), .app fo _ => do
      if fo.tag == ETag.const then
        match ← view fo with
        | .const cO usO => do
          let el ← emptyLevels
          let sl ← pinStringOfList
          if cO = sl ∧ usO = el ∧ (← strLitSupported fe) then do
            let c ← strLitToConstructor st
            r.defeq depth c b'
          else stuckIrrel mode r fe depth a' b'
        | _ => stuckIrrel mode r fe depth a' b'
      else stuckIrrel mode r fe depth a' b'
    | .app fo _, .lit (.strVal st) => do
      if fo.tag == ETag.const then
        match ← view fo with
        | .const cO usO => do
          let el ← emptyLevels
          let sl ← pinStringOfList
          if cO = sl ∧ usO = el ∧ (← strLitSupported fe) then do
            let c ← strLitToConstructor st
            r.defeq depth a' c
          else stuckIrrel mode r fe depth a' b'
        | _ => stuckIrrel mode r fe depth a' b'
      else stuckIrrel mode r fe depth a' b'
    | .fvar i _, .fvar j _ =>
      if i == j then pure true else stuckIrrel mode r fe depth a' b'
    | .const n us, .const n' us' => do
      if n = n' then do
        if ← liftFueled "level comparison" (← lvlsEq? us us') then pure true
        else stuckIrrel mode r fe depth a' b'
      else stuckIrrel mode r fe depth a' b'
    -- binder congruence, BATCHED (task #97-P6-14); the annotation comparison
    -- runs LAST, innermost binder first
    | .forallE ty₁ body₁ m₁, .forallE ty₂ body₂ m₂ =>
      defeqBinders mode r depth ty₁ body₁ m₁ ty₂ body₂ m₂ false
    | .lam ty₁ body₁ m₁, .lam ty₂ body₂ m₂ =>
      defeqBinders mode r depth ty₁ body₁ m₁ ty₂ body₂ m₂ true
    | .app _ _, .app _ _ => do
      -- stuck applications: **spine-wise** congruence (official's
      -- `is_def_eq_app`), never a recursion on the partial applications
      let aa ← getAppArgs coreWalkFuel a'
      let bb ← getAppArgs coreWalkFuel b'
      if aa.length = bb.length then do
        let fa ← getAppFn coreWalkFuel a'
        let fb ← getAppFn coreWalkFuel b'
        if ← r.defeq depth fa fb then do
          if ← defEqList r fe depth aa bb then pure true
          else stuckIrrel mode r fe depth a' b'
        else stuckIrrel mode r fe depth a' b'
      else stuckIrrel mode r fe depth a' b'
    | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ => do
      if s₁ == s₂ && i₁ == i₂ then do
        if ← r.defeq depth e₁ e₂ then pure true
        else stuckIrrel mode r fe depth a' b'
      else stuckIrrel mode r fe depth a' b'
    -- one-sided λ: eta, else the stuck fallbacks
    | .lam ty₁ body₁ m₁, _ => do
      if ← etaCert mode r fe depth ty₁ body₁ m₁ b' then pure true
      else stuckIrrel mode r fe depth a' b'
    | _, .lam ty₂ body₂ m₂ => do
      if ← etaCert mode r fe depth ty₂ body₂ m₂ a' then pure true
      else stuckIrrel mode r fe depth a' b'
    -- distinct whnf-stuck head symbols
    | _, _ => stuckIrrel mode r fe depth a' b'

/-- con-leche: ConLeche/Kernel/Core.lean:1703-1708 defeqLoop — the lazy-delta
loop: iterate `defeqStep` on its own step budget. -/
def defeqLoop (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) :
    Nat → Bool → EIdx → EIdx → AM Bool
  | 0, _, _, _ => fail (.internal "fuel exhausted: defeq loop")
  | fl + 1, pi, a, b =>
    defeqStep mode r fe depth (defeqLoop mode r fe depth fl) pi a b

/-- con-leche: ConLeche/Kernel/Core.lean:1710-1714 defeqLoopFuel — step
budget of the lazy-delta loop (lean4lean's `FuelConfig.lazyDelta`).
Exhaustion is an internal error, never a verdict. -/
def defeqLoopFuel : Nat := 100000

/-- con-leche: ConLeche/Kernel/Core.lean:1716-1719 defeqBody — the
definitional-equality body: the lazy-delta loop at its own step budget. -/
def defeqBody (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) :
    Nat → EIdx → EIdx → AM Bool :=
  fun depth a b => defeqLoop mode r fe depth defeqLoopFuel true a b

/-- con-leche: ConLeche/Kernel/Core.lean:1721-1730 isPropType — check that a
(raw) type is a `Prop` by annotating it and inferring its sort. -/
def isPropType (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (ty : EIdx) :
    AM Bool := do
  let ty' ← r.annotate depth ty
  -- io grade: `ty'` is the pass's own output, already annotated
  let s ← ensureSort r fe depth (← r.inferIO depth ty')
  let z ← zeroLevel
  liftFueled "level comparison" (← lvlEq? s z)

/-! ## The untrusted annotation writes

con-leche's `Core.lean`:2699-2893. -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1015-1016 pwWritten — is this datum
a real (non-placeholder) input annotation? -/
@[inline] def pwWritten (pw : PropWhen) : Bool := !pw.isNever

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1018-1024 annotBinderMeta — the
datum a rebuilt binder ends up with: the one threaded in from the node below,
unless it carries a real input annotation. -/
def annotBinderMeta (pw? : Option PropWhen) (mb : BinderMeta) : BinderMeta :=
  match pw? with
  | some pw => if pwWritten mb.pw then mb else ⟨pw⟩
  | none => mb

/-- con-leche: ConLeche/Kernel/Core.lean:1746-1777 annotPwPi — the ∀ node's
datum: the zero-ness of the *codomain*'s sort, on the already-annotated
opened body.  The head-symbol reader comes first and subsumes the chain
read. -/
def annotPwPi (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (body' : EIdx) :
    AM PropWhen := do
  match ← typeSortPW fe coreWalkFuel body' with
  | some pw => pure pw
  | none => do
    -- io grade: `body'` is already annotated (bottom-up)
    let v ← ensureSort r fe depth (← r.inferIO depth body')
    let lv ← readLevelM v
    pure (Level.zeronessOf lv)

/-- con-leche: ConLeche/Kernel/Core.lean:1779-1793 annotPwLam — the λ node's
datum: the zero-ness of the sort of the *body's type*. -/
def annotPwLam (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (body' : EIdx) :
    AM PropWhen := do
  match ← proofPW fe coreWalkFuel body' with
  | some pw => pure pw
  | none => do
    let bt ← r.inferIO depth body'
    let vb ← ensureSort r fe depth (← r.inferIO depth bt)
    let lvb ← readLevelM vb
    pure (Level.zeronessOf lvb)

/-! ### The annotation's binder telescopes

DESIGN §8.6 item 11: con-leche's cached-tier `annotatePisI`/`annotateLamsI`
with `annotateBindersOutI`'s outward rebuild and its task #161 P5 datum
threading, in place of the per-binder `annotateBinder` clause — which survives
as the λ residual con-leche also keeps.  `Verify/BinderLoop.lean` proves the
two loops sound against the chained bodies (`annotatePis_sound:1612`,
`annotateLams_sound:1714`), over `Expr.instantiateList_cons`. -/

/-- con-leche: ConLeche/Cached/CoreC.lean:1649-1676 annotateBindersOutI — the
annotation's OUTWARD rebuild, shared by the two loops: `abstractRange` closes
each annotated domain over the `j` free variables below it, the datum threads
outward (task #161's P5 rule: a binder keeps its own written annotation and
otherwise takes the one from the node below), and the node is rebuilt at the
tag the loop peeled it at. -/
def annotateBindersOut (isLam : Bool) (d : Nat) (pw? : Option PropWhen)
    (stk : Array (EIdx × BinderMeta)) (n : Nat) (cur : EIdx) : AM EIdx := do
  if n = 0 then pure cur
  else do
    let j := n - 1
    let e := stk[j]!
    let tyAbs ← abstractRangeFast coreWalkFuel e.1 d j 0
    let written := pw?.isSome
    let m := annotBinderMeta pw? e.2
    let pw2 := if written then some m.pw else none
    let nd ←
      if isLam then internLamE tyAbs cur m else internForallEE tyAbs cur m
    annotateBindersOut isLam d pw2 stk j nd
termination_by n

/-- con-leche: ConLeche/Cached/CoreC.lean:1704-1713 annotatePisLeafI — the ∀
loop's LEAF, with `:1693-1702 annotatePisPwI` inlined: open the residual
codomain against every free variable at once, annotate it, compute the datum
the ∀ chain wants, and hand the outward rebuild its starting point. -/
def annotatePisLeaf (r : CoreFnsA) (fe : IFEnv) (d : Nat) (t : EIdx) (k : Nat)
    (fvs : Array EIdx) (stk : Array (EIdx × BinderMeta)) : AM EIdx := do
  let to ← instantiateListFast coreWalkFuel t fvs 0
  let leafp ← r.annotate (d + k) to
  let p ← annotPwPi r fe (d + k) leafp
  let cur ← abstractRangeFast coreWalkFuel leafp d k 0
  annotateBindersOut false d (some p) stk stk.size cur

/-- con-leche: ConLeche/Cached/CoreC.lean:1715-1730 annotatePisI — the
∀-telescope annotation loop: peel a consecutive run of ∀ binders, annotating
and opening each domain in bulk, then hand the residual to the leaf. -/
def annotatePis (r : CoreFnsA) (fe : IFEnv) (d : Nat) :
    Nat → EIdx → Nat → Array EIdx → Array (EIdx × BinderMeta) → AM EIdx
  | 0, t, k, fvs, stk => annotatePisLeaf r fe d t k fvs stk
  | peel + 1, t, k, fvs, stk => do
    if t.tag == ETag.forallE then
      match ← viewBind t with
      | none => failDanglingE
      | some (ty, body, mb) => do
        let tyo ← instantiateListFast coreWalkFuel ty fvs 0
        let typ ← r.annotate (d + k) tyo
        let fv ← internFVarE (d + k) typ
        annotatePis r fe d peel body (k + 1) (fvs.push fv) (stk.push (typ, mb))
    else annotatePisLeaf r fe d t k fvs stk

/-- con-leche: ConLeche/Cached/CoreC.lean:1753-1762 annotateLamsLeafI —
`annotatePisLeaf` at the λ datum (`:1747-1751 annotateLamsPwI` inlined). -/
def annotateLamsLeaf (r : CoreFnsA) (fe : IFEnv) (d : Nat) (t : EIdx) (k : Nat)
    (fvs : Array EIdx) (stk : Array (EIdx × BinderMeta)) : AM EIdx := do
  let to ← instantiateListFast coreWalkFuel t fvs 0
  let leafp ← r.annotate (d + k) to
  let p ← annotPwLam r fe (d + k) leafp
  let cur ← abstractRangeFast coreWalkFuel leafp d k 0
  annotateBindersOut true d (some p) stk stk.size cur

/-- con-leche: ConLeche/Cached/CoreC.lean:1764-1777 annotateLamsI — the λ twin
of `annotatePis`. -/
def annotateLams (r : CoreFnsA) (fe : IFEnv) (d : Nat) :
    Nat → EIdx → Nat → Array EIdx → Array (EIdx × BinderMeta) → AM EIdx
  | 0, t, k, fvs, stk => annotateLamsLeaf r fe d t k fvs stk
  | peel + 1, t, k, fvs, stk => do
    if t.tag == ETag.lam then
      match ← viewBind t with
      | none => failDanglingE
      | some (ty, body, mb) => do
        let tyo ← instantiateListFast coreWalkFuel ty fvs 0
        let typ ← r.annotate (d + k) tyo
        let fv ← internFVarE (d + k) typ
        annotateLams r fe d peel body (k + 1) (fvs.push fv) (stk.push (typ, mb))
    else annotateLamsLeaf r fe d t k fvs stk

/-- con-leche: ConLeche/Cached/CoreC.lean:1779-1867 annotateBodyI — the
per-binder annotation clause, which con-leche's cached tier keeps as the λ
RESIDUAL (the loop is chain-identical only on `bvar`-closed nodes; the cached
bound decides in `O(1)`, and on both corpora this arm is entered zero times). -/
def annotateBinder (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (ty body : EIdx)
    (mb : BinderMeta) (isLam : Bool) : AM EIdx := do
  let typ ← r.annotate depth ty
  let fv ← internFVarE depth typ
  let ob ← instantiate1Fast coreWalkFuel body fv 0
  let bodyp ← r.annotate (depth + 1) ob
  let pw ←
    if !pwWritten mb.pw then
      if isLam then annotPwLam r fe (depth + 1) bodyp
      else annotPwPi r fe (depth + 1) bodyp
    else pure mb.pw
  let ab ← abstract1Fast coreWalkFuel bodyp depth 0
  if isLam then internLamE typ ab ⟨pw⟩ else internForallEE typ ab ⟨pw⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1795-1915 annotateBody — the
annotation body: compute the codomain-sort annotations of every binder,
bottom-up, by real inference on the opened (already annotated) body.  The
`.letE` clause runs the official `infer_let` triple and returns the ζ
reduct, which is why no other pass ever meets a `let`. -/
def annotateBody (r : CoreFnsA) (fe : IFEnv) : Nat → EIdx → AM EIdx :=
  fun depth e => do
    match ← view e with
    | .bvar _ => pure e
    | .fvar idx _ =>
      -- leaf scope check, as in `inferBody`
      if idx < depth then pure e
      else fail (.invalid "free variable out of scope")
    | .sort _ => pure e
    | .const _ _ => pure e
    | .lit (.natVal _) => do
      if ← natLitSupported fe then pure e
      else fail (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      if ← strLitSupported fe then pure e
      else fail (.notImplemented
        "string literals before the String support declarations")
    | .app f a => do
      -- structural (con-leche's task #100 stage 6), with task #97-P6-7's
      -- upward cutoff: 91.5 % of the annotation's rebuilds answer with their
      -- own argument
      let f' ← r.annotate depth f
      let a' ← r.annotate depth a
      internRebuiltApp e (f' == f && a' == a) f' a'
    -- **The binder-telescope loops** (task #97-P6-11), con-leche's own
    -- `annotateBodyI`: the first binder is peeled here, which is why the loop
    -- starts at `k = 1` with one free variable and a one-entry stack.
    | .forallE ty body mb => do
      let typ ← r.annotate depth ty
      let fv ← internFVarE depth typ
      annotatePis r fe depth peelFuel body 1 #[fv] #[(typ, mb)]
    | .lam ty body mb => do
      -- con-leche's `annotateBodyI`'s `.lam` case: "the λ-loop is chain-
      -- identical only on bvar-closed nodes (the chained tails re-open exactly
      -- what they closed); disciplined inputs always are, and the cached bound
      -- decides in O(1)".  Otherwise the spec-shaped single-binder clause runs,
      -- unchanged.
      let b ← bvarB coreWalkFuel e
      if b = 0 then do
        let typ ← r.annotate depth ty
        let fv ← internFVarE depth typ
        annotateLams r fe depth peelFuel body 1 #[fv] #[(typ, mb)]
      else annotateBinder r fe depth ty body mb true
    | .letE ty v b => do
      -- con-leche's task #217: the official `infer_let` triple runs HERE,
      -- before the ζ reduct is taken
      let ty' ← r.annotate depth ty
      let _ ← ensureSort r fe depth (← r.infer depth ty')
      let v' ← r.annotate depth v
      let tv ← r.infer depth v'
      if !(← r.defeq depth tv ty') then
        fail (.invalid "let value type mismatch")
      else do
        let bz ← instantiate1Fast coreWalkFuel b v 0
        r.annotate depth bz
    | .proj sn i pe => do
      let e' ← r.annotate depth pe
      let te ← r.whnf depth (← r.inferIO depth e')
      let hh ← getAppFn coreWalkFuel te
      if hh.tag == ETag.const then
        match ← view hh with
        | .const T _ => do
          match ← fe.findProj? T i with
          | some entry => do
            -- con-leche's task #271 (issue #7): the node's OWN structure name
            -- is official's `infer_proj` premise, checked HERE
            if T != sn then
              fail (.invalid
                "invalid projection: the node names another structure")
            else do
              let targs ← getAppArgs coreWalkFuel te
              if targs.length != entry.numParams then
                fail (.invalid "projection parameter mismatch")
              else internE (.proj T i e')
          | none => do
            let p0 ← fe.findProj? T 0
            fail (if p0.isSome then
                CheckError.invalid "projection index out of range"
              else .notImplemented
                "projection on a non-structure-like type")
        | _ => fail (.notImplemented "projection on a non-structure type")
      else fail (.notImplemented "projection on a non-structure type")

/-! ## The knot

con-leche's `Core.lean`:2897-2936 with the memo probes of
`ConLeche/Cached/CoreC.lean`:1877-1906 inlined in the slots (deviation 6):
`memoEI` passes a getter and a setter lambda per table, and two closures per
slot is what DESIGN §3.4 rules out.  The bodies above are pure of memo
logic, which is the property that matters. -/

/-- con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI — record a
`whnfCore` answer (detach before update, DESIGN §8.4 lesson 14; the cap is
DESIGN §8.3's lesson 10 — past `cacheCap` the table is dropped whole). -/
@[noinline] def whnfCoreSet (e r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.caches.whnfCoreC
  let mp := if mp.size < cacheCap then mp else ∅
  let s := { s with caches := { s.caches with whnfCoreC := ∅ } }
  set { s with caches := { s.caches with whnfCoreC := mp.insert e r } }

/-- con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI — record a `whnf`
answer. -/
@[noinline] def whnfSet (e r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.caches.whnfC
  let mp := if mp.size < cacheCap then mp else ∅
  let s := { s with caches := { s.caches with whnfC := ∅ } }
  set { s with caches := { s.caches with whnfC := mp.insert e r } }

/-- con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI — record a
full-grade `infer` answer. -/
@[noinline] def inferSet (e r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.caches.inferC
  let mp := if mp.size < cacheCap then mp else ∅
  let s := { s with caches := { s.caches with inferC := ∅ } }
  set { s with caches := { s.caches with inferC := mp.insert e r } }

/-- con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI — record an
io-grade `infer` answer, in the io grade's OWN table (con-leche's task #170
memo ruling). -/
@[noinline] def inferIOSet (e r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.caches.inferIOC
  let mp := if mp.size < cacheCap then mp else ∅
  let s := { s with caches := { s.caches with inferIOC := ∅ } }
  set { s with caches := { s.caches with inferIOC := mp.insert e r } }

/-- con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI — record an
`annotate` answer. -/
@[noinline] def annotSet (e r : EIdx) : AM Unit := do
  let s ← get
  let mp := s.caches.annotC
  let mp := if mp.size < cacheCap then mp else ∅
  let s := { s with caches := { s.caches with annotC := ∅ } }
  set { s with caches := { s.caches with annotC := mp.insert e r } }

/-- con-leche: ConLeche/Cached/CoreC.lean:1893-1906 memoBI — record a `defeq`
verdict at the ORDERED pair, both signs (con-leche's `defeqC` stores the
`Bool` result `r`, which is what makes a negative memo sound). -/
@[noinline] def defeqSet (a b : EIdx) (r : Bool) : AM Unit := do
  let s ← get
  let mp := s.caches.defeqC
  let mp := if mp.size < cacheCap then mp else ∅
  let s := { s with caches := { s.caches with defeqC := ∅ } }
  set { s with caches := { s.caches with defeqC := mp.insert (a, b) r } }

/-- con-leche: ConLeche/Kernel/Core.lean:1919-1958 coreKnot
con-leche: ConLeche/Cached/CoreC.lean:1916-1979 coreKnotI
Tie the bodies together: the record whose entry points are the bodies applied
to the record one fuel level down, each under its own memo.  Fuel is *only*
here — exhaustion is an internal error, never a verdict — and the next level
is constructed lazily inside each entry point's closure.

**The io slot's selector is `mode.ioGate`**, `Cached/CoreC.lean:1971`'s
spelling — the EXECUTED knot's, which is the knot this module twins
(deviation 5: (B) has ONE knot and it is the memoized one).  con-leche's
mode-parametric SPEC knot (`Kernel/Core.lean:2929`) selects on
`mode.betaGate` instead, and the two disagree at `.trusted`, where `ioGate`
is `true` and `betaGate` is `false` — `Kernel/Env.lean:109-133` says so, and
says why: the io grade is a *licence*, not a certificate, so the trusted lane
keeps it.  They agree at `.verified`, the mode the bridge is stated at.  The
`ioGate = false` arm is dead at both modes and is kept because it is the
clause structure the twin mirrors.

The io body runs under its own table (`inferIOC`), the full body under
`inferC`: a hit in one grade never serves the other (DESIGN §8.3, lesson 9). -/
def coreKnot (mode : CheckMode) (fe : IFEnv) (wrap : CoreFnsA → CoreFnsA) :
    Nat → CoreFnsA
  | 0 =>
    { whnfCore := fun _ _ => fail (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => fail (.internal "fuel exhausted: whnf")
      infer := fun _ _ => fail (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => fail (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => fail (.internal "fuel exhausted: annotate")
      inferIO := fun _ _ => fail (.internal "fuel exhausted: infer") }
  | fuel + 1 =>
    wrap
      { whnfCore := fun d e => do
          -- **The answer IS the argument, off the tag** (task #97-P6-7's
          -- lever 2): the six head kinds `whnfCoreBody` returns unchanged are
          -- read off the handle word, so neither the memo nor the store is
          -- touched — and neither is the memo WRITTEN, which is what keeps the
          -- table small enough for `clear_fit`'s high-water mark to settle.
          if whnfCoreStuckTag e then pure e
          else
          match (← get).caches.whnfCoreC[e]? with
          | some x => pure x
          | none => do
            let x ← whnfCoreBody mode (coreKnot mode fe wrap fuel) fe d e
            whnfCoreSet e x
            pure x
        whnf := fun d e => do
          if whnfStuckTag e then pure e
          else
          match (← get).caches.whnfC[e]? with
          | some x => pure x
          | none => do
            let x ← whnfBody (coreKnot mode fe wrap fuel) fe d e
            whnfSet e x
            pure x
        infer := fun d e => do
          match (← get).caches.inferC[e]? with
          | some x => pure x
          | none => do
            let x ← inferBody mode (coreKnot mode fe wrap fuel) fe d e
            inferSet e x
            pure x
        defeq := fun d a b => do
          match (← get).caches.defeqC[(a, b)]? with
          | some x => pure x
          | none => do
            let x ← defeqBody mode (coreKnot mode fe wrap fuel) fe d a b
            defeqSet a b x
            pure x
        annotate := fun d e => do
          match (← get).caches.annotC[e]? with
          | some x => pure x
          | none => do
            let x ← annotateBody (coreKnot mode fe wrap fuel) fe d e
            annotSet e x
            pure x
        inferIO := fun d e =>
          if mode.ioGate then do
            match (← get).caches.inferIOC[e]? with
            | some x => pure x
            | none => do
              let x ← inferBodyIO mode
                (CoreFnsA.ioView (coreKnot mode fe wrap fuel)) fe d e
              inferIOSet e x
              pure x
          else do
            match (← get).caches.inferC[e]? with
            | some x => pure x
            | none => do
              let x ← inferBody mode (coreKnot mode fe wrap fuel) fe d e
              inferSet e x
              pure x }

/-- con-leche: ConLeche/Kernel/Core.lean:1960-1963 checkFuel — the shared
fuel for the checker core: bounds the recursion depth of reduction,
inference and definitional equality. -/
def checkFuel : Nat := 100000

/-! ## The fueled entry points

`ConLeche/Kernel/TypeChecker.lean`, whose seven (T) declarations live here
because the arena has ONE knot (deviation 5): con-leche's `pureFns` is
`coreKnot mode env id` at `CheckM` with no memo, and the arena's
`coreKnot` already carries the memos, so `pureFnsA` is the same expression
over handles and the seven entries call it. -/

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:23-25 pureFns — the core, tied
at `AM`, fuel in the knot.  Named `pureFnsA` because the arena's is the
MEMOIZED knot; con-leche's `pureFns` is its unmemoized specification, whose
verdicts the memo does not change (DESIGN §8.3: the memo answers what the
body would have answered). -/
def pureFnsA (mode : CheckMode) (fe : IFEnv) : Nat → CoreFnsA :=
  coreKnot mode fe id

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:27-29 whnfCore — head
normalization without delta (fueled). -/
def whnfCore (mode : CheckMode) (fe : IFEnv) (fuel depth : Nat) (e : EIdx) :
    AM EIdx :=
  (pureFnsA mode fe fuel).whnfCore depth e

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:31-33 whnf — the full
reduction loop (fueled). -/
def whnf (mode : CheckMode) (fe : IFEnv) (fuel depth : Nat) (e : EIdx) :
    AM EIdx :=
  (pureFnsA mode fe fuel).whnf depth e

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:35-38 inferTypeCore —
full-grade type inference (fueled): the declaration front door's entry. -/
def inferTypeCore (mode : CheckMode) (fe : IFEnv) (fuel depth : Nat)
    (e : EIdx) : AM EIdx :=
  (pureFnsA mode fe fuel).infer depth e

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:40-46 inferTypeIO — type
inference at the io grade (fueled): what every internal inference call site
runs. -/
def inferTypeIO (mode : CheckMode) (fe : IFEnv) (fuel depth : Nat)
    (e : EIdx) : AM EIdx :=
  (pureFnsA mode fe fuel).inferIO depth e

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:48-50 isDefEqCore —
definitional equality (fueled). -/
def isDefEqCore (mode : CheckMode) (fe : IFEnv) (fuel depth : Nat)
    (a b : EIdx) : AM Bool :=
  (pureFnsA mode fe fuel).defeq depth a b

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:52-54 annotateCore — the
annotation pass (fueled). -/
def annotateCore (mode : CheckMode) (fe : IFEnv) (fuel depth : Nat)
    (e : EIdx) : AM EIdx :=
  (pureFnsA mode fe fuel).annotate depth e

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:56-58 ensureSortCore —
`ensureSort` over the knot (fueled). -/
def ensureSortCore (mode : CheckMode) (fe : IFEnv) (fuel depth : Nat)
    (e : EIdx) : AM LIdx :=
  ensureSort (pureFnsA mode fe fuel) fe depth e

/-! ## The per-declaration bracket

DESIGN §8.3, "Drop".  P2d calls these at each declaration boundary: the
store's scratch tier goes with `EStore.dropScratch`, and the caches lose
exactly the entries that name a handle of that tier. -/

/-- con-leche: none — **the per-declaration cache drop** (DESIGN §8.3): every
memo entry whose key or value names a scratch handle goes with the tier,
everything persistent stays (con-leche's arena #51).  P2d calls this beside
`EStore.dropScratch`, which is why it is a state operation of its own. -/
@[noinline] def flushCaches : AM Unit := do
  let s ← get
  set { s with caches := Caches.empty }

/-- con-leche: none — **the per-declaration bracket, closed**: drop the
scratch tier of the store and the cache entries that name it, in one
operation, so the two halves cannot drift apart. -/
@[noinline] def dropScratch : AM Unit := do
  flushCaches
  let s ← get
  let st := s.store
  let s := { s with store := EStore.empty }
  set { s with store := st.dropScratch }

/-- con-leche: none — **the per-declaration bracket, opened**: turn the
scratch tier on, and clear the per-call memo tables of `Memos`, which belong
to no tier and whose keys the new tier may reuse. -/
@[noinline] def enterScratch : AM Unit := do
  let s ← get
  let st := s.store
  let s := { s with store := EStore.empty, memos := Memos.empty }
  set { s with store := st.enableScratch }

end ConRon.Arena

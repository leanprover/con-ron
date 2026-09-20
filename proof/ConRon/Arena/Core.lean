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

A `Pins` record in the state, filled once per run, would make each of
these an `O(1)` field read instead of a two-or-three-probe walk; it is the
obvious P2g optimisation and is NOT taken here, because an
initialisation-order hazard (a pin read before it is filled compares
against the zero word) is exactly the kind of silent wrongness the
code-first phase should not introduce before there is a number saying it
is worth it. -/

/-- con-leche: none — intern a reserved `ConLeche.Name` and hand back its
handle.  The one place the arena turns a name VALUE into a name HANDLE
outside the parser. -/
@[inline] def pin (n : ConLeche.Name) : AM NIdx := internName n

/-- con-leche: none — the empty universe-argument list, interned.  `us ==
emptyLevels` is con-leche's pattern `.const _ []`. -/
def emptyLevels : AM LsIdx := internLsNode []

/-- con-leche: none — the level `0`, interned: the comparand of every
`Level.isEquiv u .zero` in this module. -/
def zeroLevel : AM LIdx := internLNode .zero

/-- con-leche: none — the expression `Sort 1` (`.sort (.succ .zero)`),
interned: the pinned type of `Nat`, `String`, `Char` and `Bool`. -/
def sortOne : AM EIdx := do
  let z ← internLNode .zero
  let o ← internLNode (.succ z)
  internE (.sort o)

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
    let lu ← readLevel u
    let lv ← readLevel v
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
    let lu ← readLevels us
    let lv ← readLevels vs
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

/-- con-leche: ConLeche/Kernel/Core.lean:76-96 unknownConstError — **the
verdict at a constant the environment does not know**: `sorryAx` is a
positively detected unsupported feature and DECLINES, every other
unresolved name is a malformed stream and REJECTS.  The name is read back
for the message (DESIGN §8.3: readback happens only for error text). -/
def unknownConstError (n : NIdx) : AM CheckError := do
  let sa ← pin sorryAxName
  if n == sa then pure (.notImplemented "use of the sorryAx axiom")
  else do
    let x ← readName n
    pure (.invalid s!"unknown constant {x}")

/-! ## The record of mutually recursive entry points -/

/-- con-leche: ConLeche/Kernel/Core.lean:98-124 CoreFns — the record of
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

/-- con-leche: ConLeche/Kernel/Core.lean:126-132 CoreFns.ioView — the
**io-grade view** of a core record: the record whose full-grade `infer`
slot is the io slot, so a body written against `r.infer` recurses at the io
grade when handed `r.ioView`. -/
def CoreFnsA.ioView (r : CoreFnsA) : CoreFnsA :=
  { r with infer := r.inferIO }

/-! ## The bodies' small helpers -/

/-- con-leche: ConLeche/Kernel/Core.lean:145-148 liftFueled — lift a
fuel-style partial result; `none` is an internal error. -/
def liftFueled {α : Type} (what : String) : Option α → AM α
  | some a => pure a
  | none => fail (.internal s!"fuel exhausted: {what}")

/-- con-leche: ConLeche/Kernel/Core.lean:150-153 projModelName — the
model-side name of field `i`'s projection for `T`. -/
def projModelName (T : NIdx) (i : Nat) : AM NIdx := do
  let m ← internNNode (.str T "_model")
  internNNode (.str m ("proj_" ++ toString i))

/-- con-leche: ConLeche/Kernel/Core.lean:155-162 isCtorApp — is the
expression headed by a stored constructor? -/
def isCtorApp (fe : IFEnv) (e : EIdx) : AM Bool := do
  match ← view (← getAppFn coreWalkFuel e) with
  | .const c _ =>
    match fe.find? c with
    | some (.ctorInfo _ _ _) => pure true
    | _ => pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:164-171 piResultIsProp — does the
syntactic pi telescope end in a (normalized) `Prop`? -/
def piResultIsProp (e : EIdx) : AM Bool := do
  match ← view (← piResult coreWalkFuel e) with
  | .sort u => do
    let z ← zeroLevel
    pure ((← lvlEq? u z) == some true)
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:173-181 piResultZ — **the
result-sort zero-ness datum of an inductive's type** (`IndCaps.sortZ`). -/
def piResultZ (e : EIdx) : AM PropWhen := do
  match ← view (← piResult coreWalkFuel e) with
  | .sort u => do
    let l ← readLevel u
    pure (Level.zeronessOf l)
  | _ => pure (.ifAllZero [])

/-- con-leche: ConLeche/Kernel/Core.lean:183-191 piResultNeverZero — is the
result sort of a stored inductive's type, instantiated at the given levels,
provably nonzero (official `is_never_zero`)? -/
def piResultNeverZero (lps : List NIdx) (us : LsIdx) (e : EIdx) : AM Bool := do
  match ← view (← piResult coreWalkFuel e) with
  | .sort u => do
    let ks ← readNames lps
    let vs ← readLevels us
    let l ← readLevel u
    pure (Level.subst ks vs l).isNeverZero
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:193-204 capsNeverZero — the same
question read off the STORED datum, which is what the checker runs. -/
def capsNeverZero (lps : List NIdx) (us : LsIdx) (caps : IIndCaps) :
    AM Bool := do
  let ks ← readNames lps
  let vs ← readLevels us
  pure (Level.substPW ks vs caps.sortZ).isNever

/-- con-leche: ConLeche/Kernel/Core.lean:206-243 isUnitLikeTy — is this
(whnf'd) type expression a unit-like inductive type?  con-leche's task #161
item C1: the head-name comparison against `PUnit` comes FIRST and
short-circuits after one comparison at every other head. -/
def isUnitLikeTy (fe : IFEnv) (h : EIdx) : AM Bool := do
  match ← view h with
  | .const c _ => do
    let pu ← pin punitName
    if c != pu then pure false
    else
      match fe.find? pu with
      | some (.indInfo _ _) => do
        let pr ← pin punitRecName
        match fe.find? pr with
        | some (.recInfo _ mI rP [r]) => pure (mI == rP && r.nfields == 0)
        | _ => pure false
      | _ => pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:245-264 unfoldDefinition — unfold
the (application of a) definition at the head, one step.  The stored value
is instantiated through `constValAt`, so a constant unfolded twice at the
same levels pays the substitution once. -/
def unfoldDefinition (fe : IFEnv) (e : EIdx) : AM (Option EIdx) := do
  match ← view (← getAppFn coreWalkFuel e) with
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

/-- con-leche: ConLeche/Kernel/Core.lean:266-279 unfoldableHead — may the
delta step unfold `e`'s head (the official kernel's `is_delta`)?  The
DECISION, taken before the unfolding is materialized. -/
def unfoldableHead (fe : IFEnv) (e : EIdx) : AM Bool := do
  match ← view (← getAppFn coreWalkFuel e) with
  | .const n us =>
    match fe.find? n with
    | some (.defnInfo cv _ _) => do
      let usl ← viewLs us
      pure (usl.length == cv.levelParams.length)
    | _ => pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:281-290 headHint — the
reducibility hint of the constant at the head of `e`. -/
def headHint (fe : IFEnv) (e : EIdx) : AM ReducibilityHint := do
  match ← view (← getAppFn coreWalkFuel e) with
  | .const n _ =>
    match fe.find? n with
    | some (.defnInfo _ _ hint) => pure hint
    | _ => pure .opaque
  | _ => pure .opaque

/-- con-leche: ConLeche/Kernel/Core.lean:292-301 sameConstHeads — are `a`
and `b` applications of the *same* constant (the lazy delta same-head
short-circuit)?  Both sides must actually be applications. -/
def sameConstHeads (a b : EIdx) : AM Bool := do
  match ← view a with
  | .app f₁ _ =>
    match ← view b with
    | .app f₂ _ => do
      match ← view (← getAppFn coreWalkFuel f₁) with
      | .const n₁ _ =>
        match ← view (← getAppFn coreWalkFuel f₂) with
        | .const n₂ _ => pure (n₁ == n₂)
        | _ => pure false
      | _ => pure false
    | _ => pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:303-309 natLitToConstructor — the
constructor form of a `Nat` literal, one layer. -/
def natLitToConstructor (n : Nat) : AM EIdx := do
  match n with
  | 0 => do
    let z ← pin natZeroName
    constE z
  | k + 1 => do
    let s ← pin natSuccName
    let sc ← constE s
    let l ← internE (.lit (.natVal k))
    internE (.app sc l)

/-- con-leche: ConLeche/Kernel/Core.lean:311-315 natIndOk — the stored `Nat`
declaration has the expected shape. -/
def natIndOk : Option IConstantInfo → AM Bool
  | some (.indInfo cv _) => do
    let s1 ← sortOne
    pure (cv.levelParams.isEmpty && cv.type == s1)
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:317-321 natZeroOk — the stored
`Nat.zero` declaration has the expected shape. -/
def natZeroOk : Option IConstantInfo → AM Bool
  | some (.ctorInfo cv _ _) => do
    let nt ← pin natName
    let nc ← constE nt
    pure (cv.levelParams.isEmpty && cv.type == nc)
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:323-332 natSuccOk — the stored
`Nat.succ` declaration has the expected (annotated) shape. -/
def natSuccOk : Option IConstantInfo → AM Bool
  | some (.ctorInfo cv _ _) => do
    if !cv.levelParams.isEmpty then pure false else do
      let nt ← pin natName
      let nc ← constE nt
      match ← view cv.type with
      | .forallE dom body _mb => pure (dom == nc && body == nc)
      | _ => pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:334-342 natLitSupported
con-leche: ConLeche/Kernel/FEnv.lean:116-119 natLitSupportedF
Whether the environment supports `Nat` literals.  One twin for con-leche's
two spellings (deviation 1). -/
def natLitSupported (fe : IFEnv) : AM Bool := do
  let nt ← pin natName
  if !(← natIndOk (fe.find? nt)) then pure false else do
    let nz ← pin natZeroName
    if !(← natZeroOk (fe.find? nz)) then pure false else do
      let ns ← pin natSuccName
      natSuccOk (fe.find? ns)

/-- con-leche: ConLeche/Kernel/Core.lean:344-369 Expr.constsResolve — do all
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
      let nt ← pin natName
      let nz ← pin natZeroName
      let ns ← pin natSuccName
      pure ((fe.find? nt).isSome && (fe.find? nz).isSome &&
        (fe.find? ns).isSome)
    | .lit (.strVal _) => do
      let nt ← pin natName
      let nz ← pin natZeroName
      let ns ← pin natSuccName
      let st ← pin stringName
      let sl ← pin stringOfListName
      let li ← pin listName
      let ln ← pin listNilName
      let lc ← pin listConsName
      let ch ← pin charName
      let co ← pin charOfNatName
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

/-- con-leche: ConLeche/Kernel/Core.lean:371-376 litToCtorIfNat — convert a
`Nat`-literal major premise to constructor form, one layer. -/
def litToCtorIfNat (fe : IFEnv) (h : EIdx) : AM EIdx := do
  match ← view h with
  | .lit (.natVal n) => do
    if ← natLitSupported fe then natLitToConstructor n else pure h
  | _ => pure h

/-- con-leche: ConLeche/Kernel/Core.lean:378-383 rawNatLit? — a `Nat`
literal reading of a whnf'd expression (the official kernel's
`rawNatLitExt?`). -/
def rawNatLit? (h : EIdx) : AM (Option Nat) := do
  match ← view h with
  | .lit (.natVal n) => pure (some n)
  | .const c us => do
    let e ← emptyLevels
    let nz ← pin natZeroName
    pure (if c == nz && us == e then some 0 else none)
  | _ => pure none

/-! ## String literals -/

/-- con-leche: ConLeche/Kernel/Core.lean:397-408 strLitToConstructor — the
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

/-- con-leche: ConLeche/Kernel/Core.lean:397-408 strLitToConstructor — the
constructor form of a `String` literal: `String.ofList (List.cons.{0} Char
(Char.ofNat (lit c₁)) (… (List.nil.{0} Char)))`. -/
def strLitToConstructor (s : String) : AM EIdx := do
  let z ← zeroLevel
  let zs ← internLsNode [z]
  let chN ← pin charName
  let chC ← constE chN
  let lnN ← pin listNilName
  let ln ← internE (.const lnN zs)
  let nilE ← internE (.app ln chC)
  let lcN ← pin listConsName
  let lc ← internE (.const lcN zs)
  let cons ← internE (.app lc chC)
  let coN ← pin charOfNatName
  let ofNat ← constE coN
  let spine ← strLitConsSpine cons ofNat nilE s.toList
  let slN ← pin stringOfListName
  let sl ← constE slN
  internE (.app sl spine)

/-- con-leche: ConLeche/Kernel/Core.lean:410-416 stringTyOk — the stored
`String` declaration has the expected shape. -/
def stringTyOk : Option IConstantInfo → AM Bool
  | some ci => do
    let cv ← ci.toConstantVal
    let s1 ← sortOne
    pure (cv.levelParams.isEmpty && cv.type == s1)
  | none => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:418-424 charTyOk — the stored
`Char` declaration has the expected shape. -/
def charTyOk : Option IConstantInfo → AM Bool
  | some ci => do
    let cv ← ci.toConstantVal
    let s1 ← sortOne
    pure (cv.levelParams.isEmpty && cv.type == s1)
  | none => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:426-437 listTyOk — the stored
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
      match ← view cv.type with
      | .forallE d b _mb => pure (d == sort && b == sort)
      | _ => pure false
    | _ => pure false
  | none => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:439-450 listNilTyOk — the stored
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
      let li ← pin listName
      match ← view cv.type with
      | .forallE d b _mb => do
        if d != sort then pure false else
        match ← view b with
        | .app f a =>
          match ← view f with
          | .const l1 us1 =>
            match ← view a with
            | .bvar 0 => pure (l1 == li && us1 == ps)
            | _ => pure false
          | _ => pure false
        | _ => pure false
      | _ => pure false
    | _ => pure false
  | none => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:452-469 listConsTyOk — the stored
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
      let li ← pin listName
      let b0 ← internE (.bvar 0)
      let b1 ← internE (.bvar 1)
      let b2 ← internE (.bvar 2)
      let l1 ← internE (.const li ps)
      let dom3 ← internE (.app l1 b1)
      let cod3 ← internE (.app l1 b2)
      match ← view cv.type with
      | .forallE d1 r1 _mb1 => do
        if d1 != sort then pure false else
        match ← view r1 with
        | .forallE d2 r2 _mb2 => do
          if d2 != b0 then pure false else
          match ← view r2 with
          | .forallE d3 c3 _mb3 => pure (d3 == dom3 && c3 == cod3)
          | _ => pure false
        | _ => pure false
      | _ => pure false
    | _ => pure false
  | none => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:471-480 charOfNatTyOk — the stored
`Char.ofNat` declaration has the expected (annotated) shape `Nat → Char`. -/
def charOfNatTyOk : Option IConstantInfo → AM Bool
  | some ci => do
    let cv ← ci.toConstantVal
    if !cv.levelParams.isEmpty then pure false else do
      let nt ← pin natName
      let nc ← constE nt
      let ch ← pin charName
      let cc ← constE ch
      match ← view cv.type with
      | .forallE d b _mb => pure (d == nc && b == cc)
      | _ => pure false
  | none => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:482-492 stringOfListTyOk — the
stored `String.ofList` declaration has the expected (annotated) shape
`List.{0} Char → String`. -/
def stringOfListTyOk : Option IConstantInfo → AM Bool
  | some ci => do
    let cv ← ci.toConstantVal
    if !cv.levelParams.isEmpty then pure false else do
      let z ← zeroLevel
      let zs ← internLsNode [z]
      let li ← pin listName
      let lc ← internE (.const li zs)
      let ch ← pin charName
      let cc ← constE ch
      let dom ← internE (.app lc cc)
      let st ← pin stringName
      let sc ← constE st
      match ← view cv.type with
      | .forallE d b _mb => pure (d == dom && b == sc)
      | _ => pure false
  | none => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:494-512 strLitSupported
con-leche: ConLeche/Kernel/FEnv.lean:121-130 strLitSupportedF
Whether the environment supports `String` literals: the `Nat` literal guard
plus the seven string-support declarations at exactly the expected types. -/
def strLitSupported (fe : IFEnv) : AM Bool := do
  if !(← natLitSupported fe) then pure false else do
    let st ← pin stringName
    if !(← stringTyOk (fe.find? st)) then pure false else do
      let sl ← pin stringOfListName
      if !(← stringOfListTyOk (fe.find? sl)) then pure false else do
        let li ← pin listName
        if !(← listTyOk (fe.find? li)) then pure false else do
          let ln ← pin listNilName
          if !(← listNilTyOk (fe.find? ln)) then pure false else do
            let lc ← pin listConsName
            if !(← listConsTyOk (fe.find? lc)) then pure false else do
              let ch ← pin charName
              if !(← charTyOk (fe.find? ch)) then pure false else do
                let co ← pin charOfNatName
                charOfNatTyOk (fe.find? co)


/-! ## Structural-`Nat` literal acceleration

con-leche's certified fast path (`Core.lean:514-863`): an operation
participates only when its defining recurrence equations hold by
definitional equality — checked once, at install, so *presence in the store
is the certificate*.  The sixteen reserved names are interned here exactly
as the literal guards' are. -/

/-- con-leche: ConLeche/Kernel/Core.lean:544 natPredName -/
def natPredName : AM NIdx := pin (ConLeche.natName.str "pred")
/-- con-leche: ConLeche/Kernel/Core.lean:545 natAddName -/
def natAddName : AM NIdx := pin (ConLeche.natName.str "add")
/-- con-leche: ConLeche/Kernel/Core.lean:546 natSubName -/
def natSubName : AM NIdx := pin (ConLeche.natName.str "sub")
/-- con-leche: ConLeche/Kernel/Core.lean:547 natMulName -/
def natMulName : AM NIdx := pin (ConLeche.natName.str "mul")
/-- con-leche: ConLeche/Kernel/Core.lean:548 natPowName -/
def natPowName : AM NIdx := pin (ConLeche.natName.str "pow")
/-- con-leche: ConLeche/Kernel/Core.lean:549 natBeqName -/
def natBeqName : AM NIdx := pin (ConLeche.natName.str "beq")
/-- con-leche: ConLeche/Kernel/Core.lean:550 natBleName -/
def natBleName : AM NIdx := pin (ConLeche.natName.str "ble")
/-- con-leche: ConLeche/Kernel/Core.lean:551 natDivName -/
def natDivName : AM NIdx := pin (ConLeche.natName.str "div")
/-- con-leche: ConLeche/Kernel/Core.lean:552 natModName -/
def natModName : AM NIdx := pin (ConLeche.natName.str "mod")
/-- con-leche: ConLeche/Kernel/Core.lean:553 natGcdName -/
def natGcdName : AM NIdx := pin (ConLeche.natName.str "gcd")
/-- con-leche: ConLeche/Kernel/Core.lean:554 natLandName -/
def natLandName : AM NIdx := pin (ConLeche.natName.str "land")
/-- con-leche: ConLeche/Kernel/Core.lean:555 natLorName -/
def natLorName : AM NIdx := pin (ConLeche.natName.str "lor")
/-- con-leche: ConLeche/Kernel/Core.lean:556 natXorName -/
def natXorName : AM NIdx := pin (ConLeche.natName.str "xor")
/-- con-leche: ConLeche/Kernel/Core.lean:557 natShiftLeftName -/
def natShiftLeftName : AM NIdx := pin (ConLeche.natName.str "shiftLeft")
/-- con-leche: ConLeche/Kernel/Core.lean:558 natShiftRightName -/
def natShiftRightName : AM NIdx := pin (ConLeche.natName.str "shiftRight")
/-- con-leche: ConLeche/Kernel/Core.lean:559 boolName -/
def boolName : AM NIdx := pin (ConLeche.Name.anonymous.str "Bool")
/-- con-leche: ConLeche/Kernel/Core.lean:560 boolTrueName -/
def boolTrueName : AM NIdx := pin ((ConLeche.Name.anonymous.str "Bool").str "true")
/-- con-leche: ConLeche/Kernel/Core.lean:561 boolFalseName -/
def boolFalseName : AM NIdx := pin ((ConLeche.Name.anonymous.str "Bool").str "false")

/-- con-leche: ConLeche/Kernel/Core.lean:561-566 Expr.isBoolTrue — is `e` the
constant `Bool.true` (the official kernel's `is_constant(e, Bool.true)`):
the name, no universe levels. -/
def isBoolTrue (h : EIdx) : AM Bool := do
  match ← view h with
  | .const c us => do
    let el ← emptyLevels
    if us != el then pure false else do
      let bt ← boolTrueName
      pure (c == bt)
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:568-580 Expr.quickPair — the pairs
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

/-- con-leche: ConLeche/Kernel/Core.lean:582-590 natOpNames — the certified
structural-`Nat` operations. -/
def natOpNames : AM (List NIdx) := do
  let a ← natPredName; let b ← natAddName; let c ← natSubName
  let d ← natMulName; let e ← natPowName; let f ← natBeqName
  let g ← natBleName
  pure [a, b, c, d, e, f, g]

/-- con-leche: ConLeche/Kernel/Core.lean:592-607 natDivModNames — the
WF-recursive operations with a *pinned-declaration* certified fast path. -/
def natDivModNames : AM (List NIdx) := do
  let a ← natDivName; let b ← natModName; let c ← natGcdName
  let d ← natLandName; let e ← natLorName; let f ← natXorName
  let g ← natShiftLeftName; let h ← natShiftRightName
  pure [a, b, c, d, e, f, g, h]

/-- con-leche: ConLeche/Kernel/Core.lean:609-632 natOpDeps — the operations
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

/-- con-leche: ConLeche/Kernel/Core.lean:634-663 natOpEquations — `ap1 n a`,
one of the equation builder's three local lambdas.  DESIGN §3.4 forbids the
closure, so each is a named `def`. -/
def natAp1 (n : NIdx) (a : EIdx) : AM EIdx := do
  let f ← constE n
  internE (.app f a)

/-- con-leche: ConLeche/Kernel/Core.lean:634-663 natOpEquations — `ap2 n a b`. -/
def natAp2 (n : NIdx) (a b : EIdx) : AM EIdx := do
  let f ← natAp1 n a
  internE (.app f b)

/-- con-leche: ConLeche/Kernel/Core.lean:634-663 natOpEquations — the
defining recurrence equations of a structural-`Nat` operation, over
constructor forms with free variables `d`, `d + 1` (binder-free, so the
equation sides carry no annotations). -/
def natOpEquations (d : Nat) (c : NIdx) : AM (List (EIdx × EIdx)) := do
  let nN ← pin ConLeche.natName
  let natTy ← constE nN
  let x ← internE (.fvar d natTy)
  let y ← internE (.fvar (d + 1) natTy)
  let zN ← pin ConLeche.natZeroName
  let z ← constE zN
  let sN ← pin ConLeche.natSuccName
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

/-- con-leche: ConLeche/Kernel/Core.lean:665-691 natOpResult — the reduct of
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

/-- con-leche: ConLeche/Kernel/Core.lean:693-709 natOpGuard — the dependency
half of the guard.  con-leche writes `(natOpDeps c).all (fun n => …)`;
DESIGN §3.4's rule for a `List` walk is a named helper, so this is one. -/
def natOpDepsStored (fe : IFEnv) : List NIdx → AM Bool
  | [] => pure true
  | n :: ns =>
    match fe.find? n with
    | some (.defnInfo cv _ _) =>
      if cv.levelParams.isEmpty then natOpDepsStored fe ns else pure false
    | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:693-709 natOpGuard
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

/-- con-leche: ConLeche/Kernel/Core.lean:711-721 natOpWfNames — the
pin-certified WF-recursive `Nat` operations, as a *safety net*. -/
def natOpWfNames : AM (List NIdx) := do
  let a ← natDivName; let b ← natModName; let c ← natGcdName
  let d ← natLandName; let e ← natLorName; let f ← natXorName
  let g ← natShiftLeftName; let h ← natShiftRightName
  pure [a, b, c, d, e, f, g, h]

/-- con-leche: ConLeche/Kernel/Core.lean:723-729 Expr.substConst0 —
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

/-- con-leche: ConLeche/Kernel/Core.lean:731-747 Expr.substConstAll —
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

/-- con-leche: ConLeche/Kernel/Core.lean:749-759 natOpCod — the pinned
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
    let nn ← pin ConLeche.natName
    let nc ← constE nn
    pure (e == nc)

/-- con-leche: ConLeche/Kernel/Core.lean:761-776 natOpTyPinned — the pinned
type of a certified `Nat` operation: `Nat → Nat` for the unary `pred`,
`Nat → Nat → Nat` for the arithmetic operations, `Nat → Nat → Bool` for the
comparisons. -/
def natOpTyPinned (fe : IFEnv) (c : NIdx) (ty : EIdx) : AM Bool := do
  let nn ← pin ConLeche.natName
  let nc ← constE nn
  let pr ← natPredName
  if c == pr then do
    match ← view ty with
    | .forallE dom body _mb =>
      if dom == nc then natOpCod fe c body else pure false
    | _ => pure false
  else do
    match ← view ty with
    | .forallE dom rest _mb => do
      match ← view rest with
      | .forallE dom2 body _mb2 =>
        if dom == nc && dom2 == nc then natOpCod fe c body else pure false
      | _ => pure false
    | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:778-784 natOpStoredOk — op `n` is
stored as a level-monomorphic definition with the pinned type. -/
def natOpStoredOk (fe : IFEnv) (n : NIdx) : AM Bool := do
  match fe.find? n with
  | some (.defnInfo cv _ _) =>
    if cv.levelParams.isEmpty then natOpTyPinned fe n cv.type else pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:786-809 natOpStored
con-leche: ConLeche/Kernel/FEnv.lean:147-151 natOpStoredF
**The reduction-time test for a certified `Nat` operation** (con-leche's
task #161 item B3): is `c` stored as a definition at all?  The full
`natOpGuard` is carried by the install fold invariant. -/
def natOpStored (fe : IFEnv) (c : NIdx) : AM Bool := do
  match fe.find? c with
  | some (.defnInfo _ _ _) => pure true
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:811-863 reduceNat — the binary
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

/-- con-leche: ConLeche/Kernel/Core.lean:811-863 reduceNat — literal
acceleration (the official kernel's `reduceNat`, run in the `whnf` loop
*before* delta-unfolding).  The divergence audit's D15 is preserved: the
FIRST argument is head-normalised and, unless it is a literal, the step
fails WITHOUT touching the second. -/
def reduceNat (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e : EIdx) :
    AM (Option EIdx) := do
  match ← view e with
  | .app f b => do
    match ← view f with
    | .const c us => do
      -- con-leche's `.app (.const c []) a`: `b` is its `a`
      let el ← emptyLevels
      if us != el then pure none else do
        let ns ← pin ConLeche.natSuccName
        if c == ns && (← natLitSupported fe) then do
          match ← rawNatLit? (← r.whnf depth b) with
          | some n => do
            let x ← internE (.lit (.natVal (n + 1)))
            pure (some x)
          | none => pure none
        else pure none
    | .app g a => do
      -- con-leche's `.app (.app (.const c []) a) b`
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
                  let nm ← readName c
                  fail (.notImplemented
                    s!"native Nat computation on literals ({nm})")
                | none => pure none
              | none => pure none
            else pure none
      | _ => pure none
    | _ => pure none
  | _ => pure none


/-! ## The certification helpers

con-leche's `Core.lean`:865-1310.  Every one of these recurses structurally
on a LIST (an argument spine, a slot index list), so none of them takes
fuel; what they call into the store does. -/

/-- con-leche: ConLeche/Kernel/Core.lean:865-897 iotaCerts — certify a spine
against a recursor telescope: each argument's inferred type is defeq to the
corresponding (instantiated) domain.  **The ι-slot licence**: at a
*licensed* walk (`lic = true`) a slot whose ∀-binder datum is `.never` is
skipped. -/
def iotaCerts (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (lic : Bool) :
    EIdx → List EIdx → AM Bool
  | _, [] => pure true
  | h, arg :: rest => do
    match ← view h with
    | .forallE ty body mb =>
      if lic && mb.pw.isNever then do
        let b ← instantiate1Fast coreWalkFuel body arg 0
        iotaCerts r fe depth lic b rest
      else do
        -- con-leche's task #172 B4: the spine certificate's inference at
        -- the io grade
        let ta ← r.inferIO depth arg
        if ← r.defeq depth ta ty then do
          let b ← instantiate1Fast coreWalkFuel body arg 0
          iotaCerts r fe depth lic b rest
        else pure false
    | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:899-904 piResidual — peel a
∀-telescope along an argument list. -/
def piResidual : EIdx → List EIdx → AM (Option EIdx)
  | e, [] => pure (some e)
  | h, a :: as => do
    match ← view h with
    | .forallE _ b _ => do
      let b' ← instantiate1Fast coreWalkFuel b a 0
      piResidual b' as
    | _ => pure none

/-- con-leche: ConLeche/Kernel/Core.lean:906-915 defEqList — pairwise
definitional equality of two spines. -/
def defEqList (r : CoreFnsA) (fe : IFEnv) (depth : Nat) :
    List EIdx → List EIdx → AM Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if ← r.defeq depth a b then defEqList r fe depth as bs else pure false
  | _, _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:917-933 iotaIndexOk — the
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

/-- con-leche: ConLeche/Kernel/Core.lean:935-966 proofIrrel — proof
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
    match ← view (← r.whnf depth (← r.inferIO depth ta)) with
    | .sort uT => do
      let z ← zeroLevel
      let okA ← liftFueled "level comparison" (← lvlEq? uT z)
      let tb ← r.inferIO depth b
      match ← view (← r.whnf depth (← r.inferIO depth tb)) with
      | .sort vT => do
        let okB ← liftFueled "level comparison" (← lvlEq? vT z)
        pure (okA && okB)
      | _ => pure false
    | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:968-1010 propIrrel — **the hoisted
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
    match ← view (← r.whnf depth (← r.inferIO depth ta)) with
    | .sort uT => do
      let z ← zeroLevel
      let okA ← liftFueled "level comparison" (← lvlEq? uT z)
      let tb ← r.inferIO depth b
      match ← view (← r.whnf depth (← r.inferIO depth tb)) with
      | .sort vT => do
        let okB ← liftFueled "level comparison" (← lvlEq? vT z)
        pure (okA && okB)
      | _ => pure false
    | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:1012-1035 structEtaProjCerts — the
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

/-- con-leche: ConLeche/Kernel/Core.lean:1037-1042 towerSlotsAll — the slot
walk.  con-leche writes `(List.range nF).all fun j => …`; DESIGN §3.4's rule
turns the closure into a counted recursion. -/
def towerSlotsAllGo (fe : IFEnv) (T : NIdx) : Nat → Nat → AM Bool
  | 0, _ => pure true
  | n + 1, j => do
    if (← fe.findProj? T j).isSome then towerSlotsAllGo fe T n (j + 1)
    else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:1037-1042 towerSlotsAll
con-leche: ConLeche/Kernel/FEnv.lean:97-99 FEnv.towerSlotsAllF
Are all `nF` projection slots of `T` table entries? -/
def towerSlotsAll (fe : IFEnv) (T : NIdx) (nF : Nat) : AM Bool :=
  towerSlotsAllGo fe T nF 0

/-- con-leche: ConLeche/Kernel/Core.lean:1044-1052 recSlotsAll — the
projection-function slot walk, as a counted recursion. -/
def recSlotsAllGo (fe : IFEnv) (T : NIdx) : Nat → Nat → AM Bool
  | 0, _ => pure true
  | n + 1, j => do
    match fe.find? (← projFnName T j) with
    | some (.recInfo _ _ _ _) => recSlotsAllGo fe T n (j + 1)
    | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:1044-1052 recSlotsAll
con-leche: ConLeche/Kernel/FEnv.lean:105-110 FEnv.recSlotsAllF
Are all `nF` projection slots of `T` recursor-backed projection
functions? -/
def recSlotsAll (fe : IFEnv) (T : NIdx) (nF : Nat) : AM Bool :=
  recSlotsAllGo fe T nF 0

/-- con-leche: ConLeche/Kernel/Core.lean:1054-1064 etaProjs — the `.proj`
half of the fabricated projections, as a counted recursion. -/
def projNodesGo (T : NIdx) (b : EIdx) : Nat → Nat → AM (List EIdx)
  | 0, _ => pure []
  | n + 1, j => do
    let p ← internE (.proj T j b)
    let rest ← projNodesGo T b n (j + 1)
    pure (p :: rest)

/-- con-leche: ConLeche/Kernel/Core.lean:1054-1064 etaProjs — the
projection-function half, as a counted recursion. -/
def projAppsGo (T : NIdx) (us : LsIdx) (targs : List EIdx) (b : EIdx) :
    Nat → Nat → AM (List EIdx)
  | 0, _ => pure []
  | n + 1, j => do
    let f ← internE (.const (← projFnName T j) us)
    let p ← mkAppN f (targs ++ [b])
    let rest ← projAppsGo T us targs b n (j + 1)
    pure (p :: rest)

/-- con-leche: ConLeche/Kernel/Core.lean:1054-1064 etaProjs — the fabricated
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
  let a ← pin ConLeche.eqName
  let b ← pin ConLeche.eqReflName
  let c ← pin (ConLeche.eqName.str "rec")
  let d ← pin ConLeche.natName
  let e ← pin ConLeche.natZeroName
  let f ← pin ConLeche.natSuccName
  let g ← pin (ConLeche.natName.str "rec")
  let h ← pin ConLeche.punitName
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
  let t ← pin ConLeche.quotSoundName
  pure [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, s, t]

/-- con-leche: ConLeche/Kernel/Core.lean:1066-1138 structEtaCertWith — the
structure-eta certificate against a *given* weak-head-normal type of the
stuck side. -/
def structEtaCertWith (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv)
    (depth : Nat) (a b wtb : EIdx) : AM Bool := do
  match ← view (← getAppFn coreWalkFuel a) with
  | .const c us =>
    match fe.find? c with
    | some (.ctorInfo cvc cnP cnF) => do
      let aargs ← getAppArgs coreWalkFuel a
      if aargs.length = cnP + cnF then do
        match ← view (← getAppFn coreWalkFuel wtb) with
        | .const T us' =>
          match fe.find? T with
          | some (.indInfo cvT caps) => do
            let targs ← getAppArgs coreWalkFuel wtb
            let reserved ← reservedBasisNames
            let uslen ← viewLs us'
            let slots ←
              if ← towerSlotsAll fe T caps.etaFields then pure true
              else recSlotsAll fe T caps.etaFields
            if caps.eta = true ∧ caps.etaCtor = c ∧
                reserved.contains T = false ∧ reserved.contains c = false ∧
                targs.length = caps.etaParams ∧
                uslen.length = cvT.levelParams.length ∧
                cvc.levelParams = cvT.levelParams ∧ slots = true then do
              if ← liftFueled "level comparison" (← lvlsEq? us us') then do
                let tyT ← constTyAt cvT us'
                if ← iotaCerts r fe depth false tyT targs then do
                  -- the per-slot certificates are the projection-function
                  -- kind's; a tabled family has none
                  let percerts ←
                    if ← towerSlotsAll fe T caps.etaFields then pure true
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
    | _ => pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:1140-1151 etaCtorShape — the
constructor shape official's `try_eta_struct_core` tests before inferring
anything: the candidate's head is a stored constructor applied to exactly
its parameters and fields. -/
def etaCtorShape (fe : IFEnv) (a : EIdx) : AM Bool := do
  match ← view (← getAppFn coreWalkFuel a) with
  | .const c _ =>
    match fe.find? c with
    | some (.ctorInfo _ cnP cnF) => do
      let args ← getAppArgs coreWalkFuel a
      pure (args.length == cnP + cnF)
    | _ => pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:1153-1176 structEtaCert —
structural eta certification for a stored eta-capable structure.  The
constructor-shape test comes FIRST (the divergence audit's D13). -/
def structEtaCert (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv)
    (depth : Nat) (a b : EIdx) : AM Bool := do
  if ← etaCtorShape fe a then do
    let tb ← r.inferIO depth b
    let wtb ← r.whnf depth tb
    structEtaCertWith mode r fe depth a b wtb
  else pure false

/-- con-leche: ConLeche/Kernel/Core.lean:1178-1206 structUnitCert —
unit-likeness certification: `a` and `b` inhabit the same stored unit-like
family. -/
def structUnitCert (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    AM Bool := do
  let ta ← r.inferIO depth a
  let wta ← r.whnf depth ta
  match ← view (← getAppFn coreWalkFuel wta) with
  | .const T us' =>
    match fe.find? T with
    | some (.indInfo cvT caps) => do
      let targs ← getAppArgs coreWalkFuel wta
      let reserved ← reservedBasisNames
      let uslen ← viewLs us'
      if caps.unitlike = true ∧ reserved.contains T = false ∧
          targs.length = caps.unitParams ∧
          uslen.length = cvT.levelParams.length then do
        let tb ← r.inferIO depth b
        let wtb ← r.whnf depth tb
        if ← r.defeq depth wta wtb then do
          let tyT ← constTyAt cvT us'
          iotaCerts r fe depth false tyT targs
        else pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:1208-1233 etaCert — eta
certification for a one-sided λ against a stuck term `b`. -/
def etaCert (mode : CheckMode) (r : CoreFnsA) (_fe : IFEnv) (depth : Nat)
    (ty₁ body₁ : EIdx) (m₁ : BinderMeta) (b : EIdx) : AM Bool := do
  let tb ← r.inferIO depth b
  match ← view (← r.whnf depth tb) with
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

/-- con-leche: ConLeche/Kernel/Core.lean:1235-1245 stuckIrrel — the fallback
for structurally distinct stuck terms: structural eta in either direction,
unit-likeness, else proof irrelevance. -/
def stuckIrrel (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (a b : EIdx) : AM Bool := do
  if ← structEtaCert mode r fe depth a b then pure true
  else if ← structEtaCert mode r fe depth b a then pure true
  else if ← structUnitCert r fe depth a b then pure true
  else proofIrrel r fe depth a b

/-- con-leche: ConLeche/Kernel/Core.lean:1247-1255 etaFabArgs — the
eta-rescue fabrication's argument spine: the reduced type's arguments
followed by the installed projection functions applied to the stuck
major. -/
def etaFabArgs (T : NIdx) (ust : LsIdx) (targs : List EIdx) (major : EIdx)
    (nF : Nat) : AM (List EIdx) := do
  let ps ← projAppsGo T ust targs major nF 0
  pure (targs ++ ps)

/-- con-leche: ConLeche/Kernel/Core.lean:1257-1262 etaFabArgsE —
`etaFabArgs` at the entry kind: the projections are `etaProjs`'. -/
def etaFabArgsE (fe : IFEnv) (T : NIdx) (ust : LsIdx) (targs : List EIdx)
    (major : EIdx) (nF : Nat) : AM (List EIdx) := do
  let ps ← etaProjs fe T ust targs major nF
  pure (targs ++ ps)

/-- con-leche: ConLeche/Kernel/Core.lean:1264-1290 ProjEntry.fireOk — **the
tower-fire guard**: at a `Prop`-declared structure the field's guard level
must be a proposition at this instantiation; at every other family the rule
fires unconditionally. -/
def IProjEntry.fireOk (entry : IProjEntry) (us : LsIdx) : AM Bool := do
  let z ← zeroLevel
  if !((← lvlEq? entry.structSort z) == some true) then pure true
  else do
    let ks ← readNames entry.levelParams
    let vs ← readLevels us
    let fs ← readLevel entry.fieldSort
    pure (Level.isEquiv (Level.subst ks vs fs) .zero == some true)

/-- con-leche: ConLeche/Kernel/Core.lean:1292-1305 andRescueSlotsOf — the
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

/-- con-leche: ConLeche/Kernel/Core.lean:1292-1305 andRescueSlotsOf
con-leche: ConLeche/Kernel/Core.lean:1307-1309 andRescueSlots
con-leche: ConLeche/Kernel/FEnv.lean:101-103 FEnv.andRescueSlotsF
**The pinned `And`'s projection slots, ready to fire.**  One twin for
con-leche's three spellings (deviation 1). -/
def andRescueSlots (fe : IFEnv) (ctor : NIdx) (nP : Nat) (ust : LsIdx) :
    AM Bool := do
  let an ← pin ConLeche.andName
  andRescueSlotsGo fe an ctor nP ust 2 0


/-! ## The stuck-major rescue and the ι step

con-leche's `Core.lean`:1311-1832. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1311-1493 majorToCtor — the
fabrication's fvar-leaf containment, `fab.fvarLeaves.all (fun l =>
major.fvarLeaves.contains l)`, as a named recursion (DESIGN §3.4). -/
def fvarLeavesSubset : List (Nat × EIdx) → List (Nat × EIdx) → Bool
  | [], _ => true
  | l :: ls, ms => ms.contains l && fvarLeavesSubset ls ms

/-- con-leche: ConLeche/Kernel/Core.lean:1311-1493 majorToCtor — the scope
guard the three rescue branches share (cf. `annotateProjElim`): the
fabricated major is well-scoped, closed under loose bvars, and mentions no
free variable the stuck major does not. -/
def fabScopeOk (depth : Nat) (fab major : EIdx) : AM Bool := do
  if !(← wscopedB coreWalkFuel depth fab) then pure false
  else if !(← looseBVarsBoundedFast coreWalkFuel 0 fab) then pure false
  else do
    let fl ← fvarLeaves coreWalkFuel fab
    let ml ← fvarLeaves coreWalkFuel major
    pure (fvarLeavesSubset fl ml)

/-- con-leche: ConLeche/Kernel/Core.lean:1311-1493 majorToCtor — **the
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
      match ← view (← getAppFn coreWalkFuel (← piResult coreWalkFuel cvj.type)) with
      | .const T _ =>
        match fe.find? T with
        | some (.indInfo cvT caps) => do
          if rl.k = true then do
            -- io grade (lean4lean `toCtorWhenK`'s `inferType`)
            let tmaj ← r.whnf depth (← r.inferIO depth major)
            match ← view (← getAppFn coreWalkFuel tmaj) with
            | .const T' ust => do
              let ustl ← viewLs ust
              if T' = T ∧ cvj.levelParams.length = ustl.length then do
                let targs ← getAppArgs coreWalkFuel tmaj
                if cnP ≤ targs.length then do
                  let hd ← internE (.const rl.ctor ust)
                  let fab ← mkAppN hd (targs.take cnP)
                  if ← fabScopeOk depth fab major then do
                    -- synthetic-spine certification (con-leche's task #71)
                    let tyj ← constTyAt cvj ust
                    if ← iotaCerts r fe depth false tyj (targs.take cnP) then do
                      -- the official `to_cnstr_when_K` type check
                      if ← r.defeq depth tmaj (← r.inferIO depth fab) then do
                        if ← proofIrrel r fe depth fab major then pure fab
                        else pure major
                      else pure major
                    else pure major
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else if rl.eta = true then do
            let tmaj ← r.whnf depth (← r.inferIO depth major)
            match ← view (← getAppFn coreWalkFuel tmaj) with
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
                  let tyj ← constTyAt cvj ust
                  if ← iotaCerts r fe depth false tyj fabArgs then do
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
          else do
            let an ← pin ConLeche.andName
            if T = an then do
              -- THE `And`-ONLY η RESCUE (user ruling: `And` and nothing else)
              let tmaj ← r.whnf depth (← r.inferIO depth major)
              match ← view (← getAppFn coreWalkFuel tmaj) with
              | .const T' ust => do
                let ustl ← viewLs ust
                let targs ← getAppArgs coreWalkFuel tmaj
                let ars ← andRescueSlots fe rl.ctor cnP ust
                if T' = T ∧ targs.length = cnP ∧
                    cvj.levelParams.length = ustl.length ∧ ars = true then do
                  let p0 ← internE (.proj T 0 major)
                  let p1 ← internE (.proj T 1 major)
                  let fabArgs := targs ++ [p0, p1]
                  let hd ← internE (.const rl.ctor ust)
                  let fab ← mkAppN hd fabArgs
                  if ← fabScopeOk depth fab major then do
                    let tyj ← constTyAt cvj ust
                    if ← iotaCerts r fe depth false tyj fabArgs then do
                      if ← r.defeq depth tmaj (← r.inferIO depth fab) then do
                        if ← proofIrrel r fe depth fab major then pure fab
                        else pure major
                      else pure major
                    else pure major
                  else pure major
                else pure major
              | _ => pure major
            else pure major
        | _ => pure major
      | _ => pure major
    | _ => pure major
  | _ => pure major

/-- con-leche: ConLeche/Kernel/Core.lean:1495-1507 litMajorToCtor — convert a
literal major premise to constructor form: a `Nat` literal one layer, a
`String` literal to its *reduced* constructor form. -/
def litMajorToCtor (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (h : EIdx) :
    AM EIdx := do
  match ← view h with
  | .lit (.strVal s) => do
    if ← strLitSupported fe then do
      let c ← strLitToConstructor s
      r.whnf depth c
    else pure h
  | _ => litToCtorIfNat fe h

/-- con-leche: ConLeche/Kernel/Core.lean:1509-1523 projLitToCtor — convert a
string-literal projection scrutinee to its *reduced* constructor form. -/
def projLitToCtor (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (h : EIdx) :
    AM EIdx := do
  match ← view h with
  | .lit (.strVal s) => do
    if ← strLitSupported fe then do
      let c ← strLitToConstructor s
      r.whnf depth c
    else pure h
  | _ => pure h

/-- con-leche: ConLeche/Kernel/Core.lean:1525-1540 recRuleKOf — **the K bit
at install** (`RecRule.k`): the rule's constructor has no fields and belongs
to an inductive stored with the K capability. -/
def recRuleKOf (fe : IFEnv) (ctor : NIdx) : AM Bool := do
  match fe.find? ctor with
  | some (.ctorInfo cvj _ cnF) => do
    match ← view (← getAppFn coreWalkFuel (← piResult coreWalkFuel cvj.type)) with
    | .const T _ =>
      match fe.find? T with
      | some (.indInfo _ caps) => pure (caps.ruleK && cnF == 0)
      | _ => pure false
    | _ => pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:1542-1568 recRuleEtaOf — **the
η-rescue bit at install** (`RecRule.eta`).  `Name.isProjFnShape` is a
predicate on a `ConLeche.Name`, so the recursor's name is read back for it —
an install-time path, never a reduction-time one. -/
def recRuleEtaOf (fe : IFEnv) (recName ctor : NIdx) : AM Bool := do
  match fe.find? ctor with
  | some (.ctorInfo cvj _ _) => do
    match ← view (← getAppFn coreWalkFuel (← piResult coreWalkFuel cvj.type)) with
    | .const T _ =>
      match fe.find? T with
      | some (.indInfo cvT caps) => do
        let rn ← readName recName
        pure (caps.eta && caps.etaCtor == ctor && !Name.isProjFnShape rn &&
          cvj.levelParams == cvT.levelParams)
      | _ => pure false
    | _ => pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:1570-1580 recRuleBits — **stamp a
rule's two rescue bits at install** — the one place the K and η-rescue
conditions are decided. -/
def recRuleBits (fe : IFEnv) (recName : NIdx) (rl : IRecRule) : AM IRecRule := do
  let k ← recRuleKOf fe rl.ctor
  let eta ← recRuleEtaOf fe recName rl.ctor
  pure { rl with k := k, eta := eta }

/-- con-leche: ConLeche/Kernel/Core.lean:1619-1631 projFnRule — **the stored
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

/-- con-leche: ConLeche/Kernel/Core.lean:1649-1656 recRuleK — is a recursor
K-flagged?  The stored bit of its single rule; pure, as con-leche's is. -/
def recRuleK (rules : List IRecRule) : Bool :=
  match rules with
  | [rl] => rl.k
  | _ => false

/-- con-leche: ConLeche/Kernel/Core.lean:1658-1695 prepareMajor — the major
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

/-- con-leche: ConLeche/Kernel/Core.lean:1697-1717 recFireComparands — the
nested rule's stored level comparands, substituted and re-interned
(`lvls.map (Level.subst lps us)` as a named recursion). -/
def substLevelsAt (ks : List ConLeche.Name) (vs : List Level) :
    List LIdx → AM (List LIdx)
  | [] => pure []
  | u :: us => do
    let l ← readLevel u
    let h ← internLevel (Level.subst ks vs l)
    let rest ← substLevelsAt ks vs us
    pure (h :: rest)

/-- con-leche: ConLeche/Kernel/Core.lean:1697-1717 recFireComparands — the
canonical rule's level comparands, `cvjLps.map fun p => Level.subst lps us
(.param p)`, as a named recursion. -/
def substParamLevels (ks : List ConLeche.Name) (vs : List Level) :
    List NIdx → AM (List LIdx)
  | [] => pure []
  | p :: ps => do
    let pn ← readName p
    let h ← internLevel (Level.subst ks vs (.param pn))
    let rest ← substParamLevels ks vs ps
    pure (h :: rest)

/-- con-leche: ConLeche/Kernel/Core.lean:1697-1717 recFireComparands — the
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

/-- con-leche: ConLeche/Kernel/Core.lean:1697-1717 recFireComparands — the
level and constructor-parameter comparands a firing rule's checks compare the
major's constructor levels and parameters against. -/
def recFireComparands (rl : IRecRule) (lps : List NIdx) (us : LsIdx)
    (cvjLps : List NIdx) (args : List EIdx) (rP : Nat) :
    AM (LsIdx × List EIdx) := do
  match rl.fire with
  | .nested lvls pins => do
    let ks ← readNames lps
    let vs ← readLevels us
    let ls ← substLevelsAt ks vs lvls
    let lsh ← internLsNode ls
    let ps ← instSpinePins lps us args rP pins
    pure (lsh, ps)
  | _ => do
    let ks ← readNames lps
    let vs ← readLevels us
    let ls ← substParamLevels ks vs cvjLps
    let lsh ← internLsNode ls
    pure (lsh, args.take rl.ctorParams)

/-- con-leche: ConLeche/Kernel/Core.lean:1719-1832 iotaRec — the rule lookup
`rules.find? (fun r' => r'.ctor == cj)`, as a named recursion (DESIGN
§3.4). -/
def findRule : List IRecRule → NIdx → Option IRecRule
  | [], _ => none
  | rl :: rs, c => if rl.ctor == c then some rl else findRule rs c

/-- con-leche: ConLeche/Kernel/Core.lean:1719-1832 iotaRec — **one iota
step**: the expression is a stored recursor applied to exactly its telescope,
the major premise whnfs to a fully applied constructor with a matching rule,
and the spine is certified against the recursor's own (pinned, annotated)
type. -/
def iotaRec (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (e : EIdx) : AM (Option EIdx) := do
  match ← view (← getAppFn coreWalkFuel e) with
  | .const c us =>
    match fe.find? c with
    | some (.recInfo cv mI rP rules) => do
      let args ← getAppArgs coreWalkFuel e
      let usl ← viewLs us
      -- checker change #9: the recursor's level arity, guarded as
      -- `unfoldDefinition` guards it
      if args.length = mI + 1 ∧ usl.length = cv.levelParams.length then do
        let b0 ← internE (.bvar 0)
        let major ← prepareMajor mode r fe depth c rules (args.getD mI b0)
        match ← view (← getAppFn coreWalkFuel major) with
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
                    let pOk ←
                      if rl.compareParams then
                        defEqList r fe depth (margs.take rl.ctorParams) cmp.2
                      else pure true
                    if pOk then do
                      -- the two telescope runs, *licensed*
                      let tyR ← constTyAt cv us
                      if ← iotaCerts r fe depth mode.betaGate tyR
                          (args.take mI ++ [major]) then do
                        let tyC ← constTyAt cvj usj
                        if ← iotaCerts r fe depth mode.betaGate tyC margs then do
                          if ← iotaIndexOk r fe depth mI rP rl.ctorParams tyC
                              margs ((args.take mI).drop rP) then do
                            let rhs ← ruleRhsAt c rl.ctor cv.levelParams rl.rhs us
                            let x ← mkAppN rhs
                              (args.take rP ++ margs.drop rl.ctorParams)
                            pure (some x)
                          else pure none
                        else pure none
                      else pure none
                    else pure none
                  else pure none
              else pure none
            | none => pure none
          | _ => pure none
        | _ => pure none
      else pure none
    | _ => pure none
  | _ => pure none


/-! ## The projection certificate and the reduction bodies

con-leche's `Core.lean`:1834-2074. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1834-1843 ProjEntry.typeAt — **the
type of a `.proj` node at a tower-backed entry**: the stored body,
level-instantiated at the subject type's levels, with the subject type's
arguments and the subject substituted for its `numParams + 1` loose
variables in ONE traversal. -/
def IProjEntry.typeAt (entry : IProjEntry) (us : LsIdx) (targs : List EIdx)
    (pe : EIdx) : AM EIdx := do
  let b ← instLPFast coreWalkFuel entry.levelParams us entry.body
  instantiateListFast coreWalkFuel b (pe :: targs.reverse) 0

/-- con-leche: ConLeche/Kernel/Core.lean:1845-1880 projCert — **the
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

/-- con-leche: ConLeche/Kernel/Core.lean:1882-1894 projCertAt — **the fire
certificate as the mode runs it**: the P core certifies the constructor
spine; the parity core is the official kernel's, which certifies nothing. -/
def projCertAt (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (verified lic : Bool)
    (c : NIdx) (us : LsIdx) (args : List EIdx) : AM Bool :=
  if verified then projCert r fe depth lic c us args else pure true

/-- con-leche: ConLeche/Kernel/Core.lean:1896-1928 betaGateFires — **THE β
SITE'S GATE**: at `mode.betaGate` a λ-binder whose *validated* annotation
datum is `.never` licenses skipping the certificate.  Mode-and-datum only,
so it is decidable before the certificate would have started. -/
@[inline] def betaGateFires (mode : CheckMode) (pw : PropWhen) : Bool :=
  mode.betaGate && pw.isNever

/-- con-leche: ConLeche/Kernel/Core.lean:1930-2019 whnfCoreBody — the
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
    | .app f a => do
      let f' ← r.whnfCore depth f
      match ← view f' with
      | .lam ty body mb => do
        if betaGateFires mode mb.pw then do
          let b ← instantiate1Fast coreWalkFuel body a 0
          r.whnfCore depth b
        else do
          -- con-leche's task #172 B4: the certificate's inference runs at
          -- the io grade
          let ta ← r.inferIO depth a
          if ← r.defeq depth ta ty then do
            let b ← instantiate1Fast coreWalkFuel body a 0
            r.whnfCore depth b
          else internE (.app f' a)
      | _ => do
        let ap ← internE (.app f' a)
        match ← iotaRec mode r fe depth ap with
        | some e'' => r.whnfCore depth e''
        | none => pure ap
    | .proj sn i pe => do
      let e0 ← r.whnf depth pe
      -- a string-literal scrutinee first expands to its reduced
      -- constructor form
      let e' ← projLitToCtor r fe depth e0
      match ← fe.findProj? sn i with
      | some entry => do
        match ← view (← getAppFn coreWalkFuel e') with
        | .const c us => do
          let args ← getAppArgs coreWalkFuel e'
          let usl ← viewLs us
          let fok ← entry.fireOk us
          if c = entry.ctor ∧ i < entry.numFields ∧
              args.length = entry.numParams + entry.numFields ∧
              usl.length = entry.levelParams.length ∧ fok = true then do
            let b0 ← internE (.bvar 0)
            let arg := args.getD (entry.numParams + i) b0
            if ← projCertAt r fe depth mode.verifiedChecks mode.betaGate c us
                args then
              r.whnfCore depth arg
            else internE (.proj sn i e')
          else internE (.proj sn i e')
        | _ => internE (.proj sn i e')
      | none => internE (.proj sn i e')
    | .letE _ _ _ =>
      -- **Unreachable by construction** (con-leche's task #241): annotate
      -- output is let-free
      fail (.internal "whnfCore: `let` in an annotated expression")
    | .bvar _ =>
      fail (.notImplemented "whnf beyond the supported fragment")

/-- con-leche: ConLeche/Kernel/Core.lean:2021-2029 whnfCoreLoopFuel — step
budget of the `whnfCore` head-normalization loop.  The arena's
`whnfCoreBody` is con-leche's SPEC shape — beta, iota and projection steps
chained through the knot, not iterated in a local loop — so this budget has
no reader here yet; it is twinned because the executed loop
(`Cached/CoreC.lean`'s `whnfCoreLoopI`) is what P2g will measure against,
and its budget must be the same number. -/
def whnfCoreLoopFuel : Nat := 1000000

/-- con-leche: ConLeche/Kernel/Core.lean:2031-2038 whnfLoopFuel — step budget
of the `whnf` reduction loop (lean4lean's `FuelConfig.whnf`, same value).
Literal-acceleration and delta steps are *iteration*, not recursion. -/
def whnfLoopFuel : Nat := 100000

/-- con-leche: ConLeche/Kernel/Core.lean:2040-2055 whnfStep — one iteration
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

/-- con-leche: ConLeche/Kernel/Core.lean:2057-2062 whnfLoop — the reduction
loop: iterate `whnfStep` on its own step budget, so the whole chain costs one
knot level however many steps it takes. -/
def whnfLoop (r : CoreFnsA) (fe : IFEnv) (depth : Nat) : Nat → EIdx → AM EIdx
  | 0, _ => fail (.internal "fuel exhausted: whnf loop")
  | n + 1, e => whnfStep r fe depth (whnfLoop r fe depth n) e

/-- con-leche: ConLeche/Kernel/Core.lean:2064-2066 whnfBody — the reduction
loop's body: run `whnfLoop` at its own step budget. -/
def whnfBody (r : CoreFnsA) (fe : IFEnv) : Nat → EIdx → AM EIdx :=
  fun depth e => whnfLoop r fe depth whnfLoopFuel e

/-- con-leche: ConLeche/Kernel/Core.lean:2068-2074 ensureSort — ensure `e`
(the type of some expression) is a sort, returning its level. -/
def ensureSort (r : CoreFnsA) (_fe : IFEnv) (depth : Nat) (e : EIdx) :
    AM LIdx := do
  match ← view (← r.whnf depth e) with
  | .sort u => pure u
  | _ => fail (.invalid "expected a sort")

/-- con-leche: ConLeche/Kernel/Core.lean:2076-2241 inferBody — the λ clause's
result, `.forallE ty (bt.abstract1 depth) mb`.  con-leche writes it once at
the end of a clause with three exits; the arena names it, so the three exits
share one spelling and no arm is duplicated (DESIGN §8.4's Rust shape). -/
def inferLamResult (ty bt : EIdx) (depth : Nat) (mb : BinderMeta) : AM EIdx := do
  let ab ← abstract1Fast coreWalkFuel bt depth 0
  internE (.forallE ty ab mb)

/-- con-leche: ConLeche/Kernel/Core.lean:2076-2241 inferBody — the inference
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
          let x ← readName n
          fail (.invalid s!"projection table entry used as a constant {x}")
        else do
          let cv ← ci.toConstantVal
          let usl ← viewLs us
          if usl.length != cv.levelParams.length then do
            let x ← readName n
            fail (.invalid s!"incorrect number of universe levels for {x}")
          else constTyAt cv us
    | .lit (.natVal _) => do
      if ← natLitSupported fe then do
        let nn ← pin ConLeche.natName
        constE nn
      else fail (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      if ← strLitSupported fe then do
        let sn ← pin ConLeche.stringName
        constE sn
      else fail (.notImplemented
        "string literals before the String support declarations")
    | .forallE ty body mb => do
      match ← view (← r.whnf depth (← r.infer depth ty)) with
      | .sort u => do
        let fv ← internE (.fvar depth ty)
        let ob ← instantiate1Fast coreWalkFuel body fv 0
        let v ← ensureSort r fe (depth + 1) (← r.infer (depth + 1) ob)
        let ok ←
          if mode.verifiedChecks then do
            let lv ← readLevel v
            pure (Level.zeronessOf lv == mb.pw)
          else pure true
        if !ok then
          fail (.notImplemented "sort-annotation mismatch (forall-cod)")
        else do
          let iu ← internLNode (.imax u v)
          internE (.sort iu)
      | _ => fail (.invalid "expected a sort")
    | .lam ty body mb => do
      match ← view (← r.whnf depth (← r.infer depth ty)) with
      | .sort _ => do
        let fv ← internE (.fvar depth ty)
        let ob ← instantiate1Fast coreWalkFuel body fv 0
        let bt ← r.infer (depth + 1) ob
        if mode.verifiedChecks then do
          match ← lamPw body with
          | some pwI =>
            -- con-leche's task #161 chain rule: datum equality with the
            -- neighbour, no inference
            if !(mb.pw == pwI) then
              fail (.notImplemented "sort-annotation mismatch (lam-cod-chain)")
            else inferLamResult ty bt depth mb
          | none => do
            -- the innermost binder: the task-#152 codomain-sort computation
            let btt ← r.inferIO (depth + 1) bt
            let vb ← ensureSort r fe (depth + 1) btt
            let lvb ← readLevel vb
            if !(Level.zeronessOf lvb == mb.pw) then
              fail (.notImplemented "sort-annotation mismatch (lam-cod-leaf)")
            else inferLamResult ty bt depth mb
        else inferLamResult ty bt depth mb
      | _ => fail (.invalid "expected a sort")
    | .app f a => do
      let tf ← r.infer depth f
      match ← view (← r.whnf depth tf) with
      | .forallE ty body _mt => do
        -- per-argument re-check (con-leche's task #100 de-gating)
        let ta ← r.infer depth a
        if !(← r.defeq depth ta ty) then
          fail (.invalid "application type mismatch")
        else instantiate1Fast coreWalkFuel body a 0
      | _ => fail (.invalid "function expected")
    | .proj sn i pe => do
      let te ← r.whnf depth (← r.infer depth pe)
      match ← view (← getAppFn coreWalkFuel te) with
      | .const T us => do
        match ← fe.findProj? T i with
        | some entry => do
          let targs ← getAppArgs coreWalkFuel te
          let usl ← viewLs us
          -- con-leche's task #175 wiring W5: the node's struct name must be
          -- the subject type's head
          if T = sn ∧ targs.length = entry.numParams ∧
              usl.length = entry.levelParams.length then do
            let z ← zeroLevel
            if (← lvlEq? entry.structSort z) == some true then do
              let ks ← readNames entry.levelParams
              let vs ← readLevels us
              let fs ← readLevel entry.fieldSort
              if !(Level.isEquiv (Level.subst ks vs fs) .zero == some true) then
                fail (.invalid
                  "projection from a propositional structure must be a proposition")
              else entry.typeAt us targs pe
            else entry.typeAt us targs pe
          else fail (.notImplemented "projection without a native entry")
        | none => fail (.notImplemented "projection without a native entry")
      | _ => fail (.notImplemented "projection without a native entry")
    | .letE _ _ _ =>
      fail (.internal "inferType: `let` in an annotated expression")
    | .bvar _ =>
      fail (.notImplemented "inferType beyond the supported fragment")

/-- con-leche: ConLeche/Kernel/Core.lean:2243-2371 inferBodyIO — **the io
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
          let x ← readName n
          fail (.invalid s!"projection table entry used as a constant {x}")
        else do
          let cv ← ci.toConstantVal
          let usl ← viewLs us
          if usl.length != cv.levelParams.length then do
            let x ← readName n
            fail (.invalid s!"incorrect number of universe levels for {x}")
          else constTyAt cv us
    | .lit (.natVal _) => do
      if ← natLitSupported fe then do
        let nn ← pin ConLeche.natName
        constE nn
      else fail (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      if ← strLitSupported fe then do
        let sn ← pin ConLeche.stringName
        constE sn
      else fail (.notImplemented
        "string literals before the String support declarations")
    | .forallE ty body mb => do
      match ← view (← r.whnf depth (← r.infer depth ty)) with
      | .sort u => do
        let fv ← internE (.fvar depth ty)
        let ob ← instantiate1Fast coreWalkFuel body fv 0
        let v ← ensureSort r fe (depth + 1) (← r.infer (depth + 1) ob)
        let ok ←
          if mode.verifiedChecks then do
            let lv ← readLevel v
            pure (Level.zeronessOf lv == mb.pw)
          else pure true
        if !ok then
          fail (.notImplemented "sort-annotation mismatch (forall-cod)")
        else do
          let iu ← internLNode (.imax u v)
          internE (.sort iu)
      | _ => fail (.invalid "expected a sort")
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
          let lvb ← readLevel vb
          if !(Level.zeronessOf lvb == mb.pw) then
            fail (.notImplemented "sort-annotation mismatch (lam-cod-leaf)")
          else inferLamResult ty bt depth mb
      else inferLamResult ty bt depth mb
    | .app f a => do
      let tf ← r.infer depth f
      match ← view (← r.whnf depth tf) with
      | .forallE ty body mt => do
        -- **THE io SITE.**  At a ∀ whose datum is `never` the certificate is
        -- dead weight; the read is the DATUM ALONE (the licence ruling of
        -- 2026-09-06), never the mode.
        if !mt.pw.isNever then do
          let ta ← r.infer depth a
          if !(← r.defeq depth ta ty) then
            fail (.invalid "application type mismatch")
          else instantiate1Fast coreWalkFuel body a 0
        else instantiate1Fast coreWalkFuel body a 0
      | _ => fail (.invalid "function expected")
    | .proj sn i pe => do
      let te ← r.whnf depth (← r.infer depth pe)
      match ← view (← getAppFn coreWalkFuel te) with
      | .const T us => do
        match ← fe.findProj? T i with
        | some entry => do
          let targs ← getAppArgs coreWalkFuel te
          let usl ← viewLs us
          if T = sn ∧ targs.length = entry.numParams ∧
              usl.length = entry.levelParams.length then do
            let z ← zeroLevel
            if (← lvlEq? entry.structSort z) == some true then do
              let ks ← readNames entry.levelParams
              let vs ← readLevels us
              let fs ← readLevel entry.fieldSort
              if !(Level.isEquiv (Level.subst ks vs fs) .zero == some true) then
                fail (.invalid
                  "projection from a propositional structure must be a proposition")
              else entry.typeAt us targs pe
            else entry.typeAt us targs pe
          else fail (.notImplemented "projection without a native entry")
        | none => fail (.notImplemented "projection without a native entry")
      | _ => fail (.notImplemented "projection without a native entry")
    | .letE _ _ _ =>
      fail (.internal "inferType: `let` in an annotated expression")
    | .bvar _ =>
      fail (.notImplemented "inferType beyond the supported fragment")


/-! ## Definitional equality

con-leche's `Core.lean`:2373-2697. -/

/-- con-leche: ConLeche/Kernel/Core.lean:2373-2385 boolTrueShortcut — **the
eq-true shortcut** (the divergence audit's E2): the left side is fully
head-normalised and the verdict is `true` iff the reduct is `Bool.true`. -/
def boolTrueShortcut (r : CoreFnsA) (depth : Nat) (a : EIdx) : AM Bool := do
  let w ← r.whnf depth a
  isBoolTrue w

/-- con-leche: ConLeche/Kernel/Core.lean:2387-2406 defeqSpine —
levels-and-spine congruence for two applications of the *same* stored
constant (the lazy delta same-head short-circuit, official's
`try_eq_const_app`). -/
def defeqSpine (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    AM Bool := do
  match ← view (← getAppFn coreWalkFuel a) with
  | .const n us =>
    match ← view (← getAppFn coreWalkFuel b) with
    | .const n' us' => do
      let aa ← getAppArgs coreWalkFuel a
      let bb ← getAppArgs coreWalkFuel b
      if n = n' ∧ aa.length = bb.length then
        match ← lvlsEq? us us' with
        | some true => defEqList r fe depth aa bb
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- con-leche: ConLeche/Kernel/Core.lean:2408-2668 defeqStep — the
literal-acceleration guard: *both* sides free of free variables, mirroring
the official kernel's `lazy_delta_reduction`.  The arena reads the `O(1)`
eager per-node fvar range where the specification walks. -/
def defeqNoFvars (a b : EIdx) : AM Bool := do
  if ← hasFvarFast coreWalkFuel a then pure false
  else do
    let y ← hasFvarFast coreWalkFuel b
    pure !y

/-- con-leche: ConLeche/Kernel/Core.lean:2408-2668 defeqStep — the
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
      let nz ← pin ConLeche.natZeroName
      if c = nz ∧ us = el then pure (n == 0)
      else stuckIrrel mode r fe depth a' b'
    | .const c us, .lit (.natVal n) => do
      let el ← emptyLevels
      let nz ← pin ConLeche.natZeroName
      if c = nz ∧ us = el then pure (n == 0)
      else stuckIrrel mode r fe depth a' b'
    | .lit (.natVal nn), .app f x => do
      match nn with
      | k' + 1 => do
        match ← view f with
        | .const c us => do
          let el ← emptyLevels
          let ns ← pin ConLeche.natSuccName
          if c = ns ∧ us = el then do
            let l ← internE (.lit (.natVal k'))
            r.defeq depth l x
          else stuckIrrel mode r fe depth a' b'
        | _ => stuckIrrel mode r fe depth a' b'
      | _ => stuckIrrel mode r fe depth a' b'
    | .app f x, .lit (.natVal nn) => do
      match nn with
      | k' + 1 => do
        match ← view f with
        | .const c us => do
          let el ← emptyLevels
          let ns ← pin ConLeche.natSuccName
          if c = ns ∧ us = el then do
            let l ← internE (.lit (.natVal k'))
            r.defeq depth x l
          else stuckIrrel mode r fe depth a' b'
        | _ => stuckIrrel mode r fe depth a' b'
      | _ => stuckIrrel mode r fe depth a' b'
    -- a string literal against a unary `String.ofList` application
    | .lit (.strVal st), .app fo _ => do
      match ← view fo with
      | .const cO usO => do
        let el ← emptyLevels
        let sl ← pin ConLeche.stringOfListName
        if cO = sl ∧ usO = el ∧ (← strLitSupported fe) then do
          let c ← strLitToConstructor st
          r.defeq depth c b'
        else stuckIrrel mode r fe depth a' b'
      | _ => stuckIrrel mode r fe depth a' b'
    | .app fo _, .lit (.strVal st) => do
      match ← view fo with
      | .const cO usO => do
        let el ← emptyLevels
        let sl ← pin ConLeche.stringOfListName
        if cO = sl ∧ usO = el ∧ (← strLitSupported fe) then do
          let c ← strLitToConstructor st
          r.defeq depth a' c
        else stuckIrrel mode r fe depth a' b'
      | _ => stuckIrrel mode r fe depth a' b'
    | .fvar i _, .fvar j _ =>
      if i == j then pure true else stuckIrrel mode r fe depth a' b'
    | .const n us, .const n' us' => do
      if n = n' then do
        if ← liftFueled "level comparison" (← lvlsEq? us us') then pure true
        else stuckIrrel mode r fe depth a' b'
      else stuckIrrel mode r fe depth a' b'
    | .forallE ty₁ body₁ m₁, .forallE ty₂ body₂ m₂ => do
      -- binder congruence; the annotation comparison runs LAST
      if !(← r.defeq depth ty₁ ty₂) then pure false else do
        let fv ← internE (.fvar depth ty₂)
        let o₁ ← instantiate1Fast coreWalkFuel body₁ fv 0
        let o₂ ← instantiate1Fast coreWalkFuel body₂ fv 0
        if !(← r.defeq (depth + 1) o₁ o₂) then pure false else do
          if mode.verifiedChecks && !(m₁.pw == m₂.pw) then
            fail (.notImplemented "sort-annotation mismatch (defeq-forall)")
          else pure true
    | .lam ty₁ body₁ m₁, .lam ty₂ body₂ m₂ => do
      if !(← r.defeq depth ty₁ ty₂) then pure false else do
        let fv ← internE (.fvar depth ty₂)
        let o₁ ← instantiate1Fast coreWalkFuel body₁ fv 0
        let o₂ ← instantiate1Fast coreWalkFuel body₂ fv 0
        if !(← r.defeq (depth + 1) o₁ o₂) then pure false else do
          if mode.verifiedChecks && !(m₁.pw == m₂.pw) then
            fail (.notImplemented "sort-annotation mismatch (defeq-lam)")
          else pure true
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

/-- con-leche: ConLeche/Kernel/Core.lean:2670-2675 defeqLoop — the lazy-delta
loop: iterate `defeqStep` on its own step budget. -/
def defeqLoop (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) :
    Nat → Bool → EIdx → EIdx → AM Bool
  | 0, _, _, _ => fail (.internal "fuel exhausted: defeq loop")
  | fl + 1, pi, a, b =>
    defeqStep mode r fe depth (defeqLoop mode r fe depth fl) pi a b

/-- con-leche: ConLeche/Kernel/Core.lean:2677-2681 defeqLoopFuel — step
budget of the lazy-delta loop (lean4lean's `FuelConfig.lazyDelta`).
Exhaustion is an internal error, never a verdict. -/
def defeqLoopFuel : Nat := 100000

/-- con-leche: ConLeche/Kernel/Core.lean:2683-2686 defeqBody — the
definitional-equality body: the lazy-delta loop at its own step budget. -/
def defeqBody (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) :
    Nat → EIdx → EIdx → AM Bool :=
  fun depth a b => defeqLoop mode r fe depth defeqLoopFuel true a b

/-- con-leche: ConLeche/Kernel/Core.lean:2688-2697 isPropType — check that a
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

/-- con-leche: ConLeche/Kernel/Core.lean:2713-2714 pwWritten — is this datum
a real (non-placeholder) input annotation? -/
@[inline] def pwWritten (pw : PropWhen) : Bool := !pw.isNever

/-- con-leche: ConLeche/Kernel/Core.lean:2716-2722 annotBinderMeta — the
datum a rebuilt binder ends up with: the one threaded in from the node below,
unless it carries a real input annotation. -/
def annotBinderMeta (pw? : Option PropWhen) (mb : BinderMeta) : BinderMeta :=
  match pw? with
  | some pw => if pwWritten mb.pw then mb else ⟨pw⟩
  | none => mb

/-- con-leche: ConLeche/Kernel/Core.lean:2724-2755 annotPwPi — the ∀ node's
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
    let lv ← readLevel v
    pure (Level.zeronessOf lv)

/-- con-leche: ConLeche/Kernel/Core.lean:2757-2771 annotPwLam — the λ node's
datum: the zero-ness of the sort of the *body's type*. -/
def annotPwLam (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (body' : EIdx) :
    AM PropWhen := do
  match ← proofPW fe coreWalkFuel body' with
  | some pw => pure pw
  | none => do
    let bt ← r.inferIO depth body'
    let vb ← ensureSort r fe depth (← r.inferIO depth bt)
    let lvb ← readLevel vb
    pure (Level.zeronessOf lvb)

/-- con-leche: ConLeche/Kernel/Core.lean:2773-2893 annotateBody — the
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
      -- structural (con-leche's task #100 stage 6)
      let f' ← r.annotate depth f
      let a' ← r.annotate depth a
      internE (.app f' a')
    | .forallE ty body mb => do
      let ty' ← r.annotate depth ty
      let fv ← internE (.fvar depth ty')
      let ob ← instantiate1Fast coreWalkFuel body fv 0
      let body' ← r.annotate (depth + 1) ob
      let pw ←
        if !pwWritten mb.pw then annotPwPi r fe (depth + 1) body'
        else pure mb.pw
      let ab ← abstract1Fast coreWalkFuel body' depth 0
      internE (.forallE ty' ab ⟨pw⟩)
    | .lam ty body mb => do
      let ty' ← r.annotate depth ty
      let fv ← internE (.fvar depth ty')
      let ob ← instantiate1Fast coreWalkFuel body fv 0
      let body' ← r.annotate (depth + 1) ob
      let pw ←
        if !pwWritten mb.pw then annotPwLam r fe (depth + 1) body'
        else pure mb.pw
      let ab ← abstract1Fast coreWalkFuel body' depth 0
      internE (.lam ty' ab ⟨pw⟩)
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
      match ← view (← getAppFn coreWalkFuel te) with
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

/-- con-leche: ConLeche/Cached/CoreC.lean:1892-1906 memoBI — record a `defeq`
verdict at the ORDERED pair, both signs (con-leche's `defeqC` stores the
`Bool` result `r`, which is what makes a negative memo sound). -/
@[noinline] def defeqSet (a b : EIdx) (r : Bool) : AM Unit := do
  let s ← get
  let mp := s.caches.defeqC
  let mp := if mp.size < cacheCap then mp else ∅
  let s := { s with caches := { s.caches with defeqC := ∅ } }
  set { s with caches := { s.caches with defeqC := mp.insert (a, b) r } }

/-- con-leche: ConLeche/Kernel/Core.lean:2897-2936 coreKnot
con-leche: ConLeche/Cached/CoreC.lean:1916-1979 coreKnotI
Tie the bodies together: the record whose entry points are the bodies applied
to the record one fuel level down, each under its own memo.  Fuel is *only*
here — exhaustion is an internal error, never a verdict — and the next level
is constructed lazily inside each entry point's closure.

**The io slot's selector is `mode.betaGate`**, con-leche's `Kernel/Core.lean`
spelling, not `Cached/CoreC.lean`'s `mode.ioGate`; the two agree at
`.verified`, which is the only mode the bridge is stated at.  The io body
runs under its own table (`inferIOC`), the full body under `inferC`: a hit in
one grade never serves the other (DESIGN §8.3, lesson 9). -/
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
          match (← get).caches.whnfCoreC[e]? with
          | some x => pure x
          | none => do
            let x ← whnfCoreBody mode (coreKnot mode fe wrap fuel) fe d e
            whnfCoreSet e x
            pure x
        whnf := fun d e => do
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
          if mode.betaGate then do
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

/-- con-leche: ConLeche/Kernel/Core.lean:2938-2941 checkFuel — the shared
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
@[noinline] def dropScratchEntries : AM Unit := do
  let s ← get
  let c := s.caches
  let s := { s with caches := Caches.empty }
  set { s with caches := c.dropScratchEntries }

/-- con-leche: none — **the per-declaration bracket, closed**: drop the
scratch tier of the store and the cache entries that name it, in one
operation, so the two halves cannot drift apart. -/
@[noinline] def dropScratch : AM Unit := do
  dropScratchEntries
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

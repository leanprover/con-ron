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

end ConRon.Arena

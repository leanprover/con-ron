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

end ConRon.Arena

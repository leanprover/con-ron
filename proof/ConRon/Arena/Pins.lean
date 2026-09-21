/-
# `ConRon.Arena.Pins` — the reserved names, interned ONCE (task #97-P6-4a)

con-leche compares its reserved names — `natName`, `natZeroName`,
`natSuccName`, the sixteen `Nat`-operation names, the `Bool` trio, the
`String`/`List`/`Char` family, the standard and the trusted axiom names — as
`Name` VALUES, which Lean builds once per nullary `def` and caches.  The arena
compares them as HANDLES, so `Arena/Core.lean`'s `pin` turned each one into
`internName` of a freshly built `Name`: one cons-table probe per path segment,
every time.  Task #97-P6-1's counter measured what that costs on `Init`:
**140 083 646 `NStore.intern` calls, of which 88 854 033 are probes of a `str`
node built purely to be compared and dropped** — tens of millions of rebuilds
of about forty constants.

This module is DESIGN §8.3's answer, flagged at task #97c ("the `Pins` record
that is NOT here") and deferred there for want of a number: one record, filled
once at the driver by `internReservedPins`, and every `pin` of a reserved constant
name becomes a field read.

## The table is an `Array`, and that is what kills task #97c's hazard

Task #97c declined the record because of an initialisation-order hazard: "a
pin read before it is filled compares against the zero word and silently says
*not `Nat`*".  A record of handle FIELDS has that hazard, because every 32-bit
word is a syntactically valid handle.  An `Array NIdx` does not: before
`internReservedPins` runs the table is EMPTY, so `pinAt` takes its bounds branch and
raises `.internal` — a loud stop, never a quiet wrong answer.

## What is pinned

The forty-nine names below and `reservedBasisNames`' nineteen, plus the three
interned values every `pin` site around them needs: the empty
universe-argument list, the level `0` and the expression `Sort 1`
(`Arena/Core.lean`'s `emptyLevels`, `zeroLevel` and `sortOne`, which now read
this record instead of interning).

All of them go into the PERSISTENT tier, because `internReservedPins` runs before
the parse, while the scratch tier is closed.  That matters twice: a pinned
handle must survive every `dropScratch` (it is read across all of them), and
the "a persistent node's children are persistent" clause of `StoreWF` gets the
bottom-up intern of a closed scratch tier for free.

**Denotation unchanged.**  A pin is `internName` of the same `Name`, so the
handle this record holds is the handle `pin` computed before — `denoteN` is
injective and `intern` is idempotent, so pre-interning a name the export also
carries hands the export's parse the very same handle.  What changes is only
WHEN the intern happens, and how many times.  The one obligation the bridge
owes is an instance of `intern_spec`:

    pinsOK st → st.pins.names[PIN_NAT] = (internName st natName).1
-/
import ConRon.Arena.Monad
import ConLeche.Kernel.Basis.Names
import ConLeche.Kernel.StdAxioms
import ConLeche.Kernel.TrustAxioms

namespace ConRon.Arena

open ConLeche

/-! ## The slots -/

/-- con-leche: none — the arena's own pin table; the number of pinned names. -/
def pinCount : Nat := 49

/-- con-leche: none — the arena's own pin table; `eqName`'s slot. -/
def PIN_EQ : Nat := 0
/-- con-leche: none — the arena's own pin table; `punitName`'s slot. -/
def PIN_PUNIT : Nat := 1
/-- con-leche: none — the arena's own pin table; `PUnit.rec`'s slot. -/
def PIN_PUNIT_REC : Nat := 2
/-- con-leche: none — the arena's own pin table; `natName`'s slot. -/
def PIN_NAT : Nat := 3
/-- con-leche: none — the arena's own pin table; `natZeroName`'s slot. -/
def PIN_NAT_ZERO : Nat := 4
/-- con-leche: none — the arena's own pin table; `natSuccName`'s slot. -/
def PIN_NAT_SUCC : Nat := 5
/-- con-leche: none — the arena's own pin table; `Quot.sound`'s slot. -/
def PIN_QUOT_SOUND : Nat := 6
/-- con-leche: none — the arena's own pin table; `stringName`'s slot. -/
def PIN_STRING : Nat := 7
/-- con-leche: none — the arena's own pin table; `stringOfListName`'s slot. -/
def PIN_STRING_OF_LIST : Nat := 8
/-- con-leche: none — the arena's own pin table; `listName`'s slot. -/
def PIN_LIST : Nat := 9
/-- con-leche: none — the arena's own pin table; `listNilName`'s slot. -/
def PIN_LIST_NIL : Nat := 10
/-- con-leche: none — the arena's own pin table; `listConsName`'s slot. -/
def PIN_LIST_CONS : Nat := 11
/-- con-leche: none — the arena's own pin table; `charName`'s slot. -/
def PIN_CHAR : Nat := 12
/-- con-leche: none — the arena's own pin table; `andName`'s slot. -/
def PIN_AND : Nat := 13
/-- con-leche: none — the arena's own pin table; `charOfNatName`'s slot. -/
def PIN_CHAR_OF_NAT : Nat := 14
/-- con-leche: none — the arena's own pin table; `sorryAxName`'s slot. -/
def PIN_SORRY_AX : Nat := 15
/-- con-leche: none — the arena's own pin table; `Nat.pred`'s slot. -/
def PIN_NAT_PRED : Nat := 16
/-- con-leche: none — the arena's own pin table; `Nat.add`'s slot. -/
def PIN_NAT_ADD : Nat := 17
/-- con-leche: none — the arena's own pin table; `Nat.sub`'s slot. -/
def PIN_NAT_SUB : Nat := 18
/-- con-leche: none — the arena's own pin table; `Nat.mul`'s slot. -/
def PIN_NAT_MUL : Nat := 19
/-- con-leche: none — the arena's own pin table; `Nat.pow`'s slot. -/
def PIN_NAT_POW : Nat := 20
/-- con-leche: none — the arena's own pin table; `Nat.beq`'s slot. -/
def PIN_NAT_BEQ : Nat := 21
/-- con-leche: none — the arena's own pin table; `Nat.ble`'s slot. -/
def PIN_NAT_BLE : Nat := 22
/-- con-leche: none — the arena's own pin table; `Nat.div`'s slot. -/
def PIN_NAT_DIV : Nat := 23
/-- con-leche: none — the arena's own pin table; `Nat.mod`'s slot. -/
def PIN_NAT_MOD : Nat := 24
/-- con-leche: none — the arena's own pin table; `Nat.gcd`'s slot. -/
def PIN_NAT_GCD : Nat := 25
/-- con-leche: none — the arena's own pin table; `Nat.land`'s slot. -/
def PIN_NAT_LAND : Nat := 26
/-- con-leche: none — the arena's own pin table; `Nat.lor`'s slot. -/
def PIN_NAT_LOR : Nat := 27
/-- con-leche: none — the arena's own pin table; `Nat.xor`'s slot. -/
def PIN_NAT_XOR : Nat := 28
/-- con-leche: none — the arena's own pin table; `Nat.shiftLeft`'s slot. -/
def PIN_NAT_SHIFT_LEFT : Nat := 29
/-- con-leche: none — the arena's own pin table; `Nat.shiftRight`'s slot. -/
def PIN_NAT_SHIFT_RIGHT : Nat := 30
/-- con-leche: none — the arena's own pin table; `Bool`'s slot. -/
def PIN_BOOL : Nat := 31
/-- con-leche: none — the arena's own pin table; `Bool.true`'s slot. -/
def PIN_BOOL_TRUE : Nat := 32
/-- con-leche: none — the arena's own pin table; `Bool.false`'s slot. -/
def PIN_BOOL_FALSE : Nat := 33
/-- con-leche: none — the arena's own pin table; `propextName`'s slot. -/
def PIN_PROPEXT : Nat := 34
/-- con-leche: none — the arena's own pin table; `choiceName`'s slot. -/
def PIN_CHOICE : Nat := 35
/-- con-leche: none — the arena's own pin table; `iffName`'s slot. -/
def PIN_IFF : Nat := 36
/-- con-leche: none — the arena's own pin table; `iffIntroName`'s slot. -/
def PIN_IFF_INTRO : Nat := 37
/-- con-leche: none — the arena's own pin table; `iffRecName`'s slot. -/
def PIN_IFF_REC : Nat := 38
/-- con-leche: none — the arena's own pin table; `nonemptyName`'s slot. -/
def PIN_NONEMPTY : Nat := 39
/-- con-leche: none — the arena's own pin table; `nonemptyIntroName`'s slot. -/
def PIN_NONEMPTY_INTRO : Nat := 40
/-- con-leche: none — the arena's own pin table; `nonemptyRecName`'s slot. -/
def PIN_NONEMPTY_REC : Nat := 41
/-- con-leche: none — the arena's own pin table; `trueName`'s slot. -/
def PIN_TRUE : Nat := 42
/-- con-leche: none — the arena's own pin table; `trueIntroName`'s slot. -/
def PIN_TRUE_INTRO : Nat := 43
/-- con-leche: none — the arena's own pin table; `trustCompilerName`'s slot. -/
def PIN_TRUST_COMPILER : Nat := 44
/-- con-leche: none — the arena's own pin table; `reduceNatName`'s slot. -/
def PIN_REDUCE_NAT : Nat := 45
/-- con-leche: none — the arena's own pin table; `reduceBoolName`'s slot. -/
def PIN_REDUCE_BOOL : Nat := 46
/-- con-leche: none — the arena's own pin table; `ofReduceNatName`'s slot. -/
def PIN_OF_REDUCE_NAT : Nat := 47
/-- con-leche: none — the arena's own pin table; `ofReduceBoolName`'s slot. -/
def PIN_OF_REDUCE_BOOL : Nat := 48

/-! ## Filling the table -/

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames —
the pinned names, in `PIN_*` order.  This is the list `internReservedPins` interns
and `pinAt` indexes. -/
def pinNames : List ConLeche.Name :=
  [ConLeche.eqName, ConLeche.punitName, ConLeche.punitName.str "rec",
    ConLeche.natName, ConLeche.natZeroName, ConLeche.natSuccName,
    ConLeche.quotName.str "sound", ConLeche.stringName,
    ConLeche.stringOfListName, ConLeche.listName, ConLeche.listNilName,
    ConLeche.listConsName, ConLeche.charName, ConLeche.andName,
    ConLeche.charOfNatName, ConLeche.sorryAxName,
    ConLeche.natName.str "pred", ConLeche.natName.str "add",
    ConLeche.natName.str "sub", ConLeche.natName.str "mul",
    ConLeche.natName.str "pow", ConLeche.natName.str "beq",
    ConLeche.natName.str "ble", ConLeche.natName.str "div",
    ConLeche.natName.str "mod", ConLeche.natName.str "gcd",
    ConLeche.natName.str "land", ConLeche.natName.str "lor",
    ConLeche.natName.str "xor", ConLeche.natName.str "shiftLeft",
    ConLeche.natName.str "shiftRight",
    ConLeche.Name.anonymous.str "Bool",
    (ConLeche.Name.anonymous.str "Bool").str "true",
    (ConLeche.Name.anonymous.str "Bool").str "false",
    ConLeche.propextName, ConLeche.choiceName, ConLeche.iffName,
    ConLeche.iffIntroName, ConLeche.iffRecName, ConLeche.nonemptyName,
    ConLeche.nonemptyIntroName, ConLeche.nonemptyRecName,
    ConLeche.trueName, ConLeche.trueIntroName, ConLeche.trustCompilerName,
    ConLeche.reduceNatName, ConLeche.reduceBoolName,
    ConLeche.ofReduceNatName, ConLeche.ofReduceBoolName]

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames —
the nineteen names a stream may not declare, as con-leche's values.  Its own
list rather than nineteen slots of `names`, because its only reader wants the
whole vector and because five of the nineteen are `rec` forms that nothing
else pins. -/
def reservedBasisNameValues : List ConLeche.Name :=
  [ConLeche.eqName, ConLeche.eqReflName, ConLeche.eqName.str "rec",
    ConLeche.natName, ConLeche.natZeroName, ConLeche.natSuccName,
    ConLeche.natName.str "rec", ConLeche.punitName,
    ConLeche.punitUnitName, ConLeche.punitName.str "rec",
    ConLeche.emptyName, ConLeche.emptyName.str "rec",
    ConLeche.falseName, ConLeche.falseName.str "rec",
    ConLeche.quotName, ConLeche.quotName.str "mk",
    ConLeche.quotName.str "lift", ConLeche.quotName.str "ind",
    ConLeche.quotName.str "sound"]

/-- con-leche: none — intern a list of transient names, one handle each; the
cursor recursion `internReservedPins` runs twice. -/
def internNameList : List ConLeche.Name → AM (List NIdx)
  | [] => pure []
  | n :: ns => do
    let h ← internName n
    let hs ← internNameList ns
    pure (h :: hs)

/-- con-leche: none — **intern every reserved constant into the store, ONCE,
and install the table.**  The driver calls this immediately after the state is
made and before the prelude, so the scratch tier is closed and every handle
below is persistent (the module note says why that matters). -/
def internReservedPins : AM Unit := do
  let hs ← internNameList pinNames
  let rs ← internNameList reservedBasisNameValues
  let us ← internLsNode []
  let z ← internLNode .zero
  let o ← internLNode (.succ z)
  let s1 ← internSortE o
  let s ← get
  set { s with pins :=
    { names := hs.toArray, reserved := rs, emptyLevels := us,
      zeroLevel := z, sortOne := s1 } }

/-! ## Reading the table -/

/-- con-leche: none — has the driver filled the table?  An unfilled table is
EMPTY, which is why the test is a length and not a sentinel handle. -/
@[inline] def pinsReady (st : AState) : Bool := st.pins.names.size = pinCount

/-- con-leche: none — one pinned name handle.  The bounds branch is task
#97c's hazard, turned into a stop: a pin read before the driver's
`internReservedPins` raises `.internal` rather than answering with a word that
happens to parse as a handle. -/
@[inline] def pinAt (i : Nat) : AM NIdx := do
  let s ← get
  if h : i < s.pins.names.size then pure s.pins.names[i]
  else fail (.internal "arena: reserved-name pins not interned")

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames —
the nineteen reserved names, off the table. -/
def pinReserved : AM (List NIdx) := do
  let s ← get
  if pinsReady s then pure s.pins.reserved
  else fail (.internal "arena: reserved-name pins not interned")

/-- con-leche: none — the empty universe-argument list, off the table. -/
def pinEmptyLevels : AM LsIdx := do
  let s ← get
  if pinsReady s then pure s.pins.emptyLevels
  else fail (.internal "arena: reserved-name pins not interned")

/-- con-leche: none — the level `0`, off the table. -/
def pinZeroLevel : AM LIdx := do
  let s ← get
  if pinsReady s then pure s.pins.zeroLevel
  else fail (.internal "arena: reserved-name pins not interned")

/-- con-leche: none — the expression `Sort 1`, off the table. -/
def pinSortOne : AM EIdx := do
  let s ← get
  if pinsReady s then pure s.pins.sortOne
  else fail (.internal "arena: reserved-name pins not interned")

/-! ## The forty-nine named readers, one per slot -/

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:26-30 eqName — off the table. -/
def pinEq : AM NIdx := pinAt PIN_EQ
/-- con-leche: ConLeche/Kernel/Basis/Names.lean:26-30 punitName — off the table. -/
def pinPUnit : AM NIdx := pinAt PIN_PUNIT
/-- con-leche: ConLeche/Kernel/Basis/Names.lean:26-30 punitName — `PUnit.rec`. -/
def pinPUnitRec : AM NIdx := pinAt PIN_PUNIT_REC
/-- con-leche: ConLeche/Kernel/Basis/Names.lean:26-30 natName — off the table. -/
def pinNat : AM NIdx := pinAt PIN_NAT
/-- con-leche: ConLeche/Kernel/Basis/Names.lean:26-30 natZeroName — off the table. -/
def pinNatZero : AM NIdx := pinAt PIN_NAT_ZERO
/-- con-leche: ConLeche/Kernel/Basis/Names.lean:26-30 natSuccName — off the table. -/
def pinNatSucc : AM NIdx := pinAt PIN_NAT_SUCC
/-- con-leche: ConLeche/Kernel/Basis/Names.lean:26-30 quotName — `Quot.sound`. -/
def pinQuotSound : AM NIdx := pinAt PIN_QUOT_SOUND
/-- con-leche: ConLeche/Kernel/Basis/Names.lean:26-30 stringName — off the table. -/
def pinString : AM NIdx := pinAt PIN_STRING
/-- con-leche: ConLeche/Kernel/Basis/Names.lean:26-30 stringOfListName — off the table. -/
def pinStringOfList : AM NIdx := pinAt PIN_STRING_OF_LIST
/-- con-leche: ConLeche/Kernel/Basis/Names.lean:26-30 listName — off the table. -/
def pinList : AM NIdx := pinAt PIN_LIST
/-- con-leche: ConLeche/Kernel/Basis/Names.lean:26-30 listNilName — off the table. -/
def pinListNil : AM NIdx := pinAt PIN_LIST_NIL
/-- con-leche: ConLeche/Kernel/Basis/Names.lean:26-30 listConsName — off the table. -/
def pinListCons : AM NIdx := pinAt PIN_LIST_CONS
/-- con-leche: ConLeche/Kernel/Basis/Names.lean:26-30 charName — off the table. -/
def pinChar : AM NIdx := pinAt PIN_CHAR
/-- con-leche: ConLeche/Kernel/Basis/Names.lean:26-30 andName — off the table. -/
def pinAnd : AM NIdx := pinAt PIN_AND
/-- con-leche: ConLeche/Kernel/Basis/Names.lean:26-30 charOfNatName — off the table. -/
def pinCharOfNat : AM NIdx := pinAt PIN_CHAR_OF_NAT
/-- con-leche: ConLeche/Kernel/Basis/Names.lean:26-30 sorryAxName — off the table. -/
def pinSorryAx : AM NIdx := pinAt PIN_SORRY_AX
/-- con-leche: ConLeche/Kernel/CoreK.lean:30-60 natPredName — off the table. -/
def pinNatPred : AM NIdx := pinAt PIN_NAT_PRED
/-- con-leche: ConLeche/Kernel/CoreK.lean:30-60 natAddName — off the table. -/
def pinNatAdd : AM NIdx := pinAt PIN_NAT_ADD
/-- con-leche: ConLeche/Kernel/CoreK.lean:30-60 natSubName — off the table. -/
def pinNatSub : AM NIdx := pinAt PIN_NAT_SUB
/-- con-leche: ConLeche/Kernel/CoreK.lean:30-60 natMulName — off the table. -/
def pinNatMul : AM NIdx := pinAt PIN_NAT_MUL
/-- con-leche: ConLeche/Kernel/CoreK.lean:30-60 natPowName — off the table. -/
def pinNatPow : AM NIdx := pinAt PIN_NAT_POW
/-- con-leche: ConLeche/Kernel/CoreK.lean:30-60 natBeqName — off the table. -/
def pinNatBeq : AM NIdx := pinAt PIN_NAT_BEQ
/-- con-leche: ConLeche/Kernel/CoreK.lean:30-60 natBleName — off the table. -/
def pinNatBle : AM NIdx := pinAt PIN_NAT_BLE
/-- con-leche: ConLeche/Kernel/CoreK.lean:30-60 natDivName — off the table. -/
def pinNatDiv : AM NIdx := pinAt PIN_NAT_DIV
/-- con-leche: ConLeche/Kernel/CoreK.lean:30-60 natModName — off the table. -/
def pinNatMod : AM NIdx := pinAt PIN_NAT_MOD
/-- con-leche: ConLeche/Kernel/CoreK.lean:30-60 natGcdName — off the table. -/
def pinNatGcd : AM NIdx := pinAt PIN_NAT_GCD
/-- con-leche: ConLeche/Kernel/CoreK.lean:30-60 natLandName — off the table. -/
def pinNatLand : AM NIdx := pinAt PIN_NAT_LAND
/-- con-leche: ConLeche/Kernel/CoreK.lean:30-60 natLorName — off the table. -/
def pinNatLor : AM NIdx := pinAt PIN_NAT_LOR
/-- con-leche: ConLeche/Kernel/CoreK.lean:30-60 natXorName — off the table. -/
def pinNatXor : AM NIdx := pinAt PIN_NAT_XOR
/-- con-leche: ConLeche/Kernel/CoreK.lean:30-60 natShiftLeftName — off the table. -/
def pinNatShiftLeft : AM NIdx := pinAt PIN_NAT_SHIFT_LEFT
/-- con-leche: ConLeche/Kernel/CoreK.lean:30-60 natShiftRightName — off the table. -/
def pinNatShiftRight : AM NIdx := pinAt PIN_NAT_SHIFT_RIGHT
/-- con-leche: ConLeche/Kernel/CoreK.lean:30-60 boolName — off the table. -/
def pinBool : AM NIdx := pinAt PIN_BOOL
/-- con-leche: ConLeche/Kernel/CoreK.lean:30-60 boolTrueName — off the table. -/
def pinBoolTrue : AM NIdx := pinAt PIN_BOOL_TRUE
/-- con-leche: ConLeche/Kernel/CoreK.lean:30-60 boolFalseName — off the table. -/
def pinBoolFalse : AM NIdx := pinAt PIN_BOOL_FALSE
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:39 propextName — off the table. -/
def pinPropext : AM NIdx := pinAt PIN_PROPEXT
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:42 choiceName — off the table. -/
def pinChoice : AM NIdx := pinAt PIN_CHOICE
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:45 iffName — off the table. -/
def pinIff : AM NIdx := pinAt PIN_IFF
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:48 iffIntroName — off the table. -/
def pinIffIntro : AM NIdx := pinAt PIN_IFF_INTRO
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:51 iffRecName — off the table. -/
def pinIffRec : AM NIdx := pinAt PIN_IFF_REC
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:54 nonemptyName — off the table. -/
def pinNonempty : AM NIdx := pinAt PIN_NONEMPTY
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:57 nonemptyIntroName — off the table. -/
def pinNonemptyIntro : AM NIdx := pinAt PIN_NONEMPTY_INTRO
/-- con-leche: ConLeche/Kernel/StdAxioms.lean:60 nonemptyRecName — off the table. -/
def pinNonemptyRec : AM NIdx := pinAt PIN_NONEMPTY_REC
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:52 trueName — off the table. -/
def pinTrue : AM NIdx := pinAt PIN_TRUE
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:55 trueIntroName — off the table. -/
def pinTrueIntro : AM NIdx := pinAt PIN_TRUE_INTRO
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:58 trustCompilerName — off the table. -/
def pinTrustCompiler : AM NIdx := pinAt PIN_TRUST_COMPILER
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:61 reduceNatName — off the table. -/
def pinReduceNat : AM NIdx := pinAt PIN_REDUCE_NAT
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:64 reduceBoolName — off the table. -/
def pinReduceBool : AM NIdx := pinAt PIN_REDUCE_BOOL
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:67 ofReduceNatName — off the table. -/
def pinOfReduceNat : AM NIdx := pinAt PIN_OF_REDUCE_NAT
/-- con-leche: ConLeche/Kernel/TrustAxioms.lean:70 ofReduceBoolName — off the table. -/
def pinOfReduceBool : AM NIdx := pinAt PIN_OF_REDUCE_BOOL

end ConRon.Arena

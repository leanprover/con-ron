/-
# `ConRon.Refine2.Checker.Pins` — Theorem 2 for `arena::pins` and `arena::nat_op_pin_set`

**Task #97-P5-Checker**, deliverable 2's first file (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/{pins,nat_op_pin_set}.rs` against
`proof/ConRon/Arena/{Pins,NatOpPinSet}.lean`: the arena's own pin table — the
forty-nine reserved constant names, the nineteen reserved basis names, the
empty universe-argument list, the level `0` and the expression `Sort 1`, all
interned ONCE by the driver before the prelude — and the `Nat`-operation pin
variants interned beside them.

## Why the fifty-four readers are `SimRE` and not `Sim`

`pin_at(st, i)` takes `&AState` and returns `Result<NIdx, CheckError>`: it
reads the table and can DECLINE (task #97c's hazard, turned into a stop — an
unfilled table is empty, so a pin read before `intern_reserved_pins` raises
`Internal` rather than answering with a word that happens to parse as a
handle), but it never writes.  `Refine2/Shape.lean`'s `SimR` has no error arm
and its `Sim` wants a post-state; `Refine2/Checker/Shape.lean`'s **`SimRE`**
is the two halves put together, and this file is where it earns its keep
fifty-four times.

The `Internal` decline is one of the three MIRRORED kinds, so the claim is
real: the twin declines too, at the same kind, and the two bound tests agree
clause for clause (`i < names.size` on both sides, `names.size = pinCount` on
both sides).  `PinsRel.names` — `lp.names.toList = rp.names.val.map absNIdx`
— is the whole of the correspondence.

## `intern_reserved_pins` is the one WRITER

It is the driver's startup, and DESIGN §8.3's tier discipline is the reason
its statement matters: *after it every pin node is in the persistent cons
table, so a later `intern` of the same node — whatever tier is live — probes
persistent first and hands back the persistent handle*.  The proof is
`Specs.lean`'s `intern_name`, `intern_ls_node`, `intern_l_node` and
`intern_e_sort`, six in a row, then the `Pins` record written whole.

## What these lemmas wait on

`pin_at` and its forty-nine wrappers wait on **nothing below them** — they are
`PinsRel.names` plus a bounds test, which is why they are the cheapest group
of the tier.  `intern_reserved_pins` and the three `intern_pin_set*` wait on
`Specs.lean`'s four transient walks and its per-constructor interns (task
#97-P5-1 §8's thirty-two).
-/
import ConRon.Refine2.Promote.Promote
import ConRon.Refine.PinsAbs

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine (NameWF NamesWF ExprWF StrWF)

/-! ## The table's own two writers and its four readers -/

/-- `pin_names` is the twin's `pinNames`, a pure list of con-leche `Name`s
built by nineteen `basis_names` calls.  The `NamesWF` conjunct is what every
caller of `intern_name_list` owes (`Refine2/Promote/Intern.lean`'s note). -/
theorem pin_names_refines {o} (hrun : arena.pins.pin_names = ok o) :
    ConRon.Refine.absNames o = pinNames ∧ NamesWF o := by
  sorry

/-- **`intern_reserved_pins` ⊑ `internReservedPins`** — the driver's startup:
every reserved constant interned into the PERSISTENT tier once, and the table
installed.  The scratch tier is closed when it runs (the module note says why
that matters), which is `rs.scratch_on = false` here and task #97-P5-1's
finding 8 read from the other side. -/
theorem intern_reserved_pins_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.intern_reserved_pins pers st = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o internReservedPins := by
  sorry

/-- `pins_ready` ⊑ `pinsReady` — a length test, because an unfilled table is
EMPTY and not a sentinel handle. -/
theorem pins_ready_refines {pers st lst} {o : Bool}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pins_ready st = ok o) :
    o = pinsReady lst := by
  sorry

/-- `pin_at` ⊑ `pinAt` — **the one lemma the forty-nine below are instances
of**: the bounds branch and then `PinsRel.names`. -/
theorem pin_at_refines {pers st lst} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_at st i = ok o) :
    SimRE absNIdx lst o (pinAt (absSz i)) := by
  sorry

/-- `pin_reserved` ⊑ `pinReserved` — the nineteen reserved basis names, off
the table.  `arena::core`'s `reserved_basis_names` used to build and intern
all nineteen on every call, which task #97-P6-4a's profile put at 1.1 % of
`Init`'s cycles in the `Name` construction alone. -/
theorem pin_reserved_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_reserved st = ok o) :
    SimRE absNIdxL lst o pinReserved := by
  sorry

/-- `pin_empty_levels` ⊑ `pinEmptyLevels`. -/
theorem pin_empty_levels_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_empty_levels st = ok o) :
    SimRE absLsIdx lst o pinEmptyLevels := by
  sorry

/-- `pin_zero_level` ⊑ `pinZeroLevel`. -/
theorem pin_zero_level_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_zero_level st = ok o) :
    SimRE absLIdx lst o pinZeroLevel := by
  sorry

/-- `pin_sort_one` ⊑ `pinSortOne`. -/
theorem pin_sort_one_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_sort_one st = ok o) :
    SimRE absEIdx lst o pinSortOne := by
  sorry

/-! ## The forty-nine named readers, one per slot

Each is `pin_at` at its own constant, and each lemma is `pin_at_refines` after
that constant's value.  The order is `Arena/Pins.lean`'s, which is
`arena::pins`'s. -/

/-- `pin_eq` ⊑ `pinEq`, at slot `PIN_EQ`. -/
theorem pin_eq_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_eq st = ok o) :
    SimRE absNIdx lst o pinEq := by
  sorry

/-- `pin_punit` ⊑ `pinPUnit`, at slot `PIN_PUNIT`. -/
theorem pin_punit_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_punit st = ok o) :
    SimRE absNIdx lst o pinPUnit := by
  sorry

/-- `pin_punit_rec` ⊑ `pinPUnitRec`, at slot `PIN_PUNIT_REC`. -/
theorem pin_punit_rec_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_punit_rec st = ok o) :
    SimRE absNIdx lst o pinPUnitRec := by
  sorry

/-- `pin_nat` ⊑ `pinNat`, at slot `PIN_NAT`. -/
theorem pin_nat_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat st = ok o) :
    SimRE absNIdx lst o pinNat := by
  sorry

/-- `pin_nat_zero` ⊑ `pinNatZero`, at slot `PIN_NAT_ZERO`. -/
theorem pin_nat_zero_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_zero st = ok o) :
    SimRE absNIdx lst o pinNatZero := by
  sorry

/-- `pin_nat_succ` ⊑ `pinNatSucc`, at slot `PIN_NAT_SUCC`. -/
theorem pin_nat_succ_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_succ st = ok o) :
    SimRE absNIdx lst o pinNatSucc := by
  sorry

/-- `pin_quot_sound` ⊑ `pinQuotSound`, at slot `PIN_QUOT_SOUND`. -/
theorem pin_quot_sound_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_quot_sound st = ok o) :
    SimRE absNIdx lst o pinQuotSound := by
  sorry

/-- `pin_string` ⊑ `pinString`, at slot `PIN_STRING`. -/
theorem pin_string_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_string st = ok o) :
    SimRE absNIdx lst o pinString := by
  sorry

/-- `pin_string_of_list` ⊑ `pinStringOfList`, at slot `PIN_STRING_OF_LIST`. -/
theorem pin_string_of_list_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_string_of_list st = ok o) :
    SimRE absNIdx lst o pinStringOfList := by
  sorry

/-- `pin_list` ⊑ `pinList`, at slot `PIN_LIST`. -/
theorem pin_list_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_list st = ok o) :
    SimRE absNIdx lst o pinList := by
  sorry

/-- `pin_list_nil` ⊑ `pinListNil`, at slot `PIN_LIST_NIL`. -/
theorem pin_list_nil_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_list_nil st = ok o) :
    SimRE absNIdx lst o pinListNil := by
  sorry

/-- `pin_list_cons` ⊑ `pinListCons`, at slot `PIN_LIST_CONS`. -/
theorem pin_list_cons_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_list_cons st = ok o) :
    SimRE absNIdx lst o pinListCons := by
  sorry

/-- `pin_char` ⊑ `pinChar`, at slot `PIN_CHAR`. -/
theorem pin_char_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_char st = ok o) :
    SimRE absNIdx lst o pinChar := by
  sorry

/-- `pin_and` ⊑ `pinAnd`, at slot `PIN_AND`. -/
theorem pin_and_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_and st = ok o) :
    SimRE absNIdx lst o pinAnd := by
  sorry

/-- `pin_char_of_nat` ⊑ `pinCharOfNat`, at slot `PIN_CHAR_OF_NAT`. -/
theorem pin_char_of_nat_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_char_of_nat st = ok o) :
    SimRE absNIdx lst o pinCharOfNat := by
  sorry

/-- `pin_sorry_ax` ⊑ `pinSorryAx`, at slot `PIN_SORRY_AX`. -/
theorem pin_sorry_ax_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_sorry_ax st = ok o) :
    SimRE absNIdx lst o pinSorryAx := by
  sorry

/-- `pin_nat_pred` ⊑ `pinNatPred`, at slot `PIN_NAT_PRED`. -/
theorem pin_nat_pred_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_pred st = ok o) :
    SimRE absNIdx lst o pinNatPred := by
  sorry

/-- `pin_nat_add` ⊑ `pinNatAdd`, at slot `PIN_NAT_ADD`. -/
theorem pin_nat_add_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_add st = ok o) :
    SimRE absNIdx lst o pinNatAdd := by
  sorry

/-- `pin_nat_sub` ⊑ `pinNatSub`, at slot `PIN_NAT_SUB`. -/
theorem pin_nat_sub_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_sub st = ok o) :
    SimRE absNIdx lst o pinNatSub := by
  sorry

/-- `pin_nat_mul` ⊑ `pinNatMul`, at slot `PIN_NAT_MUL`. -/
theorem pin_nat_mul_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_mul st = ok o) :
    SimRE absNIdx lst o pinNatMul := by
  sorry

/-- `pin_nat_pow` ⊑ `pinNatPow`, at slot `PIN_NAT_POW`. -/
theorem pin_nat_pow_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_pow st = ok o) :
    SimRE absNIdx lst o pinNatPow := by
  sorry

/-- `pin_nat_beq` ⊑ `pinNatBeq`, at slot `PIN_NAT_BEQ`. -/
theorem pin_nat_beq_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_beq st = ok o) :
    SimRE absNIdx lst o pinNatBeq := by
  sorry

/-- `pin_nat_ble` ⊑ `pinNatBle`, at slot `PIN_NAT_BLE`. -/
theorem pin_nat_ble_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_ble st = ok o) :
    SimRE absNIdx lst o pinNatBle := by
  sorry

/-- `pin_nat_div` ⊑ `pinNatDiv`, at slot `PIN_NAT_DIV`. -/
theorem pin_nat_div_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_div st = ok o) :
    SimRE absNIdx lst o pinNatDiv := by
  sorry

/-- `pin_nat_mod` ⊑ `pinNatMod`, at slot `PIN_NAT_MOD`. -/
theorem pin_nat_mod_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_mod st = ok o) :
    SimRE absNIdx lst o pinNatMod := by
  sorry

/-- `pin_nat_gcd` ⊑ `pinNatGcd`, at slot `PIN_NAT_GCD`. -/
theorem pin_nat_gcd_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_gcd st = ok o) :
    SimRE absNIdx lst o pinNatGcd := by
  sorry

/-- `pin_nat_land` ⊑ `pinNatLand`, at slot `PIN_NAT_LAND`. -/
theorem pin_nat_land_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_land st = ok o) :
    SimRE absNIdx lst o pinNatLand := by
  sorry

/-- `pin_nat_lor` ⊑ `pinNatLor`, at slot `PIN_NAT_LOR`. -/
theorem pin_nat_lor_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_lor st = ok o) :
    SimRE absNIdx lst o pinNatLor := by
  sorry

/-- `pin_nat_xor` ⊑ `pinNatXor`, at slot `PIN_NAT_XOR`. -/
theorem pin_nat_xor_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_xor st = ok o) :
    SimRE absNIdx lst o pinNatXor := by
  sorry

/-- `pin_nat_shift_left` ⊑ `pinNatShiftLeft`, at slot `PIN_NAT_SHIFT_LEFT`. -/
theorem pin_nat_shift_left_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_shift_left st = ok o) :
    SimRE absNIdx lst o pinNatShiftLeft := by
  sorry

/-- `pin_nat_shift_right` ⊑ `pinNatShiftRight`, at slot `PIN_NAT_SHIFT_RIGHT`. -/
theorem pin_nat_shift_right_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_shift_right st = ok o) :
    SimRE absNIdx lst o pinNatShiftRight := by
  sorry

/-- `pin_bool` ⊑ `pinBool`, at slot `PIN_BOOL`. -/
theorem pin_bool_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_bool st = ok o) :
    SimRE absNIdx lst o pinBool := by
  sorry

/-- `pin_bool_true` ⊑ `pinBoolTrue`, at slot `PIN_BOOL_TRUE`. -/
theorem pin_bool_true_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_bool_true st = ok o) :
    SimRE absNIdx lst o pinBoolTrue := by
  sorry

/-- `pin_bool_false` ⊑ `pinBoolFalse`, at slot `PIN_BOOL_FALSE`. -/
theorem pin_bool_false_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_bool_false st = ok o) :
    SimRE absNIdx lst o pinBoolFalse := by
  sorry

/-- `pin_propext` ⊑ `pinPropext`, at slot `PIN_PROPEXT`. -/
theorem pin_propext_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_propext st = ok o) :
    SimRE absNIdx lst o pinPropext := by
  sorry

/-- `pin_choice` ⊑ `pinChoice`, at slot `PIN_CHOICE`. -/
theorem pin_choice_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_choice st = ok o) :
    SimRE absNIdx lst o pinChoice := by
  sorry

/-- `pin_iff` ⊑ `pinIff`, at slot `PIN_IFF`. -/
theorem pin_iff_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_iff st = ok o) :
    SimRE absNIdx lst o pinIff := by
  sorry

/-- `pin_iff_intro` ⊑ `pinIffIntro`, at slot `PIN_IFF_INTRO`. -/
theorem pin_iff_intro_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_iff_intro st = ok o) :
    SimRE absNIdx lst o pinIffIntro := by
  sorry

/-- `pin_iff_rec` ⊑ `pinIffRec`, at slot `PIN_IFF_REC`. -/
theorem pin_iff_rec_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_iff_rec st = ok o) :
    SimRE absNIdx lst o pinIffRec := by
  sorry

/-- `pin_nonempty` ⊑ `pinNonempty`, at slot `PIN_NONEMPTY`. -/
theorem pin_nonempty_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nonempty st = ok o) :
    SimRE absNIdx lst o pinNonempty := by
  sorry

/-- `pin_nonempty_intro` ⊑ `pinNonemptyIntro`, at slot `PIN_NONEMPTY_INTRO`. -/
theorem pin_nonempty_intro_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nonempty_intro st = ok o) :
    SimRE absNIdx lst o pinNonemptyIntro := by
  sorry

/-- `pin_nonempty_rec` ⊑ `pinNonemptyRec`, at slot `PIN_NONEMPTY_REC`. -/
theorem pin_nonempty_rec_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nonempty_rec st = ok o) :
    SimRE absNIdx lst o pinNonemptyRec := by
  sorry

/-- `pin_true` ⊑ `pinTrue`, at slot `PIN_TRUE`. -/
theorem pin_true_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_true st = ok o) :
    SimRE absNIdx lst o pinTrue := by
  sorry

/-- `pin_true_intro` ⊑ `pinTrueIntro`, at slot `PIN_TRUE_INTRO`. -/
theorem pin_true_intro_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_true_intro st = ok o) :
    SimRE absNIdx lst o pinTrueIntro := by
  sorry

/-- `pin_trust_compiler` ⊑ `pinTrustCompiler`, at slot `PIN_TRUST_COMPILER`. -/
theorem pin_trust_compiler_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_trust_compiler st = ok o) :
    SimRE absNIdx lst o pinTrustCompiler := by
  sorry

/-- `pin_reduce_nat` ⊑ `pinReduceNat`, at slot `PIN_REDUCE_NAT`. -/
theorem pin_reduce_nat_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_reduce_nat st = ok o) :
    SimRE absNIdx lst o pinReduceNat := by
  sorry

/-- `pin_reduce_bool` ⊑ `pinReduceBool`, at slot `PIN_REDUCE_BOOL`. -/
theorem pin_reduce_bool_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_reduce_bool st = ok o) :
    SimRE absNIdx lst o pinReduceBool := by
  sorry

/-- `pin_of_reduce_nat` ⊑ `pinOfReduceNat`, at slot `PIN_OF_REDUCE_NAT`. -/
theorem pin_of_reduce_nat_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_of_reduce_nat st = ok o) :
    SimRE absNIdx lst o pinOfReduceNat := by
  sorry

/-- `pin_of_reduce_bool` ⊑ `pinOfReduceBool`, at slot `PIN_OF_REDUCE_BOOL`. -/
theorem pin_of_reduce_bool_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_of_reduce_bool st = ok o) :
    SimRE absNIdx lst o pinOfReduceBool := by
  sorry

/-! ## `arena::nat_op_pin_set` — the `Nat`-operation pin variants

DESIGN §8.6 P2d: *intern con-leche's `natOpPinSets` `Expr`s into the
persistent tier at startup — a one-time tree walk*.  Sixteen terms deep per
variant, and `Modeller`-style indirection is explicitly NOT wanted: the pins
are data the checker reads, not a seam. -/

/-- `intern_pin_set_proofs` is the Rust-only tail of `intern_pin_set` past its
eight pinned defining expressions (extraction rule 5 again — eight live
handles is more than the loan checker will carry across a second walk), so it
is stated against the same twin with those eight in hand. -/
theorem intern_pin_set_proofs_refines {pers st lst}
    {ps : kernel.nat_op_pins.NatOpPinSet}
    {dp mp gp lap lop xp slp srp : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hwf : NatOpPinSetWF ps)
    (hrun : arena.nat_op_pin_set.intern_pin_set_proofs pers st ps dp mp gp lap
      lop xp slp srp = ok o) :
    Sim absINatOpPinSet (fun _ => True) pers lst o
      (do
        let dc ← internExprList (ConRon.Refine.absExprs ps.div_proofs)
        let mc ← internExprList (ConRon.Refine.absExprs ps.mod_proofs)
        let gc ← internExprList (ConRon.Refine.absExprs ps.gcd_proofs)
        let lac ← internExprList (ConRon.Refine.absExprs ps.land_proofs)
        let loc ← internExprList (ConRon.Refine.absExprs ps.lor_proofs)
        let xc ← internExprList (ConRon.Refine.absExprs ps.xor_proofs)
        let slc ← internExprList (ConRon.Refine.absExprs ps.shift_left_proofs)
        let src ← internExprList (ConRon.Refine.absExprs ps.shift_right_proofs)
        pure ⟨ConRon.Refine.absString ps.toolchain, absEIdx dp, absEIdx mp,
          absEIdx gp, absEIdx lap, absEIdx lop, absEIdx xp, absEIdx slp,
          absEIdx srp, dc, mc, gc, lac, loc, xc, slc, src⟩) := by
  sorry

/-- `intern_pin_set` ⊑ `internPinSet` — one variant, sixteen terms. -/
theorem intern_pin_set_refines {pers st lst}
    {ps : kernel.nat_op_pins.NatOpPinSet} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hwf : NatOpPinSetWF ps)
    (hrun : arena.nat_op_pin_set.intern_pin_set pers st ps = ok o) :
    Sim absINatOpPinSet (fun _ => True) pers lst o
      (internPinSet (ConRon.Refine.absNatOpPinSet ps)) := by
  sorry

/-- `intern_pin_sets` ⊑ `internPinSets` at the cursor — the variant LIST, in
the order the install gate tries them. -/
theorem intern_pin_sets_refines {pers st lst}
    {pss : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet} {i : Std.Usize}
    {out : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hwf : ∀ p ∈ pss.val, NatOpPinSetWF p)
    (hrun : arena.nat_op_pin_set.intern_pin_sets pers st pss i out = ok o) :
    Sim (fun v => absINatOpPinSetL out ++ absINatOpPinSetL v) (fun _ => True)
      pers lst o
      (do pure (absINatOpPinSetL out ++
        (← internPinSets ((pss.val.drop i.val).map ConRon.Refine.absNatOpPinSet)))) := by
  sorry

end ConRon.Refine2

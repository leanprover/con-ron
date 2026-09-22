//! `arena::pins` — the reserved names, interned ONCE (task #97-P6-4a).
//!
//! con-leche compares its reserved names — `natName`, `natZeroName`,
//! `natSuccName`, the sixteen `Nat`-operation names, the `Bool` trio, the
//! `String`/`List`/`Char` family, the standard and the trusted axiom names —
//! as `Name` VALUES, which Lean builds once per nullary `def` and caches.
//! The arena compares them as HANDLES, so `arena::core::pin` turned each one
//! into `intern_name` of a freshly built `Name`: a `code_points` allocation
//! and an `Arc<NameNode>` per path segment, then one cons-table probe per
//! segment, every time.  Task #97-P6-1's counter measured what that costs on
//! `Init`: **140 083 646 `NStore::intern` calls, of which 88 854 033 are
//! probes of a `str` node built purely to be compared and dropped** — tens of
//! millions of rebuilds of about forty constants, in `natLitSupported`'s
//! three probes per literal, in `natOpNames`, in `strLitToConstructor`.
//!
//! This module is DESIGN.md's answer, flagged at task #97c ("the `Pins`
//! record that is NOT here") and deferred there for want of a number: one
//! record, filled once at the driver by `intern_reserved_pins`, and every
//! `pin` of a constant name becomes a field read.
//!
//! **Not `arena::checker`'s `intern_all_pins`.**  That one walks the `--pins`
//! RECEIPT file (the trusted pin list) into the persistent tier; this one
//! interns the checker's own reserved constants.  The two run at the same
//! point of the pipeline and mean different things, which is why they have
//! different names.
//!
//! ## The table is a `Vec`, and that is what kills task #97c's hazard
//!
//! Task #97c declined the record because of an initialisation-order hazard:
//! "a pin read before it is filled compares against the zero word and
//! silently says *not `Nat`*".  A record of handle FIELDS has that hazard,
//! because every 32-bit word is a syntactically valid handle.  A `Vec<NIdx>`
//! does not: before `intern_reserved_pins` runs the table is EMPTY, so `pin_at`
//! takes its bounds branch and raises `CheckError::Internal` — a loud stop,
//! never a quiet wrong answer.  The cost is one `len` compare per read,
//! against an interning walk it replaces.
//!
//! ## What is pinned
//!
//! The forty-nine names below and `basis_names::reserved_basis_names()`'s
//! nineteen, plus the three interned values every `pin` site around them
//! needs: the empty universe-argument list, the level `0` and the expression
//! `Sort 1` (`arena::core`'s `empty_levels`, `zero_level` and `sort_one`,
//! which now read this record instead of interning).
//!
//! All of them go into the PERSISTENT tier, because `intern_reserved_pins` runs
//! before the parse, while the scratch tier is closed.  That matters twice:
//! a pinned handle must survive every `drop_scratch` (it is read across all
//! of them), and task #97-P6-1's `pers_find_maybe` rests on "a persistent
//! node's children are persistent", which the bottom-up intern of a closed
//! scratch tier gives for free.
//!
//! **Denotation unchanged.**  A pin is `intern_name` of the same `Name`, so
//! the handle this record holds is the handle `pin` computed before —
//! `denoteN` is injective and `intern` is idempotent, so pre-interning a name
//! the export also carries hands the export's parse the very same handle.
//! What changes is only WHEN the intern happens, and how many times.
//!
//! Lean twin: `proof/ConRon/Arena/Monad.lean:123-142 AState` (DESIGN.md §8.6's
//! twin ledger, task #97-P6-4a) — `AState` gains a `pins : Pins` field and
//! `internAllPins` fills it, and the hundred-odd `pin` clauses become field
//! reads. Nothing about the DENOTATION moves, and the one obligation is an
//! instance of `intern_spec`: `intern` is idempotent on a hash-consed store, so
//! the pinned handle IS the handle the clause it replaces computed.

use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx};
use crate::arena::env::nidx_vec_dup;
use crate::arena::intern::intern_name_list;
use crate::arena::monad::{
    AState, fail, intern_e_sort, intern_l_node, intern_ls_node,
};
use crate::arena::store::LNodeView;
use crate::kernel::basis_names;
use crate::kernel::core_k;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::name::Name;
use crate::kernel::std_axioms as cstd;
use crate::kernel::trust_axioms as ctrust;
use crate::ron::hashmap::Dup;
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// The messages of this module's declines
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"arena: reserved-name pins not interned"`, as code points.  This is the
/// hazard task #97c named, turned into a stop: it can only be raised by a
/// checker path that ran before the driver's `intern_reserved_pins`.
const M_PINS_UNSET: [u32; 38] = [
    97, 114, 101, 110, 97, 58, 32, 114, 101, 115, 101, 114, 118, 101, 100, 45, 110, 97, 109,
    101, 32, 112, 105, 110, 115, 32, 110, 111, 116, 32, 105, 110, 116, 101, 114, 110, 101, 100,
];

// ---------------------------------------------------------------------------
// The slots
// ---------------------------------------------------------------------------

/// con-leche: none — the arena's own pin table; the number of pinned names
/// The length `intern_reserved_pins` fills and `pin_at` bounds-checks against.
pub const PIN_COUNT: usize = 49;

// `basis_names`
/// con-leche: none — the arena's own pin table; `basis_names::eq_name()`'s slot
pub const PIN_EQ: usize = 0;
/// con-leche: none — the arena's own pin table; `basis_names::punit_name()`'s slot
pub const PIN_PUNIT: usize = 1;
/// con-leche: none — the arena's own pin table; `basis_names::punit_rec_name()`'s slot
pub const PIN_PUNIT_REC: usize = 2;
/// con-leche: none — the arena's own pin table; `basis_names::nat_name()`'s slot
pub const PIN_NAT: usize = 3;
/// con-leche: none — the arena's own pin table; `basis_names::nat_zero_name()`'s slot
pub const PIN_NAT_ZERO: usize = 4;
/// con-leche: none — the arena's own pin table; `basis_names::nat_succ_name()`'s slot
pub const PIN_NAT_SUCC: usize = 5;
/// con-leche: none — the arena's own pin table; `basis_names::quot_sound_name()`'s slot
pub const PIN_QUOT_SOUND: usize = 6;
/// con-leche: none — the arena's own pin table; `basis_names::string_name()`'s slot
pub const PIN_STRING: usize = 7;
/// con-leche: none — the arena's own pin table; `basis_names::string_of_list_name()`'s slot
pub const PIN_STRING_OF_LIST: usize = 8;
/// con-leche: none — the arena's own pin table; `basis_names::list_name()`'s slot
pub const PIN_LIST: usize = 9;
/// con-leche: none — the arena's own pin table; `basis_names::list_nil_name()`'s slot
pub const PIN_LIST_NIL: usize = 10;
/// con-leche: none — the arena's own pin table; `basis_names::list_cons_name()`'s slot
pub const PIN_LIST_CONS: usize = 11;
/// con-leche: none — the arena's own pin table; `basis_names::char_name()`'s slot
pub const PIN_CHAR: usize = 12;
/// con-leche: none — the arena's own pin table; `basis_names::and_name()`'s slot
pub const PIN_AND: usize = 13;
/// con-leche: none — the arena's own pin table; `basis_names::char_of_nat_name()`'s slot
pub const PIN_CHAR_OF_NAT: usize = 14;
/// con-leche: none — the arena's own pin table; `basis_names::sorry_ax_name()`'s slot
pub const PIN_SORRY_AX: usize = 15;

// `core_k`
/// con-leche: none — the arena's own pin table; `core_k::nat_pred_name()`'s slot
pub const PIN_NAT_PRED: usize = 16;
/// con-leche: none — the arena's own pin table; `core_k::nat_add_name()`'s slot
pub const PIN_NAT_ADD: usize = 17;
/// con-leche: none — the arena's own pin table; `core_k::nat_sub_name()`'s slot
pub const PIN_NAT_SUB: usize = 18;
/// con-leche: none — the arena's own pin table; `core_k::nat_mul_name()`'s slot
pub const PIN_NAT_MUL: usize = 19;
/// con-leche: none — the arena's own pin table; `core_k::nat_pow_name()`'s slot
pub const PIN_NAT_POW: usize = 20;
/// con-leche: none — the arena's own pin table; `core_k::nat_beq_name()`'s slot
pub const PIN_NAT_BEQ: usize = 21;
/// con-leche: none — the arena's own pin table; `core_k::nat_ble_name()`'s slot
pub const PIN_NAT_BLE: usize = 22;
/// con-leche: none — the arena's own pin table; `core_k::nat_div_name()`'s slot
pub const PIN_NAT_DIV: usize = 23;
/// con-leche: none — the arena's own pin table; `core_k::nat_mod_name()`'s slot
pub const PIN_NAT_MOD: usize = 24;
/// con-leche: none — the arena's own pin table; `core_k::nat_gcd_name()`'s slot
pub const PIN_NAT_GCD: usize = 25;
/// con-leche: none — the arena's own pin table; `core_k::nat_land_name()`'s slot
pub const PIN_NAT_LAND: usize = 26;
/// con-leche: none — the arena's own pin table; `core_k::nat_lor_name()`'s slot
pub const PIN_NAT_LOR: usize = 27;
/// con-leche: none — the arena's own pin table; `core_k::nat_xor_name()`'s slot
pub const PIN_NAT_XOR: usize = 28;
/// con-leche: none — the arena's own pin table; `core_k::nat_shift_left_name()`'s slot
pub const PIN_NAT_SHIFT_LEFT: usize = 29;
/// con-leche: none — the arena's own pin table; `core_k::nat_shift_right_name()`'s slot
pub const PIN_NAT_SHIFT_RIGHT: usize = 30;
/// con-leche: none — the arena's own pin table; `core_k::bool_name()`'s slot
pub const PIN_BOOL: usize = 31;
/// con-leche: none — the arena's own pin table; `core_k::bool_true_name()`'s slot
pub const PIN_BOOL_TRUE: usize = 32;
/// con-leche: none — the arena's own pin table; `core_k::bool_false_name()`'s slot
pub const PIN_BOOL_FALSE: usize = 33;

// `cstd` (`con_ron_core::kernel::std_axioms`)
/// con-leche: none — the arena's own pin table; `cstd::propext_name()`'s slot
pub const PIN_PROPEXT: usize = 34;
/// con-leche: none — the arena's own pin table; `cstd::choice_name()`'s slot
pub const PIN_CHOICE: usize = 35;
/// con-leche: none — the arena's own pin table; `cstd::iff_name()`'s slot
pub const PIN_IFF: usize = 36;
/// con-leche: none — the arena's own pin table; `cstd::iff_intro_name()`'s slot
pub const PIN_IFF_INTRO: usize = 37;
/// con-leche: none — the arena's own pin table; `cstd::iff_rec_name()`'s slot
pub const PIN_IFF_REC: usize = 38;
/// con-leche: none — the arena's own pin table; `cstd::nonempty_name()`'s slot
pub const PIN_NONEMPTY: usize = 39;
/// con-leche: none — the arena's own pin table; `cstd::nonempty_intro_name()`'s slot
pub const PIN_NONEMPTY_INTRO: usize = 40;
/// con-leche: none — the arena's own pin table; `cstd::nonempty_rec_name()`'s slot
pub const PIN_NONEMPTY_REC: usize = 41;

// `ctrust` (`con_ron_core::kernel::trust_axioms`)
/// con-leche: none — the arena's own pin table; `ctrust::true_name()`'s slot
pub const PIN_TRUE: usize = 42;
/// con-leche: none — the arena's own pin table; `ctrust::true_intro_name()`'s slot
pub const PIN_TRUE_INTRO: usize = 43;
/// con-leche: none — the arena's own pin table; `ctrust::trust_compiler_name()`'s slot
pub const PIN_TRUST_COMPILER: usize = 44;
/// con-leche: none — the arena's own pin table; `ctrust::reduce_nat_name()`'s slot
pub const PIN_REDUCE_NAT: usize = 45;
/// con-leche: none — the arena's own pin table; `ctrust::reduce_bool_name()`'s slot
pub const PIN_REDUCE_BOOL: usize = 46;
/// con-leche: none — the arena's own pin table; `ctrust::of_reduce_nat_name()`'s slot
pub const PIN_OF_REDUCE_NAT: usize = 47;
/// con-leche: none — the arena's own pin table; `ctrust::of_reduce_bool_name()`'s slot
pub const PIN_OF_REDUCE_BOOL: usize = 48;

// ---------------------------------------------------------------------------
// The record
// ---------------------------------------------------------------------------

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3, task #97c)
/// The interned reserved constants, in `AState` for the run's lifetime.
///
/// `names` is `PIN_COUNT` long once `intern_reserved_pins` has run and EMPTY
/// before it, which is the whole of the initialisation-order argument in the
/// module note.  The other three are the interned values the name pins are
/// used with: `empty_levels` is `intern_ls_node []`, `zero_level` is the
/// level `0` and `sort_one` is `Sort 1` — `arena::core`'s three nullary
/// interns, which every `const_e` and every `Level.isEquiv u .zero` calls.
/// They are handles into the same persistent tier, so `Pins::empty`'s `0`
/// words are as unusable as an empty `names`: nothing reads them without
/// having read a name pin first, and `arena::core` guards its three readers
/// on `names.len()` through `pin_ready`.
pub struct Pins {
    /// The `PIN_COUNT` reserved-name handles, indexed by the `PIN_*` slots.
    pub names: Vec<NIdx>,
    /// `basis_names::reserved_basis_names()`, interned: the nineteen names a
    /// stream may not declare.  Its own list rather than nineteen slots of
    /// `names`, because its only reader wants the whole vector
    /// (`nidx_contains_from`) and because five of the nineteen are `rec_of`
    /// forms that nothing else pins.
    pub reserved: Vec<NIdx>,
    /// `arena::core::empty_levels`: the empty universe-argument list.
    pub empty_levels: LsIdx,
    /// `arena::core::zero_level`: the level `0`.
    pub zero_level: LIdx,
    /// `arena::core::sort_one`: the expression `Sort 1`.
    pub sort_one: EIdx,
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3, task #97c)
/// The unfilled table: `AState::init`'s value, and the one `pin_at` refuses.
impl Pins {
    /// con-leche: none — the arena's own pin table (DESIGN.md §8.3, task #97c)
    /// `Vec::new` allocates nothing (task #35), so this is four words.
    pub fn empty() -> Pins {
        Pins {
            names: Vec::new(),
            reserved: Vec::new(),
            empty_levels: LsIdx::of_word(0),
            zero_level: LIdx::of_word(0),
            sort_one: EIdx::of_word(0),
        }
    }
}

// ---------------------------------------------------------------------------
// Filling the table
// ---------------------------------------------------------------------------

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3, task #97c)
/// The forty-nine reserved names as VALUES, in `PIN_*` order.  This is the
/// one place they are built, and it runs once per process.
///
/// Spelled as pushes rather than a `vec![…]` literal because the extraction
/// takes the pushes as they are; the order is the `PIN_*` constants', which
/// `pins_table_is_in_slot_order` in this module's tests checks name by name.
pub fn pin_names() -> Vec<Name> {
    let mut out: Vec<Name> = Vec::new();
    out.push(basis_names::eq_name());
    out.push(basis_names::punit_name());
    out.push(basis_names::punit_rec_name());
    out.push(basis_names::nat_name());
    out.push(basis_names::nat_zero_name());
    out.push(basis_names::nat_succ_name());
    out.push(basis_names::quot_sound_name());
    out.push(basis_names::string_name());
    out.push(basis_names::string_of_list_name());
    out.push(basis_names::list_name());
    out.push(basis_names::list_nil_name());
    out.push(basis_names::list_cons_name());
    out.push(basis_names::char_name());
    out.push(basis_names::and_name());
    out.push(basis_names::char_of_nat_name());
    out.push(basis_names::sorry_ax_name());
    out.push(core_k::nat_pred_name());
    out.push(core_k::nat_add_name());
    out.push(core_k::nat_sub_name());
    out.push(core_k::nat_mul_name());
    out.push(core_k::nat_pow_name());
    out.push(core_k::nat_beq_name());
    out.push(core_k::nat_ble_name());
    out.push(core_k::nat_div_name());
    out.push(core_k::nat_mod_name());
    out.push(core_k::nat_gcd_name());
    out.push(core_k::nat_land_name());
    out.push(core_k::nat_lor_name());
    out.push(core_k::nat_xor_name());
    out.push(core_k::nat_shift_left_name());
    out.push(core_k::nat_shift_right_name());
    out.push(core_k::bool_name());
    out.push(core_k::bool_true_name());
    out.push(core_k::bool_false_name());
    out.push(cstd::propext_name());
    out.push(cstd::choice_name());
    out.push(cstd::iff_name());
    out.push(cstd::iff_intro_name());
    out.push(cstd::iff_rec_name());
    out.push(cstd::nonempty_name());
    out.push(cstd::nonempty_intro_name());
    out.push(cstd::nonempty_rec_name());
    out.push(ctrust::true_name());
    out.push(ctrust::true_intro_name());
    out.push(ctrust::trust_compiler_name());
    out.push(ctrust::reduce_nat_name());
    out.push(ctrust::reduce_bool_name());
    out.push(ctrust::of_reduce_nat_name());
    out.push(ctrust::of_reduce_bool_name());
    out
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3, task #97c)
/// Intern every reserved constant into the store, ONCE, and install the
/// table.  The driver calls this immediately after `AState::init` and before
/// the prelude, so the scratch tier is closed and every handle below is
/// persistent (the module note says why that matters).
///
/// Lean twin: `proof/ConRon/Arena/Pins.lean:224-239 internReservedPins` —
/// `internAllPins : AM Unit`, the same sequence.
pub fn intern_reserved_pins(pers: &PersTier, st: &mut AState) -> Result<(), CheckError> {
    match intern_name_list(pers, st, &pin_names()) {
        Err(e) => Err(e),
        Ok(hs) => match intern_name_list(pers, st, &basis_names::reserved_basis_names()) {
        Err(e) => Err(e),
        Ok(rs) => match intern_ls_node(pers, st, Vec::new()) {
            Err(e) => Err(e),
            Ok(us) => match intern_l_node(pers, st, LNodeView::Zero) {
                Err(e) => Err(e),
                Ok(z) => match intern_l_node(pers, st, LNodeView::Succ(z.dup2())) {
                    Err(e) => Err(e),
                    Ok(o) => match intern_e_sort(pers, st, o) {
                        Err(e) => Err(e),
                        Ok(s1) => {
                            st.pins = Pins {
                                names: hs,
                                reserved: rs,
                                empty_levels: us,
                                zero_level: z,
                                sort_one: s1,
                            };
                            Ok(())
                        }
                    },
                },
            },
        },
        },
    }
}

// ---------------------------------------------------------------------------
// Reading the table
// ---------------------------------------------------------------------------

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3, task #97c)
/// Has `intern_reserved_pins` run?  The three value pins (`empty_levels`,
/// `zero_level`, `sort_one`) have no bound of their own, so their readers
/// test this.
pub fn pins_ready(st: &AState) -> bool {
    st.pins.names.len() == PIN_COUNT
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3, task #97c)
/// The nineteen reserved basis names, off the table.  `arena::core`'s
/// `reserved_basis_names` used to build and intern all nineteen on every
/// call, which task #97-P6-4a's profile put at 1.1 % of `Init`'s cycles in
/// the `Name` construction alone; its readers copy the vector.
pub fn pin_reserved(st: &AState) -> Result<Vec<NIdx>, CheckError> {
    if pins_ready(st) {
        Ok(nidx_vec_dup(&st.pins.reserved))
    } else {
        fail(CheckError::Internal(code_points(&M_PINS_UNSET)))
    }
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3, task #97c)
/// One pinned name handle.  The bounds branch is task #97c's hazard, turned
/// into a stop: an unfilled table is empty, so a pin read before the driver's
/// `intern_reserved_pins` raises `Internal` rather than answering with a word that
/// happens to parse as a handle.
pub fn pin_at(st: &AState, i: usize) -> Result<NIdx, CheckError> {
    if i >= st.pins.names.len() {
        fail(CheckError::Internal(code_points(&M_PINS_UNSET)))
    } else {
        Ok(st.pins.names[i].dup2())
    }
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3, task #97c)
/// The empty universe-argument list, off the table.
pub fn pin_empty_levels(st: &AState) -> Result<LsIdx, CheckError> {
    if pins_ready(st) {
        Ok(st.pins.empty_levels.dup2())
    } else {
        fail(CheckError::Internal(code_points(&M_PINS_UNSET)))
    }
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3, task #97c)
/// The level `0`, off the table.
pub fn pin_zero_level(st: &AState) -> Result<LIdx, CheckError> {
    if pins_ready(st) {
        Ok(st.pins.zero_level.dup2())
    } else {
        fail(CheckError::Internal(code_points(&M_PINS_UNSET)))
    }
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3, task #97c)
/// The expression `Sort 1`, off the table.
pub fn pin_sort_one(st: &AState) -> Result<EIdx, CheckError> {
    if pins_ready(st) {
        Ok(st.pins.sort_one.dup2())
    } else {
        fail(CheckError::Internal(code_points(&M_PINS_UNSET)))
    }
}

// ---------------------------------------------------------------------------
// The forty-nine named readers: one per `PIN_*` slot
// ---------------------------------------------------------------------------

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `basis_names::eq_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_eq(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_EQ)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `basis_names::punit_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_punit(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_PUNIT)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `basis_names::punit_rec_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_punit_rec(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_PUNIT_REC)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `basis_names::nat_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nat(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NAT)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `basis_names::nat_zero_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nat_zero(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NAT_ZERO)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `basis_names::nat_succ_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nat_succ(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NAT_SUCC)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `basis_names::quot_sound_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_quot_sound(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_QUOT_SOUND)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `basis_names::string_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_string(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_STRING)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `basis_names::string_of_list_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_string_of_list(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_STRING_OF_LIST)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `basis_names::list_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_list(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_LIST)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `basis_names::list_nil_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_list_nil(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_LIST_NIL)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `basis_names::list_cons_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_list_cons(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_LIST_CONS)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `basis_names::char_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_char(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_CHAR)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `basis_names::and_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_and(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_AND)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `basis_names::char_of_nat_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_char_of_nat(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_CHAR_OF_NAT)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `basis_names::sorry_ax_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_sorry_ax(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_SORRY_AX)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `core_k::nat_pred_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nat_pred(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NAT_PRED)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `core_k::nat_add_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nat_add(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NAT_ADD)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `core_k::nat_sub_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nat_sub(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NAT_SUB)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `core_k::nat_mul_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nat_mul(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NAT_MUL)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `core_k::nat_pow_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nat_pow(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NAT_POW)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `core_k::nat_beq_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nat_beq(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NAT_BEQ)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `core_k::nat_ble_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nat_ble(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NAT_BLE)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `core_k::nat_div_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nat_div(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NAT_DIV)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `core_k::nat_mod_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nat_mod(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NAT_MOD)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `core_k::nat_gcd_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nat_gcd(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NAT_GCD)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `core_k::nat_land_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nat_land(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NAT_LAND)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `core_k::nat_lor_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nat_lor(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NAT_LOR)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `core_k::nat_xor_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nat_xor(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NAT_XOR)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `core_k::nat_shift_left_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nat_shift_left(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NAT_SHIFT_LEFT)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `core_k::nat_shift_right_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nat_shift_right(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NAT_SHIFT_RIGHT)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `core_k::bool_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_bool(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_BOOL)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `core_k::bool_true_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_bool_true(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_BOOL_TRUE)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `core_k::bool_false_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_bool_false(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_BOOL_FALSE)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `cstd::propext_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_propext(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_PROPEXT)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `cstd::choice_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_choice(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_CHOICE)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `cstd::iff_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_iff(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_IFF)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `cstd::iff_intro_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_iff_intro(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_IFF_INTRO)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `cstd::iff_rec_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_iff_rec(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_IFF_REC)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `cstd::nonempty_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nonempty(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NONEMPTY)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `cstd::nonempty_intro_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nonempty_intro(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NONEMPTY_INTRO)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `cstd::nonempty_rec_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_nonempty_rec(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_NONEMPTY_REC)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `ctrust::true_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_true(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_TRUE)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `ctrust::true_intro_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_true_intro(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_TRUE_INTRO)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `ctrust::trust_compiler_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_trust_compiler(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_TRUST_COMPILER)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `ctrust::reduce_nat_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_reduce_nat(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_REDUCE_NAT)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `ctrust::reduce_bool_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_reduce_bool(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_REDUCE_BOOL)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `ctrust::of_reduce_nat_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_of_reduce_nat(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_OF_REDUCE_NAT)
}

/// con-leche: none — the arena's own pin table (DESIGN.md §8.3)
/// `ctrust::of_reduce_bool_name()`'s handle, off the record `intern_reserved_pins` filled.
pub fn pin_of_reduce_bool(st: &AState) -> Result<NIdx, CheckError> {
    pin_at(st, PIN_OF_REDUCE_BOOL)
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::arena::core::{drop_scratch, enter_scratch};
    use crate::arena::monad::intern_name;
    use crate::arena::store::EStore;
    use crate::ron::hashmap::Eq2;

    fn ok<T>(r: Result<T, CheckError>) -> T {
        match r {
            Ok(v) => v,
            Err(_) => panic!("pins: unexpected decline"),
        }
    }

    fn pinned() -> AState {
        let pers: &PersTier = &PersTier::empty();
        let mut st = AState::init(EStore::empty());
        ok(intern_reserved_pins(pers, &mut st));
        st
    }

    /// The table and the `PIN_*` constants are one list: slot `i` holds the
    /// name `pin_names()[i]`, which is what makes a mis-numbered constant a
    /// test failure rather than a wrong pin.
    #[test]
    fn pins_table_is_in_slot_order() {
        let pers: &PersTier = &PersTier::empty();
        let ns = pin_names();
        assert_eq!(ns.len(), PIN_COUNT);
        let mut st = pinned();
        let mut i = 0;
        while i < PIN_COUNT {
            let h = ok(pin_at(&st, i));
            let h2 = ok(intern_name(pers, &mut st, &ns[i]));
            assert!(h.eq2(&h2), "slot {} is not its own name", i);
            i += 1;
        }
        assert!(ok(pin_nat(&st)).eq2(&ok(pin_at(&st, PIN_NAT))));
        assert!(ok(pin_nat_zero(&st)).eq2(&ok(pin_at(&st, PIN_NAT_ZERO))));
        assert!(ok(pin_nat_succ(&st)).eq2(&ok(pin_at(&st, PIN_NAT_SUCC))));
        assert!(ok(pin_of_reduce_bool(&st)).eq2(&ok(pin_at(&st, PIN_OF_REDUCE_BOOL))));
    }

    /// Task #97c's hazard, as this module answers it: an unfilled table is a
    /// STOP, not a wrong answer.
    #[test]
    fn an_unfilled_table_declines_rather_than_answering() {
        let st = AState::init(EStore::empty());
        assert!(pin_nat(&st).is_err());
        assert!(pin_at(&st, 0).is_err());
        assert!(pin_empty_levels(&st).is_err());
        assert!(pin_zero_level(&st).is_err());
        assert!(pin_sort_one(&st).is_err());
        assert!(!pins_ready(&st));
    }

    /// The denotation does not move: a pin is the handle `intern_name` of the
    /// same `Name` gives, and interning it again appends nothing.
    #[test]
    fn a_pin_is_what_interning_would_give() {
        let pers: &PersTier = &PersTier::empty();
        let mut st = pinned();
        let before = st.store.ns().node_count(pers);
        let h = ok(intern_name(pers, &mut st, &basis_names::nat_succ_name()));
        assert!(h.eq2(&ok(pin_nat_succ(&st))));
        assert_eq!(st.store.ns().node_count(pers), before);
    }

    /// Every pinned handle is PERSISTENT, so it survives the scratch tier —
    /// which is what every `pin_*` read inside a declaration's check relies
    /// on, and what task #97-P6-1's `pers_find_maybe` rests on.
    #[test]
    fn every_pin_is_persistent_and_survives_the_scratch_tier() {
        let mut st = pinned();
        let mut i = 0;
        while i < PIN_COUNT {
            assert!(ok(pin_at(&st, i)).is_persistent(), "slot {} is scratch", i);
            i += 1;
        }
        assert!(ok(pin_empty_levels(&st)).is_persistent());
        assert!(ok(pin_zero_level(&st)).is_persistent());
        assert!(ok(pin_sort_one(&st)).is_persistent());
        let nat = ok(pin_nat(&st));
        enter_scratch(&mut st);
        assert!(ok(pin_nat(&st)).eq2(&nat));
        drop_scratch(&mut st);
        assert!(ok(pin_nat(&st)).eq2(&nat));
    }

    /// The three value pins are `arena::core`'s three nullary interns.
    #[test]
    fn the_value_pins_are_the_nodes_core_used_to_intern() {
        let pers: &PersTier = &PersTier::empty();
        let mut st = pinned();
        let before = st.store.node_count(pers);
        let us = ok(intern_ls_node(pers, &mut st, Vec::new()));
        let z = ok(intern_l_node(pers, &mut st, LNodeView::Zero));
        let o = ok(intern_l_node(pers, &mut st, LNodeView::Succ(z.dup2())));
        let s1 = ok(intern_e_sort(pers, &mut st, o));
        assert!(us.eq2(&ok(pin_empty_levels(&st))));
        assert!(z.eq2(&ok(pin_zero_level(&st))));
        assert!(s1.eq2(&ok(pin_sort_one(&st))));
        assert_eq!(st.store.node_count(pers), before);
    }
}

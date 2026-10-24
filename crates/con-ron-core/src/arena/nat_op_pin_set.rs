//! `arena::nat_op_pin_set` — one toolchain's `Nat`-operation pins, over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/NatOpPinSet.lean`, which is
//! con-leche's `Kernel/NatOpPinSet.lean` (the record) and
//! `Kernel/NatOpPins.lean` (the `#load_natop_pins` splice that fills it, one
//! variant per committed dump under con-leche's `pins/`).
//!
//! Twenty-four of the record's twenty-five fields carry terms — eight pinned
//! defining expressions, eight certificate-proof lists and eight type-pin
//! lists — so the record is DESIGN.md §8's census class (T) and its twin is
//! the same twenty-five fields with `Expr ↦ EIdx` and `Name ↦ NIdx`.  The pin DATA is `con_ron_core::kernel::nat_op_pins::
//! NatOpPinSet`, which the binary gets by decoding the embedded
//! `kernel::pins_text::PINS_TEXT` (`kernel::pins_decode::decode_embedded`,
//! task #43) — the Rust's answer to con-leche's elaborator splice, and the
//! same values.  DESIGN.md §8.6 P2d says to intern them "into the persistent
//! tier at startup — a one-time tree walk", which is `intern_pin_sets` below,
//! called by `arena::checker`'s `intern_all_pins`.

use crate::arena::handle::{EIdx, NIdx};
use crate::arena::intern::{intern_expr, intern_expr_list};
use crate::arena::monad::{intern_name, AState};
use crate::kernel::core_types::CheckError;
use crate::kernel::expr;
use crate::kernel::expr::Expr;
use crate::kernel::name::Name;
use crate::kernel::nat_op_pins::NatOpPinSet;
use crate::arena::store::PersTier;

/// con-leche: ConLeche/Kernel/NatOpPinSet.lean:35-68 NatOpPinSet
/// Lean twin: `proof/ConRon/Arena/NatOpPinSet.lean:25-59 INatOpPinSet` — the
/// pins of one toolchain: eight pinned defining expressions, eight
/// certificate-proof lists and eight type-pin lists, in the order of
/// `natDivModNames`' family (`div`, `mod`, `gcd`, `land`, `lor`, `xor`,
/// `shiftLeft`, `shiftRight`), plus the toolchain string for diagnostics.  A
/// type pin `(n, ty)` says that the constant `n`, which the operation's
/// certificates use, has type `ty` in that toolchain.  Deviation: `toolchain : String` is a
/// `Vec<u32>` of code points (DESIGN.md §3.3), as con-ron-core's own record's
/// is.
pub struct INatOpPinSet {
    /// The generating toolchain, named in the decline message when no variant
    /// matches.
    pub toolchain: Vec<u32>,
    pub div_pin: EIdx,
    pub mod_pin: EIdx,
    pub gcd_pin: EIdx,
    pub land_pin: EIdx,
    pub lor_pin: EIdx,
    pub xor_pin: EIdx,
    pub shift_left_pin: EIdx,
    pub shift_right_pin: EIdx,
    pub div_proofs: Vec<EIdx>,
    pub mod_proofs: Vec<EIdx>,
    pub gcd_proofs: Vec<EIdx>,
    pub land_proofs: Vec<EIdx>,
    pub lor_proofs: Vec<EIdx>,
    pub xor_proofs: Vec<EIdx>,
    pub shift_left_proofs: Vec<EIdx>,
    pub shift_right_proofs: Vec<EIdx>,
    pub div_type_pins: Vec<(NIdx, EIdx)>,
    pub mod_type_pins: Vec<(NIdx, EIdx)>,
    pub gcd_type_pins: Vec<(NIdx, EIdx)>,
    pub land_type_pins: Vec<(NIdx, EIdx)>,
    pub lor_type_pins: Vec<(NIdx, EIdx)>,
    pub xor_type_pins: Vec<(NIdx, EIdx)>,
    pub shift_left_type_pins: Vec<(NIdx, EIdx)>,
    pub shift_right_type_pins: Vec<(NIdx, EIdx)>,
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// Lean twin: `proof/ConRon/Arena/NatOpPinSet.lean:93-114 internPinSet` —
/// intern one pin variant: the one-time tree walk of DESIGN.md §8.6 P2d,
/// sixteen terms deep.  The twin's sixteen `let`s are sixteen nested matches
/// (§3.4 forbids `?`), split in two so that each half is one expression.
pub fn intern_pin_set(
    pers: &PersTier,
    st: &mut AState,
    ps: &NatOpPinSet,
) -> Result<INatOpPinSet, CheckError> {
    match intern_expr(pers, st, &ps.div_pin) {
        Err(e) => Err(e),
        Ok(dp) => match intern_expr(pers, st, &ps.mod_pin) {
            Err(e) => Err(e),
            Ok(mp) => match intern_expr(pers, st, &ps.gcd_pin) {
                Err(e) => Err(e),
                Ok(gp) => match intern_expr(pers, st, &ps.land_pin) {
                    Err(e) => Err(e),
                    Ok(lap) => match intern_expr(pers, st, &ps.lor_pin) {
                        Err(e) => Err(e),
                        Ok(lop) => match intern_expr(pers, st, &ps.xor_pin) {
                            Err(e) => Err(e),
                            Ok(xp) => match intern_expr(pers, st, &ps.shift_left_pin) {
                                Err(e) => Err(e),
                                Ok(slp) => match intern_expr(pers, st, &ps.shift_right_pin) {
                                    Err(e) => Err(e),
                                    Ok(srp) => intern_pin_set_proofs(
                                        pers,
                                        st, ps, dp, mp, gp, lap, lop, xp, slp, srp,
                                    ),
                                },
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// Lean twin: `proof/ConRon/Arena/NatOpPinSet.lean:93-114 internPinSet` — the
/// eight certificate-proof lists, and the record.  Split at the twin's own
/// `let dc ←` boundary (task #97-P4c's rule for a long `do` block).
pub fn intern_pin_set_proofs(
    pers: &PersTier,
    st: &mut AState,
    ps: &NatOpPinSet,
    dp: EIdx,
    mp: EIdx,
    gp: EIdx,
    lap: EIdx,
    lop: EIdx,
    xp: EIdx,
    slp: EIdx,
    srp: EIdx,
) -> Result<INatOpPinSet, CheckError> {
    match intern_expr_list(pers, st, &ps.div_proofs) {
        Err(e) => Err(e),
        Ok(dc) => match intern_expr_list(pers, st, &ps.mod_proofs) {
            Err(e) => Err(e),
            Ok(mc) => match intern_expr_list(pers, st, &ps.gcd_proofs) {
                Err(e) => Err(e),
                Ok(gc) => match intern_expr_list(pers, st, &ps.land_proofs) {
                    Err(e) => Err(e),
                    Ok(lac) => match intern_expr_list(pers, st, &ps.lor_proofs) {
                        Err(e) => Err(e),
                        Ok(loc) => match intern_expr_list(pers, st, &ps.xor_proofs) {
                            Err(e) => Err(e),
                            Ok(xc) => match intern_expr_list(pers, st, &ps.shift_left_proofs) {
                                Err(e) => Err(e),
                                Ok(slc) => {
                                    match intern_expr_list(pers, st, &ps.shift_right_proofs) {
                                        Err(e) => Err(e),
                                        Ok(src) => intern_pin_set_type_pins(pers, st, ps, INatOpPinSet {
                                            toolchain: expr::str_copy(&ps.toolchain),
                                            div_pin: dp,
                                            mod_pin: mp,
                                            gcd_pin: gp,
                                            land_pin: lap,
                                            lor_pin: lop,
                                            xor_pin: xp,
                                            shift_left_pin: slp,
                                            shift_right_pin: srp,
                                            div_proofs: dc,
                                            mod_proofs: mc,
                                            gcd_proofs: gc,
                                            land_proofs: lac,
                                            lor_proofs: loc,
                                            xor_proofs: xc,
                                            shift_left_proofs: slc,
                                            shift_right_proofs: src,
                                            div_type_pins: Vec::new(),
                                            mod_type_pins: Vec::new(),
                                            gcd_type_pins: Vec::new(),
                                            land_type_pins: Vec::new(),
                                            lor_type_pins: Vec::new(),
                                            xor_type_pins: Vec::new(),
                                            shift_left_type_pins: Vec::new(),
                                            shift_right_type_pins: Vec::new(),
                                        }),
                                    }
                                }
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// Lean twin: `proof/ConRon/Arena/NatOpPinSet.lean:71-91 internPinSetTypePins` —
/// the eight type-pin lists, written into the record the two halves above
/// built (its eight type-pin fields empty until here).
pub fn intern_pin_set_type_pins(
    pers: &PersTier,
    st: &mut AState,
    ps: &NatOpPinSet,
    s: INatOpPinSet,
) -> Result<INatOpPinSet, CheckError> {
    match intern_type_pins(pers, st, &ps.div_type_pins) {
        Err(e) => Err(e),
        Ok(dt) => match intern_type_pins(pers, st, &ps.mod_type_pins) {
            Err(e) => Err(e),
            Ok(mt) => match intern_type_pins(pers, st, &ps.gcd_type_pins) {
                Err(e) => Err(e),
                Ok(gt) => match intern_type_pins(pers, st, &ps.land_type_pins) {
                    Err(e) => Err(e),
                    Ok(lat) => match intern_type_pins(pers, st, &ps.lor_type_pins) {
                        Err(e) => Err(e),
                        Ok(lot) => match intern_type_pins(pers, st, &ps.xor_type_pins) {
                            Err(e) => Err(e),
                            Ok(xt) => match intern_type_pins(pers, st, &ps.shift_left_type_pins) {
                                Err(e) => Err(e),
                                Ok(slt) => {
                                    match intern_type_pins(pers, st, &ps.shift_right_type_pins) {
                                        Err(e) => Err(e),
                                        Ok(srt) => {
                                            let mut s2 = s;
                                            s2.div_type_pins = dt;
                                            s2.mod_type_pins = mt;
                                            s2.gcd_type_pins = gt;
                                            s2.land_type_pins = lat;
                                            s2.lor_type_pins = lot;
                                            s2.xor_type_pins = xt;
                                            s2.shift_left_type_pins = slt;
                                            s2.shift_right_type_pins = srt;
                                            Ok(s2)
                                        }
                                    }
                                }
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// Lean twin: `proof/ConRon/Arena/NatOpPinSet.lean:61-69 internTypePins` — one
/// type-pin list: each name and each type interned, in list order.
pub fn intern_type_pins(
    pers: &PersTier,
    st: &mut AState,
    tps: &Vec<(Name, Expr)>,
) -> Result<Vec<(NIdx, EIdx)>, CheckError> {
    intern_type_pins_go(pers, st, tps, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// Lean twin: `proof/ConRon/Arena/NatOpPinSet.lean:61-69 internTypePins` — the
/// `List` recursion of the twin, as a cursor over the `Vec` (DESIGN.md §3.4's
/// standing rule).
pub fn intern_type_pins_go(
    pers: &PersTier,
    st: &mut AState,
    tps: &Vec<(Name, Expr)>,
    i: usize,
    out: Vec<(NIdx, EIdx)>,
) -> Result<Vec<(NIdx, EIdx)>, CheckError> {
    if i >= tps.len() {
        Ok(out)
    } else {
        match intern_name(pers, st, &tps[i].0) {
            Err(e) => Err(e),
            Ok(n) => match intern_expr(pers, st, &tps[i].1) {
                Err(e) => Err(e),
                Ok(t) => {
                    let mut out2 = out;
                    out2.push((n, t));
                    intern_type_pins_go(pers, st, tps, i + 1, out2)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:75-78 _
/// Lean twin: `proof/ConRon/Arena/NatOpPinSet.lean:116-123 internPinSets` —
/// intern the variant LIST, in the order the install gate tries them.
pub fn intern_pin_sets(
    pers: &PersTier,
    st: &mut AState,
    pss: &Vec<NatOpPinSet>,
    i: usize,
    out: Vec<INatOpPinSet>,
) -> Result<Vec<INatOpPinSet>, CheckError> {
    if i >= pss.len() {
        Ok(out)
    } else {
        match intern_pin_set(pers, st, &pss[i]) {
            Err(e) => Err(e),
            Ok(h) => {
                let mut out2 = out;
                out2.push(h);
                intern_pin_sets(pers, st, pss, i + 1, out2)
            }
        }
    }
}

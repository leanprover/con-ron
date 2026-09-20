//! `arena::nat_op_pin_set` — one toolchain's `Nat`-operation pins, over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/NatOpPinSet.lean`, which is
//! con-leche's `Kernel/NatOpPinSet.lean` (the record) and
//! `Kernel/NatOpPins.lean` (the `#load_natop_pins` splice that fills it, one
//! variant per committed dump under con-leche's `pins/`).
//!
//! Sixteen of the record's seventeen fields carry terms — eight pinned
//! defining expressions and eight certificate-proof lists — so the record is
//! DESIGN.md §8's census class (T) and its twin is the same seventeen fields
//! with `Expr ↦ EIdx`.  The pin DATA is `con_ron_core::kernel::nat_op_pins::
//! NatOpPinSet`, which the binary gets by decoding the embedded
//! `kernel::pins_text::PINS_TEXT` (`kernel::pins_decode::decode_embedded`,
//! task #43) — the Rust's answer to con-leche's elaborator splice, and the
//! same values.  DESIGN.md §8.6 P2d says to intern them "into the persistent
//! tier at startup — a one-time tree walk", which is `intern_pin_sets` below,
//! called by `arena::checker`'s `intern_all_pins`.

use crate::arena::handle::EIdx;
use crate::arena::intern::{intern_expr, intern_expr_list};
use crate::arena::monad::AState;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::expr;
use con_ron_core::kernel::nat_op_pins::NatOpPinSet;

/// con-leche: ConLeche/Kernel/NatOpPinSet.lean:28-51 NatOpPinSet
/// Lean twin: `proof/ConRon/Arena/NatOpPinSet.lean:29-48 INatOpPinSet` — the
/// pins of one toolchain: eight pinned defining expressions and eight
/// certificate-proof lists, in the order of `natDivModNames`' family (`div`,
/// `mod`, `gcd`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`), plus the
/// toolchain string for diagnostics.  Deviation: `toolchain : String` is a
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
}

/// con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
/// Lean twin: `proof/ConRon/Arena/NatOpPinSet.lean:52-70 internPinSet` —
/// intern one pin variant: the one-time tree walk of DESIGN.md §8.6 P2d,
/// sixteen terms deep.  The twin's sixteen `let`s are sixteen nested matches
/// (§3.4 forbids `?`), split in two so that each half is one expression.
pub fn intern_pin_set(
    st: &mut AState,
    ps: &NatOpPinSet,
) -> Result<INatOpPinSet, CheckError> {
    match intern_expr(st, &ps.div_pin) {
        Err(e) => Err(e),
        Ok(dp) => match intern_expr(st, &ps.mod_pin) {
            Err(e) => Err(e),
            Ok(mp) => match intern_expr(st, &ps.gcd_pin) {
                Err(e) => Err(e),
                Ok(gp) => match intern_expr(st, &ps.land_pin) {
                    Err(e) => Err(e),
                    Ok(lap) => match intern_expr(st, &ps.lor_pin) {
                        Err(e) => Err(e),
                        Ok(lop) => match intern_expr(st, &ps.xor_pin) {
                            Err(e) => Err(e),
                            Ok(xp) => match intern_expr(st, &ps.shift_left_pin) {
                                Err(e) => Err(e),
                                Ok(slp) => match intern_expr(st, &ps.shift_right_pin) {
                                    Err(e) => Err(e),
                                    Ok(srp) => intern_pin_set_proofs(
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

/// con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
/// Lean twin: `proof/ConRon/Arena/NatOpPinSet.lean:52-70 internPinSet` — the
/// eight certificate-proof lists, and the record.  Split at the twin's own
/// `let dc ←` boundary (task #97-P4c's rule for a long `do` block).
pub fn intern_pin_set_proofs(
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
    match intern_expr_list(st, &ps.div_proofs) {
        Err(e) => Err(e),
        Ok(dc) => match intern_expr_list(st, &ps.mod_proofs) {
            Err(e) => Err(e),
            Ok(mc) => match intern_expr_list(st, &ps.gcd_proofs) {
                Err(e) => Err(e),
                Ok(gc) => match intern_expr_list(st, &ps.land_proofs) {
                    Err(e) => Err(e),
                    Ok(lac) => match intern_expr_list(st, &ps.lor_proofs) {
                        Err(e) => Err(e),
                        Ok(loc) => match intern_expr_list(st, &ps.xor_proofs) {
                            Err(e) => Err(e),
                            Ok(xc) => match intern_expr_list(st, &ps.shift_left_proofs) {
                                Err(e) => Err(e),
                                Ok(slc) => {
                                    match intern_expr_list(st, &ps.shift_right_proofs) {
                                        Err(e) => Err(e),
                                        Ok(src) => Ok(INatOpPinSet {
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

/// con-leche: ConLeche/Kernel/NatOpPins.lean:62-65 _
/// Lean twin: `proof/ConRon/Arena/NatOpPinSet.lean:74-79 internPinSets` —
/// intern the variant LIST, in the order the install gate tries them.
pub fn intern_pin_sets(
    st: &mut AState,
    pss: &Vec<NatOpPinSet>,
    i: usize,
    out: Vec<INatOpPinSet>,
) -> Result<Vec<INatOpPinSet>, CheckError> {
    if i >= pss.len() {
        Ok(out)
    } else {
        match intern_pin_set(st, &pss[i]) {
            Err(e) => Err(e),
            Ok(h) => {
                let mut out2 = out;
                out2.push(h);
                intern_pin_sets(st, pss, i + 1, out2)
            }
        }
    }
}

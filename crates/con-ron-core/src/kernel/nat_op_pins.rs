//! `ConLeche/Kernel/NatOpPinSet.lean` and `ConLeche/Kernel/NatOpPins.lean` —
//! one toolchain's `Nat`-operation pins, and where the list of committed
//! variants comes from.
//!
//! A **pin variant** carries, per pin-certified WF-recursive `Nat` operation
//! (`Nat.div`, `Nat.mod`, `gcd`, `land`, `lor`, `xor`, `shiftLeft`,
//! `shiftRight`), that toolchain's pinned defining expression and its
//! certificate proof blobs.  The install gate
//! (`checker::check_div_mod_pin_loop`) tries the variants in order and
//! enables the operation's literal fast path on the first whose guards pass,
//! whose pin is definitionally equal to the stream's stored value and whose
//! certificates check.  The certificate *statements* the proofs are checked
//! against are hand-pinned in `checker::div_mod_cert_stmts` and shared by
//! every variant.
//!
//! **Two Lean files, one Rust module.**  `NatOpPinSet.lean` is the record and
//! `NatOpPins.lean` the generated list; the list is meaningless without the
//! record and the record has no other consumer, so they share a module
//! (DESIGN.md §3.1's one-module-per-file rule bent once, recorded here).
//!
//! **The list is a *parameter*, not a constant here** (DESIGN.md §3.6's
//! runtime-data decision; task #31 landed it).  con-leche splices
//! `natOpPinSets` (`NatOpPins.lean:61`) out of the committed `pins/*.json`
//! dumps with an elaboration-time command and reads it as a global inside
//! `checkDivModPin`.  The port cannot: the table is ~26 500 nodes and Charon
//! OOMs on the generated Rust (task #22 measured it).  It does not have to
//! either — every pin is re-checked by `isDefEq` against the stream's own
//! stored value and every certificate proof is kernel-checked against
//! `div_mod_cert_stmts`, so the list is a *hint* list whose only effect is on
//! completeness.  So `cached::installed::check_decls` takes it as
//! `pins : &Vec<NatOpPinSet>` and threads it down to the loop, and the
//! unverified driver (`con-ron-check --pins FILE`, format `con-ron-pins/1`,
//! `proof/ConRon/Dump/FORMAT.md` §7) is what reads con-leche's own value out
//! of a dump.  **This module therefore declares the record and nothing else**:
//! there is no `nat_op_pin_sets()` (§3.4 forbids the global, and the data is
//! not code).  The upstream change this asks for is `checkDecls mode pins ds`.

use crate::kernel::expr::Expr;
use std::vec::Vec;

/// con-leche: ConLeche/Kernel/NatOpPinSet.lean:28-51 NatOpPinSet
/// The pins of one toolchain: eight pinned defining expressions and eight
/// certificate-proof lists, in the order of `natDivModNames`' family, plus
/// the toolchain string for diagnostics.  Deviation: `toolchain : String` is
/// a `Vec<u32>` of code points (DESIGN.md §3.3).
pub struct NatOpPinSet {
    pub toolchain: Vec<u32>,
    pub div_pin: Expr,
    pub mod_pin: Expr,
    pub gcd_pin: Expr,
    pub land_pin: Expr,
    pub lor_pin: Expr,
    pub xor_pin: Expr,
    pub shift_left_pin: Expr,
    pub shift_right_pin: Expr,
    pub div_proofs: Vec<Expr>,
    pub mod_proofs: Vec<Expr>,
    pub gcd_proofs: Vec<Expr>,
    pub land_proofs: Vec<Expr>,
    pub lor_proofs: Vec<Expr>,
    pub xor_proofs: Vec<Expr>,
    pub shift_left_proofs: Vec<Expr>,
    pub shift_right_proofs: Vec<Expr>,
}

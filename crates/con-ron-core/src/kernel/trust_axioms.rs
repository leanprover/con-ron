//! `ConLeche/Kernel/TrustAxioms.lean` — the compiler-trust axiom family
//! (con-leche task #95).
//!
//! `Init`'s compiler-trust scaffolding is *installed* rather than
//! taint-skipped:
//!
//! * `Lean.trustCompiler : True` is trivially realizable — installed as an
//!   opaque with value `True.intro` over a pinned `True` family.
//! * `Lean.reduceNat` / `Lean.reduceBool` check as ordinary opaques and their
//!   stored values are pinned against the identity function
//!   (`kernel::trust_pins`) by definitional equality: drift declines, never
//!   silently.
//! * `Lean.ofReduceNat` / `Lean.ofReduceBool` are pinned axioms over those
//!   stored opaques.  With the reduce operation certified to be the identity
//!   at its own install (`checker::check_reduce_pin`), `∀ a b, reduce a = b →
//!   a = b` interprets to an inhabited proposition — the hypothesis *is* the
//!   conclusion.
//!
//! `sorryAx` remains the only tolerated (skip-taint) axiom
//! (`std_axioms::tolerated_axiom_names`).
//!
//! **The pins.**  `reduceNatCvA`, `reduceBoolCvA`, `ofReduceNatA` and
//! `ofReduceBoolA` are `reduceOpRaw` / `ofReduceRaw` at the two names (since
//! con-leche's task #342 there is no annotated form), and every consumer
//! reads them through `ConstantVal.matchesPin`, which is plain equality.
//! `natA` in `reduce_elem_ok` is compared by exact `ConstantInfo` equality —
//! `kernel::basis_pins`' stub.
//!
//! The `Env`/`FEnv` twins (`trustCompilerOkF`, `reduceStoredOkF`,
//! `reduceElemOkF`, `ofReduceAxOkF`, `reducePinGuardF`) are the same Rust
//! functions with a second citation: the port has one environment spelling,
//! the index (task #18's deviation 3).

use crate::kernel::basis_builder;
use crate::kernel::basis_names;
use crate::kernel::core_types;
use crate::kernel::core_k;
use crate::kernel::env::ConstantVal;
use crate::kernel::expr;
use crate::kernel::expr::Expr;
use crate::kernel::level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::std_axioms;
use crate::frontend::text;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// The pinned names (`TrustAxioms.lean:49-75`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:49-50 trueName
/// The name `True`.
pub fn true_name() -> Name {
    name::mk_str(name::anonymous(), { const S: [u32; 4] = [84, 114, 117, 101]; core_types::code_points(&S) })
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:52-53 trueIntroName
/// The name `True.intro`.
pub fn true_intro_name() -> Name {
    name::mk_str(true_name(), { const S: [u32; 5] = [105, 110, 116, 114, 111]; core_types::code_points(&S) })
}

/// con-leche: none — the `Lean` namespace prefix of the compiler-trust family
/// There is no declaration to cite: `ConLeche/Kernel/TrustAxioms.lean:56-68`
/// spells `(anonymous |>.str "Lean")` inline in each of the five `Lean.*`
/// names below (`trustCompilerName`, `reduceNatName`, `reduceBoolName`,
/// `ofReduceNatName`, `ofReduceBoolName`), so the port factors the shared
/// prefix out and `Refine/TrustAxioms.lean`'s `lean_ns_refines` states it
/// against that prefix (task #56's deviation 3, closed at task #58).
pub fn lean_ns() -> Name {
    name::mk_str(name::anonymous(), { const S: [u32; 4] = [76, 101, 97, 110]; core_types::code_points(&S) })
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:55-56 trustCompilerName
/// The name `Lean.trustCompiler`.
pub fn trust_compiler_name() -> Name {
    name::mk_str(
        lean_ns(),
        { const S: [u32; 13] = [116, 114, 117, 115, 116, 67, 111, 109, 112, 105, 108, 101, 114]; core_types::code_points(&S) },
    )
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:58-59 reduceNatName
/// The name `Lean.reduceNat`.
pub fn reduce_nat_name() -> Name {
    name::mk_str(
        lean_ns(),
        { const S: [u32; 9] = [114, 101, 100, 117, 99, 101, 78, 97, 116]; core_types::code_points(&S) },
    )
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:61-62 reduceBoolName
/// The name `Lean.reduceBool`.
pub fn reduce_bool_name() -> Name {
    name::mk_str(
        lean_ns(),
        { const S: [u32; 10] = [114, 101, 100, 117, 99, 101, 66, 111, 111, 108]; core_types::code_points(&S) },
    )
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:64-65 ofReduceNatName
/// The name `Lean.ofReduceNat`.
pub fn of_reduce_nat_name() -> Name {
    name::mk_str(
        lean_ns(),
        { const S: [u32; 11] = [111, 102, 82, 101, 100, 117, 99, 101, 78, 97, 116]; core_types::code_points(&S) },
    )
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:67-68 ofReduceBoolName
/// The name `Lean.ofReduceBool`.
pub fn of_reduce_bool_name() -> Name {
    name::mk_str(
        lean_ns(),
        { const S: [u32; 12] = [111, 102, 82, 101, 100, 117, 99, 101, 66, 111, 111, 108]; core_types::code_points(&S) },
    )
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:73-75 ofReduceOp
/// The reduce operation an `ofReduce*` axiom speaks about.
pub fn of_reduce_op(n: &Name) -> Name {
    if name::beq(n, &of_reduce_nat_name()) {
        reduce_nat_name()
    } else {
        reduce_bool_name()
    }
}

// ---------------------------------------------------------------------------
// The pinned shapes (`TrustAxioms.lean:77-152`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:83-84 trueCvA
/// Pinned `True` (shape only; capabilities are not pinned).
pub fn true_cv_a() -> ConstantVal {
    ConstantVal {
        name: true_name(),
        level_params: Vec::new(),
        ty: expr::sort(level::zero()),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:86-87 trueIntroCvA
/// Pinned `True.intro`.
pub fn true_intro_cv_a() -> ConstantVal {
    ConstantVal {
        name: true_intro_name(),
        level_params: Vec::new(),
        ty: expr::mk_const(true_name(), Vec::new()),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:89-90 trustCompilerA
/// Pinned `Lean.trustCompiler`.
pub fn trust_compiler_a() -> ConstantVal {
    ConstantVal {
        name: trust_compiler_name(),
        level_params: Vec::new(),
        ty: expr::mk_const(true_name(), Vec::new()),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:92-93 boolCvA
/// Pinned `Bool` (shape only).
pub fn bool_cv_a() -> ConstantVal {
    ConstantVal {
        name: core_k::bool_name(),
        level_params: Vec::new(),
        ty: expr::sort(level::succ(level::zero())),
    }
}


/// con-leche: ConLeche/Kernel/TrustAxioms.lean:99-101 reduceElemTy
/// The element type of a reduce operation, as the pinned constant.
pub fn reduce_elem_ty(c: &Name) -> Expr {
    if name::beq(c, &reduce_nat_name()) {
        expr::mk_const(basis_names::nat_name(), Vec::new())
    } else {
        expr::mk_const(core_k::bool_name(), Vec::new())
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:103-105 reduceOpRaw
/// Raw pinned type of `Lean.reduceNat` / `Lean.reduceBool`: `∀ (n : τ), τ`.
pub fn reduce_op_raw(c: &Name) -> ConstantVal {
    ConstantVal {
        name: name::dup(c),
        level_params: Vec::new(),
        ty: basis_builder::pi(reduce_elem_ty(c), reduce_elem_ty(c)),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:107-117 ofReduceRaw
/// Raw pinned type of `Lean.ofReduceNat` / `Lean.ofReduceBool`:
/// `∀ (a b : τ), reduce a = b → a = b` at `τ = Nat` / `Bool`.
pub fn of_reduce_raw(n: &Name) -> ConstantVal {
    let c: Name = of_reduce_op(n);
    ConstantVal {
        name: name::dup(n),
        level_params: Vec::new(),
        ty: basis_builder::pi(
            reduce_elem_ty(&c),
            basis_builder::pi(
                reduce_elem_ty(&c),
                basis_builder::pi(
                    eq_app(
                        &c,
                        expr::app(
                            basis_builder::cnst(name::dup(&c), Vec::new()),
                            basis_builder::bv(1),
                        ),
                        basis_builder::bv(0),
                    ),
                    eq_app(&c, basis_builder::bv(2), basis_builder::bv(1)),
                ),
            ),
        ),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:107-117 ofReduceRaw
/// `ofReduceRaw`'s local `eqApp` — `Eq.{1} τ x y` at the operation's element
/// type.  A local lambda in the Lean, a named function here (DESIGN.md §3.4
/// forbids closures; task #18's point 5).
pub fn eq_app(c: &Name, x: Expr, y: Expr) -> Expr {
    basis_builder::ap3(
        basis_builder::cnst(basis_names::eq_name(), std_axioms::one_level()),
        reduce_elem_ty(c),
        x,
        y,
    )
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:119-120 reduceNatCvA
/// Pinned `Lean.reduceNat`.
pub fn reduce_nat_cv_a() -> ConstantVal {
    reduce_op_raw(&reduce_nat_name())
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:122-123 reduceBoolCvA
/// Pinned `Lean.reduceBool`.
pub fn reduce_bool_cv_a() -> ConstantVal {
    reduce_op_raw(&reduce_bool_name())
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:125-126 ofReduceNatA
/// Pinned `Lean.ofReduceNat`.
pub fn of_reduce_nat_a() -> ConstantVal {
    of_reduce_raw(&of_reduce_nat_name())
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:128-129 ofReduceBoolA
/// Pinned `Lean.ofReduceBool`.
pub fn of_reduce_bool_a() -> ConstantVal {
    of_reduce_raw(&of_reduce_bool_name())
}

// ---------------------------------------------------------------------------
// The environment predicates (`TrustAxioms.lean:154-196`)
// ---------------------------------------------------------------------------







// ---------------------------------------------------------------------------
// The reduce-operation install pin (`TrustAxioms.lean:198-216`)
// ---------------------------------------------------------------------------




// ---------------------------------------------------------------------------
// The non-standard-axiom decline (`TrustAxioms.lean:203-224`)
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"_native"`, as code points: the name component `Lean.Meta.nativeEqTrue`
/// puts between the declaration and the tactic.
pub const S_NATIVE: [u32; 7] = [95, 110, 97, 116, 105, 118, 101];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"ax"`, as code points: the prefix of the axiom's own component.
pub const S_AX: [u32; 2] = [97, 120];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"decide"`, as code points: the tactic name `decide +native` passes.
pub const S_DECIDE: [u32; 6] = [100, 101, 99, 105, 100, 101];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"decide +native"`, as code points.
pub const S_DECIDE_NATIVE: [u32; 14] =
    [100, 101, 99, 105, 100, 101, 32, 43, 110, 97, 116, 105, 118, 101];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"non-standard axiom ("`, as code points: the decline message up to the
/// axiom's name.
pub const M_NONSTD_PRE: [u32; 20] = [
    110, 111, 110, 45, 115, 116, 97, 110, 100, 97, 114, 100, 32, 97, 120, 105, 111, 109, 32, 40,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// ``"), apparently added by the `"``, as code points: between the name and
/// the tactic.
pub const M_NONSTD_BY: [u32; 28] = [
    41, 44, 32, 97, 112, 112, 97, 114, 101, 110, 116, 108, 121, 32, 97, 100, 100, 101, 100, 32,
    98, 121, 32, 116, 104, 101, 32, 96,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// ``"` tactic; con-leche does not support such axioms at the moment"``, as
/// code points: after the tactic.
pub const M_NONSTD_TAC_END: [u32; 62] = [
    96, 32, 116, 97, 99, 116, 105, 99, 59, 32, 99, 111, 110, 45, 108, 101, 99, 104, 101, 32, 100,
    111, 101, 115, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 32, 115, 117, 99,
    104, 32, 97, 120, 105, 111, 109, 115, 32, 97, 116, 32, 116, 104, 101, 32, 109, 111, 109, 101,
    110, 116,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"); con-leche does not support such axioms at the moment"`, as code
/// points: after the name, when no tactic is recognised.
pub const M_NONSTD_END: [u32; 55] = [
    41, 59, 32, 99, 111, 110, 45, 108, 101, 99, 104, 101, 32, 100, 111, 101, 115, 32, 110, 111,
    116, 32, 115, 117, 112, 112, 111, 114, 116, 32, 115, 117, 99, 104, 32, 97, 120, 105, 111, 109,
    115, 32, 97, 116, 32, 116, 104, 101, 32, 109, 111, 109, 101, 110, 116,
];

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:203-215 nativeAxiomTactic?
/// **The tactic that apparently added an axiom, read off its name.**
/// `Lean.Meta.nativeEqTrue` (the basis of `native_decide`, `decide +native`
/// and `bv_decide`) asserts the result of a compiled computation as an axiom
/// named `<declaration>._native.<tactic>.ax_<i>_<j>`; `decide +native` passes
/// the tactic name `decide`.  The tactic component is returned as displayed
/// (`name::render` of the one-component name), since it is input.  The cited pattern `.str (.str (.str _
/// "_native") tac) ax` is three nested matches here, and its literal
/// comparisons are `text::cps_beq` / `text::cps_starts_with`.
pub fn native_axiom_tactic(n: &Name) -> Option<Vec<u32>> {
    match &n.0.kind {
        name::NameKind::Str(p, ax) => match &p.0.kind {
            name::NameKind::Str(q, tac) => match &q.0.kind {
                name::NameKind::Str(_, nat) => {
                    if text::cps_beq(nat, &S_NATIVE) && text::cps_starts_with(ax, &S_AX) {
                        if text::cps_beq(tac, &S_DECIDE) {
                            Some(core_types::code_points(&S_DECIDE_NATIVE))
                        } else {
                            Some(name::render(&name::mk_str(name::anonymous(), expr::str_copy(tac))))
                        }
                    } else {
                        None
                    }
                }
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:217-225 nonStdAxiomMsg
/// **The decline message for an axiom that is none of the standard axioms,
/// the compiler-trust family and `sorryAx`**: the axiom's name, and the
/// tactic that apparently added it when `native_axiom_tactic` recognises one.
/// The cited `s!` interpolations are `text::cat3` over the code-point
/// constants above, the name rendered by `name::render` (`Name.render`, `ToString Name`).
pub fn non_std_axiom_msg(n: &Name) -> Vec<u32> {
    let head = text::cat(core_types::code_points(&M_NONSTD_PRE), &name::render(n));
    match native_axiom_tactic(n) {
        Some(tac) => text::cat3(
            text::cat(head, &core_types::code_points(&M_NONSTD_BY)),
            &tac,
            &core_types::code_points(&M_NONSTD_TAC_END),
        ),
        None => text::cat(head, &core_types::code_points(&M_NONSTD_END)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cp(t: &str) -> Vec<u32> {
        t.chars().map(|c| c as u32).collect()
    }

    fn s(v: &[u32]) -> String {
        v.iter().filter_map(|c| char::from_u32(*c)).collect()
    }

    /// `<decl>._native.<tac>.<ax>`, con-leche's `nativeAx` test helper.
    fn native_ax(decl: &str, tac: &str, ax: &str) -> Name {
        let d = name::mk_str(name::anonymous(), cp(decl));
        let n = name::mk_str(d, cp("_native"));
        let t = name::mk_str(n, cp(tac));
        name::mk_str(t, cp(ax))
    }

    /// con-leche's `#guard`s on the recogniser (`tests/ConLecheTests.lean`,
    /// task #360): the three tactics, a plain axiom, a `_native…decl` name.
    #[test]
    fn native_axiom_tactic_reads_the_tactic() {
        let t = |n: &Name| native_axiom_tactic(n).map(|v| s(&v));
        assert_eq!(t(&native_ax("nd", "native_decide", "ax_1_1")).as_deref(), Some("native_decide"));
        assert_eq!(t(&native_ax("dn", "decide", "ax_1_1")).as_deref(), Some("decide +native"));
        assert_eq!(t(&native_ax("bv", "bv_decide", "ax_1_5")).as_deref(), Some("bv_decide"));
        assert_eq!(t(&name::mk_str(name::anonymous(), cp("customAx"))), None);
        assert_eq!(t(&native_ax("nd", "native_decide", "decl_1")), None);
    }

    /// The message, exactly con-leche's.
    #[test]
    fn non_std_axiom_msg_is_con_leches() {
        assert_eq!(
            s(&non_std_axiom_msg(&native_ax("nd", "native_decide", "ax_1_1"))),
            "non-standard axiom (nd._native.native_decide.ax_1_1), apparently added by the \
             `native_decide` tactic; con-leche does not support such axioms at the moment"
        );
        assert_eq!(
            s(&non_std_axiom_msg(&name::mk_str(name::anonymous(), cp("myAxiom")))),
            "non-standard axiom (myAxiom); con-leche does not support such axioms at the moment"
        );
        // The `_native` tactic component is input too (DisplayTests.lean, task #365).
        assert_eq!(
            s(&non_std_axiom_msg(&native_ax("f", "evil\n::error::x", "ax_1"))),
            "non-standard axiom (f._native.«evil\\u{000A}::error::x».ax_1), apparently added by the \
             `«evil\\u{000A}::error::x»` tactic; con-leche does not support such axioms at the moment"
        );
    }
}

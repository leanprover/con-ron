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
//! **The pins are the raw ones.**  `reduceNatCvA`, `reduceBoolCvA`,
//! `ofReduceNatA` and `ofReduceBoolA` are computed from `reduceOpRaw` /
//! `ofReduceRaw` at elaboration time by `#annotate_pins`, and every consumer
//! reads them through `ConstantVal.matchesPin`, which erases binder prop-ness
//! data — the only thing annotation changes here.  So `reduce_op_cv_a` and
//! `of_reduce_pin_a` return the **raw** pins and carry the annotated twins'
//! citation; `std_axioms`' module note has the argument in full.  The one
//! pin this does *not* work for is `natA` in `reduce_elem_ok`, compared by
//! exact `ConstantInfo` equality — `kernel::basis_pins`' stub.
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
use std::vec::Vec;

// ---------------------------------------------------------------------------
// The pinned names (`TrustAxioms.lean:49-75`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:52-53 trueName
/// The name `True`.
pub fn true_name() -> Name {
    name::mk_str(name::anonymous(), { const S: [u32; 4] = [84, 114, 117, 101]; core_types::code_points(&S) })
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:55-56 trueIntroName
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

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:58-59 trustCompilerName
/// The name `Lean.trustCompiler`.
pub fn trust_compiler_name() -> Name {
    name::mk_str(
        lean_ns(),
        { const S: [u32; 13] = [116, 114, 117, 115, 116, 67, 111, 109, 112, 105, 108, 101, 114]; core_types::code_points(&S) },
    )
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:61-62 reduceNatName
/// The name `Lean.reduceNat`.
pub fn reduce_nat_name() -> Name {
    name::mk_str(
        lean_ns(),
        { const S: [u32; 9] = [114, 101, 100, 117, 99, 101, 78, 97, 116]; core_types::code_points(&S) },
    )
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:64-65 reduceBoolName
/// The name `Lean.reduceBool`.
pub fn reduce_bool_name() -> Name {
    name::mk_str(
        lean_ns(),
        { const S: [u32; 10] = [114, 101, 100, 117, 99, 101, 66, 111, 111, 108]; core_types::code_points(&S) },
    )
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:67-68 ofReduceNatName
/// The name `Lean.ofReduceNat`.
pub fn of_reduce_nat_name() -> Name {
    name::mk_str(
        lean_ns(),
        { const S: [u32; 11] = [111, 102, 82, 101, 100, 117, 99, 101, 78, 97, 116]; core_types::code_points(&S) },
    )
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:70-71 ofReduceBoolName
/// The name `Lean.ofReduceBool`.
pub fn of_reduce_bool_name() -> Name {
    name::mk_str(
        lean_ns(),
        { const S: [u32; 12] = [111, 102, 82, 101, 100, 117, 99, 101, 66, 111, 111, 108]; core_types::code_points(&S) },
    )
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:76-78 ofReduceOp
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

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:89-90 trueCvA
/// Pinned `True` (shape only; capabilities are not pinned).  Already written
/// annotated in the Lean — `Sort 0` has no binder.
pub fn true_cv_a() -> ConstantVal {
    ConstantVal {
        name: true_name(),
        level_params: Vec::new(),
        ty: expr::sort(level::zero()),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:92-93 trueIntroCvA
/// Pinned `True.intro`.
pub fn true_intro_cv_a() -> ConstantVal {
    ConstantVal {
        name: true_intro_name(),
        level_params: Vec::new(),
        ty: expr::mk_const(true_name(), Vec::new()),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:95-96 trustCompilerA
/// Pinned `Lean.trustCompiler`.
pub fn trust_compiler_a() -> ConstantVal {
    ConstantVal {
        name: trust_compiler_name(),
        level_params: Vec::new(),
        ty: expr::mk_const(true_name(), Vec::new()),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:98-99 boolCvA
/// Pinned `Bool` (shape only).
pub fn bool_cv_a() -> ConstantVal {
    ConstantVal {
        name: core_k::bool_name(),
        level_params: Vec::new(),
        ty: expr::sort(level::succ(level::zero())),
    }
}


/// con-leche: ConLeche/Kernel/TrustAxioms.lean:105-107 reduceElemTy
/// The element type of a reduce operation, as the pinned constant.
pub fn reduce_elem_ty(c: &Name) -> Expr {
    if name::beq(c, &reduce_nat_name()) {
        expr::mk_const(basis_names::nat_name(), Vec::new())
    } else {
        expr::mk_const(core_k::bool_name(), Vec::new())
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:109-111 reduceOpRaw
/// Raw pinned type of `Lean.reduceNat` / `Lean.reduceBool`: `∀ (n : τ), τ`.
pub fn reduce_op_raw(c: &Name) -> ConstantVal {
    ConstantVal {
        name: name::dup(c),
        level_params: Vec::new(),
        ty: basis_builder::pi(reduce_elem_ty(c), reduce_elem_ty(c)),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:113-123 ofReduceRaw
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

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:113-123 ofReduceRaw
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

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:149-151 reduceOpCvA
/// con-leche: ConLeche/Kernel/TrustAxioms.lean:140-142 _
/// The pinned type of a reduce operation.  Deviation: the *raw* pin, which
/// `matchesPin` cannot tell from the annotated one (module note); the second
/// citation is the `#annotate_pins` command that computes the annotated form.
pub fn reduce_op_cv_a(c: &Name) -> ConstantVal {
    if name::beq(c, &reduce_nat_name()) {
        reduce_op_raw(&reduce_nat_name())
    } else {
        reduce_op_raw(&reduce_bool_name())
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:153-155 ofReducePinA
/// con-leche: ConLeche/Kernel/TrustAxioms.lean:144-147 _
/// The pin an `ofReduce*` axiom is matched against (raw; see
/// `reduce_op_cv_a`).
pub fn of_reduce_pin_a(n: &Name) -> ConstantVal {
    if name::beq(n, &of_reduce_nat_name()) {
        of_reduce_raw(&of_reduce_nat_name())
    } else {
        of_reduce_raw(&of_reduce_bool_name())
    }
}

// ---------------------------------------------------------------------------
// The environment predicates (`TrustAxioms.lean:154-196`)
// ---------------------------------------------------------------------------







// ---------------------------------------------------------------------------
// The reduce-operation install pin (`TrustAxioms.lean:198-216`)
// ---------------------------------------------------------------------------




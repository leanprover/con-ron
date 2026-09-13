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
use crate::kernel::basis_pins;
use crate::kernel::core_types;
use crate::kernel::core_k;
use crate::kernel::env::{ConstantInfo, ConstantVal};
use crate::kernel::expr;
use crate::kernel::expr::Expr;
use crate::kernel::expr_ops;
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use crate::kernel::level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::std_axioms;
use crate::kernel::trust_pins;
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

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:70-71 reduceOpNames
/// The reduce operations pinned at their `opaque` install.
pub fn reduce_op_names() -> Vec<Name> {
    let mut ns: Vec<Name> = Vec::new();
    ns.push(reduce_nat_name());
    ns.push(reduce_bool_name());
    ns
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

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:86-87 trueCvA
/// Pinned `True` (shape only; capabilities are not pinned).  Already written
/// annotated in the Lean — `Sort 0` has no binder.
pub fn true_cv_a() -> ConstantVal {
    ConstantVal {
        name: true_name(),
        level_params: Vec::new(),
        ty: expr::sort(level::zero()),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:89-90 trueIntroCvA
/// Pinned `True.intro`.
pub fn true_intro_cv_a() -> ConstantVal {
    ConstantVal {
        name: true_intro_name(),
        level_params: Vec::new(),
        ty: expr::mk_const(true_name(), Vec::new()),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:92-93 trustCompilerA
/// Pinned `Lean.trustCompiler`.
pub fn trust_compiler_a() -> ConstantVal {
    ConstantVal {
        name: trust_compiler_name(),
        level_params: Vec::new(),
        ty: expr::mk_const(true_name(), Vec::new()),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:95-96 boolCvA
/// Pinned `Bool` (shape only).
pub fn bool_cv_a() -> ConstantVal {
    ConstantVal {
        name: core_k::bool_name(),
        level_params: Vec::new(),
        ty: expr::sort(level::succ(level::zero())),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:98-100 reduceElemName
/// The element inductive of a reduce operation.
pub fn reduce_elem_name(c: &Name) -> Name {
    if name::beq(c, &reduce_nat_name()) {
        basis_names::nat_name()
    } else {
        core_k::bool_name()
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:102-104 reduceElemTy
/// The element type of a reduce operation, as the pinned constant.
pub fn reduce_elem_ty(c: &Name) -> Expr {
    if name::beq(c, &reduce_nat_name()) {
        expr::mk_const(basis_names::nat_name(), Vec::new())
    } else {
        expr::mk_const(core_k::bool_name(), Vec::new())
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:106-108 reduceOpRaw
/// Raw pinned type of `Lean.reduceNat` / `Lean.reduceBool`: `∀ (n : τ), τ`.
pub fn reduce_op_raw(c: &Name) -> ConstantVal {
    ConstantVal {
        name: name::dup(c),
        level_params: Vec::new(),
        ty: basis_builder::pi(reduce_elem_ty(c), reduce_elem_ty(c)),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:110-120 ofReduceRaw
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

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:110-120 ofReduceRaw
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

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:146-148 reduceOpCvA
/// con-leche: ConLeche/Kernel/TrustAxioms.lean:137-139 _
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

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:150-152 ofReducePinA
/// con-leche: ConLeche/Kernel/TrustAxioms.lean:141-144 _
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

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:156-167 trustCompilerOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:272-280 trustCompilerOkF
/// The stored `True` against its pin.  Factored out of the guard's `&&`
/// cascade (task #3's pattern 9, task #14's borrow rule).
pub fn true_pinned(fe: &FEnv) -> bool {
    match fenv::find(fe, &true_name()) {
        Some(ConstantInfo::IndInfo(cv_t, _)) => {
            std_axioms::matches_pin_fast(cv_t, &true_cv_a())
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:156-167 trustCompilerOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:272-280 trustCompilerOkF
/// The stored `True.intro` against its pin, at the pinned arity `0 0`.
pub fn true_intro_pinned(fe: &FEnv) -> bool {
    match fenv::find(fe, &true_intro_name()) {
        Some(ConstantInfo::CtorInfo(cv_ti, n_p, n_f)) => {
            if *n_p == 0 {
                if *n_f == 0 {
                    std_axioms::matches_pin_fast(cv_ti, &true_intro_cv_a())
                } else {
                    false
                }
            } else {
                false
            }
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:156-167 trustCompilerOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:272-280 trustCompilerOkF
/// Is `Lean.trustCompiler` installable here?  The `True` family must be
/// stored with the pinned shapes — so the synthesized value `True.intro`
/// resolves and inhabits the pinned type — and the checked axiom's type must
/// match the pin.
pub fn trust_compiler_ok(fe: &FEnv, cv_a: &ConstantVal) -> bool {
    if true_pinned(fe) {
        if true_intro_pinned(fe) {
            std_axioms::matches_pin_fast(cv_a, &trust_compiler_a())
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:169-175 reduceStoredOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:282-286 reduceStoredOkF
/// Is the reduce operation `c` stored as a checked opaque (`axiomInfo`, the
/// storage kind of every checked `opaque`) of the pinned type?
pub fn reduce_stored_ok(fe: &FEnv, c: &Name) -> bool {
    match fenv::find(fe, c) {
        Some(ConstantInfo::AxiomInfo(cv_r)) => {
            std_axioms::matches_pin_fast(cv_r, &reduce_op_cv_a(c))
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:177-184 reduceElemOk
/// The element-inductive shape an `ofReduce*` axiom needs: the pinned `Nat`
/// basis (`basis_pins::nat_basis_pinned`, which is the cited
/// `decide (env.find? natName = some natA)`) resp. a standardly-shaped
/// stored `Bool`.
pub fn reduce_elem_ok(fe: &FEnv, c: &Name) -> bool {
    if name::beq(c, &reduce_nat_name()) {
        basis_pins::nat_basis_pinned(fe)
    } else {
        match fenv::find(fe, &core_k::bool_name()) {
            Some(ConstantInfo::IndInfo(cv_b, _)) => {
                std_axioms::matches_pin_fast(cv_b, &bool_cv_a())
            }
            _ => false,
        }
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:186-196 ofReduceAxOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:296-302 ofReduceAxOkF
/// Is this checked axiom a pinned `ofReduce*` over a standardly-shaped
/// environment?  Requires the pinned `Eq` basis (the type is an equality
/// implication), the element inductive, and the reduce operation stored as a
/// pinned opaque — whose install already ran the identity certificate
/// (`checker::check_reduce_pin`), the fact the model consumes here.
pub fn of_reduce_ax_ok(fe: &FEnv, cv_a: &ConstantVal) -> bool {
    let c: Name = of_reduce_op(&cv_a.name);
    if basis_pins::eq_basis_pinned(fe) {
        if reduce_elem_ok(fe, &c) {
            if reduce_stored_ok(fe, &c) {
                std_axioms::matches_pin_fast(cv_a, &of_reduce_pin_a(&cv_a.name))
            } else {
                false
            }
        } else {
            false
        }
    } else {
        false
    }
}

// ---------------------------------------------------------------------------
// The reduce-operation install pin (`TrustAxioms.lean:198-216`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:200-205 reduceDeclPin
/// The pinned defining expression of a reduce operation (`trust_pins`: the
/// plain identity, every toolchain's `have := trustCompiler; b` after zeta).
pub fn reduce_decl_pin(c: &Name) -> Expr {
    if name::beq(c, &reduce_nat_name()) {
        trust_pins::reduce_nat_decl_pin()
    } else {
        trust_pins::reduce_bool_decl_pin()
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:207-211 reducePinGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:304-308 reducePinGuardF
/// Syntactic guards on the pin (checked once at install).
pub fn reduce_pin_guard(fe: &FEnv, c: &Name) -> bool {
    let pin: Expr = reduce_decl_pin(c);
    if expr_ops::loose_bvars_bounded(0, &pin) {
        if expr_ops::has_fvar(&pin) {
            false
        } else if expr_ops::all_level_params_defined_fast(&Vec::new(), &pin) {
            core_k::consts_resolve(fe, &pin)
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:213-216 reduceCertVar
/// The identity certificate's variable: `fvar 0` at the element type.
pub fn reduce_cert_var(c: &Name) -> Expr {
    expr::fvar(0, reduce_elem_ty(c))
}

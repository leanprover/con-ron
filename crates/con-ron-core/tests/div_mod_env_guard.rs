//! **The `Nat.div`/`Nat.mod` environment guard demands the dependencies'
//! *pinned type*** (task #58, DESIGN.md §1's accept direction).
//!
//! `divModEnvGuard` (`ConLeche/Kernel/Checker.lean:277-290`, and its index
//! twin `divModEnvGuardF` at `DeclCheck.lean:310-319`) tests each entry of
//! `natOpDeps c` with **`natOpStoredOk`** — stored as a level-monomorphic
//! definition *at the pinned type*.  Until task #58 the port tested them with
//! `core_k::deps_all_stored`, which is `natOpGuard`'s own `.all` and only
//! asks for the empty level-parameter list; so a stream whose `Nat.ble` was
//! stored at `Nat → Nat → Nat` rather than `Nat → Nat → Bool` took the pin
//! route in con-ron where con-leche declines.  That is an accept-direction
//! divergence, which §1 does not permit, and this is its regression guard.
//!
//! There is no such fixture in `vendor/con-leche/tests/e2e` — the corpus's
//! `Nat.div` streams all come from a real `lean4export` run, so every
//! dependency there has the type Lean gave it — so the stream is hand-built
//! here, in the style of `kernel::checker`'s own `#[cfg(test)]` module: the
//! two pinned basis blocks the guard reads are installed through
//! `checker::check_basis_decl`, `Bool` and its two values are pushed as
//! axioms, the four `natOpDeps Nat.div` entries as definitions, and the
//! declaration under test is `Nat.div : Nat → Nat → Nat := Nat.sub`, which
//! is well typed in both spellings so that the *only* thing that moves
//! between the two runs is the dependency's stored type.

use con_ron_core::cached::state_c;
use con_ron_core::cached::state_c::CState;
use con_ron_core::kernel::basis_names;
use con_ron_core::kernel::checker;
use con_ron_core::kernel::core_k;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env;
use con_ron_core::kernel::env::{
    BasisKind, CheckMode, ConstantInfo, ConstantVal, Declaration, ReducibilityHint,
};
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::{BinderMeta, Expr};
use con_ron_core::kernel::fenv;
use con_ron_core::kernel::fenv::FEnv;
use con_ron_core::kernel::level;
use con_ron_core::kernel::name::Name;
use con_ron_core::kernel::nat_op_pins::NatOpPinSet;
use con_ron_core::kernel::prop_when;

fn never_meta() -> BinderMeta {
    expr::binder_meta(prop_when::never())
}

fn nat_ty() -> Expr {
    expr::mk_const(basis_names::nat_name(), Vec::new())
}

fn bool_ty() -> Expr {
    expr::mk_const(core_k::bool_name(), Vec::new())
}

/// `a → b`, binder-free.
fn arrow(a: Expr, b: Expr) -> Expr {
    expr::forall_e(a, b, never_meta())
}

fn ax(n: Name, ty: Expr) -> ConstantInfo {
    ConstantInfo::AxiomInfo(ConstantVal { name: n, level_params: Vec::new(), ty })
}

/// A level-monomorphic definition `n : ty := Nat.zero`-shaped placeholder.
/// The guard reads only the header, never the value.
fn defn(n: Name, ty: Expr) -> ConstantInfo {
    ConstantInfo::DefnInfo(
        ConstantVal { name: n, level_params: Vec::new(), ty },
        expr::mk_const(basis_names::nat_zero_name(), Vec::new()),
        ReducibilityHint::Regular(1),
    )
}

/// The environment a `Nat.div` pin route needs, with `Nat.ble`'s codomain as
/// a parameter: `Bool` is the spelling `lean4export` produces, `Nat` the
/// mis-typed one this test is about.
fn env_for_div(ble_cod: Expr) -> FEnv {
    // The two pinned blocks the guard reads: `Eq` (`eq_basis_pinned`) and
    // `Nat` (`nat_lit_supported`, through `natOpGuard`).  `Eq` first, as
    // `BasisA.lean` installs them.
    let mut fe: FEnv = fenv::mk_fenv(env::empty());
    for k in [BasisKind::EqK, BasisKind::NatK].iter() {
        fe = match checker::check_basis_decl(fe, k) {
            Ok(fe2) => fe2,
            Err(_) => panic!("a pinned basis block must install"),
        };
    }
    // `Bool : Sort 1`, `Bool.true : Bool`, `Bool.false : Bool`.  `natOpCod`
    // reads `Bool`'s stored sort, `natOpGuard` the two values' empty level
    // parameters and `divModEnvGuard` their type.
    fe = fenv::push(fe, ax(core_k::bool_name(), expr::sort(level::succ(level::zero()))));
    fe = fenv::push(fe, ax(core_k::bool_true_name(), bool_ty()));
    fe = fenv::push(fe, ax(core_k::bool_false_name(), bool_ty()));
    // `natOpDeps Nat.div = [Nat.pred, Nat.sub, Nat.ble, Nat.div]`.
    fe = fenv::push(fe, defn(core_k::nat_pred_name(), arrow(nat_ty(), nat_ty())));
    fe = fenv::push(
        fe,
        defn(core_k::nat_sub_name(), arrow(nat_ty(), arrow(nat_ty(), nat_ty()))),
    );
    fe = fenv::push(
        fe,
        defn(core_k::nat_ble_name(), arrow(nat_ty(), arrow(nat_ty(), ble_cod))),
    );
    fe
}

/// The declaration under test: `Nat.div : Nat → Nat → Nat := Nat.sub`.  Its
/// value is a stored constant of exactly that type, so `checkDefnVal` passes
/// in both runs and the verdict is the pin route's alone.
fn div_decl() -> Declaration {
    Declaration::DefnDecl(
        ConstantVal {
            name: core_k::nat_div_name(),
            level_params: Vec::new(),
            ty: arrow(nat_ty(), arrow(nat_ty(), nat_ty())),
        },
        expr::mk_const(core_k::nat_sub_name(), Vec::new()),
        ReducibilityHint::Regular(1),
    )
}

fn msg(e: &CheckError) -> String {
    let cps = match e {
        CheckError::NotImplemented(m) => m,
        CheckError::Invalid(m) => m,
        CheckError::Internal(m) => m,
    };
    cps.iter().filter_map(|c| char::from_u32(*c)).collect()
}

/// **The guard itself.**  With the dependency stored at its pinned type the
/// guard holds; with `Nat.ble : Nat → Nat → Nat` — level parameters still
/// empty, so `core_k::deps_all_stored` is *satisfied* — it must not.
#[test]
fn div_mod_env_guard_demands_the_dependencies_pinned_type() {
    let c = core_k::nat_div_name();
    // The `Nat.div` header has to be stored for `natOpGuard`'s own
    // dependency sweep to see it (it is its own last dependency).
    let ok_env = fenv::push(
        env_for_div(bool_ty()),
        defn(core_k::nat_div_name(), arrow(nat_ty(), arrow(nat_ty(), nat_ty()))),
    );
    assert!(
        checker::div_mod_env_guard(&ok_env, &c),
        "the pinned spelling must pass the environment guard"
    );

    let bad_env = fenv::push(
        env_for_div(nat_ty()),
        defn(core_k::nat_div_name(), arrow(nat_ty(), arrow(nat_ty(), nat_ty()))),
    );
    // Exactly the conjunct the port used to be missing: the weaker test
    // `core_k::deps_all_stored` still holds on this environment.
    assert!(
        core_k::deps_all_stored(&bad_env, &core_k::nat_op_deps(&c), 0),
        "the level-parameter test alone must still pass -- that is the point"
    );
    assert!(
        !core_k::nat_op_stored_ok(&bad_env, &core_k::nat_ble_name()),
        "`Nat.ble : Nat -> Nat -> Nat` is not the pinned type"
    );
    assert!(
        !checker::div_mod_env_guard(&bad_env, &c),
        "a dependency at the wrong pinned type must fail the environment guard"
    );
}

/// **The stream.**  `check_decl` on `Nat.div : Nat → Nat → Nat := Nat.sub`
/// declines with the *environment* message when a dependency carries the
/// wrong pinned type, and reaches the pin loop — the *spelling* message —
/// when it does not.  Both are declines (`NotImplemented`), as con-leche's
/// `divModEnvGuard`/`checkDivModPinLoop` throws are.
#[test]
fn a_stream_declaring_nat_div_declines_on_a_mis_typed_dependency() {
    let mode = CheckMode::Verified;
    let pins: Vec<NatOpPinSet> = Vec::new();

    let mut st: CState = state_c::cstate_new();
    match checker::check_decl(&mode, &pins, &mut st, env_for_div(nat_ty()), &div_decl()) {
        Ok(_) => panic!("`Nat.div` over a mis-typed `Nat.ble` must not install"),
        Err(e) => {
            assert!(
                matches!(e, CheckError::NotImplemented(_)),
                "a pin-route refusal is a decline, not a reject"
            );
            assert_eq!(msg(&e), "unsupported Nat.div/mod environment");
        }
    }

    // The control: the same stream with `Nat.ble` at its pinned type gets
    // past the environment guard and is refused one step later, by the (here
    // empty) pin list.  Before task #58 the mis-typed run gave this message
    // too -- i.e. it took the route con-leche declines to take.
    let mut st2: CState = state_c::cstate_new();
    match checker::check_decl(&mode, &pins, &mut st2, env_for_div(bool_ty()), &div_decl()) {
        Ok(_) => panic!("an empty pin list cannot certify `Nat.div`"),
        Err(e) => assert_eq!(msg(&e), "unsupported Nat.div/mod spelling: no pin variant matched"),
    }
}

//! `arena::trust_axioms` — the compiler-trust family, over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/TrustAxioms.lean`, which is
//! con-leche's `Kernel/TrustAxioms.lean` and `Kernel/TrustPins.lean`: the
//! reserved names of `Lean.trustCompiler`, `Lean.reduceNat` /
//! `Lean.reduceBool` and the two `ofReduce*` axioms, the pinned shapes they
//! are matched against, and the pinned defining expression the reduce opaques'
//! install compares their stored value with.
//!
//! Same deviations as `arena::std_axioms`: the pins are
//! `con_ron_core::kernel::{trust_axioms,trust_pins}`' own values, interned
//! (`arena::intern`'s module note), and the four environment PREDICATES —
//! `trustCompilerOk`, `reduceStoredOk`, `reduceElemOk`, `ofReduceAxOk`,
//! `reducePinGuard` — are `arena::decl_check`'s `…F` twins, which cite both
//! halves of con-leche's `Env`/`FEnv` pair.
//!
//! `trueCvA`, `trueIntroCvA`, `trustCompilerA` and `boolCvA` are hand-written
//! in con-leche rather than spliced, so `con-ron-core` carries them verbatim.
//! `reduceNatCvA`, `reduceBoolCvA`, `ofReduceNatA` and `ofReduceBoolA` are
//! `#annotate_pins`' output there and `con-ron-core` carries the RAW pins in
//! their place, for `arena::std_axioms`' reason: their only consumer is
//! `matchesPin`, which erases the binder `pw` datum — the only thing the
//! annotation writes — so the two are the same comparand.

use crate::arena::env::IConstantVal;
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::intern::{intern_cv, intern_expr};
use crate::arena::monad::{intern_e, AState, read_name_m};
use crate::arena::store::ENodeView;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::trust_axioms as ctrust;
use con_ron_core::kernel::trust_pins;
use con_ron_core::ron::hashmap::Eq2;
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// The reserved names, interned (`TrustAxioms.lean:23-52` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:51-52 trueName
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:26 trueName`.
pub fn true_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_true(st)
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:54-55 trueIntroName
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:28 trueIntroName`.
pub fn true_intro_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_true_intro(st)
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:57-58 trustCompilerName
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:30 trustCompilerName`.
pub fn trust_compiler_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_trust_compiler(st)
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:60-61 reduceNatName
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:32 reduceNatName`.
pub fn reduce_nat_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_reduce_nat(st)
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:63-64 reduceBoolName
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:34 reduceBoolName`.
pub fn reduce_bool_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_reduce_bool(st)
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:66-67 ofReduceNatName
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:36 ofReduceNatName`.
pub fn of_reduce_nat_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_of_reduce_nat(st)
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:69-70 ofReduceBoolName
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:38 ofReduceBoolName`.
pub fn of_reduce_bool_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_of_reduce_bool(st)
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:72-73 reduceOpNames
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:42-45 reduceOpNames` — the
/// reduce operations pinned at their `opaque` install.  A `Vec` literal needs
/// its pushes (§3.4 has no `vec!`).
pub fn reduce_op_names(st: &mut AState) -> Result<Vec<NIdx>, CheckError> {
    match reduce_nat_name(st) {
        Err(e) => Err(e),
        Ok(a) => match reduce_bool_name(st) {
            Err(e) => Err(e),
            Ok(b) => {
                let mut out: Vec<NIdx> = Vec::with_capacity(2);
                out.push(a);
                out.push(b);
                Ok(out)
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:75-77 ofReduceOp
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:50-52 ofReduceOp` — the
/// reduce operation an `ofReduce*` axiom speaks about.  con-leche's
/// `if n = ofReduceNatName` is a handle comparison here.
pub fn of_reduce_op(st: &mut AState, n: &NIdx) -> Result<NIdx, CheckError> {
    match of_reduce_nat_name(st) {
        Err(e) => Err(e),
        Ok(orn) => {
            if n.eq2(&orn) {
                reduce_nat_name(st)
            } else {
                reduce_bool_name(st)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The pinned shapes (`TrustAxioms.lean:54-108` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:88-89 trueCvA
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:57 trueCvA`.
pub fn true_cv_a(pers: &PersTier, st: &mut AState) -> Result<IConstantVal, CheckError> {
    intern_cv(pers, st, &ctrust::true_cv_a())
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:91-92 trueIntroCvA
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:59 trueIntroCvA`.
pub fn true_intro_cv_a(pers: &PersTier, st: &mut AState) -> Result<IConstantVal, CheckError> {
    intern_cv(pers, st, &ctrust::true_intro_cv_a())
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:94-95 trustCompilerA
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:61 trustCompilerA`.
pub fn trust_compiler_a(pers: &PersTier, st: &mut AState) -> Result<IConstantVal, CheckError> {
    intern_cv(pers, st, &ctrust::trust_compiler_a())
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:97-98 boolCvA
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:63 boolCvA`.
pub fn bool_cv_a(pers: &PersTier, st: &mut AState) -> Result<IConstantVal, CheckError> {
    intern_cv(pers, st, &ctrust::bool_cv_a())
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:100-102 reduceElemName
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:67-69 reduceElemName` — the
/// element inductive of a reduce operation.
pub fn reduce_elem_name(st: &mut AState, c: &NIdx) -> Result<NIdx, CheckError> {
    match reduce_nat_name(st) {
        Err(e) => Err(e),
        Ok(rn) => {
            if c.eq2(&rn) {
                crate::arena::pins::pin_nat(st)
            } else {
                crate::arena::core::bool_name(st)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:104-106 reduceElemTy
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:73-74 reduceElemTy` — the
/// element type of a reduce operation, as the pinned constant.
pub fn reduce_elem_ty(pers: &PersTier, st: &mut AState, c: &NIdx) -> Result<EIdx, CheckError> {
    match reduce_elem_name(st, c) {
        Err(e) => Err(e),
        Ok(n) => crate::arena::core::const_e(pers, st, &n),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:108-110 reduceOpRaw
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:80-81 reduceOpRaw` — the
/// raw pinned type of `Lean.reduceNat` / `Lean.reduceBool`.  The con-ron-core
/// constant is a function of the operation's `Name`, so the twin reads the
/// handle back to call it and interns the result.
pub fn reduce_op_raw(
    pers: &PersTier,
    st: &mut AState,
    c: &NIdx,
) -> Result<IConstantVal, CheckError>  {
    match read_name_m(pers, st, c) {
        Err(e) => Err(e),
        Ok(n) => intern_cv(pers, st, &ctrust::reduce_op_raw(&n)),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:112-122 ofReduceRaw
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:85-86 ofReduceRaw` — the
/// raw pinned type of `Lean.ofReduceNat` / `Lean.ofReduceBool`.
pub fn of_reduce_raw(
    pers: &PersTier,
    st: &mut AState,
    n: &NIdx,
) -> Result<IConstantVal, CheckError>  {
    match read_name_m(pers, st, n) {
        Err(e) => Err(e),
        Ok(k) => intern_cv(pers, st, &ctrust::of_reduce_raw(&k)),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:139-141 _
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:90 reduceNatCvA` — the
/// pinned type of `Lean.reduceNat` (raw; the module note says why that is the
/// same comparand as the annotated one).
pub fn reduce_nat_cv_a(pers: &PersTier, st: &mut AState) -> Result<IConstantVal, CheckError> {
    intern_cv(pers, st, &ctrust::reduce_op_cv_a(&ctrust::reduce_nat_name()))
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:139-141 _
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:92 reduceBoolCvA`.
pub fn reduce_bool_cv_a(pers: &PersTier, st: &mut AState) -> Result<IConstantVal, CheckError> {
    intern_cv(pers, st, &ctrust::reduce_op_cv_a(&ctrust::reduce_bool_name()))
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:143-146 _
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:94 ofReduceNatA`.
pub fn of_reduce_nat_a(pers: &PersTier, st: &mut AState) -> Result<IConstantVal, CheckError> {
    intern_cv(pers, st, &ctrust::of_reduce_pin_a(&ctrust::of_reduce_nat_name()))
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:143-146 _
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:96 ofReduceBoolA`.
pub fn of_reduce_bool_a(pers: &PersTier, st: &mut AState) -> Result<IConstantVal, CheckError> {
    intern_cv(pers, st, &ctrust::of_reduce_pin_a(&ctrust::of_reduce_bool_name()))
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:148-150 reduceOpCvA
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:100-102 reduceOpCvA` — the
/// annotated pinned type of a reduce operation.
pub fn reduce_op_cv_a(
    pers: &PersTier,
    st: &mut AState,
    c: &NIdx,
) -> Result<IConstantVal, CheckError>  {
    match reduce_nat_name(st) {
        Err(e) => Err(e),
        Ok(rn) => {
            if c.eq2(&rn) {
                reduce_nat_cv_a(pers, st)
            } else {
                reduce_bool_cv_a(pers, st)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:152-154 ofReducePinA
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:106-108 ofReducePinA` — the
/// annotated pin an `ofReduce*` axiom is matched against.
pub fn of_reduce_pin_a(
    pers: &PersTier,
    st: &mut AState,
    n: &NIdx,
) -> Result<IConstantVal, CheckError>  {
    match of_reduce_nat_name(st) {
        Err(e) => Err(e),
        Ok(orn) => {
            if n.eq2(&orn) {
                of_reduce_nat_a(pers, st)
            } else {
                of_reduce_bool_a(pers, st)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The reduce-operation install pin (`TrustAxioms.lean:110-130` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/TrustPins.lean:42-43 reduceBoolDeclPin
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:114 reduceBoolDeclPin` —
/// `Lean.reduceBool`'s pinned value, `fun (b : Bool) => b`.
pub fn reduce_bool_decl_pin(pers: &PersTier, st: &mut AState) -> Result<EIdx, CheckError> {
    intern_expr(pers, st, &trust_pins::reduce_bool_decl_pin())
}

/// con-leche: ConLeche/Kernel/TrustPins.lean:45-46 reduceNatDeclPin
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:118 reduceNatDeclPin` —
/// `Lean.reduceNat`'s pinned value, `fun (n : Nat) => n`.
pub fn reduce_nat_decl_pin(pers: &PersTier, st: &mut AState) -> Result<EIdx, CheckError> {
    intern_expr(pers, st, &trust_pins::reduce_nat_decl_pin())
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:202-207 reduceDeclPin
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:122-124 reduceDeclPin` —
/// the pinned defining expression of a reduce operation.
pub fn reduce_decl_pin(pers: &PersTier, st: &mut AState, c: &NIdx) -> Result<EIdx, CheckError> {
    match reduce_nat_name(st) {
        Err(e) => Err(e),
        Ok(rn) => {
            if c.eq2(&rn) {
                reduce_nat_decl_pin(pers, st)
            } else {
                reduce_bool_decl_pin(pers, st)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:215-218 reduceCertVar
/// Lean twin: `proof/ConRon/Arena/TrustAxioms.lean:128-129 reduceCertVar` —
/// the identity certificate's variable: `fvar 0` at the element type.
pub fn reduce_cert_var(pers: &PersTier, st: &mut AState, c: &NIdx) -> Result<EIdx, CheckError> {
    match reduce_elem_ty(pers, st, c) {
        Err(e) => Err(e),
        Ok(ty) => intern_e(pers, st, ENodeView::FVar(0, ty)),
    }
}

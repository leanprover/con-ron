//! Fast prop-ness off the head symbol — `ConLeche/Kernel/PropRead.lean`
//! (con-leche's task #168).
//!
//! Two pure readers that answer "is this type a proposition?" /
//! "is this term a proof?" from the head symbol, the arity and the validated
//! `pw` annotations — no inference, no reduction, no memo.  Ported with
//! `Kernel/Core.lean` (task #18) because `core_k::prop_irrel`,
//! `core_k::annot_pw_pi` and `core_k::annot_pw_lam` are their only consumers.
//!
//! **The `find?` function argument becomes the environment itself.**  The
//! Lean abstracts every reader over `find? : Name → Option ConstantInfo` so
//! that the pure core (`Env.find?`) and the interned core (`FEnv.find?`)
//! share one body.  The port has one environment type on the checker's path
//! — the index (`FEnv`, task #14) — so the parameter is `fe: &FEnv` and the
//! lookup is `fenv::find`, whose agreement with `Env.find?` is con-leche's
//! own F-mirror lemma (`ConLeche/Verify/EnvBound.lean`).  This is cheaper
//! than task #9's one-method-trait pattern and loses nothing: there is no
//! second instantiation to share with.
//!
//! Both readers are three-valued: `Some(pw)` is the datum, `None` is
//! "unknown, fall back to inference".

use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;
use std::vec::Vec;

/// con-leche: ConLeche/Kernel/PropRead.lean:136-139 PropWhen.isProp
/// Is the datum "always zero" — the sort is `Prop` at every valuation?  The
/// cited `pw == (.ifAllZero [])` goes through the port's `prop_when::beq`.
pub fn is_prop(pw: &PropWhen) -> bool {
    prop_when::beq(pw, &prop_when::if_all_zero(Vec::new()))
}

#[cfg(test)]
mod tests {
    use crate::kernel::prop_read;
    use crate::kernel::prop_when;

    /// `isProp` at the two extremes.
    #[test]
    fn is_prop_is_the_empty_parameter_set() {
        assert!(prop_read::is_prop(&prop_when::if_all_zero(Vec::new())));
        assert!(!prop_read::is_prop(&prop_when::never()));
    }
}

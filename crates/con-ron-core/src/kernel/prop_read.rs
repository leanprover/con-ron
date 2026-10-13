//! Fast prop-ness off the head symbol — `ConLeche/Kernel/PropRead.lean`
//! (con-leche's task #168): the one datum-level predicate of the module,
//! `PropWhen.isProp`.  The readers themselves run over handles and are
//! `arena::prop_read`.

use crate::kernel::prop_when::PropWhen;

/// con-leche: ConLeche/Kernel/PropRead.lean:198-202 PropWhen.isProp
/// Is the datum "always zero" — the sort is `Prop` at every valuation?  A
/// match on `ifAllZero []`, as the cited function is (task #119: it was a
/// `==` against the canonical datum).
pub fn is_prop(pw: &PropWhen) -> bool {
    match pw {
        PropWhen::Never => false,
        PropWhen::IfAllZero(ps) => ps.is_empty(),
    }
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

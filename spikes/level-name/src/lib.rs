//! Spike P0.5 (DESIGN.md §5): `ConLeche/Kernel/Name.lean` and
//! `ConLeche/Kernel/Level.lean` ported for real, in the style of DESIGN.md
//! §3.1-§3.4, and pushed through Charon and Aeneas.
//!
//! The unit tests below are sanity checks for the port; they are not part of
//! what Charon sees (`cfg(test)`), and they are not the refinement proof.

pub mod level;
pub mod name;

#[cfg(test)]
mod tests {
    use crate::level;
    use crate::level::Level;
    use crate::name;
    use crate::name::Name;

    /// `"a.b"`-style helper: a single `str` component under `anonymous`.
    fn nm(s: &str) -> Name {
        let cs: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cs)
    }

    fn p(s: &str) -> Level {
        level::param(nm(s))
    }

    #[test]
    fn name_beq_is_structural() {
        let a = nm("foo");
        let b = nm("foo");
        let c = nm("bar");
        assert!(!name::ptr_eq(&a, &b));
        assert!(name::beq(&a, &b));
        assert!(!name::beq(&a, &c));
        assert_eq!(name::hash_data(&a), name::hash_data(&b));
    }

    #[test]
    fn name_num_and_shapes() {
        let projty = name::mk_num(nm("proj"), 3);
        assert!(level::name_is_proj_fn_shape(&projty));
        let tbl = name::mk_num(nm("projTable"), 0);
        assert!(level::name_is_proj_fn_shape(&tbl));
        assert!(!level::name_is_proj_fn_shape(&nm("proj")));
        assert!(level::name_is_model_suffix(&nm("_model")));
        assert!(!level::name_is_model_suffix(&nm("_models")));
    }

    #[test]
    fn name_nodup() {
        let mut ns: Vec<Name> = Vec::new();
        ns.push(nm("u"));
        ns.push(nm("v"));
        assert!(level::name_nodup(&ns));
        ns.push(nm("u"));
        assert!(!level::name_nodup(&ns));
    }

    #[test]
    fn level_beq_and_hash() {
        let a = level::max(p("u"), level::succ(level::zero()));
        let b = level::max(p("u"), level::succ(level::zero()));
        assert!(!level::ptr_eq(&a, &b));
        assert!(level::beq(&a, &b));
        assert_eq!(level::hash_data(&a), level::hash_data(&b));
        assert!(!level::beq(&a, &level::imax(p("u"), level::succ(level::zero()))));
    }

    /// `max u v ≥ u` and `max u v ≥ v`.
    fn leq_max(u: &Level, v: &Level) {
        let m = level::max(level::dup(u), level::dup(v));
        assert_eq!(level::leq(u, &m), Some(true));
        assert_eq!(level::leq(v, &m), Some(true));
    }

    #[test]
    fn max_is_an_upper_bound() {
        leq_max(&p("u"), &p("v"));
        leq_max(&level::zero(), &p("v"));
        leq_max(&level::succ(p("u")), &level::succ(level::succ(p("u"))));
    }

    #[test]
    fn succ_chain_is_ordered() {
        let z = level::zero();
        let one = level::succ(level::zero());
        let two = level::succ(level::succ(level::zero()));
        assert_eq!(level::leq(&z, &one), Some(true));
        assert_eq!(level::leq(&one, &two), Some(true));
        assert_eq!(level::leq(&two, &one), Some(false));
        assert_eq!(level::leq(&p("u"), &level::succ(p("u"))), Some(true));
        assert_eq!(level::leq(&level::succ(p("u")), &p("u")), Some(false));
    }

    /// `imax u 0` normalises to `0`, `imax 0 v` to `v`, `imax u (succ v)` to
    /// `max u (succ v)`.
    #[test]
    fn imax_normalisations() {
        let a = level::simplify(&level::imax(p("u"), level::zero()));
        assert!(level::is_zero_kind(&a));
        assert!(level::is_zero(&level::imax(p("u"), level::zero())));

        let b = level::simplify(&level::imax(level::zero(), p("v")));
        assert!(level::beq(&b, &p("v")));

        let c = level::simplify(&level::imax(p("u"), level::succ(p("v"))));
        assert!(level::beq(&c, &level::max(p("u"), level::succ(p("v")))));
    }

    #[test]
    fn simplify_is_idempotent() {
        let terms: Vec<Level> = {
            let mut v: Vec<Level> = Vec::new();
            v.push(level::zero());
            v.push(p("u"));
            v.push(level::max(level::zero(), p("u")));
            v.push(level::imax(p("u"), level::imax(p("v"), p("w"))));
            v.push(level::max(level::succ(p("u")), level::succ(level::zero())));
            v.push(level::imax(level::succ(level::zero()), p("v")));
            v.push(level::succ(level::max(p("u"), level::imax(p("v"), level::zero()))));
            v
        };
        let mut i = 0;
        while i < terms.len() {
            let s1 = level::simplify(&terms[i]);
            let s2 = level::simplify(&s1);
            assert!(level::beq(&s1, &s2), "simplify not idempotent at {}", i);
            i += 1;
        }
    }

    #[test]
    fn is_equiv_and_lists() {
        let a = level::max(p("u"), level::zero());
        assert_eq!(level::is_equiv(&a, &p("u")), Some(true));
        assert_eq!(level::is_equiv(&p("u"), &p("v")), Some(false));

        let mut ls: Vec<Level> = Vec::new();
        ls.push(level::max(level::zero(), p("u")));
        ls.push(level::succ(level::zero()));
        let mut rs: Vec<Level> = Vec::new();
        rs.push(p("u"));
        rs.push(level::imax(level::succ(level::zero()), level::succ(level::zero())));
        assert_eq!(level::is_equiv_list(&ls, &rs), Some(true));
        rs.push(level::zero());
        assert_eq!(level::is_equiv_list(&ls, &rs), Some(false));
    }

    #[test]
    fn subst_and_params() {
        let ks = name::singleton(&nm("u"));
        let vs = level::singleton(level::succ(level::zero()));
        let l = level::max(p("u"), p("v"));
        let s = level::subst(&ks, &vs, &l);
        assert!(level::beq(&s, &level::max(level::succ(level::zero()), p("v"))));

        assert!(level::level_has_param(&l));
        assert!(!level::level_has_param(&level::succ(level::zero())));

        let mut params: Vec<Name> = Vec::new();
        params.push(nm("u"));
        assert!(!level::all_params_defined(&params, &l));
        params.push(nm("v"));
        assert!(level::all_params_defined(&params, &l));
    }

    #[test]
    fn never_zero_and_non_zero() {
        assert!(level::is_never_zero(&level::succ(p("u"))));
        assert!(!level::is_never_zero(&level::imax(level::succ(p("u")), p("v"))));
        assert!(level::is_never_zero(&level::max(level::zero(), level::succ(p("u")))));
        assert!(level::is_non_zero(&level::imax(p("u"), level::succ(p("v")))));
        assert!(!level::is_non_zero(&p("u")));
    }

    /// The fueled `leqCore` reports exhaustion as `none`, never as a verdict.
    #[test]
    fn out_of_fuel_is_none() {
        let l = level::imax(p("u"), p("v"));
        let r = level::succ(level::zero());
        assert_eq!(level::leq_core(0, &l, &r, 0), None);
    }

    /// The `imax` by-cases rule (nanoda cases 10-15) terminates on the shapes
    /// the checker actually meets.
    #[test]
    fn imax_by_cases() {
        let l = level::imax(p("u"), p("v"));
        let r = level::max(p("u"), p("v"));
        assert_eq!(level::leq(&l, &r), Some(true));
        assert_eq!(level::leq(&r, &l), Some(false));
        let nested = level::imax(p("u"), level::imax(p("v"), p("w")));
        assert_eq!(level::is_equiv(&nested, &nested), Some(true));
        assert_eq!(
            level::leq(&nested, &level::max(p("u"), level::max(p("v"), p("w")))),
            Some(true)
        );
    }
}

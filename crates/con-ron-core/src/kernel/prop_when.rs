//! Port of `ConLeche/Kernel/PropWhen.lean` — the zero-ness datum of a sort,
//! in source order.
//!
//! **A plain two-constructor datum** (task #119, after con-leche's task #342
//! S5A).  The datum is `never | ifAllZero (ps : List Name)`, exposed and
//! uncanonicalised: duplicates and order are kept, so equal parameter sets
//! need not be equal values, and nothing here says otherwise.  The checker
//! asks two things of a datum, `isNever` (`capsNeverZero`, the ι case split)
//! and "is it `ifAllZero []`" (`PropWhen.isProp`, `kernel::prop_read`), and
//! compares data in no other way at run time; the stored `IndCaps.sortZ` is
//! compared structurally by the pin comparison (`arena::canon`), which is the
//! derived `DecidableEq` (`beq` below).  The five-constructor sealed
//! representation, the name order, `merge`/`canon` and the hash that the
//! binder annotations needed are gone with the annotations.
//!
//! Conventions, as in `name.rs` and `level.rs`: `Name`s are `P` trees taken
//! by shared reference and returned owned (`name::dup` for every share);
//! Lean's `List Name` is a `Vec<Name>` walked by an index (`*_from` helpers,
//! never a loop); a list that is *consumed* into a datum is passed by value
//! and a list that is *read* by reference (task #6's accumulator rule).
//!
//! `bindZ`'s argument `f : Name → PropWhen` is a function; §3.4 forbids
//! closures, so it becomes a one-method trait the caller implements — the
//! `Eq2`/`Hashable` pattern of `hashmap.rs`.  `holds`'s valuation is the
//! same, and lives with the tests (the kernel never evaluates a datum).
//!
//! **Not ported**: every `theorem` (the laws the substitution proofs read),
//! and the derived `Repr`/`Inhabited` instances.

use crate::kernel::name;
use crate::kernel::name::Name;

// ---------------------------------------------------------------------------
// `List Name` helpers
// ---------------------------------------------------------------------------

/// con-leche: none — the `List` tail copy, `xs.drop k ++ out` read off a `Vec`
/// Append `xs[k..]` to `out`, by index recursion (§3.4: no iterator).
pub fn append_from(xs: &Vec<Name>, k: usize, out: Vec<Name>) -> Vec<Name> {
    if k >= xs.len() {
        out
    } else {
        let mut o = out;
        o.push(name::dup(&xs[k]));
        append_from(xs, k + 1, o)
    }
}

/// con-leche: none — a copy of a whole name list, the `k = 0` case of `append_from`
/// The value copy Lean's value semantics hides (DESIGN.md §3.2).
pub fn names_copy(xs: &Vec<Name>) -> Vec<Name> {
    append_from(xs, 0, Vec::new())
}

/// con-leche: none — `List Name` equality from index `i`, the `ps == qs` of the derived `DecidableEq`
/// The index recursion of `names_beq`.
pub fn names_beq_from(ps: &Vec<Name>, qs: &Vec<Name>, i: usize) -> bool {
    if i >= ps.len() {
        true
    } else if name::beq(&ps[i], &qs[i]) {
        names_beq_from(ps, qs, i + 1)
    } else {
        false
    }
}

/// con-leche: none — `List Name` equality, the entry point of the recursion above
pub fn names_beq(ps: &Vec<Name>, qs: &Vec<Name>) -> bool {
    ps.len() == qs.len() && names_beq_from(ps, qs, 0)
}

// ---------------------------------------------------------------------------
// The datum (`PropWhen.lean:32-38`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/PropWhen.lean:32-38 PropWhen
/// The zero-ness datum of a sort: `never` (nonzero at every valuation) or
/// `ifAllZero ps` (zero exactly where every parameter in `ps` is).
pub enum PropWhen {
    Never,
    IfAllZero(Vec<Name>),
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:32-38 PropWhen
/// The `never` constructor, as a function (the callers' spelling).
pub fn never() -> PropWhen {
    PropWhen::Never
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:32-38 PropWhen
/// The `ifAllZero` constructor, as a function: the list is kept as given.
pub fn if_all_zero(ps: Vec<Name>) -> PropWhen {
    PropWhen::IfAllZero(ps)
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
pub fn dup(pw: &PropWhen) -> PropWhen {
    match pw {
        PropWhen::Never => PropWhen::Never,
        PropWhen::IfAllZero(ps) => PropWhen::IfAllZero(names_copy(ps)),
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:32-38 PropWhen
/// The cited `deriving DecidableEq`: constructor and list, structurally.
pub fn beq(a: &PropWhen, b: &PropWhen) -> bool {
    match (a, b) {
        (PropWhen::Never, PropWhen::Never) => true,
        (PropWhen::IfAllZero(ps), PropWhen::IfAllZero(qs)) => names_beq(ps, qs),
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:52-55 PropWhen.isNever
/// Is the datum `never` — is the sort nonzero at every valuation?
pub fn is_never(pw: &PropWhen) -> bool {
    match pw {
        PropWhen::Never => true,
        PropWhen::IfAllZero(_) => false,
    }
}

/// con-leche: none — the `ps.all params.contains` of `paramsDefined`'s `ifAllZero` arm
/// The index recursion the cited `List.all` becomes.
pub fn all_contained_from(params: &Vec<Name>, ps: &Vec<Name>, i: usize) -> bool {
    if i >= ps.len() {
        true
    } else if name::contains(params, &ps[i]) {
        all_contained_from(params, ps, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:60-65 PropWhen.paramsDefined
/// Are all parameters of the datum among `params`?
pub fn params_defined(params: &Vec<Name>, pw: &PropWhen) -> bool {
    match pw {
        PropWhen::Never => true,
        PropWhen::IfAllZero(ps) => all_contained_from(params, ps, 0),
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:70-76 PropWhen.inter
/// Intersection of two zero-ness predicates (the `max` rule: a `max` is zero
/// iff both sides are): `never` absorbs, parameter lists concatenate.
pub fn inter(a: &PropWhen, b: &PropWhen) -> PropWhen {
    match (a, b) {
        (PropWhen::Never, _) => PropWhen::Never,
        (PropWhen::IfAllZero(_), PropWhen::Never) => PropWhen::Never,
        (PropWhen::IfAllZero(ps), PropWhen::IfAllZero(qs)) => {
            PropWhen::IfAllZero(append_from(qs, 0, names_copy(ps)))
        }
    }
}

/// con-leche: none — Lean's `f : Name → PropWhen` argument of `bindZ`; §3.4 forbids closures
/// A substitution of data for parameters.  `Level.substPW` is the one
/// implementation the checker needs.
pub trait NameToPw {
    /// con-leche: none — the application `f n` of `bindZ`'s substitution
    /// The datum this substitution puts for a parameter.
    fn apply(&self, n: &Name) -> PropWhen;
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:96-99 PropWhen.bindZ.go
/// The index recursion the cited `List` fold becomes.
pub fn bind_z_go_from<F>(f: &F, ps: &Vec<Name>, i: usize) -> PropWhen
where
    F: NameToPw,
{
    if i >= ps.len() {
        if_all_zero(Vec::new())
    } else {
        inter(&f.apply(&ps[i]), &bind_z_go_from(f, ps, i + 1))
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:96-99 PropWhen.bindZ.go
/// `bindZ.go`, the list-level fold; the `i = 0` wrapper of the recursion
/// above.
pub fn bind_z_go<F>(f: &F, ps: &Vec<Name>) -> PropWhen
where
    F: NameToPw,
{
    bind_z_go_from(f, ps, 0)
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:101-105 PropWhen.bindZ
/// Substitute each parameter of the datum by a whole datum and intersect
/// ("all of `ps` zero" becomes "all replacements zero").
pub fn bind_z<F>(f: &F, pw: &PropWhen) -> PropWhen
where
    F: NameToPw,
{
    match pw {
        PropWhen::Never => PropWhen::Never,
        PropWhen::IfAllZero(ps) => bind_z_go(f, ps),
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::kernel::prop_when::{
        beq, bind_z, bind_z_go, dup, if_all_zero, inter, is_never, never,
        params_defined, NameToPw, PropWhen,
    };
    use crate::kernel::prop_read::is_prop;

    /// A valuation of the level parameters: Lean's `φ : Name → Nat`, as a
    /// trait (§3.4).
    trait Valuation {
        fn value_at(&self, n: &Name) -> u64;
    }

    /// `PropWhen.holds` (`PropWhen.lean:42-45`): the oracle the laws below are
    /// checked against (the kernel never evaluates a datum).
    fn holds<V: Valuation>(phi: &V, pw: &PropWhen) -> bool {
        match pw {
            PropWhen::Never => false,
            PropWhen::IfAllZero(ps) => ps.iter().all(|n| phi.value_at(n) == 0),
        }
    }

    fn nm(s: &str) -> Name {
        let cs: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cs)
    }

    fn names(ss: &[&str]) -> Vec<Name> {
        ss.iter().map(|s| nm(s)).collect()
    }

    fn pw(ss: &[&str]) -> PropWhen {
        if_all_zero(names(ss))
    }

    /// The valuation `φ n = if n ∈ zeros then 0 else 1`.
    struct Phi {
        zeros: Vec<Name>,
    }

    impl Valuation for Phi {
        fn value_at(&self, n: &Name) -> u64 {
            if name::contains(&self.zeros, n) {
                0
            } else {
                1
            }
        }
    }

    /// `n ↦ ifAllZero [a, n]`: every name is replaced by two.
    struct Split;

    impl NameToPw for Split {
        fn apply(&self, n: &Name) -> PropWhen {
            let mut v: Vec<Name> = Vec::new();
            v.push(nm("a"));
            v.push(name::dup(n));
            if_all_zero(v)
        }
    }

    /// The every-name-to-`never` substitution.
    struct ToNever;

    impl NameToPw for ToNever {
        fn apply(&self, _n: &Name) -> PropWhen {
            never()
        }
    }

    fn cases() -> Vec<PropWhen> {
        vec![never(), pw(&[]), pw(&["a"]), pw(&["b"]), pw(&["a", "b"]), pw(&["c", "a"])]
    }

    /// `holds_never`, `holds_ifAllZero`, `isNever_iff`, `isProp`.
    #[test]
    fn holds_reads_the_parameter_list() {
        let phi = Phi { zeros: names(&["a", "b"]) };
        assert!(!holds(&phi, &never()));
        assert!(holds(&phi, &pw(&[])));
        assert!(holds(&phi, &pw(&["a", "b", "a"])));
        assert!(!holds(&phi, &pw(&["a", "c"])));
        assert!(is_never(&never()));
        assert!(!is_never(&pw(&[])));
        assert!(is_prop(&pw(&[])));
        assert!(!is_prop(&pw(&["a"])));
        assert!(!is_prop(&never()));
        assert!(beq(&dup(&pw(&["b", "a"])), &pw(&["b", "a"])));
        // order is kept: no canonicalisation
        assert!(!beq(&pw(&["b", "a"]), &pw(&["a", "b"])));
    }

    /// `holds_inter`, `inter_assoc`, `inter_nil`.
    #[test]
    fn inter_is_the_holds_conjunction() {
        let phi = Phi { zeros: names(&["a", "b"]) };
        for p in cases().iter() {
            for q in cases().iter() {
                let pq = inter(p, q);
                assert_eq!(holds(&phi, &pq), holds(&phi, p) && holds(&phi, q));
                assert_eq!(is_never(&pq), is_never(p) || is_never(q));
                for r in cases().iter() {
                    assert!(beq(&inter(&pq, r), &inter(p, &inter(q, r))));
                }
            }
            assert!(beq(&inter(p, &pw(&[])), p));
        }
        assert!(beq(&inter(&pw(&["b"]), &pw(&["a"])), &pw(&["b", "a"])));
    }

    /// `paramsDefined_inter_of`.
    #[test]
    fn params_defined_is_stable_under_inter() {
        let params = names(&["a", "b"]);
        assert!(params_defined(&params, &never()));
        assert!(params_defined(&params, &pw(&[])));
        assert!(params_defined(&params, &pw(&["a", "b"])));
        assert!(!params_defined(&params, &pw(&["a", "c"])));
        assert!(params_defined(&params, &inter(&pw(&["a"]), &pw(&["b"]))));
    }

    /// `holds_bindZ_go`, `bindZ_go_append`, `bindZ_inter`.
    #[test]
    fn bind_z_substitutes_and_respects_inter() {
        let phi = Phi { zeros: names(&["a", "b"]) };
        for p in cases().iter() {
            assert_eq!(is_never(&bind_z(&Split, p)), is_never(p));
            for q in cases().iter() {
                assert!(beq(
                    &bind_z(&Split, &inter(p, q)),
                    &inter(&bind_z(&Split, p), &bind_z(&Split, q))
                ));
            }
        }
        let both = names(&["a", "b", "c"]);
        assert_eq!(
            holds(&phi, &bind_z_go(&Split, &both)),
            both.iter().all(|n| holds(&phi, &Split.apply(n)))
        );
        assert!(is_never(&bind_z(&ToNever, &pw(&["a"]))));
        assert!(!is_never(&bind_z(&ToNever, &pw(&[]))));
    }
}

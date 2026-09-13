//! `ConLeche/Frontend/Prepare.lean` — what happens between the file and the
//! fold (con-leche task #293).
//!
//! The decoder (`crate::frontend::export_c`) emits the file's records and
//! nothing else, this module PREPARES the stream the fold runs over, and every
//! verdict is the fold's.  `prepare_prelude` is total and pure — it has no
//! error channel, nothing it does can fail, and **no record of the stream is
//! dropped, rewritten or retagged**:
//!
//! 1. **the prelude's declarations first.**  The pin-certified `Nat`
//!    operations need `Eq`, `Nat`, `Bool` and the other prelude blocks
//!    installed before them, and `lean4export` walks a hash map: the report
//!    this answers is a stream that emits `Nat.shiftLeft` before the `Bool`
//!    block its certificate statements are spelled over.  So the stream's OWN
//!    copy of each prelude declaration is moved to the front, in the prelude's
//!    (dependency-correct) order, and only the prelude records the stream does
//!    NOT declare are synthesised there from the committed
//!    `pins/<toolchain>.prelude.ndjson` (`crate::frontend::prelude`).  A
//!    stream that declares the toolchain's `Bool` is therefore CHECKED on its
//!    own `Bool` record, not on a copy of ours;
//! 2. **the ground hoist** (`crate::frontend::nat_op_ground`): a pinned `Nat`
//!    operation's stream-certified structural ground (`Nat.ble`, `Nat.sub`,
//!    `Nat.mul`) is moved ahead of it when the stream declares it later.  A
//!    dependency-closed set moved earlier is still a valid stream.
//!
//! **Moving a record earlier can only reject, never accept.**  The prelude's
//! declarations depend on nothing but each other (`Quot`'s package on the
//! pinned `Eq`, which precedes it), so on any export that declares each of
//! them in its own record the move is order-preserving where it matters; and
//! where it would not be — a stream that declares `Bool` inside a block that
//! references a later definition — the moved record meets an unresolved
//! constant and the run REJECTS.  No reordering can make the fold accept a
//! record it would otherwise have turned away.  That is what licenses a
//! reordering step below the verified fold at all: the main theorem quantifies
//! over the prepared list, and this step can only shrink what is accepted.
//!
//! Both steps only REORDER, and the second one is the reason the first can be
//! one too.  The specification con-leche proves is
//!
//! ```text
//! ∃ extra, (∀ d ∈ extra, d ∈ prelude) ∧
//!   (preparePrelude ds).toList.Perm (ds.toList ++ extra)
//! ```
//!
//! with the pass-through corollary `pd ∈ ds → pd ∈ preparePrelude ds` — every
//! record of the file is in the prepared list, unchanged and exactly once, and
//! what else is there is a prelude record the file did not declare.
//!
//! **What is NOT here.**  Recognising a block as one of the five pinned basis
//! blocks, and a quotient record as the pinned package's, is the FOLD's
//! (`checker::check_decl`): it compares the record with the pin up to
//! `canon::constant_info_canon_eq` and installs the pinned block, rejects a
//! differing block through the reserved-name check and declines a differing
//! quotient record.  Nothing in this file looks at a record's contents; it
//! reads names, and only to find the stream's copy of a prelude declaration.
//!
//! **One deviation, and why.**  con-leche's `frontOf` reads `pre.decls` and
//! copies a record out of it (Lean's value semantics); `Declaration` derives
//! nothing in the port, `Clone` included (task #10's note), so `prepare_d`
//! takes the `PreludeIx` **by value** and moves each record out of it instead.
//! The prelude is parsed once per run and nothing reads the index afterwards,
//! so consuming it costs nothing and saves a deep copy of a dozen blocks.

use con_ron_core::kernel::env;
use con_ron_core::kernel::env::Declaration;
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::Name;

use crate::frontend::nat_op_ground::hoist_nat_op_ground;

/// con-leche: ConLeche/Frontend/Prepare.lean:83-88 PreludeIx
/// The built-in prelude: its records, in the order the committed file declares
/// them (`crate::frontend::prelude`).  Dependency-correct by construction — it
/// is an export of the toolchain's own environment — which is what makes it
/// usable as the front of every prepared stream.
pub struct PreludeIx {
    pub decls: Vec<Declaration>,
}

/// con-leche: ConLeche/Frontend/Prepare.lean:83-88 PreludeIx
/// The empty prelude (Lean's field default), which the prelude's own parse
/// runs against.
pub fn prelude_ix_empty() -> PreludeIx {
    PreludeIx { decls: Vec::new() }
}

/// con-leche: ConLeche/Frontend/Prepare.lean:90-93 preludeKey
/// The name a prelude record is looked up by: the block's type former, the
/// quotient constant, the axiom.  (`env::declaration_names` lists every name a
/// record declares; the first is the record's own handle.)
pub fn prelude_key(d: &Declaration) -> Name {
    match env::declaration_names(d).first() {
        Some(n) => name::dup(n),
        None => name::anonymous(),
    }
}

/// con-leche: ConLeche/Frontend/Prepare.lean:109-110 declares
/// The name-test a record is picked by.
pub fn declares(n: &Name, d: &Declaration) -> bool {
    name::contains(&env::declaration_names(d), n)
}

/// con-leche: ConLeche/Frontend/Prepare.lean:112-119 pickSpec
/// The first record declaring `n`, and the list without it — con-leche's
/// **specification** of `pick`, a plain list recursion.  It is here so that
/// the two can be compared (the module's test does), not because anything on
/// the run path calls it: a stream is millions of records long and this is a
/// stack frame per record.
pub fn pick_spec(n: &Name, mut ds: Vec<Declaration>) -> (Option<Declaration>, Vec<Declaration>) {
    if ds.is_empty() {
        return (None, ds);
    }
    let d = ds.remove(0);
    if declares(n, &d) {
        (Some(d), ds)
    } else {
        let (m, mut ds2) = pick_spec(n, ds);
        ds2.insert(0, d);
        (m, ds2)
    }
}

/// con-leche: ConLeche/Frontend/Prepare.lean:121-124 pick
/// `pick_spec` on the parse's vector: the first record declaring the name,
/// read by index, and the vector with that index erased.  The out-of-range
/// case — no record declares the name — is exactly "the stream does not
/// declare it, nothing is erased".
pub fn pick(n: &Name, mut ds: Vec<Declaration>) -> (Option<Declaration>, Vec<Declaration>) {
    match ds.iter().position(|d| declares(n, d)) {
        Some(i) => {
            let d = ds.remove(i);
            (Some(d), ds)
        }
        None => (None, ds),
    }
}

/// con-leche: ConLeche/Frontend/Prepare.lean:126-135 frontOf
/// The front of the prepared stream — the prelude's declarations, each one the
/// stream's own copy where the stream has one — and the rest of the stream, in
/// the stream's order.  The front is pushed onto an accumulator, the rest is
/// the stream with the picked records erased.
///
/// Deviation: `ps` is consumed (the module note), so `m.getD p` is a move of
/// the prelude's own record rather than a copy of it.
pub fn front_of(
    mut acc: Vec<Declaration>,
    ps: Vec<Declaration>,
    mut ds: Vec<Declaration>,
) -> (Vec<Declaration>, Vec<Declaration>) {
    for p in ps {
        let (m, ds2) = pick(&prelude_key(&p), ds);
        ds = ds2;
        acc.push(m.unwrap_or(p));
    }
    (acc, ds)
}

/// con-leche: ConLeche/Frontend/Prepare.lean:137-144 frontSpec
/// `front_of` over `pick_spec`: the specification con-leche's lemmas are
/// stated over.  As `pick_spec`, it is here to be compared with the
/// implementation and is not on the run path.
pub fn front_spec(
    ps: Vec<Declaration>,
    mut ds: Vec<Declaration>,
) -> (Vec<Declaration>, Vec<Declaration>) {
    let mut f: Vec<Declaration> = Vec::new();
    for p in ps {
        let (m, ds2) = pick_spec(&prelude_key(&p), ds);
        ds = ds2;
        f.push(m.unwrap_or(p));
    }
    (f, ds)
}

/// con-leche: ConLeche/Frontend/Prepare.lean:148-157 Prepared
/// The prepared stream and the driver's receipts.
pub struct Prepared {
    /// the prelude's declarations, then the rest of the stream
    pub decls: Vec<Declaration>,
    /// how many prelude records the stream did not declare and this step
    /// synthesised
    pub synthesised: u64,
    /// the records moved ahead of a pinned `Nat` operation they ground
    /// (names, for the driver's receipt)
    pub hoisted: Vec<Name>,
}

/// con-leche: ConLeche/Frontend/Prepare.lean:159-163 prepareD
/// **`prepare_prelude`, with its receipts.**
pub fn prepare_d(pre: PreludeIx, ds: Vec<Declaration>) -> Prepared {
    let n_in = ds.len();
    let (front, rest) = front_of(Vec::new(), pre.decls, ds);
    let mut all = front;
    all.extend(rest);
    let (decls, hoisted) = hoist_nat_op_ground(all);
    let synthesised = (decls.len() - n_in) as u64;
    Prepared {
        decls,
        synthesised,
        hoisted,
    }
}

/// con-leche: ConLeche/Frontend/Prepare.lean:165-172 preparePrelude
/// **`prepare_prelude`**: the parsed stream, prepared for the fold — the
/// prelude's declarations first (the stream's own copies where it has them),
/// the rest of the stream after them, every pinned `Nat` operation's
/// stream-certified ground ahead of it.  Total, pure, and the fold's input.
pub fn prepare_prelude(pre: PreludeIx, ds: Vec<Declaration>) -> Vec<Declaration> {
    prepare_d(pre, ds).decls
}

#[cfg(test)]
mod tests {
    use super::*;
    use con_ron_core::kernel::basis_builder::{bn, srt};
    use con_ron_core::kernel::env::ConstantVal;
    use con_ron_core::kernel::level;

    fn nm(s: &str) -> Name {
        bn(s.chars().map(|c| c as u32).collect())
    }

    fn ax(n: &str) -> Declaration {
        Declaration::AxiomDecl(ConstantVal {
            name: nm(n),
            level_params: Vec::new(),
            ty: srt(level::zero()),
        })
    }

    fn names_of(ds: &[Declaration]) -> Vec<String> {
        ds.iter()
            .map(|d| crate::frontend::export::name_str(&env::declaration_name(d)))
            .collect()
    }

    /// `pick` is `pick_spec`: the same record comes out and the same list
    /// stays behind, whether the name is declared, declared late, or not
    /// declared at all.
    #[test]
    fn pick_agrees_with_its_specification() {
        for want in ["A", "C", "Z"] {
            let mk = || vec![ax("A"), ax("B"), ax("C")];
            let (m1, r1) = pick(&nm(want), mk());
            let (m2, r2) = pick_spec(&nm(want), mk());
            assert_eq!(m1.is_some(), m2.is_some(), "{}", want);
            if let (Some(a), Some(b)) = (&m1, &m2) {
                assert!(name::beq(
                    &env::declaration_name(a),
                    &env::declaration_name(b)
                ));
            }
            assert_eq!(names_of(&r1), names_of(&r2), "{}", want);
        }
    }

    /// The stream's OWN copy of a prelude declaration is MOVED to the front —
    /// not duplicated, and not replaced by the prelude's copy — and a prelude
    /// record the stream does not declare is synthesised there.
    #[test]
    fn the_streams_own_copy_is_moved_to_the_front() {
        let pre = PreludeIx {
            decls: vec![ax("Eq"), ax("Bool")],
        };
        let stream = vec![ax("X"), ax("Bool"), ax("Y")];
        let p = prepare_d(pre, stream);
        assert_eq!(names_of(&p.decls), vec!["Eq", "Bool", "X", "Y"]);
        // one prelude record (`Eq`) was not declared by the stream
        assert_eq!(p.synthesised, 1);
        assert!(p.hoisted.is_empty());
    }

    /// Nothing is dropped: every record of the stream is in the prepared list
    /// exactly once, whatever the prelude holds.
    #[test]
    fn every_stream_record_survives_exactly_once() {
        let pre = PreludeIx {
            decls: vec![ax("Eq"), ax("Nat")],
        };
        let stream = vec![ax("Nat"), ax("A"), ax("B")];
        let out = prepare_prelude(pre, stream);
        let got = names_of(&out);
        for n in ["Nat", "A", "B"] {
            assert_eq!(got.iter().filter(|x| *x == n).count(), 1, "{}", n);
        }
        assert_eq!(got, vec!["Eq", "Nat", "A", "B"]);
    }

    /// An empty prelude is the identity (up to the hoist, which is a no-op
    /// here): the parse of the prelude itself runs against this.
    #[test]
    fn an_empty_prelude_changes_nothing() {
        let stream = vec![ax("A"), ax("B")];
        let p = prepare_d(prelude_ix_empty(), stream);
        assert_eq!(names_of(&p.decls), vec!["A", "B"]);
        assert_eq!(p.synthesised, 0);
    }
}

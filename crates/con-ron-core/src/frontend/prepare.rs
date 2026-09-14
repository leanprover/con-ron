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
//! **The deviation of the port into the verified core** (task #84), and why.
//! con-leche's `pick` ERASES the picked record from the array
//! (`Array.eraseIdxIfInBounds`) and `frontOf` moves it to the front; the
//! unverified frontend did the same with `Vec::remove`.  The Aeneas subset has
//! no operation that takes an element out of a `Vec` — no `remove`, no `pop`,
//! no `into_iter` (DESIGN.md §3.4, and `Vec::insert`'s model was wrong at task
//! #50) — so the port splits the two halves that con-leche fuses:
//!
//! * `pick_idx` is the cited `ds.findIdx (declares n)`, exactly, with the
//!   erasure recorded in a `picked` mask instead of performed;
//! * `front_of` runs that over the prelude and returns the picks and the mask;
//! * `prepared_stream` materialises the whole prepared list in ONE pass — the
//!   front, each slot either the stream's own record or the prelude's, then
//!   the stream's records the mask does not carry — at one
//!   `nat_op_ground::declaration_dup` per record.
//!
//! The list that comes out is the same list, and the cost is one copy of each
//! record's spine (the `Expr` fields are `P` handles and are shared, DESIGN.md
//! §3.2) where Lean's value semantics cost nothing.  con-leche's `pickSpec`
//! and `frontSpec` — the plain list recursions its permutation lemmas are
//! stated over — are **not** ported: they are `cons`-list specifications with
//! no caller on the run path, the subset cannot spell `d :: ds'` on a `Vec`,
//! and a Rust transliteration of a Lean spec only to extract it back to Lean
//! buys the refinement nothing.  `pick_spec` lives in this module's tests
//! instead, where it still checks `pick_idx` against the specification on
//! every `cargo test`.

use crate::frontend::nat_op_ground;
use crate::frontend::nat_op_ground::hoist_nat_op_ground;
use crate::kernel::env;
use crate::kernel::env::Declaration;
use crate::kernel::name;
use crate::kernel::name::Name;

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
/// record declares; the first is the record's own handle, and the cited
/// `head?.getD .anonymous` is the empty case.)
pub fn prelude_key(d: &Declaration) -> Name {
    let ns = env::declaration_names(d);
    if ns.len() == 0 {
        name::anonymous()
    } else {
        name::dup(&ns[0])
    }
}

/// con-leche: ConLeche/Frontend/Prepare.lean:109-110 declares
/// The name-test a record is picked by.
pub fn declares(n: &Name, d: &Declaration) -> bool {
    name::contains(&env::declaration_names(d), n)
}

/// con-leche: ConLeche/Frontend/Prepare.lean:121-124 pick
/// The cited `ds.findIdx (declares n)`: the index of the first record
/// declaring `n` that is not already spoken for, or `ds.len()` — which is what
/// `findIdx` answers when no record does, and is exactly "the stream does not
/// declare it, nothing is erased".
///
/// Deviation (the module note): a record already picked by an earlier prelude
/// key is *masked* rather than erased, because the subset cannot take an
/// element out of a `Vec`.  The mask is what makes a second key see the array
/// `eraseIdxIfInBounds` would have left behind.
pub fn pick_idx(n: &Name, ds: &Vec<Declaration>, picked: &Vec<bool>) -> usize {
    let m = ds.len();
    let mut i: usize = 0;
    let mut hit: usize = m;
    while i < m && hit == m {
        if !picked[i] && declares(n, &ds[i]) {
            hit = i;
        }
        i += 1;
    }
    hit
}

/// con-leche: none — the `picked` mask of the module note's deviation, empty
/// `n` falses: nothing has been picked out of the stream yet.  Its own
/// function because `-loops-to-rec` copies the code after a loop into every
/// exit of it, and what follows this one is the whole of `front_of`.
pub fn no_picks(n: usize) -> Vec<bool> {
    let mut picked: Vec<bool> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        picked.push(false);
        i += 1;
    }
    picked
}

/// con-leche: ConLeche/Frontend/Prepare.lean:126-135 frontOf
/// The front of the prepared stream, as *where each slot comes from*: entry
/// `j` is the index in `ds` of the stream's own copy of prelude record `j`, or
/// `ds.len()` when the stream does not declare it.  The second component is
/// the mask of the records so picked — `prepared_stream` reads both.
///
/// Deviation: the cited `frontOf` builds the front and the residual array; the
/// port builds the *plan* and leaves the building to one pass (the module
/// note).
pub fn front_of(ps: &Vec<Declaration>, ds: &Vec<Declaration>) -> (Vec<usize>, Vec<bool>) {
    let n = ds.len();
    let mut picked = no_picks(n);
    let np = ps.len();
    let mut picks: Vec<usize> = Vec::with_capacity(np);
    let mut j: usize = 0;
    while j < np {
        let k = pick_idx(&prelude_key(&ps[j]), ds, &picked);
        if k < n {
            picked[k] = true;
        }
        picks.push(k);
        j += 1;
    }
    (picks, picked)
}

/// con-leche: ConLeche/Frontend/Prepare.lean:126-135 frontOf
/// The cited `acc.push (m.getD p)` followed by `front ++ rest`, in one pass:
/// the prelude's declarations — the stream's own record where `front_of` found
/// one, the prelude's own where it did not — then the stream's records the
/// mask does not carry, in the stream's order.
pub fn prepared_stream(
    ps: &Vec<Declaration>,
    ds: &Vec<Declaration>,
    picks: &Vec<usize>,
    picked: &Vec<bool>,
) -> Vec<Declaration> {
    let out = Vec::with_capacity(ds.len() + ps.len());
    prepared_rest(prepared_front(out, ps, ds, picks), ds, picked)
}

/// con-leche: ConLeche/Frontend/Prepare.lean:126-135 frontOf
/// The cited `acc.push (m.getD p)`: the front, each slot the stream's own
/// record where `front_of` found one and the prelude's own where it did not.
pub fn prepared_front(
    out: Vec<Declaration>,
    ps: &Vec<Declaration>,
    ds: &Vec<Declaration>,
    picks: &Vec<usize>,
) -> Vec<Declaration> {
    let mut out = out;
    let n = ds.len();
    let np = ps.len();
    let mut j: usize = 0;
    while j < np {
        let k = picks[j];
        if k < n {
            out.push(nat_op_ground::declaration_dup(&ds[k]));
        } else {
            out.push(nat_op_ground::declaration_dup(&ps[j]));
        }
        j += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/Prepare.lean:159-163 prepareD
/// The cited `front ++ rest`'s second half: the stream's records the mask does
/// not carry, in the stream's order.
pub fn prepared_rest(
    out: Vec<Declaration>,
    ds: &Vec<Declaration>,
    picked: &Vec<bool>,
) -> Vec<Declaration> {
    let mut out = out;
    let n = ds.len();
    let mut i: usize = 0;
    while i < n {
        if !picked[i] {
            out.push(nat_op_ground::declaration_dup(&ds[i]));
        }
        i += 1;
    }
    out
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
    let plan = front_of(&pre.decls, &ds);
    let all = prepared_stream(&pre.decls, &ds, &plan.0, &plan.1);
    let hoisted = hoist_nat_op_ground(all);
    let synthesised = (hoisted.0.len() - n_in) as u64;
    Prepared {
        decls: hoisted.0,
        synthesised,
        hoisted: hoisted.1,
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
    use crate::kernel::basis_builder::{bn, srt};
    use crate::kernel::env::ConstantVal;
    use crate::kernel::level;

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
            .map(|d| {
                let cps = crate::frontend::text::name_str(&env::declaration_name(d));
                cps.iter().filter_map(|c| char::from_u32(*c)).collect()
            })
            .collect()
    }

    /// con-leche's `pickSpec` (`Prepare.lean:112-119`), the plain list
    /// recursion its permutation lemmas are stated over.  The module note says
    /// why it lives here and not in the ported code: it is a `cons`-list
    /// specification with no caller on the run path, and `#[cfg(test)]` is
    /// outside the Aeneas subset, so it can be spelled as con-leche spells it.
    fn pick_spec(n: &Name, ds: &[Declaration]) -> (Option<usize>, Vec<usize>) {
        if ds.is_empty() {
            return (None, Vec::new());
        }
        if declares(n, &ds[0]) {
            return (Some(0), (1..ds.len()).collect());
        }
        let (m, rest) = pick_spec(n, &ds[1..]);
        let mut out = vec![0usize];
        out.extend(rest.iter().map(|k| k + 1));
        (m.map(|k| k + 1), out)
    }

    /// `pick_idx` is `pickSpec`: the same record is found and the same list
    /// stays behind, whether the name is declared, declared late, or not
    /// declared at all.
    #[test]
    fn pick_agrees_with_its_specification() {
        for want in ["A", "C", "Z"] {
            let ds = vec![ax("A"), ax("B"), ax("C")];
            let none: Vec<bool> = vec![false; ds.len()];
            let got = pick_idx(&nm(want), &ds, &none);
            let (m, rest) = pick_spec(&nm(want), &ds);
            match m {
                Some(i) => {
                    assert_eq!(got, i, "{}", want);
                    let kept: Vec<usize> =
                        (0..ds.len()).filter(|k| *k != got).collect();
                    assert_eq!(kept, rest, "{}", want);
                }
                None => assert_eq!(got, ds.len(), "{}", want),
            }
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

    /// Two prelude records whose keys are both declared by the SAME stream
    /// record: the mask makes the second key miss, exactly as `pick`'s erasure
    /// would have.
    #[test]
    fn a_masked_record_is_not_picked_twice() {
        let ds = vec![ax("A"), ax("B")];
        let mut picked: Vec<bool> = vec![false; ds.len()];
        assert_eq!(pick_idx(&nm("A"), &ds, &picked), 0);
        picked[0] = true;
        assert_eq!(pick_idx(&nm("A"), &ds, &picked), ds.len());
    }
}

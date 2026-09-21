//! `proof/ConRon/Arena/Frontend/Prepare.lean` — **what happens between the
//! file and the fold** (task #97 P4e part 1).
//!
//! `prepare_prelude` is total — no record of the stream is dropped, rewritten
//! or retagged — and it does two things:
//!
//! 1. **the prelude's declarations first**, the stream's OWN copy of each
//!    where the stream has one and a synthesised one only where it has none,
//!    so a stream that declares the toolchain's `Bool` is checked on its own
//!    `Bool` record;
//! 2. **the ground hoist**: a pinned `Nat` operation's stream-certified
//!    structural ground is moved ahead of it when the stream declares it
//!    later.
//!
//! Moving a record earlier can only reject, never accept, which is why the
//! spec con-leche proves is as simple as it is:
//!
//! ```text
//! ∃ extra, (∀ d ∈ extra, d ∈ prelude) ∧
//!   (preparePrelude ds).toList.Perm (ds.toList ++ extra)
//! ```
//!
//! **Step 2 is `frontend::nat_op_ground`'s**, a module of its own exactly as
//! con-leche's is (task #97-P4d; task #97-P4e part 1 shipped an identity
//! placeholder here, because the pass needs the kernel's
//! `natOpNames`/`natDivModNames`, which arrived with the pins).  It is why
//! `prepare_d` takes the whole `AState` where everything else in this module
//! needs only the store.
//!
//! **Where the store comes from.**  Only `prelude_key`, whose `.anonymous`
//! fall-through has to be INTERNED, and the two functions that call it;
//! [`pick_idx`] and [`declares`] are pure, exactly as con-leche's are, because
//! `env::i_declaration_names` is (`arena/env.rs`'s `table_name` note).
//! Nothing in this module reads or writes a term.
//!
//! **The deviation of the port into the verified core** (task #84), kept
//! verbatim from `con_ron_core::frontend::prepare`: con-leche's `pick` ERASES
//! the picked record from the array (`Array.eraseIdxIfInBounds`) and `frontOf`
//! moves it to the front.  The Aeneas subset has no operation that takes an
//! element out of a `Vec` — no `remove`, no `pop`, no `into_iter` — so the
//! port splits the two halves that con-leche fuses: [`pick_idx`] is the cited
//! `ds.findIdx (declares n)` with the erasure recorded in a `picked` mask
//! instead of performed, [`front_of`] runs that over the prelude, and
//! [`prepared_stream`] materialises the whole prepared list in ONE pass.  The
//! list that comes out is the same list; the cost is one record copy per
//! record, where the copied fields are handles and `Vec` spines and not terms.
//! con-leche's `pickSpec`/`frontSpec` are not ported (they are `cons`-list
//! specifications with no caller on the run path); `pick_spec` lives in this
//! module's tests, where it still checks `pick_idx` against the specification
//! on every `cargo test`.

use crate::arena::env;
use crate::arena::env::{i_declaration_names, nidx_vec_contains, IDeclaration};
use crate::arena::handle::NIdx;
use crate::arena::monad::AState;
use crate::arena::store::{EStore, NNodeView};
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::ron::hashmap::Dup;
use crate::arena::store::PersTier;

/// con-leche: ConLeche/Frontend/Prepare.lean:83-88 PreludeIx
/// Lean twin: `proof/ConRon/Arena/Frontend/Prepare.lean:48-49 PreludeIx` — the
/// built-in prelude: its records, in the order the committed file declares
/// them.  Dependency-correct by construction — it is an export of the
/// toolchain's own environment — which is what makes it usable as the front of
/// every prepared stream.
pub struct PreludeIx {
    pub decls: Vec<IDeclaration>,
}

/// con-leche: ConLeche/Frontend/Prepare.lean:83-88 PreludeIx
/// The empty prelude (the Lean's field default), which the prelude's own parse
/// runs against.
pub fn prelude_ix_empty() -> PreludeIx {
    PreludeIx { decls: Vec::new() }
}

/// con-leche: ConLeche/Frontend/Prepare.lean:90-93 preludeKey
/// Lean twin: `proof/ConRon/Arena/Frontend/Prepare.lean:55-58 preludeKey` —
/// the name a prelude record is looked up by: the block's type former, the
/// quotient constant, the axiom.  con-leche's `.anonymous` fall-through is the
/// interned anonymous name, which is the one reason this takes the store.
pub fn prelude_key(pers: &PersTier, ar: &mut EStore, d: &IDeclaration) -> Result<NIdx, CheckError> {
    let ns = i_declaration_names(d);
    if ns.len() == 0 {
        ar.intern_name(pers, NNodeView::Anonymous)
    } else {
        Ok(ns[0].dup2())
    }
}

/// con-leche: ConLeche/Frontend/Prepare.lean:109-110 declares
/// Lean twin: `proof/ConRon/Arena/Frontend/Prepare.lean:80 declares` — the
/// name-test a record is picked by.  PURE, like con-leche's.
pub fn declares(n: &NIdx, d: &IDeclaration) -> bool {
    nidx_vec_contains(&i_declaration_names(d), n)
}

/// con-leche: ConLeche/Frontend/Prepare.lean:121-124 pick
/// Lean twin: `proof/ConRon/Arena/Frontend/Prepare.lean:91-94 pick` — the
/// cited `ds.findIdx (declares n)`: the index of the first record declaring
/// `n` that is not already spoken for, or `ds.len()` — which is what `findIdx`
/// answers when no record does, and is exactly "the stream does not declare
/// it, nothing is erased".
///
/// Deviation (the module note): a record already picked by an earlier prelude
/// key is *masked* rather than erased.
pub fn pick_idx(n: &NIdx, ds: &Vec<IDeclaration>, picked: &Vec<bool>) -> usize {
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

/// con-leche: none — the `picked` mask of the module note's deviation
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
/// Lean twin: `proof/ConRon/Arena/Frontend/Prepare.lean:100-106 frontOf` — the
/// front of the prepared stream, as *where each slot comes from*: entry `j` is
/// the index in `ds` of the stream's own copy of prelude record `j`, or
/// `ds.len()` when the stream does not declare it.  The second component is
/// the mask of the records so picked — [`prepared_stream`] reads both.
pub fn front_of(
    pers: &PersTier,
    ar: &mut EStore,
    ps: &Vec<IDeclaration>,
    ds: &Vec<IDeclaration>,
) -> Result<(Vec<usize>, Vec<bool>), CheckError> {
    let n = ds.len();
    let mut picked = no_picks(n);
    let np = ps.len();
    let mut picks: Vec<usize> = Vec::with_capacity(np);
    let mut j: usize = 0;
    while j < np {
        let key = match prelude_key(pers, ar, &ps[j]) {
            Err(e) => return Err(e),
            Ok(v) => v,
        };
        let k = pick_idx(&key, ds, &picked);
        if k < n {
            picked[k] = true;
        }
        picks.push(k);
        j += 1;
    }
    Ok((picks, picked))
}

/// con-leche: ConLeche/Frontend/Prepare.lean:126-135 frontOf
/// The cited `acc.push (m.getD p)` followed by `front ++ rest`, in one pass.
pub fn prepared_stream(
    ps: &Vec<IDeclaration>,
    ds: &Vec<IDeclaration>,
    picks: &Vec<usize>,
    picked: &Vec<bool>,
) -> Vec<IDeclaration> {
    let out = Vec::with_capacity(ds.len() + ps.len());
    prepared_rest(prepared_front(out, ps, ds, picks), ds, picked)
}

/// con-leche: ConLeche/Frontend/Prepare.lean:126-135 frontOf
/// The cited `acc.push (m.getD p)`: the front, each slot the stream's own
/// record where [`front_of`] found one and the prelude's own where it did not.
pub fn prepared_front(
    out: Vec<IDeclaration>,
    ps: &Vec<IDeclaration>,
    ds: &Vec<IDeclaration>,
    picks: &Vec<usize>,
) -> Vec<IDeclaration> {
    let mut out = out;
    let n = ds.len();
    let np = ps.len();
    let mut j: usize = 0;
    while j < np {
        let k = picks[j];
        if k < n {
            out.push(env::i_declaration_dup(&ds[k]));
        } else {
            out.push(env::i_declaration_dup(&ps[j]));
        }
        j += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/Prepare.lean:159-163 prepareD
/// The cited `front ++ rest`'s second half: the stream's records the mask does
/// not carry, in the stream's order.
pub fn prepared_rest(
    out: Vec<IDeclaration>,
    ds: &Vec<IDeclaration>,
    picked: &Vec<bool>,
) -> Vec<IDeclaration> {
    let mut out = out;
    let n = ds.len();
    let mut i: usize = 0;
    while i < n {
        if !picked[i] {
            out.push(env::i_declaration_dup(&ds[i]));
        }
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/Prepare.lean:148-157 Prepared
/// Lean twin: `proof/ConRon/Arena/Frontend/Prepare.lean:137-144 Prepared` —
/// the prepared stream and the driver's receipts.
pub struct Prepared {
    /// the prelude's declarations, then the rest of the stream
    pub decls: Vec<IDeclaration>,
    /// how many prelude records the stream did not declare and this step
    /// synthesised
    pub synthesised: u64,
    /// the records moved ahead of a pinned `Nat` operation they ground
    pub hoisted: Vec<NIdx>,
}

/// con-leche: ConLeche/Frontend/Prepare.lean:159-163 prepareD
/// Lean twin: `proof/ConRon/Arena/Frontend/Prepare.lean:147-150 prepareD` —
/// `prepare_prelude`, with its receipts.
pub fn prepare_d(
    pers: &PersTier,
    st: &mut AState,
    pre: PreludeIx,
    ds: Vec<IDeclaration>,
) -> Result<Prepared, CheckError> {
    let n_in = ds.len();
    let plan = match front_of(pers, &mut st.store, &pre.decls, &ds) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let all = prepared_stream(&pre.decls, &ds, &plan.0, &plan.1);
    // step 2, no longer a placeholder: `frontend::nat_op_ground`'s real pass
    // (task #97-P4d), which is why this function takes the whole state and not
    // just the store — the trigger set is the kernel's
    // `natOpNames`/`natDivModNames` and the closure walks the records' terms.
    let hoisted = match crate::frontend::nat_op_ground::hoist_nat_op_ground(pers, st, all) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    let synthesised = crate::frontend::export_c::sat_sub(hoisted.0.len() as u64, n_in as u64);
    Ok(Prepared {
        decls: hoisted.0,
        synthesised,
        hoisted: hoisted.1,
    })
}

/// con-leche: ConLeche/Frontend/Prepare.lean:165-172 preparePrelude
/// Lean twin: `proof/ConRon/Arena/Frontend/Prepare.lean:157-159 preparePrelude`
/// — the parsed stream, prepared for the fold: the prelude's declarations
/// first (the stream's own copies where it has them), the rest of the stream
/// after them, every pinned `Nat` operation's stream-certified ground ahead of
/// it.  An array in and an array out, the shape the parse returns and the fold
/// consumes.
pub fn prepare_prelude(
    pers: &PersTier,
    st: &mut AState,
    pre: PreludeIx,
    ds: Vec<IDeclaration>,
) -> Result<Vec<IDeclaration>, CheckError> {
    match prepare_d(pers, st, pre, ds) {
        Err(e) => Err(e),
        Ok(p) => Ok(p.decls),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arena::env::IConstantVal;
    use crate::arena::store::{ENodeView, LNodeView};

    fn cp(t: &str) -> Vec<u32> {
        t.chars().map(|c| c as u32).collect()
    }

    /// An axiom record named `n : Sort 0`, over a fresh store.
    fn ax(pers: &PersTier, ar: &mut EStore, n: &str) -> IDeclaration {
        let anon = ar.intern_name(pers, NNodeView::Anonymous).ok().unwrap();
        let name = ar.intern_name(pers, NNodeView::Str(anon, cp(n))).ok().unwrap();
        let z = ar.intern_level(pers, LNodeView::Zero).ok().unwrap();
        let ty = ar.intern(pers, ENodeView::Sort(z)).ok().unwrap();
        IDeclaration::AxiomDecl(IConstantVal {
            name,
            level_params: Vec::new(),
            ty,
        })
    }

    fn names_of(pers: &PersTier, ar: &EStore, ds: &[IDeclaration]) -> Vec<String> {
        ds.iter()
            .map(|d| {
                let ns = i_declaration_names(d);
                match env::read_name(pers, ar, &ns[0]) {
                    Ok(n) => con_ron_core::frontend::text::name_str(&n)
                        .iter()
                        .filter_map(|c| char::from_u32(*c))
                        .collect(),
                    Err(_) => "<dangling>".to_string(),
                }
            })
            .collect()
    }

    /// con-leche's `pickSpec` (`Prepare.lean:112-119`), the plain list
    /// recursion its permutation lemmas are stated over.  The module note says
    /// why it lives here and not in the ported code; `#[cfg(test)]` is outside
    /// the Aeneas subset, so it can be spelled as con-leche spells it.
    fn pick_spec(n: &NIdx, ds: &[IDeclaration]) -> (Option<usize>, Vec<usize>) {
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
        let pers: &PersTier = &PersTier::empty();
        for want in ["A", "C", "Z"] {
            let mut ar = EStore::empty();
            let ds = vec![ax(pers, &mut ar, "A"), ax(pers, &mut ar, "B"), ax(pers, &mut ar, "C")];
            let key = {
                let d = ax(pers, &mut ar, want);
                i_declaration_names(&d)[0].dup2()
            };
            let none: Vec<bool> = vec![false; ds.len()];
            let got = pick_idx(&key, &ds, &none);
            let (m, rest) = pick_spec(&key, &ds);
            match m {
                Some(i) => {
                    assert_eq!(got, i, "{}", want);
                    let kept: Vec<usize> = (0..ds.len()).filter(|k| *k != got).collect();
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
        let pers: &PersTier = &PersTier::empty();
        let mut ar = EStore::empty();
        let pre = PreludeIx {
            decls: vec![ax(pers, &mut ar, "Eq"), ax(pers, &mut ar, "Bool")],
        };
        let stream = vec![ax(pers, &mut ar, "X"), ax(pers, &mut ar, "Bool"), ax(pers, &mut ar, "Y")];
        let mut st = AState::init(ar);
        let p = prepare_d(pers, &mut st, pre, stream).ok().unwrap();
        assert_eq!(names_of(pers, &st.store, &p.decls), vec!["Eq", "Bool", "X", "Y"]);
        // one prelude record (`Eq`) was not declared by the stream
        assert_eq!(p.synthesised, 1);
        assert!(p.hoisted.is_empty());
    }

    /// Nothing is dropped: every record of the stream is in the prepared list
    /// exactly once, whatever the prelude holds.
    #[test]
    fn every_stream_record_survives_exactly_once() {
        let pers: &PersTier = &PersTier::empty();
        let mut ar = EStore::empty();
        let pre = PreludeIx {
            decls: vec![ax(pers, &mut ar, "Eq"), ax(pers, &mut ar, "Nat")],
        };
        let stream = vec![ax(pers, &mut ar, "Nat"), ax(pers, &mut ar, "A"), ax(pers, &mut ar, "B")];
        let mut st = AState::init(ar);
        let out = prepare_prelude(pers, &mut st, pre, stream).ok().unwrap();
        let got = names_of(pers, &st.store, &out);
        for n in ["Nat", "A", "B"] {
            assert_eq!(got.iter().filter(|x| *x == n).count(), 1, "{}", n);
        }
        assert_eq!(got, vec!["Eq", "Nat", "A", "B"]);
    }

    /// An empty prelude is the identity (up to the hoist, which is the
    /// identity in part 1): the parse of the prelude itself runs against this.
    #[test]
    fn an_empty_prelude_changes_nothing() {
        let pers: &PersTier = &PersTier::empty();
        let mut ar = EStore::empty();
        let stream = vec![ax(pers, &mut ar, "A"), ax(pers, &mut ar, "B")];
        let mut st = AState::init(ar);
        let p = prepare_d(pers, &mut st, prelude_ix_empty(), stream).ok().unwrap();
        assert_eq!(names_of(pers, &st.store, &p.decls), vec!["A", "B"]);
        assert_eq!(p.synthesised, 0);
    }

    /// Two prelude records whose keys are both declared by the SAME stream
    /// record: the mask makes the second key miss, exactly as `pick`'s erasure
    /// would have.
    #[test]
    fn a_masked_record_is_not_picked_twice() {
        let pers: &PersTier = &PersTier::empty();
        let mut ar = EStore::empty();
        let ds = vec![ax(pers, &mut ar, "A"), ax(pers, &mut ar, "B")];
        let key = i_declaration_names(&ds[0])[0].dup2();
        let mut picked: Vec<bool> = vec![false; ds.len()];
        assert_eq!(pick_idx(&key, &ds, &picked), 0);
        picked[0] = true;
        assert_eq!(pick_idx(&key, &ds, &picked), ds.len());
    }

    /// The hoist is the identity on a stream that declares no pinned `Nat`
    /// operation: nothing moves, no name is reported moved, and the vector
    /// comes back uncopied (task #97-P4d; the pass itself is
    /// `frontend::nat_op_ground`, tested there).
    #[test]
    fn the_hoist_is_the_identity_without_a_pinned_operation() {
        let pers: &PersTier = &PersTier::empty();
        let mut ar = EStore::empty();
        let ds = vec![ax(pers, &mut ar, "A"), ax(pers, &mut ar, "B")];
        let mut st = AState::init(ar);
        let (out, moved) =
            crate::frontend::nat_op_ground::hoist_nat_op_ground(pers, &mut st, ds)
                .ok()
                .unwrap();
        assert_eq!(names_of(pers, &st.store, &out), vec!["A", "B"]);
        assert!(moved.is_empty());
    }
}

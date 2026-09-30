//! `arena::core_io` — the io knot (the leaf lane), over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/CoreIO.lean`, itself
//! `ConLeche/Kernel/CoreIO.lean`'s.  `whnfCore` / `whnf` / `defeq` /
//! `annotate` are the *full* knot's at the same fuel — the io lane consumes
//! the certified reduction and definitional equality and never supplies them —
//! and `infer` is `inferBodyIO` tied to the io knot one level down.  The full
//! knot never mentions this one: that asymmetry is con-leche's
//! mode-provenance discipline, and it survives the change of representation
//! unchanged.
//!
//! **Class (S) in the census, twinned anyway.**  con-leche's Rust port skips
//! these three ("the port's `infer_at_i` carries the io grade as a runtime
//! flag"), because the Rust has one knot.  The arena has one knot too — the
//! memoized `coreKnot` — so this lane is, here as in con-leche, the
//! *statement subject* the io claims will be phrased at rather than a thing
//! the checker runs.  It is twinned because P3 will need it to state the knot
//! equations, and because it costs a dozen lines.
//!
//! **No memo.**  con-leche's leaf lane is unmemoized (it is a specification,
//! not an executed core), and so is this one: adding a table here would give
//! the io grade two of them and break DESIGN.md §8.3's lesson 9 ("a hit in one
//! grade never serves another") in the other direction.
//!
//! **Where the knot is.**  The twin builds a `CoreFnsA` record whose slots
//! point at the full knot and at `inferBodyIO`; §3.4 rules a record of
//! functions out, so the port's knot is `arena::core`'s six `knot_*`
//! functions taking a `lane`, and `coreKnotIO` is the value `LANE_IO` of that
//! lane — `knot_whnf_core`/`knot_whnf`/`knot_defeq`/`knot_annotate` fall
//! through to `LANE_FULL` there (the twin's `(coreKnot mode fe id (fuel +
//! 1)).whnfCore`, at the same fuel), and `knot_infer`/`knot_infer_io` are the
//! unmemoized `inferBodyIO`.  So this module is the io lane's **entry point**
//! and nothing else; every clause of it lives in `arena::core`, cited there.




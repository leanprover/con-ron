//! The four interned stores (DESIGN.md §8.3/§8.5, task #97 P4a), a
//! transliteration of `proof/ConRon/Arena/Store.lean`.
//!
//! Names, levels, level lists and expressions, each as **one array per
//! constructor per tier** of a uniform fixed-size record, a **parallel
//! derived array** holding con-leche's own cached word for that node, and a
//! **cons table** per constructor per tier keyed by the constructor's fields.
//!
//! ```text
//! NStore ⊂ LStore ⊂ LsStore ⊂ EStore
//! ```
//!
//! is the layering: a level mentions a name (`param`), a level list mentions
//! levels, an expression mentions all three.  The stores nest exactly as the
//! Lean nests them, so `NStore::view : &NStore -> &NIdx -> Option<NNodeView>`
//! and `EStore::view` are literally the twin's signatures.  Nesting costs
//! nothing at runtime: interning an expression node never touches the name
//! arrays, because an `ENodeView`'s children are handles.
//!
//! ## The derived word
//!
//! `Tbl`'s `der` array holds, per node, exactly what con-leche caches on the
//! corresponding value:
//!
//! * names — `Name.hashData`, a `u64`;
//! * levels and level lists — the `u64` hash *and* the has-a-parameter flag,
//!   because `Expr.data` reads both.  `Level` itself caches only the hash, so
//!   `LDer::has_param` is an arena addition: con-leche recomputes
//!   `levelHasParam` by an `O(|u|)` walk at every node construction, which an
//!   interned store does in `O(1)`;
//! * expressions — `Expr.data`, the packed `hash(32) | bvarB(15) | fvarB(15)
//!   | hasLP(1)` word.
//!
//! **The formulas are not re-derived here.**  Every one is
//! `crates/con-ron-core/src/kernel/expr.rs`'s smart constructor with
//! `data(&child)` replaced by `self.derived(h)` — the same
//! `pack_data`/`hash32`/`mix_hash`/`sat_succ`/`sat_pred`/`max_u64` calls, in
//! the same order, imported from that crate rather than copied.  That is
//! what makes `EStore::derived` of a handle equal to `expr::data` of the term
//! it denotes, which `mod tests` checks on hand-built terms and which the
//! Lean's `EStore.derived_exact` proves.
//!
//! ## Memory discipline
//!
//! The Lean detaches before every update (`let tb := t.f; let t := { t with
//! f := .empty }; … tb.push …`) so that the array and the table being grown
//! are uniquely referenced, and marks the functions that hand out a whole
//! table `@[noinline]`.  Neither has a Rust counterpart: `&mut self` **is**
//! the unique reference, and `Vec::push` grows in place.  The Rust is the
//! shape that discipline exists to produce.
//!
//! ## `drop_scratch` replaces the tier rather than truncating it
//!
//! The brief asks for "truncate + clear", which would keep the scratch
//! arrays' capacity from one declaration to the next.  It is not written that
//! way, for a reason that is about the model and not about speed: Aeneas
//! models neither `Vec::clear` nor `Vec::truncate`
//! (`vendor/aeneas/backends/lean/Aeneas/Std/Vec.lean` has `new`, `push`,
//! `len`, `index`, `insert`, `resize`, `with_capacity` and nothing else), so
//! either one would put a fresh external hole into the extracted model for an
//! operation the Lean twin does not perform — `NStore.dropScratch` is
//! `{ st with scr := NTables.empty, scratchOn := false }`.  Replacing the
//! tier is the twin's own step, and `ron::HashMap::new` allocates nothing at
//! all (task #35's lazy allocation), so the cons tables cost the same either
//! way; only the ten `Vec`s re-grow, which P6 measures.

use crate::kernel::core_types::code_points;
use crate::kernel::core_types::CheckError;
use crate::kernel::expr;
use crate::kernel::expr::BinderMeta;
use crate::kernel::expr::Literal;
use crate::kernel::name;
use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;
use crate::ron::hashmap::Dup;
use crate::ron::hashmap::Eq2;
// The arena's tables are the epoch-stamped open-addressed map
// (DESIGN.md's `Task #97-P6-4b`), aliased so that every use site below
// reads as it did.  `ron::hashmap::HashMap` is still what `crates/con-ron`
// uses, and is still the one with proofs.
use crate::ron::hashmap2::HashMap2 as HashMap;
use crate::ron::hashmap::Hashable;

use crate::arena::core_state::reset_map;
use std::vec::Vec;

use crate::arena::handle::e_tag_is_bind;
use crate::arena::handle::BMIdx;
use crate::arena::handle::EIdx;
use crate::arena::handle::LIdx;
use crate::arena::handle::LsIdx;
use crate::arena::handle::NIdx;
use crate::arena::handle::ETAG_APP;
use crate::arena::handle::ETAG_BVAR;
use crate::arena::handle::ETAG_CONST;
use crate::arena::handle::ETAG_FORALL_E;
use crate::arena::handle::ETAG_FVAR;
use crate::arena::handle::ETAG_LAM;
use crate::arena::handle::ETAG_LET_E;
use crate::arena::handle::ETAG_LIT;
use crate::arena::handle::ETAG_PROJ;
use crate::arena::handle::ETAG_SORT;
use crate::arena::handle::IDX_CAP;
use crate::arena::handle::LSTAG_LIST;
use crate::arena::handle::LTAG_IMAX;
use crate::arena::handle::LTAG_MAX;
use crate::arena::handle::LTAG_PARAM;
use crate::arena::handle::LTAG_SUCC;
use crate::arena::handle::LTAG_ZERO;
use crate::arena::handle::NTAG_ANONYMOUS;
use crate::arena::handle::NTAG_NUM;
use crate::arena::handle::NTAG_STR;
use crate::arena::handle::TIER_P;
use crate::arena::handle::TIER_S;

// ---------------------------------------------------------------------------
// `Native` messages for the 2^27 cap (DESIGN.md §8.3)
// ---------------------------------------------------------------------------

/// con-leche: none — the port's own `Native` decline, which con-leche cannot raise (DESIGN.md §3.4, task #67)
/// `"arena: name constructor at capacity"`, as code points (DESIGN.md §3.3:
/// the core has no `&str` constant, task #86).
const M_N_CAP: [u32; 36] = [
    97, 114, 101, 110, 97, 58, 32, 110, 97, 109, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99,
    116, 111, 114, 32, 97, 116, 32, 99, 97, 112, 97, 99, 105, 116, 121, 10,
];

/// con-leche: none — the port's own `Native` decline, which con-leche cannot raise (DESIGN.md §3.4, task #67)
/// `"arena: level constructor at capacity"`, as code points.
const M_L_CAP: [u32; 37] = [
    97, 114, 101, 110, 97, 58, 32, 108, 101, 118, 101, 108, 32, 99, 111, 110, 115, 116, 114, 117,
    99, 116, 111, 114, 32, 97, 116, 32, 99, 97, 112, 97, 99, 105, 116, 121, 10,
];

/// con-leche: none — the port's own `Native` decline, which con-leche cannot raise (DESIGN.md §3.4, task #67)
/// `"arena: level list at capacity"`, as code points.
const M_LS_CAP: [u32; 30] = [
    97, 114, 101, 110, 97, 58, 32, 108, 101, 118, 101, 108, 32, 108, 105, 115, 116, 32, 97, 116,
    32, 99, 97, 112, 97, 99, 105, 116, 121, 10,
];

/// con-leche: none — arena infrastructure (task #97-P6-6b); the frozen-tier guard
/// `"arena: append to a frozen persistent tier"`, as code points — **the
/// frozen-tier guard**.  A store whose persistent tier is SHARED
/// (`shared_on`) may append to its scratch tier and to nothing else: a
/// persistent append would hand back a handle whose index names a node of the
/// shared tier, which is the one way the split could lose `denoteE`'s
/// injectivity.  Phase B never takes the branch — `check_pending` opens the
/// scratch tier before any term is built, and `intern_persistent`'s only
/// caller is `arena::promote`, which is phase A's — so the guard states the
/// discipline rather than walking a path the run takes.  It is raised as the
/// port's own `Native` decline (task #97-P5-Usize, the maintainer's ruling):
/// con-leche and the twin have no frozen tier, so the refinement claims
/// nothing when it fires, exactly as for the capacity guard beside it.
const M_FROZEN: [u32; 41] = [
    97, 114, 101, 110, 97, 58, 32, 97, 112, 112, 101, 110, 100, 32, 116, 111, 32, 97, 32, 102,
    114, 111, 122, 101, 110, 32, 112, 101, 114, 115, 105, 115, 116, 101, 110, 116, 32, 116, 105,
    101, 114,
];

/// con-leche: none — the port's own `Native` decline, which con-leche cannot raise (DESIGN.md §3.4, task #67)
/// `"arena: expr constructor at capacity"`, as code points.
const M_E_CAP: [u32; 36] = [
    97, 114, 101, 110, 97, 58, 32, 101, 120, 112, 114, 32, 99, 111, 110, 115, 116, 114, 117, 99,
    116, 111, 114, 32, 97, 116, 32, 99, 97, 112, 97, 99, 105, 116, 121, 10,
];

// ---------------------------------------------------------------------------
// The generic interned table (`Store.lean:53-105`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:84-88 Tbl.derAt
/// The `[Inhabited δ]` of the Lean's `Tbl.derAt`: the derived word a read
/// past the end of the column answers with.  The range is a `StoreWF` clause,
/// so the fallback is never taken on a well-formed store; it exists because
/// `derAt` is total.  Spelled as the crate's own one-method trait rather than
/// `core::default::Default`, for the reason `ron::hashmap::Eq2` gives.
pub trait DerDefault {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:84-88 Tbl.derAt
    /// The value `derAt` answers with out of range.
    fn der_default() -> Self;
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:84-88 Tbl.derAt
/// The name and expression columns are a bare `u64`, whose `Inhabited` is `0`.
impl DerDefault for u64 {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:84-88 Tbl.derAt
    fn der_default() -> u64 {
        0
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:61-67 Tbl
/// nanoda's `UniqueIndexSet<A>` (`util.rs:28-33`) with con-leche's parallel
/// derived array beside it (lesson 1: derived data never lives inside the
/// cons key).  One constructor's array of one tier: the node records, the
/// parallel derived words, and the cons table from record to handle.
/// **The node record and its derived word are ONE column** (task #97-P6-5,
/// lever 3).  They were two parallel `Vec`s, so a `view` that needs both —
/// which is every substituting walk, whose cutoff reads `der` and whose body
/// then reads the record — paid two independent indexed loads into two
/// arrays, i.e. two cache misses on a cold node.  Mathlib's persistent tier
/// is 110 M expression nodes over a 32 MB L3, so those misses are the run's
/// cost rather than a constant factor: the profile of task #97-P6-5 puts
/// `ETables::der_at` + `::get` + `EStore::der_of_view` at 7.6 % of a Mathlib
/// prefix on top of what the walks pay inline.  Interleaving costs no memory
/// (the derived word rides in the padding the record already had in every one
/// of the eighteen instantiations) and no hole; the twin's `Tbl` keeps its two
/// fields and the refinement reads `rows.map (·.1)` for `nodes` and
/// `rows.map (·.2)` for `der`.
pub struct Tbl<A, I, D> {
    pub rows: Vec<(A, D)>,
    pub cons: HashMap<A, I>,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:61-67 Tbl
/// The six operations of the Lean's `Tbl` namespace.  One `impl` with every
/// bound, rather than the Lean's `variable` block plus per-`def` instance
/// arguments: all seventeen instantiations satisfy all three bounds.
impl<A, I, D> Tbl<A, I, D>
where
    A: Hashable + Eq2 + Dup,
    I: Dup,
    D: Dup + DerDefault,
{
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:73-74 Tbl.empty
    pub fn empty() -> Tbl<A, I, D> {
        Tbl { rows: Vec::new(), cons: HashMap::new() }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:78-79 Tbl.size
    /// How many nodes this constructor has in this tier.
    pub fn size(&self) -> usize {
        self.rows.len()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:81-82 Tbl.node?
    /// Read one node record.  The Lean writes `t.nodes[n]?`; the bound test is
    /// explicit here because Aeneas models indexing and `len`, not `Vec::get`.
    #[inline(always)]
    pub fn node(&self, n: usize) -> Option<&A> {
        if n >= self.rows.len() {
            None
        } else {
            Some(&self.rows[n].0)
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:84-88 Tbl.derAt
    /// Read one derived word (`der_default` out of range).
    #[inline(always)]
    pub fn der_at(&self, n: usize) -> D {
        if n >= self.rows.len() {
            D::der_default()
        } else {
            self.rows[n].1.dup2()
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-17)
    /// **This constructor's array of this tier has no room for another node.**
    /// Two limits, and the first is the one that can be approached: the handle
    /// word gives the index 27 bits (`IDX_CAP`, §8.3), and the cons table's
    /// own slot vector cannot double past `usize::MAX / 2`
    /// (`HashMap2::is_saturated_full`, task #97-HM2 §4).
    pub fn full(&self) -> bool {
        if self.rows.len() >= IDX_CAP as usize {
            true
        } else {
            self.cons.is_saturated_full()
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:90-91 Tbl.find?
    /// The cons-table probe.
    pub fn find(&self, a: &A) -> Option<I> {
        match self.cons.get(a) {
            None => None,
            Some(i) => Some(i.dup2()),
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-17); Lean twin:
    /// **none owed** — the cons-table probe that also hands back the slot a
    /// miss would be written at.  `find?` is its second component, and the
    /// twin keeps `find?` then `push`: the pair is `Refine/HashMap2.lean`'s
    /// `find_or_insert_refines`, which says it means what `insert` means, so
    /// the refinement ABSORBS the split (the slot index is a representation
    /// and `find_slot`'s `ensure_slots` is an allocation).
    ///
    /// It is what makes an interning miss cost ONE hash and ONE probe run
    /// instead of two (task #97-survey's N2): `find` then `push` probed the
    /// same table for the same record twice, and between the two the caller
    /// only computes the derived word and the handle.
    pub fn find_slot(&mut self, a: &A) -> (usize, Option<I>) {
        self.cons.find_slot(a)
    }

    /// con-leche: none — arena infrastructure (task #97-P6-17); Lean twin:
    /// **none owed** — `Tbl.push` with the cons row written at the slot
    /// `find_slot` returned.  Same value as `push`; see `find_slot`.
    pub fn push_at(&mut self, at: usize, a: A, d: D, i: I) {
        self.cons.insert_at(at, a.dup2(), i);
        self.rows.push((a, d));
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:93-98 Tbl.push
    /// Append a node with its derived word and register it in the cons table.
    /// The record is stored twice, as the Lean stores it twice — once as the
    /// array element and once as the cons key — so the caller hands over one
    /// and `push` copies it into the table.
    pub fn push(&mut self, a: A, d: D, i: I) {
        self.cons.insert(a.dup2(), i);
        self.rows.push((a, d));
    }

    /// con-leche: none — arena infrastructure (task #97-P6-1); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:73-74 Tbl.empty` — the same VALUE as
    /// `empty`, with the cons table's bucket array kept
    /// (`arena::core_state::reset_map`).  The scratch tier is emptied twice
    /// per declaration (`enable_scratch` and `drop_scratch`), 57 362 times on
    /// `Init`, and task #97-P4f measured the bucket arrays growing back from
    /// `MIN_CAPACITY` at 15.6 % of the run.
    ///
    /// The node column is *not* kept, and that is deliberate: Aeneas
    /// models neither `Vec::clear` nor `Vec::truncate` (task #97-P4a's third
    /// extraction rule), so keeping it would cost an external hole, and
    /// what it would buy is the column's re-growth alone — under the 0.9 %
    /// the same profile attributes to `RawVec::finish_grow` over the whole
    /// run, persistent tier included.  `Vec::new` allocates nothing.
    ///
    /// **Nor are they PRE-SIZED, and that is measured** (task #97-P6-4a,
    /// §8.6's item 4: "size `enter_scratch` from the previous declaration's
    /// high-water mark").  `Vec::with_capacity(self.rows.len())` here needs
    /// no hole — `with_capacity` is modelled and is `[]` abstractly — and a
    /// tier that shrinks would still shrink, the size being the last LENGTH
    /// and never the last capacity.  It was worth −0.08 % of `Init`'s
    /// instructions against `ron::hashmap`'s chained table and **+0.08 %**
    /// against `ron::hashmap2`'s (413.74 G without it, 414.05 G with, on the
    /// same tree), because it trades the doubling ladder for one allocation
    /// per table per declaration and the ladder is three or four rungs from
    /// zero.  So the lever stays priced and untaken.
    pub fn reset(&mut self) {
        self.rows = Vec::new();
        reset_map(&mut self.cons)
    }

    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    /// A copy of this table that shares nothing with it: the row column, and
    /// the cons table by `HashMap2::dup`.  It exists for one caller,
    /// `arena::checker_base::attempt_snapshot` (task #97-T2-LOCKSTEP D4), which
    /// copies a tier's SCRATCH tables so that `attempt_restore` can put them
    /// back after a failed variant attempt.  Aeneas models neither
    /// `Vec::truncate` nor `Vec::clear` (this module's note on `drop_scratch`),
    /// so a restore is a whole value moved back, and this is the copy it moves.
    pub fn dup(&self) -> Tbl<A, I, D> {
        let n = self.rows.len();
        Tbl {
            rows: Tbl::<A, I, D>::dup_rows(&self.rows, Vec::with_capacity(n), 0, n),
            cons: self.cons.dup(),
        }
    }

    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    /// `dup`'s row walk over `[lo, hi)`, pushing the copies onto `out` in index
    /// order.  **Halved rather than peeled**, for `checker_base::vec_dup_range`'s
    /// reason: a peeling recursion is one frame per row, which is a stack
    /// overflow on a long tier (task #97-P6-2).  The accumulator is passed by
    /// value and returned.
    fn dup_rows(src: &Vec<(A, D)>, out: Vec<(A, D)>, lo: usize, hi: usize) -> Vec<(A, D)> {
        if hi > lo {
            let n = hi - lo;
            if n == 1 {
                let mut out2 = out;
                out2.push((src[lo].0.dup2(), src[lo].1.dup2()));
                out2
            } else {
                let mid = lo + n / 2;
                let out2 = Tbl::<A, I, D>::dup_rows(src, out, lo, mid);
                Tbl::<A, I, D>::dup_rows(src, out2, mid, hi)
            }
        } else {
            out
        }
    }
}

// ---------------------------------------------------------------------------
// Strings and level lists: the two non-scalar fields of a node record
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; the `Hashable (List LIdx)` of `Store.lean:227-229 ListNode`
/// Lean's `Hashable (List α)`, a left fold of `mixHash` from `7`.  The value
/// is verdict-neutral (DESIGN.md §3.2: a hash need only be *a* function of the
/// value), so what matters is that the Rust and the Lean agree on which
/// *values* collide, which a fold over the same words does.
pub fn lidx_vec_hash(us: &Vec<LIdx>) -> u64 {
    lidx_vec_hash_from(us, 0, 7)
}

/// con-leche: none — the index recursion behind `lidx_vec_hash`
/// No loops (DESIGN.md §3.4).
pub fn lidx_vec_hash_from(us: &Vec<LIdx>, i: usize, acc: u64) -> u64 {
    if i >= us.len() {
        acc
    } else {
        lidx_vec_hash_from(us, i + 1, name::mix_hash(acc, us[i].hash64()))
    }
}

/// con-leche: none — arena infrastructure; the `DecidableEq (List LIdx)` of `Store.lean:227-229 ListNode`
/// Pointwise equality of two universe-argument lists.
pub fn lidx_vec_eq(a: &Vec<LIdx>, b: &Vec<LIdx>) -> bool {
    if a.len() != b.len() {
        false
    } else {
        lidx_vec_eq_from(a, b, 0)
    }
}

/// con-leche: none — the index recursion behind `lidx_vec_eq`
/// No loops (DESIGN.md §3.4).
pub fn lidx_vec_eq_from(a: &Vec<LIdx>, b: &Vec<LIdx>, i: usize) -> bool {
    if i >= a.len() {
        true
    } else if a[i].word == b[i].word {
        lidx_vec_eq_from(a, b, i + 1)
    } else {
        false
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
/// Copy a universe-argument list.
pub fn lidx_vec_dup(us: &Vec<LIdx>) -> Vec<LIdx> {
    lidx_vec_dup_from(us, 0, Vec::with_capacity(us.len()))
}

/// con-leche: none — the index recursion behind `lidx_vec_dup`
/// The accumulator is passed by value and returned (DESIGN.md §3.4 reserves
/// `&mut` for the state parameter).
pub fn lidx_vec_dup_from(us: &Vec<LIdx>, i: usize, out: Vec<LIdx>) -> Vec<LIdx> {
    if i >= us.len() {
        out
    } else {
        let mut o: Vec<LIdx> = out;
        o.push(us[i].dup2());
        lidx_vec_dup_from(us, i + 1, o)
    }
}

// ---------------------------------------------------------------------------
// Names (`Store.lean:102-147`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Store.lean:104-108 AnonNode` — the
/// `anonymous` constructor, line 35.
pub struct AnonNode {}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Store.lean:110-115 StrNode` — the `str`
/// constructor, line 36.  Deviation (DESIGN.md §3.3): the component is a
/// `Vec<u32>` of code points, as every string in the verified core is.
pub struct StrNode {
    pub pre: NIdx,
    pub s: Vec<u32>,
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Store.lean:117-122 NumNode` — the `num`
/// constructor, line 37.  Deviation (DESIGN.md §3.3): the Lean's `Nat` is a
/// `u64`, as every de Bruijn index and name component in the core is.
pub struct NumNode {
    pub pre: NIdx,
    pub n: u64,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:104-108 AnonNode
/// The cited structure's `deriving Hashable`: the constructor index (a
/// structure has one, `0`) and no fields to fold in.
impl Hashable for AnonNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:104-108 AnonNode
    fn hash64(&self) -> u64 {
        0
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:110-115 StrNode
/// `deriving Hashable`: `mixHash` folded over the fields from the
/// constructor index.
impl Hashable for StrNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:110-115 StrNode
    fn hash64(&self) -> u64 {
        name::mix_hash(name::mix_hash(0, self.pre.hash64()), name::str_hash(&self.s))
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:117-122 NumNode
impl Hashable for NumNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:117-122 NumNode
    fn hash64(&self) -> u64 {
        name::mix_hash(name::mix_hash(0, self.pre.hash64()), name::nat_hash(self.n))
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:124 instBEqAnonNode
impl Eq2 for AnonNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:124 instBEqAnonNode
    fn eq2(&self, _other: &AnonNode) -> bool {
        true
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:125 instBEqStrNode
impl Eq2 for StrNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:125 instBEqStrNode
    fn eq2(&self, other: &StrNode) -> bool {
        if self.pre.word == other.pre.word {
            name::str_eq(&self.s, &other.s)
        } else {
            false
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:126 instBEqNumNode
impl Eq2 for NumNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:126 instBEqNumNode
    fn eq2(&self, other: &NumNode) -> bool {
        if self.pre.word == other.pre.word {
            self.n == other.n
        } else {
            false
        }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for AnonNode {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> AnonNode {
        AnonNode {}
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for StrNode {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> StrNode {
        StrNode { pre: self.pre.dup2(), s: expr::str_copy(&self.s) }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for NumNode {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> NumNode {
        NumNode { pre: self.pre.dup2(), n: self.n }
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Store.lean:128-134 NNodeView` — the
/// store-side view of a name node: con-leche's three constructors with the
/// prefix as a handle.
pub enum NNodeView {
    Anonymous,
    Str(NIdx, Vec<u32>),
    Num(NIdx, u64),
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:136-140 NTables
/// One tier of the name store.
pub struct NTables {
    pub anons: Tbl<AnonNode, NIdx, u64>,
    pub strs: Tbl<StrNode, NIdx, u64>,
    pub nums: Tbl<NumNode, NIdx, u64>,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:142-147 NStore
/// The name store: two tiers and the scratch flag (DESIGN.md §8.3).
pub struct NStore {
    pub pers: NTables,
    pub scr: NTables,
    pub scratch_on: bool,
    /// The persistent tier is SHARED — this store's own `pers` is empty and
    /// every persistent read goes to the `PersTier` parameter, which a
    /// persistent append may not (task #97-P6-6b's frozen-tier guard).
    pub shared_on: bool,
}

// ---------------------------------------------------------------------------
// Levels (`Store.lean:149-214`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:41-46 Level
/// Lean twin: `proof/ConRon/Arena/Store.lean:151-155 ZeroNode` — the `zero`
/// constructor, line 41.
pub struct ZeroNode {}

/// con-leche: ConLeche/Kernel/Expr.lean:41-46 Level
/// Lean twin: `proof/ConRon/Arena/Store.lean:157-161 SuccNode` — the `succ`
/// constructor, line 42.
pub struct SuccNode {
    pub u: LIdx,
}

/// con-leche: ConLeche/Kernel/Expr.lean:41-46 Level
/// Lean twin: `proof/ConRon/Arena/Store.lean:163-169 BinLNode` — the `max`
/// constructor, line 43, and `imax`, line 44, which has the same two fields
/// and therefore the same record in its own array.
pub struct BinLNode {
    pub u: LIdx,
    pub v: LIdx,
}

/// con-leche: ConLeche/Kernel/Expr.lean:41-46 Level
/// Lean twin: `proof/ConRon/Arena/Store.lean:171-175 ParamNode` — the `param`
/// constructor, line 45.
pub struct ParamNode {
    pub n: NIdx,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:151-155 ZeroNode
impl Hashable for ZeroNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:151-155 ZeroNode
    fn hash64(&self) -> u64 {
        0
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:157-161 SuccNode
impl Hashable for SuccNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:157-161 SuccNode
    fn hash64(&self) -> u64 {
        name::mix_hash(0, self.u.hash64())
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:163-169 BinLNode
impl Hashable for BinLNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:163-169 BinLNode
    fn hash64(&self) -> u64 {
        name::mix_hash(name::mix_hash(0, self.u.hash64()), self.v.hash64())
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:171-175 ParamNode
impl Hashable for ParamNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:171-175 ParamNode
    fn hash64(&self) -> u64 {
        name::mix_hash(0, self.n.hash64())
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:177 instBEqZeroNode
impl Eq2 for ZeroNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:177 instBEqZeroNode
    fn eq2(&self, _other: &ZeroNode) -> bool {
        true
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:178 instBEqSuccNode
impl Eq2 for SuccNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:178 instBEqSuccNode
    fn eq2(&self, other: &SuccNode) -> bool {
        self.u.word == other.u.word
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:179 instBEqBinLNode
impl Eq2 for BinLNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:179 instBEqBinLNode
    fn eq2(&self, other: &BinLNode) -> bool {
        if self.u.word == other.u.word {
            self.v.word == other.v.word
        } else {
            false
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:180 instBEqParamNode
impl Eq2 for ParamNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:180 instBEqParamNode
    fn eq2(&self, other: &ParamNode) -> bool {
        self.n.word == other.n.word
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for ZeroNode {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> ZeroNode {
        ZeroNode {}
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for SuccNode {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> SuccNode {
        SuccNode { u: self.u.dup2() }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for BinLNode {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> BinLNode {
        BinLNode { u: self.u.dup2(), v: self.v.dup2() }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for ParamNode {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> ParamNode {
        ParamNode { n: self.n.dup2() }
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:41-46 Level
/// Lean twin: `proof/ConRon/Arena/Store.lean:182-190 LNodeView` — the
/// store-side view of a level node.
pub enum LNodeView {
    Zero,
    Succ(LIdx),
    Max(LIdx, LIdx),
    Imax(LIdx, LIdx),
    Param(NIdx),
}

/// con-leche: ConLeche/Kernel/Expr.lean:41-54 Level
/// Lean twin: `proof/ConRon/Arena/Store.lean:192-199 LDer` — the `hashData`
/// computed field, lines 47-53, plus the has-a-parameter flag, which
/// con-leche recomputes by a walk (`Kernel/Expr.lean:114-122 levelHasParam`)
/// because a `Level` tree has nowhere to cache it.
pub struct LDer {
    pub hash: u64,
    pub has_param: bool,
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for LDer {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> LDer {
        LDer { hash: self.hash, has_param: self.has_param }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:192-199 LDer
/// The Lean's `deriving Inhabited` on the pair, i.e. `⟨0, false⟩`.
impl DerDefault for LDer {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:192-199 LDer
    fn der_default() -> LDer {
        LDer { hash: 0, has_param: false }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:201-207 LTables
/// One tier of the level store.
pub struct LTables {
    pub zeros: Tbl<ZeroNode, LIdx, LDer>,
    pub succs: Tbl<SuccNode, LIdx, LDer>,
    pub maxs: Tbl<BinLNode, LIdx, LDer>,
    pub imaxs: Tbl<BinLNode, LIdx, LDer>,
    pub params: Tbl<ParamNode, LIdx, LDer>,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:209-214 LStore
/// The level store, over the name store.
pub struct LStore {
    pub ns: NStore,
    pub pers: LTables,
    pub scr: LTables,
    pub scratch_on: bool,
    /// The persistent tier is SHARED — this store's own `pers` is empty and
    /// every persistent read goes to the `PersTier` parameter, which a
    /// persistent append may not (task #97-P6-6b's frozen-tier guard).
    pub shared_on: bool,
}

// ---------------------------------------------------------------------------
// Level lists (`Store.lean:216-246`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:225-229 ListNode
/// The interned universe-argument list (nanoda's `LevelsPtr`, `util.rs:84`),
/// so that comparing two `const` nodes' level arguments is one word
/// comparison.  Deviation from the Lean's `List LIdx`: a `Vec<LIdx>`, which
/// is what the rest of the verified core spells a Lean `List` as.
pub struct ListNode {
    pub us: Vec<LIdx>,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:225-229 ListNode
impl Hashable for ListNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:225-229 ListNode
    fn hash64(&self) -> u64 {
        name::mix_hash(0, lidx_vec_hash(&self.us))
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:231 instBEqListNode
impl Eq2 for ListNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:231 instBEqListNode
    fn eq2(&self, other: &ListNode) -> bool {
        lidx_vec_eq(&self.us, &other.us)
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for ListNode {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> ListNode {
        ListNode { us: lidx_vec_dup(&self.us) }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:233-234 LsNodeView
/// The store-side view of a level-list node.
pub type LsNodeView = Vec<LIdx>;

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:236-239 LsTables
/// One tier of the level-list store (a single constructor).
pub struct LsTables {
    pub lists: Tbl<ListNode, LsIdx, LDer>,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:241-246 LsStore
/// The level-list store, over the level store.
pub struct LsStore {
    pub ls: LStore,
    pub pers: LsTables,
    pub scr: LsTables,
    pub scratch_on: bool,
    /// The persistent tier is SHARED — this store's own `pers` is empty and
    /// every persistent read goes to the `PersTier` parameter, which a
    /// persistent append may not (task #97-P6-6b's frozen-tier guard).
    pub shared_on: bool,
}

// ---------------------------------------------------------------------------
// Expressions (`Store.lean:248-363`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:250-254 BVarNode` — the `bvar`
/// constructor, line 344.  Deviation (DESIGN.md §3.3): the Lean's `Nat` is a
/// `u64`, as `expr::bvar`'s index already is.
pub struct BVarNode {
    pub i: u64,
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:256-261 FVarNode` — the `fvar`
/// constructor, line 345.
pub struct FVarNode {
    pub idx: u64,
    pub ty: EIdx,
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:263-267 SortNode` — the `sort`
/// constructor, line 346.
pub struct SortNode {
    pub u: LIdx,
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:269-274 ConstNode` — the `const`
/// constructor, line 347.  Two words: the level arguments are one interned
/// handle, not a list.
pub struct ConstNode {
    pub n: NIdx,
    pub us: LsIdx,
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:276-281 AppNode` — the `app`
/// constructor, line 348.  Eight bytes of node and eight of derived word,
/// which is what DESIGN.md §8.5 prices the representation at.
pub struct AppNode {
    pub f: EIdx,
    pub a: EIdx,
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:283-291 BindNode` — the `lam`
/// constructor, line 349, and `forallE`, line 350: same three fields, its own
/// array.
pub struct BindNode {
    pub ty: EIdx,
    pub body: EIdx,
    pub m: BMIdx,
}

/// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
/// Lean twin: `proof/ConRon/Arena/Store.lean:293-311 BMNode` — `BMNode`, the
/// binder-datum store's one record: a `BinderMeta`'s `PropWhen`, hash-consed
/// exactly as every other node of the arena is, so that a `BindNode` names it
/// by a `u32`.
///
/// **Why the datum leaves the node record** (task #97-P6-10 §3, priced there
/// and taken here).  `PropWhen` is sixteen bytes and `Arc`-carrying at
/// `one`/`two`/`many`, so the binder record was twenty-four bytes with a
/// reference count inside it: `Tbl<BindNode>::dup2` was a `binder_meta_dup`,
/// `Tbl<BindNode>::eq2` a `prop_when::beq` and `hash64` a `hash_pw`, at every
/// probe of the two hottest cons tables after `apps`.  Interned, the record is
/// three `u32`s of POD and the datum is compared, hashed and copied ONCE per
/// distinct value instead of once per binder node.
///
/// The cons discipline is the store's own (DESIGN.md §8.3): the persistent
/// table is probed before the scratch one, so a scratch datum never
/// duplicates a persistent one and `BMIdx` equality is `PropWhen` equality —
/// which is what keeps `denote` injective on `lam`/`forallE` now that the
/// node record names the datum rather than holding it.
pub struct BMNode {
    pub pw: PropWhen,
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:313-319 LetNode` — the `letE`
/// constructor, line 351.
pub struct LetNode {
    pub ty: EIdx,
    pub val: EIdx,
    pub body: EIdx,
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:321-325 LitNode` — the `lit`
/// constructor, line 352.
pub struct LitNode {
    pub l: Literal,
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:327-333 ProjNode` — the `proj`
/// constructor, line 353.
pub struct ProjNode {
    pub n: NIdx,
    pub i: u64,
    pub e: EIdx,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:250-254 BVarNode
impl Hashable for BVarNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:250-254 BVarNode
    fn hash64(&self) -> u64 {
        name::nat_hash(self.i)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:256-261 FVarNode
impl Hashable for FVarNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:256-261 FVarNode
    fn hash64(&self) -> u64 {
        fold3(self.ty.hash64(), name::nat_hash(self.idx))
    }
}

/// con-leche: none — arena infrastructure (task #97-P6-13); Lean twin: none —
/// the twin hashes a cons key with a `Lean.mixHash` chain per field; this
/// packing is the port's replacement for it
/// **The cons-table hash of a node: the fields PACKED, not mixed.**
///
/// A hash is verdict-neutral (DESIGN.md §3.2: any function of the value will
/// do, and `ron::hashmap2`'s own note says the refinement never looks inside
/// one — the owed `Inv` says only that a key sits where `home_index` puts
/// it).  So the question is what is cheapest that the table's FINALIZER can
/// still spread, and `home_index` is already a multiply-xor avalanche over
/// the whole word.  A handle is a `u32`, so two of them are one `u64`
/// INJECTIVELY and the packing loses nothing at all, where `Lean.mixHash` was
/// five instructions per field on top — paid on every probe of every intern
/// attempt, twice per attempt for the two tiers.
///
/// **Measured** (`Init`, task #97-P6-13 §4): the bare packing is 233.32 G
/// against 242.31 G for the `mixHash` chains, and wrapping the packed word in
/// ONE `mixHash` — better avalanche, five more instructions — is 235.94 G and
/// 110.1 G cycles against the bare packing's 108.5–109.9 G, i.e. the extra
/// mixing costs on both columns and buys no shorter probe.  Two handle words
/// as one `u64`: one `or` and one shift.
fn pack2(a: u32, b: u32) -> u64 {
    (a as u64) | ((b as u64) << 32)
}

/// con-leche: none — arena infrastructure (task #97-P6-13); Lean twin: none —
/// the twin hashes a cons key with a `Lean.mixHash` chain per field; this fold
/// is the port's replacement for it A third datum folded into a packed pair.
/// The pair already fills the word, so a third field is the one place that
/// needs mixing; the constant is `home_index`'s own.
fn fold3(ab: u64, c: u64) -> u64 {
    ab ^ c.wrapping_mul(0x9e3779b97f4a7c15)
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:263-267 SortNode
impl Hashable for SortNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:263-267 SortNode
    fn hash64(&self) -> u64 {
        self.u.hash64()
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:269-274 ConstNode
impl Hashable for ConstNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:269-274 ConstNode
    fn hash64(&self) -> u64 {
        pack2(self.n.word, self.us.word)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:276-281 AppNode
impl Hashable for AppNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:276-281 AppNode
    fn hash64(&self) -> u64 {
        pack2(self.f.word, self.a.word)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:283-291 BindNode
impl Hashable for BindNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:283-291 BindNode
    ///
    /// **Three words, packed** (task #97-P6-16): the datum is a `BMIdx` now,
    /// so the record hashes the way `ProjNode` and `LetNode` do — the two
    /// handles into one `u64` by `pack2`, folded with the third — instead of
    /// folding in a `hash_pw` that walked a `PropWhen`.
    fn hash64(&self) -> u64 {
        fold3(pack2(self.ty.word, self.body.word), self.m.word as u64)
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
/// Lean twin: `proof/ConRon/Arena/Store.lean:293-311 BMNode` — the binder-datum
/// store's cons key.
impl Hashable for BMNode {
    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Store.lean:293-311 BMNode` —
    /// `PropWhen.hash`, which is what the binder record used to fold in at
    /// every probe.
    fn hash64(&self) -> u64 {
        prop_when::hash_pw(&self.pw)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:313-319 LetNode
impl Hashable for LetNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:313-319 LetNode
    fn hash64(&self) -> u64 {
        fold3(pack2(self.ty.word, self.val.word), self.body.hash64())
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:321-325 LitNode
impl Hashable for LitNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:321-325 LitNode
    fn hash64(&self) -> u64 {
        expr::literal_hash(&self.l)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:327-333 ProjNode
impl Hashable for ProjNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:327-333 ProjNode
    fn hash64(&self) -> u64 {
        fold3(pack2(self.n.word, self.e.word), name::nat_hash(self.i))
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:335 instBEqBVarNode
impl Eq2 for BVarNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:335 instBEqBVarNode
    fn eq2(&self, other: &BVarNode) -> bool {
        self.i == other.i
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:336 instBEqFVarNode
impl Eq2 for FVarNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:336 instBEqFVarNode
    fn eq2(&self, other: &FVarNode) -> bool {
        if self.idx == other.idx {
            self.ty.word == other.ty.word
        } else {
            false
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:337 instBEqSortNode
impl Eq2 for SortNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:337 instBEqSortNode
    fn eq2(&self, other: &SortNode) -> bool {
        self.u.word == other.u.word
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:338 instBEqConstNode
impl Eq2 for ConstNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:338 instBEqConstNode
    fn eq2(&self, other: &ConstNode) -> bool {
        if self.n.word == other.n.word {
            self.us.word == other.us.word
        } else {
            false
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:339 instBEqAppNode
impl Eq2 for AppNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:339 instBEqAppNode
    fn eq2(&self, other: &AppNode) -> bool {
        if self.f.word == other.f.word {
            self.a.word == other.a.word
        } else {
            false
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:340 instBEqBindNode
impl Eq2 for BindNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:340 instBEqBindNode
    fn eq2(&self, other: &BindNode) -> bool {
        if self.ty.word == other.ty.word {
            if self.body.word == other.body.word {
                self.m.word == other.m.word
            } else {
                false
            }
        } else {
            false
        }
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
/// Lean twin: `proof/ConRon/Arena/Store.lean:341 instBEqBMNode` — the
/// binder-datum store's key equality, which is `BinderMeta`'s own `DecidableEq`
/// (`expr::binder_meta_beq`'s body).
impl Eq2 for BMNode {
    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Store.lean:341 instBEqBMNode`
    fn eq2(&self, other: &BMNode) -> bool {
        prop_when::beq(&self.pw, &other.pw)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:342 instBEqLetNode
impl Eq2 for LetNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:342 instBEqLetNode
    fn eq2(&self, other: &LetNode) -> bool {
        if self.ty.word == other.ty.word {
            if self.val.word == other.val.word {
                self.body.word == other.body.word
            } else {
                false
            }
        } else {
            false
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:343 instBEqLitNode
impl Eq2 for LitNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:343 instBEqLitNode
    fn eq2(&self, other: &LitNode) -> bool {
        expr::literal_beq(&self.l, &other.l)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:344 instBEqProjNode
impl Eq2 for ProjNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:344 instBEqProjNode
    fn eq2(&self, other: &ProjNode) -> bool {
        if self.n.word == other.n.word {
            if self.i == other.i {
                self.e.word == other.e.word
            } else {
                false
            }
        } else {
            false
        }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for BVarNode {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> BVarNode {
        BVarNode { i: self.i }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for FVarNode {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> FVarNode {
        FVarNode { idx: self.idx, ty: self.ty.dup2() }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for SortNode {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> SortNode {
        SortNode { u: self.u.dup2() }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for ConstNode {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> ConstNode {
        ConstNode { n: self.n.dup2(), us: self.us.dup2() }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for AppNode {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> AppNode {
        AppNode { f: self.f.dup2(), a: self.a.dup2() }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for BindNode {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> BindNode {
        BindNode {
            ty: self.ty.dup2(),
            body: self.body.dup2(),
            m: self.m.dup2(),
        }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for BMNode {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> BMNode {
        BMNode { pw: prop_when::dup(&self.pw) }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for LetNode {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> LetNode {
        LetNode { ty: self.ty.dup2(), val: self.val.dup2(), body: self.body.dup2() }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for LitNode {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> LitNode {
        LitNode { l: expr::literal_dup(&self.l) }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for ProjNode {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> ProjNode {
        ProjNode { n: self.n.dup2(), i: self.i, e: self.e.dup2() }
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:346-361 ENodeView` — the
/// store-side view of an expression node: con-leche's ten constructors with
/// every subterm replaced by a handle.  `BinderMeta` and `Literal` stay
/// *values* (they are not expressions), exactly as DESIGN.md §8.3 specifies,
/// and they are `con-ron-core`'s own types.
pub enum ENodeView {
    BVar(u64),
    FVar(u64, EIdx),
    Sort(LIdx),
    Const(NIdx, LsIdx),
    App(EIdx, EIdx),
    Lam(EIdx, EIdx, BinderMeta),
    ForallE(EIdx, EIdx, BinderMeta),
    LetE(EIdx, EIdx, EIdx),
    Lit(Literal),
    Proj(NIdx, u64, EIdx),
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:363-382 ETables
/// One tier of the expression store: ten arrays, ten derived columns, ten
/// cons tables.
pub struct ETables {
    pub bvars: Tbl<BVarNode, EIdx, u64>,
    pub fvars: Tbl<FVarNode, EIdx, u64>,
    pub sorts: Tbl<SortNode, EIdx, u64>,
    pub consts: Tbl<ConstNode, EIdx, u64>,
    pub apps: Tbl<AppNode, EIdx, u64>,
    pub lams: Tbl<BindNode, EIdx, u64>,
    pub foralls: Tbl<BindNode, EIdx, u64>,
    pub lets: Tbl<LetNode, EIdx, u64>,
    pub lits: Tbl<LitNode, EIdx, u64>,
    pub projs: Tbl<ProjNode, EIdx, u64>,
    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Store.lean:376-382 ETables.bms` — the tier's
    /// **binder-datum store**: the hash-consed `PropWhen`s the `lam` and
    /// `forallE` records name by a `BMIdx`, with the derived column holding
    /// `PropWhen.hash` so that `derOfBind`'s two scalars are one indexed load.
    /// It rides in `ETables` rather than beside it because it lives and dies
    /// with the tier exactly as the ten node arrays do.
    pub bms: Tbl<BMNode, BMIdx, u64>,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:384-392 EStore
/// The expression store, over the level-list store.  Two tiers: persistent
/// (parse + installed environment) and scratch (one declaration's check), the
/// tier bit of a handle selecting between them (DESIGN.md §8.3).
pub struct EStore {
    pub lss: LsStore,
    pub pers: ETables,
    pub scr: ETables,
    pub scratch_on: bool,
    /// The persistent tier is SHARED — this store's own `pers` is empty and
    /// every persistent read goes to the `PersTier` parameter, which a
    /// persistent append may not (task #97-P6-6b's frozen-tier guard).
    pub shared_on: bool,
}

// ---------------------------------------------------------------------------
// The persistent tier as ONE value (DESIGN.md §8.3, task #97-P6-6b)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:384-392 EStore
/// **The persistent tier of all four stores, as one value `n` phase-B workers
/// read by reference** — DESIGN.md §8.3's "the persistent tier is immutable in
/// phase B, each worker owns a scratch tier — no atomics anywhere", made
/// expressible.
///
/// Each store keeps its own `pers` field, which is the tier the PARSE and
/// phase A append to, and a `shared_on` flag beside `scratch_on`.  While the
/// flag is off — the parse, phase A, every test, and the whole single-lane
/// run — each persistent read goes to the owned field and the computation is
/// the one the tip performed, node for node.  While it is on, the owned field
/// is empty, a persistent append is refused (`M_FROZEN`) and every persistent
/// read goes to this record, which the driver holds and every worker borrows.
///
/// **Why a shared PARAMETER and not a field of the state.**  Task #97-P6-6
/// measured a region inside the threaded `&mut` state eight ways: a bare
/// `&u64` field on `AState` costs five function bodies Aeneas cannot
/// translate and the same borrow inside the four stores costs sixteen, while
/// everything else this split needs — the two-tier layout, the flag, the
/// value-returning readers below — extracts at zero errors.  So the sharing
/// arrives as an ordinary shared parameter, the shape `fe: &IFEnv` and `mode:
/// &CheckMode` already have, and the twin's monad becomes `ReaderT PersTier
/// (StateT AState (Except CheckError))`.
pub struct PersTier {
    pub n: NTables,
    pub l: LTables,
    pub ls: LsTables,
    pub e: ETables,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:384-392 EStore
impl PersTier {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:384-392 EStore
    /// The empty tier: what the parse and phase A are handed, since they read
    /// their own (`shared_on` false) and never this one.
    pub fn empty() -> PersTier {
        PersTier {
            n: NTables::empty(),
            l: LTables::empty(),
            ls: LsTables::empty(),
            e: ETables::empty(),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:466-471 EStore.nodeCount
    /// Expression nodes in the tier — the boundary figure `--progress` prints.
    pub fn e_count(&self) -> usize {
        self.e.count()
    }
}

// ---------------------------------------------------------------------------
// The name store's operations (`Store.lean:365-510`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:136-140 NTables
/// One tier's seven operations.
impl NTables {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:73-74 NTables.empty
    pub fn empty() -> NTables {
        NTables { anons: Tbl::empty(), strs: Tbl::empty(), nums: Tbl::empty() }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-1); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:73-74 NTables.empty` — the same value as `empty`,
    /// with the cons tables' bucket arrays kept (`Tbl::reset`).
    pub fn reset(&mut self) {
        self.anons.reset();
        self.strs.reset();
        self.nums.reset()
    }

    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    /// A copy of this tier, table by table (`Tbl::dup`): the scratch-tier
    /// snapshot of `arena::checker_base::attempt_snapshot` (task #97-T2-LOCKSTEP D4).
    pub fn dup(&self) -> NTables {
        NTables {
            anons: self.anons.dup(),
            strs: self.strs.dup(),
            nums: self.nums.dup(),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:403-404 NTables.count
    /// Nodes in this tier, over all constructors.
    pub fn count(&self) -> usize {
        self.anons.size() + self.strs.size() + self.nums.size()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:406-412 NTables.get
    /// Decode one handle against this tier's arrays.  The tier bit is *not*
    /// consulted: `NStore::view` selects the tier first.
    pub fn get(&self, i: &NIdx) -> Option<NNodeView> {
        if i.tag() == NTAG_ANONYMOUS {
            match self.anons.node(i.idx_nat()) {
                None => None,
                Some(_) => Some(NNodeView::Anonymous),
            }
        } else if i.tag() == NTAG_STR {
            match self.strs.node(i.idx_nat()) {
                None => None,
                Some(r) => Some(NNodeView::Str(r.pre.dup2(), expr::str_copy(&r.s))),
            }
        } else if i.tag() == NTAG_NUM {
            match self.nums.node(i.idx_nat()) {
                None => None,
                Some(r) => Some(NNodeView::Num(r.pre.dup2(), r.n)),
            }
        } else {
            None
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:84-88 NTables.derAt
    pub fn der_at(&self, i: &NIdx) -> u64 {
        if i.tag() == NTAG_ANONYMOUS {
            self.anons.der_at(i.idx_nat())
        } else if i.tag() == NTAG_STR {
            self.strs.der_at(i.idx_nat())
        } else if i.tag() == NTAG_NUM {
            self.nums.der_at(i.idx_nat())
        } else {
            0
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:90-91 NTables.find?
    /// The cons-table probe for a whole node view.
    pub fn find(&self, v: &NNodeView) -> Option<NIdx> {
        match v {
            NNodeView::Anonymous => self.anons.find(&AnonNode {}),
            NNodeView::Str(p, s) => {
                self.strs.find(&StrNode { pre: p.dup2(), s: expr::str_copy(s) })
            }
            NNodeView::Num(p, n) => self.nums.find(&NumNode { pre: p.dup2(), n: *n }),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:428-434 NTables.sizeOf
    /// The size of the constructor array `v` would land in; the capacity test
    /// is stated on it.
    pub fn size_of(&self, v: &NNodeView) -> usize {
        match v {
            NNodeView::Anonymous => self.anons.size(),
            NNodeView::Str(_, _) => self.strs.size(),
            NNodeView::Num(_, _) => self.nums.size(),
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-17)
    /// `Tbl::full` at the constructor array `v` would land in — the capacity
    /// test, dispatched exactly as `size_of` is.
    pub fn full_of(&self, v: &NNodeView) -> bool {
        match v {
            NNodeView::Anonymous => self.anons.full(),
            NNodeView::Str(_, _) => self.strs.full(),
            NNodeView::Num(_, _) => self.nums.full(),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:93-98 NTables.push
    /// Append a node to this tier, returning its handle.
    pub fn push(&mut self, v: NNodeView, d: u64, tier: u32) -> NIdx {
        match v {
            NNodeView::Anonymous => {
                let i: NIdx = NIdx::pack(NTAG_ANONYMOUS, tier, self.anons.size() as u32);
                self.anons.push(AnonNode {}, d, i.dup2());
                i
            }
            NNodeView::Str(p, s) => {
                let i: NIdx = NIdx::pack(NTAG_STR, tier, self.strs.size() as u32);
                self.strs.push(StrNode { pre: p, s }, d, i.dup2());
                i
            }
            NNodeView::Num(p, n) => {
                let i: NIdx = NIdx::pack(NTAG_NUM, tier, self.nums.size() as u32);
                self.nums.push(NumNode { pre: p, n }, d, i.dup2());
                i
            }
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:142-147 NStore
/// The name store's twelve operations.
impl NStore {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:73-74 NStore.empty
    pub fn empty() -> NStore {
        NStore {
            pers: NTables::empty(),
            scr: NTables::empty(),
            scratch_on: false,
            shared_on: false,
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-6b); Lean twin:
    /// `proof/ConRon/Arena/Store.lean` — the persistent arm of `NStore.view`
    ///
    /// One of the five **value-returning persistent readers** task #97-P6-6's
    /// design (A) is written around: the choice between this store's own
    /// persistent tier and the shared `PersTier` is made HERE and a value
    /// comes back, so no borrow ever leaves the choice and no region enters
    /// the record every function of the crate threads as `&mut`.
    fn pers_get(&self, pers: &PersTier, i: &NIdx) -> Option<NNodeView> {
        if self.shared_on {
            pers.n.get(i)
        } else {
            self.pers.get(i)
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-6b); Lean twin:
    /// `proof/ConRon/Arena/Store.lean` — the persistent arm of `NStore.derived`
    ///
    /// One of the five **value-returning persistent readers** task #97-P6-6's
    /// design (A) is written around: the choice between this store's own
    /// persistent tier and the shared `PersTier` is made HERE and a value
    /// comes back, so no borrow ever leaves the choice and no region enters
    /// the record every function of the crate threads as `&mut`.
    fn pers_der_at(&self, pers: &PersTier, i: &NIdx) -> u64 {
        if self.shared_on {
            pers.n.der_at(i)
        } else {
            self.pers.der_at(i)
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-6b); Lean twin:
    /// `proof/ConRon/Arena/Store.lean` — the persistent arm of `NStore.find?`
    ///
    /// One of the five **value-returning persistent readers** task #97-P6-6's
    /// design (A) is written around: the choice between this store's own
    /// persistent tier and the shared `PersTier` is made HERE and a value
    /// comes back, so no borrow ever leaves the choice and no region enters
    /// the record every function of the crate threads as `&mut`.
    fn pers_find(&self, pers: &PersTier, v: &NNodeView) -> Option<NIdx> {
        if self.shared_on {
            pers.n.find(v)
        } else {
            self.pers.find(v)
        }
    }


    /// con-leche: none — arena infrastructure (task #97-P6-17)
    /// The persistent arm of the capacity test, a value-returning persistent
    /// reader beside `pers_size_of` (task #97-P6-6b's design (A)).
    fn pers_full_of(&self, pers: &PersTier, v: &NNodeView) -> bool {
        if self.shared_on {
            pers.n.full_of(v)
        } else {
            self.pers.full_of(v)
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-6b); Lean twin:
    /// `proof/ConRon/Arena/Store.lean` — the persistent arm of `NStore.internStr`
    ///
    /// One of the five **value-returning persistent readers** task #97-P6-6's
    /// design (A) is written around: the choice between this store's own
    /// persistent tier and the shared `PersTier` is made HERE and a value
    /// comes back, so no borrow ever leaves the choice and no region enters
    /// the record every function of the crate threads as `&mut`.
    fn pers_strs_find(&self, pers: &PersTier, node: &StrNode) -> Option<NIdx> {
        if self.shared_on {
            pers.n.strs.find(node)
        } else {
            self.pers.strs.find(node)
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:466-467 NStore.persCount
    pub fn pers_count(&self, pers: &PersTier) -> usize {
        if self.shared_on {
            pers.n.count()
        } else {
            self.pers.count()
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:466-469 NStore.scrCount
    pub fn scr_count(&self) -> usize {
        self.scr.count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:466-471 NStore.nodeCount
    /// Nodes in both tiers; the fuel bound `denoteN` uses on the Lean side.
    pub fn node_count(&self, pers: &PersTier) -> usize {
        self.pers_count(pers) + self.scr_count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:473-477 NStore.view
    /// Decode a handle: the tier bit selects the array set, and a scratch
    /// handle reads as absent while the scratch tier is off.
    pub fn view(&self, pers: &PersTier, i: &NIdx) -> Option<NNodeView> {
        if i.is_persistent() {
            self.pers_get(pers, i)
        } else if self.scratch_on {
            self.scr.get(i)
        } else {
            None
        }
    }

    /// con-leche: ConLeche/Kernel/Name.lean:34-44 Name
    /// Lean twin: `proof/ConRon/Arena/Store.lean:479-483 NStore.derived` — the
    /// `hashData` computed field, lines 41-44: the derived word of a handle.
    pub fn derived(&self, pers: &PersTier, i: &NIdx) -> u64 {
        if i.is_persistent() {
            self.pers_der_at(pers, i)
        } else if self.scratch_on {
            self.scr.der_at(i)
        } else {
            0
        }
    }

    /// con-leche: ConLeche/Kernel/Name.lean:34-44 Name
    /// Lean twin: `proof/ConRon/Arena/Store.lean:485-492 NStore.derOfView` —
    /// the `hashData` computed field, lines 41-44: the derived word a node
    /// view *would* get, in `O(1)` from the children's.  The three formulas
    /// are `name::anonymous`/`mk_str`/`mk_num`'s, with `hash_data(&pre)`
    /// replaced by `self.derived(pers, p)`.
    pub fn der_of_view(&self, pers: &PersTier, v: &NNodeView) -> u64 {
        match v {
            NNodeView::Anonymous => 1723,
            NNodeView::Str(p, s) => {
                name::mix_hash(name::mix_hash(1, self.derived(pers, p)), name::str_hash(s))
            }
            NNodeView::Num(p, n) => {
                name::mix_hash(name::mix_hash(2, self.derived(pers, p)), name::nat_hash(*n))
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:90-91 NStore.find?
    /// Probe both tiers, persistent first (nanoda's `alloc_name`: "checks the
    /// longer-lived storage first").
    pub fn find(&self, pers: &PersTier, v: &NNodeView) -> Option<NIdx> {
        match self.pers_find(pers, v) {
            Some(i) => Some(i),
            None => {
                if self.scratch_on {
                    self.scr.find(v)
                } else {
                    None
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:501-521 NStore.intern
    /// Hash-cons a name node: probe persistent, then scratch, then append to
    /// the tier the store is in.  Deviation from the Lean, which is total: the
    /// `2^27`-per-constructor-per-tier limit is `capOK`, a *hypothesis* of the
    /// Lean's `intern_spec`, and DESIGN.md §8.3 puts the test here — "the Rust
    /// raises `Native` at the limit, the Lean `throw`s the same kind".
    pub fn intern(&mut self, pers: &PersTier, v: NNodeView) -> Result<NIdx, CheckError> {
        match v {
            NNodeView::Str(p, sv) => {
                let d: u64 = name::mix_hash(
                    name::mix_hash(1, self.derived(pers, &p)),
                    name::str_hash(&sv),
                );
                self.intern_str(pers, StrNode { pre: p, s: sv }, d)
            }
            NNodeView::Anonymous => self.intern_other(pers, NNodeView::Anonymous),
            NNodeView::Num(p, n) => self.intern_other(pers, NNodeView::Num(p, n)),
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-1); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:501-521 NStore.intern`, the `str` arm —
    /// **the probe key built once, by MOVE.**
    ///
    /// The twin's `t.strs.find? ⟨p, s⟩` copies nothing: a Lean `String` is a
    /// value.  `NTables::find` of an `NNodeView::Str` has to build a whole
    /// `StrNode` to hand `ron::HashMap::get` a `&K`, and that means
    /// `expr::str_copy` of the component — a malloc, a copy and a free — on
    /// every probe of every tier.  Task #97-P6-1 counted them on `Init`:
    /// **140 083 646 name interns, 88 854 033 of them of a `str` node**, so
    /// 88.9 M allocations whose only purpose was to be compared and dropped.
    /// The recursors' and basis names' handles are re-pinned in the hot loops
    /// (`pin` is `intern_name`, 73 call sites in `arena::core`), which is
    /// where the count comes from.
    ///
    /// Building the record ONCE from the view the caller already owns costs
    /// nothing at all: `sv` is moved in, not copied, and the same record is
    /// probed against both tiers and then pushed.  Same probes, same order,
    /// same result — `der_of_view`'s `str` line is spelled at the caller for
    /// the same reason, so that `sv` is still in hand when it is needed.
    pub fn intern_str(
        &mut self,
        pers: &PersTier,
        node: StrNode,
        d: u64,
    ) -> Result<NIdx, CheckError>  {
        match self.pers_strs_find(pers, &node) {
            Some(i) => Ok(i),
            None => {
                if self.scratch_on {
                    match self.scr.strs.find(&node) {
                        Some(i) => Ok(i),
                        None => {
                            if self.scr.strs.full() {
                                Err(CheckError::Native(code_points(&M_N_CAP)))
                            } else {
                                let i: NIdx =
                                    NIdx::pack(NTAG_STR, TIER_S, self.scr.strs.size() as u32);
                                self.scr.strs.push(node, d, i.dup2());
                                Ok(i)
                            }
                        }
                    }
                } else if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers.strs.full() {
                    Err(CheckError::Native(code_points(&M_N_CAP)))
                } else {
                    let i: NIdx = NIdx::pack(NTAG_STR, TIER_P, self.pers.strs.size() as u32);
                    self.pers.strs.push(node, d, i.dup2());
                    Ok(i)
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:501-521 NStore.intern` — the two arms
    /// whose record is all scalars, so that building it twice costs nothing
    /// and the twin's spelling is kept verbatim.
    pub fn intern_other(&mut self, pers: &PersTier, v: NNodeView) -> Result<NIdx, CheckError> {
        match self.pers_find(pers, &v) {
            Some(i) => Ok(i),
            None => {
                if self.scratch_on {
                    match self.scr.find(&v) {
                        Some(i) => Ok(i),
                        None => {
                            if self.scr.full_of(&v) {
                                Err(CheckError::Native(code_points(&M_N_CAP)))
                            } else {
                                let d = self.der_of_view(pers, &v);
                                Ok(self.scr.push(v, d, TIER_S))
                            }
                        }
                    }
                } else if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers_full_of(pers, &v) {
                    Err(CheckError::Native(code_points(&M_N_CAP)))
                } else {
                    let d = self.der_of_view(pers, &v);
                    Ok(self.pers.push(v, d, TIER_P))
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:523-526 NStore.enableScratch
    /// Open the scratch tier (DESIGN.md §8.3's per-declaration bracket).
    pub fn enable_scratch(&mut self) {
        self.scr.reset();
        self.scratch_on = true;
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:528-531 NStore.dropScratch
    /// Drop the scratch tier.  Persistent handles keep their bits (DESIGN.md
    /// §8.3, con-leche's lesson 6).
    pub fn drop_scratch(&mut self) {
        self.scr.reset();
        self.scratch_on = false;
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:533-537 NStore.capOK
    /// `intern`'s capacity precondition, as a test rather than a `Prop`: the
    /// constructor's array in the tier being appended to has room for one more
    /// node.
    pub fn cap_ok(&self, pers: &PersTier, v: &NNodeView) -> bool {
        if self.scratch_on {
            !self.scr.full_of(v)
        } else {
            !self.pers_full_of(pers, v)
        }
    }
}

// ---------------------------------------------------------------------------
// The level store's operations (`Store.lean:512-672`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:201-207 LTables
impl LTables {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:73-74 LTables.empty
    pub fn empty() -> LTables {
        LTables {
            zeros: Tbl::empty(),
            succs: Tbl::empty(),
            maxs: Tbl::empty(),
            imaxs: Tbl::empty(),
            params: Tbl::empty(),
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-1); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:73-74 LTables.empty` — the same value as `empty`,
    /// with the cons tables' bucket arrays kept (`Tbl::reset`).
    pub fn reset(&mut self) {
        self.zeros.reset();
        self.succs.reset();
        self.maxs.reset();
        self.imaxs.reset();
        self.params.reset()
    }

    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    /// A copy of this tier, table by table (`Tbl::dup`): the scratch-tier
    /// snapshot of `arena::checker_base::attempt_snapshot` (task #97-T2-LOCKSTEP D4).
    pub fn dup(&self) -> LTables {
        LTables {
            zeros: self.zeros.dup(),
            succs: self.succs.dup(),
            maxs: self.maxs.dup(),
            imaxs: self.imaxs.dup(),
            params: self.params.dup(),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:403-404 LTables.count
    pub fn count(&self) -> usize {
        self.zeros.size()
            + self.succs.size()
            + self.maxs.size()
            + self.imaxs.size()
            + self.params.size()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:406-412 LTables.get
    pub fn get(&self, i: &LIdx) -> Option<LNodeView> {
        if i.tag() == LTAG_ZERO {
            match self.zeros.node(i.idx_nat()) {
                None => None,
                Some(_) => Some(LNodeView::Zero),
            }
        } else if i.tag() == LTAG_SUCC {
            match self.succs.node(i.idx_nat()) {
                None => None,
                Some(r) => Some(LNodeView::Succ(r.u.dup2())),
            }
        } else if i.tag() == LTAG_MAX {
            match self.maxs.node(i.idx_nat()) {
                None => None,
                Some(r) => Some(LNodeView::Max(r.u.dup2(), r.v.dup2())),
            }
        } else if i.tag() == LTAG_IMAX {
            match self.imaxs.node(i.idx_nat()) {
                None => None,
                Some(r) => Some(LNodeView::Imax(r.u.dup2(), r.v.dup2())),
            }
        } else if i.tag() == LTAG_PARAM {
            match self.params.node(i.idx_nat()) {
                None => None,
                Some(r) => Some(LNodeView::Param(r.n.dup2())),
            }
        } else {
            None
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:84-88 LTables.derAt
    pub fn der_at(&self, i: &LIdx) -> LDer {
        if i.tag() == LTAG_ZERO {
            self.zeros.der_at(i.idx_nat())
        } else if i.tag() == LTAG_SUCC {
            self.succs.der_at(i.idx_nat())
        } else if i.tag() == LTAG_MAX {
            self.maxs.der_at(i.idx_nat())
        } else if i.tag() == LTAG_IMAX {
            self.imaxs.der_at(i.idx_nat())
        } else if i.tag() == LTAG_PARAM {
            self.params.der_at(i.idx_nat())
        } else {
            LDer::der_default()
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:90-91 LTables.find?
    pub fn find(&self, v: &LNodeView) -> Option<LIdx> {
        match v {
            LNodeView::Zero => self.zeros.find(&ZeroNode {}),
            LNodeView::Succ(u) => self.succs.find(&SuccNode { u: u.dup2() }),
            LNodeView::Max(u, w) => self.maxs.find(&BinLNode { u: u.dup2(), v: w.dup2() }),
            LNodeView::Imax(u, w) => self.imaxs.find(&BinLNode { u: u.dup2(), v: w.dup2() }),
            LNodeView::Param(n) => self.params.find(&ParamNode { n: n.dup2() }),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:428-434 LTables.sizeOf
    pub fn size_of(&self, v: &LNodeView) -> usize {
        match v {
            LNodeView::Zero => self.zeros.size(),
            LNodeView::Succ(_) => self.succs.size(),
            LNodeView::Max(_, _) => self.maxs.size(),
            LNodeView::Imax(_, _) => self.imaxs.size(),
            LNodeView::Param(_) => self.params.size(),
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-17)
    /// `Tbl::full` at the constructor array `v` would land in — the capacity
    /// test, dispatched exactly as `size_of` is.
    pub fn full_of(&self, v: &LNodeView) -> bool {
        match v {
            LNodeView::Zero => self.zeros.full(),
            LNodeView::Succ(_) => self.succs.full(),
            LNodeView::Max(_, _) => self.maxs.full(),
            LNodeView::Imax(_, _) => self.imaxs.full(),
            LNodeView::Param(_) => self.params.full(),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:93-98 LTables.push
    pub fn push(&mut self, v: LNodeView, d: LDer, tier: u32) -> LIdx {
        match v {
            LNodeView::Zero => {
                let i: LIdx = LIdx::pack(LTAG_ZERO, tier, self.zeros.size() as u32);
                self.zeros.push(ZeroNode {}, d, i.dup2());
                i
            }
            LNodeView::Succ(u) => {
                let i: LIdx = LIdx::pack(LTAG_SUCC, tier, self.succs.size() as u32);
                self.succs.push(SuccNode { u }, d, i.dup2());
                i
            }
            LNodeView::Max(u, w) => {
                let i: LIdx = LIdx::pack(LTAG_MAX, tier, self.maxs.size() as u32);
                self.maxs.push(BinLNode { u, v: w }, d, i.dup2());
                i
            }
            LNodeView::Imax(u, w) => {
                let i: LIdx = LIdx::pack(LTAG_IMAX, tier, self.imaxs.size() as u32);
                self.imaxs.push(BinLNode { u, v: w }, d, i.dup2());
                i
            }
            LNodeView::Param(n) => {
                let i: LIdx = LIdx::pack(LTAG_PARAM, tier, self.params.size() as u32);
                self.params.push(ParamNode { n }, d, i.dup2());
                i
            }
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:209-214 LStore
impl LStore {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:73-74 LStore.empty
    pub fn empty() -> LStore {
        LStore {
            ns: NStore::empty(),
            pers: LTables::empty(),
            scr: LTables::empty(),
            scratch_on: false,
            shared_on: false,
        }
    }


    /// con-leche: none — arena infrastructure (task #97-P6-6b); Lean twin:
    /// `proof/ConRon/Arena/Store.lean` — the persistent arm of `LStore.view`
    ///
    /// One of the five **value-returning persistent readers** task #97-P6-6's
    /// design (A) is written around: the choice between this store's own
    /// persistent tier and the shared `PersTier` is made HERE and a value
    /// comes back, so no borrow ever leaves the choice and no region enters
    /// the record every function of the crate threads as `&mut`.
    fn pers_get(&self, pers: &PersTier, i: &LIdx) -> Option<LNodeView> {
        if self.shared_on {
            pers.l.get(i)
        } else {
            self.pers.get(i)
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-6b); Lean twin:
    /// `proof/ConRon/Arena/Store.lean` — the persistent arm of `LStore.derived`
    ///
    /// One of the five **value-returning persistent readers** task #97-P6-6's
    /// design (A) is written around: the choice between this store's own
    /// persistent tier and the shared `PersTier` is made HERE and a value
    /// comes back, so no borrow ever leaves the choice and no region enters
    /// the record every function of the crate threads as `&mut`.
    fn pers_der_at(&self, pers: &PersTier, i: &LIdx) -> LDer {
        if self.shared_on {
            pers.l.der_at(i)
        } else {
            self.pers.der_at(i)
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-6b); Lean twin:
    /// `proof/ConRon/Arena/Store.lean` — the persistent arm of `LStore.find?`
    ///
    /// One of the five **value-returning persistent readers** task #97-P6-6's
    /// design (A) is written around: the choice between this store's own
    /// persistent tier and the shared `PersTier` is made HERE and a value
    /// comes back, so no borrow ever leaves the choice and no region enters
    /// the record every function of the crate threads as `&mut`.
    fn pers_find(&self, pers: &PersTier, v: &LNodeView) -> Option<LIdx> {
        if self.shared_on {
            pers.l.find(v)
        } else {
            self.pers.find(v)
        }
    }


    /// con-leche: none — arena infrastructure (task #97-P6-17)
    /// The persistent arm of the capacity test, a value-returning persistent
    /// reader beside `pers_size_of` (task #97-P6-6b's design (A)).
    fn pers_full_of(&self, pers: &PersTier, v: &LNodeView) -> bool {
        if self.shared_on {
            pers.l.full_of(v)
        } else {
            self.pers.full_of(v)
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:466-467 LStore.persCount
    pub fn pers_count(&self, pers: &PersTier) -> usize {
        if self.shared_on {
            pers.l.count()
        } else {
            self.pers.count()
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:466-469 LStore.scrCount
    pub fn scr_count(&self) -> usize {
        self.scr.count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:466-471 LStore.nodeCount
    pub fn node_count(&self, pers: &PersTier) -> usize {
        self.pers_count(pers) + self.scr_count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:473-477 LStore.view
    pub fn view(&self, pers: &PersTier, i: &LIdx) -> Option<LNodeView> {
        if i.is_persistent() {
            self.pers_get(pers, i)
        } else if self.scratch_on {
            self.scr.get(i)
        } else {
            None
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:41-54 Level
    /// Lean twin: `proof/ConRon/Arena/Store.lean:479-483 LStore.derived` — the
    /// `hashData` computed field, lines 47-53, and `Kernel/Expr.lean:114-122
    /// levelHasParam`.
    pub fn derived(&self, pers: &PersTier, i: &LIdx) -> LDer {
        if i.is_persistent() {
            self.pers_der_at(pers, i)
        } else if self.scratch_on {
            self.scr.der_at(i)
        } else {
            LDer::der_default()
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:41-54 Level
    /// Lean twin: `proof/ConRon/Arena/Store.lean:485-492 LStore.derOfView` —
    /// the derived record a node view would get, in `O(1)` from the
    /// children's.  con-leche recomputes the parameter flag by an `O(|u|)`
    /// walk at every construction (`Kernel/Expr.lean:114-127`); the interned
    /// store reads it off the column.
    pub fn der_of_view(&self, pers: &PersTier, v: &LNodeView) -> LDer {
        match v {
            LNodeView::Zero => LDer { hash: 1, has_param: false },
            LNodeView::Succ(u) => {
                let du = self.derived(pers, u);
                LDer { hash: name::mix_hash(3, du.hash), has_param: du.has_param }
            }
            LNodeView::Max(u, w) => {
                let du = self.derived(pers, u);
                let dw = self.derived(pers, w);
                LDer {
                    hash: name::mix_hash(5, name::mix_hash(du.hash, dw.hash)),
                    has_param: du.has_param || dw.has_param,
                }
            }
            LNodeView::Imax(u, w) => {
                let du = self.derived(pers, u);
                let dw = self.derived(pers, w);
                LDer {
                    hash: name::mix_hash(7, name::mix_hash(du.hash, dw.hash)),
                    has_param: du.has_param || dw.has_param,
                }
            }
            LNodeView::Param(n) => {
                LDer { hash: name::mix_hash(11, self.ns.derived(pers, n)), has_param: true }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:90-91 LStore.find?
    pub fn find(&self, pers: &PersTier, v: &LNodeView) -> Option<LIdx> {
        match self.pers_find(pers, v) {
            Some(i) => Some(i),
            None => {
                if self.scratch_on {
                    self.scr.find(v)
                } else {
                    None
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:501-521 LStore.intern
    pub fn intern(&mut self, pers: &PersTier, v: LNodeView) -> Result<LIdx, CheckError> {
        match self.pers_find(pers, &v) {
            Some(i) => Ok(i),
            None => {
                if self.scratch_on {
                    match self.scr.find(&v) {
                        Some(i) => Ok(i),
                        None => {
                            if self.scr.full_of(&v) {
                                Err(CheckError::Native(code_points(&M_L_CAP)))
                            } else {
                                let d = self.der_of_view(pers, &v);
                                Ok(self.scr.push(v, d, TIER_S))
                            }
                        }
                    }
                } else if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers_full_of(pers, &v) {
                    Err(CheckError::Native(code_points(&M_L_CAP)))
                } else {
                    let d = self.der_of_view(pers, &v);
                    Ok(self.pers.push(v, d, TIER_P))
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:523-526 LStore.enableScratch
    /// Open the scratch tier, here and in the name store.
    pub fn enable_scratch(&mut self) {
        self.ns.enable_scratch();
        self.scr.reset();
        self.scratch_on = true;
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:528-531 LStore.dropScratch
    /// Drop the scratch tier, here and in the name store.
    pub fn drop_scratch(&mut self) {
        self.ns.drop_scratch();
        self.scr.reset();
        self.scratch_on = false;
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:533-537 LStore.capOK
    pub fn cap_ok(&self, pers: &PersTier, v: &LNodeView) -> bool {
        if self.scratch_on {
            !self.scr.full_of(v)
        } else {
            !self.pers_full_of(pers, v)
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1790-1795 LStore.internName
    /// Intern a name from the level store.  The Lean detaches the nested store
    /// before handing it down (lesson 14); `&mut` is that, so the Rust is the
    /// delegation the detaching exists to make safe.
    pub fn intern_name(&mut self, pers: &PersTier, v: NNodeView) -> Result<NIdx, CheckError> {
        self.ns.intern(pers, v)
    }
}

// ---------------------------------------------------------------------------
// The level-list store's operations (`Store.lean:674-788`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:236-239 LsTables
impl LsTables {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:73-74 LsTables.empty
    pub fn empty() -> LsTables {
        LsTables { lists: Tbl::empty() }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-1); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:73-74 LsTables.empty` — the same value as `empty`,
    /// with the cons tables' bucket arrays kept (`Tbl::reset`).
    pub fn reset(&mut self) {

        self.lists.reset()
    }

    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    /// A copy of this tier, table by table (`Tbl::dup`): the scratch-tier
    /// snapshot of `arena::checker_base::attempt_snapshot` (task #97-T2-LOCKSTEP D4).
    pub fn dup(&self) -> LsTables {
        LsTables {
            lists: self.lists.dup(),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:403-404 LsTables.count
    pub fn count(&self) -> usize {
        self.lists.size()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:406-412 LsTables.get
    pub fn get(&self, i: &LsIdx) -> Option<LsNodeView> {
        if i.tag() == LSTAG_LIST {
            match self.lists.node(i.idx_nat()) {
                None => None,
                Some(r) => Some(lidx_vec_dup(&r.us)),
            }
        } else {
            None
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:724-729 LsTables.getLen` —
    /// `LsTables.getLen`, the LENGTH projection of `LsTables.get`. `get` copies
    /// the whole `Vec<LIdx>` out of the node (Lean shares the list where the
    /// Rust must copy it, DESIGN.md §3.2); most callers only compare the length
    /// with a declaration's level-parameter count, and that is one `Vec::len`
    /// off the record.
    #[inline(always)]
    pub fn get_len(&self, i: &LsIdx) -> Option<usize> {
        if i.tag() == LSTAG_LIST {
            match self.lists.node(i.idx_nat()) {
                None => None,
                Some(r) => Some(r.us.len()),
            }
        } else {
            None
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:84-88 LsTables.derAt
    pub fn der_at(&self, i: &LsIdx) -> LDer {
        if i.tag() == LSTAG_LIST {
            self.lists.der_at(i.idx_nat())
        } else {
            LDer::der_default()
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:90-91 LsTables.find?
    pub fn find(&self, v: &LsNodeView) -> Option<LsIdx> {
        self.lists.find(&ListNode { us: lidx_vec_dup(v) })
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:428-434 LsTables.sizeOf
    pub fn size_of(&self, _v: &LsNodeView) -> usize {
        self.lists.size()
    }

    /// con-leche: none — arena infrastructure (task #97-P6-17)
    /// `Tbl::full` at the constructor array `v` would land in — the capacity
    /// test, dispatched exactly as `size_of` is.
    pub fn full_of(&self, _v: &LsNodeView) -> bool {
        self.lists.full()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:93-98 LsTables.push
    pub fn push(&mut self, v: LsNodeView, d: LDer, tier: u32) -> LsIdx {
        let i: LsIdx = LsIdx::pack(LSTAG_LIST, tier, self.lists.size() as u32);
        self.lists.push(ListNode { us: v }, d, i.dup2());
        i
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:241-246 LsStore
impl LsStore {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:73-74 LsStore.empty
    pub fn empty() -> LsStore {
        LsStore {
            ls: LStore::empty(),
            pers: LsTables::empty(),
            scr: LsTables::empty(),
            scratch_on: false,
            shared_on: false,
        }
    }


    /// con-leche: none — arena infrastructure (task #97-P6-6b); Lean twin:
    /// `proof/ConRon/Arena/Store.lean` — the persistent arm of `LsStore.view`
    ///
    /// One of the five **value-returning persistent readers** task #97-P6-6's
    /// design (A) is written around: the choice between this store's own
    /// persistent tier and the shared `PersTier` is made HERE and a value
    /// comes back, so no borrow ever leaves the choice and no region enters
    /// the record every function of the crate threads as `&mut`.
    fn pers_get(&self, pers: &PersTier, i: &LsIdx) -> Option<LsNodeView> {
        if self.shared_on {
            pers.ls.get(i)
        } else {
            self.pers.get(i)
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-6b); Lean twin:
    /// `proof/ConRon/Arena/Store.lean` — the persistent arm of `LsStore.derived`
    ///
    /// One of the five **value-returning persistent readers** task #97-P6-6's
    /// design (A) is written around: the choice between this store's own
    /// persistent tier and the shared `PersTier` is made HERE and a value
    /// comes back, so no borrow ever leaves the choice and no region enters
    /// the record every function of the crate threads as `&mut`.
    fn pers_der_at(&self, pers: &PersTier, i: &LsIdx) -> LDer {
        if self.shared_on {
            pers.ls.der_at(i)
        } else {
            self.pers.der_at(i)
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-6b); Lean twin:
    /// `proof/ConRon/Arena/Store.lean` — the persistent arm of `LsStore.find?`
    ///
    /// One of the five **value-returning persistent readers** task #97-P6-6's
    /// design (A) is written around: the choice between this store's own
    /// persistent tier and the shared `PersTier` is made HERE and a value
    /// comes back, so no borrow ever leaves the choice and no region enters
    /// the record every function of the crate threads as `&mut`.
    fn pers_find(&self, pers: &PersTier, v: &LsNodeView) -> Option<LsIdx> {
        if self.shared_on {
            pers.ls.find(v)
        } else {
            self.pers.find(v)
        }
    }


    /// con-leche: none — arena infrastructure (task #97-P6-17)
    /// The persistent arm of the capacity test, a value-returning persistent
    /// reader beside `pers_size_of` (task #97-P6-6b's design (A)).
    fn pers_full_of(&self, pers: &PersTier, v: &LsNodeView) -> bool {
        if self.shared_on {
            pers.ls.full_of(v)
        } else {
            self.pers.full_of(v)
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:466-467 LsStore.persCount
    pub fn pers_count(&self, pers: &PersTier) -> usize {
        if self.shared_on {
            pers.ls.count()
        } else {
            self.pers.count()
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:466-469 LsStore.scrCount
    pub fn scr_count(&self) -> usize {
        self.scr.count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:466-471 LsStore.nodeCount
    pub fn node_count(&self, pers: &PersTier) -> usize {
        self.pers_count(pers) + self.scr_count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:761-762 LsStore.ns
    /// The name store underneath.
    pub fn ns(&self) -> &NStore {
        &self.ls.ns
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:473-477 LsStore.view
    pub fn view(&self, pers: &PersTier, i: &LsIdx) -> Option<LsNodeView> {
        if i.is_persistent() {
            self.pers_get(pers, i)
        } else if self.scratch_on {
            self.scr.get(i)
        } else {
            None
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-10); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:785-786 LsStore.persGetLen`
    fn pers_get_len(&self, pers: &PersTier, i: &LsIdx) -> Option<usize> {
        if self.shared_on {
            pers.ls.get_len(i)
        } else {
            self.pers.get_len(i)
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:788-793 LsStore.viewLen` —
    /// `LsStore.viewLen`, the length projection of `LsStore.view`: `viewLen h =
    /// (view h).map List.length`, which is the exactness lemma the bridge owes.
    #[inline(always)]
    pub fn view_len(&self, pers: &PersTier, i: &LsIdx) -> Option<usize> {
        if i.is_persistent() {
            self.pers_get_len(pers, i)
        } else if self.scratch_on {
            self.scr.get_len(i)
        } else {
            None
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:137-140 levelsHash
    /// Lean twin: `proof/ConRon/Arena/Store.lean:479-483 LsStore.derived` —
    /// the derived record of a level-list handle.
    pub fn derived(&self, pers: &PersTier, i: &LsIdx) -> LDer {
        if i.is_persistent() {
            self.pers_der_at(pers, i)
        } else if self.scratch_on {
            self.scr.der_at(i)
        } else {
            LDer::der_default()
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:137-140 levelsHash
    /// Lean twin: `proof/ConRon/Arena/Store.lean:485-492 LsStore.derOfView` —
    /// and `Kernel/Expr.lean:125-127 levelsHaveParam`: the derived record a
    /// level list would get.  `O(n)` in the list, as con-leche's own fold is.
    pub fn der_of_view(&self, pers: &PersTier, v: &LsNodeView) -> LDer {
        self.der_of_view_from(pers, v, 0)
    }

    /// con-leche: none — the index recursion behind `der_of_view`
    /// The Lean recurses on the list's tail; Rust carries the cursor, which
    /// is `-loops-to-rec`'s own shape (DESIGN.md §3.4: no loops).
    pub fn der_of_view_from(&self, pers: &PersTier, v: &LsNodeView, i: usize) -> LDer {
        if i >= v.len() {
            LDer { hash: 13, has_param: false }
        } else {
            let hu = self.ls.derived(pers, &v[i]);
            let hr = self.der_of_view_from(pers, v, i + 1);
            LDer {
                hash: name::mix_hash(hu.hash, hr.hash),
                has_param: hu.has_param || hr.has_param,
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:90-91 LsStore.find?
    pub fn find(&self, pers: &PersTier, v: &LsNodeView) -> Option<LsIdx> {
        match self.pers_find(pers, v) {
            Some(i) => Some(i),
            None => {
                if self.scratch_on {
                    self.scr.find(v)
                } else {
                    None
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:501-521 LsStore.intern
    pub fn intern(&mut self, pers: &PersTier, v: LsNodeView) -> Result<LsIdx, CheckError> {
        match self.pers_find(pers, &v) {
            Some(i) => Ok(i),
            None => {
                if self.scratch_on {
                    match self.scr.find(&v) {
                        Some(i) => Ok(i),
                        None => {
                            if self.scr.full_of(&v) {
                                Err(CheckError::Native(code_points(&M_LS_CAP)))
                            } else {
                                let d = self.der_of_view(pers, &v);
                                Ok(self.scr.push(v, d, TIER_S))
                            }
                        }
                    }
                } else if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers_full_of(pers, &v) {
                    Err(CheckError::Native(code_points(&M_LS_CAP)))
                } else {
                    let d = self.der_of_view(pers, &v);
                    Ok(self.pers.push(v, d, TIER_P))
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:523-526 LsStore.enableScratch
    pub fn enable_scratch(&mut self) {
        self.ls.enable_scratch();
        self.scr.reset();
        self.scratch_on = true;
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:528-531 LsStore.dropScratch
    pub fn drop_scratch(&mut self) {
        self.ls.drop_scratch();
        self.scr.reset();
        self.scratch_on = false;
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:533-537 LsStore.capOK
    pub fn cap_ok(&self, pers: &PersTier, v: &LsNodeView) -> bool {
        if self.scratch_on {
            !self.scr.full_of(v)
        } else {
            !self.pers_full_of(pers, v)
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1797-1803 LsStore.internName
    pub fn intern_name(&mut self, pers: &PersTier, v: NNodeView) -> Result<NIdx, CheckError> {
        self.ls.intern_name(pers, v)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1805-1811 LsStore.internLevel
    pub fn intern_level(&mut self, pers: &PersTier, v: LNodeView) -> Result<LIdx, CheckError> {
        self.ls.intern(pers, v)
    }
}

// ---------------------------------------------------------------------------
// The expression store's operations (`Store.lean:790-1070`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:363-382 ETables
impl ETables {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:73-74 ETables.empty
    pub fn empty() -> ETables {
        ETables {
            bvars: Tbl::empty(),
            fvars: Tbl::empty(),
            sorts: Tbl::empty(),
            consts: Tbl::empty(),
            apps: Tbl::empty(),
            lams: Tbl::empty(),
            foralls: Tbl::empty(),
            lets: Tbl::empty(),
            lits: Tbl::empty(),
            projs: Tbl::empty(),
            bms: Tbl::empty(),
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-1); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:73-74 ETables.empty` — the same value as `empty`,
    /// with the cons tables' bucket arrays kept (`Tbl::reset`).
    pub fn reset(&mut self) {
        self.bvars.reset();
        self.fvars.reset();
        self.sorts.reset();
        self.consts.reset();
        self.apps.reset();
        self.lams.reset();
        self.foralls.reset();
        self.lets.reset();
        self.lits.reset();
        self.projs.reset();
        self.bms.reset()
    }

    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    /// A copy of this tier, table by table (`Tbl::dup`): the scratch-tier
    /// snapshot of `arena::checker_base::attempt_snapshot` (task #97-T2-LOCKSTEP D4).
    pub fn dup(&self) -> ETables {
        ETables {
            bvars: self.bvars.dup(),
            fvars: self.fvars.dup(),
            sorts: self.sorts.dup(),
            consts: self.consts.dup(),
            apps: self.apps.dup(),
            lams: self.lams.dup(),
            foralls: self.foralls.dup(),
            lets: self.lets.dup(),
            lits: self.lits.dup(),
            projs: self.projs.dup(),
            bms: self.bms.dup(),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:403-404 ETables.count
    /// Nodes in this tier, over all ten constructors.
    pub fn count(&self) -> usize {
        self.bvars.size()
            + self.fvars.size()
            + self.sorts.size()
            + self.consts.size()
            + self.apps.size()
            + self.lams.size()
            + self.foralls.size()
            + self.lets.size()
            + self.lits.size()
            + self.projs.size()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:406-412 ETables.get
    /// Decode one handle against this tier's arrays: read the tag, index one
    /// array, build the view.  There is no node enum in the store (DESIGN.md
    /// §8.3).
    #[inline(always)]
    pub fn get(&self, i: &EIdx) -> Option<ENodeView> {
        if i.tag() == ETAG_BVAR {
            match self.bvars.node(i.idx_nat()) {
                None => None,
                Some(r) => Some(ENodeView::BVar(r.i)),
            }
        } else if i.tag() == ETAG_FVAR {
            match self.fvars.node(i.idx_nat()) {
                None => None,
                Some(r) => Some(ENodeView::FVar(r.idx, r.ty.dup2())),
            }
        } else if i.tag() == ETAG_SORT {
            match self.sorts.node(i.idx_nat()) {
                None => None,
                Some(r) => Some(ENodeView::Sort(r.u.dup2())),
            }
        } else if i.tag() == ETAG_CONST {
            match self.consts.node(i.idx_nat()) {
                None => None,
                Some(r) => Some(ENodeView::Const(r.n.dup2(), r.us.dup2())),
            }
        } else if i.tag() == ETAG_APP {
            match self.apps.node(i.idx_nat()) {
                None => None,
                Some(r) => Some(ENodeView::App(r.f.dup2(), r.a.dup2())),
            }
        } else if e_tag_is_bind(i.tag()) {
            None
        } else if i.tag() == ETAG_LET_E {
            match self.lets.node(i.idx_nat()) {
                None => None,
                Some(r) => Some(ENodeView::LetE(r.ty.dup2(), r.val.dup2(), r.body.dup2())),
            }
        } else if i.tag() == ETAG_LIT {
            match self.lits.node(i.idx_nat()) {
                None => None,
                Some(r) => Some(ENodeView::Lit(expr::literal_dup(&r.l))),
            }
        } else if i.tag() == ETAG_PROJ {
            match self.projs.node(i.idx_nat()) {
                None => None,
                Some(r) => Some(ENodeView::Proj(r.n.dup2(), r.i, r.e.dup2())),
            }
        } else {
            None
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:886-888 ETables.getApp` —
    /// `ETables.getApp`, the `app` PROJECTION of `ETables.get`.
    ///
    /// `get` decodes a handle of any tag into a 32-byte `ENodeView`; this
    /// reads the two fields of an `app` node and nothing else.  A caller that
    /// has already decided the tag (off the handle word, which carries it —
    /// DESIGN.md §8.3) wants only this, and it saves the callee's ten-way tag
    /// jump table, the sret view, the second dispatch on the same tag and the
    /// view's drop.  `None` is the same "out of range" this tier's `get`
    /// reports, i.e. a dangling handle.
    #[inline(always)]
    pub fn get_app(&self, i: &EIdx) -> Option<(EIdx, EIdx)> {
        match self.apps.node(i.idx_nat()) {
            None => None,
            Some(r) => Some((r.f.dup2(), r.a.dup2())),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:890-892 ETables.getSort` —
    /// `ETables.getSort`, the `sort` projection of `ETables.get`. The sibling
    /// of `getApp` at the one-field constructor: a caller that has read
    /// `ETag.sort` off the handle word wants the level handle and nothing else.
    #[inline(always)]
    pub fn get_sort(&self, i: &EIdx) -> Option<LIdx> {
        match self.sorts.node(i.idx_nat()) {
            None => None,
            Some(r) => Some(r.u.dup2()),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:894-896 ETables.getConst` —
    /// `ETables.getConst`, the `const` projection of `ETables.get`.
    #[inline(always)]
    pub fn get_const(&self, i: &EIdx) -> Option<(NIdx, LsIdx)> {
        match self.consts.node(i.idx_nat()) {
            None => None,
            Some(r) => Some((r.n.dup2(), r.us.dup2())),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:898-901 ETables.getConstName` —
    /// `ETables.getConstName`, the NAME of a `const` node. The level arguments
    /// beside it are not read: most of the crate's `const` tests compare the
    /// head name alone, and the `LsIdx` copy is work for nothing there. The
    /// sibling of `getFVarIdx`.
    #[inline(always)]
    pub fn get_const_name(&self, i: &EIdx) -> Option<NIdx> {
        match self.consts.node(i.idx_nat()) {
            None => None,
            Some(r) => Some(r.n.dup2()),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:903-905 ETables.getBVar` —
    /// `ETables.getBVar`, the `bvar` projection of `ETables.get`.
    #[inline(always)]
    pub fn get_bvar(&self, i: &EIdx) -> Option<u64> {
        match self.bvars.node(i.idx_nat()) {
            None => None,
            Some(r) => Some(r.i),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:907-909 ETables.getFVarIdx` —
    /// `ETables.getFVarIdx`, the de Bruijn LEVEL of an `fvar` node. The binder
    /// type beside it is not read: `abstract1Go`'s `fvar` arm does not descend
    /// into the annotation, so it wants the index alone and copying the type
    /// handle out would be work for nothing.
    #[inline(always)]
    pub fn get_fvar_idx(&self, i: &EIdx) -> Option<u64> {
        match self.fvars.node(i.idx_nat()) {
            None => None,
            Some(r) => Some(r.idx),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:911-913 ETables.getFVarTy` —
    /// `ETables.getFVarTy`, the binder TYPE of an `fvar` node, the other half
    /// of `getFVarIdx`. `fvarTypeD` wants the annotation and not the de Bruijn
    /// level.
    #[inline(always)]
    pub fn get_fvar_ty(&self, i: &EIdx) -> Option<EIdx> {
        match self.fvars.node(i.idx_nat()) {
            None => None,
            Some(r) => Some(r.ty.dup2()),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:915-917 ETables.getLit` —
    /// `ETables.getLit`, the `lit` projection of `ETables.get`. The one
    /// projection whose payload is not a handle: `Literal` is the datum
    /// `ENodeView::Lit` carries, and `literal_dup` is the copy the view makes
    /// anyway.
    #[inline(always)]
    pub fn get_lit(&self, i: &EIdx) -> Option<Literal> {
        match self.lits.node(i.idx_nat()) {
            None => None,
            Some(r) => Some(expr::literal_dup(&r.l)),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:919-926 ETables.getBind` —
    /// `ETables.getBind`, the `lam`/`forallE` projection of `ETables.get`. The
    /// tag picks the array, as it does in `get`; the two binder constructors
    /// have the same record shape.
    #[inline(always)]
    pub fn get_bind(&self, i: &EIdx) -> Option<(EIdx, EIdx, BMIdx)> {
        if i.tag() == ETAG_LAM {
            match self.lams.node(i.idx_nat()) {
                None => None,
                Some(r) => Some((r.ty.dup2(), r.body.dup2(), r.m.dup2())),
            }
        } else {
            match self.foralls.node(i.idx_nat()) {
                None => None,
                Some(r) => Some((r.ty.dup2(), r.body.dup2(), r.m.dup2())),
            }
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Store.lean:936-939 ETables.getBM` — read
    /// one binder datum out of this tier's store.
    #[inline(always)]
    pub fn get_bm(&self, i: &BMIdx) -> Option<BinderMeta> {
        match self.bms.node(i.idx_nat()) {
            None => None,
            Some(r) => Some(expr::binder_meta(prop_when::dup(&r.pw))),
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Store.lean:949-952 ETables.findBM` — the
    /// binder datum's cons probe in THIS tier. The record is built here, inside
    /// a leaf with no branch, as `ETables::find` builds its own.
    pub fn find_bm(&self, m: &BinderMeta) -> Option<BMIdx> {
        self.bms.find(&BMNode { pw: prop_when::dup(&m.pw) })
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Store.lean:941-947 ETables.getBMDer` —
    /// the binder datum's two DERIVED scalars, `PropWhen.hash` (the column) and
    /// `PropWhen.hasParams` (a tag test on the record), which is all
    /// `derOfBind` wants of it.
    #[inline(always)]
    pub fn get_bm_der(&self, i: &BMIdx) -> (u64, bool) {
        match self.bms.node(i.idx_nat()) {
            None => (0, false),
            Some(r) => (self.bms.der_at(i.idx_nat()), prop_when::has_params(&r.pw)),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:928-930 ETables.getLet` —
    /// `ETables.getLet`, the `letE` projection of `ETables.get`.
    #[inline(always)]
    pub fn get_let(&self, i: &EIdx) -> Option<(EIdx, EIdx, EIdx)> {
        match self.lets.node(i.idx_nat()) {
            None => None,
            Some(r) => Some((r.ty.dup2(), r.val.dup2(), r.body.dup2())),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:932-934 ETables.getProj` —
    /// `ETables.getProj`, the `proj` projection of `ETables.get`.
    #[inline(always)]
    pub fn get_proj(&self, i: &EIdx) -> Option<(NIdx, u64, EIdx)> {
        match self.projs.node(i.idx_nat()) {
            None => None,
            Some(r) => Some((r.n.dup2(), r.i, r.e.dup2())),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:84-88 ETables.derAt
    #[inline(always)]
    pub fn der_at(&self, i: &EIdx) -> u64 {
        if i.tag() == ETAG_BVAR {
            self.bvars.der_at(i.idx_nat())
        } else if i.tag() == ETAG_FVAR {
            self.fvars.der_at(i.idx_nat())
        } else if i.tag() == ETAG_SORT {
            self.sorts.der_at(i.idx_nat())
        } else if i.tag() == ETAG_CONST {
            self.consts.der_at(i.idx_nat())
        } else if i.tag() == ETAG_APP {
            self.apps.der_at(i.idx_nat())
        } else if i.tag() == ETAG_LAM {
            self.lams.der_at(i.idx_nat())
        } else if i.tag() == ETAG_FORALL_E {
            self.foralls.der_at(i.idx_nat())
        } else if i.tag() == ETAG_LET_E {
            self.lets.der_at(i.idx_nat())
        } else if i.tag() == ETAG_LIT {
            self.lits.der_at(i.idx_nat())
        } else if i.tag() == ETAG_PROJ {
            self.projs.der_at(i.idx_nat())
        } else {
            0
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:90-91 ETables.find?
    ///
    /// **`#[inline(always)]`** (task #97-P6-13): `EStore::intern` calls this
    /// twice with the SAME view, once per tier, and out of line each call
    /// re-dispatched on the view's tag, rebuilt the node record and re-hashed
    /// it.  Inlined, the two probes share all three.  −1.62 % of `Init` on
    /// its own; plain `#[inline]` is declined by LLVM on a ten-arm jump table
    /// and is worth nothing (measured).  `ETables::push` given the same
    /// attribute is +3.8 % cycles and is not taken.
    #[inline(always)]
    pub fn find(&self, v: &ENodeView, mi: &BMIdx) -> Option<EIdx> {
        match v {
            ENodeView::BVar(i) => self.bvars.find(&BVarNode { i: *i }),
            ENodeView::FVar(idx, ty) => {
                self.fvars.find(&FVarNode { idx: *idx, ty: ty.dup2() })
            }
            ENodeView::Sort(u) => self.sorts.find(&SortNode { u: u.dup2() }),
            ENodeView::Const(n, us) => {
                self.consts.find(&ConstNode { n: n.dup2(), us: us.dup2() })
            }
            ENodeView::App(f, a) => self.apps.find(&AppNode { f: f.dup2(), a: a.dup2() }),
            ENodeView::Lam(ty, b, _) => self.lams.find(&BindNode {
                ty: ty.dup2(),
                body: b.dup2(),
                m: mi.dup2(),
            }),
            ENodeView::ForallE(ty, b, _) => self.foralls.find(&BindNode {
                ty: ty.dup2(),
                body: b.dup2(),
                m: mi.dup2(),
            }),
            ENodeView::LetE(ty, val, b) => self.lets.find(&LetNode {
                ty: ty.dup2(),
                val: val.dup2(),
                body: b.dup2(),
            }),
            ENodeView::Lit(l) => self.lits.find(&LitNode { l: expr::literal_dup(l) }),
            ENodeView::Proj(n, i, e) => {
                self.projs.find(&ProjNode { n: n.dup2(), i: *i, e: e.dup2() })
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:428-434 ETables.sizeOf
    pub fn size_of(&self, v: &ENodeView) -> usize {
        match v {
            ENodeView::BVar(_) => self.bvars.size(),
            ENodeView::FVar(_, _) => self.fvars.size(),
            ENodeView::Sort(_) => self.sorts.size(),
            ENodeView::Const(_, _) => self.consts.size(),
            ENodeView::App(_, _) => self.apps.size(),
            ENodeView::Lam(_, _, _) => self.lams.size(),
            ENodeView::ForallE(_, _, _) => self.foralls.size(),
            ENodeView::LetE(_, _, _) => self.lets.size(),
            ENodeView::Lit(_) => self.lits.size(),
            ENodeView::Proj(_, _, _) => self.projs.size(),
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-17)
    /// `Tbl::full` at the constructor array `v` would land in — the capacity
    /// test, dispatched exactly as `size_of` is.
    pub fn full_of(&self, v: &ENodeView) -> bool {
        match v {
            ENodeView::BVar(_) => self.bvars.full(),
            ENodeView::FVar(_, _) => self.fvars.full(),
            ENodeView::Sort(_) => self.sorts.full(),
            ENodeView::Const(_, _) => self.consts.full(),
            ENodeView::App(_, _) => self.apps.full(),
            ENodeView::Lam(_, _, _) => self.lams.full(),
            ENodeView::ForallE(_, _, _) => self.foralls.full(),
            ENodeView::LetE(_, _, _) => self.lets.full(),
            ENodeView::Lit(_) => self.lits.full(),
            ENodeView::Proj(_, _, _) => self.projs.full(),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:93-98 ETables.push
    pub fn push(&mut self, v: ENodeView, d: u64, mi: BMIdx, tier: u32) -> EIdx {
        match v {
            ENodeView::BVar(i) => {
                let h: EIdx = EIdx::pack(ETAG_BVAR, tier, self.bvars.size() as u32);
                self.bvars.push(BVarNode { i }, d, h.dup2());
                h
            }
            ENodeView::FVar(idx, ty) => {
                let h: EIdx = EIdx::pack(ETAG_FVAR, tier, self.fvars.size() as u32);
                self.fvars.push(FVarNode { idx, ty }, d, h.dup2());
                h
            }
            ENodeView::Sort(u) => {
                let h: EIdx = EIdx::pack(ETAG_SORT, tier, self.sorts.size() as u32);
                self.sorts.push(SortNode { u }, d, h.dup2());
                h
            }
            ENodeView::Const(n, us) => {
                let h: EIdx = EIdx::pack(ETAG_CONST, tier, self.consts.size() as u32);
                self.consts.push(ConstNode { n, us }, d, h.dup2());
                h
            }
            ENodeView::App(f, a) => {
                let h: EIdx = EIdx::pack(ETAG_APP, tier, self.apps.size() as u32);
                self.apps.push(AppNode { f, a }, d, h.dup2());
                h
            }
            ENodeView::Lam(ty, b, _) => {
                let h: EIdx = EIdx::pack(ETAG_LAM, tier, self.lams.size() as u32);
                self.lams.push(BindNode { ty, body: b, m: mi }, d, h.dup2());
                h
            }
            ENodeView::ForallE(ty, b, _) => {
                let h: EIdx = EIdx::pack(ETAG_FORALL_E, tier, self.foralls.size() as u32);
                self.foralls.push(BindNode { ty, body: b, m: mi }, d, h.dup2());
                h
            }
            ENodeView::LetE(ty, val, b) => {
                let h: EIdx = EIdx::pack(ETAG_LET_E, tier, self.lets.size() as u32);
                self.lets.push(LetNode { ty, val, body: b }, d, h.dup2());
                h
            }
            ENodeView::Lit(l) => {
                let h: EIdx = EIdx::pack(ETAG_LIT, tier, self.lits.size() as u32);
                self.lits.push(LitNode { l }, d, h.dup2());
                h
            }
            ENodeView::Proj(n, i, e) => {
                let h: EIdx = EIdx::pack(ETAG_PROJ, tier, self.projs.size() as u32);
                self.projs.push(ProjNode { n, i, e }, d, h.dup2());
                h
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:485-492 EStore.derOfView` — the
/// `lam` (hash tag 19) and `forallE` (23) arms, which differ in nothing but
/// the tag.  It is `con_ron_core::kernel::expr::lam`'s body with `data(&ty)`
/// and `data(&body)` replaced by the derived column, and `m`'s two reads
/// passed in as scalars.
///
/// **Why it is a function and not the arm itself.**  The twin writes both
/// arms out inline.  Inlined here, the three-way `lpOfData ty || lpOfData b
/// || m.pw.hasParams` sits inside a `match` arm that still holds borrows into
/// the `&ENodeView`, and Aeneas cannot join the short-circuit branches under
/// those loans: *"Could not match the contexts"* (`interp/Interp.ml:617`),
/// measured at P4a.  Neither hoisting the `has_params` read to its own `let`
/// nor binding the whole disjunction to one moves it.  The two-way
/// disjunction of the `app` arm is fine, and
/// `con_ron_core::kernel::expr::lam` — the same three-way disjunction, with
/// `m` owned and no enclosing match — extracts today.  Lifting the arm's
/// arithmetic into a function of five scalars is what makes the loans dead at
/// the join, and it costs the transliteration nothing: `der_of_bind 19` and
/// `der_of_bind 23` are the twin's two arms verbatim.
pub fn der_of_bind(tag: u64, dt: u64, db: u64, hm: u64, pm: bool) -> u64 {
    let h: u64 = expr::hash32(name::mix_hash(
        tag,
        name::mix_hash(
            expr::hash_of_data(dt),
            name::mix_hash(expr::hash_of_data(db), hm),
        ),
    ));
    expr::pack_data(
        h,
        expr::max_u64(expr::bvar_of_data(dt), expr::sat_pred(expr::bvar_of_data(db))),
        expr::max_u64(expr::fvar_of_data(dt), expr::fvar_of_data(db)),
        expr::lp_of_data(dt) || expr::lp_of_data(db) || pm,
    )
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:485-492 EStore.derOfView` — the
/// `letE` arm, `con_ron_core::kernel::expr::let_e`'s body over the derived
/// column.  A function for the reason `der_of_bind` is one: its
/// level-parameter bit is a three-way disjunction too.
pub fn der_of_let(dt: u64, dv: u64, db: u64) -> u64 {
    let h: u64 = expr::hash32(name::mix_hash(
        29,
        name::mix_hash(
            expr::hash_of_data(dt),
            name::mix_hash(expr::hash_of_data(dv), expr::hash_of_data(db)),
        ),
    ));
    expr::pack_data(
        h,
        expr::max_u64(
            expr::max_u64(expr::bvar_of_data(dt), expr::bvar_of_data(dv)),
            expr::sat_pred(expr::bvar_of_data(db)),
        ),
        expr::max_u64(
            expr::max_u64(expr::fvar_of_data(dt), expr::fvar_of_data(dv)),
            expr::fvar_of_data(db),
        ),
        expr::lp_of_data(dt) || expr::lp_of_data(dv) || expr::lp_of_data(db),
    )
}

/// con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:1120-1128 eBindView` —
/// `eBindView`, the inverse of `EStore.viewBind`: rebuild the binder view a
/// walk decoded with `viewBind`, at the tag it decoded it at. `lam` and
/// `forallE` have one record shape and the projection reads either; this is the
/// one place the two arms are told apart again, so the walks that dispatch on
/// the handle's own tag keep the two clauses of the twin as one clause each.
pub fn e_bind_view(tag: u32, ty: EIdx, body: EIdx, m: BinderMeta) -> ENodeView {
    if tag == ETAG_LAM {
        ENodeView::Lam(ty, body, m)
    } else {
        ENodeView::ForallE(ty, body, m)
    }
}

/// con-leche: none — arena infrastructure (task #97-P6-1); Lean twin:
/// `proof/ConRon/Arena/Store.lean:1522-1543 EStore.eViewHasScratchChild` —
/// **a tier test on the children, not a decode**: is a child scratch?
///
/// A persistent node's children are persistent.  That is not an accident of
/// the code but a clause `StoreWF` cannot do without: a persistent handle
/// keeps its bits across `drop_scratch` (DESIGN.md §8.3, con-leche's lesson
/// 6) and must still denote afterwards, which it could not if one of its
/// children lived in the tier that just went away.  Operationally the same
/// thing: `EStore::intern` appends to the persistent tier only while
/// `scratch_on` is false, and while it is false no live handle is a scratch
/// handle.
///
/// So a view with a scratch child **cannot** be in the persistent cons table,
/// and `EStore::pers_find_maybe` does not probe it.  That probe is the single
/// most expensive thing the checker does — the persistent `apps` table alone
/// is millions of buckets over a 32 MB L3, so it is a guaranteed cache miss —
/// and on `Init` skipping it is worth **17 % of the cycles and 17 % of the
/// wall** at 1.7 % of the instructions, which is the shape of the IPC gap
/// task #97-P4f measured.
pub fn e_view_has_scratch_child(v: &ENodeView) -> bool {
    match v {
        ENodeView::BVar(_) => false,
        ENodeView::FVar(_, ty) => !ty.is_persistent(),
        ENodeView::Sort(u) => !u.is_persistent(),
        ENodeView::Const(n, us) => {
            if n.is_persistent() {
                !us.is_persistent()
            } else {
                true
            }
        }
        ENodeView::App(f, a) => {
            if f.is_persistent() {
                !a.is_persistent()
            } else {
                true
            }
        }
        ENodeView::Lam(ty, b, _) => {
            if ty.is_persistent() {
                !b.is_persistent()
            } else {
                true
            }
        }
        ENodeView::ForallE(ty, b, _) => {
            if ty.is_persistent() {
                !b.is_persistent()
            } else {
                true
            }
        }
        ENodeView::LetE(ty, val, b) => {
            if ty.is_persistent() {
                if val.is_persistent() {
                    !b.is_persistent()
                } else {
                    true
                }
            } else {
                true
            }
        }
        ENodeView::Lit(_) => false,
        ENodeView::Proj(n, _, e) => {
            if n.is_persistent() {
                !e.is_persistent()
            } else {
                true
            }
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:384-392 EStore
impl EStore {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:73-74 EStore.empty
    pub fn empty() -> EStore {
        EStore {
            lss: LsStore::empty(),
            pers: ETables::empty(),
            scr: ETables::empty(),
            scratch_on: false,
            shared_on: false,
        }
    }


    /// con-leche: none — arena infrastructure (task #97-P6-6b); Lean twin:
    /// `proof/ConRon/Arena/Store.lean` — the persistent arm of `EStore.view`
    ///
    /// One of the five **value-returning persistent readers** task #97-P6-6's
    /// design (A) is written around: the choice between this store's own
    /// persistent tier and the shared `PersTier` is made HERE and a value
    /// comes back, so no borrow ever leaves the choice and no region enters
    /// the record every function of the crate threads as `&mut`.
    #[inline(always)]
    fn pers_get(&self, pers: &PersTier, i: &EIdx) -> Option<ENodeView> {
        if self.shared_on {
            pers.e.get(i)
        } else {
            self.pers.get(i)
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-6b); Lean twin:
    /// `proof/ConRon/Arena/Store.lean` — the persistent arm of `EStore.derived`
    ///
    /// One of the five **value-returning persistent readers** task #97-P6-6's
    /// design (A) is written around: the choice between this store's own
    /// persistent tier and the shared `PersTier` is made HERE and a value
    /// comes back, so no borrow ever leaves the choice and no region enters
    /// the record every function of the crate threads as `&mut`.
    #[inline(always)]
    fn pers_der_at(&self, pers: &PersTier, i: &EIdx) -> u64 {
        if self.shared_on {
            pers.e.der_at(i)
        } else {
            self.pers.der_at(i)
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-6b); Lean twin:
    /// `proof/ConRon/Arena/Store.lean` — the persistent arm of `EStore.find?`
    ///
    /// One of the five **value-returning persistent readers** task #97-P6-6's
    /// design (A) is written around: the choice between this store's own
    /// persistent tier and the shared `PersTier` is made HERE and a value
    /// comes back, so no borrow ever leaves the choice and no region enters
    /// the record every function of the crate threads as `&mut`.
    fn pers_find(&self, pers: &PersTier, v: &ENodeView, mi: &BMIdx) -> Option<EIdx> {
        if self.shared_on {
            pers.e.find(v, mi)
        } else {
            self.pers.find(v, mi)
        }
    }


    /// con-leche: none — arena infrastructure (task #97-P6-17)
    /// The persistent arm of the capacity test, a value-returning persistent
    /// reader beside `pers_size_of` (task #97-P6-6b's design (A)).
    fn pers_full_of(&self, pers: &PersTier, v: &ENodeView) -> bool {
        if self.shared_on {
            pers.e.full_of(v)
        } else {
            self.pers.full_of(v)
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:466-467 EStore.persCount
    pub fn pers_count(&self, pers: &PersTier) -> usize {
        if self.shared_on {
            pers.e.count()
        } else {
            self.pers.count()
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:466-469 EStore.scrCount
    pub fn scr_count(&self) -> usize {
        self.scr.count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:466-471 EStore.nodeCount
    pub fn node_count(&self, pers: &PersTier) -> usize {
        self.pers_count(pers) + self.scr_count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1144-1145 EStore.lsS
    /// The level-list store underneath.
    pub fn ls_s(&self) -> &LsStore {
        &self.lss
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1144-1147 EStore.ls
    /// The level store underneath.
    pub fn ls(&self) -> &LStore {
        &self.lss.ls
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:761-762 EStore.ns
    /// The name store underneath.
    pub fn ns(&self) -> &NStore {
        &self.lss.ls.ns
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1151-1152 EStore.nder
    /// A name's derived word, read through the nesting.
    pub fn nder(&self, pers: &PersTier, i: &NIdx) -> u64 {
        self.ns().derived(pers, i)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1151-1154 EStore.lder
    /// A level's derived record.
    pub fn lder(&self, pers: &PersTier, i: &LIdx) -> LDer {
        self.ls().derived(pers, i)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1151-1156 EStore.lsder
    /// A level list's derived record.
    pub fn lsder(&self, pers: &PersTier, i: &LsIdx) -> LDer {
        self.lss.derived(pers, i)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:473-477 EStore.view
    /// Decode an expression handle: the tier bit selects the array set, the
    /// tag selects the array, the index reads it.
    #[inline(always)]
    pub fn view(&self, pers: &PersTier, i: &EIdx) -> Option<ENodeView> {
        if e_tag_is_bind(i.tag()) {
            match self.view_bind(pers, i) {
                None => None,
                Some(t) => Some(e_bind_view(i.tag(), t.0, t.1, t.2)),
            }
        } else if i.is_persistent() {
            self.pers_get(pers, i)
        } else if self.scratch_on {
            self.scr.get(i)
        } else {
            None
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-10); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1174-1177 EStore.viewApp` — the
    /// persistent arm of `EStore.viewApp`.
    #[inline(always)]
    fn pers_get_app(&self, pers: &PersTier, i: &EIdx) -> Option<(EIdx, EIdx)> {
        if self.shared_on {
            pers.e.get_app(i)
        } else {
            self.pers.get_app(i)
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1174-1177 EStore.viewApp` —
    /// `EStore.viewApp`, the `app` projection of `EStore.view`: the tier bit
    /// selects the array set, the `app` array is read, the two children come
    /// back. `view h = some (.app f a) ↔ viewApp h = some (f, a)` whenever
    /// `h.tag = app`, which is the exactness lemma the bridge owes.
    #[inline(always)]
    pub fn view_app(&self, pers: &PersTier, i: &EIdx) -> Option<(EIdx, EIdx)> {
        if i.is_persistent() {
            self.pers_get_app(pers, i)
        } else if self.scratch_on {
            self.scr.get_app(i)
        } else {
            None
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-13); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1182-1185 EStore.viewSort` — the
    /// persistent arm of `EStore.viewSort`.
    #[inline(always)]
    fn pers_get_sort(&self, pers: &PersTier, i: &EIdx) -> Option<LIdx> {
        if self.shared_on {
            pers.e.get_sort(i)
        } else {
            self.pers.get_sort(i)
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1182-1185 EStore.viewSort` —
    /// `EStore.viewSort`, the `sort` projection of `EStore.view`.
    #[inline(always)]
    pub fn view_sort(&self, pers: &PersTier, i: &EIdx) -> Option<LIdx> {
        if i.is_persistent() {
            self.pers_get_sort(pers, i)
        } else if self.scratch_on {
            self.scr.get_sort(i)
        } else {
            None
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-13); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1191-1194 EStore.viewConst` — the
    /// persistent arm of `EStore.viewConst`.
    #[inline(always)]
    fn pers_get_const(&self, pers: &PersTier, i: &EIdx) -> Option<(NIdx, LsIdx)> {
        if self.shared_on {
            pers.e.get_const(i)
        } else {
            self.pers.get_const(i)
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1191-1194 EStore.viewConst` —
    /// `EStore.viewConst`, the `const` projection of `EStore.view`.
    #[inline(always)]
    pub fn view_const(&self, pers: &PersTier, i: &EIdx) -> Option<(NIdx, LsIdx)> {
        if i.is_persistent() {
            self.pers_get_const(pers, i)
        } else if self.scratch_on {
            self.scr.get_const(i)
        } else {
            None
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-13); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1200-1203 EStore.viewConstName` — the
    /// persistent arm of `EStore.viewConstName`.
    #[inline(always)]
    fn pers_get_const_name(&self, pers: &PersTier, i: &EIdx) -> Option<NIdx> {
        if self.shared_on {
            pers.e.get_const_name(i)
        } else {
            self.pers.get_const_name(i)
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1200-1203 EStore.viewConstName` —
    /// `EStore.viewConstName`, the head NAME of a `const` node.
    #[inline(always)]
    pub fn view_const_name(&self, pers: &PersTier, i: &EIdx) -> Option<NIdx> {
        if i.is_persistent() {
            self.pers_get_const_name(pers, i)
        } else if self.scratch_on {
            self.scr.get_const_name(i)
        } else {
            None
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-10); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1205-1206 EStore.persGetBVar` — the persistent
    /// arms of the four projections below.
    #[inline(always)]
    fn pers_get_bvar(&self, pers: &PersTier, i: &EIdx) -> Option<u64> {
        if self.shared_on {
            pers.e.get_bvar(i)
        } else {
            self.pers.get_bvar(i)
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-10); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1258-1260 EStore.persGetBind`
    #[inline(always)]
    fn pers_get_bind(&self, pers: &PersTier, i: &EIdx) -> Option<(EIdx, EIdx, BMIdx)> {
        if self.shared_on {
            pers.e.get_bind(i)
        } else {
            self.pers.get_bind(i)
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Store.lean:1275-1280 EStore.viewBM` — the
    /// persistent arm of `EStore.viewBM`.
    #[inline(always)]
    fn pers_get_bm(&self, pers: &PersTier, i: &BMIdx) -> Option<BinderMeta> {
        if self.shared_on {
            pers.e.get_bm(i)
        } else {
            self.pers.get_bm(i)
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Store.lean:1287-1291 EStore.bmDer` — the
    /// persistent arm of `EStore.bmDer`.
    #[inline(always)]
    fn pers_get_bm_der(&self, pers: &PersTier, i: &BMIdx) -> (u64, bool) {
        if self.shared_on {
            pers.e.get_bm_der(i)
        } else {
            self.pers.get_bm_der(i)
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-10); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1240-1242 EStore.persGetLet`
    #[inline(always)]
    fn pers_get_let(&self, pers: &PersTier, i: &EIdx) -> Option<(EIdx, EIdx, EIdx)> {
        if self.shared_on {
            pers.e.get_let(i)
        } else {
            self.pers.get_let(i)
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-10); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1249-1251 EStore.persGetProj`
    #[inline(always)]
    fn pers_get_proj(&self, pers: &PersTier, i: &EIdx) -> Option<(NIdx, u64, EIdx)> {
        if self.shared_on {
            pers.e.get_proj(i)
        } else {
            self.pers.get_proj(i)
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-10); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1213-1215 EStore.persGetFVarIdx`
    #[inline(always)]
    fn pers_get_fvar_idx(&self, pers: &PersTier, i: &EIdx) -> Option<u64> {
        if self.shared_on {
            pers.e.get_fvar_idx(i)
        } else {
            self.pers.get_fvar_idx(i)
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1217-1220 EStore.viewFVarIdx` —
    /// `EStore.viewFVarIdx`, the `fvar` index projection.
    #[inline(always)]
    pub fn view_fvar_idx(&self, pers: &PersTier, i: &EIdx) -> Option<u64> {
        if i.is_persistent() {
            self.pers_get_fvar_idx(pers, i)
        } else if self.scratch_on {
            self.scr.get_fvar_idx(i)
        } else {
            None
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-13); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1226-1229 EStore.viewFVarTy` — the
    /// persistent arm of `EStore.viewFVarTy`.
    #[inline(always)]
    fn pers_get_fvar_ty(&self, pers: &PersTier, i: &EIdx) -> Option<EIdx> {
        if self.shared_on {
            pers.e.get_fvar_ty(i)
        } else {
            self.pers.get_fvar_ty(i)
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1226-1229 EStore.viewFVarTy` —
    /// `EStore.viewFVarTy`, the `fvar` binder-type projection.
    #[inline(always)]
    pub fn view_fvar_ty(&self, pers: &PersTier, i: &EIdx) -> Option<EIdx> {
        if i.is_persistent() {
            self.pers_get_fvar_ty(pers, i)
        } else if self.scratch_on {
            self.scr.get_fvar_ty(i)
        } else {
            None
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-13); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1235-1238 EStore.viewLit` — the
    /// persistent arm of `EStore.viewLit`.
    #[inline(always)]
    fn pers_get_lit(&self, pers: &PersTier, i: &EIdx) -> Option<Literal> {
        if self.shared_on {
            pers.e.get_lit(i)
        } else {
            self.pers.get_lit(i)
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1235-1238 EStore.viewLit` —
    /// `EStore.viewLit`, the `lit` projection of `EStore.view`.
    #[inline(always)]
    pub fn view_lit(&self, pers: &PersTier, i: &EIdx) -> Option<Literal> {
        if i.is_persistent() {
            self.pers_get_lit(pers, i)
        } else if self.scratch_on {
            self.scr.get_lit(i)
        } else {
            None
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1208-1211 EStore.viewBVar` —
    /// `EStore.viewBVar`, the `bvar` projection of `EStore.view`.
    #[inline(always)]
    pub fn view_bvar(&self, pers: &PersTier, i: &EIdx) -> Option<u64> {
        if i.is_persistent() {
            self.pers_get_bvar(pers, i)
        } else if self.scratch_on {
            self.scr.get_bvar(i)
        } else {
            None
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1293-1302 EStore.viewBind` —
    /// `EStore.viewBind`, the binder projection of `EStore.view`.
    #[inline(always)]
    pub fn view_bind(&self, pers: &PersTier, i: &EIdx) -> Option<(EIdx, EIdx, BinderMeta)> {
        match self.view_bind_i(pers, i) {
            None => None,
            Some(t) => match self.view_bm(pers, &t.2) {
                None => None,
                Some(m) => Some((t.0, t.1, m)),
            },
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-16); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1262-1268 EStore.viewBindI` —
    /// `EStore.viewBindI`, the binder projection that stops at the datum's
    /// HANDLE. This is what the rebuilding walks want: a walk that takes a
    /// binder apart and puts it back together never looks inside the datum, it
    /// only carries it across, and carrying a `BMIdx` is a register move where
    /// carrying a `BinderMeta` was a reference count out and a reference count
    /// back.
    #[inline(always)]
    pub fn view_bind_i(&self, pers: &PersTier, i: &EIdx) -> Option<(EIdx, EIdx, BMIdx)> {
        if i.is_persistent() {
            self.pers_get_bind(pers, i)
        } else if self.scratch_on {
            self.scr.get_bind(i)
        } else {
            None
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Store.lean:1275-1280 EStore.viewBM` —
    /// `EStore.viewBM`: decode a binder datum handle, the tier bit selecting
    /// the array set as it does for every other handle kind.
    #[inline(always)]
    pub fn view_bm(&self, pers: &PersTier, i: &BMIdx) -> Option<BinderMeta> {
        if i.is_persistent() {
            self.pers_get_bm(pers, i)
        } else if self.scratch_on {
            self.scr.get_bm(i)
        } else {
            None
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Store.lean:1287-1291 EStore.bmDer` —
    /// `EStore.bmDer`, the binder datum's two derived scalars (`PropWhen.hash`,
    /// `PropWhen.hasParams`), which is everything `derOfBind` asks of it.
    #[inline(always)]
    pub fn bm_der(&self, pers: &PersTier, i: &BMIdx) -> (u64, bool) {
        if i.is_persistent() {
            self.pers_get_bm_der(pers, i)
        } else if self.scratch_on {
            self.scr.get_bm_der(i)
        } else {
            (0, false)
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Store.lean:949-952 EStore.findBM` —
    /// `EStore.findBM`, the datum's cons probe over both tiers, persistent
    /// first (the store's own order). A datum that is not interned names no
    /// binder node, so `find` answers `none` for the whole binder view.
    pub fn find_bm(&self, pers: &PersTier, m: &BinderMeta) -> Option<BMIdx> {
        match self.pers_find_bm(pers, m) {
            Some(i) => Some(i),
            None => {
                if self.scratch_on {
                    self.scr.find_bm(m)
                } else {
                    None
                }
            }
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Store.lean:949-952 EStore.findBM` — the
    /// persistent arm of `EStore.findBM`.
    fn pers_find_bm(&self, pers: &PersTier, m: &BinderMeta) -> Option<BMIdx> {
        if self.shared_on {
            pers.e.find_bm(m)
        } else {
            self.pers.find_bm(m)
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Store.lean:1441-1461 EStore.internBM` —
    /// `EStore.internBM`: hash-cons a binder datum, `intern`'s own clauses at a
    /// store with one constructor — the persistent probe, the scratch probe,
    /// the capacity test, the append to the tier the store is in. The datum has
    /// no children, so there is no `eViewHasScratchChild` arm to skip the
    /// persistent probe with.
    pub fn intern_bm(&mut self, pers: &PersTier, m: BinderMeta) -> Result<BMIdx, CheckError> {
        let r: BMNode = BMNode { pw: m.pw };
        let hit: Option<BMIdx> = if self.shared_on {
            pers.e.bms.find(&r)
        } else {
            self.pers.bms.find(&r)
        };
        match hit {
            Some(hp) => Ok(hp),
            None => {
                if self.scratch_on {
                    let at: (usize, Option<BMIdx>) = self.scr.bms.find_slot(&r);
                    match at.1 {
                        Some(hs) => Ok(hs),
                        None => {
                            if self.scr.bms.full() {
                                Err(CheckError::Native(code_points(&M_E_CAP)))
                            } else {
                                let d: u64 = prop_when::hash_pw(&r.pw);
                                let h: BMIdx =
                                    BMIdx::pack(TIER_S, self.scr.bms.size() as u32);
                                self.scr.bms.push_at(at.0, r, d, h.dup2());
                                Ok(h)
                            }
                        }
                    }
                } else if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers.bms.full() {
                    Err(CheckError::Native(code_points(&M_E_CAP)))
                } else {
                    let d: u64 = prop_when::hash_pw(&r.pw);
                    let h: BMIdx = BMIdx::pack(TIER_P, self.pers.bms.size() as u32);
                    self.pers.bms.push(r, d, h.dup2());
                    Ok(h)
                }
            }
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Store.lean:1463-1474
    /// EStore.internBMPersistent` — `EStore.internBMPersistent`, the binder
    /// datum's promote-intern: `internPersistent`'s clauses at the datum store,
    /// so that a promoted binder names a PERSISTENT datum.
    pub fn intern_bm_persistent(
        &mut self,
        pers: &PersTier,
        m: BinderMeta,
    ) -> Result<BMIdx, CheckError> {
        let r: BMNode = BMNode { pw: m.pw };
        let hit: Option<BMIdx> = if self.shared_on {
            pers.e.bms.find(&r)
        } else {
            self.pers.bms.find(&r)
        };
        match hit {
            Some(hp) => Ok(hp),
            None => {
                if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers.bms.full() {
                    Err(CheckError::Native(code_points(&M_E_CAP)))
                } else {
                    let d: u64 = prop_when::hash_pw(&r.pw);
                    let h: BMIdx = BMIdx::pack(TIER_P, self.pers.bms.size() as u32);
                    self.pers.bms.push(r, d, h.dup2());
                    Ok(h)
                }
            }
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Store.lean:1513-1520
    /// EStore.internBMOfViewPersistent` — the binder datum a view names, made
    /// persistent, so that `internPersistent` can go on working over the view
    /// while the record names the datum by a handle. A non-binder view names no
    /// datum and the value is never read.
    pub fn intern_bm_of_view_persistent(
        &mut self,
        pers: &PersTier,
        v: &ENodeView,
    ) -> Result<BMIdx, CheckError> {
        match v {
            ENodeView::Lam(_, _, m) => {
                self.intern_bm_persistent(pers, expr::binder_meta_dup(m))
            }
            ENodeView::ForallE(_, _, m) => {
                self.intern_bm_persistent(pers, expr::binder_meta_dup(m))
            }
            _ => Ok(BMIdx::of_word(0)),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1244-1247 EStore.viewLet` —
    /// `EStore.viewLet`, the `letE` projection of `EStore.view`.
    #[inline(always)]
    pub fn view_let(&self, pers: &PersTier, i: &EIdx) -> Option<(EIdx, EIdx, EIdx)> {
        if i.is_persistent() {
            self.pers_get_let(pers, i)
        } else if self.scratch_on {
            self.scr.get_let(i)
        } else {
            None
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1253-1256 EStore.viewProj` —
    /// `EStore.viewProj`, the `proj` projection of `EStore.view`.
    #[inline(always)]
    pub fn view_proj(&self, pers: &PersTier, i: &EIdx) -> Option<(NIdx, u64, EIdx)> {
        if i.is_persistent() {
            self.pers_get_proj(pers, i)
        } else if self.scratch_on {
            self.scr.get_proj(i)
        } else {
            None
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr
    /// Lean twin: `proof/ConRon/Arena/Store.lean:479-483 EStore.derived` — the
    /// `data` computed field, lines 357-402: the packed derived word of an
    /// expression handle, an `O(1)` column read.
    #[inline(always)]
    pub fn derived(&self, pers: &PersTier, i: &EIdx) -> u64 {
        if i.is_persistent() {
            self.pers_der_at(pers, i)
        } else if self.scratch_on {
            self.scr.der_at(i)
        } else {
            0
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr
    /// Lean twin: `proof/ConRon/Arena/Store.lean:485-492 EStore.derOfView` —
    /// the `bvar` arm, which is `con_ron_core::kernel::expr::bvar`'s own body.
    ///
    /// **One function per arm** (task #97-P6-15).  `der_of_view` used to be
    /// the only caller and wrote the ten arms inline; `intern`'s ten
    /// per-constructor paths need the same arithmetic off the node RECORD,
    /// and a `match` on a view they have already taken apart is exactly the
    /// dispatch that task's lever removes.  Each arm is therefore a function
    /// of that arm's own fields, called from both — the same bodies, in the
    /// same order, with `data(&child)` still replaced by the derived column.
    /// The twin writes the arms out inline, as it does today.
    ///
    /// **`#[inline(always)]` on all nine** (task #97-P6-15): the arms are
    /// called from ONE per-constructor path each, on the miss branch, and out
    /// of line each miss paid a call with the record's fields spilled to it.
    /// Inlined, the arm's arithmetic joins the path that already holds them —
    /// −0.71 % of `Init` and −0.74 % of the Mathlib prefix.  `der_of_view`'s
    /// own ten-arm dispatch keeps them out of line where it is the caller,
    /// which is the cold `intern_persistent`/`promote` path.
    #[inline(always)]
    pub fn der_of_bvar(&self, i: u64) -> u64 {
        let h: u64 = expr::hash32(name::mix_hash(3, name::nat_hash(i)));
        expr::pack_data(h, expr::sat_succ(i), 0, false)
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr
    /// Lean twin: `proof/ConRon/Arena/Store.lean:485-492 EStore.derOfView` —
    /// the `fvar` arm (`con_ron_core::kernel::expr::fvar`'s body).  See
    /// `der_of_bvar`'s note.
    #[inline(always)]
    pub fn der_of_fvar(&self, pers: &PersTier, idx: u64, ty: &EIdx) -> u64 {
        let dt: u64 = self.derived(pers, ty);
        let h: u64 = expr::hash32(name::mix_hash(
            5,
            name::mix_hash(name::nat_hash(idx), expr::hash_of_data(dt)),
        ));
        expr::pack_data(h, 0, expr::sat_succ(idx), expr::lp_of_data(dt))
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr
    /// Lean twin: `proof/ConRon/Arena/Store.lean:485-492 EStore.derOfView` —
    /// the `sort` arm (`con_ron_core::kernel::expr::sort`'s body).  See
    /// `der_of_bvar`'s note.
    #[inline(always)]
    pub fn der_of_sort(&self, pers: &PersTier, u: &LIdx) -> u64 {
        let du = self.lder(pers, u);
        let h: u64 = expr::hash32(name::mix_hash(7, du.hash));
        expr::pack_data(h, 0, 0, du.has_param)
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr
    /// Lean twin: `proof/ConRon/Arena/Store.lean:485-492 EStore.derOfView` —
    /// the `const` arm (`con_ron_core::kernel::expr::mk_const`'s body).  See
    /// `der_of_bvar`'s note.
    #[inline(always)]
    pub fn der_of_const(&self, pers: &PersTier, n: &NIdx, us: &LsIdx) -> u64 {
        let dus = self.lsder(pers, us);
        let h: u64 =
            expr::hash32(name::mix_hash(11, name::mix_hash(self.nder(pers, n), dus.hash)));
        expr::pack_data(h, 0, 0, dus.has_param)
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr
    /// Lean twin: `proof/ConRon/Arena/Store.lean:485-492 EStore.derOfView` —
    /// the `app` arm (`con_ron_core::kernel::expr::app`'s body).  See
    /// `der_of_bvar`'s note.
    #[inline(always)]
    pub fn der_of_app(&self, pers: &PersTier, f: &EIdx, a: &EIdx) -> u64 {
        let df: u64 = self.derived(pers, f);
        let da: u64 = self.derived(pers, a);
        let h: u64 = expr::hash32(name::mix_hash(
            17,
            name::mix_hash(expr::hash_of_data(df), expr::hash_of_data(da)),
        ));
        expr::pack_data(
            h,
            expr::max_u64(expr::bvar_of_data(df), expr::bvar_of_data(da)),
            expr::max_u64(expr::fvar_of_data(df), expr::fvar_of_data(da)),
            expr::lp_of_data(df) || expr::lp_of_data(da),
        )
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr
    /// Lean twin: `proof/ConRon/Arena/Store.lean:485-492 EStore.derOfView` —
    /// the `lam` (hash tag 19) and `forallE` (23) arms, whose arithmetic is
    /// `der_of_bind`'s (see that function's note for why it is a function of
    /// five scalars and not the arm itself).  See `der_of_bvar`'s note.
    #[inline(always)]
    pub fn der_of_bind_at(
        &self,
        pers: &PersTier,
        tag: u64,
        ty: &EIdx,
        b: &EIdx,
        m: &BinderMeta,
    ) -> u64 {
        der_of_bind(
            tag,
            self.derived(pers, ty),
            self.derived(pers, b),
            prop_when::hash_pw(&m.pw),
            prop_when::has_params(&m.pw),
        )
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr
    /// Lean twin: `proof/ConRon/Arena/Store.lean:1375-1384 EStore.derOfBindAtI`
    /// — `derOfBindAtI`, the `lam`/`forallE` arm over the datum's HANDLE: the
    /// two scalars `derOfBind` wants of the datum are the binder-datum store's
    /// own derived column and a tag test on its record, so the arithmetic is
    /// unchanged and no `PropWhen` is walked.
    #[inline(always)]
    pub fn der_of_bind_at_i(
        &self,
        pers: &PersTier,
        tag: u64,
        ty: &EIdx,
        b: &EIdx,
        m: &BMIdx,
    ) -> u64 {
        let bd: (u64, bool) = self.bm_der(pers, m);
        der_of_bind(tag, self.derived(pers, ty), self.derived(pers, b), bd.0, bd.1)
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr
    /// Lean twin: `proof/ConRon/Arena/Store.lean:485-492 EStore.derOfView` —
    /// the `letE` arm, whose arithmetic is `der_of_let`'s.  See
    /// `der_of_bvar`'s note.
    #[inline(always)]
    pub fn der_of_let_at(&self, pers: &PersTier, ty: &EIdx, val: &EIdx, b: &EIdx) -> u64 {
        der_of_let(self.derived(pers, ty), self.derived(pers, val), self.derived(pers, b))
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr
    /// Lean twin: `proof/ConRon/Arena/Store.lean:485-492 EStore.derOfView` —
    /// the `lit` arm (`con_ron_core::kernel::expr::lit`'s body).  See
    /// `der_of_bvar`'s note.
    #[inline(always)]
    pub fn der_of_lit(&self, l: &Literal) -> u64 {
        let h: u64 = expr::hash32(name::mix_hash(31, expr::literal_hash(l)));
        expr::pack_data(h, 0, 0, false)
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr
    /// Lean twin: `proof/ConRon/Arena/Store.lean:485-492 EStore.derOfView` —
    /// the `proj` arm (`con_ron_core::kernel::expr::proj`'s body).  See
    /// `der_of_bvar`'s note.
    #[inline(always)]
    pub fn der_of_proj(&self, pers: &PersTier, s: &NIdx, i: u64, e: &EIdx) -> u64 {
        let de: u64 = self.derived(pers, e);
        let h: u64 = expr::hash32(name::mix_hash(
            37,
            name::mix_hash(
                self.nder(pers, s),
                name::mix_hash(name::nat_hash(i), expr::hash_of_data(de)),
            ),
        ));
        expr::pack_data(
            h,
            expr::bvar_of_data(de),
            expr::fvar_of_data(de),
            expr::lp_of_data(de),
        )
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr
    /// Lean twin: `proof/ConRon/Arena/Store.lean:485-492 EStore.derOfView` —
    /// the `data` computed field, lines 357-402.
    ///
    /// **Not re-derived.**  Each arm is the body of the corresponding smart
    /// constructor of `con_ron_core::kernel::expr`
    /// (`bvar`/`fvar`/`sort`/`mk_const`/`app`/`lam`/`forall_e`/`let_e`/`lit`/
    /// `proj`), with `data(&child)` replaced by `self.derived(pers, h)`, the
    /// level reads by the level store's derived column (`level_hash u ↦
    /// self.lder(pers, u).hash`, `level_has_param u ↦
    /// self.lder(pers, u).has_param`), the name read by `self.nder(pers, n)`
    /// (the `Hashable Name` instance *is* `Name.hashData`) and `levels_hash us
    /// ↦ self.lsder(pers, us).hash`.  Every `pack_data`, `hash32`, `mix_hash`,
    /// `sat_succ`, `sat_pred` and `max_u64` call is that crate's, imported and
    /// not copied, which is what makes the arena's word and `expr::data`'s
    /// word the same function of the same term — the equality `mod tests`
    /// checks per constructor.
    ///
    /// **The arms are `der_of_*` since task #97-P6-15** (see `der_of_bvar`),
    /// because `intern`'s per-constructor paths want the same arithmetic off
    /// the node record.  This function is what the paths that still hold an
    /// `ENodeView` call — `intern_persistent` and `arena::promote` — and it is
    /// the twin's `derOfView` unchanged.
    pub fn der_of_view(&self, pers: &PersTier, v: &ENodeView) -> u64 {
        match v {
            ENodeView::BVar(i) => self.der_of_bvar(*i),
            ENodeView::FVar(idx, ty) => self.der_of_fvar(pers, *idx, ty),
            ENodeView::Sort(u) => self.der_of_sort(pers, u),
            ENodeView::Const(n, us) => self.der_of_const(pers, n, us),
            ENodeView::App(f, a) => self.der_of_app(pers, f, a),
            ENodeView::Lam(ty, b, m) => self.der_of_bind_at(pers, 19, ty, b, m),
            ENodeView::ForallE(ty, b, m) => self.der_of_bind_at(pers, 23, ty, b, m),
            ENodeView::LetE(ty, val, b) => self.der_of_let_at(pers, ty, val, b),
            ENodeView::Lit(l) => self.der_of_lit(l),
            ENodeView::Proj(s, i, e) => self.der_of_proj(pers, s, *i, e),
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-1); Lean twin:
    /// `proof/ConRon/Arena/Store.lean:90-91 EStore.find?` — **the
    /// persistent half of the probe**, skipped when the view has a scratch
    /// child (`e_view_has_scratch_child`'s note).  The twin skips too since
    /// task #97-T2-LOCKSTEP (D2): `EStore.persFindMaybe`, and Theorem 1 owns
    /// the equation that the skip changes nothing under `StoreWF`
    /// (`Arena/WFSkip.lean`).
    pub fn pers_find_maybe(&self, pers: &PersTier, v: &ENodeView, mi: &BMIdx) -> Option<EIdx> {
        if self.scratch_on {
            if e_view_has_scratch_child(v) {
                None
            } else {
                self.pers_find(pers, v, mi)
            }
        } else {
            self.pers_find(pers, v, mi)
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:90-91 EStore.find?
    /// Probe both tiers, persistent first (nanoda's `alloc_expr`).
    pub fn find(&self, pers: &PersTier, v: &ENodeView) -> Option<EIdx> {
        match self.find_bm_of_view(pers, v) {
            None => None,
            Some(mi) => match self.pers_find_maybe(pers, v, &mi) {
                Some(i) => Some(i),
                None => {
                    if self.scratch_on {
                        self.scr.find(v, &mi)
                    } else {
                        None
                    }
                }
            },
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta
    /// Lean twin: `proof/ConRon/Arena/Store.lean:1495-1503 EStore.findBMOfView`
    /// — the datum handle a view's cons key needs, PROBED and not interned: a
    /// binder whose datum has never been interned is not in either table, so
    /// `none` here is `none` for the whole `find`.
    fn find_bm_of_view(&self, pers: &PersTier, v: &ENodeView) -> Option<BMIdx> {
        match v {
            ENodeView::Lam(_, _, m) => self.find_bm(pers, m),
            ENodeView::ForallE(_, _, m) => self.find_bm(pers, m),
            _ => Some(BMIdx::of_word(0)),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:501-521 EStore.intern
    /// Hash-cons an expression node: probe the persistent cons table, then the
    /// scratch one, then append to the tier the store is in (DESIGN.md §8.3).
    /// The cap test is the Lean's `capOK` turned into the `Native` decline
    /// §8.3 puts here.
    ///
    /// **Dispatched ONCE** (task #97-P6-15).  The body below used to run the
    /// whole sequence over the `ENodeView`, and each of its four steps
    /// dispatched on the view's tag again and built the node record again:
    /// the persistent probe built it (inside `ETables::find`), the scratch
    /// probe built it a second time, `der_of_view` re-dispatched to compute
    /// the derived word, and `ETables::push` re-dispatched and built it a
    /// third time to append it.  A binder paid `binder_meta_dup` at each of
    /// the three.  So the tag is read once here and the ten per-constructor
    /// paths below each build their record ONCE and hand the same `&r` to the
    /// two probes, to the capacity test and to the push — the same clauses in
    /// the same order, with the dispatch and the two rebuilds gone.
    ///
    /// The twin's `intern` is one `def` over `ENodeView`; what is owed is the
    /// ten-arm spelling and `internC v = intern (view of C)` per constructor,
    /// each of them `rfl` after the `match`.
    pub fn intern(&mut self, pers: &PersTier, v: ENodeView) -> Result<EIdx, CheckError> {
        match v {
            ENodeView::BVar(i) => self.intern_bvar(pers, i),
            ENodeView::FVar(idx, ty) => self.intern_fvar(pers, idx, ty),
            ENodeView::Sort(u) => self.intern_sort(pers, u),
            ENodeView::Const(n, us) => self.intern_const(pers, n, us),
            ENodeView::App(f, a) => self.intern_app(pers, f, a),
            ENodeView::Lam(ty, body, m) => self.intern_lam(pers, ty, body, m),
            ENodeView::ForallE(ty, body, m) => self.intern_forall_e(pers, ty, body, m),
            ENodeView::LetE(ty, val, body) => self.intern_let_e(pers, ty, val, body),
            ENodeView::Lit(l) => self.intern_lit(pers, l),
            ENodeView::Proj(n, i, e) => self.intern_proj(pers, n, i, e),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1646-1647 EStore.internBVar` —
    /// `EStore.internBVar`, the `bvar` arm of `EStore.intern`, over the node
    /// RECORD rather than over the view.
    ///
    /// The clauses are `intern`'s own, in `intern`'s order — the persistent
    /// probe (skipped when a child is scratch, `e_view_has_scratch_child`'s
    /// own arm), the scratch probe, the capacity test, the append — with the
    /// node record built ONCE and shared by all four.  See `intern`'s note.
    pub fn intern_bvar(&mut self, pers: &PersTier, i: u64) -> Result<EIdx, CheckError> {
        let r: BVarNode = BVarNode { i };
        let sk: bool = false;
        let hit: Option<EIdx> = if sk {
            None
        } else if self.shared_on {
            pers.e.bvars.find(&r)
        } else {
            self.pers.bvars.find(&r)
        };
        match hit {
            Some(hp) => Ok(hp),
            None => {
                if self.scratch_on {
                    let at: (usize, Option<EIdx>) = self.scr.bvars.find_slot(&r);
                    match at.1 {
                        Some(hs) => Ok(hs),
                        None => {
                            if self.scr.bvars.full() {
                                Err(CheckError::Native(code_points(&M_E_CAP)))
                            } else {
                                let d: u64 = self.der_of_bvar(r.i);
                                let h: EIdx =
                                    EIdx::pack(ETAG_BVAR, TIER_S, self.scr.bvars.size() as u32);
                                self.scr.bvars.push_at(at.0, r, d, h.dup2());
                                Ok(h)
                            }
                        }
                    }
                } else if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers.bvars.full() {
                    Err(CheckError::Native(code_points(&M_E_CAP)))
                } else {
                    let d: u64 = self.der_of_bvar(r.i);
                    let h: EIdx = EIdx::pack(ETAG_BVAR, TIER_P, self.pers.bvars.size() as u32);
                    self.pers.bvars.push(r, d, h.dup2());
                    Ok(h)
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1646-1650 EStore.internFVar` —
    /// `EStore.internFVar`, the `fvar` arm of `EStore.intern`, over the node
    /// RECORD rather than over the view.
    ///
    /// The clauses are `intern`'s own, in `intern`'s order — the persistent
    /// probe (skipped when a child is scratch, `e_view_has_scratch_child`'s
    /// own arm), the scratch probe, the capacity test, the append — with the
    /// node record built ONCE and shared by all four.  See `intern`'s note.
    pub fn intern_fvar(&mut self, pers: &PersTier, idx: u64, ty: EIdx) -> Result<EIdx, CheckError> {
        let r: FVarNode = FVarNode { idx, ty };
        // The negation is spelled as a branch rather than `!…` (task
        // #97-SWAP, AENEAS_FINDINGS.md F18): Aeneas renders a `!b` whose `b`
        // came from a bind as Lean's `¬ b`, i.e. a `Prop`, and relies on the
        // `Decidable` coercion to put it back in `Bool` — which works
        // everywhere the expected type is known, and NOT here, where the
        // backend joins this `if` with the one below into a tuple-returning
        // one and the `Prop` reaches a `Bool × Bool` slot.  The generated
        // model does not elaborate then.
        let sk: bool = if self.scratch_on {
            if r.ty.is_persistent() {
                false
            } else {
                true
            }
        } else {
            false
        };
        let hit: Option<EIdx> = if sk {
            None
        } else if self.shared_on {
            pers.e.fvars.find(&r)
        } else {
            self.pers.fvars.find(&r)
        };
        match hit {
            Some(hp) => Ok(hp),
            None => {
                if self.scratch_on {
                    let at: (usize, Option<EIdx>) = self.scr.fvars.find_slot(&r);
                    match at.1 {
                        Some(hs) => Ok(hs),
                        None => {
                            if self.scr.fvars.full() {
                                Err(CheckError::Native(code_points(&M_E_CAP)))
                            } else {
                                let d: u64 = self.der_of_fvar(pers, r.idx, &r.ty);
                                let h: EIdx =
                                    EIdx::pack(ETAG_FVAR, TIER_S, self.scr.fvars.size() as u32);
                                self.scr.fvars.push_at(at.0, r, d, h.dup2());
                                Ok(h)
                            }
                        }
                    }
                } else if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers.fvars.full() {
                    Err(CheckError::Native(code_points(&M_E_CAP)))
                } else {
                    let d: u64 = self.der_of_fvar(pers, r.idx, &r.ty);
                    let h: EIdx = EIdx::pack(ETAG_FVAR, TIER_P, self.pers.fvars.size() as u32);
                    self.pers.fvars.push(r, d, h.dup2());
                    Ok(h)
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1651-1652 EStore.internSort` —
    /// `EStore.internSort`, the `sort` arm of `EStore.intern`, over the node
    /// RECORD rather than over the view.
    ///
    /// The clauses are `intern`'s own, in `intern`'s order — the persistent
    /// probe (skipped when a child is scratch, `e_view_has_scratch_child`'s
    /// own arm), the scratch probe, the capacity test, the append — with the
    /// node record built ONCE and shared by all four.  See `intern`'s note.
    pub fn intern_sort(&mut self, pers: &PersTier, u: LIdx) -> Result<EIdx, CheckError> {
        let r: SortNode = SortNode { u };
        // The negation is spelled as a branch rather than `!…` (task
        // #97-SWAP, AENEAS_FINDINGS.md F18): Aeneas renders a `!b` whose `b`
        // came from a bind as Lean's `¬ b`, i.e. a `Prop`, and relies on the
        // `Decidable` coercion to put it back in `Bool` — which works
        // everywhere the expected type is known, and NOT here, where the
        // backend joins this `if` with the one below into a tuple-returning
        // one and the `Prop` reaches a `Bool × Bool` slot.  The generated
        // model does not elaborate then.
        let sk: bool = if self.scratch_on {
            if r.u.is_persistent() {
                false
            } else {
                true
            }
        } else {
            false
        };
        let hit: Option<EIdx> = if sk {
            None
        } else if self.shared_on {
            pers.e.sorts.find(&r)
        } else {
            self.pers.sorts.find(&r)
        };
        match hit {
            Some(hp) => Ok(hp),
            None => {
                if self.scratch_on {
                    let at: (usize, Option<EIdx>) = self.scr.sorts.find_slot(&r);
                    match at.1 {
                        Some(hs) => Ok(hs),
                        None => {
                            if self.scr.sorts.full() {
                                Err(CheckError::Native(code_points(&M_E_CAP)))
                            } else {
                                let d: u64 = self.der_of_sort(pers, &r.u);
                                let h: EIdx =
                                    EIdx::pack(ETAG_SORT, TIER_S, self.scr.sorts.size() as u32);
                                self.scr.sorts.push_at(at.0, r, d, h.dup2());
                                Ok(h)
                            }
                        }
                    }
                } else if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers.sorts.full() {
                    Err(CheckError::Native(code_points(&M_E_CAP)))
                } else {
                    let d: u64 = self.der_of_sort(pers, &r.u);
                    let h: EIdx = EIdx::pack(ETAG_SORT, TIER_P, self.pers.sorts.size() as u32);
                    self.pers.sorts.push(r, d, h.dup2());
                    Ok(h)
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1651-1655 EStore.internConst` —
    /// `EStore.internConst`, the `const` arm of `EStore.intern`, over the node
    /// RECORD rather than over the view.
    ///
    /// The clauses are `intern`'s own, in `intern`'s order — the persistent
    /// probe (skipped when a child is scratch, `e_view_has_scratch_child`'s
    /// own arm), the scratch probe, the capacity test, the append — with the
    /// node record built ONCE and shared by all four.  See `intern`'s note.
    pub fn intern_const(&mut self, pers: &PersTier, n: NIdx, us: LsIdx) -> Result<EIdx, CheckError> {
        let r: ConstNode = ConstNode { n, us };
        let sk: bool = if self.scratch_on {
            if r.n.is_persistent() {
                !r.us.is_persistent()
            } else {
                true
            }
        } else {
            false
        };
        let hit: Option<EIdx> = if sk {
            None
        } else if self.shared_on {
            pers.e.consts.find(&r)
        } else {
            self.pers.consts.find(&r)
        };
        match hit {
            Some(hp) => Ok(hp),
            None => {
                if self.scratch_on {
                    let at: (usize, Option<EIdx>) = self.scr.consts.find_slot(&r);
                    match at.1 {
                        Some(hs) => Ok(hs),
                        None => {
                            if self.scr.consts.full() {
                                Err(CheckError::Native(code_points(&M_E_CAP)))
                            } else {
                                let d: u64 = self.der_of_const(pers, &r.n, &r.us);
                                let h: EIdx =
                                    EIdx::pack(ETAG_CONST, TIER_S, self.scr.consts.size() as u32);
                                self.scr.consts.push_at(at.0, r, d, h.dup2());
                                Ok(h)
                            }
                        }
                    }
                } else if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers.consts.full() {
                    Err(CheckError::Native(code_points(&M_E_CAP)))
                } else {
                    let d: u64 = self.der_of_const(pers, &r.n, &r.us);
                    let h: EIdx = EIdx::pack(ETAG_CONST, TIER_P, self.pers.consts.size() as u32);
                    self.pers.consts.push(r, d, h.dup2());
                    Ok(h)
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1656-1657 EStore.internApp` —
    /// `EStore.internApp`, the `app` arm of `EStore.intern`, over the node
    /// RECORD rather than over the view.
    ///
    /// The clauses are `intern`'s own, in `intern`'s order — the persistent
    /// probe (skipped when a child is scratch, `e_view_has_scratch_child`'s
    /// own arm), the scratch probe, the capacity test, the append — with the
    /// node record built ONCE and shared by all four.  See `intern`'s note.
    pub fn intern_app(&mut self, pers: &PersTier, f: EIdx, a: EIdx) -> Result<EIdx, CheckError> {
        let r: AppNode = AppNode { f, a };
        let sk: bool = if self.scratch_on {
            if r.f.is_persistent() {
                !r.a.is_persistent()
            } else {
                true
            }
        } else {
            false
        };
        let hit: Option<EIdx> = if sk {
            None
        } else if self.shared_on {
            pers.e.apps.find(&r)
        } else {
            self.pers.apps.find(&r)
        };
        match hit {
            Some(hp) => Ok(hp),
            None => {
                if self.scratch_on {
                    let at: (usize, Option<EIdx>) = self.scr.apps.find_slot(&r);
                    match at.1 {
                        Some(hs) => Ok(hs),
                        None => {
                            if self.scr.apps.full() {
                                Err(CheckError::Native(code_points(&M_E_CAP)))
                            } else {
                                let d: u64 = self.der_of_app(pers, &r.f, &r.a);
                                let h: EIdx =
                                    EIdx::pack(ETAG_APP, TIER_S, self.scr.apps.size() as u32);
                                self.scr.apps.push_at(at.0, r, d, h.dup2());
                                Ok(h)
                            }
                        }
                    }
                } else if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers.apps.full() {
                    Err(CheckError::Native(code_points(&M_E_CAP)))
                } else {
                    let d: u64 = self.der_of_app(pers, &r.f, &r.a);
                    let h: EIdx = EIdx::pack(ETAG_APP, TIER_P, self.pers.apps.size() as u32);
                    self.pers.apps.push(r, d, h.dup2());
                    Ok(h)
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1731-1735 EStore.internLam` —
    /// `EStore.internLam`, the `lam` arm of `EStore.intern`, over the node
    /// RECORD rather than over the view.
    ///
    /// The clauses are `intern`'s own, in `intern`'s order — the persistent
    /// probe (skipped when a child is scratch, `e_view_has_scratch_child`'s
    /// own arm), the scratch probe, the capacity test, the append — with the
    /// node record built ONCE and shared by all four.  See `intern`'s note.
    pub fn intern_lam(&mut self, pers: &PersTier, ty: EIdx, body: EIdx, m: BinderMeta) -> Result<EIdx, CheckError> {
        match self.intern_bm(pers, m) {
            Err(e) => Err(e),
            Ok(mi) => self.intern_lam_i(pers, ty, body, mi),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1723-1726 EStore.internLamI` —
    /// `EStore.internLamI`, the `lam` arm over a node record whose binder datum
    /// is already a HANDLE.
    ///
    /// This is the clause the rebuilding walks call: they take a binder apart
    /// with `view_bind_i` and put it back with this, so the datum is never
    /// decoded, never compared and never reference-counted on the way through
    /// — the record is three `u32`s of POD from end to end.  `intern_lam`
    /// is this with the datum interned first, which is what a caller that
    /// holds a `BinderMeta` (the parser, the modeller, a fresh binder) wants.
    pub fn intern_lam_i(&mut self, pers: &PersTier, ty: EIdx, body: EIdx, m: BMIdx) -> Result<EIdx, CheckError> {
        let r: BindNode = BindNode { ty, body, m };
        let sk: bool = if self.scratch_on {
            if r.ty.is_persistent() {
                if r.body.is_persistent() {
                    !r.m.is_persistent()
                } else {
                    true
                }
            } else {
                true
            }
        } else {
            false
        };
        let hit: Option<EIdx> = if sk {
            None
        } else if self.shared_on {
            pers.e.lams.find(&r)
        } else {
            self.pers.lams.find(&r)
        };
        match hit {
            Some(hp) => Ok(hp),
            None => {
                if self.scratch_on {
                    let at: (usize, Option<EIdx>) = self.scr.lams.find_slot(&r);
                    match at.1 {
                        Some(hs) => Ok(hs),
                        None => {
                            if self.scr.lams.full() {
                                Err(CheckError::Native(code_points(&M_E_CAP)))
                            } else {
                                let d: u64 = self.der_of_bind_at_i(pers, 19, &r.ty, &r.body, &r.m);
                                let h: EIdx =
                                    EIdx::pack(ETAG_LAM, TIER_S, self.scr.lams.size() as u32);
                                self.scr.lams.push_at(at.0, r, d, h.dup2());
                                Ok(h)
                            }
                        }
                    }
                } else if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers.lams.full() {
                    Err(CheckError::Native(code_points(&M_E_CAP)))
                } else {
                    let d: u64 = self.der_of_bind_at_i(pers, 19, &r.ty, &r.body, &r.m);
                    let h: EIdx = EIdx::pack(ETAG_LAM, TIER_P, self.pers.lams.size() as u32);
                    self.pers.lams.push(r, d, h.dup2());
                    Ok(h)
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1736-1740 EStore.internForallE` —
    /// `EStore.internForallE`, the `forall_e` arm of `EStore.intern`, over the
    /// node RECORD rather than over the view.
    ///
    /// The clauses are `intern`'s own, in `intern`'s order — the persistent
    /// probe (skipped when a child is scratch, `e_view_has_scratch_child`'s
    /// own arm), the scratch probe, the capacity test, the append — with the
    /// node record built ONCE and shared by all four.  See `intern`'s note.
    pub fn intern_forall_e(&mut self, pers: &PersTier, ty: EIdx, body: EIdx, m: BinderMeta) -> Result<EIdx, CheckError> {
        match self.intern_bm(pers, m) {
            Err(e) => Err(e),
            Ok(mi) => self.intern_forall_e_i(pers, ty, body, mi),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1727-1730 EStore.internForallEI` —
    /// `EStore.internForallEI`, the `forall_e` arm over a node record whose
    /// binder datum is already a HANDLE.
    ///
    /// This is the clause the rebuilding walks call: they take a binder apart
    /// with `view_bind_i` and put it back with this, so the datum is never
    /// decoded, never compared and never reference-counted on the way through
    /// — the record is three `u32`s of POD from end to end.  `intern_forall_e`
    /// is this with the datum interned first, which is what a caller that
    /// holds a `BinderMeta` (the parser, the modeller, a fresh binder) wants.
    pub fn intern_forall_e_i(&mut self, pers: &PersTier, ty: EIdx, body: EIdx, m: BMIdx) -> Result<EIdx, CheckError> {
        let r: BindNode = BindNode { ty, body, m };
        let sk: bool = if self.scratch_on {
            if r.ty.is_persistent() {
                if r.body.is_persistent() {
                    !r.m.is_persistent()
                } else {
                    true
                }
            } else {
                true
            }
        } else {
            false
        };
        let hit: Option<EIdx> = if sk {
            None
        } else if self.shared_on {
            pers.e.foralls.find(&r)
        } else {
            self.pers.foralls.find(&r)
        };
        match hit {
            Some(hp) => Ok(hp),
            None => {
                if self.scratch_on {
                    let at: (usize, Option<EIdx>) = self.scr.foralls.find_slot(&r);
                    match at.1 {
                        Some(hs) => Ok(hs),
                        None => {
                            if self.scr.foralls.full() {
                                Err(CheckError::Native(code_points(&M_E_CAP)))
                            } else {
                                let d: u64 = self.der_of_bind_at_i(pers, 23, &r.ty, &r.body, &r.m);
                                let h: EIdx =
                                    EIdx::pack(ETAG_FORALL_E, TIER_S, self.scr.foralls.size() as u32);
                                self.scr.foralls.push_at(at.0, r, d, h.dup2());
                                Ok(h)
                            }
                        }
                    }
                } else if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers.foralls.full() {
                    Err(CheckError::Native(code_points(&M_E_CAP)))
                } else {
                    let d: u64 = self.der_of_bind_at_i(pers, 23, &r.ty, &r.body, &r.m);
                    let h: EIdx = EIdx::pack(ETAG_FORALL_E, TIER_P, self.pers.foralls.size() as u32);
                    self.pers.foralls.push(r, d, h.dup2());
                    Ok(h)
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1656-1660 EStore.internLetE` —
    /// `EStore.internLetE`, the `let_e` arm of `EStore.intern`, over the node
    /// RECORD rather than over the view.
    ///
    /// The clauses are `intern`'s own, in `intern`'s order — the persistent
    /// probe (skipped when a child is scratch, `e_view_has_scratch_child`'s
    /// own arm), the scratch probe, the capacity test, the append — with the
    /// node record built ONCE and shared by all four.  See `intern`'s note.
    pub fn intern_let_e(&mut self, pers: &PersTier, ty: EIdx, val: EIdx, body: EIdx) -> Result<EIdx, CheckError> {
        let r: LetNode = LetNode { ty, val, body };
        let sk: bool = if self.scratch_on {
            if r.ty.is_persistent() {
                if r.val.is_persistent() {
                    !r.body.is_persistent()
                } else {
                    true
                }
            } else {
                true
            }
        } else {
            false
        };
        let hit: Option<EIdx> = if sk {
            None
        } else if self.shared_on {
            pers.e.lets.find(&r)
        } else {
            self.pers.lets.find(&r)
        };
        match hit {
            Some(hp) => Ok(hp),
            None => {
                if self.scratch_on {
                    let at: (usize, Option<EIdx>) = self.scr.lets.find_slot(&r);
                    match at.1 {
                        Some(hs) => Ok(hs),
                        None => {
                            if self.scr.lets.full() {
                                Err(CheckError::Native(code_points(&M_E_CAP)))
                            } else {
                                let d: u64 = self.der_of_let_at(pers, &r.ty, &r.val, &r.body);
                                let h: EIdx =
                                    EIdx::pack(ETAG_LET_E, TIER_S, self.scr.lets.size() as u32);
                                self.scr.lets.push_at(at.0, r, d, h.dup2());
                                Ok(h)
                            }
                        }
                    }
                } else if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers.lets.full() {
                    Err(CheckError::Native(code_points(&M_E_CAP)))
                } else {
                    let d: u64 = self.der_of_let_at(pers, &r.ty, &r.val, &r.body);
                    let h: EIdx = EIdx::pack(ETAG_LET_E, TIER_P, self.pers.lets.size() as u32);
                    self.pers.lets.push(r, d, h.dup2());
                    Ok(h)
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1661-1663 EStore.internLit` —
    /// `EStore.internLit`, the `lit` arm of `EStore.intern`, over the node
    /// RECORD rather than over the view.
    ///
    /// The clauses are `intern`'s own, in `intern`'s order — the persistent
    /// probe (skipped when a child is scratch, `e_view_has_scratch_child`'s
    /// own arm), the scratch probe, the capacity test, the append — with the
    /// node record built ONCE and shared by all four.  See `intern`'s note.
    pub fn intern_lit(&mut self, pers: &PersTier, l: Literal) -> Result<EIdx, CheckError> {
        let r: LitNode = LitNode { l };
        let sk: bool = false;
        let hit: Option<EIdx> = if sk {
            None
        } else if self.shared_on {
            pers.e.lits.find(&r)
        } else {
            self.pers.lits.find(&r)
        };
        match hit {
            Some(hp) => Ok(hp),
            None => {
                if self.scratch_on {
                    let at: (usize, Option<EIdx>) = self.scr.lits.find_slot(&r);
                    match at.1 {
                        Some(hs) => Ok(hs),
                        None => {
                            if self.scr.lits.full() {
                                Err(CheckError::Native(code_points(&M_E_CAP)))
                            } else {
                                let d: u64 = self.der_of_lit(&r.l);
                                let h: EIdx =
                                    EIdx::pack(ETAG_LIT, TIER_S, self.scr.lits.size() as u32);
                                self.scr.lits.push_at(at.0, r, d, h.dup2());
                                Ok(h)
                            }
                        }
                    }
                } else if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers.lits.full() {
                    Err(CheckError::Native(code_points(&M_E_CAP)))
                } else {
                    let d: u64 = self.der_of_lit(&r.l);
                    let h: EIdx = EIdx::pack(ETAG_LIT, TIER_P, self.pers.lits.size() as u32);
                    self.pers.lits.push(r, d, h.dup2());
                    Ok(h)
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin:
    /// `proof/ConRon/Arena/Store.lean:1664-1666 EStore.internProj` —
    /// `EStore.internProj`, the `proj` arm of `EStore.intern`, over the node
    /// RECORD rather than over the view.
    ///
    /// The clauses are `intern`'s own, in `intern`'s order — the persistent
    /// probe (skipped when a child is scratch, `e_view_has_scratch_child`'s
    /// own arm), the scratch probe, the capacity test, the append — with the
    /// node record built ONCE and shared by all four.  See `intern`'s note.
    pub fn intern_proj(&mut self, pers: &PersTier, n: NIdx, i: u64, e: EIdx) -> Result<EIdx, CheckError> {
        let r: ProjNode = ProjNode { n, i, e };
        let sk: bool = if self.scratch_on {
            if r.n.is_persistent() {
                !r.e.is_persistent()
            } else {
                true
            }
        } else {
            false
        };
        let hit: Option<EIdx> = if sk {
            None
        } else if self.shared_on {
            pers.e.projs.find(&r)
        } else {
            self.pers.projs.find(&r)
        };
        match hit {
            Some(hp) => Ok(hp),
            None => {
                if self.scratch_on {
                    let at: (usize, Option<EIdx>) = self.scr.projs.find_slot(&r);
                    match at.1 {
                        Some(hs) => Ok(hs),
                        None => {
                            if self.scr.projs.full() {
                                Err(CheckError::Native(code_points(&M_E_CAP)))
                            } else {
                                let d: u64 = self.der_of_proj(pers, &r.n, r.i, &r.e);
                                let h: EIdx =
                                    EIdx::pack(ETAG_PROJ, TIER_S, self.scr.projs.size() as u32);
                                self.scr.projs.push_at(at.0, r, d, h.dup2());
                                Ok(h)
                            }
                        }
                    }
                } else if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers.projs.full() {
                    Err(CheckError::Native(code_points(&M_E_CAP)))
                } else {
                    let d: u64 = self.der_of_proj(pers, &r.n, r.i, &r.e);
                    let h: EIdx = EIdx::pack(ETAG_PROJ, TIER_P, self.pers.projs.size() as u32);
                    self.pers.projs.push(r, d, h.dup2());
                    Ok(h)
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:523-526 EStore.enableScratch
    /// Open the scratch tier, in all four stores.  DESIGN.md §8.3: "each tier
    /// has its own array set and cons tables, both indexed from 0".
    pub fn enable_scratch(&mut self) {
        self.lss.enable_scratch();
        self.scr.reset();
        self.scratch_on = true;
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:528-531 EStore.dropScratch
    /// Drop the scratch tier, in all four stores.  Persistent handles keep
    /// their bits, so everything that denoted before still denotes (DESIGN.md
    /// §8.3, con-leche's lesson 6).
    pub fn drop_scratch(&mut self) {
        self.lss.drop_scratch();
        self.scr.reset();
        self.scratch_on = false;
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:533-537 EStore.capOK
    pub fn cap_ok(&self, pers: &PersTier, v: &ENodeView) -> bool {
        if self.scratch_on {
            !self.scr.full_of(v)
        } else {
            !self.pers_full_of(pers, v)
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1813-1818 EStore.internName
    /// Intern a name from the expression store.
    pub fn intern_name(&mut self, pers: &PersTier, v: NNodeView) -> Result<NIdx, CheckError> {
        self.lss.intern_name(pers, v)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1820-1825 EStore.internLevel
    /// Intern a level from the expression store.
    pub fn intern_level(&mut self, pers: &PersTier, v: LNodeView) -> Result<LIdx, CheckError> {
        self.lss.intern_level(pers, v)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1827-1834 EStore.internLevels
    /// Intern a universe-argument list from the expression store.
    pub fn intern_levels(&mut self, pers: &PersTier, v: LsNodeView) -> Result<LsIdx, CheckError> {
        self.lss.intern(pers, v)
    }
}

// ---------------------------------------------------------------------------
// Interning into the PERSISTENT tier while the scratch tier is on
// (`Store.lean:1125-1298`, task #97-P6-2 — ADDITIVE: nothing above moves)
// ---------------------------------------------------------------------------
//
// DESIGN.md §8.3, "Phase A runs in the scratch tier too, with promotion": the
// install phase opens the scratch tier exactly as phase B does, and the
// handles the environment KEEPS are **promoted** before the tier is dropped —
// a memoised structural copy scratch → persistent (`arena::promote`).  The
// copy's target is the persistent tier while the scratch tier is still live,
// and `intern` cannot say that: it appends to the tier the store is IN.  So
// each store gets a twin of `intern`'s `else` branch, and nothing else about
// the store changes.
//
// **The probe order is `intern`'s own, minus the scratch probe**: the
// persistent cons table first, and an entry found there is the answer — so a
// node the parse already interned promotes to ITSELF, and a node promoted once
// is never duplicated.  The scratch table is deliberately NOT probed: a hit
// there would hand back a SCRATCH handle, which is the one thing the promotion
// exists to get rid of.
//
// The capacity test is `intern`'s, against the PERSISTENT array and with the
// same `Native` decline; `cap_ok_persistent` mirrors the twin's `Prop`
// `capOKPersistent` as the `bool` its `capOK` already is here.  The WF
// obligations — the added `childOK` precondition ("the view's children are
// persistent") and the transient `fresh` exception the bracket repairs — are
// the twin's section note, and P3's.

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1880-1891 NStore.internPersistent
/// The name store's promote-intern.
impl NStore {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1880-1891 NStore.internPersistent
    /// Hash-cons a name node into the PERSISTENT tier whatever tier the store
    /// is in: `intern`'s `else` branch, verbatim, with no scratch probe.
    pub fn intern_persistent(&mut self, pers: &PersTier, v: NNodeView) -> Result<NIdx, CheckError> {
        match self.pers_find(pers, &v) {
            Some(i) => Ok(i),
            None => {
                if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers_full_of(pers, &v) {
                    Err(CheckError::Native(code_points(&M_N_CAP)))
                } else {
                    let d = self.der_of_view(pers, &v);
                    Ok(self.pers.push(v, d, TIER_P))
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1893-1896 NStore.capOKPersistent
    /// `intern_persistent`'s capacity precondition, as a test rather than a
    /// `Prop`: the constructor's PERSISTENT array has room for one more node.
    pub fn cap_ok_persistent(&self, pers: &PersTier, v: &NNodeView) -> bool {
        !self.pers_full_of(pers, v)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1898-1908 LStore.internPersistent
/// The level store's promote-intern, and the name lift through it.
impl LStore {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1898-1908 LStore.internPersistent
    /// Hash-cons a level node into the persistent tier.
    pub fn intern_persistent(&mut self, pers: &PersTier, v: LNodeView) -> Result<LIdx, CheckError> {
        match self.pers_find(pers, &v) {
            Some(i) => Ok(i),
            None => {
                if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers_full_of(pers, &v) {
                    Err(CheckError::Native(code_points(&M_L_CAP)))
                } else {
                    let d = self.der_of_view(pers, &v);
                    Ok(self.pers.push(v, d, TIER_P))
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1910-1913 LStore.capOKPersistent
    /// The level store's capacity precondition for `intern_persistent`.
    pub fn cap_ok_persistent(&self, pers: &PersTier, v: &LNodeView) -> bool {
        !self.pers_full_of(pers, v)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1996-2003 LStore.internNamePersistent
    /// Promote-intern a name from the level store.
    pub fn intern_name_persistent(
        &mut self,
        pers: &PersTier,
        v: NNodeView,
    ) -> Result<NIdx, CheckError>  {
        self.ns.intern_persistent(pers, v)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1915-1925 LsStore.internPersistent
/// The level-list store's promote-intern, and the two lifts through it.
impl LsStore {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1915-1925 LsStore.internPersistent
    /// Hash-cons a level list into the persistent tier.
    pub fn intern_persistent(
        &mut self,
        pers: &PersTier,
        v: LsNodeView,
    ) -> Result<LsIdx, CheckError>  {
        match self.pers_find(pers, &v) {
            Some(i) => Ok(i),
            None => {
                if self.shared_on {
                    Err(CheckError::Native(code_points(&M_FROZEN)))
                } else if self.pers_full_of(pers, &v) {
                    Err(CheckError::Native(code_points(&M_LS_CAP)))
                } else {
                    let d = self.der_of_view(pers, &v);
                    Ok(self.pers.push(v, d, TIER_P))
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1927-1930 LsStore.capOKPersistent
    /// The level-list store's capacity precondition for `intern_persistent`.
    pub fn cap_ok_persistent(&self, pers: &PersTier, v: &LsNodeView) -> bool {
        !self.pers_full_of(pers, v)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:2005-2012 LsStore.internNamePersistent
    /// Promote-intern a name from the level-list store.
    pub fn intern_name_persistent(
        &mut self,
        pers: &PersTier,
        v: NNodeView,
    ) -> Result<NIdx, CheckError>  {
        self.ls.intern_name_persistent(pers, v)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:2014-2021 LsStore.internLevelPersistent
    /// Promote-intern a level from the level-list store.
    pub fn intern_level_persistent(
        &mut self,
        pers: &PersTier,
        v: LNodeView,
    ) -> Result<LIdx, CheckError>  {
        self.ls.intern_persistent(pers, v)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1932-1943 EStore.internPersistent
/// The expression store's promote-intern, and the three lifts through it.
impl EStore {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1932-1943 EStore.internPersistent
    /// Hash-cons an expression node into the persistent tier whatever tier the
    /// store is in.
    pub fn intern_persistent(&mut self, pers: &PersTier, v: ENodeView) -> Result<EIdx, CheckError> {
        match self.intern_bm_of_view_persistent(pers, &v) {
            Err(e) => Err(e),
            Ok(mi) => match self.pers_find(pers, &v, &mi) {
                Some(i) => Ok(i),
                None => {
                    if self.shared_on {
                        Err(CheckError::Native(code_points(&M_FROZEN)))
                    } else if self.pers_full_of(pers, &v) {
                        Err(CheckError::Native(code_points(&M_E_CAP)))
                    } else {
                        let d = self.der_of_view(pers, &v);
                        Ok(self.pers.push(v, d, mi, TIER_P))
                    }
                }
            },
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1983-1988 EStore.capOKPersistent
    /// The expression store's capacity precondition for `intern_persistent`.
    pub fn cap_ok_persistent(&self, pers: &PersTier, v: &ENodeView) -> bool {
        !self.pers_full_of(pers, v)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:2023-2030 EStore.internNamePersistent
    /// Promote-intern a name from the expression store.
    pub fn intern_name_persistent(
        &mut self,
        pers: &PersTier,
        v: NNodeView,
    ) -> Result<NIdx, CheckError>  {
        self.lss.intern_name_persistent(pers, v)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:2032-2039 EStore.internLevelPersistent
    /// Promote-intern a level from the expression store.
    pub fn intern_level_persistent(
        &mut self,
        pers: &PersTier,
        v: LNodeView,
    ) -> Result<LIdx, CheckError>  {
        self.lss.intern_level_persistent(pers, v)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:2041-2048 EStore.internLevelsPersistent
    /// Promote-intern a universe-argument list from the expression store.
    pub fn intern_levels_persistent(
        &mut self,
        pers: &PersTier,
        v: LsNodeView,
    ) -> Result<LsIdx, CheckError>  {
        self.lss.intern_persistent(pers, v)
    }
}

// ---------------------------------------------------------------------------
// Tests: `proof/ConRon/Arena/StoreTest.lean`'s forty-four `#guard`s
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::expr::Expr;
    use crate::kernel::level;
    use crate::kernel::level::Level;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::ron::nat;

    /// `Result::unwrap` needs `E: Debug`, and `CheckError` deliberately has
    /// none (DESIGN.md §3.4: no `derive(Debug)` on the core types).  This is
    /// the tests' `unwrap`.
    fn ok<T>(r: Result<T, CheckError>) -> T {
        match r {
            Ok(x) => x,
            Err(_) => panic!("the store declined a node the test expected it to take"),
        }
    }

    /// `"foo"` as the `Vec<u32>` of code points every string in the verified
    /// core is (DESIGN.md §3.3).
    fn cp(s: &str) -> Vec<u32> {
        s.chars().map(|c| c as u32).collect()
    }

    // --- the readback (`Denote.lean`), test-only -----------------------------
    //
    // `Denote`, `WF` and `WFProofs` are the arena's own verification (DESIGN.md
    // §8.6's P2a) and have no place in the shipped crate — but a `#guard` that
    // says `denoteE fst hAp == some eAp` cannot be mirrored without a readback.
    // These four functions are `Denote.lean`'s, fuel and all, and they live
    // here and nowhere else.

    fn denote_n_aux(st: &NStore, fuel: u64, i: &NIdx) -> Option<Name> {
        let pers: &PersTier = &PersTier::empty();
        if fuel == 0 {
            return None;
        }
        match st.view(pers, i) {
            None => None,
            Some(NNodeView::Anonymous) => Some(name::anonymous()),
            Some(NNodeView::Str(p, s)) => {
                denote_n_aux(st, fuel - 1, &p).map(|q| name::mk_str(q, s))
            }
            Some(NNodeView::Num(p, n)) => {
                denote_n_aux(st, fuel - 1, &p).map(|q| name::mk_num(q, n))
            }
        }
    }

    fn denote_n(st: &NStore, i: &NIdx) -> Option<Name> {
        let pers: &PersTier = &PersTier::empty();
        denote_n_aux(st, st.node_count(pers) as u64 + 1, i)
    }

    fn denote_l_aux(st: &LStore, fuel: u64, i: &LIdx) -> Option<Level> {
        let pers: &PersTier = &PersTier::empty();
        if fuel == 0 {
            return None;
        }
        match st.view(pers, i) {
            None => None,
            Some(LNodeView::Zero) => Some(level::zero()),
            Some(LNodeView::Succ(u)) => denote_l_aux(st, fuel - 1, &u).map(level::succ),
            Some(LNodeView::Max(u, v)) => {
                match (denote_l_aux(st, fuel - 1, &u), denote_l_aux(st, fuel - 1, &v)) {
                    (Some(a), Some(b)) => Some(level::max(a, b)),
                    _ => None,
                }
            }
            Some(LNodeView::Imax(u, v)) => {
                match (denote_l_aux(st, fuel - 1, &u), denote_l_aux(st, fuel - 1, &v)) {
                    (Some(a), Some(b)) => Some(level::imax(a, b)),
                    _ => None,
                }
            }
            Some(LNodeView::Param(n)) => denote_n(&st.ns, &n).map(level::param),
        }
    }

    fn denote_l(st: &LStore, i: &LIdx) -> Option<Level> {
        let pers: &PersTier = &PersTier::empty();
        denote_l_aux(st, st.node_count(pers) as u64 + 1, i)
    }

    fn denote_ls(st: &LsStore, i: &LsIdx) -> Option<Vec<Level>> {
        let pers: &PersTier = &PersTier::empty();
        match st.view(pers, i) {
            None => None,
            Some(us) => {
                let mut out: Vec<Level> = Vec::new();
                for u in us.iter() {
                    match denote_l(&st.ls, u) {
                        None => return None,
                        Some(l) => out.push(l),
                    }
                }
                Some(out)
            }
        }
    }

    fn denote_e_aux(st: &EStore, fuel: u64, i: &EIdx) -> Option<Expr> {
        let pers: &PersTier = &PersTier::empty();
        if fuel == 0 {
            return None;
        }
        match st.view(pers, i) {
            None => None,
            Some(ENodeView::BVar(k)) => Some(expr::bvar(k)),
            Some(ENodeView::FVar(k, ty)) => {
                denote_e_aux(st, fuel - 1, &ty).map(|t| expr::fvar(k, t))
            }
            Some(ENodeView::Sort(u)) => denote_l(st.ls(), &u).map(expr::sort),
            Some(ENodeView::Const(n, us)) => {
                match (denote_n(st.ns(), &n), denote_ls(st.ls_s(), &us)) {
                    (Some(a), Some(b)) => Some(expr::mk_const(a, b)),
                    _ => None,
                }
            }
            Some(ENodeView::App(g, a)) => {
                match (denote_e_aux(st, fuel - 1, &g), denote_e_aux(st, fuel - 1, &a)) {
                    (Some(x), Some(y)) => Some(expr::app(x, y)),
                    _ => None,
                }
            }
            Some(ENodeView::Lam(ty, b, m)) => {
                match (denote_e_aux(st, fuel - 1, &ty), denote_e_aux(st, fuel - 1, &b)) {
                    (Some(x), Some(y)) => Some(expr::lam(x, y, m)),
                    _ => None,
                }
            }
            Some(ENodeView::ForallE(ty, b, m)) => {
                match (denote_e_aux(st, fuel - 1, &ty), denote_e_aux(st, fuel - 1, &b)) {
                    (Some(x), Some(y)) => Some(expr::forall_e(x, y, m)),
                    _ => None,
                }
            }
            Some(ENodeView::LetE(ty, v, b)) => match (
                denote_e_aux(st, fuel - 1, &ty),
                denote_e_aux(st, fuel - 1, &v),
                denote_e_aux(st, fuel - 1, &b),
            ) {
                (Some(x), Some(y), Some(z)) => Some(expr::let_e(x, y, z)),
                _ => None,
            },
            Some(ENodeView::Lit(l)) => Some(expr::lit(l)),
            Some(ENodeView::Proj(n, k, e)) => {
                match (denote_n(st.ns(), &n), denote_e_aux(st, fuel - 1, &e)) {
                    (Some(s), Some(x)) => Some(expr::proj(s, k, x)),
                    _ => None,
                }
            }
        }
    }

    fn denote_e(st: &EStore, i: &EIdx) -> Option<Expr> {
        let pers: &PersTier = &PersTier::empty();
        denote_e_aux(st, st.node_count(pers) as u64 + 1, i)
    }

    // --- helpers -------------------------------------------------------------

    fn eq_e(a: &Option<Expr>, b: &Expr) -> bool {
        match a {
            None => false,
            Some(x) => expr::beq(x, b),
        }
    }

    fn eq_n(a: &Option<Name>, b: &Name) -> bool {
        match a {
            None => false,
            Some(x) => name::beq(x, b),
        }
    }

    /// Structural equality of the four `ENodeView` shapes the `#guard`s
    /// compare (the Lean gets it from `deriving DecidableEq`).
    fn view_eq(a: &Option<ENodeView>, b: &Option<ENodeView>) -> bool {
        match (a, b) {
            (None, None) => true,
            (Some(x), Some(y)) => match (x, y) {
                (ENodeView::BVar(i), ENodeView::BVar(j)) => i == j,
                (ENodeView::Sort(u), ENodeView::Sort(v)) => u.word == v.word,
                (ENodeView::Const(n, us), ENodeView::Const(m, vs)) => {
                    n.word == m.word && us.word == vs.word
                }
                (ENodeView::App(f, a2), ENodeView::App(g, b2)) => {
                    f.word == g.word && a2.word == b2.word
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// `StoreTest.lean:28-40 fixture`: `Sort 0`, `Sort 1`, the name `foo`,
    /// `foo.{0}` and an application, interned into the persistent tier, in the
    /// order the parser would.
    fn fixture() -> (EStore, LIdx, LIdx, NIdx, LsIdx, EIdx, EIdx, EIdx, EIdx) {
        let pers: &PersTier = &PersTier::empty();
        let mut st = EStore::empty();
        let z = ok(st.intern_level(pers, LNodeView::Zero));
        let one = ok(st.intern_level(pers, LNodeView::Succ(z.dup2())));
        let anon = ok(st.intern_name(pers, NNodeView::Anonymous));
        let foo = ok(st.intern_name(pers, NNodeView::Str(anon.dup2(), cp("foo"))));
        let us = ok(st.intern_levels(pers, vec![z.dup2()]));
        let s0 = ok(st.intern(pers, ENodeView::Sort(z.dup2())));
        let s1 = ok(st.intern(pers, ENodeView::Sort(one.dup2())));
        let c = ok(st.intern(pers, ENodeView::Const(foo.dup2(), us.dup2())));
        let ap = ok(st.intern(pers, ENodeView::App(c.dup2(), s0.dup2())));
        (st, z, one, foo, us, s0, s1, c, ap)
    }

    // The con-leche values the fixture's handles are supposed to denote
    // (`StoreTest.lean:49-53`), built by `con-ron-core`'s smart constructors.

    fn e_s0() -> Expr {
        expr::sort(level::zero())
    }

    fn e_s1() -> Expr {
        expr::sort(level::succ(level::zero()))
    }

    fn n_foo() -> Name {
        name::mk_str(name::anonymous(), cp("foo"))
    }

    fn e_c() -> Expr {
        expr::mk_const(n_foo(), vec![level::zero()])
    }

    fn e_ap() -> Expr {
        expr::app(e_c(), e_s0())
    }

    // --- `StoreTest.lean:55-62`: the handle layout round-trips ---------------

    #[test]
    fn handle_layout_round_trips() {
        let (_st, _z, _one, _foo, _us, s0, s1, c, ap) = fixture();
        assert_eq!(s0.tag(), ETAG_SORT); // #guard 1
        assert_eq!(ap.tag(), ETAG_APP); // #guard 2
        assert_eq!(c.tag(), ETAG_CONST); // #guard 3
        assert!(s0.is_persistent()); // #guard 4
        assert!(ap.is_persistent()); // #guard 5
        assert_eq!(s0.index(), 0); // #guard 6
        assert_eq!(s1.index(), 1); // #guard 7
    }

    // --- `StoreTest.lean:64-77`: interning is hash-consing -------------------

    #[test]
    fn interning_is_hash_consing() {
        let pers: &PersTier = &PersTier::empty();
        let (mut st, z, one, foo, _us, s0, _s1, c, ap) = fixture();

        // #guard 8: the same node interned twice gives the same handle.
        let a = ok(st.intern(pers, ENodeView::App(c.dup2(), s0.dup2())));
        let b = ok(st.intern(pers, ENodeView::App(c.dup2(), s0.dup2())));
        assert_eq!(a.word, b.word);
        assert_eq!(a.word, ap.word);

        // #guard 9
        let a = ok(st.intern(pers, ENodeView::Sort(z.dup2())));
        assert_eq!(a.word, s0.word);

        // #guard 10
        let a = ok(st.intern_level(pers, LNodeView::Succ(z.dup2())));
        assert_eq!(a.word, one.word);

        // #guard 11
        let anon = ok(st.intern_name(pers, NNodeView::Anonymous));
        let a = ok(st.intern_name(pers, NNodeView::Str(anon, cp("foo"))));
        assert_eq!(a.word, foo.word);
    }

    // --- `StoreTest.lean:79-91`: cross-tier dedup ----------------------------

    #[test]
    fn cross_tier_dedup() {
        let pers: &PersTier = &PersTier::empty();
        // #guard 12: a persistent node is never re-interned into scratch.
        let (mut st, _z, _one, _foo, _us, s0, _s1, c, ap) = fixture();
        st.enable_scratch();
        let a = ok(st.intern(pers, ENodeView::App(c.dup2(), s0.dup2())));
        assert_eq!(a.word, ap.word);
        assert!(a.is_persistent());

        // #guard 13: a genuinely new node lands in scratch, and dedups there.
        let a = ok(st.intern(pers, ENodeView::App(s0.dup2(), s0.dup2())));
        let b = ok(st.intern(pers, ENodeView::App(s0.dup2(), s0.dup2())));
        assert_eq!(a.word, b.word);
        assert!(!a.is_persistent());
    }

    // --- `StoreTest.lean:93-97`: `view` decodes what was interned ------------

    #[test]
    fn view_decodes_what_was_interned() {
        let pers: &PersTier = &PersTier::empty();
        let (st, z, _one, foo, us, s0, _s1, c, ap) = fixture();
        // #guard 14
        assert!(view_eq(&st.view(pers, &ap), &Some(ENodeView::App(c.dup2(), s0.dup2()))));
        // #guard 15
        assert!(view_eq(&st.view(pers, &s0), &Some(ENodeView::Sort(z.dup2()))));
        // #guard 16
        assert!(view_eq(&st.view(pers, &c), &Some(ENodeView::Const(foo.dup2(), us.dup2()))));
    }

    // --- `StoreTest.lean:99-107`: the denotation is con-leche's own value ----

    #[test]
    fn denotation_is_con_leches_own_value() {
        let (st, _z, _one, foo, us, s0, s1, c, ap) = fixture();
        assert!(eq_e(&denote_e(&st, &s0), &e_s0())); // #guard 17
        assert!(eq_e(&denote_e(&st, &s1), &e_s1())); // #guard 18
        assert!(eq_e(&denote_e(&st, &c), &e_c())); // #guard 19
        assert!(eq_e(&denote_e(&st, &ap), &e_ap())); // #guard 20
        assert!(eq_n(&denote_n(st.ns(), &foo), &n_foo())); // #guard 21

        // #guard 22
        let ls = denote_ls(st.ls_s(), &us).unwrap();
        assert_eq!(ls.len(), 1);
        assert!(level::beq(&ls[0], &level::zero()));
    }

    // --- `StoreTest.lean:109-123`: the derived column IS `Expr.data` ---------

    #[test]
    fn derived_column_is_expr_data() {
        let pers: &PersTier = &PersTier::empty();
        let (st, z, one, foo, us, s0, s1, c, ap) = fixture();
        assert_eq!(st.derived(pers, &s0), expr::data(&e_s0())); // #guard 23
        assert_eq!(st.derived(pers, &s1), expr::data(&e_s1())); // #guard 24
        assert_eq!(st.derived(pers, &c), expr::data(&e_c())); // #guard 25
        assert_eq!(st.derived(pers, &ap), expr::data(&e_ap())); // #guard 26
        assert_eq!(st.ns().derived(pers, &foo), name::hash_data(&n_foo())); // #guard 27
        assert_eq!(st.ls().derived(pers, &z).hash, level::hash_data(&level::zero())); // #guard 28
        // #guard 29
        assert_eq!(
            st.ls().derived(pers, &one).hash,
            level::hash_data(&level::succ(level::zero()))
        );
        // #guard 30
        assert_eq!(st.lss.derived(pers, &us).hash, level::levels_hash(&vec![level::zero()]));
        // #guard 31
        assert_eq!(
            st.lss.derived(pers, &us).has_param,
            level::levels_have_param(&vec![level::zero()])
        );
    }

    // --- `StoreTest.lean:125-140`: a binder, a bvar, the range fields --------

    #[test]
    fn binder_and_bvar_exercise_the_range_fields() {
        let pers: &PersTier = &PersTier::empty();
        let (mut st, _z, _one, _foo, _us, s0, _s1, _c, _ap) = fixture();
        let b0 = ok(st.intern(pers, ENodeView::BVar(0)));
        let lam = ok(st.intern(pers, ENodeView::Lam(
            s0.dup2(),
            b0.dup2(),
            expr::binder_meta(prop_when::never()),
        )));
        let e_b0 = expr::bvar(0);
        let e_lam = expr::lam(e_s0(), expr::bvar(0), expr::binder_meta(prop_when::never()));
        assert!(eq_e(&denote_e(&st, &b0), &e_b0)); // #guard 32
        assert!(eq_e(&denote_e(&st, &lam), &e_lam)); // #guard 33
        assert_eq!(st.derived(pers, &b0), expr::data(&e_b0)); // #guard 34
        assert_eq!(st.derived(pers, &lam), expr::data(&e_lam)); // #guard 35
    }

    // --- `StoreTest.lean:142-167`: the `dropScratch` bracket -----------------

    #[test]
    fn drop_scratch_invalidates_scratch_and_keeps_persistent() {
        let pers: &PersTier = &PersTier::empty();
        let (mut st, _z, _one, _foo, _us, s0, _s1, _c, ap) = fixture();
        let pers_view_ap = st.view(pers, &ap);
        st.enable_scratch();
        let scr = ok(st.intern(pers, ENodeView::App(s0.dup2(), s0.dup2())));

        assert!(!scr.is_persistent()); // #guard 36
        assert!(eq_e(&denote_e(&st, &scr), &expr::app(e_s0(), e_s0()))); // #guard 37
        assert!(eq_e(&denote_e(&st, &ap), &e_ap())); // #guard 38

        st.drop_scratch();
        assert!(denote_e(&st, &scr).is_none()); // #guard 39
        assert!(st.view(pers, &scr).is_none()); // #guard 40
        assert!(eq_e(&denote_e(&st, &ap), &e_ap())); // #guard 41
        assert!(view_eq(&st.view(pers, &ap), &pers_view_ap)); // #guard 42
        assert!(!st.scratch_on); // #guard 43
    }

    /// `StoreTest.lean:165-167`: a persistent handle's *bits* are unchanged by
    /// the bracket — the point of putting the tier bit above the index.
    #[test]
    fn a_persistent_handles_bits_survive_the_bracket() {
        let pers: &PersTier = &PersTier::empty();
        let (mut st, z, _one, _foo, _us, s0, _s1, _c, _ap) = fixture();
        st.enable_scratch();
        let a = ok(st.intern(pers, ENodeView::Sort(z.dup2())));
        assert_eq!(a.word, s0.word); // #guard 44
    }

    // --- beyond the twin ----------------------------------------------------

    /// `StoreTest.lean` exercises `sort`, `const`, `app`, `bvar` and `lam`.
    /// The other five expression arms, the `num` name arm and the
    /// `max`/`imax`/`param` level arms get the same treatment here, so that
    /// every `der_of_view` formula is checked against `expr::data` (or
    /// `name::hash_data` / `level::hash_data`) of the tree the same smart
    /// constructors build.  An addition the Rust side can afford because
    /// `cargo test` is cheaper than kernel reduction.
    #[test]
    fn every_der_of_view_arm_agrees_with_con_ron_cores_own() {
        let pers: &PersTier = &PersTier::empty();
        let (mut st, z, _one, foo, _us, s0, _s1, _c, _ap) = fixture();

        let fv = ok(st.intern(pers, ENodeView::FVar(3, s0.dup2())));
        let e_fv = expr::fvar(3, e_s0());
        assert!(eq_e(&denote_e(&st, &fv), &e_fv));
        assert_eq!(st.derived(pers, &fv), expr::data(&e_fv));

        let b0 = ok(st.intern(pers, ENodeView::BVar(0)));
        let fa = ok(st.intern(pers, ENodeView::ForallE(
            s0.dup2(),
            b0.dup2(),
            expr::binder_meta(prop_when::never()),
        )));
        let e_fa = expr::forall_e(e_s0(), expr::bvar(0), expr::binder_meta(prop_when::never()));
        assert!(eq_e(&denote_e(&st, &fa), &e_fa));
        assert_eq!(st.derived(pers, &fa), expr::data(&e_fa));

        let le = ok(st.intern(pers, ENodeView::LetE(s0.dup2(), s0.dup2(), b0.dup2())));
        let e_le = expr::let_e(e_s0(), e_s0(), expr::bvar(0));
        assert!(eq_e(&denote_e(&st, &le), &e_le));
        assert_eq!(st.derived(pers, &le), expr::data(&e_le));

        let li = ok(st.intern(pers, ENodeView::Lit(expr::literal_nat(nat::from_u64(7)))));
        let e_li = expr::lit(expr::literal_nat(nat::from_u64(7)));
        assert!(eq_e(&denote_e(&st, &li), &e_li));
        assert_eq!(st.derived(pers, &li), expr::data(&e_li));

        let pj = ok(st.intern(pers, ENodeView::Proj(foo.dup2(), 1, s0.dup2())));
        let e_pj = expr::proj(n_foo(), 1, e_s0());
        assert!(eq_e(&denote_e(&st, &pj), &e_pj));
        assert_eq!(st.derived(pers, &pj), expr::data(&e_pj));

        let anon = ok(st.intern_name(pers, NNodeView::Anonymous));
        let n7 = ok(st.intern_name(pers, NNodeView::Num(anon.dup2(), 7)));
        let e_n7 = name::mk_num(name::anonymous(), 7);
        assert!(eq_n(&denote_n(st.ns(), &n7), &e_n7));
        assert_eq!(st.ns().derived(pers, &n7), name::hash_data(&e_n7));

        let p = ok(st.intern_level(pers, LNodeView::Param(foo.dup2())));
        let mx = ok(st.intern_level(pers, LNodeView::Max(z.dup2(), p.dup2())));
        let im = ok(st.intern_level(pers, LNodeView::Imax(z.dup2(), p.dup2())));
        let e_p = level::param(n_foo());
        let e_mx = level::max(level::zero(), level::param(n_foo()));
        let e_im = level::imax(level::zero(), level::param(n_foo()));
        assert_eq!(st.ls().derived(pers, &p).hash, level::hash_data(&e_p));
        assert!(st.ls().derived(pers, &p).has_param);
        assert_eq!(st.ls().derived(pers, &mx).hash, level::hash_data(&e_mx));
        assert_eq!(st.ls().derived(pers, &mx).has_param, level::level_has_param(&e_mx));
        assert_eq!(st.ls().derived(pers, &im).hash, level::hash_data(&e_im));
        assert_eq!(st.ls().derived(pers, &im).has_param, level::level_has_param(&e_im));

        // a two-element universe list, so `der_of_view_from` recurses
        let us2 = ok(st.intern_levels(pers, vec![z.dup2(), p.dup2()]));
        let e_us2 = vec![level::zero(), level::param(n_foo())];
        assert_eq!(st.lss.derived(pers, &us2).hash, level::levels_hash(&e_us2));
        assert_eq!(st.lss.derived(pers, &us2).has_param, level::levels_have_param(&e_us2));
    }

    /// The tier bit is what separates the two array sets: each tier is indexed
    /// from zero, and `enable_scratch` empties the scratch tier again.
    #[test]
    fn the_two_tiers_are_indexed_from_zero_independently() {
        let pers: &PersTier = &PersTier::empty();
        let (mut st, _z, _one, _foo, _us, s0, _s1, _c, _ap) = fixture();
        st.enable_scratch();
        let scr = ok(st.intern(pers, ENodeView::BVar(0)));
        assert!(!scr.is_persistent());
        assert_eq!(scr.index(), 0);
        assert_eq!(scr.tag(), ETAG_BVAR);
        assert_eq!(s0.index(), 0);
        assert_ne!(scr.word, s0.word);
        st.enable_scratch();
        assert!(st.view(pers, &scr).is_none());
        assert_eq!(st.scr_count(), 0);
    }

    /// `find` is `intern` without the append: it misses before, hits after, and
    /// `node_count` counts exactly what was appended.
    #[test]
    fn find_agrees_with_intern_and_node_count_counts() {
        let pers: &PersTier = &PersTier::empty();
        let (mut st, _z, _one, _foo, _us, s0, _s1, _c, _ap) = fixture();
        let before = st.node_count(pers);
        assert!(st.find(pers, &ENodeView::App(s0.dup2(), s0.dup2())).is_none());
        assert!(st.cap_ok(pers, &ENodeView::App(s0.dup2(), s0.dup2())));
        let h = ok(st.intern(pers, ENodeView::App(s0.dup2(), s0.dup2())));
        assert_eq!(st.node_count(pers), before + 1);
        match st.find(pers, &ENodeView::App(s0.dup2(), s0.dup2())) {
            None => panic!("an interned node was not found"),
            Some(g) => assert_eq!(g.word, h.word),
        }
        // interning it again appends nothing
        let h2 = ok(st.intern(pers, ENodeView::App(s0.dup2(), s0.dup2())));
        assert_eq!(h2.word, h.word);
        assert_eq!(st.node_count(pers), before + 1);
    }
}

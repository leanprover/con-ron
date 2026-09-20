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

use con_ron_core::kernel::core_types::code_points;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::BinderMeta;
use con_ron_core::kernel::expr::Literal;
use con_ron_core::kernel::name;
use con_ron_core::kernel::prop_when;
use con_ron_core::ron::hashmap::Dup;
use con_ron_core::ron::hashmap::Eq2;
use con_ron_core::ron::hashmap::HashMap;
use con_ron_core::ron::hashmap::Hashable;
use std::vec::Vec;

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

/// con-leche: none — the port's own `Native` decline, which con-leche cannot raise (DESIGN.md §3.4, task #67)
/// `"arena: expr constructor at capacity"`, as code points.
const M_E_CAP: [u32; 36] = [
    97, 114, 101, 110, 97, 58, 32, 101, 120, 112, 114, 32, 99, 111, 110, 115, 116, 114, 117, 99,
    116, 111, 114, 32, 97, 116, 32, 99, 97, 112, 97, 99, 105, 116, 121, 10,
];

// ---------------------------------------------------------------------------
// The generic interned table (`Store.lean:53-105`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:87-88 Tbl.derAt
/// The `[Inhabited δ]` of the Lean's `Tbl.derAt`: the derived word a read
/// past the end of the column answers with.  The range is a `StoreWF` clause,
/// so the fallback is never taken on a well-formed store; it exists because
/// `derAt` is total.  Spelled as the crate's own one-method trait rather than
/// `core::default::Default`, for the reason `ron::hashmap::Eq2` gives.
pub trait DerDefault {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:87-88 Tbl.derAt
    /// The value `derAt` answers with out of range.
    fn der_default() -> Self;
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:87-88 Tbl.derAt
/// The name and expression columns are a bare `u64`, whose `Inhabited` is `0`.
impl DerDefault for u64 {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:87-88 Tbl.derAt
    fn der_default() -> u64 {
        0
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:64-71 Tbl
/// nanoda's `UniqueIndexSet<A>` (`util.rs:28-33`) with con-leche's parallel
/// derived array beside it (lesson 1: derived data never lives inside the
/// cons key).  One constructor's array of one tier: the node records, the
/// parallel derived words, and the cons table from record to handle.
pub struct Tbl<A, I, D> {
    pub nodes: Vec<A>,
    pub der: Vec<D>,
    pub cons: HashMap<A, I>,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:69-100 Tbl
/// The six operations of the Lean's `Tbl` namespace.  One `impl` with every
/// bound, rather than the Lean's `variable` block plus per-`def` instance
/// arguments: all seventeen instantiations satisfy all three bounds.
impl<A, I, D> Tbl<A, I, D>
where
    A: Hashable + Eq2 + Dup,
    I: Dup,
    D: Dup + DerDefault,
{
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:74 Tbl.empty
    pub fn empty() -> Tbl<A, I, D> {
        Tbl { nodes: Vec::new(), der: Vec::new(), cons: HashMap::new() }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:79 Tbl.size
    /// How many nodes this constructor has in this tier.
    pub fn size(&self) -> usize {
        self.nodes.len()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:82 Tbl.node?
    /// Read one node record.  The Lean writes `t.nodes[n]?`; the bound test is
    /// explicit here because Aeneas models indexing and `len`, not `Vec::get`.
    pub fn node(&self, n: usize) -> Option<&A> {
        if n >= self.nodes.len() {
            None
        } else {
            Some(&self.nodes[n])
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:87-88 Tbl.derAt
    /// Read one derived word (`der_default` out of range).
    pub fn der_at(&self, n: usize) -> D {
        if n >= self.der.len() {
            D::der_default()
        } else {
            self.der[n].dup2()
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:91 Tbl.find?
    /// The cons-table probe.
    pub fn find(&self, a: &A) -> Option<I> {
        match self.cons.get(a) {
            None => None,
            Some(i) => Some(i.dup2()),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:96-100 Tbl.push
    /// Append a node with its derived word and register it in the cons table.
    /// The record is stored twice, as the Lean stores it twice — once as the
    /// array element and once as the cons key — so the caller hands over one
    /// and `push` copies it into the table.
    pub fn push(&mut self, a: A, d: D, i: I) {
        self.cons.insert(a.dup2(), i);
        self.nodes.push(a);
        self.der.push(d);
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
/// Lean twin: `proof/ConRon/Arena/Store.lean:106-108 AnonNode` — the
/// `anonymous` constructor, line 35.
pub struct AnonNode {}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Store.lean:112-115 StrNode` — the `str`
/// constructor, line 36.  Deviation (DESIGN.md §3.3): the component is a
/// `Vec<u32>` of code points, as every string in the verified core is.
pub struct StrNode {
    pub pre: NIdx,
    pub s: Vec<u32>,
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Store.lean:119-122 NumNode` — the `num`
/// constructor, line 37.  Deviation (DESIGN.md §3.3): the Lean's `Nat` is a
/// `u64`, as every de Bruijn index and name component in the core is.
pub struct NumNode {
    pub pre: NIdx,
    pub n: u64,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:106-108 AnonNode
/// The cited structure's `deriving Hashable`: the constructor index (a
/// structure has one, `0`) and no fields to fold in.
impl Hashable for AnonNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:106-108 AnonNode
    fn hash64(&self) -> u64 {
        0
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:112-115 StrNode
/// `deriving Hashable`: `mixHash` folded over the fields from the
/// constructor index.
impl Hashable for StrNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:112-115 StrNode
    fn hash64(&self) -> u64 {
        name::mix_hash(name::mix_hash(0, self.pre.hash64()), name::str_hash(&self.s))
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:119-122 NumNode
impl Hashable for NumNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:119-122 NumNode
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
/// Lean twin: `proof/ConRon/Arena/Store.lean:130-134 NNodeView` — the
/// store-side view of a name node: con-leche's three constructors with the
/// prefix as a handle.
pub enum NNodeView {
    Anonymous,
    Str(NIdx, Vec<u32>),
    Num(NIdx, u64),
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:137-143 NTables
/// One tier of the name store.
pub struct NTables {
    pub anons: Tbl<AnonNode, NIdx, u64>,
    pub strs: Tbl<StrNode, NIdx, u64>,
    pub nums: Tbl<NumNode, NIdx, u64>,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:144-147 NStore
/// The name store: two tiers and the scratch flag (DESIGN.md §8.3).
pub struct NStore {
    pub pers: NTables,
    pub scr: NTables,
    pub scratch_on: bool,
}

// ---------------------------------------------------------------------------
// Levels (`Store.lean:149-214`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:40-45 Level
/// Lean twin: `proof/ConRon/Arena/Store.lean:153-155 ZeroNode` — the `zero`
/// constructor, line 41.
pub struct ZeroNode {}

/// con-leche: ConLeche/Kernel/Expr.lean:40-45 Level
/// Lean twin: `proof/ConRon/Arena/Store.lean:159-161 SuccNode` — the `succ`
/// constructor, line 42.
pub struct SuccNode {
    pub u: LIdx,
}

/// con-leche: ConLeche/Kernel/Expr.lean:40-45 Level
/// Lean twin: `proof/ConRon/Arena/Store.lean:166-169 BinLNode` — the `max`
/// constructor, line 43, and `imax`, line 44, which has the same two fields
/// and therefore the same record in its own array.
pub struct BinLNode {
    pub u: LIdx,
    pub v: LIdx,
}

/// con-leche: ConLeche/Kernel/Expr.lean:40-45 Level
/// Lean twin: `proof/ConRon/Arena/Store.lean:173-175 ParamNode` — the `param`
/// constructor, line 45.
pub struct ParamNode {
    pub n: NIdx,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:153-155 ZeroNode
impl Hashable for ZeroNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:153-155 ZeroNode
    fn hash64(&self) -> u64 {
        0
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:159-161 SuccNode
impl Hashable for SuccNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:159-161 SuccNode
    fn hash64(&self) -> u64 {
        name::mix_hash(0, self.u.hash64())
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:166-169 BinLNode
impl Hashable for BinLNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:166-169 BinLNode
    fn hash64(&self) -> u64 {
        name::mix_hash(name::mix_hash(0, self.u.hash64()), self.v.hash64())
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:173-175 ParamNode
impl Hashable for ParamNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:173-175 ParamNode
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

/// con-leche: ConLeche/Kernel/Expr.lean:40-45 Level
/// Lean twin: `proof/ConRon/Arena/Store.lean:184-190 LNodeView` — the
/// store-side view of a level node.
pub enum LNodeView {
    Zero,
    Succ(LIdx),
    Max(LIdx, LIdx),
    Imax(LIdx, LIdx),
    Param(NIdx),
}

/// con-leche: ConLeche/Kernel/Expr.lean:40-53 Level
/// Lean twin: `proof/ConRon/Arena/Store.lean:196-199 LDer` — the `hashData`
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

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:196-199 LDer
/// The Lean's `deriving Inhabited` on the pair, i.e. `⟨0, false⟩`.
impl DerDefault for LDer {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:196-199 LDer
    fn der_default() -> LDer {
        LDer { hash: 0, has_param: false }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:202-207 LTables
/// One tier of the level store.
pub struct LTables {
    pub zeros: Tbl<ZeroNode, LIdx, LDer>,
    pub succs: Tbl<SuccNode, LIdx, LDer>,
    pub maxs: Tbl<BinLNode, LIdx, LDer>,
    pub imaxs: Tbl<BinLNode, LIdx, LDer>,
    pub params: Tbl<ParamNode, LIdx, LDer>,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:210-214 LStore
/// The level store, over the name store.
pub struct LStore {
    pub ns: NStore,
    pub pers: LTables,
    pub scr: LTables,
    pub scratch_on: bool,
}

// ---------------------------------------------------------------------------
// Level lists (`Store.lean:216-246`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:227-229 ListNode
/// The interned universe-argument list (nanoda's `LevelsPtr`, `util.rs:84`),
/// so that comparing two `const` nodes' level arguments is one word
/// comparison.  Deviation from the Lean's `List LIdx`: a `Vec<LIdx>`, which
/// is what the rest of the verified core spells a Lean `List` as.
pub struct ListNode {
    pub us: Vec<LIdx>,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:227-229 ListNode
impl Hashable for ListNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:227-229 ListNode
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

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:234 LsNodeView
/// The store-side view of a level-list node.
pub type LsNodeView = Vec<LIdx>;

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:238-239 LsTables
/// One tier of the level-list store (a single constructor).
pub struct LsTables {
    pub lists: Tbl<ListNode, LsIdx, LDer>,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:242-246 LsStore
/// The level-list store, over the level store.
pub struct LsStore {
    pub ls: LStore,
    pub pers: LsTables,
    pub scr: LsTables,
    pub scratch_on: bool,
}

// ---------------------------------------------------------------------------
// Expressions (`Store.lean:248-363`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:252-254 BVarNode` — the `bvar`
/// constructor, line 344.  Deviation (DESIGN.md §3.3): the Lean's `Nat` is a
/// `u64`, as `expr::bvar`'s index already is.
pub struct BVarNode {
    pub i: u64,
}

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:258-261 FVarNode` — the `fvar`
/// constructor, line 345.
pub struct FVarNode {
    pub idx: u64,
    pub ty: EIdx,
}

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:265-267 SortNode` — the `sort`
/// constructor, line 346.
pub struct SortNode {
    pub u: LIdx,
}

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:271-274 ConstNode` — the `const`
/// constructor, line 347.  Two words: the level arguments are one interned
/// handle, not a list.
pub struct ConstNode {
    pub n: NIdx,
    pub us: LsIdx,
}

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:278-281 AppNode` — the `app`
/// constructor, line 348.  Eight bytes of node and eight of derived word,
/// which is what DESIGN.md §8.5 prices the representation at.
pub struct AppNode {
    pub f: EIdx,
    pub a: EIdx,
}

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:286-290 BindNode` — the `lam`
/// constructor, line 349, and `forallE`, line 350: same three fields, its own
/// array.
pub struct BindNode {
    pub ty: EIdx,
    pub body: EIdx,
    pub m: BinderMeta,
}

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:294-298 LetNode` — the `letE`
/// constructor, line 351.
pub struct LetNode {
    pub ty: EIdx,
    pub val: EIdx,
    pub body: EIdx,
}

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:302-304 LitNode` — the `lit`
/// constructor, line 352.
pub struct LitNode {
    pub l: Literal,
}

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:308-312 ProjNode` — the `proj`
/// constructor, line 353.
pub struct ProjNode {
    pub n: NIdx,
    pub i: u64,
    pub e: EIdx,
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:252-254 BVarNode
impl Hashable for BVarNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:252-254 BVarNode
    fn hash64(&self) -> u64 {
        name::mix_hash(0, name::nat_hash(self.i))
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:258-261 FVarNode
impl Hashable for FVarNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:258-261 FVarNode
    fn hash64(&self) -> u64 {
        name::mix_hash(name::mix_hash(0, name::nat_hash(self.idx)), self.ty.hash64())
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:265-267 SortNode
impl Hashable for SortNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:265-267 SortNode
    fn hash64(&self) -> u64 {
        name::mix_hash(0, self.u.hash64())
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:271-274 ConstNode
impl Hashable for ConstNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:271-274 ConstNode
    fn hash64(&self) -> u64 {
        name::mix_hash(name::mix_hash(0, self.n.hash64()), self.us.hash64())
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:278-281 AppNode
impl Hashable for AppNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:278-281 AppNode
    fn hash64(&self) -> u64 {
        name::mix_hash(name::mix_hash(0, self.f.hash64()), self.a.hash64())
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:286-290 BindNode
impl Hashable for BindNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:286-290 BindNode
    fn hash64(&self) -> u64 {
        name::mix_hash(
            name::mix_hash(name::mix_hash(0, self.ty.hash64()), self.body.hash64()),
            expr::binder_meta_hash(&self.m),
        )
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:294-298 LetNode
impl Hashable for LetNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:294-298 LetNode
    fn hash64(&self) -> u64 {
        name::mix_hash(
            name::mix_hash(name::mix_hash(0, self.ty.hash64()), self.val.hash64()),
            self.body.hash64(),
        )
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:302-304 LitNode
impl Hashable for LitNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:302-304 LitNode
    fn hash64(&self) -> u64 {
        name::mix_hash(0, expr::literal_hash(&self.l))
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:308-312 ProjNode
impl Hashable for ProjNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:308-312 ProjNode
    fn hash64(&self) -> u64 {
        name::mix_hash(
            name::mix_hash(name::mix_hash(0, self.n.hash64()), name::nat_hash(self.i)),
            self.e.hash64(),
        )
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:314 instBEqBVarNode
impl Eq2 for BVarNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:314 instBEqBVarNode
    fn eq2(&self, other: &BVarNode) -> bool {
        self.i == other.i
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:315 instBEqFVarNode
impl Eq2 for FVarNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:315 instBEqFVarNode
    fn eq2(&self, other: &FVarNode) -> bool {
        if self.idx == other.idx {
            self.ty.word == other.ty.word
        } else {
            false
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:316 instBEqSortNode
impl Eq2 for SortNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:316 instBEqSortNode
    fn eq2(&self, other: &SortNode) -> bool {
        self.u.word == other.u.word
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:317 instBEqConstNode
impl Eq2 for ConstNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:317 instBEqConstNode
    fn eq2(&self, other: &ConstNode) -> bool {
        if self.n.word == other.n.word {
            self.us.word == other.us.word
        } else {
            false
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:318 instBEqAppNode
impl Eq2 for AppNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:318 instBEqAppNode
    fn eq2(&self, other: &AppNode) -> bool {
        if self.f.word == other.f.word {
            self.a.word == other.a.word
        } else {
            false
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:319 instBEqBindNode
impl Eq2 for BindNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:319 instBEqBindNode
    fn eq2(&self, other: &BindNode) -> bool {
        if self.ty.word == other.ty.word {
            if self.body.word == other.body.word {
                expr::binder_meta_beq(&self.m, &other.m)
            } else {
                false
            }
        } else {
            false
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:320 instBEqLetNode
impl Eq2 for LetNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:320 instBEqLetNode
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

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:321 instBEqLitNode
impl Eq2 for LitNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:321 instBEqLitNode
    fn eq2(&self, other: &LitNode) -> bool {
        expr::literal_beq(&self.l, &other.l)
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:322 instBEqProjNode
impl Eq2 for ProjNode {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:322 instBEqProjNode
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
            m: expr::binder_meta_dup(&self.m),
        }
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

/// con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:328-338 ENodeView` — the
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

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:343-358 ETables
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
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:359-363 EStore
/// The expression store, over the level-list store.  Two tiers: persistent
/// (parse + installed environment) and scratch (one declaration's check), the
/// tier bit of a handle selecting between them (DESIGN.md §8.3).
pub struct EStore {
    pub lss: LsStore,
    pub pers: ETables,
    pub scr: ETables,
    pub scratch_on: bool,
}

// ---------------------------------------------------------------------------
// The name store's operations (`Store.lean:365-510`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:367-428 NTables
/// One tier's seven operations.
impl NTables {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:370 NTables.empty
    pub fn empty() -> NTables {
        NTables { anons: Tbl::empty(), strs: Tbl::empty(), nums: Tbl::empty() }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:375 NTables.count
    /// Nodes in this tier, over all constructors.
    pub fn count(&self) -> usize {
        self.anons.size() + self.strs.size() + self.nums.size()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:379-383 NTables.get
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

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:386-390 NTables.derAt
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

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:393-397 NTables.find?
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

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:401-405 NTables.sizeOf
    /// The size of the constructor array `v` would land in; the capacity test
    /// is stated on it.
    pub fn size_of(&self, v: &NNodeView) -> usize {
        match v {
            NNodeView::Anonymous => self.anons.size(),
            NNodeView::Str(_, _) => self.strs.size(),
            NNodeView::Num(_, _) => self.nums.size(),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:409-426 NTables.push
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

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:430-510 NStore
/// The name store's twelve operations.
impl NStore {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:433 NStore.empty
    pub fn empty() -> NStore {
        NStore { pers: NTables::empty(), scr: NTables::empty(), scratch_on: false }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:438 NStore.persCount
    pub fn pers_count(&self) -> usize {
        self.pers.count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:440 NStore.scrCount
    pub fn scr_count(&self) -> usize {
        self.scr.count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:442 NStore.nodeCount
    /// Nodes in both tiers; the fuel bound `denoteN` uses on the Lean side.
    pub fn node_count(&self) -> usize {
        self.pers_count() + self.scr_count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:446-448 NStore.view
    /// Decode a handle: the tier bit selects the array set, and a scratch
    /// handle reads as absent while the scratch tier is off.
    pub fn view(&self, i: &NIdx) -> Option<NNodeView> {
        if i.is_persistent() {
            self.pers.get(i)
        } else if self.scratch_on {
            self.scr.get(i)
        } else {
            None
        }
    }

    /// con-leche: ConLeche/Kernel/Name.lean:34-44 Name
    /// Lean twin: `proof/ConRon/Arena/Store.lean:452-454 NStore.derived` — the
    /// `hashData` computed field, lines 41-44: the derived word of a handle.
    pub fn derived(&self, i: &NIdx) -> u64 {
        if i.is_persistent() {
            self.pers.der_at(i)
        } else if self.scratch_on {
            self.scr.der_at(i)
        } else {
            0
        }
    }

    /// con-leche: ConLeche/Kernel/Name.lean:34-44 Name
    /// Lean twin: `proof/ConRon/Arena/Store.lean:459-463 NStore.derOfView` —
    /// the `hashData` computed field, lines 41-44: the derived word a node
    /// view *would* get, in `O(1)` from the children's.  The three formulas
    /// are `name::anonymous`/`mk_str`/`mk_num`'s, with `hash_data(&pre)`
    /// replaced by `self.derived(p)`.
    pub fn der_of_view(&self, v: &NNodeView) -> u64 {
        match v {
            NNodeView::Anonymous => 1723,
            NNodeView::Str(p, s) => {
                name::mix_hash(name::mix_hash(1, self.derived(p)), name::str_hash(s))
            }
            NNodeView::Num(p, n) => {
                name::mix_hash(name::mix_hash(2, self.derived(p)), name::nat_hash(*n))
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:467-470 NStore.find?
    /// Probe both tiers, persistent first (nanoda's `alloc_name`: "checks the
    /// longer-lived storage first").
    pub fn find(&self, v: &NNodeView) -> Option<NIdx> {
        match self.pers.find(v) {
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

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:474-492 NStore.intern
    /// Hash-cons a name node: probe persistent, then scratch, then append to
    /// the tier the store is in.  Deviation from the Lean, which is total: the
    /// `2^27`-per-constructor-per-tier limit is `capOK`, a *hypothesis* of the
    /// Lean's `intern_spec`, and DESIGN.md §8.3 puts the test here — "the Rust
    /// raises `Native` at the limit, the Lean `throw`s the same kind".
    pub fn intern(&mut self, v: NNodeView) -> Result<NIdx, CheckError> {
        match self.pers.find(&v) {
            Some(i) => Ok(i),
            None => {
                if self.scratch_on {
                    match self.scr.find(&v) {
                        Some(i) => Ok(i),
                        None => {
                            if self.scr.size_of(&v) >= IDX_CAP as usize {
                                Err(CheckError::Native(code_points(&M_N_CAP)))
                            } else {
                                let d = self.der_of_view(&v);
                                Ok(self.scr.push(v, d, TIER_S))
                            }
                        }
                    }
                } else if self.pers.size_of(&v) >= IDX_CAP as usize {
                    Err(CheckError::Native(code_points(&M_N_CAP)))
                } else {
                    let d = self.der_of_view(&v);
                    Ok(self.pers.push(v, d, TIER_P))
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:496-497 NStore.enableScratch
    /// Open the scratch tier (DESIGN.md §8.3's per-declaration bracket).
    pub fn enable_scratch(&mut self) {
        self.scr = NTables::empty();
        self.scratch_on = true;
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:501-502 NStore.dropScratch
    /// Drop the scratch tier.  Persistent handles keep their bits (DESIGN.md
    /// §8.3, con-leche's lesson 6).
    pub fn drop_scratch(&mut self) {
        self.scr = NTables::empty();
        self.scratch_on = false;
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:507-508 NStore.capOK
    /// `intern`'s capacity precondition, as a test rather than a `Prop`: the
    /// constructor's array in the tier being appended to has room for one more
    /// node.
    pub fn cap_ok(&self, v: &NNodeView) -> bool {
        if self.scratch_on {
            self.scr.size_of(v) < IDX_CAP as usize
        } else {
            self.pers.size_of(v) < IDX_CAP as usize
        }
    }
}

// ---------------------------------------------------------------------------
// The level store's operations (`Store.lean:512-672`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:514-591 LTables
impl LTables {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:517 LTables.empty
    pub fn empty() -> LTables {
        LTables {
            zeros: Tbl::empty(),
            succs: Tbl::empty(),
            maxs: Tbl::empty(),
            imaxs: Tbl::empty(),
            params: Tbl::empty(),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:522-523 LTables.count
    pub fn count(&self) -> usize {
        self.zeros.size()
            + self.succs.size()
            + self.maxs.size()
            + self.imaxs.size()
            + self.params.size()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:526-532 LTables.get
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

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:535-541 LTables.derAt
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

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:544-550 LTables.find?
    pub fn find(&self, v: &LNodeView) -> Option<LIdx> {
        match v {
            LNodeView::Zero => self.zeros.find(&ZeroNode {}),
            LNodeView::Succ(u) => self.succs.find(&SuccNode { u: u.dup2() }),
            LNodeView::Max(u, w) => self.maxs.find(&BinLNode { u: u.dup2(), v: w.dup2() }),
            LNodeView::Imax(u, w) => self.imaxs.find(&BinLNode { u: u.dup2(), v: w.dup2() }),
            LNodeView::Param(n) => self.params.find(&ParamNode { n: n.dup2() }),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:553-559 LTables.sizeOf
    pub fn size_of(&self, v: &LNodeView) -> usize {
        match v {
            LNodeView::Zero => self.zeros.size(),
            LNodeView::Succ(_) => self.succs.size(),
            LNodeView::Max(_, _) => self.maxs.size(),
            LNodeView::Imax(_, _) => self.imaxs.size(),
            LNodeView::Param(_) => self.params.size(),
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:562-589 LTables.push
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

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:593-672 LStore
impl LStore {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:596 LStore.empty
    pub fn empty() -> LStore {
        LStore {
            ns: NStore::empty(),
            pers: LTables::empty(),
            scr: LTables::empty(),
            scratch_on: false,
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:601 LStore.persCount
    pub fn pers_count(&self) -> usize {
        self.pers.count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:603 LStore.scrCount
    pub fn scr_count(&self) -> usize {
        self.scr.count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:605 LStore.nodeCount
    pub fn node_count(&self) -> usize {
        self.pers_count() + self.scr_count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:608-610 LStore.view
    pub fn view(&self, i: &LIdx) -> Option<LNodeView> {
        if i.is_persistent() {
            self.pers.get(i)
        } else if self.scratch_on {
            self.scr.get(i)
        } else {
            None
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:40-53 Level
    /// Lean twin: `proof/ConRon/Arena/Store.lean:614-616 LStore.derived` — the
    /// `hashData` computed field, lines 47-53, and `Kernel/Expr.lean:114-122
    /// levelHasParam`.
    pub fn derived(&self, i: &LIdx) -> LDer {
        if i.is_persistent() {
            self.pers.der_at(i)
        } else if self.scratch_on {
            self.scr.der_at(i)
        } else {
            LDer::der_default()
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:40-53 Level
    /// Lean twin: `proof/ConRon/Arena/Store.lean:621-631 LStore.derOfView` —
    /// the derived record a node view would get, in `O(1)` from the
    /// children's.  con-leche recomputes the parameter flag by an `O(|u|)`
    /// walk at every construction (`Kernel/Expr.lean:114-127`); the interned
    /// store reads it off the column.
    pub fn der_of_view(&self, v: &LNodeView) -> LDer {
        match v {
            LNodeView::Zero => LDer { hash: 1, has_param: false },
            LNodeView::Succ(u) => {
                let du = self.derived(u);
                LDer { hash: name::mix_hash(3, du.hash), has_param: du.has_param }
            }
            LNodeView::Max(u, w) => {
                let du = self.derived(u);
                let dw = self.derived(w);
                LDer {
                    hash: name::mix_hash(5, name::mix_hash(du.hash, dw.hash)),
                    has_param: du.has_param || dw.has_param,
                }
            }
            LNodeView::Imax(u, w) => {
                let du = self.derived(u);
                let dw = self.derived(w);
                LDer {
                    hash: name::mix_hash(7, name::mix_hash(du.hash, dw.hash)),
                    has_param: du.has_param || dw.has_param,
                }
            }
            LNodeView::Param(n) => {
                LDer { hash: name::mix_hash(11, self.ns.derived(n)), has_param: true }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:634-637 LStore.find?
    pub fn find(&self, v: &LNodeView) -> Option<LIdx> {
        match self.pers.find(v) {
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

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:640-658 LStore.intern
    pub fn intern(&mut self, v: LNodeView) -> Result<LIdx, CheckError> {
        match self.pers.find(&v) {
            Some(i) => Ok(i),
            None => {
                if self.scratch_on {
                    match self.scr.find(&v) {
                        Some(i) => Ok(i),
                        None => {
                            if self.scr.size_of(&v) >= IDX_CAP as usize {
                                Err(CheckError::Native(code_points(&M_L_CAP)))
                            } else {
                                let d = self.der_of_view(&v);
                                Ok(self.scr.push(v, d, TIER_S))
                            }
                        }
                    }
                } else if self.pers.size_of(&v) >= IDX_CAP as usize {
                    Err(CheckError::Native(code_points(&M_L_CAP)))
                } else {
                    let d = self.der_of_view(&v);
                    Ok(self.pers.push(v, d, TIER_P))
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:661-662 LStore.enableScratch
    /// Open the scratch tier, here and in the name store.
    pub fn enable_scratch(&mut self) {
        self.ns.enable_scratch();
        self.scr = LTables::empty();
        self.scratch_on = true;
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:665-666 LStore.dropScratch
    /// Drop the scratch tier, here and in the name store.
    pub fn drop_scratch(&mut self) {
        self.ns.drop_scratch();
        self.scr = LTables::empty();
        self.scratch_on = false;
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:669-670 LStore.capOK
    pub fn cap_ok(&self, v: &LNodeView) -> bool {
        if self.scratch_on {
            self.scr.size_of(v) < IDX_CAP as usize
        } else {
            self.pers.size_of(v) < IDX_CAP as usize
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1080-1084 LStore.internName
    /// Intern a name from the level store.  The Lean detaches the nested store
    /// before handing it down (lesson 14); `&mut` is that, so the Rust is the
    /// delegation the detaching exists to make safe.
    pub fn intern_name(&mut self, v: NNodeView) -> Result<NIdx, CheckError> {
        self.ns.intern(v)
    }
}

// ---------------------------------------------------------------------------
// The level-list store's operations (`Store.lean:674-788`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:676-709 LsTables
impl LsTables {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:679 LsTables.empty
    pub fn empty() -> LsTables {
        LsTables { lists: Tbl::empty() }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:684 LsTables.count
    pub fn count(&self) -> usize {
        self.lists.size()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:687-689 LsTables.get
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

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:692-693 LsTables.derAt
    pub fn der_at(&self, i: &LsIdx) -> LDer {
        if i.tag() == LSTAG_LIST {
            self.lists.der_at(i.idx_nat())
        } else {
            LDer::der_default()
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:696 LsTables.find?
    pub fn find(&self, v: &LsNodeView) -> Option<LsIdx> {
        self.lists.find(&ListNode { us: lidx_vec_dup(v) })
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:699 LsTables.sizeOf
    pub fn size_of(&self, _v: &LsNodeView) -> usize {
        self.lists.size()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:702-707 LsTables.push
    pub fn push(&mut self, v: LsNodeView, d: LDer, tier: u32) -> LsIdx {
        let i: LsIdx = LsIdx::pack(LSTAG_LIST, tier, self.lists.size() as u32);
        self.lists.push(ListNode { us: v }, d, i.dup2());
        i
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:711-788 LsStore
impl LsStore {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:714 LsStore.empty
    pub fn empty() -> LsStore {
        LsStore {
            ls: LStore::empty(),
            pers: LsTables::empty(),
            scr: LsTables::empty(),
            scratch_on: false,
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:719 LsStore.persCount
    pub fn pers_count(&self) -> usize {
        self.pers.count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:721 LsStore.scrCount
    pub fn scr_count(&self) -> usize {
        self.scr.count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:723 LsStore.nodeCount
    pub fn node_count(&self) -> usize {
        self.pers_count() + self.scr_count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:726 LsStore.ns
    /// The name store underneath.
    pub fn ns(&self) -> &NStore {
        &self.ls.ns
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:729-731 LsStore.view
    pub fn view(&self, i: &LsIdx) -> Option<LsNodeView> {
        if i.is_persistent() {
            self.pers.get(i)
        } else if self.scratch_on {
            self.scr.get(i)
        } else {
            None
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:136-139 levelsHash
    /// Lean twin: `proof/ConRon/Arena/Store.lean:735-737 LsStore.derived` —
    /// the derived record of a level-list handle.
    pub fn derived(&self, i: &LsIdx) -> LDer {
        if i.is_persistent() {
            self.pers.der_at(i)
        } else if self.scratch_on {
            self.scr.der_at(i)
        } else {
            LDer::der_default()
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:136-139 levelsHash
    /// Lean twin: `proof/ConRon/Arena/Store.lean:742-747 LsStore.derOfView` —
    /// and `Kernel/Expr.lean:125-127 levelsHaveParam`: the derived record a
    /// level list would get.  `O(n)` in the list, as con-leche's own fold is.
    pub fn der_of_view(&self, v: &LsNodeView) -> LDer {
        self.der_of_view_from(v, 0)
    }

    /// con-leche: none — the index recursion behind `der_of_view`
    /// The Lean recurses on the list's tail; Rust carries the cursor, which
    /// is `-loops-to-rec`'s own shape (DESIGN.md §3.4: no loops).
    pub fn der_of_view_from(&self, v: &LsNodeView, i: usize) -> LDer {
        if i >= v.len() {
            LDer { hash: 13, has_param: false }
        } else {
            let hu = self.ls.derived(&v[i]);
            let hr = self.der_of_view_from(v, i + 1);
            LDer {
                hash: name::mix_hash(hu.hash, hr.hash),
                has_param: hu.has_param || hr.has_param,
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:750-753 LsStore.find?
    pub fn find(&self, v: &LsNodeView) -> Option<LsIdx> {
        match self.pers.find(v) {
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

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:756-774 LsStore.intern
    pub fn intern(&mut self, v: LsNodeView) -> Result<LsIdx, CheckError> {
        match self.pers.find(&v) {
            Some(i) => Ok(i),
            None => {
                if self.scratch_on {
                    match self.scr.find(&v) {
                        Some(i) => Ok(i),
                        None => {
                            if self.scr.size_of(&v) >= IDX_CAP as usize {
                                Err(CheckError::Native(code_points(&M_LS_CAP)))
                            } else {
                                let d = self.der_of_view(&v);
                                Ok(self.scr.push(v, d, TIER_S))
                            }
                        }
                    }
                } else if self.pers.size_of(&v) >= IDX_CAP as usize {
                    Err(CheckError::Native(code_points(&M_LS_CAP)))
                } else {
                    let d = self.der_of_view(&v);
                    Ok(self.pers.push(v, d, TIER_P))
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:777-778 LsStore.enableScratch
    pub fn enable_scratch(&mut self) {
        self.ls.enable_scratch();
        self.scr = LsTables::empty();
        self.scratch_on = true;
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:781-782 LsStore.dropScratch
    pub fn drop_scratch(&mut self) {
        self.ls.drop_scratch();
        self.scr = LsTables::empty();
        self.scratch_on = false;
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:785-786 LsStore.capOK
    pub fn cap_ok(&self, v: &LsNodeView) -> bool {
        if self.scratch_on {
            self.scr.size_of(v) < IDX_CAP as usize
        } else {
            self.pers.size_of(v) < IDX_CAP as usize
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1087-1092 LsStore.internName
    pub fn intern_name(&mut self, v: NNodeView) -> Result<NIdx, CheckError> {
        self.ls.intern_name(v)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1095-1100 LsStore.internLevel
    pub fn intern_level(&mut self, v: LNodeView) -> Result<LIdx, CheckError> {
        self.ls.intern(v)
    }
}

// ---------------------------------------------------------------------------
// The expression store's operations (`Store.lean:790-1070`)
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:792-920 ETables
impl ETables {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:795-796 ETables.empty
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
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:801-803 ETables.count
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

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:808-821 ETables.get
    /// Decode one handle against this tier's arrays: read the tag, index one
    /// array, build the view.  There is no node enum in the store (DESIGN.md
    /// §8.3).
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
        } else if i.tag() == ETAG_LAM {
            match self.lams.node(i.idx_nat()) {
                None => None,
                Some(r) => Some(ENodeView::Lam(
                    r.ty.dup2(),
                    r.body.dup2(),
                    expr::binder_meta_dup(&r.m),
                )),
            }
        } else if i.tag() == ETAG_FORALL_E {
            match self.foralls.node(i.idx_nat()) {
                None => None,
                Some(r) => Some(ENodeView::ForallE(
                    r.ty.dup2(),
                    r.body.dup2(),
                    expr::binder_meta_dup(&r.m),
                )),
            }
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

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:824-835 ETables.derAt
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

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:838-849 ETables.find?
    pub fn find(&self, v: &ENodeView) -> Option<EIdx> {
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
            ENodeView::Lam(ty, b, m) => self.lams.find(&BindNode {
                ty: ty.dup2(),
                body: b.dup2(),
                m: expr::binder_meta_dup(m),
            }),
            ENodeView::ForallE(ty, b, m) => self.foralls.find(&BindNode {
                ty: ty.dup2(),
                body: b.dup2(),
                m: expr::binder_meta_dup(m),
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

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:852-863 ETables.sizeOf
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

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:866-918 ETables.push
    pub fn push(&mut self, v: ENodeView, d: u64, tier: u32) -> EIdx {
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
            ENodeView::Lam(ty, b, m) => {
                let h: EIdx = EIdx::pack(ETAG_LAM, tier, self.lams.size() as u32);
                self.lams.push(BindNode { ty, body: b, m }, d, h.dup2());
                h
            }
            ENodeView::ForallE(ty, b, m) => {
                let h: EIdx = EIdx::pack(ETAG_FORALL_E, tier, self.foralls.size() as u32);
                self.foralls.push(BindNode { ty, body: b, m }, d, h.dup2());
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

/// con-leche: ConLeche/Kernel/Expr.lean:343-402 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:992-1005 EStore.derOfView` — the
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

/// con-leche: ConLeche/Kernel/Expr.lean:343-402 Expr
/// Lean twin: `proof/ConRon/Arena/Store.lean:1006-1014 EStore.derOfView` — the
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

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:922-1070 EStore
impl EStore {
    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:925 EStore.empty
    pub fn empty() -> EStore {
        EStore {
            lss: LsStore::empty(),
            pers: ETables::empty(),
            scr: ETables::empty(),
            scratch_on: false,
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:930 EStore.persCount
    pub fn pers_count(&self) -> usize {
        self.pers.count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:932 EStore.scrCount
    pub fn scr_count(&self) -> usize {
        self.scr.count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:934 EStore.nodeCount
    pub fn node_count(&self) -> usize {
        self.pers_count() + self.scr_count()
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:937 EStore.lsS
    /// The level-list store underneath.
    pub fn ls_s(&self) -> &LsStore {
        &self.lss
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:939 EStore.ls
    /// The level store underneath.
    pub fn ls(&self) -> &LStore {
        &self.lss.ls
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:941 EStore.ns
    /// The name store underneath.
    pub fn ns(&self) -> &NStore {
        &self.lss.ls.ns
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:944 EStore.nder
    /// A name's derived word, read through the nesting.
    pub fn nder(&self, i: &NIdx) -> u64 {
        self.ns().derived(i)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:946 EStore.lder
    /// A level's derived record.
    pub fn lder(&self, i: &LIdx) -> LDer {
        self.ls().derived(i)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:948 EStore.lsder
    /// A level list's derived record.
    pub fn lsder(&self, i: &LsIdx) -> LDer {
        self.lss.derived(i)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:952-954 EStore.view
    /// Decode an expression handle: the tier bit selects the array set, the
    /// tag selects the array, the index reads it.
    pub fn view(&self, i: &EIdx) -> Option<ENodeView> {
        if i.is_persistent() {
            self.pers.get(i)
        } else if self.scratch_on {
            self.scr.get(i)
        } else {
            None
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:343-402 Expr
    /// Lean twin: `proof/ConRon/Arena/Store.lean:958-960 EStore.derived` — the
    /// `data` computed field, lines 357-402: the packed derived word of an
    /// expression handle, an `O(1)` column read.
    pub fn derived(&self, i: &EIdx) -> u64 {
        if i.is_persistent() {
            self.pers.der_at(i)
        } else if self.scratch_on {
            self.scr.der_at(i)
        } else {
            0
        }
    }

    /// con-leche: ConLeche/Kernel/Expr.lean:343-402 Expr
    /// Lean twin: `proof/ConRon/Arena/Store.lean:974-1023 EStore.derOfView` —
    /// the `data` computed field, lines 357-402.
    ///
    /// **Not re-derived.**  Each arm is the body of the corresponding smart
    /// constructor of `con_ron_core::kernel::expr`
    /// (`bvar`/`fvar`/`sort`/`mk_const`/`app`/`lam`/`forall_e`/`let_e`/`lit`/
    /// `proj`), with `data(&child)` replaced by `self.derived(h)`, the level
    /// reads by the level store's derived column (`level_hash u ↦
    /// self.lder(u).hash`, `level_has_param u ↦ self.lder(u).has_param`), the
    /// name read by `self.nder(n)` (the `Hashable Name` instance *is*
    /// `Name.hashData`) and `levels_hash us ↦ self.lsder(us).hash`.  Every
    /// `pack_data`, `hash32`, `mix_hash`, `sat_succ`, `sat_pred` and `max_u64`
    /// call below is that crate's, imported and not copied, which is what
    /// makes the arena's word and `expr::data`'s word the same function of
    /// the same term — the equality `mod tests` checks per constructor.
    pub fn der_of_view(&self, v: &ENodeView) -> u64 {
        match v {
            ENodeView::BVar(i) => {
                let h: u64 = expr::hash32(name::mix_hash(3, name::nat_hash(*i)));
                expr::pack_data(h, expr::sat_succ(*i), 0, false)
            }
            ENodeView::FVar(idx, ty) => {
                let dt: u64 = self.derived(ty);
                let h: u64 = expr::hash32(name::mix_hash(
                    5,
                    name::mix_hash(name::nat_hash(*idx), expr::hash_of_data(dt)),
                ));
                expr::pack_data(h, 0, expr::sat_succ(*idx), expr::lp_of_data(dt))
            }
            ENodeView::Sort(u) => {
                let du = self.lder(u);
                let h: u64 = expr::hash32(name::mix_hash(7, du.hash));
                expr::pack_data(h, 0, 0, du.has_param)
            }
            ENodeView::Const(n, us) => {
                let dus = self.lsder(us);
                let h: u64 = expr::hash32(name::mix_hash(
                    11,
                    name::mix_hash(self.nder(n), dus.hash),
                ));
                expr::pack_data(h, 0, 0, dus.has_param)
            }
            ENodeView::App(f, a) => {
                let df: u64 = self.derived(f);
                let da: u64 = self.derived(a);
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
            ENodeView::Lam(ty, b, m) => der_of_bind(
                19,
                self.derived(ty),
                self.derived(b),
                prop_when::hash_pw(&m.pw),
                prop_when::has_params(&m.pw),
            ),
            ENodeView::ForallE(ty, b, m) => der_of_bind(
                23,
                self.derived(ty),
                self.derived(b),
                prop_when::hash_pw(&m.pw),
                prop_when::has_params(&m.pw),
            ),
            ENodeView::LetE(ty, val, b) => {
                der_of_let(self.derived(ty), self.derived(val), self.derived(b))
            }
            ENodeView::Lit(l) => {
                let h: u64 = expr::hash32(name::mix_hash(31, expr::literal_hash(l)));
                expr::pack_data(h, 0, 0, false)
            }
            ENodeView::Proj(s, i, e) => {
                let de: u64 = self.derived(e);
                let h: u64 = expr::hash32(name::mix_hash(
                    37,
                    name::mix_hash(
                        self.nder(s),
                        name::mix_hash(name::nat_hash(*i), expr::hash_of_data(de)),
                    ),
                ));
                expr::pack_data(
                    h,
                    expr::bvar_of_data(de),
                    expr::fvar_of_data(de),
                    expr::lp_of_data(de),
                )
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1024-1027 EStore.find?
    /// Probe both tiers, persistent first (nanoda's `alloc_expr`).
    pub fn find(&self, v: &ENodeView) -> Option<EIdx> {
        match self.pers.find(v) {
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

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1032-1050 EStore.intern
    /// Hash-cons an expression node: probe the persistent cons table, then the
    /// scratch one, then append to the tier the store is in (DESIGN.md §8.3).
    /// The cap test is the Lean's `capOK` turned into the `Native` decline
    /// §8.3 puts here.
    pub fn intern(&mut self, v: ENodeView) -> Result<EIdx, CheckError> {
        match self.pers.find(&v) {
            Some(i) => Ok(i),
            None => {
                if self.scratch_on {
                    match self.scr.find(&v) {
                        Some(i) => Ok(i),
                        None => {
                            if self.scr.size_of(&v) >= IDX_CAP as usize {
                                Err(CheckError::Native(code_points(&M_E_CAP)))
                            } else {
                                let d = self.der_of_view(&v);
                                Ok(self.scr.push(v, d, TIER_S))
                            }
                        }
                    }
                } else if self.pers.size_of(&v) >= IDX_CAP as usize {
                    Err(CheckError::Native(code_points(&M_E_CAP)))
                } else {
                    let d = self.der_of_view(&v);
                    Ok(self.pers.push(v, d, TIER_P))
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1054-1055 EStore.enableScratch
    /// Open the scratch tier, in all four stores.  DESIGN.md §8.3: "each tier
    /// has its own array set and cons tables, both indexed from 0".
    pub fn enable_scratch(&mut self) {
        self.lss.enable_scratch();
        self.scr = ETables::empty();
        self.scratch_on = true;
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1060-1061 EStore.dropScratch
    /// Drop the scratch tier, in all four stores.  Persistent handles keep
    /// their bits, so everything that denoted before still denotes (DESIGN.md
    /// §8.3, con-leche's lesson 6).
    pub fn drop_scratch(&mut self) {
        self.lss.drop_scratch();
        self.scr = ETables::empty();
        self.scratch_on = false;
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1067-1068 EStore.capOK
    pub fn cap_ok(&self, v: &ENodeView) -> bool {
        if self.scratch_on {
            self.scr.size_of(v) < IDX_CAP as usize
        } else {
            self.pers.size_of(v) < IDX_CAP as usize
        }
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1103-1107 EStore.internName
    /// Intern a name from the expression store.
    pub fn intern_name(&mut self, v: NNodeView) -> Result<NIdx, CheckError> {
        self.lss.intern_name(v)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1110-1114 EStore.internLevel
    /// Intern a level from the expression store.
    pub fn intern_level(&mut self, v: LNodeView) -> Result<LIdx, CheckError> {
        self.lss.intern_level(v)
    }

    /// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/Store.lean:1118-1123 EStore.internLevels
    /// Intern a universe-argument list from the expression store.
    pub fn intern_levels(&mut self, v: LsNodeView) -> Result<LsIdx, CheckError> {
        self.lss.intern(v)
    }
}

// ---------------------------------------------------------------------------
// Tests: `proof/ConRon/Arena/StoreTest.lean`'s forty-four `#guard`s
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use con_ron_core::kernel::expr::Expr;
    use con_ron_core::kernel::level;
    use con_ron_core::kernel::level::Level;
    use con_ron_core::kernel::name;
    use con_ron_core::kernel::name::Name;
    use con_ron_core::ron::nat;

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
        if fuel == 0 {
            return None;
        }
        match st.view(i) {
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
        denote_n_aux(st, st.node_count() as u64 + 1, i)
    }

    fn denote_l_aux(st: &LStore, fuel: u64, i: &LIdx) -> Option<Level> {
        if fuel == 0 {
            return None;
        }
        match st.view(i) {
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
        denote_l_aux(st, st.node_count() as u64 + 1, i)
    }

    fn denote_ls(st: &LsStore, i: &LsIdx) -> Option<Vec<Level>> {
        match st.view(i) {
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
        if fuel == 0 {
            return None;
        }
        match st.view(i) {
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
        denote_e_aux(st, st.node_count() as u64 + 1, i)
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
        let mut st = EStore::empty();
        let z = ok(st.intern_level(LNodeView::Zero));
        let one = ok(st.intern_level(LNodeView::Succ(z.dup2())));
        let anon = ok(st.intern_name(NNodeView::Anonymous));
        let foo = ok(st.intern_name(NNodeView::Str(anon.dup2(), cp("foo"))));
        let us = ok(st.intern_levels(vec![z.dup2()]));
        let s0 = ok(st.intern(ENodeView::Sort(z.dup2())));
        let s1 = ok(st.intern(ENodeView::Sort(one.dup2())));
        let c = ok(st.intern(ENodeView::Const(foo.dup2(), us.dup2())));
        let ap = ok(st.intern(ENodeView::App(c.dup2(), s0.dup2())));
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
        let (mut st, z, one, foo, _us, s0, _s1, c, ap) = fixture();

        // #guard 8: the same node interned twice gives the same handle.
        let a = ok(st.intern(ENodeView::App(c.dup2(), s0.dup2())));
        let b = ok(st.intern(ENodeView::App(c.dup2(), s0.dup2())));
        assert_eq!(a.word, b.word);
        assert_eq!(a.word, ap.word);

        // #guard 9
        let a = ok(st.intern(ENodeView::Sort(z.dup2())));
        assert_eq!(a.word, s0.word);

        // #guard 10
        let a = ok(st.intern_level(LNodeView::Succ(z.dup2())));
        assert_eq!(a.word, one.word);

        // #guard 11
        let anon = ok(st.intern_name(NNodeView::Anonymous));
        let a = ok(st.intern_name(NNodeView::Str(anon, cp("foo"))));
        assert_eq!(a.word, foo.word);
    }

    // --- `StoreTest.lean:79-91`: cross-tier dedup ----------------------------

    #[test]
    fn cross_tier_dedup() {
        // #guard 12: a persistent node is never re-interned into scratch.
        let (mut st, _z, _one, _foo, _us, s0, _s1, c, ap) = fixture();
        st.enable_scratch();
        let a = ok(st.intern(ENodeView::App(c.dup2(), s0.dup2())));
        assert_eq!(a.word, ap.word);
        assert!(a.is_persistent());

        // #guard 13: a genuinely new node lands in scratch, and dedups there.
        let a = ok(st.intern(ENodeView::App(s0.dup2(), s0.dup2())));
        let b = ok(st.intern(ENodeView::App(s0.dup2(), s0.dup2())));
        assert_eq!(a.word, b.word);
        assert!(!a.is_persistent());
    }

    // --- `StoreTest.lean:93-97`: `view` decodes what was interned ------------

    #[test]
    fn view_decodes_what_was_interned() {
        let (st, z, _one, foo, us, s0, _s1, c, ap) = fixture();
        // #guard 14
        assert!(view_eq(&st.view(&ap), &Some(ENodeView::App(c.dup2(), s0.dup2()))));
        // #guard 15
        assert!(view_eq(&st.view(&s0), &Some(ENodeView::Sort(z.dup2()))));
        // #guard 16
        assert!(view_eq(&st.view(&c), &Some(ENodeView::Const(foo.dup2(), us.dup2()))));
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
        let (st, z, one, foo, us, s0, s1, c, ap) = fixture();
        assert_eq!(st.derived(&s0), expr::data(&e_s0())); // #guard 23
        assert_eq!(st.derived(&s1), expr::data(&e_s1())); // #guard 24
        assert_eq!(st.derived(&c), expr::data(&e_c())); // #guard 25
        assert_eq!(st.derived(&ap), expr::data(&e_ap())); // #guard 26
        assert_eq!(st.ns().derived(&foo), name::hash_data(&n_foo())); // #guard 27
        assert_eq!(st.ls().derived(&z).hash, level::hash_data(&level::zero())); // #guard 28
        // #guard 29
        assert_eq!(
            st.ls().derived(&one).hash,
            level::hash_data(&level::succ(level::zero()))
        );
        // #guard 30
        assert_eq!(st.lss.derived(&us).hash, level::levels_hash(&vec![level::zero()]));
        // #guard 31
        assert_eq!(
            st.lss.derived(&us).has_param,
            level::levels_have_param(&vec![level::zero()])
        );
    }

    // --- `StoreTest.lean:125-140`: a binder, a bvar, the range fields --------

    #[test]
    fn binder_and_bvar_exercise_the_range_fields() {
        let (mut st, _z, _one, _foo, _us, s0, _s1, _c, _ap) = fixture();
        let b0 = ok(st.intern(ENodeView::BVar(0)));
        let lam = ok(st.intern(ENodeView::Lam(
            s0.dup2(),
            b0.dup2(),
            expr::binder_meta(prop_when::never()),
        )));
        let e_b0 = expr::bvar(0);
        let e_lam = expr::lam(e_s0(), expr::bvar(0), expr::binder_meta(prop_when::never()));
        assert!(eq_e(&denote_e(&st, &b0), &e_b0)); // #guard 32
        assert!(eq_e(&denote_e(&st, &lam), &e_lam)); // #guard 33
        assert_eq!(st.derived(&b0), expr::data(&e_b0)); // #guard 34
        assert_eq!(st.derived(&lam), expr::data(&e_lam)); // #guard 35
    }

    // --- `StoreTest.lean:142-167`: the `dropScratch` bracket -----------------

    #[test]
    fn drop_scratch_invalidates_scratch_and_keeps_persistent() {
        let (mut st, _z, _one, _foo, _us, s0, _s1, _c, ap) = fixture();
        let pers_view_ap = st.view(&ap);
        st.enable_scratch();
        let scr = ok(st.intern(ENodeView::App(s0.dup2(), s0.dup2())));

        assert!(!scr.is_persistent()); // #guard 36
        assert!(eq_e(&denote_e(&st, &scr), &expr::app(e_s0(), e_s0()))); // #guard 37
        assert!(eq_e(&denote_e(&st, &ap), &e_ap())); // #guard 38

        st.drop_scratch();
        assert!(denote_e(&st, &scr).is_none()); // #guard 39
        assert!(st.view(&scr).is_none()); // #guard 40
        assert!(eq_e(&denote_e(&st, &ap), &e_ap())); // #guard 41
        assert!(view_eq(&st.view(&ap), &pers_view_ap)); // #guard 42
        assert!(!st.scratch_on); // #guard 43
    }

    /// `StoreTest.lean:165-167`: a persistent handle's *bits* are unchanged by
    /// the bracket — the point of putting the tier bit above the index.
    #[test]
    fn a_persistent_handles_bits_survive_the_bracket() {
        let (mut st, z, _one, _foo, _us, s0, _s1, _c, _ap) = fixture();
        st.enable_scratch();
        let a = ok(st.intern(ENodeView::Sort(z.dup2())));
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
        let (mut st, z, _one, foo, _us, s0, _s1, _c, _ap) = fixture();

        let fv = ok(st.intern(ENodeView::FVar(3, s0.dup2())));
        let e_fv = expr::fvar(3, e_s0());
        assert!(eq_e(&denote_e(&st, &fv), &e_fv));
        assert_eq!(st.derived(&fv), expr::data(&e_fv));

        let b0 = ok(st.intern(ENodeView::BVar(0)));
        let fa = ok(st.intern(ENodeView::ForallE(
            s0.dup2(),
            b0.dup2(),
            expr::binder_meta(prop_when::never()),
        )));
        let e_fa = expr::forall_e(e_s0(), expr::bvar(0), expr::binder_meta(prop_when::never()));
        assert!(eq_e(&denote_e(&st, &fa), &e_fa));
        assert_eq!(st.derived(&fa), expr::data(&e_fa));

        let le = ok(st.intern(ENodeView::LetE(s0.dup2(), s0.dup2(), b0.dup2())));
        let e_le = expr::let_e(e_s0(), e_s0(), expr::bvar(0));
        assert!(eq_e(&denote_e(&st, &le), &e_le));
        assert_eq!(st.derived(&le), expr::data(&e_le));

        let li = ok(st.intern(ENodeView::Lit(expr::literal_nat(nat::from_u64(7)))));
        let e_li = expr::lit(expr::literal_nat(nat::from_u64(7)));
        assert!(eq_e(&denote_e(&st, &li), &e_li));
        assert_eq!(st.derived(&li), expr::data(&e_li));

        let pj = ok(st.intern(ENodeView::Proj(foo.dup2(), 1, s0.dup2())));
        let e_pj = expr::proj(n_foo(), 1, e_s0());
        assert!(eq_e(&denote_e(&st, &pj), &e_pj));
        assert_eq!(st.derived(&pj), expr::data(&e_pj));

        let anon = ok(st.intern_name(NNodeView::Anonymous));
        let n7 = ok(st.intern_name(NNodeView::Num(anon.dup2(), 7)));
        let e_n7 = name::mk_num(name::anonymous(), 7);
        assert!(eq_n(&denote_n(st.ns(), &n7), &e_n7));
        assert_eq!(st.ns().derived(&n7), name::hash_data(&e_n7));

        let p = ok(st.intern_level(LNodeView::Param(foo.dup2())));
        let mx = ok(st.intern_level(LNodeView::Max(z.dup2(), p.dup2())));
        let im = ok(st.intern_level(LNodeView::Imax(z.dup2(), p.dup2())));
        let e_p = level::param(n_foo());
        let e_mx = level::max(level::zero(), level::param(n_foo()));
        let e_im = level::imax(level::zero(), level::param(n_foo()));
        assert_eq!(st.ls().derived(&p).hash, level::hash_data(&e_p));
        assert!(st.ls().derived(&p).has_param);
        assert_eq!(st.ls().derived(&mx).hash, level::hash_data(&e_mx));
        assert_eq!(st.ls().derived(&mx).has_param, level::level_has_param(&e_mx));
        assert_eq!(st.ls().derived(&im).hash, level::hash_data(&e_im));
        assert_eq!(st.ls().derived(&im).has_param, level::level_has_param(&e_im));

        // a two-element universe list, so `der_of_view_from` recurses
        let us2 = ok(st.intern_levels(vec![z.dup2(), p.dup2()]));
        let e_us2 = vec![level::zero(), level::param(n_foo())];
        assert_eq!(st.lss.derived(&us2).hash, level::levels_hash(&e_us2));
        assert_eq!(st.lss.derived(&us2).has_param, level::levels_have_param(&e_us2));
    }

    /// The tier bit is what separates the two array sets: each tier is indexed
    /// from zero, and `enable_scratch` empties the scratch tier again.
    #[test]
    fn the_two_tiers_are_indexed_from_zero_independently() {
        let (mut st, _z, _one, _foo, _us, s0, _s1, _c, _ap) = fixture();
        st.enable_scratch();
        let scr = ok(st.intern(ENodeView::BVar(0)));
        assert!(!scr.is_persistent());
        assert_eq!(scr.index(), 0);
        assert_eq!(scr.tag(), ETAG_BVAR);
        assert_eq!(s0.index(), 0);
        assert_ne!(scr.word, s0.word);
        st.enable_scratch();
        assert!(st.view(&scr).is_none());
        assert_eq!(st.scr_count(), 0);
    }

    /// `find` is `intern` without the append: it misses before, hits after, and
    /// `node_count` counts exactly what was appended.
    #[test]
    fn find_agrees_with_intern_and_node_count_counts() {
        let (mut st, _z, _one, _foo, _us, s0, _s1, _c, _ap) = fixture();
        let before = st.node_count();
        assert!(st.find(&ENodeView::App(s0.dup2(), s0.dup2())).is_none());
        assert!(st.cap_ok(&ENodeView::App(s0.dup2(), s0.dup2())));
        let h = ok(st.intern(ENodeView::App(s0.dup2(), s0.dup2())));
        assert_eq!(st.node_count(), before + 1);
        match st.find(&ENodeView::App(s0.dup2(), s0.dup2())) {
            None => panic!("an interned node was not found"),
            Some(g) => assert_eq!(g.word, h.word),
        }
        // interning it again appends nothing
        let h2 = ok(st.intern(ENodeView::App(s0.dup2(), s0.dup2())));
        assert_eq!(h2.word, h.word);
        assert_eq!(st.node_count(), before + 1);
    }
}

//! `proof/ConRon/Arena/Frontend/Types.lean` — **the frontend's own types over
//! handles** (task #97 P4e part 1).
//!
//! The representation-free half of con-leche's frontend
//! (`ConLeche/Frontend/Export.lean`) plus the two records the parse hands to
//! things it does not own: the projection rewrite's owner
//! (`ConLeche/Frontend/ProjRec.lean`) and the in-process modeller's block
//! (`ConLeche/Frontend/InModel/Mutual.lean`).
//!
//! **The error channel.**  con-leche's frontend runs in `abbrev M := Except
//! String` and pairs a failure with the input LINE at the chunk drivers
//! (`Except (CheckError × Nat)`); DESIGN.md §8.4 gives (B) one monad and the
//! twin's census records that "the frontend's own `M` collapses into `AM`".
//! The Rust merges the two arms the same way `con_ron_core::frontend::
//! export_c` does, into one `Result` with two arms
//! ([`export_c::LineErr`](super::export_c::LineErr)); the difference from
//! con-ron-core's is that the message arm carries a whole `CheckError` and not
//! a `Vec<u32>`, because `EStore::intern` can decline with `Native` at the
//! `2^27` cap (DESIGN.md §8.3) and that kind must survive to the exit code.
//!
//! **The in-process modeller is a one-method seam** (DESIGN.md §8.2's
//! `Modeller`, and `con_ron_core::frontend::in_model_rec::Modeller`'s shape
//! exactly).  con-leche calls `InModel.generate` directly; (B) takes a
//! `Modeller` whose single method maps handles to handles, and part 1 supplies
//! [`DeclineModeller`], which declines every block it is asked about.  The
//! seam is UNVERIFIED by design: a wrong generated record is rejected or
//! declined by the fold, never accepted, so its correctness decides coverage
//! and not soundness.  What a default instantiation must NOT be is con-leche's
//! own `InModel.generate` on read-back terms: that builds `Expr` trees, which
//! is the one thing DESIGN.md §8.3 forbids the parse.  **The Rust modeller
//! instantiation for the checker is `crates/con-ron`'s existing unverified
//! port**, outside this crate as it is outside `con-ron-core`, for the reason
//! `in_model_rec`'s module note gives.

use crate::arena::env::{IConstantVal, IDeclaration, IRecRule};
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::store::EStore;
use con_ron_core::kernel::core_types;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env::ReducibilityHint;
use con_ron_core::ron::hashmap::HashMap;

// ---------------------------------------------------------------------------
// Record verdicts (`Types.lean:44-59` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/Export.lean:71-79 RecordVerdict
/// Lean twin: `proof/ConRon/Arena/Frontend/Types.lean:48-50 RecordVerdict` —
/// what a declaration record carries out of the parse when it does not produce
/// a state: a positive DECLINE, or a REJECT (the record's redundant fields
/// contradict the block's own declarations).  A message is a `Vec<u32>` of
/// code points (DESIGN.md §3.3), as every Lean `String` is in the port.
pub enum RecordVerdict {
    Declined(Vec<u32>),
    Invalid(Vec<u32>),
}

/// con-leche: ConLeche/Frontend/Export.lean:81-85 RecordVerdict.toError
/// Lean twin: `proof/ConRon/Arena/Frontend/Types.lean:55-57 RecordVerdict.toError`
/// — the checker error a record verdict becomes; the caller pairs it with the
/// line the record was read at.
pub fn record_verdict_to_error(v: RecordVerdict) -> CheckError {
    match v {
        RecordVerdict::Declined(what) => core_types::not_implemented(what),
        RecordVerdict::Invalid(what) => core_types::invalid(what),
    }
}

// ---------------------------------------------------------------------------
// The projection rewrite's owner (`Types.lean:61-79` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ProjRec.lean:83-104 ProjRecOwner
/// Lean twin: `proof/ConRon/Arena/Frontend/Types.lean:68-79 ProjRecOwner` —
/// what the projection-function rewrite needs to know about one
/// structure-like owner `T` of a parsed inductive block the direct install
/// does not serve.  A field-for-field mirror; the rewrite that READS it is
/// task #97e part 2 (it needs the `ExprOps` twins of
/// `ConLeche/Frontend/ProjRec.lean`), so nothing writes this table today and
/// `export_c::proj_rewrite_d` answers what con-leche answers at an empty one.
///
/// Deviation: the field `T` is `t` (Rust field names are lower case).
pub struct ProjRecOwner {
    pub t: NIdx,
    pub lps: Vec<NIdx>,
    pub n_p: u64,
    pub ctor: NIdx,
    pub n_f: u64,
    pub rec_name: NIdx,
    pub rec_lps: Vec<NIdx>,
    pub rec_type: EIdx,
    pub num_motives: u64,
    pub num_minors: u64,
}

// ---------------------------------------------------------------------------
// The in-process modeller's block (`Types.lean:81-130` of the twin)
//
// con-leche's `InModel` namespace has its own `IndTypeRec`/`IndCtorRec`/
// `IndRecRec` — the *resolved* shape records, not the scanner's — so the twins
// carry an `M` prefix to keep them apart from
// `con_ron_core::frontend::scan_types::IndTypeRec`, which `export_c` uses as
// it is (the scanner is reused, not twinned).
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/InModel/Mutual.lean:65-74 IndTypeRec
/// Lean twin: `proof/ConRon/Arena/Frontend/Types.lean:92-100 MIndTypeRec` —
/// one type former of a parsed block, resolved.
pub struct MIndTypeRec {
    pub cv: IConstantVal,
    pub n_p: u64,
    pub n_idx: u64,
    pub ctors: Vec<NIdx>,
    pub is_rec: bool,
    pub is_reflexive: bool,
    pub num_nested: u64,
}

/// con-leche: ConLeche/Frontend/InModel/Mutual.lean:76-81 IndCtorRec
/// Lean twin: `proof/ConRon/Arena/Frontend/Types.lean:104-108 MIndCtorRec` —
/// one constructor of a parsed block, resolved.
pub struct MIndCtorRec {
    pub cv: IConstantVal,
    pub n_p: u64,
    pub n_f: u64,
}

/// con-leche: ConLeche/Frontend/InModel/Mutual.lean:83-92 IndRecRec
/// Lean twin: `proof/ConRon/Arena/Frontend/Types.lean:112-119 MIndRecRec` —
/// one recursor of a parsed block, resolved.
pub struct MIndRecRec {
    pub cv: IConstantVal,
    pub n_p: u64,
    pub n_m: u64,
    pub nm: u64,
    pub n_i: u64,
    pub rules: Vec<IRecRule>,
}

/// con-leche: ConLeche/Frontend/InModel/Mutual.lean:94-99 BlockRec
/// Lean twin: `proof/ConRon/Arena/Frontend/Types.lean:123-127 BlockRec` — a
/// parsed inductive block.
pub struct BlockRec {
    pub types: Vec<MIndTypeRec>,
    pub ctors: Vec<MIndCtorRec>,
    pub recs: Vec<MIndRecRec>,
}

// ---------------------------------------------------------------------------
// What the generator reads besides the block (`Types.lean:129-147` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:454-455 ConstTable
/// Lean twin: `proof/ConRon/Arena/Frontend/Types.lean:131 ConstTable` — the
/// declared types of the constants pushed so far, by name.
///
/// Deviation: the twin's `NIdx → Option (List NIdx × EIdx)` is a Lean
/// closure over the parse state; the core owns the table and §3.4 has no
/// closures, so this is the table itself and [`ctx_tbl`] is the lambda —
/// `con_ron_core::frontend::in_model_rec::ModelCtx`'s own deviation.
pub type ConstTable = HashMap<NIdx, (Vec<NIdx>, EIdx)>;

/// con-leche: ConLeche/Frontend/InModel/Mutual.lean:101-108 Ctx
/// Lean twin: `proof/ConRon/Arena/Frontend/Types.lean:135-138 Ctx` — what the
/// generator reads besides the block.  The three function fields become three
/// borrows (the [`ConstTable`] deviation); a lifetime-parameterised struct is
/// established vocabulary in the port (`kernel::level::SubstZ<'a>`).
pub struct ModelCtx<'a> {
    pub tbl: &'a ConstTable,
    pub heights: &'a HashMap<NIdx, u64>,
    pub blocks: &'a HashMap<NIdx, BlockRec>,
}

/// con-leche: ConLeche/Frontend/ExportC.lean:603-607 _
/// The cited `fun n => st.constTypes[n]?`: a pushed constant's level
/// parameters and declared type, borrowed off the context.
pub fn ctx_tbl<'a>(ctx: &'a ModelCtx<'a>, n: &NIdx) -> Option<&'a (Vec<NIdx>, EIdx)> {
    ctx.tbl.get(n)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:603-607 _
/// The cited `fun n => st.heights.getD n 0`.
pub fn ctx_height(ctx: &ModelCtx, n: &NIdx) -> u64 {
    match ctx.heights.get(n) {
        None => 0,
        Some(h) => *h,
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:603-607 _
/// The cited `fun n => st.indBlocks[n]?`.
pub fn ctx_block<'a>(ctx: &'a ModelCtx<'a>, n: &NIdx) -> Option<&'a BlockRec> {
    ctx.blocks.get(n)
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:608-611 hintHeight
/// Lean twin: `proof/ConRon/Arena/Frontend/Types.lean:142-144 hintHeight` —
/// the definitional height a reducibility hint carries.  It is `InModel`'s,
/// and the parse needs it at one place only (`export_c::note_decl`, which
/// books a pushed definition's height for the generator's hint arithmetic),
/// so the seam carries it.
pub fn hint_height(h: &ReducibilityHint) -> u64 {
    match h {
        ReducibilityHint::Regular(n) => *n,
        ReducibilityHint::Abbrev => 0,
        ReducibilityHint::Opaque => 0,
    }
}

// ---------------------------------------------------------------------------
// The seam (`Types.lean:149-173` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/InModel.lean:34-37 wants
/// Lean twin: `proof/ConRon/Arena/Frontend/Types.lean:149-152 wants` — is the
/// block one the modeller is for: mutual (several types) or nested
/// (`numNested > 0`)?  It reads counts and no term, so it is the same function
/// over handles and stays beside the seam rather than inside it.
pub fn wants(b: &BlockRec) -> bool {
    if b.types.len() > 1 {
        return true;
    }
    wants_nested(b, 0)
}

/// con-leche: ConLeche/Frontend/InModel.lean:34-37 wants
/// The cited `b.types.any (·.numNested > 0)`, as the cursor recursion §3.4
/// asks for outside a loop-exempt walk.
pub fn wants_nested(b: &BlockRec, i: usize) -> bool {
    if i >= b.types.len() {
        false
    } else if b.types[i].num_nested > 0 {
        true
    } else {
        wants_nested(b, i + 1)
    }
}

/// con-leche: ConLeche/Frontend/InModel.lean:39-45 generate
/// Lean twin: `proof/ConRon/Arena/Frontend/Types.lean:163-164 Modeller` —
/// **the modeller seam** (DESIGN.md §8.2's `Modeller`).  One method: a block
/// in, the model records it generates in stream order or the reason it is
/// declined.  Handles in, handles out — nothing in (B) may build an `Expr`
/// tree, and a default instantiation that called con-leche's own generator on
/// read-back terms would do exactly that.
///
/// **Why a trait and not a function pointer** (`in_model_rec`'s reason,
/// unchanged): a trait method on a type parameter extracts as a *typeclass
/// field* — an opaque function of the quantified `Self` — so the extracted
/// parse is quantified over an arbitrary modeller and a later refinement
/// carries one hypothesis about its output rather than a port of four
/// thousand lines whose correctness decides coverage and not soundness.  A
/// `dyn` object or a function pointer is outside the subset (DESIGN.md §3.4).
///
/// The store is in hand because the twin's method is in `AM`: a generated
/// record's terms are handles, and building one means interning it.
pub trait Modeller {
    /// con-leche: ConLeche/Frontend/InModel.lean:39-45 generate
    /// The one method: the block's model records, or the decline's text.
    fn generate(
        &self,
        ar: &mut EStore,
        ctx: &ModelCtx,
        b: &BlockRec,
    ) -> Result<Vec<IDeclaration>, Vec<u32>>;
}

/// con-leche: none — the declining stub (B) ships until the generator is ported (task #97e part 2)
/// Lean twin: `proof/ConRon/Arena/Frontend/Types.lean:172-173 declineModeller`
/// — the modeller that declines every block `wants` routes to it.  A decline
/// here is `install_ind_d`'s own `.declined` verdict naming the block: the
/// same positive statement con-leche makes when its own generator declines a
/// residual class, so the verdict machinery around it is exercised by the
/// fixtures.
pub struct DeclineModeller {}

/// con-leche: none — the declining stub (B) ships until the generator is ported (task #97e part 2)
/// Lean twin: `proof/ConRon/Arena/Frontend/Types.lean:172-173 declineModeller`
impl Modeller for DeclineModeller {
    /// con-leche: none — the declining stub (B) ships until the generator is ported (task #97e part 2)
    /// The twin's sentence, verbatim: `"the arena's in-process modeller is not
    /// ported yet"`.
    fn generate(
        &self,
        _ar: &mut EStore,
        _ctx: &ModelCtx,
        _b: &BlockRec,
    ) -> Result<Vec<IDeclaration>, Vec<u32>> {
        const M: [u32; 49] = [
            116, 104, 101, 32, 97, 114, 101, 110, 97, 39, 115, 32, 105, 110, 45, 112, 114,
            111, 99, 101, 115, 115, 32, 109, 111, 100, 101, 108, 108, 101, 114, 32, 105,
            115, 32, 110, 111, 116, 32, 112, 111, 114, 116, 101, 100, 32, 121, 101, 116,
        ];
        Err(core_types::code_points(&M))
    }
}

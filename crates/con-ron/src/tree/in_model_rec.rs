//! `ConLeche/Frontend/InModel/Mutual.lean`'s block records and
//! `ConLeche/Frontend/InModel.lean`'s `wants` — **the modeller's data and the
//! seam it is called through, and nothing else**.
//!
//! The in-process modeller itself (`InModel.generate`, six thousand lines of
//! `crates/con-ron/src/in_model/`) stays in the unverified crate.  Its own
//! module note says why that is sound: "soundness needs nothing from this
//! module" — every record it generates is checked by the fold as a stream
//! declaration, so a wrong one is rejected or declined, never accepted.  What
//! it decides is *coverage*, which no theorem about the checker's soundness
//! mentions.
//!
//! What has to cross into the core is therefore only
//!
//! * the four records the parse builds for it (`block_rec_of` in `export_c`
//!   fills them out of the scanned inductive record), because they are built
//!   inside the parse and so inside the extraction;
//! * `wants`, the parse's own decision to call the modeller at all;
//! * the reader `ModelCtx` the parse hands it, which is the three tables the
//!   parse keeps (`ExportC.lean:603-607`'s three lambdas); and
//! * the call itself, as the one-method trait [`Modeller`].
//!
//! **Why a trait and not a function pointer.**  A trait method on a type
//! parameter extracts as a *typeclass field* — an opaque function of the
//! quantified `Self` — so the Lean the parse extracts to is quantified over an
//! arbitrary modeller and the refinement carries one hypothesis about its
//! output instead of a port of the generator.  A `dyn` object or a function
//! pointer is outside the subset (DESIGN.md §3.4).
//!
//! **`Ctx`'s three function fields become three borrows.**  con-leche's
//! `InModel.Ctx` is a record of three Lean closures over the parse state; the
//! core owns the tables those closures read, so `ModelCtx` borrows them and
//! `ctx_tbl`/`ctx_height`/`ctx_block` are the three lambdas.  A
//! lifetime-parameterised struct is established vocabulary here
//! (`kernel::level::SubstZ<'a>`, `kernel::inductives::modeled::BlockRename<'a>`).

use con_ron_core::kernel::env;
use con_ron_core::kernel::env::{ConstantVal, Declaration, RecRule, ReducibilityHint};
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::Expr;
use con_ron_core::kernel::name::Name;
use con_ron_core::kernel::prop_when;
use con_ron_core::ron::hashmap::HashMap;
use con_ron_core::ron::ptr::P;

/// con-leche: ConLeche/Frontend/InModel/Mutual.lean:81-90 IndTypeRec
/// One inductive type of a parsed block, with the export's shape data.
pub struct IndTypeRec {
    pub cv: ConstantVal,
    pub n_p: u64,
    pub n_idx: u64,
    pub ctors: Vec<Name>,
    pub is_rec: bool,
    pub is_reflexive: bool,
    pub num_nested: u64,
}

/// con-leche: none — `IndTypeRec` derives nothing (DESIGN.md §3.4); the
/// house-style explicit copy.
pub fn ind_type_rec_dup(t: &IndTypeRec) -> IndTypeRec {
    IndTypeRec {
        cv: env::constant_val_dup(&t.cv),
        n_p: t.n_p,
        n_idx: t.n_idx,
        ctors: prop_when::names_copy(&t.ctors),
        is_rec: t.is_rec,
        is_reflexive: t.is_reflexive,
        num_nested: t.num_nested,
    }
}

/// con-leche: ConLeche/Frontend/InModel/Mutual.lean:92-97 IndCtorRec
/// One constructor of a parsed block.
pub struct IndCtorRec {
    pub cv: ConstantVal,
    pub n_p: u64,
    pub n_f: u64,
}

/// con-leche: none — `IndCtorRec` derives nothing (DESIGN.md §3.4).
pub fn ind_ctor_rec_dup(c: &IndCtorRec) -> IndCtorRec {
    IndCtorRec {
        cv: env::constant_val_dup(&c.cv),
        n_p: c.n_p,
        n_f: c.n_f,
    }
}

/// con-leche: ConLeche/Frontend/InModel/Mutual.lean:99-108 IndRecRec
/// One recursor of a parsed block (`numParams`, `numMotives`, `numMinors`,
/// `numIndices` as exported).
pub struct IndRecRec {
    pub cv: ConstantVal,
    pub n_p: u64,
    pub n_m: u64,
    pub nm: u64,
    pub n_i: u64,
    pub rules: Vec<RecRule>,
}

/// con-leche: none — `IndRecRec` derives nothing (DESIGN.md §3.4).
pub fn ind_rec_rec_dup(r: &IndRecRec) -> IndRecRec {
    IndRecRec {
        cv: env::constant_val_dup(&r.cv),
        n_p: r.n_p,
        n_m: r.n_m,
        nm: r.nm,
        n_i: r.n_i,
        rules: rec_rules_dup(&r.rules),
    }
}

/// con-leche: ConLeche/Frontend/InModel/Mutual.lean:110-115 BlockRec
/// A parsed inductive block.
pub struct BlockRec {
    pub types: Vec<IndTypeRec>,
    pub ctors: Vec<IndCtorRec>,
    pub recs: Vec<IndRecRec>,
}

/// con-leche: none — `BlockRec` derives nothing (DESIGN.md §3.4).  The parse
/// itself never needs this — a block is shared through `ron::ptr::P` — but the
/// record is public data and the core spells a copy out per type.
pub fn block_rec_dup(b: &BlockRec) -> BlockRec {
    BlockRec {
        types: ind_type_recs_dup(&b.types),
        ctors: ind_ctor_recs_dup(&b.ctors),
        recs: ind_rec_recs_dup(&b.recs),
    }
}

/// con-leche: none — `List.map RecRule.dup`, which §3.4 forbids as an
/// iterator adapter; `frontend/` may loop (task #84).
fn rec_rules_dup(rs: &Vec<RecRule>) -> Vec<RecRule> {
    let mut out: Vec<RecRule> = Vec::with_capacity(rs.len());
    let n = rs.len();
    let mut i = 0usize;
    while i < n {
        out.push(env::rec_rule_dup(&rs[i]));
        i += 1;
    }
    out
}

/// con-leche: none — `List.map IndTypeRec.dup` (see `rec_rules_dup`).
fn ind_type_recs_dup(ts: &Vec<IndTypeRec>) -> Vec<IndTypeRec> {
    let mut out: Vec<IndTypeRec> = Vec::with_capacity(ts.len());
    let n = ts.len();
    let mut i = 0usize;
    while i < n {
        out.push(ind_type_rec_dup(&ts[i]));
        i += 1;
    }
    out
}

/// con-leche: none — `List.map IndCtorRec.dup` (see `rec_rules_dup`).
fn ind_ctor_recs_dup(cs: &Vec<IndCtorRec>) -> Vec<IndCtorRec> {
    let mut out: Vec<IndCtorRec> = Vec::with_capacity(cs.len());
    let n = cs.len();
    let mut i = 0usize;
    while i < n {
        out.push(ind_ctor_rec_dup(&cs[i]));
        i += 1;
    }
    out
}

/// con-leche: none — `List.map IndRecRec.dup` (see `rec_rules_dup`).
fn ind_rec_recs_dup(rs: &Vec<IndRecRec>) -> Vec<IndRecRec> {
    let mut out: Vec<IndRecRec> = Vec::with_capacity(rs.len());
    let n = rs.len();
    let mut i = 0usize;
    while i < n {
        out.push(ind_rec_rec_dup(&rs[i]));
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:522-525 hintHeight
/// The height a hint records.  It is `InModel`'s, and the parse needs it at
/// one place only — `export_c::note_decl_entries`, which books a pushed
/// definition's height for the generator's hint arithmetic — so the seam
/// carries it rather than the core growing a copy of `Kit`.
pub fn hint_height(h: &ReducibilityHint) -> u64 {
    match h {
        ReducibilityHint::Regular(n) => *n,
        ReducibilityHint::Abbrev => 0,
        ReducibilityHint::Opaque => 0,
    }
}

/// con-leche: ConLeche/Frontend/InModel.lean:34-37 wants
/// Is the block one this modeller is for: mutual (several types) or nested
/// (`numNested > 0`)?
pub fn wants(b: &BlockRec) -> bool {
    if b.types.len() > 1 {
        return true;
    }
    let n = b.types.len();
    let mut i = 0usize;
    while i < n {
        if b.types[i].num_nested > 0 {
            return true;
        }
        i += 1;
    }
    false
}

/// con-leche: ConLeche/Frontend/InModel/Mutual.lean:117-124 Ctx
/// What the generator reads besides the block: the declared types of the
/// constants so far, the definitional heights, and the parsed inductive
/// blocks so far by member type name (the nested rung reads a container's
/// shape off it).
///
/// Deviation: con-leche's three fields are functions closing over the parse
/// state.  The core owns the tables, closures are out (DESIGN.md §3.4), so
/// this borrows the three tables and `ctx_tbl`/`ctx_height`/`ctx_block` below
/// are the three lambdas of `ExportC.lean:604-605`.
pub struct ModelCtx<'a> {
    pub tbl: &'a HashMap<Name, (Vec<Name>, Expr)>,
    pub heights: &'a HashMap<Name, u64>,
    pub blocks: &'a HashMap<Name, P<BlockRec>>,
}

/// con-leche: ConLeche/Frontend/ExportC.lean:603-607 _
/// The cited `fun n => st.constTypes[n]?`: a constant's level parameters and
/// declared type, if the parse has pushed it.
pub fn ctx_tbl<'a>(ctx: &'a ModelCtx<'a>, n: &Name) -> Option<(Vec<Name>, Expr)> {
    match ctx.tbl.get(n) {
        None => None,
        Some(e) => Some((prop_when::names_copy(&e.0), expr::dup(&e.1))),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:603-607 _
/// The cited `fun n => st.heights.getD n 0`: a definition's height, `0` when
/// the parse has not pushed a definition of that name.
pub fn ctx_height(ctx: &ModelCtx, n: &Name) -> u64 {
    match ctx.heights.get(n) {
        None => 0,
        Some(h) => *h,
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:603-607 _
/// The cited `fun n => st.indBlocks[n]?`: the parsed block a member type name
/// belongs to.
pub fn ctx_block<'a>(ctx: &'a ModelCtx<'a>, n: &Name) -> Option<&'a BlockRec> {
    match ctx.blocks.get(n) {
        None => None,
        Some(p) => Some(&**p),
    }
}

/// con-leche: ConLeche/Frontend/InModel.lean:39-45 generate
/// **The modeller seam.**  Generate the model records of a block, in stream
/// order, or the reason the block is declined.
///
/// The implementation is `crates/con-ron/src/in_model/`, outside the core and
/// outside the extraction: this trait is all the parse knows of it.  On a type
/// parameter it extracts as a typeclass field — an opaque function — so the
/// extracted parse is quantified over an arbitrary modeller.
pub trait Modeller {
    /// con-leche: ConLeche/Frontend/InModel.lean:39-45 generate
    /// The one method: the block's model records, or the decline's text.
    fn generate(&self, ctx: &ModelCtx, b: &BlockRec) -> Result<Vec<Declaration>, Vec<u32>>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use con_ron_core::kernel::env::ConstantVal;
    use con_ron_core::kernel::name;

    fn cp(t: &str) -> Vec<u32> {
        t.chars().map(|c| c as u32).collect()
    }

    fn nm(s: &str) -> Name {
        name::mk_str(name::anonymous(), cp(s))
    }

    fn ty_rec(s: &str, nested: u64) -> IndTypeRec {
        IndTypeRec {
            cv: ConstantVal {
                name: nm(s),
                level_params: Vec::new(),
                ty: expr::sort(con_ron_core::kernel::level::zero()),
            },
            n_p: 0,
            n_idx: 0,
            ctors: Vec::new(),
            is_rec: false,
            is_reflexive: false,
            num_nested: nested,
        }
    }

    fn block(ts: Vec<IndTypeRec>) -> BlockRec {
        BlockRec {
            types: ts,
            ctors: Vec::new(),
            recs: Vec::new(),
        }
    }

    /// `wants` is "several types, or some type nested".
    #[test]
    fn wants_is_mutual_or_nested() {
        assert!(!wants(&block(Vec::new())));
        assert!(!wants(&block(vec![ty_rec("T", 0)])));
        assert!(wants(&block(vec![ty_rec("T", 1)])));
        assert!(wants(&block(vec![ty_rec("T", 0), ty_rec("U", 0)])));
    }

    /// The three readers are the three lambdas: a table hit, a defaulted
    /// height, a block by member name.
    #[test]
    fn the_ctx_readers_read_the_tables() {
        let mut tbl: HashMap<Name, (Vec<Name>, Expr)> = HashMap::new();
        tbl.insert(
            nm("A"),
            (Vec::new(), expr::sort(con_ron_core::kernel::level::zero())),
        );
        let mut heights: HashMap<Name, u64> = HashMap::new();
        heights.insert(nm("A"), 7);
        let mut blocks: HashMap<Name, P<BlockRec>> = HashMap::new();
        blocks.insert(nm("T"), con_ron_core::ron::ptr::new(block(vec![ty_rec("T", 0)])));
        let ctx = ModelCtx {
            tbl: &tbl,
            heights: &heights,
            blocks: &blocks,
        };
        assert!(ctx_tbl(&ctx, &nm("A")).is_some());
        assert!(ctx_tbl(&ctx, &nm("B")).is_none());
        assert_eq!(ctx_height(&ctx, &nm("A")), 7);
        assert_eq!(ctx_height(&ctx, &nm("B")), 0);
        assert_eq!(ctx_block(&ctx, &nm("T")).map(|b| b.types.len()), Some(1));
        assert!(ctx_block(&ctx, &nm("U")).is_none());
    }

    /// `hint_height` reads a `Regular` hint and zeroes the other two.
    #[test]
    fn hint_height_reads_regular() {
        assert_eq!(hint_height(&ReducibilityHint::Regular(4)), 4);
        assert_eq!(hint_height(&ReducibilityHint::Abbrev), 0);
        assert_eq!(hint_height(&ReducibilityHint::Opaque), 0);
    }

    /// The explicit copies are structural.
    #[test]
    fn the_dups_copy() {
        let b = block(vec![ty_rec("T", 2)]);
        let c = block_rec_dup(&b);
        assert_eq!(c.types.len(), 1);
        assert_eq!(c.types[0].num_nested, 2);
        let x = ind_ctor_rec_dup(&IndCtorRec {
            cv: ConstantVal {
                name: nm("mk"),
                level_params: Vec::new(),
                ty: expr::sort(con_ron_core::kernel::level::zero()),
            },
            n_p: 1,
            n_f: 2,
        });
        assert_eq!((x.n_p, x.n_f), (1, 2));
    }
}

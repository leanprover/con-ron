//! `ConLeche/Frontend/InModel.lean` — **the modeller seam, instantiated by
//! delegation** (DESIGN.md §8.2, task #97 P4f), the Rust side of the Lean
//! twin's `proof/ConRon/Arena/Frontend/InModel.lean`.
//!
//! `con_ron_core::frontend::types::Modeller` is the arena's one-method seam:
//! handles in, handles out.  What fills it here is **`crates/con-ron`'s own
//! in-process modeller, unchanged** — the 6 200 lines of
//! `crate::in_model::{kit, mutual, nested}` that the shipping binary runs —
//! with a readback in front of it and an intern behind it:
//!
//! ```text
//! BlockRec over handles  --denote-->  con-ron-core's BlockRec (Expr trees)
//!                                       |  crate::in_model::generate
//!                                       v
//! Vec<IDeclaration>      <--intern--  Vec<Declaration>
//! ```
//!
//! **This is the twin's own instantiation, one representation down.**  The
//! Lean reads the block back, calls *con-leche's* generator and interns what
//! comes out; the Rust reads the block back, calls *con-ron's port of that
//! generator* and interns what comes out.  So the two binaries of the
//! differential sweep run the SAME unverified modeller: `con-ron` calls it on
//! the trees its parser builds, `con-ron` calls it on the trees this
//! module reads back out of the store.  A block modelled differently by the
//! two would be a difference the sweep could not attribute, and there is now
//! no way for one to arise.
//!
//! **Nothing here is verified and nothing here needs to be** (DESIGN.md §8.2,
//! and con-leche's own module note): a wrong generated record is rejected or
//! declined by the fold, never accepted, so this layer decides *coverage* and
//! not soundness.  It is outside `scripts/lint-rust-style.sh` and outside the
//! extraction, exactly as `crate::in_model` is.
//!
//! ## The three things that make it cheap
//!
//! 1. **The readback is memoised on the handle** for the length of one
//!    `generate` call, so the export's sharing survives it: a term interned
//!    once is read back once per call, whatever number of the block's records
//!    (and of the context's answers) mention it.  The Lean twin memoises for
//!    the same reason ("an unmemoised readback unfolds the DAG, which on
//!    `tower_struct` does not finish"), and at the same extent: its
//!    `denoteBlockRec` starts at an empty memo per call.  Here the memo is a
//!    plain `std::collections::HashMap<u32, Expr>` keyed by the handle word,
//!    and `Expr` is a counted pointer (DESIGN.md §3.2), so a hit is one bump.
//!
//!    **Per call, not per run** (task #97-T2-LOCKSTEP lane Frontend round 3,
//!    the coordinator's ruling): a memo that outlives the call is sound only
//!    while every entry is the readback in the CURRENT store — true along a
//!    run, false at the arbitrary related state the capstone's
//!    `ModellerRefines` hypothesis quantifies over.  Per call, `InProcess` is
//!    a function of `(pers, store, ctx, block)`, which is what that
//!    hypothesis says of it.  The memo across calls saved nothing measurable
//!    (DESIGN.md, the round's section: `init`/`core`/`mathlib` parses within
//!    ±0.002 % of `instructions:u`).
//! 2. **The context is three CLOSURES, not three tables.**  con-leche's
//!    `InModel.Ctx` is `Name → …` and `crate::in_model::mutual::Ctx` is
//!    three `dyn Fn`s, so a name the generator never asks about is never read
//!    back.  Reading the parse's whole constant table back per block would be
//!    a second tree parse of the stream, which is the one thing DESIGN.md §8.3
//!    forbids.  (`crate::tree::in_model_rec::ModelCtx`'s three
//!    borrowed maps are the seam the core's own parse uses; this module goes
//!    under it, straight to `crate::in_model::generate`.)
//! 3. **Only a block `wants` routes here is read back at all** — mutual, or
//!    nested.  The stream is never read back.
//!
//! ## `blocks`: per call, one slot per block of the context
//!
//! `Ctx::blocks` is `&dyn Fn(&Name) -> Option<&BlockRec>`: it hands the
//! generator a *reference* to a parsed block, because the core's own parse has
//! one to hand.  Here the tree block does not exist until it is asked for, so
//! the readback builds it into a slot that lives as long as the call: a
//! `Vec<OnceCell<Box<BlockRec>>>` with one cell per block of the context,
//! allocated at the call's first ask (never resized, so a cell is never moved
//! and `OnceCell::get_or_init` hands out a reference of the call's lifetime),
//! and a per-call map from the handle word to the tree already built.
//!
//! **Why per call and not per run** (task #97-T2-LOCKSTEP lane Frontend
//! round 3): until then the tree blocks were `Box::leak`ed into a cache that
//! lived as long as the modeller, keyed by the member type's name handle and
//! never invalidated.  `export_c::note_ind_blocks` OVERWRITES the context's
//! entry at a name when a second inductive record declares a type of the same
//! name, so the cache served the first block where the twin's `ctxOf`
//! (`Arena/Frontend/InModel.lean`), which reads `ctx.blocks h` afresh at every
//! call, reads the second — a divergence at the seam the capstone's
//! `ModellerRefines` hypothesis states.  Within one call the context and the
//! store are fixed, so a per-call slot cannot disagree with the twin.
//!
//! ## The generator itself lives under this file
//!
//! `in_model::{kit, mutual, nested}` are `ConLeche/Frontend/InModel/*`'s own
//! three modules, ported at task #37 and untouched by the arena campaign:
//! they build `Expr` trees, which is exactly what `generate` below is handed
//! and what the intern turns back into handles.  Task #97-SWAP moved the
//! adapter on top of them and retired the `Expr`-tree parser's own seam
//! (`frontend::in_model_rec`'s `Modeller`), so there is one seam now and it
//! is `crate::frontend::types::Modeller`.
//!
//! **`ConLeche/Frontend/InModelDump.lean` is not ported.**  It is the
//! `CON_LECHE_INMODEL_DUMP=OUT` debug path: a copy of the raw input with the
//! generated records spliced in ahead of their block, written through
//! `Frontend/ExportWrite.lean`'s `ExportWriter`.  It is not on the checking
//! path (its own header says so), and the writer it is built on is the one
//! source file task #37 deliberately left out — an output format, not
//! something a checker reads.  So con-ron has no `--inmodel-dump`, and
//! `StateD.inModelGen`, the array that feeds it, stays unported too.
//!
//! `InModel.wants` is ported in `con_ron_core::frontend::export_c`
//! (`in_model_wants`), where the call site is: its two fields are the scan
//! record's own, so the test needs neither `BlockRec` nor `blockRecOf`.

pub mod kit;
pub mod mutual;
pub mod nested;

use std::cell::{OnceCell, RefCell};
use std::collections::HashMap;

use con_ron_core::arena::env::{IConstantVal, IDeclaration, IRecRule, IRecRuleFire};
use con_ron_core::arena::handle::{EIdx, LIdx, LsIdx, NIdx};
use con_ron_core::arena::monad::AState;
use con_ron_core::arena::store::{ENodeView, EStore, LNodeView, NNodeView};
use con_ron_core::frontend::types::{
    BlockRec as IBlockRec, MIndCtorRec, MIndRecRec, MIndTypeRec, ModelCtx, Modeller,
};

use con_ron_core::kernel::env::{ConstantVal, Declaration, RecRule, RecRuleFire};
use con_ron_core::kernel::expr::Expr;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::name::{Name, NameKind};
use con_ron_core::kernel::{expr, level, name};

use crate::in_model::mutual::{BlockRec, Ctx, IndCtorRec, IndRecRec, IndTypeRec};
use con_ron_core::arena::store::PersTier;

/// con-leche: none — the seam's instantiation (task #97 P4f); Lean twin: proof/ConRon/Arena/Frontend/InModel.lean:187-213 inProcessModeller
/// **The modeller the binary passes**: `crate::in_model`'s generator behind
/// the arena's handle seam.  It carries NO state: the readback memo and the
/// tree blocks `Ctx::blocks` must return a reference to live for one
/// `generate` call (the module note).
pub struct InProcess {}

/// con-leche: none — the seam's instantiation (task #97 P4f); Lean twin: proof/ConRon/Arena/Frontend/InModel.lean:187-213 inProcessModeller
impl InProcess {
    /// con-leche: none — the seam's instantiation (task #97 P4f)
    /// The modeller (stateless).
    pub fn new() -> InProcess {
        InProcess {}
    }
}

/// con-leche: none — the seam's instantiation (task #97 P4f)
impl Default for InProcess {
    /// con-leche: none — the seam's instantiation (task #97 P4f)
    fn default() -> InProcess {
        InProcess::new()
    }
}

// ---------------------------------------------------------------------------
// The readback (`Arena/Frontend/Readback.lean` of the twin, `Denote.lean`'s
// families with a memo)
// ---------------------------------------------------------------------------

/// con-leche: none — the readback of a name handle; Lean twin: proof/ConRon/Arena/Denote.lean:85-88 denoteN
/// A name, read back.  Names are short and the store is shallow, so this one
/// is unmemoised, as the twin's `denoteN` is.
fn read_name(pers: &PersTier, ar: &EStore, h: &NIdx) -> Option<Name> {
    match ar.ns().view(pers, h) {
        None => None,
        Some(NNodeView::Anonymous) => Some(name::anonymous()),
        Some(NNodeView::Str(p, s)) => read_name(pers, ar, &p).map(|q| name::mk_str(q, s)),
        Some(NNodeView::Num(p, k)) => read_name(pers, ar, &p).map(|q| name::mk_num(q, k)),
    }
}

/// con-leche: none — the readback of a name-handle list; Lean twin: proof/ConRon/Arena/Frontend/Readback.lean:92-98 denoteNList
/// A list of names, read back.
fn read_names(pers: &PersTier, ar: &EStore, hs: &[NIdx]) -> Option<Vec<Name>> {
    let mut out: Vec<Name> = Vec::with_capacity(hs.len());
    for h in hs.iter() {
        out.push(read_name(pers, ar, h)?);
    }
    Some(out)
}

/// con-leche: none — the readback of a level handle; Lean twin: proof/ConRon/Arena/Denote.lean:129-132 denoteL
/// A level, read back.
fn read_level(pers: &PersTier, ar: &EStore, h: &LIdx) -> Option<Level> {
    match ar.ls().view(pers, h) {
        None => None,
        Some(LNodeView::Zero) => Some(level::zero()),
        Some(LNodeView::Succ(u)) => read_level(pers, ar, &u).map(level::succ),
        Some(LNodeView::Max(u, v)) => {
            let a = read_level(pers, ar, &u)?;
            let b = read_level(pers, ar, &v)?;
            Some(level::max(a, b))
        }
        Some(LNodeView::Imax(u, v)) => {
            let a = read_level(pers, ar, &u)?;
            let b = read_level(pers, ar, &v)?;
            Some(level::imax(a, b))
        }
        Some(LNodeView::Param(n)) => read_name(pers, ar, &n).map(level::param),
    }
}

/// con-leche: none — the readback of a level-list handle; Lean twin: proof/ConRon/Arena/Denote.lean:173-177 denoteLs
/// An interned level list, read back.
fn read_levels(pers: &PersTier, ar: &EStore, h: &LsIdx) -> Option<Vec<Level>> {
    let us = ar.ls_s().view(pers, h)?;
    let mut out: Vec<Level> = Vec::with_capacity(us.len());
    for u in us.iter() {
        out.push(read_level(pers, ar, u)?);
    }
    Some(out)
}

/// con-leche: none — the readback of a level-handle list; Lean twin: proof/ConRon/Arena/Denote.lean:168-171 denoteLList
/// A `Vec<LIdx>` (a recursor rule's nested levels), read back.
fn read_level_list(pers: &PersTier, ar: &EStore, hs: &[LIdx]) -> Option<Vec<Level>> {
    let mut out: Vec<Level> = Vec::with_capacity(hs.len());
    for h in hs.iter() {
        out.push(read_level(pers, ar, h)?);
    }
    Some(out)
}

/// con-leche: none — the MEMOISED readback of an expression handle; Lean twin: proof/ConRon/Arena/Frontend/Readback.lean:297-302 denoteEShared
/// **The readback that matters**: one `Expr` per handle, whatever the number
/// of parents.  The recursion is on the store's own rank (a child is interned
/// before its parent), so the depth is the term's and the 1 GB stack the
/// driver's thread has is what carries it, as it carries the checker.
fn read_expr(pers: &PersTier, m: &mut HashMap<u32, Expr>, ar: &EStore, h: &EIdx) -> Option<Expr> {
    if let Some(e) = m.get(&h.word) {
        return Some(expr::dup(e));
    }
    let v = ar.view(pers, h)?;
    let e: Expr = match v {
        ENodeView::BVar(k) => expr::bvar(k),
        ENodeView::FVar(k, ty) => expr::fvar(k, read_expr(pers, m, ar, &ty)?),
        ENodeView::Sort(u) => expr::sort(read_level(pers, ar, &u)?),
        ENodeView::Const(n, us) => expr::mk_const(read_name(pers, ar, &n)?, read_levels(pers, ar, &us)?),
        ENodeView::App(f, a) => {
            let x = read_expr(pers, m, ar, &f)?;
            let y = read_expr(pers, m, ar, &a)?;
            expr::app(x, y)
        }
        ENodeView::Lam(ty, b, bm) => {
            let x = read_expr(pers, m, ar, &ty)?;
            let y = read_expr(pers, m, ar, &b)?;
            expr::lam(x, y, bm)
        }
        ENodeView::ForallE(ty, b, bm) => {
            let x = read_expr(pers, m, ar, &ty)?;
            let y = read_expr(pers, m, ar, &b)?;
            expr::forall_e(x, y, bm)
        }
        ENodeView::LetE(ty, val, b) => {
            let x = read_expr(pers, m, ar, &ty)?;
            let y = read_expr(pers, m, ar, &val)?;
            let z = read_expr(pers, m, ar, &b)?;
            expr::let_e(x, y, z)
        }
        ENodeView::Lit(l) => expr::lit(l),
        ENodeView::Proj(n, k, e) => {
            let s = read_name(pers, ar, &n)?;
            let x = read_expr(pers, m, ar, &e)?;
            expr::proj(s, k, x)
        }
    };
    m.insert(h.word, expr::dup(&e));
    Some(e)
}

/// con-leche: none — the readback of a constant value; Lean twin: proof/ConRon/Arena/Frontend/Readback.lean:114-120 denoteCV
/// A `ConstantVal`, read back.
fn read_cv(
    pers: &PersTier,
    m: &mut HashMap<u32, Expr>,
    ar: &EStore,
    cv: &IConstantVal,
) -> Option<ConstantVal>  {
    Some(ConstantVal {
        name: read_name(pers, ar, &cv.name)?,
        level_params: read_names(pers, ar, &cv.level_params)?,
        ty: read_expr(pers, m, ar, &cv.ty)?,
    })
}

/// con-leche: none — the readback of a recursor rule; Lean twin: proof/ConRon/Arena/Frontend/Readback.lean:131-136 denoteRule
/// A `RecRule`, read back, its firing datum included.
fn read_rule(
    pers: &PersTier,
    m: &mut HashMap<u32, Expr>,
    ar: &EStore,
    r: &IRecRule,
) -> Option<RecRule>  {
    let fire = match &r.fire {
        IRecRuleFire::Inert => RecRuleFire::Inert,
        IRecRuleFire::Plain => RecRuleFire::Plain,
        IRecRuleFire::Nested(us, pins) => {
            let ls = read_level_list(pers, ar, us)?;
            let mut ps: Vec<Expr> = Vec::with_capacity(pins.len());
            for p in pins.iter() {
                ps.push(read_expr(pers, m, ar, p)?);
            }
            RecRuleFire::Nested(ls, ps)
        }
    };
    Some(RecRule {
        ctor: read_name(pers, ar, &r.ctor)?,
        nfields: r.nfields,
        ctor_params: r.ctor_params,
        fire,
        rhs: read_expr(pers, m, ar, &r.rhs)?,
        k: r.k,
        eta: r.eta,
        params_blind: r.params_blind,
    })
}

/// con-leche: none — the readback of one type former of a parsed block; Lean twin: proof/ConRon/Arena/Frontend/InModel.lean:66-74 denoteMTypeGo
fn read_type(
    pers: &PersTier,
    m: &mut HashMap<u32, Expr>,
    ar: &EStore,
    t: &MIndTypeRec,
) -> Option<IndTypeRec>  {
    Some(IndTypeRec {
        cv: read_cv(pers, m, ar, &t.cv)?,
        n_p: t.n_p,
        n_idx: t.n_idx,
        ctors: read_names(pers, ar, &t.ctors)?,
        is_rec: t.is_rec,
        is_reflexive: t.is_reflexive,
        num_nested: t.num_nested,
    })
}

/// con-leche: none — the readback of one constructor of a parsed block; Lean twin: proof/ConRon/Arena/Frontend/InModel.lean:88-93 denoteMCtorGo
fn read_ctor(
    pers: &PersTier,
    m: &mut HashMap<u32, Expr>,
    ar: &EStore,
    c: &MIndCtorRec,
) -> Option<IndCtorRec>  {
    Some(IndCtorRec {
        cv: read_cv(pers, m, ar, &c.cv)?,
        n_p: c.n_p,
        n_f: c.n_f,
    })
}

/// con-leche: none — the readback of one recursor of a parsed block; Lean twin: proof/ConRon/Arena/Frontend/InModel.lean:107-115 denoteMRecGo
fn read_rec(
    pers: &PersTier,
    m: &mut HashMap<u32, Expr>,
    ar: &EStore,
    r: &MIndRecRec,
) -> Option<IndRecRec>  {
    let mut rules: Vec<RecRule> = Vec::with_capacity(r.rules.len());
    for rl in r.rules.iter() {
        rules.push(read_rule(pers, m, ar, rl)?);
    }
    Some(IndRecRec {
        cv: read_cv(pers, m, ar, &r.cv)?,
        n_p: r.n_p,
        n_m: r.n_m,
        nm: r.nm,
        n_i: r.n_i,
        rules,
    })
}

/// con-leche: none — the readback of a parsed inductive block; Lean twin: proof/ConRon/Arena/Frontend/InModel.lean:144-149 denoteBlockRec
/// The block the generator takes.  One memo for the whole block (and the
/// whole `generate` call), so the sharing between its types, constructors and
/// recursors survives the readback.
fn read_block(
    pers: &PersTier,
    m: &mut HashMap<u32, Expr>,
    ar: &EStore,
    b: &IBlockRec,
) -> Option<BlockRec>  {
    let mut types: Vec<IndTypeRec> = Vec::with_capacity(b.types.len());
    for t in b.types.iter() {
        types.push(read_type(pers, m, ar, t)?);
    }
    let mut ctors: Vec<IndCtorRec> = Vec::with_capacity(b.ctors.len());
    for c in b.ctors.iter() {
        ctors.push(read_ctor(pers, m, ar, c)?);
    }
    let mut recs: Vec<IndRecRec> = Vec::with_capacity(b.recs.len());
    for r in b.recs.iter() {
        recs.push(read_rec(pers, m, ar, r)?);
    }
    Some(BlockRec {
        types,
        ctors,
        recs,
    })
}

// ---------------------------------------------------------------------------
// The context: a name, back to its handle
// ---------------------------------------------------------------------------

/// con-leche: none — the store probe behind the context's three closures; Lean twin: proof/ConRon/Arena/Frontend/InModel.lean:159-183 ctxOf
/// The cited `nameHandle?`: the handle of a name the store has already
/// interned, **without interning it**.  A name the store has never seen is a
/// name no declaration carries, so `None` here is the right answer and not a
/// failure — which is exactly what the twin's `nameHandle?` says.  It is
/// `NStore::find` up the prefix chain, the cons table's own probe.
fn name_handle(pers: &PersTier, ar: &EStore, n: &Name) -> Option<NIdx> {
    match &n.0.kind {
        NameKind::Anonymous => ar.ns().find(pers, &NNodeView::Anonymous),
        NameKind::Str(p, s) => {
            let h = name_handle(pers, ar, p)?;
            ar.ns().find(pers, &NNodeView::Str(h, s.clone()))
        }
        NameKind::Num(p, k) => {
            let h = name_handle(pers, ar, p)?;
            ar.ns().find(pers, &NNodeView::Num(h, *k))
        }
    }
}

// ---------------------------------------------------------------------------
// The seam
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/InModel.lean:39-45 generate
/// **The modeller, by delegation** (the module note): the block read back,
/// `crate::in_model::generate` run on it — the same function the `con-ron`
/// binary runs — and the declarations it returns interned into the tier the
/// parse is in, which is the persistent one.
impl Modeller for InProcess {
    /// con-leche: ConLeche/Frontend/InModel.lean:39-45 generate
    /// The one method.  The immutable half (readback, generate) is a block of
    /// its own, so the `&mut EStore` the intern needs is free by the time the
    /// generator has answered.
    fn generate(
        &self,
    pers: &PersTier,
        ar: &mut EStore,
        ctx: &ModelCtx,
        b: &IBlockRec,
    ) -> Result<Vec<IDeclaration>, Vec<u32>> {
        let gen: Result<Vec<Declaration>, String> = {
            let store: &EStore = ar;
            // The readback memo of this call (module note, item 1).
            let memo: RefCell<HashMap<u32, Expr>> = RefCell::new(HashMap::new());
            // The tree blocks of this call (module note, `blocks`): one cell
            // per block of the context, allocated at the first ask (only the
            // nested rung asks); `seen` maps a handle word to its tree, and
            // its size is the next free cell.
            let slots: OnceCell<Vec<OnceCell<Box<BlockRec>>>> = OnceCell::new();
            let seen: RefCell<HashMap<u32, &BlockRec>> = RefCell::new(HashMap::new());
            let bp = match read_block(pers, &mut memo.borrow_mut(), store, b) {
                Some(x) => x,
                None => return Err(cps("arena: dangling handle in a modelled block")),
            };
            // The three closures of `ctxOf`: a name to its handle, the arena's
            // own context at that handle, the answer read back.
            let tbl = |n: &Name| -> Option<(Vec<Name>, Expr)> {
                let h = name_handle(pers, store, n)?;
                let (lps, ty) = con_ron_core::frontend::types::ctx_tbl(ctx, &h)?;
                let ls = read_names(pers, store, lps)?;
                let t = read_expr(pers, &mut memo.borrow_mut(), store, ty)?;
                Some((ls, t))
            };
            let hs = |n: &Name| -> u64 {
                match name_handle(pers, store, n) {
                    None => 0,
                    Some(h) => con_ron_core::frontend::types::ctx_height(ctx, &h),
                }
            };
            let bl = |n: &Name| -> Option<&BlockRec> {
                let h = name_handle(pers, store, n)?;
                if let Some(r) = seen.borrow().get(&h.word) {
                    return Some(*r);
                }
                let ib = con_ron_core::frontend::types::ctx_block(ctx, &h)?;
                let cells = slots.get_or_init(|| (0..ctx.blocks.len()).map(|_| OnceCell::new()).collect());
                // A handle is entered once, and only at a block of the
                // context, so there are at most `ctx.blocks.len()` entries
                // and `get` cannot miss.
                let i: usize = seen.borrow().len();
                let cell: &OnceCell<Box<BlockRec>> = cells.get(i)?;
                let tree = read_block(pers, &mut memo.borrow_mut(), store, ib)?;
                let r: &BlockRec = cell.get_or_init(|| Box::new(tree));
                seen.borrow_mut().insert(h.word, r);
                Some(r)
            };
            let c = Ctx {
                tbl: &tbl,
                heights: &hs,
                blocks: &bl,
            };
            crate::in_model::generate(&c, &bp)
        };
        let ds: Vec<Declaration> = match gen {
            Ok(ds) => ds,
            Err(why) => return Err(why.chars().map(|ch| ch as u32).collect()),
        };
        // …and back into the store.  `intern_decls` takes the whole `AState`
        // (it is `Readback.lean`'s `internDecls`, which is in `AM`), so the
        // store is lent to one for the call and taken back after it: the
        // memo tables an `AState::init` brings are empty and stay empty, the
        // intern touching nothing but the store and its cons tables.
        let mut ast = AState::init(std::mem::replace(ar, EStore::empty()));
        let r = con_ron_core::arena::intern::intern_decls(pers, &mut ast, &ds);
        *ar = ast.store;
        // An intern failure (a table at capacity) is NOT a decline: the
        // twin's `internDecls` throws, and `AM`'s throw (`StateT AState
        // (Except CheckError)`) has no state to resume at, so no twin run
        // leaves the partly-interned store this call would keep.  The seam's
        // error is a message and cannot say `Native`, so the port stops here
        // — no verdict, which is what the twin's throw means (task
        // #97-T2-LOCKSTEP lane Frontend round 3, the coordinator's ruling c2).
        match r {
            Ok(hs) => Ok(hs),
            Err(e) => panic!("in-process modeller: interning the generated records failed: {}", crate::driver::message(&e)),
        }
    }
}

/// con-leche: none — a message as code points (DESIGN.md §3.3)
fn cps(s: &str) -> Vec<u32> {
    s.chars().map(|c| c as u32).collect()
}

/// con-leche: ConLeche/Frontend/InModel.lean:39-45 generate
/// Generate the model records of a block, in stream order, or the reason the
/// block is declined.
pub fn generate(ctx: &Ctx, b: &BlockRec) -> Result<Vec<Declaration>, String> {
    if b.types.iter().any(|t| t.num_nested > 0) {
        nested::gen_nested(ctx, b)
    } else {
        mutual::gen_mutual(ctx, b)
    }
}

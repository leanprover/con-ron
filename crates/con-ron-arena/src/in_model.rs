//! `ConLeche/Frontend/InModel.lean` — **the modeller seam, instantiated by
//! delegation** (DESIGN.md §8.2, task #97 P4f), the Rust side of the Lean
//! twin's `proof/ConRon/Arena/Frontend/InModel.lean`.
//!
//! `arena_core::frontend::types::Modeller` is the arena's one-method seam:
//! handles in, handles out.  What fills it here is **`crates/con-ron`'s own
//! in-process modeller, unchanged** — the 6 200 lines of
//! `con_ron::in_model::{kit, mutual, nested}` that the shipping binary runs —
//! with a readback in front of it and an intern behind it:
//!
//! ```text
//! BlockRec over handles  --denote-->  con-ron-core's BlockRec (Expr trees)
//!                                       |  con_ron::in_model::generate
//!                                       v
//! Vec<IDeclaration>      <--intern--  Vec<Declaration>
//! ```
//!
//! **This is the twin's own instantiation, one representation down.**  The
//! Lean reads the block back, calls *con-leche's* generator and interns what
//! comes out; the Rust reads the block back, calls *con-ron's port of that
//! generator* and interns what comes out.  So the two binaries of the
//! differential sweep run the SAME unverified modeller: `con-ron` calls it on
//! the trees its parser builds, `con-ron-arena` calls it on the trees this
//! module reads back out of the store.  A block modelled differently by the
//! two would be a difference the sweep could not attribute, and there is now
//! no way for one to arise.
//!
//! **Nothing here is verified and nothing here needs to be** (DESIGN.md §8.2,
//! and con-leche's own module note): a wrong generated record is rejected or
//! declined by the fold, never accepted, so this layer decides *coverage* and
//! not soundness.  It is outside `scripts/lint-rust-style.sh` and outside the
//! extraction, exactly as `con_ron::in_model` is.
//!
//! ## The three things that make it cheap
//!
//! 1. **The readback is memoised on the handle** and the memo lives as long as
//!    the modeller, so the export's sharing survives it: a term interned once
//!    is read back once, whatever number of blocks mention it.  The Lean twin
//!    memoises for the same reason ("an unmemoised readback unfolds the DAG,
//!    which on `tower_struct` does not finish"); here the memo is a plain
//!    `std::collections::HashMap<u32, Expr>` keyed by the handle word, and
//!    `Expr` is a counted pointer (DESIGN.md §3.2), so a hit is one bump.
//! 2. **The context is three CLOSURES, not three tables.**  con-leche's
//!    `InModel.Ctx` is `Name → …` and `con_ron::in_model::mutual::Ctx` is
//!    three `dyn Fn`s, so a name the generator never asks about is never read
//!    back.  Reading the parse's whole constant table back per block would be
//!    a second tree parse of the stream, which is the one thing DESIGN.md §8.3
//!    forbids.  (`con_ron_core::frontend::in_model_rec::ModelCtx`'s three
//!    borrowed maps are the seam the core's own parse uses; this module goes
//!    under it, straight to `con_ron::in_model::generate`.)
//! 3. **Only a block `wants` routes here is read back at all** — mutual, or
//!    nested.  The stream is never read back.
//!
//! ## `blocks` and the leak
//!
//! `Ctx::blocks` is `&dyn Fn(&Name) -> Option<&BlockRec>`: it hands the
//! generator a *reference* to a parsed block, because the core's own parse has
//! one to hand.  Here the tree block does not exist until it is asked for, so
//! the readback allocates it and `Box::leak`s it into a `&'static BlockRec`,
//! remembering it by handle word.  Safe Rust, and bounded by the number of
//! DISTINCT blocks the nested rung asks about across a run — a handful (the
//! containers a nested block recurses through), each read back once.

use std::cell::RefCell;
use std::collections::HashMap;

use arena_core::arena::env::{IConstantVal, IDeclaration, IRecRule, IRecRuleFire};
use arena_core::arena::handle::{EIdx, LIdx, LsIdx, NIdx};
use arena_core::arena::monad::AState;
use arena_core::arena::store::{ENodeView, EStore, LNodeView, NNodeView};
use arena_core::frontend::types::{
    BlockRec as IBlockRec, MIndCtorRec, MIndRecRec, MIndTypeRec, ModelCtx, Modeller,
};

use con_ron_core::kernel::env::{ConstantVal, Declaration, RecRule, RecRuleFire};
use con_ron_core::kernel::expr::Expr;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::name::{Name, NameKind};
use con_ron_core::kernel::{expr, level, name};

use con_ron::in_model::mutual::{BlockRec, Ctx, IndCtorRec, IndRecRec, IndTypeRec};

/// con-leche: none — the seam's instantiation (task #97 P4f); Lean twin: proof/ConRon/Arena/Frontend/InModel.lean:196-206 inProcessModeller
/// **The modeller the binary passes**: `con_ron::in_model`'s generator behind
/// the arena's handle seam.  The two caches are the module note's — the
/// readback memo, and the leaked tree blocks `Ctx::blocks` must return a
/// reference to.
pub struct InProcess {
    /// The readback memo, keyed by the expression handle's word.  Handles are
    /// stable for the life of the parse (the persistent tier is append-only
    /// and the scratch tier is off), so an entry never goes stale.
    memo: RefCell<HashMap<u32, Expr>>,
    /// The blocks already read back, by the handle word of the member type
    /// name they are keyed on in the parse state.
    blocks: RefCell<HashMap<u32, &'static BlockRec>>,
}

/// con-leche: none — the seam's instantiation (task #97 P4f); Lean twin: proof/ConRon/Arena/Frontend/InModel.lean:196-206 inProcessModeller
impl InProcess {
    /// con-leche: none — the seam's instantiation (task #97 P4f)
    /// A modeller with empty caches.
    pub fn new() -> InProcess {
        InProcess {
            memo: RefCell::new(HashMap::new()),
            blocks: RefCell::new(HashMap::new()),
        }
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

/// con-leche: none — the readback of a name handle; Lean twin: proof/ConRon/Arena/Denote.lean:87-88 denoteN
/// A name, read back.  Names are short and the store is shallow, so this one
/// is unmemoised, as the twin's `denoteN` is.
fn read_name(ar: &EStore, h: &NIdx) -> Option<Name> {
    match ar.ns().view(h) {
        None => None,
        Some(NNodeView::Anonymous) => Some(name::anonymous()),
        Some(NNodeView::Str(p, s)) => read_name(ar, &p).map(|q| name::mk_str(q, s)),
        Some(NNodeView::Num(p, k)) => read_name(ar, &p).map(|q| name::mk_num(q, k)),
    }
}

/// con-leche: none — the readback of a name-handle list; Lean twin: proof/ConRon/Arena/Frontend/Readback.lean denoteNList
/// A list of names, read back.
fn read_names(ar: &EStore, hs: &[NIdx]) -> Option<Vec<Name>> {
    let mut out: Vec<Name> = Vec::with_capacity(hs.len());
    for h in hs.iter() {
        out.push(read_name(ar, h)?);
    }
    Some(out)
}

/// con-leche: none — the readback of a level handle; Lean twin: proof/ConRon/Arena/Denote.lean:99-107 denoteL
/// A level, read back.
fn read_level(ar: &EStore, h: &LIdx) -> Option<Level> {
    match ar.ls().view(h) {
        None => None,
        Some(LNodeView::Zero) => Some(level::zero()),
        Some(LNodeView::Succ(u)) => read_level(ar, &u).map(level::succ),
        Some(LNodeView::Max(u, v)) => {
            let a = read_level(ar, &u)?;
            let b = read_level(ar, &v)?;
            Some(level::max(a, b))
        }
        Some(LNodeView::Imax(u, v)) => {
            let a = read_level(ar, &u)?;
            let b = read_level(ar, &v)?;
            Some(level::imax(a, b))
        }
        Some(LNodeView::Param(n)) => read_name(ar, &n).map(level::param),
    }
}

/// con-leche: none — the readback of a level-list handle; Lean twin: proof/ConRon/Arena/Denote.lean denoteLs
/// An interned level list, read back.
fn read_levels(ar: &EStore, h: &LsIdx) -> Option<Vec<Level>> {
    let us = ar.ls_s().view(h)?;
    let mut out: Vec<Level> = Vec::with_capacity(us.len());
    for u in us.iter() {
        out.push(read_level(ar, u)?);
    }
    Some(out)
}

/// con-leche: none — the readback of a level-handle list; Lean twin: proof/ConRon/Arena/Frontend/Readback.lean denoteLList
/// A `Vec<LIdx>` (a recursor rule's nested levels), read back.
fn read_level_list(ar: &EStore, hs: &[LIdx]) -> Option<Vec<Level>> {
    let mut out: Vec<Level> = Vec::with_capacity(hs.len());
    for h in hs.iter() {
        out.push(read_level(ar, h)?);
    }
    Some(out)
}

/// con-leche: none — the MEMOISED readback of an expression handle; Lean twin: proof/ConRon/Arena/Frontend/Readback.lean:denoteEShared
/// **The readback that matters**: one `Expr` per handle, whatever the number
/// of parents.  The recursion is on the store's own rank (a child is interned
/// before its parent), so the depth is the term's and the 1 GB stack the
/// driver's thread has is what carries it, as it carries the checker.
fn read_expr(m: &mut HashMap<u32, Expr>, ar: &EStore, h: &EIdx) -> Option<Expr> {
    if let Some(e) = m.get(&h.word) {
        return Some(expr::dup(e));
    }
    let v = ar.view(h)?;
    let e: Expr = match v {
        ENodeView::BVar(k) => expr::bvar(k),
        ENodeView::FVar(k, ty) => expr::fvar(k, read_expr(m, ar, &ty)?),
        ENodeView::Sort(u) => expr::sort(read_level(ar, &u)?),
        ENodeView::Const(n, us) => expr::mk_const(read_name(ar, &n)?, read_levels(ar, &us)?),
        ENodeView::App(f, a) => {
            let x = read_expr(m, ar, &f)?;
            let y = read_expr(m, ar, &a)?;
            expr::app(x, y)
        }
        ENodeView::Lam(ty, b, bm) => {
            let x = read_expr(m, ar, &ty)?;
            let y = read_expr(m, ar, &b)?;
            expr::lam(x, y, bm)
        }
        ENodeView::ForallE(ty, b, bm) => {
            let x = read_expr(m, ar, &ty)?;
            let y = read_expr(m, ar, &b)?;
            expr::forall_e(x, y, bm)
        }
        ENodeView::LetE(ty, val, b) => {
            let x = read_expr(m, ar, &ty)?;
            let y = read_expr(m, ar, &val)?;
            let z = read_expr(m, ar, &b)?;
            expr::let_e(x, y, z)
        }
        ENodeView::Lit(l) => expr::lit(l),
        ENodeView::Proj(n, k, e) => {
            let s = read_name(ar, &n)?;
            let x = read_expr(m, ar, &e)?;
            expr::proj(s, k, x)
        }
    };
    m.insert(h.word, expr::dup(&e));
    Some(e)
}

/// con-leche: none — the readback of a constant value; Lean twin: proof/ConRon/Arena/Frontend/Readback.lean denoteCV
/// A `ConstantVal`, read back.
fn read_cv(m: &mut HashMap<u32, Expr>, ar: &EStore, cv: &IConstantVal) -> Option<ConstantVal> {
    Some(ConstantVal {
        name: read_name(ar, &cv.name)?,
        level_params: read_names(ar, &cv.level_params)?,
        ty: read_expr(m, ar, &cv.ty)?,
    })
}

/// con-leche: none — the readback of a recursor rule; Lean twin: proof/ConRon/Arena/Frontend/Readback.lean denoteRule
/// A `RecRule`, read back, its firing datum included.
fn read_rule(m: &mut HashMap<u32, Expr>, ar: &EStore, r: &IRecRule) -> Option<RecRule> {
    let fire = match &r.fire {
        IRecRuleFire::Inert => RecRuleFire::Inert,
        IRecRuleFire::Plain => RecRuleFire::Plain,
        IRecRuleFire::Nested(us, pins) => {
            let ls = read_level_list(ar, us)?;
            let mut ps: Vec<Expr> = Vec::with_capacity(pins.len());
            for p in pins.iter() {
                ps.push(read_expr(m, ar, p)?);
            }
            RecRuleFire::Nested(ls, ps)
        }
    };
    Some(RecRule {
        ctor: read_name(ar, &r.ctor)?,
        nfields: r.nfields,
        ctor_params: r.ctor_params,
        fire,
        rhs: read_expr(m, ar, &r.rhs)?,
        k: r.k,
        eta: r.eta,
        params_blind: r.params_blind,
    })
}

/// con-leche: none — the readback of one type former of a parsed block; Lean twin: proof/ConRon/Arena/Frontend/InModel.lean:66-73 denoteMTypeGo
fn read_type(m: &mut HashMap<u32, Expr>, ar: &EStore, t: &MIndTypeRec) -> Option<IndTypeRec> {
    Some(IndTypeRec {
        cv: read_cv(m, ar, &t.cv)?,
        n_p: t.n_p,
        n_idx: t.n_idx,
        ctors: read_names(ar, &t.ctors)?,
        is_rec: t.is_rec,
        is_reflexive: t.is_reflexive,
        num_nested: t.num_nested,
    })
}

/// con-leche: none — the readback of one constructor of a parsed block; Lean twin: proof/ConRon/Arena/Frontend/InModel.lean:88-93 denoteMCtorGo
fn read_ctor(m: &mut HashMap<u32, Expr>, ar: &EStore, c: &MIndCtorRec) -> Option<IndCtorRec> {
    Some(IndCtorRec {
        cv: read_cv(m, ar, &c.cv)?,
        n_p: c.n_p,
        n_f: c.n_f,
    })
}

/// con-leche: none — the readback of one recursor of a parsed block; Lean twin: proof/ConRon/Arena/Frontend/InModel.lean:107-115 denoteMRecGo
fn read_rec(m: &mut HashMap<u32, Expr>, ar: &EStore, r: &MIndRecRec) -> Option<IndRecRec> {
    let mut rules: Vec<RecRule> = Vec::with_capacity(r.rules.len());
    for rl in r.rules.iter() {
        rules.push(read_rule(m, ar, rl)?);
    }
    Some(IndRecRec {
        cv: read_cv(m, ar, &r.cv)?,
        n_p: r.n_p,
        n_m: r.n_m,
        nm: r.nm,
        n_i: r.n_i,
        rules,
    })
}

/// con-leche: none — the readback of a parsed inductive block; Lean twin: proof/ConRon/Arena/Frontend/InModel.lean:143-148 denoteBlockRec
/// The block the generator takes.  One memo for the whole block *and* for the
/// whole run, so the sharing between its types, constructors and recursors —
/// and between one block and the next — survives the readback.
fn read_block(m: &mut HashMap<u32, Expr>, ar: &EStore, b: &IBlockRec) -> Option<BlockRec> {
    let mut types: Vec<IndTypeRec> = Vec::with_capacity(b.types.len());
    for t in b.types.iter() {
        types.push(read_type(m, ar, t)?);
    }
    let mut ctors: Vec<IndCtorRec> = Vec::with_capacity(b.ctors.len());
    for c in b.ctors.iter() {
        ctors.push(read_ctor(m, ar, c)?);
    }
    let mut recs: Vec<IndRecRec> = Vec::with_capacity(b.recs.len());
    for r in b.recs.iter() {
        recs.push(read_rec(m, ar, r)?);
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

/// con-leche: none — the store probe behind the context's three closures; Lean twin: proof/ConRon/Arena/Frontend/InModel.lean:161-186 ctxOf
/// The cited `nameHandle?`: the handle of a name the store has already
/// interned, **without interning it**.  A name the store has never seen is a
/// name no declaration carries, so `None` here is the right answer and not a
/// failure — which is exactly what the twin's `nameHandle?` says.  It is
/// `NStore::find` up the prefix chain, the cons table's own probe.
fn name_handle(ar: &EStore, n: &Name) -> Option<NIdx> {
    match &n.0.kind {
        NameKind::Anonymous => ar.ns().find(&NNodeView::Anonymous),
        NameKind::Str(p, s) => {
            let h = name_handle(ar, p)?;
            ar.ns().find(&NNodeView::Str(h, s.clone()))
        }
        NameKind::Num(p, k) => {
            let h = name_handle(ar, p)?;
            ar.ns().find(&NNodeView::Num(h, *k))
        }
    }
}

// ---------------------------------------------------------------------------
// The seam
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/InModel.lean:39-45 generate
/// **The modeller, by delegation** (the module note): the block read back,
/// `con_ron::in_model::generate` run on it — the same function the `con-ron`
/// binary runs — and the declarations it returns interned into the tier the
/// parse is in, which is the persistent one.
impl Modeller for InProcess {
    /// con-leche: ConLeche/Frontend/InModel.lean:39-45 generate
    /// The one method.  The immutable half (readback, generate) is a block of
    /// its own, so the `&mut EStore` the intern needs is free by the time the
    /// generator has answered.
    fn generate(
        &self,
        ar: &mut EStore,
        ctx: &ModelCtx,
        b: &IBlockRec,
    ) -> Result<Vec<IDeclaration>, Vec<u32>> {
        let gen: Result<Vec<Declaration>, String> = {
            let store: &EStore = ar;
            let bp = match read_block(&mut self.memo.borrow_mut(), store, b) {
                Some(x) => x,
                None => return Err(cps("arena: dangling handle in a modelled block")),
            };
            // The three closures of `ctxOf`: a name to its handle, the arena's
            // own context at that handle, the answer read back.
            let tbl = |n: &Name| -> Option<(Vec<Name>, Expr)> {
                let h = name_handle(store, n)?;
                let (lps, ty) = arena_core::frontend::types::ctx_tbl(ctx, &h)?;
                let ls = read_names(store, lps)?;
                let t = read_expr(&mut self.memo.borrow_mut(), store, ty)?;
                Some((ls, t))
            };
            let hs = |n: &Name| -> u64 {
                match name_handle(store, n) {
                    None => 0,
                    Some(h) => arena_core::frontend::types::ctx_height(ctx, &h),
                }
            };
            let bl = |n: &Name| -> Option<&BlockRec> {
                let h = name_handle(store, n)?;
                if let Some(r) = self.blocks.borrow().get(&h.word) {
                    return Some(*r);
                }
                let ib = arena_core::frontend::types::ctx_block(ctx, &h)?;
                let tree = read_block(&mut self.memo.borrow_mut(), store, ib)?;
                // `Ctx::blocks` hands back a REFERENCE (the core's own parse
                // has one to hand); this one is built on demand, so it is
                // leaked and remembered.  Bounded by the distinct blocks the
                // nested rung asks about — see the module note.
                let r: &'static BlockRec = Box::leak(Box::new(tree));
                self.blocks.borrow_mut().insert(h.word, r);
                Some(r)
            };
            let c = Ctx {
                tbl: &tbl,
                heights: &hs,
                blocks: &bl,
            };
            con_ron::in_model::generate(&c, &bp)
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
        let r = arena_core::arena::intern::intern_decls(&mut ast, &ds);
        *ar = ast.store;
        match r {
            Ok(hs) => Ok(hs),
            Err(e) => Err(con_ron::driver::message(&e).chars().map(|ch| ch as u32).collect()),
        }
    }
}

/// con-leche: none — a message as code points (DESIGN.md §3.3)
fn cps(s: &str) -> Vec<u32> {
    s.chars().map(|c| c as u32).collect()
}

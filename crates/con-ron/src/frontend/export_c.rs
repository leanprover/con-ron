//! `ConLeche/Frontend/ExportC.lean` — the **semantic layer** of the parse:
//! `apply_line` resolves a scanned record's stream indices against the parse
//! tables, builds the `Name`/`Level`/`Expr` nodes through con-ron-core's smart
//! constructors, and runs the taint policy, the prelude dedupe, the
//! projection rewrite and (in con-leche) the in-process modeller.
//!
//! The export's `ie`-indices *are* the sharing: the format already
//! externalises exactly the DAG structure an arena would reconstruct, so the
//! parse keeps a stream-index-keyed table of `Expr` **values** and a table hit
//! is a shared node by reference (an `Rc` clone).  Nothing rebuilds a term.
//!
//! **Three pure transformations of the parsed list happen here**, below the
//! verified fold — the fold sees their result as an ordinary list of records,
//! and the main theorem quantifies over that list: the built-in prelude
//! (`push_decl`), the ground hoist (`nat_op_ground`, applied by
//! `parse_result_of_state`), and the projection-function rewrite
//! (`proj_rec`).
//!
//! ## The in-process modeller (task #39)
//!
//! con-leche generates a `_model` family for every **mutual or nested**
//! inductive block at parse time and pushes it ahead of the block, which then
//! installs through the modeled route.  `process_line_core_d` does that here:
//! at the point `InModel.wants` (ported as `in_model_wants`) says yes it
//! builds the `BlockRec` (`block_rec_of`), calls `in_model::generate`, pushes
//! the records it returns through `push_gen_d` and books each of them with
//! `note_gen_names`, and only then pushes the block.  A generator decline is
//! the run's decline, naming the class.
//!
//! Three `StateD` fields exist for it and for nothing else — `const_types`
//! and `heights` (the sort inferer's and the generated definitions' hint
//! source, filled by `note_decl` at every push) and `ind_blocks` (the nested
//! rung's container shapes, filled at every inductive record).  They hold
//! every declaration's type in a hash map for the whole run, which is the
//! parse's one memory cost that scales with the stream rather than with the
//! DAG; con-leche pays it for the same reason.  `inModelGen`, the fourth, is
//! **not** ported: it feeds `CON_LECHE_INMODEL_DUMP` alone, whose writer
//! (`Frontend/ExportWrite.lean`) con-ron does not have (`in_model`'s note).
//!
//! `CON_LECHE_INMODEL=0` means what it means in con-leche: the block is
//! pushed bare and the *fold* declines it at the install, having found no
//! route.  `CON_LECHE_INMODEL_CENSUS=1` records a generator decline and
//! pushes the block bare instead of declining the parse, so one parse lists
//! every block's outcome.
//!
//! ## Other deviations
//!
//! * `M (StateD ⊕ RecordVerdict)` becomes `Result<(), LineErr>` over a
//!   `&mut StateD`: one error channel with two arms instead of a monad over a
//!   sum, and the state threaded by mutable reference instead of returned.
//!   con-leche threads it linearly for the same reason Rust's `&mut` gives
//!   for free (`ExportC.lean`'s task-#78 note: a handler that closes over the
//!   state holds it at RC 2 and every insert inside copies it).
//! * `PreludeIx.byName` maps a `Name` to the prelude record's **index** in
//!   `decls`, not to the record: `DeclC` derives nothing, `Clone` included
//!   (task #10's note), so a map of records would need a copy.
//! * `feed_chunk` and `parse_export_handle_d` read `&[u8]` slices of a
//!   `Vec<u8>` buffer rather than a `ByteArray`; the chunk size, the carried
//!   tail and the "position 0 means an incomplete tail" contract are
//!   con-leche's.

use std::rc::Rc;
use std::collections::{HashMap, HashSet};
use std::io::Read;

use con_ron_core::cached::parsed_c::DeclC;
use con_ron_core::kernel::basis_names as bnm;
use con_ron_core::kernel::env;
use con_ron_core::kernel::env::{BasisKind, ConstantInfo, ConstantVal, ReducibilityHint};
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::{BinderMeta, Expr, ExprKind, Literal};
use con_ron_core::kernel::expr_ops;
use con_ron_core::kernel::level;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::{Name, NameKind};
use con_ron_core::kernel::prop_when;
use con_ron_core::kernel::prop_when::PropWhen;
use con_ron_core::kernel::std_axioms;

use crate::frontend::basis_raw;
use crate::frontend::export::{
    canon_eq_list, constant_info_canon_eq, constant_val_canon_eq, name_str, FrontendError,
    RecordVerdict, TAINT_SENTINEL,
};
use crate::frontend::nat_op_ground::{decl_names, hoist_nat_op_ground, NameKey};
use crate::frontend::proj_rec;
use crate::frontend::scan_fast;
use crate::in_model;
use crate::frontend::scan_types::{
    id_table_get, id_table_insert, id_table_singleton, scan_err_render, CVRec, DeclRec, ExprRec,
    HintsRec, IdTable, IndCtorRec, IndRecRec, IndTypeRec, LevelRec, LineRec, NameRec, PwRec,
    RuleRec,
};

/// con-leche: ConLeche/Frontend/Export.lean:405 M
/// con-leche: ConLeche/Frontend/Export.lean:353-361 RecordVerdict
/// The two ways applying one line can fail: a parse message (con-leche's
/// `M = Except String`) or a record verdict (its `StateD ⊕ RecordVerdict`'s
/// right summand).  Merging them into one `Result` is this module's first
/// deviation; the taint sentinel is still told apart by its message, exactly
/// as `applyDeclD` tells it apart.
pub enum LineErr {
    Msg(String),
    Verdict(RecordVerdict),
}

/// con-leche: none — `throw` in con-leche's `M`, i.e. `Except.error`.
pub fn merr<T>(msg: String) -> Result<T, LineErr> {
    Err(LineErr::Msg(msg))
}

/// con-leche: none — `.inr (.declined …)`, the decline half of
/// `StateD ⊕ RecordVerdict`.
pub fn declined<T>(what: String) -> Result<T, LineErr> {
    Err(LineErr::Verdict(RecordVerdict::Declined(what)))
}

/// con-leche: none — `.inr (.invalid …)`, the reject half of
/// `StateD ⊕ RecordVerdict`.
pub fn invalid<T>(what: String) -> Result<T, LineErr> {
    Err(LineErr::Verdict(RecordVerdict::Invalid(what)))
}

/// con-leche: ConLeche/Kernel/Env.lean:350-354 BasisKind
/// Lean's `deriving DecidableEq` on `BasisKind`, which the prelude dedupe and
/// the pin match compare with `==`.  con-ron-core has no counterpart: the
/// verified core never compares two kinds (it dispatches on one), so the
/// comparison lives with its only consumer.
pub fn basis_kind_beq(a: &BasisKind, b: &BasisKind) -> bool {
    matches!(
        (a, b),
        (BasisKind::EqK, BasisKind::EqK)
            | (BasisKind::NatK, BasisKind::NatK)
            | (BasisKind::PunitK, BasisKind::PunitK)
            | (BasisKind::EmptyK, BasisKind::EmptyK)
            | (BasisKind::FalseK, BasisKind::FalseK)
            | (BasisKind::QuotK, BasisKind::QuotK)
    )
}

/// con-leche: ConLeche/Frontend/ExportC.lean:94-102 DeclC.asInfo?
/// The constant a definition-like record would store, for the canon
/// comparison (`opaqueDecl` is told apart from `defnDecl` by
/// `decl_same_canon`'s constructor test, not here).
pub fn decl_as_info(d: &DeclC) -> Option<ConstantInfo> {
    match d {
        DeclC::AxiomDecl(cv) => Some(ConstantInfo::AxiomInfo(env::constant_val_dup(cv))),
        DeclC::DefnDecl(cv, v, h) => Some(ConstantInfo::DefnInfo(
            env::constant_val_dup(cv),
            expr::dup(v),
            env::reducibility_hint_dup(h),
        )),
        DeclC::ThmDecl(cv, v) => Some(ConstantInfo::ThmInfo(
            env::constant_val_dup(cv),
            expr::dup(v),
        )),
        DeclC::OpaqueDecl(cv, v) => Some(ConstantInfo::DefnInfo(
            env::constant_val_dup(cv),
            expr::dup(v),
            ReducibilityHint::Opaque,
        )),
        _ => None,
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:104-114 DeclC.sameCanon
/// Two parsed records are the same declaration: same kind, and equal up to the
/// basis-matching canonical form.
pub fn decl_same_canon(a: &DeclC, b: &DeclC) -> bool {
    match (a, b) {
        (DeclC::BasisDecl(k), DeclC::BasisDecl(k2)) => basis_kind_beq(k, k2),
        (DeclC::IndDecl(bl, np), DeclC::IndDecl(bl2, np2)) => np == np2 && canon_eq_list(bl, bl2),
        (DeclC::OpaqueDecl(_, _), DeclC::DefnDecl(_, _, _)) => false,
        (DeclC::DefnDecl(_, _, _), DeclC::OpaqueDecl(_, _)) => false,
        _ => match (decl_as_info(a), decl_as_info(b)) {
            (Some(x), Some(y)) => constant_info_canon_eq(&x, &y),
            _ => false,
        },
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:116-122 PreludeIx
/// The built-in prelude, indexed: its records in order, the definition-like
/// and inductive records by every name they declare, and the basis blocks by
/// kind.  Deviation: `by_name` holds the record's index in `decls` (the module
/// note).
pub struct PreludeIx {
    pub decls: Vec<DeclC>,
    pub by_name: HashMap<NameKey, usize>,
    pub basis: Vec<BasisKind>,
}

/// con-leche: ConLeche/Frontend/ExportC.lean:116-122 PreludeIx
/// The empty prelude (Lean's field defaults), which the prelude's own parse
/// runs against.
pub fn prelude_ix_empty() -> PreludeIx {
    PreludeIx {
        decls: Vec::new(),
        by_name: HashMap::new(),
        basis: Vec::new(),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:124-129 PreludeIx.ofDecls
pub fn prelude_ix_of_decls(ds: Vec<DeclC>) -> PreludeIx {
    let mut ix = prelude_ix_empty();
    for d in ds {
        match &d {
            DeclC::BasisDecl(k) => {
                ix.basis.push(env::basis_kind_dup(k));
            }
            _ => {
                let at = ix.decls.len();
                for n in decl_names(&d) {
                    ix.by_name.insert(NameKey(n), at);
                }
            }
        }
        ix.decls.push(d);
    }
    ix
}

/// con-leche: ConLeche/Frontend/ExportC.lean:133-202 StateD
/// The direct parse state: stream-index-keyed tables of *values* (names and
/// levels as trees, expressions as `Expr` — a table hit is a shared node by
/// reference), the parsed declarations as `DeclC`, and the taint bookkeeping.
/// The four modeller-only fields are not here (the module note).
pub struct StateD {
    pub names: IdTable<Name>,
    pub levels: IdTable<Level>,
    pub exprs: IdTable<Expr>,
    pub decls: Vec<DeclC>,
    pub tainted: HashMap<u64, Name>,
    pub tainted_names: HashMap<NameKey, Name>,
    pub taint_skipped: Vec<(Name, Name)>,
    /// structure-like owners the projection rewrite serves, by type name
    pub proj_owners: HashMap<NameKey, proj_rec::ProjRecOwner>,
    /// field sorts, by artifact iota name `T._model.proj_i.iota` (the
    /// in-process modeller's own, and only those)
    pub proj_levels: HashMap<NameKey, Level>,
    /// the declared types of every declaration pushed so far (the prelude's
    /// included), by name: the in-process modeller's sort inferer reads them
    pub const_types: HashMap<NameKey, (Vec<Name>, Expr)>,
    /// the definitional heights of the definitions pushed so far (the hints
    /// of the generated definitions are computed from them)
    pub heights: HashMap<NameKey, u64>,
    /// the parsed inductive blocks, by member type name (the in-process
    /// modeller's nested rung reads a container's shape off it)
    pub ind_blocks: HashMap<NameKey, std::rc::Rc<in_model::mutual::BlockRec>>,
    /// the `PUnit` basis block has been parsed
    pub punit_seen: bool,
    /// projection functions rewritten so far (names, for the driver's trace)
    pub proj_rewrites: Vec<Name>,
    /// the built-in prelude this parse dedupes against
    pub prelude: PreludeIx,
    /// in-process modelling of mutual/nested blocks is on
    pub in_model: bool,
    /// the blocks modelled in-process, in stream order
    pub in_modelled: Vec<Name>,
    /// how many records the in-process modeller GENERATED and pushed
    pub gen_records: u64,
    /// each generated record's leading name ↦ the block it models
    pub gen_owner: HashMap<NameKey, Name>,
    /// the number of `inductive` records seen so far
    pub ind_count: u64,
    /// CENSUS mode (`CON_LECHE_INMODEL_CENSUS=1`)
    pub in_model_census: bool,
    /// the census's declines: block name and reason
    pub in_model_declined: Vec<(Name, String)>,
    /// stream records dropped as identical copies of prelude records
    pub prelude_dropped: u64,
}

/// con-leche: ConLeche/Frontend/ExportC.lean:878-885 StateD.init
/// The initial parse state over a prelude: `PUnit` counts as seen for the
/// projection rewrite when the prelude installs it, and `note_decl` is folded
/// over the prelude's records to seed the modeller's declaration table (the
/// prelude's `Nat`, `Eq`, `PUnit`, … are constants the sort inferer meets).
pub fn state_d_init(prelude: PreludeIx, in_model: bool, census: bool) -> StateD {
    let punit_seen = prelude
        .basis
        .iter()
        .any(|k| basis_kind_beq(k, &BasisKind::PunitK));
    let mut st = StateD {
        names: id_table_singleton(name::anonymous()),
        levels: id_table_singleton(level::zero()),
        exprs: crate::frontend::scan_types::id_table_empty(),
        decls: Vec::new(),
        tainted: HashMap::new(),
        tainted_names: HashMap::new(),
        taint_skipped: Vec::new(),
        proj_owners: HashMap::new(),
        proj_levels: HashMap::new(),
        const_types: HashMap::new(),
        heights: HashMap::new(),
        ind_blocks: HashMap::new(),
        punit_seen,
        proj_rewrites: Vec::new(),
        prelude,
        in_model,
        in_modelled: Vec::new(),
        gen_records: 0,
        gen_owner: HashMap::new(),
        ind_count: 0,
        in_model_census: census,
        in_model_declined: Vec::new(),
        prelude_dropped: 0,
    };
    // `prelude.decls.foldl noteDecl`: the entries are collected first because
    // they are read out of the state the fold writes into (Lean's value
    // semantics make the fold's argument a separate object).
    let mut es: Vec<(Name, Vec<Name>, Expr, Option<u64>)> = Vec::new();
    for d in st.prelude.decls.iter() {
        for e in note_decl_entries(d) {
            es.push(e);
        }
    }
    note_entries(&mut st, es);
    st
}

/// con-leche: ConLeche/Frontend/ExportC.lean:203-220 noteDecl
/// The constants one pushed declaration declares, with their level
/// parameters, declared types and (for a definition) definitional height:
/// the cited `cvs`.
pub fn note_decl_entries(d: &DeclC) -> Vec<(Name, Vec<Name>, Expr, Option<u64>)> {
    let one = |cv: &ConstantVal, h: Option<u64>| -> Vec<(Name, Vec<Name>, Expr, Option<u64>)> {
        vec![(
            name::dup(&cv.name),
            cv.level_params.iter().map(name::dup).collect(),
            expr::dup(&cv.ty),
            h,
        )]
    };
    match d {
        DeclC::AxiomDecl(cv) => one(cv, None),
        DeclC::DefnDecl(cv, _, h) => one(cv, Some(in_model::kit::hint_height(h))),
        DeclC::ThmDecl(cv, _) => one(cv, None),
        DeclC::OpaqueDecl(cv, _) => one(cv, None),
        DeclC::BasisDecl(k) => basis_raw::basis_decls(k)
            .iter()
            .map(|ci| {
                let cv = env::to_constant_val(ci);
                (
                    name::dup(&cv.name),
                    cv.level_params.iter().map(name::dup).collect(),
                    expr::dup(&cv.ty),
                    None,
                )
            })
            .collect(),
        DeclC::IndDecl(block, _) => block
            .iter()
            .map(|ci| {
                let cv = env::to_constant_val(ci);
                (
                    name::dup(&cv.name),
                    cv.level_params.iter().map(name::dup).collect(),
                    expr::dup(&cv.ty),
                    None,
                )
            })
            .collect(),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:203-220 noteDecl
/// The insert half of `noteDecl`: the cited `cvs.foldl` over `constTypes`
/// and `heights`.
pub fn note_entries(st: &mut StateD, es: Vec<(Name, Vec<Name>, Expr, Option<u64>)>) {
    for (n, lps, ty, h) in es {
        if let Some(hv) = h {
            st.heights.insert(NameKey(name::dup(&n)), hv);
        }
        st.const_types.insert(NameKey(n), (lps, ty));
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:203-220 noteDecl
/// Record a pushed declaration's constants in the declaration table
/// (`const_types`, `heights`).
pub fn note_decl(st: &mut StateD, d: &DeclC) {
    let es = note_decl_entries(d);
    note_entries(st, es);
}

/// con-leche: ConLeche/Frontend/ExportC.lean:222-239 pushDecl
/// **The prelude dedupe**, at every declaration push: a basis block the
/// prelude holds is dropped by kind; a record under a prelude name is dropped
/// when it is the same declaration (`decl_same_canon`) and declines the stream
/// when it differs.  Every record that is actually pushed goes through
/// `note_decl` (the cited `.inl (noteDecl … d)`), which is what feeds the
/// modeller's declaration table.
pub fn push_decl(st: &mut StateD, d: DeclC) -> Result<(), LineErr> {
    match &d {
        DeclC::BasisDecl(k) => {
            if st.prelude.basis.iter().any(|p| basis_kind_beq(p, k)) {
                st.prelude_dropped += 1;
            } else {
                note_decl(st, &d);
                st.decls.push(d);
            }
            Ok(())
        }
        _ => {
            let hit = decl_names(&d)
                .into_iter()
                .find_map(|n| st.prelude.by_name.get(&NameKey(name::dup(&n))).map(|i| (n, *i)));
            match hit {
                None => {
                    note_decl(st, &d);
                    st.decls.push(d);
                    Ok(())
                }
                Some((n, at)) => {
                    if decl_same_canon(&d, &st.prelude.decls[at]) {
                        st.prelude_dropped += 1;
                        Ok(())
                    } else {
                        declined(format!(
                            "declaration {} differs from the checker's built-in prelude \
                             (the toolchain's own {}, installed first)",
                            name_str(&n),
                            name_str(&n)
                        ))
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:241-244 StateD.name
pub fn st_name(st: &StateD, i: u64) -> Result<Name, LineErr> {
    match id_table_get(&st.names, i) {
        Some(n) => Ok(name::dup(n)),
        None => merr(format!("undefined name index {}", i)),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:246-249 StateD.level
pub fn st_level(st: &StateD, i: u64) -> Result<Level, LineErr> {
    match id_table_get(&st.levels, i) {
        Some(l) => Ok(level::dup(l)),
        None => merr(format!("undefined level index {}", i)),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:251-254 StateD.expr
pub fn st_expr(st: &StateD, i: u64) -> Result<Expr, LineErr> {
    match id_table_get(&st.exprs, i) {
        Some(e) => Ok(expr::dup(e)),
        None => merr(format!("undefined expr index {}", i)),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:256-269 getDeclD
/// Declaration-level expression lookup: the taint sentinel, then the table
/// read.  (The frontend tree-size budget that used to sit here was retired at
/// con-leche task #215; the DAG-tower fixtures are the standing gate in its
/// place.)
pub fn get_decl_d(st: &StateD, i: u64) -> Result<Expr, LineErr> {
    if st.tainted.contains_key(&i) {
        return merr(TAINT_SENTINEL.to_string());
    }
    st_expr(st, i)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:271-274 parsePwD
/// The `pw` datum over the direct name table.
pub fn parse_pw_d(st: &StateD, r: &PwRec) -> Result<PropWhen, LineErr> {
    match r {
        PwRec::Never => Ok(prop_when::never()),
        PwRec::IfAllZero(ns) => {
            let mut out: Vec<Name> = Vec::new();
            for i in ns {
                out.push(st_name(st, *i)?);
            }
            Ok(prop_when::if_all_zero(out))
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:278-285 parseNameEntryD
/// A name-table entry: the name value is built directly.
pub fn parse_name_entry_d(st: &mut StateD, i: u64, r: &NameRec) -> Result<(), LineErr> {
    let v = match r {
        NameRec::Str(pre, s) => {
            let p = st_name(st, *pre)?;
            name::mk_str(p, s.clone())
        }
        NameRec::Num(pre, n) => {
            let p = st_name(st, *pre)?;
            name::mk_num(p, *n)
        }
    };
    id_table_insert(&mut st.names, i, v);
    Ok(())
}

/// con-leche: ConLeche/Frontend/ExportC.lean:287-294 parseLevelEntryD
/// A level-table entry.
pub fn parse_level_entry_d(st: &mut StateD, i: u64, r: &LevelRec) -> Result<(), LineErr> {
    let l = match r {
        LevelRec::Succ(u) => level::succ(st_level(st, *u)?),
        LevelRec::Max(a, b) => level::max(st_level(st, *a)?, st_level(st, *b)?),
        LevelRec::Imax(a, b) => level::imax(st_level(st, *a)?, st_level(st, *b)?),
        LevelRec::Param(n) => level::param(st_name(st, *n)?),
    };
    id_table_insert(&mut st.levels, i, l);
    Ok(())
}

/// con-leche: ConLeche/Frontend/ExportC.lean:296-304 exprRecChildren
/// The child expression-table indices of an entry (for taint propagation).
pub fn expr_rec_children(r: &ExprRec) -> Vec<u64> {
    match r {
        ExprRec::App(f, a) => vec![*f, *a],
        ExprRec::Lam(ty, bd, _) => vec![*ty, *bd],
        ExprRec::ForallE(ty, bd, _) => vec![*ty, *bd],
        ExprRec::LetE(ty, vl, bd) => vec![*ty, *vl, *bd],
        ExprRec::Proj(_, _, s) => vec![*s],
        _ => Vec::new(),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:306-350 parseExprEntryD
/// An expression-table entry: build the node from the children's table values
/// (the derived fields are the smart constructors'), with the taint
/// bookkeeping unchanged.  Binder names are display data the official
/// kernel's equality and hash ignore; ours are `.anonymous` on every parsed
/// binder, so `==` is α-equivalence downstream.
pub fn parse_expr_entry_d(st: &mut StateD, i: u64, r: &ExprRec) -> Result<(), LineErr> {
    let (e, taint_const): (Expr, Option<Name>) = match r {
        ExprRec::Bvar(k) => (expr::mk_bvar(*k), None),
        ExprRec::Sort(u) => (expr::sort(st_level(st, *u)?), None),
        ExprRec::Const(n, us) => {
            let nm = st_name(st, *n)?;
            let mut ls: Vec<Level> = Vec::new();
            for u in us {
                ls.push(st_level(st, *u)?);
            }
            let taint_c = if st.tainted_names.is_empty() {
                None
            } else {
                st.tainted_names
                    .get(&NameKey(name::dup(&nm)))
                    .map(name::dup)
            };
            (expr::mk_const(nm, ls), taint_c)
        }
        ExprRec::App(f, a) => (expr::app(st_expr(st, *f)?, st_expr(st, *a)?), None),
        ExprRec::Lam(ty, bd, pw) => (
            expr::lam(
                st_expr(st, *ty)?,
                st_expr(st, *bd)?,
                BinderMeta {
                    pw: Rc::new(parse_pw_d(st, pw)?),
                },
            ),
            None,
        ),
        ExprRec::ForallE(ty, bd, pw) => (
            expr::forall_e(
                st_expr(st, *ty)?,
                st_expr(st, *bd)?,
                BinderMeta {
                    pw: Rc::new(parse_pw_d(st, pw)?),
                },
            ),
            None,
        ),
        ExprRec::LetE(ty, vl, bd) => (
            expr::let_e(st_expr(st, *ty)?, st_expr(st, *vl)?, st_expr(st, *bd)?),
            None,
        ),
        ExprRec::Proj(tn, ix, s) => (
            expr::proj(st_name(st, *tn)?, *ix, st_expr(st, *s)?),
            None,
        ),
        ExprRec::NatVal(digits) => {
            let n = match con_ron_dump::natdec::from_decimal(digits) {
                Ok(n) => n,
                Err(e) => return merr(format!("malformed natVal literal: {}", e)),
            };
            (expr::lit(Literal::NatVal(Rc::new(n))), None)
        }
        ExprRec::StrVal(s) => (expr::lit(Literal::StrVal(Rc::new(s.clone()))), None),
    };
    // the child scan runs only once a tolerated axiom has put something in
    // the table: an entry can be tainted only below one
    let taint: Option<Name> = match taint_const {
        Some(n) => Some(n),
        None => {
            if st.tainted.is_empty() {
                None
            } else {
                expr_rec_children(r)
                    .into_iter()
                    .find_map(|c| st.tainted.get(&c).map(name::dup))
            }
        }
    };
    id_table_insert(&mut st.exprs, i, e);
    if let Some(root) = taint {
        st.tainted.insert(i, root);
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/ExportC.lean:354-360 parseCVD
/// A declaration's common data.
pub fn parse_cv_d(st: &StateD, cv: &CVRec) -> Result<ConstantVal, LineErr> {
    let nm = st_name(st, cv.name)?;
    let ty = get_decl_d(st, cv.ty)?;
    let mut lps: Vec<Name> = Vec::new();
    for i in &cv.level_params {
        lps.push(st_name(st, *i)?);
    }
    Ok(ConstantVal {
        name: nm,
        level_params: lps,
        ty,
    })
}

/// con-leche: ConLeche/Frontend/ExportC.lean:362-374 projRewriteD
/// The projection-function rewrite at a definition record: the value is
/// `fun p⃗ self => .proj T i self` for a recorded owner `T`, the field's sort
/// is on record from the artifact, `PUnit` is available, and the definition's
/// level parameters are the block's.  `None` = leave the record as parsed.
///
/// **Always `None` until task #38**: `proj_levels` is filled only by
/// `note_proj_iota` on a record the in-process modeller generated.
pub fn proj_rewrite_d(st: &StateD, cv: &ConstantVal, vl: &Expr) -> Option<Expr> {
    let body = proj_rec::lam_body(vl);
    let (t, i) = match &body.0.kind {
        ExprKind::Proj(t, i, sub) => match &sub.0.kind {
            ExprKind::Bvar(0) => (name::dup(t), *i),
            _ => return None,
        },
        _ => return None,
    };
    let o = st.proj_owners.get(&NameKey(name::dup(&t)))?;
    if !st.punit_seen {
        return None;
    }
    if !crate::frontend::export::names_beq(&cv.level_params, &o.lps) {
        return None;
    }
    let l = st
        .proj_levels
        .get(&NameKey(proj_rec::proj_iota_name(&t, i)))?;
    proj_rec::proj_rec_value(o, l, &cv.ty, vl, i)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:376-389 noteProjIota
/// An artifact `T._model.proj_i.iota` names the field's sort in its `Eq`
/// level: recorded for the projection rewrite.  Run on the records the
/// in-process modeller GENERATES and on those alone, so unreachable until
/// task #38.
pub fn note_proj_iota(st: &mut StateD, cvp: &ConstantVal) {
    if proj_rec::is_proj_iota_name(&cvp.name) {
        if let Some(l) = proj_rec::proj_iota_level(&cvp.ty) {
            st.proj_levels.insert(NameKey(name::dup(&cvp.name)), l);
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:391-398 pushGenD
/// Push one record the in-process modeller generated: `push_decl`, plus the
/// projection-iota registration (the ONLY place it runs).  Unreachable until
/// task #38, and the entry point that task calls.
pub fn push_gen_d(st: &mut StateD, d: DeclC) -> Result<(), LineErr> {
    if let DeclC::ThmDecl(cv, _) = &d {
        let cv2 = env::constant_val_dup(cv);
        note_proj_iota(st, &cv2);
    }
    push_decl(st, d)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:400-408 noteGen
/// Book a record the in-process modeller generated for block `T0`: a
/// declaration of the FOLD, never a record of the file, so the driver's
/// headline count subtracts it and a failure at it is reported with the block
/// it models.
pub fn note_gen(st: &mut StateD, d: &DeclC, t0: &Name) {
    note_gen_names(st, decl_names(d), t0);
}

/// con-leche: ConLeche/Frontend/ExportC.lean:400-408 noteGen
/// `note_gen` at the record's names already in hand.  The call site needs
/// this half: `push_gen_d` takes the `DeclC` by value (it is pushed into the
/// state), and whether it pushed — the cited `st'.decls.size > before` — is
/// known only afterwards, when the record is gone.  con-leche reads `d.names`
/// at that point because a Lean value is still there to read.
pub fn note_gen_names(st: &mut StateD, names: Vec<Name>, t0: &Name) {
    st.gen_records += 1;
    for n in names {
        st.gen_owner.insert(NameKey(n), name::dup(t0));
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:410-416 indPiTeleLen
/// **The syntactic Π-telescope length of a declared type**: official counts a
/// constructor's binders by walking `is_pi` without reducing, and the count
/// past the parameters is the `numFields` of the constructor it generates.
pub fn ind_pi_tele_len(e: &Expr) -> u64 {
    let mut n: u64 = 0;
    let mut cur = expr::dup(e);
    loop {
        let next = match &cur.0.kind {
            ExprKind::ForallE(_, b, _) => {
                n += 1;
                expr::dup(b)
            }
            _ => return n,
        };
        cur = next;
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:418-421 parseRuleD
/// One recursor rule of an inductive record, resolved.
pub fn parse_rule_d(st: &StateD, ru: &RuleRec) -> Result<env::RecRule, LineErr> {
    Ok(env::rec_rule_parsed(
        st_name(st, ru.ctor)?,
        ru.nfields,
        get_decl_d(st, ru.rhs)?,
    ))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:423-447 blockRecOf
/// The export's shape data of an inductive record, for the in-process
/// modeller.
pub fn block_rec_of(
    st: &StateD,
    types: &[IndTypeRec],
    ctors: &[IndCtorRec],
    recs: &[IndRecRec],
) -> Result<in_model::mutual::BlockRec, LineErr> {
    let mut ts: Vec<in_model::mutual::IndTypeRec> = Vec::new();
    for t in types {
        let mut cs: Vec<Name> = Vec::new();
        for c in &t.ctors {
            cs.push(st_name(st, *c)?);
        }
        ts.push(in_model::mutual::IndTypeRec {
            cv: parse_cv_d(st, &t.cv)?,
            n_p: t.num_params,
            n_idx: t.num_indices,
            ctors: cs,
            is_rec: t.is_rec,
            is_reflexive: t.is_reflexive,
            num_nested: t.num_nested,
        });
    }
    let mut cts: Vec<in_model::mutual::IndCtorRec> = Vec::new();
    for c in ctors {
        cts.push(in_model::mutual::IndCtorRec {
            cv: parse_cv_d(st, &c.cv)?,
            n_p: c.num_params,
            n_f: c.num_fields,
        });
    }
    let mut rcs: Vec<in_model::mutual::IndRecRec> = Vec::new();
    for r in recs {
        let mut rules: Vec<env::RecRule> = Vec::new();
        for ru in &r.rules {
            rules.push(parse_rule_d(st, ru)?);
        }
        rcs.push(in_model::mutual::IndRecRec {
            cv: parse_cv_d(st, &r.cv)?,
            n_p: r.num_params,
            n_m: r.num_motives,
            nm: r.num_minors,
            n_i: r.num_indices,
            rules,
        });
    }
    Ok(in_model::mutual::BlockRec {
        types: ts,
        ctors: cts,
        recs: rcs,
    })
}

/// con-leche: ConLeche/Frontend/InModel.lean:35-38 wants
/// Is the block one the modeller is for: mutual (several types) or nested
/// (`numNested > 0`)?  con-leche asks this of the `InModel.BlockRec`
/// `blockRecOf` builds; the two fields it reads are the scan records' own
/// (`types.length` and `numNested`), so the port asks it of those and needs
/// neither `BlockRec` nor `blockRecOf` (the module note).
pub fn in_model_wants(tys: &[IndTypeRec]) -> bool {
    tys.len() > 1 || tys.iter().any(|t| t.num_nested > 0)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:449-767 processLineCoreD.registerProjOwners
/// Record the structure-like owners of a parsed block that the projection
/// rewrite serves.
pub fn register_proj_owners(
    st: &mut StateD,
    tys: &[IndTypeRec],
    cts: &[IndCtorRec],
    rcs: &[IndRecRec],
    block: &Vec<ConstantInfo>,
) -> Result<(), LineErr> {
    let mut types: Vec<proj_rec::ProjTypeRec> = Vec::new();
    for t in tys {
        let cv = parse_cv_d(st, &t.cv)?;
        let mut ctors: Vec<Name> = Vec::new();
        for c in &t.ctors {
            ctors.push(st_name(st, *c)?);
        }
        types.push(proj_rec::ProjTypeRec {
            name: name::dup(&cv.name),
            lps: cv.level_params.iter().map(name::dup).collect(),
            ty: expr::dup(&cv.ty),
            n_p: t.num_params,
            n_i: t.num_indices,
            ctors,
            is_rec: t.is_rec,
        });
    }
    let mut ctors: Vec<proj_rec::ProjCtorRec> = Vec::new();
    for c in cts {
        let cv = parse_cv_d(st, &c.cv)?;
        ctors.push(proj_rec::ProjCtorRec {
            name: name::dup(&cv.name),
            n_f: c.num_fields,
            ty: expr::dup(&cv.ty),
        });
    }
    let mut recs: Vec<proj_rec::ProjRecRec> = Vec::new();
    for r in rcs {
        let cv = parse_cv_d(st, &r.cv)?;
        recs.push(proj_rec::ProjRecRec {
            name: name::dup(&cv.name),
            lps: cv.level_params.iter().map(name::dup).collect(),
            ty: expr::dup(&cv.ty),
            n_m: r.num_motives,
            nm: r.num_minors,
        });
    }
    for o in proj_rec::proj_rec_owners(block, &types, &ctors, &recs) {
        st.proj_owners.insert(NameKey(name::dup(&o.t)), o);
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/ExportC.lean:449-767 processLineCoreD
/// The record's own semantics: the declaration kinds, producing `DeclC`
/// records.  Every branch, guard and error string is the one the `Lean.Json`
/// reader this replaced had; only the reads changed, from key lookups in a DOM
/// to fields of a syntax record.
pub fn process_line_core_d(st: &mut StateD, d: &DeclRec) -> Result<(), LineErr> {
    match d {
        DeclRec::Ax(cvr, is_unsafe) => {
            let cvp = parse_cv_d(st, cvr)?;
            if *is_unsafe {
                return declined("unsafe axiom".to_string());
            }
            if name::beq(&cvp.name, &bnm::quot_sound_name()) {
                let pin = &basis_raw::quot_basis()[4];
                return if constant_info_canon_eq(&ConstantInfo::AxiomInfo(cvp), pin) {
                    Ok(())
                } else {
                    declined("quotient soundness axiom mismatch".to_string())
                };
            }
            push_decl(st, DeclC::AxiomDecl(cvp))
        }
        DeclRec::Defn(cvr, value, hints, safety) => {
            let cvp = parse_cv_d(st, cvr)?;
            if safety != "safe" {
                return declined(format!("definition with safety '{}'", safety));
            }
            let vl = get_decl_d(st, *value)?;
            let h = match hints {
                HintsRec::Abbrev => ReducibilityHint::Abbrev,
                HintsRec::Opaque => ReducibilityHint::Opaque,
                HintsRec::Regular(n) => ReducibilityHint::Regular(*n),
            };
            // the projection-function rewrite: a non-direct structure-like's
            // `fun p⃗ self => .proj T i self` becomes the recursor
            // application, at the field sort the artifact names
            match proj_rewrite_d(st, &cvp, &vl) {
                Some(vl2) => {
                    let n = name::dup(&cvp.name);
                    push_decl(st, DeclC::DefnDecl(cvp, vl2, h))?;
                    st.proj_rewrites.push(n);
                    Ok(())
                }
                None => push_decl(st, DeclC::DefnDecl(cvp, vl, h)),
            }
        }
        DeclRec::Thm(cvr, value) => {
            let cvp = parse_cv_d(st, cvr)?;
            let vl = get_decl_d(st, *value)?;
            // a proof field's projection function is exported as a theorem
            // (the elaborator's choice for a `Prop`-valued field): the same
            // rewrite applies
            match proj_rewrite_d(st, &cvp, &vl) {
                Some(vl2) => {
                    let n = name::dup(&cvp.name);
                    push_decl(st, DeclC::ThmDecl(cvp, vl2))?;
                    st.proj_rewrites.push(n);
                    Ok(())
                }
                None => push_decl(st, DeclC::ThmDecl(cvp, vl)),
            }
        }
        DeclRec::Opaq(cvr, value, is_unsafe) => {
            let cvp = parse_cv_d(st, cvr)?;
            if *is_unsafe {
                return declined("unsafe opaque declaration".to_string());
            }
            let vl = get_decl_d(st, *value)?;
            push_decl(st, DeclC::OpaqueDecl(cvp, vl))
        }
        DeclRec::Quot(cvr, kind) => {
            let cv = parse_cv_d(st, cvr)?;
            let slot: usize = match kind.as_str() {
                "type" => 0,
                "ctor" => 1,
                "lift" => 2,
                "ind" => 3,
                k => return merr(format!("unknown quotient kind '{}'", k)),
            };
            let pin = &basis_raw::quot_basis()[slot];
            // the two records are compared at `toConstantVal`
            if constant_val_canon_eq(&cv, &env::to_constant_val(pin)) {
                if slot == 0 {
                    push_decl(st, DeclC::BasisDecl(BasisKind::QuotK))
                } else {
                    Ok(())
                }
            } else {
                declined("quotient declaration mismatch".to_string())
            }
        }
        DeclRec::Ind(tys, cts, rcs) => process_ind_decl_d(st, tys, cts, rcs),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:449-767 processLineCoreD
/// `processLineCoreD`'s `.ind` arm, which is two thirds of the function: the
/// unsafe decline, the declared parameter count (task #228), the block's
/// redundant fields (task #271), the block's `ConstantInfo`s, the projection
/// owners, the basis-pin match, and the modeller point task #38 fills in.
pub fn process_ind_decl_d(
    st: &mut StateD,
    tys: &[IndTypeRec],
    cts: &[IndCtorRec],
    rcs: &[IndRecRec],
) -> Result<(), LineErr> {
    st.ind_count += 1;
    // an `unsafe inductive` is DECLINED, not an error: the official kernel
    // admits unsafe blocks (it skips positivity for them); we support no
    // unsafe declaration at all.
    if tys.iter().any(|t| t.is_unsafe) {
        return declined("unsafe inductive declaration".to_string());
    }
    // TASK #228 — THE DECLARED PARAMETER COUNT.  A block whose type records
    // disagree on `numParams` has no declared count this checker could hold
    // official to, and is positively declined here.
    let n_pd = match tys.first() {
        Some(t) => t.num_params,
        None => 0,
    };
    if !tys.iter().all(|t| t.num_params == n_pd) {
        return declined("inductive block whose type records disagree on numParams".to_string());
    }
    // TASK #271 (issues #5 and #7) — THE BLOCK'S REDUNDANT FIELDS.  These are
    // consistency checks between the stream's own fields, so they live here,
    // in the parse, and their verdict is `.invalid`: the fold never sees such
    // a block.
    let mut ty_names: Vec<Name> = Vec::new();
    for t in tys {
        ty_names.push(st_name(st, t.cv.name)?);
    }
    let mut ty_types: Vec<Expr> = Vec::new();
    for t in tys {
        ty_types.push(get_decl_d(st, t.cv.ty)?);
    }
    let mut listed: Vec<Vec<Name>> = Vec::new();
    for t in tys {
        let mut ns: Vec<Name> = Vec::new();
        for c in &t.ctors {
            ns.push(st_name(st, *c)?);
        }
        listed.push(ns);
    }
    let mut ctor_names: Vec<Name> = Vec::new();
    for c in cts {
        ctor_names.push(st_name(st, c.cv.name)?);
    }
    let flat: Vec<Name> = listed.iter().flatten().map(name::dup).collect();
    let mut seen: HashSet<NameKey> = HashSet::new();
    for n in flat.iter() {
        if !seen.insert(NameKey(name::dup(n))) {
            return invalid("duplicate constructor name in an inductive type's ctors".to_string());
        }
    }
    if flat.len() != cts.len() {
        return invalid(format!(
            "the inductive block lists {} constructors and carries {} constructor records",
            flat.len(),
            cts.len()
        ));
    }
    let mut ctor_ix: HashMap<NameKey, usize> = HashMap::new();
    for (k, n) in ctor_names.iter().enumerate() {
        ctor_ix.entry(NameKey(name::dup(n))).or_insert(k);
    }
    // the constructors IN THE BLOCK'S OWN ORDER, `types[].ctors` in type
    // order (issue #5): a record array in another order is the same block,
    // and the recursor generated from it is the same one
    let mut ordered: Vec<IndCtorRec> = Vec::new();
    for (t_at, t) in ty_names.iter().enumerate() {
        let mut j: u64 = 0;
        for n in listed[t_at].iter() {
            let k = match ctor_ix.get(&NameKey(name::dup(n))) {
                None => return invalid(format!("No such constructor {}", name_str(n))),
                Some(k) => *k,
            };
            let c = match cts.get(k) {
                None => return invalid(format!("No such constructor {}", name_str(n))),
                Some(c) => c,
            };
            if let Some(ci) = c.cidx {
                if ci != j {
                    return invalid(format!(
                        "constructor {} declares cidx {}; it is constructor {} of {}",
                        name_str(n),
                        ci,
                        j,
                        name_str(t)
                    ));
                }
            }
            if let Some(iw) = c.induct {
                let iwn = st_name(st, iw)?;
                if !name::beq(&iwn, t) {
                    return invalid(format!(
                        "constructor {} declares induct {}; it is a constructor of {}",
                        name_str(n),
                        name_str(&iwn),
                        name_str(t)
                    ));
                }
            }
            // `numFields`: official counts the constructor's own Π binders
            // without reducing and stores the count past the parameters, so a
            // record that declares another number is not the generated
            // constructor.
            let cty = get_decl_d(st, c.cv.ty)?;
            if n_pd + c.num_fields != ind_pi_tele_len(&cty) {
                return invalid(format!(
                    "constructor {} declares {} fields at {} parameters; \
                     its type has {} binders",
                    name_str(n),
                    c.num_fields,
                    n_pd,
                    ind_pi_tele_len(&cty)
                ));
            }
            ordered.push(c.clone());
            j += 1;
        }
    }
    let cts: Vec<IndCtorRec> = ordered;
    // The recursor records: the counts and the K flag the GENERATED recursor
    // carries.  NOT at a NESTED block — the kernel specialises a nested block
    // into a mutual one with a mimic type per nested occurrence, and the
    // recursors it generates are the SPECIALISED block's.
    let nested = tys.iter().any(|t| t.num_nested != 0);
    let n_types = tys.len() as u64;
    let n_ctors = cts.len() as u64;
    // official's `is_K_target`: the block is a `Prop`, has ONE type with ONE
    // constructor, and that constructor takes only the parameters.  At a
    // former whose declared type is not a syntactic Π-telescope ending in a
    // sort the sort cannot be read here and the flag is left to the install.
    let k_expected: Option<bool> = if ty_types.len() == 1 && listed.len() == 1 && cts.len() == 1 {
        if listed[0].len() == 1 {
            match &expr_ops::pi_result(&ty_types[0]).0.kind {
                ExprKind::Sort(s) => Some(
                    cts[0].num_fields == 0
                        && level::is_equiv(s, &level::zero()) == Some(true),
                ),
                _ => None,
            }
        } else {
            Some(false)
        }
    } else {
        Some(false)
    };
    if !nested {
        for r in rcs.iter() {
            let rn = st_name(st, r.cv.name)?;
            if r.num_params != n_pd {
                return invalid(format!(
                    "recursor {} declares {} parameters; the block declares {}",
                    name_str(&rn),
                    r.num_params,
                    n_pd
                ));
            }
            if r.num_motives != n_types {
                return invalid(format!(
                    "recursor {} declares {} motives; the block has {} inductive types",
                    name_str(&rn),
                    r.num_motives,
                    n_types
                ));
            }
            if r.num_minors != n_ctors {
                return invalid(format!(
                    "recursor {} declares {} minor premises; the block has {} constructors",
                    name_str(&rn),
                    r.num_minors,
                    n_ctors
                ));
            }
            if let Some(k_e) = k_expected {
                if r.k != k_e {
                    return invalid(format!(
                        "recursor {} declares k := {}; the generated recursor of this \
                         block is{} K-like",
                        name_str(&rn),
                        r.k,
                        if k_e { "" } else { " not" }
                    ));
                }
            }
            // `numIndices` of `T.rec` is what is left of `T`'s own telescope
            // once the parameters are peeled; unreadable at a former declared
            // at a definition, and then not checked
            if let NameKind::Str(t_pre, last) = &rn.0.kind {
                if last.iter().copied().eq("rec".chars().map(|c| c as u32)) {
                    for (tn, tt) in ty_names.iter().zip(ty_types.iter()) {
                        if name::beq(tn, t_pre) {
                            if let Some(n) = env::pi_sort_tele_len(tt) {
                                if n_pd + r.num_indices != n {
                                    return invalid(format!(
                                        "recursor {} declares {} indices; {} has {} at {} \
                                         parameters",
                                        name_str(&rn),
                                        r.num_indices,
                                        name_str(t_pre),
                                        n - n_pd,
                                        n_pd
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    let mut block: Vec<ConstantInfo> = Vec::new();
    for t in tys {
        block.push(ConstantInfo::IndInfo(
            parse_cv_d(st, &t.cv)?,
            env::ind_caps_default(),
        ));
    }
    for c in cts.iter() {
        block.push(ConstantInfo::CtorInfo(
            parse_cv_d(st, &c.cv)?,
            c.num_params,
            c.num_fields,
        ));
    }
    for r in rcs.iter() {
        let mut rules: Vec<env::RecRule> = Vec::new();
        for ru in &r.rules {
            rules.push(parse_rule_d(st, ru)?);
        }
        block.push(ConstantInfo::RecInfo(
            parse_cv_d(st, &r.cv)?,
            r.num_params + r.num_motives + r.num_minors + r.num_indices,
            r.num_params + r.num_motives + r.num_minors,
            rules,
        ));
    }
    // the projection rewrite's owner table (the export's own shape data)
    register_proj_owners(st, tys, &cts, rcs, &block)?;
    // TASK #215 — the basis-pin NAME pre-filter.  `canon` renames only
    // *level parameters* — it leaves every constant name alone — so a block
    // can match a pin only when its members' names are the pin's, member for
    // member.  Selecting the candidate by name first is a handful of `Name`
    // comparisons, and no canonical form is built at all for any block that is
    // not one of the five.
    let block_names: Vec<Name> = block.iter().map(env::constant_info_name).collect();
    let mut pin_hit: Option<BasisKind> = None;
    for k in basis_raw::block_pin_kinds() {
        let pin = basis_raw::basis_decls(&k);
        let pin_names: Vec<Name> = pin.iter().map(env::constant_info_name).collect();
        if crate::frontend::export::names_beq(&pin_names, &block_names) {
            if canon_eq_list(&block, &pin) {
                pin_hit = Some(k);
            }
            break;
        }
    }
    if let Some(k) = pin_hit {
        if basis_kind_beq(&k, &BasisKind::PunitK) {
            st.punit_seen = true;
        }
        return push_decl(st, DeclC::BasisDecl(k));
    }
    // THE IN-PROCESS MODELLER (the ONLY model source, and the only one there
    // IS — a stream `_model` record is an ordinary declaration and is never
    // consulted): a mutual or nested block gets its `_model` family generated
    // here and pushed ahead of it; the block then installs through the modeled
    // route.  A generator decline is the run's decline, naming the class (the
    // residual: infinitary nesting, a `Prop` block with a large eliminator).
    let t0 = match block_names.first() {
        Some(n) => name::dup(n),
        None => name::anonymous(),
    };
    let b = std::rc::Rc::new(block_rec_of(st, tys, &cts, rcs)?);
    for t in b.types.iter() {
        st.ind_blocks
            .insert(NameKey(name::dup(&t.cv.name)), std::rc::Rc::clone(&b));
    }
    if st.in_model && in_model_wants(tys) {
        let gen = {
            let const_types = &st.const_types;
            let heights = &st.heights;
            let ind_blocks = &st.ind_blocks;
            let tbl = |n: &Name| -> Option<(Vec<Name>, Expr)> {
                const_types.get(&NameKey(name::dup(n))).map(|(lps, ty)| {
                    (lps.iter().map(name::dup).collect(), expr::dup(ty))
                })
            };
            let hs = |n: &Name| -> u64 {
                *heights.get(&NameKey(name::dup(n))).unwrap_or(&0)
            };
            let bl = |n: &Name| -> Option<&in_model::mutual::BlockRec> {
                ind_blocks.get(&NameKey(name::dup(n))).map(|r| &**r)
            };
            let ctx = in_model::mutual::Ctx {
                tbl: &tbl,
                heights: &hs,
                blocks: &bl,
            };
            in_model::generate(&ctx, &b)
        };
        match gen {
            Err(why) => {
                if st.in_model_census {
                    st.in_model_declined.push((name::dup(&t0), why));
                    return push_decl(st, DeclC::IndDecl(block, n_pd));
                }
                return declined(format!("in-process model of {}: {}", name_str(&t0), why));
            }
            Ok(gen) => {
                for d in gen {
                    // a generated record is a declaration of the FOLD and not
                    // a record of the file: booked here, so the verdict line
                    // reports the file's own count
                    let before = st.decls.len();
                    let names = decl_names(&d);
                    push_gen_d(st, d)?;
                    if st.decls.len() > before {
                        note_gen_names(st, names, &t0);
                    }
                }
                st.in_modelled.push(name::dup(&t0));
                return push_decl(st, DeclC::IndDecl(block, n_pd));
            }
        }
    }
    push_decl(st, DeclC::IndDecl(block, n_pd))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:769-793 declRecordScanD
/// The read-only pre-scan for the taint policy: the names a declaration
/// record declares, and the expression indices it reads.
pub fn decl_record_scan_d(st: &StateD, d: &DeclRec) -> Result<(Vec<Name>, Vec<u64>), LineErr> {
    match d {
        DeclRec::Ax(cv, _) => Ok((vec![st_name(st, cv.name)?], vec![cv.ty])),
        DeclRec::Quot(cv, _) => Ok((vec![st_name(st, cv.name)?], vec![cv.ty])),
        DeclRec::Defn(cv, v, _, _) => Ok((vec![st_name(st, cv.name)?], vec![cv.ty, *v])),
        DeclRec::Thm(cv, v) => Ok((vec![st_name(st, cv.name)?], vec![cv.ty, *v])),
        DeclRec::Opaq(cv, v, _) => Ok((vec![st_name(st, cv.name)?], vec![cv.ty, *v])),
        DeclRec::Ind(tys, cts, rcs) => {
            let mut names: Vec<Name> = Vec::new();
            let mut idxs: Vec<u64> = Vec::new();
            for t in tys {
                names.push(st_name(st, t.cv.name)?);
                idxs.push(t.cv.ty);
            }
            for c in cts {
                names.push(st_name(st, c.cv.name)?);
                idxs.push(c.cv.ty);
            }
            for r in rcs {
                names.push(st_name(st, r.cv.name)?);
                idxs.push(r.cv.ty);
            }
            for r in rcs {
                for ru in &r.rules {
                    idxs.push(ru.rhs);
                }
            }
            Ok((names, idxs))
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:795-824 applyDeclD
/// The taint policy at a declaration record.
pub fn apply_decl_d(st: &mut StateD, d: &DeclRec) -> Result<(), LineErr> {
    if let DeclRec::Ax(cv, _) = d {
        let nm = st_name(st, cv.name)?;
        if name::contains(&std_axioms::tolerated_axiom_names(), &nm) {
            st.tainted_names
                .insert(NameKey(name::dup(&nm)), name::dup(&nm));
            return Ok(());
        }
    }
    if !st.tainted.is_empty() {
        let (names, idxs) = decl_record_scan_d(st, d)?;
        let root = idxs
            .into_iter()
            .find_map(|i| st.tainted.get(&i).map(name::dup));
        if let Some(root) = root {
            let head = match names.first() {
                Some(n) => name::dup(n),
                None => name::anonymous(),
            };
            for n in names {
                st.tainted_names.insert(NameKey(n), name::dup(&root));
            }
            st.taint_skipped.push((head, root));
            return Ok(());
        }
    }
    match process_line_core_d(st, d) {
        Ok(()) => Ok(()),
        Err(LineErr::Msg(e)) => {
            if e == TAINT_SENTINEL {
                declined("declaration uses a skipped (non-pinned) axiom".to_string())
            } else {
                Err(LineErr::Msg(e))
            }
        }
        Err(v) => Err(v),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:826-840 applyLine
/// **The semantic layer**: one scanned line applied to the parse state.
pub fn apply_line(st: &mut StateD, r: &LineRec) -> Result<(), LineErr> {
    match r {
        LineRec::Expr(i, e) => parse_expr_entry_d(st, *i, e),
        LineRec::Name(i, n) => parse_name_entry_d(st, *i, n),
        LineRec::Level(i, l) => parse_level_entry_d(st, *i, l),
        LineRec::Decl(d) => apply_decl_d(st, d),
        LineRec::Header => Ok(()),
        LineRec::Blank => Ok(()),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:844-876 ParseResultD
/// The direct parse result: declarations over `Expr` and the taint skips.
pub struct ParseResultD {
    /// the built-in prelude's records first, then the stream's
    pub decls: Vec<DeclC>,
    pub taint_skipped: Vec<(Name, Name)>,
    /// projection functions rewritten to recursor form
    pub proj_rewrites: Vec<Name>,
    /// how many of `decls` are the prelude's, and how many stream records
    /// were dropped as identical copies of prelude records: the stream's
    /// accepted-record count is `decls.len() - prelude_count + prelude_dropped`
    pub prelude_count: u64,
    pub prelude_dropped: u64,
    /// the records moved ahead of a pinned `Nat` operation they ground
    pub hoisted: Vec<Name>,
    /// the blocks modelled in-process, in stream order (always empty: #38)
    pub in_modelled: Vec<Name>,
    /// how many of `decls` the in-process modeller generated, and which block
    /// each of them models (always empty: #38)
    pub gen_records: u64,
    pub gen_owner: HashMap<NameKey, Name>,
    /// the census's declines (block, reason)
    pub in_model_declined: Vec<(Name, String)>,
}

/// con-leche: ConLeche/Frontend/ExportC.lean:887-894 ParseResultD.ofState
/// The result: the prelude's records, then the stream's with every pinned
/// operation's stream-certified ground hoisted ahead of it.
pub fn parse_result_of_state(st: StateD) -> ParseResultD {
    let StateD {
        decls,
        taint_skipped,
        proj_rewrites,
        prelude,
        gen_records,
        gen_owner,
        in_modelled,
        in_model_declined,
        prelude_dropped,
        ..
    } = st;
    let (stream, hoisted) = hoist_nat_op_ground(decls);
    let prelude_count = prelude.decls.len() as u64;
    let mut out = prelude.decls;
    out.extend(stream);
    ParseResultD {
        decls: out,
        taint_skipped,
        proj_rewrites,
        prelude_count,
        prelude_dropped,
        hoisted,
        in_modelled,
        gen_records,
        gen_owner,
        in_model_declined,
    }
}

/// con-leche: none — `FrontendError` from a `LineErr`, at a line number: the
/// `applyFinalLine`/`feedChunk` arms that turn `M`'s message into
/// `.parseError line msg` and a record verdict into its own error.
pub fn line_err_to_frontend(e: LineErr, line_no: u64) -> FrontendError {
    match e {
        LineErr::Msg(m) => FrontendError::ParseError(line_no, m),
        LineErr::Verdict(v) => crate::frontend::export::record_verdict_to_error(v),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:896-906 applyFinalLine
/// Scan and apply the LAST line of a stream — the one no newline ends.  A
/// syntactic failure is reported at its offset in the line.
pub fn apply_final_line(
    st: &mut StateD,
    b: &[u8],
    i: usize,
    line_no: u64,
) -> Result<(), FrontendError> {
    match scan_fast::scan_line_fwd(b, i) {
        Err(e) => Err(FrontendError::ParseError(
            line_no,
            scan_err_render(&crate::frontend::scan_types::ScanErr {
                offset: e.offset - i,
                what: e.what,
            }),
        )),
        Ok((r, _)) => apply_line(st, &r).map_err(|e| line_err_to_frontend(e, line_no)),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:908-943 feedChunk
/// Every COMPLETE line of the chunk from `i`, applied in order: the line count
/// and where the incomplete tail begins (the caller carries it into the next
/// chunk).  A line a chunk cut in half is told from a malformed one by whether
/// the rest of the chunk holds a newline at all — which is why a scan failure
/// is not immediately an error.
pub fn feed_chunk(
    st: &mut StateD,
    b: &[u8],
    i: usize,
    line_no: u64,
) -> Result<(u64, usize), FrontendError> {
    let mut i = i;
    let mut line_no = line_no;
    while i < b.len() {
        match scan_fast::scan_line_fwd(b, i) {
            Err(e) => {
                return if scan_fast::newline_from(b, i) {
                    Err(FrontendError::ParseError(
                        line_no + 1,
                        scan_err_render(&crate::frontend::scan_types::ScanErr {
                            offset: e.offset - i,
                            what: e.what,
                        }),
                    ))
                } else {
                    Ok((line_no, i))
                };
            }
            Ok((r, j)) => {
                // `0` is the recogniser's "the buffer ended before a newline
                // did": these bytes are an incomplete tail, not a line.
                if j == 0 {
                    return Ok((line_no, i));
                }
                apply_line(st, &r).map_err(|e| line_err_to_frontend(e, line_no + 1))?;
                if i >= j {
                    return Err(FrontendError::ParseError(
                        line_no + 1,
                        "the line scanner made no progress".to_string(),
                    ));
                }
                i = j;
                line_no += 1;
            }
        }
    }
    Ok((line_no, i))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:945-946 chunkSize
/// How many bytes the streaming driver asks for at a time.
pub const CHUNK_SIZE: usize = 4 * 1024 * 1024;

/// con-leche: ConLeche/Frontend/ExportC.lean:948-961 parseExportD
/// Wholesale direct parse (tests and small inputs).  `prelude` is the built-in
/// prelude the result is prepended with and deduped against (empty for the
/// prelude's own parse).
pub fn parse_export_d(
    contents: &[u8],
    prelude: PreludeIx,
    in_model: bool,
    census: bool,
) -> Result<ParseResultD, FrontendError> {
    let mut st = state_d_init(prelude, in_model, census);
    let (line_no, tail) = feed_chunk(&mut st, contents, 0, 0)?;
    if tail < contents.len() {
        apply_final_line(&mut st, contents, tail, line_no + 1)?;
    }
    Ok(parse_result_of_state(st))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:963-996 parseExportHandleD
/// Streaming direct parse off an open reader.
///
/// The reader is read strictly forward, 4 MiB at a time, and is never seeked,
/// re-opened or asked for its size — so the source may be a *pipe* just as
/// well as a file (con-leche task #180: no scratch file at all, anywhere).
/// It is a property to preserve: a seek or a re-open here would silently
/// re-introduce a temp file.  The unconsumed tail of a chunk — at most one
/// incomplete line — is carried into the next one.
pub fn parse_export_handle_d<R: Read>(
    h: &mut R,
    prelude: PreludeIx,
    in_model: bool,
    census: bool,
    chunk: usize,
) -> std::io::Result<Result<ParseResultD, FrontendError>> {
    let mut st = state_d_init(prelude, in_model, census);
    let mut carry: Vec<u8> = Vec::new();
    let mut line_no: u64 = 0;
    let mut buf0: Vec<u8> = vec![0u8; chunk];
    loop {
        let n = read_up_to(h, &mut buf0)?;
        if n == 0 {
            if !carry.is_empty() {
                if let Err(e) = apply_final_line(&mut st, &carry, 0, line_no + 1) {
                    return Ok(Err(e));
                }
            }
            return Ok(Ok(parse_result_of_state(st)));
        }
        let buf: Vec<u8> = if carry.is_empty() {
            buf0[..n].to_vec()
        } else {
            let mut v = std::mem::take(&mut carry);
            v.extend_from_slice(&buf0[..n]);
            v
        };
        match feed_chunk(&mut st, &buf, 0, line_no) {
            Err(e) => return Ok(Err(e)),
            Ok((l, tail)) => {
                line_no = l;
                carry = buf[tail..].to_vec();
            }
        }
    }
}

/// con-leche: none — `IO.FS.Handle.read`, which returns *up to* `n` bytes and
/// an empty buffer at end of file; `Read::read` may also stop short of a full
/// buffer mid-file, so the port loops until the buffer is full or the reader
/// is done.
pub fn read_up_to<R: Read>(h: &mut R, buf: &mut [u8]) -> std::io::Result<usize> {
    let mut got = 0usize;
    while got < buf.len() {
        match h.read(&mut buf[got..]) {
            Ok(0) => break,
            Ok(n) => got += n,
            Err(ref e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }
    Ok(got)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:998-1003 parseExportStreamD
/// Streaming direct parse of a file.
pub fn parse_export_stream_d(
    path: &str,
    prelude: PreludeIx,
    in_model: bool,
    census: bool,
    chunk: usize,
) -> std::io::Result<Result<ParseResultD, FrontendError>> {
    let mut f = std::fs::File::open(path)?;
    parse_export_handle_d(&mut f, prelude, in_model, census, chunk)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(text: &str) -> Result<ParseResultD, FrontendError> {
        parse_export_d(text.as_bytes(), prelude_ix_empty(), true, false)
    }

    /// A minimal stream: the header, one name, one level, one sort and an
    /// axiom over it.
    #[test]
    fn a_minimal_stream_parses() {
        let s = concat!(
            "{\"meta\":{\"exporter\":{\"name\":\"lean4export\"}}}\n",
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n",
            "{\"il\":1,\"succ\":0}\n",
            "{\"ie\":0,\"sort\":1}\n",
            "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}\n"
        );
        let r = parse(s).unwrap_or_else(|e| panic!("{:?}", e));
        assert_eq!(r.decls.len(), 1);
        assert_eq!(r.prelude_count, 0);
        match &r.decls[0] {
            DeclC::AxiomDecl(cv) => assert_eq!(name_str(&cv.name), "A"),
            _ => panic!("not an axiom"),
        }
    }

    /// An undefined index is a parse error naming the line, not a panic.
    #[test]
    fn an_undefined_index_is_a_parse_error() {
        let s = "{\"ie\":0,\"sort\":7}\n";
        match parse(s) {
            Err(FrontendError::ParseError(line, msg)) => {
                assert_eq!(line, 1);
                assert!(msg.contains("undefined level index 7"), "{}", msg);
            }
            other => panic!("{:?}", other.err()),
        }
    }

    /// An unsafe declaration is a DECLINE, not an error.
    #[test]
    fn unsafe_declarations_decline() {
        let s = concat!(
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n",
            "{\"ie\":0,\"sort\":0}\n",
            "{\"axiom\":{\"isUnsafe\":true,\"levelParams\":[],\"name\":1,\"type\":0}}\n"
        );
        match parse(s) {
            Err(FrontendError::Unsupported(w)) => assert_eq!(w, "unsafe axiom"),
            other => panic!("{:?}", other.err()),
        }
    }

    /// A mutual block reaches the modeller and the modeller declines it,
    /// naming the block AND the class: this one has no recursors, so the
    /// generator's own shape check is what refuses it (task #39).
    #[test]
    fn a_mutual_block_declines_at_the_modeller_point() {
        // two type formers `T : Type` and `U : Type`, one constructor each,
        // no recursors: enough for `wants` (two types) without being a
        // well-formed block, because the decline happens before any install.
        let s = concat!(
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"T\"}}\n",
            "{\"in\":2,\"str\":{\"pre\":1,\"str\":\"mk\"}}\n",
            "{\"in\":3,\"str\":{\"pre\":0,\"str\":\"U\"}}\n",
            "{\"in\":4,\"str\":{\"pre\":3,\"str\":\"mk\"}}\n",
            "{\"il\":1,\"succ\":0}\n",
            "{\"ie\":0,\"sort\":1}\n",
            "{\"ie\":1,\"const\":{\"name\":1,\"us\":[]}}\n",
            "{\"ie\":2,\"const\":{\"name\":3,\"us\":[]}}\n",
            "{\"inductive\":{\"ctors\":[",
            "{\"isUnsafe\":false,\"levelParams\":[],\"name\":2,\"numFields\":0,",
            "\"numParams\":0,\"type\":1},",
            "{\"isUnsafe\":false,\"levelParams\":[],\"name\":4,\"numFields\":0,",
            "\"numParams\":0,\"type\":2}],\"recs\":[],\"types\":[",
            "{\"ctors\":[2],\"isRec\":false,\"isReflexive\":false,\"isUnsafe\":false,",
            "\"levelParams\":[],\"name\":1,\"numIndices\":0,\"numNested\":0,",
            "\"numParams\":0,\"type\":0},",
            "{\"ctors\":[4],\"isRec\":false,\"isReflexive\":false,\"isUnsafe\":false,",
            "\"levelParams\":[],\"name\":3,\"numIndices\":0,\"numNested\":0,",
            "\"numParams\":0,\"type\":0}]}}\n"
        );
        match parse(s) {
            Err(FrontendError::Unsupported(w)) => {
                assert!(w.starts_with("in-process model of T:"), "{}", w);
                assert!(
                    w.contains("recursor count differs from member count"),
                    "{}",
                    w
                );
            }
            other => panic!("{:?}", other.err()),
        }
        // with the modeller off the block is pushed bare, as in con-leche
        let r = parse_export_d(s.as_bytes(), prelude_ix_empty(), false, false)
            .unwrap_or_else(|e| panic!("{:?}", e));
        assert_eq!(r.decls.len(), 1);
        // and in census mode it is reported and the parse continues
        let r = parse_export_d(s.as_bytes(), prelude_ix_empty(), true, true)
            .unwrap_or_else(|e| panic!("{:?}", e));
        assert_eq!(r.in_model_declined.len(), 1);
        assert_eq!(name_str(&r.in_model_declined[0].0), "T");
    }

    /// A block whose constructor declares the wrong `numFields` is INVALID
    /// (exit 1), not declined: the stream contradicts its own declarations.
    #[test]
    fn a_contradicted_redundant_field_is_invalid() {
        let s = concat!(
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"T\"}}\n",
            "{\"in\":2,\"str\":{\"pre\":1,\"str\":\"mk\"}}\n",
            "{\"il\":1,\"succ\":0}\n",
            "{\"ie\":0,\"sort\":1}\n",
            "{\"ie\":1,\"const\":{\"name\":1,\"us\":[]}}\n",
            "{\"inductive\":{\"ctors\":[",
            "{\"isUnsafe\":false,\"levelParams\":[],\"name\":2,\"numFields\":3,",
            "\"numParams\":0,\"type\":1}],\"recs\":[],\"types\":[",
            "{\"ctors\":[2],\"isRec\":false,\"isReflexive\":false,\"isUnsafe\":false,",
            "\"levelParams\":[],\"name\":1,\"numIndices\":0,\"numNested\":0,",
            "\"numParams\":0,\"type\":0}]}}\n"
        );
        match parse(s) {
            Err(FrontendError::Invalid(w)) => {
                assert!(w.contains("declares 3 fields"), "{}", w);
            }
            other => panic!("{:?}", other.err()),
        }
    }

    /// The chunk boundary: the same stream parsed in 8-byte chunks gives the
    /// same records, because an incomplete line is carried and not
    /// misreported.
    #[test]
    fn chunking_does_not_change_the_parse() {
        let s = concat!(
            "{\"meta\":{\"exporter\":{\"name\":\"lean4export\"}}}\n",
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n",
            "{\"ie\":0,\"sort\":0}\n",
            "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}\n"
        );
        let whole = parse(s).unwrap_or_else(|e| panic!("{:?}", e));
        for chunk in [1usize, 2, 7, 8, 13, 64] {
            let mut cur = std::io::Cursor::new(s.as_bytes().to_vec());
            let r = parse_export_handle_d(&mut cur, prelude_ix_empty(), true, false, chunk)
                .expect("io")
                .unwrap_or_else(|e| panic!("chunk {}: {:?}", chunk, e));
            assert_eq!(r.decls.len(), whole.decls.len(), "chunk {}", chunk);
        }
    }

    /// A final line with no newline is applied (`applyFinalLine`).
    #[test]
    fn a_final_line_without_a_newline_is_applied() {
        let s = concat!(
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n",
            "{\"ie\":0,\"sort\":0}\n",
            "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}"
        );
        let r = parse(s).unwrap_or_else(|e| panic!("{:?}", e));
        assert_eq!(r.decls.len(), 1);
    }
}

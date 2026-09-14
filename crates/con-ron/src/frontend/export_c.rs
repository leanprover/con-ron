//! `ConLeche/Frontend/ExportC.lean` — the **semantic layer** of the parse:
//! `apply_line` resolves a scanned record's stream indices against the parse
//! tables and builds the `Name`/`Level`/`Expr` nodes through con-ron-core's
//! smart constructors.
//!
//! The export's `ie`-indices *are* the sharing: the format already
//! externalises exactly the DAG structure an arena would reconstruct, so the
//! parse keeps a stream-index-keyed table of `Expr` **values** and a table hit
//! is a shared node by reference (an `Rc` clone).  Nothing rebuilds a term.
//!
//! **THE DECODER EMITS THE FILE'S RECORDS AND NOTHING ELSE** (con-leche task
//! #293).  Every inductive block parses to an `IndDecl` — `Nat` and `Eq` like
//! any other — and every `#QUOT` record to a `QuotDecl` carrying the constant
//! the file declares at the kind it declares it at.  No basis recognition, no
//! reserved-name logic, no prelude, no dedupe and no reordering happen here:
//! the checker's own prelude is put in front, the pinned shapes are recognised
//! and the pinned `Nat` operations' ground is hoisted by
//! `crate::frontend::prepare`, between this parse and the fold, and every
//! VERDICT — a basis redefinition, a quotient mismatch, a stream copy of a
//! prelude record that differs — is the fold's.
//!
//! **Two non-decoding steps are left here**, and both die with the in-process
//! modeller (con-leche task #279):
//!
//! * **the projection-function rewrite** (`crate::frontend::proj_rec`), the
//!   one surface rewrite this parse performs on a definition record: a
//!   projection function `fun p⃗ self => .proj T i self` of a structure-like
//!   owner the direct install does not serve is replaced, before it reaches
//!   the checker, by the recursor application that module documents.  Two
//!   bookkeeping tables feed it — `proj_owners` and `proj_levels`;
//! * **the in-process modeller** (`crate::in_model`): a mutual or nested
//!   block's `_model` family is generated here and pushed ahead of the block.
//!
//! ## The in-process modeller
//!
//! `install_ind_d` does that at the point `in_model_wants` says yes: it builds
//! the `BlockRec` (`block_rec_of`), calls `in_model::generate`, pushes the
//! records it returns through `push_gen_list` — which books each of them with
//! `note_gen_names` — and only then pushes the block.  A generator decline is
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
//! ## Two parser tightenings (con-leche task #290)
//!
//! * **an index is bound once**: a line that binds a table index a previous
//!   line already bound is a parse error (`rebound_error`, the three
//!   `st_fresh_*` tests).  What the rule buys is the one property a theorem
//!   about the FILE needs of the tables — the entry a line bound is the entry
//!   every later line reads, whatever else the file holds;
//! * **the size guard**: the byte reader addresses its buffer by machine
//!   word, so an input of `USize.size` bytes or more is refused before any of
//!   it is read (`size_error`, and the running `total` the chunk step carries).
//!
//! ## Other deviations
//!
//! * `M (StateD ⊕ RecordVerdict)` becomes `Result<(), LineErr>` over a
//!   `&mut StateD`: one error channel with two arms instead of a monad over a
//!   sum, and the state threaded by mutable reference instead of returned.
//!   con-leche threads it linearly for the same reason Rust's `&mut` gives
//!   for free (`ExportC.lean`'s task-#78 note: a handler that closes over the
//!   state holds it at RC 2 and every insert inside copies it).  The two
//!   `LineErr` arms become `(CheckError, line)` at the two call sites that
//!   know the line (`apply_final_line`, `feed_chunk`).
//! * `IdTable.bound` has no counterpart in `scan_types` (it arrived with
//!   con-leche task #290 and its only consumers are the three tests below), so
//!   the three read the table through `id_table_get(…).is_some()` —
//!   `IdTable.bound_eq`, which con-leche proves beside the definition.
//!   con-leche writes the test against a BORROWED state because an owned one
//!   made its compiler project and `inc` every field before the test; `&StateD`
//!   is that, by construction.
//! * `feed_chunk` and `parse_export_handle_d` read `&[u8]` slices of a
//!   `Vec<u8>` buffer rather than a `ByteArray`; the chunk size, the carried
//!   tail and the "position 0 means an incomplete tail" contract are
//!   con-leche's.

use std::collections::{HashMap, HashSet};
use std::io::Read;

use con_ron_core::kernel::basis_raw;
use con_ron_core::kernel::core_types;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env;
use con_ron_core::kernel::env::{
    ConstantInfo, ConstantVal, Declaration, QuotKind, ReducibilityHint,
};
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::{Expr, ExprKind};
use con_ron_core::kernel::expr_ops;
use con_ron_core::kernel::level;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::{Name, NameKind};
use con_ron_core::kernel::prop_when;
use con_ron_core::kernel::prop_when::PropWhen;

use crate::frontend::export::{cps, name_str, record_verdict_to_error, RecordVerdict};
use crate::frontend::nat_op_ground::NameKey;
use crate::frontend::proj_rec;
use crate::frontend::scan_fast;
use crate::frontend::scan_types::{
    id_table_get, id_table_insert, id_table_singleton, scan_err_render, CVRec, DeclRec, ExprRec,
    HintsRec, IdTable, IndCtorRec, IndRecRec, IndTypeRec, LevelRec, LineRec, NameRec, PwRec,
    RuleRec,
};
use crate::in_model;

/// con-leche: ConLeche/Frontend/Export.lean:117 M
/// con-leche: ConLeche/Frontend/Export.lean:71-79 RecordVerdict
/// The two ways applying one line can fail: a parse message (con-leche's
/// `M = Except String`) or a record verdict (its `StateD ⊕ RecordVerdict`'s
/// right summand).  Merging them into one `Result` is this module's first
/// deviation; the two arms are told apart again at `line_err_to_check`, where
/// the line number is in hand.
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

/// con-leche: none — the `M`/verdict pair resolved against the line it was
/// read at: the `applyFinalLine`/`feedChunk` arms that turn `M`'s message into
/// `(.internal msg, line)` and a record verdict into `(v.toError, line)`.
pub fn line_err_to_check(e: LineErr, line_no: u64) -> (CheckError, u64) {
    match e {
        LineErr::Msg(m) => (core_types::internal(cps(&m)), line_no),
        LineErr::Verdict(v) => (record_verdict_to_error(v), line_no),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:78-134 StateD
/// The direct parse state: stream-index-keyed tables of *values* (names and
/// levels as trees, expressions as `Expr` — a table hit is a shared node by
/// reference) and the parsed declarations as `Declaration`.  `inModelGen`, the
/// debug dump's field, is not ported (the module note).
pub struct StateD {
    pub names: IdTable<Name>,
    pub levels: IdTable<Level>,
    pub exprs: IdTable<Expr>,
    pub decls: Vec<Declaration>,
    /// structure-like owners the projection rewrite serves, by type name
    pub proj_owners: HashMap<NameKey, proj_rec::ProjRecOwner>,
    /// field sorts, by artifact iota name `T._model.proj_i.iota` (the
    /// in-process modeller's own, and only those)
    pub proj_levels: HashMap<NameKey, Level>,
    /// projection functions rewritten so far (names, for the driver's trace)
    pub proj_rewrites: Vec<Name>,
    /// the declared types of every declaration pushed so far, by name: the
    /// in-process modeller's sort inferer reads them
    pub const_types: HashMap<NameKey, (Vec<Name>, Expr)>,
    /// the definitional heights of the definitions pushed so far (the hints
    /// of the generated definitions are computed from them)
    pub heights: HashMap<NameKey, u64>,
    /// in-process modelling of mutual/nested blocks is on
    pub in_model: bool,
    /// the blocks modelled in-process, in stream order
    pub in_modelled: Vec<Name>,
    /// how many records the in-process modeller GENERATED and pushed: they are
    /// declarations of the fold like any other, but they are not records of
    /// the FILE, so the driver's headline count subtracts them
    pub gen_records: u64,
    /// each generated record's leading name ↦ the block it models
    pub gen_owner: HashMap<NameKey, Name>,
    /// the number of `inductive` records seen so far
    pub ind_count: u64,
    /// the parsed inductive blocks, by member type name (the in-process
    /// modeller's nested rung reads a container's shape off it)
    pub ind_blocks: HashMap<NameKey, std::rc::Rc<in_model::mutual::BlockRec>>,
    /// CENSUS mode (`CON_LECHE_INMODEL_CENSUS=1`): a generator decline is
    /// recorded and the block pushed bare instead of declining the parse
    pub in_model_census: bool,
    /// the census's declines: block name and reason
    pub in_model_declined: Vec<(Name, String)>,
}

/// con-leche: ConLeche/Frontend/ExportC.lean:755-758 StateD.init
/// The initial parse state.  There is no prelude here any more (con-leche task
/// #293): the parse starts from the file's first record, and putting the
/// prelude's declarations in front is `prepare::prepare_prelude`'s.
pub fn state_d_init(in_model: bool, census: bool) -> StateD {
    StateD {
        names: id_table_singleton(name::anonymous()),
        levels: id_table_singleton(level::zero()),
        exprs: crate::frontend::scan_types::id_table_empty(),
        decls: Vec::new(),
        proj_owners: HashMap::new(),
        proj_levels: HashMap::new(),
        proj_rewrites: Vec::new(),
        const_types: HashMap::new(),
        heights: HashMap::new(),
        in_model,
        in_modelled: Vec::new(),
        gen_records: 0,
        gen_owner: HashMap::new(),
        ind_count: 0,
        ind_blocks: HashMap::new(),
        in_model_census: census,
        in_model_declined: Vec::new(),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:135-153 noteDecl
/// con-leche: ConLeche/Kernel/Basis.lean:40-47 BasisKind.decls
/// The constants one pushed declaration declares, with their level
/// parameters, declared types and (for a definition) definitional height:
/// the cited `cvs`.
pub fn note_decl_entries(d: &Declaration) -> Vec<(Name, Vec<Name>, Expr, Option<u64>)> {
    let one = |cv: &ConstantVal, h: Option<u64>| -> Vec<(Name, Vec<Name>, Expr, Option<u64>)> {
        vec![(
            name::dup(&cv.name),
            cv.level_params.iter().map(name::dup).collect(),
            expr::dup(&cv.ty),
            h,
        )]
    };
    let block = |bl: &Vec<ConstantInfo>| -> Vec<(Name, Vec<Name>, Expr, Option<u64>)> {
        bl.iter()
            .map(|ci| {
                let cv = env::to_constant_val(ci);
                (
                    name::dup(&cv.name),
                    cv.level_params.iter().map(name::dup).collect(),
                    expr::dup(&cv.ty),
                    None,
                )
            })
            .collect()
    };
    match d {
        Declaration::AxiomDecl(cv) => one(cv, None),
        Declaration::DefnDecl(cv, _, h) => one(cv, Some(in_model::kit::hint_height(h))),
        Declaration::ThmDecl(cv, _) => one(cv, None),
        Declaration::OpaqueDecl(cv, _) => one(cv, None),
        Declaration::BasisDecl(k) => block(&basis_raw::basis_kind_decls(k)),
        Declaration::QuotDecl(_, cv) => one(cv, None),
        Declaration::IndDecl(bl, _) => block(bl),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:135-153 noteDecl
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

/// con-leche: ConLeche/Frontend/ExportC.lean:135-153 noteDecl
/// Record a pushed declaration's constants in the declaration table
/// (`const_types`, `heights`).
pub fn note_decl(st: &mut StateD, d: &Declaration) {
    let es = note_decl_entries(d);
    note_entries(st, es);
}

/// con-leche: ConLeche/Frontend/ExportC.lean:155-162 pushDecl
/// **One parsed record, appended** (con-leche task #293): the decoder keeps
/// the file's records in the file's order, so this is total — it cannot
/// decline and it cannot drop.  What used to sit here was the prelude dedupe —
/// a basis block the prelude held dropped by kind, a record under a prelude
/// name dropped when identical and DECLINING the stream when different — and
/// it is `prepare::prepare_prelude`'s and the fold's now.
pub fn push_decl(st: &mut StateD, d: Declaration) {
    note_decl(st, &d);
    st.decls.push(d);
}

/// con-leche: ConLeche/Frontend/ExportC.lean:164-167 StateD.name
pub fn st_name(st: &StateD, i: u64) -> Result<Name, LineErr> {
    match id_table_get(&st.names, i) {
        Some(n) => Ok(name::dup(n)),
        None => merr(format!("undefined name index {}", i)),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:169-172 StateD.level
pub fn st_level(st: &StateD, i: u64) -> Result<Level, LineErr> {
    match id_table_get(&st.levels, i) {
        Some(l) => Ok(level::dup(l)),
        None => merr(format!("undefined level index {}", i)),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:174-177 StateD.expr
pub fn st_expr(st: &StateD, i: u64) -> Result<Expr, LineErr> {
    match id_table_get(&st.exprs, i) {
        Some(e) => Ok(expr::dup(e)),
        None => merr(format!("undefined expr index {}", i)),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:179-189 getDeclD
/// Declaration-level expression lookup: the table read.  (The frontend
/// tree-size budget that used to sit here was retired at con-leche task #215,
/// and the taint sentinel that stood beside it at task #292; the DAG-tower
/// fixtures are the standing gate in the budget's place.)
pub fn get_decl_d(st: &StateD, i: u64) -> Result<Expr, LineErr> {
    st_expr(st, i)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:191-194 parsePwD
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

/// con-leche: ConLeche/Frontend/ExportC.lean:207-209 reboundError
/// The rebinding error, named once.
pub fn rebound_error(what: &str, i: u64) -> String {
    format!("{} index {} is already bound", what, i)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:211-220 StateD.freshName
/// con-leche: ConLeche/Frontend/Scan/Types.lean:363-372 IdTable.bound
/// Every table entry is bound once (con-leche task #290): a line that binds an
/// index a previous line already bound is a parse error.  The tables let a
/// later line overwrite an entry all the same (they are resolved eagerly, so
/// nothing already built could change); what the rule buys is the one property
/// a theorem about the FILE needs of them — the entry a line bound is the
/// entry every later line reads, whatever else the file holds.
///
/// `scan_types` has no `bound`, so the test reads the table instead —
/// `IdTable.bound_eq`, which con-leche proves beside the definition.  The
/// state is BORROWED for the same reason con-leche's is: an owned one made its
/// compiler project and `inc` every field before the test.
pub fn st_fresh_name(st: &StateD, i: u64) -> Result<(), LineErr> {
    if id_table_get(&st.names, i).is_some() {
        merr(rebound_error("name", i))
    } else {
        Ok(())
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:221-222 StateD.freshLevel
/// con-leche: ConLeche/Frontend/Scan/Types.lean:363-372 IdTable.bound
/// `st_fresh_name` on the level table.
pub fn st_fresh_level(st: &StateD, i: u64) -> Result<(), LineErr> {
    if id_table_get(&st.levels, i).is_some() {
        merr(rebound_error("level", i))
    } else {
        Ok(())
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:223-224 StateD.freshExpr
/// con-leche: ConLeche/Frontend/Scan/Types.lean:363-372 IdTable.bound
/// `st_fresh_name` on the expression table.
pub fn st_fresh_expr(st: &StateD, i: u64) -> Result<(), LineErr> {
    if id_table_get(&st.exprs, i).is_some() {
        merr(rebound_error("expression", i))
    } else {
        Ok(())
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:228-237 parseNameEntryD
/// A name-table entry: the name value is built directly.  The parent index is
/// resolved before the freshness test, as in the cited `do` block.
pub fn parse_name_entry_d(st: &mut StateD, i: u64, r: &NameRec) -> Result<(), LineErr> {
    let v = match r {
        NameRec::Str(pre, s) => {
            let p = st_name(st, *pre)?;
            st_fresh_name(st, i)?;
            name::mk_str(p, s.clone())
        }
        NameRec::Num(pre, n) => {
            let p = st_name(st, *pre)?;
            st_fresh_name(st, i)?;
            name::mk_num(p, *n)
        }
    };
    id_table_insert(&mut st.names, i, v);
    Ok(())
}

/// con-leche: ConLeche/Frontend/ExportC.lean:239-247 parseLevelEntryD
/// A level-table entry.
pub fn parse_level_entry_d(st: &mut StateD, i: u64, r: &LevelRec) -> Result<(), LineErr> {
    st_fresh_level(st, i)?;
    let l = match r {
        LevelRec::Succ(u) => level::succ(st_level(st, *u)?),
        LevelRec::Max(a, b) => level::max(st_level(st, *a)?, st_level(st, *b)?),
        LevelRec::Imax(a, b) => level::imax(st_level(st, *a)?, st_level(st, *b)?),
        LevelRec::Param(n) => level::param(st_name(st, *n)?),
    };
    id_table_insert(&mut st.levels, i, l);
    Ok(())
}

/// con-leche: ConLeche/Frontend/ExportC.lean:249-279 parseExprEntryD
/// An expression-table entry: build the node from the children's table values
/// (the derived fields are the smart constructors').  Binder names are display
/// data the official kernel's equality and hash ignore; ours are `.anonymous`
/// on every parsed binder, so `==` is α-equivalence downstream.
pub fn parse_expr_entry_d(st: &mut StateD, i: u64, r: &ExprRec) -> Result<(), LineErr> {
    st_fresh_expr(st, i)?;
    let e: Expr = match r {
        ExprRec::Bvar(k) => expr::mk_bvar(*k),
        ExprRec::Sort(u) => expr::sort(st_level(st, *u)?),
        ExprRec::Const(n, us) => {
            let nm = st_name(st, *n)?;
            let mut ls: Vec<Level> = Vec::new();
            for u in us {
                ls.push(st_level(st, *u)?);
            }
            expr::mk_const(nm, ls)
        }
        ExprRec::App(f, a) => expr::app(st_expr(st, *f)?, st_expr(st, *a)?),
        ExprRec::Lam(ty, bd, pw) => expr::lam(
            st_expr(st, *ty)?,
            st_expr(st, *bd)?,
            expr::binder_meta(parse_pw_d(st, pw)?),
        ),
        ExprRec::ForallE(ty, bd, pw) => expr::forall_e(
            st_expr(st, *ty)?,
            st_expr(st, *bd)?,
            expr::binder_meta(parse_pw_d(st, pw)?),
        ),
        ExprRec::LetE(ty, vl, bd) => {
            expr::let_e(st_expr(st, *ty)?, st_expr(st, *vl)?, st_expr(st, *bd)?)
        }
        ExprRec::Proj(tn, ix, s) => expr::proj(st_name(st, *tn)?, *ix, st_expr(st, *s)?),
        ExprRec::NatVal(digits) => {
            let n = match con_ron_dump::natdec::from_decimal(digits) {
                Ok(n) => n,
                Err(e) => return merr(format!("malformed natVal literal: {}", e)),
            };
            expr::lit(expr::literal_nat(n))
        }
        ExprRec::StrVal(s) => expr::lit(expr::literal_str(s.clone())),
    };
    id_table_insert(&mut st.exprs, i, e);
    Ok(())
}

/// con-leche: ConLeche/Frontend/ExportC.lean:283-289 parseCVD
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

/// con-leche: ConLeche/Frontend/ExportC.lean:291-302 projRewriteD
/// The projection-function rewrite at a definition record: the value is
/// `fun p⃗ self => .proj T i self` for a recorded owner `T`, the field's sort
/// is on record from the artifact, and the definition's level parameters are
/// the block's.  `None` = leave the record as parsed.  (The `punitSeen` guard
/// that stood here went with con-leche task #293: the `PUnit` block the
/// constant motives need is the prelude's, put in front of every fold by
/// `prepare::prepare_prelude`, so the parse no longer tracks whether the
/// stream has declared one.)
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
    if !crate::frontend::export::names_beq(&cv.level_params, &o.lps) {
        return None;
    }
    let l = st
        .proj_levels
        .get(&NameKey(proj_rec::proj_iota_name(&t, i)))?;
    proj_rec::proj_rec_value(o, l, &cv.ty, vl, i)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:304-317 noteProjIota
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

/// con-leche: ConLeche/Frontend/ExportC.lean:319-326 pushGenD
/// Push one record the in-process modeller generated: `push_decl`, plus the
/// projection-iota registration (the ONLY place it runs).  Total since
/// con-leche task #293, as `push_decl` is.
pub fn push_gen_d(st: &mut StateD, d: Declaration) {
    if let Declaration::ThmDecl(cv, _) = &d {
        let cv2 = env::constant_val_dup(cv);
        note_proj_iota(st, &cv2);
    }
    push_decl(st, d)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:328-336 noteGen
/// Book a record the in-process modeller generated for block `T0`: a
/// declaration of the FOLD, never a record of the file, so the driver's
/// headline count subtracts it and a failure at it is reported with the block
/// it models.
pub fn note_gen(st: &mut StateD, d: &Declaration, t0: &Name) {
    note_gen_names(st, env::declaration_names(d), t0);
}

/// con-leche: ConLeche/Frontend/ExportC.lean:328-336 noteGen
/// `note_gen` at the record's names already in hand.  `push_gen_list` needs
/// this half: `push_gen_d` takes the `Declaration` by value (it is pushed into
/// the state), and con-leche reads `d.names` afterwards because a Lean value
/// is still there to read.
pub fn note_gen_names(st: &mut StateD, names: Vec<Name>, t0: &Name) {
    st.gen_records += 1;
    for n in names {
        st.gen_owner.insert(NameKey(n), name::dup(t0));
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:398-404 pushGenList
/// Push the records the in-process modeller generated (the loop of
/// `install_ind_d`, as a function), each booked as a declaration of the fold
/// and not a record of the file.
pub fn push_gen_list(st: &mut StateD, gen: Vec<Declaration>, t0: &Name) {
    for d in gen {
        let names = env::declaration_names(&d);
        push_gen_d(st, d);
        note_gen_names(st, names, t0);
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:338-344 indPiTeleLen
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

/// con-leche: ConLeche/Frontend/ExportC.lean:346-349 parseRuleD
/// One recursor rule of an inductive record, resolved.
pub fn parse_rule_d(st: &StateD, ru: &RuleRec) -> Result<env::RecRule, LineErr> {
    Ok(env::rec_rule_parsed(
        st_name(st, ru.ctor)?,
        ru.nfields,
        get_decl_d(st, ru.rhs)?,
    ))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:351-375 blockRecOf
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

/// con-leche: ConLeche/Frontend/InModel.lean:34-37 wants
/// Is the block one the modeller is for: mutual (several types) or nested
/// (`numNested > 0`)?  con-leche asks this of the `InModel.BlockRec`
/// `blockRecOf` builds; the two fields it reads are the scan records' own
/// (`types.length` and `numNested`), so the port asks it of those and needs
/// neither `BlockRec` nor `blockRecOf` (the module note).
pub fn in_model_wants(tys: &[IndTypeRec]) -> bool {
    tys.len() > 1 || tys.iter().any(|t| t.num_nested > 0)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:377-396 registerProjOwners
/// Record the structure-like owners of a parsed block that the projection
/// rewrite serves (`proj_rec::proj_rec_owners`).
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


/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// **An inductive record, validated** (con-leche tasks #217, #228, #271): the
/// half of the record's processing that reads the state and changes nothing —
/// the verdict, or the block's constructors in the block's own order with the
/// declared parameter count.  Split from `install_ind_d` at con-leche task
/// #290 so that a proof about what the parse does to its state need not look
/// here at all; the state is BORROWED, which is that split in the type.
///
/// Deviation: con-leche returns `RecordVerdict ⊕ (List IndCtorRec × Nat)` and
/// the port returns the verdict through `LineErr`, the module's one merged
/// error channel.
pub fn validate_ind_d(
    st: &StateD,
    tys: &[IndTypeRec],
    cts: &[IndCtorRec],
    rcs: &[IndRecRec],
) -> Result<(Vec<IndCtorRec>, u64), LineErr> {
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
    Ok((cts, n_pd))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:560-623 installIndD
/// **An inductive record, installed**: the block's constants, the
/// projection-owner table, the in-process modeller, the push.  Every change
/// to the state a validated inductive record makes is here.
pub fn install_ind_d(
    st: &mut StateD,
    tys: &[IndTypeRec],
    cts: Vec<IndCtorRec>,
    rcs: &[IndRecRec],
    n_pd: u64,
) -> Result<(), LineErr> {
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
    // **EVERY BLOCK IS AN `IndDecl`** (con-leche task #293): the basis-pin
    // match that used to stand here - a name pre-filter and then
    // `canon_eq_list` against the five pinned blocks - is the FOLD's
    // (`checker::check_decl` asks `basis_raw::basis_pin_hit`).  A block under
    // a pinned name that does NOT match keeps its `IndDecl` form and is
    // rejected by the fold's reserved-name check, exactly as before.
    // THE IN-PROCESS MODELLER (the ONLY model source, and the only one there
    // IS — a stream `_model` record is an ordinary declaration and is never
    // consulted): a mutual or nested block gets its `_model` family generated
    // here and pushed ahead of it; the block then installs through the modeled
    // route.  A generator decline is the run's decline, naming the class (the
    // residual: infinitary nesting, a `Prop` block with a large eliminator).
    let t0 = match block.first() {
        Some(ci) => env::constant_info_name(ci),
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
                    push_decl(st, Declaration::IndDecl(block, n_pd));
                    return Ok(());
                }
                return declined(format!("in-process model of {}: {}", name_str(&t0), why));
            }
            Ok(gen) => {
                // a generated record is a declaration of the FOLD and not a
                // record of the file: booked in `push_gen_list`, so the
                // verdict line reports the file's own count
                push_gen_list(st, gen, &t0);
                st.in_modelled.push(name::dup(&t0));
                push_decl(st, Declaration::IndDecl(block, n_pd));
                return Ok(());
            }
        }
    }
    push_decl(st, Declaration::IndDecl(block, n_pd));
    Ok(())
}

/// con-leche: ConLeche/Frontend/ExportC.lean:625-697 processLineCoreD
/// The record's own semantics: the declaration kinds, producing `Declaration`
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
            // **`Quot.sound` is the FOLD's** (con-leche task #293): the axiom
            // record is forwarded like any other, and the fold compares it
            // with the pinned soundness axiom — the decline on a mismatch was
            // the parser's and is not any more.  **`sorryAx` is the fold's
            // too** (task #292): the record is forwarded, installs nothing,
            // and a *use* of it declines at the record that uses it.
            push_decl(st, Declaration::AxiomDecl(cvp));
            Ok(())
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
                    push_decl(st, Declaration::DefnDecl(cvp, vl2, h));
                    st.proj_rewrites.push(n);
                    Ok(())
                }
                None => {
                    push_decl(st, Declaration::DefnDecl(cvp, vl, h));
                    Ok(())
                }
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
                    push_decl(st, Declaration::ThmDecl(cvp, vl2));
                    st.proj_rewrites.push(n);
                    Ok(())
                }
                None => {
                    push_decl(st, Declaration::ThmDecl(cvp, vl));
                    Ok(())
                }
            }
        }
        DeclRec::Opaq(cvr, value, is_unsafe) => {
            let cvp = parse_cv_d(st, cvr)?;
            if *is_unsafe {
                return declined("unsafe opaque declaration".to_string());
            }
            let vl = get_decl_d(st, *value)?;
            push_decl(st, Declaration::OpaqueDecl(cvp, vl));
            Ok(())
        }
        DeclRec::Quot(cvr, kind) => {
            // **ONE RECORD PER `#QUOT` LINE** (con-leche task #293): the file
            // declares the quotient package as four records, and the decoder
            // emits four — the constant as the file declares it, at the kind
            // the file declares it at.  The comparison with the pinned block
            // and the decline on a mismatch are the fold's `.quotDecl` arm's,
            // not the parser's any more.
            let cv = parse_cv_d(st, cvr)?;
            let qk = match kind.as_str() {
                "type" => QuotKind::Type,
                "ctor" => QuotKind::Ctor,
                "lift" => QuotKind::Lift,
                "ind" => QuotKind::Ind,
                k => return merr(format!("unknown quotient kind '{}'", k)),
            };
            push_decl(st, Declaration::QuotDecl(qk, cv));
            Ok(())
        }
        DeclRec::Ind(tys, cts, rcs) => {
            st.ind_count += 1;
            let (cts, n_pd) = validate_ind_d(st, tys, cts, rcs)?;
            install_ind_d(st, tys, cts, rcs, n_pd)
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:699-711 applyDeclD
/// A declaration record.  **`sorryAx` is the FOLD's** (con-leche task #292):
/// the parse forwards every declaration record, the `sorryAx` axiom record
/// included — the fold checks its type, installs nothing for it, and declines
/// at the first record that USES the name.  What used to stand here was a
/// read-only taint pre-scan (`declRecordScanD`) that dropped the axiom record
/// without even parsing its type and skipped every declaration reaching it,
/// transitively, with the driver turning a non-empty skip list into a decline
/// at the END of the run.  The verdict was the same; the position was not, and
/// the parser owned a semantic decision.
pub fn apply_decl_d(st: &mut StateD, d: &DeclRec) -> Result<(), LineErr> {
    process_line_core_d(st, d)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:713-726 applyLine
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

/// con-leche: ConLeche/Frontend/ExportC.lean:730-753 ParseResultD
/// The direct parse result: the declarations over `Expr`, and the parse's
/// receipts.  No arena, and — since con-leche task #293 — no prelude, no
/// dedupe count and no hoist receipt: those are `prepare::Prepared`'s.
pub struct ParseResultD {
    /// the FILE's declaration records, in the file's order, plus the records
    /// the in-process modeller generated
    pub decls: Vec<Declaration>,
    /// projection functions rewritten to recursor form
    pub proj_rewrites: Vec<Name>,
    /// the blocks modelled in-process, in stream order
    pub in_modelled: Vec<Name>,
    /// how many of `decls` the in-process modeller generated, and which block
    /// each of them models: the driver subtracts the count from its headline
    /// number — a generated record is a declaration of the fold, never a
    /// record of the file — and names the block when one of them fails
    pub gen_records: u64,
    pub gen_owner: HashMap<NameKey, Name>,
    /// the census's declines (block, reason)
    pub in_model_declined: Vec<(Name, String)>,
}

/// con-leche: ConLeche/Frontend/ExportC.lean:760-763 ParseResultD.ofState
/// The result: the file's records, in the file's order.
pub fn parse_result_of_state(st: StateD) -> ParseResultD {
    let StateD {
        decls,
        proj_rewrites,
        in_modelled,
        gen_records,
        gen_owner,
        in_model_declined,
        ..
    } = st;
    ParseResultD {
        decls,
        proj_rewrites,
        in_modelled,
        gen_records,
        gen_owner,
        in_model_declined,
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:765-775 applyFinalLine
/// Scan and apply the LAST line of a stream — the one no newline ends.  A
/// syntactic failure is reported at its offset in the line.
pub fn apply_final_line(
    st: &mut StateD,
    b: &[u8],
    i: usize,
    line_no: u64,
) -> Result<(), (CheckError, u64)> {
    match scan_fast::scan_line_fwd(b, i) {
        Err(e) => Err((
            core_types::internal(cps(&scan_err_render(
                &crate::frontend::scan_types::ScanErr {
                    offset: e.offset - i,
                    what: e.what,
                },
            ))),
            line_no,
        )),
        Ok((r, _)) => apply_line(st, &r).map_err(|e| line_err_to_check(e, line_no)),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:777-811 feedChunk
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
) -> Result<(u64, usize), (CheckError, u64)> {
    let mut i = i;
    let mut line_no = line_no;
    while i < b.len() {
        match scan_fast::scan_line_fwd(b, i) {
            Err(e) => {
                return if scan_fast::newline_from(b, i) {
                    Err((
                        core_types::internal(cps(&scan_err_render(
                            &crate::frontend::scan_types::ScanErr {
                                offset: e.offset - i,
                                what: e.what,
                            },
                        ))),
                        line_no + 1,
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
                apply_line(st, &r).map_err(|e| line_err_to_check(e, line_no + 1))?;
                if i >= j {
                    return Err((
                        core_types::internal(cps("the line scanner made no progress")),
                        line_no + 1,
                    ));
                }
                i = j;
                line_no += 1;
            }
        }
    }
    Ok((line_no, i))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:813-814 chunkSize
/// How many bytes the streaming driver asks for at a time.
pub const CHUNK_SIZE: usize = 4 * 1024 * 1024;

/// con-leche: none — `USize.size`, the number of machine words.  Rust spells
/// it `usize::BITS`, and the comparison is in `u128` because `1 << 64` does
/// not fit the type it bounds.
pub const USIZE_SIZE: u128 = 1u128 << usize::BITS;

/// con-leche: ConLeche/Frontend/ExportC.lean:816-825 sizeError
/// **The size guard** (con-leche task #290).  The byte reader addresses its
/// buffer by machine word, so an input of `USize.size` bytes or more is
/// refused before any of it is read — the wholesale parse at its length, the
/// streaming parse when the bytes read so far would reach it.  No real input
/// comes near, and the guard is what lets con-leche's file theorem stand
/// without a size hypothesis: an accepted parse is a parse of a buffer the
/// word addresses.
///
/// The error carries line 0: there is no line to name, the input is refused
/// before one is read.
pub fn size_error() -> (CheckError, u64) {
    (
        core_types::not_implemented(cps(&format!("an input of {} bytes or more", USIZE_SIZE))),
        0,
    )
}

/// con-leche: ConLeche/Frontend/ExportC.lean:827-839 parseBytes
/// **Wholesale direct parse of a byte buffer**: the whole input fed at once,
/// then the last line.  The specification the streaming parse is proved equal
/// to.
///
/// A `&[u8]`'s length is a `usize` by construction, so on this target the
/// guard cannot fire; it is kept because it is the shape con-leche's theorem
/// reads, and because `chunk_step`'s running total — which is not a slice
/// length — can reach it on a narrow word.
pub fn parse_bytes(
    b: &[u8],
    in_model: bool,
    census: bool,
) -> Result<ParseResultD, (CheckError, u64)> {
    if (b.len() as u128) >= USIZE_SIZE {
        return Err(size_error());
    }
    let mut st = state_d_init(in_model, census);
    let (line_no, tail) = feed_chunk(&mut st, b, 0, 0)?;
    if tail < b.len() {
        apply_final_line(&mut st, b, tail, line_no + 1)?;
    }
    Ok(parse_result_of_state(st))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:841-846 parseExportD
/// Wholesale direct parse of a string (the built-in prelude, tests and small
/// inputs): `parse_bytes` of its UTF-8.
pub fn parse_export_d(
    contents: &str,
    in_model: bool,
    census: bool,
) -> Result<ParseResultD, (CheckError, u64)> {
    parse_bytes(contents.as_bytes(), in_model, census)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:848-865 chunkStep
/// **One chunk of the stream, applied** (con-leche task #290): the carried
/// incomplete tail is put in front of the new bytes, every complete line of
/// the buffer is fed, and the new incomplete tail is cut off for the next
/// chunk; `total` counts the bytes read before this chunk, for the size guard.
/// This is the step the streaming reader takes, pure, so that `parse_chunks` —
/// the same step folded over a list of chunks — is exactly what the binary
/// computes and can be compared with the wholesale parse.
pub fn chunk_step(
    st: &mut StateD,
    carry: Vec<u8>,
    line_no: u64,
    total: u64,
    buf0: &[u8],
) -> Result<(Vec<u8>, u64, u64), (CheckError, u64)> {
    if (total as u128) + (buf0.len() as u128) >= USIZE_SIZE {
        return Err(size_error());
    }
    let buf: Vec<u8> = if carry.is_empty() {
        buf0.to_vec()
    } else {
        let mut v = carry;
        v.extend_from_slice(buf0);
        v
    };
    let (line_no, tail) = feed_chunk(st, &buf, 0, line_no)?;
    Ok((buf[tail..].to_vec(), line_no, total + buf0.len() as u64))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:867-874 chunkFinish
/// The end of the stream: the carried tail, if any, is its last line.
pub fn chunk_finish(
    mut st: StateD,
    carry: &[u8],
    line_no: u64,
) -> Result<ParseResultD, (CheckError, u64)> {
    if carry.is_empty() {
        return Ok(parse_result_of_state(st));
    }
    apply_final_line(&mut st, carry, 0, line_no + 1)?;
    Ok(parse_result_of_state(st))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:876-880 concatBytes
/// The bytes of a list of chunks, in order: what the chunks a handle hands out
/// add up to.
pub fn concat_bytes(chunks: &[Vec<u8>]) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    for c in chunks {
        out.extend_from_slice(c);
    }
    out
}

/// con-leche: ConLeche/Frontend/ExportC.lean:882-901 parseChunks
/// **The streaming parse, purely** (con-leche task #290): `chunk_step` folded
/// over a list of chunks, `chunk_finish` at its end — what
/// `parse_export_handle_d` does with the chunks its handle hands out, minus
/// the reads.  The list is folded whole (task #294): an empty chunk
/// contributes nothing and the fold goes on, so the parse of a list of chunks
/// is the parse of their concatenation, however it was cut.  The loop's
/// end-of-input decision — an empty READ is the end of the file — is the
/// loop's own, not the step's.
pub fn parse_chunks(
    chunks: &[Vec<u8>],
    in_model: bool,
    census: bool,
) -> Result<ParseResultD, (CheckError, u64)> {
    let mut st = state_d_init(in_model, census);
    let mut carry: Vec<u8> = Vec::new();
    let mut line_no: u64 = 0;
    let mut total: u64 = 0;
    for c in chunks {
        let (c2, l, t) = chunk_step(&mut st, carry, line_no, total, c)?;
        carry = c2;
        line_no = l;
        total = t;
    }
    chunk_finish(st, &carry, line_no)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:903-931 parseExportHandleD
/// Streaming direct parse off an open reader.
///
/// The reader is read strictly forward, 4 MiB at a time, and is never seeked,
/// re-opened or asked for its size — so the source may be a *pipe* just as
/// well as a file (con-leche task #180: no scratch file at all, anywhere).
/// It is a property to preserve: a seek or a re-open here would silently
/// re-introduce a temp file.  The unconsumed tail of a chunk — at most one
/// incomplete line — is carried into the next one.  Each step is `chunk_step`,
/// the end `chunk_finish`: the loop is `parse_chunks`' with the reads
/// interleaved, stopping at the first empty read.
pub fn parse_export_handle_d<R: Read>(
    h: &mut R,
    in_model: bool,
    census: bool,
    chunk: usize,
) -> std::io::Result<Result<ParseResultD, (CheckError, u64)>> {
    let mut st = state_d_init(in_model, census);
    let mut carry: Vec<u8> = Vec::new();
    let mut line_no: u64 = 0;
    let mut total: u64 = 0;
    let mut buf0: Vec<u8> = vec![0u8; chunk];
    loop {
        let n = read_up_to(h, &mut buf0)?;
        if n == 0 {
            return Ok(chunk_finish(st, &carry, line_no));
        }
        match chunk_step(&mut st, carry, line_no, total, &buf0[..n]) {
            Err(e) => return Ok(Err(e)),
            Ok((c, l, t)) => {
                carry = c;
                line_no = l;
                total = t;
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

/// con-leche: ConLeche/Frontend/ExportC.lean:933-938 parseExportStreamD
/// Streaming direct parse of a file.
pub fn parse_export_stream_d(
    path: &str,
    in_model: bool,
    census: bool,
    chunk: usize,
) -> std::io::Result<Result<ParseResultD, (CheckError, u64)>> {
    let mut f = std::fs::File::open(path)?;
    parse_export_handle_d(&mut f, in_model, census, chunk)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(text: &str) -> Result<ParseResultD, (CheckError, u64)> {
        parse_export_d(text, true, false)
    }

    /// The message of a `CheckError`, as a Rust string: `CheckError` carries
    /// code points and derives no `Debug`, so the tests render it themselves.
    fn msg(e: &CheckError) -> String {
        let m = match e {
            CheckError::NotImplemented(m)
            | CheckError::Invalid(m)
            | CheckError::Internal(m)
            | CheckError::Native(m) => m,
        };
        m.iter().filter_map(|c| char::from_u32(*c)).collect()
    }

    /// A failed parse, rendered for a panic message: the class, the line and
    /// the message.
    fn show(e: &(CheckError, u64)) -> String {
        let tag = match e.0 {
            CheckError::NotImplemented(_) => "declined",
            CheckError::Invalid(_) => "invalid",
            CheckError::Internal(_) => "internal",
            CheckError::Native(_) => "native",
        };
        format!("{} at line {}: {}", tag, e.1, msg(&e.0))
    }

    /// A result that was expected to fail, rendered for a panic message.
    fn shown(r: Result<ParseResultD, (CheckError, u64)>) -> String {
        match r {
            Ok(_) => "an accepted parse".to_string(),
            Err(e) => show(&e),
        }
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
        let r = parse(s).unwrap_or_else(|e| panic!("{}", show(&e)));
        assert_eq!(r.decls.len(), 1);
        match &r.decls[0] {
            Declaration::AxiomDecl(cv) => assert_eq!(name_str(&cv.name), "A"),
            _ => panic!("not an axiom"),
        }
    }

    /// An undefined index is a parse error naming the line, not a panic.
    #[test]
    fn an_undefined_index_is_a_parse_error() {
        let s = "{\"ie\":0,\"sort\":7}\n";
        match parse(s) {
            Err((CheckError::Internal(msg), line)) => {
                assert_eq!(line, 1);
                let m: String = msg.iter().filter_map(|c| char::from_u32(*c)).collect();
                assert!(m.contains("undefined level index 7"), "{}", m);
            }
            other => panic!("{}", shown(other)),
        }
    }

    /// **An index is bound once** (con-leche task #290): a second entry at an
    /// index a previous line bound is a parse error naming the table.
    #[test]
    fn rebinding_a_table_index_is_a_parse_error() {
        for (s, what) in [
            (
                concat!(
                    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n",
                    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"B\"}}\n"
                ),
                "name index 1 is already bound",
            ),
            (
                concat!("{\"il\":1,\"succ\":0}\n", "{\"il\":1,\"succ\":0}\n"),
                "level index 1 is already bound",
            ),
            (
                concat!("{\"ie\":0,\"sort\":0}\n", "{\"ie\":0,\"sort\":0}\n"),
                "expression index 0 is already bound",
            ),
        ] {
            match parse(s) {
                Err((CheckError::Internal(msg), 2)) => {
                    let m: String = msg.iter().filter_map(|c| char::from_u32(*c)).collect();
                    assert_eq!(m, what);
                }
                other => panic!("{}: {}", what, shown(other)),
            }
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
            Err((CheckError::NotImplemented(w), _)) => {
                let m: String = w.iter().filter_map(|c| char::from_u32(*c)).collect();
                assert_eq!(m, "unsafe axiom");
            }
            other => panic!("{}", shown(other)),
        }
    }

    /// **One record per `#QUOT` line** (con-leche task #293): the decoder
    /// emits the constant the file declares, at the kind it declares it at,
    /// and matches nothing against a pin.
    #[test]
    fn a_quot_record_is_one_quot_decl() {
        let s = concat!(
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Whatever\"}}\n",
            "{\"ie\":0,\"sort\":0}\n",
            "{\"quot\":{\"kind\":\"lift\",\"levelParams\":[],\"name\":1,\"type\":0}}\n"
        );
        let r = parse(s).unwrap_or_else(|e| panic!("{}", show(&e)));
        assert_eq!(r.decls.len(), 1);
        match &r.decls[0] {
            Declaration::QuotDecl(k, cv) => {
                assert_eq!(env::quot_kind_slot(k), 2);
                assert_eq!(name_str(&cv.name), "Whatever");
            }
            _ => panic!("not a quotient record"),
        }
    }

    /// An unknown quotient kind is a parse error.
    #[test]
    fn an_unknown_quotient_kind_is_a_parse_error() {
        let s = concat!(
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Q\"}}\n",
            "{\"ie\":0,\"sort\":0}\n",
            "{\"quot\":{\"kind\":\"nope\",\"levelParams\":[],\"name\":1,\"type\":0}}\n"
        );
        match parse(s) {
            Err((CheckError::Internal(msg), 3)) => {
                let m: String = msg.iter().filter_map(|c| char::from_u32(*c)).collect();
                assert_eq!(m, "unknown quotient kind 'nope'");
            }
            other => panic!("{}", shown(other)),
        }
    }

    /// A mutual block reaches the modeller and the modeller declines it,
    /// naming the block AND the class: this one has no recursors, so the
    /// generator's own shape check is what refuses it.
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
            Err((CheckError::NotImplemented(w), _)) => {
                let m: String = w.iter().filter_map(|c| char::from_u32(*c)).collect();
                assert!(m.starts_with("in-process model of T:"), "{}", m);
                assert!(
                    m.contains("recursor count differs from member count"),
                    "{}",
                    m
                );
            }
            other => panic!("{}", shown(other)),
        }
        // with the modeller off the block is pushed bare, as in con-leche
        let r = parse_export_d(s, false, false).unwrap_or_else(|e| panic!("{}", show(&e)));
        assert_eq!(r.decls.len(), 1);
        // and in census mode it is reported and the parse continues
        let r = parse_export_d(s, true, true).unwrap_or_else(|e| panic!("{}", show(&e)));
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
            Err((CheckError::Invalid(w), _)) => {
                let m: String = w.iter().filter_map(|c| char::from_u32(*c)).collect();
                assert!(m.contains("declares 3 fields"), "{}", m);
            }
            other => panic!("{}", shown(other)),
        }
    }

    /// The chunk boundary: the same stream parsed in small chunks gives the
    /// same records, because an incomplete line is carried and not
    /// misreported.  Both the reader loop and the pure `parse_chunks` are
    /// checked, and an empty chunk anywhere contributes nothing (con-leche
    /// task #294).
    #[test]
    fn chunking_does_not_change_the_parse() {
        let s = concat!(
            "{\"meta\":{\"exporter\":{\"name\":\"lean4export\"}}}\n",
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n",
            "{\"ie\":0,\"sort\":0}\n",
            "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}\n"
        );
        let whole = parse(s).unwrap_or_else(|e| panic!("{}", show(&e)));
        for chunk in [1usize, 2, 7, 8, 13, 64] {
            let mut cur = std::io::Cursor::new(s.as_bytes().to_vec());
            let r = parse_export_handle_d(&mut cur, true, false, chunk)
                .expect("io")
                .unwrap_or_else(|e| panic!("chunk {}: {}", chunk, show(&e)));
            assert_eq!(r.decls.len(), whole.decls.len(), "chunk {}", chunk);
            let cs: Vec<Vec<u8>> = s
                .as_bytes()
                .chunks(chunk)
                .map(|c| c.to_vec())
                .collect::<Vec<_>>();
            let r = parse_chunks(&cs, true, false)
                .unwrap_or_else(|e| panic!("pure chunk {}: {}", chunk, show(&e)));
            assert_eq!(r.decls.len(), whole.decls.len(), "pure chunk {}", chunk);
            assert_eq!(concat_bytes(&cs), s.as_bytes());
        }
        // an empty chunk anywhere is a no-op
        let b = s.as_bytes();
        let cs: Vec<Vec<u8>> = vec![
            b[..70].to_vec(),
            Vec::new(),
            b[70..71].to_vec(),
            b[71..].to_vec(),
            Vec::new(),
        ];
        let r = parse_chunks(&cs, true, false).unwrap_or_else(|e| panic!("{}", show(&e)));
        assert_eq!(r.decls.len(), whole.decls.len());
    }

    /// A final line with no newline is applied (`applyFinalLine`).
    #[test]
    fn a_final_line_without_a_newline_is_applied() {
        let s = concat!(
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n",
            "{\"ie\":0,\"sort\":0}\n",
            "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}"
        );
        let r = parse(s).unwrap_or_else(|e| panic!("{}", show(&e)));
        assert_eq!(r.decls.len(), 1);
    }
}

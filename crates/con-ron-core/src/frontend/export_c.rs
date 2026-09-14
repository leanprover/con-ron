//! `ConLeche/Frontend/ExportC.lean` — the **semantic layer** of the parse:
//! `apply_line` resolves a scanned record's stream indices against the parse
//! tables and builds the `Name`/`Level`/`Expr` nodes through the kernel's
//! smart constructors.
//!
//! The export's `ie`-indices *are* the sharing: the format already
//! externalises exactly the DAG structure an arena would reconstruct, so the
//! parse keeps a stream-index-keyed table of `Expr` **values** and a table hit
//! is a shared node by reference (a `ron::ptr::P` bump).  Nothing rebuilds a
//! term.
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
//! * **the in-process modeller**: a mutual or nested block's `_model` family
//!   is generated here and pushed ahead of the block.
//!
//! ## The in-process modeller, and why it is a type parameter
//!
//! `install_ind_d` calls it at the point `in_model_rec::wants` says yes: it
//! builds the `BlockRec` (`block_rec_of`), calls `Modeller::generate`, pushes
//! the records it returns through `push_gen_list` — which books each of them
//! with `note_gen_names` — and only then pushes the block.  A generator
//! decline is the run's decline, naming the class.
//!
//! The generator ITSELF is not in the core (task #84): it lives in
//! `crates/con-ron/src/in_model/`, and the parse reaches it through the
//! one-method trait `in_model_rec::Modeller` on a type parameter, which
//! extracts as a typeclass field — an opaque function.  Its own module note
//! is the licence: "soundness needs nothing from this module", because every
//! record it generates is checked by the fold as a stream declaration.  Every
//! function below that can reach `install_ind_d` therefore carries `<M:
//! Modeller>` and a leading `m: &M`, up to `parse_bytes`/`parse_chunks`.
//!
//! Three `StateD` fields exist for it and for nothing else — `const_types`
//! and `heights` (the sort inferer's and the generated definitions' hint
//! source, filled by `note_decl` at every push) and `ind_blocks` (the nested
//! rung's container shapes, filled at every inductive record).  They hold
//! every declaration's type in a hash map for the whole run, which is the
//! parse's one memory cost that scales with the stream rather than with the
//! DAG; con-leche pays it for the same reason.  `inModelGen`, the fourth, is
//! **not** ported: it feeds `CON_LECHE_INMODEL_DUMP` alone, whose writer
//! (`Frontend/ExportWrite.lean`) con-ron does not have.
//!
//! `CON_LECHE_INMODEL=0` means what it means in con-leche: the block is
//! pushed bare and the *fold* declines it at the install, having found no
//! route.  `CON_LECHE_INMODEL_CENSUS=1` records a generator decline and
//! pushes the block bare instead of declining the parse, so one parse lists
//! every block's outcome.  Both flags are `StateD` fields (`inModel`,
//! `inModelCensus`), as they are in con-leche; the environment is the
//! driver's business.
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
//! * **every message is a `Vec<u32>` of code points** (DESIGN.md §3.3) built
//!   from a function-local `const M: [u32; N]` and `core_types::code_points`,
//!   with `text::cat`/`cat3`, `text::name_str` and `text::u64_str` for what
//!   con-leche's `s!"…"` interpolates.  One interpolation is dropped and said
//!   so at its function: `size_error`'s byte count, which does not fit a
//!   `u64`.  The differential compares exit codes, so a shortened message
//!   costs nothing.
//! * `NameKey` does not exist here: `crate::ron::hashmap::HashMap` takes its
//!   key dictionary from `Hashable`/`Eq2`, which `kernel::name::Name` has, so
//!   the tables are keyed by `Name` directly.  A `HashSet` is a
//!   `HashMap<_, bool>`.
//! * **the subset's helpers.**  §3.4 has no closures, no iterator adapters
//!   and no `?`, and Aeneas duplicates the code AFTER a loop into every loop
//!   exit, so a long function with loops in the middle of it is split: each
//!   loop is its own function whose tail is one line, and the caller is a
//!   chain of `match`es.  `validate_ind_d` and `install_ind_d` are the two
//!   that needed it; every piece cites the whole of the function it came out
//!   of.
//! * `IdTable.bound` has no counterpart in `scan_types` (it arrived with
//!   con-leche task #290 and its only consumers are the three tests below), so
//!   the three read the table through `id_table_get(…).is_some()` —
//!   `IdTable.bound_eq`, which con-leche proves beside the definition.
//!   con-leche writes the test against a BORROWED state because an owned one
//!   made its compiler project and `inc` every field before the test; `&StateD`
//!   is that, by construction.
//! * `feed_chunk` reads `&[u8]` slices of a `Vec<u8>` buffer rather than a
//!   `ByteArray`; the chunk size, the carried tail and the "position 0 means
//!   an incomplete tail" contract are con-leche's.
//! * **the reader is not here.**  `parseExportHandleD` and
//!   `parseExportStreamD` are `std::io` — the streaming *reader*, not the
//!   parse — and stay in the driver, which calls `chunk_step`/`chunk_finish`
//!   in the loop `parse_chunks` spells out purely.

use crate::frontend::export::{record_verdict_to_error, RecordVerdict};
use crate::frontend::in_model_rec;
use crate::frontend::nat_decimal;
use crate::frontend::in_model_rec::{BlockRec, ModelCtx, Modeller};
use crate::frontend::proj_rec;
use crate::frontend::scan_fast;
use crate::frontend::scan_types;
use crate::frontend::scan_types::{
    id_table_get, id_table_insert, id_table_singleton, scan_err_render, CVRec, DeclRec, ExprRec,
    HintsRec, IdTable, IndCtorRec, IndRecRec, IndTypeRec, LevelRec, LineRec, NameRec, PwRec,
    RuleRec, ScanErr,
};
use crate::frontend::text;
use crate::kernel::basis_raw;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::kernel::env;
use crate::kernel::env::{
    ConstantInfo, ConstantVal, Declaration, QuotKind, RecRule, ReducibilityHint,
};
use crate::kernel::expr;
use crate::kernel::expr::{Expr, ExprKind};
use crate::kernel::expr_ops;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::{Name, NameKind};
use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;
use crate::ron::hashmap::HashMap;
use crate::ron::ptr;
use crate::ron::ptr::P;

/// con-leche: ConLeche/Frontend/Export.lean:117 M
/// con-leche: ConLeche/Frontend/Export.lean:71-79 RecordVerdict
/// The two ways applying one line can fail: a parse message (con-leche's
/// `M = Except String`) or a record verdict (its `StateD ⊕ RecordVerdict`'s
/// right summand).  Merging them into one `Result` is this module's first
/// deviation; the two arms are told apart again at `line_err_to_check`, where
/// the line number is in hand.
pub enum LineErr {
    Msg(Vec<u32>),
    Verdict(RecordVerdict),
}

/// con-leche: none — `throw` in con-leche's `M`, i.e. `Except.error`.
pub fn merr<T>(msg: Vec<u32>) -> Result<T, LineErr> {
    Err(LineErr::Msg(msg))
}

/// con-leche: none — `.inr (.declined …)`, the decline half of
/// `StateD ⊕ RecordVerdict`.
pub fn declined<T>(what: Vec<u32>) -> Result<T, LineErr> {
    Err(LineErr::Verdict(RecordVerdict::Declined(what)))
}

/// con-leche: none — `.inr (.invalid …)`, the reject half of
/// `StateD ⊕ RecordVerdict`.
pub fn invalid<T>(what: Vec<u32>) -> Result<T, LineErr> {
    Err(LineErr::Verdict(RecordVerdict::Invalid(what)))
}

/// con-leche: none — the `M`/verdict pair resolved against the line it was
/// read at: the `applyFinalLine`/`feedChunk` arms that turn `M`'s message into
/// `(.internal msg, line)` and a record verdict into `(v.toError, line)`.
pub fn line_err_to_check(e: LineErr, line_no: u64) -> (CheckError, u64) {
    match e {
        LineErr::Msg(m) => (core_types::internal(m), line_no),
        LineErr::Verdict(v) => (record_verdict_to_error(v), line_no),
    }
}

/// con-leche: none — Lean's `s!"{b}"` on a `Bool`; one recursor message
/// prints the flag the record declares.
pub fn bool_str(b: bool) -> Vec<u32> {
    if b {
        const T: [u32; 4] = [116, 114, 117, 101];
        core_types::code_points(&T)
    } else {
        const F: [u32; 5] = [102, 97, 108, 115, 101];
        core_types::code_points(&F)
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
    pub proj_owners: HashMap<Name, proj_rec::ProjRecOwner>,
    /// field sorts, by artifact iota name `T._model.proj_i.iota` (the
    /// in-process modeller's own, and only those)
    pub proj_levels: HashMap<Name, Level>,
    /// projection functions rewritten so far (names, for the driver's trace)
    pub proj_rewrites: Vec<Name>,
    /// the declared types of every declaration pushed so far, by name: the
    /// in-process modeller's sort inferer reads them
    pub const_types: HashMap<Name, (Vec<Name>, Expr)>,
    /// the definitional heights of the definitions pushed so far (the hints
    /// of the generated definitions are computed from them)
    pub heights: HashMap<Name, u64>,
    /// in-process modelling of mutual/nested blocks is on
    pub in_model: bool,
    /// the blocks modelled in-process, in stream order
    pub in_modelled: Vec<Name>,
    /// how many records the in-process modeller GENERATED and pushed: they are
    /// declarations of the fold like any other, but they are not records of
    /// the FILE, so the driver's headline count subtracts them
    pub gen_records: u64,
    /// each generated record's leading name ↦ the block it models
    pub gen_owner: HashMap<Name, Name>,
    /// the number of `inductive` records seen so far
    pub ind_count: u64,
    /// the parsed inductive blocks, by member type name (the in-process
    /// modeller's nested rung reads a container's shape off it)
    pub ind_blocks: HashMap<Name, P<BlockRec>>,
    /// CENSUS mode (`CON_LECHE_INMODEL_CENSUS=1`): a generator decline is
    /// recorded and the block pushed bare instead of declining the parse
    pub in_model_census: bool,
    /// the census's declines: block name and reason
    pub in_model_declined: Vec<(Name, Vec<u32>)>,
}

/// con-leche: ConLeche/Frontend/ExportC.lean:755-758 StateD.init
/// The initial parse state.  There is no prelude here any more (con-leche task
/// #293): the parse starts from the file's first record, and putting the
/// prelude's declarations in front is `prepare::prepare_prelude`'s.
pub fn state_d_init(in_model: bool, census: bool) -> StateD {
    StateD {
        names: id_table_singleton(name::anonymous()),
        levels: id_table_singleton(level::zero()),
        exprs: scan_types::id_table_empty(),
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

/// con-leche: ConLeche/Frontend/ExportC.lean:603-607 _
/// **The modeller's window on the state, one.**  The cited
/// `fun n => st.constTypes[n]?`: a pushed constant's level parameters and
/// declared type.  It is an accessor rather than a field read because the
/// modeller is outside the core and `StateD` is not part of its interface —
/// these three and `state_model_ctx` are.
pub fn state_const_type<'a>(st: &'a StateD, n: &Name) -> Option<&'a (Vec<Name>, Expr)> {
    st.const_types.get(n)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:603-607 _
/// **Two.**  The cited `fun n => st.heights.getD n 0`.
pub fn state_height(st: &StateD, n: &Name) -> u64 {
    match st.heights.get(n) {
        None => 0,
        Some(h) => *h,
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:603-607 _
/// **Three.**  The cited `fun n => st.indBlocks[n]?`.
pub fn state_ind_block<'a>(st: &'a StateD, n: &Name) -> Option<&'a BlockRec> {
    match st.ind_blocks.get(n) {
        None => None,
        Some(p) => Some(&**p),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:603-607 _
/// The cited `let ctx : InModel.Ctx := ⟨…, …, …⟩`: the three tables the
/// modeller reads, borrowed off the state.
pub fn state_model_ctx<'a>(st: &'a StateD) -> ModelCtx<'a> {
    ModelCtx {
        tbl: &st.const_types,
        heights: &st.heights,
        blocks: &st.ind_blocks,
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:135-153 noteDecl
/// con-leche: ConLeche/Kernel/Basis.lean:40-47 BasisKind.decls
/// The constants one pushed declaration declares, with their level
/// parameters, declared types and (for a definition) definitional height:
/// the cited `cvs`.
pub fn note_decl_entries(d: &Declaration) -> Vec<(Name, Vec<Name>, Expr, Option<u64>)> {
    match d {
        Declaration::AxiomDecl(cv) => note_one(cv, None),
        Declaration::DefnDecl(cv, _, h) => note_one(cv, Some(in_model_rec::hint_height(h))),
        Declaration::ThmDecl(cv, _) => note_one(cv, None),
        Declaration::OpaqueDecl(cv, _) => note_one(cv, None),
        Declaration::BasisDecl(k) => note_block(&basis_raw::basis_kind_decls(k), 0, Vec::new()),
        Declaration::QuotDecl(_, cv) => note_one(cv, None),
        Declaration::IndDecl(bl, _) => note_block(bl, 0, Vec::new()),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:135-153 noteDecl
/// `note_decl_entries`' one-constant case (con-leche's `[(cv, h)]`), which
/// §3.4 spells as a function rather than the `let one := fun …` the
/// unverified port wrote.
pub fn note_one(cv: &ConstantVal, h: Option<u64>) -> Vec<(Name, Vec<Name>, Expr, Option<u64>)> {
    let mut out: Vec<(Name, Vec<Name>, Expr, Option<u64>)> = Vec::new();
    out.push((
        name::dup(&cv.name),
        prop_when::names_copy(&cv.level_params),
        expr::dup(&cv.ty),
        h,
    ));
    out
}

/// con-leche: ConLeche/Frontend/ExportC.lean:135-153 noteDecl
/// `note_decl_entries`' block case (con-leche's `block.map`), as an index
/// loop with the accumulator passed by value.
pub fn note_block(
    bl: &Vec<ConstantInfo>,
    i: usize,
    out: Vec<(Name, Vec<Name>, Expr, Option<u64>)>,
) -> Vec<(Name, Vec<Name>, Expr, Option<u64>)> {
    let mut out = out;
    let n = bl.len();
    let mut k = i;
    while k < n {
        let cv = env::to_constant_val(&bl[k]);
        out.push((
            name::dup(&cv.name),
            prop_when::names_copy(&cv.level_params),
            expr::dup(&cv.ty),
            None,
        ));
        k += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/ExportC.lean:135-153 noteDecl
/// The insert half of `noteDecl`: the cited `cvs.foldl` over `constTypes`
/// and `heights`.
///
/// The list is BORROWED and each entry copied in (a `Name`/`Expr` copy is a
/// pointer bump, a `Vec<Name>` copy one spine): Aeneas' `Vec` model has no
/// `pop`, `remove` or `swap_remove`, so there is no way to move an element
/// out of an owned `Vec` inside the subset.  Its unverified twin took the
/// list by value.
pub fn note_entries(st: &mut StateD, es: &Vec<(Name, Vec<Name>, Expr, Option<u64>)>) {
    let n = es.len();
    let mut i = 0usize;
    while i < n {
        let e = &es[i];
        match e.3 {
            None => {}
            Some(hv) => {
                st.heights.insert(name::dup(&e.0), hv);
            }
        }
        st.const_types.insert(
            name::dup(&e.0),
            (prop_when::names_copy(&e.1), expr::dup(&e.2)),
        );
        i += 1;
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:135-153 noteDecl
/// Record a pushed declaration's constants in the declaration table
/// (`const_types`, `heights`).
pub fn note_decl(st: &mut StateD, d: &Declaration) {
    let es = note_decl_entries(d);
    note_entries(st, &es);
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
        None => {
            const M: [u32; 21] = [
                117, 110, 100, 101, 102, 105, 110, 101, 100, 32, 110, 97, 109, 101, 32, 105,
                110, 100, 101, 120, 32
            ];
            merr(text::cat(core_types::code_points(&M), &text::u64_str(i)))
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:169-172 StateD.level
pub fn st_level(st: &StateD, i: u64) -> Result<Level, LineErr> {
    match id_table_get(&st.levels, i) {
        Some(l) => Ok(level::dup(l)),
        None => {
            const M: [u32; 22] = [
                117, 110, 100, 101, 102, 105, 110, 101, 100, 32, 108, 101, 118, 101, 108,
                32, 105, 110, 100, 101, 120, 32
            ];
            merr(text::cat(core_types::code_points(&M), &text::u64_str(i)))
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:174-177 StateD.expr
pub fn st_expr(st: &StateD, i: u64) -> Result<Expr, LineErr> {
    match id_table_get(&st.exprs, i) {
        Some(e) => Ok(expr::dup(e)),
        None => {
            const M: [u32; 21] = [
                117, 110, 100, 101, 102, 105, 110, 101, 100, 32, 101, 120, 112, 114, 32,
                105, 110, 100, 101, 120, 32
            ];
            merr(text::cat(core_types::code_points(&M), &text::u64_str(i)))
        }
    }
}

/// con-leche: none — `is.mapM st.name`, which §3.4 forbids as an iterator
/// adapter: a name-index list resolved, as an index loop whose tail is one
/// line (the parse's level-parameter and constructor lists).
pub fn st_names(st: &StateD, is: &Vec<u64>) -> Result<Vec<Name>, LineErr> {
    let mut out: Vec<Name> = Vec::with_capacity(is.len());
    let n = is.len();
    let mut i = 0usize;
    while i < n {
        match st_name(st, is[i]) {
            Err(e) => return Err(e),
            Ok(v) => out.push(v),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: none — `us.mapM st.level` (see `st_names`).
pub fn st_levels(st: &StateD, is: &Vec<u64>) -> Result<Vec<Level>, LineErr> {
    let mut out: Vec<Level> = Vec::with_capacity(is.len());
    let n = is.len();
    let mut i = 0usize;
    while i < n {
        match st_level(st, is[i]) {
            Err(e) => return Err(e),
            Ok(v) => out.push(v),
        }
        i += 1;
    }
    Ok(out)
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
        PwRec::IfAllZero(ns) => match st_names(st, ns) {
            Err(e) => Err(e),
            Ok(out) => Ok(prop_when::if_all_zero(out)),
        },
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:207-209 reboundError
/// The rebinding error, named once.  `what` is one of three `const [u32; N]`
/// literals at the call sites, con-leche's `"name"`/`"level"`/`"expression"`.
pub fn rebound_error(what: &[u32], i: u64) -> Vec<u32> {
    const A: [u32; 7] = [32, 105, 110, 100, 101, 120, 32];
    const B: [u32; 17] = [
        32, 105, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 98, 111, 117, 110, 100
    ];
    let s = text::cat3(
        core_types::code_points(what),
        &core_types::code_points(&A),
        &text::u64_str(i),
    );
    text::cat(s, &core_types::code_points(&B))
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
    match id_table_get(&st.names, i) {
        Some(_) => {
            const W: [u32; 4] = [110, 97, 109, 101];
            merr(rebound_error(&W, i))
        }
        None => Ok(()),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:221-222 StateD.freshLevel
/// con-leche: ConLeche/Frontend/Scan/Types.lean:363-372 IdTable.bound
/// `st_fresh_name` on the level table.
pub fn st_fresh_level(st: &StateD, i: u64) -> Result<(), LineErr> {
    match id_table_get(&st.levels, i) {
        Some(_) => {
            const W: [u32; 5] = [108, 101, 118, 101, 108];
            merr(rebound_error(&W, i))
        }
        None => Ok(()),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:223-224 StateD.freshExpr
/// con-leche: ConLeche/Frontend/Scan/Types.lean:363-372 IdTable.bound
/// `st_fresh_name` on the expression table.
pub fn st_fresh_expr(st: &StateD, i: u64) -> Result<(), LineErr> {
    match id_table_get(&st.exprs, i) {
        Some(_) => {
            const W: [u32; 10] = [101, 120, 112, 114, 101, 115, 115, 105, 111, 110];
            merr(rebound_error(&W, i))
        }
        None => Ok(()),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:228-237 parseNameEntryD
/// A name-table entry: the name value is built directly.  The parent index is
/// resolved before the freshness test, as in the cited `do` block.
pub fn parse_name_entry_d(st: &mut StateD, i: u64, r: &NameRec) -> Result<(), LineErr> {
    let v = match r {
        NameRec::Str(pre, s) => match st_name(st, *pre) {
            Err(e) => return Err(e),
            Ok(p) => match st_fresh_name(st, i) {
                Err(e) => return Err(e),
                Ok(()) => name::mk_str(p, core_types::code_points(s)),
            },
        },
        NameRec::Num(pre, k) => match st_name(st, *pre) {
            Err(e) => return Err(e),
            Ok(p) => match st_fresh_name(st, i) {
                Err(e) => return Err(e),
                Ok(()) => name::mk_num(p, *k),
            },
        },
    };
    id_table_insert(&mut st.names, i, v);
    Ok(())
}

/// con-leche: ConLeche/Frontend/ExportC.lean:239-247 parseLevelEntryD
/// A level-table entry.
pub fn parse_level_entry_d(st: &mut StateD, i: u64, r: &LevelRec) -> Result<(), LineErr> {
    match st_fresh_level(st, i) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    let l = match parse_level_rec_d(st, r) {
        Err(e) => return Err(e),
        Ok(l) => l,
    };
    id_table_insert(&mut st.levels, i, l);
    Ok(())
}

/// con-leche: ConLeche/Frontend/ExportC.lean:239-247 parseLevelEntryD
/// The value half of `parse_level_entry_d`: the node built from the
/// children's table values.  Split out so the entry point is a `match`
/// chain with no `?` (§3.4).
pub fn parse_level_rec_d(st: &StateD, r: &LevelRec) -> Result<Level, LineErr> {
    match r {
        LevelRec::Succ(u) => match st_level(st, *u) {
            Err(e) => Err(e),
            Ok(a) => Ok(level::succ(a)),
        },
        LevelRec::Max(a, b) => match st_level(st, *a) {
            Err(e) => Err(e),
            Ok(x) => match st_level(st, *b) {
                Err(e) => Err(e),
                Ok(y) => Ok(level::max(x, y)),
            },
        },
        LevelRec::Imax(a, b) => match st_level(st, *a) {
            Err(e) => Err(e),
            Ok(x) => match st_level(st, *b) {
                Err(e) => Err(e),
                Ok(y) => Ok(level::imax(x, y)),
            },
        },
        LevelRec::Param(n) => match st_name(st, *n) {
            Err(e) => Err(e),
            Ok(p) => Ok(level::param(p)),
        },
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:249-279 parseExprEntryD
/// An expression-table entry: build the node from the children's table values
/// (the derived fields are the smart constructors').  Binder names are display
/// data the official kernel's equality and hash ignore; ours are `.anonymous`
/// on every parsed binder, so `==` is α-equivalence downstream.
pub fn parse_expr_entry_d(st: &mut StateD, i: u64, r: &ExprRec) -> Result<(), LineErr> {
    match st_fresh_expr(st, i) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    let e = match parse_expr_rec_d(st, r) {
        Err(e) => return Err(e),
        Ok(e) => e,
    };
    id_table_insert(&mut st.exprs, i, e);
    Ok(())
}

/// con-leche: ConLeche/Frontend/ExportC.lean:249-279 parseExprEntryD
/// The value half of `parse_expr_entry_d` (see `parse_level_rec_d`).
pub fn parse_expr_rec_d(st: &StateD, r: &ExprRec) -> Result<Expr, LineErr> {
    match r {
        ExprRec::Bvar(k) => Ok(expr::mk_bvar(*k)),
        ExprRec::Sort(u) => match st_level(st, *u) {
            Err(e) => Err(e),
            Ok(l) => Ok(expr::sort(l)),
        },
        ExprRec::Const(n, us) => match st_name(st, *n) {
            Err(e) => Err(e),
            Ok(nm) => match st_levels(st, us) {
                Err(e) => Err(e),
                Ok(ls) => Ok(expr::mk_const(nm, ls)),
            },
        },
        ExprRec::App(f, a) => match st_expr(st, *f) {
            Err(e) => Err(e),
            Ok(x) => match st_expr(st, *a) {
                Err(e) => Err(e),
                Ok(y) => Ok(expr::app(x, y)),
            },
        },
        ExprRec::Lam(ty, bd, pw) => match st_expr(st, *ty) {
            Err(e) => Err(e),
            Ok(t) => match st_expr(st, *bd) {
                Err(e) => Err(e),
                Ok(b) => match parse_pw_d(st, pw) {
                    Err(e) => Err(e),
                    Ok(p) => Ok(expr::lam(t, b, expr::binder_meta(p))),
                },
            },
        },
        ExprRec::ForallE(ty, bd, pw) => match st_expr(st, *ty) {
            Err(e) => Err(e),
            Ok(t) => match st_expr(st, *bd) {
                Err(e) => Err(e),
                Ok(b) => match parse_pw_d(st, pw) {
                    Err(e) => Err(e),
                    Ok(p) => Ok(expr::forall_e(t, b, expr::binder_meta(p))),
                },
            },
        },
        ExprRec::LetE(ty, vl, bd) => match st_expr(st, *ty) {
            Err(e) => Err(e),
            Ok(t) => match st_expr(st, *vl) {
                Err(e) => Err(e),
                Ok(v) => match st_expr(st, *bd) {
                    Err(e) => Err(e),
                    Ok(b) => Ok(expr::let_e(t, v, b)),
                },
            },
        },
        ExprRec::Proj(tn, ix, s) => match st_name(st, *tn) {
            Err(e) => Err(e),
            Ok(t) => match st_expr(st, *s) {
                Err(e) => Err(e),
                Ok(x) => Ok(expr::proj(t, *ix, x)),
            },
        },
        ExprRec::NatVal(digits) => match nat_decimal::from_decimal(digits) {
            None => merr(scan_types::err_tag_describe(&scan_types::ErrTag::BadNatVal)),
            Some(n) => Ok(expr::lit(expr::literal_nat(n))),
        },
        ExprRec::StrVal(s) => Ok(expr::lit(expr::literal_str(core_types::code_points(s)))),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:283-289 parseCVD
/// A declaration's common data.
pub fn parse_cv_d(st: &StateD, cv: &CVRec) -> Result<ConstantVal, LineErr> {
    match st_name(st, cv.name) {
        Err(e) => Err(e),
        Ok(nm) => match get_decl_d(st, cv.ty) {
            Err(e) => Err(e),
            Ok(ty) => match st_names(st, &cv.level_params) {
                Err(e) => Err(e),
                Ok(lps) => Ok(ConstantVal {
                    name: nm,
                    level_params: lps,
                    ty,
                }),
            },
        },
    }
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
/// **Always `None` until the modeller runs**: `proj_levels` is filled only by
/// `note_proj_iota` on a record the in-process modeller generated.
pub fn proj_rewrite_d(st: &StateD, cv: &ConstantVal, vl: &Expr) -> Option<Expr> {
    let body = proj_rec::lam_body(vl);
    let (t, i) = match &body.0.kind {
        ExprKind::Proj(t, i, sub) => match &sub.0.kind {
            ExprKind::Bvar(k) => {
                if *k == 0 {
                    (name::dup(t), *i)
                } else {
                    return None;
                }
            }
            _ => return None,
        },
        _ => return None,
    };
    match st.proj_owners.get(&t) {
        None => None,
        Some(o) => {
            if !crate::frontend::export::names_beq(&cv.level_params, &o.lps) {
                return None;
            }
            match st.proj_levels.get(&proj_rec::proj_iota_name(&t, i)) {
                None => None,
                Some(l) => proj_rec::proj_rec_value(o, l, &cv.ty, vl, i),
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:304-317 noteProjIota
/// An artifact `T._model.proj_i.iota` names the field's sort in its `Eq`
/// level: recorded for the projection rewrite.  Run on the records the
/// in-process modeller GENERATES and on those alone.
pub fn note_proj_iota(st: &mut StateD, cvp: &ConstantVal) {
    if proj_rec::is_proj_iota_name(&cvp.name) {
        match proj_rec::proj_iota_level(&cvp.ty) {
            None => {}
            Some(l) => {
                st.proj_levels.insert(name::dup(&cvp.name), l);
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:319-326 pushGenD
/// Push one record the in-process modeller generated: `push_decl`, plus the
/// projection-iota registration (the ONLY place it runs).  Total since
/// con-leche task #293, as `push_decl` is.
pub fn push_gen_d(st: &mut StateD, d: Declaration) {
    match &d {
        Declaration::ThmDecl(cv, _) => {
            let cv2 = env::constant_val_dup(cv);
            note_proj_iota(st, &cv2);
        }
        _ => {}
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
    let n = names.len();
    let mut i = 0usize;
    while i < n {
        st.gen_owner.insert(name::dup(&names[i]), name::dup(t0));
        i += 1;
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:398-404 pushGenList
/// Push the records the in-process modeller generated (the loop of
/// `install_ind_d`, as a function), each booked as a declaration of the fold
/// and not a record of the file.
/// The list is BORROWED and each record copied in, for `note_entries`'
/// reason: the subset has no way to move an element out of an owned `Vec`.
pub fn push_gen_list(st: &mut StateD, gen: &Vec<Declaration>, t0: &Name) {
    let n = gen.len();
    let mut i = 0usize;
    while i < n {
        let names = env::declaration_names(&gen[i]);
        push_gen_d(st, declaration_dup(&gen[i]));
        note_gen_names(st, names, t0);
        i += 1;
    }
}

/// con-leche: none — the record copy `kernel::env` does not spell out, needed
/// because `push_gen_list` walks a borrowed list (see there).  Every field is
/// copied by the kernel's own `_dup`; a `ConstantVal`, an `Expr` and a `Name`
/// copy are pointer bumps.
pub fn declaration_dup(d: &Declaration) -> Declaration {
    match d {
        Declaration::AxiomDecl(cv) => Declaration::AxiomDecl(env::constant_val_dup(cv)),
        Declaration::DefnDecl(cv, v, h) => Declaration::DefnDecl(
            env::constant_val_dup(cv),
            expr::dup(v),
            env::reducibility_hint_dup(h),
        ),
        Declaration::ThmDecl(cv, v) => {
            Declaration::ThmDecl(env::constant_val_dup(cv), expr::dup(v))
        }
        Declaration::OpaqueDecl(cv, v) => {
            Declaration::OpaqueDecl(env::constant_val_dup(cv), expr::dup(v))
        }
        Declaration::BasisDecl(k) => Declaration::BasisDecl(env::basis_kind_dup(k)),
        Declaration::QuotDecl(k, cv) => {
            Declaration::QuotDecl(env::quot_kind_dup(k), env::constant_val_dup(cv))
        }
        Declaration::IndDecl(bl, n) => Declaration::IndDecl(constant_infos_dup(bl), *n),
    }
}

/// con-leche: none — `declaration_dup`'s block case, as an index loop.
pub fn constant_infos_dup(bl: &Vec<ConstantInfo>) -> Vec<ConstantInfo> {
    let mut out: Vec<ConstantInfo> = Vec::with_capacity(bl.len());
    let n = bl.len();
    let mut i = 0usize;
    while i < n {
        out.push(env::constant_info_dup(&bl[i]));
        i += 1;
    }
    out
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
pub fn parse_rule_d(st: &StateD, ru: &RuleRec) -> Result<RecRule, LineErr> {
    match st_name(st, ru.ctor) {
        Err(e) => Err(e),
        Ok(c) => match get_decl_d(st, ru.rhs) {
            Err(e) => Err(e),
            Ok(rhs) => Ok(env::rec_rule_parsed(c, ru.nfields, rhs)),
        },
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:346-349 parseRuleD
/// A recursor record's whole rule list (`r.rules.mapM (parseRuleD st)`).
pub fn parse_rules_d(st: &StateD, rus: &Vec<RuleRec>) -> Result<Vec<RecRule>, LineErr> {
    let mut out: Vec<RecRule> = Vec::with_capacity(rus.len());
    let n = rus.len();
    let mut i = 0usize;
    while i < n {
        match parse_rule_d(st, &rus[i]) {
            Err(e) => return Err(e),
            Ok(r) => out.push(r),
        }
        i += 1;
    }
    Ok(out)
}
// ==== agent C: assembled tail ====

/// con-leche: none — `x - y` on a `Nat`, which truncates at zero; Rust's
/// `u64`/`usize` subtraction does not, and Aeneas would carry the
/// non-underflow as a proof obligation a malformed stream can falsify.  Two
/// message positions and one offset read it.
pub fn sat_sub(a: u64, b: u64) -> u64 {
    if a >= b {
        a - b
    } else {
        0
    }
}

/// con-leche: none — `sat_sub` on the scanner's `usize` offsets: a scan
/// failure inside a line is reported at its offset IN the line.
pub fn rel_offset(off: usize, i: usize) -> usize {
    if off >= i {
        off - i
    } else {
        0
    }
}

/// con-leche: none — `CVRec` derives nothing (DESIGN.md §3.4) and
/// `validate_ind_d` returns the block's constructor records reordered, which
/// con-leche gets for free from Lean's sharing.
pub fn cv_rec_dup(cv: &CVRec) -> CVRec {
    let mut lps: Vec<u64> = Vec::with_capacity(cv.level_params.len());
    let n = cv.level_params.len();
    let mut i = 0usize;
    while i < n {
        lps.push(cv.level_params[i]);
        i += 1;
    }
    CVRec {
        name: cv.name,
        level_params: lps,
        ty: cv.ty,
    }
}

/// con-leche: none — `scan_types::IndCtorRec` derives nothing; see
/// `cv_rec_dup`.
pub fn ind_ctor_rec_dup(c: &IndCtorRec) -> IndCtorRec {
    IndCtorRec {
        cv: cv_rec_dup(&c.cv),
        is_unsafe: c.is_unsafe,
        num_fields: c.num_fields,
        num_params: c.num_params,
        cidx: c.cidx,
        induct: c.induct,
    }
}

/// con-leche: none — `proj_rec::ProjRecOwner` derives nothing, and
/// `register_proj_owners` inserts owners out of a borrowed list (Aeneas' `Vec`
/// model has no way to move an element out of an owned one).  It is here
/// rather than in `proj_rec` because this is its only caller.
pub fn proj_rec_owner_dup(o: &proj_rec::ProjRecOwner) -> proj_rec::ProjRecOwner {
    proj_rec::ProjRecOwner {
        t: name::dup(&o.t),
        lps: prop_when::names_copy(&o.lps),
        n_p: o.n_p,
        ctor: name::dup(&o.ctor),
        n_f: o.n_f,
        rec_name: name::dup(&o.rec_name),
        rec_lps: prop_when::names_copy(&o.rec_lps),
        rec_type: expr::dup(&o.rec_type),
        num_motives: o.num_motives,
        num_minors: o.num_minors,
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:351-375 blockRecOf
/// The export's shape data of an inductive record, for the in-process
/// modeller.
pub fn block_rec_of(
    st: &StateD,
    types: &Vec<IndTypeRec>,
    ctors: &Vec<IndCtorRec>,
    recs: &Vec<IndRecRec>,
) -> Result<BlockRec, LineErr> {
    match block_rec_types(st, types) {
        Err(e) => Err(e),
        Ok(ts) => match block_rec_ctors(st, ctors) {
            Err(e) => Err(e),
            Ok(cs) => match block_rec_recs(st, recs) {
                Err(e) => Err(e),
                Ok(rs) => Ok(BlockRec {
                    types: ts,
                    ctors: cs,
                    recs: rs,
                }),
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:351-375 blockRecOf
/// The cited `types.mapM`, as a loop whose tail is one line.
pub fn block_rec_types(
    st: &StateD,
    types: &Vec<IndTypeRec>,
) -> Result<Vec<in_model_rec::IndTypeRec>, LineErr> {
    let mut out: Vec<in_model_rec::IndTypeRec> = Vec::with_capacity(types.len());
    let n = types.len();
    let mut i = 0usize;
    while i < n {
        let t = &types[i];
        let cs = match st_names(st, &t.ctors) {
            Err(e) => return Err(e),
            Ok(v) => v,
        };
        match parse_cv_d(st, &t.cv) {
            Err(e) => return Err(e),
            Ok(cv) => out.push(in_model_rec::IndTypeRec {
                cv,
                n_p: t.num_params,
                n_idx: t.num_indices,
                ctors: cs,
                is_rec: t.is_rec,
                is_reflexive: t.is_reflexive,
                num_nested: t.num_nested,
            }),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:351-375 blockRecOf
/// The cited `ctors.mapM`.
pub fn block_rec_ctors(
    st: &StateD,
    ctors: &Vec<IndCtorRec>,
) -> Result<Vec<in_model_rec::IndCtorRec>, LineErr> {
    let mut out: Vec<in_model_rec::IndCtorRec> = Vec::with_capacity(ctors.len());
    let n = ctors.len();
    let mut i = 0usize;
    while i < n {
        let c = &ctors[i];
        match parse_cv_d(st, &c.cv) {
            Err(e) => return Err(e),
            Ok(cv) => out.push(in_model_rec::IndCtorRec {
                cv,
                n_p: c.num_params,
                n_f: c.num_fields,
            }),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:351-375 blockRecOf
/// The cited `recs.mapM`.
pub fn block_rec_recs(
    st: &StateD,
    recs: &Vec<IndRecRec>,
) -> Result<Vec<in_model_rec::IndRecRec>, LineErr> {
    let mut out: Vec<in_model_rec::IndRecRec> = Vec::with_capacity(recs.len());
    let n = recs.len();
    let mut i = 0usize;
    while i < n {
        let r = &recs[i];
        let rules = match parse_rules_d(st, &r.rules) {
            Err(e) => return Err(e),
            Ok(v) => v,
        };
        match parse_cv_d(st, &r.cv) {
            Err(e) => return Err(e),
            Ok(cv) => out.push(in_model_rec::IndRecRec {
                cv,
                n_p: r.num_params,
                n_m: r.num_motives,
                nm: r.num_minors,
                n_i: r.num_indices,
                rules,
            }),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:377-396 registerProjOwners
/// Record the structure-like owners of a parsed block that the projection
/// rewrite serves (`proj_rec::proj_rec_owners`).
pub fn register_proj_owners(
    st: &mut StateD,
    tys: &Vec<IndTypeRec>,
    cts: &Vec<IndCtorRec>,
    rcs: &Vec<IndRecRec>,
    block: &Vec<ConstantInfo>,
) -> Result<(), LineErr> {
    let types = match proj_type_recs_of(st, tys) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let ctors = match proj_ctor_recs_of(st, cts) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let recs = match proj_rec_recs_of(st, rcs) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let owners = proj_rec::proj_rec_owners(block, &types, &ctors, &recs);
    insert_proj_owners(st, &owners);
    Ok(())
}

/// con-leche: ConLeche/Frontend/ExportC.lean:377-396 registerProjOwners
/// The cited `types` component.
pub fn proj_type_recs_of(
    st: &StateD,
    tys: &Vec<IndTypeRec>,
) -> Result<Vec<proj_rec::ProjTypeRec>, LineErr> {
    let mut out: Vec<proj_rec::ProjTypeRec> = Vec::with_capacity(tys.len());
    let n = tys.len();
    let mut i = 0usize;
    while i < n {
        let t = &tys[i];
        let cv = match parse_cv_d(st, &t.cv) {
            Err(e) => return Err(e),
            Ok(v) => v,
        };
        let ctors = match st_names(st, &t.ctors) {
            Err(e) => return Err(e),
            Ok(v) => v,
        };
        out.push(proj_rec::ProjTypeRec {
            name: name::dup(&cv.name),
            lps: prop_when::names_copy(&cv.level_params),
            ty: expr::dup(&cv.ty),
            n_p: t.num_params,
            n_i: t.num_indices,
            ctors,
            is_rec: t.is_rec,
        });
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:377-396 registerProjOwners
/// The cited `ctors` component.
pub fn proj_ctor_recs_of(
    st: &StateD,
    cts: &Vec<IndCtorRec>,
) -> Result<Vec<proj_rec::ProjCtorRec>, LineErr> {
    let mut out: Vec<proj_rec::ProjCtorRec> = Vec::with_capacity(cts.len());
    let n = cts.len();
    let mut i = 0usize;
    while i < n {
        let c = &cts[i];
        match parse_cv_d(st, &c.cv) {
            Err(e) => return Err(e),
            Ok(cv) => out.push(proj_rec::ProjCtorRec {
                name: name::dup(&cv.name),
                n_f: c.num_fields,
                ty: expr::dup(&cv.ty),
            }),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:377-396 registerProjOwners
/// The cited `recs` component.
pub fn proj_rec_recs_of(
    st: &StateD,
    rcs: &Vec<IndRecRec>,
) -> Result<Vec<proj_rec::ProjRecRec>, LineErr> {
    let mut out: Vec<proj_rec::ProjRecRec> = Vec::with_capacity(rcs.len());
    let n = rcs.len();
    let mut i = 0usize;
    while i < n {
        let r = &rcs[i];
        match parse_cv_d(st, &r.cv) {
            Err(e) => return Err(e),
            Ok(cv) => out.push(proj_rec::ProjRecRec {
                name: name::dup(&cv.name),
                lps: prop_when::names_copy(&cv.level_params),
                ty: expr::dup(&cv.ty),
                n_m: r.num_motives,
                nm: r.num_minors,
            }),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:377-396 registerProjOwners
/// The cited `owners.foldl` into `projOwners`.
pub fn insert_proj_owners(st: &mut StateD, owners: &Vec<proj_rec::ProjRecOwner>) {
    let n = owners.len();
    let mut i = 0usize;
    while i < n {
        st.proj_owners
            .insert(name::dup(&owners[i].t), proj_rec_owner_dup(&owners[i]));
        i += 1;
    }
}

// ---------------------------------------------------------------------------
// `validateIndD` (`ExportC.lean:406-558`) and its pieces
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// The cited `tys.any (·.isUnsafe)`.
pub fn any_ty_unsafe(tys: &Vec<IndTypeRec>) -> bool {
    let n = tys.len();
    let mut i = 0usize;
    while i < n {
        if tys[i].is_unsafe {
            return true;
        }
        i += 1;
    }
    false
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// The cited `tys.any (·.numNested != 0)`.
pub fn any_ty_nested(tys: &Vec<IndTypeRec>) -> bool {
    let n = tys.len();
    let mut i = 0usize;
    while i < n {
        if tys[i].num_nested != 0 {
            return true;
        }
        i += 1;
    }
    false
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// The cited `tys.all (·.numParams == nPd)`.
pub fn all_num_params(tys: &Vec<IndTypeRec>, n_pd: u64) -> bool {
    let n = tys.len();
    let mut i = 0usize;
    while i < n {
        if tys[i].num_params != n_pd {
            return false;
        }
        i += 1;
    }
    true
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// The block's type-former names.
pub fn ty_names_of(st: &StateD, tys: &Vec<IndTypeRec>) -> Result<Vec<Name>, LineErr> {
    let mut out: Vec<Name> = Vec::with_capacity(tys.len());
    let n = tys.len();
    let mut i = 0usize;
    while i < n {
        match st_name(st, tys[i].cv.name) {
            Err(e) => return Err(e),
            Ok(v) => out.push(v),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// The block's type-former declared types.
pub fn ty_types_of(st: &StateD, tys: &Vec<IndTypeRec>) -> Result<Vec<Expr>, LineErr> {
    let mut out: Vec<Expr> = Vec::with_capacity(tys.len());
    let n = tys.len();
    let mut i = 0usize;
    while i < n {
        match get_decl_d(st, tys[i].cv.ty) {
            Err(e) => return Err(e),
            Ok(v) => out.push(v),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// The constructor names each type record LISTS, in type order.
pub fn listed_ctors_of(st: &StateD, tys: &Vec<IndTypeRec>) -> Result<Vec<Vec<Name>>, LineErr> {
    let mut out: Vec<Vec<Name>> = Vec::with_capacity(tys.len());
    let n = tys.len();
    let mut i = 0usize;
    while i < n {
        match st_names(st, &tys[i].ctors) {
            Err(e) => return Err(e),
            Ok(v) => out.push(v),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// The names of the constructor RECORDS the block carries, in record order.
pub fn ctor_names_of(st: &StateD, cts: &Vec<IndCtorRec>) -> Result<Vec<Name>, LineErr> {
    let mut out: Vec<Name> = Vec::with_capacity(cts.len());
    let n = cts.len();
    let mut i = 0usize;
    while i < n {
        match st_name(st, cts[i].cv.name) {
            Err(e) => return Err(e),
            Ok(v) => out.push(v),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// The cited `listed.flatten`.
pub fn flatten_listed(listed: &Vec<Vec<Name>>) -> Vec<Name> {
    let mut out: Vec<Name> = Vec::new();
    let n = listed.len();
    let mut i = 0usize;
    while i < n {
        let inner = &listed[i];
        let k = inner.len();
        let mut j = 0usize;
        while j < k {
            out.push(name::dup(&inner[j]));
            j += 1;
        }
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// Does the flattened constructor list repeat a name?  con-leche's
/// `HashSet.insert` test; the port's set is a `HashMap<Name, bool>`.
pub fn names_have_dup(flat: &Vec<Name>) -> bool {
    let mut seen: HashMap<Name, bool> = HashMap::new();
    let n = flat.len();
    let mut i = 0usize;
    while i < n {
        if seen.contains_key(&flat[i]) {
            return true;
        }
        seen.insert(name::dup(&flat[i]), true);
        i += 1;
    }
    false
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// The constructor records by name, FIRST record wins (con-leche's
/// `HashMap.insertIfNew`).
pub fn ctor_index_of(ns: &Vec<Name>) -> HashMap<Name, u64> {
    let mut m: HashMap<Name, u64> = HashMap::new();
    let n = ns.len();
    let mut k = 0usize;
    while k < n {
        if !m.contains_key(&ns[k]) {
            m.insert(name::dup(&ns[k]), k as u64);
        }
        k += 1;
    }
    m
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"No such constructor {n}"`.
pub fn no_such_ctor_error(n: &Name) -> Vec<u32> {
    const A: [u32; 20] = [
        78, 111, 32, 115, 117, 99, 104, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111,
        114, 32
    ];
    text::cat(core_types::code_points(&A), &text::name_str(n))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"the inductive block lists {a} constructors and carries {b} constructor
/// records"`.
pub fn ctor_count_error(a: u64, b: u64) -> Vec<u32> {
    const A: [u32; 26] = [
        116, 104, 101, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99,
        107, 32, 108, 105, 115, 116, 115, 32
    ];
    const B: [u32; 26] = [
        32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 115, 32, 97, 110, 100, 32,
        99, 97, 114, 114, 105, 101, 115, 32
    ];
    const C: [u32; 20] = [
        32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 114, 101, 99, 111, 114,
        100, 115
    ];
    let s = text::cat3(
        core_types::code_points(&A),
        &text::u64_str(a),
        &core_types::code_points(&B),
    );
    text::cat3(s, &text::u64_str(b), &core_types::code_points(&C))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"constructor {n} declares cidx {ci}; it is constructor {j} of {t}"`.
pub fn cidx_error(n: &Name, ci: u64, j: u64, t: &Name) -> Vec<u32> {
    const A: [u32; 12] = [99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32];
    const B: [u32; 15] = [32, 100, 101, 99, 108, 97, 114, 101, 115, 32, 99, 105, 100, 120, 32];
    const C: [u32; 20] = [
        59, 32, 105, 116, 32, 105, 115, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111,
        114, 32
    ];
    const D: [u32; 4] = [32, 111, 102, 32];
    let s = text::cat3(
        core_types::code_points(&A),
        &text::name_str(n),
        &core_types::code_points(&B),
    );
    let s = text::cat3(s, &text::u64_str(ci), &core_types::code_points(&C));
    let s = text::cat3(s, &text::u64_str(j), &core_types::code_points(&D));
    text::cat(s, &text::name_str(t))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"constructor {n} declares induct {iw}; it is a constructor of {t}"`.
pub fn induct_error(n: &Name, iw: &Name, t: &Name) -> Vec<u32> {
    const A: [u32; 12] = [99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32];
    const B: [u32; 17] = [
        32, 100, 101, 99, 108, 97, 114, 101, 115, 32, 105, 110, 100, 117, 99, 116, 32
    ];
    const C: [u32; 25] = [
        59, 32, 105, 116, 32, 105, 115, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99,
        116, 111, 114, 32, 111, 102, 32
    ];
    let s = text::cat3(
        core_types::code_points(&A),
        &text::name_str(n),
        &core_types::code_points(&B),
    );
    let s = text::cat3(s, &text::name_str(iw), &core_types::code_points(&C));
    text::cat(s, &text::name_str(t))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"constructor {n} declares {f} fields at {p} parameters; its type has {b}
/// binders"`.
pub fn fields_error(n: &Name, f: u64, p: u64, b: u64) -> Vec<u32> {
    const A: [u32; 12] = [99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32];
    const B: [u32; 10] = [32, 100, 101, 99, 108, 97, 114, 101, 115, 32];
    const C: [u32; 11] = [32, 102, 105, 101, 108, 100, 115, 32, 97, 116, 32];
    const D: [u32; 26] = [
        32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 59, 32, 105, 116, 115, 32, 116,
        121, 112, 101, 32, 104, 97, 115, 32
    ];
    const E: [u32; 8] = [32, 98, 105, 110, 100, 101, 114, 115];
    let s = text::cat3(
        core_types::code_points(&A),
        &text::name_str(n),
        &core_types::code_points(&B),
    );
    let s = text::cat3(s, &text::u64_str(f), &core_types::code_points(&C));
    let s = text::cat3(s, &text::u64_str(p), &core_types::code_points(&D));
    text::cat3(s, &text::u64_str(b), &core_types::code_points(&E))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// One constructor record, validated against the block's own declarations:
/// the redundant `cidx` and `induct` fields and the declared `numFields`.
pub fn check_one_ctor(
    st: &StateD,
    n: &Name,
    t: &Name,
    c: &IndCtorRec,
    j: u64,
    n_pd: u64,
) -> Result<(), LineErr> {
    match c.cidx {
        None => {}
        Some(ci) => {
            if ci != j {
                return invalid(cidx_error(n, ci, j, t));
            }
        }
    }
    match c.induct {
        None => {}
        Some(iw) => {
            let iwn = match st_name(st, iw) {
                Err(e) => return Err(e),
                Ok(v) => v,
            };
            if !name::beq(&iwn, t) {
                return invalid(induct_error(n, &iwn, t));
            }
        }
    }
    // `numFields`: official counts the constructor's own Π binders without
    // reducing and stores the count past the parameters, so a record that
    // declares another number is not the generated constructor.
    let cty = match get_decl_d(st, c.cv.ty) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let b = ind_pi_tele_len(&cty);
    if n_pd + c.num_fields != b {
        return invalid(fields_error(n, c.num_fields, n_pd, b));
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// One type former's constructors, in the order the type record LISTS them:
/// the inner loop of the reordering, with the accumulator passed by value.
pub fn order_type_ctors(
    st: &StateD,
    t: &Name,
    ns: &Vec<Name>,
    cts: &Vec<IndCtorRec>,
    ctor_ix: &HashMap<Name, u64>,
    n_pd: u64,
    out: Vec<IndCtorRec>,
) -> Result<Vec<IndCtorRec>, LineErr> {
    let mut out = out;
    let n = ns.len();
    let mut j: u64 = 0;
    let mut i = 0usize;
    while i < n {
        let nm = &ns[i];
        let k = match ctor_ix.get(nm) {
            None => return invalid(no_such_ctor_error(nm)),
            Some(k) => *k as usize,
        };
        if k >= cts.len() {
            return invalid(no_such_ctor_error(nm));
        }
        match check_one_ctor(st, nm, t, &cts[k], j, n_pd) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        out.push(ind_ctor_rec_dup(&cts[k]));
        j += 1;
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// **The constructors IN THE BLOCK'S OWN ORDER**, `types[].ctors` in type
/// order (con-leche task #271, issue #5): a record array in another order is
/// the same block, and the recursor generated from it is the same one.
pub fn order_block_ctors(
    st: &StateD,
    ty_names: &Vec<Name>,
    listed: &Vec<Vec<Name>>,
    cts: &Vec<IndCtorRec>,
    ctor_ix: &HashMap<Name, u64>,
    n_pd: u64,
) -> Result<Vec<IndCtorRec>, LineErr> {
    let mut out: Vec<IndCtorRec> = Vec::new();
    let n = ty_names.len();
    let mut t_at = 0usize;
    while t_at < n {
        match order_type_ctors(st, &ty_names[t_at], &listed[t_at], cts, ctor_ix, n_pd, out) {
            Err(e) => return Err(e),
            Ok(o) => out = o,
        }
        t_at += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// official's `is_K_target`: the block is a `Prop`, has ONE type with ONE
/// constructor, and that constructor takes only the parameters.  At a former
/// whose declared type is not a syntactic Π-telescope ending in a sort the
/// sort cannot be read here and the flag is left to the install (`None`).
pub fn k_expected_of(
    ty_types: &Vec<Expr>,
    listed: &Vec<Vec<Name>>,
    cts: &Vec<IndCtorRec>,
) -> Option<bool> {
    if ty_types.len() != 1 || listed.len() != 1 || cts.len() != 1 {
        return Some(false);
    }
    if listed[0].len() != 1 {
        return Some(false);
    }
    let res = expr_ops::pi_result(&ty_types[0]);
    match &res.0.kind {
        ExprKind::Sort(s) => {
            let z = level::zero();
            let is_prop = match level::is_equiv(s, &z) {
                Some(b) => b,
                None => false,
            };
            Some(cts[0].num_fields == 0 && is_prop)
        }
        _ => None,
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"recursor {rn} declares {a} parameters; the block declares {b}"`.
pub fn rec_params_error(rn: &Name, a: u64, b: u64) -> Vec<u32> {
    const A: [u32; 9] = [114, 101, 99, 117, 114, 115, 111, 114, 32];
    const B: [u32; 10] = [32, 100, 101, 99, 108, 97, 114, 101, 115, 32];
    const C: [u32; 32] = [
        32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 59, 32, 116, 104, 101, 32, 98,
        108, 111, 99, 107, 32, 100, 101, 99, 108, 97, 114, 101, 115, 32
    ];
    let s = text::cat3(
        core_types::code_points(&A),
        &text::name_str(rn),
        &core_types::code_points(&B),
    );
    let s = text::cat3(s, &text::u64_str(a), &core_types::code_points(&C));
    text::cat(s, &text::u64_str(b))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"recursor {rn} declares {a} motives; the block has {b} inductive types"`.
pub fn rec_motives_error(rn: &Name, a: u64, b: u64) -> Vec<u32> {
    const A: [u32; 9] = [114, 101, 99, 117, 114, 115, 111, 114, 32];
    const B: [u32; 10] = [32, 100, 101, 99, 108, 97, 114, 101, 115, 32];
    const C: [u32; 24] = [
        32, 109, 111, 116, 105, 118, 101, 115, 59, 32, 116, 104, 101, 32, 98, 108, 111, 99,
        107, 32, 104, 97, 115, 32
    ];
    const D: [u32; 16] = [
        32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 115
    ];
    let s = text::cat3(
        core_types::code_points(&A),
        &text::name_str(rn),
        &core_types::code_points(&B),
    );
    let s = text::cat3(s, &text::u64_str(a), &core_types::code_points(&C));
    text::cat3(s, &text::u64_str(b), &core_types::code_points(&D))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"recursor {rn} declares {a} minor premises; the block has {b}
/// constructors"`.
pub fn rec_minors_error(rn: &Name, a: u64, b: u64) -> Vec<u32> {
    const A: [u32; 9] = [114, 101, 99, 117, 114, 115, 111, 114, 32];
    const B: [u32; 10] = [32, 100, 101, 99, 108, 97, 114, 101, 115, 32];
    const C: [u32; 31] = [
        32, 109, 105, 110, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 115, 59, 32,
        116, 104, 101, 32, 98, 108, 111, 99, 107, 32, 104, 97, 115, 32
    ];
    const D: [u32; 13] = [32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 115];
    let s = text::cat3(
        core_types::code_points(&A),
        &text::name_str(rn),
        &core_types::code_points(&B),
    );
    let s = text::cat3(s, &text::u64_str(a), &core_types::code_points(&C));
    text::cat3(s, &text::u64_str(b), &core_types::code_points(&D))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"recursor {rn} declares k := {k}; the generated recursor of this block
/// is[ not] K-like"`.
pub fn rec_k_error(rn: &Name, k: bool, k_e: bool) -> Vec<u32> {
    const A: [u32; 9] = [114, 101, 99, 117, 114, 115, 111, 114, 32];
    const B: [u32; 15] = [32, 100, 101, 99, 108, 97, 114, 101, 115, 32, 107, 32, 58, 61, 32];
    const C: [u32; 41] = [
        59, 32, 116, 104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101,
        99, 117, 114, 115, 111, 114, 32, 111, 102, 32, 116, 104, 105, 115, 32, 98, 108, 111,
        99, 107, 32, 105, 115
    ];
    const D: [u32; 4] = [32, 110, 111, 116];
    const E: [u32; 7] = [32, 75, 45, 108, 105, 107, 101];
    let s = text::cat3(
        core_types::code_points(&A),
        &text::name_str(rn),
        &core_types::code_points(&B),
    );
    let s = text::cat3(s, &bool_str(k), &core_types::code_points(&C));
    let s = if k_e {
        s
    } else {
        text::cat(s, &core_types::code_points(&D))
    };
    text::cat(s, &core_types::code_points(&E))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"recursor {rn} declares {a} indices; {t} has {b} at {p} parameters"`.
pub fn rec_indices_error(rn: &Name, a: u64, t: &Name, b: u64, p: u64) -> Vec<u32> {
    const A: [u32; 9] = [114, 101, 99, 117, 114, 115, 111, 114, 32];
    const B: [u32; 10] = [32, 100, 101, 99, 108, 97, 114, 101, 115, 32];
    const C: [u32; 10] = [32, 105, 110, 100, 105, 99, 101, 115, 59, 32];
    const D: [u32; 5] = [32, 104, 97, 115, 32];
    const E: [u32; 4] = [32, 97, 116, 32];
    const F: [u32; 11] = [32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115];
    let s = text::cat3(
        core_types::code_points(&A),
        &text::name_str(rn),
        &core_types::code_points(&B),
    );
    let s = text::cat3(s, &text::u64_str(a), &core_types::code_points(&C));
    let s = text::cat3(s, &text::name_str(t), &core_types::code_points(&D));
    let s = text::cat3(s, &text::u64_str(b), &core_types::code_points(&E));
    text::cat3(s, &text::u64_str(p), &core_types::code_points(&F))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `numIndices` of `T.rec` is what is left of `T`'s own telescope once the
/// parameters are peeled; unreadable at a former declared at a definition,
/// and then not checked.
pub fn check_rec_indices(
    rn: &Name,
    t_pre: &Name,
    num_indices: u64,
    ty_names: &Vec<Name>,
    ty_types: &Vec<Expr>,
    n_pd: u64,
) -> Result<(), LineErr> {
    let n = ty_names.len();
    let mut i = 0usize;
    while i < n {
        if name::beq(&ty_names[i], t_pre) {
            match env::pi_sort_tele_len(&ty_types[i]) {
                None => {}
                Some(k) => {
                    if n_pd + num_indices != k {
                        return invalid(rec_indices_error(
                            rn,
                            num_indices,
                            t_pre,
                            sat_sub(k, n_pd),
                            n_pd,
                        ));
                    }
                }
            }
        }
        i += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// One recursor record: the counts and the K flag the GENERATED recursor
/// carries.
pub fn check_one_rec(
    st: &StateD,
    r: &IndRecRec,
    ty_names: &Vec<Name>,
    ty_types: &Vec<Expr>,
    n_pd: u64,
    n_types: u64,
    n_ctors: u64,
    k_exp: &Option<bool>,
) -> Result<(), LineErr> {
    let rn = match st_name(st, r.cv.name) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    if r.num_params != n_pd {
        return invalid(rec_params_error(&rn, r.num_params, n_pd));
    }
    if r.num_motives != n_types {
        return invalid(rec_motives_error(&rn, r.num_motives, n_types));
    }
    if r.num_minors != n_ctors {
        return invalid(rec_minors_error(&rn, r.num_minors, n_ctors));
    }
    match k_exp {
        None => {}
        Some(k_e) => {
            if r.k != *k_e {
                return invalid(rec_k_error(&rn, r.k, *k_e));
            }
        }
    }
    match &rn.0.kind {
        NameKind::Str(t_pre, last) => {
            const R: [u32; 3] = [114, 101, 99];
            if text::cps_beq(last, &R) {
                check_rec_indices(&rn, t_pre, r.num_indices, ty_names, ty_types, n_pd)
            } else {
                Ok(())
            }
        }
        _ => Ok(()),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// Every recursor record of the block.  NOT run at a NESTED block — the
/// kernel specialises a nested block into a mutual one with a mimic type per
/// nested occurrence, and the recursors it generates are the SPECIALISED
/// block's.
pub fn check_rec_records(
    st: &StateD,
    rcs: &Vec<IndRecRec>,
    ty_names: &Vec<Name>,
    ty_types: &Vec<Expr>,
    n_pd: u64,
    n_types: u64,
    n_ctors: u64,
    k_exp: &Option<bool>,
) -> Result<(), LineErr> {
    let n = rcs.len();
    let mut i = 0usize;
    while i < n {
        match check_one_rec(st, &rcs[i], ty_names, ty_types, n_pd, n_types, n_ctors, k_exp) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
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
/// error channel.  The loops are the functions above (the module note).
pub fn validate_ind_d(
    st: &StateD,
    tys: &Vec<IndTypeRec>,
    cts: &Vec<IndCtorRec>,
    rcs: &Vec<IndRecRec>,
) -> Result<(Vec<IndCtorRec>, u64), LineErr> {
    // an `unsafe inductive` is DECLINED, not an error: the official kernel
    // admits unsafe blocks (it skips positivity for them); we support no
    // unsafe declaration at all.
    if any_ty_unsafe(tys) {
        const M1: [u32; 28] = [
            117, 110, 115, 97, 102, 101, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32,
            100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110
        ];
        return declined(core_types::code_points(&M1));
    }
    // TASK #228 — THE DECLARED PARAMETER COUNT.  A block whose type records
    // disagree on `numParams` has no declared count this checker could hold
    // official to, and is positively declined here.
    let n_pd = if tys.len() == 0 { 0 } else { tys[0].num_params };
    if !all_num_params(tys, n_pd) {
        const M2: [u32; 56] = [
            105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99, 107, 32, 119,
            104, 111, 115, 101, 32, 116, 121, 112, 101, 32, 114, 101, 99, 111, 114, 100,
            115, 32, 100, 105, 115, 97, 103, 114, 101, 101, 32, 111, 110, 32, 110, 117, 109,
            80, 97, 114, 97, 109, 115
        ];
        return declined(core_types::code_points(&M2));
    }
    // TASK #271 (issues #5 and #7) — THE BLOCK'S REDUNDANT FIELDS.  These are
    // consistency checks between the stream's own fields, so they live here,
    // in the parse, and their verdict is `.invalid`: the fold never sees such
    // a block.
    let ty_names = match ty_names_of(st, tys) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let ty_types = match ty_types_of(st, tys) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let listed = match listed_ctors_of(st, tys) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let ctor_names = match ctor_names_of(st, cts) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    let flat = flatten_listed(&listed);
    if names_have_dup(&flat) {
        const M3: [u32; 55] = [
            100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 99, 111, 110, 115, 116, 114, 117,
            99, 116, 111, 114, 32, 110, 97, 109, 101, 32, 105, 110, 32, 97, 110, 32, 105,
            110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 39, 115, 32, 99,
            116, 111, 114, 115
        ];
        return invalid(core_types::code_points(&M3));
    }
    if flat.len() != cts.len() {
        return invalid(ctor_count_error(flat.len() as u64, cts.len() as u64));
    }
    let ctor_ix = ctor_index_of(&ctor_names);
    let ordered = match order_block_ctors(st, &ty_names, &listed, cts, &ctor_ix, n_pd) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    // The recursor records: the counts and the K flag the GENERATED recursor
    // carries.
    let nested = any_ty_nested(tys);
    let n_types = tys.len() as u64;
    let n_ctors = ordered.len() as u64;
    let k_exp = k_expected_of(&ty_types, &listed, &ordered);
    if !nested {
        match check_rec_records(st, rcs, &ty_names, &ty_types, n_pd, n_types, n_ctors, &k_exp) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
    }
    Ok((ordered, n_pd))
}

// ---------------------------------------------------------------------------
// `installIndD` (`ExportC.lean:560-623`) and its pieces
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ExportC.lean:560-623 installIndD
/// The cited `types ++ ctors ++ recs`: the block's `ConstantInfo`s, built in
/// three loops each of which is its own function.
pub fn ind_block_of(
    st: &StateD,
    tys: &Vec<IndTypeRec>,
    cts: &Vec<IndCtorRec>,
    rcs: &Vec<IndRecRec>,
) -> Result<Vec<ConstantInfo>, LineErr> {
    match ind_block_types(st, tys, Vec::new()) {
        Err(e) => Err(e),
        Ok(b) => match ind_block_ctors(st, cts, b) {
            Err(e) => Err(e),
            Ok(b2) => ind_block_recs(st, rcs, b2),
        },
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:560-623 installIndD
/// The cited `tys.mapM`.
pub fn ind_block_types(
    st: &StateD,
    tys: &Vec<IndTypeRec>,
    out: Vec<ConstantInfo>,
) -> Result<Vec<ConstantInfo>, LineErr> {
    let mut out = out;
    let n = tys.len();
    let mut i = 0usize;
    while i < n {
        match parse_cv_d(st, &tys[i].cv) {
            Err(e) => return Err(e),
            Ok(cv) => out.push(ConstantInfo::IndInfo(cv, env::ind_caps_default())),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:560-623 installIndD
/// The cited `cts.mapM`.
pub fn ind_block_ctors(
    st: &StateD,
    cts: &Vec<IndCtorRec>,
    out: Vec<ConstantInfo>,
) -> Result<Vec<ConstantInfo>, LineErr> {
    let mut out = out;
    let n = cts.len();
    let mut i = 0usize;
    while i < n {
        let c = &cts[i];
        match parse_cv_d(st, &c.cv) {
            Err(e) => return Err(e),
            Ok(cv) => out.push(ConstantInfo::CtorInfo(cv, c.num_params, c.num_fields)),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:560-623 installIndD
/// The cited `rcs.mapM`.
pub fn ind_block_recs(
    st: &StateD,
    rcs: &Vec<IndRecRec>,
    out: Vec<ConstantInfo>,
) -> Result<Vec<ConstantInfo>, LineErr> {
    let mut out = out;
    let n = rcs.len();
    let mut i = 0usize;
    while i < n {
        let r = &rcs[i];
        let rules = match parse_rules_d(st, &r.rules) {
            Err(e) => return Err(e),
            Ok(v) => v,
        };
        match parse_cv_d(st, &r.cv) {
            Err(e) => return Err(e),
            Ok(cv) => out.push(ConstantInfo::RecInfo(
                cv,
                r.num_params + r.num_motives + r.num_minors + r.num_indices,
                r.num_params + r.num_motives + r.num_minors,
                rules,
            )),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:560-623 installIndD
/// The cited `b.types.foldl (fun m t => m.insert t.cv.name b)`: the block is
/// registered under every member type name, shared through `ron::ptr`.
pub fn note_ind_blocks(st: &mut StateD, b: &P<BlockRec>) {
    let n = b.types.len();
    let mut i = 0usize;
    while i < n {
        st.ind_blocks
            .insert(name::dup(&b.types[i].cv.name), ptr::clone(b));
        i += 1;
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:560-623 installIndD
/// `"in-process model of {t0}: {why}"`.
pub fn in_model_decline(t0: &Name, why: &Vec<u32>) -> Vec<u32> {
    const A: [u32; 20] = [
        105, 110, 45, 112, 114, 111, 99, 101, 115, 115, 32, 109, 111, 100, 101, 108, 32,
        111, 102, 32
    ];
    const B: [u32; 2] = [58, 32];
    let s = text::cat3(
        core_types::code_points(&A),
        &text::name_str(t0),
        &core_types::code_points(&B),
    );
    text::cat(s, why)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:560-623 installIndD
/// **THE IN-PROCESS MODELLER** (the ONLY model source, and the only one there
/// IS — a stream `_model` record is an ordinary declaration and is never
/// consulted): a mutual or nested block gets its `_model` family generated
/// here and pushed ahead of it; the block then installs through the modeled
/// route.  A generator decline is the run's decline, naming the class (the
/// residual: infinitary nesting, a `Prop` block with a large eliminator).
///
/// Split out of `install_ind_d` so that the caller's tail after its own
/// `match` is one call; `m` is the seam (the module note).
pub fn install_gen<G: Modeller>(
    m: &G,
    st: &mut StateD,
    block: Vec<ConstantInfo>,
    n_pd: u64,
    t0: &Name,
    b: &P<BlockRec>,
) -> Result<(), LineErr> {
    let gen = {
        let ctx = state_model_ctx(st);
        m.generate(&ctx, &**b)
    };
    match gen {
        Err(why) => {
            if st.in_model_census {
                st.in_model_declined.push((name::dup(t0), why));
                push_decl(st, Declaration::IndDecl(block, n_pd));
                Ok(())
            } else {
                declined(in_model_decline(t0, &why))
            }
        }
        Ok(gen2) => {
            // a generated record is a declaration of the FOLD and not a
            // record of the file: booked in `push_gen_list`, so the verdict
            // line reports the file's own count
            push_gen_list(st, &gen2, t0);
            st.in_modelled.push(name::dup(t0));
            push_decl(st, Declaration::IndDecl(block, n_pd));
            Ok(())
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:560-623 installIndD
/// **An inductive record, installed**: the block's constants, the
/// projection-owner table, the in-process modeller, the push.  Every change
/// to the state a validated inductive record makes is here.
///
/// **EVERY BLOCK IS AN `IndDecl`** (con-leche task #293): the basis-pin match
/// that used to stand here — a name pre-filter and then `canon_eq_list`
/// against the five pinned blocks — is the FOLD's (`checker::check_decl` asks
/// `basis_raw::basis_pin_hit`).  A block under a pinned name that does NOT
/// match keeps its `IndDecl` form and is rejected by the fold's reserved-name
/// check, exactly as before.
pub fn install_ind_d<G: Modeller>(
    m: &G,
    st: &mut StateD,
    tys: &Vec<IndTypeRec>,
    cts: Vec<IndCtorRec>,
    rcs: &Vec<IndRecRec>,
    n_pd: u64,
) -> Result<(), LineErr> {
    let block = match ind_block_of(st, tys, &cts, rcs) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    // the projection rewrite's owner table (the export's own shape data)
    match register_proj_owners(st, tys, &cts, rcs, &block) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    let t0 = if block.len() == 0 {
        name::anonymous()
    } else {
        env::constant_info_name(&block[0])
    };
    let b = match block_rec_of(st, tys, &cts, rcs) {
        Err(e) => return Err(e),
        Ok(v) => ptr::new(v),
    };
    note_ind_blocks(st, &b);
    if st.in_model && in_model_rec::wants(&b) {
        install_gen(m, st, block, n_pd, &t0, &b)
    } else {
        push_decl(st, Declaration::IndDecl(block, n_pd));
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// The line, the chunk, the parse
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ExportC.lean:625-697 processLineCoreD
/// `"definition with safety '{s}'"`.
pub fn safety_error(s: &Vec<u32>) -> Vec<u32> {
    const A: [u32; 24] = [
        100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 119, 105, 116, 104, 32, 115,
        97, 102, 101, 116, 121, 32, 39
    ];
    const B: [u32; 1] = [39];
    text::cat3(core_types::code_points(&A), s, &core_types::code_points(&B))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:625-697 processLineCoreD
/// `"unknown quotient kind '{k}'"`.
pub fn quot_kind_error(k: &Vec<u32>) -> Vec<u32> {
    const A: [u32; 23] = [
        117, 110, 107, 110, 111, 119, 110, 32, 113, 117, 111, 116, 105, 101, 110, 116, 32,
        107, 105, 110, 100, 32, 39
    ];
    const B: [u32; 1] = [39];
    text::cat3(core_types::code_points(&A), k, &core_types::code_points(&B))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:625-697 processLineCoreD
/// The `#QUOT` record's `kind` word, as the kernel's `QuotKind`.
pub fn quot_kind_of(k: &Vec<u32>) -> Option<QuotKind> {
    const T: [u32; 4] = [116, 121, 112, 101];
    const C: [u32; 4] = [99, 116, 111, 114];
    const L: [u32; 4] = [108, 105, 102, 116];
    const I: [u32; 3] = [105, 110, 100];
    if text::cps_beq(k, &T) {
        Some(QuotKind::Type)
    } else if text::cps_beq(k, &C) {
        Some(QuotKind::Ctor)
    } else if text::cps_beq(k, &L) {
        Some(QuotKind::Lift)
    } else if text::cps_beq(k, &I) {
        Some(QuotKind::Ind)
    } else {
        None
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:625-697 processLineCoreD
/// The record's own semantics: the declaration kinds, producing `Declaration`
/// records.  Every branch, guard and error string is the one the `Lean.Json`
/// reader this replaced had; only the reads changed, from key lookups in a DOM
/// to fields of a syntax record.
pub fn process_line_core_d<G: Modeller>(
    m: &G,
    st: &mut StateD,
    d: &DeclRec,
) -> Result<(), LineErr> {
    match d {
        DeclRec::Ax(cvr, is_unsafe) => {
            let cvp = match parse_cv_d(st, cvr) {
                Err(e) => return Err(e),
                Ok(v) => v,
            };
            if *is_unsafe {
                const M1: [u32; 12] = [117, 110, 115, 97, 102, 101, 32, 97, 120, 105, 111, 109];
                return declined(core_types::code_points(&M1));
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
            let cvp = match parse_cv_d(st, cvr) {
                Err(e) => return Err(e),
                Ok(v) => v,
            };
            const SAFE: [u32; 4] = [115, 97, 102, 101];
            if !text::cps_beq(safety, &SAFE) {
                return declined(safety_error(safety));
            }
            let vl = match get_decl_d(st, *value) {
                Err(e) => return Err(e),
                Ok(v) => v,
            };
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
            let cvp = match parse_cv_d(st, cvr) {
                Err(e) => return Err(e),
                Ok(v) => v,
            };
            let vl = match get_decl_d(st, *value) {
                Err(e) => return Err(e),
                Ok(v) => v,
            };
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
            let cvp = match parse_cv_d(st, cvr) {
                Err(e) => return Err(e),
                Ok(v) => v,
            };
            if *is_unsafe {
                const M2: [u32; 25] = [
                    117, 110, 115, 97, 102, 101, 32, 111, 112, 97, 113, 117, 101, 32, 100,
                    101, 99, 108, 97, 114, 97, 116, 105, 111, 110
                ];
                return declined(core_types::code_points(&M2));
            }
            let vl = match get_decl_d(st, *value) {
                Err(e) => return Err(e),
                Ok(v) => v,
            };
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
            let cv = match parse_cv_d(st, cvr) {
                Err(e) => return Err(e),
                Ok(v) => v,
            };
            match quot_kind_of(kind) {
                None => merr(quot_kind_error(kind)),
                Some(qk) => {
                    push_decl(st, Declaration::QuotDecl(qk, cv));
                    Ok(())
                }
            }
        }
        DeclRec::Ind(tys, cts, rcs) => {
            st.ind_count += 1;
            match validate_ind_d(st, tys, cts, rcs) {
                Err(e) => Err(e),
                Ok((cts2, n_pd)) => install_ind_d(m, st, tys, cts2, rcs, n_pd),
            }
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
pub fn apply_decl_d<G: Modeller>(m: &G, st: &mut StateD, d: &DeclRec) -> Result<(), LineErr> {
    process_line_core_d(m, st, d)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:713-726 applyLine
/// **The semantic layer**: one scanned line applied to the parse state.
pub fn apply_line<G: Modeller>(m: &G, st: &mut StateD, r: &LineRec) -> Result<(), LineErr> {
    match r {
        LineRec::Expr(i, e) => parse_expr_entry_d(st, *i, e),
        LineRec::Name(i, n) => parse_name_entry_d(st, *i, n),
        LineRec::Level(i, l) => parse_level_entry_d(st, *i, l),
        LineRec::Decl(d) => apply_decl_d(m, st, d),
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
    pub gen_owner: HashMap<Name, Name>,
    /// the census's declines (block, reason)
    pub in_model_declined: Vec<(Name, Vec<u32>)>,
}

/// con-leche: ConLeche/Frontend/ExportC.lean:760-763 ParseResultD.ofState
/// The result: the file's records, in the file's order.
pub fn parse_result_of_state(st: StateD) -> ParseResultD {
    ParseResultD {
        decls: st.decls,
        proj_rewrites: st.proj_rewrites,
        in_modelled: st.in_modelled,
        gen_records: st.gen_records,
        gen_owner: st.gen_owner,
        in_model_declined: st.in_model_declined,
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:765-775 applyFinalLine
/// Scan and apply the LAST line of a stream — the one no newline ends.  A
/// syntactic failure is reported at its offset in the line.
pub fn apply_final_line<G: Modeller>(
    m: &G,
    st: &mut StateD,
    b: &[u8],
    i: usize,
    line_no: u64,
) -> Result<(), (CheckError, u64)> {
    match scan_fast::scan_line_fwd(b, i) {
        Err(e) => Err((
            core_types::internal(scan_err_render(&ScanErr {
                offset: rel_offset(e.offset, i),
                what: e.what,
            })),
            line_no,
        )),
        Ok((r, _)) => match apply_line(m, st, &r) {
            Err(e) => Err(line_err_to_check(e, line_no)),
            Ok(()) => Ok(()),
        },
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:777-811 feedChunk
/// Every COMPLETE line of the chunk from `i`, applied in order: the line count
/// and where the incomplete tail begins (the caller carries it into the next
/// chunk).  A line a chunk cut in half is told from a malformed one by whether
/// the rest of the chunk holds a newline at all — which is why a scan failure
/// is not immediately an error.
pub fn feed_chunk<G: Modeller>(
    m: &G,
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
                if scan_fast::newline_from(b, i) {
                    return Err((
                        core_types::internal(scan_err_render(&ScanErr {
                            offset: rel_offset(e.offset, i),
                            what: e.what,
                        })),
                        line_no + 1,
                    ));
                }
                return Ok((line_no, i));
            }
            Ok((r, j)) => {
                // `0` is the recogniser's "the buffer ended before a newline
                // did": these bytes are an incomplete tail, not a line.
                if j == 0 {
                    return Ok((line_no, i));
                }
                match apply_line(m, st, &r) {
                    Err(e) => return Err(line_err_to_check(e, line_no + 1)),
                    Ok(()) => {}
                }
                if i >= j {
                    const NOPROG: [u32; 33] = [
                        116, 104, 101, 32, 108, 105, 110, 101, 32, 115, 99, 97, 110, 110,
                        101, 114, 32, 109, 97, 100, 101, 32, 110, 111, 32, 112, 114, 111,
                        103, 114, 101, 115, 115
                    ];
                    return Err((
                        core_types::internal(core_types::code_points(&NOPROG)),
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
///
/// **The port drops the interpolated byte count**: `USize.size` is `2^64` on
/// this target, which no `u64` renders, and the differential compares exit
/// codes.  The message names the bound instead of spelling it.
pub fn size_error() -> (CheckError, u64) {
    const M: [u32; 36] = [
        97, 110, 32, 105, 110, 112, 117, 116, 32, 111, 102, 32, 85, 83, 105, 122, 101, 46,
        115, 105, 122, 101, 32, 98, 121, 116, 101, 115, 32, 111, 114, 32, 109, 111, 114, 101
    ];
    (core_types::not_implemented(core_types::code_points(&M)), 0)
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
pub fn parse_bytes<G: Modeller>(
    m: &G,
    b: &[u8],
    in_model: bool,
    census: bool,
) -> Result<ParseResultD, (CheckError, u64)> {
    if (b.len() as u128) >= USIZE_SIZE {
        return Err(size_error());
    }
    let mut st = state_d_init(in_model, census);
    match feed_chunk(m, &mut st, b, 0, 0) {
        Err(e) => Err(e),
        Ok((line_no, tail)) => parse_bytes_final(m, st, b, tail, line_no),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:827-839 parseBytes
/// The cited tail of `parseBytes`: the last line, the one no newline ends.
pub fn parse_bytes_final<G: Modeller>(
    m: &G,
    st: StateD,
    b: &[u8],
    tail: usize,
    line_no: u64,
) -> Result<ParseResultD, (CheckError, u64)> {
    let mut st = st;
    if tail < b.len() {
        match apply_final_line(m, &mut st, b, tail, line_no + 1) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
    }
    Ok(parse_result_of_state(st))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:841-846 parseExportD
/// Wholesale direct parse of a string (the built-in prelude, tests and small
/// inputs): `parse_bytes` of its UTF-8.  The `&str` is con-leche's `String`
/// argument and `as_bytes` its `String.toUTF8`; `prelude_text::PRELUDE_TEXT`
/// is the one caller inside the core, and Aeneas reads a `&str` as `Str` whose
/// `toStr` is the string's UTF-8 bytes (`prelude_text`'s note).
pub fn parse_export_d<G: Modeller>(
    m: &G,
    contents: &str,
    in_model: bool,
    census: bool,
) -> Result<ParseResultD, (CheckError, u64)> {
    parse_bytes(m, contents.as_bytes(), in_model, census)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:848-865 chunkStep
/// **One chunk of the stream, applied** (con-leche task #290): the carried
/// incomplete tail is put in front of the new bytes, every complete line of
/// the buffer is fed, and the new incomplete tail is cut off for the next
/// chunk; `total` counts the bytes read before this chunk, for the size guard.
/// This is the step the streaming reader takes, pure, so that `parse_chunks` —
/// the same step folded over a list of chunks — is exactly what the binary
/// computes and can be compared with the wholesale parse.
pub fn chunk_step<G: Modeller>(
    m: &G,
    st: &mut StateD,
    carry: Vec<u8>,
    line_no: u64,
    total: u64,
    buf0: &[u8],
) -> Result<(Vec<u8>, u64, u64), (CheckError, u64)> {
    if (total as u128) + (buf0.len() as u128) >= USIZE_SIZE {
        return Err(size_error());
    }
    let buf: Vec<u8> = if carry.len() == 0 {
        buf0.to_vec()
    } else {
        let mut v = carry;
        v.extend_from_slice(buf0);
        v
    };
    match feed_chunk(m, st, &buf[..], 0, line_no) {
        Err(e) => Err(e),
        Ok((line_no2, tail)) => Ok((
            buf[tail..].to_vec(),
            line_no2,
            total + (buf0.len() as u64),
        )),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:867-874 chunkFinish
/// The end of the stream: the carried tail, if any, is its last line.
pub fn chunk_finish<G: Modeller>(
    m: &G,
    st: StateD,
    carry: &[u8],
    line_no: u64,
) -> Result<ParseResultD, (CheckError, u64)> {
    let mut st = st;
    if carry.len() == 0 {
        return Ok(parse_result_of_state(st));
    }
    match apply_final_line(m, &mut st, carry, 0, line_no + 1) {
        Err(e) => Err(e),
        Ok(()) => Ok(parse_result_of_state(st)),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:876-880 concatBytes
/// The bytes of a list of chunks, in order: what the chunks a handle hands out
/// add up to.
pub fn concat_bytes(chunks: &Vec<Vec<u8>>) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let n = chunks.len();
    let mut i = 0usize;
    while i < n {
        out.extend_from_slice(&chunks[i][..]);
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/ExportC.lean:882-901 parseChunks
/// **The streaming parse, purely** (con-leche task #290): `chunk_step` folded
/// over a list of chunks, `chunk_finish` at its end — what the driver's reader
/// does with the chunks its handle hands out, minus the reads.  The list is
/// folded whole (task #294): an empty chunk contributes nothing and the fold
/// goes on, so the parse of a list of chunks is the parse of their
/// concatenation, however it was cut.  The reader loop's end-of-input decision
/// — an empty READ is the end of the file — is the reader's own, not the
/// step's, and it stayed in the driver with the reader.
pub fn parse_chunks<G: Modeller>(
    m: &G,
    chunks: &Vec<Vec<u8>>,
    in_model: bool,
    census: bool,
) -> Result<ParseResultD, (CheckError, u64)> {
    let mut st = state_d_init(in_model, census);
    let mut carry: Vec<u8> = Vec::new();
    let mut line_no: u64 = 0;
    let mut total: u64 = 0;
    let n = chunks.len();
    let mut i = 0usize;
    while i < n {
        match chunk_step(m, &mut st, carry, line_no, total, &chunks[i][..]) {
            Err(e) => return Err(e),
            Ok((c2, l, t)) => {
                carry = c2;
                line_no = l;
                total = t;
            }
        }
        i += 1;
    }
    chunk_finish(m, st, &carry[..], line_no)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A modeller that declines every block with one fixed sentence.  The
    /// real one is `crates/con-ron/src/in_model/`, in the other crate, which
    /// the core cannot call: the tests that need it are the differential's
    /// and the driver's.
    struct NoModel;

    impl Modeller for NoModel {
        fn generate(&self, _ctx: &ModelCtx, _b: &BlockRec) -> Result<Vec<Declaration>, Vec<u32>> {
            Err(cp("no modeller in the core"))
        }
    }

    fn cp(t: &str) -> Vec<u32> {
        t.chars().map(|c| c as u32).collect()
    }

    fn parse(text: &str) -> Result<ParseResultD, (CheckError, u64)> {
        parse_export_d(&NoModel, text, true, false)
    }

    /// A `Name`, rendered: `text::name_str` as a Rust string.
    fn nm(n: &Name) -> String {
        text::name_str(n)
            .iter()
            .filter_map(|c| char::from_u32(*c))
            .collect()
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
            Declaration::AxiomDecl(cv) => assert_eq!(nm(&cv.name), "A"),
            _ => panic!("not an axiom"),
        }
    }

    /// An undefined index is a parse error naming the line, not a panic.
    #[test]
    fn an_undefined_index_is_a_parse_error() {
        let s = "{\"ie\":0,\"sort\":7}\n";
        match parse(s) {
            Err((CheckError::Internal(m), line)) => {
                assert_eq!(line, 1);
                let m: String = m.iter().filter_map(|c| char::from_u32(*c)).collect();
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
                Err((CheckError::Internal(m), 2)) => {
                    let m: String = m.iter().filter_map(|c| char::from_u32(*c)).collect();
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
                assert_eq!(nm(&cv.name), "Whatever");
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
            Err((CheckError::Internal(m), 3)) => {
                let m: String = m.iter().filter_map(|c| char::from_u32(*c)).collect();
                assert_eq!(m, "unknown quotient kind 'nope'");
            }
            other => panic!("{}", shown(other)),
        }
    }

    /// A mutual block reaches the modeller, and the modeller's decline is the
    /// run's, naming the block AND the class.  With the REAL modeller the
    /// class is the generator's own shape check ("recursor count differs from
    /// member count" on this block, which has no recursors); here it is the
    /// test modeller's sentence, so what this states is the seam: `wants`
    /// fires on two types, `generate` is called, and its message reaches the
    /// verdict with the block's name in front of it.
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
                assert!(m.contains("no modeller in the core"), "{}", m);
            }
            other => panic!("{}", shown(other)),
        }
        // with the modeller off the block is pushed bare, as in con-leche
        let r = parse_export_d(&NoModel, s, false, false)
            .unwrap_or_else(|e| panic!("{}", show(&e)));
        assert_eq!(r.decls.len(), 1);
        // and in census mode it is reported and the parse continues
        let r = parse_export_d(&NoModel, s, true, true)
            .unwrap_or_else(|e| panic!("{}", show(&e)));
        assert_eq!(r.in_model_declined.len(), 1);
        assert_eq!(nm(&r.in_model_declined[0].0), "T");
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
    /// misreported.  An empty chunk anywhere contributes nothing (con-leche
    /// task #294).  The READER's loop over the same step is the driver's and
    /// is tested there.
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
            let cs: Vec<Vec<u8>> = s
                .as_bytes()
                .chunks(chunk)
                .map(|c| c.to_vec())
                .collect::<Vec<_>>();
            let r = parse_chunks(&NoModel, &cs, true, false)
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
        let r = parse_chunks(&NoModel, &cs, true, false)
            .unwrap_or_else(|e| panic!("{}", show(&e)));
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

    /// The size guard's message is a decline at line 0 (`sizeError`).
    #[test]
    fn the_size_guard_declines_at_line_zero() {
        let (e, line) = size_error();
        assert_eq!(line, 0);
        match e {
            CheckError::NotImplemented(w) => {
                let m: String = w.iter().filter_map(|c| char::from_u32(*c)).collect();
                assert!(m.starts_with("an input of"), "{}", m);
            }
            _ => panic!("the size guard is not a decline"),
        }
    }
}

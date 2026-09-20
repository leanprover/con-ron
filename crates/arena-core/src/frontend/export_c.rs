//! `proof/ConRon/Arena/Frontend/ExportC.lean` — **the export parser INTO THE
//! STORE** (DESIGN.md §8.3 "Parsing", task #97 P4e part 1).
//!
//! con-leche's `ConLeche/Frontend/ExportC.lean`, clause for clause, with one
//! change: **no `Expr` is ever built**.  Where `con_ron_core::frontend::
//! export_c` keeps `IdTable<Name>` / `IdTable<Level>` / `IdTable<Expr>` of
//! *values*, this keeps `IdTable<NIdx>` / `IdTable<LIdx>` / `IdTable<EIdx>` of
//! **handles** into the persistent tier of the `EStore`; a table hit is the
//! same shared node it is there, by handle rather than by `ron::ptr` bump, so
//! the export's own sharing is preserved exactly (DESIGN.md §8.3,
//! con-leche's lesson 25).
//!
//! The scanner is NOT twinned and the prelude text is reused — see this
//! directory's `mod.rs`.  `scan_line_fwd`, `newline_from` and `IdTable` are
//! `con_ron_core::frontend::{scan_fast, scan_types}`'s, at the three handle
//! kinds.
//!
//! **Two non-decoding steps are stubs in part 1**, both of them the twin's
//! stubs and both listed as task #97e part 2: the projection-function rewrite
//! ([`proj_rewrite_d`], [`note_proj_iota`], [`register_proj_owners`]), which
//! needs the `ExprOps` twins of `ConLeche/Frontend/ProjRec.lean`, and the
//! in-process modeller, which sits behind the one-method
//! [`Modeller`](super::types::Modeller) seam.  With `proj_owners` and
//! `proj_levels` never written, the rewrite's `None` is the *same* answer
//! con-leche gives on those streams: its own `st.projOwners[T]?` misses on
//! every record too.
//!
//! ## Deviations
//!
//! * **`AM (StateD ⊕ RecordVerdict)` is `Result<(), LineErr>` over a
//!   `&mut EStore` and a `&mut StateD`** — one error channel with two arms
//!   instead of a monad over a sum, and both states threaded by mutable
//!   reference instead of returned.  con-leche threads `StateD` linearly for
//!   the reason Rust's `&mut` gives for free (its task-#78 note: a handler
//!   that closes over the state holds it at RC 2 and every insert inside
//!   copies it).  [`LineErr`]'s message arm carries a whole `CheckError` where
//!   con-ron-core's carries a `Vec<u32>`: `EStore::intern` declines with
//!   `Native` at the `2^27` cap (DESIGN.md §8.3) and that kind has to reach
//!   the exit code.
//! * **every message is a `Vec<u32>` of code points** (DESIGN.md §3.3) built
//!   from a function-local `const M: [u32; N]` and `core_types::code_points`,
//!   with `text::cat`/`cat3`, `text::name_str` and `text::u64_str` for what
//!   con-leche's `s!"…"` interpolates.  `size_error` drops its interpolated
//!   byte count, as con-ron-core's does and for the same reason.  A `NIdx` in
//!   a message is READ BACK (`env::read_name`) and then rendered, which is the
//!   twin's `← readName` exactly.
//! * **`Nat` is `u64`** for every stream index and count (DESIGN.md §3.3),
//!   and con-leche's truncating `Nat` subtraction is [`sat_sub`].
//! * **the subset's helpers.**  §3.4 has no closures, no iterator adapters and
//!   no `?`, and Aeneas duplicates the code AFTER a loop into every loop exit,
//!   so a long function with loops in the middle of it is split: each loop is
//!   its own function whose tail is one line, and the caller is a chain of
//!   `match`es.  `validate_ind_d` and `install_ind_d` are the two that needed
//!   it, exactly as in con-ron-core; every piece cites the whole of the
//!   function it came out of.
//! * **the reader is not here.**  `parseExportHandleD`/`parseExportStreamD`
//!   are `IO`, which DESIGN.md §8.4 forbids in (B) and which the twin does not
//!   port either; the driver owns the reads and calls [`chunk_step`] and
//!   [`chunk_finish`] in the loop [`parse_chunks`] spells out purely.

use crate::arena::env;
use crate::arena::env::{
    i_constant_info_name, i_constant_val_dup, i_declaration_names, i_rec_rule_parsed,
    nidx_vec_dup, IConstantInfo, IConstantVal, IDeclaration, IRecRule,
};
use crate::arena::handle::{EIdx, LIdx, NIdx};
use crate::arena::store::{ENodeView, EStore, LNodeView, NNodeView};
use crate::frontend::types::{
    hint_height, record_verdict_to_error, wants, BlockRec, ConstTable, MIndCtorRec,
    MIndRecRec, MIndTypeRec, ModelCtx, Modeller, ProjRecOwner, RecordVerdict,
};
use con_ron_core::frontend::nat_decimal;
use con_ron_core::frontend::scan_fast;
use con_ron_core::frontend::scan_types;
use con_ron_core::frontend::scan_types::{
    id_table_get, id_table_insert, id_table_singleton, scan_err_render, CVRec, DeclRec,
    ErrTag, ExprRec, HintsRec, IdTable, IndCtorRec, IndRecRec, IndTypeRec, LevelRec, LineRec,
    NameRec, PwRec, RuleRec, ScanErr,
};
use con_ron_core::frontend::text;
use con_ron_core::kernel::core_types;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env::{QuotKind, ReducibilityHint};
use con_ron_core::kernel::expr;
use con_ron_core::kernel::level;
use con_ron_core::kernel::prop_when;
use con_ron_core::kernel::prop_when::PropWhen;
use con_ron_core::ron::hashmap::{Dup, Eq2, HashMap};

// ---------------------------------------------------------------------------
// The error channel (`Types.lean`'s note, `ExportC.lean`'s `fail`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/Export.lean:117 M
/// The two ways applying one line can fail: a checker error (the twin's
/// `fail`, which is `AM`'s `throw`) or a record verdict (the twin's
/// `StateD ⊕ RecordVerdict`'s right summand).  Merging them into one `Result`
/// is con-ron-core's deviation, kept; the two arms are told apart again at
/// [`line_err_to_check`], where the line number is in hand.
pub enum LineErr {
    Err(CheckError),
    Verdict(RecordVerdict),
}

/// con-leche: ConLeche/Kernel/Core.lean:47-66 CheckError
/// Lean twin: `proof/ConRon/Arena/Monad.lean:125-126 fail` — the one failure
/// primitive, lifted into the parse's merged channel.
pub fn fail<T>(e: CheckError) -> Result<T, LineErr> {
    Err(LineErr::Err(e))
}

/// con-leche: none — `fail (.internal …)`, the twin's spelling of con-leche's `throw` in `M`
/// An internal parse failure at a code-point message.
pub fn merr<T>(msg: Vec<u32>) -> Result<T, LineErr> {
    Err(LineErr::Err(core_types::internal(msg)))
}

/// con-leche: none — `.inr (.declined …)`, the decline half of `StateD ⊕ RecordVerdict`
pub fn declined<T>(what: Vec<u32>) -> Result<T, LineErr> {
    Err(LineErr::Verdict(RecordVerdict::Declined(what)))
}

/// con-leche: none — `.inr (.invalid …)`, the reject half of `StateD ⊕ RecordVerdict`
pub fn invalid<T>(what: Vec<u32>) -> Result<T, LineErr> {
    Err(LineErr::Verdict(RecordVerdict::Invalid(what)))
}

/// con-leche: none — the `AM`/verdict pair resolved against the line it was read at
/// The `applyFinalLine`/`feedChunk` arms that turn a failure into
/// `(e, line)` and a record verdict into `(v.toError, line)`.
pub fn line_err_to_check(e: LineErr, line_no: u64) -> (CheckError, u64) {
    match e {
        LineErr::Err(e) => (e, line_no),
        LineErr::Verdict(v) => (record_verdict_to_error(v), line_no),
    }
}

/// con-leche: none — Lean's `s!"{b}"` on a `Bool`; one recursor message prints the flag the record declares
pub fn bool_str(b: bool) -> Vec<u32> {
    if b {
        const T_TRUE: [u32; 4] = [
            116, 114, 117, 101,
        ];
        core_types::code_points(&T_TRUE)
    } else {
        const F_FALSE: [u32; 5] = [
            102, 97, 108, 115, 101,
        ];
        core_types::code_points(&F_FALSE)
    }
}

/// con-leche: none — `x - y` on a `Nat`, which truncates at zero; Rust's `u64` subtraction does not
/// Two message positions and one offset read it.
pub fn sat_sub(a: u64, b: u64) -> u64 {
    if a >= b {
        a - b
    } else {
        0
    }
}

/// con-leche: none — `sat_sub` on the scanner's `usize` offsets
/// A scan failure inside a line is reported at its offset IN the line.
pub fn rel_offset(off: usize, i: usize) -> usize {
    if off >= i {
        off - i
    } else {
        0
    }
}

/// con-leche: none — a scan failure as the checker's error, at its offset in the line
/// con-leche renders *every* scan error as `.internal`; the port has one tag
/// con-leche has not got (`ErrTag::IndexOverflow`, `scan_types`' deviation 1),
/// and under the full-outcome ruling that one is `Native` — the port's own
/// decline, about which a refinement lemma claims nothing.  Found by a proof
/// at task #87 and kept here unchanged.
pub fn scan_err_to_check(e: &ScanErr) -> CheckError {
    match e.what {
        ErrTag::IndexOverflow => core_types::native(scan_err_render(e)),
        _ => core_types::internal(scan_err_render(e)),
    }
}

// ---------------------------------------------------------------------------
// Fuel (`ExportC.lean:72-84` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — the fuel every DAG walk of the frontend is run at
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:82-84 storeFuel` — the
/// store's node count, which bounds the length of any path through it because
/// a child is interned before its parent.  con-leche's walks are structural on
/// `Expr` and need none.
pub fn store_fuel(ar: &EStore) -> u64 {
    ar.node_count() as u64 + 1
}

// ---------------------------------------------------------------------------
// The direct parse state (`ExportC.lean:88-128` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ExportC.lean:78-134 StateD
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:95-128 StateD` — the
/// direct parse state: stream-index-keyed tables of HANDLES (a table hit is
/// the same shared node, named by its handle) and the parsed declarations as
/// `IDeclaration`.
///
/// `names` and `levels` have no default: index 0 of each is the format's
/// implicit `Name.anonymous` / `Level.zero`, and over handles that means the
/// handle those two nodes were interned at, which only [`state_d_init`] can
/// know.
pub struct StateD {
    pub names: IdTable<NIdx>,
    pub levels: IdTable<LIdx>,
    pub exprs: IdTable<EIdx>,
    pub decls: Vec<IDeclaration>,
    /// structure-like owners the projection rewrite serves, by type name
    pub proj_owners: HashMap<NIdx, ProjRecOwner>,
    /// field sorts, by artifact iota name `T._model.proj_i.iota`
    pub proj_levels: HashMap<NIdx, LIdx>,
    /// projection functions rewritten so far (names, for the driver's trace)
    pub proj_rewrites: Vec<NIdx>,
    /// the declared types of every declaration pushed so far, by name
    pub const_types: ConstTable,
    /// the definitional heights of the definitions pushed so far
    pub heights: HashMap<NIdx, u64>,
    /// in-process modelling of mutual/nested blocks is on
    pub in_model: bool,
    /// the blocks modelled in-process, in stream order
    pub in_modelled: Vec<NIdx>,
    /// how many records the in-process modeller GENERATED and pushed
    pub gen_records: u64,
    /// each generated record's leading name ↦ the block it models
    pub gen_owner: HashMap<NIdx, NIdx>,
    /// per modelled block, its ordinal among the stream's `inductive` records
    /// and the generated records.  **The twin has this field and
    /// `con_ron_core::frontend::export_c` does not** (it feeds con-leche's
    /// `CON_LECHE_INMODEL_DUMP`, whose writer con-ron has no port of); the
    /// lockstep rule of DESIGN.md §8.6 is clause-for-clause with the twin, so
    /// it is here, at one record copy per generated record where Lean shares.
    pub in_model_gen: Vec<(u64, Vec<IDeclaration>)>,
    /// the number of `inductive` records seen so far
    pub ind_count: u64,
    /// the parsed inductive blocks, by member type name
    pub ind_blocks: HashMap<NIdx, BlockRec>,
    /// CENSUS mode: a generator decline is recorded and the block pushed bare
    pub in_model_census: bool,
    /// the census's declines: block name and reason
    pub in_model_declined: Vec<(NIdx, Vec<u32>)>,
}

/// con-leche: ConLeche/Frontend/ExportC.lean:755-758 StateD.init
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:686-690 StateD.init` —
/// the initial parse state.  Over handles it INTERNS: index 0 of the name
/// table is the format's implicit `Name.anonymous` and index 0 of the level
/// table its `Level.zero`, in the PERSISTENT tier, which is the tier the whole
/// parse appends to (`scratch_on` is `false` on `EStore::empty` and the parse
/// never enables the scratch one).
pub fn state_d_init(
    ar: &mut EStore,
    in_model: bool,
    census: bool,
) -> Result<StateD, CheckError> {
    let n0 = match ar.intern_name(NNodeView::Anonymous) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    let l0 = match ar.intern_level(LNodeView::Zero) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    Ok(StateD {
        names: id_table_singleton(n0),
        levels: id_table_singleton(l0),
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
        in_model_gen: Vec::new(),
        ind_count: 0,
        ind_blocks: HashMap::new(),
        in_model_census: census,
        in_model_declined: Vec::new(),
    })
}

/// con-leche: ConLeche/Frontend/ExportC.lean:603-607 _
/// The cited `let ctx : InModel.Ctx := ⟨…, …, …⟩`: the three tables the
/// modeller reads, borrowed off the state (`types::ModelCtx`'s deviation).
pub fn state_model_ctx<'a>(st: &'a StateD) -> ModelCtx<'a> {
    ModelCtx {
        tbl: &st.const_types,
        heights: &st.heights,
        blocks: &st.ind_blocks,
    }
}

// ---------------------------------------------------------------------------
// Booking a pushed record (`ExportC.lean:140-161` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ExportC.lean:135-153 noteDecl
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:140-156 noteDecl` —
/// the constants one pushed declaration declares, with their level parameters,
/// declared types and (for a definition) definitional height: the cited `cvs`.
///
/// **The `.basisDecl` arm fails loudly** where con-leche reads the pinned
/// block's constants out of `BasisKind.decls`.  No frontend function produces
/// a `BasisDecl` (it is the fold's own record for "install the pinned block"),
/// so the arm is unreachable from the parse; the pinned tables it would read
/// are P2d's, and a loud `internal` beats a silent empty list the day someone
/// makes it reachable.
pub fn note_decl_entries(
    ar: &mut EStore,
    d: &IDeclaration,
) -> Result<Vec<(NIdx, Vec<NIdx>, EIdx, Option<u64>)>, LineErr> {
    match d {
        IDeclaration::AxiomDecl(cv) => Ok(note_one(cv, None)),
        IDeclaration::DefnDecl(cv, _, h) => Ok(note_one(cv, Some(hint_height(h)))),
        IDeclaration::ThmDecl(cv, _) => Ok(note_one(cv, None)),
        IDeclaration::OpaqueDecl(cv, _) => Ok(note_one(cv, None)),
        IDeclaration::QuotDecl(_, cv) => Ok(note_one(cv, None)),
        IDeclaration::BasisDecl(_) => {
            const M_BASISDECL: [u32; 44] = [
                110, 111, 116, 101, 68, 101, 99, 108, 58, 32, 97, 32, 98, 97, 115, 105, 115,
                68, 101, 99, 108, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 112, 97, 114,
                115, 101, 114, 32, 114, 101, 99, 111, 114, 100,
            ];
            merr(core_types::code_points(&M_BASISDECL))
        }
        IDeclaration::IndDecl(bl, _) => note_block(ar, bl, 0, Vec::new()),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:135-153 noteDecl
/// `note_decl_entries`' one-constant case (con-leche's `[(cv, h)]`), which
/// §3.4 spells as a function rather than a `let one := fun …`.
pub fn note_one(
    cv: &IConstantVal,
    h: Option<u64>,
) -> Vec<(NIdx, Vec<NIdx>, EIdx, Option<u64>)> {
    let mut out: Vec<(NIdx, Vec<NIdx>, EIdx, Option<u64>)> = Vec::with_capacity(1);
    out.push((
        cv.name.dup2(),
        nidx_vec_dup(&cv.level_params),
        cv.ty.dup2(),
        h,
    ));
    out
}

/// con-leche: ConLeche/Frontend/ExportC.lean:135-153 noteDecl
/// `note_decl_entries`' block case (con-leche's `block.mapM`), as an index
/// loop with the accumulator passed by value.  It is `mapM` and not `map` in
/// the twin because `toConstantVal` interns a `.projInfo`'s dummy type — which
/// no parsed block is.
pub fn note_block(
    ar: &mut EStore,
    bl: &Vec<IConstantInfo>,
    i: usize,
    out: Vec<(NIdx, Vec<NIdx>, EIdx, Option<u64>)>,
) -> Result<Vec<(NIdx, Vec<NIdx>, EIdx, Option<u64>)>, LineErr> {
    let mut out = out;
    let n = bl.len();
    let mut k = i;
    while k < n {
        match env::i_constant_info_to_constant_val(ar, &bl[k]) {
            Err(e) => return fail(e),
            Ok(cv) => out.push((
                cv.name.dup2(),
                nidx_vec_dup(&cv.level_params),
                cv.ty.dup2(),
                None,
            )),
        }
        k += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:135-153 noteDecl
/// The insert half of `noteDecl`: the cited `cvs.foldl` over `constTypes` and
/// `heights`.  The twin's detach-before-update (DESIGN.md §8.4 lesson 14) has
/// no Rust counterpart — `&mut` **is** the unique reference the detaching
/// exists to manufacture.
pub fn note_entries(st: &mut StateD, es: &Vec<(NIdx, Vec<NIdx>, EIdx, Option<u64>)>) {
    let n = es.len();
    let mut i = 0usize;
    while i < n {
        let e = &es[i];
        match e.3 {
            None => {}
            Some(hv) => {
                st.heights.insert(e.0.dup2(), hv);
            }
        }
        st.const_types
            .insert(e.0.dup2(), (nidx_vec_dup(&e.1), e.2.dup2()));
        i += 1;
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:135-153 noteDecl
/// Record a pushed declaration's constants in the declaration table.
pub fn note_decl(ar: &mut EStore, st: &mut StateD, d: &IDeclaration) -> Result<(), LineErr> {
    match note_decl_entries(ar, d) {
        Err(e) => Err(e),
        Ok(es) => {
            note_entries(st, &es);
            Ok(())
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:155-162 pushDecl
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:160-161 pushDecl` —
/// one parsed record, appended: the decoder keeps the file's records in the
/// file's order.
pub fn push_decl(
    ar: &mut EStore,
    st: &mut StateD,
    d: IDeclaration,
) -> Result<(), LineErr> {
    match note_decl(ar, st, &d) {
        Err(e) => Err(e),
        Ok(()) => {
            st.decls.push(d);
            Ok(())
        }
    }
}

// ---------------------------------------------------------------------------
// The table reads (`ExportC.lean:165-198` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ExportC.lean:164-167 StateD.name
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:165-168 StateD.name`
pub fn st_name(st: &StateD, i: u64) -> Result<NIdx, LineErr> {
    match id_table_get(&st.names, i) {
        Some(n) => Ok(n.dup2()),
        None => {
            const M_UNDEF_NAME: [u32; 21] = [
                117, 110, 100, 101, 102, 105, 110, 101, 100, 32, 110, 97, 109, 101, 32, 105,
                110, 100, 101, 120, 32,
            ];
            merr(text::cat(
                core_types::code_points(&M_UNDEF_NAME),
                &text::u64_str(i),
            ))
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:169-172 StateD.level
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:172-175 StateD.level`
pub fn st_level(st: &StateD, i: u64) -> Result<LIdx, LineErr> {
    match id_table_get(&st.levels, i) {
        Some(l) => Ok(l.dup2()),
        None => {
            const M_UNDEF_LEVEL: [u32; 22] = [
                117, 110, 100, 101, 102, 105, 110, 101, 100, 32, 108, 101, 118, 101, 108,
                32, 105, 110, 100, 101, 120, 32,
            ];
            merr(text::cat(
                core_types::code_points(&M_UNDEF_LEVEL),
                &text::u64_str(i),
            ))
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:174-177 StateD.expr
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:179-182 StateD.expr`
pub fn st_expr(st: &StateD, i: u64) -> Result<EIdx, LineErr> {
    match id_table_get(&st.exprs, i) {
        Some(e) => Ok(e.dup2()),
        None => {
            const M_UNDEF_EXPR: [u32; 21] = [
                117, 110, 100, 101, 102, 105, 110, 101, 100, 32, 101, 120, 112, 114, 32,
                105, 110, 100, 101, 120, 32,
            ];
            merr(text::cat(
                core_types::code_points(&M_UNDEF_EXPR),
                &text::u64_str(i),
            ))
        }
    }
}

/// con-leche: none — `is.mapM st.name`, which §3.4 forbids as an iterator adapter
/// A name-index list resolved, as an index loop whose tail is one line (the
/// parse's level-parameter and constructor lists).
pub fn st_names(st: &StateD, is: &Vec<u64>) -> Result<Vec<NIdx>, LineErr> {
    let mut out: Vec<NIdx> = Vec::with_capacity(is.len());
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

/// con-leche: none — `us.mapM st.level` (see `st_names`)
pub fn st_levels(st: &StateD, is: &Vec<u64>) -> Result<Vec<LIdx>, LineErr> {
    let mut out: Vec<LIdx> = Vec::with_capacity(is.len());
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
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:187-188 getDeclD` —
/// declaration-level expression lookup: the table read.  (The frontend
/// tree-size budget that used to sit here was retired at con-leche's task
/// #215.)
pub fn get_decl_d(st: &StateD, i: u64) -> Result<EIdx, LineErr> {
    st_expr(st, i)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:191-194 parsePwD
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:194-198 parsePwD` —
/// the `pw` datum over the direct name table.  `PropWhen` holds `Name`s — task
/// #97a's store already carries `BinderMeta`, hence `PropWhen`, inside its
/// binder node — so the resolved handles are READ BACK to names here, which is
/// `denoteN` itself (DESIGN.md §8.3 lesson 4's move, at the name store).
pub fn parse_pw_d(ar: &EStore, st: &StateD, r: &PwRec) -> Result<PropWhen, LineErr> {
    match r {
        PwRec::Never => Ok(prop_when::never()),
        PwRec::IfAllZero(ns) => match st_names(st, ns) {
            Err(e) => Err(e),
            Ok(hs) => match env::read_names(ar, &hs) {
                Err(e) => fail(e),
                Ok(out) => Ok(prop_when::if_all_zero(out)),
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The rebinding test (`ExportC.lean:202-222` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ExportC.lean:207-209 reboundError
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:204-205 reboundError`
/// — the rebinding error, named once.  `what` is one of three
/// `const [u32; N]` literals at the call sites, con-leche's
/// `"name"`/`"level"`/`"expression"`.
pub fn rebound_error(what: &[u32], i: u64) -> Vec<u32> {
    const A_IDX: [u32; 7] = [
        32, 105, 110, 100, 101, 120, 32,
    ];
    const B_BOUND: [u32; 17] = [
        32, 105, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 98, 111, 117, 110, 100,
    ];
    let s = text::cat3(
        core_types::code_points(what),
        &core_types::code_points(&A_IDX),
        &text::u64_str(i),
    );
    text::cat(s, &core_types::code_points(&B_BOUND))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:211-220 StateD.freshName
/// con-leche: ConLeche/Frontend/Scan/Types.lean:363-372 IdTable.bound
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:211-212 StateD.freshName`
/// — every table entry is bound once: a line that binds an index a previous
/// line already bound is a parse error.  `scan_types` has no `bound`, so the
/// test reads the table instead (`IdTable.bound_eq`, which con-leche proves
/// beside the definition).  The state is BORROWED for the reason the twin's
/// `@& StateD` and `@[noinline]` exist: con-leche measured a 17 % parse-phase
/// instruction increase when an owned read let the compiler deconstruct the
/// state before the test.
pub fn st_fresh_name(st: &StateD, i: u64) -> Result<(), LineErr> {
    match id_table_get(&st.names, i) {
        Some(_) => {
            const W_NAME: [u32; 4] = [
                110, 97, 109, 101,
            ];
            merr(rebound_error(&W_NAME, i))
        }
        None => Ok(()),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:221-222 StateD.freshLevel
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:216-217 StateD.freshLevel`
pub fn st_fresh_level(st: &StateD, i: u64) -> Result<(), LineErr> {
    match id_table_get(&st.levels, i) {
        Some(_) => {
            const W_LEVEL: [u32; 5] = [
                108, 101, 118, 101, 108,
            ];
            merr(rebound_error(&W_LEVEL, i))
        }
        None => Ok(()),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:223-224 StateD.freshExpr
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:221-222 StateD.freshExpr`
pub fn st_fresh_expr(st: &StateD, i: u64) -> Result<(), LineErr> {
    match id_table_get(&st.exprs, i) {
        Some(_) => {
            const W_EXPR: [u32; 10] = [
                101, 120, 112, 114, 101, 115, 115, 105, 111, 110,
            ];
            merr(rebound_error(&W_EXPR, i))
        }
        None => Ok(()),
    }
}

// ---------------------------------------------------------------------------
// Table entries (`ExportC.lean:228-282` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ExportC.lean:228-237 parseNameEntryD
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:228-238 parseNameEntryD`
/// — a name-table entry: the node is INTERNED and the table records its
/// handle.  The parent index is resolved before the freshness test, as in the
/// cited `do` block.
pub fn parse_name_entry_d(
    ar: &mut EStore,
    st: &mut StateD,
    i: u64,
    r: &NameRec,
) -> Result<(), LineErr> {
    let v = match r {
        NameRec::Str(pre, s) => match st_name(st, *pre) {
            Err(e) => return Err(e),
            Ok(p) => match st_fresh_name(st, i) {
                Err(e) => return Err(e),
                Ok(()) => NNodeView::Str(p, core_types::code_points(s)),
            },
        },
        NameRec::Num(pre, k) => match st_name(st, *pre) {
            Err(e) => return Err(e),
            Ok(p) => match st_fresh_name(st, i) {
                Err(e) => return Err(e),
                Ok(()) => NNodeView::Num(p, *k),
            },
        },
    };
    match ar.intern_name(v) {
        Err(e) => fail(e),
        Ok(h) => {
            id_table_insert(&mut st.names, i, h);
            Ok(())
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:239-247 parseLevelEntryD
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:242-249 parseLevelEntryD`
/// — a level-table entry, interned.
pub fn parse_level_entry_d(
    ar: &mut EStore,
    st: &mut StateD,
    i: u64,
    r: &LevelRec,
) -> Result<(), LineErr> {
    match st_fresh_level(st, i) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    let v = match parse_level_rec_d(st, r) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    match ar.intern_level(v) {
        Err(e) => fail(e),
        Ok(h) => {
            id_table_insert(&mut st.levels, i, h);
            Ok(())
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:239-247 parseLevelEntryD
/// The node-view half of `parse_level_entry_d`: the view built from the
/// children's table handles.  Split out so the entry point is a `match` chain
/// with no `?` (§3.4), as con-ron-core's `parse_level_rec_d` is.
pub fn parse_level_rec_d(st: &StateD, r: &LevelRec) -> Result<LNodeView, LineErr> {
    match r {
        LevelRec::Succ(u) => match st_level(st, *u) {
            Err(e) => Err(e),
            Ok(a) => Ok(LNodeView::Succ(a)),
        },
        LevelRec::Max(a, b) => match st_level(st, *a) {
            Err(e) => Err(e),
            Ok(x) => match st_level(st, *b) {
                Err(e) => Err(e),
                Ok(y) => Ok(LNodeView::Max(x, y)),
            },
        },
        LevelRec::Imax(a, b) => match st_level(st, *a) {
            Err(e) => Err(e),
            Ok(x) => match st_level(st, *b) {
                Err(e) => Err(e),
                Ok(y) => Ok(LNodeView::Imax(x, y)),
            },
        },
        LevelRec::Param(n) => match st_name(st, *n) {
            Err(e) => Err(e),
            Ok(p) => Ok(LNodeView::Param(p)),
        },
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:249-279 parseExprEntryD
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:261-282 parseExprEntryD`
/// — an expression-table entry: the node is interned from the children's
/// HANDLES, and the packed derived word `Expr.data` computes is computed by
/// `intern` out of the children's derived columns (task #97a's `der_of_view`).
/// Binder names are display data the official kernel's equality and hash
/// ignore; ours are anonymous on every parsed binder, so handle equality is
/// α-equivalence downstream, exactly as `==` is in con-leche.
pub fn parse_expr_entry_d(
    ar: &mut EStore,
    st: &mut StateD,
    i: u64,
    r: &ExprRec,
) -> Result<(), LineErr> {
    match st_fresh_expr(st, i) {
        Err(e) => return Err(e),
        Ok(()) => {}
    }
    match parse_expr_rec_d(ar, st, r) {
        Err(e) => Err(e),
        Ok(h) => {
            id_table_insert(&mut st.exprs, i, h);
            Ok(())
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:249-279 parseExprEntryD
/// The value half of `parse_expr_entry_d` (see `parse_level_rec_d`), which
/// here INTERNS rather than returning a view: a `const` node's universe
/// arguments are one `LsIdx` of their own (`intern_levels`), which is what
/// keeps the `const` node two words (DESIGN.md §8.3), so the arm cannot hand
/// a single view back.
pub fn parse_expr_rec_d(
    ar: &mut EStore,
    st: &StateD,
    r: &ExprRec,
) -> Result<EIdx, LineErr> {
    match r {
        ExprRec::Bvar(k) => match ar.intern(ENodeView::BVar(*k)) {
            Err(e) => fail(e),
            Ok(h) => Ok(h),
        },
        ExprRec::Sort(u) => match st_level(st, *u) {
            Err(e) => Err(e),
            Ok(l) => match ar.intern(ENodeView::Sort(l)) {
                Err(e) => fail(e),
                Ok(h) => Ok(h),
            },
        },
        ExprRec::Const(n, us) => match st_name(st, *n) {
            Err(e) => Err(e),
            Ok(nm) => match st_levels(st, us) {
                Err(e) => Err(e),
                Ok(ls) => match ar.intern_levels(ls) {
                    Err(e) => fail(e),
                    Ok(lsh) => match ar.intern(ENodeView::Const(nm, lsh)) {
                        Err(e) => fail(e),
                        Ok(h) => Ok(h),
                    },
                },
            },
        },
        ExprRec::App(f, a) => match st_expr(st, *f) {
            Err(e) => Err(e),
            Ok(x) => match st_expr(st, *a) {
                Err(e) => Err(e),
                Ok(y) => match ar.intern(ENodeView::App(x, y)) {
                    Err(e) => fail(e),
                    Ok(h) => Ok(h),
                },
            },
        },
        ExprRec::Lam(ty, bd, pw) => match st_expr(st, *ty) {
            Err(e) => Err(e),
            Ok(t) => match st_expr(st, *bd) {
                Err(e) => Err(e),
                Ok(b) => match parse_pw_d(ar, st, pw) {
                    Err(e) => Err(e),
                    Ok(p) => match ar.intern(ENodeView::Lam(t, b, expr::binder_meta(p))) {
                        Err(e) => fail(e),
                        Ok(h) => Ok(h),
                    },
                },
            },
        },
        ExprRec::ForallE(ty, bd, pw) => match st_expr(st, *ty) {
            Err(e) => Err(e),
            Ok(t) => match st_expr(st, *bd) {
                Err(e) => Err(e),
                Ok(b) => match parse_pw_d(ar, st, pw) {
                    Err(e) => Err(e),
                    Ok(p) => {
                        match ar.intern(ENodeView::ForallE(t, b, expr::binder_meta(p))) {
                            Err(e) => fail(e),
                            Ok(h) => Ok(h),
                        }
                    }
                },
            },
        },
        ExprRec::LetE(ty, vl, bd) => match st_expr(st, *ty) {
            Err(e) => Err(e),
            Ok(t) => match st_expr(st, *vl) {
                Err(e) => Err(e),
                Ok(v) => match st_expr(st, *bd) {
                    Err(e) => Err(e),
                    Ok(b) => match ar.intern(ENodeView::LetE(t, v, b)) {
                        Err(e) => fail(e),
                        Ok(h) => Ok(h),
                    },
                },
            },
        },
        ExprRec::Proj(tn, ix, s) => match st_name(st, *tn) {
            Err(e) => Err(e),
            Ok(t) => match st_expr(st, *s) {
                Err(e) => Err(e),
                Ok(x) => match ar.intern(ENodeView::Proj(t, *ix, x)) {
                    Err(e) => fail(e),
                    Ok(h) => Ok(h),
                },
            },
        },
        ExprRec::NatVal(digits) => match nat_decimal::from_decimal(digits) {
            None => merr(scan_types::err_tag_describe(&ErrTag::BadNatVal)),
            Some(n) => match ar.intern(ENodeView::Lit(expr::literal_nat(n))) {
                Err(e) => fail(e),
                Ok(h) => Ok(h),
            },
        },
        ExprRec::StrVal(s) => {
            let l = expr::literal_str(core_types::code_points(s));
            match ar.intern(ENodeView::Lit(l)) {
                Err(e) => fail(e),
                Ok(h) => Ok(h),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Declaration records (`ExportC.lean:288-404` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ExportC.lean:283-289 parseCVD
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:288-293 parseCVD` — a
/// declaration's common data; the type stays a handle.  Pure in the store: it
/// is three table reads and nothing is interned.
pub fn parse_cv_d(st: &StateD, cv: &CVRec) -> Result<IConstantVal, LineErr> {
    match st_name(st, cv.name) {
        Err(e) => Err(e),
        Ok(nm) => match get_decl_d(st, cv.ty) {
            Err(e) => Err(e),
            Ok(ty) => match st_names(st, &cv.level_params) {
                Err(e) => Err(e),
                Ok(lps) => Ok(IConstantVal {
                    name: nm,
                    level_params: lps,
                    ty,
                }),
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:291-302 projRewriteD
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:307-309 projRewriteD`
/// — the projection-function rewrite at a definition record.
///
/// **Task #97e part 1 ships the `none` arm only**, in the twin and here.
/// con-leche's body is `lamBody`, a `projOwners` lookup, a level-parameter
/// comparison, a `projLevels` lookup and `projRecValue` — the last of which is
/// 52 lines over `ExprOps` (`ConLeche/Frontend/ProjRec.lean:279-330`),
/// scheduled as part 2.  Until then `proj_owners` and `proj_levels` are never
/// written (see [`register_proj_owners`] and [`note_proj_iota`]), so
/// con-leche's own second line — `let o ← st.projOwners[T]?` — would miss on
/// every record too: the answer this returns is the answer con-leche's body
/// computes at an empty owner table, and no record is rewritten by either
/// side.
pub fn proj_rewrite_d(_st: &StateD, _cv: &IConstantVal, _vl: &EIdx) -> Option<EIdx> {
    None
}

/// con-leche: ConLeche/Frontend/ExportC.lean:304-317 noteProjIota
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:320-321 noteProjIota`
/// — an artifact `T._model.proj_i.iota` names the field's sort in its `Eq`
/// level, recorded for the projection rewrite.
///
/// **Part 1 records nothing**: the artifacts it reads are records the
/// in-process modeller GENERATES (con-leche's task #219: the only source), and
/// the modeller is `types::DeclineModeller`, so no such record reaches this
/// function.  Its two readers (`isProjIotaName`, `projIotaLevel`) are part 2
/// with the rest of `ProjRec`.
pub fn note_proj_iota(_st: &mut StateD, _cvp: &IConstantVal) {}

/// con-leche: ConLeche/Frontend/ExportC.lean:319-326 pushGenD
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:326-329 pushGenD` —
/// push one record the in-process modeller generated: `push_decl`, plus the
/// projection-iota registration (the ONLY place it runs).
pub fn push_gen_d(
    ar: &mut EStore,
    st: &mut StateD,
    d: IDeclaration,
) -> Result<(), LineErr> {
    match &d {
        IDeclaration::ThmDecl(cv, _) => {
            let cv2 = i_constant_val_dup(cv);
            note_proj_iota(st, &cv2);
        }
        _ => {}
    }
    push_decl(ar, st, d)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:328-336 noteGen
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:334-339 noteGen` —
/// book a record the in-process modeller generated for block `T0`: a
/// declaration of the FOLD, never a record of the file, so the driver's
/// headline count subtracts it.
pub fn note_gen(st: &mut StateD, d: &IDeclaration, t0: &NIdx) {
    note_gen_names(st, i_declaration_names(d), t0);
}

/// con-leche: ConLeche/Frontend/ExportC.lean:328-336 noteGen
/// `note_gen` at the record's names already in hand.  `push_gen_list` needs
/// this half: `push_gen_d` takes the record by value (it is pushed into the
/// state), and con-leche reads `d.names` afterwards because a Lean value is
/// still there to read.
pub fn note_gen_names(st: &mut StateD, names: Vec<NIdx>, t0: &NIdx) {
    st.gen_records += 1;
    let n = names.len();
    let mut i = 0usize;
    while i < n {
        st.gen_owner.insert(names[i].dup2(), t0.dup2());
        i += 1;
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:398-404 pushGenList
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:402-404 pushGenList` —
/// push the records the in-process modeller generated, each booked as a
/// declaration of the fold and not a record of the file.  The list is BORROWED
/// and each record copied in: the Aeneas subset has no way to move an element
/// out of an owned `Vec`.
pub fn push_gen_list(
    ar: &mut EStore,
    st: &mut StateD,
    gen: &Vec<IDeclaration>,
    t0: &NIdx,
) -> Result<(), LineErr> {
    let n = gen.len();
    let mut i = 0usize;
    while i < n {
        let names = i_declaration_names(&gen[i]);
        match push_gen_d(ar, st, env::i_declaration_dup(&gen[i])) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        note_gen_names(st, names, t0);
        i += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/ExportC.lean:338-344 indPiTeleLen
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:345-350 indPiTeleLen`
/// — the syntactic Π-telescope length of a declared type: official counts a
/// constructor's binders by walking `is_pi` without reducing, and the count
/// past the parameters is the `numFields` of the constructor it generates.
///
/// The twin's fuelled recursion is a `while` here (this directory's loop
/// relaxation); `-loops-to-rec` gives the recursion back.
pub fn ind_pi_tele_len(ar: &EStore, fuel: u64, h: &EIdx) -> Result<u64, LineErr> {
    let mut n: u64 = 0;
    let mut cur = h.dup2();
    let mut left = fuel;
    while left > 0 {
        match env::view_e(ar, &cur) {
            Err(e) => return fail(e),
            Ok(ENodeView::ForallE(_, b, _)) => {
                cur = b;
                n += 1;
            }
            Ok(_) => return Ok(n),
        }
        left -= 1;
    }
    const M_FUEL_TELE: [u32; 28] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 105,
        110, 100, 80, 105, 84, 101, 108, 101, 76, 101, 110,
    ];
    merr(core_types::code_points(&M_FUEL_TELE))
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1134-1138 piResult
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:784-789 piResult` — the body of
/// a syntactic `∀`-telescope.  `validate_ind_d`'s `is_K_target` is its one
/// caller in the frontend; the `ExprOps` twin proper is `arena/expr_ops.rs`,
/// which task #97 P4b writes, and this call site moves to it then.  Three
/// lines, spelled here rather than left as a hole in the one function that
/// needs it.
pub fn pi_result(ar: &EStore, fuel: u64, h: &EIdx) -> Result<EIdx, LineErr> {
    let mut cur = h.dup2();
    let mut left = fuel;
    while left > 0 {
        match env::view_e(ar, &cur) {
            Err(e) => return fail(e),
            Ok(ENodeView::ForallE(_, b, _)) => cur = b,
            Ok(_) => return Ok(cur),
        }
        left -= 1;
    }
    const M_FUEL_PIRES: [u32; 24] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 112,
        105, 82, 101, 115, 117, 108, 116,
    ];
    merr(core_types::code_points(&M_FUEL_PIRES))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:346-349 parseRuleD
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:355-357 parseRuleD` —
/// one recursor rule of an inductive record, resolved.  The install-computed
/// fields carry con-leche's own parse placeholders.
pub fn parse_rule_d(st: &StateD, ru: &RuleRec) -> Result<IRecRule, LineErr> {
    match st_name(st, ru.ctor) {
        Err(e) => Err(e),
        Ok(c) => match get_decl_d(st, ru.rhs) {
            Err(e) => Err(e),
            Ok(rhs) => Ok(i_rec_rule_parsed(c, ru.nfields, rhs)),
        },
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:346-349 parseRuleD
/// A recursor record's whole rule list (`r.rules.mapM (parseRuleD st)`).
pub fn parse_rules_d(st: &StateD, rus: &Vec<RuleRec>) -> Result<Vec<IRecRule>, LineErr> {
    let mut out: Vec<IRecRule> = Vec::with_capacity(rus.len());
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

/// con-leche: none — `scan_types::CVRec` derives nothing (DESIGN.md §3.4)
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

/// con-leche: none — `scan_types::IndCtorRec` derives nothing; see `cv_rec_dup`
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

/// con-leche: ConLeche/Frontend/ExportC.lean:351-375 blockRecOf
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:361-383 blockRecOf` —
/// the export's shape data of an inductive record, for the in-process
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
) -> Result<Vec<MIndTypeRec>, LineErr> {
    let mut out: Vec<MIndTypeRec> = Vec::with_capacity(types.len());
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
            Ok(cv) => out.push(MIndTypeRec {
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
) -> Result<Vec<MIndCtorRec>, LineErr> {
    let mut out: Vec<MIndCtorRec> = Vec::with_capacity(ctors.len());
    let n = ctors.len();
    let mut i = 0usize;
    while i < n {
        let c = &ctors[i];
        match parse_cv_d(st, &c.cv) {
            Err(e) => return Err(e),
            Ok(cv) => out.push(MIndCtorRec {
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
) -> Result<Vec<MIndRecRec>, LineErr> {
    let mut out: Vec<MIndRecRec> = Vec::with_capacity(recs.len());
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
            Ok(cv) => out.push(MIndRecRec {
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

/// con-leche: none — `BlockRec` derives nothing (DESIGN.md §3.4)
/// The block copy `note_ind_blocks` needs.  con-leche shares one block value
/// under every member type name and `con_ron_core::frontend::export_c` shares
/// a `ron::ptr::P<BlockRec>`; DESIGN.md §8.5 gives the arena no `ron::ptr` at
/// all, so the arena copies — one copy per type former of a block, on the
/// parse path only, and a block is shape data (counts and handles) with no
/// term in it.
pub fn block_rec_dup(b: &BlockRec) -> BlockRec {
    BlockRec {
        types: m_ind_type_recs_dup(&b.types, 0, Vec::with_capacity(b.types.len())),
        ctors: m_ind_ctor_recs_dup(&b.ctors, 0, Vec::with_capacity(b.ctors.len())),
        recs: m_ind_rec_recs_dup(&b.recs, 0, Vec::with_capacity(b.recs.len())),
    }
}

/// con-leche: none — `BlockRec` derives nothing (DESIGN.md §3.4)
/// `block_rec_dup`'s type-former list.
pub fn m_ind_type_recs_dup(
    ts: &Vec<MIndTypeRec>,
    i: usize,
    out: Vec<MIndTypeRec>,
) -> Vec<MIndTypeRec> {
    let mut out = out;
    let n = ts.len();
    let mut k = i;
    while k < n {
        let t = &ts[k];
        out.push(MIndTypeRec {
            cv: i_constant_val_dup(&t.cv),
            n_p: t.n_p,
            n_idx: t.n_idx,
            ctors: nidx_vec_dup(&t.ctors),
            is_rec: t.is_rec,
            is_reflexive: t.is_reflexive,
            num_nested: t.num_nested,
        });
        k += 1;
    }
    out
}

/// con-leche: none — `BlockRec` derives nothing (DESIGN.md §3.4)
/// `block_rec_dup`'s constructor list.
pub fn m_ind_ctor_recs_dup(
    cs: &Vec<MIndCtorRec>,
    i: usize,
    out: Vec<MIndCtorRec>,
) -> Vec<MIndCtorRec> {
    let mut out = out;
    let n = cs.len();
    let mut k = i;
    while k < n {
        let c = &cs[k];
        out.push(MIndCtorRec {
            cv: i_constant_val_dup(&c.cv),
            n_p: c.n_p,
            n_f: c.n_f,
        });
        k += 1;
    }
    out
}

/// con-leche: none — `BlockRec` derives nothing (DESIGN.md §3.4)
/// `block_rec_dup`'s recursor list.
pub fn m_ind_rec_recs_dup(
    rs: &Vec<MIndRecRec>,
    i: usize,
    out: Vec<MIndRecRec>,
) -> Vec<MIndRecRec> {
    let mut out = out;
    let n = rs.len();
    let mut k = i;
    while k < n {
        let r = &rs[k];
        out.push(MIndRecRec {
            cv: i_constant_val_dup(&r.cv),
            n_p: r.n_p,
            n_m: r.n_m,
            nm: r.nm,
            n_i: r.n_i,
            rules: env::i_rec_rules_dup(&r.rules),
        });
        k += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/ExportC.lean:377-396 registerProjOwners
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:394-397 registerProjOwners`
/// — record the structure-like owners of a parsed block that the projection
/// rewrite serves.
///
/// **Part 1 registers nothing**, in the twin and here.  The owners come from
/// `projRecOwners` (`ConLeche/Frontend/ProjRec.lean:332-370`), which runs
/// `occursConstFast` and `projRecValue` over the block's constructor types —
/// the `ExprOps` work scheduled as task #97e part 2.  With the table empty,
/// [`proj_rewrite_d`] returns what con-leche returns at an empty table.
pub fn register_proj_owners(
    _st: &mut StateD,
    _tys: &Vec<IndTypeRec>,
    _cts: &Vec<IndCtorRec>,
    _rcs: &Vec<IndRecRec>,
    _block: &Vec<IConstantInfo>,
) {
}

// ---------------------------------------------------------------------------
// `validateIndD` (`ExportC.lean:419-516` of the twin) and its pieces
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
/// The cited `nPs.all (· == nPd)`.
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
/// The cited `tys.mapM fun t => st.name t.cv.name`.
pub fn ty_names_of(st: &StateD, tys: &Vec<IndTypeRec>) -> Result<Vec<NIdx>, LineErr> {
    let mut out: Vec<NIdx> = Vec::with_capacity(tys.len());
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
/// The cited `tys.mapM fun t => getDeclD st t.cv.type`.
pub fn ty_types_of(st: &StateD, tys: &Vec<IndTypeRec>) -> Result<Vec<EIdx>, LineErr> {
    let mut out: Vec<EIdx> = Vec::with_capacity(tys.len());
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
/// The cited `tys.mapM fun t => t.ctors.mapM st.name`.
pub fn listed_ctors_of(
    st: &StateD,
    tys: &Vec<IndTypeRec>,
) -> Result<Vec<Vec<NIdx>>, LineErr> {
    let mut out: Vec<Vec<NIdx>> = Vec::with_capacity(tys.len());
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
/// The cited `cts.mapM fun c => st.name c.cv.name`.
pub fn ctor_names_of(st: &StateD, cts: &Vec<IndCtorRec>) -> Result<Vec<NIdx>, LineErr> {
    let mut out: Vec<NIdx> = Vec::with_capacity(cts.len());
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
pub fn flatten_listed(listed: &Vec<Vec<NIdx>>) -> Vec<NIdx> {
    let mut out: Vec<NIdx> = Vec::new();
    let n = listed.len();
    let mut i = 0usize;
    while i < n {
        let m = listed[i].len();
        let mut j = 0usize;
        while j < m {
            out.push(listed[i][j].dup2());
            j += 1;
        }
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// The cited `flat.Nodup`, decided: does the flattened constructor list repeat
/// a name?  A handle-keyed set pass, as `con_ron_core::frontend::export_c`'s
/// is (a `HashMap<_, bool>`), and not the quadratic scan: Aeneas answers
/// "Returns inside of nested loops are not supported yet" to the latter
/// (measured at this task).  Handle equality is name equality, which is sound
/// because `denoteN` is injective (task #97a's `denoteN_inj`).
pub fn names_have_dup(flat: &Vec<NIdx>) -> bool {
    let mut seen: HashMap<NIdx, bool> = HashMap::with_capacity(flat.len());
    let n = flat.len();
    let mut i = 0usize;
    while i < n {
        if seen.contains_key(&flat[i]) {
            return true;
        }
        seen.insert(flat[i].dup2(), true);
        i += 1;
    }
    false
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// The cited `ctorNames.foldl … ({}, 0)`: the constructor records by name,
/// **LAST record wins** — the cited fold's `Std.HashMap.insert` overwrites,
/// and task #87's refinement of `validateIndD` found that the difference is
/// observable (with a repeated constructor name the two sides run
/// `check_one_ctor` on *different* records).
pub fn ctor_index_of(ns: &Vec<NIdx>) -> HashMap<NIdx, u64> {
    let mut m: HashMap<NIdx, u64> = HashMap::with_capacity(ns.len());
    let n = ns.len();
    let mut i = 0usize;
    while i < n {
        m.insert(ns[i].dup2(), i as u64);
        i += 1;
    }
    m
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"No such constructor {n}"`.
pub fn no_such_ctor_error(n: &Vec<u32>) -> Vec<u32> {
    const A_NOSUCH: [u32; 20] = [
        78, 111, 32, 115, 117, 99, 104, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111,
        114, 32,
    ];
    text::cat(core_types::code_points(&A_NOSUCH), n)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"the inductive block lists {a} constructors and carries {b} constructor
/// records"`.
pub fn ctor_count_error(a: u64, b: u64) -> Vec<u32> {
    const A_LISTS: [u32; 26] = [
        116, 104, 101, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99,
        107, 32, 108, 105, 115, 116, 115, 32,
    ];
    const B_LISTS: [u32; 26] = [
        32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 115, 32, 97, 110, 100, 32,
        99, 97, 114, 114, 105, 101, 115, 32,
    ];
    const C_LISTS: [u32; 20] = [
        32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 114, 101, 99, 111, 114,
        100, 115,
    ];
    let s = text::cat3(
        core_types::code_points(&A_LISTS),
        &text::u64_str(a),
        &core_types::code_points(&B_LISTS),
    );
    text::cat3(s, &text::u64_str(b), &core_types::code_points(&C_LISTS))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"constructor {n} declares cidx {ci}; it is constructor {j} of {t}"`.
pub fn cidx_error(n: &Vec<u32>, ci: u64, j: u64, t: &Vec<u32>) -> Vec<u32> {
    const A_CTOR: [u32; 12] = [
        99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32,
    ];
    const B_DECLARES: [u32; 10] = [
        32, 100, 101, 99, 108, 97, 114, 101, 115, 32,
    ];
    const C_CIDX: [u32; 5] = [
        99, 105, 100, 120, 32,
    ];
    const D_ITIS: [u32; 20] = [
        59, 32, 105, 116, 32, 105, 115, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111,
        114, 32,
    ];
    const E_OF: [u32; 4] = [
        32, 111, 102, 32,
    ];
    let s = text::cat3(
        core_types::code_points(&A_CTOR),
        n,
        &core_types::code_points(&B_DECLARES),
    );
    let s = text::cat3(s, &core_types::code_points(&C_CIDX), &text::u64_str(ci));
    let s = text::cat3(s, &core_types::code_points(&D_ITIS), &text::u64_str(j));
    text::cat3(s, &core_types::code_points(&E_OF), t)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"constructor {n} declares induct {iw}; it is a constructor of {t}"`.
pub fn induct_error(n: &Vec<u32>, iw: &Vec<u32>, t: &Vec<u32>) -> Vec<u32> {
    const A_CTOR: [u32; 12] = [
        99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32,
    ];
    const B_DECLARES: [u32; 10] = [
        32, 100, 101, 99, 108, 97, 114, 101, 115, 32,
    ];
    const C_INDUCT: [u32; 7] = [
        105, 110, 100, 117, 99, 116, 32,
    ];
    const D_CTOROF: [u32; 25] = [
        59, 32, 105, 116, 32, 105, 115, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99,
        116, 111, 114, 32, 111, 102, 32,
    ];
    let s = text::cat3(
        core_types::code_points(&A_CTOR),
        n,
        &core_types::code_points(&B_DECLARES),
    );
    let s = text::cat3(s, &core_types::code_points(&C_INDUCT), iw);
    text::cat3(s, &core_types::code_points(&D_CTOROF), t)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"constructor {n} declares {f} fields at {p} parameters; its type has {b}
/// binders"`.
pub fn fields_error(n: &Vec<u32>, f: u64, p: u64, b: u64) -> Vec<u32> {
    const A_CTOR: [u32; 12] = [
        99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32,
    ];
    const B_DECLARES: [u32; 10] = [
        32, 100, 101, 99, 108, 97, 114, 101, 115, 32,
    ];
    const C_FIELDS: [u32; 11] = [
        32, 102, 105, 101, 108, 100, 115, 32, 97, 116, 32,
    ];
    const D_PARAMS: [u32; 26] = [
        32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 59, 32, 105, 116, 115, 32, 116,
        121, 112, 101, 32, 104, 97, 115, 32,
    ];
    const E_BINDERS: [u32; 8] = [
        32, 98, 105, 110, 100, 101, 114, 115,
    ];
    let s = text::cat3(
        core_types::code_points(&A_CTOR),
        n,
        &core_types::code_points(&B_DECLARES),
    );
    let s = text::cat3(s, &text::u64_str(f), &core_types::code_points(&C_FIELDS));
    let s = text::cat3(s, &text::u64_str(p), &core_types::code_points(&D_PARAMS));
    text::cat3(s, &text::u64_str(b), &core_types::code_points(&E_BINDERS))
}

/// con-leche: none — `s!"{← readName n}"`, the twin's one message idiom
/// A name handle READ BACK and rendered: `denoteN` (`env::read_name`) then
/// `text::name_str`.  Every `validate_ind_d` message that names a declaration
/// goes through it, which is what keeps the arena's verdict text the pure
/// checker's word for word.
pub fn show_name(ar: &EStore, h: &NIdx) -> Result<Vec<u32>, LineErr> {
    match env::read_name(ar, h) {
        Err(e) => fail(e),
        Ok(n) => Ok(text::name_str(&n)),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// One constructor record, validated against the block's own declarations:
/// the redundant `cidx` and `induct` fields and the declared `numFields`.
pub fn check_one_ctor(
    ar: &EStore,
    fuel: u64,
    st: &StateD,
    n: &NIdx,
    t: &NIdx,
    c: &IndCtorRec,
    j: u64,
    n_pd: u64,
) -> Result<(), LineErr> {
    match c.cidx {
        None => {}
        Some(ci) => {
            if ci != j {
                let ns = match show_name(ar, n) {
                    Err(e) => return Err(e),
                    Ok(v) => v,
                };
                let ts = match show_name(ar, t) {
                    Err(e) => return Err(e),
                    Ok(v) => v,
                };
                return invalid(cidx_error(&ns, ci, j, &ts));
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
            if !iwn.eq2(t) {
                let ns = match show_name(ar, n) {
                    Err(e) => return Err(e),
                    Ok(v) => v,
                };
                let is = match show_name(ar, &iwn) {
                    Err(e) => return Err(e),
                    Ok(v) => v,
                };
                let ts = match show_name(ar, t) {
                    Err(e) => return Err(e),
                    Ok(v) => v,
                };
                return invalid(induct_error(&ns, &is, &ts));
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
    let b = match ind_pi_tele_len(ar, fuel, &cty) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    if n_pd + c.num_fields != b {
        let ns = match show_name(ar, n) {
            Err(e) => return Err(e),
            Ok(v) => v,
        };
        return invalid(fields_error(&ns, c.num_fields, n_pd, b));
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// One type former's constructors, in the order the type record LISTS them:
/// the inner `for` of the twin's reordering, with the accumulator passed by
/// value.
pub fn order_type_ctors(
    ar: &EStore,
    fuel: u64,
    st: &StateD,
    t: &NIdx,
    ns: &Vec<NIdx>,
    cts: &Vec<IndCtorRec>,
    ctor_ix: &HashMap<NIdx, u64>,
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
            None => match show_name(ar, nm) {
                Err(e) => return Err(e),
                Ok(v) => return invalid(no_such_ctor_error(&v)),
            },
            Some(k) => *k as usize,
        };
        if k >= cts.len() {
            match show_name(ar, nm) {
                Err(e) => return Err(e),
                Ok(v) => return invalid(no_such_ctor_error(&v)),
            }
        }
        match check_one_ctor(ar, fuel, st, nm, t, &cts[k], j, n_pd) {
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
/// order: a record array in another order is the same block, and the recursor
/// generated from it is the same one.
pub fn order_block_ctors(
    ar: &EStore,
    fuel: u64,
    st: &StateD,
    ty_names: &Vec<NIdx>,
    listed: &Vec<Vec<NIdx>>,
    cts: &Vec<IndCtorRec>,
    ctor_ix: &HashMap<NIdx, u64>,
    n_pd: u64,
) -> Result<Vec<IndCtorRec>, LineErr> {
    let mut out: Vec<IndCtorRec> = Vec::new();
    let n = ty_names.len();
    let mut t_at = 0usize;
    while t_at < n {
        match order_type_ctors(
            ar,
            fuel,
            st,
            &ty_names[t_at],
            &listed[t_at],
            cts,
            ctor_ix,
            n_pd,
            out,
        ) {
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
///
/// The level comparison runs on a READ-BACK level tree (DESIGN.md §8.3 lesson
/// 4, "intern the representation, not the algorithm"): `env::read_level` then
/// `con_ron_core::kernel::level::is_equiv`, which is the twin's
/// `Level.isEquiv (← readLevel s) .zero`.
pub fn k_expected_of(
    ar: &EStore,
    fuel: u64,
    ty_types: &Vec<EIdx>,
    listed: &Vec<Vec<NIdx>>,
    cts: &Vec<IndCtorRec>,
) -> Result<Option<bool>, LineErr> {
    if ty_types.len() != 1 || listed.len() != 1 || cts.len() != 1 {
        return Ok(Some(false));
    }
    if listed[0].len() != 1 {
        return Ok(Some(false));
    }
    let res = match pi_result(ar, fuel, &ty_types[0]) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    match env::view_e(ar, &res) {
        Err(e) => fail(e),
        Ok(ENodeView::Sort(s)) => match env::read_level(ar, &s) {
            Err(e) => fail(e),
            Ok(l) => {
                let z = level::zero();
                let is_prop = match level::is_equiv(&l, &z) {
                    Some(b) => b,
                    None => false,
                };
                Ok(Some(cts[0].num_fields == 0 && is_prop))
            }
        },
        Ok(_) => Ok(None),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"recursor {rn} declares {a} parameters; the block declares {b}"`.
pub fn rec_params_error(rn: &Vec<u32>, a: u64, b: u64) -> Vec<u32> {
    const A_REC: [u32; 9] = [
        114, 101, 99, 117, 114, 115, 111, 114, 32,
    ];
    const B_DECLARES: [u32; 10] = [
        32, 100, 101, 99, 108, 97, 114, 101, 115, 32,
    ];
    const C_PARAMS: [u32; 32] = [
        32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 59, 32, 116, 104, 101, 32, 98,
        108, 111, 99, 107, 32, 100, 101, 99, 108, 97, 114, 101, 115, 32,
    ];
    let s = text::cat3(
        core_types::code_points(&A_REC),
        rn,
        &core_types::code_points(&B_DECLARES),
    );
    let s = text::cat3(s, &text::u64_str(a), &core_types::code_points(&C_PARAMS));
    text::cat(s, &text::u64_str(b))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"recursor {rn} declares {a} motives; the block has {b} inductive types"`.
pub fn rec_motives_error(rn: &Vec<u32>, a: u64, b: u64) -> Vec<u32> {
    const A_REC: [u32; 9] = [
        114, 101, 99, 117, 114, 115, 111, 114, 32,
    ];
    const B_DECLARES: [u32; 10] = [
        32, 100, 101, 99, 108, 97, 114, 101, 115, 32,
    ];
    const C_MOTIVES: [u32; 24] = [
        32, 109, 111, 116, 105, 118, 101, 115, 59, 32, 116, 104, 101, 32, 98, 108, 111, 99,
        107, 32, 104, 97, 115, 32,
    ];
    const D_INDTYPES: [u32; 16] = [
        32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 115,
    ];
    let s = text::cat3(
        core_types::code_points(&A_REC),
        rn,
        &core_types::code_points(&B_DECLARES),
    );
    let s = text::cat3(s, &text::u64_str(a), &core_types::code_points(&C_MOTIVES));
    text::cat3(s, &text::u64_str(b), &core_types::code_points(&D_INDTYPES))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"recursor {rn} declares {a} minor premises; the block has {b}
/// constructors"`.
pub fn rec_minors_error(rn: &Vec<u32>, a: u64, b: u64) -> Vec<u32> {
    const A_REC: [u32; 9] = [
        114, 101, 99, 117, 114, 115, 111, 114, 32,
    ];
    const B_DECLARES: [u32; 10] = [
        32, 100, 101, 99, 108, 97, 114, 101, 115, 32,
    ];
    const C_MINORS: [u32; 31] = [
        32, 109, 105, 110, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101, 115, 59, 32,
        116, 104, 101, 32, 98, 108, 111, 99, 107, 32, 104, 97, 115, 32,
    ];
    const D_CTORS: [u32; 13] = [
        32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 115,
    ];
    let s = text::cat3(
        core_types::code_points(&A_REC),
        rn,
        &core_types::code_points(&B_DECLARES),
    );
    let s = text::cat3(s, &text::u64_str(a), &core_types::code_points(&C_MINORS));
    text::cat3(s, &text::u64_str(b), &core_types::code_points(&D_CTORS))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"recursor {rn} declares k := {k}; the generated recursor of this block
/// is[ not] K-like"`.
pub fn rec_k_error(rn: &Vec<u32>, k: bool, k_e: bool) -> Vec<u32> {
    const A_REC: [u32; 9] = [
        114, 101, 99, 117, 114, 115, 111, 114, 32,
    ];
    const B_K: [u32; 15] = [
        32, 100, 101, 99, 108, 97, 114, 101, 115, 32, 107, 32, 58, 61, 32,
    ];
    const C_GENREC: [u32; 41] = [
        59, 32, 116, 104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101,
        99, 117, 114, 115, 111, 114, 32, 111, 102, 32, 116, 104, 105, 115, 32, 98, 108, 111,
        99, 107, 32, 105, 115,
    ];
    const D_NOT: [u32; 4] = [
        32, 110, 111, 116,
    ];
    const E_KLIKE: [u32; 7] = [
        32, 75, 45, 108, 105, 107, 101,
    ];
    let s = text::cat3(
        core_types::code_points(&A_REC),
        rn,
        &core_types::code_points(&B_K),
    );
    let s = text::cat3(s, &bool_str(k), &core_types::code_points(&C_GENREC));
    let s = if k_e {
        s
    } else {
        text::cat(s, &core_types::code_points(&D_NOT))
    };
    text::cat(s, &core_types::code_points(&E_KLIKE))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `"recursor {rn} declares {a} indices; {t} has {b} at {p} parameters"`.
pub fn rec_indices_error(rn: &Vec<u32>, a: u64, t: &Vec<u32>, b: u64, p: u64) -> Vec<u32> {
    const A_REC: [u32; 9] = [
        114, 101, 99, 117, 114, 115, 111, 114, 32,
    ];
    const B_DECLARES: [u32; 10] = [
        32, 100, 101, 99, 108, 97, 114, 101, 115, 32,
    ];
    const C_INDICES: [u32; 10] = [
        32, 105, 110, 100, 105, 99, 101, 115, 59, 32,
    ];
    const D_HAS: [u32; 5] = [
        32, 104, 97, 115, 32,
    ];
    const E_AT: [u32; 4] = [
        32, 97, 116, 32,
    ];
    const F_PARAMS: [u32; 11] = [
        32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115,
    ];
    let s = text::cat3(
        core_types::code_points(&A_REC),
        rn,
        &core_types::code_points(&B_DECLARES),
    );
    let s = text::cat3(s, &text::u64_str(a), &core_types::code_points(&C_INDICES));
    let s = text::cat3(s, t, &core_types::code_points(&D_HAS));
    let s = text::cat3(s, &text::u64_str(b), &core_types::code_points(&E_AT));
    text::cat3(s, &text::u64_str(p), &core_types::code_points(&F_PARAMS))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// `numIndices` of `T.rec` is what is left of `T`'s own telescope once the
/// parameters are peeled; unreadable at a former declared at a definition, and
/// then not checked.
pub fn check_rec_indices(
    ar: &EStore,
    fuel: u64,
    rn: &NIdx,
    t_pre: &NIdx,
    num_indices: u64,
    ty_names: &Vec<NIdx>,
    ty_types: &Vec<EIdx>,
    n_pd: u64,
) -> Result<(), LineErr> {
    let n = ty_names.len();
    let mut i = 0usize;
    while i < n {
        if ty_names[i].eq2(t_pre) {
            match env::pi_sort_tele_len(ar, fuel, &ty_types[i]) {
                Err(e) => return fail(e),
                Ok(None) => {}
                Ok(Some(k)) => {
                    if n_pd + num_indices != k {
                        let rs = match show_name(ar, rn) {
                            Err(e) => return Err(e),
                            Ok(v) => v,
                        };
                        let ts = match show_name(ar, t_pre) {
                            Err(e) => return Err(e),
                            Ok(v) => v,
                        };
                        return invalid(rec_indices_error(
                            &rs,
                            num_indices,
                            &ts,
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
    ar: &EStore,
    fuel: u64,
    st: &StateD,
    r: &IndRecRec,
    ty_names: &Vec<NIdx>,
    ty_types: &Vec<EIdx>,
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
        match show_name(ar, &rn) {
            Err(e) => return Err(e),
            Ok(v) => return invalid(rec_params_error(&v, r.num_params, n_pd)),
        }
    }
    if r.num_motives != n_types {
        match show_name(ar, &rn) {
            Err(e) => return Err(e),
            Ok(v) => return invalid(rec_motives_error(&v, r.num_motives, n_types)),
        }
    }
    if r.num_minors != n_ctors {
        match show_name(ar, &rn) {
            Err(e) => return Err(e),
            Ok(v) => return invalid(rec_minors_error(&v, r.num_minors, n_ctors)),
        }
    }
    match k_exp {
        None => {}
        Some(k_e) => {
            if r.k != *k_e {
                match show_name(ar, &rn) {
                    Err(e) => return Err(e),
                    Ok(v) => return invalid(rec_k_error(&v, r.k, *k_e)),
                }
            }
        }
    }
    match env::view_n(ar, &rn) {
        Err(e) => fail(e),
        Ok(NNodeView::Str(t_pre, last)) => {
            const R_REC: [u32; 3] = [
                114, 101, 99,
            ];
            if text::cps_beq(&last, &R_REC) {
                check_rec_indices(ar, fuel, &rn, &t_pre, r.num_indices, ty_names, ty_types, n_pd)
            } else {
                Ok(())
            }
        }
        Ok(_) => Ok(()),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// Every recursor record of the block.  NOT run at a NESTED block — the kernel
/// specialises a nested block into a mutual one with a mimic type per nested
/// occurrence, and the recursors it generates are the SPECIALISED block's.
pub fn check_rec_records(
    ar: &EStore,
    fuel: u64,
    st: &StateD,
    rcs: &Vec<IndRecRec>,
    ty_names: &Vec<NIdx>,
    ty_types: &Vec<EIdx>,
    n_pd: u64,
    n_types: u64,
    n_ctors: u64,
    k_exp: &Option<bool>,
) -> Result<(), LineErr> {
    let n = rcs.len();
    let mut i = 0usize;
    while i < n {
        match check_one_rec(
            ar, fuel, st, &rcs[i], ty_names, ty_types, n_pd, n_types, n_ctors, k_exp,
        ) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
        i += 1;
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/ExportC.lean:406-558 validateIndD
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:419-516 validateIndD`
/// — **an inductive record, VALIDATED**: the half of the record's processing
/// that reads the state and changes nothing.  Every guard, every verdict and
/// every message is con-leche's; what changed is that a name comparison is a
/// handle comparison, that a structural read of a type is a `view`, and that
/// the level algorithm behind `k_expected_of` runs on a read-back level tree.
///
/// Deviation: con-leche returns `RecordVerdict ⊕ (List IndCtorRec × Nat)` and
/// the port returns the verdict through [`LineErr`], the module's one merged
/// error channel.  The twin's two `for`/`mut` loops are the functions above
/// (this module's note).
pub fn validate_ind_d(
    ar: &EStore,
    st: &StateD,
    tys: &Vec<IndTypeRec>,
    cts: &Vec<IndCtorRec>,
    rcs: &Vec<IndRecRec>,
) -> Result<(Vec<IndCtorRec>, u64), LineErr> {
    // an `unsafe inductive` is DECLINED, not an error
    if any_ty_unsafe(tys) {
        const M_UNSAFE_IND: [u32; 28] = [
            117, 110, 115, 97, 102, 101, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32,
            100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110,
        ];
        return declined(core_types::code_points(&M_UNSAFE_IND));
    }
    // THE DECLARED PARAMETER COUNT: well defined for the block exactly when
    // its type records AGREE on it
    let n_pd = if tys.len() == 0 { 0 } else { tys[0].num_params };
    if !all_num_params(tys, n_pd) {
        const M_NUMPARAMS: [u32; 56] = [
            105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99, 107, 32, 119,
            104, 111, 115, 101, 32, 116, 121, 112, 101, 32, 114, 101, 99, 111, 114, 100,
            115, 32, 100, 105, 115, 97, 103, 114, 101, 101, 32, 111, 110, 32, 110, 117, 109,
            80, 97, 114, 97, 109, 115,
        ];
        return declined(core_types::code_points(&M_NUMPARAMS));
    }
    // THE BLOCK'S REDUNDANT FIELDS: consistency checks between the stream's
    // own fields, whose verdict is `.invalid` — the fold never sees such a
    // block
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
        const M_DUP_CTOR: [u32; 55] = [
            100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 99, 111, 110, 115, 116, 114, 117,
            99, 116, 111, 114, 32, 110, 97, 109, 101, 32, 105, 110, 32, 97, 110, 32, 105,
            110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 39, 115, 32, 99,
            116, 111, 114, 115,
        ];
        return invalid(core_types::code_points(&M_DUP_CTOR));
    }
    if flat.len() != cts.len() {
        return invalid(ctor_count_error(flat.len() as u64, cts.len() as u64));
    }
    let ctor_ix = ctor_index_of(&ctor_names);
    let fuel = store_fuel(ar);
    let ordered = match order_block_ctors(ar, fuel, st, &ty_names, &listed, cts, &ctor_ix, n_pd)
    {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    // the recursor records: the counts and the K flag the GENERATED recursor
    // carries.  NOT at a NESTED block.
    let nested = any_ty_nested(tys);
    let n_types = tys.len() as u64;
    let n_ctors = ordered.len() as u64;
    let k_exp = match k_expected_of(ar, fuel, &ty_types, &listed, &ordered) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    if !nested {
        match check_rec_records(
            ar, fuel, st, rcs, &ty_names, &ty_types, n_pd, n_types, n_ctors, &k_exp,
        ) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
    }
    Ok((ordered, n_pd))
}

// ---------------------------------------------------------------------------
// `installIndD` (`ExportC.lean:526-572` of the twin) and its pieces
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ExportC.lean:560-623 installIndD
/// The cited `types ++ ctors ++ recs`: the block's `IConstantInfo`s, built in
/// three loops each of which is its own function.
pub fn ind_block_of(
    st: &StateD,
    tys: &Vec<IndTypeRec>,
    cts: &Vec<IndCtorRec>,
    rcs: &Vec<IndRecRec>,
) -> Result<Vec<IConstantInfo>, LineErr> {
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
    out: Vec<IConstantInfo>,
) -> Result<Vec<IConstantInfo>, LineErr> {
    let mut out = out;
    let n = tys.len();
    let mut i = 0usize;
    while i < n {
        match parse_cv_d(st, &tys[i].cv) {
            Err(e) => return Err(e),
            Ok(cv) => out.push(IConstantInfo::IndInfo(cv, env::i_ind_caps_default())),
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
    out: Vec<IConstantInfo>,
) -> Result<Vec<IConstantInfo>, LineErr> {
    let mut out = out;
    let n = cts.len();
    let mut i = 0usize;
    while i < n {
        let c = &cts[i];
        match parse_cv_d(st, &c.cv) {
            Err(e) => return Err(e),
            Ok(cv) => out.push(IConstantInfo::CtorInfo(cv, c.num_params, c.num_fields)),
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
    out: Vec<IConstantInfo>,
) -> Result<Vec<IConstantInfo>, LineErr> {
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
            Ok(cv) => out.push(IConstantInfo::RecInfo(
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
/// registered under every member type name (at a copy each, `block_rec_dup`'s
/// note).
pub fn note_ind_blocks(st: &mut StateD, b: &BlockRec) {
    let n = b.types.len();
    let mut i = 0usize;
    while i < n {
        st.ind_blocks
            .insert(b.types[i].cv.name.dup2(), block_rec_dup(b));
        i += 1;
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:560-623 installIndD
/// `"in-process model of {t0}: {why}"`.
pub fn in_model_decline(t0: &Vec<u32>, why: &Vec<u32>) -> Vec<u32> {
    const A_INMODEL: [u32; 20] = [
        105, 110, 45, 112, 114, 111, 99, 101, 115, 115, 32, 109, 111, 100, 101, 108, 32,
        111, 102, 32,
    ];
    const B_COLON: [u32; 2] = [
        58, 32,
    ];
    let s = text::cat3(
        core_types::code_points(&A_INMODEL),
        t0,
        &core_types::code_points(&B_COLON),
    );
    text::cat(s, why)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:560-623 installIndD
/// **THE IN-PROCESS MODELLER** (DESIGN.md §8.2's seam): a mutual or nested
/// block gets its `_model` family generated here and pushed ahead of it.  A
/// generator decline is the run's decline, naming the class; in CENSUS mode it
/// is recorded and the block pushed bare.
///
/// Split out of [`install_ind_d`] so that the caller's tail after its own
/// `match` is one call.
pub fn install_gen<G: Modeller>(
    m: &G,
    ar: &mut EStore,
    st: &mut StateD,
    block: Vec<IConstantInfo>,
    n_pd: u64,
    t0: &NIdx,
    b: &BlockRec,
) -> Result<(), LineErr> {
    let gen = {
        let ctx = state_model_ctx(st);
        m.generate(ar, &ctx, b)
    };
    match gen {
        Err(why) => {
            if st.in_model_census {
                st.in_model_declined.push((t0.dup2(), why));
                push_decl(ar, st, IDeclaration::IndDecl(block, n_pd))
            } else {
                match show_name(ar, t0) {
                    Err(e) => Err(e),
                    Ok(t) => declined(in_model_decline(&t, &why)),
                }
            }
        }
        Ok(gen2) => {
            // a generated record is a declaration of the FOLD and not a record
            // of the file: booked in `push_gen_list`, so the verdict line
            // reports the file's own count
            match push_gen_list(ar, st, &gen2, t0) {
                Err(e) => return Err(e),
                Ok(()) => {}
            }
            st.in_modelled.push(t0.dup2());
            let ord = sat_sub(st.ind_count, 1);
            let mut copy: Vec<IDeclaration> = Vec::with_capacity(gen2.len());
            let n = gen2.len();
            let mut i = 0usize;
            while i < n {
                copy.push(env::i_declaration_dup(&gen2[i]));
                i += 1;
            }
            st.in_model_gen.push((ord, copy));
            push_decl(ar, st, IDeclaration::IndDecl(block, n_pd))
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:560-623 installIndD
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:526-572 installIndD` —
/// **an inductive record, INSTALLED**: the block's constants, the
/// projection-owner table, the in-process modeller, the push.  Every change to
/// the state a validated inductive record makes is here.
///
/// **EVERY BLOCK IS AN `IndDecl`**: the basis-pin match is `prepare`'s and the
/// fold's, never the parser's.
pub fn install_ind_d<G: Modeller>(
    m: &G,
    ar: &mut EStore,
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
    register_proj_owners(st, tys, &cts, rcs, &block);
    let t0 = if block.len() == 0 {
        match ar.intern_name(NNodeView::Anonymous) {
            Err(e) => return fail(e),
            Ok(h) => h,
        }
    } else {
        i_constant_info_name(&block[0])
    };
    let b = match block_rec_of(st, tys, &cts, rcs) {
        Err(e) => return Err(e),
        Ok(v) => v,
    };
    note_ind_blocks(st, &b);
    if st.in_model && wants(&b) {
        install_gen(m, ar, st, block, n_pd, &t0, &b)
    } else {
        push_decl(ar, st, IDeclaration::IndDecl(block, n_pd))
    }
}

// ---------------------------------------------------------------------------
// The line (`ExportC.lean:577-655` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ExportC.lean:625-697 processLineCoreD
/// `"definition with safety '{s}'"`.
pub fn safety_error(s: &Vec<u32>) -> Vec<u32> {
    const A_SAFETY: [u32; 24] = [
        100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 119, 105, 116, 104, 32, 115,
        97, 102, 101, 116, 121, 32, 39,
    ];
    const B_QUOTE: [u32; 1] = [
        39,
    ];
    text::cat3(
        core_types::code_points(&A_SAFETY),
        s,
        &core_types::code_points(&B_QUOTE),
    )
}

/// con-leche: ConLeche/Frontend/ExportC.lean:625-697 processLineCoreD
/// `"unknown quotient kind '{k}'"`.
pub fn quot_kind_error(k: &Vec<u32>) -> Vec<u32> {
    const A_QUOTKIND: [u32; 23] = [
        117, 110, 107, 110, 111, 119, 110, 32, 113, 117, 111, 116, 105, 101, 110, 116, 32,
        107, 105, 110, 100, 32, 39,
    ];
    const B_QUOTE: [u32; 1] = [
        39,
    ];
    text::cat3(
        core_types::code_points(&A_QUOTKIND),
        k,
        &core_types::code_points(&B_QUOTE),
    )
}

/// con-leche: ConLeche/Frontend/ExportC.lean:625-697 processLineCoreD
/// The `#QUOT` record's `kind` word, as the kernel's `QuotKind`.
pub fn quot_kind_of(k: &Vec<u32>) -> Option<QuotKind> {
    const K_TYPE: [u32; 4] = [
        116, 121, 112, 101,
    ];
    const K_CTOR: [u32; 4] = [
        99, 116, 111, 114,
    ];
    const K_LIFT: [u32; 4] = [
        108, 105, 102, 116,
    ];
    const K_IND: [u32; 3] = [
        105, 110, 100,
    ];
    if text::cps_beq(k, &K_TYPE) {
        Some(QuotKind::Type)
    } else if text::cps_beq(k, &K_CTOR) {
        Some(QuotKind::Ctor)
    } else if text::cps_beq(k, &K_LIFT) {
        Some(QuotKind::Lift)
    } else if text::cps_beq(k, &K_IND) {
        Some(QuotKind::Ind)
    } else {
        None
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:625-697 processLineCoreD
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:577-634 processLineCoreD`
/// — the record's own semantics: the declaration kinds, producing
/// `IDeclaration` records.  Every branch, guard and error string is
/// con-leche's.
pub fn process_line_core_d<G: Modeller>(
    m: &G,
    ar: &mut EStore,
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
                const M_UNSAFE_AX: [u32; 12] = [
                    117, 110, 115, 97, 102, 101, 32, 97, 120, 105, 111, 109,
                ];
                return declined(core_types::code_points(&M_UNSAFE_AX));
            }
            // `Quot.sound` is the FOLD's: the axiom record is forwarded like
            // any other, and `sorryAx` with it.
            push_decl(ar, st, IDeclaration::AxiomDecl(cvp))
        }
        DeclRec::Defn(cvr, value, hints, safety) => {
            let cvp = match parse_cv_d(st, cvr) {
                Err(e) => return Err(e),
                Ok(v) => v,
            };
            const S_SAFE: [u32; 4] = [
                115, 97, 102, 101,
            ];
            if !text::cps_beq(safety, &S_SAFE) {
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
            // the projection-function rewrite
            match proj_rewrite_d(st, &cvp, &vl) {
                Some(vl2) => {
                    let n = cvp.name.dup2();
                    match push_decl(ar, st, IDeclaration::DefnDecl(cvp, vl2, h)) {
                        Err(e) => Err(e),
                        Ok(()) => {
                            st.proj_rewrites.push(n);
                            Ok(())
                        }
                    }
                }
                None => push_decl(ar, st, IDeclaration::DefnDecl(cvp, vl, h)),
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
            match proj_rewrite_d(st, &cvp, &vl) {
                Some(vl2) => {
                    let n = cvp.name.dup2();
                    match push_decl(ar, st, IDeclaration::ThmDecl(cvp, vl2)) {
                        Err(e) => Err(e),
                        Ok(()) => {
                            st.proj_rewrites.push(n);
                            Ok(())
                        }
                    }
                }
                None => push_decl(ar, st, IDeclaration::ThmDecl(cvp, vl)),
            }
        }
        DeclRec::Opaq(cvr, value, is_unsafe) => {
            let cvp = match parse_cv_d(st, cvr) {
                Err(e) => return Err(e),
                Ok(v) => v,
            };
            if *is_unsafe {
                const M_UNSAFE_OPAQ: [u32; 25] = [
                    117, 110, 115, 97, 102, 101, 32, 111, 112, 97, 113, 117, 101, 32, 100,
                    101, 99, 108, 97, 114, 97, 116, 105, 111, 110,
                ];
                return declined(core_types::code_points(&M_UNSAFE_OPAQ));
            }
            let vl = match get_decl_d(st, *value) {
                Err(e) => return Err(e),
                Ok(v) => v,
            };
            push_decl(ar, st, IDeclaration::OpaqueDecl(cvp, vl))
        }
        DeclRec::Quot(cvr, kind) => {
            // ONE RECORD PER `#QUOT` LINE: the constant as the file declares
            // it, at the kind the file declares it at
            let cv = match parse_cv_d(st, cvr) {
                Err(e) => return Err(e),
                Ok(v) => v,
            };
            match quot_kind_of(kind) {
                None => merr(quot_kind_error(kind)),
                Some(qk) => push_decl(ar, st, IDeclaration::QuotDecl(qk, cv)),
            }
        }
        DeclRec::Ind(tys, cts, rcs) => {
            st.ind_count += 1;
            match validate_ind_d(ar, st, tys, cts, rcs) {
                Err(e) => Err(e),
                Ok((cts2, n_pd)) => install_ind_d(m, ar, st, tys, cts2, rcs, n_pd),
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:699-711 applyDeclD
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:639-641 applyDeclD` —
/// a declaration record.  `sorryAx` is the FOLD's: the parse forwards every
/// declaration record, the `sorryAx` axiom record included.
pub fn apply_decl_d<G: Modeller>(
    m: &G,
    ar: &mut EStore,
    st: &mut StateD,
    d: &DeclRec,
) -> Result<(), LineErr> {
    process_line_core_d(m, ar, st, d)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:713-726 applyLine
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:647-655 applyLine` —
/// **THE SEMANTIC LAYER**: one scanned line applied to the parse state.  The
/// scanned record is con-leche's own (`Scan/Fast.lean`, reused); what this
/// does with it is resolve the indices, INTERN the nodes, and run the rewrite
/// and the modeller seam.
pub fn apply_line<G: Modeller>(
    m: &G,
    ar: &mut EStore,
    st: &mut StateD,
    r: &LineRec,
) -> Result<(), LineErr> {
    match r {
        LineRec::Expr(i, e) => parse_expr_entry_d(ar, st, *i, e),
        LineRec::Name(i, n) => parse_name_entry_d(ar, st, *i, n),
        LineRec::Level(i, l) => parse_level_entry_d(ar, st, *i, l),
        LineRec::Decl(d) => apply_decl_d(m, ar, st, d),
        LineRec::Header => Ok(()),
        LineRec::Blank => Ok(()),
    }
}

// ---------------------------------------------------------------------------
// The line feed and the drivers (`ExportC.lean:663-836` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ExportC.lean:730-753 ParseResultD
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:663-678 ParseResultD`
/// — the direct parse result: the declarations over handles, and the parse's
/// receipts.  No arena conversion: the handles already point into the
/// persistent tier the fold will read.
pub struct ParseResultD {
    /// the FILE's declaration records, in the file's order, plus the records
    /// the in-process modeller generated
    pub decls: Vec<IDeclaration>,
    /// projection functions rewritten to recursor form
    pub proj_rewrites: Vec<NIdx>,
    /// the blocks modelled in-process, in stream order
    pub in_modelled: Vec<NIdx>,
    /// how many of `decls` the in-process modeller generated, and which block
    /// each of them models
    pub gen_records: u64,
    pub gen_owner: HashMap<NIdx, NIdx>,
    /// the in-process modeller's generated records per block
    pub in_model_gen: Vec<(u64, Vec<IDeclaration>)>,
    /// the census's declines (block, reason)
    pub in_model_declined: Vec<(NIdx, Vec<u32>)>,
}

/// con-leche: ConLeche/Frontend/ExportC.lean:760-763 ParseResultD.ofState
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:694-696 ParseResultD.ofState`
/// — the result: the file's records, in the file's order.
pub fn parse_result_of_state(st: StateD) -> ParseResultD {
    ParseResultD {
        decls: st.decls,
        proj_rewrites: st.proj_rewrites,
        in_modelled: st.in_modelled,
        gen_records: st.gen_records,
        gen_owner: st.gen_owner,
        in_model_gen: st.in_model_gen,
        in_model_declined: st.in_model_declined,
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:765-775 applyFinalLine
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:703-710 applyFinalLine`
/// — scan and apply the LAST line of a stream, the one no newline ends.  A
/// syntactic failure is reported at its offset in the line.  con-leche calls
/// `scanLineSpec` and lets `@[csimp]` substitute `scanLineFwd`; this calls
/// `scan_line_fwd`, which is what all three binaries execute.
pub fn apply_final_line<G: Modeller>(
    m: &G,
    ar: &mut EStore,
    st: &mut StateD,
    b: &[u8],
    i: usize,
    line_no: u64,
) -> Result<(), (CheckError, u64)> {
    match scan_fast::scan_line_fwd(b, i) {
        Err(e) => Err((
            scan_err_to_check(&ScanErr {
                offset: rel_offset(e.offset, i),
                what: e.what,
            }),
            line_no,
        )),
        Ok((r, _)) => match apply_line(m, ar, st, &r) {
            Err(e) => Err(line_err_to_check(e, line_no)),
            Ok(()) => Ok(()),
        },
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:777-811 feedChunk
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:719-741 feedChunk` —
/// every COMPLETE line of the chunk from `i`, applied in order: the line count
/// and where the incomplete tail begins.  A line a chunk cut in half is told
/// from a malformed one by whether the rest of the chunk holds a newline at
/// all — which is why a scan failure is not immediately an error.
pub fn feed_chunk<G: Modeller>(
    m: &G,
    ar: &mut EStore,
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
                        scan_err_to_check(&ScanErr {
                            offset: rel_offset(e.offset, i),
                            what: e.what,
                        }),
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
                match apply_line(m, ar, st, &r) {
                    Err(e) => return Err(line_err_to_check(e, line_no + 1)),
                    Ok(()) => {}
                }
                if i >= j {
                    const M_NOPROG: [u32; 33] = [
                        116, 104, 101, 32, 108, 105, 110, 101, 32, 115, 99, 97, 110, 110,
                        101, 114, 32, 109, 97, 100, 101, 32, 110, 111, 32, 112, 114, 111,
                        103, 114, 101, 115, 115,
                    ];
                    return Err((
                        core_types::internal(core_types::code_points(&M_NOPROG)),
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
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:745 chunkSize` — how
/// many bytes the streaming driver asks for at a time.
pub const CHUNK_SIZE: usize = 4 * 1024 * 1024;

/// con-leche: none — `USize.size`, the number of machine words
/// Rust spells it `usize::BITS`, and the comparison is in `u128` because
/// `1 << 64` does not fit the type it bounds.
pub const USIZE_SIZE: u128 = 1u128 << usize::BITS;

/// con-leche: ConLeche/Frontend/ExportC.lean:816-825 sizeError
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:750-751 sizeError` —
/// **THE SIZE GUARD**: the byte reader addresses its buffer by machine word,
/// so an input of `USize.size` bytes or more is refused before any of it is
/// read.  The error carries line 0: there is no line to name.  The port drops
/// the interpolated byte count (`2^64` renders in no `u64`), as con-ron-core's
/// does.
pub fn size_error() -> (CheckError, u64) {
    const M_SIZE: [u32; 36] = [
        97, 110, 32, 105, 110, 112, 117, 116, 32, 111, 102, 32, 85, 83, 105, 122, 101, 46,
        115, 105, 122, 101, 32, 98, 121, 116, 101, 115, 32, 111, 114, 32, 109, 111, 114, 101,
    ];
    (
        core_types::not_implemented(core_types::code_points(&M_SIZE)),
        0,
    )
}

/// con-leche: ConLeche/Frontend/ExportC.lean:827-839 parseBytes
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:756-767 parseBytes` —
/// **wholesale direct parse of a byte buffer**: the whole input fed at once,
/// then the last line.  The specification the streaming parse is proved equal
/// to.
pub fn parse_bytes<G: Modeller>(
    m: &G,
    ar: &mut EStore,
    b: &[u8],
    in_model: bool,
    census: bool,
) -> Result<ParseResultD, (CheckError, u64)> {
    if (b.len() as u128) >= USIZE_SIZE {
        return Err(size_error());
    }
    let mut st = match state_d_init(ar, in_model, census) {
        Err(e) => return Err((e, 0)),
        Ok(v) => v,
    };
    match feed_chunk(m, ar, &mut st, b, 0, 0) {
        Err(e) => Err(e),
        Ok((line_no, tail)) => parse_bytes_final(m, ar, st, b, tail, line_no),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:827-839 parseBytes
/// The cited tail of `parseBytes`: the last line, the one no newline ends.
pub fn parse_bytes_final<G: Modeller>(
    m: &G,
    ar: &mut EStore,
    st: StateD,
    b: &[u8],
    tail: usize,
    line_no: u64,
) -> Result<ParseResultD, (CheckError, u64)> {
    let mut st = st;
    if tail < b.len() {
        match apply_final_line(m, ar, &mut st, b, tail, line_no + 1) {
            Err(e) => return Err(e),
            Ok(()) => {}
        }
    }
    Ok(parse_result_of_state(st))
}

/// con-leche: ConLeche/Frontend/ExportC.lean:841-846 parseExportD
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:772-774 parseExportD`
/// — wholesale direct parse of a string (the built-in prelude, tests and small
/// inputs): `parse_bytes` of its UTF-8.
pub fn parse_export_d<G: Modeller>(
    m: &G,
    ar: &mut EStore,
    contents: &str,
    in_model: bool,
    census: bool,
) -> Result<ParseResultD, (CheckError, u64)> {
    parse_bytes(m, ar, contents.as_bytes(), in_model, census)
}

/// con-leche: ConLeche/Frontend/ExportC.lean:848-865 chunkStep
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:780-788 chunkStep` —
/// **one chunk of the stream, applied**: the carried incomplete tail is put in
/// front of the new bytes, every complete line of the buffer is fed, and the
/// new incomplete tail is cut off for the next chunk; `total` counts the bytes
/// read before this chunk, for the size guard.
pub fn chunk_step<G: Modeller>(
    m: &G,
    ar: &mut EStore,
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
    match feed_chunk(m, ar, st, &buf[..], 0, line_no) {
        Err(e) => Err(e),
        Ok((line_no2, tail)) => Ok((
            buf[tail..].to_vec(),
            line_no2,
            total + (buf0.len() as u64),
        )),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:867-874 chunkFinish
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:792-797 chunkFinish` —
/// the end of the stream: the carried tail, if any, is its last line.
pub fn chunk_finish<G: Modeller>(
    m: &G,
    ar: &mut EStore,
    st: StateD,
    carry: &[u8],
    line_no: u64,
) -> Result<ParseResultD, (CheckError, u64)> {
    let mut st = st;
    if carry.len() == 0 {
        return Ok(parse_result_of_state(st));
    }
    match apply_final_line(m, ar, &mut st, carry, 0, line_no + 1) {
        Err(e) => Err(e),
        Ok(()) => Ok(parse_result_of_state(st)),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:876-880 concatBytes
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:801-803 concatBytes` —
/// the bytes of a list of chunks, in order.
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
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:813-825 parseChunksGo`
/// — **THE STREAMING PARSE, PURELY**: `chunk_step` folded over a list of
/// chunks, `chunk_finish` at its end — what the driver's read loop does with
/// the chunks its handle hands out, minus the reads.  The list is folded
/// whole: an empty chunk contributes nothing and the fold goes on, so the
/// parse of a list of chunks is the parse of their concatenation, however it
/// was cut.  The twin's `parseChunksGo` is this loop; `-loops-to-rec` gives it
/// back.
pub fn parse_chunks<G: Modeller>(
    m: &G,
    ar: &mut EStore,
    chunks: &Vec<Vec<u8>>,
    in_model: bool,
    census: bool,
) -> Result<ParseResultD, (CheckError, u64)> {
    let mut st = match state_d_init(ar, in_model, census) {
        Err(e) => return Err((e, 0)),
        Ok(v) => v,
    };
    let mut carry: Vec<u8> = Vec::new();
    let mut line_no: u64 = 0;
    let mut total: u64 = 0;
    let n = chunks.len();
    let mut i = 0usize;
    while i < n {
        match chunk_step(m, ar, &mut st, carry, line_no, total, &chunks[i][..]) {
            Err(e) => return Err(e),
            Ok((c2, l, t)) => {
                carry = c2;
                line_no = l;
                total = t;
            }
        }
        i += 1;
    }
    chunk_finish(m, ar, st, &carry[..], line_no)
}

/// con-leche: none — the line number folded into the message
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean:832-836 atLine` —
/// con-leche reports a parse failure as `(CheckError, lineNo)` and its
/// `Main.lean` prints the pair; the arena's driver seam is `Except CheckError
/// Nat` and has no position channel, so the number goes into the text instead.
/// The KIND — hence the exit code — is untouched.
pub fn at_line(e: CheckError, n: u64) -> CheckError {
    const A_LINE: [u32; 7] = [
        32, 40, 108, 105, 110, 101, 32,
    ];
    const B_PAREN: [u32; 1] = [
        41,
    ];
    let suffix = text::cat3(
        core_types::code_points(&A_LINE),
        &text::u64_str(n),
        &core_types::code_points(&B_PAREN),
    );
    match e {
        CheckError::NotImplemented(w) => core_types::not_implemented(text::cat(w, &suffix)),
        CheckError::Invalid(w) => core_types::invalid(text::cat(w, &suffix)),
        CheckError::Internal(w) => core_types::internal(text::cat(w, &suffix)),
        CheckError::Native(w) => core_types::native(text::cat(w, &suffix)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::types::DeclineModeller;
    use con_ron_core::kernel::env as cenv;

    /// The hand-written export snippets of `con_ron_core::frontend::
    /// export_c`'s tests, which are con-leche's own fixtures in miniature.
    /// The Lean twin of task #97e has no `#guard`s of its own — it was
    /// measured against the 348 e2e fixtures and `Init` — so these are the
    /// snippets both Rust parsers are checked on, and the point of the
    /// comparison is that the arena's answers are the tree parser's.
    fn minimal() -> &'static str {
        concat!(
            "{\"meta\":{\"exporter\":{\"name\":\"lean4export\"}}}\n",
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n",
            "{\"il\":1,\"succ\":0}\n",
            "{\"ie\":0,\"sort\":1}\n",
            "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}\n"
        )
    }

    fn mutual_block() -> &'static str {
        concat!(
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
        )
    }

    fn bad_fields() -> &'static str {
        concat!(
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
        )
    }

    /// A one-type block whose single constructor takes no field and whose
    /// former lands in `Prop`: official's `is_K_target`, which is what
    /// `k_expected_of` decides — so the recursor record that claims `k :=
    /// false` is INVALID.  This is the one `validate_ind_d` arm that runs the
    /// READ-BACK level algorithm (`env::read_level` then `level::is_equiv`),
    /// the arena's `Level.isEquiv (← readLevel s) .zero`.
    fn k_like_block(k: &str) -> String {
        format!(
            concat!(
                "{{\"in\":1,\"str\":{{\"pre\":0,\"str\":\"K\"}}}}\n",
                "{{\"in\":2,\"str\":{{\"pre\":1,\"str\":\"mk\"}}}}\n",
                "{{\"in\":3,\"str\":{{\"pre\":1,\"str\":\"rec\"}}}}\n",
                "{{\"ie\":0,\"sort\":0}}\n",
                "{{\"ie\":1,\"const\":{{\"name\":1,\"us\":[]}}}}\n",
                "{{\"inductive\":{{\"ctors\":[",
                "{{\"isUnsafe\":false,\"levelParams\":[],\"name\":2,\"numFields\":0,",
                "\"numParams\":0,\"type\":1}}],\"recs\":[",
                "{{\"isUnsafe\":false,\"k\":{},\"levelParams\":[],\"name\":3,",
                "\"numIndices\":0,\"numMinors\":1,\"numMotives\":1,\"numParams\":0,",
                "\"rules\":[],\"type\":1}}],\"types\":[",
                "{{\"ctors\":[2],\"isRec\":false,\"isReflexive\":false,",
                "\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"numIndices\":0,",
                "\"numNested\":0,\"numParams\":0,\"type\":0}}]}}}}\n"
            ),
            k
        )
    }

    fn cp(t: &str) -> Vec<u32> {
        t.chars().map(|c| c as u32).collect()
    }

    fn s_of(v: &[u32]) -> String {
        v.iter().filter_map(|c| char::from_u32(*c)).collect()
    }

    /// The message of a `CheckError`, as a Rust string: `CheckError` carries
    /// code points and derives no `Debug`.
    fn msg(e: &CheckError) -> String {
        let m = match e {
            CheckError::NotImplemented(m)
            | CheckError::Invalid(m)
            | CheckError::Internal(m)
            | CheckError::Native(m) => m,
        };
        s_of(m)
    }

    fn tag(e: &CheckError) -> &'static str {
        match e {
            CheckError::NotImplemented(_) => "declined",
            CheckError::Invalid(_) => "invalid",
            CheckError::Internal(_) => "internal",
            CheckError::Native(_) => "native",
        }
    }

    fn show(e: &(CheckError, u64)) -> String {
        format!("{} at line {}: {}", tag(&e.0), e.1, msg(&e.0))
    }

    fn shown(r: &Result<ParseResultD, (CheckError, u64)>) -> String {
        match r {
            Ok(_) => "an accepted parse".to_string(),
            Err(e) => show(e),
        }
    }

    /// One snippet, parsed into a fresh store: the result and the store's
    /// three node counts.
    struct Parsed {
        r: Result<ParseResultD, (CheckError, u64)>,
        n_e: usize,
        n_l: usize,
        n_n: usize,
    }

    fn parse_with(text: &str, in_model: bool, census: bool) -> Parsed {
        let mut ar = EStore::empty();
        let r = parse_export_d(&DeclineModeller {}, &mut ar, text, in_model, census);
        Parsed {
            r,
            n_e: ar.node_count(),
            n_l: ar.ls().node_count(),
            n_n: ar.ns().node_count(),
        }
    }

    fn parse(text: &str) -> Parsed {
        parse_with(text, true, false)
    }

    /// A `NIdx` read back and rendered, as a Rust string: the tests' own
    /// `readName`, which is what every `validate_ind_d` message does.
    fn nm(ar: &EStore, h: &NIdx) -> String {
        match env::read_name(ar, h) {
            Ok(n) => s_of(&text::name_str(&n)),
            Err(_) => "<dangling>".to_string(),
        }
    }

    // --- the tree parser, for the side-by-side ------------------------------

    struct NoModel;

    impl con_ron_core::frontend::in_model_rec::Modeller for NoModel {
        fn generate(
            &self,
            _ctx: &con_ron_core::frontend::in_model_rec::ModelCtx,
            _b: &con_ron_core::frontend::in_model_rec::BlockRec,
        ) -> Result<Vec<cenv::Declaration>, Vec<u32>> {
            Err(cp("no modeller in the core"))
        }
    }

    /// The same snippet through `con_ron_core::frontend::export_c`, the
    /// `Expr`-tree parser this one is the handle twin of.
    fn tree_parse(
        text: &str,
    ) -> Result<con_ron_core::frontend::export_c::ParseResultD, (CheckError, u64)> {
        con_ron_core::frontend::export_c::parse_export_d(&NoModel, text, true, false)
    }

    // --- the tests ---------------------------------------------------------

    /// A minimal stream: the header, one name, one level, one sort and an
    /// axiom over it.
    #[test]
    fn a_minimal_stream_parses() {
        let mut ar = EStore::empty();
        let r = parse_export_d(&DeclineModeller {}, &mut ar, minimal(), true, false)
            .unwrap_or_else(|e| panic!("{}", show(&e)));
        assert_eq!(r.decls.len(), 1);
        match &r.decls[0] {
            IDeclaration::AxiomDecl(cv) => assert_eq!(nm(&ar, &cv.name), "A"),
            _ => panic!("not an axiom"),
        }
    }

    /// An undefined index is a parse error naming the line, not a panic.
    #[test]
    fn an_undefined_index_is_a_parse_error() {
        let p = parse("{\"ie\":0,\"sort\":7}\n");
        match &p.r {
            Err((CheckError::Internal(m), 1)) => {
                assert!(s_of(m).contains("undefined level index 7"), "{}", s_of(m));
            }
            other => panic!("{}", shown(other)),
        }
    }

    /// **An index is bound once**: a second entry at an index a previous line
    /// bound is a parse error naming the table.
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
            let p = parse(s);
            match &p.r {
                Err((CheckError::Internal(m), 2)) => assert_eq!(s_of(m), what),
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
        let p = parse(s);
        match &p.r {
            Err((CheckError::NotImplemented(w), _)) => assert_eq!(s_of(w), "unsafe axiom"),
            other => panic!("{}", shown(other)),
        }
    }

    /// **One record per `#QUOT` line**: the decoder emits the constant the
    /// file declares, at the kind it declares it at, and matches nothing
    /// against a pin.
    #[test]
    fn a_quot_record_is_one_quot_decl() {
        let s = concat!(
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Whatever\"}}\n",
            "{\"ie\":0,\"sort\":0}\n",
            "{\"quot\":{\"kind\":\"lift\",\"levelParams\":[],\"name\":1,\"type\":0}}\n"
        );
        let mut ar = EStore::empty();
        let r = parse_export_d(&DeclineModeller {}, &mut ar, s, true, false)
            .unwrap_or_else(|e| panic!("{}", show(&e)));
        assert_eq!(r.decls.len(), 1);
        match &r.decls[0] {
            IDeclaration::QuotDecl(k, cv) => {
                assert_eq!(cenv::quot_kind_slot(k), 2);
                assert_eq!(nm(&ar, &cv.name), "Whatever");
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
        let p = parse(s);
        match &p.r {
            Err((CheckError::Internal(m), 3)) => {
                assert_eq!(s_of(m), "unknown quotient kind 'nope'")
            }
            other => panic!("{}", shown(other)),
        }
    }

    /// A mutual block reaches the modeller, and the DECLINING modeller's
    /// decline is the run's, naming the block AND the class — the twin's
    /// `declineModeller` sentence, through `install_ind_d`'s `.declined`
    /// verdict.  With the modeller off the block is pushed bare, and in census
    /// mode it is recorded and the parse continues.
    #[test]
    fn a_mutual_block_declines_at_the_modeller_point() {
        let s = mutual_block();
        let p = parse(s);
        match &p.r {
            Err((CheckError::NotImplemented(w), _)) => {
                let m = s_of(w);
                assert!(m.starts_with("in-process model of T:"), "{}", m);
                assert!(m.contains("not ported yet"), "{}", m);
            }
            other => panic!("{}", shown(other)),
        }
        let off = parse_with(s, false, false);
        match &off.r {
            Ok(r) => assert_eq!(r.decls.len(), 1),
            other => panic!("{}", shown(other)),
        }
        let mut ar = EStore::empty();
        let r = parse_export_d(&DeclineModeller {}, &mut ar, s, true, true)
            .unwrap_or_else(|e| panic!("{}", show(&e)));
        assert_eq!(r.in_model_declined.len(), 1);
        assert_eq!(nm(&ar, &r.in_model_declined[0].0), "T");
    }

    /// A block whose constructor declares the wrong `numFields` is INVALID
    /// (exit 1), not declined: the stream contradicts its own declarations.
    /// The message names the constructor, which means the handle was read back
    /// (`show_name`).
    #[test]
    fn a_contradicted_redundant_field_is_invalid() {
        let p = parse(bad_fields());
        match &p.r {
            Err((CheckError::Invalid(w), _)) => {
                let m = s_of(w);
                assert!(m.contains("T.mk declares 3 fields"), "{}", m);
            }
            other => panic!("{}", shown(other)),
        }
    }

    /// **`is_K_target` over a read-back level.**  A `Prop` block with one
    /// fieldless constructor generates a K-like recursor, so a record claiming
    /// `k := false` contradicts the block; `k := true` is accepted.  This is
    /// the only `validate_ind_d` arm that runs `pi_result`, `view` and
    /// `level::is_equiv` on a level read out of the store.
    #[test]
    fn k_like_is_decided_on_the_read_back_level() {
        let p = parse(&k_like_block("false"));
        match &p.r {
            Err((CheckError::Invalid(w), _)) => {
                let m = s_of(w);
                assert!(m.contains("declares k := false"), "{}", m);
                assert!(m.ends_with("is K-like"), "{}", m);
            }
            other => panic!("{}", shown(other)),
        }
        let ok = parse(&k_like_block("true"));
        match &ok.r {
            Ok(r) => assert_eq!(r.decls.len(), 1),
            other => panic!("{}", shown(other)),
        }
    }

    /// The chunk boundary: the same stream parsed in small chunks gives the
    /// same records AND the same store, because an incomplete line is carried
    /// and not misreported.  An empty chunk anywhere contributes nothing.
    #[test]
    fn chunking_does_not_change_the_parse() {
        let s = minimal();
        let whole = parse(s);
        let (wd, wn) = match &whole.r {
            Ok(r) => (r.decls.len(), (whole.n_e, whole.n_l, whole.n_n)),
            other => panic!("{}", shown(other)),
        };
        for chunk in [1usize, 2, 7, 8, 13, 64] {
            let cs: Vec<Vec<u8>> = s.as_bytes().chunks(chunk).map(|c| c.to_vec()).collect();
            let mut ar = EStore::empty();
            let r = parse_chunks(&DeclineModeller {}, &mut ar, &cs, true, false)
                .unwrap_or_else(|e| panic!("chunk {}: {}", chunk, show(&e)));
            assert_eq!(r.decls.len(), wd, "chunk {}", chunk);
            assert_eq!(
                (ar.node_count(), ar.ls().node_count(), ar.ns().node_count()),
                wn,
                "chunk {}",
                chunk
            );
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
        let mut ar = EStore::empty();
        let r = parse_chunks(&DeclineModeller {}, &mut ar, &cs, true, false)
            .unwrap_or_else(|e| panic!("{}", show(&e)));
        assert_eq!(r.decls.len(), wd);
    }

    /// A final line with no newline is applied (`applyFinalLine`).
    #[test]
    fn a_final_line_without_a_newline_is_applied() {
        let s = concat!(
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n",
            "{\"ie\":0,\"sort\":0}\n",
            "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}"
        );
        let p = parse(s);
        match &p.r {
            Ok(r) => assert_eq!(r.decls.len(), 1),
            other => panic!("{}", shown(other)),
        }
    }

    /// The size guard's message is a decline at line 0 (`sizeError`).
    #[test]
    fn the_size_guard_declines_at_line_zero() {
        let (e, line) = size_error();
        assert_eq!(line, 0);
        assert_eq!(tag(&e), "declined");
        assert!(msg(&e).starts_with("an input of"));
    }

    /// `at_line` folds the line into the message and leaves the KIND — hence
    /// the exit code — alone.
    #[test]
    fn at_line_keeps_the_kind() {
        let e = at_line(core_types::invalid(cp("nope")), 17);
        assert_eq!(tag(&e), "invalid");
        assert_eq!(msg(&e), "nope (line 17)");
    }

    /// **THE SIDE-BY-SIDE.**  Every snippet, through the handle parser and
    /// through `con_ron_core`'s `Expr`-tree parser: the same outcome class and
    /// the same declaration count.  The two modellers decline with different
    /// sentences, so the decline's TEXT is not compared — its kind is.
    #[test]
    fn the_arena_agrees_with_the_tree_parser_on_every_snippet() {
        let k_false = k_like_block("false");
        let k_true = k_like_block("true");
        let unsafe_ax = concat!(
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n",
            "{\"ie\":0,\"sort\":0}\n",
            "{\"axiom\":{\"isUnsafe\":true,\"levelParams\":[],\"name\":1,\"type\":0}}\n"
        );
        let bad_quot = concat!(
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Q\"}}\n",
            "{\"ie\":0,\"sort\":0}\n",
            "{\"quot\":{\"kind\":\"nope\",\"levelParams\":[],\"name\":1,\"type\":0}}\n"
        );
        let cases: Vec<&str> = vec![
            minimal(),
            mutual_block(),
            bad_fields(),
            &k_false,
            &k_true,
            "{\"ie\":0,\"sort\":7}\n",
            unsafe_ax,
            bad_quot,
        ];
        for (i, s) in cases.iter().enumerate() {
            let a = parse(s);
            let t = tree_parse(s);
            match (&a.r, &t) {
                (Ok(ra), Ok(rt)) => {
                    assert_eq!(ra.decls.len(), rt.decls.len(), "case {}", i);
                    assert_eq!(ra.gen_records, rt.gen_records, "case {}", i);
                }
                (Err(ea), Err(et)) => {
                    assert_eq!(tag(&ea.0), tag(&et.0), "case {}: {}", i, msg(&ea.0));
                    assert_eq!(ea.1, et.1, "case {}", i);
                }
                _ => panic!("case {}: {}", i, shown(&a.r)),
            }
        }
    }

    /// **THE NODE COUNTS.**  DESIGN.md §8.3's claim about the parse is that
    /// the export already externalises the DAG, so the persistent tier holds
    /// exactly one node per export entry — the twin measured that on `Init`
    /// (6 136 571 expression nodes against `init.counts`' own sum).  On a
    /// snippet the same identity is checkable by hand: the expression node
    /// count is the number of `"ie"` lines, the name count the number of
    /// `"in"` lines plus the implicit `Name.anonymous` at index 0, and the
    /// level count the number of `"il"` lines plus the implicit `Level.zero`.
    #[test]
    fn the_node_counts_are_the_streams_own_entry_counts() {
        let k_true = k_like_block("true");
        for s in [minimal(), k_true.as_str()] {
            let ie = s.matches("{\"ie\":").count();
            let iname = s.matches("{\"in\":").count();
            let il = s.matches("{\"il\":").count();
            let p = parse(s);
            assert!(p.r.is_ok(), "{}", shown(&p.r));
            assert_eq!(p.n_e, ie, "expression nodes");
            assert_eq!(p.n_n, iname + 1, "name nodes");
            assert_eq!(p.n_l, il + 1, "level nodes");
        }
    }

    /// **Hash-consing, at the parse.**  Two export entries that spell the same
    /// term are ONE node: the export's `ie` indices are the sharing, and the
    /// cons table finds the rest.  con-leche's tree parse cannot say this —
    /// its two entries are two allocations that only `==` relates.
    #[test]
    fn two_equal_entries_are_one_node() {
        let s = concat!(
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n",
            "{\"ie\":0,\"sort\":0}\n",
            "{\"ie\":1,\"sort\":0}\n",
            "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":1}}\n"
        );
        let mut ar = EStore::empty();
        let r = parse_export_d(&DeclineModeller {}, &mut ar, s, true, false)
            .unwrap_or_else(|e| panic!("{}", show(&e)));
        assert_eq!(r.decls.len(), 1);
        // two `ie` entries, one interned node
        assert_eq!(ar.node_count(), 1);
    }

    /// The parse appends to the PERSISTENT tier and never enables the scratch
    /// one (DESIGN.md §8.3: every node the frontend makes is persistent).
    #[test]
    fn the_parse_stays_in_the_persistent_tier() {
        let mut ar = EStore::empty();
        let r = parse_export_d(&DeclineModeller {}, &mut ar, minimal(), true, false)
            .unwrap_or_else(|e| panic!("{}", show(&e)));
        assert_eq!(r.decls.len(), 1);
        assert_eq!(ar.scr_count(), 0);
        assert_eq!(ar.pers_count(), ar.node_count());
        match &r.decls[0] {
            IDeclaration::AxiomDecl(cv) => {
                assert!(cv.ty.is_persistent());
                assert!(cv.name.is_persistent());
            }
            _ => panic!("not an axiom"),
        }
    }
}

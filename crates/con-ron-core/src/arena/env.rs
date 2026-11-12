//! `proof/ConRon/Arena/Env.lean` — **the declaration layer over handles**
//! (DESIGN.md §8, task #97 P4e part 1), transliterated field for field.
//!
//! con-leche's `ConLeche/Kernel/Env.lean` declares the types the frontend
//! assembles and the fold consumes: `ConstantVal`, `RecRule`, `IndCaps`,
//! `ProjTable`, `ProjEntry`, `ConstantInfo` and `Declaration`.  Each of them
//! is DESIGN.md §8's census class **(T)** — not because it computes anything
//! but because it *carries a term*.  This module is the mirror of those types
//! with
//!
//! ```text
//! Expr ↦ EIdx      Name ↦ NIdx      Level ↦ LIdx      List Level ↦ Vec<LIdx>
//! ```
//!
//! and nothing else changed: the same constructors in the same order, the same
//! fields with the same names, the same install placeholders.  The `I` prefix
//! is the only renaming, and it exists for the reason the Lean twin's does —
//! so that a module may name both `con_ron_core::kernel::env::ConstantInfo`
//! and this one.
//!
//! **What is NOT twinned.**  `ReducibilityHint`, `BasisKind`, `QuotKind` and
//! `PropWhen` are census class **(P)** — they carry no term — and DESIGN.md
//! §8.7's ruling is that (B) imports con-leche's representation-free types
//! rather than copying them.  The Rust does the same across the crate
//! boundary: they are `con_ron_core::kernel::{env,prop_when}`'s own types,
//! used as they are.  `PropWhen` is the interesting one: it holds
//! `ConLeche.Name`s, and it is read only as `IndCaps.sortZ` (task #119: the
//! binder datum it once also was is gone), so a handle twin of it would buy
//! nothing.
//!
//! **The projection tables are their own component** (con-leche task #362).
//! `IEnv` is `{consts, tables}` and `IFEnv` indexes the tables by their
//! structure's name, exactly as con-leche's `Env`/`FEnv`; a table is not a
//! constant, so `i_constant_info_name` and `i_constant_info_to_constant_val`
//! are projections and touch no store.
//!
//! ## Three deviations from the Lean twin, all of them the port's standing ones
//!
//! * **`AM` is `&mut EStore` plus `Result<_, CheckError>`.**  The twin's
//!   monad is `StateT AState (Except CheckError)`; `AState` is the store and
//!   the `ExprOps` memo tables (`Arena/Monad.lean`), and nothing in this
//!   module or in `frontend/` touches a memo.  So the Rust threads the one
//!   field it uses, by the `&mut` that `Vec`-shaped state gets everywhere in
//!   the port, and Aeneas threads it back as a return value.  When
//!   `arena/monad.rs` lands (task #97 P4b) an `AState` holds this `EStore` and
//!   every call site here becomes `&mut ast.store` — no body changes.
//! * **`Env.consts` and `Env.tables` are stored oldest-first**: `Vec::push`
//!   appends and the Aeneas subset has no `cons`.  The indexes are built in
//!   the cited (newest-wins) order either way (`mk_ifenv_go`, `mk_tbls_go`).
//! * **the indexes hold a SLOT where the twin's hold the record.**  Lean's
//!   value semantics share a `ConstantInfo` between `Env` and `FEnv` for
//!   nothing; con-ron-core stores a `P<ConstantInfo>` in both, and DESIGN §8.5
//!   says the arena has **no `ron::ptr`** at all.  Part 1 therefore gave the
//!   index its own COPY of every constant and left the question to a
//!   measurement — and task #97-P6-5 took it: on a Mathlib prefix the second
//!   copy was 19 % of the whole run, because `arena::inductives` duplicates
//!   the environment per inductive block and every duplicate copied both.  The
//!   index row is now `(counter, slot)` into `env.consts`, which is a POD; the
//!   refinement relation reads `idx[n] = (c, s) ∧ consts[s] = ci` where the
//!   twin reads `idx[n] = (c, ci)`, and no twin clause moves.  The table
//!   map `tbls` is the same design for the same reason: a row is the slot of
//!   the table in `env.tables`, where con-leche's `Std.HashMap Name
//!   ProjTable` holds the table itself.
//!
//! ## `Monad.lean`'s primitives live at the bottom of this file, for now
//!
//! `view`, `viewN`, `readName` and `readLevel` are `Arena/Monad.lean`'s, and
//! their Rust home is `arena/monad.rs` — which task #97 P4b writes.  This
//! module and `frontend/` need four of them today, so they are spelled here,
//! in a section of their own, and move when that module lands.  They are the
//! two-line dangling-handle wrappers and `Denote.lean`'s fuel-indexed
//! readback, which task #97-P4a kept in `mod tests` because nothing shipped
//! needed it: the frontend's error text and its `is_K_target` do.

use crate::arena::handle::{EIdx, LIdx, NIdx};
use crate::arena::store::{ENodeView, EStore, NNodeView};
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::kernel::env::{QuotKind, ReducibilityHint};
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::ron::hashmap::{Dup, Eq2};
// The arena's tables are the epoch-stamped open-addressed map
// (DESIGN.md's `Task #97-P6-4b`), aliased so that every use site below
// reads as it did.  `ron::hashmap::HashMap` is still what `crates/con-ron`
// uses, and is still the one with proofs.
use crate::ron::hashmap2::HashMap2 as HashMap;
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// Handle vectors (Lean's `List NIdx` / `List EIdx`, which share by value)
// ---------------------------------------------------------------------------

/// con-leche: none — a `List NIdx` copy; Lean's list is shared by value (DESIGN.md §3.2)
/// A level-parameter or constructor-name list, copied.  §3.4 has no iterator
/// adapters, so the walk is the index recursion the rest of the core uses.
pub fn nidx_vec_dup(ns: &Vec<NIdx>) -> Vec<NIdx> {
    nidx_vec_dup_from(ns, 0, Vec::with_capacity(ns.len()))
}

/// con-leche: none — a `List NIdx` copy; Lean's list is shared by value (DESIGN.md §3.2)
/// The cursor recursion behind `nidx_vec_dup`.
pub fn nidx_vec_dup_from(ns: &Vec<NIdx>, i: usize, out: Vec<NIdx>) -> Vec<NIdx> {
    if i >= ns.len() {
        out
    } else {
        let mut out = out;
        out.push(ns[i].dup2());
        nidx_vec_dup_from(ns, i + 1, out)
    }
}

/// con-leche: none — `List.contains` on a handle list, which is handle equality (DESIGN.md §8.3)
/// Whether `n` is in `ns`.  A name comparison IS a handle comparison, which is
/// sound because `denoteN` is injective (task #97a's `denoteN_inj`; DESIGN.md
/// §8.3 makes exactness a soundness obligation for exactly this reason).
pub fn nidx_vec_contains(ns: &Vec<NIdx>, n: &NIdx) -> bool {
    nidx_vec_contains_from(ns, 0, n)
}

/// con-leche: none — `List.contains` on a handle list, which is handle equality (DESIGN.md §8.3)
/// The cursor recursion behind `nidx_vec_contains`.
pub fn nidx_vec_contains_from(ns: &Vec<NIdx>, i: usize, n: &NIdx) -> bool {
    if i >= ns.len() {
        false
    } else if ns[i].eq2(n) {
        true
    } else {
        nidx_vec_contains_from(ns, i + 1, n)
    }
}

/// con-leche: none — a `List EIdx` copy; Lean's list is shared by value (DESIGN.md §3.2)
/// A projection table's bodies, copied.
pub fn eidx_vec_dup(es: &Vec<EIdx>) -> Vec<EIdx> {
    eidx_vec_dup_from(es, 0, Vec::with_capacity(es.len()))
}

/// con-leche: none — a `List EIdx` copy; Lean's list is shared by value (DESIGN.md §3.2)
/// The cursor recursion behind `eidx_vec_dup`.
pub fn eidx_vec_dup_from(es: &Vec<EIdx>, i: usize, out: Vec<EIdx>) -> Vec<EIdx> {
    if i >= es.len() {
        out
    } else {
        let mut out = out;
        out.push(es[i].dup2());
        eidx_vec_dup_from(es, i + 1, out)
    }
}

/// con-leche: none — a `List LIdx` copy; Lean's list is shared by value (DESIGN.md §3.2)
/// A nested rule's stored levels, copied.  `store::lidx_vec_dup` is
/// the same walk; this name is here so that the three handle kinds read alike
/// at the call sites of this module.
pub fn lidx_vec_dup(us: &Vec<LIdx>) -> Vec<LIdx> {
    crate::arena::store::lidx_vec_dup(us)
}

// ---------------------------------------------------------------------------
// The constant's common data (`Env.lean:71-77` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:83-88 ConstantVal
/// Lean twin: `proof/ConRon/Arena/Env.lean:49-55 IConstantVal` — data common
/// to all constants, with the name and the type as handles.  Deviation: the
/// field `type` is `ty` (`type` is a Rust keyword, task #6's modulo rule).
pub struct IConstantVal {
    pub name: NIdx,
    pub level_params: Vec<NIdx>,
    pub ty: EIdx,
}

/// con-leche: ConLeche/Kernel/Env.lean:83-88 ConstantVal
/// The record copy: two handle words and one `Vec<NIdx>` spine.
pub fn i_constant_val_dup(cv: &IConstantVal) -> IConstantVal {
    IConstantVal {
        name: cv.name.dup2(),
        level_params: nidx_vec_dup(&cv.level_params),
        ty: cv.ty.dup2(),
    }
}

// ---------------------------------------------------------------------------
// Recursor rules (`Env.lean:81-107` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:90-122 RecRuleFire
/// Lean twin: `proof/ConRon/Arena/Env.lean:59-66 IRecRuleFire` — how a stored
/// recursor rule fires.  `.nested`'s and `.levels`'s lists become handle lists;
/// the parse writes the placeholder `.plain`.
pub enum IRecRuleFire {
    Plain,
    Nested(Vec<LIdx>, Vec<EIdx>),
    Levels(Vec<LIdx>),
}

/// con-leche: ConLeche/Kernel/Env.lean:90-122 RecRuleFire
/// The copy; `.nested`'s two lists are copied spine-wise.
pub fn i_rec_rule_fire_dup(f: &IRecRuleFire) -> IRecRuleFire {
    match f {
        IRecRuleFire::Plain => IRecRuleFire::Plain,
        IRecRuleFire::Nested(lvls, pins) => {
            IRecRuleFire::Nested(lidx_vec_dup(lvls), eidx_vec_dup(pins))
        }
        IRecRuleFire::Levels(lvls) => IRecRuleFire::Levels(lidx_vec_dup(lvls)),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:124-139 RecRule
/// Lean twin: `proof/ConRon/Arena/Env.lean:68-76 IRecRule` — one iota rule of
/// a recursor: the record's three fields and `fire`, read off the recursor's
/// record (the parse placeholder `.plain`), exactly as con-leche's.
pub struct IRecRule {
    pub ctor: NIdx,
    pub nfields: u64,
    pub fire: IRecRuleFire,
    pub rhs: EIdx,
}

/// con-leche: ConLeche/Kernel/Env.lean:124-139 RecRule
/// The record copy.
pub fn i_rec_rule_dup(r: &IRecRule) -> IRecRule {
    IRecRule {
        ctor: r.ctor.dup2(),
        nfields: r.nfields,
        fire: i_rec_rule_fire_dup(&r.fire),
        rhs: r.rhs.dup2(),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:124-139 RecRule
/// A rule at the cited *parse placeholder* `fire := .plain`.
/// Rust has no field defaults, so the record the parser builds
/// (`export_c::parse_rule_d`) goes through this constructor, exactly as
/// con-ron-core's `env::rec_rule_parsed` does.
pub fn i_rec_rule_parsed(ctor: NIdx, nfields: u64, rhs: EIdx) -> IRecRule {
    IRecRule {
        ctor,
        nfields,
        fire: IRecRuleFire::Plain,
        rhs,
    }
}

/// con-leche: none — a `List RecRule` copy; Lean's list is shared by value (DESIGN.md §3.2)
/// A recursor's whole rule list, copied.
pub fn i_rec_rules_dup(rs: &Vec<IRecRule>) -> Vec<IRecRule> {
    i_rec_rules_dup_from(rs, 0, Vec::with_capacity(rs.len()))
}

/// con-leche: none — a `List RecRule` copy; Lean's list is shared by value (DESIGN.md §3.2)
/// The cursor recursion behind `i_rec_rules_dup`.
pub fn i_rec_rules_dup_from(rs: &Vec<IRecRule>, i: usize, out: Vec<IRecRule>) -> Vec<IRecRule> {
    if i >= rs.len() {
        out
    } else {
        let mut out = out;
        out.push(i_rec_rule_dup(&rs[i]));
        i_rec_rules_dup_from(rs, i + 1, out)
    }
}

// ---------------------------------------------------------------------------
// Inductive capabilities (`Env.lean:114-131` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:184-227 IndCaps
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove env::IIndCaps_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Env.lean:80-96 IIndCaps` — the
/// definitional capabilities of a stored inductive type that its block alone
/// decides.  The constructor and the counts every η reader works at are the
/// family's projection table's (`ifenv_find_table`), not the record's.
pub struct IIndCaps {
    /// official's `is_non_rec_structure`: one constructor, no index, a block
    /// that is not recursive
    pub eta: bool,
    /// the block's members (official's `all`), itself included
    pub all: Vec<NIdx>,
    /// the family's parameter count (official's `inductive_val.nparams`)
    pub nparams: u64,
    /// the family's index count (official's `inductive_val.nindices`), read off
    /// the block's recursor record
    pub n_idx: u64,
    /// the family's constructors, in declaration order (official's `cnstrs`)
    pub ctors: Vec<NIdx>,
}

/// con-leche: ConLeche/Kernel/Env.lean:184-227 IndCaps
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove env::i_ind_caps_default_refines, then delete this line
/// The cited structure's *field defaults*, which Rust has not.  The zero handle is the twin's `default :
/// NIdx`, the `Inhabited` instance of `Idx`.
pub fn i_ind_caps_default() -> IIndCaps {
    IIndCaps {
        eta: false,
        all: Vec::new(),
        nparams: 0,
        n_idx: 0,
        ctors: Vec::new(),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:184-227 IndCaps
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove env::i_ind_caps_dup_refines, then delete this line
/// The record copy.
pub fn i_ind_caps_dup(c: &IIndCaps) -> IIndCaps {
    IIndCaps {
        eta: c.eta,
        all: nidx_vec_dup(&c.all),
        nparams: c.nparams,
        n_idx: c.n_idx,
        ctors: nidx_vec_dup(&c.ctors),
    }
}

// ---------------------------------------------------------------------------
// Projection tables (`Env.lean:135-176` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:229-265 ProjTable
/// Lean twin: `proof/ConRon/Arena/Env.lean:100-110 IProjTable` — one
/// structure's projection table, every term field a handle; stored in the
/// environment's table component (`IEnv.tables`), keyed on `struct_name`.
pub struct IProjTable {
    pub struct_name: NIdx,
    pub level_params: Vec<NIdx>,
    pub num_params: u64,
    pub ctor: NIdx,
    pub num_fields: u64,
    pub bodies: Vec<EIdx>,
}

/// con-leche: ConLeche/Kernel/Env.lean:267-280 ProjEntry
/// Lean twin: `proof/ConRon/Arena/Env.lean:112-122 IProjEntry` — the per-field
/// view of a projection table.
pub struct IProjEntry {
    pub struct_name: NIdx,
    pub idx: u64,
    pub level_params: Vec<NIdx>,
    pub num_params: u64,
    pub ctor: NIdx,
    pub num_fields: u64,
    pub body: EIdx,
}

/// con-leche: ConLeche/Kernel/Env.lean:282-286 ProjTable.entry
/// Lean twin: `proof/ConRon/Arena/Env.lean:124-129 IProjTable.entry` — the
/// view at field `i`.  con-leche's `default` expression becomes the zero
/// handle (the twin's `Inhabited (Idx k)`): a table is only read at
/// `i < num_fields`, where the default is not reachable.
pub fn i_proj_table_entry(tbl: &IProjTable, i: u64) -> IProjEntry {
    let body = if i < tbl.bodies.len() as u64 {
        tbl.bodies[i as usize].dup2()
    } else {
        EIdx::of_word(0)
    };
    IProjEntry {
        struct_name: tbl.struct_name.dup2(),
        idx: i,
        level_params: nidx_vec_dup(&tbl.level_params),
        num_params: tbl.num_params,
        ctor: tbl.ctor.dup2(),
        num_fields: tbl.num_fields,
        body,
    }
}

// ---------------------------------------------------------------------------
// Stored constants (`Env.lean:181-191` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:288-312 ConstantInfo
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove env::IConstantInfo_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Env.lean:133-145 IConstantInfo` — the
/// information stored about an accepted constant, over handles; a recursor
/// carries its record's K flag, the `bool` before its rules.
pub enum IConstantInfo {
    AxiomInfo(IConstantVal),
    DefnInfo(IConstantVal, EIdx, ReducibilityHint),
    ThmInfo(IConstantVal),
    IndInfo(IConstantVal, IIndCaps),
    CtorInfo(IConstantVal, u64, u64),
    RecInfo(IConstantVal, u64, u64, bool, Vec<IRecRule>),
}

/// con-leche: ConLeche/Kernel/Env.lean:288-312 ConstantInfo
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove env::i_constant_info_dup_refines, then delete this line
/// The record copy, constructor for constructor.
pub fn i_constant_info_dup(c: &IConstantInfo) -> IConstantInfo {
    match c {
        IConstantInfo::AxiomInfo(cv) => IConstantInfo::AxiomInfo(i_constant_val_dup(cv)),
        IConstantInfo::DefnInfo(cv, v, h) => IConstantInfo::DefnInfo(
            i_constant_val_dup(cv),
            v.dup2(),
            crate::kernel::env::reducibility_hint_dup(h),
        ),
        IConstantInfo::ThmInfo(cv) => IConstantInfo::ThmInfo(i_constant_val_dup(cv)),
        IConstantInfo::IndInfo(cv, caps) => {
            IConstantInfo::IndInfo(i_constant_val_dup(cv), i_ind_caps_dup(caps))
        }
        IConstantInfo::CtorInfo(cv, a, b) => {
            IConstantInfo::CtorInfo(i_constant_val_dup(cv), *a, *b)
        }
        IConstantInfo::RecInfo(cv, a, b, k, rs) => {
            IConstantInfo::RecInfo(i_constant_val_dup(cv), *a, *b, *k, i_rec_rules_dup(rs))
        }
    }
}

/// con-leche: none — a `List ConstantInfo` copy; Lean's list is shared by value (DESIGN.md §3.2)
/// A block's constants, copied.
pub fn i_constant_infos_dup(cs: &Vec<IConstantInfo>) -> Vec<IConstantInfo> {
    i_constant_infos_dup_from(cs, 0, Vec::with_capacity(cs.len()))
}

/// con-leche: none — a `List ConstantInfo` copy; Lean's list is shared by value (DESIGN.md §3.2)
/// The cursor recursion behind `i_constant_infos_dup`.
pub fn i_constant_infos_dup_from(
    cs: &Vec<IConstantInfo>,
    i: usize,
    out: Vec<IConstantInfo>,
) -> Vec<IConstantInfo> {
    if i >= cs.len() {
        out
    } else {
        let mut out = out;
        out.push(i_constant_info_dup(&cs[i]));
        i_constant_infos_dup_from(cs, i + 1, out)
    }
}

// ---------------------------------------------------------------------------
// Declaration records (`Env.lean:196-206` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:332-368 Declaration
/// Lean twin: `proof/ConRon/Arena/Env.lean:149-159 IDeclaration` — a
/// declaration presented to the checker, over handles.  Six constructors,
/// con-leche's own order.
pub enum IDeclaration {
    AxiomDecl(IConstantVal),
    DefnDecl(IConstantVal, EIdx, ReducibilityHint),
    ThmDecl(IConstantVal, EIdx),
    OpaqueDecl(IConstantVal, EIdx),
    IndDecl(Vec<IConstantInfo>, u64),
    QuotDecl(QuotKind, IConstantVal),
}

/// con-leche: ConLeche/Kernel/Env.lean:332-368 Declaration
/// The record copy.  `prepare` needs it: the Aeneas subset has no way to move
/// an element out of an owned `Vec` (no `remove`, no `pop`, no `into_iter`),
/// so a record picked out of the parsed stream is copied rather than taken,
/// exactly as `frontend::prepare` of con-ron-core does.
pub fn i_declaration_dup(d: &IDeclaration) -> IDeclaration {
    match d {
        IDeclaration::AxiomDecl(cv) => IDeclaration::AxiomDecl(i_constant_val_dup(cv)),
        IDeclaration::DefnDecl(cv, v, h) => IDeclaration::DefnDecl(
            i_constant_val_dup(cv),
            v.dup2(),
            crate::kernel::env::reducibility_hint_dup(h),
        ),
        IDeclaration::ThmDecl(cv, v) => IDeclaration::ThmDecl(i_constant_val_dup(cv), v.dup2()),
        IDeclaration::OpaqueDecl(cv, v) => {
            IDeclaration::OpaqueDecl(i_constant_val_dup(cv), v.dup2())
        }
        IDeclaration::IndDecl(bl, n) => IDeclaration::IndDecl(i_constant_infos_dup(bl), *n),
        IDeclaration::QuotDecl(k, cv) => IDeclaration::QuotDecl(
            crate::kernel::env::quot_kind_dup(k),
            i_constant_val_dup(cv),
        ),
    }
}

// ---------------------------------------------------------------------------
// Reading a stored constant (`Env.lean:226-264` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:427-429 ConstantInfo.toConstantVal
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove env::i_constant_info_to_constant_val_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Env.lean:163-167 IConstantInfo.toConstantVal`
/// — the constant's common data, copied.
pub fn i_constant_info_to_constant_val(c: &IConstantInfo) -> IConstantVal {
    match c {
        IConstantInfo::AxiomInfo(v) => i_constant_val_dup(v),
        IConstantInfo::DefnInfo(v, _, _) => i_constant_val_dup(v),
        IConstantInfo::ThmInfo(v) => i_constant_val_dup(v),
        IConstantInfo::IndInfo(v, _) => i_constant_val_dup(v),
        IConstantInfo::CtorInfo(v, _, _) => i_constant_val_dup(v),
        IConstantInfo::RecInfo(v, _, _, _, _) => i_constant_val_dup(v),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:431 name
/// Lean twin: `proof/ConRon/Arena/Env.lean:169-173 IConstantInfo.name` — the
/// constant's name: the environment index's key.
pub fn i_constant_info_name(c: &IConstantInfo) -> NIdx {
    match c {
        IConstantInfo::AxiomInfo(v) => v.name.dup2(),
        IConstantInfo::DefnInfo(v, _, _) => v.name.dup2(),
        IConstantInfo::ThmInfo(v) => v.name.dup2(),
        IConstantInfo::IndInfo(v, _) => v.name.dup2(),
        IConstantInfo::CtorInfo(v, _, _) => v.name.dup2(),
        IConstantInfo::RecInfo(v, _, _, _, _) => v.name.dup2(),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:437-444 Declaration.names
/// Lean twin: `proof/ConRon/Arena/Env.lean:175-181 IDeclaration.names` — the
/// names a declaration record declares; `prepare::prelude_key`'s lookup and
/// the ground hoist's name index read it.
pub fn i_declaration_names(d: &IDeclaration) -> Vec<NIdx> {
    match d {
        IDeclaration::AxiomDecl(cv) => i_declaration_one_name(cv),
        IDeclaration::DefnDecl(cv, _, _) => i_declaration_one_name(cv),
        IDeclaration::ThmDecl(cv, _) => i_declaration_one_name(cv),
        IDeclaration::OpaqueDecl(cv, _) => i_declaration_one_name(cv),
        IDeclaration::QuotDecl(_, cv) => i_declaration_one_name(cv),
        IDeclaration::IndDecl(block, _) => i_constant_info_names_from(block, 0, Vec::new()),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:437-444 Declaration.names
/// The cited `[cv.name]`, as a function: §3.4 has no `vec!`.
pub fn i_declaration_one_name(cv: &IConstantVal) -> Vec<NIdx> {
    let mut out: Vec<NIdx> = Vec::with_capacity(1);
    out.push(cv.name.dup2());
    out
}

/// con-leche: ConLeche/Kernel/Env.lean:437-444 Declaration.names
/// The cited `block.map (·.name)`, as the index recursion of task #3.
pub fn i_constant_info_names_from(
    block: &Vec<IConstantInfo>,
    i: usize,
    out: Vec<NIdx>,
) -> Vec<NIdx> {
    if i >= block.len() {
        out
    } else {
        let mut out = out;
        out.push(i_constant_info_name(&block[i]));
        i_constant_info_names_from(block, i + 1, out)
    }
}

// ---------------------------------------------------------------------------
// The environment (`Env.lean:278-337` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:448-460 Env
/// Lean twin: `proof/ConRon/Arena/Env.lean:185-194 IEnv` — the global
/// environment: the constants accepted so far and the structures' projection
/// tables.  Names are unique (the checker rejects duplicates), so the order is
/// irrelevant for lookup; so are the tables' structure names.  The tables are
/// not constants: no `.const` names one, `.proj` nodes alone read them, keyed
/// on the structure's name (`ifenv_find_table`).
///
/// Deviation (the module note): the cited lists are newest-first and these
/// `Vec`s are **oldest-first**, because `Vec::push` appends.
pub struct IEnv {
    pub consts: Vec<IConstantInfo>,
    pub tables: Vec<IProjTable>,
}

/// con-leche: ConLeche/Kernel/Env.lean:464-465 Env.empty
/// Lean twin: `proof/ConRon/Arena/Env.lean:196-198 IEnv.empty` — the empty
/// environment; the starting point of every checker run.
pub fn i_env_empty() -> IEnv {
    IEnv {
        consts: Vec::new(),
        tables: Vec::new(),
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:55-76 FEnv
/// Lean twin: `proof/ConRon/Arena/Env.lean:227-236 IFEnv` — the environment
/// with its `O(1)` index (DESIGN.md §8.3 lesson 13), over the frozen base of a
/// stream's index.  con-leche's `ovl` field is not ported (see `ifenv_find`).
///
/// **The environment has two tiers, like the store.**  An `IFEnv` is one LAYER:
/// a job's own, empty until its record pushes.  The BASE is the stream's index
/// (`arena::stream_index::IStreamIndex`), built once before any check and
/// frozen into the `PersTier` (`checker::freeze_tier`), where every worker reads
/// it by reference.  The layer's own entries are all visible (con-leche's local
/// index has no counter); the base is read below the layer's two bounds,
/// con-leche's `FBase.below` and `FBase.belowRec`, which live here because the
/// base itself is shared.
///
/// **The index row is a SLOT and not an `IConstantInfo`** (task #97-P6-5,
/// lever 1): the twin's row carries the constant itself, a shared value in Lean
/// and a second deep copy in Rust.  Every writer keeps `idx` and `env.consts`
/// in step (`ifenv_push`, `ifenv_push_temp`, `ifenv_pop_temp`) and
/// `ifenv_find` reads `env.consts[s]`.  The table map `tbls` is built the same
/// way: its row is the table's slot in `env.tables`.
pub struct IFEnv {
    pub env: IEnv,
    pub idx: HashMap<NIdx, u64>,
    pub tbls: HashMap<NIdx, u64>,
    /// The base's constants are visible below this counter (`FBase.below`).
    pub base_below: u64,
    /// The base's tables are visible below this record position
    /// (`FBase.belowRec`).
    pub base_below_rec: u64,
}

/// con-leche: ConLeche/Kernel/FEnv.lean:55-76 FEnv
/// Lean twin: `proof/ConRon/Arena/Env.lean:227-236 IFEnv` — **an empty layer
/// over the frozen base**, the base visible below counter `below` and record
/// position `below_rec`: con-leche's `⟨⟨[], []⟩, {}, { base with below,
/// belowRec }, [], {}⟩`, the base itself being the `PersTier`'s.
pub fn ifenv_layer(below: u64, below_rec: u64) -> IFEnv {
    IFEnv {
        env: i_env_empty(),
        idx: HashMap::new(),
        tbls: HashMap::new(),
        base_below: below,
        base_below_rec: below_rec,
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:98-105 FEnv.lookup
/// con-leche: ConLeche/Kernel/FEnv.lean:118-128 FEnv.find?
/// Lean twin: `proof/ConRon/Arena/Env.lean:267-270 IFEnv.find?` — indexed
/// lookup: the own layer, and on a miss the frozen base (`ifenv_find_base`).
/// con-leche's `FEnv` also carries an overlay (the inductive block's rule-less
/// recursors as a view sharing the index), which the port has not: its block
/// install pushes and pops in place (`ifenv_push_temp`/`ifenv_pop_temp`).
///
/// **An empty layer is not hashed into** (`FEnv.lookup`): a job's own layer is
/// empty until its record pushes, and the lookups are hot.
pub fn ifenv_find<'a>(pers: &'a PersTier, fe: &'a IFEnv, n: &NIdx) -> Option<&'a IConstantInfo> {
    if fe.idx.len() == 0 {
        ifenv_find_base(pers, fe.base_below, n)
    } else {
        match fe.idx.get(n) {
            Some(s) => {
                if (*s as usize) < fe.env.consts.len() {
                    Some(&fe.env.consts[*s as usize])
                } else {
                    None
                }
            }
            None => ifenv_find_base(pers, fe.base_below, n),
        }
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:41-45 FBase.find?
/// Lean twin: `proof/ConRon/Arena/Env.lean:267-270 IFEnv.find?` — **the base
/// layer's lookup**: the stream index's first entry of `n`, visible below the
/// layer's counter.  The base's slot is the entry's counter
/// (`arena::stream_index`'s note).
pub fn ifenv_find_base<'a>(pers: &'a PersTier, below: u64, n: &NIdx) -> Option<&'a IConstantInfo> {
    match pers.env.idx.get(n) {
        Some(c) => {
            if *c < below && (*c as usize) < pers.env.consts.len() {
                Some(&pers.env.consts[*c as usize])
            } else {
                None
            }
        }
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:130-134 FEnv.push
/// Lean twin: `proof/ConRon/Arena/Env.lean:272-275 IFEnv.push` — the index of
/// the cons-extended environment: the new entry's slot indexed under its
/// name; the tables are untouched.
pub fn ifenv_push(fe: IFEnv, ci: IConstantInfo) -> IFEnv {
    let mut fe = fe;
    let s = fe.env.consts.len() as u64;
    fe.idx.insert(i_constant_info_name(&ci), s);
    fe.env.consts.push(ci);
    fe
}

/// con-leche: ConLeche/Kernel/FEnv.lean:136-141 FEnv.pushTable
/// Lean twin: `proof/ConRon/Arena/Env.lean:277-281 IFEnv.pushTable` — **install a
/// projection table**: the table component extended and the table map's row
/// under the structure's name pointed at it; the constant index untouched.
pub fn ifenv_push_table(fe: IFEnv, t: IProjTable) -> IFEnv {
    let mut fe = fe;
    let s = fe.env.tables.len() as u64;
    fe.tbls.insert(t.struct_name.dup2(), s);
    fe.env.tables.push(t);
    fe
}

/// con-leche: ConLeche/Kernel/FEnv.lean:168-173 FEnv.rawTable?
/// Lean twin: `proof/ConRon/Arena/Env.lean:295-300 IFEnv.rawTable?` — the table
/// map's lookup, ungated: the own layer, and on a miss the frozen base
/// (`ifenv_table_base`).
pub fn ifenv_raw_table<'a>(pers: &'a PersTier, fe: &'a IFEnv, t: &NIdx) -> Option<&'a IProjTable> {
    match fe.tbls.get(t) {
        Some(s) => {
            if (*s as usize) < fe.env.tables.len() {
                Some(&fe.env.tables[*s as usize])
            } else {
                None
            }
        }
        None => ifenv_table_base(pers, fe.base_below_rec, t),
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:47-51 FBase.findTable?
/// Lean twin: `proof/ConRon/Arena/Env.lean:295-300 IFEnv.rawTable?` — **the base
/// layer's table lookup**: the stream index's first table of `t`, visible below
/// the layer's record position.
pub fn ifenv_table_base<'a>(pers: &'a PersTier, below_rec: u64, t: &NIdx) -> Option<&'a IProjTable> {
    match pers.env.tbls.get(t) {
        Some(e) => {
            if e.0 < below_rec && (e.1 as usize) < pers.env.tables.len() {
                Some(&pers.env.tables[e.1 as usize])
            } else {
                None
            }
        }
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:175-179 FEnv.findTable?
/// Lean twin: `proof/ConRon/Arena/Env.lean:302-305 IFEnv.findTable?` — **the table
/// lookup**: `t`'s table, visible exactly where the constant `t` is.
pub fn ifenv_find_table<'a>(pers: &'a PersTier, fe: &'a IFEnv, t: &NIdx) -> Option<&'a IProjTable> {
    if ifenv_find(pers, fe, t).is_some() {
        ifenv_raw_table(pers, fe, t)
    } else {
        None
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:83-88 ConstantVal
/// Lean twin: the `Inhabited ConstantVal` default — `⟨.anonymous, [], default⟩`
/// with the zero handles (the twin's `default : NIdx`/`EIdx`).  Only a
/// total function's unreachable arm reads it.
pub fn i_constant_info_dummy_val() -> IConstantVal {
    IConstantVal {
        name: NIdx::of_word(0),
        level_params: Vec::new(),
        ty: EIdx::of_word(0),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:288-312 ConstantInfo
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove env::i_constant_info_dummy_refines, then delete this line
/// Lean twin: none — the `Inhabited IConstantInfo` the twin gets for free
/// (task #97-P6-5, lever 5).  `Vec::resize` takes a filler it never reads when
/// it shrinks; this is that filler, and nothing else may use it.
pub fn i_constant_info_dummy() -> IConstantInfo {
    IConstantInfo::AxiomInfo(IConstantVal {
        name: NIdx::of_word(0),
        level_params: Vec::new(),
        ty: EIdx::of_word(0),
    })
}

/// con-leche: ConLeche/Kernel/Env.lean:288-312 ConstantInfo
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove env::impl core::clone::Clone for IConstantInfo_refines, then delete this line
/// Lean twin: none — `core::clone::Clone` for `IConstantInfo`, which
/// `Vec::resize`'s signature demands (task #97-P6-5, lever 5).  It is
/// `i_constant_info_dup` and nothing else; no `#[derive]` (DESIGN.md §3.4).
impl core::clone::Clone for IConstantInfo {
    /// con-leche: ConLeche/Kernel/Env.lean:288-312 ConstantInfo
    /// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove env::clone_refines, then delete this line
    fn clone(&self) -> IConstantInfo {
        i_constant_info_dup(self)
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:130-134 FEnv.push
/// Lean twin: `proof/ConRon/Arena/Env.lean:272-275 IFEnv.push` — **the push of
/// a TEMPORARY extension, with what it displaced** (task #97-P6-5, lever 4).
///
/// The twin writes `fe_r := fe.push stored` and goes on using `fe`, which in
/// Lean is free; in Rust that is an `O(environment)` deep copy.  Where the
/// extension is read-only and its lifetime is a bracket — the block's
/// recursor self-environment, con-leche's `FEnv.overlay` — the port pushes in
/// place and pops afterwards, which is `O(1)`.
///
/// The pop is EXACT and needs no side condition: `insert` hands back the row
/// it displaced (`None` when the name was fresh), so `ifenv_pop_temp` puts
/// that row back rather than assuming the name was new.
pub fn ifenv_push_temp(fe: &mut IFEnv, ci: IConstantInfo) -> Option<u64> {
    let s = fe.env.consts.len() as u64;
    let prev = fe.idx.insert(i_constant_info_name(&ci), s);
    fe.env.consts.push(ci);
    prev
}

/// con-leche: ConLeche/Kernel/FEnv.lean:130-134 FEnv.push
/// Lean twin: `proof/ConRon/Arena/Env.lean:283-293 IFEnv.popTemp` — the inverse
/// of `ifenv_push_temp`: the constant popped, the displaced index row put
/// back.  See that function's note.
pub fn ifenv_pop_temp(fe: &mut IFEnv, n: &NIdx, prev: Option<u64>) {
    // `Vec::resize` and NOT `Vec::pop`: Aeneas models the first
    // (`Aeneas/Std/Vec.lean:439`, `resize_spec`, `v.val.resize new_len value`)
    // and not the second, and task #97-P4a's rule is that every extraction
    // hole is a `con-ron-core` boundary function.  Shrinking never reads the
    // filler, so `i_constant_info_dummy` is a value and not a meaning.
    let m: usize = fe.env.consts.len();
    if m == 0 {
        ()
    } else {
        fe.env.consts.resize(m - 1, i_constant_info_dummy());
    }
    match prev {
        Some(row) => {
            let _ = fe.idx.insert(n.dup2(), row);
        }
        None => {
            let _ = fe.idx.remove(n);
        }
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:181-185 FEnv.findProj?
/// Lean twin: `proof/ConRon/Arena/Env.lean:307-312 IFEnv.findProj?` — indexed
/// projection-table lookup: the structure's table, viewed at field `i`.
pub fn ifenv_find_proj(pers: &PersTier, fe: &IFEnv, t: &NIdx, i: u64) -> Option<IProjEntry> {
    match ifenv_find_table(pers, fe, t) {
        Some(tbl) => {
            if i < tbl.num_fields {
                Some(i_proj_table_entry(tbl, i))
            } else {
                None
            }
        }
        None => None,
    }
}

// ---------------------------------------------------------------------------
// The environment's value semantics (`Env.lean`'s records are values)
//
// Lean copies a record for free; the three items below are what that costs in
// Rust, and they are here because `Arena/Env.lean` is where the twin declares
// the types.  `checkIndRecs` (`arena::inductives::modeled`) is the one reader
// that needs a whole `IFEnv` copy — it uses `fe₂` four times — which is
// exactly the site where `con_ron_core::kernel::fenv::dup` is called on the
// tree-shaped side.
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// `Monad.lean`'s primitives, pending `arena/monad.rs` (task #97 P4b)
//
// `view`, `viewN`, `readName` and `readLevel` are `Arena/Monad.lean`'s, whose
// Rust home is `arena/monad.rs`.  This module (`pi_sort_tele_len`) and
// `frontend/` (the error text, `k_expected_of`) need four of
// them today; they are spelled here, together, and move when that module
// lands.  The two readbacks are `Denote.lean`'s `denoteN`/`denoteL`, fuel and
// all, which task #97-P4a kept in `mod tests` because nothing shipped needed
// them.
// ---------------------------------------------------------------------------

/// con-leche: none — the port's own dangling-handle guard; Lean twin: proof/ConRon/Arena/Monad.lean:156-163 view
/// Decode an expression handle.  A dangling handle is an internal error: the
/// checker never builds one, and the bridge claims nothing on failure.
pub fn view_e(pers: &PersTier, ar: &EStore, h: &EIdx) -> Result<ENodeView, CheckError> {
    match ar.view(pers, h) {
        Some(v) => Ok(v),
        None => {
            const M: [u32; 33] = [
                97, 114, 101, 110, 97, 58, 32, 100, 97, 110, 103, 108, 105, 110, 103, 32, 101, 120,
                112, 114, 101, 115, 115, 105, 111, 110, 32, 104, 97, 110, 100, 108, 101,
            ];
            Err(core_types::internal(core_types::code_points(&M)))
        }
    }
}

/// con-leche: none — the port's own dangling-handle guard; Lean twin: proof/ConRon/Arena/Monad.lean:377-382 viewN
/// Decode a name handle.
pub fn view_n(pers: &PersTier, ar: &EStore, h: &NIdx) -> Result<NNodeView, CheckError> {
    match ar.ns().view(pers, h) {
        Some(v) => Ok(v),
        None => Err(dangling_name()),
    }
}

/// con-leche: none — the port's own dangling-handle guard; Lean twin: proof/ConRon/Arena/Monad.lean:377-382 viewN
/// `"arena: dangling name handle"`, named once: `view_n` and `read_name` raise
/// the same error, as the twin's two primitives do.
pub fn dangling_name() -> CheckError {
    const M: [u32; 27] = [
        97, 114, 101, 110, 97, 58, 32, 100, 97, 110, 103, 108, 105, 110, 103, 32, 110, 97, 109,
        101, 32, 104, 97, 110, 100, 108, 101,
    ];
    core_types::internal(core_types::code_points(&M))
}

/// con-leche: ConLeche/Kernel/Name.lean:18-38 Name
/// Lean twin: `proof/ConRon/Arena/Monad.lean:402-410 readName` — read a name
/// back out of the store as a transient `Name`.  Names are compared by handle
/// throughout the checker (DESIGN.md §8.3), so this is the error-text and
/// level-substitution path only, and the readback IS the denotation
/// (`Denote.lean`'s `denoteN`).
pub fn read_name(pers: &PersTier, ar: &EStore, h: &NIdx) -> Result<Name, CheckError> {
    read_name_at(pers, ar, ar.ns().node_count(pers) as u64 + 1, h)
}

/// con-leche: ConLeche/Kernel/Name.lean:18-38 Name
/// The fuel-indexed readback itself (`Denote.lean`'s `denoteNAux`): the store's
/// name-node count bounds every path, because a prefix is interned before the
/// name that carries it.
pub fn read_name_at(pers: &PersTier, ar: &EStore, fuel: u64, h: &NIdx) -> Result<Name, CheckError> {
    if fuel == 0 {
        return Err(dangling_name());
    }
    match ar.ns().view(pers, h) {
        None => Err(dangling_name()),
        Some(NNodeView::Anonymous) => Ok(name::anonymous()),
        Some(NNodeView::Str(p, s)) => match read_name_at(pers, ar, fuel - 1, &p) {
            Err(e) => Err(e),
            Ok(q) => Ok(name::mk_str(q, s)),
        },
        Some(NNodeView::Num(p, n)) => match read_name_at(pers, ar, fuel - 1, &p) {
            Err(e) => Err(e),
            Ok(q) => Ok(name::mk_num(q, n)),
        },
    }
}

// ---------------------------------------------------------------------------
// The syntactic Π-telescope (`Env.lean:357-360` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:374-388 Expr.piSortTeleLen?
/// Lean twin: `proof/ConRon/Arena/Env.lean:316-326 piSortTeleLen?` — the
/// length of a syntactic Π-telescope ending in a SORT.  A spine walk, so the
/// fuel is the store's node count; con-leche's structural recursion is the
/// same walk with the node read through `view`.
pub fn pi_sort_tele_len(
    pers: &PersTier,
    ar: &EStore,
    fuel: u64,
    h: &EIdx,
) -> Result<Option<u64>, CheckError>  {
    if fuel == 0 {
        const M: [u32; 34] = [
            102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 112, 105,
            83, 111, 114, 116, 84, 101, 108, 101, 76, 101, 110, 63, 32, 40, 69, 41,
        ];
        return Err(core_types::internal(core_types::code_points(&M)));
    }
    match view_e(pers, ar, h) {
        Err(e) => Err(e),
        Ok(ENodeView::ForallE(_, body)) => match pi_sort_tele_len(pers, ar, fuel - 1, &body) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some(n)) => Ok(Some(n + 1)),
        },
        Ok(ENodeView::Sort(_)) => Ok(Some(0)),
        Ok(_) => Ok(None),
    }
}

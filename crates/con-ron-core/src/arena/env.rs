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
//! `ConLeche.Name`s, but task #97a already put `BinderMeta` — hence
//! `PropWhen` — inside the store's own `lam`/`forallE` node, so a handle twin
//! of it would be a second spelling of a datum the representation uses.
//!
//! **The one added field, and why.**  `IProjTable` carries a `table_name:
//! NIdx` con-leche's `ProjTable` does not.  con-leche COMPUTES the reserved
//! name (`ConstantInfo.toConstantVal`'s `.projInfo` arm is `projTableName
//! tbl.structName`); over handles, computing a name means INTERNING it, i.e.
//! touching the store — and `i_constant_info_name` must stay pure, because it
//! is the key of the environment index (DESIGN.md §8.3 lesson 13) and
//! `i_env_find`, the index build and `prepare::prelude_key` all run it in a
//! loop.  So the install keeps the handle it interned, as hash-consing always
//! does, and `IProjTable.table_name` is by construction `proj_table_name
//! struct_name`.  The consequence is the useful split:
//! `i_constant_info_name` and `i_declaration_names` are **pure**, while
//! `i_constant_info_to_constant_val`, `i_constant_info_type` and
//! `i_declaration_name` — which still have to intern a `Sort 1` or an
//! `.anonymous` — take the store, and are off every hot path.
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
//! * **`Env.consts` is stored oldest-first** and `i_env_find` scans it from
//!   the back, which is con-ron-core's `kernel::env::Env` deviation (task
//!   #50): `Vec::push` appends and the Aeneas subset has no `cons`.  The
//!   cited (newest-first) order is what is scanned either way.
//! * **the index holds a SLOT where the twin's holds the record.**  Lean's
//!   value semantics share a `ConstantInfo` between `Env` and `FEnv` for
//!   nothing; con-ron-core stores a `P<ConstantInfo>` in both, and DESIGN §8.5
//!   says the arena has **no `ron::ptr`** at all.  Part 1 therefore gave the
//!   index its own COPY of every constant and left the question to a
//!   measurement — and task #97-P6-5 took it: on a Mathlib prefix the second
//!   copy was 19 % of the whole run, because `arena::inductives` duplicates
//!   the environment per inductive block and every duplicate copied both.  The
//!   index row is now `(counter, slot)` into `env.consts`, which is a POD; the
//!   refinement relation reads `idx[n] = (c, s) ∧ consts[s] = ci` where the
//!   twin reads `idx[n] = (c, ci)`, and no twin clause moves.
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
use crate::arena::store::{ENodeView, EStore, LNodeView, NNodeView};
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::kernel::env::{QuotKind, ReducibilityHint};
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;
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
/// A projection table's field-sort guards, copied.  `store::lidx_vec_dup` is
/// the same walk; this name is here so that the three handle kinds read alike
/// at the call sites of this module.
pub fn lidx_vec_dup(us: &Vec<LIdx>) -> Vec<LIdx> {
    crate::arena::store::lidx_vec_dup(us)
}

// ---------------------------------------------------------------------------
// The constant's common data (`Env.lean:71-77` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:186-191 ConstantVal
/// Lean twin: `proof/ConRon/Arena/Env.lean:66-72 IConstantVal` — data common
/// to all constants, with the name and the type as handles.  Deviation: the
/// field `type` is `ty` (`type` is a Rust keyword, task #6's modulo rule).
pub struct IConstantVal {
    pub name: NIdx,
    pub level_params: Vec<NIdx>,
    pub ty: EIdx,
}

/// con-leche: ConLeche/Kernel/Env.lean:186-191 ConstantVal
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

/// con-leche: ConLeche/Kernel/Env.lean:193-237 RecRuleFire
/// Lean twin: `proof/ConRon/Arena/Env.lean:76-83 IRecRuleFire` — how a stored
/// recursor rule may fire.  `.nested`'s level and pin lists become handle
/// lists; the parse writes the placeholder `.inert` and never the other two.
pub enum IRecRuleFire {
    Inert,
    Plain,
    Nested(Vec<LIdx>, Vec<EIdx>),
}

/// con-leche: ConLeche/Kernel/Env.lean:193-237 RecRuleFire
/// The copy; `.nested`'s two lists are copied spine-wise.
pub fn i_rec_rule_fire_dup(f: &IRecRuleFire) -> IRecRuleFire {
    match f {
        IRecRuleFire::Inert => IRecRuleFire::Inert,
        IRecRuleFire::Plain => IRecRuleFire::Plain,
        IRecRuleFire::Nested(lvls, pins) => {
            IRecRuleFire::Nested(lidx_vec_dup(lvls), eidx_vec_dup(pins))
        }
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:239-282 RecRule
/// Lean twin: `proof/ConRon/Arena/Env.lean:85-98 IRecRule` — one iota rule of
/// a recursor.  `ctor_params`, `fire`, `k`, `eta` and `params_blind` are
/// install-computed and carry the parse placeholders `0`/`.inert`/`false`,
/// exactly as con-leche's do.
pub struct IRecRule {
    pub ctor: NIdx,
    pub nfields: u64,
    pub ctor_params: u64,
    pub fire: IRecRuleFire,
    pub rhs: EIdx,
    pub k: bool,
    pub eta: bool,
    pub params_blind: bool,
}

/// con-leche: ConLeche/Kernel/Env.lean:239-282 RecRule
/// The record copy.
pub fn i_rec_rule_dup(r: &IRecRule) -> IRecRule {
    IRecRule {
        ctor: r.ctor.dup2(),
        nfields: r.nfields,
        ctor_params: r.ctor_params,
        fire: i_rec_rule_fire_dup(&r.fire),
        rhs: r.rhs.dup2(),
        k: r.k,
        eta: r.eta,
        params_blind: r.params_blind,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:239-282 RecRule
/// A rule at the cited *parse placeholders* — the Lean's field defaults
/// `ctorParams := 0`, `fire := .inert`, `k := eta := paramsBlind := false`.
/// Rust has no field defaults, so the record the parser builds
/// (`export_c::parse_rule_d`) goes through this constructor, exactly as
/// con-ron-core's `env::rec_rule_parsed` does.
pub fn i_rec_rule_parsed(ctor: NIdx, nfields: u64, rhs: EIdx) -> IRecRule {
    IRecRule {
        ctor,
        nfields,
        ctor_params: 0,
        fire: IRecRuleFire::Inert,
        rhs,
        k: false,
        eta: false,
        params_blind: false,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:284-291 RecRule.compareParams
/// Lean twin: `proof/ConRon/Arena/Env.lean:100-105 IRecRule.compareParams` —
/// whether the iota step compares this rule's parameter comparands.
pub fn i_rec_rule_compare_params(rl: &IRecRule) -> bool {
    match rl.fire {
        IRecRuleFire::Plain => !rl.params_blind,
        IRecRuleFire::Inert => true,
        IRecRuleFire::Nested(..) => true,
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

/// con-leche: ConLeche/Kernel/Env.lean:347-374 IndCaps
/// Lean twin: `proof/ConRon/Arena/Env.lean:109-125 IIndCaps` — the
/// definitional capabilities of a stored inductive type.  `eta_ctor` is a
/// handle; `sort_z` stays con-leche's `PropWhen`, which is the datum the
/// store's own binder metadata already carries (the module note).
pub struct IIndCaps {
    pub eta: bool,
    /// con-leche's default is `.anonymous`; the handle's is the zero word.
    /// Neither is a name the field ever *denotes*: the cited doc says the
    /// field is "meaningful only when `eta`", and the install writes it then.
    pub eta_ctor: NIdx,
    pub eta_params: u64,
    pub eta_fields: u64,
    pub unitlike: bool,
    pub unit_params: u64,
    pub rule_k: bool,
    pub sort_z: PropWhen,
}

/// con-leche: ConLeche/Kernel/Env.lean:347-374 IndCaps
/// The cited structure's *field defaults*, which Rust has not — and, as
/// con-ron-core's `env::ind_caps_default` records, the one that is not the
/// obvious zero is **`sortZ := .ifAllZero []`**, which reads "zero at every
/// valuation" and not `.never`.  The zero handle is the twin's `default :
/// NIdx`, the `Inhabited` instance of `Idx`.
pub fn i_ind_caps_default() -> IIndCaps {
    IIndCaps {
        eta: false,
        eta_ctor: NIdx::of_word(0),
        eta_params: 0,
        eta_fields: 0,
        unitlike: false,
        unit_params: 0,
        rule_k: false,
        sort_z: prop_when::if_all_zero(Vec::new()),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:347-374 IndCaps
/// The record copy.
pub fn i_ind_caps_dup(c: &IIndCaps) -> IIndCaps {
    IIndCaps {
        eta: c.eta,
        eta_ctor: c.eta_ctor.dup2(),
        eta_params: c.eta_params,
        eta_fields: c.eta_fields,
        unitlike: c.unitlike,
        unit_params: c.unit_params,
        rule_k: c.rule_k,
        sort_z: prop_when::dup(&c.sort_z),
    }
}

// ---------------------------------------------------------------------------
// Projection tables (`Env.lean:135-176` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:376-431 ProjTable
/// Lean twin: `proof/ConRon/Arena/Env.lean:129-146 IProjTable` — one
/// structure's projection table, every term field a handle.
pub struct IProjTable {
    pub struct_name: NIdx,
    /// **The one field con-leche's `ProjTable` does not have**: the reserved
    /// name `proj_table_name struct_name` the table is stored under, kept
    /// rather than recomputed so that `i_constant_info_name` — the environment
    /// index's key — is pure.  See the module note.
    pub table_name: NIdx,
    pub level_params: Vec<NIdx>,
    pub num_params: u64,
    pub ctor: NIdx,
    pub num_fields: u64,
    pub struct_sort: LIdx,
    pub bodies: Vec<EIdx>,
    pub guards: Vec<LIdx>,
    pub off: u64,
}

/// con-leche: ConLeche/Kernel/Env.lean:376-431 ProjTable
/// The record copy.
pub fn i_proj_table_dup(t: &IProjTable) -> IProjTable {
    IProjTable {
        struct_name: t.struct_name.dup2(),
        table_name: t.table_name.dup2(),
        level_params: nidx_vec_dup(&t.level_params),
        num_params: t.num_params,
        ctor: t.ctor.dup2(),
        num_fields: t.num_fields,
        struct_sort: t.struct_sort.dup2(),
        bodies: eidx_vec_dup(&t.bodies),
        guards: lidx_vec_dup(&t.guards),
        off: t.off,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:433-452 ProjEntry
/// Lean twin: `proof/ConRon/Arena/Env.lean:148-161 IProjEntry` — the per-field
/// view of a projection table.
pub struct IProjEntry {
    pub struct_name: NIdx,
    pub idx: u64,
    pub level_params: Vec<NIdx>,
    pub num_params: u64,
    pub ctor: NIdx,
    pub num_fields: u64,
    pub body: EIdx,
    pub field_sort: LIdx,
    pub struct_sort: LIdx,
    pub off: u64,
}

/// con-leche: ConLeche/Kernel/Env.lean:454-458 ProjTable.entry
/// Lean twin: `proof/ConRon/Arena/Env.lean:163-169 IProjTable.entry` — the
/// view at field `i`.  con-leche's `default` expression and its `.zero` guard
/// level become the zero handle of each kind (the twin's `Inhabited (Idx k)`):
/// a table is only read at `i < num_fields`, where neither default is
/// reachable.
pub fn i_proj_table_entry(tbl: &IProjTable, i: u64) -> IProjEntry {
    let body = if i < tbl.bodies.len() as u64 {
        tbl.bodies[i as usize].dup2()
    } else {
        EIdx::of_word(0)
    };
    let field_sort = if i < tbl.guards.len() as u64 {
        tbl.guards[i as usize].dup2()
    } else {
        LIdx::of_word(0)
    };
    IProjEntry {
        struct_name: tbl.struct_name.dup2(),
        idx: i,
        level_params: nidx_vec_dup(&tbl.level_params),
        num_params: tbl.num_params,
        ctor: tbl.ctor.dup2(),
        num_fields: tbl.num_fields,
        body,
        field_sort,
        struct_sort: tbl.struct_sort.dup2(),
        off: tbl.off,
    }
}

// ---------------------------------------------------------------------------
// Stored constants (`Env.lean:181-191` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:460-486 ConstantInfo
/// Lean twin: `proof/ConRon/Arena/Env.lean:173-183 IConstantInfo` — the
/// information stored about an accepted constant, over handles.
pub enum IConstantInfo {
    AxiomInfo(IConstantVal),
    DefnInfo(IConstantVal, EIdx, ReducibilityHint),
    ThmInfo(IConstantVal, EIdx),
    IndInfo(IConstantVal, IIndCaps),
    CtorInfo(IConstantVal, u64, u64),
    RecInfo(IConstantVal, u64, u64, Vec<IRecRule>),
    ProjInfo(IProjTable),
}

/// con-leche: ConLeche/Kernel/Env.lean:460-486 ConstantInfo
/// The record copy, constructor for constructor.
pub fn i_constant_info_dup(c: &IConstantInfo) -> IConstantInfo {
    match c {
        IConstantInfo::AxiomInfo(cv) => IConstantInfo::AxiomInfo(i_constant_val_dup(cv)),
        IConstantInfo::DefnInfo(cv, v, h) => IConstantInfo::DefnInfo(
            i_constant_val_dup(cv),
            v.dup2(),
            crate::kernel::env::reducibility_hint_dup(h),
        ),
        IConstantInfo::ThmInfo(cv, v) => IConstantInfo::ThmInfo(i_constant_val_dup(cv), v.dup2()),
        IConstantInfo::IndInfo(cv, caps) => {
            IConstantInfo::IndInfo(i_constant_val_dup(cv), i_ind_caps_dup(caps))
        }
        IConstantInfo::CtorInfo(cv, a, b) => {
            IConstantInfo::CtorInfo(i_constant_val_dup(cv), *a, *b)
        }
        IConstantInfo::RecInfo(cv, a, b, rs) => {
            IConstantInfo::RecInfo(i_constant_val_dup(cv), *a, *b, i_rec_rules_dup(rs))
        }
        IConstantInfo::ProjInfo(t) => IConstantInfo::ProjInfo(i_proj_table_dup(t)),
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

/// con-leche: ConLeche/Kernel/Env.lean:506-560 Declaration
/// Lean twin: `proof/ConRon/Arena/Env.lean:187-199 IDeclaration` — a
/// declaration presented to the checker, over handles.  Seven constructors,
/// con-leche's own order; the frontend produces every one but `BasisDecl`,
/// which is the fold's own record for "install the pinned basis block".
pub enum IDeclaration {
    AxiomDecl(IConstantVal),
    DefnDecl(IConstantVal, EIdx, ReducibilityHint),
    ThmDecl(IConstantVal, EIdx),
    OpaqueDecl(IConstantVal, EIdx),
    BasisDecl(crate::kernel::env::BasisKind),
    IndDecl(Vec<IConstantInfo>, u64),
    QuotDecl(QuotKind, IConstantVal),
}

/// con-leche: ConLeche/Kernel/Env.lean:506-560 Declaration
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
        IDeclaration::BasisDecl(k) => {
            IDeclaration::BasisDecl(crate::kernel::env::basis_kind_dup(k))
        }
        IDeclaration::IndDecl(bl, n) => IDeclaration::IndDecl(i_constant_infos_dup(bl), *n),
        IDeclaration::QuotDecl(k, cv) => IDeclaration::QuotDecl(
            crate::kernel::env::quot_kind_dup(k),
            i_constant_val_dup(cv),
        ),
    }
}

// ---------------------------------------------------------------------------
// The reserved names (`Env.lean:212-222` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:623-629 projFnName
/// Lean twin: `proof/ConRon/Arena/Env.lean:203-208 projFnName` — the public
/// projection-*function* name for field `i` of structure `T`.  Building a name
/// means interning it, so the twin is monadic and this takes the store.
pub fn proj_fn_name(
    pers: &PersTier,
    ar: &mut EStore,
    t: &NIdx,
    i: u64,
) -> Result<NIdx, CheckError>  {
    const S: [u32; 4] = [112, 114, 111, 106];
    match ar.intern_name(pers, NNodeView::Str(t.dup2(), core_types::code_points(&S))) {
        Err(e) => Err(e),
        Ok(s) => ar.intern_name(pers, NNodeView::Num(s, i)),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:631-635 projTableName
/// Lean twin: `proof/ConRon/Arena/Env.lean:210-214 projTableName` — the
/// reserved name of structure `T`'s projection table.
pub fn proj_table_name(pers: &PersTier, ar: &mut EStore, t: &NIdx) -> Result<NIdx, CheckError> {
    const S: [u32; 9] = [112, 114, 111, 106, 84, 97, 98, 108, 101];
    match ar.intern_name(pers, NNodeView::Str(t.dup2(), core_types::code_points(&S))) {
        Err(e) => Err(e),
        Ok(s) => ar.intern_name(pers, NNodeView::Num(s, 0)),
    }
}

// ---------------------------------------------------------------------------
// Reading a stored constant (`Env.lean:226-264` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:639-642 ConstantInfo.toConstantVal
/// Lean twin: `proof/ConRon/Arena/Env.lean:218-229 IConstantInfo.toConstantVal`
/// — the constant's common data.  The `.projInfo` arm BUILDS the closed dummy
/// type `Sort 1`, which over handles means interning it: that is the one
/// reason this projection takes the store (the module note).  The table's own
/// name is the stored `table_name` and is not recomputed.
pub fn i_constant_info_to_constant_val(
    pers: &PersTier,
    ar: &mut EStore,
    c: &IConstantInfo,
) -> Result<IConstantVal, CheckError> {
    match c {
        IConstantInfo::AxiomInfo(v) => Ok(i_constant_val_dup(v)),
        IConstantInfo::DefnInfo(v, _, _) => Ok(i_constant_val_dup(v)),
        IConstantInfo::ThmInfo(v, _) => Ok(i_constant_val_dup(v)),
        IConstantInfo::IndInfo(v, _) => Ok(i_constant_val_dup(v)),
        IConstantInfo::CtorInfo(v, _, _) => Ok(i_constant_val_dup(v)),
        IConstantInfo::RecInfo(v, _, _, _) => Ok(i_constant_val_dup(v)),
        IConstantInfo::ProjInfo(tbl) => match ar.intern_level(pers, LNodeView::Zero) {
            Err(e) => Err(e),
            Ok(z) => match ar.intern_level(pers, LNodeView::Succ(z)) {
                Err(e) => Err(e),
                Ok(one) => match ar.intern(pers, ENodeView::Sort(one)) {
                    Err(e) => Err(e),
                    Ok(ty) => Ok(IConstantVal {
                        name: tbl.table_name.dup2(),
                        level_params: nidx_vec_dup(&tbl.level_params),
                        ty,
                    }),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:644 name
/// Lean twin: `proof/ConRon/Arena/Env.lean:231-238 IConstantInfo.name` — the
/// constant's name.  **PURE**, unlike `to_constant_val`: it is the environment
/// index's key, and `IProjTable.table_name` is the stored handle that makes it
/// so (the module note).
pub fn i_constant_info_name(c: &IConstantInfo) -> NIdx {
    match c {
        IConstantInfo::AxiomInfo(v) => v.name.dup2(),
        IConstantInfo::DefnInfo(v, _, _) => v.name.dup2(),
        IConstantInfo::ThmInfo(v, _) => v.name.dup2(),
        IConstantInfo::IndInfo(v, _) => v.name.dup2(),
        IConstantInfo::CtorInfo(v, _, _) => v.name.dup2(),
        IConstantInfo::RecInfo(v, _, _, _) => v.name.dup2(),
        IConstantInfo::ProjInfo(tbl) => tbl.table_name.dup2(),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:646-651 ConstantInfo.isTowerEntry
/// Lean twin: `proof/ConRon/Arena/Env.lean:240-244 IConstantInfo.isTowerEntry`
/// — a projection table is a table, not a term.
pub fn i_constant_info_is_tower_entry(c: &IConstantInfo) -> bool {
    match c {
        IConstantInfo::ProjInfo(_) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:653 ConstantInfo.type
/// Lean twin: `proof/ConRon/Arena/Env.lean:246-249 IConstantInfo.type` — the
/// constant's declared type.
pub fn i_constant_info_type(
    pers: &PersTier,
    ar: &mut EStore,
    c: &IConstantInfo,
) -> Result<EIdx, CheckError>  {
    match i_constant_info_to_constant_val(pers, ar, c) {
        Err(e) => Err(e),
        Ok(v) => Ok(v.ty),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:565-568 name
/// Lean twin: `proof/ConRon/Arena/Env.lean:251-257 IDeclaration.name` — the
/// name of a non-basis declaration.  con-leche's `.anonymous` fall-through is
/// the interned anonymous name here, which is why the store is in hand.
pub fn i_declaration_name(
    pers: &PersTier,
    ar: &mut EStore,
    d: &IDeclaration,
) -> Result<NIdx, CheckError>  {
    match d {
        IDeclaration::AxiomDecl(v) => Ok(v.name.dup2()),
        IDeclaration::DefnDecl(v, _, _) => Ok(v.name.dup2()),
        IDeclaration::ThmDecl(v, _) => Ok(v.name.dup2()),
        IDeclaration::OpaqueDecl(v, _) => Ok(v.name.dup2()),
        IDeclaration::QuotDecl(_, v) => Ok(v.name.dup2()),
        IDeclaration::BasisDecl(_) => ar.intern_name(pers, NNodeView::Anonymous),
        IDeclaration::IndDecl(_, _) => ar.intern_name(pers, NNodeView::Anonymous),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:659-670 Declaration.names
/// Lean twin: `proof/ConRon/Arena/Env.lean:259-266 IDeclaration.names` — the
/// names a declaration record declares; `prepare::prelude_key`'s lookup and
/// the ground hoist's name index read it.  **PURE**, because
/// `i_constant_info_name` is.
pub fn i_declaration_names(d: &IDeclaration) -> Vec<NIdx> {
    match d {
        IDeclaration::AxiomDecl(cv) => i_declaration_one_name(cv),
        IDeclaration::DefnDecl(cv, _, _) => i_declaration_one_name(cv),
        IDeclaration::ThmDecl(cv, _) => i_declaration_one_name(cv),
        IDeclaration::OpaqueDecl(cv, _) => i_declaration_one_name(cv),
        IDeclaration::QuotDecl(_, cv) => i_declaration_one_name(cv),
        IDeclaration::IndDecl(block, _) => i_constant_info_names_from(block, 0, Vec::new()),
        IDeclaration::BasisDecl(_) => Vec::new(),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:659-670 Declaration.names
/// The cited `[cv.name]`, as a function: §3.4 has no `vec!`.
pub fn i_declaration_one_name(cv: &IConstantVal) -> Vec<NIdx> {
    let mut out: Vec<NIdx> = Vec::with_capacity(1);
    out.push(cv.name.dup2());
    out
}

/// con-leche: ConLeche/Kernel/Env.lean:659-670 Declaration.names
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

/// con-leche: ConLeche/Kernel/Env.lean:674-679 Env
/// Lean twin: `proof/ConRon/Arena/Env.lean:270-275 IEnv` — the global
/// environment: the constants accepted so far.  Names are unique (the checker
/// rejects duplicates), so the order is irrelevant for lookup.
///
/// Deviation (the module note): the cited list is newest-first and this `Vec`
/// is **oldest-first**, because `Vec::push` appends; `i_env_find` scans from
/// the back, which is the cited order.
pub struct IEnv {
    pub consts: Vec<IConstantInfo>,
}

/// con-leche: ConLeche/Kernel/Env.lean:683-684 Env.empty
/// Lean twin: `proof/ConRon/Arena/Env.lean:277-279 IEnv.empty` — the empty
/// environment; the starting point of every checker run.
pub fn i_env_empty() -> IEnv {
    IEnv { consts: Vec::new() }
}

/// con-leche: ConLeche/Kernel/Env.lean:686-687 Env.find?
/// Lean twin: `proof/ConRon/Arena/Env.lean:281-286 IEnv.find?` — the linear
/// lookup.  A name comparison is a handle comparison, sound because `denoteN`
/// is injective (task #97a's `denoteN_inj`).
pub fn i_env_find<'a>(env: &'a IEnv, n: &NIdx) -> Option<&'a IConstantInfo> {
    i_env_find_from(&env.consts, env.consts.len(), n)
}

/// con-leche: ConLeche/Kernel/Env.lean:686-687 Env.find?
/// The index recursion the cited `List.find?` becomes, counting **down**:
/// `i_env_find_from(cs, i, n)` searches `cs[..i]` from the top, which is the
/// cited list from the front (the `IEnv` deviation).
pub fn i_env_find_from<'a>(
    cs: &'a Vec<IConstantInfo>,
    i: usize,
    n: &NIdx,
) -> Option<&'a IConstantInfo> {
    if i == 0 {
        None
    } else if i_constant_info_name(&cs[i - 1]).eq2(n) {
        Some(&cs[i - 1])
    } else {
        i_env_find_from(cs, i - 1, n)
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:689-695 Env.findProj?
/// Lean twin: `proof/ConRon/Arena/Env.lean:288-295 IEnv.findProj?` — the
/// projection-table entry for field `i` of `T`: the structure's table
/// (`proj_table_name T`), viewed at field `i`.  Takes the store only because
/// the reserved name has to be interned to be looked up.
pub fn i_env_find_proj(
    pers: &PersTier,
    ar: &mut EStore,
    env: &IEnv,
    t: &NIdx,
    i: u64,
) -> Result<Option<IProjEntry>, CheckError> {
    match proj_table_name(pers, ar, t) {
        Err(e) => Err(e),
        Ok(tn) => match i_env_find(env, &tn) {
            Some(IConstantInfo::ProjInfo(tbl)) => {
                if i < tbl.num_fields {
                    Ok(Some(i_proj_table_entry(tbl, i)))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        },
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:29-49 FEnv
/// Lean twin: `proof/ConRon/Arena/Env.lean:297-303 IFEnv` — the environment
/// with its `O(1)` index (DESIGN.md §8.3 lesson 13).  Entries with counter
/// `< visible_below` are visible; `visible_below` doubles as the next counter
/// `push` hands out.
///
/// **The READERS take the bound as a scalar** (`vis: u64`, task #97-P6-6b),
/// and this field is what phase A — which threads the record by value and
/// pushes into it — passes them.  Phase B passes `pc.vis` and never touches
/// the record, which is what lets `n` workers share one `&IFEnv`.
///
/// **The index row is `(counter, SLOT)` and not `(counter, IConstantInfo)`**
/// (task #97-P6-5, lever 1).  The twin's row carries the constant itself,
/// which in Lean is a shared value; in Rust it was a SECOND full copy of
/// every stored constant — `env.consts[s]` and `idx[name].1` held the same
/// record twice, both of them deep — and `ifenv_dup` therefore copied the
/// environment twice, each copy a `Vec<NIdx>` malloc per constant.  The
/// Mathlib profile of task #97-P6-5 put that at **19 % of the whole run**
/// (72 % of the install phase), because `arena::inductives` copies the
/// environment three times per inductive block and Mathlib has 6 720 of them
/// over a 691 128-entry environment.
///
/// The row is now the constant's SLOT in `env.consts`, so the map is a POD
/// and `dup` is a slot memcpy.  Every writer keeps the two in step —
/// `ifenv_push` pushes then indexes, `promote::index_promoted` writes the
/// slot back and re-indexes it, `promote::erase_installed` only removes — and
/// `ifenv_find` reads `env.consts[s]`.  The refinement relation for `IFEnv`
/// says `idx[n] = (c, s) ∧ consts[s] = ci` where the twin says
/// `idx[n] = (c, ci)`; no twin clause moves and `find?` answers the same
/// constant (task #97-P6-5's twin ledger).
pub struct IFEnv {
    pub env: IEnv,
    pub idx: HashMap<NIdx, (u64, u64)>,
    pub visible_below: u64,
}

/// con-leche: ConLeche/Kernel/FEnv.lean:51-60 mkFEnvGo
/// Lean twin: `proof/ConRon/Arena/Env.lean:305-312 mkIFEnvGo` — the index
/// build.  The cited recursion runs from the back of the newest-first list, so
/// that the newest constant is inserted last and wins, exactly as
/// `List.find?` takes the first match; over this `Vec`'s oldest-first order
/// that is increasing `i`, with the running counter threaded down.
pub fn mk_ifenv_go(
    cs: &Vec<IConstantInfo>,
    i: usize,
    c: u64,
    m: HashMap<NIdx, (u64, u64)>,
) -> (u64, HashMap<NIdx, (u64, u64)>) {
    if i >= cs.len() {
        (c, m)
    } else {
        let mut m = m;
        m.insert(i_constant_info_name(&cs[i]), (c, i as u64));
        mk_ifenv_go(cs, i + 1, c + 1, m)
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:62-66 mkFEnv
/// Lean twin: `proof/ConRon/Arena/Env.lean:314-318 mkIFEnv` — build the index
/// of `env`, with nothing hidden.  Takes the environment by value: the `IFEnv`
/// owns it.
pub fn mk_ifenv(env: IEnv) -> IFEnv {
    let p = mk_ifenv_go(&env.consts, 0, 0, HashMap::with_capacity(env.consts.len()));
    IFEnv {
        env,
        idx: p.1,
        visible_below: p.0,
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:70-75 FEnv.find?
/// Lean twin: `proof/ConRon/Arena/Env.lean:320-325 IFEnv.find?` — indexed
/// lookup, bounded by the visibility counter.
///
/// **The bound is a PARAMETER and not the record's field** (task #97-P6-6b).
/// The twin reads `fe.visibleBelow`; the Rust reads `vis`, because phase B's
/// `n` workers hold ONE `&IFEnv` between them and each checks its record at
/// its own prefix view (`pc.vis`).  Splitting the scalar out of the index is
/// what makes that possible: `check_pending` no longer takes the index by
/// value to restrict it, so a worker copies no environment at all.  Every
/// caller that still threads an environment BY VALUE — phase A's installs —
/// passes that record's own `visible_below`, so the function's answer is the
/// twin's `FEnv.find?` verbatim wherever the twin is what runs.
pub fn ifenv_find<'a>(vis: u64, fe: &'a IFEnv, n: &NIdx) -> Option<&'a IConstantInfo> {
    match fe.idx.get(n) {
        Some(e) => {
            if e.0 < vis && (e.1 as usize) < fe.env.consts.len() {
                Some(&fe.env.consts[e.1 as usize])
            } else {
                None
            }
        }
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:77-80 FEnv.restrictTo
/// Lean twin: `proof/ConRon/Arena/Env.lean:327-330 IFEnv.restrictTo` —
/// restrict the view to the first `k` installed constants; `O(1)`, a field
/// update.  Takes the record by value and returns it, which is what makes the
/// update `O(1)` in Rust (con-ron-core's `fenv` module note).
pub fn ifenv_restrict_to(fe: IFEnv, k: u64) -> IFEnv {
    let mut fe = fe;
    fe.visible_below = k;
    fe
}

/// con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push
/// Lean twin: `proof/ConRon/Arena/Env.lean:332-337 IFEnv.push` — the index of
/// the cons-extended environment: the new entry gets the next installation
/// counter and the visibility bound advances with it.
pub fn ifenv_push(fe: IFEnv, ci: IConstantInfo) -> IFEnv {
    let mut fe = fe;
    let c = fe.visible_below;
    let s = fe.env.consts.len() as u64;
    fe.idx.insert(i_constant_info_name(&ci), (c, s));
    fe.env.consts.push(ci);
    fe.visible_below = c + 1;
    fe
}

/// con-leche: ConLeche/Kernel/Env.lean:460-486 ConstantInfo
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

/// con-leche: ConLeche/Kernel/Env.lean:460-486 ConstantInfo
/// Lean twin: none — `core::clone::Clone` for `IConstantInfo`, which
/// `Vec::resize`'s signature demands (task #97-P6-5, lever 5).  It is
/// `i_constant_info_dup` and nothing else; no `#[derive]` (DESIGN.md §3.4).
impl core::clone::Clone for IConstantInfo {
    /// con-leche: ConLeche/Kernel/Env.lean:460-486 ConstantInfo
    fn clone(&self) -> IConstantInfo {
        i_constant_info_dup(self)
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push
/// Lean twin: `proof/ConRon/Arena/Env.lean:332-337 IFEnv.push` — **the push of
/// a TEMPORARY extension, with what it displaced** (task #97-P6-5, lever 4).
///
/// The twin writes `fe_r := fe.push stored` and goes on using `fe`, which in
/// Lean is free; in Rust that is `ifenv_push(ifenv_dup(fe), stored)`, an
/// `O(environment)` deep copy, and `arena::inductives` does it once per
/// inductive block over an environment that is 691 128 constants at the end
/// of Mathlib.  Where the extension is read-only and its lifetime is a
/// bracket — `check_native_rec_rules`'s recursor self-environment — the port
/// pushes in place and pops afterwards, which is `O(1)`.
///
/// The pop is EXACT and needs no side condition: `insert` hands back the row
/// it displaced (`None` when the name was fresh), so `ifenv_pop_temp` puts
/// that row back rather than assuming the name was new.  `pop (push fe ci) =
/// fe` is therefore an equation, which is what the refinement needs to keep
/// reading the twin's `fe` where the Rust reads the restored record.
pub fn ifenv_push_temp(fe: &mut IFEnv, ci: IConstantInfo) -> Option<(u64, u64)> {
    let c = fe.visible_below;
    let s = fe.env.consts.len() as u64;
    let prev = fe.idx.insert(i_constant_info_name(&ci), (c, s));
    fe.env.consts.push(ci);
    fe.visible_below = c + 1;
    prev
}

/// con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push
/// Lean twin: `proof/ConRon/Arena/Env.lean:332-337 IFEnv.push` — the inverse
/// of `ifenv_push_temp`: the constant popped, the displaced index row put
/// back, the visibility bound restored.  See that function's note.
pub fn ifenv_pop_temp(fe: &mut IFEnv, n: &NIdx, prev: Option<(u64, u64)>) {
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
    fe.visible_below = fe.visible_below - 1;
}

/// con-leche: ConLeche/Kernel/FEnv.lean:29-49 FEnv
/// Lean twin: none — a representation read (task #97-P6-5, lever 5).  The raw
/// index row under a name, VISIBLE OR NOT, which is what `ifenv_pop_temp` has
/// to put back when the caller pushed over it.  `ifenv_find` cannot serve: it
/// hides a row whose counter is at or above the visibility bound, and a hidden
/// row is exactly the one a naive pop would lose.
pub fn ifenv_row(fe: &IFEnv, n: &NIdx) -> Option<(u64, u64)> {
    match fe.idx.get(n) {
        Some(e) => Some(*e),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:91-95 FEnv.findProj?
/// Lean twin: `proof/ConRon/Arena/Env.lean:339-344 IFEnv.findProj?` — indexed
/// projection-table lookup.
pub fn ifenv_find_proj(
    pers: &PersTier,
    vis: u64,
    ar: &mut EStore,
    fe: &IFEnv,
    t: &NIdx,
    i: u64,
) -> Result<Option<IProjEntry>, CheckError> {
    match proj_table_name(pers, ar, t) {
        Err(e) => Err(e),
        Ok(tn) => match ifenv_find(vis, fe, &tn) {
            Some(IConstantInfo::ProjInfo(tbl)) => {
                if i < tbl.num_fields {
                    Ok(Some(i_proj_table_entry(tbl, i)))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        },
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

/// con-leche: ConLeche/Kernel/Env.lean:460-486 ConstantInfo
/// Lean twin: `proof/ConRon/Arena/Env.lean:173-183 IConstantInfo` — the
/// dictionary `ron::HashMap::dup` needs to copy an `IFEnv`'s index.
impl Dup for IConstantInfo {
    /// con-leche: ConLeche/Kernel/Env.lean:460-486 ConstantInfo
    fn dup2(&self) -> IConstantInfo {
        i_constant_info_dup(self)
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:677-679 Env
/// Lean twin: `proof/ConRon/Arena/Env.lean:270-275 IEnv` — the environment
/// copy Lean's value semantics gives for free.
pub fn i_env_dup(e: &IEnv) -> IEnv {
    IEnv {
        consts: i_constant_infos_dup(&e.consts),
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:29-49 FEnv
/// Lean twin: `proof/ConRon/Arena/Env.lean:297-303 IFEnv` — the indexed
/// environment's copy: the constants, the index and the visibility bound.
/// `O(size)`, as `con_ron_core::kernel::fenv::dup` is, and for the same reason
/// — but since task #97-P6-5's lever 1 the index half is a **slot memcpy**
/// and not a second deep copy of every constant, so the cost is one
/// `IConstantInfo` copy per constant instead of two.  The five callers are
/// all in `arena::inductives`, where a block is checked against an extended
/// environment while the original has to survive.
pub fn ifenv_dup(fe: &IFEnv) -> IFEnv {
    IFEnv {
        env: i_env_dup(&fe.env),
        idx: fe.idx.dup(),
        visible_below: fe.visible_below,
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:70-75 FEnv.find?
/// Lean twin: `proof/ConRon/Arena/Env.lean:320-325 IFEnv.find?` — **the stored
/// constant, COPIED.**  Every reader whose answer outlives a `&mut st` pays the
/// copy (task #97-P4c's row); written INLINE, the `Option`-producing match
/// leaves Aeneas with two loan contexts it cannot join (*"Could not match the
/// contexts"*, `interp/Interp.ml:617`), which is task #97-P4c's extraction
/// rule 5 at an `ifenv_find` rather than at a `HashMap::get`.  So the copy is
/// one function and is never inlined.
pub fn find_ci(vis: u64, fe: &IFEnv, n: &NIdx) -> Option<IConstantInfo> {
    match ifenv_find(vis, fe, n) {
        Some(ci) => Some(i_constant_info_dup(ci)),
        None => None,
    }
}

// ---------------------------------------------------------------------------
// `Monad.lean`'s primitives, pending `arena/monad.rs` (task #97 P4b)
//
// `view`, `viewN`, `readName` and `readLevel` are `Arena/Monad.lean`'s, whose
// Rust home is `arena/monad.rs`.  This module (`pi_sort_tele_len`) and
// `frontend/` (the error text, `parse_pw_d`, `k_expected_of`) need four of
// them today; they are spelled here, together, and move when that module
// lands.  The two readbacks are `Denote.lean`'s `denoteN`/`denoteL`, fuel and
// all, which task #97-P4a kept in `mod tests` because nothing shipped needed
// them.
// ---------------------------------------------------------------------------

/// con-leche: none — the port's own dangling-handle guard; Lean twin: proof/ConRon/Arena/Monad.lean:157-164 view
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

/// con-leche: none — the port's own dangling-handle guard; Lean twin: proof/ConRon/Arena/Monad.lean:403-408 viewN
/// Decode a name handle.
pub fn view_n(pers: &PersTier, ar: &EStore, h: &NIdx) -> Result<NNodeView, CheckError> {
    match ar.ns().view(pers, h) {
        Some(v) => Ok(v),
        None => Err(dangling_name()),
    }
}

/// con-leche: none — the port's own dangling-handle guard; Lean twin: proof/ConRon/Arena/Monad.lean:403-408 viewN
/// `"arena: dangling name handle"`, named once: `view_n` and `read_name` raise
/// the same error, as the twin's two primitives do.
pub fn dangling_name() -> CheckError {
    const M: [u32; 27] = [
        97, 114, 101, 110, 97, 58, 32, 100, 97, 110, 103, 108, 105, 110, 103, 32, 110, 97, 109,
        101, 32, 104, 97, 110, 100, 108, 101,
    ];
    core_types::internal(core_types::code_points(&M))
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Monad.lean:428-436 readName` — read a name
/// back out of the store as a transient `Name`.  Names are compared by handle
/// throughout the checker (DESIGN.md §8.3), so this is the error-text and
/// level-substitution path only, and the readback IS the denotation
/// (`Denote.lean`'s `denoteN`).
pub fn read_name(pers: &PersTier, ar: &EStore, h: &NIdx) -> Result<Name, CheckError> {
    read_name_at(pers, ar, ar.ns().node_count(pers) as u64 + 1, h)
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
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

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Monad.lean:438-447 readNames` — read a LIST
/// of name handles back.  `ks.mapM readName` would do it with a closure, which
/// DESIGN.md §3.4 forbids, so this is the cursor recursion.
pub fn read_names(pers: &PersTier, ar: &EStore, hs: &Vec<NIdx>) -> Result<Vec<Name>, CheckError> {
    read_names_from(pers, ar, hs, 0, Vec::with_capacity(hs.len()))
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// The cursor recursion behind `read_names`.
pub fn read_names_from(
    pers: &PersTier,
    ar: &EStore,
    hs: &Vec<NIdx>,
    i: usize,
    out: Vec<Name>,
) -> Result<Vec<Name>, CheckError> {
    if i >= hs.len() {
        Ok(out)
    } else {
        match read_name(pers, ar, &hs[i]) {
            Err(e) => Err(e),
            Ok(x) => {
                let mut out = out;
                out.push(x);
                read_names_from(pers, ar, hs, i + 1, out)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:26-37 subst
/// Lean twin: `proof/ConRon/Arena/Monad.lean:495-504 readLevel` — **the
/// readback** (DESIGN.md §8.3 lesson 4, "intern the representation, not the
/// algorithm"): a level ALGORITHM runs on a transient `Level` tree read out of
/// the store, never on handles.  The readback is `denoteL` itself.
pub fn read_level(pers: &PersTier, ar: &EStore, h: &LIdx) -> Result<Level, CheckError> {
    read_level_at(pers, ar, ar.ls().node_count(pers) as u64 + 1, h)
}

/// con-leche: ConLeche/Kernel/Level.lean:26-37 subst
/// The fuel-indexed readback itself (`Denote.lean`'s `denoteLAux`).
pub fn read_level_at(
    pers: &PersTier,
    ar: &EStore,
    fuel: u64,
    h: &LIdx,
) -> Result<Level, CheckError>  {
    if fuel == 0 {
        return Err(dangling_level());
    }
    match ar.ls().view(pers, h) {
        None => Err(dangling_level()),
        Some(LNodeView::Zero) => Ok(level::zero()),
        Some(LNodeView::Succ(u)) => match read_level_at(pers, ar, fuel - 1, &u) {
            Err(e) => Err(e),
            Ok(a) => Ok(level::succ(a)),
        },
        Some(LNodeView::Max(u, v)) => match read_level_at(pers, ar, fuel - 1, &u) {
            Err(e) => Err(e),
            Ok(a) => match read_level_at(pers, ar, fuel - 1, &v) {
                Err(e) => Err(e),
                Ok(b) => Ok(level::max(a, b)),
            },
        },
        Some(LNodeView::Imax(u, v)) => match read_level_at(pers, ar, fuel - 1, &u) {
            Err(e) => Err(e),
            Ok(a) => match read_level_at(pers, ar, fuel - 1, &v) {
                Err(e) => Err(e),
                Ok(b) => Ok(level::imax(a, b)),
            },
        },
        Some(LNodeView::Param(n)) => match read_name(pers, ar, &n) {
            Err(e) => Err(e),
            Ok(x) => Ok(level::param(x)),
        },
    }
}

/// con-leche: none — the port's own dangling-handle guard; Lean twin: proof/ConRon/Arena/Monad.lean:462-468 viewL
/// `"arena: dangling level handle"`, named once.
pub fn dangling_level() -> CheckError {
    const M: [u32; 28] = [
        97, 114, 101, 110, 97, 58, 32, 100, 97, 110, 103, 108, 105, 110, 103, 32, 108, 101, 118,
        101, 108, 32, 104, 97, 110, 100, 108, 101,
    ];
    core_types::internal(core_types::code_points(&M))
}

// ---------------------------------------------------------------------------
// The syntactic Π-telescope (`Env.lean:357-360` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:572-586 Expr.piSortTeleLen?
/// Lean twin: `proof/ConRon/Arena/Env.lean:348-358 piSortTeleLen?` — the
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
        Ok(ENodeView::ForallE(_, body, _)) => match pi_sort_tele_len(pers, ar, fuel - 1, &body) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some(n)) => Ok(Some(n + 1)),
        },
        Ok(ENodeView::Sort(_)) => Ok(Some(0)),
        Ok(_) => Ok(None),
    }
}

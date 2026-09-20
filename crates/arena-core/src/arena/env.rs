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
//! * **the index copies the record** where Lean's value semantics share it.
//!   con-ron-core stores a `P<ConstantInfo>` in both `Env` and `FEnv`; DESIGN
//!   §8.5 says the arena has **no `ron::ptr`** at all, so `IFEnv`'s index
//!   holds its own copy — which for a handle-shaped record is a `Vec` spine
//!   and no term at all.  Whether that is what P2c wants of the index is
//!   P2c's measurement, not part 1's.
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
use con_ron_core::kernel::core_types;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env::{QuotKind, ReducibilityHint};
use con_ron_core::kernel::level;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::Name;
use con_ron_core::kernel::prop_when;
use con_ron_core::kernel::prop_when::PropWhen;
use con_ron_core::ron::hashmap::{Dup, Eq2, HashMap};

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
/// Lean twin: `proof/ConRon/Arena/Env.lean:73-77 IConstantVal` — data common
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
/// Lean twin: `proof/ConRon/Arena/Env.lean:84-88 IRecRuleFire` — how a stored
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
/// Lean twin: `proof/ConRon/Arena/Env.lean:94-103 IRecRule` — one iota rule of
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
/// Lean twin: `proof/ConRon/Arena/Env.lean:107-110 IRecRule.compareParams` —
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
/// Lean twin: `proof/ConRon/Arena/Env.lean:117-131 IIndCaps` — the
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
/// Lean twin: `proof/ConRon/Arena/Env.lean:137-155 IProjTable` — one
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
/// Lean twin: `proof/ConRon/Arena/Env.lean:159-171 IProjEntry` — the per-field
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
/// Lean twin: `proof/ConRon/Arena/Env.lean:175-177 IProjTable.entry` — the
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
/// Lean twin: `proof/ConRon/Arena/Env.lean:183-191 IConstantInfo` — the
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
            con_ron_core::kernel::env::reducibility_hint_dup(h),
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
/// Lean twin: `proof/ConRon/Arena/Env.lean:198-206 IDeclaration` — a
/// declaration presented to the checker, over handles.  Seven constructors,
/// con-leche's own order; the frontend produces every one but `BasisDecl`,
/// which is the fold's own record for "install the pinned basis block".
pub enum IDeclaration {
    AxiomDecl(IConstantVal),
    DefnDecl(IConstantVal, EIdx, ReducibilityHint),
    ThmDecl(IConstantVal, EIdx),
    OpaqueDecl(IConstantVal, EIdx),
    BasisDecl(con_ron_core::kernel::env::BasisKind),
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
            con_ron_core::kernel::env::reducibility_hint_dup(h),
        ),
        IDeclaration::ThmDecl(cv, v) => IDeclaration::ThmDecl(i_constant_val_dup(cv), v.dup2()),
        IDeclaration::OpaqueDecl(cv, v) => {
            IDeclaration::OpaqueDecl(i_constant_val_dup(cv), v.dup2())
        }
        IDeclaration::BasisDecl(k) => {
            IDeclaration::BasisDecl(con_ron_core::kernel::env::basis_kind_dup(k))
        }
        IDeclaration::IndDecl(bl, n) => IDeclaration::IndDecl(i_constant_infos_dup(bl), *n),
        IDeclaration::QuotDecl(k, cv) => IDeclaration::QuotDecl(
            con_ron_core::kernel::env::quot_kind_dup(k),
            i_constant_val_dup(cv),
        ),
    }
}

// ---------------------------------------------------------------------------
// The reserved names (`Env.lean:212-222` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:623-629 projFnName
/// Lean twin: `proof/ConRon/Arena/Env.lean:212-215 projFnName` — the public
/// projection-*function* name for field `i` of structure `T`.  Building a name
/// means interning it, so the twin is monadic and this takes the store.
pub fn proj_fn_name(ar: &mut EStore, t: &NIdx, i: u64) -> Result<NIdx, CheckError> {
    const S: [u32; 4] = [112, 114, 111, 106];
    match ar.intern_name(NNodeView::Str(t.dup2(), core_types::code_points(&S))) {
        Err(e) => Err(e),
        Ok(s) => ar.intern_name(NNodeView::Num(s, i)),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:631-635 projTableName
/// Lean twin: `proof/ConRon/Arena/Env.lean:219-222 projTableName` — the
/// reserved name of structure `T`'s projection table.
pub fn proj_table_name(ar: &mut EStore, t: &NIdx) -> Result<NIdx, CheckError> {
    const S: [u32; 9] = [112, 114, 111, 106, 84, 97, 98, 108, 101];
    match ar.intern_name(NNodeView::Str(t.dup2(), core_types::code_points(&S))) {
        Err(e) => Err(e),
        Ok(s) => ar.intern_name(NNodeView::Num(s, 0)),
    }
}

// ---------------------------------------------------------------------------
// Reading a stored constant (`Env.lean:226-264` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:639-642 ConstantInfo.toConstantVal
/// Lean twin: `proof/ConRon/Arena/Env.lean:229-236 IConstantInfo.toConstantVal`
/// — the constant's common data.  The `.projInfo` arm BUILDS the closed dummy
/// type `Sort 1`, which over handles means interning it: that is the one
/// reason this projection takes the store (the module note).  The table's own
/// name is the stored `table_name` and is not recomputed.
pub fn i_constant_info_to_constant_val(
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
        IConstantInfo::ProjInfo(tbl) => match ar.intern_level(LNodeView::Zero) {
            Err(e) => Err(e),
            Ok(z) => match ar.intern_level(LNodeView::Succ(z)) {
                Err(e) => Err(e),
                Ok(one) => match ar.intern(ENodeView::Sort(one)) {
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
/// Lean twin: `proof/ConRon/Arena/Env.lean:242-245 IConstantInfo.name` — the
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
/// Lean twin: `proof/ConRon/Arena/Env.lean:249-251 IConstantInfo.isTowerEntry`
/// — a projection table is a table, not a term.
pub fn i_constant_info_is_tower_entry(c: &IConstantInfo) -> bool {
    match c {
        IConstantInfo::ProjInfo(_) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:653 ConstantInfo.type
/// Lean twin: `proof/ConRon/Arena/Env.lean:255-256 IConstantInfo.type` — the
/// constant's declared type.
pub fn i_constant_info_type(ar: &mut EStore, c: &IConstantInfo) -> Result<EIdx, CheckError> {
    match i_constant_info_to_constant_val(ar, c) {
        Err(e) => Err(e),
        Ok(v) => Ok(v.ty),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:565-568 name
/// Lean twin: `proof/ConRon/Arena/Env.lean:260-264 IDeclaration.name` — the
/// name of a non-basis declaration.  con-leche's `.anonymous` fall-through is
/// the interned anonymous name here, which is why the store is in hand.
pub fn i_declaration_name(ar: &mut EStore, d: &IDeclaration) -> Result<NIdx, CheckError> {
    match d {
        IDeclaration::AxiomDecl(v) => Ok(v.name.dup2()),
        IDeclaration::DefnDecl(v, _, _) => Ok(v.name.dup2()),
        IDeclaration::ThmDecl(v, _) => Ok(v.name.dup2()),
        IDeclaration::OpaqueDecl(v, _) => Ok(v.name.dup2()),
        IDeclaration::QuotDecl(_, v) => Ok(v.name.dup2()),
        IDeclaration::BasisDecl(_) => ar.intern_name(NNodeView::Anonymous),
        IDeclaration::IndDecl(_, _) => ar.intern_name(NNodeView::Anonymous),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:659-670 Declaration.names
/// Lean twin: `proof/ConRon/Arena/Env.lean:268-273 IDeclaration.names` — the
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
/// Lean twin: `proof/ConRon/Arena/Env.lean:280-282 IEnv` — the global
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
/// Lean twin: `proof/ConRon/Arena/Env.lean:286-287 IEnv.empty` — the empty
/// environment; the starting point of every checker run.
pub fn i_env_empty() -> IEnv {
    IEnv { consts: Vec::new() }
}

/// con-leche: ConLeche/Kernel/Env.lean:686-687 Env.find?
/// Lean twin: `proof/ConRon/Arena/Env.lean:292-293 IEnv.find?` — the linear
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
/// Lean twin: `proof/ConRon/Arena/Env.lean:299-303 IEnv.findProj?` — the
/// projection-table entry for field `i` of `T`: the structure's table
/// (`proj_table_name T`), viewed at field `i`.  Takes the store only because
/// the reserved name has to be interned to be looked up.
pub fn i_env_find_proj(
    ar: &mut EStore,
    env: &IEnv,
    t: &NIdx,
    i: u64,
) -> Result<Option<IProjEntry>, CheckError> {
    match proj_table_name(ar, t) {
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
/// Lean twin: `proof/ConRon/Arena/Env.lean:309-312 IFEnv` — the environment
/// with its `O(1)` index (DESIGN.md §8.3 lesson 13).  Entries with counter
/// `< visible_below` are visible; `visible_below` doubles as the next counter
/// `push` hands out.
pub struct IFEnv {
    pub env: IEnv,
    pub idx: HashMap<NIdx, (u64, IConstantInfo)>,
    pub visible_below: u64,
}

/// con-leche: ConLeche/Kernel/FEnv.lean:51-60 mkFEnvGo
/// Lean twin: `proof/ConRon/Arena/Env.lean:317-321 mkIFEnvGo` — the index
/// build.  The cited recursion runs from the back of the newest-first list, so
/// that the newest constant is inserted last and wins, exactly as
/// `List.find?` takes the first match; over this `Vec`'s oldest-first order
/// that is increasing `i`, with the running counter threaded down.
pub fn mk_ifenv_go(
    cs: &Vec<IConstantInfo>,
    i: usize,
    c: u64,
    m: HashMap<NIdx, (u64, IConstantInfo)>,
) -> (u64, HashMap<NIdx, (u64, IConstantInfo)>) {
    if i >= cs.len() {
        (c, m)
    } else {
        let mut m = m;
        m.insert(
            i_constant_info_name(&cs[i]),
            (c, i_constant_info_dup(&cs[i])),
        );
        mk_ifenv_go(cs, i + 1, c + 1, m)
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:62-66 mkFEnv
/// Lean twin: `proof/ConRon/Arena/Env.lean:325-327 mkIFEnv` — build the index
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
/// Lean twin: `proof/ConRon/Arena/Env.lean:331-334 IFEnv.find?` — indexed
/// lookup, bounded by the visibility counter.
pub fn ifenv_find<'a>(fe: &'a IFEnv, n: &NIdx) -> Option<&'a IConstantInfo> {
    match fe.idx.get(n) {
        Some(e) => {
            if e.0 < fe.visible_below {
                Some(&e.1)
            } else {
                None
            }
        }
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:77-80 FEnv.restrictTo
/// Lean twin: `proof/ConRon/Arena/Env.lean:338-339 IFEnv.restrictTo` —
/// restrict the view to the first `k` installed constants; `O(1)`, a field
/// update.  Takes the record by value and returns it, which is what makes the
/// update `O(1)` in Rust (con-ron-core's `fenv` module note).
pub fn ifenv_restrict_to(fe: IFEnv, k: u64) -> IFEnv {
    let mut fe = fe;
    fe.visible_below = k;
    fe
}

/// con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push
/// Lean twin: `proof/ConRon/Arena/Env.lean:344-346 IFEnv.push` — the index of
/// the cons-extended environment: the new entry gets the next installation
/// counter and the visibility bound advances with it.
pub fn ifenv_push(fe: IFEnv, ci: IConstantInfo) -> IFEnv {
    let mut fe = fe;
    let c = fe.visible_below;
    fe.idx
        .insert(i_constant_info_name(&ci), (c, i_constant_info_dup(&ci)));
    fe.env.consts.push(ci);
    fe.visible_below = c + 1;
    fe
}

/// con-leche: ConLeche/Kernel/FEnv.lean:91-95 FEnv.findProj?
/// Lean twin: `proof/ConRon/Arena/Env.lean:350-353 IFEnv.findProj?` — indexed
/// projection-table lookup.
pub fn ifenv_find_proj(
    ar: &mut EStore,
    fe: &IFEnv,
    t: &NIdx,
    i: u64,
) -> Result<Option<IProjEntry>, CheckError> {
    match proj_table_name(ar, t) {
        Err(e) => Err(e),
        Ok(tn) => match ifenv_find(fe, &tn) {
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
/// Lean twin: `proof/ConRon/Arena/Env.lean:183-191 IConstantInfo` — the
/// dictionary `ron::HashMap::dup` needs to copy an `IFEnv`'s index.
impl Dup for IConstantInfo {
    /// con-leche: ConLeche/Kernel/Env.lean:460-486 ConstantInfo
    fn dup2(&self) -> IConstantInfo {
        i_constant_info_dup(self)
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:677-679 Env
/// Lean twin: `proof/ConRon/Arena/Env.lean:280-282 IEnv` — the environment
/// copy Lean's value semantics gives for free.
pub fn i_env_dup(e: &IEnv) -> IEnv {
    IEnv {
        consts: i_constant_infos_dup(&e.consts),
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:29-49 FEnv
/// Lean twin: `proof/ConRon/Arena/Env.lean:309-312 IFEnv` — the indexed
/// environment's copy: the constants, the index and the visibility bound.
/// `O(size)`, as `con_ron_core::kernel::fenv::dup` is, and for the same reason.
pub fn ifenv_dup(fe: &IFEnv) -> IFEnv {
    IFEnv {
        env: i_env_dup(&fe.env),
        idx: fe.idx.dup(),
        visible_below: fe.visible_below,
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:70-75 FEnv.find?
/// Lean twin: `proof/ConRon/Arena/Env.lean:331-334 IFEnv.find?` — **the stored
/// constant, COPIED.**  Every reader whose answer outlives a `&mut st` pays the
/// copy (task #97-P4c's row); written INLINE, the `Option`-producing match
/// leaves Aeneas with two loan contexts it cannot join (*"Could not match the
/// contexts"*, `interp/Interp.ml:617`), which is task #97-P4c's extraction
/// rule 5 at an `ifenv_find` rather than at a `HashMap::get`.  So the copy is
/// one function and is never inlined.
pub fn find_ci(fe: &IFEnv, n: &NIdx) -> Option<IConstantInfo> {
    match ifenv_find(fe, n) {
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

/// con-leche: none — the port's own dangling-handle guard; Lean twin: proof/ConRon/Arena/Monad.lean:133-138 view
/// Decode an expression handle.  A dangling handle is an internal error: the
/// checker never builds one, and the bridge claims nothing on failure.
pub fn view_e(ar: &EStore, h: &EIdx) -> Result<ENodeView, CheckError> {
    match ar.view(h) {
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

/// con-leche: none — the port's own dangling-handle guard; Lean twin: proof/ConRon/Arena/Monad.lean:158-162 viewN
/// Decode a name handle.
pub fn view_n(ar: &EStore, h: &NIdx) -> Result<NNodeView, CheckError> {
    match ar.ns().view(h) {
        Some(v) => Ok(v),
        None => Err(dangling_name()),
    }
}

/// con-leche: none — the port's own dangling-handle guard; Lean twin: proof/ConRon/Arena/Monad.lean:158-162 viewN
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
/// Lean twin: `proof/ConRon/Arena/Monad.lean:180-184 readName` — read a name
/// back out of the store as a transient `Name`.  Names are compared by handle
/// throughout the checker (DESIGN.md §8.3), so this is the error-text and
/// level-substitution path only, and the readback IS the denotation
/// (`Denote.lean`'s `denoteN`).
pub fn read_name(ar: &EStore, h: &NIdx) -> Result<Name, CheckError> {
    read_name_at(ar, ar.ns().node_count() as u64 + 1, h)
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// The fuel-indexed readback itself (`Denote.lean`'s `denoteNAux`): the store's
/// name-node count bounds every path, because a prefix is interned before the
/// name that carries it.
pub fn read_name_at(ar: &EStore, fuel: u64, h: &NIdx) -> Result<Name, CheckError> {
    if fuel == 0 {
        return Err(dangling_name());
    }
    match ar.ns().view(h) {
        None => Err(dangling_name()),
        Some(NNodeView::Anonymous) => Ok(name::anonymous()),
        Some(NNodeView::Str(p, s)) => match read_name_at(ar, fuel - 1, &p) {
            Err(e) => Err(e),
            Ok(q) => Ok(name::mk_str(q, s)),
        },
        Some(NNodeView::Num(p, n)) => match read_name_at(ar, fuel - 1, &p) {
            Err(e) => Err(e),
            Ok(q) => Ok(name::mk_num(q, n)),
        },
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// Lean twin: `proof/ConRon/Arena/Monad.lean:188-194 readNames` — read a LIST
/// of name handles back.  `ks.mapM readName` would do it with a closure, which
/// DESIGN.md §3.4 forbids, so this is the cursor recursion.
pub fn read_names(ar: &EStore, hs: &Vec<NIdx>) -> Result<Vec<Name>, CheckError> {
    read_names_from(ar, hs, 0, Vec::with_capacity(hs.len()))
}

/// con-leche: ConLeche/Kernel/Name.lean:34-37 Name
/// The cursor recursion behind `read_names`.
pub fn read_names_from(
    ar: &EStore,
    hs: &Vec<NIdx>,
    i: usize,
    out: Vec<Name>,
) -> Result<Vec<Name>, CheckError> {
    if i >= hs.len() {
        Ok(out)
    } else {
        match read_name(ar, &hs[i]) {
            Err(e) => Err(e),
            Ok(x) => {
                let mut out = out;
                out.push(x);
                read_names_from(ar, hs, i + 1, out)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:26-37 subst
/// Lean twin: `proof/ConRon/Arena/Monad.lean:233-238 readLevel` — **the
/// readback** (DESIGN.md §8.3 lesson 4, "intern the representation, not the
/// algorithm"): a level ALGORITHM runs on a transient `Level` tree read out of
/// the store, never on handles.  The readback is `denoteL` itself.
pub fn read_level(ar: &EStore, h: &LIdx) -> Result<Level, CheckError> {
    read_level_at(ar, ar.ls().node_count() as u64 + 1, h)
}

/// con-leche: ConLeche/Kernel/Level.lean:26-37 subst
/// The fuel-indexed readback itself (`Denote.lean`'s `denoteLAux`).
pub fn read_level_at(ar: &EStore, fuel: u64, h: &LIdx) -> Result<Level, CheckError> {
    if fuel == 0 {
        return Err(dangling_level());
    }
    match ar.ls().view(h) {
        None => Err(dangling_level()),
        Some(LNodeView::Zero) => Ok(level::zero()),
        Some(LNodeView::Succ(u)) => match read_level_at(ar, fuel - 1, &u) {
            Err(e) => Err(e),
            Ok(a) => Ok(level::succ(a)),
        },
        Some(LNodeView::Max(u, v)) => match read_level_at(ar, fuel - 1, &u) {
            Err(e) => Err(e),
            Ok(a) => match read_level_at(ar, fuel - 1, &v) {
                Err(e) => Err(e),
                Ok(b) => Ok(level::max(a, b)),
            },
        },
        Some(LNodeView::Imax(u, v)) => match read_level_at(ar, fuel - 1, &u) {
            Err(e) => Err(e),
            Ok(a) => match read_level_at(ar, fuel - 1, &v) {
                Err(e) => Err(e),
                Ok(b) => Ok(level::imax(a, b)),
            },
        },
        Some(LNodeView::Param(n)) => match read_name(ar, &n) {
            Err(e) => Err(e),
            Ok(x) => Ok(level::param(x)),
        },
    }
}

/// con-leche: none — the port's own dangling-handle guard; Lean twin: proof/ConRon/Arena/Monad.lean:213-217 viewL
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
/// Lean twin: `proof/ConRon/Arena/Env.lean:355-360 piSortTeleLen?` — the
/// length of a syntactic Π-telescope ending in a SORT.  A spine walk, so the
/// fuel is the store's node count; con-leche's structural recursion is the
/// same walk with the node read through `view`.
pub fn pi_sort_tele_len(ar: &EStore, fuel: u64, h: &EIdx) -> Result<Option<u64>, CheckError> {
    if fuel == 0 {
        const M: [u32; 34] = [
            102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 112, 105,
            83, 111, 114, 116, 84, 101, 108, 101, 76, 101, 110, 63, 32, 40, 69, 41,
        ];
        return Err(core_types::internal(core_types::code_points(&M)));
    }
    match view_e(ar, h) {
        Err(e) => Err(e),
        Ok(ENodeView::ForallE(_, body, _)) => match pi_sort_tele_len(ar, fuel - 1, &body) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some(n)) => Ok(Some(n + 1)),
        },
        Ok(ENodeView::Sort(_)) => Ok(Some(0)),
        Ok(_) => Ok(None),
    }
}

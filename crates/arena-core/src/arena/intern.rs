//! `arena::intern` — con-ron-core's pinned VALUES into the store.
//!
//! The Rust twin of `proof/ConRon/Arena/Intern.lean` (the five fresh-memo
//! entry points) over `proof/ConRon/Arena/Frontend/Readback.lean`'s interning
//! walk, which is the function they delegate to.  DESIGN.md §8.3's lesson 4 —
//! "intern the representation, not the algorithm" — applied to the checker's
//! PINNED DATA.
//!
//! ## Where the data comes from, and why it is not a twin
//!
//! Three families of con-leche declaration are pure `Expr` / `ConstantInfo`
//! *values* written out by hand or spliced by an elaborator: the basis blocks
//! (`BasisKind.decls` / `declsA`), the standard- and compiler-trust axiom pins,
//! and the `Nat`-operation pin variants.  DESIGN.md §8.7's ruling is that (B)
//! IMPORTS con-leche's representation-free data rather than copying it, so the
//! Lean twin's pin modules are one line each: the con-leche constant, interned.
//!
//! The Rust cannot import con-leche, but it does not have to: **`con-ron-core`
//! already carries every one of those values** — `kernel::basis_raw` and
//! `kernel::basis_tables` (generated from `BasisKind.decls`/`declsA` at task
//! #22), `kernel::std_axioms`, `kernel::trust_axioms`, `kernel::trust_pins`,
//! and `kernel::pins_decode::decode` of the embedded `kernel::pins_text::
//! PINS_TEXT` for the pin variants (task #43).  So the arena's pin modules are
//! one line each here too: the con-ron-core constant, interned by this module.
//! A pin is therefore the *same value* on both sides of the differential test
//! by construction, not by two agreeing transcriptions.
//!
//! ## The walk is memoised, and each entry point starts fresh
//!
//! A value read out of con-ron-core is a counted-pointer DAG whose subterms are
//! shared; interning it structurally would walk each shared subterm once per
//! occurrence, which is what task #97e part 2 memoised the Lean walk for.  The
//! memo is a `ron::HashMap<Expr, EIdx>` threaded explicitly, exactly as
//! `con_ron_core::kernel::decl_check::consts_resolve_f_go` threads its
//! `HashMap<Expr, bool>`; the four LEAF arms (`bvar`, `sort`, `const`, `lit`)
//! bypass it, as the twin's do.  `Intern.lean`'s five entry points each start
//! from `∅`, so that neither side owns the other's memo, and this module's do
//! the same.
//!
//! **The tier matters.**  A pin interned while the scratch tier is live would
//! go with the tier and the environment would hold a dangling handle; the
//! startup walk (`arena::checker`'s `intern_all_pins`) runs before the first
//! `enter_scratch`, and after it a later `intern` of the same node probes the
//! persistent cons table first and hands back the persistent handle whatever
//! tier is live (DESIGN.md §8.3).

use crate::arena::env::{
    IConstantInfo, IConstantVal, IDeclaration, IIndCaps, IProjTable, IRecRule, IRecRuleFire,
};
use crate::arena::handle::{EIdx, LIdx, NIdx};
use crate::arena::monad::{intern_e, intern_level, intern_levels, intern_name, AState};
use crate::arena::store::ENodeView;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env as cenv;
use con_ron_core::kernel::env::{ConstantInfo, ConstantVal, Declaration, IndCaps, ProjTable, RecRule, RecRuleFire};
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::{Expr, ExprView};
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::name::Name;
use con_ron_core::kernel::prop_when;
use con_ron_core::ron::hashmap::{Dup, HashMap};

/// con-leche: none — the interning walk's memo; Lean twin: proof/ConRon/Arena/Frontend/Readback.lean:455-462 EMemo
/// The memo of the interning walk: a transient `Expr` node to the handle it
/// was interned at.  Keyed on the VALUE (`expr::data`'s hash and
/// `expr::beq`), which is what makes a shared subterm cost one probe.
pub type EMemo = HashMap<Expr, EIdx>;

/// con-leche: none — a fresh memo; Lean twin: proof/ConRon/Arena/Frontend/Readback.lean:455-462 EMemo
/// The `∅` every `Intern.lean` entry point starts from.
pub fn memo_empty() -> EMemo {
    HashMap::new()
}

/// con-leche: none — probe the interning memo; Lean twin: proof/ConRon/Arena/Frontend/Readback.lean:464-523 internExprGo
/// The `m[e]?` of the walk, as its own function: a `HashMap::get` match that
/// produces a value is never inlined (task #97-P4c's extraction rule 5).
pub fn memo_get(m: &EMemo, e: &Expr) -> Option<EIdx> {
    match m.get(e) {
        Some(h) => Some(h.dup2()),
        None => None,
    }
}

/// con-leche: none — intern a transient expression DAG; Lean twin: proof/ConRon/Arena/Frontend/Readback.lean:464-523 internExprGo
/// **The interning walk.**  The four leaf arms intern directly (they are
/// `O(1)` and a memo row would cost more than it saves — the twin's own
/// arrangement); every other arm probes the memo first and records its answer.
/// The memo is threaded as a `&mut`, where the twin threads it as an argument
/// and a result: the same table, one borrow (`con_ron_core::kernel::
/// decl_check::consts_resolve_f_go`'s shape).
pub fn intern_expr_go(st: &mut AState, m: &mut EMemo, e: &Expr) -> Result<EIdx, CheckError> {
    match expr::view(e) {
        ExprView::Bvar(i) => intern_e(st, ENodeView::BVar(*i)),
        ExprView::Sort(u) => match intern_level(st, u) {
            Err(err) => Err(err),
            Ok(hu) => intern_e(st, ENodeView::Sort(hu)),
        },
        ExprView::Const(n, us) => match intern_name(st, n) {
            Err(err) => Err(err),
            Ok(hn) => match intern_levels(st, us) {
                Err(err) => Err(err),
                Ok(hus) => intern_e(st, ENodeView::Const(hn, hus)),
            },
        },
        ExprView::Lit(l) => intern_e(st, ENodeView::Lit(expr::literal_dup(l))),
        _ => match memo_get(m, e) {
            Some(h) => Ok(h),
            None => match intern_expr_node(st, m, e) {
                Err(err) => Err(err),
                Ok(h) => {
                    m.insert(expr::dup(e), h.dup2());
                    Ok(h)
                }
            },
        },
    }
}

/// con-leche: none — the non-leaf arms of the interning walk; Lean twin: proof/ConRon/Arena/Frontend/Readback.lean:464-523 internExprGo
/// The six memoized arms, past the probe.  Split off so that the probe's
/// `match` ends before the state is taken mutably again (extraction rule 5).
pub fn intern_expr_node(st: &mut AState, m: &mut EMemo, e: &Expr) -> Result<EIdx, CheckError> {
    match expr::view(e) {
        ExprView::Fvar(i, ty) => match intern_expr_go(st, m, ty) {
            Err(err) => Err(err),
            Ok(t) => intern_e(st, ENodeView::FVar(*i, t)),
        },
        ExprView::App(f, a) => match intern_expr_go(st, m, f) {
            Err(err) => Err(err),
            Ok(hf) => match intern_expr_go(st, m, a) {
                Err(err) => Err(err),
                Ok(ha) => intern_e(st, ENodeView::App(hf, ha)),
            },
        },
        ExprView::Lam(ty, b, bi) => match intern_expr_go(st, m, ty) {
            Err(err) => Err(err),
            Ok(ht) => match intern_expr_go(st, m, b) {
                Err(err) => Err(err),
                Ok(hb) => intern_e(st, ENodeView::Lam(ht, hb, expr::binder_meta_dup(bi))),
            },
        },
        ExprView::ForallE(ty, b, bi) => match intern_expr_go(st, m, ty) {
            Err(err) => Err(err),
            Ok(ht) => match intern_expr_go(st, m, b) {
                Err(err) => Err(err),
                Ok(hb) => intern_e(st, ENodeView::ForallE(ht, hb, expr::binder_meta_dup(bi))),
            },
        },
        ExprView::LetE(ty, v, b) => match intern_expr_go(st, m, ty) {
            Err(err) => Err(err),
            Ok(ht) => match intern_expr_go(st, m, v) {
                Err(err) => Err(err),
                Ok(hv) => match intern_expr_go(st, m, b) {
                    Err(err) => Err(err),
                    Ok(hb) => intern_e(st, ENodeView::LetE(ht, hv, hb)),
                },
            },
        },
        ExprView::Proj(n, i, sub) => match intern_name(st, n) {
            Err(err) => Err(err),
            Ok(hn) => match intern_expr_go(st, m, sub) {
                Err(err) => Err(err),
                Ok(hs) => intern_e(st, ENodeView::Proj(hn, *i, hs)),
            },
        },
        _ => intern_expr_go(st, m, e),
    }
}

/// con-leche: none — intern a transient term at a fresh memo
/// Lean twin: `proof/ConRon/Arena/Intern.lean:47-48 internExpr`.
pub fn intern_expr(st: &mut AState, e: &Expr) -> Result<EIdx, CheckError> {
    let mut m: EMemo = memo_empty();
    intern_expr_go(st, &mut m, e)
}

/// con-leche: none — intern a list of transient terms; Lean twin: proof/ConRon/Arena/Frontend/Readback.lean:528-533 internExprList
/// The `List` recursion of the twin, as a cursor over the `Vec` (DESIGN.md
/// §3.4's standing rule).
pub fn intern_expr_list_go(
    st: &mut AState,
    m: &mut EMemo,
    es: &Vec<Expr>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= es.len() {
        Ok(out)
    } else {
        match intern_expr_go(st, m, &es[i]) {
            Err(err) => Err(err),
            Ok(h) => {
                let mut out2 = out;
                out2.push(h);
                intern_expr_list_go(st, m, es, i + 1, out2)
            }
        }
    }
}

/// con-leche: none — intern a list of transient terms at a fresh memo
/// Lean twin: `proof/ConRon/Arena/Intern.lean:50-52 internExprList`.
pub fn intern_expr_list(st: &mut AState, es: &Vec<Expr>) -> Result<Vec<EIdx>, CheckError> {
    let mut m: EMemo = memo_empty();
    intern_expr_list_go(st, &mut m, es, 0, Vec::new())
}

/// con-leche: none — intern a list of transient names; Lean twin: proof/ConRon/Arena/Frontend/Readback.lean:536-541 internNameList
/// The cursor recursion; names carry no memo (a name is a small value and its
/// cons table is the memo).
pub fn intern_name_list_go(
    st: &mut AState,
    ns: &Vec<Name>,
    i: usize,
    out: Vec<NIdx>,
) -> Result<Vec<NIdx>, CheckError> {
    if i >= ns.len() {
        Ok(out)
    } else {
        match intern_name(st, &ns[i]) {
            Err(err) => Err(err),
            Ok(h) => {
                let mut out2 = out;
                out2.push(h);
                intern_name_list_go(st, ns, i + 1, out2)
            }
        }
    }
}

/// con-leche: none — intern a list of transient names
/// Lean twin: `proof/ConRon/Arena/Frontend/Readback.lean:536-541 internNameList`.
pub fn intern_name_list(st: &mut AState, ns: &Vec<Name>) -> Result<Vec<NIdx>, CheckError> {
    intern_name_list_go(st, ns, 0, Vec::new())
}

/// con-leche: none — intern a list of transient levels; Lean twin: proof/ConRon/Arena/Monad.lean:316-320 internLevelList
/// The level-list cursor, for a nested rule's stored levels and a projection
/// table's guards.  `arena::monad::intern_level_list` is the same walk; this
/// one is here so that `intern_fire` and `intern_proj_table` read like the
/// twin's clauses.
pub fn intern_level_list_go(
    st: &mut AState,
    us: &Vec<Level>,
    i: usize,
    out: Vec<LIdx>,
) -> Result<Vec<LIdx>, CheckError> {
    if i >= us.len() {
        Ok(out)
    } else {
        match intern_level(st, &us[i]) {
            Err(err) => Err(err),
            Ok(h) => {
                let mut out2 = out;
                out2.push(h);
                intern_level_list_go(st, us, i + 1, out2)
            }
        }
    }
}

/// con-leche: none — intern a `ConstantVal`; Lean twin: proof/ConRon/Arena/Frontend/Readback.lean:544-548 internCV
/// The memoized form, for a block whose members share subterms.
pub fn intern_cv_go(
    st: &mut AState,
    m: &mut EMemo,
    cv: &ConstantVal,
) -> Result<IConstantVal, CheckError> {
    match intern_name(st, &cv.name) {
        Err(err) => Err(err),
        Ok(n) => match intern_name_list(st, &cv.level_params) {
            Err(err) => Err(err),
            Ok(lps) => match intern_expr_go(st, m, &cv.ty) {
                Err(err) => Err(err),
                Ok(ty) => Ok(IConstantVal { name: n, level_params: lps, ty }),
            },
        },
    }
}

/// con-leche: none — intern a transient `ConstantVal` at a fresh memo
/// Lean twin: `proof/ConRon/Arena/Intern.lean:54-56 internCV`.
pub fn intern_cv(st: &mut AState, cv: &ConstantVal) -> Result<IConstantVal, CheckError> {
    let mut m: EMemo = memo_empty();
    intern_cv_go(st, &mut m, cv)
}

/// con-leche: none — intern a recursor rule's firing mode
/// Lean twin: `proof/ConRon/Arena/Frontend/Readback.lean:551-557 internFire`.
pub fn intern_fire(
    st: &mut AState,
    m: &mut EMemo,
    f: &RecRuleFire,
) -> Result<IRecRuleFire, CheckError> {
    match f {
        RecRuleFire::Inert => Ok(IRecRuleFire::Inert),
        RecRuleFire::Plain => Ok(IRecRuleFire::Plain),
        RecRuleFire::Nested(lvls, pins) => match intern_level_list_go(st, lvls, 0, Vec::new()) {
            Err(err) => Err(err),
            Ok(hls) => match intern_expr_list_go(st, m, pins, 0, Vec::new()) {
                Err(err) => Err(err),
                Ok(hps) => Ok(IRecRuleFire::Nested(hls, hps)),
            },
        },
    }
}

/// con-leche: none — intern one recursor rule
/// Lean twin: `proof/ConRon/Arena/Frontend/Readback.lean:560-564 internRule`.
pub fn intern_rule(st: &mut AState, m: &mut EMemo, rl: &RecRule) -> Result<IRecRule, CheckError> {
    match intern_name(st, &rl.ctor) {
        Err(err) => Err(err),
        Ok(c) => match intern_fire(st, m, &rl.fire) {
            Err(err) => Err(err),
            Ok(f) => match intern_expr_go(st, m, &rl.rhs) {
                Err(err) => Err(err),
                Ok(r) => Ok(IRecRule {
                    ctor: c,
                    nfields: rl.nfields,
                    ctor_params: rl.ctor_params,
                    fire: f,
                    rhs: r,
                    k: rl.k,
                    eta: rl.eta,
                    params_blind: rl.params_blind,
                }),
            },
        },
    }
}

/// con-leche: none — intern a rule list
/// Lean twin: `proof/ConRon/Arena/Frontend/Readback.lean:567-572 internRules`.
pub fn intern_rules(
    st: &mut AState,
    m: &mut EMemo,
    rs: &Vec<RecRule>,
    i: usize,
    out: Vec<IRecRule>,
) -> Result<Vec<IRecRule>, CheckError> {
    if i >= rs.len() {
        Ok(out)
    } else {
        match intern_rule(st, m, &rs[i]) {
            Err(err) => Err(err),
            Ok(r) => {
                let mut out2 = out;
                out2.push(r);
                intern_rules(st, m, rs, i + 1, out2)
            }
        }
    }
}

/// con-leche: none — intern an inductive's capabilities
/// Lean twin: `proof/ConRon/Arena/Frontend/Readback.lean:575-578 internCaps`.
pub fn intern_caps(st: &mut AState, c: &IndCaps) -> Result<IIndCaps, CheckError> {
    match intern_name(st, &c.eta_ctor) {
        Err(err) => Err(err),
        Ok(ct) => Ok(IIndCaps {
            eta: c.eta,
            eta_ctor: ct,
            eta_params: c.eta_params,
            eta_fields: c.eta_fields,
            unitlike: c.unitlike,
            unit_params: c.unit_params,
            rule_k: c.rule_k,
            sort_z: prop_when::dup(&c.sort_z),
        }),
    }
}

/// con-leche: none — intern a projection table
/// Lean twin: `proof/ConRon/Arena/Frontend/Readback.lean:583-591 internProjTable`.
/// `table_name` is the field `arena::env` adds: the reserved name, interned
/// here so that `i_constant_info_name` stays pure.
pub fn intern_proj_table(
    st: &mut AState,
    m: &mut EMemo,
    t: &ProjTable,
) -> Result<IProjTable, CheckError> {
    match intern_name(st, &t.struct_name) {
        Err(err) => Err(err),
        Ok(sn) => match crate::arena::env::proj_table_name(&mut st.store, &sn) {
            Err(err) => Err(err),
            Ok(tn) => intern_proj_table_rest(st, m, t, sn, tn),
        },
    }
}

/// con-leche: none — the tail of the projection-table interning
/// Lean twin: `proof/ConRon/Arena/Frontend/Readback.lean:583-591 internProjTable`.
/// Split at the twin's own `let`-boundary, so each state-threading call is a
/// tail call (task #97-P4c's rule).
pub fn intern_proj_table_rest(
    st: &mut AState,
    m: &mut EMemo,
    t: &ProjTable,
    sn: NIdx,
    tn: NIdx,
) -> Result<IProjTable, CheckError> {
    match intern_name_list(st, &t.level_params) {
        Err(err) => Err(err),
        Ok(lps) => match intern_name(st, &t.ctor) {
            Err(err) => Err(err),
            Ok(c) => match intern_level(st, &t.struct_sort) {
                Err(err) => Err(err),
                Ok(ss) => match intern_expr_list_go(st, m, &t.bodies, 0, Vec::new()) {
                    Err(err) => Err(err),
                    Ok(bs) => match intern_level_list_go(st, &t.guards, 0, Vec::new()) {
                        Err(err) => Err(err),
                        Ok(gs) => Ok(IProjTable {
                            struct_name: sn,
                            table_name: tn,
                            level_params: lps,
                            num_params: t.num_params,
                            ctor: c,
                            num_fields: t.num_fields,
                            struct_sort: ss,
                            bodies: bs,
                            guards: gs,
                            off: t.off,
                        }),
                    },
                },
            },
        },
    }
}

/// con-leche: none — intern a stored constant
/// Lean twin: `proof/ConRon/Arena/Frontend/Readback.lean:594-619 internCI`.
pub fn intern_ci_go(
    st: &mut AState,
    m: &mut EMemo,
    c: &ConstantInfo,
) -> Result<IConstantInfo, CheckError> {
    match c {
        ConstantInfo::AxiomInfo(v) => match intern_cv_go(st, m, v) {
            Err(err) => Err(err),
            Ok(cv) => Ok(IConstantInfo::AxiomInfo(cv)),
        },
        ConstantInfo::DefnInfo(v, e, h) => match intern_cv_go(st, m, v) {
            Err(err) => Err(err),
            Ok(cv) => match intern_expr_go(st, m, e) {
                Err(err) => Err(err),
                Ok(x) => Ok(IConstantInfo::DefnInfo(cv, x, cenv::reducibility_hint_dup(h))),
            },
        },
        ConstantInfo::ThmInfo(v, e) => match intern_cv_go(st, m, v) {
            Err(err) => Err(err),
            Ok(cv) => match intern_expr_go(st, m, e) {
                Err(err) => Err(err),
                Ok(x) => Ok(IConstantInfo::ThmInfo(cv, x)),
            },
        },
        ConstantInfo::IndInfo(v, c2) => match intern_cv_go(st, m, v) {
            Err(err) => Err(err),
            Ok(cv) => match intern_caps(st, c2) {
                Err(err) => Err(err),
                Ok(caps) => Ok(IConstantInfo::IndInfo(cv, caps)),
            },
        },
        ConstantInfo::CtorInfo(v, n_p, n_f) => match intern_cv_go(st, m, v) {
            Err(err) => Err(err),
            Ok(cv) => Ok(IConstantInfo::CtorInfo(cv, *n_p, *n_f)),
        },
        ConstantInfo::RecInfo(v, m_i, r_p, rs) => match intern_cv_go(st, m, v) {
            Err(err) => Err(err),
            Ok(cv) => match intern_rules(st, m, rs, 0, Vec::new()) {
                Err(err) => Err(err),
                Ok(rules) => Ok(IConstantInfo::RecInfo(cv, *m_i, *r_p, rules)),
            },
        },
        ConstantInfo::ProjInfo(t) => match intern_proj_table(st, m, t) {
            Err(err) => Err(err),
            Ok(tbl) => Ok(IConstantInfo::ProjInfo(tbl)),
        },
    }
}

/// con-leche: none — intern a transient `ConstantInfo` at a fresh memo
/// Lean twin: `proof/ConRon/Arena/Intern.lean:58-60 internCI`.
pub fn intern_ci(st: &mut AState, c: &ConstantInfo) -> Result<IConstantInfo, CheckError> {
    let mut m: EMemo = memo_empty();
    intern_ci_go(st, &mut m, c)
}

/// con-leche: none — intern a block's constants
/// Lean twin: `proof/ConRon/Arena/Frontend/Readback.lean:622-627 internCIList`.
pub fn intern_ci_list_go(
    st: &mut AState,
    m: &mut EMemo,
    cs: &Vec<ConstantInfo>,
    i: usize,
    out: Vec<IConstantInfo>,
) -> Result<Vec<IConstantInfo>, CheckError> {
    if i >= cs.len() {
        Ok(out)
    } else {
        match intern_ci_go(st, m, &cs[i]) {
            Err(err) => Err(err),
            Ok(h) => {
                let mut out2 = out;
                out2.push(h);
                intern_ci_list_go(st, m, cs, i + 1, out2)
            }
        }
    }
}

/// con-leche: none — intern a block of transient `ConstantInfo`s at ONE memo
/// Lean twin: `proof/ConRon/Arena/Intern.lean:62-65 internCIList` — one memo,
/// so that the sharing between a block's members survives.
pub fn intern_ci_list(
    st: &mut AState,
    cs: &Vec<ConstantInfo>,
) -> Result<Vec<IConstantInfo>, CheckError> {
    let mut m: EMemo = memo_empty();
    intern_ci_list_go(st, &mut m, cs, 0, Vec::new())
}

/// con-leche: none — intern a declaration record
/// Lean twin: `proof/ConRon/Arena/Frontend/Readback.lean:632-655 internDecl` —
/// the inverse of `denoteDecl`.  The parser builds handles directly, so this
/// is the differential test's road from a con-ron-core declaration list to the
/// arena's; it is shipped rather than test-only because `Readback.lean` ships
/// it and the two modules are twins.
pub fn intern_decl(
    st: &mut AState,
    m: &mut EMemo,
    d: &Declaration,
) -> Result<IDeclaration, CheckError> {
    match d {
        Declaration::AxiomDecl(v) => match intern_cv_go(st, m, v) {
            Err(err) => Err(err),
            Ok(cv) => Ok(IDeclaration::AxiomDecl(cv)),
        },
        Declaration::DefnDecl(v, e, h) => match intern_cv_go(st, m, v) {
            Err(err) => Err(err),
            Ok(cv) => match intern_expr_go(st, m, e) {
                Err(err) => Err(err),
                Ok(x) => Ok(IDeclaration::DefnDecl(cv, x, cenv::reducibility_hint_dup(h))),
            },
        },
        Declaration::ThmDecl(v, e) => match intern_cv_go(st, m, v) {
            Err(err) => Err(err),
            Ok(cv) => match intern_expr_go(st, m, e) {
                Err(err) => Err(err),
                Ok(x) => Ok(IDeclaration::ThmDecl(cv, x)),
            },
        },
        Declaration::OpaqueDecl(v, e) => match intern_cv_go(st, m, v) {
            Err(err) => Err(err),
            Ok(cv) => match intern_expr_go(st, m, e) {
                Err(err) => Err(err),
                Ok(x) => Ok(IDeclaration::OpaqueDecl(cv, x)),
            },
        },
        Declaration::BasisDecl(k) => Ok(IDeclaration::BasisDecl(cenv::basis_kind_dup(k))),
        Declaration::IndDecl(block, n_p) => {
            match intern_ci_list_go(st, m, block, 0, Vec::new()) {
                Err(err) => Err(err),
                Ok(b) => Ok(IDeclaration::IndDecl(b, *n_p)),
            }
        }
        Declaration::QuotDecl(k, v) => match intern_cv_go(st, m, v) {
            Err(err) => Err(err),
            Ok(cv) => Ok(IDeclaration::QuotDecl(cenv::quot_kind_dup(k), cv)),
        },
    }
}

/// con-leche: none — intern a declaration list
/// Lean twin: `proof/ConRon/Arena/Frontend/Readback.lean:657-662 internDecls`.
pub fn intern_decls_go(
    st: &mut AState,
    m: &mut EMemo,
    ds: &Vec<Declaration>,
    i: usize,
    out: Vec<IDeclaration>,
) -> Result<Vec<IDeclaration>, CheckError> {
    if i >= ds.len() {
        Ok(out)
    } else {
        match intern_decl(st, m, &ds[i]) {
            Err(err) => Err(err),
            Ok(h) => {
                let mut out2 = out;
                out2.push(h);
                intern_decls_go(st, m, ds, i + 1, out2)
            }
        }
    }
}

/// con-leche: none — intern a declaration list at ONE memo
/// Lean twin: `proof/ConRon/Arena/Frontend/Readback.lean:657-662 internDecls`.
pub fn intern_decls(
    st: &mut AState,
    ds: &Vec<Declaration>,
) -> Result<Vec<IDeclaration>, CheckError> {
    let mut m: EMemo = memo_empty();
    intern_decls_go(st, &mut m, ds, 0, Vec::new())
}

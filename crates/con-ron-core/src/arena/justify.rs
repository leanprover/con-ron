//! `arena::justify` — **axioms justified by a solution**.
//!
//! The Rust twin of `proof/ConRon/Arena/Justify.lean`, which is con-leche's
//! `Cached/Justify.lean`.  A stream may declare more axioms than the standard
//! ones when a **solution** justifies them: a second stream, checked as usual,
//! whose index holds a constant of the same name and the same type, everything
//! that type reads being the same constant in both up to the names of its
//! level parameters (`justify_why`, the cone walk `cone_go`).  A definition,
//! theorem or opaque constant whose value uses `sorryAx` is the axiom of its
//! statement (`side_record`).  Without a solution every record takes its own
//! check (`check_record` at `None` is `check_decl::check_decl`).
//!
//! **One store.**  Both streams are read into the driver's store; the
//! solution's index (`stream_index::build_index` over its records) is checked
//! as a flat run, then the challenge's index is built on the thawed store and
//! frozen, and the challenge's jobs read the solution through `Solution`.
//! Hash-consing makes con-leche's structural comparisons (`copyB`,
//! `refinesB`, `ProjTable.beqP`) handle comparisons; a renaming of level
//! parameters is the core's level substitution (`basis::constant_info_at_lps`,
//! the cited `atLpsC`), whose result a job interns in its scratch tier — the
//! persistent table is probed first, so an equal term is the persistent
//! handle.

use crate::arena::basis::{basis_names_error, basis_names_ok, constant_info_at_lps, constant_val_at_lps};
use crate::arena::canon::{eidx_vec_beq, i_constant_info_beq, i_constant_val_beq, nidx_vec_beq};
use crate::arena::check_decl::check_decl;
use crate::arena::checker_base::{check_constant_val, name_nodup};
use crate::arena::core::{nat_op_name, reserved_basis_names, CORE_WALK_FUEL};
use crate::arena::env::{
    i_constant_info_name, i_constant_info_to_constant_val, i_constant_val_dup, i_declaration_dup,
    ifenv_find, ifenv_find_table, ifenv_push, nidx_vec_contains, nidx_vec_dup, IConstantInfo,
    IConstantVal, IDeclaration, IFEnv, IProjTable,
};
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::inductives::block_shape::REC_SUFFIX;
use crate::arena::inductives::struct_parts::mentions_const;
use crate::arena::monad::{fail, intern_n_node, read_name_m, AState};
use crate::arena::nat_op_pin_set::INatOpPinSet;
use crate::arena::needs::{
    needs_const, needs_go, needs_names, needs_st_empty, needs_table, nidx_append, NeedsSt,
};
use crate::arena::pins::{pin_quot_sound, pin_sorry_ax};
use crate::arena::std_axioms::{choice_name, propext_name};
use crate::arena::store::{NNodeView, PersTier};
use crate::arena::stream_index::IStreamIndex;
use crate::arena::trust_axioms::{
    of_reduce_bool_name, of_reduce_nat_name, reduce_op_names, trust_compiler_name,
};
use crate::frontend::text;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::CheckMode;
use crate::kernel::name;
use crate::ron::hashmap::{Dup, Eq2};
use crate::ron::hashmap2::HashMap2 as HashMap;

// ---------------------------------------------------------------------------
// The messages
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"the solution has no constant "`, as code points.
pub const M_NO_CONSTANT: [u32; 29] = [116, 104, 101, 32, 115, 111, 108, 117, 116, 105, 111, 110, 32, 104, 97, 115, 32, 110, 111, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"the solution's "`, as code points.
pub const M_SOL_PRE: [u32; 15] = [116, 104, 101, 32, 115, 111, 108, 117, 116, 105, 111, 110, 39, 115, 32];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `" has another type"`, as code points.
pub const M_ANOTHER_TYPE: [u32; 17] = [32, 104, 97, 115, 32, 97, 110, 111, 116, 104, 101, 114, 32, 116, 121, 112, 101];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"its type reads "`, as code points.
pub const M_TYPE_READS: [u32; 15] = [105, 116, 115, 32, 116, 121, 112, 101, 32, 114, 101, 97, 100, 115, 32];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `", which the solution does not declare alike"`, as code points.
pub const M_NOT_ALIKE: [u32; 43] = [44, 32, 119, 104, 105, 99, 104, 32, 116, 104, 101, 32, 115, 111, 108, 117, 116, 105, 111, 110, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 100, 101, 99, 108, 97, 114, 101, 32, 97, 108, 105, 107, 101];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `" is not justified by the solution: "`, as code points.
pub const M_NOT_JUSTIFIED: [u32; 35] = [32, 105, 115, 32, 110, 111, 116, 32, 106, 117, 115, 116, 105, 102, 105, 101, 100, 32, 98, 121, 32, 116, 104, 101, 32, 115, 111, 108, 117, 116, 105, 111, 110, 58, 32];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"def "`, as code points.
pub const M_LBL_DEF: [u32; 4] = [100, 101, 102, 32];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"theorem "`, as code points.
pub const M_LBL_THM: [u32; 8] = [116, 104, 101, 111, 114, 101, 109, 32];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"opaque "`, as code points.
pub const M_LBL_OPAQUE: [u32; 7] = [111, 112, 97, 113, 117, 101, 32];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"axiom "`, as code points.
pub const M_LBL_AXIOM: [u32; 6] = [97, 120, 105, 111, 109, 32];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"inductive "`, as code points.
pub const M_LBL_IND: [u32; 10] = [105, 110, 100, 117, 99, 116, 105, 118, 101, 32];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"quot "`, as code points.
pub const M_LBL_QUOT: [u32; 5] = [113, 117, 111, 116, 32];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: coneGo"`, as code points.
pub const M_FUEL_CONE: [u32; 22] = [102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 99, 111, 110, 101, 71, 111];

// ---------------------------------------------------------------------------
// Which records offer a statement
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/Justify.lean:47-51 builtinAxiomName
/// Lean twin: `proof/ConRon/Arena/Justify.lean:33-43 builtinAxiomName` — **the built-in
/// axioms**: they keep their own check, solution or not.
pub fn builtin_axiom_name(st: &mut AState, n: &NIdx) -> Result<bool, CheckError> {
    match propext_name(st) {
        Err(e) => Err(e),
        Ok(a) => match choice_name(st) {
            Err(e) => Err(e),
            Ok(b) => match pin_quot_sound(st) {
                Err(e) => Err(e),
                Ok(c) => match pin_sorry_ax(st) {
                    Err(e) => Err(e),
                    Ok(d) => match trust_compiler_name(st) {
                        Err(e) => Err(e),
                        Ok(f) => match of_reduce_nat_name(st) {
                            Err(e) => Err(e),
                            Ok(g) => match of_reduce_bool_name(st) {
                                Err(e) => Err(e),
                                Ok(h) => Ok(n.eq2(&a)
                                    || n.eq2(&b)
                                    || n.eq2(&c)
                                    || n.eq2(&d)
                                    || n.eq2(&f)
                                    || n.eq2(&g)
                                    || n.eq2(&h)),
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Cached/Justify.lean:53-61 sideRecord
/// Lean twin: `proof/ConRon/Arena/Justify.lean:45-52 sideRecordVal` — a value record's
/// arm: the axiom of its statement when its value uses a hole (and its name is
/// no built-in axiom's), the record itself otherwise.
pub fn side_record_val(
    pers: &PersTier,
    st: &mut AState,
    d: &IDeclaration,
    cv: &IConstantVal,
    v: &EIdx,
) -> Result<IDeclaration, CheckError> {
    match builtin_axiom_name(st, &cv.name) {
        Err(e) => Err(e),
        Ok(true) => Ok(i_declaration_dup(d)),
        Ok(false) => match pin_sorry_ax(st) {
            Err(e) => Err(e),
            Ok(sa) => match mentions_const(pers, st, &sa, v) {
                Err(e) => Err(e),
                Ok(true) => Ok(IDeclaration::AxiomDecl(i_constant_val_dup(cv))),
                Ok(false) => Ok(i_declaration_dup(d)),
            },
        },
    }
}

/// con-leche: ConLeche/Cached/Justify.lean:53-61 sideRecord
/// Lean twin: `proof/ConRon/Arena/Justify.lean:54-61 sideRecord` — **a definition,
/// theorem or opaque constant whose value uses a hole is the axiom of its
/// statement**; every other record is itself.  The cited or-pattern is three
/// arms here.
pub fn side_record(pers: &PersTier, st: &mut AState, d: &IDeclaration) -> Result<IDeclaration, CheckError> {
    match d {
        IDeclaration::DefnDecl(cv, v, _) => side_record_val(pers, st, d, cv, v),
        IDeclaration::ThmDecl(cv, v) => side_record_val(pers, st, d, cv, v),
        IDeclaration::OpaqueDecl(cv, v) => side_record_val(pers, st, d, cv, v),
        _ => Ok(i_declaration_dup(d)),
    }
}

/// con-leche: ConLeche/Cached/Justify.lean:63-67 sideRecords
/// Lean twin: `proof/ConRon/Arena/Justify.lean:63-71 sideRecordsGo` — **the records a
/// fold with a solution checks**: every record through `side_record`, from
/// cursor `i`, onto `out`.  The cited `none` arm is the flat path, which does
/// not call this.
pub fn side_records(
    pers: &PersTier,
    st: &mut AState,
    ds: &Vec<IDeclaration>,
    i: usize,
    out: Vec<IDeclaration>,
) -> Result<Vec<IDeclaration>, CheckError> {
    if i >= ds.len() {
        Ok(out)
    } else {
        match side_record(pers, st, &ds[i]) {
            Err(e) => Err(e),
            Ok(d) => {
                let mut out = out;
                out.push(d);
                side_records(pers, st, ds, i + 1, out)
            }
        }
    }
}

/// con-leche: ConLeche/Cached/Justify.lean:69-77 justifiable
/// Lean twin: `proof/ConRon/Arena/Justify.lean:73-83 justifiable` — **the statement a
/// record offers to a solution**: an axiom's, other than a built-in one's, and
/// not at a certified `Nat` operation's or a compiler-trust operation's name.
pub fn justifiable(st: &mut AState, pd: &IDeclaration) -> Result<Option<IConstantVal>, CheckError> {
    match pd {
        IDeclaration::AxiomDecl(cv) => match builtin_axiom_name(st, &cv.name) {
            Err(e) => Err(e),
            Ok(true) => Ok(None),
            Ok(false) => match nat_op_name(st, &cv.name) {
                Err(e) => Err(e),
                Ok(true) => Ok(None),
                Ok(false) => match reduce_op_names(st) {
                    Err(e) => Err(e),
                    Ok(rs) => {
                        if nidx_vec_contains(&rs, &cv.name) {
                            Ok(None)
                        } else {
                            Ok(Some(i_constant_val_dup(cv)))
                        }
                    }
                },
            },
        },
        _ => Ok(None),
    }
}

// ---------------------------------------------------------------------------
// The comparison
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/Justify.lean:81-83 levelsRenaming
/// Lean twin: `proof/ConRon/Arena/Justify.lean:87-90 levelsRenaming` — two lists of
/// level-parameter names a renaming relates: as many, neither with a repeat.
pub fn levels_renaming(ps: &Vec<NIdx>, ps2: &Vec<NIdx>) -> bool {
    ps.len() == ps2.len() && name_nodup(ps) && name_nodup(ps2)
}

/// con-leche: ConLeche/Cached/Justify.lean:85-91 sameCvUpToLevels
/// con-leche: ConLeche/Cached/CheckerC.lean:123-126 _root_.ConLeche.ConstantVal.atLpsC
/// Lean twin: `proof/ConRon/Arena/Justify.lean:92-102 sameCvUpToLevels` — **the
/// input's statement, the solution's up to the names of its level
/// parameters**: the same, or a renaming apart and the solution's (`cv2`) at
/// the input's names the input's.  `basis::constant_val_at_lps` is the cited
/// `atLpsC` (the core's level substitution keeps the sharing).
pub fn same_cv_up_to_levels(
    pers: &PersTier,
    st: &mut AState,
    cv: &IConstantVal,
    cv2: &IConstantVal,
) -> Result<bool, CheckError> {
    if nidx_vec_beq(&cv.level_params, &cv2.level_params, 0) {
        Ok(i_constant_val_beq(cv, cv2))
    } else if levels_renaming(&cv.level_params, &cv2.level_params) {
        match constant_val_at_lps(pers, st, cv2, &cv.level_params) {
            Err(e) => Err(e),
            Ok(r) => Ok(i_constant_val_beq(&r, cv)),
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Cached/Justify.lean:93-97 _root_.ConLeche.ProjTable.beqP
/// Lean twin: none — the twin's derived `DecidableEq` (`==`), which Rust cannot
/// derive (§3.4); field by field.
pub fn i_proj_table_beq(a: &IProjTable, b: &IProjTable) -> bool {
    a.struct_name.eq2(&b.struct_name)
        && nidx_vec_beq(&a.level_params, &b.level_params, 0)
        && a.num_params == b.num_params
        && a.ctor.eq2(&b.ctor)
        && a.num_fields == b.num_fields
        && eidx_vec_beq(&a.bodies, &b.bodies, 0)
}

/// con-leche: ConLeche/Cached/Justify.lean:99-103 tableBeqP
/// Lean twin: `proof/ConRon/Arena/Justify.lean:104-108 tableBeqP` — two lookups' tables.
pub fn table_beq_p(a: Option<&IProjTable>, b: Option<&IProjTable>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => i_proj_table_beq(x, y),
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:435-438 isStmtKind
/// Lean twin: `proof/ConRon/Arena/Justify.lean:110-114 IConstantInfo.isStmtKind` — a
/// definition, theorem or axiom: the kinds whose copies may differ by a value.
pub fn is_stmt_kind(ci: &IConstantInfo) -> bool {
    match ci {
        IConstantInfo::DefnInfo(_, _, _) => true,
        IConstantInfo::ThmInfo(_) => true,
        IConstantInfo::AxiomInfo(_) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Cached/Justify.lean:105-115 copyB
/// con-leche: ConLeche/Cached/CheckerC.lean:128-142 _root_.ConLeche.ConstantInfo.atLpsC
/// Lean twin: `proof/ConRon/Arena/Justify.lean:116-131 copyB` — **the input's constant
/// `ci` is a copy of the solution's `ci2`**: the same, or, for a definition,
/// theorem or axiom at a name no pin reserves, the solution's at the input's
/// level-parameter names, a renaming apart.  `basis::constant_info_at_lps` is
/// the cited `atLpsC`.
pub fn copy_b(
    pers: &PersTier,
    st: &mut AState,
    ci2: &IConstantInfo,
    ci: &IConstantInfo,
) -> Result<bool, CheckError> {
    let cv: IConstantVal = i_constant_info_to_constant_val(ci);
    let cv2: IConstantVal = i_constant_info_to_constant_val(ci2);
    if nidx_vec_beq(&cv.level_params, &cv2.level_params, 0) {
        Ok(i_constant_info_beq(ci, ci2))
    } else if is_stmt_kind(ci2) {
        match reserved_basis_names(st) {
            Err(e) => Err(e),
            Ok(rs) => {
                if !nidx_vec_contains(&rs, &cv2.name)
                    && levels_renaming(&cv2.level_params, &cv.level_params)
                {
                    match constant_info_at_lps(pers, st, ci2, &cv.level_params) {
                        Err(e) => Err(e),
                        Ok(r) => Ok(i_constant_info_beq(&r, ci)),
                    }
                } else {
                    Ok(false)
                }
            }
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Cached/Justify.lean:117-126 refinesB
/// Lean twin: `proof/ConRon/Arena/Justify.lean:133-146 refinesB` — **the input's copy
/// is the solution's**: a copy of it, or an axiom that copies the statement of
/// a solution definition, theorem or axiom other than a compiler-trust
/// operation.
pub fn refines_b(
    pers: &PersTier,
    st: &mut AState,
    ci: &IConstantInfo,
    ci2: &IConstantInfo,
) -> Result<bool, CheckError> {
    match copy_b(pers, st, ci2, ci) {
        Err(e) => Err(e),
        Ok(true) => Ok(true),
        Ok(false) => match ci {
            IConstantInfo::AxiomInfo(_) => {
                if is_stmt_kind(ci2) {
                    match reduce_op_names(st) {
                        Err(e) => Err(e),
                        Ok(rs) => {
                            let cv2: IConstantVal = i_constant_info_to_constant_val(ci2);
                            if nidx_vec_contains(&rs, &cv2.name) {
                                Ok(false)
                            } else {
                                copy_b(pers, st, &IConstantInfo::AxiomInfo(cv2), ci)
                            }
                        }
                    }
                } else {
                    Ok(false)
                }
            }
            _ => Ok(false),
        },
    }
}

// ---------------------------------------------------------------------------
// The solution
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/Justify.lean:128-133 Solution
/// Lean twin: `proof/ConRon/Arena/Justify.lean:150-155 ISolution` — **the solution, as
/// the justification reads it**: the solution stream's frozen index (every
/// constant visible: con-leche's `mkFEnv envS`), and the input's record mates.
/// The index's handles are the solution's, in the one store both streams were
/// read into, so a comparison with the input's is a handle comparison.
pub struct Solution {
    pub ix: IStreamIndex,
    pub mates: HashMap<NIdx, Vec<NIdx>>,
}

/// con-leche: ConLeche/Cached/Justify.lean:135-142 recordMates
/// Lean twin: `proof/ConRon/Arena/Justify.lean:157-164 matesInsert` — the cited
/// `m.getD b.name #[]`, copied, split off so that the lookup's loan ends here
/// (extraction rule 5).
pub fn mates_get(m: &HashMap<NIdx, Vec<NIdx>>, b: &NIdx) -> Vec<NIdx> {
    match m.get(b) {
        Some(v) => nidx_vec_dup(v),
        None => Vec::new(),
    }
}

/// con-leche: ConLeche/Cached/Justify.lean:135-142 recordMates
/// Lean twin: `proof/ConRon/Arena/Justify.lean:157-164 matesInsert` — one block's
/// members from cursor `j`, each mapped to what it had and the block's names
/// `ns`.
pub fn mates_insert(
    m: HashMap<NIdx, Vec<NIdx>>,
    block: &Vec<IConstantInfo>,
    ns: &Vec<NIdx>,
    j: usize,
) -> HashMap<NIdx, Vec<NIdx>> {
    if j >= block.len() {
        m
    } else {
        let b: NIdx = i_constant_info_name(&block[j]);
        let prev: Vec<NIdx> = mates_get(&m, &b);
        let k: usize = ns.len();
        let v: Vec<NIdx> = nidx_append(prev, ns, 0, k);
        let mut m = m;
        m.insert(b, v);
        mates_insert(m, block, ns, j + 1)
    }
}

/// con-leche: ConLeche/Cached/Justify.lean:135-142 recordMates
/// Lean twin: `proof/ConRon/Arena/Justify.lean:166-172 recordMatesGo` — its `block.map (·.name)`: a block's names,
/// in order, from cursor `j`.
pub fn block_names(block: &Vec<IConstantInfo>, j: usize, out: Vec<NIdx>) -> Vec<NIdx> {
    if j >= block.len() {
        out
    } else {
        let mut out = out;
        out.push(i_constant_info_name(&block[j]));
        block_names(block, j + 1, out)
    }
}

/// con-leche: ConLeche/Cached/Justify.lean:135-142 recordMates
/// Lean twin: `proof/ConRon/Arena/Justify.lean:166-172 recordMatesGo` — **the input's
/// record mates**, the records from cursor `i` on: each name an inductive
/// block declares, mapped to the names of every block that declares it.
pub fn record_mates(
    ds: &Vec<IDeclaration>,
    i: usize,
    m: HashMap<NIdx, Vec<NIdx>>,
) -> HashMap<NIdx, Vec<NIdx>> {
    if i >= ds.len() {
        m
    } else {
        match &ds[i] {
            IDeclaration::IndDecl(block, _) => {
                let ns: Vec<NIdx> = block_names(block, 0, Vec::new());
                let m2: HashMap<NIdx, Vec<NIdx>> = mates_insert(m, block, &ns, 0);
                record_mates(ds, i + 1, m2)
            }
            _ => record_mates(ds, i + 1, m),
        }
    }
}

/// con-leche: ConLeche/Cached/Justify.lean:144-146 solutionOf
/// con-leche: ConLeche/Driver/CheckPool.lean:57-75 Jobs.build
/// Lean twin: `proof/ConRon/Arena/Justify.lean:174-179 solutionOf` — **the solution a
/// fold over `ds` reads**: the solution stream's frozen index `ix`
/// (`stream_index::build_index` over the solution's records, the cited
/// `mkFEnv e`), with the record mates of `ds` — the challenge's records as the
/// fold checks them (after `side_records`).  The driver builds the challenge's
/// index after the solution's check, on the thawed store, so `ix`'s handles
/// stay valid.  The cited `none` arm is the flat path's `None`.
pub fn solution_of(ix: IStreamIndex, ds: &Vec<IDeclaration>) -> Solution {
    Solution {
        ix,
        mates: record_mates(ds, 0, HashMap::new()),
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:278-283 FEnv.find?
/// Lean twin: `proof/ConRon/Arena/Justify.lean:181-186 ISolution.find?` — **the
/// solution's lookup**: its index's first entry of `n`, every counter visible
/// (the cited `mkFEnv envS` holds the whole stream).
pub fn solution_find<'a>(sol: &'a Solution, n: &NIdx) -> Option<&'a IConstantInfo> {
    match sol.ix.idx.get(n) {
        Some(c) => {
            if *c < sol.ix.next && (*c as usize) < sol.ix.consts.len() {
                Some(&sol.ix.consts[*c as usize])
            } else {
                None
            }
        }
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:413-417 FEnv.findTable?
/// Lean twin: `proof/ConRon/Arena/Justify.lean:188-195 ISolution.findTable?` — the
/// solution's table lookup: `n`'s first table, visible where the constant `n`
/// is (every record position).
pub fn solution_find_table<'a>(sol: &'a Solution, n: &NIdx) -> Option<&'a IProjTable> {
    if solution_find(sol, n).is_some() {
        match sol.ix.tbls.get(n) {
            Some(e) => {
                if e.0 < (sol.ix.firsts.len() as u64) && (e.1 as usize) < sol.ix.tables.len() {
                    Some(&sol.ix.tables[e.1 as usize])
                } else {
                    None
                }
            }
            None => None,
        }
    } else {
        None
    }
}

// ---------------------------------------------------------------------------
// The cone
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/Justify.lean:148-161 entryNeeds
/// Lean twin: `proof/ConRon/Arena/Justify.lean:199-206 recNames` — `caps.all.map (·.str
/// "rec")`, interned, from cursor `j`, pushed onto `out`.
pub fn rec_names_of(
    pers: &PersTier,
    st: &mut AState,
    all: &Vec<NIdx>,
    j: usize,
    out: Vec<NIdx>,
) -> Result<Vec<NIdx>, CheckError> {
    if j >= all.len() {
        Ok(out)
    } else {
        match intern_n_node(pers, st, NNodeView::Str(all[j].dup2(), code_points(&REC_SUFFIX))) {
            Err(e) => Err(e),
            Ok(n) => {
                let mut o: Vec<NIdx> = out;
                o.push(n);
                rec_names_of(pers, st, all, j + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Cached/Justify.lean:148-161 entryNeeds
/// Lean twin: `proof/ConRon/Arena/Justify.lean:208-227 entryNeeds` — the cited
/// `x.names (mates.getD n #[]).toList`, split off so that the lookup's loan
/// ends here (extraction rule 5).
pub fn needs_mates(mates: &HashMap<NIdx, Vec<NIdx>>, n: &NIdx, x: NeedsSt) -> NeedsSt {
    match mates.get(n) {
        Some(ms) => needs_names(x, ms),
        None => x,
    }
}

/// con-leche: ConLeche/Cached/Justify.lean:148-161 entryNeeds
/// Lean twin: `proof/ConRon/Arena/Justify.lean:208-227 entryNeeds` — **what the
/// justification follows from a constant**: its laws' names, a type former's
/// constructors and its block's recursors, its record's mates, and the names of
/// its projection table in the input's index `fe`.
pub fn entry_needs(
    pers: &PersTier,
    st: &mut AState,
    mates: &HashMap<NIdx, Vec<NIdx>>,
    fe: &IFEnv,
    ci: &IConstantInfo,
) -> Result<Vec<NIdx>, CheckError> {
    match needs_const(pers, st, needs_st_empty(), ci) {
        Err(e) => Err(e),
        Ok(x0) => {
            let r: Result<NeedsSt, CheckError> = match ci {
                IConstantInfo::IndInfo(_, caps) => {
                    let x1: NeedsSt = needs_names(x0, &caps.ctors);
                    match rec_names_of(pers, st, &caps.all, 0, Vec::new()) {
                        Err(e) => Err(e),
                        Ok(rn) => Ok(needs_names(x1, &rn)),
                    }
                }
                _ => Ok(x0),
            };
            match r {
                Err(e) => Err(e),
                Ok(x2) => {
                    let n: NIdx = i_constant_info_name(ci);
                    let x3: NeedsSt = needs_mates(mates, &n, x2);
                    match ifenv_find_table(pers, fe, &n) {
                        Some(t) => match needs_table(pers, st, x3, t) {
                            Err(e) => Err(e),
                            Ok(x4) => Ok(x4.acc),
                        },
                        None => Ok(x3.acc),
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/Justify.lean:163-183 coneGo
/// Lean twin: `proof/ConRon/Arena/Justify.lean:229-244 coneEntry` — **one name of the
/// cone, compared**: `Some` of what it reads when the input's constant is the
/// solution's (`refines_b`) with the same table, `None` when it is not (or
/// either index lacks it).
pub fn cone_entry(
    pers: &PersTier,
    st: &mut AState,
    sol: &Solution,
    fe: &IFEnv,
    n: &NIdx,
) -> Result<Option<Vec<NIdx>>, CheckError> {
    match ifenv_find(pers, fe, n) {
        None => Ok(None),
        Some(ci) => match solution_find(sol, n) {
            None => Ok(None),
            Some(ci2) => match refines_b(pers, st, ci, ci2) {
                Err(e) => Err(e),
                Ok(false) => Ok(None),
                Ok(true) => {
                    if table_beq_p(ifenv_find_table(pers, fe, n), solution_find_table(sol, n)) {
                        match entry_needs(pers, st, &sol.mates, fe, ci) {
                            Err(e) => Err(e),
                            Ok(ns) => Ok(Some(ns)),
                        }
                    } else {
                        Ok(None)
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Cached/Justify.lean:163-183 coneGo
/// Lean twin: `proof/ConRon/Arena/Justify.lean:246-268 coneGo` — **the cone walk**:
/// every name of `work` from cursor `i`, and everything it reads, is the same
/// constant in the input's index `fe` and the solution's; the first name that
/// is not, or `None`.  Each name is compared once (`seen`); `fuel` bounds the
/// names compared.  The answer carries the fuel and `seen` on.
///
/// Deviation of shape: con-leche's work list `entryNeeds ci ++ work` is a
/// recursion here — a name's needs walked to the end before the rest of
/// `work` — which visits the names in the same order with the same `seen`
/// and fuel (the Aeneas subset cannot pop a `Vec`).  `depth` bounds that
/// recursion (the cited walk has no stack): a walk past it is an internal
/// error, never a verdict.
pub fn cone_go(
    pers: &PersTier,
    st: &mut AState,
    sol: &Solution,
    fe: &IFEnv,
    depth: u64,
    fuel: u64,
    seen: HashMap<NIdx, bool>,
    work: &Vec<NIdx>,
    i: usize,
) -> Result<(Option<NIdx>, u64, HashMap<NIdx, bool>), CheckError> {
    if depth == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_CONE)))
    } else if i >= work.len() {
        Ok((None, fuel, seen))
    } else if seen.contains_key(&work[i]) {
        cone_go(pers, st, sol, fe, depth, fuel, seen, work, i + 1)
    } else if fuel == 0 {
        Ok((Some(work[i].dup2()), fuel, seen))
    } else {
        match cone_entry(pers, st, sol, fe, &work[i]) {
            Err(e) => Err(e),
            Ok(None) => Ok((Some(work[i].dup2()), fuel, seen)),
            Ok(Some(ns)) => {
                let mut s2: HashMap<NIdx, bool> = seen;
                s2.insert(work[i].dup2(), true);
                match cone_go(pers, st, sol, fe, depth - 1, fuel - 1, s2, &ns, 0) {
                    Err(e) => Err(e),
                    Ok((Some(m), f, s)) => Ok((Some(m), f, s)),
                    Ok((None, f, s)) => cone_go(pers, st, sol, fe, depth, f, s, work, i + 1),
                }
            }
        }
    }
}

/// con-leche: none — a rejection's text: the cited `s!` with a name read back
/// The message `pre ++ n ++ post`, the name read back and rendered.
pub fn name_msg(
    pers: &PersTier,
    st: &mut AState,
    pre: Vec<u32>,
    n: &NIdx,
    post: Vec<u32>,
) -> Result<Vec<u32>, CheckError> {
    match read_name_m(pers, st, n) {
        Err(e) => Err(e),
        Ok(nm) => Ok(text::cat3(pre, &name::render(&nm), &post)),
    }
}

/// con-leche: ConLeche/Cached/Justify.lean:185-196 justifyWhy
/// Lean twin: `proof/ConRon/Arena/Justify.lean:270-284 justifyWhy` — **is the statement
/// `cv` justified by the solution**, at the input's index `fe`: `None`, or why
/// not.
pub fn justify_why(
    pers: &PersTier,
    st: &mut AState,
    sol: &Solution,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<Option<Vec<u32>>, CheckError> {
    match solution_find(sol, &cv.name) {
        None => match name_msg(pers, st, code_points(&M_NO_CONSTANT), &cv.name, Vec::new()) {
            Err(e) => Err(e),
            Ok(m) => Ok(Some(m)),
        },
        Some(cs) => {
            let cvs: IConstantVal = i_constant_info_to_constant_val(cs);
            match same_cv_up_to_levels(pers, st, cv, &cvs) {
                Err(e) => Err(e),
                Ok(false) => match name_msg(
                    pers,
                    st,
                    code_points(&M_SOL_PRE),
                    &cv.name,
                    code_points(&M_ANOTHER_TYPE),
                ) {
                    Err(e) => Err(e),
                    Ok(m) => Ok(Some(m)),
                },
                Ok(true) => match needs_go(pers, st, HashMap::new(), Vec::new(), CORE_WALK_FUEL, &cv.ty) {
                    Err(e) => Err(e),
                    Ok((_, ns)) => {
                        let fuel: u64 = (sol.ix.idx.len() as u64) + 1;
                        match cone_go(pers, st, sol, fe, CORE_WALK_FUEL, fuel, HashMap::new(), &ns, 0) {
                            Err(e) => Err(e),
                            Ok((None, _, _)) => Ok(None),
                            Ok((Some(n), _, _)) => match name_msg(
                                pers,
                                st,
                                code_points(&M_TYPE_READS),
                                &n,
                                code_points(&M_NOT_ALIKE),
                            ) {
                                Err(e) => Err(e),
                                Ok(m) => Ok(Some(m)),
                            },
                        }
                    }
                },
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The check of one record, with a solution
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/ParsedC.lean:334-343 declCLabel
/// Lean twin: `proof/ConRon/Arena/Justify.lean:288-300 declLabel` — a record's kind and
/// name, for a message (an empty block's name is the anonymous one).
pub fn decl_label(pers: &PersTier, st: &mut AState, d: &IDeclaration) -> Result<Vec<u32>, CheckError> {
    match d {
        IDeclaration::DefnDecl(cv, _, _) => name_msg(pers, st, code_points(&M_LBL_DEF), &cv.name, Vec::new()),
        IDeclaration::ThmDecl(cv, _) => name_msg(pers, st, code_points(&M_LBL_THM), &cv.name, Vec::new()),
        IDeclaration::OpaqueDecl(cv, _) => name_msg(pers, st, code_points(&M_LBL_OPAQUE), &cv.name, Vec::new()),
        IDeclaration::AxiomDecl(cv) => name_msg(pers, st, code_points(&M_LBL_AXIOM), &cv.name, Vec::new()),
        IDeclaration::QuotDecl(_, cv) => name_msg(pers, st, code_points(&M_LBL_QUOT), &cv.name, Vec::new()),
        IDeclaration::IndDecl(block, _) => {
            if block.len() > 0 {
                let n: NIdx = i_constant_info_name(&block[0]);
                name_msg(pers, st, code_points(&M_LBL_IND), &n, Vec::new())
            } else {
                Ok(text::cat(code_points(&M_LBL_IND), &name::render(&name::anonymous())))
            }
        }
    }
}

/// con-leche: ConLeche/Cached/Justify.lean:200-216 checkRecordC
/// Lean twin: `proof/ConRon/Arena/Justify.lean:302-313 checkJustified` — **the
/// justification route**: the statement `cv` justified by the solution
/// (`justify_why`), its type checked (`check_constant_val`, no reserved name
/// allowed), the reserved names' check, and its axiom pushed.  The cited
/// `flushC` is the job's bracket's (`enter_record`): the route starts from
/// fresh caches already.
pub fn check_justified(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    sol: &Solution,
    fe: IFEnv,
    pd: &IDeclaration,
    cv: &IConstantVal,
) -> Result<IFEnv, CheckError> {
    match justify_why(pers, st, sol, &fe, cv) {
        Err(e) => Err(e),
        Ok(Some(why)) => match decl_label(pers, st, pd) {
            Err(e) => Err(e),
            Ok(lbl) => fail(CheckError::Invalid(text::cat3(lbl, &code_points(&M_NOT_JUSTIFIED), &why))),
        },
        Ok(None) => match check_constant_val(pers, st, mode, &fe, cv, false, false, false) {
            Err(e) => Err(e),
            Ok(()) => match basis_names_ok(pers, st, pd) {
                Err(e) => Err(e),
                Ok(true) => Ok(ifenv_push(pers, fe, IConstantInfo::AxiomInfo(i_constant_val_dup(cv)))),
                Ok(false) => match basis_names_error(pers, st, pd) {
                    Err(e) => Err(e),
                    Ok(e) => fail(e),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Cached/Justify.lean:200-216 checkRecordC
/// Lean twin: `proof/ConRon/Arena/Justify.lean:315-326 checkRecord` — **the check of one
/// record**, with a solution or none.  A record that offers a statement
/// (`justifiable`) takes the justification route where there is a solution;
/// every other record, and every record without one, its own check
/// (`check_decl::check_decl`, the cited `checkDeclStepC` past the bracket's
/// flush).  Without a solution this is one test of the `Option`.
pub fn check_record(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    sol: Option<&Solution>,
    fe: IFEnv,
    pd: &IDeclaration,
) -> Result<IFEnv, CheckError> {
    match sol {
        None => check_decl(pers, st, mode, pins, fe, pd),
        Some(j) => match justifiable(st, pd) {
            Err(e) => Err(e),
            Ok(None) => check_decl(pers, st, mode, pins, fe, pd),
            Ok(Some(cv)) => check_justified(pers, st, mode, j, fe, pd, &cv),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arena::checker::{freeze_tier, intern_all_pins, run_job, thaw_tier, worker_state};
    use crate::arena::intern::{intern_cv, intern_expr};
    use crate::arena::pins::max_nat_size_default;
    use crate::arena::stream_index::{build_index, stream_index_empty};
    use crate::kernel::env::{ConstantVal, ReducibilityHint};
    use crate::kernel::expr;
    use crate::kernel::expr::Expr;
    use crate::kernel::level;
    use crate::kernel::level::Level;
    use crate::kernel::name::Name;

    fn nm(s: &str) -> Name {
        name::mk_str(name::anonymous(), s.chars().map(|c| c as u32).collect())
    }

    fn prop() -> Expr {
        expr::sort(level::zero())
    }

    fn ty() -> Expr {
        expr::sort(level::succ(level::zero()))
    }

    /// A record, written as con-ron-core values; interned by `intern_rec`.
    enum Rec {
        Ax(&'static str, Vec<&'static str>, Expr),
        Def(&'static str, Vec<&'static str>, Expr, Expr),
        Thm(&'static str, Expr, Expr),
    }

    fn cv(n: &str, lps: &Vec<&'static str>, t: Expr) -> ConstantVal {
        let mut ls: Vec<Name> = Vec::new();
        for l in lps {
            ls.push(nm(l));
        }
        ConstantVal { name: nm(n), level_params: ls, ty: t }
    }

    fn intern_rec(pers: &PersTier, st: &mut AState, r: &Rec) -> IDeclaration {
        match r {
            Rec::Ax(n, lps, t) => IDeclaration::AxiomDecl(
                intern_cv(pers, st, &cv(n, lps, expr::dup(t))).ok().unwrap(),
            ),
            Rec::Def(n, lps, t, v) => IDeclaration::DefnDecl(
                intern_cv(pers, st, &cv(n, lps, expr::dup(t))).ok().unwrap(),
                intern_expr(pers, st, v).ok().unwrap(),
                ReducibilityHint::Regular(1),
            ),
            Rec::Thm(n, t, v) => IDeclaration::ThmDecl(
                intern_cv(pers, st, &cv(n, &Vec::new(), expr::dup(t))).ok().unwrap(),
                intern_expr(pers, st, v).ok().unwrap(),
            ),
        }
    }

    /// Every job of `ds` on one worker over the frozen `ix`, in order.
    fn run_all(
        st: &mut AState,
        ix: IStreamIndex,
        ipins: &Vec<INatOpPinSet>,
        sol: Option<&Solution>,
        ds: &Vec<IDeclaration>,
    ) -> (IStreamIndex, Result<(), CheckError>) {
        let tier = freeze_tier(&mut st.store, ix);
        let mut w = worker_state(&st.pins);
        let mut r: Result<(), CheckError> = Ok(());
        let mut k: u64 = 0;
        while (k as usize) < ds.len() && r.is_ok() {
            r = match run_job(&tier, &mut w, &CheckMode::Verified, ipins, sol, ds, k) {
                Ok(()) => Ok(()),
                Err((e, _)) => Err(e),
            };
            k += 1;
        }
        (thaw_tier(&mut st.store, tier), r)
    }

    /// The driver's compare run over hand-built streams: the solution checked
    /// flat, then the challenge (holes as axioms) with its axioms justified by
    /// the solution's index.  The challenge's verdict, its message as text.
    fn compare(sol: &Vec<Rec>, chal: &Vec<Rec>) -> Result<(), String> {
        let pers: &PersTier = &PersTier::empty();
        let mut st = AState::init(crate::arena::store::EStore::empty());
        crate::arena::pins::intern_reserved_pins(pers, &mut st).ok().unwrap();
        let ipins = intern_all_pins(pers, &mut st, &Vec::new(), &max_nat_size_default()).ok().unwrap();
        let mut ds_s: Vec<IDeclaration> = Vec::new();
        for r in sol {
            ds_s.push(intern_rec(pers, &mut st, r));
        }
        let mut ds_c0: Vec<IDeclaration> = Vec::new();
        for r in chal {
            ds_c0.push(intern_rec(pers, &mut st, r));
        }
        let ix_s = build_index(pers, &mut st, stream_index_empty(), &ds_s, 0).ok().unwrap();
        let (ix_s, rs) = run_all(&mut st, ix_s, &ipins, None, &ds_s);
        assert!(rs.is_ok(), "the solution must check");
        let ds_c = side_records(pers, &mut st, &ds_c0, 0, Vec::new()).ok().unwrap();
        let ix_c = build_index(pers, &mut st, stream_index_empty(), &ds_c, 0).ok().unwrap();
        let sol = solution_of(ix_s, &ds_c);
        let (_ix_c, rc) = run_all(&mut st, ix_c, &ipins, Some(&sol), &ds_c);
        match rc {
            Ok(()) => Ok(()),
            Err(CheckError::Invalid(m)) => Err(m.iter().filter_map(|c| char::from_u32(*c)).collect()),
            Err(_) => Err(String::from("<not an invalid>")),
        }
    }

    /// `Prop → Prop`.
    fn prop_to_prop() -> Expr {
        expr::forall_e(prop(), prop())
    }

    /// `∀ p : Prop, p`.
    fn all_props() -> Expr {
        expr::forall_e(prop(), expr::bvar(0))
    }

    #[test]
    fn justified_axiom() {
        let sol = vec![Rec::Def("A", vec![], ty(), prop())];
        let chal = vec![Rec::Ax("A", vec![], ty())];
        assert_eq!(compare(&sol, &chal), Ok(()));
    }

    #[test]
    fn axiom_without_a_solution_constant() {
        let sol = vec![Rec::Def("B", vec![], ty(), prop())];
        let chal = vec![Rec::Ax("A", vec![], ty())];
        assert_eq!(
            compare(&sol, &chal),
            Err(String::from("axiom A is not justified by the solution: the solution has no constant A"))
        );
    }

    #[test]
    fn axiom_with_another_type() {
        let sol = vec![Rec::Def("A", vec![], prop_to_prop(), expr::lam(prop(), expr::bvar(0)))];
        let chal = vec![Rec::Ax("A", vec![], ty())];
        assert_eq!(
            compare(&sol, &chal),
            Err(String::from("axiom A is not justified by the solution: the solution's A has another type"))
        );
    }

    fn t_const() -> Expr {
        expr::mk_const(nm("T"), Vec::new())
    }

    #[test]
    fn a_cone_that_agrees() {
        let sol = vec![Rec::Def("T", vec![], ty(), prop()), Rec::Def("a", vec![], t_const(), all_props())];
        let chal = vec![Rec::Def("T", vec![], ty(), prop()), Rec::Ax("a", vec![], t_const())];
        assert_eq!(compare(&sol, &chal), Ok(()));
    }

    #[test]
    fn a_cone_that_differs() {
        let sol = vec![
            Rec::Def("T", vec![], ty(), prop_to_prop()),
            Rec::Def("a", vec![], t_const(), expr::lam(prop(), expr::bvar(0))),
        ];
        let chal = vec![Rec::Def("T", vec![], ty(), prop()), Rec::Ax("a", vec![], t_const())];
        assert_eq!(
            compare(&sol, &chal),
            Err(String::from(
                "axiom a is not justified by the solution: its type reads T, which the solution does not declare alike"
            ))
        );
    }

    fn sort_succ_param(p: &str) -> Expr {
        expr::sort(level::succ(level::param(nm(p))))
    }

    fn sort_param(p: &str) -> Expr {
        let l: Level = level::param(nm(p));
        expr::sort(l)
    }

    #[test]
    fn level_parameters_renamed() {
        let sol = vec![Rec::Def("A", vec!["v"], sort_succ_param("v"), sort_param("v"))];
        let chal = vec![Rec::Ax("A", vec!["u"], sort_succ_param("u"))];
        assert_eq!(compare(&sol, &chal), Ok(()));
    }

    #[test]
    fn level_parameters_not_a_renaming() {
        let sol = vec![Rec::Def("A", vec!["v", "w"], sort_succ_param("v"), sort_param("v"))];
        let chal = vec![Rec::Ax("A", vec!["u"], sort_succ_param("u"))];
        assert_eq!(
            compare(&sol, &chal),
            Err(String::from("axiom A is not justified by the solution: the solution's A has another type"))
        );
    }

    /// `∀ p : Prop, p → p`.
    fn id_ty() -> Expr {
        expr::forall_e(prop(), expr::forall_e(expr::bvar(0), expr::bvar(1)))
    }

    #[test]
    fn a_hole_is_its_statement() {
        let hole = expr::app(
            expr::mk_const(crate::kernel::basis_names::sorry_ax_name(), vec![level::zero()]),
            id_ty(),
        );
        let sol = vec![Rec::Thm("t", id_ty(), expr::lam(prop(), expr::lam(expr::bvar(0), expr::bvar(0))))];
        let chal = vec![Rec::Thm("t", id_ty(), hole)];
        assert_eq!(compare(&sol, &chal), Ok(()));
        // and against a solution without it
        let sol2 = vec![Rec::Def("A", vec![], ty(), prop())];
        let hole2 = expr::app(
            expr::mk_const(crate::kernel::basis_names::sorry_ax_name(), vec![level::zero()]),
            id_ty(),
        );
        let chal2 = vec![Rec::Thm("t", id_ty(), hole2)];
        assert_eq!(
            compare(&sol2, &chal2),
            Err(String::from("axiom t is not justified by the solution: the solution has no constant t"))
        );
    }

    #[test]
    fn without_a_solution_an_axiom_declines() {
        let pers: &PersTier = &PersTier::empty();
        let mut st = AState::init(crate::arena::store::EStore::empty());
        crate::arena::pins::intern_reserved_pins(pers, &mut st).ok().unwrap();
        let ipins = intern_all_pins(pers, &mut st, &Vec::new(), &max_nat_size_default()).ok().unwrap();
        let ds = vec![intern_rec(pers, &mut st, &Rec::Ax("A", vec![], ty()))];
        let ix = build_index(pers, &mut st, stream_index_empty(), &ds, 0).ok().unwrap();
        let (_, r) = run_all(&mut st, ix, &ipins, None, &ds);
        assert!(matches!(r, Err(CheckError::NotImplemented(_))));
    }
}

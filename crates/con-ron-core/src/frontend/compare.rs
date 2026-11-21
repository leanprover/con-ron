//! `ConLeche/Driver/Compare.lean` — a challenge and its solution, the pure parts
//! (task #165).
//!
//! What the compared run decides of the records and of the `--constant` names
//! before anything is checked: the name a record is found under ([`rec_key`]),
//! its kind for the messages ([`rec_kind`]), a theorem read as the hole it is
//! ([`hole_record`], [`hole_records`]), and a `--constant` name that is no
//! declaration of the challenge module ([`foreign_constant`], over the homes the
//! challenge's read reports, `records::homes_of`).  The run itself, its reads and
//! its lines (`compareG`, `fallbackOnly`, `hoistedNote`, `readFailed`) are the
//! driver's, in `crates/con-ron`.
//!
//! ## Deviations
//!
//! * **`recKey` of an inductive block with no type is `None`**, upstream's
//!   `.anonymous`: a handle of the anonymous name is interned, and this reads a
//!   record without a store.  No block the preparation accepts is empty.
//! * Names are compared by handle: one store interns both reads' names, so equal
//!   names are equal handles.

use crate::arena::env;
use crate::arena::env::IDeclaration;
use crate::arena::handle::NIdx;
use crate::arena::justify::builtin_axiom_name;
use crate::arena::monad::AState;
use crate::arena::pins::pin_sorry_ax;
use crate::arena::store::{EStore, PersTier};
use crate::frontend::nat_op_ground::UsedConsts;
use crate::kernel::core_types::CheckError;
use crate::frontend::olean::view;
use crate::frontend::text;
use crate::ron::hashmap::Dup;
use crate::ron::hashmap::Eq2;
use crate::ron::hashmap2::HashMap2;

/// con-leche: ConLeche/Driver/Compare.lean:48-52 recKey
/// **The name a record is found under**: its constant's, an inductive block's
/// first (`None` for a block with no type, module note).
pub fn rec_key(d: &IDeclaration) -> Option<NIdx> {
    match d {
        IDeclaration::AxiomDecl(cv) => Some(cv.name.dup2()),
        IDeclaration::DefnDecl(cv, _, _) => Some(cv.name.dup2()),
        IDeclaration::ThmDecl(cv, _) => Some(cv.name.dup2()),
        IDeclaration::OpaqueDecl(cv, _) => Some(cv.name.dup2()),
        IDeclaration::QuotDecl(_, cv) => Some(cv.name.dup2()),
        IDeclaration::IndDecl(b, _) => {
            if b.len() == 0 {
                None
            } else {
                Some(env::i_constant_info_name(&b[0]))
            }
        }
    }
}

/// con-leche: ConLeche/Driver/Compare.lean:54-61 recKind
/// A record's kind, for the messages.
pub fn rec_kind(d: &IDeclaration) -> Vec<u32> {
    match d {
        IDeclaration::AxiomDecl(_) => { const M: [u32; 5] = [97, 120, 105, 111, 109]; crate::kernel::core_types::code_points(&M) },
        IDeclaration::DefnDecl(_, _, _) => { const M: [u32; 10] = [100, 101, 102, 105, 110, 105, 116, 105, 111, 110]; crate::kernel::core_types::code_points(&M) },
        IDeclaration::ThmDecl(_, _) => { const M: [u32; 7] = [116, 104, 101, 111, 114, 101, 109]; crate::kernel::core_types::code_points(&M) },
        IDeclaration::OpaqueDecl(_, _) => { const M: [u32; 15] = [111, 112, 97, 113, 117, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116]; crate::kernel::core_types::code_points(&M) },
        IDeclaration::QuotDecl(_, _) => { const M: [u32; 17] = [113, 117, 111, 116, 105, 101, 110, 116, 32, 99, 111, 110, 115, 116, 97, 110, 116]; crate::kernel::core_types::code_points(&M) },
        IDeclaration::IndDecl(_, _) => { const M: [u32; 14] = [105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101]; crate::kernel::core_types::code_points(&M) },
    }
}

/// con-leche: ConLeche/Driver/Compare.lean:63-70 holeRecord
/// Lean twin: `proof/ConRon/Arena/Frontend/Compare.lean:41-53 holeRecord` — **a theorem
/// read as the hole it is** (`--olean --compare`): a theorem whose file says its
/// value uses `sorryAx` (`u`, the read's used constants: `OleanRead`'s
/// `UsedConsts`) is the axiom of its statement; a theorem at a built-in axiom's
/// name keeps its own check, and every other record is itself.
pub fn hole_record<U: UsedConsts>(u: &U, pers: &PersTier, st: &mut AState, d: &IDeclaration) -> Result<IDeclaration, CheckError> {
    match d {
        IDeclaration::ThmDecl(cv, _) => match builtin_axiom_name(st, &cv.name) {
            Err(e) => Err(e),
            Ok(true) => Ok(env::i_declaration_dup(d)),
            Ok(false) => match u.used_consts(pers, st, d) {
                Err(e) => Err(e),
                Ok(us) => match pin_sorry_ax(st) {
                    Err(e) => Err(e),
                    Ok(sa) => {
                        if env::nidx_vec_contains(&us, &sa) {
                            Ok(IDeclaration::AxiomDecl(env::i_constant_val_dup(cv)))
                        } else {
                            Ok(env::i_declaration_dup(d))
                        }
                    }
                },
            },
        },
        _ => Ok(env::i_declaration_dup(d)),
    }
}

/// con-leche: ConLeche/Driver/Compare.lean:132-138 chalRecords
/// Lean twin: `proof/ConRon/Arena/Frontend/Compare.lean:55-62 holeRecordsGo` — the cited
/// `recs.map (holeRecord uses)`: every record from cursor `i` through
/// [`hole_record`], onto `out`.  A loop, one iteration per record
/// (`arena::stream_index::build_index`'s reason).
pub fn hole_records<U: UsedConsts>(
    u: &U,
    pers: &PersTier,
    st: &mut AState,
    ds: &Vec<IDeclaration>,
    i: usize,
    out: Vec<IDeclaration>,
) -> Result<Vec<IDeclaration>, CheckError> {
    let mut out: Vec<IDeclaration> = out;
    let mut i: usize = i;
    loop {
        if i >= ds.len() {
            return Ok(out);
        }
        match hole_record(u, pers, st, &ds[i]) {
            Err(e) => return Err(e),
            Ok(d) => {
                out.push(d);
                i = i + 1;
            }
        }
    }
}

/// con-leche: ConLeche/Driver/Compare.lean:103-110 foreignConstant
/// `homes[c]? != some challenge`: `c` is not a declaration of the challenge module.
pub fn foreign_at(homes: &HashMap2<NIdx, NIdx>, challenge: &NIdx, c: &NIdx) -> bool {
    match homes.get(c) {
        None => true,
        Some(h) => !h.eq2(challenge),
    }
}

/// con-leche: ConLeche/Driver/Compare.lean:103-110 foreignConstant
/// `cs.find? (homes[·]? != some challenge)`, as a position (`cs.len()`: none).
pub fn first_foreign(homes: &HashMap2<NIdx, NIdx>, challenge: &NIdx, cs: &Vec<NIdx>) -> usize {
    let mut i = 0usize;
    while i < cs.len() {
        if foreign_at(homes, challenge, &cs[i]) {
            return i;
        }
        i += 1;
    }
    i
}

/// con-leche: ConLeche/Driver/Compare.lean:103-110 foreignConstant
/// **A `--constant` name that is no declaration of the challenge module**, and
/// why; `homes` the challenge closure's (`records::homes_of`).
pub fn foreign_constant(pers: &PersTier, ar: &EStore, constants: &Option<Vec<NIdx>>, challenge: &NIdx, homes: &HashMap2<NIdx, NIdx>) -> Option<Vec<u32>> {
    match constants {
        None => None,
        Some(cs) => {
            let i = first_foreign(homes, challenge, cs);
            if i < cs.len() {
                let t = text::cat3({ const M: [u32; 11] = [45, 45, 99, 111, 110, 115, 116, 97, 110, 116, 61]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, &cs[i]), &{ const M: [u32; 44] = [58, 32, 110, 111, 116, 32, 97, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 111, 102, 32, 116, 104, 101, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 32, 109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) });
                let t = text::cat(t, &view::name_text(pers, ar, challenge));
                match homes.get(&cs[i]) {
                    Some(h) => Some(text::cat3(t, &{ const M: [u32; 8] = [32, 40, 105, 116, 32, 105, 115, 32]; crate::kernel::core_types::code_points(&M) }, &text::cat(view::name_text(pers, ar, h), &{ const M: [u32; 3] = [39, 115, 41]; crate::kernel::core_types::code_points(&M) }))),
                    None => Some(text::cat(t, &{ const M: [u32; 39] = [32, 40, 110, 111, 32, 109, 111, 100, 117, 108, 101, 32, 111, 102, 32, 105, 116, 115, 32, 99, 108, 111, 115, 117, 114, 101, 32, 100, 101, 99, 108, 97, 114, 101, 115, 32, 105, 116, 41]; crate::kernel::core_types::code_points(&M) })),
                }
            } else {
                None
            }
        }
    }
}

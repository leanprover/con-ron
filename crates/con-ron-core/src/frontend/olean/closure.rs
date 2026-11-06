//! `ConLeche/Frontend/Olean/Closure.lean` — the import closure (task #142).
//!
//! The closure's module order from the headers alone, then every module of it
//! loaded (`olean::lazy`, upstream task #481: a theorem's value stays in its
//! file).
//!
//! ## Deviations
//!
//! * **`parMapExcept` is the sequential map** (`load_closure`).  The store has one
//!   writer and the reader interns as it reads; DESIGN.md's `### Task #142` weighs
//!   the alternatives with the numbers.  The class's model says the two are one.
//! * **The read's heartbeat** (`ReadNotes`, upstream task #484) is the file
//!   seam's: `CheckerIO.liftIO (n.say ..)` and `(n.moduleLoaded ..)` are
//!   `OleanFs::read_notes_say` and `read_notes_module_loaded`, and the notes
//!   themselves, with the pace, belong to the instance (`crates/con-ron`).
//!   Nothing they do changes what the reads return.
//! * **A `List` used as a stack is a `Vec` and its top**: the head of the Lean's
//!   list is the last live element.  The extraction's `Vec` has no `pop`, so the
//!   top is an index and a popped slot stays until it is overwritten.
//! * **Every walk carries fuel** (§3.4, "recursion carries the same explicit
//!   fuel"): [`CLOSURE_FUEL`], as `closureGo` does upstream, spent being an
//!   `Internal` error; `olean::lazy`'s `partial` walks take it too.

use crate::arena::handle::NIdx;
use crate::arena::store::{EStore, PersTier};
use crate::frontend::olean::files;
use crate::frontend::olean::files::OleanFs;
use crate::frontend::olean::lazy;
use crate::frontend::olean::lazy::Loaded;
use crate::frontend::olean::spec::{ImportRec, OleanPins};
use crate::frontend::olean::view;
use crate::frontend::olean::view::OLeanLevel;
use crate::frontend::text;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::ron::hashmap::Dup;
use crate::ron::hashmap2::HashMap2;

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:52-54 closureFuel
/// The walks' step bound: far beyond any closure.
pub const CLOSURE_FUEL: u64 = 1 << 40;

/// con-leche: none — a walk's fuel spent
pub fn out_of_fuel<T>() -> Result<T, CheckError> {
    Err(core_types::internal({ const M: [u32; 42] = [116, 104, 101, 32, 105, 109, 112, 111, 114, 116, 32, 99, 108, 111, 115, 117, 114, 101, 39, 115, 32, 119, 97, 108, 107, 32, 114, 97, 110, 32, 111, 117, 116, 32, 111, 102, 32, 115, 116, 101, 112, 115]; crate::kernel::core_types::code_points(&M) }))
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:23-50 closureGo
/// The cycle check of `closureGo`: the first import of `m` on the walk's current
/// path, if any.
pub fn import_on_path<'a>(imps: &'a Vec<ImportRec>, seen: &HashMap2<NIdx, bool>, done: &HashMap2<NIdx, bool>) -> Option<&'a NIdx> {
    let mut i = 0usize;
    while i < imps.len() {
        let c = &imps[i].module;
        if seen.contains_key(c) && !done.contains_key(c) {
            return Some(c);
        }
        i += 1;
    }
    None
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:23-50 closureGo
/// Push onto the walk's stack with its top at `sp`; the new top.
pub fn walk_push(stack: &mut Vec<(NIdx, bool)>, sp: usize, x: (NIdx, bool)) -> usize {
    if sp < stack.len() {
        stack[sp] = x;
    } else {
        stack.push(x);
    }
    sp + 1
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:23-50 closureGo
/// `kids ++ (m, true) :: rest`, onto the stack; the new top.
pub fn walk_expand(stack: &mut Vec<(NIdx, bool)>, sp: usize, m: &NIdx, imps: &Vec<ImportRec>, seen: &HashMap2<NIdx, bool>) -> usize {
    let mut s = walk_push(stack, sp, (m.dup2(), true));
    let mut i = imps.len();
    while i > 0 {
        i -= 1;
        if !seen.contains_key(&imps[i].module) {
            s = walk_push(stack, s, (imps[i].module.dup2(), false));
        }
    }
    s
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:23-50 closureGo
/// **The import closure, in Lean's module order**: a module after everything it
/// imports, a depth-first post-order, by an explicit stack.  A module whose imports
/// are being expanded is on the walk's current path, so an import of it is a cycle.
pub fn closure_go<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp_dirs: &Vec<Vec<u32>>, stack: Vec<(NIdx, bool)>, top: usize) -> Result<Vec<NIdx>, CheckError> {
    let mut stack = stack;
    let mut sp = top;
    let mut fuel = CLOSURE_FUEL;
    let mut seen: HashMap2<NIdx, bool> = HashMap2::new();
    let mut done: HashMap2<NIdx, bool> = HashMap2::new();
    let mut out: Vec<NIdx> = Vec::new();
    while sp > 0 {
        if fuel == 0 {
            return out_of_fuel();
        }
        fuel -= 1;
        sp -= 1;
        let m: NIdx = stack[sp].0.dup2();
        if stack[sp].1 {
            done.insert(m.dup2(), true);
            out.push(m);
        } else if !seen.contains_key(&m) {
            match files::module_imports(fs, pk, pers, ar, sp_dirs, &m) {
                Err(e) => return Err(e),
                Ok(imps) => {
                    seen.insert(m.dup2(), true);
                    match import_on_path(&imps, &seen, &done) {
                        Some(c) => {
                            let t = text::cat({ const M: [u32; 14] = [105, 109, 112, 111, 114, 116, 32, 99, 121, 99, 108, 101, 58, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, &m));
                            let t = text::cat(t, &{ const M: [u32; 9] = [32, 105, 109, 112, 111, 114, 116, 115, 32]; crate::kernel::core_types::code_points(&M) });
                            return Err(core_types::internal(text::cat(t, &view::name_text(pers, ar, c))));
                        }
                        None => sp = walk_expand(&mut stack, sp, &m, &imps, &seen),
                    }
                }
            }
        }
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:56-58 closureOrder
/// The closure's module order from the roots.
pub fn closure_order<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp_dirs: &Vec<Vec<u32>>, roots: &Vec<NIdx>) -> Result<Vec<NIdx>, CheckError> {
    let mut stack: Vec<(NIdx, bool)> = Vec::with_capacity(roots.len());
    let mut sp = 0usize;
    let mut i = roots.len();
    while i > 0 {
        i -= 1;
        sp = walk_push(&mut stack, sp, (roots[i].dup2(), false));
    }
    closure_go(fs, pk, pers, ar, sp_dirs, stack, sp)
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:62-74 loadModule
/// **Load one module** for the merge, module `idx` of the `total` in the
/// closure's order: its private view, what Lean's own import outside the module
/// system and lean4export load, its theorems' values left in the file
/// (`lazy::load_view`).
pub fn load_module<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp_dirs: &Vec<Vec<u32>>, total: u64, m: &NIdx, idx: u64) -> Result<Loaded, CheckError> {
    match files::read_files(fs, pers, ar, sp_dirs, m, &OLeanLevel::Private) {
        Err(e) => Err(e),
        Ok(f) => {
            let r = lazy::load_view(pk, pers, ar, idx, m, &f);
            let size = match &r {
                Ok(l) => l.constants.len() as u64,
                Err(_) => 0,
            };
            fs.read_notes_module_loaded(total, size);
            r
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:76-88 loadClosure
/// `order.toList.zipIdx`, loaded in order, up to the first failure.
pub fn load_all<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp_dirs: &Vec<Vec<u32>>, order: &Vec<NIdx>) -> Result<Vec<Loaded>, CheckError> {
    let mut out: Vec<Loaded> = Vec::with_capacity(order.len());
    let total = order.len() as u64;
    let mut i = 0usize;
    while i < order.len() {
        match load_module(fs, pk, pers, ar, sp_dirs, total, &order[i], i as u64) {
            Err(e) => return Err(e),
            Ok(l) => out.push(l),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:76-88 loadClosure
/// **The closure, loaded**: its modules in Lean's order (module note on
/// `parMapExcept`), the heartbeat saying when the walk and the load start.
pub fn load_closure<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp_dirs: &Vec<Vec<u32>>, roots: &Vec<NIdx>) -> Result<Vec<Loaded>, CheckError> {
    fs.read_notes_say(&{ const M: [u32; 26] = [116, 114, 97, 99, 105, 110, 103, 32, 116, 104, 101, 32, 105, 109, 112, 111, 114, 116, 32, 99, 108, 111, 115, 117, 114, 101]; crate::kernel::core_types::code_points(&M) });
    match closure_order(fs, pk, pers, ar, sp_dirs, roots) {
        Err(e) => Err(e),
        Ok(order) => {
            let line = text::cat3({ const M: [u32; 8] = [108, 111, 97, 100, 105, 110, 103, 32]; crate::kernel::core_types::code_points(&M) }, &text::u64_str(order.len() as u64), &{ const M: [u32; 8] = [32, 109, 111, 100, 117, 108, 101, 115]; crate::kernel::core_types::code_points(&M) });
            fs.read_notes_say(&line);
            load_all(fs, pk, pers, ar, sp_dirs, &order)
        }
    }
}

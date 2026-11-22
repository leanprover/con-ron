//! `ConLeche/Frontend/Olean/Levels.lean` — what Lean loads for a module, from
//! the headers (task #166).
//!
//! The levels are the least fixpoint of the rules of Lean's `importModulesCore`
//! lattice over two flags per module (`LoadFlags`); the order is Lean's
//! `moduleNames` restricted to the modules with data.  Each module's header is
//! read once (`files::module_imports`), nothing else of its files.
//!
//! ## Deviations
//!
//! * **The worklist is a `Vec` and its top**, the head of the Lean's list the
//!   last live element, as `olean::closure`'s walk: a popped slot stays until
//!   it is overwritten.
//! * **The header read is the search path's** (`files::module_imports`), where
//!   upstream takes any `imps` (a worker answers from tables read up front,
//!   `Driver/Tables.lean`, performance only).
//! * `ModSet` is a `Vec<u8>`, upstream's `ByteArray`.

use crate::arena::handle::NIdx;
use crate::arena::store::{EStore, PersTier};
use crate::frontend::olean::closure;
use crate::frontend::olean::files;
use crate::frontend::olean::files::OleanFs;
use crate::frontend::olean::spec::{ImportF, ImportRec, OleanPins};
use crate::frontend::olean::view;
use crate::frontend::olean::view::OLeanLevel;
use crate::frontend::text;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::ron::hashmap::Dup;
use crate::ron::hashmap2::HashMap2;

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:36-42 LoadFlags
/// **A loaded module's two flags** in `importModulesCore`'s lattice.
pub struct LoadFlags {
    pub import_all: bool,
    pub is_exported: bool,
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:36-42 LoadFlags
/// The flags, copied.
pub fn load_flags_dup(l: &LoadFlags) -> LoadFlags {
    LoadFlags { import_all: l.import_all, is_exported: l.is_exported }
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:36-42 LoadFlags
/// The derived `BEq`.
pub fn load_flags_beq(a: &LoadFlags, b: &LoadFlags) -> bool {
    a.import_all == b.import_all && a.is_exported == b.is_exported
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:44-45 LoadFlags.level
/// The part of a module the fixpoint loads.
pub fn load_flags_level(l: &LoadFlags) -> OLeanLevel {
    if l.import_all {
        OLeanLevel::Private
    } else {
        OLeanLevel::Exported
    }
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:47-52 LvWork
/// One step of the fixpoint's worklist.
pub enum LvWork {
    /// an import of a module at its flags
    Imp(LoadFlags, ImportRec),
    /// a newly met module's imports are done: it takes its place in the order
    Done(NIdx, LoadFlags),
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:47-52 LvWork
/// A step, copied.
pub fn lv_work_dup(w: &LvWork) -> LvWork {
    match w {
        LvWork::Imp(pf, i) => LvWork::Imp(load_flags_dup(pf), import_rec_dup(i)),
        LvWork::Done(m, fl) => LvWork::Done(m.dup2(), load_flags_dup(fl)),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:403-404 ImportRec
/// An import, copied.
pub fn import_rec_dup(i: &ImportRec) -> ImportRec {
    ImportF { module: i.module.dup2(), import_all: i.import_all, is_exported: i.is_exported, is_meta: i.is_meta }
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:54-63 LvState
/// The fixpoint's state.
pub struct LvState {
    /// the flags of every module that has its place
    pub flags: HashMap2<NIdx, LoadFlags>,
    /// the modules met but not yet placed
    pub open: HashMap2<NIdx, bool>,
    /// the modules in Lean's order (`moduleNames`)
    pub order: Vec<NIdx>,
    /// every met module's imports, read once
    pub imports: HashMap2<NIdx, Vec<ImportRec>>,
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:54-63 LvState
/// The empty state (the structure's defaults).
pub fn lv_state_empty() -> LvState {
    LvState { flags: HashMap2::new(), open: HashMap2::new(), order: Vec::new(), imports: HashMap2::new() }
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:69-111 levelsGo
/// Push onto the worklist with its top at `sp`; the new top.
pub fn lv_push(stack: &mut Vec<LvWork>, sp: usize, x: LvWork) -> usize {
    if sp < stack.len() {
        stack[sp] = x;
    } else {
        stack.push(x);
    }
    sp + 1
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:65-67 LvWork.ofImports
/// `LvWork.ofImports fl imps ++ rest`, onto the worklist (the first import on
/// top); the new top.
pub fn lv_push_imports(stack: &mut Vec<LvWork>, sp: usize, fl: &LoadFlags, imps: &Vec<ImportRec>) -> usize {
    let mut s = sp;
    let mut i = imps.len();
    while i > 0 {
        i -= 1;
        s = lv_push(stack, s, LvWork::Imp(load_flags_dup(fl), import_rec_dup(&imps[i])));
    }
    s
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:69-111 levelsGo
/// The fixpoint's steps spent.
pub fn levels_out_of_fuel<T>() -> Result<T, CheckError> {
    Err(core_types::internal({ const M: [u32; 36] = [116, 104, 101, 32, 104, 101, 97, 100, 101, 114, 32, 102, 105, 120, 112, 111, 105, 110, 116, 32, 114, 97, 110, 32, 111, 117, 116, 32, 111, 102, 32, 115, 116, 101, 112, 115]; crate::kernel::core_types::code_points(&M) }))
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:69-111 levelsGo
/// A module met again while its own imports are expanded.
pub fn levels_cycle(pers: &PersTier, ar: &EStore, m: &NIdx) -> CheckError {
    let t = text::cat({ const M: [u32; 33] = [105, 109, 112, 111, 114, 116, 32, 99, 121, 99, 108, 101, 58, 32, 97, 32, 109, 111, 100, 117, 108, 101, 32, 105, 109, 112, 111, 114, 116, 105, 110, 103, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, m));
    core_types::internal(text::cat(t, &{ const M: [u32; 18] = [32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 98, 121, 32, 105, 116]; crate::kernel::core_types::code_points(&M) }))
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:69-111 levelsGo
/// A module with its place, met again at flags `fl`: its flags joined with
/// them, where they grow (`None`: they do not).
pub fn levels_join(flags: &HashMap2<NIdx, LoadFlags>, fl: &LoadFlags, m: &NIdx) -> Option<LoadFlags> {
    match flags.get(m) {
        None => None,
        Some(old) => {
            let j = LoadFlags { import_all: fl.import_all || old.import_all, is_exported: fl.is_exported || old.is_exported };
            if load_flags_beq(&j, old) {
                None
            } else {
                Some(j)
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:69-111 levelsGo
/// A met module's imports, again, at its joined flags, onto the worklist; the
/// new top.
pub fn levels_again(stack: &mut Vec<LvWork>, sp: usize, imports: &HashMap2<NIdx, Vec<ImportRec>>, fl: &LoadFlags, m: &NIdx) -> usize {
    match imports.get(m) {
        Some(is) => lv_push_imports(stack, sp, fl, is),
        None => sp,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:69-111 levelsGo
/// **The fixpoint's worklist** (`importModulesCore.go`, iterative).  At `imp pf
/// i`: followed if the importer's data is loaded and the import is public or
/// the importer is loaded whole; a module with its place has its flags joined
/// (`levels_join`); a module met for the first time has its header read, its
/// imports expanded at its flags and its place after them (`done`).  A module
/// met again while its own imports are expanded is an import cycle.  `fuel`
/// bounds the steps.
pub fn levels_go<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp_dirs: &files::Roots, g_priv: bool, stack: Vec<LvWork>, top: usize, st: LvState) -> Result<LvState, CheckError> {
    let mut stack = stack;
    let mut sp = top;
    let mut st = st;
    let mut fuel = closure::CLOSURE_FUEL;
    while sp > 0 {
        if fuel == 0 {
            return levels_out_of_fuel();
        }
        fuel -= 1;
        sp -= 1;
        match lv_work_dup(&stack[sp]) {
            LvWork::Done(m, fl) => {
                st.flags.insert(m.dup2(), fl);
                st.open.remove(&m);
                st.order.push(m);
            }
            LvWork::Imp(pf, i) => {
                if i.is_exported || pf.import_all {
                    let fl = LoadFlags { import_all: g_priv || (pf.import_all && i.import_all), is_exported: pf.is_exported && i.is_exported };
                    let m: NIdx = i.module;
                    if st.flags.contains_key(&m) {
                        match levels_join(&st.flags, &fl, &m) {
                            None => {}
                            Some(fl2) => {
                                sp = levels_again(&mut stack, sp, &st.imports, &fl2, &m);
                                st.flags.insert(m, fl2);
                            }
                        }
                    } else if st.open.contains_key(&m) {
                        return Err(levels_cycle(pers, ar, &m));
                    } else {
                        match files::module_imports(fs, pk, pers, ar, sp_dirs, &m) {
                            Err(e) => return Err(e),
                            Ok(is) => {
                                sp = lv_push(&mut stack, sp, LvWork::Done(m.dup2(), load_flags_dup(&fl)));
                                sp = lv_push_imports(&mut stack, sp, &fl, &is);
                                st.open.insert(m.dup2(), true);
                                st.imports.insert(m, is);
                            }
                        }
                    }
                }
            }
        }
    }
    Ok(st)
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:113-122 HeaderLoads
/// **What Lean loads for a module**: its header's fixpoint, in Lean's module
/// order.
pub struct HeaderLoads {
    /// the loaded modules, in Lean's order
    pub order: Vec<NIdx>,
    /// by position in `order`: the module's flags
    pub flags: Vec<LoadFlags>,
    /// by position in `order`: the module's imports, off the start of its `M.olean`
    pub imports: Vec<Vec<ImportRec>>,
    /// a module's position in `order`
    pub index: HashMap2<NIdx, u64>,
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:124-153 headerFixpoint
/// The fixpoint's state as `HeaderLoads`: by position in the order, each
/// module's flags and imports (moved out of the state), and the positions.
pub fn header_loads_of(st: LvState) -> HeaderLoads {
    let mut st = st;
    let n = st.order.len();
    let mut flags: Vec<LoadFlags> = Vec::with_capacity(n);
    let mut imports: Vec<Vec<ImportRec>> = Vec::with_capacity(n);
    let mut index: HashMap2<NIdx, u64> = HashMap2::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        let m: NIdx = st.order[i].dup2();
        flags.push(flags_at(&st.flags, &m));
        imports.push(imports_out(&mut st.imports, &m));
        index.insert(m, i as u64);
        i += 1;
    }
    HeaderLoads { order: st.order, flags, imports, index }
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:124-153 headerFixpoint
/// `(st.flags[m]?).getD default`.
pub fn flags_at(flags: &HashMap2<NIdx, LoadFlags>, m: &NIdx) -> LoadFlags {
    match flags.get(m) {
        Some(fl) => load_flags_dup(fl),
        None => LoadFlags { import_all: false, is_exported: false },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:124-153 headerFixpoint
/// `(st.imports[m]?).getD #[]`, moved out of the state (each module is read
/// once).
pub fn imports_out(imports: &mut HashMap2<NIdx, Vec<ImportRec>>, m: &NIdx) -> Vec<ImportRec> {
    match imports.remove(m) {
        Some(is) => is,
        None => Vec::new(),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:124-153 headerFixpoint
/// **The header fixpoint** of a module whose header says `is_module` and
/// `imports`: every module Lean's `importModulesCore` loads for it, in Lean's
/// module order, with the part it loads of each (`load_flags_level`).
pub fn header_fixpoint<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp_dirs: &files::Roots, is_module: bool, imports: &Vec<ImportRec>) -> Result<HeaderLoads, CheckError> {
    let root = LoadFlags { import_all: true, is_exported: is_module };
    let mut stack: Vec<LvWork> = Vec::with_capacity(imports.len());
    let sp = lv_push_imports(&mut stack, 0, &root, imports);
    match levels_go(fs, pk, pers, ar, sp_dirs, !is_module, stack, sp, lv_state_empty()) {
        Err(e) => Err(e),
        Ok(st) => Ok(header_loads_of(st)),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:160-161 ModSet.empty
/// The empty set over `n` modules.
pub fn mod_set_empty(n: u64) -> Vec<u8> {
    let k = ((n + 7) / 8) as usize;
    let mut s: Vec<u8> = Vec::with_capacity(k);
    let mut i = 0usize;
    while i < k {
        s.push(0);
        i += 1;
    }
    s
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:163-165 ModSet.has
/// Is position `i` in the set.
pub fn mod_set_has(s: &Vec<u8>, i: u64) -> bool {
    let b = (i / 8) as usize;
    if b < s.len() {
        (s[b] >> ((i % 8) as u8)) & 1 == 1
    } else {
        false
    }
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:167-169 ModSet.add
/// The set with position `i` added.
pub fn mod_set_add(s: Vec<u8>, i: u64) -> Vec<u8> {
    let mut s = s;
    let b = (i / 8) as usize;
    if b < s.len() {
        s[b] = s[b] | (1u8 << ((i % 8) as u8));
    }
    s
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:171-173 ModSet.union
/// The union of two sets of one size.
pub fn mod_set_union(s: Vec<u8>, t: &Vec<u8>) -> Vec<u8> {
    let mut s = s;
    let mut k = 0usize;
    while k < t.len() {
        if k < s.len() {
            s[k] = s[k] | t[k];
        }
        k += 1;
    }
    s
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:179-193 pubClosures
/// One module's public-import closure, from those of the modules before it:
/// itself, and every public import's closure (or the import itself, where it
/// is not placed before it).
pub fn pub_closure_at(ld: &HeaderLoads, acc: &Vec<Vec<u8>>, i: usize) -> Vec<u8> {
    let n = ld.order.len() as u64;
    let mut s = mod_set_add(mod_set_empty(n), i as u64);
    if i < ld.imports.len() {
        let imps = &ld.imports[i];
        let mut k = 0usize;
        while k < imps.len() {
            s = pub_closure_step(ld, acc, s, &imps[k]);
            k += 1;
        }
    }
    s
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:179-193 pubClosures
/// One import of a module: a public one's closure joined (its own position,
/// where it is not placed yet).
pub fn pub_closure_step(ld: &HeaderLoads, acc: &Vec<Vec<u8>>, s: Vec<u8>, imp: &ImportRec) -> Vec<u8> {
    if !imp.is_exported {
        return s;
    }
    match ld.index.get(&imp.module) {
        Some(j) => {
            if (*j as usize) < acc.len() {
                mod_set_union(s, &acc[*j as usize])
            } else {
                mod_set_add(s, *j)
            }
        }
        None => s,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:179-193 pubClosures
/// **Each loaded module's public-import closure**: the modules a path of
/// `public import`s leads to from it, itself included, by position in the load
/// order.  A public import of a loaded module is placed before it, so one pass
/// in order.
pub fn pub_closures(ld: &HeaderLoads) -> Vec<Vec<u8>> {
    let n = ld.order.len();
    let mut acc: Vec<Vec<u8>> = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        let s = pub_closure_at(ld, &acc, i);
        acc.push(s);
        i += 1;
    }
    acc
}

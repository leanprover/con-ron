//! `ConLeche/Driver/Graph.lean` — the import graph of a closure, checked (task
//! #166; upstream task #467).
//!
//! The header of every module of the roots' import closure is read
//! (`files::module_imports`), and the graph is checked **acyclic** with every
//! import resolving: an order is computed (Kahn's worklist, `kahn`) and
//! validated (`verdict`): every module of the closure has a rank, no two the
//! same, and every import edge goes to a smaller rank.  The closure and its
//! edges are every import of every kind.  Upstream's exit-code wrapper
//! (`checkGraphG`, its two lines) is the driver's.
//!
//! ## Deviations
//!
//! * **`parMapExcept` is the sequential map** (`olean::closure`'s note), and
//!   upstream's `jobs` is not a parameter.
//! * **No `Roots` cache** (`files::find_module`'s note): `closure_levels`
//!   returns the closure alone, where upstream returns it with the roots it
//!   resolved.
//! * **The imports a run adds** (`extra : Name → Array ImportRec`, a compared
//!   challenge's solution) are the pair `cmp` (challenge, solution), `None`
//!   for none: the two functions upstream's callers pass (`cmpExtra C S`, or no
//!   import).
//! * **A rank function is two tables**, the closure's positions (`index_of`)
//!   and the positions' ranks (`ranks_of`), read by `rank_of`.
//! * `Array.modify`/`set!`/`get!` out of range are a guarded no-op / the
//!   default, as upstream's.

use crate::arena::env;
use crate::arena::handle::NIdx;
use crate::arena::store::{EStore, PersTier};
use crate::frontend::olean::files;
use crate::frontend::olean::files::OleanFs;
use crate::frontend::olean::levels;
use crate::frontend::olean::spec::{ImportF, ImportRec, OleanPins};
use crate::frontend::olean::view;
use crate::frontend::text;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::ron::hashmap::{Dup, Eq2};
use crate::ron::hashmap2::HashMap2;

/// con-leche: ConLeche/Driver/Graph.lean:38-40 solutionImport
/// **The import a compared run adds to the challenge's header**: the solution,
/// `import all`.
pub fn solution_import(s: &NIdx) -> ImportRec {
    ImportF { module: s.dup2(), import_all: true, is_exported: false, is_meta: false }
}

/// con-leche: ConLeche/Driver/Graph.lean:42-45 cmpExtra
/// **The imports a modular run adds to a header**: the solution to the
/// challenge's, none to any other module's (`cmp`: the challenge and the
/// solution; `None`, no import added anywhere).
pub fn cmp_extra(cmp: &Option<(NIdx, NIdx)>, m: &NIdx) -> Vec<ImportRec> {
    let mut v: Vec<ImportRec> = Vec::new();
    match cmp {
        Some((c, s)) => {
            if m.eq2(c) {
                v.push(solution_import(s));
            }
        }
        None => {}
    }
    v
}

/// con-leche: ConLeche/Driver/Graph.lean:48-58 missingOn
/// Whether one of a module's files is at a directory.
pub fn file_at<F: OleanFs>(fs: &F, d: &Vec<u32>, n: &crate::kernel::name::Name, ext: &Vec<u32>) -> Result<bool, CheckError> {
    match fs.path_exists(&files::mod_file_of(d, n, ext)) {
        Err(e) => Err(core_types::internal(e)),
        Ok(b) => Ok(b),
    }
}

/// con-leche: ConLeche/Driver/Graph.lean:48-58 missingOn
/// Whether the search path has none of `m`'s files: no directory of it holds
/// `m`'s root, or the one that does holds none of `m`'s three files.
/// Deviation: a failed existence test is its message (upstream's model has
/// none).
pub fn missing_on<F: OleanFs>(fs: &F, pers: &PersTier, ar: &EStore, sp: &files::Roots, m: &NIdx) -> Result<bool, CheckError> {
    let n = match env::read_name(pers, ar, m) {
        Err(e) => return Err(e),
        Ok(n) => n,
    };
    match files::look_at(fs, &sp.path, &sp.fallback, &files::name_root(&n)) {
        files::RootAt::Missing => Ok(true),
        files::RootAt::Dir(d) => {
            match file_at(fs, &d, &n, &{ const M: [u32; 5] = [111, 108, 101, 97, 110]; crate::kernel::core_types::code_points(&M) }) {
                Err(e) => return Err(e),
                Ok(true) => return Ok(false),
                Ok(false) => {}
            }
            match file_at(fs, &d, &n, &{ const M: [u32; 12] = [111, 108, 101, 97, 110, 46, 115, 101, 114, 118, 101, 114]; crate::kernel::core_types::code_points(&M) }) {
                Err(e) => return Err(e),
                Ok(true) => return Ok(false),
                Ok(false) => {}
            }
            match file_at(fs, &d, &n, &{ const M: [u32; 13] = [111, 108, 101, 97, 110, 46, 112, 114, 105, 118, 97, 116, 101]; crate::kernel::core_types::code_points(&M) }) {
                Err(e) => Err(e),
                Ok(b) => Ok(!b),
            }
        }
        _ => Ok(false),
    }
}

/// con-leche: ConLeche/Driver/Graph.lean:60-70 hdrOf
/// **A module's imports**, read off its header (`module_imports`), followed by
/// the imports the run adds to it; a module the search path does not have is
/// invalid input.
pub fn hdr_of<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp: &files::Roots, cmp: &Option<(NIdx, NIdx)>, m: &NIdx) -> Result<(NIdx, Vec<ImportRec>), CheckError> {
    match files::module_imports(fs, pk, pers, ar, sp, m) {
        Ok(imps) => {
            let mut imps = imps;
            let x = cmp_extra(cmp, m);
            let mut i = 0usize;
            while i < x.len() {
                imps.push(levels::import_rec_dup(&x[i]));
                i += 1;
            }
            Ok((m.dup2(), imps))
        }
        Err(e) => match missing_on(fs, pers, ar, sp, m) {
            Err(e2) => Err(e2),
            Ok(true) => {
                let t = text::cat({ const M: [u32; 7] = [109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, m));
                Err(core_types::invalid(text::cat(t, &{ const M: [u32; 30] = [58, 32, 110, 111, 32, 46, 111, 108, 101, 97, 110, 32, 111, 110, 32, 116, 104, 101, 32, 115, 101, 97, 114, 99, 104, 32, 112, 97, 116, 104]; crate::kernel::core_types::code_points(&M) })))
            }
            Ok(false) => Err(e),
        },
    }
}

/// con-leche: ConLeche/Driver/Graph.lean:72-80 expand
/// **One level of the walk**: the modules read, in order, onto `out`, and the
/// imports not yet seen onto `next`, the next level.
pub fn expand(pk: &OleanPins, seen: &mut HashMap2<NIdx, bool>, out: &mut Vec<(NIdx, Vec<ImportRec>)>, next: &mut Vec<NIdx>, rs: Vec<(NIdx, Vec<ImportRec>)>) {
    let mut rs = rs;
    let mut i = 0usize;
    while i < rs.len() {
        let imps = &rs[i].1;
        let mut k = 0usize;
        while k < imps.len() {
            if !seen.contains_key(&imps[k].module) {
                seen.insert(imps[k].module.dup2(), true);
                next.push(imps[k].module.dup2());
            }
            k += 1;
        }
        out.push(core::mem::replace(&mut rs[i], (pk.anon.dup2(), Vec::new())));
        i += 1;
    }
}

/// con-leche: ConLeche/Driver/Graph.lean:99-100 levelFuel
/// The walk's level bound: far beyond any closure.
pub const LEVEL_FUEL: u64 = 1 << 40;

/// con-leche: ConLeche/Driver/Graph.lean:82-97 closureLevels
/// One level's headers, read in order.
pub fn level_hdrs<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp: &files::Roots, cmp: &Option<(NIdx, NIdx)>, lvl: &Vec<NIdx>) -> Result<Vec<(NIdx, Vec<ImportRec>)>, CheckError> {
    let mut rs: Vec<(NIdx, Vec<ImportRec>)> = Vec::with_capacity(lvl.len());
    let mut i = 0usize;
    while i < lvl.len() {
        match hdr_of(fs, pk, pers, ar, sp, cmp, &lvl[i]) {
            Err(e) => return Err(e),
            Ok(r) => rs.push(r),
        }
        i += 1;
    }
    Ok(rs)
}

/// con-leche: ConLeche/Driver/Graph.lean:82-97 closureLevels
/// **The closure, level by level**: a level's headers read, the modules first
/// met there the next level.  `LEVEL_FUEL` bounds the levels, an internal error
/// when spent.
pub fn closure_levels<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp: &files::Roots, cmp: &Option<(NIdx, NIdx)>, lvl: Vec<NIdx>, seen: HashMap2<NIdx, bool>, out: Vec<(NIdx, Vec<ImportRec>)>) -> Result<Vec<(NIdx, Vec<ImportRec>)>, CheckError> {
    let mut lvl = lvl;
    let mut seen = seen;
    let mut out = out;
    let mut fuel = LEVEL_FUEL;
    while lvl.len() > 0 {
        if fuel == 0 {
            return Err(core_types::internal({ const M: [u32; 35] = [116, 104, 101, 32, 99, 108, 111, 115, 117, 114, 101, 39, 115, 32, 119, 97, 108, 107, 32, 114, 97, 110, 32, 111, 117, 116, 32, 111, 102, 32, 115, 116, 101, 112, 115]; crate::kernel::core_types::code_points(&M) }));
        }
        fuel -= 1;
        match level_hdrs(fs, pk, pers, ar, sp, cmp, &lvl) {
            Err(e) => return Err(e),
            Ok(rs) => {
                let mut next: Vec<NIdx> = Vec::new();
                expand(pk, &mut seen, &mut out, &mut next, rs);
                lvl = next;
            }
        }
    }
    Ok(out)
}

/// con-leche: ConLeche/Driver/Graph.lean:102-106 dedup
/// The roots, each once, in order, and the set of them.
pub fn dedup(xs: &Vec<NIdx>) -> (Vec<NIdx>, HashMap2<NIdx, bool>) {
    let mut s: HashMap2<NIdx, bool> = HashMap2::new();
    let mut acc: Vec<NIdx> = Vec::new();
    let mut i = 0usize;
    while i < xs.len() {
        if !s.contains_key(&xs[i]) {
            s.insert(xs[i].dup2(), true);
            acc.push(xs[i].dup2());
        }
        i += 1;
    }
    (acc, s)
}

/// con-leche: ConLeche/Driver/Graph.lean:110-115 indexOf
/// Each module's position in the closure.
pub fn index_of(c: &Vec<(NIdx, Vec<ImportRec>)>) -> HashMap2<NIdx, u64> {
    let mut idx: HashMap2<NIdx, u64> = HashMap2::new();
    let mut k = 0usize;
    while k < c.len() {
        idx.insert(c[k].0.dup2(), k as u64);
        k += 1;
    }
    idx
}

/// con-leche: ConLeche/Driver/Graph.lean:117-120 depsOf
/// `idx[m]?`.
pub fn idx_lookup(idx: &HashMap2<NIdx, u64>, m: &NIdx) -> Option<u64> {
    match idx.get(m) {
        Some(j) => Some(*j),
        None => None,
    }
}

/// con-leche: ConLeche/Driver/Graph.lean:117-120 depsOf
/// Each module's imports, by position (an import outside the closure left
/// out).
pub fn deps_of(idx: &HashMap2<NIdx, u64>, c: &Vec<(NIdx, Vec<ImportRec>)>) -> Vec<Vec<u64>> {
    let mut out: Vec<Vec<u64>> = Vec::with_capacity(c.len());
    let mut k = 0usize;
    while k < c.len() {
        let imps = &c[k].1;
        let mut d: Vec<u64> = Vec::with_capacity(imps.len());
        let mut i = 0usize;
        while i < imps.len() {
            match idx_lookup(idx, &imps[i].module) {
                Some(j) => d.push(j),
                None => {}
            }
            i += 1;
        }
        out.push(d);
        k += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Graph.lean:122-146 kahn
/// `users`: each position's importers, an importer once per edge.
pub fn kahn_users(deps: &Vec<Vec<u64>>) -> Vec<Vec<u64>> {
    let n = deps.len();
    let mut users: Vec<Vec<u64>> = Vec::with_capacity(n);
    let mut k = 0usize;
    while k < n {
        users.push(Vec::new());
        k += 1;
    }
    let mut x = 0usize;
    while x < n {
        let d = &deps[x];
        let mut i = 0usize;
        while i < d.len() {
            let j = d[i] as usize;
            if j < users.len() {
                users[j].push(x as u64);
            }
            i += 1;
        }
        x += 1;
    }
    users
}

/// con-leche: ConLeche/Driver/Graph.lean:122-146 kahn
/// **Kahn's worklist**: the positions in an order where each comes after
/// everything it imports; on a cyclic graph, the part of it that waits on no
/// cycle.  `wait` is each module's number of import edges not yet released.
pub fn kahn(deps: &Vec<Vec<u64>>) -> Vec<u64> {
    let n = deps.len();
    let users = kahn_users(deps);
    let mut wait: Vec<u64> = Vec::with_capacity(n);
    let mut q: Vec<u64> = Vec::new();
    let mut k = 0usize;
    while k < n {
        wait.push(deps[k].len() as u64);
        if deps[k].len() == 0 {
            q.push(k as u64);
        }
        k += 1;
    }
    let mut i = 0usize;
    let mut t = 0usize;
    while t < n && i < q.len() {
        let x = q[i] as usize;
        if x < users.len() {
            let us = &users[x];
            let mut u = 0usize;
            while u < us.len() {
                let y = us[u] as usize;
                if y < wait.len() {
                    let w = wait[y];
                    if w > 0 {
                        wait[y] = w - 1;
                    }
                    if w == 1 {
                        q.push(us[u]);
                    }
                }
                u += 1;
            }
        }
        i += 1;
        t += 1;
    }
    q
}

/// con-leche: ConLeche/Driver/Graph.lean:148-153 ranksOf
/// **The ranks**: a position's place in the order, `None` for a position the
/// order lacks.
pub fn ranks_of(n: u64, ord: &Vec<u64>) -> Vec<Option<u64>> {
    let mut rank: Vec<Option<u64>> = Vec::with_capacity(n as usize);
    let mut k = 0u64;
    while k < n {
        rank.push(None);
        k += 1;
    }
    let mut t = 0usize;
    while t < ord.len() {
        let p = ord[t] as usize;
        if p < rank.len() {
            rank[p] = Some(t as u64);
        }
        t += 1;
    }
    rank
}

/// con-leche: ConLeche/Driver/Graph.lean:155-157 rankOf
/// A module's rank, by name.
pub fn rank_of(idx: &HashMap2<NIdx, u64>, rank: &Vec<Option<u64>>, m: &NIdx) -> Option<u64> {
    match idx.get(m) {
        None => None,
        Some(k) => {
            let i = *k as usize;
            if i < rank.len() {
                match &rank[i] {
                    Some(r) => Some(*r),
                    None => None,
                }
            } else {
                None
            }
        }
    }
}

/// con-leche: ConLeche/Driver/Graph.lean:159-180 cycleOf
/// The first position the order lacks (`ord`'s positions marked done).
pub fn cycle_start(n: usize, done: &Vec<bool>) -> Option<usize> {
    let mut k = 0usize;
    while k < n {
        if !done[k] {
            return Some(k);
        }
        k += 1;
    }
    None
}

/// con-leche: ConLeche/Driver/Graph.lean:159-180 cycleOf
/// The first import of `x` outside the order.
pub fn cycle_next(deps: &Vec<Vec<u64>>, done: &Vec<bool>, x: usize) -> Option<usize> {
    if x < deps.len() {
        let d = &deps[x];
        let mut i = 0usize;
        while i < d.len() {
            let y = d[i] as usize;
            if !(y < done.len() && done[y]) {
                return Some(y);
            }
            i += 1;
        }
    }
    None
}

/// con-leche: ConLeche/Driver/Graph.lean:159-180 cycleOf
/// One step of the walk at `x`: a repeat (its first visit's place on the
/// path), or `x` on the path and the next module (`None`: no import of `x`
/// outside the order).
pub enum CycleStep {
    Repeat(u64),
    Next(Option<usize>),
}

/// con-leche: ConLeche/Driver/Graph.lean:159-180 cycleOf
/// `if let some p := at?[x]! then … ; at? := at?.set! x (some path.size); path :=
/// path.push x; deps[x]!.find? (!done[·]!)`.
pub fn cycle_step(deps: &Vec<Vec<u64>>, done: &Vec<bool>, at: &mut Vec<Option<u64>>, path: &mut Vec<u64>, x: usize) -> CycleStep {
    if x < at.len() {
        match &at[x] {
            Some(p) => return CycleStep::Repeat(*p),
            None => {}
        }
        at[x] = Some(path.len() as u64);
    }
    path.push(x as u64);
    CycleStep::Next(cycle_next(deps, done, x))
}

/// con-leche: ConLeche/Driver/Graph.lean:159-180 cycleOf
/// The positions `ord` lists, marked.
pub fn done_of(n: usize, ord: &Vec<u64>) -> Vec<bool> {
    let mut done: Vec<bool> = Vec::with_capacity(n);
    let mut k = 0usize;
    while k < n {
        done.push(false);
        k += 1;
    }
    let mut j = 0usize;
    while j < ord.len() {
        let p = ord[j] as usize;
        if p < done.len() {
            done[p] = true;
        }
        j += 1;
    }
    done
}

/// con-leche: ConLeche/Driver/Graph.lean:159-180 cycleOf
/// **A cycle**, given the order: from the first module outside it, an import
/// outside it, until a module repeats; the modules from its first visit on, in
/// import order.
pub fn cycle_of(deps: &Vec<Vec<u64>>, ord: &Vec<u64>) -> Option<Vec<u64>> {
    let n = deps.len();
    let done = done_of(n, ord);
    match cycle_start(n, &done) {
        None => None,
        Some(s) => {
            let mut path: Vec<u64> = Vec::new();
            let mut at: Vec<Option<u64>> = Vec::with_capacity(n);
            let mut a = 0usize;
            while a < n {
                at.push(None);
                a += 1;
            }
            let mut x = s;
            let mut rep: Option<u64> = None;
            let mut fin = false;
            let mut t = 0usize;
            while t < n + 1 && !fin {
                match cycle_step(deps, &done, &mut at, &mut path, x) {
                    CycleStep::Repeat(p) => {
                        rep = Some(p);
                        fin = true;
                    }
                    CycleStep::Next(Some(y)) => x = y,
                    CycleStep::Next(None) => fin = true,
                }
                t += 1;
            }
            match rep {
                Some(p) => Some(path_from(&path, p as usize)),
                None => Some(path),
            }
        }
    }
}

/// con-leche: ConLeche/Driver/Graph.lean:159-180 cycleOf
/// `path.extract p path.size`.
pub fn path_from(path: &Vec<u64>, p: usize) -> Vec<u64> {
    let mut out: Vec<u64> = Vec::new();
    let mut i = p;
    while i < path.len() {
        out.push(path[i]);
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Graph.lean:184-186 namesOf
/// The closure's names.
pub fn names_of(c: &Vec<(NIdx, Vec<ImportRec>)>) -> HashMap2<NIdx, bool> {
    let mut s: HashMap2<NIdx, bool> = HashMap2::new();
    let mut k = 0usize;
    while k < c.len() {
        s.insert(c[k].0.dup2(), true);
        k += 1;
    }
    s
}

/// con-leche: ConLeche/Driver/Graph.lean:188-191 rankLt
/// `a` and `b` are ranks, `a` below `b`.
pub fn rank_lt(a: &Option<u64>, b: &Option<u64>) -> bool {
    match (a, b) {
        (Some(x), Some(y)) => *x < *y,
        _ => false,
    }
}

/// con-leche: ConLeche/Driver/Graph.lean:193-195 edgeOk
/// An import of `m` goes to a module of the closure of a smaller rank.
pub fn edge_ok(pos: &HashMap2<NIdx, bool>, idx: &HashMap2<NIdx, u64>, rank: &Vec<Option<u64>>, m: &NIdx, i: &ImportRec) -> bool {
    pos.contains_key(&i.module) && rank_lt(&rank_of(idx, rank, &i.module), &rank_of(idx, rank, m))
}

/// con-leche: ConLeche/Driver/Graph.lean:197-211 verdict
/// The first import of `m` that is not `edge_ok`.
pub fn bad_edge(pos: &HashMap2<NIdx, bool>, idx: &HashMap2<NIdx, u64>, rank: &Vec<Option<u64>>, m: &NIdx, imps: &Vec<ImportRec>) -> Option<usize> {
    let mut i = 0usize;
    while i < imps.len() {
        if !edge_ok(pos, idx, rank, m, &imps[i]) {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// con-leche: ConLeche/Driver/Graph.lean:197-211 verdict
/// `distinctGo (C.map fun e => rk e.1) {}`: no two modules of the closure have
/// the same rank (the missing rank counting as one value).
pub fn ranks_distinct(c: &Vec<(NIdx, Vec<ImportRec>)>, idx: &HashMap2<NIdx, u64>, rank: &Vec<Option<u64>>) -> bool {
    let mut seen: HashMap2<u64, bool> = HashMap2::new();
    let mut none_seen = false;
    let mut k = 0usize;
    while k < c.len() {
        match rank_of(idx, rank, &c[k].0) {
            None => {
                if none_seen {
                    return false;
                }
                none_seen = true;
            }
            Some(r) => {
                if seen.contains_key(&r) {
                    return false;
                }
                seen.insert(r, true);
            }
        }
        k += 1;
    }
    true
}

/// con-leche: ConLeche/Driver/Graph.lean:197-211 verdict
/// `roots.find? (!pos.contains ·)`, as a position.
pub fn first_missing_root(pos: &HashMap2<NIdx, bool>, roots: &Vec<NIdx>) -> Option<usize> {
    let mut r = 0usize;
    while r < roots.len() {
        if !pos.contains_key(&roots[r]) {
            return Some(r);
        }
        r += 1;
    }
    None
}

/// con-leche: ConLeche/Driver/Graph.lean:197-211 verdict
/// `C.find? (fun e => (rk e.1).isNone)`, as a position.
pub fn first_unranked(c: &Vec<(NIdx, Vec<ImportRec>)>, idx: &HashMap2<NIdx, u64>, rank: &Vec<Option<u64>>) -> Option<usize> {
    let mut k = 0usize;
    while k < c.len() {
        if rank_of(idx, rank, &c[k].0).is_none() {
            return Some(k);
        }
        k += 1;
    }
    None
}

/// con-leche: ConLeche/Driver/Graph.lean:197-211 verdict
/// `C.find? (fun e => !e.2.all (edgeOk pos rk e.1))` and its bad import, as
/// positions.
pub fn first_bad_node(pos: &HashMap2<NIdx, bool>, idx: &HashMap2<NIdx, u64>, rank: &Vec<Option<u64>>, c: &Vec<(NIdx, Vec<ImportRec>)>) -> Option<(usize, usize)> {
    let mut e = 0usize;
    while e < c.len() {
        match bad_edge(pos, idx, rank, &c[e].0, &c[e].1) {
            Some(i) => return Some((e, i)),
            None => {}
        }
        e += 1;
    }
    None
}

/// con-leche: ConLeche/Driver/Graph.lean:197-211 verdict
/// **What the verdict finds wrong**: a root outside the closure, a module of
/// it with no rank, two with one rank, an import edge (its module and its
/// import's) not to a smaller rank.  Deviation: upstream's verdict is the
/// error; here the fault, and its message apart (`fault_error`).
pub enum Fault {
    Root(NIdx),
    Unranked(NIdx),
    Twice,
    Edge(NIdx, Option<NIdx>),
}

/// con-leche: ConLeche/Driver/Graph.lean:197-211 verdict
/// **The verdict on a closure and a numbering**: `None` when every root is in
/// the closure, every module of it has a rank, no two the same, and every import
/// edge goes to a module of the closure of a smaller rank; else the first thing
/// wrong.
pub fn verdict(roots: &Vec<NIdx>, c: &Vec<(NIdx, Vec<ImportRec>)>, idx: &HashMap2<NIdx, u64>, rank: &Vec<Option<u64>>) -> Option<Fault> {
    let pos = names_of(c);
    match first_missing_root(&pos, roots) {
        Some(r) => return Some(Fault::Root(roots[r].dup2())),
        None => {}
    }
    match first_unranked(c, idx, rank) {
        Some(k) => return Some(Fault::Unranked(c[k].0.dup2())),
        None => {}
    }
    if !ranks_distinct(c, idx, rank) {
        return Some(Fault::Twice);
    }
    match first_bad_node(&pos, idx, rank, c) {
        Some((e, i)) => Some(Fault::Edge(c[e].0.dup2(), Some(c[e].1[i].module.dup2()))),
        None => None,
    }
}

/// con-leche: ConLeche/Driver/Graph.lean:197-211 verdict
/// A fault's error, upstream's message.
pub fn fault_error(pers: &PersTier, ar: &EStore, f: &Fault) -> CheckError {
    match f {
        Fault::Root(r) => {
            let t = text::cat({ const M: [u32; 9] = [116, 104, 101, 32, 114, 111, 111, 116, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, r));
            core_types::internal(text::cat(t, &{ const M: [u32; 22] = [32, 105, 115, 32, 110, 111, 116, 32, 105, 110, 32, 116, 104, 101, 32, 99, 108, 111, 115, 117, 114, 101]; crate::kernel::core_types::code_points(&M) }))
        }
        Fault::Unranked(m) => {
            let t = text::cat({ const M: [u32; 11] = [116, 104, 101, 32, 109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, m));
            core_types::internal(text::cat(t, &{ const M: [u32; 27] = [32, 111, 102, 32, 116, 104, 101, 32, 99, 108, 111, 115, 117, 114, 101, 32, 104, 97, 115, 32, 110, 111, 32, 114, 97, 110, 107]; crate::kernel::core_types::code_points(&M) }))
        }
        Fault::Twice => core_types::internal({ const M: [u32; 45] = [116, 119, 111, 32, 109, 111, 100, 117, 108, 101, 115, 32, 111, 102, 32, 116, 104, 101, 32, 99, 108, 111, 115, 117, 114, 101, 32, 104, 97, 118, 101, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 114, 97, 110, 107]; crate::kernel::core_types::code_points(&M) }),
        Fault::Edge(m, i) => {
            let t = text::cat({ const M: [u32; 11] = [116, 104, 101, 32, 105, 109, 112, 111, 114, 116, 32]; crate::kernel::core_types::code_points(&M) }, &view::name_text(pers, ar, m));
            let it = match i {
                Some(i) => view::name_text(pers, ar, i),
                None => { const M: [u32; 11] = [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93]; crate::kernel::core_types::code_points(&M) },
            };
            core_types::invalid(text::cat(text::cat3(t, &{ const M: [u32; 3] = [32, 8594, 32]; crate::kernel::core_types::code_points(&M) }, &it), &{ const M: [u32; 30] = [32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 103, 111, 32, 116, 111, 32, 97, 32, 115, 109, 97, 108, 108, 101, 114, 32, 114, 97, 110, 107]; crate::kernel::core_types::code_points(&M) }))
        }
    }
}

/// con-leche: ConLeche/Driver/Graph.lean:215-218 cycleMsg
/// A cycle's message: its modules in import order, the first repeated at the
/// end.
pub fn cycle_msg(pers: &PersTier, ar: &EStore, c: &Vec<(NIdx, Vec<ImportRec>)>, cyc: &Vec<u64>) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::new();
    let mut i = 0usize;
    while i < cyc.len() + 1 && cyc.len() > 0 {
        let k = if i < cyc.len() { cyc[i] as usize } else { cyc[0] as usize };
        if i > 0 {
            out = text::cat(out, &{ const M: [u32; 3] = [32, 8594, 32]; crate::kernel::core_types::code_points(&M) });
        }
        if k < c.len() {
            out = text::cat(out, &view::name_text(pers, ar, &c[k].0));
        } else {
            out = text::cat(out, &{ const M: [u32; 11] = [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93]; crate::kernel::core_types::code_points(&M) });
        }
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Graph.lean:220-238 graphOf
/// **The roots' closure, its graph checked**: walk the closure's headers,
/// compute an order, validate it; the closure, or the first thing wrong (an
/// import cycle named by its modules).
pub fn graph_of<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp: &files::Roots, roots: &Vec<NIdx>, cmp: &Option<(NIdx, NIdx)>) -> Result<Vec<(NIdx, Vec<ImportRec>)>, CheckError> {
    let (lvl, seen) = dedup(roots);
    let c = match closure_levels(fs, pk, pers, ar, sp, cmp, lvl, seen, Vec::new()) {
        Err(e) => return Err(e),
        Ok(c) => c,
    };
    let idx = index_of(&c);
    let deps = deps_of(&idx, &c);
    let ord = kahn(&deps);
    match cycle_of(&deps, &ord) {
        Some(cyc) => {
            let t = text::cat({ const M: [u32; 14] = [105, 109, 112, 111, 114, 116, 32, 99, 121, 99, 108, 101, 58, 32]; crate::kernel::core_types::code_points(&M) }, &cycle_msg(pers, ar, &c, &cyc));
            return Err(core_types::invalid(t));
        }
        None => {}
    }
    match verdict(roots, &c, &idx, &ranks_of(c.len() as u64, &ord)) {
        Some(f) => Err(fault_error(pers, ar, &f)),
        None => Ok(c),
    }
}

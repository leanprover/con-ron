//! `ConLeche/Frontend/Olean/Sparse.lean` — the sparse decoder (task #142).
//!
//! A constant at a time, each with a memo of its own: from one root, exactly the
//! objects the root leads to, each once, a recursion on the location.  Beside its
//! own memo, a read may be handed **a frontier** (`Frontier`): values of the
//! region's objects read earlier, read-only; an object the frontier holds is
//! taken from it and what lies below it is not visited.  This is how a theorem's
//! value is read when its check needs it (`frontier_expr`, upstream task #481).
//!
//! Deviations: the memo maps locations to handles, and the kid tables are
//! `Vec`s.  A frontier's handles are the load's, persistent, so a read in a
//! worker's scratch tier interns over them.

use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx};
use crate::arena::store::{EStore, PersTier};
use crate::frontend::olean::fast;
use crate::frontend::olean::region;
use crate::frontend::olean::region::Region;
use crate::frontend::olean::spec;
use crate::frontend::olean::spec::{CEntryF, OleanPins, PtrRead, RdErr, Sub};
use crate::ron::hashmap::Dup;
use crate::ron::hashmap2::HashMap2;

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:77-87 kidTable
/// The list of one kid.
pub fn kids1(a: (u64, u8, bool)) -> Vec<(u64, u8, bool)> {
    let mut v: Vec<(u64, u8, bool)> = Vec::with_capacity(1);
    v.push(a);
    v
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:77-87 kidTable
/// The list of two kids.
pub fn kids2(a: (u64, u8, bool), b: (u64, u8, bool)) -> Vec<(u64, u8, bool)> {
    let mut v: Vec<(u64, u8, bool)> = Vec::with_capacity(2);
    v.push(a);
    v.push(b);
    v
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:77-87 kidTable
/// The shape's field count decides.
pub fn kids_if(ok: bool, v: Vec<(u64, u8, bool)>) -> Option<Vec<(u64, u8, bool)>> {
    if ok {
        Some(v)
    } else {
        None
    }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:47-50 nameKids
pub fn name_kids(t: u64, n: u64) -> Option<Vec<(u64, u8, bool)>> {
    if (t == 1 || t == 2) && n == 2 {
        Some(kids1((0, fast::K_NAME, true)))
    } else {
        None
    }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:52-58 levelKids
pub fn level_kids(t: u64, n: u64) -> Option<Vec<(u64, u8, bool)>> {
    match t {
        0 => kids_if(n == 0, Vec::new()),
        1 => kids_if(n == 1, kids1((0, fast::K_LEVEL, true))),
        2 => kids_if(n == 2, kids2((0, fast::K_LEVEL, true), (1, fast::K_LEVEL, true))),
        3 => kids_if(n == 2, kids2((0, fast::K_LEVEL, true), (1, fast::K_LEVEL, true))),
        4 => kids_if(n == 1, kids1((0, fast::K_NAME, true))),
        _ => None,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:60-62 levelsKids
pub fn levels_kids(t: u64, n: u64) -> Option<Vec<(u64, u8, bool)>> {
    if t == 1 && n == 2 {
        Some(kids2((0, fast::K_LEVEL, true), (1, fast::K_LEVELS, true)))
    } else {
        None
    }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:64-75 exprKids
pub fn expr_kids(t: u64, n: u64) -> Option<Vec<(u64, u8, bool)>> {
    match t {
        0 => kids_if(n == 1, Vec::new()),
        3 => kids_if(n == 1, kids1((0, fast::K_LEVEL, true))),
        4 => kids_if(n == 2, kids2((0, fast::K_NAME, true), (1, fast::K_LEVELS, true))),
        5 => kids_if(n == 2, kids2((0, fast::K_EXPR, false), (1, fast::K_EXPR, false))),
        6 => kids_if(n == 3, kids2((1, fast::K_EXPR, false), (2, fast::K_EXPR, false))),
        7 => kids_if(n == 3, kids2((1, fast::K_EXPR, false), (2, fast::K_EXPR, false))),
        8 => {
            let mut v = kids2((1, fast::K_EXPR, false), (2, fast::K_EXPR, false));
            v.push((3, fast::K_EXPR, false));
            kids_if(n == 4, v)
        }
        9 => kids_if(n == 1, Vec::new()),
        10 => kids_if(n == 2, kids1((1, fast::K_EXPR, false))),
        11 => kids_if(n == 3, kids2((0, fast::K_NAME, true), (2, fast::K_EXPR, false))),
        _ => None,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:77-87 kidTable
/// **The objects an object leads to**: the pointer fields its node function
/// follows, or `None` when the node function reads no object of that shape.
pub fn kid_table(k: u8, t: u64, n: u64) -> Option<Vec<(u64, u8, bool)>> {
    if k == fast::K_NAME {
        name_kids(t, n)
    } else if k == fast::K_LEVEL {
        level_kids(t, n)
    } else if k == fast::K_LEVELS {
        levels_kids(t, n)
    } else {
        expr_kids(t, n)
    }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:92-98 SM
/// A sparse decoder's memo: the values read so far, by location, one map per kind.
pub struct SM {
    pub names: HashMap2<u64, NIdx>,
    pub levels: HashMap2<u64, LIdx>,
    pub lists: HashMap2<u64, LsIdx>,
    pub exprs: HashMap2<u64, EIdx>,
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:92-98 SM
/// The empty memo (the structure's defaults).
pub fn sm_empty() -> SM {
    SM { names: HashMap2::new(), levels: HashMap2::new(), lists: HashMap2::new(), exprs: HashMap2::new() }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:100-105 SM.has
/// Does the memo hold the object at `g` as kind `k`.
pub fn sm_has(st: &SM, k: u8, g: u64) -> bool {
    if k == fast::K_NAME {
        st.names.contains_key(&g)
    } else if k == fast::K_LEVEL {
        st.levels.contains_key(&g)
    } else if k == fast::K_LEVELS {
        st.lists.contains_key(&g)
    } else {
        st.exprs.contains_key(&g)
    }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:109-113 Table
/// A read-only table by location: `keys` ascending, `vals[i]` the value at
/// `keys[i]`.
pub struct Table<T> {
    pub keys: Vec<u64>,
    pub vals: Vec<T>,
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:109-113 Table
/// The empty table (the structure's defaults).
pub fn table_empty<T>() -> Table<T> {
    Table { keys: Vec::new(), vals: Vec::new() }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:115-127 Table.search
/// The binary search of `Table.get`, between `lo` and `hi`: the position of
/// `c`'s value.  A loop (this directory's exemption): the Lean's tail recursion.
pub fn table_search<T>(t: &Table<T>, c: u64, lo: usize, hi: usize) -> Option<usize> {
    let mut lo = lo;
    let mut hi = hi;
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if mid >= t.keys.len() {
            return None;
        }
        let k = t.keys[mid];
        if k == c {
            if mid < t.vals.len() {
                return Some(mid);
            } else {
                return None;
            }
        } else if k < c {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    None
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:129-130 Table.get
/// The value at location `c`.
pub fn table_get<T: Dup>(t: &Table<T>, c: u64) -> Option<T> {
    match table_search(t, c, 0, t.keys.len()) {
        Some(i) => Some(t.vals[i].dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:132-138 Frontier
/// **Values read earlier, by kind and location**, read-only: which objects it
/// holds is a matter of speed alone.  Its handles are the load's, persistent.
pub struct Frontier {
    pub names: Table<NIdx>,
    pub levels: Table<LIdx>,
    pub lists: Table<LsIdx>,
    pub exprs: Table<EIdx>,
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:132-138 Frontier
/// The empty frontier (the structure's defaults, `Inhabited`).
pub fn frontier_empty() -> Frontier {
    Frontier { names: table_empty(), levels: table_empty(), lists: table_empty(), exprs: table_empty() }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:142-147 Frontier.has
/// Does the frontier hold the object at `g` as kind `k`.
pub fn frontier_has(b: &Frontier, k: u8, g: u64) -> bool {
    if k == fast::K_NAME {
        table_search(&b.names, g, 0, b.names.keys.len()).is_some()
    } else if k == fast::K_LEVEL {
        table_search(&b.levels, g, 0, b.levels.keys.len()).is_some()
    } else if k == fast::K_LEVELS {
        table_search(&b.lists, g, 0, b.lists.keys.len()).is_some()
    } else {
        table_search(&b.exprs, g, 0, b.exprs.keys.len()).is_some()
    }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:149-151 SM.holds
/// Does the read hold the object at `g` as kind `k`: its memo or the frontier.
#[inline(always)]
pub fn sm_holds(st: &SM, b: &Frontier, k: u8, g: u64) -> bool {
    sm_has(st, k, g) || frontier_has(b, k, g)
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:153-157 lookup
/// The value of a kid: the memo's, or the frontier's.
#[inline(always)]
pub fn lookup<T: Dup>(m: &HashMap2<u64, T>, t: &Table<T>, c: u64) -> Option<T> {
    match m.get(&c) {
        Some(v) => Some(v.dup2()),
        None => table_get(t, c),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:159-177 SM.buildIn
/// The memo over a frontier, as the node functions' `sub` (`lookup` per kind).
pub struct SMIn<'a> {
    pub st: &'a SM,
    pub b: &'a Frontier,
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:159-177 SM.buildIn
impl<'a> Sub for SMIn<'a> {
    /// con-leche: ConLeche/Frontend/Olean/Sparse.lean:153-157 lookup
    fn sub_name(&self, c: u64) -> Option<NIdx> {
        lookup(&self.st.names, &self.b.names, c)
    }

    /// con-leche: ConLeche/Frontend/Olean/Sparse.lean:153-157 lookup
    fn sub_level(&self, c: u64) -> Option<LIdx> {
        lookup(&self.st.levels, &self.b.levels, c)
    }

    /// con-leche: ConLeche/Frontend/Olean/Sparse.lean:153-157 lookup
    fn sub_levels(&self, c: u64) -> Option<LsIdx> {
        lookup(&self.st.lists, &self.b.lists, c)
    }

    /// con-leche: ConLeche/Frontend/Olean/Sparse.lean:153-157 lookup
    fn sub_expr(&self, c: u64) -> Option<EIdx> {
        lookup(&self.st.exprs, &self.b.exprs, c)
    }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:159-177 SM.buildIn
/// **The object at `g`, read as kind `k`**, by the specification's node function,
/// its kids' values from the memo or the frontier, and added to the memo.
pub fn sm_build_in(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, b: &Frontier, k: u8, g: u64, st: &mut SM) -> Result<(), RdErr> {
    if k == fast::K_NAME {
        match spec::name_node(pk, pers, ar, bs, r, g, &SMIn { st: &*st, b }) {
            Err(e) => Err(e),
            Ok(v) => {
                st.names.insert(g, v);
                Ok(())
            }
        }
    } else if k == fast::K_LEVEL {
        match spec::level_node(pk, pers, ar, bs, r, g, &SMIn { st: &*st, b }) {
            Err(e) => Err(e),
            Ok(v) => {
                st.levels.insert(g, v);
                Ok(())
            }
        }
    } else if k == fast::K_LEVELS {
        match spec::levels_node(pk, pers, ar, bs, r, g, &SMIn { st: &*st, b }) {
            Err(e) => Err(e),
            Ok(v) => {
                st.lists.insert(g, v);
                Ok(())
            }
        }
    } else {
        match spec::expr_node(pk, pers, ar, bs, r, g, &SMIn { st: &*st, b }) {
            Err(e) => Err(e),
            Ok(v) => {
                st.exprs.insert(g, v);
                Ok(())
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:184-197 sGo
/// **The object at `g` read as kind `k`, into the memo**: nothing to do if the
/// memo or the frontier holds it; else its kids, then the object itself.
pub fn s_go(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, b: &Frontier, k: u8, g: u64, st: &mut SM) -> Result<(), RdErr> {
    if sm_holds(st, b, k, g) {
        return Ok(());
    }
    if !region::region_fits(bs, r, g) {
        return Err(RdErr::Bad);
    }
    match kid_table(k, region::region_tag(bs, g), region::region_nobjs(bs, g)) {
        None => Err(RdErr::Bad),
        Some(fs) => match kids_go(pk, pers, ar, bs, r, b, g, &fs, 0, st) {
            Err(e) => Err(e),
            Ok(()) => sm_build_in(pk, pers, ar, bs, r, b, k, g, st),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:199-214 kidsGo
/// The kids the fields `fs` from position `i` of the object at `g` lead to, into
/// the memo.
pub fn kids_go(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, b: &Frontier, g: u64, fs: &Vec<(u64, u8, bool)>, i: usize, st: &mut SM) -> Result<(), RdErr> {
    if i >= fs.len() {
        return Ok(());
    }
    let v = region::region_fld(bs, g, fs[i].0);
    if fs[i].2 && v == 1 {
        kids_go(pk, pers, ar, bs, r, b, g, fs, i + 1, st)
    } else {
        match region::region_down(r, g, v) {
            None => Err(RdErr::Bad),
            Some(c) => match s_go(pk, pers, ar, bs, r, b, fs[i].1, c, st) {
                Err(e) => Err(e),
                Ok(()) => kids_go(pk, pers, ar, bs, r, b, g, fs, i + 1, st),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:219-221 frontierExpr
/// **The `Expr` at location `c`**, read with a memo of its own over a frontier.
pub fn frontier_expr(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, b: &Frontier, c: u64) -> Result<EIdx, RdErr> {
    let mut st: SM = sm_empty();
    match s_go(pk, pers, ar, bs, r, b, fast::K_EXPR, c, &mut st) {
        Err(e) => Err(e),
        Ok(()) => match lookup(&st.exprs, &b.exprs, c) {
            Some(h) => Ok(h),
            None => Err(RdErr::Bad),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:223-228 sparseNameP
/// **The `Name` a pointer stands for**, read sparsely.
pub fn sparse_name_p(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, v: u64) -> Result<NIdx, RdErr> {
    if v == 1 {
        return Ok(pk.anon.dup2());
    }
    match region::region_loc(r, v) {
        None => Err(RdErr::Bad),
        Some(c) => {
            let b: Frontier = frontier_empty();
            let mut st: SM = sm_empty();
            match s_go(pk, pers, ar, bs, r, &b, fast::K_NAME, c, &mut st) {
                Err(e) => Err(e),
                Ok(()) => match lookup(&st.names, &b.names, c) {
                    Some(h) => Ok(h),
                    None => Err(RdErr::Bad),
                },
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:230-234 sparseExprP
/// **The `Expr` a pointer stands for**, read sparsely.
pub fn sparse_expr_p(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, v: u64) -> Result<EIdx, RdErr> {
    match region::region_loc(r, v) {
        None => Err(RdErr::Bad),
        Some(c) => frontier_expr(pk, pers, ar, bs, r, &frontier_empty(), c),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:236-239 sparseEntry
/// The two reads of `sparseEntry`, as a pointer read.
pub struct SparseRead;

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:236-239 sparseEntry
impl PtrRead for SparseRead {
    /// con-leche: ConLeche/Frontend/Olean/Sparse.lean:236-239 sparseEntry
    fn rd_name(&self, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, v: u64) -> Result<NIdx, RdErr> {
        sparse_name_p(pk, pers, ar, bs, r, v)
    }

    /// con-leche: ConLeche/Frontend/Olean/Sparse.lean:236-239 sparseEntry
    fn rd_expr(&self, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, v: u64) -> Result<EIdx, RdErr> {
        sparse_expr_p(pk, pers, ar, bs, r, v)
    }
}

/// con-leche: ConLeche/Frontend/Olean/Sparse.lean:236-239 sparseEntry
/// **A constant's names and expressions, read sparsely**: each root with a memo
/// of its own.
pub fn sparse_entry(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, sk: &CEntryF<u64, u64>) -> Result<CEntryF<NIdx, EIdx>, RdErr> {
    spec::c_entry_map(&SparseRead, pk, pers, ar, bs, r, sk)
}

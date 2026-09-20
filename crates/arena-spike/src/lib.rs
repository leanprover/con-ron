//! The P2s spike's Rust side (DESIGN.md §8.6, experiments C and D).
//!
//! A throw-away transliteration of `proof/ConRon/Arena/Spike/Mini.lean`: a
//! three-constructor arena (`bvar`, `app`, `lam`) with `u32` handles, a
//! per-constructor `Vec`, hash-consing by linear scan (the spike's stand-in
//! for the cons table — the same *function*, an association from node to
//! handle, with the lookup cost irrelevant to a proof), a `Vec` memo, and
//! `instantiate1` over it.
//!
//! Written to DESIGN.md §3.4's rules: no closures, no `?`, no loops (index
//! carrying recursion instead), no `derive(Debug)`, checked arithmetic,
//! explicit fuel.

/// con-leche: none — the handle's constructor tag (the high 4 bits of the
/// word; DESIGN §8.3).
pub const TAG_BVAR: u32 = 0;
/// con-leche: none — see `TAG_BVAR`.
pub const TAG_APP: u32 = 1;
/// con-leche: none — see `TAG_BVAR`.
pub const TAG_LAM: u32 = 2;
/// con-leche: none — `2^28`, the per-constructor index capacity of the spike's
/// one-tier handle (the real arena's is `2^27` per constructor per tier).
pub const IDX_CAP: u32 = 268435456;

/// con-leche: none — assemble a handle.  Arithmetic, not shifts: the
/// roundtrip lemmas are then `omega` (task #97a's decision, DESIGN §8.3).
pub fn mk(tag: u32, idx: u32) -> u32 {
    tag * IDX_CAP + idx
}

/// con-leche: none — the handle's tag.
pub fn tag_of(h: u32) -> u32 {
    h / IDX_CAP
}

/// con-leche: none — the handle's index into its constructor's array.
pub fn idx_of(h: u32) -> u32 {
    h % IDX_CAP
}

/// con-leche: ConLeche/Kernel/Expr.lean:344 Expr.app — an application node.
pub struct AppNode {
    pub f: u32,
    pub a: u32,
}

/// con-leche: ConLeche/Kernel/Expr.lean:344 Expr.lam — a λ node.  The spike
/// drops the binder metadata: it is carried unchanged by `instantiate1` and
/// adds nothing to the experiment.
pub struct LamNode {
    pub ty: u32,
    pub body: u32,
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:62 Inst1MemoInv — one memo entry:
/// the node, the cursor, the answer.
pub struct MemoEntry {
    pub key_h: u32,
    pub key_d: u32,
    pub val: u32,
}

/// con-leche: ConLeche/Cached/CoreC.lean:120 CState — the whole state: the
/// three per-constructor arrays and the `instantiate1` memo.
pub struct State {
    pub bvars: Vec<u32>,
    pub apps: Vec<AppNode>,
    pub lams: Vec<LamNode>,
    pub memo: Vec<MemoEntry>,
}

impl State {
    /// con-leche: none — the empty arena.
    pub fn new() -> State {
        State {
            bvars: Vec::new(),
            apps: Vec::new(),
            lams: Vec::new(),
            memo: Vec::new(),
        }
    }
}

impl Default for State {
    fn default() -> State {
        State::new()
    }
}

/// con-leche: none — is `h` a decodable `bvar` handle?  The three `view_*`
/// functions together are `EStore.view` of the frozen store API.
pub fn view_bvar(st: &State, h: u32) -> Option<u32> {
    if tag_of(h) == TAG_BVAR {
        let i = idx_of(h) as usize;
        if i < st.bvars.len() {
            Some(st.bvars[i])
        } else {
            None
        }
    } else {
        None
    }
}

/// con-leche: none — decode an `app` handle into its two children.
pub fn view_app(st: &State, h: u32) -> Option<(u32, u32)> {
    if tag_of(h) == TAG_APP {
        let i = idx_of(h) as usize;
        if i < st.apps.len() {
            Some((st.apps[i].f, st.apps[i].a))
        } else {
            None
        }
    } else {
        None
    }
}

/// con-leche: none — decode a `lam` handle into its two children.
pub fn view_lam(st: &State, h: u32) -> Option<(u32, u32)> {
    if tag_of(h) == TAG_LAM {
        let i = idx_of(h) as usize;
        if i < st.lams.len() {
            Some((st.lams[i].ty, st.lams[i].body))
        } else {
            None
        }
    } else {
        None
    }
}

/// con-leche: none — the cons-table probe for `bvar`, as an index-carrying
/// recursion (DESIGN §3.4: no loops).
pub fn find_bvar_from(st: &State, k: u32, i: usize) -> Option<u32> {
    if i < st.bvars.len() {
        if st.bvars[i] == k {
            Some(mk(TAG_BVAR, i as u32))
        } else {
            find_bvar_from(st, k, i + 1)
        }
    } else {
        None
    }
}

/// con-leche: none — see `find_bvar_from`.
pub fn find_bvar(st: &State, k: u32) -> Option<u32> {
    find_bvar_from(st, k, 0)
}

/// con-leche: none — the cons-table probe for `app`.
pub fn find_app_from(st: &State, f: u32, a: u32, i: usize) -> Option<u32> {
    if i < st.apps.len() {
        if st.apps[i].f == f && st.apps[i].a == a {
            Some(mk(TAG_APP, i as u32))
        } else {
            find_app_from(st, f, a, i + 1)
        }
    } else {
        None
    }
}

/// con-leche: none — see `find_app_from`.
pub fn find_app(st: &State, f: u32, a: u32) -> Option<u32> {
    find_app_from(st, f, a, 0)
}

/// con-leche: none — the cons-table probe for `lam`.
pub fn find_lam_from(st: &State, ty: u32, body: u32, i: usize) -> Option<u32> {
    if i < st.lams.len() {
        if st.lams[i].ty == ty && st.lams[i].body == body {
            Some(mk(TAG_LAM, i as u32))
        } else {
            find_lam_from(st, ty, body, i + 1)
        }
    } else {
        None
    }
}

/// con-leche: none — see `find_lam_from`.
pub fn find_lam(st: &State, ty: u32, body: u32) -> Option<u32> {
    find_lam_from(st, ty, body, 0)
}

/// con-leche: Setlec/Kernel/IExpr.lean:464 intern — hash-cons a `bvar`.
/// `None` is the arena's `Native` verdict at the capacity limit.
pub fn intern_bvar(st: &mut State, k: u32) -> Option<u32> {
    match find_bvar(st, k) {
        Some(h) => Some(h),
        None => {
            let n = st.bvars.len();
            if (n as u32) < IDX_CAP {
                st.bvars.push(k);
                Some(mk(TAG_BVAR, n as u32))
            } else {
                None
            }
        }
    }
}

/// con-leche: Setlec/Kernel/IExpr.lean:464 intern — hash-cons an `app`.
pub fn intern_app(st: &mut State, f: u32, a: u32) -> Option<u32> {
    match find_app(st, f, a) {
        Some(h) => Some(h),
        None => {
            let n = st.apps.len();
            if (n as u32) < IDX_CAP {
                st.apps.push(AppNode { f, a });
                Some(mk(TAG_APP, n as u32))
            } else {
                None
            }
        }
    }
}

/// con-leche: Setlec/Kernel/IExpr.lean:464 intern — hash-cons a `lam`.
pub fn intern_lam(st: &mut State, ty: u32, body: u32) -> Option<u32> {
    match find_lam(st, ty, body) {
        Some(h) => Some(h),
        None => {
            let n = st.lams.len();
            if (n as u32) < IDX_CAP {
                st.lams.push(LamNode { ty, body });
                Some(mk(TAG_LAM, n as u32))
            } else {
                None
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:81 instantiate1Go — the memo
/// probe, as an index-carrying recursion.
pub fn memo_get_from(st: &State, h: u32, d: u32, i: usize) -> Option<u32> {
    if i < st.memo.len() {
        if st.memo[i].key_h == h && st.memo[i].key_d == d {
            Some(st.memo[i].val)
        } else {
            memo_get_from(st, h, d, i + 1)
        }
    } else {
        None
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:81 instantiate1Go — see
/// `memo_get_from`.
pub fn memo_get(st: &State, h: u32, d: u32) -> Option<u32> {
    memo_get_from(st, h, d, 0)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:116 instantiate1Go — record an
/// answer.
pub fn memo_set(st: &mut State, h: u32, d: u32, r: u32) {
    st.memo.push(MemoEntry {
        key_h: h,
        key_d: d,
        val: r,
    });
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:33 instantiate1, `:81`
/// instantiate1Go — **the subject**: replace `bvar d` by `v` in the term `h`
/// denotes, over handles, memoized.  `None` is a failure (a dangling handle,
/// exhausted fuel, or a full arena) and the refinement claims nothing there.
pub fn instantiate1(st: &mut State, v: u32, fuel: u32, h: u32, d: u32) -> Option<u32> {
    if fuel == 0 {
        return None;
    }
    let tag = tag_of(h);
    if tag == TAG_BVAR {
        match view_bvar(st, h) {
            Some(i) => {
                if i == d {
                    Some(v)
                } else if i > d {
                    intern_bvar(st, i - 1)
                } else {
                    Some(h)
                }
            }
            None => None,
        }
    } else if tag == TAG_APP {
        match view_app(st, h) {
            Some(fa) => match memo_get(st, h, d) {
                Some(r) => Some(r),
                None => match instantiate1(st, v, fuel - 1, fa.0, d) {
                    Some(f2) => match instantiate1(st, v, fuel - 1, fa.1, d) {
                        Some(a2) => match intern_app(st, f2, a2) {
                            Some(r) => {
                                memo_set(st, h, d, r);
                                Some(r)
                            }
                            None => None,
                        },
                        None => None,
                    },
                    None => None,
                },
            },
            None => None,
        }
    } else if tag == TAG_LAM {
        match view_lam(st, h) {
            Some(tb) => match memo_get(st, h, d) {
                Some(r) => Some(r),
                None => match instantiate1(st, v, fuel - 1, tb.0, d) {
                    Some(t2) => match instantiate1(st, v, fuel - 1, tb.1, d + 1) {
                        Some(b2) => match intern_lam(st, t2, b2) {
                            Some(r) => {
                                memo_set(st, h, d, r);
                                Some(r)
                            }
                            None => None,
                        },
                        None => None,
                    },
                    None => None,
                },
            },
            None => None,
        }
    } else {
        None
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:120 instantiate1 — the top-level
/// call: the memo is dropped before and after, because it depends on `v`.
pub fn instantiate1_top(st: &mut State, v: u32, fuel: u32, h: u32) -> Option<u32> {
    st.memo = Vec::new();
    let r = instantiate1(st, v, fuel, h, 0);
    st.memo = Vec::new();
    r
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn beta_on_identity() {
        // (λ. bvar 0) applied: instantiate1 of the body at cursor 0 with v.
        let mut st = State::new();
        let b0 = intern_bvar(&mut st, 0).unwrap();
        let b1 = intern_bvar(&mut st, 1).unwrap();
        let body = intern_app(&mut st, b0, b1).unwrap();
        let v = intern_bvar(&mut st, 7).unwrap();
        let r = instantiate1_top(&mut st, v, 100, body).unwrap();
        // bvar 0 ↦ v, bvar 1 ↦ bvar 0
        let expect = intern_app(&mut st, v, b0).unwrap();
        assert_eq!(r, expect);
    }

    #[test]
    fn under_a_binder_the_cursor_moves() {
        let mut st = State::new();
        let b1 = intern_bvar(&mut st, 1).unwrap();
        let b0 = intern_bvar(&mut st, 0).unwrap();
        let lam = intern_lam(&mut st, b0, b1).unwrap();
        let v = intern_bvar(&mut st, 9).unwrap();
        let r = instantiate1_top(&mut st, v, 100, lam).unwrap();
        // λ (bvar 0 ↦ v) . (bvar 1 ↦ v at cursor 1)
        let expect = intern_lam(&mut st, v, v).unwrap();
        assert_eq!(r, expect);
    }

    #[test]
    fn sharing_is_preserved_by_the_memo() {
        let mut st = State::new();
        let b0 = intern_bvar(&mut st, 0).unwrap();
        let inner = intern_app(&mut st, b0, b0).unwrap();
        let outer = intern_app(&mut st, inner, inner).unwrap();
        let v = intern_bvar(&mut st, 3).unwrap();
        let r = instantiate1_top(&mut st, v, 100, outer).unwrap();
        let vi = intern_app(&mut st, v, v).unwrap();
        let expect = intern_app(&mut st, vi, vi).unwrap();
        assert_eq!(r, expect);
    }

    #[test]
    fn fuel_exhaustion_is_a_failure() {
        let mut st = State::new();
        let b0 = intern_bvar(&mut st, 0).unwrap();
        let ap = intern_app(&mut st, b0, b0).unwrap();
        assert_eq!(instantiate1_top(&mut st, b0, 1, ap), None);
    }
}

//! `ConLeche/Frontend/Olean/Spec.lean` — what the reader computes from a
//! module's bytes (task #142).
//!
//! Upstream's file is the SPECIFICATION: a value read field by field, by
//! recursion on the location, no memo.  **Everything there that reads a `Level`
//! or an `Expr` is `noncomputable`** (exponential in the sharing), so it is not
//! ported (`scripts/provenance-skip.txt`); Theorem 1 cites it.  What is ported
//! is what executes: the node functions, the skeletons, the name reads and the
//! name-table check.
//!
//! ## Deviations
//!
//! * **Terms go straight into the store, as the stream parser's do.**  A node
//!   function INTERNS (it is the parse's `parse_expr_rec_d`, reading a region
//!   instead of a record), so a value is a handle.  [`RdErr`] holds the two ways
//!   that can fail: upstream's `none` (`Bad`), and the store's own `Native`
//!   decline at its capacity (`Err`), which the Lean has no room for.
//! * **`sub : (c : Nat) → c < g → Option α` is the trait [`Sub`]**, with one
//!   instance per memo (`fast::DS`, `sparse::SM`): the subset has no closure.
//!   `nameAt` ties the knot with itself, so it spells the `Name` node out.
//! * **`CEntryF.mapM` is the trait [`PtrRead`]**, for the same reason.
//! * **What is known in advance is [`OleanPins`]**: the handles of the three
//!   nullary constructors and of the names the reader spells (`mkN`).
//! * **A `Nat` in a skeleton is a saturating word** (`region::nat_saturate`):
//!   [`skel_fits`] turns `u64::MAX` into the `Native` decline right after the
//!   skeleton is read, and [`nat_word`] does the same in a node.
//! * **`Std.HashSet Name` is keyed by handle.**  A name is hash-consed in the
//!   store, so the handle is the name.

use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx};
use crate::arena::store::{ENodeView, EStore, LNodeView, NNodeView, PersTier};
use crate::frontend::olean::region;
use crate::frontend::olean::region::Region;
use crate::frontend::scan_types::HintsRec;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::kernel::expr;
use crate::kernel::expr::Literal;
use crate::ron::hashmap::Dup;
use crate::ron::hashmap::Eq2;
use crate::ron::hashmap2::HashMap2;

/// con-leche: none — `Option`'s `none`, and the store's capacity decline, which
/// the Lean does not have (module note).
pub enum RdErr {
    Bad,
    Err(CheckError),
}

/// con-leche: none — the handles the reader needs in advance (module note).
pub struct OleanPins {
    pub anon: NIdx,
    pub zero: LIdx,
    pub nil: LsIdx,
    /// `mkN ["Nat"]`
    pub n_nat: NIdx,
    /// `mkN ["Char", "ofNat"]`
    pub n_char_of_nat: NIdx,
    /// `mkN ["String", "ofList"]`
    pub n_string_of_list: NIdx,
    /// `mkN ["Eq"]`
    pub n_eq: NIdx,
    /// `mkN ["Quot"]`
    pub n_quot: NIdx,
    /// `mkN ["Quot", "mk"]`
    pub n_quot_mk: NIdx,
    /// `mkN ["Quot", "lift"]`
    pub n_quot_lift: NIdx,
    /// `mkN ["Quot", "ind"]`
    pub n_quot_ind: NIdx,
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:22-23 mkN
/// One name, from a parent and a component (`mkN`'s step).
pub fn mk_n_step(pers: &PersTier, ar: &mut EStore, p: NIdx, s: Vec<u32>) -> Result<NIdx, CheckError> {
    ar.intern_name(pers, NNodeView::Str(p, s))
}

/// con-leche: ConLeche/Frontend/Olean/Closure.lean:22-23 mkN
/// con-leche: ConLeche/Frontend/Olean/Emit.lean:278-280 quotNames
/// The reader's known handles, interned once, before any file is read.
pub fn olean_pins(pers: &PersTier, ar: &mut EStore) -> Result<OleanPins, CheckError> {
    let anon = match ar.intern_name(pers, NNodeView::Anonymous) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    let zero = match ar.intern_level(pers, LNodeView::Zero) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    let nil = match ar.intern_levels(pers, Vec::new()) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    let n_nat = match mk_n_step(pers, ar, anon.dup2(), { const M: [u32; 3] = [78, 97, 116]; crate::kernel::core_types::code_points(&M) }) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    let n_char = match mk_n_step(pers, ar, anon.dup2(), { const M: [u32; 4] = [67, 104, 97, 114]; crate::kernel::core_types::code_points(&M) }) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    let n_char_of_nat = match mk_n_step(pers, ar, n_char, { const M: [u32; 5] = [111, 102, 78, 97, 116]; crate::kernel::core_types::code_points(&M) }) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    let n_string = match mk_n_step(pers, ar, anon.dup2(), { const M: [u32; 6] = [83, 116, 114, 105, 110, 103]; crate::kernel::core_types::code_points(&M) }) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    let n_string_of_list = match mk_n_step(pers, ar, n_string, { const M: [u32; 6] = [111, 102, 76, 105, 115, 116]; crate::kernel::core_types::code_points(&M) }) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    let n_eq = match mk_n_step(pers, ar, anon.dup2(), { const M: [u32; 2] = [69, 113]; crate::kernel::core_types::code_points(&M) }) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    let n_quot = match mk_n_step(pers, ar, anon.dup2(), { const M: [u32; 4] = [81, 117, 111, 116]; crate::kernel::core_types::code_points(&M) }) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    let n_quot_mk = match mk_n_step(pers, ar, n_quot.dup2(), { const M: [u32; 2] = [109, 107]; crate::kernel::core_types::code_points(&M) }) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    let n_quot_lift = match mk_n_step(pers, ar, n_quot.dup2(), { const M: [u32; 4] = [108, 105, 102, 116]; crate::kernel::core_types::code_points(&M) }) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    let n_quot_ind = match mk_n_step(pers, ar, n_quot.dup2(), { const M: [u32; 3] = [105, 110, 100]; crate::kernel::core_types::code_points(&M) }) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    Ok(OleanPins {
        anon,
        zero,
        nil,
        n_nat,
        n_char_of_nat,
        n_string_of_list,
        n_eq,
        n_quot,
        n_quot_mk,
        n_quot_lift,
        n_quot_ind,
    })
}

/// con-leche: none — a `Nat` that became a word (`region::nat_saturate`), checked
/// where a term is built from it: `u64::MAX` is the `Native` decline.
#[inline(always)]
pub fn nat_word(k: u64) -> Result<u64, RdErr> {
    if k == u64::MAX {
        Err(RdErr::Err(core_types::native({ const M: [u32; 54] = [97, 32, 110, 117, 109, 98, 101, 114, 32, 105, 110, 32, 97, 110, 32, 46, 111, 108, 101, 97, 110, 32, 102, 105, 108, 101, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 102, 105, 116, 32, 97, 32, 109, 97, 99, 104, 105, 110, 101, 32, 119, 111, 114, 100]; crate::kernel::core_types::code_points(&M) })))
    } else {
        Ok(k)
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:111-125 nameNode
/// con-leche: ConLeche/Frontend/Olean/Spec.lean:127-148 levelNode
/// con-leche: ConLeche/Frontend/Olean/Spec.lean:150-160 levelsNode
/// con-leche: ConLeche/Frontend/Olean/Spec.lean:162-206 exprNode
/// **The `sub` arguments of the node functions**: a value of a recursive type at
/// a location below the object being read (`fast::DS`'s memo, `sparse::SM`'s).
pub trait Sub {
    /// con-leche: ConLeche/Frontend/Olean/Spec.lean:111-125 nameNode
    fn sub_name(&self, c: u64) -> Option<NIdx>;
    /// con-leche: ConLeche/Frontend/Olean/Spec.lean:127-148 levelNode
    fn sub_level(&self, c: u64) -> Option<LIdx>;
    /// con-leche: ConLeche/Frontend/Olean/Spec.lean:150-160 levelsNode
    fn sub_levels(&self, c: u64) -> Option<LsIdx>;
    /// con-leche: ConLeche/Frontend/Olean/Spec.lean:162-206 exprNode
    fn sub_expr(&self, c: u64) -> Option<EIdx>;
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:73-78 Region.nameIn
/// A `Name` pointer the object at `g` holds, read through `sub`.
#[inline(always)]
pub fn name_in<S: Sub>(pk: &OleanPins, r: &Region, g: u64, v: u64, sub: &S) -> Result<NIdx, RdErr> {
    if v == 1 {
        Ok(pk.anon.dup2())
    } else {
        match region::region_down(r, g, v) {
            Some(c) => match sub.sub_name(c) {
                Some(h) => Ok(h),
                None => Err(RdErr::Bad),
            },
            None => Err(RdErr::Bad),
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:80-85 Region.levelIn
/// A `Level` pointer the object at `g` holds, read through `sub`.
#[inline(always)]
pub fn level_in<S: Sub>(pk: &OleanPins, r: &Region, g: u64, v: u64, sub: &S) -> Result<LIdx, RdErr> {
    if v == 1 {
        Ok(pk.zero.dup2())
    } else {
        match region::region_down(r, g, v) {
            Some(c) => match sub.sub_level(c) {
                Some(h) => Ok(h),
                None => Err(RdErr::Bad),
            },
            None => Err(RdErr::Bad),
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:87-92 Region.levelsIn
/// A `List Level` pointer the object at `g` holds, read through `sub`.
#[inline(always)]
pub fn levels_in<S: Sub>(pk: &OleanPins, r: &Region, g: u64, v: u64, sub: &S) -> Result<LsIdx, RdErr> {
    if v == 1 {
        Ok(pk.nil.dup2())
    } else {
        match region::region_down(r, g, v) {
            Some(c) => match sub.sub_levels(c) {
                Some(h) => Ok(h),
                None => Err(RdErr::Bad),
            },
            None => Err(RdErr::Bad),
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:94-98 Region.exprIn
/// An `Expr` pointer the object at `g` holds, read through `sub`.
#[inline(always)]
pub fn expr_in<S: Sub>(r: &Region, g: u64, v: u64, sub: &S) -> Result<EIdx, RdErr> {
    match region::region_down(r, g, v) {
        Some(c) => match sub.sub_expr(c) {
            Some(h) => Ok(h),
            None => Err(RdErr::Bad),
        },
        None => Err(RdErr::Bad),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:100-107 Region.litP
/// **A `Literal`** the object at `g` holds.
pub fn lit_p(bs: &[u8], r: &Region, g: u64, v: u64) -> Option<Literal> {
    match region::region_down(r, g, v) {
        Some(c) => {
            if region::region_is_ctor(bs, r, c, 0, 1) {
                match region::region_nat_p(bs, r, c, region::region_fld(bs, c, 0)) {
                    Some(n) => Some(expr::literal_nat(n)),
                    None => None,
                }
            } else if region::region_is_ctor(bs, r, c, 1, 1) {
                match region::region_str_p(bs, r, c, region::region_fld(bs, c, 0)) {
                    Some(s) => Some(expr::literal_str(s)),
                    None => None,
                }
            } else {
                None
            }
        }
        None => None,
    }
}

/// con-leche: none — `intern`'s failure, in the reader's channel
#[inline(always)]
pub fn rd_of<T>(x: Result<T, CheckError>) -> Result<T, RdErr> {
    match x {
        Ok(h) => Ok(h),
        Err(e) => Err(RdErr::Err(e)),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:111-125 nameNode
/// `| 1, 2 | 2, 2`: the shapes of a `Name` object.
#[inline(always)]
pub fn name_shape(t: u64, n: u64) -> bool {
    (t == 1 || t == 2) && n == 2
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:111-125 nameNode
/// **A `Name` object** at `g`, interned.
pub fn name_node<S: Sub>(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, g: u64, sub: &S) -> Result<NIdx, RdErr> {
    if !region::region_fits(bs, r, g) {
        return Err(RdErr::Bad);
    }
    let t = region::region_tag(bs, g);
    if name_shape(t, region::region_nobjs(bs, g)) {
        let p = match name_in(pk, r, g, region::region_fld(bs, g, 0), sub) {
            Err(e) => return Err(e),
            Ok(p) => p,
        };
        name_tail(pers, ar, bs, r, g, t, p)
    } else {
        Err(RdErr::Bad)
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:111-125 nameNode
/// The two arms of a `Name` node after its parent: the component, and the intern.
pub fn name_tail(pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, g: u64, t: u64, p: NIdx) -> Result<NIdx, RdErr> {
    if t == 1 {
        match region::region_str_p(bs, r, g, region::region_fld(bs, g, 1)) {
            None => Err(RdErr::Bad),
            Some(s) => rd_of(ar.intern_name(pers, NNodeView::Str(p, s))),
        }
    } else {
        match region::region_nat_sat(bs, r, g, region::region_fld(bs, g, 1)) {
            None => Err(RdErr::Bad),
            Some(i) => match nat_word(i) {
                Err(e) => Err(e),
                Ok(i) => rd_of(ar.intern_name(pers, NNodeView::Num(p, i))),
            },
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:127-148 levelNode
/// **A `Level` object** at `g`, interned (`mvar` is malformed input).
pub fn level_node<S: Sub>(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, g: u64, sub: &S) -> Result<LIdx, RdErr> {
    if !region::region_fits(bs, r, g) {
        return Err(RdErr::Bad);
    }
    let n = region::region_nobjs(bs, g);
    match region::region_tag(bs, g) {
        0 => {
            if n == 0 {
                Ok(pk.zero.dup2())
            } else {
                Err(RdErr::Bad)
            }
        }
        1 => {
            if n == 1 {
                match level_in(pk, r, g, region::region_fld(bs, g, 0), sub) {
                    Err(e) => Err(e),
                    Ok(u) => rd_of(ar.intern_level(pers, LNodeView::Succ(u))),
                }
            } else {
                Err(RdErr::Bad)
            }
        }
        2 => level_bin(pk, pers, ar, bs, r, g, n, false, sub),
        3 => level_bin(pk, pers, ar, bs, r, g, n, true, sub),
        4 => {
            if n == 1 {
                match name_in(pk, r, g, region::region_fld(bs, g, 0), sub) {
                    Err(e) => Err(e),
                    Ok(x) => rd_of(ar.intern_level(pers, LNodeView::Param(x))),
                }
            } else {
                Err(RdErr::Bad)
            }
        }
        _ => Err(RdErr::Bad),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:127-148 levelNode
/// The `max` and `imax` arms.
pub fn level_bin<S: Sub>(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, g: u64, n: u64, imax: bool, sub: &S) -> Result<LIdx, RdErr> {
    if n != 2 {
        return Err(RdErr::Bad);
    }
    match level_in(pk, r, g, region::region_fld(bs, g, 0), sub) {
        Err(e) => Err(e),
        Ok(u) => match level_in(pk, r, g, region::region_fld(bs, g, 1), sub) {
            Err(e) => Err(e),
            Ok(v) => {
                if imax {
                    rd_of(ar.intern_level(pers, LNodeView::Imax(u, v)))
                } else {
                    rd_of(ar.intern_level(pers, LNodeView::Max(u, v)))
                }
            }
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:150-160 levelsNode
/// **A `List Level` cell** at `g`: `u :: us` as one interned list.  Deviation:
/// every suffix of a list that the file holds as a cell is interned too; the
/// store's level lists are short and hash-consed, so this is a few nodes.
pub fn levels_node<S: Sub>(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, g: u64, sub: &S) -> Result<LsIdx, RdErr> {
    if !region::region_fits(bs, r, g) {
        return Err(RdErr::Bad);
    }
    if region::region_tag(bs, g) == 1 && region::region_nobjs(bs, g) == 2 {
        match level_in(pk, r, g, region::region_fld(bs, g, 0), sub) {
            Err(e) => Err(e),
            Ok(u) => match levels_in(pk, r, g, region::region_fld(bs, g, 1), sub) {
                Err(e) => Err(e),
                Ok(us) => levels_cons(pers, ar, u, &us),
            },
        }
    } else {
        Err(RdErr::Bad)
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:150-160 levelsNode
/// `u :: us` over handles.
pub fn levels_cons(pers: &PersTier, ar: &mut EStore, u: LIdx, us: &LsIdx) -> Result<LsIdx, RdErr> {
    match ar.ls_s().view(pers, us) {
        None => rd_of(crate::arena::monad::fail_dangling_ls()),
        Some(rest) => {
            let mut out: Vec<LIdx> = Vec::with_capacity(rest.len() + 1);
            out.push(u);
            let mut i = 0usize;
            while i < rest.len() {
                out.push(rest[i].dup2());
                i += 1;
            }
            rd_of(ar.intern_levels(pers, out))
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:162-206 exprNode
/// **An `Expr` object** at `g`, interned.  Metadata is transparent: an `mdata`
/// node IS its body.
pub fn expr_node<S: Sub>(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, g: u64, sub: &S) -> Result<EIdx, RdErr> {
    if !region::region_fits(bs, r, g) {
        return Err(RdErr::Bad);
    }
    let n = region::region_nobjs(bs, g);
    match region::region_tag(bs, g) {
        5 => {
            if n == 2 {
                expr_app(pers, ar, bs, r, g, sub)
            } else {
                Err(RdErr::Bad)
            }
        }
        0 => {
            if n == 1 {
                expr_bvar(pers, ar, bs, r, g)
            } else {
                Err(RdErr::Bad)
            }
        }
        3 => {
            if n == 1 {
                match level_in(pk, r, g, region::region_fld(bs, g, 0), sub) {
                    Err(e) => Err(e),
                    Ok(u) => rd_of(ar.intern(pers, ENodeView::Sort(u))),
                }
            } else {
                Err(RdErr::Bad)
            }
        }
        4 => {
            if n == 2 {
                expr_const(pk, pers, ar, bs, r, g, sub)
            } else {
                Err(RdErr::Bad)
            }
        }
        6 => {
            if n == 3 {
                expr_bind(pers, ar, bs, r, g, false, sub)
            } else {
                Err(RdErr::Bad)
            }
        }
        7 => {
            if n == 3 {
                expr_bind(pers, ar, bs, r, g, true, sub)
            } else {
                Err(RdErr::Bad)
            }
        }
        8 => {
            if n == 4 {
                expr_let(pers, ar, bs, r, g, sub)
            } else {
                Err(RdErr::Bad)
            }
        }
        9 => {
            if n == 1 {
                match lit_p(bs, r, g, region::region_fld(bs, g, 0)) {
                    None => Err(RdErr::Bad),
                    Some(l) => rd_of(ar.intern(pers, ENodeView::Lit(l))),
                }
            } else {
                Err(RdErr::Bad)
            }
        }
        10 => {
            if n == 2 {
                expr_in(r, g, region::region_fld(bs, g, 1), sub)
            } else {
                Err(RdErr::Bad)
            }
        }
        11 => {
            if n == 3 {
                expr_proj(pk, pers, ar, bs, r, g, sub)
            } else {
                Err(RdErr::Bad)
            }
        }
        _ => Err(RdErr::Bad),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:162-206 exprNode
/// The `app` arm.
#[inline(always)]
pub fn expr_app<S: Sub>(pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, g: u64, sub: &S) -> Result<EIdx, RdErr> {
    match expr_in(r, g, region::region_fld(bs, g, 0), sub) {
        Err(e) => Err(e),
        Ok(f) => match expr_in(r, g, region::region_fld(bs, g, 1), sub) {
            Err(e) => Err(e),
            Ok(a) => rd_of(ar.intern(pers, ENodeView::App(f, a))),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:162-206 exprNode
/// The `bvar` arm.
pub fn expr_bvar(pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, g: u64) -> Result<EIdx, RdErr> {
    match region::region_nat_sat(bs, r, g, region::region_fld(bs, g, 0)) {
        None => Err(RdErr::Bad),
        Some(i) => match nat_word(i) {
            Err(e) => Err(e),
            Ok(i) => rd_of(ar.intern(pers, ENodeView::BVar(i))),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:162-206 exprNode
/// The `const` arm.
pub fn expr_const<S: Sub>(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, g: u64, sub: &S) -> Result<EIdx, RdErr> {
    match name_in(pk, r, g, region::region_fld(bs, g, 0), sub) {
        Err(e) => Err(e),
        Ok(x) => match levels_in(pk, r, g, region::region_fld(bs, g, 1), sub) {
            Err(e) => Err(e),
            Ok(us) => rd_of(ar.intern(pers, ENodeView::Const(x, us))),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:162-206 exprNode
/// The `lam` and `forallE` arms.
pub fn expr_bind<S: Sub>(pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, g: u64, pi: bool, sub: &S) -> Result<EIdx, RdErr> {
    match expr_in(r, g, region::region_fld(bs, g, 1), sub) {
        Err(e) => Err(e),
        Ok(ty) => match expr_in(r, g, region::region_fld(bs, g, 2), sub) {
            Err(e) => Err(e),
            Ok(b) => {
                if pi {
                    rd_of(ar.intern(pers, ENodeView::ForallE(ty, b)))
                } else {
                    rd_of(ar.intern(pers, ENodeView::Lam(ty, b)))
                }
            }
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:162-206 exprNode
/// The `letE` arm.
pub fn expr_let<S: Sub>(pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, g: u64, sub: &S) -> Result<EIdx, RdErr> {
    match expr_in(r, g, region::region_fld(bs, g, 1), sub) {
        Err(e) => Err(e),
        Ok(ty) => match expr_in(r, g, region::region_fld(bs, g, 2), sub) {
            Err(e) => Err(e),
            Ok(v) => match expr_in(r, g, region::region_fld(bs, g, 3), sub) {
                Err(e) => Err(e),
                Ok(b) => rd_of(ar.intern(pers, ENodeView::LetE(ty, v, b))),
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:162-206 exprNode
/// The `proj` arm.
pub fn expr_proj<S: Sub>(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, g: u64, sub: &S) -> Result<EIdx, RdErr> {
    match name_in(pk, r, g, region::region_fld(bs, g, 0), sub) {
        Err(e) => Err(e),
        Ok(s) => match region::region_nat_sat(bs, r, g, region::region_fld(bs, g, 1)) {
            None => Err(RdErr::Bad),
            Some(i) => match nat_word(i) {
                Err(e) => Err(e),
                Ok(i) => match expr_in(r, g, region::region_fld(bs, g, 2), sub) {
                    Err(e) => Err(e),
                    Ok(x) => rd_of(ar.intern(pers, ENodeView::Proj(s, i, x))),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:210-213 nameAt
/// con-leche: ConLeche/Frontend/Olean/Spec.lean:111-125 nameNode
/// **The `Name` stored at location `g`**, interned: a `Name` is a chain, so this
/// is linear, and it is the one read of the specification that executes.
pub fn name_at(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, g: u64) -> Result<NIdx, RdErr> {
    if !region::region_fits(bs, r, g) {
        return Err(RdErr::Bad);
    }
    let t = region::region_tag(bs, g);
    if name_shape(t, region::region_nobjs(bs, g)) {
        let v = region::region_fld(bs, g, 0);
        let p = if v == 1 {
            pk.anon.dup2()
        } else {
            match region::region_down(r, g, v) {
                None => return Err(RdErr::Bad),
                Some(c) => match name_at(pk, pers, ar, bs, r, c) {
                    Err(e) => return Err(e),
                    Ok(p) => p,
                },
            }
        };
        name_tail(pers, ar, bs, r, g, t, p)
    } else {
        Err(RdErr::Bad)
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:231-236 nameP
/// The `Name` a pointer stands for.
pub fn name_p(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, v: u64) -> Result<NIdx, RdErr> {
    if v == 1 {
        Ok(pk.anon.dup2())
    } else {
        match region::region_loc(r, v) {
            Some(c) => name_at(pk, pers, ar, bs, r, c),
            None => Err(RdErr::Bad),
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:250-260 CKindF
/// A constant's kind, generic in what stands for a name and an expression:
/// pointers in the skeleton, handles once read.
pub enum CKindF<N, E> {
    Ax(bool),
    Defn(E, HintsRec, Vec<u32>),
    Thm(E, Vec<N>),
    Opaq(E, bool),
    Quot(Vec<u32>),
    Induct(u64, u64, Vec<N>, Vec<N>, u64, bool, bool, bool),
    Ctor(N, u64, u64, u64, bool),
    Recur(Vec<N>, u64, u64, u64, u64, Vec<(N, u64, E)>, bool, bool),
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:271-272 CKind
/// con-leche: ConLeche/Frontend/Olean/Spec.lean:262-266 CEntryF
/// One stored constant, generic in what stands for a name and an expression.
pub struct CEntryF<N, E> {
    pub name: N,
    pub level_params: Vec<N>,
    pub ty: E,
    pub kind: CKindF<N, E>,
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:274-296 CKindF.mapM
/// con-leche: ConLeche/Frontend/Olean/Spec.lean:298-305 CEntryF.mapM
/// The `fn` and `fe` of `CEntryF.mapM`: what a pointer of a skeleton stands for.
pub trait PtrRead {
    /// con-leche: ConLeche/Frontend/Olean/Spec.lean:298-305 CEntryF.mapM
    fn rd_name(&self, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, v: u64) -> Result<NIdx, RdErr>;
    /// con-leche: ConLeche/Frontend/Olean/Spec.lean:298-305 CEntryF.mapM
    fn rd_expr(&self, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, v: u64) -> Result<EIdx, RdErr>;
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:274-296 CKindF.mapM
/// `all.mapM fn`.
pub fn names_map<R: PtrRead>(rd: &R, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, ns: &Vec<u64>) -> Result<Vec<NIdx>, RdErr> {
    let mut out: Vec<NIdx> = Vec::with_capacity(ns.len());
    let mut i = 0usize;
    while i < ns.len() {
        match rd.rd_name(pk, pers, ar, bs, r, ns[i]) {
            Err(e) => return Err(e),
            Ok(h) => out.push(h),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:274-296 CKindF.mapM
/// `rules.mapM`.
pub fn rules_map<R: PtrRead>(rd: &R, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, rs: &Vec<(u64, u64, u64)>) -> Result<Vec<(NIdx, u64, EIdx)>, RdErr> {
    let mut out: Vec<(NIdx, u64, EIdx)> = Vec::with_capacity(rs.len());
    let mut i = 0usize;
    while i < rs.len() {
        match rd.rd_name(pk, pers, ar, bs, r, rs[i].0) {
            Err(e) => return Err(e),
            Ok(c) => match rd.rd_expr(pk, pers, ar, bs, r, rs[i].2) {
                Err(e) => return Err(e),
                Ok(x) => out.push((c, rs[i].1, x)),
            },
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: none — a hint, copied (`HintsRec` is plain data in the Lean)
pub fn hints_dup(h: &HintsRec) -> HintsRec {
    match h {
        HintsRec::Abbrev => HintsRec::Abbrev,
        HintsRec::Opaque => HintsRec::Opaque,
        HintsRec::Regular(n) => HintsRec::Regular(*n),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:274-296 CKindF.mapM
/// Read every name and expression of a kind.
pub fn c_kind_map<R: PtrRead>(rd: &R, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, k: &CKindF<u64, u64>) -> Result<CKindF<NIdx, EIdx>, RdErr> {
    match k {
        CKindF::Ax(u) => Ok(CKindF::Ax(*u)),
        CKindF::Defn(v, h, s) => match rd.rd_expr(pk, pers, ar, bs, r, *v) {
            Err(e) => Err(e),
            Ok(x) => Ok(CKindF::Defn(x, hints_dup(h), expr::str_copy(s))),
        },
        CKindF::Thm(v, all) => match rd.rd_expr(pk, pers, ar, bs, r, *v) {
            Err(e) => Err(e),
            Ok(x) => match names_map(rd, pk, pers, ar, bs, r, all) {
                Err(e) => Err(e),
                Ok(a) => Ok(CKindF::Thm(x, a)),
            },
        },
        CKindF::Opaq(v, u) => match rd.rd_expr(pk, pers, ar, bs, r, *v) {
            Err(e) => Err(e),
            Ok(x) => Ok(CKindF::Opaq(x, *u)),
        },
        CKindF::Quot(s) => Ok(CKindF::Quot(expr::str_copy(s))),
        CKindF::Induct(np, ni, all, cs, nn, ir, iu, irf) => match names_map(rd, pk, pers, ar, bs, r, all) {
            Err(e) => Err(e),
            Ok(a) => match names_map(rd, pk, pers, ar, bs, r, cs) {
                Err(e) => Err(e),
                Ok(c) => Ok(CKindF::Induct(*np, *ni, a, c, *nn, *ir, *iu, *irf)),
            },
        },
        CKindF::Ctor(ind, ci, np, nf, iu) => match rd.rd_name(pk, pers, ar, bs, r, *ind) {
            Err(e) => Err(e),
            Ok(i) => Ok(CKindF::Ctor(i, *ci, *np, *nf, *iu)),
        },
        CKindF::Recur(all, np, ni, nmo, nmi, rules, k2, iu) => match names_map(rd, pk, pers, ar, bs, r, all) {
            Err(e) => Err(e),
            Ok(a) => match rules_map(rd, pk, pers, ar, bs, r, rules) {
                Err(e) => Err(e),
                Ok(rs) => Ok(CKindF::Recur(a, *np, *ni, *nmo, *nmi, rs, *k2, *iu)),
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:298-305 CEntryF.mapM
/// Read every name and expression of a constant.
pub fn c_entry_map<R: PtrRead>(rd: &R, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, c: &CEntryF<u64, u64>) -> Result<CEntryF<NIdx, EIdx>, RdErr> {
    let name = match rd.rd_name(pk, pers, ar, bs, r, c.name) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    let lps = match names_map(rd, pk, pers, ar, bs, r, &c.level_params) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    let ty = match rd.rd_expr(pk, pers, ar, bs, r, c.ty) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    match c_kind_map(rd, pk, pers, ar, bs, r, &c.kind) {
        Err(e) => Err(e),
        Ok(kind) => Ok(CEntryF { name, level_params: lps, ty, kind }),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:307-308 Region.natF
/// A `Nat` field, as a saturating word (module note).
#[inline(always)]
pub fn nat_f(bs: &[u8], r: &Region, g: u64, i: u64) -> Option<u64> {
    region::region_nat_sat(bs, r, g, region::region_fld(bs, g, i))
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:310-312 Region.nameList
/// A `List Name` field: its elements' pointers.
pub fn name_list(bs: &[u8], r: &Region, g: u64, i: u64) -> Option<Vec<u64>> {
    region::region_list(bs, r, g, region::region_fld(bs, g, i))
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:314-321 hintsSkel
/// A definition's reducibility hints, the field `hv` of the object at `x`.
pub fn hints_skel(bs: &[u8], r: &Region, x: u64, hv: u64) -> Option<HintsRec> {
    if hv == 1 {
        Some(HintsRec::Opaque)
    } else if hv == 3 {
        Some(HintsRec::Abbrev)
    } else {
        match region::region_down(r, x, hv) {
            None => None,
            Some(h) => {
                if !region::region_is_ctor(bs, r, h, 2, 0) {
                    return None;
                }
                match region::region_u32(bs, r, h, 0) {
                    None => None,
                    Some(k) => Some(HintsRec::Regular(k as u64)),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:323-327 ruleSkel
/// A recursor rule `v`, a cell of the recursor object at `x`.
pub fn rule_skel(bs: &[u8], r: &Region, x: u64, v: u64) -> Option<(u64, u64, u64)> {
    match region::region_down(r, x, v) {
        None => None,
        Some(y) => {
            if !region::region_is_ctor(bs, r, y, 0, 3) {
                return None;
            }
            match region::region_ptr_fld(bs, r, y, 0) {
                None => None,
                Some(c) => match nat_f(bs, r, y, 1) {
                    None => None,
                    Some(n) => match region::region_ptr_fld(bs, r, y, 2) {
                        None => None,
                        Some(e) => Some((c, n, e)),
                    },
                },
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:329-369 kindSkel
/// `cells.toList.mapM (ruleSkel r x)`.
pub fn rules_skel(bs: &[u8], r: &Region, x: u64, cells: &Vec<u64>) -> Option<Vec<(u64, u64, u64)>> {
    let mut out: Vec<(u64, u64, u64)> = Vec::with_capacity(cells.len());
    let mut i = 0usize;
    while i < cells.len() {
        match rule_skel(bs, r, x, cells[i]) {
            None => return None,
            Some(ru) => out.push(ru),
        }
        i += 1;
    }
    Some(out)
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:329-369 kindSkel
/// A definition's arm of `kindSkel`.
pub fn kind_skel_defn(bs: &[u8], r: &Region, x: u64) -> Option<CKindF<u64, u64>> {
    if !region::region_is_ctor(bs, r, x, 0, 4) {
        return None;
    }
    match region::region_ptr_fld(bs, r, x, 1) {
        None => None,
        Some(value) => match hints_skel(bs, r, x, region::region_fld(bs, x, 2)) {
            None => None,
            Some(hints) => match region::region_u8(bs, r, x, 0) {
                Some(0) => Some(CKindF::Defn(value, hints, { const M: [u32; 6] = [117, 110, 115, 97, 102, 101]; crate::kernel::core_types::code_points(&M) })),
                Some(1) => Some(CKindF::Defn(value, hints, { const M: [u32; 4] = [115, 97, 102, 101]; crate::kernel::core_types::code_points(&M) })),
                Some(2) => Some(CKindF::Defn(value, hints, { const M: [u32; 7] = [112, 97, 114, 116, 105, 97, 108]; crate::kernel::core_types::code_points(&M) })),
                _ => None,
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:329-369 kindSkel
/// An inductive type's arm of `kindSkel`.
pub fn kind_skel_induct(bs: &[u8], r: &Region, x: u64) -> Option<CKindF<u64, u64>> {
    if !region::region_is_ctor(bs, r, x, 0, 6) {
        return None;
    }
    match nat_f(bs, r, x, 1) {
        None => None,
        Some(np) => match nat_f(bs, r, x, 2) {
            None => None,
            Some(ni) => match name_list(bs, r, x, 3) {
                None => None,
                Some(all) => match name_list(bs, r, x, 4) {
                    None => None,
                    Some(cs) => match nat_f(bs, r, x, 5) {
                        None => None,
                        Some(nn) => match region::region_bool(bs, r, x, 0) {
                            None => None,
                            Some(ir) => match region::region_bool(bs, r, x, 1) {
                                None => None,
                                Some(iu) => match region::region_bool(bs, r, x, 2) {
                                    None => None,
                                    Some(irf) => Some(CKindF::Induct(np, ni, all, cs, nn, ir, iu, irf)),
                                },
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:329-369 kindSkel
/// A recursor's arm of `kindSkel`.
pub fn kind_skel_recur(bs: &[u8], r: &Region, x: u64) -> Option<CKindF<u64, u64>> {
    if !region::region_is_ctor(bs, r, x, 0, 7) {
        return None;
    }
    match name_list(bs, r, x, 1) {
        None => None,
        Some(all) => match region::region_list(bs, r, x, region::region_fld(bs, x, 6)) {
            None => None,
            Some(cells) => match rules_skel(bs, r, x, &cells) {
                None => None,
                Some(rules) => match nat_f(bs, r, x, 2) {
                    None => None,
                    Some(np) => match nat_f(bs, r, x, 3) {
                        None => None,
                        Some(ni) => match nat_f(bs, r, x, 4) {
                            None => None,
                            Some(nmo) => match nat_f(bs, r, x, 5) {
                                None => None,
                                Some(nmi) => match region::region_bool(bs, r, x, 0) {
                                    None => None,
                                    Some(k) => match region::region_bool(bs, r, x, 1) {
                                        None => None,
                                        Some(iu) => Some(CKindF::Recur(all, np, ni, nmo, nmi, rules, k, iu)),
                                    },
                                },
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:329-369 kindSkel
/// The kind of the `ConstantInfo` of tag `t`, its value object at `x`.
pub fn kind_skel(bs: &[u8], r: &Region, t: u64, x: u64) -> Option<CKindF<u64, u64>> {
    if t == 0 {
        if !region::region_is_ctor(bs, r, x, 0, 1) {
            return None;
        }
        match region::region_bool(bs, r, x, 0) {
            None => None,
            Some(u) => Some(CKindF::Ax(u)),
        }
    } else if t == 1 {
        kind_skel_defn(bs, r, x)
    } else if t == 2 {
        if !region::region_is_ctor(bs, r, x, 0, 3) {
            return None;
        }
        match region::region_ptr_fld(bs, r, x, 1) {
            None => None,
            Some(v) => match name_list(bs, r, x, 2) {
                None => None,
                Some(all) => Some(CKindF::Thm(v, all)),
            },
        }
    } else if t == 3 {
        if !region::region_is_ctor(bs, r, x, 0, 3) {
            return None;
        }
        match region::region_ptr_fld(bs, r, x, 1) {
            None => None,
            Some(v) => match region::region_bool(bs, r, x, 0) {
                None => None,
                Some(u) => Some(CKindF::Opaq(v, u)),
            },
        }
    } else if t == 4 {
        if !region::region_is_ctor(bs, r, x, 0, 1) {
            return None;
        }
        match region::region_u8(bs, r, x, 0) {
            Some(0) => Some(CKindF::Quot({ const M: [u32; 4] = [116, 121, 112, 101]; crate::kernel::core_types::code_points(&M) })),
            Some(1) => Some(CKindF::Quot({ const M: [u32; 4] = [99, 116, 111, 114]; crate::kernel::core_types::code_points(&M) })),
            Some(2) => Some(CKindF::Quot({ const M: [u32; 4] = [108, 105, 102, 116]; crate::kernel::core_types::code_points(&M) })),
            Some(3) => Some(CKindF::Quot({ const M: [u32; 3] = [105, 110, 100]; crate::kernel::core_types::code_points(&M) })),
            _ => None,
        }
    } else if t == 5 {
        kind_skel_induct(bs, r, x)
    } else if t == 6 {
        if !region::region_is_ctor(bs, r, x, 0, 5) {
            return None;
        }
        match region::region_ptr_fld(bs, r, x, 1) {
            None => None,
            Some(ind) => match nat_f(bs, r, x, 2) {
                None => None,
                Some(ci) => match nat_f(bs, r, x, 3) {
                    None => None,
                    Some(np) => match nat_f(bs, r, x, 4) {
                        None => None,
                        Some(nf) => match region::region_bool(bs, r, x, 0) {
                            None => None,
                            Some(iu) => Some(CKindF::Ctor(ind, ci, np, nf, iu)),
                        },
                    },
                },
            },
        }
    } else {
        kind_skel_recur(bs, r, x)
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:371-383 constSkel
/// **The skeleton of the `ConstantInfo` at location `c`**: everything but its
/// names and expressions, which stay pointers.
pub fn const_skel(bs: &[u8], r: &Region, c: u64) -> Option<CEntryF<u64, u64>> {
    if !(region::region_nobjs(bs, c) == 1 && region::region_tag(bs, c) <= 7 && region::region_fits(bs, r, c)) {
        return None;
    }
    let x = match region::region_down(r, c, region::region_fld(bs, c, 0)) {
        None => return None,
        Some(x) => x,
    };
    if !(1 <= region::region_nobjs(bs, x) && region::region_fits(bs, r, x)) {
        return None;
    }
    let cv = match region::region_down(r, x, region::region_fld(bs, x, 0)) {
        None => return None,
        Some(cv) => cv,
    };
    if !region::region_is_ctor(bs, r, cv, 0, 3) {
        return None;
    }
    let name = match region::region_ptr_fld(bs, r, cv, 0) {
        None => return None,
        Some(v) => v,
    };
    let lps = match name_list(bs, r, cv, 1) {
        None => return None,
        Some(v) => v,
    };
    let ty = match region::region_ptr_fld(bs, r, cv, 2) {
        None => return None,
        Some(v) => v,
    };
    match kind_skel(bs, r, region::region_tag(bs, c), x) {
        None => None,
        Some(kind) => Some(CEntryF { name, level_params: lps, ty, kind }),
    }
}

/// con-leche: none — the numbers a skeleton holds fit a word (module note)
/// A number `u64::MAX` in a skeleton is the `Native` decline; `Nat`s below it are
/// themselves.
pub fn skel_fits<N, E>(c: &CEntryF<N, E>) -> Result<(), RdErr> {
    let bad: bool = match &c.kind {
        CKindF::Induct(np, ni, _, _, nn, _, _, _) => *np == u64::MAX || *ni == u64::MAX || *nn == u64::MAX,
        CKindF::Ctor(_, ci, np, nf, _) => *ci == u64::MAX || *np == u64::MAX || *nf == u64::MAX,
        CKindF::Recur(_, np, ni, nmo, nmi, rules, _, _) => {
            *np == u64::MAX || *ni == u64::MAX || *nmo == u64::MAX || *nmi == u64::MAX || rules_too_big(rules)
        }
        _ => false,
    };
    if bad {
        match nat_word(u64::MAX) {
            Err(e) => Err(e),
            Ok(_) => Ok(()),
        }
    } else {
        Ok(())
    }
}

/// con-leche: none — `skel_fits`'s walk over a recursor's rules
pub fn rules_too_big<N, E>(rules: &Vec<(N, u64, E)>) -> bool {
    let mut i = 0usize;
    while i < rules.len() {
        if rules[i].1 == u64::MAX {
            return true;
        }
        i += 1;
    }
    false
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:387-397 ImportF
/// One `import` of a module, with Lean's flags, generic in its name.
pub struct ImportF<N> {
    pub module: N,
    pub import_all: bool,
    pub is_exported: bool,
    pub is_meta: bool,
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:403-404 ImportRec
/// An `import`, its name read.
pub type ImportRec = ImportF<NIdx>;

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:387-397 ImportF
/// The cited `BEq`, on two `import`s whose names are handles.
pub fn import_rec_beq(a: &ImportRec, b: &ImportRec) -> bool {
    a.module.eq2(&b.module)
        && a.import_all == b.import_all
        && a.is_exported == b.is_exported
        && a.is_meta == b.is_meta
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:387-397 ImportF
/// `Array ImportRec`'s `BEq`.
pub fn imports_beq(a: &Vec<ImportRec>, b: &Vec<ImportRec>) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0usize;
    while i < a.len() {
        if !import_rec_beq(&a[i], &b[i]) {
            return false;
        }
        i += 1;
    }
    true
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:406-409 ImportF.mapM
/// Read an `import`'s name.
pub fn import_map<R: PtrRead>(rd: &R, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, i: &ImportF<u64>) -> Result<ImportRec, RdErr> {
    match rd.rd_name(pk, pers, ar, bs, r, i.module) {
        Err(e) => Err(e),
        Ok(m) => Ok(ImportF { module: m, import_all: i.import_all, is_exported: i.is_exported, is_meta: i.is_meta }),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:411-416 importSkel
/// The `Import` object at location `i`: the module's name, then three one-byte
/// scalars in declaration order.
pub fn import_skel(bs: &[u8], r: &Region, i: u64) -> Option<ImportF<u64>> {
    if !region::region_is_ctor(bs, r, i, 0, 1) {
        return None;
    }
    match region::region_ptr_fld(bs, r, i, 0) {
        None => None,
        Some(module) => match region::region_bool(bs, r, i, 0) {
            None => None,
            Some(import_all) => match region::region_bool(bs, r, i, 1) {
                None => None,
                Some(is_exported) => match region::region_bool(bs, r, i, 2) {
                    None => None,
                    Some(is_meta) => Some(ImportF { module, import_all, is_exported, is_meta }),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:418-424 ModSkel
/// **The skeleton of the root `ModuleData`.**
pub struct ModSkel {
    pub is_module: bool,
    pub imports: Vec<ImportF<u64>>,
    pub consts: Vec<u64>,
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:426-433 moduleSkel
/// `imps.toList.mapM (importSkel r)`.
pub fn imports_skel(bs: &[u8], r: &Region, imps: &Vec<u64>) -> Option<Vec<ImportF<u64>>> {
    let mut out: Vec<ImportF<u64>> = Vec::with_capacity(imps.len());
    let mut i = 0usize;
    while i < imps.len() {
        match import_skel(bs, r, imps[i]) {
            None => return None,
            Some(x) => out.push(x),
        }
        i += 1;
    }
    Some(out)
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:426-433 moduleSkel
/// The skeleton of the `ModuleData` at address `root`.
pub fn module_skel(bs: &[u8], r: &Region, root: u64) -> Option<ModSkel> {
    let g = match region::region_loc(r, root) {
        None => return None,
        Some(g) => g,
    };
    if !region::region_is_ctor(bs, r, g, 0, 5) {
        return None;
    }
    let is_module = match region::region_bool(bs, r, g, 0) {
        None => return None,
        Some(b) => b,
    };
    let imps = match region::region_obj_array(bs, r, g, region::region_fld(bs, g, 0)) {
        None => return None,
        Some(v) => v,
    };
    let imports = match imports_skel(bs, r, &imps) {
        None => return None,
        Some(v) => v,
    };
    match region::region_obj_array(bs, r, g, region::region_fld(bs, g, 2)) {
        None => None,
        Some(consts) => Some(ModSkel { is_module, imports, consts }),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:435-440 ModDecoded
/// What the reader takes of a module: the flag, the imports and the constants.
pub struct ModDecoded {
    pub is_module: bool,
    pub imports: Vec<ImportRec>,
    pub constants: Vec<CEntryF<NIdx, EIdx>>,
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:447-457 constNamesGo
/// `r.loc sk.name == some n || nameP r sk.name == some a`.
pub fn name_entry_agrees(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, n: u64, v: u64, a: &NIdx) -> Result<bool, CheckError> {
    let same_object: bool = match region::region_loc(r, v) {
        Some(l) => l == n,
        None => false,
    };
    if same_object {
        Ok(true)
    } else {
        match name_p(pk, pers, ar, bs, r, v) {
            Err(RdErr::Bad) => Ok(false),
            Err(RdErr::Err(e)) => Err(e),
            Ok(b) => Ok(b.eq2(a)),
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:447-457 constNamesGo
/// One entry of the walk: entry `i` names constant `i`, a name not seen before.
pub fn const_name_step(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, n: u64, c: u64, seen: &mut HashMap2<NIdx, bool>) -> Result<bool, CheckError> {
    match const_skel(bs, r, c) {
        None => Ok(false),
        Some(sk) => match name_at(pk, pers, ar, bs, r, n) {
            Err(RdErr::Bad) => Ok(false),
            Err(RdErr::Err(e)) => Err(e),
            Ok(a) => match name_entry_agrees(pk, pers, ar, bs, r, n, sk.name, &a) {
                Err(e) => Err(e),
                Ok(false) => Ok(false),
                Ok(true) => {
                    if seen.contains_key(&a) {
                        Ok(false)
                    } else {
                        seen.insert(a, true);
                        Ok(true)
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:447-457 constNamesGo
/// `constNamesOk`'s walk over the two arrays: `seen` the names before.  Whether
/// the walk passes is the `bool`; only the store's capacity is an `Err`.
pub fn const_names_go(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, ns: &Vec<u64>, cs: &Vec<u64>, seen: &mut HashMap2<NIdx, bool>) -> Result<bool, CheckError> {
    let mut i = 0usize;
    while i < ns.len() {
        match const_name_step(pk, pers, ar, bs, r, ns[i], cs[i], seen) {
            Err(e) => return Err(e),
            Ok(false) => return Ok(false),
            Ok(true) => {}
        }
        i += 1;
    }
    Ok(true)
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:459-479 constNamesOk
/// **A part's name table agrees with its constants**: as many entries, entry `i`
/// the name of constant `i`, no name twice.
pub fn const_names_ok(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, bs: &[u8], r: &Region, root: u64) -> Result<bool, CheckError> {
    let g = match region::region_loc(r, root) {
        None => return Ok(false),
        Some(g) => g,
    };
    if !region::region_is_ctor(bs, r, g, 0, 5) {
        return Ok(false);
    }
    let ns = match region::region_obj_array(bs, r, g, region::region_fld(bs, g, 1)) {
        None => return Ok(false),
        Some(v) => v,
    };
    let cs = match region::region_obj_array(bs, r, g, region::region_fld(bs, g, 2)) {
        None => return Ok(false),
        Some(v) => v,
    };
    if ns.len() != cs.len() {
        return Ok(false);
    }
    let mut seen: HashMap2<NIdx, bool> = HashMap2::with_capacity(ns.len());
    const_names_go(pk, pers, ar, bs, r, &ns, &cs, &mut seen)
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:492-493 CEntryF.stmt
/// A stored constant's statement over handles.
pub struct StmtRec {
    pub name: NIdx,
    pub level_params: Vec<NIdx>,
    pub ty: EIdx,
}

/// con-leche: ConLeche/Frontend/Olean/Spec.lean:492-493 CEntryF.stmt
/// A stored constant's statement.
pub fn c_entry_stmt(c: &CEntryF<NIdx, EIdx>) -> StmtRec {
    StmtRec {
        name: c.name.dup2(),
        level_params: crate::arena::env::nidx_vec_dup(&c.level_params),
        ty: c.ty.dup2(),
    }
}

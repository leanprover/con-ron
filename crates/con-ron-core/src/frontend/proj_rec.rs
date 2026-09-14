//! `ConLeche/Frontend/ProjRec.lean` — projection functions of non-direct
//! structure-likes, rewritten as recursor applications.
//!
//! The elaborator spells a structure's projection function as
//! `fun p⃗ self => .proj T i self`.  The official kernel types `.proj T i` on
//! every *structure-like* type; this checker serves `.proj` only on the class
//! its direct install recognises, so on the Mathlib stream the first
//! projection function of a mutual member declines the run.  The user's
//! design (2026-09-06, verbatim): *"replace these projection functions, only
//! for mutual (not direct) inductives, by recursor applications, before
//! installation.  Completely transparent to the verified code."*  This module
//! is that rewrite, a pure function on the parsed declaration.
//!
//! **It cannot fire yet, and that is deliberate** (task #37).  The
//! elimination level `ℓ` is not syntactic in the projection's codomain: it is
//! read off the model family's own artifact `T._model.proj_i.iota`, and since
//! con-leche task #219 the ONLY source of that artifact is the in-process
//! modeller (`ConLeche/Frontend/InModel/Mutual.lean`).  con-ron declines
//! every stream that needs the modeller until the modeller lands, so
//! `export_c`'s `proj_levels` is always empty and the rewrite always answers
//! `None` — the declaration stays as parsed and declines as before, which is
//! exactly con-leche's "no artifact, no rewrite".  The module is ported now so
//! that the modeller task is the modeller and nothing else; its unit tests
//! below exercise the shape recognisers and the owner census, which DO run on
//! every inductive record of every stream.
//!
//! **Deviations.**  `occursConst`'s budgeted descent (`occursConstB`) is not
//! ported: it exists so that the common case allocates no `Std.HashSet` in
//! Lean, and `crate::ron::hashmap::HashMap::new` allocates nothing until its
//! first insert (task #35's lazy slots), so `occurs_const_fast` is the
//! memoised walk alone (all four Lean declarations are cited on it).  The
//! three tuple types `projRecOwners` takes become named structs, because a
//! seven-component Lean tuple read as `·.2.2.2.2.2.2` is not something to
//! transliterate.  And the two `Expr → Option Expr` functions `buildBinders`
//! takes are one-method traits on a type parameter (`MkBinder`), not closures:
//! §3.4 has no closures and no `dyn`, and a trait method on a type parameter
//! extracts as a typeclass field, which is what the refinement will quantify
//! over.
//!
//! `occursConstGo`'s `Std.HashSet Expr` is a `HashMap<Expr, bool>` keyed by
//! the `Expr` itself — con-leche's own dictionary (`Hashable Expr` is
//! `Expr.hash`, `Eq2 Expr` is `Expr.beq`), where the unverified frontend
//! keyed an `ExprKey` newtype by the node's address;
//! `crate::frontend::nat_op_ground`'s module note carries the reasoning and
//! the one measurement that argues the other way.

use crate::cached::expr_ops_c;
use crate::frontend::text;
use crate::kernel::basis_names as bnm;
use crate::kernel::core_types;
use crate::kernel::env;
use crate::kernel::env::ConstantInfo;
use crate::kernel::expr;
use crate::kernel::expr::{BinderMeta, Expr, ExprKind};
use crate::kernel::expr_ops;
use crate::kernel::inductives::native_parts;
use crate::kernel::inductives::struct_parts;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::levels;
use crate::kernel::name;
use crate::kernel::name::{Name, NameKind};
use crate::ron::hashmap::HashMap;

/// con-leche: ConLeche/Frontend/ProjRec.lean:83-104 ProjRecOwner
/// What the rewrite needs to know about one structure-like owner `T` of a
/// parsed inductive block that the direct install does not serve.
pub struct ProjRecOwner {
    /// the type former
    pub t: Name,
    /// the block's level parameters
    pub lps: Vec<Name>,
    /// parameter count
    pub n_p: u64,
    /// the single constructor
    pub ctor: Name,
    /// its field count
    pub n_f: u64,
    /// the owner's recursor `T.rec`: name, level parameters, type
    pub rec_name: Name,
    pub rec_lps: Vec<Name>,
    pub rec_type: Expr,
    /// the recursor's motive and minor counts (the export's own)
    pub num_motives: u64,
    pub num_minors: u64,
}

// ---------------------------------------------------------------------------
// The artifact's name, and the level it carries
// ---------------------------------------------------------------------------

/// con-leche: none — `String.startsWith` on the port's code-point representation
/// Whether the code-point string `s` begins with the literal `lit` (a
/// function-local `const …: [u32; N]`).  `text::cps_beq` is the whole-string
/// twin.
pub fn cps_starts_with(s: &Vec<u32>, lit: &[u32]) -> bool {
    if s.len() < lit.len() {
        return false;
    }
    let n = lit.len();
    let mut i: usize = 0;
    while i < n {
        if s[i] != lit[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:106-111 projIotaName
/// The name of the model family's constructor-reduction theorem for field `i`
/// of `T`: `T._model.proj_i.iota`.  The cited `s!"proj_{i}"` is
/// `text::cat`/`text::u64_str` (§3.4 has no `format!`).
pub fn proj_iota_name(t: &Name, i: u64) -> Name {
    const MODEL: [u32; 6] = [95, 109, 111, 100, 101, 108];
    const PROJ: [u32; 5] = [112, 114, 111, 106, 95];
    const IOTA: [u32; 4] = [105, 111, 116, 97];
    let a = name::mk_str(name::dup(t), core_types::code_points(&MODEL));
    let b = name::mk_str(
        a,
        text::cat(core_types::code_points(&PROJ), &text::u64_str(i)),
    );
    name::mk_str(b, core_types::code_points(&IOTA))
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:113-118 isProjIotaName
/// Is `n` of the shape `X._model.proj_i.iota`?  Cheap pre-filter for the
/// theorem records (the last component decides before anything is compared).
pub fn is_proj_iota_name(n: &Name) -> bool {
    const MODEL: [u32; 6] = [95, 109, 111, 100, 101, 108];
    const PROJ: [u32; 5] = [112, 114, 111, 106, 95];
    const IOTA: [u32; 4] = [105, 111, 116, 97];
    match &n.0.kind {
        NameKind::Str(p1, last) => {
            if !text::cps_beq(last, &IOTA) {
                false
            } else {
                match &p1.0.kind {
                    NameKind::Str(p2, s) => match &p2.0.kind {
                        NameKind::Str(_, m) => {
                            text::cps_beq(m, &MODEL) && cps_starts_with(s, &PROJ)
                        }
                        _ => false,
                    },
                    _ => false,
                }
            }
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:120-125 projIotaLevel
/// The `Eq` level of an artifact iota statement `∀ …, @Eq.{ℓ} α a b`: the
/// field's sort.  `None` on any other shape.
pub fn proj_iota_level(ty: &Expr) -> Option<Level> {
    let head = expr_ops::get_app_fn(&expr_ops::pi_result(ty));
    match &head.0.kind {
        ExprKind::Const(n, us) => {
            if levels::len(us) == 1 && name::beq(n, &bnm::eq_name()) {
                Some(levels::head_d(us))
            } else {
                None
            }
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// `occursConst`, memoised
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ProjRec.lean:227-231 occursConstFast
/// con-leche: ConLeche/Frontend/ProjRec.lean:180-225 occursConstGo
/// con-leche: ConLeche/Frontend/ProjRec.lean:151-178 occursConstB
/// con-leche: ConLeche/Frontend/ProjRec.lean:127-136 occursConst
/// Does the constant `n` occur in `e`?  (Not through fvar type annotations —
/// parsed declarations are fvar-free.)  Memoised: the map holds the subterms
/// already shown NOT to mention `n`, so only `false` is recorded — a `true`
/// aborts the walk and no `true` is ever re-queried.  `proj_rec_owners` runs
/// this over every constructor binder domain of every inductive block in the
/// stream, and structural recursion means `O(tree)` on a shared DAG.
pub fn occurs_const_fast(n: &Name, e: &Expr) -> bool {
    let mut seen: HashMap<Expr, bool> = HashMap::new();
    occurs_const_go(n, &mut seen, e)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:180-225 occursConstGo
/// The memoised descent's body: the four leaf arms answer before the probe,
/// every compound node is probed, walked, and recorded when it comes out
/// `false`.
pub fn occurs_const_go(n: &Name, seen: &mut HashMap<Expr, bool>, e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::Const(m, _) => name::beq(m, n),
        ExprKind::Bvar(_) => false,
        ExprKind::Fvar(_, _) => false,
        ExprKind::Sort(_) => false,
        ExprKind::Lit(_) => false,
        _ => {
            if seen.contains_key(e) {
                false
            } else {
                let hit = occurs_const_node(n, seen, e);
                if !hit {
                    seen.insert(expr::dup(e), false);
                }
                hit
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:180-225 occursConstGo
/// The inner `match e with` of the miss branch, split off so the probe's
/// borrow dies before the descent mutates the memo (task #14's rule).  The
/// final arm is unreachable — the four leaf kinds answered above.
pub fn occurs_const_node(n: &Name, seen: &mut HashMap<Expr, bool>, e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::App(f, a) => {
            if occurs_const_go(n, seen, f) {
                true
            } else {
                occurs_const_go(n, seen, a)
            }
        }
        ExprKind::Lam(ty, b, _) | ExprKind::ForallE(ty, b, _) => {
            if occurs_const_go(n, seen, ty) {
                true
            } else {
                occurs_const_go(n, seen, b)
            }
        }
        ExprKind::LetE(t, v, b) => {
            if occurs_const_go(n, seen, t) {
                true
            } else if occurs_const_go(n, seen, v) {
                true
            } else {
                occurs_const_go(n, seen, b)
            }
        }
        ExprKind::Proj(_, _, sub) => occurs_const_go(n, seen, sub),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Telescopes
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ProjRec.lean:233-237 lamBody
/// The body under every leading `λ` (the projection shape's pre-filter: the
/// node under the value's binders).
pub fn lam_body(e: &Expr) -> Expr {
    match &e.0.kind {
        ExprKind::Lam(_, b, _) => lam_body(b),
        _ => expr::dup(e),
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:239-245 stripPisAll
/// Strip every leading `∀`: the binder list (outermost first) and the body.
/// A spine walk, so the loop the directory's relaxation allows (the cited Lean
/// is the tail recursion Lean compiles to one).
pub fn strip_pis_all(e: &Expr) -> (Vec<(Expr, BinderMeta)>, Expr) {
    let mut bs: Vec<(Expr, BinderMeta)> = Vec::new();
    let mut cur = expr::dup(e);
    let mut more = true;
    while more {
        let next = match &cur.0.kind {
            ExprKind::ForallE(ty, b, m) => {
                bs.push((expr::dup(ty), expr::binder_meta_dup(m)));
                Some(expr::dup(b))
            }
            _ => None,
        };
        match next {
            Some(x) => {
                cur = x;
            }
            None => {
                more = false;
            }
        }
    }
    (bs, cur)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:247-249 mkLams
/// Rebuild a `λ`-telescope over a binder list (outermost first).  The cited
/// `foldr` is a countdown loop (§3.4 has no closures).
pub fn mk_lams(bs: &Vec<(Expr, BinderMeta)>, body: Expr) -> Expr {
    let mut acc = body;
    let mut i = bs.len();
    while i > 0 {
        i -= 1;
        acc = expr::lam(expr::dup(&bs[i].0), acc, expr::binder_meta_dup(&bs[i].1));
    }
    acc
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:251-257 instPisOpen
/// Instantiate the leading `∀`-binders at *open* arguments (the body-frame
/// variables and the built motives/minors), one binder per argument,
/// returning the residual telescope.
pub fn inst_pis_open(e: &Expr, args: &Vec<Expr>) -> Option<Expr> {
    let mut cur = expr::dup(e);
    let n = args.len();
    let mut i: usize = 0;
    let mut ok = true;
    while i < n && ok {
        let next = match &cur.0.kind {
            ExprKind::ForallE(_, body, _) => {
                Some(expr_ops_c::instantiate1_lift(body, &args[i], 0))
            }
            _ => None,
        };
        match next {
            Some(x) => {
                cur = x;
                i += 1;
            }
            None => {
                ok = false;
            }
        }
    }
    inst_pis_open_done(ok, cur)
}

/// con-leche: none — `inst_pis_open`'s tail, out of the loop
/// Aeneas' `-loops-to-rec` copies whatever follows a loop into every one of
/// its exits, so the tail is a function of its own.
pub fn inst_pis_open_done(ok: bool, cur: Expr) -> Option<Expr> {
    if ok {
        Some(cur)
    } else {
        None
    }
}

/// con-leche: none — the `Expr → Option Expr` argument of `buildBinders`
/// A one-method trait on a type parameter, where con-leche passes a function
/// (§3.4 has no closures, no `dyn` and no function pointers).  It extracts as
/// a typeclass field, i.e. an opaque function the refinement quantifies over,
/// and the two implementations below are the motive and the minor builders.
pub trait MkBinder {
    /// con-leche: none — the trait's one method.  **Not named `mk`**: a trait
    /// becomes a Lean `structure` and its methods become fields, and `mk` is
    /// the name Lean reserves for a structure's own constructor, so a method
    /// called `mk` produces a `structure` Lean refuses to elaborate
    /// ("Invalid field name `mk`", AENEAS_FINDINGS §3.7).
    fn binder(&self, dom: &Expr) -> Option<Expr>;
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:259-269 buildBinders
/// Peel `k` binders of a telescope, building one term per binder from its
/// (progressively instantiated) domain, and instantiating the telescope with
/// that term before the next binder is read.
pub fn build_binders<M: MkBinder>(mk: &M, k: u64, e: &Expr) -> Option<(Vec<Expr>, Expr)> {
    let mut out: Vec<Expr> = Vec::new();
    let mut cur = expr::dup(e);
    let mut i: u64 = 0;
    let mut ok = true;
    while i < k && ok {
        match build_binders_step(mk, &cur) {
            Some((t, b)) => {
                out.push(t);
                cur = b;
                i += 1;
            }
            None => {
                ok = false;
            }
        }
    }
    build_binders_done(ok, out, cur)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:259-269 buildBinders
/// The cited `| k + 1, .forallE dom body _ => do let t ← mk dom; …`: one
/// binder's term and the telescope instantiated at it, or `None` for the
/// cited `| _ + 1, _ => none`.  Its own function because `cur`'s borrow (the
/// `dom` and `body` of the match) may not still be alive where the loop
/// rebinds `cur` — AENEAS_FINDINGS §2.1 F1, which is what "Could not match the
/// contexts" was pointing at.
pub fn build_binders_step<M: MkBinder>(mk: &M, cur: &Expr) -> Option<(Expr, Expr)> {
    match &cur.0.kind {
        ExprKind::ForallE(dom, body, _) => build_binders_step_at(mk, dom, body),
        _ => None,
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:259-269 buildBinders
/// The cited `do` block of that arm, at the binder's domain and body: the
/// arm's own branch lifted out of the `match` on `cur` (§2.1 F3 — an arm must
/// end in a call, never in a branch).
pub fn build_binders_step_at<M: MkBinder>(
    mk: &M,
    dom: &Expr,
    body: &Expr,
) -> Option<(Expr, Expr)> {
    match mk.binder(dom) {
        Some(t) => {
            let b = expr_ops_c::instantiate1_lift(body, &t, 0);
            Some((t, b))
        }
        None => None,
    }
}

/// con-leche: none — `build_binders`' tail, out of the loop
/// As `inst_pis_open_done`: the post-loop code is a function so that
/// `-loops-to-rec` copies one call and not the tuple.
pub fn build_binders_done(ok: bool, out: Vec<Expr>, cur: Expr) -> Option<(Vec<Expr>, Expr)> {
    if ok {
        Some((out, cur))
    } else {
        None
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:271-277 headIs
/// Is `T` the head of the owner's own carrier: the motive domain
/// `∀ (t : T p⃗), Sort ℓ` (exactly one binder) or the major-premise domain.
pub fn head_is(t: &Name, e: &Expr) -> bool {
    match &expr_ops::get_app_fn(e).0.kind {
        ExprKind::Const(n, _) => name::beq(n, t),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// The rewrite
// ---------------------------------------------------------------------------

/// con-leche: none — Lean's `[ℓ]`, a one-element level list
/// `vec![…]` is out of the subset (it pulls `MaybeUninit` into the model), so
/// the port builds the singleton by hand.
pub fn one_level(l: &Level) -> Vec<Level> {
    let mut us: Vec<Level> = Vec::with_capacity(1);
    us.push(level::dup(l));
    us
}

/// con-leche: none — `.const punitName [ℓ]`, spelled once
/// The constant every motive but the owner's answers.
pub fn punit_at(l: &Level) -> Expr {
    expr::mk_const(bnm::punit_name(), one_level(l))
}

/// con-leche: none — `.const punitUnitName [ℓ]`, spelled once
/// The value every minor but the owner constructor's returns.
pub fn punit_unit_at(l: &Level) -> Expr {
    expr::mk_const(bnm::punit_unit_name(), one_level(l))
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// The cited `mkMotive`: the owner's motive is `fun (t : T p⃗) => R` (`R`'s
/// parameter references skip the new binder; its subject reference IS the new
/// binder); every other one is the constant `PUnit.{ℓ}` over its telescope.
pub struct MkMotive {
    pub t: Name,
    pub r: Expr,
    pub l: Level,
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// `mkMotive`, as the one method of `MkBinder`.
impl MkBinder for MkMotive {
    /// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
    /// The cited three-arm `match stripPisAll dom with`.
    fn binder(&self, dom: &Expr) -> Option<Expr> {
        let bse = strip_pis_all(dom);
        match &bse.1 .0.kind {
            ExprKind::Sort(_) => {
                if bse.0.len() == 1 {
                    if head_is(&self.t, &bse.0[0].0) {
                        Some(expr::lam(
                            expr::dup(&bse.0[0].0),
                            expr_ops::lift_loose_bvars(1, 1, &self.r),
                            expr::binder_meta_dup(&bse.0[0].1),
                        ))
                    } else {
                        Some(expr::lam(
                            expr::dup(&bse.0[0].0),
                            punit_at(&self.l),
                            expr::binder_meta_dup(&bse.0[0].1),
                        ))
                    }
                } else {
                    Some(mk_lams(&bse.0, punit_at(&self.l)))
                }
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// The cited `mkMinor`: the owner constructor's minor returns field `i` of its
/// telescope (fields first, then the inductive hypotheses); every other one
/// returns `PUnit.unit.{ℓ}`.  The owner's minor is the one whose codomain
/// applies a motive to the owner constructor.
pub struct MkMinor {
    pub ctor: Name,
    pub i: u64,
    pub l: Level,
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// `mkMinor`, as the one method of `MkBinder`.
impl MkBinder for MkMinor {
    /// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
    /// The cited `match cod.getAppArgs.getLast? with`; the empty spine is the
    /// cited `none` arm.
    fn binder(&self, dom: &Expr) -> Option<Expr> {
        let bse = strip_pis_all(dom);
        let args = expr_ops::get_app_args(&bse.1);
        if args.len() == 0 {
            None
        } else if head_is(&self.ctor, &args[args.len() - 1]) {
            if self.i < (bse.0.len() as u64) {
                Some(mk_lams(
                    &bse.0,
                    expr::mk_bvar((bse.0.len() as u64) - 1 - self.i),
                ))
            } else {
                None
            }
        } else {
            Some(mk_lams(&bse.0, punit_unit_at(&self.l)))
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// The cited `(List.range o.nP).map fun k => Expr.bvar (o.nP - k)`: the body
/// frame is the value's own `nP + 1` binders, so parameter `k` is
/// `bvar (nP - k)` and the subject is `bvar 0`.
pub fn bvar_params(n_p: u64) -> Vec<Expr> {
    let mut out: Vec<Expr> = Vec::with_capacity(n_p as usize);
    let mut k: u64 = 0;
    while k < n_p {
        out.push(expr::mk_bvar(n_p - k));
        k += 1;
    }
    out
}

/// con-leche: none — Lean's `xs ++ ys` on the recursor's argument spine
/// Append `xs` to the accumulator (§3.4: accumulators travel by value).
pub fn append_exprs(out: Vec<Expr>, xs: &Vec<Expr>) -> Vec<Expr> {
    let mut out = out;
    let n = xs.len();
    let mut i: usize = 0;
    while i < n {
        out.push(expr::dup(&xs[i]));
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// **The rewrite.**  `ty`/`val` are the definition's declared type and value,
/// `i` the projected field, `l` the field's sort (from the artifact).  `None`
/// = the value is not of the projection shape (the caller keeps the
/// declaration unchanged).  The cited `do` block's `←`/`guard` steps are
/// explicit `match`es (§3.4 has no `?`).
pub fn proj_rec_value(o: &ProjRecOwner, l: &Level, ty: &Expr, val: &Expr, i: u64) -> Option<Expr> {
    match expr_ops::strip_lams(o.n_p + 1, val) {
        None => None,
        Some(lbsb) => {
            let want = expr::proj(name::dup(&o.t), i, expr::mk_bvar(0));
            if !expr::beq(&lbsb.1, &want) {
                None
            } else if i >= o.n_f {
                None
            } else {
                match expr_ops::strip_pis(o.n_p + 1, ty) {
                    None => None,
                    Some(r) => proj_rec_value_at(o, l, &r.1, &lbsb.0, i),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// The cited block from `let us := o.lps.map Level.param` to the last
/// `buildBinders`: the recursor's type at the chosen elimination level, its
/// parameters instantiated at the body frame, then the motives and the minors.
pub fn proj_rec_value_at(
    o: &ProjRecOwner,
    l: &Level,
    r: &Expr,
    lbs: &Vec<(Expr, BinderMeta)>,
    i: u64,
) -> Option<Expr> {
    let us = struct_parts::params_of(&o.lps);
    let lus = append_levels(one_level(l), &us);
    let rty0 = expr_ops::instantiate_level_params(&o.rec_lps, &lus, &o.rec_type);
    let params = bvar_params(o.n_p);
    match inst_pis_open(&rty0, &params) {
        None => None,
        Some(rty1) => {
            let mkm = MkMotive {
                t: name::dup(&o.t),
                r: expr::dup(r),
                l: level::dup(l),
            };
            match build_binders(&mkm, o.num_motives, &rty1) {
                None => None,
                Some(mrt) => {
                    let mkn = MkMinor {
                        ctor: name::dup(&o.ctor),
                        i,
                        l: level::dup(l),
                    };
                    match build_binders(&mkn, o.num_minors, &mrt.1) {
                        None => None,
                        Some(nrt) => proj_rec_value_major(
                            o, &lus, &params, &mrt.0, &nrt.0, lbs, &nrt.1,
                        ),
                    }
                }
            }
        }
    }
}

/// con-leche: none — Lean's `ℓ :: us`, an accumulator append
/// `append_exprs` for the recursor's level list.
pub fn append_levels(out: Vec<Level>, us: &Vec<Level>) -> Vec<Level> {
    let mut out = out;
    let n = us.len();
    let mut i: usize = 0;
    while i < n {
        out.push(level::dup(&us[i]));
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// The cited final `match rty with | .forallE majDom _ _ => …`: the owner has
/// no indices, so the next binder is the subject itself, and the value is
/// `T.rec.{ℓ, u⃗} p⃗ motives minors (bvar 0)` under the definition's own
/// binders.
pub fn proj_rec_value_major(
    o: &ProjRecOwner,
    lus: &Vec<Level>,
    params: &Vec<Expr>,
    motives: &Vec<Expr>,
    minors: &Vec<Expr>,
    lbs: &Vec<(Expr, BinderMeta)>,
    rty: &Expr,
) -> Option<Expr> {
    match &rty.0.kind {
        ExprKind::ForallE(maj_dom, _, _) => {
            if !head_is(&o.t, maj_dom) {
                None
            } else {
                let mut args: Vec<Expr> = Vec::new();
                args = append_exprs(args, params);
                args = append_exprs(args, motives);
                args = append_exprs(args, minors);
                args.push(expr::mk_bvar(0));
                let app = expr_ops::mk_app_n(
                    expr::mk_const(name::dup(&o.rec_name), expr_ops::levels_copy(lus)),
                    &args,
                );
                Some(mk_lams(lbs, app))
            }
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The owner census
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// `types`' component of the export record's own shape data (Lean's
/// `(name, levelParams, type, numParams, numIndices, ctors, isRec)`).
pub struct ProjTypeRec {
    pub name: Name,
    pub lps: Vec<Name>,
    pub ty: Expr,
    pub n_p: u64,
    pub n_i: u64,
    pub ctors: Vec<Name>,
    pub is_rec: bool,
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// `ctors`' component (Lean's `(name, numFields, type)`).
pub struct ProjCtorRec {
    pub name: Name,
    pub n_f: u64,
    pub ty: Expr,
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// `recs`' component (Lean's `(name, levelParams, type, numMotives,
/// numMinors)`).
pub struct ProjRecRec {
    pub name: Name,
    pub lps: Vec<Name>,
    pub ty: Expr,
    pub n_m: u64,
    pub nm: u64,
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// The cited `types.map (·.1)`: the block's type formers.
pub fn type_names(types: &[ProjTypeRec]) -> Vec<Name> {
    let n = types.len();
    let mut out: Vec<Name> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        out.push(name::dup(&types[i].name));
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// The cited `types.any (·.2.2.2.2.2.2)`: the export's own `isRec` flag on any
/// member.
pub fn any_is_rec(types: &[ProjTypeRec]) -> bool {
    let n = types.len();
    let mut i: usize = 0;
    while i < n {
        if types[i].is_rec {
            return true;
        }
        i += 1;
    }
    false
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// The cited `ctors.any fun (_, _, cty) => (stripPisAll cty).1.any …`: a block
/// name in a constructor's binder *domains* (its result names the owner by
/// definition).
pub fn any_ctor_mentions(block_names: &Vec<Name>, ctors: &[ProjCtorRec]) -> bool {
    let n = ctors.len();
    let mut i: usize = 0;
    while i < n {
        let bse = strip_pis_all(&ctors[i].ty);
        if any_dom_mentions(block_names, &bse.0) {
            return true;
        }
        i += 1;
    }
    false
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// The cited `fun (d, _) => …` over the constructor's binder domains.
pub fn any_dom_mentions(block_names: &Vec<Name>, bs: &Vec<(Expr, BinderMeta)>) -> bool {
    let n = bs.len();
    let mut i: usize = 0;
    while i < n {
        if any_name_mentions(block_names, &bs[i].0) {
            return true;
        }
        i += 1;
    }
    false
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// The cited innermost `blockNames.any fun n => occursConstFast n d`, one
/// domain.  Its own function because Aeneas supports no `return` inside a
/// *nested* loop at all ("Returns inside of nested loops are not supported
/// yet"); lifted out, each of the two loops is a single loop whose early
/// return is followed by a constant.
pub fn any_name_mentions(block_names: &Vec<Name>, d: &Expr) -> bool {
    let m = block_names.len();
    let mut j: usize = 0;
    while j < m {
        if occurs_const_fast(&block_names[j], d) {
            return true;
        }
        j += 1;
    }
    false
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// The cited `ctors.find? (·.1 == C)`, as an index (the subset has no
/// closures).
pub fn find_ctor(ctors: &[ProjCtorRec], n: &Name) -> Option<usize> {
    let m = ctors.len();
    let mut i: usize = 0;
    while i < m {
        if name::beq(&ctors[i].name, n) {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// The cited `recs.find? (·.1 == T.str "rec")`, as an index.
pub fn find_rec(recs: &[ProjRecRec], n: &Name) -> Option<usize> {
    let m = recs.len();
    let mut i: usize = 0;
    while i < m {
        if name::beq(&recs[i].name, n) {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// The cited `types.filterMap`'s body on one type record: the officially
/// structure-like member (one constructor, zero indices, non-`Prop`) whose
/// recursor carries an elimination level parameter.
pub fn proj_rec_owner_at(
    t: &ProjTypeRec,
    ctors: &[ProjCtorRec],
    recs: &[ProjRecRec],
) -> Option<ProjRecOwner> {
    if t.ctors.len() != 1 {
        return None;
    }
    if t.n_i != 0 {
        return None;
    }
    let s = match expr_ops::strip_pis(t.n_p, &t.ty) {
        None => return None,
        Some(b) => match &b.1 .0.kind {
            ExprKind::Sort(s) => level::dup(s),
            _ => return None,
        },
    };
    match level::is_equiv(&s, &level::zero()) {
        Some(true) => return None,
        _ => {}
    }
    let ci = match find_ctor(ctors, &t.ctors[0]) {
        None => return None,
        Some(j) => j,
    };
    const REC: [u32; 3] = [114, 101, 99];
    let want_rec = name::mk_str(name::dup(&t.name), core_types::code_points(&REC));
    let ri = match find_rec(recs, &want_rec) {
        None => return None,
        Some(j) => j,
    };
    if recs[ri].lps.len() != t.lps.len() + 1 {
        return None;
    }
    Some(ProjRecOwner {
        t: name::dup(&t.name),
        lps: crate::kernel::prop_when::names_copy(&t.lps),
        n_p: t.n_p,
        ctor: name::dup(&t.ctors[0]),
        n_f: ctors[ci].n_f,
        rec_name: name::dup(&recs[ri].name),
        rec_lps: crate::kernel::prop_when::names_copy(&recs[ri].lps),
        rec_type: expr::dup(&recs[ri].ty),
        num_motives: recs[ri].n_m,
        num_minors: recs[ri].nm,
    })
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Which block members the rewrite serves: the officially structure-like ones
/// (one constructor, zero indices) of a block the direct install does not
/// recognise — `struct_parts_core` rejects it (mutual, multi-constructor,
/// indexed, shape mismatch) or it is recursive (the export's `isRec`, or a
/// block name occurring in a constructor's binder domains).  Propositional
/// owners and owners whose recursor carries no elimination level parameter
/// are left out.
pub fn proj_rec_owners(
    block: &Vec<ConstantInfo>,
    types: &[ProjTypeRec],
    ctors: &[ProjCtorRec],
    recs: &[ProjRecRec],
) -> Vec<ProjRecOwner> {
    let block_names = type_names(types);
    let recursive = any_is_rec(types) || any_ctor_mentions(&block_names, ctors);
    let direct = match struct_parts::struct_parts_core(block) {
        Some(_) => true,
        None => false,
    };
    if direct && !recursive {
        return Vec::new();
    }
    // a block the fixpoint route takes serves its structure-like member's
    // `.proj` nodes natively, so no rewrite (the block's DECLARED parameter
    // count: the first type record's)
    let n_pd = if types.len() == 0 { 0 } else { types[0].n_p };
    match native_parts::native_parts(n_pd, block) {
        Some(_) => return Vec::new(),
        None => {}
    }
    proj_rec_owners_go(types, ctors, recs)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// The cited `types.filterMap`, as the loop over the type records.
pub fn proj_rec_owners_go(
    types: &[ProjTypeRec],
    ctors: &[ProjCtorRec],
    recs: &[ProjRecRec],
) -> Vec<ProjRecOwner> {
    let n = types.len();
    let mut out: Vec<ProjRecOwner> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        match proj_rec_owner_at(&types[i], ctors, recs) {
            Some(o) => out.push(o),
            None => {}
        }
        i += 1;
    }
    out
}

/// con-leche: none — `env::to_constant_val(ci).name`, spelled here so
/// `export_c`'s owner registration reads like the Lean.
pub fn info_name(ci: &ConstantInfo) -> Name {
    env::constant_info_name(ci)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::basis_builder::{bn, cnst, pi, prop, srt, type1};

    fn nm(s: &str) -> Name {
        bn(s.chars().map(|c| c as u32).collect())
    }

    fn dotted(p: Name, s: &str) -> Name {
        name::mk_str(p, s.chars().map(|c| c as u32).collect())
    }

    /// The artifact name and its pre-filter.
    #[test]
    fn proj_iota_names() {
        let n = proj_iota_name(&nm("T"), 3);
        assert!(is_proj_iota_name(&n));
        assert!(!is_proj_iota_name(&nm("T")));
        assert!(!is_proj_iota_name(&dotted(nm("T"), "iota")));
        // `_model.notproj_0.iota` is not one
        let bad = dotted(dotted(dotted(nm("T"), "_model"), "notproj_0"), "iota");
        assert!(!is_proj_iota_name(&bad));
        // and neither is `_model.proj_0.other`
        let bad2 = dotted(dotted(dotted(nm("T"), "_model"), "proj_0"), "other");
        assert!(!is_proj_iota_name(&bad2));
    }

    /// The name is spelled out of code points, so it is the name con-leche's
    /// `s!"proj_{i}"` builds.
    #[test]
    fn the_artifact_name_is_spelled_out() {
        let n = proj_iota_name(&nm("T"), 12);
        let s: String = crate::frontend::text::name_str(&n)
            .iter()
            .filter_map(|c| char::from_u32(*c))
            .collect();
        assert_eq!(s, "T._model.proj_12.iota");
    }

    /// The `Eq` level of an artifact statement is the field's sort.
    #[test]
    fn the_iota_statement_names_the_field_sort() {
        let u = level::param(nm("u"));
        let mut args: Vec<Expr> = Vec::new();
        args.push(expr::mk_bvar(0));
        args.push(expr::mk_bvar(0));
        args.push(expr::mk_bvar(0));
        let stmt = pi(
            type1(),
            expr_ops::mk_app_n(cnst(bnm::eq_name(), one_level(&u)), &args),
        );
        match proj_iota_level(&stmt) {
            Some(l) => assert!(level::beq(&l, &u)),
            None => panic!("no level"),
        }
        // any other head is `None`
        assert!(proj_iota_level(&pi(type1(), cnst(nm("X"), Vec::new()))).is_none());
    }

    /// `occursConst`, memoised: a constant under a shared DAG is found, and a
    /// term that does not mention it answers `false` without revisiting.
    #[test]
    fn occurs_const_walks_a_dag() {
        let c = cnst(nm("C"), Vec::new());
        let shared = expr::app(cnst(nm("D"), Vec::new()), expr::dup(&c));
        let e = expr::app(expr::dup(&shared), expr::dup(&shared));
        assert!(occurs_const_fast(&nm("C"), &e));
        assert!(occurs_const_fast(&nm("D"), &e));
        assert!(!occurs_const_fast(&nm("E"), &e));
    }

    /// `stripPisAll`/`mkLams` round-trip a telescope, and `lamBody` reaches
    /// the node under every `λ`.
    #[test]
    fn telescope_helpers() {
        let t = pi(type1(), pi(prop(), expr::mk_bvar(0)));
        let (bs, body) = strip_pis_all(&t);
        assert_eq!(bs.len(), 2);
        let lams = mk_lams(&bs, expr::dup(&body));
        assert!(expr::beq(&lam_body(&lams), &body));
    }

    /// A one-constructor, index-free, non-`Prop`, non-recursive block whose
    /// direct install DOES serve it gets no owner; the same block made mutual
    /// (two type records) gets one.
    #[test]
    fn owner_census_skips_the_direct_shapes() {
        // `S (a : Type) : Type` with one constructor `S.mk (a : Type) (x : a)
        // : S a` and a recursor `S.rec.{u,?}`
        let s = nm("S");
        let mk = dotted(name::dup(&s), "mk");
        let rec = dotted(name::dup(&s), "rec");
        let ty_s = pi(type1(), type1());
        let ty_mk = pi(
            type1(),
            pi(
                expr::mk_bvar(0),
                expr::app(cnst(name::dup(&s), Vec::new()), expr::mk_bvar(1)),
            ),
        );
        let ty_rec = pi(type1(), srt(level::param(nm("u"))));
        let types = vec![ProjTypeRec {
            name: name::dup(&s),
            lps: Vec::new(),
            ty: expr::dup(&ty_s),
            n_p: 1,
            n_i: 0,
            ctors: vec![name::dup(&mk)],
            is_rec: false,
        }];
        let ctors = vec![ProjCtorRec {
            name: name::dup(&mk),
            n_f: 1,
            ty: expr::dup(&ty_mk),
        }];
        let recs = vec![ProjRecRec {
            name: name::dup(&rec),
            lps: vec![nm("u")],
            ty: expr::dup(&ty_rec),
            n_m: 1,
            nm: 1,
        }];
        // The block as `ConstantInfo`s, so `struct_parts_core`/`native_parts`
        // see something of the right length; whatever they answer, a
        // PROPOSITIONAL owner is never an owner, which is the clause this
        // asserts.
        let block: Vec<ConstantInfo> = Vec::new();
        let prop_types = vec![ProjTypeRec {
            name: name::dup(&s),
            lps: Vec::new(),
            ty: pi(type1(), prop()),
            n_p: 1,
            n_i: 0,
            ctors: vec![name::dup(&mk)],
            is_rec: false,
        }];
        assert!(proj_rec_owners(&block, &prop_types, &ctors, &recs).is_empty());
        // an indexed owner is never one either
        let idx_types = vec![ProjTypeRec {
            name: name::dup(&s),
            lps: Vec::new(),
            ty: expr::dup(&ty_s),
            n_p: 1,
            n_i: 1,
            ctors: vec![name::dup(&mk)],
            is_rec: false,
        }];
        assert!(proj_rec_owners(&block, &idx_types, &ctors, &recs).is_empty());
        // the well-shaped one IS an owner (the block is empty, so neither
        // recogniser claims it)
        let got = proj_rec_owners(&block, &types, &ctors, &recs);
        assert_eq!(got.len(), 1);
        assert!(name::beq(&got[0].t, &s));
        assert_eq!(got[0].n_f, 1);
    }
}

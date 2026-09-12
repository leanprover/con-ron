//! Port of `ConLeche/Kernel/PropWhen.lean` — the zero-ness datum of a
//! binder's codomain sort, in source order.
//!
//! **The representation is the Lean's, constructor for constructor.**  The
//! Lean module seals a five-constructor `private inductive PropWhenRepr`
//! (`never | always | one p | two p q (p < q) | many ps (Sorted ps ∧ 2 < |ps|)`)
//! inside a one-field `structure PropWhen` whose constructor and field are
//! `private`; this module does the same with a module-private
//! `enum PropWhenRepr` inside a `pub struct PropWhen` with a private field.
//! Rust's module privacy is exactly Lean's seal: outside `prop_when` the type
//! can be held and passed but not built or matched, so the smart constructor
//! is the only way in and the canonical-form invariant cannot be dodged.
//!
//! The alternative — a three-constructor `Never | Always | Params(Vec<Name>)`
//! carrying the sorted list — was rejected because it does not keep the
//! *operations* one-to-one, which is what DESIGN.md §3.1 asks for and what
//! the refinement proof spends its budget on.  Every operation here
//! (`holds`, `inter`, `params_defined`, `to_list`, `has_params`, `hash`,
//! `equiv_r`, `bind_z`) dispatches on the five constructors in the Lean's own
//! arm order, so each Rust arm refines one Lean arm by `rfl`.  Collapsing to
//! one list constructor turns each of those five-way matches into a
//! `List.all` / `merge` computation that is merely *provably* equal to the
//! Lean arm it stands for — roughly five lemmas per operation, some thirty in
//! all, bought for nothing.  It would also throw away what the constructors
//! are *for*: con-leche's census (the module doc at `PropWhen.lean:360`)
//! found 605 492 data with no parameter, 123 332 with one, 16 with two and
//! **none** longer, so `always`/`one`/`two` are 100 % of the real traffic and
//! they touch no list cell at all.  The proof-carrying fields (`p < q`,
//! `Sorted ps ∧ 2 < ps.length`) are erased in Rust, as every Lean proof field
//! is; they come back as the Lean-side well-formedness predicate that §3.5
//! already uses for `NameWF`/`NodeWF`, under which `to_list` is canonical and
//! `beq` is equality.
//!
//! Conventions, as in `name.rs` and `level.rs`: `Name`s are `P` trees taken
//! by shared reference and returned owned (`name::dup` for every share);
//! Lean's `List Name` is a `Vec<Name>` walked by an index (`*_from` helpers,
//! never a loop); a list that is *consumed* into a datum is passed by value
//! and a list that is *read* by reference (task #6's accumulator rule).
//!
//! `PropWhen` itself is **not** behind a handle: four of the five
//! constructors hold no heap cell beyond the names' own handles, and by the
//! census the fifth never occurs, so `dup` is a shallow value copy — which is
//! also what Lean's value semantics gives.
//!
//! Two of the Lean's arguments are *functions* (`holds`'s valuation
//! `φ : Name → Nat`, `bindZ`'s substitution `f : Name → PropWhen`).  §3.4
//! forbids closures, so each becomes a one-method trait the caller
//! implements — the `Eq2`/`Hashable` pattern of `hashmap.rs`, which task #7
//! measured against `core` traits and preferred.
//!
//! **Not ported** (recorded so the next task does not re-derive it):
//! `PropWhen.Sorted` (a `Prop`: the representation invariant, cited on
//! `PropWhenRepr` below and destined for the Lean-side `PropWhenWF`),
//! `casesZ` (`PropWhen.lean:643-660`, a dependent eliminator — proof
//! machinery, no executable content), `reprPrec'` and its `Repr` instance
//! (`:662-682`, rendering only; DESIGN.md §3.1 says message strings need not
//! match), the `Inhabited` instance (`:475`, Lean's `default`), and every
//! `theorem` — the whole law battery from `:992` on, which is the *spec*
//! this port will be proved against, not code.

use crate::ron::hashmap::Eq2;
use crate::ron::hashmap::Hashable;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::name::NameKind;

// ---------------------------------------------------------------------------
// A strict total order on names (`PropWhen.lean:56-187`)
// ---------------------------------------------------------------------------

/// con-leche: none — Lean's core `Ordering`, the result type of `Name.cmp`
/// Three-way comparison, as `nat::Cmp` is for bignums.  A separate type from
/// `nat::Cmp` because it is a separate Lean type, and the two never meet.
pub enum Ordering {
    Lt,
    Eq,
    Gt,
}

/// con-leche: none — Lean's core `Ordering.then`, used by `Name.cmp`
/// `Ordering.then`: the first comparison unless it is `eq`.
pub fn ord_then(a: Ordering, b: Ordering) -> Ordering {
    match a {
        Ordering::Eq => b,
        _ => a,
    }
}

/// con-leche: none — Lean's core `compare : String → String → Ordering`, used by `Name.cmp`
/// Lexicographic comparison of two strings.  Lean's `String.compare` is
/// `compareOfLessAndEq`, i.e. the lexicographic order of the code-point
/// lists (`Init/Data/Ord/String.lean:32`), so on the `Vec<u32>` of DESIGN.md
/// §3.3 it is this walk: first difference wins, a proper prefix is smaller.
pub fn str_compare(a: &Vec<u32>, b: &Vec<u32>) -> Ordering {
    str_compare_from(a, b, 0)
}

/// con-leche: none — the index recursion behind `str_compare`
/// No loops (DESIGN.md §3.4).
pub fn str_compare_from(a: &Vec<u32>, b: &Vec<u32>, i: usize) -> Ordering {
    if i >= a.len() && i >= b.len() {
        Ordering::Eq
    } else if i >= a.len() {
        Ordering::Lt
    } else if i >= b.len() {
        Ordering::Gt
    } else if a[i] < b[i] {
        Ordering::Lt
    } else if a[i] > b[i] {
        Ordering::Gt
    } else {
        str_compare_from(a, b, i + 1)
    }
}

/// con-leche: none — Lean's core `compare : Nat → Nat → Ordering`, used by `Name.cmp`
/// The `Name.num` payload is a `u64` (DESIGN.md §3.3), so this is the
/// machine comparison.
pub fn nat_compare(m: u64, n: u64) -> Ordering {
    if m < n {
        Ordering::Lt
    } else if m > n {
        Ordering::Gt
    } else {
        Ordering::Eq
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:75-85 Name.cmp
/// `Name.cmp`, the structural lexicographic order that makes the canonical
/// form canonical: constructor order `anonymous < str < num`, then the
/// prefix, then the payload.  The nine arms are the Lean's nine arms.
pub fn name_cmp(a: &Name, b: &Name) -> Ordering {
    match (&a.0.kind, &b.0.kind) {
        (NameKind::Anonymous, NameKind::Anonymous) => Ordering::Eq,
        (NameKind::Anonymous, NameKind::Str(_, _)) => Ordering::Lt,
        (NameKind::Anonymous, NameKind::Num(_, _)) => Ordering::Lt,
        (NameKind::Str(_, _), NameKind::Anonymous) => Ordering::Gt,
        (NameKind::Num(_, _), NameKind::Anonymous) => Ordering::Gt,
        (NameKind::Str(_, _), NameKind::Num(_, _)) => Ordering::Lt,
        (NameKind::Num(_, _), NameKind::Str(_, _)) => Ordering::Gt,
        (NameKind::Str(p, s), NameKind::Str(q, t)) => {
            ord_then(name_cmp(p, q), str_compare(s, t))
        }
        (NameKind::Num(p, m), NameKind::Num(q, n)) => {
            ord_then(name_cmp(p, q), nat_compare(*m, *n))
        }
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:87-88 _
/// The cited `instance : LT Name := ⟨fun a b => cmp a b = .lt⟩`, as a
/// decision procedure — the Lean's `Decidable (a < b)` instance
/// (`:90-91`) is `inferInstanceAs (Decidable (cmp a b = .lt))`, the same
/// test.  Nothing in the executed code calls it (the sorted layer compares
/// with `Name.cmp` directly); it is here because the representation
/// invariant is stated with it.
pub fn name_lt(a: &Name, b: &Name) -> bool {
    match name_cmp(a, b) {
        Ordering::Lt => true,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// The sorted-list layer (`PropWhen.lean:188-355`)
// ---------------------------------------------------------------------------

/// con-leche: none — the `List` tail copy behind `merge`'s `[], bs => bs` arm
/// Push `xs[k..]` onto `out`.  Lean *returns* the remaining list, which is
/// free under sharing; a `Vec` has to copy the tail (`name::dup` per cell,
/// so the names themselves are still shared).  The accumulator is passed by
/// value and returned, never by `&mut` (DESIGN.md §3.4, task #6).
pub fn append_from(xs: &Vec<Name>, k: usize, out: Vec<Name>) -> Vec<Name> {
    if k >= xs.len() {
        out
    } else {
        let mut o: Vec<Name> = out;
        o.push(name::dup(&xs[k]));
        append_from(xs, k + 1, o)
    }
}

/// con-leche: none — a copy of a whole name list, the `i = 0` case of `append_from`
/// Lean's sharing made explicit.
pub fn names_copy(xs: &Vec<Name>) -> Vec<Name> {
    append_from(xs, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:212-222 merge
/// `PropWhen.merge`, the ordered union of two sorted lists.
pub fn merge(as_: &Vec<Name>, bs: &Vec<Name>) -> Vec<Name> {
    merge_from(as_, 0, bs, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:212-222 merge
/// The index recursion the cited `List` recursion becomes: `i`/`j` are the
/// two cons positions and `out` the prefix already emitted, which is what
/// Lean builds by consing on the way out.
pub fn merge_from(
    as_: &Vec<Name>,
    i: usize,
    bs: &Vec<Name>,
    j: usize,
    out: Vec<Name>,
) -> Vec<Name> {
    if i >= as_.len() {
        append_from(bs, j, out)
    } else if j >= bs.len() {
        append_from(as_, i, out)
    } else {
        match name_cmp(&as_[i], &bs[j]) {
            Ordering::Lt => {
                let mut o: Vec<Name> = out;
                o.push(name::dup(&as_[i]));
                merge_from(as_, i + 1, bs, j, o)
            }
            Ordering::Eq => {
                let mut o: Vec<Name> = out;
                o.push(name::dup(&as_[i]));
                merge_from(as_, i + 1, bs, j + 1, o)
            }
            Ordering::Gt => {
                let mut o: Vec<Name> = out;
                o.push(name::dup(&bs[j]));
                merge_from(as_, i, bs, j + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:288-291 canon
/// `PropWhen.canon` — sort and deduplicate by folding the singletons in.
pub fn canon(ps: &Vec<Name>) -> Vec<Name> {
    canon_from(ps, 0)
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:288-291 canon
/// The index recursion the cited `List.foldr` becomes: a `foldr` is the
/// recursion that merges `ps[i]` into the canonical form of `ps[i+1..]`.
pub fn canon_from(ps: &Vec<Name>, i: usize) -> Vec<Name> {
    if i >= ps.len() {
        Vec::new()
    } else {
        let rest: Vec<Name> = canon_from(ps, i + 1);
        merge(&name::singleton(&ps[i]), &rest)
    }
}

// ---------------------------------------------------------------------------
// The sealed representation (`PropWhen.lean:360-415`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/PropWhen.lean:360-384 PropWhenRepr
/// con-leche: ConLeche/Kernel/PropWhen.lean:201-202 PropWhen.Sorted
/// The five constructors of the cited `private inductive`.  Deviation: the
/// invariants the Lean constructors carry as proof fields — `two` requires
/// `p < q`, `many` requires the cited `Sorted ps` and `2 < ps.length` — are
/// erased, as every Lean proof field is under Charon; they come back as the
/// Lean-side well-formedness predicate (DESIGN.md §3.5), under which
/// `to_list` is the canonical representative of the parameter *set* and
/// `beq` is equality.  Module-private, which is Rust's spelling of the
/// cited `private`: nothing outside this file can build or match one.
enum PropWhenRepr {
    Never,
    Always,
    One(Name),
    Two(Name, Name),
    Many(Vec<Name>),
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:386-415 PropWhen
/// The zero-ness datum: for a level `l`, the set `Z(l) = {φ | eval φ l = 0}`
/// of zeroing valuations, which is either empty (`never`) or "every
/// parameter in `ps` is zero" (`if_all_zero ps`).  The field is private, so
/// the type is opaque outside this module exactly as the cited `structure`
/// with its `private ofRepr ::` constructor is opaque outside `PropWhen.lean`.
pub struct PropWhen {
    repr: PropWhenRepr,
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:386-415 PropWhen
/// The cited `private ofRepr ::` constructor.
fn of_repr(r: PropWhenRepr) -> PropWhen {
    PropWhen { repr: r }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
/// Share a datum.  Shallow: the names are handles, and only the `Many` arm —
/// which the census says never occurs — copies a list spine.
pub fn dup(pw: &PropWhen) -> PropWhen {
    match &pw.repr {
        PropWhenRepr::Never => of_repr(PropWhenRepr::Never),
        PropWhenRepr::Always => of_repr(PropWhenRepr::Always),
        PropWhenRepr::One(p) => of_repr(PropWhenRepr::One(name::dup(p))),
        PropWhenRepr::Two(p, q) => {
            of_repr(PropWhenRepr::Two(name::dup(p), name::dup(q)))
        }
        PropWhenRepr::Many(ps) => of_repr(PropWhenRepr::Many(names_copy(ps))),
    }
}

// ---------------------------------------------------------------------------
// The comparison and the hash (`PropWhen.lean:426-461`)
// ---------------------------------------------------------------------------

/// con-leche: none — `List Name` equality, the `ps == qs` of `equivR`'s `many` arm
/// The index recursion Lean's `List.beq` becomes; a length mismatch is
/// `false`, as in `Level.isEquivList`.
pub fn names_beq_from(ps: &Vec<Name>, qs: &Vec<Name>, i: usize) -> bool {
    if i >= ps.len() && i >= qs.len() {
        true
    } else if i >= ps.len() || i >= qs.len() {
        false
    } else if name::beq(&ps[i], &qs[i]) {
        names_beq_from(ps, qs, i + 1)
    } else {
        false
    }
}

/// con-leche: none — `List Name` equality, the entry point of the recursion above
/// Lean writes `ps == qs`.
pub fn names_beq(ps: &Vec<Name>, qs: &Vec<Name>) -> bool {
    names_beq_from(ps, qs, 0)
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:437-444 PropWhen.equivR
/// `PropWhen.equivR`: structural equality spelled constructor-wise, so that
/// the name comparisons go through `Name.beq` (the pointer- and
/// hash-guarded one) rather than a derived structural walk.
fn equiv_r(x: &PropWhenRepr, y: &PropWhenRepr) -> bool {
    match (x, y) {
        (PropWhenRepr::Never, PropWhenRepr::Never) => true,
        (PropWhenRepr::Always, PropWhenRepr::Always) => true,
        (PropWhenRepr::One(a), PropWhenRepr::One(b)) => name::beq(a, b),
        (PropWhenRepr::Two(a, b), PropWhenRepr::Two(c, d)) => {
            name::beq(a, c) && name::beq(b, d)
        }
        (PropWhenRepr::Many(ps), PropWhenRepr::Many(qs)) => names_beq(ps, qs),
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:449-453 PropWhen.decEq
/// con-leche: ConLeche/Kernel/PropWhen.lean:455 _
/// `PropWhen.decEq` and the `DecidableEq` instance it feeds.  By canonicity
/// this *is* zero-ness agreement at every valuation (`eq_iff_holds`), which
/// is why the checker compares data with `==` and no separate equivalence
/// test exists.
pub fn beq(a: &PropWhen, b: &PropWhen) -> bool {
    equiv_r(&a.repr, &b.repr)
}

/// con-leche: none — Lean's core `Hashable (List α)` instance (`Init/Data/Hashable.lean:37`)
/// `as.foldl (fun r a => mixHash r (hash a)) 7`, as an index recursion.
pub fn names_hash_from(ps: &Vec<Name>, i: usize, acc: u64) -> u64 {
    if i >= ps.len() {
        acc
    } else {
        names_hash_from(ps, i + 1, name::mix_hash(acc, name::hash_data(&ps[i])))
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:360-384 PropWhenRepr
/// The cited inductive's `deriving Hashable`: the constructor index, then
/// `mixHash` folded over the fields (`Lean/Elab/Deriving/Hashable.lean:50`).
/// Deviation: the derived instance also folds the *erased proof* fields
/// (`h : p < q`, `h : Sorted ps ∧ …`), which do not exist here.  Hash values
/// are a free choice anyway (DESIGN.md §3.2: `mixHash` is opaque in the
/// proofs, hashes only move memo entries between buckets, and our string
/// hash already differs), so ours folds the data only — what it must be is
/// a function of the value, which canonicity makes a function of the set.
fn hash_repr(r: &PropWhenRepr) -> u64 {
    match r {
        PropWhenRepr::Never => 0,
        PropWhenRepr::Always => 1,
        PropWhenRepr::One(p) => name::mix_hash(2, name::hash_data(p)),
        PropWhenRepr::Two(p, q) => name::mix_hash(
            name::mix_hash(3, name::hash_data(p)),
            name::hash_data(q),
        ),
        PropWhenRepr::Many(ps) => name::mix_hash(4, names_hash_from(ps, 0, 7)),
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:457-459 PropWhen.hash'
/// con-leche: ConLeche/Kernel/PropWhen.lean:461 _
/// `PropWhen.hash'` and the `Hashable` instance it feeds — a hash of the
/// parameter *set*, by canonicity.
pub fn hash_pw(pw: &PropWhen) -> u64 {
    hash_repr(&pw.repr)
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:461 _
/// The cited `instance : Hashable PropWhen := ⟨hash'⟩`, as the key
/// dictionary of `crate::ron::hashmap` (task #7).
impl Hashable for PropWhen {
    /// con-leche: ConLeche/Kernel/PropWhen.lean:457-459 PropWhen.hash'
    /// `hash'`.
    fn hash64(&self) -> u64 {
        hash_pw(self)
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:455 _
/// The cited `instance : DecidableEq PropWhen := decEq`, as the key
/// dictionary of `crate::ron::hashmap` (task #7).
impl Eq2 for PropWhen {
    /// con-leche: ConLeche/Kernel/PropWhen.lean:449-453 PropWhen.decEq
    /// `decEq`.
    fn eq2(&self, other: &Self) -> bool {
        beq(self, other)
    }
}

// ---------------------------------------------------------------------------
// The encapsulation boundary (`PropWhen.lean:463-525`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/PropWhen.lean:470-473 PropWhen.never
/// "The codomain sort is nonzero at every valuation."
pub fn never() -> PropWhen {
    of_repr(PropWhenRepr::Never)
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:480-487 PropWhen.ofSorted
/// `PropWhen.ofSorted`: the datum of an *already sorted* list — the
/// dedicated small constructors up to length 2, the list chain above.
/// Deviations: the sortedness proof is erased (see `PropWhenRepr`), so the
/// caller owes it; and the list is taken **by value**, so the `many` arm
/// moves it instead of re-consing (the `[p]`/`[p, q]` arms copy the one or
/// two names out, which is what Lean's pattern match does for free).
fn of_sorted(ps: Vec<Name>) -> PropWhen {
    if ps.len() == 0 {
        of_repr(PropWhenRepr::Always)
    } else if ps.len() == 1 {
        of_repr(PropWhenRepr::One(name::dup(&ps[0])))
    } else if ps.len() == 2 {
        of_repr(PropWhenRepr::Two(name::dup(&ps[0]), name::dup(&ps[1])))
    } else {
        of_repr(PropWhenRepr::Many(ps))
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:489-495 PropWhen.two'
/// `PropWhen.two'`: the two-name datum from two arbitrary names — one
/// comparison, no list cell.  (Lean's `'` has no Rust spelling; the name is
/// `two_prime`.)
fn two_prime(p: &Name, q: &Name) -> PropWhen {
    match name_cmp(p, q) {
        Ordering::Lt => of_repr(PropWhenRepr::Two(name::dup(p), name::dup(q))),
        Ordering::Eq => of_repr(PropWhenRepr::One(name::dup(p))),
        Ordering::Gt => of_repr(PropWhenRepr::Two(name::dup(q), name::dup(p))),
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:497-507 PropWhen.ifAllZero
/// **The smart constructor**: "every parameter in `ps` is zero", normalised
/// to the canonical representative of the *set* of `ps`.  The empty and
/// singleton cases touch no list cell and no comparison, the pair case is
/// one comparison, and only length ≥ 3 runs the sort.  Deviation: the list
/// arrives by value, and the length dispatch is an `if` chain rather than
/// list patterns Rust cannot write over a `Vec`.
pub fn if_all_zero(ps: Vec<Name>) -> PropWhen {
    if ps.len() == 0 {
        of_repr(PropWhenRepr::Always)
    } else if ps.len() == 1 {
        of_repr(PropWhenRepr::One(name::dup(&ps[0])))
    } else if ps.len() == 2 {
        two_prime(&ps[0], &ps[1])
    } else {
        of_sorted(canon(&ps))
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:509-518 PropWhen.toList
/// The parameter list of a datum — sorted and duplicate-free; `never` reads
/// as `[]` (use `to_list_opt` where the distinction matters).  Deviation:
/// the result is an owned copy, since the `many` arm cannot hand out the
/// list it holds.
pub fn to_list(pw: &PropWhen) -> Vec<Name> {
    match &pw.repr {
        PropWhenRepr::Never => Vec::new(),
        PropWhenRepr::Always => Vec::new(),
        PropWhenRepr::One(p) => name::singleton(p),
        PropWhenRepr::Two(p, q) => {
            let mut v: Vec<Name> = Vec::new();
            v.push(name::dup(p));
            v.push(name::dup(q));
            v
        }
        PropWhenRepr::Many(ps) => names_copy(ps),
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:520-525 PropWhen.toList?
/// `toList?` — the view that inverts `if_all_zero`: `None` at `never`.
pub fn to_list_opt(pw: &PropWhen) -> Option<Vec<Name>> {
    match &pw.repr {
        PropWhenRepr::Never => None,
        _ => Some(to_list(pw)),
    }
}

// ---------------------------------------------------------------------------
// The observers (`PropWhen.lean:684-799`)
// ---------------------------------------------------------------------------

/// con-leche: none — Lean's `φ : Name → Nat` argument of `holds`; §3.4 forbids closures
/// A valuation of the level parameters.  Level-parameter values are `u64`
/// (DESIGN.md §3.3: the `Nat`s that are never large).
pub trait Valuation {
    /// con-leche: none — the application `φ n` of `holds`'s valuation
    /// The value of a parameter under this valuation.
    fn value_at(&self, n: &Name) -> u64;
}

/// con-leche: none — the `ps.all fun n => φ n == 0` of `holds`'s `many` arm
/// The index recursion the cited `List.all` becomes.
pub fn all_zero_from<V>(phi: &V, ps: &Vec<Name>, i: usize) -> bool
where
    V: Valuation,
{
    if i >= ps.len() {
        true
    } else if phi.value_at(&ps[i]) == 0 {
        all_zero_from(phi, ps, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:691-700 PropWhen.holds
/// Does the datum hold at a valuation — is the codomain sort zero there?
/// (The model side's dispatch bit; the kernel never evaluates this, it only
/// compares data with `==`.)  Deviation: the valuation is a trait
/// dictionary, not a closure.
pub fn holds<V>(phi: &V, pw: &PropWhen) -> bool
where
    V: Valuation,
{
    match &pw.repr {
        PropWhenRepr::Never => false,
        PropWhenRepr::Always => true,
        PropWhenRepr::One(p) => phi.value_at(p) == 0,
        PropWhenRepr::Two(p, q) => phi.value_at(p) == 0 && phi.value_at(q) == 0,
        PropWhenRepr::Many(ps) => all_zero_from(phi, ps, 0),
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:716-738 PropWhen.isNever
/// Is the datum `never`?  The only kernel-decidable reading of the
/// annotation that the verification tier licenses a check-skip on, and only
/// under `μ.verifiedChecks` — see the cited doc comment.
pub fn is_never(pw: &PropWhen) -> bool {
    match &pw.repr {
        PropWhenRepr::Never => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:751-759 PropWhen.hasParams
/// Does the datum mention any level parameter — is `Level.substPW` ever
/// non-trivial on it?  Folded into `Expr.hasLevelParam`.
pub fn has_params(pw: &PropWhen) -> bool {
    match &pw.repr {
        PropWhenRepr::Never => false,
        PropWhenRepr::Always => false,
        _ => true,
    }
}

/// con-leche: none — the `ps.all params.contains` of `paramsDefined`'s `many` arm
/// The index recursion the cited `List.all` becomes.
pub fn all_contained_from(params: &Vec<Name>, ps: &Vec<Name>, i: usize) -> bool {
    if i >= ps.len() {
        true
    } else if name::contains(params, &ps[i]) {
        all_contained_from(params, ps, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:778-789 PropWhen.paramsDefined
/// Are all parameters of the datum among `params`?  Folded into
/// `Expr.allLevelParamsDefined`: level instantiation's composition law is
/// false for data whose parameters escape the declaration's.
pub fn params_defined(params: &Vec<Name>, pw: &PropWhen) -> bool {
    match &pw.repr {
        PropWhenRepr::Never => true,
        PropWhenRepr::Always => true,
        PropWhenRepr::One(p) => name::contains(params, p),
        PropWhenRepr::Two(p, q) => {
            name::contains(params, p) && name::contains(params, q)
        }
        PropWhenRepr::Many(ps) => all_contained_from(params, ps, 0),
    }
}

// ---------------------------------------------------------------------------
// The producers (`PropWhen.lean:861-955`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/PropWhen.lean:861-874 PropWhen.inter
/// Intersection of two zero-ness predicates (the `max` rule: a `max` is zero
/// iff both sides are): `never` absorbs, sets unite through the ordered
/// merge, so the output is canonical.  The `always`/singleton arms answer
/// without touching a list cell — 99.99 % of the calls, by the census.
pub fn inter(a: &PropWhen, b: &PropWhen) -> PropWhen {
    match (&a.repr, &b.repr) {
        (PropWhenRepr::Never, _) => never(),
        (_, PropWhenRepr::Never) => never(),
        (PropWhenRepr::Always, _) => dup(b),
        (_, PropWhenRepr::Always) => dup(a),
        (PropWhenRepr::One(x), PropWhenRepr::One(y)) => two_prime(x, y),
        _ => of_sorted(merge(&to_list(a), &to_list(b))),
    }
}

/// con-leche: none — Lean's `f : Name → PropWhen` argument of `bindZ`; §3.4 forbids closures
/// A substitution of data for parameters.  `Level.substPW` (not ported yet —
/// `Kernel/Level.lean:205`) is the one implementation the checker needs.
pub trait NameToPw {
    /// con-leche: none — the application `f n` of `bindZ`'s substitution
    /// The datum this substitution puts for a parameter.
    fn apply(&self, n: &Name) -> PropWhen;
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:938-941 PropWhen.bindZ.go
/// The index recursion the cited `List` fold becomes.
pub fn bind_z_go_from<F>(f: &F, ps: &Vec<Name>, i: usize) -> PropWhen
where
    F: NameToPw,
{
    if i >= ps.len() {
        if_all_zero(Vec::new())
    } else {
        inter(&f.apply(&ps[i]), &bind_z_go_from(f, ps, i + 1))
    }
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:938-941 PropWhen.bindZ.go
/// `bindZ.go`, the list-level fold; the `i = 0` wrapper of the recursion
/// above.
pub fn bind_z_go<F>(f: &F, ps: &Vec<Name>) -> PropWhen
where
    F: NameToPw,
{
    bind_z_go_from(f, ps, 0)
}

/// con-leche: ConLeche/Kernel/PropWhen.lean:943-955 PropWhen.bindZ
/// Substitute each parameter of the datum by a whole datum and intersect
/// ("all of `ps` zero" becomes "all replacements zero") — the monadic bind
/// of the zero-ness reading.  Canonical on output because `inter` is.
pub fn bind_z<F>(f: &F, pw: &PropWhen) -> PropWhen
where
    F: NameToPw,
{
    match &pw.repr {
        PropWhenRepr::Never => never(),
        PropWhenRepr::Always => if_all_zero(Vec::new()),
        PropWhenRepr::One(p) => f.apply(p),
        PropWhenRepr::Two(p, q) => inter(&f.apply(p), &f.apply(q)),
        PropWhenRepr::Many(ps) => bind_z_go(f, ps),
    }
}

#[cfg(test)]
mod tests {
    use crate::ron::hashmap::Eq2;
    use crate::ron::hashmap::Hashable;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::kernel::prop_when::{
        beq, bind_z, bind_z_go, canon, dup, has_params, hash_pw, holds, if_all_zero, inter,
        is_never, name_cmp, name_lt, names_beq, never, params_defined, to_list, to_list_opt,
        NameToPw, Ordering, PropWhen, Valuation,
    };

    fn nm(s: &str) -> Name {
        let cs: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cs)
    }

    fn names(ss: &[&str]) -> Vec<Name> {
        ss.iter().map(|s| nm(s)).collect()
    }

    fn pw(ss: &[&str]) -> PropWhen {
        if_all_zero(names(ss))
    }

    fn shown(p: &PropWhen) -> Vec<String> {
        to_list(p)
            .iter()
            .map(|n| match &n.0.kind {
                name::NameKind::Str(_, s) => {
                    s.iter().map(|c| char::from_u32(*c).unwrap()).collect()
                }
                _ => String::from("?"),
            })
            .collect()
    }

    /// The valuation `φ n = if n ∈ zeros then 0 else 1`.
    struct Phi {
        zeros: Vec<Name>,
    }

    impl Valuation for Phi {
        fn value_at(&self, n: &Name) -> u64 {
            if name::contains(&self.zeros, n) {
                0
            } else {
                1
            }
        }
    }

    /// The unit substitution `n ↦ ifAllZero [n]` of `bindZ_unit`.
    struct Unit;

    impl NameToPw for Unit {
        fn apply(&self, n: &Name) -> PropWhen {
            if_all_zero(name::singleton(n))
        }
    }

    /// `n ↦ ifAllZero (table n)`: every name is replaced by two others.
    struct Split;

    impl NameToPw for Split {
        fn apply(&self, n: &Name) -> PropWhen {
            let mut v: Vec<Name> = Vec::new();
            v.push(nm("a"));
            v.push(name::dup(n));
            if_all_zero(v)
        }
    }

    /// The every-name-to-`never` substitution.
    struct ToNever;

    impl NameToPw for ToNever {
        fn apply(&self, _n: &Name) -> PropWhen {
            never()
        }
    }

    /// `Name.cmp` is a strict total order: irreflexive, asymmetric,
    /// transitive and trichotomous (`PropWhen.lean:159-186`).
    #[test]
    fn name_cmp_is_a_strict_total_order() {
        let ns: Vec<Name> = {
            let mut v: Vec<Name> = Vec::new();
            v.push(name::anonymous());
            v.push(nm("a"));
            v.push(nm("b"));
            v.push(nm("ab"));
            v.push(name::mk_num(name::anonymous(), 1));
            v.push(name::mk_num(name::anonymous(), 2));
            v.push(name::mk_str(nm("a"), "b".chars().map(|c| c as u32).collect()));
            v
        };
        for a in ns.iter() {
            assert!(matches!(name_cmp(a, a), Ordering::Eq));
            assert!(!name_lt(a, a));
            for b in ns.iter() {
                // trichotomy, and `cmp a b = (cmp b a).swap`
                let ab = matches!(name_cmp(a, b), Ordering::Lt);
                let ba = matches!(name_cmp(b, a), Ordering::Lt);
                let eq = matches!(name_cmp(a, b), Ordering::Eq);
                assert_eq!(eq, name::beq(a, b));
                assert!(ab as u8 + ba as u8 + eq as u8 == 1);
                for c in ns.iter() {
                    if name_lt(a, b) && name_lt(b, c) {
                        assert!(name_lt(a, c));
                    }
                }
            }
        }
        // constructor order `anonymous < str < num`, then prefix, then payload
        assert!(name_lt(&name::anonymous(), &nm("a")));
        assert!(name_lt(&nm("zzz"), &name::mk_num(name::anonymous(), 0)));
        assert!(name_lt(&nm("a"), &nm("ab")));
        assert!(name_lt(&nm("ab"), &nm("b")));
    }

    /// `canon` sorts, deduplicates and is idempotent (`canon_canon`), and
    /// `toList` of a datum is what `canon` of its input is
    /// (`toList_ifAllZero`).
    #[test]
    fn canon_sorts_dedups_and_is_idempotent() {
        let raw = names(&["c", "a", "b", "a", "c"]);
        let c1 = canon(&raw);
        assert_eq!(shown(&if_all_zero(names(&["c", "a", "b", "a", "c"]))), ["a", "b", "c"]);
        assert!(names_beq(&c1, &canon(&c1)));
        assert_eq!(c1.len(), 3);
        // the small cases go through the dedicated constructors, and still
        // come out canonical
        assert_eq!(shown(&pw(&["b", "a"])), ["a", "b"]);
        assert_eq!(shown(&pw(&["a", "a"])), ["a"]);
        assert!(to_list(&never()).is_empty());
        assert!(to_list_opt(&never()).is_none());
        assert!(to_list_opt(&pw(&[])).is_some());
    }

    /// Canonicity: `ifAllZero ps = ifAllZero qs ↔ (∀ n, n ∈ ps ↔ n ∈ qs)`
    /// (`ifAllZero_eq_iff`), and the hash follows the value
    /// (`Hashable` on the canonical representation).
    #[test]
    fn equal_sets_are_equal_data() {
        let a = pw(&["a", "b", "c"]);
        let b = pw(&["c", "b", "a", "b"]);
        assert!(beq(&a, &b));
        assert!(a.eq2(&b));
        assert_eq!(hash_pw(&a), hash_pw(&b));
        assert_eq!(a.hash64(), b.hash64());
        assert!(!beq(&a, &pw(&["a", "b"])));
        assert!(!beq(&never(), &pw(&[])));
        assert!(beq(&never(), &never()));
        assert!(beq(&dup(&a), &a));
        // the pair case is `two'`, the ≥3 case the sorted chain
        assert!(beq(&pw(&["b", "a"]), &pw(&["a", "b"])));
    }

    /// `holds_never`, `holds_ifAllZero` and `isNever`/`hasParams`
    /// (`PropWhen.lean:702-780`).
    #[test]
    fn holds_reads_the_parameter_set() {
        let phi = Phi { zeros: names(&["a", "b"]) };
        assert!(!holds(&phi, &never()));
        assert!(holds(&phi, &pw(&[])));
        assert!(holds(&phi, &pw(&["a"])));
        assert!(holds(&phi, &pw(&["a", "b"])));
        assert!(!holds(&phi, &pw(&["a", "c"])));
        assert!(!holds(&phi, &pw(&["a", "b", "c"])));
        assert!(holds(&phi, &pw(&["b", "a", "a"])));

        assert!(is_never(&never()));
        assert!(!is_never(&pw(&[])));
        assert!(!has_params(&never()));
        assert!(!has_params(&pw(&[])));
        assert!(has_params(&pw(&["a"])));
        assert!(has_params(&pw(&["a", "b", "c"])));
    }

    /// `holds_inter`, `inter_comm`, `inter_self`, `inter_assoc`,
    /// `inter_nil`/`nil_inter`, `inter_never_left`/`_right`
    /// (`PropWhen.lean:876-1047`).
    #[test]
    fn inter_is_the_set_union_and_the_holds_conjunction() {
        let phi = Phi { zeros: names(&["a", "b"]) };
        let cases: Vec<PropWhen> = {
            let mut v: Vec<PropWhen> = Vec::new();
            v.push(never());
            v.push(pw(&[]));
            v.push(pw(&["a"]));
            v.push(pw(&["b"]));
            v.push(pw(&["a", "b"]));
            v.push(pw(&["c", "a"]));
            v.push(pw(&["a", "b", "c"]));
            v
        };
        for p in cases.iter() {
            for q in cases.iter() {
                let pq = inter(p, q);
                // holds_inter
                assert_eq!(holds(&phi, &pq), holds(&phi, p) && holds(&phi, q));
                // inter_comm
                assert!(beq(&pq, &inter(q, p)));
                // never absorbs
                assert_eq!(is_never(&pq), is_never(p) || is_never(q));
                for r in cases.iter() {
                    // inter_assoc
                    assert!(beq(&inter(&pq, r), &inter(p, &inter(q, r))));
                }
            }
            // inter_self, inter_nil, nil_inter
            assert!(beq(&inter(p, p), p));
            assert!(beq(&inter(p, &pw(&[])), p));
            assert!(beq(&inter(&pw(&[]), p), p));
            assert!(beq(&inter(p, &never()), &never()));
            assert!(beq(&inter(&never(), p), &never()));
        }
        // `inter_ifAllZero`: the lists append (and normalise)
        assert!(beq(&inter(&pw(&["b"]), &pw(&["a"])), &pw(&["a", "b"])));
        assert_eq!(shown(&inter(&pw(&["c", "a"]), &pw(&["b", "a"]))), ["a", "b", "c"]);
    }

    /// `paramsDefined_inter_of` and the `never`/`ifAllZero` equations
    /// (`PropWhen.lean:796-1013`).
    #[test]
    fn params_defined_is_stable_under_inter() {
        let params = names(&["a", "b"]);
        assert!(params_defined(&params, &never()));
        assert!(params_defined(&params, &pw(&[])));
        assert!(params_defined(&params, &pw(&["a"])));
        assert!(params_defined(&params, &pw(&["a", "b"])));
        assert!(!params_defined(&params, &pw(&["a", "c"])));
        assert!(!params_defined(&params, &pw(&["a", "b", "c"])));
        let p = pw(&["a"]);
        let q = pw(&["b"]);
        assert!(params_defined(&params, &inter(&p, &q)));
    }

    /// `bindZ_never`, `bindZ_ifAllZero`, `bindZ_unit` and `bindZ_inter`
    /// (`PropWhen.lean:957-1064`).
    #[test]
    fn bind_z_substitutes_and_respects_inter() {
        let cases: Vec<PropWhen> = {
            let mut v: Vec<PropWhen> = Vec::new();
            v.push(never());
            v.push(pw(&[]));
            v.push(pw(&["a"]));
            v.push(pw(&["b", "c"]));
            v.push(pw(&["a", "b", "c"]));
            v
        };
        for p in cases.iter() {
            // bindZ_unit: `n ↦ ifAllZero [n]` reproduces the datum
            assert!(beq(&bind_z(&Unit, p), p));
            // bindZ_never / bindZ at never
            assert_eq!(is_never(&bind_z(&Split, p)), is_never(p));
            for q in cases.iter() {
                // bindZ_inter
                assert!(beq(
                    &bind_z(&Split, &inter(p, q)),
                    &inter(&bind_z(&Split, p), &bind_z(&Split, q))
                ));
            }
        }
        // the substitution really substitutes, and normalises the union
        assert_eq!(shown(&bind_z(&Split, &pw(&["b", "c"]))), ["a", "b", "c"]);
        // a parameter mapped to `never` makes the whole datum `never` —
        // except at `never`/`always`, which have no parameter to map
        assert!(is_never(&bind_z(&ToNever, &pw(&["a"]))));
        assert!(!is_never(&bind_z(&ToNever, &pw(&[]))));
        // bindZ_go_append: the fold splits over an append
        let ps = names(&["a", "b"]);
        let qs = names(&["c"]);
        let both = names(&["a", "b", "c"]);
        assert!(beq(
            &bind_z_go(&Split, &both),
            &inter(&bind_z_go(&Split, &ps), &bind_z_go(&Split, &qs))
        ));
    }
}

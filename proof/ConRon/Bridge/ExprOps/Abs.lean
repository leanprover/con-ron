/-
# `ConRon.Bridge.ExprOps.Abs` — Theorem 1 for the ABSTRACTION family

DESIGN §8.2's Theorem 1 at the five twins of `Arena/ExprOps.lean` that close
free variables into bound ones: `abstractRange` (the SPEC descent, `:669`),
`abstract1Go` / `abstract1Fast` (`:1520`, `:1585`) and `abstractRangeGo` /
`abstractRangeFast` (`:1616`, `:1686`).

Written against `ExprOps/Inst1.lean`, the tier's exemplar: the same `…Spec`
record for one level of the recursion and the same fuel induction; the arms
are closed by `grind` (see *The closer* below), with no per-arm step
lemmas.

## The three deviations this family carries

1. **`abstractRange` is the SPEC and `abstractRangeGo` is the EXECUTED form**
   (task #97-P6-11, `Arena/ExprOps.lean`'s own note).  `abstractRange` is
   kept as the statement subject, so `abstractRangeGo`'s theorem is stated
   against con-leche's `Expr.abstractRange` too and the executed form's three
   devices are the deviations: the `fvarB ≤ d` cutoff at the node
   (licence: `abstractRange_of_fvarRange_le` below, which is con-leche's
   `abstractRange_eq_self`, `ConLeche/Verify/AbstractRange.lean:61`, at
   `fvarRange` instead of `fvarsBelow`), the per-call memo keyed by
   `(node, cursor)` and shared with `abstract1` (see 3), and — at the entry
   only — the `k = 0` identity, whose licence is `abstractRange_zero_eq`
   below (con-leche's `abstractRange_zero`, `:23`).  `abstractRange … d 1 c`
   is `abstract1 … d c` by con-leche's `abstractRange_succ` (`:32`) composed
   with `abstractRange_zero`; `ExprOpsTest.lean`'s guards check both.
2. **The upward `internRebuilt` cutoff** (task #97-P6-5) at every rebuilding
   arm of the two executed walks.  `Bridge/Specs.lean`'s `internRebuilt*_spec`
   family discharges it; `Bridge/Rel.lean`'s `denoteEView_ext` is what makes
   the `same = true` branch's conclusion the other branch's.  The SPEC descent
   `abstractRange` has no cutoff and interns unconditionally.
3. **The two executed walks share one memo table** (`abs1C`).
   `Arena/ExprOps.lean`: "The two walks never nest … That is a table
   IDENTITY, not a clause."  `Bridge/StateOK.lean`'s `Abs1MemoA d` is the
   `abstract1` reading of that table and `AbsRangeMemoA d k` below is the
   `abstractRange` reading; the two are never in scope at once, and
   `abs1Set_specA` — the memo insert's spec with the pure function a
   parameter — is what lets one primitive serve both.

## What this module ASSUMES: `fvarB`

Both executed walks begin with `fvarB fuel h`, the memoised exact fvar range
(`Arena/ExprOps.lean:1489`).  That twin is another group's Theorem 1, so its
statement arrives here as the hypothesis `FvarBSpec` — the record below,
which is exactly the shape group A's `fvarB` theorem will have (`RelV
Expr.fvarRange` plus the frame `abs1C` needs).  When that theorem lands, the
hypothesis is discharged once at each `…Fast` entry and nothing else in this
file changes.

## `abstract1Go` is proved ONE THEOREM PER ARM

DESIGN §8.6's arm-split ruling (coordinator, 2026-09-22) and task #97-P3-2:
`abstract1Go` is a `mutual` block — a dispatcher and one `def` per
constructor arm — and the proof follows it exactly, the way
`ExprOps/Inst1.lean` does for `instantiate1Go`.  The five arm theorems take
the previous fuel level's `Abs1Spec` as their induction hypothesis and their
own TAG as a hypothesis (`EStore.viewApp` does not test the tag), and the
dispatcher's `vcgen` list is the five of them.  `vcgen` (task #111)
instantiates an arm spec at the state `fvarB` returned and leaves the arm's
preconditions at that state as verification conditions.

## The closer

Every proof is `sym only [bridge_grind] => vcgen [...] <;> finish`.  What
`grind` needs is equations, never a `fun`:

* the pure functions are NAMED (`abs1Fn d k`, `absRangeFn d k c`), so the
  answer relation `RelE (abs1Fn d k)` and the memo invariant
  `MemoOK (abs1Fn d)` carry no lambda; one `=` lemma per constructor the
  walk descends into (`abs1Fn_app`, …), and the cutoff and the catch-all as
  two lemmas the DISPATCHER passes to `sym` (`abs1Fn_cutoff`,
  `abs1Fn_leaf`);
* the view a tag-guarded projection read gives, the denotation's
  constructor from its tag and the children's denotations are
  `Bridge/Grind.lean` §6's (`view_of_viewApp`, `exprTag_app`, the
  `DenoteView` extractions);
* the memo insert is `abs1Set_specA`, the insert's spec with the walk's
  function a parameter (given in the `vcgen` list) and the invariant and
  the answer as PRECONDITIONS, so that its post is a plain conjunction.

-/
import ConRon.Bridge.ExprOps.MemoSpecs

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

/-! ## The pure licences

Two pure facts about con-leche's `abstractRange`, which con-leche states in
`Verify/` against `fvarsBelow` rather than against `fvarRange`.  They are
re-proved here at the field the arena READS, so that this tier imports
`ConLeche.Kernel.*` only.  (`abstract1`'s, `Expr.abstract1_of_fvarRange_le`,
con-leche has at `fvarRange` already.) -/

/-- con-leche: ConLeche/Verify/AbstractRange.lean:61 abstractRange_eq_self —
**the fvar-range cutoff's licence**: abstracting a range at or above a term's
fvar range is the identity.  con-leche states it at `fvarsBelow d`; this is
the same statement at `fvarRange ≤ d`, which is what the arena's derived
column carries (`fvarsBelow_iff`, `ConLeche/Verify/Shift.lean:39`). -/
theorem abstractRange_of_fvarRange_le :
    ∀ (e : Expr) (d k c : Nat), e.fvarRange ≤ d →
      e.abstractRange d k c = e := by
  intro e
  induction e <;> intro d k c h <;>
    simp_all [Expr.abstractRange, Expr.fvarRange, Nat.max_le] <;> omega

/-- con-leche: ConLeche/Verify/AbstractRange.lean:23 abstractRange_zero — the
`k = 0` identity, which `abstractRangeFast` tests FIRST (task #97-P6-11: it
is what makes the annotation telescope's outermost binder domain cost
nothing). -/
theorem abstractRange_zero_eq :
    ∀ (e : Expr) (d c : Nat), e.abstractRange d 0 c = e := by
  intro e
  induction e <;> intro d c <;> simp_all [Expr.abstractRange] <;> omega

/-! ## The pure functions, named

`grind` must see the walk's pure function as a TERM, not a `fun`: `abs1Fn d` and `absRangeFn d k` are the memo
invariant's function, `abs1Fn d k` and `absRangeFn d k c` the answer
relation's.  Each comes with one `=` lemma per constructor the walk descends
into — they fire once congruence closure knows the denotation's constructor
(`Bridge/Grind.lean`'s `exprTag_app` & co.) — and with the cutoff and the catch-all, which
only the dispatcher needs and passes to `sym` itself. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:659-671 abstract1 — `abstract1`
with the cursor first, as the memo table keys it. -/
def abs1Fn (d k : Nat) (e : Expr) : Expr := e.abstract1 d k

/-- con-leche: ConLeche/Kernel/ExprOps.lean:686-703 abstractRange —
`abstractRange` with the cursor first, as the memo table keys it. -/
def absRangeFn (d k c : Nat) (e : Expr) : Expr := e.abstractRange d k c

/-- con-leche: ConLeche/Kernel/ExprOps.lean:665 abstract1 — the `app` clause. -/
@[bridge_grind =] theorem abs1Fn_app (d k : Nat) (f a : Expr) :
    abs1Fn d k (.app f a) = .app (abs1Fn d k f) (abs1Fn d k a) := rfl
/-- con-leche: ConLeche/Kernel/ExprOps.lean:666 abstract1 — the `lam` clause. -/
@[bridge_grind =] theorem abs1Fn_lam (d k : Nat) (t b : Expr) :
    abs1Fn d k (.lam t b) = .lam (abs1Fn d k t) (abs1Fn d (k + 1) b) := rfl
/-- con-leche: ConLeche/Kernel/ExprOps.lean:667 abstract1 — the `forallE`
clause. -/
@[bridge_grind =] theorem abs1Fn_forallE (d k : Nat) (t b : Expr) :
    abs1Fn d k (.forallE t b) = .forallE (abs1Fn d k t) (abs1Fn d (k + 1) b) := rfl
/-- con-leche: ConLeche/Kernel/ExprOps.lean:668-669 abstract1 — the `letE`
clause. -/
@[bridge_grind =] theorem abs1Fn_letE (d k : Nat) (t w b : Expr) :
    abs1Fn d k (.letE t w b) =
      .letE (abs1Fn d k t) (abs1Fn d k w) (abs1Fn d (k + 1) b) := rfl
/-- con-leche: ConLeche/Kernel/ExprOps.lean:671 abstract1 — the `proj`
clause. -/
@[bridge_grind =] theorem abs1Fn_proj (d k : Nat) (n : ConLeche.Name) (i : Nat)
    (s : Expr) : abs1Fn d k (.proj n i s) = .proj n i (abs1Fn d k s) := rfl
/-- con-leche: ConLeche/Kernel/ExprOps.lean:662 abstract1 — the `fvar`
clause: the leaf at the abstracted level becomes `bvar k`. -/
@[bridge_grind =] theorem abs1Fn_fvar (d k i : Nat) (t : Expr) :
    abs1Fn d k (.fvar i t) = if i = d then .bvar k else .fvar i t := rfl

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1765 abstract1_of_fvarRange_le —
the cutoff of `abstract1Go`. -/
theorem abs1Fn_cutoff {d k : Nat} {e : Expr} (h : e.fvarRange ≤ d) :
    abs1Fn d k e = e :=
  Expr.abstract1_of_fvarRange_le e d k h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:659-671 abstract1 — the
catch-all: a term whose tag is none of the five the walk dispatches on is a
`bvar`, `sort`, `const` or `lit`, all four fixed points. -/
theorem abs1Fn_leaf {d k : Nat} {e : Expr}
    (h1 : exprTag e ≠ ETag.fvar) (h2 : exprTag e ≠ ETag.app)
    (h3 : ETag.isBind (exprTag e) = false) (h4 : exprTag e ≠ ETag.letE)
    (h5 : exprTag e ≠ ETag.proj) : abs1Fn d k e = e := by
  cases e <;> simp_all [abs1Fn, exprTag, Expr.abstract1, ETag.isBind] <;> decide

/-- con-leche: ConLeche/Kernel/ExprOps.lean:694 abstractRange — the `app`
clause. -/
@[bridge_grind =] theorem absRangeFn_app (d k c : Nat) (f a : Expr) :
    absRangeFn d k c (.app f a) = .app (absRangeFn d k c f) (absRangeFn d k c a) := rfl
/-- con-leche: ConLeche/Kernel/ExprOps.lean:695-696 abstractRange — the `lam`
clause. -/
@[bridge_grind =] theorem absRangeFn_lam (d k c : Nat) (t b : Expr) :
    absRangeFn d k c (.lam t b) = .lam (absRangeFn d k c t) (absRangeFn d k (c + 1) b) :=
  rfl
/-- con-leche: ConLeche/Kernel/ExprOps.lean:697-698 abstractRange — the
`forallE` clause. -/
@[bridge_grind =] theorem absRangeFn_forallE (d k c : Nat) (t b : Expr) :
    absRangeFn d k c (.forallE t b) =
      .forallE (absRangeFn d k c t) (absRangeFn d k (c + 1) b) := rfl
/-- con-leche: ConLeche/Kernel/ExprOps.lean:699-701 abstractRange — the
`letE` clause. -/
@[bridge_grind =] theorem absRangeFn_letE (d k c : Nat) (t w b : Expr) :
    absRangeFn d k c (.letE t w b) =
      .letE (absRangeFn d k c t) (absRangeFn d k c w) (absRangeFn d k (c + 1) b) := rfl
/-- con-leche: ConLeche/Kernel/ExprOps.lean:703 abstractRange — the `proj`
clause. -/
@[bridge_grind =] theorem absRangeFn_proj (d k c : Nat) (n : ConLeche.Name) (i : Nat)
    (s : Expr) : absRangeFn d k c (.proj n i s) = .proj n i (absRangeFn d k c s) := rfl
/-- con-leche: ConLeche/Kernel/ExprOps.lean:689-691 abstractRange — the
`fvar` clause, at the executed walk's `Bool` range test. -/
@[bridge_grind =] theorem absRangeFn_fvar (d k c i : Nat) (t : Expr) :
    absRangeFn d k c (.fvar i t) =
      if (decide (d ≤ i) && decide (i < d + k)) = true then .bvar (c + (d + k - 1 - i))
      else .fvar i t := by
  simp [absRangeFn, Expr.abstractRange]

/-- con-leche: ConLeche/Verify/AbstractRange.lean:61 abstractRange_eq_self —
the cutoff of `abstractRangeGo`. -/
theorem absRangeFn_cutoff {d k c : Nat} {e : Expr} (h : e.fvarRange ≤ d) :
    absRangeFn d k c e = e :=
  abstractRange_of_fvarRange_le e d k c h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:686-703 abstractRange — the
catch-all, as `abs1Fn_leaf`. -/
theorem absRangeFn_leaf {d k c : Nat} {e : Expr}
    (h1 : exprTag e ≠ ETag.fvar) (h2 : exprTag e ≠ ETag.app)
    (h3 : ETag.isBind (exprTag e) = false) (h4 : exprTag e ≠ ETag.letE)
    (h5 : exprTag e ≠ ETag.proj) : absRangeFn d k c e = e := by
  cases e <;> simp_all [absRangeFn, exprTag, Expr.abstractRange, ETag.isBind] <;> decide

/-! ## The answer relations

`Bridge/Rel.lean`'s generic `RelE` at the named function (no `fun` for
`grind` to split on). -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — `abstract1`'s answer
relation. -/
abbrev Abs1At (d k : Nat) : EStore → EIdx → EStore → EIdx → Prop :=
  RelE (abs1Fn d k)

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — `abstractRange`'s answer
relation, at the SPEC function for both the spec descent and the executed
walk. -/
abbrev AbsRangeAt (d k c : Nat) : EStore → EIdx → EStore → EIdx → Prop :=
  RelE (absRangeFn d k c)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1772-1774 Abs1MemoInv — the
`abstract1` reading of the SHARED memo table `abs1C`, at the named function
(`Bridge/StateOK.lean`'s `Abs1MemoA d` is the same invariant with a `fun`,
definitionally). -/
abbrev Abs1MemoF (d : Nat) (s : AState) : Prop :=
  MemoOK (abs1Fn d) s.memos.abs1C s.store

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1772-1774 Abs1MemoInv — the
`abstractRange` reading of the SHARED memo table `abs1C` (`Abs1MemoF` is its
sibling). -/
abbrev AbsRangeMemoA (d k : Nat) (s : AState) : Prop :=
  MemoOK (absRangeFn d k) s.memos.abs1C s.store

/-! ## The memo insert, generic in the walk

`abs1Set`'s spec at the walk's function: it takes the function as a parameter — `vcgen`'s list gives
it, `abs1Set_specA (f := abs1Fn d)` — and the invariant and the answer as
PRECONDITIONS, which `vcgen` leaves as verification conditions; the post is a
plain conjunction. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1772-1774 Abs1MemoInv — `abs1Set`
carrying the memo invariant of the walk `f` the caller names. -/
theorem abs1Set_specA (f : Nat → Expr → Expr) (s₀ : AState) (h : EIdx) (c : Nat)
    (r : EIdx) (hk : (denoteE s₀.store h).isSome = true)
    (hm : MemoOK f s₀.memos.abs1C s₀.store) (hr : RelE (f c) s₀.store h s₀.store r) :
    ⦃fun s => s = s₀⦄ abs1Set (h, c) r
    ⦃fun _u s' => s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ MemoOK f s'.memos.abs1C s'.store; ⊤⦄ := by
  vcgen [abs1Set]
  subst_vars
  exact ⟨rfl, rfl, rfl, MemoOK.insert hm rfl hk hr⟩

/-! ## `fvarB`, as a hypothesis (see the module header)

The memoised exact fvar range is another group's twin; its Theorem 1 arrives
here as a record, exactly as the fuel induction's own hypothesis does.  The
frame is what this family needs and no more: `fvarB` reads the store and
writes only `fvarBC`, so `abs1C` — the table BOTH walks below key their memo
in — stands still across it. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1436-1441 fvarB — Theorem 1 for
`fvarB`, as an assumption. -/
structure FvarBSpec : Prop where
  run : ∀ (fuel : Nat) (s₁ : AState) (h : EIdx), StateOK s₁ →
    (denoteE s₁.store h).isSome = true →
    ⦃fun s => s = s₁⦄ fvarB fuel h
    ⦃fun r s' => s'.store = s₁.store ∧ s'.caches = s₁.caches ∧
        s'.pins = s₁.pins ∧ s'.memos.abs1C = s₁.memos.abs1C ∧
        RelV Expr.fvarRange s₁.store h r; ⊤⦄

/-! ## Theorem 1 for `abstract1` — `ExprOps.lean:1520`, `:1585` -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `abstract1Go`'s recursion. -/
structure Abs1Spec (d : Nat) (rec : EIdx → Nat → AM EIdx) : Prop where
  run : ∀ (s₁ : AState) (h : EIdx) (kk : Nat), StateOK s₁ → Abs1MemoF d s₁ →
    (denoteE s₁.store h).isSome = true →
    ⦃fun s => s = s₁⦄ rec h kk
    ⦃fun r s' => StateOK s' ∧ Abs1MemoF d s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        Abs1At d kk s₁.store h s'.store r; ⊤⦄

/-! ### The binder intern, with the VIEW-monotonicity conjunct

`ExprOps/MemoSpecs.lean`'s `internRebuiltBind_specV` — the binder intern with
view monotonicity: `abstract1Go`'s binder arm interns between the recursive
calls and the memo insert, so without the conjunct the walk's own view
monotonicity dies at that arm.  A local spec, so no other file's verification
conditions change shape under it. -/
attribute [local spec high] internRebuiltBind_specV

/-! ### The five ARM theorems (DESIGN §8.6's arm-split ruling, 2026-09-22)

One theorem per `mutual`-block arm, exactly as `ExprOps/Inst1.lean` does, and
for the reason task #97-P3-1 gives: **the `fvarB` call lives in the DISPATCHER
only**.  Each arm is the probe, the projection, the recursive calls (the
induction hypothesis in the `vcgen` list), the intern and the insert; the
view monotonicity of the arm's post is the callees' `∀` conjuncts, chained
by `grind`. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the `app`
ARM: probe, project, recurse into both children, rebuild, insert. -/
theorem abstract1ArmApp_spec (d fuel : Nat)
    (ih : Abs1Spec d (abstract1Go d fuel)) (s₁ : AState) (h : EIdx) (kk : Nat)
    (hok : StateOK s₁) (hm : Abs1MemoF d s₁)
    (hden : (denoteE s₁.store h).isSome = true)
    (htg : (h.tag == ETag.app) = true) :
    ⦃fun s => s = s₁⦄ abstract1ArmApp d fuel h kk
    ⦃fun r s' => StateOK s' ∧ Abs1MemoF d s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        Abs1At d kk s₁.store h s'.store r; ⊤⦄ := by
  sym only [bridge_grind, denoteEView, opt2] =>
    vcgen [abstract1ArmApp, ih.run, abs1Set_specA (f := abs1Fn d)] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the BINDER
ARM (`lam` and `forallE` in one, as the tag dispatch tests them).  The body
descends at `kk + 1`, and the binder DATUM is carried across unchanged, which
is what the `viewBM` monotonicity conjunct is for. -/
theorem abstract1ArmBind_spec (d fuel : Nat)
    (ih : Abs1Spec d (abstract1Go d fuel)) (s₁ : AState) (h : EIdx) (kk : Nat)
    (hok : StateOK s₁) (hm : Abs1MemoF d s₁)
    (hden : (denoteE s₁.store h).isSome = true)
    (htg : ETag.isBind h.tag = true) :
    ⦃fun s => s = s₁⦄ abstract1ArmBind d fuel h kk
    ⦃fun r s' => StateOK s' ∧ Abs1MemoF d s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        Abs1At d kk s₁.store h s'.store r; ⊤⦄ := by
  sym only [bridge_grind, denoteEView, opt2, ETag.isBind] =>
    vcgen [abstract1ArmBind, ih.run, abs1Set_specA (f := abs1Fn d)] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the `fvar`
ARM, which does not recurse and needs no induction hypothesis: at the
abstracted level it interns a fresh `bvar kk`, at any other it answers the
handle it was given. -/
theorem abstract1ArmFVar_spec (d : Nat) (s₁ : AState) (h : EIdx) (kk : Nat)
    (hok : StateOK s₁) (hm : Abs1MemoF d s₁)
    (hden : (denoteE s₁.store h).isSome = true)
    (htg : (h.tag == ETag.fvar) = true) :
    ⦃fun s => s = s₁⦄ abstract1ArmFVar d h kk
    ⦃fun r s' => StateOK s' ∧ Abs1MemoF d s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        Abs1At d kk s₁.store h s'.store r; ⊤⦄ := by
  sym only [bridge_grind, denoteEView] =>
    vcgen [abstract1ArmFVar] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the `letE`
ARM; the body is the one child at the bumped cursor.  Three recursive calls
put the body's answer six instantiation generations from the subject's view,
past `grind`'s default of 8 with the transport at the insert: `gen := 10`. -/
theorem abstract1ArmLet_spec (d fuel : Nat)
    (ih : Abs1Spec d (abstract1Go d fuel)) (s₁ : AState) (h : EIdx) (kk : Nat)
    (hok : StateOK s₁) (hm : Abs1MemoF d s₁)
    (hden : (denoteE s₁.store h).isSome = true)
    (htg : (h.tag == ETag.letE) = true) :
    ⦃fun s => s = s₁⦄ abstract1ArmLet d fuel h kk
    ⦃fun r s' => StateOK s' ∧ Abs1MemoF d s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        Abs1At d kk s₁.store h s'.store r; ⊤⦄ := by
  sym only [bridge_grind, denoteEView, opt3] =>
    vcgen [abstract1ArmLet, ih.run, abs1Set_specA (f := abs1Fn d)] <;>
      finish (gen := 10)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the `proj`
ARM.  The struct NAME is carried unchanged: `DenoteView.proj` names its
denotation, `denoteN_le` carries it to the intern. -/
theorem abstract1ArmProj_spec (d fuel : Nat)
    (ih : Abs1Spec d (abstract1Go d fuel)) (s₁ : AState) (h : EIdx) (kk : Nat)
    (hok : StateOK s₁) (hm : Abs1MemoF d s₁)
    (hden : (denoteE s₁.store h).isSome = true)
    (htg : (h.tag == ETag.proj) = true) :
    ⦃fun s => s = s₁⦄ abstract1ArmProj d fuel h kk
    ⦃fun r s' => StateOK s' ∧ Abs1MemoF d s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        Abs1At d kk s₁.store h s'.store r; ⊤⦄ := by
  sym only [bridge_grind, denoteEView, opt2] =>
    vcgen [abstract1ArmProj, ih.run, abs1Set_specA (f := abs1Fn d)] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:764-776 abstract1
con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go
**THEOREM 1 for `abstract1`**, at one level of the recursion, by induction on
the fuel.  The dispatcher: `fvarB`'s answer and `abs1Fn_cutoff` close the
cutoff, the five arm theorems the tag chain, `abs1Fn_leaf` the catch-all. -/
theorem abstract1Go_spec (hfv : FvarBSpec) (d : Nat) :
    ∀ fuel, Abs1Spec d (abstract1Go d fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h kk _ _ _
    sym only [bridge_grind] => vcgen [abstract1Go_zero] <;> finish
  | succ fuel ih =>
    constructor
    intro s₀ h kk hok hm hden
    sym only [bridge_grind, abs1Fn_cutoff, abs1Fn_leaf] =>
      vcgen [abstract1Go_succ, abstract1ArmApp_spec d fuel ih,
        abstract1ArmBind_spec d fuel ih, abstract1ArmFVar_spec d,
        abstract1ArmLet_spec d fuel ih, abstract1ArmProj_spec d fuel ih,
        hfv.run] <;> finish

/-! ## The axiom check -/

#print axioms abstractRange_of_fvarRange_le
#print axioms abstractRange_zero_eq
#print axioms abstract1Go_spec

end ConRon.Bridge.ExprOps

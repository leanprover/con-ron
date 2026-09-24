/-
# `ConRon.Bridge.ExprOps.Abs` — Theorem 1 for the ABSTRACTION family

DESIGN §8.2's Theorem 1 at the five twins of `Arena/ExprOps.lean` that close
free variables into bound ones: `abstractRange` (the SPEC descent, `:669`),
`abstract1Go` / `abstract1Fast` (`:1520`, `:1585`) and `abstractRangeGo` /
`abstractRangeFast` (`:1616`, `:1686`).

Written against `ExprOps/Inst1.lean`, the tier's exemplar: the same `…Spec`
record for one level of the recursion, the same fuel induction, the same
per-arm `_step` lemmas in "the shape `mvcgen` actually produces", the same
`abs_hyp`, the same `attribute [-grind]` line.

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
   `ExprOps/MemoSpecs.lean`'s `abs1Set_specI` — the memo insert's spec with
   the pure function moved INSIDE the postcondition — is what lets one
   primitive serve both.

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
dispatcher's `mvcgen` list is the five of them.

It is what closed this file's five open goals.  `fvarB` lives in the
DISPATCHER and the arms never call it, so an arm has no store hop at all and
every hypothesis is found by `assumption`; what is left for the dispatcher is
the hop, the cutoff and the catch-all.  The hop is not free even there —
`mvcgen` matches an arm spec's POSTCONDITION first and so pins its start
state to `s₀`, which is the state before `fvarB` — so each arm is used
through a `…_hop` wrapper that names the two states separately (see that
section's note).
-/
import ConRon.Bridge.ExprOps.MemoSpecs

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

/-! ### Attribute hygiene (task #97s round 2, item 1)

`RelE.ext`, `.of_ext` and `.retarget` close the answer relation under `Ext` in
both directions, so every intermediate store multiplies every answer already
known; the `_step` lemmas carry the chain themselves.  `attribute [-grind]`
does not travel through an import, so every file of this tier repeats the
line. -/
attribute [-grind] RelE.ext RelE.of_ext RelE.retarget

/-- con-leche: none — `mvcgen` hands an arm its projection read as
`some fields = st.viewC h`, i.e. REVERSED, so the one-line `assumption` that
supplies a step lemma's hypothesis has to try both orientations. -/
macro "abs_hyp" : tactic => `(tactic| first
  | assumption
  | (symm; assumption)
  | grind only [Ext.trans, Ext.refl]
  | grind [StateOK])

/-! ## The pure licences

Three pure facts about con-leche's `abstractRange`, one of which con-leche
has (`abstract1_of_fvarRange_le`, `ConLeche/Kernel/ExprOps.lean:1765`) and two
of which it states in `Verify/` against `fvarsBelow` rather than against
`fvarRange`.  They are re-proved here at the field the arena READS, so that
this tier imports `ConLeche.Kernel.*` only. -/

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

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1765 abstract1_of_fvarRange_le —
the same licence for `abstract1`, which con-leche has at `fvarRange`
already. -/
theorem abstract1_of_fvarRange_le_ {e : Expr} {d k : Nat}
    (h : e.fvarRange ≤ d) : Expr.abstract1 e d k = e :=
  Expr.abstract1_of_fvarRange_le e d k h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:764-776 abstract1 — the four LEAF
constructors a catch-all arm covers are fixed points of `abstract1`. -/
theorem abstract1_leaf {e : Expr} {d k : Nat}
    (h : (∃ u, e = .sort u) ∨ (∃ n us, e = .const n us) ∨ (∃ l, e = .lit l) ∨
      ∃ i, e = .bvar i) : Expr.abstract1 e d k = e := by
  rcases h with ⟨u, rfl⟩ | ⟨n, us, rfl⟩ | ⟨l, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [Expr.abstract1]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-808 abstractRange — and of
`abstractRange`. -/
theorem abstractRange_leaf {e : Expr} {d k c : Nat}
    (h : (∃ u, e = .sort u) ∨ (∃ n us, e = .const n us) ∨ (∃ l, e = .lit l) ∨
      ∃ i, e = .bvar i) : e.abstractRange d k c = e := by
  rcases h with ⟨u, rfl⟩ | ⟨n, us, rfl⟩ | ⟨l, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [Expr.abstractRange]

/-! ## The answer relations

`Bridge/Rel.lean`'s generic `RelE` with the pure function fixed (task #97b
finding 1), so all of `RelE`'s eliminators apply and `grind` still sees a head
symbol. -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — `abstract1`'s answer
relation. -/
abbrev Abs1At (d k : Nat) : EStore → EIdx → EStore → EIdx → Prop :=
  RelE (fun e => Expr.abstract1 e d k)

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — `abstractRange`'s answer
relation, at the SPEC function for both the spec descent and the executed
walk. -/
abbrev AbsRangeAt (d k c : Nat) : EStore → EIdx → EStore → EIdx → Prop :=
  RelE (fun e => e.abstractRange d k c)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1772-1774 Abs1MemoInv — the
`abstractRange` reading of the SHARED memo table `abs1C`
(`Bridge/StateOK.lean` has the `abstract1` reading, `Abs1MemoA d`; this is
its sibling and belongs beside it). -/
abbrev AbsRangeMemoA (d k : Nat) (s : AState) : Prop :=
  MemoOK (fun c e => e.abstractRange d k c) s.memos.abs1C s.store

/-! ## The step lemmas, in the shape `mvcgen` actually produces

Task #97s round 1's group 7 and round 2's item 3.  Five per walk: the four
branching node kinds and the `fvar` leaf that ANSWERS (the one arm where the
two walks differ). -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-808 abstractRange — the `app`
arm. -/
theorem AbsRangeAt.app_step {d k c : Nat} {st s1 s2 s3 : EStore}
    {h f a rf ra r : EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.app f a))
    (hx1 : Ext st s1) (hf : AbsRangeAt d k c st f s1 rf)
    (hx2 : Ext s1 s2) (ha : AbsRangeAt d k c s1 a s2 ra)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) :
    AbsRangeAt d k c st h s3 r :=
  RelE.app hwf hview (fun _ _ => rfl) ((hf.ext hx2).ext hx3)
    ((ha.of_ext hx1).ext hx3) hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-808 abstractRange — the two
binder arms at a tag the walk carries (`eBindView`), with the binder datum
UNCHANGED (`abstractRange` does not touch it). -/
theorem AbsRangeAt.bind_step {d k c : Nat} {st s1 s2 s3 : EStore}
    {h ty b rt rb r : EIdx} {m : BinderMeta} {tg : UInt32} (hwf : StoreWF st)
    (htg : ETag.isBind tg = true)
    (hview : st.view h = some (eBindView tg ty b m))
    (hx1 : Ext st s1) (ht : AbsRangeAt d k c st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : AbsRangeAt d k (c + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (eBindView tg rt rb m)) :
    AbsRangeAt d k c st h s3 r := by
  rcases (show tg = ETag.lam ∨ tg = ETag.forallE by
      simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq] at htg; exact htg)
    with rfl | rfl
  · rw [eBindView] at hview hr; simp only [beq_self_eq_true, if_true] at hview hr
    exact RelE.lam hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
      ((hb.of_ext hx1).ext hx3) hr
  · rw [eBindView] at hview hr
    simp only [ETag.lam, ETag.forallE] at hview hr
    exact RelE.forallE hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
      ((hb.of_ext hx1).ext hx3) hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-808 abstractRange — the `lam`
arm at the CONSTRUCTOR (the spec descent reads the datum's value out of the
view and puts it back unchanged). -/
theorem AbsRangeAt.lam_step {d k c : Nat} {st s1 s2 s3 : EStore}
    {h ty b rt rb r : EIdx} {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.lam ty b m))
    (hx1 : Ext st s1) (ht : AbsRangeAt d k c st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : AbsRangeAt d k (c + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.lam rt rb m)) :
    AbsRangeAt d k c st h s3 r :=
  RelE.lam hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
    ((hb.of_ext hx1).ext hx3) hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-808 abstractRange — and the
`forallE` arm. -/
theorem AbsRangeAt.forallE_step {d k c : Nat} {st s1 s2 s3 : EStore}
    {h ty b rt rb r : EIdx} {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.forallE ty b m))
    (hx1 : Ext st s1) (ht : AbsRangeAt d k c st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : AbsRangeAt d k (c + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.forallE rt rb m)) :
    AbsRangeAt d k c st h s3 r :=
  RelE.forallE hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
    ((hb.of_ext hx1).ext hx3) hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-808 abstractRange — the `letE`
arm, whose BODY is the one child at the bumped cursor. -/
theorem AbsRangeAt.letE_step {d k c : Nat} {st s1 s2 s3 s4 : EStore}
    {h ty w b rt rw rb r : EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.letE ty w b))
    (hx1 : Ext st s1) (ht : AbsRangeAt d k c st ty s1 rt)
    (hx2 : Ext s1 s2) (hw : AbsRangeAt d k c s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : AbsRangeAt d k (c + 1) s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) :
    AbsRangeAt d k c st h s4 r :=
  RelE.letE hwf hview (fun _ _ _ => rfl) (((ht.ext hx2).ext hx3).ext hx4)
    (((hw.of_ext hx1).ext hx3).ext hx4) ((hb.of_ext (hx1.trans hx2)).ext hx4) hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-808 abstractRange — the `proj`
arm, whose struct name is carried unchanged. -/
theorem AbsRangeAt.proj_step {d k c : Nat} {st s1 s2 : EStore}
    {h sub rs r : EIdx} {n : NIdx} {i : Nat} {nm : ConLeche.Name}
    (hwf : StoreWF st) (hview : st.view h = some (.proj n i sub))
    (hx1 : Ext st s1) (hs : AbsRangeAt d k c st sub s1 rs)
    (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs))
    (hn0 : denoteN st.ns n = some nm) : AbsRangeAt d k c st h s2 r :=
  RelE.proj hwf hview (fun _ => rfl) (hs.ext hx2) hn0
    (denoteN_ext (denoteN_ext hn0 hx1) hx2) hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-808 abstractRange — the `fvar`
arm IN THE RANGE: the leaf is replaced by the bound variable of the binder it
names, and the annotation is not descended into. -/
theorem AbsRangeAt.fvar_hit {d k c idx : Nat} {st st' : EStore} {h ty r : EIdx}
    (hwf : StoreWF st) (hview : st.view h = some (.fvar idx ty))
    (hin : d ≤ idx ∧ idx < d + k)
    (hr : denoteE st' r = some (.bvar (c + (d + k - 1 - idx)))) :
    AbsRangeAt d k c st h st' r := by
  intro e he
  obtain ⟨t, rfl, _⟩ := denote_fvar_inv hwf hview he
  show denoteE st' r = some ((Expr.fvar idx t).abstractRange d k c)
  have h2 : (Expr.fvar idx t).abstractRange d k c
      = Expr.bvar (c + (d + k - 1 - idx)) := by
    simp [Expr.abstractRange, hin]
  rw [h2]; exact hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-808 abstractRange — the `fvar`
arm OUTSIDE the range: the handle answers itself. -/
theorem AbsRangeAt.fvar_miss {d k c idx : Nat} {st : EStore} {h ty : EIdx}
    (hwf : StoreWF st) (hview : st.view h = some (.fvar idx ty))
    (hout : ¬ (d ≤ idx ∧ idx < d + k)) : AbsRangeAt d k c st h st h := by
  intro e he
  obtain ⟨t, rfl, _⟩ := denote_fvar_inv hwf hview he
  show denoteE st h = some ((Expr.fvar idx t).abstractRange d k c)
  have h2 : (Expr.fvar idx t).abstractRange d k c = Expr.fvar idx t := by
    simp [Expr.abstractRange, hout]
  rw [h2]; exact he

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-808 abstractRange — the LEAF
arms of the SPEC descent, which dispatches on the VIEW and so knows which
constructor it is looking at. -/
theorem AbsRangeAt.self_of_leafView {d k c : Nat} {st : EStore} {h : EIdx}
    {v : ENodeView} (hwf : StoreWF st) (hview : st.view h = some v)
    (hv : (∃ i, v = .bvar i) ∨ (∃ u, v = .sort u) ∨
      (∃ n us, v = .const n us) ∨ ∃ l, v = .lit l) :
    AbsRangeAt d k c st h st h := by
  intro e he
  show denoteE st h = some (e.abstractRange d k c)
  have hleaf : (∃ u, e = .sort u) ∨ (∃ n us, e = .const n us) ∨
      (∃ l, e = .lit l) ∨ ∃ i, e = .bvar i := by
    rcases hv with ⟨i, rfl⟩ | ⟨u, rfl⟩ | ⟨n, us, rfl⟩ | ⟨l, rfl⟩
    · exact Or.inr (Or.inr (Or.inr ⟨i, denote_bvar_inv hwf hview he⟩))
    · obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hview he
      exact Or.inl ⟨l, rfl⟩
    · obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hview he
      exact Or.inr (Or.inl ⟨nm, ls, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨l, denote_lit_inv hwf hview he⟩))
  rw [abstractRange_leaf hleaf]
  exact he

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-808 abstractRange — the LEAF
arms at a TAG dispatch (the executed walk's catch-all `else`): `bvar`, `sort`,
`const` and `lit` answer the handle they were given. -/
theorem AbsRangeAt.leaf {d k c : Nat} {st : EStore} {h : EIdx}
    {v : ENodeView} (hwf : StoreWF st) (hview : st.view h = some v)
    (hfvar : ¬ (h.tag = ETag.fvar)) (happ : ¬ (h.tag = ETag.app))
    (hbind : ETag.isBind h.tag = false) (hlet : ¬ (h.tag = ETag.letE))
    (hproj : ¬ (h.tag = ETag.proj)) : AbsRangeAt d k c st h st h := by
  intro e he
  show denoteE st h = some (e.abstractRange d k c)
  have htag := EStore.tagOf_of_view hview
  have hleaf : (∃ u, e = .sort u) ∨ (∃ n us, e = .const n us) ∨
      (∃ l, e = .lit l) ∨ ∃ i, e = .bvar i := by
    cases v with
    | bvar i => exact Or.inr (Or.inr (Or.inr ⟨i, denote_bvar_inv hwf hview he⟩))
    | fvar j t => exact absurd (htag.trans rfl) hfvar
    | sort u =>
      obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hview he
      exact Or.inl ⟨l, rfl⟩
    | const n us =>
      obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hview he
      exact Or.inr (Or.inl ⟨nm, ls, rfl⟩)
    | app f a => exact absurd (htag.trans rfl) happ
    | lam ty b m =>
      rw [htag] at hbind; simp [ENodeView.tagOf, ETag.isBind] at hbind
    | forallE ty b m =>
      rw [htag] at hbind
      simp [ENodeView.tagOf, ETag.isBind, ETag.lam, ETag.forallE] at hbind
    | letE ty w b => exact absurd (htag.trans rfl) hlet
    | lit l => exact Or.inr (Or.inr (Or.inl ⟨l, denote_lit_inv hwf hview he⟩))
    | proj n i sub => exact absurd (htag.trans rfl) hproj
  rw [abstractRange_leaf hleaf]
  exact he

/-! ## Theorem 1 for `abstractRange` — the SPEC descent (`ExprOps.lean:669`)

The bare structural descent con-leche's `Kernel/ExprOps.lean:791` is: no
cutoff, no memo, `internE` at every rebuilt node.  It is what the executed
walk is *stated against*, and the checker calls it nowhere (task #97-P6-11
replaced every call with `abstractRangeFast`) — so its theorem is the
family's statement anchor and the cheapest of the five. -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `abstractRange`'s descent. -/
structure AbsRangeSpec (d k : Nat) (rec : EIdx → Nat → AM EIdx) : Prop where
  run : ∀ (s₁ : AState) (h : EIdx) (c : Nat), StateOK s₁ →
    (denoteE s₁.store h).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec h c
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₁.store s'.store ∧ BMExt s₁.store s'.store ∧
        s'.memos = s₁.memos ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        AbsRangeAt d k c s₁.store h s'.store r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-808 abstractRange —
**THEOREM 1 for the `abstractRange` SPEC descent**, at one level of the
recursion, by induction on the fuel. -/
theorem abstractRange_spec (d k : Nat) :
    ∀ fuel, AbsRangeSpec d k (fun h c => abstractRange fuel h d k c) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h c _ _
    mvcgen [abstractRange_zero]
    all_goals bridge_vcs [Expr.abstractRange]
  | succ fuel ih =>
    constructor
    intro s₀ h c hok hden
    have hrec := ih.run
    mvcgen [abstractRange_succ, absRangeArmApp, absRangeArmLam, absRangeArmForallE, absRangeArmLet, absRangeArmProj, hrec]
    all_goals try bridge_vcs [Expr.abstractRange]
    -- Eleven structural verification conditions remain, in goal order: the
    -- four LEAF views, the `fvar` leaf's two branches, and the five rebuilding
    -- arms.  Task #97s round 2's item 3 ("the two structural verification
    -- conditions of every arm applied by hand"), and the intern's
    -- postcondition arrives as an IMPLICATION chain here rather than as a
    -- conjunction, so each rebuilding arm `intro`s it first.
    -- `bvar`
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
        AbsRangeAt.self_of_leafView hok.wf (by abs_hyp) (by grind)⟩
    -- `fvar`, in the range: the fresh `bvar` node
    next =>
      bridge_peel
      subst_vars
      intro _hwf2 hx _hlss _hmem _hcach _hpin _hvm _hbm _hview2 hr
      refine ⟨by grind only [StateOK, StateOK.mk], by grind only [Ext.trans],
        by grind only [BMExt, BMExt.trans, BMExt.refl],
        by grind, by grind, by grind, ?_⟩
      exact AbsRangeAt.fvar_hit hok.wf (by abs_hyp) (by abs_hyp)
        (by rw [hr, denoteEView])
    -- `fvar`, outside the range
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
        AbsRangeAt.fvar_miss hok.wf (by abs_hyp) (by abs_hyp)⟩
    -- `sort`, `const`, `lit`
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
        AbsRangeAt.self_of_leafView hok.wf (by abs_hyp) (by grind)⟩
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
        AbsRangeAt.self_of_leafView hok.wf (by abs_hyp) (by grind)⟩
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
        AbsRangeAt.self_of_leafView hok.wf (by abs_hyp) (by grind)⟩
    -- `app`
    next =>
      bridge_peel
      subst_vars
      intro _hwf2 hx _hlss _hmem _hcach _hpin _hvm _hbm _hview2 hr
      refine ⟨by grind only [StateOK, StateOK.mk], by grind only [Ext.trans],
        by grind only [BMExt, BMExt.trans, BMExt.refl],
        by grind, by grind, by grind, ?_⟩
      exact AbsRangeAt.app_step hok.wf (by abs_hyp) (by abs_hyp) (by abs_hyp)
        (by abs_hyp) (by abs_hyp) hx hr
    -- `lam`
    next =>
      bridge_peel
      subst_vars
      intro _hwf2 hx _hlss _hmem _hcach _hpin _hvm _hbm _hview2 hr
      refine ⟨by grind only [StateOK, StateOK.mk], by grind only [Ext.trans],
        by grind only [BMExt, BMExt.trans, BMExt.refl],
        by grind, by grind, by grind, ?_⟩
      exact AbsRangeAt.lam_step hok.wf (by abs_hyp) (by abs_hyp) (by abs_hyp)
        (by abs_hyp) (by abs_hyp) hx hr
    -- `forallE`
    next =>
      bridge_peel
      subst_vars
      intro _hwf2 hx _hlss _hmem _hcach _hpin _hvm _hbm _hview2 hr
      refine ⟨by grind only [StateOK, StateOK.mk], by grind only [Ext.trans],
        by grind only [BMExt, BMExt.trans, BMExt.refl],
        by grind, by grind, by grind, ?_⟩
      exact AbsRangeAt.forallE_step hok.wf (by abs_hyp) (by abs_hyp)
        (by abs_hyp) (by abs_hyp) (by abs_hyp) hx hr
    -- `letE`
    next =>
      bridge_peel
      subst_vars
      intro _hwf2 hx _hlss _hmem _hcach _hpin _hvm _hbm _hview2 hr
      refine ⟨by grind only [StateOK, StateOK.mk], by grind only [Ext.trans],
        by grind only [BMExt, BMExt.trans, BMExt.refl],
        by grind, by grind, by grind, ?_⟩
      exact AbsRangeAt.letE_step hok.wf (by abs_hyp) (by abs_hyp) (by abs_hyp)
        (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp) hx hr
    -- `proj`
    next =>
      bridge_peel
      subst_vars
      obtain ⟨nm, es, _, hn0, _⟩ :=
        denote_eq_proj hok.wf (by abs_hyp) hden
      intro _hwf2 hx _hlss _hmem _hcach _hpin _hvm _hbm _hview2 hr
      refine ⟨by grind only [StateOK, StateOK.mk], by grind only [Ext.trans],
        by grind only [BMExt, BMExt.trans, BMExt.refl],
        by grind, by grind, by grind, ?_⟩
      exact AbsRangeAt.proj_step hok.wf (by abs_hyp) (by abs_hyp) (by abs_hyp)
        hx hr hn0


/-! ## The executed walks' own lemmas

The cutoff, the `fvar` leaf that answers, and the catch-all — the three arms
where the executed walks differ from the spec descent. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1765 abstract1_of_fvarRange_le —
the CUTOFF arm of `abstract1Go`, packaged as one step lemma (task #97s's rule
about a lemma whose hypotheses `grind` would have to assemble: here the pair
`fvarB`'s answer relation + con-leche's licence fires once). -/
theorem Abs1At.cutoff {st : EStore} {h : EIdx} {d kk fb : Nat}
    (hfb : RelV Expr.fvarRange st h fb) (hle : fb ≤ d) :
    Abs1At d kk st h st h := by
  intro e he
  show denoteE st h = some (Expr.abstract1 e d kk)
  have h1 : fb = e.fvarRange := hfb e he
  rw [abstract1_of_fvarRange_le_ (by omega)]
  exact he

/-- con-leche: ConLeche/Verify/AbstractRange.lean:61 abstractRange_eq_self —
the same cutoff for `abstractRangeGo`. -/
theorem AbsRangeAt.cutoff {st : EStore} {h : EIdx} {d k c fb : Nat}
    (hfb : RelV Expr.fvarRange st h fb) (hle : fb ≤ d) :
    AbsRangeAt d k c st h st h := by
  intro e he
  show denoteE st h = some (e.abstractRange d k c)
  have h1 : fb = e.fvarRange := hfb e he
  rw [abstractRange_of_fvarRange_le e d k c (by omega)]
  exact he

/-- con-leche: ConLeche/Kernel/ExprOps.lean:764-776 abstract1 — the `fvar`
arm AT the abstracted level: the leaf becomes `bvar kk`. -/
theorem Abs1At.fvar_hit {d kk idx : Nat} {st st' : EStore} {h ty r : EIdx}
    (hwf : StoreWF st) (hview : st.view h = some (.fvar idx ty))
    (hidx : idx = d) (hr : denoteE st' r = some (.bvar kk)) :
    Abs1At d kk st h st' r := by
  intro e he
  obtain ⟨t, rfl, _⟩ := denote_fvar_inv hwf hview he
  show denoteE st' r = some (Expr.abstract1 (.fvar idx t) d kk)
  rw [show Expr.abstract1 (.fvar idx t) d kk = Expr.bvar kk by
    simp [Expr.abstract1, hidx]]
  exact hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:764-776 abstract1 — and at any
other level, where the handle answers itself. -/
theorem Abs1At.fvar_miss {d kk idx : Nat} {st : EStore} {h ty : EIdx}
    (hwf : StoreWF st) (hview : st.view h = some (.fvar idx ty))
    (hidx : ¬ (idx = d)) : Abs1At d kk st h st h := by
  intro e he
  obtain ⟨t, rfl, _⟩ := denote_fvar_inv hwf hview he
  show denoteE st h = some (Expr.abstract1 (.fvar idx t) d kk)
  rw [show Expr.abstract1 (.fvar idx t) d kk = Expr.fvar idx t by
    simp [Expr.abstract1, hidx]]
  exact he

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-808 abstractRange — the `fvar`
arm of the EXECUTED walk, whose range test is the `Bool` conjunction. -/
theorem AbsRangeAt.fvar_hitB {d k c idx : Nat} {st st' : EStore}
    {h ty r : EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.fvar idx ty))
    (hin : (decide (d ≤ idx) && decide (idx < d + k)) = true)
    (hr : denoteE st' r = some (.bvar (c + (d + k - 1 - idx)))) :
    AbsRangeAt d k c st h st' r :=
  AbsRangeAt.fvar_hit hwf hview (by simp at hin; omega) hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:791-808 abstractRange — and its
`false` branch. -/
theorem AbsRangeAt.fvar_missB {d k c idx : Nat} {st : EStore} {h ty : EIdx}
    (hwf : StoreWF st) (hview : st.view h = some (.fvar idx ty))
    (hout : ¬ ((decide (d ≤ idx) && decide (idx < d + k)) = true)) :
    AbsRangeAt d k c st h st h :=
  AbsRangeAt.fvar_miss hwf hview (by simp at hout; omega)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:764-776 abstract1 — the CATCH-ALL
arm of `abstract1Go` / `abstractRangeGo`: a handle whose tag is none of the
five the walk dispatches on denotes `bvar`, `sort`, `const` or `lit`, all four
of which are fixed points. -/
theorem Abs1At.leaf {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {v : ENodeView} {d kk : Nat} (hview : st.view h = some v)
    (hfvar : ¬ (h.tag = ETag.fvar)) (happ : ¬ (h.tag = ETag.app))
    (hbind : ETag.isBind h.tag = false) (hlet : ¬ (h.tag = ETag.letE))
    (hproj : ¬ (h.tag = ETag.proj)) : Abs1At d kk st h st h := by
  intro e he
  show denoteE st h = some (Expr.abstract1 e d kk)
  have htag := EStore.tagOf_of_view hview
  have hleaf : (∃ u, e = .sort u) ∨ (∃ n us, e = .const n us) ∨
      (∃ l, e = .lit l) ∨ ∃ i, e = .bvar i := by
    cases v with
    | bvar i => exact Or.inr (Or.inr (Or.inr ⟨i, denote_bvar_inv hwf hview he⟩))
    | fvar j t => exact absurd (htag.trans rfl) hfvar
    | sort u =>
      obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hview he
      exact Or.inl ⟨l, rfl⟩
    | const n us =>
      obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hview he
      exact Or.inr (Or.inl ⟨nm, ls, rfl⟩)
    | app f a => exact absurd (htag.trans rfl) happ
    | lam ty b m =>
      rw [htag] at hbind; simp [ENodeView.tagOf, ETag.isBind] at hbind
    | forallE ty b m =>
      rw [htag] at hbind
      simp [ENodeView.tagOf, ETag.isBind, ETag.lam, ETag.forallE] at hbind
    | letE ty w b => exact absurd (htag.trans rfl) hlet
    | lit l => exact Or.inr (Or.inr (Or.inl ⟨l, denote_lit_inv hwf hview he⟩))
    | proj n i sub => exact absurd (htag.trans rfl) hproj
  rw [abstract1_leaf hleaf]
  exact he

/-! ### The `abstract1` step lemmas

The executed walks test the TAG and then project (task #97-P6-13), so the arms
are guarded by tag equations and a REVERSED projection read; the `view` fact
each step lemma wants is derived by `Bridge/Rel.lean`'s group 6. -/

theorem Abs1At.app_step {d kk : Nat} {st s1 s2 s3 : EStore}
    {h f a rf ra r : EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.app f a))
    (hx1 : Ext st s1) (hf : Abs1At d kk st f s1 rf)
    (hx2 : Ext s1 s2) (ha : Abs1At d kk s1 a s2 ra)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) :
    Abs1At d kk st h s3 r :=
  RelE.app hwf hview (fun _ _ => rfl) ((hf.ext hx2).ext hx3)
    ((ha.of_ext hx1).ext hx3) hr

theorem Abs1At.bind_step {d kk : Nat} {st s1 s2 s3 : EStore}
    {h ty b rt rb r : EIdx} {m : BinderMeta} {tg : UInt32} (hwf : StoreWF st)
    (htg : ETag.isBind tg = true)
    (hview : st.view h = some (eBindView tg ty b m))
    (hx1 : Ext st s1) (ht : Abs1At d kk st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : Abs1At d (kk + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (eBindView tg rt rb m)) :
    Abs1At d kk st h s3 r := by
  rcases (show tg = ETag.lam ∨ tg = ETag.forallE by
      simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq] at htg; exact htg)
    with rfl | rfl
  · rw [eBindView] at hview hr; simp only [beq_self_eq_true, if_true] at hview hr
    exact RelE.lam hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
      ((hb.of_ext hx1).ext hx3) hr
  · rw [eBindView] at hview hr
    simp only [ETag.lam, ETag.forallE] at hview hr
    exact RelE.forallE hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
      ((hb.of_ext hx1).ext hx3) hr

theorem Abs1At.letE_step {d kk : Nat} {st s1 s2 s3 s4 : EStore}
    {h ty w b rt rw rb r : EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.letE ty w b))
    (hx1 : Ext st s1) (ht : Abs1At d kk st ty s1 rt)
    (hx2 : Ext s1 s2) (hw : Abs1At d kk s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : Abs1At d (kk + 1) s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) :
    Abs1At d kk st h s4 r :=
  RelE.letE hwf hview (fun _ _ _ => rfl) (((ht.ext hx2).ext hx3).ext hx4)
    (((hw.of_ext hx1).ext hx3).ext hx4) ((hb.of_ext (hx1.trans hx2)).ext hx4) hr

theorem Abs1At.proj_step {d kk : Nat} {st s1 s2 : EStore} {h sub rs r : EIdx}
    {n : NIdx} {i : Nat} {nm : ConLeche.Name} (hwf : StoreWF st)
    (hview : st.view h = some (.proj n i sub))
    (hx1 : Ext st s1) (hs : Abs1At d kk st sub s1 rs)
    (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs))
    (hn0 : denoteN st.ns n = some nm) : Abs1At d kk st h s2 r :=
  RelE.proj hwf hview (fun _ => rfl) (hs.ext hx2) hn0
    (denoteN_ext (denoteN_ext hn0 hx1) hx2) hr


/-! ### The same lemmas at the arm's own hypotheses, WITH the `fvarB` hop

Task #97s round 1's group 7 ("the per-site step lemmas, as the verification
condition presents them"), plus one argument the exemplar does not need: the
extra hypothesis `hst : st0 = st`.

Both executed walks call `fvarB` BEFORE they read the store, and `fvarB`'s
Theorem 1 frames the store with an EQUATION (`s'.store = s₁.store`) rather
than leaving the state alone — it writes `fvarBC` — so a store fact read
after it is *equal to* but not syntactically the one the answer relation is
stated from.

**Since DESIGN §8.6's arm-split ruling the hop no longer happens in an arm.**
`fvarB` lives in the DISPATCHER and the five `mutual`-block arms never call
it, so each arm theorem below applies these at `hst := rfl` and every other
hypothesis is found by `assumption`, exactly as in `ExprOps/Inst1.lean`; the
hop itself is done once per arm, in the `…_hop` wrappers further down.  The
`hst` argument is kept because `abstractRangeGo`'s twin (`ExprOps/Owed.lean`)
is not split and still reads the store after `fvarB`. -/

/-- con-leche: none — `Abs1At.app_step` at the arm's own hypotheses. -/
theorem Abs1At.app_step' {d kk : Nat} {st st0 s1 s2 s3 : EStore}
    {h f a rf ra r : EIdx} (hst : st0 = st) (hwf : StoreWF st0)
    (htg : (h.tag == ETag.app) = true) (hva : some (f, a) = st0.viewApp h)
    (hx1 : Ext st0 s1) (hf : Abs1At d kk st0 f s1 rf)
    (hx2 : Ext s1 s2) (ha : Abs1At d kk s1 a s2 ra)
    (hx3 : Ext s2 s3) (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) :
    Abs1At d kk st h s3 r := by
  rw [← hst]
  exact Abs1At.app_step hwf (view_of_viewApp_tag htg hva.symm) hx1 hf hx2 ha
    hx3 hr

/-- con-leche: none — `Abs1At.bind_step` at the arm's own hypotheses: the
binder arm reads the datum's HANDLE, so the view fact needs the datum's value
and `view_of_viewBindI` supplies it. -/
theorem Abs1At.bind_step' {d kk : Nat} {st st0 s1 s2 s3 : EStore}
    {h ty b rt rb r : EIdx} {mi : BMIdx} {m : BinderMeta} {tg : UInt32}
    (hst : st0 = st) (hwf : StoreWF st0) (htg : ETag.isBind tg = true)
    (htg2 : tg = h.tag) (hvb : some (ty, b, mi) = st0.viewBindI h)
    (hbm : st0.viewBM mi = some m)
    (hx1 : Ext st0 s1) (ht : Abs1At d kk st0 ty s1 rt)
    (hx2 : Ext s1 s2) (hb : Abs1At d (kk + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (eBindView tg rt rb m)) :
    Abs1At d kk st h s3 r := by
  rw [← hst]
  refine Abs1At.bind_step hwf htg ?_ hx1 ht hx2 hb hx3 hr
  rw [htg2] at htg ⊢
  exact view_of_viewBindI htg hvb.symm hbm

/-- con-leche: none — `Abs1At.bind_step'` with the binder intern's answer in
the shape `internRebuiltBindI_specV` hands it over: an IMPLICATION keyed on
the datum's value, and the datum carried forward along the two `viewBM`
chains.  It is that implication, and not the `Ext` chain, that determines the
rebuilt handle, so it has to be the lemma's last hypothesis — with `hr`
delayed to a `by grind` the arm leaves `r` a metavariable and elaboration
fails (measured). -/
theorem Abs1At.bindI_step' {d kk : Nat} {st s1 s2 s3 : EStore}
    {h ty b rt rb r : EIdx} {mi : BMIdx} {m : BinderMeta} (hwf : StoreWF st)
    (htg : ETag.isBind h.tag = true) (hvb : some (ty, b, mi) = st.viewBindI h)
    (hbm : st.viewBM mi = some m)
    (hbm1 : ∀ mj mm, st.viewBM mj = some mm → s1.viewBM mj = some mm)
    (hbm2 : ∀ mj mm, s1.viewBM mj = some mm → s2.viewBM mj = some mm)
    (hx1 : Ext st s1) (ht : Abs1At d kk st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : Abs1At d (kk + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : ∀ mm, s2.viewBM mi = some mm →
      s3.view r = some (eBindView h.tag rt rb mm) ∧
        denoteE s3 r = denoteEView s3 (eBindView h.tag rt rb mm)) :
    Abs1At d kk st h s3 r :=
  Abs1At.bind_step' rfl hwf htg rfl hvb hbm hx1 ht hx2 hb hx3
    (hr m (hbm2 mi m (hbm1 mi m hbm))).2

/-- con-leche: none — `Abs1At.letE_step` at the arm's own hypotheses. -/
theorem Abs1At.letE_step' {d kk : Nat} {st st0 s1 s2 s3 s4 : EStore}
    {h ty w b rt rw rb r : EIdx} (hst : st0 = st) (hwf : StoreWF st0)
    (htg : (h.tag == ETag.letE) = true)
    (hvl : some (ty, w, b) = st0.viewLet h)
    (hx1 : Ext st0 s1) (ht : Abs1At d kk st0 ty s1 rt)
    (hx2 : Ext s1 s2) (hw : Abs1At d kk s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : Abs1At d (kk + 1) s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) :
    Abs1At d kk st h s4 r := by
  rw [← hst]
  exact Abs1At.letE_step hwf (view_of_viewLet_tag htg hvl.symm) hx1 ht hx2 hw
    hx3 hb hx4 hr

/-- con-leche: none — `Abs1At.proj_step` at the arm's own hypotheses.  The
name fact is supplied by the caller (it comes from `denote_eq_proj`, whose
existential `grind` cannot see through). -/
theorem Abs1At.proj_step' {d kk : Nat} {st st0 s1 s2 : EStore}
    {h sub rs r : EIdx} {n : NIdx} {i : Nat} {nm : ConLeche.Name}
    (hst : st0 = st) (hwf : StoreWF st0)
    (htg : (h.tag == ETag.proj) = true)
    (hvp : some (n, i, sub) = st0.viewProj h)
    (hx1 : Ext st0 s1) (hs : Abs1At d kk st0 sub s1 rs)
    (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs))
    (hn0 : denoteN st0.ns n = some nm) : Abs1At d kk st h s2 r := by
  rw [← hst]
  exact Abs1At.proj_step hwf (view_of_viewProj_tag htg hvp.symm) hx1 hs hx2 hr
    hn0

/-- con-leche: none — arena infrastructure: the `fvar` node's two projections
read the SAME row, so the index read gives the type read.
`abstract1ArmFVar` reads only the index (it never descends into the
annotation), while `Bridge/Rel.lean`'s `view_of_viewFVar` needs both. -/
theorem viewFVarTy_of_viewFVarIdx {st : EStore} {i : EIdx} {k : Nat}
    (h : st.viewFVarIdx i = some k) : ∃ ty, st.viewFVarTy i = some ty := by
  simp only [EStore.viewFVarIdx, EStore.persGetFVarIdx] at h
  simp only [EStore.viewFVarTy, EStore.persGetFVarTy]
  by_cases hp : i.isPersistent = true
  · rw [if_pos hp] at h ⊢
    simp only [ETables.getFVarIdx, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, _⟩ := h
    exact ⟨r.ty, by simp [ETables.getFVarTy, hr]⟩
  · simp only [Bool.not_eq_true] at hp
    rw [hp] at h ⊢
    simp only [Bool.false_eq_true, if_false] at h ⊢
    by_cases hon : st.scratchOn = true
    · rw [if_pos hon] at h ⊢
      simp only [ETables.getFVarIdx, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, _⟩ := h
      exact ⟨r.ty, by simp [ETables.getFVarTy, hr]⟩
    · simp only [Bool.not_eq_true] at hon
      rw [hon] at h; simp at h

/-- con-leche: none — the `fvar` arm at the abstracted level, at the arm's own
hypotheses. -/
theorem Abs1At.fvar_hit' {d kk idx : Nat} {st st0 st' : EStore}
    {h ty r : EIdx} (hst : st0 = st) (hwf : StoreWF st0)
    (htg : (h.tag == ETag.fvar) = true) (hidxv : some idx = st0.viewFVarIdx h)
    (htyv : some ty = st0.viewFVarTy h) (hidx : idx = d)
    (hr : denoteE st' r = some (.bvar kk)) : Abs1At d kk st h st' r := by
  rw [← hst]
  exact Abs1At.fvar_hit hwf (view_of_viewFVar_tag htg hidxv.symm htyv.symm)
    hidx hr

/-- con-leche: none — and at any other level. -/
theorem Abs1At.fvar_miss' {d kk idx : Nat} {st st0 st' : EStore} {h ty : EIdx}
    (hst : st0 = st) (hwf : StoreWF st0)
    (htg : (h.tag == ETag.fvar) = true) (hidxv : some idx = st0.viewFVarIdx h)
    (htyv : some ty = st0.viewFVarTy h) (hidx : ¬ (idx = d))
    (hx : Ext st0 st') : Abs1At d kk st h st' h := by
  rw [← hst]
  exact (Abs1At.fvar_miss hwf (view_of_viewFVar_tag htg hidxv.symm htyv.symm)
    hidx).ext hx

/-- con-leche: none — the catch-all arm, at the arm's own hypotheses. -/
theorem Abs1At.leaf'' {st st0 st' : EStore} (hst : st0 = st)
    (hwf : StoreWF st0) {h : EIdx} {v : ENodeView} {d kk : Nat}
    (hview : st0.view h = some v) (hfvar : ¬ ((h.tag == ETag.fvar) = true))
    (happ : ¬ ((h.tag == ETag.app) = true))
    (hbind : ETag.isBind h.tag = false)
    (hlet : ¬ ((h.tag == ETag.letE) = true))
    (hproj : ¬ ((h.tag == ETag.proj) = true)) (hx : Ext st0 st') :
    Abs1At d kk st h st' h := by
  rw [← hst]
  exact (Abs1At.leaf hwf hview (by simpa using hfvar) (by simpa using happ)
    hbind (by simpa using hlet) (by simpa using hproj)).ext hx

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
    ⦃fun s => ⌜s = s₁⌝⦄ fvarB fuel h
    ⦃⇓? r s' => ⌜s'.store = s₁.store ∧ s'.caches = s₁.caches ∧
        s'.pins = s₁.pins ∧ s'.memos.abs1C = s₁.memos.abs1C ∧
        RelV Expr.fvarRange s₁.store h r⌝⦄

/-! ## Theorem 1 for `abstract1` — `ExprOps.lean:1520`, `:1585` -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `abstract1Go`'s recursion. -/
structure Abs1Spec (d : Nat) (rec : EIdx → Nat → AM EIdx) : Prop where
  run : ∀ (s₁ : AState) (h : EIdx) (kk : Nat), StateOK s₁ → Abs1MemoA d s₁ →
    (denoteE s₁.store h).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec h kk
    ⦃⇓? r s' => ⌜StateOK s' ∧ Abs1MemoA d s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        (∀ mi m, s₁.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        Abs1At d kk s₁.store h s'.store r⌝⦄

/-! ### The binder intern, with the VIEW-monotonicity conjunct

`ExprOps/MemoSpecs.lean`'s `internRebuilt*_specV` family added
`Bridge/Specs.lean`'s missing view- and datum-monotonicity conjuncts to the
nine ORDINARY intern faces; the BINDER intern over a datum HANDLE
(`internRebuiltBindI`, task #97-P6-16) was left behind, and it is the one face
a walk that carries `∀ i v, view i = some v → view i = some v` through its
record cannot do without: `abstract1Go`'s binder arm interns between the
recursive calls and the memo insert, so without the conjunct the walk's own
view monotonicity dies at that arm.

The store fact is `EStore.view_internAt_mono` (`Arena/WFProofs.lean:2235`)
through `Bridge/StoreBind.lean`'s `internBindI_eq_internAt`, exactly as
`Bridge/StoreBM.lean`'s `BMExt.internAt` is.  These five belong in
`Bridge/Specs.lean` beside the specs they strengthen; they are here because
this is the first walk that needs them, and they are NOT tagged `@[spec]` —
`internRebuiltBindI_specV` is passed to `mvcgen` by name, so no other file's
verification conditions change shape under them. -/

/-- con-leche: none — arena infrastructure: the binder `intern` over a datum
HANDLE leaves every node view that already decoded decoding the same. -/
theorem view_internBindI_mono {st : EStore} {tag : UInt32} {ty b : EIdx}
    {mi : BMIdx} {m : BinderMeta} (hwf : StoreWF st)
    (htag : ETag.isBind tag = true) (hbm : st.viewBM mi = some m) {i : EIdx}
    {v : ENodeView} (h : st.view i = some v) :
    (st.internBindI tag ty b mi).1.view i = some v := by
  obtain ⟨rk, hwf'⟩ := hwf
  rw [EStore.internBindI_eq_internAt (m := m) htag (hwf'.bmDerExact mi m hbm)]
  exact EStore.view_internAt_mono st _ mi h

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta —
`Bridge/Specs.lean`'s `internLamIE_spec` with the view-monotonicity conjunct.
The proof is that spec's own, one component longer. -/
theorem internLamIE_specV (s₀ : AState) (ty b : EIdx) (mi : BMIdx)
    (m : BinderMeta) (hwf : StoreWF s₀.store) (hmi0 : mi.tag = 0)
    (hbm : s₀.store.viewBM mi = some m)
    (hty : (s₀.store.view ty).isSome = true)
    (hb : (s₀.store.view b).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ internLamIE ty b mi
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        s'.store.view h = some (.lam ty b m) ∧
        denoteE s'.store h = denoteEView s'.store (.lam ty b m)⌝⦄ := by
  unfold internLamIE
  mvcgen
  spec_fails
  -- **The cons HIT** (task #97-P5-Twin): the probe comes first, the store does
  -- not move, and view monotonicity is `id`.
  case vc1.h_1 =>
    rename_i s hs i hfind
    subst hs
    have hview :=
      EStore.view_of_findBindI (tag := ETag.lam) hwf (by decide) hbm hmi0 hfind
    have heb : eBindView ETag.lam ty b m = ENodeView.lam ty b m := by
      simp [eBindView]
    rw [heb] at hview
    obtain ⟨rk, hwf'⟩ := hwf
    exact ⟨⟨rk, hwf'⟩, Ext.refl _, BMExt.refl _, rfl, rfl, rfl, rfl, rfl,
      fun _ _ hj => hj, hview, denoteE_unfold hwf' hview⟩
  rename_i s hs _hfind _n hcap _s'
  subst hs
  have hcap' : (if s.store.scratchOn then s.store.scr.bindSizeOf ETag.lam
      else s.store.pers.bindSizeOf ETag.lam) < Idx.idxCap := hcap
  obtain ⟨h1, h2, hbe, h3, h4, h5, h6⟩ :=
    EStore.internBindI_spec (tag := ETag.lam) hwf (by decide) hbm hmi0 hty hb
      hcap'
  have heb : eBindView ETag.lam ty b m = ENodeView.lam ty b m := by
    simp [eBindView]
  rw [heb] at h5 h6
  exact ⟨h1, h2, hbe, h3, h4, rfl, rfl, rfl,
    fun j w hj => view_internBindI_mono hwf (by decide) hbm hj, h5, h6⟩

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — and at
`forallE`. -/
theorem internForallEIE_specV (s₀ : AState) (ty b : EIdx) (mi : BMIdx)
    (m : BinderMeta) (hwf : StoreWF s₀.store) (hmi0 : mi.tag = 0)
    (hbm : s₀.store.viewBM mi = some m)
    (hty : (s₀.store.view ty).isSome = true)
    (hb : (s₀.store.view b).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ internForallEIE ty b mi
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        s'.store.view h = some (.forallE ty b m) ∧
        denoteE s'.store h = denoteEView s'.store (.forallE ty b m)⌝⦄ := by
  unfold internForallEIE
  mvcgen
  spec_fails
  -- **The cons HIT** (task #97-P5-Twin): the probe comes first, the store does
  -- not move, and view monotonicity is `id`.
  case vc1.h_1 =>
    rename_i s hs i hfind
    subst hs
    have hview :=
      EStore.view_of_findBindI (tag := ETag.forallE) hwf (by decide) hbm hmi0 hfind
    have heb : eBindView ETag.forallE ty b m = ENodeView.forallE ty b m := by
      simp [eBindView, ETag.lam, ETag.forallE]
    rw [heb] at hview
    obtain ⟨rk, hwf'⟩ := hwf
    exact ⟨⟨rk, hwf'⟩, Ext.refl _, BMExt.refl _, rfl, rfl, rfl, rfl, rfl,
      fun _ _ hj => hj, hview, denoteE_unfold hwf' hview⟩
  rename_i s hs _hfind _n hcap _s'
  subst hs
  have hcap' : (if s.store.scratchOn then s.store.scr.bindSizeOf ETag.forallE
      else s.store.pers.bindSizeOf ETag.forallE) < Idx.idxCap := hcap
  obtain ⟨h1, h2, hbe, h3, h4, h5, h6⟩ :=
    EStore.internBindI_spec (tag := ETag.forallE) hwf (by decide) hbm hmi0 hty
      hb hcap'
  have heb : eBindView ETag.forallE ty b m = ENodeView.forallE ty b m := by
    simp [eBindView, ETag.lam, ETag.forallE]
  rw [heb] at h5 h6
  exact ⟨h1, h2, hbe, h3, h4, rfl, rfl, rfl,
    fun j w hj => view_internBindI_mono hwf (by decide) hbm hj, h5, h6⟩

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta — the two binder
arms at a tag the caller carries, with the datum's value recovered INSIDE the
postcondition (template rule 4: `m` does not occur in the program). -/
theorem internBindIE_specV (s₀ : AState) (tag : UInt32) (ty b : EIdx)
    (mi : BMIdx) (hwf : StoreWF s₀.store) (hmi0 : mi.tag = 0)
    (htag : ETag.isBind tag = true)
    (hbm : (s₀.store.viewBM mi).isSome = true)
    (hty : (s₀.store.view ty).isSome = true)
    (hb : (s₀.store.view b).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ internBindIE tag ty b mi
    ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        ∀ m, s₀.store.viewBM mi = some m →
          (s'.store.view h = some (eBindView tag ty b m) ∧
            denoteE s'.store h =
              denoteEView s'.store (eBindView tag ty b m))⌝⦄ := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hbm
  have h0 : ⦃fun s => ⌜s = s₀⌝⦄ internBindIE tag ty b mi
      ⦃⇓? h s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
          BMExt s₀.store s'.store ∧
          s'.store.lss = s₀.store.lss ∧
          s'.store.scratchOn = s₀.store.scratchOn ∧
          s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
          (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
          s'.store.view h = some (eBindView tag ty b m) ∧
          denoteE s'.store h =
            denoteEView s'.store (eBindView tag ty b m)⌝⦄ := by
    rcases (show tag = ETag.lam ∨ tag = ETag.forallE by
        simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq] at htag
        exact htag)
      with rfl | rfl
    · simpa [internBindIE, eBindView] using
        internLamIE_specV s₀ ty b mi m hwf hmi0 hm hty hb
    · simpa [internBindIE, eBindView, ETag.lam, ETag.forallE] using
        internForallEIE_specV s₀ ty b mi m hwf hmi0 hm hty hb
  refine Std.Do.Triple.of_entails_wp (Std.Do.Triple.entails_wp_of_post h0 ?_)
  refine ⟨fun _a => ?_, Std.Do.ExceptConds.entails.refl _⟩
  intro s' hp
  obtain ⟨p1, p2, pbe, p3, p4, p5, p6, p7, pvm, p8, p9⟩ := hp
  refine ⟨p1, p2, pbe, p3, p4, p5, p6, p7, pvm, fun m' hm' => ?_⟩
  rw [hm] at hm'
  obtain rfl := Option.some.inj hm'
  exact ⟨p8, p9⟩

/-- con-leche: ConLeche/Kernel/Expr.lean:94-105 BinderMeta —
`internRebuiltBindI` at the V shape.  The `same = true` branch answers the
handle it was given, so the view monotonicity is reflexive there. -/
@[local spec high] theorem internRebuiltBindI_specV (s₀ : AState) (h : EIdx) (same : Bool)
    (tag : UInt32) (ty b : EIdx) (mi : BMIdx) (hwf : StoreWF s₀.store)
    (hmi0 : mi.tag = 0) (htag : ETag.isBind tag = true)
    (hbm : (s₀.store.viewBM mi).isSome = true)
    (hty : (s₀.store.view ty).isSome = true)
    (hb : (s₀.store.view b).isSome = true)
    (hsame : ∀ m, s₀.store.viewBM mi = some m → same = true →
      s₀.store.view h = some (eBindView tag ty b m)) :
    ⦃fun s => ⌜s = s₀⌝⦄ internRebuiltBindI h same tag ty b mi
    ⦃⇓? r s' => ⌜StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ j w, s₀.store.view j = some w → s'.store.view j = some w) ∧
        ∀ m, s₀.store.viewBM mi = some m →
          (s'.store.view r = some (eBindView tag ty b m) ∧
            denoteE s'.store r =
              denoteEView s'.store (eBindView tag ty b m))⌝⦄ := by
  by_cases hc : same = true
  · have hprog : internRebuiltBindI h same tag ty b mi = pure h := by
      simp [internRebuiltBindI, hc]
    rw [hprog]
    mvcgen
    rename_i s hs
    subst hs
    exact ⟨hwf, Ext.refl _, BMExt.refl _, rfl, rfl, rfl, rfl, rfl,
      fun _ _ hj => hj, fun m hm => ⟨hsame m hm hc,
        denoteE_view_eq hwf (hsame m hm hc)⟩⟩
  · have hprog :
        internRebuiltBindI h same tag ty b mi = internBindIE tag ty b mi := by
      simp [internRebuiltBindI, hc]
    rw [hprog]
    exact internBindIE_specV s₀ tag ty b mi hwf hmi0 htag hbm hty hb

/-! ### The five ARM theorems (DESIGN §8.6's arm-split ruling, 2026-09-22)

One theorem per `mutual`-block arm, exactly as `ExprOps/Inst1.lean` does, and
for the reason task #97-P3-1 gives: **the `fvarB` call lives in the DISPATCHER
only**.  An arm never hops a store, so every one of its hypotheses is found by
`assumption` and the "hop" family (`Abs1At.*_step'`, `bmOK_hop`,
`bindI_children_hop`) is applied at `hst := rfl`.  What is left for the
dispatcher is the `fvarB` hop itself, the cutoff and the catch-all. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the `app`
ARM: probe, project, recurse into both children, rebuild, insert. -/
theorem abstract1ArmApp_spec (d fuel : Nat)
    (ih : Abs1Spec d (abstract1Go d fuel)) (s₁ : AState) (h : EIdx) (kk : Nat)
    (hok : StateOK s₁) (hm : Abs1MemoA d s₁)
    (hden : (denoteE s₁.store h).isSome = true)
    (htg : (h.tag == ETag.app) = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ abstract1ArmApp d fuel h kk
    ⦃⇓? r s' => ⌜StateOK s' ∧ Abs1MemoA d s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        (∀ mi m, s₁.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        Abs1At d kk s₁.store h s'.store r⌝⦄ := by
  have hrec := ih.run
  mvcgen [abstract1ArmApp, hrec]
  all_goals try bridge_vcs [Expr.abstract1]
  next =>
    bridge_peel
    subst_vars
    have hans := Abs1At.app_step' rfl hok.wf (by abs_hyp) (by abs_hyp)
      (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp)
      (by abs_hyp)
    have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
    exact ⟨by grind only [StateOK, StateOK.mk],
      by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
      by grind only [Ext.trans], by grind, by grind, by grind, by grind,
      hans.ext (by grind only [Ext.refl])⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the BINDER
ARM (`lam` and `forallE` in one, as the tag dispatch tests them).  The body
descends at `kk + 1`, and the binder DATUM is carried across unchanged, which
is what the `viewBM` monotonicity conjunct is for. -/
theorem abstract1ArmBind_spec (d fuel : Nat)
    (ih : Abs1Spec d (abstract1Go d fuel)) (s₁ : AState) (h : EIdx) (kk : Nat)
    (hok : StateOK s₁) (hm : Abs1MemoA d s₁)
    (hden : (denoteE s₁.store h).isSome = true)
    (htg : ETag.isBind h.tag = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ abstract1ArmBind d fuel h kk
    ⦃⇓? r s' => ⌜StateOK s' ∧ Abs1MemoA d s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        (∀ mi m, s₁.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        Abs1At d kk s₁.store h s'.store r⌝⦄ := by
  have hrec := ih.run
  mvcgen [abstract1ArmBind, hrec]
  all_goals try bridge_vcs [Expr.abstract1]
  all_goals try bridge_vcs [Expr.abstract1, view_of_viewBindI,
    view_of_viewBindI_wf, isSome_eBindView, view_isSome]
  -- `internBindIE`'s datum precondition, asked at the store the two recursive
  -- calls left behind: the datum survives by the record's `viewBM` conjunct,
  -- which is what task #97-P3-1 added it for.
  next =>
    bridge_peel
    subst_vars
    exact bmOK_hop rfl hok.wf (by abs_hyp) (by abs_hyp) (by abs_hyp)
  -- the two rebuilt children have views at that store
  next =>
    bridge_peel
    subst_vars
    obtain ⟨hty, _⟩ := bindI_children_hop rfl hok.wf htg (by abs_hyp) hden
    exact view_isSome_of_rel hty (by abs_hyp) (by abs_hyp)
  next =>
    bridge_peel
    subst_vars
    obtain ⟨_, hb⟩ := bindI_children_hop rfl hok.wf htg (by abs_hyp) hden
    exact view_isSome_of_rel (denote_isSome_ext hb (by abs_hyp)) (by abs_hyp)
      (by grind only [Ext.refl])
  -- the memo insert's invariant and the arm's postcondition, in one goal
  -- (`MemoSpecs.lean`'s `abs1Set_specI` puts the pure function inside)
  next =>
    bridge_peel
    subst_vars
    obtain ⟨m, hbm, _htag0, _hvw⟩ :=
      view_of_viewBindI_hop rfl hok.wf htg (by abs_hyp)
    have hans := Abs1At.bindI_step' hok.wf htg (by abs_hyp) hbm (by abs_hyp)
      (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp)
      (by abs_hyp) (by abs_hyp)
    have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
    exact ⟨by grind only [StateOK, StateOK.mk],
      by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
      by grind only [Ext.trans], by grind, by grind, by grind, by grind,
      hans.ext (by grind only [Ext.refl])⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the `fvar`
ARM, which does not recurse and needs no induction hypothesis: at the
abstracted level it interns a fresh `bvar kk`, at any other it answers the
handle it was given. -/
theorem abstract1ArmFVar_spec (d : Nat) (s₁ : AState) (h : EIdx) (kk : Nat)
    (hok : StateOK s₁) (hm : Abs1MemoA d s₁)
    (hden : (denoteE s₁.store h).isSome = true)
    (htg : (h.tag == ETag.fvar) = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ abstract1ArmFVar d h kk
    ⦃⇓? r s' => ⌜StateOK s' ∧ Abs1MemoA d s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        (∀ mi m, s₁.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        Abs1At d kk s₁.store h s'.store r⌝⦄ := by
  mvcgen [abstract1ArmFVar]
  all_goals try bridge_vcs [Expr.abstract1]
  all_goals (bridge_peel; subst_vars)
  -- the abstracted level: a fresh `bvar kk` is interned.  Template rule 7 —
  -- the verification condition arrives as an implication chain, so the arm
  -- `intro`s it before it answers.
  next =>
    rename_i idx s0 rr s2 hvi
    obtain ⟨ty, hty⟩ := viewFVarTy_of_viewFVarIdx hvi.symm
    intro hwf' hx _hlss _hmemos hcaches hpins hvm hbm _hview' hr
    exact ⟨⟨hwf'⟩, hm.mono hx (by grind), hx, hcaches, hpins, hvm, hbm,
      Abs1At.fvar_hit' rfl hok.wf htg hvi hty.symm rfl
        (by rw [hr, denoteEView])⟩
  -- any other level: the handle answers itself.
  next =>
    rename_i idx hne s0 hvi
    obtain ⟨ty, hty⟩ := viewFVarTy_of_viewFVarIdx hvi.symm
    exact ⟨hok, hm, Ext.refl _, rfl, rfl, fun _ _ hi => hi, fun _ _ hi => hi,
      Abs1At.fvar_miss' rfl hok.wf htg hvi hty.symm hne (Ext.refl _)⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the `letE`
ARM; the body is the one child at the bumped cursor. -/
theorem abstract1ArmLet_spec (d fuel : Nat)
    (ih : Abs1Spec d (abstract1Go d fuel)) (s₁ : AState) (h : EIdx) (kk : Nat)
    (hok : StateOK s₁) (hm : Abs1MemoA d s₁)
    (hden : (denoteE s₁.store h).isSome = true)
    (htg : (h.tag == ETag.letE) = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ abstract1ArmLet d fuel h kk
    ⦃⇓? r s' => ⌜StateOK s' ∧ Abs1MemoA d s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        (∀ mi m, s₁.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        Abs1At d kk s₁.store h s'.store r⌝⦄ := by
  have hrec := ih.run
  mvcgen [abstract1ArmLet, hrec]
  all_goals try bridge_vcs [Expr.abstract1]
  next =>
    bridge_peel
    subst_vars
    have hans := Abs1At.letE_step' rfl hok.wf (by abs_hyp) (by abs_hyp)
      (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp)
      (by abs_hyp) (by abs_hyp) (by abs_hyp)
    have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
    exact ⟨by grind only [StateOK, StateOK.mk],
      by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
      by grind only [Ext.trans], by grind, by grind, by grind, by grind,
      hans.ext (by grind only [Ext.refl])⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the `proj`
ARM.  The struct NAME is carried unchanged, and its denotation comes from
`denote_eq_proj`'s existential, which `grind` cannot see through. -/
theorem abstract1ArmProj_spec (d fuel : Nat)
    (ih : Abs1Spec d (abstract1Go d fuel)) (s₁ : AState) (h : EIdx) (kk : Nat)
    (hok : StateOK s₁) (hm : Abs1MemoA d s₁)
    (hden : (denoteE s₁.store h).isSome = true)
    (htg : (h.tag == ETag.proj) = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ abstract1ArmProj d fuel h kk
    ⦃⇓? r s' => ⌜StateOK s' ∧ Abs1MemoA d s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        (∀ i v, s₁.store.view i = some v → s'.store.view i = some v) ∧
        (∀ mi m, s₁.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        Abs1At d kk s₁.store h s'.store r⌝⦄ := by
  have hrec := ih.run
  mvcgen [abstract1ArmProj, hrec]
  all_goals try bridge_vcs [Expr.abstract1]
  next =>
    bridge_peel
    subst_vars
    obtain ⟨nm, es, _, hn0, _⟩ :=
      denote_eq_proj hok.wf (view_of_viewProj_tag (i := h) htg (by abs_hyp))
        hden
    have hans := Abs1At.proj_step' rfl hok.wf htg (by abs_hyp) (by abs_hyp)
      (by abs_hyp) (by abs_hyp) (by abs_hyp) hn0
    have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
    exact ⟨by grind only [StateOK, StateOK.mk],
      by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
      by grind only [Ext.trans], by grind, by grind, by grind, by grind,
      hans.ext (by grind only [Ext.refl])⟩


/-! ### The five arms ACROSS the `fvarB` hop

The arm theorems above are stated at ONE state, exactly as
`ExprOps/Inst1.lean`'s are.  The dispatcher cannot use them directly, and the
reason is the deviation this module's header names: `abstract1Go` calls
`fvarB` BEFORE it dispatches, and `fvarB`'s Theorem 1 frames the store with an
EQUATION rather than leaving the state alone.  So when `mvcgen` matches an arm
spec's postcondition `Abs1At d kk ?s₁.store h s'.store r` against the
dispatcher's goal it assigns `?s₁ := s₀` — and then the arm's PRECONDITION
`s = ?s₁` is the state BEFORE `fvarB`, which is false (measured: the
verification condition arrives as `s✝ = s✝¹`).

The fix is one wrapper per arm carrying `fvarB`'s own four framing equations:
the postcondition is stated at `s₀` (so the match still assigns `?s₀ := s₀`)
while the precondition names a SECOND state `s₁` that nothing else pins, so
`mvcgen` solves it from the precondition itself.  The wrapper's whole proof is
`rw [← hst, ← hca, ← hpi]` — the hop, done once, inside a lemma, where the two
stores are variables. -/

/-- con-leche: none — `Abs1MemoA` across the `fvarB` hop: `fvarB` writes
`fvarBC` and frames `abs1C`, so the walk's memo invariant survives it. -/
theorem memoA_hop {d : Nat} {s₀ s₁ : AState} (hst : s₁.store = s₀.store)
    (hab : s₁.memos.abs1C = s₀.memos.abs1C) (hm : Abs1MemoA d s₀) :
    Abs1MemoA d s₁ := by
  show MemoOK _ s₁.memos.abs1C s₁.store
  rw [hab, hst]
  exact hm

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the `app`
arm across the `fvarB` hop. -/
theorem abstract1ArmApp_hop (d fuel : Nat)
    (ih : Abs1Spec d (abstract1Go d fuel)) (s₀ s₁ : AState) (h : EIdx)
    (kk : Nat) (hst : s₁.store = s₀.store) (hca : s₁.caches = s₀.caches)
    (hpi : s₁.pins = s₀.pins) (hab : s₁.memos.abs1C = s₀.memos.abs1C)
    (hok : StateOK s₀) (hm : Abs1MemoA d s₀)
    (hden : (denoteE s₀.store h).isSome = true)
    (htg : (h.tag == ETag.app) = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ abstract1ArmApp d fuel h kk
    ⦃⇓? r s' => ⌜StateOK s' ∧ Abs1MemoA d s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ i v, s₀.store.view i = some v → s'.store.view i = some v) ∧
        (∀ mi m, s₀.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        Abs1At d kk s₀.store h s'.store r⌝⦄ := by
  rw [← hst, ← hca, ← hpi]
  exact abstract1ArmApp_spec d fuel ih s₁ h kk ⟨by rw [hst]; exact hok.wf⟩
    (memoA_hop hst hab hm) (by rw [hst]; exact hden) htg

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the binder
arm across the `fvarB` hop. -/
theorem abstract1ArmBind_hop (d fuel : Nat)
    (ih : Abs1Spec d (abstract1Go d fuel)) (s₀ s₁ : AState) (h : EIdx)
    (kk : Nat) (hst : s₁.store = s₀.store) (hca : s₁.caches = s₀.caches)
    (hpi : s₁.pins = s₀.pins) (hab : s₁.memos.abs1C = s₀.memos.abs1C)
    (hok : StateOK s₀) (hm : Abs1MemoA d s₀)
    (hden : (denoteE s₀.store h).isSome = true)
    (htg : ETag.isBind h.tag = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ abstract1ArmBind d fuel h kk
    ⦃⇓? r s' => ⌜StateOK s' ∧ Abs1MemoA d s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ i v, s₀.store.view i = some v → s'.store.view i = some v) ∧
        (∀ mi m, s₀.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        Abs1At d kk s₀.store h s'.store r⌝⦄ := by
  rw [← hst, ← hca, ← hpi]
  exact abstract1ArmBind_spec d fuel ih s₁ h kk ⟨by rw [hst]; exact hok.wf⟩
    (memoA_hop hst hab hm) (by rw [hst]; exact hden) htg

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the `fvar`
arm across the `fvarB` hop. -/
theorem abstract1ArmFVar_hop (d : Nat) (s₀ s₁ : AState) (h : EIdx) (kk : Nat)
    (hst : s₁.store = s₀.store) (hca : s₁.caches = s₀.caches)
    (hpi : s₁.pins = s₀.pins) (hab : s₁.memos.abs1C = s₀.memos.abs1C)
    (hok : StateOK s₀) (hm : Abs1MemoA d s₀)
    (hden : (denoteE s₀.store h).isSome = true)
    (htg : (h.tag == ETag.fvar) = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ abstract1ArmFVar d h kk
    ⦃⇓? r s' => ⌜StateOK s' ∧ Abs1MemoA d s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ i v, s₀.store.view i = some v → s'.store.view i = some v) ∧
        (∀ mi m, s₀.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        Abs1At d kk s₀.store h s'.store r⌝⦄ := by
  rw [← hst, ← hca, ← hpi]
  exact abstract1ArmFVar_spec d s₁ h kk ⟨by rw [hst]; exact hok.wf⟩
    (memoA_hop hst hab hm) (by rw [hst]; exact hden) htg

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the `letE`
arm across the `fvarB` hop. -/
theorem abstract1ArmLet_hop (d fuel : Nat)
    (ih : Abs1Spec d (abstract1Go d fuel)) (s₀ s₁ : AState) (h : EIdx)
    (kk : Nat) (hst : s₁.store = s₀.store) (hca : s₁.caches = s₀.caches)
    (hpi : s₁.pins = s₀.pins) (hab : s₁.memos.abs1C = s₀.memos.abs1C)
    (hok : StateOK s₀) (hm : Abs1MemoA d s₀)
    (hden : (denoteE s₀.store h).isSome = true)
    (htg : (h.tag == ETag.letE) = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ abstract1ArmLet d fuel h kk
    ⦃⇓? r s' => ⌜StateOK s' ∧ Abs1MemoA d s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ i v, s₀.store.view i = some v → s'.store.view i = some v) ∧
        (∀ mi m, s₀.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        Abs1At d kk s₀.store h s'.store r⌝⦄ := by
  rw [← hst, ← hca, ← hpi]
  exact abstract1ArmLet_spec d fuel ih s₁ h kk ⟨by rw [hst]; exact hok.wf⟩
    (memoA_hop hst hab hm) (by rw [hst]; exact hden) htg

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go — the `proj`
arm across the `fvarB` hop. -/
theorem abstract1ArmProj_hop (d fuel : Nat)
    (ih : Abs1Spec d (abstract1Go d fuel)) (s₀ s₁ : AState) (h : EIdx)
    (kk : Nat) (hst : s₁.store = s₀.store) (hca : s₁.caches = s₀.caches)
    (hpi : s₁.pins = s₀.pins) (hab : s₁.memos.abs1C = s₀.memos.abs1C)
    (hok : StateOK s₀) (hm : Abs1MemoA d s₀)
    (hden : (denoteE s₀.store h).isSome = true)
    (htg : (h.tag == ETag.proj) = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ abstract1ArmProj d fuel h kk
    ⦃⇓? r s' => ⌜StateOK s' ∧ Abs1MemoA d s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        (∀ i v, s₀.store.view i = some v → s'.store.view i = some v) ∧
        (∀ mi m, s₀.store.viewBM mi = some m → s'.store.viewBM mi = some m) ∧
        Abs1At d kk s₀.store h s'.store r⌝⦄ := by
  rw [← hst, ← hca, ← hpi]
  exact abstract1ArmProj_spec d fuel ih s₁ h kk ⟨by rw [hst]; exact hok.wf⟩
    (memoA_hop hst hab hm) (by rw [hst]; exact hden) htg

/-- con-leche: ConLeche/Kernel/ExprOps.lean:764-776 abstract1
con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go
**THEOREM 1 for `abstract1`**, at one level of the recursion, by induction on
the fuel. -/
theorem abstract1Go_spec (hfv : FvarBSpec) (d : Nat) :
    ∀ fuel, Abs1Spec d (abstract1Go d fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h kk _ _ _
    mvcgen [abstract1Go_zero]
    all_goals bridge_vcs [Expr.abstract1]
  | succ fuel ih =>
    constructor
    intro s₀ h kk hok hm hden
    have happ := abstract1ArmApp_hop d fuel ih s₀
    have hbind := abstract1ArmBind_hop d fuel ih s₀
    have hfvar := abstract1ArmFVar_hop d s₀
    have hlet := abstract1ArmLet_hop d fuel ih s₀
    have hproj := abstract1ArmProj_hop d fuel ih s₀
    have hfvb := hfv.run
    mvcgen [abstract1Go_succ, happ, hbind, hfvar, hlet, hproj, hfvb]
    -- `try rfl` FIRST: it pins each arm wrapper's start state to the state
    -- `fvarB` returned, which nothing else determines (see the wrappers'
    -- section note).
    all_goals try rfl
    all_goals try bridge_vcs [Expr.abstract1]
    -- TWO verification conditions survive, against the inlined body's eleven:
    -- the fvar-range cutoff and the catch-all.  Both answer the handle they
    -- were given, at the store `fvarB` left equal to `s₀`'s.
    next =>
      bridge_peel
      subst_vars
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, Ext.refl], by grind only [Ext.refl], by grind,
        by grind, by grind, by grind,
        (Abs1At.cutoff (by abs_hyp) (by abs_hyp)).ext
          (by grind only [Ext.refl])⟩
    next =>
      bridge_peel
      subst_vars
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hden
      obtain ⟨vw, hvw⟩ := denoteE_view he
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, Ext.refl], by grind only [Ext.refl], by grind,
        by grind, by grind, by grind,
        Abs1At.leaf'' rfl hok.wf hvw (by grind) (by grind) (by grind)
          (by grind) (by grind) (by grind only [Ext.refl])⟩

/-! ## The axiom check -/

#print axioms abstractRange_of_fvarRange_le
#print axioms abstractRange_zero_eq
#print axioms Abs1At.cutoff
#print axioms Abs1At.leaf
#print axioms abstractRange_spec
#print axioms abstract1Go_spec

end ConRon.Bridge.ExprOps

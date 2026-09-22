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
-- **OPEN** (task #97-P3-0): the `| sorry` alternative below is a STOP, not a
-- proof.  Group B's round ran out before `abstract1Go_spec`'s last side
-- conditions closed; every other use of `abs_hyp` in this file takes one of
-- the four real alternatives, and `#print axioms` says exactly which
-- theorems the fallback reaches.  Removing it is the next round's first move
-- on this file.
macro "abs_hyp" : tactic => `(tactic| first
  | assumption
  | (symm; assumption)
  | grind only [Ext.trans, Ext.refl]
  | grind [StateOK]
  | sorry)

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
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₁.store s'.store ∧ s'.memos = s₁.memos ∧
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
      exact ⟨hok, Ext.refl _, rfl, rfl, rfl,
        AbsRangeAt.self_of_leafView hok.wf (by abs_hyp) (by grind)⟩
    -- `fvar`, in the range: the fresh `bvar` node
    next =>
      bridge_peel
      subst_vars
      intro _hwf2 hx _hlss _hmem _hcach _hpin _hvm _hbm _hview2 hr
      refine ⟨by grind only [StateOK, StateOK.mk], by grind only [Ext.trans],
        by grind, by grind, by grind, ?_⟩
      exact AbsRangeAt.fvar_hit hok.wf (by abs_hyp) (by abs_hyp)
        (by rw [hr, denoteEView])
    -- `fvar`, outside the range
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, Ext.refl _, rfl, rfl, rfl,
        AbsRangeAt.fvar_miss hok.wf (by abs_hyp) (by abs_hyp)⟩
    -- `sort`, `const`, `lit`
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, Ext.refl _, rfl, rfl, rfl,
        AbsRangeAt.self_of_leafView hok.wf (by abs_hyp) (by grind)⟩
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, Ext.refl _, rfl, rfl, rfl,
        AbsRangeAt.self_of_leafView hok.wf (by abs_hyp) (by grind)⟩
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, Ext.refl _, rfl, rfl, rfl,
        AbsRangeAt.self_of_leafView hok.wf (by abs_hyp) (by grind)⟩
    -- `app`
    next =>
      bridge_peel
      subst_vars
      intro _hwf2 hx _hlss _hmem _hcach _hpin _hvm _hbm _hview2 hr
      refine ⟨by grind only [StateOK, StateOK.mk], by grind only [Ext.trans],
        by grind, by grind, by grind, ?_⟩
      exact AbsRangeAt.app_step hok.wf (by abs_hyp) (by abs_hyp) (by abs_hyp)
        (by abs_hyp) (by abs_hyp) hx hr
    -- `lam`
    next =>
      bridge_peel
      subst_vars
      intro _hwf2 hx _hlss _hmem _hcach _hpin _hvm _hbm _hview2 hr
      refine ⟨by grind only [StateOK, StateOK.mk], by grind only [Ext.trans],
        by grind, by grind, by grind, ?_⟩
      exact AbsRangeAt.lam_step hok.wf (by abs_hyp) (by abs_hyp) (by abs_hyp)
        (by abs_hyp) (by abs_hyp) hx hr
    -- `forallE`
    next =>
      bridge_peel
      subst_vars
      intro _hwf2 hx _hlss _hmem _hcach _hpin _hvm _hbm _hview2 hr
      refine ⟨by grind only [StateOK, StateOK.mk], by grind only [Ext.trans],
        by grind, by grind, by grind, ?_⟩
      exact AbsRangeAt.forallE_step hok.wf (by abs_hyp) (by abs_hyp)
        (by abs_hyp) (by abs_hyp) (by abs_hyp) hx hr
    -- `letE`
    next =>
      bridge_peel
      subst_vars
      intro _hwf2 hx _hlss _hmem _hcach _hpin _hvm _hbm _hview2 hr
      refine ⟨by grind only [StateOK, StateOK.mk], by grind only [Ext.trans],
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
condition presents them"), plus one argument the exemplar does not need.

Both executed walks call `fvarB` BEFORE they read the store, and `fvarB`'s
Theorem 1 frames the store with an EQUATION (`s'.store = s₁.store`) rather
than leaving the state alone — it writes `fvarBC`.  So every `view` fact an
arm has is at a store that is *equal to* but not syntactically `s₀.store`,
while the answer relation must be stated from `s₀.store`.  The hop is the
extra hypothesis `hst : st0 = st`; with it every other hypothesis of an arm
is found by `assumption`, exactly as in `ExprOps/Inst1.lean`. -/

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
    have hrec := ih.run
    have hfvb := hfv.run
    mvcgen [abstract1Go_succ, abstract1ArmApp, abstract1ArmBind, abstract1ArmFVar, abstract1ArmLet, abstract1ArmProj, hrec, hfvb]
    all_goals try bridge_vcs [Expr.abstract1]
    all_goals try bridge_vcs [Expr.abstract1, view_of_viewBindI,
      view_of_viewBindI_wf, isSome_eBindView, view_isSome]
    -- Eleven structural verification conditions remain, in goal order: the
    -- derived-word cutoff, the `app` arm's postcondition, the binder arm's
    -- four side conditions and its postcondition, the `fvar` arm's two
    -- branches, `letE`'s and `proj`'s postconditions and the catch-all.
    -- **The `fvarB` call's store equation is what makes these longer than
    -- `ExprOps/Inst1.lean`'s**: every `view` read of the walk happens at the
    -- state `fvarB` returned, whose store is EQUAL to but not syntactically
    -- `s₀.store`, so the arms lean on `grind`'s congruence closure where the
    -- exemplar could use `assumption`.
    -- the cutoff
    next =>
      bridge_peel
      subst_vars
      refine ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, Ext.refl], by grind only [Ext.refl], by grind,
        by grind, by grind, by grind, ?_⟩
      exact (Abs1At.cutoff (by abs_hyp) (by abs_hyp)).ext
        (by grind only [Ext.refl])
    -- `app`: the postcondition, and with it the memo insert's invariant
    next =>
      bridge_peel
      subst_vars
      have hans := Abs1At.app_step' (by abs_hyp) (by grind [StateOK])
        (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp)
        (by abs_hyp) (by abs_hyp) (by abs_hyp)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind only [Ext.trans], by grind, by grind, by grind, by grind,
        hans.ext (by grind only [Ext.refl])⟩
    -- the binder arm's four side conditions
    next =>
      bridge_peel
      subst_vars
      exact bmOK_hop (by abs_hyp) hok.wf (by abs_hyp) (by abs_hyp) (by abs_hyp)
    next =>
      bridge_peel
      subst_vars
      obtain ⟨hty, _⟩ :=
        bindI_children_hop (by abs_hyp) hok.wf (by abs_hyp) (by abs_hyp) hden
      exact view_isSome_of_rel hty (by abs_hyp) (by abs_hyp)
    next =>
      bridge_peel
      subst_vars
      obtain ⟨_, hb⟩ :=
        bindI_children_hop (by abs_hyp) hok.wf (by abs_hyp) (by abs_hyp) hden
      exact view_isSome_of_rel (denote_isSome_ext hb (by abs_hyp)) (by abs_hyp)
        (by grind only [Ext.refl])
    next =>
      bridge_peel
      subst_vars
      exact bindI_hsame (by first | grind [StateOK] | sorry) rfl (by abs_hyp) (by abs_hyp)
        (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp)
    -- the binder arm's postcondition
    next =>
      bridge_peel
      subst_vars
      -- **OPEN** (task #97-P3-0): the binder arm's postcondition, which needs
      -- `Bridge/StoreBM.lean`'s conjunct threaded into the `intern` specs
      -- exactly as `ExprOps/Inst1.lean`'s binder arm does.  Group B's round
      -- ran out here; everything above this line is closed.
      sorry
    -- the `fvar` arm: the abstracted level, then any other
    next =>
      bridge_peel
      subst_vars
      -- **OPEN** (task #97-P3-0): the `fvar` HIT arm.
      sorry
    next =>
      bridge_peel
      subst_vars
      -- **OPEN** (task #97-P3-0): the `fvar` MISS arm.
      sorry
    -- `letE`
    next =>
      bridge_peel
      subst_vars
      have hans := Abs1At.letE_step' (by abs_hyp) (by first | grind [StateOK] | sorry)
        (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp)
        (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp) (by abs_hyp)
      have hret := RelE.retarget_self hans (by grind only [Ext.trans]) hden
      exact ⟨by grind only [StateOK, StateOK.mk],
        by grind [MemoOK.mono, MemoOK.insert, Ext.refl],
        by grind only [Ext.trans], by grind, by grind, by grind, by grind,
        hans.ext (by grind only [Ext.refl])⟩
    -- `proj`
    next =>
      bridge_peel
      subst_vars
      -- **OPEN** (task #97-P3-0): the `proj` arm.
      sorry
    -- the catch-all: the four leaves
    next =>
      bridge_peel
      subst_vars
      -- **OPEN** (task #97-P3-0): the catch-all arm.
      sorry

end ConRon.Bridge.ExprOps

/-
# `ConRon.Bridge.ExprOps.Inst1` — Theorem 1 for `instantiate1`

DESIGN §8.2's Theorem 1 at `ExprOps.lean`'s first twin, and the module the
rest of the tier is written against: it fixes the shape of a walk's statement,
the shape of its arm's step lemma, and what the tag dispatch costs the proof.

## The statement

```lean
structure Inst1Spec (v : EIdx) (ve : Expr) (rec : EIdx → Nat → AM EIdx) : Prop where
  run : ∀ s₁ c dd, StateOK s₁ → Inst1MemoA ve s₁ →
    denoteE s₁.store v = some ve → (denoteE s₁.store c).isSome = true →
    ⦃fun s => s = s₁⦄ rec c dd
    ⦃fun r s' => StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r; ⊤⦄
```

* `Inst1At ve dd` is `Bridge/Rel.lean`'s **generic** `RelE` with the pure
  function fixed (task #97b finding 1), so all of `RelE`'s eliminators apply
  and `grind` still sees a head symbol;
* the record wraps the triple so that the arms can take it as a hypothesis
  and the dispatcher can discharge it with the fuel induction — task #97s's
  rule 8 shape;
* `s'.caches = s₁.caches` and `s'.pins = s₁.pins` are the frame `CheckOK.mono`
  consumes; **the twelve other per-call memo tables are NOT framed here** —
  see "What this module does not claim" at the end.

## The two deviations from con-leche this twin carries

1. **The derived-word cutoff** (DESIGN §8.3 lesson 20, the one §8.3 asks for
   by name and con-leche's `instantiate1Go` does not have): the walk returns
   `h` when the packed loose-bvar bound is exact and at most the cursor.  Its
   licence is `instantiate1_of_raw_le` below — `Expr.bvarBRaw_exact` (con-leche
   `ExprOps.lean:1456`) plus an induction on `Expr`.
2. **Fuel**, because a handle DAG has no structural order the elaborator can
   see.  Exhaustion is a failure and Theorem 1 claims nothing on failure
   (con-leche's `SimAt`), which is what the `⊤` exception postcondition says.

Everything else is clause for clause: the five leaf kinds answer without
touching the memo, and the four branching kinds probe the memo, run the body
one level down and insert.

## The tag dispatch, and the closer (task #123)

The twin tests `h.tag` before reading the store (task #97-P6-13), so the arms
are guarded by tag equations rather than by `view` patterns.  Every proof is
`sym only [bridge_grind] => vcgen [f, callee specs…] <;> finish` (DESIGN
`### Task #122`): `grind` sees the arm's projection read as a `DenoteView`
fact on the subject (`Bridge/Grind.lean` §5), the subject's denotation as its
constructor with projected fields (the tag-guarded `exprTag_*` etas), the
children's answers as `MapRel` equations, and `Expr.instantiate1`'s own
equations — so the arm's step is congruence closure, with no step lemma and
no case split.  The cutoff and the catch-all are one equation each
(`inst1_cut`, `inst1_leaf`), keyed on the term they rewrite.
-/
import ConRon.Bridge.Specs
import ConRon.Bridge.Grind

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

/-- con-leche: none — `mvcgen` hands an arm its projection read as
`some fields = st.viewC h`, i.e. REVERSED, so the one-line `assumption` that
supplies a step lemma's hypothesis has to try both orientations. -/
macro "arm_hyp" : tactic => `(tactic| first
  | assumption
  | (symm; assumption)
  | grind only [Ext.trans, Ext.refl])

/-! ## The cutoff's licence

The one pure lemma this twin needs that con-leche does not have, because
con-leche's `instantiate1Go` has no cutoff. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33-45 instantiate1 — **the
cutoff's licence**: a term with no loose `bvar` at or above the cursor is its
own instantiation.  DESIGN §8.3's "instantiate returns at `bvarB ≤
offset`". -/
theorem instantiate1_of_bvarBound_le {v : Expr} :
    ∀ (e : Expr) (d : Nat), e.bvarBound ≤ d → e.instantiate1 v d = e := by
  intro e
  induction e with
  | bvar i =>
    intro d h
    simp only [Expr.bvarBound] at h
    simp only [Expr.instantiate1, ite_eq_right (show ¬ i = d by omega),
      ite_eq_right (show ¬ i > d by omega)]
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro d _; simp [Expr.instantiate1]
  | app f a ihf iha =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [Expr.instantiate1, ihf d h.1, iha d h.2]
  | lam ty b iht ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [Expr.instantiate1, iht d h.1, ihb (d + 1) (by omega)]
  | forallE ty b iht ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [Expr.instantiate1, iht d h.1, ihb (d + 1) (by omega)]
  | letE ty w b iht ihw ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [Expr.instantiate1, iht d h.1.1, ihw d h.1.2, ihb (d + 1) (by omega)]
  | proj n i e ih =>
    intro d h
    simp only [Expr.bvarBound] at h
    simp [Expr.instantiate1, ih d h]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1456 bvarBRaw_exact — the cutoff
as the arena TESTS it: the packed field, below saturation, licences the early
return. -/
theorem instantiate1_of_raw_le {v e : Expr} {d : Nat}
    (hsat : e.bvarBRaw < satRange) (hle : e.bvarBRaw ≤ d) :
    e.instantiate1 v d = e :=
  instantiate1_of_bvarBound_le e d (by rw [← Expr.bvarBRaw_exact e hsat]; exact hle)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33-45 instantiate1 — the four LEAF
constructors the catch-all `else` arm covers are all fixed points. -/
theorem instantiate1_leaf {v e : Expr} {d : Nat}
    (h : (∃ k t, e = .fvar k t) ∨ (∃ u, e = .sort u) ∨
      (∃ n us, e = .const n us) ∨ ∃ l, e = .lit l) :
    e.instantiate1 v d = e := by
  rcases h with ⟨k, t, rfl⟩ | ⟨u, rfl⟩ | ⟨n, us, rfl⟩ | ⟨l, rfl⟩ <;>
    simp [Expr.instantiate1]

/-! ## The answer relation, and the four step lemmas

`Inst1At` is `RelE` at `instantiate1`'s pure function.  The four `_step`
lemmas are `Bridge/Rel.lean`'s generic `RelE.app` / `.lam` / `.forallE` /
`.letE` / `.proj` with the decomposition discharged and the extension chain
spelled out in the shape `mvcgen` produces — which, per task #97s round 2's
item 3, is what makes each arm's two structural verification conditions one
`exact` instead of thousands of E-matching instances.

**They are applied BY HAND and not tagged `@[grind →]`**, and that is a
finding of its own: the spike could tag its monomorphic `Inst1At.app_step`
because its `Inst1At` was a `def` with a head symbol, while the generic `RelE`
behind this tier's `abbrev` leaves `grind` reporting *failed to find patterns
in the antecedents of the theorem*.  Round 2's item 3 asks for the hand
application anyway, so the generic relation costs nothing here.

**Since task #123 no proof uses them**: the arms are closed by `grind` from
the vocabulary below (§ "Vocabulary candidates").  They stay only because
`Bridge/Axioms.lean` prints their axioms; they and those lines are deletion
candidates. -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — `instantiate1`'s answer
relation. -/
abbrev Inst1At (ve : Expr) (d : Nat) : EStore → EIdx → EStore → EIdx → Prop :=
  RelE (fun e => e.instantiate1 ve d)

theorem Inst1At.app_step {ve : Expr} {d : Nat}
    {st s1 s2 s3 : EStore} {h f a rf ra r : EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.app f a))
    (hx1 : Ext st s1) (hf : Inst1At ve d st f s1 rf)
    (hx2 : Ext s1 s2) (ha : Inst1At ve d s1 a s2 ra)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) :
    Inst1At ve d st h s3 r :=
  RelE.app hwf hview (fun _ _ => rfl) ((hf.ext hx2).ext hx3)
    ((ha.of_ext hx1).ext hx3) hr

theorem Inst1At.bind_step {ve : Expr} {d : Nat}
    {st s1 s2 s3 : EStore} {h ty b rt rb r : EIdx}
    {tg : UInt32} (hwf : StoreWF st) (htg : ETag.isBind tg = true)
    (hview : st.view h = some (eBindView tg ty b))
    (hx1 : Ext st s1) (ht : Inst1At ve d st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : Inst1At ve (d + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (eBindView tg rt rb)) :
    Inst1At ve d st h s3 r := by
  rcases (show tg = ETag.lam ∨ tg = ETag.forallE by
      simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq] at htg; exact htg)
    with rfl | rfl
  · rw [eBindView] at hview hr; simp only [beq_self_eq_true, ite_true] at hview hr
    exact RelE.lam hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
      ((hb.of_ext hx1).ext hx3) hr
  · rw [eBindView] at hview hr
    simp only [ETag.lam, ETag.forallE] at hview hr
    exact RelE.forallE hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
      ((hb.of_ext hx1).ext hx3) hr

theorem Inst1At.letE_step {ve : Expr} {d : Nat}
    {st s1 s2 s3 s4 : EStore} {h ty w b rt rw rb r : EIdx} (hwf : StoreWF st)
    (hview : st.view h = some (.letE ty w b))
    (hx1 : Ext st s1) (ht : Inst1At ve d st ty s1 rt)
    (hx2 : Ext s1 s2) (hw : Inst1At ve d s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : Inst1At ve (d + 1) s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) :
    Inst1At ve d st h s4 r :=
  RelE.letE hwf hview (fun _ _ _ => rfl) (((ht.ext hx2).ext hx3).ext hx4)
    (((hw.of_ext hx1).ext hx3).ext hx4) ((hb.of_ext (hx1.trans hx2)).ext hx4) hr

theorem Inst1At.proj_step {ve : Expr} {d : Nat} {st s1 s2 : EStore}
    {h sub rs r : EIdx} {n : NIdx} {i : Nat} {nm : ConLeche.Name}
    (hwf : StoreWF st) (hview : st.view h = some (.proj n i sub))
    (hx1 : Ext st s1) (hs : Inst1At ve d st sub s1 rs)
    (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs))
    (hn0 : denoteN st.ns n = some nm) : Inst1At ve d st h s2 r :=
  RelE.proj hwf hview (fun _ => rfl) (hs.ext hx2) hn0
    (denoteN_ext (denoteN_ext hn0 hx1) hx2) hr

/-! ### The same four, in the shape `mvcgen` actually produces

Task #97s round 1's group 7 ("the per-site step lemmas, as the verification
condition presents them"), and it is load-bearing for a different reason here
than there: the twin dispatches on the TAG and then projects, so what the arm
has is `(h.tag == ETag.app) = true` and `some (f, a) = st.viewApp h` —
REVERSED, because `mvcgen` orients a spec's postcondition equation that way.
With the view derived inside the lemma, `f` and `a` are determined by the
hypothesis `assumption` finds; with a `have` in front of the `exact` they are
metavariables when `assumption` runs, and it fails (measured).

-/

/-- con-leche: none — `Inst1At.app_step` at the arm's own hypotheses. -/
theorem Inst1At.app_step' {ve : Expr} {d : Nat} {st s1 s2 s3 : EStore}
    {h f a rf ra r : EIdx} (hwf : StoreWF st)
    (htg : (h.tag == ETag.app) = true) (hva : some (f, a) = st.viewApp h)
    (hx1 : Ext st s1) (hf : Inst1At ve d st f s1 rf)
    (hx2 : Ext s1 s2) (ha : Inst1At ve d s1 a s2 ra)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) :
    Inst1At ve d st h s3 r :=
  Inst1At.app_step hwf (view_of_viewApp_tag htg hva.symm) hx1 hf hx2 ha hx3 hr

/-- con-leche: none — `Inst1At.letE_step` at the arm's own hypotheses. -/
theorem Inst1At.letE_step' {ve : Expr} {d : Nat} {st s1 s2 s3 s4 : EStore}
    {h ty w b rt rw rb r : EIdx} (hwf : StoreWF st)
    (htg : (h.tag == ETag.letE) = true)
    (hvl : some (ty, w, b) = st.viewLet h)
    (hx1 : Ext st s1) (ht : Inst1At ve d st ty s1 rt)
    (hx2 : Ext s1 s2) (hw : Inst1At ve d s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : Inst1At ve (d + 1) s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) :
    Inst1At ve d st h s4 r :=
  Inst1At.letE_step hwf (view_of_viewLet_tag htg hvl.symm) hx1 ht hx2 hw hx3 hb
    hx4 hr

/-- con-leche: none — `Inst1At.proj_step` at the arm's own hypotheses.  The
name fact is supplied by the caller (it comes from `denote_eq_proj`, whose
existential `grind` cannot see through). -/
theorem Inst1At.proj_step' {ve : Expr} {d : Nat} {st s1 s2 : EStore}
    {h sub rs r : EIdx} {n : NIdx} {i : Nat} {nm : ConLeche.Name}
    (hwf : StoreWF st) (htg : (h.tag == ETag.proj) = true)
    (hvp : some (n, i, sub) = st.viewProj h)
    (hx1 : Ext st s1) (hs : Inst1At ve d st sub s1 rs)
    (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs))
    (hn0 : denoteN st.ns n = some nm) : Inst1At ve d st h s2 r :=
  Inst1At.proj_step hwf (view_of_viewProj_tag htg hvp.symm) hx1 hs hx2 hr hn0

/-- con-leche: none — `Inst1At.bind_step` at the arm's own hypotheses: the
binder arm reads `viewBind`, and `view_of_viewBind` gives the view back. -/
theorem Inst1At.bind_step' {ve : Expr} {d : Nat} {st s1 s2 s3 : EStore}
    {h ty b rt rb r : EIdx} {tg : UInt32}
    (hwf : StoreWF st) (htg : ETag.isBind tg = true) (htg2 : tg = h.tag)
    (hvb : some (ty, b) = st.viewBind h)
    (hx1 : Ext st s1) (ht : Inst1At ve d st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : Inst1At ve (d + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (eBindView tg rt rb)) :
    Inst1At ve d st h s3 r := by
  refine Inst1At.bind_step hwf htg ?_ hx1 ht hx2 hb hx3 hr
  rw [htg2]
  exact view_of_viewBind hvb.symm

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33-45 instantiate1 — the CUTOFF
arm, packaged as one step lemma.  Left as three separate hints
(`EStore.derived_exact`, `Expr.bvarBRaw`, `instantiate1_of_raw_le`) it sends
`grind` into an ematching spiral on `((ve.instantiate1 ve d).instantiate1 ve
d)…`; as one lemma with the store read as its pattern it fires once (task
#97s's one manual verification condition). -/
theorem Inst1At.cutoff {st : EStore} (hwf : StoreWF st) {h : EIdx} {d : Nat}
    {ve : Expr} (hsat : (bvarOfData (st.derived h)).toNat < satRange)
    (hle : (bvarOfData (st.derived h)).toNat ≤ d) : Inst1At ve d st h st h := by
  intro e he
  show denoteE st h = some (e.instantiate1 ve d)
  have hd := EStore.derived_exact hwf he
  rw [hd] at hsat hle
  rw [instantiate1_of_raw_le hsat hle]
  exact he

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33-45 instantiate1 — the CATCH-ALL
arm: a handle whose tag is none of the six the walk dispatches on denotes a
leaf, and `instantiate1` is the identity there. -/
theorem Inst1At.leaf {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {v : ENodeView} {d : Nat} {ve : Expr} (hview : st.view h = some v)
    (happ : ¬ (h.tag = ETag.app)) (hbind : ETag.isBind h.tag = false)
    (hbvar : ¬ (h.tag = ETag.bvar)) (hlet : ¬ (h.tag = ETag.letE))
    (hproj : ¬ (h.tag = ETag.proj)) : Inst1At ve d st h st h := by
  intro e he
  show denoteE st h = some (e.instantiate1 ve d)
  rw [instantiate1_leaf
    (denote_leaf_of_tag hwf hview happ hbind hbvar hlet hproj he)]
  exact he


/-! ## Vocabulary candidates for Bridge/Grind.lean (task #123)

What `grind` needs to close the arms, in `Bridge/Grind.lean`'s §5 style:
every fact an equation between terms built from the subject, keyed on the
terms the verification condition already has.  The declarations are
`private` and their patterns `local`, so that no importer of this module
(`Subst`, `ExprOps/Spine`, `Core/Walks/Spine`, …) sees them before the
coordinator hoists them.

* the state invariant and the answer relation as equations (`StateOK` is its
  store's well-formedness; `RelE` is `MapRel` on the two denotation terms,
  and `MapRel` at a denoting subject is the equation it says);
* the per-call memo table as a fact per probe (`MemoAt`, the `MemoOK.get`
  of a `getElem?` term), carried along the store order (`memoOK_le`) and
  satisfied by a dropped table;
* each projection read under its tag as the `DenoteView` fact on the
  subject, and the extraction lemmas `Bridge/Grind.lean` §5 does not have
  yet (`bvar`, `lam`, `forallE`, `letE`, `proj`);
* the denotation's constructor from its tag, as an eta over the §5
  projections — guarded, so it fires only where the tag is KNOWN (unguarded,
  `grind` case-splits on equalities between the tag constants);
* a node whose children denote has a view (`view_isSome`), at the two
  stores the intern specs ask about. -/

/-- con-leche: none — `StateOK` is its store's well-formedness. -/
private theorem stateOK_eq (s : AState) : StateOK s = StoreWF s.store :=
  propext ⟨fun h => h.wf, fun h => ⟨h⟩⟩
attribute [local bridge_grind =] stateOK_eq

/-- con-leche: none — `RelE` is `MapRel` on the two denotation terms (both
directions, so a `RelE` goal is one too). -/
private theorem relE_eq_mapRel (g : Expr → Expr) (st : EStore) (c : EIdx) (st' : EStore)
    (r : EIdx) : RelE g st c st' r = MapRel g (denoteE st c) (denoteE st' r) := by
  apply propext; constructor
  · exact RelE.mapRel
  · intro h e he; rw [he] at h; exact h
attribute [local bridge_grind =] relE_eq_mapRel

/-- con-leche: none — `MapRel` at a denoting subject, as an equation (so a
`MapRel` goal is one too). -/
private theorem mapRel_some_eq (g : Expr → Expr) (e : Expr) (o : Option Expr) :
    MapRel g (some e) o = (o = some (g e)) := rfl
attribute [local bridge_grind =] mapRel_some_eq

/-- con-leche: ConLeche/Kernel/ExprOps.lean:61-63 Inst1MemoInv — what a
cursor-keyed memo table says at one probe: a recorded entry is the answer. -/
private def MemoAt (f : Nat → Expr → Expr) (st : EStore) (k : EIdx × Nat) :
    Option EIdx → Prop
  | some r => MapRel (f k.2) (denoteE st k.1) (denoteE st r)
  | none => True

/-- con-leche: ConLeche/Kernel/ExprOps.lean:61-63 Inst1MemoInv — `MemoOK.get`
at every probe of the table, keyed by the invariant and the probe. -/
private theorem memoAt {f : Nat → Expr → Expr} {tbl : Std.HashMap (EIdx × Nat) EIdx}
    {st : EStore} (hm : MemoOK f tbl st) (k : EIdx × Nat) : MemoAt f st k tbl[k]? := by
  cases h : tbl[k]? with
  | none => trivial
  | some r => exact RelE.mapRel (MemoOK.get hm h)
local grind_pattern [bridge_grind] memoAt => MemoOK f tbl st, tbl[k]?

/-- con-leche: none — `MemoAt` at a hit. -/
private theorem memoAt_some_eq (f : Nat → Expr → Expr) (st : EStore) (k : EIdx × Nat)
    (r : EIdx) : MemoAt f st k (some r) = MapRel (f k.2) (denoteE st k.1) (denoteE st r) := rfl
attribute [local bridge_grind =] memoAt_some_eq

/-- con-leche: none — `MemoOK.mono` along the store order, keyed by the two
invariant terms. -/
private theorem memoOK_le {f : Nat → Expr → Expr} {tbl : Std.HashMap (EIdx × Nat) EIdx}
    {st st' : EStore} (hm : MemoOK f tbl st) (hx : st ≤ st') : MemoOK f tbl st' :=
  MemoOK.mono hm hx rfl
local grind_pattern [bridge_grind] memoOK_le => MemoOK f tbl st, MemoOK f tbl st'

/-- con-leche: none — a dropped table satisfies the invariant (guarded: only
at a table known to be empty). -/
private theorem memoOK_of_empty {f : Nat → Expr → Expr}
    {tbl : Std.HashMap (EIdx × Nat) EIdx} {st : EStore} (h : tbl = ∅) : MemoOK f tbl st :=
  MemoOK.of_empty h
local grind_pattern [bridge_grind] memoOK_of_empty => MemoOK f tbl st where
  guard tbl = ∅

/-- con-leche: none — the `app` projection under its tag is the subject's
view fact. -/
private theorem denoteView_viewApp {st : EStore} (hwf : StoreWF st) {i f a : EIdx}
    (htg : i.tag = ETag.app) (h : st.viewApp i = some (f, a)) :
    DenoteView st (some (.app f a)) (denoteE st i) :=
  view_of_viewApp htg h ▸ denote_view hwf i
local grind_pattern [bridge_grind] denoteView_viewApp => st.viewApp i, some (f, a) where
  guard st.viewApp i = some (f, a)

/-- con-leche: none — the binder projection is the subject's view fact, at
the tag the handle carries. -/
private theorem denoteView_viewBind {st : EStore} (hwf : StoreWF st) {i ty b : EIdx}
    (h : st.viewBind i = some (ty, b)) :
    DenoteView st (some (eBindView i.tag ty b)) (denoteE st i) :=
  view_of_viewBind h ▸ denote_view hwf i
local grind_pattern [bridge_grind] denoteView_viewBind => st.viewBind i, some (ty, b) where
  guard st.viewBind i = some (ty, b)

/-- con-leche: none — the `letE` projection under its tag. -/
private theorem denoteView_viewLet {st : EStore} (hwf : StoreWF st) {i ty w b : EIdx}
    (htg : i.tag = ETag.letE) (h : st.viewLet i = some (ty, w, b)) :
    DenoteView st (some (.letE ty w b)) (denoteE st i) :=
  view_of_viewLet htg h ▸ denote_view hwf i
local grind_pattern [bridge_grind] denoteView_viewLet => st.viewLet i, some (ty, w, b) where
  guard st.viewLet i = some (ty, w, b)

/-- con-leche: none — the `proj` projection under its tag. -/
private theorem denoteView_viewProj {st : EStore} (hwf : StoreWF st) {i : EIdx} {n : NIdx}
    {k : Nat} {sub : EIdx} (htg : i.tag = ETag.proj) (h : st.viewProj i = some (n, k, sub)) :
    DenoteView st (some (.proj n k sub)) (denoteE st i) :=
  view_of_viewProj htg h ▸ denote_view hwf i
local grind_pattern [bridge_grind] denoteView_viewProj => st.viewProj i, some (n, k, sub) where
  guard st.viewProj i = some (n, k, sub)

/-- con-leche: none — the `bvar` projection under its tag. -/
private theorem denoteView_viewBVar {st : EStore} (hwf : StoreWF st) {i : EIdx} {k : Nat}
    (htg : i.tag = ETag.bvar) (h : st.viewBVar i = some k) :
    DenoteView st (some (.bvar k)) (denoteE st i) :=
  view_of_viewBVar htg h ▸ denote_view hwf i
local grind_pattern [bridge_grind] denoteView_viewBVar => st.viewBVar i, some k where
  guard st.viewBVar i = some k

/-- con-leche: none — a `bvar` view's index is the denotation's. -/
private theorem DenoteView.bvar {st : EStore} {i : Nat} {e : Expr}
    (H : DenoteView st (some (.bvar i)) (some e)) : exprBVar e = i := H
local grind_pattern [bridge_grind] DenoteView.bvar => DenoteView st (some (.bvar i)) (some e)

/-- con-leche: none — a `lam` view's children denote the binder type and
body. -/
private theorem DenoteView.lam {st : EStore} {t b : EIdx} {e : Expr}
    (H : DenoteView st (some (.lam t b)) (some e)) :
    denoteE st t = some (exprBinderType e) ∧ denoteE st b = some (exprBody e) := H
local grind_pattern [bridge_grind] DenoteView.lam => DenoteView st (some (.lam t b)) (some e)

/-- con-leche: none — a `forallE` view's children, likewise. -/
private theorem DenoteView.forallE {st : EStore} {t b : EIdx} {e : Expr}
    (H : DenoteView st (some (.forallE t b)) (some e)) :
    denoteE st t = some (exprBinderType e) ∧ denoteE st b = some (exprBody e) := H
local grind_pattern [bridge_grind] DenoteView.forallE =>
  DenoteView st (some (.forallE t b)) (some e)

/-- con-leche: none — a `letE` view's three children. -/
private theorem DenoteView.letE {st : EStore} {t w b : EIdx} {e : Expr}
    (H : DenoteView st (some (.letE t w b)) (some e)) :
    denoteE st t = some (exprBinderType e) ∧ denoteE st w = some (exprLetVal e) ∧
      denoteE st b = some (exprBody e) := H
local grind_pattern [bridge_grind] DenoteView.letE => DenoteView st (some (.letE t w b)) (some e)

/-- con-leche: none — a `proj` view's name, index and structure. -/
private theorem DenoteView.proj {st : EStore} {n : NIdx} {i : Nat} {sub : EIdx} {e : Expr}
    (H : DenoteView st (some (.proj n i sub)) (some e)) :
    denoteN st.ns n = some (exprProjName e) ∧ exprProjIdx e = i ∧
      denoteE st sub = some (exprProjStruct e) := ⟨H.1, H.2.2⟩
local grind_pattern [bridge_grind] DenoteView.proj =>
  DenoteView st (some (.proj n i sub)) (some e)

/-- con-leche: none — an expression tagged `app` IS an application of its
projections (guarded: only where the tag is known). -/
private theorem exprTag_app {e : Expr} (h : exprTag e = ETag.app) :
    e = .app (exprFn e) (exprArg e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
local grind_pattern [bridge_grind] exprTag_app => exprTag e where
  guard exprTag e = ETag.app

/-- con-leche: none — tagged `lam`. -/
private theorem exprTag_lam {e : Expr} (h : exprTag e = ETag.lam) :
    e = .lam (exprBinderType e) (exprBody e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
local grind_pattern [bridge_grind] exprTag_lam => exprTag e where
  guard exprTag e = ETag.lam

/-- con-leche: none — tagged `forallE`. -/
private theorem exprTag_forallE {e : Expr} (h : exprTag e = ETag.forallE) :
    e = .forallE (exprBinderType e) (exprBody e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
local grind_pattern [bridge_grind] exprTag_forallE => exprTag e where
  guard exprTag e = ETag.forallE

/-- con-leche: none — tagged `letE`. -/
private theorem exprTag_letE {e : Expr} (h : exprTag e = ETag.letE) :
    e = .letE (exprBinderType e) (exprLetVal e) (exprBody e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
local grind_pattern [bridge_grind] exprTag_letE => exprTag e where
  guard exprTag e = ETag.letE

/-- con-leche: none — tagged `proj`. -/
private theorem exprTag_proj {e : Expr} (h : exprTag e = ETag.proj) :
    e = .proj (exprProjName e) (exprProjIdx e) (exprProjStruct e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
local grind_pattern [bridge_grind] exprTag_proj => exprTag e where
  guard exprTag e = ETag.proj

/-- con-leche: none — tagged `bvar`. -/
private theorem exprTag_bvar {e : Expr} (h : exprTag e = ETag.bvar) :
    e = .bvar (exprBVar e) := by
  cases e <;> first | rfl | (simp only [exprTag] at h; exact absurd h (by decide))
local grind_pattern [bridge_grind] exprTag_bvar => exprTag e where
  guard exprTag e = ETag.bvar

/-- con-leche: none — a handle that denotes has a view, keyed by the view
test the intern specs ask for. -/
private theorem view_isSome' {st : EStore} {h : EIdx} (hs : (denoteE st h).isSome = true) :
    (st.view h).isSome = true := view_isSome hs
local grind_pattern [bridge_grind] view_isSome' => (st.view h).isSome

/-- con-leche: none — a name handle that denotes has a view. -/
private theorem nview_isSome' {st : NStore} {c : NIdx} (hs : (denoteN st c).isSome = true) :
    (st.view c).isSome = true := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs; exact nview_isSome_of_denote hx
local grind_pattern [bridge_grind] nview_isSome' => (NStore.view st c).isSome

/-! ### `instantiate1`'s two non-structural clauses as equations

The derived-word cutoff and the catch-all, each keyed on the term it
rewrites, so that the dispatcher's two exits need no step lemma. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1456 bvarBRaw_exact — the
CUTOFF as an equation: below the packed bound, `instantiate1` is the identity
on the handle's denotation (guarded by the denotation). -/
private theorem inst1_cut {st : EStore} (hwf : StoreWF st) {h : EIdx} {e v : Expr} {d : Nat}
    (he : denoteE st h = some e) (hsat : (bvarOfData (st.derived h)).toNat < satRange)
    (hle : (bvarOfData (st.derived h)).toNat ≤ d) : e.instantiate1 v d = e := by
  have hd := EStore.derived_exact hwf he
  rw [hd] at hsat hle
  exact instantiate1_of_raw_le hsat hle
local grind_pattern [bridge_grind] inst1_cut =>
    bvarOfData (st.derived h), Expr.instantiate1 e v d where
  guard denoteE st h = some e

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33-45 instantiate1 — the
CATCH-ALL as an equation: a term whose tag is none of the six the walk
dispatches on is a fixed point. -/
private theorem inst1_leaf {e v : Expr} {d : Nat} (happ : ¬ exprTag e = ETag.app)
    (hbind : ETag.isBind (exprTag e) = false) (hbvar : ¬ exprTag e = ETag.bvar)
    (hlet : ¬ exprTag e = ETag.letE) (hproj : ¬ exprTag e = ETag.proj) :
    e.instantiate1 v d = e := by
  cases e <;> simp_all [exprTag, ETag.isBind, Expr.instantiate1] <;> contradiction
local grind_pattern [bridge_grind] inst1_leaf => Expr.instantiate1 e v d, exprTag e

/-! ## Theorem 1 for `instantiate1Go`

One level of the recursion as a record, so that the fuel induction has
something to hand the arms (task #97s rule 8).

**Since DESIGN §8.6's arm-split ruling** (coordinator, 2026-09-22) the twin
is a `mutual` block — a dispatcher and one `def` per constructor arm — and
the proof follows it exactly: one theorem per arm, each taking the previous
fuel level's record as its induction hypothesis, and a dispatcher whose
`mvcgen` list is the five arm theorems.  The dispatcher's body is then the
cutoff, the tag chain and six calls, so `mvcgen` leaves a handful of
verification conditions instead of the seventy-nine the inline body left, and
`grind` — which was 66 of the 71 net seconds — never sees more than one arm's
worth of context at a time.

**Each arm carries its own tag hypothesis.**  `EStore.viewApp` does not test
the tag (it is the array read the tag dispatch has already decided, tasks
#97-P6-10 and #97-P6-13), so `view_of_viewApp` needs `h.tag = ETag.app` and
the arm theorem takes it as a parameter; the dispatcher supplies it from the
branch it is in, as one more verification condition that `assumption` closes. -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `instantiate1Go`'s recursion. -/
structure Inst1Spec (v : EIdx) (ve : Expr) (rec : EIdx → Nat → AM EIdx) :
    Prop where
  run : ∀ (s₁ : AState) (c : EIdx) (dd : Nat), StateOK s₁ → Inst1MemoA ve s₁ →
    denoteE s₁.store v = some ve → (denoteE s₁.store c).isSome = true →
    ⦃fun s => s = s₁⦄ rec c dd
    ⦃fun r s' => StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r; ⊤⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the `bvar`
ARM, which is not recursive and needs no induction hypothesis.  The three
branches are `Expr.instantiate1`'s own three, and they are written out because
the closer will not unfold `RelE` (a `def`); at one arm in one theorem that is
nine lines rather than the file-wide `unfold RelE` that task #97-P3-0 measured
breaking the `proj` arm. -/
theorem instantiate1ArmBVar_spec (v : EIdx) (ve : Expr) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hm : Inst1MemoA ve s₁)
    (hv : denoteE s₁.store v = some ve)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.bvar) = true) :
    ⦃fun s => s = s₁⦄ instantiate1ArmBVar v c dd
    ⦃fun r s' => StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r; ⊤⦄ := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hden
  -- the three branches are `Expr.instantiate1`'s own three
  sym only [bridge_grind, denoteEView, Expr.instantiate1] =>
    vcgen [instantiate1ArmBVar] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the `app`
ARM: probe, project, recurse into both children, rebuild, insert. -/
theorem instantiate1ArmApp_spec (v : EIdx) (ve : Expr) (fuel : Nat)
    (ih : Inst1Spec v ve (instantiate1Go v fuel)) (s₁ : AState) (c : EIdx)
    (dd : Nat) (hok : StateOK s₁) (hm : Inst1MemoA ve s₁)
    (hv : denoteE s₁.store v = some ve)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.app) = true) :
    ⦃fun s => s = s₁⦄ instantiate1ArmApp v fuel c dd
    ⦃fun r s' => StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r; ⊤⦄ := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hden
  sym only [bridge_grind, denoteEView, opt2, Expr.instantiate1] =>
    vcgen [instantiate1ArmApp, ih.run, inst1Set_spec (ve := ve)] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the BINDER
ARM (`lam` and `forallE` in one, as the tag dispatch tests them). -/
theorem instantiate1ArmBind_spec (v : EIdx) (ve : Expr) (fuel : Nat)
    (ih : Inst1Spec v ve (instantiate1Go v fuel)) (s₁ : AState) (c : EIdx)
    (dd : Nat) (hok : StateOK s₁) (hm : Inst1MemoA ve s₁)
    (hv : denoteE s₁.store v = some ve)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : ETag.isBind c.tag = true) :
    ⦃fun s => s = s₁⦄ instantiate1ArmBind v fuel c dd
    ⦃fun r s' => StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r; ⊤⦄ := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hden
  -- `lam` or `forallE`: the one case split, on `ETag.isBind`'s disjunction
  sym only [bridge_grind, denoteEView, opt2, Expr.instantiate1, ETag.isBind] =>
    vcgen [instantiate1ArmBind, ih.run, inst1Set_spec (ve := ve)] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the `letE`
ARM; the body descends at `dd + 1`. -/
theorem instantiate1ArmLet_spec (v : EIdx) (ve : Expr) (fuel : Nat)
    (ih : Inst1Spec v ve (instantiate1Go v fuel)) (s₁ : AState) (c : EIdx)
    (dd : Nat) (hok : StateOK s₁) (hm : Inst1MemoA ve s₁)
    (hv : denoteE s₁.store v = some ve)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.letE) = true) :
    ⦃fun s => s = s₁⦄ instantiate1ArmLet v fuel c dd
    ⦃fun r s' => StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r; ⊤⦄ := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hden
  sym only [bridge_grind, denoteEView, opt3, Expr.instantiate1] =>
    vcgen [instantiate1ArmLet, ih.run, inst1Set_spec (ve := ve)] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the `proj`
ARM.  The struct NAME is carried unchanged, and its denotation comes from
`denote_eq_proj`'s existential, which `grind` cannot see through. -/
theorem instantiate1ArmProj_spec (v : EIdx) (ve : Expr) (fuel : Nat)
    (ih : Inst1Spec v ve (instantiate1Go v fuel)) (s₁ : AState) (c : EIdx)
    (dd : Nat) (hok : StateOK s₁) (hm : Inst1MemoA ve s₁)
    (hv : denoteE s₁.store v = some ve)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.proj) = true) :
    ⦃fun s => s = s₁⦄ instantiate1ArmProj v fuel c dd
    ⦃fun r s' => StateOK s' ∧ Inst1MemoA ve s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1At ve dd s₁.store c s'.store r; ⊤⦄ := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hden
  sym only [bridge_grind, denoteEView, opt2, Expr.instantiate1] =>
    vcgen [instantiate1ArmProj, ih.run, inst1Set_spec (ve := ve)] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33-45 instantiate1
con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go
**THEOREM 1 for `instantiate1`**, at one level of the recursion, by induction
on the fuel.  The dispatcher: the cutoff, the tag chain, the five arms by
name, and the catch-all. -/
theorem instantiate1Go_spec (v : EIdx) (ve : Expr) :
    ∀ fuel, Inst1Spec v ve (instantiate1Go v fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h d _ _ _ _
    sym only [bridge_grind] => vcgen [instantiate1Go_zero] <;> finish
  | succ fuel ih =>
    constructor
    intro s₀ h d hok hm hv hden
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hden
    -- the five arms' preconditions, the derived-word cutoff and the catch-all
    sym only [bridge_grind] =>
      vcgen [instantiate1Go_succ, instantiate1ArmApp_spec v ve fuel ih,
        instantiate1ArmBind_spec v ve fuel ih, instantiate1ArmBVar_spec v ve,
        instantiate1ArmLet_spec v ve fuel ih, instantiate1ArmProj_spec v ve fuel ih] <;> finish
/-! ## The top-level entry, and Theorem 1 as a statement about a RUN

`instantiate1Fast` is con-leche's `(instantiate1Go v {} e d).1`: the memo is
fresh before and dropped after, because its answers depend on the substituted
term.  The dropped memo satisfies `Inst1MemoA` for EVERY substituted term
(`MemoOK.of_empty`), which is why the per-call memo never appears in a
caller's invariant. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast —
**THEOREM 1 for `instantiate1`, at the entry point**. -/
theorem instantiate1Fast_spec (fuel : Nat) (s₀ : AState) (e v : EIdx) (d : Nat)
    (ve : Expr) (hok : StateOK s₀) (hv : denoteE s₀.store v = some ve)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => s = s₀⦄ instantiate1Fast fuel e v d
    ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.memos.inst1C = ∅ ∧
        Inst1At ve d s₀.store e s'.store r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [instantiate1Fast, (instantiate1Go_spec v ve fuel).run] <;> finish

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the same statement about
a RUN, which is the form the tier above consumes. -/
theorem instantiate1Fast_run {fuel : Nat} {s₀ s' : AState} {e v r : EIdx}
    {d : Nat} {ve : Expr} (hok : StateOK s₀)
    (hv : denoteE s₀.store v = some ve)
    (hden : (denoteE s₀.store e).isSome = true)
    (hrun : (instantiate1Fast fuel e v d).run s₀ = Except.ok (r, s')) :
    StateOK s' ∧ Ext s₀.store s'.store ∧
      s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧ s'.memos.inst1C = ∅ ∧
      Inst1At ve d s₀.store e s'.store r :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    (instantiate1Fast_spec fuel s₀ e v d ve hok hv hden)

/-! ## The axiom check -/

#print axioms instantiate1_of_bvarBound_le
#print axioms instantiate1_of_raw_le
#print axioms Inst1At.cutoff
#print axioms Inst1At.leaf

end ConRon.Bridge.ExprOps

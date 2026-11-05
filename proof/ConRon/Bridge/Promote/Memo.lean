/-
# `ConRon.Bridge.Promote.Memo` — what a promotion needs of its stores

A promotion reads the scratch tier by `view` and writes only the persistent one, so
it holds with no invariant on the scratch tier: what ran before it may have left
anything there.  Its statements therefore live at two stores: the SOURCE `src`,
in which the promotion's input denotes, and the persistent PROJECTION
`st.dropScratch` of the store it runs on.

* `Kept d d'`: the answer's denotation `d'` exists and agrees with whatever the
  subject's denotation `d` is;
* `PSrc src st`: the two stores read the same where the promotion reads them;
* `PMemoPi m src st`: every row of the promotion memo is a promoted pair;
* `PFrame`: a promotion touches nothing but the store.
-/
module

public import ConRon.Bridge.Promote.Pers
public import ConRon.Arena.PromoteExt

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## What an answer keeps -/

/-- con-leche: none — arena infrastructure; **the answer's denotation against the
subject's**: the answer denotes, and if the subject denotes then it denotes the same.
The subject need not denote: nothing is known of the store a promotion reads. -/
abbrev Kept {α : Type} (d d' : Option α) : Prop :=
  (∃ y, d' = some y) ∧ ∀ x, d = some x → d' = some x

/-- con-leche: none — arena infrastructure; the answer's side moves along an
implication. -/
theorem Kept.post {α : Type} {d d' d'' : Option α} (h : Kept d d')
    (hx : ∀ y, d' = some y → d'' = some y) : Kept d d'' :=
  ⟨let ⟨y, hy⟩ := h.1; ⟨y, hx y hy⟩, fun x hd => hx x (h.2 x hd)⟩

/-- con-leche: none — arena infrastructure; the subject's side moves back along an
implication. -/
theorem Kept.pre {α : Type} {d0 d d' : Option α} (h : Kept d d')
    (hx : ∀ y, d0 = some y → d = some y) : Kept d0 d' :=
  ⟨h.1, fun x hd => h.2 x (hx x hd)⟩

/-- con-leche: none — arena infrastructure; a value that does not depend on the store
is kept. -/
theorem Kept.some {α : Type} (a : α) : Kept (some a) (some a) :=
  ⟨⟨a, rfl⟩, fun _ h => h⟩

/-- con-leche: none — arena infrastructure; `Kept` through `Option.map`. -/
theorem Kept.map {α β : Type} (f : α → β) {d d' : Option α} (h : Kept d d') :
    Kept (d.map f) (d'.map f) := by
  obtain ⟨⟨y, hy⟩, hk⟩ := h
  refine ⟨⟨f y, by simp [hy]⟩, fun x hx => ?_⟩
  simp only [Option.map_eq_some_iff] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, hk a ha, rfl⟩

/-- con-leche: none — arena infrastructure; `Kept` through `opt2`. -/
theorem Kept.opt2 {α β γ : Type} (f : α → β → γ) {a a' : Option α} {b b' : Option β}
    (ha : Kept a a') (hb : Kept b b') : Kept (opt2 f a b) (opt2 f a' b') := by
  obtain ⟨⟨y, hy⟩, hka⟩ := ha
  obtain ⟨⟨z, hz⟩, hkb⟩ := hb
  refine ⟨⟨f y z, by simp [hy, hz, ConRon.Arena.opt2]⟩, fun x hx => ?_⟩
  simp only [opt2_eq_some_iff] at hx ⊢
  obtain ⟨p, q, hp, hq, rfl⟩ := hx
  exact ⟨p, q, hka p hp, hkb q hq, rfl⟩

/-- con-leche: none — arena infrastructure; `Kept` through `opt3`. -/
theorem Kept.opt3 {α β γ δ : Type} (f : α → β → γ → δ) {a a' : Option α}
    {b b' : Option β} {c c' : Option γ} (ha : Kept a a') (hb : Kept b b')
    (hc : Kept c c') : Kept (opt3 f a b c) (opt3 f a' b' c') := by
  obtain ⟨⟨y, hy⟩, hka⟩ := ha
  obtain ⟨⟨z, hz⟩, hkb⟩ := hb
  obtain ⟨⟨w, hw⟩, hkc⟩ := hc
  refine ⟨⟨f y z w, by simp [hy, hz, hw, ConRon.Arena.opt3]⟩, fun x hx => ?_⟩
  simp only [opt3_eq_some_iff] at hx ⊢
  obtain ⟨p, q, r, hp, hq, hr, rfl⟩ := hx
  exact ⟨p, q, r, hka p hp, hkb q hq, hkc r hr, rfl⟩

/-! ## The two stores -/

/-- con-leche: none — arena infrastructure; **what a promotion needs of the store
it runs on and the store its input denotes in**: the persistent projection and the
source are well formed, a scratch handle the source can read reads the same in the
store, and a persistent handle that denotes in the source denotes the same in the
projection.  Nothing is asked of the store's scratch tier beyond that. -/
structure PSrc (src st : EStore) : Prop where
  piWF : StoreWF st.dropScratch
  srcWF : StoreWF src
  scrE : ∀ i v, i.isPersistent = false → src.view i = some v → st.view i = some v
  scrLs : ∀ i v, i.isPersistent = false → src.lss.view i = some v → st.lss.view i = some v
  scrL : ∀ i v, i.isPersistent = false → src.ls.view i = some v → st.ls.view i = some v
  scrN : ∀ i v, i.isPersistent = false → src.ns.view i = some v → st.ns.view i = some v
  persE : ∀ i x, i.isPersistent = true → denoteE src i = some x →
    denoteE st.dropScratch i = some x
  persLs : ∀ i x, i.isPersistent = true → denoteLs src.lss i = some x →
    denoteLs st.dropScratch.lss i = some x
  persL : ∀ i x, i.isPersistent = true → denoteL src.ls i = some x →
    denoteL st.dropScratch.ls i = some x
  persN : ∀ i x, i.isPersistent = true → denoteN src.ns i = some x →
    denoteN st.dropScratch.ns i = some x

/-- con-leche: none — arena infrastructure; the persistent clauses of `PSrc`, as the
relation they are. -/
theorem PSrc.pext {src st : EStore} (h : PSrc src st) : PExt src st.dropScratch :=
  ⟨⟨⟨h.persN, h.persL⟩, h.persLs⟩, h.persE⟩

/-! ## The promotion memo -/

/-- con-leche: none — arena infrastructure; **the promotion memo over the two
stores**: every row's answer is persistent and keeps its key's denotation, in all
four tables, which is the record `Arena/Promote.lean` threads. -/
structure PMemoPi (m : PMemo) (src st : EStore) : Prop where
  eM : ∀ h r, m.eM[h]? = some r →
    PersE r ∧ Kept (denoteE src h) (denoteE st.dropScratch r)
  nM : ∀ h r, m.nM[h]? = some r →
    PersN r ∧ Kept (denoteN src.ns h) (denoteN st.dropScratch.ns r)
  lM : ∀ h r, m.lM[h]? = some r →
    PersL r ∧ Kept (denoteL src.ls h) (denoteL st.dropScratch.ls r)
  lsM : ∀ h r, m.lsM[h]? = some r →
    PersLs r ∧ Kept (denoteLs src.lss h) (denoteLs st.dropScratch.lss r)

/-- con-leche: none — arena infrastructure; the EMPTY memo has no rows, which is what
every declaration's promotion starts from. -/
theorem PMemoPi.empty (src st : EStore) : PMemoPi PMemo.empty src st where
  eM := by intro h r hk; simp [PMemo.empty] at hk
  nM := by intro h r hk; simp [PMemo.empty] at hk
  lM := by intro h r hk; simp [PMemo.empty] at hk
  lsM := by intro h r hk; simp [PMemo.empty] at hk

/-- con-leche: none — arena infrastructure; a row recorded before an append to the
projection is still a promoted pair after it. -/
theorem PMemoPi.mono {m : PMemo} {src st st' : EStore} (h : PMemoPi m src st)
    (hx : Ext st.dropScratch st'.dropScratch) : PMemoPi m src st' where
  eM := fun k r hk => ⟨(h.eM k r hk).1, (h.eM k r hk).2.post (hx.expr r)⟩
  nM := fun k r hk => ⟨(h.nM k r hk).1, (h.nM k r hk).2.post (hx.lss.ls.ns r)⟩
  lM := fun k r hk => ⟨(h.lM k r hk).1, (h.lM k r hk).2.post (hx.lss.ls.lvl r)⟩
  lsM := fun k r hk => ⟨(h.lsM k r hk).1, (h.lsM k r hk).2.post (hx.lss.lst r)⟩

/-- con-leche: none — arena infrastructure; one more expression row. -/
theorem PMemoPi.insertE {m : PMemo} {src st : EStore} (hm : PMemoPi m src st) {h r : EIdx}
    (hp : PersE r) (hk : Kept (denoteE src h) (denoteE st.dropScratch r)) :
    PMemoPi { m with eM := m.eM.insert h r } src st := by
  refine ⟨?_, hm.nM, hm.lM, hm.lsM⟩
  intro k r' hr
  simp only [Std.HashMap.getElem?_insert] at hr
  split at hr
  · rename_i he
    obtain rfl := Option.some.inj hr
    obtain rfl := eq_of_beq he
    exact ⟨hp, hk⟩
  · exact hm.eM k r' hr

/-- con-leche: none — arena infrastructure; one more name row. -/
theorem PMemoPi.insertN {m : PMemo} {src st : EStore} (hm : PMemoPi m src st) {h r : NIdx}
    (hp : PersN r) (hk : Kept (denoteN src.ns h) (denoteN st.dropScratch.ns r)) :
    PMemoPi { m with nM := m.nM.insert h r } src st := by
  refine ⟨hm.eM, ?_, hm.lM, hm.lsM⟩
  intro k r' hr
  simp only [Std.HashMap.getElem?_insert] at hr
  split at hr
  · rename_i he
    obtain rfl := Option.some.inj hr
    obtain rfl := eq_of_beq he
    exact ⟨hp, hk⟩
  · exact hm.nM k r' hr

/-- con-leche: none — arena infrastructure; one more level row. -/
theorem PMemoPi.insertL {m : PMemo} {src st : EStore} (hm : PMemoPi m src st) {h r : LIdx}
    (hp : PersL r) (hk : Kept (denoteL src.ls h) (denoteL st.dropScratch.ls r)) :
    PMemoPi { m with lM := m.lM.insert h r } src st := by
  refine ⟨hm.eM, hm.nM, ?_, hm.lsM⟩
  intro k r' hr
  simp only [Std.HashMap.getElem?_insert] at hr
  split at hr
  · rename_i he
    obtain rfl := Option.some.inj hr
    obtain rfl := eq_of_beq he
    exact ⟨hp, hk⟩
  · exact hm.lM k r' hr

/-- con-leche: none — arena infrastructure; one more level-list row. -/
theorem PMemoPi.insertLs {m : PMemo} {src st : EStore} (hm : PMemoPi m src st) {h r : LsIdx}
    (hp : PersLs r) (hk : Kept (denoteLs src.lss h) (denoteLs st.dropScratch.lss r)) :
    PMemoPi { m with lsM := m.lsM.insert h r } src st := by
  refine ⟨hm.eM, hm.nM, hm.lM, ?_⟩
  intro k r' hr
  simp only [Std.HashMap.getElem?_insert] at hr
  split at hr
  · rename_i he
    obtain rfl := Option.some.inj hr
    obtain rfl := eq_of_beq he
    exact ⟨hp, hk⟩
  · exact hm.lsM k r' hr

/-! ## The frame

A promotion touches no memo table of `Monad.lean` at all. -/

/-- con-leche: none — arena infrastructure; a promotion leaves everything but
the store alone.  One predicate rather than four conjuncts, so that a caller's
composition is one `trans` per step. -/
structure PFrame (s s' : AState) : Prop where
  memos : s'.memos = s.memos
  caches : s'.caches = s.caches
  pins : s'.pins = s.pins
  scratchOn : s'.store.scratchOn = s.store.scratchOn

/-- con-leche: none — arena infrastructure; `Arena/PromoteExt.lean`'s step
relation IS `Ext` plus the frame. -/
theorem PFrame.of_aext {s s' : AState} (h : AExt s s') : PFrame s s' :=
  ⟨h.memos, h.caches, h.pins, h.scratchOn⟩

end ConRon.Bridge

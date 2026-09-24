/-
# `ConRon.Bridge.Promote.Memo` — the promotion memo's invariant and the frame

`Bridge/Promote/Exact.lean`'s vocabulary, moved below the walks that prove it
(task #97-P3-Promote): `PMemoOK` (every row of the promotion memo is a
promoted pair) and `PFrame` (a promotion touches nothing but the store).
Nothing about either definition changed.
-/
import ConRon.Bridge.Promote.StoreP
import ConRon.Arena.PromoteExt

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The promotion memo -/

/-- con-leche: none — arena infrastructure; a promotion memo's expression
rows are promoted pairs: the answer is persistent and denotes what the key
denotes. -/
def PMemoEOK (tbl : Std.HashMap EIdx EIdx) (st : EStore) : Prop :=
  ∀ h r, tbl[h]? = some r →
    PersE r ∧ ∃ e, denoteE st h = some e ∧ denoteE st r = some e

/-- con-leche: none — arena infrastructure; the same at a NAME handle. -/
def PMemoNOK (tbl : Std.HashMap NIdx NIdx) (st : EStore) : Prop :=
  ∀ h r, tbl[h]? = some r →
    PersN r ∧ ∃ x, denoteN st.ns h = some x ∧ denoteN st.ns r = some x

/-- con-leche: none — arena infrastructure; the same at a LEVEL handle. -/
def PMemoLOK (tbl : Std.HashMap LIdx LIdx) (st : EStore) : Prop :=
  ∀ h r, tbl[h]? = some r →
    PersL r ∧ ∃ u, denoteL st.ls h = some u ∧ denoteL st.ls r = some u

/-- con-leche: none — arena infrastructure; the same at a universe-argument
LIST handle. -/
def PMemoLsOK (tbl : Std.HashMap LsIdx LsIdx) (st : EStore) : Prop :=
  ∀ h r, tbl[h]? = some r →
    PersLs r ∧ ∃ us, denoteLs st.lss h = some us ∧ denoteLs st.lss r = some us

/-- con-leche: none — arena infrastructure; **the promotion memo denotes**:
all four tables at once, which is the record `Arena/Promote.lean` threads. -/
structure PMemoOK (m : PMemo) (st : EStore) : Prop where
  eM : PMemoEOK m.eM st
  nM : PMemoNOK m.nM st
  lM : PMemoLOK m.lM st
  lsM : PMemoLsOK m.lsM st

/-- con-leche: none — arena infrastructure; the EMPTY memo is sound, which is
what every declaration's promotion starts from (`PMemo.empty`). -/
theorem PMemoOK.empty (st : EStore) : PMemoOK PMemo.empty st where
  eM := by intro h r hk; simp [PMemo.empty] at hk
  nM := by intro h r hk; simp [PMemo.empty] at hk
  lM := by intro h r hk; simp [PMemo.empty] at hk
  lsM := by intro h r hk; simp [PMemo.empty] at hk

/-- con-leche: none — arena infrastructure; the memo invariant transports
across an append: a row recorded before an `internPersistent` is still a
promoted pair after it. -/
theorem PMemoOK.mono {m : PMemo} {st st' : EStore} (h : PMemoOK m st)
    (hx : Ext st st') : PMemoOK m st' where
  eM := by
    intro k r hk
    obtain ⟨hp, e, h1, h2⟩ := h.eM k r hk
    exact ⟨hp, e, hx.expr _ _ h1, hx.expr _ _ h2⟩
  nM := by
    intro k r hk
    obtain ⟨hp, x, h1, h2⟩ := h.nM k r hk
    exact ⟨hp, x, hx.lss.ls.ns _ _ h1, hx.lss.ls.ns _ _ h2⟩
  lM := by
    intro k r hk
    obtain ⟨hp, u, h1, h2⟩ := h.lM k r hk
    exact ⟨hp, u, hx.lss.ls.lvl _ _ h1, hx.lss.ls.lvl _ _ h2⟩
  lsM := by
    intro k r hk
    obtain ⟨hp, us, h1, h2⟩ := h.lsM k r hk
    exact ⟨hp, us, hx.lss.lst _ _ h1, hx.lss.lst _ _ h2⟩

/-! ## The four handle kinds

Each spec has the same six conjuncts: the invariant survives, the arena only
grows, the memo stays sound, the answer is persistent, the answer denotes what
the subject denoted, and the rest of the state (the per-call memos, the
caches, the pin table, the scratch flag) stood still.

The last conjunct is the per-call memo FRAME task #97-P3-0 §7 asks for, at the
one place it is free: a promotion touches no memo table of `Monad.lean` at
all. -/

/-- con-leche: none — arena infrastructure; a promotion leaves everything but
the store alone.  One predicate rather than four conjuncts, so that a caller's
composition is one `trans` per step. -/
structure PFrame (s s' : AState) : Prop where
  memos : s'.memos = s.memos
  caches : s'.caches = s.caches
  pins : s'.pins = s.pins
  scratchOn : s'.store.scratchOn = s.store.scratchOn

theorem PFrame.refl (s : AState) : PFrame s s := ⟨rfl, rfl, rfl, rfl⟩

theorem PFrame.trans {a b c : AState} (h₁ : PFrame a b) (h₂ : PFrame b c) :
    PFrame a c :=
  ⟨by rw [h₂.memos, h₁.memos], by rw [h₂.caches, h₁.caches],
   by rw [h₂.pins, h₁.pins], by rw [h₂.scratchOn, h₁.scratchOn]⟩

/-- con-leche: none — arena infrastructure; `Arena/PromoteExt.lean`'s step
relation IS `Ext` plus the frame. -/
theorem PFrame.of_aext {s s' : AState} (h : AExt s s') : PFrame s s' :=
  ⟨h.memos, h.caches, h.pins, h.scratchOn⟩

end ConRon.Bridge

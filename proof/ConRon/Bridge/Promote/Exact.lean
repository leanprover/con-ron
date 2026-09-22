/-
# `ConRon.Bridge.Promote.Exact` — the promotion is EXACT, and its memo is sound

`Arena/Promote.lean`'s own module note names the obligation this file states:

> `denote (promote h) = denote h` is the exactness lemma P3 owes; it is an
> induction on the recursion below, with `EStore.internPersistent`'s `consP`
> and `derExact` at each node.

Three things are owed at every entry of `Arena/Promote.lean`, and they travel
together because the recursion threads all three:

1. **exactness** — the promoted handle denotes what the original denoted.
   This is the whole soundness content: the promotion is a change of
   REPRESENTATION and of nothing else, so an environment the fold promoted
   denotes the environment it denoted before;
2. **persistence** — the answer is in the persistent tier (`Pers…`,
   `Bridge/Promote/Pers.lean`).  This is what the *next* `dropScratch`
   consumes: `PExt` transports a persistent denotation and nothing else, so
   without this clause the fold's environment would decode to nothing one step
   later;
3. **the memo invariant** `PMemoOK` — every row of the promotion memo is a
   promoted pair.  It is `Bridge/StateOK.lean`'s `MemoOK` shape with
   persistence added and the pure function replaced by the identity: a
   promotion computes nothing, it copies.

`PMemoOK` is stated at the STORE and not at a pure function, which is what
makes `.mono` across an `Ext` the only transport it needs: a row recorded
before an append is still a promoted pair after it.

**The shape of the sorries** (task #97-P3-Checker, sorry list items 3-5): the
four handle-kind recursions are the tier's inductions — `promoteE_spec` is a
ten-arm fuel induction in `Bridge/ExprOps/Inst1.lean`'s shape, and the three
below it are the same at three / five / one constructors.  The declaration
layer above them (`promoteCV`, `promoteCI`, `promoteVG`, `promoteNew`) is
mechanical do-notation over those four and is stated here for its consumers —
`Bridge/Checker/Fold.lean`'s per-declaration bridge reads `promoteNew_spec`
and `promoteVG_spec` and nothing else from this file.
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

/-- con-leche: none — arena infrastructure; **`promoteN` is exact.**

`sorry`: the three-arm fuel induction over `internPersistentN`.  Task
#97-P3-Checker's sorry list, item 3. -/
theorem promoteN_spec {m m' : PMemo} {fuel : Nat} {h r : NIdx} {x : ConLeche.Name}
    {s s' : AState} (hwf : StoreWFP s.store) (hm : PMemoOK m s.store)
    (hd : denoteN s.store.ns h = some x)
    (hrun : promoteN m fuel h s = .ok ((m', r), s')) :
    StoreWFP s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersN r ∧ denoteN s'.store.ns r = some x ∧ PFrame s s' := by
  sorry

/-- con-leche: none — arena infrastructure; **`promoteL` is exact.**

`sorry`: the five-arm fuel induction, `promoteN_spec` at the `.param` arm.
Task #97-P3-Checker's sorry list, item 3. -/
theorem promoteL_spec {m m' : PMemo} {fuel : Nat} {h r : LIdx} {u : Level}
    {s s' : AState} (hwf : StoreWFP s.store) (hm : PMemoOK m s.store)
    (hd : denoteL s.store.ls h = some u)
    (hrun : promoteL m fuel h s = .ok ((m', r), s')) :
    StoreWFP s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersL r ∧ denoteL s'.store.ls r = some u ∧ PFrame s s' := by
  sorry

/-- con-leche: none — arena infrastructure; **`promoteLs` is exact.**

`sorry`: the list recursion over `promoteL_spec`.  Task #97-P3-Checker's
sorry list, item 3. -/
theorem promoteLs_spec {m m' : PMemo} {fuel : Nat} {h r : LsIdx}
    {us : List Level} {s s' : AState} (hwf : StoreWFP s.store)
    (hm : PMemoOK m s.store) (hd : denoteLs s.store.lss h = some us)
    (hrun : promoteLs m fuel h s = .ok ((m', r), s')) :
    StoreWFP s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersLs r ∧ denoteLs s'.store.lss r = some us ∧ PFrame s s' := by
  sorry

/-- con-leche: none — arena infrastructure; **`promoteE` is exact** — THE
exactness lemma `Arena/Promote.lean` names ("`denote (promote h) = denote h`
is the exactness lemma P3 owes").

`sorry`: the ten-arm fuel induction, in `Bridge/ExprOps/Inst1.lean`'s shape
(a `…Spec` record for one level, the per-arm step lemmas, `arm_hyp`), over
`EStore.internPersistent_spec` and the three lemmas above.  Task
#97-P3-Checker's sorry list, item 3, and the largest of them. -/
theorem promoteE_spec {m m' : PMemo} {fuel : Nat} {h r : EIdx} {e : Expr}
    {s s' : AState} (hwf : StoreWFP s.store) (hm : PMemoOK m s.store)
    (hd : denoteE s.store h = some e)
    (hrun : promoteE m fuel h s = .ok ((m', r), s')) :
    StoreWFP s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersE r ∧ denoteE s'.store r = some e ∧ PFrame s s' := by
  sorry

/-! ## The declaration layer

`Arena/Promote.lean`'s record walk, field for field, and the two entries the
fold calls.  Each is do-notation over the four above, so each is mechanical;
each is stated at the DENOTATION its consumer wants, which for the
declaration layer is `Arena/Frontend/Readback.lean`'s `denoteCV` / `denoteCI`
family. -/

/-- con-leche: none — arena infrastructure; **promoting a constant's header
keeps its denotation.**

`sorry`: three calls of `promoteN_spec`/`promoteE_spec` and the list lift.
Task #97-P3-Checker's sorry list, item 4. -/
theorem promoteCV_spec {m m' : PMemo} {fuel : Nat} {cv cv' : IConstantVal}
    {c : ConstantVal} {s s' : AState} (hwf : StoreWFP s.store)
    (hm : PMemoOK m s.store) (hd : Frontend.denoteCV s.store cv = some c)
    (hrun : promoteCV m fuel cv s = .ok ((m', cv'), s')) :
    StoreWFP s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersCV cv' ∧ Frontend.denoteCV s'.store cv' = some c ∧ PFrame s s' := by
  sorry

/-- con-leche: none — arena infrastructure; **promoting a stored constant
keeps its denotation** — the seven `IConstantInfo` constructors.

`sorry`: `promoteCV_spec` plus the rule / capability / projection-table
lifts.  Task #97-P3-Checker's sorry list, item 4. -/
theorem promoteCI_spec {m m' : PMemo} {fuel : Nat} {ci ci' : IConstantInfo}
    {c : ConstantInfo} {s s' : AState} (hwf : StoreWFP s.store)
    (hm : PMemoOK m s.store) (hd : Frontend.denoteCI s.store ci = some c)
    (hrun : promoteCI m fuel ci s = .ok ((m', ci'), s')) :
    StoreWFP s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersCI ci' ∧ Frontend.denoteCI s'.store ci' = some c ∧ PFrame s s' := by
  sorry

/-- con-leche: none — arena infrastructure; a block's constants, at ONE memo.

`sorry`: the list recursion over `promoteCI_spec`.  Task #97-P3-Checker's
sorry list, item 4. -/
theorem promoteCIList_spec {m m' : PMemo} {fuel : Nat}
    {cs cs' : List IConstantInfo} {xs : List ConstantInfo} {s s' : AState}
    (hwf : StoreWFP s.store) (hm : PMemoOK m s.store)
    (hd : Frontend.denoteCIList s.store cs = some xs)
    (hrun : promoteCIList m fuel cs s = .ok ((m', cs'), s')) :
    StoreWFP s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersCIList cs' ∧ Frontend.denoteCIList s'.store cs' = some xs ∧
      PFrame s s' := by
  sorry

/-- con-leche: none — arena infrastructure; **the install/check seam is
promoted exactly**: an `opaque`'s value is not in the environment, so the
`ValueGroup` is promoted beside it and at the SAME memo, and phase B therefore
checks the same term phase A installed.

`sorry`: `promoteCV_spec` and `promoteE_spec`.  Task #97-P3-Checker's sorry
list, item 4. -/
theorem promoteVG_spec {m m' : PMemo} {fuel : Nat} {g g' : Arena.ValueGroup}
    {c : ConstantVal} {e : Expr} {s s' : AState} (hwf : StoreWFP s.store)
    (hm : PMemoOK m s.store) (hcv : Frontend.denoteCV s.store g.cvA = some c)
    (hjv : denoteE s.store g.jv = some e)
    (hrun : promoteVG m fuel g s = .ok ((m', g'), s')) :
    StoreWFP s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersVG g' ∧ g'.kind = g.kind ∧
      Frontend.denoteCV s'.store g'.cvA = some c ∧
      denoteE s'.store g'.jv = some e ∧ PFrame s s' := by
  sorry

/-! ## The fold's entry

`promoteNew` is the only one of these the fold calls on the environment, and
its statement is what makes the per-declaration bridge work: **the environment
after the promotion denotes the environment before it**, and every handle in
it is persistent, so the `dropScratch` that follows changes nothing the fold
can see.

The index clause is the one `Arena/Promote.lean`'s `eraseInstalled` /
`indexPromoted` exist for: the promotion MOVES a name handle, so a row under
the old key must go, and the new rows must be re-inserted at the counters the
constants were pushed with — otherwise `IFEnv.find?` answers a constant under
a word `dropScratch` is about to hand back to the next declaration. -/

/-- con-leche: none — arena infrastructure; the denotation of an environment
INDEX: its constant list, read back.  §8.2's `denoteEnv`. -/
def denoteIEnv (st : EStore) (e : IEnv) : Option Env :=
  (Frontend.denoteCIList st e.consts).map Env.mk

/-- con-leche: none — arena infrastructure; the denotation of the indexed
environment is the denotation of its list (the index is a cache of the list,
DESIGN §8.3 lesson 13). -/
def denoteFEnv (st : EStore) (fe : IFEnv) : Option Env := denoteIEnv st fe.env

/-- con-leche: ConLeche/Kernel/FEnv.lean:62-66 mkFEnv — **the index is its
list's index**, which is con-leche's own join-point clause
(`Verify/Cached/BridgeC.lean:609`'s `fe' = mkFEnv fe'.env`).  `IFEnv.push`
preserves it; `IFEnv.restrictTo` does not, which is why phase B's prefix view
is handled by a congruence (`mkFEnv_find?_visibleBelow`) and not by this. -/
def IFEnvCoh (fe : IFEnv) : Prop := fe = mkIFEnv fe.env

/-- con-leche: ConLeche/Kernel/FEnv.lean:82-89 FEnv.push — **the step only
PUSHED**: everything the fold's step did to the environment was `IFEnv.push`,
so the old list is a suffix of the new one.  `Arena/Promote.lean`'s
`promoteNew` note is this fact in prose ("every install route in (B) grows the
environment by `IFEnv.push` alone […] so the `k` newest entries of
`fe.env.consts` are exactly the step's"), and it is what makes the promotion's
`k` mean what the fold thinks it means. -/
def Pushed (fe0 fe : IFEnv) : Prop :=
  ∃ new, fe.env.consts = new ++ fe0.env.consts

theorem Pushed.refl (fe : IFEnv) : Pushed fe fe := ⟨[], rfl⟩

theorem Pushed.trans {a b c : IFEnv} (h₁ : Pushed a b) (h₂ : Pushed b c) :
    Pushed a c := by
  obtain ⟨n₁, e₁⟩ := h₁
  obtain ⟨n₂, e₂⟩ := h₂
  exact ⟨n₂ ++ n₁, by rw [e₂, e₁, List.append_assoc]⟩

theorem Pushed.push (fe : IFEnv) (ci : IConstantInfo) : Pushed fe (fe.push ci) :=
  ⟨[ci], rfl⟩

/-- con-leche: none — arena infrastructure; **the fold's promotion is
exact**: the `k` constants the step installed are copied into the persistent
tier and re-indexed, and the environment denotes what it denoted.

`fe0` is the PRE-step environment and `k` the counter difference, which is
what `Arena/Checker.lean`'s `checkDeclStep` and `annotStep` compute; the
hypotheses say the step only pushed and that everything below it was already
persistent, which is the fold's own invariant one step earlier.

`sorry`: `promoteCIList_spec` on the `take k`, plus the index bookkeeping
(`eraseInstalled` / `indexPromoted` rebuild exactly the rows `mkIFEnv` would
give, which is what `IFEnvCoh` on both sides reduces the index clause to).
Task #97-P3-Checker's sorry list, item 5. -/
theorem promoteNew_spec {m m' : PMemo} {fuel k : Nat} {fe0 fe fe' : IFEnv}
    {env : Env} {s s' : AState} (hwf : StoreWFP s.store)
    (hm : PMemoOK m s.store) (hcoh0 : IFEnvCoh fe0) (hp0 : PersIFEnv fe0)
    (hcoh : IFEnvCoh fe) (hpush : Pushed fe0 fe)
    (hk : k = fe.visibleBelow - fe0.visibleBelow)
    (hd : denoteFEnv s.store fe = some env)
    (hrun : promoteNew m fuel k fe s = .ok ((m', fe'), s')) :
    StoreWFP s'.store ∧ Ext s.store s'.store ∧ PMemoOK m' s'.store ∧
      PersIFEnv fe' ∧ IFEnvCoh fe' ∧ denoteFEnv s'.store fe' = some env ∧
      fe'.visibleBelow = fe.visibleBelow ∧ PFrame s s' := by
  sorry

end ConRon.Bridge

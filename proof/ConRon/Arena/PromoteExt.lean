/-
# `ConRon.Arena.PromoteExt` — `Ext` across the PROMOTION

Task #97a, follow-up 4, second half.  `WFProofs.lean`'s last section gives
`Ext st st'` at every appending primitive of `Store.lean`; the promotion
(`Arena/Promote.lean`, task #97-P6-2) is the one entry that could not be
stated there, because it is MONADIC: twenty walks in
`AM = StateT AState (Except CheckError)`, not functions on an `EStore`.

Task #97-P5-2 §11 item 4 names `promote` beside `internBindI` and the three
node interns as an `Ext` the refinement demands and the store layer does not
supply, and `Bridge/Promote/Exact.lean`'s six-conjunct `promote*_spec`s each
carried `Ext s.store s'.store` and a `PFrame` among their `sorry`s.  Those two
conjuncts need **no hypothesis at all** — no `StoreWF`, no `PMemoOK`, no
denotation — because the promotion's only state-changing primitives are the
four `internPersistent*`, each of which appends and nothing else.  So they
are proved here, unconditionally and once, and what was left to the bridge
(proved there since) needs the invariant: `StoreWFP`, `PMemoOK`,
`PersE`, and `denote (promote h) = denote h`.

## The shape

`AExt s s'` is the bundle: the arena extended, and the three non-store fields
plus the scratch flag stood still.  That is exactly `Ext` ∧
`Bridge/Promote/Exact.lean`'s `PFrame`, and the promotion's own module note
("a promotion touches no memo table of `Monad.lean` at all") is what makes
the second half true.

`AExtOf a` is "`a` is such a step".  It is closed under `pure`, `fail`,
`bind` and the monad's readers, and holds of each `internPersistent*`; every
walk below is then that closure applied by `aext_auto`, a twenty-line
`repeat' first` over the leaves.  Two details earn their keep:

* **`with_reducible`.**  Without it the leaf `exact`s cost an `isDefEq`
  against every other primitive's unfolded body — `view ?h =?= promoteN m k p`
  delta-unfolds both — and four of the walks blow the default
  `maxHeartbeats`.  At reducible transparency a leaf either matches
  syntactically or fails at once, and the file elaborates at the default.
* **`refine AExtOf.bind ?_ fun _ => ?_` rather than `apply` + `intro`.**
  `AExtOf` is a `def` that unfolds to a `∀`, so a bare `intro` walks INTO the
  definition and strands the goal as a hypothesis about a run.  Introducing
  the binder in the `refine` keeps every goal at the `AExtOf` level.

Each walk is proved under a `…_aext` name and re-exported as `AExtOf.of_…`
immediately afterwards.  That is not cosmetic: `aext_auto`'s leaf list names
the `AExtOf.of_…` form, and if the theorem being proved carried that name the
tactic would close the goal with itself — a circular proof Lean rejects as a
failed termination check.  With the rename the leaf for a walk exists only
AFTER that walk is proved, and `first` skips an alternative naming a constant
that does not exist yet.
-/
import ConRon.Arena.Promote
import ConRon.Arena.PersistentRun

namespace ConRon.Arena

open ConLeche

/-! ## The step relation -/

/-- con-leche: none — arena infrastructure; **one `AM` step that only
appends**: the arena extends, and the memo tables, the caches, the pin table
and the scratch flag stand still.  `Ext` plus `Bridge/Promote/Exact.lean`'s
`PFrame`, as one predicate so that a caller's composition is one `trans` per
step. -/
structure AExt (s s' : AState) : Prop where
  /-- every handle that denoted in `s` denotes the same in `s'` -/
  ext : Ext s.store s'.store
  /-- the per-call memo tables did not move -/
  memos : s'.memos = s.memos
  /-- the per-declaration caches did not move -/
  caches : s'.caches = s.caches
  /-- the pin table did not move -/
  pins : s'.pins = s.pins
  /-- the tier the store is in did not change -/
  scratchOn : s'.store.scratchOn = s.store.scratchOn

/-- con-leche: none — arena infrastructure; no step at all is a step. -/
theorem AExt.refl (s : AState) : AExt s s := ⟨Ext.refl _, rfl, rfl, rfl, rfl⟩

/-- con-leche: none — arena infrastructure; two appends compose. -/
theorem AExt.trans {a b c : AState} (h₁ : AExt a b) (h₂ : AExt b c) : AExt a c :=
  ⟨h₁.ext.trans h₂.ext, by rw [h₂.memos, h₁.memos], by rw [h₂.caches, h₁.caches],
    by rw [h₂.pins, h₁.pins], by rw [h₂.scratchOn, h₁.scratchOn]⟩

/-- con-leche: none — arena infrastructure; **`a` is an appending step**:
whenever it succeeds, its post-state extends its pre-state.  Stated over the
run rather than over `a` itself, which is what makes it closed under `bind`. -/
def AExtOf {α : Type} (a : AM α) : Prop :=
  ∀ s r s', a s = .ok (r, s') → AExt s s'

/-- con-leche: none — arena infrastructure; `pure` moves nothing. -/
theorem AExtOf.of_pure {α : Type} (x : α) : AExtOf (Pure.pure x : AM α) := by
  intro s r s' h
  simp only [Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact AExt.refl _

/-- con-leche: none — arena infrastructure; a `fail` IS the error, at every
state — the one equation the failure arms below need. -/
theorem fail_apply {α : Type} (e : CheckError) (s : AState) :
    (fail e : AM α) s = .error e := rfl

/-- con-leche: none — arena infrastructure; a `fail` never succeeds, so it is
vacuously a step. -/
theorem AExtOf.of_fail {α : Type} (e : CheckError) : AExtOf (fail e : AM α) := by
  intro s r s' h
  rw [fail_apply] at h
  exact absurd h (by simp)

/-- con-leche: none — arena infrastructure; `get` moves nothing. -/
theorem AExtOf.of_get : AExtOf (get : AM AState) := by
  intro s r s' h
  simp only [get, getThe, MonadStateOf.get, StateT.get, Except.ok.injEq,
    Prod.mk.injEq, pure, Except.pure] at h
  obtain ⟨-, rfl⟩ := h
  exact AExt.refl _

/-- con-leche: none — arena infrastructure; **the closure property**: a step
followed by a step is a step.  This is the whole content of the walks below. -/
theorem AExtOf.bind {α β : Type} {a : AM α} {f : α → AM β}
    (ha : AExtOf a) (hf : ∀ x, AExtOf (f x)) : AExtOf (a >>= f) := by
  intro s r s' h
  simp only [Bind.bind, StateT.bind] at h
  cases hax : a s with
  | error e => rw [hax] at h; simp [Except.bind] at h
  | ok p =>
    rw [hax] at h
    simp only [Except.bind] at h
    exact (ha s p.1 p.2 hax).trans (hf p.1 p.2 r s' h)

/-! ## The primitives — the four `internPersistent*`

The only state-changing operations the promotion performs.  Each is
`intern`'s persistent branch behind a cons probe and a capacity test, so each
has three outcomes: a hit that moves nothing, a miss that appends (where
`WFProofs.lean`'s `…Persistent_ext` is quoted), and the `Native` the
capacity test raises, which never succeeds. -/

/-- con-leche: none — arena infrastructure; read a run off an `Except.ok`
equation: the post-state is whatever the left-hand side named. -/
theorem AExt.of_run_eq {α : Type} {x y : α} {s t s' : AState}
    (h : (Except.ok (x, t) : Except CheckError (α × AState)) = .ok (y, s'))
    (hx : AExt s t) : AExt s s' := by
  have hs : t = s' := congrArg Prod.snd (Except.ok.inj h)
  subst hs
  exact hx

theorem internPersistentN_aext {v : NNodeView} {s : AState} {r : NIdx} {s' : AState}
    (h : internPersistentN v s = .ok (r, s')) : AExt s s' := by
  cases hf : s.store.ns.pers.find? v with
  | some hh =>
    simp only [internPersistentN, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf] at h
    exact AExt.of_run_eq h (AExt.refl _)
  | none =>
    by_cases hc : s.store.ns.pers.sizeOf v < Idx.idxCap
    · simp only [internPersistentN, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
        if_pos hc] at h
      exact AExt.of_run_eq h
        ⟨EStore.internNamePersistent_ext s.store v, rfl, rfl, rfl,
          EStore.scratchOn_internNamePersistent s.store v⟩
    · simp only [internPersistentN, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        if_neg hc, fail_apply] at h
      exact absurd h (by simp)

theorem AExtOf.of_internPersistentN (v : NNodeView) :
    AExtOf (internPersistentN v) := fun _ _ _ h => internPersistentN_aext h

theorem internPersistentL_aext {v : LNodeView} {s : AState} {r : LIdx} {s' : AState}
    (h : internPersistentL v s = .ok (r, s')) : AExt s s' := by
  cases hf : s.store.ls.pers.find? v with
  | some hh =>
    simp only [internPersistentL, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf] at h
    exact AExt.of_run_eq h (AExt.refl _)
  | none =>
    by_cases hc : s.store.ls.pers.sizeOf v < Idx.idxCap
    · simp only [internPersistentL, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
        if_pos hc] at h
      exact AExt.of_run_eq h
        ⟨EStore.internLevelPersistent_ext s.store v, rfl, rfl, rfl,
          EStore.scratchOn_internLevelPersistent s.store v⟩
    · simp only [internPersistentL, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        if_neg hc, fail_apply] at h
      exact absurd h (by simp)

theorem AExtOf.of_internPersistentL (v : LNodeView) :
    AExtOf (internPersistentL v) := fun _ _ _ h => internPersistentL_aext h

theorem internPersistentLs_aext {v : LsNodeView} {s : AState} {r : LsIdx} {s' : AState}
    (h : internPersistentLs v s = .ok (r, s')) : AExt s s' := by
  cases hf : s.store.lss.pers.find? v with
  | some hh =>
    simp only [internPersistentLs, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf] at h
    exact AExt.of_run_eq h (AExt.refl _)
  | none =>
    by_cases hc : s.store.lss.pers.sizeOf v < Idx.idxCap
    · simp only [internPersistentLs, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
        if_pos hc] at h
      exact AExt.of_run_eq h
        ⟨EStore.internLevelsPersistent_ext s.store v, rfl, rfl, rfl,
          EStore.scratchOn_internLevelsPersistent s.store v⟩
    · simp only [internPersistentLs, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        if_neg hc, fail_apply] at h
      exact absurd h (by simp)

theorem AExtOf.of_internPersistentLs (v : LsNodeView) :
    AExtOf (internPersistentLs v) := fun _ _ _ h => internPersistentLs_aext h

theorem internPersistentE_aext {v : ENodeView} {s : AState} {r : EIdx} {s' : AState}
    (h : internPersistentE v s = .ok (r, s')) : AExt s s' := by
  obtain ⟨-, -, -, rfl⟩ := internPersistentE_ok h
  exact ⟨EStore.internPersistent_ext s.store v, rfl, rfl, rfl,
    EStore.scratchOn_internPersistent s.store v⟩

theorem AExtOf.of_internPersistentE (v : ENodeView) :
    AExtOf (internPersistentE v) := fun _ _ _ h => internPersistentE_aext h

/-! ## The readers

`viewN` / `viewL` / `viewLs` / `view` read the store and either answer or
fail; neither arm writes. -/

theorem viewN_aext {h : NIdx} {s : AState} {r : NNodeView} {s' : AState}
    (hr : viewN h s = .ok (r, s')) : AExt s s' := by
  cases hv : s.store.ns.view h with
  | some v =>
    simp only [viewN, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, Except.bind, Except.pure, hv] at hr
    exact AExt.of_run_eq hr (AExt.refl _)
  | none =>
    simp only [viewN, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, Except.bind, Except.pure, hv, fail_apply] at hr
    exact absurd hr (by simp)

theorem AExtOf.of_viewN (h : NIdx) : AExtOf (viewN h) := fun _ _ _ hr => viewN_aext hr

theorem viewL_aext {h : LIdx} {s : AState} {r : LNodeView} {s' : AState}
    (hr : viewL h s = .ok (r, s')) : AExt s s' := by
  cases hv : s.store.ls.view h with
  | some v =>
    simp only [viewL, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, Except.bind, Except.pure, hv] at hr
    exact AExt.of_run_eq hr (AExt.refl _)
  | none =>
    simp only [viewL, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, Except.bind, Except.pure, hv, fail_apply] at hr
    exact absurd hr (by simp)

theorem AExtOf.of_viewL (h : LIdx) : AExtOf (viewL h) := fun _ _ _ hr => viewL_aext hr

theorem viewLs_aext {h : LsIdx} {s : AState} {r : LsNodeView} {s' : AState}
    (hr : viewLs h s = .ok (r, s')) : AExt s s' := by
  cases hv : s.store.lss.view h with
  | some v =>
    simp only [viewLs, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, Except.bind, Except.pure, hv] at hr
    exact AExt.of_run_eq hr (AExt.refl _)
  | none =>
    simp only [viewLs, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, Except.bind, Except.pure, hv, fail_apply] at hr
    exact absurd hr (by simp)

theorem AExtOf.of_viewLs (h : LsIdx) : AExtOf (viewLs h) :=
  fun _ _ _ hr => viewLs_aext hr

theorem view_aext {h : EIdx} {s : AState} {r : ENodeView} {s' : AState}
    (hr : view h s = .ok (r, s')) : AExt s s' := by
  cases hv : s.store.view h with
  | some v =>
    simp only [view, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, Except.bind, Except.pure, hv] at hr
    exact AExt.of_run_eq hr (AExt.refl _)
  | none =>
    simp only [view, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, Except.bind, Except.pure, hv, fail_apply] at hr
    exact absurd hr (by simp)

theorem AExtOf.of_view (h : EIdx) : AExtOf (view h) := fun _ _ _ hr => view_aext hr

/-! ## The peeling tactic -/

set_option hygiene false in
/-- Peel an `AM` program down to its leaves: `pure`, `fail`, the readers, the
four persistent interns and the promotion walks already proved.  The `ih`
clauses are the fuel and list inductions' own hypotheses, which is why the
macro is `hygiene false` (`tag_cases` above takes the same licence).

Each walk below is proved under a `…_aext` name and re-exported as
`AExtOf.of_…` immediately afterwards, so that the macro's own leaf list never
names the theorem it is being run inside: a `first` alternative that mentions
a constant that does not yet exist is simply skipped. -/
macro "aext_auto" : tactic => `(tactic|
  repeat' first
    | with_reducible exact AExtOf.of_pure _
    | with_reducible exact AExtOf.of_fail _
    | with_reducible exact ih
    | with_reducible exact ih _
    | with_reducible exact ih _ _
    | with_reducible exact ih _ _ _
    | with_reducible exact AExtOf.of_view _
    | with_reducible exact AExtOf.of_viewN _
    | with_reducible exact AExtOf.of_viewL _
    | with_reducible exact AExtOf.of_viewLs _
    | with_reducible exact AExtOf.of_internPersistentE _
    | with_reducible exact AExtOf.of_internPersistentN _
    | with_reducible exact AExtOf.of_internPersistentL _
    | with_reducible exact AExtOf.of_internPersistentLs _
    | with_reducible exact AExtOf.of_promoteN _ _ _
    | with_reducible exact AExtOf.of_promoteL _ _ _
    | with_reducible exact AExtOf.of_promoteLList _ _ _
    | with_reducible exact AExtOf.of_promoteLs _ _ _
    | with_reducible exact AExtOf.of_promoteE _ _ _
    | with_reducible exact AExtOf.of_promoteNList _ _ _
    | with_reducible exact AExtOf.of_promoteEList _ _ _
    | with_reducible exact AExtOf.of_promoteCV _ _ _
    | with_reducible exact AExtOf.of_promoteFire _ _ _
    | with_reducible exact AExtOf.of_promoteRule _ _ _
    | with_reducible exact AExtOf.of_promoteRules _ _ _
    | with_reducible exact AExtOf.of_promoteCaps _ _ _
    | with_reducible exact AExtOf.of_promoteProjTable _ _ _
    | with_reducible exact AExtOf.of_promoteCI _ _ _
    | with_reducible exact AExtOf.of_promoteCIList _ _ _
    | with_reducible refine AExtOf.bind ?_ fun _ => ?_
    | split)

/-! ## The walks

`promoteN` / `promoteL` / `promoteLList` / `promoteLs` / `promoteE` and the
two handle lists.  Each is `aext_auto` over the leaves above plus its own
induction hypothesis — the fuel's for the three fuelled walks, the list's for
the four list recursions. -/

theorem promoteN_aext (m : PMemo) (fuel : Nat) (h : NIdx) :
    AExtOf (promoteN m fuel h) := by
  induction fuel generalizing m h with
  | zero => exact AExtOf.of_fail _
  | succ k ih => unfold promoteN; aext_auto

theorem AExtOf.of_promoteN (m : PMemo) (fuel : Nat) (h : NIdx) :
    AExtOf (promoteN m fuel h) := promoteN_aext m fuel h

theorem promoteL_aext (m : PMemo) (fuel : Nat) (h : LIdx) :
    AExtOf (promoteL m fuel h) := by
  induction fuel generalizing m h with
  | zero => exact AExtOf.of_fail _
  | succ k ih => unfold promoteL; aext_auto

theorem AExtOf.of_promoteL (m : PMemo) (fuel : Nat) (h : LIdx) :
    AExtOf (promoteL m fuel h) := promoteL_aext m fuel h

theorem promoteLList_aext (m : PMemo) (fuel : Nat) (us : List LIdx) :
    AExtOf (promoteLList m fuel us) := by
  induction us generalizing m with
  | nil => exact AExtOf.of_pure _
  | cons a as ih => unfold promoteLList; aext_auto

theorem AExtOf.of_promoteLList (m : PMemo) (fuel : Nat) (us : List LIdx) :
    AExtOf (promoteLList m fuel us) := promoteLList_aext m fuel us

theorem promoteLs_aext (m : PMemo) (fuel : Nat) (h : LsIdx) :
    AExtOf (promoteLs m fuel h) := by
  unfold promoteLs; aext_auto

theorem AExtOf.of_promoteLs (m : PMemo) (fuel : Nat) (h : LsIdx) :
    AExtOf (promoteLs m fuel h) := promoteLs_aext m fuel h

theorem promoteE_aext (m : PMemo) (fuel : Nat) (h : EIdx) :
    AExtOf (promoteE m fuel h) := by
  induction fuel generalizing m h with
  | zero => exact AExtOf.of_fail _
  | succ k ih => unfold promoteE; aext_auto

theorem AExtOf.of_promoteE (m : PMemo) (fuel : Nat) (h : EIdx) :
    AExtOf (promoteE m fuel h) := promoteE_aext m fuel h

theorem promoteNList_aext (m : PMemo) (fuel : Nat) (ns : List NIdx) :
    AExtOf (promoteNList m fuel ns) := by
  induction ns generalizing m with
  | nil => exact AExtOf.of_pure _
  | cons a as ih => unfold promoteNList; aext_auto

theorem AExtOf.of_promoteNList (m : PMemo) (fuel : Nat) (ns : List NIdx) :
    AExtOf (promoteNList m fuel ns) := promoteNList_aext m fuel ns

theorem promoteEList_aext (m : PMemo) (fuel : Nat) (es : List EIdx) :
    AExtOf (promoteEList m fuel es) := by
  induction es generalizing m with
  | nil => exact AExtOf.of_pure _
  | cons a as ih => unfold promoteEList; aext_auto

theorem AExtOf.of_promoteEList (m : PMemo) (fuel : Nat) (es : List EIdx) :
    AExtOf (promoteEList m fuel es) := promoteEList_aext m fuel es

/-! ## The declaration layer

`Arena/Env.lean`'s record field for field, and `promoteNew`, the entry the
phase-A bracket calls.  Nothing here touches the store except through the
walks above, so every one of them is the same one-line tactic. -/

theorem promoteCV_aext (m : PMemo) (fuel : Nat) (cv : IConstantVal) :
    AExtOf (promoteCV m fuel cv) := by
  unfold promoteCV; aext_auto

theorem AExtOf.of_promoteCV (m : PMemo) (fuel : Nat) (cv : IConstantVal) :
    AExtOf (promoteCV m fuel cv) := promoteCV_aext m fuel cv

theorem promoteFire_aext (m : PMemo) (fuel : Nat) (f : IRecRuleFire) :
    AExtOf (promoteFire m fuel f) := by
  cases f <;> (unfold promoteFire; aext_auto)

theorem AExtOf.of_promoteFire (m : PMemo) (fuel : Nat) (f : IRecRuleFire) :
    AExtOf (promoteFire m fuel f) := promoteFire_aext m fuel f

theorem promoteRule_aext (m : PMemo) (fuel : Nat) (rl : IRecRule) :
    AExtOf (promoteRule m fuel rl) := by
  unfold promoteRule; aext_auto

theorem AExtOf.of_promoteRule (m : PMemo) (fuel : Nat) (rl : IRecRule) :
    AExtOf (promoteRule m fuel rl) := promoteRule_aext m fuel rl

theorem promoteRules_aext (m : PMemo) (fuel : Nat) (rs : List IRecRule) :
    AExtOf (promoteRules m fuel rs) := by
  induction rs generalizing m with
  | nil => exact AExtOf.of_pure _
  | cons a as ih => unfold promoteRules; aext_auto

theorem AExtOf.of_promoteRules (m : PMemo) (fuel : Nat) (rs : List IRecRule) :
    AExtOf (promoteRules m fuel rs) := promoteRules_aext m fuel rs

theorem promoteCaps_aext (m : PMemo) (fuel : Nat) (c : IIndCaps) :
    AExtOf (promoteCaps m fuel c) := by
  unfold promoteCaps; aext_auto

theorem AExtOf.of_promoteCaps (m : PMemo) (fuel : Nat) (c : IIndCaps) :
    AExtOf (promoteCaps m fuel c) := promoteCaps_aext m fuel c

theorem promoteProjTable_aext (m : PMemo) (fuel : Nat) (t : IProjTable) :
    AExtOf (promoteProjTable m fuel t) := by
  unfold promoteProjTable; aext_auto

theorem AExtOf.of_promoteProjTable (m : PMemo) (fuel : Nat) (t : IProjTable) :
    AExtOf (promoteProjTable m fuel t) := promoteProjTable_aext m fuel t

theorem promoteCI_aext (m : PMemo) (fuel : Nat) (ci : IConstantInfo) :
    AExtOf (promoteCI m fuel ci) := by
  cases ci <;> (unfold promoteCI; aext_auto)

theorem AExtOf.of_promoteCI (m : PMemo) (fuel : Nat) (ci : IConstantInfo) :
    AExtOf (promoteCI m fuel ci) := promoteCI_aext m fuel ci

theorem promoteCIList_aext (m : PMemo) (fuel : Nat) (cs : List IConstantInfo) :
    AExtOf (promoteCIList m fuel cs) := by
  induction cs generalizing m with
  | nil => exact AExtOf.of_pure _
  | cons a as ih => unfold promoteCIList; aext_auto

theorem AExtOf.of_promoteCIList (m : PMemo) (fuel : Nat) (cs : List IConstantInfo) :
    AExtOf (promoteCIList m fuel cs) := promoteCIList_aext m fuel cs

theorem promoteDecl_aext (m : PMemo) (fuel : Nat) (d : IDeclaration) :
    AExtOf (promoteDecl m fuel d) := by
  cases d <;> (unfold promoteDecl; aext_auto)

theorem AExtOf.of_promoteDecl (m : PMemo) (fuel : Nat) (d : IDeclaration) :
    AExtOf (promoteDecl m fuel d) := promoteDecl_aext m fuel d

theorem promoteVG_aext (m : PMemo) (fuel : Nat) (g : ValueGroup) :
    AExtOf (promoteVG m fuel g) := by
  unfold promoteVG; aext_auto

theorem AExtOf.of_promoteVG (m : PMemo) (fuel : Nat) (g : ValueGroup) :
    AExtOf (promoteVG m fuel g) := promoteVG_aext m fuel g

theorem promoteNew_aext (m : PMemo) (fuel k : Nat) (fe : IFEnv) :
    AExtOf (promoteNew m fuel k fe) := by
  unfold promoteNew; aext_auto

theorem AExtOf.of_promoteNew (m : PMemo) (fuel k : Nat) (fe : IFEnv) :
    AExtOf (promoteNew m fuel k fe) := promoteNew_aext m fuel k fe


/-! ## The `Ext` corollaries

What `Bridge/Promote/Exact.lean`'s `promote*_spec` conjuncts ask for, in the
shape they ask for it.  `AExt` carries the frame too (`.memos`, `.caches`,
`.pins`, `.scratchOn`), so a consumer that wants `PFrame` reads the same
value. -/

/-- con-leche: none — arena infrastructure; **promoting a NAME extends the
arena.** -/
theorem promoteN_ext {m m' : PMemo} {fuel : Nat} {h r : NIdx} {s s' : AState}
    (hrun : promoteN m fuel h s = .ok ((m', r), s')) : Ext s.store s'.store :=
  (promoteN_aext m fuel h s (m', r) s' hrun).ext

/-- con-leche: none — arena infrastructure; **promoting a LEVEL extends the
arena.** -/
theorem promoteL_ext {m m' : PMemo} {fuel : Nat} {h r : LIdx} {s s' : AState}
    (hrun : promoteL m fuel h s = .ok ((m', r), s')) : Ext s.store s'.store :=
  (promoteL_aext m fuel h s (m', r) s' hrun).ext

/-- con-leche: none — arena infrastructure; **promoting a universe-argument
LIST extends the arena.** -/
theorem promoteLs_ext {m m' : PMemo} {fuel : Nat} {h r : LsIdx} {s s' : AState}
    (hrun : promoteLs m fuel h s = .ok ((m', r), s')) : Ext s.store s'.store :=
  (promoteLs_aext m fuel h s (m', r) s' hrun).ext

/-- con-leche: none — arena infrastructure; **promoting an EXPRESSION extends
the arena** — the `Ext` conjunct of `Bridge/Promote/Exact.lean`'s
`promoteE_spec`, THE exactness lemma of promotion (proved; it takes the
conjunct from `promoteE_aext` directly, as this lemma does). -/
theorem promoteE_ext {m m' : PMemo} {fuel : Nat} {h r : EIdx} {s s' : AState}
    (hrun : promoteE m fuel h s = .ok ((m', r), s')) : Ext s.store s'.store :=
  (promoteE_aext m fuel h s (m', r) s' hrun).ext

/-- con-leche: none — arena infrastructure; promoting a stored CONSTANT
extends the arena. -/
theorem promoteCI_ext {m m' : PMemo} {fuel : Nat} {ci r : IConstantInfo}
    {s s' : AState} (hrun : promoteCI m fuel ci s = .ok ((m', r), s')) :
    Ext s.store s'.store :=
  (promoteCI_aext m fuel ci s (m', r) s' hrun).ext

/-- con-leche: none — arena infrastructure; promoting a DECLARATION record
extends the arena. -/
theorem promoteDecl_ext {m m' : PMemo} {fuel : Nat} {d r : IDeclaration}
    {s s' : AState} (hrun : promoteDecl m fuel d s = .ok ((m', r), s')) :
    Ext s.store s'.store :=
  (promoteDecl_aext m fuel d s (m', r) s' hrun).ext

/-- con-leche: none — arena infrastructure; promoting the install/check seam
extends the arena. -/
theorem promoteVG_ext {m m' : PMemo} {fuel : Nat} {g r : ValueGroup}
    {s s' : AState} (hrun : promoteVG m fuel g s = .ok ((m', r), s')) :
    Ext s.store s'.store :=
  (promoteVG_aext m fuel g s (m', r) s' hrun).ext

/-- con-leche: none — arena infrastructure; **the phase-A bracket's promotion
half extends the arena** — the fold's own entry. -/
theorem promoteNew_ext {m m' : PMemo} {fuel k : Nat} {fe r : IFEnv}
    {s s' : AState} (hrun : promoteNew m fuel k fe s = .ok ((m', r), s')) :
    Ext s.store s'.store :=
  (promoteNew_aext m fuel k fe s (m', r) s' hrun).ext

/-! ## The trust census

`[propext, Classical.choice, Quot.sound]` and nothing else — no `sorryAx`,
and (task #97a's arithmetic packing) no `bv_decide` axiom. -/

#print axioms Ext.of_view_mono
#print axioms EStore.internBindI_ext
#print axioms EStore.internBM_ext
#print axioms EStore.internAt_ext
#print axioms EStore.internPersistent_ext
#print axioms EStore.internName_ext
#print axioms EStore.internLevel_ext
#print axioms EStore.internLevels_ext
#print axioms NStore.internPersistent_ext
#print axioms LStore.internPersistent_ext
#print axioms LsStore.internPersistent_ext
#print axioms promoteN_ext
#print axioms promoteL_ext
#print axioms promoteLs_ext
#print axioms promoteE_ext
#print axioms promoteCI_ext
#print axioms promoteDecl_ext
#print axioms promoteVG_ext
#print axioms promoteNew_ext

end ConRon.Arena

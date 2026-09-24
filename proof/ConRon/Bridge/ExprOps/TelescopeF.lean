/-
# `ConRon.Bridge.ExprOps.TelescopeF` — Theorem 1 for the BATCHED telescope
peels, and for `recRulePlain`

The tail of phase P3's group D, split off `ExprOps/Spine.lean` because that
file's elaboration had reached 30 s with seventeen twins in it (task #97s
round 2's style rule: split rather than fight).  Five twins:
`instPisAtFGo` (:1252), `instPisAtF` (:1269), `instLamsAtFGo` (:1277),
`instLamsAtF` (:1294) and `recRulePlain` (:1330).

## The accumulator's ORIENTATION — the one fact this file exists to pin down

Task #97-P6-15 moved thirteen accumulator sites from a `List` built with
`::` to an `Array` built with `Array.push`; `instPisAtFGo` and
`instLamsAtFGo` are two of them.  con-leche's `instPisAtFGo (a :: acc)`
prepends, the twin's `instPisAtFGo (acc.push a)` appends, so

> **an accumulator array that denotes `L` in array order is con-leche's
> `L.reverse`.**

Every statement below therefore applies con-leche's function at
`eacc.reverse`, and the `push` step's arithmetic is
`(eacc ++ [ea]).reverse = ea :: eacc.reverse` — which is exactly
con-leche's `a :: acc`.  `ExprOpsTest.lean`'s `instantiateList` guards are
the same reversal's own test, computed rather than written out
(`con-leche's [cf, s1] is the twin's #[s1, cf]`), and
`InstListSpec` below carries the same `.reverse` for
`instantiateListFast`.

## The axiom check

**Nothing in this file is unproved**, and since task #97-P3-1 nothing it
consumes is either: `instPisAtFGo_spec`, `instLamsAtFGo_spec`,
`recRulePlain_spec`, `instPisAtF_spec` and `instLamsAtF_spec` all report
`[propext, Classical.choice, Quot.sound]`.  The last two used to inherit
`ExprOps/Inst1`'s open goals through `ExprOps/Spine`'s `instPisAt_spec` /
`instLamsAt_spec`; the arm split closed those.

## `instantiateListFast` as a HYPOTHESIS

The four `…F` twins call `instantiateListFast`, whose Theorem 1 belongs to
this tier's `Subst` group and does not exist yet.  `InstListSpec` is that
theorem as a record, in the shape `instantiate1Fast_spec` already has —
metavariable-free, because the substituted LIST's denotation is quantified
inside `RelEA` and not named in the precondition (template rule 4).  When
`Subst.lean` lands the record is discharged at its own
`instantiateListFast_spec` and the four theorems become unconditional;
nothing in their statements changes.
-/
import ConRon.Bridge.ExprOps.Spine

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

attribute [-grind] RelE.ext RelE.of_ext RelE.retarget

/-! ## 1. `instantiateListFast`'s Theorem 1, as a record -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1 for
`instantiateListFast`, taken as a hypothesis (the `Subst` group owns its
proof).  The `.reverse` is task #97-P6-15's push-order accumulator: the
array's entry `j` from the END is con-leche's `vs[j]`. -/
structure InstListSpec (fuel : Nat) : Prop where
  run : ∀ (s₁ : AState) (e : EIdx) (vs : Array EIdx) (d : Nat), StateOK s₁ →
    (denoteE s₁.store e).isSome = true →
    (Frontend.denoteEList s₁.store vs.toList).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ instantiateListFast fuel e vs d
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        RelEA (fun x ws => x.instantiateList ws.reverse d) s₁.store e
          vs.toList s'.store r⌝⦄

/-! ## 2. The three step lemmas of a BATCHED peel

`RelEPAA` is `RelEP` with the argument list AND the pending accumulator as
extra subjects, both quantified inside the relation.  These three lemmas
belong in `Bridge/Rel.lean` group 7 beside `RelEPA`'s. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1181-1190 instPisAtFGo — the NIL
clause: the argument list is exhausted, so the residual receives the whole
accumulator in ONE `instantiateList` traversal (that is the lever). -/
theorem RelEPAA.nil_step
    {F : Expr → List Expr → List Expr → Option (List Expr × Expr)}
    {st s1 : EStore} {e r : EIdx} {acc : List EIdx} {d : Nat}
    (hg : RelEA (fun x ws => x.instantiateList ws.reverse d) st e acc s1 r)
    (hdec : ∀ x ws, F x ws [] = some ([], x.instantiateList ws.reverse d)) :
    RelEPAA F st e acc [] s1 (some ([], r)) := by
  intro x eacc es hx hacc hes
  simp only [Frontend.denoteEList, Option.some.injEq] at hes
  subst hes
  rw [hdec]
  simp only [denoteEP, Frontend.denoteEList, hg x eacc hx hacc]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1181-1190 instPisAtFGo — the CONS
clause: peel the raw `∀` binder, PUSH its argument, recurse, and give the
domain the accumulator it had at THIS level.  `hpush` is where the
orientation is discharged: the twin's `(acc.push a).toList` is
`acc.toList ++ [a]`, whose denotation reverses to con-leche's `a :: acc`. -/
theorem RelEPAA.forallE_step
    {F Fr : Expr → List Expr → List Expr → Option (List Expr × Expr)}
    {st s1 s2 : EStore} {h dom body a dh : EIdx} {p : List EIdx × EIdx}
    {acc accP as : List EIdx} {ea : Expr} {m : BinderMeta} {d : Nat}
    (hwf : StoreWF st) (hview : st.view h = some (.forallE dom body m))
    (hea : denoteE st a = some ea)
    (hx1 : Ext st s1) (hx2 : Ext s1 s2)
    (hrec : RelEPAA Fr st body accP as s1 (some p))
    (hdom : RelEA (fun x ws => x.instantiateList ws.reverse d) s1 dom acc s2 dh)
    (hpush : accP = acc ++ [a])
    (hdec : ∀ x y ws ys ds res, Fr y (ws ++ [ea]) ys = some (ds, res) →
      F (.forallE x y m) ws (ea :: ys) =
        some (x.instantiateList ws.reverse d :: ds, res)) :
    RelEPAA F st h acc (a :: as) s2 (some (dh :: p.1, p.2)) := by
  subst hpush
  intro x eacc es hx hacc hes
  obtain ⟨edom, ebody, rfl, hdt, hdb⟩ := denote_forallE_inv hwf hview hx
  simp only [Frontend.denoteEList] at hes
  cases has : Frontend.denoteEList st as with
  | none => rw [hea, has] at hes; simp at hes
  | some eas =>
    rw [hea, has] at hes
    obtain rfl := Option.some.inj hes
    obtain ⟨ds, res, hres, hdds, hdres⟩ :=
      denoteEP_some_inv
        (hrec ebody (eacc ++ [ea]) eas hdb
          (denoteEList_snoc hea acc eacc hacc) has)
    rw [hdec edom ebody eacc eas ds res hres]
    simp only [denoteEP, Frontend.denoteEList,
      hdom edom eacc (denote_ext hdt hx1)
        (denoteEList_ext hx1 acc eacc hacc),
      denoteEList_ext hx2 p.1 ds hdds, denote_ext hdres hx2]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1198-1204 instLamsAtFGo — the same
at a λ binder. -/
theorem RelEPAA.lam_step
    {F Fr : Expr → List Expr → List Expr → Option (List Expr × Expr)}
    {st s1 s2 : EStore} {h dom body a dh : EIdx} {p : List EIdx × EIdx}
    {acc accP as : List EIdx} {ea : Expr} {m : BinderMeta} {d : Nat}
    (hwf : StoreWF st) (hview : st.view h = some (.lam dom body m))
    (hea : denoteE st a = some ea)
    (hx1 : Ext st s1) (hx2 : Ext s1 s2)
    (hrec : RelEPAA Fr st body accP as s1 (some p))
    (hdom : RelEA (fun x ws => x.instantiateList ws.reverse d) s1 dom acc s2 dh)
    (hpush : accP = acc ++ [a])
    (hdec : ∀ x y ws ys ds res, Fr y (ws ++ [ea]) ys = some (ds, res) →
      F (.lam x y m) ws (ea :: ys) =
        some (x.instantiateList ws.reverse d :: ds, res)) :
    RelEPAA F st h acc (a :: as) s2 (some (dh :: p.1, p.2)) := by
  subst hpush
  intro x eacc es hx hacc hes
  obtain ⟨edom, ebody, rfl, hdt, hdb⟩ := denote_lam_inv hwf hview hx
  simp only [Frontend.denoteEList] at hes
  cases has : Frontend.denoteEList st as with
  | none => rw [hea, has] at hes; simp at hes
  | some eas =>
    rw [hea, has] at hes
    obtain rfl := Option.some.inj hes
    obtain ⟨ds, res, hres, hdds, hdres⟩ :=
      denoteEP_some_inv
        (hrec ebody (eacc ++ [ea]) eas hdb
          (denoteEList_snoc hea acc eacc hacc) has)
    rw [hdec edom ebody eacc eas ds res hres]
    simp only [denoteEP, Frontend.denoteEList,
      hdom edom eacc (denote_ext hdt hx1)
        (denoteEList_ext hx1 acc eacc hacc),
      denoteEList_ext hx2 p.1 ds hdds, denote_ext hdres hx2]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1181-1190 instPisAtFGo — the
`none` clause at a `∀`. -/
theorem RelEPAA.noneF_step
    {F Fr : Expr → List Expr → List Expr → Option (List Expr × Expr)}
    {st s1 : EStore} {h dom body a : EIdx} {acc accP as : List EIdx}
    {ea : Expr} {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.forallE dom body m))
    (hea : denoteE st a = some ea)
    (hrec : RelEPAA Fr st body accP as s1 none)
    (hpush : accP = acc ++ [a])
    (hdec : ∀ y ws ys, Fr y (ws ++ [ea]) ys = none →
      ∀ x, F (.forallE x y m) ws (ea :: ys) = none) :
    RelEPAA F st h acc (a :: as) s1 none := by
  subst hpush
  intro x eacc es hx hacc hes
  obtain ⟨edom, ebody, rfl, hdt, hdb⟩ := denote_forallE_inv hwf hview hx
  simp only [Frontend.denoteEList] at hes
  cases has : Frontend.denoteEList st as with
  | none => rw [hea, has] at hes; simp at hes
  | some eas =>
    rw [hea, has] at hes
    obtain rfl := Option.some.inj hes
    have hh :=
      hrec ebody (eacc ++ [ea]) eas hdb (denoteEList_snoc hea acc eacc hacc) has
    simp only [denoteEP, Option.some.injEq] at hh
    rw [hdec ebody eacc eas hh.symm edom, denoteEP]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1198-1204 instLamsAtFGo — the
`none` clause at a λ. -/
theorem RelEPAA.noneL_step
    {F Fr : Expr → List Expr → List Expr → Option (List Expr × Expr)}
    {st s1 : EStore} {h dom body a : EIdx} {acc accP as : List EIdx}
    {ea : Expr} {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.lam dom body m))
    (hea : denoteE st a = some ea)
    (hrec : RelEPAA Fr st body accP as s1 none)
    (hpush : accP = acc ++ [a])
    (hdec : ∀ y ws ys, Fr y (ws ++ [ea]) ys = none →
      ∀ x, F (.lam x y m) ws (ea :: ys) = none) :
    RelEPAA F st h acc (a :: as) s1 none := by
  subst hpush
  intro x eacc es hx hacc hes
  obtain ⟨edom, ebody, rfl, hdt, hdb⟩ := denote_lam_inv hwf hview hx
  simp only [Frontend.denoteEList] at hes
  cases has : Frontend.denoteEList st as with
  | none => rw [hea, has] at hes; simp at hes
  | some eas =>
    rw [hea, has] at hes
    obtain rfl := Option.some.inj hes
    have hh :=
      hrec ebody (eacc ++ [ea]) eas hdb (denoteEList_snoc hea acc eacc hacc) has
    simp only [denoteEP, Option.some.injEq] at hh
    rw [hdec ebody eacc eas hh.symm edom, denoteEP]

/-- con-leche: none — `RelEPAA` at a fallthrough arm that answers `none`: the
RAW telescope is shorter than the argument list, which is the branch the
wrapper's fallback exists for. -/
theorem RelEPAA.none_of_view_cons
    {F : Expr → List Expr → List Expr → Option (List Expr × Expr)}
    {st : EStore} {h a : EIdx} {v : ENodeView} {acc as : List EIdx}
    (hwf : StoreWF st) (hview : st.view h = some v)
    (hf : ∀ e ws x xs, denoteEView st v = some e → F e ws (x :: xs) = none) :
    RelEPAA F st h acc (a :: as) st none := by
  intro e eacc es he hacc hes
  rw [denoteE_view_eq hwf hview] at he
  simp only [Frontend.denoteEList] at hes
  cases hea : denoteE st a with
  | none => rw [hea] at hes; simp at hes
  | some ea =>
    cases has : Frontend.denoteEList st as with
    | none => rw [hea, has] at hes; simp at hes
    | some eas =>
      rw [hea, has] at hes
      obtain rfl := Option.some.inj hes
      rw [denoteEP, hf e eacc ea eas he]

/-! ## 3. The pure functions' clauses

The three `Option.map` clauses of each `…Go`, and the fallthrough. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1181-1190 instPisAtFGo — the
`some` clause, with the accumulator's REVERSAL discharged. -/
theorem instPisAtFGo_cons {x y ea : Expr} {ws ys ds : List Expr} {res : Expr}
    {m : BinderMeta}
    (hh : Expr.instPisAtFGo (ws ++ [ea]).reverse ys y = some (ds, res)) :
    Expr.instPisAtFGo ws.reverse (ea :: ys) (.forallE x y m) =
      some (x.instantiateList ws.reverse :: ds, res) := by
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append] at hh
  simp [Expr.instPisAtFGo, hh]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1181-1190 instPisAtFGo — the
`none` clause. -/
theorem instPisAtFGo_cons_none {y ea : Expr} {ws ys : List Expr}
    (hh : Expr.instPisAtFGo (ws ++ [ea]).reverse ys y = none) (x : Expr)
    (m : BinderMeta) :
    Expr.instPisAtFGo ws.reverse (ea :: ys) (.forallE x y m) = none := by
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append] at hh
  simp [Expr.instPisAtFGo, hh]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1198-1204 instLamsAtFGo — the
`some` clause. -/
theorem instLamsAtFGo_cons {x y ea : Expr} {ws ys ds : List Expr} {res : Expr}
    {m : BinderMeta}
    (hh : Expr.instLamsAtFGo (ws ++ [ea]).reverse ys y = some (ds, res)) :
    Expr.instLamsAtFGo ws.reverse (ea :: ys) (.lam x y m) =
      some (x.instantiateList ws.reverse :: ds, res) := by
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append] at hh
  simp [Expr.instLamsAtFGo, hh]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1198-1204 instLamsAtFGo — the
`none` clause. -/
theorem instLamsAtFGo_cons_none {y ea : Expr} {ws ys : List Expr}
    (hh : Expr.instLamsAtFGo (ws ++ [ea]).reverse ys y = none) (x : Expr)
    (m : BinderMeta) :
    Expr.instLamsAtFGo ws.reverse (ea :: ys) (.lam x y m) = none := by
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append] at hh
  simp [Expr.instLamsAtFGo, hh]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1181-1190 instPisAtFGo — the
fallthrough clause. -/
theorem instPisAtFGo_of_not_forallE {e x : Expr} {ws xs : List Expr}
    (h : ∀ ty b m, e ≠ Expr.forallE ty b m) :
    Expr.instPisAtFGo ws (x :: xs) e = none := by
  cases e with
  | forallE ty b m => exact absurd rfl (h ty b m)
  | _ => simp [Expr.instPisAtFGo]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1198-1204 instLamsAtFGo — the
fallthrough clause. -/
theorem instLamsAtFGo_of_not_lam {e x : Expr} {ws xs : List Expr}
    (h : ∀ ty b m, e ≠ Expr.lam ty b m) :
    Expr.instLamsAtFGo ws (x :: xs) e = none := by
  cases e with
  | lam ty b m => exact absurd rfl (h ty b m)
  | _ => simp [Expr.instLamsAtFGo]

/-! ## 4. Theorem 1 for the two `…Go`s -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1181-1190 instPisAtFGo —
**THEOREM 1** for `instPisAtFGo`.  The accumulator is a PUSH-ORDER `Array`
(task #97-P6-15), so con-leche's function is applied at `eacc.reverse`; the
induction is on the argument list. -/
theorem instPisAtFGo_spec {fuel : Nat} (hil : InstListSpec fuel) :
    ∀ (args : List EIdx) (s₀ : AState) (acc : Array EIdx) (h : EIdx),
    StateOK s₀ → (denoteE s₀.store h).isSome = true →
    (Frontend.denoteEList s₀.store acc.toList).isSome = true →
    (Frontend.denoteEList s₀.store args).isSome = true →
    ⦃fun s => ⌜s = s₀⌝⦄ instPisAtFGo fuel acc args h
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        RelEPAA (fun e eacc es => Expr.instPisAtFGo eacc.reverse es e)
          s₀.store h acc.toList args s'.store r⌝⦄ := by
  have hrun := hil.run
  intro args
  induction args with
  | nil =>
    intro s₀ acc h hok hden hacc hargs
    mvcgen [instPisAtFGo, hrun]
    all_goals try bridge_vcs
    all_goals
      (arm_pre
       first
       | assumption
       | (refine ⟨by first | arm_hyp | exact ⟨by arm_hyp⟩,
            by grind only [Ext.trans],
            by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
          exact RelEPAA.nil_step (by arm_hyp) (fun _ _ => rfl)))
  | cons a as ih =>
    intro s₀ acc h hok hden hacc hargs
    obtain ⟨ha1, ha2⟩ := denoteEList_cons_isSome hargs
    obtain ⟨ea, hea⟩ := Option.isSome_iff_exists.mp ha1
    obtain ⟨eacc0, hacc0⟩ := Option.isSome_iff_exists.mp hacc
    have hpushs : (Frontend.denoteEList s₀.store (acc.push a).toList).isSome
        = true := by
      rw [Array.toList_push, denoteEList_snoc hea acc.toList eacc0 hacc0]; rfl
    mvcgen [instPisAtFGo, ih, hrun]
    all_goals try bridge_vcs
    -- Ten verification conditions remain: seven `isSome`/`StateOK` side
    -- goals of the two calls (the closer leaves them only because it does
    -- not `intro` the arrows `mvcgen` puts in front) and the three answers.
    all_goals
      (arm_pre
       first
       | assumption
       | (refine ⟨by first | arm_hyp | exact ⟨by arm_hyp⟩,
            by grind only [Ext.trans],
            by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
          first
          | exact RelEPAA.forallE_step
              (Fr := fun e eacc es => Expr.instPisAtFGo eacc.reverse es e)
              hok.wf (by arm_hyp) hea (by arm_hyp) (by arm_hyp) (by arm_hyp)
              (by arm_hyp) (by simp)
              (fun _ _ _ _ _ _ hh => instPisAtFGo_cons hh)
          | exact RelEPAA.noneF_step
              (Fr := fun e eacc es => Expr.instPisAtFGo eacc.reverse es e)
              hok.wf (by arm_hyp) hea (by arm_hyp) (by simp)
              (fun _ _ _ hh x => instPisAtFGo_cons_none hh x _))
       | exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl,
           RelEPAA.none_of_view_cons hok.wf (by arm_hyp) (fun e ws x xs he =>
             instPisAtFGo_of_not_forallE
               (denoteEView_not_forallE he (by assumption)))⟩
       | exact (isSome_forallE hok.wf (by arm_hyp) (by arm_hyp)).1
       | exact (isSome_forallE hok.wf (by arm_hyp) (by arm_hyp)).2
       | exact denoteEList_isSome_ext (by arm_hyp) (by arm_hyp)
       | exact denote_isSome_ext
           ((isSome_forallE hok.wf (by arm_hyp) (by arm_hyp)).1) (by arm_hyp)
       | exact denote_isSome_ext (by arm_hyp) (by arm_hyp)
       | grind)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1198-1204 instLamsAtFGo —
**THEOREM 1** for `instLamsAtFGo`, the λ counterpart. -/
theorem instLamsAtFGo_spec {fuel : Nat} (hil : InstListSpec fuel) :
    ∀ (args : List EIdx) (s₀ : AState) (acc : Array EIdx) (h : EIdx),
    StateOK s₀ → (denoteE s₀.store h).isSome = true →
    (Frontend.denoteEList s₀.store acc.toList).isSome = true →
    (Frontend.denoteEList s₀.store args).isSome = true →
    ⦃fun s => ⌜s = s₀⌝⦄ instLamsAtFGo fuel acc args h
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        RelEPAA (fun e eacc es => Expr.instLamsAtFGo eacc.reverse es e)
          s₀.store h acc.toList args s'.store r⌝⦄ := by
  have hrun := hil.run
  intro args
  induction args with
  | nil =>
    intro s₀ acc h hok hden hacc hargs
    mvcgen [instLamsAtFGo, hrun]
    all_goals try bridge_vcs
    all_goals
      (arm_pre
       first
       | assumption
       | (refine ⟨by first | arm_hyp | exact ⟨by arm_hyp⟩,
            by grind only [Ext.trans],
            by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
          exact RelEPAA.nil_step (by arm_hyp) (fun _ _ => rfl)))
  | cons a as ih =>
    intro s₀ acc h hok hden hacc hargs
    obtain ⟨ha1, ha2⟩ := denoteEList_cons_isSome hargs
    obtain ⟨ea, hea⟩ := Option.isSome_iff_exists.mp ha1
    obtain ⟨eacc0, hacc0⟩ := Option.isSome_iff_exists.mp hacc
    have hpushs : (Frontend.denoteEList s₀.store (acc.push a).toList).isSome
        = true := by
      rw [Array.toList_push, denoteEList_snoc hea acc.toList eacc0 hacc0]; rfl
    mvcgen [instLamsAtFGo, ih, hrun]
    all_goals try bridge_vcs
    all_goals
      (arm_pre
       first
       | assumption
       | (refine ⟨by first | arm_hyp | exact ⟨by arm_hyp⟩,
            by grind only [Ext.trans],
            by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
          first
          | exact RelEPAA.lam_step
              (Fr := fun e eacc es => Expr.instLamsAtFGo eacc.reverse es e)
              hok.wf (by arm_hyp) hea (by arm_hyp) (by arm_hyp) (by arm_hyp)
              (by arm_hyp) (by simp)
              (fun _ _ _ _ _ _ hh => instLamsAtFGo_cons hh)
          | exact RelEPAA.noneL_step
              (Fr := fun e eacc es => Expr.instLamsAtFGo eacc.reverse es e)
              hok.wf (by arm_hyp) hea (by arm_hyp) (by simp)
              (fun _ _ _ hh x => instLamsAtFGo_cons_none hh x _))
       | exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl,
           RelEPAA.none_of_view_cons hok.wf (by arm_hyp) (fun e ws x xs he =>
             instLamsAtFGo_of_not_lam
               (denoteEView_not_lam he (by assumption)))⟩
       | exact (isSome_lam hok.wf (by arm_hyp) (by arm_hyp)).1
       | exact (isSome_lam hok.wf (by arm_hyp) (by arm_hyp)).2
       | exact denoteEList_isSome_ext (by arm_hyp) (by arm_hyp)
       | exact denote_isSome_ext
           ((isSome_lam hok.wf (by arm_hyp) (by arm_hyp)).1) (by arm_hyp)
       | exact denote_isSome_ext (by arm_hyp) (by arm_hyp)
       | grind)

/-! ## 5. The two wrappers

`instPisAtF` runs the one-pass walk and falls back to the sequential spec
when the RAW telescope is shorter than the argument list.  So its answer
relation is `RelEPA` at con-leche's `instPisAtF`, and the two branches are
the two arms of con-leche's own `match`. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1192-1196 instPisAtF — the `some`
branch's equation: the wrapper answers the `Go`'s answer. -/
theorem instPisAtF_of_some {e : Expr} {es ds : List Expr} {res : Expr}
    (h : Expr.instPisAtFGo [] es e = some (ds, res)) :
    Expr.instPisAtF es e = some (ds, res) := by
  rw [Expr.instPisAtF, h]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1192-1196 instPisAtF — the `none`
branch's equation: the wrapper answers the sequential spec. -/
theorem instPisAtF_of_none {e : Expr} {es : List Expr}
    (h : Expr.instPisAtFGo [] es e = none) :
    Expr.instPisAtF es e = Expr.instPisAt es e := by
  rw [Expr.instPisAtF, h]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1206-1210 instLamsAtF — the same
two. -/
theorem instLamsAtF_of_some {e : Expr} {es ds : List Expr} {res : Expr}
    (h : Expr.instLamsAtFGo [] es e = some (ds, res)) :
    Expr.instLamsAtF es e = some (ds, res) := by
  rw [Expr.instLamsAtF, h]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1206-1210 instLamsAtF — the
`none` branch's equation. -/
theorem instLamsAtF_of_none {e : Expr} {es : List Expr}
    (h : Expr.instLamsAtFGo [] es e = none) :
    Expr.instLamsAtF es e = Expr.instLamsAt es e := by
  rw [Expr.instLamsAtF, h]

/-- con-leche: none — the wrapper's `some` branch as a step lemma: the `Go`'s
`RelEPAA` at the EMPTY accumulator is the wrapper's `RelEPA`. -/
theorem RelEPA.of_go_some
    {F : Expr → List Expr → Option (List Expr × Expr)}
    {G : Expr → List Expr → List Expr → Option (List Expr × Expr)}
    {st st' : EStore} {h : EIdx} {as : List EIdx} {p : List EIdx × EIdx}
    (hg : RelEPAA G st h [] as st' (some p))
    (hdec : ∀ e es ds res, G e [] es = some (ds, res) → F e es = some (ds, res)) :
    RelEPA F st h as st' (some p) := by
  intro e es he hes
  obtain ⟨ds, res, hres, hdds, hdres⟩ :=
    denoteEP_some_inv (hg e [] es he rfl hes)
  rw [hdec e es ds res hres]
  simp only [denoteEP, hdds, hdres]

/-- con-leche: none — the wrapper's `none` branch: the `Go` failed, so the
wrapper's answer relation IS the sequential walk's. -/
theorem RelEPA.of_go_none
    {F Fs : Expr → List Expr → Option (List Expr × Expr)}
    {G : Expr → List Expr → List Expr → Option (List Expr × Expr)}
    {st s1 st' : EStore} {h : EIdx} {as : List EIdx}
    {r : Option (List EIdx × EIdx)}
    (hg : RelEPAA G st h [] as s1 none) (hx1 : Ext st s1)
    (hs : RelEPA Fs s1 h as st' r)
    (hdec : ∀ e es, G e [] es = none → F e es = Fs e es) :
    RelEPA F st h as st' r := by
  intro e es he hes
  have hh := hg e [] es he rfl hes
  simp only [denoteEP, Option.some.injEq] at hh
  rw [hdec e es hh.symm]
  exact hs e es (denote_ext he hx1) (denoteEList_ext hx1 as es hes)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1192-1196 instPisAtF —
**THEOREM 1** for `instPisAtF`: the one-pass `instPisAt`, with the
sequential spec as its unconditional fallback. -/
theorem instPisAtF_spec {fuel : Nat} (hil : InstListSpec fuel)
    (s₀ : AState) (args : List EIdx) (h : EIdx) (hok : StateOK s₀)
    (hden : (denoteE s₀.store h).isSome = true)
    (hargs : (Frontend.denoteEList s₀.store args).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ instPisAtF fuel args h
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        RelEPA (fun e es => Expr.instPisAtF es e) s₀.store h args
          s'.store r⌝⦄ := by
  have hgo := instPisAtFGo_spec hil args
  have hseq := instPisAt_spec fuel args
  mvcgen [instPisAtF, hgo, hseq]
  all_goals try bridge_vcs
  -- Eight verification conditions: the three side goals of each call and the
  -- two answers (the `Go` succeeded; the `Go` failed and the SEQUENTIAL walk
  -- answered), which are con-leche's own two `match` arms.
  all_goals
    (arm_pre
     first
     | assumption
     | exact denote_isSome_ext (by arm_hyp) (by arm_hyp)
     | exact denoteEList_isSome_ext (by arm_hyp) (by arm_hyp)
     | (refine ⟨by first | arm_hyp | exact ⟨by arm_hyp⟩,
          by grind only [Ext.trans],
          by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
        first
        | exact RelEPA.of_go_some (by arm_hyp)
            (fun _ _ _ _ hh => instPisAtF_of_some hh)
        | exact RelEPA.of_go_none (by arm_hyp) (by arm_hyp) (by arm_hyp)
            (fun _ _ hh => instPisAtF_of_none hh))
     | grind)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1206-1210 instLamsAtF —
**THEOREM 1** for `instLamsAtF`. -/
theorem instLamsAtF_spec {fuel : Nat} (hil : InstListSpec fuel)
    (s₀ : AState) (args : List EIdx) (h : EIdx) (hok : StateOK s₀)
    (hden : (denoteE s₀.store h).isSome = true)
    (hargs : (Frontend.denoteEList s₀.store args).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLamsAtF fuel args h
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        RelEPA (fun e es => Expr.instLamsAtF es e) s₀.store h args
          s'.store r⌝⦄ := by
  have hgo := instLamsAtFGo_spec hil args
  have hseq := instLamsAt_spec fuel args
  mvcgen [instLamsAtF, hgo, hseq]
  all_goals try bridge_vcs
  all_goals
    (arm_pre
     first
     | assumption
     | exact denote_isSome_ext (by arm_hyp) (by arm_hyp)
     | exact denoteEList_isSome_ext (by arm_hyp) (by arm_hyp)
     | (refine ⟨by first | arm_hyp | exact ⟨by arm_hyp⟩,
          by grind only [Ext.trans],
          by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
        first
        | exact RelEPA.of_go_some (by arm_hyp)
            (fun _ _ _ _ hh => instLamsAtF_of_some hh)
        | exact RelEPA.of_go_none (by arm_hyp) (by arm_hyp) (by arm_hyp)
            (fun _ _ hh => instLamsAtF_of_none hh))
     | grind)

/-! ## 6. `recRulePlain`

The one twin of this group whose answer is a `Bool` computed by an equality
test on HANDLES where con-leche tests `Expr`s.  Its doc comment says why that
is the same test — "exactness makes it the structural comparison con-leche
writes" — and the licence is `WFProofs.lean`'s `denoteE_inj`.  The three
lemmas below turn that into a statement about LISTS, and they belong in
`Bridge/Rel.lean` (group 2, beside `denoteEList_ext`). -/

/-- con-leche: none — a denoting handle list's PREFIX denotes the
denotation's prefix.  `recRulePlain` compares `args.take cnP`.  Named
`…_takePrefix` and not `denoteEList_take` because the `Subst` group's
`SubstLemmas.lean` declares the same fact under the latter name with its
arguments in the other order; one of the two goes when `Bridge/Rel.lean`
adopts it. -/
theorem denoteEList_takePrefix {st : EStore} :
    ∀ (l : List EIdx) (x : List Expr) (n : Nat),
      Frontend.denoteEList st l = some x →
        Frontend.denoteEList st (l.take n) = some (x.take n) := by
  intro l
  induction l with
  | nil =>
    intro x n h
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h
    simp [Frontend.denoteEList]
  | cons j js ih =>
    intro x n h
    simp only [Frontend.denoteEList] at h
    cases hj : denoteE st j with
    | none => rw [hj] at h; simp at h
    | some y =>
      cases hjs : Frontend.denoteEList st js with
      | none => rw [hj, hjs] at h; simp at h
      | some ys =>
        rw [hj, hjs] at h
        simp only [Option.some.injEq] at h
        subst h
        cases n with
        | zero => simp [Frontend.denoteEList]
        | succ k =>
          simp only [List.take_succ_cons, Frontend.denoteEList, hj,
            ih ys k hjs]

/-- con-leche: none — **exactness at a LIST**: two handle lists that denote
the same expression list are equal.  `WFProofs.lean`'s `denoteE_inj`, lifted;
this is what makes `recRulePlain`'s index comparison con-leche's structural
one. -/
theorem denoteEList_inj {st : EStore} (hwf : StoreWF st) :
    ∀ (l1 l2 : List EIdx) (x : List Expr),
      Frontend.denoteEList st l1 = some x →
        Frontend.denoteEList st l2 = some x → l1 = l2 := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 x h1 h2
    simp only [Frontend.denoteEList, Option.some.injEq] at h1
    subst h1
    cases l2 with
    | nil => rfl
    | cons k ks =>
      simp only [Frontend.denoteEList] at h2
      cases hk : denoteE st k with
      | none => rw [hk] at h2; simp at h2
      | some y =>
        cases hks : Frontend.denoteEList st ks with
        | none => rw [hk, hks] at h2; simp at h2
        | some ys => rw [hk, hks] at h2; simp at h2
  | cons j js ih =>
    intro l2 x h1 h2
    simp only [Frontend.denoteEList] at h1
    cases hj : denoteE st j with
    | none => rw [hj] at h1; simp at h1
    | some y =>
      cases hjs : Frontend.denoteEList st js with
      | none => rw [hj, hjs] at h1; simp at h1
      | some ys =>
        rw [hj, hjs] at h1
        simp only [Option.some.injEq] at h1
        subst h1
        cases l2 with
        | nil => simp [Frontend.denoteEList] at h2
        | cons k ks =>
          simp only [Frontend.denoteEList] at h2
          cases hk : denoteE st k with
          | none => rw [hk] at h2; simp at h2
          | some z =>
            cases hks : Frontend.denoteEList st ks with
            | none => rw [hk, hks] at h2; simp at h2
            | some zs =>
              rw [hk, hks] at h2
              simp only [Option.some.injEq, List.cons.injEq] at h2
              obtain ⟨rfl, rfl⟩ := h2
              rw [denoteE_inj hwf hj hk, ih ks zs hjs hks]

/-- con-leche: none — and therefore the two `==` agree: the twin's index
comparison IS con-leche's structural one. -/
theorem denoteEList_beq {st : EStore} (hwf : StoreWF st) {l1 l2 : List EIdx}
    {x1 x2 : List Expr} (h1 : Frontend.denoteEList st l1 = some x1)
    (h2 : Frontend.denoteEList st l2 = some x2) : (l1 == l2) = (x1 == x2) := by
  by_cases he : l1 = l2
  · subst he
    rw [h1] at h2
    obtain rfl := Option.some.inj h2
    simp
  · have hne : x1 ≠ x2 := by
      intro hx
      subst hx
      exact he (denoteEList_inj hwf l1 l2 x1 h1 h2)
    rw [show (l1 == l2) = false from by simp only [beq_eq_false_iff_ne]; exact he,
      show (x1 == x2) = false from by simp only [beq_eq_false_iff_ne]; exact hne]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1229-1244 recRulePlain — the
comparand list at cursor `0`, which is what `recRulePlain` cites. -/
theorem bvarRangeSpec_zero (mI n : Nat) :
    bvarRangeSpec mI n 0 =
      (List.range n).map (fun j => Expr.bvar (mI - 1 - j)) := by
  rw [bvarRangeSpec_eq_range]
  simp

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1229-1244 recRulePlain — the
arity gate's `false` clause. -/
theorem recRulePlain_of_not_le {e : Expr} {mI rP cnP : Nat}
    (h : (decide (cnP ≤ rP) && decide (rP ≤ mI)) = false) :
    Expr.recRulePlain e mI rP cnP = false := by
  simp [Expr.recRulePlain, h]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1229-1244 recRulePlain — the
`stripPis` failure's `false` clause. -/
theorem recRulePlain_of_strip_none {e : Expr} {mI rP cnP : Nat}
    (h : Expr.stripPis mI e = none) : Expr.recRulePlain e mI rP cnP = false := by
  simp [Expr.recRulePlain, h]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1229-1244 recRulePlain — the
residual-is-not-a-`∀` `false` clause. -/
theorem recRulePlain_of_body_not_forallE {e e2 : Expr}
    {bs : List (Expr × BinderMeta)} {mI rP cnP : Nat}
    (h : Expr.stripPis mI e = some (bs, e2))
    (h2 : ∀ ty b m, e2 ≠ Expr.forallE ty b m) :
    Expr.recRulePlain e mI rP cnP = false := by
  cases e2 with
  | forallE ty b m => exact absurd rfl (h2 ty b m)
  | _ => simp [Expr.recRulePlain, h]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1229-1244 recRulePlain — the
CANONICAL clause: the arity gate passes and the telescope strips to a `∀`. -/
theorem recRulePlain_eq_beq {e edom ebody : Expr}
    {bs : List (Expr × BinderMeta)} {m : BinderMeta} {mI rP cnP : Nat}
    (hle : (decide (cnP ≤ rP) && decide (rP ≤ mI)) = true)
    (hsp : Expr.stripPis mI e = some (bs, .forallE edom ebody m)) :
    Expr.recRulePlain e mI rP cnP =
      (edom.getAppArgs.take cnP ==
        (List.range cnP).map (fun k => Expr.bvar (mI - 1 - k))) := by
  simp [Expr.recRulePlain, hsp, hle]


/-! ### `recRulePlain`'s four arms, as four lemmas

`mvcgen` leaves five verification conditions — the arity gate, the
`stripPis` failure, the residual-is-not-a-`∀` fallthrough, the canonical
comparison, and the `getAppArgs` call's `isSome` side goal.  Each is one
lemma, so the arm proofs are one `exact` and never name a hypothesis
`mvcgen` made inaccessible. -/

/-- con-leche: none — what `RelBP`'s `some` answer says about the residual
handle: it denotes.  Belongs in `Bridge/Rel.lean` group 7. -/
theorem RelBP.snd_isSome {F : Expr → Option (List (Expr × BinderMeta) × Expr)}
    {st st' : EStore} {c : EIdx} {p : List (EIdx × BinderMeta) × EIdx}
    {e : Expr} (h : RelBP F st c st' (some p)) (he : denoteE st c = some e) :
    (denoteE st' p.2).isSome = true := by
  obtain ⟨xs, x, _, _, hx⟩ := denoteBP_some_inv (h e he)
  rw [hx]; rfl

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1229-1244 recRulePlain — the
arity gate's arm. -/
theorem recRulePlain_notLe {st : EStore} {recTy : EIdx} {mI rP cnP : Nat}
    (h : (decide (cnP ≤ rP) && decide (rP ≤ mI)) = false) :
    RelV (fun x => Expr.recRulePlain x mI rP cnP) st recTy false :=
  fun _ _ => (recRulePlain_of_not_le h).symm

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1229-1244 recRulePlain — the
`stripPis`-failed arm. -/
theorem recRulePlain_stripNone {st : EStore} {recTy : EIdx} {erecTy : Expr}
    (hrecTy : denoteE st recTy = some erecTy) {mI rP cnP : Nat}
    (hstrip : RelBP (Expr.stripPis mI) st recTy st none) :
    RelV (fun x => Expr.recRulePlain x mI rP cnP) st recTy false := by
  intro e he
  rw [hrecTy] at he
  obtain rfl := Option.some.inj he
  have hh := hstrip erecTy hrecTy
  simp only [denoteBP, Option.some.injEq] at hh
  exact (recRulePlain_of_strip_none hh.symm).symm

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1229-1244 recRulePlain — the
residual-is-not-a-`∀` arm. -/
theorem recRulePlain_notPi {st : EStore} (hwf : StoreWF st) {recTy : EIdx}
    {erecTy : Expr} (hrecTy : denoteE st recTy = some erecTy)
    {p : List (EIdx × BinderMeta) × EIdx} {v : ENodeView} {mI rP cnP : Nat}
    (hstrip : RelBP (Expr.stripPis mI) st recTy st (some p))
    (hview : st.view p.2 = some v) (hv : ∀ ty b m, v ≠ .forallE ty b m) :
    RelV (fun x => Expr.recRulePlain x mI rP cnP) st recTy false := by
  intro e he
  rw [hrecTy] at he
  obtain rfl := Option.some.inj he
  obtain ⟨bs, e2, hsp, _, he2⟩ := denoteBP_some_inv (hstrip erecTy hrecTy)
  refine (recRulePlain_of_body_not_forallE hsp ?_).symm
  exact denoteEView_not_forallE
    (by rw [← denoteE_view_eq hwf hview]; exact he2) hv

/-- con-leche: none — a denoted handle list is as long as its denotation. -/
theorem denoteEList_length_tf {st : EStore} :
    ∀ (l : List EIdx) (es : List Expr),
      Frontend.denoteEList st l = some es → es.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro es h
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    simp [← h]
  | cons a as ih =>
    intro es h
    simp only [Frontend.denoteEList] at h
    cases ha : denoteE st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteEList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        simp only [Option.some.injEq] at h
        rw [← h]
        simp [ih ys has]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1229-1244 recRulePlain — **the
canonical arm**, where the two halves con-leche does not have come in:
`bvarRangeSpec_zero` (the interned comparand list IS con-leche's `List.range`
literal) and `denoteEList_beq` (the twin's INDEX comparison is con-leche's
structural one, by `denoteE_inj`). -/
theorem recRulePlain_canonical {st : EStore} (hwf : StoreWF st)
    {recTy : EIdx} {erecTy : Expr} (hrecTy : denoteE st recTy = some erecTy)
    {p : List (EIdx × BinderMeta) × EIdx} {dom body : EIdx} {m : BinderMeta}
    {args want : List EIdx} {mI rP cnP : Nat} {sA : AState}
    (hstrip : RelBP (Expr.stripPis mI) st recTy st (some p))
    (hview : st.view p.2 = some (.forallE dom body m))
    (hargs : RelEL Expr.getAppArgs st dom st args)
    (hwant : Frontend.denoteEList sA.store want = some (bvarRangeSpec mI cnP 0))
    (hx : Ext st sA.store) (hok1 : StateOK sA)
    (hle : (decide (cnP ≤ rP) && decide (rP ≤ mI)) = true) :
    RelV (fun x => Expr.recRulePlain x mI rP cnP) st recTy
      (args.take want.length == want) := by
  -- the twin takes the prefix as long as the comparand, as the port does
  -- (task #97-T2-LOCKSTEP); the comparand is `cnP` long
  have hlen : want.length = cnP := by
    have := denoteEList_length_tf _ _ hwant
    rw [bvarRangeSpec_eq_range] at this
    simpa using this.symm
  rw [hlen]
  intro e he
  rw [hrecTy] at he
  obtain rfl := Option.some.inj he
  obtain ⟨bs, e2, hsp, _, he2⟩ := denoteBP_some_inv (hstrip erecTy hrecTy)
  obtain ⟨edom, ebody, rfl, hdt, _⟩ := denote_forallE_inv hwf hview he2
  show (args.take cnP == want) = Expr.recRulePlain erecTy mI rP cnP
  rw [recRulePlain_eq_beq hle hsp, ← bvarRangeSpec_zero]
  exact denoteEList_beq hok1.wf
    (denoteEList_takePrefix args edom.getAppArgs cnP
      (denoteEList_ext hx args edom.getAppArgs (hargs edom hdt))) hwant

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1229-1244 recRulePlain —
**THEOREM 1** for `recRulePlain`: a recursor rule is canonical when its
constructor's parameters are exactly the recursor's own leading arguments.
The answer is a `Bool` — representation-free — so the relation is `RelV`,
which names no target store even though `bvarRange` interns. -/
theorem recRulePlain_spec (fuel : Nat) (s₀ : AState) (recTy : EIdx)
    (mI rP cnP : Nat) (hok : StateOK s₀)
    (hden : (denoteE s₀.store recTy).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ recRulePlain fuel recTy mI rP cnP
    ⦃⇓? b s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧ s'.memos = s₀.memos ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        RelV (fun x => Expr.recRulePlain x mI rP cnP) s₀.store recTy b⌝⦄ := by
  have hstrip := stripPis_spec mI
  have hargs := getAppArgs_spec fuel
  have hrange := bvarRange_spec cnP
  obtain ⟨erecTy, hrecTy⟩ := Option.isSome_iff_exists.mp hden
  mvcgen [recRulePlain, hstrip, hargs, hrange]
  all_goals try bridge_vcs
  all_goals
    (arm_pre
     first
     | assumption
     | exact (isSome_forallE hok.wf (by arm_hyp)
         (RelBP.snd_isSome (by arm_hyp) hrecTy)).1
     | exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl, recRulePlain_notLe (by grind)⟩
     | exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
         recRulePlain_stripNone hrecTy (by arm_hyp)⟩
     | exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
         recRulePlain_notPi hok.wf hrecTy (by arm_hyp) (by arm_hyp)
           (by assumption)⟩
     | (refine ⟨by arm_hyp, by arm_hyp,
          by grind only [BMExt.trans, BMExt.refl],
          by arm_hyp, by arm_hyp, by arm_hyp,
          ?_⟩
        exact recRulePlain_canonical hok.wf hrecTy (by arm_hyp) (by arm_hyp)
          (by arm_hyp) (by arm_hyp) (by arm_hyp) (by arm_hyp) (by grind))
     -- the tag-first `else` arm (task #97-P5-Core round 4): the residual's
     -- view is recovered from its denotation
     | (obtain ⟨v, hv⟩ := view_of_denote_isSome (RelBP.snd_isSome (by arm_hyp) hrecTy)
        exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
          recRulePlain_notPi hok.wf hrecTy (by arm_hyp) hv
            (fun ty b m hh => view_tagOf_ne hv (t := ETag.forallE) (by arm_hyp)
              (by rw [hh]; rfl))⟩)
     | grind)

/-! ## The axiom check -/

#print axioms instPisAtFGo_spec
#print axioms instLamsAtFGo_spec
#print axioms instPisAtF_spec
#print axioms instLamsAtF_spec
#print axioms recRulePlain_spec
#print axioms denoteEList_inj
#print axioms denoteEList_beq
#print axioms denoteEList_takePrefix
#print axioms bvarRangeSpec_zero

end ConRon.Bridge.ExprOps

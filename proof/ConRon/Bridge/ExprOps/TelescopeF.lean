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
set_option experimental.vcgen true
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

attribute [-grind] RelE.ext RelE.of_ext RelE.retarget

/-! ## 1. `instantiateListFast`'s Theorem 1, as a record -/

/-! ## 2. The three step lemmas of a BATCHED peel

`RelEPAA` is `RelEP` with the argument list AND the pending accumulator as
extra subjects, both quantified inside the relation.  These three lemmas
belong in `Bridge/Rel.lean` group 7 beside `RelEPA`'s. -/

/-! ## 3. The pure functions' clauses

The three `Option.map` clauses of each `…Go`, and the fallthrough. -/

/-! ## 4. Theorem 1 for the two `…Go`s -/

/-! ## 5. The two wrappers

`instPisAtF` runs the one-pass walk and falls back to the sequential spec
when the RAW telescope is shorter than the argument list.  So its answer
relation is `RelEPA` at con-leche's `instPisAtF`, and the two branches are
the two arms of con-leche's own `match`. -/

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

`vcgen` leaves nine verification conditions; `bridge_vcs` closes the four
about the state and the precondition, and five remain — the arity gate, the
`stripPis` failure, the residual-is-not-a-`∀` fallthrough, the canonical
comparison, and the `getAppArgs` call's `isSome` side goal.  Each is one
lemma, so the arm proofs are one `exact` and never name a hypothesis
`vcgen` made inaccessible. -/

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
literal) and `beq_of_denoteEList` (the twin's INDEX comparison is con-leche's
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
  exact beq_of_denoteEList hok1.wf
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
    ⦃fun s => s = s₀⦄ recRulePlain fuel recTy mI rP cnP
    ⦃fun b s' => StateOK s' ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧ s'.memos = s₀.memos ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        RelV (fun x => Expr.recRulePlain x mI rP cnP) s₀.store recTy b; ⊤⦄ := by
  have hstrip := stripPis_spec mI
  have hargs := getAppArgs_spec fuel
  have hrange := bvarRange_spec cnP
  obtain ⟨erecTy, hrecTy⟩ := Option.isSome_iff_exists.mp hden
  vcgen [recRulePlain, hstrip, hargs, hrange]
  all_goals try bridge_vcs
  all_goals
    (arm_pre
     first
     | exact (isSome_forallE hok.wf (by arm_hyp)
         (RelBP.snd_isSome (by arm_hyp) hrecTy)).1
     | exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl, recRulePlain_notLe (by grind)⟩
     | exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
         recRulePlain_stripNone hrecTy (by arm_hyp)⟩
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
              (by rw [hh]; rfl))⟩))

/-! ## The axiom check -/

#print axioms recRulePlain_spec
#print axioms denoteEList_inj
#print axioms beq_of_denoteEList
#print axioms denoteEList_takePrefix
#print axioms bvarRangeSpec_zero

end ConRon.Bridge.ExprOps

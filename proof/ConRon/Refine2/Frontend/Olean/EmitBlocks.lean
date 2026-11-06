/-
# `ConRon.Refine2.Frontend.Olean.EmitBlocks` — `olean/emit.rs`'s check of the blocks, against the twin's

**Task #142, Theorem 2.**  The check reads the merge and writes nothing: `PR`.  Every failure
is `.internal`, on both sides, whether or not the name in the twin's message reads back
(the twin's `readName` fails at `.internal` too): `FailsInt`.  Messages are never compared.
-/
import ConRon.Refine2.Frontend.Olean.EmitWalk

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.emit (block_bad block_member_ok block_ctor_ok block_members_ok block_members_ok_loop
  block_ctors_ok block_ctors_ok_loop block_step_induct block_step_ctor block_step_recur quot_all_quot
  quot_all_quot_loop quot_named block_step blocks_ok blocks_ok_loop)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Arena.Frontend.Olean (entriesOf quotNames quotConstants blockMemberOk blockCtorOk blockStep blocksOk)

/-! ## The shape -/

/-- A twin action that fails, from any state, at `.internal`. -/
def FailsInt {β : Type} (x : AM β) : Prop :=
  ∀ s, ∃ le, x.run s = .error le ∧ lAErrKind le = some .internal

theorem FailsInt.fail {β : Type} (m : String) : FailsInt (Arena.fail (.internal m) : AM β) :=
  fun _ => ⟨_, rfl, rfl⟩

/-- A name read in the message: its own failure is `.internal` too. -/
theorem FailsInt.read_bind {β : Type} (n : NIdx) {k : ConLeche.Name → AM β}
    (h : ∀ a, FailsInt (k a)) : FailsInt (Arena.readName n >>= k) := by
  intro s
  cases hd : denoteN s.store.ns n with
  | none =>
    refine ⟨.internal "arena: dangling name handle", ?_, rfl⟩
    rw [StateT.run_bind, readName_run_none hd]
    rfl
  | some x =>
    rw [am_bind_ok (readName_run_some hd)]
    exact h x s

theorem PR.pure_step {α β γ : Type} {R : α → β → Prop} {f : Result γ}
    {k : γ → Result (core.result.Result α kernel.core_types.CheckError)} {x : AM β}
    (h : ∀ a, f = ok a → PR R (k a) x) : PR R (Std.bind f k) x := by
  intro o hm
  obtain ⟨a, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact h a h1 o h2

theorem PR.pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} (hR : R a b) :
    PR R (ok (.Ok a)) (Pure.pure b) := by
  intro o h s
  cases Result.ok_injective h
  exact ⟨b, rfl, hR⟩

theorem block_bad_internal {pers : arena.store.PersTier} {ar : arena.store.EStore}
    {n : arena.handle.NIdx} {what : alloc.vec.Vec Std.U32} {ce}
    (h : block_bad pers ar n what = ok ce) : ∃ t, ce = .Internal t := by
  rw [block_bad] at h
  peel h as s, -
  peel h as v, -
  peel h as v1, -
  peel h as t, -
  peel h as s1, -
  peel h as v2, -
  peel h as t1, -
  peel h as v3, h3
  rw [kernel.core_types.internal] at h
  exact ⟨_, (Result.ok_injective h).symm⟩

/-- A failure: `block_bad`, against a twin action that fails. -/
theorem PR.bad {α β : Type} {R : α → β → Prop} {pers : arena.store.PersTier}
    {ar : arena.store.EStore} {n : arena.handle.NIdx} {what : alloc.vec.Vec Std.U32} {x : AM β}
    (hx : FailsInt x) :
    PR R (Std.bind (block_bad pers ar n what)
      (fun ce => ok (core.result.Result.Err ce) : kernel.core_types.CheckError → Result (core.result.Result α kernel.core_types.CheckError))) x := by
  intro o h s
  peel h as ce, hce
  obtain ⟨t, rfl⟩ := block_bad_internal hce
  cases Result.ok_injective h
  intro k hk
  cases hk
  exact hx s

/-- A twin failure with names read in its message. -/
macro "fails_int" : tactic =>
  `(tactic| repeat (first
      | exact FailsInt.fail _
      | refine FailsInt.read_bind _ fun _ => ?_))

/-- The Rust's message and its `block_bad`, against the twin's failure. -/
macro "bad_arm" : tactic =>
  `(tactic| repeat (first
      | exact PR.bad (by fails_int)
      | refine PR.pure_step fun _ _ => ?_))

/-! ## A block member, a constructor -/

/-- The test of a member's `skipped` against the type's. -/
theorem skip_arm {m : frontend.olean.closure.CEntry} {m' : Arena.Frontend.Olean.CEntry} (hc : CEntryRel m m')
    {sk : Bool} {x : AM Unit}
    {k : Result (core.result.Result Unit kernel.core_types.CheckError)}
    (hk : PR (fun _ _ => True) k x) :
    PR (fun _ _ => True) (do
        let b1 ← frontend.olean.closure.c_entry_skipped m
        if b1 = sk then ok (core.result.Result.Ok ()) else k)
      (if (m'.skipped == sk) = true then Pure.pure () else x) := by
  refine PR.pure_step fun b1 hb1 => ?_
  rw [c_entry_skipped_eq hc hb1]
  by_cases he : m'.skipped = sk
  · rw [ite_eq_left he, ite_eq_left (by simp [he])]
    exact PR.pure trivial
  · rw [ite_eq_right he, ite_eq_right (by simpa using he)]
    exact hk

theorem block_member_ok_pr {pers : arena.store.PersTier} {ar : arena.store.EStore}
    {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg')
    (n x : arena.handle.NIdx) (all : alloc.vec.Vec arena.handle.NIdx) (sk : Bool) :
    PR (fun _ _ => True) (block_member_ok pers ar mg n all sk x)
      (blockMemberOk mg' (absNIdx n) (all.val.map absNIdx) sk (absNIdx x)) := by
  rw [block_member_ok, blockMemberOk]
  refine PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.pure_step fun _ _ =>
    PR.pure_step fun _ _ => PR.pure_step fun o1 h1 => ?_
  have hg := mg_get_rel hm h1
  cases hg' : mg'.get (absNIdx x) with
  | none =>
    rw [hg'] at hg
    cases hg
    bad_arm
  | some m' =>
    rw [hg'] at hg
    cases hg with
    | some hc =>
      have hk := hc.1.kind
      dsimp only
      generalize frontend.olean.spec.CEntryF.kind _ = k at hk ⊢
      generalize m'.c.kind = k' at hk ⊢
      cases k <;> cases k' <;> try exact (hk : False).elim
      case Induct.induct np ni all2 cs nn ir iu irf np' ni' all2' cs' nn' ir' iu' irf' =>
        obtain ⟨-, -, hall, -⟩ := hk
        have hall' : all2.val.map absNIdx = all2' := hall
        subst hall'
        refine PR.pure_step fun b hb => ?_
        have e := nidx_list_eq_abs hb
        dsimp only
        rw [← e]
        cases b with
        | false =>
          rw [ite_eq_right (by simp), ite_eq_right (by simp)]
          bad_arm
        | true =>
          rw [ite_eq_left rfl, ite_eq_left rfl]
          exact skip_arm hc (by bad_arm)
      all_goals bad_arm

theorem block_ctor_ok_pr {pers : arena.store.PersTier} {ar : arena.store.EStore}
    {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg')
    (n x : arena.handle.NIdx) (sk : Bool) :
    PR (fun _ _ => True) (block_ctor_ok pers ar mg n sk x)
      (blockCtorOk mg' (absNIdx n) sk (absNIdx x)) := by
  rw [block_ctor_ok, blockCtorOk]
  refine PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.pure_step fun _ _ =>
    PR.pure_step fun _ _ => PR.pure_step fun o1 h1 => ?_
  have hg := mg_get_rel hm h1
  cases hg' : mg'.get (absNIdx x) with
  | none =>
    rw [hg'] at hg
    cases hg
    bad_arm
  | some m' =>
    rw [hg'] at hg
    cases hg with
    | some hc =>
      have hk := hc.1.kind
      dsimp only
      generalize frontend.olean.spec.CEntryF.kind _ = k at hk ⊢
      generalize m'.c.kind = k' at hk ⊢
      cases k <;> cases k' <;> try exact (hk : False).elim
      case Ctor.ctor ind ci np nf iu ind' ci' np' nf' iu' =>
        obtain ⟨rfl, -⟩ := hk
        refine PR.pure_step fun b hb => ?_
        have e := nidx_eq2_abs hb
        dsimp only
        rw [← e]
        cases b with
        | false =>
          rw [ite_eq_right (by simp), ite_eq_right (by simp)]
          bad_arm
        | true =>
          rw [ite_eq_left rfl, ite_eq_left rfl]
          exact skip_arm hc (by bad_arm)
      all_goals bad_arm

/-! ## The loops over them -/

theorem forM_map {α β : Type} (g : α → β) (f : β → AM Unit) (l : List α) :
    (l.map g).forM f = l.forM (fun x => f (g x)) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp

theorem forM_cons' {α : Type} (a : α) (l : List α) (g : α → AM Unit) :
    (a :: l).forM g = g a >>= fun _ => l.forM g := rfl

/-- **A checking `Vec` loop, as `forM`.** -/
theorem up_loop_pr {A : Type} (v : alloc.vec.Vec A)
    {L : Std.Usize → Result (core.result.Result Unit kernel.core_types.CheckError)}
    {step : A → Result (core.result.Result Unit kernel.core_types.CheckError)}
    (hL : ∀ i, L i = if i < alloc.vec.Vec.len v then do
        let x ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice A) v i
        let r ← step x
        match r with
        | .Ok _ => do
          let i2 ← i + 1#usize
          L i2
        | .Err _ => ok r
      else ok (.Ok ()))
    {g : A → AM Unit} (hstep : ∀ x, PR (fun _ _ => True) (step x) (g x)) (i : Std.Usize) :
    PR (fun _ _ => True) (L i) ((v.val.drop i.val).forM g) := by
  have key : ∀ (k : Nat) (i : Std.Usize), v.val.length - i.val = k →
      PR (fun _ _ => True) (L i) ((v.val.drop i.val).forM g) := by
    intro k
    induction k with
    | zero =>
      intro i hk
      rw [hL, ite_eq_right (not_lt_len hk), drop_stop hk]
      exact PR.pure trivial
    | succ k ih =>
      intro i hk o h s
      rw [hL, ite_eq_left (lt_len hk)] at h
      peel h as x, hx
      peel h as r, hr
      rw [idx_cons hx, forM_cons']
      have h1 := hstep x r hr s
      cases r with
      | Ok u =>
        obtain ⟨b, hb, -⟩ := h1
        rw [am_bind_ok hb]
        peel h as i2, hi2
        have := ih i2 (by rw [usize_succ hi2]; omega) o h s
        rwa [usize_succ hi2] at this
      | Err e =>
        cases Result.ok_injective h
        show AErrSim e _
        rw [StateT.run_bind]
        exact AErrSim.bind h1 _
  exact key _ i rfl

theorem block_members_ok_pr {pers : arena.store.PersTier} {ar : arena.store.EStore}
    {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg')
    (n : arena.handle.NIdx) (all : alloc.vec.Vec arena.handle.NIdx) (sk : Bool) :
    PR (fun _ _ => True) (block_members_ok pers ar mg n all sk)
      ((all.val.map absNIdx).forM
        (blockMemberOk mg' (absNIdx n) (all.val.map absNIdx) sk)) := by
  rw [block_members_ok, forM_map]
  exact up_loop_pr (L := fun i => block_members_ok_loop pers ar mg n all sk i) all
    (step := fun x => block_member_ok pers ar mg n all sk x)
    (fun i => by rw [block_members_ok_loop]; rfl)
    (fun x => block_member_ok_pr hm n x all sk) 0#usize

theorem block_ctors_ok_pr {pers : arena.store.PersTier} {ar : arena.store.EStore}
    {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg')
    (n : arena.handle.NIdx) (cs : alloc.vec.Vec arena.handle.NIdx) (sk : Bool) :
    PR (fun _ _ => True) (block_ctors_ok pers ar mg n cs sk)
      ((cs.val.map absNIdx).forM (blockCtorOk mg' (absNIdx n) sk)) := by
  rw [block_ctors_ok, forM_map]
  exact up_loop_pr (L := fun i => block_ctors_ok_loop pers ar mg n cs sk i) cs
    (step := fun x => block_ctor_ok pers ar mg n sk x)
    (fun i => by rw [block_ctors_ok_loop]; rfl)
    (fun x => block_ctor_ok_pr hm n x sk) 0#usize

/-! ## The arms of `block_step` -/

theorem block_step_induct_pr {pers : arena.store.PersTier} {ar : arena.store.EStore}
    {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg')
    (n : arena.handle.NIdx) (all cs : alloc.vec.Vec arena.handle.NIdx) (sk : Bool) {x : AM Unit}
    (hx : FailsInt x) :
    PR (fun _ _ => True) (block_step_induct pers ar mg n all cs sk)
      (if (all.val.map absNIdx).contains (absNIdx n) then
        (all.val.map absNIdx).forM (blockMemberOk mg' (absNIdx n) (all.val.map absNIdx) sk) >>= fun _ =>
          (cs.val.map absNIdx).forM (blockCtorOk mg' (absNIdx n) sk)
       else x) := by
  rw [block_step_induct]
  refine PR.pure_step fun b hb => ?_
  rw [← nidx_contains_eq hb]
  cases b with
  | false =>
    rw [ite_eq_right (by simp), ite_eq_right (by simp)]
    refine PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.bad hx
  | true =>
    rw [ite_eq_left rfl, ite_eq_left rfl]
    intro o h s
    peel h as r, hr
    have h1 := block_members_ok_pr hm n all sk r hr s
    cases r with
    | Ok u =>
      obtain ⟨b, hb', -⟩ := h1
      rw [am_bind_ok hb']
      exact block_ctors_ok_pr hm n cs sk o h s
    | Err e =>
      cases Result.ok_injective h
      show AErrSim e _
      rw [StateT.run_bind]
      exact AErrSim.bind h1 _

theorem block_step_ctor_pr {pers : arena.store.PersTier} {ar : arena.store.EStore}
    {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg')
    (n ind : arena.handle.NIdx) {x1 x2 x3 : AM Unit} (h1 : FailsInt x1) (h2 : FailsInt x2)
    (h3 : FailsInt x3) :
    PR (fun _ _ => True) (block_step_ctor pers ar mg n ind)
      (match mg'.get (absNIdx ind) with
       | none => x1
       | some t =>
         match t.c.kind with
         | .induct _ _ _ cs .. => if cs.contains (absNIdx n) then Pure.pure () else x2
         | _ => x3) := by
  rw [block_step_ctor]
  refine PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.pure_step fun _ _ =>
    PR.pure_step fun _ _ => PR.pure_step fun o1 ho1 => ?_
  have hg := mg_get_rel hm ho1
  cases hg' : mg'.get (absNIdx ind) with
  | none =>
    rw [hg'] at hg
    cases hg
    refine PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.bad h1
  | some m' =>
    rw [hg'] at hg
    cases hg with
    | some hc =>
      have hk := hc.1.kind
      dsimp only
      generalize frontend.olean.spec.CEntryF.kind _ = k at hk ⊢
      generalize m'.c.kind = k' at hk ⊢
      cases k <;> cases k' <;> try exact (hk : False).elim
      case Induct.induct np ni all cs nn ir iu irf np' ni' all' cs' nn' ir' iu' irf' =>
        obtain ⟨-, -, -, hcs, -⟩ := hk
        have hcs' : cs.val.map absNIdx = cs' := hcs
        subst hcs'
        refine PR.pure_step fun b hb => ?_
        dsimp only
        rw [← nidx_contains_eq hb]
        cases b with
        | false =>
          rw [ite_eq_right (by simp), ite_eq_right (by simp)]
          refine PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.bad h2
        | true =>
          rw [ite_eq_left rfl, ite_eq_left rfl]
          exact PR.pure trivial
      all_goals refine PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.bad h3

theorem block_step_recur_pr {pers : arena.store.PersTier} {ar : arena.store.EStore}
    {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg')
    (n : arena.handle.NIdx) (all : alloc.vec.Vec arena.handle.NIdx) (sk : Bool) {x0 : AM Unit}
    {x1 x2 x3 x4 : NIdx → AM Unit} (h0 : FailsInt x0) (h1 : ∀ t, FailsInt (x1 t))
    (h2 : ∀ t, FailsInt (x2 t)) (h3 : ∀ t, FailsInt (x3 t)) (h4 : ∀ t, FailsInt (x4 t)) :
    PR (fun _ _ => True) (block_step_recur pers ar mg n all sk)
      (match all.val.map absNIdx with
       | [] => x0
       | t :: _ =>
         match mg'.get t with
         | none => x1 t
         | some m =>
           match m.c.kind with
           | .induct _ _ all' .. =>
             if all' == all.val.map absNIdx then
               if m.skipped == sk then Pure.pure () else x2 t
             else x3 t
           | _ => x4 t) := by
  rw [block_step_recur]
  cases hv : all.val with
  | nil =>
    rw [ite_eq_left (UScalar.eq_of_val_eq (by simp [alloc.vec.Vec.len, hv]))]
    refine PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.bad h0
  | cons a rest =>
    rw [ite_eq_right (fun hc => by
      have := congrArg UScalar.val hc
      simp [alloc.vec.Vec.len, hv] at this)]
    refine PR.pure_step fun t ht => ?_
    have hta := ConRon.Refine.ExprOps.vec_index_getElem? ht
    rw [hv] at hta
    cases (by simpa using hta : a = t)
    refine PR.pure_step fun _ _ => PR.pure_step fun o1 ho1 => ?_
    have hg := mg_get_rel hm ho1
    rw [List.map_cons]
    dsimp only
    cases hg' : mg'.get (absNIdx a) with
    | none =>
      rw [hg'] at hg
      cases hg
      refine PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.pure_step fun _ _ =>
        PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.bad (h1 _)
    | some m' =>
      rw [hg'] at hg
      cases hg with
      | some hc =>
        have hk := hc.1.kind
        dsimp only
        generalize frontend.olean.spec.CEntryF.kind _ = k at hk ⊢
        generalize m'.c.kind = k' at hk ⊢
        cases k <;> cases k' <;> try exact (hk : False).elim
        case Induct.induct np ni all2 cs nn ir iu irf np' ni' all2' cs' nn' ir' iu' irf' =>
          obtain ⟨-, -, hall, -⟩ := hk
          have hall' : all2.val.map absNIdx = all2' := hall
          subst hall'
          refine PR.pure_step fun b hb => ?_
          have e := nidx_list_eq_abs hb
          rw [hv, List.map_cons] at e
          dsimp only
          rw [← e]
          cases b with
          | false =>
            rw [ite_eq_right (by simp), ite_eq_right (by simp)]
            refine PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.pure_step fun _ _ =>
              PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.bad (h3 _)
          | true =>
            rw [ite_eq_left rfl, ite_eq_left rfl]
            refine skip_arm hc ?_
            refine PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.pure_step fun _ _ =>
              PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.bad (h2 _)
        all_goals
          refine PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.pure_step fun _ _ =>
            PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.bad (h4 _)

/-! ## The quotient package -/

theorem quot_named_eq {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {n : arena.handle.NIdx} {b : Bool} (h : quot_named mg n = ok b) :
    b = (entriesOf mg' [absNIdx n]).all (·.c.kind.tag == 4) := by
  rw [quot_named] at h
  peel h as o1, h1
  have hg := mg_get_rel hm h1
  simp only [entriesOf, List.filterMap_cons, List.filterMap_nil]
  cases hg' : mg'.get (absNIdx n) with
  | none =>
    rw [hg'] at hg
    cases hg
    exact (Result.ok_injective h).symm
  | some c' =>
    rw [hg'] at hg
    cases hg with
    | some hc =>
      peel h as t, ht
      cases Result.ok_injective h
      have hk := hc.1.kind
      simp only [List.all_cons, List.all_nil, Bool.and_true]
      rw [frontend.olean.reads.c_kind_tag.eq_def] at ht
      generalize frontend.olean.spec.CEntryF.kind _ = k at hk ht ⊢
      generalize c'.c.kind = k' at hk ⊢
      cases k <;> cases k' <;> try exact (hk : False).elim
      all_goals (cases Result.ok_injective ht; rfl)

theorem quot_all_quot_eq {pk : frontend.olean.spec.OleanPins} {mg : frontend.olean.merge.Merged}
    {mg' : Arena.Frontend.Olean.Merged} (hm : MergedRel mg mg') {b : Bool}
    (h : quot_all_quot pk mg = ok b) :
    b = (entriesOf mg' (quotConstants (absPins pk) mg')).all (·.c.kind.tag == 4) := by
  rw [quot_all_quot] at h
  peel h as qs, hqs
  rw [← quot_constants_rel hm hqs]
  have key : ∀ (k : Nat) (i : Std.Usize) (o : Bool), qs.val.length - i.val = k →
      quot_all_quot_loop mg qs i = ok o →
      o = (entriesOf mg' ((qs.val.drop i.val).map absNIdx)).all (·.c.kind.tag == 4) := by
    intro k
    induction k with
    | zero =>
      intro i o hk h
      rw [quot_all_quot_loop, ite_eq_right (not_lt_len hk)] at h
      cases Result.ok_injective h
      rw [drop_stop hk]
      rfl
    | succ k ih =>
      intro i o hk h
      rw [quot_all_quot_loop, ite_eq_left (lt_len hk)] at h
      peel h as n, hn
      peel h as b, hb
      have e := quot_named_eq hm hb
      have e2 : ∀ t, (entriesOf mg' (absNIdx n :: t)).all (·.c.kind.tag == 4) =
          ((entriesOf mg' [absNIdx n]).all (·.c.kind.tag == 4) &&
            (entriesOf mg' t).all (·.c.kind.tag == 4)) := by
        intro t
        simp only [entriesOf, List.filterMap_cons, List.filterMap_nil]
        cases mg'.get (absNIdx n) <;> simp
      rw [idx_cons hn, List.map_cons, e2, ← e]
      cases b with
      | true =>
        rw [ite_eq_left rfl] at h
        peel h as i2, hi2
        have := ih i2 o (by rw [usize_succ hi2]; omega) h
        rw [usize_succ hi2] at this
        simpa using this
      | false =>
        rw [ite_eq_right (by simp)] at h
        exact (Result.ok_injective h).symm
  simpa using key _ 0#usize b rfl h

/-- The test of the package's kinds. -/
theorem quot_ok_arm {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {ar : arena.store.EStore} {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {n : arena.handle.NIdx} {x : AM Unit} (hx : FailsInt x) :
    PR (fun _ _ => True) (do
        let b ← quot_all_quot pk mg
        if b = true then ok (core.result.Result.Ok ()) else do
          let s ← lift (Std.Array.to_slice frontend.olean.emit.block_step.M)
          let v ← kernel.core_types.code_points s
          let ce ← block_bad pers ar n v
          ok (core.result.Result.Err ce))
      (if (entriesOf mg' (quotConstants (absPins pk) mg')).all (·.c.kind.tag == 4) = true then
        Pure.pure () else x) := by
  refine PR.pure_step fun b hb => ?_
  rw [← quot_all_quot_eq hm hb]
  cases b with
  | true =>
    rw [ite_eq_left rfl, ite_eq_left rfl]
    exact PR.pure trivial
  | false =>
    rw [ite_eq_right (by simp), ite_eq_right (by simp)]
    exact PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.bad hx

theorem quot_names_contains (pk : frontend.olean.spec.OleanPins) (n : NIdx) :
    (quotNames (absPins pk)).contains n =
      ((n == absNIdx pk.n_quot) || (n == absNIdx pk.n_quot_mk) || (n == absNIdx pk.n_quot_lift) ||
        (n == absNIdx pk.n_quot_ind)) := by
  simp only [quotNames, absPins, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_assoc]

/-- The quotient arm of `block_step`. -/
theorem block_step_quot {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {ar : arena.store.EStore} {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') {n : arena.handle.NIdx} {x y : AM Unit} (hx : FailsInt x) (hy : FailsInt y) :
    PR (fun _ _ => True) (do
        let b ← arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 n pk.n_quot
        if b = true then do
          let b1 ← quot_all_quot pk mg
          if b1 = true then ok (core.result.Result.Ok ()) else do
            let s ← lift (Std.Array.to_slice frontend.olean.emit.block_step.M)
            let v ← kernel.core_types.code_points s
            let ce ← block_bad pers ar n v
            ok (core.result.Result.Err ce)
        else do
          let b1 ← arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 n pk.n_quot_mk
          if b1 = true then do
            let b2 ← quot_all_quot pk mg
            if b2 = true then ok (core.result.Result.Ok ()) else do
              let s ← lift (Std.Array.to_slice frontend.olean.emit.block_step.M)
              let v ← kernel.core_types.code_points s
              let ce ← block_bad pers ar n v
              ok (core.result.Result.Err ce)
          else do
            let b2 ← arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 n pk.n_quot_lift
            if b2 = true then do
              let b3 ← quot_all_quot pk mg
              if b3 = true then ok (core.result.Result.Ok ()) else do
                let s ← lift (Std.Array.to_slice frontend.olean.emit.block_step.M)
                let v ← kernel.core_types.code_points s
                let ce ← block_bad pers ar n v
                ok (core.result.Result.Err ce)
            else do
              let b3 ← arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 n pk.n_quot_ind
              if b3 = true then do
                let b4 ← quot_all_quot pk mg
                if b4 = true then ok (core.result.Result.Ok ()) else do
                  let s ← lift (Std.Array.to_slice frontend.olean.emit.block_step.M)
                  let v ← kernel.core_types.code_points s
                  let ce ← block_bad pers ar n v
                  ok (core.result.Result.Err ce)
              else do
                let s ← lift (Std.Array.to_slice frontend.olean.emit.block_step.M_1)
                let v ← kernel.core_types.code_points s
                let ce ← block_bad pers ar n v
                ok (core.result.Result.Err ce))
      (if (quotNames (absPins pk)).contains (absNIdx n) = true then
        if (entriesOf mg' (quotConstants (absPins pk) mg')).all (·.c.kind.tag == 4) = true then
          Pure.pure () else x
       else y) := by
  rw [quot_names_contains]
  refine PR.pure_step fun b hb => ?_
  rw [← nidx_eq2_abs hb]
  cases b with
  | true =>
    rw [ite_eq_left rfl, ite_eq_left (by simp)]
    exact quot_ok_arm hm hx
  | false =>
    rw [ite_eq_right (by simp)]
    refine PR.pure_step fun b hb => ?_
    rw [← nidx_eq2_abs hb]
    cases b with
    | true =>
      rw [ite_eq_left rfl, ite_eq_left (by simp)]
      exact quot_ok_arm hm hx
    | false =>
      rw [ite_eq_right (by simp)]
      refine PR.pure_step fun b hb => ?_
      rw [← nidx_eq2_abs hb]
      cases b with
      | true =>
        rw [ite_eq_left rfl, ite_eq_left (by simp)]
        exact quot_ok_arm hm hx
      | false =>
        rw [ite_eq_right (by simp)]
        refine PR.pure_step fun b hb => ?_
        rw [← nidx_eq2_abs hb]
        cases b with
        | true =>
          rw [ite_eq_left rfl, ite_eq_left (by simp)]
          exact quot_ok_arm hm hx
        | false =>
          rw [ite_eq_right (by simp), ite_eq_right (by simp)]
          exact PR.pure_step fun _ _ => PR.pure_step fun _ _ => PR.bad hy

/-! ## `block_step`, `blocks_ok` -/

/-- **`block_step` is `blockStep`.** -/
theorem block_step_pr {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {ar : arena.store.EStore} {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') (n : arena.handle.NIdx) :
    PR (fun _ _ => True) (block_step pk pers ar mg n) (blockStep (absPins pk) mg' (absNIdx n)) := by
  rw [block_step, blockStep]
  refine PR.pure_step fun o1 h1 => ?_
  have hg := mg_get_rel hm h1
  cases hg' : mg'.get (absNIdx n) with
  | none =>
    rw [hg'] at hg
    cases hg
    exact PR.pure trivial
  | some c' =>
    rw [hg'] at hg
    cases hg with
    | some hc =>
      have hk := hc.1.kind
      dsimp only
      generalize frontend.olean.spec.CEntryF.kind _ = k at hk ⊢
      generalize c'.c.kind = k' at hk ⊢
      cases k <;> cases k' <;> try exact (hk : False).elim
      case Ax.ax u u' => exact PR.pure trivial
      case Defn.defn v hh s v' h' s' => exact PR.pure trivial
      case Thm.thm v a v' a' => exact PR.pure trivial
      case Opaq.opaq v u v' u' => exact PR.pure trivial
      case Quot.quot s s' =>
        exact block_step_quot hm (by fails_int) (by fails_int)
      case Induct.induct np ni all cs nn ir iu irf np' ni' all' cs' nn' ir' iu' irf' =>
        obtain ⟨-, -, hall, hcs, -⟩ := hk
        have hall' : all.val.map absNIdx = all' := hall
        have hcs' : cs.val.map absNIdx = cs' := hcs
        subst hall' hcs'
        refine PR.pure_step fun b hb => ?_
        rw [c_entry_skipped_eq hc hb]
        exact block_step_induct_pr hm n all cs _ (by fails_int)
      case Ctor.ctor ind ci np nf iu ind' ci' np' nf' iu' =>
        obtain ⟨rfl, -⟩ := hk
        exact block_step_ctor_pr hm n ind (by fails_int) (by fails_int) (by fails_int)
      case Recur.recur all np ni nmo nmi rules kk iu all' np' ni' nmo' nmi' rules' kk' iu' =>
        obtain ⟨hall, -⟩ := hk
        have hall' : all.val.map absNIdx = all' := hall
        subst hall'
        refine PR.pure_step fun b hb => ?_
        rw [c_entry_skipped_eq hc hb]
        exact block_step_recur_pr hm n all _ (by fails_int) (fun _ => by fails_int)
          (fun _ => by fails_int) (fun _ => by fails_int) (fun _ => by fails_int)

/-- **`blocks_ok` is `blocksOk`.** -/
theorem blocks_ok_pr {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {ar : arena.store.EStore} {mg : frontend.olean.merge.Merged} {mg' : Arena.Frontend.Olean.Merged}
    (hm : MergedRel mg mg') :
    PR (fun _ _ => True) (blocks_ok pk pers ar mg) (blocksOk (absPins pk) mg') := by
  rw [blocks_ok, blocksOk, ← hm.order, forM_map]
  exact up_loop_pr (L := fun i => blocks_ok_loop pk pers ar mg i) mg.order
    (step := fun x => block_step pk pers ar mg x)
    (fun i => by rw [blocks_ok_loop]; rfl)
    (fun x => block_step_pr hm x) 0#usize

end ConRon.Refine2.Frontend.Olean

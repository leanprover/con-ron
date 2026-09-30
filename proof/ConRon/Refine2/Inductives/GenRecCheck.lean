/-
# `ConRon.Refine2.Inductives.GenRecCheck` — Theorem 2 for `gen_rec`'s stage

**Task #105** (DESIGN.md §8.2, Theorem 2).  The second half of
`crates/con-ron-core/src/arena/inductives/gen_rec.rs` against
`proof/ConRon/Arena/Inductives/GenRec.lean`: the classes read and checked
(`check_block_classes`), per class and constructor the datum and node
agreement (`class_ctor_of`), the generated types and rules checked and
installed, and `gen_rec_check`.  The generator is `GenRec.lean`.

## Shapes

* A Rust cursor with a pushing accumulator against a twin that conses after
  its recursive call: the statement puts the accumulator in front of the twin's
  answer (`A a = A out ++ b`), and the step's tail is `ls_tail_cons` /
  `lsr_tail_cons`.
* The Rust passes `vis` beside `fe`: the relation is `CoreCtx vis rf lf`, as in
  `RecCheck.lean`.
-/
import ConRon.Refine2.Inductives.GenRec

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open Lockstep
open scoped IndSide

attribute [local lockstep_simp] pos_core_walk_fuel_abs pos_core_walk_fuel_val
  gr_absIConstantVal_name gr_absIConstantVal_levelParams gr_absIConstantVal_type
attribute [local lockstep] pos_zero_level_ls pos_i_constant_val_dup_spec rc_shape_member_names_twin

/-! ## The cons tails -/

theorem ls_tail_cons {β τ : Type} {A : τ → List β} {pers : arena.store.PersTier}
    {m : Result (core.result.Result τ kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM (List β)} {y : β} {out out1 : τ}
    (h : LS pers (fun a b => A a = A out1 ++ b) m lst x) (hout : A out1 = A out ++ [y]) :
    LS pers (fun a b => A a = A out ++ b) m lst (do let r ← x; pure (y :: r)) :=
  LS.twin_map h (fun a b h1 => by rw [h1, hout]; simp)

theorem lsr_tail_cons {β τ : Type} {A : τ → List β} {pers : arena.store.PersTier}
    {m : Result (core.result.Result τ kernel.core_types.CheckError)}
    {st : arena.monad.AState} {lst : AState} {x : AM (List β)} {y : β} {out out1 : τ}
    (h : LSR pers (fun a b => A a = A out1 ++ b) m st lst x) (hout : A out1 = A out ++ [y]) :
    LS pers (fun a b => A a = A out ++ b) (m >>= fun o => ok (o, st)) lst
      (do let r ← x; pure (y :: r)) :=
  ls_tail_cons (LSR.tail_ls h rfl (fun _ _ h => h)) hout

/-! ## `nfs_of_ctor`, `minor_hits`, `class_minor_slot` -/

@[lockstep] theorem nfs_of_ctor_twin (es : alloc.vec.Vec arena.inductives.positivity.NestCtorNf)
    (c : arena.handle.NIdx) :
    LSP (arena.inductives.gen_rec.nfs_of_ctor es c 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq ((es.val.map absNestCtorNf).filter (·.ctor == absNIdx c))
        (o.val.map absNestCtorNf)) := by
  intro o h
  have := vec_cursor_filterMap es
    (fun e => if (absNestCtorNf e).ctor == absNIdx c then some (absNestCtorNf e) else none)
    (fun v => v.val.map absNestCtorNf)
    (arena.inductives.gen_rec.nfs_of_ctor es c) ?_ ?_ 0#usize _ o h
  · rw [TwinEq, this, filterMap_ite_eq absNestCtorNf (·.ctor == absNIdx c)]
    simp [alloc.vec.Vec.new]
  · intro i out o hn h
    rw [arena.inductives.gen_rec.nfs_of_ctor.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len es by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro k x out o hx h
    rw [arena.inductives.gen_rec.nfs_of_ctor.eq_def, if_neg (show ¬ k ≥ alloc.vec.Vec.len es by
      have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv := nidx_eq2_abs hb
    cases b
    · rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      refine ⟨i2, out, absSz_add_one hi2, ?_, h⟩
      simp [absNestCtorNf, ← hbv]
    · rw [if_pos rfl] at h
      obtain ⟨q1, hq1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      refine ⟨i2, out1, absSz_add_one hi2, ?_, h⟩
      rw [nest_ctor_nf_dup_spec _ _ hq1] at hout1
      simp [ConRon.Refine.vec_push_val hout1, absNestCtorNf, ← hbv]

/-- `classMinorSlot`'s hit at slot `s` (its `match`-lambda, named). -/
def grMinorHit (slots : List ClassSlot) (c : Nat) (C : NIdx) (s : Nat) :
    Option (Nat × List (Nat × Nat)) :=
  match slots[s]? with
  | some (.minor c' C' ihs) => if c' == c && C' == C then some (s, ihs) else none
  | _ => none

def classMinorSlot' (rd : ClassRead) (c : Nat) (C : NIdx) : AM (Nat × List (Nat × Nat)) := do
  let hits := (List.range rd.slots.length).filterMap (grMinorHit rd.slots c C)
  match hits with
  | [h] => pure h
  | _ => fail (.invalid "generated recursor: the recursors' prefix does not have exactly one \
      minor premise for  (official: invalid recursor)")

theorem classMinorSlot_eq : classMinorSlot = classMinorSlot' := by
  funext rd c C
  simp only [classMinorSlot, classMinorSlot']
  congr 2

def absHit (p : Std.U64 × alloc.vec.Vec (Std.U64 × Std.U64)) : Nat × List (Nat × Nat) :=
  (absU p.1, p.2.val.map absNatPair)

theorem minor_hits_abs (slots : alloc.vec.Vec arena.inductives.class_read.ClassSlot)
    (c : Std.U64) (cn : arena.handle.NIdx) :
    ∀ (s : Std.Usize) out o, arena.inductives.gen_rec.minor_hits slots c cn s out = ok o →
      o.val.map absHit = out.val.map absHit ++
        (List.range' s.val (slots.val.length - s.val)).filterMap
          (grMinorHit (slots.val.map absClassSlot) (absU c) (absNIdx cn)) := by
  intro s
  refine cursor_induction (fun i : Std.Usize => i.val) slots.val.length
    (fun s (_ : Unit) => ∀ out o, arena.inductives.gen_rec.minor_hits slots c cn s out = ok o →
      o.val.map absHit = out.val.map absHit ++
        (List.range' s.val (slots.val.length - s.val)).filterMap
          (grMinorHit (slots.val.map absClassSlot) (absU c) (absNIdx cn))) ?_ ?_ s ()
  · intro s _ hn out o h
    rw [arena.inductives.gen_rec.minor_hits.eq_def,
      if_pos (show s ≥ alloc.vec.Vec.len slots by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [show slots.val.length - s.val = 0 by omega]; simp
  · intro s _ hs ih out o h
    rw [arena.inductives.gen_rec.minor_hits.eq_def,
      if_neg (show ¬ s ≥ alloc.vec.Vec.len slots by scalar_tac)] at h
    rw [show slots.val.length - s.val = (slots.val.length - (s.val + 1)) + 1 by omega,
      List.range'_succ, List.filterMap_cons]
    obtain ⟨cs, hcs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx := vec_index_some hcs
    cases cs with
    | Motive k =>
      have hg : grMinorHit (slots.val.map absClassSlot) (absU c) (absNIdx cn) s.val = none := by
        simp only [grMinorHit, List.getElem?_map, hx, Option.map_some, absClassSlot]
      rw [hg]
      obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi1v : i1.val = s.val + 1 := absSz_add_one hi1
      rw [ih i1 () hi1v out o h, hi1v]
    | Minor c2 n2 ihs =>
      have hg : grMinorHit (slots.val.map absClassSlot) (absU c) (absNIdx cn) s.val =
          if absU c2 == absU c && absNIdx n2 == absNIdx cn then
            some (s.val, ihs.val.map absNatPair) else none := by
        simp only [grMinorHit, List.getElem?_map, hx, Option.map_some, absClassSlot]
      rw [hg]
      dsimp only at h
      by_cases hc : c2 = c
      · rw [if_pos hc] at h
        obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hbv := nidx_eq2_abs hb
        subst hc
        cases b
        · rw [if_neg (by simp)] at h
          obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hi1v : i1.val = s.val + 1 := absSz_add_one hi1
          rw [ih i1 () hi1v out o h, hi1v, ← hbv]
          simp
        · rw [if_pos rfl] at h
          obtain ⟨k, hk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hi2v : i2.val = s.val + 1 := absSz_add_one hi2
          rw [ih i2 () hi2v out1 o h, hi2v, ← hbv,
            ConRon.Refine.vec_push_val hout1, pairs_dup_spec _ _ hv]
          have hkv : k.val = s.val := by
            simp only [lift, Result.ok.injEq] at hk; subst hk
            exact ConRon.Refine.ExprOps.usize_cast_u64_val s
          simp [absHit, absU, hkv]
      · rw [if_neg hc] at h
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi1v : i1.val = s.val + 1 := absSz_add_one hi1
        rw [ih i1 () hi1v out o h, hi1v]
        have : (absU c2 == absU c) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h'; exact hc (u64_eq_iff_val.mpr h')
        simp [this]

@[lockstep] theorem minor_hits_twin (slots : alloc.vec.Vec arena.inductives.class_read.ClassSlot)
    (c : Std.U64) (cn : arena.handle.NIdx) :
    LSP (arena.inductives.gen_rec.minor_hits slots c cn 0#usize (alloc.vec.Vec.new _))
      (fun o => TwinEq ((List.range (slots.val.map absClassSlot).length).filterMap
          (grMinorHit (slots.val.map absClassSlot) (absU c) (absNIdx cn))) (o.val.map absHit)) := by
  intro o h
  rw [TwinEq, minor_hits_abs slots c cn 0#usize _ o h]
  simp [alloc.vec.Vec.new, List.range_eq_range']

theorem gr_absClassRead_slots (r : arena.inductives.class_read.ClassRead) :
    (absClassRead r).slots = r.slots.val.map absClassSlot := rfl
theorem gr_absClassRead_recCls (r : arena.inductives.class_read.ClassRead) :
    (absClassRead r).recCls = r.rec_cls.val.map absU := rfl
attribute [local lockstep_simp] gr_absClassRead_slots gr_absClassRead_recCls

/-- `class_minor_slot` ⊑ `classMinorSlot` (a pure read that may fail). -/
@[lockstep] theorem class_minor_slot_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (rd : arena.inductives.class_read.ClassRead) (c : Std.U64)
    (cn : arena.handle.NIdx) :
    LSR pers (fun a b => b = absHit a) (arena.inductives.gen_rec.class_minor_slot rd c cn) st lst
      (classMinorSlot (absClassRead rd) (absU c) (absNIdx cn)) := by
  apply LSR.of_LS
  rw [arena.inductives.gen_rec.class_minor_slot, classMinorSlot_eq, classMinorSlot']
  lockstep
  · rename_i hw hd tl hdisc
    have hlen : a.val.length = 1 := by
      have := congrArg (fun x : Std.Usize => x.val) hc; simpa [alloc.vec.Vec.len] using this
    obtain ⟨h0, ha⟩ := List.length_eq_one_iff.mp hlen
    rw [ha] at hdisc
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at hdisc
    obtain ⟨rfl, rfl⟩ := hdisc
    simp only [ha]
    exact LS.pure rfl hrel hinv
  · have hlen : (‹alloc.vec.Vec (Std.U64 × alloc.vec.Vec (Std.U64 × Std.U64))›).val.length ≠ 1 := by
      intro h1; apply hc; scalar_tac
    rcases ha : (‹alloc.vec.Vec (Std.U64 × alloc.vec.Vec (Std.U64 × Std.U64))›).val with
      _ | ⟨h0, _ | ⟨h1, t⟩⟩
    all_goals simp only [ha, List.map_nil, List.map_cons]
    all_goals first | (simp [ha] at hlen; done) | lockstep

end ConRon.Refine2

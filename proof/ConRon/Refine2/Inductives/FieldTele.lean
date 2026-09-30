/-
# `ConRon.Refine2.Inductives.FieldTele` — Theorem 2 for `arena::inductives::field_tele`

**Task #105** (DESIGN.md §8.2).  `crates/con-ron-core/src/arena/inductives/field_tele.rs`
against `proof/ConRon/Arena/Inductives/FieldTele.lean`: `pi_binders`, the
leading `∀` telescope of a term.  The lowest module of the tier, so it also
carries the telescope's abstraction (`absBinderL`), which every higher module
reads.

The Rust pushes each binder onto an accumulator on the way in, the twin conses
it on the way out: the statement puts the accumulator in front of the twin's
list (`pi_binders_ls`), and the callers' form (`Vec::new()`) is the twin
itself (`pi_binders_new_ls`).  It is a READ (`LSR`): `&AState`.
-/
import ConRon.Refine2.Tactic.Prims
import ConRon.Arena.Inductives.FieldTele

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-- A `Vec<(EIdx, BinderMeta)>` as the twin's `List (EIdx × BinderMeta)` —
`piBinders`' telescope.  `Refine2/Checker/Shape.lean`'s `absBinderArr` is the
same `Vec` read as `domsMatchAux`' `Array`. -/
def absBinderL (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    List (EIdx × ConLeche.BinderMeta) :=
  v.val.map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)

def absBinderLFrom (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
    (i : Std.Usize) : List (EIdx × ConLeche.BinderMeta) :=
  (v.val.drop i.val).map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)

/-! ## The error constructors, for the `lockstep` tactic

The port builds a decline's error as `invalid (code_points M_…)` (or
`not_implemented`/`internal`) and then `fail`s with it; the twin fails with the
kind and a message string.  The kinds are what `AErrSim` compares, so each
constructor is a Rust-only step whose spec is the constructor itself. -/

open Lockstep in
@[lockstep] theorem core_types_invalid_ls (m : alloc.vec.Vec Std.U32) :
    LSP (kernel.core_types.invalid m) (fun e => e = .Invalid m) := by
  intro e h; simp only [kernel.core_types.invalid, Result.ok.injEq] at h; exact h.symm

open Lockstep in
@[lockstep] theorem core_types_not_implemented_ls (m : alloc.vec.Vec Std.U32) :
    LSP (kernel.core_types.not_implemented m) (fun e => e = .NotImplemented m) := by
  intro e h; simp only [kernel.core_types.not_implemented, Result.ok.injEq] at h
  exact h.symm

open Lockstep in
@[lockstep] theorem core_types_internal_ls (m : alloc.vec.Vec Std.U32) :
    LSP (kernel.core_types.internal m) (fun e => e = .Internal m) := by
  intro e h; simp only [kernel.core_types.internal, Result.ok.injEq] at h; exact h.symm

open Lockstep in
/-- `pi_binders` ⊑ `piBinders`, with the accumulated binders in front — a READ
(`LSR`), by the counted fuel induction. -/
@[lockstep] theorem pi_binders_ls
    {pers st lst}
    {fuel : Std.U64}
    {h : arena.handle.EIdx}
    {out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = (fun r => (absBinderL r.1, absEIdx r.2)) a)
      (arena.inductives.field_tele.pi_binders pers st fuel h out) st lst
      (do
        let q ← piBinders (absU fuel) (absEIdx h)
        pure (absBinderL out ++ q.1, q.2)) := by
  suffices H : ∀ (n : Nat) (fuel : Std.U64) (h : arena.handle.EIdx)
      (out : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) (lst : AState),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = (fun r => (absBinderL r.1, absEIdx r.2)) a)
        (arena.inductives.field_tele.pi_binders pers st fuel h out) st lst
        (do
          let q ← piBinders (absU fuel) (absEIdx h)
          pure (absBinderL out ++ q.1, q.2)) from H _ fuel h out lst rfl hrel hinv
  clear hrel hinv
  intro n
  induction n with
  | zero =>
    intro fuel h out lst hf hrel hinv
    have h0 : fuel = 0#u64 := by scalar_tac
    subst h0
    rw [arena.inductives.field_tele.pi_binders.eq_def, if_pos rfl]
    rw [show absU (0#u64 : Std.U64) = 0 from rfl, piBinders]
    apply LSR.of_LS
    lockstep
  | succ n ih =>
    intro fuel h out lst hf hrel hinv
    rw [arena.inductives.field_tele.pi_binders.eq_def, if_neg (by scalar_tac)]
    rw [show absU fuel = n + 1 by simp [absU, hf], piBinders]
    apply LSR.of_LS
    lockstep
    rename_i v hv
    refine LSR.tail_ls (ih _ _ _ _ ?_ (by assumption) (by assumption)) ?_ (fun _ _ h => h)
    · scalar_tac
    · have e : absU a = n := by simp only [absU]; scalar_tac
      simp only [e, absBinderL, hv, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append, List.nil_append]
      rfl

open Lockstep in
/-- `pi_binders` from an empty accumulator IS `piBinders` (the callers' form). -/
@[lockstep] theorem pi_binders_new_ls
    {pers st lst}
    {fuel : Std.U64}
    {h : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = (fun r => (absBinderL r.1, absEIdx r.2)) a)
      (arena.inductives.field_tele.pi_binders pers st fuel h
        (alloc.vec.Vec.new (arena.handle.EIdx × kernel.expr.BinderMeta))) st lst
      (piBinders (absU fuel) (absEIdx h)) := by
  have hl := pi_binders_ls (fuel := fuel) (h := h)
    (out := alloc.vec.Vec.new (arena.handle.EIdx × kernel.expr.BinderMeta)) hrel hinv
  have e : (do
      let q ← piBinders (absU fuel) (absEIdx h)
      pure (absBinderL (alloc.vec.Vec.new (arena.handle.EIdx × kernel.expr.BinderMeta)) ++ q.1,
        q.2) : AM _) = piBinders (absU fuel) (absEIdx h) := by
    simp [absBinderL, alloc.vec.Vec.new]
  rwa [e] at hl

end ConRon.Refine2

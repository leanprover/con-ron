/-
# `ConRon.Refine2.Core.Entries` — the six fueled entry points, from `KnotRel`

**Task #97-P5-Core, the tier's interface.**  `ConLeche/Kernel/TypeChecker.lean`'s
seven (T) declarations live in `arena::core` because the arena has ONE knot
(the twin's deviation 5), and each is `LANE_FULL` applied to the knot entry of
the same name.  So each of these is `KnotRel f` at `LANE_FULL` with
`laneKnot_full` in front of it, and **none of them needs anything else** — they
are the whole of what the Checker tier consumes from this tier.

`ensure_sort_core` is the seventh and is NOT here: `ensure_sort` is a body, not
a knot slot (it runs `r.whnf` and then reads the view), so it belongs in
`Core/Arms/*` with the rest of the bodies and its statement is there.

**What the Checker tier should call:** `knotRel_checkFuel`, below —
`KnotRel (absU CHECK_FUEL)`, i.e. `KnotRel 100000` — and then the six
`*_refines`.  **Since task #97-P5-Core round 4 they are LOCKSTEP statements**:
over `AStateRel₀` (no `StoreWF`), with no `EResolves` premise and a `Sim₀`
conclusion (no `Ext`).  Task #97-P5-0's finding 3 — the tag-first / view-first
split that made them need a resolving argument — is gone because the twin now
tests the tag where the port does (round 4's audit); a consumer that still
wants `Sim` takes `Sim₀.toSim` with the twin's own two facts from Theorem 1.
-/
import ConRon.Refine2.Core.Induction

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena


section Entries

variable {pers vis st mode fe lfe fu depth lst}

/-- `arena::core::whnf` against `Arena.whnf`, with no side condition. -/
theorem whnf_refines {f : Nat} (hk : KnotRel f) {e o} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (hf : absU fu = f)
    (hrun : arena.core.whnf pers vis st mode fe fu depth e = ok o) :
    Sim₀ absEIdx pers lst o
      (Arena.whnf (ConRon.Refine.absMode mode) lfe f (absU depth)
        (absEIdx e)) := by
  rw [arena.core.whnf] at hrun
  have h := hk.whnf hrel hinv hctx hf hrun
  rw [laneKnot_full] at h
  exact h

/-- `arena::core::infer_type_core` against `Arena.inferTypeCore`. -/
theorem infer_type_core_refines {f : Nat} (hk : KnotRel f) {e o} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (hf : absU fu = f)
    (hrun : arena.core.infer_type_core pers vis st mode fe fu depth e = ok o) :
    Sim₀ absEIdx pers lst o
      (Arena.inferTypeCore (ConRon.Refine.absMode mode) lfe f (absU depth)
        (absEIdx e)) := by
  rw [arena.core.infer_type_core] at hrun
  have h := hk.infer hrel hinv hctx hf hrun
  rw [laneKnot_full] at h
  exact h

/-- `arena::core::is_def_eq_core` against `Arena.isDefEqCore`. -/
theorem is_def_eq_core_refines {f : Nat} (hk : KnotRel f) {a b o} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (hf : absU fu = f)
    (hrun : arena.core.is_def_eq_core pers vis st mode fe fu depth a b = ok o) :
    Sim₀ id pers lst o
      (Arena.isDefEqCore (ConRon.Refine.absMode mode) lfe f (absU depth)
        (absEIdx a) (absEIdx b)) := by
  rw [arena.core.is_def_eq_core] at hrun
  have h := hk.defeq hrel hinv hctx hf hrun
  rw [laneKnot_full] at h
  exact h

/-- `arena::core::annotate_core` against `Arena.annotateCore`. -/
theorem annotate_core_refines {f : Nat} (hk : KnotRel f) {e o} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe)
    (hf : absU fu = f)
    (hrun : arena.core.annotate_core pers vis st mode fe fu depth e = ok o) :
    Sim₀ absEIdx pers lst o
      (Arena.annotateCore (ConRon.Refine.absMode mode) lfe f (absU depth)
        (absEIdx e)) := by
  rw [arena.core.annotate_core] at hrun
  have h := hk.annotate hrel hinv hctx hf hrun
  rw [laneKnot_full] at h
  exact h

end Entries

/-! ## The fuel the checker runs at

`CHECK_FUEL = 100000 = checkFuel`, on both sides, and the Checker tier calls
`knot_rel` at exactly that. -/

theorem check_fuel_abs : absU arena.core.CHECK_FUEL = Arena.checkFuel := by
  rw [arena.core.CHECK_FUEL, Arena.checkFuel]
  rfl


section Axioms


/-- info: 'ConRon.Refine2.whnf_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whnf_refines

/-- info: 'ConRon.Refine2.is_def_eq_core_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms is_def_eq_core_refines

/-- info: 'ConRon.Refine2.check_fuel_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_fuel_abs

end Axioms

end ConRon.Refine2

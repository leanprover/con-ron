/-
# `ConRon.Refine2.Inductives.Prims` — the tier's `@[lockstep]` callees from other tiers

Task #97-T2-LOCKSTEP lane Inductives round 3.  The tier's Rust calls about
65 functions outside `arena::inductives` (the core's level comparison, the
environment's readers, the checker's `checker_base`, the promote tier's name
builders …).  Their Theorem-2 lemmas live with their owners, mostly as
`_refines`/`_run` statements in `Sim₀`/`LSS` form without the `@[lockstep]`
attribute; this file files them for the tactic — in `LS` form where a
conversion is needed, by `attribute [lockstep]` where not — and adds the
Rust-only specs the tier's zips need.  Nothing here restates an owner's lemma.
-/
import ConRon.Refine2.Checker.Base

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

open Lockstep in
/-- `arena::core::lvl_eq` ⊑ `lvlEq?` (`Refine2/Checker/Base.lean`). -/
@[lockstep] theorem lvl_eq_ls {pers st lst} {u v : arena.handle.LIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.core.lvl_eq pers st u v) lst
      (lvlEq? (absLIdx u) (absLIdx v)) :=
  LS.ofSim₀ fun _ h => lvl_eq_refines hrel hinv h

attribute [lockstep] proj_table_name_lss

end ConRon.Refine2

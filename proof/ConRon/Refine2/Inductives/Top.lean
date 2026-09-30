/-
# `ConRon.Refine2.Inductives.Top` — the tier's exports to the checker

**Task #105** (DESIGN.md §8.2, Theorem 2).  The `.indDecl` arm of
`arena::check_decl::check_decl` — `arena::check_decl::check_ind_decl` against
`Arena/CheckDecl.lean`'s `checkDecl` arm — is the pinned-basis test, the
declared parameter count, the recogniser and ONE route (the uniform install
`checkBlock` or the shapeless decline `checkShapeless`).  The basis-pin half
(`basis_pin_hit`, `check_basis_decl`) and `ind_params_ok` are the checker
tier's, and `Refine2/Checker/Top.lean` imports this module, so the arm's own
statement (`check_ind_decl_refines`) is proved THERE by one `lockstep` call,
over the three companions this module exports:

| Rust | twin |
|---|---|
| `block_parts::block_parts` | `blockParts?` |
| `block_tail::check_block` | `checkBlock` |
| `check_decl::check_shapeless` | `checkShapeless` |

All three are stated lockstep: `AStateRel₀`, `AStateInv`, the environment
related and well formed (`IFEnvRelI`, also the answer relation of the two
installs, because the checker's fold needs both for its next step).  No
`KnotRel` binder: `knotRel_checkFuel'` is a theorem
(`Refine2/Checker/KnotHyp.lean`).
-/
import ConRon.Refine2.Inductives.Abs
import ConRon.Refine2.Inductives.SumInstallF
-- `checker_base::ind_params_ok` and `check_constant_val` are the checker
-- tier's (`Checker/Base.lean`).
import ConRon.Refine2.Checker.Base

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open scoped ConRon.Refine2.IndSide

open ConRon.Arena

open Lockstep

/-- **`block_parts::block_parts` ⊑ `blockParts?`** — the recogniser. -/
@[lockstep] theorem block_parts_ls {pers st lst} {n_pd : Std.U64}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = Option.map absBlockParts a)
      (arena.inductives.block_parts.block_parts pers st n_pd block) lst
      (blockParts? (absU n_pd) (absICIL block)) := by
  sorry

/-- **`block_tail::check_block` ⊑ `checkBlock`** — the uniform install. -/
@[lockstep] theorem check_block_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    {p0 : arena.inductives.block_parts.BlockParts}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.inductives.block_tail.check_block pers st mode rf block p0) lst
      (checkBlock (ConRon.Refine.absMode mode) lf (absICIL block) (absBlockParts p0)) := by
  sorry

/-- **`check_decl::check_shapeless` ⊑ `checkShapeless`** — a block the
recogniser does not read: its formers checked, then a decline. -/
@[lockstep] theorem check_shapeless_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {block : alloc.vec.Vec arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.check_decl.check_shapeless pers st mode rf block) lst
      (checkShapeless (ConRon.Refine.absMode mode) lf (absICIL block)) := by
  sorry

end ConRon.Refine2

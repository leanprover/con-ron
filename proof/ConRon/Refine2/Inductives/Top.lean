/-
# `ConRon.Refine2.Inductives.Top` — the tier's exports to the checker

**Task #105** (DESIGN.md §8.2, Theorem 2).  The `.indDecl` arm of
`arena::check_decl::check_decl_kind` — `arena::check_decl::check_ind_decl`
against `Arena/CheckDecl.lean`'s `checkDeclKind` arm — is the declared parameter
count, the reader and ONE route (the uniform install `checkBlock`, or the
reader's reject).  `ind_params_ok` is the checker tier's, and
`Refine2/Checker/Top.lean` imports this module, so the arm's own statement
(`check_ind_decl_refines`) is proved THERE by one `lockstep` call, over the
two companions this module exports:

| Rust | twin |
|---|---|
| `block_shape::read_block` | `readBlock` |
| `block_tail::check_block` | `checkBlock` |

Both are stated lockstep: `AStateRel₀`, `AStateInv`, the environment
related and well formed (`IFEnvRelI`, also the answer relation of the two
installs, because the checker's fold needs both for its next step).  No
`KnotRel` binder: `knotRel_checkFuel'` is a theorem
(`Refine2/Checker/KnotHyp.lean`).
-/
import ConRon.Refine2.Inductives.Abs
import ConRon.Refine2.Inductives.Prims
import ConRon.Refine2.Inductives.BlockTail
import ConRon.Refine2.Inductives.StreamRecs
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

end ConRon.Refine2

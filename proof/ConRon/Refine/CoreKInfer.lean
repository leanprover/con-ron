/-
`CORE_PLAN.md` step 4 (task #49): the **pure inference clauses** of
`crates/con-ron-core/src/kernel/core_k.rs` -- the seven state-free functions
the cited `inferBody`/`annotateBody` arms of `ConLeche/Kernel/Core.lean` are
factored into, i.e. everything those arms compute without touching the
checker's recursive knot:

* `infer_lit_nat` (`:2424`) and `infer_lit_str` (`:2441`) -- the two literal
  arms of `inferBody` (`Core.lean:2039-2204`; the twin `inferBodyIO`
  `:2206-2334` has the same two arms);
* `infer_fvar` (`:2460`) -- the `.fvar` arm's scope check;
* `proj_entry_type_at` (`:2335`) -- `ProjEntry.typeAt` (`Core.lean:1797-1806`;
  twin `Cached/ExprOpsC.lean:623-642 ProjEntry.typeAtI`), the only one of the
  seven that returns a bare `Expr`;
* `proj_type_at_checked` (`:2479`) and `infer_proj_at` (`:2516`) -- the `.proj`
  arm of `inferBody`, split at the table lookup;
* `annotate_proj_entry` (`:2640`) -- the `.proj` arm of `annotateBody`
  (`Core.lean:2736-2856`).

## What carries the proofs

**Nothing below the `Expr` layer is re-walked.**  `proj_entry_type_at` is one
`instantiate_level_params` (`Refine/ExprOpsMeta.lean`), one spine reversal and
one `instantiate_list_fast` (`Refine/ExprOpsSubst.lean`); `infer_proj_at` adds
`get_app_fn`/`get_app_args` (`Refine/ExprOpsSpine.lean`) and `find_proj`
(`Refine/CoreKProj.lean`, which this file imports for `find_proj_refines` and
for the `ProjEntryWF` that lemma hands back with the entry).

**The cited arms are transcribed, not applied.**  `inferBody` and
`annotateBody` are open-recursion bodies over a `CoreFns m` record: their
`.proj` arms call `r.whnf`/`r.infer`, so there is no way to *apply* them to
abstracted arguments at this granularity, and the three `*L` definitions below
are verbatim transcriptions of the cited arms' state-free parts with the
recursive results (`te`, `e'`) as parameters -- exactly the factoring the Rust
doc comments describe.  `projPropGuard_eq` discharges the one step of the
transcription that is not literal: the cited `.proj` arm *inlines*
`ProjEntry.fireOk`'s body (`Core.lean:1250-1253`) as an `if`/`unless` pair
where the port calls the function, and that lemma proves the two agree.  Error
*messages* are carried in the transcriptions for readability only -- DESIGN.md
§3.1 does not require them to match.

**The failure half** (task #67).  Every `<fn>_refines` below is stated over the
Rust computation's *whole* inner outcome: a `match out with | .Ok r => <the
accept direction> | .Err ce => ErrSim ce <the same con-leche side>`.  Every one
of this file's twelve `CheckError` sites is a *mirrored* `throw`, so con-leche
throws at the same kind, and `invalid_arm`/`not_implemented_arm` below do the
shared bookkeeping.  The `.Err` half of each is *also* kept as the companion
`<fn>_err` stated just above it, because that half needs strictly **fewer**
hypotheses than the accept half (`infer_lit_nat` does not need `hnat` to
decline, `infer_fvar` does not need `hty`, `proj_type_at_checked` needs neither
`hrev` nor `htargs`/`hpe`, `annotate_proj_entry` does not need `he2`): the
companion is therefore the primitive of each pair, keeping its pre-#67
signature for its call sites in `Core/Arms/{Infer,Annotate}.lean`, and the
folded `<fn>_refines` discharges its `.Err` arm with it.

**Five facts are hypotheses**, each owned by a sibling agent of this task and
stated in exactly the shape that agent proves, so that discharging it at merge
is one `exact`:

| hypothesis | what discharges it |
|---|---|
| `hnat` | `Refine/CoreKNames.lean`'s `nat_name_refines` |
| `hstr` | `Refine/CoreKNames.lean`'s `string_name_refines` |
| `hnls` | `core_k::nat_lit_supported`'s refinement (`Refine/CoreKSupport.lean`) |
| `hsls` | `core_k::str_lit_supported`'s refinement (`Refine/CoreKSupport.lean`) |
| `hfire` (`ProjEntryFireOk`) | `proj_entry_fire_ok`'s refinement (`Refine/CoreKGuards.lean`) |
| `hrev` (`RevAppendExprs`) | `Refine/CoreKVec.lean`'s `rev_append_exprs_refines` |

`constKind_wf_inv` belongs in `Refine/Expr.lean` beside the `*_inv` family;
`Refine/CoreKLits.lean` has the same lemma under the name `const_wf_inv`, so
one of the two goes at merge.  `levelsWF_empty` likewise duplicates a one-liner
several `CoreK*` files carry.
-/
import ConRon.Refine.CoreKProj
import ConLeche.Kernel.Core

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.CoreK

/-! ## The mirrored `throw` arms (task #67)

Every `CheckError` this file's seven functions build is one of `core_k.rs`'s
*mirrored* sites: the port turns a code-point constant into a `Vec<u32>` and
hands it to `core_types::invalid`/`not_implemented`, and the cited con-leche arm
`throw`s at the same kind.  The two helpers below do that bookkeeping once --
the message is never read (DESIGN.md §3.1), so the con-leche side's string is
whatever the transcription carries. -/

/-! ## The two literal arms of `inferBody` -/

/-! ## The `.fvar` arm -/

/-! ## `ProjEntry.typeAt` -/

/-! ## The `.proj` arm of `inferBody` -/

/-! ## The `.proj` arm of `annotateBody` -/

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

end ConRon.Refine.CoreK

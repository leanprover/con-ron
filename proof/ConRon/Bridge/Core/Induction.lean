/-
# `ConRon.Bridge.Core.Induction` — the fuel induction, and the tier's axiom
census

DESIGN §8.2, and the third of the three pieces
`_tmp/t97/conleche-arena-history.md` §2.3 names ("one walk per twin body,
five memo wrapper steps, **one knot induction**").  con-leche's is
`Verify/Cached/KnotC.lean:530 ssimC`; this is the same term.

```lean
theorem knot_spec … : ∀ f, KnotSpec mode env fe f
  | 0     => knotSpec_zero …
  | f + 1 => { whnfCore := fun … => memoWhnfCore_step … (whnfCoreBody_spec … (knot_spec … f)) …
               … }
```

Each slot at `f + 1` is its memo wrapper applied to its body walk applied to
the induction hypothesis at `f`.  Nothing else is in it — which is the point
of splitting the tower this way: the wrappers are closed
(`Bridge/Core/Memo.lean`), the induction is closed (here), and every `sorry`
the tier carries is inside one of the six body walks.

## What the Checker tier gets

`knot_spec … checkFuel : KnotSpec mode env fe ConRon.Arena.checkFuel` — the
hypothesis DESIGN §8.2's per-declaration bridge is written against, and the
reason `Bridge/Checker/**` can be developed against a `KnotSpec` hypothesis
without waiting for the arms.  `checkFuel` is con-leche's own number
(`ConLeche/Kernel/Core.lean:1960`), twinned verbatim by task #97c, so the two
sides' fuel constants are literally equal — but nothing here depends on that:
the statement is at an arbitrary `f`.
-/
import ConRon.Bridge.Core.Arms.WhnfCore
import ConRon.Bridge.Core.Arms.Whnf
import ConRon.Bridge.Core.Arms.Infer
import ConRon.Bridge.Core.Arms.InferIO
import ConRon.Bridge.Core.Arms.Defeq
import ConRon.Bridge.Core.Arms.Annotate
import ConLeche.Verify.BetaGate

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

/-! ## The two mode facts the induction needs

`mode.ioGate` is `true` at EVERY mode (`ConLeche/Kernel/Env.lean:131`, the
licence ruling of 2026-09-06: the io grade is a licence, not a certificate,
so the trusted lane keeps it) and `mode.betaGate` follows from
`verifiedChecks`.  The twin's knot selects its io slot on `ioGate`
(`Cached/CoreC.lean:1971`'s spelling) and the pure knot on `betaGate` — task
#97c's smaller deviation 4 — so the two agree exactly at the mode the bridge
is stated at, and this is where that is cashed. -/

/-- con-leche: ConLeche/Kernel/Env.lean:131 CheckMode.ioGate — the io slot is
the io body at every mode. -/
theorem ioGate_true (mode : CheckMode) : mode.ioGate = true := by
  cases mode <;> rfl

/-! ## The induction -/

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:530 ssimC
con-leche: ConLeche/Verify/SimIKnot.lean ssimI
**THEOREM 1 AT EVERY FUEL.**  The arena's memoized knot refines con-leche's
six fueled entry points on inputs that denote and are well scoped.

The proof is con-leche's architecture term for term: fuel zero throws
everywhere, and at `f + 1` each slot is `memo_<slot>_step` applied to
`<body>_spec` applied to the induction hypothesis. -/
theorem knot_spec {mode : CheckMode} {env : Env} {fe : IFEnv}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true) :
    ∀ f, KnotSpec mode env fe f
  | 0 => knotSpec_zero mode env fe
  | f + 1 =>
    { whnfCore := fun s₀ d i e hok hden hw =>
        memoWhnfCore_step henv
          (whnfCoreBody_spec henv hμ (knot_spec henv hμ f)) s₀ d i e hok hden hw
      whnf := fun s₀ d i e hok hden hw =>
        memoWhnf_step henv
          (whnfBody_spec henv hμ (knot_spec henv hμ f)) s₀ d i e hok hden hw
      infer := fun s₀ d i e hok hden hw =>
        memoInfer_step henv
          (inferBody_spec henv hμ (knot_spec henv hμ f)) s₀ d i e hok hden hw
      defeq := fun s₀ d i j a b hok hda hdb hwa hwb =>
        memoDefeq_step henv
          (defeqBody_spec henv hμ (knot_spec henv hμ f)) s₀ d i j a b hok hda
          hdb hwa hwb
      annotate := fun s₀ d i e hok hden hw =>
        memoAnnotate_step henv
          (annotateBody_spec henv hμ (knot_spec henv hμ f)) s₀ d i e hok hden hw
      inferIO := fun s₀ d i e hok hden hw =>
        memoInferIO_step henv (ioGate_true mode)
          (inferBodyIO_spec henv hμ (ConLeche.betaGate_of_verifiedChecks hμ)
            (knot_spec henv hμ f)) s₀ d i e hok hden hw }

/-- con-leche: ConLeche/Kernel/Core.lean:1960-1963 checkFuel — **what the
Checker tier takes as its hypothesis**: the knot at the fuel the seven entry
points of `Arena/Core.lean` are called with. -/
theorem knot_spec_checkFuel {mode : CheckMode} {env : Env} {fe : IFEnv}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true) :
    KnotSpec mode env fe ConRon.Arena.checkFuel :=
  knot_spec henv hμ _

/-! ## The axiom census

DESIGN §8's gate for every tier of this library: `#print axioms` at the three
standard axioms on every CLOSED theorem, and a `sorryAx` on exactly the
declarations the task section lists.  The three come in through
`Std.HashMap`, `Classical` in `Option`'s lemmas and `Quot` in `String`, which
is what every tier of this repository already carries. -/

section Census

/-! ### The statement layer — closed -/

#print axioms SimE.ext
#print axioms SimE.denote
#print axioms SimE.wscoped
#print axioms SimE.toCache
#print axioms knotSpec_zero
#print axioms ioGate_true

/-! ### The knot's six slots, unfolded -/

#print axioms coreKnot_whnfCore_succ
#print axioms coreKnot_whnf_succ
#print axioms coreKnot_infer_succ
#print axioms coreKnot_defeq_succ
#print axioms coreKnot_annotate_succ
#print axioms coreKnot_inferIO_succ

/-! ### The six cache setters and the cache-insert lemmas — closed -/

#print axioms whnfCoreSet_spec
#print axioms whnfSet_spec
#print axioms inferSet_spec
#print axioms inferIOSet_spec
#print axioms annotSet_spec
#print axioms defeqSet_spec
#print axioms EntryCacheOK.insert
#print axioms EntryCacheOK.empty
#print axioms EntryCacheOK.insert_capped
#print axioms DefeqCacheOK.insert_capped
#print axioms CacheOK.insertWhnfCore
#print axioms CacheOK.insertWhnf
#print axioms CacheOK.insertInfer
#print axioms CacheOK.insertInferIO
#print axioms CacheOK.insertAnnot
#print axioms CacheOK.insertDefeq
#print axioms CheckOK.ofCache

/-! ### The stuck-tag branch — closed -/

#print axioms whnfCoreStuckTag_ne
#print axioms whnfStuckTag_eq
#print axioms denote_stuck_of_whnfCoreStuckTag
#print axioms denote_stuck_of_whnfStuckTag
#print axioms whnfCore_of_stuck
#print axioms whnf_of_stuck

/-! ### **The six memo wrappers — closed.**  This is the tier's own result:
the whole memo layer of Theorem 1's Core tier is sorry-free, at the three
standard axioms. -/

#print axioms memoWhnfCore_step
#print axioms memoWhnf_step
#print axioms memoInfer_step
#print axioms memoInferIO_step
#print axioms memoAnnotate_step
#print axioms memoDefeq_step

/-! ### The per-arm step lemmas — closed, fifty-two of them -/

#print axioms whnfCore_app_beta_gate
#print axioms whnfCore_app_beta_cert
#print axioms whnfCore_app_stuck
#print axioms whnfCore_app_iota
#print axioms whnfCore_app_iota_none
#print axioms whnfCore_proj_none
#print axioms whnfCore_proj_fire
#print axioms whnfCore_proj_cert_false
#print axioms whnfCore_proj_guard

#print axioms whnfLoop_reduceNat
#print axioms whnfLoop_delta
#print axioms whnfLoop_done
#print axioms whnf_of_loop

#print axioms infer_sort
#print axioms infer_fvar
#print axioms infer_const
#print axioms infer_natLit
#print axioms infer_strLit
#print axioms infer_forallE
#print axioms infer_lam_chain
#print axioms infer_lam_leaf
#print axioms infer_lam_trusted
#print axioms infer_app
#print axioms infer_proj_nonprop
#print axioms infer_proj_prop

#print axioms inferIO_lam_chain
#print axioms inferIO_lam_leaf
#print axioms inferIO_lam_trusted
#print axioms inferIO_app_licensed
#print axioms inferIO_app_cert

#print axioms defeq_of_loop
#print axioms defeqLoop_syntactic
#print axioms defeqLoop_boolTrue
#print axioms defeqLoop_whnf_eq
#print axioms defeqLoop_propIrrel
#print axioms defeqLoop_reduceNat_left
#print axioms defeqLoop_reduceNat_right
#print axioms defeqLoop_forallE
#print axioms defeqLoop_lam

#print axioms annot_bvar
#print axioms annot_fvar
#print axioms annot_sort
#print axioms annot_const
#print axioms annot_natLit
#print axioms annot_strLit
#print axioms annot_app
#print axioms annot_forallE_written
#print axioms annot_forallE_computed
#print axioms annot_lam_written
#print axioms annot_lam_computed
#print axioms annot_letE
#print axioms annot_proj

/-! ### The open list — `sorryAx` is EXPECTED on exactly these

Nine declarations, each with its reason at its site and in DESIGN §8's task
section `### Task #97-P3-Core`: the six body walks, the three batched-clause
carries and the port-side peel.  `knot_spec` inherits from the six. -/

#print axioms whnfCoreBody_app_batched
#print axioms whnfCoreBody_spec
#print axioms whnfBody_spec
#print axioms inferBody_app_batched
#print axioms inferBody_binders_batched
#print axioms inferBody_spec
#print axioms inferBodyIO_spec
#print axioms defeqPeel_chain
#print axioms defeqBody_spec
#print axioms annotateBody_binders_batched
#print axioms annotateBody_spec
#print axioms knot_spec
#print axioms knot_spec_checkFuel

end Census

end ConRon.Bridge.Core

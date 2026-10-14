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
of splitting the tower this way: the wrappers are `Bridge/Core/Memo.lean`'s,
the induction is here, and the six body walks are
`Bridge/Core/Arms/*.lean`'s.

## What the Checker tier gets

`knot_spec … checkFuel : KnotSpec mode env fe ConRon.Arena.checkFuel` — the
hypothesis DESIGN §8.2's per-declaration bridge is written against, and the
reason `Bridge/Checker/**` depends on the core only through a `KnotSpec`
hypothesis.  `checkFuel` is con-leche's own number
(`ConLeche/Kernel/Core.lean:1960`), twinned verbatim (DESIGN `### Task #97c`), so the two
sides' fuel constants are literally equal — but nothing here depends on that:
the statement is at an arbitrary `f`.
-/
import ConRon.Bridge.Core.Arms.WhnfCore
import ConRon.Bridge.Core.Arms.Whnf
import ConRon.Bridge.Core.Arms.Infer
import ConRon.Bridge.Core.Arms.InferIO
import ConRon.Bridge.Core.Arms.Defeq

namespace ConRon.Bridge.Core

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The induction -/

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:530 ssimC
con-leche: ConLeche/Verify/SimIKnot.lean ssimI
**THEOREM 1 AT EVERY FUEL.**  The arena's memoized knot refines con-leche's
five fueled entry points on inputs that denote and are well scoped.

The proof is con-leche's architecture term for term: fuel zero throws
everywhere, and at `f + 1` each slot is `memo_<slot>_step` applied to
`<body>_spec` applied to the induction hypothesis. -/
theorem knot_spec {mode : CheckMode} {env : Env} {fe : IFEnv}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true) :
    ∀ f, KnotSpec mode env fe f
  | 0 => knotSpec_zero mode env fe
  | f + 1 =>
    { whnfCore := fun {c} s₀ d i e hok hden hw =>
        memoWhnfCore_step henv
          (fun c => whnfCoreBody_spec henv hμ (knot_spec henv hμ f) c) (c := c)
          s₀ d i e hok hden hw
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
      inferIO := fun s₀ d i e hok hden hw =>
        memoInferIO_step henv
          (inferBodyIO_spec henv hμ (knot_spec henv hμ f)) s₀ d i e hok hden hw }

/-- con-leche: ConLeche/Kernel/Core.lean:1960-1963 checkFuel — **what the
Checker tier takes as its hypothesis**: the knot at the fuel the seven entry
points of `Arena/Core.lean` are called with. -/
theorem knot_spec_checkFuel {mode : CheckMode} {env : Env} {fe : IFEnv}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true) :
    KnotSpec mode env fe ConRon.Arena.checkFuel :=
  knot_spec henv hμ _

/-! ## The axiom census

DESIGN §8's gate for every tier of this library: `#print axioms` at the three
standard axioms on every theorem.  The three come in through
`Std.HashMap`, `Classical` in `Option`'s lemmas and `Quot` in `String`, which
is what every tier of this repository already carries. -/

section Census

/-! ### The statement layer -/

#print axioms knotSpec_zero

/-! ### The knot's five slots, unfolded -/

#print axioms coreKnot_whnfCore_succ
#print axioms coreKnot_whnf_succ
#print axioms coreKnot_infer_succ
#print axioms coreKnot_defeq_succ
#print axioms coreKnot_inferIO_succ

/-! ### The cache setters and the cache-insert lemmas -/

#print axioms whnfCoreSet_spec
#print axioms whnfSet_spec
#print axioms inferSet_spec
#print axioms inferIOSet_spec
#print axioms defeqSet_spec
#print axioms EntryCacheOK.insert
#print axioms DefeqCacheOK.insert
#print axioms CacheOK.insertWhnfCore
#print axioms CacheOK.insertWhnf
#print axioms CacheOK.insertInfer
#print axioms CacheOK.insertInferIO
#print axioms CacheOK.insertDefeq
#print axioms CheckOK.ofCache

/-! ### The stuck-tag branch -/

#print axioms whnfCoreStuckTag_ne
#print axioms whnfStuckTag_eq
#print axioms denote_stuck_of_whnfCoreStuckTag
#print axioms denote_stuck_of_whnfStuckTag
#print axioms whnfCore_of_stuck
#print axioms whnf_of_stuck

/-! ### **The five memo wrappers.**  This is the tier's own result: the whole
memo layer of Theorem 1's Core tier, at the three standard axioms. -/

#print axioms memoWhnfCore_step
#print axioms memoWhnf_step
#print axioms memoInfer_step
#print axioms memoInferIO_step
#print axioms memoDefeq_step

/-! ### The per-arm step lemmas -/

#print axioms mStep_app
#print axioms mStep_proj_none
#print axioms mStep_proj_some
#print axioms whnfCore_of_loopM
#print axioms reduceProjCore_eq

#print axioms whnfLoop_reduceNat
#print axioms whnfLoop_delta
#print axioms whnfLoop_done
#print axioms whnf_of_loop

#print axioms infer_sort
#print axioms infer_fvar
#print axioms infer_const
#print axioms infer_natLit
#print axioms infer_strLit
#print axioms infer_proj_nonprop
#print axioms infer_proj_prop

#print axioms infer_letE
#print axioms inferIO_lam
#print axioms inferIO_letE

#print axioms defeqBody_syntactic
#print axioms defeqBody_boolTrue
#print axioms defeqBody_quick
#print axioms defeqBody_propIrrel
#print axioms defeqBody_verdict
#print axioms defeqBody_unknown

/-! ### The body walks, the batched-clause carries and the knot

The six body walks, the batched-clause carries and the port-side peel (DESIGN
§8's task section `### Task #97-P3-Core` gives each one's structure), and
`knot_spec` over them; each prints the three standard axioms only. -/

#print axioms betaPeel_carry
#print axioms whnfApp_carry
#print axioms whnfCoreStep_spec
#print axioms whnfCoreLoop_spec
#print axioms whnfCoreBody_spec
#print axioms whnfBody_spec
#print axioms inferBody_app_batched
#print axioms inferBody_binders_batched
#print axioms inferBody_spec
#print axioms inferBodyIO_spec
#print axioms defeqBinders_spec
#print axioms defeqBody_spec
#print axioms knot_spec
#print axioms knot_spec_checkFuel

end Census

end ConRon.Bridge.Core

/-
# `ConRon.Bridge.Core.Arms.InferIO` — Theorem 1 for `inferBodyIO`

DESIGN §8.2, rule 8's inventory for `ConLeche/Kernel/Core.lean:1276-1404
inferBodyIO` — **the io grade** (con-leche's task #170/#172 B4).  The body is
`inferBody` with two clauses changed, and those two are the only lemmas that
differ from `Bridge/Core/Arms/Infer.lean`'s:

| clause | exit | lemma |
|---|---|---|
| `.lam` | **no domain-sort run** (official's `infer_lambda` at `infer_only`) | `inferIO_lam_chain`, `inferIO_lam_leaf`, `inferIO_lam_trusted` |
| `.app` | **the licensed arm**: the ∀'s datum is `never`, so no certificate | `inferIO_app_licensed` |
| `.app` | the unlicensed arm: the certificate runs, as at the full grade | `inferIO_app_cert` |

Everything else (`.sort`, `.fvar`, `.const`, the two literals, `.forallE`,
`.proj`, the two throws) is byte-identical to `inferBody`'s, and the io
lemmas for those clauses are the same proofs at `inferTypeIO`; the four that
this round states are below, the rest are listed in DESIGN §8's task section.

## Why the statements are at `betaGate = true`

The knot's io slot selects the grade once per level: at `mode.betaGate = false`
the slot IS full inference (`ConLeche.inferTypeIO_off`), so the io lemmas are
`Infer.lean`'s verbatim and there is nothing to state.  The bridge is stated
at `.verified`, where the bit is on — which is also where the twin's
`mode.ioGate` agrees with it (task #97c's smaller deviation 4).

## The grade propagates through the RECORD, not through a flag

`inferBodyIO` recurses through `r.infer`, and the knot hands it
`CoreFns.ioView (coreKnot … fuel)` — the record whose `infer` slot is the io
slot.  So every `r.infer` below is `ConLeche.inferTypeIO mode env F`, which
is what the hypotheses say.  This is official's `infer_type_core` passing
`infer_only` down, without a textual twin.
-/
import ConRon.Bridge.Core.Memo

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env}

/-! ## 1. The λ clause: no domain-sort run -/

/-- con-leche: ConLeche/Kernel/Core.lean:1328-1349 inferBodyIO — the io λ
clause's **chain rule**.  Note what is NOT here: `inferBody`'s
`r.whnf (← r.infer ty)` domain-sort run.  Official's `infer_lambda` skips it
at `infer_only`, and the P row never consumed it. -/
theorem inferIO_lam_chain {F d : Nat} {ty body bt : Expr} {mb : BinderMeta}
    {pwI : PropWhen} (hg : mode.betaGate = true)
    (hb : ConLeche.inferTypeIO mode env F (d + 1)
      (body.instantiate1 (.fvar d ty)) = .ok bt)
    (hv : mode.verifiedChecks = true) (hpw : body.lamPw = some pwI)
    (hz : (mb.pw == pwI) = true) :
    ConLeche.inferTypeIO mode env (F + 1) d (.lam ty body mb) =
      .ok (.forallE ty (bt.abstract1 d) mb) := by
  rw [ConLeche.inferTypeIO_succ, if_pos hg]
  simp only [ConLeche.inferBodyIO, CoreFns.ioView, ConLeche.inferTypeIO_def,
    hb, hv, hpw, hz, bind, Except.bind, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1340-1348 inferBodyIO — the io λ
clause's **innermost binder**: the codomain-sort validation stays (it is what
makes the λ datum trustworthy), and at this grade its own inference is the io
one too. -/
theorem inferIO_lam_leaf {F d : Nat} {ty body bt btt : Expr}
    {mb : BinderMeta} {vb : Level} (hg : mode.betaGate = true)
    (hb : ConLeche.inferTypeIO mode env F (d + 1)
      (body.instantiate1 (.fvar d ty)) = .ok bt)
    (hv : mode.verifiedChecks = true) (hpw : body.lamPw = none)
    (hbtt : ConLeche.inferTypeIO mode env F (d + 1) bt = .ok btt)
    (hvb : ConLeche.whnf mode env F (d + 1) btt = .ok (.sort vb))
    (hz : (Level.zeronessOf vb == mb.pw) = true) :
    ConLeche.inferTypeIO mode env (F + 1) d (.lam ty body mb) =
      .ok (.forallE ty (bt.abstract1 d) mb) := by
  rw [ConLeche.inferTypeIO_succ, if_pos hg]
  simp only [ConLeche.inferBodyIO, CoreFns.ioView, ConLeche.inferTypeIO_def,
    ConLeche.ensureSort, ConLeche.whnf_def, hb, hv, hpw, hbtt, hvb, hz, bind,
    Except.bind, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1328-1349 inferBodyIO — the io λ
clause at a mode that runs no TT-lane check. -/
theorem inferIO_lam_trusted {F d : Nat} {ty body bt : Expr}
    {mb : BinderMeta} (hg : mode.betaGate = true)
    (hb : ConLeche.inferTypeIO mode env F (d + 1)
      (body.instantiate1 (.fvar d ty)) = .ok bt)
    (hv : mode.verifiedChecks = false) :
    ConLeche.inferTypeIO mode env (F + 1) d (.lam ty body mb) =
      .ok (.forallE ty (bt.abstract1 d) mb) := by
  rw [ConLeche.inferTypeIO_succ, if_pos hg]
  simp only [ConLeche.inferBodyIO, CoreFns.ioView, ConLeche.inferTypeIO_def,
    hb, hv, bind, Except.bind, Bool.false_eq_true, if_false, pure,
    Except.pure]

/-! ## 2. The application clause: **the io site** -/

/-- con-leche: ConLeche/Kernel/Core.lean:1350-1373 inferBodyIO — **the io
site**: at a ∀ whose validated datum is `never` the per-argument certificate
is dead weight (the premise-form io claim derives the membership from the
subject's own `WellDenoted` app slot), so it is skipped.  The READ IS THE
DATUM ALONE — con-leche's licence ruling of 2026-09-06 — which is why no
`mode` conjunct appears. -/
theorem inferIO_app_licensed {F d : Nat} {f a tf ty body : Expr}
    {mt : BinderMeta} (hg : mode.betaGate = true)
    (hf : ConLeche.inferTypeIO mode env F d f = .ok tf)
    (hw : ConLeche.whnf mode env F d tf = .ok (.forallE ty body mt))
    (hlic : mt.pw.isNever = true) :
    ConLeche.inferTypeIO mode env (F + 1) d (.app f a) =
      .ok (body.instantiate1 a) := by
  rw [ConLeche.inferTypeIO_succ, if_pos hg]
  simp only [ConLeche.inferBodyIO, CoreFns.ioView, ConLeche.inferTypeIO_def,
    ConLeche.whnf_def, hf, hw, hlic, bind, Except.bind, pure, Except.pure]
  simp

/-- con-leche: ConLeche/Kernel/Core.lean:1368-1372 inferBodyIO — the
application clause at a **possibly-zero** datum: the certificate runs
unconditionally.  The squash regime's membership is model-class-wide
unrecoverable, and that fence is absolute. -/
theorem inferIO_app_cert {F d : Nat} {f a tf ty body ta : Expr}
    {mt : BinderMeta} (hg : mode.betaGate = true)
    (hf : ConLeche.inferTypeIO mode env F d f = .ok tf)
    (hw : ConLeche.whnf mode env F d tf = .ok (.forallE ty body mt))
    (hlic : mt.pw.isNever = false)
    (hta : ConLeche.inferTypeIO mode env F d a = .ok ta)
    (hde : ConLeche.isDefEqCore mode env F d ta ty = .ok true) :
    ConLeche.inferTypeIO mode env (F + 1) d (.app f a) =
      .ok (body.instantiate1 a) := by
  rw [ConLeche.inferTypeIO_succ, if_pos hg]
  simp only [ConLeche.inferBodyIO, CoreFns.ioView, ConLeche.inferTypeIO_def,
    ConLeche.whnf_def, ConLeche.defeq_def, hf, hw, hlic, hta, hde, bind,
    Except.bind, Bool.false_eq_true, if_false, pure, Except.pure]
  simp

/-! ## 3. The body theorem -/

/-- con-leche: ConLeche/Verify/Cached/DiscC5.lean inferBodyIOC_sim —
**THEOREM 1 for `inferBodyIO`**.

**OPEN** (task #97-P3-Core), and for the same reasons as `inferBody_spec`:
the twin's io `.app` clause is the batched `inferSpineIO`/`inferAppIOAt`
(task #97-P6-9) and its `.proj` clause needs the same three callee rules.
The io lane keeps CHAINED binder clauses — con-leche's `inferBodyIOI` does
(task #97-P6-12's own note), so `infer_lam_open`/`_cod`/`_result` survive as
this lane's λ clause and the batched-telescope debt of `Infer.lean` does NOT
apply here. -/
theorem inferBodyIO_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hg : mode.betaGate = true) (hsim : KnotSpec mode env fe fuel) :
    BodySpec mode env fe
      (inferBodyIO mode (CoreFnsA.ioView (coreKnot mode fe id fuel)) fe)
      (ConLeche.inferTypeIO mode env) := by
  sorry

end ConRon.Bridge.Core

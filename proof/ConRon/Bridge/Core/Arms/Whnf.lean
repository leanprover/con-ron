/-
# `ConRon.Bridge.Core.Arms.Whnf` — Theorem 1 for `whnfBody`

DESIGN §8.2, rule 8's inventory for `ConLeche/Kernel/Core.lean:1073-1099`
(`whnfStep`, `whnfLoop`, `whnfBody`).  This body is the smallest of the six:
a LOOP, not a dispatch, so the inventory is three exits of one iteration plus
the entry bracket.

| clause | exit | lemma |
|---|---|---|
| `whnfStep` | literal acceleration fires | `whnfLoop_reduceNat` |
| `whnfStep` | a definition unfolds | `whnfLoop_delta` |
| `whnfStep` | neither — the reduct is the head normal form | `whnfLoop_done` |
| `whnfBody` | the entry at `whnfLoopFuel` | `whnf_of_loop` |
| the five values | the wrapper's stuck tag | `Bridge/Core/Memo.lean`'s `whnf_of_stuck` |

**The loop is `whnfLoopFuel` deep and the knot is one level.**  That is
con-leche's own task #106 shape and the arena copies it verbatim (task #97c:
"`whnfLoopFuel` and `whnfLoopFuel` are con-leche's numbers verbatim"), so the
twin's induction is on the LOOP's budget with the knot record fixed — one
`Nat` induction, not a second fuel tower.  `whnfBody_spec` below is where it
runs.
-/
import ConRon.Bridge.Core.Memo

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env}

/-! ## 1. One iteration of the reduction loop -/

/-- con-leche: ConLeche/Kernel/Core.lean:1080-1082 whnfStep — **literal
acceleration**: the head normal form is a `Nat` constructor application the
`reduceNat` pass packs back into a literal, and the loop continues on the
packed form. -/
theorem whnfLoop_reduceNat {F d n : Nat} {e e₁ e₂ res : Expr}
    (h1 : ConLeche.whnfCore mode env F d e = .ok e₁)
    (h2 : ConLeche.reduceNat (ConLeche.pureFns mode env F) env d e₁
      = .ok (some e₂))
    (hk : ConLeche.whnfLoop (ConLeche.pureFns mode env F) env d n e₂
      = .ok res) :
    ConLeche.whnfLoop (ConLeche.pureFns mode env F) env d (n + 1) e
      = .ok res := by
  rw [ConLeche.whnfLoop, ConLeche.whnfStep]
  simp only [ConLeche.whnfCore_def, h1, h2, bind, Except.bind]
  exact hk

/-- con-leche: ConLeche/Kernel/Core.lean:1083-1085 whnfStep — **the delta
step**: the head is an unfoldable constant, and the loop continues on the
unfolding. -/
theorem whnfLoop_delta {F d n : Nat} {e e₁ e₂ res : Expr}
    (h1 : ConLeche.whnfCore mode env F d e = .ok e₁)
    (h2 : ConLeche.reduceNat (ConLeche.pureFns mode env F) env d e₁
      = .ok none)
    (h3 : ConLeche.unfoldDefinition env e₁ = some e₂)
    (hk : ConLeche.whnfLoop (ConLeche.pureFns mode env F) env d n e₂
      = .ok res) :
    ConLeche.whnfLoop (ConLeche.pureFns mode env F) env d (n + 1) e
      = .ok res := by
  rw [ConLeche.whnfLoop, ConLeche.whnfStep]
  simp only [ConLeche.whnfCore_def, h1, h2, h3, bind, Except.bind]
  exact hk

/-- con-leche: ConLeche/Kernel/Core.lean:1086 whnfStep — **the loop's exit**:
nothing further reduces, so the `whnfCore` reduct is the answer. -/
theorem whnfLoop_done {F d n : Nat} {e e₁ : Expr}
    (h1 : ConLeche.whnfCore mode env F d e = .ok e₁)
    (h2 : ConLeche.reduceNat (ConLeche.pureFns mode env F) env d e₁
      = .ok none)
    (h3 : ConLeche.unfoldDefinition env e₁ = none) :
    ConLeche.whnfLoop (ConLeche.pureFns mode env F) env d (n + 1) e
      = .ok e₁ := by
  rw [ConLeche.whnfLoop, ConLeche.whnfStep]
  simp only [ConLeche.whnfCore_def, h1, h2, h3, bind, Except.bind, pure,
    Except.pure]

/-! ## 2. The entry bracket -/

/-- con-leche: ConLeche/Kernel/Core.lean:1097-1099 whnfBody — the body IS the
loop at its own budget, so the entry is one rewrite.  This is the lemma the
twin's `whnfBody` theorem ends on. -/
theorem whnf_of_loop {F d : Nat} {e res : Expr}
    (h : ConLeche.whnfLoop (ConLeche.pureFns mode env F) env d
      ConLeche.whnfLoopFuel e = .ok res) :
    ConLeche.whnf mode env (F + 1) d e = .ok res := by
  rw [ConLeche.whnf_succ, ConLeche.whnfBody]
  exact h

/-! ## 3. The body theorem -/

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean whnfBodyC_sim — **THEOREM 1
for `whnfBody`**.

**OPEN** (task #97-P3-Core).  What is missing is one `Nat` induction on the
loop's budget over the three step lemmas above, plus two callee rules that
are `Arena/Core.lean` walks and not knot slots: `reduceNat` (which re-enters
the `whnf` slot at its literal arguments) and `unfoldDefinition` (which is
pure but reads `fe`, so its rule is an `IFEnvOK` consequence rather than a
`BodySpec`).  Neither is hard; neither was reached this round. -/
theorem whnfBody_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) :
    BodySpec mode env fe (whnfBody (coreKnot mode fe id fuel) fe)
      (ConLeche.whnf mode env) := by
  sorry

end ConRon.Bridge.Core

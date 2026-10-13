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
import ConRon.Bridge.Core.Walks.Owed
import ConRon.Bridge.Core.Walks.Mono
import ConRon.Bridge.Core.Walks.Nat
import ConRon.Bridge.Frame

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env}

/-! ## 1. One iteration of the reduction loop -/

/-- con-leche: ConLeche/Kernel/Core.lean:1120-1121 whnfStep — **literal
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

/-- con-leche: ConLeche/Kernel/Core.lean:1123-1124 whnfStep — **the delta
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

/-- con-leche: ConLeche/Kernel/Core.lean:1125 whnfStep — **the loop's exit**:
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

/-! ### The three iterations with their fuels merged (task #120)

The same three step lemmas, each from the three runs a verification
condition has — one `∃ F` per callee — with the `max` merge inside, so that an
arm is closed by `bridge_frame [...]` instead of a hand-written merge.  And the
two inversions of an OPTIONAL answer (`denoteEO`) the loop's callees return. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1120-1121 whnfStep — the literal
acceleration, fuels merged. -/
theorem whnfLoop_reduceNat_ex {F₁ F₂ F₃ d n : Nat} {e e₁ e₂ res : Expr}
    (h1 : ConLeche.whnfCore mode env F₁ d e = .ok e₁)
    (h2 : ConLeche.reduceNat (ConLeche.pureFns mode env F₂) env d e₁ = .ok (some e₂))
    (hk : ConLeche.whnfLoop (ConLeche.pureFns mode env F₃) env d n e₂ = .ok res) :
    ∃ F, ConLeche.whnfLoop (ConLeche.pureFns mode env F) env d (n + 1) e = .ok res :=
  ⟨max F₁ (max F₂ F₃), whnfLoop_reduceNat
    (ConLeche.whnfCore_mono (Nat.le_max_left _ _) h1)
    (reduceNatFueled_mono
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) h2)
    (whnfLoopFueled_mono
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hk)⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1123-1124 whnfStep — the delta step,
fuels merged. -/
theorem whnfLoop_delta_ex {F₁ F₂ F₃ d n : Nat} {e e₁ e₂ res : Expr}
    (h1 : ConLeche.whnfCore mode env F₁ d e = .ok e₁)
    (h2 : ConLeche.reduceNat (ConLeche.pureFns mode env F₂) env d e₁ = .ok none)
    (h3 : ConLeche.unfoldDefinition env e₁ = some e₂)
    (hk : ConLeche.whnfLoop (ConLeche.pureFns mode env F₃) env d n e₂ = .ok res) :
    ∃ F, ConLeche.whnfLoop (ConLeche.pureFns mode env F) env d (n + 1) e = .ok res :=
  ⟨max F₁ (max F₂ F₃), whnfLoop_delta
    (ConLeche.whnfCore_mono (Nat.le_max_left _ _) h1)
    (reduceNatFueled_mono
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) h2)
    h3
    (whnfLoopFueled_mono
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hk)⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1125 whnfStep — the loop's exit,
fuels merged. -/
theorem whnfLoop_done_ex {F₁ F₂ d n : Nat} {e e₁ : Expr}
    (h1 : ConLeche.whnfCore mode env F₁ d e = .ok e₁)
    (h2 : ConLeche.reduceNat (ConLeche.pureFns mode env F₂) env d e₁ = .ok none)
    (h3 : ConLeche.unfoldDefinition env e₁ = none) :
    ∃ F, ConLeche.whnfLoop (ConLeche.pureFns mode env F) env d (n + 1) e = .ok e₁ :=
  ⟨max F₁ F₂, whnfLoop_done
    (ConLeche.whnfCore_mono (Nat.le_max_left _ _) h1)
    (reduceNatFueled_mono (Nat.le_max_right _ _) h2) h3⟩

/-! ## 2. The entry bracket -/

/-- con-leche: ConLeche/Kernel/Core.lean:1134-1136 whnfBody — the body IS the
loop at its own budget, so the entry is one rewrite.  This is the lemma the
twin's `whnfBody` theorem ends on. -/
theorem whnf_of_loop {F d : Nat} {e res : Expr}
    (h : ConLeche.whnfLoop (ConLeche.pureFns mode env F) env d
      ConLeche.whnfLoopFuel e = .ok res) :
    ConLeche.whnf mode env (F + 1) d e = .ok res := by
  rw [ConLeche.whnf_succ, ConLeche.whnfBody]
  exact h

/-! ## 3. The loop, by induction on its budget (task #97-P3-Core-2)

The three step lemmas above are about con-leche's loop; this is the twin's,
and the two meet in `whnfBody_spec`.  Two things make it work that did not
exist before this round:

* **the fuel merge** (`Bridge/Core/Walks/Mono.lean`).  Each iteration hands
  out its own `∃ F` — one from `KnotSpec.whnfCore`, one from `reduceNat`, one
  from the induction hypothesis — and the three have to become one before a
  step lemma can apply.  `Verify/Mono.lean`'s `whnfCore_mono`, this tier's
  `reduceNatFueled_mono` and its `whnfLoopFueled_mono` are the three lifts,
  and `max` is the merge.  DESIGN §8's `### Task #97-P3-CoreWalks` §6.1 named
  this as the tier's one unpriced line item and this is where it is spent;
* **`ConRon.Arena.whnfLoopFuel = ConLeche.whnfLoopFuel`** — task #97c twinned
  con-leche's number verbatim, but con-leche SEALS it, so the equation needs
  one `unseal`.

`whnfLoop_spec` stands on two walk theorems, both CLOSED in task
#97-P3-Core round 4: `reduceNat_spec` (`Bridge/Core/Walks/Nat.lean`) and
`unfoldDefinition_spec` (`Bridge/Core/Walks/Spine.lean`, over
`Walks/Cached.lean`'s `constValAt_spec'`).  The second needed `EnvWF env`
(the unfolding's scope is `unfoldDefinition_WScoped`'s, whose hypothesis it
is), so the loop takes it too; `whnfBody_spec` always did. -/

unseal ConLeche.whnfLoopFuel in
/-- con-leche: ConLeche/Kernel/Core.lean:1101-1108 whnfLoopFuel — the two
budgets are the same number (task #97c).  con-leche's is `@[irreducible]`,
so the equation needs an `unseal`; the arena's is a plain `def`. -/
theorem whnfLoopFuel_eq :
    ConRon.Arena.whnfLoopFuel = ConLeche.whnfLoopFuel := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1127-1132 whnfLoop — **THEOREM 1 for
the reduction LOOP**, at an arbitrary step budget: one `Nat` induction over
§1's three step lemmas, with the fuel merge at every iteration. -/
theorem whnfLoop_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hsim : KnotSpec mode env fe fuel) :
    ∀ (n : Nat) (s₀ : AState) (d : Nat) (i : EIdx),
      CheckOK mode env fe s₀ →
      (∃ e, denoteE s₀.store i = some e ∧ Expr.WScoped d e) →
      ⦃fun s => s = s₀⦄
        ConRon.Arena.whnfLoop (coreKnot mode fe id fuel) fe d n i
      ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧
          ∀ e, denoteE s₀.store i = some e →
            ∃ v, denoteE s'.store r = some v ∧ Expr.WScoped d v ∧
              ∃ F, ConLeche.whnfLoop (ConLeche.pureFns mode env F) env d n e
                = .ok v; ⊤⦄ := by
  intro n
  induction n with
  | zero =>
    intro s₀ d i _ _
    vcgen [ConRon.Arena.whnfLoop]
  | succ n ih =>
    intro s₀ d i hok hdw
    obtain ⟨e, hden, hw⟩ := hdw
    have hwc := hsim.whnfCore (c := false) (e := e)
    have hud := unfoldDefinition_spec (mode := mode) (fe := fe) henv (d := d)
    vcgen [ConRon.Arena.whnfLoop, ConRon.Arena.whnfStep,
      hwc, reduceNat_spec hsim, hud, ih]
    all_goals (bridge_peel; subst_vars)
    -- every exit: the three iterations' fuels merged by the `_ex` lemmas
    bridge_auto [whnfLoop_reduceNat_ex, whnfLoop_delta_ex, whnfLoop_done_ex]

/-! ## 4. The body theorem -/

/-- con-leche: ConLeche/Kernel/Core.lean:1134-1136 whnfBody — the loop's
answer at the twin's budget is a `whnf` answer (`whnf_of_loop` with the
budgets' equation, in the shape `bridge_auto` concludes). -/
theorem SimE.of_whnfLoop {st : EStore} {r : EIdx} {d F : Nat} {e v : Expr}
    (h : denoteE st r = some v) (hw : Expr.WScoped d v)
    (hF : ConLeche.whnfLoop (ConLeche.pureFns mode env F) env d
      ConRon.Arena.whnfLoopFuel e = .ok v) :
    SimE (ConLeche.whnf mode env) d e st r := by
  rw [whnfLoopFuel_eq] at hF
  exact ⟨v, h, hw, F + 1, whnf_of_loop hF⟩

/-- con-leche: ConLeche/Verify/Cached/DiscC4.lean whnfBodyC_sim — **THEOREM 1
for `whnfBody`**.

**PROVED** (task #97-P3-Core-2) and **SORRY-FREE** since task #97-P3-Core
round 4: `whnfLoop_spec` above is the `Nat` induction, `whnfLoopFuel_eq` is
the entry, and `whnf_of_loop` is the bracket; the two walks it stood on
(`reduceNat_spec`, `unfoldDefinition_spec`) are closed.  The first of the six
bodies at `[propext, Classical.choice, Quot.sound]`. -/
theorem whnfBody_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (_hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) :
    BodySpec mode env fe (whnfBody (coreKnot mode fe id fuel) fe)
      (ConLeche.whnf mode env) := by
  intro s₀ d i e hok hden hw
  have hloop := whnfLoop_spec henv hsim
  vcgen [ConRon.Arena.whnfBody, hloop]
  all_goals (bridge_peel; subst_vars)
  -- the loop's answer, through the entry bracket
  bridge_auto [SimE.of_whnfLoop]

/-! ## 5. The axiom census -/

section Census

#print axioms whnfLoop_reduceNat
#print axioms whnfLoop_delta
#print axioms whnfLoop_done
#print axioms whnf_of_loop
#print axioms whnfLoopFuel_eq
/-! `whnfLoop_spec` and `whnfBody_spec`: no `sorryAx` since round 4. -/
#print axioms whnfLoop_spec
#print axioms whnfBody_spec

end Census

end ConRon.Bridge.Core

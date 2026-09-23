/-
# `ConRon.Bridge.Core.Arms.Defeq` — Theorem 1 for `defeqBody`

DESIGN §8.2, rule 8's inventory for `ConLeche/Kernel/Core.lean:1461-1719`
(`defeqStep`, `defeqLoop`, `defeqBody`).  This is the largest of the six
bodies — a LOOP whose step has twenty-five exits — and the only one whose
twin carries a clause con-leche has no cached-tier counterpart for: **the
batched binder descent** (task #97-P6-14), licensed as a port-side lever by
the maintainer's ruling before DESIGN §8.7, "with its own identification
lemma against the pure tier's chained arms owed by the bridge (P3)".

That lemma is `defeqPeel_chain` below, and this module is where the debt is
paid or recorded.

## The step's exits

| group | exit | lemma |
|---|---|---|
| entry | the syntactic fast path `a == b` | `defeqLoop_syntactic` |
| entry | the eq-true shortcut (con-leche's audit E2) | `defeqLoop_boolTrue` |
| entry | the `whnfCore` pair is syntactically equal | `defeqLoop_whnf_eq` |
| entry | proof irrelevance (hoisted, D3/D4) | `defeqLoop_propIrrel` |
| literals | `reduceNat` fires on the left / on the right | `defeqLoop_reduceNat_left`, `_right` |
| lazy delta | one-sided, hint-ordered, same-head congruence, both | OWED (§5) |
| congruence | `∀`/`∀` and `λ`/`λ` — the **peeled** arms | `defeqLoop_forallE`, `defeqLoop_lam` |
| congruence | sort, lit, fvar, const, app, proj, the literal/ctor pairs, η | OWED (§5) |
| the loop | `defeqBody` at `defeqLoopFuel` | `defeq_of_loop` |

## What makes the binder arms special

They are the arms the twin does NOT run clause for clause.  `defeqPeel` holds
the two raw bodies and the `k` free variables it has introduced, opens each
domain against them in ONE `instantiate_list` and compares it where the chain
compares it; `defeqPeelLeaf` opens the two residuals once and hands the pair
back to the knot; `defeqPeelDone` raises the innermost annotation mismatch on
the way out.  Two equality short-circuits ride with it (the peel returns at
`a.eq2 b`; the domain's knot call is skipped when the two raw domains are the
same handle, 87.7 % of peeled levels).

The identification argument is written out on `Arena/Core.lean`'s `defeqPeel`
and restated as `defeqPeel_chain`'s doc comment below; its four parts are the
opens' agreement by `Expr.instantiateList_cons`, the five facts that make the
chain REACH this arm at every peeled level, the innermost-first order of the
annotation test, and the memo/fuel accounting.
-/
import ConRon.Bridge.Core.Memo

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env}

/-! ## 1. The loop's entry bracket -/

/-- con-leche: ConLeche/Kernel/Core.lean:1716-1719 defeqBody — the body IS
the lazy-delta loop at its own budget, entered with the entry flag `pi` set
(con-leche's audit D3: `pi` is what makes proof irrelevance run once per
`is_def_eq_core` entry and not once per delta step). -/
theorem defeq_of_loop {F d : Nat} {a b : Expr} {r : Bool}
    (h : ConLeche.defeqLoop mode (ConLeche.pureFns mode env F) env d
      ConLeche.defeqLoopFuel true a b = .ok r) :
    ConLeche.isDefEqCore mode env (F + 1) d a b = .ok r := by
  rw [ConLeche.isDefEqCore_succ, ConLeche.defeqBody]
  exact h

/-! ## 2. The step's four entry exits -/

/-- con-leche: ConLeche/Kernel/Core.lean:1463-1464 defeqStep — **the
syntactic fast path**, the references' most-hit branch. -/
theorem defeqLoop_syntactic {F d n : Nat} {pi : Bool} {a b : Expr}
    (h : (a == b) = true) :
    ConLeche.defeqLoop mode (ConLeche.pureFns mode env F) env d (n + 1) pi a b
      = .ok true := by
  rw [ConLeche.defeqLoop, ConLeche.defeqStep]
  simp only [h, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1465-1470 defeqStep — **the eq-true
shortcut** (the divergence audit's E2): the right side is `Bool.true`, the
left is free-variable-free, and its head normal form is `Bool.true`. -/
theorem defeqLoop_boolTrue {F d n : Nat} {pi : Bool} {a b : Expr}
    (hab : (a == b) = false)
    (hsc : (if pi && b.isBoolTrue && !a.hasFvar then
        ConLeche.boolTrueShortcut (ConLeche.pureFns mode env F) d a
      else pure false) = (.ok true : CheckM Bool)) :
    ConLeche.defeqLoop mode (ConLeche.pureFns mode env F) env d (n + 1) pi a b
      = .ok true := by
  rw [ConLeche.defeqLoop, ConLeche.defeqStep]
  simp only [hab, Bool.false_eq_true, if_false]
  rw [hsc]
  simp only [bind, Except.bind, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1471-1474 defeqStep — the two head
normal forms are **syntactically equal**. -/
theorem defeqLoop_whnf_eq {F d n : Nat} {pi : Bool} {a b a' b' : Expr}
    (hab : (a == b) = false)
    (hsc : (if pi && b.isBoolTrue && !a.hasFvar then
        ConLeche.boolTrueShortcut (ConLeche.pureFns mode env F) d a
      else pure false) = (.ok false : CheckM Bool))
    (ha : ConLeche.whnfCore mode env F d a = .ok a')
    (hb : ConLeche.whnfCore mode env F d b = .ok b')
    (heq : (a' == b') = true) :
    ConLeche.defeqLoop mode (ConLeche.pureFns mode env F) env d (n + 1) pi a b
      = .ok true := by
  rw [ConLeche.defeqLoop, ConLeche.defeqStep]
  simp only [hab, Bool.false_eq_true, if_false]
  rw [hsc]
  simp only [ConLeche.whnfCore_def, ha, hb, heq, bind, Except.bind, if_true,
    pure, Except.pure]
  simp

/-- con-leche: ConLeche/Kernel/Core.lean:1475-1499 defeqStep — **proof
irrelevance**, hoisted before lazy delta exactly as in the official kernel and
run once per entry (D3), never on a pair `quick_is_def_eq` decides itself
(D4). -/
theorem defeqLoop_propIrrel {F d n : Nat} {pi : Bool} {a b a' b' : Expr}
    (hab : (a == b) = false)
    (hsc : (if pi && b.isBoolTrue && !a.hasFvar then
        ConLeche.boolTrueShortcut (ConLeche.pureFns mode env F) d a
      else pure false) = (.ok false : CheckM Bool))
    (ha : ConLeche.whnfCore mode env F d a = .ok a')
    (hb : ConLeche.whnfCore mode env F d b = .ok b')
    (heq : (a' == b') = false)
    (hpi : (if pi && !a'.quickPair b' then
        ConLeche.propIrrel (ConLeche.pureFns mode env F) env d a' b'
      else pure false) = (.ok true : CheckM Bool)) :
    ConLeche.defeqLoop mode (ConLeche.pureFns mode env F) env d (n + 1) pi a b
      = .ok true := by
  rw [ConLeche.defeqLoop, ConLeche.defeqStep]
  simp only [hab, Bool.false_eq_true, if_false]
  rw [hsc]
  simp only [bind, Except.bind, Bool.false_eq_true, if_false,
    ConLeche.whnfCore_def, ha, hb, heq]
  rw [hpi]
  simp only [bind, Except.bind, if_true, pure, Except.pure]

/-! ## 3. Literal acceleration

Both sides free-variable-free is the official kernel's own guard
(`lazy_delta_reduction`'s `(!has_fvar(t_n) && !has_fvar(s_n))`), and
DESIGN's reduction-strategy ruling forbids dropping it: unguarded folding
delta-grinds an open `Int32`/`Int64` pair toward `2^31` unary `succ` steps. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1517-1521 defeqStep — `reduceNat`
fires on the **left** and the loop re-enters at the entry flag. -/
theorem defeqLoop_reduceNat_left {F d n : Nat} {pi : Bool}
    {a b a' b' a₂ : Expr} {r : Bool}
    (hab : (a == b) = false)
    (hsc : (if pi && b.isBoolTrue && !a.hasFvar then
        ConLeche.boolTrueShortcut (ConLeche.pureFns mode env F) d a
      else pure false) = (.ok false : CheckM Bool))
    (ha : ConLeche.whnfCore mode env F d a = .ok a')
    (hb : ConLeche.whnfCore mode env F d b = .ok b')
    (heq : (a' == b') = false)
    (hpi : (if pi && !a'.quickPair b' then
        ConLeche.propIrrel (ConLeche.pureFns mode env F) env d a' b'
      else pure false) = (.ok false : CheckM Bool))
    (hn : (if !a'.hasFvar && !b'.hasFvar then
        ConLeche.reduceNat (ConLeche.pureFns mode env F) env d a'
      else pure none) = (.ok (some a₂) : CheckM (Option Expr)))
    (hk : ConLeche.defeqLoop mode (ConLeche.pureFns mode env F) env d n true
      a₂ b' = .ok r) :
    ConLeche.defeqLoop mode (ConLeche.pureFns mode env F) env d (n + 1) pi a b
      = .ok r := by
  rw [ConLeche.defeqLoop, ConLeche.defeqStep]
  simp only [hab, Bool.false_eq_true, if_false]
  rw [hsc]
  simp only [bind, Except.bind, Bool.false_eq_true, if_false,
    ConLeche.whnfCore_def, ha, hb, heq]
  rw [hpi]
  simp only [bind, Except.bind, Bool.false_eq_true, if_false]
  rw [hn]
  simp only [bind, Except.bind]
  exact hk

/-- con-leche: ConLeche/Kernel/Core.lean:1522-1525 defeqStep — `reduceNat`
fires on the **right**. -/
theorem defeqLoop_reduceNat_right {F d n : Nat} {pi : Bool}
    {a b a' b' b₂ : Expr} {r : Bool}
    (hab : (a == b) = false)
    (hsc : (if pi && b.isBoolTrue && !a.hasFvar then
        ConLeche.boolTrueShortcut (ConLeche.pureFns mode env F) d a
      else pure false) = (.ok false : CheckM Bool))
    (ha : ConLeche.whnfCore mode env F d a = .ok a')
    (hb : ConLeche.whnfCore mode env F d b = .ok b')
    (heq : (a' == b') = false)
    (hpi : (if pi && !a'.quickPair b' then
        ConLeche.propIrrel (ConLeche.pureFns mode env F) env d a' b'
      else pure false) = (.ok false : CheckM Bool))
    (hn1 : (if !a'.hasFvar && !b'.hasFvar then
        ConLeche.reduceNat (ConLeche.pureFns mode env F) env d a'
      else pure none) = (.ok none : CheckM (Option Expr)))
    (hn2 : (if !a'.hasFvar && !b'.hasFvar then
        ConLeche.reduceNat (ConLeche.pureFns mode env F) env d b'
      else pure none) = (.ok (some b₂) : CheckM (Option Expr)))
    (hk : ConLeche.defeqLoop mode (ConLeche.pureFns mode env F) env d n true
      a' b₂ = .ok r) :
    ConLeche.defeqLoop mode (ConLeche.pureFns mode env F) env d (n + 1) pi a b
      = .ok r := by
  rw [ConLeche.defeqLoop, ConLeche.defeqStep]
  simp only [hab, Bool.false_eq_true, if_false]
  rw [hsc]
  simp only [bind, Except.bind, Bool.false_eq_true, if_false,
    ConLeche.whnfCore_def, ha, hb, heq]
  rw [hpi]
  simp only [bind, Except.bind, Bool.false_eq_true, if_false]
  rw [hn1]
  simp only [bind, Except.bind]
  rw [hn2]
  simp only [bind, Except.bind]
  exact hk

/-! ## 4. The binder-congruence arms — what the peel replaces

A `∀`/`∀` (or `λ`/`λ`) pair reaches this arm through five facts about the
earlier ones, and those five are exactly what the twin's batched descent has
to reproduce at EVERY peeled level (the ruling's identification obligation):

1. `whnfCore` is the identity on a binder (its first six clauses), so `a'`
   and `b'` are the binders themselves;
2. `isBoolTrue` of a binder is `false`, so the eq-true shortcut does not
   fire;
3. `quickPair` is `true` on a `∀`/`∀` and a `λ`/`λ` pair, so proof
   irrelevance is skipped (D4);
4. `reduceNat`'s match needs an `.app`, so literal acceleration answers
   `none`;
5. `unfoldableHead` reads `getAppFn`, which is the binder itself, so lazy
   delta answers `false, false`.

The two lemmas below are the arm as the chain runs it; `defeqPeel_chain` is
the statement that the twin's batched descent agrees with iterating them. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1636-1654 defeqStep — the `∀`/`∀`
congruence: the domains, then the bodies opened at ONE free variable (the
second domain's, which is the chain's own choice), then — LAST, and only at
the verified modes — the two prop-ness data (con-leche's task #161: only a
pair that is otherwise definitionally equal can reach the test, so a firing
mismatch is exactly the cross-provenance coherence corner). -/
theorem defeqLoop_forallE {F d n : Nat} {pi : Bool} {a b : Expr}
    {ty₁ body₁ ty₂ body₂ : Expr} {m₁ m₂ : BinderMeta}
    (hab : (a == b) = false)
    (hsc : (if pi && b.isBoolTrue && !a.hasFvar then
        ConLeche.boolTrueShortcut (ConLeche.pureFns mode env F) d a
      else pure false) = (.ok false : CheckM Bool))
    (ha : ConLeche.whnfCore mode env F d a = .ok (.forallE ty₁ body₁ m₁))
    (hb : ConLeche.whnfCore mode env F d b = .ok (.forallE ty₂ body₂ m₂))
    (heq : ((Expr.forallE ty₁ body₁ m₁) == .forallE ty₂ body₂ m₂) = false)
    (hd1 : ConLeche.isDefEqCore mode env F d ty₁ ty₂ = .ok true)
    (hd2 : ConLeche.isDefEqCore mode env F (d + 1)
      (body₁.instantiate1 (.fvar d ty₂)) (body₂.instantiate1 (.fvar d ty₂))
      = .ok true)
    (hm : (mode.verifiedChecks && !(m₁.pw == m₂.pw)) = false) :
    ConLeche.defeqLoop mode (ConLeche.pureFns mode env F) env d (n + 1) pi a b
      = .ok true := by
  rw [ConLeche.defeqLoop, ConLeche.defeqStep]
  simp only [hab, Bool.false_eq_true, if_false]
  rw [hsc]
  simp [ConLeche.whnfCore_def, ConLeche.defeq_def, ha, hb, heq,
    ConLeche.Expr.quickPair, ConLeche.reduceNat, ConLeche.unfoldableHead,
    ConLeche.unfoldDefinition, ConLeche.Expr.getAppFn, hd1, hd2, hm, bind,
    Except.bind, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1655-1662 defeqStep — the `λ`/`λ`
congruence, the same clause at the other binder. -/
theorem defeqLoop_lam {F d n : Nat} {pi : Bool} {a b : Expr}
    {ty₁ body₁ ty₂ body₂ : Expr} {m₁ m₂ : BinderMeta}
    (hab : (a == b) = false)
    (hsc : (if pi && b.isBoolTrue && !a.hasFvar then
        ConLeche.boolTrueShortcut (ConLeche.pureFns mode env F) d a
      else pure false) = (.ok false : CheckM Bool))
    (ha : ConLeche.whnfCore mode env F d a = .ok (.lam ty₁ body₁ m₁))
    (hb : ConLeche.whnfCore mode env F d b = .ok (.lam ty₂ body₂ m₂))
    (heq : ((Expr.lam ty₁ body₁ m₁) == .lam ty₂ body₂ m₂) = false)
    (hd1 : ConLeche.isDefEqCore mode env F d ty₁ ty₂ = .ok true)
    (hd2 : ConLeche.isDefEqCore mode env F (d + 1)
      (body₁.instantiate1 (.fvar d ty₂)) (body₂.instantiate1 (.fvar d ty₂))
      = .ok true)
    (hm : (mode.verifiedChecks && !(m₁.pw == m₂.pw)) = false) :
    ConLeche.defeqLoop mode (ConLeche.pureFns mode env F) env d (n + 1) pi a b
      = .ok true := by
  rw [ConLeche.defeqLoop, ConLeche.defeqStep]
  simp only [hab, Bool.false_eq_true, if_false]
  rw [hsc]
  simp [ConLeche.whnfCore_def, ConLeche.defeq_def, ha, hb, heq,
    ConLeche.Expr.quickPair, ConLeche.reduceNat, ConLeche.unfoldableHead,
    ConLeche.unfoldDefinition, ConLeche.Expr.getAppFn, hd1, hd2, hm, bind,
    Except.bind, pure, Except.pure]

/-! ## 5. The peel's identification — the campaign's one port-side debt -/

/-- con-leche: none — **OPEN** (task #97-P3-Core), and it is the one
obligation in this tier that con-leche has NO lemma for: task #97-P6-14's
batched defeq binder descent is the arena's own algorithm
(`Arena/Core.lean`'s `defeqPeel` / `defeqPeelLeaf` / `defeqPeelDone`),
licensed as a port-side lever by the maintainer's ruling before DESIGN §8.7
with "its own identification lemma against the pure tier's chained arms owed
by the bridge (P3)".

**The argument, from the loop's doc comment**, in four parts:

1. **The opens agree.**  The peel accumulates the `k` free variables it has
   introduced and opens each domain against them in one `instantiateList`;
   the chain opens one binder at a time with `instantiate1`.  The two are the
   same term by `Expr.instantiateList_cons` (`ConLeche/Verify/InstList.lean`),
   which is the equation the `instantiate1` ruling already made the bridge
   owe once (task #97-P6-9) and which `Bridge/ExprOps/Inst1.lean` states as
   `instantiateList_spec` — still `sorry` there, so this lemma inherits that
   gap as well as its own.
2. **The chain REACHES this arm at every peeled level.**  §4's five facts,
   each one clause of `defeqStep`'s earlier arms: `whnfCore` is the identity
   on a binder, `isBoolTrue` is `false`, `quickPair` is `true`, `reduceNat`
   answers `none`, `unfoldableHead` answers `false`.  So the chain's run
   between two peeled levels is exactly one `defeqStep` and nothing else,
   which is what makes the loop's budget accounting in part 4 finite.
3. **A failure lands at the same binder.**  The annotation test is
   innermost-first in the chain (it runs after both recursive calls
   succeed), and the peel carries the mismatch outward in two scalars
   (`mism`, `mismLam`) so that `defeqPeelDone` raises it at the same binder
   the chain would.  The two equality short-circuits are verdict-neutral:
   `a.eq2 b` is the chain's own syntactic fast path, and skipping the
   domain's knot call at two identical raw handles is that path one level
   down (`denoteE` is injective, DESIGN §8.3, so equal handles are equal
   terms).
4. **The caches see less and the fuel is existential.**  The peel enters the
   `defeq` memo once per telescope where the chain enters it once per binder,
   so every row the peel writes the chain would also have written; and
   Theorem 1's pure side is `∃ F`, so the chain's larger fuel is free.

What is missing to CLOSE it is part 1's callee rule and a `Nat` induction on
the peel's `k`; nothing in the argument is open. -/
theorem defeqPeel_chain {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (ty1 body1 ty2 body2 : EIdx)
    (m1 m2 : BinderMeta) (isLam : Bool) (t1 b1 t2 b2 : Expr)
    (hok : CheckOK mode env fe s₀)
    (ht1 : denoteE s₀.store ty1 = some t1)
    (hb1 : denoteE s₀.store body1 = some b1)
    (ht2 : denoteE s₀.store ty2 = some t2)
    (hb2 : denoteE s₀.store body2 = some b2)
    (hwa : Expr.WScoped d (if isLam then .lam t1 b1 m1 else .forallE t1 b1 m1))
    (hwb : Expr.WScoped d
      (if isLam then .lam t2 b2 m2 else .forallE t2 b2 m2)) :
    ⦃fun s => ⌜s = s₀⌝⦄
      defeqBinders mode (coreKnot mode fe id fuel) d ty1 body1 m1 ty2 body2 m2
        isLam
    ⦃⇓? x s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        SimV (ConLeche.isDefEqCore mode env) d
          (if isLam then .lam t1 b1 m1 else .forallE t1 b1 m1)
          (if isLam then .lam t2 b2 m2 else .forallE t2 b2 m2) x⌝⦄ := by
  sorry

/-! ## 6. The loop, skeletonised (task #97-P3-Core round 5)

`defeqBody_spec` below is proved from ONE child, `defeqStep_spec`: the twin's
`defeqStep` at an arbitrary continuation `k`, against con-leche's
`defeqLoop … (n + 1)`, under the hypothesis that `k` refines
`defeqLoop … n`.  `defeqLoop_spec` is the `Nat` induction over it
(`Arms/Whnf.lean`'s `whnfLoop_spec` is the template), and the entry bracket
is `defeq_of_loop`.  Every `sorry` of the `defeq` body is therefore the step's:
`defeqPeel_chain` above and the five certificate walks of `Walks/Owed.lean`
are its callee rules.

The step's subjects arrive as the loop's own reducts (a `reduceNat` answer,
an unfolding), so the step and the loop take their denotations in answer
shape: ∃ in the precondition, ∀ in the postcondition. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1703-1708 defeqLoop — what a
continuation of the lazy-delta loop at budget `n` promises: the frame, and
con-leche's loop at `n` on every denotation of the two subjects. -/
def DefeqLoopK (mode : CheckMode) (env : Env) (fe : IFEnv) (d n : Nat)
    (k : Bool → EIdx → EIdx → AM Bool) : Prop :=
  ∀ (pi : Bool) (a b : EIdx) (s₀ : AState),
    CheckOK mode env fe s₀ →
    (∃ x, denoteE s₀.store a = some x ∧ Expr.WScoped d x) →
    (∃ y, denoteE s₀.store b = some y ∧ Expr.WScoped d y) →
    ⦃fun s => ⌜s = s₀⌝⦄ k pi a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ x y, denoteE s₀.store a = some x → denoteE s₀.store b = some y →
          ∃ F, ConLeche.defeqLoop mode (ConLeche.pureFns mode env F) env d n
            pi x y = .ok r⌝⦄

/-- con-leche: ConLeche/Kernel/Core.lean:1461-1701 defeqStep — **THEOREM 1
for one step of the lazy-delta loop**, at a continuation that refines the
loop one budget down.

**OPEN** — the `defeq` body's whole content: the entry group (§2's four
exits, `isBoolTrue_spec`, `hasFvarFast`, `boolTrueShortcut`, two
`KnotSpec.whnfCore'`, `propIrrel_spec'`), the literal group
(`reduceNat_spec`, §2's two), lazy delta (`unfoldableHead_spec`,
`unfoldDefinition_spec`, `headHint_spec`, `sameConstHeads_spec`,
`defeqSpine_spec`, all CLOSED in `Walks/Spine.lean`), and the congruence
group (`lvlEq?`/`lvlsEq?`, `strLitToConstructor`, `defeqPeel_chain`,
`defEqList_spec`, `etaCert_spec`, `stuckIrrel_spec`). -/
theorem defeqStep_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) (d n : Nat)
    (k : Bool → EIdx → EIdx → AM Bool) (hk : DefeqLoopK mode env fe d n k) :
    DefeqLoopK mode env fe d (n + 1)
      (defeqStep mode (coreKnot mode fe id fuel) fe d k) := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1703-1708 defeqLoop — **THEOREM 1
for the lazy-delta LOOP**, at every budget: the `Nat` induction over
`defeqStep_spec`. -/
theorem defeqLoop_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) (d : Nat) :
    ∀ n, DefeqLoopK mode env fe d n
      (ConRon.Arena.defeqLoop mode (coreKnot mode fe id fuel) fe d n) := by
  intro n
  induction n with
  | zero =>
    intro pi a b s₀ _ _ _
    mvcgen [ConRon.Arena.defeqLoop]
    exact fun h => h.elim
  | succ n ih =>
    exact defeqStep_spec henv hμ hsim d n _ ih

unseal ConLeche.defeqLoopFuel in
/-- con-leche: ConLeche/Kernel/Core.lean:1710-1714 defeqLoopFuel — the two
budgets are the same number (task #97c); con-leche's is `@[irreducible]`. -/
theorem defeqLoopFuel_eq :
    ConRon.Arena.defeqLoopFuel = ConLeche.defeqLoopFuel := rfl

/-! ## 7. The body theorem -/

/-- con-leche: ConLeche/Verify/Cached/DiscC6.lean defeqBodyC_sim — **THEOREM 1
for `defeqBody`**.

**OPEN** (task #97-P3-Core).  What is missing, beyond `defeqPeel_chain`: the
lazy-delta group's four exits and the congruence group's remaining eleven,
whose step lemmas are mechanical in the shape of §2's and §4's but which this
round did not reach; and the callee rules for `propIrrel`, `stuckIrrel`,
`etaCert`, `defeqSpine` and `defEqList` — five `Arena/Core.lean` walks that
are not knot slots.  The eight step lemmas above are closed. -/
theorem defeqBody_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) :
    BodySpecV mode env fe (defeqBody mode (coreKnot mode fe id fuel) fe)
      (ConLeche.isDefEqCore mode env) := by
  intro s₀ d i j a b hok hda hdb hwa hwb
  have hloop := defeqLoop_spec henv hμ hsim d ConRon.Arena.defeqLoopFuel true
    i j s₀ hok ⟨a, hda, hwa⟩ ⟨b, hdb, hwb⟩
  mvcgen [ConRon.Arena.defeqBody, hloop]
  intro hck hx hp hres
  obtain ⟨F, hF⟩ := hres a b hda hdb
  rw [defeqLoopFuel_eq] at hF
  exact ⟨hck, hx, hp, F + 1, defeq_of_loop hF⟩

end ConRon.Bridge.Core

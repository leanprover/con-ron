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
import ConRon.Bridge.Core.Walks.PropRead
import ConRon.Bridge.Core.Walks.Guards
import ConRon.Bridge.ExprOps.Ranges

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

/-! ## 6. The step's pure side, staged (task #97-P3-Core round 5)

`defeqStep_spec` is proved stage by stage (§8), and every stage names a
pure fact at SOME fuel.  Merging a dozen fuel existentials with `max` at each
of the step's twenty-five exits is what `Walks/Mono.lean`'s `merge2` does for
two; here the facts are carried in the **eventually** form `Ev` instead —
"from some fuel on" — which is closed under conjunction for free, and one
`Ev.exists` at the exit picks the fuel.  Each stage turns its callee's `∃ F`
into `Ev` by the callee's own monotonicity lemma.

The prefix of `defeqStep` that every exit past the literal group has run is
`DqPre`; `defeqLoop_tail` rewrites the loop at such a prefix to `dqTail`, a
copy of con-leche's lazy-delta-and-congruence tail as a function of the two
head normal forms, and `dqCongr` is the congruence half of it.  Both are
stated by `rfl` against con-leche's `defeqStep`, so the copies cannot drift:
a change upstream breaks `defeqLoop_tail`'s proof, not its meaning. -/

/-- con-leche: none — **eventually at every fuel**: `p` holds from some fuel
on.  The fuel-monotone facts of the pure tier are exactly the ones that can
be put in this form, and two of them combine with no arithmetic at the use
site. -/
def Ev (p : Nat → Prop) : Prop := ∃ F₀, ∀ F, F₀ ≤ F → p F

/-- con-leche: none — `Ev` is closed under conjunction. -/
theorem Ev.and {p q : Nat → Prop} (hp : Ev p) (hq : Ev q) :
    Ev (fun F => p F ∧ q F) := by
  obtain ⟨F₁, h₁⟩ := hp
  obtain ⟨F₂, h₂⟩ := hq
  exact ⟨max F₁ F₂, fun F hF =>
    ⟨h₁ F (Nat.le_trans (Nat.le_max_left _ _) hF),
     h₂ F (Nat.le_trans (Nat.le_max_right _ _) hF)⟩⟩

/-- con-leche: none — a fuel-free fact holds eventually. -/
theorem Ev.const {P : Prop} (h : P) : Ev (fun _ => P) := ⟨0, fun _ _ => h⟩

/-- con-leche: none — the consequence rule of `Ev`. -/
theorem Ev.imp {p q : Nat → Prop} (hp : Ev p) (h : ∀ F, p F → q F) : Ev q := by
  obtain ⟨F₀, h₀⟩ := hp
  exact ⟨F₀, fun F hF => h F (h₀ F hF)⟩

/-- con-leche: ConLeche/Verify/Mono.lean:158 isDefEqCore_mono — **the
entry into `Ev`**: a fuel-monotone fact that holds at some fuel holds
eventually. -/
theorem Ev.of_mono {p : Nat → Prop} (hm : ∀ {f f' : Nat}, f ≤ f' → p f → p f')
    (h : ∃ F, p F) : Ev p := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, fun F' h' => hm h' hF⟩

/-- con-leche: none — **the exit from `Ev`**: the fuel the exit names. -/
theorem Ev.exists {p : Nat → Prop} (h : Ev p) : ∃ F, p F := by
  obtain ⟨F₀, h₀⟩ := h
  exact ⟨F₀, h₀ F₀ (Nat.le_refl _)⟩

end ConRon.Bridge.Core

/- The two copies are written with con-leche's names alone in scope: the
arena twin has a function of the same name for most of them. -/
namespace ConRon.Bridge.Core

open ConLeche

set_option autoImplicit false

section Copies

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- con-leche: ConLeche/Kernel/Core.lean:1579-1701 defeqStep — **the
congruence half of the step's tail**, the `match a', b' with` block
verbatim, as a function of the two head normal forms.  `defeqLoop_tail`
identifies it with the step by `rfl`. -/
def dqCongr (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (a' b' : Expr) : m Bool :=
    match a', b' with
    | .sort u, .sort v => liftFueled "level comparison" (Level.isEquiv u v)
    | .lit l₁, .lit l₂ => pure (l₁ == l₂)
    | .lit (.natVal n), .const c us =>
      if c = natZeroName ∧ us = [] then pure (n == 0)
      else stuckIrrel mode r env depth (.lit (.natVal n)) (.const c us)
    | .const c us, .lit (.natVal n) =>
      if c = natZeroName ∧ us = [] then pure (n == 0)
      else stuckIrrel mode r env depth (.const c us) (.lit (.natVal n))
    | .lit (.natVal nn), .app f x =>
      match nn, f with
      | k + 1, .const c [] =>
        if c = natSuccName then r.defeq depth (.lit (.natVal k)) x
        else stuckIrrel mode r env depth (.lit (.natVal nn)) (.app f x)
      | _, _ => stuckIrrel mode r env depth (.lit (.natVal nn)) (.app f x)
    | .app f x, .lit (.natVal nn) =>
      match nn, f with
      | k + 1, .const c [] =>
        if c = natSuccName then r.defeq depth x (.lit (.natVal k))
        else stuckIrrel mode r env depth (.app f x) (.lit (.natVal nn))
      | _, _ => stuckIrrel mode r env depth (.app f x) (.lit (.natVal nn))
    | .lit (.strVal st), .app (.const cO usO) x =>
      if cO = stringOfListName ∧ usO = [] ∧ strLitSupported env then
        r.defeq depth (strLitToConstructor st) (.app (.const cO usO) x)
      else
        stuckIrrel mode r env depth (.lit (.strVal st)) (.app (.const cO usO) x)
    | .app (.const cO usO) x, .lit (.strVal st) =>
      if cO = stringOfListName ∧ usO = [] ∧ strLitSupported env then
        r.defeq depth (.app (.const cO usO) x) (strLitToConstructor st)
      else
        stuckIrrel mode r env depth (.app (.const cO usO) x) (.lit (.strVal st))
    | .fvar i ty₁, .fvar j ty₂ =>
      if i == j then pure true
      else stuckIrrel mode r env depth (.fvar i ty₁) (.fvar j ty₂)
    | .const n us, .const n' us' => do
      if n = n' then
        if ← liftFueled "level comparison" (Level.isEquivList us us') then
          pure true
        else stuckIrrel mode r env depth (.const n us) (.const n' us')
      else stuckIrrel mode r env depth (.const n us) (.const n' us')
    | .forallE ty₁ body₁ m₁, .forallE ty₂ body₂ m₂ => do
      unless ← r.defeq depth ty₁ ty₂ do return false
      unless ← r.defeq (depth + 1)
          (body₁.instantiate1 (.fvar depth ty₂))
          (body₂.instantiate1 (.fvar depth ty₂)) do return false
      if mode.verifiedChecks && !(m₁.pw == m₂.pw) then
        throw (.notImplemented "sort-annotation mismatch (defeq-forall)")
      pure true
    | .lam ty₁ body₁ m₁, .lam ty₂ body₂ m₂ => do
      unless ← r.defeq depth ty₁ ty₂ do return false
      unless ← r.defeq (depth + 1)
          (body₁.instantiate1 (.fvar depth ty₂))
          (body₂.instantiate1 (.fvar depth ty₂)) do return false
      if mode.verifiedChecks && !(m₁.pw == m₂.pw) then
        throw (.notImplemented "sort-annotation mismatch (defeq-lam)")
      pure true
    | .app f₁ a₁, .app f₂ a₂ => do
      if (Expr.app f₁ a₁).getAppArgs.length =
          (Expr.app f₂ a₂).getAppArgs.length then
        if ← r.defeq depth (Expr.app f₁ a₁).getAppFn
            (Expr.app f₂ a₂).getAppFn then
          if ← defEqList r env depth (Expr.app f₁ a₁).getAppArgs
              (Expr.app f₂ a₂).getAppArgs then pure true
          else stuckIrrel mode r env depth (.app f₁ a₁) (.app f₂ a₂)
        else stuckIrrel mode r env depth (.app f₁ a₁) (.app f₂ a₂)
      else stuckIrrel mode r env depth (.app f₁ a₁) (.app f₂ a₂)
    | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ => do
      if s₁ == s₂ && i₁ == i₂ then
        if ← r.defeq depth e₁ e₂ then pure true
        else stuckIrrel mode r env depth (.proj s₁ i₁ e₁) (.proj s₂ i₂ e₂)
      else stuckIrrel mode r env depth (.proj s₁ i₁ e₁) (.proj s₂ i₂ e₂)
    | .lam ty₁ body₁ m₁, b₂ => do
      if ← etaCert mode r env depth ty₁ body₁ m₁ b₂ then pure true
      else stuckIrrel mode r env depth (.lam ty₁ body₁ m₁) b₂
    | a₁, .lam ty₂ body₂ m₂ => do
      if ← etaCert mode r env depth ty₂ body₂ m₂ a₁ then pure true
      else stuckIrrel mode r env depth a₁ (.lam ty₂ body₂ m₂)
    | e₁, e₂ => stuckIrrel mode r env depth e₁ e₂

/-- con-leche: ConLeche/Kernel/Core.lean:1526-1578 defeqStep — **the lazy
delta half of the step's tail** (decision before materialization), with the
congruence half as `dqCongr`. -/
def dqTail (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Bool → Expr → Expr → m Bool) (a' b' : Expr) : m Bool := do
    match unfoldableHead env a', unfoldableHead env b' with
    | true, false =>
      match unfoldDefinition env a' with
      | some a₂ => k false a₂ b'
      | none => pure false
    | false, true =>
      match unfoldDefinition env b' with
      | some b₂ => k false a' b₂
      | none => pure false
    | true, true =>
      let ha := headHint env a'
      let hb := headHint env b'
      if ReducibilityHint.lt hb ha then
        match unfoldDefinition env a' with
        | some a₂ => k false a₂ b'
        | none => pure false
      else if ReducibilityHint.lt ha hb then
        match unfoldDefinition env b' with
        | some b₂ => k false a' b₂
        | none => pure false
      else if ReducibilityHint.sameRegular ha hb && sameConstHeads a' b' then
        if ← defeqSpine r env depth a' b' then pure true
        else
          match unfoldDefinition env a', unfoldDefinition env b' with
          | some a₂, some b₂ => k false a₂ b₂
          | _, _ => pure false
      else
        match unfoldDefinition env a', unfoldDefinition env b' with
        | some a₂, some b₂ => k false a₂ b₂
        | _, _ => pure false
    | false, false => dqCongr mode r env depth a' b'

end Copies

end ConRon.Bridge.Core

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env}

/-- con-leche: ConLeche/Kernel/Core.lean:1461-1525 defeqStep — **the
prefix every exit past the literal group has run**, at one fuel: no
syntactic hit, no eq-true shortcut, the two `whnfCore`s, no syntactic hit on
the reducts, no proof irrelevance, no literal acceleration on either side.
The hypotheses are spelled as con-leche's code spells them (§2's lemmas take
them one by one). -/
structure DqPre (mode : CheckMode) (env : Env) (F d : Nat) (pi : Bool)
    (x y x' y' : Expr) : Prop where
  hab : (x == y) = false
  hsc : (if pi && y.isBoolTrue && !x.hasFvar then
      ConLeche.boolTrueShortcut (ConLeche.pureFns mode env F) d x
    else pure false) = (.ok false : CheckM Bool)
  ha : ConLeche.whnfCore mode env F d x = .ok x'
  hb : ConLeche.whnfCore mode env F d y = .ok y'
  heq : (x' == y') = false
  hpi : (if pi && !x'.quickPair y' then
      ConLeche.propIrrel (ConLeche.pureFns mode env F) env d x' y'
    else pure false) = (.ok false : CheckM Bool)
  hn1 : (if !x'.hasFvar && !y'.hasFvar then
      ConLeche.reduceNat (ConLeche.pureFns mode env F) env d x'
    else pure none) = (.ok none : CheckM (Option Expr))
  hn2 : (if !x'.hasFvar && !y'.hasFvar then
      ConLeche.reduceNat (ConLeche.pureFns mode env F) env d y'
    else pure none) = (.ok none : CheckM (Option Expr))

/-- con-leche: ConLeche/Kernel/Core.lean:1461-1701 defeqStep — **the loop
past the prefix IS the tail**: `defeqStep`'s remaining term, by `rfl` against
the two copies above. -/
theorem defeqLoop_tail {F d n : Nat} {pi : Bool} {x y x' y' : Expr}
    (h : DqPre mode env F d pi x y x' y') :
    ConLeche.defeqLoop mode (ConLeche.pureFns mode env F) env d (n + 1) pi x y
      = dqTail mode (ConLeche.pureFns mode env F) env d
          (ConLeche.defeqLoop mode (ConLeche.pureFns mode env F) env d n)
          x' y' := by
  rw [ConLeche.defeqLoop, ConLeche.defeqStep]
  simp only [h.hab, Bool.false_eq_true, if_false]
  rw [h.hsc]
  simp only [bind, Except.bind, Bool.false_eq_true, if_false,
    ConLeche.whnfCore_def, h.ha, h.hb, h.heq]
  rw [h.hpi]
  simp only [bind, Except.bind, Bool.false_eq_true, if_false]
  rw [h.hn1]
  simp only [bind, Except.bind]
  rw [h.hn2]
  rfl

/-! ### The tail's exits -/

section TailExits

variable {r : CoreFns CheckM} {d : Nat} {k : Bool → Expr → Expr → CheckM Bool}
  {x' y' : Expr}

/-- con-leche: ConLeche/Kernel/Core.lean:1579 defeqStep — neither head
unfolds: the congruence half. -/
theorem dqTail_ff (hua : unfoldableHead env x' = false)
    (hub : unfoldableHead env y' = false) :
    dqTail mode r env d k x' y' = dqCongr mode r env d x' y' := by
  simp only [dqTail, hua, hub]

/-- con-leche: ConLeche/Kernel/Core.lean:1537-1540 defeqStep — only the left
head unfolds. -/
theorem dqTail_tf (hua : unfoldableHead env x' = true)
    (hub : unfoldableHead env y' = false) :
    dqTail mode r env d k x' y' =
      (match unfoldDefinition env x' with
        | some a₂ => k false a₂ y'
        | none => pure false) := by
  simp only [dqTail, hua, hub]

/-- con-leche: ConLeche/Kernel/Core.lean:1541-1544 defeqStep — only the
right head unfolds. -/
theorem dqTail_ft (hua : unfoldableHead env x' = false)
    (hub : unfoldableHead env y' = true) :
    dqTail mode r env d k x' y' =
      (match unfoldDefinition env y' with
        | some b₂ => k false x' b₂
        | none => pure false) := by
  simp only [dqTail, hua, hub]

/-- con-leche: ConLeche/Kernel/Core.lean:1548-1551 defeqStep — both unfold,
the left hint is greater: unfold the left. -/
theorem dqTail_tt_left (hua : unfoldableHead env x' = true)
    (hub : unfoldableHead env y' = true)
    (hlt : ReducibilityHint.lt (headHint env y') (headHint env x') = true) :
    dqTail mode r env d k x' y' =
      (match unfoldDefinition env x' with
        | some a₂ => k false a₂ y'
        | none => pure false) := by
  simp only [dqTail, hua, hub, hlt, if_true]

/-- con-leche: ConLeche/Kernel/Core.lean:1552-1555 defeqStep — both unfold,
the right hint is greater: unfold the right. -/
theorem dqTail_tt_right (hua : unfoldableHead env x' = true)
    (hub : unfoldableHead env y' = true)
    (hlt1 : ReducibilityHint.lt (headHint env y') (headHint env x') = false)
    (hlt2 : ReducibilityHint.lt (headHint env x') (headHint env y') = true) :
    dqTail mode r env d k x' y' =
      (match unfoldDefinition env y' with
        | some b₂ => k false x' b₂
        | none => pure false) := by
  simp only [dqTail, hua, hub, hlt1, hlt2, Bool.false_eq_true, if_false,
    if_true]

/-- con-leche: ConLeche/Kernel/Core.lean:1556-1571 defeqStep — both unfold at
equal regular hints on the same head constant: the spine congruence, then
both unfoldings. -/
theorem dqTail_tt_spine (hua : unfoldableHead env x' = true)
    (hub : unfoldableHead env y' = true)
    (hlt1 : ReducibilityHint.lt (headHint env y') (headHint env x') = false)
    (hlt2 : ReducibilityHint.lt (headHint env x') (headHint env y') = false)
    (hsr : (ReducibilityHint.sameRegular (headHint env x') (headHint env y') &&
      sameConstHeads x' y') = true) :
    dqTail mode r env d k x' y' =
      (do
        if ← defeqSpine r env d x' y' then pure true
        else
          match unfoldDefinition env x', unfoldDefinition env y' with
          | some a₂, some b₂ => k false a₂ b₂
          | _, _ => pure false) := by
  simp only [dqTail, hua, hub, hlt1, hlt2, hsr, Bool.false_eq_true, if_false,
    if_true]

/-- con-leche: ConLeche/Kernel/Core.lean:1572-1575 defeqStep — both unfold,
no order and no shared head: unfold both. -/
theorem dqTail_tt_both (hua : unfoldableHead env x' = true)
    (hub : unfoldableHead env y' = true)
    (hlt1 : ReducibilityHint.lt (headHint env y') (headHint env x') = false)
    (hlt2 : ReducibilityHint.lt (headHint env x') (headHint env y') = false)
    (hsr : (ReducibilityHint.sameRegular (headHint env x') (headHint env y') &&
      sameConstHeads x' y') = false) :
    dqTail mode r env d k x' y' =
      (match unfoldDefinition env x', unfoldDefinition env y' with
        | some a₂, some b₂ => k false a₂ b₂
        | _, _ => pure false) := by
  simp only [dqTail, hua, hub, hlt1, hlt2, hsr, Bool.false_eq_true, if_false]

/-- con-leche: ConLeche/Kernel/Core.lean:1567 defeqStep — the spine
congruence answers `true`. -/
theorem dqTail_tt_spine_true (hua : unfoldableHead env x' = true)
    (hub : unfoldableHead env y' = true)
    (hlt1 : ReducibilityHint.lt (headHint env y') (headHint env x') = false)
    (hlt2 : ReducibilityHint.lt (headHint env x') (headHint env y') = false)
    (hsr : (ReducibilityHint.sameRegular (headHint env x') (headHint env y') &&
      sameConstHeads x' y') = true)
    (hsp : defeqSpine r env d x' y' = .ok true) :
    dqTail mode r env d k x' y' = .ok true := by
  rw [dqTail_tt_spine hua hub hlt1 hlt2 hsr]
  simp only [bind, Except.bind, hsp, if_true]; rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1568-1571 defeqStep — the spine
congruence answers `false`: unfold both. -/
theorem dqTail_tt_spine_false (hua : unfoldableHead env x' = true)
    (hub : unfoldableHead env y' = true)
    (hlt1 : ReducibilityHint.lt (headHint env y') (headHint env x') = false)
    (hlt2 : ReducibilityHint.lt (headHint env x') (headHint env y') = false)
    (hsr : (ReducibilityHint.sameRegular (headHint env x') (headHint env y') &&
      sameConstHeads x' y') = true)
    (hsp : defeqSpine r env d x' y' = .ok false) :
    dqTail mode r env d k x' y' =
      (match unfoldDefinition env x', unfoldDefinition env y' with
        | some a₂, some b₂ => k false a₂ b₂
        | _, _ => pure false) := by
  rw [dqTail_tt_spine hua hub hlt1 hlt2 hsr]
  simp only [bind, Except.bind, hsp, Bool.false_eq_true, if_false]

end TailExits

/-! ## 7. The step's twin side: stage rules

Each stage of §8's staged proof is one of these, or a callee rule from
`Walks/*` applied at a NAMED subject. -/

/-- con-leche: none — `Ev` at the exit: a goal that follows eventually from a
fact that holds eventually holds at some fuel. -/
theorem Ev.finish {P G : Nat → Prop} (hG : Ev (fun F => P F → G F))
    (hP : Ev P) : ∃ F, G F :=
  (Ev.exists (hG.and hP)).imp fun _ h => h.1 h.2

/-- con-leche: none — the frame-and-verdict postcondition every stage of the
step ends in: the state invariant, the store only grown and the pins
untouched since `s₀`, and the pure goal `G` at some fuel. -/
def DqPost (mode : CheckMode) (env : Env) (fe : IFEnv) (s₀ : AState)
    (G : Nat → Bool → Prop) (r : Bool) (s' : AState) : Prop :=
  CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
    ∃ F, G F r

/-- con-leche: none — **a `pure` exit** at a pinned state. -/
theorem triple_pure_post {α : Type} {s₀ : AState} {v : α}
    {Q : α → AState → Prop} (h : Q v s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ (pure v : AM α) ⦃⇓? r s => ⌜Q r s⌝⦄ := by
  mvcgen
  subst_vars; exact h

/-- con-leche: none — **a join point**: the do-compiler's
`if c then x >>= jp else y >>= jp` is the bind of the `if`. -/
theorem triple_ite_bind {α β : Type} {c : Prop} [Decidable c] {x y : AM α}
    {f : α → AM β} {s₀ : AState} {R : β → AState → Prop}
    (h : ⦃fun s => ⌜s = s₀⌝⦄ ((if c then x else y) >>= f)
      ⦃⇓? b s => ⌜R b s⌝⦄) :
    ⦃fun s => ⌜s = s₀⌝⦄ (if c then x >>= f else y >>= f)
      ⦃⇓? b s => ⌜R b s⌝⦄ := by
  by_cases hc : c
  · rw [if_pos hc] at h ⊢; exact h
  · rw [if_neg hc] at h ⊢; exact h

/-- con-leche: none — `CheckOK` across a stage that moved nothing but the
memos. -/
theorem _root_.ConRon.Bridge.CheckOK.of_store_eq {mode : CheckMode} {env : Env} {fe : IFEnv}
    {s s' : AState} (h : CheckOK mode env fe s) (hst : s'.store = s.store)
    (hc : s'.caches = s.caches) (hp : s'.pins = s.pins) :
    CheckOK mode env fe s' :=
  h.mono ⟨by rw [hst]; exact h.state.wf⟩ (by rw [hst]; exact Ext.refl _) hc hp

/-- con-leche: ConLeche/Kernel/Core.lean:1406-1418 boolTrueShortcut —
**the eq-true shortcut's guarded call**, both guard outcomes: the twin's
`boolTrueShortcut` is `KnotSpec.whnf` then `isBoolTrue`, con-leche's is
`whnf` then `Expr.isBoolTrue`. -/
theorem boolTrueShortcutIf_spec {fe : IFEnv} {fuel : Nat}
    (hsim : KnotSpec mode env fe fuel) (s₀ : AState) (d : Nat) (a : EIdx)
    (x : Expr) (c : Bool) (hok : CheckOK mode env fe s₀)
    (hx : denoteE s₀.store a = some x) (hwx : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      (if c = true then
        ConRon.Arena.boolTrueShortcut (coreKnot mode fe id fuel) d a
      else pure false)
    ⦃⇓? sc s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Ev (fun F => (if c then
          ConLeche.boolTrueShortcut (ConLeche.pureFns mode env F) d x
          else pure false) = (.ok sc : CheckM Bool))⌝⦄ := by
  cases c
  · simp only [Bool.false_eq_true, if_false]
    exact triple_pure_post ⟨hok, Ext.refl _, rfl, Ev.const rfl⟩
  · simp only [if_true]
    unfold ConRon.Arena.boolTrueShortcut
    refine triple_seq (hsim.whnf s₀ d a x hok hx hwx) ?_
    rintro w s1 ⟨hok1, hx1, hp1, v, hv, _hwv, F1, hF1⟩
    refine triple_mono (isBoolTrue_spec s1 w v hok1 hv) ?_
    rintro sc s2 ⟨hok2, hst2, hp2, rfl⟩
    refine ⟨hok2, by rw [hst2]; exact hx1, hp2.trans hp1, ?_⟩
    refine Ev.of_mono (p := fun F => ConLeche.boolTrueShortcut
      (ConLeche.pureFns mode env F) d x = .ok v.isBoolTrue)
      (fun hle h => boolTrueShortcutFueled_mono hle h) ⟨F1, ?_⟩
    simp only [ConLeche.boolTrueShortcut, ConLeche.whnf_def, hF1, bind,
      Except.bind, pure, Except.pure]

/-- con-leche: none — **the constructor tag of a denotation**: the four tag
bits of a handle are the tag of the expression it denotes. -/
def exprTag : Expr → UInt32
  | .bvar _ => ETag.bvar
  | .fvar _ _ => ETag.fvar
  | .sort _ => ETag.sort
  | .const _ _ => ETag.const
  | .app _ _ => ETag.app
  | .lam _ _ _ => ETag.lam
  | .forallE _ _ _ => ETag.forallE
  | .letE _ _ _ => ETag.letE
  | .lit _ => ETag.lit
  | .proj _ _ _ => ETag.proj

/-- con-leche: none — DESIGN §8.3: a handle's tag is its denotation's. -/
theorem tag_of_denote {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr}
    (hd : denoteE st h = some e) : h.tag = exprTag e := by
  obtain ⟨v, hv⟩ := denoteE_view hd
  rw [EStore.tagOf_of_view hv]
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv hd]; rfl
  | fvar k t => obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv hd; rfl
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv hd; rfl
  | const n us => obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hv hd; rfl
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv hd; rfl
  | lam ty b m => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv hd; rfl
  | forallE ty b m =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv hd; rfl
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv hd; rfl
  | lit l => rw [denote_lit_inv hwf hv hd]; rfl
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv hd; rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:466-471 Expr.quickPair — the
twin's tag test IS con-leche's constructor match. -/
theorem quickPair_denote {st : EStore} (hwf : StoreWF st) {a b : EIdx}
    {x y : Expr} (ha : denoteE st a = some x) (hb : denoteE st b = some y) :
    ConRon.Arena.quickPair a b = x.quickPair y := by
  unfold ConRon.Arena.quickPair
  rw [tag_of_denote hwf ha, tag_of_denote hwf hb]
  cases x <;> cases y <;> rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1500-1516 defeqStep — the literal
guard: the twin's two eager fvar-range reads are con-leche's
`!a'.hasFvar && !b'.hasFvar`. -/
theorem defeqNoFvars_spec {fe : IFEnv} (s₀ : AState) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hx : denoteE s₀.store a = some x)
    (hy : denoteE s₀.store b = some y) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.defeqNoFvars a b
    ⦃⇓? nf s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ nf = (!x.hasFvar && !y.hasFvar)⌝⦄ := by
  unfold ConRon.Arena.defeqNoFvars
  refine triple_seq (ExprOps.hasFvarFast_spec coreWalkFuel s₀ a hok.state
    (by rw [hx]; rfl)) ?_
  rintro hfa s1 ⟨hst1, hc1, hp1, hr1⟩
  have hok1 := hok.of_store_eq hst1 hc1 hp1
  have e1 : hfa = x.hasFvar := hr1 x hx
  subst e1
  cases hxa : x.hasFvar
  · simp only [Bool.false_eq_true, if_false]
    refine triple_seq (ExprOps.hasFvarFast_spec coreWalkFuel s1 b hok1.state
      (by rw [hst1, hy]; rfl)) ?_
    rintro hfb s2 ⟨hst2, hc2, hp2, hr2⟩
    have e2 : hfb = y.hasFvar := hr2 y (by rw [hst1]; exact hy)
    subst e2
    exact triple_pure_post ⟨hok1.of_store_eq hst2 hc2 hp2, hst2.trans hst1,
      hp2.trans hp1, by simp⟩
  · simp only [if_true]
    exact triple_pure_post ⟨hok1, hst1, hp1, by simp⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1517-1525 defeqStep — **the
guarded literal acceleration**, both guard outcomes, in the `SimOOp` shape
with the fuel carried eventually. -/
theorem reduceNatIf_spec {fe : IFEnv} {fuel : Nat}
    (hsim : KnotSpec mode env fe fuel) (s₀ : AState) (d : Nat) (e : EIdx)
    (x : Expr) (c : Bool) (hok : CheckOK mode env fe s₀)
    (hx : denoteE s₀.store e = some x) (hwx : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      (if c = true then
        ConRon.Arena.reduceNat (coreKnot mode fe id fuel) fe d e
      else pure none)
    ⦃⇓? o s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∃ v, denoteEO s'.store o = some v ∧
          (∀ z, v = some z → Expr.WScoped d z) ∧
          Ev (fun F => (if c then
            ConLeche.reduceNat (ConLeche.pureFns mode env F) env d x
            else pure none) = (.ok v : CheckM (Option Expr)))⌝⦄ := by
  cases c
  · simp only [Bool.false_eq_true, if_false]
    exact triple_pure_post ⟨hok, Ext.refl _, rfl, none, rfl,
      (fun _ h => nomatch h), Ev.const rfl⟩
  · simp only [if_true]
    refine triple_mono (reduceNat_spec hsim s₀ d e hok ⟨x, hx, hwx⟩) ?_
    rintro o s1 ⟨hok1, hx1, hp1, hsim1⟩
    obtain ⟨v, hv, hwv, hF⟩ := hsim1 x hx
    exact ⟨hok1, hx1, hp1, v, hv, hwv,
      Ev.of_mono (p := fun F => ConLeche.reduceNat
        (ConLeche.pureFns mode env F) env d x = .ok v)
        (fun hle h => reduceNatFueled_mono hle h) hF⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1475-1499 defeqStep — **the
hoisted proof-irrelevance test's guarded call**, both guard outcomes, over
`propIrrel_spec` (`Walks/PropRead.lean`). -/
theorem propIrrelIf_spec {fe : IFEnv} {fuel : Nat}
    (hsim : KnotSpec mode env fe fuel) (s₀ : AState) (d : Nat) (a b : EIdx)
    (x y : Expr) (c : Bool) (hok : CheckOK mode env fe s₀)
    (hx : denoteE s₀.store a = some x) (hy : denoteE s₀.store b = some y)
    (hwx : Expr.WScoped d x) (hwy : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      (if c = true then
        ConRon.Arena.propIrrel (coreKnot mode fe id fuel) fe d a b
      else pure false)
    ⦃⇓? pir s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Ev (fun F => (if c then
          ConLeche.propIrrel (ConLeche.pureFns mode env F) env d x y
          else pure false) = (.ok pir : CheckM Bool))⌝⦄ := by
  cases c
  · simp only [Bool.false_eq_true, if_false]
    exact triple_pure_post ⟨hok, Ext.refl _, rfl, Ev.const rfl⟩
  · simp only [if_true]
    refine triple_mono (propIrrel_spec hsim s₀ d a b x y hok hx hy hwx hwy) ?_
    rintro pir s1 ⟨hok1, hx1, hp1, hF⟩
    exact ⟨hok1, hx1, hp1, Ev.of_mono (p := fun F => ConLeche.propIrrel
      (ConLeche.pureFns mode env F) env d x y = .ok pir)
      (fun hle h => propIrrelFueled_mono hle h) hF⟩

end ConRon.Bridge.Core

/- The twin's two copies, with the arena's names alone in scope. -/
namespace ConRon.Bridge.Core

open ConRon.Arena

set_option autoImplicit false

/-- con-leche: ConLeche/Kernel/Core.lean:1579-1701 defeqStep — **the twin's
congruence half**, `Arena/Core.lean`'s `match ← view a', ← view b' with`
block verbatim.  `defeqStep_at` meets it by definitional unfolding. -/
def dqCongrA (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (a' b' : EIdx) : AM Bool := do
  match ← view a', ← view b' with
  | .sort u, .sort v => liftFueled "level comparison" (← lvlEq? u v)
  | .lit l₁, .lit l₂ => pure (l₁ == l₂)
  -- a packed literal against a constructor form: compare shape-directed
  | .lit (.natVal n), .const c us => do
    let el ← emptyLevels
    let nz ← pinNatZero
    if c = nz ∧ us = el then pure (n == 0)
    else stuckIrrel mode r fe depth a' b'
  | .const c us, .lit (.natVal n) => do
    let el ← emptyLevels
    let nz ← pinNatZero
    if c = nz ∧ us = el then pure (n == 0)
    else stuckIrrel mode r fe depth a' b'
  | .lit (.natVal nn), .app f x => do
    match nn with
    | k' + 1 => do
      match ← view f with
      | .const c us => do
        let el ← emptyLevels
        let ns ← pinNatSucc
        if c = ns ∧ us = el then do
          let l ← internE (.lit (.natVal k'))
          r.defeq depth l x
        else stuckIrrel mode r fe depth a' b'
      | _ => stuckIrrel mode r fe depth a' b'
    | _ => stuckIrrel mode r fe depth a' b'
  | .app f x, .lit (.natVal nn) => do
    match nn with
    | k' + 1 => do
      match ← view f with
      | .const c us => do
        let el ← emptyLevels
        let ns ← pinNatSucc
        if c = ns ∧ us = el then do
          let l ← internE (.lit (.natVal k'))
          r.defeq depth x l
        else stuckIrrel mode r fe depth a' b'
      | _ => stuckIrrel mode r fe depth a' b'
    | _ => stuckIrrel mode r fe depth a' b'
  -- a string literal against a unary `String.ofList` application
  | .lit (.strVal st), .app fo _ => do
    match ← view fo with
    | .const cO usO => do
      let el ← emptyLevels
      let sl ← pinStringOfList
      if cO = sl ∧ usO = el ∧ (← strLitSupported fe) then do
        let c ← strLitToConstructor st
        r.defeq depth c b'
      else stuckIrrel mode r fe depth a' b'
    | _ => stuckIrrel mode r fe depth a' b'
  | .app fo _, .lit (.strVal st) => do
    match ← view fo with
    | .const cO usO => do
      let el ← emptyLevels
      let sl ← pinStringOfList
      if cO = sl ∧ usO = el ∧ (← strLitSupported fe) then do
        let c ← strLitToConstructor st
        r.defeq depth a' c
      else stuckIrrel mode r fe depth a' b'
    | _ => stuckIrrel mode r fe depth a' b'
  | .fvar i _, .fvar j _ =>
    if i == j then pure true else stuckIrrel mode r fe depth a' b'
  | .const n us, .const n' us' => do
    if n = n' then do
      if ← liftFueled "level comparison" (← lvlsEq? us us') then pure true
      else stuckIrrel mode r fe depth a' b'
    else stuckIrrel mode r fe depth a' b'
  -- binder congruence, BATCHED (task #97-P6-14); the annotation comparison
  -- runs LAST, innermost binder first
  | .forallE ty₁ body₁ m₁, .forallE ty₂ body₂ m₂ =>
    defeqBinders mode r depth ty₁ body₁ m₁ ty₂ body₂ m₂ false
  | .lam ty₁ body₁ m₁, .lam ty₂ body₂ m₂ =>
    defeqBinders mode r depth ty₁ body₁ m₁ ty₂ body₂ m₂ true
  | .app _ _, .app _ _ => do
    -- stuck applications: **spine-wise** congruence (official's
    -- `is_def_eq_app`), never a recursion on the partial applications
    let aa ← getAppArgs coreWalkFuel a'
    let bb ← getAppArgs coreWalkFuel b'
    if aa.length = bb.length then do
      let fa ← getAppFn coreWalkFuel a'
      let fb ← getAppFn coreWalkFuel b'
      if ← r.defeq depth fa fb then do
        if ← defEqList r fe depth aa bb then pure true
        else stuckIrrel mode r fe depth a' b'
      else stuckIrrel mode r fe depth a' b'
    else stuckIrrel mode r fe depth a' b'
  | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ => do
    if s₁ == s₂ && i₁ == i₂ then do
      if ← r.defeq depth e₁ e₂ then pure true
      else stuckIrrel mode r fe depth a' b'
    else stuckIrrel mode r fe depth a' b'
  -- one-sided λ: eta, else the stuck fallbacks
  | .lam ty₁ body₁ m₁, _ => do
    if ← etaCert mode r fe depth ty₁ body₁ m₁ b' then pure true
    else stuckIrrel mode r fe depth a' b'
  | _, .lam ty₂ body₂ m₂ => do
    if ← etaCert mode r fe depth ty₂ body₂ m₂ a' then pure true
    else stuckIrrel mode r fe depth a' b'
  -- distinct whnf-stuck head symbols
  | _, _ => stuckIrrel mode r fe depth a' b'

/-- con-leche: ConLeche/Kernel/Core.lean:1526-1578 defeqStep — **the twin's
lazy-delta half**, verbatim, with the congruence half as `dqCongrA`. -/
def dqTailA (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (k : Bool → EIdx → EIdx → AM Bool) (a' b' : EIdx) : AM Bool := do
  let ua ← unfoldableHead fe a'
  let ub ← unfoldableHead fe b'
  match ua, ub with
  | true, false =>
    match ← unfoldDefinition fe a' with
    | some a₂ => k false a₂ b'
    | none => pure false
  | false, true =>
    match ← unfoldDefinition fe b' with
    | some b₂ => k false a' b₂
    | none => pure false
  | true, true => do
    let ha ← headHint fe a'
    let hb ← headHint fe b'
    if ConLeche.ReducibilityHint.lt hb ha then
      match ← unfoldDefinition fe a' with
      | some a₂ => k false a₂ b'
      | none => pure false
    else if ConLeche.ReducibilityHint.lt ha hb then
      match ← unfoldDefinition fe b' with
      | some b₂ => k false a' b₂
      | none => pure false
    else if ConLeche.ReducibilityHint.sameRegular ha hb && (← sameConstHeads a' b') then do
      -- same constant at equal *regular* hints: cheap congruence first
      if ← defeqSpine r fe depth a' b' then pure true
      else
        match ← unfoldDefinition fe a', ← unfoldDefinition fe b' with
        | some a₂, some b₂ => k false a₂ b₂
        | _, _ => pure false
    else
      match ← unfoldDefinition fe a', ← unfoldDefinition fe b' with
      | some a₂, some b₂ => k false a₂ b₂
      | _, _ => pure false
  | false, false => dqCongrA mode r fe depth a' b'

end ConRon.Bridge.Core

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env}

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


/-! ### The exits, once

Every exit of the step's tail ends in one of four programs — a `pure`
verdict, the continuation `k`, a knot `defeq`, or the stuck fallback — and
each is proved here once, at an arbitrary pure goal `G` that follows
eventually from the exit's own pure run. -/

/-- con-leche: none — **a `pure` verdict** at the end of a stage. -/
theorem dq_pure_exit {fe : IFEnv} {s₀ s : AState} {G : Nat → Bool → Prop}
    {v : Bool} (hok : CheckOK mode env fe s) (hxs : Ext s₀.store s.store)
    (hps : s.pins = s₀.pins) (hG : Ev (fun F => G F v)) :
    ⦃fun s' => ⌜s' = s⌝⦄ (pure v : AM Bool)
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ :=
  triple_pure_post ⟨hok, hxs, hps, hG.exists⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1703-1708 defeqLoop — **the
continuation**: one more lap of the loop, at the budget below. -/
theorem dq_k_exit {fe : IFEnv} {d n : Nat}
    {k : Bool → EIdx → EIdx → AM Bool} (hk : DefeqLoopK mode env fe d n k)
    {s₀ s : AState} {G : Nat → Bool → Prop} (pi : Bool) (p q : EIdx)
    (u w : Expr) (hok : CheckOK mode env fe s) (hxs : Ext s₀.store s.store)
    (hps : s.pins = s₀.pins) (hp : denoteE s.store p = some u)
    (hq : denoteE s.store q = some w) (hwu : Expr.WScoped d u)
    (hww : Expr.WScoped d w)
    (hG : Ev (fun F => ∀ r, ConLeche.defeqLoop mode
      (ConLeche.pureFns mode env F) env d n pi u w = .ok r → G F r)) :
    ⦃fun s' => ⌜s' = s⌝⦄ k pi p q
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ := by
  refine triple_mono (hk pi p q s hok ⟨u, hp, hwu⟩ ⟨w, hq, hww⟩) ?_
  rintro r s' ⟨hok', hx', hp', hr⟩
  exact ⟨hok', hxs.trans hx', hp'.trans hps,
    Ev.finish (hG.imp fun _ h => h r)
      (Ev.of_mono (fun hle h => defeqLoopFueled_mono hle h) (hr u w hp hq))⟩

/-- con-leche: ConLeche/Kernel/TypeChecker.lean isDefEqCore — **a knot
`defeq`** as the verdict. -/
theorem dq_defeq_exit {fe : IFEnv} {fuel d : Nat}
    (hsim : KnotSpec mode env fe fuel) {s₀ s : AState}
    {G : Nat → Bool → Prop} (p q : EIdx) (u w : Expr)
    (hok : CheckOK mode env fe s) (hxs : Ext s₀.store s.store)
    (hps : s.pins = s₀.pins) (hp : denoteE s.store p = some u)
    (hq : denoteE s.store q = some w) (hwu : Expr.WScoped d u)
    (hww : Expr.WScoped d w)
    (hG : Ev (fun F => ∀ r, ConLeche.isDefEqCore mode env F d u w = .ok r →
      G F r)) :
    ⦃fun s' => ⌜s' = s⌝⦄ (coreKnot mode fe id fuel).defeq d p q
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ := by
  refine triple_mono (hsim.defeq s d p q u w hok hp hq hwu hww) ?_
  rintro r s' ⟨hok', hx', hp', hr⟩
  exact ⟨hok', hxs.trans hx', hp'.trans hps,
    Ev.finish (hG.imp fun _ h => h r)
      (Ev.of_mono (fun hle h => ConLeche.isDefEqCore_mono hle h) hr)⟩

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — **the stuck
fallback** as the verdict, over `stuckIrrel_spec` (`Walks/Owed.lean`,
OPEN).  The one call site of that rule in this module. -/
theorem dq_stuck_exit {fe : IFEnv} {fuel d : Nat}
    (hsim : KnotSpec mode env fe fuel) {s₀ s : AState}
    {G : Nat → Bool → Prop} (p q : EIdx) (u w : Expr)
    (hok : CheckOK mode env fe s) (hxs : Ext s₀.store s.store)
    (hps : s.pins = s₀.pins) (hp : denoteE s.store p = some u)
    (hq : denoteE s.store q = some w) (hwu : Expr.WScoped d u)
    (hww : Expr.WScoped d w)
    (hG : Ev (fun F => ∀ r, ConLeche.stuckIrrel mode
      (ConLeche.pureFns mode env F) env d u w = .ok r → G F r)) :
    ⦃fun s' => ⌜s' = s⌝⦄
      ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d p q
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ := by
  refine triple_mono (stuckIrrel_spec hsim s d p q u w hok hp hq hwu hww) ?_
  rintro r s' ⟨hok', hx', hp', hr⟩
  exact ⟨hok', hxs.trans hx', hp'.trans hps,
    Ev.finish (hG.imp fun _ h => h r)
      (Ev.of_mono (fun hle h => stuckIrrelFueled_mono hle h) hr)⟩

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:145-155 unfoldDefinition — **an
unfolding and what follows it**: `unfoldDefinition` at a named subject, its
answer handed on with its denotation. -/
theorem dq_unfold_seq {fe : IFEnv} {d : Nat} (henv : ConLeche.EnvWF env)
    {s₀ s : AState} {G : Nat → Bool → Prop} (e : EIdx) (u : Expr)
    (f : Option EIdx → AM Bool)
    (hok : CheckOK mode env fe s) (he : denoteE s.store e = some u)
    (hwu : Expr.WScoped d u)
    (hsome : ∀ (s' : AState) (e₂ : EIdx) (u₂ : Expr),
      CheckOK mode env fe s' → Ext s.store s'.store → s'.pins = s.pins →
      denoteE s'.store e₂ = some u₂ → Expr.WScoped d u₂ →
      unfoldDefinition env u = some u₂ →
      ⦃fun t => ⌜t = s'⌝⦄ f (some e₂) ⦃⇓? r t => ⌜DqPost mode env fe s₀ G r t⌝⦄)
    (hnone : ∀ (s' : AState), CheckOK mode env fe s' →
      Ext s.store s'.store → s'.pins = s.pins →
      unfoldDefinition env u = none →
      ⦃fun t => ⌜t = s'⌝⦄ f none ⦃⇓? r t => ⌜DqPost mode env fe s₀ G r t⌝⦄) :
    ⦃fun t => ⌜t = s⌝⦄ (ConRon.Arena.unfoldDefinition fe e >>= f)
    ⦃⇓? r t => ⌜DqPost mode env fe s₀ G r t⌝⦄ := by
  refine triple_seq (unfoldDefinition_spec henv s d e hok ⟨u, he, hwu⟩) ?_
  rintro o s1 ⟨hok1, hx1, hp1, ho⟩
  obtain ⟨hdo, hwo⟩ := ho u he
  cases o with
  | some e₂ =>
    obtain ⟨u₂, hu₂, hd₂⟩ := denoteEO_some_inv hdo
    exact hsome s1 e₂ u₂ hok1 hx1 hp1 hd₂ (hwo u₂ hu₂) hu₂
  | none =>
    exact hnone s1 hok1 hx1 hp1 (denoteEO_none_inv hdo)


/-! ### The tail -/

/-- con-leche: ConLeche/Kernel/Core.lean:1579-1701 defeqStep — **the
congruence half**, at head normal forms that neither unfold. -/
theorem dqCongrA_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) (d : Nat)
    (s₀ s₁ : AState) (a' b' : EIdx) (x' y' : Expr)
    (hok : CheckOK mode env fe s₁) (hx₁ : Ext s₀.store s₁.store)
    (hp₁ : s₁.pins = s₀.pins)
    (hx : denoteE s₁.store a' = some x') (hy : denoteE s₁.store b' = some y')
    (hwx : Expr.WScoped d x') (hwy : Expr.WScoped d y')
    (G : Nat → Bool → Prop)
    (hG : Ev (fun F => ∀ r, dqCongr mode (ConLeche.pureFns mode env F) env d
      x' y' = .ok r → G F r)) :
    ⦃fun s => ⌜s = s₁⌝⦄ dqCongrA mode (coreKnot mode fe id fuel) fe d a' b'
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1568-1575 defeqStep — **both sides
unfold**, then `k` on the two unfoldings or `false`. -/
theorem dq_both_exit {fe : IFEnv} {d n : Nat} (henv : ConLeche.EnvWF env)
    {k : Bool → EIdx → EIdx → AM Bool} (hk : DefeqLoopK mode env fe d n k)
    {s₀ s : AState} {G : Nat → Bool → Prop} (a' b' : EIdx) (x' y' : Expr)
    (hok : CheckOK mode env fe s) (hxs : Ext s₀.store s.store)
    (hps : s.pins = s₀.pins)
    (hx : denoteE s.store a' = some x') (hy : denoteE s.store b' = some y')
    (hwx : Expr.WScoped d x') (hwy : Expr.WScoped d y')
    (hG : Ev (fun F => ∀ r, (match unfoldDefinition env x',
        unfoldDefinition env y' with
      | some a₂, some b₂ => ConLeche.defeqLoop mode
          (ConLeche.pureFns mode env F) env d n false a₂ b₂
      | _, _ => pure false) = .ok r → G F r)) :
    ⦃fun t => ⌜t = s⌝⦄
      (do
        let o1 ← ConRon.Arena.unfoldDefinition fe a'
        let o2 ← ConRon.Arena.unfoldDefinition fe b'
        match o1, o2 with
        | some a₂, some b₂ => k false a₂ b₂
        | _, _ => pure false)
    ⦃⇓? r t => ⌜DqPost mode env fe s₀ G r t⌝⦄ := by
  refine dq_unfold_seq henv a' x' _ hok hx hwx ?_ ?_
  · intro s1 e₂ u₂ hok1 hx1 hp1 hd₂ hw₂ hu₂
    refine dq_unfold_seq henv b' y' _ hok1 (denote_ext hy hx1) hwy ?_ ?_
    · intro s2 f₂ w₂ hok2 hx2 hp2 hf₂ hwf₂ hw₂'
      exact dq_k_exit hk false e₂ f₂ u₂ w₂ hok2 (hxs.trans (hx1.trans hx2))
        (hp2.trans (hp1.trans hps)) (denote_ext hd₂ hx2) hf₂ hw₂ hwf₂
        (hG.imp fun _ h r hr => h r (by rw [hu₂, hw₂']; exact hr))
    · intro s2 hok2 hx2 hp2 hn
      exact dq_pure_exit hok2 (hxs.trans (hx1.trans hx2))
        (hp2.trans (hp1.trans hps))
        (hG.imp fun _ h => h false (by rw [hu₂, hn]; rfl))
  · intro s1 hok1 hx1 hp1 hn
    refine triple_seq (unfoldDefinition_spec henv s1 d b' hok1
      ⟨y', denote_ext hy hx1, hwy⟩) ?_
    rintro o s2 ⟨hok2, hx2, hp2, _⟩
    exact dq_pure_exit hok2 (hxs.trans (hx1.trans hx2))
      (hp2.trans (hp1.trans hps))
      (hG.imp fun _ h => h false (by rw [hn]; rfl))

/-- con-leche: ConLeche/Kernel/Core.lean:1526-1701 defeqStep — **the tail**:
lazy delta, then congruence. -/
theorem dqTailA_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) (d n : Nat)
    (k : Bool → EIdx → EIdx → AM Bool) (hk : DefeqLoopK mode env fe d n k)
    (s₀ s₁ : AState) (a' b' : EIdx) (x' y' : Expr)
    (hok : CheckOK mode env fe s₁) (hx₁ : Ext s₀.store s₁.store)
    (hp₁ : s₁.pins = s₀.pins)
    (hx : denoteE s₁.store a' = some x') (hy : denoteE s₁.store b' = some y')
    (hwx : Expr.WScoped d x') (hwy : Expr.WScoped d y')
    (G : Nat → Bool → Prop)
    (hG : Ev (fun F => ∀ r, dqTail mode (ConLeche.pureFns mode env F) env d
      (ConLeche.defeqLoop mode (ConLeche.pureFns mode env F) env d n) x' y'
      = .ok r → G F r)) :
    ⦃fun s => ⌜s = s₁⌝⦄ dqTailA mode (coreKnot mode fe id fuel) fe d k a' b'
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ := by
  unfold dqTailA
  refine triple_seq (unfoldableHead_spec s₁ a' x' hok hx) ?_
  rintro ua s2 ⟨hok2, hst2, hp2, hua⟩
  refine triple_seq (unfoldableHead_spec s2 b' y' hok2 (by rw [hst2]; exact hy)) ?_
  rintro ub s3 ⟨hok3, hst3, hp3, hub⟩
  have hst13 : s3.store = s₁.store := hst3.trans hst2
  have hx3 : denoteE s3.store a' = some x' := by rw [hst13]; exact hx
  have hy3 : denoteE s3.store b' = some y' := by rw [hst13]; exact hy
  have hx03 : Ext s₀.store s3.store := by rw [hst13]; exact hx₁
  have hp03 : s3.pins = s₀.pins := hp3.trans (hp2.trans hp₁)
  cases ua <;> cases ub
  · -- neither unfolds: congruence
    exact dqCongrA_spec henv hμ hsim d s₀ s3 a' b' x' y' hok3 hx03 hp03 hx3 hy3
      hwx hwy G (hG.imp fun _ h r hr =>
        h r (by rw [dqTail_ff hua.symm hub.symm]; exact hr))
  · -- only the right unfolds
    refine dq_unfold_seq henv b' y' _ hok3 hy3 hwy ?_ ?_
    · intro s' e₂ u₂ hok' hx' hp' hd₂ hw₂ hu
      exact dq_k_exit hk false a' e₂ x' u₂ hok' (hx03.trans hx')
        (hp'.trans hp03) (denote_ext hx3 hx') hd₂ hwx hw₂
        (hG.imp fun _ h r hr =>
          h r (by rw [dqTail_ft hua.symm hub.symm, hu]; exact hr))
    · intro s' hok' hx' hp' hu
      exact dq_pure_exit hok' (hx03.trans hx') (hp'.trans hp03)
        (hG.imp fun _ h =>
          h false (by rw [dqTail_ft hua.symm hub.symm, hu]; rfl))
  · -- only the left unfolds
    refine dq_unfold_seq henv a' x' _ hok3 hx3 hwx ?_ ?_
    · intro s' e₂ u₂ hok' hx' hp' hd₂ hw₂ hu
      exact dq_k_exit hk false e₂ b' u₂ y' hok' (hx03.trans hx')
        (hp'.trans hp03) hd₂ (denote_ext hy3 hx') hw₂ hwy
        (hG.imp fun _ h r hr =>
          h r (by rw [dqTail_tf hua.symm hub.symm, hu]; exact hr))
    · intro s' hok' hx' hp' hu
      exact dq_pure_exit hok' (hx03.trans hx') (hp'.trans hp03)
        (hG.imp fun _ h =>
          h false (by rw [dqTail_tf hua.symm hub.symm, hu]; rfl))
  · -- both unfold: the hints decide
    refine triple_seq (headHint_spec s3 a' x' hok3 hx3) ?_
    rintro ha s4 ⟨hok4, hst4, hp4, rfl⟩
    refine triple_seq (headHint_spec s4 b' y' hok4 (by rw [hst4]; exact hy3)) ?_
    rintro hb s5 ⟨hok5, hst5, hp5, rfl⟩
    have hst35 : s5.store = s3.store := hst5.trans hst4
    have hx5 : denoteE s5.store a' = some x' := by rw [hst35]; exact hx3
    have hy5 : denoteE s5.store b' = some y' := by rw [hst35]; exact hy3
    have hx05 : Ext s₀.store s5.store := by rw [hst35]; exact hx03
    have hp05 : s5.pins = s₀.pins := hp5.trans (hp4.trans hp03)
    split
    · rename_i hlt
      refine dq_unfold_seq henv a' x' _ hok5 hx5 hwx ?_ ?_
      · intro s' e₂ u₂ hok' hx' hp' hd₂ hw₂ hu
        exact dq_k_exit hk false e₂ b' u₂ y' hok' (hx05.trans hx')
          (hp'.trans hp05) hd₂ (denote_ext hy5 hx') hw₂ hwy
          (hG.imp fun _ h r hr =>
            h r (by rw [dqTail_tt_left hua.symm hub.symm hlt, hu]; exact hr))
      · intro s' hok' hx' hp' hu
        exact dq_pure_exit hok' (hx05.trans hx') (hp'.trans hp05)
          (hG.imp fun _ h =>
            h false (by rw [dqTail_tt_left hua.symm hub.symm hlt, hu]; rfl))
    rename_i hlt1
    simp only [Bool.not_eq_true] at hlt1
    split
    · rename_i hlt2
      refine dq_unfold_seq henv b' y' _ hok5 hy5 hwy ?_ ?_
      · intro s' e₂ u₂ hok' hx' hp' hd₂ hw₂ hu
        exact dq_k_exit hk false a' e₂ x' u₂ hok' (hx05.trans hx')
          (hp'.trans hp05) (denote_ext hx5 hx') hd₂ hwx hw₂
          (hG.imp fun _ h r hr =>
            h r (by rw [dqTail_tt_right hua.symm hub.symm hlt1 hlt2, hu]
                    exact hr))
      · intro s' hok' hx' hp' hu
        exact dq_pure_exit hok' (hx05.trans hx') (hp'.trans hp05)
          (hG.imp fun _ h =>
            h false (by rw [dqTail_tt_right hua.symm hub.symm hlt1 hlt2, hu]
                        rfl))
    rename_i hlt2
    simp only [Bool.not_eq_true] at hlt2
    refine triple_seq (sameConstHeads_spec s5 a' b' x' y' hok5 hx5 hy5) ?_
    rintro sch s6 ⟨hok6, hst6, hp6, rfl⟩
    have hx6 : denoteE s6.store a' = some x' := by rw [hst6]; exact hx5
    have hy6 : denoteE s6.store b' = some y' := by rw [hst6]; exact hy5
    have hx06 : Ext s₀.store s6.store := by rw [hst6]; exact hx05
    have hp06 : s6.pins = s₀.pins := hp6.trans hp05
    split
    · rename_i hsr
      refine triple_seq (defeqSpine_spec hsim s6 d a' b' x' y' hok6 hx6 hy6
        hwx hwy) ?_
      rintro sp s7 ⟨hok7, hx7, hp7, hsp⟩
      have hspE : Ev (fun F => ConLeche.defeqSpine (ConLeche.pureFns mode env F)
          env d x' y' = .ok sp) :=
        Ev.of_mono (fun hle h => defeqSpineFueled_mono hle h) hsp
      have hx07 := hx06.trans hx7
      have hp07 : s7.pins = s₀.pins := hp7.trans hp06
      cases sp
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact dq_both_exit henv hk a' b' x' y' hok7 hx07 hp07
          (denote_ext hx6 hx7) (denote_ext hy6 hx7) hwx hwy
          ((hG.and hspE).imp fun _ ⟨h, hs⟩ r hr => h r (by
            rw [dqTail_tt_spine_false hua.symm hub.symm hlt1 hlt2 hsr hs]
            exact hr))
      · simp only [↓reduceIte]
        exact dq_pure_exit hok7 hx07 hp07 ((hG.and hspE).imp fun _ ⟨h, hs⟩ =>
          h true (dqTail_tt_spine_true hua.symm hub.symm hlt1 hlt2 hsr hs))
    · rename_i hsr
      simp only [Bool.not_eq_true] at hsr
      exact dq_both_exit henv hk a' b' x' y' hok6 hx06 hp06 hx6 hy6 hwx hwy
        (hG.imp fun _ h r hr => h r (by
          rw [dqTail_tt_both hua.symm hub.symm hlt1 hlt2 hsr]; exact hr))
/-- con-leche: ConLeche/Kernel/Core.lean:1461-1701 defeqStep — the step at
FIXED denotations of its two subjects. -/
theorem defeqStep_at {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) (d n : Nat)
    (k : Bool → EIdx → EIdx → AM Bool) (hk : DefeqLoopK mode env fe d n k)
    (pi : Bool) (a b : EIdx) (s₀ : AState) (x y : Expr)
    (hok : CheckOK mode env fe s₀)
    (hx : denoteE s₀.store a = some x) (hy : denoteE s₀.store b = some y)
    (hwx : Expr.WScoped d x) (hwy : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄ defeqStep mode (coreKnot mode fe id fuel) fe d k pi a b
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ (fun F r =>
        ConLeche.defeqLoop mode (ConLeche.pureFns mode env F) env d (n + 1)
          pi x y = .ok r) r s'⌝⦄ := by
  have hwf := hok.state.wf
  unfold ConRon.Arena.defeqStep
  split
  · -- the syntactic fast path
    rename_i hab
    rw [beq_of_denoteE hwf hx hy] at hab
    exact triple_pure_post ⟨hok, Ext.refl _, rfl, 0, defeqLoop_syntactic hab⟩
  rename_i hab
  rw [beq_of_denoteE hwf hx hy] at hab
  simp only [Bool.not_eq_true] at hab
  -- the eq-true shortcut's two guard reads
  refine triple_seq (isBoolTrue_spec s₀ b y hok hy) ?_
  rintro bt s1 ⟨hok1, hst1, hp1, rfl⟩
  refine triple_seq (ExprOps.hasFvarFast_spec coreWalkFuel s1 a hok1.state
    (by rw [hst1, hx]; rfl)) ?_
  rintro hf s2 ⟨hst2, hc2, hp2, hr2⟩
  have hfe : hf = x.hasFvar := hr2 x (by rw [hst1]; exact hx)
  subst hfe
  have hok2 := hok1.of_store_eq hst2 hc2 hp2
  have hst02 : s2.store = s₀.store := hst2.trans hst1
  have hp02 : s2.pins = s₀.pins := hp2.trans hp1
  refine triple_ite_bind ?_
  refine triple_seq (boolTrueShortcutIf_spec hsim s2 d a x _ hok2
    (by rw [hst02]; exact hx) hwx) ?_
  rintro sc s3 ⟨hok3, hx3, hp3, hsc⟩
  have hx03 : Ext s₀.store s3.store := by rw [← hst02]; exact hx3
  have hp03 : s3.pins = s₀.pins := hp3.trans hp02
  try dsimp only
  cases sc
  case true =>
    simp only [if_true]
    obtain ⟨F, hF⟩ := hsc.exists
    exact triple_pure_post ⟨hok3, hx03, hp03, F, defeqLoop_boolTrue hab hF⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- the two head normal forms
  refine triple_seq (hsim.whnfCore s3 d a x hok3 (denote_ext hx hx03) hwx) ?_
  rintro a' s4 ⟨hok4, hx4, hp4, x', hdx', hwx', F4, hF4⟩
  have hx04 := hx03.trans hx4
  refine triple_seq (hsim.whnfCore s4 d b y hok4 (denote_ext hy hx04) hwy) ?_
  rintro b' s5 ⟨hok5, hx5, hp5, y', hdy', hwy', F5, hF5⟩
  have hx05 := hx04.trans hx5
  have hp05 : s5.pins = s₀.pins := hp5.trans (hp4.trans hp03)
  have hdx5 := denote_ext hdx' hx5
  have hwf5 := hok5.state.wf
  have ha : Ev (fun F => ConLeche.whnfCore mode env F d x = .ok x') :=
    Ev.of_mono (fun hle h => ConLeche.whnfCore_mono hle h) ⟨F4, hF4⟩
  have hb : Ev (fun F => ConLeche.whnfCore mode env F d y = .ok y') :=
    Ev.of_mono (fun hle h => ConLeche.whnfCore_mono hle h) ⟨F5, hF5⟩
  split
  · -- the reducts are syntactically equal
    rename_i heq
    rw [beq_of_denoteE hwf5 hdx5 hdy'] at heq
    obtain ⟨F, ⟨h1, h2⟩, h3⟩ := (hsc.and ha |>.and hb).exists
    exact triple_pure_post ⟨hok5, hx05, hp05, F,
      defeqLoop_whnf_eq hab h1 h2 h3 heq⟩
  rename_i heq
  rw [beq_of_denoteE hwf5 hdx5 hdy'] at heq
  simp only [Bool.not_eq_true] at heq
  -- proof irrelevance
  rw [quickPair_denote hwf5 hdx5 hdy']
  refine triple_ite_bind ?_
  refine triple_seq (propIrrelIf_spec hsim s5 d a' b' x' y' _ hok5 hdx5 hdy'
    hwx' hwy') ?_
  rintro pir s6 ⟨hok6, hx6, hp6, hpi⟩
  have hx06 := hx05.trans hx6
  have hp06 : s6.pins = s₀.pins := hp6.trans hp05
  try dsimp only
  cases pir
  case true =>
    simp only [if_true]
    obtain ⟨F, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩⟩ := (hsc.and ha |>.and hb |>.and hpi).exists
    exact triple_pure_post ⟨hok6, hx06, hp06, F,
      defeqLoop_propIrrel hab h1 h2 h3 heq h4⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hdx6 := denote_ext hdx5 hx6
  have hdy6 := denote_ext hdy' hx6
  -- the literal guard
  refine triple_seq (defeqNoFvars_spec s6 a' b' x' y' hok6 hdx6 hdy6) ?_
  rintro nf s7 ⟨hok7, hst7, hp7, rfl⟩
  have hx07 : Ext s₀.store s7.store := by rw [hst7]; exact hx06
  have hp07 : s7.pins = s₀.pins := hp7.trans hp06
  have hdx7 : denoteE s7.store a' = some x' := by rw [hst7]; exact hdx6
  have hdy7 : denoteE s7.store b' = some y' := by rw [hst7]; exact hdy6
  -- literal acceleration on the left
  refine triple_seq (reduceNatIf_spec hsim s7 d a' x' _ hok7 hdx7 hwx') ?_
  rintro o1 s8 ⟨hok8, hx8, hp8, v1, hv1, hwv1, hn1⟩
  have hx08 := hx07.trans hx8
  have hp08 : s8.pins = s₀.pins := hp8.trans hp07
  have hdy8 := denote_ext hdy7 hx8
  cases o1 with
  | some a₂ =>
    obtain ⟨z, rfl, hz⟩ := denoteEO_some_inv hv1
    try dsimp only
    refine triple_mono (hk true a₂ b' s8 hok8 ⟨z, hz, hwv1 z rfl⟩
      ⟨y', hdy8, hwy'⟩) ?_
    rintro r s9 ⟨hok9, hx9, hp9, hr⟩
    obtain ⟨F9, hF9⟩ := hr z y' hz hdy8
    have hl : Ev (fun F => ConLeche.defeqLoop mode (ConLeche.pureFns mode env F)
        env d n true z y' = .ok r) :=
      Ev.of_mono (fun hle h => defeqLoopFueled_mono hle h) ⟨F9, hF9⟩
    obtain ⟨F, ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩⟩ :=
      (hsc.and ha |>.and hb |>.and hpi |>.and hn1 |>.and hl).exists
    exact ⟨hok9, hx08.trans hx9, hp9.trans hp08, F,
      defeqLoop_reduceNat_left hab h1 h2 h3 heq h4 h5 h6⟩
  | none =>
  obtain rfl := denoteEO_none_inv hv1
  try dsimp only
  have hdx8 := denote_ext hdx7 hx8
  -- literal acceleration on the right
  refine triple_seq (reduceNatIf_spec hsim s8 d b' y' _ hok8 hdy8 hwy') ?_
  rintro o2 s9 ⟨hok9, hx9, hp9, v2, hv2, hwv2, hn2⟩
  have hx09 := hx08.trans hx9
  have hp09 : s9.pins = s₀.pins := hp9.trans hp08
  have hdx9 := denote_ext hdx8 hx9
  cases o2 with
  | some b₂ =>
    obtain ⟨z, rfl, hz⟩ := denoteEO_some_inv hv2
    try dsimp only
    refine triple_mono (hk true a' b₂ s9 hok9 ⟨x', hdx9, hwx'⟩
      ⟨z, hz, hwv2 z rfl⟩) ?_
    rintro r s10 ⟨hok10, hx10, hp10, hr⟩
    obtain ⟨F10, hF10⟩ := hr x' z hdx9 hz
    have hl : Ev (fun F => ConLeche.defeqLoop mode (ConLeche.pureFns mode env F)
        env d n true x' z = .ok r) :=
      Ev.of_mono (fun hle h => defeqLoopFueled_mono hle h) ⟨F10, hF10⟩
    obtain ⟨F, ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩⟩ :=
      (hsc.and ha |>.and hb |>.and hpi |>.and hn1 |>.and hn2 |>.and hl).exists
    exact ⟨hok10, hx09.trans hx10, hp10.trans hp09, F,
      defeqLoop_reduceNat_right hab h1 h2 h3 heq h4 h5 h6 h7⟩
  | none =>
  obtain rfl := denoteEO_none_inv hv2
  try dsimp only
  -- the prefix is complete: hand the tail to `dqTailA_spec`
  have hpre : Ev (fun F => DqPre mode env F d pi x y x' y') :=
    (hsc.and ha |>.and hb |>.and hpi |>.and hn1 |>.and hn2).imp
      fun _ ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ =>
        ⟨hab, h1, h2, h3, heq, h4, h5, h6⟩
  exact dqTailA_spec henv hμ hsim d n k hk s₀ s9 a' b' x' y' hok9 hx09 hp09
    hdx9 (denote_ext hdy8 hx9) hwx' hwy' _
    (hpre.imp fun _ h r ht => (defeqLoop_tail h).trans ht)
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
  intro pi a b s₀ hok ⟨x, hx, hwx⟩ ⟨y, hy, hwy⟩
  refine triple_mono
    (defeqStep_at henv hμ hsim d n k hk pi a b s₀ x y hok hx hy hwx hwy) ?_
  rintro r s' ⟨hok', hx', hp', F, hF⟩
  refine ⟨hok', hx', hp', fun x₁ y₁ hx₁ hy₁ => ?_⟩
  obtain rfl := Option.some.inj (hx₁.symm.trans hx)
  obtain rfl := Option.some.inj (hy₁.symm.trans hy)
  exact ⟨F, hF⟩

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

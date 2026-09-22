/-
# `ConRon.Bridge.Core.EnsureSort` — the seventh entry point

Task #97-P3-CoreWalks, ask 2 of the Checker tier.  `Arena/Core.lean` has
SEVEN entry points and `coreKnot` has six slots: `ensureSortCore` is built on
top of the knot (`ensureSort (pureFnsA mode fe fuel) fe depth e`) rather than
being one of its fields, so `Bridge/Core/Knot.lean`'s `KnotSpec` does not
cover it — and the declaration front door calls it at every constant, which
is why `Bridge/Checker/Hyp.lean` had to carry `EnsureSortSpec` as a second
named hypothesis beside `KnotSpec`.

This module discharges it.  It is one `whnf` call and a tag test: the
theorem is `KnotSpec.whnf` followed by `Bridge/Rel.lean`'s `denote_sort_inv`,
and the pure side is con-leche's own `ensureSort_def` (`Verify/Knot.lean:215`,
which is `rfl`).

**Why it is its own module rather than a line in `Bridge/Core/Induction.lean`.**
`Bridge/Checker/Hyp.lean` imports `Core.Induction` for `knot_spec_checkFuel`;
it now imports this too, and keeping the two apart means the Checker tier's
import closure does not grow by the six `Arms/` modules a second time.  It
takes `KnotSpec` as a HYPOTHESIS, so it needs `Core/Knot.lean` and nothing
else — the same discipline `Bridge/Core/Arms/*.lean` follow.
-/
import ConRon.Bridge.Core.Knot

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env}

/-! ## 1. The answer relation

`Bridge/Core/Knot.lean`'s `SimE` at a `Level` answer.  There is no
well-scopedness conjunct: a level has no binder depth, so nothing a caller
does with the answer needs one.  `Bridge/Checker/Hyp.lean` states the same
relation for its hypothesis; the two are the same definition, so its
`EnsureSortSpec` is discharged by `exact`. -/

/-- con-leche: ConLeche/Verify/SimI.lean:254 RelL — the level-valued answer
relation of a core entry point. -/
def SimL (op : Nat → Nat → Expr → CheckM Level) (d : Nat) (e : Expr)
    (st' : EStore) (r : LIdx) : Prop :=
  ∃ u, denoteL st'.ls r = some u ∧ ∃ F, op F d e = .ok u

/-- con-leche: none — the answer survives an arena extension. -/
theorem SimL.ext {op : Nat → Nat → Expr → CheckM Level} {d : Nat} {e : Expr}
    {st st' : EStore} {r : LIdx} (h : SimL op d e st r) (hx : Ext st st') :
    SimL op d e st' r := by
  obtain ⟨u, hu, F, hF⟩ := h
  exact ⟨u, hx.lss.ls.lvl _ _ hu, F, hF⟩

/-! ## 2. The pure side's one step lemma

Rule 8 at a body with one exit: `ensureSortCore` succeeds exactly when the
reduction loop lands on a sort.  con-leche's `ensureSort_def`
(`Verify/Knot.lean:215`) is `rfl`, so this is one `simp only`. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1101-1107 ensureSort — the entry's
only exit: `whnf` answered a sort, so `ensureSortCore` answers its level. -/
theorem ensureSortCore_of_whnf {F d : Nat} {e : Expr} {l : Level}
    (h : ConLeche.whnf mode env F d e = .ok (.sort l)) :
    ConLeche.ensureSortCore mode env F d e = .ok l := by
  rw [← ConLeche.ensureSort_def]
  simp only [ConLeche.ensureSort, ConLeche.whnf_def] at h ⊢
  simp only [h, bind, Except.bind, pure, Except.pure]

/-! ## 3. The entry's theorem -/

/-- con-leche: ConLeche/Kernel/TypeChecker.lean:56-58 ensureSortCore —
**THEOREM 1 for the seventh entry point**, at a knot record that satisfies
`KnotSpec` (which is `Bridge/Core/Induction.lean`'s `knot_spec_checkFuel` at
the fuel every entry is called with).

`Bridge/Checker/Hyp.lean`'s `EnsureSortSpec` is this statement; the Checker
tier's `CoreSpec` is therefore fully discharged by the Core tier, modulo the
six body walks `KnotSpec` itself is waiting on. -/
theorem ensureSortCore_spec {fe : IFEnv} {f : Nat}
    (hsim : KnotSpec mode env fe f)
    (s₀ : AState) (d : Nat) (i : EIdx) (e : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store i = some e)
    (hw : Expr.WScoped d e) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.ensureSortCore mode fe f d i
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimL (ConLeche.ensureSortCore mode env) d e s'.store r⌝⦄ := by
  have hb := hsim.whnf s₀ d i e hok hden hw
  mvcgen [ConRon.Arena.ensureSortCore, ConRon.Arena.ensureSort,
    ConRon.Arena.pureFnsA, hb]
  all_goals (bridge_peel; subst_vars)
  all_goals
    first
      | (intro hf; exact False.elim hf)
      | (rename_i hck hvw hsm hxt hpn
         refine ⟨hck, hxt, hpn, ?_⟩
         obtain ⟨v, hv, _hwv, F, hF⟩ := hsm
         obtain ⟨l, rfl, hl⟩ := denote_sort_inv hck.state.wf hvw hv
         exact ⟨l, hl, F, ensureSortCore_of_whnf hF⟩)
      | (exact hok)
      | (exact hden)

end ConRon.Bridge.Core

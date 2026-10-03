/-
# `ConRon.Bridge.Core.Arms.Defeq` — Theorem 1 for `defeqBody`

DESIGN §8.2, rule 8's inventory for con-leche 8afe1815's definitional
equality (`ConLeche/Kernel/Core.lean:1478-1831`, `quickDefEq` … `defeqBody`),
restructured after the official `is_def_eq_core` (task #109).  One spec per
twin function, each relating `Arena/Core.lean`'s function to con-leche's at
`pureFns mode env F`, with the frame (`CheckOK`, `Ext`, pins) and the pure
answer at some fuel (`Ev`, `DqPost`: `Arms/DefeqBase.lean`):

| twin function | spec | module |
|---|---|---|
| `quickDefEq` (binder arms: the batched `defeqBinders`) | `quickDefEq_spec` (`defeqBinders_spec`) | `Arms/DefeqLazy.lean` (`Arms/DefeqPeel.lean`) |
| `isNatZero`, `natPred?`, `defeqOffset` | `isNatZero_spec`, `natPred?_spec`, `defeqOffset_spec` | `Arms/DefeqLazy.lean` |
| `headIsProj`, `tryUnfoldProjApp` | `headIsProj_spec`, `tryUnfoldProjApp_spec` | `Arms/DefeqLazy.lean` |
| `deltaQuick`, `lazyDeltaStep` | `deltaQuick_spec`, `lazyDeltaStep_spec` | `Arms/DefeqLazy.lean` |
| `lazyDeltaReduction` (induction on the budget) | `lazyDeltaReduction_spec` | `Arms/DefeqLazy.lean` |
| `defeqStuck` | `defeqStuck_spec` | `Arms/DefeqStuck.lean` |
| `lazyDeltaProjReduction` (induction on the budget) | `lazyDeltaProjReduction_spec` | here, §2 |
| `defeqProjPair` | `defeqProjPair_spec` | here, §2 |
| `defeqBody` | `defeqBody_spec` (via `defeqBody_at`) | here, §3 |

The pure side of `defeqBody` is §1: one equation per exit of con-leche's
body, each under the facts the exit has established (`defeqBody_quick` …
`defeqBody_restart`).  The projection rule of `lazyDeltaProjReduction` is
`Walks/ProjCore.lean`'s `reduceProjCore_spec`.

## The batched binder descent

`quickDefEq`'s `.forallE`/`.lam` arms are the ones the twin does NOT run
clause for clause: `defeqBinders` compares the first domains and then hands
the two telescopes to the batched `defeqPeel`, which opens each domain
against the accumulated free variables in ONE `instantiateList`.  Its
identification against the chained arms (task #97-P6-14's port-side debt) is
`Arms/DefeqPeel.lean`'s `defeqBinders_spec`; the peel's justification is the
same as before: at each level the chain runs `defeqBody`, whose prefix is a
no-op on two binders (`isBoolTrue` is `false`, the cheap `whnfCore` is the
identity on binders), so it reaches `quickDefEq`'s binder arm on the pair
itself (`isDefEqCore_bnd`).
-/
import ConRon.Bridge.Core.Arms.DefeqLazy
import ConRon.Bridge.Core.Arms.DefeqStuck
import ConRon.Bridge.Core.Walks.ProjCore

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env}

/-! ## 1. The pure side of `defeqBody`, exit by exit -/

section PureBody

variable {F d : Nat} {x y x' y' : Expr}

/-- con-leche: ConLeche/Kernel/Core.lean:1791-1831 defeqBody — **the
syntactic fast path**. -/
theorem defeqBody_syntactic (h : (x == y) = true) :
    ConLeche.defeqBody mode (ConLeche.pureFns mode env F) env d x y = .ok true := by
  rw [ConLeche.defeqBody]
  simp only [h, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1791-1831 defeqBody — **the eq-true
shortcut** (the divergence audit's E2). -/
theorem defeqBody_boolTrue (hab : (x == y) = false)
    (hsc : (if (y.isBoolTrue && !x.hasFvar) = true then
        ConLeche.boolTrueShortcut (ConLeche.pureFns mode env F) d x
      else pure false) = (.ok true : CheckM Bool)) :
    ConLeche.defeqBody mode (ConLeche.pureFns mode env F) env d x y = .ok true := by
  rw [ConLeche.defeqBody]
  simp only [hab, Bool.false_eq_true, if_false]
  rw [hsc]
  simp only [bind, Except.bind, if_true, pure, Except.pure]

/-- con-leche: ConLeche/Kernel/Core.lean:1791-1831 defeqBody — **the prefix
every later exit has run**, at one fuel: no syntactic hit, no eq-true
shortcut, the two cheap head normal forms. -/
structure DbPre (mode : CheckMode) (env : Env) (F d : Nat)
    (x y x' y' : Expr) : Prop where
  hab : (x == y) = false
  hsc : (if (y.isBoolTrue && !x.hasFvar) = true then
      ConLeche.boolTrueShortcut (ConLeche.pureFns mode env F) d x
    else pure false) = (.ok false : CheckM Bool)
  ha : ConLeche.whnfCore mode env F d x true = .ok x'
  hb : ConLeche.whnfCore mode env F d y true = .ok y'

/-- con-leche: ConLeche/Kernel/Core.lean:1791-1831 defeqBody — the body past
the prefix: `quickDefEq` on the cheap head normal forms and what follows. -/
theorem defeqBody_pre (h : DbPre mode env F d x y x' y') :
    ConLeche.defeqBody mode (ConLeche.pureFns mode env F) env d x y =
      (ConLeche.quickDefEq mode (ConLeche.pureFns mode env F) d x' y' >>= fun o =>
        match o with
        | some v => pure v
        | none => do
          if ← ConLeche.propIrrel (ConLeche.pureFns mode env F) env d x' y' then
            pure true else
          match ← ConLeche.lazyDeltaReduction mode (ConLeche.pureFns mode env F)
              env d ConLeche.defeqLoopFuel x' y' with
          | .verdict v => pure v
          | .unknown a₁ b₁ =>
          if ← ConLeche.defeqProjPair mode (ConLeche.pureFns mode env F) env d a₁ b₁
            then pure true else
          if !a₁.headIsProj && !b₁.headIsProj then
            ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d a₁ b₁ else
          let a₂ ← (ConLeche.pureFns mode env F).whnfCore false d a₁
          let b₂ ← (ConLeche.pureFns mode env F).whnfCore false d b₁
          if a₂ == a₁ && b₂ == b₁ then
            ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d a₁ b₁
          else (ConLeche.pureFns mode env F).defeq d a₂ b₂) := by
  rw [ConLeche.defeqBody]
  simp only [h.hab, Bool.false_eq_true, if_false]
  rw [h.hsc]
  simp only [bind, Except.bind, Bool.false_eq_true, if_false,
    ConLeche.whnfCore_def, h.ha, h.hb]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1791-1831 defeqBody — the easy
cases decide. -/
theorem defeqBody_quick {v : Bool} (h : DbPre mode env F d x y x' y')
    (hq : ConLeche.quickDefEq mode (ConLeche.pureFns mode env F) d x' y'
      = .ok (some v)) :
    ConLeche.defeqBody mode (ConLeche.pureFns mode env F) env d x y = .ok v := by
  rw [defeqBody_pre h, hq]; rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1791-1831 defeqBody — **proof
irrelevance**. -/
theorem defeqBody_propIrrel (h : DbPre mode env F d x y x' y')
    (hq : ConLeche.quickDefEq mode (ConLeche.pureFns mode env F) d x' y' = .ok none)
    (hpi : ConLeche.propIrrel (ConLeche.pureFns mode env F) env d x' y' = .ok true) :
    ConLeche.defeqBody mode (ConLeche.pureFns mode env F) env d x y = .ok true := by
  rw [defeqBody_pre h, hq]
  simp only [bind, Except.bind, hpi]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1791-1831 defeqBody — the facts
past the lazy-delta loop that the last four exits share. -/
structure DbMid (mode : CheckMode) (env : Env) (F d : Nat)
    (x' y' : Expr) (r : LazyRes) : Prop where
  hq : ConLeche.quickDefEq mode (ConLeche.pureFns mode env F) d x' y' = .ok none
  hpi : ConLeche.propIrrel (ConLeche.pureFns mode env F) env d x' y' = .ok false
  hl : ConLeche.lazyDeltaReduction mode (ConLeche.pureFns mode env F) env d
    ConLeche.defeqLoopFuel x' y' = .ok r

/-- con-leche: ConLeche/Kernel/Core.lean:1791-1831 defeqBody — **the
lazy-delta loop decides**. -/
theorem defeqBody_verdict {v : Bool} (h : DbPre mode env F d x y x' y')
    (hm : DbMid mode env F d x' y' (.verdict v)) :
    ConLeche.defeqBody mode (ConLeche.pureFns mode env F) env d x y = .ok v := by
  rw [defeqBody_pre h, hm.hq]
  simp only [bind, Except.bind, hm.hpi, Bool.false_eq_true, if_false, hm.hl]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1791-1831 defeqBody — the body past
the loop's `unknown`: the proj/proj check and what follows. -/
theorem defeqBody_unknown {a₁ b₁ : Expr} (h : DbPre mode env F d x y x' y')
    (hm : DbMid mode env F d x' y' (.unknown a₁ b₁)) :
    ConLeche.defeqBody mode (ConLeche.pureFns mode env F) env d x y =
      (ConLeche.defeqProjPair mode (ConLeche.pureFns mode env F) env d a₁ b₁ >>=
        fun pp => if pp = true then pure true else
          if (!a₁.headIsProj && !b₁.headIsProj) = true then
            ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d a₁ b₁ else
          (ConLeche.whnfCore mode env F d a₁ false >>= fun a₂ =>
            ConLeche.whnfCore mode env F d b₁ false >>= fun b₂ =>
            if (a₂ == a₁ && b₂ == b₁) = true then
              ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d a₁ b₁
            else ConLeche.isDefEqCore mode env F d a₂ b₂)) := by
  rw [defeqBody_pre h, hm.hq]
  simp only [bind, Except.bind, hm.hpi, Bool.false_eq_true, if_false, hm.hl]
  rfl

end PureBody

/-! ## 2. The proj/proj check: `lazyDeltaProjReduction`, `defeqProjPair` -/

section ProjPair

variable {fe : IFEnv} {fuel : Nat}

/-- con-leche: ConLeche/Kernel/Core.lean:1691-1709 lazyDeltaProjReduction —
the loop's tail once the step found the scrutinees different or stuck: the
projection on both, and the fields, or else the scrutinees, compared. -/
def ldprTail (mode : CheckMode) (r : CoreFns CheckM) (env : Env) (d : Nat)
    (sn : Name) (i : Nat) (a b : Expr) : CheckM Bool := do
  match ← ConLeche.reduceProjCore mode r env d sn i a with
  | some x =>
    match ← ConLeche.reduceProjCore mode r env d sn i b with
    | some y => r.defeq d x y
    | none => r.defeq d a b
  | none => r.defeq d a b

/-- con-leche: ConLeche/Kernel/Core.lean:1691-1709 lazyDeltaProjReduction —
**the tail on the twin side**, against `ldprTail`. -/
theorem ldprTail_spec (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel) (d : Nat) (sn : NIdx) (nm : Name)
    (i : Nat) {s₀ s₁ : AState} (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₁) (hx₁ : Ext s₀.store s₁.store)
    (hp₁ : s₁.pins = s₀.pins) (hsn : denoteN s₁.store.ns sn = some nm)
    (hx : denoteE s₁.store a = some x) (hy : denoteE s₁.store b = some y)
    (hwx : Expr.WScoped d x) (hwy : Expr.WScoped d y)
    (G : Nat → Bool → Prop)
    (hG : Ev (fun F => ∀ r, ldprTail mode (ConLeche.pureFns mode env F) env d nm i
      x y = .ok r → G F r)) :
    ⦃fun s => ⌜s = s₁⌝⦄
      (do
        match ← ConRon.Arena.reduceProjCore mode (coreKnot mode fe id fuel) fe d sn i a with
        | some p =>
          match ← ConRon.Arena.reduceProjCore mode (coreKnot mode fe id fuel) fe d sn i b with
          | some q => (coreKnot mode fe id fuel).defeq d p q
          | none => (coreKnot mode fe id fuel).defeq d a b
        | none => (coreKnot mode fe id fuel).defeq d a b)
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ G r s'⌝⦄ := by
  refine triple_seq (reduceProjCore_spec henv hsim s₁ d sn i a nm x hok hsn hx hwx) ?_
  rintro o1 s2 ⟨hok2, hx2, hp2, v1, hv1, hwv1, F1, hF1⟩
  have hR1 : Ev (fun F => ConLeche.reduceProjCore mode (ConLeche.pureFns mode env F)
      env d nm i x = .ok v1) :=
    Ev.of_mono (fun hle h => reduceProjCoreFueled_mono hle h) ⟨F1, hF1⟩
  have hx12 := hx₁.trans hx2
  have hp12 : s2.pins = s₀.pins := hp2.trans hp₁
  cases o1 with
  | none =>
    obtain rfl := denoteEO_none_inv hv1
    exact dq_defeq_exit hsim a b x y hok2 hx12 hp12 (denote_ext hx hx2)
      (denote_ext hy hx2) hwx hwy ((hG.and hR1).imp fun F ⟨h, h1⟩ r hr => h r (by
        unfold ldprTail; simp only [h1, bind, Except.bind]; exact hr))
  | some p =>
    obtain ⟨px, rfl, hdp⟩ := denoteEO_some_inv hv1
    dsimp only
    refine triple_seq (reduceProjCore_spec henv hsim s2 d sn i b nm y hok2
      (denoteN_ext hsn hx2) (denote_ext hy hx2) hwy) ?_
    rintro o2 s3 ⟨hok3, hx3, hp3, v2, hv2, hwv2, F2, hF2⟩
    have hR2 : Ev (fun F => ConLeche.reduceProjCore mode (ConLeche.pureFns mode env F)
        env d nm i y = .ok v2) :=
      Ev.of_mono (fun hle h => reduceProjCoreFueled_mono hle h) ⟨F2, hF2⟩
    have hx13 := hx12.trans hx3
    have hp13 : s3.pins = s₀.pins := hp3.trans hp12
    cases o2 with
    | none =>
      obtain rfl := denoteEO_none_inv hv2
      exact dq_defeq_exit hsim a b x y hok3 hx13 hp13 (denote_ext hx (hx2.trans hx3))
        (denote_ext hy (hx2.trans hx3)) hwx hwy
        (((hG.and hR1).and hR2).imp fun F ⟨⟨h, h1⟩, h2⟩ r hr => h r (by
          unfold ldprTail; simp only [h1, h2, bind, Except.bind]; exact hr))
    | some q =>
      obtain ⟨qy, rfl, hdq⟩ := denoteEO_some_inv hv2
      exact dq_defeq_exit hsim p q px qy hok3 hx13 hp13 (denote_ext hdp hx3) hdq
        (hwv1 px rfl) (hwv2 qy rfl)
        (((hG.and hR1).and hR2).imp fun F ⟨⟨h, h1⟩, h2⟩ r hr => h r (by
          unfold ldprTail; simp only [h1, h2, bind, Except.bind]; exact hr))

/-- con-leche: ConLeche/Kernel/Core.lean:1691-1709 lazyDeltaProjReduction —
**THEOREM 1 for the projection loop**, at every budget, by induction on it:
one `lazyDeltaStep` on the scrutinees, whose `cont` is the next iteration,
whose `eq` decides, and whose `diff`/`unknown` hand over to `ldprTail`. -/
theorem lazyDeltaProjReduction_spec (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel) (d : Nat) (sn : NIdx) (nm : Name)
    (i : Nat) :
    ∀ (n : Nat) (s₀ : AState) (a b : EIdx) (x y : Expr),
      CheckOK mode env fe s₀ → denoteN s₀.store.ns sn = some nm →
      denoteE s₀.store a = some x → denoteE s₀.store b = some y →
      Expr.WScoped d x → Expr.WScoped d y →
      ⦃fun s => ⌜s = s₀⌝⦄
        ConRon.Arena.lazyDeltaProjReduction mode (coreKnot mode fe id fuel) fe d sn i
          n a b
      ⦃⇓? r s' => ⌜DqPost mode env fe s₀ (fun F r =>
          ConLeche.lazyDeltaProjReduction mode (ConLeche.pureFns mode env F) env d
            nm i n x y = .ok r) r s'⌝⦄
  | 0, s₀, a, b, x, y, _, _, _, _, _, _ => by
    rw [ConRon.Arena.lazyDeltaProjReduction]
    exact triple_fail
  | n + 1, s₀, a, b, x, y, hok, hsn, hx, hy, hwx, hwy => by
    rw [ConRon.Arena.lazyDeltaProjReduction]
    refine triple_seq (lazyDeltaStep_spec henv hsim d s₀ a b x y hok hx hy hwx hwy) ?_
    rintro st s1 ⟨hok1, hx1, hp1, w, hr, hS⟩
    have hstep : ∀ F, ConLeche.lazyDeltaStep mode (ConLeche.pureFns mode env F) env d
        x y = .ok w →
        ConLeche.lazyDeltaProjReduction mode (ConLeche.pureFns mode env F) env d nm i
          (n + 1) x y =
        (match w with
          | .cont a' b' => ConLeche.lazyDeltaProjReduction mode
              (ConLeche.pureFns mode env F) env d nm i n a' b'
          | .eq => pure true
          | .diff => ldprTail mode (ConLeche.pureFns mode env F) env d nm i x y
          | .unknown => ldprTail mode (ConLeche.pureFns mode env F) env d nm i x y) := by
      intro F h
      rw [ConLeche.lazyDeltaProjReduction]
      simp only [bind, Except.bind, h]
      cases w <;> rfl
    have hP := hS.imp fun F h => hstep F h
    have hsn1 := denoteN_ext hsn hx1
    rcases st with ⟨a', b'⟩ | _ | _ | _ <;> rcases w with ⟨x', y'⟩ | _ | _ | _ <;>
      simp only [DSRel] at hr
    · -- `cont`: the next iteration
      obtain ⟨ha', hb', hwx', hwy'⟩ := hr
      refine triple_mono (lazyDeltaProjReduction_spec henv hsim d sn nm i n s1 a' b'
        x' y' hok1 hsn1 ha' hb' hwx' hwy') ?_
      rintro r s2 ⟨hok2, hx2, hp2, F2, hF2⟩
      have hL : Ev (fun F => ConLeche.lazyDeltaProjReduction mode
          (ConLeche.pureFns mode env F) env d nm i n x' y' = .ok r) :=
        Ev.of_mono (fun hle h => lazyDeltaProjReductionFueled_mono hle h) ⟨F2, hF2⟩
      exact ⟨hok2, hx1.trans hx2, hp2.trans hp1,
        Ev.exists ((hP.and hL).imp fun _ ⟨h1, h2⟩ => h1.trans h2)⟩
    · -- `eq`
      exact triple_pure_post ⟨hok1, hx1, hp1, Ev.exists (hP.imp fun _ h => h)⟩
    · -- `diff`
      exact ldprTail_spec henv hsim d sn nm i a b x y hok1 hx1 hp1 hsn1
        (denote_ext hx hx1) (denote_ext hy hx1) hwx hwy _
        (hP.imp fun _ h r hr => h.trans hr)
    · -- `unknown`
      exact ldprTail_spec henv hsim d sn nm i a b x y hok1 hx1 hp1 hsn1
        (denote_ext hx hx1) (denote_ext hy hx1) hwx hwy _
        (hP.imp fun _ h r hr => h.trans hr)

/-- con-leche: ConLeche/Kernel/Core.lean:1711-1720 defeqProjPair — a pair that
is not two projections answers `false`. -/
theorem defeqProjPair_not {r : CoreFns CheckM} {d : Nat} {x y : Expr}
    (h : ¬ (exprTag x = ETag.proj ∧ exprTag y = ETag.proj)) :
    ConLeche.defeqProjPair mode r env d x y = pure false := by
  unfold ConLeche.defeqProjPair
  split
  · exfalso; exact h ⟨rfl, rfl⟩
  · rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1711-1720 defeqProjPair — **THEOREM 1
for the proj/proj check**: the two tag tests are con-leche's constructor
match, handle equality of the structure names is name equality, and the
scrutinees go through `lazyDeltaProjReduction_spec` at the shared budget. -/
theorem defeqProjPair_spec (henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel) (d : Nat) (s₀ : AState) (a b : EIdx)
    (x y : Expr) (hok : CheckOK mode env fe s₀)
    (hx : denoteE s₀.store a = some x) (hy : denoteE s₀.store b = some y)
    (hwx : Expr.WScoped d x) (hwy : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.defeqProjPair mode (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ (fun F r =>
        ConLeche.defeqProjPair mode (ConLeche.pureFns mode env F) env d x y = .ok r)
        r s'⌝⦄ := by
  have hwf := hok.state.wf
  unfold ConRon.Arena.defeqProjPair
  rw [tag_of_denote hwf hx, tag_of_denote hwf hy]
  split
  · rename_i hpp
    obtain ⟨va, hva⟩ := denoteE_view hx
    obtain ⟨vb, hvb⟩ := denoteE_view hy
    refine view_bind_triple hva ?_
    refine view_bind_triple hvb ?_
    have hA := VD.of_view hwf hva hx
    have hB := VD.of_view hwf hvb hy
    rcases hA with _ | _ | _ | _ | _ | _ | _ | _ | _ |
      ⟨pn1, pi1, ps1, pnm1, pes1, hpn1, hps1⟩
    case proj =>
      rcases hB with _ | _ | _ | _ | _ | _ | _ | _ | _ |
        ⟨pn2, pi2, ps2, pnm2, pes2, hpn2, hps2⟩
      case proj =>
        try dsimp only
        have hbeq : (pn1 == pn2 && pi1 == pi2) = (pnm1 == pnm2 && pi1 == pi2) := by
          rw [beq_handle_eq hwf hpn1 hpn2]
        have hw1 : Expr.WScoped d pes1 := by simpa [Expr.WScoped] using hwx
        have hw2 : Expr.WScoped d pes2 := by simpa [Expr.WScoped] using hwy
        split
        · rename_i hc
          rw [hbeq] at hc
          refine triple_mono (lazyDeltaProjReduction_spec henv hsim d pn1 pnm1 pi1
            ConRon.Arena.defeqLoopFuel s₀ ps1 ps2 pes1 pes2 hok hpn1 hps1 hps2 hw1
            hw2) ?_
          rintro r s' ⟨hok', hx', hp', F, hF⟩
          refine ⟨hok', hx', hp', F, ?_⟩
          unfold ConLeche.defeqProjPair
          dsimp only
          rw [if_pos hc, ← defeqLoopFuel_eq]
          simp only [beq_iff_eq, Bool.and_eq_true] at hc
          obtain ⟨rfl, rfl⟩ := hc
          exact hF
        · rename_i hc
          rw [hbeq] at hc
          exact triple_pure_post ⟨hok, Ext.refl _, rfl, 0, by
            unfold ConLeche.defeqProjPair; dsimp only; rw [if_neg hc]; rfl⟩
      all_goals
        simp only [Bool.and_eq_true] at hpp
        exact absurd hpp.2 (by simp only [exprTag]; decide)
    all_goals
      simp only [Bool.and_eq_true] at hpp
      exact absurd hpp.1 (by simp only [exprTag]; decide)
  · rename_i hpp
    exact triple_pure_post ⟨hok, Ext.refl _, rfl, 0, by
      dsimp only
      rw [defeqProjPair_not (fun ⟨h1, h2⟩ => hpp (by simp [h1, h2]))]; rfl⟩

end ProjPair

/-! ## 3. The body -/

section Body

variable {fe : IFEnv} {fuel : Nat}

/-- con-leche: ConLeche/Kernel/Core.lean:1791-1831 defeqBody — **THEOREM 1
for the body at FIXED denotations of its two subjects**, stage by stage: the
syntactic fast path, the eq-true shortcut, the cheap head normal forms,
`quickDefEq`, proof irrelevance, the lazy-delta loop, the proj/proj check,
and — only at a projection-headed side — the full `whnfCore` and either the
stuck comparison or a restart through the knot. -/
theorem defeqBody_at (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) (d : Nat) (s₀ : AState) (a b : EIdx)
    (x y : Expr) (hok : CheckOK mode env fe s₀)
    (hx : denoteE s₀.store a = some x) (hy : denoteE s₀.store b = some y)
    (hwx : Expr.WScoped d x) (hwy : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄ defeqBody mode (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? r s' => ⌜DqPost mode env fe s₀ (fun F r =>
        ConLeche.defeqBody mode (ConLeche.pureFns mode env F) env d x y = .ok r)
        r s'⌝⦄ := by
  have hwf := hok.state.wf
  unfold ConRon.Arena.defeqBody
  split
  · -- the syntactic fast path
    rename_i hab
    rw [beq_of_denoteE hwf hx hy] at hab
    exact triple_pure_post ⟨hok, Ext.refl _, rfl, 0, defeqBody_syntactic hab⟩
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
  dsimp only
  refine triple_ite_bind ?_
  refine triple_seq (boolTrueShortcutIf_spec hsim s2 d a x _ hok2
    (by rw [hst02]; exact hx) hwx) ?_
  rintro sc s3 ⟨hok3, hx3, hp3, hsc⟩
  have hx03 : Ext s₀.store s3.store := by rw [← hst02]; exact hx3
  have hp03 : s3.pins = s₀.pins := hp3.trans hp02
  cases sc
  case true =>
    simp only [if_true]
    obtain ⟨F, hF⟩ := hsc.exists
    exact triple_pure_post ⟨hok3, hx03, hp03, F, defeqBody_boolTrue hab hF⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- the two cheap head normal forms
  refine triple_seq (hsim.whnfCore (c := true) s3 d a x hok3 (denote_ext hx hx03)
    hwx) ?_
  rintro a' s4 ⟨hok4, hx4, hp4, x', hdx', hwx', F4, hF4⟩
  have hx04 := hx03.trans hx4
  refine triple_seq (hsim.whnfCore (c := true) s4 d b y hok4 (denote_ext hy hx04)
    hwy) ?_
  rintro b' s5 ⟨hok5, hx5, hp5, y', hdy', hwy', F5, hF5⟩
  have hx05 := hx04.trans hx5
  have hp05 : s5.pins = s₀.pins := hp5.trans (hp4.trans hp03)
  have hdx5 := denote_ext hdx' hx5
  have ha : Ev (fun F => ConLeche.whnfCore mode env F d x true = .ok x') :=
    Ev.of_mono (fun hle h => ConLeche.whnfCore_mono hle h) ⟨F4, hF4⟩
  have hb : Ev (fun F => ConLeche.whnfCore mode env F d y true = .ok y') :=
    Ev.of_mono (fun hle h => ConLeche.whnfCore_mono hle h) ⟨F5, hF5⟩
  have hpre : Ev (fun F => DbPre mode env F d x y x' y') :=
    ((hsc.and ha).and hb).imp fun _ ⟨⟨h1, h2⟩, h3⟩ => ⟨hab, h1, h2, h3⟩
  -- the easy cases
  refine triple_seq (quickDefEq_spec hsim d s5 a' b' x' y' hok5 hdx5 hdy' hwx'
    hwy') ?_
  rintro q s6 ⟨hok6, hx6, hp6, hq⟩
  have hx06 := hx05.trans hx6
  have hp06 : s6.pins = s₀.pins := hp6.trans hp05
  cases q with
  | some v =>
    exact triple_pure_post ⟨hok6, hx06, hp06,
      Ev.exists ((hpre.and hq).imp fun _ ⟨h1, h2⟩ => defeqBody_quick h1 h2)⟩
  | none =>
  dsimp only
  -- proof irrelevance
  have hdx6 := denote_ext hdx5 hx6
  have hdy6 := denote_ext hdy' hx6
  refine triple_seq (propIrrel_spec hsim s6 d a' b' x' y' hok6 hdx6 hdy6 hwx' hwy') ?_
  rintro pir s7 ⟨hok7, hx7, hp7, hpiF⟩
  have hpi : Ev (fun F => ConLeche.propIrrel (ConLeche.pureFns mode env F) env d x' y'
      = .ok pir) :=
    Ev.of_mono (p := fun F => ConLeche.propIrrel (ConLeche.pureFns mode env F) env d
      x' y' = .ok pir) (fun hle h => propIrrelFueled_mono hle h) hpiF
  have hx07 := hx06.trans hx7
  have hp07 : s7.pins = s₀.pins := hp7.trans hp06
  cases pir
  case true =>
    simp only [if_true]
    exact triple_pure_post ⟨hok7, hx07, hp07,
      Ev.exists (((hpre.and hq).and hpi).imp fun _ ⟨⟨h1, h2⟩, h3⟩ =>
        defeqBody_propIrrel h1 h2 h3)⟩
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- the lazy-delta loop
  refine triple_seq (lazyDeltaReduction_spec henv hsim d ConRon.Arena.defeqLoopFuel s7
    a' b' x' y' hok7 (denote_ext hdx6 hx7) (denote_ext hdy6 hx7) hwx' hwy') ?_
  rintro lr s8 ⟨hok8, hx8, hp8, w, hrw, hL⟩
  rw [defeqLoopFuel_eq] at hL
  have hx08 := hx07.trans hx8
  have hp08 : s8.pins = s₀.pins := hp8.trans hp07
  have hmid : ∀ w', w = w' → Ev (fun F => DbPre mode env F d x y x' y' ∧
      DbMid mode env F d x' y' w') := fun w' hw' =>
    (((hpre.and hq).and hpi).and hL).imp fun _ ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ =>
      ⟨h1, ⟨h2, h3, hw' ▸ h4⟩⟩
  rcases lr with v | ⟨a₁, b₁⟩ <;> rcases w with v' | ⟨x₁, y₁⟩ <;>
    simp only [LRRel] at hrw
  · subst hrw
    exact triple_pure_post ⟨hok8, hx08, hp08,
      Ev.exists ((hmid _ rfl).imp fun _ ⟨h1, h2⟩ => defeqBody_verdict h1 h2)⟩
  obtain ⟨ha₁, hb₁, hwx₁, hwy₁⟩ := hrw
  have hU := hmid _ rfl
  dsimp only
  -- the proj/proj check
  refine triple_seq (defeqProjPair_spec henv hsim d s8 a₁ b₁ x₁ y₁ hok8 ha₁ hb₁
    hwx₁ hwy₁) ?_
  rintro pp s9 ⟨hok9, hx9, hp9, F9, hF9⟩
  have hPP : Ev (fun F => ConLeche.defeqProjPair mode (ConLeche.pureFns mode env F)
      env d x₁ y₁ = .ok pp) :=
    Ev.of_mono (fun hle h => defeqProjPairF_mono hle h) ⟨F9, hF9⟩
  have hx09 := hx08.trans hx9
  have hp09 : s9.pins = s₀.pins := hp9.trans hp08
  have hU' : Ev (fun F => ConLeche.defeqBody mode (ConLeche.pureFns mode env F) env
      d x y =
      (if pp = true then pure true else
          if (!x₁.headIsProj && !y₁.headIsProj) = true then
            ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d x₁ y₁ else
          (ConLeche.whnfCore mode env F d x₁ false >>= fun a₂ =>
            ConLeche.whnfCore mode env F d y₁ false >>= fun b₂ =>
            if (a₂ == x₁ && b₂ == y₁) = true then
              ConLeche.defeqStuck mode (ConLeche.pureFns mode env F) env d x₁ y₁
            else ConLeche.isDefEqCore mode env F d a₂ b₂))) :=
    (hU.and hPP).imp fun _ ⟨⟨h1, h2⟩, h3⟩ => by
      rw [defeqBody_unknown h1 h2, h3]; rfl
  cases pp
  case true =>
    simp only [if_true]
    exact triple_pure_post ⟨hok9, hx09, hp09, Ev.exists (hU'.imp fun _ h => by
      dsimp only; rw [h]; rfl)⟩
  simp only [Bool.false_eq_true, ↓reduceIte] at hU' ⊢
  have hdx₁ := denote_ext ha₁ hx9
  have hdy₁ := denote_ext hb₁ hx9
  -- the two projection-head tests
  refine triple_seq (headIsProj_spec s9 a₁ x₁ hok9 hdx₁) ?_
  rintro pa s10 ⟨hs10, rfl⟩
  subst s10
  refine triple_seq (headIsProj_spec s9 b₁ y₁ hok9 hdy₁) ?_
  rintro pb s10 ⟨hs10, rfl⟩
  subst s10
  split
  · -- neither side is projection-headed: the stuck comparison
    rename_i hnp
    exact defeqStuck_spec henv hμ hsim d s₀ s9 a₁ b₁ x₁ y₁ hok9 hx09 hp09 hdx₁ hdy₁
      hwx₁ hwy₁ _ (hU'.imp fun _ h r hr => by rw [h, if_pos hnp]; exact hr)
  rename_i hnp
  -- the full `whnfCore` of both sides
  refine triple_seq (hsim.whnfCore (c := false) s9 d a₁ x₁ hok9 hdx₁ hwx₁) ?_
  rintro a₂ s10 ⟨hok10, hx10, hp10, x₂, hdx₂, hwx₂, F10, hF10⟩
  refine triple_seq (hsim.whnfCore (c := false) s10 d b₁ y₁ hok10
    (denote_ext hdy₁ hx10) hwy₁) ?_
  rintro b₂ s11 ⟨hok11, hx11, hp11, y₂, hdy₂, hwy₂, F11, hF11⟩
  have hW1 : Ev (fun F => ConLeche.whnfCore mode env F d x₁ false = .ok x₂) :=
    Ev.of_mono (fun hle h => ConLeche.whnfCore_mono hle h) ⟨F10, hF10⟩
  have hW2 : Ev (fun F => ConLeche.whnfCore mode env F d y₁ false = .ok y₂) :=
    Ev.of_mono (fun hle h => ConLeche.whnfCore_mono hle h) ⟨F11, hF11⟩
  have hx011 := (hx09.trans hx10).trans hx11
  have hp011 : s11.pins = s₀.pins := hp11.trans (hp10.trans hp09)
  have hwf11 := hok11.state.wf
  have hdx₂' := denote_ext hdx₂ hx11
  have hdx₁' := denote_ext hdx₁ (hx10.trans hx11)
  have hdy₁' := denote_ext hdy₁ (hx10.trans hx11)
  have heq : (a₂ == a₁ && b₂ == b₁) = (x₂ == x₁ && y₂ == y₁) := by
    rw [beq_of_denoteE hwf11 hdx₂' hdx₁', beq_of_denoteE hwf11 hdy₂ hdy₁']
  rw [heq]
  split
  · -- both unchanged: the stuck comparison
    rename_i hun
    exact defeqStuck_spec henv hμ hsim d s₀ s11 a₁ b₁ x₁ y₁ hok11 hx011 hp011 hdx₁'
      hdy₁' hwx₁ hwy₁ _ (((hU'.and hW1).and hW2).imp fun _ ⟨⟨h, h1⟩, h2⟩ r hr => by
        rw [h, if_neg hnp]
        simp only [h1, h2, bind, Except.bind, hun, if_true]
        exact hr)
  · -- a restart through the knot
    rename_i hun
    exact dq_defeq_exit hsim a₂ b₂ x₂ y₂ hok11 hx011 hp011 hdx₂' hdy₂ hwx₂ hwy₂
      (((hU'.and hW1).and hW2).imp fun _ ⟨⟨h, h1⟩, h2⟩ r hr => by
        rw [h, if_neg hnp]
        simp only [h1, h2, bind, Except.bind, hun, Bool.false_eq_true, if_false]
        exact hr)

/-- con-leche: ConLeche/Verify/Cached/DiscC5.lean defeqBodyC_sim — **THEOREM 1
for `defeqBody`**: `defeqBody_at` at the two subjects' denotations, one fuel
up (`isDefEqCore_succ`). -/
theorem defeqBody_spec {fe : IFEnv} {fuel : Nat}
    (henv : ConLeche.EnvWF env) (hμ : mode.verifiedChecks = true)
    (hsim : KnotSpec mode env fe fuel) :
    BodySpecV mode env fe (defeqBody mode (coreKnot mode fe id fuel) fe)
      (ConLeche.isDefEqCore mode env) := by
  intro s₀ d i j a b hok hda hdb hwa hwb
  refine triple_mono (defeqBody_at henv hμ hsim d s₀ i j a b hok hda hdb hwa hwb) ?_
  rintro r s' ⟨hok', hx', hp', F, hF⟩
  exact ⟨hok', hx', hp', F + 1, by rw [ConLeche.isDefEqCore_succ]; exact hF⟩

end Body

/-! ## 4. The axiom census -/

section Census

#print axioms defeqBinders_spec
#print axioms quickDefEq_spec
#print axioms defeqOffset_spec
#print axioms tryUnfoldProjApp_spec
#print axioms lazyDeltaStep_spec
#print axioms lazyDeltaReduction_spec
#print axioms defeqStuck_spec
#print axioms lazyDeltaProjReduction_spec
#print axioms defeqProjPair_spec
#print axioms defeqBody_at
#print axioms defeqBody_spec

end Census

end ConRon.Bridge.Core

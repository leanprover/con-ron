/-
# `ConRon.Bridge.Core.Walks.ProjCore` — the projection rule on a reduced scrutinee

con-leche's `reduceProjCore` (the official kernel's `reduce_proj_core`) is
the projection rule on a reduced scrutinee, shared by `whnfCoreBody`'s
`.proj` clause and the definitional equality's `lazyDeltaProjReduction`.  The
twin ports it as one walk, and this module proves it once, as a standalone
walk theorem both callers apply.

| theorem | what it is |
|---|---|
| `projRuleFn`, `reduceProjCore_eq` | con-leche's function as the literal expansion and ONE equation over tags and projections |
| `reduceProjCoreFueled_mono` | fuel monotonicity, from con-leche's `reduceProjCore_mono` |
| `ProjCoreAns.of_lit` | the walk's one exit, as a `grind` lemma over the expansion's answer |
| `reduceProjCore_specA` | the walk, `sym … vcgen … finish`, answer `ProjCoreAns` |
| `reduceProjCore_spec` | **THEOREM 1 for `reduceProjCore`**, in `SimOOp` form |

The walk's callees: `projLitToCtor_spec`, `projAnsAt`,
`getAppFn_spec`, the head's `view`, `getAppArgs_spec`, `viewLsLen`,
`IProjEntry.fireOk_specA`, `internE (.bvar 0)`, `projCertAt_specA`.
-/
import ConRon.Bridge.Core.Walks.ProjLit
import ConLeche.Verify.BetaSpine

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. con-leche's `reduceProjCore` as one equation

The rule after the literal expansion is a pure function of the expanded
scrutinee (`projRuleFn`), written over the tag and projections `grind`
reads, so that the walk's answer is ONE equation (`reduceProjCore_eq`). -/

/-- con-leche: ConLeche/Kernel/Core.lean:905-925 reduceProjCore — the rule on
the expanded scrutinee `v`: the table entry for `(nm, k)`, the head
constant's guards, the certificate, the selected field. -/
def projRuleFn (mode : CheckMode) (env : Env) (nm : Name) (k : Nat) (v : Expr) :
    Option Expr :=
  if (env.findProj? nm k).isSome = true ∧ exprTag v.getAppFn = ETag.const ∧
      exprConstName v.getAppFn = (projOf (env.findProj? nm k)).ctor ∧
      k < (projOf (env.findProj? nm k)).numFields ∧
      v.getAppArgs.length = (projOf (env.findProj? nm k)).numParams +
        (projOf (env.findProj? nm k)).numFields ∧
      (exprConstLevels v.getAppFn).length = (projOf (env.findProj? nm k)).levelParams.length ∧
      (projOf (env.findProj? nm k)).fireOk (exprConstLevels v.getAppFn) = true ∧
      ConLeche.projCertAt env mode.verifiedChecks (exprConstName v.getAppFn) v.getAppArgs = true
  then some (v.getAppArgs.getD ((projOf (env.findProj? nm k)).numParams + k) (.bvar 0))
  else none
attribute [bridge_grind =] projRuleFn

/-- con-leche: ConLeche/Kernel/Core.lean:905-925 reduceProjCore — the
function is the literal expansion followed by `projRuleFn`. -/
theorem reduceProjCore_eq (F d : Nat) (nm : Name) (k : Nat) (c : Expr) :
    ConLeche.reduceProjCoreFueled mode env F d nm k c =
      (ConLeche.projLitToCtorFueled mode env F d c).bind
        (fun v => .ok (projRuleFn mode env nm k v)) := by
  simp only [ConLeche.reduceProjCoreFueled, ConLeche.reduceProjCore,
    ConLeche.projLitToCtorFueled, bind, Except.bind]
  cases ConLeche.projLitToCtor (ConLeche.pureFns mode env F) env d c with
  | error e => rfl
  | ok v =>
    simp only [projRuleFn]
    cases hf : env.findProj? nm k with
    | none => simp [pure, Except.pure]
    | some p =>
      simp only [projOf, Option.isSome_some, true_and]
      cases hg : v.getAppFn with
      | const n us =>
        simp only [exprTag, exprConstName, exprConstLevels, true_and]
        by_cases hgd : n = p.ctor ∧ k < p.numFields ∧
            v.getAppArgs.length = p.numParams + p.numFields ∧
            us.length = p.levelParams.length ∧ p.fireOk us = true
        · cases ConLeche.projCertAt env mode.verifiedChecks n v.getAppArgs <;>
            simp [hgd, pure, Except.pure]
        · have hgd' : ¬ (n = p.ctor ∧ k < p.numFields ∧
              v.getAppArgs.length = p.numParams + p.numFields ∧
              us.length = p.levelParams.length ∧ p.fireOk us = true ∧
              ConLeche.projCertAt env mode.verifiedChecks n v.getAppArgs = true) :=
            fun h => hgd ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
          simp only [hgd, hgd', ite_false, pure, Except.pure]
      | _ => simp [exprTag, pure, Except.pure, ETag.const, ETag.bvar, ETag.fvar, ETag.sort,
          ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj]

/-- con-leche: ConLeche/Verify/BetaSpine.lean:466 reduceProjCore_mono — at
the pure knot. -/
theorem reduceProjCoreFueled_mono {F F' d i : Nat} {sn : Name} {c : Expr}
    (hle : F ≤ F') {o : Option Expr}
    (h : ConLeche.reduceProjCoreFueled mode env F d sn i c = .ok o) :
    ConLeche.reduceProjCoreFueled mode env F' d sn i c = .ok o :=
  ConLeche.reduceProjCore_mono hle h

/-! ## 2. The answer and the callees in answer shape -/

/-- con-leche: ConLeche/Kernel/Core.lean:905-925 reduceProjCore — **the
answer** of the walk (a named predicate: `SimOOp` at the pure call, its
`fun` hidden from `grind`). -/
def ProjCoreAns (mode : CheckMode) (env : Env) (d : Nat) (nm : Name) (k : Nat) (c : Expr)
    (st : EStore) (r : Option EIdx) : Prop :=
  SimOOp (fun F => ConLeche.reduceProjCoreFueled mode env F d nm k c) d st r

/-- con-leche: none — a literal expansion's answer denotes. -/
theorem ProjLitAns.isSome {d : Nat} {x : Expr} {st : EStore} {r : EIdx}
    (h : ProjLitAns mode env d x st r) : (denoteE st r).isSome = true := by
  obtain ⟨v, hv, _⟩ := h
  rw [hv]; rfl
grind_pattern [bridge_grind] ProjLitAns.isSome => ProjLitAns mode env d x st r

/-- con-leche: ConLeche/Kernel/Core.lean:905-925 reduceProjCore — **the
walk's one exit**: the expansion answered `e`, and the walk's answer denotes
`projRuleFn` at `e`'s denotation (at the walk's final store `st₂`). -/
theorem ProjCoreAns.of_lit {d : Nat} {nm : Name} {k : Nat} {c : Expr}
    {st₁ st₂ : EStore} {e : EIdx} {r : Option EIdx}
    (hl : ProjLitAns mode env d c st₁ e)
    (hr : denoteEO st₂ r = some ((denoteE st₁ e).bind (projRuleFn mode env nm k))) :
    ProjCoreAns mode env d nm k c st₂ r := by
  obtain ⟨v, hv, hwv, F, hF⟩ := hl
  rw [hv, Option.bind_some] at hr
  refine ⟨_, hr, fun y hy => ?_, F, ?_⟩
  · simp only [projRuleFn] at hy
    split at hy
    · cases hy
      rename_i hg
      have hj : (projOf (env.findProj? nm k)).numParams + k < v.getAppArgs.length := by
        omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      exact Expr.WScoped.getAppArgs hwv _ (List.getElem_mem _)
    · cases hy
  · dsimp only at hF ⊢
    rw [reduceProjCore_eq, hF]; rfl
grind_pattern [bridge_grind] ProjCoreAns.of_lit =>
  ProjCoreAns mode env d nm k c st₂ r, ProjLitAns mode env d c st₁ e

/-- con-leche: ConLeche/Kernel/Core.lean:890-892 projCertAt — the
certificate at optional subjects (one equation at `some`). -/
def projCertAtO (env : Env) (verified : Bool) : Option Name → Option (List Expr) → Bool
  | some cn, some xs => ConLeche.projCertAt env verified cn xs
  | _, _ => false

/-- con-leche: none — `projCertAtO` at denoting subjects. -/
@[bridge_grind =] theorem projCertAtO_some (verified : Bool) (cn : Name) (xs : List Expr) :
    projCertAtO env verified (some cn) (some xs) = ConLeche.projCertAt env verified cn xs := rfl

/-- con-leche: ConLeche/Kernel/Core.lean:890-892 projCertAt — `projCertAt_spec`
in answer shape: the certificate at whatever the handles denote. -/
theorem projCertAt_specA (s₀ : AState) (hok : CheckOK mode env fe s₀)
    (verified : Bool) (c : NIdx) (args : List EIdx)
    (hc : (denoteN s₀.store.ns c).isSome = true)
    (hargs : (Frontend.denoteEList s₀.store args).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.projCertAt fe verified c args
    ⦃fun b s' => s' = s₀ ∧ b = projCertAtO env verified (denoteN s₀.store.ns c)
        (Frontend.denoteEList s₀.store args); ⊤⦄ := by
  obtain ⟨cn, hcn⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp hargs
  rw [hcn, hxs]
  exact projCertAt_spec s₀ hok verified c args cn xs hcn hxs

/-! ## 3. The walk theorem -/

section Walk

/-! The guard compares the head's constant handle with the entry's: the name
handles as `idxOfName` (`Bridge/Grind.lean` §6), for this walk only. -/

local grind_pattern [bridge_grind] nameIdx => denoteN st.ns n
local grind_pattern [bridge_grind] NameIdx.some => NameIdx st n (some nm)

/-- con-leche: ConLeche/Kernel/Core.lean:978-1010 reduceProjCore — the walk
in answer shape (`ProjCoreAns`). -/
theorem reduceProjCore_specA {fuel : Nat}
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (sn : NIdx) (k : Nat) (c : EIdx)
    (nm : Name) (ce : Expr)
    (hok : CheckOK mode env fe s₀) (hsn : denoteN s₀.store.ns sn = some nm)
    (hden : denoteE s₀.store c = some ce) (hw : Expr.WScoped d ce) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.reduceProjCore mode (coreKnot mode fe id fuel) fe d sn k c
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ProjCoreAns mode env d nm k ce s'.store r; ⊤⦄ := by
  sym only [bridge_grind, Option.getD_some] =>
    vcgen [ConRon.Arena.reduceProjCore, projLitToCtor_spec hsim (x := ce),
      ExprOps.getAppFn_spec, ExprOps.getAppArgs_spec, viewLsLen_spec,
      IProjEntry.fireOk_specA (mode := mode) (env := env) (fe := fe),
      internE_specC (mode := mode) (env := env) (fe := fe),
      projCertAt_specA (mode := mode) (env := env) (fe := fe)] <;> finish

end Walk

/-- con-leche: ConLeche/Kernel/Core.lean:978-1010 reduceProjCore — **THEOREM
1 for `reduceProjCore`**: at a scrutinee handle `c` denoting a well-scoped
`ce` and a structure name `sn` denoting `nm`, the twin's projection rule
answers what con-leche's `reduceProjCore` answers at some fuel — `none` when
the rule does not fire, and otherwise the selected field, well-scoped.  The
walk both `whnfCoreBody`'s `.proj` clause and `lazyDeltaProjReduction`
consume (`reduceProjCore_specA`; `ProjCoreAns` is `SimOOp` at the pure
call). -/
theorem reduceProjCore_spec {fuel : Nat} (_henv : ConLeche.EnvWF env)
    (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (sn : NIdx) (k : Nat) (c : EIdx)
    (nm : Name) (ce : Expr)
    (hok : CheckOK mode env fe s₀) (hsn : denoteN s₀.store.ns sn = some nm)
    (hden : denoteE s₀.store c = some ce) (hw : Expr.WScoped d ce) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.reduceProjCore mode (coreKnot mode fe id fuel) fe d sn k c
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimOOp (fun F => ConLeche.reduceProjCoreFueled mode env F d nm k ce) d
          s'.store r; ⊤⦄ :=
  reduceProjCore_specA hsim s₀ d sn k c nm ce hok hsn hden hw

section Census

#print axioms reduceProjCore_eq
#print axioms reduceProjCore_specA
#print axioms reduceProjCore_spec

end Census

end ConRon.Bridge.Core

/-
# `ConRon.Bridge.Checker.TypePins` — the type pins of the `Nat.div`/`Nat.mod` gate

Each pin variant carries, per pin-certified operation, the types its toolchain
gives the few constants the certificates use whose types differ between
supported toolchains (con-leche's task #364).  The gate checks them twice:
syntactically in the variant's pin guard (`typePinsGuard`, the last clause of
`divModPinGuard`) and by definitional equality before the value pin
(`checkTypePins`, the first step of `checkDivModPinAt`).  This module is their
bridge: the stored type a pin is compared against (`typePinStored_spec`), one
type pin's guard and the list of them (`typePinGuard_spec`,
`typePinsGuard_spec`), and the comparison loop (`checkTypePins_spec`), each a
`sym only [bridge_grind, …] => vcgen […] <;> finish` proof over the callees'
specs.

**The answers are named.**  The guard's answer is `TypePinGuardP`, con-leche's
`List.all` closure body as a function of the pin's two components, and the
list's is `typePinsGuardP`, the `List.all` itself as a recursion
(`typePinsGuardP_eq` is the bridge back to the closure).  The comparison's
answer is `SimBOp (typePinsOp …)`: con-leche's `checkTypePins` at some fuel,
with one `SimBOp` lemma per clause (`typePins_nil_sim`, `typePins_cons_true_sim`,
`typePins_cons_false_sim`), the fuels merged by `checkTypePins_mono`.
-/
import ConRon.Bridge.Checker.DeclVal
import ConRon.Bridge.Core.Walks.IotaLeaves
import ConRon.Bridge.Core.Walks.Nat

open ConLeche ConRon.Arena Std.WP

namespace ConRon.Bridge

set_option autoImplicit false
set_option experimental.vcgen true

open scoped Lean.Order

open ConRon.Bridge.Core

variable {μ : CheckMode} {env : Env} {fe : IFEnv}

/-! ## The pure side, as equations and named answers -/

/-- con-leche: ConLeche/Kernel/Checker.lean:154-161 typePinStored — as ONE
equation over the lookup's projections (no `match` for `grind` to split). -/
theorem typePinStored_eq (env : Env) (n : ConLeche.Name) :
    ConLeche.typePinStored env n =
      if (env.find? n).isSome then (cValP (env.find? n)).type else .sort .zero := by
  unfold ConLeche.typePinStored
  cases env.find? n <;> rfl

/-- con-leche: ConLeche/Kernel/Checker.lean:311-321 divModPinGuard — the
body of the type-pin clause's `List.all` closure, at one pin. -/
def TypePinGuardP (env : Env) (n : ConLeche.Name) (ty : Expr) : Bool :=
  (env.find? n).isSome && !(ConLeche.typePinStored env n).hasFvar &&
    ty.looseBVarsBounded 0 && !ty.hasFvar && ty.constsResolve env

/-- con-leche: ConLeche/Kernel/Checker.lean:311-321 divModPinGuard — the
type-pin clause's `List.all`, as a recursion. -/
def typePinsGuardP (env : Env) : List (ConLeche.Name × Expr) → Bool
  | [] => true
  | p :: rest => TypePinGuardP env p.1 p.2 && typePinsGuardP env rest

/-- con-leche: ConLeche/Kernel/Checker.lean:311-321 divModPinGuard — the
recursion is the closure's `List.all`. -/
theorem typePinsGuardP_eq (env : Env) (tps : List (ConLeche.Name × Expr)) :
    typePinsGuardP env tps = tps.all fun p =>
      (env.find? p.1).isSome && !(ConLeche.typePinStored env p.1).hasFvar &&
        p.2.looseBVarsBounded 0 && !p.2.hasFvar && p.2.constsResolve env := by
  induction tps with
  | nil => rfl
  | cons p rest ih => simp only [typePinsGuardP, TypePinGuardP, List.all_cons, ih]

/-- con-leche: ConLeche/Kernel/Checker.lean:332-340 checkTypePins — the
comparison loop as a fueled family (`SimBOp`'s argument). -/
def typePinsOp (μ : CheckMode) (env : Env) (tps : List (ConLeche.Name × Expr)) :
    Nat → CheckM Bool :=
  fun F => ConLeche.checkTypePins (ConLeche.fueledOps μ F) env tps

/-- con-leche: ConLeche/Verify/BridgeDecl.lean checkTypePins_datF — the loop
is monotone in its fuel. -/
theorem checkTypePins_mono {tps : List (ConLeche.Name × Expr)} {r : Bool} {F F' : Nat}
    (hle : F ≤ F')
    (h : ConLeche.checkTypePins (ConLeche.fueledOps μ F) env tps = .ok r) :
    ConLeche.checkTypePins (ConLeche.fueledOps μ F') env tps = .ok r := by
  rw [← ConLeche.checkTypePins_datF (mode := μ)] at h ⊢
  exact (ConLeche.checkTypePins (ConLeche.fueledOpsM μ) env tps).property hle h

/-- con-leche: ConLeche/Kernel/Checker.lean:332-340 checkTypePins — the empty
list (at any fuel). -/
theorem typePins_nil_sim : SimBOp (typePinsOp μ env []) true := ⟨0, rfl⟩
grind_pattern [bridge_grind] typePins_nil_sim => typePinsOp μ env []

/-- con-leche: ConLeche/Kernel/Checker.lean:332-340 checkTypePins — the head
pin agrees: the answer is the tail's, the two fuels merged. -/
theorem typePins_cons_true_sim {n : ConLeche.Name} {ty : Expr}
    {rest : List (ConLeche.Name × Expr)} {r : Bool}
    (h : SimV (ConLeche.isDefEqCore μ env) 0 (ConLeche.typePinStored env n) ty true)
    (ht : SimBOp (typePinsOp μ env rest) r) :
    SimBOp (typePinsOp μ env ((n, ty) :: rest)) r := by
  obtain ⟨F₁, h⟩ := h
  obtain ⟨F₂, ht⟩ := ht
  refine ⟨max F₁ F₂, ?_⟩
  simp only [typePinsOp, ConLeche.checkTypePins, ConLeche.fueledOps,
    ConLeche.isDefEqCore_mono (Nat.le_max_left _ _) h, bind, Except.bind, ite_true]
  exact checkTypePins_mono (Nat.le_max_right _ _) ht
grind_pattern [bridge_grind] typePins_cons_true_sim =>
  SimV (ConLeche.isDefEqCore μ env) 0 (ConLeche.typePinStored env n) ty true,
  SimBOp (typePinsOp μ env rest) r, typePinsOp μ env ((n, ty) :: rest)

/-- con-leche: ConLeche/Kernel/Checker.lean:332-340 checkTypePins — the head
pin disagrees: so does the list. -/
theorem typePins_cons_false_sim {n : ConLeche.Name} {ty : Expr}
    {rest : List (ConLeche.Name × Expr)}
    (h : SimV (ConLeche.isDefEqCore μ env) 0 (ConLeche.typePinStored env n) ty false) :
    SimBOp (typePinsOp μ env ((n, ty) :: rest)) false := by
  obtain ⟨F, h⟩ := h
  refine ⟨F, ?_⟩
  simp only [typePinsOp, ConLeche.checkTypePins, ConLeche.fueledOps, h, bind,
    Except.bind, Bool.false_eq_true, ite_false]
  rfl
grind_pattern [bridge_grind] typePins_cons_false_sim =>
  SimV (ConLeche.isDefEqCore μ env) 0 (ConLeche.typePinStored env n) ty false,
  typePinsOp μ env ((n, ty) :: rest)

/-! ## The callees at the tier's invariant -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1709-1710 hasFvarFast —
`ExprOps/Ranges.lean`'s `hasFvarFast_spec` at the tier's invariant
(`CheckOK.mono`). -/
theorem hasFvarFast_specC (fuel : Nat) (s₀ : AState) (e : EIdx)
    (hok : CheckOK μ env fe s₀) (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => s = s₀⦄ hasFvarFast fuel e
    ⦃fun r s' => CheckOK μ env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins ∧
        RelV Expr.hasFvar s₀.store e r; ⊤⦄ :=
  triple_mono (ExprOps.hasFvarFast_spec fuel s₀ e hok.state hden)
    (fun _ _ ⟨hst, hc, hp, hr⟩ =>
      ⟨hok.mono (by rw [stateOK_eq, hst]; exact hok.state.wf)
        (by rw [hst]; exact Ext.refl _) hc hp, hst, hp, hr⟩)

/-- con-leche: ConLeche/Kernel/DeclCheck.lean:197-199 Expr.constsResolveFFast
— `Bridge/Checker/Names.lean`'s `constsResolveFFast_run` as a triple, at the
tier's invariant. -/
theorem constsResolveFFast_specC (s₀ : AState) (e : EIdx)
    (hok : CheckOK μ env fe s₀) (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => s = s₀⦄ constsResolveFFast fe e
    ⦃fun r s' => CheckOK μ env fe s' ∧ s'.store = s₀.store ∧ s'.pins = s₀.pins ∧
        RelV (Expr.constsResolve env) s₀.store e r; ⊤⦄ :=
  AM.triple_of_run_at fun r s' h => by
    obtain ⟨x, hd⟩ := Option.isSome_iff_exists.mp hden
    obtain ⟨h1, h2, h3, h4⟩ := constsResolveFFast_run hok hd h
    exact ⟨hok.mono (by rw [stateOK_eq, h1]; exact hok.state.wf)
      (by rw [h1]; exact Ext.refl _) h2 h3, h1, h3,
      fun y hy => by rw [hd] at hy; cases hy; exact h4⟩

/-! ## The stored type -/

/-- con-leche: none — `denoteEView` at a `sort` view (the vocabulary of
`Bridge/Grind.lean` §6 has the other constructors). -/
theorem denoteEView_sort_eq (st : EStore) (u : LIdx) :
    denoteEView st (.sort u) = (denoteL st.ls u).map Expr.sort := rfl

/-- con-leche: ConLeche/Kernel/Checker.lean:154-161 typePinStored — the
stored type a type pin is compared against denotes con-leche's: the found
constant's type, or the `Sort 0` the twin interns for an absent one. -/
theorem typePinStored_spec (s₀ : AState) (n : NIdx) (nm : ConLeche.Name)
    (hok : CheckOK μ env fe s₀) (hn : denoteN s₀.store.ns n = some nm) :
    ⦃fun s => s = s₀⦄ Arena.typePinStored fe n
    ⦃fun r s' => CheckOK μ env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        denoteE s'.store r = some (ConLeche.typePinStored env nm); ⊤⦄ := by
  sym only [bridge_grind, typePinStored_eq, denoteCV_type, denoteEView_sort_eq] =>
    vcgen [Arena.typePinStored, Arena.zeroLevel, pinZeroLevel_spec s₀ hok.pins,
      internE_specC (mode := μ) (env := env) (fe := fe)] <;> finish

/-! ## The guard -/

/-- con-leche: ConLeche/Kernel/Checker.lean:311-321 divModPinGuard — one
type pin's guard answers con-leche's closure body at the pin's denotation. -/
theorem typePinGuard_spec (s₀ : AState) (n : NIdx) (ty : EIdx) (nm : ConLeche.Name)
    (T : Expr) (hok : CheckOK μ env fe s₀) (hn : denoteN s₀.store.ns n = some nm)
    (ht : denoteE s₀.store ty = some T) :
    ⦃fun s => s = s₀⦄ Arena.typePinGuard fe n ty
    ⦃fun r s' => CheckOK μ env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        r = TypePinGuardP env nm T; ⊤⦄ := by
  sym only [bridge_grind, TypePinGuardP] =>
    vcgen [Arena.typePinGuard, typePinStored_spec s₀ n nm hok hn,
      hasFvarFast_specC (μ := μ) (env := env) (fe := fe),
      looseBVarsBoundedFast_specC (mode := μ) (env := env) (fe := fe),
      constsResolveFFast_specC (μ := μ) (env := env) (fe := fe)] <;> finish

/-- con-leche: ConLeche/Kernel/Checker.lean:311-321 divModPinGuard — the
type-pin clause: the list of guards answers `typePinsGuardP` at the list's
denotation. -/
theorem typePinsGuard_spec :
    ∀ (tps : List (NIdx × EIdx)) (tpsP : List (ConLeche.Name × Expr)) (s₀ : AState),
      CheckOK μ env fe s₀ → TypePinsDenote s₀.store tps tpsP →
      ⦃fun s => s = s₀⦄ Arena.typePinsGuard fe tps
      ⦃fun r s' => CheckOK μ env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
          r = typePinsGuardP env tpsP; ⊤⦄ := by
  intro tps
  induction tps with
  | nil =>
    intro tpsP s₀ hok hd
    cases tpsP with
    | nil => sym only [bridge_grind, typePinsGuardP] => vcgen [Arena.typePinsGuard] <;> finish
    | cons _ _ => exact hd.elim
  | cons p ps ih =>
    intro tpsP s₀ hok hd
    cases tpsP with
    | nil => exact hd.elim
    | cons q qs =>
      obtain ⟨h1, h2, h3⟩ := hd
      have step := fun s₁ hk hx => ih qs s₁ hk (TypePinsDenote.mono hx _ _ h3)
      clear ih h3
      sym only [bridge_grind, typePinsGuardP] =>
        vcgen [Arena.typePinsGuard, typePinGuard_spec s₀ p.1 p.2 q.1 q.2 hok h1 h2,
          step] <;> finish

/-! ## The comparison -/

/-- con-leche: ConLeche/Kernel/Checker.lean:332-340 checkTypePins — **the
type pins compared**: each stored type against its pin by `KnotSpec.defeq`
at depth 0, the answer con-leche's at some fuel.  Both sides of every
comparison are closed (`hc`, which the variant's guard provides). -/
theorem checkTypePins_spec (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) :
    ∀ (tps : List (NIdx × EIdx)) (tpsP : List (ConLeche.Name × Expr)) (s₀ : AState),
      CheckOK μ env fe s₀ → TypePinsDenote s₀.store tps tpsP →
      (∀ p ∈ tpsP, (ConLeche.typePinStored env p.1).hasFvar = false ∧
        p.2.hasFvar = false) →
      ⦃fun s => s = s₀⦄ Arena.checkTypePins μ fe tps
      ⦃fun r s' => CheckOK μ env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
          SimBOp (typePinsOp μ env tpsP) r; ⊤⦄ := by
  have hknot := hk.knot env fe henv
  intro tps
  induction tps with
  | nil =>
    intro tpsP s₀ hok hd _
    cases tpsP with
    | nil => sym only [bridge_grind] => vcgen [Arena.checkTypePins] <;> finish
    | cons _ _ => exact hd.elim
  | cons p ps ih =>
    intro tpsP s₀ hok hd hc
    cases tpsP with
    | nil => exact hd.elim
    | cons q qs =>
      obtain ⟨h1, h2, h3⟩ := hd
      have hw1 : Expr.WScoped 0 (ConLeche.typePinStored env q.1) :=
        ConLeche.Expr.WScoped.of_not_hasFvar (hc q (by simp)).1
      have hw2 : Expr.WScoped 0 q.2 :=
        ConLeche.Expr.WScoped.of_not_hasFvar (hc q (by simp)).2
      have step := fun s₁ hk hx =>
        ih qs s₁ hk (TypePinsDenote.mono hx _ _ h3) (fun r hr => hc r (by simp [hr]))
      have dq : ∀ (s₁ : AState) (i : EIdx), CheckOK μ env fe s₁ → Ext s₀.store s₁.store →
          denoteE s₁.store i = some (ConLeche.typePinStored env q.1) →
          ⦃fun s => s = s₁⦄ Arena.isDefEqCore μ fe Arena.checkFuel 0 i p.2
          ⦃fun x s' => CheckOK μ env fe s' ∧ Ext s₁.store s'.store ∧ s'.pins = s₁.pins ∧
            SimV (ConLeche.isDefEqCore μ env) 0 (ConLeche.typePinStored env q.1) q.2 x; ⊤⦄ :=
        fun s₁ i hk hx hi =>
          hknot.defeq s₁ 0 i p.2 (ConLeche.typePinStored env q.1) q.2 hk hi
            (denote_ext h2 hx) hw1 hw2
      clear ih h3 hc
      sym only [bridge_grind] =>
        vcgen [Arena.checkTypePins,
          typePinStored_spec s₀ p.1 q.1 hok h1, dq, step] <;> finish

end ConRon.Bridge

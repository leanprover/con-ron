/-
# `ConRon.Bridge.Inductives.BlockWF` — the uniform route keeps `EnvWF`

A PURE con-leche-side result (task #105): an accepting run of con-leche's
`checkBlock` (and of `checkDecl` at an `.indDecl` that is not a pinned basis
block) at the fueled operations yields a well-formed environment.  No twin,
no `AState`.

Upstream proves the same chain only through the cached driver
(`ConLeche/Verify/Cached/GenRecC.lean`'s `checkBlockKS_run` /
`checkBlockPassS_run` / `checkBlockTailS_run`); here it is stated off the
PURE runs directly, with the same ingredients: `direct_block_inds_wf`,
`direct_block_ctors_wf`, `genRecCheck_recsWF`, `direct_table_wf`.
-/
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Cached.GenRecC
import ConLeche.Verify.BridgeDecl
import ConLeche.Semantics.Bridge.Sound
import ConLeche.Kernel.CheckDecl

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche

/-- con-leche: Kernel/Inductives/BlockTail.lean:111 checkBlockTables — the
projection tables keep well-formedness (`direct_table_wf` at every
structure-like member). -/
theorem checkBlockTables_envWF (p : BlockShape) :
    ∀ (l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))) {env env' : Env},
      EnvWF env → checkBlockTables (m := CheckM) p l env = .ok env' → EnvWF env'
  | [], env, env', henv, h => by
    simp only [checkBlockTables, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ henv
  | (ms, ctorsA, sortss) :: rest, env, env', henv, h => by
    obtain ⟨env₁, h1, h⟩ := exceptBind_ok h
    refine checkBlockTables_envWF p rest ?_ h
    split at h1
    · split at h1
      · exact direct_table_wf henv h1
      · simp only [pure, Except.pure, Except.ok.injEq] at h1
        exact h1 ▸ henv
    · simp only [pure, Except.pure, Except.ok.injEq] at h1
      exact h1 ▸ henv

/-- con-leche: Kernel/Inductives/BlockTail.lean:62 checkBlockPass — the
pass's formers' environment, and that environment with the constructors
consed, are well-formed (`direct_block_inds_wf`, `direct_block_ctors_wf`). -/
theorem checkBlockPass_envWF {μ : CheckMode} {F : Nat} {env : Env} {p₀ : BlockParts}
    {isRec : Bool} {q : BlockPass Env} (henv : EnvWF env)
    (h : checkBlockPass (fueledOps μ F) env p₀ isRec = .ok q) :
    EnvWF q.env₁ ∧ EnvWF (consBlockCtors q.p.nP q.ctorsAs q.env₁) := by
  unfold checkBlockPass at h
  obtain ⟨⟨env₁, cvTas, p₁⟩, hI, h⟩ := exceptBind_ok h
  obtain ⟨henv₁, -⟩ := direct_block_inds_wf henv hI
  obtain ⟨⟨ctorsAs, sortsss⟩, hC, h⟩ := exceptBind_ok h
  have henv₂ := direct_block_ctors_wf (nP := (p₀.complete p₁).nP) henv₁ hC
  obtain ⟨_, -, h⟩ := exceptBind_ok h
  obtain ⟨_, -, h⟩ := exceptBind_ok h
  obtain ⟨⟨_, _, _⟩, -, h⟩ := exceptBind_ok h
  obtain ⟨_, -, h⟩ := exceptBind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨henv₁, henv₂⟩

/-- con-leche: Kernel/Inductives/BlockTail.lean:62 checkBlockPass — the pass's
canonical parameters are one per block parameter (`blockNestCtx` opens the head
former's `nP` binders), and every class it checked as a major is, at an outside
inductive, at parameters below the block's (`targetMajorOf`'s outside arm).
These are `genRecCheck_recsWF`'s premises; upstream reads them off its cached
run (`checkBlockPassS_run`), here off the pure one. -/
theorem checkBlockPass_classes {μ : CheckMode} {F : Nat} {env : Env} {p₀ : BlockParts}
    {isRec : Bool} {q : BlockPass Env}
    (h : checkBlockPass (fueledOps μ F) env p₀ isRec = .ok q) :
    q.params.length = q.p.nP ∧ ∀ M ∈ q.cls, ClassOutParams q.p.nP M := by
  obtain ⟨p₁, ctx, holes, -, -, -, -, hctx, hcls, -, -, hpar, -, hp⟩ := checkBlockPass_inv h
  obtain ⟨_, fvsP, _, -, hop, rfl, -⟩ := blockNestCtx_inv hctx
  refine ⟨?_, fun M hM => ?_⟩
  · rw [hpar, hp]
    exact ConLeche.Verify.openPisAtFvars_length _ hop
  · obtain ⟨C⟩ := checkBlockClasses_run hcls
    obtain ⟨hlen, hall⟩ := classMajors_run C.hMs
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hM
    have hik : i < C.keys.length := by
      have := (List.getElem?_eq_some_iff.mp hi).1; omega
    obtain ⟨M', hM', ⟨R⟩⟩ := hall i _ (List.getElem?_eq_getElem hik)
    rw [hi] at hM'
    obtain rfl := Option.some.inj hM'
    intro hMn
    obtain ⟨-, -, -, -, -, -, hl, hsc, -⟩ := R.major.outside_facts hMn
    rw [hp]
    exact ⟨hl, hsc⟩

/-- con-leche: Kernel/Inductives/BlockTail.lean:127 checkBlockTail — from a
pass whose constructors' environment is well-formed, whose parameters are the
block's and whose outside classes sit below them (`checkBlockPass_classes`),
the install after it yields a well-formed environment (`genRecCheck_recsWF`,
then the tables). -/
theorem checkBlockTail_envWF {μ : CheckMode} {F : Nat} {block : List ConstantInfo}
    {q : BlockPass Env} {env' : Env}
    (henv₂ : EnvWF (consBlockCtors q.p.nP q.ctorsAs q.env₁))
    (hpl : q.params.length = q.p.nP) (hcls : ∀ M ∈ q.cls, ClassOutParams q.p.nP M)
    (h : checkBlockTail (fueledOps μ F) block q = .ok env') : EnvWF env' := by
  unfold checkBlockTail at h
  obtain ⟨_, -, h⟩ := exceptBind_ok h
  obtain ⟨out, hR, h⟩ := exceptBind_ok h
  have henv₃ := ConLeche.Cached.genRecCheck_recsWF (mode := μ) henv₂ hR hpl hcls
    (consBlockCtors q.p.nP q.ctorsAs q.env₁).find?
  exact checkBlockTables_envWF _ _ henv₃ h

/-- con-leche: Kernel/Inductives/BlockTail.lean:143 checkBlock — an accepting
run of the uniform install at the fueled operations yields a well-formed
environment. -/
theorem checkBlock_envWF {μ : CheckMode} {F : Nat} {env env' : Env}
    {block : List ConstantInfo} {p : BlockParts} (henv : EnvWF env)
    (h : ConLeche.checkBlock (fueledOps μ F) env block p = .ok env') : EnvWF env' := by
  unfold checkBlock at h
  dsimp only at h
  split at h
  · obtain ⟨q, hP, h⟩ := exceptBind_ok h
    obtain ⟨hpl, hcls⟩ := checkBlockPass_classes hP
    exact checkBlockTail_envWF (checkBlockPass_envWF henv hP).2 hpl hcls h
  · obtain ⟨_, h, -⟩ := exceptBind_ok h
    exact nomatch h

end ConRon.Bridge.Inductives

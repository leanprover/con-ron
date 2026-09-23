/-
# `ConRon.Bridge.Checker.BasisWF` — the pinned blocks are well formed

Task #97-P3-Checker round 10.  `checkDecl`'s basis and quotient arms push a
pinned block (`BasisKind.declsA`), and `DeclOut`'s `envWF` clause needs
`ConstWF` of every constant of it.  con-leche's model tier proves exactly
this, block by block — but INLINE, as the `have hwf1 … hwfN : EnvWF …` steps
of `Model/Basis{Blocks,Eq,Empty,False,Quot}.lean`'s `declBasisPB_*K`, which
prove `Nonempty (EnvModelM …)` and export no `EnvWF` lemma.  There is nothing
to cite, so this module proves local copies (upstream ask: a
`declBasisRun_envWF` beside `DeclBasisRun`).

The proof is not a transcription of the model tier's, which rewrites
`Env.find?` through an abstract tail at every reference.  Here each pinned
constant's `ConstWF` is a CLOSED fact — at the block's own prefix (and, for
the quotient block, the pinned `eqA` it resolves against) — decided by
evaluation, and `constWF_le` (a local copy of `Verify/Cached/BridgeCS4.lean`'s
private `constWF_le'`) moves it to the installed environment, whose lookups
find everything the prefix's do.

This module imports con-leche only: the statement and the proof are pure.
-/
import ConLeche.Semantics.Bridge.Sound
import ConLeche.Kernel.BasisA
import ConLeche.Verify.EnvWF

namespace ConRon.Bridge

open ConLeche ConLeche.Semantics

set_option autoImplicit false

/-- con-leche: ConLeche/Verify/Cached/BridgeCS4.lean:342 constWF_le' (private
there) — transport `ConstWF` along lookup-presence monotonicity. -/
theorem constWF_le {envA envB : Env}
    (hle : ∀ n, (envA.find? n).isSome = true → (envB.find? n).isSome = true)
    {c : ConstantInfo} (h : ConstWF envA c) : ConstWF envB c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩ := h
  refine ⟨h1, h2, Expr.constsResolve_le hle h3, h4, ?_, ?_,
    fun tbl heq =>
      let ⟨hs, hb⟩ := h8 tbl heq
      ⟨hs, fun i b hbi =>
        let ⟨g1, g2, g3, g4⟩ := hb i b hbi
        ⟨g1, g2, Expr.constsResolve_le hle g3, g4⟩⟩, h9⟩
  · intro cv v hint heq
    obtain ⟨g1, g2, g3, g4⟩ := h5 cv v hint heq
    exact ⟨g1, g2, Expr.constsResolve_le hle g3, g4⟩
  · intro cv a b e heq r hr
    obtain ⟨g1, g2, g3, g4, g5⟩ := h6 cv a b e heq r hr
    refine ⟨g1, g2, Expr.constsResolve_le hle g3, g4, ?_⟩
    intro lvls pins hf
    obtain ⟨n1, n2, n3, n4⟩ := g5 lvls pins hf
    refine ⟨n1, n2, ?_, n4⟩
    intro pin hp
    obtain ⟨p1, p2, p3, p4⟩ := n3 pin hp
    exact ⟨p1, p2, Expr.constsResolve_le hle p3, p4⟩

/-- con-leche: none — a rule whose firing mode is decidably not `.nested`
fires no nested certificate (`nomatch` would have to evaluate the mode in the
elaborator, which the pinned recursors' `recRulePlain` tests make slow). -/
theorem RecRuleFire.ne_nested {f : RecRuleFire}
    (h : (match f with | .nested _ _ => true | _ => false) = false)
    (lvls : List Level) (pins : List Expr) : f ≠ .nested lvls pins := by
  intro he; subst he; exact nomatch h

/-- con-leche: ConLeche/Verify/EnvWF.lean:147 ConstWF (the `.recInfo` clause)
— a recursor's rules, all at once, from one Boolean test (the rule list of a
pinned recursor need not be a literal, so the clause cannot be split rule by
rule before evaluation). -/
theorem recRules_ok {env : Env} {lps : List Name} {rules : List RecRule}
    (h : rules.all (fun r => !r.rhs.hasFvar && r.rhs.allLevelParamsDefined lps &&
      r.rhs.constsResolve env && r.rhs.looseBVarsBounded 0 &&
      !(match r.fire with | .nested _ _ => true | _ => false)) = true)
    (P : List Level → List Expr → Prop) :
    ∀ r, r ∈ rules →
      (RecRule.rhs r).hasFvar = false ∧
      (RecRule.rhs r).allLevelParamsDefined lps = true ∧
      (RecRule.rhs r).constsResolve env = true ∧
      (RecRule.rhs r).looseBVarsBounded 0 = true ∧
      ∀ lvls pins, RecRule.fire r = .nested lvls pins → P lvls pins := by
  intro r hr
  have h1 := List.all_eq_true.mp h r hr
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
  obtain ⟨⟨⟨⟨g1, g2⟩, g3⟩, g4⟩, g5⟩ := h1
  refine ⟨g1, g2, g3, g4, fun lvls pins hf => ?_⟩
  rw [hf] at g5
  exact nomatch g5

/-- A closed `ConstWF` goal, at a pinned constant: every clause by evaluation. -/
macro "constWF_closed" : tactic => `(tactic| (
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ?_, ?_, ?_, ?_⟩
  · intro cv v hint heq
    cases heq <;>
      exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · intro cv mI rP rules heq
    cases heq <;> exact recRules_ok (by decide +kernel) _
  · intro tbl heq
    cases heq
  · intro cv caps heq
    cases heq <;> exact ⟨fun h => by first | exact absurd h (by decide +kernel) | decide +kernel,
      fun h => by first | exact absurd h (by decide +kernel) | decide +kernel⟩))

/-- con-leche: ConLeche/Semantics/Decl.lean:66 DeclBasisRun — what a pinned
block resolves against besides itself: the quotient block's types mention the
pinned equality former, which `DeclBasisRun`'s side condition stores. -/
def basisExtra : BasisKind → List ConstantInfo
  | .quotK => [eqA]
  | _ => []

/-- con-leche: ConLeche/Model/Basis{Blocks,Eq,Empty,False,Quot}.lean
declBasisPB_*K (the inline `hwf1 … hwfN`) — **every pinned constant is well
formed at its block** (and the block's extra), a closed fact decided by
evaluation. -/
theorem declsA_constWF (k : BasisKind) :
    ∀ c ∈ k.declsA, ConstWF ⟨k.declsA.reverse ++ basisExtra k⟩ c := by
  intro c hc
  cases k <;>
    simp only [BasisKind.declsA, List.mem_cons, List.not_mem_nil, or_false] at hc <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> constWF_closed

/-! ## The install -/

/-- con-leche: ConLeche/Kernel/BasisA.lean:51 BasisKind.declsA — no pinned
constant is a projection table (`Bridge/Checker/Basis.lean`'s
`basis_declsA_no_proj`, restated here below that module). -/
theorem basis_declsA_noTower (k : BasisKind) :
    ∀ x ∈ BasisKind.declsA k, x.isTowerEntry = false := by
  cases k <;> decide

/-- con-leche: none — a lookup that finds something in a list's tail finds
something in the list. -/
theorem find?_isSome_append_right (pre rest : List ConstantInfo) (n : Name)
    (h : ((⟨rest⟩ : Env).find? n).isSome = true) :
    ((⟨pre ++ rest⟩ : Env).find? n).isSome = true := by
  simp only [Env.find?, List.find?_append] at h ⊢
  cases hp : pre.find? (·.name == n) with
  | none => simpa using h
  | some _ => simp

/-- con-leche: none — a lookup that finds something in a list's front finds
something in the list. -/
theorem find?_isSome_append_left (pre rest : List ConstantInfo) (n : Name)
    (h : ((⟨pre⟩ : Env).find? n).isSome = true) :
    ((⟨pre ++ rest⟩ : Env).find? n).isSome = true := by
  simp only [Env.find?, List.find?_append] at h ⊢
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
  simp [hx]

/-- con-leche: ConLeche/Semantics/Decl.lean:57 BasisInstallRun — the block's
install pushes the block, in order: the environment it reaches is the block
reversed in front of the one it started from. -/
theorem basisInstallRun_consts : ∀ (cs : List ConstantInfo) {e e' : Env},
    BasisInstallRun e cs e' → e'.consts = cs.reverse ++ e.consts
  | [], _, _, h => by simp only [BasisInstallRun] at h; subst h; rfl
  | c :: cs, e, e', h => by
    simp only [BasisInstallRun] at h
    rw [basisInstallRun_consts cs h.2]
    simp

/-- con-leche: ConLeche/Model/Basis{Blocks,Eq,Empty,False,Quot}.lean
declBasisPB_*K (their `hwf1 … hwfN`, inline there) — **a pinned block's
install keeps the environment well formed**: the block's constants are well
formed at the block (`declsA_constWF`), which the installed environment's
lookups subsume, and the old constants' lookups survive the push. -/
theorem declBasisRun_envWF {e e' : Env} {k : BasisKind} (h : DeclBasisRun e k e')
    (hwf : EnvWF e) : EnvWF e' := by
  obtain ⟨hq, hrun⟩ := h
  have hc := basisInstallRun_consts _ hrun
  obtain ⟨cs'⟩ := e'
  simp only at hc
  subst hc
  intro c hc
  rcases List.mem_append.mp hc with hb | ho
  · refine constWF_le (fun n hn => ?_) (declsA_constWF k c (List.mem_reverse.mp hb))
    simp only [Env.find?, List.find?_append] at hn
    cases hp : k.declsA.reverse.find? (·.name == n) with
    | some _ => exact find?_isSome_append_left _ _ n (by simp [Env.find?, hp])
    | none =>
      rw [hp, Option.none_or] at hn
      refine find?_isSome_append_right _ _ n ?_
      cases k with
      | quotK =>
        simp only [basisExtra, List.find?_cons, List.find?_nil] at hn
        split at hn
        · rename_i hnm
          have hnm : eqA.name = n := by simpa using hnm
          rw [← hnm, show eqA.name = eqName from rfl, hq rfl]; rfl
        · simp at hn
      | _ => simp [basisExtra] at hn
  · exact constWF_le (fun n hn => find?_isSome_append_right _ _ n hn) (hwf c ho)

/-! ## The whole step, off the inductive route -/

/-- con-leche: none — **what a step pushed are not projection tables**: the
environment grew by a front of non-tower constants. -/
def NoTowerPush (env env' : Env) : Prop :=
  ∃ newP, env'.consts = newP ++ env.consts ∧ ∀ x ∈ newP, x.isTowerEntry = false

theorem NoTowerPush.refl (env : Env) : NoTowerPush env env :=
  ⟨[], rfl, fun _ h => nomatch h⟩

theorem NoTowerPush.cons (env : Env) (c : ConstantInfo) (hc : c.isTowerEntry = false) :
    NoTowerPush env ⟨c :: env.consts⟩ :=
  ⟨[c], rfl, fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hc⟩

theorem declBasisRun_noTower {e e' : Env} {k : BasisKind} (h : DeclBasisRun e k e') :
    NoTowerPush e e' :=
  ⟨k.declsA.reverse, basisInstallRun_consts _ h.2, fun x hx =>
    basis_declsA_noTower k x (List.mem_reverse.mp hx)⟩

/-- con-leche: ConLeche/Semantics/DeclRun.lean:93 ConstantValRun — the type
half of `ConstWF` at a checked header, stored in the extended environment. -/
theorem constantValRun_typeWF {μ : CheckMode} {F : Nat} {env : Env}
    {cv : ConstantVal} {type' : Expr} (h : ConstantValRun μ F env cv type')
    (c : ConstantInfo) :
    type'.hasFvar = false ∧ type'.allLevelParamsDefined cv.levelParams = true ∧
      type'.constsResolve ⟨c :: env.consts⟩ = true ∧ type'.looseBVarsBounded 0 = true := by
  obtain ⟨-, -, -, -, hb, hf, hann, hlp, hres, -⟩ := h
  obtain ⟨g1, g2⟩ := annotate_syntax hann hf hb
  exact ⟨g1, hlp, Expr.constsResolve_mono hres, g2⟩

/-- con-leche: ConLeche/Semantics/DeclRun.lean:107 ValueFrontRun — the value
half of `ConstWF` at a checked value. -/
theorem valueFrontRun_valueWF {μ : CheckMode} {F : Nat} {env : Env}
    {cv : ConstantVal} {value type' value' : Expr}
    (h : ValueFrontRun μ F env cv value type' value') (c : ConstantInfo) :
    value'.hasFvar = false ∧ value'.allLevelParamsDefined cv.levelParams = true ∧
      value'.constsResolve ⟨c :: env.consts⟩ = true ∧
      value'.looseBVarsBounded 0 = true := by
  obtain ⟨hb, hf, hann, hlp, hres, -⟩ := h
  obtain ⟨g1, g2⟩ := annotate_syntax hann hf hb
  exact ⟨g1, hlp, Expr.constsResolve_mono hres, g2⟩

/-- con-leche: ConLeche/Verify/EnvWF.lean:147 ConstWF — a checked header,
stored with no value (`axiomInfo`) or with an unread one (`thmInfo`). -/
theorem constWF_ofType {env : Env} {c : ConstantInfo}
    (ht : c.toConstantVal.type.hasFvar = false ∧
      c.toConstantVal.type.allLevelParamsDefined c.toConstantVal.levelParams = true ∧
      c.toConstantVal.type.constsResolve env = true ∧
      c.toConstantVal.type.looseBVarsBounded 0 = true)
    (hc : (∃ cv, c = .axiomInfo cv) ∨ ∃ cv v, c = .thmInfo cv v) : ConstWF env c := by
  obtain ⟨t1, t2, t3, t4⟩ := ht
  refine ⟨t1, t2, t3, t4, ?_, ?_, ?_, ?_⟩ <;>
    rcases hc with ⟨cv, rfl⟩ | ⟨cv, v, rfl⟩ <;>
    first
      | (intro _ _ _ heq; exact ConstantInfo.noConfusion heq)
      | (intro _ _ _ _ heq; exact ConstantInfo.noConfusion heq)
      | (intro _ heq; exact ConstantInfo.noConfusion heq)
      | (intro _ _ heq; exact ConstantInfo.noConfusion heq)

/-- con-leche: ConLeche/Semantics/Bridge/Sound.lean:52 checkDeclRun_ofEnvFactsE
— **every arm off the inductive route keeps the environment well formed and
pushes no projection table**, read off `DeclRun`: the value arms' records
carry the type's and the value's guards and annotate outputs
(`annotate_syntax`), the axiom arm's the type's, and the pinned blocks are
`declBasisRun_envWF`.  (The unpinned inductive route is `IndSpec`'s and is
excluded by `hd`.) -/
theorem checkDecl_wf_pure {μ : CheckMode} {pinsP : List NatOpPinSet} {F : Nat}
    {env env' : Env} {d : Declaration}
    (h : ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pinsP env d = .ok env')
    (hwf : EnvWF env)
    (hd : ∀ b nP, d = .indDecl b nP → (basisPinHit b).isSome = true) :
    EnvWF env' ∧ NoTowerPush env env' := by
  have hrun := checkDeclRun_ofEnvFactsE h
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, hvf, rfl, -⟩ := hrun
    refine ⟨EnvWF.cons hwf ?_, NoTowerPush.cons _ _ rfl⟩
    obtain ⟨t1, t2, t3, t4⟩ := constantValRun_typeWF hcv
      (.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
    refine ⟨t1, t2, t3, t4, fun _ _ _ heq => ?_, fun _ _ _ _ heq => ?_,
      fun _ heq => ?_, fun _ _ heq => ?_⟩
    · obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.defnInfo.inj heq
      exact valueFrontRun_valueWF hvf _
    all_goals exact ConstantInfo.noConfusion heq
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, -, rfl⟩ := hrun
    exact ⟨EnvWF.cons hwf (constWF_ofType (constantValRun_typeWF hcv _)
      (Or.inr ⟨_, _, rfl⟩)), NoTowerPush.cons _ _ rfl⟩
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, -, rfl, -⟩ := hrun
    exact ⟨EnvWF.cons hwf (constWF_ofType (constantValRun_typeWF hcv _)
      (Or.inl ⟨_, rfl⟩)), NoTowerPush.cons _ _ rfl⟩
  | axiomDecl cv =>
    rcases hrun with ⟨-, rfl⟩ | ⟨type', hcv, hdisj⟩
    · exact ⟨hwf, NoTowerPush.refl _⟩
    · have hax : EnvWF ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩ ∧
          NoTowerPush env ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩ :=
        ⟨EnvWF.cons hwf (constWF_ofType (constantValRun_typeWF hcv _)
          (Or.inl ⟨_, rfl⟩)), NoTowerPush.cons _ _ rfl⟩
      rcases hdisj with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
      · exact hax
      · exact hax
      · exact hax
      · exact ⟨hwf, NoTowerPush.refl _⟩
  | basisDecl kind => exact ⟨declBasisRun_envWF hrun hwf, declBasisRun_noTower hrun⟩
  | quotDecl k cv =>
    cases k with
    | type => exact ⟨declBasisRun_envWF hrun hwf, declBasisRun_noTower hrun⟩
    | _ => (simp only [DeclRun] at hrun; subst hrun; exact ⟨hwf, NoTowerPush.refl _⟩)
  | indDecl block nP =>
    simp only [DeclRun] at hrun
    split at hrun
    · exact ⟨declBasisRun_envWF hrun hwf, declBasisRun_noTower hrun⟩
    · rename_i hnone
      have := hd block nP rfl
      rw [hnone] at this
      exact nomatch this

end ConRon.Bridge

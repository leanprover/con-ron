/-
# `ConRon.Bridge.Inductives.NativeParts` — Theorem 1 for the generated recursor

`Arena/Inductives/NativeParts.lean`'s thirty-three twins against
`ConLeche/Kernel/Inductives/NativeParts.lean`: the positivity classification,
the recursor type and right-hand sides the install FABRICATES and compares the
stream's against, the rule checks and the two recognisers.

**All PURE grade.**  Nothing here calls the knot; `recPositivity` and
`recFamOk` walk handles and `mentionsConst` them, and the generators intern.

## The five higher-order arguments, and how their statements read

Task #97d-2's deviation 3 removed five function arguments con-leche passes,
because DESIGN §3.4 forbids a closure.  Three of them are in this module:

* `structRuleBodyR`'s and `structIhPis`' `teleOf`/`idxOf` became the
  constructor type `cty` and the two counts, with `structFieldTeleOf` /
  `structFieldIdxOf` called INSIDE;
* `nativeRulesOk` carries the same substitution one level up.

So each of those statements is a `…_congr`-shaped one in task #97-P3-0 §2's
sense: the twin is compared with con-leche's function AT the two concrete
readers, `fun i => ConLeche.structFieldTeleOf ctyP nP nF i` and its sibling.
That instantiation is the whole content of the deviation, and stating it is
what discharges it.

## `piBinders` has fuel and con-leche's does not

`Expr.piBinders` is structural on the `Expr`; the twin cannot be, because a
handle has no structural measure, so it takes `coreWalkFuel`.  Partial
correctness makes this free: `PSpec` assumes the run ACCEPTED, and a run that
exhausted its fuel `fail`ed.  The same applies to `recPositivity`.
-/
import ConRon.Bridge.Inductives.SumParts

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The positivity classification -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:78-87 recFamOk
Is `e` the family at the parameter variables followed by `nIdx` index
expressions none of which mentions the block?  Official's `is_valid_ind_app`.

`sorry`: `Bridge/ExprOps/Spine.lean`'s `getAppSpine` spec, `structFam_spec`
and `mentionsConst_spec`. -/
theorem recFamOk_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nIdx o : Nat) (e : EIdx) (eP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧ denoteE st e = some eP)
      (Arena.recFamOk T lps nP nIdx o e)
      (RV (ConLeche.recFamOk TP lpsP nP nIdx o eP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:89-111 recPositivity
The field domain's kind, walking under its own binders.

`sorry`: a fuel induction whose `.forallE` arm is `Bridge/Rel.lean`'s
`forallE` inversion and whose leaf arm is `recFamOk_spec` + `mentionsConst_spec`. -/
theorem recPositivity_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nIdx o fuel : Nat) (h : EIdx) (hP : Expr)
    (k : Nat) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧ denoteE st h = some hP)
      (Arena.recPositivity T lps nP nIdx o fuel h k)
      (RK (ConLeche.recPositivity TP lpsP nP nIdx o hP k)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:113-116 recFieldKind
The entry at `k = 0`.

`sorry`: `recPositivity_spec`. -/
theorem recFieldKind_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nIdx o : Nat) (dom : EIdx) (domP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧ denoteE st dom = some domP)
      (Arena.recFieldKind T lps nP nIdx o dom)
      (RK (ConLeche.recFieldKind TP lpsP nP nIdx o domP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:118-145 recCtorKinds
One constructor's field kinds, or `none` when its residual is not the family.

`sorry`: the telescope peel (`Bridge/ExprOps/TelescopeF.lean`) and
`recFieldKind_spec` at each domain. -/
theorem recCtorKinds_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nIdx : Nat) (c : IConstantVal × Nat)
    (cP : ConstantVal × Nat) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        Frontend.denoteCV st c.1 = some cP.1 ∧ c.2 = cP.2)
      (Arena.recCtorKinds T lps nP nIdx c)
      (ROp RKs (ConLeche.recCtorKinds TP lpsP nP nIdx cP)) := by
  sorry

/-! ## The telescope readers -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:147-154 Expr.piBinders
Peel `fuel` Π binders; the twin's fuel is invisible under partial correctness
(see the module note).

`sorry`: a fuel induction over `Bridge/Rel.lean`'s `forallE` inversion. -/
theorem piBinders_spec (fuel : Nat) (h : EIdx) (hP : Expr) :
    PSpec (fun st => denoteE st h = some hP)
      (Arena.piBinders fuel h)
      (fun st r => denoteBinders st r.1 = some (Expr.piBinders hP).1 ∧
        denoteE st r.2 = some (Expr.piBinders hP).2) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:156-161 structFieldTeleOf
Field `i`'s own Π-telescope.

`sorry`: `piBinders_spec` under the constructor telescope. -/
theorem structFieldTeleOf_spec (cty : EIdx) (ctyP : Expr) (nP nF i : Nat) :
    PSpec (fun st => denoteE st cty = some ctyP)
      (Arena.structFieldTeleOf cty nP nF i)
      (RB (ConLeche.structFieldTeleOf ctyP nP nF i)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:163-169 structFieldIdxOf
Field `i`'s index arguments.

`sorry`: `piBinders_spec` and `Bridge/ExprOps/Spine.lean`'s `getAppSpine`
spec. -/
theorem structFieldIdxOf_spec (cty : EIdx) (ctyP : Expr) (nP nF i : Nat) :
    PSpec (fun st => denoteE st cty = some ctyP)
      (Arena.structFieldIdxOf cty nP nF i)
      (REL (ConLeche.structFieldIdxOf ctyP nP nF i)) := by
  sorry

/-! ## The three pure record operations

`recIdxOf`, `NativeParts.complete` and `NativeParts.withKinds` touch no term
(task #97d-2's deviation 8), so their statements are plain equations rather
than `PSpec`s — and all three are CLOSED. -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:171-175 recIdxOf
The positions of the recursive fields.  The twin's `RecFieldKind` is
con-leche's under `kindOf`, and `recIdxOf` reads nothing else. -/
theorem recIdxOf_spec (ks : List Arena.RecFieldKind) :
    Arena.recIdxOf ks = ConLeche.recIdxOf (ks.map kindOf) := by
  simp only [Arena.recIdxOf, ConLeche.recIdxOf, List.length_map]
  congr 1
  funext i
  cases h : ks[i]?  with
  | none =>
    have : (ks.map kindOf)[i]? = none := by simp [h]
    simp only [List.getD, h, this, Option.getD]
    rfl
  | some k =>
    have : (ks.map kindOf)[i]? = some (kindOf k) := by simp [h]
    simp only [List.getD, h, this, Option.getD]
    cases k <;> rfl

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:194-199 NativeParts.complete
The record completed by the former's stage: the shape moves, the kinds and the
pin bit stay. -/
theorem complete_spec {st : EStore} {p₀ : Arena.NativeParts}
    {q₀ : ConLeche.NativeParts} {p₁ : Arena.InductiveShape}
    {q₁ : ConLeche.InductiveShape} (h₀ : PartsRel st p₀ q₀)
    (h₁ : ShapeRel st p₁ q₁) :
    PartsRel st (p₀.complete p₁) (q₀.complete q₁) :=
  ⟨h₁, h₀.kinds, h₀.recPinned⟩

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:616-622 NativeParts.withKinds
The record with the classification's kinds written in. -/
theorem withKinds_spec {st : EStore} {p : Arena.NativeParts}
    {q : ConLeche.NativeParts} {ks : List (List Arena.RecFieldKind)}
    (h : PartsRel st p q) :
    PartsRel st (p.withKinds ks) (q.withKinds (ks.map (·.map kindOf))) :=
  ⟨h.shape, rfl, h.recPinned⟩

/-! ## The generated recursor -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:230-235 structRecPrefixAt
The recursor's leading spine `p⃗ motive m⃗` as seen from under the fields.

`sorry`: `structPsAt_spec` twice and `internBVarE_spec`. -/
theorem structRecPrefixAt_spec (nP n nF e : Nat) :
    PSpec PT (Arena.structRecPrefixAt nP n nF e)
      (REL (ConLeche.structRecPrefixAt nP n nF e)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:237-244 structIdxAt
A recursive field's index expression relocated to the rule frame.

`sorry`: `Bridge/ExprOps/Subst.lean`'s `liftLooseBVarsFast_spec`, twice. -/
theorem structIdxAt_spec (nF o i l m : Nat) (e : EIdx) (eP : Expr) :
    PSpec (fun st => denoteE st e = some eP)
      (Arena.structIdxAt nF o i l m e)
      (RE (ConLeche.structIdxAt nF o i l m eP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:246-252 structTeleAt
A field's telescope relocated, with a fresh `PropWhen` on each binder.

`sorry`: `structIdxAt_spec` at each domain, a list map. -/
theorem structTeleAt_spec (nF o i l : Nat) (pw : PropWhen)
    (tele : List (EIdx × BinderMeta)) (teleP : List (Expr × BinderMeta)) :
    PSpec (fun st => denoteBinders st tele = some teleP)
      (Arena.structTeleAt nF o i l pw tele)
      (RB (ConLeche.structTeleAt nF o i l pw teleP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:254-255 structTeleVars
`bvarsDesc m`; con-leche's is the same `List.range` map. -/
theorem structTeleVars_spec (m : Nat) :
    PSpec PT (Arena.structTeleVars m) (REL (ConLeche.structTeleVars m)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:257-260 Expr.mkPisOf
Close a body under a telescope of Π binders.

`sorry`: a list induction over `internE_spec` at `.forallE`. -/
theorem mkPisOf_spec (bs : List (EIdx × BinderMeta))
    (bsP : List (Expr × BinderMeta)) (body : EIdx) (bodyP : Expr) :
    PSpec (fun st => denoteBinders st bs = some bsP ∧
        denoteE st body = some bodyP)
      (Arena.mkPisOf bs body) (RE (Expr.mkPisOf bsP bodyP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:261-263 Expr.mkLamsOf
The same with `.lam`.

`sorry`: `mkPisOf_spec`'s argument. -/
theorem mkLamsOf_spec (bs : List (EIdx × BinderMeta))
    (bsP : List (Expr × BinderMeta)) (body : EIdx) (bodyP : Expr) :
    PSpec (fun st => denoteBinders st bs = some bsP ∧
        denoteE st body = some bodyP)
      (Arena.mkLamsOf bs body) (RE (Expr.mkLamsOf bsP bodyP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:265-277 structIhApp
The inductive-hypothesis application inside a minor premise.

`sorry`: `structRecPrefixAt_spec`, `structTeleVars_spec`, `structIdxAt_spec`
and `mkAppN`'s spec. -/
theorem structIhApp_spec (recC : NIdx) (recCP : ConLeche.Name) (rlvls : LsIdx)
    (rlvlsP : List Level) (pw : PropWhen) (nP n nF i : Nat)
    (tele : List (EIdx × BinderMeta)) (teleP : List (Expr × BinderMeta))
    (idx : List EIdx) (idxP : List Expr) :
    PSpec (fun st => denoteN st.ns recC = some recCP ∧
        denoteLs st.lss rlvls = some rlvlsP ∧
        denoteBinders st tele = some teleP ∧
        Frontend.denoteEList st idx = some idxP)
      (Arena.structIhApp recC rlvls pw nP n nF i tele idx)
      (RE (ConLeche.structIhApp recCP rlvlsP pw nP n nF i teleP idxP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:279-288 structRuleBodyR
The rule's right-hand-side body.  **Task #97d-2's deviation 3**: con-leche
takes `teleOf`/`idxOf` as FUNCTIONS and the twin takes the constructor type and
calls the two readers itself, so the statement compares the twin with
con-leche at those two readers — which is what discharges the deviation.

`sorry`: `structFieldTeleOf_spec`, `structFieldIdxOf_spec`, `structIhApp_spec`
and `mkAppN`'s spec. -/
theorem structRuleBodyR_spec (recC : NIdx) (recCP : ConLeche.Name)
    (rlvls : LsIdx) (rlvlsP : List Level) (pw : PropWhen) (nP n nF j : Nat)
    (recIdx : List Nat) (cty : EIdx) (ctyP : Expr) :
    PSpec (fun st => denoteN st.ns recC = some recCP ∧
        denoteLs st.lss rlvls = some rlvlsP ∧ denoteE st cty = some ctyP)
      (Arena.structRuleBodyR recC rlvls pw nP n nF j recIdx cty)
      (RE (ConLeche.structRuleBodyR recCP rlvlsP pw nP n nF j recIdx
        (fun i => ConLeche.structFieldTeleOf ctyP nP nF i)
        (fun i => ConLeche.structFieldIdxOf ctyP nP nF i))) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:290-305 structIhPis
The inductive-hypothesis binders in front of a minor premise's body.  The same
deviation, the same instantiation; note con-leche's `nP` is not a parameter of
its version (it reads it through `teleOf`).

`sorry`: a list induction over `structTeleAt_spec`, `structIhApp_spec` and
`mkPisOf_spec`. -/
theorem structIhPis_spec (nF o nP : Nat) (pw : PropWhen) (cty : EIdx)
    (ctyP : Expr) (is : List Nat) (l : Nat) (body : EIdx) (bodyP : Expr) :
    PSpec (fun st => denoteE st cty = some ctyP ∧
        denoteE st body = some bodyP)
      (Arena.structIhPis nF o nP pw cty is l body)
      (RE (ConLeche.structIhPis nF o pw
        (fun i => ConLeche.structFieldTeleOf ctyP nP nF i)
        (fun i => ConLeche.structFieldIdxOf ctyP nP nF i) is l bodyP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:307-320 structMinorTyR
One minor premise's type.

`sorry`: `replacePisPw_spec`, `structIhPis_spec`, `structCtorSpineAt_spec`
and `structRecPrefixAt_spec`. -/
theorem structMinorTyR_spec (C : NIdx) (CP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nF o : Nat) (pw : PropWhen) (cty : EIdx)
    (ctyP : Expr) (recIdx : List Nat) :
    PSpec (fun st => denoteN st.ns C = some CP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st cty = some ctyP)
      (Arena.structMinorTyR C lps nP nF o pw cty recIdx)
      (ROp RE (ConLeche.structMinorTyR CP lpsP nP nF o pw ctyP recIdx)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:322-330 structMinorsPisR
All the minor premises as Π binders in front of a body.

`sorry`: a list induction over `structMinorTyR_spec` and `internE_spec`. -/
theorem structMinorsPisR_spec (lps : List NIdx) (lpsP : List ConLeche.Name)
    (nP : Nat) (pw : PropWhen) (cs : List (NIdx × Nat × EIdx × List Nat))
    (csP : List (ConLeche.Name × Nat × Expr × List Nat)) (o : Nat)
    (body : EIdx) (bodyP : Expr) :
    PSpec (fun st => Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteCtors4 st cs = some csP ∧ denoteE st body = some bodyP)
      (Arena.structMinorsPisR lps nP pw cs o body)
      (ROp RE (ConLeche.structMinorsPisR lpsP nP pw csP o bodyP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:332-339 structMinorsLamsR
The same as λ binders.

`sorry`: `structMinorsPisR_spec`'s argument with `.lam`. -/
theorem structMinorsLamsR_spec (lps : List NIdx) (lpsP : List ConLeche.Name)
    (nP : Nat) (pw : PropWhen) (cs : List (NIdx × Nat × EIdx × List Nat))
    (csP : List (ConLeche.Name × Nat × Expr × List Nat)) (o : Nat)
    (body : EIdx) (bodyP : Expr) :
    PSpec (fun st => Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteCtors4 st cs = some csP ∧ denoteE st body = some bodyP)
      (Arena.structMinorsLamsR lps nP pw cs o body)
      (ROp RE (ConLeche.structMinorsLamsR lpsP nP pw csP o bodyP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:341-362 structRecTyR
**THE GENERATED RECURSOR'S TYPE** — the term the install compares the stream's
recursor against, so this statement is what makes "the recursor is the
generated one" mean the same on both sides.

`sorry`: `structMotiveTyI_spec`, `structMinorsPisR_spec`,
`structElimLevel_spec`, `structFamI_spec` and `replacePisPw_spec`. -/
theorem structRecTyR_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (elim : NIdx) (elimP : ConLeche.Name)
    (large : Bool) (nP nIdx : Nat) (tty : EIdx) (ttyP : Expr)
    (ctors : List (NIdx × Nat × EIdx × List Nat))
    (ctorsP : List (ConLeche.Name × Nat × Expr × List Nat)) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteN st.ns elim = some elimP ∧ denoteE st tty = some ttyP ∧
        denoteCtors4 st ctors = some ctorsP)
      (Arena.structRecTyR T lps elim large nP nIdx tty ctors)
      (ROp RE (ConLeche.structRecTyR TP lpsP elimP large nP nIdx ttyP ctorsP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:364-386 structRecRhsR
**THE GENERATED RULE'S RIGHT-HAND SIDE**, constructor `j`'s.

`sorry`: `structRecTyR_spec`'s pieces plus `structMinorsLamsR_spec`,
`structRuleBodyR_spec` and `pisToLamsPw_spec`. -/
theorem structRecRhsR_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (elim : NIdx) (elimP : ConLeche.Name)
    (large : Bool) (nP nIdx : Nat) (tty : EIdx) (ttyP : Expr)
    (ctors : List (NIdx × Nat × EIdx × List Nat))
    (ctorsP : List (ConLeche.Name × Nat × Expr × List Nat)) (recC : NIdx)
    (recCP : ConLeche.Name) (rlvls : LsIdx) (rlvlsP : List Level) (j : Nat) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteN st.ns elim = some elimP ∧ denoteE st tty = some ttyP ∧
        denoteCtors4 st ctors = some ctorsP ∧
        denoteN st.ns recC = some recCP ∧ denoteLs st.lss rlvls = some rlvlsP)
      (Arena.structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j)
      (ROp RE (ConLeche.structRecRhsR TP lpsP elimP large nP nIdx ttyP ctorsP
        recCP rlvlsP j)) := by
  sorry

/-! ## The four-tuple and the rule checks -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:388-392 nativeCtors4
The generators' input: each constructor's name, field count, type and
recursive-field positions.  Pure on both sides.

`sorry`: a list zip induction over `recIdxOf_spec` (closed above) and the
`denoteCtors`/`denoteCtors4` clauses. -/
theorem nativeCtors4_spec (st : EStore) (ctorsA : List (IConstantVal × Nat))
    (ctorsAP : List (ConstantVal × Nat))
    (kinds : List (List Arena.RecFieldKind))
    (h : denoteCtors st ctorsA = some ctorsAP) :
    denoteCtors4 st (Arena.nativeCtors4 ctorsA kinds)
      = some (ConLeche.nativeCtors4 ctorsAP (kinds.map (·.map kindOf))) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:394-445 nativeRulePrefixOk
The stream rule's λ prefix is the generated one.

`sorry`: `stripLams`' spec and the structural comparison through
`denoteE_inj`. -/
theorem nativeRulePrefixOk_spec (recTy : EIdx) (recTyP : Expr)
    (nP n j nF : Nat) (rhs : EIdx) (rhsP : Expr) :
    PSpec (fun st => denoteE st recTy = some recTyP ∧
        denoteE st rhs = some rhsP)
      (Arena.nativeRulePrefixOk recTy nP n j nF rhs)
      (RV (ConLeche.nativeRulePrefixOk recTyP nP n j nF rhsP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:447-475 nativeRulesOk
**The stream's rules are the generated ones**, constructor by constructor.

`sorry`: `structRecRhsR_spec`, `nativeRulePrefixOk_spec` and
`nativeCtors4_spec`, over a list induction. -/
theorem nativeRulesOk_spec (recC : NIdx) (recCP : ConLeche.Name)
    (rlvls : LsIdx) (rlvlsP : List Level) (pw : PropWhen) (nP n : Nat)
    (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat))
    (kinds : List (List Arena.RecFieldKind)) (rhss : List EIdx)
    (rhssP : List Expr) (recTy : EIdx) (recTyP : Expr) :
    PSpec (fun st => denoteN st.ns recC = some recCP ∧
        denoteLs st.lss rlvls = some rlvlsP ∧ denoteCtors st cs = some csP ∧
        Frontend.denoteEList st rhss = some rhssP ∧
        denoteE st recTy = some recTyP)
      (Arena.nativeRulesOk recC rlvls pw nP n cs kinds rhss recTy)
      (RV (ConLeche.nativeRulesOk recCP rlvlsP pw nP n csP
        (kinds.map (·.map kindOf)) rhssP recTyP)) := by
  sorry

/-! ## The recogniser -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:501-523 nativeCounts?
The declared parameter and index counts, or `none`.

`sorry`: `piSortTeleLen?`'s spec (`Bridge/ExprOps/TelescopeF.lean`). -/
theorem nativeCounts?_spec (nPd : Nat) (cvT : IConstantVal)
    (cvTP : ConstantVal) (cs : List (IConstantVal × Nat × Nat))
    (csP : List (ConstantVal × Nat × Nat)) (mI rP : Nat) :
    PSpec (fun st => Frontend.denoteCV st cvT = some cvTP ∧
        denoteCtors3 st cs = some csP)
      (Arena.nativeCounts? nPd cvT cs mI rP)
      (RV (ConLeche.nativeCounts? nPd cvTP csP mI rP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:525-549 nativeRecPinOk
The stream's recursor record passed the structural pin.  Pure on both sides.

`sorry`: the block's `denoteCIList` inverted at each member, plus `denoteN_inj`
at the recursor's name. -/
theorem nativeRecPinOk_spec (st : EStore) (p : Arena.InductiveShape)
    (q : ConLeche.InductiveShape) (block : List IConstantInfo)
    (blockP : List ConstantInfo) (hp : ShapeRel st p q)
    (hb : Frontend.denoteCIList st block = some blockP) :
    Arena.nativeRecPinOk p block = ConLeche.nativeRecPinOk q blockP := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:551-560 nativeRecLpsOk
The recursor's level parameters are the block's (with the elimination
parameter in front at the large eliminator).  Pure on both sides.

`sorry`: `denoteNList`'s injectivity at the two level-parameter lists. -/
theorem nativeRecLpsOk_spec (st : EStore) (p : Arena.InductiveShape)
    (q : ConLeche.InductiveShape) (hp : ShapeRel st p q) :
    Arena.nativeRecLpsOk p = ConLeche.nativeRecLpsOk q := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
Read a block into the shape record, or refuse it.  **Two-sided**: the dispatch
reads it.

**CORE grade, not pure** (task #97-P3-Ind round 2's finding; the argument is
in `Bridge/Inductives/Rel.lean`'s frame section).  Like `structPartsCore?`
this recogniser asks `lvlEq? s z` for `isProp`, and `lvlEq?` moves two of the
fourteen per-declaration cache tables, so `PStep` is the wrong frame.

`sorry`: `sumSplit_spec` (closed), `nativeCounts?_spec`, `nativeRecPinOk_spec`,
`nativeRecLpsOk_spec`, `lvlEq?_spec` (closed) and `internNNode_spec` at
`T.str "rec"`. -/
theorem nativeShape?_spec {μ : CheckMode} {env : Env} (fe : IFEnv) (nPd : Nat)
    (block : List IConstantInfo) (blockP : List ConstantInfo) :
    CSpec μ env fe (fun st => Frontend.denoteCIList st block = some blockP)
      (Arena.nativeShape? nPd block)
      (ROp RShape (ConLeche.nativeShape? nPd blockP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:631-652 nativeParts?
**THE DISPATCH'S RECOGNISER** — `checkIndDecl` routes on this and on nothing
else (task #219), so its two-sidedness is the soundness of the route choice.

**CORE grade, not pure**, because `nativeShape?` is (task #97-P3-Ind round 2's
finding).  This is the statement `checkIndDecl_bridge` consumes, so round 1's
`PSpec` form was a false lemma UNDER A PROVED THEOREM — the one place in the
tier where the defect was load-bearing rather than merely stated.

`sorry`: `nativeShape?_spec`, `recCtorKinds_spec` at each constructor and
`withKinds_spec` (closed above). -/
theorem nativeParts?_spec {μ : CheckMode} {env : Env} (fe : IFEnv) (nPd : Nat)
    (block : List IConstantInfo) (blockP : List ConstantInfo) :
    CSpec μ env fe (fun st => Frontend.denoteCIList st block = some blockP)
      (Arena.nativeParts? nPd block)
      (ROp RParts (ConLeche.nativeParts? nPd blockP)) := by
  sorry

end ConRon.Bridge.Inductives

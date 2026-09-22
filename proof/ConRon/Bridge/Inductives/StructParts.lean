/-
# `ConRon.Bridge.Inductives.StructParts` — Theorem 1 for the generators

`Arena/Inductives/StructParts.lean`'s twenty-nine twins against
`ConLeche/Kernel/Inductives/StructParts.lean`: the families, the spines, the
Π→λ rewrites, the structure recogniser, the projection bodies and the two
memoised `Expr` predicates.

**Every twin here is PURE grade.**  Not one of them calls the knot: they
intern nodes, read the store, read the pin table and walk handles.  So every
statement is a `PSpec` and the frame is `PStep` — task #97-P3-0 §2's rule that
an `ExprOps`-shaped theorem must not carry the cache clauses, applied to the
generators.

## The three memo invariants

`hasLooseBVarBGo`, `structUsedLaterGo` and `mentionsConstGo` thread an
explicit `Std.HashMap` (task #97d-2's deviation 5: the memo stays an ARGUMENT
because each answer depends on data fixed for one call, and nothing was added
to `AState`).  Each needs an invariant in `Bridge/StateOK.lean`'s `MemoOK`
shape — "every recorded answer is the real one" — and the invariant travels
in and out of the walk, which is what makes these three statements different
from the other twenty-six.

con-leche's own are `LooseBVarMemoInv` (`StructParts.lean:428-433`) and
`MentionsMemoInv` (`StructParts.lean:806-812`); the arena's are the same
predicate at handle keys, through `denoteE`.
-/
import ConRon.Bridge.Inductives.Rel

namespace ConRon.Bridge.Inductives

set_option autoImplicit false
set_option mvcgen.warning false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The three memo invariants -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:428-433 LooseBVarMemoInv
The `(handle, cursor)`-keyed memo of `hasLooseBVarB`: every recorded answer is
the real one at the key's own cursor. -/
def LooseMemoOK (tbl : Std.HashMap (EIdx × Nat) Bool) (st : EStore) : Prop :=
  ∀ (k : EIdx × Nat) (r : Bool), tbl[k]? = some r →
    ∃ e, denoteE st k.1 = some e ∧ r = Expr.hasLooseBVarB k.2 e

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:806-812 MentionsMemoInv
The handle-keyed memo of `mentionsConst T`. -/
def MentionsMemoOK (T : ConLeche.Name) (tbl : Std.HashMap EIdx Bool)
    (st : EStore) : Prop :=
  ∀ (k : EIdx) (r : Bool), tbl[k]? = some r →
    ∃ e, denoteE st k = some e ∧ r = Expr.mentionsConst T e

/-! ## Level lists over handles -/

/-- con-leche: none — `lps.map .param`, interned.  con-leche writes the list
inline at every use; over handles a level list is a node, so the twin builds
it once and this is the one statement that says the node is that list.

`sorry`: `internLNode_spec` at each element and `internLsNode_spec` at the
result, by a list induction — `Bridge/Specs.lean` has both. -/
theorem paramLevels_spec (lps : List NIdx) (lpsP : List ConLeche.Name) :
    PSpec (fun st => Frontend.denoteNList st.ns lps = some lpsP)
      (Arena.paramLevels lps) (RLs (lpsP.map Level.param)) := by
  sorry

/-! ## The families and the spines -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:134-137 structPsAt
The parameter variables as seen from under `o` extra binders.

`sorry`: a `Nat` recursion over `internBVarE_spec`; the pure side is a
`List.range` map, so the induction is on `nP` with the cursor `k` generalised. -/
theorem structPsAt_spec (o nP : Nat) :
    PSpec PT (Arena.structPsAt o nP) (REL (ConLeche.structPsAt o nP)) := by
  sorry

/-- con-leche: none — `bvarsDesc n` is `structPsAt 0 n`, `rfl` on both sides. -/
theorem bvarsDesc_spec (n : Nat) :
    PSpec PT (Arena.bvarsDesc n) (REL (ConLeche.structPsAt 0 n)) :=
  structPsAt_spec 0 n

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:82-86 structFam
The type former applied to its parameter variables.

`sorry`: `paramLevels_spec`, `internConstE_spec` and `mkAppN`'s own spec
(`Bridge/ExprOps/Spine.lean`), composed. -/
theorem structFam_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP o : Nat) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP)
      (Arena.structFam T lps nP o) (RE (ConLeche.structFam TP lpsP nP o)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:88-94 structCtorSpine
The constructor applied to the parameter and field variables.

`sorry`: as `structFam_spec`, with the two spines appended. -/
theorem structCtorSpine_spec (C : NIdx) (CP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nF : Nat) :
    PSpec (fun st => denoteN st.ns C = some CP ∧
        Frontend.denoteNList st.ns lps = some lpsP)
      (Arena.structCtorSpine C lps nP nF)
      (RE (ConLeche.structCtorSpine CP lpsP nP nF)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:96-99 structRuleBody
The minor premise applied to the field variables.

`sorry`: `internBVarE_spec`, `bvarsDesc_spec` and `mkAppN`'s spec. -/
theorem structRuleBody_spec (nF : Nat) :
    PSpec PT (Arena.structRuleBody nF) (RE (ConLeche.structRuleBody nF)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:139-142 structElimLevel
The recursor's elimination level.

`sorry`: `internLNode_spec` at `.param`/`.zero`, one `if`. -/
theorem structElimLevel_spec (elim : NIdx) (elimP : ConLeche.Name)
    (large : Bool) :
    PSpec (fun st => denoteN st.ns elim = some elimP)
      (Arena.structElimLevel elim large)
      (RL (ConLeche.structElimLevel elimP large)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:144-150 structCtorSpineAt
`structCtorSpine` at an arbitrary offset between the parameters and the
fields.

`sorry`: as `structCtorSpine_spec`. -/
theorem structCtorSpineAt_spec (C : NIdx) (CP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (o nP nF : Nat) :
    PSpec (fun st => denoteN st.ns C = some CP ∧
        Frontend.denoteNList st.ns lps = some lpsP)
      (Arena.structCtorSpineAt C lps o nP nF)
      (RE (ConLeche.structCtorSpineAt CP lpsP o nP nF)) := by
  sorry

/-! ## The Π→Π and Π→λ rewrites -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:152-158 Expr.replacePisPw
Replace a `k`-binder Π-telescope's body, re-stamping every binder's `PropWhen`.

`sorry`: a `Nat` recursion whose binder arm is `internE_spec` at `.forallE` —
`Bridge/Rel.lean`'s `RelE.forallE` step lemma at a CHANGED binder datum, which
is exactly the shape task #97-P3-0 §2 says that lemma exists for. -/
theorem replacePisPw_spec (pw : PropWhen) (k : Nat) (h b : EIdx)
    (hP bP : Expr) :
    PSpec (fun st => denoteE st h = some hP ∧ denoteE st b = some bP)
      (Arena.replacePisPw pw k h b)
      (ROp RE (Expr.replacePisPw pw k hP bP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:160-167 Expr.pisToLamsPw
The same with `.lam` in place of `.forallE`.

`sorry`: `replacePisPw_spec`'s argument with `RelE.lam`. -/
theorem pisToLamsPw_spec (pw : PropWhen) (k : Nat) (h b : EIdx)
    (hP bP : Expr) :
    PSpec (fun st => denoteE st h = some hP ∧ denoteE st b = some bP)
      (Arena.pisToLamsPw pw k h b)
      (ROp RE (Expr.pisToLamsPw pw k hP bP)) := by
  sorry

/-! ## The indexed family -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:189-194 structFamI
The family at its parameters and `nIdx` index variables.

`sorry`: `structFam_spec`'s argument with the index spine appended. -/
theorem structFamI_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nIdx e o : Nat) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP)
      (Arena.structFamI T lps nP nIdx e o)
      (RE (ConLeche.structFamI TP lpsP nP nIdx e o)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:196-202 structCtorResidOk
Does the constructor's residual target the family?  A `Bool` answer, so `RV`
and no target store — task #97-P3-0 §5's finding 1.

`sorry`: `structFamI_spec` and one handle equality, which is `denoteE_inj`. -/
theorem structCtorResidOk_spec (T : NIdx) (TP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (nP o nIdx : Nat)
    (cbody : EIdx) (cbodyP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st cbody = some cbodyP)
      (Arena.structCtorResidOk T lps nP o nIdx cbody)
      (RV (ConLeche.structCtorResidOk TP lpsP nP o nIdx cbodyP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:204-211 structMotiveTyI
The motive's type at the parameters' frame.

`sorry`: `structFamI_spec`, two `internE_spec`s and `replacePisPw_spec`. -/
theorem structMotiveTyI_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nIdx : Nat) (l : LIdx) (lP : Level)
    (itele : EIdx) (iteleP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteL st.ls l = some lP ∧ denoteE st itele = some iteleP)
      (Arena.structMotiveTyI T lps nP nIdx l itele)
      (ROp RE (ConLeche.structMotiveTyI TP lpsP nP nIdx lP iteleP)) := by
  sorry

/-! ## The recogniser -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:246-281 structShape
The shape facts the model reads off the stored (annotated) types.  A `Bool`
answer.

`sorry`: `stripPis`' spec (`Bridge/ExprOps/TelescopeF.lean`), the tag
dispatch through `Bridge/Rel.lean`'s `EStore.tagOf_of_view`, `structFam_spec`,
`structCtorSpine_spec` and five handle equalities through `denoteE_inj`. -/
theorem structShape_spec (T C : NIdx) (TP CP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (elim : NIdx) (elimP : ConLeche.Name)
    (large : Bool) (nP nF : Nat) (tty cty rty : EIdx)
    (ttyP ctyP rtyP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteN st.ns C = some CP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteN st.ns elim = some elimP ∧ denoteE st tty = some ttyP ∧
        denoteE st cty = some ctyP ∧ denoteE st rty = some rtyP)
      (Arena.structShape T C lps elim large nP nF tty cty rty)
      (RV (ConLeche.structShape TP CP lpsP elimP large nP nF ttyP ctyP rtyP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:283-329 structPartsCore?
Recognise a direct simple-structure block.  `none` means "not this class", and
the relation is TWO-SIDED (`ROp`): a twin that failed to recognise a block
con-leche recognises would take the other route.

`sorry`: `structShape_spec`, `stripLams`' and `stripPis`' specs, the reserved
name table through `PinsOK`, and `internNNode_spec` at `T.str "rec"`. -/
theorem structPartsCore?_spec (block : List IConstantInfo)
    (blockP : List ConstantInfo) :
    PSpec (fun st => Frontend.denoteCIList st block = some blockP)
      (Arena.structPartsCore? block)
      (ROp RSParts (ConLeche.structPartsCore? blockP)) := by
  sorry

/-! ## The projection bodies -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:331-337 structProjPs
**The one arithmetic identification of this module**: con-leche writes the
projection parameter spine as `bvar (nP - k)` and `structPsAt 1 nP` as
`bvar (1 + nP - 1 - k)`.  The arena's `structProjPs` is `structPsAt 1 nP` by
definition (task #97d-2 kept the twin's two names apart because con-leche
writes them at different frames), so the twins agree exactly when these two
`Nat` expressions do — which they do, and `omega` says so. -/
theorem structProjPs_eq (nP : Nat) :
    ConLeche.structPsAt 1 nP = ConLeche.structProjPs nP := by
  simp only [ConLeche.structPsAt, ConLeche.structProjPs]
  congr 1
  funext k
  congr 1
  omega

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:331-337 structProjPs
The projection types' parameter spine. -/
theorem structProjPs_spec (nP : Nat) :
    PSpec PT (Arena.structProjPs nP) (REL (ConLeche.structProjPs nP)) := by
  rw [← structProjPs_eq]
  exact structPsAt_spec 1 nP

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:339-345 structProjArgP
The `j`-th projection applied to the structure variable.

`sorry`: `internProjE_spec` and `internBVarE_spec`. -/
theorem structProjArgP_spec (T : NIdx) (TP : ConLeche.Name) (j : Nat) :
    PSpec (fun st => denoteN st.ns T = some TP)
      (Arena.structProjArgP T j) (RE (ConLeche.structProjArgP TP j)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:347-354 structProjResidP
The constructor type's residual after `i` projections have been substituted.

`sorry`: `Bridge/ExprOps/Owed.lean`'s `instPisAtLift_spec` — still open on
that tier's own list — plus `structProjPs_spec` and `structProjArgP_spec`. -/
theorem structProjResidP_spec (T : NIdx) (TP : ConLeche.Name) (nP : Nat)
    (cty : EIdx) (ctyP : Expr) (i : Nat) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteE st cty = some ctyP)
      (Arena.structProjResidP T nP cty i)
      (ROp RE (ConLeche.structProjResidP TP nP ctyP i)) := by
  sorry

/-! ## `hasLooseBVarB`, memoised

`hasLooseBVarBIns` has NO statement of its own: it is the memo-insert helper
(con-leche's `Expr.hasLooseBVarBIns`), a pure function on `Bool ×
Std.HashMap` with no handle in it, and its content is entirely inside
`hasLooseBVarBGo_spec`'s invariant step.  Census class (S). -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:442-478 Expr.hasLooseBVarBGo
The memoised walk: the answer is the real one AND the memo it hands back is
still sound.

`sorry`: a fuel induction with the memo threaded, in
`Bridge/ExprOps/Walks.lean`'s shape, plus the `bvarB` cutoff
(`Bridge/ExprOps/Ranges.lean`'s `bvarB_spec`, closed) for the early return. -/
theorem hasLooseBVarBGo_spec (memo : Std.HashMap (EIdx × Nat) Bool) (i : Nat)
    (fuel : Nat) (h : EIdx) (hP : Expr) :
    PSpec (fun st => denoteE st h = some hP ∧ LooseMemoOK memo st)
      (Arena.hasLooseBVarBGo memo i fuel h)
      (fun st r => r.1 = Expr.hasLooseBVarB i hP ∧ LooseMemoOK r.2 st) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:624-626 Expr.hasLooseBVarBFast
The entry: an empty memo is sound, so the answer is the real one.

`sorry`: `hasLooseBVarBGo_spec` at the empty memo. -/
theorem hasLooseBVarBFast_spec (i : Nat) (e : EIdx) (eP : Expr) :
    PSpec (fun st => denoteE st e = some eP)
      (Arena.hasLooseBVarBFast i e) (RV (Expr.hasLooseBVarB i eP)) := by
  sorry

/-! ## The projection guards -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:633-641 structUsedLater
Is field `j` mentioned by a later field's domain?

`sorry`: `hasLooseBVarBFast_spec` under the constructor type's telescope. -/
theorem structUsedLater_spec (cty : EIdx) (ctyP : Expr) (nP j : Nat) :
    PSpec (fun st => denoteE st cty = some ctyP)
      (Arena.structUsedLater cty nP j)
      (RV (ConLeche.structUsedLater ctyP nP j)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:669-674 structUsedLaterGo
The same with the memo threaded (task #236's one shared memo across `nF`
calls).

`sorry`: `hasLooseBVarBGo_spec` under the telescope. -/
theorem structUsedLaterGo_spec (memo : Std.HashMap (EIdx × Nat) Bool)
    (cty : EIdx) (ctyP : Expr) (nP j : Nat) :
    PSpec (fun st => denoteE st cty = some ctyP ∧ LooseMemoOK memo st)
      (Arena.structUsedLaterGo memo cty nP j)
      (fun st r => r.1 = ConLeche.structUsedLater ctyP nP j ∧
        LooseMemoOK r.2 st) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:685-692 structUsedLaterList
The `n` answers from `base` up, one memo through all of them.

`sorry`: a `Nat` recursion over `structUsedLaterGo_spec`. -/
theorem structUsedLaterList_spec (cty : EIdx) (ctyP : Expr) (nP : Nat)
    (memo : Std.HashMap (EIdx × Nat) Bool) (n base : Nat) :
    PSpec (fun st => denoteE st cty = some ctyP ∧ LooseMemoOK memo st)
      (Arena.structUsedLaterList cty nP memo n base)
      (RV ((List.range n).map fun k => ConLeche.structUsedLater ctyP nP (base + k))) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:643-656 structProjGuards
con-leche: ConLeche/Kernel/Inductives/StructParts.lean:722-732 structProjGuardsFast
The guard level of each field: `Prop` where the field is used later, the
field's own sort otherwise.  The answer is a `List LIdx` and NOT an `LsIdx`
(task #97d-2's deviation 6), so the relation is `RLL`.

`sorry`: `structUsedLaterList_spec` and `zeroLevel`'s pin read
(`Bridge/Specs.lean`, closed). -/
theorem structProjGuards_spec (cty : EIdx) (ctyP : Expr) (nP nF : Nat)
    (sorts : List LIdx) (sortsP : List Level) :
    PSpec (fun st => denoteE st cty = some ctyP ∧
        denoteLList st.ls sorts = some sortsP)
      (Arena.structProjGuards cty nP nF sorts)
      (RLL (ConLeche.structProjGuards ctyP nP nF sortsP)) := by
  sorry

/-! ## The projection bodies -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:748-766 structProjBodiesGo
Peel `k` field binders, substituting the projection of the structure variable
for each.

`sorry`: a `Nat` recursion over `instantiate1LiftFast_spec`
(`Bridge/ExprOps/Subst.lean`) and `structProjArgP_spec`. -/
theorem structProjBodiesGo_spec (T : NIdx) (TP : ConLeche.Name) (k i : Nat)
    (h : EIdx) (hP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteE st h = some hP)
      (Arena.structProjBodiesGo T k i h)
      (ROp REL (ConLeche.structProjBodiesGo TP k i hP)) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:768-771 structProjBodies
The entry, after `nP` parameter binders.

`sorry`: `structProjBodiesGo_spec` and `structProjResidP_spec`. -/
theorem structProjBodies_spec (T : NIdx) (TP : ConLeche.Name) (nP nF : Nat)
    (cty : EIdx) (ctyP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteE st cty = some ctyP)
      (Arena.structProjBodies T nP nF cty)
      (ROp REA (ConLeche.structProjBodies TP nP nF ctyP)) := by
  sorry

/-! ## `mentionsConst`, memoised -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:814-849 Expr.mentionsConstGo
The memoised walk.  Note the `fvar` arm: a free variable carries its type, and
the walk descends into it — DESIGN §8.3's "a handle determines its own typing
context".

`sorry`: a fuel induction with the memo threaded; the name equality is
`denoteN_inj` (`Bridge/Rel.lean`), which is what makes handle inequality
structural inequality. -/
theorem mentionsConstGo_spec (T : NIdx) (TP : ConLeche.Name)
    (memo : Std.HashMap EIdx Bool) (fuel : Nat) (h : EIdx) (hP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteE st h = some hP ∧
        MentionsMemoOK TP memo st)
      (Arena.mentionsConstGo T memo fuel h)
      (fun st r => r.1 = Expr.mentionsConst TP hP ∧
        MentionsMemoOK TP r.2 st) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:922-924 Expr.mentionsConstFast
The entry at an empty memo.

`sorry`: `mentionsConstGo_spec`. -/
theorem mentionsConst_spec (T : NIdx) (TP : ConLeche.Name) (e : EIdx)
    (eP : Expr) :
    PSpec (fun st => denoteN st.ns T = some TP ∧ denoteE st e = some eP)
      (Arena.mentionsConst T e) (RV (Expr.mentionsConst TP eP)) := by
  sorry

end ConRon.Bridge.Inductives

/-
# `ConRon.Bridge.Core.Walks.StrLit` — the `String` literal guard

Task #97-P3-Core round 5 (sub-lane Leaves).  The literal clauses of
`inferBody`, `inferBodyIO` and `annotateBody` run `natLitSupported`
(`Walks/Nat.lean`, closed in round 4) and `strLitSupported`
(`Arena/Core.lean:709`), and the second had no bridge spec.  This module is
that spec and the seven state-only walks under it (`stringTyOk`,
`stringOfListTyOk`, `listTyOk`, `listNilTyOk`, `listConsTyOk`, `charTyOk`,
`charOfNatTyOk`), each an EQUATION with the con-leche function of the same
name (`ConLeche/Kernel/CoreDefs.lean:301-403`) — `Walks/Nat.lean`'s
`natIndOk`/`natZeroOk`/`natSuccOk` shape: the twin interns the expected
shape's pieces and compares handles, con-leche matches the stored type, and
DESIGN §8.3's *index equality is structural equality* (`beq_of_denoteE`,
`beq_of_denoteLs`, `pinBeq`) makes the two the same test.

Also here, because the two inference bodies' `.const` clauses need it and a
`Walks/` module is where a callee fact belongs: `denoteCI_nonTower`, the
constant lookup's two facts behind the tower-entry guard, and
`toConstantVal_spec`, the stored constant's common data in general (the
`.projInfo` arm INTERNS its `Sort 1`).
-/
import ConRon.Bridge.Core.Walks.Nat

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. A stored constant's common data -/

/-- con-leche: ConLeche/Kernel/Env.lean:639-651 ConstantInfo.toConstantVal /
isTowerEntry — a stored non-tower constant projects its value purely, and
denotes a non-tower constant with that value. -/
theorem denoteCI_nonTower {st : EStore} {ci : IConstantInfo}
    {c : ConstantInfo} (h : Frontend.denoteCI st ci = some c)
    (ht : ci.isTowerEntry = false) :
    c.isTowerEntry = false ∧ ∃ v, ci.toConstantVal = (pure v : AM _) ∧
      Frontend.denoteCV st v = some c.toConstantVal := by
  cases ci with
  | projInfo t => simp [IConstantInfo.isTowerEntry] at ht
  | axiomInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    exact ⟨rfl, v, rfl, hcv⟩
  | ctorInfo v nP nF =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨cv, hcv, rfl⟩ := h
    exact ⟨rfl, v, rfl, hcv⟩
  | defnInfo v e hh =>
    simp only [Frontend.denoteCI] at h
    split at h
    · rename_i cv x hcv _; cases h; exact ⟨rfl, v, rfl, hcv⟩
    · simp at h
  | thmInfo v e =>
    simp only [Frontend.denoteCI] at h
    split at h
    · rename_i cv x hcv _; cases h; exact ⟨rfl, v, rfl, hcv⟩
    · simp at h
  | indInfo v caps =>
    simp only [Frontend.denoteCI] at h
    split at h
    · rename_i cv x hcv _; cases h; exact ⟨rfl, v, rfl, hcv⟩
    · simp at h
  | recInfo v mI rP rs =>
    simp only [Frontend.denoteCI] at h
    split at h
    · rename_i cv x hcv _; cases h; exact ⟨rfl, v, rfl, hcv⟩
    · simp at h

/-- con-leche: ConLeche/Kernel/Env.lean:639-642 ConstantInfo.toConstantVal —
**THEOREM 1 for `toConstantVal`**, at the two fields the shape guards read:
the level parameters and the type.  (The `.projInfo` arm's NAME is
`projTableName`'s, which `denoteCI` drops; nothing here reads it.) -/
theorem toConstantVal_spec (s₀ : AState) (ci : IConstantInfo)
    (c : ConstantInfo) (hok : CheckOK mode env fe s₀)
    (hci : Frontend.denoteCI s₀.store ci = some c) :
    ⦃fun s => ⌜s = s₀⌝⦄ ci.toConstantVal
    ⦃⇓? cv s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Frontend.denoteNList s₀.store.ns cv.levelParams =
          some c.toConstantVal.levelParams ∧
        denoteE s'.store cv.type = some c.toConstantVal.type⌝⦄ := by
  have hwf := hok.state.wf
  cases hti : ci.isTowerEntry
  · obtain ⟨_, v, hv, hcv⟩ := denoteCI_nonTower hci hti
    obtain ⟨_, hlp, hty⟩ := denoteCV_inv hcv
    rw [hv]
    mvcgen
    bridge_peel; subst_vars
    exact ⟨hok, Ext.refl _, rfl, hlp, hty⟩
  · cases ci with
    | projInfo t =>
      simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hci
      obtain ⟨t', ht', rfl⟩ := hci
      have hlp : Frontend.denoteNList s₀.store.ns t.levelParams =
          some t'.levelParams := by
        simp only [Frontend.denoteProjTable] at ht'
        split at ht'
        · rename_i sn lps c hsn hlps hc
          split at ht'
          · cases ht'; exact hlps
          · simp at ht'
        · simp at ht'
      mvcgen [IConstantInfo.toConstantVal]
      all_goals (bridge_peel; subst_vars)
      case vc7.true.projInfo.post.success.post.success.post.success =>
        rename_i _ r0 sA r1 sB _ _ _ _ w3 x1 x2 x3 _ _ _ _ _ _ _ _ c3 _ _ p3 c1 c2
          _ p1 p2 _ _ d1 _ d2 _ d3
        have h0 : denoteL sA.store.ls r0 = some Level.zero := by
          rw [d1]; simp [denoteLView]
        have h1 : denoteL sB.store.ls r1 = some (Level.succ .zero) := by
          rw [d2]; simp [denoteLView, denoteL_ext h0 x2]
        refine ⟨hok.mono ⟨w3⟩ (x1.trans (x2.trans x3))
            (c3.trans (c2.trans c1)) (p3.trans (p2.trans p1)),
          x1.trans (x2.trans x3), p3.trans (p2.trans p1), hlp, ?_⟩
        rw [d3]; simp [denoteEView, denoteL_ext h1 x3,
          ConstantInfo.toConstantVal]
      case vc2.hv =>
        constructor
        · intro c hc; simp [LNodeView.lchildren] at hc
        · intro c hc; simp [LNodeView.nchildren] at hc
      case vc4.hv =>
        rename_i hv0 _
        constructor
        · intro c hc; simp [LNodeView.lchildren] at hc; subst hc
          rw [hv0]; rfl
        · intro c hc; simp [LNodeView.nchildren] at hc
      case vc6.hv =>
        rename_i hv1 _
        exact viewOK_sort (by rw [hv1]; rfl)
      all_goals assumption
    | _ => simp [IConstantInfo.isTowerEntry] at hti

/-! ## 2. The pinned names, at their values -/

/-- con-leche: none — a pin read at a slot whose reserved name is `x`
denotes `x` (`pinAt_spec` with the slot's name supplied). -/
theorem pinAt_named (s₀ : AState) (i : Nat) (x : ConLeche.Name)
    (hp : PinsOK s₀) (hx : pinNames[i]? = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ pinAt i
    ⦃⇓? n s' => ⌜s' = s₀ ∧ denoteN s₀.store.ns n = some x⌝⦄ := by
  mvcgen [pinAt_spec]
  all_goals (bridge_peel; subst_vars)
  case vc1.post.success => intro hs hd; exact ⟨hs, hd x hx⟩
  case vc2 => intro s hs; subst hs; exact hp

/-! ## 3. The two `Type`-valued shapes: `String` and `Char` -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:301-307 stringTyOk — **THEOREM 1
for `stringTyOk`**. -/
theorem stringTyOk_spec (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK mode env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.stringTyOk oc
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.stringTyOk oc'⌝⦄ := by
  cases oc with
  | none =>
    simp only [OptCI] at hrel; subst hrel
    mvcgen [ConRon.Arena.stringTyOk]
    all_goals (bridge_peel; subst_vars; exact ⟨hok, Ext.refl _, rfl, rfl⟩)
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    have htc := toConstantVal_spec (mode := mode) (env := env) (fe := fe)
      s₀ ci c hok hci
    mvcgen [ConRon.Arena.stringTyOk, ConRon.Arena.sortOne, htc]
    all_goals (bridge_peel; subst_vars)
    case vc3.some.post.success.post.success =>
      rename_i hlp hck hs1 hty hx hp
      refine ⟨hck, hx, hp, ?_⟩
      simp only [ConLeche.stringTyOk, isEmpty_of_denoteNList hlp,
        beq_of_denoteE hck.state.wf hty hs1]
    all_goals (apply CheckOK.pins; assumption)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:309-315 charTyOk — **THEOREM 1
for `charTyOk`**. -/
theorem charTyOk_spec (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK mode env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.charTyOk oc
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.charTyOk oc'⌝⦄ := by
  cases oc with
  | none =>
    simp only [OptCI] at hrel; subst hrel
    mvcgen [ConRon.Arena.charTyOk]
    all_goals (bridge_peel; subst_vars; exact ⟨hok, Ext.refl _, rfl, rfl⟩)
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    have htc := toConstantVal_spec (mode := mode) (env := env) (fe := fe)
      s₀ ci c hok hci
    mvcgen [ConRon.Arena.charTyOk, ConRon.Arena.sortOne, htc]
    all_goals (bridge_peel; subst_vars)
    case vc3.some.post.success.post.success =>
      rename_i hlp hck hs1 hty hx hp
      refine ⟨hck, hx, hp, ?_⟩
      simp only [ConLeche.charTyOk, isEmpty_of_denoteNList hlp,
        beq_of_denoteE hck.state.wf hty hs1]
    all_goals (apply CheckOK.pins; assumption)

/-! ## 4. The `List` shapes -/

/-- con-leche: none — a one-element name-handle list denotes a one-element
name list, and a list of any other length denotes one of that length. -/
theorem denoteNList_single {st : NStore} {p : NIdx} {xs : List ConLeche.Name}
    (h : Frontend.denoteNList st [p] = some xs) :
    ∃ P, xs = [P] ∧ denoteN st p = some P := by
  simp only [Frontend.denoteNList] at h
  cases hp : denoteN st p with
  | none => simp [hp] at h
  | some P => simp [hp] at h; exact ⟨P, h.symm, rfl⟩

/-- con-leche: none — the same, contrapositively. -/
theorem denoteNList_not_single {st : NStore} {hs : List NIdx}
    {xs : List ConLeche.Name} (h : Frontend.denoteNList st hs = some xs)
    (hn : ∀ p, hs ≠ [p]) : ∀ P, xs ≠ [P] := by
  intro P hP; subst hP
  have hl := denoteNList_len h
  match hs, hl with
  | [p], _ => exact hn p rfl

/-! ### The pure side's shapes

Each guard below matches a NESTED pattern on the stored type, where the twin
views one node at a time and compares each child against an interned
comparand.  These lemmas restate con-leche's guards in the twin's order —
one child at a time, a Boolean test per child — so that each twin exit meets
its pure counterpart in one `simp`. -/

/-- con-leche: none — `Type p`, the sort the `List` shapes are built on. -/
abbrev typeAt (P : ConLeche.Name) : Expr := .sort (.succ (.param P))

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:317-328 listTyOk — at a
one-parameter constant whose type is a `∀`, the two sides against `Type p`. -/
theorem listTyOk_forallE {c : ConstantInfo} {P : ConLeche.Name}
    {D B : Expr} {m : BinderMeta} (hl : c.toConstantVal.levelParams = [P])
    (ht : c.toConstantVal.type = .forallE D B m) :
    ConLeche.listTyOk (some c) = (D == typeAt P && B == typeAt P) := by
  simp only [ConLeche.listTyOk, hl, ht]
  cases D <;> cases B <;> (rw [Bool.eq_iff_iff]; simp [typeAt])

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:317-328 listTyOk — the type is
not a `∀`. -/
theorem listTyOk_not_forallE {c : ConstantInfo} {P : ConLeche.Name}
    (hl : c.toConstantVal.levelParams = [P])
    (ht : ∀ D B m, c.toConstantVal.type ≠ .forallE D B m) :
    ConLeche.listTyOk (some c) = false := by
  simp only [ConLeche.listTyOk, hl]
  split
  · rename_i u1 u2 mb heq; exact absurd heq (ht _ _ _)
  · rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:317-343 — the three `List`
guards at a constant that does not have exactly one level parameter. -/
theorem listTyOks_not_single {c : ConstantInfo}
    (hl : ∀ P, c.toConstantVal.levelParams ≠ [P]) :
    ConLeche.listTyOk (some c) = false ∧ ConLeche.listNilTyOk (some c) = false ∧
      ConLeche.listConsTyOk (some c) = false := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    simp only [ConLeche.listTyOk, ConLeche.listNilTyOk, ConLeche.listConsTyOk]
    try split
    all_goals first
      | rfl
      | (rename_i p heq; exact absurd heq (hl p))

/-- con-leche: none — `listNilTyOk`'s codomain test, `List.{p} (bvar 0)`. -/
def listNilCod (P : ConLeche.Name) : Expr → Bool
  | .app (.const l1 us1) (.bvar 0) => l1 == ConLeche.listName && us1 == [.param P]
  | _ => false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:330-341 listNilTyOk — in the
twin's order: the domain against `Type p`, then the codomain. -/
theorem listNilTyOk_forallE {c : ConstantInfo} {P : ConLeche.Name}
    {D B : Expr} {m : BinderMeta} (hl : c.toConstantVal.levelParams = [P])
    (ht : c.toConstantVal.type = .forallE D B m) :
    ConLeche.listNilTyOk (some c) = (D == typeAt P && listNilCod P B) := by
  simp only [ConLeche.listNilTyOk, hl, ht]
  cases D <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt]; done))
  cases B <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt, listNilCod]; done))
  rename_i F A
  cases F <;> cases A <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt, listNilCod]; done))
  rename_i k
  cases k <;> (rw [Bool.eq_iff_iff]; simp [typeAt, listNilCod, and_assoc])

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:330-360 — the `List.nil` and
`List.cons` guards at a one-parameter constant whose type is not a `∀`. -/
theorem listNilConsTyOk_not_forallE {c : ConstantInfo} {P : ConLeche.Name}
    (hl : c.toConstantVal.levelParams = [P])
    (ht : ∀ D B m, c.toConstantVal.type ≠ .forallE D B m) :
    ConLeche.listNilTyOk (some c) = false ∧
      ConLeche.listConsTyOk (some c) = false := by
  refine ⟨?_, ?_⟩
  · simp only [ConLeche.listNilTyOk, hl]
    split
    · rename_i heq; exact absurd heq (ht _ _ _)
    · rfl
  · simp only [ConLeche.listConsTyOk, hl]
    split
    · rename_i heq; exact absurd heq (ht _ _ _)
    · rfl

/-! ### Interning the comparands -/

/-- con-leche: none — `internLNode (.param p)`'s precondition. -/
theorem lviewOK_param {st : EStore} {p : NIdx} {P : ConLeche.Name}
    (h : denoteN st.ns p = some P) : st.ls.ViewOK (.param p) :=
  ⟨fun c hc => by simp [LNodeView.lchildren] at hc,
   fun c hc => by
     simp [LNodeView.nchildren] at hc; subst hc
     exact nview_isSome_of_denote h⟩

/-- con-leche: none — `internLNode (.succ u)`'s precondition. -/
theorem lviewOK_succ {st : EStore} {u : LIdx} {w : LNodeView}
    (h : st.ls.view u = some w) : st.ls.ViewOK (.succ u) :=
  ⟨fun c hc => by
     simp [LNodeView.lchildren] at hc; subst hc; rw [h]; rfl,
   fun c hc => by simp [LNodeView.nchildren] at hc⟩

/-- con-leche: none — the interned `Type p` of the `List` shapes: a
`param`, a `succ` and a `sort` node over a name handle denoting `P`. -/
theorem denote_typeAt {s₂ s₁ s₀ : AState} {p : NIdx} {r₂ r₁ : LIdx}
    {r₀ : EIdx} {P : ConLeche.Name} (hp : denoteN s₂.store.ns p = some P)
    (h₂ : denoteL s₂.store.ls r₂ = denoteLView s₂.store.ls (.param p))
    (h₁ : denoteL s₁.store.ls r₁ = denoteLView s₁.store.ls (.succ r₂))
    (h₀ : denoteE s₀.store r₀ = denoteEView s₀.store (.sort r₁))
    (x₂₁ : Ext s₂.store s₁.store) (x₁₀ : Ext s₁.store s₀.store) :
    denoteE s₀.store r₀ = some (typeAt P) := by
  have hpl : denoteL s₂.store.ls r₂ = some (.param P) := by
    rw [h₂]; simp only [denoteLView]
    rw [show denoteN s₂.store.ls.ns p = some P from hp]; rfl
  have hsp : denoteL s₁.store.ls r₁ = some (.succ (.param P)) := by
    rw [h₁]; simp [denoteLView, denoteL_ext hpl x₂₁]
  rw [h₀]; simp [denoteEView, denoteL_ext hsp x₁₀, typeAt]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:317-328 listTyOk — **THEOREM 1
for `listTyOk`**. -/
theorem listTyOk_spec (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK mode env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.listTyOk oc
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.listTyOk oc'⌝⦄ := by
  cases oc with
  | none =>
    simp only [OptCI] at hrel; subst hrel
    mvcgen [ConRon.Arena.listTyOk]
    all_goals (bridge_peel; subst_vars; exact ⟨hok, Ext.refl _, rfl, rfl⟩)
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    have htc := toConstantVal_spec (mode := mode) (env := env) (fe := fe)
      s₀ ci c hok hci
    mvcgen [ConRon.Arena.listTyOk, htc]
    all_goals (bridge_peel; subst_vars)
    case vc3.hv =>
      rename_i s1 r0 p0 hsingle s0 ck_s0 d_r0_type_s0 x_s1_s0 p_s0_s1 hlps
      obtain ⟨P, _, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      exact lviewOK_param (denoteN_ext hdp x_s1_s0)
    case vc5.hv =>
      rename_i s2 r1 p0 hsingle s1 r0 s0 ck_s1 wf_s0 x_s1_s0 _ d_r1_type_s1 _ _ _
        c_s0_s1 p_s0_s1 vl_r0_s0 dl_r0_s0 x_s2_s1 p_s1_s2 hlps
      exact lviewOK_succ vl_r0_s0
    case vc7.hv =>
      rename_i s3 r2 p0 hsingle s2 r1 s1 r0 s0 ck_s2 wf_s1 wf_s0 x_s2_s1 x_s1_s0 _
        _ d_r2_type_s2 _ _ _ _ _ _ c_s1_s2 c_s0_s1 p_s1_s2 p_s0_s1 vl_r1_s1
        dl_r1_s1 vl_r0_s0 dl_r0_s0 x_s3_s2 p_s2_s3 hlps
      exact viewOK_sort (by rw [vl_r0_s0]; rfl)
    case vc8.some.post.success.h_1.post.success.post.success.post.success.post.success.h_1 =>
      rename_i s4 r3 p0 hsingle s3 r2 s2 r1 s1 r0 dom0 body0 mb0 s0 ck_s3 wf_s2
        wf_s1 x_s3_s2 x_s2_s1 _ _ d_r3_type_s3 _ _ _ _ _ _ c_s2_s3 c_s1_s2
        p_s2_s3 p_s1_s2 vl_r2_s2 dl_r2_s2 vl_r1_s1 dl_r1_s1 x_s4_s3 p_s3_s4 hlps
        wf_s0 v_r3_type_s0 x_s1_s0 _ _ c_s0_s1 p_s0_s1 _ _ v_r0_s0 d_r0_s0
      have x30 := x_s3_s2.trans (x_s2_s1.trans x_s1_s0)
      refine ⟨ck_s3.mono ⟨wf_s0⟩ x30 (c_s0_s1.trans (c_s1_s2.trans c_s2_s3))
          (p_s0_s1.trans (p_s1_s2.trans p_s2_s3)), x_s4_s3.trans x30,
        p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans p_s3_s4)), ?_⟩
      obtain ⟨P, hP, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      obtain ⟨D, B, hT, hD, hB⟩ :=
        denote_forallE_inv wf_s0 v_r3_type_s0 (denote_ext d_r3_type_s3 x30)
      have hso := denote_typeAt (denoteN_ext hdp (x_s4_s3.trans x_s3_s2))
        dl_r2_s2 dl_r1_s1 d_r0_s0 x_s2_s1 x_s1_s0
      rw [beq_of_denoteE wf_s0 hD hso, beq_of_denoteE wf_s0 hB hso,
        listTyOk_forallE hP hT]
    case vc9.some.post.success.h_1.post.success.post.success.post.success.post.success.h_2 =>
      rename_i s4 r3 p0 hsingle s3 r2 s2 r1 s1 r0 x1 hnot0 s0 ck_s3 wf_s2 wf_s1
        x_s3_s2 x_s2_s1 _ _ d_r3_type_s3 _ _ _ _ _ _ c_s2_s3 c_s1_s2 p_s2_s3
        p_s1_s2 vl_r2_s2 dl_r2_s2 vl_r1_s1 dl_r1_s1 x_s4_s3 p_s3_s4 hlps wf_s0
        v_r3_type_s0 x_s1_s0 _ _ c_s0_s1 p_s0_s1 _ _ v_r0_s0 d_r0_s0
      have x30 := x_s3_s2.trans (x_s2_s1.trans x_s1_s0)
      refine ⟨ck_s3.mono ⟨wf_s0⟩ x30 (c_s0_s1.trans (c_s1_s2.trans c_s2_s3))
          (p_s0_s1.trans (p_s1_s2.trans p_s2_s3)), x_s4_s3.trans x30,
        p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans p_s3_s4)), ?_⟩
      obtain ⟨P, hP, _⟩ := denoteNList_single (hsingle ▸ hlps)
      exact (listTyOk_not_forallE hP (denote_not_forallE wf_s0 v_r3_type_s0
        (denote_ext d_r3_type_s3 x30) hnot0)).symm
    case vc10.some.post.success.h_2 =>
      rename_i s1 r0 s0 ck_s0 d_r0_type_s0 x_s1_s0 p_s0_s1 hlps hnotsingle
      exact ⟨ck_s0, x_s1_s0, p_s0_s1,
        (listTyOks_not_single (denoteNList_not_single hlps hnotsingle)).1.symm⟩
    all_goals first
      | assumption
      | (apply CheckOK.wf'; assumption)

/-- con-leche: none — `listNilCod` at a codomain that is not
`List.{_} (bvar 0)`. -/
theorem listNilCod_of_not {P : ConLeche.Name} {B : Expr}
    (h : ∀ L US, B ≠ .app (.const L US) (.bvar 0)) : listNilCod P B = false := by
  unfold listNilCod
  split
  · rename_i l1 us1; exact absurd rfl (h l1 us1)
  · rfl

/-- con-leche: none — a handle whose view is not `bvar 0` does not denote
`bvar 0`. -/
theorem denote_ne_bvar0 {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} {v : ENodeView} (hv : st.view h = some v)
    (he : denoteE st h = some e) (hne : v = .bvar 0 → False) :
    e ≠ .bvar 0 := by
  rintro rfl
  rw [denoteE_view_eq hwf hv] at he
  cases v <;> simp [denoteEView, Option.map_eq_some_iff, opt2_eq_some_iff] at he
  · subst he; exact hne rfl

/-- con-leche: none — the level-list store's well-formedness, off the
whole store's. -/
theorem StoreWF.lssWF' {st : EStore} (h : StoreWF st) : LsStoreWF st.lss := by
  obtain ⟨rk, hrk⟩ := h; exact hrk.lss

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:330-341 listNilTyOk — **THEOREM
1 for `listNilTyOk`**. -/
theorem listNilTyOk_spec (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK mode env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.listNilTyOk oc
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.listNilTyOk oc'⌝⦄ := by
  cases oc with
  | none =>
    simp only [OptCI] at hrel; subst hrel
    mvcgen [ConRon.Arena.listNilTyOk]
    all_goals (bridge_peel; subst_vars; exact ⟨hok, Ext.refl _, rfl, rfl⟩)
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    have htc := toConstantVal_spec (mode := mode) (env := env) (fe := fe)
      s₀ ci c hok hci
    mvcgen [ConRon.Arena.listNilTyOk, ConRon.Arena.pinList, htc]
    all_goals (bridge_peel; subst_vars)
    case vc3.hv =>
      rename_i s1 r0 p0 hsingle s0 ck_s0 d_r0_type_s0 x_s1_s0 p_s0_s1 hlps
      obtain ⟨P, _, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      exact lviewOK_param (denoteN_ext hdp x_s1_s0)
    case vc5.hv =>
      rename_i s2 r1 p0 hsingle s1 r0 s0 ck_s1 wf_s0 x_s1_s0 _ d_r1_type_s1 _ _ _
        c_s0_s1 p_s0_s1 vl_r0_s0 dl_r0_s0 x_s2_s1 p_s1_s2 hlps
      exact lviewOK_succ vl_r0_s0
    case vc7.hv =>
      rename_i s3 r2 p0 hsingle s2 r1 s1 r0 s0 ck_s2 wf_s1 wf_s0 x_s2_s1 x_s1_s0 _
        _ d_r2_type_s2 _ _ _ _ _ _ c_s1_s2 c_s0_s1 p_s1_s2 p_s0_s1 vl_r1_s1
        dl_r1_s1 vl_r0_s0 dl_r0_s0 x_s3_s2 p_s2_s3 hlps
      exact viewOK_sort (by rw [vl_r0_s0]; rfl)
    case vc9.hv =>
      rename_i s4 r3 p0 hsingle s3 r2 s2 r1 s1 r0 s0 ck_s3 wf_s2 wf_s1 wf_s0 x_s3_s2
        x_s2_s1 x_s1_s0 _ _ _ d_r3_type_s3 _ _ _ _ _ c_s0_s1 _ _ p_s0_s1 c_s2_s3
        c_s1_s2 _ p_s2_s3 p_s1_s2 _ vl_r2_s2 dl_r2_s2 vl_r1_s1 dl_r1_s1 v_r0_s0
        d_r0_s0 x_s4_s3 p_s3_s4 hlps
      obtain ⟨P, _, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      have hpl : denoteL s2.store.ls r2 = some (.param P) := by
        rw [dl_r2_s2]; simp only [denoteLView]
        rw [show denoteN s2.store.ls.ns p0 = some P from
          denoteN_ext hdp (x_s4_s3.trans x_s3_s2)]; rfl
      intro c hc
      simp only [List.mem_singleton] at hc; subst hc
      exact lview_isSome_of_denote (denoteL_ext hpl (x_s2_s1.trans x_s1_s0))
    case vc10.hp =>
      rename_i s5 r4 p0 hsingle s4 r3 s3 r2 s2 r1 s1 r0 s0 ck_s4 wf_s3 wf_s2 wf_s1
        wf_s0 x_s4_s3 x_s3_s2 x_s2_s1 x_s1_s0 _ _ _ _ d_r4_type_s4 _ _ _ _ _ _
        c_s1_s2 _ _ _ p_s1_s2 _ c_s3_s4 c_s2_s3 _ c_s0_s1 p_s3_s4 p_s2_s3 _
        p_s0_s1 vl_r3_s3 dl_r3_s3 vl_r2_s2 dl_r2_s2 v_r1_s1 d_r1_s1 vls_r0_s0
        dls_r0_s0 x_s5_s4 p_s4_s5 hlps
      exact ck_s4.pins.mono (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0)))
        (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans p_s3_s4)))
    case vc11.some.post.success.h_1.post.success.post.success.post.success.post.success.post.success.post.success.h_1.isTrue =>
      rename_i s5 r5 p0 hsingle s4 r4 s3 r3 s2 r2 s1 r1 r0 dom0 body0 mb0 hbeq0 s0
        ck_s4 wf_s3 wf_s2 wf_s1 x_s4_s3 x_s3_s2 x_s2_s1 _ _ _ d_r5_type_s4 _ _ _ _
        _ c_s1_s2 _ _ p_s1_s2 c_s3_s4 c_s2_s3 _ p_s3_s4 p_s2_s3 _ vl_r4_s3
        dl_r4_s3 vl_r3_s2 dl_r3_s2 v_r2_s1 d_r2_s1 x_s5_s4 p_s4_s5 hlps
        v_r5_type_s0 wf_s0 _ x_s1_s0 _ _ _ _ c_s0_s1 p_s0_s1 vls_r1_s0 dls_r1_s0
      have x40 := x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))
      refine ⟨ck_s4.mono ⟨wf_s0⟩ x40
          (c_s0_s1.trans (c_s1_s2.trans (c_s2_s3.trans c_s3_s4)))
          (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans p_s3_s4))),
        x_s5_s4.trans x40,
        (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans p_s3_s4))).trans p_s4_s5,
        ?_⟩
      obtain ⟨P, hP, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      have hty0 := denote_ext d_r5_type_s4 x40
      have hso := denote_ext (denote_typeAt
        (denoteN_ext hdp (x_s5_s4.trans x_s4_s3)) dl_r4_s3 dl_r3_s2 d_r2_s1
        x_s3_s2 x_s2_s1) x_s1_s0
      obtain ⟨D, B, hT, hD, hB⟩ := denote_forallE_inv wf_s0 v_r5_type_s0 hty0
      have hDb := beq_of_denoteE wf_s0 hD hso
      rw [listNilTyOk_forallE hP hT]
      rw [bne, hDb] at hbeq0
      simp only [Bool.not_eq_true', Bool.eq_false_iff] at hbeq0
      simp [hbeq0]
    case vc12.some.post.success.h_1.post.success.post.success.post.success.post.success.post.success.post.success.h_1.isFalse.post.success.h_1.post.success.h_1.post.success.h_1 =>
      rename_i s5 r5 p0 hsingle s4 r4 s3 r3 s2 r2 s1 r1 r0 dom0 body0 mb0 hneg0 f20
        a0 c0 us0 s0 ck_s4 wf_s3 wf_s2 wf_s1 x_s4_s3 x_s3_s2 x_s2_s1 _ _ _
        d_r5_type_s4 _ _ _ _ _ c_s1_s2 _ _ p_s1_s2 c_s3_s4 c_s2_s3 _ p_s3_s4
        p_s2_s3 _ vl_r4_s3 dl_r4_s3 vl_r3_s2 dl_r3_s2 v_r2_s1 d_r2_s1 x_s5_s4
        p_s4_s5 hlps v_a0_s0 v_f20_s0 v_body0_s0 v_r5_type_s0 wf_s0 hpin x_s1_s0
        _ _ _ _ c_s0_s1 p_s0_s1 vls_r1_s0 dls_r1_s0
      have x40 := x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))
      refine ⟨ck_s4.mono ⟨wf_s0⟩ x40
          (c_s0_s1.trans (c_s1_s2.trans (c_s2_s3.trans c_s3_s4)))
          (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans p_s3_s4))),
        x_s5_s4.trans x40,
        (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans p_s3_s4))).trans p_s4_s5,
        ?_⟩
      obtain ⟨P, hP, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      have hty0 := denote_ext d_r5_type_s4 x40
      have hso := denote_ext (denote_typeAt
        (denoteN_ext hdp (x_s5_s4.trans x_s4_s3)) dl_r4_s3 dl_r3_s2 d_r2_s1
        x_s3_s2 x_s2_s1) x_s1_s0
      obtain ⟨D, B, hT, hD, hB⟩ := denote_forallE_inv wf_s0 v_r5_type_s0 hty0
      have hDb := beq_of_denoteE wf_s0 hD hso
      rw [listNilTyOk_forallE hP hT]
      rw [bne, hDb] at hneg0
      have hDe : D = typeAt P := by simpa using hneg0
      subst hDe
      obtain ⟨F, A, rfl, hF, hA⟩ := denote_app_inv wf_s0 v_body0_s0 hB
      obtain ⟨L, US, rfl, hL, hUS⟩ := denote_const_inv wf_s0 v_f20_s0 hF
      obtain rfl := denote_bvar_inv wf_s0 v_a0_s0 hA
      have hpl : denoteL s0.store.ls r4 = some (.param P) := by
        refine denoteL_ext ?_ (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))
        rw [dl_r4_s3]; simp only [denoteLView]
        rw [show denoteN s3.store.ls.ns p0 = some P from
          denoteN_ext hdp (x_s5_s4.trans x_s4_s3)]; rfl
      have hps : denoteLs s0.store.lss r1 = some [.param P] := by
        rw [dls_r1_s0]
        simp [denoteLsView, denoteLList, opt2,
          show denoteL s0.store.lss.ls r4 = some (Level.param P) from hpl]
      rw [pinBeq wf_s0 hL (hpin _ rfl),
        beq_of_denoteLs (StoreWF.lssWF' wf_s0) hUS hps]
      simp [listNilCod]
    case vc13.some.post.success.h_1.post.success.post.success.post.success.post.success.post.success.post.success.h_1.isFalse.post.success.h_1.post.success.h_1.post.success.h_2 =>
      rename_i s5 r5 p0 hsingle s4 r4 s3 r3 s2 r2 s1 r1 r0 dom0 body0 mb0 hneg0 f20
        a0 c0 us0 x1 hnb s0 ck_s4 wf_s3 wf_s2 wf_s1 x_s4_s3 x_s3_s2 x_s2_s1 _ _ _
        d_r5_type_s4 _ _ _ _ _ c_s1_s2 _ _ p_s1_s2 c_s3_s4 c_s2_s3 _ p_s3_s4
        p_s2_s3 _ vl_r4_s3 dl_r4_s3 vl_r3_s2 dl_r3_s2 v_r2_s1 d_r2_s1 x_s5_s4
        p_s4_s5 hlps v_a0_s0 v_f20_s0 v_body0_s0 v_r5_type_s0 wf_s0 hpin x_s1_s0
        _ _ _ _ c_s0_s1 p_s0_s1 vls_r1_s0 dls_r1_s0
      have x40 := x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))
      refine ⟨ck_s4.mono ⟨wf_s0⟩ x40
          (c_s0_s1.trans (c_s1_s2.trans (c_s2_s3.trans c_s3_s4)))
          (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans p_s3_s4))),
        x_s5_s4.trans x40,
        (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans p_s3_s4))).trans p_s4_s5,
        ?_⟩
      obtain ⟨P, hP, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      have hty0 := denote_ext d_r5_type_s4 x40
      have hso := denote_ext (denote_typeAt
        (denoteN_ext hdp (x_s5_s4.trans x_s4_s3)) dl_r4_s3 dl_r3_s2 d_r2_s1
        x_s3_s2 x_s2_s1) x_s1_s0
      obtain ⟨D, B, hT, hD, hB⟩ := denote_forallE_inv wf_s0 v_r5_type_s0 hty0
      have hDb := beq_of_denoteE wf_s0 hD hso
      rw [listNilTyOk_forallE hP hT]
      obtain ⟨F, A, rfl, hF, hA⟩ := denote_app_inv wf_s0 v_body0_s0 hB
      have hA0 := denote_ne_bvar0 wf_s0 v_a0_s0 hA hnb
      rw [listNilCod_of_not (fun L US h => by cases h; exact hA0 rfl)]
      simp
    case vc14.some.post.success.h_1.post.success.post.success.post.success.post.success.post.success.post.success.h_1.isFalse.post.success.h_1.post.success.h_2 =>
      rename_i s5 r5 p0 hsingle s4 r4 s3 r3 s2 r2 s1 r1 r0 dom0 body0 mb0 hneg0 f20
        a0 x1 hnot0 s0 ck_s4 wf_s3 wf_s2 wf_s1 x_s4_s3 x_s3_s2 x_s2_s1 _ _ _
        d_r5_type_s4 _ _ _ _ _ c_s1_s2 _ _ p_s1_s2 c_s3_s4 c_s2_s3 _ p_s3_s4
        p_s2_s3 _ vl_r4_s3 dl_r4_s3 vl_r3_s2 dl_r3_s2 v_r2_s1 d_r2_s1 x_s5_s4
        p_s4_s5 hlps v_f20_s0 v_body0_s0 v_r5_type_s0 wf_s0 hpin x_s1_s0 _ _ _ _
        c_s0_s1 p_s0_s1 vls_r1_s0 dls_r1_s0
      have x40 := x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))
      refine ⟨ck_s4.mono ⟨wf_s0⟩ x40
          (c_s0_s1.trans (c_s1_s2.trans (c_s2_s3.trans c_s3_s4)))
          (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans p_s3_s4))),
        x_s5_s4.trans x40,
        (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans p_s3_s4))).trans p_s4_s5,
        ?_⟩
      obtain ⟨P, hP, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      have hty0 := denote_ext d_r5_type_s4 x40
      have hso := denote_ext (denote_typeAt
        (denoteN_ext hdp (x_s5_s4.trans x_s4_s3)) dl_r4_s3 dl_r3_s2 d_r2_s1
        x_s3_s2 x_s2_s1) x_s1_s0
      obtain ⟨D, B, hT, hD, hB⟩ := denote_forallE_inv wf_s0 v_r5_type_s0 hty0
      have hDb := beq_of_denoteE wf_s0 hD hso
      rw [listNilTyOk_forallE hP hT]
      obtain ⟨F, A, rfl, hF, hA⟩ := denote_app_inv wf_s0 v_body0_s0 hB
      have hF0 := denote_not_const wf_s0 v_f20_s0 hF hnot0
      rw [listNilCod_of_not (fun L US h => by cases h; exact hF0 L US rfl)]
      simp
    case vc15.some.post.success.h_1.post.success.post.success.post.success.post.success.post.success.post.success.h_1.isFalse.post.success.h_2 =>
      rename_i s5 r5 p0 hsingle s4 r4 s3 r3 s2 r2 s1 r1 r0 dom0 body0 mb0 hneg0 x1
        hnot0 s0 ck_s4 wf_s3 wf_s2 wf_s1 x_s4_s3 x_s3_s2 x_s2_s1 _ _ _
        d_r5_type_s4 _ _ _ _ _ c_s1_s2 _ _ p_s1_s2 c_s3_s4 c_s2_s3 _ p_s3_s4
        p_s2_s3 _ vl_r4_s3 dl_r4_s3 vl_r3_s2 dl_r3_s2 v_r2_s1 d_r2_s1 x_s5_s4
        p_s4_s5 hlps v_body0_s0 v_r5_type_s0 wf_s0 _ x_s1_s0 _ _ _ _ c_s0_s1
        p_s0_s1 vls_r1_s0 dls_r1_s0
      have x40 := x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))
      refine ⟨ck_s4.mono ⟨wf_s0⟩ x40
          (c_s0_s1.trans (c_s1_s2.trans (c_s2_s3.trans c_s3_s4)))
          (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans p_s3_s4))),
        x_s5_s4.trans x40,
        (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans p_s3_s4))).trans p_s4_s5,
        ?_⟩
      obtain ⟨P, hP, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      have hty0 := denote_ext d_r5_type_s4 x40
      have hso := denote_ext (denote_typeAt
        (denoteN_ext hdp (x_s5_s4.trans x_s4_s3)) dl_r4_s3 dl_r3_s2 d_r2_s1
        x_s3_s2 x_s2_s1) x_s1_s0
      obtain ⟨D, B, hT, hD, hB⟩ := denote_forallE_inv wf_s0 v_r5_type_s0 hty0
      have hDb := beq_of_denoteE wf_s0 hD hso
      rw [listNilTyOk_forallE hP hT]
      have hB0 := denote_not_app wf_s0 v_body0_s0 hB hnot0
      rw [listNilCod_of_not (fun L US h => hB0 _ _ h)]
      simp
    case vc16.some.post.success.h_1.post.success.post.success.post.success.post.success.post.success.post.success.h_2 =>
      rename_i s5 r5 p0 hsingle s4 r4 s3 r3 s2 r2 s1 r1 r0 x1 hnot0 s0 ck_s4 wf_s3
        wf_s2 wf_s1 x_s4_s3 x_s3_s2 x_s2_s1 _ _ _ d_r5_type_s4 _ _ _ _ _ c_s1_s2 _
        _ p_s1_s2 c_s3_s4 c_s2_s3 _ p_s3_s4 p_s2_s3 _ vl_r4_s3 dl_r4_s3 vl_r3_s2
        dl_r3_s2 v_r2_s1 d_r2_s1 x_s5_s4 p_s4_s5 hlps v_r5_type_s0 wf_s0 _
        x_s1_s0 _ _ _ _ c_s0_s1 p_s0_s1 vls_r1_s0 dls_r1_s0
      have x40 := x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))
      refine ⟨ck_s4.mono ⟨wf_s0⟩ x40
          (c_s0_s1.trans (c_s1_s2.trans (c_s2_s3.trans c_s3_s4)))
          (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans p_s3_s4))),
        x_s5_s4.trans x40,
        (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans p_s3_s4))).trans p_s4_s5,
        ?_⟩
      obtain ⟨P, hP, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      have hty0 := denote_ext d_r5_type_s4 x40
      have hso := denote_ext (denote_typeAt
        (denoteN_ext hdp (x_s5_s4.trans x_s4_s3)) dl_r4_s3 dl_r3_s2 d_r2_s1
        x_s3_s2 x_s2_s1) x_s1_s0
      exact (listNilConsTyOk_not_forallE hP
        (denote_not_forallE wf_s0 v_r5_type_s0 hty0 hnot0)).1.symm
    case vc17.some.post.success.h_2 =>
      rename_i s1 r0 s0 ck_s0 d_r0_type_s0 x_s1_s0 p_s0_s1 hlps hnotsingle
      exact ⟨ck_s0, x_s1_s0, p_s0_s1,
        (listTyOks_not_single (denoteNList_not_single hlps hnotsingle)).2.1.symm⟩
    all_goals first
      | assumption
      | (apply CheckOK.wf'; assumption)

/-- con-leche: none — `List.{p} (bvar k)`, the `List.cons` shape's two
applications. -/
abbrev listApp (P : ConLeche.Name) (k : Nat) : Expr :=
  .app (.const ConLeche.listName [.param P]) (.bvar k)

/-- con-leche: none — `listConsTyOk`'s innermost `∀`, in the twin's order. -/
def listConsR2 (P : ConLeche.Name) : Expr → Bool
  | .forallE D3 C3 _ => D3 == listApp P 1 && C3 == listApp P 2
  | _ => false

/-- con-leche: none — `listConsTyOk`'s middle `∀`, in the twin's order. -/
def listConsR (P : ConLeche.Name) : Expr → Bool
  | .forallE D2 R2 _ => D2 == .bvar 0 && listConsR2 P R2
  | _ => false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:343-360 listConsTyOk — in the
twin's order: each binder's domain against its interned comparand, one `∀`
at a time. -/
theorem listConsTyOk_forallE {c : ConstantInfo} {P : ConLeche.Name}
    {D R : Expr} {m : BinderMeta} (hl : c.toConstantVal.levelParams = [P])
    (ht : c.toConstantVal.type = .forallE D R m) :
    ConLeche.listConsTyOk (some c) = (D == typeAt P && listConsR P R) := by
  simp only [ConLeche.listConsTyOk, hl, ht]
  cases D <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt]; done))
  cases R <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt, listConsR]; done))
  rename_i D2 R2 _
  cases D2 <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt, listConsR]; done))
  rename_i k
  cases k <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt, listConsR]; done))
  cases R2 <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt, listConsR, listConsR2]; done))
  rename_i D3 C3 _
  cases D3 <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt, listConsR, listConsR2]; done))
  rename_i F3 A3
  cases F3 <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt, listConsR, listConsR2]; done))
  cases A3 <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt, listConsR, listConsR2]; done))
  rename_i k3
  cases C3 <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt, listConsR, listConsR2]; done))
  rename_i F4 A4
  cases F4 <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt, listConsR, listConsR2]; done))
  cases A4 <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt, listConsR, listConsR2]; done))
  all_goals (rw [Bool.eq_iff_iff]; simp [typeAt, listConsR, listConsR2]; try grind)

/-- con-leche: none — `listConsR` at a codomain that is not a `∀`. -/
theorem listConsR_of_not {P : ConLeche.Name} {R : Expr}
    (h : ∀ D B m, R ≠ .forallE D B m) : listConsR P R = false := by
  unfold listConsR; split
  · rename_i D B m; exact absurd rfl (h D B m)
  · rfl

/-- con-leche: none — `listConsR2` at a codomain that is not a `∀`. -/
theorem listConsR2_of_not {P : ConLeche.Name} {R : Expr}
    (h : ∀ D B m, R ≠ .forallE D B m) : listConsR2 P R = false := by
  unfold listConsR2; split
  · rename_i D B m; exact absurd rfl (h D B m)
  · rfl

/-! ### The interned comparands' denotations, one node at a time -/

/-- con-leche: none — an interned `bvar k`. -/
theorem denote_view_bvar {st : EStore} {h : EIdx} {k : Nat}
    (hd : denoteE st h = denoteEView st (.bvar k)) :
    denoteE st h = some (.bvar k) := by rw [hd]; rfl

/-- con-leche: none — an interned constant. -/
theorem denote_view_const {st : EStore} {h : EIdx} {n : NIdx} {us : LsIdx}
    {N : ConLeche.Name} {US : List Level}
    (hd : denoteE st h = denoteEView st (.const n us))
    (hn : denoteN st.ns n = some N) (hus : denoteLs st.lss us = some US) :
    denoteE st h = some (.const N US) := by
  rw [hd]; simp [denoteEView, opt2, hn, hus]

/-- con-leche: none — an interned application. -/
theorem denote_view_app {st : EStore} {h f a : EIdx} {F A : Expr}
    (hd : denoteE st h = denoteEView st (.app f a))
    (hf : denoteE st f = some F) (ha : denoteE st a = some A) :
    denoteE st h = some (.app F A) := by
  rw [hd]; simp [denoteEView, opt2, hf, ha]

/-- con-leche: none — an interned `param`. -/
theorem denoteL_view_param {st : EStore} {h : LIdx} {p : NIdx}
    {P : ConLeche.Name}
    (hd : denoteL st.ls h = denoteLView st.ls (.param p))
    (hp : denoteN st.ns p = some P) : denoteL st.ls h = some (.param P) := by
  rw [hd]; simp only [denoteLView]
  rw [show denoteN st.ls.ns p = some P from hp]; rfl

/-- con-leche: none — an interned one-element level list. -/
theorem denoteLs_view_single {st : EStore} {h : LsIdx} {u : LIdx}
    {U : Level} (hd : denoteLs st.lss h = denoteLsView st.lss [u])
    (hu : denoteL st.ls u = some U) : denoteLs st.lss h = some [U] := by
  rw [hd]
  simp [denoteLsView, denoteLList, opt2,
    show denoteL st.lss.ls u = some U from hu]

/-- con-leche: none — a denoting level-list handle has a view. -/
theorem lsview_isSome_of_denote {st : LsStore} {h : LsIdx}
    {xs : List Level} (hd : denoteLs st h = some xs) :
    (st.view h).isSome = true := by
  obtain ⟨w, hw, _⟩ := denoteLs_view hd; rw [hw]; rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:343-360 listConsTyOk — **THEOREM
1 for `listConsTyOk`**. -/
theorem listConsTyOk_spec (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK mode env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.listConsTyOk oc
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.listConsTyOk oc'⌝⦄ := by
  cases oc with
  | none =>
    simp only [OptCI] at hrel; subst hrel
    mvcgen [ConRon.Arena.listConsTyOk]
    all_goals (bridge_peel; subst_vars; exact ⟨hok, Ext.refl _, rfl, rfl⟩)
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    have htc := toConstantVal_spec (mode := mode) (env := env) (fe := fe)
      s₀ ci c hok hci
    mvcgen [ConRon.Arena.listConsTyOk, ConRon.Arena.pinList, htc]
    all_goals (bridge_peel; subst_vars)
    case vc3.hv =>
      rename_i s1 r0 p0 hsingle s0 ck_s0 d_r0_type_s0 x_s1_s0 p_s0_s1 hlps
      obtain ⟨P, _, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      exact lviewOK_param (denoteN_ext hdp x_s1_s0)
    case vc5.hv =>
      rename_i s2 r1 p0 hsingle s1 r0 s0 ck_s1 wf_s0 x_s1_s0 _ d_r1_type_s1 _ _ _
        c_s0_s1 p_s0_s1 vl_r0_s0 dl_r0_s0 x_s2_s1 p_s1_s2 hlps
      exact lviewOK_succ vl_r0_s0
    case vc7.hv =>
      rename_i s3 r2 p0 hsingle s2 r1 s1 r0 s0 ck_s2 wf_s1 wf_s0 x_s2_s1 x_s1_s0 _
        _ d_r2_type_s2 _ _ _ _ _ _ c_s1_s2 c_s0_s1 p_s1_s2 p_s0_s1 vl_r1_s1
        dl_r1_s1 vl_r0_s0 dl_r0_s0 x_s3_s2 p_s2_s3 hlps
      exact viewOK_sort (by rw [vl_r0_s0]; rfl)
    case vc9.hv =>
      rename_i s4 r3 p0 hsingle s3 r2 s2 r1 s1 r0 s0 ck_s3 wf_s2 wf_s1 wf_s0 x_s3_s2
        x_s2_s1 x_s1_s0 _ _ _ d_r3_type_s3 _ _ _ _ _ c_s0_s1 _ _ p_s0_s1 c_s2_s3
        c_s1_s2 _ p_s2_s3 p_s1_s2 _ vl_r2_s2 dl_r2_s2 vl_r1_s1 dl_r1_s1 v_r0_s0
        d_r0_s0 x_s4_s3 p_s3_s4 hlps
      obtain ⟨P, _, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      have hpl := denoteL_view_param dl_r2_s2
        (denoteN_ext hdp (x_s4_s3.trans x_s3_s2))
      intro c hc
      simp only [List.mem_singleton] at hc; subst hc
      exact lview_isSome_of_denote (denoteL_ext hpl (x_s2_s1.trans x_s1_s0))
    case vc10.hp =>
      rename_i s5 r4 p0 hsingle s4 r3 s3 r2 s2 r1 s1 r0 s0 ck_s4 wf_s3 wf_s2 wf_s1
        wf_s0 x_s4_s3 x_s3_s2 x_s2_s1 x_s1_s0 _ _ _ _ d_r4_type_s4 _ _ _ _ _ _
        c_s1_s2 _ _ _ p_s1_s2 _ c_s3_s4 c_s2_s3 _ c_s0_s1 p_s3_s4 p_s2_s3 _
        p_s0_s1 vl_r3_s3 dl_r3_s3 vl_r2_s2 dl_r2_s2 v_r1_s1 d_r1_s1 vls_r0_s0
        dls_r0_s0 x_s5_s4 p_s4_s5 hlps
      exact ck_s4.pins.mono (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0)))
        (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans p_s3_s4)))
    case vc18.hv =>
      rename_i s8 r8 p0 hsingle s7 r7 s6 r6 s5 r5 s4 r4 r3 s3 r2 s2 r1 s1 r0 s0
        ck_s7 wf_s6 wf_s5 wf_s4 wf_s2 wf_s1 wf_s0 x_s7_s6 x_s6_s5 x_s5_s4 x_s3_s2
        x_s2_s1 x_s1_s0 _ _ _ _ _ _ d_r8_type_s7 _ _ _ _ _ _ _ _ c_s4_s5 c_s2_s3
        c_s1_s2 c_s0_s1 _ _ p_s4_s5 p_s2_s3 p_s1_s2 p_s0_s1 c_s6_s7 c_s5_s6 _ _ _
        _ p_s6_s7 p_s5_s6 _ _ _ _ vl_r7_s6 dl_r7_s6 vl_r6_s5 dl_r6_s5 v_r5_s4
        d_r5_s4 v_r2_s2 d_r2_s2 v_r1_s1 d_r1_s1 v_r0_s0 d_r0_s0 x_s8_s7 p_s7_s8
        hlps wf_s3 hpin x_s4_s3 _ _ _ _ c_s3_s4 p_s3_s4 vls_r4_s3 dls_r4_s3
      obtain ⟨P, _, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      have hpl := denoteL_view_param dl_r7_s6
        (denoteN_ext hdp (x_s8_s7.trans x_s7_s6))
      have hps := denoteLs_view_single dls_r4_s3
        (denoteL_ext hpl (x_s6_s5.trans (x_s5_s4.trans x_s4_s3)))
      have x30 := x_s3_s2.trans (x_s2_s1.trans x_s1_s0)
      exact viewOK_const (nview_isSome_of_denote (denoteN_ext (hpin _ rfl) x30))
        (lsview_isSome_of_denote (denoteLs_ext hps x30))
    case vc20.hv =>
      rename_i s9 r9 p0 hsingle s8 r8 s7 r7 s6 r6 s5 r5 r4 s4 r3 s3 r2 s2 r1 s1 r0 s0
        ck_s8 wf_s7 wf_s6 wf_s5 wf_s3 wf_s2 wf_s1 wf_s0 x_s8_s7 x_s7_s6 x_s6_s5
        x_s4_s3 x_s3_s2 x_s2_s1 x_s1_s0 _ _ _ _ _ _ _ d_r9_type_s8 _ _ _ _ _ _ _ _
        _ c_s5_s6 c_s3_s4 c_s2_s3 c_s1_s2 c_s0_s1 _ _ p_s5_s6 p_s3_s4 p_s2_s3
        p_s1_s2 p_s0_s1 c_s7_s8 c_s6_s7 _ _ _ _ _ p_s7_s8 p_s6_s7 _ _ _ _ _
        vl_r8_s7 dl_r8_s7 vl_r7_s6 dl_r7_s6 v_r6_s5 d_r6_s5 v_r3_s3 d_r3_s3
        v_r2_s2 d_r2_s2 v_r1_s1 d_r1_s1 v_r0_s0 d_r0_s0 x_s9_s8 p_s8_s9 hlps
        wf_s4 hpin x_s5_s4 _ _ _ _ c_s4_s5 p_s4_s5 vls_r5_s4 dls_r5_s4
      obtain ⟨P, _, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      have hpl := denoteL_view_param dl_r8_s7
        (denoteN_ext hdp (x_s9_s8.trans x_s8_s7))
      have hps := denoteLs_view_single dls_r5_s4
        (denoteL_ext hpl (x_s7_s6.trans (x_s6_s5.trans x_s5_s4)))
      have x40 := x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))
      have hl1 := denote_view_const d_r0_s0 (denoteN_ext (hpin _ rfl) x40)
        (denoteLs_ext hps x40)
      have hb1 := denote_ext (denote_view_bvar d_r2_s2) (x_s2_s1.trans x_s1_s0)
      exact viewOK_app (by rw [hl1]; rfl) (by rw [hb1]; rfl)
    case vc22.hv =>
      rename_i s10 r10 p0 hsingle s9 r9 s8 r8 s7 r7 s6 r6 r5 s5 r4 s4 r3 s3 r2 s2
        r1 s1 r0 s0 ck_s9 wf_s8 wf_s7 wf_s6 wf_s4 wf_s3 wf_s2 wf_s1 wf_s0 x_s9_s8
        x_s8_s7 x_s7_s6 x_s5_s4 x_s4_s3 x_s3_s2 x_s2_s1 x_s1_s0 _ _ _ _ _ _ _ _
        d_r10_type_s9 _ _ _ _ _ _ _ _ _ _ c_s6_s7 c_s4_s5 c_s3_s4 c_s2_s3 c_s1_s2
        c_s0_s1 _ _ p_s6_s7 p_s4_s5 p_s3_s4 p_s2_s3 p_s1_s2 p_s0_s1 c_s8_s9
        c_s7_s8 _ _ _ _ _ _ p_s8_s9 p_s7_s8 _ _ _ _ _ _ vl_r9_s8 dl_r9_s8
        vl_r8_s7 dl_r8_s7 v_r7_s6 d_r7_s6 v_r4_s4 d_r4_s4 v_r3_s3 d_r3_s3 v_r2_s2
        d_r2_s2 v_r1_s1 d_r1_s1 v_r0_s0 d_r0_s0 x_s10_s9 p_s9_s10 hlps wf_s5 hpin
        x_s6_s5 _ _ _ _ c_s5_s6 p_s5_s6 vls_r6_s5 dls_r6_s5
      obtain ⟨P, _, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      have hpl := denoteL_view_param dl_r9_s8
        (denoteN_ext hdp (x_s10_s9.trans x_s9_s8))
      have hps := denoteLs_view_single dls_r6_s5
        (denoteL_ext hpl (x_s8_s7.trans (x_s7_s6.trans x_s6_s5)))
      have x51 := x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans x_s2_s1))
      have hl1 := denote_view_const d_r1_s1 (denoteN_ext (hpin _ rfl) x51)
        (denoteLs_ext hps x51)
      exact viewOK_app (by rw [denote_ext hl1 x_s1_s0]; rfl)
        (by rw [denote_ext (denote_view_bvar d_r2_s2) (x_s2_s1.trans x_s1_s0)]; rfl)
    case vc23.some.post.success.h_1.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.h_1.isTrue =>
      rename_i s11 r11 p0 hsingle s10 r10 s9 r9 s8 r8 s7 r7 r6 s6 r5 s5 r4 s4
        r3 s3 r2 s2 r1 s1 r0 dom0 body0 mb0 hbeq0 s0 ck_s10 wf_s9 wf_s8 wf_s7
        wf_s5 wf_s4 wf_s3 wf_s2 wf_s1 x_s10_s9 x_s9_s8 x_s8_s7 x_s6_s5 x_s5_s4
        x_s4_s3 x_s3_s2 x_s2_s1 _ _ _ _ _ _ _ _ d_r11_type_s10 _ _ _ _ _ _ _ _
        _ _ c_s7_s8 c_s5_s6 c_s4_s5 c_s3_s4 c_s2_s3 c_s1_s2 _ _ p_s7_s8
        p_s5_s6 p_s4_s5 p_s3_s4 p_s2_s3 p_s1_s2 c_s9_s10 c_s8_s9 _ _ _ _ _ _
        p_s9_s10 p_s8_s9 _ _ _ _ _ _ vl_r10_s9 dl_r10_s9 vl_r9_s8 dl_r9_s8
        v_r8_s7 d_r8_s7 v_r5_s5 d_r5_s5 v_r4_s4 d_r4_s4 v_r3_s3 d_r3_s3
        v_r2_s2 d_r2_s2 v_r1_s1 d_r1_s1 x_s11_s10 p_s10_s11 hlps wf_s6 hpin
        x_s7_s6 _ _ _ _ c_s6_s7 p_s6_s7 vls_r7_s6 dls_r7_s6 wf_s0
        v_r11_type_s0 x_s1_s0 _ _ c_s0_s1 p_s0_s1 _ _ v_r0_s0 d_r0_s0
      have x100 := (x_s10_s9.trans (x_s9_s8.trans (x_s8_s7.trans (x_s7_s6.trans (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0)))))))))
      refine ⟨ck_s10.mono ⟨wf_s0⟩ x100 (c_s0_s1.trans (c_s1_s2.trans (c_s2_s3.trans (c_s3_s4.trans (c_s4_s5.trans (c_s5_s6.trans (c_s6_s7.trans (c_s7_s8.trans (c_s8_s9.trans c_s9_s10))))))))) (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4.trans (p_s4_s5.trans (p_s5_s6.trans (p_s6_s7.trans (p_s7_s8.trans (p_s8_s9.trans p_s9_s10))))))))),
        x_s11_s10.trans x100, (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4.trans (p_s4_s5.trans (p_s5_s6.trans (p_s6_s7.trans (p_s7_s8.trans (p_s8_s9.trans p_s9_s10))))))))).trans p_s10_s11, ?_⟩
      obtain ⟨P, hP, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      have hp9 := denoteN_ext hdp (x_s11_s10.trans x_s10_s9)
      have hso := denote_ext (denote_typeAt hp9 dl_r10_s9 dl_r9_s8 d_r8_s7
        x_s9_s8 x_s8_s7) (x_s7_s6.trans (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))))))
      have hty0 := denote_ext d_r11_type_s10 x100
      have hwf0 := wf_s0
      obtain ⟨D, R, hT, hD, _⟩ := denote_forallE_inv hwf0 v_r11_type_s0 hty0
      rw [bne, beq_of_denoteE hwf0 hD hso] at hbeq0
      simp only [Bool.not_eq_true', Bool.eq_false_iff] at hbeq0
      rw [listConsTyOk_forallE hP hT]; simp [hbeq0]
    case vc24.some.post.success.h_1.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.h_1.isFalse.post.success.h_1.isTrue =>
      rename_i s11 r11 p0 hsingle s10 r10 s9 r9 s8 r8 s7 r7 r6 s6 r5 s5 r4 s4
        r3 s3 r2 s2 r1 s1 r0 dom1 body1 mb1 hneg0 dom0 body0 mb0 hbeq0 s0
        ck_s10 wf_s9 wf_s8 wf_s7 wf_s5 wf_s4 wf_s3 wf_s2 wf_s1 x_s10_s9
        x_s9_s8 x_s8_s7 x_s6_s5 x_s5_s4 x_s4_s3 x_s3_s2 x_s2_s1 _ _ _ _ _ _ _
        _ d_r11_type_s10 _ _ _ _ _ _ _ _ _ _ c_s7_s8 c_s5_s6 c_s4_s5 c_s3_s4
        c_s2_s3 c_s1_s2 _ _ p_s7_s8 p_s5_s6 p_s4_s5 p_s3_s4 p_s2_s3 p_s1_s2
        c_s9_s10 c_s8_s9 _ _ _ _ _ _ p_s9_s10 p_s8_s9 _ _ _ _ _ _ vl_r10_s9
        dl_r10_s9 vl_r9_s8 dl_r9_s8 v_r8_s7 d_r8_s7 v_r5_s5 d_r5_s5 v_r4_s4
        d_r4_s4 v_r3_s3 d_r3_s3 v_r2_s2 d_r2_s2 v_r1_s1 d_r1_s1 x_s11_s10
        p_s10_s11 hlps wf_s6 hpin x_s7_s6 _ _ _ _ c_s6_s7 p_s6_s7 vls_r7_s6
        dls_r7_s6 v_body1_s0 wf_s0 v_r11_type_s0 x_s1_s0 _ _ c_s0_s1 p_s0_s1 _
        _ v_r0_s0 d_r0_s0
      have x100 := (x_s10_s9.trans (x_s9_s8.trans (x_s8_s7.trans (x_s7_s6.trans (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0)))))))))
      refine ⟨ck_s10.mono ⟨wf_s0⟩ x100 (c_s0_s1.trans (c_s1_s2.trans (c_s2_s3.trans (c_s3_s4.trans (c_s4_s5.trans (c_s5_s6.trans (c_s6_s7.trans (c_s7_s8.trans (c_s8_s9.trans c_s9_s10))))))))) (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4.trans (p_s4_s5.trans (p_s5_s6.trans (p_s6_s7.trans (p_s7_s8.trans (p_s8_s9.trans p_s9_s10))))))))),
        x_s11_s10.trans x100, (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4.trans (p_s4_s5.trans (p_s5_s6.trans (p_s6_s7.trans (p_s7_s8.trans (p_s8_s9.trans p_s9_s10))))))))).trans p_s10_s11, ?_⟩
      obtain ⟨P, hP, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      have hp9 := denoteN_ext hdp (x_s11_s10.trans x_s10_s9)
      have hso := denote_ext (denote_typeAt hp9 dl_r10_s9 dl_r9_s8 d_r8_s7
        x_s9_s8 x_s8_s7) (x_s7_s6.trans (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))))))
      have hty0 := denote_ext d_r11_type_s10 x100
      have hwf0 := wf_s0
      have hpl := denoteL_view_param dl_r10_s9 hp9
      have hps := denoteLs_view_single dls_r7_s6 (denoteL_ext hpl (x_s9_s8.trans (x_s8_s7.trans x_s7_s6)))
      have hl1 := denote_view_const d_r2_s2 (denoteN_ext (hpin _ rfl) (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans x_s3_s2))))
        (denoteLs_ext hps (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans x_s3_s2))))
      have hb0 := denote_ext (denote_view_bvar d_r5_s5) (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))))
      have hd3 := denote_ext (denote_view_app d_r1_s1 (denote_ext hl1 x_s2_s1)
        (denote_ext (denote_view_bvar d_r4_s4) (x_s4_s3.trans (x_s3_s2.trans x_s2_s1)))) x_s1_s0
      have hc3 := denote_view_app d_r0_s0 (denote_ext hl1 (x_s2_s1.trans x_s1_s0))
        (denote_ext (denote_view_bvar d_r3_s3) (x_s3_s2.trans (x_s2_s1.trans x_s1_s0)))
      obtain ⟨D, R, hT, hD, hR⟩ := denote_forallE_inv hwf0 v_r11_type_s0 hty0
      obtain ⟨D2, R2, rfl, hD2, _⟩ := denote_forallE_inv hwf0 v_body1_s0 hR
      rw [bne, beq_of_denoteE hwf0 hD2 hb0] at hbeq0
      simp only [Bool.not_eq_true', Bool.eq_false_iff] at hbeq0
      rw [listConsTyOk_forallE hP hT]; simp [listConsR, hbeq0]
    case vc25.some.post.success.h_1.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.h_1.isFalse.post.success.h_1.isFalse.post.success.h_1 =>
      rename_i s11 r11 p0 hsingle s10 r10 s9 r9 s8 r8 s7 r7 r6 s6 r5 s5 r4 s4
        r3 s3 r2 s2 r1 s1 r0 dom2 body2 mb2 hneg0 dom1 body1 mb1 hneg1 dom0
        body0 mb0 s0 ck_s10 wf_s9 wf_s8 wf_s7 wf_s5 wf_s4 wf_s3 wf_s2 wf_s1
        x_s10_s9 x_s9_s8 x_s8_s7 x_s6_s5 x_s5_s4 x_s4_s3 x_s3_s2 x_s2_s1 _ _ _
        _ _ _ _ _ d_r11_type_s10 _ _ _ _ _ _ _ _ _ _ c_s7_s8 c_s5_s6 c_s4_s5
        c_s3_s4 c_s2_s3 c_s1_s2 _ _ p_s7_s8 p_s5_s6 p_s4_s5 p_s3_s4 p_s2_s3
        p_s1_s2 c_s9_s10 c_s8_s9 _ _ _ _ _ _ p_s9_s10 p_s8_s9 _ _ _ _ _ _
        vl_r10_s9 dl_r10_s9 vl_r9_s8 dl_r9_s8 v_r8_s7 d_r8_s7 v_r5_s5 d_r5_s5
        v_r4_s4 d_r4_s4 v_r3_s3 d_r3_s3 v_r2_s2 d_r2_s2 v_r1_s1 d_r1_s1
        x_s11_s10 p_s10_s11 hlps wf_s6 hpin x_s7_s6 _ _ _ _ c_s6_s7 p_s6_s7
        vls_r7_s6 dls_r7_s6 v_body1_s0 v_body2_s0 wf_s0 v_r11_type_s0 x_s1_s0
        _ _ c_s0_s1 p_s0_s1 _ _ v_r0_s0 d_r0_s0
      have x100 := (x_s10_s9.trans (x_s9_s8.trans (x_s8_s7.trans (x_s7_s6.trans (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0)))))))))
      refine ⟨ck_s10.mono ⟨wf_s0⟩ x100 (c_s0_s1.trans (c_s1_s2.trans (c_s2_s3.trans (c_s3_s4.trans (c_s4_s5.trans (c_s5_s6.trans (c_s6_s7.trans (c_s7_s8.trans (c_s8_s9.trans c_s9_s10))))))))) (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4.trans (p_s4_s5.trans (p_s5_s6.trans (p_s6_s7.trans (p_s7_s8.trans (p_s8_s9.trans p_s9_s10))))))))),
        x_s11_s10.trans x100, (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4.trans (p_s4_s5.trans (p_s5_s6.trans (p_s6_s7.trans (p_s7_s8.trans (p_s8_s9.trans p_s9_s10))))))))).trans p_s10_s11, ?_⟩
      obtain ⟨P, hP, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      have hp9 := denoteN_ext hdp (x_s11_s10.trans x_s10_s9)
      have hso := denote_ext (denote_typeAt hp9 dl_r10_s9 dl_r9_s8 d_r8_s7
        x_s9_s8 x_s8_s7) (x_s7_s6.trans (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))))))
      have hty0 := denote_ext d_r11_type_s10 x100
      have hwf0 := wf_s0
      have hpl := denoteL_view_param dl_r10_s9 hp9
      have hps := denoteLs_view_single dls_r7_s6 (denoteL_ext hpl (x_s9_s8.trans (x_s8_s7.trans x_s7_s6)))
      have hl1 := denote_view_const d_r2_s2 (denoteN_ext (hpin _ rfl) (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans x_s3_s2))))
        (denoteLs_ext hps (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans x_s3_s2))))
      have hb0 := denote_ext (denote_view_bvar d_r5_s5) (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))))
      have hd3 := denote_ext (denote_view_app d_r1_s1 (denote_ext hl1 x_s2_s1)
        (denote_ext (denote_view_bvar d_r4_s4) (x_s4_s3.trans (x_s3_s2.trans x_s2_s1)))) x_s1_s0
      have hc3 := denote_view_app d_r0_s0 (denote_ext hl1 (x_s2_s1.trans x_s1_s0))
        (denote_ext (denote_view_bvar d_r3_s3) (x_s3_s2.trans (x_s2_s1.trans x_s1_s0)))
      obtain ⟨D, R, hT, hD, hR⟩ := denote_forallE_inv hwf0 v_r11_type_s0 hty0
      obtain ⟨D2, R2, rfl, hD2, hR2⟩ := denote_forallE_inv hwf0 v_body2_s0 hR
      obtain ⟨D3, C3, rfl, hD3, hC3⟩ := denote_forallE_inv hwf0 v_body1_s0 hR2
      have hDe : D = typeAt P := by
        rw [bne, beq_of_denoteE hwf0 hD hso] at hneg0; simpa using hneg0
      have hD2e : D2 = .bvar 0 := by
        rw [bne, beq_of_denoteE hwf0 hD2 hb0] at hneg1; simpa using hneg1
      subst hDe hD2e
      rw [beq_of_denoteE hwf0 hD3 hd3, beq_of_denoteE hwf0 hC3 hc3,
        listConsTyOk_forallE hP hT]
      simp [listConsR, listConsR2]
    case vc26.some.post.success.h_1.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.h_1.isFalse.post.success.h_1.isFalse.post.success.h_2 =>
      rename_i s11 r11 p0 hsingle s10 r10 s9 r9 s8 r8 s7 r7 r6 s6 r5 s5 r4 s4
        r3 s3 r2 s2 r1 s1 r0 dom1 body1 mb1 hneg0 dom0 body0 mb0 hneg1 x1
        hnot0 s0 ck_s10 wf_s9 wf_s8 wf_s7 wf_s5 wf_s4 wf_s3 wf_s2 wf_s1
        x_s10_s9 x_s9_s8 x_s8_s7 x_s6_s5 x_s5_s4 x_s4_s3 x_s3_s2 x_s2_s1 _ _ _
        _ _ _ _ _ d_r11_type_s10 _ _ _ _ _ _ _ _ _ _ c_s7_s8 c_s5_s6 c_s4_s5
        c_s3_s4 c_s2_s3 c_s1_s2 _ _ p_s7_s8 p_s5_s6 p_s4_s5 p_s3_s4 p_s2_s3
        p_s1_s2 c_s9_s10 c_s8_s9 _ _ _ _ _ _ p_s9_s10 p_s8_s9 _ _ _ _ _ _
        vl_r10_s9 dl_r10_s9 vl_r9_s8 dl_r9_s8 v_r8_s7 d_r8_s7 v_r5_s5 d_r5_s5
        v_r4_s4 d_r4_s4 v_r3_s3 d_r3_s3 v_r2_s2 d_r2_s2 v_r1_s1 d_r1_s1
        x_s11_s10 p_s10_s11 hlps wf_s6 hpin x_s7_s6 _ _ _ _ c_s6_s7 p_s6_s7
        vls_r7_s6 dls_r7_s6 v_body0_s0 v_body1_s0 wf_s0 v_r11_type_s0 x_s1_s0
        _ _ c_s0_s1 p_s0_s1 _ _ v_r0_s0 d_r0_s0
      have x100 := (x_s10_s9.trans (x_s9_s8.trans (x_s8_s7.trans (x_s7_s6.trans (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0)))))))))
      refine ⟨ck_s10.mono ⟨wf_s0⟩ x100 (c_s0_s1.trans (c_s1_s2.trans (c_s2_s3.trans (c_s3_s4.trans (c_s4_s5.trans (c_s5_s6.trans (c_s6_s7.trans (c_s7_s8.trans (c_s8_s9.trans c_s9_s10))))))))) (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4.trans (p_s4_s5.trans (p_s5_s6.trans (p_s6_s7.trans (p_s7_s8.trans (p_s8_s9.trans p_s9_s10))))))))),
        x_s11_s10.trans x100, (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4.trans (p_s4_s5.trans (p_s5_s6.trans (p_s6_s7.trans (p_s7_s8.trans (p_s8_s9.trans p_s9_s10))))))))).trans p_s10_s11, ?_⟩
      obtain ⟨P, hP, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      have hp9 := denoteN_ext hdp (x_s11_s10.trans x_s10_s9)
      have hso := denote_ext (denote_typeAt hp9 dl_r10_s9 dl_r9_s8 d_r8_s7
        x_s9_s8 x_s8_s7) (x_s7_s6.trans (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))))))
      have hty0 := denote_ext d_r11_type_s10 x100
      have hwf0 := wf_s0
      have hpl := denoteL_view_param dl_r10_s9 hp9
      have hps := denoteLs_view_single dls_r7_s6 (denoteL_ext hpl (x_s9_s8.trans (x_s8_s7.trans x_s7_s6)))
      have hl1 := denote_view_const d_r2_s2 (denoteN_ext (hpin _ rfl) (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans x_s3_s2))))
        (denoteLs_ext hps (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans x_s3_s2))))
      have hb0 := denote_ext (denote_view_bvar d_r5_s5) (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))))
      have hd3 := denote_ext (denote_view_app d_r1_s1 (denote_ext hl1 x_s2_s1)
        (denote_ext (denote_view_bvar d_r4_s4) (x_s4_s3.trans (x_s3_s2.trans x_s2_s1)))) x_s1_s0
      have hc3 := denote_view_app d_r0_s0 (denote_ext hl1 (x_s2_s1.trans x_s1_s0))
        (denote_ext (denote_view_bvar d_r3_s3) (x_s3_s2.trans (x_s2_s1.trans x_s1_s0)))
      obtain ⟨D, R, hT, hD, hR⟩ := denote_forallE_inv hwf0 v_r11_type_s0 hty0
      obtain ⟨D2, R2, rfl, hD2, hR2⟩ := denote_forallE_inv hwf0 v_body1_s0 hR
      rw [listConsTyOk_forallE hP hT]
      simp only [listConsR,
        listConsR2_of_not (denote_not_forallE hwf0 v_body0_s0 hR2 hnot0)]
      simp
    case vc27.some.post.success.h_1.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.h_1.isFalse.post.success.h_2 =>
      rename_i s11 r11 p0 hsingle s10 r10 s9 r9 s8 r8 s7 r7 r6 s6 r5 s5 r4 s4
        r3 s3 r2 s2 r1 s1 r0 dom0 body0 mb0 hneg0 x1 hnot0 s0 ck_s10 wf_s9
        wf_s8 wf_s7 wf_s5 wf_s4 wf_s3 wf_s2 wf_s1 x_s10_s9 x_s9_s8 x_s8_s7
        x_s6_s5 x_s5_s4 x_s4_s3 x_s3_s2 x_s2_s1 _ _ _ _ _ _ _ _ d_r11_type_s10
        _ _ _ _ _ _ _ _ _ _ c_s7_s8 c_s5_s6 c_s4_s5 c_s3_s4 c_s2_s3 c_s1_s2 _
        _ p_s7_s8 p_s5_s6 p_s4_s5 p_s3_s4 p_s2_s3 p_s1_s2 c_s9_s10 c_s8_s9 _ _
        _ _ _ _ p_s9_s10 p_s8_s9 _ _ _ _ _ _ vl_r10_s9 dl_r10_s9 vl_r9_s8
        dl_r9_s8 v_r8_s7 d_r8_s7 v_r5_s5 d_r5_s5 v_r4_s4 d_r4_s4 v_r3_s3
        d_r3_s3 v_r2_s2 d_r2_s2 v_r1_s1 d_r1_s1 x_s11_s10 p_s10_s11 hlps wf_s6
        hpin x_s7_s6 _ _ _ _ c_s6_s7 p_s6_s7 vls_r7_s6 dls_r7_s6 v_body0_s0
        wf_s0 v_r11_type_s0 x_s1_s0 _ _ c_s0_s1 p_s0_s1 _ _ v_r0_s0 d_r0_s0
      have x100 := (x_s10_s9.trans (x_s9_s8.trans (x_s8_s7.trans (x_s7_s6.trans (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0)))))))))
      refine ⟨ck_s10.mono ⟨wf_s0⟩ x100 (c_s0_s1.trans (c_s1_s2.trans (c_s2_s3.trans (c_s3_s4.trans (c_s4_s5.trans (c_s5_s6.trans (c_s6_s7.trans (c_s7_s8.trans (c_s8_s9.trans c_s9_s10))))))))) (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4.trans (p_s4_s5.trans (p_s5_s6.trans (p_s6_s7.trans (p_s7_s8.trans (p_s8_s9.trans p_s9_s10))))))))),
        x_s11_s10.trans x100, (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4.trans (p_s4_s5.trans (p_s5_s6.trans (p_s6_s7.trans (p_s7_s8.trans (p_s8_s9.trans p_s9_s10))))))))).trans p_s10_s11, ?_⟩
      obtain ⟨P, hP, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      have hp9 := denoteN_ext hdp (x_s11_s10.trans x_s10_s9)
      have hso := denote_ext (denote_typeAt hp9 dl_r10_s9 dl_r9_s8 d_r8_s7
        x_s9_s8 x_s8_s7) (x_s7_s6.trans (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))))))
      have hty0 := denote_ext d_r11_type_s10 x100
      have hwf0 := wf_s0
      obtain ⟨D, R, hT, hD, hR⟩ := denote_forallE_inv hwf0 v_r11_type_s0 hty0
      rw [listConsTyOk_forallE hP hT,
        listConsR_of_not (denote_not_forallE hwf0 v_body0_s0 hR hnot0)]
      simp
    case vc28.some.post.success.h_1.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.post.success.h_2 =>
      rename_i s11 r11 p0 hsingle s10 r10 s9 r9 s8 r8 s7 r7 r6 s6 r5 s5 r4 s4
        r3 s3 r2 s2 r1 s1 r0 x1 hnot0 s0 ck_s10 wf_s9 wf_s8 wf_s7 wf_s5 wf_s4
        wf_s3 wf_s2 wf_s1 x_s10_s9 x_s9_s8 x_s8_s7 x_s6_s5 x_s5_s4 x_s4_s3
        x_s3_s2 x_s2_s1 _ _ _ _ _ _ _ _ d_r11_type_s10 _ _ _ _ _ _ _ _ _ _
        c_s7_s8 c_s5_s6 c_s4_s5 c_s3_s4 c_s2_s3 c_s1_s2 _ _ p_s7_s8 p_s5_s6
        p_s4_s5 p_s3_s4 p_s2_s3 p_s1_s2 c_s9_s10 c_s8_s9 _ _ _ _ _ _ p_s9_s10
        p_s8_s9 _ _ _ _ _ _ vl_r10_s9 dl_r10_s9 vl_r9_s8 dl_r9_s8 v_r8_s7
        d_r8_s7 v_r5_s5 d_r5_s5 v_r4_s4 d_r4_s4 v_r3_s3 d_r3_s3 v_r2_s2
        d_r2_s2 v_r1_s1 d_r1_s1 x_s11_s10 p_s10_s11 hlps wf_s6 hpin x_s7_s6 _
        _ _ _ c_s6_s7 p_s6_s7 vls_r7_s6 dls_r7_s6 wf_s0 v_r11_type_s0 x_s1_s0
        _ _ c_s0_s1 p_s0_s1 _ _ v_r0_s0 d_r0_s0
      have x100 := (x_s10_s9.trans (x_s9_s8.trans (x_s8_s7.trans (x_s7_s6.trans (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0)))))))))
      refine ⟨ck_s10.mono ⟨wf_s0⟩ x100 (c_s0_s1.trans (c_s1_s2.trans (c_s2_s3.trans (c_s3_s4.trans (c_s4_s5.trans (c_s5_s6.trans (c_s6_s7.trans (c_s7_s8.trans (c_s8_s9.trans c_s9_s10))))))))) (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4.trans (p_s4_s5.trans (p_s5_s6.trans (p_s6_s7.trans (p_s7_s8.trans (p_s8_s9.trans p_s9_s10))))))))),
        x_s11_s10.trans x100, (p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4.trans (p_s4_s5.trans (p_s5_s6.trans (p_s6_s7.trans (p_s7_s8.trans (p_s8_s9.trans p_s9_s10))))))))).trans p_s10_s11, ?_⟩
      obtain ⟨P, hP, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      have hp9 := denoteN_ext hdp (x_s11_s10.trans x_s10_s9)
      have hso := denote_ext (denote_typeAt hp9 dl_r10_s9 dl_r9_s8 d_r8_s7
        x_s9_s8 x_s8_s7) (x_s7_s6.trans (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans x_s1_s0))))))
      have hty0 := denote_ext d_r11_type_s10 x100
      have hwf0 := wf_s0
      exact (listNilConsTyOk_not_forallE hP
        (denote_not_forallE hwf0 v_r11_type_s0 hty0 hnot0)).2.symm
    case vc29.some.post.success.h_2 =>
      rename_i s1 r0 s0 ck_s0 d_r0_type_s0 x_s1_s0 p_s0_s1 hlps hnotsingle
      exact ⟨ck_s0, x_s1_s0, p_s0_s1,
        (listTyOks_not_single (denoteNList_not_single hlps hnotsingle)).2.2.symm⟩
    all_goals first
      | assumption
      | (apply CheckOK.wf'; assumption)
      | exact viewOK_bvar

end ConRon.Bridge.Core

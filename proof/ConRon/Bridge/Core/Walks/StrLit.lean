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

end ConRon.Bridge.Core

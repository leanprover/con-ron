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
`beq_of_denoteLs`, `beq_handle_eq`) makes the two the same test.

Also here, because the two inference bodies' `.const` clauses need it and a
`Walks/` module is where a callee fact belongs: `denoteCI_nonTower`, the
constant lookup's two facts behind the tower-entry guard, and
`toConstantVal_spec`, the stored constant's common data in general (the
`.projInfo` arm INTERNS its `Sort 1`).
-/
import ConRon.Bridge.Core.Walks.Nat

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

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
  | thmInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨cv, hcv, rfl⟩ := h; exact ⟨rfl, v, rfl, hcv⟩
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
    ⦃fun s => s = s₀⦄ ci.toConstantVal
    ⦃fun cv s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        Frontend.denoteNList s₀.store.ns cv.levelParams =
          some c.toConstantVal.levelParams ∧
        denoteE s'.store cv.type = some c.toConstantVal.type; ⊤⦄ := by
  have hwf := hok.state.wf
  cases hti : ci.isTowerEntry
  · obtain ⟨_, v, hv, hcv⟩ := denoteCI_nonTower hci hti
    obtain ⟨_, hlp, hty⟩ := denoteCV_inv hcv
    rw [hv]
    vcgen
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
      vcgen [IConstantInfo.toConstantVal]
      all_goals (bridge_peel; subst_vars)
      all_goals clear_tag_hyps
      case vc1 =>
        rename_i _ sA sB _ _ _ w3 x1 x2 x3 _ _ _ _ _ _ _ _ c3 _ _ p3 c1 c2 _ p1 p2 _ d3 _ d1
          _ d2
        have h0 : denoteL sA.store.ls z = some Level.zero := by
          rw [d1]; simp [denoteLView]
        have h1 : denoteL sB.store.ls one = some (Level.succ .zero) := by
          rw [d2]; simp [denoteLView, denoteL_ext h0 x2]
        refine ⟨hok.mono ⟨w3⟩ (x1.trans (x2.trans x3))
            (c3.trans (c2.trans c1)) (p3.trans (p2.trans p1)),
          x1.trans (x2.trans x3), p3.trans (p2.trans p1), hlp, ?_⟩
        rw [d3]; simp [denoteEView, denoteL_ext h1 x3,
          ConstantInfo.toConstantVal]
      case vc7 =>
        constructor
        · intro c hc; simp [LNodeView.lchildren] at hc
        · intro c hc; simp [LNodeView.nchildren] at hc
      case vc5 =>
        rename_i hv0 _
        constructor
        · intro c hc; simp [LNodeView.lchildren] at hc; subst hc
          rw [hv0]; rfl
        · intro c hc; simp [LNodeView.nchildren] at hc
      case vc3 =>
        rename_i hv1 _
        exact viewOK_sort (by rw [hv1]; rfl)
      all_goals assumption
    | _ => simp [IConstantInfo.isTowerEntry] at hti

/-! ## 3. The two `Type`-valued shapes: `String` and `Char` -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:301-307 stringTyOk — **THEOREM 1
for `stringTyOk`**. -/
theorem stringTyOk_spec (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK mode env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => s = s₀⦄ ConRon.Arena.stringTyOk oc
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.stringTyOk oc'; ⊤⦄ := by
  cases oc with
  | none =>
    simp only [OptCI] at hrel; subst hrel
    vcgen [ConRon.Arena.stringTyOk]
    all_goals (bridge_peel; subst_vars; exact ⟨hok, Ext.refl _, rfl, rfl⟩)
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    have htc := toConstantVal_spec (mode := mode) (env := env) (fe := fe)
      s₀ ci c hok hci
    vcgen [ConRon.Arena.stringTyOk, ConRon.Arena.sortOne, htc]
    all_goals (bridge_peel; subst_vars)
    all_goals clear_tag_hyps
    case vc1 =>
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
    ⦃fun s => s = s₀⦄ ConRon.Arena.charTyOk oc
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.charTyOk oc'; ⊤⦄ := by
  cases oc with
  | none =>
    simp only [OptCI] at hrel; subst hrel
    vcgen [ConRon.Arena.charTyOk]
    all_goals (bridge_peel; subst_vars; exact ⟨hok, Ext.refl _, rfl, rfl⟩)
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    have htc := toConstantVal_spec (mode := mode) (env := env) (fe := fe)
      s₀ ci c hok hci
    vcgen [ConRon.Arena.charTyOk, ConRon.Arena.sortOne, htc]
    all_goals (bridge_peel; subst_vars)
    all_goals clear_tag_hyps
    case vc1 =>
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
    {D B : Expr} (hl : c.toConstantVal.levelParams = [P])
    (ht : c.toConstantVal.type = .forallE D B) :
    ConLeche.listTyOk (some c) = (D == typeAt P && B == typeAt P) := by
  simp only [ConLeche.listTyOk, hl, ht]
  cases D <;> cases B <;> (rw [Bool.eq_iff_iff]; simp [typeAt])

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:317-328 listTyOk — the type is
not a `∀`. -/
theorem listTyOk_not_forallE {c : ConstantInfo} {P : ConLeche.Name}
    (hl : c.toConstantVal.levelParams = [P])
    (ht : ∀ D B, c.toConstantVal.type ≠ .forallE D B) :
    ConLeche.listTyOk (some c) = false := by
  simp only [ConLeche.listTyOk, hl]
  split
  · rename_i u1 u2 heq; exact absurd heq (ht _ _)
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
    {D B : Expr} (hl : c.toConstantVal.levelParams = [P])
    (ht : c.toConstantVal.type = .forallE D B) :
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
    (ht : ∀ D B, c.toConstantVal.type ≠ .forallE D B) :
    ConLeche.listNilTyOk (some c) = false ∧
      ConLeche.listConsTyOk (some c) = false := by
  refine ⟨?_, ?_⟩
  · simp only [ConLeche.listNilTyOk, hl]
    split
    · rename_i heq; exact absurd heq (ht _ _)
    · rfl
  · simp only [ConLeche.listConsTyOk, hl]
    split
    · rename_i heq; exact absurd heq (ht _ _)
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

/-! ### Staged interning (task #119: the shapes are proved stage by stage) -/

/-- con-leche: none — **a `pure` exit** at a pinned state. -/
theorem triple_pureS {α : Type} {s₀ : AState} {v : α}
    {Q : α → AState → Prop} (h : Q v s₀) :
    ⦃fun s => s = s₀⦄ (pure v : AM α) ⦃fun r s => Q r s; ⊤⦄ := by
  vcgen
  subst_vars; exact h

/-- con-leche: none — `internLNode` at the tier's invariant. -/
theorem internLNode_okS (s₀ : AState) (w : LNodeView)
    (hok : CheckOK mode env fe s₀) (hv : s₀.store.ls.ViewOK w) :
    ⦃fun s => s = s₀⦄ internLNode w
    ⦃fun h s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ s'.store.ls.view h = some w ∧
        denoteL s'.store.ls h = denoteLView s'.store.ls w; ⊤⦄ :=
  triple_mono (internLNode_spec s₀ w hok.state.wf hv)
    (fun _ _ ⟨hwf', hx', _, _, _, _, hc', hp', hv', hd⟩ =>
      ⟨hok.mono ⟨hwf'⟩ hx' hc' hp', hx', hp', hv', hd⟩)

/-- con-leche: none — `internLsNode` at the tier's invariant. -/
theorem internLsNode_okS (s₀ : AState) (w : LsNodeView)
    (hok : CheckOK mode env fe s₀) (hv : s₀.store.lss.ViewOK w) :
    ⦃fun s => s = s₀⦄ internLsNode w
    ⦃fun h s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ s'.store.lss.view h = some w ∧
        denoteLs s'.store.lss h = denoteLsView s'.store.lss w; ⊤⦄ :=
  triple_mono (internLsNode_spec s₀ w hok.state.wf hv)
    (fun _ _ ⟨hwf', hx', _, _, _, _, hc', hp', hv', hd⟩ =>
      ⟨hok.mono ⟨hwf'⟩ hx' hc' hp', hx', hp', hv', hd⟩)

/-- con-leche: none — `internE` at the tier's invariant. -/
theorem internE_okS (s₀ : AState) (w : ENodeView)
    (hok : CheckOK mode env fe s₀) (hv : s₀.store.ViewOK w) :
    ⦃fun s => s = s₀⦄ internE w
    ⦃fun h s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ s'.store.view h = some w ∧
        denoteE s'.store h = denoteEView s'.store w; ⊤⦄ :=
  triple_mono (internE_spec s₀ w hok.state.wf hv)
    (fun _ _ ⟨hwf', hx', _, _, _, hc', hp', hv', hd⟩ =>
      ⟨hok.mono ⟨hwf'⟩ hx' hc' hp', hx', hp', hv', hd⟩)

/-- con-leche: none — a pinned name, off the table. -/
theorem pinAt_okS (s₀ : AState) (i : Nat) (hok : CheckOK mode env fe s₀) :
    ⦃fun s => s = s₀⦄ pinAt i
    ⦃fun n s' => s' = s₀ ∧ ∀ x, pinNames[i]? = some x →
        denoteN s₀.store.ns n = some x; ⊤⦄ :=
  pinAt_spec s₀ i hok.pins

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:317-328 listTyOk — **THEOREM 1
for `listTyOk`**. -/
theorem listTyOk_spec (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK mode env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => s = s₀⦄ ConRon.Arena.listTyOk oc
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.listTyOk oc'; ⊤⦄ := by
  cases oc with
  | none =>
    simp only [OptCI] at hrel; subst hrel
    vcgen [ConRon.Arena.listTyOk]
    all_goals (bridge_peel; subst_vars; exact ⟨hok, Ext.refl _, rfl, rfl⟩)
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    simp only [ConRon.Arena.listTyOk]
    refine triple_seq (toConstantVal_spec s₀ ci c hok hci) ?_
    rintro cv s1 ⟨hok1, hx1, hp1, hlp, hty⟩
    split
    rotate_left
    · rename_i hnotsingle
      exact triple_pureS ⟨hok1, hx1, hp1,
        (listTyOks_not_single (denoteNList_not_single hlp hnotsingle)).1.symm⟩
    rename_i p hsingle
    rw [hsingle] at hlp
    obtain ⟨P, hP, hdp⟩ := denoteNList_single hlp
    refine triple_seq (internLNode_okS s1 (.param p) hok1
      (lviewOK_param (denoteN_ext hdp hx1))) ?_
    rintro pl s2 ⟨hok2, hx2, hp2, hv2, hd2⟩
    refine triple_seq (internLNode_okS s2 (.succ pl) hok2 (lviewOK_succ hv2)) ?_
    rintro sp s3 ⟨hok3, hx3, hp3, hv3, hd3⟩
    refine triple_seq (internE_okS s3 (.sort sp) hok3
      (viewOK_sort (by rw [hv3]; rfl))) ?_
    rintro so s4 ⟨hok4, hx4, hp4, _, hd4⟩
    have hpl : denoteL s2.store.ls pl = some (.param P) :=
      denoteL_view_param hd2 (denoteN_ext hdp (hx1.trans hx2))
    have hso : denoteE s4.store so = some (typeAt P) :=
      denote_typeAt (denoteN_ext hdp (hx1.trans hx2)) hd2 hd3 hd4 hx3 hx4
    have hx14 : Ext s1.store s4.store := hx2.trans (hx3.trans hx4)
    have hx04 : Ext s₀.store s4.store := hx1.trans hx14
    have hp04 : s4.pins = s₀.pins := hp4.trans (hp3.trans (hp2.trans hp1))
    have hty4 := denote_ext hty hx14
    have hwf4 := hok4.state.wf
    obtain ⟨v, hv⟩ := denoteE_view hty4
    refine tag_view_bind_triple hv ?_
      (fun hne => by cases v <;> first | rfl | exact absurd rfl hne)
    cases v
    case forallE d b =>
      obtain ⟨D, B, hT, hD, hB⟩ := denote_forallE_inv hwf4 hv hty4
      dsimp only
      refine triple_pureS ⟨hok4, hx04, hp04, ?_⟩
      rw [beq_of_denoteE hwf4 hD hso, beq_of_denoteE hwf4 hB hso,
        listTyOk_forallE hP hT]
    all_goals
      dsimp only
      exact triple_pureS ⟨hok4, hx04, hp04, (listTyOk_not_forallE hP
        (denote_not_forallE hwf4 hv hty4 (fun _ _ h => nomatch h))).symm⟩
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
    ⦃fun s => s = s₀⦄ ConRon.Arena.listNilTyOk oc
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.listNilTyOk oc'; ⊤⦄ := by
  cases oc with
  | none =>
    simp only [OptCI] at hrel; subst hrel
    vcgen [ConRon.Arena.listNilTyOk]
    all_goals (bridge_peel; subst_vars; exact ⟨hok, Ext.refl _, rfl, rfl⟩)
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    simp only [ConRon.Arena.listNilTyOk]
    refine triple_seq (toConstantVal_spec s₀ ci c hok hci) ?_
    rintro cv s1 ⟨hok1, hx1, hp1, hlp, hty⟩
    split
    rotate_left
    · rename_i hnotsingle
      exact triple_pureS ⟨hok1, hx1, hp1,
        (listTyOks_not_single (denoteNList_not_single hlp hnotsingle)).2.1.symm⟩
    rename_i p hsingle
    rw [hsingle] at hlp
    obtain ⟨P, hP, hdp⟩ := denoteNList_single hlp
    refine triple_seq (internLNode_okS s1 (.param p) hok1
      (lviewOK_param (denoteN_ext hdp hx1))) ?_
    rintro pl s2 ⟨hok2, hx2, hp2, hv2, hd2⟩
    refine triple_seq (internLNode_okS s2 (.succ pl) hok2 (lviewOK_succ hv2)) ?_
    rintro sp s3 ⟨hok3, hx3, hp3, hv3, hd3⟩
    refine triple_seq (internE_okS s3 (.sort sp) hok3
      (viewOK_sort (by rw [hv3]; rfl))) ?_
    rintro so s4 ⟨hok4, hx4, hp4, _, hd4⟩
    have hpl : denoteL s2.store.ls pl = some (.param P) :=
      denoteL_view_param hd2 (denoteN_ext hdp (hx1.trans hx2))
    have hso : denoteE s4.store so = some (typeAt P) :=
      denote_typeAt (denoteN_ext hdp (hx1.trans hx2)) hd2 hd3 hd4 hx3 hx4
    have hx14 : Ext s1.store s4.store := hx2.trans (hx3.trans hx4)
    refine triple_seq (internLsNode_okS s4 [pl] hok4 (by
      intro c hc
      simp only [List.mem_singleton] at hc; subst hc
      exact lview_isSome_of_denote (denoteL_ext hpl (hx3.trans hx4)))) ?_
    rintro ps s5 ⟨hok5, hx5, hp5, _, hd5⟩
    have hps : denoteLs s5.store.lss ps = some [.param P] :=
      denoteLs_view_single hd5 (denoteL_ext hpl ((hx3.trans hx4).trans hx5))
    simp only [ConRon.Arena.pinList]
    refine triple_seq (pinAt_okS s5 _ hok5) ?_
    rintro li s6 ⟨hs6, hli⟩
    subst s6
    have hli' : denoteN s5.store.ns li = some ConLeche.listName := hli _ rfl
    have hx15 : Ext s1.store s5.store := hx14.trans hx5
    have hx05 : Ext s₀.store s5.store := hx1.trans hx15
    have hp05 : s5.pins = s₀.pins :=
      hp5.trans (hp4.trans (hp3.trans (hp2.trans hp1)))
    have hso5 := denote_ext hso hx5
    have hty5 := denote_ext hty hx15
    have hwf5 := hok5.state.wf
    have hfalse : ∀ (b : Bool), b = ConLeche.listNilTyOk (some c) →
        ⦃fun s => s = s5⦄ (pure b : AM Bool)
        ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ r = ConLeche.listNilTyOk (some c); ⊤⦄ :=
      fun b hb => triple_pureS ⟨hok5, hx05, hp05, hb⟩
    obtain ⟨v, hv⟩ := denoteE_view hty5
    refine tag_view_bind_triple hv ?_
      (fun hne => by cases v <;> first | rfl | exact absurd rfl hne)
    cases v
    case forallE d b =>
      obtain ⟨D, B, hT, hD, hB⟩ := denote_forallE_inv hwf5 hv hty5
      rw [listNilTyOk_forallE hP hT] at hfalse ⊢
      dsimp only
      rw [bne, beq_of_denoteE hwf5 hD hso5]
      by_cases hDe : (D == typeAt P) = true
      · rw [hDe]
        simp only [Bool.not_true, Bool.false_eq_true, ite_false, Bool.true_and]
        simp only [hDe, Bool.true_and] at hfalse
        obtain ⟨vb, hvb⟩ := denoteE_view hB
        refine tag_view_bind_triple hvb ?_
          (fun hne => by cases vb <;> first | rfl | exact absurd rfl hne)
        cases vb
        case app f a =>
          obtain ⟨F, A, rfl, hF, hA⟩ := denote_app_inv hwf5 hvb hB
          dsimp only
          obtain ⟨vf, hvf⟩ := denoteE_view hF
          refine tag_view_bind_triple hvf ?_
            (fun hne => by cases vf <;> first | rfl | exact absurd rfl hne)
          cases vf
          case const l1 us1 =>
            obtain ⟨L, US, rfl, hL, hUS⟩ := denote_const_inv hwf5 hvf hF
            dsimp only
            obtain ⟨va, hva⟩ := denoteE_view hA
            refine tag_view_bind_triple hva ?_
              (fun hne => by cases va <;> first | rfl | exact absurd rfl hne)
            cases va
            case bvar k =>
              obtain rfl := denote_bvar_inv hwf5 hva hA
              cases k with
              | zero =>
                try dsimp only
                refine hfalse _ ?_
                rw [beq_handle_eq hwf5 hL hli',
                  beq_of_denoteLs (StoreWF.lssWF' hwf5) hUS hps]
                simp [listNilCod]
              | succ k =>
                try dsimp only
                exact hfalse _ (by simp [listNilCod])
            all_goals
              dsimp only
              refine hfalse _ (listNilCod_of_not (fun L' US' h => ?_)).symm
              injection h with h1 h2
              exact denote_ne_bvar0 hwf5 hva hA (fun h => nomatch h) h2
          all_goals
            dsimp only
            refine hfalse _ (listNilCod_of_not (fun L' US' h => ?_)).symm
            injection h with h1 h2
            exact denote_not_const hwf5 hvf hF (fun _ _ h => nomatch h) _ _ h1
        all_goals
          dsimp only
          refine hfalse _ (listNilCod_of_not (fun L' US' h => ?_)).symm
          exact denote_not_app hwf5 hvb hB (fun _ _ h => nomatch h) _ _ h
      · have hDf : (D == typeAt P) = false := by simpa using hDe
        rw [hDf]
        simp only [Bool.not_false, ite_true]
        exact triple_pureS ⟨hok5, hx05, hp05, by simp⟩
    all_goals
      dsimp only
      exact hfalse _ (listNilConsTyOk_not_forallE hP
        (denote_not_forallE hwf5 hv hty5 (fun _ _ h => nomatch h))).1.symm
/-- con-leche: none — `List.{p} (bvar k)`, the `List.cons` shape's two
applications. -/
abbrev listApp (P : ConLeche.Name) (k : Nat) : Expr :=
  .app (.const ConLeche.listName [.param P]) (.bvar k)

/-- con-leche: none — `listConsTyOk`'s innermost `∀`, in the twin's order. -/
def listConsR2 (P : ConLeche.Name) : Expr → Bool
  | .forallE D3 C3 => D3 == listApp P 1 && C3 == listApp P 2
  | _ => false

/-- con-leche: none — `listConsTyOk`'s middle `∀`, in the twin's order. -/
def listConsR (P : ConLeche.Name) : Expr → Bool
  | .forallE D2 R2 => D2 == .bvar 0 && listConsR2 P R2
  | _ => false

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:343-360 listConsTyOk — in the
twin's order: each binder's domain against its interned comparand, one `∀`
at a time. -/
theorem listConsTyOk_forallE {c : ConstantInfo} {P : ConLeche.Name}
    {D R : Expr} (hl : c.toConstantVal.levelParams = [P])
    (ht : c.toConstantVal.type = .forallE D R) :
    ConLeche.listConsTyOk (some c) = (D == typeAt P && listConsR P R) := by
  simp only [ConLeche.listConsTyOk, hl, ht]
  cases D <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt]; done))
  cases R <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt, listConsR]; done))
  rename_i D2 R2
  cases D2 <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt, listConsR]; done))
  rename_i k
  cases k <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt, listConsR]; done))
  cases R2 <;> (try (rw [Bool.eq_iff_iff]; simp [typeAt, listConsR, listConsR2]; done))
  rename_i D3 C3
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
    (h : ∀ D B, R ≠ .forallE D B) : listConsR P R = false := by
  unfold listConsR; split
  · rename_i D B; exact absurd rfl (h D B)
  · rfl

/-- con-leche: none — `listConsR2` at a codomain that is not a `∀`. -/
theorem listConsR2_of_not {P : ConLeche.Name} {R : Expr}
    (h : ∀ D B, R ≠ .forallE D B) : listConsR2 P R = false := by
  unfold listConsR2; split
  · rename_i D B; exact absurd rfl (h D B)
  · rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:343-360 listConsTyOk — **THEOREM
1 for `listConsTyOk`**. -/
theorem listConsTyOk_spec (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK mode env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => s = s₀⦄ ConRon.Arena.listConsTyOk oc
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.listConsTyOk oc'; ⊤⦄ := by
  cases oc with
  | none =>
    simp only [OptCI] at hrel; subst hrel
    vcgen [ConRon.Arena.listConsTyOk]
    all_goals (bridge_peel; subst_vars; exact ⟨hok, Ext.refl _, rfl, rfl⟩)
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    have htc := toConstantVal_spec (mode := mode) (env := env) (fe := fe)
      s₀ ci c hok hci
    vcgen [ConRon.Arena.listConsTyOk, ConRon.Arena.pinList, htc]
    all_goals (bridge_peel; subst_vars)
    all_goals clear_tag_hyps
    case vc30 =>
      rename_i s1 s0 p0 hsingle ck_s0 d_r0_type_s0 x_s1_s0 p_s0_s1 hlps
      obtain ⟨P, _, hdp⟩ := denoteNList_single (hsingle ▸ hlps)
      exact lviewOK_param (denoteN_ext hdp x_s1_s0)
    case vc28 =>
      rename_i s2 s1 p0 hsingle s0 ck_s1 wf_s0 x_s1_s0 _ d_r1_type_s1 _ _ _ c_s0_s1 p_s0_s1
        vl_r0_s0 dl_r0_s0 x_s2_s1 p_s1_s2 hlps
      exact lviewOK_succ vl_r0_s0
    case vc26 =>
      rename_i s3 s2 p0 hsingle s1 s0 ck_s2 wf_s1 wf_s0 x_s2_s1 x_s1_s0 _ _ d_r2_type_s2 _ _
        _ _ _ _ c_s1_s2 c_s0_s1 p_s1_s2 p_s0_s1 vl_r1_s1 dl_r1_s1 vl_r0_s0 dl_r0_s0 x_s3_s2
        p_s2_s3 hlps
      exact viewOK_sort (by rw [vl_r0_s0]; rfl)
    case vc24 =>
      sorry
    case vc22 =>
      sorry
    case vc15 =>
      sorry
    case vc13 =>
      sorry
    case vc11 =>
      sorry
    case vc1 =>
      sorry
    case vc2 =>
      sorry
    case vc3 =>
      sorry
    case vc4 =>
      sorry
    -- round 4: the tag-first twin's `else` arm
    case vc5 =>
      sorry
    case vc6 =>
      sorry
    -- round 4: the tag-first twin's `else` arm
    case vc7 =>
      sorry
    case vc8 =>
      sorry
    -- round 4: the tag-first twin's `else` arm
    case vc9 =>
      sorry
    case vc31 =>
      rename_i s1 s0 ck_s0 d_r0_type_s0 x_s1_s0 p_s0_s1 hlps hnotsingle
      exact ⟨ck_s0, x_s1_s0, p_s0_s1,
        (listTyOks_not_single (denoteNList_not_single hlps hnotsingle)).2.2.symm⟩
    all_goals first
      | assumption
      | (apply CheckOK.wf'; assumption)
      | exact viewOK_bvar

/-! ## 5. The two function shapes: `Char.ofNat` and `String.ofList` -/

/-- con-leche: none — `constE_spec` in ANSWER shape: the name handle comes
off a pin, so its denotation goes in as an existential and out as a
universal (round 3's rule; two `constE`s at different names share one
`vcgen` call here). -/
theorem constE_spec' (s₀ : AState) (n : NIdx) (hok : CheckOK mode env fe s₀)
    (hn : ∃ nm, denoteN s₀.store.ns n = some nm) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.constE n
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ ∀ nm, denoteN s₀.store.ns n = some nm →
          denoteE s'.store r = some (.const nm []); ⊤⦄ := by
  obtain ⟨nm, hnm⟩ := hn
  have h := constE_spec (mode := mode) (env := env) (fe := fe) s₀ n nm hok hnm
  vcgen [h]
  rename_i hpost
  obtain ⟨hck, hx, hp, hd⟩ := hpost
  refine ⟨hck, hx, hp, fun nm' hn' => ?_⟩
  rw [hnm] at hn'; obtain rfl := Option.some.inj hn'; exact hd

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:362-371 charOfNatTyOk — in the
twin's order, at a level-monomorphic constant whose type is a `∀`. -/
theorem charOfNatTyOk_forallE {c : ConstantInfo} {D B : Expr} (hl : c.toConstantVal.levelParams.isEmpty = true)
    (ht : c.toConstantVal.type = .forallE D B) :
    ConLeche.charOfNatTyOk (some c) =
      (D == .const ConLeche.natName [] && B == .const ConLeche.charName []) := by
  simp only [ConLeche.charOfNatTyOk, hl, ht, Bool.true_and]
  cases D <;> (try (rw [Bool.eq_iff_iff]; simp; done))
  rename_i n1 us1
  cases us1 <;> (try (rw [Bool.eq_iff_iff]; simp; done))
  cases B <;> (try (rw [Bool.eq_iff_iff]; simp; done))
  rename_i n2 us2
  cases us2 <;> (rw [Bool.eq_iff_iff]; simp)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:362-383 — the two function
guards at a constant whose type is not a `∀`. -/
theorem fnTyOks_not_forallE {c : ConstantInfo}
    (ht : ∀ D B, c.toConstantVal.type ≠ .forallE D B) :
    ConLeche.charOfNatTyOk (some c) = false ∧
      ConLeche.stringOfListTyOk (some c) = false := by
  refine ⟨?_, ?_⟩
  · simp only [ConLeche.charOfNatTyOk]
    split
    · rename_i heq; exact absurd heq (ht _ _)
    · simp
  · simp only [ConLeche.stringOfListTyOk]
    split
    · rename_i heq; exact absurd heq (ht _ _)
    · simp

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:362-383 — the two function
guards at a level-polymorphic constant. -/
theorem fnTyOks_not_empty {c : ConstantInfo}
    (hl : c.toConstantVal.levelParams.isEmpty = false) :
    ConLeche.charOfNatTyOk (some c) = false ∧
      ConLeche.stringOfListTyOk (some c) = false := by
  simp [ConLeche.charOfNatTyOk, ConLeche.stringOfListTyOk, hl]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:362-371 charOfNatTyOk — **THEOREM
1 for `charOfNatTyOk`**. -/
theorem charOfNatTyOk_spec (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK mode env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => s = s₀⦄ ConRon.Arena.charOfNatTyOk oc
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.charOfNatTyOk oc'; ⊤⦄ := by
  cases oc with
  | none =>
    simp only [OptCI] at hrel; subst hrel
    vcgen [ConRon.Arena.charOfNatTyOk]
    all_goals (bridge_peel; subst_vars; exact ⟨hok, Ext.refl _, rfl, rfl⟩)
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    have htc := toConstantVal_spec (mode := mode) (env := env) (fe := fe)
      s₀ ci c hok hci
    have hce := fun (s : AState) (n : NIdx) =>
      constE_spec' (mode := mode) (env := env) (fe := fe) s n
    vcgen [ConRon.Arena.charOfNatTyOk, ConRon.Arena.pinNat,
      ConRon.Arena.pinChar, htc, hce]
    all_goals (bridge_peel; subst_vars)
    all_goals clear_tag_hyps
    case vc1 =>
      rename_i s1 s0 hne ck_s0 d_r0_type_s0 x_s1_s0 p_s0_s1 hlps
      refine ⟨ck_s0, x_s1_s0, p_s0_s1, ?_⟩
      rw [isEmpty_of_denoteNList hlps] at hne
      simp only [Bool.not_eq_true', Bool.eq_false_iff] at hne
      exact (fnTyOks_not_empty (by simpa using hne)).1.symm
    case vc10 =>
      rename_i s1 s0 hneg0 ck_s0 d_r0_type_s0 x_s1_s0 p_s0_s1 hlps
      exact ck_s0.pins
    case vc8 =>
      rename_i s1 hneg0 s0 hlps ck_s0 hpin d_r1_type_s0 x_s1_s0 p_s0_s1
      exact ck_s0
    case vc9 =>
      rename_i s1 hneg0 s0 hlps ck_s0 hpin d_r1_type_s0 x_s1_s0 p_s0_s1
      exact ⟨_, hpin _ rfl⟩
    case vc7 =>
      rename_i s2 hneg0 s1 s0 ck_s0 x_s1_s0 p_s0_s1 _ hlps ck_s1 hpin d_r2_type_s1 x_s2_s1
        p_s1_s2
      exact ck_s0.pins
    case vc5 =>
      rename_i s2 hneg0 s1 s0 hlps ck_s1 hpin d_r3_type_s1 x_s2_s1 p_s1_s2 ck_s0 hpin_2
        x_s1_s0 p_s0_s1 _
      exact ck_s0
    case vc6 =>
      rename_i s2 hneg0 s1 s0 hlps ck_s1 hpin d_r3_type_s1 x_s2_s1 p_s1_s2 ck_s0 hpin_2
        x_s1_s0 p_s0_s1 _
      exact ⟨_, hpin_2 _ rfl⟩
    case vc2 =>
      sorry
    case vc3 =>
      rename_i s3 hneg0 s2 s1 s0 x1 hnot0 hlps ck_s2 hpin d_r4_type_s2 x_s3_s2 p_s2_s3 ck_s1
        hpin_2 x_s2_s1 p_s1_s2 hc1 ck_s0 x_s1_s0 p_s0_s1 hc2 v_r4_type_s0
      have x20 := x_s2_s1.trans x_s1_s0
      refine ⟨ck_s0, x_s3_s2.trans x20, p_s0_s1.trans (p_s1_s2.trans p_s2_s3), ?_⟩
      exact (fnTyOks_not_forallE (denote_not_forallE ck_s0.state.wf v_r4_type_s0
        (denote_ext d_r4_type_s2 x20) hnot0)).1.symm

    -- round 4: the type does not carry the `forallE` TAG
    case vc4 =>
      sorry
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:373-383 stringOfListTyOk — in
the twin's order, at a level-monomorphic constant whose type is a `∀`. -/
theorem stringOfListTyOk_forallE {c : ConstantInfo} {D B : Expr} (hl : c.toConstantVal.levelParams.isEmpty = true)
    (ht : c.toConstantVal.type = .forallE D B) :
    ConLeche.stringOfListTyOk (some c) =
      (D == .app (.const ConLeche.listName [.zero]) (.const ConLeche.charName [])
        && B == .const ConLeche.stringName []) := by
  simp only [ConLeche.stringOfListTyOk, hl, ht, Bool.true_and]
  cases D <;> (try (rw [Bool.eq_iff_iff]; simp; done))
  rename_i F A
  cases F <;> (try (rw [Bool.eq_iff_iff]; simp; done))
  cases A <;> (try (rw [Bool.eq_iff_iff]; simp; done))
  rename_i n1 us1
  cases us1 <;> (try (rw [Bool.eq_iff_iff]; simp; done))
  cases B <;> (try (rw [Bool.eq_iff_iff]; simp; done))
  rename_i n2 us2
  cases us2 <;> (rw [Bool.eq_iff_iff]; simp [and_assoc])

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:373-383 stringOfListTyOk —
**THEOREM 1 for `stringOfListTyOk`**. -/
theorem stringOfListTyOk_spec (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK mode env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => s = s₀⦄ ConRon.Arena.stringOfListTyOk oc
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.stringOfListTyOk oc'; ⊤⦄ := by
  cases oc with
  | none =>
    simp only [OptCI] at hrel; subst hrel
    vcgen [ConRon.Arena.stringOfListTyOk]
    all_goals (bridge_peel; subst_vars; exact ⟨hok, Ext.refl _, rfl, rfl⟩)
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    have htc := toConstantVal_spec (mode := mode) (env := env) (fe := fe)
      s₀ ci c hok hci
    have hce := fun (s : AState) (n : NIdx) =>
      constE_spec' (mode := mode) (env := env) (fe := fe) s n
    vcgen [ConRon.Arena.stringOfListTyOk, ConRon.Arena.zeroLevel,
      ConRon.Arena.pinList, ConRon.Arena.pinChar, ConRon.Arena.pinString,
      htc, hce]
    all_goals (bridge_peel; subst_vars)
    all_goals clear_tag_hyps
    case vc1 =>
      rename_i s1 s0 hne ck_s0 d_r0_type_s0 x_s1_s0 p_s0_s1 hlps
      refine ⟨ck_s0, x_s1_s0, p_s0_s1, ?_⟩
      rw [isEmpty_of_denoteNList hlps] at hne
      simp only [Bool.not_eq_true', Bool.eq_false_iff] at hne
      exact (fnTyOks_not_empty (by simpa using hne)).2.symm
    case vc18 =>
      rename_i s1 s0 hneg0 ck_s0 d_r0_type_s0 x_s1_s0 p_s0_s1 hlps
      exact ck_s0.pins
    case vc17 =>
      rename_i dl_r0_s0 _ _ _
      intro c hc
      simp only [List.mem_singleton] at hc; subst hc
      exact lview_isSome_of_denote dl_r0_s0
    case vc15 =>
      rename_i s2 hneg0 s1 s0 wf_s0 x_s1_s0 _ _ _ _ c_s0_s1 p_s0_s1 vls_r0_s0 dls_r0_s0 hlps
        ck_s1 dl_r1_s1 d_r2_type_s1 x_s2_s1 p_s1_s2
      exact ck_s1.pins.mono x_s1_s0 p_s0_s1
    case vc14 =>
      rename_i s2 hneg0 s1 s0 hlps ck_s1 dl_r2_s1 d_r3_type_s1 x_s2_s1 p_s1_s2 wf_s0 hpin
        x_s1_s0 _ _ _ _ c_s0_s1 p_s0_s1 vls_r1_s0 dls_r1_s0
      exact viewOK_const (nview_isSome_of_denote (hpin _ rfl))
        (by rw [vls_r1_s0]; rfl)
    case vc12 =>
      sorry
    case vc10 =>
      sorry
    case vc11 =>
      sorry
    case vc9 =>
      sorry
    case vc7 =>
      sorry
    case vc5 =>
      sorry
    case vc6 =>
      sorry
    case vc2 =>
      sorry
    case vc3 =>
      sorry
    -- round 4: the type does not carry the `forallE` TAG
    case vc4 =>
      sorry
    all_goals first
      | assumption
      | (apply CheckOK.wf'; assumption)

/-! ## 6. `strLitSupported` -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:385-403 strLitSupported —
**THEOREM 1 for `strLitSupported`**: the `Nat` literal guard, then the seven
string-support declarations at exactly the expected types. -/
theorem strLitSupported_spec (s₀ : AState) (hok : CheckOK mode env fe s₀) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.strLitSupported fe
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.strLitSupported env; ⊤⦄ := by
  have hn := fun (s : AState) =>
    natLitSupported_spec (mode := mode) (env := env) (fe := fe) s
  have h1 := fun (s : AState) (oc : Option IConstantInfo) =>
    stringTyOk_spec (mode := mode) (env := env) (fe := fe) s oc
      (env.find? ConLeche.stringName)
  have h2 := fun (s : AState) (oc : Option IConstantInfo) =>
    stringOfListTyOk_spec (mode := mode) (env := env) (fe := fe) s oc
      (env.find? ConLeche.stringOfListName)
  have h3 := fun (s : AState) (oc : Option IConstantInfo) =>
    listTyOk_spec (mode := mode) (env := env) (fe := fe) s oc
      (env.find? ConLeche.listName)
  have h4 := fun (s : AState) (oc : Option IConstantInfo) =>
    listNilTyOk_spec (mode := mode) (env := env) (fe := fe) s oc
      (env.find? ConLeche.listNilName)
  have h5 := fun (s : AState) (oc : Option IConstantInfo) =>
    listConsTyOk_spec (mode := mode) (env := env) (fe := fe) s oc
      (env.find? ConLeche.listConsName)
  have h6 := fun (s : AState) (oc : Option IConstantInfo) =>
    charTyOk_spec (mode := mode) (env := env) (fe := fe) s oc
      (env.find? ConLeche.charName)
  have h7 := fun (s : AState) (oc : Option IConstantInfo) =>
    charOfNatTyOk_spec (mode := mode) (env := env) (fe := fe) s oc
      (env.find? ConLeche.charOfNatName)
  vcgen [ConRon.Arena.strLitSupported, ConRon.Arena.pinString,
    ConRon.Arena.pinStringOfList, ConRon.Arena.pinList,
    ConRon.Arena.pinListNil, ConRon.Arena.pinListCons, ConRon.Arena.pinChar,
    ConRon.Arena.pinCharOfNat, hn, h1, h2, h3, h4, h5, h6, h7]
  all_goals (bridge_peel; subst_vars)
  all_goals clear_tag_hyps
  case vc1 =>
    rename_i s1 s0 ck_s0 x_s1_s0 p_s0_s1 _
    refine ⟨ck_s0, x_s1_s0,
      p_s0_s1, ?_⟩
    simp_all [ConLeche.strLitSupported]
  case vc2 =>
    rename_i s2 s1 s0 ck_s0 x_s1_s0 p_s0_s1 hneg0 ck_s1 hpin x_s2_s1 p_s1_s2 _
    refine ⟨ck_s0, x_s2_s1.trans (x_s1_s0),
      p_s0_s1.trans (p_s1_s2), ?_⟩
    simp_all [ConLeche.strLitSupported]
  case vc3 =>
    rename_i s3 s2 s1 s0 ck_s0 x_s1_s0 p_s0_s1 hneg0 ck_s2 hpin x_s3_s2 p_s2_s3 hneg1 ck_s1
      hpin_2 x_s2_s1 p_s1_s2 _
    refine ⟨ck_s0, x_s3_s2.trans (x_s2_s1.trans (x_s1_s0)),
      p_s0_s1.trans (p_s1_s2.trans (p_s2_s3)), ?_⟩
    simp_all [ConLeche.strLitSupported]
  case vc4 =>
    rename_i s4 s3 s2 s1 s0 ck_s0 x_s1_s0 p_s0_s1 hneg0 ck_s3 hpin x_s4_s3 p_s3_s4 hneg1
      ck_s2 hpin_2 x_s3_s2 p_s2_s3 hneg2 ck_s1 hpin_3 x_s2_s1 p_s1_s2 _
    refine ⟨ck_s0, x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans (x_s1_s0))),
      p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4))), ?_⟩
    simp_all [ConLeche.strLitSupported]
  case vc5 =>
    rename_i s5 s4 s3 s2 s1 s0 ck_s0 x_s1_s0 p_s0_s1 hneg0 ck_s4 hpin x_s5_s4 p_s4_s5 hneg1
      ck_s3 hpin_2 x_s4_s3 p_s3_s4 hneg2 ck_s2 hpin_3 x_s3_s2 p_s2_s3 hneg3 ck_s1 hpin_4
      x_s2_s1 p_s1_s2 _
    refine ⟨ck_s0, x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans (x_s1_s0)))),
      p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4.trans (p_s4_s5)))), ?_⟩
    simp_all [ConLeche.strLitSupported]
  case vc6 =>
    rename_i s6 s5 s4 s3 s2 s1 s0 ck_s0 x_s1_s0 p_s0_s1 hneg0 ck_s5 hpin x_s6_s5 p_s5_s6
      hneg1 ck_s4 hpin_2 x_s5_s4 p_s4_s5 hneg2 ck_s3 hpin_3 x_s4_s3 p_s3_s4 hneg3 ck_s2
      hpin_4 x_s3_s2 p_s2_s3 hneg4 ck_s1 hpin_5 x_s2_s1 p_s1_s2 _
    refine ⟨ck_s0, x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans (x_s2_s1.trans
        (x_s1_s0))))),
      p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4.trans (p_s4_s5.trans (p_s5_s6))))), ?_⟩
    simp_all [ConLeche.strLitSupported]
  case vc7 =>
    rename_i s7 s6 s5 s4 s3 s2 s1 s0 ck_s0 x_s1_s0 p_s0_s1 hneg0 ck_s6 hpin x_s7_s6 p_s6_s7
      hneg1 ck_s5 hpin_2 x_s6_s5 p_s5_s6 hneg2 ck_s4 hpin_3 x_s5_s4 p_s4_s5 hneg3 ck_s3
      hpin_4 x_s4_s3 p_s3_s4 hneg4 ck_s2 hpin_5 x_s3_s2 p_s2_s3 hneg5 ck_s1 hpin_6 x_s2_s1
      p_s1_s2 _
    refine ⟨ck_s0, x_s7_s6.trans (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans (x_s3_s2.trans
        (x_s2_s1.trans (x_s1_s0)))))),
      p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4.trans (p_s4_s5.trans (p_s5_s6.trans
        (p_s6_s7)))))), ?_⟩
    simp_all [ConLeche.strLitSupported]
  case vc8 =>
    rename_i s8 s7 s6 s5 s4 s3 s2 s1 s0 ck_s0 x_s1_s0 p_s0_s1 hneg0 ck_s7 hpin x_s8_s7
      p_s7_s8 hneg1 ck_s6 hpin_2 x_s7_s6 p_s6_s7 hneg2 ck_s5 hpin_3 x_s6_s5 p_s5_s6 hneg3
      ck_s4 hpin_4 x_s5_s4 p_s4_s5 hneg4 ck_s3 hpin_5 x_s4_s3 p_s3_s4 hneg5 ck_s2 hpin_6
      x_s3_s2 p_s2_s3 hneg6 ck_s1 hpin_7 x_s2_s1 p_s1_s2
    refine ⟨ck_s0, x_s8_s7.trans (x_s7_s6.trans (x_s6_s5.trans (x_s5_s4.trans (x_s4_s3.trans
        (x_s3_s2.trans (x_s2_s1.trans (x_s1_s0))))))),
      p_s0_s1.trans (p_s1_s2.trans (p_s2_s3.trans (p_s3_s4.trans (p_s4_s5.trans (p_s5_s6.trans
        (p_s6_s7.trans (p_s7_s8))))))), ?_⟩
    simp_all [ConLeche.strLitSupported]
  all_goals first
    | assumption
    | (apply CheckOK.pins; assumption)
    | (apply optCI_find (by assumption); apply_assumption; rfl)

/-! ## 7. The axiom census -/

section Census

#print axioms denoteCI_nonTower
#print axioms toConstantVal_spec
#print axioms stringTyOk_spec
#print axioms charTyOk_spec
#print axioms listTyOk_spec
#print axioms listNilTyOk_spec
#print axioms listConsTyOk_spec
#print axioms charOfNatTyOk_spec
#print axioms stringOfListTyOk_spec
#print axioms strLitSupported_spec

end Census

end ConRon.Bridge.Core

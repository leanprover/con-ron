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

/-! ## The string walks' vocabulary

The interning of a level at the tier's invariant (its readbacks and `ViewOK`
preconditions are `Bridge/Grind.lean` §7's), the record fields the shape
guards read, and `OptCI` as `grind` reads it. -/

/-! `Bridge/Grind.lean` §6's handle inverses and the tags' values, registered
locally (they fire on every denotation; these walks compare handles against
pins and interned lists, and tags as literals). -/
local grind_pattern [bridge_grind] nameIdx => denoteN st.ns n
local grind_pattern [bridge_grind] NameIdx.some => NameIdx st n (some nm)
local grind_pattern [bridge_grind] lsIdxAt => denoteLs st.lss n
local grind_pattern [bridge_grind] LsIdxAt.some => LsIdxAt st n (some ls)
local grind_pattern [bridge_grind] eIdxAt => denoteE st n
local grind_pattern [bridge_grind] EIdxAt.some => EIdxAt st n (some e)
attribute [local bridge_grind =] ETag.bvar ETag.fvar ETag.sort ETag.const ETag.app ETag.lam
  ETag.forallE ETag.letE ETag.lit ETag.proj exprTag

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

/-- con-leche: none — `toConstantVal`'s two fields the shape guards read, at
an optional stored constant's denotation. -/
def CVFields (st₀ st : EStore) (cv : IConstantVal) : Option ConstantInfo → Prop
  | some c => Frontend.denoteNList st₀.ns cv.levelParams = some c.toConstantVal.levelParams ∧
      denoteE st cv.type = some c.toConstantVal.type
  | none => True

/-- con-leche: none — `CVFields` at a denoting constant. -/
theorem CVFields.some {st₀ st : EStore} {cv : IConstantVal} {c : ConstantInfo}
    (H : CVFields st₀ st cv (some c)) :
    Frontend.denoteNList st₀.ns cv.levelParams = some c.toConstantVal.levelParams ∧
      denoteE st cv.type = some c.toConstantVal.type := H
grind_pattern [bridge_grind] CVFields.some => CVFields st₀ st cv (some c)

attribute [bridge_grind =] OptCI

grind_pattern [bridge_grind] optCI_find => OptCI s.store (fe.find? n) (env.find? nm),
  CheckOK mode env fe s


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
    sym only [bridge_grind] => vcgen <;> finish
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
      sym only [bridge_grind, ConstantInfo.toConstantVal] =>
        vcgen [IConstantInfo.toConstantVal,
          internLNode_okS (mode := mode) (env := env) (fe := fe),
          internE_specC (mode := mode) (env := env) (fe := fe)] <;> finish
    | _ => simp [IConstantInfo.isTowerEntry] at hti

/-- con-leche: ConLeche/Kernel/Env.lean:639-642 ConstantInfo.toConstantVal —
`toConstantVal_spec` in answer shape: the two fields at whatever the stored
constant denotes (`CVFields`). -/
theorem toConstantVal_specA (s₀ : AState) (ci : IConstantInfo)
    (hok : CheckOK mode env fe s₀)
    (hci : (Frontend.denoteCI s₀.store ci).isSome = true) :
    ⦃fun s => s = s₀⦄ ci.toConstantVal
    ⦃fun cv s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        CVFields s₀.store s'.store cv (Frontend.denoteCI s₀.store ci); ⊤⦄ := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hci
  refine triple_mono (toConstantVal_spec s₀ ci c hok hc) ?_
  rintro cv s' ⟨h1, h2, h3, h4, h5⟩
  rw [hc]
  exact ⟨h1, h2, h3, h4, h5⟩

/-! ## 3. The two `Type`-valued shapes: `String` and `Char` -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:301-307 stringTyOk — **THEOREM 1
for `stringTyOk`**. -/
theorem stringTyOk_spec (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK mode env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => s = s₀⦄ ConRon.Arena.stringTyOk oc
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.stringTyOk oc'; ⊤⦄ := by
  sym only [bridge_grind, ConLeche.stringTyOk] =>
    vcgen [ConRon.Arena.stringTyOk, ConRon.Arena.sortOne,
      toConstantVal_specA (mode := mode) (env := env) (fe := fe)] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:309-315 charTyOk — **THEOREM 1
for `charTyOk`**. -/
theorem charTyOk_spec (s₀ : AState) (oc : Option IConstantInfo)
    (oc' : Option ConstantInfo) (hok : CheckOK mode env fe s₀)
    (hrel : OptCI s₀.store oc oc') :
    ⦃fun s => s = s₀⦄ ConRon.Arena.charTyOk oc
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.charTyOk oc'; ⊤⦄ := by
  sym only [bridge_grind, ConLeche.charTyOk] =>
    vcgen [ConRon.Arena.charTyOk, ConRon.Arena.sortOne,
      toConstantVal_specA (mode := mode) (env := env) (fe := fe)] <;> finish

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
    sym only [bridge_grind, ConLeche.listTyOk] =>
      vcgen [ConRon.Arena.listTyOk] <;> finish
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    simp only [ConRon.Arena.listTyOk]
    refine triple_seq (toConstantVal_spec s₀ ci c hok hci) ?_
    rintro cv s1 ⟨hok1, hx1, hp1, hlp, hty⟩
    split
    -- the match on the level-parameter list, by its arms' names
    case h_2 hnotsingle =>
      exact triple_pureS ⟨hok1, hx1, hp1,
        (listTyOks_not_single (denoteNList_not_single hlp hnotsingle)).1.symm⟩
    case' h_1 p hsingle => skip
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
    sym only [bridge_grind, ConLeche.listNilTyOk] =>
      vcgen [ConRon.Arena.listNilTyOk] <;> finish
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    simp only [ConRon.Arena.listNilTyOk]
    refine triple_seq (toConstantVal_spec s₀ ci c hok hci) ?_
    rintro cv s1 ⟨hok1, hx1, hp1, hlp, hty⟩
    split
    -- the match on the level-parameter list, by its arms' names
    case h_2 hnotsingle =>
      exact triple_pureS ⟨hok1, hx1, hp1,
        (listTyOks_not_single (denoteNList_not_single hlp hnotsingle)).2.1.symm⟩
    case' h_1 p hsingle => skip
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
    sym only [bridge_grind, ConLeche.listConsTyOk] =>
      vcgen [ConRon.Arena.listConsTyOk] <;> finish
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    simp only [ConRon.Arena.listConsTyOk]
    refine triple_seq (toConstantVal_spec s₀ ci c hok hci) ?_
    rintro cv s1 ⟨hok1, hx1, hp1, hlp, hty⟩
    split
    -- the match on the level-parameter list, by its arms' names
    case h_2 hnotsingle =>
      exact triple_pureS ⟨hok1, hx1, hp1,
        (listTyOks_not_single (denoteNList_not_single hlp hnotsingle)).2.2.symm⟩
    case' h_1 p hsingle => skip
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
    refine triple_seq (internLsNode_okS s4 [pl] hok4 (by
      intro c hc
      simp only [List.mem_singleton] at hc; subst hc
      exact lview_isSome_of_denote (denoteL_ext hpl (hx3.trans hx4)))) ?_
    rintro ps s5 ⟨hok5, hx5, hp5, hvps, hd5⟩
    have hps : denoteLs s5.store.lss ps = some [.param P] :=
      denoteLs_view_single hd5 (denoteL_ext hpl ((hx3.trans hx4).trans hx5))
    simp only [ConRon.Arena.pinList]
    refine triple_seq (pinAt_okS s5 _ hok5) ?_
    rintro li s6 ⟨hs6, hli⟩
    subst s6
    have hli' : denoteN s5.store.ns li = some ConLeche.listName := hli _ rfl
    refine triple_seq (internE_okS s5 (.bvar 0) hok5 viewOK_bvar) ?_
    rintro b0 s6 ⟨hok6, hx6, hp6, _, hd6⟩
    refine triple_seq (internE_okS s6 (.bvar 1) hok6 viewOK_bvar) ?_
    rintro b1 s7 ⟨hok7, hx7, hp7, _, hd7⟩
    refine triple_seq (internE_okS s7 (.bvar 2) hok7 viewOK_bvar) ?_
    rintro b2 s8 ⟨hok8, hx8, hp8, _, hd8⟩
    have hx58 := hx6.trans (hx7.trans hx8)
    refine triple_seq (internE_okS s8 (.const li ps) hok8
      (viewOK_const (nview_isSome_of_denote (denoteN_ext hli' hx58))
        (lsview_isSome_of_denote (denoteLs_ext hps hx58)))) ?_
    rintro l1 s9 ⟨hok9, hx9, hp9, _, hd9⟩
    have hl1 : denoteE s9.store l1 = some (.const ConLeche.listName [.param P]) :=
      denote_view_const hd9 (denoteN_ext hli' (hx58.trans hx9))
        (denoteLs_ext hps (hx58.trans hx9))
    have hb1 : denoteE s9.store b1 = some (.bvar 1) :=
      denote_ext (denote_view_bvar hd7) (hx8.trans hx9)
    have hb2 : denoteE s9.store b2 = some (.bvar 2) :=
      denote_ext (denote_view_bvar hd8) hx9
    refine triple_seq (internE_okS s9 (.app l1 b1) hok9
      (viewOK_app (by rw [hl1]; rfl) (by rw [hb1]; rfl))) ?_
    rintro dom3 s10 ⟨hok10, hx10, hp10, _, hd10⟩
    have hdom3 : denoteE s10.store dom3 = some (listApp P 1) :=
      denote_view_app hd10 (denote_ext hl1 hx10) (denote_ext hb1 hx10)
    refine triple_seq (internE_okS s10 (.app l1 b2) hok10
      (viewOK_app (by rw [denote_ext hl1 hx10]; rfl)
        (by rw [denote_ext hb2 hx10]; rfl))) ?_
    rintro cod3 s11 ⟨hok11, hx11, hp11, _, hd11⟩
    have hcod3 : denoteE s11.store cod3 = some (listApp P 2) :=
      denote_view_app hd11 (denote_ext hl1 (hx10.trans hx11))
        (denote_ext hb2 (hx10.trans hx11))
    have hx511 : Ext s5.store s11.store :=
      hx58.trans (hx9.trans (hx10.trans hx11))
    have hx111 : Ext s1.store s11.store :=
      hx2.trans (hx3.trans (hx4.trans (hx5.trans hx511)))
    have hx011 : Ext s₀.store s11.store := hx1.trans hx111
    have hp011 : s11.pins = s₀.pins := by
      rw [hp11, hp10, hp9, hp8, hp7, hp6, hp5, hp4, hp3, hp2, hp1]
    have hwf := hok11.state.wf
    have hso' := denote_ext hso (hx5.trans hx511)
    have hb0 : denoteE s11.store b0 = some (.bvar 0) :=
      denote_ext (denote_view_bvar hd6) (hx7.trans (hx8.trans (hx9.trans
        (hx10.trans hx11))))
    have hdom3' := denote_ext hdom3 hx11
    have hty' := denote_ext hty hx111
    have hret : ∀ (b : Bool), b = ConLeche.listConsTyOk (some c) →
        ⦃fun s => s = s11⦄ (pure b : AM Bool)
        ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
          s'.pins = s₀.pins ∧ r = ConLeche.listConsTyOk (some c); ⊤⦄ :=
      fun b hb => triple_pureS ⟨hok11, hx011, hp011, hb⟩
    obtain ⟨v, hv⟩ := denoteE_view hty'
    refine tag_view_bind_triple hv ?_
      (fun hne => by cases v <;> first | rfl | exact absurd rfl hne)
    cases v
    case forallE d1 r1 =>
      obtain ⟨D, R, hT, hD, hR⟩ := denote_forallE_inv hwf hv hty'
      have hpure := listConsTyOk_forallE hP hT
      dsimp only
      rw [bne, beq_of_denoteE hwf hD hso']
      by_cases hDe : (D == typeAt P) = true
      · rw [hDe]
        simp only [Bool.not_true, Bool.false_eq_true, ite_false]
        rw [hDe, Bool.true_and] at hpure
        obtain ⟨vr, hvr⟩ := denoteE_view hR
        refine tag_view_bind_triple hvr ?_
          (fun hne => by cases vr <;> first | rfl | exact absurd rfl hne)
        cases vr
        case forallE d2 r2 =>
          obtain ⟨D2, R2, rfl, hD2, hR2⟩ := denote_forallE_inv hwf hvr hR
          dsimp only
          rw [bne, beq_of_denoteE hwf hD2 hb0]
          by_cases hD2e : (D2 == .bvar 0) = true
          · rw [hD2e]
            simp only [Bool.not_true, Bool.false_eq_true, ite_false]
            have hpure2 : ConLeche.listConsTyOk (some c) = listConsR2 P R2 := by
              rw [hpure]; simp [listConsR, hD2e]
            obtain ⟨vr2, hvr2⟩ := denoteE_view hR2
            refine tag_view_bind_triple hvr2 ?_
              (fun hne => by cases vr2 <;> first | rfl | exact absurd rfl hne)
            cases vr2
            case forallE d3 c3 =>
              obtain ⟨D3, C3, rfl, hD3, hC3⟩ := denote_forallE_inv hwf hvr2 hR2
              dsimp only
              refine hret _ ?_
              rw [hpure2, beq_of_denoteE hwf hD3 hdom3',
                beq_of_denoteE hwf hC3 hcod3]
              rfl
            all_goals
              dsimp only
              exact hret _ (by
                rw [hpure2, listConsR2_of_not (denote_not_forallE hwf hvr2 hR2
                  (fun _ _ h => nomatch h))])
          · have hf : (D2 == .bvar 0) = false := by simpa using hD2e
            rw [hf]
            simp only [Bool.not_false, ite_true]
            exact hret _ (by rw [hpure]; simp [listConsR, hf])
        all_goals
          dsimp only
          exact hret _ (by
            rw [hpure, listConsR_of_not (denote_not_forallE hwf hvr hR
              (fun _ _ h => nomatch h))])
      · have hf : (D == typeAt P) = false := by simpa using hDe
        rw [hf]
        simp only [Bool.not_false, ite_true]
        exact hret _ (by rw [hpure, hf]; rfl)
    all_goals
      dsimp only
      exact hret _ (listNilConsTyOk_not_forallE hP
        (denote_not_forallE hwf hv hty' (fun _ _ h => nomatch h))).2.symm
/-! ## 5. The two function shapes: `Char.ofNat` and `String.ofList` -/

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
    sym only [bridge_grind, ConLeche.charOfNatTyOk] =>
      vcgen [ConRon.Arena.charOfNatTyOk] <;> finish
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    simp only [ConRon.Arena.charOfNatTyOk]
    refine triple_seq (toConstantVal_spec s₀ ci c hok hci) ?_
    rintro cv s1 ⟨hok1, hx1, hp1, hlp, hty⟩
    have hemp := isEmpty_of_denoteNList hlp
    by_cases hne : (!cv.levelParams.isEmpty) = true
    · rw [ite_eq_left hne]
      rw [hemp] at hne
      exact triple_pureS ⟨hok1, hx1, hp1,
        (fnTyOks_not_empty (by simpa using hne)).1.symm⟩
    rw [ite_eq_right hne]
    have hl : c.toConstantVal.levelParams.isEmpty = true := by
      rw [← hemp]; simpa using hne
    simp only [ConRon.Arena.pinNat, ConRon.Arena.pinChar]
    refine triple_seq (pinAt_okS s1 _ hok1) ?_
    rintro nt s2 ⟨hs2, hnt⟩
    subst s2
    refine triple_seq (constE_spec s1 nt _ hok1 (hnt _ rfl)) ?_
    rintro nc s2 ⟨hok2, hx2, hp2, hnc⟩
    refine triple_seq (pinAt_okS s2 _ hok2) ?_
    rintro ch s3 ⟨hs3, hch⟩
    subst s3
    refine triple_seq (constE_spec s2 ch _ hok2 (hch _ rfl)) ?_
    rintro cc s3 ⟨hok3, hx3, hp3, hcc⟩
    have hwf := hok3.state.wf
    have hx13 := hx2.trans hx3
    have hx03 : Ext s₀.store s3.store := hx1.trans hx13
    have hp03 : s3.pins = s₀.pins := by rw [hp3, hp2, hp1]
    have hnc' := denote_ext hnc hx3
    have hcc' := hcc
    have hty' := denote_ext hty hx13
    obtain ⟨v, hv⟩ := denoteE_view hty'
    refine tag_view_bind_triple hv ?_
      (fun hne => by cases v <;> first | rfl | exact absurd rfl hne)
    cases v
    case forallE d b =>
      obtain ⟨D, B, hT, hD, hB⟩ := denote_forallE_inv hwf hv hty'
      dsimp only
      refine triple_pureS ⟨hok3, hx03, hp03, ?_⟩
      rw [beq_of_denoteE hwf hD hnc', beq_of_denoteE hwf hB hcc',
        charOfNatTyOk_forallE hl hT]
    all_goals
      dsimp only
      exact triple_pureS ⟨hok3, hx03, hp03, (fnTyOks_not_forallE
        (denote_not_forallE hwf hv hty' (fun _ _ h => nomatch h))).1.symm⟩
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
    sym only [bridge_grind, ConLeche.stringOfListTyOk] =>
      vcgen [ConRon.Arena.stringOfListTyOk] <;> finish
  | some ci =>
    obtain ⟨c, hci, rfl⟩ := hrel
    simp only [ConRon.Arena.stringOfListTyOk]
    refine triple_seq (toConstantVal_spec s₀ ci c hok hci) ?_
    rintro cv s1 ⟨hok1, hx1, hp1, hlp, hty⟩
    have hemp := isEmpty_of_denoteNList hlp
    by_cases hne : (!cv.levelParams.isEmpty) = true
    · rw [ite_eq_left hne]
      rw [hemp] at hne
      exact triple_pureS ⟨hok1, hx1, hp1,
        (fnTyOks_not_empty (by simpa using hne)).2.symm⟩
    rw [ite_eq_right hne]
    have hl : c.toConstantVal.levelParams.isEmpty = true := by
      rw [← hemp]; simpa using hne
    unfold ConRon.Arena.zeroLevel
    simp only [ConRon.Arena.pinList, ConRon.Arena.pinChar, ConRon.Arena.pinString]
    refine triple_seq (pinZeroLevel_spec s1 hok1.pins) ?_
    rintro z s2 ⟨hs2, hz⟩
    subst s2
    refine triple_seq (internLsNode_okS s1 [z] hok1 (by
      intro c hc
      simp only [List.mem_singleton] at hc; subst hc
      exact lview_isSome_of_denote hz)) ?_
    rintro zs s2 ⟨hok2, hx2, hp2, hvzs, hdzs⟩
    have hzs : denoteLs s2.store.lss zs = some [.zero] :=
      denoteLs_view_single hdzs (denoteL_ext hz hx2)
    refine triple_seq (pinAt_okS s2 _ hok2) ?_
    rintro li s3 ⟨hs3, hli⟩
    subst s3
    have hli' : denoteN s2.store.ns li = some ConLeche.listName := hli _ rfl
    refine triple_seq (internE_okS s2 (.const li zs) hok2
      (viewOK_const (nview_isSome_of_denote hli') (by rw [hvzs]; rfl))) ?_
    rintro lc s3 ⟨hok3, hx3, hp3, _, hd3⟩
    have hlc : denoteE s3.store lc = some (.const ConLeche.listName [.zero]) :=
      denote_view_const hd3 (denoteN_ext hli' hx3) (denoteLs_ext hzs hx3)
    refine triple_seq (pinAt_okS s3 _ hok3) ?_
    rintro ch s4 ⟨hs4, hch⟩
    subst s4
    refine triple_seq (constE_spec s3 ch _ hok3 (hch _ rfl)) ?_
    rintro cc s4 ⟨hok4, hx4, hp4, hcc⟩
    have hcc' := hcc
    refine triple_seq (internE_okS s4 (.app lc cc) hok4
      (viewOK_app (by rw [denote_ext hlc hx4]; rfl) (by rw [hcc']; rfl))) ?_
    rintro dom s5 ⟨hok5, hx5, hp5, _, hd5⟩
    have hdom : denoteE s5.store dom = some (.app (.const ConLeche.listName [.zero])
        (.const ConLeche.charName [])) :=
      denote_view_app hd5 (denote_ext hlc (hx4.trans hx5)) (denote_ext hcc' hx5)
    refine triple_seq (pinAt_okS s5 _ hok5) ?_
    rintro st s6 ⟨hs6, hst⟩
    subst s6
    refine triple_seq (constE_spec s5 st _ hok5 (hst _ rfl)) ?_
    rintro sc s6 ⟨hok6, hx6, hp6, hsc⟩
    have hsc' := hsc
    have hwf := hok6.state.wf
    have hx16 : Ext s1.store s6.store :=
      hx2.trans (hx3.trans (hx4.trans (hx5.trans hx6)))
    have hx06 : Ext s₀.store s6.store := hx1.trans hx16
    have hp06 : s6.pins = s₀.pins := by rw [hp6, hp5, hp4, hp3, hp2, hp1]
    have hdom' := denote_ext hdom hx6
    have hty' := denote_ext hty hx16
    obtain ⟨v, hv⟩ := denoteE_view hty'
    refine tag_view_bind_triple hv ?_
      (fun hne => by cases v <;> first | rfl | exact absurd rfl hne)
    cases v
    case forallE d b =>
      obtain ⟨D, B, hT, hD, hB⟩ := denote_forallE_inv hwf hv hty'
      dsimp only
      refine triple_pureS ⟨hok6, hx06, hp06, ?_⟩
      rw [beq_of_denoteE hwf hD hdom', beq_of_denoteE hwf hB hsc',
        stringOfListTyOk_forallE hl hT]
    all_goals
      dsimp only
      exact triple_pureS ⟨hok6, hx06, hp06, (fnTyOks_not_forallE
        (denote_not_forallE hwf hv hty' (fun _ _ h => nomatch h))).2.symm⟩
/-! ## 6. `strLitSupported` -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:385-403 strLitSupported —
**THEOREM 1 for `strLitSupported`**: the `Nat` literal guard, then the seven
string-support declarations at exactly the expected types. -/
theorem strLitSupported_spec (s₀ : AState) (hok : CheckOK mode env fe s₀) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.strLitSupported fe
    ⦃fun b s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.strLitSupported env; ⊤⦄ := by
  sym only [bridge_grind, ConLeche.strLitSupported] =>
    vcgen [ConRon.Arena.strLitSupported, ConRon.Arena.pinString,
      ConRon.Arena.pinStringOfList, ConRon.Arena.pinList,
      ConRon.Arena.pinListNil, ConRon.Arena.pinListCons, ConRon.Arena.pinChar,
      ConRon.Arena.pinCharOfNat, natLitSupported_spec (mode := mode) (env := env) (fe := fe),
      stringTyOk_spec (mode := mode) (env := env) (fe := fe) (oc' := env.find? ConLeche.stringName),
      stringOfListTyOk_spec (mode := mode) (env := env) (fe := fe) (oc' := env.find? ConLeche.stringOfListName),
      listTyOk_spec (mode := mode) (env := env) (fe := fe) (oc' := env.find? ConLeche.listName),
      listNilTyOk_spec (mode := mode) (env := env) (fe := fe) (oc' := env.find? ConLeche.listNilName),
      listConsTyOk_spec (mode := mode) (env := env) (fe := fe) (oc' := env.find? ConLeche.listConsName),
      charTyOk_spec (mode := mode) (env := env) (fe := fe) (oc' := env.find? ConLeche.charName),
      charOfNatTyOk_spec (mode := mode) (env := env) (fe := fe) (oc' := env.find? ConLeche.charOfNatName),
      pinAt_specE] <;> finish

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

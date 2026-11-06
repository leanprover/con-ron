/-
# `ConRon.Bridge.Frontend.Olean.MergeAll` — every constant of the closure, merged

`isPropCheap` and `subsumes` against upstream's, `mergeEntry`, and the two nested loops of
`mergeAll`.  The note on spent fuel is `Merge.lean`'s.
-/
module

public import ConRon.Bridge.Frontend.Olean.Merge
import ConRon.Bridge.Specs

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Arena.Frontend.Olean (OleanPins Merged Loaded CEntry subsumes isPropCheap isPropBody
  isPropHead isPropDrop mergeEntry mergeAll)
open ConLeche.Frontend.Olean (CEntryF CKindF bind_some_left closureFuel)

/-! ## The walks leave the state alone -/

theorem isPropHead_state : ∀ (fuel : Nat) {e : EIdx} {k : Nat} {o : Option (NIdx × Nat)}
    {s s' : AState}, isPropHead fuel e k s = .ok (o, s') → s' = s
  | 0, e, k, o, s, s', h => by
    rw [isPropHead] at h
    exact (AM.pure_ok h).2
  | fuel + 1, e, k, o, s, s', h => by
    rw [isPropHead] at h
    obtain ⟨v, s₁, h1, h⟩ := AM.bind_ok h
    obtain ⟨hs1, -⟩ := view_run h1
    rw [hs1] at h
    cases v with
    | app f a => exact isPropHead_state fuel h
    | const _ _ => exact (AM.pure_ok h).2
    | bvar _ => exact (AM.pure_ok h).2
    | fvar _ _ => exact (AM.pure_ok h).2
    | sort _ => exact (AM.pure_ok h).2
    | lam _ _ => exact (AM.pure_ok h).2
    | forallE _ _ => exact (AM.pure_ok h).2
    | letE _ _ _ => exact (AM.pure_ok h).2
    | lit _ => exact (AM.pure_ok h).2
    | proj _ _ _ => exact (AM.pure_ok h).2

theorem isPropDrop_state : ∀ (k : Nat) {e : EIdx} {o : Option EIdx} {s s' : AState},
    isPropDrop k e s = .ok (o, s') → s' = s
  | 0, e, o, s, s', h => by
    rw [isPropDrop] at h
    exact (AM.pure_ok h).2
  | k + 1, e, o, s, s', h => by
    rw [isPropDrop] at h
    obtain ⟨v, s₁, h1, h⟩ := AM.bind_ok h
    obtain ⟨hs1, -⟩ := view_run h1
    rw [hs1] at h
    cases v with
    | forallE _ _ => exact isPropDrop_state k h
    | app _ _ => exact (AM.pure_ok h).2
    | const _ _ => exact (AM.pure_ok h).2
    | bvar _ => exact (AM.pure_ok h).2
    | fvar _ _ => exact (AM.pure_ok h).2
    | sort _ => exact (AM.pure_ok h).2
    | lam _ _ => exact (AM.pure_ok h).2
    | letE _ _ _ => exact (AM.pure_ok h).2
    | lit _ => exact (AM.pure_ok h).2
    | proj _ _ _ => exact (AM.pure_ok h).2

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap — **the twin's test leaves
the state alone, and its `true` is upstream's.** -/
theorem isPropCheap_run {pk : OleanPins} {s : AState} (hok : StateOK s) (hnu : NullsRel s.store pk)
    {mg : Merged} {mgC : ConLeche.Frontend.Olean.Merged} (hm : MergedRel s.store mg mgC)
    {ty : EIdx} {tyC : Expr} (hty : denoteE s.store ty = some tyC) {b : Bool} {s' : AState}
    (h : isPropCheap pk mg ty s = .ok (b, s')) :
    s' = s ∧ (b = true → ConLeche.Frontend.Olean.isPropCheap mgC.map tyC = true) := by
  unfold isPropCheap at h
  obtain ⟨x, s₁, h1, h⟩ := AM.bind_ok h
  obtain ⟨hs1, xC, hx, hbd⟩ := isPropBody_run hok _ hty h1
  rw [hs1] at h
  obtain ⟨o, s₂, h2, h⟩ := AM.bind_ok h
  have hs2 := isPropHead_state _ h2
  rw [hs2] at h
  rcases o with _ | ⟨n, k⟩
  · obtain ⟨hv, hs⟩ := AM.pure_ok h
    exact ⟨hs, fun hb => by rw [hv] at hb; cases hb⟩
  · obtain ⟨-, hbody, nC, hn, hhead⟩ := isPropHead_run hok _ hx h2
    simp only [] at h
    cases hg : mg.get n with
    | none =>
      simp only [hg] at h
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      exact ⟨hs, fun hb => by rw [hv] at hb; cases hb⟩
    | some d =>
      simp only [hg] at h
      obtain ⟨dC, hdC, hdd⟩ := hm.got hn hg
      obtain ⟨-, -, htd, -⟩ := denoteCEntry_parts hdd
      obtain ⟨o', s₃, h3, h⟩ := AM.bind_ok h
      have hs3 := isPropDrop_state _ h3
      rw [hs3] at h
      cases o' with
      | none =>
        obtain ⟨hv, hs⟩ := AM.pure_ok h
        exact ⟨hs, fun hb => by rw [hv] at hb; cases hb⟩
      | some y =>
        obtain ⟨-, yC, hy, hdrop⟩ := isPropDrop_run hok _ htd h3
        obtain ⟨v, s₄, h4, h⟩ := AM.bind_ok h
        obtain ⟨hs4, hv⟩ := view_run h4
        rw [hs4] at h
        have hden := denoteE_view_eq hok.wf hv
        rw [hden] at hy
        have hfin : s' = s ∧ (b = true → ∃ u, v = .sort u ∧ u = pk.zero) := by
          cases v with
          | sort u =>
            obtain ⟨hv', hs⟩ := AM.pure_ok h
            refine ⟨hs, fun hb => ⟨u, rfl, ?_⟩⟩
            rw [hv'] at hb
            simpa using hb
          | bvar _ => obtain ⟨hv', hs⟩ := AM.pure_ok h; exact ⟨hs, fun hb => by rw [hv'] at hb; cases hb⟩
          | fvar _ _ => obtain ⟨hv', hs⟩ := AM.pure_ok h; exact ⟨hs, fun hb => by rw [hv'] at hb; cases hb⟩
          | const _ _ => obtain ⟨hv', hs⟩ := AM.pure_ok h; exact ⟨hs, fun hb => by rw [hv'] at hb; cases hb⟩
          | app _ _ => obtain ⟨hv', hs⟩ := AM.pure_ok h; exact ⟨hs, fun hb => by rw [hv'] at hb; cases hb⟩
          | lam _ _ => obtain ⟨hv', hs⟩ := AM.pure_ok h; exact ⟨hs, fun hb => by rw [hv'] at hb; cases hb⟩
          | forallE _ _ => obtain ⟨hv', hs⟩ := AM.pure_ok h; exact ⟨hs, fun hb => by rw [hv'] at hb; cases hb⟩
          | letE _ _ _ => obtain ⟨hv', hs⟩ := AM.pure_ok h; exact ⟨hs, fun hb => by rw [hv'] at hb; cases hb⟩
          | lit _ => obtain ⟨hv', hs⟩ := AM.pure_ok h; exact ⟨hs, fun hb => by rw [hv'] at hb; cases hb⟩
          | proj _ _ _ => obtain ⟨hv', hs⟩ := AM.pure_ok h; exact ⟨hs, fun hb => by rw [hv'] at hb; cases hb⟩
        refine ⟨hfin.1, fun hb => ?_⟩
        obtain ⟨u, rfl, rfl⟩ := hfin.2 hb
        have hyC : yC = .sort .zero := by
          have hz := hnu.zero
          simp only [denoteEView, hz, Option.map_some, Option.some.injEq] at hy
          exact hy.symm
        subst hyC
        unfold ConLeche.Frontend.Olean.isPropCheap
        rw [hbd, hbody, hhead]
        simp only [hdC, hdrop]

/-! ## `subsumes` -/

theorem nameList_beq {st : EStore} (hw : NStoreWF st.ns) {l l' : List NIdx}
    {zs zs' : List ConLeche.Name} (h : l.mapM (denoteN st.ns) = some zs)
    (h' : l'.mapM (denoteN st.ns) = some zs') : (l == l') = (zs == zs') := by
  cases hb : (l == l') with
  | true =>
    have := beq_iff_eq.mp hb
    rw [this] at h
    have hz : zs = zs' := Option.some.inj (h.symm.trans h')
    simp [hz]
  | false =>
    symm
    rw [beq_eq_false_iff_ne]
    intro hz
    have := nameList_inj hw h (hz ▸ h')
    simp [this] at hb

theorem tag_thm {N E : Type} {k : CKindF N E} (h : k.tag = 2) : ∃ v a, k = .thm v a := by
  cases k <;> simp_all [CKindF.tag]

theorem tag_ax {N E : Type} {k : CKindF N E} (h : k.tag = 0) : ∃ u, k = .ax u := by
  cases k <;> simp_all [CKindF.tag]

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:45-52 subsumes — the tags upstream's kinds
compare at. -/
theorem kindsArm_false {z1 z2 : ConLeche.Frontend.Olean.CKind} {n : ConLeche.Name}
    (h : ¬ ((z1.tag = 2 ∧ z2.tag = 2) ∨ (z1.tag = 2 ∧ z2.tag = 0) ∨ (z1.tag = 0 ∧ z2.tag = 0)))
    {m : Std.HashMap ConLeche.Name ConLeche.Frontend.Olean.CEntry} {t : Expr} :
    (match (generalizing := false) z1, z2 with
      | .thm _ a₁, .thm _ a₂ => a₁ == a₂
      | .thm _ a₁, .ax u₂ => a₁ == [n] && !u₂
      | .ax u₁, .ax u₂ => u₁ == u₂ && ConLeche.Frontend.Olean.isPropCheap m t
      | _, _ => false) = false := by
  cases z1 <;> cases z2 <;> first
    | rfl
    | exact (h (.inl ⟨rfl, rfl⟩)).elim
    | exact (h (.inr (.inl ⟨rfl, rfl⟩))).elim
    | exact (h (.inr (.inr ⟨rfl, rfl⟩))).elim

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:45-52 subsumes — **the twin's `true` is
upstream's, and upstream may say `true` to a twin's `false` only at two axioms of one type**, where
the twin's own test answered `false`. -/
theorem subsumes_run {pk : OleanPins} {s : AState} (hok : StateOK s) (hnu : NullsRel s.store pk)
    {mg : Merged} {mgC : ConLeche.Frontend.Olean.Merged} (hm : MergedRel s.store mg mgC)
    {c1 c2 : CEntry} {z1 z2 : ConLeche.Frontend.Olean.CEntry}
    (h1 : denoteCEntry s.store c1 = some z1) (h2 : denoteCEntry s.store c2 = some z2)
    {b : Bool} {s' : AState} (h : subsumes pk mg c1 c2 s = .ok (b, s')) :
    s' = s ∧ (b = true → ConLeche.Frontend.Olean.subsumes mgC.map z1 z2 = true) ∧
      (b = false → ConLeche.Frontend.Olean.subsumes mgC.map z1 z2 = true →
        ∃ u, c1.c.kind = .ax u ∧ c2.c.kind = .ax u ∧ c1.c.type = c2.c.type ∧
          isPropCheap pk mg c1.c.type s = .ok (false, s)) := by
  have hw := nsWF_of_StateOK hok
  obtain ⟨n1, l1, t1, k1⟩ := denoteCEntry_parts h1
  obtain ⟨n2, l2, t2, k2⟩ := denoteCEntry_parts h2
  have hcmp : (c1.c.name == c2.c.name && c1.c.type == c2.c.type && c1.c.levelParams == c2.c.levelParams)
      = (z1.name == z2.name && z1.type == z2.type && z1.levelParams == z2.levelParams) := by
    have e1 : (c1.c.name == c2.c.name) = (z1.name == z2.name) := by
      cases hb : (c1.c.name == c2.c.name) with
      | true =>
        have := beq_iff_eq.mp hb
        rw [this] at n1
        have hz : z1.name = z2.name := Option.some.inj (n1.symm.trans n2)
        simp [hz]
      | false =>
        symm
        rw [beq_eq_false_iff_ne]
        intro hz
        have := denoteN_inj hw n1 (hz ▸ n2)
        simp [this] at hb
    have e2 : (c1.c.type == c2.c.type) = (z1.type == z2.type) := by
      cases hb : (c1.c.type == c2.c.type) with
      | true =>
        have := beq_iff_eq.mp hb
        rw [this] at t1
        have hz : z1.type = z2.type := Option.some.inj (t1.symm.trans t2)
        simp [hz]
      | false =>
        symm
        rw [beq_eq_false_iff_ne]
        intro hz
        have := denoteE_inj hok.wf t1 (hz ▸ t2)
        simp [this] at hb
    have e3 : (c1.c.levelParams == c2.c.levelParams) = (z1.levelParams == z2.levelParams) := by
      cases hb : (c1.c.levelParams == c2.c.levelParams) with
      | true =>
        have := beq_iff_eq.mp hb
        rw [this] at l1
        have hz : z1.levelParams = z2.levelParams := Option.some.inj (l1.symm.trans l2)
        simp [hz]
      | false =>
        symm
        rw [beq_eq_false_iff_ne]
        intro hz
        have := nameList_inj hw l1 (hz ▸ l2)
        simp [this] at hb
    rw [e1, e2, e3]
  generalize hF : subsumes pk mg c1 c2 = f at h
  unfold subsumes at hF
  unfold ConLeche.Frontend.Olean.subsumes
  rw [← hcmp]
  by_cases hc : (c1.c.name == c2.c.name && c1.c.type == c2.c.type && c1.c.levelParams == c2.c.levelParams) = true
  · simp only [hc, ↓reduceIte, Bool.true_and] at hF ⊢
    have hty : c1.c.type = c2.c.type := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact hc.1.2
    have htag1 := (ConLeche.Frontend.Olean.CKindF.mapM_tag k1).1
    have htag2 := (ConLeche.Frontend.Olean.CKindF.mapM_tag k2).1
    split at hF
    · -- two theorems
      rename_i v a v' a' hk1 hk2
      subst hF
      rw [hk1] at k1
      rw [hk2] at k2
      simp only [CKindF.mapM] at k1 k2
      obtain ⟨w, -, k1⟩ := bind_some_left k1
      obtain ⟨as, ha, k1⟩ := bind_some_left k1
      obtain ⟨w', -, k2⟩ := bind_some_left k2
      obtain ⟨as', ha', k2⟩ := bind_some_left k2
      simp only [pure, Option.some.injEq] at k1 k2
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      subst hv
      simp only [← k1, ← k2]
      rw [nameList_beq hw ha ha']
      exact ⟨hs, id, fun hb hb' => by rw [hb] at hb'; cases hb'⟩
    · -- a theorem and an axiom
      rename_i v a u hk1 hk2
      subst hF
      rw [hk1] at k1
      rw [hk2] at k2
      simp only [CKindF.mapM] at k1 k2
      obtain ⟨w, -, k1⟩ := bind_some_left k1
      obtain ⟨as, ha, k1⟩ := bind_some_left k1
      simp only [pure, Option.some.injEq] at k1 k2
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      subst hv
      simp only [← k1, ← k2]
      have hl : [c2.c.name].mapM (denoteN s.store.ns) = some [z2.name] := by
        simp only [List.mapM_cons, List.mapM_nil, n2]; rfl
      rw [nameList_beq hw ha hl]
      exact ⟨hs, id, fun hb hb' => by rw [hb] at hb'; cases hb'⟩
    · -- two axioms
      rename_i u u' hk1 hk2
      subst hF
      rw [hk1] at k1
      rw [hk2] at k2
      simp only [CKindF.mapM, pure, Option.some.injEq] at k1 k2
      simp only [← k1, ← k2]
      by_cases hu : (u == u') = true
      · simp only [hu, ↓reduceIte, Bool.true_and] at h ⊢
        obtain ⟨hs, htrue⟩ := isPropCheap_run hok hnu hm t1 h
        refine ⟨hs, htrue, fun hb _ => ?_⟩
        have huu : u = u' := by simpa using hu
        subst huu
        subst hb
        rw [hs] at h
        exact ⟨u, hk1, hk2, hty, h⟩
      · simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨hv, hs⟩ := AM.pure_ok h
        subst hv
        simp only [Bool.not_eq_true] at hu
        refine ⟨hs, fun hb => (by cases hb), fun _ hb => ?_⟩
        simp [hu] at hb
    · -- anything else
      rename_i h3 h4 h5
      subst hF
      obtain ⟨hv, hs⟩ := AM.pure_ok h
      subst hv
      have hfalse := kindsArm_false (z1 := z1.kind) (z2 := z2.kind) (n := z2.name) (m := mgC.map)
        (t := z1.type) (by
          rw [← htag1, ← htag2]
          rintro (⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩)
          · obtain ⟨v, x, e⟩ := tag_thm a
            obtain ⟨v', x', e'⟩ := tag_thm b
            exact h3 _ _ _ _ e e'
          · obtain ⟨v, x, e⟩ := tag_thm a
            obtain ⟨u, e'⟩ := tag_ax b
            exact h4 _ _ _ e e'
          · obtain ⟨u, e⟩ := tag_ax a
            obtain ⟨u', e'⟩ := tag_ax b
            exact h5 _ _ e e')
      refine ⟨hs, fun hb => (by cases hb), fun _ hb => ?_⟩
      have hb2 := hfalse.symm.trans hb
      cases hb2
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hF
    subst hF
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    simp only [Bool.not_eq_true] at hc
    subst hv
    refine ⟨hs, fun hb => (by cases hb), fun _ hb => ?_⟩
    simp [hc] at hb

/-- At two axioms of one type, `subsumes` answers its test on the type, in either order. -/
theorem subsumes_ax_false {pk : OleanPins} {mg : Merged} {c1 c2 : CEntry} {u : Bool} {s : AState}
    (h1 : c1.c.kind = .ax u) (h2 : c2.c.kind = .ax u)
    (ht : isPropCheap pk mg c1.c.type s = .ok (false, s)) :
    subsumes pk mg c1 c2 s = .ok (false, s) := by
  generalize hF : subsumes pk mg c1 c2 = f
  unfold subsumes at hF
  by_cases hc : (c1.c.name == c2.c.name && c1.c.type == c2.c.type && c1.c.levelParams == c2.c.levelParams) = true
  · simp only [hc, ↓reduceIte, h1, h2, BEq.rfl] at hF
    subst hF
    exact ht
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hF
    subst hF
    rfl

/-! ## One constant -/

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:59-70 mergeEntry — a constant stored under its
name, on both sides. -/
theorem MergedRel.insert {st : EStore} (hw : NStoreWF st.ns) {mg : Merged}
    {mgC : ConLeche.Frontend.Olean.Merged} (hm : MergedRel st mg mgC) {m i : Nat} {c : CEntry}
    {cC : ConLeche.Frontend.Olean.CEntry}
    (hc : (mg.ls[m]?).bind (·.constants[i]?) = some c) (hd : denoteCEntry st c = some cC)
    (ord : Array NIdx) (ordC : Array ConLeche.Name)
    (hord : ListRel (NR st) ord.toList ordC.toList) :
    MergedRel st { ls := mg.ls, map := mg.map.insert c.c.name (m, i), order := ord }
      { map := mgC.map.insert cC.name cC, order := ordC } := by
  obtain ⟨hn, -, -, -⟩ := denoteCEntry_parts hd
  have hget : ∀ (n : NIdx), n ≠ c.c.name →
      ({ ls := mg.ls, map := mg.map.insert c.c.name (m, i), order := ord } : Merged).get n = mg.get n := by
    intro n hne
    have hbne : (c.c.name == n) = false := by
      simpa using fun e : c.c.name = n => hne e.symm
    simp only [Merged.get, Std.HashMap.getElem?_insert, hbne, Bool.false_eq_true, ↓reduceIte]
  have hself : ({ ls := mg.ls, map := mg.map.insert c.c.name (m, i), order := ord } : Merged).get
      c.c.name = some c := by
    simp only [Merged.get, Std.HashMap.getElem?_insert_self]
    exact hc
  refine ⟨fun {n nC x} hdn hx => ?_, fun {n nC} hdn hx => ?_, fun {n nC} hdn => ?_, hord,
    fun {n p} hp => ?_, fun {nC z} hz => ?_⟩
  · by_cases e : n = c.c.name
    · subst e
      rw [hself] at hx
      cases hx
      have hnn : nC = cC.name := Option.some.inj (hdn.symm.trans hn)
      subst hnn
      exact ⟨cC, Std.HashMap.getElem?_insert_self, hd⟩
    · rw [hget n e] at hx
      obtain ⟨z, hz, hdz⟩ := hm.got hdn hx
      have hne : cC.name ≠ nC := fun e' => e (denoteN_inj hw hdn (e' ▸ hn))
      refine ⟨z, ?_, hdz⟩
      simp only [Std.HashMap.getElem?_insert, hne, beq_iff_eq, ↓reduceIte, hz]
  · by_cases e : n = c.c.name
    · subst e
      rw [hself] at hx
      cases hx
    · rw [hget n e] at hx
      have hne : cC.name ≠ nC := fun e' => e (denoteN_inj hw hdn (e' ▸ hn))
      simp only [Std.HashMap.getElem?_insert, hne, beq_iff_eq, ↓reduceIte, hm.absent hdn hx]
  · simp only [Std.HashMap.contains_insert]
    rw [hm.contains hdn]
    by_cases e : n = c.c.name
    · subst e
      have hnn : nC = cC.name := Option.some.inj (hdn.symm.trans hn)
      subst hnn
      simp
    · have hne : cC.name ≠ nC := fun e' => e (denoteN_inj hw hdn (e' ▸ hn))
      have hne' : c.c.name ≠ n := fun e' => e e'.symm
      rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr hne']
  · rw [Std.HashMap.getElem?_insert] at hp
    by_cases e : c.c.name = n
    · subst e
      rw [hn]
      rfl
    · rw [beq_eq_false_iff_ne.mpr e] at hp
      exact hm.keys hp
  · rw [Std.HashMap.getElem?_insert] at hz
    by_cases e : cC.name = nC
    · subst e
      exact ⟨c.c.name, hn, by simp⟩
    · rw [beq_eq_false_iff_ne.mpr e] at hz
      obtain ⟨n, hdn, hcn⟩ := hm.keysC hz
      exact ⟨n, hdn, by simp [Std.HashMap.contains_insert, hcn]⟩

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:59-70 mergeEntry — **one constant merged**,
the arm upstream's. -/
theorem mergeEntry_run {pk : OleanPins} {s : AState} (hok : StateOK s) (hnu : NullsRel s.store pk)
    {mg mg' : Merged} {mgC : ConLeche.Frontend.Olean.Merged} (hm : MergedRel s.store mg mgC)
    {m i : Nat} {c : CEntry} {cC : ConLeche.Frontend.Olean.CEntry}
    (hc : (mg.ls[m]?).bind (·.constants[i]?) = some c) (hd : denoteCEntry s.store c = some cC)
    {s' : AState} (h : mergeEntry pk mg m i c s = .ok (mg', s')) :
    s' = s ∧ mg'.ls = mg.ls ∧ ∃ mgC', ConLeche.Frontend.Olean.mergeEntry mgC cC = .ok mgC' ∧
      MergedRel s.store mg' mgC' := by
  have hw := nsWF_of_StateOK hok
  obtain ⟨hn, -, -, -⟩ := denoteCEntry_parts hd
  unfold mergeEntry at h
  cases hg : mg.get c.c.name with
  | none =>
    simp only [hg] at h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    subst hv
    refine ⟨hs, rfl, _, ?_, hm.insert hw hc hd (mg.order.push c.c.name) (mgC.order.push cC.name)
      (array_rel_push hm.order hn)⟩
    simp only [ConLeche.Frontend.Olean.mergeEntry, hm.absent hn hg]
    rfl
  | some prev =>
    simp only [hg] at h
    obtain ⟨prevC, hp, hdp⟩ := hm.got hn hg
    obtain ⟨b1, s₁, h1, h2⟩ := AM.bind_ok h
    obtain ⟨hs1, ht1, hf1⟩ := subsumes_run hok hnu hm hd hdp h1
    rw [hs1] at h2
    cases b1 with
    | true =>
      simp only [↓reduceIte] at h2
      obtain ⟨hv, hs⟩ := AM.pure_ok h2
      subst hv
      refine ⟨hs, rfl, _, ?_, hm.insert hw hc hd mg.order mgC.order hm.order⟩
      simp only [ConLeche.Frontend.Olean.mergeEntry, hp, ht1 rfl, ↓reduceIte]
      rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h2
      obtain ⟨b2, s₂, h3, h4⟩ := AM.bind_ok h2
      obtain ⟨hs2, ht2, -⟩ := subsumes_run hok hnu hm hdp hd h3
      rw [hs2] at h4
      cases b2 with
      | true =>
        simp only [↓reduceIte] at h4
        obtain ⟨hv, hs⟩ := AM.pure_ok h4
        subst hv
        refine ⟨hs, rfl, mgC, ?_, hm⟩
        have hfalse : ConLeche.Frontend.Olean.subsumes mgC.map cC prevC = false := by
          cases he : ConLeche.Frontend.Olean.subsumes mgC.map cC prevC with
          | false => rfl
          | true =>
            obtain ⟨u, ha, hb, hty, hisp⟩ := hf1 rfl he
            have hisp' : isPropCheap pk mg' prev.c.type s = .ok (false, s) := by
              rw [← hty]; exact hisp
            have := subsumes_ax_false hb ha hisp'
            rw [hs2, this] at h3
            cases h3
        simp only [ConLeche.Frontend.Olean.mergeEntry, hp, hfalse, Bool.false_eq_true, ↓reduceIte,
          ht2 rfl]
        rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h4
        obtain ⟨n, s₃, h5, h6⟩ := AM.bind_ok h4
        cases h6

/-! ## The two loops -/

/-- A `for` over a range, every step yielding, with its invariant. -/
theorem forIn'_range_inv {β : Type} {n : Nat} {f : (i : Nat) → i ∈ [0:n] → β → AM (ForInStep β)}
    {I : Nat → β → AState → Prop}
    (hstep : ∀ i (hi : i ∈ [0:n]) b s r s', I i b s → f i hi b s = .ok (r, s') →
      ∃ b', r = .yield b' ∧ I (i + 1) b' s') {b₀ b : β} {s₀ s : AState} (h₀ : I 0 b₀ s₀)
    (h : forIn' [0:n] b₀ f s₀ = .ok (b, s)) : I n b s := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range'] at h
  have key : ∀ (m k : Nat) (hle : k + m = n) {b₁ : β} {s₁ : AState}, I k b₁ s₁ →
      ∀ (g : (i : Nat) → i ∈ List.range' k m 1 → β → AM (ForInStep β)),
      (∀ i hi b s r s', I i b s → g i hi b s = .ok (r, s') →
        ∃ b', r = .yield b' ∧ I (i + 1) b' s') →
      forIn' (List.range' k m 1) b₁ g s₁ = .ok (b, s) → I n b s := by
    intro m
    induction m with
    | zero =>
      intro k hle b₁ s₁ hI g _ hrun
      have hk : k = n := by omega
      subst hk
      simp only [List.range'_zero, List.forIn'_nil] at hrun
      obtain ⟨hv, hs⟩ := AM.pure_ok hrun
      subst hv
      subst hs
      exact hI
    | succ m ih =>
      intro k hle b₁ s₁ hI g hg hrun
      simp only [List.range'_succ, List.forIn'_cons] at hrun
      obtain ⟨r, s₂, h1, h2⟩ := AM.bind_ok hrun
      obtain ⟨b', rfl, hI'⟩ := hg k (by simp) b₁ s₁ r s₂ hI h1
      exact ih (k + 1) (by omega) hI' _
        (fun i hi b s r s' hI2 hrun2 => hg i _ b s r s' hI2 hrun2) h2
  have hsize : ([0:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  exact key _ 0 (by rw [hsize]; omega) h₀ _
    (fun i hi b s r s' hI hrun => hstep i _ b s r s' hI hrun) h

theorem listRel_get {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {ys : List β}, ListRel R l ys → ∀ {i : Nat} (hi : i < l.length),
      ∃ hj : i < ys.length, R l[i] ys[i]
  | _, _, .nil, _, hi => by simp at hi
  | _, _, .cons a _, 0, _ => ⟨by simp, a⟩
  | _, _, .cons _ b, i + 1, hi => by
    obtain ⟨hj, hr⟩ := listRel_get b (i := i) (by simpa using hi)
    exact ⟨by simpa using hj, hr⟩

/-- The folds of upstream's merge, a list at a time. -/
theorem foldlM_take_succ {α β ε : Type} (f : β → α → Except ε β) (l : List α) (b : β) {i : Nat}
    (hi : i < l.length) :
    (l.take (i + 1)).foldlM f b = (l.take i).foldlM f b >>= fun a => f a l[i] := by
  rw [← List.take_append_getElem hi, List.foldlM_append]
  simp

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:72-73 mergeAll — **the closure's constants
merged, on the same arms.** -/
theorem mergeAll_run {pk : OleanPins} {s : AState} (hok : StateOK s) (hnu : NullsRel s.store pk)
    {ls : Array Loaded} {lsC : List ConLeche.Frontend.Olean.Loaded}
    (hrel : ListRel (LoadedRel s.store) ls.toList lsC)
    {mg : Merged} {s' : AState} (h : mergeAll pk ls s = .ok (mg, s')) :
    s' = s ∧ mg.ls = ls ∧ ∃ mgC, ConLeche.Frontend.Olean.mergeAll lsC.toArray = .ok mgC ∧
      MergedRel s.store mg mgC := by
  let stepC : ConLeche.Frontend.Olean.Merged → ConLeche.Frontend.Olean.Loaded →
      Except ConLeche.CheckError ConLeche.Frontend.Olean.Merged :=
    fun mg l => l.constants.foldlM ConLeche.Frontend.Olean.mergeEntry mg
  unfold mergeAll at h
  obtain ⟨b, s₁, hloop, h⟩ := AM.bind_ok h
  obtain ⟨hv, hs⟩ := AM.pure_ok h
  subst hv
  subst hs
  have hinit : MergedRel s.store { ls := ls } ({} : ConLeche.Frontend.Olean.Merged) :=
    ⟨fun {n nC c} _ hc => by simp [Merged.get] at hc,
     fun {n nC} _ _ => by simp,
     fun {n nC} _ => by simp,
     .nil,
     fun {n p} hp => by simp at hp,
     fun {nC c} hc => by simp at hc⟩
  have hI := forIn'_range_inv (I := fun m (b : Merged) t => s = t ∧ b.ls = ls ∧ ∃ mgC,
      (lsC.take m).foldlM stepC {} = .ok mgC ∧ MergedRel s.store b mgC)
    (fun m hm b t r t' hI hrun => by
      obtain ⟨rfl, hbl, mgC, hfold, hrelB⟩ := hI
      have hml : m < ls.toList.length := by simpa using hm.2.1
      obtain ⟨hmC, hdl⟩ := listRel_get hrel hml
      simp only [Array.getElem_toList] at hdl
      have hcsR := listRel_of_mapM hdl.constants
      dsimp only at hrun
      obtain ⟨c, t₁, hin, hrest⟩ := AM.bind_ok hrun
      simp only [pure_bind] at hrest
      obtain ⟨hv, hs⟩ := AM.pure_ok hrest
      have hJ := forIn'_range_inv (I := fun i (b : Merged) u => s = u ∧ b.ls = ls ∧ ∃ mgD,
          (lsC[m].constants.toList.take i).foldlM ConLeche.Frontend.Olean.mergeEntry mgC = .ok mgD ∧
            MergedRel s.store b mgD)
        (fun i hi b u r u' hJ hrun2 => by
          obtain ⟨hu, hbl', mgD, hf, hrd⟩ := hJ
          subst hu
          obtain ⟨b2, u₁, h1, h2⟩ := AM.bind_ok hrun2
          simp only [pure_bind] at h2
          obtain ⟨hv2, hs2⟩ := AM.pure_ok h2
          have hil : i < ls[m].constants.toList.length := by simpa using hi.2.1
          obtain ⟨hic, hdc⟩ := listRel_get hcsR hil
          simp only [Array.getElem_toList] at hdc
          have hmm : m < ls.size := hm.2.1
          have hii : i < ls[m].constants.size := hi.2.1
          have hpos : (b.ls[m]?).bind (·.constants[i]?) = some ls[m].constants[i] := by
            rw [hbl']
            simp [hmm, hii]
          obtain ⟨e1, e2, mgE, e3, e4⟩ := mergeEntry_run hok hnu hrd hpos hdc h1
          refine ⟨b2, hv2, ?_⟩
          refine ⟨(hs2.trans e1).symm, e2.trans hbl', mgE, ?_, e4⟩
          rw [foldlM_take_succ _ _ _ hic, hf]
          exact e3)
        (b₀ := b) (s₀ := s) ⟨rfl, hbl, mgC, rfl, hrelB⟩ hin
      obtain ⟨hu, hcl, mgD, hf, hrd⟩ := hJ
      refine ⟨c, hv, hu.trans hs.symm, hcl, mgD, ?_, hrd⟩
      have hlen : lsC[m].constants.toList.length = ls[m].constants.size := by
        have := hcsR.length_eq
        simpa using this.symm
      rw [← hlen, List.take_length] at hf
      rw [foldlM_take_succ _ _ _ hmC, hfold]
      show stepC mgC lsC[m] = _
      simp only [stepC]
      rw [← Array.foldlM_toList]
      exact hf)
    (b₀ := { ls := ls }) (s₀ := s) ⟨rfl, rfl, {}, rfl, hinit⟩ hloop
  obtain ⟨hs, hbl, mgC, hf, hrd⟩ := hI
  have hlen : lsC.length = ls.size := by
    have := hrel.length_eq
    simpa using this.symm
  rw [← hlen, List.take_length] at hf
  refine ⟨hs.symm, hbl, mgC, ?_, hrd⟩
  simp only [ConLeche.Frontend.Olean.mergeAll, List.foldlM_toArray]
  exact hf

end ConRon.Bridge.Frontend.Olean

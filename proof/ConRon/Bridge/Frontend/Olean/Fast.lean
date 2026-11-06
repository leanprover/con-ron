/-
# `ConRon.Bridge.Frontend.Olean.Fast` — both passes over one region

The mark pass is upstream's own, so `Verify/Frontend/Olean/Mark.lean`'s `markPass_spec`
applies as it stands: at its `A := False` it says that a mark pass which did not fail
leaves every marked object's kids marked (`Closed`).  The upward sweep is the twin's, and
its invariant is upstream's `Built` over handles: **every marked slot below the sweep
holds a handle denoting the specification's value** (`nameAt`, `levelAt`, `levelsAt`,
`exprAt`).  A slot not marked holds a filler, and nothing reads it.

So this tier relates the twin's memo to the specification directly and never to upstream's
fast decoder: `parseView_eq_spec` is the bridge between that decoder and the specification,
and the twin meets them at the specification.
-/
module

public import ConRon.Arena.Frontend.Olean.Fast
public import ConRon.Bridge.Frontend.Olean.Nodes
public import ConLeche.Verify.Frontend.Olean.Mark
public import ConLeche.Verify.Frontend.Olean.Engine
public import ConLeche.Verify.Frontend.Olean.Equiv
import ConLeche.Verify.Frontend.Olean.Build

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Arena.Frontend.Olean (OleanPins Sub DS buildSlot buildPass)
open ConLeche.Frontend.Olean (Region Kid kName kLevel kLevels kExpr kidTable nameAt levelAt levelsAt
  exprAt marked marksAt Closed IsKind getD_set! eight_div)

/-- con-leche: ConLeche/Verify/Frontend/Olean/Build.lean:26 ValOK — the marked object at
slot `s`, read as kind `k`, is its specification's value, denoted by the memo's handle. -/
@[expose] def SlotOK (st : EStore) (r : Region) (memo : DS) (k : UInt8) (s : Nat) : Prop :=
  (k = kName → ∃ n, nameAt r (8 * s) = some n ∧
    denoteN st.ns (memo.names.getD s default) = some n) ∧
  (k = kLevel → ∃ u, levelAt r (8 * s) = some u ∧
    denoteL st.ls (memo.levels.getD s default) = some u) ∧
  (k = kLevels → ∃ us, levelsAt r (8 * s) = some us ∧
    denoteLs st.lss (memo.lists.getD s default) = some us) ∧
  (k = kExpr → ∃ e, exprAt r (8 * s) = some e ∧
    denoteE st (memo.exprs.getD s default) = some e)

theorem SlotOK.ext {st st' : EStore} {r : Region} {memo : DS} {k : UInt8} {s : Nat}
    (h : SlotOK st r memo k s) (hx : Ext st st') : SlotOK st' r memo k s := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · obtain ⟨n, a, b⟩ := h1 e; exact ⟨n, a, denoteN_ext b hx⟩
  · obtain ⟨n, a, b⟩ := h2 e; exact ⟨n, a, denoteL_ext b hx⟩
  · obtain ⟨n, a, b⟩ := h3 e; exact ⟨n, a, denoteLs_ext b hx⟩
  · obtain ⟨n, a, b⟩ := h4 e; exact ⟨n, a, denote_ext b hx⟩

/-- con-leche: ConLeche/Verify/Frontend/Olean/Build.lean:33 Built — every marked object
below slot `p` holds its value. -/
@[expose] def Built (st : EStore) (r : Region) (m : ByteArray) (memo : DS) (p : Nat) : Prop :=
  ∀ s, s < p → ∀ k, IsKind k → marked m k s = true → SlotOK st r memo k s

/-- `Built` and the kinds of slot `p` already swept. -/
@[expose] def Part (st : EStore) (r : Region) (m : ByteArray) (memo : DS) (p : Nat)
    (K : UInt8 → Prop) : Prop :=
  Built st r m memo p ∧ ∀ k, K k → IsKind k → marked m k p = true → SlotOK st r memo k p

theorem Part.ext {st st' : EStore} {r : Region} {m : ByteArray} {memo : DS} {p : Nat}
    {K : UInt8 → Prop} (h : Part st r m memo p K) (hx : Ext st st') : Part st' r m memo p K :=
  ⟨fun s hs k hk hm => (h.1 s hs k hk hm).ext hx,
   fun k hK hk hm => (h.2 k hK hk hm).ext hx⟩

/-- con-leche: ConLeche/Verify/Frontend/Olean/Build.lean:38 kid_val — the memo answers at
a kid of a marked object below the sweep. -/
theorem Built.subRel {st : EStore} {r : Region} {m : ByteArray} {memo : DS} {p n : Nat}
    (hc : Closed r m 0 n) (hb : Built st r m memo p) (hpn : p < n) {k : UInt8} (hk : IsKind k)
    (hm : marked m k p = true) :
    SubRel st r k (8 * p) memo.sub (fun c _ => exprAt r c) (fun c _ => nameAt r c)
      (fun c _ => levelAt r c) (fun c _ => levelsAt r c) := by
  have hkid : ∀ {k' : UInt8} {c : Nat}, Kid r k (8 * p) k' c → SlotOK st r memo k' (c / 8) := by
    intro k' c hkid
    have hlt := hkid.lt
    have hmod := hkid.mod
    exact hb (c / 8) (by omega) k' hkid.kind ((hc p (by omega) hpn k hk hm).2 k' c hkid)
  refine ⟨fun c _ h => ?_, fun c _ h => ?_, fun c _ h => ?_, fun c _ h => ?_⟩
  · obtain ⟨x, a, b⟩ := (hkid h).1 rfl
    rw [eight_div h.mod] at a
    exact ⟨_, x, rfl, b, a⟩
  · obtain ⟨x, a, b⟩ := (hkid h).2.1 rfl
    rw [eight_div h.mod] at a
    exact ⟨_, x, rfl, b, a⟩
  · obtain ⟨x, a, b⟩ := (hkid h).2.2.1 rfl
    rw [eight_div h.mod] at a
    exact ⟨_, x, rfl, b, a⟩
  · obtain ⟨x, a, b⟩ := (hkid h).2.2.2 rfl
    rw [eight_div h.mod] at a
    exact ⟨_, x, rfl, b, a⟩

/-! ## A slot's writes -/

/-- con-leche: ConLeche/Verify/Frontend/Olean/Memo.lean:135 DS.Sized -/
structure Sized (memo : DS) (n : Nat) : Prop where
  names : memo.names.size = n
  levels : memo.levels.size = n
  exprs : memo.exprs.size = n
  lists : memo.lists.size = n

theorem sized_fresh (n : Nat) : Sized (DS.fresh n) n :=
  ⟨by simp [DS.fresh], by simp [DS.fresh], by simp [DS.fresh], by simp [DS.fresh]⟩

theorem getD_set_same {α : Type} {a : Array α} {p : Nat} {v d : α} (h : p < a.size) :
    (a.set! p v).getD p d = v := by
  simp [h]

theorem getD_set_ne {α : Type} {a : Array α} {p s : Nat} {v d : α} (h : p ≠ s) :
    (a.set! p v).getD s d = a.getD s d := by
  simp [h]

theorem kinds_ne' : kName ≠ kLevel ∧ kName ≠ kExpr ∧ kName ≠ kLevels ∧ kLevel ≠ kExpr ∧
    kLevel ≠ kLevels ∧ kExpr ≠ kLevels := by decide

theorem Part.setName {st : EStore} {r : Region} {m : ByteArray} {memo : DS} {p n : Nat}
    {K : UInt8 → Prop} (h : Part st r m memo p K) (hs : Sized memo n) (hp : p < n) {v : NIdx}
    {x : ConLeche.Name} (hx : nameAt r (8 * p) = some x) (hv : denoteN st.ns v = some x) :
    Part st r m (memo.setName p v) p (fun k => K k ∨ k = kName) ∧ Sized (memo.setName p v) n := by
  have hsz : memo.names.size = n := hs.names
  refine ⟨⟨fun s hsp k hk hm => ?_, fun k hK hk hm => ?_⟩, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h.1 s hsp k hk hm
    refine ⟨fun e => ?_, h2, h3, h4⟩
    obtain ⟨a, b, c⟩ := h1 e
    refine ⟨a, b, ?_⟩
    simp only [DS.setName]
    rw [getD_set_ne (by omega)]
    exact c
  · rcases hK with hK | rfl
    · obtain ⟨h1, h2, h3, h4⟩ := h.2 k hK hk hm
      refine ⟨fun e => ?_, h2, h3, h4⟩
      obtain ⟨a, b, c⟩ := h1 e
      refine ⟨a, b, ?_⟩
      simp only [DS.setName]
      rw [getD_set_same (by omega)]
      exact hv.trans (hx.symm.trans b)
    · refine ⟨fun _ => ⟨x, hx, ?_⟩, fun e => absurd e kinds_ne'.1, fun e => absurd e kinds_ne'.2.2.1,
        fun e => absurd e kinds_ne'.2.1⟩
      simp only [DS.setName]
      rw [getD_set_same (by omega)]
      exact hv
  · exact ⟨by simp [DS.setName, hs.names], hs.levels, hs.exprs, hs.lists⟩

theorem Part.setLevel {st : EStore} {r : Region} {m : ByteArray} {memo : DS} {p n : Nat}
    {K : UInt8 → Prop} (h : Part st r m memo p K) (hs : Sized memo n) (hp : p < n) {v : LIdx}
    {x : Level} (hx : levelAt r (8 * p) = some x) (hv : denoteL st.ls v = some x) :
    Part st r m (memo.setLevel p v) p (fun k => K k ∨ k = kLevel) ∧ Sized (memo.setLevel p v) n := by
  have hsz : memo.levels.size = n := hs.levels
  refine ⟨⟨fun s hsp k hk hm => ?_, fun k hK hk hm => ?_⟩, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h.1 s hsp k hk hm
    refine ⟨h1, fun e => ?_, h3, h4⟩
    obtain ⟨a, b, c⟩ := h2 e
    refine ⟨a, b, ?_⟩
    simp only [DS.setLevel]
    rw [getD_set_ne (by omega)]
    exact c
  · rcases hK with hK | rfl
    · obtain ⟨h1, h2, h3, h4⟩ := h.2 k hK hk hm
      refine ⟨h1, fun e => ?_, h3, h4⟩
      obtain ⟨a, b, c⟩ := h2 e
      refine ⟨a, b, ?_⟩
      simp only [DS.setLevel]
      rw [getD_set_same (by omega)]
      exact hv.trans (hx.symm.trans b)
    · refine ⟨fun e => absurd e.symm kinds_ne'.1, fun _ => ⟨x, hx, ?_⟩,
        fun e => absurd e kinds_ne'.2.2.2.2.1, fun e => absurd e kinds_ne'.2.2.2.1⟩
      simp only [DS.setLevel]
      rw [getD_set_same (by omega)]
      exact hv
  · exact ⟨hs.names, by simp [DS.setLevel, hs.levels], hs.exprs, hs.lists⟩

theorem Part.setLevels {st : EStore} {r : Region} {m : ByteArray} {memo : DS} {p n : Nat}
    {K : UInt8 → Prop} (h : Part st r m memo p K) (hs : Sized memo n) (hp : p < n) {v : LsIdx}
    {x : List Level} (hx : levelsAt r (8 * p) = some x) (hv : denoteLs st.lss v = some x) :
    Part st r m (memo.setLevels p v) p (fun k => K k ∨ k = kLevels) ∧
      Sized (memo.setLevels p v) n := by
  have hsz : memo.lists.size = n := hs.lists
  refine ⟨⟨fun s hsp k hk hm => ?_, fun k hK hk hm => ?_⟩, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h.1 s hsp k hk hm
    refine ⟨h1, h2, fun e => ?_, h4⟩
    obtain ⟨a, b, c⟩ := h3 e
    refine ⟨a, b, ?_⟩
    simp only [DS.setLevels]
    rw [getD_set_ne (by omega)]
    exact c
  · rcases hK with hK | rfl
    · obtain ⟨h1, h2, h3, h4⟩ := h.2 k hK hk hm
      refine ⟨h1, h2, fun e => ?_, h4⟩
      obtain ⟨a, b, c⟩ := h3 e
      refine ⟨a, b, ?_⟩
      simp only [DS.setLevels]
      rw [getD_set_same (by omega)]
      exact hv.trans (hx.symm.trans b)
    · refine ⟨fun e => absurd e.symm kinds_ne'.2.2.1, fun e => absurd e.symm kinds_ne'.2.2.2.2.1,
        fun _ => ⟨x, hx, ?_⟩, fun e => absurd e.symm kinds_ne'.2.2.2.2.2⟩
      simp only [DS.setLevels]
      rw [getD_set_same (by omega)]
      exact hv
  · exact ⟨hs.names, hs.levels, hs.exprs, by simp [DS.setLevels, hs.lists]⟩

theorem Part.setExpr {st : EStore} {r : Region} {m : ByteArray} {memo : DS} {p n : Nat}
    {K : UInt8 → Prop} (h : Part st r m memo p K) (hs : Sized memo n) (hp : p < n) {v : EIdx}
    {x : Expr} (hx : exprAt r (8 * p) = some x) (hv : denoteE st v = some x) :
    Part st r m (memo.setExpr p v) p (fun k => K k ∨ k = kExpr) ∧ Sized (memo.setExpr p v) n := by
  have hsz : memo.exprs.size = n := hs.exprs
  refine ⟨⟨fun s hsp k hk hm => ?_, fun k hK hk hm => ?_⟩, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h.1 s hsp k hk hm
    refine ⟨h1, h2, h3, fun e => ?_⟩
    obtain ⟨a, b, c⟩ := h4 e
    refine ⟨a, b, ?_⟩
    simp only [DS.setExpr]
    rw [getD_set_ne (by omega)]
    exact c
  · rcases hK with hK | rfl
    · obtain ⟨h1, h2, h3, h4⟩ := h.2 k hK hk hm
      refine ⟨h1, h2, h3, fun e => ?_⟩
      obtain ⟨a, b, c⟩ := h4 e
      refine ⟨a, b, ?_⟩
      simp only [DS.setExpr]
      rw [getD_set_same (by omega)]
      exact hv.trans (hx.symm.trans b)
    · refine ⟨fun e => absurd e.symm kinds_ne'.2.1, fun e => absurd e.symm kinds_ne'.2.2.2.1,
        fun e => absurd e kinds_ne'.2.2.2.2.2, fun _ => ⟨x, hx, ?_⟩⟩
      simp only [DS.setExpr]
      rw [getD_set_same (by omega)]
      exact hv
  · exact ⟨hs.names, hs.levels, by simp [DS.setExpr, hs.exprs], hs.lists⟩

/-! ## One slot, swept -/

/-- con-leche: ConLeche/Frontend/Olean/Fast.lean:232-241 buildKind
One kind of a slot, and what follows it. -/
@[expose] def slotStep {α : Type} (b : Bool) (node : AM (Option α)) (memo : DS) (set : α → DS)
    (k : DS → AM (Option DS)) : AM (Option DS) :=
  if b = true then do
    match ← node with
    | none => pure none
    | some v => k (set v)
  else k memo

theorem slotStep_run {α : Type} {b : Bool} {node : AM (Option α)} {memo memo' : DS} {set : α → DS}
    {k : DS → AM (Option DS)} {s s' : AState}
    (h : slotStep b node memo set k s = .ok (some memo', s')) :
    (b = false ∧ k memo s = .ok (some memo', s')) ∨
      (b = true ∧ ∃ v s₁, node s = .ok (some v, s₁) ∧ k (set v) s₁ = .ok (some memo', s')) := by
  unfold slotStep at h
  cases b with
  | false => exact .inl ⟨rfl, by simpa using h⟩
  | true =>
    simp only [↓reduceIte] at h
    obtain ⟨o, s₁, hn, hrest⟩ := AM.bind_ok h
    cases o with
    | none => exact (none_not_some (α := DS) hrest).elim
    | some v => exact .inr ⟨rfl, v, s₁, hn, hrest⟩

/-- A kind not marked at the slot is swept. -/
theorem Part.notMarked {st : EStore} {r : Region} {m : ByteArray} {memo : DS} {p : Nat}
    {K : UInt8 → Prop} {K' : UInt8} (h : Part st r m memo p K) (hb : marked m K' p = false) :
    Part st r m memo p (fun k => K k ∨ k = K') := by
  refine ⟨h.1, fun k hK hk hm => ?_⟩
  rcases hK with hK | rfl
  · exact h.2 k hK hk hm
  · rw [hb] at hm; cases hm

/-- The context every run of the reader carries. -/
structure Ctx (pk : OleanPins) (s : AState) : Prop where
  ok : StateOK s
  off : s.store.scratchOn = false
  nulls : NullsRel s.store pk

theorem Ctx.step {pk : OleanPins} {s s' : AState} (h : Ctx pk s) (hst : ParseStep s s') :
    Ctx pk s' :=
  ⟨hst.ok, by rw [hst.scratch]; exact h.off, h.nulls.ext hst.ext⟩

theorem buildSlot_run {pk : OleanPins} {r : Region} {m : ByteArray} {n p : Nat} {memo memo' : DS}
    {s s' : AState} (hctx : Ctx pk s) (hc : Closed r m 0 n) (hpn : p < n) (hs : Sized memo n)
    (hb : Built s.store r m memo p)
    (hrun : buildSlot pk r m memo p s = .ok (some memo', s')) :
    ParseStep s s' ∧ Built s'.store r m memo' (p + 1) ∧ Sized memo' n := by
  have hEq : buildSlot pk r m memo p =
      slotStep (marked m kName p) (Arena.Frontend.Olean.nameNode pk r (8 * p) memo.sub) memo (memo.setName p)
        (fun memo => slotStep (marked m kLevel p) (Arena.Frontend.Olean.levelNode pk r (8 * p) memo.sub)
          memo (memo.setLevel p)
          (fun memo => slotStep (marked m kLevels p) (Arena.Frontend.Olean.levelsNode pk r (8 * p) memo.sub)
            memo (memo.setLevels p)
            (fun memo => slotStep (marked m kExpr p) (Arena.Frontend.Olean.exprNode pk r (8 * p) memo.sub)
              memo (memo.setExpr p) (fun memo => pure (some memo))))) := by
    unfold buildSlot slotStep
    simp only [pure_bind]
    repeat' first | rfl | (refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)) | (refine bind_congr (fun x => ?_); cases x)
  rw [hEq] at hrun
  have hk1 : IsKind kName := Or.inl rfl
  have hk2 : IsKind kLevel := Or.inr (Or.inl rfl)
  have hk3 : IsKind kExpr := Or.inr (Or.inr (Or.inl rfl))
  have hk4 : IsKind kLevels := Or.inr (Or.inr (Or.inr rfl))
  have hp0 : Part s.store r m memo p (fun _ => False) := ⟨hb, fun _ h => h.elim⟩
  have hspec : ∀ (a : Nat), 8 * a = 8 * a := fun _ => rfl
  -- the name
  obtain ⟨memo1, s1, hst1, hP1, hS1, hrun1⟩ :
      ∃ memo1 s1, ParseStep s s1 ∧ Part s1.store r m memo1 p (fun k => False ∨ k = kName) ∧
        Sized memo1 n ∧ slotStep (marked m kLevel p) (Arena.Frontend.Olean.levelNode pk r (8 * p) memo1.sub)
          memo1 (memo1.setLevel p)
          (fun memo => slotStep (marked m kLevels p) (Arena.Frontend.Olean.levelsNode pk r (8 * p) memo.sub)
            memo (memo.setLevels p)
            (fun memo => slotStep (marked m kExpr p) (Arena.Frontend.Olean.exprNode pk r (8 * p) memo.sub)
              memo (memo.setExpr p) (fun memo => pure (some memo)))) s1 = .ok (some memo', s') := by
    rcases slotStep_run hrun with ⟨hb1, hk⟩ | ⟨hb1, v, s1, hn, hk⟩
    · exact ⟨memo, s, ParseStep.refl hctx.ok, hp0.notMarked hb1, hs, hk⟩
    · obtain ⟨hst, x, hx, hd⟩ := nameNode_run hctx.ok hctx.off hctx.nulls
        (hb.subRel hc hpn hk1 hb1) hn
      obtain ⟨hP, hS⟩ := (hp0.ext hst.ext).setName hs hpn (x := x)
        (by rw [nameAt]; exact hx) hd
      exact ⟨_, s1, hst, hP, hS, hk⟩
  have hctx1 := hctx.step hst1
  -- the level
  obtain ⟨memo2, s2, hst2, hP2, hS2, hrun2⟩ :
      ∃ memo2 s2, ParseStep s1 s2 ∧
        Part s2.store r m memo2 p (fun k => (False ∨ k = kName) ∨ k = kLevel) ∧
        Sized memo2 n ∧ slotStep (marked m kLevels p) (Arena.Frontend.Olean.levelsNode pk r (8 * p) memo2.sub)
            memo2 (memo2.setLevels p)
            (fun memo => slotStep (marked m kExpr p) (Arena.Frontend.Olean.exprNode pk r (8 * p) memo.sub)
              memo (memo.setExpr p) (fun memo => pure (some memo))) s2 = .ok (some memo', s') := by
    rcases slotStep_run hrun1 with ⟨hb1, hk⟩ | ⟨hb1, v, s2, hn, hk⟩
    · exact ⟨memo1, s1, ParseStep.refl hctx1.ok, hP1.notMarked hb1, hS1, hk⟩
    · obtain ⟨hst, x, hx, hd⟩ := levelNode_run hctx1.ok hctx1.off hctx1.nulls
        (hP1.1.subRel hc hpn hk2 hb1) hn
      obtain ⟨hP, hS⟩ := (hP1.ext hst.ext).setLevel hS1 hpn (x := x)
        (by rw [levelAt]; exact hx) hd
      exact ⟨_, s2, hst, hP, hS, hk⟩
  have hctx2 := hctx1.step hst2
  -- the list of levels
  obtain ⟨memo3, s3, hst3, hP3, hS3, hrun3⟩ :
      ∃ memo3 s3, ParseStep s2 s3 ∧
        Part s3.store r m memo3 p (fun k => ((False ∨ k = kName) ∨ k = kLevel) ∨ k = kLevels) ∧
        Sized memo3 n ∧ slotStep (marked m kExpr p) (Arena.Frontend.Olean.exprNode pk r (8 * p) memo3.sub)
              memo3 (memo3.setExpr p) (fun memo => pure (some memo)) s3 = .ok (some memo', s') := by
    rcases slotStep_run hrun2 with ⟨hb1, hk⟩ | ⟨hb1, v, s3, hn, hk⟩
    · exact ⟨memo2, s2, ParseStep.refl hctx2.ok, hP2.notMarked hb1, hS2, hk⟩
    · obtain ⟨hst, x, hx, hd⟩ := levelsNode_run hctx2.ok hctx2.off hctx2.nulls
        (hP2.1.subRel hc hpn hk4 hb1) hn
      obtain ⟨hP, hS⟩ := (hP2.ext hst.ext).setLevels hS2 hpn (x := x)
        (by rw [levelsAt]; exact hx) hd
      exact ⟨_, s3, hst, hP, hS, hk⟩
  have hctx3 := hctx2.step hst3
  -- the expression
  have hfin : ParseStep s3 s' ∧
      Part s'.store r m memo' p
        (fun k => (((False ∨ k = kName) ∨ k = kLevel) ∨ k = kLevels) ∨ k = kExpr) ∧
      Sized memo' n := by
    rcases slotStep_run hrun3 with ⟨hb1, hk⟩ | ⟨hb1, v, s4, hn, hk⟩
    · obtain ⟨hv, hs'⟩ := AM.pure_ok hk
      cases hv
      subst hs'
      exact ⟨ParseStep.refl hctx3.ok, hP3.notMarked hb1, hS3⟩
    · obtain ⟨hv, hs'⟩ := AM.pure_ok hk
      cases hv
      subst hs'
      obtain ⟨hst, x, hx, hd⟩ := exprNode_run hctx3.ok hctx3.off hctx3.nulls
        (hP3.1.subRel hc hpn hk3 hb1) hn
      obtain ⟨hP, hS⟩ := (hP3.ext hst.ext).setExpr hS3 hpn (x := x)
        (by rw [exprAt]; exact hx) hd
      exact ⟨hst, hP, hS⟩
  obtain ⟨hst4, hP4, hS4⟩ := hfin
  refine ⟨((hst1.trans hst2).trans hst3).trans hst4, fun t ht k hk hm => ?_, hS4⟩
  by_cases e : t = p
  · subst e
    refine hP4.2 k ?_ hk hm
    rcases hk with rfl | rfl | rfl | rfl <;> simp
  · exact hP4.1 t (by omega) k hk hm

/-! ## The upward sweep -/

/-- con-leche: ConLeche/Verify/Frontend/Olean/Build.lean buildPass_spec — **every marked
object of the region holds its value**, on the sweep's way up. -/
theorem buildPass_run {pk : OleanPins} {r : Region} {m : ByteArray} {n : Nat}
    (hc : Closed r m 0 n) : ∀ (fuel p : Nat), n - p ≤ fuel → ∀ {memo memo' : DS} {s s' : AState},
    Ctx pk s → Sized memo n → Built s.store r m memo p →
    buildPass pk r m n memo p s = .ok (some memo', s') →
    ParseStep s s' ∧ (p ≤ n → Built s'.store r m memo' n) ∧ Sized memo' n := by
  intro fuel
  induction fuel with
  | zero =>
    intro p hp memo memo' s s' hctx hs hb hrun
    rw [buildPass] at hrun
    have : ¬ p < n := by omega
    simp only [this, ↓reduceIte] at hrun
    obtain ⟨hv, hs'⟩ := AM.pure_ok hrun
    cases hv
    subst hs'
    refine ⟨ParseStep.refl hctx.ok, fun hpn => ?_, hs⟩
    have : p = n := by omega
    subst this
    exact hb
  | succ fuel ih =>
    intro p hp memo memo' s s' hctx hs hb hrun
    rw [buildPass] at hrun
    by_cases hpn : p < n
    · simp only [hpn, ↓reduceIte] at hrun
      by_cases hm : (marksAt m p != 0) = true
      · simp only [hm, ↓reduceIte] at hrun
        obtain ⟨o, s₁, hslot, hrest⟩ := AM.bind_ok hrun
        cases o with
        | none => exact (none_not_some (α := DS) hrest).elim
        | some st =>
          obtain ⟨hst, hb1, hs1⟩ := buildSlot_run hctx hc hpn hs hb hslot
          obtain ⟨hst2, hb2, hs2⟩ := ih (p + 1) (by omega) (hctx.step hst) hs1 hb1 hrest
          exact ⟨hst.trans hst2, fun _ => hb2 (by omega), hs2⟩
      · simp only [hm, Bool.false_eq_true, ↓reduceIte] at hrun
        have hb1 : Built s.store r m memo (p + 1) := by
          intro t ht k hk hmk
          by_cases e : t = p
          · subst e
            rw [ConLeche.Frontend.Olean.marked_of_marksAt_zero hm] at hmk
            cases hmk
          · exact hb t (by omega) k hk hmk
        obtain ⟨hst2, hb2, hs2⟩ := ih (p + 1) (by omega) hctx hs hb1 hrun
        exact ⟨hst2, fun _ => hb2 (by omega), hs2⟩
    · simp only [hpn, ↓reduceIte] at hrun
      obtain ⟨hv, hs'⟩ := AM.pure_ok hrun
      cases hv
      subst hs'
      refine ⟨ParseStep.refl hctx.ok, fun hle => ?_, hs⟩
      have : p = n := by omega
      subst this
      exact hb

/-! ## The roots -/

/-- con-leche: ConLeche/Verify/Frontend/Olean/Engine.lean:54 rootsFold — what marking the
roots does, where it does not fail. -/
theorem rootsFold_some {r : Region} {n : Nat} {K : UInt8} (hK : IsKind K) {nil : Bool} :
    ∀ (vs : List UInt64) (st st' : ByteArray), st.size = n →
      (∀ v ∈ vs, r.locGo v r.segs.size / 8 < n) →
      vs.foldlM (ConLeche.Frontend.Olean.markRoot r K nil) st = some st' →
      st'.size = n ∧ ConLeche.Frontend.Olean.failedM st' = ConLeche.Frontend.Olean.failedM st ∧
        ConLeche.Frontend.Olean.Sub st st' ∧
        ∀ v ∈ vs, ¬ (nil = true ∧ v = 1) → ∃ c, r.loc v = some c ∧ marked st' K (c / 8) = true
  | [], st, st', hs, _, h => by
    simp only [List.foldlM_nil] at h
    cases h
    exact ⟨hs, rfl, ConLeche.Frontend.Olean.Sub.refl st, fun _ h => absurd h (by simp)⟩
  | v :: vs, st, st', hs, hb, h => by
    simp only [List.foldlM_cons, bind, Option.bind] at h
    have hstep : ConLeche.Frontend.Olean.markRoot r K nil st v =
        if (nil && v == 1) = true then some st
        else match r.loc v with
          | some c => some (ConLeche.Frontend.Olean.mark st K (c / 8))
          | none => none := rfl
    rw [hstep] at h
    by_cases hn : nil = true ∧ v = 1
    · have : (nil && v == 1) = true := by simp [hn.1, hn.2]
      simp only [this, ↓reduceIte] at h
      obtain ⟨hs', hf', hsub, hm⟩ := rootsFold_some hK vs st st' hs (fun w hw => hb w (List.mem_cons_of_mem _ hw)) h
      refine ⟨hs', hf', hsub, fun w hw hnw => ?_⟩
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact absurd hn hnw
      · exact hm w hw hnw
    · have : (nil && v == 1) = false := by
        cases nil <;> simp_all
      simp only [this, Bool.false_eq_true, ↓reduceIte] at h
      cases hl : r.loc v with
      | none => simp [hl] at h
      | some c =>
        simp only [hl] at h
        have hs1 : (ConLeche.Frontend.Olean.mark st K (c / 8)).size = n := by
          rw [ConLeche.Frontend.Olean.size_mark, hs]
        obtain ⟨hs', hf', hsub, hm⟩ := rootsFold_some hK vs _ st' hs1 (fun w hw => hb w (List.mem_cons_of_mem _ hw)) h
        have hsub1 : ConLeche.Frontend.Olean.Sub st (ConLeche.Frontend.Olean.mark st K (c / 8)) := by
          intro k t hk hmk
          rw [ConLeche.Frontend.Olean.marked_mark st hK hk, hmk]
          rfl
        refine ⟨hs', hf'.trans (ConLeche.Frontend.Olean.failedM_mark st hK _), hsub1.trans hsub,
          fun w hw hnw => ?_⟩
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · refine ⟨c, hl, hsub K _ hK ?_⟩
          have hcn : c / 8 < n := by
            have := hb w (by simp); rw [ConLeche.Frontend.Olean.loc_eq hl] at this; exact this
          rw [ConLeche.Frontend.Olean.marked_mark st hK hK]
          simp [hs, hcn]
        · exact hm w hw hnw

end ConRon.Bridge.Frontend.Olean

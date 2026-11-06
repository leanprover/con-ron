/-
# `ConRon.Bridge.Frontend.Olean.Nodes` — one object of the file, interned

The twin's node functions (`Arena/Frontend/Olean/Spec.lean`) read an object and
intern it; con-leche's (`ConLeche/Frontend/Olean/Spec.lean`) read it and build the
value.  A node function asks about the objects below it through `sub`.

**The relation is denotation, at the kids.**  A memo's slot that was never written
holds a filler, in both readers, and the two fillers need not agree, so `SubRel` asks
for agreement exactly where a node reads: at a `Kid` (`Verify/Frontend/Olean/Kids.lean`)
of the object.  `Kid` is what upstream's `…Node_congr` lemmas use, and the mark pass
marks exactly the kids.

Each theorem is one direction: the twin's `some` is upstream's `some`, with the
denotation of the handle.  A twin's `none` or `fail` claims nothing.
-/
module

public import ConRon.Arena.Frontend.Olean.Spec
public import ConRon.Bridge.Frontend.Shared
public import ConLeche.Verify.Frontend.Olean.Kids
import ConRon.Bridge.Specs
import ConRon.Bridge.SpecsL

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Arena.Frontend.Olean (OleanPins Sub)
open ConLeche.Frontend.Olean (Region Kid kName kLevel kLevels kExpr kidTable)

/-- con-leche: none — the three nullary handles the node functions use, denoting. -/
structure NullsRel (st : EStore) (pk : OleanPins) : Prop where
  anon : denoteN st.ns pk.anon = some .anonymous
  zero : denoteL st.ls pk.zero = some .zero
  nil : denoteLs st.lss pk.nil = some []

theorem NullsRel.ext {st st' : EStore} {pk : OleanPins} (h : NullsRel st pk) (hx : Ext st st') :
    NullsRel st' pk :=
  ⟨denoteN_ext h.anon hx, denoteL_ext h.zero hx, denoteLs_ext h.nil hx⟩

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:111-206 nameNode — **`sub`
denotes at the kids** of the object at `g`, read as kind `k`. -/
structure SubRel (st : EStore) (r : Region) (k : UInt8) (g : Nat) (sub : Sub)
    (ex : (c : Nat) → c < g → Option Expr) (nm : (c : Nat) → c < g → Option ConLeche.Name)
    (lv : (c : Nat) → c < g → Option Level) (ls : (c : Nat) → c < g → Option (List Level)) :
    Prop where
  name : ∀ c h, Kid r k g kName c →
    ∃ x n, sub.name c = some x ∧ denoteN st.ns x = some n ∧ nm c h = some n
  level : ∀ c h, Kid r k g kLevel c →
    ∃ x u, sub.level c = some x ∧ denoteL st.ls x = some u ∧ lv c h = some u
  levels : ∀ c h, Kid r k g kLevels c →
    ∃ x us, sub.levels c = some x ∧ denoteLs st.lss x = some us ∧ ls c h = some us
  expr : ∀ c h, Kid r k g kExpr c →
    ∃ x e, sub.expr c = some x ∧ denoteE st x = some e ∧ ex c h = some e

/-! ## A pointer the object holds -/

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:73-78 Region.nameIn -/
theorem nameIn_sim {st : EStore} {pk : OleanPins} (hpk : NullsRel st pk) {r : Region} {g : Nat}
    {v : UInt64} {sub : Sub} {nm : (c : Nat) → c < g → Option ConLeche.Name}
    (hk : ∀ c h, ¬ v = 1 → r.down g v = some c →
      ∃ x n, sub.name c = some x ∧ denoteN st.ns x = some n ∧ nm c h = some n)
    {x : NIdx} (hx : Arena.Frontend.Olean.nameIn pk r g v sub = some x) :
    ∃ n, r.nameIn g v nm = some n ∧ denoteN st.ns x = some n := by
  unfold Arena.Frontend.Olean.nameIn at hx
  unfold Region.nameIn
  by_cases hv : v = 1
  · simp only [hv, BEq.rfl, ↓reduceIte, Option.some.injEq] at hx ⊢
    subst hx
    exact ⟨_, rfl, hpk.anon⟩
  · simp only [hv, beq_iff_eq, ↓reduceIte] at hx ⊢
    split
    · rename_i c heq
      rw [heq] at hx
      obtain ⟨y, n, hy, hd, hn⟩ := hk c (Region.down_lt heq) hv heq
      simp only [hy, Option.some.injEq] at hx
      subst hx
      exact ⟨n, hn, hd⟩
    · rename_i hc
      rw [hc] at hx
      cases hx

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:80-85 Region.levelIn -/
theorem levelIn_sim {st : EStore} {pk : OleanPins} (hpk : NullsRel st pk) {r : Region} {g : Nat}
    {v : UInt64} {sub : Sub} {lv : (c : Nat) → c < g → Option Level}
    (hk : ∀ c h, ¬ v = 1 → r.down g v = some c →
      ∃ x n, sub.level c = some x ∧ denoteL st.ls x = some n ∧ lv c h = some n)
    {x : LIdx} (hx : Arena.Frontend.Olean.levelIn pk r g v sub = some x) :
    ∃ n, r.levelIn g v lv = some n ∧ denoteL st.ls x = some n := by
  unfold Arena.Frontend.Olean.levelIn at hx
  unfold Region.levelIn
  by_cases hv : v = 1
  · simp only [hv, BEq.rfl, ↓reduceIte, Option.some.injEq] at hx ⊢
    subst hx
    exact ⟨_, rfl, hpk.zero⟩
  · simp only [hv, beq_iff_eq, ↓reduceIte] at hx ⊢
    split
    · rename_i c heq
      rw [heq] at hx
      obtain ⟨y, n, hy, hd, hn⟩ := hk c (Region.down_lt heq) hv heq
      simp only [hy, Option.some.injEq] at hx
      subst hx
      exact ⟨n, hn, hd⟩
    · rename_i hc
      rw [hc] at hx
      cases hx

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:87-92 Region.levelsIn -/
theorem levelsIn_sim {st : EStore} {pk : OleanPins} (hpk : NullsRel st pk) {r : Region} {g : Nat}
    {v : UInt64} {sub : Sub} {ls : (c : Nat) → c < g → Option (List Level)}
    (hk : ∀ c h, ¬ v = 1 → r.down g v = some c →
      ∃ x n, sub.levels c = some x ∧ denoteLs st.lss x = some n ∧ ls c h = some n)
    {x : LsIdx} (hx : Arena.Frontend.Olean.levelsIn pk r g v sub = some x) :
    ∃ n, r.levelsIn g v ls = some n ∧ denoteLs st.lss x = some n := by
  unfold Arena.Frontend.Olean.levelsIn at hx
  unfold Region.levelsIn
  by_cases hv : v = 1
  · simp only [hv, BEq.rfl, ↓reduceIte, Option.some.injEq] at hx ⊢
    subst hx
    exact ⟨_, rfl, hpk.nil⟩
  · simp only [hv, beq_iff_eq, ↓reduceIte] at hx ⊢
    split
    · rename_i c heq
      rw [heq] at hx
      obtain ⟨y, n, hy, hd, hn⟩ := hk c (Region.down_lt heq) hv heq
      simp only [hy, Option.some.injEq] at hx
      subst hx
      exact ⟨n, hn, hd⟩
    · rename_i hc
      rw [hc] at hx
      cases hx

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:94-98 Region.exprIn -/
theorem exprIn_sim {st : EStore} {r : Region} {g : Nat}
    {v : UInt64} {sub : Sub} {ex : (c : Nat) → c < g → Option Expr}
    (hk : ∀ c h, r.down g v = some c →
      ∃ x n, sub.expr c = some x ∧ denoteE st x = some n ∧ ex c h = some n)
    {x : EIdx} (hx : Arena.Frontend.Olean.exprIn r g v sub = some x) :
    ∃ n, r.exprIn g v ex = some n ∧ denoteE st x = some n := by
  unfold Arena.Frontend.Olean.exprIn at hx
  unfold Region.exprIn
  split
  · rename_i c heq
    rw [heq] at hx
    obtain ⟨y, n, hy, hd, hn⟩ := hk c (Region.down_lt heq) heq
    simp only [hy, Option.some.injEq] at hx
    subst hx
    exact ⟨n, hn, hd⟩
  · rename_i hc
    rw [hc] at hx
    cases hx

/-! ## The shapes of a run -/

theorem none_not_some {α : Type} {x : α} {s s' : AState}
    (h : (pure none : AM (Option α)) s = .ok (some x, s')) : False := by
  have := (AM.pure_ok h).1
  cases this

/-- A kid named by the kid table's entry. -/
theorem kid_of {r : Region} {k k' : UInt8} {g i : Nat} {nil : Bool}
    {fs : List (Nat × UInt8 × Bool)} (hf : r.fits g = true)
    (hfs : kidTable k (r.tag g) (r.nobjs g) = some fs) (hm : (i, k', nil) ∈ fs) {c : Nat}
    (hv : ¬ (nil = true ∧ r.fld g i = 1)) (hd : r.down g (r.fld g i) = some c) :
    Kid r k g k' c :=
  ⟨hf, fs, hfs, i, nil, hm, hv, hd⟩

/-- con-leche: none — `natWord` is the identity where it answers. -/
theorem natWord_run {k k' : Nat} {s s' : AState}
    (h : Arena.Frontend.Olean.natWord k s = .ok (k', s')) : k' = k ∧ s' = s := by
  unfold Arena.Frontend.Olean.natWord at h
  split at h
  · cases h
  · obtain ⟨h1, h2⟩ := AM.pure_ok h
    exact ⟨h1, h2⟩

/-! ## One `Name` -/

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:111-125 nameNode
The two arms after the parent, whatever the parent's read was: `t` the tag. -/
theorem nameTail_run {s s' : AState} (hok : StateOK s)
    {r : Region} {g t : Nat} {p : NIdx} {q : ConLeche.Name} (hp : denoteN s.store.ns p = some q)
    {h : NIdx} (hrun : Arena.Frontend.Olean.nameTail r g t p s = .ok (some h, s')) :
    ParseStep s s' ∧ ∃ n, denoteN s'.store.ns h = some n ∧
      ((t = 1 ∧ ∃ str, r.strP g (r.fld g 1) = some str ∧ n = .str q str) ∨
       (t ≠ 1 ∧ ∃ i, r.natP g (r.fld g 1) = some i ∧ n = .num q i)) := by
  generalize hF : Arena.Frontend.Olean.nameTail r g t p = f at hrun
  unfold Arena.Frontend.Olean.nameTail at hF
  by_cases ht : t = 1
  · subst ht
    simp only [BEq.rfl, ↓reduceIte] at hF
    split at hF
    · subst hF; exact (none_not_some hrun).elim
    · rename_i str hstr
      subst hF
      obtain ⟨y, s₁, hin, hrest⟩ := AM.bind_ok hrun
      obtain ⟨hv', hs⟩ := AM.pure_ok hrest
      cases hv'
      subst hs
      obtain ⟨hst, hd⟩ := internNNode_sstep hok (v := .str p str)
        (by intro c hc
            simp only [NNodeView.children, List.mem_singleton] at hc
            subst hc; exact nview_isSome_of_denote hp) hin
      refine ⟨hst.toParse', .str q str, ?_, .inl ⟨rfl, str, hstr, rfl⟩⟩
      rw [hd]
      simp only [denoteNView, denoteN_ext hp hst.ext, Option.map_some]
  · have hb : (t == 1) = false := by simpa using ht
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at hF
    split at hF
    · subst hF; exact (none_not_some hrun).elim
    · rename_i i hi
      subst hF
      obtain ⟨k, s₁, hw, hrest⟩ := AM.bind_ok hrun
      obtain ⟨hk1, hk2⟩ := natWord_run hw
      rw [hk1, hk2] at hrest
      obtain ⟨y, s₂, hin, hrest⟩ := AM.bind_ok hrest
      obtain ⟨hv', hs⟩ := AM.pure_ok hrest
      cases hv'
      subst hs
      obtain ⟨hst, hd⟩ := internNNode_sstep hok (v := .num p i)
        (by intro c hc
            simp only [NNodeView.children, List.mem_singleton] at hc
            subst hc; exact nview_isSome_of_denote hp) hin
      refine ⟨hst.toParse', .num q i, ?_, .inr ⟨ht, i, hi, rfl⟩⟩
      rw [hd]
      simp only [denoteNView, denoteN_ext hp hst.ext, Option.map_some]

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:111-125 nameNode -/
theorem nameNode_run {s s' : AState} (hok : StateOK s)
    {pk : OleanPins} (hpk : NullsRel s.store pk) {r : Region} {g : Nat} {sub : Sub}
    {ex : (c : Nat) → c < g → Option Expr} {nm : (c : Nat) → c < g → Option ConLeche.Name}
    {lv : (c : Nat) → c < g → Option Level} {ls : (c : Nat) → c < g → Option (List Level)}
    (hsub : SubRel s.store r kName g sub ex nm lv ls) {h : NIdx}
    (hrun : Arena.Frontend.Olean.nameNode pk r g sub s = .ok (some h, s')) :
    ParseStep s s' ∧ ∃ n, ConLeche.Frontend.Olean.nameNode r g nm = some n ∧
      denoteN s'.store.ns h = some n := by
  generalize hF : Arena.Frontend.Olean.nameNode pk r g sub = f at hrun
  unfold Arena.Frontend.Olean.nameNode at hF
  unfold ConLeche.Frontend.Olean.nameNode
  by_cases hf : r.fits g = true
  · simp only [hf, ↓reduceIte] at hF ⊢
    by_cases hc : ((r.tag g == 1 || r.tag g == 2) && r.nobjs g == 2) = true
    · simp only [hc, ↓reduceIte] at hF
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
      obtain ⟨htt, hn⟩ := hc
      have hfs : kidTable kName (r.tag g) (r.nobjs g) = some [(0, kName, true)] := by
        rcases htt with ht | ht <;>
          simp [ht, hn, ConLeche.Frontend.Olean.kidTable, ConLeche.Frontend.Olean.nameKids]
      split at hF
      · subst hF; exact (none_not_some hrun).elim
      · rename_i p hp
        subst hF
        obtain ⟨q, hq, hdq⟩ := nameIn_sim (nm := nm) hpk
          (fun c h hv hd => hsub.name c h (kid_of (nil := true) hf hfs (by simp) (by simpa using hv) hd)) hp
        obtain ⟨hst, n, hdn, ha⟩ := nameTail_run hok hdq hrun
        refine ⟨hst, n, ?_, hdn⟩
        rcases ha with ⟨ht1, str, hstr, rfl⟩ | ⟨ht1, i, hi, rfl⟩
        · simp [ht1, hn, hq, hstr]
        · have ht2 : r.tag g = 2 := by rcases htt with h | h; exact absurd h ht1; exact h
          simp [ht2, hn, hq, hi]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hF
      subst hF; exact (none_not_some hrun).elim
  · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hF
    subst hF; exact (none_not_some hrun).elim

/-! ## One `Level` -/

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:127-148 levelNode -/
theorem levelNode_run {s s' : AState} (hok : StateOK s)
    {pk : OleanPins} (hpk : NullsRel s.store pk) {r : Region} {g : Nat} {sub : Sub}
    {ex : (c : Nat) → c < g → Option Expr} {nm : (c : Nat) → c < g → Option ConLeche.Name}
    {lv : (c : Nat) → c < g → Option Level} {ls : (c : Nat) → c < g → Option (List Level)}
    (hsub : SubRel s.store r kLevel g sub ex nm lv ls) {h : LIdx}
    (hrun : Arena.Frontend.Olean.levelNode pk r g sub s = .ok (some h, s')) :
    ParseStep s s' ∧ ∃ u, ConLeche.Frontend.Olean.levelNode r g lv nm = some u ∧
      denoteL s'.store.ls h = some u := by
  have hL : ∀ {i : Nat} {fs}, r.fits g = true →
      kidTable kLevel (r.tag g) (r.nobjs g) = some fs → (i, kLevel, true) ∈ fs →
      ∀ {x : LIdx}, Arena.Frontend.Olean.levelIn pk r g (r.fld g i) sub = some x →
      ∃ n, r.levelIn g (r.fld g i) lv = some n ∧ denoteL s.store.ls x = some n :=
    fun hf hfs hm _ hx => levelIn_sim hpk
      (fun c h hv hd => hsub.level c h (kid_of hf hfs hm (by simpa using hv) hd)) hx
  generalize hF : Arena.Frontend.Olean.levelNode pk r g sub = f at hrun
  unfold Arena.Frontend.Olean.levelNode at hF
  unfold ConLeche.Frontend.Olean.levelNode
  by_cases hf : r.fits g = true
  · simp only [hf, ↓reduceIte] at hF ⊢
    generalize ht : r.tag g = t at hF ⊢
    generalize hn : r.nobjs g = n at hF ⊢
    have hkt : ∀ {a b fs}, ConLeche.Frontend.Olean.levelKids a b = some fs → t = a → n = b →
        kidTable kLevel (r.tag g) (r.nobjs g) = some fs := by
      intro a b fs hfs h1 h2
      rw [ht, hn, h1, h2]; exact hfs
    split at hF
    · -- zero
      subst hF
      obtain ⟨hv, hs⟩ := AM.pure_ok hrun
      cases hv
      subst hs
      exact ⟨ParseStep.refl hok, .zero, rfl, hpk.zero⟩
    · -- succ
      split at hF
      · subst hF; exact (none_not_some hrun).elim
      · rename_i x hx
        subst hF
        obtain ⟨u, hu, hdu⟩ := hL hf (hkt (a := 1) (b := 1) rfl rfl rfl) (by simp) hx
        obtain ⟨y, s₁, hin, hrest⟩ := AM.bind_ok hrun
        obtain ⟨hv', hs⟩ := AM.pure_ok hrest
        cases hv'
        subst hs
        obtain ⟨hst, hd⟩ := internLNode_sstep hok
          (⟨by intro c hc
               simp only [LNodeView.lchildren, List.mem_singleton] at hc
               subst hc; exact lview_isSome_of_denote hdu,
            by intro c hc; simp only [LNodeView.nchildren] at hc; exact absurd hc (by simp)⟩) hin
        refine ⟨hst.toParse', .succ u, by simp [hu], ?_⟩
        rw [hd]
        simp only [denoteLView, denoteL_ext hdu hst.ext, Option.map_some]
    · -- max
      split at hF
      · rename_i x y hx hy
        subst hF
        obtain ⟨u, hu, hdu⟩ := hL hf (hkt (a := 2) (b := 2) rfl rfl rfl) (by simp) hx
        obtain ⟨v, hv, hdv⟩ := hL hf (hkt (a := 2) (b := 2) rfl rfl rfl) (by simp) hy
        obtain ⟨y', s₁, hin, hrest⟩ := AM.bind_ok hrun
        obtain ⟨hv', hs⟩ := AM.pure_ok hrest
        cases hv'
        subst hs
        obtain ⟨hst, hd⟩ := internLNode_sstep hok (v := .max x y)
          (⟨by intro c hc
               simp only [LNodeView.lchildren, List.mem_cons, List.not_mem_nil, or_false] at hc
               rcases hc with rfl | rfl
               · exact lview_isSome_of_denote hdu
               · exact lview_isSome_of_denote hdv,
            by intro c hc; simp only [LNodeView.nchildren] at hc; exact absurd hc (by simp)⟩) hin
        refine ⟨hst.toParse', .max u v, by simp [hu, hv], ?_⟩
        rw [hd]
        simp only [denoteLView, opt2_eq_some_iff]
        exact ⟨u, v, denoteL_ext hdu hst.ext, denoteL_ext hdv hst.ext, rfl⟩
      · subst hF; exact (none_not_some hrun).elim
    · -- imax
      split at hF
      · rename_i x y hx hy
        subst hF
        obtain ⟨u, hu, hdu⟩ := hL hf (hkt (a := 3) (b := 2) rfl rfl rfl) (by simp) hx
        obtain ⟨v, hv, hdv⟩ := hL hf (hkt (a := 3) (b := 2) rfl rfl rfl) (by simp) hy
        obtain ⟨y', s₁, hin, hrest⟩ := AM.bind_ok hrun
        obtain ⟨hv', hs⟩ := AM.pure_ok hrest
        cases hv'
        subst hs
        obtain ⟨hst, hd⟩ := internLNode_sstep hok (v := .imax x y)
          (⟨by intro c hc
               simp only [LNodeView.lchildren, List.mem_cons, List.not_mem_nil, or_false] at hc
               rcases hc with rfl | rfl
               · exact lview_isSome_of_denote hdu
               · exact lview_isSome_of_denote hdv,
            by intro c hc; simp only [LNodeView.nchildren] at hc; exact absurd hc (by simp)⟩) hin
        refine ⟨hst.toParse', .imax u v, by simp [hu, hv], ?_⟩
        rw [hd]
        simp only [denoteLView, opt2_eq_some_iff]
        exact ⟨u, v, denoteL_ext hdu hst.ext, denoteL_ext hdv hst.ext, rfl⟩
      · subst hF; exact (none_not_some hrun).elim
    · -- param
      split at hF
      · subst hF; exact (none_not_some hrun).elim
      · rename_i x hx
        subst hF
        obtain ⟨q, hq, hdq⟩ := nameIn_sim (nm := nm) hpk
          (fun c h hv hd => hsub.name c h
            (kid_of (nil := true) hf (hkt (a := 4) (b := 1) rfl rfl rfl) (by simp) (by simpa using hv) hd)) hx
        obtain ⟨y, s₁, hin, hrest⟩ := AM.bind_ok hrun
        obtain ⟨hv', hs⟩ := AM.pure_ok hrest
        cases hv'
        subst hs
        obtain ⟨hst, hd⟩ := internLNode_sstep hok
          (⟨by intro c hc; simp only [LNodeView.lchildren] at hc; exact absurd hc (by simp),
            by intro c hc
               simp only [LNodeView.nchildren, List.mem_singleton] at hc
               subst hc; exact nview_isSome_of_denote hdq⟩) hin
        refine ⟨hst.toParse', .param q, by simp [hq], ?_⟩
        rw [hd]
        have hdq2 : denoteN s'.store.ls.ns x = some q := denoteN_ext hdq hst.ext
        simp only [denoteLView, hdq2, Option.map_some]
    · subst hF; exact (none_not_some hrun).elim
  · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hF
    subst hF; exact (none_not_some hrun).elim

/-! ## One `List Level` cell -/

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:150-160 levelsNode -/
theorem levelsNode_run {s s' : AState} (hok : StateOK s)
    {pk : OleanPins} (hpk : NullsRel s.store pk) {r : Region} {g : Nat} {sub : Sub}
    {ex : (c : Nat) → c < g → Option Expr} {nm : (c : Nat) → c < g → Option ConLeche.Name}
    {lv : (c : Nat) → c < g → Option Level} {ls : (c : Nat) → c < g → Option (List Level)}
    (hsub : SubRel s.store r kLevels g sub ex nm lv ls) {h : LsIdx}
    (hrun : Arena.Frontend.Olean.levelsNode pk r g sub s = .ok (some h, s')) :
    ParseStep s s' ∧ ∃ us, ConLeche.Frontend.Olean.levelsNode r g ls lv = some us ∧
      denoteLs s'.store.lss h = some us := by
  generalize hF : Arena.Frontend.Olean.levelsNode pk r g sub = f at hrun
  unfold Arena.Frontend.Olean.levelsNode at hF
  unfold ConLeche.Frontend.Olean.levelsNode
  by_cases hf : r.fits g = true
  · simp only [hf, ↓reduceIte] at hF ⊢
    by_cases hc : (r.tag g == 1 && r.nobjs g == 2) = true
    · simp only [hc, ↓reduceIte] at hF
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨ht, hn⟩ := hc
      have hfs : kidTable kLevels (r.tag g) (r.nobjs g)
          = some [(0, kLevel, true), (1, kLevels, true)] := by
        rw [ht, hn]; rfl
      split at hF
      · rename_i x y hx hy
        subst hF
        obtain ⟨u, hu, hdu⟩ := levelIn_sim (lv := lv) hpk
          (fun c h hv hd => hsub.level c h
            (kid_of (nil := true) hf hfs (by simp) (by simpa using hv) hd)) hx
        obtain ⟨us, hus, hdus⟩ := levelsIn_sim (ls := ls) hpk
          (fun c h hv hd => hsub.levels c h
            (kid_of (nil := true) hf hfs (by simp) (by simpa using hv) hd)) hy
        rw [Arena.Frontend.Olean.levelsCons] at hrun
        obtain ⟨rest, s₁, hview, hrest⟩ := AM.bind_ok hrun
        obtain ⟨hs1, hv⟩ := AM.of_run (P := fun t => t = s) rfl hview (viewLs_spec s y)
        rw [hs1] at hrest
        have hdl : denoteLList s.store.ls rest = some us := by
          unfold denoteLs at hdus
          rw [hv] at hdus
          exact hdus
        have hdc : denoteLList s.store.ls (x :: rest) = some (u :: us) := by
          simp only [denoteLList, hdu, hdl]; rfl
        obtain ⟨y', s₂, hin, hrest⟩ := AM.bind_ok hrest
        obtain ⟨hv', hs⟩ := AM.pure_ok hrest
        cases hv'
        subst hs
        obtain ⟨hst, hd⟩ := internLsNode_sstep hok
          (lsViewOK_of_denoteLList (st := s.store) _ _ hdc) hin
        refine ⟨hst.toParse', u :: us, by simp [ht, hn, hu, hus], ?_⟩
        rw [hd]
        exact denoteLList_ext hst.ext.lss.ls _ _ hdc
      · subst hF; exact (none_not_some hrun).elim
    · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hF
      subst hF; exact (none_not_some hrun).elim
  · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hF
    subst hF; exact (none_not_some hrun).elim

/-! ## One `Expr` -/

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:162-206 exprNode — one node interned,
its view denoting. -/
theorem internE_some {s s' : AState} (hok : StateOK s)
    {v : ENodeView} (hv : s.store.ViewOK v) {e : Expr}
    (hd : ∀ t : EStore, Ext s.store t → denoteEView t v = some e) {h : EIdx}
    (hrun : (internE v >>= fun x => pure (some x)) s = .ok (some h, s')) :
    ParseStep s s' ∧ denoteE s'.store h = some e := by
  obtain ⟨y, s₁, hin, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hv', hs⟩ := AM.pure_ok hrest
  cases hv'
  subst hs
  obtain ⟨hst, hden⟩ := internE_sstep hok hv hin
  exact ⟨hst.toParse', by rw [hden]; exact hd _ hst.ext⟩

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:162-206 exprNode -/
theorem exprNode_run {s s' : AState} (hok : StateOK s)
    {pk : OleanPins} (hpk : NullsRel s.store pk) {r : Region} {g : Nat} {sub : Sub}
    {ex : (c : Nat) → c < g → Option Expr} {nm : (c : Nat) → c < g → Option ConLeche.Name}
    {lv : (c : Nat) → c < g → Option Level} {ls : (c : Nat) → c < g → Option (List Level)}
    (hsub : SubRel s.store r kExpr g sub ex nm lv ls) {h : EIdx}
    (hrun : Arena.Frontend.Olean.exprNode pk r g sub s = .ok (some h, s')) :
    ParseStep s s' ∧ ∃ e, ConLeche.Frontend.Olean.exprNode r g ex nm lv ls = some e ∧
      denoteE s'.store h = some e := by
  have hE : ∀ {i : Nat} {fs}, r.fits g = true →
      kidTable kExpr (r.tag g) (r.nobjs g) = some fs → (i, kExpr, false) ∈ fs →
      ∀ {x : EIdx}, Arena.Frontend.Olean.exprIn r g (r.fld g i) sub = some x →
      ∃ n, r.exprIn g (r.fld g i) ex = some n ∧ denoteE s.store x = some n :=
    fun hf hfs hm _ hx => exprIn_sim
      (fun c h hd => hsub.expr c h (kid_of (nil := false) hf hfs hm (by simp) hd)) hx
  have hN : ∀ {i : Nat} {fs}, r.fits g = true →
      kidTable kExpr (r.tag g) (r.nobjs g) = some fs → (i, kName, true) ∈ fs →
      ∀ {x : NIdx}, Arena.Frontend.Olean.nameIn pk r g (r.fld g i) sub = some x →
      ∃ n, r.nameIn g (r.fld g i) nm = some n ∧ denoteN s.store.ns x = some n :=
    fun hf hfs hm _ hx => nameIn_sim hpk
      (fun c h hv hd => hsub.name c h (kid_of (nil := true) hf hfs hm (by simpa using hv) hd)) hx
  generalize hF : Arena.Frontend.Olean.exprNode pk r g sub = f at hrun
  unfold Arena.Frontend.Olean.exprNode at hF
  unfold ConLeche.Frontend.Olean.exprNode
  by_cases hf : r.fits g = true
  · simp only [hf, ↓reduceIte] at hF ⊢
    generalize ht : r.tag g = t at hF ⊢
    generalize hn : r.nobjs g = n at hF ⊢
    have hkt : ∀ {a b fs}, ConLeche.Frontend.Olean.exprKids a b = some fs → t = a → n = b →
        kidTable kExpr (r.tag g) (r.nobjs g) = some fs := by
      intro a b fs hfs h1 h2
      rw [ht, hn, h1, h2]; exact hfs
    split at hF
    · -- bvar
      split at hF
      · subst hF; exact (none_not_some hrun).elim
      · rename_i i hi
        subst hF
        obtain ⟨k, s₁, hw, hrest⟩ := AM.bind_ok hrun
        obtain ⟨hk1, hk2⟩ := natWord_run hw
        rw [hk1, hk2] at hrest
        obtain ⟨hst, hd⟩ := internE_some (e := .bvar i) hok viewOK_bvar (fun _ _ => rfl) hrest
        exact ⟨hst, .bvar i, by simp [hi], hd⟩
    · -- sort
      split at hF
      · subst hF; exact (none_not_some hrun).elim
      · rename_i x hx
        subst hF
        obtain ⟨u, hu, hdu⟩ := levelIn_sim (lv := lv) hpk
          (fun c h hv hd => hsub.level c h
            (kid_of (nil := true) hf (hkt (a := 3) (b := 1) rfl rfl rfl) (by simp)
              (by simpa using hv) hd)) hx
        obtain ⟨hst, hd⟩ := internE_some (e := .sort u) hok
          (viewOK_sort (lview_isSome_of_denote hdu))
          (fun t hx' => by
            have := denoteL_ext hdu hx'
            simp only [denoteEView, this, Option.map_some]) hrun
        exact ⟨hst, .sort u, by simp [hu], hd⟩
    · -- const
      split at hF
      · rename_i x y hx hy
        subst hF
        obtain ⟨q, hq, hdq⟩ := hN hf (hkt (a := 4) (b := 2) rfl rfl rfl) (by simp) hx
        obtain ⟨us, hus, hdus⟩ := levelsIn_sim (ls := ls) hpk
          (fun c h hv hd => hsub.levels c h
            (kid_of (nil := true) hf (hkt (a := 4) (b := 2) rfl rfl rfl) (by simp)
              (by simpa using hv) hd)) hy
        obtain ⟨hst, hd⟩ := internE_some (e := .const q us) hok
          (viewOK_const (nview_isSome_of_denote hdq)
            (by obtain ⟨w, hw, -⟩ := Arena.denoteLs_view hdus; rw [hw]; rfl))
          (fun t hx' => by
            simp only [denoteEView, opt2_eq_some_iff]
            exact ⟨q, us, denoteN_ext hdq hx', denoteLs_ext hdus hx', rfl⟩) hrun
        exact ⟨hst, .const q us, by simp [hq, hus], hd⟩
      · subst hF; exact (none_not_some hrun).elim
    · -- app
      split at hF
      · rename_i x y hx hy
        subst hF
        obtain ⟨a, ha, hda⟩ := hE hf (hkt (a := 5) (b := 2) rfl rfl rfl) (by simp) hx
        obtain ⟨b, hb, hdb⟩ := hE hf (hkt (a := 5) (b := 2) rfl rfl rfl) (by simp) hy
        obtain ⟨hst, hd⟩ := internE_some (e := .app a b) hok
          (viewOK_app (by rw [hda]; rfl) (by rw [hdb]; rfl))
          (fun t hx' => by
            simp only [denoteEView, opt2_eq_some_iff]
            exact ⟨a, b, denote_ext hda hx', denote_ext hdb hx', rfl⟩) hrun
        exact ⟨hst, .app a b, by simp [ha, hb], hd⟩
      · subst hF; exact (none_not_some hrun).elim
    · -- lam
      split at hF
      · rename_i x y hx hy
        subst hF
        obtain ⟨a, ha, hda⟩ := hE hf (hkt (a := 6) (b := 3) rfl rfl rfl) (by simp) hx
        obtain ⟨b, hb, hdb⟩ := hE hf (hkt (a := 6) (b := 3) rfl rfl rfl) (by simp) hy
        obtain ⟨hst, hd⟩ := internE_some (e := .lam a b) hok
          (viewOK_lam (by rw [hda]; rfl) (by rw [hdb]; rfl))
          (fun t hx' => by
            simp only [denoteEView, opt2_eq_some_iff]
            exact ⟨a, b, denote_ext hda hx', denote_ext hdb hx', rfl⟩) hrun
        exact ⟨hst, .lam a b, by simp [ha, hb], hd⟩
      · subst hF; exact (none_not_some hrun).elim
    · -- forall
      split at hF
      · rename_i x y hx hy
        subst hF
        obtain ⟨a, ha, hda⟩ := hE hf (hkt (a := 7) (b := 3) rfl rfl rfl) (by simp) hx
        obtain ⟨b, hb, hdb⟩ := hE hf (hkt (a := 7) (b := 3) rfl rfl rfl) (by simp) hy
        obtain ⟨hst, hd⟩ := internE_some (e := .forallE a b) hok
          (viewOK_forallE (by rw [hda]; rfl) (by rw [hdb]; rfl))
          (fun t hx' => by
            simp only [denoteEView, opt2_eq_some_iff]
            exact ⟨a, b, denote_ext hda hx', denote_ext hdb hx', rfl⟩) hrun
        exact ⟨hst, .forallE a b, by simp [ha, hb], hd⟩
      · subst hF; exact (none_not_some hrun).elim
    · -- let
      split at hF
      · rename_i x y z hx hy hz
        subst hF
        obtain ⟨a, ha, hda⟩ := hE hf (hkt (a := 8) (b := 4) rfl rfl rfl) (by simp) hx
        obtain ⟨b, hb, hdb⟩ := hE hf (hkt (a := 8) (b := 4) rfl rfl rfl) (by simp) hy
        obtain ⟨c, hc, hdc⟩ := hE hf (hkt (a := 8) (b := 4) rfl rfl rfl) (by simp) hz
        obtain ⟨hst, hd⟩ := internE_some (e := .letE a b c) hok
          (viewOK_letE (by rw [hda]; rfl) (by rw [hdb]; rfl) (by rw [hdc]; rfl))
          (fun t hx' => by
            simp only [denoteEView, opt3_eq_some_iff]
            exact ⟨a, b, c, denote_ext hda hx', denote_ext hdb hx', denote_ext hdc hx', rfl⟩) hrun
        exact ⟨hst, .letE a b c, by simp [ha, hb, hc], hd⟩
      · subst hF; exact (none_not_some hrun).elim
    · -- lit
      split at hF
      · subst hF; exact (none_not_some hrun).elim
      · rename_i l hl
        subst hF
        obtain ⟨hst, hd⟩ := internE_some (e := .lit l) hok viewOK_lit (fun _ _ => rfl) hrun
        refine ⟨hst, .lit l, ?_, hd⟩
        simp only [Arena.Frontend.Olean.litP] at hl
        simp [hl]
    · -- mdata
      subst hF
      obtain ⟨hv, hs⟩ := AM.pure_ok hrun
      subst hs
      obtain ⟨b, hb, hdb⟩ := hE hf (hkt (a := 10) (b := 2) rfl rfl rfl) (by simp) hv.symm
      exact ⟨ParseStep.refl hok, b, hb, hdb⟩
    · -- proj
      split at hF
      · subst hF; exact (none_not_some hrun).elim
      · rename_i x hx
        split at hF
        · subst hF; exact (none_not_some hrun).elim
        · rename_i i hi
          subst hF
          obtain ⟨q, hq, hdq⟩ := hN hf (hkt (a := 11) (b := 3) rfl rfl rfl) (by simp) hx
          obtain ⟨k, s₁, hw, hrest⟩ := AM.bind_ok hrun
          obtain ⟨hk1, hk2⟩ := natWord_run hw
          rw [hk1, hk2] at hrest
          cases hy : Arena.Frontend.Olean.exprIn r g (r.fld g 2) sub with
          | none =>
            simp only [hy] at hrest
            exact (none_not_some hrest).elim
          | some y =>
            simp only [hy] at hrest
            obtain ⟨b, hb, hdb⟩ := hE hf (hkt (a := 11) (b := 3) rfl rfl rfl) (by simp) hy
            obtain ⟨hst, hd⟩ := internE_some (e := .proj q i b) hok
              (viewOK_proj (nview_isSome_of_denote hdq) (by rw [hdb]; rfl))
              (fun t hx' => by
                simp only [denoteEView, opt2_eq_some_iff]
                exact ⟨q, b, denoteN_ext hdq hx', denote_ext hdb hx', rfl⟩) hrest
            exact ⟨hst, .proj q i b, by simp [hq, hi, hb], hd⟩
    · subst hF; exact (none_not_some hrun).elim
  · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hF
    subst hF; exact (none_not_some hrun).elim

/-! ## `nameAt`, `nameP`: a `Name` is read by its recursion -/

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:210-213 nameAt -/
theorem nameAt_run {r : Region} {pk : OleanPins} : ∀ (g : Nat) {s s' : AState},
    StateOK s → NullsRel s.store pk → ∀ {h : NIdx},
    Arena.Frontend.Olean.nameAt pk r g s = .ok (some h, s') →
    ParseStep s s' ∧ ∃ n, ConLeche.Frontend.Olean.nameAt r g = some n ∧
      denoteN s'.store.ns h = some n := by
  intro g
  induction g using Nat.strongRecOn with
  | _ g ih =>
    intro s s' hok hpk h hrun
    rw [Arena.Frontend.Olean.nameAt] at hrun
    rw [ConLeche.Frontend.Olean.nameAt, ConLeche.Frontend.Olean.nameNode]
    generalize hF : (if r.fits g = true then _ else _ : AM (Option NIdx)) = f at hrun
    by_cases hf : r.fits g = true
    · simp only [hf, ↓reduceIte] at hF ⊢
      by_cases hc : ((r.tag g == 1 || r.tag g == 2) && r.nobjs g == 2) = true
      · simp only [hc, ↓reduceIte] at hF
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
        obtain ⟨htt, hn⟩ := hc
        have hend : ∀ {q : ConLeche.Name} {y : NIdx} {t : AState},
            r.nameIn g (r.fld g 0) (fun c _ => ConLeche.Frontend.Olean.nameAt r c) = some q →
            denoteN t.store.ns y = some q → StateOK t →
            ParseStep s t →
            Arena.Frontend.Olean.nameTail r g (r.tag g) y t = .ok (some h, s') →
            ParseStep s s' ∧ ∃ n, (match r.tag g, r.nobjs g with
              | 1, 2 => (do
                  let p ← r.nameIn g (r.fld g 0) fun c _ => ConLeche.Frontend.Olean.nameAt r c
                  let s ← r.strP g (r.fld g 1)
                  pure (ConLeche.Name.str p s))
              | 2, 2 => (do
                  let p ← r.nameIn g (r.fld g 0) fun c _ => ConLeche.Frontend.Olean.nameAt r c
                  let i ← r.natP g (r.fld g 1)
                  pure (ConLeche.Name.num p i))
              | _, _ => none) = some n ∧ denoteN s'.store.ns h = some n := by
          intro q y t hq hdy hokt hstep htail
          obtain ⟨hst, n, hdn, ha⟩ := nameTail_run hokt hdy htail
          refine ⟨hstep.trans hst, n, ?_, hdn⟩
          rcases ha with ⟨ht1, str, hstr, rfl⟩ | ⟨ht1, i, hi, rfl⟩
          · simp [ht1, hn, hq, hstr]
          · have ht2 : r.tag g = 2 := by rcases htt with h | h; exact absurd h ht1; exact h
            simp [ht2, hn, hq, hi]
        by_cases hv : (r.fld g 0 == 1) = true
        · simp only [hv, ↓reduceIte] at hF
          subst hF
          exact hend (q := .anonymous) (by simp [Region.nameIn, hv]) hpk.anon hok
            (ParseStep.refl hok) hrun
        · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hF
          have hv' : ¬ r.fld g 0 = 1 := by simpa using hv
          split at hF
          · subst hF; exact (none_not_some hrun).elim
          · rename_i c heq
            subst hF
            obtain ⟨o, s₁, hat, hrest⟩ := AM.bind_ok hrun
            cases o with
            | none => exact (none_not_some hrest).elim
            | some p =>
              obtain ⟨hst, q, hq, hdp⟩ := ih c (Region.down_lt heq) hok hpk hat
              refine hend (q := q) ?_ hdp hst.ok hst hrest
              simp only [Region.nameIn, hv', beq_iff_eq, ↓reduceIte]
              split
              · rename_i c' heq'
                rw [heq] at heq'
                cases heq'
                exact hq
              · rename_i hne
                rw [heq] at hne
                cases hne
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hF
        subst hF; exact (none_not_some hrun).elim
    · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hF
      subst hF; exact (none_not_some hrun).elim

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:231-236 nameP -/
theorem nameP_run {r : Region} {pk : OleanPins} {v : UInt64} {s s' : AState}
    (hok : StateOK s) (hpk : NullsRel s.store pk) {h : NIdx}
    (hrun : Arena.Frontend.Olean.nameP pk r v s = .ok (some h, s')) :
    ParseStep s s' ∧ ∃ n, ConLeche.Frontend.Olean.nameP r v = some n ∧
      denoteN s'.store.ns h = some n := by
  generalize hF : Arena.Frontend.Olean.nameP pk r v = f at hrun
  unfold Arena.Frontend.Olean.nameP at hF
  unfold ConLeche.Frontend.Olean.nameP
  by_cases hv : (v == 1) = true
  · simp only [hv, ↓reduceIte] at hF ⊢
    subst hF
    obtain ⟨hh, hs⟩ := AM.pure_ok hrun
    cases hh
    subst hs
    exact ⟨ParseStep.refl hok, _, rfl, hpk.anon⟩
  · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hF ⊢
    split at hF
    · rename_i c hc
      subst hF
      rw [hc]
      exact nameAt_run c hok hpk hrun
    · subst hF; exact (none_not_some hrun).elim

end ConRon.Bridge.Frontend.Olean

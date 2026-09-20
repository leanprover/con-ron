/-
# Experiment D's layer: a denotation *on the Aeneas state*

DESIGN §8.6's experiment D is the one-layer alternative: the Aeneas model of
`crates/arena-spike` against con-leche's pure `instantiate1`, with **no twin
in between**.  So the denotation has to be defined on `Generated.State`
directly — over `alloc.vec.Vec` and `Std.U32`, not over `MState`'s `List`s
and `Nat`s — and no statement or proof in this module or in `ExpD.lean`
mentions `MState`, `absState` or `mInstantiate1`.

What it *does* reuse from `MiniAbs.lean` is the machine-word arithmetic —
`abs_tag`, `abs_idx`, `abs_cast_usize`, `abs_cast_u32`, `abs_mk`,
`usize_succ`, `vec_push_inv`, and the capacity invariant `GWF`.  None of
those mentions the twin; they are the lemmas *any* proof about this Rust has
to have, and the round-2 report counts them once and charges them to both
routes.

The module is otherwise a transcription of `MiniSpecs.lean` into the Aeneas
types, and the transcription *is* the measurement.
-/
import ConRon.Arena.Spike.MiniAbs

namespace ConRon.Arena.Spike

open ConLeche Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-! ## The views, on the Aeneas state

The three tag constants and `mIdxCap` are shared with `Mini.lean` — they are
literally `0`, `1`, `2` and `2^28`, the Rust's own `const`s, and duplicating
them would make the comparison less honest, not more.  Nothing else here
comes from the twin. -/

theorem gtag_bvar_ne_app : ¬ (mTagApp = mTagBvar) := by decide
theorem gtag_bvar_ne_lam : ¬ (mTagLam = mTagBvar) := by decide
theorem gtag_app_ne_lam : ¬ (mTagLam = mTagApp) := by decide

/-- con-leche: none — `crates/arena-spike/src/lib.rs:32` tag_of, as a Lean
function of the machine word. -/
def gTagOf (h : U32) : Nat := h.val / mIdxCap

/-- con-leche: none — `crates/arena-spike/src/lib.rs:37` idx_of. -/
def gIdxOf (h : U32) : Nat := h.val % mIdxCap

/-- con-leche: none — `crates/arena-spike/src/lib.rs:92` view_bvar. -/
def gViewBvar (st : Generated.State) (h : U32) : Option U32 :=
  if gTagOf h = mTagBvar then st.bvars.val[gIdxOf h]? else none

/-- con-leche: none — `crates/arena-spike/src/lib.rs:106` view_app. -/
def gViewApp (st : Generated.State) (h : U32) : Option (U32 × U32) :=
  if gTagOf h = mTagApp then (st.apps.val[gIdxOf h]?).map (fun n => (n.f, n.a)) else none

/-- con-leche: none — `crates/arena-spike/src/lib.rs:120` view_lam. -/
def gViewLam (st : Generated.State) (h : U32) : Option (U32 × U32) :=
  if gTagOf h = mTagLam then (st.lams.val[gIdxOf h]?).map (fun n => (n.ty, n.body)) else none

theorem gViewBvar_tag {st : Generated.State} {h i : U32}
    (hv : gViewBvar st h = some i) : gTagOf h = mTagBvar := by
  simp only [gViewBvar] at hv; split at hv
  · assumption
  · simp at hv

theorem gViewApp_tag {st : Generated.State} {h : U32} {p : U32 × U32}
    (hv : gViewApp st h = some p) : gTagOf h = mTagApp := by
  simp only [gViewApp] at hv; split at hv
  · assumption
  · simp at hv

theorem gViewLam_tag {st : Generated.State} {h : U32} {p : U32 × U32}
    (hv : gViewLam st h = some p) : gTagOf h = mTagLam := by
  simp only [gViewLam] at hv; split at hv
  · assumption
  · simp at hv

/-! ## The Rust's `view_*` computes them

One lemma per primitive; this is where D pays C1's `u32` arithmetic, inside
the denotation layer rather than beside it. -/

theorem gview_bvar (st : Generated.State) (h : U32) :
    Generated.view_bvar st h = .ok (gViewBvar st h) := by
  obtain ⟨t, ht, htv⟩ := abs_tag h
  obtain ⟨i, hi, hiv⟩ := abs_idx h
  obtain ⟨j, hj, hjv⟩ := abs_cast_usize i
  have hjv' : j.val = gIdxOf h := by rw [hjv]; exact hiv
  unfold Generated.view_bvar gViewBvar
  simp only [ht, hi, hj, bind_tc_ok, alloc.vec.Vec.index_slice_index]
  by_cases hteq : t = Generated.TAG_BVAR
  · have hm : gTagOf h = mTagBvar := by
      show mTagOf (absU h) = mTagBvar
      rw [← htv, ← tagbvar, hteq]
    rw [if_pos hteq, if_pos hm]
    by_cases hlt : j < alloc.vec.Vec.len st.bvars
    · have hb : j.val < st.bvars.val.length := by simpa using hlt
      obtain ⟨x, hx1, hx2⟩ :=
        spec_imp_exists (alloc.vec.Vec.index_usize_spec st.bvars j (by simpa using hb))
      rw [if_pos hlt, hx1, bind_tc_ok, ← hjv', List.getElem?_eq_getElem hb, hx2]
    · have hb : st.bvars.val.length ≤ j.val := by simpa using hlt
      rw [if_neg hlt, ← hjv', List.getElem?_eq_none hb]
  · have hm : ¬ (gTagOf h = mTagBvar) := by
      show ¬ (mTagOf (absU h) = mTagBvar)
      rw [← htv, ← tagbvar, absU_eq]; exact hteq
    rw [if_neg hteq, if_neg hm]

theorem gview_app (st : Generated.State) (h : U32) :
    Generated.view_app st h = .ok (gViewApp st h) := by
  obtain ⟨t, ht, htv⟩ := abs_tag h
  obtain ⟨i, hi, hiv⟩ := abs_idx h
  obtain ⟨j, hj, hjv⟩ := abs_cast_usize i
  have hjv' : j.val = gIdxOf h := by rw [hjv]; exact hiv
  unfold Generated.view_app gViewApp
  simp only [ht, hi, hj, bind_tc_ok, alloc.vec.Vec.index_slice_index]
  by_cases hteq : t = Generated.TAG_APP
  · have hm : gTagOf h = mTagApp := by
      show mTagOf (absU h) = mTagApp
      rw [← htv, ← tagapp, hteq]
    rw [if_pos hteq, if_pos hm]
    by_cases hlt : j < alloc.vec.Vec.len st.apps
    · have hb : j.val < st.apps.val.length := by simpa using hlt
      obtain ⟨x, hx1, hx2⟩ :=
        spec_imp_exists (alloc.vec.Vec.index_usize_spec st.apps j (by simpa using hb))
      rw [if_pos hlt, hx1, bind_tc_ok, ← hjv', List.getElem?_eq_getElem hb, hx2]
      rfl
    · have hb : st.apps.val.length ≤ j.val := by simpa using hlt
      rw [if_neg hlt, ← hjv', List.getElem?_eq_none hb]
      rfl
  · have hm : ¬ (gTagOf h = mTagApp) := by
      show ¬ (mTagOf (absU h) = mTagApp)
      rw [← htv, ← tagapp, absU_eq]; exact hteq
    rw [if_neg hteq, if_neg hm]

theorem gview_lam (st : Generated.State) (h : U32) :
    Generated.view_lam st h = .ok (gViewLam st h) := by
  obtain ⟨t, ht, htv⟩ := abs_tag h
  obtain ⟨i, hi, hiv⟩ := abs_idx h
  obtain ⟨j, hj, hjv⟩ := abs_cast_usize i
  have hjv' : j.val = gIdxOf h := by rw [hjv]; exact hiv
  unfold Generated.view_lam gViewLam
  simp only [ht, hi, hj, bind_tc_ok, alloc.vec.Vec.index_slice_index]
  by_cases hteq : t = Generated.TAG_LAM
  · have hm : gTagOf h = mTagLam := by
      show mTagOf (absU h) = mTagLam
      rw [← htv, ← taglam, hteq]
    rw [if_pos hteq, if_pos hm]
    by_cases hlt : j < alloc.vec.Vec.len st.lams
    · have hb : j.val < st.lams.val.length := by simpa using hlt
      obtain ⟨x, hx1, hx2⟩ :=
        spec_imp_exists (alloc.vec.Vec.index_usize_spec st.lams j (by simpa using hb))
      rw [if_pos hlt, hx1, bind_tc_ok, ← hjv', List.getElem?_eq_getElem hb, hx2]
      rfl
    · have hb : st.lams.val.length ≤ j.val := by simpa using hlt
      rw [if_neg hlt, ← hjv', List.getElem?_eq_none hb]
      rfl
  · have hm : ¬ (gTagOf h = mTagLam) := by
      show ¬ (mTagOf (absU h) = mTagLam)
      rw [← htv, ← taglam, absU_eq]; exact hteq
    rw [if_neg hteq, if_neg hm]


/-! ## The extension order -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt (the `Ext` conjunct) — the
arena only grows, and only at the end of each `Vec`. -/
structure GExt (st st' : Generated.State) : Prop where
  bvars : ∃ l, st'.bvars.val = st.bvars.val ++ l
  apps : ∃ l, st'.apps.val = st.apps.val ++ l
  lams : ∃ l, st'.lams.val = st.lams.val ++ l

theorem GExt.refl (st : Generated.State) : GExt st st :=
  ⟨⟨[], by simp⟩, ⟨[], by simp⟩, ⟨[], by simp⟩⟩

theorem GExt.trans {a b c : Generated.State} (h1 : GExt a b) (h2 : GExt b c) : GExt a c := by
  obtain ⟨⟨l1, e1⟩, ⟨m1, f1⟩, ⟨n1, g1⟩⟩ := h1
  obtain ⟨⟨l2, e2⟩, ⟨m2, f2⟩, ⟨n2, g2⟩⟩ := h2
  exact ⟨⟨l1 ++ l2, by rw [e2, e1, List.append_assoc]⟩,
         ⟨m1 ++ m2, by rw [f2, f1, List.append_assoc]⟩,
         ⟨n1 ++ n2, by rw [g2, g1, List.append_assoc]⟩⟩

theorem gprefix_getElem {α : Type} {l l' m : List α} {i : Nat} {x : α}
    (hl : l' = l ++ m) (h : l[i]? = some x) : l'[i]? = some x := by
  subst hl
  have hi : i < l.length := by
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp h
    exact hlt
  rw [List.getElem?_append_left hi]; exact h

theorem GExt.viewBvar {st st' : Generated.State} (hx : GExt st st') {h i : U32}
    (hv : gViewBvar st h = some i) : gViewBvar st' h = some i := by
  obtain ⟨l, hl⟩ := hx.bvars
  simp only [gViewBvar] at hv ⊢
  split at hv
  · rename_i ht; rw [if_pos ht]; exact gprefix_getElem hl hv
  · simp at hv

theorem GExt.viewApp {st st' : Generated.State} (hx : GExt st st') {h : U32}
    {p : U32 × U32} (hv : gViewApp st h = some p) : gViewApp st' h = some p := by
  obtain ⟨l, hl⟩ := hx.apps
  simp only [gViewApp] at hv ⊢
  split at hv
  · rename_i ht
    rw [if_pos ht]
    simp only [Option.map_eq_some_iff] at hv ⊢
    obtain ⟨x, hx1, hx2⟩ := hv
    exact ⟨x, gprefix_getElem hl hx1, hx2⟩
  · simp at hv

theorem GExt.viewLam {st st' : Generated.State} (hx : GExt st st') {h : U32}
    {p : U32 × U32} (hv : gViewLam st h = some p) : gViewLam st' h = some p := by
  obtain ⟨l, hl⟩ := hx.lams
  simp only [gViewLam] at hv ⊢
  split at hv
  · rename_i ht
    rw [if_pos ht]
    simp only [Option.map_eq_some_iff] at hv ⊢
    obtain ⟨x, hx1, hx2⟩ := hv
    exact ⟨x, gprefix_getElem hl hx1, hx2⟩
  · simp at hv

/-! ## The denotation, as a relation

`MiniSpecs.lean`'s group, at the Aeneas types. -/

/-- con-leche: ConLeche/Kernel/Expr.lean:344 Expr — the fuel-indexed readback
of an Aeneas handle. -/
def denoteGAux (st : Generated.State) : Nat → U32 → Option Expr
  | 0, _ => none
  | f + 1, h =>
    if gTagOf h = mTagBvar then (gViewBvar st h).map (fun i => Expr.bvar i.val)
    else if gTagOf h = mTagApp then
      match gViewApp st h with
      | none => none
      | some (a, b) => opt2 Expr.app (denoteGAux st f a) (denoteGAux st f b)
    else if gTagOf h = mTagLam then
      match gViewLam st h with
      | none => none
      | some (a, b) =>
        opt2 (fun x y => Expr.lam x y default) (denoteGAux st f a) (denoteGAux st f b)
    else none

theorem dg_bvar {st : Generated.State} {h i : U32} (n : Nat)
    (hv : gViewBvar st h = some i) : denoteGAux st (n + 1) h = some (.bvar i.val) := by
  simp only [denoteGAux, if_pos (gViewBvar_tag hv), hv, Option.map_some]

theorem dg_app {st : Generated.State} {h a b : U32} (n : Nat)
    (hv : gViewApp st h = some (a, b)) :
    denoteGAux st (n + 1) h = opt2 Expr.app (denoteGAux st n a) (denoteGAux st n b) := by
  have ht := gViewApp_tag hv
  have hb : ¬ (gTagOf h = mTagBvar) := by rw [ht]; exact gtag_bvar_ne_app
  simp only [denoteGAux, if_neg hb, if_pos ht, hv]

theorem dg_lam {st : Generated.State} {h a b : U32} (n : Nat)
    (hv : gViewLam st h = some (a, b)) :
    denoteGAux st (n + 1) h
      = opt2 (fun x y => Expr.lam x y default) (denoteGAux st n a) (denoteGAux st n b) := by
  have ht := gViewLam_tag hv
  have hb : ¬ (gTagOf h = mTagBvar) := by rw [ht]; exact gtag_bvar_ne_lam
  have ha : ¬ (gTagOf h = mTagApp) := by rw [ht]; exact gtag_app_ne_lam
  simp only [denoteGAux, if_neg hb, if_neg ha, if_pos ht, hv]

theorem dg_inv {st : Generated.State} {h : U32} {e : Expr} :
    ∀ (n : Nat), denoteGAux st n h = some e →
      (∃ m i, n = m + 1 ∧ gViewBvar st h = some i ∧ e = .bvar i.val) ∨
      (∃ m a b ea eb, n = m + 1 ∧ gViewApp st h = some (a, b) ∧ e = .app ea eb ∧
        denoteGAux st m a = some ea ∧ denoteGAux st m b = some eb) ∨
      (∃ m a b ea eb, n = m + 1 ∧ gViewLam st h = some (a, b) ∧ e = .lam ea eb default ∧
        denoteGAux st m a = some ea ∧ denoteGAux st m b = some eb) := by
  intro n hd
  cases n with
  | zero => simp [denoteGAux] at hd
  | succ m =>
    by_cases hb : gTagOf h = mTagBvar
    · simp only [denoteGAux, if_pos hb, Option.map_eq_some_iff] at hd
      obtain ⟨i, hi, he⟩ := hd
      exact Or.inl ⟨m, i, rfl, hi, he.symm⟩
    · by_cases ha : gTagOf h = mTagApp
      · cases hv : gViewApp st h with
        | none => simp only [denoteGAux, if_neg hb, if_pos ha, hv] at hd; simp at hd
        | some p =>
          obtain ⟨a, b⟩ := p
          rw [dg_app m hv, opt2_eq_some_iff] at hd
          obtain ⟨x, y, hx, hy, he⟩ := hd
          exact Or.inr (Or.inl ⟨m, a, b, x, y, rfl, rfl, he.symm, hx, hy⟩)
      · by_cases hl : gTagOf h = mTagLam
        · cases hv : gViewLam st h with
          | none => simp only [denoteGAux, if_neg hb, if_neg ha, if_pos hl, hv] at hd; simp at hd
          | some p =>
            obtain ⟨a, b⟩ := p
            rw [dg_lam m hv, opt2_eq_some_iff] at hd
            obtain ⟨x, y, hx, hy, he⟩ := hd
            exact Or.inr (Or.inr ⟨m, a, b, x, y, rfl, rfl, he.symm, hx, hy⟩)
        · simp only [denoteGAux, if_neg hb, if_neg ha, if_neg hl] at hd; simp at hd

theorem denoteGAux_mono (st : Generated.State) :
    ∀ (n m : Nat) (h : U32) (e : Expr), denoteGAux st n h = some e → n ≤ m →
      denoteGAux st m h = some e := by
  intro n
  induction n with
  | zero => intro m h e hd _; simp [denoteGAux] at hd
  | succ n ih =>
    intro m h e hd hnm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hnm' : n ≤ m' := by omega
    rcases dg_inv (n + 1) hd with ⟨k, i, hk, hv, he⟩ | ⟨k, a, b, ea, eb, hk, hv, he, hx, hy⟩ |
      ⟨k, a, b, ea, eb, hk, hv, he, hx, hy⟩
    · rw [dg_bvar m' hv, he]
    · cases hk
      rw [dg_app m' hv, opt2_eq_some_iff]
      exact ⟨ea, eb, ih m' a ea hx hnm', ih m' b eb hy hnm', he.symm⟩
    · cases hk
      rw [dg_lam m' hv, opt2_eq_some_iff]
      exact ⟨ea, eb, ih m' a ea hx hnm', ih m' b eb hy hnm', he.symm⟩

/-- con-leche: ConLeche/Kernel/Expr.lean:344 Expr — **the readback relation,
on the Aeneas state**. -/
def DenotesG (st : Generated.State) (h : U32) (e : Expr) : Prop :=
  ∃ n, denoteGAux st n h = some e

theorem DenotesG.uniq {st : Generated.State} {h : U32} {e e' : Expr}
    (h1 : DenotesG st h e) (h2 : DenotesG st h e') : e = e' := by
  obtain ⟨n, hn⟩ := h1
  obtain ⟨m, hm⟩ := h2
  have a1 := denoteGAux_mono st n (max n m) h e hn (Nat.le_max_left _ _)
  have a2 := denoteGAux_mono st m (max n m) h e' hm (Nat.le_max_right _ _)
  rw [a1] at a2
  exact Option.some.inj a2

theorem DenotesG.ext {st st' : Generated.State} {h : U32} {e : Expr}
    (hd : DenotesG st h e) (hx : GExt st st') : DenotesG st' h e := by
  obtain ⟨n, hn⟩ := hd
  refine ⟨n, ?_⟩
  induction n generalizing h e with
  | zero => simp [denoteGAux] at hn
  | succ n ih =>
    rcases dg_inv (n + 1) hn with ⟨k, i, hk, hv, he⟩ | ⟨k, a, b, ea, eb, hk, hv, he, hxx, hyy⟩ |
      ⟨k, a, b, ea, eb, hk, hv, he, hxx, hyy⟩
    · rw [dg_bvar n (hx.viewBvar hv), he]
    · cases hk
      rw [dg_app n (hx.viewApp hv), opt2_eq_some_iff]
      exact ⟨ea, eb, ih hxx, ih hyy, he.symm⟩
    · cases hk
      rw [dg_lam n (hx.viewLam hv), opt2_eq_some_iff]
      exact ⟨ea, eb, ih hxx, ih hyy, he.symm⟩

theorem DenotesG.bvar {st : Generated.State} {h i : U32} (hv : gViewBvar st h = some i) :
    DenotesG st h (.bvar i.val) := ⟨1, dg_bvar 0 hv⟩

theorem DenotesG.app {st : Generated.State} {h a b : U32} {ea eb : Expr}
    (hv : gViewApp st h = some (a, b)) (ha : DenotesG st a ea) (hb : DenotesG st b eb) :
    DenotesG st h (.app ea eb) := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨max n m + 1, ?_⟩
  rw [dg_app _ hv, opt2_eq_some_iff]
  exact ⟨ea, eb, denoteGAux_mono st n _ a ea hn (Nat.le_max_left _ _),
    denoteGAux_mono st m _ b eb hm (Nat.le_max_right _ _), rfl⟩

theorem DenotesG.lam {st : Generated.State} {h a b : U32} {ea eb : Expr}
    (hv : gViewLam st h = some (a, b)) (ha : DenotesG st a ea) (hb : DenotesG st b eb) :
    DenotesG st h (.lam ea eb default) := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨max n m + 1, ?_⟩
  rw [dg_lam _ hv, opt2_eq_some_iff]
  exact ⟨ea, eb, denoteGAux_mono st n _ a ea hn (Nat.le_max_left _ _),
    denoteGAux_mono st m _ b eb hm (Nat.le_max_right _ _), rfl⟩

theorem DenotesG.bvar_inv {st : Generated.State} {h i : U32} {e : Expr}
    (hv : gViewBvar st h = some i) (hd : DenotesG st h e) : e = .bvar i.val :=
  hd.uniq (DenotesG.bvar hv)

theorem DenotesG.app_inv {st : Generated.State} {h a b : U32} {e : Expr}
    (hv : gViewApp st h = some (a, b)) (hd : DenotesG st h e) :
    ∃ ea eb, e = .app ea eb ∧ DenotesG st a ea ∧ DenotesG st b eb := by
  obtain ⟨n, hn⟩ := hd
  rcases dg_inv n hn with ⟨k, i, hk, hv2, _⟩ | ⟨k, a', b', ea, eb, hk, hv2, he, hx, hy⟩ |
    ⟨k, a', b', ea, eb, hk, hv2, he, hx, hy⟩
  · exact absurd ((gViewApp_tag hv).symm.trans (gViewBvar_tag hv2)) gtag_bvar_ne_app
  · rw [hv] at hv2
    have hp := Option.some.inj hv2
    have h1 : a = a' := congrArg Prod.fst hp
    have h2 : b = b' := congrArg Prod.snd hp
    subst h1; subst h2
    exact ⟨ea, eb, he, ⟨k, hx⟩, ⟨k, hy⟩⟩
  · exact absurd ((gViewLam_tag hv2).symm.trans (gViewApp_tag hv)) gtag_app_ne_lam

theorem DenotesG.lam_inv {st : Generated.State} {h a b : U32} {e : Expr}
    (hv : gViewLam st h = some (a, b)) (hd : DenotesG st h e) :
    ∃ ea eb, e = .lam ea eb default ∧ DenotesG st a ea ∧ DenotesG st b eb := by
  obtain ⟨n, hn⟩ := hd
  rcases dg_inv n hn with ⟨k, i, hk, hv2, _⟩ | ⟨k, a', b', ea, eb, hk, hv2, he, hx, hy⟩ |
    ⟨k, a', b', ea, eb, hk, hv2, he, hx, hy⟩
  · exact absurd ((gViewLam_tag hv).symm.trans (gViewBvar_tag hv2)) gtag_bvar_ne_lam
  · exact absurd ((gViewLam_tag hv).symm.trans (gViewApp_tag hv2)) gtag_app_ne_lam
  · rw [hv] at hv2
    have hp := Option.some.inj hv2
    have h1 : a = a' := congrArg Prod.fst hp
    have h2 : b = b' := congrArg Prod.snd hp
    subst h1; subst h2
    exact ⟨ea, eb, he, ⟨k, hx⟩, ⟨k, hy⟩⟩

/-- con-leche: none — "this handle reads back as something". -/
def DenotesSomeG (st : Generated.State) (c : U32) : Prop := ∃ e, DenotesG st c e

theorem DenotesSomeG.ext {st st' : Generated.State} {c : U32}
    (hd : DenotesSomeG st c) (hx : GExt st st') : DenotesSomeG st' c :=
  ⟨hd.choose, hd.choose_spec.ext hx⟩

theorem DenotesSomeG.of_app {st : Generated.State} {h a b : U32}
    (hv : gViewApp st h = some (a, b)) (hs : DenotesSomeG st h) :
    DenotesSomeG st a ∧ DenotesSomeG st b := by
  obtain ⟨e, he⟩ := hs
  obtain ⟨ea, eb, _, ha, hb⟩ := DenotesG.app_inv hv he
  exact ⟨⟨ea, ha⟩, ⟨eb, hb⟩⟩

theorem DenotesSomeG.of_lam {st : Generated.State} {h a b : U32}
    (hv : gViewLam st h = some (a, b)) (hs : DenotesSomeG st h) :
    DenotesSomeG st a ∧ DenotesSomeG st b := by
  obtain ⟨e, he⟩ := hs
  obtain ⟨ea, eb, _, ha, hb⟩ := DenotesG.lam_inv hv he
  exact ⟨⟨ea, ha⟩, ⟨eb, hb⟩⟩


/-! ## The answer relation, the per-site lemmas and the memo -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — "`r` in `st'` is what
`instantiate1` makes of `c` in `st`, at cursor `d`". -/
def Inst1AtG (ve : Expr) (d : Nat) (st : Generated.State) (c : U32)
    (st' : Generated.State) (r : U32) : Prop :=
  ∀ e, DenotesG st c e → DenotesG st' r (e.instantiate1 ve d)

@[grind →] theorem Inst1AtG.apply {ve : Expr} {d : Nat} {st st' : Generated.State}
    {c r : U32} {e : Expr} (h : Inst1AtG ve d st c st' r) (he : DenotesG st c e) :
    DenotesG st' r (e.instantiate1 ve d) := h e he

@[grind →] theorem Inst1AtG.denotes {ve : Expr} {d : Nat} {st st' : Generated.State}
    {c r : U32} (h : Inst1AtG ve d st c st' r) (hs : DenotesSomeG st c) :
    DenotesSomeG st' r := ⟨_, h hs.choose hs.choose_spec⟩

theorem Inst1AtG.ext {ve : Expr} {d : Nat} {st st' st'' : Generated.State} {c r : U32}
    (h : Inst1AtG ve d st c st' r) (hx : GExt st' st'') : Inst1AtG ve d st c st'' r :=
  fun e he => (h e he).ext hx

theorem Inst1AtG.of_ext {ve : Expr} {d : Nat} {st st0 st' : Generated.State} {c r : U32}
    (h : Inst1AtG ve d st c st' r) (hx : GExt st0 st) : Inst1AtG ve d st0 c st' r :=
  fun e he => h e (he.ext hx)

theorem Inst1AtG.retarget {ve : Expr} {d : Nat} {st st0 st' : Generated.State} {c r : U32}
    (h : Inst1AtG ve d st c st' r) (hx : GExt st st0) (hs : DenotesSomeG st c) :
    Inst1AtG ve d st0 c st' r := by
  intro e he
  obtain ⟨e0, he0⟩ := hs
  have heq := (he0.ext hx).uniq he
  subst heq
  exact h e0 he0

theorem Inst1AtG.app_step {ve : Expr} {d : Nat} {st s1 s2 s3 : Generated.State}
    {h f a rf ra r : U32} (hview : gViewApp st h = some (f, a))
    (hx1 : GExt st s1) (hf : Inst1AtG ve d st f s1 rf)
    (hx2 : GExt s1 s2) (ha : Inst1AtG ve d s1 a s2 ra)
    (hx3 : GExt s2 s3) (hr : gViewApp s3 r = some (rf, ra)) :
    Inst1AtG ve d st h s3 r := by
  intro e he
  obtain ⟨ef, ea, rfl, hdf, hda⟩ := DenotesG.app_inv hview he
  have h1 : DenotesG s3 rf (ef.instantiate1 ve d) := ((hf ef hdf).ext hx2).ext hx3
  have h2 : DenotesG s3 ra (ea.instantiate1 ve d) := ((ha ea (hda.ext hx1)).ext hx3)
  exact DenotesG.app hr h1 h2

theorem Inst1AtG.lam_step {ve : Expr} {d : Nat} {st s1 s2 s3 : Generated.State}
    {h ty b rt rb r : U32} (hview : gViewLam st h = some (ty, b))
    (hx1 : GExt st s1) (ht : Inst1AtG ve d st ty s1 rt)
    (hx2 : GExt s1 s2) (hb : Inst1AtG ve (d + 1) s1 b s2 rb)
    (hx3 : GExt s2 s3) (hr : gViewLam s3 r = some (rt, rb)) :
    Inst1AtG ve d st h s3 r := by
  intro e he
  obtain ⟨et, eb, rfl, hdt, hdb⟩ := DenotesG.lam_inv hview he
  have h1 : DenotesG s3 rt (et.instantiate1 ve d) := ((ht et hdt).ext hx2).ext hx3
  have h2 : DenotesG s3 rb (eb.instantiate1 ve (d + 1)) := ((hb eb (hdb.ext hx1)).ext hx3)
  exact DenotesG.lam hr h1 h2

theorem Inst1AtG.bvar_hit {ve : Expr} {st : Generated.State} {h d v : U32}
    (hv : gViewBvar st h = some d) (hvd : DenotesG st v ve) :
    Inst1AtG ve d.val st h st v := by
  intro e he
  rw [DenotesG.bvar_inv hv he]
  have hb : (Expr.bvar d.val).instantiate1 ve d.val = ve := by simp [Expr.instantiate1]
  rw [hb]
  exact hvd

theorem Inst1AtG.bvar_gt {ve : Expr} {st st' : Generated.State} {h d i r j : U32}
    (hv : gViewBvar st h = some i) (hgt : d.val < i.val) (hj : j.val = i.val - 1)
    (hr : gViewBvar st' r = some j) : Inst1AtG ve d.val st h st' r := by
  intro e he
  rw [DenotesG.bvar_inv hv he]
  have hb : (Expr.bvar i.val).instantiate1 ve d.val = Expr.bvar j.val := by
    simp only [Expr.instantiate1, if_neg (show ¬ i.val = d.val by omega),
      if_pos (show i.val > d.val by omega), hj]
  rw [hb]
  exact DenotesG.bvar hr

theorem Inst1AtG.bvar_le {ve : Expr} {st : Generated.State} {h d i : U32}
    (hv : gViewBvar st h = some i) (hne : ¬ i = d) (hle : ¬ d.val < i.val) :
    Inst1AtG ve d.val st h st h := by
  intro e he
  rw [DenotesG.bvar_inv hv he]
  have hne' : ¬ i.val = d.val := fun hc => hne (UScalar.val_eq_imp _ _ hc)
  have hb : (Expr.bvar i.val).instantiate1 ve d.val = Expr.bvar i.val := by
    simp only [Expr.instantiate1, if_neg hne', if_neg (show ¬ i.val > d.val by omega)]
  rw [hb]
  exact DenotesG.bvar hv

/-! ## The memo -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:62 Inst1MemoInv — the memo's
invariant on the Aeneas state. -/
def Inst1MemoG (ve : Expr) (st : Generated.State) : Prop :=
  ∀ me ∈ st.memo.val, ∃ e, DenotesG st me.key_h e ∧
    DenotesG st me.val (e.instantiate1 ve me.key_d.val)

theorem denoteGAux_congr {st st' : Generated.State} (h1 : st'.bvars = st.bvars)
    (h2 : st'.apps = st.apps) (h3 : st'.lams = st.lams) :
    ∀ (n : Nat) (h : U32), denoteGAux st' n h = denoteGAux st n h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    simp only [denoteGAux, gViewBvar, gViewApp, gViewLam, h1, h2, h3, ih]

theorem DenotesG.congr {st st' : Generated.State} (h1 : st'.bvars = st.bvars)
    (h2 : st'.apps = st.apps) (h3 : st'.lams = st.lams) {h : U32} {e : Expr}
    (hd : DenotesG st h e) : DenotesG st' h e := by
  obtain ⟨n, hn⟩ := hd
  exact ⟨n, by rw [denoteGAux_congr h1 h2 h3]; exact hn⟩

theorem Inst1MemoG.mono {ve : Expr} {st st' : Generated.State} (hm : Inst1MemoG ve st)
    (hx : GExt st st') (hc : st'.memo = st.memo) : Inst1MemoG ve st' := by
  intro me hmem
  rw [hc] at hmem
  obtain ⟨e, h1, h2⟩ := hm me hmem
  exact ⟨e, h1.ext hx, h2.ext hx⟩


/-! ## The cons tables and hash-consing, on the Aeneas state

C1's `abs_find_*` and `abs_intern_*` again, with the twin's view replaced by
`gView*`: the same inductions, the same `u32` arithmetic, a different
conclusion. -/

theorem gmk_tag (t j : Nat) (hj : j < mIdxCap) : (mMk t j) / mIdxCap = t := by
  simp only [mMk, mIdxCap] at hj ⊢
  omega

theorem gmk_idx (t j : Nat) (hj : j < mIdxCap) : (mMk t j) % mIdxCap = j := by
  simp only [mMk, mIdxCap] at hj ⊢
  omega

theorem gfind_bvar_from (st : Generated.State) (hwf : st.bvars.val.length ≤ mIdxCap)
    (k : U32) : ∀ (n : Nat) (i : Usize), st.bvars.val.length ≤ i.val + n →
    ∃ o : Option U32, Generated.find_bvar_from st k i = .ok o ∧
      ∀ r, o = some r → gViewBvar st r = some k := by
  intro n
  induction n with
  | zero =>
    intro i hn
    rw [Generated.find_bvar_from.eq_def]
    have hge : ¬ (i < alloc.vec.Vec.len st.bvars) := by
      intro hc; have : i.val < st.bvars.val.length := by simpa using hc
      omega
    rw [if_neg hge]
    exact ⟨none, rfl, by intro r hr; simp at hr⟩
  | succ n ih =>
    intro i hn
    rw [Generated.find_bvar_from.eq_def]
    by_cases hlt : i < alloc.vec.Vec.len st.bvars
    · have hb : i.val < st.bvars.val.length := by simpa using hlt
      obtain ⟨x, hx1, hx2⟩ :=
        spec_imp_exists (alloc.vec.Vec.index_usize_spec st.bvars i (by simpa using hb))
      rw [if_pos hlt]
      simp only [alloc.vec.Vec.index_slice_index, hx1, bind_tc_ok]
      by_cases hk : x = k
      · rw [if_pos hk]
        have hic : i.val < mIdxCap := by omega
        have hcast : absU (UScalar.cast .U32 i : U32) = i.val := by
          rw [absU, abs_cast_u32 i (by omega)]
        obtain ⟨o, ho1, ho2⟩ :=
          abs_mk Generated.TAG_BVAR (UScalar.cast .U32 i)
            (by rw [tagbvar]; simp [mTagBvar]) (by rw [hcast]; exact hic)
        simp only [lift, bind_tc_ok, ho1]
        refine ⟨some o, rfl, ?_⟩
        intro r hr
        cases hr
        rw [tagbvar, hcast, absU] at ho2
        simp only [gViewBvar, gTagOf, gIdxOf, ho2, gmk_tag _ _ hic, gmk_idx _ _ hic]
        rw [List.getElem?_eq_getElem hb, ← hx2, hk]
        simp
      · rw [if_neg hk]
        obtain ⟨j, hj1, hj2⟩ := usize_succ i (by scalar_tac)
        simp only [hj1, bind_tc_ok]
        exact ih j (by omega)
    · have hb : st.bvars.val.length ≤ i.val := by
        by_contra hc; exact hlt (by simpa using Nat.lt_of_not_le hc)
      rw [if_neg hlt]
      exact ⟨none, rfl, by intro r hr; simp at hr⟩

theorem gfind_app_from (st : Generated.State) (hwf : st.apps.val.length ≤ mIdxCap)
    (f a : U32) : ∀ (n : Nat) (i : Usize), st.apps.val.length ≤ i.val + n →
    ∃ o : Option U32, Generated.find_app_from st f a i = .ok o ∧
      ∀ r, o = some r → gViewApp st r = some (f, a) := by
  intro n
  induction n with
  | zero =>
    intro i hn
    rw [Generated.find_app_from.eq_def]
    have hge : ¬ (i < alloc.vec.Vec.len st.apps) := by
      intro hc; have : i.val < st.apps.val.length := by simpa using hc
      omega
    rw [if_neg hge]
    exact ⟨none, rfl, by intro r hr; simp at hr⟩
  | succ n ih =>
    intro i hn
    rw [Generated.find_app_from.eq_def]
    by_cases hlt : i < alloc.vec.Vec.len st.apps
    · have hb : i.val < st.apps.val.length := by simpa using hlt
      obtain ⟨x, hx1, hx2⟩ :=
        spec_imp_exists (alloc.vec.Vec.index_usize_spec st.apps i (by simpa using hb))
      rw [if_pos hlt]
      simp only [alloc.vec.Vec.index_slice_index, hx1, bind_tc_ok]
      by_cases hk : x.f = f ∧ x.a = a
      · rw [if_pos hk.1, if_pos hk.2]
        have hic : i.val < mIdxCap := by omega
        have hcast : absU (UScalar.cast .U32 i : U32) = i.val := by
          rw [absU, abs_cast_u32 i (by omega)]
        obtain ⟨o, ho1, ho2⟩ :=
          abs_mk Generated.TAG_APP (UScalar.cast .U32 i)
            (by rw [tagapp]; simp [mTagApp]) (by rw [hcast]; exact hic)
        simp only [lift, bind_tc_ok, ho1]
        refine ⟨some o, rfl, ?_⟩
        intro r hr
        cases hr
        rw [tagapp, hcast, absU] at ho2
        simp only [gViewApp, gTagOf, gIdxOf, ho2, gmk_tag _ _ hic, gmk_idx _ _ hic]
        rw [List.getElem?_eq_getElem hb, ← hx2]
        simp [hk.1, hk.2]
      · obtain ⟨j, hj1, hj2⟩ := usize_succ i (by scalar_tac)
        by_cases hf : x.f = f
        · rw [if_pos hf, if_neg (fun hc => hk ⟨hf, hc⟩), hj1, bind_tc_ok]
          exact ih j (by omega)
        · rw [if_neg hf, hj1, bind_tc_ok]
          exact ih j (by omega)
    · have hb : st.apps.val.length ≤ i.val := by
        by_contra hc; exact hlt (by simpa using Nat.lt_of_not_le hc)
      rw [if_neg hlt]
      exact ⟨none, rfl, by intro r hr; simp at hr⟩

theorem gfind_lam_from (st : Generated.State) (hwf : st.lams.val.length ≤ mIdxCap)
    (ty b : U32) : ∀ (n : Nat) (i : Usize), st.lams.val.length ≤ i.val + n →
    ∃ o : Option U32, Generated.find_lam_from st ty b i = .ok o ∧
      ∀ r, o = some r → gViewLam st r = some (ty, b) := by
  intro n
  induction n with
  | zero =>
    intro i hn
    rw [Generated.find_lam_from.eq_def]
    have hge : ¬ (i < alloc.vec.Vec.len st.lams) := by
      intro hc; have : i.val < st.lams.val.length := by simpa using hc
      omega
    rw [if_neg hge]
    exact ⟨none, rfl, by intro r hr; simp at hr⟩
  | succ n ih =>
    intro i hn
    rw [Generated.find_lam_from.eq_def]
    by_cases hlt : i < alloc.vec.Vec.len st.lams
    · have hb : i.val < st.lams.val.length := by simpa using hlt
      obtain ⟨x, hx1, hx2⟩ :=
        spec_imp_exists (alloc.vec.Vec.index_usize_spec st.lams i (by simpa using hb))
      rw [if_pos hlt]
      simp only [alloc.vec.Vec.index_slice_index, hx1, bind_tc_ok]
      by_cases hk : x.ty = ty ∧ x.body = b
      · rw [if_pos hk.1, if_pos hk.2]
        have hic : i.val < mIdxCap := by omega
        have hcast : absU (UScalar.cast .U32 i : U32) = i.val := by
          rw [absU, abs_cast_u32 i (by omega)]
        obtain ⟨o, ho1, ho2⟩ :=
          abs_mk Generated.TAG_LAM (UScalar.cast .U32 i)
            (by rw [taglam]; simp [mTagLam]) (by rw [hcast]; exact hic)
        simp only [lift, bind_tc_ok, ho1]
        refine ⟨some o, rfl, ?_⟩
        intro r hr
        cases hr
        rw [taglam, hcast, absU] at ho2
        simp only [gViewLam, gTagOf, gIdxOf, ho2, gmk_tag _ _ hic, gmk_idx _ _ hic]
        rw [List.getElem?_eq_getElem hb, ← hx2]
        simp [hk.1, hk.2]
      · obtain ⟨j, hj1, hj2⟩ := usize_succ i (by scalar_tac)
        by_cases hf : x.ty = ty
        · rw [if_pos hf, if_neg (fun hc => hk ⟨hf, hc⟩), hj1, bind_tc_ok]
          exact ih j (by omega)
        · rw [if_neg hf, hj1, bind_tc_ok]
          exact ih j (by omega)
    · have hb : st.lams.val.length ≤ i.val := by
        by_contra hc; exact hlt (by simpa using Nat.lt_of_not_le hc)
      rw [if_neg hlt]
      exact ⟨none, rfl, by intro r hr; simp at hr⟩


theorem gfind_bvar (st : Generated.State) (hwf : GWF st) (k : U32) :
    ∃ o : Option U32, Generated.find_bvar st k = .ok o ∧
      ∀ r, o = some r → gViewBvar st r = some k :=
  gfind_bvar_from st hwf.bvars k st.bvars.val.length 0#usize (by simp)

theorem gfind_app (st : Generated.State) (hwf : GWF st) (f a : U32) :
    ∃ o : Option U32, Generated.find_app st f a = .ok o ∧
      ∀ r, o = some r → gViewApp st r = some (f, a) :=
  gfind_app_from st hwf.apps f a st.apps.val.length 0#usize (by simp)

theorem gfind_lam (st : Generated.State) (hwf : GWF st) (ty b : U32) :
    ∃ o : Option U32, Generated.find_lam st ty b = .ok o ∧
      ∀ r, o = some r → gViewLam st r = some (ty, b) :=
  gfind_lam_from st hwf.lams ty b st.lams.val.length 0#usize (by simp)

theorem gintern_bvar (st : Generated.State) (hwf : GWF st) (k : U32) :
    ∃ (o : Option U32) (st' : Generated.State),
      Generated.intern_bvar st k = .ok (o, st') ∧ GWF st' ∧ GExt st st' ∧
      st'.memo = st.memo ∧ ∀ r, o = some r → gViewBvar st' r = some k := by
  obtain ⟨of, hf1, hf2⟩ := gfind_bvar st hwf k
  unfold Generated.intern_bvar
  rw [hf1, bind_tc_ok]
  cases of with
  | some h => exact ⟨some h, st, rfl, hwf, GExt.refl _, rfl, hf2⟩
  | none =>
    have hn : (alloc.vec.Vec.len st.bvars).val = st.bvars.val.length := by simp
    have hcast : absU (UScalar.cast .U32 (alloc.vec.Vec.len st.bvars) : U32)
        = st.bvars.val.length := by
      rw [absU, abs_cast_u32 _ (by rw [hn]; exact hwf.bvars), hn]
    simp only [lift, bind_tc_ok]
    by_cases hlt : (UScalar.cast .U32 (alloc.vec.Vec.len st.bvars) : U32) < Generated.IDX_CAP
    · have hlt' : st.bvars.val.length < mIdxCap := by
        have hx : (UScalar.cast .U32 (alloc.vec.Vec.len st.bvars) : U32).val
            < (Generated.IDX_CAP : U32).val := by simpa using hlt
        rw [show ((UScalar.cast .U32 (alloc.vec.Vec.len st.bvars) : U32)).val
              = st.bvars.val.length from hcast] at hx
        rw [← idxcap]; exact hx
      obtain ⟨v, hv1, hv2⟩ :=
        spec_imp_exists (alloc.vec.Vec.push_spec st.bvars k (by
          have := Usize.bounds_eq; simp only [mIdxCap] at hlt'; scalar_tac))
      obtain ⟨o, ho1, ho2⟩ :=
        abs_mk Generated.TAG_BVAR (UScalar.cast .U32 (alloc.vec.Vec.len st.bvars))
          (by rw [tagbvar]; simp [mTagBvar]) (by rw [hcast]; exact hlt')
      rw [if_pos hlt, hv1, bind_tc_ok]
      simp only [bind_tc_ok, ho1]
      refine ⟨some o, { st with bvars := v }, rfl,
        ⟨by rw [hv2]; simp; omega, hwf.apps, hwf.lams⟩,
        ⟨⟨[k], by rw [hv2]⟩, ⟨[], by simp⟩, ⟨[], by simp⟩⟩, rfl, ?_⟩
      intro r hr
      cases hr
      rw [tagbvar, hcast, absU] at ho2
      simp only [gViewBvar, gTagOf, gIdxOf, ho2, gmk_tag _ _ hlt', gmk_idx _ _ hlt']
      show (v.val)[st.bvars.val.length]? = some k
      rw [hv2]
      simp
    · rw [if_neg hlt]
      exact ⟨none, st, rfl, hwf, GExt.refl _, rfl, by intro r hr; simp at hr⟩

theorem gintern_app (st : Generated.State) (hwf : GWF st) (f a : U32) :
    ∃ (o : Option U32) (st' : Generated.State),
      Generated.intern_app st f a = .ok (o, st') ∧ GWF st' ∧ GExt st st' ∧
      st'.memo = st.memo ∧ ∀ r, o = some r → gViewApp st' r = some (f, a) := by
  obtain ⟨of, hf1, hf2⟩ := gfind_app st hwf f a
  unfold Generated.intern_app
  rw [hf1, bind_tc_ok]
  cases of with
  | some h => exact ⟨some h, st, rfl, hwf, GExt.refl _, rfl, hf2⟩
  | none =>
    have hn : (alloc.vec.Vec.len st.apps).val = st.apps.val.length := by simp
    have hcast : absU (UScalar.cast .U32 (alloc.vec.Vec.len st.apps) : U32)
        = st.apps.val.length := by
      rw [absU, abs_cast_u32 _ (by rw [hn]; exact hwf.apps), hn]
    simp only [lift, bind_tc_ok]
    by_cases hlt : (UScalar.cast .U32 (alloc.vec.Vec.len st.apps) : U32) < Generated.IDX_CAP
    · have hlt' : st.apps.val.length < mIdxCap := by
        have hx : (UScalar.cast .U32 (alloc.vec.Vec.len st.apps) : U32).val
            < (Generated.IDX_CAP : U32).val := by simpa using hlt
        rw [show ((UScalar.cast .U32 (alloc.vec.Vec.len st.apps) : U32)).val
              = st.apps.val.length from hcast] at hx
        rw [← idxcap]; exact hx
      obtain ⟨v, hv1, hv2⟩ :=
        spec_imp_exists (alloc.vec.Vec.push_spec st.apps
          ({ f := f, a := a } : Generated.AppNode) (by
            have := Usize.bounds_eq; simp only [mIdxCap] at hlt'; scalar_tac))
      obtain ⟨o, ho1, ho2⟩ :=
        abs_mk Generated.TAG_APP (UScalar.cast .U32 (alloc.vec.Vec.len st.apps))
          (by rw [tagapp]; simp [mTagApp]) (by rw [hcast]; exact hlt')
      rw [if_pos hlt, hv1, bind_tc_ok]
      simp only [bind_tc_ok, ho1]
      refine ⟨some o, { st with apps := v }, rfl,
        ⟨hwf.bvars, by rw [hv2]; simp; omega, hwf.lams⟩,
        ⟨⟨[], by simp⟩, ⟨[{ f := f, a := a }], by rw [hv2]⟩, ⟨[], by simp⟩⟩, rfl, ?_⟩
      intro r hr
      cases hr
      rw [tagapp, hcast, absU] at ho2
      simp only [gViewApp, gTagOf, gIdxOf, ho2, gmk_tag _ _ hlt', gmk_idx _ _ hlt']
      show ((v.val)[st.apps.val.length]?).map (fun n => (n.f, n.a)) = some (f, a)
      rw [hv2]
      simp
    · rw [if_neg hlt]
      exact ⟨none, st, rfl, hwf, GExt.refl _, rfl, by intro r hr; simp at hr⟩

theorem gintern_lam (st : Generated.State) (hwf : GWF st) (ty b : U32) :
    ∃ (o : Option U32) (st' : Generated.State),
      Generated.intern_lam st ty b = .ok (o, st') ∧ GWF st' ∧ GExt st st' ∧
      st'.memo = st.memo ∧ ∀ r, o = some r → gViewLam st' r = some (ty, b) := by
  obtain ⟨of, hf1, hf2⟩ := gfind_lam st hwf ty b
  unfold Generated.intern_lam
  rw [hf1, bind_tc_ok]
  cases of with
  | some h => exact ⟨some h, st, rfl, hwf, GExt.refl _, rfl, hf2⟩
  | none =>
    have hn : (alloc.vec.Vec.len st.lams).val = st.lams.val.length := by simp
    have hcast : absU (UScalar.cast .U32 (alloc.vec.Vec.len st.lams) : U32)
        = st.lams.val.length := by
      rw [absU, abs_cast_u32 _ (by rw [hn]; exact hwf.lams), hn]
    simp only [lift, bind_tc_ok]
    by_cases hlt : (UScalar.cast .U32 (alloc.vec.Vec.len st.lams) : U32) < Generated.IDX_CAP
    · have hlt' : st.lams.val.length < mIdxCap := by
        have hx : (UScalar.cast .U32 (alloc.vec.Vec.len st.lams) : U32).val
            < (Generated.IDX_CAP : U32).val := by simpa using hlt
        rw [show ((UScalar.cast .U32 (alloc.vec.Vec.len st.lams) : U32)).val
              = st.lams.val.length from hcast] at hx
        rw [← idxcap]; exact hx
      obtain ⟨v, hv1, hv2⟩ :=
        spec_imp_exists (alloc.vec.Vec.push_spec st.lams
          ({ ty := ty, body := b } : Generated.LamNode) (by
            have := Usize.bounds_eq; simp only [mIdxCap] at hlt'; scalar_tac))
      obtain ⟨o, ho1, ho2⟩ :=
        abs_mk Generated.TAG_LAM (UScalar.cast .U32 (alloc.vec.Vec.len st.lams))
          (by rw [taglam]; simp [mTagLam]) (by rw [hcast]; exact hlt')
      rw [if_pos hlt, hv1, bind_tc_ok]
      simp only [bind_tc_ok, ho1]
      refine ⟨some o, { st with lams := v }, rfl,
        ⟨hwf.bvars, hwf.apps, by rw [hv2]; simp; omega⟩,
        ⟨⟨[], by simp⟩, ⟨[], by simp⟩, ⟨[{ ty := ty, body := b }], by rw [hv2]⟩⟩, rfl, ?_⟩
      intro r hr
      cases hr
      rw [taglam, hcast, absU] at ho2
      simp only [gViewLam, gTagOf, gIdxOf, ho2, gmk_tag _ _ hlt', gmk_idx _ _ hlt']
      show ((v.val)[st.lams.val.length]?).map (fun n => (n.ty, n.body)) = some (ty, b)
      rw [hv2]
      simp
    · rw [if_neg hlt]
      exact ⟨none, st, rfl, hwf, GExt.refl _, rfl, by intro r hr; simp at hr⟩


/-! ## The memo, on the Aeneas state -/

theorem gmemo_get_from (st : Generated.State) (h d : U32) :
    ∀ (n : Nat) (i : Usize), st.memo.val.length ≤ i.val + n →
    ∃ o : Option U32, Generated.memo_get_from st h d i = .ok o ∧
      ∀ r, o = some r →
        ∃ me ∈ st.memo.val, me.key_h = h ∧ me.key_d = d ∧ me.val = r := by
  intro n
  induction n with
  | zero =>
    intro i hn
    rw [Generated.memo_get_from.eq_def]
    have hge : ¬ (i < alloc.vec.Vec.len st.memo) := by
      intro hc; have : i.val < st.memo.val.length := by simpa using hc
      omega
    rw [if_neg hge]
    exact ⟨none, rfl, by intro r hr; simp at hr⟩
  | succ n ih =>
    intro i hn
    rw [Generated.memo_get_from.eq_def]
    by_cases hlt : i < alloc.vec.Vec.len st.memo
    · have hb : i.val < st.memo.val.length := by simpa using hlt
      obtain ⟨x, hx1, hx2⟩ :=
        spec_imp_exists (alloc.vec.Vec.index_usize_spec st.memo i (by simpa using hb))
      rw [if_pos hlt]
      simp only [alloc.vec.Vec.index_slice_index, hx1, bind_tc_ok]
      by_cases hk : x.key_h = h ∧ x.key_d = d
      · rw [if_pos hk.1, if_pos hk.2]
        refine ⟨some x.val, rfl, ?_⟩
        intro r hr
        simp only [Option.some.injEq] at hr
        exact ⟨x, by rw [hx2]; exact List.getElem_mem hb, hk.1, hk.2, hr⟩
      · obtain ⟨j, hj1, hj2⟩ := usize_succ i (by scalar_tac)
        by_cases hf : x.key_h = h
        · rw [if_pos hf, if_neg (fun hc => hk ⟨hf, hc⟩), hj1, bind_tc_ok]
          exact ih j (by omega)
        · rw [if_neg hf, hj1, bind_tc_ok]
          exact ih j (by omega)
    · have hb : st.memo.val.length ≤ i.val := by
        by_contra hc; exact hlt (by simpa using Nat.lt_of_not_le hc)
      rw [if_neg hlt]
      exact ⟨none, rfl, by intro r hr; simp at hr⟩

theorem gmemo_get (st : Generated.State) (h d : U32) :
    ∃ o : Option U32, Generated.memo_get st h d = .ok o ∧
      ∀ r, o = some r →
        ∃ me ∈ st.memo.val, me.key_h = h ∧ me.key_d = d ∧ me.val = r :=
  gmemo_get_from st h d st.memo.val.length 0#usize (by simp)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:62 Inst1MemoInv — **the memo
hit**. -/
theorem Inst1MemoG.get {ve : Expr} {st : Generated.State} {h d r : U32}
    (hm : Inst1MemoG ve st)
    (hmem : ∃ me ∈ st.memo.val, me.key_h = h ∧ me.key_d = d ∧ me.val = r) :
    Inst1AtG ve d.val st h st r := by
  obtain ⟨me, hme, e1, e2, e3⟩ := hmem
  obtain ⟨e, h1, h2⟩ := hm me hme
  rw [e1] at h1
  rw [e2, e3] at h2
  intro e' he'
  have heq := h1.uniq he'
  subst heq
  exact h2

/-- con-leche: ConLeche/Kernel/ExprOps.lean:116 instantiate1Go — the memo
insert, inverted. -/
theorem gmemo_set (st st' : Generated.State) (h d r : U32)
    (hr : Generated.memo_set st h d r = .ok st') :
    st'.bvars = st.bvars ∧ st'.apps = st.apps ∧ st'.lams = st.lams ∧
      st'.memo.val = st.memo.val ++ [{ key_h := h, key_d := d, val := r }] := by
  unfold Generated.memo_set at hr
  cases hp : alloc.vec.Vec.push st.memo
      ({ key_h := h, key_d := d, val := r } : Generated.MemoEntry) using Result.cases with
  | ret v =>
    rw [hp, bind_tc_ok, Result.ok.injEq] at hr
    subst hr
    exact ⟨rfl, rfl, rfl, vec_push_inv _ _ _ hp⟩
  | vis e k => rw [hp] at hr; simp at hr
  | div => rw [hp] at hr; simp at hr

theorem Inst1MemoG.insert {ve : Expr} {st st' : Generated.State} {h d r : U32}
    (hm : Inst1MemoG ve st) (hset : Generated.memo_set st h d r = .ok st')
    (hk : DenotesSomeG st h) (hr : Inst1AtG ve d.val st h st r) : Inst1MemoG ve st' := by
  obtain ⟨hb, ha, hl, hmemo⟩ := gmemo_set st st' h d r hset
  intro me hme
  rw [hmemo, List.mem_append, List.mem_singleton] at hme
  rcases hme with hme | heq
  · obtain ⟨e, h1, h2⟩ := hm me hme
    exact ⟨e, h1.congr hb ha hl, h2.congr hb ha hl⟩
  · subst heq
    obtain ⟨e, he⟩ := hk
    exact ⟨e, he.congr hb ha hl, (hr e he).congr hb ha hl⟩

theorem GWF.of_memo_set {st st' : Generated.State} {h d r : U32}
    (hwf : GWF st) (hset : Generated.memo_set st h d r = .ok st') : GWF st' := by
  obtain ⟨hb, ha, hl, _⟩ := gmemo_set st st' h d r hset
  exact ⟨by rw [hb]; exact hwf.bvars, by rw [ha]; exact hwf.apps, by rw [hl]; exact hwf.lams⟩

theorem GExt.of_memo_set {st st' : Generated.State} {h d r : U32}
    (hset : Generated.memo_set st h d r = .ok st') : GExt st st' := by
  obtain ⟨hb, ha, hl, _⟩ := gmemo_set st st' h d r hset
  exact ⟨⟨[], by rw [hb]; simp⟩, ⟨[], by rw [ha]; simp⟩, ⟨[], by rw [hl]; simp⟩⟩

end ConRon.Arena.Spike

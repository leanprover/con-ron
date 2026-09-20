/-
# Experiment C1's layer: the Aeneas state, abstracted to the Lean twin's

DESIGN §8.6's experiment C1 is *representation only*: `Std.U32` becomes
`Nat`, `alloc.vec.Vec` becomes `List`, and `Result` becomes
`StateT MState (Except CheckError)`.  No `Expr` occurs anywhere in this
module, and none of the lemmas below mentions a denotation.

The module is **one abstraction lemma per store primitive** — the eight
`_tmp/t97/spike-report.md` §5 predicted — plus the machine arithmetic they
need.  What the spike did *not* predict, and what the numbers in the report's
round-2 section record, is that the representation half is **not**
invariant-free: Rust's `n as u32` truncates rather than failing, so
`find_*_from`'s index cast is faithful only below `IDX_CAP`, and C1 needs the
arena-capacity invariant `GWF` exactly as the denotation half needs
`StoreWF`.  That invariant is maintained by `intern_*`'s own capacity test,
which is the same test the twin makes.
-/
import ConRon.Arena.Spike.Mini
import ConRon.Arena.Spike.MiniRun
import ConRon.Arena.Spike.Generated.Funs

namespace ConRon.Arena.Spike

open ConLeche Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-! ## The abstraction -/

/-- con-leche: none — a machine word as a number. -/
def absU (x : U32) : Nat := x.val

/-- con-leche: none — the Aeneas state as the twin's state. -/
def absState (st : Generated.State) : MState :=
  ⟨st.bvars.val.map absU,
   st.apps.val.map (fun n => (absU n.f, absU n.a)),
   st.lams.val.map (fun n => (absU n.ty, absU n.body)),
   st.memo.val.map (fun e => (absU e.key_h, absU e.key_d, absU e.val))⟩

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the representation
invariant**: no constructor array is longer than `IDX_CAP`.  Maintained by
`intern_*`'s capacity test; needed because `as u32` truncates. -/
structure GWF (st : Generated.State) : Prop where
  bvars : st.bvars.val.length ≤ mIdxCap
  apps : st.apps.val.length ≤ mIdxCap
  lams : st.lams.val.length ≤ mIdxCap

/-! ## Handle arithmetic -/

theorem absU_inj {x y : U32} (h : absU x = absU y) : x = y := UScalar.val_eq_imp _ _ h
theorem absU_eq {x y : U32} : (absU x = absU y) ↔ x = y := ⟨absU_inj, fun h => by rw [h]⟩

theorem idxcap : absU Generated.IDX_CAP = mIdxCap := by simp [absU, Generated.IDX_CAP, mIdxCap]
theorem tagbvar : absU Generated.TAG_BVAR = mTagBvar := by
  simp [absU, Generated.TAG_BVAR, mTagBvar]
theorem tagapp : absU Generated.TAG_APP = mTagApp := by simp [absU, Generated.TAG_APP, mTagApp]
theorem taglam : absU Generated.TAG_LAM = mTagLam := by simp [absU, Generated.TAG_LAM, mTagLam]

/-- con-leche: none — `tag_of` never fails and computes `mTagOf`. -/
theorem abs_tag (h : U32) : ∃ t : U32, Generated.tag_of h = .ok t ∧ absU t = mTagOf (absU h) := by
  obtain ⟨t, h1, h2⟩ :=
    spec_imp_exists (U32.div_spec (y := Generated.IDX_CAP) h (by simp [Generated.IDX_CAP]))
  exact ⟨t, h1, by simp only [absU, mTagOf] at *; rw [h2, ← idxcap]; rfl⟩

/-- con-leche: none — `idx_of` never fails and computes `mIdxOf`. -/
theorem abs_idx (h : U32) : ∃ t : U32, Generated.idx_of h = .ok t ∧ absU t = mIdxOf (absU h) := by
  obtain ⟨t, h1, h2⟩ :=
    spec_imp_exists (U32.rem_spec (y := Generated.IDX_CAP) h (by simp [Generated.IDX_CAP]))
  exact ⟨t, h1, by simp only [absU, mIdxOf] at *; rw [h2, ← idxcap]; rfl⟩

/-- con-leche: none — `usize::from(u32)` is exact on every platform Aeneas
models (`Usize.max` is `U32.max` or `U64.max`). -/
theorem abs_cast_usize (i : U32) :
    ∃ j : Usize, (lift (UScalar.cast .Usize i) : Result Usize) = .ok j ∧ j.val = i.val := by
  have hb : (i.val : Nat) ≤ UScalar.max .Usize := by
    have := i.hBounds; have := Usize.bounds_eq
    simp only [UScalar.max_USize_eq]; scalar_tac
  exact spec_imp_exists (UScalar.cast_inBounds_spec .Usize i hb)

/-- con-leche: none — **the truncating cast**, faithful below `IDX_CAP`.
`lift` never fails, so the only content is the modulus. -/
theorem abs_cast_u32 (i : Usize) (h : i.val ≤ mIdxCap) :
    (UScalar.cast .U32 i : U32).val = i.val := by
  have := UScalar.cast_inBounds_spec (src_ty := .Usize) .U32 i (by simp [mIdxCap] at h; scalar_tac)
  simpa [lift] using spec_imp_exists this

/-- con-leche: none — `mk` never fails for a tag below three and an index
below `IDX_CAP`, and it computes `mMk`. -/
theorem abs_mk (t i : U32) (ht : absU t ≤ 2) (hi : absU i < mIdxCap) :
    ∃ o : U32, Generated.mk t i = .ok o ∧ absU o = mMk (absU t) (absU i) := by
  simp only [absU, mIdxCap] at ht hi
  obtain ⟨m, hm1, hm2⟩ :=
    spec_imp_exists (U32.mul_spec (x := t) (y := Generated.IDX_CAP)
      (by simp only [Generated.IDX_CAP]; scalar_tac))
  have hmv : m.val = t.val * 268435456 := by rw [hm2]; simp [Generated.IDX_CAP]
  obtain ⟨o, ho1, ho2⟩ :=
    spec_imp_exists (U32.add_spec (x := m) (y := i) (by rw [hmv]; scalar_tac))
  refine ⟨o, ?_, ?_⟩
  · unfold Generated.mk; rw [hm1, bind_tc_ok, ho1]
  · simp only [absU, mMk, mIdxCap]; rw [ho2, hmv]

/-! ## The three views -/

theorem abs_view_bvar (st : Generated.State) (h : U32) :
    ∃ o : Option U32, Generated.view_bvar st h = .ok o ∧
      (absState st).viewBvar (absU h) = o.map absU := by
  obtain ⟨t, ht, htv⟩ := abs_tag h
  obtain ⟨i, hi, hiv⟩ := abs_idx h
  obtain ⟨j, hj, hjv⟩ := abs_cast_usize i
  have hjv' : j.val = mIdxOf (absU h) := by rw [hjv]; exact hiv
  unfold Generated.view_bvar MState.viewBvar
  simp only [ht, hi, hj, bind_tc_ok, alloc.vec.Vec.index_slice_index]
  by_cases hteq : t = Generated.TAG_BVAR
  · have hm : mTagOf (absU h) = mTagBvar := by rw [← htv, ← tagbvar, hteq]
    rw [if_pos hteq, if_pos hm]
    by_cases hlt : j < alloc.vec.Vec.len st.bvars
    · have hb : j.val < st.bvars.val.length := by simpa using hlt
      obtain ⟨x, hx1, hx2⟩ :=
        spec_imp_exists (alloc.vec.Vec.index_usize_spec st.bvars j (by simpa using hb))
      rw [if_pos hlt, hx1, bind_tc_ok]
      refine ⟨some x, rfl, ?_⟩
      simp only [absState, Option.map_some, List.getElem?_map, ← hjv']
      rw [List.getElem?_eq_getElem hb, hx2]; rfl
    · have hb : st.bvars.val.length ≤ j.val := by simpa using hlt
      rw [if_neg hlt]
      exact ⟨none, rfl, by
        simp only [absState, Option.map_none, List.getElem?_map, ← hjv',
          List.getElem?_eq_none hb]⟩
  · have hm : ¬ (mTagOf (absU h) = mTagBvar) := by
      rw [← htv, ← tagbvar, absU_eq]; exact hteq
    rw [if_neg hteq, if_neg hm]
    exact ⟨none, rfl, rfl⟩

theorem abs_view_app (st : Generated.State) (h : U32) :
    ∃ o : Option (U32 × U32), Generated.view_app st h = .ok o ∧
      (absState st).viewApp (absU h) = o.map (fun p => (absU p.1, absU p.2)) := by
  obtain ⟨t, ht, htv⟩ := abs_tag h
  obtain ⟨i, hi, hiv⟩ := abs_idx h
  obtain ⟨j, hj, hjv⟩ := abs_cast_usize i
  have hjv' : j.val = mIdxOf (absU h) := by rw [hjv]; exact hiv
  unfold Generated.view_app MState.viewApp
  simp only [ht, hi, hj, bind_tc_ok, alloc.vec.Vec.index_slice_index]
  by_cases hteq : t = Generated.TAG_APP
  · have hm : mTagOf (absU h) = mTagApp := by rw [← htv, ← tagapp, hteq]
    rw [if_pos hteq, if_pos hm]
    by_cases hlt : j < alloc.vec.Vec.len st.apps
    · have hb : j.val < st.apps.val.length := by simpa using hlt
      obtain ⟨x, hx1, hx2⟩ :=
        spec_imp_exists (alloc.vec.Vec.index_usize_spec st.apps j (by simpa using hb))
      rw [if_pos hlt, hx1, bind_tc_ok]
      refine ⟨some (x.f, x.a), rfl, ?_⟩
      simp only [absState, Option.map_some, List.getElem?_map, ← hjv']
      rw [List.getElem?_eq_getElem hb, hx2]; rfl
    · have hb : st.apps.val.length ≤ j.val := by simpa using hlt
      rw [if_neg hlt]
      exact ⟨none, rfl, by
        simp only [absState, Option.map_none, List.getElem?_map, ← hjv',
          List.getElem?_eq_none hb]⟩
  · have hm : ¬ (mTagOf (absU h) = mTagApp) := by
      rw [← htv, ← tagapp, absU_eq]; exact hteq
    rw [if_neg hteq, if_neg hm]
    exact ⟨none, rfl, rfl⟩

theorem abs_view_lam (st : Generated.State) (h : U32) :
    ∃ o : Option (U32 × U32), Generated.view_lam st h = .ok o ∧
      (absState st).viewLam (absU h) = o.map (fun p => (absU p.1, absU p.2)) := by
  obtain ⟨t, ht, htv⟩ := abs_tag h
  obtain ⟨i, hi, hiv⟩ := abs_idx h
  obtain ⟨j, hj, hjv⟩ := abs_cast_usize i
  have hjv' : j.val = mIdxOf (absU h) := by rw [hjv]; exact hiv
  unfold Generated.view_lam MState.viewLam
  simp only [ht, hi, hj, bind_tc_ok, alloc.vec.Vec.index_slice_index]
  by_cases hteq : t = Generated.TAG_LAM
  · have hm : mTagOf (absU h) = mTagLam := by rw [← htv, ← taglam, hteq]
    rw [if_pos hteq, if_pos hm]
    by_cases hlt : j < alloc.vec.Vec.len st.lams
    · have hb : j.val < st.lams.val.length := by simpa using hlt
      obtain ⟨x, hx1, hx2⟩ :=
        spec_imp_exists (alloc.vec.Vec.index_usize_spec st.lams j (by simpa using hb))
      rw [if_pos hlt, hx1, bind_tc_ok]
      refine ⟨some (x.ty, x.body), rfl, ?_⟩
      simp only [absState, Option.map_some, List.getElem?_map, ← hjv']
      rw [List.getElem?_eq_getElem hb, hx2]; rfl
    · have hb : st.lams.val.length ≤ j.val := by simpa using hlt
      rw [if_neg hlt]
      exact ⟨none, rfl, by
        simp only [absState, Option.map_none, List.getElem?_map, ← hjv',
          List.getElem?_eq_none hb]⟩
  · have hm : ¬ (mTagOf (absU h) = mTagLam) := by
      rw [← htv, ← taglam, absU_eq]; exact hteq
    rw [if_neg hteq, if_neg hm]
    exact ⟨none, rfl, rfl⟩


/-- con-leche: none — the checked `u32` addition, inverted: it only fails on
overflow, and the caller is told it did not. -/
theorem u32_add_inv {x y z : U32} (h : (x + y : Result U32) = .ok z) :
    z.val = x.val + y.val := by
  have he := UScalar.add_equiv x y
  rw [h] at he
  simp only [Result.match.ok] at he
  exact he.2.1

/-! ## The cons tables

`find_*_from` is the Rust's index-carrying recursion; `listFindIdx` is the
twin's structural one.  One induction each, on the number of entries left. -/

theorem usize_succ (i : Usize) (h : i.val < Usize.max) :
    ∃ j : Usize, (i + 1#usize : Result Usize) = Result.ok j ∧ j.val = i.val + 1 := by
  have hb : (i.val : Nat) + (1#usize : Usize).val ≤ Usize.max := by
    have : (1#usize : Usize).val = 1 := by scalar_tac
    omega
  simpa using spec_imp_exists (Usize.add_spec (x := i) (y := 1#usize) hb)

theorem abs_find_bvar_from (st : Generated.State) (hwf : st.bvars.val.length ≤ mIdxCap)
    (k : U32) : ∀ (n : Nat) (i : Usize), st.bvars.val.length ≤ i.val + n →
    ∃ o : Option U32, Generated.find_bvar_from st k i = .ok o ∧
      (listFindIdx ((st.bvars.val.drop i.val).map absU) (absU k) i.val).map (mMk mTagBvar)
        = o.map absU := by
  intro n
  induction n with
  | zero =>
    intro i hn
    rw [Generated.find_bvar_from.eq_def]
    have hge : ¬ (i < alloc.vec.Vec.len st.bvars) := by
      intro hc; have : i.val < st.bvars.val.length := by simpa using hc
      omega
    rw [if_neg hge]
    exact ⟨none, rfl, by rw [List.drop_eq_nil_of_le (by omega)]; rfl⟩
  | succ n ih =>
    intro i hn
    rw [Generated.find_bvar_from.eq_def]
    by_cases hlt : i < alloc.vec.Vec.len st.bvars
    · have hb : i.val < st.bvars.val.length := by simpa using hlt
      obtain ⟨x, hx1, hx2⟩ :=
        spec_imp_exists (alloc.vec.Vec.index_usize_spec st.bvars i (by simpa using hb))
      rw [if_pos hlt]
      simp only [alloc.vec.Vec.index_slice_index, hx1, bind_tc_ok]
      rw [List.drop_eq_getElem_cons hb, List.map_cons, listFindIdx]
      by_cases hk : x = k
      · rw [if_pos hk]
        have hcast : (UScalar.cast .U32 i : U32).val = i.val := abs_cast_u32 i (by omega)
        obtain ⟨o, ho1, ho2⟩ :=
          abs_mk Generated.TAG_BVAR (UScalar.cast .U32 i)
            (by rw [tagbvar]; simp [mTagBvar]) (by rw [absU, hcast]; omega)
        simp only [lift, bind_tc_ok, ho1]
        refine ⟨some o, rfl, ?_⟩
        have hbeq : (absU st.bvars.val[i.val] == absU k) = true := by rw [← hx2, hk]; simp
        rw [if_pos hbeq]
        simp only [Option.map_some]
        rw [ho2, tagbvar, absU, hcast]
      · rw [if_neg hk]
        obtain ⟨j, hj1, hj2⟩ := usize_succ i (by scalar_tac)
        simp only [hj1, bind_tc_ok]
        have hbeq : ¬ ((absU st.bvars.val[i.val] == absU k) = true) := by
          rw [← hx2]; simp only [beq_iff_eq]; intro hc; exact hk (absU_inj hc)
        rw [if_neg hbeq, ← hj2]
        exact ih j (by omega)
    · have hb : st.bvars.val.length ≤ i.val := by
        by_contra hc; exact hlt (by simpa using Nat.lt_of_not_le hc)
      rw [if_neg hlt]
      exact ⟨none, rfl, by rw [List.drop_eq_nil_of_le (by omega)]; rfl⟩

theorem abs_find_bvar (st : Generated.State) (hwf : GWF st) (k : U32) :
    ∃ o : Option U32, Generated.find_bvar st k = .ok o ∧
      mFindBvar (absState st) (absU k) = o.map absU := by
  obtain ⟨o, h1, h2⟩ := abs_find_bvar_from st hwf.bvars k st.bvars.val.length 0#usize (by simp)
  exact ⟨o, h1, h2⟩

theorem abs_find_app_from (st : Generated.State) (hwf : st.apps.val.length ≤ mIdxCap)
    (f a : U32) : ∀ (n : Nat) (i : Usize), st.apps.val.length ≤ i.val + n →
    ∃ o : Option U32, Generated.find_app_from st f a i = .ok o ∧
      (listFindIdx ((st.apps.val.drop i.val).map (fun n => (absU n.f, absU n.a)))
        (absU f, absU a) i.val).map (mMk mTagApp) = o.map absU := by
  intro n
  induction n with
  | zero =>
    intro i hn
    rw [Generated.find_app_from.eq_def]
    have hge : ¬ (i < alloc.vec.Vec.len st.apps) := by
      intro hc; have : i.val < st.apps.val.length := by simpa using hc
      omega
    rw [if_neg hge]
    exact ⟨none, rfl, by rw [List.drop_eq_nil_of_le (by omega)]; rfl⟩
  | succ n ih =>
    intro i hn
    rw [Generated.find_app_from.eq_def]
    by_cases hlt : i < alloc.vec.Vec.len st.apps
    · have hb : i.val < st.apps.val.length := by simpa using hlt
      obtain ⟨x, hx1, hx2⟩ :=
        spec_imp_exists (alloc.vec.Vec.index_usize_spec st.apps i (by simpa using hb))
      rw [if_pos hlt]
      simp only [alloc.vec.Vec.index_slice_index, hx1, bind_tc_ok]
      rw [List.drop_eq_getElem_cons hb, List.map_cons, listFindIdx]
      by_cases hk : x.f = f ∧ x.a = a
      · rw [if_pos hk.1, if_pos hk.2]
        have hcast : (UScalar.cast .U32 i : U32).val = i.val := abs_cast_u32 i (by omega)
        obtain ⟨o, ho1, ho2⟩ :=
          abs_mk Generated.TAG_APP (UScalar.cast .U32 i)
            (by rw [tagapp]; simp [mTagApp]) (by rw [absU, hcast]; omega)
        simp only [lift, bind_tc_ok, ho1]
        refine ⟨some o, rfl, ?_⟩
        have hbeq : (((absU st.apps.val[i.val].f, absU st.apps.val[i.val].a))
            == ((absU f, absU a) : Nat × Nat)) = true := by rw [← hx2, hk.1, hk.2]; simp
        rw [if_pos hbeq]
        simp only [Option.map_some]
        rw [ho2, tagapp, absU, hcast]
      · obtain ⟨j, hj1, hj2⟩ :=
          usize_succ i (by scalar_tac)
        have hbeq : ¬ ((((absU st.apps.val[i.val].f, absU st.apps.val[i.val].a))
            == ((absU f, absU a) : Nat × Nat)) = true) := by
          rw [← hx2]; simp only [beq_iff_eq, Prod.mk.injEq]
          intro hc; exact hk ⟨absU_inj hc.1, absU_inj hc.2⟩
        rw [if_neg hbeq]
        by_cases hf : x.f = f
        · rw [if_pos hf, if_neg (fun hc => hk ⟨hf, hc⟩), hj1, bind_tc_ok, ← hj2]
          exact ih j (by omega)
        · rw [if_neg hf, hj1, bind_tc_ok, ← hj2]
          exact ih j (by omega)
    · have hb : st.apps.val.length ≤ i.val := by
        by_contra hc; exact hlt (by simpa using Nat.lt_of_not_le hc)
      rw [if_neg hlt]
      exact ⟨none, rfl, by rw [List.drop_eq_nil_of_le (by omega)]; rfl⟩

theorem abs_find_app (st : Generated.State) (hwf : GWF st) (f a : U32) :
    ∃ o : Option U32, Generated.find_app st f a = .ok o ∧
      mFindApp (absState st) (absU f) (absU a) = o.map absU := by
  obtain ⟨o, h1, h2⟩ := abs_find_app_from st hwf.apps f a st.apps.val.length 0#usize (by simp)
  exact ⟨o, h1, h2⟩

theorem abs_find_lam_from (st : Generated.State) (hwf : st.lams.val.length ≤ mIdxCap)
    (ty b : U32) : ∀ (n : Nat) (i : Usize), st.lams.val.length ≤ i.val + n →
    ∃ o : Option U32, Generated.find_lam_from st ty b i = .ok o ∧
      (listFindIdx ((st.lams.val.drop i.val).map (fun n => (absU n.ty, absU n.body)))
        (absU ty, absU b) i.val).map (mMk mTagLam) = o.map absU := by
  intro n
  induction n with
  | zero =>
    intro i hn
    rw [Generated.find_lam_from.eq_def]
    have hge : ¬ (i < alloc.vec.Vec.len st.lams) := by
      intro hc; have : i.val < st.lams.val.length := by simpa using hc
      omega
    rw [if_neg hge]
    exact ⟨none, rfl, by rw [List.drop_eq_nil_of_le (by omega)]; rfl⟩
  | succ n ih =>
    intro i hn
    rw [Generated.find_lam_from.eq_def]
    by_cases hlt : i < alloc.vec.Vec.len st.lams
    · have hb : i.val < st.lams.val.length := by simpa using hlt
      obtain ⟨x, hx1, hx2⟩ :=
        spec_imp_exists (alloc.vec.Vec.index_usize_spec st.lams i (by simpa using hb))
      rw [if_pos hlt]
      simp only [alloc.vec.Vec.index_slice_index, hx1, bind_tc_ok]
      rw [List.drop_eq_getElem_cons hb, List.map_cons, listFindIdx]
      by_cases hk : x.ty = ty ∧ x.body = b
      · rw [if_pos hk.1, if_pos hk.2]
        have hcast : (UScalar.cast .U32 i : U32).val = i.val := abs_cast_u32 i (by omega)
        obtain ⟨o, ho1, ho2⟩ :=
          abs_mk Generated.TAG_LAM (UScalar.cast .U32 i)
            (by rw [taglam]; simp [mTagLam]) (by rw [absU, hcast]; omega)
        simp only [lift, bind_tc_ok, ho1]
        refine ⟨some o, rfl, ?_⟩
        have hbeq : (((absU st.lams.val[i.val].ty, absU st.lams.val[i.val].body))
            == ((absU ty, absU b) : Nat × Nat)) = true := by rw [← hx2, hk.1, hk.2]; simp
        rw [if_pos hbeq]
        simp only [Option.map_some]
        rw [ho2, taglam, absU, hcast]
      · obtain ⟨j, hj1, hj2⟩ :=
          usize_succ i (by scalar_tac)
        have hbeq : ¬ ((((absU st.lams.val[i.val].ty, absU st.lams.val[i.val].body))
            == ((absU ty, absU b) : Nat × Nat)) = true) := by
          rw [← hx2]; simp only [beq_iff_eq, Prod.mk.injEq]
          intro hc; exact hk ⟨absU_inj hc.1, absU_inj hc.2⟩
        rw [if_neg hbeq]
        by_cases hf : x.ty = ty
        · rw [if_pos hf, if_neg (fun hc => hk ⟨hf, hc⟩), hj1, bind_tc_ok, ← hj2]
          exact ih j (by omega)
        · rw [if_neg hf, hj1, bind_tc_ok, ← hj2]
          exact ih j (by omega)
    · have hb : st.lams.val.length ≤ i.val := by
        by_contra hc; exact hlt (by simpa using Nat.lt_of_not_le hc)
      rw [if_neg hlt]
      exact ⟨none, rfl, by rw [List.drop_eq_nil_of_le (by omega)]; rfl⟩

theorem abs_find_lam (st : Generated.State) (hwf : GWF st) (ty b : U32) :
    ∃ o : Option U32, Generated.find_lam st ty b = .ok o ∧
      mFindLam (absState st) (absU ty) (absU b) = o.map absU := by
  obtain ⟨o, h1, h2⟩ := abs_find_lam_from st hwf.lams ty b st.lams.val.length 0#usize (by simp)
  exact ⟨o, h1, h2⟩


/-! ## Hash-consing

`intern_*` is where the capacity test lives, and where `GWF` is maintained.
The Rust tests `(len as u32) < IDX_CAP` and the twin tests `len < mIdxCap`;
under `GWF` the cast is exact, so the two tests agree — that equivalence is
the whole content of these three lemmas. -/

theorem abs_intern_bvar (st : Generated.State) (hwf : GWF st) (k : U32) :
    ∃ (o : Option U32) (st' : Generated.State),
      Generated.intern_bvar st k = .ok (o, st') ∧ GWF st' ∧
      ∀ r, o = some r →
        (mInternBvar (absU k)).run (absState st) = .ok (absU r, absState st') := by
  obtain ⟨of, hf1, hf2⟩ := abs_find_bvar st hwf k
  unfold Generated.intern_bvar
  rw [hf1, bind_tc_ok]
  cases of with
  | some h =>
    refine ⟨some h, st, rfl, hwf, ?_⟩
    intro r hr; cases hr
    rw [mInternBvar_run, hf2, Option.map_some]
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
        ⟨by rw [hv2]; simp; omega, hwf.apps, hwf.lams⟩, ?_⟩
      intro r hr; cases hr
      rw [mInternBvar_run, hf2, Option.map_none]
      have hlen : (absState st).bvars.length < mIdxCap := by
        simp only [absState, List.length_map]; exact hlt'
      rw [if_pos hlen, ho2, tagbvar]
      simp only [absState, hv2, List.map_append, List.map_cons, List.map_nil,
        List.length_map, hcast]
    · rw [if_neg hlt]
      exact ⟨none, st, rfl, hwf, by intro r hr; cases hr⟩

theorem abs_intern_app (st : Generated.State) (hwf : GWF st) (f a : U32) :
    ∃ (o : Option U32) (st' : Generated.State),
      Generated.intern_app st f a = .ok (o, st') ∧ GWF st' ∧
      ∀ r, o = some r →
        (mInternApp (absU f) (absU a)).run (absState st) = .ok (absU r, absState st') := by
  obtain ⟨of, hf1, hf2⟩ := abs_find_app st hwf f a
  unfold Generated.intern_app
  rw [hf1, bind_tc_ok]
  cases of with
  | some h =>
    refine ⟨some h, st, rfl, hwf, ?_⟩
    intro r hr; cases hr
    rw [mInternApp_run, hf2, Option.map_some]
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
        ⟨hwf.bvars, by rw [hv2]; simp; omega, hwf.lams⟩, ?_⟩
      intro r hr; cases hr
      rw [mInternApp_run, hf2, Option.map_none]
      have hlen : (absState st).apps.length < mIdxCap := by
        simp only [absState, List.length_map]; exact hlt'
      rw [if_pos hlen, ho2, tagapp]
      simp only [absState, hv2, List.map_append, List.map_cons, List.map_nil,
        List.length_map, hcast]
    · rw [if_neg hlt]
      exact ⟨none, st, rfl, hwf, by intro r hr; cases hr⟩

theorem abs_intern_lam (st : Generated.State) (hwf : GWF st) (ty b : U32) :
    ∃ (o : Option U32) (st' : Generated.State),
      Generated.intern_lam st ty b = .ok (o, st') ∧ GWF st' ∧
      ∀ r, o = some r →
        (mInternLam (absU ty) (absU b)).run (absState st) = .ok (absU r, absState st') := by
  obtain ⟨of, hf1, hf2⟩ := abs_find_lam st hwf ty b
  unfold Generated.intern_lam
  rw [hf1, bind_tc_ok]
  cases of with
  | some h =>
    refine ⟨some h, st, rfl, hwf, ?_⟩
    intro r hr; cases hr
    rw [mInternLam_run, hf2, Option.map_some]
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
        ⟨hwf.bvars, hwf.apps, by rw [hv2]; simp; omega⟩, ?_⟩
      intro r hr; cases hr
      rw [mInternLam_run, hf2, Option.map_none]
      have hlen : (absState st).lams.length < mIdxCap := by
        simp only [absState, List.length_map]; exact hlt'
      rw [if_pos hlen, ho2, taglam]
      simp only [absState, hv2, List.map_append, List.map_cons, List.map_nil,
        List.length_map, hcast]
    · rw [if_neg hlt]
      exact ⟨none, st, rfl, hwf, by intro r hr; cases hr⟩

/-! ## The memo -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:81 instantiate1Go — the probe, at
an offset: the shape the Rust's index-carrying recursion has. -/
def mMemoGetFrom (st : MState) (h d i : Nat) : Option Nat :=
  match listFindIdx ((st.memo.map (fun e => (e.1, e.2.1))).drop i) (h, d) i with
  | none => none
  | some j => (st.memo[j]?).map (fun e => e.2.2)

theorem mMemoGetFrom_zero (st : MState) (h d : Nat) :
    mMemoGetFrom st h d 0 = mMemoGet st h d := rfl

theorem mMemoGetFrom_abs (st : Generated.State) (h d : U32) (i : Nat) :
    mMemoGetFrom (absState st) (absU h) (absU d) i
      = match listFindIdx ((st.memo.val.drop i).map (fun e => (absU e.key_h, absU e.key_d)))
                (absU h, absU d) i with
        | none => none
        | some j => (st.memo.val[j]?).map (fun e => absU e.val) := by
  simp only [mMemoGetFrom, absState, List.map_map, ← List.map_drop, Function.comp_def]
  cases listFindIdx ((st.memo.val.drop i).map (fun e => (absU e.key_h, absU e.key_d)))
      (absU h, absU d) i with
  | none => rfl
  | some j => simp only [List.getElem?_map, Option.map_map, Function.comp_def]

theorem abs_memo_get_from (st : Generated.State) (h d : U32) :
    ∀ (n : Nat) (i : Usize), st.memo.val.length ≤ i.val + n →
    ∃ o : Option U32, Generated.memo_get_from st h d i = .ok o ∧
      mMemoGetFrom (absState st) (absU h) (absU d) i.val = o.map absU := by
  intro n
  induction n with
  | zero =>
    intro i hn
    rw [Generated.memo_get_from.eq_def]
    have hge : ¬ (i < alloc.vec.Vec.len st.memo) := by
      intro hc; have : i.val < st.memo.val.length := by simpa using hc
      omega
    rw [if_neg hge]
    exact ⟨none, rfl, by rw [mMemoGetFrom_abs, List.drop_eq_nil_of_le (by omega)]; rfl⟩
  | succ n ih =>
    intro i hn
    rw [Generated.memo_get_from.eq_def]
    by_cases hlt : i < alloc.vec.Vec.len st.memo
    · have hb : i.val < st.memo.val.length := by simpa using hlt
      obtain ⟨x, hx1, hx2⟩ :=
        spec_imp_exists (alloc.vec.Vec.index_usize_spec st.memo i (by simpa using hb))
      rw [if_pos hlt]
      simp only [alloc.vec.Vec.index_slice_index, hx1, bind_tc_ok]
      rw [mMemoGetFrom_abs, List.drop_eq_getElem_cons hb, List.map_cons, listFindIdx]
      by_cases hk : x.key_h = h ∧ x.key_d = d
      · rw [if_pos hk.1, if_pos hk.2]
        refine ⟨some x.val, rfl, ?_⟩
        have hbeq : ((absU st.memo.val[i.val].key_h, absU st.memo.val[i.val].key_d)
            == ((absU h, absU d) : Nat × Nat)) = true := by rw [← hx2, hk.1, hk.2]; simp
        rw [if_pos hbeq]
        simp only [List.getElem?_eq_getElem hb, Option.map_some, ← hx2]
      · have hbeq : ¬ (((absU st.memo.val[i.val].key_h, absU st.memo.val[i.val].key_d)
            == ((absU h, absU d) : Nat × Nat)) = true) := by
          rw [← hx2]; simp only [beq_iff_eq, Prod.mk.injEq]
          intro hc; exact hk ⟨absU_inj hc.1, absU_inj hc.2⟩
        obtain ⟨j, hj1, hj2⟩ :=
          usize_succ i (by scalar_tac)
        obtain ⟨o, ho1, ho2⟩ := ih j (by omega)
        rw [mMemoGetFrom_abs, hj2] at ho2
        rw [if_neg hbeq]
        by_cases hf : x.key_h = h
        · exact ⟨o, by rw [if_pos hf, if_neg (fun hc => hk ⟨hf, hc⟩), hj1, bind_tc_ok, ho1], ho2⟩
        · exact ⟨o, by rw [if_neg hf, hj1, bind_tc_ok, ho1], ho2⟩
    · have hb : st.memo.val.length ≤ i.val := by
        by_contra hc; exact hlt (by simpa using Nat.lt_of_not_le hc)
      rw [if_neg hlt]
      exact ⟨none, rfl, by rw [mMemoGetFrom_abs, List.drop_eq_nil_of_le (by omega)]; rfl⟩

theorem abs_memo_get (st : Generated.State) (h d : U32) :
    ∃ o : Option U32, Generated.memo_get st h d = .ok o ∧
      mMemoGet (absState st) (absU h) (absU d) = o.map absU := by
  obtain ⟨o, h1, h2⟩ := abs_memo_get_from st h d st.memo.val.length 0#usize (by simp)
  exact ⟨o, h1, by rw [← mMemoGetFrom_zero]; simpa using h2⟩

/-- con-leche: none — `Vec::push` inverted: it only fails at `Usize.max`, and
the caller is told it did not. -/
theorem vec_push_inv {α : Type} (v w : alloc.vec.Vec α) (x : α)
    (h : v.push x = .ok w) : w.val = v.val ++ [x] := by
  unfold alloc.vec.Vec.push at h
  dsimp only at h
  split at h
  · rw [Result.ok.injEq] at h; subst h; simp
  · simp at h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:116 instantiate1Go — the memo
insert.  Stated by inversion: Aeneas models `Vec::push` as failing at
`Usize.max`, and `GWF` does not bound the memo (the fuel does), so the
success is a hypothesis rather than a conclusion. -/
theorem abs_memo_set (st st' : Generated.State) (h d r : U32)
    (hr : Generated.memo_set st h d r = .ok st') :
    absState st' = { absState st with
      memo := (absState st).memo ++ [(absU h, absU d, absU r)] } ∧
      (GWF st → GWF st') := by
  unfold Generated.memo_set at hr
  cases hp : alloc.vec.Vec.push st.memo
      ({ key_h := h, key_d := d, val := r } : Generated.MemoEntry) using Result.cases with
  | ret v =>
    rw [hp, bind_tc_ok, Result.ok.injEq] at hr
    subst hr
    have hv := vec_push_inv _ _ _ hp
    refine ⟨?_, fun hw => ⟨hw.bvars, hw.apps, hw.lams⟩⟩
    simp only [absState, hv, List.map_append, List.map_cons, List.map_nil]
  | vis e k => rw [hp] at hr; simp at hr
  | div => rw [hp] at hr; simp at hr

end ConRon.Arena.Spike

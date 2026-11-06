/-
# `ConRon.Refine2.Frontend.Olean.Spec` — `olean/spec.rs` against `Arena/Frontend/Olean/Spec.lean`

**Task #142, Theorem 2.**  The node functions, in lockstep with the twin's, intern for
intern; the pointer reads through `Sub` and `PtrRead`; the skeletons against upstream's.
-/
import ConRon.Refine2.Frontend.Olean.Shape

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.region (region_fld region_down region_tag region_nobjs region_fits
  region_str_p region_nat_sat region_nat_p region_is_ctor)
open frontend.olean.spec (name_in level_in levels_in expr_in nat_word name_tail name_node
  name_shape level_node level_bin levels_cons levels_cons_loop levels_node lit_p)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Arena.Frontend.Olean (Sub nameIn levelIn levelsIn exprIn natWord wordMax nameTail
  nameNode levelNode levelsCons levelsNode exprNode litP nameAt nameP)
open ConRon.Refine.HashMap (uscalar_add_eq)

/-! ## `Sub` -/

/-- **A `Sub` instance's answers are a twin `Sub`'s**, answer for answer. -/
structure SubRel {S : Type} (inst : frontend.olean.spec.Sub S) (s : S) (t : Sub) : Prop where
  nm : ∀ c o, inst.sub_name s c = ok o → o.map absNIdx = t.name c.val
  lv : ∀ c o, inst.sub_level s c = ok o → o.map absLIdx = t.level c.val
  lvs : ∀ c o, inst.sub_levels s c = ok o → o.map absLsIdx = t.levels c.val
  ex : ∀ c o, inst.sub_expr s c = ok o → o.map absEIdx = t.expr c.val

theorem fld_0 {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g x : Std.U64}
    (h : region_fld bs g 0#u64 = ok x) : (absRegion bs r).fld g.val 0 = absWord x :=
  (region_fld_eq bs h).symm

theorem fld_1 {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g x : Std.U64}
    (h : region_fld bs g 1#u64 = ok x) : (absRegion bs r).fld g.val 1 = absWord x :=
  (region_fld_eq bs h).symm

theorem fld_2 {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g x : Std.U64}
    (h : region_fld bs g 2#u64 = ok x) : (absRegion bs r).fld g.val 2 = absWord x :=
  (region_fld_eq bs h).symm

theorem fld_3 {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g x : Std.U64}
    (h : region_fld bs g 3#u64 = ok x) : (absRegion bs r).fld g.val 3 = absWord x :=
  (region_fld_eq bs h).symm

theorem word_eq_one {v : Std.U64} : (absWord v == 1) = true ↔ v = 1#u64 := by
  rw [beq_iff_eq]
  constructor
  · intro he
    have := congrArg UInt64.toNat he
    rw [absWord_toNat] at this
    exact UScalar.eq_of_val_eq (by rw [this]; rfl)
  · intro he; rw [he]; rfl

/-- **`name_in` is `nameIn`.** -/
theorem name_in_eq {S : Type} {inst : frontend.olean.spec.Sub S} {s : S} {t : Sub} (bs : Slice Std.U8)
    (hs : SubRel inst s t) {pk r g v o} (h : name_in inst pk r g v s = ok o) :
    RdP (EqA absNIdx) o (nameIn (absPins pk) (absRegion bs r) g.val (absWord v) t) := by
  rw [name_in] at h
  simp only [nameIn]
  split at h
  · rename_i hv
    peel h as n, hn
    cases Result.ok_injective h
    rw [nidx_dup2_ok hn, ite_eq_left (word_eq_one.mpr hv)]
    exact ⟨_, rfl, rfl⟩
  · rename_i hv
    rw [ite_eq_right (fun he => hv (word_eq_one.mp he))]
    peel h as o1, ho1
    rw [← region_down_eq bs ho1]
    cases o1 with
    | none => cases Result.ok_injective h; rfl
    | some c =>
      dsimp only at h
      peel h as o2, ho2
      have e := hs.nm c o2 ho2
      simp only [locOf, Option.map_some, ← e]
      cases o2 with
      | none => cases Result.ok_injective h; rfl
      | some x => cases Result.ok_injective h; exact ⟨_, rfl, rfl⟩

/-- **`level_in` is `levelIn`.** -/
theorem level_in_eq {S : Type} {inst : frontend.olean.spec.Sub S} {s : S} {t : Sub} (bs : Slice Std.U8)
    (hs : SubRel inst s t) {pk r g v o} (h : level_in inst pk r g v s = ok o) :
    RdP (EqA absLIdx) o (levelIn (absPins pk) (absRegion bs r) g.val (absWord v) t) := by
  rw [level_in] at h
  simp only [levelIn]
  split at h
  · rename_i hv
    peel h as n, hn
    cases Result.ok_injective h
    rw [lidx_dup2_ok hn, ite_eq_left (word_eq_one.mpr hv)]
    exact ⟨_, rfl, rfl⟩
  · rename_i hv
    rw [ite_eq_right (fun he => hv (word_eq_one.mp he))]
    peel h as o1, ho1
    rw [← region_down_eq bs ho1]
    cases o1 with
    | none => cases Result.ok_injective h; rfl
    | some c =>
      dsimp only at h
      peel h as o2, ho2
      have e := hs.lv c o2 ho2
      simp only [locOf, Option.map_some, ← e]
      cases o2 with
      | none => cases Result.ok_injective h; rfl
      | some x => cases Result.ok_injective h; exact ⟨_, rfl, rfl⟩

/-- **`levels_in` is `levelsIn`.** -/
theorem levels_in_eq {S : Type} {inst : frontend.olean.spec.Sub S} {s : S} {t : Sub} (bs : Slice Std.U8)
    (hs : SubRel inst s t) {pk r g v o} (h : levels_in inst pk r g v s = ok o) :
    RdP (EqA absLsIdx) o (levelsIn (absPins pk) (absRegion bs r) g.val (absWord v) t) := by
  rw [levels_in] at h
  simp only [levelsIn]
  split at h
  · rename_i hv
    peel h as n, hn
    cases Result.ok_injective h
    rw [lsidx_dup2_ok hn, ite_eq_left (word_eq_one.mpr hv)]
    exact ⟨_, rfl, rfl⟩
  · rename_i hv
    rw [ite_eq_right (fun he => hv (word_eq_one.mp he))]
    peel h as o1, ho1
    rw [← region_down_eq bs ho1]
    cases o1 with
    | none => cases Result.ok_injective h; rfl
    | some c =>
      dsimp only at h
      peel h as o2, ho2
      have e := hs.lvs c o2 ho2
      simp only [locOf, Option.map_some, ← e]
      cases o2 with
      | none => cases Result.ok_injective h; rfl
      | some x => cases Result.ok_injective h; exact ⟨_, rfl, rfl⟩

/-- **`expr_in` is `exprIn`.** -/
theorem expr_in_eq {S : Type} {inst : frontend.olean.spec.Sub S} {s : S} {t : Sub} (bs : Slice Std.U8)
    (hs : SubRel inst s t) {r g v o} (h : expr_in inst r g v s = ok o) :
    RdP (EqA absEIdx) o (exprIn (absRegion bs r) g.val (absWord v) t) := by
  rw [expr_in] at h
  simp only [exprIn]
  peel h as o1, ho1
  rw [← region_down_eq bs ho1]
  cases o1 with
  | none => cases Result.ok_injective h; rfl
  | some c =>
    dsimp only at h
    peel h as o2, ho2
    have e := hs.ex c o2 ho2
    simp only [locOf, Option.map_some, ← e]
    cases o2 with
    | none => cases Result.ok_injective h; rfl
    | some x => cases Result.ok_injective h; exact ⟨_, rfl, rfl⟩

/-! ## The numbers of a node -/

/-- **`nat_word` is `natWord`.**  The word and its `Nat` agree below the saturation
point; at it, both decline. -/
theorem nat_word_eq {k : Std.U64} {n : Nat} {o} (hs : SatRel k n) (h : nat_word k = ok o) {lst} :
    match o with
    | .Ok i => i.val = n ∧ (natWord n).run lst = .ok (n, lst)
    | .Err .Bad => False
    | .Err (.Err e) => AErrSim e ((natWord n).run lst) := by
  rw [nat_word] at h
  have hw : wordMax = 2 ^ 64 - 1 := rfl
  split at h
  · rename_i hk
    peel h as s, -
    peel h as v, -
    peel h as ce, hce
    cases Result.ok_injective h
    rw [kernel.core_types.native] at hce
    cases Result.ok_injective hce
    simp only [natWord]
    rw [ite_eq_left (by rw [hw]; exact hs.max_iff.mp hk)]
    exact AErrSim.mk rfl rfl
  · rename_i hk
    cases Result.ok_injective h
    have hn : ¬ wordMax ≤ n := by rw [hw]; exact fun he => hk (hs.max_iff.mpr he)
    simp only [natWord]
    rw [ite_eq_right hn]
    exact ⟨hs.val_of_ne hk, rfl⟩

/-! ## `nameTail`, `nameNode` -/

theorem region_str_at_wf {bs : Slice Std.U8} {r : frontend.olean.region.Region} {c : Std.U64}
    {o : Option (alloc.vec.Vec Std.U32)} (h : frontend.olean.region.region_str_at bs r c = ok o) :
    ∀ s, o = some s → ConRon.Refine.StrWF s := by
  rw [frontend.olean.region.region_str_at] at h
  peel h as t, -
  split at h
  · peel h as i1, -
    peel h as sz, -
    peel h as fe, -
    split at h
    · peel h as i2, -
      peel h as i3, -
      split at h
      · peel h as i4, -
        peel h as i5, -
        peel h as i6, -
        split at h
        · simp only [lift, bind_ok] at h
          peel h as i8, -
          peel h as i9, -
          intro s hs
          subst hs
          exact utf8_decode_wf h
        · cases Result.ok_injective h; intro s hs; cases hs
      · cases Result.ok_injective h; intro s hs; cases hs
    · cases Result.ok_injective h; intro s hs; cases hs
  · cases Result.ok_injective h; intro s hs; cases hs

theorem region_str_p_wf {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g v : Std.U64}
    {o : Option (alloc.vec.Vec Std.U32)} (h : region_str_p bs r g v = ok o) :
    ∀ s, o = some s → ConRon.Refine.StrWF s := by
  rw [region_str_p] at h
  peel h as o1, -
  cases o1 with
  | none => cases Result.ok_injective h; intro s hs; cases hs
  | some c => exact region_str_at_wf h

/-- **`name_tail` is `nameTail`.** -/
theorem name_tail_refines {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g t : Std.U64}
    {p : arena.handle.NIdx} {pers st lst} (hr : RegionFits bs r) :
    RS pers (EqA absNIdx) st lst (name_tail pers st.store bs r g t p)
      (nameTail (absRegion bs r) g.val t.val (absNIdx p)) := by
  rw [name_tail]
  simp only [nameTail]
  by_cases ht : t = 1#u64
  · have l : t.val = 1 := by rw [ht]; rfl
    rw [ite_eq_left ht, ite_eq_left (by rw [l]; rfl)]
    refine RS.pure_step fun i hi => RS.pure_step fun o ho => ?_
    rw [fld_1 hi, ← region_str_p_eq hr ho]
    cases o with
    | none => exact RS.none
    | some s => exact RS.intern_name (region_str_p_wf ho s rfl)
  · have l : t.val ≠ 1 := fun he => ht (UScalar.eq_of_val_eq (by rw [he]; rfl))
    rw [ite_eq_right ht, ite_eq_right (by simpa using l)]
    refine RS.pure_step fun i hi => RS.pure_step fun o ho => ?_
    rw [fld_1 hi]
    have hn := region_nat_sat_eq (bs := bs) (r := r) ho
    revert hn
    generalize (absRegion bs r).natP g.val (absWord i) = y
    intro hn
    cases hn with
    | none => exact RS.none
    | some hs =>
      rename_i k n
      refine RS.pure_step fun o1 ho1 => ?_
      intro hrel hinv o2 s' hm
      have hw := nat_word_eq hs ho1 (lst := lst)
      cases o1 with
      | Ok i2 =>
        obtain ⟨hv, hrun⟩ := hw
        subst hv
        rw [am_bind_ok hrun]
        exact RS.intern_name (v := .Num p i2) trivial hrel hinv o2 s' hm
      | Err e =>
        cases Result.ok_injective hm
        cases e with
        | Bad => exact hw.elim
        | Err ce =>
          show AErrSim ce _
          rw [StateT.run_bind]
          exact AErrSim.bind hw _

/-- `name_shape`, the test of `nameNode`. -/
theorem name_shape_eq {t n : Std.U64} {b : Bool} (h : name_shape t n = ok b) :
    b = ((t.val == 1 || t.val == 2) && n.val == 2) := by
  rw [name_shape] at h
  have l1 : (1#u64 : Std.U64).val = 1 := by decide
  have l2 : (2#u64 : Std.U64).val = 2 := by decide
  have en : decide (n = 2#u64) = (n.val == 2) := by
    by_cases h3 : n = 2#u64
    · simp [h3, l2]
    · have : n.val ≠ 2 := fun he => h3 (UScalar.eq_of_val_eq (by rw [he, l2]))
      simp [h3, this]
  split at h
  · rename_i h1
    cases Result.ok_injective h
    simp [h1, l1, en]
  · rename_i h1
    have h1' : t.val ≠ 1 := fun he => h1 (UScalar.eq_of_val_eq (by rw [he, l1]))
    split at h
    · rename_i h2
      cases Result.ok_injective h
      simp [h2, l2, en]
    · rename_i h2
      have h2' : t.val ≠ 2 := fun he => h2 (UScalar.eq_of_val_eq (by rw [he, l2]))
      cases Result.ok_injective h
      simp [h1', h2']

/-- **`name_node` is `nameNode`.** -/
theorem name_node_refines {S : Type} {inst : frontend.olean.spec.Sub S} {s : S} {tt : Sub}
    {pk bs r g pers st lst} (hr : RegionFits bs r) (hs : SubRel inst s tt) :
    RS pers (EqA absNIdx) st lst (name_node inst pk pers st.store bs r g s)
      (nameNode (absPins pk) (absRegion bs r) g.val tt) := by
  rw [name_node]
  simp only [nameNode]
  refine RS.pure_step fun b hb => ?_
  rw [← region_fits_eq bs hb]
  split
  · refine RS.pure_step fun t ht => RS.pure_step fun i hi => RS.pure_step fun b1 hb2 => ?_
    rw [← region_tag_eq bs ht, ← region_nobjs_eq bs hi, ← name_shape_eq hb2]
    split
    · refine RS.pure_step fun i1 hi1 => RS.pure_step fun r1 hr1 => ?_
      rw [fld_0 hi1]
      have e := name_in_eq bs hs hr1
      cases r1 with
      | Ok p =>
        obtain ⟨b, hy, rfl⟩ := e
        rw [hy]
        exact name_tail_refines hr
      | Err e1 =>
        cases e1 with
        | Bad => rw [show _ = Option.none from e]; exact RS.none
        | Err _ => exact e.elim
    · exact RS.none
  · exact RS.none

/-! ## `levelNode` -/

theorem u64_lit_ne {n : Std.U64} {k : Std.U64} (h : ¬ n = k) : n.val ≠ k.val :=
  fun he => h (UScalar.eq_of_val_eq he)

/-- A `levelIn`'s outcome splits. -/
theorem rs_rd_elim {α β : Type} {P : Prop} {o : core.result.Result α frontend.olean.spec.RdErr}
    {y : Option β} {R : α → β → Prop} (h : RdP R o y)
    (hok : ∀ a b, o = .Ok a → y = Option.some b → R a b → P)
    (hbad : o = .Err .Bad → y = Option.none → P) : P := by
  cases o with
  | Ok a => obtain ⟨b, hy, hr⟩ := h; exact hok a b rfl hy hr
  | Err e =>
    cases e with
    | Bad => exact hbad rfl h
    | Err _ => exact h.elim

/-- **`level_bin` is the `max` and `imax` arms of `levelNode`.** -/
theorem level_bin_refines {S : Type} {inst : frontend.olean.spec.Sub S} {s : S} {tt : Sub}
    {pk bs r g n pers st lst} {imax : Bool} (hs : SubRel inst s tt) :
    RS pers (EqA absLIdx) st lst (level_bin inst pk pers st.store bs r g n imax s)
      (if n.val = 2 then
        match levelIn (absPins pk) (absRegion bs r) g.val ((absRegion bs r).fld g.val 0) tt,
          levelIn (absPins pk) (absRegion bs r) g.val ((absRegion bs r).fld g.val 1) tt with
        | Option.some u, Option.some v =>
          do pure (Option.some (← internLNode (if imax then .imax u v else .max u v)))
        | _, _ => pure Option.none
      else pure Option.none) := by
  have l2 : (2#u64 : Std.U64).val = 2 := by decide
  rw [level_bin]
  by_cases hn : n = 2#u64
  · simp only [hn, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, l2]
    refine RS.pure_step fun i hi => RS.pure_step fun r1 hr1 => ?_
    rw [fld_0 hi]
    refine rs_rd_elim (level_in_eq bs hs hr1) (fun a b hA hy hR => ?_) (fun hA hy => ?_)
    · subst hA; rw [hy]; cases hR
      dsimp only
      refine RS.pure_step fun i1 hi1 => RS.pure_step fun r2 hr2 => ?_
      rw [fld_1 hi1]
      refine rs_rd_elim (level_in_eq bs hs hr2) (fun a2 b2 hA2 hy2 hR2 => ?_) (fun hA2 hy2 => ?_)
      · subst hA2; rw [hy2]; cases hR2
        dsimp only
        cases imax with
        | true => exact RS.intern_level (v := .Imax a a2)
        | false => exact RS.intern_level (v := .Max a a2)
      · subst hA2; rw [hy2]; exact RS.none
    · subst hA; rw [hy]; exact RS.none
  · have : (n != 2#u64) = true := by simpa using hn
    rw [ite_eq_left this, ite_eq_right (by rw [← l2]; exact u64_lit_ne hn)]
    exact RS.none

/-- **`level_node` is `levelNode`.** -/
theorem level_node_refines {S : Type} {inst : frontend.olean.spec.Sub S} {s : S} {tt : Sub}
    {pk bs r g pers st lst} (hs : SubRel inst s tt) :
    RS pers (EqA absLIdx) st lst (level_node inst pk pers st.store bs r g s)
      (levelNode (absPins pk) (absRegion bs r) g.val tt) := by
  rw [level_node]
  simp only [levelNode]
  refine RS.pure_step fun b hb => ?_
  rw [← region_fits_eq bs hb]
  split
  · refine RS.pure_step fun n hn => RS.pure_step fun t ht => ?_
    rw [← region_tag_eq bs ht, ← region_nobjs_eq bs hn]
    split
    · trace_state
      sorry
    all_goals sorry
  · exact RS.none

end ConRon.Refine2.Frontend.Olean

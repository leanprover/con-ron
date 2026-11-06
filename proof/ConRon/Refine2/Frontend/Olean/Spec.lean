/-
# `ConRon.Refine2.Frontend.Olean.Spec` — `olean/spec.rs` against `Arena/Frontend/Olean/Spec.lean`

**Task #142, Theorem 2.**  The node functions, in lockstep with the twin's, intern for
intern; the pointer reads through `Sub` and `PtrRead`; the skeletons against upstream's.
-/
import ConRon.Refine2.Frontend.Olean.Skel

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
open ConRon.Refine.ExprOps (with_capacity_val)

/-! ## `Sub` -/

/-- **A `Sub` instance's answers are a twin `Sub`'s**, answer for answer. -/
structure SubRel {S : Type} (inst : frontend.olean.spec.Sub S) (s : S) (t : Sub) : Prop where
  nm : ∀ c o, inst.sub_name s c = ok o → o.map absNIdx = t.name c.val
  lv : ∀ c o, inst.sub_level s c = ok o → o.map absLIdx = t.level c.val
  lvs : ∀ c o, inst.sub_levels s c = ok o → o.map absLsIdx = t.levels c.val
  ex : ∀ c o, inst.sub_expr s c = ok o → o.map absEIdx = t.expr c.val

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

/-- The twin's match on `(tag, nobjs)` at a number of fields the arm does not have: its
last arm, or what `e` proves. -/
macro "twin_arm " n:ident hv:ident e:term : tactic =>
  `(tactic| (generalize UScalar.val $n:ident = N at *
             rcases N with _ | _ | _ | _ | _ | N <;>
               first | exact absurd rfl $hv:ident | exact $e))

/-- The value a `RdP` answers, or the twin's `none`. -/
macro "rd_step " e:term " as " a:ident : tactic =>
  `(tactic| (refine rs_rd_elim $e (fun $a:ident b hA hy hR => ?_)
               (fun hA hy => by subst hA; rw [hy]; exact RS.none)
             subst hA; rw [hy]; cases hR; try dsimp only))

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
    · by_cases hN : n = 0#u64
      · subst hN
        rw [ite_eq_left rfl]
        refine RS.pure_step fun l hl => ?_
        rw [lidx_dup2_ok hl]
        exact RS.some rfl
      · rw [ite_eq_right hN]
        have hv := u64_lit_ne hN
        twin_arm n hv RS.none
    · by_cases hN : n = 1#u64
      · subst hN
        rw [ite_eq_left rfl]
        refine RS.pure_step fun i hi => RS.pure_step fun r1 hr1 => ?_
        show RS _ _ _ _ _ (match levelIn _ _ _ ((absRegion bs r).fld _ 0) tt with
          | none => pure none
          | some u => do pure (some (← internLNode (.succ u))))
        rw [fld_0 hi]
        rd_step (level_in_eq bs hs hr1) as a
        exact RS.intern_level (v := .Succ a)
      · rw [ite_eq_right hN]
        have hv := u64_lit_ne hN
        twin_arm n hv RS.none
    · have h := level_bin_refines (imax := false) (pk := pk) (bs := bs) (r := r) (g := g) (n := n)
        (pers := pers) (st := st) (lst := lst) hs
      by_cases hN : n = 2#u64
      · subst hN
        rw [ite_eq_left (by decide)] at h
        exact h
      · rw [ite_eq_right (by rw [show (2 : Nat) = (2#u64 : Std.U64).val from rfl]; exact u64_lit_ne hN)] at h
        have hv := u64_lit_ne hN
        twin_arm n hv h
    · have h := level_bin_refines (imax := true) (pk := pk) (bs := bs) (r := r) (g := g) (n := n)
        (pers := pers) (st := st) (lst := lst) hs
      by_cases hN : n = 2#u64
      · subst hN
        rw [ite_eq_left (by decide)] at h
        exact h
      · rw [ite_eq_right (by rw [show (2 : Nat) = (2#u64 : Std.U64).val from rfl]; exact u64_lit_ne hN)] at h
        have hv := u64_lit_ne hN
        twin_arm n hv h
    · by_cases hN : n = 1#u64
      · subst hN
        rw [ite_eq_left rfl]
        refine RS.pure_step fun i hi => RS.pure_step fun r1 hr1 => ?_
        show RS _ _ _ _ _ (match nameIn _ _ _ ((absRegion bs r).fld _ 0) tt with
          | none => pure none
          | some n => do pure (some (← internLNode (.param n))))
        rw [fld_0 hi]
        rd_step (name_in_eq bs hs hr1) as a
        exact RS.intern_level (v := .Param a)
      · rw [ite_eq_right hN]
        have hv := u64_lit_ne hN
        twin_arm n hv RS.none
    · rename_i h0 h1 h2 h3 h4
      have e0 : t.val ≠ 0 := fun he => h0 (UScalar.eq_of_val_eq he)
      have e1 : t.val ≠ 1 := fun he => h1 (UScalar.eq_of_val_eq he)
      have e2 : t.val ≠ 2 := fun he => h2 (UScalar.eq_of_val_eq he)
      have e3 : t.val ≠ 3 := fun he => h3 (UScalar.eq_of_val_eq he)
      have e4 : t.val ≠ 4 := fun he => h4 (UScalar.eq_of_val_eq he)
      generalize UScalar.val t = T at e0 e1 e2 e3 e4 ⊢
      rcases T with _ | _ | _ | _ | _ | T
      · exact absurd rfl e0
      · exact absurd rfl e1
      · exact absurd rfl e2
      · exact absurd rfl e3
      · exact absurd rfl e4
      · exact RS.none
  · exact RS.none

/-! ## `levelsNode` -/

/-- `levels_cons_loop` appends the rest of the list. -/
theorem levels_cons_loop_val {rest : alloc.vec.Vec arena.handle.LIdx} :
    ∀ (k : Nat) (i : Std.Usize) (out r : alloc.vec.Vec arena.handle.LIdx),
      rest.val.length - i.val ≤ k → levels_cons_loop rest out i = ok r →
        r.val = out.val ++ rest.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro i out r hk h
    rw [levels_cons_loop] at h
    rw [ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
  | succ k ih =>
    intro i out r hk h
    rw [levels_cons_loop] at h
    by_cases hi : i < alloc.vec.Vec.len rest
    · rw [ite_eq_left hi] at h
      have hlt : i.val < rest.val.length := by scalar_tac
      peel h as l, hl
      peel h as l1, hl1
      peel h as out1, ho
      peel h as i2, hi2
      have hv := ConRon.Refine.ExprOps.vec_index_getElem? hl
      have hiv := uscalar_add_eq hi2
      rw [ih i2 out1 r (by scalar_tac) h, ConRon.Refine.vec_push_val ho, lidx_dup2_ok hl1,
        List.drop_eq_getElem_cons hlt, hiv]
      have : rest.val[i.val] = l := by
        rw [List.getElem?_eq_getElem hlt] at hv; exact Option.some.inj hv
      simp [this]
    · rw [ite_eq_right hi] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by scalar_tac), List.append_nil]

/-- **`levels_cons` is `levelsCons`.** -/
theorem levels_cons_refines {pers st lst} {u : arena.handle.LIdx} {us : arena.handle.LsIdx} :
    RS pers (EqA absLsIdx) st lst (levels_cons pers st.store u us)
      (levelsCons (absLIdx u) (absLsIdx us)) := by
  intro hrel hinv o s' h
  rw [levels_cons] at h
  simp only [levelsCons]
  peel h as ls, hls
  rw [arena.store.EStore.ls_s] at hls
  have hn2 : ls = st.store.lss := (Result.ok_injective hls).symm
  subst hn2
  peel h as v, hv
  have hview := lsstore_view_abs hrel.store.lss hv
  have hrunl : (viewLs (absLsIdx us)).run lst
      = match lst.store.lss.view (absLsIdx us) with
        | some x => Except.ok (x, lst)
        | none => Except.error (.internal "arena: dangling level-list handle") := by
    show (match lst.store.lss.view (absLsIdx us) with
          | some v => (pure v : AM _)
          | none => Arena.fail (.internal "arena: dangling level-list handle")).run lst = _
    cases lst.store.lss.view (absLsIdx us) <;> rfl
  cases v with
  | none =>
    rw [hview] at hrunl
    peel h as r0, hr0
    peel h as r1, hr1
    rw [arena.monad.fail_dangling_ls] at hr0
    peel hr0 as s0, -
    peel hr0 as v0, -
    have e := fail_run hr0
    subst e
    cases Result.ok_injective (show ok (.Err (.Err (.Internal v0))) = ok r1 from hr1)
    cases Result.ok_injective h
    show AErrSim _ _
    rw [StateT.run_bind, hrunl]
    exact AErrSim.internal rfl
  | some rest =>
    rw [hview] at hrunl
    dsimp only at h
    peel h as i1, -
    peel h as out1, ho1
    peel h as out2, ho2
    have hval := levels_cons_loop_val _ _ _ _ (Nat.le_refl _) ho2
    rw [ConRon.Refine.vec_push_val ho1] at hval
    simp only [with_capacity_val, List.nil_append, List.singleton_append] at hval
    have hb : (viewLs (absLsIdx us)).run lst = .ok (absLsNodeView rest, lst) := hrunl
    rw [am_bind_ok hb]
    have hv' : absLsNodeView out2 = absLIdx u :: absLsNodeView rest := by
      simp [absLsNodeView, hval]
    rw [← hv']
    exact RS.intern_levels hrel hinv o s' h

/-- **`levels_node` is `levelsNode`.** -/
theorem levels_node_refines {S : Type} {inst : frontend.olean.spec.Sub S} {s : S} {tt : Sub}
    {pk bs r g pers st lst} (hs : SubRel inst s tt) :
    RS pers (EqA absLsIdx) st lst (levels_node inst pk pers st.store bs r g s)
      (levelsNode (absPins pk) (absRegion bs r) g.val tt) := by
  rw [levels_node]
  simp only [levelsNode]
  refine RS.pure_step fun b hb => ?_
  rw [← region_fits_eq bs hb]
  split
  · refine RS.pure_step fun t ht => ?_
    rw [← region_tag_eq bs ht]
    by_cases hT : t = 1#u64
    · subst hT
      rw [ite_eq_left rfl]
      refine RS.pure_step fun n hn => ?_
      rw [← region_nobjs_eq bs hn]
      by_cases hN : n = 2#u64
      · subst hN
        rw [ite_eq_left rfl, ite_eq_left (by decide)]
        refine RS.pure_step fun i hi => RS.pure_step fun r1 hr1 => ?_
        rw [fld_0 hi]
        rd_step (level_in_eq bs hs hr1) as a
        refine RS.pure_step fun i1 hi1 => RS.pure_step fun r2 hr2 => ?_
        rw [fld_1 hi1]
        rd_step (levels_in_eq bs hs hr2) as a1
        exact levels_cons_refines
      · have hv := u64_lit_ne hN
        rw [ite_eq_right hN, ite_eq_right (by
          intro he
          simp only [Bool.and_eq_true, beq_iff_eq] at he
          exact hv he.2)]
        exact RS.none
    · have hv := u64_lit_ne hT
      rw [ite_eq_right hT, ite_eq_right (by
        intro he
        simp only [Bool.and_eq_true, beq_iff_eq] at he
        exact hv he.1)]
      exact RS.none
  · exact RS.none

/-! ## `exprNode`, arm by arm -/

/-- **`lit_p` is `Region.litP`.** -/
theorem lit_p_eq {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g v : Std.U64} {o}
    (hr : RegionFits bs r) (h : lit_p bs r g v = ok o) :
    o.map ConRon.Refine.absLiteral = (absRegion bs r).litP g.val (absWord v) ∧
      ∀ l, o = some l → ConRon.Refine.LiteralWF l := by
  rw [lit_p] at h
  rw [ConLeche.Frontend.Olean.Region.litP]
  peel h as o1, ho1
  rw [← region_down_eq bs ho1]
  cases o1 with
  | none => cases Result.ok_injective h; exact ⟨rfl, fun l hl => by cases hl⟩
  | some c =>
    dsimp only [locOf, Option.map_some]
    peel h as b, hb
    have eb : b = (absRegion bs r).isCtor c.val 0 1 := region_is_ctor_eq bs hb
    rw [← eb]
    split at h
    · rename_i hb1
      rw [ite_eq_left hb1]
      peel h as i, hi
      peel h as o1, ho1
      obtain ⟨e, hwf⟩ := region_nat_p_eq ho1
      rw [fld_0 hi, ← e]
      cases o1 with
      | none => cases Result.ok_injective h; exact ⟨rfl, fun l hl => by cases hl⟩
      | some n =>
        simp only [kernel.expr.literal_nat, ConRon.Refine.ptr_new_eq, bind_ok] at h
        cases Result.ok_injective h
        exact ⟨rfl, fun l hl => by cases hl; exact hwf n rfl⟩
    · rename_i hb1
      rw [ite_eq_right hb1]
      peel h as b1, hb1'
      have eb1 : b1 = (absRegion bs r).isCtor c.val 1 1 := region_is_ctor_eq bs hb1'
      rw [← eb1]
      split at h
      · rename_i hb2
        rw [ite_eq_left hb2]
        peel h as i, hi
        peel h as o1, ho1
        have e := region_str_p_eq hr ho1
        rw [fld_0 hi, ← e]
        cases o1 with
        | none => cases Result.ok_injective h; exact ⟨rfl, fun l hl => by cases hl⟩
        | some st =>
          have hwf := region_str_p_wf ho1 st rfl
          simp only [kernel.expr.literal_str, ConRon.Refine.ptr_new_eq, bind_ok] at h
          cases Result.ok_injective h
          exact ⟨rfl, fun l hl => by cases hl; exact hwf⟩
      · rename_i hb2
        rw [ite_eq_right hb2]
        cases Result.ok_injective h
        exact ⟨rfl, fun l hl => by cases hl⟩

/-- A number of a node: the `Native` decline, or its value. -/
theorem RS.nat_word_step {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {k' : Std.U64} {n : Nat}
    {k : core.result.Result Std.U64 frontend.olean.spec.RdErr →
      Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore)}
    {g : Nat → AM (Option β)} (hs : SatRel k' n)
    (he : ∀ e, k (.Err e) = ok (.Err e, st.store))
    (hk : ∀ i : Std.U64, i.val = n → RS pers R st lst (k (.Ok i)) (g n)) :
    RS pers R st lst (Std.bind (nat_word k') k) (natWord n >>= g) := by
  intro hrel hinv o s' hm
  obtain ⟨o1, ho1, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have hw := nat_word_eq hs ho1 (lst := lst)
  cases o1 with
  | Ok i2 =>
    obtain ⟨hv, hrun⟩ := hw
    rw [am_bind_ok hrun]
    exact hk i2 hv hrel hinv o s' hm
  | Err e =>
    rw [he e] at hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hm)
    cases e with
    | Bad => exact hw.elim
    | Err ce =>
      show AErrSim ce _
      rw [StateT.run_bind]
      exact AErrSim.bind hw _

/-- A saturated number of a node, or the twin's `none`. -/
macro "sat_step " e:term " as " n:ident hk:ident : tactic =>
  `(tactic| (refine sat_elim $e (fun hA hy => by subst hA; rw [hy]; exact RS.none)
               (fun k' $n:ident hA hy $hk:ident => ?_)
             subst hA; rw [hy]; try dsimp only))

theorem not_lit {v : arena.store.ENodeView} (hv : ∀ l, v ≠ .Lit l) :
    ∀ l, v = .Lit l → ConRon.Refine.LiteralWF l := fun l h => absurd h (hv l)

/-- The `app` arm. -/
theorem expr_app_refines {S : Type} {inst : frontend.olean.spec.Sub S} {s : S} {tt : Sub}
    {bs r g pers st lst} (hs : SubRel inst s tt) :
    RS pers (EqA absEIdx) st lst (frontend.olean.spec.expr_app inst pers st.store bs r g s)
      (match exprIn (absRegion bs r) g.val ((absRegion bs r).fld g.val 0) tt,
          exprIn (absRegion bs r) g.val ((absRegion bs r).fld g.val 1) tt with
        | Option.some f, Option.some a => do pure (Option.some (← internE (.app f a)))
        | _, _ => pure Option.none) := by
  rw [frontend.olean.spec.expr_app]
  refine RS.pure_step fun i hi => RS.pure_step fun r1 hr1 => ?_
  rw [fld_0 hi]
  rd_step (expr_in_eq bs hs hr1) as a
  refine RS.pure_step fun i1 hi1 => RS.pure_step fun r2 hr2 => ?_
  rw [fld_1 hi1]
  rd_step (expr_in_eq bs hs hr2) as a1
  exact RS.intern (v := .App a a1) (not_lit (by simp))

/-- The `bvar` arm. -/
theorem expr_bvar_refines {bs : Slice Std.U8} {r g pers st lst} :
    RS pers (EqA absEIdx) st lst (frontend.olean.spec.expr_bvar pers st.store bs r g)
      (match (absRegion bs r).natP g.val ((absRegion bs r).fld g.val 0) with
        | Option.none => pure Option.none
        | Option.some i => do pure (Option.some (← internE (.bvar (← natWord i))))) := by
  rw [frontend.olean.spec.expr_bvar]
  refine RS.pure_step fun i hi => RS.pure_step fun o ho => ?_
  rw [fld_0 hi]
  sat_step (region_nat_sat_eq ho) as n hk
  refine RS.nat_word_step hk (fun _ => rfl) fun i2 hi2 => ?_
  subst hi2
  exact RS.intern (v := .BVar i2) (not_lit (by simp))

/-- The `const` arm. -/
theorem expr_const_refines {S : Type} {inst : frontend.olean.spec.Sub S} {s : S} {tt : Sub}
    {pk bs r g pers st lst} (hs : SubRel inst s tt) :
    RS pers (EqA absEIdx) st lst (frontend.olean.spec.expr_const inst pk pers st.store bs r g s)
      (match nameIn (absPins pk) (absRegion bs r) g.val ((absRegion bs r).fld g.val 0) tt,
          levelsIn (absPins pk) (absRegion bs r) g.val ((absRegion bs r).fld g.val 1) tt with
        | Option.some n, Option.some us => do pure (Option.some (← internE (.const n us)))
        | _, _ => pure Option.none) := by
  rw [frontend.olean.spec.expr_const]
  refine RS.pure_step fun i hi => RS.pure_step fun r1 hr1 => ?_
  rw [fld_0 hi]
  rd_step (name_in_eq bs hs hr1) as a
  refine RS.pure_step fun i1 hi1 => RS.pure_step fun r2 hr2 => ?_
  rw [fld_1 hi1]
  rd_step (levels_in_eq bs hs hr2) as a1
  exact RS.intern (v := .Const a a1) (not_lit (by simp))

/-- The `lam` and `forallE` arms. -/
theorem expr_bind_refines {S : Type} {inst : frontend.olean.spec.Sub S} {s : S} {tt : Sub}
    {bs r g pers st lst} {pi : Bool} (hs : SubRel inst s tt) :
    RS pers (EqA absEIdx) st lst (frontend.olean.spec.expr_bind inst pers st.store bs r g pi s)
      (match exprIn (absRegion bs r) g.val ((absRegion bs r).fld g.val 1) tt,
          exprIn (absRegion bs r) g.val ((absRegion bs r).fld g.val 2) tt with
        | Option.some t, Option.some b =>
          do pure (Option.some (← internE (if pi then .forallE t b else .lam t b)))
        | _, _ => pure Option.none) := by
  rw [frontend.olean.spec.expr_bind]
  refine RS.pure_step fun i hi => RS.pure_step fun r1 hr1 => ?_
  rw [fld_1 hi]
  rd_step (expr_in_eq bs hs hr1) as a
  refine RS.pure_step fun i1 hi1 => RS.pure_step fun r2 hr2 => ?_
  rw [fld_2 hi1]
  rd_step (expr_in_eq bs hs hr2) as a1
  cases pi with
  | true => exact RS.intern (v := .ForallE a a1) (not_lit (by simp))
  | false => exact RS.intern (v := .Lam a a1) (not_lit (by simp))

/-- The `letE` arm. -/
theorem expr_let_refines {S : Type} {inst : frontend.olean.spec.Sub S} {s : S} {tt : Sub}
    {bs r g pers st lst} (hs : SubRel inst s tt) :
    RS pers (EqA absEIdx) st lst (frontend.olean.spec.expr_let inst pers st.store bs r g s)
      (match exprIn (absRegion bs r) g.val ((absRegion bs r).fld g.val 1) tt,
          exprIn (absRegion bs r) g.val ((absRegion bs r).fld g.val 2) tt,
          exprIn (absRegion bs r) g.val ((absRegion bs r).fld g.val 3) tt with
        | Option.some t, Option.some v, Option.some b =>
          do pure (Option.some (← internE (.letE t v b)))
        | _, _, _ => pure Option.none) := by
  rw [frontend.olean.spec.expr_let]
  refine RS.pure_step fun i hi => RS.pure_step fun r1 hr1 => ?_
  rw [fld_1 hi]
  rd_step (expr_in_eq bs hs hr1) as a
  refine RS.pure_step fun i1 hi1 => RS.pure_step fun r2 hr2 => ?_
  rw [fld_2 hi1]
  rd_step (expr_in_eq bs hs hr2) as a1
  refine RS.pure_step fun i2 hi2 => RS.pure_step fun r3 hr3 => ?_
  rw [fld_3 hi2]
  rd_step (expr_in_eq bs hs hr3) as a2
  exact RS.intern (v := .LetE a a1 a2) (not_lit (by simp))

/-- The `proj` arm. -/
theorem expr_proj_refines {S : Type} {inst : frontend.olean.spec.Sub S} {s : S} {tt : Sub}
    {pk bs r g pers st lst} (hs : SubRel inst s tt) :
    RS pers (EqA absEIdx) st lst (frontend.olean.spec.expr_proj inst pk pers st.store bs r g s)
      (match nameIn (absPins pk) (absRegion bs r) g.val ((absRegion bs r).fld g.val 0) tt with
        | Option.none => pure Option.none
        | Option.some s =>
          match (absRegion bs r).natP g.val ((absRegion bs r).fld g.val 1) with
          | Option.none => pure Option.none
          | Option.some i => do
            let i ← natWord i
            match exprIn (absRegion bs r) g.val ((absRegion bs r).fld g.val 2) tt with
            | Option.none => pure Option.none
            | Option.some x => pure (Option.some (← internE (.proj s i x)))) := by
  rw [frontend.olean.spec.expr_proj]
  refine RS.pure_step fun i hi => RS.pure_step fun r1 hr1 => ?_
  rw [fld_0 hi]
  rd_step (name_in_eq bs hs hr1) as a
  refine RS.pure_step fun i1 hi1 => RS.pure_step fun o ho => ?_
  rw [fld_1 hi1]
  sat_step (region_nat_sat_eq ho) as n hk
  refine RS.nat_word_step hk (fun _ => rfl) fun i2 hi2 => ?_
  subst hi2
  refine RS.pure_step fun i3 hi3 => RS.pure_step fun r3 hr3 => ?_
  rw [fld_2 hi3]
  rd_step (expr_in_eq bs hs hr3) as a2
  exact RS.intern (v := .Proj a i2 a2) (not_lit (by simp))

/-- **`expr_node` is `exprNode`.** -/
theorem expr_node_refines {S : Type} {inst : frontend.olean.spec.Sub S} {s : S} {tt : Sub}
    {pk bs r g pers st lst} (hr : RegionFits bs r) (hs : SubRel inst s tt) :
    RS pers (EqA absEIdx) st lst (frontend.olean.spec.expr_node inst pk pers st.store bs r g s)
      (exprNode (absPins pk) (absRegion bs r) g.val tt) := by
  rw [frontend.olean.spec.expr_node]
  simp only [exprNode]
  refine RS.pure_step fun b hb => ?_
  rw [← region_fits_eq bs hb]
  split
  · refine RS.pure_step fun n hn => RS.pure_step fun t ht => ?_
    rw [← region_tag_eq bs ht, ← region_nobjs_eq bs hn]
    split
    · by_cases hN : n = 2#u64
      · subst hN
        rw [ite_eq_left rfl]
        exact expr_app_refines hs
      · rw [ite_eq_right hN]
        have hv := u64_lit_ne hN
        twin_arm n hv RS.none
    · by_cases hN : n = 1#u64
      · subst hN
        rw [ite_eq_left rfl]
        exact expr_bvar_refines
      · rw [ite_eq_right hN]
        have hv := u64_lit_ne hN
        twin_arm n hv RS.none
    · by_cases hN : n = 1#u64
      · subst hN
        rw [ite_eq_left rfl]
        refine RS.pure_step fun i hi => RS.pure_step fun r1 hr1 => ?_
        show RS _ _ _ _ _ (match levelIn _ _ _ ((absRegion bs r).fld _ 0) tt with
          | none => pure none
          | some u => do pure (some (← internE (.sort u))))
        rw [fld_0 hi]
        rd_step (level_in_eq bs hs hr1) as a
        exact RS.intern (v := .Sort a) (not_lit (by simp))
      · rw [ite_eq_right hN]
        have hv := u64_lit_ne hN
        twin_arm n hv RS.none
    · by_cases hN : n = 2#u64
      · subst hN
        rw [ite_eq_left rfl]
        exact expr_const_refines hs
      · rw [ite_eq_right hN]
        have hv := u64_lit_ne hN
        twin_arm n hv RS.none
    · by_cases hN : n = 3#u64
      · subst hN
        rw [ite_eq_left rfl]
        exact expr_bind_refines (pi := false) hs
      · rw [ite_eq_right hN]
        have hv := u64_lit_ne hN
        twin_arm n hv RS.none
    · by_cases hN : n = 3#u64
      · subst hN
        rw [ite_eq_left rfl]
        exact expr_bind_refines (pi := true) hs
      · rw [ite_eq_right hN]
        have hv := u64_lit_ne hN
        twin_arm n hv RS.none
    · by_cases hN : n = 4#u64
      · subst hN
        rw [ite_eq_left rfl]
        exact expr_let_refines hs
      · rw [ite_eq_right hN]
        have hv := u64_lit_ne hN
        twin_arm n hv RS.none
    · by_cases hN : n = 1#u64
      · subst hN
        rw [ite_eq_left rfl]
        refine RS.pure_step fun i hi => RS.pure_step fun o ho => ?_
        show RS _ _ _ _ _ (match litP _ _ ((absRegion bs r).fld _ 0) with
          | none => pure none
          | some l => do pure (some (← internE (.lit l))))
        rw [fld_0 hi]
        obtain ⟨e, hwf⟩ := lit_p_eq hr ho
        rw [litP, ← e]
        cases o with
        | none => exact RS.none
        | some l =>
          exact RS.intern (v := .Lit l) (by intro l1 h1; cases h1; exact hwf l rfl)
      · rw [ite_eq_right hN]
        have hv := u64_lit_ne hN
        twin_arm n hv RS.none
    · by_cases hN : n = 2#u64
      · subst hN
        rw [ite_eq_left rfl]
        refine RS.pure_step fun i hi => RS.pure_step fun r1 hr1 => ?_
        show RS _ _ _ _ _ (pure (exprIn _ _ ((absRegion bs r).fld _ 1) tt))
        rw [fld_1 hi]
        rd_step (expr_in_eq bs hs hr1) as a
        exact RS.some rfl
      · rw [ite_eq_right hN]
        have hv := u64_lit_ne hN
        twin_arm n hv RS.none
    · by_cases hN : n = 3#u64
      · subst hN
        rw [ite_eq_left rfl]
        exact expr_proj_refines hs
      · rw [ite_eq_right hN]
        have hv := u64_lit_ne hN
        twin_arm n hv RS.none
    · rename_i h5 h0 h3 h4 h6 h7 h8 h9 h10 h11
      have e0 : t.val ≠ 0 := fun he => h0 (UScalar.eq_of_val_eq he)
      have e3 : t.val ≠ 3 := fun he => h3 (UScalar.eq_of_val_eq he)
      have e4 : t.val ≠ 4 := fun he => h4 (UScalar.eq_of_val_eq he)
      have e5 : t.val ≠ 5 := fun he => h5 (UScalar.eq_of_val_eq he)
      have e6 : t.val ≠ 6 := fun he => h6 (UScalar.eq_of_val_eq he)
      have e7 : t.val ≠ 7 := fun he => h7 (UScalar.eq_of_val_eq he)
      have e8 : t.val ≠ 8 := fun he => h8 (UScalar.eq_of_val_eq he)
      have e9 : t.val ≠ 9 := fun he => h9 (UScalar.eq_of_val_eq he)
      have e10 : t.val ≠ 10 := fun he => h10 (UScalar.eq_of_val_eq he)
      have e11 : t.val ≠ 11 := fun he => h11 (UScalar.eq_of_val_eq he)
      generalize UScalar.val t = T at e0 e3 e4 e5 e6 e7 e8 e9 e10 e11 ⊢
      rcases T with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | T
      · exact absurd rfl e0
      · exact RS.none
      · exact RS.none
      · exact absurd rfl e3
      · exact absurd rfl e4
      · exact absurd rfl e5
      · exact absurd rfl e6
      · exact absurd rfl e7
      · exact absurd rfl e8
      · exact absurd rfl e9
      · exact absurd rfl e10
      · exact absurd rfl e11
      · exact RS.none
  · exact RS.none

/-! ## `nameAt`, `nameP` -/

/-- **`name_at` is `nameAt`.** -/
theorem name_at_refines {pk bs r pers} (hr : RegionFits bs r) :
    ∀ (m : Nat) (g : Std.U64) st lst, g.val < m →
      RS pers (EqA absNIdx) st lst (frontend.olean.spec.name_at pk pers st.store bs r g)
        (nameAt (absPins pk) (absRegion bs r) g.val) := by
  intro m
  induction m with
  | zero => intro g _ _ h; omega
  | succ m ih =>
    intro g st lst hm
    rw [frontend.olean.spec.name_at, nameAt]
    refine RS.pure_step fun b hb => ?_
    rw [← region_fits_eq bs hb]
    split
    · refine RS.pure_step fun t ht => RS.pure_step fun i hi => RS.pure_step fun b1 hb2 => ?_
      dsimp only
      rw [← region_tag_eq bs ht, ← region_nobjs_eq bs hi, ← name_shape_eq hb2]
      split
      · refine RS.pure_step fun v hv => ?_
        have e0 : (absRegion bs r).fld g.val 0 = absWord v := fld_0 hv
        simp only [e0]
        split
        · rename_i hv1
          rw [ite_eq_left (word_eq_one.mpr hv1)]
          refine RS.pure_step fun p hp => ?_
          rw [nidx_dup2_ok hp]
          exact name_tail_refines hr
        · rename_i hv1
          rw [ite_eq_right (fun he => hv1 (word_eq_one.mp he))]
          refine RS.pure_step fun o ho => ?_
          have ed := region_down_eq bs ho
          rw [← e0] at ed
          cases o with
          | none =>
            dsimp only
            split
            · exact RS.none
            · rename_i c hdn
              rw [hdn] at ed
              cases ed
          | some c' =>
            dsimp only
            split
            · rename_i hdn
              rw [hdn] at ed
              cases ed
            · rename_i c hdn
              rw [hdn] at ed
              cases ed
              have hlt : c'.val < g.val := ConLeche.Frontend.Olean.Region.down_lt hdn
              beta_reduce
              refine RS.bind_of (ih c' st lst (by omega)) (fun _ _ => by rfl) rfl
                fun a b s1 lst1 hR => ?_
              cases hR
              exact name_tail_refines hr
      · exact RS.none
    · exact RS.none

/-- **`name_p` is `nameP`.** -/
theorem name_p_refines {pk bs r pers st lst} {v : Std.U64} (hr : RegionFits bs r) :
    RS pers (EqA absNIdx) st lst (frontend.olean.spec.name_p pk pers st.store bs r v)
      (nameP (absPins pk) (absRegion bs r) (absWord v)) := by
  rw [frontend.olean.spec.name_p, nameP]
  split
  · rename_i hv
    rw [ite_eq_left (word_eq_one.mpr hv)]
    refine RS.pure_step fun p hp => ?_
    rw [nidx_dup2_ok hp]
    exact RS.some rfl
  · rename_i hv
    rw [ite_eq_right (fun he => hv (word_eq_one.mp he))]
    refine RS.pure_step fun o ho => ?_
    rw [← region_loc_eq bs ho]
    cases o with
    | none => exact RS.none
    | some c => exact name_at_refines hr _ c st lst (Nat.lt_succ_self _)

end ConRon.Refine2.Frontend.Olean

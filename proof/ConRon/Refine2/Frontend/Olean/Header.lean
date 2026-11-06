/-
# `ConRon.Refine2.Frontend.Olean.Header` — a module's imports off the start of a file

**Task #142, Theorem 2.**  `word_up`, `hdr_adv`, `hdr_walk` against upstream's; `imports_read`,
`imports_in`, `imports_pre` against the twin's.

The sums of the walk saturate where upstream's `Nat`s go on.  A file has fewer than `2 ^ 60`
bytes (`PartFits`), so past that a word and its `Nat` are both beyond every test: `Loose`.
-/
import ConRon.Refine2.Frontend.Olean.SpecEntry
import ConRon.Refine2.Frontend.Olean.Parts

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.region (rd_u8 rd_u64 sat_add sat_mul8 region_tag region_file_end TAG_ARRAY
  TAG_STRING TAG_MPZ DATA_START region_obj_array_go)
open frontend.olean.spec (import_skel import_map name_p)
open frontend.olean.header (word_up hdr_adv hdr_walk hdr_walk_loop imports_read imports_read_loop
  imports_in imports_pre)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Arena.Frontend.Olean (nameP importsRead importsIn importsPre)
open ConLeche.Frontend.Olean (wordUp hdrAdv hdrWalk rdU8 rdU64 tagArray tagString tagMPZ importSkel
  ImportF)
open ConRon.Refine.HashMap (uscalar_add_eq uscalar_sub_eq uscalar_mul_eq uscalar_div_eq)

/-! ## The walk -/

/-- A word and a `Nat`: equal, or both past anything a file's size asks. -/
def Loose (k : Std.U64) (x : Nat) : Prop := k.val = x ∨ (2 ^ 60 ≤ k.val ∧ 2 ^ 60 ≤ x)

/-- **`word_up` is `wordUp`**, of a saturated number. -/
theorem word_up_spec {n k : Std.U64} {x : Nat} (hn : n.val = min x (2 ^ 64 - 1))
    (h : word_up n = ok k) : Loose k (wordUp x) := by
  rw [word_up] at h
  peel h as s, hs
  have hsv := sat_add_spec hs
  have l7 : (7#u64 : Std.U64).val = 7 := by decide
  rw [l7] at hsv
  simp only [wordUp]
  split at h
  · rename_i hm
    cases Result.ok_injective h
    have : s.val = 2 ^ 64 - 1 := by rw [hm, u64_max_val]
    right
    rw [u64_max_val]
    omega
  · rename_i hm
    have hne : s.val ≠ 2 ^ 64 - 1 := fun he => hm (UScalar.eq_of_val_eq (by rw [he, u64_max_val]))
    peel h as i, hi
    have v1 := uscalar_div_eq hi
    have v2 := uscalar_mul_eq h
    rw [u64_val_lit8] at v1 v2
    left
    omega

/-- **`hdr_adv` is `hdrAdv`.** -/
theorem hdr_adv_spec {b : Slice Std.U8} {g k : Std.U64} (h : hdr_adv b g = ok k) :
    Loose k (hdrAdv (absBytes b) g.val) := by
  rw [hdr_adv] at h
  simp only [lift, bind_ok] at h
  simp only [hdrAdv]
  peel h as i, hi
  peel h as c7, hc7
  have l7 : (7#u64 : Std.U64).val = 7 := by decide
  have e7 := rd_u8_eq hc7
  rw [uscalar_add_eq hi, l7] at e7
  have et : (rdU8 (absBytes b) (g.val + 7)).toNat = c7.val := by rw [← e7, absByte_toNat]
  have ts := tag_string_val
  have ts2 : tagString = 249 := rfl
  rw [et, ts2]
  split at h
  · rename_i hc
    have hc' : c7.val = 249 := by
      have := congrArg UScalar.val hc
      rw [cast_u64_u8, ts] at this
      exact this
    rw [ite_eq_left (by simp [hc'])]
    peel h as i3, hi3
    peel h as i4, hi4
    peel h as i5, hi5
    have e8 := rd_u64_eq hi4
    rw [uscalar_add_eq hi3, u64_val_lit8] at e8
    have hn : (rdU64 (absBytes b) (g.val + 8)).toNat = i4.val := by rw [← e8, absWord_toNat]
    have v5 := sat_add_spec hi5
    have l32 : (32#u64 : Std.U64).val = 32 := by decide
    rw [l32] at v5
    rw [hn]
    exact word_up_spec v5 h
  · rename_i hc
    have hc' : c7.val ≠ 249 := by
      intro he
      apply hc
      apply UScalar.eq_of_val_eq
      rw [cast_u64_u8, ts, he]
    rw [ite_eq_right (by simp [hc'])]
    peel h as i3, hi3
    peel h as i4, hi4
    peel h as i6, hi6
    peel h as i7, hi7
    peel h as i9, hi9
    peel h as i10, hi10
    have l4 : (4#u64 : Std.U64).val = 4 := by decide
    have l5 : (5#u64 : Std.U64).val = 5 := by decide
    have l256 : (256#u64 : Std.U64).val = 256 := by decide
    have e4 := rd_u8_eq hi4
    rw [uscalar_add_eq hi3, l4] at e4
    have e5 := rd_u8_eq hi7
    rw [uscalar_add_eq hi6, l5] at e5
    have n4 : (rdU8 (absBytes b) (g.val + 4)).toNat = i4.val := by rw [← e4, absByte_toNat]
    have n5 : (rdU8 (absBytes b) (g.val + 5)).toNat = i7.val := by rw [← e5, absByte_toNat]
    have v9 := uscalar_mul_eq hi9
    rw [l256, cast_u64_u8] at v9
    have v10 := uscalar_add_eq hi10
    rw [cast_u64_u8] at v10
    rw [n4, n5]
    refine word_up_spec ?_ h
    have := u64_lt i10
    omega

/-- The outcome of the walk, as upstream's. -/
def absWalk : frontend.olean.header.HdrWalk → ConLeche.Frontend.Olean.HdrWalk
  | .Found c e => .found c.val e.val
  | .Short => .short
  | .Bad => .bad

/-- **The walk**, whatever the size below `2 ^ 60`. -/
theorem hdr_walk_loop_eq {b : Slice Std.U8} {size : Std.U64} (hs : size.val = b.val.length)
    (hb : b.val.length < 2 ^ 60) :
    ∀ (k : Nat) {g : Std.U64} {G : Nat} {o}, b.val.length - G ≤ k → Loose g G →
      hdr_walk_loop b g size = ok o → absWalk o = hdrWalk (absBytes b) G := by
  have l16 : (16#u64 : Std.U64).val = 16 := by decide
  have l7 : (7#u64 : Std.U64).val = 7 := by decide
  have l24 : (24#u64 : Std.U64).val = 24 := by decide
  have short : ∀ {g : Std.U64} {G : Nat} {o}, Loose g G → ¬ G + 16 ≤ b.val.length →
      hdr_walk_loop b g size = ok o → absWalk o = hdrWalk (absBytes b) G := by
    intro g G o hL hG h
    rw [hdr_walk_loop] at h
    rw [hdrWalk, dite_eq_right (by rw [absBytes_size]; exact hG)]
    split at h
    · cases Result.ok_injective h; rfl
    · rename_i h16
      have h16' : ¬ size.val < 16 := by have : ¬ size.val < (16#u64 : Std.U64).val := h16; omega
      peel h as i, hi
      have hiv := uscalar_sub_eq hi
      rw [l16] at hiv
      have hgi : g > i := by
        show i.val < g.val
        rcases hL with hL | ⟨hL, -⟩ <;> omega
      rw [ite_eq_left hgi] at h
      cases Result.ok_injective h
      rfl
  intro k
  induction k with
  | zero =>
    intro g G o hk hL h
    exact short hL (by omega) h
  | succ k ih =>
    intro g G o hk hL h
    by_cases hG : G + 16 ≤ b.val.length
    swap
    · exact short hL hG h
    have hgv : g.val = G := by rcases hL with hL | ⟨-, hL⟩ <;> omega
    subst hgv
    rw [hdr_walk_loop] at h
    rw [hdrWalk, dite_eq_left (by rw [absBytes_size]; exact hG)]
    have h16' : ¬ size < 16#u64 := by
      show ¬ size.val < (16#u64 : Std.U64).val
      omega
    rw [ite_eq_right h16'] at h
    peel h as i, hi
    have hiv := uscalar_sub_eq hi
    rw [l16] at hiv
    have hgi : ¬ g > i := by
      show ¬ i.val < g.val
      omega
    rw [ite_eq_right hgi] at h
    simp only [lift, bind_ok] at h
    peel h as i1, hi1
    peel h as c7, hc7
    have e7 := rd_u8_eq hc7
    rw [uscalar_add_eq hi1, l7] at e7
    have et : (rdU8 (absBytes b) (g.val + 7)).toNat = c7.val := by rw [← e7, absByte_toNat]
    have ta := tag_array_val
    have ts := tag_string_val
    have tm := tag_mpz_val
    have ta2 : tagArray = 246 := rfl
    have ts2 : tagString = 249 := rfl
    have tm2 : tagMPZ = 250 := rfl
    rw [et, ta2, ts2, tm2]
    have hcast := cast_u64_u8 c7
    /- The arms of an object that is walked past. -/
    have arm : ∀ {o}, (do
        let adv ← hdr_adv b g
        if adv < 8#u64 then Result.ok frontend.olean.header.HdrWalk.Bad
        else do
          let g1 ← sat_add g adv
          hdr_walk_loop b g1 size) = ok o →
        absWalk o = (if _hs : 8 ≤ hdrAdv (absBytes b) g.val then
          hdrWalk (absBytes b) (g.val + hdrAdv (absBytes b) g.val) else .bad) := by
      intro o h
      peel h as adv, hadv
      have hA := hdr_adv_spec hadv
      generalize hdrAdv (absBytes b) g.val = A at hA ⊢
      split at h
      · rename_i hlt
        have hlt' : adv.val < 8 := by simpa using (show adv.val < (8#u64 : Std.U64).val from hlt)
        cases Result.ok_injective h
        rw [dite_eq_right (by rcases hA with hA | ⟨hA1, hA⟩ <;> omega)]
        rfl
      · rename_i hge
        have hge' : ¬ adv.val < 8 := by simpa using (show ¬ adv.val < (8#u64 : Std.U64).val from hge)
        have hA8 : 8 ≤ A := by rcases hA with hA | ⟨-, hA⟩ <;> omega
        rw [dite_eq_left hA8]
        peel h as g1, hg1
        have v := sat_add_spec hg1
        refine ih (by omega) ?_ h
        rcases hA with hA | ⟨hA, hA2⟩
        · by_cases hm : g.val + adv.val ≤ 2 ^ 64 - 1
          · left; omega
          · right; omega
        · right; omega
    by_cases h1 : UScalar.cast UScalarTy.U64 c7 = TAG_ARRAY
    · rw [ite_eq_left h1] at h
      have h1' : c7.val = 246 := by
        have := congrArg UScalar.val h1
        rw [hcast, ta] at this
        exact this
      rw [ite_eq_left h1']
      peel h as lo, hlo
      peel h as i3, hi3
      peel h as i4, hi4
      peel h as m, hm
      have vlo := uscalar_add_eq hlo
      rw [l24] at vlo
      have e8 := rd_u64_eq hi4
      rw [uscalar_add_eq hi3, u64_val_lit8] at e8
      have hn : (rdU64 (absBytes b) (g.val + 8)).toNat = i4.val := by rw [← e8, absWord_toNat]
      have vm := sat_mul8_spec hm
      rw [hn, absBytes_size]
      split at h
      · rename_i hle
        have hle' : lo.val ≤ size.val := hle
        peel h as i5, hi5
        have vi5 := uscalar_sub_eq hi5
        split at h
        · rename_i hm2
          have hm2' : m.val ≤ i5.val := hm2
          peel h as i6, hi6
          have v6 := uscalar_add_eq hi6
          cases Result.ok_injective h
          have hbig : m.val = 8 * i4.val := by omega
          rw [ite_eq_left (by omega)]
          show ConLeche.Frontend.Olean.HdrWalk.found g.val i6.val = _
          rw [v6, vlo, hbig]
        · rename_i hm2
          have hm2' : ¬ m.val ≤ i5.val := hm2
          cases Result.ok_injective h
          rw [ite_eq_right (by omega)]
          rfl
      · rename_i hle
        have hle' : ¬ lo.val ≤ size.val := hle
        cases Result.ok_injective h
        rw [ite_eq_right (by omega)]
        rfl
    · rw [ite_eq_right h1] at h
      have h1' : c7.val ≠ 246 := by
        intro he
        apply h1
        apply UScalar.eq_of_val_eq
        rw [hcast, ta, he]
      rw [ite_eq_right h1']
      by_cases h2 : UScalar.cast UScalarTy.U64 c7 <= 243#u64
      · rw [ite_eq_left h2] at h
        have h2' : c7.val ≤ 243 := by
          have l : (243#u64 : Std.U64).val = 243 := by decide
          have : (UScalar.cast UScalarTy.U64 c7).val ≤ (243#u64 : Std.U64).val := h2
          omega
        rw [ite_eq_left (Or.inl h2')]
        exact arm h
      · rw [ite_eq_right h2] at h
        have h2' : ¬ c7.val ≤ 243 := by
          have l : (243#u64 : Std.U64).val = 243 := by decide
          have : ¬ (UScalar.cast UScalarTy.U64 c7).val ≤ (243#u64 : Std.U64).val := h2
          omega
        by_cases h3 : UScalar.cast UScalarTy.U64 c7 = TAG_STRING
        · rw [ite_eq_left h3] at h
          have h3' : c7.val = 249 := by
            have := congrArg UScalar.val h3
            rw [hcast, ts] at this
            exact this
          rw [ite_eq_left (Or.inr (Or.inl h3'))]
          exact arm h
        · rw [ite_eq_right h3] at h
          have h3' : c7.val ≠ 249 := by
            intro he
            apply h3
            apply UScalar.eq_of_val_eq
            rw [hcast, ts, he]
          by_cases h4 : UScalar.cast UScalarTy.U64 c7 = TAG_MPZ
          · rw [ite_eq_left h4] at h
            have h4' : c7.val = 250 := by
              have := congrArg UScalar.val h4
              rw [hcast, tm] at this
              exact this
            rw [ite_eq_left (Or.inr (Or.inr h4'))]
            exact arm h
          · rw [ite_eq_right h4] at h
            have h4' : c7.val ≠ 250 := by
              intro he
              apply h4
              apply UScalar.eq_of_val_eq
              rw [hcast, tm, he]
            cases Result.ok_injective h
            rw [ite_eq_right (by omega)]
            rfl

/-- **`hdr_walk` is `hdrWalk`.** -/
theorem hdr_walk_eq {b : Slice Std.U8} {g : Std.U64} {o} (hb : b.val.length < 2 ^ 60)
    (h : hdr_walk b g = ok o) : absWalk o = hdrWalk (absBytes b) g.val := by
  rw [hdr_walk] at h
  simp only [lift, bind_ok] at h
  exact hdr_walk_loop_eq (by rw [cast_u64_usize]; simp) hb _ (Nat.le_refl _) (Or.inl rfl) h

/-- The found outcome lies inside the bytes. -/
theorem hdrWalk_found_le {B : ByteArray} :
    ∀ (k : Nat) {G c e : Nat}, B.size - G ≤ k → hdrWalk B G = .found c e → e ≤ B.size := by
  intro k
  induction k with
  | zero =>
    intro G c e hk h
    rw [hdrWalk, dite_eq_right (by omega)] at h
    cases h
  | succ k ih =>
    intro G c e hk h
    rw [hdrWalk] at h
    split at h
    · rename_i hG
      split at h
      · split at h
        · rename_i hle
          injection h with h1 h2
          omega
        · cases h
      · split at h
        · split at h
          · rename_i hs
            exact ih (by omega) h
          · cases h
        · cases h
    · cases h

/-! ## The pointer read -/

/-- The twin's pointer read of the imports: `nameP`, and no expression. -/
def namePT (P : ConRon.Arena.Frontend.Olean.OleanPins) (R : ConLeche.Frontend.Olean.Region) :
    ConRon.Arena.Frontend.Olean.PtrRead :=
  ⟨nameP P R, fun _ => pure none⟩

/-- **`NamePRead` is `nameP`.** -/
theorem name_p_read_rel {pk bs r pers} (hr : RegionFits bs r) :
    PtrRel frontend.olean.header.NamePRead.Insts.Con_ron_coreFrontendOleanSpecPtrRead ()
      (namePT (absPins pk) (absRegion bs r)) pk bs r pers where
  nm _ _ _ := name_p_refines hr
  ex _ _ _ := RS.none

/-- The imports, as the twin's array. -/
abbrev ImpA (v : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))
    (a : Array ConRon.Arena.Frontend.Olean.ImportRec) : Prop :=
  a = (v.val.map (absImportF absNIdx)).toArray

/-- A pure answer, then the rest, at `OptionT AM`. -/
theorem optionT_pure_some {α β : Type} (a : α) (g : α → OptionT AM β) :
    (OptionT.mk (pure (some a)) >>= g : OptionT AM β) = g a := rfl

/-- **`imports_read` is `importsRead`.** -/
theorem imports_read_refines {pk bs r pers st lst} (hr : RegionFits bs r)
    {imps : alloc.vec.Vec Std.U64} :
    RS pers ImpA st lst (imports_read pk pers st.store bs r imps)
      (importsRead (absPins pk) (absRegion bs r) (absLocs imps)) := by
  have hp := name_p_read_rel (pk := pk) (pers := pers) hr
  have main : RS pers (fun v l => List.Forall₂ (EqA (absImportF absNIdx)) v.val l) st lst
      (imports_read pk pers st.store bs r imps)
      ((imps.val.map (·.val)).mapM (m := OptionT AM) fun i => do
        let sk ← OptionT.mk (pure (importSkel (absRegion bs r) i))
        sk.mapM (m := OptionT AM) fun v => OptionT.mk (nameP (absPins pk) (absRegion bs r) v)) := by
    rw [imports_read]
    refine RS.vec_map (R := EqA (absImportF absNIdx))
      (loop := fun ar out i => imports_read_loop pk pers ar bs r imps out i)
      (forall₂_of_map (A := fun v : Std.U64 => v.val) imps.val) ?_ ?_ (by simp) (by rfl)
    · intro ar out i hi
      show imports_read_loop pk pers ar bs r imps out i = _
      rw [imports_read_loop, ite_eq_right (by scalar_tac)]
    · intro i out x x' K Rf st lst hx hS hK
      cases hS
      show RS _ _ _ _ (imports_read_loop pk pers st.store bs r imps out i) _
      rw [imports_read_loop,
        ite_eq_left (by have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)]
      refine RS.pure_step fun y hy => ?_
      have hy3 := ConRon.Refine.ExprOps.vec_index_getElem? hy
      rw [hx] at hy3
      cases Option.some.inj hy3
      refine RS.pure_step fun o ho => ?_
      have e := import_skel_eq (bs := bs) (r := r) ho
      simp only [bind_assoc]
      rw [← e]
      cases o with
      | none => exact RS.none
      | some sk =>
        rw [Option.map_some, optionT_pure_some]
        refine RS.bindT (import_map_refines hp st lst) (fun _ _ => by rfl) fun a b s1 lst1 hR =>
          RS.pure_step fun out1 ho1 => RS.pure_step fun i3 hi3 => ?_
        exact hK a b s1 lst1 out1 i3 hR (ConRon.Refine.vec_push_val ho1) (uscalar_add_eq hi3)
  have e : importsRead (absPins pk) (absRegion bs r) (absLocs imps) =
      (((imps.val.map (·.val)).mapM (m := OptionT AM) fun i => do
        let sk ← OptionT.mk (pure (importSkel (absRegion bs r) i))
        sk.mapM (m := OptionT AM) fun v => OptionT.mk (nameP (absPins pk) (absRegion bs r) v)) >>=
        fun l => pure l.toArray : OptionT AM _) := by
    show (Array.mapM (m := OptionT AM) _ (absLocs imps)) = _
    rw [absLocs, List.mapM_toArray, map_eq_pure_bind]
  rw [e]
  exact RS.map_pure main (fun a b h => by
    show b.toArray = _
    rw [← forall₂_eqA h])

/-- **`imports_in` is `importsIn`.** -/
theorem imports_in_refines {pk bs r pers st lst} {c : Std.U64} (hr : RegionFits bs r) :
    RS pers ImpA st lst (imports_in pk pers st.store bs r c)
      (importsIn (absPins pk) (absRegion bs r) c.val) := by
  rw [imports_in, importsIn]
  refine RS.pure_step fun t ht => ?_
  rw [← region_tag_eq bs ht]
  have tv : tagArray = 246 := rfl
  have tv2 := tag_array_val
  rw [tv]
  by_cases hc : t = TAG_ARRAY
  · have hc' : t.val = 246 := by rw [hc, tv2]
    rw [ite_eq_right (by simp [hc]), ite_eq_left (by simp [hc'])]
    refine RS.pure_step fun i1 hi1 => RS.pure_step fun n hn => RS.pure_step fun i2 hi2 =>
      RS.pure_step fun i3 hi3 => RS.pure_step fun i4 hi4 => RS.pure_step fun i5 hi5 => ?_
    have v1 := uscalar_add_eq hi1
    have en := rd_u64_eq hn
    rw [v1, u64_val_lit8] at en
    have v2 := uscalar_add_eq hi2
    have l24 : (24#u64 : Std.U64).val = 24 := by decide
    rw [l24] at v2
    have v3 := sat_mul8_spec hi3
    have v4 := sat_add_spec hi4
    obtain ⟨ff1, ff2⟩ := file_end_fits hr hi5
    dsimp only
    rw [show ConLeche.Frontend.Olean.rdU64 (absRegion bs r).bytes (c.val + 8) = absWord n from en.symm,
      absWord_toNat, ← region_file_end_eq bs hi5]
    by_cases hgt : i4 > i5
    · have hgt' : i5.val < i4.val := hgt
      rw [ite_eq_left hgt, ite_eq_right (by omega)]
      exact RS.none
    · have hgt' : ¬ i5.val < i4.val := hgt
      rw [ite_eq_right hgt, ite_eq_left (by omega)]
      simp only [lift, bind_ok]
      refine RS.pure_step fun o ho => ?_
      have e := region_obj_array_go_eq (bs := bs) (r := r) (n.val - (0#u64 : Std.U64).val) rfl ho
      rw [v2] at e
      rw [show (absRegion bs r).objArrayGo c.val (c.val + 24) n.val 0 (Array.mkEmpty n.val) = _ from e.symm]
      cases o with
      | none => exact RS.none
      | some imps => exact imports_read_refines hr
  · have hc' : t.val ≠ 246 := by
      intro he
      apply hc
      apply UScalar.eq_of_val_eq
      rw [tv2, he]
    rw [ite_eq_left (by simpa using hc), ite_eq_right (by simp [hc'])]
    exact RS.none

/-- The bytes of a prefix. -/
theorem absBytes_prefix {b pre : Slice Std.U8} {e : Nat} (h : pre.val = List.slice 0 e b.val) :
    absBytes pre = (absBytes b).extract 0 e := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  apply Array.ext'
  simp [absBytes, h]

/-- **`imports_pre` is `importsPre`**, of a file of fewer than `2 ^ 60` bytes. -/
theorem imports_pre_refines {pk pers st lst} {b : Slice Std.U8} (hb : b.val.length < 2 ^ 60) :
    RS pers ImpA st lst (imports_pre pk pers st.store b) (importsPre (absPins pk) (absBytes b)) := by
  rw [imports_pre, importsPre]
  refine RS.pure_step fun hw hhw => ?_
  have ew := hdr_walk_eq hb hhw
  have hds : DATA_START.val = ConLeche.Frontend.Olean.dataStart := data_start_val
  rw [hds] at ew
  rw [← ew]
  cases hw with
  | Short => exact RS.none
  | Bad => exact RS.none
  | Found c e =>
    have hle : e.val ≤ b.val.length := by
      have := hdrWalk_found_le (B := absBytes b) _ (Nat.le_refl _) ew.symm
      rwa [absBytes_size] at this
    simp only [lift, bind_ok, absWalk]
    have hmax : e.val ≤ Std.Usize.max := by
      have : b.val.length ≤ Std.Usize.max := by scalar_tac
      omega
    have hce := ConRon.Refine.ExprOps.u64_cast_usize_val hmax
    refine RS.pure_step fun pre hpre => RS.pure_step fun i1 hi1 => RS.pure_step fun segs1 hs1 => ?_
    rw [Slice.index_SliceIndexRangeUsizeSliceInst, core.slice.index.SliceIndexRangeUsizeSlice.index] at hpre
    have hc0 : (0#usize : Std.Usize).val = 0 := by decide
    have hprev : pre.val = List.slice 0 e.val b.val := by
      split at hpre
      · cases Result.ok_injective hpre
        rw [Slice.from_val]
        simp only [hc0, hce]
      · exact absurd hpre (by simp)
    have hplen : pre.val.length = e.val := by
      rw [hprev]; simp [List.slice]; omega
    have hsv : segs1.val = [({ base := i1, off := 0#u64, size := e } : frontend.olean.region.Seg)] := by
      rw [ConRon.Refine.vec_push_val hs1]; rfl
    have hfits : RegionFits pre { segs := segs1 } := by
      intro s hm
      have : s = ({ base := i1, off := 0#u64, size := e } : frontend.olean.region.Seg) := by
        simpa [hsv] using hm
      subst this
      have l0 : (0#u64 : Std.U64).val = 0 := by decide
      show (0#u64 : Std.U64).val + e.val ≤ _ ∧ (0#u64 : Std.U64).val + e.val < _
      rw [l0, hplen]
      omega
    have hbytes := absBytes_prefix hprev
    have er : absRegion pre { segs := segs1 } =
        ConLeche.Frontend.Olean.Region.single
          ⟨rdU64 ((absBytes b).extract 0 e.val) 80, (absBytes b).extract 0 e.val⟩ := by
      have hs := absRegion_segs_one pre { segs := segs1 } hsv
      have e80 := rd_u64_eq hi1
      have l80 : (80#u64 : Std.U64).val = 80 := by decide
      rw [l80] at e80
      simp only [ConLeche.Frontend.Olean.Region.single, ← hbytes, ← e80]
      show (⟨absBytes pre, (absRegion pre { segs := segs1 }).segs⟩ : ConLeche.Frontend.Olean.Region) = _
      rw [hs]
      have : (absBytes pre).size = e.val := by rw [absBytes_size, hplen]
      simp only [this, absSeg]
      rfl
    rw [← er]
    exact imports_in_refines hfits

end ConRon.Refine2.Frontend.Olean

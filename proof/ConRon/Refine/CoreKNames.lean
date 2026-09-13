/-
`CORE_PLAN.md` step 4 (task #49), part two: **the pinned names and name tables
of `kernel/core_k.rs`**, against `ConLeche/Kernel/Core.lean`.

Three groups, all state-free:

* the eighteen pinned `Nat`/`Bool` operation names (`Core.lean:505-522`), each
  the same `str_lit_step` five-liner as `Refine/BasisNames.lean`'s;
* the three name tables (`natOpNames`, `natDivModNames`, `natOpWfNames`), the
  fifteen-arm `natOpDeps` chain and the `reduceNat` disjunction
  `is_nat_bin_op`;
* `projModelName`, i.e. `proj_model_name` and the `nat_to_dec`/`nat_to_dec_go`
  decimal recursion it needs.

What was hard: **`nat_to_dec_go` is Lean's `toString` on a `Nat`**, so the
refinement has to meet Lean core's `Nat.toDigits` head on.  It turned out to be
no detour: `Nat.toDigits_of_lt_base` and `Nat.toDigits_of_base_le`
(`Init/Data/Nat/ToString.lean`) are exactly the port's two arms --
`n < 10 ↦ [digitChar n]` and `n ↦ toDigits (n / 10) ++ [digitChar (n % 10)]`
-- so a strong induction on `i.val` closes it with no number theory beyond
`Nat.toNat_digitChar_of_lt_ten` and `Char.ofNat_toNat`; `toString` is then
`String.ofList (toDigits 10 n)` by `Nat.toString_eq_ofList_toDigits`.  No
`sorry` anywhere in the file.

`is_nat_bin_op` has no `def` of its own in the cited Lean: it is `reduceNat`'s
`∨`-chain, so it is stated as the corresponding `Bool` disjunction.

One lemma needed here belongs in `CoreKBase.lean` (or `HashMap.lean`, beside
its `%`-free siblings) and is written locally until then: `uscalar_rem_eq`, the
`%` twin of `HashMap.uscalar_div_eq`.
-/
import ConRon.Refine.BasisNames
import ConLeche.Kernel.Core

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel
open ConRon.Refine.BasisNames

namespace ConRon.Refine.CoreK

/-! ## The pinned `Nat`/`Bool` operation names of `core_k.rs` -/

/-- `ConLeche/Kernel/Core.lean:505-505 natPredName` --
`core_k::nat_pred_name` refines `natPredName`. -/
theorem nat_pred_name_refines {n : name.Name} (h : core_k.nat_pred_name = ok n) :
    absName n = ConLeche.natPredName ∧ NameWF n := by
  rw [core_k.nat_pred_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nat_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [112#u32, 114#u32, 101#u32, 100#u32]) (by simp [core_k.nat_pred_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Core.lean:506-506 natAddName` --
`core_k::nat_add_name` refines `natAddName`. -/
theorem nat_add_name_refines {n : name.Name} (h : core_k.nat_add_name = ok n) :
    absName n = ConLeche.natAddName ∧ NameWF n := by
  rw [core_k.nat_add_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nat_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [97#u32, 100#u32, 100#u32]) (by simp [core_k.nat_add_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Core.lean:507-507 natSubName` --
`core_k::nat_sub_name` refines `natSubName`. -/
theorem nat_sub_name_refines {n : name.Name} (h : core_k.nat_sub_name = ok n) :
    absName n = ConLeche.natSubName ∧ NameWF n := by
  rw [core_k.nat_sub_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nat_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [115#u32, 117#u32, 98#u32]) (by simp [core_k.nat_sub_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Core.lean:508-508 natMulName` --
`core_k::nat_mul_name` refines `natMulName`. -/
theorem nat_mul_name_refines {n : name.Name} (h : core_k.nat_mul_name = ok n) :
    absName n = ConLeche.natMulName ∧ NameWF n := by
  rw [core_k.nat_mul_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nat_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [109#u32, 117#u32, 108#u32]) (by simp [core_k.nat_mul_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Core.lean:509-509 natPowName` --
`core_k::nat_pow_name` refines `natPowName`. -/
theorem nat_pow_name_refines {n : name.Name} (h : core_k.nat_pow_name = ok n) :
    absName n = ConLeche.natPowName ∧ NameWF n := by
  rw [core_k.nat_pow_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nat_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [112#u32, 111#u32, 119#u32]) (by simp [core_k.nat_pow_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Core.lean:510-510 natBeqName` --
`core_k::nat_beq_name` refines `natBeqName`. -/
theorem nat_beq_name_refines {n : name.Name} (h : core_k.nat_beq_name = ok n) :
    absName n = ConLeche.natBeqName ∧ NameWF n := by
  rw [core_k.nat_beq_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nat_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [98#u32, 101#u32, 113#u32]) (by simp [core_k.nat_beq_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Core.lean:511-511 natBleName` --
`core_k::nat_ble_name` refines `natBleName`. -/
theorem nat_ble_name_refines {n : name.Name} (h : core_k.nat_ble_name = ok n) :
    absName n = ConLeche.natBleName ∧ NameWF n := by
  rw [core_k.nat_ble_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nat_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [98#u32, 108#u32, 101#u32]) (by simp [core_k.nat_ble_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Core.lean:512-512 natDivName` --
`core_k::nat_div_name` refines `natDivName`. -/
theorem nat_div_name_refines {n : name.Name} (h : core_k.nat_div_name = ok n) :
    absName n = ConLeche.natDivName ∧ NameWF n := by
  rw [core_k.nat_div_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nat_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [100#u32, 105#u32, 118#u32]) (by simp [core_k.nat_div_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Core.lean:513-513 natModName` --
`core_k::nat_mod_name` refines `natModName`. -/
theorem nat_mod_name_refines {n : name.Name} (h : core_k.nat_mod_name = ok n) :
    absName n = ConLeche.natModName ∧ NameWF n := by
  rw [core_k.nat_mod_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nat_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [109#u32, 111#u32, 100#u32]) (by simp [core_k.nat_mod_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Core.lean:514-514 natGcdName` --
`core_k::nat_gcd_name` refines `natGcdName`. -/
theorem nat_gcd_name_refines {n : name.Name} (h : core_k.nat_gcd_name = ok n) :
    absName n = ConLeche.natGcdName ∧ NameWF n := by
  rw [core_k.nat_gcd_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nat_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [103#u32, 99#u32, 100#u32]) (by simp [core_k.nat_gcd_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Core.lean:515-515 natLandName` --
`core_k::nat_land_name` refines `natLandName`. -/
theorem nat_land_name_refines {n : name.Name} (h : core_k.nat_land_name = ok n) :
    absName n = ConLeche.natLandName ∧ NameWF n := by
  rw [core_k.nat_land_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nat_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [108#u32, 97#u32, 110#u32, 100#u32]) (by simp [core_k.nat_land_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Core.lean:516-516 natLorName` --
`core_k::nat_lor_name` refines `natLorName`. -/
theorem nat_lor_name_refines {n : name.Name} (h : core_k.nat_lor_name = ok n) :
    absName n = ConLeche.natLorName ∧ NameWF n := by
  rw [core_k.nat_lor_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nat_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [108#u32, 111#u32, 114#u32]) (by simp [core_k.nat_lor_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Core.lean:517-517 natXorName` --
`core_k::nat_xor_name` refines `natXorName`. -/
theorem nat_xor_name_refines {n : name.Name} (h : core_k.nat_xor_name = ok n) :
    absName n = ConLeche.natXorName ∧ NameWF n := by
  rw [core_k.nat_xor_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nat_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [120#u32, 111#u32, 114#u32]) (by simp [core_k.nat_xor_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Core.lean:518-518 natShiftLeftName` --
`core_k::nat_shift_left_name` refines `natShiftLeftName`. -/
theorem nat_shift_left_name_refines {n : name.Name} (h : core_k.nat_shift_left_name = ok n) :
    absName n = ConLeche.natShiftLeftName ∧ NameWF n := by
  rw [core_k.nat_shift_left_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nat_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [115#u32, 104#u32, 105#u32, 102#u32, 116#u32, 76#u32, 101#u32, 102#u32,
      116#u32]) (by simp [core_k.nat_shift_left_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Core.lean:519-519 natShiftRightName` --
`core_k::nat_shift_right_name` refines `natShiftRightName`. -/
theorem nat_shift_right_name_refines {n : name.Name} (h : core_k.nat_shift_right_name = ok n) :
    absName n = ConLeche.natShiftRightName ∧ NameWF n := by
  rw [core_k.nat_shift_right_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nat_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [115#u32, 104#u32, 105#u32, 102#u32, 116#u32, 82#u32, 105#u32, 103#u32, 104#u32,
      116#u32]) (by simp [core_k.nat_shift_right_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Core.lean:520-520 boolName` --
`core_k::bool_name` refines `boolName`. -/
theorem bool_name_refines {n : name.Name} (h : core_k.bool_name = ok n) :
    absName n = ConLeche.boolName ∧ NameWF n := by
  rw [core_k.bool_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [66#u32, 111#u32, 111#u32, 108#u32]) (by simp [core_k.bool_name.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Core.lean:521-521 boolTrueName` --
`core_k::bool_true_name` refines `boolTrueName`. -/
theorem bool_true_name_refines {n : name.Name} (h : core_k.bool_true_name = ok n) :
    absName n = ConLeche.boolTrueName ∧ NameWF n := by
  rw [core_k.bool_true_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := bool_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [116#u32, 114#u32, 117#u32, 101#u32]) (by simp [core_k.bool_true_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Core.lean:522-522 boolFalseName` --
`core_k::bool_false_name` refines `boolFalseName`. -/
theorem bool_false_name_refines {n : name.Name} (h : core_k.bool_false_name = ok n) :
    absName n = ConLeche.boolFalseName ∧ NameWF n := by
  rw [core_k.bool_false_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := bool_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [102#u32, 97#u32, 108#u32, 115#u32,
      101#u32]) (by simp [core_k.bool_false_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩
/-! ## The name tables -/

/-- `ConLeche/Kernel/Core.lean:545-553 natOpNames` --
`core_k::nat_op_names` refines `natOpNames`: the certified
structural-`Nat` operations, in the cited order. -/
theorem nat_op_names_refines {v : alloc.vec.Vec name.Name}
    (h : core_k.nat_op_names = ok v) :
    absNames v = ConLeche.natOpNames ∧ NamesWF v := by
  rw [core_k.nat_op_names] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨m0, hm0, w0, hw0, m1, hm1, w1, hw1, m2, hm2, w2, hw2, m3, hm3, w3, hw3, m4, hm4, w4,
    hw4, m5, hm5, w5, hw5, m6, hm6, hlast⟩ := h
  obtain ⟨e0, f0⟩ := nat_pred_name_refines hm0
  obtain ⟨e1, f1⟩ := nat_add_name_refines hm1
  obtain ⟨e2, f2⟩ := nat_sub_name_refines hm2
  obtain ⟨e3, f3⟩ := nat_mul_name_refines hm3
  obtain ⟨e4, f4⟩ := nat_pow_name_refines hm4
  obtain ⟨e5, f5⟩ := nat_beq_name_refines hm5
  obtain ⟨e6, f6⟩ := nat_ble_name_refines hm6
  have hval : v.val = [m0, m1, m2, m3, m4, m5, m6] := by
    rw [vec_push_val hlast, vec_push_val hw5, vec_push_val hw4, vec_push_val hw3,
      vec_push_val hw2, vec_push_val hw1, vec_push_val hw0]
    simp
  refine ⟨?_, ?_⟩
  · rw [absNames, hval]
    simp only [List.map_cons, List.map_nil, e0, e1, e2, e3, e4, e5, e6]
    rfl
  · intro x hx
    rw [hval] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    exacts [f0, f1, f2, f3, f4, f5, f6]

/-- `ConLeche/Kernel/Core.lean:555-570 natDivModNames` --
`core_k::nat_div_mod_names` refines `natDivModNames`. -/
theorem nat_div_mod_names_refines {v : alloc.vec.Vec name.Name}
    (h : core_k.nat_div_mod_names = ok v) :
    absNames v = ConLeche.natDivModNames ∧ NamesWF v := by
  rw [core_k.nat_div_mod_names] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨m0, hm0, w0, hw0, m1, hm1, w1, hw1, m2, hm2, w2, hw2, m3, hm3, w3, hw3, m4, hm4, w4,
    hw4, m5, hm5, w5, hw5, m6, hm6, w6, hw6, m7, hm7, hlast⟩ := h
  obtain ⟨e0, f0⟩ := nat_div_name_refines hm0
  obtain ⟨e1, f1⟩ := nat_mod_name_refines hm1
  obtain ⟨e2, f2⟩ := nat_gcd_name_refines hm2
  obtain ⟨e3, f3⟩ := nat_land_name_refines hm3
  obtain ⟨e4, f4⟩ := nat_lor_name_refines hm4
  obtain ⟨e5, f5⟩ := nat_xor_name_refines hm5
  obtain ⟨e6, f6⟩ := nat_shift_left_name_refines hm6
  obtain ⟨e7, f7⟩ := nat_shift_right_name_refines hm7
  have hval : v.val = [m0, m1, m2, m3, m4, m5, m6, m7] := by
    rw [vec_push_val hlast, vec_push_val hw6, vec_push_val hw5, vec_push_val hw4,
      vec_push_val hw3, vec_push_val hw2, vec_push_val hw1, vec_push_val hw0]
    simp
  refine ⟨?_, ?_⟩
  · rw [absNames, hval]
    simp only [List.map_cons, List.map_nil, e0, e1, e2, e3, e4, e5, e6, e7]
    rfl
  · intro x hx
    rw [hval] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    exacts [f0, f1, f2, f3, f4, f5, f6, f7]

/-- `ConLeche/Kernel/Core.lean:674-684 natOpWfNames` --
`core_k::nat_op_wf_names` refines `natOpWfNames` -- the same eight names as
`natDivModNames`, spelled separately in the Lean and separately here. -/
theorem nat_op_wf_names_refines {v : alloc.vec.Vec name.Name}
    (h : core_k.nat_op_wf_names = ok v) :
    absNames v = ConLeche.natOpWfNames ∧ NamesWF v := by
  rw [core_k.nat_op_wf_names] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨m0, hm0, w0, hw0, m1, hm1, w1, hw1, m2, hm2, w2, hw2, m3, hm3, w3, hw3, m4, hm4, w4,
    hw4, m5, hm5, w5, hw5, m6, hm6, w6, hw6, m7, hm7, hlast⟩ := h
  obtain ⟨e0, f0⟩ := nat_div_name_refines hm0
  obtain ⟨e1, f1⟩ := nat_mod_name_refines hm1
  obtain ⟨e2, f2⟩ := nat_gcd_name_refines hm2
  obtain ⟨e3, f3⟩ := nat_land_name_refines hm3
  obtain ⟨e4, f4⟩ := nat_lor_name_refines hm4
  obtain ⟨e5, f5⟩ := nat_xor_name_refines hm5
  obtain ⟨e6, f6⟩ := nat_shift_left_name_refines hm6
  obtain ⟨e7, f7⟩ := nat_shift_right_name_refines hm7
  have hval : v.val = [m0, m1, m2, m3, m4, m5, m6, m7] := by
    rw [vec_push_val hlast, vec_push_val hw6, vec_push_val hw5, vec_push_val hw4,
      vec_push_val hw3, vec_push_val hw2, vec_push_val hw1, vec_push_val hw0]
    simp
  refine ⟨?_, ?_⟩
  · rw [absNames, hval]
    simp only [List.map_cons, List.map_nil, e0, e1, e2, e3, e4, e5, e6, e7]
    rfl
  · intro x hx
    rw [hval] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    exacts [f0, f1, f2, f3, f4, f5, f6, f7]
/-! ## `nat_op_deps` -/

/-- `ConLeche/Kernel/Core.lean:572-595 natOpDeps` --
`core_k::nat_op_deps` refines `natOpDeps`: the cited `if … else if …` chain,
arm for arm, with the empty tail as the empty `Vec`. -/
theorem nat_op_deps_refines {c : name.Name} {v : alloc.vec.Vec name.Name}
    (hc : NameWF c) (h : core_k.nat_op_deps c = ok v) :
    absNames v = ConLeche.natOpDeps (absName c) ∧ NamesWF v := by
  rw [core_k.nat_op_deps] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n0, hn0, c0, hc0, h⟩ := h
  obtain ⟨e0, f0⟩ := nat_pred_name_refines hn0
  cases c0 with
  | true =>
    simp only [reduceIte] at h
    have hval : v.val = [n0] := by
      rw [vec_push_val h]; simp
    have hh : absName c = ConLeche.natPredName := by
      have hq := Name.beq_refines hc f0 hc0
      rw [e0] at hq; simpa using hq.symm
    refine ⟨?_, ?_⟩
    · rw [absNames, hval, hh]
      simp only [List.map_cons, List.map_nil, e0]
      rfl
    · intro x hx
      rw [hval] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl
      exacts [f0]
  | false =>
    simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
    have g0 : absName c ≠ ConLeche.natPredName := by
      have hq := Name.beq_refines hc f0 hc0
      rw [e0] at hq; simpa using hq.symm
    obtain ⟨n1, hn1, c1, hc1, h⟩ := h
    obtain ⟨e1, f1⟩ := nat_add_name_refines hn1
    cases c1 with
    | true =>
      simp only [reduceIte] at h
      have hval : v.val = [n1] := by
        rw [vec_push_val h]; simp
      have hh : absName c = ConLeche.natAddName := by
        have hq := Name.beq_refines hc f1 hc1
        rw [e1] at hq; simpa using hq.symm
      refine ⟨?_, ?_⟩
      · rw [absNames, hval, hh]
        simp only [List.map_cons, List.map_nil, e1]
        rfl
      · intro x hx
        rw [hval] at hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl
        exacts [f1]
    | false =>
      simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
      have g1 : absName c ≠ ConLeche.natAddName := by
        have hq := Name.beq_refines hc f1 hc1
        rw [e1] at hq; simpa using hq.symm
      obtain ⟨n2, hn2, c2, hc2, h⟩ := h
      obtain ⟨e2, f2⟩ := nat_sub_name_refines hn2
      cases c2 with
      | true =>
        simp only [reduceIte, bind_eq_ok_iff] at h
        obtain ⟨w0, p0, plast⟩ := h
        have hval : v.val = [n0, n2] := by
          rw [vec_push_val plast, vec_push_val p0]
          simp
        have hh : absName c = ConLeche.natSubName := by
          have hq := Name.beq_refines hc f2 hc2
          rw [e2] at hq; simpa using hq.symm
        refine ⟨?_, ?_⟩
        · rw [absNames, hval, hh]
          simp only [List.map_cons, List.map_nil, e0, e2]
          rfl
        · intro x hx
          rw [hval] at hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl|rfl
          exacts [f0, f2]
      | false =>
        simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
        have g2 : absName c ≠ ConLeche.natSubName := by
          have hq := Name.beq_refines hc f2 hc2
          rw [e2] at hq; simpa using hq.symm
        obtain ⟨n3, hn3, c3, hc3, h⟩ := h
        obtain ⟨e3, f3⟩ := nat_mul_name_refines hn3
        cases c3 with
        | true =>
          simp only [reduceIte, bind_eq_ok_iff] at h
          obtain ⟨w0, p0, plast⟩ := h
          have hval : v.val = [n1, n3] := by
            rw [vec_push_val plast, vec_push_val p0]
            simp
          have hh : absName c = ConLeche.natMulName := by
            have hq := Name.beq_refines hc f3 hc3
            rw [e3] at hq; simpa using hq.symm
          refine ⟨?_, ?_⟩
          · rw [absNames, hval, hh]
            simp only [List.map_cons, List.map_nil, e1, e3]
            rfl
          · intro x hx
            rw [hval] at hx
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl|rfl
            exacts [f1, f3]
        | false =>
          simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
          have g3 : absName c ≠ ConLeche.natMulName := by
            have hq := Name.beq_refines hc f3 hc3
            rw [e3] at hq; simpa using hq.symm
          obtain ⟨n4, hn4, c4, hc4, h⟩ := h
          obtain ⟨e4, f4⟩ := nat_pow_name_refines hn4
          cases c4 with
          | true =>
            simp only [reduceIte, bind_eq_ok_iff] at h
            obtain ⟨w0, p0, w1, p1, plast⟩ := h
            have hval : v.val = [n1, n3, n4] := by
              rw [vec_push_val plast, vec_push_val p1, vec_push_val p0]
              simp
            have hh : absName c = ConLeche.natPowName := by
              have hq := Name.beq_refines hc f4 hc4
              rw [e4] at hq; simpa using hq.symm
            refine ⟨?_, ?_⟩
            · rw [absNames, hval, hh]
              simp only [List.map_cons, List.map_nil, e1, e3, e4]
              rfl
            · intro x hx
              rw [hval] at hx
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl|rfl|rfl
              exacts [f1, f3, f4]
          | false =>
            simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
            have g4 : absName c ≠ ConLeche.natPowName := by
              have hq := Name.beq_refines hc f4 hc4
              rw [e4] at hq; simpa using hq.symm
            obtain ⟨n5, hn5, c5, hc5, h⟩ := h
            obtain ⟨e5, f5⟩ := nat_beq_name_refines hn5
            cases c5 with
            | true =>
              simp only [reduceIte] at h
              have hval : v.val = [n5] := by
                rw [vec_push_val h]; simp
              have hh : absName c = ConLeche.natBeqName := by
                have hq := Name.beq_refines hc f5 hc5
                rw [e5] at hq; simpa using hq.symm
              refine ⟨?_, ?_⟩
              · rw [absNames, hval, hh]
                simp only [List.map_cons, List.map_nil, e5]
                rfl
              · intro x hx
                rw [hval] at hx
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with rfl
                exacts [f5]
            | false =>
              simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
              have g5 : absName c ≠ ConLeche.natBeqName := by
                have hq := Name.beq_refines hc f5 hc5
                rw [e5] at hq; simpa using hq.symm
              obtain ⟨n6, hn6, c6, hc6, h⟩ := h
              obtain ⟨e6, f6⟩ := nat_ble_name_refines hn6
              cases c6 with
              | true =>
                simp only [reduceIte] at h
                have hval : v.val = [n6] := by
                  rw [vec_push_val h]; simp
                have hh : absName c = ConLeche.natBleName := by
                  have hq := Name.beq_refines hc f6 hc6
                  rw [e6] at hq; simpa using hq.symm
                refine ⟨?_, ?_⟩
                · rw [absNames, hval, hh]
                  simp only [List.map_cons, List.map_nil, e6]
                  rfl
                · intro x hx
                  rw [hval] at hx
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                  rcases hx with rfl
                  exacts [f6]
              | false =>
                simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
                have g6 : absName c ≠ ConLeche.natBleName := by
                  have hq := Name.beq_refines hc f6 hc6
                  rw [e6] at hq; simpa using hq.symm
                obtain ⟨n7, hn7, c7, hc7, h⟩ := h
                obtain ⟨e7, f7⟩ := nat_div_name_refines hn7
                cases c7 with
                | true =>
                  simp only [reduceIte, bind_eq_ok_iff] at h
                  obtain ⟨w0, p0, w1, p1, w2, p2, plast⟩ := h
                  have hval : v.val = [n0, n2, n6, n7] := by
                    rw [vec_push_val plast, vec_push_val p2,
                      vec_push_val p1, vec_push_val p0]
                    simp
                  have hh : absName c = ConLeche.natDivName := by
                    have hq := Name.beq_refines hc f7 hc7
                    rw [e7] at hq; simpa using hq.symm
                  refine ⟨?_, ?_⟩
                  · rw [absNames, hval, hh]
                    simp only [List.map_cons, List.map_nil, e0, e2, e6, e7]
                    rfl
                  · intro x hx
                    rw [hval] at hx
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                    rcases hx with rfl|rfl|rfl|rfl
                    exacts [f0, f2, f6, f7]
                | false =>
                  simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
                  have g7 : absName c ≠ ConLeche.natDivName := by
                    have hq := Name.beq_refines hc f7 hc7
                    rw [e7] at hq; simpa using hq.symm
                  obtain ⟨n8, hn8, c8, hc8, h⟩ := h
                  obtain ⟨e8, f8⟩ := nat_mod_name_refines hn8
                  cases c8 with
                  | true =>
                    simp only [reduceIte, bind_eq_ok_iff] at h
                    obtain ⟨w0, p0, w1, p1, w2, p2, plast⟩ := h
                    have hval : v.val = [n0, n2, n6, n8] := by
                      rw [vec_push_val plast, vec_push_val p2,
                        vec_push_val p1, vec_push_val p0]
                      simp
                    have hh : absName c = ConLeche.natModName := by
                      have hq := Name.beq_refines hc f8 hc8
                      rw [e8] at hq; simpa using hq.symm
                    refine ⟨?_, ?_⟩
                    · rw [absNames, hval, hh]
                      simp only [List.map_cons, List.map_nil, e0, e2, e6, e8]
                      rfl
                    · intro x hx
                      rw [hval] at hx
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                      rcases hx with rfl|rfl|rfl|rfl
                      exacts [f0, f2, f6, f8]
                  | false =>
                    simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
                    have g8 : absName c ≠ ConLeche.natModName := by
                      have hq := Name.beq_refines hc f8 hc8
                      rw [e8] at hq; simpa using hq.symm
                    obtain ⟨n9, hn9, c9, hc9, h⟩ := h
                    obtain ⟨e9, f9⟩ := nat_gcd_name_refines hn9
                    cases c9 with
                    | true =>
                      simp only [reduceIte, bind_eq_ok_iff] at h
                      obtain ⟨w0, p0, w1, p1, plast⟩ := h
                      have hval : v.val = [n6, n8, n9] := by
                        rw [vec_push_val plast, vec_push_val p1, vec_push_val p0]
                        simp
                      have hh : absName c = ConLeche.natGcdName := by
                        have hq := Name.beq_refines hc f9 hc9
                        rw [e9] at hq; simpa using hq.symm
                      refine ⟨?_, ?_⟩
                      · rw [absNames, hval, hh]
                        simp only [List.map_cons, List.map_nil, e6, e8, e9]
                        rfl
                      · intro x hx
                        rw [hval] at hx
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                        rcases hx with rfl|rfl|rfl
                        exacts [f6, f8, f9]
                    | false =>
                      simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
                      have g9 : absName c ≠ ConLeche.natGcdName := by
                        have hq := Name.beq_refines hc f9 hc9
                        rw [e9] at hq; simpa using hq.symm
                      obtain ⟨n10, hn10, c10, hc10, h⟩ := h
                      obtain ⟨e10, f10⟩ := nat_land_name_refines hn10
                      cases c10 with
                      | true =>
                        simp only [reduceIte, bind_eq_ok_iff] at h
                        obtain ⟨w0, p0, w1, p1, w2, p2, w3, p3, w4, p4, plast⟩ := h
                        have hval : v.val = [n1, n3, n6, n7, n8, n10] := by
                          rw [vec_push_val plast, vec_push_val p4,
                            vec_push_val p3, vec_push_val p2, vec_push_val p1, vec_push_val p0]
                          simp
                        have hh : absName c = ConLeche.natLandName := by
                          have hq := Name.beq_refines hc f10 hc10
                          rw [e10] at hq; simpa using hq.symm
                        refine ⟨?_, ?_⟩
                        · rw [absNames, hval, hh]
                          simp only [List.map_cons, List.map_nil, e1, e3, e6, e7, e8, e10]
                          rfl
                        · intro x hx
                          rw [hval] at hx
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                          rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
                          exacts [f1, f3, f6, f7, f8, f10]
                      | false =>
                        simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
                        have g10 : absName c ≠ ConLeche.natLandName := by
                          have hq := Name.beq_refines hc f10 hc10
                          rw [e10] at hq; simpa using hq.symm
                        obtain ⟨n11, hn11, c11, hc11, h⟩ := h
                        obtain ⟨e11, f11⟩ := nat_lor_name_refines hn11
                        cases c11 with
                        | true =>
                          simp only [reduceIte, bind_eq_ok_iff] at h
                          obtain ⟨w0, p0, w1, p1, w2, p2, w3, p3, w4, p4, w5, p5, plast⟩ := h
                          have hval : v.val = [n1, n2, n3, n6, n7, n8, n11] := by
                            rw [vec_push_val plast, vec_push_val p5,
                              vec_push_val p4, vec_push_val p3, vec_push_val p2, vec_push_val p1,
                                vec_push_val p0]
                            simp
                          have hh : absName c = ConLeche.natLorName := by
                            have hq := Name.beq_refines hc f11 hc11
                            rw [e11] at hq; simpa using hq.symm
                          refine ⟨?_, ?_⟩
                          · rw [absNames, hval, hh]
                            simp only [List.map_cons, List.map_nil, e1, e2, e3, e6, e7, e8, e11]
                            rfl
                          · intro x hx
                            rw [hval] at hx
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                            rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl
                            exacts [f1, f2, f3, f6, f7, f8, f11]
                        | false =>
                          simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
                          have g11 : absName c ≠ ConLeche.natLorName := by
                            have hq := Name.beq_refines hc f11 hc11
                            rw [e11] at hq; simpa using hq.symm
                          obtain ⟨n12, hn12, c12, hc12, h⟩ := h
                          obtain ⟨e12, f12⟩ := nat_xor_name_refines hn12
                          cases c12 with
                          | true =>
                            simp only [reduceIte, bind_eq_ok_iff] at h
                            obtain ⟨w0, p0, w1, p1, w2, p2, w3, p3, w4, p4, plast⟩ := h
                            have hval : v.val = [n1, n3, n6, n7, n8, n12] := by
                              rw [vec_push_val plast, vec_push_val p4,
                                vec_push_val p3, vec_push_val p2, vec_push_val p1,
                                  vec_push_val p0]
                              simp
                            have hh : absName c = ConLeche.natXorName := by
                              have hq := Name.beq_refines hc f12 hc12
                              rw [e12] at hq; simpa using hq.symm
                            refine ⟨?_, ?_⟩
                            · rw [absNames, hval, hh]
                              simp only [List.map_cons, List.map_nil, e1, e3, e6, e7, e8, e12]
                              rfl
                            · intro x hx
                              rw [hval] at hx
                              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                              rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
                              exacts [f1, f3, f6, f7, f8, f12]
                          | false =>
                            simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
                            have g12 : absName c ≠ ConLeche.natXorName := by
                              have hq := Name.beq_refines hc f12 hc12
                              rw [e12] at hq; simpa using hq.symm
                            obtain ⟨n13, hn13, c13, hc13, h⟩ := h
                            obtain ⟨e13, f13⟩ := nat_shift_left_name_refines hn13
                            cases c13 with
                            | true =>
                              simp only [reduceIte, bind_eq_ok_iff] at h
                              obtain ⟨w0, p0, w1, p1, w2, p2, plast⟩ := h
                              have hval : v.val = [n2, n3, n6, n13] := by
                                rw [vec_push_val plast, vec_push_val p2,
                                  vec_push_val p1, vec_push_val p0]
                                simp
                              have hh : absName c = ConLeche.natShiftLeftName := by
                                have hq := Name.beq_refines hc f13 hc13
                                rw [e13] at hq; simpa using hq.symm
                              refine ⟨?_, ?_⟩
                              · rw [absNames, hval, hh]
                                simp only [List.map_cons, List.map_nil, e2, e3, e6, e13]
                                rfl
                              · intro x hx
                                rw [hval] at hx
                                simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                                rcases hx with rfl|rfl|rfl|rfl
                                exacts [f2, f3, f6, f13]
                            | false =>
                              simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
                              have g13 : absName c ≠ ConLeche.natShiftLeftName := by
                                have hq := Name.beq_refines hc f13 hc13
                                rw [e13] at hq; simpa using hq.symm
                              obtain ⟨n14, hn14, c14, hc14, h⟩ := h
                              obtain ⟨e14, f14⟩ := nat_shift_right_name_refines hn14
                              cases c14 with
                              | true =>
                                simp only [reduceIte, bind_eq_ok_iff] at h
                                obtain ⟨w0, p0, w1, p1, w2, p2, plast⟩ := h
                                have hval : v.val = [n2, n6, n7, n14] := by
                                  rw [vec_push_val plast, vec_push_val p2,
                                    vec_push_val p1, vec_push_val p0]
                                  simp
                                have hh : absName c = ConLeche.natShiftRightName := by
                                  have hq := Name.beq_refines hc f14 hc14
                                  rw [e14] at hq; simpa using hq.symm
                                refine ⟨?_, ?_⟩
                                · rw [absNames, hval, hh]
                                  simp only [List.map_cons, List.map_nil, e2, e6, e7, e14]
                                  rfl
                                · intro x hx
                                  rw [hval] at hx
                                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                                  rcases hx with rfl|rfl|rfl|rfl
                                  exacts [f2, f6, f7, f14]
                              | false =>
                                simp only [Bool.false_eq_true, reduceIte] at h
                                have g14 : absName c ≠ ConLeche.natShiftRightName := by
                                  have hq := Name.beq_refines hc f14 hc14
                                  rw [e14] at hq; simpa using hq.symm
                                have hv : v = alloc.vec.Vec.new name.Name :=
                                  (Result.ok_injective h).symm
                                have hd : ConLeche.natOpDeps (absName c) = [] := by
                                  simp only [ConLeche.natOpDeps, g0, g1, g2, g3, g4, g5,
                                    g6, g7, g8, g9, g10, g11, g12, g13, g14, reduceIte]
                                refine ⟨by rw [absNames, hv, hd]; rfl, ?_⟩
                                intro x hx; rw [hv] at hx; simp at hx
/-! ## `is_nat_bin_op` -/

/-- `ConLeche/Kernel/Core.lean:774-826 reduceNat` --
`core_k::is_nat_bin_op` is the fourteen-way `∨`-chain of the cited `reduceNat`
guard, as its own predicate: the cited Lean has no `def` of its own for it, so
the chain is spelled out in the statement. -/
theorem is_nat_bin_op_refines {c : name.Name} {b : Bool} (hc : NameWF c)
    (h : core_k.is_nat_bin_op c = ok b) :
    b = decide (absName c = ConLeche.natAddName ∨ absName c = ConLeche.natSubName ∨
      absName c = ConLeche.natMulName ∨ absName c = ConLeche.natPowName ∨
      absName c = ConLeche.natBeqName ∨ absName c = ConLeche.natBleName ∨
      absName c = ConLeche.natDivName ∨ absName c = ConLeche.natModName ∨
      absName c = ConLeche.natGcdName ∨ absName c = ConLeche.natLandName ∨
      absName c = ConLeche.natLorName ∨ absName c = ConLeche.natXorName ∨
      absName c = ConLeche.natShiftLeftName ∨
      absName c = ConLeche.natShiftRightName) := by
  rw [core_k.is_nat_bin_op] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n0, hn0, c0, hc0, h⟩ := h
  obtain ⟨e0, f0⟩ := nat_add_name_refines hn0
  cases c0 with
  | true =>
    simp only [reduceIte] at h
    have hh : absName c = ConLeche.natAddName := by
      have hq := Name.beq_refines hc f0 hc0
      rw [e0] at hq; simpa using hq.symm
    exact (Result.ok_injective h).symm.trans
      (decide_eq_true (by simp [hh])).symm
  | false =>
    simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
    have g0 : absName c ≠ ConLeche.natAddName := by
      have hq := Name.beq_refines hc f0 hc0
      rw [e0] at hq; simpa using hq.symm
    obtain ⟨n1, hn1, c1, hc1, h⟩ := h
    obtain ⟨e1, f1⟩ := nat_sub_name_refines hn1
    cases c1 with
    | true =>
      simp only [reduceIte] at h
      have hh : absName c = ConLeche.natSubName := by
        have hq := Name.beq_refines hc f1 hc1
        rw [e1] at hq; simpa using hq.symm
      exact (Result.ok_injective h).symm.trans
        (decide_eq_true (by simp [hh])).symm
    | false =>
      simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
      have g1 : absName c ≠ ConLeche.natSubName := by
        have hq := Name.beq_refines hc f1 hc1
        rw [e1] at hq; simpa using hq.symm
      obtain ⟨n2, hn2, c2, hc2, h⟩ := h
      obtain ⟨e2, f2⟩ := nat_mul_name_refines hn2
      cases c2 with
      | true =>
        simp only [reduceIte] at h
        have hh : absName c = ConLeche.natMulName := by
          have hq := Name.beq_refines hc f2 hc2
          rw [e2] at hq; simpa using hq.symm
        exact (Result.ok_injective h).symm.trans
          (decide_eq_true (by simp [hh])).symm
      | false =>
        simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
        have g2 : absName c ≠ ConLeche.natMulName := by
          have hq := Name.beq_refines hc f2 hc2
          rw [e2] at hq; simpa using hq.symm
        obtain ⟨n3, hn3, c3, hc3, h⟩ := h
        obtain ⟨e3, f3⟩ := nat_pow_name_refines hn3
        cases c3 with
        | true =>
          simp only [reduceIte] at h
          have hh : absName c = ConLeche.natPowName := by
            have hq := Name.beq_refines hc f3 hc3
            rw [e3] at hq; simpa using hq.symm
          exact (Result.ok_injective h).symm.trans
            (decide_eq_true (by simp [hh])).symm
        | false =>
          simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
          have g3 : absName c ≠ ConLeche.natPowName := by
            have hq := Name.beq_refines hc f3 hc3
            rw [e3] at hq; simpa using hq.symm
          obtain ⟨n4, hn4, c4, hc4, h⟩ := h
          obtain ⟨e4, f4⟩ := nat_beq_name_refines hn4
          cases c4 with
          | true =>
            simp only [reduceIte] at h
            have hh : absName c = ConLeche.natBeqName := by
              have hq := Name.beq_refines hc f4 hc4
              rw [e4] at hq; simpa using hq.symm
            exact (Result.ok_injective h).symm.trans
              (decide_eq_true (by simp [hh])).symm
          | false =>
            simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
            have g4 : absName c ≠ ConLeche.natBeqName := by
              have hq := Name.beq_refines hc f4 hc4
              rw [e4] at hq; simpa using hq.symm
            obtain ⟨n5, hn5, c5, hc5, h⟩ := h
            obtain ⟨e5, f5⟩ := nat_ble_name_refines hn5
            cases c5 with
            | true =>
              simp only [reduceIte] at h
              have hh : absName c = ConLeche.natBleName := by
                have hq := Name.beq_refines hc f5 hc5
                rw [e5] at hq; simpa using hq.symm
              exact (Result.ok_injective h).symm.trans
                (decide_eq_true (by simp [hh])).symm
            | false =>
              simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
              have g5 : absName c ≠ ConLeche.natBleName := by
                have hq := Name.beq_refines hc f5 hc5
                rw [e5] at hq; simpa using hq.symm
              obtain ⟨n6, hn6, c6, hc6, h⟩ := h
              obtain ⟨e6, f6⟩ := nat_div_name_refines hn6
              cases c6 with
              | true =>
                simp only [reduceIte] at h
                have hh : absName c = ConLeche.natDivName := by
                  have hq := Name.beq_refines hc f6 hc6
                  rw [e6] at hq; simpa using hq.symm
                exact (Result.ok_injective h).symm.trans
                  (decide_eq_true (by simp [hh])).symm
              | false =>
                simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
                have g6 : absName c ≠ ConLeche.natDivName := by
                  have hq := Name.beq_refines hc f6 hc6
                  rw [e6] at hq; simpa using hq.symm
                obtain ⟨n7, hn7, c7, hc7, h⟩ := h
                obtain ⟨e7, f7⟩ := nat_mod_name_refines hn7
                cases c7 with
                | true =>
                  simp only [reduceIte] at h
                  have hh : absName c = ConLeche.natModName := by
                    have hq := Name.beq_refines hc f7 hc7
                    rw [e7] at hq; simpa using hq.symm
                  exact (Result.ok_injective h).symm.trans
                    (decide_eq_true (by simp [hh])).symm
                | false =>
                  simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
                  have g7 : absName c ≠ ConLeche.natModName := by
                    have hq := Name.beq_refines hc f7 hc7
                    rw [e7] at hq; simpa using hq.symm
                  obtain ⟨n8, hn8, c8, hc8, h⟩ := h
                  obtain ⟨e8, f8⟩ := nat_gcd_name_refines hn8
                  cases c8 with
                  | true =>
                    simp only [reduceIte] at h
                    have hh : absName c = ConLeche.natGcdName := by
                      have hq := Name.beq_refines hc f8 hc8
                      rw [e8] at hq; simpa using hq.symm
                    exact (Result.ok_injective h).symm.trans
                      (decide_eq_true (by simp [hh])).symm
                  | false =>
                    simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
                    have g8 : absName c ≠ ConLeche.natGcdName := by
                      have hq := Name.beq_refines hc f8 hc8
                      rw [e8] at hq; simpa using hq.symm
                    obtain ⟨n9, hn9, c9, hc9, h⟩ := h
                    obtain ⟨e9, f9⟩ := nat_land_name_refines hn9
                    cases c9 with
                    | true =>
                      simp only [reduceIte] at h
                      have hh : absName c = ConLeche.natLandName := by
                        have hq := Name.beq_refines hc f9 hc9
                        rw [e9] at hq; simpa using hq.symm
                      exact (Result.ok_injective h).symm.trans
                        (decide_eq_true (by simp [hh])).symm
                    | false =>
                      simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
                      have g9 : absName c ≠ ConLeche.natLandName := by
                        have hq := Name.beq_refines hc f9 hc9
                        rw [e9] at hq; simpa using hq.symm
                      obtain ⟨n10, hn10, c10, hc10, h⟩ := h
                      obtain ⟨e10, f10⟩ := nat_lor_name_refines hn10
                      cases c10 with
                      | true =>
                        simp only [reduceIte] at h
                        have hh : absName c = ConLeche.natLorName := by
                          have hq := Name.beq_refines hc f10 hc10
                          rw [e10] at hq; simpa using hq.symm
                        exact (Result.ok_injective h).symm.trans
                          (decide_eq_true (by simp [hh])).symm
                      | false =>
                        simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
                        have g10 : absName c ≠ ConLeche.natLorName := by
                          have hq := Name.beq_refines hc f10 hc10
                          rw [e10] at hq; simpa using hq.symm
                        obtain ⟨n11, hn11, c11, hc11, h⟩ := h
                        obtain ⟨e11, f11⟩ := nat_xor_name_refines hn11
                        cases c11 with
                        | true =>
                          simp only [reduceIte] at h
                          have hh : absName c = ConLeche.natXorName := by
                            have hq := Name.beq_refines hc f11 hc11
                            rw [e11] at hq; simpa using hq.symm
                          exact (Result.ok_injective h).symm.trans
                            (decide_eq_true (by simp [hh])).symm
                        | false =>
                          simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
                          have g11 : absName c ≠ ConLeche.natXorName := by
                            have hq := Name.beq_refines hc f11 hc11
                            rw [e11] at hq; simpa using hq.symm
                          obtain ⟨n12, hn12, c12, hc12, h⟩ := h
                          obtain ⟨e12, f12⟩ := nat_shift_left_name_refines hn12
                          cases c12 with
                          | true =>
                            simp only [reduceIte] at h
                            have hh : absName c = ConLeche.natShiftLeftName := by
                              have hq := Name.beq_refines hc f12 hc12
                              rw [e12] at hq; simpa using hq.symm
                            exact (Result.ok_injective h).symm.trans
                              (decide_eq_true (by simp [hh])).symm
                          | false =>
                            simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
                            have g12 : absName c ≠ ConLeche.natShiftLeftName := by
                              have hq := Name.beq_refines hc f12 hc12
                              rw [e12] at hq; simpa using hq.symm
                            obtain ⟨n13, hn13, hlast⟩ := h
                            obtain ⟨e13, f13⟩ := nat_shift_right_name_refines hn13
                            rw [Name.beq_refines hc f13 hlast, e13]
                            simp only [g0, g1, g2, g3, g4, g5, g6,
                              g7, g8, g9, g10, g11, g12, false_or]
/-! ## `projModelName`: the decimal recursion and the model-side name -/

/-- The `%` twin of `HashMap.uscalar_div_eq`.  **Belongs in `CoreKBase.lean`**
(or beside its siblings in `Refine/HashMap.lean`'s `Scalars` section); it is
written here because this is the first file that needs a `%`. -/
theorem uscalar_rem_eq {ty : UScalarTy} {x y z : UScalar ty} (hy : y.val ≠ 0)
    (h : x % y = ok z) : z.val = x.val % y.val := by
  obtain ⟨w, hw, hval⟩ := WP.spec_imp_exists (UScalar.rem_bv_spec x hy)
  rw [h] at hw
  rw [Result.ok_injective hw]; exact hval.1

/-- A `u64`-to-`u32` cast is the identity below `10` -- the only values
`nat_to_dec_go` casts (`ExprOps.lean`'s `u64_cast_usize_val` is the `usize`
twin). -/
theorem u64_cast_u32_val_of_lt_ten {x : Std.U64} (h : x.val < 10) :
    (Std.UScalar.cast .U32 x).val = x.val := by
  refine Std.UScalar.cast_val_mod_pow_of_inBounds_eq _ _ ?_
  have hb : (10 : Nat) ≤ 2 ^ UScalarTy.U32.numBits := by
    rw [UScalarTy.U32_numBits_eq]; decide
  omega

/-- `absCodes` of a concatenation: `proj_model_name` builds its suffix as
`"proj_" ++ toString i`. -/
theorem absCodes_append (l₁ l₂ : List Std.U32) :
    absCodes (l₁ ++ l₂) = absCodes l₁ ++ absCodes l₂ := by
  simp [absCodes, String.ofList_append]

/-- `ConLeche/Kernel/Core.lean:113-116 projModelName` --
the digit recursion of `core_k::nat_to_dec_go`: the accumulator with `i`'s
decimal characters appended, most significant first.  Lean's `toString` on a
`Nat` is `String.ofList (Nat.toDigits 10 ·)`, and `Nat.toDigits_of_lt_base` /
`Nat.toDigits_of_base_le` are exactly the port's two arms, so the induction is
the strong one on the number `i.val` itself and the only arithmetic needed is
`Nat.toNat_digitChar_of_lt_ten` with `Char.ofNat_toNat`. -/
theorem nat_to_dec_go_val (N : Nat) :
    ∀ (i : Std.U64) (out r : alloc.vec.Vec Std.U32), i.val = N → StrWF out →
      core_k.nat_to_dec_go i out = ok r →
      r.val.map (fun c => Char.ofNat c.val)
          = out.val.map (fun c => Char.ofNat c.val) ++ Nat.toDigits 10 i.val
        ∧ StrWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro i out r hN hwf h
    rw [core_k.nat_to_dec_go.eq_def] at h
    split at h
    next hlt =>
      simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, exists_eq_left'] at h
      have hiv : i.val < 10 := by scalar_tac
      obtain ⟨d, hd, hpush⟩ := h
      have hdv : d.val = 48 + i.val := by
        rw [HashMap.uscalar_add_eq hd, u64_cast_u32_val_of_lt_ten hiv]; rfl
      refine ⟨?_, ?_⟩
      · rw [vec_push_val hpush, Nat.toDigits_of_lt_base (b := 10) hiv]
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [hdv, ← Nat.toNat_digitChar_of_lt_ten hiv, Char.ofNat_toNat]
      · intro cc hcc
        rw [vec_push_val hpush] at hcc
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcc
        rcases hcc with hcc | rfl
        · exact hwf cc hcc
        · exact Or.inl (by omega)
    next hge =>
      simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, exists_eq_left'] at h
      have hiv : 10 ≤ i.val := by scalar_tac
      obtain ⟨q, hq, out1, hrec, m, hm, d, hd, hpush⟩ := h
      have hqv : q.val = i.val / 10 := by
        rw [HashMap.uscalar_div_eq hq]; rfl
      have h10 : ((10#u64 : Std.U64)).val ≠ 0 := by decide
      have hmv : m.val = i.val % 10 := by
        rw [uscalar_rem_eq h10 hm]; rfl
      have hmlt : m.val < 10 := by rw [hmv]; omega
      obtain ⟨hr1, hr2⟩ := ih q.val (by rw [hqv, ← hN]; omega) q out out1 rfl hwf hrec
      have hdv : d.val = 48 + m.val := by
        rw [HashMap.uscalar_add_eq hd, u64_cast_u32_val_of_lt_ten hmlt]; rfl
      refine ⟨?_, ?_⟩
      · rw [vec_push_val hpush, Nat.toDigits_of_base_le (b := 10) (by omega) hiv]
        simp only [List.map_append, List.map_cons, List.map_nil, hr1, hqv]
        rw [List.append_assoc, hdv, hmv,
          ← Nat.toNat_digitChar_of_lt_ten (n := i.val % 10) (by omega), Char.ofNat_toNat]
      · intro cc hcc
        rw [vec_push_val hpush] at hcc
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcc
        rcases hcc with hcc | rfl
        · exact hr2 cc hcc
        · exact Or.inl (by omega)

/-- `ConLeche/Kernel/Core.lean:113-116 projModelName` --
`core_k::nat_to_dec_go` in the §3.5 shape, read off the induction above: the
accumulator with `toString i` appended. -/
theorem nat_to_dec_go_refines {i : Std.U64} {out r : alloc.vec.Vec Std.U32}
    (hwf : StrWF out) (h : core_k.nat_to_dec_go i out = ok r) :
    absCodes r.val = absCodes out.val ++ toString i.val ∧ StrWF r := by
  obtain ⟨h1, h2⟩ := nat_to_dec_go_val i.val i out r rfl hwf h
  refine ⟨?_, h2⟩
  simp only [absCodes, h1, Nat.toString_eq_ofList_toDigits, String.ofList_append]

/-- `ConLeche/Kernel/Core.lean:113-116 projModelName` --
`core_k::nat_to_dec` is Lean's `toString` on the `u64` index, and the code
points it produces are valid `Char`s. -/
theorem nat_to_dec_refines {i : Std.U64} {r : alloc.vec.Vec Std.U32}
    (h : core_k.nat_to_dec i = ok r) :
    absCodes r.val = toString i.val ∧ StrWF r := by
  rw [core_k.nat_to_dec] at h
  obtain ⟨h1, h2⟩ := nat_to_dec_go_val i.val i (alloc.vec.Vec.new Std.U32) r rfl
    (by intro c hc; simp at hc) h
  refine ⟨?_, h2⟩
  rw [absCodes, h1, Nat.toString_eq_ofList_toDigits]
  simp

/-- `ConLeche/Kernel/Core.lean:113-116 projModelName` --
`core_k::proj_model_name` refines `projModelName`, i.e.
`(T.str "_model").str ("proj_" ++ toString i)`. -/
theorem proj_model_name_refines {t : name.Name} {i : Std.U64} {n : name.Name}
    (ht : NameWF t) (h : core_k.proj_model_name t i = ok n) :
    absName n = ConLeche.projModelName (absName t) i.val ∧ NameWF n := by
  rw [core_k.proj_model_name] at h
  simp only [bind_eq_ok_iff, name_dup_eq, lift_eq, Result.ok.injEq,
    exists_eq_left'] at h
  obtain ⟨v, hv, head, hhead, s2, hs2, dgs, hdgs, s4, hs4, hmk⟩ := h
  obtain ⟨hh1, hh2⟩ := str_lit_step ht rfl hv hhead
    (L := [95#u32, 109#u32, 111#u32, 100#u32, 101#u32, 108#u32])
    (by simp [core_k.proj_model_name.MODEL]) (by decide)
  obtain ⟨hdg, hdgwf⟩ := nat_to_dec_refines hdgs
  have hs2v : s2.val = [112#u32, 114#u32, 111#u32, 106#u32, 95#u32] := by
    rw [code_points_val hs2, Array.val_to_slice]
    simp [core_k.proj_model_name.PROJ_]
  have hs4v : s4.val = s2.val ++ dgs.val := by
    rw [code_points_from_val _ (alloc.vec.Vec.deref dgs) 0#usize s2 s4 rfl hs4]
    simp [alloc.vec.Vec.deref]
  have hs4wf : StrWF s4 := by
    intro cc hcc
    rw [hs4v, hs2v] at hcc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcc
    rcases hcc with (rfl | rfl | rfl | rfl | rfl) | hcc
    · decide
    · decide
    · decide
    · decide
    · decide
    · exact hdgwf cc hcc
  refine ⟨?_, NameWF.str hh2 hs4wf hmk⟩
  rw [Name.mk_str_refines hmk, hh1, absString_eq, hs4v, absCodes_append, hs2v,
    hdg]
  rfl

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/--
info: 'ConRon.Refine.CoreK.proj_model_name_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms proj_model_name_refines

end ConRon.Refine.CoreK

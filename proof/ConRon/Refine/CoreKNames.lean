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

end ConRon.Refine.CoreK

/-
# `ConRon.Refine2.Frontend.NatOpDeps` — `arena::core::nat_op_deps` against `natOpDeps`

**Task #97-T2-LOCKSTEP lane Frontend round 3.**  The port reads the fifteen
operation pins into a `NatOpPins` record (`nat_op_pins`, split in two by the
extraction) and tests `c` against them; the twin (`Arena/Core.lean:882`) reads
the same fifteen pins in the same order and tests the same chain.  The pin
readers are one `@[lockstep]` lemma each; the record is a Rust-only repack.

## `sorry` count in this file: 0
-/
import ConRon.Refine2.Checker.Base

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend

open ConRon.Arena
open ConRon.Refine2.Lockstep

@[lockstep] theorem nat_pred_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_pred_name st) lst natPredName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv
    (fun _ hr => pin_nat_pred_refines hrel hinv hr) (by rw [arena.core.nat_pred_name] at h; exact h)

@[lockstep] theorem nat_add_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_add_name st) lst natAddName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv
    (fun _ hr => pin_nat_add_refines hrel hinv hr) (by rw [arena.core.nat_add_name] at h; exact h)

@[lockstep] theorem nat_sub_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_sub_name st) lst natSubName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv
    (fun _ hr => pin_nat_sub_refines hrel hinv hr) (by rw [arena.core.nat_sub_name] at h; exact h)

@[lockstep] theorem nat_mul_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_mul_name st) lst natMulName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv
    (fun _ hr => pin_nat_mul_refines hrel hinv hr) (by rw [arena.core.nat_mul_name] at h; exact h)

@[lockstep] theorem nat_pow_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_pow_name st) lst natPowName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv
    (fun _ hr => pin_nat_pow_refines hrel hinv hr) (by rw [arena.core.nat_pow_name] at h; exact h)

@[lockstep] theorem nat_beq_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_beq_name st) lst natBeqName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv
    (fun _ hr => pin_nat_beq_refines hrel hinv hr) (by rw [arena.core.nat_beq_name] at h; exact h)

@[lockstep] theorem nat_ble_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_ble_name st) lst natBleName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv
    (fun _ hr => pin_nat_ble_refines hrel hinv hr) (by rw [arena.core.nat_ble_name] at h; exact h)

@[lockstep] theorem nat_div_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_div_name st) lst natDivName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv
    (fun _ hr => pin_nat_div_refines hrel hinv hr) (by rw [arena.core.nat_div_name] at h; exact h)

@[lockstep] theorem nat_mod_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_mod_name st) lst natModName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv
    (fun _ hr => pin_nat_mod_refines hrel hinv hr) (by rw [arena.core.nat_mod_name] at h; exact h)

@[lockstep] theorem nat_gcd_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_gcd_name st) lst natGcdName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv
    (fun _ hr => pin_nat_gcd_refines hrel hinv hr) (by rw [arena.core.nat_gcd_name] at h; exact h)

@[lockstep] theorem nat_land_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_land_name st) lst natLandName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv
    (fun _ hr => pin_nat_land_refines hrel hinv hr) (by rw [arena.core.nat_land_name] at h; exact h)

@[lockstep] theorem nat_lor_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_lor_name st) lst natLorName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv
    (fun _ hr => pin_nat_lor_refines hrel hinv hr) (by rw [arena.core.nat_lor_name] at h; exact h)

@[lockstep] theorem nat_xor_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_xor_name st) lst natXorName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv
    (fun _ hr => pin_nat_xor_refines hrel hinv hr) (by rw [arena.core.nat_xor_name] at h; exact h)

@[lockstep] theorem nat_shift_left_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_shift_left_name st) lst natShiftLeftName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv
    (fun _ hr => pin_nat_shift_left_refines hrel hinv hr) (by rw [arena.core.nat_shift_left_name] at h; exact h)

@[lockstep] theorem nat_shift_right_name_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_shift_right_name st) lst natShiftRightName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv
    (fun _ hr => pin_nat_shift_right_refines hrel hinv hr) (by rw [arena.core.nat_shift_right_name] at h; exact h)

/-! ## The pin record

`nat_op_pins` returns the fifteen pins as one record; the twin reads them one
by one.  `NatOpPinsT` is that record at twin handles, `natOpPinsT` the twin's
fifteen reads collected into it (a Refine2-side name for the prefix of
`natOpDeps`, not a twin change), and `natOpDeps_eq` splits `natOpDeps` there. -/

structure NatOpPinsT where
  pr : NIdx
  ad : NIdx
  su : NIdx
  mu : NIdx
  po : NIdx
  be : NIdx
  bl : NIdx
  di : NIdx
  mo : NIdx
  gc : NIdx
  la : NIdx
  lo : NIdx
  xo : NIdx
  sl : NIdx
  sr : NIdx

def absNatOpPins (p : arena.core.NatOpPins) : NatOpPinsT :=
  ⟨absNIdx p.pr, absNIdx p.ad, absNIdx p.su, absNIdx p.mu, absNIdx p.po, absNIdx p.be, absNIdx p.bl, absNIdx p.di, absNIdx p.mo, absNIdx p.gc, absNIdx p.la, absNIdx p.lo, absNIdx p.xo, absNIdx p.sl, absNIdx p.sr⟩

def natOpPinsT : AM NatOpPinsT := do
  let pr ← natPredName
  let ad ← natAddName
  let su ← natSubName
  let mu ← natMulName
  let po ← natPowName
  let be ← natBeqName
  let bl ← natBleName
  let di ← natDivName
  let mo ← natModName
  let gc ← natGcdName
  let la ← natLandName
  let lo ← natLorName
  let xo ← natXorName
  let sl ← natShiftLeftName
  let sr ← natShiftRightName
  pure ⟨pr, ad, su, mu, po, be, bl, di, mo, gc, la, lo, xo, sl, sr⟩

/-- The selection of `natOpDeps` (`Arena/Core.lean:888-903`), on the record. -/
def natOpDepsPick (c : NIdx) (p : NatOpPinsT) : List NIdx :=
  if c == p.pr then [p.pr]
  else if c == p.ad then [p.ad]
  else if c == p.su then [p.pr, p.su]
  else if c == p.mu then [p.ad, p.mu]
  else if c == p.po then [p.ad, p.mu, p.po]
  else if c == p.be then [p.be]
  else if c == p.bl then [p.bl]
  else if c == p.di then [p.pr, p.su, p.bl, p.di]
  else if c == p.mo then [p.pr, p.su, p.bl, p.mo]
  else if c == p.gc then [p.bl, p.mo, p.gc]
  else if c == p.la then [p.ad, p.mu, p.bl, p.di, p.mo, p.la]
  else if c == p.lo then [p.ad, p.su, p.mu, p.bl, p.di, p.mo, p.lo]
  else if c == p.xo then [p.ad, p.mu, p.bl, p.di, p.mo, p.xo]
  else if c == p.sl then [p.su, p.mu, p.bl, p.sl]
  else if c == p.sr then [p.su, p.bl, p.di, p.sr]
  else []

private theorem am_pure_ite {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (pure (if c then a else b) : AM α) = if c then pure a else pure b := by
  split <;> rfl

theorem natOpDeps_eq (c : NIdx) :
    natOpDeps c = natOpPinsT >>= fun p => pure (natOpDepsPick c p) := by
  simp only [natOpDeps, natOpPinsT, natOpDepsPick, bind_assoc, pure_bind, am_pure_ite]

theorem nidx_eq2_ok (a b : arena.handle.NIdx) :
    arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = ok (absNIdx a == absNIdx b) := by
  have h : arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b
      = ok (decide (a.word = b.word)) := rfl
  rw [h, nidx_eq2_abs h]

attribute [local lockstep_inline] arena.core.nat_op_pins_rest

theorem nat_op_pins_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNatOpPins a) (arena.core.nat_op_pins st) lst natOpPinsT := by
  unfold arena.core.nat_op_pins natOpPinsT
  lockstep

theorem nat_op_deps_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (c : arena.handle.NIdx) :
    LS pers (fun a b => b = absNIdxL a) (arena.core.nat_op_deps st c) lst
      (natOpDeps (absNIdx c)) := by
  unfold arena.core.nat_op_deps
  rw [natOpDeps_eq]
  refine LS.bind (nat_op_pins_ls hrel hinv) rfl (fun e st1 => ?_)
    (fun a b st1 lst1 hab hrel1 hinv1 => ?_)
  · intro o st' h
    exact (Prod.mk.inj (Result.ok_injective h)).1.symm
  · subst hab
    intro o st' h
    obtain ⟨b0, hb0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [nidx_eq2_ok] at hb0
    cases Result.ok_injective hb0
    simp only [nidx_eq2_ok, Aeneas.Std.bind_tc_ok] at h
    simp only [natOpDepsPick, absNatOpPins]
    show LOut pers _ o st' (.ok (_, lst1))
    by_cases h0 : (absNIdx c == absNIdx a.pr) = true
    · rw [if_pos h0] at h ⊢
      repeat (obtain ⟨_, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; have := push_nidx_val hp; clear hp)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      exact ⟨_, _, rfl, by simp [absNIdxL, *], hrel1, hinv1⟩
    rw [if_neg h0] at h ⊢
    by_cases h1 : (absNIdx c == absNIdx a.ad) = true
    · rw [if_pos h1] at h ⊢
      repeat (obtain ⟨_, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; have := push_nidx_val hp; clear hp)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      exact ⟨_, _, rfl, by simp [absNIdxL, *], hrel1, hinv1⟩
    rw [if_neg h1] at h ⊢
    by_cases h2 : (absNIdx c == absNIdx a.su) = true
    · rw [if_pos h2] at h ⊢
      repeat (obtain ⟨_, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; have := push_nidx_val hp; clear hp)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      exact ⟨_, _, rfl, by simp [absNIdxL, *], hrel1, hinv1⟩
    rw [if_neg h2] at h ⊢
    by_cases h3 : (absNIdx c == absNIdx a.mu) = true
    · rw [if_pos h3] at h ⊢
      repeat (obtain ⟨_, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; have := push_nidx_val hp; clear hp)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      exact ⟨_, _, rfl, by simp [absNIdxL, *], hrel1, hinv1⟩
    rw [if_neg h3] at h ⊢
    by_cases h4 : (absNIdx c == absNIdx a.po) = true
    · rw [if_pos h4] at h ⊢
      repeat (obtain ⟨_, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; have := push_nidx_val hp; clear hp)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      exact ⟨_, _, rfl, by simp [absNIdxL, *], hrel1, hinv1⟩
    rw [if_neg h4] at h ⊢
    by_cases h5 : (absNIdx c == absNIdx a.be) = true
    · rw [if_pos h5] at h ⊢
      repeat (obtain ⟨_, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; have := push_nidx_val hp; clear hp)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      exact ⟨_, _, rfl, by simp [absNIdxL, *], hrel1, hinv1⟩
    rw [if_neg h5] at h ⊢
    by_cases h6 : (absNIdx c == absNIdx a.bl) = true
    · rw [if_pos h6] at h ⊢
      repeat (obtain ⟨_, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; have := push_nidx_val hp; clear hp)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      exact ⟨_, _, rfl, by simp [absNIdxL, *], hrel1, hinv1⟩
    rw [if_neg h6] at h ⊢
    by_cases h7 : (absNIdx c == absNIdx a.di) = true
    · rw [if_pos h7] at h ⊢
      repeat (obtain ⟨_, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; have := push_nidx_val hp; clear hp)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      exact ⟨_, _, rfl, by simp [absNIdxL, *], hrel1, hinv1⟩
    rw [if_neg h7] at h ⊢
    by_cases h8 : (absNIdx c == absNIdx a.mo) = true
    · rw [if_pos h8] at h ⊢
      repeat (obtain ⟨_, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; have := push_nidx_val hp; clear hp)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      exact ⟨_, _, rfl, by simp [absNIdxL, *], hrel1, hinv1⟩
    rw [if_neg h8] at h ⊢
    by_cases h9 : (absNIdx c == absNIdx a.gc) = true
    · rw [if_pos h9] at h ⊢
      repeat (obtain ⟨_, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; have := push_nidx_val hp; clear hp)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      exact ⟨_, _, rfl, by simp [absNIdxL, *], hrel1, hinv1⟩
    rw [if_neg h9] at h ⊢
    by_cases h10 : (absNIdx c == absNIdx a.la) = true
    · rw [if_pos h10] at h ⊢
      repeat (obtain ⟨_, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; have := push_nidx_val hp; clear hp)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      exact ⟨_, _, rfl, by simp [absNIdxL, *], hrel1, hinv1⟩
    rw [if_neg h10] at h ⊢
    by_cases h11 : (absNIdx c == absNIdx a.lo) = true
    · rw [if_pos h11] at h ⊢
      repeat (obtain ⟨_, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; have := push_nidx_val hp; clear hp)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      exact ⟨_, _, rfl, by simp [absNIdxL, *], hrel1, hinv1⟩
    rw [if_neg h11] at h ⊢
    by_cases h12 : (absNIdx c == absNIdx a.xo) = true
    · rw [if_pos h12] at h ⊢
      repeat (obtain ⟨_, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; have := push_nidx_val hp; clear hp)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      exact ⟨_, _, rfl, by simp [absNIdxL, *], hrel1, hinv1⟩
    rw [if_neg h12] at h ⊢
    by_cases h13 : (absNIdx c == absNIdx a.sl) = true
    · rw [if_pos h13] at h ⊢
      repeat (obtain ⟨_, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; have := push_nidx_val hp; clear hp)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      exact ⟨_, _, rfl, by simp [absNIdxL, *], hrel1, hinv1⟩
    rw [if_neg h13] at h ⊢
    by_cases h14 : (absNIdx c == absNIdx a.sr) = true
    · rw [if_pos h14] at h ⊢
      repeat (obtain ⟨_, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; have := push_nidx_val hp; clear hp)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
      exact ⟨_, _, rfl, by simp [absNIdxL, *], hrel1, hinv1⟩
    rw [if_neg h14] at h ⊢
    repeat (obtain ⟨_, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; have := push_nidx_val hp; clear hp)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
    exact ⟨_, _, rfl, by simp [absNIdxL, *], hrel1, hinv1⟩

end ConRon.Refine2.Frontend

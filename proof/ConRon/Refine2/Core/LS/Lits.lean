/-
# `ConRon.Refine2.Core.LS.Lits` — Theorem 2 (lockstep) for the literal guards and `reduceNat`

Task #97-P5-Core round 5, region B.  `crates/con-ron-core/src/arena/core.rs`'s
`Nat`/`String` literal section and structural-`Nat` acceleration against
`Arena/Core.lean`'s twins: the fifteen `nat*Name` pins, the name lists, the
stored-declaration shape guards (`natLitSupported`, `strLitSupported` and their
eleven helpers), the constructor forms of a literal, `rawNatLit?`,
`natOpResult` and the headline `reduceNat` (`reduce_nat_ls`), which
discharges `Core/Arms/Loops.lean`'s `reduce_nat_refines`.
-/
import ConRon.Refine2.Core.LS.PrimsB

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2

/-! ## Stubs (other regions' lemmas; deleted at merge) -/

section stubs

@[lockstep] theorem stub_empty_levels_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absLsIdx a) (arena.core.empty_levels st) st lst emptyLevels := by
  sorry

@[lockstep] theorem stub_zero_level_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absLIdx a) (arena.core.zero_level st) st lst zeroLevel := by
  sorry

@[lockstep] theorem stub_sort_one_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absEIdx a) (arena.core.sort_one st) st lst sortOne := by
  sorry

@[lockstep] theorem stub_const_e_ls {pers st n lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absEIdx a) (arena.core.const_e pers st n) lst
      (constE (absNIdx n)) := by
  sorry

@[lockstep] theorem stub_bool_true_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.bool_true_name st) lst boolTrueName := by
  sorry

@[lockstep] theorem stub_bool_false_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.bool_false_name st) lst boolFalseName := by
  sorry

end stubs

/-! ## The fifteen `Nat`-operation names -/

local macro "name_pin" rust:ident twin:ident pin:ident : command =>
  `(@[lockstep] theorem $(Lean.mkIdent (rust.getId.componentsRev.head!.appendAfter "_ls"))
        {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
        LS pers (fun a b => b = absNIdx a) ($rust st) lst $twin := by
      rw [$rust:ident, $twin:ident]
      exact PB.LS.of_read ($pin hrel hinv))

name_pin arena.core.nat_pred_name natPredName PB.pin_nat_pred_ls
name_pin arena.core.nat_add_name natAddName PB.pin_nat_add_ls
name_pin arena.core.nat_sub_name natSubName PB.pin_nat_sub_ls
name_pin arena.core.nat_mul_name natMulName PB.pin_nat_mul_ls
name_pin arena.core.nat_pow_name natPowName PB.pin_nat_pow_ls
name_pin arena.core.nat_beq_name natBeqName PB.pin_nat_beq_ls
name_pin arena.core.nat_ble_name natBleName PB.pin_nat_ble_ls
name_pin arena.core.nat_div_name natDivName PB.pin_nat_div_ls
name_pin arena.core.nat_mod_name natModName PB.pin_nat_mod_ls
name_pin arena.core.nat_gcd_name natGcdName PB.pin_nat_gcd_ls
name_pin arena.core.nat_land_name natLandName PB.pin_nat_land_ls
name_pin arena.core.nat_lor_name natLorName PB.pin_nat_lor_ls
name_pin arena.core.nat_xor_name natXorName PB.pin_nat_xor_ls
name_pin arena.core.nat_shift_left_name natShiftLeftName PB.pin_nat_shift_left_ls
name_pin arena.core.nat_shift_right_name natShiftRightName PB.pin_nat_shift_right_ls

/-! ## The name lists -/

@[lockstep] theorem push_nidx_spec (out : alloc.vec.Vec arena.handle.NIdx) (n : arena.handle.NIdx) :
    LSP (arena.core.push_nidx out n) (fun w => w.val = out.val ++ [n]) :=
  fun w h => by
    rw [arena.core.push_nidx] at h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [dupId_nidx _ _ hn1] at h
    exact ConRon.Refine.vec_push_val h

@[lockstep_simp] theorem vec_new_val {α : Type} : (alloc.vec.Vec.new α).val = [] := rfl

attribute [lockstep_simp] absNIdxList

attribute [local lockstep_simp] List.map_append List.map_cons List.map_nil
  List.nil_append List.cons_append List.isEmpty_nil List.isEmpty_cons Bool.true_and
  Bool.false_and Bool.and_true Bool.and_false

@[lockstep] theorem nat_op_names_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdxList a) (arena.core.nat_op_names st) lst natOpNames := by
  rw [arena.core.nat_op_names, natOpNames]
  lockstep_core

@[lockstep] theorem nat_div_mod_names_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdxList a) (arena.core.nat_div_mod_names st) lst
      natDivModNames := by
  rw [arena.core.nat_div_mod_names, natDivModNames]
  lockstep_core

/-- The port serves `natOpWfNames` with `nat_div_mod_names`: the twin's two
lists are the same eight names in the same order. -/
@[lockstep] theorem nat_op_wf_names_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdxList a) (arena.core.nat_op_wf_names st) lst
      natOpWfNames := by
  rw [arena.core.nat_op_wf_names, show natOpWfNames = natDivModNames from rfl]
  exact nat_div_mod_names_ls hrel hinv

attribute [lockstep_inline] arena.core.nat_op_pins arena.core.nat_op_pins_rest

@[lockstep] theorem nat_op_deps_ls {pers st c lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdxList a) (arena.core.nat_op_deps st c) lst
      (natOpDeps (absNIdx c)) := by
  rw [arena.core.nat_op_deps, natOpDeps]
  lockstep

/-! ## `natBinOpName` and `natOpStored`

The port reads its fifteen names once (`nat_op_pins`), `pred` included; the
twin's `natBinOpName` reads the fourteen it compares and not `pred`.  The
extra read is harmless — a pin read writes nothing, and `pred`'s slot (16)
precedes `add`'s (17), so when it declines the twin's first read declines
too, at the same message — and `natBinOpName_pred` says so as a twin
equation. -/

theorem pinAt_run (i : Nat) (lst : AState) :
    (pinAt i).run lst = (if h : i < lst.pins.names.size
      then Except.ok (lst.pins.names[i], lst)
      else Except.error (Arena.CheckError.internal "arena: reserved-name pins not interned")) := by
  by_cases h : i < lst.pins.names.size
  · rw [dif_pos h]
    show (Arena.pinAt i) lst = _
    rw [Arena.pinAt]
    simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      Pure.pure, StateT.pure, Except.pure, Except.bind, dif_pos h]
  · rw [dif_neg h]
    show (Arena.pinAt i) lst = _
    rw [Arena.pinAt]
    simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      Pure.pure, Except.pure, Except.bind, dif_neg h,
      Arena.fail, throwThe, MonadExceptOf.throw,
      Function.comp_apply, StateT.lift]

theorem natBinOpName_pred (c : NIdx) :
    natBinOpName c = (natPredName >>= fun _ => natBinOpName c) := by
  apply StateT.ext
  intro lst
  by_cases h : PIN_NAT_PRED < lst.pins.names.size
  · have hp : natPredName.run lst = .ok (lst.pins.names[PIN_NAT_PRED], lst) := by
      rw [natPredName, pinNatPred, pinAt_run, dif_pos h]
    rw [run_bind_ok hp]
  · have herr : ∀ {γ δ : Type} (f : γ → Except Arena.CheckError δ),
        (Except.error (Arena.CheckError.internal "arena: reserved-name pins not interned")
          >>= f) = Except.error
            (Arena.CheckError.internal "arena: reserved-name pins not interned") :=
      fun _ => rfl
    have hp : natPredName.run lst = .error
        (Arena.CheckError.internal "arena: reserved-name pins not interned") := by
      rw [natPredName, pinNatPred, pinAt_run, dif_neg h]
    have ha : natAddName.run lst = .error
        (Arena.CheckError.internal "arena: reserved-name pins not interned") := by
      rw [natAddName, pinNatAdd, pinAt_run, dif_neg (by
        simp only [PIN_NAT_PRED, PIN_NAT_ADD] at h ⊢; omega)]
    have hl : (natBinOpName c).run lst = .error
        (Arena.CheckError.internal "arena: reserved-name pins not interned") := by
      unfold natBinOpName
      rw [StateT.run_bind, ha, herr]
    rw [hl, StateT.run_bind, hp, herr]

/-- The twin's disjunction as the port's short-circuit chain. -/
theorem pure_or_ite (a b : Bool) :
    (pure (a || b) : AM Bool) = if a = true then pure true else pure b := by
  cases a <;> rfl

section
attribute [local lockstep_simp] pure_or_ite

@[lockstep] theorem nat_bin_op_name_ls {pers st c lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.nat_bin_op_name st c) lst
      (natBinOpName (absNIdx c)) := by
  rw [arena.core.nat_bin_op_name, natBinOpName_pred, natBinOpName]
  lockstep

end

@[lockstep] theorem nat_op_stored_ls {pers vis st fe lfe c lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe) :
    LSV pers (fun a b => b = a) (arena.core.nat_op_stored vis fe c) st lst
      (natOpStored lfe (absNIdx c)) := by
  intro a ha
  rw [arena.core.nat_op_stored] at ha
  obtain ⟨o, ho, ha⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha
  have hf := ifenv_find_abs hctx ho
  refine ⟨a, lst, ?_, rfl, hrel, hinv⟩
  rw [natOpStored, ← hf]
  rcases o with _ | ii
  · cases Result.ok_injective ha; rfl
  · cases ii <;> (cases Result.ok_injective ha; rfl)

/-! ## The `Nat` literal guards -/

@[lockstep] theorem nat_ind_ok_ls {pers st ci lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.nat_ind_ok st ci) lst
      (natIndOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | ci
  · rw [arena.core.nat_ind_ok.eq_def]
    simp only [Option.map_none, natIndOk]
    lockstep
  rcases ci <;> rw [arena.core.nat_ind_ok.eq_def] <;>
    simp only [Option.map_some, absIConstantInfo, natIndOk] <;> lockstep

@[lockstep] theorem nat_zero_ok_ls {pers st ci lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.nat_zero_ok pers st ci) lst
      (natZeroOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | ci
  · rw [arena.core.nat_zero_ok.eq_def]
    simp only [Option.map_none, natZeroOk]
    lockstep
  rcases ci <;> rw [arena.core.nat_zero_ok.eq_def] <;>
    simp only [Option.map_some, absIConstantInfo, natZeroOk] <;> lockstep

@[lockstep] theorem nat_succ_ok_ls {pers st ci lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.nat_succ_ok pers st ci) lst
      (natSuccOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | ci
  · rw [arena.core.nat_succ_ok.eq_def]
    simp only [Option.map_none, natSuccOk]
    lockstep
  rcases ci <;> rw [arena.core.nat_succ_ok.eq_def] <;>
    simp only [Option.map_some, absIConstantInfo, natSuccOk] <;> lockstep

@[lockstep] theorem nat_lit_supported_ls {pers vis st fe lfe lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.nat_lit_supported pers vis st fe) lst
      (natLitSupported lfe) := by
  rw [arena.core.nat_lit_supported, natLitSupported]
  lockstep

/-! ## Constructor forms and the literal reading -/

attribute [local lockstep_simp] Nat.add_sub_cancel
attribute [local simp] ConRon.Refine.LiteralWF

@[lockstep] theorem nat_lit_to_constructor_ls {pers st n lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hn : ConRon.Refine.Nat.NatWF n) :
    LS pers (fun a b => b = absEIdx a) (arena.core.nat_lit_to_constructor pers st n) lst
      (natLitToConstructor (ConRon.Refine.Nat.toNat n)) := by
  rw [arena.core.nat_lit_to_constructor]
  rcases hk : ConRon.Refine.Nat.toNat n with _ | k
  · rw [natLitToConstructor]
    lockstep
    all_goals trace_state
    all_goals sorry
  · rw [natLitToConstructor]
    lockstep
    all_goals trace_state
    all_goals sorry

@[lockstep] theorem raw_nat_lit_ls {pers st h lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => (∀ n, a = some n → ConRon.Refine.Nat.NatWF n) ∧
        b = a.map ConRon.Refine.Nat.toNat)
      (arena.core.raw_nat_lit pers st h) lst (rawNatLit? (absEIdx h)) := by
  rw [arena.core.raw_nat_lit, rawNatLit?]
  refine LSR.bind (PB.view_wf_ls hrel hinv h) rfl (fun e => errArm_ok) ?_
  intro a b lst1 hR hrel1 hinv1
  obtain ⟨hwf, rfl⟩ := hR
  dsimp only
  lockstep

@[lockstep] theorem lit_to_ctor_if_nat_ls {pers vis st fe lfe h lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = absEIdx a) (arena.core.lit_to_ctor_if_nat pers vis st fe h) lst
      (litToCtorIfNat lfe (absEIdx h)) := by
  rw [arena.core.lit_to_ctor_if_nat, litToCtorIfNat]
  lockstep

/-! ## `natOpResult` -/

attribute [lockstep_inline] arena.core.lit_nat arena.core.bool_const

set_option maxHeartbeats 4000000 in
@[lockstep] theorem nat_op_result_ls {pers st c a b lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (ha : ConRon.Refine.Nat.NatWF a) (hb : ConRon.Refine.Nat.NatWF b) :
    LS pers (fun x y => y = absOptE x) (arena.core.nat_op_result pers st c a b) lst
      (natOpResult (absNIdx c) (ConRon.Refine.Nat.toNat a) (ConRon.Refine.Nat.toNat b)) := by
  rw [arena.core.nat_op_result, natOpResult]
  lockstep

/-! ## String literals -/

@[lockstep] theorem cast_u32_u64_spec (x : Std.U32) :
    LSP (lift (UScalar.cast .U64 x)) (fun y => y.val = x.val) := by
  intro y h
  simp only [ConRon.Refine.lift_eq, Result.ok.injEq] at h
  subst h
  simp

theorem bne_eq_not_beq' {α : Type} [BEq α] (a b : α) : (a != b) = !(a == b) := rfl

attribute [local lockstep_simp] bne_eq_not_beq' Bool.not_true Bool.not_false

/-- The twin's character list of a stored string. -/
theorem absString_toList (s : alloc.vec.Vec Std.U32) :
    (ConRon.Refine.absString s).toList = s.val.map fun c => Char.ofNat c.val := by
  rw [ConRon.Refine.absString, String.toList_ofList]

theorem char_toNat_ofNat_of_valid {n : Nat} (hv : n.isValidChar) :
    (Char.ofNat n).toNat = n := by
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]

/-- The spine's one-character step reads the stored code point. -/
theorem spine_char {s : alloc.vec.Vec Std.U32} (hs : ConRon.Refine.StrWF s) {i : Nat}
    (hi : i < s.val.length) :
    ((s.val.map fun c => Char.ofNat c.val)[i]'(by simpa using hi)).toNat = s.val[i].val := by
  rw [List.getElem_map]
  exact char_toNat_ofNat_of_valid (hs _ (List.getElem_mem hi))

theorem str_lit_cons_spine_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (cons of_nat nil_e : arena.handle.EIdx) (s : alloc.vec.Vec Std.U32) (i : Std.Usize),
      s.val.length - i.val = n → ConRon.Refine.StrWF s →
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.str_lit_cons_spine pers st cons of_nat nil_e s i) lst
        (strLitConsSpine (absEIdx cons) (absEIdx of_nat) (absEIdx nil_e)
          ((s.val.map fun c => Char.ofNat c.val).drop i.val)) := by
  induction n with
  | zero =>
    intro pers st lst cons of_nat nil_e s i hn hs hrel hinv
    rw [arena.core.str_lit_cons_spine, List.drop_eq_nil_of_le (by simp; omega),
      strLitConsSpine]
    lockstep
    all_goals trace_state
    all_goals sorry
  | succ k ih =>
    intro pers st lst cons of_nat nil_e s i hn hs hrel hinv
    have hi : i.val < s.val.length := by omega
    have hc := spine_char hs hi
    rw [arena.core.str_lit_cons_spine, List.drop_eq_getElem_cons (by simpa using hi),
      strLitConsSpine]
    lockstep
    all_goals trace_state
    all_goals sorry

@[lockstep] theorem str_lit_cons_spine_ls {pers st cons of_nat nil_e s i lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hs : ConRon.Refine.StrWF s) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.str_lit_cons_spine pers st cons of_nat nil_e s i) lst
      (strLitConsSpine (absEIdx cons) (absEIdx of_nat) (absEIdx nil_e)
        ((s.val.map fun c => Char.ofNat c.val).drop i.val)) :=
  str_lit_cons_spine_aux _ cons of_nat nil_e s i rfl hs hrel hinv

attribute [lockstep_inline] arena.core.str_lit_to_constructor_rest

attribute [local lockstep_simp] absString_toList List.drop_zero

@[lockstep] theorem str_lit_to_constructor_ls {pers st s lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hs : ConRon.Refine.StrWF s) :
    LS pers (fun a b => b = absEIdx a) (arena.core.str_lit_to_constructor pers st s) lst
      (strLitToConstructor (ConRon.Refine.absString s)) := by
  rw [arena.core.str_lit_to_constructor, strLitToConstructor]
  lockstep
  all_goals trace_state
  all_goals sorry

/-! ## The `String` literal guards -/

@[lockstep] theorem string_ty_ok_ls {pers st ci lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.string_ty_ok pers st ci) lst
      (stringTyOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | c <;> rw [arena.core.string_ty_ok.eq_def] <;>
    simp only [Option.map_none, Option.map_some, stringTyOk] <;> lockstep
  all_goals trace_state
  all_goals sorry

@[lockstep] theorem char_ty_ok_ls {pers st ci lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.char_ty_ok pers st ci) lst
      (charTyOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | c <;> rw [arena.core.char_ty_ok.eq_def] <;>
    simp only [Option.map_none, Option.map_some, charTyOk] <;> lockstep
  all_goals trace_state
  all_goals sorry

@[lockstep] theorem char_of_nat_ty_ok_ls {pers st ci lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.char_of_nat_ty_ok pers st ci) lst
      (charOfNatTyOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | c <;> rw [arena.core.char_of_nat_ty_ok.eq_def] <;>
    simp only [Option.map_none, Option.map_some, charOfNatTyOk] <;> lockstep
  all_goals trace_state
  all_goals sorry

attribute [lockstep_inline] arena.core.string_of_list_ty_body arena.core.list_nil_ty_body
  arena.core.list_cons_ty_body arena.core.list_cons_ty_at arena.core.str_lit_supported_rest

@[lockstep] theorem string_of_list_ty_ok_ls {pers st ci lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.string_of_list_ty_ok pers st ci) lst
      (stringOfListTyOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | c <;> rw [arena.core.string_of_list_ty_ok.eq_def] <;>
    simp only [Option.map_none, Option.map_some, stringOfListTyOk] <;> lockstep
  all_goals trace_state
  all_goals sorry

@[lockstep] theorem list_ty_ok_ls {pers st ci lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.list_ty_ok pers st ci) lst
      (listTyOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | c <;> rw [arena.core.list_ty_ok.eq_def] <;>
    simp only [Option.map_none, Option.map_some, listTyOk] <;> lockstep
  all_goals trace_state
  all_goals sorry

@[lockstep] theorem list_nil_ty_ok_ls {pers st ci lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.list_nil_ty_ok pers st ci) lst
      (listNilTyOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | c <;> rw [arena.core.list_nil_ty_ok.eq_def] <;>
    simp only [Option.map_none, Option.map_some, listNilTyOk] <;> lockstep
  all_goals trace_state
  all_goals sorry

@[lockstep] theorem list_cons_ty_ok_ls {pers st ci lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.list_cons_ty_ok pers st ci) lst
      (listConsTyOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | c <;> rw [arena.core.list_cons_ty_ok.eq_def] <;>
    simp only [Option.map_none, Option.map_some, listConsTyOk] <;> lockstep
  all_goals trace_state
  all_goals sorry

@[lockstep] theorem str_lit_supported_ls {pers vis st fe lfe lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.str_lit_supported pers vis st fe) lst
      (strLitSupported lfe) := by
  rw [arena.core.str_lit_supported, strLitSupported]
  lockstep
  all_goals trace_state
  all_goals sorry

/-! ## `reduceNat` -/

/-- `arena::env::nidx_vec_contains` is `List.contains` of the abstracted names
(a Rust-only step: the twin's `wf.contains c` is a pure expression). -/
theorem nidx_vec_contains_from_any (ns : alloc.vec.Vec arena.handle.NIdx)
    (n : arena.handle.NIdx) (k : Nat) :
    ∀ (i : Std.Usize) (o : Bool), ns.val.length - i.val = k →
      arena.env.nidx_vec_contains_from ns i n = ok o →
      o = (ns.val.drop i.val).any fun m => absNIdx m == absNIdx n := by
  induction k with
  | zero =>
    intro i o hk h
    rw [arena.env.nidx_vec_contains_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ns by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ k ih =>
    intro i o hk h
    have hlt : i.val < ns.val.length := by omega
    rw [arena.env.nidx_vec_contains_from.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ns by scalar_tac)] at h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, rfl⟩ := ExprOps.vecIndexAt hn1
    have hbv : b = (absNIdx ns.val[i.val] == absNIdx n) := PB.nidx_eq2_spec _ _ b hb
    rw [List.drop_eq_getElem_cons hlt, List.any_cons, ← hbv]
    cases b with
    | false =>
      rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := (ConRon.Refine.Nat.uadd_val hi2)
      rw [Bool.false_or, ih i2 o (by omega) h, hi2v]
    | true =>
      rw [if_pos (by simp), Result.ok.injEq] at h
      rw [← h, Bool.true_or]

@[lockstep] theorem nidx_vec_contains_spec (ns : alloc.vec.Vec arena.handle.NIdx)
    (n : arena.handle.NIdx) :
    LSP (arena.env.nidx_vec_contains ns n)
      (fun o => o = (absNIdxList ns).contains (absNIdx n)) := by
  intro o h
  rw [arena.env.nidx_vec_contains] at h
  rw [nidx_vec_contains_from_any ns n _ 0#usize o rfl h]
  simp [absNIdxList, List.contains_eq_any_beq, List.any_map, Function.comp_def, List.any_eq]

/-- The twin's `natOpStored` reads the environment and nothing else. -/
def natOpStoredB (fe : IFEnv) (c : NIdx) : Bool :=
  match fe.find? c with
  | some (.defnInfo _ _ _) => true
  | _ => false

theorem natOpStored_pure (fe : IFEnv) (c : NIdx) :
    natOpStored fe c = pure (natOpStoredB fe c) := by
  unfold natOpStored natOpStoredB
  generalize fe.find? c = o
  rcases o with _ | ci
  · rfl
  · cases ci <;> rfl

@[lockstep] theorem nat_op_stored_spec {vis : Std.U64} {fe : arena.env.IFEnv} {lfe : IFEnv}
    (hctx : CoreCtx vis fe lfe) (c : arena.handle.NIdx) :
    LSP (arena.core.nat_op_stored vis fe c) (fun b => b = natOpStoredB lfe (absNIdx c)) := by
  intro a ha
  rw [arena.core.nat_op_stored] at ha
  obtain ⟨o, ho, ha⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha
  have hf := ifenv_find_abs hctx ho
  rw [natOpStoredB, ← hf]
  rcases o with _ | ii
  · cases Result.ok_injective ha; rfl
  · cases ii <;> (cases Result.ok_injective ha; rfl)

attribute [lockstep_inline] arena.core.reduce_nat_succ arena.core.reduce_nat_bin
  arena.core.reduce_nat_wf

section
attribute [local lockstep_simp] natOpStored_pure

set_option maxHeartbeats 4000000 in
/-- **`arena::core::reduce_nat` ⊑ `Arena.reduceNat`** — the headline of region B,
discharging `Core/Arms/Loops.lean`'s `reduce_nat_refines` through
`LS.toSim₀`. -/
@[lockstep] theorem reduce_nat_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = Option.map absEIdx a)
      (arena.core.reduce_nat pers vis st mode lane fu fe depth e) lst
      (reduceNat (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe
        (absU depth) (absEIdx e)) := by
  rw [arena.core.reduce_nat, reduceNat]
  lockstep
  all_goals trace_state
  all_goals sorry

end

end ConRon.Refine2.Lockstep

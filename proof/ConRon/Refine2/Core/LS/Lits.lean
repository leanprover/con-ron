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
import ConRon.Refine2.Core.LS.Leaves

-- the Core regions' `lockstep_simp` rules (scoped, task #97-P5-Core round 5)
open scoped ConRon.Refine2.Lockstep.CoreLSReg ConRon.Refine2.Lockstep.PA1.CoreLSReg ConRon.Refine2.Lockstep.PB.CoreLSReg

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

-- `PrimsB`/`PrimsE` unfold the record abstraction only locally now (the
-- Checker lane reads it folded); the Core region files read it unfolded
attribute [local lockstep_simp] ConRon.Refine2.absIConstantVal

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2


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

@[local lockstep_simp] theorem vec_new_val_B {α : Type} : (alloc.vec.Vec.new α).val = [] := rfl

attribute [local lockstep_simp] absNIdxList

attribute [local lockstep_simp] List.map_append List.map_cons List.map_nil
  List.nil_append List.cons_append List.isEmpty_nil List.isEmpty_cons Bool.true_and
  Bool.false_and Bool.and_true Bool.and_false

/- In the region's namespace: the Checker lane states the same two reads
against `absNIdxL` in `Lockstep` (`Checker/Base.lean`). -/
namespace PB

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

end PB

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
  · rw [natLitToConstructor]
    lockstep

@[lockstep] theorem raw_nat_lit_ls {pers st h lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => (∀ n, a = some n → ConRon.Refine.Nat.NatWF n) ∧
        b = a.map ConRon.Refine.Nat.toNat)
      (arena.core.raw_nat_lit pers st h) lst (rawNatLit? (absEIdx h)) := by
  rw [arena.core.raw_nat_lit, rawNatLit?]
  refine LSR.bind (PB.view_wf_ls hrel hinv h) rfl (fun e => errArm_ok) ?_
  intro a b lst1 hR hrel1 hinv1
  obtain ⟨hwf, rfl⟩ := hR
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

/-- Local: `lockstep`'s `apply` unifies its `UScalar.cast .U64 x` with a
`usize` cast by unfolding `cast` (an ill-typed assignment the kernel rejects,
`Inductives/NativeParts`' `native_shape_at`), so it is filed for this file
only. -/
@[local lockstep] theorem cast_u32_u64_spec (x : Std.U32) :
    LSP (lift (UScalar.cast .U64 x)) (fun y => y.val = x.val) := by
  intro y h
  simp only [ConRon.Refine.lift_eq, Result.ok.injEq] at h
  subst h
  simp

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
  | succ k ih =>
    intro pers st lst cons of_nat nil_e s i hn hs hrel hinv
    have hi : i.val < s.val.length := by omega
    have hc := spine_char hs hi
    rw [arena.core.str_lit_cons_spine, List.drop_eq_getElem_cons (by simpa using hi),
      strLitConsSpine]
    lockstep

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

/-! ## The `String` literal guards -/

private theorem usize_zero_val_lits : (0#usize : Std.Usize).val = 0 := rfl

set_option hygiene false in
/-- Glue for `listTyOk`/`listNilTyOk`/`listConsTyOk`: the twin matches
`cv.levelParams` against `[p]`, the port tests the length and reads slot 0.
Case on the twin's list; the length decides the port's test, and slot 0 is
`p`. -/
local macro "level_params_single" : tactic => `(tactic| (
  rcases hm : List.map absNIdx a.level_params.val with _ | ⟨p, _ | ⟨q, m⟩⟩ <;>
    have hlen := congrArg List.length hm <;>
    simp (config := {failIfUnchanged := false}) only [List.length_map, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.reduceAdd] at hlen <;>
    simp (config := {failIfUnchanged := false}) only [PB.vec_len_bne_one, hlen, decide_true, decide_false, Bool.not_true, Bool.not_false,
      Nat.reduceEqDiff, Bool.false_eq_true, not_true_eq_false, not_false_eq_true] at hc <;>
    first
    | (obtain ⟨x, l1, hlx, hx, -⟩ := List.map_eq_cons_iff.mp hm
       subst hx
       try simp only [bind_pure]
       lockstep
       -- the port's slot-0 read, once the zip reaches it
       all_goals
         simp (config := {failIfUnchanged := false}) only
           [List.getElem_of_eq hlx, usize_zero_val_lits, List.getElem_cons_zero]
         try simp only [bind_pure]
         lockstep)
    | lockstep))

open Lean Meta Elab Tactic in
/-- Is the twin's head the `match` on a constant's level-parameter list, with
the port's length test `hc` in hand?  Then `level_params_single` runs before
`lockstep`'s own move on a stuck twin `match` (which cases the list's handles
field by field, task #97-T2-TACTIC round 2). -/
elab "lp_ready" : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  unless ty.isAppOfArity ``Lockstep.LS 7 do throwError "lp_ready: not LS"
  let some mapp ← matchMatcherApp? (ty.getArg! 6) | throwError "lp_ready: no match"
  let some d := mapp.discrs[0]? | throwError "lp_ready: no discriminant"
  unless (d.find? (·.isAppOf ``arena.env.IConstantVal.level_params)).isSome do
    throwError "lp_ready: not the level parameters"
  unless (← getLCtx).any (fun h => h.userName == `hc) do throwError "lp_ready: no test"

/-- `lockstep`, with the level-parameter glue taken at the twin's `match`. -/
macro "lockstep_lp" : tactic =>
  `(tactic| repeat' (first | (lp_ready; level_params_single) | lockstep_step))

@[lockstep] theorem string_ty_ok_ls {pers st ci lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.string_ty_ok pers st ci) lst
      (stringTyOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | c <;> rw [arena.core.string_ty_ok.eq_def] <;>
    simp only [Option.map_none, Option.map_some, stringTyOk] <;> lockstep

@[lockstep] theorem char_ty_ok_ls {pers st ci lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.char_ty_ok pers st ci) lst
      (charTyOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | c <;> rw [arena.core.char_ty_ok.eq_def] <;>
    simp only [Option.map_none, Option.map_some, charTyOk] <;> lockstep

@[lockstep] theorem char_of_nat_ty_ok_ls {pers st ci lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.char_of_nat_ty_ok pers st ci) lst
      (charOfNatTyOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | c <;> rw [arena.core.char_of_nat_ty_ok.eq_def] <;>
    simp only [Option.map_none, Option.map_some, charOfNatTyOk] <;> lockstep

attribute [lockstep_inline] arena.core.string_of_list_ty_body arena.core.list_nil_ty_body
  arena.core.list_cons_ty_body arena.core.list_cons_ty_at arena.core.str_lit_supported_rest

@[lockstep] theorem string_of_list_ty_ok_ls {pers st ci lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.string_of_list_ty_ok pers st ci) lst
      (stringOfListTyOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | c <;> rw [arena.core.string_of_list_ty_ok.eq_def] <;>
    simp only [Option.map_none, Option.map_some, stringOfListTyOk] <;> lockstep

@[lockstep] theorem list_ty_ok_ls {pers st ci lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.list_ty_ok pers st ci) lst
      (listTyOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | c <;> rw [arena.core.list_ty_ok.eq_def] <;>
    simp only [Option.map_none, Option.map_some, listTyOk] <;> lockstep_lp

@[lockstep] theorem list_nil_ty_ok_ls {pers st ci lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.list_nil_ty_ok pers st ci) lst
      (listNilTyOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | c <;> rw [arena.core.list_nil_ty_ok.eq_def] <;>
    simp only [Option.map_none, Option.map_some, listNilTyOk] <;> lockstep_lp
  -- glue: the port's `Some(0)` pattern on the `u64` de Bruijn index against the
  -- twin's `.bvar 0` pattern (a `match` on a `Nat`: the tactic now cases it,
  -- and the `n + 1` branch against the port's `0` closes by the index's value)
  all_goals first
    | (exfalso; simp_all; done)
    | (exfalso; rename_i heq _ hd; rw [heq] at hd; simp [Std.UScalar.val] at hd)
    | (exfalso; rename_i hne hd; apply hne; apply Std.UScalar.eq_of_val_eq
       rw [hd]; simp [Std.UScalar.val])
    | (split <;> first
    | (lockstep; done)
    | (exfalso; simp_all; done)
    | (exfalso; rename_i hne _ heq; apply hne; apply Std.UScalar.eq_of_val_eq
       simp only [ENodeView.bvar.injEq] at heq; rw [heq]; rfl))

@[lockstep] theorem list_cons_ty_ok_ls {pers st ci lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = a) (arena.core.list_cons_ty_ok pers st ci) lst
      (listConsTyOk (ci.map absIConstantInfo)) := by
  rcases ci with _ | c <;> rw [arena.core.list_cons_ty_ok.eq_def] <;>
    simp only [Option.map_none, Option.map_some, listConsTyOk] <;> lockstep_lp

@[lockstep] theorem str_lit_supported_ls {pers vis st fe lfe lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hctx : CoreCtx vis fe lfe) :
    LS pers (fun a b => b = a) (arena.core.str_lit_supported pers vis st fe) lst
      (strLitSupported lfe) := by
  rw [arena.core.str_lit_supported, strLitSupported]
  lockstep

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

end

/-! ## Axiom census -/

/-- info: 'ConRon.Refine2.Lockstep.reduce_nat_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms reduce_nat_ls

/-- info: 'ConRon.Refine2.Lockstep.str_lit_supported_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms str_lit_supported_ls

/-- info: 'ConRon.Refine2.Lockstep.str_lit_to_constructor_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms str_lit_to_constructor_ls

/-- info: 'ConRon.Refine2.Lockstep.lit_to_ctor_if_nat_ls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lit_to_ctor_if_nat_ls

end ConRon.Refine2.Lockstep

/-! The region's `lockstep_simp` rules, registered `scoped` (task #97-P5-Core
round 5): active under `open scoped ConRon.Refine2.Lockstep.CoreLSReg` only, so that they
stay out of the other tiers' `lockstep` runs (the Checker lane imports the
knot since task #97-T2-LOCKSTEP lane Checker DeclCheck). -/
namespace ConRon.Refine2.Lockstep.CoreLSReg
open Aeneas Aeneas.Std Result
open ConRon.Generated
open ConRon.Arena ConRon.Refine2
attribute [scoped lockstep_simp] vec_new_val_B absNIdxList
end ConRon.Refine2.Lockstep.CoreLSReg

/-
Task #49's last file: **every imported hypothesis of the `CoreK*` family,
discharged**.

The eleven files of `CORE_PLAN.md` step 4 were written in parallel, so a lemma
that compares against a pinned name, or that calls another file's function,
takes what it needs as an explicit hypothesis of exactly the shape the owning
file proves (`PinnedName`, `PinnedNames`, `CoreK.NatOpPinned`,
`CoreK.PinnedBasisNames`, `CoreK.VecFacts`, `CoreK.EnvFacts`,
`CoreK.LpEmptySpec`, …).  That keeps each file self-contained and its statements
exact; it leaves the *hypotheses* to be closed once, here, from the lemmas that
prove them.

Nothing in this file is a new claim: every declaration is an instance of a
bundle whose fields are `<fn>_refines` lemmas of the sibling files, so after it
no theorem of step 4 depends on anything unproved.  Step 6's knot applies the
guards through these.
-/
import ConRon.Refine.CoreKNames
import ConRon.Refine.CoreKVec
import ConRon.Refine.CoreKLits
import ConRon.Refine.CoreKSupport
import ConRon.Refine.CoreKGuards
import ConRon.Refine.CoreKNatOps
import ConRon.Refine.CoreKShapes
import ConRon.Refine.CoreKInfer

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.CoreK

/-! ## The pinned names of `kernel/basis_names.rs` -/

theorem pinned_eq_name : PinnedName basis_names.eq_name ConLeche.eqName :=
  fun _ h => BasisNames.eq_name_refines h
theorem pinned_eq_refl_name : PinnedName basis_names.eq_refl_name ConLeche.eqReflName :=
  fun _ h => BasisNames.eq_refl_name_refines h
theorem pinned_punit_name : PinnedName basis_names.punit_name ConLeche.punitName :=
  fun _ h => BasisNames.punit_name_refines h
theorem pinned_punit_rec_name :
    PinnedName basis_names.punit_rec_name ConLeche.punitRecName :=
  fun _ h => BasisNames.punit_rec_name_refines h
theorem pinned_nat_name : PinnedName basis_names.nat_name ConLeche.natName :=
  fun _ h => BasisNames.nat_name_refines h
theorem pinned_nat_zero_name : PinnedName basis_names.nat_zero_name ConLeche.natZeroName :=
  fun _ h => BasisNames.nat_zero_name_refines h
theorem pinned_nat_succ_name : PinnedName basis_names.nat_succ_name ConLeche.natSuccName :=
  fun _ h => BasisNames.nat_succ_name_refines h
theorem pinned_punit_unit_name :
    PinnedName basis_names.punit_unit_name ConLeche.punitUnitName :=
  fun _ h => BasisNames.punit_unit_name_refines h
theorem pinned_empty_name : PinnedName basis_names.empty_name ConLeche.emptyName :=
  fun _ h => BasisNames.empty_name_refines h
theorem pinned_false_name : PinnedName basis_names.false_name ConLeche.falseName :=
  fun _ h => BasisNames.false_name_refines h
theorem pinned_quot_name : PinnedName basis_names.quot_name ConLeche.quotName :=
  fun _ h => BasisNames.quot_name_refines h
theorem pinned_quot_mk_name : PinnedName basis_names.quot_mk_name ConLeche.quotMkName :=
  fun _ h => BasisNames.quot_mk_name_refines h
theorem pinned_quot_lift_name : PinnedName basis_names.quot_lift_name ConLeche.quotLiftName :=
  fun _ h => BasisNames.quot_lift_name_refines h
theorem pinned_quot_ind_name : PinnedName basis_names.quot_ind_name ConLeche.quotIndName :=
  fun _ h => BasisNames.quot_ind_name_refines h
theorem pinned_quot_sound_name :
    PinnedName basis_names.quot_sound_name ConLeche.quotSoundName :=
  fun _ h => BasisNames.quot_sound_name_refines h
theorem pinned_string_name : PinnedName basis_names.string_name ConLeche.stringName :=
  fun _ h => BasisNames.string_name_refines h
theorem pinned_string_of_list_name :
    PinnedName basis_names.string_of_list_name ConLeche.stringOfListName :=
  fun _ h => BasisNames.string_of_list_name_refines h
theorem pinned_list_name : PinnedName basis_names.list_name ConLeche.listName :=
  fun _ h => BasisNames.list_name_refines h
theorem pinned_list_nil_name : PinnedName basis_names.list_nil_name ConLeche.listNilName :=
  fun _ h => BasisNames.list_nil_name_refines h
theorem pinned_list_cons_name :
    PinnedName basis_names.list_cons_name ConLeche.listConsName :=
  fun _ h => BasisNames.list_cons_name_refines h
theorem pinned_char_name : PinnedName basis_names.char_name ConLeche.charName :=
  fun _ h => BasisNames.char_name_refines h
theorem pinned_and_name : PinnedName basis_names.and_name ConLeche.andName :=
  fun _ h => BasisNames.and_name_refines h
theorem pinned_and_intro_name :
    PinnedName basis_names.and_intro_name ConLeche.andIntroName :=
  fun _ h => BasisNames.and_intro_name_refines h
theorem pinned_char_of_nat_name :
    PinnedName basis_names.char_of_nat_name ConLeche.charOfNatName :=
  fun _ h => BasisNames.char_of_nat_name_refines h
theorem pinned_reserved_basis_names :
    PinnedNames basis_names.reserved_basis_names ConLeche.reservedBasisNames :=
  fun _ h => BasisNames.reserved_basis_names_refines h

/-! ## The pinned `Nat`/`Bool` names and tables of `kernel/core_k.rs` -/

theorem pinned_nat_pred_name : PinnedName core_k.nat_pred_name ConLeche.natPredName :=
  fun _ h => nat_pred_name_refines h
theorem pinned_nat_add_name : PinnedName core_k.nat_add_name ConLeche.natAddName :=
  fun _ h => nat_add_name_refines h
theorem pinned_nat_sub_name : PinnedName core_k.nat_sub_name ConLeche.natSubName :=
  fun _ h => nat_sub_name_refines h
theorem pinned_nat_mul_name : PinnedName core_k.nat_mul_name ConLeche.natMulName :=
  fun _ h => nat_mul_name_refines h
theorem pinned_nat_pow_name : PinnedName core_k.nat_pow_name ConLeche.natPowName :=
  fun _ h => nat_pow_name_refines h
theorem pinned_nat_beq_name : PinnedName core_k.nat_beq_name ConLeche.natBeqName :=
  fun _ h => nat_beq_name_refines h
theorem pinned_nat_ble_name : PinnedName core_k.nat_ble_name ConLeche.natBleName :=
  fun _ h => nat_ble_name_refines h
theorem pinned_nat_div_name : PinnedName core_k.nat_div_name ConLeche.natDivName :=
  fun _ h => nat_div_name_refines h
theorem pinned_nat_mod_name : PinnedName core_k.nat_mod_name ConLeche.natModName :=
  fun _ h => nat_mod_name_refines h
theorem pinned_nat_gcd_name : PinnedName core_k.nat_gcd_name ConLeche.natGcdName :=
  fun _ h => nat_gcd_name_refines h
theorem pinned_nat_land_name : PinnedName core_k.nat_land_name ConLeche.natLandName :=
  fun _ h => nat_land_name_refines h
theorem pinned_nat_lor_name : PinnedName core_k.nat_lor_name ConLeche.natLorName :=
  fun _ h => nat_lor_name_refines h
theorem pinned_nat_xor_name : PinnedName core_k.nat_xor_name ConLeche.natXorName :=
  fun _ h => nat_xor_name_refines h
theorem pinned_nat_shift_left_name :
    PinnedName core_k.nat_shift_left_name ConLeche.natShiftLeftName :=
  fun _ h => nat_shift_left_name_refines h
theorem pinned_nat_shift_right_name :
    PinnedName core_k.nat_shift_right_name ConLeche.natShiftRightName :=
  fun _ h => nat_shift_right_name_refines h
theorem pinned_bool_name : PinnedName core_k.bool_name ConLeche.boolName :=
  fun _ h => bool_name_refines h
theorem pinned_bool_true_name : PinnedName core_k.bool_true_name ConLeche.boolTrueName :=
  fun _ h => bool_true_name_refines h
theorem pinned_bool_false_name : PinnedName core_k.bool_false_name ConLeche.boolFalseName :=
  fun _ h => bool_false_name_refines h

theorem pinned_nat_op_names : PinnedNames core_k.nat_op_names ConLeche.natOpNames :=
  fun _ h => nat_op_names_refines h
theorem pinned_nat_div_mod_names :
    PinnedNames core_k.nat_div_mod_names ConLeche.natDivModNames :=
  fun _ h => nat_div_mod_names_refines h
theorem pinned_nat_op_wf_names : PinnedNames core_k.nat_op_wf_names ConLeche.natOpWfNames :=
  fun _ h => nat_op_wf_names_refines h

/-! ## The bundles -/

/-- `CoreKSupport.lean`'s ten `basis_names` pins. -/
theorem pinnedBasisNames : PinnedBasisNames where
  nat := fun _ h => BasisNames.nat_name_refines h
  natZero := fun _ h => BasisNames.nat_zero_name_refines h
  natSucc := fun _ h => BasisNames.nat_succ_name_refines h
  string := fun _ h => BasisNames.string_name_refines h
  stringOfList := fun _ h => BasisNames.string_of_list_name_refines h
  list := fun _ h => BasisNames.list_name_refines h
  listNil := fun _ h => BasisNames.list_nil_name_refines h
  listCons := fun _ h => BasisNames.list_cons_name_refines h
  char := fun _ h => BasisNames.char_name_refines h
  charOfNat := fun _ h => BasisNames.char_of_nat_name_refines h

/-- `CoreKLits.lean`'s seventeen `Nat`-operation pins. -/
theorem natOpPinned : NatOpPinned where
  pred := pinned_nat_pred_name
  add := pinned_nat_add_name
  sub := pinned_nat_sub_name
  mul := pinned_nat_mul_name
  pow := pinned_nat_pow_name
  div := pinned_nat_div_name
  mod := pinned_nat_mod_name
  gcd := pinned_nat_gcd_name
  land := pinned_nat_land_name
  lor := pinned_nat_lor_name
  xor := pinned_nat_xor_name
  shl := pinned_nat_shift_left_name
  shr := pinned_nat_shift_right_name
  beq := pinned_nat_beq_name
  ble := pinned_nat_ble_name
  boolTrue := pinned_bool_true_name
  boolFalse := pinned_bool_false_name

/-- `CoreKShapes.lean`'s three `Vec` helpers. -/
theorem vecFacts : VecFacts where
  exprSingleton := fun he h => expr_singleton_refines he h
  appendExprs := fun hx hy h => append_exprs_refines hx hy h
  fvarLeavesSubset := fun hx hy h => fvar_leaves_subset_refines hx hy h

/-- `CoreKInfer.lean`'s `core_k::rev_append_exprs` clause. -/
theorem revAppendExprs : RevAppendExprs :=
  fun _ _ _ ho ht h => rev_append_exprs_refines ho ht h

/-- `CoreKInfer.lean`'s `core_k::proj_entry_fire_ok` clause. -/
theorem projEntryFireOk : ProjEntryFireOk :=
  fun _ _ _ he hus h => proj_entry_fire_ok_refines he hus h

/-- `CoreKNatOps.lean`'s `env::to_constant_val` clause. -/
theorem toConstantValSpec : ToConstantValSpec :=
  fun _ _ hc h => to_constant_val_refines hc h

/-- `CoreKNatOps.lean`'s `core_k::lp_empty` clause. -/
theorem lpEmptySpec {fe : fenv.FEnv} {lfe : ConLeche.FEnv} (hfe : FindAgree fe lfe) :
    LpEmptySpec fe lfe := fun _ _ hn h => lp_empty_refines hfe hn h

/-- `CoreKNatOps.lean`'s and `CoreKInfer.lean`'s `core_k::nat_lit_supported`
clause. -/
theorem natLitSupportedSpec {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) : NatLitSupportedSpec fe lfe :=
  fun _ h => nat_lit_supported_refines pinnedBasisNames hfe hwf h

/-- `CoreKGuards.lean`'s and `CoreKInfer.lean`'s `core_k::str_lit_supported`
clause. -/
theorem strLitSupportedSpec {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) :
    ∀ c : Bool, core_k.str_lit_supported fe = ok c → c = ConLeche.strLitSupportedF lfe :=
  fun _ h => str_lit_supported_refines pinnedBasisNames hfe hwf h

/-- `CoreKNatOps.lean`'s `core_k::defn_probe` clause. -/
theorem defnProbeSpec {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hfe : FindAgree fe lfe) (hwf : FindWF fe) : DefnProbeSpec fe lfe := by
  intro n o hn h
  obtain ⟨habs, hwf'⟩ := defn_probe_refines hfe hwf hn h
  refine ⟨habs, ?_⟩
  intro t ht
  exact hwf' t.1 t.2.1 t.2.2 (by rw [← ht])

/-- `CoreKShapes.lean`'s two `env` copies and two owning probes. -/
theorem envFacts : EnvFacts where
  levelsCopy := fun h => env_levels_copy_val h
  exprsCopy := fun h => env_exprs_copy_val h
  ctorProbe := fun hfe hwf hn h => ctor_probe_refines hfe hwf hn h
  indProbe := fun hfe hwf hn h => ind_probe_refines hfe hwf hn h
  constWF := fun he => wf_const_inv he

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/--
info: 'ConRon.Refine.CoreK.natOpPinned' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms natOpPinned

end ConRon.Refine.CoreK

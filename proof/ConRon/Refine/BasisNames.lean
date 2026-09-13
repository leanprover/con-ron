/-
`CORE_PLAN.md` step 4 (task #49), part one: **the pinned basis names**.

Every one of the 26 `pub fn` of `crates/con-ron-core/src/kernel/basis_names.rs`
refines its cited `ConLeche/Kernel/Basis/Names.lean` `def`, with `NameWF` on
the side.  Nothing here reads a state, an environment or an expression -- the
Rust module mentions no expression representation, exactly as the Lean's does
-- so each lemma is the same five lines: unfold the generated body, split the
two-or-three-bind `do` chain with `bind_eq_ok_iff`, and hand the pieces to
`CoreKBase`'s `str_lit_step`, which turns `name::mk_str pre (code_points S)`
into `.str (absName pre) (absCodes S)` and a `NameWF` proof.  The `const [u32;
N]` of DESIGN.md §3.3 is `@[irreducible]`, so its list is produced by
`simp [<the const's generated name>]` and the literal's code points are checked
valid by `decide`; the final `absCodes [69, 113] = "Eq"` step is `rfl`.

Two shapes are not closed-name lemmas:

* `rec_of` takes a `Name`, so it takes `NameWF` for it and refines
  `n.str "rec"` -- the suffix the cited Lean spells out at each of its five
  `reservedBasisNames` sites.
* `reserved_basis_names` returns a `Vec<Name>`; it is stated as
  `absNames v = reservedBasisNames ∧ NamesWF v` and proved by reading the 19
  pushes off with `vec_push_val`.

Nothing was hard.  `punit_rec_name` goes through `rec_of` in the port and is
spelled out in the Lean, so its lemma composes `punit_name_refines` with
`rec_of_refines` and finishes by `rfl`.
-/
import ConRon.Refine.CoreKBase

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.BasisNames

/-! ## basis_names -/

/-- `ConLeche/Kernel/Basis/Names.lean:17-18 eqName` --
`basis_names::eq_name` refines `eqName`. -/
theorem eq_name_refines {n : name.Name} (h : basis_names.eq_name = ok n) :
    absName n = ConLeche.eqName ∧ NameWF n := by
  rw [basis_names.eq_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [69#u32, 113#u32]) (by simp [basis_names.eq_name.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:20-21 eqReflName` --
`basis_names::eq_refl_name` refines `eqReflName`. -/
theorem eq_refl_name_refines {n : name.Name} (h : basis_names.eq_refl_name = ok n) :
    absName n = ConLeche.eqReflName ∧ NameWF n := by
  rw [basis_names.eq_refl_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := eq_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [114#u32, 101#u32, 102#u32, 108#u32]) (by simp [basis_names.eq_refl_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:23-24 punitName` --
`basis_names::punit_name` refines `punitName`. -/
theorem punit_name_refines {n : name.Name} (h : basis_names.punit_name = ok n) :
    absName n = ConLeche.punitName ∧ NameWF n := by
  rw [basis_names.punit_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [80#u32, 85#u32, 110#u32, 105#u32,
      116#u32]) (by simp [basis_names.punit_name.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-! `rec_of` and the two names built through it. -/

/-- `ConLeche/Kernel/Basis/Names.lean:105-115 reservedBasisNames` --
`basis_names::rec_of` is the `n.str "rec"` suffix the Lean spells out at each
of its five sites; it refines exactly that. -/
theorem rec_of_refines {n r : name.Name} (hn : NameWF n)
    (h : basis_names.rec_of n = ok r) :
    absName r = (absName n).str "rec" ∧ NameWF r := by
  rw [basis_names.rec_of] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨s, hs, v, hv, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step hn hs hv hmk
    (L := [114#u32, 101#u32, 99#u32]) (by simp [basis_names.rec_of.S]) (by decide)
  exact ⟨by rw [h1]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:26-29 punitRecName` --
`basis_names::punit_rec_name` refines `punitRecName`. -/
theorem punit_rec_name_refines {n : name.Name}
    (h : basis_names.punit_rec_name = ok n) :
    absName n = ConLeche.punitRecName ∧ NameWF n := by
  rw [basis_names.punit_rec_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, hrec⟩ := h
  obtain ⟨hp, hpwf⟩ := punit_name_refines ha
  obtain ⟨h1, h1wf⟩ := rec_of_refines hpwf hrec
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:31-32 natName` --
`basis_names::nat_name` refines `natName`. -/
theorem nat_name_refines {n : name.Name} (h : basis_names.nat_name = ok n) :
    absName n = ConLeche.natName ∧ NameWF n := by
  rw [basis_names.nat_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [78#u32, 97#u32, 116#u32]) (by simp [basis_names.nat_name.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:34-35 natZeroName` --
`basis_names::nat_zero_name` refines `natZeroName`. -/
theorem nat_zero_name_refines {n : name.Name} (h : basis_names.nat_zero_name = ok n) :
    absName n = ConLeche.natZeroName ∧ NameWF n := by
  rw [basis_names.nat_zero_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nat_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [122#u32, 101#u32, 114#u32,
      111#u32]) (by simp [basis_names.nat_zero_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:37-38 natSuccName` --
`basis_names::nat_succ_name` refines `natSuccName`. -/
theorem nat_succ_name_refines {n : name.Name} (h : basis_names.nat_succ_name = ok n) :
    absName n = ConLeche.natSuccName ∧ NameWF n := by
  rw [basis_names.nat_succ_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := nat_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [115#u32, 117#u32, 99#u32, 99#u32]) (by simp [basis_names.nat_succ_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:40-41 punitUnitName` --
`basis_names::punit_unit_name` refines `punitUnitName`. -/
theorem punit_unit_name_refines {n : name.Name} (h : basis_names.punit_unit_name = ok n) :
    absName n = ConLeche.punitUnitName ∧ NameWF n := by
  rw [basis_names.punit_unit_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := punit_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [117#u32, 110#u32, 105#u32,
      116#u32]) (by simp [basis_names.punit_unit_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:43-43 emptyName` --
`basis_names::empty_name` refines `emptyName`. -/
theorem empty_name_refines {n : name.Name} (h : basis_names.empty_name = ok n) :
    absName n = ConLeche.emptyName ∧ NameWF n := by
  rw [basis_names.empty_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [69#u32, 109#u32, 112#u32, 116#u32,
      121#u32]) (by simp [basis_names.empty_name.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:45-49 falseName` --
`basis_names::false_name` refines `falseName`. -/
theorem false_name_refines {n : name.Name} (h : basis_names.false_name = ok n) :
    absName n = ConLeche.falseName ∧ NameWF n := by
  rw [basis_names.false_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [70#u32, 97#u32, 108#u32, 115#u32,
      101#u32]) (by simp [basis_names.false_name.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:51-52 quotName` --
`basis_names::quot_name` refines `quotName`. -/
theorem quot_name_refines {n : name.Name} (h : basis_names.quot_name = ok n) :
    absName n = ConLeche.quotName ∧ NameWF n := by
  rw [basis_names.quot_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [81#u32, 117#u32, 111#u32, 116#u32]) (by simp [basis_names.quot_name.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:54-55 quotMkName` --
`basis_names::quot_mk_name` refines `quotMkName`. -/
theorem quot_mk_name_refines {n : name.Name} (h : basis_names.quot_mk_name = ok n) :
    absName n = ConLeche.quotMkName ∧ NameWF n := by
  rw [basis_names.quot_mk_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := quot_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [109#u32, 107#u32]) (by simp [basis_names.quot_mk_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:57-58 quotLiftName` --
`basis_names::quot_lift_name` refines `quotLiftName`. -/
theorem quot_lift_name_refines {n : name.Name} (h : basis_names.quot_lift_name = ok n) :
    absName n = ConLeche.quotLiftName ∧ NameWF n := by
  rw [basis_names.quot_lift_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := quot_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [108#u32, 105#u32, 102#u32,
      116#u32]) (by simp [basis_names.quot_lift_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:60-61 quotIndName` --
`basis_names::quot_ind_name` refines `quotIndName`. -/
theorem quot_ind_name_refines {n : name.Name} (h : basis_names.quot_ind_name = ok n) :
    absName n = ConLeche.quotIndName ∧ NameWF n := by
  rw [basis_names.quot_ind_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := quot_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [105#u32, 110#u32, 100#u32]) (by simp [basis_names.quot_ind_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:63-64 quotSoundName` --
`basis_names::quot_sound_name` refines `quotSoundName`. -/
theorem quot_sound_name_refines {n : name.Name} (h : basis_names.quot_sound_name = ok n) :
    absName n = ConLeche.quotSoundName ∧ NameWF n := by
  rw [basis_names.quot_sound_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := quot_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [115#u32, 111#u32, 117#u32, 110#u32,
      100#u32]) (by simp [basis_names.quot_sound_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:73-74 stringName` --
`basis_names::string_name` refines `stringName`. -/
theorem string_name_refines {n : name.Name} (h : basis_names.string_name = ok n) :
    absName n = ConLeche.stringName ∧ NameWF n := by
  rw [basis_names.string_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [83#u32, 116#u32, 114#u32, 105#u32, 110#u32,
      103#u32]) (by simp [basis_names.string_name.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:76-77 stringOfListName` --
`basis_names::string_of_list_name` refines `stringOfListName`. -/
theorem string_of_list_name_refines {n : name.Name} (h : basis_names.string_of_list_name = ok n) :
    absName n = ConLeche.stringOfListName ∧ NameWF n := by
  rw [basis_names.string_of_list_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := string_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [111#u32, 102#u32, 76#u32, 105#u32, 115#u32,
      116#u32]) (by simp [basis_names.string_of_list_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:79-80 listName` --
`basis_names::list_name` refines `listName`. -/
theorem list_name_refines {n : name.Name} (h : basis_names.list_name = ok n) :
    absName n = ConLeche.listName ∧ NameWF n := by
  rw [basis_names.list_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [76#u32, 105#u32, 115#u32, 116#u32]) (by simp [basis_names.list_name.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:82-83 listNilName` --
`basis_names::list_nil_name` refines `listNilName`. -/
theorem list_nil_name_refines {n : name.Name} (h : basis_names.list_nil_name = ok n) :
    absName n = ConLeche.listNilName ∧ NameWF n := by
  rw [basis_names.list_nil_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := list_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [110#u32, 105#u32, 108#u32]) (by simp [basis_names.list_nil_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:85-86 listConsName` --
`basis_names::list_cons_name` refines `listConsName`. -/
theorem list_cons_name_refines {n : name.Name} (h : basis_names.list_cons_name = ok n) :
    absName n = ConLeche.listConsName ∧ NameWF n := by
  rw [basis_names.list_cons_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := list_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [99#u32, 111#u32, 110#u32,
      115#u32]) (by simp [basis_names.list_cons_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:88-89 charName` --
`basis_names::char_name` refines `charName`. -/
theorem char_name_refines {n : name.Name} (h : basis_names.char_name = ok n) :
    absName n = ConLeche.charName ∧ NameWF n := by
  rw [basis_names.char_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [67#u32, 104#u32, 97#u32, 114#u32]) (by simp [basis_names.char_name.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:91-97 andName` --
`basis_names::and_name` refines `andName`. -/
theorem and_name_refines {n : name.Name} (h : basis_names.and_name = ok n) :
    absName n = ConLeche.andName ∧ NameWF n := by
  rw [basis_names.and_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step (Name.anonymous_wf ha) hs hv hmk
    (L := [65#u32, 110#u32, 100#u32]) (by simp [basis_names.and_name.S]) (by decide)
  exact ⟨by rw [h1, Name.anonymous_refines ha]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:99-100 andIntroName` --
`basis_names::and_intro_name` refines `andIntroName`. -/
theorem and_intro_name_refines {n : name.Name} (h : basis_names.and_intro_name = ok n) :
    absName n = ConLeche.andIntroName ∧ NameWF n := by
  rw [basis_names.and_intro_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := and_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [105#u32, 110#u32, 116#u32, 114#u32,
      111#u32]) (by simp [basis_names.and_intro_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:102-103 charOfNatName` --
`basis_names::char_of_nat_name` refines `charOfNatName`. -/
theorem char_of_nat_name_refines {n : name.Name} (h : basis_names.char_of_nat_name = ok n) :
    absName n = ConLeche.charOfNatName ∧ NameWF n := by
  rw [basis_names.char_of_nat_name] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨a, ha, s, hs, v, hv, hmk⟩ := h
  obtain ⟨hp, hpwf⟩ := char_name_refines ha
  obtain ⟨h1, h1wf⟩ := str_lit_step hpwf hs hv hmk
    (L := [111#u32, 102#u32, 78#u32, 97#u32,
      116#u32]) (by simp [basis_names.char_of_nat_name.S]) (by decide)
  exact ⟨by rw [h1, hp]; rfl, h1wf⟩

/-- `ConLeche/Kernel/Basis/Names.lean:105-115 reservedBasisNames` --
`basis_names::reserved_basis_names` refines `reservedBasisNames`: the cited
`List Name` is the `Vec<Name>` built in the cited order, and the five
`… .str "rec"` entries go through `rec_of`. -/
theorem reserved_basis_names_refines {v : alloc.vec.Vec name.Name}
    (h : basis_names.reserved_basis_names = ok v) :
    absNames v = ConLeche.reservedBasisNames ∧ NamesWF v := by
  rw [basis_names.reserved_basis_names] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨m0, hm0, w0, hw0, m1, hm1, w1, hw1, m2, hm2, w2, hw2, m3, hm3, w3, hw3, m4, hm4, w4,
    hw4, m5, hm5, w5, hw5, m6, hm6, w6, hw6, m7, hm7, w7, hw7, m8, hm8, w8, hw8, m9, hm9, w9, hw9,
    m10, hm10, w10, hw10, m11, hm11, w11, hw11, m12, hm12, w12, hw12, m13, hm13, w13, hw13, m14,
    hm14, w14, hw14, m15, hm15, w15, hw15, m16, hm16, w16, hw16, m17, hm17, w17, hw17, m18, hm18,
    hlast⟩ := h
  obtain ⟨e0, f0⟩ := eq_name_refines hm0
  obtain ⟨e1, f1⟩ := eq_refl_name_refines hm1
  obtain ⟨e2, f2⟩ := rec_of_refines f0 hm2
  obtain ⟨e3, f3⟩ := nat_name_refines hm3
  obtain ⟨e4, f4⟩ := nat_zero_name_refines hm4
  obtain ⟨e5, f5⟩ := nat_succ_name_refines hm5
  obtain ⟨e6, f6⟩ := rec_of_refines f3 hm6
  obtain ⟨e7, f7⟩ := punit_name_refines hm7
  obtain ⟨e8, f8⟩ := punit_unit_name_refines hm8
  obtain ⟨e9, f9⟩ := rec_of_refines f7 hm9
  obtain ⟨e10, f10⟩ := empty_name_refines hm10
  obtain ⟨e11, f11⟩ := rec_of_refines f10 hm11
  obtain ⟨e12, f12⟩ := false_name_refines hm12
  obtain ⟨e13, f13⟩ := rec_of_refines f12 hm13
  obtain ⟨e14, f14⟩ := quot_name_refines hm14
  obtain ⟨e15, f15⟩ := quot_mk_name_refines hm15
  obtain ⟨e16, f16⟩ := quot_lift_name_refines hm16
  obtain ⟨e17, f17⟩ := quot_ind_name_refines hm17
  obtain ⟨e18, f18⟩ := quot_sound_name_refines hm18
  have hval : v.val = [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16,
    m17, m18] := by
    rw [vec_push_val hlast, vec_push_val hw17, vec_push_val hw16, vec_push_val hw15,
      vec_push_val hw14, vec_push_val hw13, vec_push_val hw12, vec_push_val hw11,
      vec_push_val hw10, vec_push_val hw9, vec_push_val hw8, vec_push_val hw7, vec_push_val hw6,
      vec_push_val hw5, vec_push_val hw4, vec_push_val hw3, vec_push_val hw2, vec_push_val hw1,
      vec_push_val hw0]
    simp
  refine ⟨?_, ?_⟩
  · rw [absNames, hval]
    simp only [List.map_cons, List.map_nil, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12,
      e13, e14, e15, e16, e17, e18]
    rfl
  · intro x hx
    rw [hval] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    exacts [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18]

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/--
info: 'ConRon.Refine.BasisNames.reserved_basis_names_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reserved_basis_names_refines

end ConRon.Refine.BasisNames

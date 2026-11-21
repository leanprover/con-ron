/-
# `ConRon.Refine2.Frontend.Olean.AllViews` — `view::parse_all_views` against `parseAllViews`

**Task #166, Theorem 2.**  What `check_views` (`CheckViews.lean`) reads of a module's skeleton:
its imports (`mod_skel_imports` against `sk.imports.mapM`), a stored constant as the twin's
(`ERel`), and a pointwise read of two related lists (`f2_get`).
-/
import ConRon.Refine2.Frontend.Olean.View
import ConRon.Refine2.Frontend.Olean.Stmts
import ConRon.Refine2.Frontend.ExportC
import ConRon.Refine2.Frontend.Olean.Group

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.region (region_loc region_single part_module_data_addr region_of_parts2
  region_of_parts3)
open frontend.olean.fast (consts_skel consts_skel_loop many_skels many_skels_loop many_read
  many_read_loop mod_skel_read mod_skel_imports mod_skel_imports_loop mod_skel_constants
  mod_skel_constants_loop all_const_names_ok all_const_names_ok_loop many_roots many_roots_loop0
  many_roots_loop0_loop0 many_roots_loop1 many_roots_loop1_loop0 parse_many parse_at
  take_decoded run_passes c_entry_names c_entry_exprs)
open frontend.olean.spec (const_skel module_skel skel_fits import_map c_entry_map names_map
  const_names_ok)
open frontend.olean.view (mod_files_is_module rules_dup rules_dup_loop c_kind_dup c_entry_dup
  mod_decoded_dup mod_decoded_dup_loop0 mod_decoded_dup_loop1 loc_is_some loc_in_two
  check_imports_pre parse_view parse_all_views parse_all_views_module)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Arena.Frontend.Olean (constsSkel manySkels skelFits entryMap allConstNamesOk parseMany
  parseAt runPasses constNamesOk checkImportsPre parseView parseAllViews parseAllViewsModule
  importsPre)
open ConLeche.Frontend.Olean (CKindF CEntryF ImportF ModSkel constSkel moduleSkel ModFiles OLeanLevel)
open ConLeche.Frontend.Olean.Region (ofParts single)
open ConRon.Refine.HashMap (uscalar_add_eq uscalar_div_eq)

/-- **`mod_skel_imports` is `sk.imports.mapM`.** -/
theorem mod_skel_imports_refines {R : Type} {inst : frontend.olean.spec.PtrRead R} {rd : R}
    {t : Arena.Frontend.Olean.PtrRead} {pk bs r pers} (hp : PtrRel inst rd t pk bs r pers)
    {sk : frontend.olean.spec.ModSkel} {l : List (ImportF UInt64)}
    (hl : sk.imports.val.map (absImportF absWord) = l) (st lst) :
    RS pers (fun v l' => List.Forall₂ (EqA (absImportF absNIdx)) v.val l') st lst
      (mod_skel_imports inst rd pk pers st.store bs r sk)
      (l.mapM (m := OptionT AM) fun i => ImportF.mapM (m := OptionT AM) (fun v => OptionT.mk (t.rdName v)) i) := by
  subst hl
  rw [mod_skel_imports]
  refine RS.vec_map (R := EqA (absImportF absNIdx))
    (loop := fun ar out i => mod_skel_imports_loop inst rd pk pers ar bs r sk.imports out i)
    (forall₂_of_map (A := absImportF absWord) sk.imports.val) ?_ ?_ (by simp) (by rfl)
  · intro ar out i hi
    show mod_skel_imports_loop inst rd pk pers ar bs r sk.imports out i = _
    rw [mod_skel_imports_loop, ite_eq_right (by scalar_tac)]
  · intro i out x x' K Rf st lst hx hS hK
    cases hS
    show RS _ _ _ _ (mod_skel_imports_loop inst rd pk pers st.store bs r sk.imports out i) _
    rw [mod_skel_imports_loop,
      ite_eq_left (by have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)]
    refine RS.pure_step fun y hy => ?_
    have hy3 := ConRon.Refine.ExprOps.vec_index_getElem? hy
    rw [hx] at hy3
    cases Option.some.inj hy3
    refine RS.bindT (import_map_refines hp st lst) (fun _ _ => by rfl) fun a b s1 lst1 hR =>
      RS.pure_step fun out1 ho => RS.pure_step fun i3 hi3 => ?_
    exact hK a b s1 lst1 out1 i3 hR (ConRon.Refine.vec_push_val ho) (uscalar_add_eq hi3)

theorem am_pure_bind {α β : Type} (a : α) (g : α → AM β) : (pure a >>= g) = g a := rfl

/-- A stored constant, as the twin's. -/
abbrev ERel := EntryRel (N := arena.handle.NIdx) (E := arena.handle.EIdx) absNIdx absEIdx ValRel

/-- Two lists related pointwise: an entry of the first, its partner in the second. -/
theorem f2_get {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : List.Forall₂ R l l') {i : Nat} {x : α} (hi : l[i]? = some x) :
    ∃ y, l'[i]? = some y ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hi
  | cons hab _ ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact ⟨_, rfl, hab⟩
    | succ i => simpa using ih (by simpa using hi)

end ConRon.Refine2.Frontend.Olean

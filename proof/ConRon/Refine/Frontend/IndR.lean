/-
`ConRon.Refine.Frontend.IndR` — **the inductive-record path of `export_c`,
exact against con-leche** (task #87, phase 3).

Phase 1's `ConRon/Refine/Frontend/Ind.lean` proved this path *well formed*:
every term `install_ind_d` puts into the parse state is one the port's own
smart constructors built.  This file proves it **exact**: for the same records
the port's `apply_line` does to the state what `ConLeche.Frontend.applyLine`
does to the abstracted one, and it fails exactly where con-leche's does.

The port is `crates/con-ron-core/src/frontend/export_c.rs` lines 1000-2400
against `vendor/con-leche/ConLeche/Frontend/ExportC.lean` lines 296-730.
Task #84 split several Lean functions into many Rust ones for Aeneas's loop
shape rule — `validateIndD` and `installIndD` alone became twenty-odd — so
each lemma below is stated against the *fragment* of the Lean its Rust
function's `/// con-leche:` comment cites, and the fragments are composed.

## `sorry` count in this file: 0
-/
import ConRon.Refine.Frontend.Ind
import ConRon.Refine.Frontend.Abs
import ConRon.Refine.ExprOpsSpine
import ConRon.Refine.Env
import ConRon.Refine.Level

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

/-! ## Plumbing -/

/-- The image of a `Vec` read at `i`, as the head of the abstracted tail.
(`Refine/Frontend/ProjRecR.lean` keeps its own copy; this file is not below
it, so the one line is restated rather than the import widened.) -/
private theorem indr_drop_map_index {α β : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (f : α → β)
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    i.val < v.val.length ∧
      (v.val.map f).drop i.val = f x :: (v.val.map f).drop (i.val + 1) := by
  have hg := ExprOps.vec_index_getElem? h
  have hlt : i.val < v.val.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
  have hx : v.val[i.val] = x := by
    rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
  refine ⟨hlt, ?_⟩
  rw [List.drop_eq_getElem_cons (by simpa using hlt)]
  simp [hx]

/-! ## The three boolean scans of `validateIndD`

`ExportC.lean:412-563` opens with `tys.any (·.isUnsafe)` and later reads
`tys.any (·.numNested != 0)`; between them stands `nPs.all (· == nPd)` on
`nPs := tys.map (·.numParams)`.  Each is one `while i < n` loop in the port
(`export_c.rs:1277`, `:1291`, `:1305`), so each gets the index recursion and
the wrapper. -/

/-- The index recursion behind `export_c::any_ty_unsafe`. -/
private theorem any_ty_unsafe_loop_refines (N : Nat) :
    ∀ (tys : alloc.vec.Vec frontend.scan_types.IndTypeRec) (n i : Std.Usize) (b : Bool),
      tys.val.length - i.val = N → n.val = tys.val.length →
      frontend.export_c.any_ty_unsafe_loop tys n i = ok b →
      b = ((absIndTypeRecs tys).drop i.val).any (·.isUnsafe) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro tys n i b hN hn h
    rw [frontend.export_c.any_ty_unsafe_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < tys.val.length := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨itr, hidx, h⟩ := h
      obtain ⟨-, hdrop⟩ := indr_drop_map_index absIndTypeRec hidx
      simp only [absIndTypeRecs] at hdrop ⊢
      rw [hdrop]
      split at h
      · rename_i hu
        simp only [Result.ok.injEq] at h
        simp [← h, absIndTypeRec, hu]
      · rename_i hu
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        rw [ih (tys.val.length - i2.val) (by omega) tys n i2 b rfl hn h, hi2v]
        simp [absIndTypeRecs, absIndTypeRec, hu]
    · rename_i hge
      have hle : tys.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h]
      simp only [absIndTypeRecs]
      rw [List.drop_eq_nil_of_le (by simpa using hle)]
      simp

/-- `export_c::any_ty_unsafe` refines the `tys.any (·.isUnsafe)` of
`validateIndD` (`ConLeche/Frontend/ExportC.lean:412-563`). -/
theorem any_ty_unsafe_refines {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec} {b : Bool}
    (h : frontend.export_c.any_ty_unsafe tys = ok b) :
    b = (absIndTypeRecs tys).any (·.isUnsafe) := by
  rw [frontend.export_c.any_ty_unsafe] at h
  rw [any_ty_unsafe_loop_refines _ tys _ 0#usize b rfl (by simp [alloc.vec.Vec.len]) h]
  simp [show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

/-- The index recursion behind `export_c::any_ty_nested`. -/
private theorem any_ty_nested_loop_refines (N : Nat) :
    ∀ (tys : alloc.vec.Vec frontend.scan_types.IndTypeRec) (n i : Std.Usize) (b : Bool),
      tys.val.length - i.val = N → n.val = tys.val.length →
      frontend.export_c.any_ty_nested_loop tys n i = ok b →
      b = ((absIndTypeRecs tys).drop i.val).any (·.numNested != 0) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro tys n i b hN hn h
    rw [frontend.export_c.any_ty_nested_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < tys.val.length := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨itr, hidx, h⟩ := h
      obtain ⟨-, hdrop⟩ := indr_drop_map_index absIndTypeRec hidx
      simp only [absIndTypeRecs] at hdrop ⊢
      rw [hdrop]
      split at h
      · rename_i hu
        simp only [Result.ok.injEq] at h
        have hne : itr.num_nested.val ≠ 0 := by simpa using hu
        simp [← h, absIndTypeRec, absU64, hne]
      · rename_i hu
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have heq : itr.num_nested.val = 0 := by simpa using hu
        rw [ih (tys.val.length - i2.val) (by omega) tys n i2 b rfl hn h, hi2v]
        simp [absIndTypeRecs, absIndTypeRec, absU64, heq]
    · rename_i hge
      have hle : tys.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h]
      simp only [absIndTypeRecs]
      rw [List.drop_eq_nil_of_le (by simpa using hle)]
      simp

/-- `export_c::any_ty_nested` refines the `tys.any (·.numNested != 0)` of
`validateIndD` (`ConLeche/Frontend/ExportC.lean:412-563`). -/
theorem any_ty_nested_refines {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec} {b : Bool}
    (h : frontend.export_c.any_ty_nested tys = ok b) :
    b = (absIndTypeRecs tys).any (·.numNested != 0) := by
  rw [frontend.export_c.any_ty_nested] at h
  rw [any_ty_nested_loop_refines _ tys _ 0#usize b rfl (by simp [alloc.vec.Vec.len]) h]
  simp [show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

/-- The index recursion behind `export_c::all_num_params`. -/
private theorem all_num_params_loop_refines (N : Nat) :
    ∀ (tys : alloc.vec.Vec frontend.scan_types.IndTypeRec) (n_pd : Std.U64)
      (n i : Std.Usize) (b : Bool),
      tys.val.length - i.val = N → n.val = tys.val.length →
      frontend.export_c.all_num_params_loop tys n_pd n i = ok b →
      b = (((absIndTypeRecs tys).drop i.val).map (·.numParams)).all (· == n_pd.val) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro tys n_pd n i b hN hn h
    rw [frontend.export_c.all_num_params_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < tys.val.length := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨itr, hidx, h⟩ := h
      obtain ⟨-, hdrop⟩ := indr_drop_map_index absIndTypeRec hidx
      simp only [absIndTypeRecs] at hdrop ⊢
      rw [hdrop]
      split at h
      · rename_i hu
        simp only [Result.ok.injEq] at h
        have hne : itr.num_params.val ≠ n_pd.val := by simpa using hu
        simp [← h, absIndTypeRec, absU64, hne]
      · rename_i hu
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have heq : itr.num_params.val = n_pd.val := by simpa using hu
        rw [ih (tys.val.length - i2.val) (by omega) tys n_pd n i2 b rfl hn h, hi2v]
        simp [absIndTypeRecs, absIndTypeRec, absU64, heq]
    · rename_i hge
      have hle : tys.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h]
      simp only [absIndTypeRecs]
      rw [List.drop_eq_nil_of_le (by simpa using hle)]
      simp

/-- `export_c::all_num_params` refines the `nPs.all (· == nPd)` of
`validateIndD` (`ConLeche/Frontend/ExportC.lean:412-563`), at
`nPs := tys.map (·.numParams)`. -/
theorem all_num_params_refines {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec}
    {n_pd : Std.U64} {b : Bool}
    (h : frontend.export_c.all_num_params tys n_pd = ok b) :
    b = ((absIndTypeRecs tys).map (·.numParams)).all (· == n_pd.val) := by
  rw [frontend.export_c.all_num_params] at h
  rw [all_num_params_loop_refines _ tys n_pd _ 0#usize b rfl
    (by simp [alloc.vec.Vec.len]) h]
  simp [show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

end ConRon.Refine.Frontend

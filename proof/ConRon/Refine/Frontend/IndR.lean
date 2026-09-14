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
import ConRon.Refine.CoreKGuards
import ConRon.Refine.CoreKShapes

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

/-- A machine word is its value: the port's `!=` on a `u32` code point is
inequality of the two `Nat`s. -/
private theorem uscalar_val_inj {ty : Std.UScalarTy} {a b : Std.UScalar ty}
    (h : a.val = b.val) : a = b := by
  rw [Std.UScalar.eq_equiv_bv_eq]
  exact BitVec.eq_of_toNat_eq h

/-- A `const [u32; N]` literal read as a slice: the slice is the array
(DESIGN.md §3.3's spelling of a Lean string literal). -/
private theorem slice_lit_val {k : Std.Usize} {S : Array Std.U32 k} {s : Slice Std.U32}
    (h : lift (Array.to_slice S) = ok s) : s.val = S.val := by
  simp only [lift_eq, Result.ok.injEq] at h
  subst h
  simp [Array.val_to_slice]

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

/-! ## `text::cps_beq`, the literal comparison

Four of this file's readers compare a scanned `Vec<u32>` with a `const [u32;
N]` literal — `process_line_core_d`'s `safety` and `quot_kind_of`'s four kind
words, `check_one_rec`'s `"rec"`.  On con-leche's side those are `String`
matches, and the bridge is `CoreKBase.absString_eq_codes` on top of the one
loop lemma here. -/

/-- The index recursion behind `text::cps_beq`. -/
private theorem cps_beq_loop_refines (N : Nat) :
    ∀ (s : alloc.vec.Vec Std.U32) (lit : Slice Std.U32) (n i : Std.Usize) (b : Bool),
      s.val.length - i.val = N → n.val = s.val.length → s.val.length = lit.val.length →
      frontend.text.cps_beq_loop s lit n i = ok b →
      (b = true ↔ s.val.drop i.val = lit.val.drop i.val) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro s lit n i b hN hn hlen h
    rw [frontend.text.cps_beq_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < s.val.length := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, hc, c2, hc2, h⟩ := h
      obtain ⟨-, hdrops⟩ := indr_drop_map_index (fun x : Std.U32 => x) hc
      have hdrops' : s.val.drop i.val = c :: s.val.drop (i.val + 1) := by
        simpa using hdrops
      have hlit : lit.val[i.val]'(by omega) = c2 := by
        have hg := slice_index_getElem? hc2
        rw [List.getElem?_eq_getElem (by omega)] at hg
        exact Option.some_injective _ hg
      have hdropl : lit.val.drop i.val = c2 :: lit.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (by omega), hlit]
      rw [hdrops', hdropl]
      split at h
      · rename_i hne
        simp only [Result.ok.injEq] at h
        have hval : ¬ (c.val = c2.val) := by simpa using hne
        have hcc : c ≠ c2 := fun hc => hval (congrArg Std.UScalar.val hc)
        simp [← h, hcc]
      · rename_i hne
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hceq : c = c2 := uscalar_val_inj (by simpa using hne)
        rw [ih (s.val.length - i2.val) (by omega) s lit n i2 b rfl hn hlen h, hi2v]
        simp [hceq]
    · rename_i hge
      have hle : s.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h]
      rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
      simp

/-- `text::cps_beq` is list equality of the code points. -/
theorem cps_beq_refines {s : alloc.vec.Vec Std.U32} {lit : Slice Std.U32} {b : Bool}
    (h : frontend.text.cps_beq s lit = ok b) : (b = true ↔ s.val = lit.val) := by
  rw [frontend.text.cps_beq] at h
  split at h
  · rename_i hne
    have hl : s.val.length ≠ lit.val.length := by
      simpa [alloc.vec.Vec.len, Slice.len] using hne
    simp only [Result.ok.injEq] at h
    refine ⟨fun hb => absurd (h ▸ hb) (by simp), fun he => ?_⟩
    exact absurd (congrArg List.length he) hl
  · rename_i hne
    have hl : s.val.length = lit.val.length := by
      simpa [alloc.vec.Vec.len, Slice.len] using hne
    have hh := cps_beq_loop_refines _ s lit _ 0#usize b rfl (by simp [alloc.vec.Vec.len]) hl h
    simpa [show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hh

/-- A scanned string payload equals a literal exactly when `cps_beq` says so. -/
theorem cps_beq_str {s : alloc.vec.Vec Std.U32} {lit : Slice Std.U32} {b : Bool}
    (hs : StrWF s) (hL : ∀ c ∈ lit.val, Nat.isValidChar c.val)
    (h : frontend.text.cps_beq s lit = ok b) :
    (b = true ↔ absString s = absCodes lit.val) := by
  rw [cps_beq_refines h]
  exact (CoreK.absString_eq_codes hs hL (by scalar_tac)).symm

/-! ## `indPiTeleLen` (`ConLeche/Frontend/ExportC.lean:342-344`)

The port walks the spine with `core_k::is_forall` and an owning step function
(`ind_pi_body`), because Aeneas cannot hold `cur`'s borrow across the write
that rebinds it; con-leche pattern-matches.  The walk is an induction on the
`ExprWF` derivation, not on a `Nat` measure. -/

/-- `export_c::ind_pi_body` is the `∀`-binder's body. -/
private theorem ind_pi_body_forall {d : Std.U64} {ty bo : expr.Expr}
    {m : expr.BinderMeta} {r : expr.Expr}
    (h : frontend.export_c.ind_pi_body (expr.Expr.mk (expr.ExprNode.mk d
      (expr.ExprKind.ForallE ty bo m))) = ok r) : r = bo := by
  rw [frontend.export_c.ind_pi_body] at h
  simp only [arc_deref_eq, ExprOps.node_kind, expr_dup_eq, bind_tc_ok,
    Result.ok.injEq] at h
  exact h.symm

/-- The spine walk behind `export_c::ind_pi_tele_len`. -/
private theorem ind_pi_tele_len_loop_refines (cur : expr.Expr) (hcur : ExprWF cur) :
    ∀ (n r : Std.U64), frontend.export_c.ind_pi_tele_len_loop n cur = ok r →
      r.val = n.val + ConLeche.Frontend.indPiTeleLen (absExpr cur) := by
  induction cur, hcur using ExprWF.ind_node with
  | forall_e d ty bo m hwf ihty ihb =>
    intro n r h
    rw [frontend.export_c.ind_pi_tele_len_loop.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    have hbt : b = true := by
      rw [CoreK.is_forall_refines hb]; simp [absExpr_mk, absExprKind]
    rw [hbt] at h
    simp only [reduceIte, bind_eq_ok_iff] at h
    obtain ⟨cur1, hcur1, n1, hn1, h⟩ := h
    obtain ⟨hty, hbo, hm⟩ := ExprWF.forall_e_kids hwf
    rw [ind_pi_body_forall hcur1] at h
    have hn1v : n1.val = n.val + 1 := HashMap.uscalar_add_eq hn1
    rw [ihb hbo n1 r h, hn1v]
    simp only [absExpr_mk, absExprKind, ConLeche.Frontend.indPiTeleLen]
    omega
  | _ =>
    intro n r h
    rw [frontend.export_c.ind_pi_tele_len_loop.eq_def] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    have hbf : b = false := by
      rw [CoreK.is_forall_refines hb]; simp [absExpr_mk, absExprKind]
    rw [hbf] at h
    simp only [Bool.false_eq_true, reduceIte, Result.ok.injEq] at h
    rw [← h]
    simp [absExpr_mk, absExprKind, ConLeche.Frontend.indPiTeleLen]

/-- `export_c::ind_pi_tele_len` refines `indPiTeleLen`
(`ConLeche/Frontend/ExportC.lean:342-344`). -/
theorem ind_pi_tele_len_refines {e : expr.Expr} {r : Std.U64} (he : ExprWF e)
    (h : frontend.export_c.ind_pi_tele_len e = ok r) :
    r.val = ConLeche.Frontend.indPiTeleLen (absExpr e) := by
  rw [frontend.export_c.ind_pi_tele_len] at h
  simp only [expr_dup_eq, bind_tc_ok] at h
  rw [ind_pi_tele_len_loop_refines e he _ r h]
  simp

/-! ## `listed.flatten` (`ConLeche/Frontend/ExportC.lean:412-563`) -/

/-- A `Vec<Vec<Name>>` as con-leche's `List (List Name)`: the constructor names
each type record LISTS, in type order. -/
def absNamess (v : alloc.vec.Vec (alloc.vec.Vec name.Name)) : List (List ConLeche.Name) :=
  v.val.map absNames

/-- The inner index recursion behind `export_c::flatten_listed`. -/
private theorem flatten_listed_inner_refines (N : Nat) :
    ∀ (out inner r : alloc.vec.Vec name.Name) (k j : Std.Usize),
      inner.val.length - j.val = N → k.val = inner.val.length →
      frontend.export_c.flatten_listed_loop0_loop0 out inner k j = ok r →
      absNames r = absNames out ++ (absNames inner).drop j.val := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro out inner r k j hN hk h
    rw [frontend.export_c.flatten_listed_loop0_loop0.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : j.val < inner.val.length := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨nm, hidx, nm1, hdup, out1, hpush, j2, hj2, h⟩ := h
      obtain ⟨-, hdrop⟩ := indr_drop_map_index absName hidx
      rw [name_dup_eq] at hdup
      have hnm1 : nm1 = nm := (Result.ok_injective hdup).symm
      rw [hnm1] at hpush
      have hj2v : j2.val = j.val + 1 := HashMap.uscalar_add_eq hj2
      rw [ih (inner.val.length - j2.val) (by omega) out1 inner r k j2 rfl hk h, hj2v]
      rw [absNames, vec_push_val hpush]
      simp only [absNames] at hdrop ⊢
      rw [hdrop]; simp
    · rename_i hge
      have hle : inner.val.length ≤ j.val := by scalar_tac
      rw [← Result.ok_injective h]
      simp only [absNames]
      rw [List.drop_eq_nil_of_le (by simpa using hle)]
      simp

/-- The outer index recursion behind `export_c::flatten_listed`. -/
private theorem flatten_listed_loop_refines (N : Nat) :
    ∀ (listed : alloc.vec.Vec (alloc.vec.Vec name.Name)) (out r : alloc.vec.Vec name.Name)
      (n i : Std.Usize),
      listed.val.length - i.val = N → n.val = listed.val.length →
      frontend.export_c.flatten_listed_loop0 listed out n i = ok r →
      absNames r = absNames out ++ ((absNamess listed).drop i.val).flatten := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro listed out r n i hN hn h
    rw [frontend.export_c.flatten_listed_loop0.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < listed.val.length := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨inner, hidx, out1, hinner, i2, hi2, h⟩ := h
      obtain ⟨-, hdrop⟩ := indr_drop_map_index absNames hidx
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      have hin := flatten_listed_inner_refines _ out inner out1 _ 0#usize rfl
        (by simp [alloc.vec.Vec.len]) hinner
      rw [ih (listed.val.length - i2.val) (by omega) listed out1 r n i2 rfl hn h,
        hin, hi2v]
      simp only [absNamess] at hdrop ⊢
      rw [hdrop]
      simp [show ((0#usize : Std.Usize)).val = 0 by scalar_tac]
    · rename_i hge
      have hle : listed.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h]
      simp only [absNamess]
      rw [List.drop_eq_nil_of_le (by simpa using hle)]
      simp

/-- `export_c::flatten_listed` refines the `listed.flatten` of `validateIndD`
(`ConLeche/Frontend/ExportC.lean:412-563`). -/
theorem flatten_listed_refines {listed : alloc.vec.Vec (alloc.vec.Vec name.Name)}
    {r : alloc.vec.Vec name.Name}
    (h : frontend.export_c.flatten_listed listed = ok r) :
    absNames r = (absNamess listed).flatten := by
  rw [frontend.export_c.flatten_listed] at h
  rw [flatten_listed_loop_refines _ listed _ r _ 0#usize rfl
    (by simp [alloc.vec.Vec.len]) h]
  simp [absNames, alloc.vec.Vec.new, show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

/-! ## `quot_kind_of` (`ConLeche/Frontend/ExportC.lean:629-709`, the `.quot` arm) -/

/-- `export_c::quot_kind_of` refines the `match kind with | "type" => …` of
`processLineCoreD`'s `.quot` arm (`ConLeche/Frontend/ExportC.lean:629-709`). -/
theorem quot_kind_of_refines {k : alloc.vec.Vec Std.U32} {o : Option env.QuotKind}
    (hk : StrWF k) (h : frontend.export_c.quot_kind_of k = ok o) :
    o.map absQuotKind =
      (if absString k = "type" then some ConLeche.QuotKind.type
       else if absString k = "ctor" then some ConLeche.QuotKind.ctor
       else if absString k = "lift" then some ConLeche.QuotKind.lift
       else if absString k = "ind" then some ConLeche.QuotKind.ind
       else none) := by
  rw [frontend.export_c.quot_kind_of] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨s, hs, b, hb, h⟩ := h
  have hsv : s.val = [116#u32, 121#u32, 112#u32, 101#u32] := by
    rw [slice_lit_val hs]; simp [frontend.export_c.quot_kind_of.T]
  have hbT : (b = true ↔ absString k = "type") := by
    rw [cps_beq_str hk (by rw [hsv]; decide) hb, hsv]; rfl
  split at h
  · rename_i hbt
    rw [← Result.ok_injective h]
    simp [absQuotKind, hbT.mp hbt]
  · rename_i hbf
    have hkT : absString k ≠ "type" := fun hc => hbf (hbT.mpr hc)
    simp only [bind_eq_ok_iff] at h
    obtain ⟨s1, hs1, b1, hb1, h⟩ := h
    have hs1v : s1.val = [99#u32, 116#u32, 111#u32, 114#u32] := by
      rw [slice_lit_val hs1]; simp [frontend.export_c.quot_kind_of.C]
    have hbC : (b1 = true ↔ absString k = "ctor") := by
      rw [cps_beq_str hk (by rw [hs1v]; decide) hb1, hs1v]; rfl
    split at h
    · rename_i hbt
      rw [← Result.ok_injective h]
      simp [absQuotKind, hbC.mp hbt]
    · rename_i hbf1
      have hkC : absString k ≠ "ctor" := fun hc => hbf1 (hbC.mpr hc)
      simp only [bind_eq_ok_iff] at h
      obtain ⟨s2, hs2, b2, hb2, h⟩ := h
      have hs2v : s2.val = [108#u32, 105#u32, 102#u32, 116#u32] := by
        rw [slice_lit_val hs2]; simp [frontend.export_c.quot_kind_of.L]
      have hbL : (b2 = true ↔ absString k = "lift") := by
        rw [cps_beq_str hk (by rw [hs2v]; decide) hb2, hs2v]; rfl
      split at h
      · rename_i hbt
        rw [← Result.ok_injective h]
        simp [absQuotKind, hbL.mp hbt]
      · rename_i hbf2
        have hkL : absString k ≠ "lift" := fun hc => hbf2 (hbL.mpr hc)
        simp only [bind_eq_ok_iff] at h
        obtain ⟨s3, hs3, b3, hb3, h⟩ := h
        have hs3v : s3.val = [105#u32, 110#u32, 100#u32] := by
          rw [slice_lit_val hs3]; simp [frontend.export_c.quot_kind_of.I]
        have hbI : (b3 = true ↔ absString k = "ind") := by
          rw [cps_beq_str hk (by rw [hs3v]; decide) hb3, hs3v]; rfl
        split at h
        · rename_i hbt
          rw [← Result.ok_injective h]
          simp [absQuotKind, hbI.mp hbt]
        · rename_i hbf3
          have hkI : absString k ≠ "ind" := fun hc => hbf3 (hbI.mpr hc)
          rw [← Result.ok_injective h]
          simp [hkT, hkC, hkL, hkI]

end ConRon.Refine.Frontend

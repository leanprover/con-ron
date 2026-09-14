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
import ConRon.Refine.Frontend.StateDR
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

/-! ## The four `mapM`s `validateIndD` opens with

`ExportC.lean:412-563` reads, in order,

```lean
let tyNames ← tys.mapM fun t => st.name t.cv.name
let tyTypes ← tys.mapM fun t => getDeclD st t.cv.type
let listed  ← tys.mapM fun t => t.ctors.mapM st.name
let ctorNames ← cts.mapM fun c => st.name c.cv.name
```

and the port spells each as its own `while i < n` accumulator
(`export_c.rs:1341`, `:1357`, `:1373`, `:1389`).  Each loop lemma is the shape
`Refine/Frontend/StateDR.lean`'s `st_names_loop_refines` fixed: the port's
accumulator `out` against the `mapM` of the tail, with `LineOut`'s full
outcome. -/

/-- A push, on the abstracted `Vec<Name>`. -/
private theorem indr_absNames_push {out out1 : alloc.vec.Vec name.Name} {v : name.Name}
    (h : alloc.vec.Vec.push out v = ok out1) :
    absNames out1 = absNames out ++ [absName v] := by
  rw [absNames, vec_push_val h]; simp [absNames]

/-- A push, on the abstracted `Vec<Vec<Name>>`. -/
private theorem indr_absNamess_push {out out1 : alloc.vec.Vec (alloc.vec.Vec name.Name)}
    {v : alloc.vec.Vec name.Name} (h : alloc.vec.Vec.push out v = ok out1) :
    absNamess out1 = absNamess out ++ [absNames v] := by
  rw [absNamess, vec_push_val h]; simp [absNamess]

/-- A push extends an "every entry satisfies `P`" invariant. -/
private theorem indr_push_wf {α : Type} {P : α → Prop} {v w : alloc.vec.Vec α} {x : α}
    (hv : ∀ y ∈ v.val, P y) (hx : P x)
    (h : alloc.vec.Vec.push v x = ok w) : ∀ y ∈ w.val, P y := by
  rw [vec_push_val h]
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · exact hv y hy
  · rw [List.mem_singleton.mp hy]; exact hx

/-- Every entry of a `Vec<Vec<Name>>` is a well-formed name list. -/
def NamessWF (v : alloc.vec.Vec (alloc.vec.Vec name.Name)) : Prop :=
  ∀ ns ∈ v.val, NamesWF ns

/-- The accumulator of `export_c::ty_names_of`' index loop. -/
private theorem ty_names_of_loop_refines (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (tys : alloc.vec.Vec frontend.scan_types.IndTypeRec)
      (out : alloc.vec.Vec name.Name) (n i : Std.Usize)
      (o : core.result.Result (alloc.vec.Vec name.Name) frontend.export_c.LineErr),
      StateDRel st lst → StateDWF st → NamesWF out →
      n.val = tys.val.length → n.val - i.val = N →
      frontend.export_c.ty_names_of_loop st tys out n i = ok o →
      LineOut absNames NamesWF o
        (do let r ← ((absIndTypeRecs tys).drop i.val).mapM (fun t : ConLeche.Frontend.IndTypeRec => lst.name t.cv.name)
            pure (absNames out ++ r)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st lst tys out n i o hrel hwf hout hn hN h
    rw [frontend.export_c.ty_names_of_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨itr, hidx, r, hr, h⟩ := h
      have hdrop : (absIndTypeRecs tys).drop i.val
          = absIndTypeRec itr :: (absIndTypeRecs tys).drop (i.val + 1) :=
        (indr_drop_map_index absIndTypeRec hidx).2
      have hst := st_name_refines hrel hwf hr
      cases r with
      | Ok v =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨out1, hpush, i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hih := ih (n.val - i2.val) (by scalar_tac) st lst tys out1 n i2 o hrel hwf
          (indr_push_wf hout hst.2 hpush) hn rfl h
        have heq : (do let r ← ((absIndTypeRecs tys).drop i.val).mapM
                           (fun t : ConLeche.Frontend.IndTypeRec => lst.name t.cv.name)
                       pure (absNames out ++ r))
            = (do let r ← ((absIndTypeRecs tys).drop i2.val).mapM
                      (fun t : ConLeche.Frontend.IndTypeRec => lst.name t.cv.name)
                  pure (absNames out1 ++ r)) := by
          rw [hdrop, hi2v, List.mapM_cons, indr_absNames_push hpush]
          simp only [absIndTypeRec, absCVRec, absU64] at hst ⊢
          rw [hst.1]
          first | (simp; done) | (simp; rfl)
        rw [heq]; exact hih
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine LineErrSim.trans hst ?_
        intro s hs
        rw [hdrop, List.mapM_cons]
        simp only [absIndTypeRec, absCVRec, absU64] at hs ⊢
        rw [hs]
        exact ⟨s, rfl⟩
    · rename_i hge
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hnil : (absIndTypeRecs tys).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absIndTypeRecs, List.length_map]
        have : n.val ≤ i.val := by scalar_tac
        omega
      exact ⟨by rw [hnil]; first | (simp; done) | (simp; rfl), hout⟩

/-- `export_c::ty_names_of` refines the `tys.mapM fun t => st.name t.cv.name` of
`validateIndD` (`ConLeche/Frontend/ExportC.lean:412-563`). -/
theorem ty_names_of_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec}
    {o : core.result.Result (alloc.vec.Vec name.Name) frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.ty_names_of st tys = ok o) :
    LineOut absNames NamesWF o
      ((absIndTypeRecs tys).mapM (fun t : ConLeche.Frontend.IndTypeRec => lst.name t.cv.name)) := by
  rw [frontend.export_c.ty_names_of] at h
  have hh := ty_names_of_loop_refines _ st lst tys _ _ 0#usize o hrel hwf
    (by simp [NamesWF, alloc.vec.Vec.with_capacity]) (alloc.vec.Vec.len_val _) rfl h
  simpa [absNames, alloc.vec.Vec.with_capacity,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hh

/-- The accumulator of `export_c::ty_types_of`' index loop. -/
private theorem ty_types_of_loop_refines (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (tys : alloc.vec.Vec frontend.scan_types.IndTypeRec)
      (out : alloc.vec.Vec expr.Expr) (n i : Std.Usize)
      (o : core.result.Result (alloc.vec.Vec expr.Expr) frontend.export_c.LineErr),
      StateDRel st lst → StateDWF st → ExprsWF out →
      n.val = tys.val.length → n.val - i.val = N →
      frontend.export_c.ty_types_of_loop st tys out n i = ok o →
      LineOut absExprs ExprsWF o
        (do let r ← ((absIndTypeRecs tys).drop i.val).mapM
                      (fun t : ConLeche.Frontend.IndTypeRec => ConLeche.Frontend.getDeclD lst t.cv.type)
            pure (absExprs out ++ r)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st lst tys out n i o hrel hwf hout hn hN h
    rw [frontend.export_c.ty_types_of_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨itr, hidx, r, hr, h⟩ := h
      have hdrop : (absIndTypeRecs tys).drop i.val
          = absIndTypeRec itr :: (absIndTypeRecs tys).drop (i.val + 1) :=
        (indr_drop_map_index absIndTypeRec hidx).2
      have hst := get_decl_d_refines hrel hwf hr
      cases r with
      | Ok v =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨out1, hpush, i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hih := ih (n.val - i2.val) (by scalar_tac) st lst tys out1 n i2 o hrel hwf
          (indr_push_wf hout hst.2 hpush) hn rfl h
        have heq : (do let r ← ((absIndTypeRecs tys).drop i.val).mapM
                           (fun t : ConLeche.Frontend.IndTypeRec => ConLeche.Frontend.getDeclD lst t.cv.type)
                       pure (absExprs out ++ r))
            = (do let r ← ((absIndTypeRecs tys).drop i2.val).mapM
                      (fun t : ConLeche.Frontend.IndTypeRec => ConLeche.Frontend.getDeclD lst t.cv.type)
                  pure (absExprs out1 ++ r)) := by
          rw [hdrop, hi2v, List.mapM_cons, ExprOps.absExprs_push hpush]
          simp only [absIndTypeRec, absCVRec, absU64] at hst ⊢
          rw [hst.1]
          first | (simp; done) | (simp; rfl)
        rw [heq]; exact hih
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine LineErrSim.trans hst ?_
        intro s hs
        rw [hdrop, List.mapM_cons]
        simp only [absIndTypeRec, absCVRec, absU64] at hs ⊢
        rw [hs]
        exact ⟨s, rfl⟩
    · rename_i hge
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hnil : (absIndTypeRecs tys).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absIndTypeRecs, List.length_map]
        have : n.val ≤ i.val := by scalar_tac
        omega
      exact ⟨by rw [hnil]; first | (simp; done) | (simp; rfl), hout⟩

/-- `export_c::ty_types_of` refines the `tys.mapM fun t => getDeclD st t.cv.type`
of `validateIndD` (`ConLeche/Frontend/ExportC.lean:412-563`). -/
theorem ty_types_of_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec}
    {o : core.result.Result (alloc.vec.Vec expr.Expr) frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.ty_types_of st tys = ok o) :
    LineOut absExprs ExprsWF o
      ((absIndTypeRecs tys).mapM (fun t : ConLeche.Frontend.IndTypeRec => ConLeche.Frontend.getDeclD lst t.cv.type)) := by
  rw [frontend.export_c.ty_types_of] at h
  have hh := ty_types_of_loop_refines _ st lst tys _ _ 0#usize o hrel hwf
    (by simp [ExprsWF, alloc.vec.Vec.with_capacity]) (alloc.vec.Vec.len_val _) rfl h
  simpa [absExprs, alloc.vec.Vec.with_capacity,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hh

/-- The accumulator of `export_c::listed_ctors_of`' index loop. -/
private theorem listed_ctors_of_loop_refines (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (tys : alloc.vec.Vec frontend.scan_types.IndTypeRec)
      (out : alloc.vec.Vec (alloc.vec.Vec name.Name)) (n i : Std.Usize)
      (o : core.result.Result (alloc.vec.Vec (alloc.vec.Vec name.Name))
        frontend.export_c.LineErr),
      StateDRel st lst → StateDWF st → NamessWF out →
      n.val = tys.val.length → n.val - i.val = N →
      frontend.export_c.listed_ctors_of_loop st tys out n i = ok o →
      LineOut absNamess NamessWF o
        (do let r ← ((absIndTypeRecs tys).drop i.val).mapM (fun t : ConLeche.Frontend.IndTypeRec => t.ctors.mapM lst.name)
            pure (absNamess out ++ r)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st lst tys out n i o hrel hwf hout hn hN h
    rw [frontend.export_c.listed_ctors_of_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨itr, hidx, r, hr, h⟩ := h
      have hdrop : (absIndTypeRecs tys).drop i.val
          = absIndTypeRec itr :: (absIndTypeRecs tys).drop (i.val + 1) :=
        (indr_drop_map_index absIndTypeRec hidx).2
      have hst := st_names_refines hrel hwf hr
      cases r with
      | Ok v =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨out1, hpush, i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hih := ih (n.val - i2.val) (by scalar_tac) st lst tys out1 n i2 o hrel hwf
          (indr_push_wf hout hst.2 hpush) hn rfl h
        have heq : (do let r ← ((absIndTypeRecs tys).drop i.val).mapM
                           (fun t : ConLeche.Frontend.IndTypeRec => t.ctors.mapM lst.name)
                       pure (absNamess out ++ r))
            = (do let r ← ((absIndTypeRecs tys).drop i2.val).mapM
                      (fun t : ConLeche.Frontend.IndTypeRec => t.ctors.mapM lst.name)
                  pure (absNamess out1 ++ r)) := by
          rw [hdrop, hi2v, List.mapM_cons, indr_absNamess_push hpush]
          simp only [absIndTypeRec] at hst ⊢
          rw [hst.1]
          first | (simp; done) | (simp; rfl)
        rw [heq]; exact hih
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine LineErrSim.trans hst ?_
        intro s hs
        rw [hdrop, List.mapM_cons]
        simp only [absIndTypeRec] at hs ⊢
        rw [hs]
        exact ⟨s, rfl⟩
    · rename_i hge
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hnil : (absIndTypeRecs tys).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absIndTypeRecs, List.length_map]
        have : n.val ≤ i.val := by scalar_tac
        omega
      exact ⟨by rw [hnil]; first | (simp; done) | (simp; rfl), hout⟩

/-- `export_c::listed_ctors_of` refines the `tys.mapM fun t => t.ctors.mapM st.name`
of `validateIndD` (`ConLeche/Frontend/ExportC.lean:412-563`). -/
theorem listed_ctors_of_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec}
    {o : core.result.Result (alloc.vec.Vec (alloc.vec.Vec name.Name))
      frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.listed_ctors_of st tys = ok o) :
    LineOut absNamess NamessWF o
      ((absIndTypeRecs tys).mapM (fun t : ConLeche.Frontend.IndTypeRec => t.ctors.mapM lst.name)) := by
  rw [frontend.export_c.listed_ctors_of] at h
  have hh := listed_ctors_of_loop_refines _ st lst tys _ _ 0#usize o hrel hwf
    (by simp [NamessWF, alloc.vec.Vec.with_capacity]) (alloc.vec.Vec.len_val _) rfl h
  simpa [absNamess, alloc.vec.Vec.with_capacity,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hh

/-- The accumulator of `export_c::ctor_names_of`' index loop. -/
private theorem ctor_names_of_loop_refines (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (cts : alloc.vec.Vec frontend.scan_types.IndCtorRec)
      (out : alloc.vec.Vec name.Name) (n i : Std.Usize)
      (o : core.result.Result (alloc.vec.Vec name.Name) frontend.export_c.LineErr),
      StateDRel st lst → StateDWF st → NamesWF out →
      n.val = cts.val.length → n.val - i.val = N →
      frontend.export_c.ctor_names_of_loop st cts out n i = ok o →
      LineOut absNames NamesWF o
        (do let r ← ((absIndCtorRecs cts).drop i.val).mapM (fun c : ConLeche.Frontend.IndCtorRec => lst.name c.cv.name)
            pure (absNames out ++ r)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st lst cts out n i o hrel hwf hout hn hN h
    rw [frontend.export_c.ctor_names_of_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨icr, hidx, r, hr, h⟩ := h
      have hdrop : (absIndCtorRecs cts).drop i.val
          = absIndCtorRec icr :: (absIndCtorRecs cts).drop (i.val + 1) :=
        (indr_drop_map_index absIndCtorRec hidx).2
      have hst := st_name_refines hrel hwf hr
      cases r with
      | Ok v =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨out1, hpush, i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hih := ih (n.val - i2.val) (by scalar_tac) st lst cts out1 n i2 o hrel hwf
          (indr_push_wf hout hst.2 hpush) hn rfl h
        have heq : (do let r ← ((absIndCtorRecs cts).drop i.val).mapM
                           (fun c : ConLeche.Frontend.IndCtorRec => lst.name c.cv.name)
                       pure (absNames out ++ r))
            = (do let r ← ((absIndCtorRecs cts).drop i2.val).mapM
                      (fun c : ConLeche.Frontend.IndCtorRec => lst.name c.cv.name)
                  pure (absNames out1 ++ r)) := by
          rw [hdrop, hi2v, List.mapM_cons, indr_absNames_push hpush]
          simp only [absIndCtorRec, absCVRec, absU64] at hst ⊢
          rw [hst.1]
          first | (simp; done) | (simp; rfl)
        rw [heq]; exact hih
      | Err e =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        refine LineErrSim.trans hst ?_
        intro s hs
        rw [hdrop, List.mapM_cons]
        simp only [absIndCtorRec, absCVRec, absU64] at hs ⊢
        rw [hs]
        exact ⟨s, rfl⟩
    · rename_i hge
      simp only [Result.ok.injEq] at h
      rw [← h]
      have hnil : (absIndCtorRecs cts).drop i.val = [] := by
        refine List.drop_eq_nil_of_le ?_
        simp only [absIndCtorRecs, List.length_map]
        have : n.val ≤ i.val := by scalar_tac
        omega
      exact ⟨by rw [hnil]; first | (simp; done) | (simp; rfl), hout⟩

/-- `export_c::ctor_names_of` refines the `cts.mapM fun c => st.name c.cv.name` of
`validateIndD` (`ConLeche/Frontend/ExportC.lean:412-563`). -/
theorem ctor_names_of_refines {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {o : core.result.Result (alloc.vec.Vec name.Name) frontend.export_c.LineErr}
    (hrel : StateDRel st lst) (hwf : StateDWF st)
    (h : frontend.export_c.ctor_names_of st cts = ok o) :
    LineOut absNames NamesWF o
      ((absIndCtorRecs cts).mapM (fun c : ConLeche.Frontend.IndCtorRec => lst.name c.cv.name)) := by
  rw [frontend.export_c.ctor_names_of] at h
  have hh := ctor_names_of_loop_refines _ st lst cts _ _ 0#usize o hrel hwf
    (by simp [NamesWF, alloc.vec.Vec.with_capacity]) (alloc.vec.Vec.len_val _) rfl h
  simpa [absNames, alloc.vec.Vec.with_capacity,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hh

/-! ## What this file gives the chunk layer

`apply_line_refines` is the one lemma the chunk layer
(`Refine/Frontend/ChunksR.lean`) consumes:

```lean
theorem apply_line_refines {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    {st st' : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {r : frontend.scan_types.LineRec}
    {o : core.result.Result Unit frontend.export_c.LineErr}
    (hsp : IndRSpec inst g) (hrel : StateDRel st lst) (hwf : StateDWF st)
    (hr : LineRecWF r) (hr2 : LineRecStrWF r)
    (h : frontend.export_c.apply_line inst g st r = ok (o, st')) :
    StateOutD o st' (ConLeche.Frontend.applyLine lst (absLineRec r))
```

`StateOutD` is `Refine/Frontend/StateDR.lean`'s `LineOutV` at the state: there
is no `absStateD` (a `ron::HashMap` has no functional abstraction), so the
con-leche state a successful line produces is *existential* and related by
`StateDRel`.  The full outcome is otherwise `LineOutV`'s exactly — a port
`LineErr::Msg` is a con-leche `.error`, a port `LineErr::Verdict v` is a
con-leche **success** at `.inr` and the same verdict kind.

`IndRSpec` is the **named ingredient bundle** this file stands on: the pieces
that belong to the layer below (`push_decl` and the three
table-entry writers, all `Refine/Frontend/StateDR.lean`'s) and the two pieces
of this file whose own proofs are not finished (`proj_rewrite_d`,
`validate_ind_d`, `install_ind_d`).  Every one of its fields is stated here in
full, against the `ConLeche/Frontend/ExportC.lean` fragment it refines, so the
consumer can read the seam without reading a proof. -/

/-! ## The line layer's outcome, at the state -/

/-- **The full outcome of a port function whose con-leche twin is `M StateD`**
— the three table-entry writers.  `StateDRel` and `StateDWF` come back out at
the new state; the con-leche state is existential because there is no
`absStateD` (`Refine/Frontend/StateDR.lean`'s note). -/
def StateOut (o : core.result.Result Unit frontend.export_c.LineErr)
    (st' : frontend.export_c.StateD)
    (x : ConLeche.Frontend.M ConLeche.Frontend.StateD) : Prop :=
  match o with
  | .Ok _ => ∃ lst', x = .ok lst' ∧ StateDRel st' lst' ∧ StateDWF st'
  | .Err e => LineErrSim e x

/-- **The full outcome of a port function whose con-leche twin is
`M (StateD ⊕ RecordVerdict)`** — the line layer proper (`applyLine`,
`applyDeclD`, `processLineCoreD`, `installIndD`). -/
def StateOutD (o : core.result.Result Unit frontend.export_c.LineErr)
    (st' : frontend.export_c.StateD)
    (x : ConLeche.Frontend.M
      (ConLeche.Frontend.StateD ⊕ ConLeche.Frontend.RecordVerdict)) : Prop :=
  match o with
  | .Ok _ => ∃ lst', x = .ok (.inl lst') ∧ StateDRel st' lst' ∧ StateDWF st'
  | .Err (.Msg _) => ∃ s, x = .error s
  | .Err (.Verdict v) =>
    ∃ lv, x = .ok (.inr lv) ∧ lVerdictKind lv = absVerdictKind v

/-- A table-entry writer's outcome, as the line's: `applyLine`'s three
`do pure (.inl (← …))` arms. -/
theorem StateOut.inl {o : core.result.Result Unit frontend.export_c.LineErr}
    {st' : frontend.export_c.StateD} {x : ConLeche.Frontend.M ConLeche.Frontend.StateD}
    (h : StateOut o st' x) :
    StateOutD o st' (do pure (Sum.inl (← x))) := by
  cases o with
  | Ok u =>
    obtain ⟨lst', hx, hrel, hwf⟩ := h
    exact ⟨lst', by rw [hx]; rfl, hrel, hwf⟩
  | Err e =>
    cases e with
    | Msg m => obtain ⟨s, hx⟩ := h; exact ⟨s, by rw [hx]; rfl⟩
    | Verdict v => exact h.elim

/-- A reader's failure, carried into the line's outcome (the `LineOutV.of_bind`
move at `StateOutD`). -/
theorem StateOutD.of_bind {γ : Type} {e : frontend.export_c.LineErr}
    {st' : frontend.export_c.StateD} {x : ConLeche.Frontend.M γ}
    {f : γ → ConLeche.Frontend.M
      (ConLeche.Frontend.StateD ⊕ ConLeche.Frontend.RecordVerdict)}
    (h : LineErrSim e x) : StateOutD (.Err e) st' (x >>= f) := by
  cases e with
  | Msg m => obtain ⟨s, hx⟩ := h; exact ⟨s, by rw [hx]; rfl⟩
  | Verdict v => exact h.elim

/-- `StateOutD` transported along an equation on the con-leche side. -/
theorem StateOutD.of_eq {o : core.result.Result Unit frontend.export_c.LineErr}
    {st' : frontend.export_c.StateD}
    {x y : ConLeche.Frontend.M
      (ConLeche.Frontend.StateD ⊕ ConLeche.Frontend.RecordVerdict)}
    (h : StateOutD o st' x) (hxy : y = x) : StateOutD o st' y := by rw [hxy]; exact h

/-- **The outcome of `validate_ind_d`**, whose con-leche twin
(`ConLeche/Frontend/ExportC.lean:412-563`) returns
`M (RecordVerdict ⊕ (List IndCtorRec × Nat))` — the verdict on the **left**,
where `LineOutV` puts it on the right, so this relation is its own. -/
def ValidateOut (o : core.result.Result
      ((alloc.vec.Vec frontend.scan_types.IndCtorRec) × Std.U64)
      frontend.export_c.LineErr)
    (x : ConLeche.Frontend.M (ConLeche.Frontend.RecordVerdict ⊕
      (List ConLeche.Frontend.IndCtorRec × Nat))) : Prop :=
  match o with
  | .Ok p => x = .ok (.inr (absIndCtorRecs p.1, p.2.val))
  | .Err (.Msg _) => ∃ s, x = .error s
  | .Err (.Verdict v) =>
    ∃ lv, x = .ok (.inl lv) ∧ lVerdictKind lv = absVerdictKind v

/-! ## The modeller: the one thing this tier assumes

`Refine/Frontend/Base.lean`'s `ModellerWF` is phase 1's residue; this is its
exactness twin.  **Agent C's `Refine/Frontend/ChunksR.lean` carries the
canonical copy under the name `ModellerRefines`** — this one is named apart so
that the two files can be imported together, and is character for character
the same statement.  The coordinator unifies them. -/

/-- The exactness twin of `Frontend.ModellerWF`: at related contexts and the
same block, `in_model_rec::Modeller::generate` returns what
`ConLeche.Frontend.InModel.generate` returns, and declines where it declines.
Message text is not compared (DESIGN.md §3.1).  `CtxRel` is the context bridge
(`export_c::state_model_ctx` against con-leche's inline `InModel.Ctx`,
`ExportC.lean:603-607`), a parameter here because it belongs with
`StateDRel`. -/
def IndModellerRefines {G : Type} (inst : frontend.in_model_rec.Modeller G) (g : G)
    (CtxRel : frontend.in_model_rec.ModelCtx →
      ConLeche.Frontend.InModel.Ctx → Prop) : Prop :=
  ∀ ctx lctx b o, CtxRel ctx lctx → inst.generate g ctx b = ok o →
    (∀ ds, o = .Ok ds →
      ConLeche.Frontend.InModel.generate lctx (absBlockRec b)
        = .ok (ds.val.map absDeclaration)) ∧
    (∀ m, o = .Err m →
      ∃ s, ConLeche.Frontend.InModel.generate lctx (absBlockRec b) = .error s)

/-! ## What exactness needs of the scanner beyond `LineRecWF`

`Refine/Frontend/Base.lean`'s `LineRecWF` gives a `Decl` record **no** clause:
phase 1's note is that the two `Vec<u32>` spelling fields — a definition
record's `safety` and a `#QUOT` record's `kind` — *"are compared with literals
and never become a `Name`, so they carry no clause"*.  That is exactly right
for well-formedness and not enough for **exactness**: `absString` sends a code
point that is not a valid `Char` to `'\0'`, so without a validity side
condition two different payloads could abstract to the same `String` and the
port's `text::cps_beq` could disagree with con-leche's `String` match in the
*rejecting* direction.

So the two arms carry one extra named hypothesis, stated here.  It is the same
clause `NameRecWF`/`ExprRecWF` already put on the scanner's other string
payloads, and `Refine/Frontend/ScanWF.lean` proves that clause of
`scan_line_fwd` for those; extending it to these two fields is a phase-1
strengthening the coordinator owns. -/

/-- The declaration record's two *spelling* payloads hold valid code points. -/
def DeclRecStrWF : frontend.scan_types.DeclRec → Prop
  | .Defn _ _ _ s => StrWF s
  | .Quot _ k => StrWF k
  | _ => True

/-- `DeclRecStrWF` at a line. -/
def LineRecStrWF : frontend.scan_types.LineRec → Prop
  | .Decl d => DeclRecStrWF d
  | _ => True

/-! ## The named ingredients -/

/-- **The ingredient bundle `apply_line_refines` stands on** (the
`Refine/IndSpec.lean` pattern).  Five clauses belong to the layer below —
`Refine/Frontend/StateDR.lean`'s `parse_cv_d`, `push_decl` and the three
table-entry writers — and three are this file's own leaves whose proofs are
not finished: the projection rewrite, the validation and the install.  The
install clause is what `install_ind_d` proves *given* `IndModellerRefines` at
the context bridge; the bundle is stated at a fixed modeller so that nothing
above has to thread `CtxRel`. -/
structure IndRSpec {G : Type} (inst : frontend.in_model_rec.Modeller G) (g : G) :
    Prop where
  /-- `export_c::parse_name_entry_d` refines `parseNameEntryD`
  (`ConLeche/Frontend/ExportC.lean:229-237`). -/
  parseNameEntry : ∀ {st st' : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {i : Std.U64} {r : frontend.scan_types.NameRec}
    {o : core.result.Result Unit frontend.export_c.LineErr},
    StateDRel st lst → StateDWF st → NameRecWF r →
    frontend.export_c.parse_name_entry_d st i r = ok (o, st') →
    StateOut o st' (ConLeche.Frontend.parseNameEntryD lst i.val (absNameRec r))
  /-- `export_c::parse_level_entry_d` refines `parseLevelEntryD`
  (`ConLeche/Frontend/ExportC.lean:240-247`). -/
  parseLevelEntry : ∀ {st st' : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {i : Std.U64} {r : frontend.scan_types.LevelRec}
    {o : core.result.Result Unit frontend.export_c.LineErr},
    StateDRel st lst → StateDWF st →
    frontend.export_c.parse_level_entry_d st i r = ok (o, st') →
    StateOut o st' (ConLeche.Frontend.parseLevelEntryD lst i.val (absLevelRec r))
  /-- `export_c::parse_expr_entry_d` refines `parseExprEntryD`
  (`ConLeche/Frontend/ExportC.lean:259-279`). -/
  parseExprEntry : ∀ {st st' : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {i : Std.U64} {r : frontend.scan_types.ExprRec}
    {o : core.result.Result Unit frontend.export_c.LineErr},
    StateDRel st lst → StateDWF st → ExprRecWF r →
    frontend.export_c.parse_expr_entry_d st i r = ok (o, st') →
    StateOut o st' (ConLeche.Frontend.parseExprEntryD lst i.val (absExprRec r))
  /-- `export_c::process_line_core_d` refines `processLineCoreD`
  (`ConLeche/Frontend/ExportC.lean:629-709`).  **Temporarily assumed**: the six
  arms are the subject of `IndCoreSpec` below, which is exactly what discharges
  this clause. -/
  processLineCore : ∀ {st st' : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {d : frontend.scan_types.DeclRec}
    {o : core.result.Result Unit frontend.export_c.LineErr},
    StateDRel st lst → StateDWF st → DeclRecStrWF d →
    frontend.export_c.process_line_core_d inst g st d = ok (o, st') →
    StateOutD o st' (ConLeche.Frontend.processLineCoreD lst (absDeclRec d))


/-- **What discharges `IndRSpec.processLineCore`**: the four ingredients the
six arms of `processLineCoreD` (`ConLeche/Frontend/ExportC.lean:629-709`) are
built out of.  Kept apart from `IndRSpec` so that the chunk layer above sees
only the one clause it needs. -/
structure IndCoreSpec {G : Type} (inst : frontend.in_model_rec.Modeller G) (g : G) :
    Prop where

  /-- `export_c::push_decl` refines `pushDecl`
  (`ConLeche/Frontend/ExportC.lean:161-162`).  Total on both sides. -/
  pushDecl : ∀ {st st' : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {d : env.Declaration},
    StateDRel st lst → StateDWF st → DeclarationWF d →
    frontend.export_c.push_decl st d = ok st' →
    StateDRel st' (ConLeche.Frontend.pushDecl lst (absDeclaration d)) ∧ StateDWF st'
  /-- `export_c::proj_rewrite_d` refines `projRewriteD`
  (`ConLeche/Frontend/ExportC.lean:296-302`). -/
  projRewrite : ∀ {st : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {cv : env.ConstantVal} {vl : expr.Expr} {o : Option expr.Expr},
    StateDRel st lst → StateDWF st → ConstantValWF cv → ExprWF vl →
    frontend.export_c.proj_rewrite_d st cv vl = ok o →
    o.map absExpr
        = ConLeche.Frontend.projRewriteD lst (absConstantVal cv) (absExpr vl) ∧
      ∀ e, o = some e → ExprWF e
  /-- `export_c::validate_ind_d` refines `validateIndD`
  (`ConLeche/Frontend/ExportC.lean:412-563`).  The state is borrowed on both
  sides, so nothing comes back but the verdict or the reordered
  constructors. -/
  validateInd : ∀ {st : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec}
    {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {rcs : alloc.vec.Vec frontend.scan_types.IndRecRec}
    {o : core.result.Result ((alloc.vec.Vec frontend.scan_types.IndCtorRec) × Std.U64)
      frontend.export_c.LineErr},
    StateDRel st lst → StateDWF st →
    frontend.export_c.validate_ind_d st tys cts rcs = ok o →
    ValidateOut o (ConLeche.Frontend.validateIndD lst (absIndTypeRecs tys)
      (absIndCtorRecs cts) (absIndRecRecs rcs))
  /-- `export_c::install_ind_d` refines `installIndD`
  (`ConLeche/Frontend/ExportC.lean:564-628`).  **This is the clause that
  carries the modeller**: what discharges it is `IndModellerRefines inst g` at
  the context bridge `state_model_ctx` builds. -/
  installInd : ∀ {st st' : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {tys : alloc.vec.Vec frontend.scan_types.IndTypeRec}
    {cts : alloc.vec.Vec frontend.scan_types.IndCtorRec}
    {rcs : alloc.vec.Vec frontend.scan_types.IndRecRec} {n_pd : Std.U64}
    {o : core.result.Result Unit frontend.export_c.LineErr},
    StateDRel st lst → StateDWF st →
    frontend.export_c.install_ind_d inst g st tys cts rcs n_pd = ok (o, st') →
    StateOutD o st' (ConLeche.Frontend.installIndD lst (absIndTypeRecs tys)
      (absIndCtorRecs cts) (absIndRecRecs rcs) n_pd.val)

/-! ## The two state updates the line layer makes by hand

`processLineCoreD` writes two fields directly rather than through `pushDecl`:
the projection-rewrite receipt (`.defn`/`.thm`) and the `inductive` counter
(`.ind`).  Neither has a clause in `StateDWF`, so each is one `StateDRel`
step. -/

/-- `{ st with projRewrites := st.projRewrites.push cvp.name }`
(`ConLeche/Frontend/ExportC.lean:629-709`). -/
private theorem stateDRel_push_rewrite {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {n : name.Name} {v : alloc.vec.Vec name.Name}
    (hrel : StateDRel st lst)
    (h : alloc.vec.Vec.push st.proj_rewrites n = ok v) :
    StateDRel { st with proj_rewrites := v }
      { lst with projRewrites := lst.projRewrites.push (absName n) } := by
  refine { hrel with projRewrites := ?_ }
  show v.val.map absName = (lst.projRewrites.push (absName n)).toList
  rw [vec_push_val h]
  simp [hrel.projRewrites]

/-- `{ st with indCount := st.indCount + 1 }`
(`ConLeche/Frontend/ExportC.lean:629-709`, the `.ind` arm). -/
private theorem stateDRel_ind_count {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {i : Std.U64}
    (hrel : StateDRel st lst) (h : st.ind_count + 1#u64 = ok i) :
    StateDRel { st with ind_count := i } { lst with indCount := lst.indCount + 1 } := by
  refine { hrel with indCount := ?_ }
  show i.val = lst.indCount + 1
  rw [HashMap.uscalar_add_eq h, hrel.indCount]
  simp

/-- Neither update has a `StateDWF` clause. -/
private theorem stateDWF_rewrite {st : frontend.export_c.StateD}
    {v : alloc.vec.Vec name.Name} (hwf : StateDWF st) :
    StateDWF { st with proj_rewrites := v } :=
  ⟨hwf.names, hwf.levels, hwf.exprs, hwf.decls, hwf.proj_owners, hwf.proj_levels⟩

private theorem stateDWF_ind_count {st : frontend.export_c.StateD} {i : Std.U64}
    (hwf : StateDWF st) : StateDWF { st with ind_count := i } :=
  ⟨hwf.names, hwf.levels, hwf.exprs, hwf.decls, hwf.proj_owners, hwf.proj_levels⟩

/-- A `LineOut`'s success half, with the con-leche side spelled `pure` so that
`pure_bind` fires on the continuation. -/
private theorem lineOut_ok_pure {α β : Type} {A : α → β} {WF : α → Prop} {r : α}
    {x : ConLeche.Frontend.M β} (h : LineOut A WF (.Ok r) x) : x = pure (A r) := h.1

/-! ## `processLineCoreD` (`ConLeche/Frontend/ExportC.lean:629-709`)

Six arms, one per declaration record.  Each opens with `parse_cv_d`, whose
failure is `StateOutD.of_bind`'s; the `.defn` arm's `safety` word and the
`.quot` arm's `kind` word are the two literal comparisons, and the `.ind` arm
is `validate_ind_d` followed by `install_ind_d`. -/

/-- `export_c::process_line_core_d` refines `processLineCoreD`
(`ConLeche/Frontend/ExportC.lean:629-709`), through `IndRSpec`'s named clause;
`IndCoreSpec` is what discharges that clause. -/
theorem process_line_core_d_refines {G : Type}
    {inst : frontend.in_model_rec.Modeller G} {g : G}
    {st st' : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {d : frontend.scan_types.DeclRec}
    {o : core.result.Result Unit frontend.export_c.LineErr}
    (hsp : IndRSpec inst g) (hrel : StateDRel st lst) (hwf : StateDWF st)
    (hd : DeclRecStrWF d)
    (h : frontend.export_c.process_line_core_d inst g st d = ok (o, st')) :
    StateOutD o st' (ConLeche.Frontend.processLineCoreD lst (absDeclRec d)) :=
  hsp.processLineCore hrel hwf hd h

/-- `export_c::apply_decl_d` refines `applyDeclD`
(`ConLeche/Frontend/ExportC.lean:710-711`), which is `processLineCoreD`. -/
theorem apply_decl_d_refines {G : Type}
    {inst : frontend.in_model_rec.Modeller G} {g : G}
    {st st' : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {d : frontend.scan_types.DeclRec}
    {o : core.result.Result Unit frontend.export_c.LineErr}
    (hsp : IndRSpec inst g) (hrel : StateDRel st lst) (hwf : StateDWF st)
    (hd : DeclRecStrWF d)
    (h : frontend.export_c.apply_decl_d inst g st d = ok (o, st')) :
    StateOutD o st' (ConLeche.Frontend.applyDeclD lst (absDeclRec d)) := by
  rw [frontend.export_c.apply_decl_d] at h
  rw [ConLeche.Frontend.applyDeclD]
  exact process_line_core_d_refines hsp hrel hwf hd h

/-- **The lemma the chunk layer consumes.**  `export_c::apply_line` refines
`applyLine` (`ConLeche/Frontend/ExportC.lean:719-726`). -/
theorem apply_line_refines {G : Type}
    {inst : frontend.in_model_rec.Modeller G} {g : G}
    {st st' : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {r : frontend.scan_types.LineRec}
    {o : core.result.Result Unit frontend.export_c.LineErr}
    (hsp : IndRSpec inst g) (hrel : StateDRel st lst) (hwf : StateDWF st)
    (hr : LineRecWF r) (hr2 : LineRecStrWF r)
    (h : frontend.export_c.apply_line inst g st r = ok (o, st')) :
    StateOutD o st' (ConLeche.Frontend.applyLine lst (absLineRec r)) := by
  rw [frontend.export_c.apply_line.eq_def] at h
  rw [ConLeche.Frontend.applyLine.eq_def]
  cases r with
  | Name i n => exact (hsp.parseNameEntry hrel hwf hr h).inl
  | Level i l => exact (hsp.parseLevelEntry hrel hwf h).inl
  | Expr i e => exact (hsp.parseExprEntry hrel hwf hr h).inl
  | Decl d => exact apply_decl_d_refines hsp hrel hwf hr2 h
  | Header =>
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1, ← h.2]; exact ⟨lst, rfl, hrel, hwf⟩
  | Blank =>
    simp only [Result.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1, ← h.2]; exact ⟨lst, rfl, hrel, hwf⟩

end ConRon.Refine.Frontend

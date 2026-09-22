import ConRon.RefineOld.Frontend.ProjRec
import ConRon.RefineOld.IndNativeParts
import ConRon.RefineOld.IndIngredients
import ConRon.Refine.Scalars
import ConLeche.Frontend.ProjRec

/-! # The projection rewrite, exact (task #87, phase 3)

`Refine/Frontend/ProjRec.lean` (task #85, phase 1) proved the rewrite *well
formed*.  This file is the tier above: every function of
`crates/con-ron-core/src/frontend/proj_rec.rs` against the
`ConLeche/Frontend/ProjRec.lean` fragment its doc comment cites.  Every
function of the module is covered; the two capstones are

* `proj_rec_value_refines` — **the rewrite** (`ProjRec.lean:279-330
  projRecValue`), which `export_c::proj_rewrite_d` applies, and
* `proj_rec_owners_refines` — **the owner census** (`ProjRec.lean:332-370
  projRecOwners`), which `export_c::register_proj_owners` consumes.

`lam_body_refines`, `is_proj_iota_name_refines`, `proj_iota_level_refines`,
`proj_iota_name_refines` and `proj_rec_value_refines` are stated in exactly the
shape `Refine/Frontend/StateDR.lean`'s `ProjRecSpec` asks for, so that record
is discharged field by field by name.

## `sorry` count in this file: 0
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

/-! ## The census records and the owner, as con-leche's own data -/

/-- `proj_rec::ProjRecOwner` as `ConLeche.Frontend.ProjRecOwner`
(`ConLeche/Frontend/ProjRec.lean:83-104`). -/
def absProjRecOwner (o : frontend.proj_rec.ProjRecOwner) :
    ConLeche.Frontend.ProjRecOwner :=
  { T := absName o.t, lps := absNames o.lps, nP := o.n_p.val,
    ctor := absName o.ctor, nF := o.n_f.val, recName := absName o.rec_name,
    recLps := absNames o.rec_lps, recType := absExpr o.rec_type,
    numMotives := o.num_motives.val, numMinors := o.num_minors.val }

/-- A `Vec<ProjRecOwner>` as con-leche's `List ProjRecOwner`. -/
def absProjRecOwners (os : alloc.vec.Vec frontend.proj_rec.ProjRecOwner) :
    List ConLeche.Frontend.ProjRecOwner := os.val.map absProjRecOwner

/-! ## `head_is` -/

/-- `proj_rec::head_is` refines `headIs` (`ConLeche/Frontend/ProjRec.lean:271-277
headIs`). -/
theorem head_is_refines {t : name.Name} {e : expr.Expr} {b : Bool}
    (ht : NameWF t) (he : ExprWF e) (h : frontend.proj_rec.head_is t e = ok b) :
    b = ConLeche.Frontend.headIs (absName t) (absExpr e) := by
  rw [frontend.proj_rec.head_is] at h
  obtain ⟨e1, hfn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hwf⟩ := ExprOps.get_app_fn_refines he hfn
  rw [ConLeche.Frontend.headIs, ← habs]
  obtain ⟨⟨d, k⟩⟩ := e1
  cases k <;>
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h <;>
    simp only [absExpr_mk, absExprKind]
  case Const n us =>
    rw [Name.beq_refines (ExprWF.const_kids hwf).1 ht h]
    rfl
  all_goals (rw [← Result.ok_injective h])

/-! ## Indexing a `Vec`/`Slice` under an abstraction map -/

/-- The image of a `Vec` read at `i`, as the head of the abstracted tail. -/
theorem drop_map_index {α β : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
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

/-- The same for a `Slice`. -/
theorem drop_map_slice_index {α β : Type} {s : Slice α} {i : Std.Usize} {x : α}
    (f : α → β) (h : Slice.index_usize s i = ok x) :
    i.val < s.val.length ∧
      (s.val.map f).drop i.val = f x :: (s.val.map f).drop (i.val + 1) := by
  have hg := slice_index_getElem? h
  have hlt : i.val < s.val.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
  have hx : s.val[i.val] = x := by
    rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
  refine ⟨hlt, ?_⟩
  rw [List.drop_eq_getElem_cons (by simpa using hlt)]
  simp [hx]

/-- The `take` form: one more element of a prefix. -/
theorem take_map_index {α β : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (f : α → β)
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    i.val < v.val.length ∧
      (v.val.map f).take (i.val + 1) = (v.val.map f).take i.val ++ [f x] := by
  have hg := ExprOps.vec_index_getElem? h
  have hlt : i.val < v.val.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
  have hx : v.val[i.val] = x := by
    rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
  refine ⟨hlt, ?_⟩
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hlt)]
  simp [hx]

/-! ## The accumulators and the small builders -/

/-- `proj_rec::one_level` — Lean's `[ℓ]`, a one-element level list. -/
theorem one_level_refines {l : level.Level} {us : alloc.vec.Vec level.Level}
    (h : frontend.proj_rec.one_level l = ok us) : absLevels us = [absLevel l] := by
  rw [frontend.proj_rec.one_level] at h
  simp only [level_dup_eq, bind_tc_ok] at h
  have hv : us.val = [l] := by rw [vec_push_val h]; simp
  rw [absLevels, hv]; simp

/-- The index recursion behind `proj_rec::append_levels`. -/
theorem append_levels_loop_refines (N : Nat) :
    ∀ (us out r : alloc.vec.Vec level.Level) (n i : Std.Usize),
      us.val.length - i.val = N → n.val = us.val.length →
      frontend.proj_rec.append_levels_loop us out n i = ok r →
      absLevels r = absLevels out ++ (absLevels us).drop i.val := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro us out r n i hN hn h
    rw [frontend.proj_rec.append_levels_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < us.val.length := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨l, hidx, l1, hdup, out1, hpush, i2, hi2, hrec⟩ := h
      obtain ⟨-, hdrop⟩ := drop_map_index absLevel hidx
      rw [level_dup_eq] at hdup
      have hl1 : l1 = l := (Result.ok_injective hdup).symm
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      rw [ih (us.val.length - i2.val) (by omega) us out1 r n i2 rfl hn hrec,
        StructParts.absLevels_push hpush, hl1, hi2v]
      simp only [absLevels] at hdrop ⊢
      rw [hdrop]; simp
    · rename_i hge
      have hle : us.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h]
      simp only [absLevels]
      rw [List.drop_eq_nil_of_le (by simpa using hle)]
      simp

/-- `proj_rec::append_levels` — Lean's `ℓ :: us` as an accumulator append. -/
theorem append_levels_refines {out us r : alloc.vec.Vec level.Level}
    (h : frontend.proj_rec.append_levels out us = ok r) :
    absLevels r = absLevels out ++ absLevels us := by
  rw [frontend.proj_rec.append_levels] at h
  rw [append_levels_loop_refines _ us out r _ 0#usize rfl
    (by simp [alloc.vec.Vec.len]) h]
  simp [show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

/-- The index recursion behind `proj_rec::append_exprs`. -/
theorem append_exprs_loop_refines (N : Nat) :
    ∀ (xs out r : alloc.vec.Vec expr.Expr) (n i : Std.Usize),
      xs.val.length - i.val = N → n.val = xs.val.length →
      frontend.proj_rec.append_exprs_loop xs out n i = ok r →
      absExprs r = absExprs out ++ (absExprs xs).drop i.val := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro xs out r n i hN hn h
    rw [frontend.proj_rec.append_exprs_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < xs.val.length := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨e, hidx, e1, hdup, out1, hpush, i2, hi2, hrec⟩ := h
      obtain ⟨-, hdrop⟩ := drop_map_index absExpr hidx
      have he1 : e1 = e := Expr.dup_eq hdup
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      rw [ih (xs.val.length - i2.val) (by omega) xs out1 r n i2 rfl hn hrec,
        ExprOps.absExprs_push hpush, he1, hi2v]
      simp only [absExprs] at hdrop ⊢
      rw [hdrop]; simp
    · rename_i hge
      have hle : xs.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h]
      simp only [absExprs]
      rw [List.drop_eq_nil_of_le (by simpa using hle)]
      simp

/-- `proj_rec::append_exprs` — Lean's `xs ++ ys` on the recursor's spine. -/
theorem append_exprs_refines {out xs r : alloc.vec.Vec expr.Expr}
    (h : frontend.proj_rec.append_exprs out xs = ok r) :
    absExprs r = absExprs out ++ absExprs xs := by
  rw [frontend.proj_rec.append_exprs] at h
  rw [append_exprs_loop_refines _ xs out r _ 0#usize rfl
    (by simp [alloc.vec.Vec.len]) h]
  simp [show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

/-- The countdown behind `proj_rec::bvar_params`. -/
theorem bvar_params_loop_refines (N : Nat) :
    ∀ (n_p : Std.U64) (out r : alloc.vec.Vec expr.Expr) (k : Std.U64),
      n_p.val - k.val = N →
      frontend.proj_rec.bvar_params_loop n_p out k = ok r →
      absExprs r = absExprs out ++
        (((List.range n_p.val).drop k.val).map
          fun j => ConLeche.Expr.bvar (n_p.val - j)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro n_p out r k hN h
    rw [frontend.proj_rec.bvar_params_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : k.val < n_p.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i, hi, e, he, out1, hpush, k1, hk1, hrec⟩ := h
      have hiv : i.val = n_p.val - k.val := HashMap.uscalar_sub_eq hi
      have hk1v : k1.val = k.val + 1 := HashMap.uscalar_add_eq hk1
      have hdrop : (List.range n_p.val).drop k.val
          = k.val :: (List.range n_p.val).drop (k.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hltv)]
        simp
      rw [ih (n_p.val - k1.val) (by omega) n_p out1 r k1 rfl hrec,
        ExprOps.absExprs_push hpush, hk1v, hdrop, Expr.mk_bvar_refines he, hiv]
      simp
    · rename_i hge
      have hle : n_p.val ≤ k.val := by scalar_tac
      rw [← Result.ok_injective h, List.drop_eq_nil_of_le (by simpa using hle)]
      simp

/-- `proj_rec::bvar_params` — the cited `(List.range o.nP).map fun k =>
Expr.bvar (o.nP - k)` (`ConLeche/Frontend/ProjRec.lean:279-330 projRecValue`). -/
theorem bvar_params_refines {n_p : Std.U64} {r : alloc.vec.Vec expr.Expr}
    (h : frontend.proj_rec.bvar_params n_p = ok r) :
    absExprs r = (List.range n_p.val).map fun j => ConLeche.Expr.bvar (n_p.val - j) := by
  rw [frontend.proj_rec.bvar_params] at h
  simp only [lift_eq, bind_tc_ok] at h
  rw [bvar_params_loop_refines _ n_p _ r 0#u64 rfl h]
  simp [absExprs, alloc.vec.Vec.with_capacity,
    show ((0#u64 : Std.U64)).val = 0 by scalar_tac]

/-- `proj_rec::punit_at` — `.const punitName [ℓ]`. -/
theorem punit_at_refines {l : level.Level} {e : expr.Expr}
    (h : frontend.proj_rec.punit_at l = ok e) :
    absExpr e = .const ConLeche.punitName [absLevel l] := by
  rw [frontend.proj_rec.punit_at] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, v, hv, hmk⟩ := h
  rw [Expr.mk_const_refines hmk, (BasisNames.punit_name_refines hn).1,
    one_level_refines hv]

/-- `proj_rec::punit_unit_at` — `.const punitUnitName [ℓ]`. -/
theorem punit_unit_at_refines {l : level.Level} {e : expr.Expr}
    (h : frontend.proj_rec.punit_unit_at l = ok e) :
    absExpr e = .const ConLeche.punitUnitName [absLevel l] := by
  rw [frontend.proj_rec.punit_unit_at] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, v, hv, hmk⟩ := h
  rw [Expr.mk_const_refines hmk, (BasisNames.punit_unit_name_refines hn).1,
    one_level_refines hv]

/-- The countdown behind `proj_rec::mk_lams`. -/
theorem mk_lams_loop_refines (N : Nat) :
    ∀ (bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)) (acc r : expr.Expr)
      (i : Std.Usize),
      i.val = N → i.val ≤ bs.val.length →
      frontend.proj_rec.mk_lams_loop bs acc i = ok r →
      absExpr r = ConLeche.Frontend.mkLams
        ((ExprOps.absBinders bs).take i.val) (absExpr acc) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro bs acc r i hN hle h
    rw [frontend.proj_rec.mk_lams_loop.eq_def] at h
    split at h
    · rename_i hgt
      have hgtv : 0 < i.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i1, hi1, p, hidx, h⟩ := h
      have hi1v : i1.val = i.val - 1 := HashMap.uscalar_sub_eq hi1
      obtain ⟨hlt1, htake⟩ :=
        take_map_index (fun q => (absExpr q.1, absBinderMeta q.2)) hidx
      obtain ⟨e, bm⟩ := p
      obtain ⟨e1, hdup, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨bm1, hbm, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨acc1, hlam, hrec⟩ := bind_eq_ok_iff.mp h
      rw [Expr.dup_eq hdup] at hlam
      rw [Expr.binder_meta_dup_eq hbm] at hlam
      rw [ih i1.val (by omega) bs acc1 r i1 rfl (by omega) hrec,
        Expr.lam_refines hlam]
      have hiv : i.val = i1.val + 1 := by omega
      simp only [ExprOps.absBinders]
      rw [hiv, htake]
      simp [ConLeche.Frontend.mkLams]
    · rename_i hge
      have hz : i.val = 0 := by scalar_tac
      rw [← Result.ok_injective h, hz]
      simp [ConLeche.Frontend.mkLams]

/-- `proj_rec::mk_lams` refines `mkLams` (`ConLeche/Frontend/ProjRec.lean:247-249
mkLams`). -/
theorem mk_lams_refines {bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {body r : expr.Expr} (h : frontend.proj_rec.mk_lams bs body = ok r) :
    absExpr r = ConLeche.Frontend.mkLams (ExprOps.absBinders bs) (absExpr body) := by
  rw [frontend.proj_rec.mk_lams] at h
  rw [mk_lams_loop_refines _ bs body r _ rfl (by simp [alloc.vec.Vec.len]) h]
  congr 1
  exact List.take_of_length_le (by simp [ExprOps.absBinders, alloc.vec.Vec.len])

/-! ## The telescope walkers -/

/-- `expr_ops_c::instantiate1_lift` at con-leche's *pure* spelling: the cached
twin's `@[csimp]` partner (`Verify/Cached/OpsC.lean:2224 instantiate1LiftC_spec`),
which is what `ConLeche/Frontend/ProjRec.lean` writes. -/
theorem inst1_lift_refines {e v r : expr.Expr} {d : Std.U64} (he : ExprWF e)
    (hv : ExprWF v) (h : cached.expr_ops_c.instantiate1_lift e v d = ok r) :
    absExpr r = ConLeche.Expr.instantiate1Lift (absExpr e) (absExpr v) d.val ∧
      ExprWF r := by
  obtain ⟨h1, h2⟩ := ExprOpsC.instantiate1_lift_refines he hv h
  exact ⟨by rw [h1, ConLeche.Expr.instantiate1LiftC_spec], h2⟩

/-- The spine walk behind `proj_rec::strip_pis_all`. -/
theorem strip_pis_all_loop_refines (cur : expr.Expr) (hcur : ExprWF cur) :
    ∀ (bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta))
      (r : (alloc.vec.Vec (expr.Expr × expr.BinderMeta)) × expr.Expr),
      frontend.proj_rec.strip_pis_all_loop bs cur true = ok r →
      ExprOps.absBinders r.1 = ExprOps.absBinders bs ++
          (ConLeche.Frontend.stripPisAll (absExpr cur)).1 ∧
        absExpr r.2 = (ConLeche.Frontend.stripPisAll (absExpr cur)).2 := by
  induction cur, hcur using ExprWF.ind_node with
  | forall_e d ty bo m hwf ihty ihb =>
    intro bs r h
    obtain ⟨bs', e'⟩ := r
    rw [frontend.proj_rec.strip_pis_all_loop.eq_def] at h
    rust_norm h
    all_goals first
      | exact absurd trivial ‹¬True›
      | (rename_i bs2 bm hand
         obtain ⟨hbm, hpush⟩ := hand
         obtain ⟨hty, hb, hm⟩ := ExprWF.forall_e_kids hwf
         rw [Expr.binder_meta_dup_eq hbm] at hpush
         obtain ⟨h1, h2⟩ := ihb hb bs2 (bs', e') h
         rw [ExprOps.absBinders_push hpush] at h1
         exact ⟨by rw [h1]; simp [ConLeche.Frontend.stripPisAll],
           by rw [h2]; simp [ConLeche.Frontend.stripPisAll]⟩)
  | _ =>
    intro bs r h
    obtain ⟨bs', e'⟩ := r
    rw [frontend.proj_rec.strip_pis_all_loop.eq_def] at h
    rust_norm h
    all_goals first
      | exact absurd trivial ‹¬True›
      | (rw [strip_pis_all_loop_false h]
         simp [ConLeche.Frontend.stripPisAll])

/-- `proj_rec::strip_pis_all` refines `stripPisAll`
(`ConLeche/Frontend/ProjRec.lean:239-245 stripPisAll`). -/
theorem strip_pis_all_refines {e : expr.Expr}
    {r : (alloc.vec.Vec (expr.Expr × expr.BinderMeta)) × expr.Expr} (he : ExprWF e)
    (h : frontend.proj_rec.strip_pis_all e = ok r) :
    (ExprOps.absBinders r.1, absExpr r.2) = ConLeche.Frontend.stripPisAll (absExpr e) := by
  rw [frontend.proj_rec.strip_pis_all] at h
  simp only [expr_dup_eq, bind_tc_ok] at h
  obtain ⟨h1, h2⟩ := strip_pis_all_loop_refines e he _ r h
  rw [h2]
  rw [h1]
  simp [ExprOps.absBinders]

/-- The abstraction half of `lam_body_refines`, by the `Name`-style node
induction; the well-formedness half is phase 1's `lam_body_wf`. -/
private theorem lam_body_abs (e : expr.Expr) (he : ExprWF e) :
    ∀ b, frontend.proj_rec.lam_body e = ok b →
      absExpr b = ConLeche.Frontend.lamBody (absExpr e) := by
  induction e, he using ExprWF.ind_node with
  | lam d ty bo m hwf ihty ihb =>
    intro b h
    rw [frontend.proj_rec.lam_body.eq_def] at h
    rust_norm h
    rw [ihb (ExprWF.lam_kids hwf).2.1 b h]
    simp [ConLeche.Frontend.lamBody]
  | _ =>
    intro b h
    rw [frontend.proj_rec.lam_body.eq_def] at h
    rust_norm h
    simp [ConLeche.Frontend.lamBody]

/-- `proj_rec::lam_body` refines `lamBody` (`ConLeche/Frontend/ProjRec.lean:233-237
lamBody`): the node under the value's leading `λ`s.  Stated in the shape
`Refine/Frontend/StateDR.lean`'s `ProjRecSpec.lamBody` asks for. -/
theorem lam_body_refines (e : expr.Expr) (he : ExprWF e) :
    ∀ b, frontend.proj_rec.lam_body e = ok b →
      absExpr b = ConLeche.Frontend.lamBody (absExpr e) ∧ ExprWF b :=
  fun b h => ⟨lam_body_abs e he b h, lam_body_wf e he b h⟩

/-- The index recursion behind `proj_rec::inst_pis_open`. -/
theorem inst_pis_open_loop_refines (N : Nat) :
    ∀ (args : alloc.vec.Vec expr.Expr) (cur : expr.Expr) (n i : Std.Usize)
      (r : expr.Expr × Bool),
      n.val - i.val = N → n.val = args.val.length → ExprsWF args → ExprWF cur →
      frontend.proj_rec.inst_pis_open_loop args cur n i true = ok r →
      (if r.2 then some (absExpr r.1) else none)
        = ConLeche.Frontend.instPisOpen (absExpr cur) ((absExprs args).drop i.val) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro args cur n i r hN hn hargs hcur h
    obtain ⟨cur1, ok1⟩ := r
    obtain ⟨⟨d, kind⟩⟩ := cur
    rw [frontend.proj_rec.inst_pis_open_loop.eq_def] at h
    rust_norm h
    case h_7 =>
      rename_i ty bo m hkd ea e1 hand i1 hi1
      obtain ⟨hidx, hinst⟩ := hand
      have hkind : kind = .ForallE ty bo m := (of_kind_forall_e_iff _ _ _ _).mp hkd
      subst hkind
      obtain ⟨-, hbo, -⟩ := ExprWF.forall_e_kids hcur
      obtain ⟨hlt, hea, hdrop⟩ := ExprOps.vec_index_expr hargs hidx
      obtain ⟨habs, hwf⟩ := inst1_lift_refines hbo hea hinst
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      rw [ih (n.val - i1.val) (by omega) args e1 n i1 (cur1, ok1) rfl hn hargs hwf h,
        habs, hdrop, hi1v]
      simp [ConLeche.Frontend.instPisOpen]
    -- `rust_norm`'s `split` delta-unfolds `ExprView.ofKind` before generalising, so
    -- the arm's equation is a bare matcher and the `of_kind_*_iff` simp lemmas do not
    -- match it; fold it back first, then invert.
    all_goals
      try (rename_i hkd
           replace hkd : ron.node.ExprView.ofKind _ = _ := hkd
           of_kind_inv hkd
           subst hkd)
    all_goals
      first
        | exact absurd trivial ‹¬True›
        | (have hle : n.val ≤ i.val := by scalar_tac
           simp only [absExprs]
           rw [List.drop_eq_nil_of_le (by simpa [hn] using hle)]
           subst_vars
           simp [ConLeche.Frontend.instPisOpen])
        | (rw [inst_pis_open_loop_false h]
           have hlt : i.val < n.val := by scalar_tac
           have hne : ((absExprs args).drop i.val) ≠ [] := by
             simp only [absExprs, ne_eq, List.drop_eq_nil_iff, List.length_map]
             omega
           obtain ⟨a0, as0, hl⟩ := List.exists_cons_of_ne_nil hne
           rw [hl]
           simp [ConLeche.Frontend.instPisOpen])

/-- `proj_rec::inst_pis_open` refines `instPisOpen`
(`ConLeche/Frontend/ProjRec.lean:251-257 instPisOpen`). -/
theorem inst_pis_open_refines {e : expr.Expr} {args : alloc.vec.Vec expr.Expr}
    {r : Option expr.Expr} (he : ExprWF e) (hargs : ExprsWF args)
    (h : frontend.proj_rec.inst_pis_open e args = ok r) :
    Option.map absExpr r = ConLeche.Frontend.instPisOpen (absExpr e) (absExprs args) := by
  rw [frontend.proj_rec.inst_pis_open] at h
  simp only [expr_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
  obtain ⟨p, hloop, hdone⟩ := h
  obtain ⟨cur1, ok1⟩ := p
  have habs := inst_pis_open_loop_refines _ args e _ 0#usize (cur1, ok1) rfl
    (by simp [alloc.vec.Vec.len]) hargs he hloop
  rw [show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero] at habs
  replace hdone : frontend.proj_rec.inst_pis_open_done ok1 cur1 = ok r := hdone
  rw [frontend.proj_rec.inst_pis_open_done.eq_def] at hdone
  cases ok1 with
  | true =>
    simp only [if_true] at hdone habs
    rw [← Result.ok_injective hdone]; simpa using habs
  | false =>
    simp only [Bool.false_eq_true, if_false] at hdone habs
    rw [← Result.ok_injective hdone]; simpa using habs

/-! ## `build_binders`, parametric in its dictionary -/

/-- `Option.bind` at a `some`. -/
@[simp] theorem option_some_bind {α β : Type} (a : α) (g : α → Option β) :
    (some a).bind g = g a := rfl

/-- An `Option` `guard` that holds. -/
theorem guard_opt_pos {c : Prop} [Decidable c] (hc : c) :
    (guard c : Option Unit) = some () := by simp [guard, hc]

/-- …and one that does not. -/
theorem guard_opt_neg {c : Prop} [Decidable c] (hc : ¬ c) :
    (guard c : Option Unit) = none := by simp [guard, hc]

/-- `>>=` at a `some`. -/
@[simp] theorem option_bind_some_l {α β : Type} (a : α) (g : α → Option β) :
    (some a : Option α) >>= g = g a := rfl

/-- Two `Option.map`s in a row. -/
theorem option_map_comp {α β γ : Type} (x : Option α) (g : α → β) (k : β → γ) :
    (x.map g).map k = x.map fun a => k (g a) := by cases x <;> rfl

/-- `Option.bind` into a `some` is `Option.map`. -/
theorem option_bind_some {α β : Type} (x : Option α) (g : α → β) :
    (x.bind fun a => some (g a)) = x.map g := by cases x <;> rfl

/-- The dictionary's refinement obligation: the binder it makes out of a
well-formed domain is what con-leche's `Expr → Option Expr` gives. -/
def MkBinderRefines {M : Type} (inst : frontend.proj_rec.MkBinder M) (mk : M)
    (f : ConLeche.Expr → Option ConLeche.Expr) : Prop :=
  ∀ dom, ExprWF dom → ∀ o, inst.binder mk dom = ok o →
    Option.map absExpr o = f (absExpr dom)

/-- `proj_rec::build_binders_step` — one peeled binder, as the cited
`| k + 1, .forallE dom body _ => …` arm (`ConLeche/Frontend/ProjRec.lean:259-269
buildBinders`). -/
theorem build_binders_step_refines {M : Type} {inst : frontend.proj_rec.MkBinder M}
    {mk : M} {f : ConLeche.Expr → Option ConLeche.Expr} {cur : expr.Expr}
    {o : Option (expr.Expr × expr.Expr)} (hmk : MkBinderRefines inst mk f)
    (hmkw : MkBinderWF inst mk) (hcur : ExprWF cur)
    (h : frontend.proj_rec.build_binders_step inst mk cur = ok o) :
    ∀ kk, ConLeche.Frontend.buildBinders f (kk + 1) (absExpr cur)
      = o.bind fun p => (ConLeche.Frontend.buildBinders f kk (absExpr p.2)).map
          fun q => (absExpr p.1 :: q.1, q.2) := by
  obtain ⟨⟨d, kind⟩⟩ := cur
  rw [frontend.proj_rec.build_binders_step.eq_def] at h
  rust_norm h
  case h_7 =>
    rename_i ty bo m hkd
    have hkind : kind = .ForallE ty bo m := (of_kind_forall_e_iff _ _ _ _).mp hkd
    subst hkind
    obtain ⟨hdom, hbody, -⟩ := ExprWF.forall_e_kids hcur
    rw [frontend.proj_rec.build_binders_step_at] at h
    obtain ⟨o1, hb, h⟩ := bind_eq_ok_iff.mp h
    have hfa := hmk _ hdom o1 hb
    cases o1 with
    | none =>
      rw [← Result.ok_injective h]
      intro kk
      simp only [Option.map_none] at hfa
      simp only [absExpr_mk, absExprKind, ConLeche.Frontend.buildBinders, ← hfa]
      rfl
    | some t =>
      obtain ⟨b0, hinst, h⟩ := bind_eq_ok_iff.mp h
      have ht : ExprWF t := hmkw _ hdom t hb
      obtain ⟨habs, hwf⟩ := inst1_lift_refines hbody ht hinst
      rw [show ((0#u64 : Std.U64)).val = 0 by scalar_tac] at habs
      rw [← Result.ok_injective h]
      intro kk
      simp only [Option.map_some] at hfa
      simp only [absExpr_mk, absExprKind, ConLeche.Frontend.buildBinders, ← hfa]
      simp [habs, option_bind_some]
  -- the nine arms that are not a `∀`: fold the unfolded `ExprView.ofKind` matcher
  -- back so `of_kind_inv` can read the kind off the arm's equation
  all_goals (rename_i hkd
             replace hkd : ron.node.ExprView.ofKind _ = _ := hkd
             of_kind_inv hkd
             subst hkd
             intro kk
             rfl)

/-- The countdown behind `proj_rec::build_binders`. -/
theorem build_binders_loop_refines {M : Type} {inst : frontend.proj_rec.MkBinder M}
    {mk : M} {f : ConLeche.Expr → Option ConLeche.Expr} (hmk : MkBinderRefines inst mk f)
    (hmkw : MkBinderWF inst mk) (N : Nat) :
    ∀ (k : Std.U64) (out : alloc.vec.Vec expr.Expr) (cur : expr.Expr) (i : Std.U64)
      (r : (alloc.vec.Vec expr.Expr) × expr.Expr × Bool),
      k.val - i.val = N → ExprWF cur →
      frontend.proj_rec.build_binders_loop inst mk k out cur i true = ok r →
      (if r.2.2 then some (absExprs r.1, absExpr r.2.1) else none)
        = (ConLeche.Frontend.buildBinders f (k.val - i.val) (absExpr cur)).map
            fun p => (absExprs out ++ p.1, p.2) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro k out cur i r hN hcur h
    rw [frontend.proj_rec.build_binders_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < k.val := by scalar_tac
      simp only [if_true, bind_eq_ok_iff] at h
      obtain ⟨o, hstep, h⟩ := h
      have hsr := build_binders_step_refines hmk hmkw hcur hstep
      have hk : k.val - i.val = (k.val - (i.val + 1)) + 1 := by omega
      cases o with
      | none =>
        rw [build_binders_loop_false h, hk, hsr]
        simp
      | some p =>
        obtain ⟨t, b⟩ := p
        replace h : (do
            let out1 ← alloc.vec.Vec.push out t
            let i1 ← i + 1#u64
            frontend.proj_rec.build_binders_loop inst mk k out1 b i1 true) = ok r := h
        simp only [bind_eq_ok_iff] at h
        obtain ⟨out1, hpush, i1, hi1, hrec⟩ := h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        obtain ⟨hwt, hwb⟩ := build_binders_step_wf hmkw hcur hstep t b rfl
        rw [ih (k.val - i1.val) (by omega) k out1 b i1 r rfl hwb hrec,
          ExprOps.absExprs_push hpush, hk, hsr, hi1v, option_some_bind,
          option_map_comp]
        congr 1
        funext q
        simp
    · rename_i hge
      have hle : k.val ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h, show k.val - i.val = 0 by omega]
      simp [ConLeche.Frontend.buildBinders]

/-- `proj_rec::build_binders` refines `buildBinders`
(`ConLeche/Frontend/ProjRec.lean:259-269 buildBinders`), the dictionary's
refinement and well-formedness as hypotheses. -/
theorem build_binders_refines {M : Type} {inst : frontend.proj_rec.MkBinder M}
    {mk : M} {f : ConLeche.Expr → Option ConLeche.Expr} {k : Std.U64} {e : expr.Expr}
    {r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)}
    (hmk : MkBinderRefines inst mk f) (hmkw : MkBinderWF inst mk) (he : ExprWF e)
    (h : frontend.proj_rec.build_binders inst mk k e = ok r) :
    Option.map (fun p => (absExprs p.1, absExpr p.2)) r
      = ConLeche.Frontend.buildBinders f k.val (absExpr e) := by
  rw [frontend.proj_rec.build_binders] at h
  simp only [expr_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
  obtain ⟨p, hloop, hdone⟩ := h
  obtain ⟨out0, cur0, ok0⟩ := p
  have habs := build_binders_loop_refines hmk hmkw _ k _ e 0#u64 (out0, cur0, ok0)
    rfl he hloop
  rw [show ((0#u64 : Std.U64)).val = 0 by scalar_tac, Nat.sub_zero] at habs
  have hid : ∀ (x : Option (List ConLeche.Expr × ConLeche.Expr)),
      (x.map fun p => (absExprs (alloc.vec.Vec.new expr.Expr) ++ p.1, p.2)) = x := by
    intro x
    cases x with
    | none => rfl
    | some q => simp [absExprs]
  rw [hid] at habs
  replace hdone : frontend.proj_rec.build_binders_done ok0 out0 cur0 = ok r := hdone
  rw [frontend.proj_rec.build_binders_done.eq_def] at hdone
  rw [← habs]
  cases ok0 with
  | true =>
    simp only [if_true] at hdone ⊢
    rw [← Result.ok_injective hdone]
    simp [absExprs]
  | false =>
    simp only [Bool.false_eq_true, if_false] at hdone ⊢
    rw [← Result.ok_injective hdone]; simp

/-! ## The three fragments of `projRecValue`

`ConLeche/Frontend/ProjRec.lean:279-330 projRecValue` binds its two binder
builders as local `let`s and ends in a `match rty with`; the port factors all
three out (`MkMotive`/`MkMinor`, `proj_rec_value_major`), and task #84 split
its tail into `proj_rec_value_at` for the Aeneas loop-shape rule.  These four
definitions are that same factoring **on the con-leche side**, written out
verbatim; `projRecValue_eq` below is the equivalence proof, and it is `rfl`:
they are the cited term's own sub-terms, zeta-expanded. -/

/-- `projRecValue`'s `mkMotive` (`ProjRec.lean:300-306`). -/
def lMkMotive (T : ConLeche.Name) (R : ConLeche.Expr) (l : ConLeche.Level) :
    ConLeche.Expr → Option ConLeche.Expr := fun dom =>
  match ConLeche.Frontend.stripPisAll dom with
  | ([(d, m)], .sort _) =>
    if ConLeche.Frontend.headIs T d then some (.lam d (R.liftLooseBVars 1 1) m)
    else some (.lam d (.const ConLeche.punitName [l]) m)
  | (bs, .sort _) =>
    some (ConLeche.Frontend.mkLams bs (.const ConLeche.punitName [l]))
  | _ => none

/-- `projRecValue`'s `mkMinor` at `stripPisAll`'s answer (`ProjRec.lean:312-320`). -/
def lMkMinorAt (C : ConLeche.Name) (i : Nat) (l : ConLeche.Level)
    (bs : List (ConLeche.Expr × ConLeche.BinderMeta)) (cod : ConLeche.Expr) :
    Option ConLeche.Expr :=
  match cod.getAppArgs.getLast? with
  | some major =>
    if ConLeche.Frontend.headIs C major then
      if i < bs.length then
        some (ConLeche.Frontend.mkLams bs (.bvar (bs.length - 1 - i)))
      else none
    else some (ConLeche.Frontend.mkLams bs (.const ConLeche.punitUnitName [l]))
  | none => none

/-- `projRecValue`'s `mkMinor` (`ProjRec.lean:312-320`). -/
def lMkMinor (C : ConLeche.Name) (i : Nat) (l : ConLeche.Level) :
    ConLeche.Expr → Option ConLeche.Expr := fun dom =>
  lMkMinorAt C i l (ConLeche.Frontend.stripPisAll dom).1
    (ConLeche.Frontend.stripPisAll dom).2

/-- …at a known `stripPisAll`. -/
theorem lMkMinor_eq {C : ConLeche.Name} {i : Nat} {l : ConLeche.Level}
    {dom : ConLeche.Expr} {bs : List (ConLeche.Expr × ConLeche.BinderMeta)}
    {cod : ConLeche.Expr} (hst : ConLeche.Frontend.stripPisAll dom = (bs, cod)) :
    lMkMinor C i l dom = lMkMinorAt C i l bs cod := by rw [lMkMinor, hst]

/-- `projRecValue`'s closing `match rty with` (`ProjRec.lean:324-330`). -/
def lProjRecMajor (T recName : ConLeche.Name) (lus : List ConLeche.Level)
    (params motives minors : List ConLeche.Expr)
    (lbs : List (ConLeche.Expr × ConLeche.BinderMeta)) (rty : ConLeche.Expr) :
    Option ConLeche.Expr :=
  match rty with
  | .forallE majDom _ _ => do
    guard (ConLeche.Frontend.headIs T majDom)
    let app := ConLeche.Expr.mkAppN (.const recName lus)
      (params ++ motives ++ minors ++ [.bvar 0])
    pure (ConLeche.Frontend.mkLams lbs app)
  | _ => none

/-- `projRecValue`'s tail, from `let us := o.lps.map Level.param` on
(`ProjRec.lean:290-330`) — the port's `proj_rec_value_at`. -/
def lProjRecValueAt (o : ConLeche.Frontend.ProjRecOwner) (l : ConLeche.Level)
    (R : ConLeche.Expr) (lbs : List (ConLeche.Expr × ConLeche.BinderMeta))
    (i : Nat) : Option ConLeche.Expr :=
  let us := o.lps.map ConLeche.Level.param
  let rty := o.recType.instantiateLevelParams o.recLps (l :: us)
  let params := (List.range o.nP).map fun k => ConLeche.Expr.bvar (o.nP - k)
  do
  let rty ← ConLeche.Frontend.instPisOpen rty params
  let (motives, rty) ←
    ConLeche.Frontend.buildBinders (lMkMotive o.T R l) o.numMotives rty
  let (minors, rty) ←
    ConLeche.Frontend.buildBinders (lMkMinor o.ctor i l) o.numMinors rty
  lProjRecMajor o.T o.recName (l :: us) params motives minors lbs rty

/-- **The factoring is the cited term.** -/
theorem projRecValue_eq (o : ConLeche.Frontend.ProjRecOwner) (l : ConLeche.Level)
    (ty val : ConLeche.Expr) (i : Nat) :
    ConLeche.Frontend.projRecValue o l ty val i
      = (do
        let (lbs, body) ← val.stripLams (o.nP + 1)
        guard (body == .proj o.T i (.bvar 0))
        guard (i < o.nF)
        let (_, R) ← ty.stripPis (o.nP + 1)
        lProjRecValueAt o l R lbs i) := by
  unfold ConLeche.Frontend.projRecValue lProjRecValueAt lProjRecMajor lMkMotive
    lMkMinor lMkMinorAt
  rfl

/-- …and the same with the two `guard`s read as `if`s, which is the shape the
port's `expr::beq` and `i >= o.n_f` tests give. -/
theorem projRecValue_eq' (o : ConLeche.Frontend.ProjRecOwner) (l : ConLeche.Level)
    (ty val : ConLeche.Expr) (i : Nat) :
    ConLeche.Frontend.projRecValue o l ty val i
      = (ConLeche.Expr.stripLams (o.nP + 1) val).bind (fun p =>
          if p.2 = ConLeche.Expr.proj o.T i (ConLeche.Expr.bvar 0) then
            if i < o.nF then
              (ConLeche.Expr.stripPis (o.nP + 1) ty).bind (fun q =>
                lProjRecValueAt o l q.2 p.1 i)
            else none
          else none) := by
  rw [projRecValue_eq]
  cases hsl : ConLeche.Expr.stripLams (o.nP + 1) val with
  | none => rfl
  | some p =>
    by_cases h1 : p.2 = ConLeche.Expr.proj o.T i (ConLeche.Expr.bvar 0) <;>
      by_cases h2 : i < o.nF <;> simp [guard, h1, h2]

/-! ## The two dictionaries -/

/-- The abstraction of a `Vec` the port found to have length one. -/
theorem binders_singleton {bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {p : expr.Expr × expr.BinderMeta}
    (hlen : alloc.vec.Vec.len bs = (1#usize : Std.Usize))
    (h : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice (expr.Expr × expr.BinderMeta)) bs 0#usize
      = ok p) :
    ExprOps.absBinders bs = [(absExpr p.1, absBinderMeta p.2)] := by
  have hl : bs.val.length = 1 := by
    have := alloc.vec.Vec.len_val bs; rw [hlen] at this; scalar_tac
  have hg := ExprOps.vec_index_getElem? h
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl
  rw [hx] at hg
  simp only [show ((0#usize : Std.Usize)).val = 0 by scalar_tac,
    List.getElem?_cons_zero, Option.some.injEq] at hg
  rw [ExprOps.absBinders, hx, ← hg]
  simp

/-- A list whose length is not one is empty or has two heads. -/
theorem list_ne_singleton {α : Type} (xs : List α) (h : xs.length ≠ 1) :
    xs = [] ∨ ∃ a b tl, xs = a :: b :: tl := by
  match xs with
  | [] => exact Or.inl rfl
  | [_] => simp at h
  | a :: b :: tl => exact Or.inr ⟨a, b, tl, rfl⟩

/-- …and of one the port found not to. -/
theorem binders_not_singleton {bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    (hlen : ¬ alloc.vec.Vec.len bs = (1#usize : Std.Usize)) :
    ExprOps.absBinders bs = [] ∨
      ∃ a b tl, ExprOps.absBinders bs = a :: b :: tl := by
  have hl : bs.val.length ≠ 1 := by
    intro hc
    exact hlen (by have := alloc.vec.Vec.len_val bs; scalar_tac)
  rcases list_ne_singleton bs.val hl with hnil | ⟨a, b, tl, hcons⟩
  · exact Or.inl (by rw [ExprOps.absBinders, hnil]; rfl)
  · exact Or.inr ⟨_, _, _, by rw [ExprOps.absBinders, hcons]; rfl⟩

/-- `lMkMotive` declines a domain whose `stripPisAll` body is not a sort. -/
theorem lMkMotive_not_sort {T : ConLeche.Name} {R : ConLeche.Expr}
    {l : ConLeche.Level} {dom : ConLeche.Expr}
    {bs : List (ConLeche.Expr × ConLeche.BinderMeta)} {e : ConLeche.Expr}
    (hst : ConLeche.Frontend.stripPisAll dom = (bs, e))
    (h : ∀ u, e ≠ ConLeche.Expr.sort u) : lMkMotive T R l dom = none := by
  rw [lMkMotive, hst]
  split <;> first | rfl | (exfalso; simp_all)

/-- A node's abstraction, read off its observed kind. -/
theorem absExpr_of_kind {e : expr.Expr} {k : expr.ExprKind} (h : e._0.kind = k) :
    absExpr e = absExprKind k := by
  obtain ⟨⟨d, kk⟩⟩ := e
  rw [← h]; rfl

/-- `proj_rec::MkMotive` refines `projRecValue`'s `mkMotive`
(`ConLeche/Frontend/ProjRec.lean:300-306`). -/
theorem mk_motive_refines {t : name.Name} {rr : expr.Expr} {l : level.Level}
    (ht : NameWF t) (hr : ExprWF rr) :
    MkBinderRefines frontend.proj_rec.MkMotive.Insts.Con_ron_coreFrontendProj_recMkBinder
      { t := t, r := rr, l := l } (lMkMotive (absName t) (absExpr rr) (absLevel l)) := by
  intro dom hdom o h
  replace h : frontend.proj_rec.MkMotive.Insts.Con_ron_coreFrontendProj_recMkBinder.binder
      { t := t, r := rr, l := l } dom = ok o := h
  rw [frontend.proj_rec.MkMotive.Insts.Con_ron_coreFrontendProj_recMkBinder.binder] at h
  obtain ⟨p, hsp, -⟩ := bind_eq_ok_iff.mp h
  have habs := strip_pis_all_refines hdom hsp
  obtain ⟨hbs, hbody⟩ := strip_pis_all_wf hdom hsp
  rw [hsp] at h
  simp only [bind_tc_ok] at h
  rust_norm h
  all_goals (try simp only [] at habs hbs hbody)
  case h_3.isTrue.isTrue =>
    rename_i _ u hkd hlen e1 bm hidx b hhi hbt e3 hlift bm1 hbmd e4 hlam
    obtain ⟨-, hmem⟩ := vec_index_mem hidx
    obtain ⟨he1, hbm⟩ := hbs _ hmem
    have hHI : ConLeche.Frontend.headIs (absName t) (absExpr e1) = true := by
      rw [← head_is_refines ht he1 hhi]; exact hbt
    rw [lMkMotive, ← habs, binders_singleton hlen hidx,
      absExpr_of_kind ((of_kind_sort_iff _ _).mp hkd)]
    simp only [absExprKind, hHI, if_true, Option.map_some, Expr.lam_refines hlam,
      Expr.binder_meta_dup_eq hbmd, (ExprOps.lift_loose_bvars_refines hr hlift).1]
    norm_num
  case h_3.isTrue.isFalse =>
    rename_i _ u hkd hlen e1 bm hidx b hhi hbf e3 hpu bm1 hbmd e4 hlam
    obtain ⟨-, hmem⟩ := vec_index_mem hidx
    obtain ⟨he1, hbm⟩ := hbs _ hmem
    have hHI : ConLeche.Frontend.headIs (absName t) (absExpr e1) = false := by
      rw [← head_is_refines ht he1 hhi]; simpa using hbf
    rw [lMkMotive, ← habs, binders_singleton hlen hidx,
      absExpr_of_kind ((of_kind_sort_iff _ _).mp hkd)]
    simp only [absExprKind, hHI, Bool.false_eq_true, if_false, Option.map_some,
      Expr.lam_refines hlam, Expr.binder_meta_dup_eq hbmd, punit_at_refines hpu]
  case h_3.isFalse =>
    rename_i _ u hkd hlen e1 hpu e2 hml
    rw [lMkMotive, ← habs, absExpr_of_kind ((of_kind_sort_iff _ _).mp hkd)]
    rcases binders_not_singleton hlen with hnil | ⟨a, b, tl, hcons⟩
    · rw [hnil]
      simp only [absExprKind, Option.map_some, mk_lams_refines hml,
        punit_at_refines hpu, hnil]
    · rw [hcons]
      simp only [absExprKind, Option.map_some, mk_lams_refines hml,
        punit_at_refines hpu, hcons]
  -- the nine kinds whose `stripPisAll` body is not a `Sort`; as above, the arm's
  -- equation needs folding back before `of_kind_inv` can invert it
  all_goals (rename_i hkd
             replace hkd : ron.node.ExprView.ofKind _ = _ := hkd
             of_kind_inv hkd
             rw [lMkMotive_not_sort habs.symm
               (by rw [absExpr_of_kind hkd]; intro u hc; simp [absExprKind] at hc)]
             rfl)

/-- The last argument of an empty spine. -/
theorem getLast?_empty {v : alloc.vec.Vec expr.Expr}
    (h : alloc.vec.Vec.len v = (0#usize : Std.Usize)) : (absExprs v).getLast? = none := by
  have hlv := alloc.vec.Vec.len_val v
  have h0 : v.val.length = 0 := by rw [h] at hlv; scalar_tac
  simp only [absExprs]
  rw [List.getLast?_eq_getElem?]
  simp [h0]

/-- The last argument of a spine the port read at `len - 1`. -/
theorem getLast?_last {v : alloc.vec.Vec expr.Expr} {i : Std.Usize} {x : expr.Expr}
    (hne : ¬ alloc.vec.Vec.len v = (0#usize : Std.Usize))
    (hi : alloc.vec.Vec.len v - (1#usize : Std.Usize) = ok i)
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice expr.Expr) v i
      = ok x) : (absExprs v).getLast? = some (absExpr x) := by
  have hlv := alloc.vec.Vec.len_val v
  have h0 : 0 < v.val.length := by
    rcases Nat.eq_zero_or_pos v.val.length with hz | hp
    · exact absurd (by scalar_tac) hne
    · exact hp
  have hiv : i.val = v.val.length - 1 := by
    rw [HashMap.uscalar_sub_eq hi]; scalar_tac
  have hg := ExprOps.vec_index_getElem? h
  simp only [absExprs]
  rw [List.getLast?_eq_getElem?, List.length_map, List.getElem?_map, ← hiv, hg]
  rfl

/-- A binder list's length, through the port's `u64` widening. -/
theorem binders_len_cast (bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)) :
    (Std.UScalar.cast .U64 (alloc.vec.Vec.len bs) : Std.U64).val
      = (ExprOps.absBinders bs).length := by
  rw [ExprOps.usize_cast_u64_val, ExprOps.absBinders, List.length_map]
  have := alloc.vec.Vec.len_val bs; scalar_tac

/-- `proj_rec::MkMinor` refines `projRecValue`'s `mkMinor`
(`ConLeche/Frontend/ProjRec.lean:312-320`). -/
theorem mk_minor_refines {c : name.Name} {i : Std.U64} {l : level.Level}
    (hc : NameWF c) :
    MkBinderRefines frontend.proj_rec.MkMinor.Insts.Con_ron_coreFrontendProj_recMkBinder
      { ctor := c, i := i, l := l } (lMkMinor (absName c) i.val (absLevel l)) := by
  intro dom hdom o h
  replace h : frontend.proj_rec.MkMinor.Insts.Con_ron_coreFrontendProj_recMkBinder.binder
      { ctor := c, i := i, l := l } dom = ok o := h
  rw [frontend.proj_rec.MkMinor.Insts.Con_ron_coreFrontendProj_recMkBinder.binder] at h
  obtain ⟨p, hsp, -⟩ := bind_eq_ok_iff.mp h
  have habs := strip_pis_all_refines hdom hsp
  obtain ⟨hbs, hbody⟩ := strip_pis_all_wf hdom hsp
  rw [hsp] at h
  simp only [bind_tc_ok] at h
  rust_norm h
  all_goals (try simp only [] at habs hbs hbody)
  case isTrue =>
    rename_i v e args hga hlen0
    obtain ⟨hgabs, hgwf⟩ := ExprOps.get_app_args_refines hbody hga
    rw [lMkMinor_eq habs.symm, lMkMinorAt, ← hgabs, getLast?_empty hlen0]
    rfl
  case isFalse.isTrue.isTrue =>
    rename_i v e args hga hne0 hlt i2 hi2 e1 hidx b hhi hbt i7 hi7 i8 hi8 e2 hbv e3 hml
    obtain ⟨hgabs, hgwf⟩ := ExprOps.get_app_args_refines hbody hga
    obtain ⟨-, hmem⟩ := vec_index_mem hidx
    have he1 : ExprWF e1 := hgwf _ hmem
    have hHI : ConLeche.Frontend.headIs (absName c) (absExpr e1) = true := by
      rw [← head_is_refines hc he1 hhi]; exact hbt
    have hcast := binders_len_cast v
    have hltv : i.val < (ExprOps.absBinders v).length := by rw [← hcast]; scalar_tac
    have hi7v : i7.val = (ExprOps.absBinders v).length - 1 := by
      rw [HashMap.uscalar_sub_eq hi7, hcast]; scalar_tac
    have hi8v : i8.val = (ExprOps.absBinders v).length - 1 - i.val := by
      rw [HashMap.uscalar_sub_eq hi8, hi7v]
    rw [lMkMinor_eq habs.symm, lMkMinorAt, ← hgabs, getLast?_last hne0 hi2 hidx]
    simp only [hHI, if_true]
    rw [if_pos hltv, Option.map_some, mk_lams_refines hml,
      Expr.mk_bvar_refines hbv, hi8v]
    simp
  case isFalse.isTrue.isFalse =>
    rename_i v e args hga hne0 hlt i2 hi2 e1 hidx b hhi hbf e2 hpu e3 hml
    obtain ⟨hgabs, hgwf⟩ := ExprOps.get_app_args_refines hbody hga
    obtain ⟨-, hmem⟩ := vec_index_mem hidx
    have he1 : ExprWF e1 := hgwf _ hmem
    have hHI : ConLeche.Frontend.headIs (absName c) (absExpr e1) = false := by
      rw [← head_is_refines hc he1 hhi]; simpa using hbf
    rw [lMkMinor_eq habs.symm, lMkMinorAt, ← hgabs, getLast?_last hne0 hi2 hidx]
    simp only [hHI, Bool.false_eq_true, if_false]
    rw [Option.map_some, mk_lams_refines hml, punit_unit_at_refines hpu]
  case isFalse.isFalse.isTrue =>
    rename_i v e args hga hne0 hge i2 hi2 e1 hidx b hhi hbt
    obtain ⟨hgabs, hgwf⟩ := ExprOps.get_app_args_refines hbody hga
    obtain ⟨-, hmem⟩ := vec_index_mem hidx
    have he1 : ExprWF e1 := hgwf _ hmem
    have hHI : ConLeche.Frontend.headIs (absName c) (absExpr e1) = true := by
      rw [← head_is_refines hc he1 hhi]; exact hbt
    have hcast := binders_len_cast v
    have hgev : ¬ i.val < (ExprOps.absBinders v).length := by rw [← hcast]; scalar_tac
    rw [lMkMinor_eq habs.symm, lMkMinorAt, ← hgabs, getLast?_last hne0 hi2 hidx]
    simp only [hHI, if_true]
    rw [if_neg hgev]
    rfl
  case isFalse.isFalse.isFalse =>
    rename_i v e args hga hne0 hge i2 hi2 e1 hidx b hhi hbf e2 hpu e3 hml
    obtain ⟨hgabs, hgwf⟩ := ExprOps.get_app_args_refines hbody hga
    obtain ⟨-, hmem⟩ := vec_index_mem hidx
    have he1 : ExprWF e1 := hgwf _ hmem
    have hHI : ConLeche.Frontend.headIs (absName c) (absExpr e1) = false := by
      rw [← head_is_refines hc he1 hhi]; simpa using hbf
    rw [lMkMinor_eq habs.symm, lMkMinorAt, ← hgabs, getLast?_last hne0 hi2 hidx]
    simp only [hHI, Bool.false_eq_true, if_false]
    rw [Option.map_some, mk_lams_refines hml, punit_unit_at_refines hpu]

/-! ## The rewrite -/

@[simp] theorem absProjRecOwner_T (o : frontend.proj_rec.ProjRecOwner) :
    (absProjRecOwner o).T = absName o.t := rfl
@[simp] theorem absProjRecOwner_lps (o : frontend.proj_rec.ProjRecOwner) :
    (absProjRecOwner o).lps = absNames o.lps := rfl
@[simp] theorem absProjRecOwner_nP (o : frontend.proj_rec.ProjRecOwner) :
    (absProjRecOwner o).nP = o.n_p.val := rfl
@[simp] theorem absProjRecOwner_ctor (o : frontend.proj_rec.ProjRecOwner) :
    (absProjRecOwner o).ctor = absName o.ctor := rfl
@[simp] theorem absProjRecOwner_nF (o : frontend.proj_rec.ProjRecOwner) :
    (absProjRecOwner o).nF = o.n_f.val := rfl
@[simp] theorem absProjRecOwner_recName (o : frontend.proj_rec.ProjRecOwner) :
    (absProjRecOwner o).recName = absName o.rec_name := rfl
@[simp] theorem absProjRecOwner_recLps (o : frontend.proj_rec.ProjRecOwner) :
    (absProjRecOwner o).recLps = absNames o.rec_lps := rfl
@[simp] theorem absProjRecOwner_recType (o : frontend.proj_rec.ProjRecOwner) :
    (absProjRecOwner o).recType = absExpr o.rec_type := rfl
@[simp] theorem absProjRecOwner_numMotives (o : frontend.proj_rec.ProjRecOwner) :
    (absProjRecOwner o).numMotives = o.num_motives.val := rfl
@[simp] theorem absProjRecOwner_numMinors (o : frontend.proj_rec.ProjRecOwner) :
    (absProjRecOwner o).numMinors = o.num_minors.val := rfl

/-- `lProjRecMajor` at a `∀`. -/
theorem lProjRecMajor_eq {T rn : ConLeche.Name} {lus : List ConLeche.Level}
    {ps ms mns : List ConLeche.Expr}
    {lbs : List (ConLeche.Expr × ConLeche.BinderMeta)}
    {rty majDom bo : ConLeche.Expr} {m : ConLeche.BinderMeta}
    (h : rty = .forallE majDom bo m) :
    lProjRecMajor T rn lus ps ms mns lbs rty
      = (do
          guard (ConLeche.Frontend.headIs T majDom)
          pure (ConLeche.Frontend.mkLams lbs
            (ConLeche.Expr.mkAppN (.const rn lus) (ps ++ ms ++ mns ++ [.bvar 0])))) := by
  rw [h, lProjRecMajor]

/-- …and at anything else. -/
theorem lProjRecMajor_not_forall {T rn : ConLeche.Name} {lus : List ConLeche.Level}
    {ps ms mns : List ConLeche.Expr}
    {lbs : List (ConLeche.Expr × ConLeche.BinderMeta)} {rty : ConLeche.Expr}
    (h : ∀ a b c, rty ≠ ConLeche.Expr.forallE a b c) :
    lProjRecMajor T rn lus ps ms mns lbs rty = none := by
  rw [lProjRecMajor]
  intro a b c hc
  exact h a b c hc

/-- `proj_rec::proj_rec_value_major` refines `projRecValue`'s closing
`match rty with` (`ConLeche/Frontend/ProjRec.lean:324-330`). -/
theorem proj_rec_value_major_refines {o : frontend.proj_rec.ProjRecOwner}
    {lus : alloc.vec.Vec level.Level} {params motives minors : alloc.vec.Vec expr.Expr}
    {lbs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {rty : expr.Expr}
    {res : Option expr.Expr} (ho : ProjRecOwnerWF o) (hlus : LevelsWF lus)
    (hparams : ExprsWF params) (hmotives : ExprsWF motives) (hminors : ExprsWF minors)
    (_hlbs : ExprOps.BindersWF lbs) (hrty : ExprWF rty)
    (h : frontend.proj_rec.proj_rec_value_major o lus params motives minors lbs rty
      = ok res) :
    Option.map absExpr res = lProjRecMajor (absName o.t) (absName o.rec_name)
      (absLevels lus) (absExprs params) (absExprs motives) (absExprs minors)
      (ExprOps.absBinders lbs) (absExpr rty) := by
  obtain ⟨⟨d, kind⟩⟩ := rty
  rw [frontend.proj_rec.proj_rec_value_major.eq_def] at h
  cases kind <;>
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind, name_dup_eq] at h
  case ForallE maj_dom bo m =>
    rw [lProjRecMajor_eq (rty := absExpr (expr.Expr.mk (expr.ExprNode.mk d
      (expr.ExprKind.ForallE maj_dom bo m)))) rfl]
    obtain ⟨hmd, hbo, hm⟩ := ExprWF.forall_e_kids hrty
    obtain ⟨b, hhi, h⟩ := bind_eq_ok_iff.mp h
    have hbeq := head_is_refines ho.1 hmd hhi
    subst hbeq
    cases hb : ConLeche.Frontend.headIs (absName o.t) (absExpr maj_dom) <;>
      rw [hb] at h <;>
      simp only [Bool.false_eq_true, if_false, if_true] at h
    · rw [← Result.ok_injective h]; rfl
    · obtain ⟨a1, ha1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨a2, ha2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨a3, ha3, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨bv, hbv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨args3, hpush, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨lus2, hlc, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨app, happ, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e2, hml, hh⟩ := bind_eq_ok_iff.mp h
      have hnew : ExprsWF (alloc.vec.Vec.new expr.Expr) := fun y hy => by simp at hy
      have hnewa : absExprs (alloc.vec.Vec.new expr.Expr) = [] := by
        simp [absExprs]
      have h1 : ExprsWF a1 := append_exprs_wf hnew hparams ha1
      have h2 : ExprsWF a2 := append_exprs_wf h1 hmotives ha2
      have h3 : ExprsWF a3 := append_exprs_wf h2 hminors ha3
      have h4 : ExprsWF args3 := by
        intro y hy
        rw [vec_push_val hpush] at hy
        rcases List.mem_append.1 hy with hy1 | hy1
        · exact h3 y hy1
        · simp only [List.mem_singleton] at hy1; rw [hy1]; exact Expr.mk_bvar_wf hbv
      have hA1 := append_exprs_refines ha1
      have hA2 := append_exprs_refines ha2
      have hA3 := append_exprs_refines ha3
      have hA4 : absExprs args3 = absExprs a3 ++ [ConLeche.Expr.bvar 0] := by
        rw [ExprOps.absExprs_push hpush, Expr.mk_bvar_refines hbv]
        norm_num
      have h5 : LevelsWF lus2 := fun u hu => hlus u
        (by rw [← ExprOps.levels_copy_val hlc]; exact hu)
      have hL : absLevels lus2 = absLevels lus := by
        rw [absLevels, absLevels, ExprOps.levels_copy_val hlc]
      have h6 : ExprWF ce := Expr.mk_const_wf ho.2.2.2.1 h5 hce
      rw [← Result.ok_injective hh, Option.map_some, mk_lams_refines hml,
        (ExprOps.mk_app_n_refines h6 h4 happ).1, Expr.mk_const_refines hce, hL,
        hA4, hA3, hA2, hA1, hnewa]
      simp
  all_goals (rw [lProjRecMajor_not_forall
                   (by intro a1 b1 c1 hc; simp [absExprKind] at hc),
                 ← Result.ok_injective h]
             rfl)

/-- `proj_rec::proj_rec_value_at` refines `projRecValue`'s tail
(`ConLeche/Frontend/ProjRec.lean:290-330`), i.e. `lProjRecValueAt`. -/
theorem proj_rec_value_at_refines {o : frontend.proj_rec.ProjRecOwner}
    {l : level.Level} {r : expr.Expr}
    {lbs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {i : Std.U64}
    {res : Option expr.Expr} (ho : ProjRecOwnerWF o) (hl : LevelWF l) (hr : ExprWF r)
    (hlbs : ExprOps.BindersWF lbs)
    (h : frontend.proj_rec.proj_rec_value_at o l r lbs i = ok res) :
    Option.map absExpr res =
      lProjRecValueAt (absProjRecOwner o) (absLevel l) (absExpr r)
        (ExprOps.absBinders lbs) i.val := by
  rw [frontend.proj_rec.proj_rec_value_at] at h
  simp only [name_dup_eq, expr_dup_eq, level_dup_eq, bind_tc_ok] at h
  obtain ⟨us, hus, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨lus, hlus, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨rty0, hrty0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨params, hparams, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hUSa, hUS⟩ := StructParts.params_of_refines ho.2.1 hus
  have hV1 : LevelsWF v1 := one_level_wf hl hv1
  have hLUS : LevelsWF lus := append_levels_wf hV1 hUS hlus
  have hLUSa : absLevels lus = absLevel l :: (absNames o.lps).map ConLeche.Level.param := by
    rw [append_levels_refines hlus, one_level_refines hv1, hUSa]; rfl
  obtain ⟨hRTY0a, hRTY0⟩ :=
    ExprOps.instantiate_level_params_refines ho.2.2.2.2.1 hLUS ho.2.2.2.2.2 hrty0
  have hPARS : ExprsWF params := bvar_params_wf hparams
  have hPARSa := bvar_params_refines hparams
  have hO1 := inst_pis_open_refines hRTY0 hPARS ho1
  rw [lProjRecValueAt]
  simp only [absProjRecOwner_T, absProjRecOwner_lps, absProjRecOwner_nP,
    absProjRecOwner_ctor, absProjRecOwner_recName, absProjRecOwner_recLps,
    absProjRecOwner_recType, absProjRecOwner_numMotives, absProjRecOwner_numMinors]
  rw [← hLUSa, ← hRTY0a, ← hPARSa, ← hO1]
  cases o1 with
  | none => rw [← Result.ok_injective h]; rfl
  | some rty1 =>
    have hRTY1 : ExprWF rty1 := inst_pis_open_wf hRTY0 hPARS ho1 rty1 rfl
    simp only [Option.map_some, option_bind_some_l]
    obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
    have hO2 := build_binders_refines (mk_motive_refines ho.1 hr) (mk_motive_wf hr hl)
      hRTY1 ho2
    rw [← hO2]
    cases o2 with
    | none => rw [← Result.ok_injective h]; rfl
    | some mrt =>
      obtain ⟨hMOTS, hMRT⟩ :=
        build_binders_wf (mk_motive_wf hr hl) hRTY1 ho2 mrt.1 mrt.2 rfl
      simp only [Option.map_some, option_bind_some_l]
      replace h : (do
          let o3 ← frontend.proj_rec.build_binders
            frontend.proj_rec.MkMinor.Insts.Con_ron_coreFrontendProj_recMkBinder
            { ctor := o.ctor, i := i, l := l } o.num_minors mrt.2
          match o3 with
          | none => ok none
          | some nrt =>
            frontend.proj_rec.proj_rec_value_major o lus params mrt.1 nrt.1 lbs nrt.2)
        = ok res := h
      obtain ⟨o3, ho3, h⟩ := bind_eq_ok_iff.mp h
      have hO3 := build_binders_refines (mk_minor_refines ho.2.2.1) (mk_minor_wf hl)
        hMRT ho3
      rw [← hO3]
      cases o3 with
      | none => rw [← Result.ok_injective h]; rfl
      | some nrt =>
        obtain ⟨hMINS, hNRT⟩ :=
          build_binders_wf (mk_minor_wf hl) hMRT ho3 nrt.1 nrt.2 rfl
        simp only [Option.map_some, option_bind_some_l]
        rw [proj_rec_value_major_refines ho hLUS hPARS hMOTS hMINS hlbs hNRT h,
          hLUSa]

/-- The abstraction half of **the rewrite**
(`ConLeche/Frontend/ProjRec.lean:279-330 projRecValue`); the well-formedness
half is phase 1's `proj_rec_value_wf`. -/
private theorem proj_rec_value_abs {o : frontend.proj_rec.ProjRecOwner} {l : level.Level}
    {ty val : expr.Expr} {i : Std.U64} {res : Option expr.Expr}
    (ho : ProjRecOwnerWF o) (hl : LevelWF l) (hty : ExprWF ty) (hval : ExprWF val)
    (h : frontend.proj_rec.proj_rec_value o l ty val i = ok res) :
    Option.map absExpr res = ConLeche.Frontend.projRecValue (absProjRecOwner o)
      (absLevel l) (absExpr ty) (absExpr val) i.val := by
  rw [projRecValue_eq']
  rw [frontend.proj_rec.proj_rec_value] at h
  simp only [name_dup_eq, bind_tc_ok] at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  have hi1v : i1.val = o.n_p.val + 1 := HashMap.uscalar_add_eq hi1
  obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hSLa, hSL⟩ := ExprOps.strip_lams_refines hval ho1
  simp only [absProjRecOwner_nP, absProjRecOwner_nF, absProjRecOwner_T]
  rw [← hi1v, ← hSLa]
  cases o1 with
  | none => rw [← Result.ok_injective h]; rfl
  | some lbsb =>
    obtain ⟨hLV, hLB⟩ := hSL lbsb rfl
    obtain ⟨bv, hbv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨want, hwant, h⟩ := bind_eq_ok_iff.mp h
    have hWANT : absExpr want = .proj (absName o.t) i.val (.bvar 0) := by
      rw [Expr.proj_refines hwant, Expr.mk_bvar_refines hbv]; simp
    have hWWF : ExprWF want := Expr.proj_wf ho.1 (Expr.mk_bvar_wf hbv) hwant
    replace h : (do
        let b ← expr.beq lbsb.2 want
        if b then
          (if i ≥ o.n_f then ok (none : Option expr.Expr)
           else do
             let o2 ← expr_ops.strip_pis i1 ty
             match o2 with
             | none => ok none
             | some q => frontend.proj_rec.proj_rec_value_at o l q.2 lbsb.1 i)
        else ok none) = ok res := h
    obtain ⟨b, hbeq, h⟩ := bind_eq_ok_iff.mp h
    rw [Expr.beq_refines hLB hWWF hbeq, hWANT] at h
    simp only [Option.map_some, option_some_bind]
    by_cases hb : absExpr lbsb.2 = ConLeche.Expr.proj (absName o.t) i.val (ConLeche.Expr.bvar 0)
    · rw [if_pos (by simp [hb])] at h
      rw [if_pos hb]
      split at h
      · rename_i hge
        have hnlt : ¬ i.val < o.n_f.val := by scalar_tac
        rw [← Result.ok_injective h, if_neg hnlt]
        rfl
      · rename_i hge
        have hlt : i.val < o.n_f.val := by scalar_tac
        rw [if_pos hlt]
        obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hSPa, hSP⟩ := ExprOps.strip_pis_refines hty ho2
        rw [← hSPa]
        cases o2 with
        | none => rw [← Result.ok_injective h]; rfl
        | some q =>
          obtain ⟨-, hTB⟩ := hSP q rfl
          simp only [Option.map_some, option_some_bind]
          exact proj_rec_value_at_refines ho hl hTB hLV h
    · rw [if_neg (by simp [hb])] at h
      rw [← Result.ok_injective h, if_neg hb]
      rfl

/-- **The rewrite** (`ConLeche/Frontend/ProjRec.lean:279-330 projRecValue`):
what `export_c::proj_rewrite_d` stores in place of the parsed value.  Stated in
the shape `Refine/Frontend/StateDR.lean`'s `ProjRecSpec.projRecValue` asks for
(its `absProjOwner` is this file's `absProjRecOwner`, definitionally). -/
theorem proj_rec_value_refines (o : frontend.proj_rec.ProjRecOwner) (l : level.Level)
    (ty val : expr.Expr) (i : Std.U64) (res : Option expr.Expr)
    (ho : ProjRecOwnerWF o) (hl : LevelWF l) (hty : ExprWF ty) (hval : ExprWF val)
    (h : frontend.proj_rec.proj_rec_value o l ty val i = ok res) :
    Option.map absExpr res = ConLeche.Frontend.projRecValue (absProjRecOwner o)
        (absLevel l) (absExpr ty) (absExpr val) i.val ∧
      ∀ e, res = some e → ExprWF e :=
  ⟨proj_rec_value_abs ho hl hty hval h,
    fun _ he => proj_rec_value_wf ho hl hty hval (he ▸ h)⟩

/-! ## The artifact iota statement: its name's shape and its level

`crates/con-ron-core/src/frontend/proj_rec.rs:95-168` — the three readers
`export_c::note_proj_iota` and `export_c::proj_rewrite_d` call on a parsed
`ConstantVal`.  `text::cps_beq` has a public twin in
`Refine/Frontend/IndR.lean` (`cps_beq_refines`/`cps_beq_str`); this file is
below that one in the graph, so the two loop lemmas here are `private` copies
and the coordinator should merge them when the files meet. -/

private theorem slice_lit_val {k : Std.Usize} {S : Array Std.U32 k} {s : Slice Std.U32}
    (h : lift (Array.to_slice S) = ok s) : s.val = S.val := by
  simp only [lift_eq, Result.ok.injEq] at h
  subst h
  simp [Array.val_to_slice]

private theorem codes_inj {X Y : List Std.U32}
    (hX : ∀ c ∈ X, Nat.isValidChar c.val) (hY : ∀ c ∈ Y, Nat.isValidChar c.val)
    (h : X.map (fun c => Char.ofNat c.val) = Y.map (fun c => Char.ofNat c.val)) :
    X = Y := by
  have key : ∀ (l : List Std.U32), (∀ c ∈ l, Nat.isValidChar c.val) →
      l.map (fun c => (Char.ofNat c.val).toNat) = l.map (fun c => c.val) := by
    intro l hl
    apply List.map_congr_left
    intro c hc
    simp [Char.ofNat, Char.ofNatAux, Char.toNat, hl c hc]
  have h2 := congrArg (List.map Char.toNat) h
  simp only [List.map_map, Function.comp_def] at h2
  rw [key _ hX, key _ hY] at h2
  exact List.map_injective_iff.mpr (fun a b hab => Std.UScalar.val_eq_imp_iff.mpr hab) h2

/-! ## `proj_rec::cps_starts_with` -/

/-- The index recursion behind `proj_rec::cps_starts_with`. -/
private theorem cps_starts_with_loop_val (N : Nat) :
    ∀ (s : alloc.vec.Vec Std.U32) (lit : Slice Std.U32) (n i : Std.Usize) (b : Bool),
      n.val - i.val = N → n.val ≤ s.val.length → n.val ≤ lit.val.length →
      frontend.proj_rec.cps_starts_with_loop s lit n i = ok b →
      (b = true ↔ (s.val.take n.val).drop i.val = (lit.val.take n.val).drop i.val) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro s lit n i b hN hs hl h
    rw [frontend.proj_rec.cps_starts_with_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < n.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, hc, c2, hc2, h⟩ := h
      have hcv : s.val[i.val]'(by omega) = c := by
        have hg := ExprOps.vec_index_getElem? hc
        rw [List.getElem?_eq_getElem (by omega)] at hg
        exact Option.some_injective _ hg
      have hc2v : lit.val[i.val]'(by omega) = c2 := by
        have hg := slice_index_getElem? hc2
        rw [List.getElem?_eq_getElem (by omega)] at hg
        exact Option.some_injective _ hg
      have hds : (s.val.take n.val).drop i.val = c :: (s.val.take n.val).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simp; omega)]
        simp [hcv]
      have hdl : (lit.val.take n.val).drop i.val
          = c2 :: (lit.val.take n.val).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simp; omega)]
        simp [hc2v]
      rw [hds, hdl]
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
        have hceq : c = c2 := Std.UScalar.val_eq_imp_iff.mpr (by simpa using hne)
        rw [ih (n.val - i2.val) (by omega) s lit n i2 b rfl hs hl h, hi2v]
        simp [hceq]
    · rename_i hge
      have hle : n.val ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h]
      rw [List.drop_eq_nil_of_le (by simp; omega), List.drop_eq_nil_of_le (by simp; omega)]
      simp

/-- `proj_rec::cps_starts_with` is list prefixhood of the code points. -/
theorem cps_starts_with_refines {s : alloc.vec.Vec Std.U32} {lit : Slice Std.U32}
    {b : Bool} (h : frontend.proj_rec.cps_starts_with s lit = ok b) :
    (b = true ↔ lit.val <+: s.val) := by
  rw [frontend.proj_rec.cps_starts_with] at h
  split at h
  · rename_i hlt
    have hll : s.val.length < lit.val.length := by
      have := alloc.vec.Vec.len_val s
      have := Slice.len_val lit
      scalar_tac
    rw [← Result.ok_injective h]
    simp only [Bool.false_eq_true, false_iff]
    intro hc
    exact absurd hc.length_le (by omega)
  · rename_i hge
    have hll : lit.val.length ≤ s.val.length := by
      have := alloc.vec.Vec.len_val s
      have := Slice.len_val lit
      scalar_tac
    have hn : (Slice.len lit).val = lit.val.length := Slice.len_val lit
    have hh := cps_starts_with_loop_val _ s lit (Slice.len lit) 0#usize b rfl
      (by omega) (by omega) h
    rw [show ((0#usize : Std.Usize)).val = 0 by scalar_tac] at hh
    simp only [List.drop_zero, hn, List.take_of_length_le (le_refl _)] at hh
    rw [hh, List.prefix_iff_eq_take]
    constructor
    · intro hc; exact hc.symm
    · intro hc; exact hc.symm

/-- `proj_rec::cps_starts_with` against Lean's `String.startsWith`. -/
theorem cps_starts_with_str {s : alloc.vec.Vec Std.U32} {lit : Slice Std.U32}
    {b : Bool} (hs : StrWF s) (hL : ∀ c ∈ lit.val, Nat.isValidChar c.val)
    (h : frontend.proj_rec.cps_starts_with s lit = ok b) :
    b = (absString s).startsWith (absCodes lit.val) := by
  have hpre := cps_starts_with_refines h
  have hstr : (absString s).startsWith (absCodes lit.val) = true ↔ lit.val <+: s.val := by
    rw [String.startsWith_string_iff]
    simp only [absCodes, absString, String.toList_ofList]
    constructor
    · intro hc
      have h1 := List.prefix_iff_eq_take.mp hc
      simp only [List.length_map, ← List.map_take] at h1
      exact List.prefix_iff_eq_take.mpr
        (codes_inj hL (fun c hc' => hs c (List.mem_of_mem_take hc')) h1)
    · intro hc
      exact hc.map _
  rw [Bool.eq_iff_iff, hpre, hstr]


/-! ## `text::cat` -/

/-- The index recursion behind `text::cat`: it copies `b[i..n)` onto `out`. -/
private theorem cat_loop_val (N : Nat) :
    ∀ (b out : alloc.vec.Vec Std.U32) (n i : Std.Usize) (r : alloc.vec.Vec Std.U32),
      n.val - i.val = N → n.val ≤ b.val.length → i.val ≤ n.val →
      frontend.text.cat_loop b out n i = ok r →
      r.val = out.val ++ (b.val.take n.val).drop i.val := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro b out n i r hN hnb hin h
    rw [frontend.text.cat_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < n.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hx, out1, hpush, i2, hi2, h⟩ := h
      have hxv : b.val[i.val]'(by omega) = x := by
        have hg := ExprOps.vec_index_getElem? hx
        rw [List.getElem?_eq_getElem (by omega)] at hg
        exact Option.some_injective _ hg
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      rw [ih (n.val - i2.val) (by omega) b out1 n i2 r rfl hnb (by omega) h, hi2v,
        vec_push_val hpush]
      rw [List.drop_eq_getElem_cons (show i.val < (b.val.take n.val).length by simp; omega)]
      simp [hxv]
    · rename_i hge
      have hle : n.val ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h,
        List.drop_eq_nil_of_le (by simp; omega)]
      simp

/-- `text::cat` is list append (`ConLeche/Frontend/ProjRec.lean:110-114
projIotaName`, the `"proj_" ++ toString i` component). -/
theorem cat_val {a b r : alloc.vec.Vec Std.U32} (h : frontend.text.cat a b = ok r) :
    r.val = a.val ++ b.val := by
  rw [frontend.text.cat] at h
  have hn : (alloc.vec.Vec.len b).val = b.val.length := alloc.vec.Vec.len_val b
  rw [cat_loop_val _ b a (alloc.vec.Vec.len b) 0#usize r rfl (by omega) (by scalar_tac) h]
  simp [show ((0#usize : Std.Usize)).val = 0 by scalar_tac, hn]

/-! ## `text::u64_str` -/

/-- The digit recursion behind `text::u64_str`: the accumulator holds the
digits least significant first, so read backwards it is `Nat.toDigits`. -/
private theorem u64_str_loop0_val (N : Nat) :
    ∀ (rev : alloc.vec.Vec Std.U32) (k : Std.U64) (r : alloc.vec.Vec Std.U32),
      k.val = N → frontend.text.u64_str_loop0 rev k = ok r →
      r.val.reverse.map (fun c => Char.ofNat c.val)
        = (if k.val = 0 then [] else Nat.toDigits 10 k.val)
          ++ rev.val.reverse.map (fun c => Char.ofNat c.val) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro rev k r hN h
    rw [frontend.text.u64_str_loop0.eq_def] at h
    split at h
    · rename_i hgt
      have hkv : 0 < k.val := by scalar_tac
      simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, exists_eq_left'] at h
      obtain ⟨m, hm, d, hd, rev1, hpush, k1, hk1, hrec⟩ := h
      have h10 : ((10#u64 : Std.U64)).val ≠ 0 := by decide
      have hmv : m.val = k.val % 10 := by rw [CoreK.uscalar_rem_eq h10 hm]; rfl
      have hmlt : m.val < 10 := by rw [hmv]; omega
      have hdv : d.val = 48 + m.val := by
        rw [HashMap.uscalar_add_eq hd, CoreK.u64_cast_u32_val_of_lt_ten hmlt]; rfl
      have hk1v : k1.val = k.val / 10 := by rw [HashMap.uscalar_div_eq hk1]; rfl
      have hdc : Char.ofNat d.val = Nat.digitChar (k.val % 10) := by
        rw [hdv, hmv, ← Nat.toNat_digitChar_of_lt_ten (n := k.val % 10) (by omega),
          Char.ofNat_toNat]
      rw [ih k1.val (by rw [hk1v, ← hN]; omega) rev1 k1 r rfl hrec, hk1v,
        vec_push_val hpush]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.map_cons, List.cons_append]
      by_cases hlt : k.val < 10
      · have hz : k.val / 10 = 0 := by omega
        rw [hz]
        simp only [if_neg (by omega : ¬ k.val = 0)]
        rw [Nat.toDigits_of_lt_base hlt, hdc, Nat.mod_eq_of_lt hlt]
        simp
      · have hz : ¬ (k.val / 10 = 0) := by omega
        have hD : Nat.toDigits 10 k.val
            = Nat.toDigits 10 (k.val / 10) ++ [Nat.digitChar (k.val % 10)] :=
          Nat.toDigits_of_base_le (b := 10) (by omega) (by omega)
        rw [if_neg hz, if_neg (by omega : ¬ k.val = 0), hD, hdc]
        simp
    · rename_i hge
      have hkv : k.val = 0 := by scalar_tac
      rw [← Result.ok_injective h, if_pos hkv]
      simp

/-- The copy-back recursion behind `text::u64_str`: it reverses `rev[0..i)`
onto `out`. -/
private theorem u64_str_loop1_val (N : Nat) :
    ∀ (rev out r : alloc.vec.Vec Std.U32) (i : Std.Usize),
      i.val = N → i.val ≤ rev.val.length →
      frontend.text.u64_str_loop1 rev out i = ok r →
      r.val = out.val ++ (rev.val.take i.val).reverse := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro rev out r i hN hi h
    rw [frontend.text.u64_str_loop1.eq_def] at h
    split at h
    · rename_i hgt
      have hiv : 0 < i.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i1, hi1, x, hx, out1, hpush, hrec⟩ := h
      have hi1v : i1.val = i.val - 1 := by
        rw [HashMap.uscalar_sub_eq hi1]; scalar_tac
      have hxv : rev.val[i1.val]'(by omega) = x := by
        have hg := ExprOps.vec_index_getElem? hx
        rw [List.getElem?_eq_getElem (by omega)] at hg
        exact Option.some_injective _ hg
      rw [ih i1.val (by omega) rev out1 r i1 rfl (by omega) hrec, vec_push_val hpush]
      have htk : rev.val.take i.val = rev.val.take i1.val ++ [rev.val[i1.val]'(by omega)] := by
        rw [show i.val = i1.val + 1 by omega, List.take_add_one]
        simp [List.getElem?_eq_getElem (show i1.val < rev.val.length by omega)]
      rw [htk, hxv]
      simp
    · rename_i hge
      have hiv : i.val = 0 := by scalar_tac
      rw [← Result.ok_injective h, hiv]
      simp

/-- `text::u64_str` is Lean's `toString` on the index
(`ConLeche/Frontend/ProjRec.lean:110-114 projIotaName`). -/
theorem u64_str_refines {i : Std.U64} {s : alloc.vec.Vec Std.U32}
    (h : frontend.text.u64_str i = ok s) : absCodes s.val = toString i.val := by
  rw [frontend.text.u64_str] at h
  have hgoal : s.val.map (fun c => Char.ofNat c.val) = Nat.toDigits 10 i.val := by
    split at h
    · rename_i hz
      have hzv : i.val = 0 := by scalar_tac
      rw [vec_push_val h]
      simp [hzv]
    · rename_i hz
      have hzv : i.val ≠ 0 := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨rev, hrev, h⟩ := h
      have hnew : (alloc.vec.Vec.new Std.U32).val = [] := rfl
      have hwc : (alloc.vec.Vec.with_capacity Std.U32 (alloc.vec.Vec.len rev)).val = [] := rfl
      have h0 := u64_str_loop0_val i.val (alloc.vec.Vec.new Std.U32) i rev rfl hrev
      rw [if_neg hzv, hnew] at h0
      simp only [List.reverse_nil, List.map_nil, List.append_nil] at h0
      have hn : (alloc.vec.Vec.len rev).val = rev.val.length := alloc.vec.Vec.len_val rev
      rw [u64_str_loop1_val _ rev _ s (alloc.vec.Vec.len rev) rfl (by omega) h, hwc, hn,
        List.take_of_length_le (le_refl _), List.nil_append]
      exact h0
  rw [absCodes, hgoal, Nat.toString_eq_ofList_toDigits]


/-- `proj_rec::proj_iota_name` refines `projIotaName`
(`ConLeche/Frontend/ProjRec.lean:106-111 projIotaName`): the model family's
constructor-reduction theorem for field `i` of `T`, `T._model.proj_i.iota`. -/
theorem proj_iota_name_refines (t : name.Name) (ht : NameWF t) :
    ∀ (i : Std.U64) n, frontend.proj_rec.proj_iota_name t i = ok n →
      absName n = ConLeche.Frontend.projIotaName (absName t) i.val ∧ NameWF n := by
  intro i n h
  rw [frontend.proj_rec.proj_iota_name] at h
  simp only [name_dup_eq, lift_eq, bind_tc_ok, bind_eq_ok_iff] at h
  obtain ⟨v, hv, a, ha, v1, hv1, v2, hv2, v3, hv3, b, hb, v4, hv4, hmk⟩ := h
  obtain ⟨haabs, hawf⟩ := str_lit_step ht (lift_eq _) hv ha
    (L := [95#u32, 109#u32, 111#u32, 100#u32, 101#u32, 108#u32])
    (by simp [frontend.proj_rec.proj_iota_name.MODEL]) (by decide)
  have hv1v : v1.val = [112#u32, 114#u32, 111#u32, 106#u32, 95#u32] := by
    rw [code_points_val hv1, Array.val_to_slice]
    simp [frontend.proj_rec.proj_iota_name.PROJ]
  have hv1s : StrWF v1 := by rw [StrWF]; rw [hv1v]; decide
  have hbwf : NameWF b := Name.mk_str_wf hawf (cat_wf hv1s (u64_str_wf hv2) hv3) hb
  obtain ⟨hnabs, hnwf⟩ := str_lit_step hbwf (lift_eq _) hv4 hmk
    (L := [105#u32, 111#u32, 116#u32, 97#u32])
    (by simp [frontend.proj_rec.proj_iota_name.IOTA]) (by decide)
  refine ⟨?_, hnwf⟩
  rw [hnabs, Name.mk_str_refines hb, haabs, absString_eq, cat_val hv3,
    CoreK.absCodes_append, hv1v, u64_str_refines hv2]
  rfl

/-! ## `text::cps_beq` -/

private theorem cps_beq_loop_val (N : Nat) :
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
      have hcv : s.val[i.val]'(by omega) = c := by
        have hg := ExprOps.vec_index_getElem? hc
        rw [List.getElem?_eq_getElem (by omega)] at hg
        exact Option.some_injective _ hg
      have hc2v : lit.val[i.val]'(by omega) = c2 := by
        have hg := slice_index_getElem? hc2
        rw [List.getElem?_eq_getElem (by omega)] at hg
        exact Option.some_injective _ hg
      have hds : s.val.drop i.val = c :: s.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (show i.val < s.val.length by omega), hcv]
      have hdl : lit.val.drop i.val = c2 :: lit.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (show i.val < lit.val.length by omega), hc2v]
      rw [hds, hdl]
      split at h
      · rename_i hne
        simp only [Result.ok.injEq] at h
        have hval : ¬ (c.val = c2.val) := by simpa using hne
        have hcc : c ≠ c2 := fun hq => hval (congrArg Std.UScalar.val hq)
        simp [← h, hcc]
      · rename_i hne
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i2, hi2, h⟩ := h
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        have hceq : c = c2 := Std.UScalar.val_eq_imp_iff.mpr (by simpa using hne)
        rw [ih (s.val.length - i2.val) (by omega) s lit n i2 b rfl hn hlen h, hi2v]
        simp [hceq]
    · rename_i hge
      have hle : s.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h]
      rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
      simp

private theorem cps_beq_val {s : alloc.vec.Vec Std.U32} {lit : Slice Std.U32} {b : Bool}
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
    have hh := cps_beq_loop_val _ s lit _ 0#usize b rfl (by simp [alloc.vec.Vec.len]) hl h
    simpa [show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using hh

private theorem cps_beq_codes {s : alloc.vec.Vec Std.U32} {lit : Slice Std.U32} {b : Bool}
    (hs : StrWF s) (hL : ∀ c ∈ lit.val, Nat.isValidChar c.val)
    (h : frontend.text.cps_beq s lit = ok b) :
    (b = true ↔ absString s = absCodes lit.val) := by
  rw [cps_beq_val h]
  constructor
  · intro hq; rw [absString_eq, hq]
  · intro hq
    simp only [absString_eq, absCodes] at hq
    exact codes_inj hs hL (String.ofList_inj.mp hq)

/-! ## `isProjIotaName`, unfolded -/

private theorem isProjIotaName_str3 (p : ConLeche.Name) (m sfx l : String) :
    ConLeche.Frontend.isProjIotaName (.str (.str (.str p m) sfx) l)
      = (decide (l = "iota") && decide (m = "_model") && sfx.startsWith "proj_") := by
  by_cases hl : l = "iota" <;> by_cases hm : m = "_model" <;>
    simp_all [ConLeche.Frontend.isProjIotaName]

private theorem isProjIotaName_ne_iota {p : ConLeche.Name} {l : String} (h : l ≠ "iota") :
    ConLeche.Frontend.isProjIotaName (.str p l) = false := by
  rcases p with _ | ⟨q, sfx⟩ | ⟨q, k⟩
  · simp [ConLeche.Frontend.isProjIotaName]
  · rcases q with _ | ⟨r, m⟩ | ⟨r, k2⟩
    · simp [ConLeche.Frontend.isProjIotaName]
    · rw [isProjIotaName_str3]; simp [h]
    · simp [ConLeche.Frontend.isProjIotaName]
  · simp [ConLeche.Frontend.isProjIotaName]

private theorem isProjIotaName_anon (l : String) :
    ConLeche.Frontend.isProjIotaName (.str .anonymous l) = false := by
  simp [ConLeche.Frontend.isProjIotaName]

private theorem isProjIotaName_num (q : ConLeche.Name) (k : Nat) (l : String) :
    ConLeche.Frontend.isProjIotaName (.str (.num q k) l) = false := by
  simp [ConLeche.Frontend.isProjIotaName]

private theorem isProjIotaName_anon2 (sfx l : String) :
    ConLeche.Frontend.isProjIotaName (.str (.str .anonymous sfx) l) = false := by
  simp [ConLeche.Frontend.isProjIotaName]

private theorem isProjIotaName_num2 (q : ConLeche.Name) (k : Nat) (sfx l : String) :
    ConLeche.Frontend.isProjIotaName (.str (.str (.num q k) sfx) l) = false := by
  simp [ConLeche.Frontend.isProjIotaName]

/-! ## `proj_rec::is_proj_iota_name` -/

/-- `proj_rec::is_proj_iota_name` refines `isProjIotaName`
(`ConLeche/Frontend/ProjRec.lean:113-118 isProjIotaName`). -/
theorem is_proj_iota_name_refines (n : name.Name) (hn : NameWF n) :
    ∀ b, frontend.proj_rec.is_proj_iota_name n = ok b →
      b = ConLeche.Frontend.isProjIotaName (absName n) := by
  intro b h
  rw [frontend.proj_rec.is_proj_iota_name] at h
  obtain ⟨⟨d, k⟩⟩ := n
  cases k <;> simp only [arc_deref_eq, bind_tc_ok, CoreK.name_node_kind] at h <;>
    simp only [absName_mk, absNameKind]
  case Anonymous => rw [← Result.ok_injective h]; simp [ConLeche.Frontend.isProjIotaName]
  case Num pre m => rw [← Result.ok_injective h]; simp [ConLeche.Frontend.isProjIotaName]
  case Str p1 last =>
    obtain ⟨hp1wf, hlastwf⟩ := NameWF.str_kids hn
    simp only [bind_eq_ok_iff] at h
    obtain ⟨sl, hsl, b1, hb1, h⟩ := h
    have hslv : sl.val = [105#u32, 111#u32, 116#u32, 97#u32] := by
      rw [slice_lit_val hsl]; simp [frontend.proj_rec.is_proj_iota_name.IOTA]
    have hiota : (b1 = true ↔ absString last = "iota") := by
      rw [cps_beq_codes hlastwf (by rw [hslv]; decide) hb1, hslv]; rfl
    split at h
    · rename_i hb1t
      obtain ⟨⟨d1, k1⟩⟩ := p1
      cases k1 <;> simp only [CoreK.name_node_kind] at h <;>
        simp only [absName_mk, absNameKind]
      case Anonymous => rw [← Result.ok_injective h, isProjIotaName_anon]
      case Num q j => rw [← Result.ok_injective h, isProjIotaName_num]
      case Str p2 s1 =>
        obtain ⟨hp2wf, hs1wf⟩ := NameWF.str_kids hp1wf
        obtain ⟨⟨d2, k2⟩⟩ := p2
        cases k2 <;> simp only [CoreK.name_node_kind] at h <;>
          simp only [absName_mk, absNameKind]
        case Anonymous => rw [← Result.ok_injective h, isProjIotaName_anon2]
        case Num q j => rw [← Result.ok_injective h, isProjIotaName_num2]
        case Str p3 m =>
          obtain ⟨hp3wf, hmwf⟩ := NameWF.str_kids hp2wf
          simp only [bind_eq_ok_iff] at h
          obtain ⟨sl2, hsl2, b2, hb2, h⟩ := h
          have hsl2v : sl2.val = [95#u32, 109#u32, 111#u32, 100#u32, 101#u32, 108#u32] := by
            rw [slice_lit_val hsl2]; simp [frontend.proj_rec.is_proj_iota_name.MODEL]
          have hmodel : (b2 = true ↔ absString m = "_model") := by
            rw [cps_beq_codes hmwf (by rw [hsl2v]; decide) hb2, hsl2v]; rfl
          rw [isProjIotaName_str3]
          split at h
          · rename_i hb2t
            simp only [bind_eq_ok_iff] at h
            obtain ⟨sl3, hsl3, h⟩ := h
            have hsl3v : sl3.val = [112#u32, 114#u32, 111#u32, 106#u32, 95#u32] := by
              rw [slice_lit_val hsl3]; simp [frontend.proj_rec.is_proj_iota_name.PROJ]
            have hstart := cps_starts_with_str hs1wf (by rw [hsl3v]; decide) h
            rw [hstart, hsl3v]
            rw [hiota.mp hb1t, hmodel.mp hb2t]
            simp
            rfl
          · rename_i hb2f
            have hne : absString m ≠ "_model" := fun hc => hb2f (hmodel.mpr hc)
            rw [← Result.ok_injective h]
            simp [hne]
    · rename_i hb1f
      have hne : absString last ≠ "iota" := fun hc => hb1f (hiota.mpr hc)
      rw [← Result.ok_injective h, isProjIotaName_ne_iota hne]

/-- `proj_rec::proj_iota_level` refines `projIotaLevel`
(`ConLeche/Frontend/ProjRec.lean:120-125 projIotaLevel`). -/
theorem proj_iota_level_refines (ty : expr.Expr) (hty : ExprWF ty) :
    ∀ o, frontend.proj_rec.proj_iota_level ty = ok o →
      Option.map absLevel o = ConLeche.Frontend.projIotaLevel (absExpr ty) ∧
        ∀ l, o = some l → LevelWF l := by
  intro o h
  rw [frontend.proj_rec.proj_iota_level] at h
  obtain ⟨pr, hpr, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpra, hprwf⟩ := ExprOps.pi_result_refines hty hpr
  obtain ⟨hd, hfn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hfa, hfwf⟩ := ExprOps.get_app_fn_refines hprwf hfn
  rw [ConLeche.Frontend.projIotaLevel, ← hpra, ← hfa]
  obtain ⟨⟨d, k⟩⟩ := hd
  cases k <;>
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h <;>
    simp only [absExpr_mk, absExprKind]
  case Const n us =>
    obtain ⟨hnwf, huswf⟩ := ExprWF.const_kids hfwf
    split at h
    · rename_i hlen
      have hlv : us.val.length = 1 := by
        have := alloc.vec.Vec.len_val us
        scalar_tac
      obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp hlv
      simp only [absLevels, hu, List.map_cons, List.map_nil]
      obtain ⟨en, hen, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hena, henwf⟩ := BasisNames.eq_name_refines hen
      obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
      have hbv : b = decide (absName n = ConLeche.eqName) := by
        rw [Name.beq_refines hnwf henwf hb, hena]
      split at h
      · rename_i hbt
        rw [hbv] at hbt
        obtain ⟨l, hl, h⟩ := bind_eq_ok_iff.mp h
        have hlu : l = u := by
          have hg := ExprOps.vec_index_getElem? hl
          rw [hu] at hg
          simpa using hg.symm
        subst hlu
        simp only [level_dup_eq, bind_tc_ok, Result.ok.injEq] at h
        subst o
        have hdec : (decide (absName n = ConLeche.eqName)) = true := by
          simpa using hbt
        simp only [beq_iff_eq, of_decide_eq_true hdec]
        exact ⟨rfl, fun l' hl' => by
          cases hl'
          exact huswf _ (by rw [hu]; simp)⟩
      · rename_i hbf
        rw [hbv] at hbf
        have hne : ¬ (absName n = ConLeche.eqName) := by
          intro hc; exact hbf (by simp [hc])
        rw [← Result.ok_injective h]
        simp only [beq_iff_eq, if_neg hne, Option.map_none]
        simp
    · rename_i hlen
      have hlv : us.val.length ≠ 1 := by
        have := alloc.vec.Vec.len_val us
        intro hc
        exact hlen (by scalar_tac)
      rw [← Result.ok_injective h]
      refine ⟨?_, by simp⟩
      simp only [absLevels, Option.map_none]
      rcases hl : us.val with _ | ⟨x, xs⟩
      · simp
      · rcases xs with _ | ⟨y, ys⟩
        · exact absurd (by rw [hl]; rfl) hlv
        · simp
  all_goals (rw [← Result.ok_injective h]; exact ⟨rfl, by simp⟩)

/-! ## `occursConst`, memoised

The port drops con-leche's budgeted descent (`occursConstB`) and runs the
memoised walk alone (the module note of `proj_rec.rs`), so what it computes is
`occursConstGo n {} e`.  This section proves the port's walk against the *pure*
`occursConst` under the memo invariant "a recorded key does not mention `n`". -/

/-- The memo's meaning (`ConLeche/Frontend/ProjRec.lean:180-225 occursConstGo`):
only `false` is ever recorded, and it is recorded for subterms that really do
not mention `n`. -/
def OccQ (lm : ConLeche.Name) (a : ConLeche.Expr) (b : Bool) : Prop :=
  b = false ∧ ConLeche.Frontend.occursConst lm a = false

/-- A memo hit is a subterm already shown not to mention `n`. -/
theorem occ_hit {n : name.Name} {seen : ron.hashmap.HashMap expr.Expr Bool}
    {e : expr.Expr} {b : Bool}
    (hm : ExprOps.MemoInv ExprWF absExpr (OccQ (absName n)) seen) (he : ExprWF e)
    (h : ron.hashmap.HashMap.contains_key expr.Expr.Insts.Con_ron_coreRonHashmapHashable
      expr.Expr.Insts.Con_ron_coreRonHashmapEq2 seen e = ok b) :
    b = true → ConLeche.Frontend.occursConst (absName n) (absExpr e) = false := by
  rw [ron.hashmap.HashMap.contains_key] at h
  obtain ⟨o, hget, hb⟩ := bind_eq_ok_iff.mp h
  cases o with
  | none => intro hbt; rw [← Result.ok_injective hb] at hbt; simp at hbt
  | some v =>
    intro _
    exact (ExprOps.hit' hget hm ExprOps.expr_key_exact he).2

/-- Recording a `false` keeps the invariant. -/
theorem occ_set {n : name.Name} {seen seen' : ron.hashmap.HashMap expr.Expr Bool}
    {e : expr.Expr} {old : Option Bool}
    (hm : ExprOps.MemoInv ExprWF absExpr (OccQ (absName n)) seen) (he : ExprWF e)
    (hq : ConLeche.Frontend.occursConst (absName n) (absExpr e) = false)
    (h : ron.hashmap.HashMap.insert expr.Expr.Insts.Con_ron_coreRonHashmapHashable
      expr.Expr.Insts.Con_ron_coreRonHashmapEq2 seen e false = ok (old, seen')) :
    ExprOps.MemoInv ExprWF absExpr (OccQ (absName n)) seen' :=
  ExprOps.set' h hm ExprOps.expr_key_exact he ⟨rfl, hq⟩

/-- `proj_rec::occurs_const_go`/`occurs_const_node` refine `occursConst`
(`ConLeche/Frontend/ProjRec.lean:127-136 occursConst`), the memo invariant
threaded through. -/
theorem occurs_const_go_refines {n : name.Name} (hn : NameWF n)
    (e : expr.Expr) (he : ExprWF e) :
    ∀ (seen : ron.hashmap.HashMap expr.Expr Bool)
      (r : Bool × ron.hashmap.HashMap expr.Expr Bool),
      ExprOps.MemoInv ExprWF absExpr (OccQ (absName n)) seen →
      frontend.proj_rec.occurs_const_go n seen e = ok r →
      r.1 = ConLeche.Frontend.occursConst (absName n) (absExpr e) ∧
        ExprOps.MemoInv ExprWF absExpr (OccQ (absName n)) r.2 := by
  induction e, he using ExprWF.ind_node with
  | bvar d i hwf =>
    intro seen r hm h
    rw [frontend.proj_rec.occurs_const_go.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    exact ⟨rfl, hm⟩
  | fvar d idx ty hwf ihty =>
    intro seen r hm h
    rw [frontend.proj_rec.occurs_const_go.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    exact ⟨rfl, hm⟩
  | sort d u hwf =>
    intro seen r hm h
    rw [frontend.proj_rec.occurs_const_go.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    exact ⟨rfl, hm⟩
  | lit d lt hwf =>
    intro seen r hm h
    rw [frontend.proj_rec.occurs_const_go.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    rw [← Result.ok_injective h]
    exact ⟨rfl, hm⟩
  | mk_const d m us hwf =>
    intro seen r hm h
    rw [frontend.proj_rec.occurs_const_go.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨b, hbeq, h⟩ := bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    refine ⟨?_, hm⟩
    rw [Name.beq_refines (ExprWF.const_kids hwf).1 hn hbeq]
    rfl
  | app d f a hwf ihf iha =>
    intro seen r hm h
    obtain ⟨hf, ha⟩ := ExprWF.app_kids hwf
    rw [frontend.proj_rec.occurs_const_go.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨bc, hcont, h⟩ := bind_eq_ok_iff.mp h
    cases bc with
    | true =>
      simp only [if_true] at h
      rw [← Result.ok_injective h]
      exact ⟨(occ_hit hm hwf hcont rfl).symm, hm⟩
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨p, hnode, h⟩ := bind_eq_ok_iff.mp h
      replace h : (if p.1 then ok (true, p.2)
        else do
          let e1 ← expr.dup (expr.Expr.mk (expr.ExprNode.mk d (expr.ExprKind.App f a)))
          let q ← ron.hashmap.HashMap.insert
            expr.Expr.Insts.Con_ron_coreRonHashmapHashable
            expr.Expr.Insts.Con_ron_coreRonHashmapEq2 p.2 e1 false
          ok (false, q.2)) = ok r := h
      rw [frontend.proj_rec.occurs_const_node.eq_def] at hnode
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at hnode
      obtain ⟨q, hq, hnode⟩ := bind_eq_ok_iff.mp hnode
      replace hnode : (if q.1 then ok (true, q.2)
        else frontend.proj_rec.occurs_const_go n q.2 a) = ok p := hnode
      obtain ⟨hq1, hq2⟩ := ihf hf seen q hm hq
      cases hqb : q.1 with
      | true =>
        rw [hqb] at hnode
        simp only [if_true] at hnode
        rw [← Result.ok_injective hnode] at h
        simp only [if_true] at h
        rw [← Result.ok_injective h]
        rw [hqb] at hq1
        exact ⟨by simp [ConLeche.Frontend.occursConst, ← hq1], hq2⟩
      | false =>
        rw [hqb] at hnode
        simp only [Bool.false_eq_true, if_false] at hnode
        obtain ⟨hp1, hp2⟩ := iha ha q.2 p hq2 hnode
        rw [hqb] at hq1
        cases hpb : p.1 with
        | true =>
          rw [hpb] at h
          simp only [if_true] at h
          rw [← Result.ok_injective h]
          rw [hpb] at hp1
          exact ⟨by simp [ConLeche.Frontend.occursConst, ← hq1, ← hp1], hp2⟩
        | false =>
          rw [hpb] at h
          simp only [Bool.false_eq_true, if_false, expr_dup_eq, bind_tc_ok] at h
          obtain ⟨w, hins, h⟩ := bind_eq_ok_iff.mp h
          rw [hpb] at hp1
          have hocc : ConLeche.Frontend.occursConst (absName n)
              (absExpr (expr.Expr.mk (expr.ExprNode.mk d
                (expr.ExprKind.App f a)))) = false := by
            simp [ConLeche.Frontend.occursConst, ← hq1, ← hp1]
          rw [← Result.ok_injective h]
          exact ⟨hocc.symm, occ_set (old := w.1) (seen' := w.2) hp2 hwf hocc hins⟩
  | lam d ty bo bm hwf ihty ihbo =>
    intro seen r hm h
    obtain ⟨hty, hbo, -⟩ := ExprWF.lam_kids hwf
    rw [frontend.proj_rec.occurs_const_go.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨bc, hcont, h⟩ := bind_eq_ok_iff.mp h
    cases bc with
    | true =>
      simp only [if_true] at h
      rw [← Result.ok_injective h]
      exact ⟨(occ_hit hm hwf hcont rfl).symm, hm⟩
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨p, hnode, h⟩ := bind_eq_ok_iff.mp h
      replace h : (if p.1 then ok (true, p.2)
        else do
          let e1 ← expr.dup (expr.Expr.mk (expr.ExprNode.mk d
            (expr.ExprKind.Lam ty bo bm)))
          let q ← ron.hashmap.HashMap.insert
            expr.Expr.Insts.Con_ron_coreRonHashmapHashable
            expr.Expr.Insts.Con_ron_coreRonHashmapEq2 p.2 e1 false
          ok (false, q.2)) = ok r := h
      rw [frontend.proj_rec.occurs_const_node.eq_def] at hnode
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at hnode
      obtain ⟨q, hq, hnode⟩ := bind_eq_ok_iff.mp hnode
      replace hnode : (if q.1 then ok (true, q.2)
        else frontend.proj_rec.occurs_const_go n q.2 bo) = ok p := hnode
      obtain ⟨hq1, hq2⟩ := ihty hty seen q hm hq
      cases hqb : q.1 with
      | true =>
        rw [hqb] at hnode
        simp only [if_true] at hnode
        rw [← Result.ok_injective hnode] at h
        simp only [if_true] at h
        rw [← Result.ok_injective h]
        rw [hqb] at hq1
        exact ⟨by simp [ConLeche.Frontend.occursConst, ← hq1], hq2⟩
      | false =>
        rw [hqb] at hnode
        simp only [Bool.false_eq_true, if_false] at hnode
        obtain ⟨hp1, hp2⟩ := ihbo hbo q.2 p hq2 hnode
        rw [hqb] at hq1
        cases hpb : p.1 with
        | true =>
          rw [hpb] at h
          simp only [if_true] at h
          rw [← Result.ok_injective h]
          rw [hpb] at hp1
          exact ⟨by simp [ConLeche.Frontend.occursConst, ← hq1, ← hp1], hp2⟩
        | false =>
          rw [hpb] at h
          simp only [Bool.false_eq_true, if_false, expr_dup_eq, bind_tc_ok] at h
          obtain ⟨w, hins, h⟩ := bind_eq_ok_iff.mp h
          rw [hpb] at hp1
          have hocc : ConLeche.Frontend.occursConst (absName n)
              (absExpr (expr.Expr.mk (expr.ExprNode.mk d
                (expr.ExprKind.Lam ty bo bm)))) = false := by
            simp [ConLeche.Frontend.occursConst, ← hq1, ← hp1]
          rw [← Result.ok_injective h]
          exact ⟨hocc.symm, occ_set (old := w.1) (seen' := w.2) hp2 hwf hocc hins⟩
  | forall_e d ty bo bm hwf ihty ihbo =>
    intro seen r hm h
    obtain ⟨hty, hbo, -⟩ := ExprWF.forall_e_kids hwf
    rw [frontend.proj_rec.occurs_const_go.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨bc, hcont, h⟩ := bind_eq_ok_iff.mp h
    cases bc with
    | true =>
      simp only [if_true] at h
      rw [← Result.ok_injective h]
      exact ⟨(occ_hit hm hwf hcont rfl).symm, hm⟩
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨p, hnode, h⟩ := bind_eq_ok_iff.mp h
      replace h : (if p.1 then ok (true, p.2)
        else do
          let e1 ← expr.dup (expr.Expr.mk (expr.ExprNode.mk d
            (expr.ExprKind.ForallE ty bo bm)))
          let q ← ron.hashmap.HashMap.insert
            expr.Expr.Insts.Con_ron_coreRonHashmapHashable
            expr.Expr.Insts.Con_ron_coreRonHashmapEq2 p.2 e1 false
          ok (false, q.2)) = ok r := h
      rw [frontend.proj_rec.occurs_const_node.eq_def] at hnode
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at hnode
      obtain ⟨q, hq, hnode⟩ := bind_eq_ok_iff.mp hnode
      replace hnode : (if q.1 then ok (true, q.2)
        else frontend.proj_rec.occurs_const_go n q.2 bo) = ok p := hnode
      obtain ⟨hq1, hq2⟩ := ihty hty seen q hm hq
      cases hqb : q.1 with
      | true =>
        rw [hqb] at hnode
        simp only [if_true] at hnode
        rw [← Result.ok_injective hnode] at h
        simp only [if_true] at h
        rw [← Result.ok_injective h]
        rw [hqb] at hq1
        exact ⟨by simp [ConLeche.Frontend.occursConst, ← hq1], hq2⟩
      | false =>
        rw [hqb] at hnode
        simp only [Bool.false_eq_true, if_false] at hnode
        obtain ⟨hp1, hp2⟩ := ihbo hbo q.2 p hq2 hnode
        rw [hqb] at hq1
        cases hpb : p.1 with
        | true =>
          rw [hpb] at h
          simp only [if_true] at h
          rw [← Result.ok_injective h]
          rw [hpb] at hp1
          exact ⟨by simp [ConLeche.Frontend.occursConst, ← hq1, ← hp1], hp2⟩
        | false =>
          rw [hpb] at h
          simp only [Bool.false_eq_true, if_false, expr_dup_eq, bind_tc_ok] at h
          obtain ⟨w, hins, h⟩ := bind_eq_ok_iff.mp h
          rw [hpb] at hp1
          have hocc : ConLeche.Frontend.occursConst (absName n)
              (absExpr (expr.Expr.mk (expr.ExprNode.mk d
                (expr.ExprKind.ForallE ty bo bm)))) = false := by
            simp [ConLeche.Frontend.occursConst, ← hq1, ← hp1]
          rw [← Result.ok_injective h]
          exact ⟨hocc.symm, occ_set (old := w.1) (seen' := w.2) hp2 hwf hocc hins⟩
  | let_e d ty v bo hwf ihty ihv ihbo =>
    intro seen r hm h
    obtain ⟨hty, hv, hbo⟩ := ExprWF.let_e_kids hwf
    rw [frontend.proj_rec.occurs_const_go.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨bc, hcont, h⟩ := bind_eq_ok_iff.mp h
    cases bc with
    | true =>
      simp only [if_true] at h
      rw [← Result.ok_injective h]
      exact ⟨(occ_hit hm hwf hcont rfl).symm, hm⟩
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨p, hnode, h⟩ := bind_eq_ok_iff.mp h
      replace h : (if p.1 then ok (true, p.2)
        else do
          let e1 ← expr.dup (expr.Expr.mk (expr.ExprNode.mk d
            (expr.ExprKind.LetE ty v bo)))
          let q ← ron.hashmap.HashMap.insert
            expr.Expr.Insts.Con_ron_coreRonHashmapHashable
            expr.Expr.Insts.Con_ron_coreRonHashmapEq2 p.2 e1 false
          ok (false, q.2)) = ok r := h
      rw [frontend.proj_rec.occurs_const_node.eq_def] at hnode
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at hnode
      obtain ⟨q, hq, hnode⟩ := bind_eq_ok_iff.mp hnode
      replace hnode : (if q.1 then ok (true, q.2)
        else do
          let q2 ← frontend.proj_rec.occurs_const_go n q.2 v
          if q2.1 then ok (true, q2.2)
          else frontend.proj_rec.occurs_const_go n q2.2 bo) = ok p := hnode
      obtain ⟨hq1, hq2⟩ := ihty hty seen q hm hq
      cases hqb : q.1 with
      | true =>
        rw [hqb] at hnode
        simp only [if_true] at hnode
        rw [← Result.ok_injective hnode] at h
        simp only [if_true] at h
        rw [← Result.ok_injective h]
        rw [hqb] at hq1
        exact ⟨by simp [ConLeche.Frontend.occursConst, ← hq1], hq2⟩
      | false =>
        rw [hqb] at hnode
        simp only [Bool.false_eq_true, if_false] at hnode
        obtain ⟨q2, hq2a, hnode⟩ := bind_eq_ok_iff.mp hnode
        obtain ⟨hq2v, hq2m⟩ := ihv hv q.2 q2 hq2 hq2a
        rw [hqb] at hq1
        cases hq2b : q2.1 with
        | true =>
          rw [hq2b] at hnode
          simp only [if_true] at hnode
          rw [← Result.ok_injective hnode] at h
          simp only [if_true] at h
          rw [← Result.ok_injective h]
          rw [hq2b] at hq2v
          exact ⟨by simp [ConLeche.Frontend.occursConst, ← hq1, ← hq2v], hq2m⟩
        | false =>
          rw [hq2b] at hnode
          simp only [Bool.false_eq_true, if_false] at hnode
          obtain ⟨hp1, hp2⟩ := ihbo hbo q2.2 p hq2m hnode
          rw [hq2b] at hq2v
          cases hpb : p.1 with
          | true =>
            rw [hpb] at h
            simp only [if_true] at h
            rw [← Result.ok_injective h]
            rw [hpb] at hp1
            exact ⟨by simp [ConLeche.Frontend.occursConst, ← hq1, ← hq2v, ← hp1], hp2⟩
          | false =>
            rw [hpb] at h
            simp only [Bool.false_eq_true, if_false, expr_dup_eq, bind_tc_ok] at h
            obtain ⟨w, hins, h⟩ := bind_eq_ok_iff.mp h
            rw [hpb] at hp1
            have hocc : ConLeche.Frontend.occursConst (absName n)
                (absExpr (expr.Expr.mk (expr.ExprNode.mk d
                  (expr.ExprKind.LetE ty v bo)))) = false := by
              simp [ConLeche.Frontend.occursConst, ← hq1, ← hq2v, ← hp1]
            rw [← Result.ok_injective h]
            exact ⟨hocc.symm, occ_set (old := w.1) (seen' := w.2) hp2 hwf hocc hins⟩
  | proj d sn idx x hwf ihx =>
    intro seen r hm h
    obtain ⟨-, hx⟩ := ExprWF.proj_kids hwf
    rw [frontend.proj_rec.occurs_const_go.eq_def] at h
    simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
    obtain ⟨bc, hcont, h⟩ := bind_eq_ok_iff.mp h
    cases bc with
    | true =>
      simp only [if_true] at h
      rw [← Result.ok_injective h]
      exact ⟨(occ_hit hm hwf hcont rfl).symm, hm⟩
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨p, hnode, h⟩ := bind_eq_ok_iff.mp h
      replace h : (if p.1 then ok (true, p.2)
        else do
          let e1 ← expr.dup (expr.Expr.mk (expr.ExprNode.mk d
            (expr.ExprKind.Proj sn idx x)))
          let q ← ron.hashmap.HashMap.insert
            expr.Expr.Insts.Con_ron_coreRonHashmapHashable
            expr.Expr.Insts.Con_ron_coreRonHashmapEq2 p.2 e1 false
          ok (false, q.2)) = ok r := h
      rw [frontend.proj_rec.occurs_const_node.eq_def] at hnode
      simp only [expr_view_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at hnode
      obtain ⟨hp1, hp2⟩ := ihx hx seen p hm hnode
      cases hpb : p.1 with
      | true =>
        rw [hpb] at h
        simp only [if_true] at h
        rw [← Result.ok_injective h]
        rw [hpb] at hp1
        exact ⟨by simp [ConLeche.Frontend.occursConst, ← hp1], hp2⟩
      | false =>
        rw [hpb] at h
        simp only [Bool.false_eq_true, if_false, expr_dup_eq, bind_tc_ok] at h
        obtain ⟨w, hins, h⟩ := bind_eq_ok_iff.mp h
        rw [hpb] at hp1
        have hocc : ConLeche.Frontend.occursConst (absName n)
            (absExpr (expr.Expr.mk (expr.ExprNode.mk d
              (expr.ExprKind.Proj sn idx x)))) = false := by
          simp [ConLeche.Frontend.occursConst, ← hp1]
        rw [← Result.ok_injective h]
        exact ⟨hocc.symm, occ_set (old := w.1) (seen' := w.2) hp2 hwf hocc hins⟩

/-! ### con-leche's own bridge: `occursConstFast` computes `occursConst`

`projRecOwners` calls `occursConstFast`, and `ProjRec.lean`'s note says the
pure `occursConst` "stays as its specification" — but con-leche proves nothing
about it, so the bridge is proved here: the budgeted descent is sound whenever
it answers, and the memoised walk is sound under "every recorded subterm really
does not mention `n`". -/

/-- The budgeted descent, when it answers, answers `occursConst`
(`ConLeche/Frontend/ProjRec.lean:151-178 occursConstB`). -/
theorem occursConstB_sound (n : ConLeche.Name) (e : ConLeche.Expr) :
    ∀ (fuel : Nat) (b : Bool) (f' : Nat),
      ConLeche.Frontend.occursConstB n fuel e = (some b, f') →
      b = ConLeche.Frontend.occursConst n e := by
  induction e with
  | app f a ihf iha =>
    intro fuel b f' h
    cases fuel with
    | zero => simp [ConLeche.Frontend.occursConstB] at h
    | succ k =>
      simp only [ConLeche.Frontend.occursConstB] at h
      rcases hgf : ConLeche.Frontend.occursConstB n k f with ⟨of, fu⟩
      rw [hgf] at h
      cases of with
      | none => simp at h
      | some bf =>
        cases bf with
        | true =>
          simp only [Prod.mk.injEq, Option.some.injEq] at h
          rw [← h.1, ConLeche.Frontend.occursConst, ← ihf k true fu hgf]
          rfl
        | false =>
          simp only at h
          rw [iha fu b f' h, ConLeche.Frontend.occursConst, ← ihf k false fu hgf]
          rfl
  | lam ty bo bi ihty ihbo =>
    intro fuel b f' h
    cases fuel with
    | zero => simp [ConLeche.Frontend.occursConstB] at h
    | succ k =>
      simp only [ConLeche.Frontend.occursConstB] at h
      rcases hgf : ConLeche.Frontend.occursConstB n k ty with ⟨of, fu⟩
      rw [hgf] at h
      cases of with
      | none => simp at h
      | some bf =>
        cases bf with
        | true =>
          simp only [Prod.mk.injEq, Option.some.injEq] at h
          rw [← h.1, ConLeche.Frontend.occursConst, ← ihty k true fu hgf]
          rfl
        | false =>
          simp only at h
          rw [ihbo fu b f' h, ConLeche.Frontend.occursConst, ← ihty k false fu hgf]
          rfl
  | forallE ty bo bi ihty ihbo =>
    intro fuel b f' h
    cases fuel with
    | zero => simp [ConLeche.Frontend.occursConstB] at h
    | succ k =>
      simp only [ConLeche.Frontend.occursConstB] at h
      rcases hgf : ConLeche.Frontend.occursConstB n k ty with ⟨of, fu⟩
      rw [hgf] at h
      cases of with
      | none => simp at h
      | some bf =>
        cases bf with
        | true =>
          simp only [Prod.mk.injEq, Option.some.injEq] at h
          rw [← h.1, ConLeche.Frontend.occursConst, ← ihty k true fu hgf]
          rfl
        | false =>
          simp only at h
          rw [ihbo fu b f' h, ConLeche.Frontend.occursConst, ← ihty k false fu hgf]
          rfl
  | letE t v bo iht ihv ihbo =>
    intro fuel b f' h
    cases fuel with
    | zero => simp [ConLeche.Frontend.occursConstB] at h
    | succ k =>
      simp only [ConLeche.Frontend.occursConstB] at h
      rcases hgt : ConLeche.Frontend.occursConstB n k t with ⟨ot, fu⟩
      rw [hgt] at h
      cases ot with
      | none => simp at h
      | some bt =>
        cases bt with
        | true =>
          simp only [Prod.mk.injEq, Option.some.injEq] at h
          rw [← h.1, ConLeche.Frontend.occursConst, ← iht k true fu hgt]
          rfl
        | false =>
          simp only at h
          rcases hgv : ConLeche.Frontend.occursConstB n fu v with ⟨ov, fv⟩
          rw [hgv] at h
          cases ov with
          | none => simp at h
          | some bv =>
            cases bv with
            | true =>
              simp only [Prod.mk.injEq, Option.some.injEq] at h
              rw [← h.1, ConLeche.Frontend.occursConst, ← iht k false fu hgt,
                ← ihv fu true fv hgv]
              rfl
            | false =>
              simp only at h
              rw [ihbo fv b f' h, ConLeche.Frontend.occursConst,
                ← iht k false fu hgt, ← ihv fu false fv hgv]
              rfl
  | proj s idx x ihx =>
    intro fuel b f' h
    cases fuel with
    | zero => simp [ConLeche.Frontend.occursConstB] at h
    | succ k =>
      simp only [ConLeche.Frontend.occursConstB] at h
      rw [ihx k b f' h, ConLeche.Frontend.occursConst]
  | _ =>
    intro fuel b f' h
    simp only [ConLeche.Frontend.occursConstB, Prod.mk.injEq, Option.some.injEq] at h
    rw [← h.1]
    rfl

/-- The memoised walk answers `occursConst` under "everything recorded really
does not mention `n`" (`ConLeche/Frontend/ProjRec.lean:180-225
occursConstGo`). -/
theorem occursConstGo_sound (n : ConLeche.Name) (e : ConLeche.Expr) :
    ∀ (seen : Std.HashSet ConLeche.Expr),
      (∀ x, seen.contains x = true → ConLeche.Frontend.occursConst n x = false) →
      (ConLeche.Frontend.occursConstGo n seen e).1 = ConLeche.Frontend.occursConst n e ∧
      ∀ x, (ConLeche.Frontend.occursConstGo n seen e).2.contains x = true →
        ConLeche.Frontend.occursConst n x = false := by
  induction e with
  | app f a ihf iha =>
    intro seen hs
    rw [ConLeche.Frontend.occursConstGo]
    by_cases hc : seen.contains (ConLeche.Expr.app f a) = true
    · rw [if_pos hc]; exact ⟨(hs _ hc).symm, hs⟩
    · rw [if_neg hc]
      obtain ⟨ihf1, ihf2⟩ := ihf seen hs
      rcases hgf : ConLeche.Frontend.occursConstGo n seen f with ⟨bf, sf⟩
      rw [hgf] at ihf1 ihf2
      cases bf with
      | true =>
        simp only []
        exact ⟨by simp [ConLeche.Frontend.occursConst, ← ihf1], ihf2⟩
      | false =>
        simp only []
        obtain ⟨iha1, iha2⟩ := iha sf ihf2
        rcases hga : ConLeche.Frontend.occursConstGo n sf a with ⟨ba, sa⟩
        rw [hga] at iha1 iha2
        cases ba with
        | true =>
          simp only []
          exact ⟨by simp [ConLeche.Frontend.occursConst, ← ihf1, ← iha1], iha2⟩
        | false =>
          simp only []
          have hocc : ConLeche.Frontend.occursConst n (ConLeche.Expr.app f a) = false := by
            simp [ConLeche.Frontend.occursConst, ← ihf1, ← iha1]
          refine ⟨hocc.symm, ?_⟩
          intro x hx
          rw [Std.HashSet.contains_insert] at hx
          rcases Bool.or_eq_true .. |>.mp hx with h1 | h1
          · rw [← eq_of_beq h1]; exact hocc
          · exact iha2 x h1
  | lam ty bo bi ihty ihbo =>
    intro seen hs
    rw [ConLeche.Frontend.occursConstGo]
    by_cases hc : seen.contains (ConLeche.Expr.lam ty bo bi) = true
    · rw [if_pos hc]; exact ⟨(hs _ hc).symm, hs⟩
    · rw [if_neg hc]
      obtain ⟨ihf1, ihf2⟩ := ihty seen hs
      rcases hgf : ConLeche.Frontend.occursConstGo n seen ty with ⟨bf, sf⟩
      rw [hgf] at ihf1 ihf2
      cases bf with
      | true =>
        simp only []
        exact ⟨by simp [ConLeche.Frontend.occursConst, ← ihf1], ihf2⟩
      | false =>
        simp only []
        obtain ⟨iha1, iha2⟩ := ihbo sf ihf2
        rcases hga : ConLeche.Frontend.occursConstGo n sf bo with ⟨ba, sa⟩
        rw [hga] at iha1 iha2
        cases ba with
        | true =>
          simp only []
          exact ⟨by simp [ConLeche.Frontend.occursConst, ← ihf1, ← iha1], iha2⟩
        | false =>
          simp only []
          have hocc : ConLeche.Frontend.occursConst n
              (ConLeche.Expr.lam ty bo bi) = false := by
            simp [ConLeche.Frontend.occursConst, ← ihf1, ← iha1]
          refine ⟨hocc.symm, ?_⟩
          intro x hx
          rw [Std.HashSet.contains_insert] at hx
          rcases Bool.or_eq_true .. |>.mp hx with h1 | h1
          · rw [← eq_of_beq h1]; exact hocc
          · exact iha2 x h1
  | forallE ty bo bi ihty ihbo =>
    intro seen hs
    rw [ConLeche.Frontend.occursConstGo]
    by_cases hc : seen.contains (ConLeche.Expr.forallE ty bo bi) = true
    · rw [if_pos hc]; exact ⟨(hs _ hc).symm, hs⟩
    · rw [if_neg hc]
      obtain ⟨ihf1, ihf2⟩ := ihty seen hs
      rcases hgf : ConLeche.Frontend.occursConstGo n seen ty with ⟨bf, sf⟩
      rw [hgf] at ihf1 ihf2
      cases bf with
      | true =>
        simp only []
        exact ⟨by simp [ConLeche.Frontend.occursConst, ← ihf1], ihf2⟩
      | false =>
        simp only []
        obtain ⟨iha1, iha2⟩ := ihbo sf ihf2
        rcases hga : ConLeche.Frontend.occursConstGo n sf bo with ⟨ba, sa⟩
        rw [hga] at iha1 iha2
        cases ba with
        | true =>
          simp only []
          exact ⟨by simp [ConLeche.Frontend.occursConst, ← ihf1, ← iha1], iha2⟩
        | false =>
          simp only []
          have hocc : ConLeche.Frontend.occursConst n
              (ConLeche.Expr.forallE ty bo bi) = false := by
            simp [ConLeche.Frontend.occursConst, ← ihf1, ← iha1]
          refine ⟨hocc.symm, ?_⟩
          intro x hx
          rw [Std.HashSet.contains_insert] at hx
          rcases Bool.or_eq_true .. |>.mp hx with h1 | h1
          · rw [← eq_of_beq h1]; exact hocc
          · exact iha2 x h1
  | letE t v bo iht ihv ihbo =>
    intro seen hs
    rw [ConLeche.Frontend.occursConstGo]
    by_cases hc : seen.contains (ConLeche.Expr.letE t v bo) = true
    · rw [if_pos hc]; exact ⟨(hs _ hc).symm, hs⟩
    · rw [if_neg hc]
      obtain ⟨ih11, ih12⟩ := iht seen hs
      rcases hg1 : ConLeche.Frontend.occursConstGo n seen t with ⟨b1, s1⟩
      rw [hg1] at ih11 ih12
      cases b1 with
      | true =>
        simp only []
        exact ⟨by simp [ConLeche.Frontend.occursConst, ← ih11], ih12⟩
      | false =>
        simp only []
        obtain ⟨ih21, ih22⟩ := ihv s1 ih12
        rcases hg2 : ConLeche.Frontend.occursConstGo n s1 v with ⟨b2, s2⟩
        rw [hg2] at ih21 ih22
        cases b2 with
        | true =>
          simp only []
          exact ⟨by simp [ConLeche.Frontend.occursConst, ← ih11, ← ih21], ih22⟩
        | false =>
          simp only []
          obtain ⟨ih31, ih32⟩ := ihbo s2 ih22
          rcases hg3 : ConLeche.Frontend.occursConstGo n s2 bo with ⟨b3, s3⟩
          rw [hg3] at ih31 ih32
          cases b3 with
          | true =>
            simp only []
            exact ⟨by simp [ConLeche.Frontend.occursConst, ← ih11, ← ih21, ← ih31],
              ih32⟩
          | false =>
            simp only []
            have hocc : ConLeche.Frontend.occursConst n
                (ConLeche.Expr.letE t v bo) = false := by
              simp [ConLeche.Frontend.occursConst, ← ih11, ← ih21, ← ih31]
            refine ⟨hocc.symm, ?_⟩
            intro x hx
            rw [Std.HashSet.contains_insert] at hx
            rcases Bool.or_eq_true .. |>.mp hx with h1 | h1
            · rw [← eq_of_beq h1]; exact hocc
            · exact ih32 x h1
  | proj sn idx sub ihsub =>
    intro seen hs
    rw [ConLeche.Frontend.occursConstGo]
    by_cases hc : seen.contains (ConLeche.Expr.proj sn idx sub) = true
    · rw [if_pos hc]; exact ⟨(hs _ hc).symm, hs⟩
    · rw [if_neg hc]
      obtain ⟨ih1, ih2⟩ := ihsub seen hs
      rcases hg : ConLeche.Frontend.occursConstGo n seen sub with ⟨b1, s1⟩
      rw [hg] at ih1 ih2
      cases b1 with
      | true =>
        simp only []
        exact ⟨by simp [ConLeche.Frontend.occursConst, ← ih1], ih2⟩
      | false =>
        simp only []
        have hocc : ConLeche.Frontend.occursConst n
            (ConLeche.Expr.proj sn idx sub) = false := by
          simp [ConLeche.Frontend.occursConst, ← ih1]
        refine ⟨hocc.symm, ?_⟩
        intro x hx
        rw [Std.HashSet.contains_insert] at hx
        rcases Bool.or_eq_true .. |>.mp hx with h1 | h1
        · rw [← eq_of_beq h1]; exact hocc
        · exact ih2 x h1
  | _ => intro seen hs; exact ⟨rfl, hs⟩

/-- **`occursConstFast` computes `occursConst`**
(`ConLeche/Frontend/ProjRec.lean:227-231`). -/
theorem occursConstFast_eq (n : ConLeche.Name) (e : ConLeche.Expr) :
    ConLeche.Frontend.occursConstFast n e = ConLeche.Frontend.occursConst n e := by
  rw [ConLeche.Frontend.occursConstFast]
  rcases hb : ConLeche.Frontend.occursConstB n 4096 e with ⟨ob, fb⟩
  cases ob with
  | none => exact (occursConstGo_sound n e {} (by intro x hx; simp at hx)).1
  | some rr => exact occursConstB_sound n e 4096 rr fb hb

/-- `proj_rec::occurs_const_fast` refines `occursConstFast`
(`ConLeche/Frontend/ProjRec.lean:227-231 occursConstFast`). -/
theorem occurs_const_fast_refines {n : name.Name} {e : expr.Expr} {b : Bool}
    (hn : NameWF n) (he : ExprWF e)
    (h : frontend.proj_rec.occurs_const_fast n e = ok b) :
    b = ConLeche.Frontend.occursConstFast (absName n) (absExpr e) := by
  rw [frontend.proj_rec.occurs_const_fast] at h
  obtain ⟨seen, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨p, hgo, h⟩ := bind_eq_ok_iff.mp h
  replace h : ok p.1 = ok b := h
  rw [← Result.ok_injective h, occursConstFast_eq]
  exact (occurs_const_go_refines hn e he seen p (ExprOps.new_memo_inv hnew) hgo).1

/-! ## The owner census

`ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners` takes its three lists as
tuples; the port's three named structs abstract onto exactly those tuples. -/

/-- `proj_rec::ProjTypeRec` as Lean's `(name, levelParams, type, numParams,
numIndices, ctors, isRec)`. -/
def absProjTypeRec (t : frontend.proj_rec.ProjTypeRec) :
    ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Nat × Nat ×
      List ConLeche.Name × Bool :=
  (absName t.name, absNames t.lps, absExpr t.ty, t.n_p.val, t.n_i.val,
    absNames t.ctors, t.is_rec)

/-- `proj_rec::ProjCtorRec` as Lean's `(name, numFields, type)`. -/
def absProjCtorRec (c : frontend.proj_rec.ProjCtorRec) :
    ConLeche.Name × Nat × ConLeche.Expr :=
  (absName c.name, c.n_f.val, absExpr c.ty)

/-- `proj_rec::ProjRecRec` as Lean's `(name, levelParams, type, numMotives,
numMinors)`. -/
def absProjRecRec (r : frontend.proj_rec.ProjRecRec) :
    ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Nat × Nat :=
  (absName r.name, absNames r.lps, absExpr r.ty, r.n_m.val, r.nm.val)

def absProjTypeRecs (ts : Slice frontend.proj_rec.ProjTypeRec) :
    List (ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Nat × Nat ×
      List ConLeche.Name × Bool) := ts.val.map absProjTypeRec

def absProjCtorRecs (cs : Slice frontend.proj_rec.ProjCtorRec) :
    List (ConLeche.Name × Nat × ConLeche.Expr) := cs.val.map absProjCtorRec

def absProjRecRecs (rs : Slice frontend.proj_rec.ProjRecRec) :
    List (ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Nat × Nat) :=
  rs.val.map absProjRecRec

/-- Well-formedness of the three census records, phase 1's predicates gathered. -/
theorem projCtorRecs_name_wf {cs : Slice frontend.proj_rec.ProjCtorRec}
    (hc : ∀ c ∈ cs.val, ProjCtorRecWF c) : ∀ c ∈ cs.val, NameWF c.name :=
  fun c hcm => (hc c hcm).1

/-! ### `type_names` -/

theorem type_names_loop_refines (N : Nat) :
    ∀ (types : Slice frontend.proj_rec.ProjTypeRec) (n i : Std.Usize)
      (out r : alloc.vec.Vec name.Name),
      types.val.length - i.val = N → n.val = types.val.length →
      frontend.proj_rec.type_names_loop types n out i = ok r →
      absNames r = absNames out ++
        ((absProjTypeRecs types).map (fun q => q.1)).drop i.val := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro types n i out r hN hn h
    rw [frontend.proj_rec.type_names_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < types.val.length := by scalar_tac
      simp only [name_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
      obtain ⟨ptr, hidx, out1, hpush, i1, hi1, hrec⟩ := h
      obtain ⟨-, hdrop⟩ :=
        drop_map_slice_index (fun t => (absProjTypeRec t).1) hidx
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      rw [ih (types.val.length - i1.val) (by omega) types n i1 out1 r rfl hn hrec,
        show absNames out1 = absNames out ++ [absName ptr.name] from by
          rw [absNames, absNames, vec_push_val hpush]; simp, hi1v]
      simp only [absProjTypeRecs, List.map_map]
      rw [show ((fun q => q.1) ∘ absProjTypeRec) = fun t => (absProjTypeRec t).1 from rfl,
        hdrop]
      simp [absProjTypeRec]
    · rename_i hge
      have hle : types.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h]
      rw [List.drop_eq_nil_of_le (by simpa [absProjTypeRecs] using hle)]
      simp

/-- `proj_rec::type_names` refines the cited `types.map (·.1)`
(`ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners`). -/
theorem type_names_refines {types : Slice frontend.proj_rec.ProjTypeRec}
    {r : alloc.vec.Vec name.Name}
    (h : frontend.proj_rec.type_names types = ok r) :
    absNames r = (absProjTypeRecs types).map (fun q => q.1) := by
  rw [frontend.proj_rec.type_names] at h
  rw [type_names_loop_refines _ types _ 0#usize _ r rfl (by simp [Slice.len]) h]
  simp [absNames, alloc.vec.Vec.with_capacity,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

/-! ### The four `any` scans -/

theorem any_is_rec_loop_refines (N : Nat) :
    ∀ (types : Slice frontend.proj_rec.ProjTypeRec) (n i : Std.Usize) (b : Bool),
      types.val.length - i.val = N → n.val = types.val.length →
      frontend.proj_rec.any_is_rec_loop types n i = ok b →
      b = ((absProjTypeRecs types).drop i.val).any (fun q => q.2.2.2.2.2.2) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro types n i b hN hn h
    rw [frontend.proj_rec.any_is_rec_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < types.val.length := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨ptr, hidx, h⟩ := h
      obtain ⟨-, hdrop⟩ := drop_map_slice_index absProjTypeRec hidx
      simp only [absProjTypeRecs]
      rw [hdrop, List.any_cons]
      split at h
      · rename_i hr
        rw [← Result.ok_injective h]
        simp [absProjTypeRec, hr]
      · rename_i hr
        obtain ⟨i1, hi1, hrec⟩ := bind_eq_ok_iff.mp h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        rw [ih (types.val.length - i1.val) (by omega) types n i1 b rfl hn hrec,
          hi1v]
        simp [absProjTypeRec, Bool.eq_false_iff.mpr hr, absProjTypeRecs]
    · rename_i hge
      have hle : types.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h,
        List.drop_eq_nil_of_le (by simpa [absProjTypeRecs] using hle)]
      rfl

/-- `proj_rec::any_is_rec` refines the cited `types.any (·.2.2.2.2.2.2)`. -/
theorem any_is_rec_refines {types : Slice frontend.proj_rec.ProjTypeRec} {b : Bool}
    (h : frontend.proj_rec.any_is_rec types = ok b) :
    b = (absProjTypeRecs types).any (fun q => q.2.2.2.2.2.2) := by
  rw [frontend.proj_rec.any_is_rec] at h
  rw [any_is_rec_loop_refines _ types _ 0#usize b rfl (by simp [Slice.len]) h]
  simp [show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

theorem any_name_mentions_loop_refines (N : Nat) :
    ∀ (bns : alloc.vec.Vec name.Name) (d : expr.Expr) (m j : Std.Usize) (b : Bool),
      bns.val.length - j.val = N → m.val = bns.val.length →
      (∀ x ∈ bns.val, NameWF x) → ExprWF d →
      frontend.proj_rec.any_name_mentions_loop bns d m j = ok b →
      b = ((absNames bns).drop j.val).any
        (fun nm => ConLeche.Frontend.occursConstFast nm (absExpr d)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro bns d m j b hN hm hbns hd h
    rw [frontend.proj_rec.any_name_mentions_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : j.val < bns.val.length := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨nm, hidx, bb, hocc, h⟩ := h
      obtain ⟨-, hmem⟩ := vec_index_mem hidx
      obtain ⟨-, hdrop⟩ := drop_map_index absName hidx
      simp only [absNames]
      rw [hdrop, List.any_cons,
        ← occurs_const_fast_refines (hbns nm hmem) hd hocc]
      split at h
      · rename_i hr
        rw [← Result.ok_injective h]
        simp [hr]
      · rename_i hr
        obtain ⟨j1, hj1, hrec⟩ := bind_eq_ok_iff.mp h
        have hj1v : j1.val = j.val + 1 := HashMap.uscalar_add_eq hj1
        rw [ih (bns.val.length - j1.val) (by omega) bns d m j1 b rfl hm hbns hd hrec,
          hj1v]
        simp [Bool.eq_false_iff.mpr hr, absNames]
    · rename_i hge
      have hle : bns.val.length ≤ j.val := by scalar_tac
      rw [← Result.ok_injective h,
        List.drop_eq_nil_of_le (by simpa [absNames] using hle)]
      rfl

/-- `proj_rec::any_name_mentions` refines the cited innermost
`blockNames.any fun n => occursConstFast n d`. -/
theorem any_name_mentions_refines {bns : alloc.vec.Vec name.Name} {d : expr.Expr}
    {b : Bool} (hbns : ∀ x ∈ bns.val, NameWF x) (hd : ExprWF d)
    (h : frontend.proj_rec.any_name_mentions bns d = ok b) :
    b = (absNames bns).any
      (fun nm => ConLeche.Frontend.occursConstFast nm (absExpr d)) := by
  rw [frontend.proj_rec.any_name_mentions] at h
  rw [any_name_mentions_loop_refines _ bns d _ 0#usize b rfl
    (by simp [alloc.vec.Vec.len]) hbns hd h]
  simp [show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

theorem any_dom_mentions_loop_refines (N : Nat) :
    ∀ (bns : alloc.vec.Vec name.Name)
      (bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)) (n i : Std.Usize) (b : Bool),
      bs.val.length - i.val = N → n.val = bs.val.length →
      (∀ x ∈ bns.val, NameWF x) → ExprOps.BindersWF bs →
      frontend.proj_rec.any_dom_mentions_loop bns bs n i = ok b →
      b = ((ExprOps.absBinders bs).drop i.val).any (fun q =>
        (absNames bns).any
          (fun nm => ConLeche.Frontend.occursConstFast nm q.1)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro bns bs n i b hN hn hbns hbs h
    rw [frontend.proj_rec.any_dom_mentions_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < bs.val.length := by scalar_tac
      obtain ⟨p, hidx, h⟩ := bind_eq_ok_iff.mp h
      replace h : (do
          let bb ← frontend.proj_rec.any_name_mentions bns p.1
          if bb then ok true
          else do
            let i1 ← i + 1#usize
            frontend.proj_rec.any_dom_mentions_loop bns bs n i1) = ok b := h
      obtain ⟨-, hmem⟩ := vec_index_mem hidx
      obtain ⟨hpe, -⟩ := hbs p hmem
      obtain ⟨-, hdrop⟩ :=
        drop_map_index (fun q => (absExpr q.1, absBinderMeta q.2)) hidx
      obtain ⟨bb, hany, h⟩ := bind_eq_ok_iff.mp h
      simp only [ExprOps.absBinders]
      rw [hdrop, List.any_cons, ← any_name_mentions_refines hbns hpe hany]
      split at h
      · rename_i hr
        rw [← Result.ok_injective h]
        simp [hr]
      · rename_i hr
        obtain ⟨i1, hi1, hrec⟩ := bind_eq_ok_iff.mp h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        rw [ih (bs.val.length - i1.val) (by omega) bns bs n i1 b rfl hn hbns hbs hrec,
          hi1v]
        simp [Bool.eq_false_iff.mpr hr, ExprOps.absBinders]
    · rename_i hge
      have hle : bs.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h,
        List.drop_eq_nil_of_le (by simpa [ExprOps.absBinders] using hle)]
      rfl

/-- `proj_rec::any_dom_mentions` refines the cited `fun (d, _) => …`. -/
theorem any_dom_mentions_refines {bns : alloc.vec.Vec name.Name}
    {bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {b : Bool}
    (hbns : ∀ x ∈ bns.val, NameWF x) (hbs : ExprOps.BindersWF bs)
    (h : frontend.proj_rec.any_dom_mentions bns bs = ok b) :
    b = (ExprOps.absBinders bs).any (fun q =>
      (absNames bns).any
        (fun nm => ConLeche.Frontend.occursConstFast nm q.1)) := by
  rw [frontend.proj_rec.any_dom_mentions] at h
  rw [any_dom_mentions_loop_refines _ bns bs _ 0#usize b rfl
    (by simp [alloc.vec.Vec.len]) hbns hbs h]
  simp [show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

theorem any_ctor_mentions_loop_refines (N : Nat) :
    ∀ (bns : alloc.vec.Vec name.Name) (ctors : Slice frontend.proj_rec.ProjCtorRec)
      (n i : Std.Usize) (b : Bool),
      ctors.val.length - i.val = N → n.val = ctors.val.length →
      (∀ x ∈ bns.val, NameWF x) → (∀ c ∈ ctors.val, ProjCtorRecWF c) →
      frontend.proj_rec.any_ctor_mentions_loop bns ctors n i = ok b →
      b = ((absProjCtorRecs ctors).drop i.val).any (fun c =>
        (ConLeche.Frontend.stripPisAll c.2.2).1.any (fun q =>
          (absNames bns).any
            (fun nm => ConLeche.Frontend.occursConstFast nm q.1))) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro bns ctors n i b hN hn hbns hctors h
    rw [frontend.proj_rec.any_ctor_mentions_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < ctors.val.length := by scalar_tac
      obtain ⟨pcr, hidx, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨-, hmem⟩ := slice_index_mem hidx
      obtain ⟨-, hcty⟩ := hctors pcr hmem
      obtain ⟨-, hdrop⟩ := drop_map_slice_index absProjCtorRec hidx
      obtain ⟨p, hsp, h⟩ := bind_eq_ok_iff.mp h
      replace h : (do
          let bb ← frontend.proj_rec.any_dom_mentions bns p.1
          if bb then ok true
          else do
            let i1 ← i + 1#usize
            frontend.proj_rec.any_ctor_mentions_loop bns ctors n i1) = ok b := h
      have habs := strip_pis_all_refines hcty hsp
      obtain ⟨hbs, -⟩ := strip_pis_all_wf hcty hsp
      obtain ⟨bb, hany, h⟩ := bind_eq_ok_iff.mp h
      simp only [absProjCtorRecs]
      rw [hdrop, List.any_cons]
      simp only [absProjCtorRec]
      rw [← habs, ← any_dom_mentions_refines hbns hbs hany]
      split at h
      · rename_i hr
        rw [← Result.ok_injective h]
        simp [hr]
      · rename_i hr
        obtain ⟨i1, hi1, hrec⟩ := bind_eq_ok_iff.mp h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        rw [ih (ctors.val.length - i1.val) (by omega) bns ctors n i1 b rfl hn hbns
          hctors hrec, hi1v]
        simp [Bool.eq_false_iff.mpr hr, absProjCtorRecs]
    · rename_i hge
      have hle : ctors.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h,
        List.drop_eq_nil_of_le (by simpa [absProjCtorRecs] using hle)]
      rfl

/-- `proj_rec::any_ctor_mentions` refines the cited
`ctors.any fun (_, _, cty) => …`. -/
theorem any_ctor_mentions_refines {bns : alloc.vec.Vec name.Name}
    {ctors : Slice frontend.proj_rec.ProjCtorRec} {b : Bool}
    (hbns : ∀ x ∈ bns.val, NameWF x) (hctors : ∀ c ∈ ctors.val, ProjCtorRecWF c)
    (h : frontend.proj_rec.any_ctor_mentions bns ctors = ok b) :
    b = (absProjCtorRecs ctors).any (fun c =>
      (ConLeche.Frontend.stripPisAll c.2.2).1.any (fun q =>
        (absNames bns).any
          (fun nm => ConLeche.Frontend.occursConstFast nm q.1))) := by
  rw [frontend.proj_rec.any_ctor_mentions] at h
  rw [any_ctor_mentions_loop_refines _ bns ctors _ 0#usize b rfl
    (by simp [Slice.len]) hbns hctors h]
  simp [show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

/-! ### `find_ctor` / `find_rec`

The port hands back an *index* where con-leche's `List.find?` hands back the
record, so each lemma says what `find?` answers at the index the port found. -/

theorem find_ctor_loop_refines (N : Nat) :
    ∀ (ctors : Slice frontend.proj_rec.ProjCtorRec) (nm : name.Name) (m i : Std.Usize)
      (o : Option Std.Usize),
      ctors.val.length - i.val = N → m.val = ctors.val.length →
      (∀ c ∈ ctors.val, ProjCtorRecWF c) → NameWF nm →
      frontend.proj_rec.find_ctor_loop ctors nm m i = ok o →
      (o = none → ((absProjCtorRecs ctors).drop i.val).find?
          (fun q => q.1 == absName nm) = none) ∧
      (∀ j, o = some j → ∃ c, Slice.index_usize ctors j = ok c ∧
        ((absProjCtorRecs ctors).drop i.val).find? (fun q => q.1 == absName nm)
          = some (absProjCtorRec c)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro ctors nm m i o hN hm hc hnm h
    rw [frontend.proj_rec.find_ctor_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < ctors.val.length := by scalar_tac
      obtain ⟨pcr, hidx, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨-, hmem⟩ := slice_index_mem hidx
      obtain ⟨-, hdrop⟩ := drop_map_slice_index absProjCtorRec hidx
      obtain ⟨b, hbeq, h⟩ := bind_eq_ok_iff.mp h
      have hbv : b = decide (absName pcr.name = absName nm) :=
        Name.beq_refines (hc pcr hmem).1 hnm hbeq
      simp only [absProjCtorRecs]
      rw [hdrop]
      split at h
      · rename_i hb
        rw [hb] at hbv
        refine ⟨by intro hc0; rw [← Result.ok_injective h] at hc0; simp at hc0, ?_⟩
        intro j hj
        rw [← Result.ok_injective h] at hj
        simp only [Option.some.injEq] at hj
        refine ⟨pcr, by rw [← hj]; exact hidx, ?_⟩
        rw [List.find?_cons_of_pos (by simp only [absProjCtorRec, beq_iff_eq]; exact of_decide_eq_true hbv.symm)]
      · rename_i hb
        obtain ⟨i1, hi1, hrec⟩ := bind_eq_ok_iff.mp h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        have hbf : b = false := by
          cases b with
          | true => exact absurd rfl hb
          | false => rfl
        rw [hbf] at hbv
        obtain ⟨ih1, ih2⟩ :=
          ih (ctors.val.length - i1.val) (by omega) ctors nm m i1 o rfl hm hc hnm hrec
        rw [hi1v] at ih1 ih2
        simp only [absProjCtorRecs] at ih1 ih2
        refine ⟨?_, ?_⟩
        · intro h0
          rw [List.find?_cons_of_neg (by
            simp only [absProjCtorRec, beq_iff_eq]; exact of_decide_eq_false hbv.symm)]
          exact ih1 h0
        · intro j h0
          obtain ⟨c, hc1, hc2⟩ := ih2 j h0
          refine ⟨c, hc1, ?_⟩
          rw [List.find?_cons_of_neg (by
            simp only [absProjCtorRec, beq_iff_eq]; exact of_decide_eq_false hbv.symm)]
          exact hc2
    · rename_i hge
      have hle : ctors.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h,
        List.drop_eq_nil_of_le (by simpa [absProjCtorRecs] using hle)]
      exact ⟨fun _ => rfl, by intro j hj; simp at hj⟩

/-- `proj_rec::find_ctor` refines the cited `ctors.find? (·.1 == C)`. -/
theorem find_ctor_refines {ctors : Slice frontend.proj_rec.ProjCtorRec}
    {nm : name.Name} {o : Option Std.Usize}
    (hc : ∀ c ∈ ctors.val, ProjCtorRecWF c) (hnm : NameWF nm)
    (h : frontend.proj_rec.find_ctor ctors nm = ok o) :
    (o = none → (absProjCtorRecs ctors).find? (fun q => q.1 == absName nm) = none) ∧
    (∀ j, o = some j → ∃ c, Slice.index_usize ctors j = ok c ∧
      (absProjCtorRecs ctors).find? (fun q => q.1 == absName nm)
        = some (absProjCtorRec c)) := by
  rw [frontend.proj_rec.find_ctor] at h
  obtain ⟨h1, h2⟩ :=
    find_ctor_loop_refines _ ctors nm _ 0#usize o rfl (by simp [Slice.len]) hc hnm h
  rw [show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero] at h1 h2
  exact ⟨h1, h2⟩

theorem find_rec_loop_refines (N : Nat) :
    ∀ (recs : Slice frontend.proj_rec.ProjRecRec) (nm : name.Name) (m i : Std.Usize)
      (o : Option Std.Usize),
      recs.val.length - i.val = N → m.val = recs.val.length →
      (∀ x ∈ recs.val, ProjRecRecWF x) → NameWF nm →
      frontend.proj_rec.find_rec_loop recs nm m i = ok o →
      (o = none → ((absProjRecRecs recs).drop i.val).find?
          (fun q => q.1 == absName nm) = none) ∧
      (∀ j, o = some j → ∃ x, Slice.index_usize recs j = ok x ∧
        ((absProjRecRecs recs).drop i.val).find? (fun q => q.1 == absName nm)
          = some (absProjRecRec x)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro recs nm m i o hN hm hr hnm h
    rw [frontend.proj_rec.find_rec_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < recs.val.length := by scalar_tac
      obtain ⟨prr, hidx, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨-, hmem⟩ := slice_index_mem hidx
      obtain ⟨-, hdrop⟩ := drop_map_slice_index absProjRecRec hidx
      obtain ⟨b, hbeq, h⟩ := bind_eq_ok_iff.mp h
      have hbv : b = decide (absName prr.name = absName nm) :=
        Name.beq_refines (hr prr hmem).1 hnm hbeq
      simp only [absProjRecRecs]
      rw [hdrop]
      split at h
      · rename_i hb
        rw [hb] at hbv
        refine ⟨by intro hc0; rw [← Result.ok_injective h] at hc0; simp at hc0, ?_⟩
        intro j hj
        rw [← Result.ok_injective h] at hj
        simp only [Option.some.injEq] at hj
        refine ⟨prr, by rw [← hj]; exact hidx, ?_⟩
        rw [List.find?_cons_of_pos (by simp only [absProjRecRec, beq_iff_eq]; exact of_decide_eq_true hbv.symm)]
      · rename_i hb
        obtain ⟨i1, hi1, hrec⟩ := bind_eq_ok_iff.mp h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        have hbf : b = false := by
          cases b with
          | true => exact absurd rfl hb
          | false => rfl
        rw [hbf] at hbv
        obtain ⟨ih1, ih2⟩ :=
          ih (recs.val.length - i1.val) (by omega) recs nm m i1 o rfl hm hr hnm hrec
        rw [hi1v] at ih1 ih2
        simp only [absProjRecRecs] at ih1 ih2
        refine ⟨?_, ?_⟩
        · intro h0
          rw [List.find?_cons_of_neg (by
            simp only [absProjRecRec, beq_iff_eq]; exact of_decide_eq_false hbv.symm)]
          exact ih1 h0
        · intro j h0
          obtain ⟨c, hc1, hc2⟩ := ih2 j h0
          refine ⟨c, hc1, ?_⟩
          rw [List.find?_cons_of_neg (by
            simp only [absProjRecRec, beq_iff_eq]; exact of_decide_eq_false hbv.symm)]
          exact hc2
    · rename_i hge
      have hle : recs.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h,
        List.drop_eq_nil_of_le (by simpa [absProjRecRecs] using hle)]
      exact ⟨fun _ => rfl, by intro j hj; simp at hj⟩

/-- `proj_rec::find_rec` refines the cited `recs.find? (·.1 == T.str "rec")`. -/
theorem find_rec_refines {recs : Slice frontend.proj_rec.ProjRecRec}
    {nm : name.Name} {o : Option Std.Usize}
    (hr : ∀ x ∈ recs.val, ProjRecRecWF x) (hnm : NameWF nm)
    (h : frontend.proj_rec.find_rec recs nm = ok o) :
    (o = none → (absProjRecRecs recs).find? (fun q => q.1 == absName nm) = none) ∧
    (∀ j, o = some j → ∃ x, Slice.index_usize recs j = ok x ∧
      (absProjRecRecs recs).find? (fun q => q.1 == absName nm)
        = some (absProjRecRec x)) := by
  rw [frontend.proj_rec.find_rec] at h
  obtain ⟨h1, h2⟩ :=
    find_rec_loop_refines _ recs nm _ 0#usize o rfl (by simp [Slice.len]) hr hnm h
  rw [show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero] at h1 h2
  exact ⟨h1, h2⟩

/-! ### The `filterMap` body

`projRecOwners`' `types.filterMap fun (T, lps, tty, nP, nI, cs, _) => do …`
(`ConLeche/Frontend/ProjRec.lean:362-370`), written out as the port factors it
(`proj_rec_owner_at`); `projRecOwners_eq` below is the equivalence. -/

/-- The tail from `ctors.find?` on. -/
def lOwnerTail (T : ConLeche.Name) (lps : List ConLeche.Name) (nP : Nat)
    (C : ConLeche.Name) (ctors : List (ConLeche.Name × Nat × ConLeche.Expr))
    (recs : List (ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Nat × Nat)) :
    Option ConLeche.Frontend.ProjRecOwner := do
  let (_, nF, _) ← ctors.find? (fun q => q.1 == C)
  let (rn, rlps, rty, nM, nm) ← recs.find? (fun q => q.1 == T.str "rec")
  guard (rlps.length == lps.length + 1)
  pure ⟨T, lps, nP, C, nF, rn, rlps, rty, nM, nm⟩

/-- The whole `filterMap` body. -/
def lProjRecOwnerAt
    (t : ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Nat × Nat ×
      List ConLeche.Name × Bool)
    (ctors : List (ConLeche.Name × Nat × ConLeche.Expr))
    (recs : List (ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Nat × Nat)) :
    Option ConLeche.Frontend.ProjRecOwner := do
  let [C] := t.2.2.2.2.2.1 | none
  guard (t.2.2.2.2.1 == 0)
  let (_, .sort s) ← t.2.2.1.stripPis t.2.2.2.1 | none
  guard (ConLeche.Level.isEquiv s .zero != some true)
  lOwnerTail t.1 t.2.1 t.2.2.2.1 C ctors recs

/-- `projRecOwners`' `recursive` (`ProjRec.lean:351-353`). -/
def lRecursive
    (types : List (ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Nat × Nat ×
      List ConLeche.Name × Bool))
    (ctors : List (ConLeche.Name × Nat × ConLeche.Expr)) : Bool :=
  types.any (fun q => q.2.2.2.2.2.2) ||
    ctors.any (fun c => (ConLeche.Frontend.stripPisAll c.2.2).1.any (fun d =>
      (types.map (fun q => q.1)).any
        (fun nm => ConLeche.Frontend.occursConstFast nm d.1)))

/-- **The factoring is the cited term.** -/
theorem projRecOwners_eq (block : List ConLeche.ConstantInfo)
    (types : List (ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Nat × Nat ×
      List ConLeche.Name × Bool))
    (ctors : List (ConLeche.Name × Nat × ConLeche.Expr))
    (recs : List (ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Nat × Nat)) :
    ConLeche.Frontend.projRecOwners block types ctors recs
      = (if (ConLeche.structPartsCore? block).isSome && !(lRecursive types ctors) then []
         else if (ConLeche.nativeParts?
             ((types.head?.map (fun q => q.2.2.2.1)).getD 0) block).isSome then []
         else types.filterMap (fun t => lProjRecOwnerAt t ctors recs)) := by
  unfold ConLeche.Frontend.projRecOwners lRecursive lProjRecOwnerAt lOwnerTail
  rfl

/-! ### The port's `proj_rec_owner_at` -/

/-- A one-element `Vec<Name>`, as its abstraction. -/
theorem absNames_singleton_of_len {v : alloc.vec.Vec name.Name}
    (hlen : alloc.vec.Vec.len v = (1#usize : Std.Usize)) :
    ∃ x, v.val = [x] ∧ absNames v = [absName x] := by
  have hl : v.val.length = 1 := by
    have := alloc.vec.Vec.len_val v; rw [hlen] at this; scalar_tac
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl
  exact ⟨x, hx, by rw [absNames, hx]; rfl⟩

/-- …and one that is not. -/
theorem absNames_not_singleton {v : alloc.vec.Vec name.Name}
    (hlen : ¬ alloc.vec.Vec.len v = (1#usize : Std.Usize)) :
    absNames v = [] ∨ ∃ a b tl, absNames v = a :: b :: tl := by
  have hl : v.val.length ≠ 1 := by
    intro hc; exact hlen (by have := alloc.vec.Vec.len_val v; scalar_tac)
  rcases list_ne_singleton v.val hl with hnil | ⟨a, b, tl, hcons⟩
  · exact Or.inl (by rw [absNames, hnil]; rfl)
  · exact Or.inr ⟨_, _, _, by rw [absNames, hcons]; rfl⟩

private theorem lAt_multi
    (t : ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Nat × Nat ×
      List ConLeche.Name × Bool)
    (ctors : List (ConLeche.Name × Nat × ConLeche.Expr))
    (recs : List (ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Nat × Nat))
    (h : t.2.2.2.2.2.1 = [] ∨ ∃ a b tl, t.2.2.2.2.2.1 = a :: b :: tl) :
    lProjRecOwnerAt t ctors recs = none := by
  unfold lProjRecOwnerAt
  rcases h with h | ⟨a, b, tl, h⟩ <;> rw [h]

private theorem lAt_single
    (t : ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Nat × Nat ×
      List ConLeche.Name × Bool)
    (ctors : List (ConLeche.Name × Nat × ConLeche.Expr))
    (recs : List (ConLeche.Name × List ConLeche.Name × ConLeche.Expr × Nat × Nat))
    (C : ConLeche.Name) (h : t.2.2.2.2.2.1 = [C]) :
    lProjRecOwnerAt t ctors recs =
      (do
        guard (t.2.2.2.2.1 == 0)
        let (_, .sort s) ← t.2.2.1.stripPis t.2.2.2.1 | none
        guard (ConLeche.Level.isEquiv s .zero != some true)
        lOwnerTail t.1 t.2.1 t.2.2.2.1 C ctors recs) := by
  unfold lProjRecOwnerAt
  rw [h]


/-- The tail of `proj_rec::proj_rec_owner_at` from `find_ctor` on, i.e.
`lOwnerTail`.  Stated as its own lemma because the port's `level::is_equiv`
match repeats it in two arms. -/
private theorem owner_tail_refines {t : frontend.proj_rec.ProjTypeRec}
    {ctors : Slice frontend.proj_rec.ProjCtorRec}
    {recs : Slice frontend.proj_rec.ProjRecRec}
    {C : name.Name} {o : Option frontend.proj_rec.ProjRecOwner}
    (htn : NameWF t.name) (htctors : NamesWF t.ctors)
    (hc : ∀ c ∈ ctors.val, ProjCtorRecWF c) (hr : ∀ x ∈ recs.val, ProjRecRecWF x)
    (hCv : t.ctors.val = [C])
    (h : (do
      let n ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice name.Name)
        t.ctors 0#usize
      let o2 ← frontend.proj_rec.find_ctor ctors n
      match o2 with
      | none => ok none
      | some j => do
        let n1 ← name.dup t.name
        let s2 ← lift (Array.to_slice frontend.proj_rec.proj_rec_owner_at.REC)
        let v ← core_types.code_points s2
        let want_rec ← name.mk_str n1 v
        let o3 ← frontend.proj_rec.find_rec recs want_rec
        match o3 with
        | none => ok none
        | some j1 => do
          let prr ← Slice.index_usize recs j1
          let i3 ← alloc.vec.Vec.len t.lps + 1#usize
          if alloc.vec.Vec.len prr.lps != i3 then
            ok (none : Option frontend.proj_rec.ProjRecOwner)
          else do
            let v1 ← prop_when.names_copy t.lps
            let n2 ← name.dup n
            let pcr ← Slice.index_usize ctors j
            let n3 ← name.dup prr.name
            let v2 ← prop_when.names_copy prr.lps
            let e1 ← expr.dup prr.ty
            ok (some { t := n1, lps := v1, n_p := t.n_p, ctor := n2, n_f := pcr.n_f,
                       rec_name := n3, rec_lps := v2, rec_type := e1,
                       num_motives := prr.n_m, num_minors := prr.nm })) = ok o) :
    Option.map absProjRecOwner o
      = lOwnerTail (absName t.name) (absNames t.lps) t.n_p.val (absName C)
          (absProjCtorRecs ctors) (absProjRecRecs recs) := by
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, o2, ho2, h⟩ := h
  have hnC : n = C := by
    have hg := ExprOps.vec_index_getElem? hn
    rw [hCv] at hg
    simpa using hg.symm
  subst hnC
  have hnwf : NameWF n := htctors n (by rw [hCv]; simp)
  obtain ⟨hfc1, hfc2⟩ := find_ctor_refines hc hnwf ho2
  rw [lOwnerTail]
  cases o2 with
  | none =>
    rw [hfc1 rfl, ← Result.ok_injective h]
    rfl
  | some j =>
    obtain ⟨pcr, hpcr, hfind⟩ := hfc2 j rfl
    rw [hfind]
    simp only [absProjCtorRec]
    simp only [name_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
    obtain ⟨s2, hs2, v, hv, want, hwant, o3, ho3, h⟩ := h
    obtain ⟨hwa, hwwf⟩ := str_lit_step htn hs2 hv hwant
      (L := [114#u32, 101#u32, 99#u32])
      (by simp [frontend.proj_rec.proj_rec_owner_at.REC]) (by decide)
    have hwa' : absName want = (absName t.name).str "rec" := hwa
    obtain ⟨hfr1, hfr2⟩ := find_rec_refines hr hwwf ho3
    rw [← hwa']
    cases o3 with
    | none =>
      rw [hfr1 rfl, ← Result.ok_injective h]
      rfl
    | some j1 =>
      obtain ⟨prr, hprr, hfindr⟩ := hfr2 j1 rfl
      rw [hfindr]
      simp only [absProjRecRec, option_bind_some_l]
      simp only [bind_eq_ok_iff] at h
      obtain ⟨prr2, hprr2, i3, hi3, h⟩ := h
      have hprr2e : prr2 = prr := Result.ok_injective (hprr2.symm.trans hprr)
      subst hprr2e
      have hi3v : i3.val = t.lps.val.length + 1 := by
        rw [HashMap.uscalar_add_eq hi3, alloc.vec.Vec.len_val]
        scalar_tac
      have hlenv : (alloc.vec.Vec.len prr2.lps).val = prr2.lps.val.length :=
        alloc.vec.Vec.len_val _
      split at h
      · rename_i hne
        simp only [bne_iff_ne, ne_eq] at hne
        have hnev : ¬ ((absNames prr2.lps).length = (absNames t.lps).length + 1) := by
          simp only [absNames, List.length_map]
          intro hcc
          exact hne (Std.UScalar.val_eq_imp_iff.mpr (by rw [hlenv, hi3v]; omega))
        rw [guard_opt_neg (by simpa using hnev), ← Result.ok_injective h]
        rfl
      · rename_i heq
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at heq
        have heqv : (absNames prr2.lps).length = (absNames t.lps).length + 1 := by
          simp only [absNames, List.length_map]
          have := congrArg Std.UScalar.val heq
          rw [hlenv, hi3v] at this
          omega
        rw [guard_opt_pos (by simpa using heqv)]
        simp only [bind_eq_ok_iff] at h
        obtain ⟨v1, hv1, pcr2, hpcr2, v2, hv2, e1, he1, h⟩ := h
        have hpcr2e : pcr2 = pcr := Result.ok_injective (hpcr2.symm.trans hpcr)
        subst hpcr2e
        rw [← Result.ok_injective h]
        simp only [Option.map_some, absProjRecOwner, absNames,
          PropWhen.names_copy_val hv1, PropWhen.names_copy_val hv2, Expr.dup_eq he1]
        rfl

/-- `proj_rec::proj_rec_owner_at` refines `projRecOwners`' `filterMap` body
(`ConLeche/Frontend/ProjRec.lean:362-370`), in the factoring `lProjRecOwnerAt`. -/
theorem proj_rec_owner_at_refines {t : frontend.proj_rec.ProjTypeRec}
    {ctors : Slice frontend.proj_rec.ProjCtorRec}
    {recs : Slice frontend.proj_rec.ProjRecRec}
    {o : Option frontend.proj_rec.ProjRecOwner}
    (ht : ProjTypeRecWF t) (hc : ∀ c ∈ ctors.val, ProjCtorRecWF c)
    (hr : ∀ x ∈ recs.val, ProjRecRecWF x)
    (h : frontend.proj_rec.proj_rec_owner_at t ctors recs = ok o) :
    Option.map absProjRecOwner o
      = lProjRecOwnerAt (absProjTypeRec t) (absProjCtorRecs ctors)
          (absProjRecRecs recs) := by
  obtain ⟨htn, htlps, htty, htctors⟩ := ht
  rw [frontend.proj_rec.proj_rec_owner_at] at h
  split at h
  · rename_i hlen
    rw [← Result.ok_injective h, lAt_multi _ _ _ ?_]
    · rfl
    · have hlen1 : ¬ (alloc.vec.Vec.len t.ctors = (1#usize : Std.Usize)) := by
        simp only [bne_iff_ne, ne_eq] at hlen; exact hlen
      rcases absNames_not_singleton (v := t.ctors) hlen1 with hq | ⟨a, b, tl, hq⟩
      · exact Or.inl hq
      · exact Or.inr ⟨a, b, tl, hq⟩
  · rename_i hlen
    have hlen1 : alloc.vec.Vec.len t.ctors = (1#usize : Std.Usize) := by
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen; exact hlen
    obtain ⟨C, hCv, hCa⟩ := absNames_singleton_of_len (v := t.ctors) hlen1
    rw [lAt_single _ _ _ (absName C) hCa]
    split at h
    · rename_i hni
      simp only [bne_iff_ne, ne_eq] at hni
      have hnz : ¬ (((absProjTypeRec t).2.2.2.2.1 == 0) = true) := by
        simp only [absProjTypeRec, beq_iff_eq]
        intro hcc
        exact hni (Std.UScalar.val_eq_imp_iff.mpr (by rw [hcc]; rfl))
      rw [guard_opt_neg hnz, ← Result.ok_injective h]
      rfl
    · rename_i hni
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hni
      have hnz : (((absProjTypeRec t).2.2.2.2.1 == 0) = true) := by
        simp only [absProjTypeRec, beq_iff_eq]; rw [hni]; rfl
      rw [guard_opt_pos hnz]
      simp only [option_bind_some_l, absProjTypeRec]
      simp only [bind_eq_ok_iff] at h
      obtain ⟨op, hop, h⟩ := h
      obtain ⟨hspa, hsp⟩ := ExprOps.strip_pis_refines htty hop
      rw [← hspa]
      cases op with
      | none => rw [← Result.ok_injective h]; rfl
      | some q =>
        obtain ⟨-, htb⟩ := hsp q rfl
        obtain ⟨pb, tb⟩ := q
        simp only [Option.map_some, option_bind_some_l]
        obtain ⟨⟨d, k⟩⟩ := tb
        cases k <;>
          simp only [expr_view_eq, bind_tc_ok, level_dup_eq] at h <;>
          simp only [absExpr_mk, absExprKind]
        case «Sort» s =>
          obtain ⟨l0, hl0, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
          have hswf : LevelWF s := ExprWF.sort_kids htb
          have hIE : ConLeche.Level.isEquiv (absLevel s) ConLeche.Level.zero = o1 := by
            rw [← Level.zero_refines hl0]
            exact Level.is_equiv_refines hswf (Level.zero_wf hl0) ho1
          by_cases htrue : o1 = some true
          · subst htrue
            rw [guard_opt_neg (by simp [hIE])]
            have ho : o = none := (Result.ok_injective h).symm
            rw [ho]
            rfl
          · rw [guard_opt_pos (by simp [hIE, htrue])]
            cases o1 with
            | none => exact owner_tail_refines htn htctors hc hr hCv h
            | some b1 =>
              cases b1 with
              | true => exact absurd rfl htrue
              | false =>
                simp only [Bool.false_eq_true, if_false] at h
                exact owner_tail_refines htn htctors hc hr hCv h
        all_goals (rw [← Result.ok_injective h]; rfl)


/-- The names `type_names` copies are the type records' own, so well formed. -/
private theorem type_names_loop_wf (N : Nat) :
    ∀ (types : Slice frontend.proj_rec.ProjTypeRec) (n i : Std.Usize)
      (out r : alloc.vec.Vec name.Name),
      types.val.length - i.val = N → n.val = types.val.length →
      (∀ x ∈ types.val, ProjTypeRecWF x) → (∀ x ∈ out.val, NameWF x) →
      frontend.proj_rec.type_names_loop types n out i = ok r →
      ∀ x ∈ r.val, NameWF x := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro types n i out r hN hn htypes hout h
    rw [frontend.proj_rec.type_names_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [name_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
      obtain ⟨ptr, hidx, out1, hpush, i1, hi1, hrec⟩ := h
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      obtain ⟨-, hmem⟩ := slice_index_mem hidx
      have hltv : i.val < types.val.length := by scalar_tac
      refine ih (types.val.length - i1.val) (by omega) types n i1 out1 r rfl hn
        htypes ?_ hrec
      intro x hx
      rw [vec_push_val hpush] at hx
      rcases List.mem_append.1 hx with hx1 | hx1
      · exact hout x hx1
      · simp only [List.mem_singleton] at hx1
        rw [hx1]
        exact (htypes ptr hmem).1
    · rw [← Result.ok_injective h]; exact hout

/-- `proj_rec::type_names` copies well-formed names. -/
theorem type_names_wf {types : Slice frontend.proj_rec.ProjTypeRec}
    {r : alloc.vec.Vec name.Name} (ht : ∀ x ∈ types.val, ProjTypeRecWF x)
    (h : frontend.proj_rec.type_names types = ok r) : ∀ x ∈ r.val, NameWF x := by
  rw [frontend.proj_rec.type_names] at h
  exact type_names_loop_wf _ types _ 0#usize _ r rfl (by simp [Slice.len]) ht
    (fun x hx => by simp [alloc.vec.Vec.with_capacity] at hx) h

/-! ### `proj_rec_owners_go`, the `filterMap` -/

/-- The index recursion behind `proj_rec::proj_rec_owners_go`. -/
private theorem proj_rec_owners_go_loop_refines (N : Nat) :
    ∀ (types : Slice frontend.proj_rec.ProjTypeRec)
      (ctors : Slice frontend.proj_rec.ProjCtorRec)
      (recs : Slice frontend.proj_rec.ProjRecRec) (n : Std.Usize)
      (out r : alloc.vec.Vec frontend.proj_rec.ProjRecOwner) (i : Std.Usize),
      types.val.length - i.val = N → n.val = types.val.length →
      (∀ x ∈ types.val, ProjTypeRecWF x) → (∀ c ∈ ctors.val, ProjCtorRecWF c) →
      (∀ x ∈ recs.val, ProjRecRecWF x) →
      frontend.proj_rec.proj_rec_owners_go_loop types ctors recs n out i = ok r →
      absProjRecOwners r = absProjRecOwners out ++
        ((absProjTypeRecs types).drop i.val).filterMap
          (fun q => lProjRecOwnerAt q (absProjCtorRecs ctors) (absProjRecRecs recs)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro types ctors recs n out r i hN hn htypes hctors hrecs h
    rw [frontend.proj_rec.proj_rec_owners_go_loop.eq_def] at h
    split at h
    · rename_i hlt
      have hltv : i.val < types.val.length := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨ptr, hidx, o, ho, out1, hout1, i1, hi1, hrec⟩ := h
      obtain ⟨-, hmem⟩ := slice_index_mem hidx
      obtain ⟨-, hdrop⟩ := drop_map_slice_index absProjTypeRec hidx
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      have hat := proj_rec_owner_at_refines (htypes ptr hmem) hctors hrecs ho
      rw [ih (types.val.length - i1.val) (by omega) types ctors recs n out1 r i1 rfl hn
        htypes hctors hrecs hrec, hi1v]
      simp only [absProjTypeRecs] at hdrop ⊢
      rw [hdrop, List.filterMap_cons]
      cases o with
      | none =>
        rw [← hat]
        simp only [Option.map_none]
        rw [← Result.ok_injective hout1]
      | some o1 =>
        rw [← hat]
        simp only [Option.map_some]
        rw [show absProjRecOwners out1 = absProjRecOwners out ++ [absProjRecOwner o1] from by
          rw [absProjRecOwners, absProjRecOwners, vec_push_val hout1]; simp]
        simp
    · rename_i hge
      have hle : types.val.length ≤ i.val := by scalar_tac
      rw [← Result.ok_injective h,
        List.drop_eq_nil_of_le (by simpa [absProjTypeRecs] using hle)]
      simp

/-- `proj_rec::proj_rec_owners_go` refines the cited `types.filterMap`
(`ConLeche/Frontend/ProjRec.lean:362-370`). -/
theorem proj_rec_owners_go_refines {types : Slice frontend.proj_rec.ProjTypeRec}
    {ctors : Slice frontend.proj_rec.ProjCtorRec}
    {recs : Slice frontend.proj_rec.ProjRecRec}
    {os : alloc.vec.Vec frontend.proj_rec.ProjRecOwner}
    (ht : ∀ x ∈ types.val, ProjTypeRecWF x) (hc : ∀ c ∈ ctors.val, ProjCtorRecWF c)
    (hr : ∀ x ∈ recs.val, ProjRecRecWF x)
    (h : frontend.proj_rec.proj_rec_owners_go types ctors recs = ok os) :
    absProjRecOwners os = (absProjTypeRecs types).filterMap
      (fun q => lProjRecOwnerAt q (absProjCtorRecs ctors) (absProjRecRecs recs)) := by
  rw [frontend.proj_rec.proj_rec_owners_go] at h
  rw [proj_rec_owners_go_loop_refines _ types ctors recs _
    (alloc.vec.Vec.new frontend.proj_rec.ProjRecOwner) os 0#usize rfl
    (by simp [Slice.len]) ht hc hr h]
  simp [absProjRecOwners, alloc.vec.Vec.new,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

/-! ### `proj_rec_owners`, the census's verdict -/

/-- The port's `n_pd`: the block's DECLARED parameter count, the first type
record's, `0` on an empty census. -/
private theorem n_pd_refines {types : Slice frontend.proj_rec.ProjTypeRec}
    {n_pd : Std.U64}
    (h : (if Slice.len types = 0#usize then ok 0#u64
          else do
            let ptr ← Slice.index_usize types 0#usize
            ok ptr.n_p) = ok n_pd) :
    n_pd.val = (((absProjTypeRecs types).head?.map (fun q => q.2.2.2.1)).getD 0) := by
  have hlen := Slice.len_val types
  split at h
  · rename_i hz
    have hzv : types.val = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hq : (Slice.len types).val = ((0#usize : Std.Usize)).val := by rw [hz]
      rw [hlen] at hq
      simpa using hq
    rw [← Result.ok_injective h]
    simp [absProjTypeRecs, hzv]
  · rename_i hz
    obtain ⟨ptr, hptr, h⟩ := bind_eq_ok_iff.mp h
    have hzv : 0 < types.val.length := by
      by_contra hq
      exact hz (Std.UScalar.val_eq_imp_iff.mpr (by rw [hlen]; scalar_tac))
    have hg := slice_index_getElem? hptr
    rw [show ((0#usize : Std.Usize)).val = 0 by scalar_tac] at hg
    rcases hl : types.val with _ | ⟨x, xs⟩
    · rw [hl] at hzv; simp at hzv
    · have hx : x = ptr := by rw [hl] at hg; simpa using hg
      rw [← Result.ok_injective h]
      simp [absProjTypeRecs, hl, ← hx, absProjTypeRec]

/-- `proj_rec::proj_rec_owners` refines `projRecOwners`
(`ConLeche/Frontend/ProjRec.lean:332-370`): which block members the projection
rewrite serves. -/
theorem proj_rec_owners_refines {block : alloc.vec.Vec env.ConstantInfo}
    {types : Slice frontend.proj_rec.ProjTypeRec}
    {ctors : Slice frontend.proj_rec.ProjCtorRec}
    {recs : Slice frontend.proj_rec.ProjRecRec}
    {os : alloc.vec.Vec frontend.proj_rec.ProjRecOwner}
    (hblock : ConstantInfosWF block) (ht : ∀ x ∈ types.val, ProjTypeRecWF x)
    (hc : ∀ c ∈ ctors.val, ProjCtorRecWF c) (hr : ∀ x ∈ recs.val, ProjRecRecWF x)
    (h : frontend.proj_rec.proj_rec_owners block types ctors recs = ok os) :
    absProjRecOwners os = ConLeche.Frontend.projRecOwners (absConstantInfos block)
      (absProjTypeRecs types) (absProjCtorRecs ctors) (absProjRecRecs recs) := by
  rw [frontend.proj_rec.proj_rec_owners] at h
  obtain ⟨bns, hbns, h⟩ := bind_eq_ok_iff.mp h
  have hbnsa := type_names_refines hbns
  have hbnswf := type_names_wf ht hbns
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hba := any_is_rec_refines hb
  obtain ⟨rc, hrc, h⟩ := bind_eq_ok_iff.mp h
  have hrca : rc = lRecursive (absProjTypeRecs types) (absProjCtorRecs ctors) := by
    rw [lRecursive, ← hba]
    split at hrc
    · rename_i hbt
      rw [← Result.ok_injective hrc, hbt]
      simp
    · rename_i hbf
      rw [any_ctor_mentions_refines hbnswf hc hrc, hbnsa]
      simp only [Bool.not_eq_true] at hbf
      simp [hbf]
  obtain ⟨sp, hsp, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hspa, -⟩ := StructParts.struct_parts_core_refines hblock hsp
  obtain ⟨dir, hdir, h⟩ := bind_eq_ok_iff.mp h
  have hdira : dir = (ConLeche.structPartsCore? (absConstantInfos block)).isSome := by
    rw [← hspa]
    cases sp with
    | none => rw [← Result.ok_injective hdir]; rfl
    | some p => rw [← Result.ok_injective hdir]; rfl
  rw [projRecOwners_eq]
  have hnat : ∀ (n_pd : Std.U64) (o1 : Option inductives.native_parts.NativeParts)
      (os' : alloc.vec.Vec frontend.proj_rec.ProjRecOwner),
      n_pd.val = (((absProjTypeRecs types).head?.map (fun q => q.2.2.2.1)).getD 0) →
      inductives.native_parts.native_parts n_pd block = ok o1 →
      (match o1 with
        | none => frontend.proj_rec.proj_rec_owners_go types ctors recs
        | some _ => ok (alloc.vec.Vec.new frontend.proj_rec.ProjRecOwner)) = ok os' →
      absProjRecOwners os' =
        (if (ConLeche.nativeParts?
            (((absProjTypeRecs types).head?.map (fun q => q.2.2.2.1)).getD 0)
            (absConstantInfos block)).isSome then []
         else (absProjTypeRecs types).filterMap
           (fun q => lProjRecOwnerAt q (absProjCtorRecs ctors) (absProjRecRecs recs))) := by
    intro n_pd o1 os' hn_pd hnp hgo
    obtain ⟨hnpa, -⟩ := NativeParts.native_parts_refines IndIngredients.structGens hblock hnp
    rw [hn_pd] at hnpa
    cases o1 with
    | none =>
      rw [← hnpa]
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, if_false]
      exact proj_rec_owners_go_refines ht hc hr hgo
    | some p =>
      rw [← hnpa]
      simp only [Option.map_some, Option.isSome_some, if_true]
      rw [← Result.ok_injective hgo]
      simp [absProjRecOwners, alloc.vec.Vec.new]
  split at h
  · rename_i hdt
    rw [hdira] at hdt
    split at h
    · rename_i hrt
      rw [hrca] at hrt
      rw [if_neg (by simp [hdt, hrt])]
      obtain ⟨n_pd, hn_pd, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
      exact hnat n_pd o1 os (n_pd_refines hn_pd) ho1 h
    · rename_i hrf
      rw [hrca] at hrf
      simp only [Bool.not_eq_true] at hrf
      rw [if_pos (by simp [hdt, hrf]), ← Result.ok_injective h]
      simp [absProjRecOwners, alloc.vec.Vec.new]
  · rename_i hdf
    rw [hdira] at hdf
    simp only [Bool.not_eq_true] at hdf
    rw [if_neg (by simp [hdf])]
    obtain ⟨n_pd, hn_pd, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
    exact hnat n_pd o1 os (n_pd_refines hn_pd) ho1 h

/-- `proj_rec::info_name` is `env::constant_info_name`, spelled in this module
so that `export_c`'s owner registration reads like the Lean (the Rust doc
comment's "con-leche: none"). -/
theorem info_name_refines {ci : env.ConstantInfo} {n : name.Name}
    (hc : ConstantInfoWF ci) (h : frontend.proj_rec.info_name ci = ok n) :
    absName n = ConLeche.ConstantInfo.name (absConstantInfo ci) ∧ NameWF n := by
  rw [frontend.proj_rec.info_name] at h
  exact ⟨Env.constant_info_name_refines h, Env.constant_info_name_wf hc h⟩

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/--
info: 'ConRon.Refine.Frontend.proj_rec_value_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms proj_rec_value_refines

/--
info: 'ConRon.Refine.Frontend.proj_rec_owners_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms proj_rec_owners_refines

end ConRon.Refine.Frontend

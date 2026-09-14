import ConRon.Refine.Frontend.ProjRec
import ConRon.Refine.IndNativeParts
import ConRon.Refine.IndIngredients
import ConRon.Refine.Scalars
import ConLeche.Frontend.ProjRec

/-! # The projection rewrite, exact (task #87, phase 3)

`Refine/Frontend/ProjRec.lean` (task #85, phase 1) proved the rewrite *well
formed*.  This file is the tier above: every function of
`crates/con-ron-core/src/frontend/proj_rec.rs` against the
`ConLeche/Frontend/ProjRec.lean` fragment its doc comment cites.

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
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h <;>
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

/-- `proj_rec::lam_body` refines `lamBody` (`ConLeche/Frontend/ProjRec.lean:233-237
lamBody`). -/
theorem lam_body_refines (e : expr.Expr) (he : ExprWF e) :
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
      rename_i ea e1 hand i1 hi1
      obtain ⟨hidx, hinst⟩ := hand
      obtain ⟨-, hbo, -⟩ := ExprWF.forall_e_kids hcur
      obtain ⟨hlt, hea, hdrop⟩ := ExprOps.vec_index_expr hargs hidx
      obtain ⟨habs, hwf⟩ := inst1_lift_refines hbo hea hinst
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      rw [ih (n.val - i1.val) (by omega) args e1 n i1 (cur1, ok1) rfl hn hargs hwf h,
        habs, hdrop, hi1v]
      simp [ConLeche.Frontend.instPisOpen]
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
  all_goals (intro kk; rfl)

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

end ConRon.Refine.Frontend

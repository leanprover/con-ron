/-
# `ConRon.Refine2.Frontend.Olean.FastMany` — the module reads of `olean/fast.rs`

**Task #142, Theorem 2.**  `parse_many`, `parse_at`: the name tables checked, the skeletons,
both passes, and the values read back out of the memo.
-/
import ConRon.Refine2.Frontend.Olean.FastRoots

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.region (region_loc)
open frontend.olean.fast (consts_skel consts_skel_loop many_skels many_skels_loop many_read
  many_read_loop mod_skel_read mod_skel_imports mod_skel_imports_loop mod_skel_constants
  mod_skel_constants_loop all_const_names_ok all_const_names_ok_loop many_roots parse_many parse_at
  take_decoded stmts_read stmts_read_loop stmts_roots stmts_fast run_passes)
open frontend.olean.spec (const_skel module_skel skel_fits import_map c_entry_map names_map
  const_names_ok)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Arena.Frontend.Olean (constsSkel manySkels skelFits entryMap allConstNamesOk parseMany
  parseAt stmtsFast runPasses constNamesOk)
open ConLeche.Frontend.Olean (CKindF CEntryF ImportF ModSkel constSkel moduleSkel)
open ConRon.Refine.HashMap (uscalar_add_eq uscalar_div_eq)

/-! ## `PS`: a read that takes no store -/

/-- What a read that takes no store claims of a twin's run that leaves the state alone. -/
def PSOut {α β : Type} (R : α → β → Prop) (lst : AState)
    (o : core.result.Result α frontend.olean.spec.RdErr)
    (y : Except Arena.CheckError (Option β × AState)) : Prop :=
  match o with
  | .Ok a => ∃ b, y = .ok (some b, lst) ∧ R a b
  | .Err .Bad => y = .ok (none, lst)
  | .Err (.Err e) => AErrSim e y

/-- **The judgement of a read that takes no store.** -/
def PS {α β : Type} (R : α → β → Prop) (m : Result (core.result.Result α frontend.olean.spec.RdErr))
    (x : AM (Option β)) : Prop :=
  ∀ o, m = ok o → ∀ lst, PSOut R lst o (x.run lst)

/-- The answer of the rest of a list read, then this element in front of it. -/
theorem PSOut.cons {α β : Type} {R : α → β → Prop} {lst : AState} {pre : List β} {b : β}
    {o : core.result.Result (alloc.vec.Vec α) frontend.olean.spec.RdErr} {x : AM (Option (List β))}
    {g : Option (List β) → AM (Option (List β))}
    (h : PSOut (fun v l => List.Forall₂ R v.val ((pre ++ [b]) ++ l)) lst o (x.run lst))
    (h0 : g none = pure none) (hs : ∀ l, g (some l) = pure (some (b :: l))) :
    PSOut (fun v l => List.Forall₂ R v.val (pre ++ l)) lst o ((x >>= g).run lst) := by
  cases o with
  | Ok a =>
    obtain ⟨l, hx, hR⟩ := h
    rw [am_bind_ok hx, hs]
    exact ⟨b :: l, rfl, by simpa using hR⟩
  | Err e =>
    cases e with
    | Bad =>
      rw [am_bind_ok h, h0]
      rfl
    | Err e =>
      show AErrSim e _
      rw [StateT.run_bind]
      exact AErrSim.bind h _

/-! ## The skeletons -/

/-- A skeleton whose numbers fit. -/
abbrev EV := EntryRel absWord absWord ValRel

/-- `consts_skel`'s loop, with what it has so far. -/
theorem consts_skel_loop_ps {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {consts : alloc.vec.Vec Std.U64} :
    ∀ (k : Nat) {i : Std.Usize} {out} {pre : List (CEntryF UInt64 UInt64)} {o} (lst : AState),
      consts.val.length - i.val ≤ k → List.Forall₂ EV out.val pre →
      consts_skel_loop bs r consts out i = ok o →
      PSOut (fun v l => List.Forall₂ EV v.val (pre ++ l)) lst o
        ((constsSkel (absRegion bs r) ((consts.val.drop i.val).map (·.val))).run lst) := by
  intro k
  induction k with
  | zero =>
    intro i out pre o lst hk hpre h
    rw [consts_skel_loop, ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega)]
    exact ⟨[], rfl, by simpa using hpre⟩
  | succ k ih =>
    intro i out pre o lst hk hpre h
    rw [consts_skel_loop] at h
    by_cases hi : i < alloc.vec.Vec.len consts
    · rw [ite_eq_left hi] at h
      have hlt : i.val < consts.val.length := by scalar_tac
      peel h as c, hc
      obtain ⟨_, hce⟩ := vec_index_eq hc
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, ← hce, constsSkel]
      peel h as o1, ho1
      refine sat_elim (const_skel_eq (bs := bs) (r := r) ho1) (fun hA hy => ?_) (fun sk sk' hA hy hS => ?_)
      · subst hA
        rw [hy]
        cases Result.ok_injective h
        rfl
      subst hA
      rw [hy]
      dsimp only at h ⊢
      peel h as r1, hr1
      have hF := skel_fits_refines hS hr1 (lst := lst)
      cases r1 with
      | Ok u =>
        obtain ⟨hrun, hEV⟩ := hF
        rw [am_bind_ok hrun]
        peel h as out1, ho
        peel h as i3, hi3
        have hiv : i3.val = i.val + 1 := uscalar_add_eq hi3
        rw [← hiv]
        exact PSOut.cons (ih (i := i3) lst (by omega) (pre := pre ++ [sk'])
          (by rw [ConRon.Refine.vec_push_val ho]; exact List.rel_append hpre (List.Forall₂.cons hEV List.Forall₂.nil)) h)
          rfl (fun _ => rfl)
      | Err e =>
        cases Result.ok_injective h
        cases e with
        | Bad => exact hF.elim
        | Err e =>
          show AErrSim e _
          rw [StateT.run_bind]
          exact AErrSim.bind hF _
    · rw [ite_eq_right hi] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by scalar_tac)]
      exact ⟨[], rfl, by simpa using hpre⟩

/-- **`consts_skel` is `constsSkel`.** -/
theorem consts_skel_ps {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {consts : alloc.vec.Vec Std.U64} {l : List Nat} (hl : consts.val.map (·.val) = l) :
    PS (fun v l => List.Forall₂ EV v.val l) (consts_skel bs r consts) (constsSkel (absRegion bs r) l) := by
  subst hl
  intro o h lst
  rw [consts_skel] at h
  have := consts_skel_loop_ps (pre := []) _ lst (Nat.le_refl _) (by exact List.Forall₂.nil) h
  simpa using this

/-! ## The memo as a pointer read -/

/-- A word of the memo at a location of the region, as the twin's. -/
theorem memo_word {β : Type} {A : Std.U32 → β} {v : alloc.vec.Vec Std.U32} {a : Array β}
    (h : v.val.map A = a.toList) {bs : Slice Std.U8} {c i : Std.U64} {x : Std.U32} {d : β}
    (hc : c.val + 8 ≤ bs.val.length) (hi : c / 8#u64 = ok i)
    (hx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U32) v
      (UScalar.cast UScalarTy.Usize i) = ok x) :
    a.getD (c.val / 8) d = A x := by
  rw [← word_at h hi hx (d := d), tr_of_le]
  have := bytes_le_max bs
  omega

/-- **The memo as `PtrRead`.** -/
theorem ds_ptr_rel {pk bs r pers} {d : frontend.olean.fast.DS} {t : TDS} (hr : RegionFits bs r)
    (hd : DSRel d t) :
    PtrRel frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecPtrRead d
      (ConRon.Arena.Frontend.Olean.DS.read (absPins pk) (absRegion bs r) t) pk bs r pers where
  nm st lst v := by
    show RS _ _ _ _ (frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecPtrRead.rd_name d pk pers st.store bs r v)
      (pure (ConRon.Arena.Frontend.Olean.DS.nameOf (absPins pk) (absRegion bs r) t (absWord v)))
    rw [frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecPtrRead.rd_name]
    simp only [ConRon.Arena.Frontend.Olean.DS.nameOf]
    by_cases hv : v = 1#u64
    · rw [ite_eq_left hv, ite_eq_left (word_eq_one.mpr hv)]
      refine RS.pure_step fun n hn => ?_
      rw [nidx_dup2_ok hn]
      exact RS.some rfl
    · rw [ite_eq_right hv, ite_eq_right (fun he => hv (word_eq_one.mp he))]
      refine RS.pure_step fun o ho => ?_
      rw [← region_loc_eq bs ho]
      cases o with
      | none => exact RS.none
      | some c =>
        simp only [lift, bind_ok]
        refine RS.pure_step fun i hi => RS.pure_step fun x hx => RS.pure_step fun n hn => ?_
        cases Result.ok_injective hn
        simp only [locOf, Option.map_some]
        rw [memo_word hd.names (region_loc_fits hr ho) hi hx]
        exact RS.some rfl
  ex st lst v := by
    show RS _ _ _ _ (frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecPtrRead.rd_expr d pk pers st.store bs r v)
      (pure (ConRon.Arena.Frontend.Olean.DS.exprOf (absRegion bs r) t (absWord v)))
    rw [frontend.olean.fast.DS.Insts.Con_ron_coreFrontendOleanSpecPtrRead.rd_expr]
    simp only [ConRon.Arena.Frontend.Olean.DS.exprOf]
    refine RS.pure_step fun o ho => ?_
    rw [← region_loc_eq bs ho]
    cases o with
    | none => exact RS.none
    | some c =>
      simp only [lift, bind_ok]
      refine RS.pure_step fun i hi => RS.pure_step fun x hx => RS.pure_step fun n hn => ?_
      cases Result.ok_injective hn
      simp only [locOf, Option.map_some]
      rw [memo_word hd.exprs (region_loc_fits hr ho) hi hx]
      exact RS.some rfl

end ConRon.Refine2.Frontend.Olean

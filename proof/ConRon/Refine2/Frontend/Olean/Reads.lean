/-
# `ConRon.Refine2.Frontend.Olean.Reads` — `olean/reads.rs` against the twin's

**Task #142, Theorem 2.**  The reads of a part of a `ModuleData`: the name positions, one
constant, some statements.
-/
import ConRon.Refine2.Frontend.Olean.FastMany
import ConRon.Refine2.Frontend.Olean.Sparse
import ConRon.Refine2.Frontend.Olean.Header

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.spec (const_skel module_skel skel_fits name_p)
open frontend.olean.reads (c_kind_skipped c_kind_tag distinct_go distinct_go_loop name_position
  name_positions_go name_positions_go_loop imports_named imports_named_loop name_positions_at
  entry_at stmts_at)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Arena.Frontend.Olean (namePosition namePositionsAt entryAt stmtsAt nameP)
open ConLeche.Frontend.Olean (CKindF CEntryF ImportF ModSkel constSkel moduleSkel distinctGo)
open ConRon.Refine.HashMap (uscalar_add_eq)

/-! ## The kinds -/

/-- **`c_kind_tag` is `CKindF.tag`.** -/
theorem c_kind_tag_eq {N N' E E' : Type} {AN : N → N'} {AE : E → E'} {RN : NatRel}
    {k : frontend.olean.spec.CKindF N E} {k' : CKindF N' E'} (hk : KindRel AN AE RN k k') {x : Std.U64}
    (h : c_kind_tag k = ok x) : x.val = k'.tag := by
  delta c_kind_tag at h
  cases k <;> cases k' <;> first
    | exact hk.elim
    | (cases Result.ok_injective h; rfl)

/-- **`c_kind_skipped` is `CKindF.skipped`.** -/
theorem c_kind_skipped_eq {N N' E E' : Type} {AN : N → N'} {AE : E → E'} {RN : NatRel}
    {k : frontend.olean.spec.CKindF N E} {k' : CKindF N' E'} (hk : KindRel AN AE RN k k') {b : Bool}
    (h : c_kind_skipped k = ok b) : b = k'.skipped := by
  delta c_kind_skipped at h
  cases k <;> cases k' <;> try exact hk.elim
  case Defn.defn v h1 s v' h' s' =>
    obtain ⟨-, -, rfl, w⟩ := hk
    dsimp only at h
    simp only [lift, bind_ok] at h
    peel h as b1, hb1
    cases Result.ok_injective h
    have hv : (Std.Array.to_slice frontend.olean.reads.c_kind_skipped.S_SAFE).val
        = [115#u32, 97#u32, 102#u32, 101#u32] := by
      unfold frontend.olean.reads.c_kind_skipped.S_SAFE; rfl
    have e := ConRon.Refine2.Frontend.cps_beq_str w (by rw [hv]; decide) hb1
    rw [hv] at e
    have e' : (b1 = true) ↔ ConRon.Refine.absString s = "safe" := e
    show decide (¬ b1 = true) = (ConRon.Refine.absString s != "safe")
    by_cases hs : ConRon.Refine.absString s = "safe"
    · rw [hs]; simp [e'.mpr hs]
    · have : ¬ b1 = true := fun hb => hs (e'.mp hb)
      simp [this, hs]
  case Ax.ax =>
    cases (show _ = _ from hk)
    exact (Result.ok_injective h).symm
  case Thm.thm =>
    exact (Result.ok_injective h).symm
  case Opaq.opaq =>
    obtain ⟨-, rfl⟩ := hk
    exact (Result.ok_injective h).symm
  case Quot.quot =>
    exact (Result.ok_injective h).symm
  case Induct.induct =>
    obtain ⟨-, -, -, -, -, -, rfl, -⟩ := hk
    exact (Result.ok_injective h).symm
  case Ctor.ctor =>
    obtain ⟨-, -, -, -, rfl⟩ := hk
    exact (Result.ok_injective h).symm
  case Recur.recur =>
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := hk
    exact (Result.ok_injective h).symm

/-! ## The name positions -/

/-- `reads::NamePosition`, as the twin's. -/
def absNamePos (p : frontend.olean.reads.NamePosition) : ConRon.Arena.Frontend.Olean.NamePosition :=
  ⟨p.loc.val, absNIdx p.name, p.tag.val, p.skipped⟩

/-- `reads::NamePositions`, as the twin's. -/
def absNamePositions (p : frontend.olean.reads.NamePositions) :
    ConRon.Arena.Frontend.Olean.NamePositions :=
  ⟨⟨p.header.is_module, (p.header.imports.val.map (absImportF absNIdx)).toArray⟩,
    (p.consts.val.map absNamePos).toArray⟩

/-- **`name_position` is `namePosition`.** -/
theorem name_position_refines {pk bs r pers st lst} {c : Std.U64} (hr : RegionFits bs r) :
    RS pers (EqA absNamePos) st lst (name_position pk pers st.store bs r c)
      (namePosition (absPins pk) (absRegion bs r) c.val) := by
  rw [name_position, namePosition]
  refine RS.pure_step fun o ho => ?_
  refine sat_elim (const_skel_eq (bs := bs) (r := r) ho) (fun hA hy => ?_) (fun sk sk' hA hy hS => ?_)
  · subst hA
    rw [hy]
    exact RS.none
  subst hA
  rw [hy]
  dsimp only
  rw [← hS.name]
  refine RS.bind_of (name_p_refines hr) (fun _ _ => rfl) rfl fun a b s1 lst1 hR => ?_
  cases hR
  refine RS.pure_step fun i hi => RS.pure_step fun b1 hb1 => ?_
  rw [← c_kind_tag_eq hS.kind hi, ← c_kind_skipped_eq hS.kind hb1]
  exact RS.some rfl

/-- **`name_positions_go` is `consts.mapM`.** -/
theorem name_positions_go_refines {pk bs r pers} {consts : alloc.vec.Vec Std.U64} {l : List Nat}
    (hr : RegionFits bs r) (hl : consts.val.map (·.val) = l) (st lst) :
    RS pers (fun v l' => List.Forall₂ (EqA absNamePos) v.val l') st lst
      (name_positions_go pk pers st.store bs r consts)
      (l.mapM (m := OptionT AM) fun c => OptionT.mk (namePosition (absPins pk) (absRegion bs r) c)) := by
  subst hl
  rw [name_positions_go]
  refine RS.vec_map (R := EqA absNamePos)
    (loop := fun ar out i => name_positions_go_loop pk pers ar bs r consts out i)
    (forall₂_of_map (A := fun v : Std.U64 => v.val) consts.val) ?_ ?_ (by simp) (by rfl)
  · intro ar out i hi
    show name_positions_go_loop pk pers ar bs r consts out i = _
    rw [name_positions_go_loop, ite_eq_right (by scalar_tac)]
  · intro i out x x' K Rf st lst hx hS hK
    cases hS
    show RS _ _ _ _ (name_positions_go_loop pk pers st.store bs r consts out i) _
    rw [name_positions_go_loop,
      ite_eq_left (by have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)]
    refine RS.pure_step fun y hy => ?_
    have hy3 := ConRon.Refine.ExprOps.vec_index_getElem? hy
    rw [hx] at hy3
    cases Option.some.inj hy3
    refine RS.bindT (name_position_refines hr) (fun _ _ => by rfl) fun a b s1 lst1 hR =>
      RS.pure_step fun out1 ho => RS.pure_step fun i3 hi3 => ?_
    exact hK a b s1 lst1 out1 i3 hR (ConRon.Refine.vec_push_val ho) (uscalar_add_eq hi3)

/-- **`imports_named` is `imports.mapM (ImportF.mapM (nameP r))`.** -/
theorem imports_named_refines {pk bs r pers} {imports : alloc.vec.Vec (frontend.olean.spec.ImportF Std.U64)}
    {l : List (ImportF UInt64)} (hr : RegionFits bs r) (hl : imports.val.map (absImportF absWord) = l)
    (st lst) :
    RS pers (fun v l' => List.Forall₂ (EqA (absImportF absNIdx)) v.val l') st lst
      (imports_named pk pers st.store bs r imports)
      (l.mapM (m := OptionT AM) fun i =>
        ImportF.mapM (m := OptionT AM) (fun v => OptionT.mk (nameP (absPins pk) (absRegion bs r) v)) i) := by
  subst hl
  have hp := name_p_read_rel (pk := pk) (pers := pers) hr
  rw [imports_named]
  refine RS.vec_map (R := EqA (absImportF absNIdx))
    (loop := fun ar out i => imports_named_loop pk pers ar bs r imports out i)
    (forall₂_of_map (A := absImportF absWord) imports.val) ?_ ?_ (by simp) (by rfl)
  · intro ar out i hi
    show imports_named_loop pk pers ar bs r imports out i = _
    rw [imports_named_loop, ite_eq_right (by scalar_tac)]
  · intro i out x x' K Rf st lst hx hS hK
    cases hS
    show RS _ _ _ _ (imports_named_loop pk pers st.store bs r imports out i) _
    rw [imports_named_loop,
      ite_eq_left (by have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)]
    refine RS.pure_step fun y hy => ?_
    have hy3 := ConRon.Refine.ExprOps.vec_index_getElem? hy
    rw [hx] at hy3
    cases Option.some.inj hy3
    refine RS.bindT (import_map_refines hp st lst) (fun _ _ => by rfl) fun a b s1 lst1 hR =>
      RS.pure_step fun out1 ho => RS.pure_step fun i3 hi3 => ?_
    exact hK a b s1 lst1 out1 i3 hR (ConRon.Refine.vec_push_val ho) (uscalar_add_eq hi3)

/-- `distinct_go`'s loop is `distinctGo`, the `seen` table the twin's set. -/
theorem distinct_go_loop_eq {cs : alloc.vec.Vec frontend.olean.reads.NamePosition} :
    ∀ (k : Nat) {i : Std.Usize} {s} {se : _root_.Std.HashSet NIdx} {b : Bool},
      cs.val.length - i.val ≤ k → SeenRel s se → distinct_go_loop cs s i = ok b →
      b = distinctGo ((cs.val.drop i.val).map fun p => absNIdx p.name) se := by
  intro k
  induction k with
  | zero =>
    intro i s se b hk hS h
    rw [distinct_go_loop, ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ k ih =>
    intro i s se b hk hS h
    rw [distinct_go_loop] at h
    by_cases hi : i < alloc.vec.Vec.len cs
    · rw [ite_eq_left hi] at h
      have hlt : i.val < cs.val.length := by scalar_tac
      peel h as np, hnp
      obtain ⟨_, hne⟩ := vec_index_eq hnp
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, ← hne, distinctGo]
      peel h as b1, hb1
      have e := SetRel.contains_key nidx_eq2 hS hb1
      simp only [_root_.Std.HashSet.containsThenInsert_fst, _root_.Std.HashSet.containsThenInsert_snd, ← e]
      cases b1 with
      | true =>
        cases Result.ok_injective h
        rfl
      | false =>
        rw [ite_eq_right Bool.false_ne_true] at h
        peel h as n, hn
        peel h as q, hq
        obtain ⟨old, s1⟩ := q
        rw [nidx_dup2_ok hn] at hq
        peel h as i2, hi2
        have hiv : i2.val = i.val + 1 := uscalar_add_eq hi2
        rw [Bool.not_false, Bool.true_and, ← hiv]
        exact ih (by omega) (SetRel.insert nidx_eq2 absNIdx_inj hS hq) h
    · rw [ite_eq_right hi] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by scalar_tac)]
      rfl

/-- **`distinct_go` is `distinctGo`.** -/
theorem distinct_go_eq {cs : alloc.vec.Vec frontend.olean.reads.NamePosition} {b : Bool} {n : Nat}
    (h : distinct_go cs = ok b) :
    b = distinctGo (cs.val.map fun p => absNIdx p.name) (_root_.Std.HashSet.emptyWithCapacity n) := by
  rw [distinct_go] at h
  peel h as s, hs
  simpa using distinct_go_loop_eq _ (i := 0#usize) (Nat.le_refl _) (SetRel.with_capacity hs) h

/-- **`name_positions_at` is `namePositionsAt`.** -/
theorem name_positions_at_refines {pk bs r pers st lst} {root : Std.U64} (hr : RegionFits bs r) :
    RS pers (EqA absNamePositions) st lst (name_positions_at pk pers st.store bs r root)
      (namePositionsAt (absPins pk) (absRegion bs r) (absWord root)) := by
  rw [name_positions_at, namePositionsAt]
  refine RS.pure_step fun o ho => ?_
  refine sat_elim (module_skel_eq hr ho) (fun hA hy => ?_) (fun sk sk' hA hy hS => ?_)
  · subst hA
    rw [hy]
    exact RS.none
  subst hA
  rw [hy]
  dsimp only
  show RS _ _ _ _ _ (_ >>= _ : OptionT AM _)
  refine RS.bindT (imports_named_refines hr hS.imports st lst) (fun _ _ => by rfl)
    fun a b s1 lst1 hR => ?_
  show RS _ _ _ _ _ (_ >>= _ : OptionT AM _)
  refine RS.bindT (name_positions_go_refines hr hS.consts (withStore st s1) lst1) (fun _ _ => by rfl)
    fun a2 b2 s2 lst2 hR2 => ?_
  have e2 := forall₂_eqA hR2
  subst e2
  refine RS.pure_step fun b1 hb1 => ?_
  have ed := distinct_go_eq (n := (a2.val.map absNamePos).length) hb1
  have em : (a2.val.map absNamePos).map (·.name) = a2.val.map fun p => absNIdx p.name := by
    simp [absNamePos]
  rw [em, ← ed]
  cases b1 with
  | false => exact RS.none
  | true =>
    simp only [↓reduceIte]
    refine RS.some ?_
    show _ = _
    rw [← forall₂_eqA hR, ← hS.isModule]
    rfl

/-! ## One constant, some statements -/

/-- **`entry_at` is `entryAt`.** -/
theorem entry_at_refines {pk bs r pers st lst} {c : Std.U64} (hr : RegionFits bs r) :
    RS pers (EntryRel absNIdx absEIdx ValRel) st lst (entry_at pk pers st.store bs r c)
      (entryAt (absPins pk) (absRegion bs r) c.val) := by
  rw [entry_at, entryAt]
  refine RS.pure_step fun o ho => ?_
  refine sat_elim (const_skel_eq (bs := bs) (r := r) ho) (fun hA hy => ?_) (fun sk sk' hA hy hS => ?_)
  · subst hA
    rw [hy]
    exact RS.none
  subst hA
  rw [hy]
  dsimp only
  refine RS.pure_step fun r1 hr1 => ?_
  intro hrel hinv o s' hm
  have hF := skel_fits_refines hS hr1 (lst := lst)
  cases r1 with
  | Ok u =>
    obtain ⟨hrun, hEV⟩ := hF
    rw [am_bind_ok hrun]
    exact sparse_entry_refines hr hEV hrel hinv o s' hm
  | Err e =>
    cases Result.ok_injective hm
    cases e with
    | Bad => exact hF.elim
    | Err e =>
      show AErrSim e _
      rw [StateT.run_bind]
      exact AErrSim.bind hF _

/-- **`stmts_at` is `stmtsAt`.** -/
theorem stmts_at_refines {pk bs r pers st lst} {cs : alloc.vec.Vec Std.U64} {l : List Nat}
    (hr : RegionFits bs r) (hl : cs.val.map (·.val) = l) :
    RS pers (fun v l' => List.Forall₂ (EqA absStmt) v.val l') st lst
      (stmts_at pk pers st.store bs r cs) (stmtsAt (absPins pk) (absRegion bs r) l) := by
  rw [stmts_at, stmtsAt]
  exact RS.ps_bind (consts_skel_ps hl) (fun _ => rfl) rfl fun sks l' hR => stmts_fast_refines hr hR

end ConRon.Refine2.Frontend.Olean

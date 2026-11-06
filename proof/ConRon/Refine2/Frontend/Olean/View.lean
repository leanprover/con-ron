/-
# `ConRon.Refine2.Frontend.Olean.View` — `olean/view.rs` against `Arena/Frontend/Olean/View.lean`

**Task #142, Theorem 2.**  A view is upstream's `ModFiles.viewRegion`: `ViewO` says of the Rust's
answer that its bytes and its region are upstream's, and that they fit, which the reads ask.
`region_dup` is the identity.  `parse_view` is the twin's `parseView`.
-/
import ConRon.Refine2.Frontend.Olean.ModFilesRel
import ConRon.Refine2.Frontend.Olean.FastMany
import ConRon.Refine2.Frontend.Olean.Header
import ConRon.Arena.Frontend.Olean.View

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.region (region_single part_module_data_addr region_of_parts2 region_of_parts3
  region_loc)
open frontend.olean.spec (module_skel)
open frontend.olean.view (mod_files_is_module view_bytes view_region_of region_dup region_dup_loop
  view_server view_private mod_files_view_region rules_dup rules_dup_loop c_kind_dup c_entry_dup
  mod_decoded_dup mod_decoded_dup_loop0 mod_decoded_dup_loop1 loc_is_some loc_in_two all_views_at
  mod_files_up_to check_imports_pre parse_view parse_all_views parse_all_views_module)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConLeche.Frontend.Olean (ModFiles OLeanLevel)
open ConLeche.Frontend.Olean.Region (ofParts single)
open ConRon.Arena
open ConRon.Arena.Frontend.Olean (checkImportsPre parseView parseAllViews parseAllViewsModule parseAt
  parseMany importsPre)

/-! ## The copies -/

theorem vec_ext {α : Type} {a b : alloc.vec.Vec α} (h : a.val = b.val) : a = b :=
  alloc.vec.Vec.ext a b h

theorem add_one_usize {i j : Std.Usize} (h : i + 1#usize = ok j) : j.val = i.val + 1 := by
  rw [ConRon.Refine.HashMap.uscalar_add_eq h]; rfl

/-- **A loop that copies a vector.** -/
theorem dup_walk {α : Type} {v : List α}
    {L : Std.Usize → alloc.vec.Vec α → Result (alloc.vec.Vec α)}
    (hL : ∀ i out r, L i out = ok r → (v.length ≤ i.val ∧ r = out) ∨
      ∃ x out' j, v[i.val]? = some x ∧ out'.val = out.val ++ [x] ∧ j.val = i.val + 1 ∧ L j out' = ok r)
    (n : Nat) : ∀ i out r, v.length - i.val ≤ n → out.val = v.take i.val → L i out = ok r → r.val = v := by
  induction n with
  | zero =>
    intro i out r hn ho h
    rcases hL i out r h with ⟨hle, rfl⟩ | ⟨x, _, _, hx, _⟩
    · rw [ho, List.take_of_length_le hle]
    · have := (List.getElem?_eq_some_iff.mp hx).1
      omega
  | succ n ih =>
    intro i out r hn ho h
    rcases hL i out r h with ⟨hle, rfl⟩ | ⟨x, out', j, hx, ho', hj, hl⟩
    · rw [ho, List.take_of_length_le hle]
    · have hlt := (List.getElem?_eq_some_iff.mp hx).1
      refine ih j out' r (by omega) ?_ hl
      rw [ho', ho, hj, List.take_add_one, hx]
      rfl

/-- The walk's start. -/
theorem dup_walk0 {α : Type} {v : List α} {c : Std.Usize}
    {L : Std.Usize → alloc.vec.Vec α → Result (alloc.vec.Vec α)}
    (hL : ∀ i out r, L i out = ok r → (v.length ≤ i.val ∧ r = out) ∨
      ∃ x out' j, v[i.val]? = some x ∧ out'.val = out.val ++ [x] ∧ j.val = i.val + 1 ∧ L j out' = ok r)
    {r : alloc.vec.Vec α} (h : L 0#usize (alloc.vec.Vec.with_capacity α c) = ok r) : r.val = v :=
  dup_walk hL _ 0#usize _ r (Nat.le_refl _) (by simp) h

theorem len_le_of_not_lt {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    (hc : ¬ i < alloc.vec.Vec.len v) : v.val.length ≤ i.val := by
  have : ¬ i.val < v.val.length := by simpa [UScalar.lt_equiv] using hc
  omega

/-- **`region_dup` is the identity.** -/
theorem region_dup_eq {r r' : frontend.olean.region.Region} (h : region_dup r = ok r') : r' = r := by
  rw [region_dup] at h
  peel h as segs, hs
  cases Result.ok_injective h
  have e : segs.val = r.segs.val := by
    refine dup_walk0 (L := fun i out => region_dup_loop r.segs out i) ?_ hs
    intro i out o h
    rw [region_dup_loop] at h
    by_cases hc : i < alloc.vec.Vec.len r.segs
    · rw [ite_eq_left hc] at h
      peel h as x, hx
      peel h as o1, ho1
      peel h as j, hj
      exact Or.inr ⟨x, o1, j, ConRon.Refine.ExprOps.vec_index_getElem? hx,
        ConRon.Refine.vec_push_val ho1, add_one_usize hj, h⟩
    · rw [ite_eq_right hc] at h
      exact Or.inl ⟨len_le_of_not_lt hc, (Result.ok_injective h).symm⟩
  have e2 : segs = r.segs := vec_ext e
  rw [e2]

/-! ## `isModule` and the region of a view -/

/-- `view::OLeanLevel`, as upstream's. -/
def absLevel : frontend.olean.view.OLeanLevel → OLeanLevel
  | .Exported => .exported
  | .Server => .server
  | .Private => .private

/-- **`mod_files_is_module` is `ModFiles.isModule`.** -/
theorem mod_files_is_module_eq {f : frontend.olean.view.ModFiles} {f' : ModFiles}
    (hf : ModFilesRel f f') {b : Bool} (h : mod_files_is_module f = ok b) : b = f'.isModule := by
  rw [mod_files_is_module] at h
  peel h as r, hr
  peel h as i, hi
  peel h as o, ho
  obtain ⟨e1, e2⟩ := region_single_eq hf.fitsE hr
  have hrel := module_skel_eq e2 ho
  rw [e1, part_module_data_addr_eq hi, ← hf.exported] at hrel
  rw [ModFiles.isModule]
  revert hrel
  generalize ConLeche.Frontend.Olean.moduleSkel (single f'.exported) f'.exported.moduleDataAddr = y
  intro hrel
  cases hrel with
  | none => exact (Result.ok_injective h).symm
  | some hs =>
    exact (Result.ok_injective h).symm.trans hs.isModule

/-- What a Rust view says of upstream's. -/
def ViewOk (f : frontend.olean.view.ModFiles) (vb : frontend.olean.view.ViewBytes) (a : Std.U64)
    (y : Option (ConLeche.Frontend.Olean.Region × UInt64)) : Prop :=
  ∀ bs r, view_bytes f vb = ok bs → view_region_of f vb = ok r →
    y = some (absRegion bs r, absWord a) ∧ RegionFits bs r

/-- **The answer of a Rust view function, against upstream's `Option`.** -/
def ViewO (f : frontend.olean.view.ModFiles)
    (o : Option (frontend.olean.view.ViewBytes × Std.U64))
    (y : Option (ConLeche.Frontend.Olean.Region × UInt64)) : Prop :=
  match o with
  | none => y = none
  | some (vb, a) => ViewOk f vb a y

theorem view_exported {f : frontend.olean.view.ModFiles} {f' : ModFiles} (hf : ModFilesRel f f')
    {i : Std.U64} (h : part_module_data_addr f.exported = ok i) :
    ViewOk f .Exported i (some (single f'.exported, f'.exported.moduleDataAddr)) := by
  intro bs r hb hr
  cases Result.ok_injective hb
  obtain ⟨e1, e2⟩ := region_single_eq hf.fitsE hr
  refine ⟨?_, e2⟩
  rw [e1, part_module_data_addr_eq h, hf.exported]

theorem view_joined {f : frontend.olean.view.ModFiles} {b : frontend.olean.region.RegionBuf}
    {a : Std.U64} {y} (hy : y = some (absRegion (alloc.vec.Vec.deref b.bytes) b.region, absWord a))
    (hfit : RegionFits (alloc.vec.Vec.deref b.bytes) b.region) : ViewOk f (.Joined b) a y := by
  intro bs r hb hr
  cases Result.ok_injective hb
  obtain rfl := region_dup_eq hr
  exact ⟨hy, hfit⟩

/-- `view_server`: the `.server` arm when the module is one. -/
theorem view_server_eq {f : frontend.olean.view.ModFiles} {f' : ModFiles} (hf : ModFilesRel f f')
    {o} (h : view_server f = ok o) :
    ViewO f o (do
      let s ← f'.server
      let r ← (ofParts #[f'.exported, s]).toOption
      pure (r, s.moduleDataAddr)) := by
  rw [view_server] at h
  rw [hf.server, hf.exported]
  cases hs : f.server with
  | none =>
    rw [hs] at h
    cases Result.ok_injective h
    rfl
  | some s =>
    rw [hs] at h
    dsimp only at h
    peel h as r, hr
    have e := region_of_parts2_eq hf.fitsE (hf.fitsS s hs) hr
    cases r with
    | Err _ =>
      cases Result.ok_injective h
      obtain ⟨-, m, em⟩ := e
      simp [ViewO, em, Except.toOption]
    | Ok b =>
      peel h as i, hi
      cases Result.ok_injective h
      obtain ⟨em, hfit⟩ := e
      refine view_joined ?_ hfit
      simp [em, Except.toOption, part_module_data_addr_eq hi]

/-- `view_private`: the `.private` arm when the module is one. -/
theorem view_private_eq {f : frontend.olean.view.ModFiles} {f' : ModFiles} (hf : ModFilesRel f f')
    {o} (h : view_private f = ok o) :
    ViewO f o (do
      let s ← f'.server
      let p ← f'.private
      let r ← (ofParts #[f'.exported, s, p]).toOption
      pure (r, p.moduleDataAddr)) := by
  rw [view_private] at h
  rw [hf.server, hf.private, hf.exported]
  cases hs : f.server with
  | none =>
    rw [hs] at h
    cases Result.ok_injective h
    rfl
  | some s =>
    rw [hs] at h
    dsimp only at h
    cases hp : f.private_part with
    | none =>
      rw [hp] at h
      cases Result.ok_injective h
      rfl
    | some p =>
      rw [hp] at h
      dsimp only at h
      peel h as r, hr
      have e := region_of_parts3_eq hf.fitsE (hf.fitsS s hs) (hf.fitsP p hp) hr
      cases r with
      | Err _ =>
        cases Result.ok_injective h
        obtain ⟨-, m, em⟩ := e
        simp [ViewO, em, Except.toOption]
      | Ok b =>
        peel h as i, hi
        cases Result.ok_injective h
        obtain ⟨em, hfit⟩ := e
        refine view_joined ?_ hfit
        simp [em, Except.toOption, part_module_data_addr_eq hi]

/-- **`mod_files_view_region` is `ModFiles.viewRegion`.** -/
theorem mod_files_view_region_eq {f : frontend.olean.view.ModFiles} {f' : ModFiles}
    (hf : ModFilesRel f f') {level : frontend.olean.view.OLeanLevel} {o}
    (h : mod_files_view_region f level = ok o) : ViewO f o (f'.viewRegion (absLevel level)) := by
  delta mod_files_view_region at h
  cases level with
  | Exported =>
    dsimp only at h
    peel h as i, hi
    cases Result.ok_injective h
    exact view_exported hf hi
  | Server =>
    dsimp only at h
    peel h as b, hb
    have e := mod_files_is_module_eq hf hb
    rw [absLevel, ModFiles.viewRegion, ← e]
    cases b with
    | true =>
      rw [ite_eq_left rfl] at h ⊢
      exact view_server_eq hf h
    | false =>
      rw [ite_eq_right (by simp)] at h ⊢
      peel h as i, hi
      cases Result.ok_injective h
      exact view_exported hf hi
  | Private =>
    dsimp only at h
    peel h as b, hb
    have e := mod_files_is_module_eq hf hb
    rw [absLevel, ModFiles.viewRegion, ← e]
    cases b with
    | true =>
      rw [ite_eq_left rfl] at h ⊢
      exact view_private_eq hf h
    | false =>
      rw [ite_eq_right (by simp)] at h ⊢
      peel h as i, hi
      cases Result.ok_injective h
      exact view_exported hf hi

/-! ## `parse_view` -/

/-- The imports of a header, as the twin's array. -/
@[reducible] def absImports (v : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)) :
    Array (ConLeche.Frontend.Olean.ImportF NIdx) :=
  (v.val.map (absImportF absNIdx)).toArray

theorem dec_imports {d d'} (hd : ModDecodedRel d d') : d'.imports = absImports d.imports := by
  rw [absImports, hd.imports]

/-- `imports_pre` of a module's exported file is `importsPre`. -/
theorem imports_pre_ok {pk pers f f'} (hf : ModFilesRel f f') (st lst) :
    RS pers (EqA absImports) st lst
      (frontend.olean.header.imports_pre pk pers st.store (alloc.vec.Vec.deref f.exported.bytes))
      (importsPre (absPins pk) (absBytes (alloc.vec.Vec.deref f.exported.bytes))) :=
  imports_pre_refines (by rw [deref_val]; exact hf.fitsE.size)

/-- **`check_imports_pre` is `checkImportsPre`.** -/
theorem check_imports_pre_refines {pk pers st lst f f' d d'}
    (hf : ModFilesRel f f') (hd : ModDecodedRel d d') :
    RS pers ModDecodedRel st lst (check_imports_pre pk pers st.store f d) (checkImportsPre (absPins pk) f' d') := by
  rw [check_imports_pre, checkImportsPre, hf.exported]
  refine RS.of_eq (RS.bind (g := fun pre => if pre == d'.imports then pure (some d') else pure none)
    (imports_pre_ok hf st lst) (fun e s1 => by cases e <;> rfl) fun a b s1 lst1 hab => ?_) ?_
  · cases hab
    refine RS.pure_step fun c hc => ?_
    rw [dec_imports hd, ← imports_beq_eq hc]
    cases c with
    | true =>
      rw [ite_eq_left rfl]
      exact RS.some hd
    | false =>
      rw [ite_eq_right (by simp)]
      exact RS.none
  · congr 1
    funext o
    cases o <;> rfl

/-- **`parse_view` is `parseView`.** -/
theorem parse_view_refines {pk pers st lst f f' level}
    (hf : ModFilesRel f f') :
    RS pers ModDecodedRel st lst (parse_view pk pers st.store f level) (parseView (absPins pk) f' (absLevel level)) := by
  rw [parse_view, parseView]
  refine RS.pure_step fun o ho => ?_
  have hV := mod_files_view_region_eq hf ho
  cases o with
  | none =>
    rw [show f'.viewRegion (absLevel level) = none from hV]
    exact RS.none
  | some p =>
    obtain ⟨vb, a⟩ := p
    dsimp only
    refine RS.pure_step fun bs hb => RS.pure_step fun r hr => ?_
    obtain ⟨e, hfit⟩ := hV bs r hb hr
    rw [e]
    dsimp only
    refine RS.of_eq (RS.bind (g := fun d => checkImportsPre (absPins pk) f' d) (parse_at_refines hfit) ?_ ?_) ?_
    · intros; rfl
    · intro _ _ _ _ hab
      exact check_imports_pre_refines hf hab
    · congr 1
      funext o
      cases o <;> rfl

end ConRon.Refine2.Frontend.Olean

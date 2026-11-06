/-
# `ConRon.Refine2.Frontend.Olean.View` — `olean/view.rs` against `Arena/Frontend/Olean/View.lean`

**Task #142, Theorem 2.**  A view is upstream's `ModFiles.viewRegion`: `ViewO` says of the Rust's
answer that its bytes and its region are upstream's, and that they fit, which the reads ask.
What `view.rs` copies, it copies: `region_dup`, `c_entry_dup`, `mod_decoded_dup` are the identity.
-/
import ConRon.Refine2.Frontend.Olean.ModFilesRel
import ConRon.Refine2.Frontend.Olean.Skel
import ConRon.Arena.Frontend.Olean.View

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.region (region_single part_module_data_addr region_of_parts2 region_of_parts3
  region_loc)
open frontend.olean.spec (module_skel)
open frontend.olean.view (mod_files_is_module view_bytes view_region_of region_dup region_dup_loop
  view_server view_private mod_files_view_region rules_dup rules_dup_loop c_kind_dup c_entry_dup
  mod_decoded_dup mod_decoded_dup_loop0 mod_decoded_dup_loop1 loc_is_some loc_in_two all_views_at
  mod_files_up_to)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConLeche.Frontend.Olean (ModFiles OLeanLevel)
open ConLeche.Frontend.Olean.Region (ofParts single)

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

theorem not_lt_len {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
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
      exact Or.inl ⟨not_lt_len hc, (Result.ok_injective h).symm⟩
  have e2 : segs = r.segs := vec_ext e
  rw [e2]

/-- **`rules_dup` is the identity.** -/
theorem rules_dup_eq {r r' : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx)}
    (h : rules_dup r = ok r') : r' = r := by
  rw [rules_dup] at h
  refine vec_ext (dup_walk0 (L := fun i out => rules_dup_loop r out i) ?_ h)
  intro i out o h
  rw [rules_dup_loop] at h
  by_cases hc : i < alloc.vec.Vec.len r
  · rw [ite_eq_left hc] at h
    peel h as ⟨n, u, e⟩, hx
    peel h as n1, hn1
    obtain rfl := nidx_dup2_ok hn1
    peel h as e1, he1
    obtain rfl := eidx_dup2_ok he1
    peel h as o1, ho1
    peel h as j, hj
    exact Or.inr ⟨_, o1, j, ConRon.Refine.ExprOps.vec_index_getElem? hx,
      ConRon.Refine.vec_push_val ho1, add_one_usize hj, h⟩
  · rw [ite_eq_right hc] at h
    exact Or.inl ⟨not_lt_len hc, (Result.ok_injective h).symm⟩

theorem nidx_vec_dup_eq {v v' : alloc.vec.Vec arena.handle.NIdx}
    (h : arena.env.nidx_vec_dup v = ok v') : v' = v :=
  vec_ext (ConRon.Refine2.nidx_vec_dup_val h)

theorem hints_dup_self {h r : frontend.scan_types.HintsRec}
    (e : frontend.olean.spec.hints_dup h = ok r) : r = h := by
  cases h <;> exact (Result.ok_injective e).symm

/-- **`c_kind_dup` is the identity.** -/
theorem c_kind_dup_eq {k k' : frontend.olean.spec.CKindF arena.handle.NIdx arena.handle.EIdx}
    (h : c_kind_dup k = ok k') : k' = k := by
  delta c_kind_dup at h
  cases k <;> dsimp only at h
  · exact (Result.ok_injective h).symm
  · peel h as e, he
    obtain rfl := eidx_dup2_ok he
    peel h as hr, hhr
    obtain rfl := hints_dup_self hhr
    peel h as v, hv
    cases Result.ok_injective h
    rw [ConRon.Refine.Expr.str_copy_eq hv]
  · peel h as e, he
    obtain rfl := eidx_dup2_ok he
    peel h as v, hv
    cases Result.ok_injective h
    rw [nidx_vec_dup_eq hv]
  · peel h as e, he
    obtain rfl := eidx_dup2_ok he
    cases Result.ok_injective h
    rfl
  · peel h as v, hv
    cases Result.ok_injective h
    rw [ConRon.Refine.Expr.str_copy_eq hv]
  · peel h as v, hv
    peel h as v1, hv1
    cases Result.ok_injective h
    rw [nidx_vec_dup_eq hv, nidx_vec_dup_eq hv1]
  · peel h as n, hn
    obtain rfl := nidx_dup2_ok hn
    cases Result.ok_injective h
    rfl
  · peel h as v, hv
    peel h as v1, hv1
    cases Result.ok_injective h
    rw [nidx_vec_dup_eq hv, rules_dup_eq hv1]

/-- **`c_entry_dup` is the identity.** -/
theorem c_entry_dup_eq {c c' : frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx}
    (h : c_entry_dup c = ok c') : c' = c := by
  rw [c_entry_dup] at h
  peel h as n, hn
  obtain rfl := nidx_dup2_ok hn
  peel h as v, hv
  peel h as e, he
  obtain rfl := eidx_dup2_ok he
  peel h as k, hk
  cases Result.ok_injective h
  rw [nidx_vec_dup_eq hv, c_kind_dup_eq hk]

/-- **`mod_decoded_dup` is the identity.** -/
theorem mod_decoded_dup_eq {d d' : frontend.olean.spec.ModDecoded}
    (h : mod_decoded_dup d = ok d') : d' = d := by
  rw [mod_decoded_dup] at h
  peel h as im, him
  peel h as cs, hcs
  cases Result.ok_injective h
  have e1 : im = d.imports := by
    refine vec_ext (dup_walk0 (L := fun i out => mod_decoded_dup_loop0 d.imports out i) ?_ him)
    intro i out o h
    rw [mod_decoded_dup_loop0] at h
    by_cases hc : i < alloc.vec.Vec.len d.imports
    · rw [ite_eq_left hc] at h
      peel h as x, hx
      peel h as n, hn
      obtain rfl := nidx_dup2_ok hn
      peel h as o1, ho1
      peel h as j, hj
      exact Or.inr ⟨x, o1, j, ConRon.Refine.ExprOps.vec_index_getElem? hx,
        ConRon.Refine.vec_push_val ho1, add_one_usize hj, h⟩
    · rw [ite_eq_right hc] at h
      exact Or.inl ⟨not_lt_len hc, (Result.ok_injective h).symm⟩
  have e2 : cs = d.constants := by
    refine vec_ext (dup_walk0 (L := fun i out => mod_decoded_dup_loop1 d.constants out i) ?_ hcs)
    intro i out o h
    rw [mod_decoded_dup_loop1] at h
    by_cases hc : i < alloc.vec.Vec.len d.constants
    · rw [ite_eq_left hc] at h
      peel h as x, hx
      peel h as c1, hc1
      obtain rfl := c_entry_dup_eq hc1
      peel h as o1, ho1
      peel h as j, hj
      exact Or.inr ⟨_, o1, j, ConRon.Refine.ExprOps.vec_index_getElem? hx,
        ConRon.Refine.vec_push_val ho1, add_one_usize hj, h⟩
    · rw [ite_eq_right hc] at h
      exact Or.inl ⟨not_lt_len hc, (Result.ok_injective h).symm⟩
  rw [e1, e2]

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

/-! ## The location tests -/

/-- `loc_is_some` is `(r.loc a).isSome`. -/
theorem loc_is_some_eq (bs : Slice Std.U8) {r : frontend.olean.region.Region} {a : Std.U64} {b : Bool}
    (h : loc_is_some r a = ok b) : b = ((absRegion bs r).loc (absWord a)).isSome := by
  rw [loc_is_some] at h
  peel h as o, ho
  rw [← region_loc_eq bs ho]
  cases o <;> exact (Result.ok_injective h).symm

/-- `loc_in_two`: the location test in the region of two files. -/
theorem loc_in_two_eq {a b : frontend.olean.region.Part} {addr : Std.U64} {o : Bool}
    (ha : PartFits a) (hb : PartFits b) (h : loc_in_two a b addr = ok o) :
    o = match ofParts #[absPart a, absPart b] with
      | .error _ => false
      | .ok r2 => (r2.loc (absWord addr)).isSome := by
  rw [loc_in_two] at h
  peel h as r, hr
  have e := region_of_parts2_eq ha hb hr
  cases r with
  | Err _ =>
    obtain ⟨-, m, em⟩ := e
    rw [em]
    exact (Result.ok_injective h).symm
  | Ok b2 =>
    obtain ⟨em, -⟩ := e
    rw [em]
    exact loc_is_some_eq _ h

end ConRon.Refine2.Frontend.Olean

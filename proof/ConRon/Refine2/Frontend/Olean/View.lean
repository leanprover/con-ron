/-
# `ConRon.Refine2.Frontend.Olean.View` — `olean/view.rs` against `Arena/Frontend/Olean/View.lean`

**Task #142, Theorem 2.**  A view is upstream's `ModFiles.viewRegion`: `ViewO` says of the Rust's
answer that its bytes and its region are upstream's, and that they fit, which the reads ask.
What `view.rs` copies, it copies: `region_dup`, `c_entry_dup`, `mod_decoded_dup` are the identity.
-/
import ConRon.Refine2.Frontend.Olean.ModFilesRel
import ConRon.Refine2.Frontend.Olean.Reads
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

/-! ## A decoded view -/

/-- A stored constant, as the twin's. -/
abbrev ERel := EntryRel (N := arena.handle.NIdx) (E := arena.handle.EIdx) absNIdx absEIdx ValRel

/-- **`view::AllViews` against the twin's.** -/
structure AllViewsRel (v : frontend.olean.view.AllViews) (v' : Arena.Frontend.Olean.AllViews) :
    Prop where
  exported : ModDecodedRel v.exported v'.exported
  server : ModDecodedRel v.server v'.server
  «private» : ModDecodedRel v.private_part v'.private

/-- `all_views_at` is `AllViews.at`. -/
theorem all_views_at_eq {v v' level d} (hv : AllViewsRel v v')
    (h : all_views_at v level = ok d) : ModDecodedRel d (v'.at (absLevel level)) := by
  cases level
  · cases Result.ok_injective h; exact hv.exported
  · cases Result.ok_injective h; exact hv.server
  · cases Result.ok_injective h; exact hv.private

/-- `mod_files_up_to` is `ModFiles.upTo`. -/
theorem mod_files_up_to_eq {f f' level r} (hf : ModFilesRel f f') (h : mod_files_up_to f level = ok r) :
    ModFilesRel r (f'.upTo (absLevel level)) := by
  cases level
  · cases Result.ok_injective h
    exact ⟨hf.exported, rfl, rfl, hf.fitsE, by simp, by simp⟩
  · cases Result.ok_injective h
    exact ⟨hf.exported, hf.server, rfl, hf.fitsE, hf.fitsS, by simp⟩
  · cases Result.ok_injective h
    exact hf

/-! ## `parse_view` -/

/-- The imports of a header, as the twin's array. -/
@[reducible] def absImports (v : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)) :
    Array (ConLeche.Frontend.Olean.ImportF NIdx) :=
  (v.val.map (absImportF absNIdx)).toArray

theorem dec_imports {d d'} (hd : ModDecodedRel d d') : d'.imports = absImports d.imports := by
  rw [absImports, hd.imports]

theorem am_pure_bind {α β : Type} (a : α) (g : α → AM β) : (pure a >>= g) = g a := rfl

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

theorem list3 {α : Type} {l : List α} {a b c : α} (h : l.length = 3) (h0 : l[0]? = some a)
    (h1 : l[1]? = some b) (h2 : l[2]? = some c) : l = [a, b, c] := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨_, _⟩⟩⟩⟩ <;> simp_all

theorem len_bne_three {α : Type} {ds : alloc.vec.Vec α} (h : ds.val.length = 3) :
    ¬ (alloc.vec.Vec.len ds != 3#usize) = true := by
  simp only [bne_iff_ne]
  intro hn
  exact hn (UScalar.eq_of_val_eq (by simpa using h))

theorem len_bne_ne {α : Type} {ds : alloc.vec.Vec α} (h : ¬ ds.val.length = 3) :
    (alloc.vec.Vec.len ds != 3#usize) = true := by
  simp only [bne_iff_ne]
  intro he
  apply h
  have := congrArg (fun x : Std.Usize => x.val) he
  simpa using this

/-- `take_decoded`: the value at `i`, and the others stay. -/
theorem take_dec {ds i d ds'} (h : frontend.olean.fast.take_decoded ds i = ok (d, ds')) :
    ds.val[i.val]? = some d ∧ ∀ j, j ≠ i.val → ds'.val[j]? = ds.val[j]? := by
  rw [frontend.olean.fast.take_decoded] at h
  peel h as ⟨md, back⟩, hm
  have hb := ConRon.Refine2.Frontend.idt_index_mut_back hm
  rw [alloc.vec.Vec.index_mut_slice_index, alloc.vec.Vec.index_mut_usize] at hm
  peel hm as y, hy
  simp only [Result.ok.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, -⟩ := hm
  cases Result.ok_injective h
  subst hb
  refine ⟨ConRon.Refine.ExprOps.vec_index_getElem? (by rw [alloc.vec.Vec.index_slice_index]; exact hy), ?_⟩
  intro j hj
  rw [alloc.vec.Vec.set_val_eq, List.getElem?_set_ne (Ne.symm hj)]

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

/-- **`parse_all_views_module` is `parseAllViewsModule`.** -/
theorem parse_all_views_module_refines {pk pers st lst f f' s p}
    (hf : ModFilesRel f f') (hs : f.server = some s) (hp : f.private_part = some p) :
    RS pers AllViewsRel st lst (parse_all_views_module pk pers st.store f s p)
      (parseAllViewsModule (absPins pk) f' (absPart s) (absPart p)) := by
  have fE := hf.fitsE
  have fS := hf.fitsS s hs
  have fP := hf.fitsP p hp
  rw [parse_all_views_module, parseAllViewsModule, hf.exported]
  refine RS.pure_step fun ae hae => RS.pure_step fun a_s has => RS.pure_step fun ap hap =>
    RS.pure_step fun r1 hr1 => RS.pure_step fun b hb => ?_
  obtain ⟨e1, -⟩ := region_single_eq fE hr1
  rw [loc_is_some_eq (alloc.vec.Vec.deref f.exported.bytes) hb, e1, part_module_data_addr_eq hae]
  rw [← part_module_data_addr_eq hae, ← part_module_data_addr_eq has, ← part_module_data_addr_eq hap]
  by_cases c1 : ((single (absPart f.exported)).loc (absWord ae)).isSome = true
  · rw [ite_eq_left c1, ite_eq_left c1]
    simp only [am_pure_bind]
    refine RS.pure_step fun b1 hb1 => ?_
    rw [loc_in_two_eq fE fS hb1]
    cases e2 : ofParts #[absPart f.exported, absPart s] with
    | error _ =>
      rw [ite_eq_right (by simp)]
      exact RS.none
    | ok r2 =>
      dsimp only
      by_cases c2 : (r2.loc (absWord a_s)).isSome = true
      · rw [ite_eq_left c2, ite_eq_left c2]
        refine RS.pure_step fun o3 ho3 => ?_
        have e3 := region_of_parts3_eq fE fS fP ho3
        cases o3 with
        | Err _ =>
          obtain ⟨-, _, em⟩ := e3
          rw [em]
          exact RS.none
        | Ok buf =>
          obtain ⟨em, hfit⟩ := e3
          rw [em]
          dsimp only
          intro hrel hinv o s' h
          peel h as a1, h1
          peel h as a2, h2
          peel h as a3, h3
          peel h as ⟨r2', ar1⟩, hmany
          have hS := parse_many_refines (addrs := a3) hfit hrel hinv r2' ar1 hmany
          have ha : a3.val.map absWord = [absWord ae, absWord a_s, absWord ap] := by
            rw [ConRon.Refine.vec_push_val h3, ConRon.Refine.vec_push_val h2, ConRon.Refine.vec_push_val h1]
            rfl
          rw [ha] at hS
          cases r2' with
          | Err ee =>
            cases Result.ok_injective h
            cases ee with
            | Bad =>
              obtain ⟨lst1, hx, hrel1, hinv1⟩ := hS
              rw [am_bind_ok hx]
              exact ⟨lst1, rfl, hrel1, hinv1⟩
            | Err e =>
              intro k' hk'
              obtain ⟨le, hle, hkk⟩ := hS k' hk'
              refine ⟨le, ?_, hkk⟩
              rw [StateT.run_bind, hle]
              rfl
          | Ok ds =>
            obtain ⟨l, lst1, hx, hl, hrel1, hinv1⟩ := hS
            rw [am_bind_ok hx]
            replace h : (if (alloc.vec.Vec.len ds != 3#usize) = true then _ else _) = ok (o, s') := h
            by_cases hlen : ds.val.length = 3
            · rw [ite_eq_right (len_bne_three hlen)] at h
              peel h as ⟨dp, ds1⟩, ht2
              peel h as ⟨d_s, ds2⟩, ht1
              peel h as ⟨de, _⟩, ht0
              obtain ⟨g2, k2⟩ := take_dec ht2
              obtain ⟨g1, k1⟩ := take_dec ht1
              obtain ⟨g0, -⟩ := take_dec ht0
              have g0' := g0
              rw [k1 _ (by decide), k2 _ (by decide)] at g0'
              have g1' := g1
              rw [k2 _ (by decide)] at g1'
              obtain ⟨y0, hy0, r0⟩ := f2_get hl g0'
              obtain ⟨y1, hy1, r1'⟩ := f2_get hl g1'
              obtain ⟨y2, hy2, r2'⟩ := f2_get hl g2
              have el := list3 (by rw [← hl.length_eq]; exact hlen) hy0 hy1 hy2
              subst el
              dsimp only
              peel h as ⟨r3, ar2⟩, himp
              have hS3 : RdOut pers (EqA absImports) (withStore st ar2) r3
                  ((importsPre (absPins pk) (absPart f.exported).bytes).run lst1) :=
                imports_pre_ok hf (withStore st ar1) lst1 hrel1 hinv1 r3 ar2 himp
              cases r3 with
              | Err ee =>
                cases Result.ok_injective h
                cases ee with
                | Bad =>
                  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := hS3
                  rw [am_bind_ok hx2]
                  exact ⟨lst2, rfl, hrel2, hinv2⟩
                | Err e =>
                  intro k' hk'
                  obtain ⟨le, hle, hkk⟩ := hS3 k' hk'
                  refine ⟨le, ?_, hkk⟩
                  rw [StateT.run_bind, hle]
                  rfl
              | Ok pre =>
                obtain ⟨_, lst2, hx2, rfl, hrel2, hinv2⟩ := hS3
                rw [am_bind_ok hx2]
                dsimp only
                replace h : (Std.bind (frontend.olean.spec.imports_beq _ de.imports) _) = ok (o, s') := h
                rw [dec_imports r0, dec_imports r1', dec_imports r2']
                peel h as b3, hb3
                rw [← imports_beq_eq hb3]
                cases b3 with
                | false =>
                  rw [ite_eq_right (by simp)] at h ⊢
                  cases Result.ok_injective h
                  exact ⟨lst2, rfl, hrel2, hinv2⟩
                | true =>
                  rw [ite_eq_left rfl] at h
                  peel h as b4, hb4
                  rw [← imports_beq_eq hb4]
                  cases b4 with
                  | false =>
                    rw [ite_eq_right (by simp)] at h ⊢
                    cases Result.ok_injective h
                    exact ⟨lst2, rfl, hrel2, hinv2⟩
                  | true =>
                    rw [ite_eq_left rfl] at h
                    peel h as b5, hb5
                    rw [← imports_beq_eq hb5]
                    cases b5 with
                    | false =>
                      rw [ite_eq_right (by simp)] at h ⊢
                      cases Result.ok_injective h
                      exact ⟨lst2, rfl, hrel2, hinv2⟩
                    | true =>
                      rw [ite_eq_left rfl] at h
                      rw [ite_eq_left (show (true && true && true) = true from rfl)]
                      cases Result.ok_injective h
                      exact ⟨_, lst2, rfl, ⟨r0, r1', r2'⟩, hrel2, hinv2⟩
            · rw [ite_eq_left (len_bne_ne hlen)] at h
              cases Result.ok_injective h
              have hne : l.length ≠ 3 := by rw [← hl.length_eq]; exact hlen
              have hn : ∀ a b c, l ≠ [a, b, c] := by
                rintro a b c rfl
                exact hne rfl
              refine ⟨lst1, ?_, hrel1, hinv1⟩
              revert hn hne
              rcases l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> intro hne hn <;>
                first | exact absurd rfl (hn _ _ _) | rfl
      · rw [ite_eq_right c2, ite_eq_right c2]
        exact RS.none
  · rw [ite_eq_right c1, ite_eq_right c1]
    exact RS.none

/-- **`parse_all_views` is `parseAllViews`.** -/
theorem parse_all_views_refines {pk pers st lst f f'}
    (hf : ModFilesRel f f') :
    RS pers AllViewsRel st lst (parse_all_views pk pers st.store f) (parseAllViews (absPins pk) f') := by
  rw [parse_all_views, parseAllViews]
  refine RS.pure_step fun b hb => ?_
  rw [← mod_files_is_module_eq hf hb]
  cases b with
  | true =>
    rw [ite_eq_left rfl, ite_eq_left rfl, hf.server, hf.private]
    cases hs : f.server with
    | none => exact RS.none
    | some s =>
      cases hp : f.private_part with
      | none => exact RS.none
      | some p => exact parse_all_views_module_refines hf hs hp
  | false =>
    rw [ite_eq_right (by simp), ite_eq_right (by simp)]
    refine RS.of_eq (RS.bind (g := fun d => pure (some ⟨d, d, d⟩))
      (parse_view_refines (level := .Exported) hf) ?_ ?_) ?_
    · intros; rfl
    · intro d d' s1 lst1 hd
      refine RS.pure_step fun d2 hd2 => ?_
      obtain rfl := mod_decoded_dup_eq hd2
      exact RS.some ⟨hd, hd, hd⟩
    · congr 1
      funext o
      cases o <;> rfl

/-! ## The reads of a view -/

/-- The walk of `read_name_positions`, `read_entry`, `read_stmts`: the view, then the read
`hk` of its bytes and region. -/
macro "view_read " hf:term ", " hk:term : tactic =>
  `(tactic| (
    refine RS.pure_step fun o ho => ?_
    have hV := mod_files_view_region_eq $hf ho
    cases o with
    | none =>
      rw [show _ = none from hV]
      exact RS.none
    | some p =>
      obtain ⟨vb, a⟩ := p
      dsimp only
      refine RS.pure_step fun bs hb => RS.pure_step fun r hr => ?_
      obtain ⟨e, hfit⟩ := hV bs r hb hr
      rw [e]
      exact $hk hfit))

/-- **`read_name_positions` is `readNamePositions`.** -/
theorem read_name_positions_refines {pk pers st lst f f' level} (hf : ModFilesRel f f') :
    RS pers (EqA absNamePositions) st lst
      (frontend.olean.view.read_name_positions pk pers st.store f level)
      (Arena.Frontend.Olean.readNamePositions (absPins pk) f' (absLevel level)) := by
  rw [frontend.olean.view.read_name_positions, Arena.Frontend.Olean.readNamePositions]
  view_read hf, name_positions_at_refines

/-- **`read_entry` is `readEntry`.** -/
theorem read_entry_refines {pk pers st lst f f' level} {c : Std.U64} (hf : ModFilesRel f f') :
    RS pers ERel st lst (frontend.olean.view.read_entry pk pers st.store f level c)
      (Arena.Frontend.Olean.readEntry (absPins pk) f' (absLevel level) c.val) := by
  rw [frontend.olean.view.read_entry, Arena.Frontend.Olean.readEntry]
  view_read hf, entry_at_refines

/-- **`read_stmts` is `readStmts`.** -/
theorem read_stmts_refines {pk pers st lst f f' level} {cs : alloc.vec.Vec Std.U64}
    (hf : ModFilesRel f f') :
    RS pers (fun v l => List.Forall₂ (EqA absStmt) v.val l) st lst
      (frontend.olean.view.read_stmts pk pers st.store f level cs)
      (Arena.Frontend.Olean.readStmts (absPins pk) f' (absLevel level) (cs.val.map (·.val))) := by
  rw [frontend.olean.view.read_stmts, Arena.Frontend.Olean.readStmts]
  view_read hf, (fun h => stmts_at_refines h rfl)

/-! ## `view_error` -/

/-- A message path of `view_error`: pure steps, ending in an `.internal`. -/
def IntLeaf (m : Result (kernel.core_types.CheckError × arena.store.EStore)) : Prop :=
  ∀ e s', m = ok (e, s') → absAErrKind e = some .internal

theorem IntLeaf.step {δ : Type} {f : Result δ}
    {k : δ → Result (kernel.core_types.CheckError × arena.store.EStore)}
    (h : ∀ a, IntLeaf (k a)) : IntLeaf (Std.bind f k) := by
  intro e s' hm
  obtain ⟨a, _, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact h a e s' h2

theorem IntLeaf.done {ar : arena.store.EStore} (v : alloc.vec.Vec Std.U32) :
    IntLeaf (Std.bind (kernel.core_types.internal v) fun e => ok (e, ar)) := by
  intro e s' h
  simp only [kernel.core_types.internal, bind_ok] at h
  cases Result.ok_injective h
  rfl

/-- `undecodable` is an `.internal`. -/
theorem undecodable_kind {pers ar m ce} (h : frontend.olean.view.undecodable pers ar m = ok ce) :
    absAErrKind ce = some .internal := by
  rw [frontend.olean.view.undecodable] at h
  peel h as _, _
  peel h as _, _
  peel h as _, _
  peel h as _, _
  peel h as _, _
  peel h as _, _
  peel h as _, _
  rw [kernel.core_types.internal] at h
  cases Result.ok_injective h
  rfl

theorem IntLeaf.undec {pers ar m} :
    IntLeaf (Std.bind (frontend.olean.view.undecodable pers ar m) fun e => ok (e, ar)) := by
  intro e s' h
  peel h as ce, hce
  cases Result.ok_injective h
  exact undecodable_kind hce

/-- A message path of `view_error`. -/
macro "int_leaf" : tactic =>
  `(tactic| repeat' first | exact IntLeaf.done _ | exact IntLeaf.undec | refine IntLeaf.step fun _ => ?_)

/-- **`view_error` is `viewError`**, thrown: an error at the kind of the twin's.  The name is in
its message only, so the twin's `m'` is any. -/
theorem view_error_refines {γ : Type} {pk pers st lst f f' level} {m : arena.handle.NIdx} {m' : ConLeche.Name}
    (hf : ModFilesRel f f') (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) {ce ar'}
    (h : frontend.olean.view.view_error pk pers st.store m f level = ok (ce, ar')) :
    AErrSim ce ((Arena.Frontend.Olean.viewError (absPins pk) m' f' (absLevel level) >>=
      Arena.fail (α := γ)).run lst) := by
  rw [frontend.olean.view.view_error] at h
  peel h as _, _
  peel h as _, _
  peel h as _, _
  peel h as _, _
  unfold Arena.Frontend.Olean.viewError
  peel h as o, ho
  have hV := mod_files_view_region_eq hf ho
  cases o with
  | none =>
    rw [show f'.viewRegion (absLevel level) = none from hV]
    exact ConRon.Refine2.AErrSim.of_kind rfl ((show IntLeaf _ by int_leaf) _ _ h) rfl
  | some p =>
    obtain ⟨vb, a⟩ := p
    dsimp only at h
    peel h as bs, hb
    peel h as r, hr
    obtain ⟨e, hfit⟩ := hV bs r hb hr
    rw [e]
    dsimp only
    peel h as ⟨r1, ar1⟩, hc
    have hC := const_names_ok_refines hfit hrel hinv r1 ar1 hc
    cases r1 with
    | Err e1 =>
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Result.ok_injective h)
      rw [StateT.run_bind, StateT.run_bind]
      exact AErrSim.bind (AErrSim.bind hC _) _
    | Ok b =>
      obtain ⟨b', lst1, hx, rfl, hrel1, hinv1⟩ := hC
      rw [StateT.run_bind, am_bind_ok hx]
      cases b with
      | false =>
        rw [ite_eq_right (by simp)]
        replace h : (if false = true then _ else _) = ok (ce, ar') := h
        rw [ite_eq_right (by simp)] at h
        exact ConRon.Refine2.AErrSim.of_kind rfl ((show IntLeaf _ by int_leaf) _ _ h) rfl
      | true =>
        rw [ite_eq_left rfl]
        replace h : (if true = true then _ else _) = ok (ce, ar') := h
        rw [ite_eq_left rfl] at h
        peel h as ⟨r2, ar2⟩, hpa
        have hS := parse_at_refines hfit hrel1 hinv1 r2 ar2 hpa
        cases r2 with
        | Ok d =>
          obtain ⟨d', lst2, hx2, -, -, -⟩ := hS
          rw [am_bind_ok hx2]
          exact ConRon.Refine2.AErrSim.of_kind rfl ((show IntLeaf _ by int_leaf) _ _ h) rfl
        | Err ee =>
          cases ee with
          | Bad =>
            obtain ⟨lst2, hx2, -, -⟩ := hS
            rw [am_bind_ok hx2]
            exact ConRon.Refine2.AErrSim.of_kind rfl ((show IntLeaf _ by int_leaf) _ _ h) rfl
          | Err e2 =>
            obtain ⟨rfl, -⟩ := Prod.mk.inj (Result.ok_injective h)
            rw [StateT.run_bind]
            exact AErrSim.bind (AErrSim.bind hS _) _

end ConRon.Refine2.Frontend.Olean

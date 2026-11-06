/-
# `ConRon.Refine2.Frontend.Olean.ReadValue` — a theorem's value, read in its check

**Task #143, Theorem 2** (upstream task #481).  An `--olean` read leaves a theorem's value in
its file; the theorem's job reads it (`records::read_value`) into the worker's store, over the
module's frontier (`sparse::frontier_expr`), from the module region the worker keeps between
jobs (`ValueCache`, `region_for`).  Against the twin's `readValue`, `regionFor`.

A read reaches a file, so the judgement is the accept's alone (`FsRel` relates `Ok` answers):
the Rust's `Ok` is the twin's `.ok`, the caches related (`VCRel`) and the states as every
reader relates them.
-/
import ConRon.Refine2.Frontend.Olean.Sparse
import ConRon.Refine2.Frontend.Olean.FilesRead
import ConRon.Refine2.Frontend.Olean.Contract

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.records (region_for read_value owned_view value_cache_empty)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Arena.Frontend.Olean (regionFor readValue)
open ConLeche.Frontend.Olean (refModule refLoc refBase)

/-- `REF_BASE` is `refBase`. -/
theorem ref_base_val {x : Std.U64} (h : frontend.olean.lazy.REF_BASE = ok x) : x.val = refBase := by
  rw [frontend.olean.lazy.REF_BASE] at h
  have := (ConRon.Refine.Nat.ushiftLeftI_val h).2
  rw [this]; decide

/-- `ref_module` is `refModule`. -/
theorem ref_module_eq {code i : Std.U64} (h : frontend.olean.lazy.ref_module code = ok i) :
    i.val = refModule code.val := by
  rw [frontend.olean.lazy.ref_module] at h
  peel h as b, hb
  rw [ConRon.Refine.Nat.urem_val h, ref_base_val hb, refModule]

/-- `ref_loc` is `refLoc`. -/
theorem ref_loc_eq {code i : Std.U64} (h : frontend.olean.lazy.ref_loc code = ok i) :
    i.val = refLoc code.val := by
  rw [frontend.olean.lazy.ref_loc] at h
  peel h as b, hb
  rw [ConRon.Refine.Nat.udiv_val h, ref_base_val hb, refLoc]

/-- **A worker's cache against the twin's**: the module's position, and its region with the
bytes, as the twin's region (`absRegion`), within the bytes. -/
structure VCRel (c : frontend.olean.records.ValueCache) (c' : Arena.Frontend.Olean.ValueCache) :
    Prop where
  idx : c.idx.val = c'.idx
  region : Option.Rel (fun (rb : frontend.olean.region.RegionBuf) r' =>
      absRegion (alloc.vec.Vec.deref rb.bytes) rb.region = r' ∧
        RegionFits (alloc.vec.Vec.deref rb.bytes) rb.region) c.region c'.region

/-- `value_cache_empty` is the twin's `{}`. -/
theorem value_cache_empty_rel {c} (h : value_cache_empty = ok c) : VCRel c {} := by
  rw [value_cache_empty] at h
  cases Result.ok_injective h
  exact ⟨rfl, .none⟩

/-- `region_dup`'s loop always answers: it pushes onto a vector no longer than its source. -/
theorem region_dup_loop_ok (v : alloc.vec.Vec frontend.olean.region.Seg) :
    ∀ (k : Nat) (segs : alloc.vec.Vec frontend.olean.region.Seg) (i : Std.Usize),
      v.val.length - i.val = k → segs.val.length = i.val →
      ∃ out, frontend.olean.view.region_dup_loop v segs i = ok out := by
  intro k
  induction k with
  | zero =>
    intro segs i hk hs
    refine ⟨segs, ?_⟩
    rw [frontend.olean.view.region_dup_loop, ite_eq_right (by scalar_tac)]
  | succ k ih =>
    intro segs i hk hs
    rw [frontend.olean.view.region_dup_loop, ite_eq_left (by scalar_tac)]
    have hlt : i.val < v.val.length := by omega
    obtain ⟨x, hx, -⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec v i hlt)
    have hmax : segs.val.length < Std.Usize.max := by have := v.property; omega
    obtain ⟨w, hw, hwv⟩ := WP.spec_imp_exists (alloc.vec.Vec.push_spec segs
      { x with off := x.off, size := x.size } hmax)
    have hmax2 : i.val + 1 ≤ Std.Usize.max := by have := v.property; omega
    obtain ⟨j, hj, hjv⟩ := ConRon.Refine.usize_add_ok hmax2
    obtain ⟨out, ho⟩ := ih w j (by omega) (by rw [hwv]; simp [hs, hjv])
    refine ⟨out, ?_⟩
    simp only [alloc.vec.Vec.index_slice_index, bind_ok, hx, hw, hj, ho]

/-- **`region_dup` answers its argument.** -/
theorem region_dup_ok (r : frontend.olean.region.Region) :
    frontend.olean.view.region_dup r = ok r := by
  have ⟨out, ho⟩ := region_dup_loop_ok r.segs _ (alloc.vec.Vec.with_capacity _ (alloc.vec.Vec.len r.segs))
    0#usize rfl (by simp [alloc.vec.Vec.with_capacity])
  have h : frontend.olean.view.region_dup r = ok { segs := out } := by
    rw [frontend.olean.view.region_dup]
    simp only [bind_ok, ho]
  rw [h, region_dup_eq h]

/-- **`owned_view`: the bytes and the region the view reads**, so a view's answer is the
region of the owned buffer. -/
theorem owned_view_rel {f : frontend.olean.view.ModFiles} {vb : frontend.olean.view.ViewBytes}
    {a : Std.U64} {y} (hv : ViewOk f vb a y) {rb} (h : owned_view f vb = ok rb) :
    y = some (absRegion (alloc.vec.Vec.deref rb.bytes) rb.region, absWord a) ∧
      RegionFits (alloc.vec.Vec.deref rb.bytes) rb.region := by
  cases vb with
  | Exported =>
    simp only [owned_view] at h
    peel h as r, hr
    cases Result.ok_injective h
    exact hv _ _ rfl (by rw [frontend.olean.view.view_region_of]; exact hr)
  | Joined b =>
    simp only [owned_view] at h
    cases Result.ok_injective h
    exact hv _ _ rfl (by rw [frontend.olean.view.view_region_of]; exact region_dup_ok _)

section reads

variable {F : Type} {inst : frontend.olean.files.OleanFs F} {fsv : F}
  {fs : Arena.Frontend.Olean.OleanFs}

/-- **`region_for`'s accept is `regionFor`'s**: the store unchanged, the twin's run reading
nothing, and the region of module `idx` in the caches both hand on. -/
theorem region_for_ok {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {sp : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    {m : arena.handle.NIdx} {idx : Std.U64} {c c1 : frontend.olean.records.ValueCache}
    {c' : Arena.Frontend.Olean.ValueCache} {s'} (hfs : FsRel inst fsv fs) (hc : VCRel c c')
    (hrel : AStateRel₀ pers st lst)
    (h : region_for inst fsv pk pers st.store sp m idx c = ok (.Ok (), s', c1)) :
    s' = st.store ∧ ∃ c1' r', (regionFor fs (absPins pk) (absSearchPath sp) (absNIdx m) idx.val c').run lst
        = .ok ((c1', .ok r'), lst) ∧ VCRel c1 c1' ∧ c1'.region = some r' := by
  -- the read of the files, both sides
  have hread : ∀ {s' c1}, (do
        let r ← frontend.olean.files.read_files inst fsv pers st.store sp m
          frontend.olean.view.OLeanLevel.Private
        match r with
        | core.result.Result.Ok f =>
          let o1 ← frontend.olean.view.mod_files_view_region f frontend.olean.view.OLeanLevel.Private
          match o1 with
          | none =>
            let (e, ar1) ← frontend.olean.view.view_error pk pers st.store m f
              frontend.olean.view.OLeanLevel.Private
            let c1 ← value_cache_empty
            ok (core.result.Result.Err e, ar1, c1)
          | some p =>
            let (vb, _) := p
            let rb ← owned_view f vb
            ok (core.result.Result.Ok (), st.store, { idx, region := (some rb) })
        | core.result.Result.Err e =>
          let c1 ← value_cache_empty
          ok (core.result.Result.Err e, st.store, c1)) = ok (.Ok (), s', c1) →
      s' = st.store ∧ ∃ c1' r',
        (regionFor.readRegion fs (absPins pk) (absSearchPath sp) (absNIdx m) idx.val).run lst
          = .ok ((c1', .ok r'), lst) ∧ VCRel c1 c1' ∧ c1'.region = some r' := by
    intro s' c1 h
    peel h as r, hr
    cases r with
    | Err e =>
      dsimp only at h
      peel h as c2, -
      cases (Prod.mk.inj (Result.ok_injective h)).1
    | Ok f =>
      dsimp only at h
      obtain ⟨n, hn⟩ := read_files_name hr
      obtain ⟨f', e1, hf⟩ := read_files_refines hfs hn hr
      peel h as o1, ho1
      have hV := mod_files_view_region_eq hf ho1
      cases o1 with
      | none =>
        dsimp only at h
        peel h as q, -
        obtain ⟨e, ar1⟩ := q
        peel h as c2, -
        cases (Prod.mk.inj (Result.ok_injective h)).1
      | some p =>
        obtain ⟨vb, a⟩ := p
        dsimp only at h
        peel h as rb, hrb
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Result.ok_injective h)
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
        obtain ⟨hy, hfit⟩ := owned_view_rel hV hrb
        refine ⟨rfl, ⟨idx.val, some (absRegion (alloc.vec.Vec.deref rb.bytes) rb.region)⟩,
          absRegion (alloc.vec.Vec.deref rb.bytes) rb.region, ?_, ⟨rfl, .some ⟨rfl, hfit⟩⟩, rfl⟩
        have e1' : Arena.Frontend.Olean.readFiles fs (absSearchPath sp) (ConRon.Refine.absName n)
            .private = .ok f' := e1
        have hy' : f'.viewRegion .private =
            some (absRegion (alloc.vec.Vec.deref rb.bytes) rb.region, absWord a) := hy
        show ((Arena.readName (absNIdx m)) >>= _).run lst = _
        rw [am_bind_ok (read_name_run hrel hn)]
        simp only [e1', hy']
        rfl
  rw [region_for] at h
  cases hcr : c.region with
  | none =>
    rw [hcr] at h
    simp only [bind_ok] at h
    obtain ⟨hs, c1', r', hx, hc1, hr1⟩ := hread h
    refine ⟨hs, c1', r', ?_, hc1, hr1⟩
    have hc' : c'.region = none := by
      have := hc.region; rw [hcr] at this
      cases hh : c'.region with
      | none => rfl
      | some _ => rw [hh] at this; cases this
    rw [Arena.Frontend.Olean.regionFor, hc']
    exact hx
  | some rb =>
    rw [hcr] at h
    simp only [bind_ok] at h
    obtain ⟨r', hr', hrel'⟩ : ∃ r', c'.region = some r' ∧
        (absRegion (alloc.vec.Vec.deref rb.bytes) rb.region = r' ∧
          RegionFits (alloc.vec.Vec.deref rb.bytes) rb.region) := by
      have := hc.region; rw [hcr] at this
      cases hh : c'.region with
      | none => rw [hh] at this; cases this
      | some r' => rw [hh] at this; cases this with | some h => exact ⟨r', rfl, h⟩
    by_cases hidx : c.idx = idx
    · simp only [hidx, decide_true] at h
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Result.ok_injective h)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      refine ⟨rfl, c', r', ?_, ?_, hr'⟩
      · rw [Arena.Frontend.Olean.regionFor, hr']
        have : (c'.idx == idx.val) = true := by rw [← hc.idx, hidx]; simp
        simp only [this, ↓reduceIte]
        rfl
      · refine ⟨by rw [← hidx]; exact hc.idx, ?_⟩
        rw [hr']
        exact .some hrel'
    · simp only [hidx, decide_false] at h
      obtain ⟨hs, c1', r1, hx, hc1, hr1⟩ := hread h
      refine ⟨hs, c1', r1, ?_, hc1, hr1⟩
      rw [Arena.Frontend.Olean.regionFor, hr']
      have : (c'.idx == idx.val) = false := by
        rw [← hc.idx]; simp only [beq_eq_false_iff_ne]
        exact fun he => hidx (UScalar.eq_of_val_eq he)
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact hx

/-- **`read_value`'s accept is `readValue`'s**: a theorem's value from its reference's code,
the files of its module (through the worker's cache), then the value over the module's
frontier, interned into the worker's store.  `values` are the read's `ModRef`s (`OleanReadRel`). -/
theorem read_value_refines {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {sp : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    {values : alloc.vec.Vec frontend.olean.records.ModRef}
    {values' : Array Arena.Frontend.Olean.ModRef} {c c1 : frontend.olean.records.ValueCache}
    {c' : Arena.Frontend.Olean.ValueCache} {code : Std.U64} {e : arena.handle.EIdx} {s'}
    (hfs : FsRel inst fsv fs) (hv : List.Forall₂ ModRefRel values.val values'.toList)
    (hc : VCRel c c') (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (h : read_value inst fsv pk pers st.store sp values c code = ok (.Ok e, s', c1)) :
    ∃ c1' lst', (readValue fs (absPins pk) (absSearchPath sp) values' c' code.val).run lst
        = .ok ((c1', .ok (absEIdx e)), lst') ∧ VCRel c1 c1' ∧
      AStateRel₀ pers (withStore st s') lst' ∧ AStateInv pers (withStore st s') := by
  rw [read_value] at h
  peel h as i, hi
  have hiv := ref_module_eq hi
  peel h as i2, hi2
  have hi2v : i2.val = values.val.length := by
    simp only [lift, Result.ok.injEq] at hi2
    subst hi2
    rw [usize_cast_u64_val', vec_len_val]
  by_cases hlt : i < i2
  · rw [ite_eq_left hlt] at h
    have hlt' : i.val < values.val.length := by rw [← hi2v]; exact hlt
    peel h as i3, hi3
    have hi3v : i3.val = i.val := by
      simp only [lift] at hi3
      have := Result.ok_injective hi3
      rw [← this]
      exact ConRon.Refine.ExprOps.u64_cast_usize_val (by have := values.property; omega)
    peel h as md, hmd
    have hmd0 := ConRon.Refine.ExprOps.vec_index_getElem? hmd
    obtain ⟨md', hmd', hmr⟩ := forall₂_getElem? hv hmd0
    obtain ⟨⟨r, ar1, c2⟩, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r with
    | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
    | Ok u =>
      dsimp only at h
      obtain ⟨rfl, c2', r', hx, hc2, hr2⟩ := region_for_ok hfs hc hrel hq
      obtain ⟨rb, hrb, hrbr⟩ : ∃ rb, c2.region = some rb ∧
          (absRegion (alloc.vec.Vec.deref rb.bytes) rb.region = r' ∧
            RegionFits (alloc.vec.Vec.deref rb.bytes) rb.region) := by
        have := hc2.region; rw [hr2] at this
        cases hh : c2.region with
        | none => rw [hh] at this; cases this
        | some rb => rw [hh] at this; cases this with | some h => exact ⟨rb, rfl, h⟩
      obtain ⟨cidx, creg⟩ := c2
      simp only at hrb
      subst hrb
      peel h as i4, hi4
      have hi4v := ref_loc_eq hi4
      peel h as q2, hq2
      obtain ⟨r1, ar2⟩ := q2
      have hF := frontier_expr_refines (pk := pk) (pers := pers) (st := st) (lst := lst) (c := i4)
        hrbr.2 hmr.frontier hrel hinv r1 ar2 hq2
      cases r1 with
      | Err re =>
        cases re with
        | Bad =>
          peel h as ce, -
          cases (Prod.mk.inj (Result.ok_injective h)).1
        | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
      | Ok e' =>
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Result.ok_injective h)
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
        cases h1
        obtain ⟨b, lst2, hx2, hR, hrel2, hinv2⟩ := hF
        cases hR
        refine ⟨c2', lst2, ?_, hc2, hrel2, hinv2⟩
        rw [Arena.Frontend.Olean.readValue]
        have hmd'' : values'[refModule code.val]? = some md' := by
          rw [← hiv, ← Array.getElem?_toList, ← hi3v]; exact hmd'
        simp only [hmd'']
        rw [← hiv, ← hmr.name]
        show ((regionFor _ _ _ _ _ c') >>= _).run lst = _
        rw [am_bind_ok hx]
        rw [hrbr.1, hi4v] at hx2
        show ((Arena.Frontend.Olean.frontierExpr _ r' _ _) >>= _).run lst = _
        rw [am_bind_ok hx2]
        rfl
  · rw [ite_eq_right hlt] at h
    peel h as s1, -
    peel h as v1, -
    peel h as v2, -
    peel h as t, -
    peel h as v3, -
    peel h as v4, -
    peel h as ce, -
    peel h as v5, -
    peel h as v6, -
    peel h as ce2, -
    cases (Prod.mk.inj (Result.ok_injective h)).1

end reads

end ConRon.Refine2.Frontend.Olean

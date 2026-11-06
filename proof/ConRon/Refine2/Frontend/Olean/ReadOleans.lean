/-
# `ConRon.Refine2.Frontend.Olean.ReadOleans` — Theorem 2 at the reader

**Tasks #142, #143, Theorem 2.**  `read_oleans_refines` proves `Contract.lean`'s
`ReadOleansRefines`: `records::read_oleans`'s accept is the twin's `readOleans`.  Composition only,
of the steps `read_oleans` takes: the pins (`olean_pins_refines`), the closure's lazy load
(`load_closure_refines`), the merge, the blocks' check, the roots, the emission, the records
(`decls_of_rel`) and the modules' references (`mod_refs_rel`), the store unchanged past the load.
-/
import ConRon.Refine2.Frontend.Olean.Contract
import ConRon.Refine2.Frontend.Olean.ClosureRead
import ConRon.Refine2.Frontend.Olean.Records

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena

/-- **Theorem 2 at the reader**: the Rust's accepting read of the closure is the twin's, on a
record of the file system answering as the Rust's instance. -/
theorem read_oleans_refines : ReadOleansRefines := by
  intro F inst fsv fs pers rst lst dirs roots rd ar' hfs hrel hinv h
  rw [frontend.olean.records.read_oleans] at h
  peel h as q, hq
  obtain ⟨r0, ar1⟩ := q
  have h0 := olean_pins_refines hrel hinv _ _ hq
  cases r0 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok p =>
  obtain ⟨pk', lst1, hx1, rfl, hrel1, hinv1⟩ := h0
  peel h as q1, hq1
  obtain ⟨r1, ar2⟩ := q1
  cases r1 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok l =>
  obtain ⟨ls', lst2, hx2, hls, hrel2, hinv2⟩ :=
    load_closure_refines (st := withStore rst ar1) (lst := lst1) (pk := p) (pers := pers)
      (sp_dirs := dirs) (roots := roots) hfs hrel1 hinv1 _ _ hq1
  -- the notes, then the merge
  peel h as s0, -
  peel h as v0, -
  peel h as i1, -
  peel h as v1, -
  peel h as s1, -
  peel h as v2, -
  peel h as v3, -
  peel h as u0, -
  peel h as r2, hr2
  have hM := merge_all_rel (st := withStore (withStore rst ar1) ar2) (lst := lst2) p hls hrel2 hinv2 r2 hr2
  cases r2 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok m =>
  obtain ⟨mg', lst3, hx3, hm, hrel3, hinv3⟩ := hM
  peel h as s2, -
  peel h as v4, -
  peel h as i3, -
  peel h as v5, -
  peel h as s3, -
  peel h as v6, -
  peel h as v7, -
  peel h as u1, -
  -- the blocks' check and the roots
  peel h as r3, hr3
  have hB := blocks_ok_pr hm (pk := p) (pers := pers) (ar := ar2) r3 hr3 lst3
  cases r3 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok u =>
  obtain ⟨b, hxb, -⟩ := hB
  peel h as r4, hr4
  have hR := root_constants_pr hm (Option.Rel.none) (pers := pers) (ar := ar2) r4 hr4 lst3
  cases r4 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok cs =>
  obtain ⟨cs', hxcs, hcs⟩ := hR
  peel h as s4, -
  peel h as v8, -
  peel h as i5, -
  peel h as v9, -
  peel h as s5, -
  peel h as v10, -
  peel h as v11, -
  peel h as u2, -
  -- the emission and the records
  peel h as r5, hr5
  have hE := emit_all_rel hm hcs (pk := p) r5 hr5 lst3
  cases r5 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok em =>
  obtain ⟨lem, hxe, he⟩ := hE
  peel h as r6, hr6
  have hD := decls_of_rel (rst := withStore (withStore rst ar1) ar2) hrel3 hinv3 he hr6
  cases r6 with
  | Err e => cases (Prod.mk.inj (Result.ok_injective h)).1
  | Ok ds =>
  obtain ⟨dv, lst4, hxd, hdv, hrel4, hinv4⟩ := hD
  peel h as q2, hq2
  obtain ⟨values, mg2⟩ := q2
  obtain ⟨h1, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
  cases h1
  obtain ⟨hvals, hmg2⟩ := mod_refs_rel hm hq2
  refine ⟨⟨dv.decls, (Arena.Frontend.Olean.modRefs mg').2, (Arena.Frontend.Olean.modRefs mg').1,
    absPins p⟩, lst4, ?_, ⟨?_, hvals, hmg2, rfl⟩, hrel4, hinv4⟩
  · show (Arena.Frontend.Olean.oleanPins >>= _).run lst = _
    rw [am_bind_ok hx1]
    show ((Arena.Frontend.Olean.loadClosure fs (absPins p) (absSearchPath dirs) (absNIdxArr roots))
      >>= _).run lst1 = _
    rw [am_bind_ok hx2]
    show ((Arena.Frontend.Olean.mergeAll (absPins p) ls') >>= _).run lst2 = _
    rw [am_bind_ok hx3]
    show ((Arena.Frontend.Olean.blocksOk (absPins p) mg') >>= _).run lst3 = _
    rw [am_bind_ok hxb]
    show ((Arena.Frontend.Olean.rootConstants mg' none) >>= _).run lst3 = _
    rw [am_bind_ok hxcs]
    show ((Arena.Frontend.Olean.emitAll (absPins p) mg' cs') >>= _).run lst3 = _
    rw [am_bind_ok hxe]
    show ((Arena.Frontend.Olean.declsOf lem) >>= _).run lst3 = _
    rw [am_bind_ok hxd]
    rfl
  · rw [hdv.decls, absIDeclArr]

end ConRon.Refine2.Frontend.Olean

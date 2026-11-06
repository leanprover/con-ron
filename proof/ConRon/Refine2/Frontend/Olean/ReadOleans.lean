/-
# `ConRon.Refine2.Frontend.Olean.ReadOleans` — Theorem 2 at the reader

**Task #142, Theorem 2.**  `read_oleans_refines` proves `Contract.lean`'s `ReadOleansRefines`:
`records::read_oleans`'s accept is the twin's `readOleans`.  Composition only, of the three
steps `read_oleans` takes: the pins (`olean_pins_refines`), the closure's load
(`load_closure_refines`) and the rest on one snapshot of the store (`read_tail_rel`).
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
  intro F inst fsv fs pers rst lst dirs roots r ar' hfs hrel hinv h
  rw [frontend.olean.records.read_oleans] at h
  peel h as q, hq
  obtain ⟨r0, ar1⟩ := q
  have h0 := olean_pins_refines hrel hinv _ _ hq
  cases r0 with
  | Err e =>
    obtain ⟨h1, -⟩ := Prod.mk.inj (Result.ok_injective h)
    cases h1
  | Ok p =>
    obtain ⟨pk', lst1, hx1, rfl, hrel1, hinv1⟩ := h0
    peel h as q1, hq1
    obtain ⟨r1, ar2⟩ := q1
    cases r1 with
    | Err e =>
      obtain ⟨h1, -⟩ := Prod.mk.inj (Result.ok_injective h)
      cases h1
    | Ok l =>
      obtain ⟨ls', lst2, hx2, hls, hrel2, hinv2⟩ :=
        load_closure_refines (st := withStore rst ar1) (lst := lst1) (pk := p) (pers := pers)
          (sp_dirs := dirs) (roots := roots) hfs hrel1 hinv1 _ _ hq1
      obtain ⟨rfl, hs⟩ := read_tail_rel (rst := withStore (withStore rst ar1) ar2) (lst := lst2)
        (pk := p) hrel2 hinv2 hls Option.Rel.none h
      obtain ⟨rv, lst', hx, hR, hrel', hinv'⟩ := hs
      refine ⟨rv, lst', ?_, hR, hrel', hinv'⟩
      show (Arena.Frontend.Olean.oleanPins >>= _).run lst = _
      rw [am_bind_ok hx1]
      show ((Arena.Frontend.Olean.loadClosure fs (absPins p) (absSearchPath dirs) (absNIdxArr roots))
        >>= _).run lst1 = _
      rw [am_bind_ok hx2]
      exact hx

end ConRon.Refine2.Frontend.Olean

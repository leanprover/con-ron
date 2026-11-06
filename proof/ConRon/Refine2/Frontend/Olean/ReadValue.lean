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
  sorry -- T143-STUB

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
  sorry -- T143-STUB

end reads

end ConRon.Refine2.Frontend.Olean

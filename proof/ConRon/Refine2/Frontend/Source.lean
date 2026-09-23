/-
# `ConRon.Refine2.Frontend.Source` — the reader loop IS `parse_chunks`

**Task #97-P5-Driver** (task #97-COMPOSE's mismatch 11(b), priced by task
#97-P5-Front §4).  The binary parses with `export_c::parse_source`, the
reader loop, over `driver::HandleSource` — the file handle as the core's
`ChunkSource` trait, `Modeller`'s arrangement: the trait declared in the
verified crate, the one implementation in the driver.  The capstone is stated
about `export_c::parse_chunks` over a list of chunks.  This module equates
the two, at the level of the Aeneas model, under ONE hypothesis about the
source:

    ReadsAs inst src cs   —   the source's successive reads are the chunks
                              `cs`, each nonempty, and then an empty one

which is the one thing about the input the binary trusts (the reads are the
file's bytes, in order: OVERVIEW §8.2's I/O row).  The proof is the two loops
side by side: `parse_source_loop` (from the `loop`) and `parse_chunks_loop`
(from the `while`) make the same `chunk_step` calls on the same buffers and
the same `chunk_finish` at the end, so they return the same result and the
same state.  Nothing about the parse itself is used — this is a statement
about the Rust, not a refinement.
-/
import ConRon.Generated
import ConRon.Refine.Abs

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine2.Frontend

/-- con-leche: none — the input seam's hypothesis.  **The source hands out
the chunks `cs`, each nonempty, and then an empty buffer**: the reads of the
file, in order.  A statement about the unverified `ChunkSource` instance, as
`ModellerRefines` is one about the unverified `Modeller` instance. -/
def ReadsAs {S : Type} (inst : frontend.export_c.ChunkSource S) :
    S → List (alloc.vec.Vec Std.U8) → Prop
  | src, [] => ∃ e src', inst.next_chunk src = ok (e, src') ∧ e.val = []
  | src, c :: cs => c.val ≠ [] ∧
      ∃ src', inst.next_chunk src = ok (c, src') ∧ ReadsAs inst src' cs

private theorem vec_index_ok' {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    (hi : i.val < v.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i
      = ok v.val[i.val] := by
  simp only [alloc.vec.Vec.index_slice_index]
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec v i hi)
  rw [hy, hyv]

/-- **The two loops agree**: from the same parser state, the reader loop over
a source that reads as the chunks left in the list (from cursor `i`) returns
what the list loop returns, with the same arena state. -/
theorem parse_source_loop_eq {G S : Type} {mi : frontend.types.Modeller G}
    {inst : frontend.export_c.ChunkSource S} {pers : arena.store.PersTier} {m : G}
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)} :
    ∀ (cs : List (alloc.vec.Vec Std.U8)) {ar src st carry line_no total}
      {i : Std.Usize} {o},
      chunks.val.drop i.val = cs → ReadsAs inst src cs →
      frontend.export_c.parse_source_loop mi inst pers m ar src st carry line_no
        total = ok o →
      frontend.export_c.parse_chunks_loop mi pers m ar chunks st carry line_no total
        (alloc.vec.Vec.len chunks) i = ok (o.1, o.2.1) := by
  intro cs
  induction cs with
  | nil =>
    intro ar src st carry line_no total i o hdrop hreads hrun
    obtain ⟨e, src', hnext, he⟩ := hreads
    have hge : ¬ i < alloc.vec.Vec.len chunks := by
      have := List.drop_eq_nil_iff.mp hdrop
      have hl := alloc.vec.Vec.len_val chunks
      scalar_tac
    rw [frontend.export_c.parse_source_loop] at hrun
    rw [frontend.export_c.parse_chunks_loop, if_neg hge]
    have hlen : alloc.vec.Vec.len e = 0#usize := by
      have := alloc.vec.Vec.len_val e
      have h2 : e.val.length = 0 := by rw [he]; rfl
      scalar_tac
    obtain ⟨⟨buf, src1⟩, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [hnext] at hp
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hp)
    change (if alloc.vec.Vec.len e = 0#usize then _ else _) = ok o at hrun
    rw [if_pos hlen] at hrun
    obtain ⟨s, hs, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [hs]
    simp only [bind_tc_ok]
    obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [hq]
    obtain ⟨r, ar1⟩ := q
    have ho := (Result.ok_injective hrun).symm
    subst ho
    rfl
  | cons c cs ih =>
    intro ar src st carry line_no total i o hdrop hreads hrun
    obtain ⟨hne, src', hnext, hrest⟩ := hreads
    have hlt : i.val < chunks.val.length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hdrop
      exact absurd hdrop (by simp)
    have hci : chunks.val[i.val] = c := by
      rw [List.drop_eq_getElem_cons hlt] at hdrop
      exact (List.cons.inj hdrop).1
    have hdrop' : chunks.val.drop (i.val + 1) = cs := by
      rw [List.drop_eq_getElem_cons hlt] at hdrop
      exact (List.cons.inj hdrop).2
    have hlt' : i < alloc.vec.Vec.len chunks := by
      have := alloc.vec.Vec.len_val chunks
      scalar_tac
    rw [frontend.export_c.parse_source_loop] at hrun
    rw [frontend.export_c.parse_chunks_loop, if_pos hlt']
    have hlen : ¬ alloc.vec.Vec.len c = 0#usize := by
      intro h0
      have := alloc.vec.Vec.len_val c
      apply hne
      have h1 : c.val.length = 0 := by scalar_tac
      exact List.eq_nil_of_length_eq_zero h1
    obtain ⟨⟨buf, src1⟩, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [hnext] at hp
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hp)
    change (if alloc.vec.Vec.len c = 0#usize then _ else _) = ok o at hrun
    rw [if_neg hlen] at hrun
    rw [vec_index_ok' (by simpa using hlt)]
    simp only [bind_tc_ok, hci]
    obtain ⟨s, hs, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [hs]
    simp only [bind_tc_ok]
    obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [hq]
    simp only [bind_tc_ok]
    obtain ⟨r, ar1, st1⟩ := q
    try dsimp only at hrun ⊢
    cases r with
    | Err e =>
      have ho := (Result.ok_injective hrun).symm
      subst ho
      rfl
    | Ok t =>
      obtain ⟨c2, l, t1⟩ := t
      try dsimp only at hrun ⊢
      have hi1 : ∃ i1 : Std.Usize, i + 1#usize = ok i1 ∧ i1.val = i.val + 1 := by
        have hmax : i.val + 1 ≤ Std.Usize.max := by
          have := alloc.vec.Vec.len_val chunks
          have := chunks.property
          scalar_tac
        obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists (Std.Usize.add_spec (x := i) (y := 1#usize)
          (by scalar_tac))
        exact ⟨z, hz, by scalar_tac⟩
      obtain ⟨i1, hi1, hi1v⟩ := hi1
      rw [hi1]
      simp only [bind_tc_ok]
      exact ih (i := i1) (by rw [hi1v]; exact hdrop') hrest hrun

/-- **`parse_source` IS `parse_chunks` over the chunks read**: the reader
loop the binary runs, over a source that reads as the chunks of `chunks`
(each nonempty) and then an empty buffer, returns what `parse_chunks` returns
on `chunks`, with the same arena state. -/
theorem parse_source_eq {G S : Type} {mi : frontend.types.Modeller G}
    {inst : frontend.export_c.ChunkSource S} {pers : arena.store.PersTier} {m : G}
    {ar : arena.monad.AState} {src : S}
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)} {in_model census : Bool} {o}
    (hreads : ReadsAs inst src chunks.val)
    (hrun : frontend.export_c.parse_source mi inst pers m ar src in_model census = ok o) :
    frontend.export_c.parse_chunks mi pers m ar chunks in_model census
      = ok (o.1, o.2.1) := by
  rw [frontend.export_c.parse_source] at hrun
  rw [frontend.export_c.parse_chunks]
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [hq]
  simp only [bind_tc_ok]
  obtain ⟨r, e⟩ := q
  try dsimp only at hrun ⊢
  cases r with
  | Err e1 =>
    have ho := (Result.ok_injective hrun).symm
    subst ho
    rfl
  | Ok v =>
    try dsimp only at hrun ⊢
    exact parse_source_loop_eq chunks.val (i := 0#usize) (by simp) hreads hrun

end ConRon.Refine2.Frontend

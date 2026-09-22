import ConRon.RefineOld.Frontend.ScanWF
import ConRon.RefineOld.Frontend.Readers
import ConRon.RefineOld.Frontend.ProjRec
import ConRon.RefineOld.Frontend.Ind

/-! # The top of the parse (task #85, phase 1)

`Refine/Frontend/Base.lean` fixes the vocabulary, `ScanWF.lean` discharges the
scanner's one obligation, `Readers.lean` the entry readers, `ProjRec.lean` the
projection rewrite's builder and `Ind.lean` the inductive install.  **This file
is the top**: one scanned line applied to the state (`apply_line`), the chunk
fold that applies every complete line of a buffer (`feed_chunk`), and the three
entry points the rest of the port calls — `parse_bytes`, `parse_chunks` and the
built-in prelude.

What comes out is the statement `Refine/Main.lean`'s last standing input
hypothesis asks for: **every declaration the parse hands back is well formed**,

    ∀ d ∈ r.decls.val, DeclarationWF d

with no hypothesis on the bytes at all.  The only residue is `ModellerWF` —
DESIGN.md §3's ruling of 2026-09-13, *"leave the modeller unverified if you
can"* — which every statement carries and which disappears the day upstream
drops the modeller.

**The prelude is reached parametrically.**  `builtin_prelude_e_wf` is
`parse_bytes_wf` at `prelude_text::prelude_text()` and **evaluates nothing**:
`parse_bytes_wf` holds for every byte slice, so the 16,922-byte constant is
never unfolded (`AENEAS_FINDINGS.md` §3.8 measured evaluating it as out of
reach).  The prelude constant is a `[u8; …]` and not a `&str` — unlike
`kernel::pins_text`'s `PINS_TEXT` — so **it** costs the census nothing.

**The census is Lean's three, since task #86.**  `toStr` discharges its
`s.toByteArray.size ≤ U32.max` bound with `decide +native` on *every* extracted
`&str` constant (`AENEAS_FINDINGS.md` §3.8), and the scanner's key table used to
be sixty-eight such constants (`scan_fast::key_at`'s sixty-six member
spellings, and `scan_bool`'s `"true"` and `"false"`).  The axioms sit in the
constants' *definitions*, so every statement that named
`scan_fast::scan_line_fwd` inherited them whether or not anything was decided.
Task #86 spelled the table `[u8; N]`, which carries no axiom; the only `toStr`
constant left in the port is `kernel::pins_text::PINS_TEXT`, and only
`Refine/Main.lean`'s `_embedded` pair names it.

## `sorry` count in this file: 0
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

/-! ## Plumbing -/

/-- `StateDWF` reads six of the seventeen fields; a write to any other keeps
it.  `process_line_core_d`'s `.Ind` arm bumps the block counter before it
validates. -/
private theorem stateDWF_ind_count {st : frontend.export_c.StateD} {i : Std.U64}
    (hst : StateDWF st) : StateDWF { st with ind_count := i } :=
  ⟨hst.names, hst.levels, hst.exprs, hst.decls, hst.proj_owners, hst.proj_levels⟩

/-- The same for the `proj_rewrites` receipt, which the two rewriting arms
push a name onto. -/
private theorem stateDWF_proj_rewrites {st : frontend.export_c.StateD}
    {v : alloc.vec.Vec name.Name} (hst : StateDWF st) :
    StateDWF { st with proj_rewrites := v } :=
  ⟨hst.names, hst.levels, hst.exprs, hst.decls, hst.proj_owners, hst.proj_levels⟩

/-- The arms that cannot have produced an `.Ok`: `declined`, `merr` and
`invalid` are `ok (.Err …)` by definition, and so are the `line_err_to_check`
and `scan_err_render` tails. -/
local macro "dead " h:ident : tactic =>
  `(tactic| (exfalso; revert $h:ident;
             simp [frontend.export_c.declined, frontend.export_c.merr,
               frontend.export_c.invalid, bind_eq_ok_iff, uncurry_apply_pair]))

/-! ## One line -/

/-- `export_c::proj_rewrite_d` (con-leche: `ConLeche/Frontend/ExportC.lean:291-302`
`projRewriteD`).  The projection-function rewrite at a definition record: the
recorded owner comes out of `st.proj_owners` and the field's sort out of
`st.proj_levels` — both by `Base.lean`'s `map_get_wf`, which needs **neither**
an `Eq2Spec` nor a table invariant — and `proj_rec::proj_rec_value` builds the
recursor application from them, the constant's type and the parsed value. -/
theorem proj_rewrite_d_wf {st : frontend.export_c.StateD} {cv : env.ConstantVal}
    {vl e : expr.Expr} (hst : StateDWF st) (hcv : ConstantValWF cv) (hvl : ExprWF vl)
    (h : frontend.export_c.proj_rewrite_d st cv vl = ok (some e)) : ExprWF e := by
  rw [frontend.export_c.proj_rewrite_d.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨body, -, en, -, h⟩ := h
  split at h <;> try (exfalso; revert h; simp; done)
  simp only [bind_eq_ok_iff] at h
  obtain ⟨en1, -, h⟩ := h
  split at h <;> try (exfalso; revert h; simp; done)
  split at h
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨t1, -, o, ho, h⟩ := h
    split at h
    · exfalso; revert h; simp
    · rename_i o1
      have ho1 : ProjRecOwnerWF o1 := map_get_wf hst.proj_owners ho
      simp only [bind_eq_ok_iff] at h
      obtain ⟨b, -, h⟩ := h
      split at h
      · simp only [bind_eq_ok_iff] at h
        obtain ⟨n, -, o2, ho2, h⟩ := h
        split at h
        · exfalso; revert h; simp
        · rename_i l
          exact proj_rec_value_wf ho1 (map_get_wf hst.proj_levels ho2)
            hcv.2.2 hvl h
      · exfalso; revert h; simp
  · exfalso; revert h; simp

/-- `export_c::process_line_core_d` (con-leche:
`ConLeche/Frontend/ExportC.lean:625-697` `processLineCoreD`).  The six
declaration kinds, each building a `Declaration` out of what the readers hand
back: `parse_cv_d` for the constant, `get_decl_d` for the value, and
`install_ind_d` for a block.

**The record itself carries no obligation.**  `scan_types::DeclRec` holds two
`Vec<u32>`s — the `safety` and the `quotKind` *spellings* — and both are only
ever compared with a literal (`text::cps_beq` against `SAFE`,
`quot_kind_of`); neither becomes a `Name`, so no arm reads a string out of the
record and the lemma takes no record-WF hypothesis. -/
theorem process_line_core_d_wf {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    {st st' : frontend.export_c.StateD} {d : frontend.scan_types.DeclRec}
    (hgen : ModellerWF inst g) (hst : StateDWF st)
    (h : frontend.export_c.process_line_core_d inst g st d = ok (.Ok (), st')) :
    StateDWF st' := by
  rw [frontend.export_c.process_line_core_d.eq_def] at h
  split at h
  · -- `DeclRec::Ax`
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r, hr, h⟩ := h
    split at h
    · split at h
      · dead h
      · simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨st1, hpush, -, rfl⟩ := h
        refine push_decl_wf hst ?_ hpush
        exact parse_cv_d_wf hst hr
    · dead h
  · -- `DeclRec::Defn`
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r, hr, h⟩ := h
    split at h
    · rename_i v
      have hv : ConstantValWF v := parse_cv_d_wf hst hr
      simp only [bind_eq_ok_iff] at h
      obtain ⟨s, -, b, -, h⟩ := h
      split at h
      · simp only [bind_eq_ok_iff] at h
        obtain ⟨r1, hr1, h⟩ := h
        split at h
        · rename_i v1
          have hv1 : ExprWF v1 := get_decl_d_wf hst hr1
          simp only [bind_eq_ok_iff] at h
          obtain ⟨hint, -, o, ho, h⟩ := h
          split at h
          · simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨st1, hpush, -, rfl⟩ := h
            refine push_decl_wf hst ?_ hpush
            exact ⟨hv, hv1⟩
          · rename_i vl2
            have hvl2 : ExprWF vl2 := proj_rewrite_d_wf hst hv hv1 ho
            simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨n, -, st1, hpush, v2, -, -, rfl⟩ := h
            refine stateDWF_proj_rewrites (push_decl_wf hst ?_ hpush)
            exact ⟨hv, hvl2⟩
        · dead h
      · dead h
    · dead h
  · -- `DeclRec::Thm`
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r, hr, h⟩ := h
    split at h
    · rename_i v
      have hv : ConstantValWF v := parse_cv_d_wf hst hr
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r1, hr1, h⟩ := h
      split at h
      · rename_i v1
        have hv1 : ExprWF v1 := get_decl_d_wf hst hr1
        simp only [bind_eq_ok_iff] at h
        obtain ⟨o, ho, h⟩ := h
        split at h
        · simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨st1, hpush, -, rfl⟩ := h
          refine push_decl_wf hst ?_ hpush
          exact ⟨hv, hv1⟩
        · rename_i vl2
          have hvl2 : ExprWF vl2 := proj_rewrite_d_wf hst hv hv1 ho
          simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨n, -, st1, hpush, v2, -, -, rfl⟩ := h
          refine stateDWF_proj_rewrites (push_decl_wf hst ?_ hpush)
          exact ⟨hv, hvl2⟩
      · dead h
    · dead h
  · -- `DeclRec::Opaq`
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r, hr, h⟩ := h
    split at h
    · rename_i v
      have hv : ConstantValWF v := parse_cv_d_wf hst hr
      split at h
      · dead h
      · simp only [bind_eq_ok_iff] at h
        obtain ⟨r1, hr1, h⟩ := h
        split at h
        · simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨st1, hpush, -, rfl⟩ := h
          refine push_decl_wf hst ?_ hpush
          exact ⟨hv, get_decl_d_wf hst hr1⟩
        · dead h
    · dead h
  · -- `DeclRec::Quot`
    simp only [bind_eq_ok_iff] at h
    obtain ⟨r, hr, h⟩ := h
    split at h
    · rename_i v
      have hv : ConstantValWF v := parse_cv_d_wf hst hr
      simp only [bind_eq_ok_iff] at h
      obtain ⟨o, -, h⟩ := h
      split at h
      · dead h
      · simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨st1, hpush, -, rfl⟩ := h
        refine push_decl_wf hst ?_ hpush
        exact hv
    · dead h
  · -- `DeclRec::Ind`
    simp only [bind_eq_ok_iff] at h
    obtain ⟨i, -, r, -, h⟩ := h
    split at h
    · rename_i p
      obtain ⟨cts2, n_pd⟩ := p
      exact install_ind_d_wf hgen (stateDWF_ind_count hst) h
    · dead h

/-- `export_c::apply_decl_d` (con-leche:
`ConLeche/Frontend/ExportC.lean:699-711` `applyDeclD`).  `process_line_core_d`
verbatim: the read-only taint pre-scan that used to stand here went with
con-leche task #292. -/
theorem apply_decl_d_wf {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    {st st' : frontend.export_c.StateD} {d : frontend.scan_types.DeclRec}
    (hgen : ModellerWF inst g) (hst : StateDWF st)
    (h : frontend.export_c.apply_decl_d inst g st d = ok (.Ok (), st')) :
    StateDWF st' := by
  rw [frontend.export_c.apply_decl_d] at h
  exact process_line_core_d_wf hgen hst h

/-- `export_c::apply_line` (con-leche: `ConLeche/Frontend/ExportC.lean:713-726`
`applyLine`).  **The semantic layer**: one scanned line applied to the parse
state.  The three entry arms take the scanner's string obligation
(`LineRecWF`); the header and the blank line change nothing. -/
theorem apply_line_wf {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    {st st' : frontend.export_c.StateD} {r : frontend.scan_types.LineRec}
    (hgen : ModellerWF inst g) (hst : StateDWF st) (hr : LineRecWF r)
    (h : frontend.export_c.apply_line inst g st r = ok (.Ok (), st')) :
    StateDWF st' := by
  rw [frontend.export_c.apply_line.eq_def] at h
  split at h
  · exact parse_name_entry_d_wf hst hr h
  · exact parse_level_entry_d_wf hst h
  · exact parse_expr_entry_d_wf hst hr h
  · exact apply_decl_d_wf hgen hst h
  · simp only [Result.ok.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ hst
  · simp only [Result.ok.injEq, Prod.mk.injEq] at h
    exact h.2 ▸ hst

/-! ## The chunk fold -/

/-- `export_c::apply_final_line` (con-leche:
`ConLeche/Frontend/ExportC.lean:765-775` `applyFinalLine`).  The last line of a
stream, the one no newline ends: `scan_line_fwd_wf` supplies the `LineRecWF`
that `apply_line_wf` asks for. -/
theorem apply_final_line_wf {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    {st st' : frontend.export_c.StateD} {b : Slice Std.U8} {i : Std.Usize}
    {ln : Std.U64} (hgen : ModellerWF inst g) (hst : StateDWF st)
    (h : frontend.export_c.apply_final_line inst g st b i ln = ok (.Ok (), st')) :
    StateDWF st' := by
  rw [frontend.export_c.apply_final_line.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  split at h
  · rename_i p
    obtain ⟨r1, j⟩ := p
    simp only [uncurry_apply_pair, bind_eq_ok_iff] at h
    obtain ⟨⟨r2, st1⟩, happ, h⟩ := h
    simp only [uncurry_apply_pair] at h
    split at h
    · simp only [Result.ok.injEq, Prod.mk.injEq] at h
      exact h.2 ▸ apply_line_wf hgen hst (scan_line_fwd_wf hr) happ
    · dead h
  · dead h

/-- **The file's main loop** (`export_c::feed_chunk`'s `while`, con-leche:
`ConLeche/Frontend/ExportC.lean:777-811` `feedChunk`).  The invariant is
`StateDWF` and nothing else.

`feed_chunk_loop` is `partial_fixpoint` and has no induction principle, so the
invariant goes by strong induction on a `Nat` measure.  The loop does **not**
step by one: it jumps the byte index to the scanner's `j`.  What makes the
measure decrease is the code's own no-progress guard — `if i >= j` is an
internal error, so the recursive call has `i < j` — together with the `i <
b.len` the loop is under; hence the measure `b.len - i`. -/
private theorem feed_chunk_loop_wf {G : Type} {inst : frontend.in_model_rec.Modeller G}
    {g : G} (hgen : ModellerWF inst g) (N : Nat) :
    ∀ (st : frontend.export_c.StateD) (b : Slice Std.U8) (i : Std.Usize)
      (ln : Std.U64) (p : Std.U64 × Std.Usize) (st' : frontend.export_c.StateD),
      StateDWF st → (Slice.len b).val - i.val = N →
      frontend.export_c.feed_chunk_loop inst g st b i ln = ok (.Ok p, st') →
      StateDWF st' := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st b i ln p st' hst hN h
    rw [frontend.export_c.feed_chunk_loop.eq_def] at h
    simp only [] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r, hr, h⟩ := h
      split at h
      · rename_i q
        obtain ⟨r1, j⟩ := q
        simp only [uncurry_apply_pair] at h
        split at h
        · simp only [Result.ok.injEq, Prod.mk.injEq] at h
          exact h.2 ▸ hst
        · simp only [bind_eq_ok_iff] at h
          obtain ⟨⟨r2, st1⟩, happ, h⟩ := h
          simp only [uncurry_apply_pair] at h
          split at h
          · have hst1 : StateDWF st1 := apply_line_wf hgen hst (scan_line_fwd_wf hr) happ
            split at h
            · dead h
            · rename_i hge
              simp only [bind_eq_ok_iff] at h
              obtain ⟨ln1, -, h⟩ := h
              exact ih ((Slice.len b).val - j.val) (by scalar_tac) st1 b j ln1 p st'
                hst1 rfl h
          · dead h
      · simp only [bind_eq_ok_iff] at h
        obtain ⟨b1, -, h⟩ := h
        split at h
        · dead h
        · simp only [Result.ok.injEq, Prod.mk.injEq] at h
          exact h.2 ▸ hst
    · simp only [Result.ok.injEq, Prod.mk.injEq] at h
      exact h.2 ▸ hst

/-- `export_c::feed_chunk` (con-leche:
`ConLeche/Frontend/ExportC.lean:777-811` `feedChunk`).  Every complete line of
the chunk from `i`, applied in order. -/
theorem feed_chunk_wf {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    {st st' : frontend.export_c.StateD} {b : Slice Std.U8} {i : Std.Usize}
    {ln : Std.U64} {p : Std.U64 × Std.Usize} (hgen : ModellerWF inst g)
    (hst : StateDWF st)
    (h : frontend.export_c.feed_chunk inst g st b i ln = ok (.Ok p, st')) :
    StateDWF st' :=
  feed_chunk_loop_wf hgen _ st b i ln p st' hst rfl h

/-- `export_c::parse_result_of_state` (con-leche:
`ConLeche/Frontend/ExportC.lean:760-763` `ParseResultD.ofState`).  The result is
the state's own fields, so the invariant's `decls` clause *is* the conclusion. -/
theorem parse_result_of_state_wf {st : frontend.export_c.StateD}
    {r : frontend.export_c.ParseResultD} (hst : StateDWF st)
    (h : frontend.export_c.parse_result_of_state st = ok r) :
    ∀ d ∈ r.decls.val, DeclarationWF d := by
  rw [frontend.export_c.parse_result_of_state] at h
  simp only [Result.ok.injEq] at h
  exact h ▸ hst.decls

/-- `export_c::parse_bytes_final` (con-leche:
`ConLeche/Frontend/ExportC.lean:827-839` `parseBytes`, its cited tail).  The
last line, then the result. -/
theorem parse_bytes_final_wf {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    {st : frontend.export_c.StateD} {b : Slice Std.U8} {tail : Std.Usize}
    {ln : Std.U64} {r : frontend.export_c.ParseResultD}
    (hgen : ModellerWF inst g) (hst : StateDWF st)
    (h : frontend.export_c.parse_bytes_final inst g st b tail ln = ok (.Ok r)) :
    ∀ d ∈ r.decls.val, DeclarationWF d := by
  rw [frontend.export_c.parse_bytes_final.eq_def] at h
  simp only [] at h
  split at h
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨i1, -, ⟨r2, st1⟩, hfin, h⟩ := h
    simp only [uncurry_apply_pair] at h
    split at h
    · simp only [bind_eq_ok_iff, Result.ok.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨prd, hprd, hr⟩ := h
      exact parse_result_of_state_wf (apply_final_line_wf hgen hst hfin) (hr ▸ hprd)
    · dead h
  · simp only [bind_eq_ok_iff, Result.ok.injEq, core.result.Result.Ok.injEq] at h
    obtain ⟨prd, hprd, hr⟩ := h
    exact parse_result_of_state_wf hst (hr ▸ hprd)

/-- `export_c::chunk_step` (con-leche:
`ConLeche/Frontend/ExportC.lean:848-865` `chunkStep`).  One chunk of the
stream: the carried tail in front of the new bytes, `feed_chunk`, then the new
tail cut off.  Only `feed_chunk` touches the state. -/
theorem chunk_step_wf {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    {st st' : frontend.export_c.StateD} {carry : alloc.vec.Vec Std.U8}
    {ln total : Std.U64} {buf : Slice Std.U8}
    {q : (alloc.vec.Vec Std.U8) × Std.U64 × Std.U64}
    (hgen : ModellerWF inst g) (hst : StateDWF st)
    (h : frontend.export_c.chunk_step inst g st carry ln total buf = ok (.Ok q, st')) :
    StateDWF st' := by
  rw [frontend.export_c.chunk_step.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨i, -, i2, -, i3, -, i4, -, h⟩ := h
  split at h
  · dead h
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨buf1, -, s, -, ⟨r, st1⟩, hfeed, h⟩ := h
    simp only [uncurry_apply_pair] at h
    split at h
    · rename_i t
      obtain ⟨ln2, tail⟩ := t
      simp only [uncurry_apply_pair, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨s1, -, v, -, i7, -, i8, -, -, hs⟩ := h
      exact hs ▸ feed_chunk_wf hgen hst hfeed
    · dead h

/-- `export_c::chunk_finish` (con-leche:
`ConLeche/Frontend/ExportC.lean:867-874` `chunkFinish`).  The end of the
stream: the carried tail, if any, is its last line. -/
theorem chunk_finish_wf {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    {st : frontend.export_c.StateD} {carry : Slice Std.U8} {ln : Std.U64}
    {r : frontend.export_c.ParseResultD}
    (hgen : ModellerWF inst g) (hst : StateDWF st)
    (h : frontend.export_c.chunk_finish inst g st carry ln = ok (.Ok r)) :
    ∀ d ∈ r.decls.val, DeclarationWF d := by
  rw [frontend.export_c.chunk_finish.eq_def] at h
  simp only [] at h
  split at h
  · simp only [bind_eq_ok_iff, Result.ok.injEq, core.result.Result.Ok.injEq] at h
    obtain ⟨prd, hprd, hr⟩ := h
    exact parse_result_of_state_wf hst (hr ▸ hprd)
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨i1, -, ⟨r2, st1⟩, hfin, h⟩ := h
    simp only [uncurry_apply_pair] at h
    split at h
    · simp only [bind_eq_ok_iff, Result.ok.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨prd, hprd, hr⟩ := h
      exact parse_result_of_state_wf (apply_final_line_wf hgen hst hfin) (hr ▸ hprd)
    · dead h

/-! ## The three headlines -/

/-- **Wholesale direct parse of a byte buffer** (`export_c::parse_bytes`,
con-leche: `ConLeche/Frontend/ExportC.lean:827-839` `parseBytes`): every
declaration it hands back is well formed, for **every** byte slice — the size
guard, the scanner's verdicts and the line errors are all accounted for by the
`.Ok` hypothesis alone. -/
theorem parse_bytes_wf {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (hgen : ModellerWF inst g) {b : Slice Std.U8} {im ce : Bool}
    {r : frontend.export_c.ParseResultD}
    (h : frontend.export_c.parse_bytes inst g b im ce = ok (.Ok r)) :
    ∀ d ∈ r.decls.val, DeclarationWF d := by
  rw [frontend.export_c.parse_bytes.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨i1, -, i2, -, h⟩ := h
  split at h
  · dead h
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨st, hinit, ⟨r1, st1⟩, hfeed, h⟩ := h
    simp only [uncurry_apply_pair] at h
    split at h
    · rename_i q
      obtain ⟨ln, tail⟩ := q
      exact parse_bytes_final_wf hgen (feed_chunk_wf hgen (state_d_init_wf hinit) hfeed) h
    · dead h

/-- The chunk fold's loop (`export_c::parse_chunks`'s `while i < n`, con-leche:
`ConLeche/Frontend/ExportC.lean:882-901` `parseChunks`).  The plain shape: one
chunk per step, `chunk_step` applied to the carried tail, so the measure is
`n - i` and the invariant is `StateDWF`. -/
private theorem parse_chunks_loop_wf {G : Type} {inst : frontend.in_model_rec.Modeller G}
    {g : G} (hgen : ModellerWF inst g) (N : Nat) :
    ∀ (chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (st : frontend.export_c.StateD)
      (carry : alloc.vec.Vec Std.U8) (ln total : Std.U64) (n i : Std.Usize)
      (r : frontend.export_c.ParseResultD),
      StateDWF st → n.val - i.val = N →
      frontend.export_c.parse_chunks_loop inst g chunks st carry ln total n i = ok (.Ok r) →
      ∀ d ∈ r.decls.val, DeclarationWF d := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro chunks st carry ln total n i r hst hN h
    rw [frontend.export_c.parse_chunks_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨v, -, s, -, ⟨r1, st1⟩, hstep, h⟩ := h
      simp only [uncurry_apply_pair] at h
      split at h
      · rename_i t
        obtain ⟨c2, l, t1⟩ := t
        simp only [uncurry_apply_pair, bind_eq_ok_iff] at h
        obtain ⟨i1, hi1, h⟩ := h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        exact ih (n.val - i1.val) (by scalar_tac) chunks st1 c2 l t1 n i1 r
          (chunk_step_wf hgen hst hstep) rfl h
      · dead h
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨s, -, h⟩ := h
      exact chunk_finish_wf hgen hst h

/-- **The streaming parse** (`export_c::parse_chunks`, con-leche:
`ConLeche/Frontend/ExportC.lean:882-901` `parseChunks`): `chunk_step` folded
over a list of chunks and closed by `chunk_finish`.  The same conclusion as
`parse_bytes_wf`, for **any** cutting of the input into chunks. -/
theorem parse_chunks_wf {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (hgen : ModellerWF inst g)
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)} {im ce : Bool}
    {r : frontend.export_c.ParseResultD}
    (h : frontend.export_c.parse_chunks inst g chunks im ce = ok (.Ok r)) :
    ∀ d ∈ r.decls.val, DeclarationWF d := by
  rw [frontend.export_c.parse_chunks.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨st, hinit, h⟩ := h
  exact parse_chunks_loop_wf hgen _ chunks st _ _ _ _ _ r (state_d_init_wf hinit) rfl h

/-- **The built-in prelude** (`prelude::builtin_prelude_e`, con-leche:
`ConLeche/Frontend/Prelude.lean:64-68` `builtinPreludeE`).  `parse_bytes_wf` at
`prelude_text::prelude_text()` — and it **evaluates nothing**: the conclusion
holds for every byte slice, so the 16,922-byte constant is never unfolded
(`AENEAS_FINDINGS.md` §3.8 measured that as out of reach).

Unlike `kernel::pins_text`'s `PINS_TEXT`, the prelude constant is a `[u8; …]`
and not a `&str`, so **the prelude itself** contributes nothing to the census;
what the census does carry is the *scanner's* `&str` key table, which every
statement in this file carries (the module note explains it). -/
theorem builtin_prelude_e_wf {M : Type} {inst : frontend.in_model_rec.Modeller M} {m : M}
    (hgen : ModellerWF inst m) {pre : frontend.prepare.PreludeIx}
    (h : frontend.prelude.builtin_prelude_e inst m = ok (.Ok pre)) :
    ∀ d ∈ pre.decls.val, DeclarationWF d := by
  rw [frontend.prelude.builtin_prelude_e.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨text, -, r, hr, h⟩ := h
  split at h
  · rename_i r1
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h
    exact h ▸ parse_bytes_wf hgen hr
  · dead h

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

The three headlines: Lean's own three axioms and nothing else, since task #86
spelled the scanner's key table as byte arrays (the module note).  No
`native_decide` is invoked anywhere in `proof/`, and nothing here evaluates the
key table or the prelude text. -/

/-- info: 'ConRon.Refine.Frontend.parse_bytes_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_bytes_wf

/-- info: 'ConRon.Refine.Frontend.parse_chunks_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_chunks_wf

/-- info: 'ConRon.Refine.Frontend.builtin_prelude_e_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms builtin_prelude_e_wf

end ConRon.Refine.Frontend

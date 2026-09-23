/-
# `ConRon.Refine2.Frontend.Top` — the line layer, the chunk drivers, the prelude

**Task #97-P5-Frontend**, the third of `frontend/export_c.rs`'s files and all
of `frontend/prelude.rs`: `process_line_core_d`, `apply_line`, `feed_chunk`,
`chunk_step`, `chunk_finish`, `parse_chunks` and `builtin_prelude_e` — and the
tier's two top statements.

## The tier's top statement, and what it is FOR

    theorem parse_chunks_refines … :
      SimStreamRel ParseResultDRel pers lst o
        (parseChunks (absModeller …) (absChunks chunks) in_model census)

*The Rust parse of a chunk list accepting implies the twin's parse accepts,
with the abstracted declarations and a state related to the Rust's.*  With
`Refine2/Checker/Top.lean`'s `install_then_check_refines` — which is what
`crates/con-ron/src/driver.rs` calls per record — and
`prepare_prelude_refines` between them, **con-ron's pipeline has a statement
at the bytes**: the chunks go in, the fold's verdict comes out, and every step
between is a named lemma about a named port function.

The driver's own read loop is UNVERIFIED and stays so (`scripts/holes.sh` is
where that boundary is recorded).  What the driver does is fold `chunk_step`
over the buffers its handle hands out and close with `chunk_finish`, and
`parse_chunks` is that fold's pure specification — the twin's `runPipeline`
keeps the same relationship to its own `readFold` (task #97e part 2 §5), and
equating the two is con-leche's `parseChunks_eq_parseExportD`, which belongs
to neither side's refinement.

## Four hypotheses and no more

`AStateRel` / `AStateInv` are the tier's own; `ScanSpec` is the byte
recogniser's (three clauses, every one a theorem of `RefineOld/Frontend/`
against the SAME Rust functions — see `Refine2/Frontend/Shape.lean`'s section
note); `ModellerRefines` is the seam's, and DESIGN §8.2 puts the modeller
outside the verified surface by design.  **`ModellerWF` is NOT among them**,
and that is the arena's dividend: the original campaign's `hgen` said *"every
declaration `Modeller::generate` returns is well formed"*, and over handles
`absIDeclaration` is total, so nothing needs it.

`DeclRecStrWF` does not appear either — it is inside `ScanSpec.scanLineStr`,
which is where the scanner owes it.

## `sorry` count in this file: 15
-/
import ConRon.Refine2.Frontend.ExportCInd

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend

open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (LineRec DeclRec)

/-! ## The line layer -/

/-- **`process_line_core_d` refines `processLineCoreD`**
(`ExportC.lean:600-658`) — the record's own semantics: the declaration kinds,
producing `IDeclaration` records.  The `safety` and `kind` spellings are
compared against con-leche `String` LITERALS, which is why this is the one
line-layer statement that carries `DeclRecStrWF`. -/
theorem process_line_core_d_refines {G : Type} {inst : frontend.types.Modeller G}
    {m : G} {lmd : Arena.Frontend.Modeller} {pers rst lst rsd lsd d o}
    (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd) (hs : DeclRecStrWF d)
    (h : frontend.export_c.process_line_core_d inst pers m rst rsd d = ok o) :
    SimDV pers lst o (processLineCoreD lmd lsd (absDeclRec d)) := by sorry

/-- **`apply_decl_d` refines `applyDeclD`** (`ExportC.lean:662-664`). -/
theorem apply_decl_d_refines {G : Type} {inst : frontend.types.Modeller G}
    {m : G} {lmd : Arena.Frontend.Modeller} {pers rst lst rsd lsd d o}
    (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd) (hs : DeclRecStrWF d)
    (h : frontend.export_c.apply_decl_d inst pers m rst rsd d = ok o) :
    SimDV pers lst o (applyDeclD lmd lsd (absDeclRec d)) := by sorry

/-- **`apply_line` refines `applyLine`** (`ExportC.lean:670-678`) — THE
SEMANTIC LAYER: one scanned line applied to the parse state. -/
theorem apply_line_refines {G : Type} {inst : frontend.types.Modeller G}
    {m : G} {lmd : Arena.Frontend.Modeller} {pers rst lst rsd lsd r o}
    (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (hs : LineRecStrWF r) (hnat : LineNatValSpec r)
    (h : frontend.export_c.apply_line inst pers m rst rsd r = ok o) :
    SimDV pers lst o (applyLine lmd lsd (absLineRec r)) := by sorry

/-! ## The chunk drivers

Four functions, and their error channel is a PAIR — the position travels as a
VALUE because (B) has ONE monad (DESIGN §8.4), where con-leche changes monad
to `StateT CState (Except (CheckError × Nat))`.  The port matches exactly, so
`SimStream` is `Refine2/Checker/Top.lean`'s `SimFold` at this pair. -/

/-- **`size_error`** — THE SIZE GUARD's error: an input of `USize.size` bytes
or more is refused before any of it is read.  The port drops the interpolated
byte count (`2 ^ 64` renders in no `u64`); the KIND is what is claimed. -/
theorem size_error_refines {o} (h : frontend.export_c.size_error = ok o) :
    absAErrKind o.1 = lAErrKind sizeError.1 ∧ absU o.2 = sizeError.2 := by
  rw [frontend.export_c.size_error] at h
  obtain ⟨s, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨ce, hce, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [kernel.core_types.not_implemented] at hce
  simp only [Result.ok.injEq] at hce h
  subst h
  refine ⟨by rw [← hce]; rfl, rfl⟩

/-- **`CHUNK_SIZE` refines `chunkSize`** (`ExportC.lean:768`). -/
theorem chunk_size_refines {v} (h : frontend.export_c.CHUNK_SIZE = ok v) :
    v.val = chunkSize.toNat := by
  -- `4 * 1024 * 1024` on both sides, but the twin's is a `USize` numeral and
  -- the port's a `Std.Usize` product; the round trip wants `USize.toNat` of a
  -- literal, which neither `decide` nor `simp` takes here.
  sorry

/-- **`concat_bytes` refines `concatBytes`** (`ExportC.lean:824-826`). -/
theorem concat_bytes_refines {chunks v}
    (h : frontend.export_c.concat_bytes chunks = ok v) :
    absChunk v = concatBytes (absChunks chunks) := by sorry

/-- **`apply_final_line` refines `applyFinalLine`** (`ExportC.lean:726-739`) —
the LAST line of a stream, the one no newline ends.  A syntactic failure is
reported at its offset in the line. -/
theorem apply_final_line_refines {G : Type} {inst : frontend.types.Modeller G}
    {m : G} {lmd : Arena.Frontend.Modeller} {pers rst lst rsd lsd b i line_no o}
    (hsc : ScanSpec) (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.apply_final_line inst pers m rst rsd b i line_no
      = ok o) :
    SimStreamD (fun _ => ()) pers lst o
      (do
        match ← applyFinalLine lmd lsd (absBytes b) (absPos i) (absU line_no) with
        | .error e => pure (.error e)
        | .ok st => pure (.ok (st, ()))) := by sorry

/-- **`feed_chunk` refines `feedChunk`** (`ExportC.lean:742-765`) — every
COMPLETE line of the chunk from `i`, applied in order.  A line a chunk cut in
half is told from a malformed one by whether the rest of the chunk holds a
newline at all, which is why a scan failure is not immediately an error. -/
theorem feed_chunk_refines {G : Type} {inst : frontend.types.Modeller G}
    {m : G} {lmd : Arena.Frontend.Modeller} {pers rst lst rsd lsd b i line_no o}
    (hsc : ScanSpec) (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.feed_chunk inst pers m rst rsd b i line_no = ok o) :
    SimStreamD (fun p => (absU p.1, absPos p.2)) pers lst o
      (do
        match ← feedChunk lmd lsd (absBytes b) (absPos i) (absU line_no) with
        | .error e => pure (.error e)
        | .ok (st, n, j) => pure (.ok (st, (n, j)))) := by sorry

/-- **`parse_bytes_final`** — the cited tail of `parseBytes`: the last line. -/
theorem parse_bytes_final_refines {G : Type} {inst : frontend.types.Modeller G}
    {m : G} {lmd : Arena.Frontend.Modeller} {pers rst lst rsd lsd b tail line_no o}
    (hsc : ScanSpec) (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.parse_bytes_final inst pers m rst rsd b tail line_no
      = ok o) :
    SimStreamRel ParseResultDRel pers lst o
      (if absPos tail < (absBytes b).usize then do
        match ← applyFinalLine lmd lsd (absBytes b) (absPos tail) (absU line_no + 1) with
        | .error e => pure (.error e)
        | .ok st => pure (.ok (ParseResultD.ofState st))
      else pure (.ok (ParseResultD.ofState lsd))) := by sorry

/-- **`parse_bytes` refines `parseBytes`** (`ExportC.lean:779-790`) —
wholesale direct parse of a byte buffer, the specification the streaming parse
is proved equal to. -/
theorem parse_bytes_refines {G : Type} {inst : frontend.types.Modeller G}
    {m : G} {lmd : Arena.Frontend.Modeller} {pers rst lst b in_model census o}
    (hsc : ScanSpec) (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.parse_bytes inst pers m rst b in_model census = ok o) :
    SimStreamRel ParseResultDRel pers lst o
      (parseBytes lmd (absBytes b) in_model census) := by sorry

/-- **`parse_export_d` refines `parseExportD`** (`ExportC.lean:795-797`).
Aeneas reads a `&str` as its bytes and `core::str::as_bytes` is con-ron-core's
own hole (OVERVIEW §8.1), modelled as the identity — which is exactly what
`String.toUTF8` is on the twin's side. -/
theorem parse_export_d_refines {G : Type} {inst : frontend.types.Modeller G}
    {m : G} {lmd : Arena.Frontend.Modeller} {pers rst lst contents in_model census o}
    (hsc : ScanSpec) (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.parse_export_d inst pers m rst contents in_model census
      = ok o) :
    ∀ b s, core.str.Str.as_bytes contents = ok b →
      (absBytes b) = String.toUTF8 s →
      SimStreamRel ParseResultDRel pers lst o
        (parseExportD lmd s in_model census) := by sorry

/-- **`chunk_step` refines `chunkStep`** (`ExportC.lean:803-811`) — one chunk
of the stream, applied: the carried incomplete tail in front of the new bytes,
every complete line fed, the new incomplete tail cut off for the next chunk. -/
theorem chunk_step_refines {G : Type} {inst : frontend.types.Modeller G}
    {m : G} {lmd : Arena.Frontend.Modeller}
    {pers rst lst rsd lsd carry line_no total buf0 o}
    (hsc : ScanSpec) (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.chunk_step inst pers m rst rsd carry line_no total buf0
      = ok o) :
    SimStreamD (fun p => (absChunk p.1, absU p.2.1, absU p.2.2)) pers lst o
      (do
        match ← chunkStep lmd lsd (absChunk carry) (absU line_no) (absU total)
            (absBytes buf0) with
        | .error e => pure (.error e)
        | .ok (st, c, n, t) => pure (.ok (st, (c, n, t)))) := by sorry

/-- **`chunk_finish` refines `chunkFinish`** (`ExportC.lean:815-820`) — the end
of the stream: the carried tail, if any, is its last line. -/
theorem chunk_finish_refines {G : Type} {inst : frontend.types.Modeller G}
    {m : G} {lmd : Arena.Frontend.Modeller} {pers rst lst rsd lsd carry line_no o}
    (hsc : ScanSpec) (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.chunk_finish inst pers m rst rsd carry line_no = ok o) :
    SimStreamRel ParseResultDRel pers lst o
      (chunkFinish lmd lsd (absBytes carry) (absU line_no)) := by sorry

/-! ## The tier's first top statement -/

/-- **`parse_chunks` refines `parseChunks`** (`ExportC.lean:846-848`) — **THE
STREAMING PARSE**: `chunk_step` folded over a list of chunks with
`chunk_finish` at its end, which is what the driver's read loop does with the
buffers its handle hands out, minus the reads.

*The Rust parse of the chunks accepting implies the twin's parse accepts, with
the abstracted state and declarations.*  Four hypotheses: the two state ones,
the scanner's, and the modeller's. -/
theorem parse_chunks_refines {G : Type} {inst : frontend.types.Modeller G}
    {m : G} {lmd : Arena.Frontend.Modeller} {pers rst lst chunks in_model census o}
    (hsc : ScanSpec) (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.parse_chunks inst pers m rst chunks in_model census
      = ok o) :
    SimStreamRel ParseResultDRel pers lst o
      (parseChunks lmd (absChunks chunks) in_model census) := by sorry

/-! ## The prelude, and the tier's second top statement -/

/-- **`prelude::builtin_prelude_text`** — the committed prelude bytes.  The
port's constant is generated by `scripts/gen-prelude.sh` and the twin's by
`scripts/gen-prelude-lean.sh`, both with a `--check` gate and both in the same
67 chunks of at most 256 bytes; this says the two are the same bytes, which is
the ONE fact about them a proof needs and which no proof can get from either
generator. -/
theorem builtin_prelude_text_refines {v}
    (h : frontend.prelude.builtin_prelude_text = ok v) :
    absChunk v = preludeText := by sorry

/-- **`prelude::builtin_prelude_e` refines `builtinPreludeE`**
(`Arena/Frontend/Prelude.lean:52-56`) — **the tier's second top statement**:
the built-in prelude, parsed with the ORDINARY parser into the same store the
stream goes into, so that the prelude's nodes and the stream's are hash-consed
together.

Task #97e part 1 measured what that is worth: on an empty input the store
holds 196 expression, 5 level and 55 name nodes, and on `Init` the totals are
the stream's own entry counts alone — every prelude node coincides with a node
the stream declares anyway. -/
theorem builtin_prelude_e_refines {G : Type} {inst : frontend.types.Modeller G}
    {m : G} {lmd : Arena.Frontend.Modeller} {pers rst lst o}
    (hsc : ScanSpec) (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.prelude.builtin_prelude_e inst pers m rst = ok o) :
    SimStream absPreludeIx pers lst o (builtinPreludeE lmd) := by sorry

/-- `usize as u64`: a widening, so the value is kept. -/
theorem cast_u64_usize {i : Std.Usize} {r : Std.U64}
    (h : lift (UScalar.cast .U64 i) = ok r) : r.val = i.val := by
  simp only [lift, Result.ok.injEq] at h
  subst h
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have := i.hBounds
  simp only [UScalarTy.numBits] at this ⊢
  cases System.Platform.numBits_eq with
  | inl h => rw [h] at this; omega
  | inr h => rw [h] at this; omega

/-! ## The preparation (moved here from `Prepare.lean`, task #97-P5-Front)

`prepare_d` runs the hoist and `export_c::sat_sub`, so its refinement sits
above both. -/

/-- **`prepare::prepare_d` refines `prepareD`**
(`Arena/Frontend/Prepare.lean:128-131`) — one of the tier's named
deliverables.  Composed from `front_of_refines`, `prepared_stream_refines`,
`hoist_nat_op_ground_refines` and `sat_sub_refines`. -/
theorem prepare_d_refines {pers rst lst pre ds o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.prepare.prepare_d pers rst pre ds = ok o) :
    Sim absPrepared (fun _ => True) pers lst o
      (prepareD (absPreludeIx pre) (absIDeclArr ds)) := by
  rw [frontend.prepare.prepare_d] at h
  obtain ⟨⟨r, e⟩, hf, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hF := front_of_refines hrel hinv hf
  simp only [Sim] at hF ⊢
  simp only [prepareD, absPreludeIx, am_run_bind']
  cases r with
  | Err e1 =>
    have ho := Result.ok_injective h; subst ho
    exact AErrSim.bind hF _
  | Ok v =>
    obtain ⟨v1, v2⟩ := v
    obtain ⟨lst1, hx1, hrel1, hinv1, hext1, hwf1⟩ := hF
    rw [hx1]
    simp only at h
    obtain ⟨all, hall, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hs := prepared_stream_refines hwf1.1 hall
    obtain ⟨⟨r1, st1⟩, hh, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hH := hoist_nat_op_ground_refines hrel1 hinv1 hh
    simp only [Sim] at hH
    have hfr : (absPlan pre.decls ds (v1, v2)).1 ++ (absPlan pre.decls ds (v1, v2)).2
        = absIDeclArr all := by rw [hs]; rfl
    simp only [except_ok_bind]
    rw [hfr]
    cases r1 with
    | Err e2 =>
      have ho := Result.ok_injective h; subst ho
      exact AErrSim.bind hH _
    | Ok hv =>
      obtain ⟨v3, v4⟩ := hv
      obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := hH
      rw [hx2]
      try simp only at h
      obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨syn, hsyn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have ho := Result.ok_injective h; subst ho
      have hsv := sat_sub_refines hsyn
      refine ⟨lst2, ?_, hrel2, hinv2, Ext.trans hext1 hext2, trivial⟩
      simp only [except_ok_bind, absPrepared]
      have e1 := cast_u64_usize hi1
      have e2 := cast_u64_usize hi2
      rw [hsv, absU, absU, e1, e2]
      simp [absIDeclArr]
      rfl

/-- **`prepare::prepare_prelude` refines `preparePrelude`**
(`Arena/Frontend/Prepare.lean:138-140`) — the second half of what the driver
runs after the parse, and what `Refine2/Checker/Top.lean`'s
`install_then_check_refines` is handed. -/
theorem prepare_prelude_refines {pers rst lst pre ds o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.prepare.prepare_prelude pers rst pre ds = ok o) :
    Sim absIDeclArr (fun _ => True) pers lst o
      (preparePrelude (absPreludeIx pre) (absIDeclArr ds)) := by
  rw [frontend.prepare.prepare_prelude] at h
  obtain ⟨⟨r, st1⟩, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hD := prepare_d_refines hrel hinv hd
  simp only [Sim] at hD ⊢
  simp only [preparePrelude, am_run_bind']
  cases r with
  | Err e =>
    have ho := Result.ok_injective h; subst ho
    exact AErrSim.bind hD _
  | Ok p =>
    have ho := Result.ok_injective h; subst ho
    obtain ⟨lst', hx, hrel', hinv', hext', -⟩ := hD
    rw [hx]
    exact ⟨lst', rfl, hrel', hinv', hext', trivial⟩


/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.Frontend.size_error_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms size_error_refines

end ConRon.Refine2.Frontend

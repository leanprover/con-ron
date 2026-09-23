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

## `sorry` count in this file: 7
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

/-! ## Stream plumbing (task #97-P5-Front)

Three moves every chunk driver's proof makes: the twin's result-reshaping
wrapper (`match ← x with | .error e => pure (.error e) | .ok … => pure (.ok …)`)
is a `map` on the run; a `StreamErrSim` survives a continuation that passes an
error value through; and `SimStreamD`'s success arm, read back through the
wrapper, is a run of the unwrapped action. -/

theorem except_pure_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (pure a : Except ε α) >>= f = f a := rfl

theorem stream_run_map {β γ : Type} (x : AM (Except (Arena.CheckError × Nat) β))
    (f : β → γ) (lst : AState) :
    (x >>= fun r => pure (r.map f) : AM (Except (Arena.CheckError × Nat) γ)).run lst =
      (x.run lst) >>= fun p => .ok (p.1.map f, p.2) := rfl

/-- The wrapper IS a map: `g` passes an error value through and maps a
success by `f`.  Stated over an arbitrary `g` because every `match ← x with`
elaborates to its own auxiliary matcher, which no rewrite can key on. -/
theorem wrap_map {β γ : Type} (x : AM (Except (Arena.CheckError × Nat) β))
    {g : Except (Arena.CheckError × Nat) β → AM (Except (Arena.CheckError × Nat) γ)}
    (f : β → γ) (h1 : ∀ e, g (.error e) = pure (.error e))
    (h2 : ∀ b, g (.ok b) = pure (.ok (f b))) :
    (x >>= g) = (x >>= fun r => pure (r.map f)) := by
  congr 1; funext r; cases r with
  | error e => exact h1 e
  | ok b => exact h2 b

/-- An error pair's claim survives a continuation that passes an error value
through unchanged. -/
theorem StreamErrSim.bind {γ δ : Type} {p : kernel.core_types.CheckError × Std.U64}
    {x : Except Arena.CheckError (Except (Arena.CheckError × Nat) γ × AState)}
    (h : StreamErrSim p x)
    (g : Except (Arena.CheckError × Nat) γ × AState →
      Except Arena.CheckError (Except (Arena.CheckError × Nat) δ × AState))
    (hg : ∀ e s, g (.error e, s) = .ok (.error e, s)) :
    StreamErrSim p (x >>= g) := by
  intro k hk
  rcases h k hk with ⟨le, lst', hx, hle⟩ | ⟨le, hx, hle⟩
  · exact Or.inl ⟨le, lst', by rw [hx]; exact hg _ _, hle⟩
  · exact Or.inr ⟨le, by rw [hx]; rfl, hle⟩

/-- `SimStreamD`'s success arm at a wrapper, as the unwrapped run. -/
theorem stream_map_ok {β γ : Type} {x : Except Arena.CheckError
      (Except (Arena.CheckError × Nat) β × AState)} {f : β → γ}
    {c : γ} {lst' : AState}
    (h : (x >>= fun p => .ok (p.1.map f, p.2)) = .ok (.ok c, lst')) :
    ∃ b, x = .ok (.ok b, lst') ∧ f b = c := by
  revert h
  rcases x with e | ⟨r, s⟩
  · intro h; cases h
  · rcases r with e | b
    · intro h; cases h
    · intro h
      have h' : (Except.ok (Except.ok (f b), s) :
          Except Arena.CheckError (Except (Arena.CheckError × Nat) γ × AState))
          = .ok (.ok c, lst') := h
      injection h' with h''
      injection h'' with h1 h2
      injection h1 with h1
      subst h2
      exact ⟨b, rfl, h1⟩

/-- `SimStreamD`'s error arm at a wrapper, as the unwrapped run's. -/
theorem StreamErrSim.of_map {β γ : Type} {p : kernel.core_types.CheckError × Std.U64}
    {x : Except Arena.CheckError (Except (Arena.CheckError × Nat) β × AState)} {f : β → γ}
    (h : StreamErrSim p (x >>= fun q => .ok (q.1.map f, q.2))) :
    StreamErrSim p x := by
  intro k hk
  rcases h k hk with ⟨le, lst', hx, hle⟩ | ⟨le, hx, hle⟩
  · left
    revert hx
    rcases x with e | ⟨r, s⟩
    · intro hx; cases hx
    · rcases r with e | b
      · intro hx
        have hx' : (Except.ok (Except.error e, s) :
            Except Arena.CheckError (Except (Arena.CheckError × Nat) γ × AState))
            = .ok (.error (le, absU p.2), lst') := hx
        injection hx' with h1
        injection h1 with h1 h2
        injection h1 with h1
        subst h1; subst h2
        exact ⟨le, s, rfl, hle⟩
      · intro hx; cases hx
  · right
    revert hx
    rcases x with e | ⟨r, s⟩
    · intro hx; cases hx; exact ⟨le, rfl, hle⟩
    · rcases r with e | b <;> (intro hx; cases hx)

/-- `SimStreamD`'s success arm, through a wrapper, as the unwrapped run.  The
hypothesis comes first so that it fixes `x` and `g` before the two `rfl`s are
checked. -/
theorem stream_unwrap_ok {β γ : Type} {x : AM (Except (Arena.CheckError × Nat) β)}
    {g : Except (Arena.CheckError × Nat) β → AM (Except (Arena.CheckError × Nat) γ)}
    {lst lst' : AState} {c : γ}
    (hx : (x >>= g).run lst = .ok (.ok c, lst')) (f : β → γ)
    (h1 : ∀ e, g (.error e) = pure (.error e))
    (h2 : ∀ b, g (.ok b) = pure (.ok (f b))) :
    ∃ b, x.run lst = .ok (.ok b, lst') ∧ f b = c := by
  rw [wrap_map x f h1 h2, stream_run_map] at hx
  exact stream_map_ok hx

/-- The same, at the error arm. -/
theorem stream_unwrap_err {β γ : Type} {x : AM (Except (Arena.CheckError × Nat) β)}
    {g : Except (Arena.CheckError × Nat) β → AM (Except (Arena.CheckError × Nat) γ)}
    {lst : AState} {p : kernel.core_types.CheckError × Std.U64}
    (hx : StreamErrSim p ((x >>= g).run lst)) (f : β → γ)
    (h1 : ∀ e, g (.error e) = pure (.error e))
    (h2 : ∀ b, g (.ok b) = pure (.ok (f b))) :
    StreamErrSim p (x.run lst) := by
  rw [wrap_map x f h1 h2, stream_run_map] at hx
  exact StreamErrSim.of_map hx

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

/-- `USIZE_SIZE` is `USize.size`: `1 << usize::BITS` in `u128`. -/
theorem usize_size_val {x : Std.U128} (h : frontend.export_c.USIZE_SIZE = ok x) :
    x.val = USize.size := by
  rw [frontend.export_c.USIZE_SIZE] at h
  have hb : (core.num.Usize.BITS).val = System.Platform.numBits := by
    simp [core.num.Usize.BITS, UScalarTy.numBits]
  have hy : (core.num.Usize.BITS).val < UScalarTy.numBits .U128 := by
    rw [hb]; simp only [UScalarTy.numBits]
    cases System.Platform.numBits_eq with
    | inl h => rw [h]; omega
    | inr h => rw [h]; omega
  obtain ⟨z, hz, hzv, -⟩ := WP.spec_imp_exists
    (UScalar.ShiftLeft_spec (1#u128 : Std.U128) core.num.Usize.BITS _ hy rfl)
  rw [hz] at h
  cases Result.ok_injective h
  have h1 : (1#u128 : Std.U128).val = 1 := rfl
  rw [hzv, hb, h1]
  simp only [USize.size, UScalar.size, UScalarTy.numBits, Nat.shiftLeft_eq, Nat.one_mul]
  apply Nat.mod_eq_of_lt
  cases System.Platform.numBits_eq with
  | inl h => rw [h]; decide
  | inr h => rw [h]; decide

/-- `as u128` on a `usize` or a `u64`: a widening. -/
theorem cast_u128_val {ty : UScalarTy} {i : UScalar ty} {r : Std.U128}
    (hty : ty.numBits ≤ 64)
    (h : lift (UScalar.cast .U128 i) = ok r) : r.val = i.val := by
  simp only [lift, Result.ok.injEq] at h
  subst h
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have h1 := i.hBounds
  have h2 : 2 ^ ty.numBits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) hty
  have h3 : UScalarTy.numBits .U128 = 128 := rfl
  rw [h3]
  have h4 : (2 : Nat) ^ 64 < 2 ^ 128 := by decide
  omega

theorem usize_numBits_le : UScalarTy.numBits .Usize ≤ 64 := by
  simp only [UScalarTy.numBits]
  cases System.Platform.numBits_eq with
  | inl h => rw [h]; omega
  | inr h => rw [h]

/-- **`CHUNK_SIZE` refines `chunkSize`** (`ExportC.lean:768`). -/
theorem chunk_size_refines {v} (h : frontend.export_c.CHUNK_SIZE = ok v) :
    v.val = chunkSize.toNat := by
  rw [frontend.export_c.CHUNK_SIZE] at h
  obtain ⟨a, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [(ConRon.Refine.Nat.umul_val h).2, (ConRon.Refine.Nat.umul_val ha).2]
  have hc : chunkSize.toNat = 4194304 := by
    simp only [chunkSize]
    cases System.Platform.numBits_eq with
    | inl h32 => simp [USize.toNat_mul, USize.toNat_ofNat, h32]
    | inr h64 => simp [USize.toNat_mul, USize.toNat_ofNat, h64]
  rw [hc]; rfl

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
        | .ok st => pure (.ok (st, ()))) := by
  rw [frontend.export_c.apply_final_line] at h
  obtain ⟨sr, hsr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hS := hsc.scanLineFwd hsr
  simp only [SimStreamD, am_run_bind']
  cases sr with
  | Ok p =>
    obtain ⟨r1, j⟩ := p
    have hscan : ConLeche.Frontend.scanLineFwd (absBytes b) (absPos i) =
        .ok (absLineRec r1) (absPos j) := hS
    obtain ⟨hwf, hnat⟩ := hsc.scanLineStr hsr
    obtain ⟨⟨r2, ar1, st1⟩, hap, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hA := apply_line_refines hmr hrel hinv hd hi hwf hnat hap
    have hrun : (applyFinalLine lmd lsd (absBytes b) (absPos i) (absU line_no)).run lst =
        (applyLine lmd lsd (absLineRec r1)).run lst >>= fun q =>
          (match q.1 with
           | .inr v => (pure (.error (v.toError, absU line_no)) :
                AM (Except (Arena.CheckError × Nat) Arena.Frontend.StateD))
           | .inl st => pure (.ok st)).run q.2 := by
      simp only [applyFinalLine, hscan]
      rfl
    rw [hrun]
    simp only [SimDV] at hA
    cases r2 with
    | Ok u =>
      have ho := Result.ok_injective h; subst ho
      obtain ⟨lsd', lst', hx, hd', hi', hrel', hinv', hext'⟩ := hA
      exact ⟨lsd', lst', by rw [hx]; rfl, hd', hi', hrel', hinv', hext'⟩
    | Err e =>
      obtain ⟨p1, hp1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have ho := Result.ok_injective h; subst ho
      obtain ⟨hpos, herr, hver⟩ := line_err_to_check_refines hp1
      show StreamErrSim p1 _
      cases e with
      | Err ce =>
        intro k hk
        rw [herr ce rfl] at hk
        obtain ⟨le, hx, hle⟩ := hA k hk
        exact Or.inr ⟨le, by rw [hx]; rfl, hle⟩
      | Verdict v =>
        obtain ⟨lv, lst', hx, hkv, -⟩ := hA
        intro k hk
        rw [hver v lv rfl hkv] at hk
        refine Or.inl ⟨lv.toError, lst', ?_, hk⟩
        rw [hx, hpos]; rfl
  | Err e =>
    obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have ho := Result.ok_injective h; subst ho
    obtain ⟨hnone, hsome⟩ := scan_err_to_check_refines hce
    show StreamErrSim (ce, line_no) _
    intro k hk
    cases ht : absErrTag e.what with
    | none => rw [hnone ht] at hk; cases hk
    | some tg =>
      rw [hsome tg ht] at hk
      cases hk
      have hscan : ConLeche.Frontend.scanLineFwd (absBytes b) (absPos i) =
          .err ⟨e.offset.val, tg⟩ := by
        have := (hS : ScanErrSim e _) ⟨e.offset.val, tg⟩ (by rw [absScanErr, ht]; rfl)
        exact this
      refine Or.inl ⟨.internal (ConLeche.Frontend.ScanErr.render
        ⟨e.offset.val - (absPos i).toNat, tg⟩), lst, ?_, rfl⟩
      simp only [applyFinalLine, hscan]
      rfl

/-- **A line the con-leche scanner accepts with a continue position ends at a
newline at or after its start** — `scanLineFwd`'s `0` is exactly "the buffer
ran out before a newline did".  A fact about con-leche's recogniser alone
(task #97-P5-Front): `skipWs` and `scanLineLoop` only move forward, and the
only nonzero continue position is one past a `10` byte.  It is what lets the
port's "scan error, no newline ahead: an incomplete tail" arm agree with the
twin whatever the twin's scanner answers there, `IndexOverflow` included. -/
theorem scanLineFwd_ok_newline {b : ByteArray} {i : USize} {r : LineRec} {j : USize}
    (h : ConLeche.Frontend.scanLineFwd b i = .ok r j) (hj : j ≠ 0) :
    ConLeche.Frontend.newlineFrom b i = true := by sorry

theorem absPos_beq_zero (j : Std.Usize) : (absPos j == 0) = decide (j.val = 0) := by
  by_cases hj : j.val = 0
  · have : absPos j = 0 := by
      apply USize.toNat_inj.mp; rw [absPos_toNat, hj]; rfl
    simp [this, hj]
  · have : absPos j ≠ 0 := by
      intro h0; apply hj; have := congrArg USize.toNat h0; simpa using this
    simp [this, hj]

theorem absPos_lt_iff (i j : Std.Usize) : absPos i < absPos j ↔ i.val < j.val := by
  rw [USize.lt_iff_toNat_lt, absPos_toNat, absPos_toNat]

/-- **`feed_chunk`'s loop refines `feedChunk`** (task #97-P5-Front), unwrapped:
the twin's result already has the `StateD × β` shape `SimStreamD` reads.  By
induction on the bytes left; the step is `apply_line_refines` behind the
scanner's `ScanSpec`, and the three exits are the scanner's error (reported only
when a newline follows), the incomplete tail, and the no-progress guard. -/
theorem feed_chunk_loop_refines {G : Type} {inst : frontend.types.Modeller G}
    {m : G} {lmd : Arena.Frontend.Modeller} {pers} {b : Slice Std.U8}
    (hsc : ScanSpec) (hmr : ModellerRefines inst m lmd) :
    ∀ (i : Std.Usize) (rst : arena.monad.AState) (lst : AState)
      (rsd : frontend.export_c.StateD) (lsd : Arena.Frontend.StateD)
      (line_no : Std.U64) (o),
      AStateRel pers rst lst → AStateInv pers rst → StateDRel rsd lsd → StateDInv rsd →
      frontend.export_c.feed_chunk_loop inst pers m rst rsd b i line_no = ok o →
      SimStreamD (fun p => (absU p.1, absPos p.2)) pers lst o
        (feedChunk lmd lsd (absBytes b) (absPos i) (absU line_no)) := by
  suffices H : ∀ (k : Nat) (i : Std.Usize) (rst : arena.monad.AState) (lst : AState)
      (rsd : frontend.export_c.StateD) (lsd : Arena.Frontend.StateD)
      (line_no : Std.U64) (o),
      b.val.length - i.val = k →
      AStateRel pers rst lst → AStateInv pers rst → StateDRel rsd lsd → StateDInv rsd →
      frontend.export_c.feed_chunk_loop inst pers m rst rsd b i line_no = ok o →
      SimStreamD (fun p => (absU p.1, absPos p.2)) pers lst o
        (feedChunk lmd lsd (absBytes b) (absPos i) (absU line_no)) from
    fun i rst lst rsd lsd line_no o => H _ i rst lst rsd lsd line_no o rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro i rst lst rsd lsd line_no o hk hrel hinv hd hi h
  rw [frontend.export_c.feed_chunk_loop] at h
  simp only [SimStreamD]
  split at h
  · rename_i hlt
    have hlt' : absPos i < (absBytes b).usize := absPos_lt_usize.mpr (by scalar_tac)
    rw [feedChunk, dif_pos hlt']
    obtain ⟨sr, hsr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hS := hsc.scanLineFwd hsr
    cases sr with
    | Ok p =>
      obtain ⟨r1, j⟩ := p
      replace h : ite (j = 0#usize) _ _ = ok o := h
      have hscan : ConLeche.Frontend.scanLineFwd (absBytes b) (absPos i) =
          .ok (absLineRec r1) (absPos j) := hS
      simp only [hscan, absPos_beq_zero]
      split at h
      · rename_i hj0
        have ho := Result.ok_injective h; subst ho
        have : j.val = 0 := by rw [hj0]; rfl
        simp only [this, decide_true, if_true]
        exact ⟨lsd, lst, rfl, hd, hi, hrel, hinv, Ext.refl _⟩
      · rename_i hj0
        have hj0' : ¬ j.val = 0 := fun hv => hj0 (by scalar_tac)
        simp only [hj0', decide_false, Bool.false_eq_true, if_false]
        obtain ⟨hwf, hnat⟩ := hsc.scanLineStr hsr
        obtain ⟨⟨r2, ar1, st1⟩, hap, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hA := apply_line_refines hmr hrel hinv hd hi hwf hnat hap
        simp only [SimDV] at hA
        rw [am_run_bind']
        cases r2 with
        | Ok u =>
          obtain ⟨lsd', lst', hx, hd', hi', hrel', hinv', hext'⟩ := hA
          rw [hx]
          simp only [except_ok_bind]
          split at h
          · rename_i hge
            have hge' : ¬ absPos i < absPos j := by rw [absPos_lt_iff]; scalar_tac
            simp only [dif_neg hge']
            obtain ⟨s, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            obtain ⟨ce, hce, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            have ho := Result.ok_injective h; subst ho
            simp only [kernel.core_types.internal, Result.ok.injEq] at hce
            subst hce
            intro k' hk'
            simp only [absAErrKind_internal, Option.some.injEq] at hk'
            subst hk'
            refine Or.inl ⟨.internal "the line scanner made no progress", lst', ?_, rfl⟩
            rw [absU_add_one hi2]; rfl
          · rename_i hlt2
            have hlt2' : absPos i < absPos j := by rw [absPos_lt_iff]; scalar_tac
            simp only [dif_pos hlt2']
            obtain ⟨line_no1, hl1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            have hR := ih (b.val.length - j.val) (by scalar_tac) j ar1 lst' st1 lsd'
              line_no1 o rfl hrel' hinv' hd' hi' h
            rw [absU_add_one hl1] at hR
            simp only [SimStreamD] at hR
            rcases o with ⟨r3, st3, sd3⟩
            cases r3 with
            | Ok q =>
              obtain ⟨l4, s4, hx4, hd4, hi4, hr4, hv4, he4⟩ := hR
              exact ⟨l4, s4, hx4, hd4, hi4, hr4, hv4, Ext.trans hext' he4⟩
            | Err p => exact hR
        | Err e =>
          obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          obtain ⟨p1, hp1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have ho := Result.ok_injective h; subst ho
          obtain ⟨hpos, herr, hver⟩ := line_err_to_check_refines hp1
          rw [absU_add_one hi2] at hpos
          show StreamErrSim p1 _
          cases e with
          | Err ce =>
            intro k' hk'
            rw [herr ce rfl] at hk'
            obtain ⟨le, hx, hle⟩ := hA k' hk'
            exact Or.inr ⟨le, by rw [hx]; rfl, hle⟩
          | Verdict v =>
            obtain ⟨lv, lst', hx, hkv, -⟩ := hA
            intro k' hk'
            rw [hver v lv rfl hkv] at hk'
            refine Or.inl ⟨lv.toError, lst', ?_, hk'⟩
            rw [hx, hpos]; rfl
    | Err e =>
      simp only at h
      obtain ⟨nl, hnl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hnl' := hsc.newlineFrom hnl
      split at h
      · rename_i hnlt
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨ce, hce, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have ho := Result.ok_injective h; subst ho
        obtain ⟨hnone, hsome⟩ := scan_err_to_check_refines hce
        show StreamErrSim (ce, i3) _
        intro k' hk'
        cases ht : absErrTag e.what with
        | none => rw [hnone ht] at hk'; cases hk'
        | some tg =>
          rw [hsome tg ht] at hk'
          cases hk'
          have hscan : ConLeche.Frontend.scanLineFwd (absBytes b) (absPos i) =
              .err ⟨e.offset.val, tg⟩ :=
            (hS : ScanErrSim e _) ⟨e.offset.val, tg⟩ (by rw [absScanErr, ht]; rfl)
          have hnlt' : ConLeche.Frontend.newlineFrom (absBytes b) (absPos i) = true := by
            rw [← hnl']; exact hnlt
          refine Or.inl ⟨.internal (ConLeche.Frontend.ScanErr.render
            ⟨e.offset.val - (absPos i).toNat, tg⟩), lst, ?_, rfl⟩
          simp only [hscan, hnlt', if_true]
          rw [absU_add_one hi3]; rfl
      · rename_i hnlf
        have ho := Result.ok_injective h; subst ho
        have hnlf' : ConLeche.Frontend.newlineFrom (absBytes b) (absPos i) = false := by
          rw [← hnl']; simpa using hnlf
        -- the twin: whatever its scanner answers here, with no newline ahead the
        -- line is an incomplete tail (`scanLineFwd_ok_newline`)
        refine ⟨lsd, lst, ?_, hd, hi, hrel, hinv, Ext.refl _⟩
        cases hsc2 : ConLeche.Frontend.scanLineFwd (absBytes b) (absPos i) with
        | err se =>
          simp only [hnlf', Bool.false_eq_true, if_false]
          rfl
        | ok r j =>
          by_cases hj : j = 0
          · simp only [hj, beq_self_eq_true, if_true]
            rfl
          · have := scanLineFwd_ok_newline hsc2 hj
            rw [hnlf'] at this; cases this
  · rename_i hge
    have hge' : ¬ absPos i < (absBytes b).usize := by
      rw [absPos_lt_usize]; scalar_tac
    have ho := Result.ok_injective h; subst ho
    rw [feedChunk, dif_neg hge']
    exact ⟨lsd, lst, rfl, hd, hi, hrel, hinv, Ext.refl _⟩

/-- A wrapper that reshapes nothing: `SimStreamD` goes through it. -/
theorem SimStreamD.of_wrap_id {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {lst : AState}
    {o : core.result.Result α (kernel.core_types.CheckError × Std.U64) ×
      arena.monad.AState × frontend.export_c.StateD}
    {x : AM (Except (Arena.CheckError × Nat) (Arena.Frontend.StateD × β))}
    {g : Except (Arena.CheckError × Nat) (Arena.Frontend.StateD × β) →
      AM (Except (Arena.CheckError × Nat) (Arena.Frontend.StateD × β))}
    (hx : SimStreamD A pers lst o x)
    (h1 : ∀ e, g (.error e) = pure (.error e)) (h2 : ∀ b, g (.ok b) = pure (.ok b)) :
    SimStreamD A pers lst o (x >>= g) := by
  have hw : x >>= g = x := by
    rw [wrap_map x id h1 h2]
    conv => rhs; rw [← bind_pure x]
    congr 1; funext r; cases r <;> rfl
  rw [hw]; exact hx

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
        | .ok (st, n, j) => pure (.ok (st, (n, j)))) := by
  have hL := feed_chunk_loop_refines hsc hmr i rst lst rsd lsd line_no o hrel hinv hd hi h
  refine SimStreamD.of_wrap_id hL ?_ ?_
  · intro e; rfl
  · intro q; rfl

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
      else pure (.ok (ParseResultD.ofState lsd))) := by
  rw [frontend.export_c.parse_bytes_final] at h
  simp only [SimStreamRel]
  split at h
  · rename_i hlt
    have hlt' : absPos tail < (absBytes b).usize := absPos_lt_usize.mpr (by scalar_tac)
    rw [if_pos hlt']
    obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨r, ar1, st1⟩, hap, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hA := apply_final_line_refines hsc hmr hrel hinv hd hi hap
    have hl : absU i1 = absU line_no + 1 := absU_add_one hi1
    rw [hl] at hA
    simp only [SimStreamD] at hA
    rw [am_run_bind']
    cases r with
    | Ok u =>
      simp only at hA
      obtain ⟨prd, hprd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have ho := Result.ok_injective h; subst ho
      obtain ⟨lsd', lst', hx, hd', hi', hrel', hinv', hext'⟩ := hA
      obtain ⟨b', hb, hfb⟩ := stream_unwrap_ok hx (fun st => (st, ())) (fun _ => rfl)
        (fun _ => rfl)
      simp only [Prod.mk.injEq] at hfb
      obtain ⟨rfl, -⟩ := hfb
      refine ⟨ParseResultD.ofState b', lst', ?_, parse_result_of_state_refines hd' hprd,
        hrel', hinv', hext'⟩
      rw [hb]; rfl
    | Err e =>
      simp only at hA
      have ho := Result.ok_injective h; subst ho
      have hA' := stream_unwrap_err hA (fun st => (st, ())) (fun _ => rfl) (fun _ => rfl)
      exact StreamErrSim.bind hA' _ (fun _ _ => rfl)
  · rename_i hge
    have hge' : ¬ absPos tail < (absBytes b).usize := by
      rw [absPos_lt_usize]; scalar_tac
    rw [if_neg hge']
    obtain ⟨prd, hprd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have ho := Result.ok_injective h; subst ho
    exact ⟨ParseResultD.ofState lsd, lst, rfl, parse_result_of_state_refines hd hprd,
      hrel, hinv, Ext.refl _⟩

/-- **`parse_bytes` refines `parseBytes`** (`ExportC.lean:779-790`) —
wholesale direct parse of a byte buffer, the specification the streaming parse
is proved equal to. -/
theorem parse_bytes_refines {G : Type} {inst : frontend.types.Modeller G}
    {m : G} {lmd : Arena.Frontend.Modeller} {pers rst lst b in_model census o}
    (hsc : ScanSpec) (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.export_c.parse_bytes inst pers m rst b in_model census = ok o) :
    SimStreamRel ParseResultDRel pers lst o
      (parseBytes lmd (absBytes b) in_model census) := by
  rw [frontend.export_c.parse_bytes] at h
  obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hv1 : i1.val = b.val.length := by
    rw [cast_u128_val usize_numBits_le hi1]; simp
  have hv2 := usize_size_val hi2
  have hlt : b.val.length < USize.size := by
    have := absBytes_usize b
    have := (absBytes b).usize.toNat_lt_size
    simp_all
  split at h
  · rename_i hge; exfalso; scalar_tac
  have hsz : ¬ (absBytes b).size ≥ USize.size := by rw [absBytes_size]; omega
  obtain ⟨⟨r, e⟩, hs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hS := state_d_init_refines hrel hinv hs
  simp only [SimRel] at hS
  simp only [SimStreamRel, parseBytes, hsz, if_false, am_run_bind']
  simp only [except_pure_bind, StateT.run_pure]
  cases r with
  | Err e1 =>
    have ho := Result.ok_injective h; subst ho
    exact StreamErrSim.of_throw (n := 0#u64) hS
  | Ok v =>
    try simp only at h
    obtain ⟨lsd, lst1, hx1, ⟨hd1, hi1'⟩, hrel1, hinv1, hext1⟩ := hS
    rw [hx1]
    simp only [except_ok_bind]
    obtain ⟨⟨r1, ar1, v1⟩, hf, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hF := feed_chunk_refines hsc hmr hrel1 hinv1 hd1 hi1' hf
    simp only [SimStreamD] at hF
    have h00 : absPos 0#usize = 0 := rfl
    have h00' : absU 0#u64 = 0 := rfl
    rw [h00, h00'] at hF
    cases r1 with
    | Ok p =>
      obtain ⟨line_no, tail⟩ := p
      obtain ⟨lsd', lst', hx, hd', hi', hrel', hinv', hext'⟩ := hF
      obtain ⟨⟨st2, n2, j2⟩, hb, hfb⟩ := stream_unwrap_ok hx (fun q => (q.1, q.2.1, q.2.2))
        (fun _ => rfl) (fun _ => rfl)
      simp only [Prod.mk.injEq] at hfb
      obtain ⟨rfl, rfl, rfl⟩ := hfb
      have hP := parse_bytes_final_refines hsc hmr hrel' hinv' hd' hi' h
      simp only [SimStreamRel] at hP ⊢
      rw [hb]
      simp only [except_ok_bind]
      rcases o with ⟨r2, st'⟩
      cases r2 with
      | Ok r =>
        obtain ⟨v, l2, hx2, hR, hr2, hi2, he2⟩ := hP
        exact ⟨v, l2, hx2, hR, hr2, hi2, Ext.trans (Ext.trans hext1 hext') he2⟩
      | Err p => exact hP
    | Err p =>
      have ho := Result.ok_injective h; subst ho
      have hF' := stream_unwrap_err hF (fun q => (q.1, q.2.1, q.2.2)) (fun _ => rfl) (fun _ => rfl)
      exact StreamErrSim.bind hF' _ (fun _ _ => rfl)

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

/-! ### Byte vectors (task #97-P5-Front) -/

theorem clone_u8 : ∀ x : Std.U8, core.clone.CloneU8.clone x = ok x := fun _ => rfl

theorem to_vec_u8_val {s : Slice Std.U8} {v : alloc.vec.Vec Std.U8}
    (h : alloc.slice.Slice.to_vec core.clone.CloneU8 s = ok v) : v.val = s.val := by
  obtain ⟨v', hv', hs⟩ := WP.spec_imp_exists
    (alloc.slice.Slice.to_vec_spec core.clone.CloneU8 s (fun x _ => clone_u8 x))
  rw [hv'] at h
  cases Result.ok_injective h
  rw [hs]; rfl

theorem extend_u8_val {v w : alloc.vec.Vec Std.U8} {s : Slice Std.U8}
    (h : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s = ok w) :
    w.val = v.val ++ s.val := by
  obtain ⟨s', hs', hss⟩ := WP.spec_imp_exists
    (Slice.clone_spec (clone := core.clone.CloneU8.clone) (s := s) (fun x _ => clone_u8 x))
  unfold alloc.vec.Vec.extend_from_slice at h
  split at h
  · split at h
    · rename_i s'' hm
      simp only [Result.ok.injEq] at h
      subst h
      have : Slice.clone core.clone.CloneU8.clone s = ok s'' := by simpa using hm
      rw [hs'] at this
      cases Result.ok_injective this
      simp [hss]
    · simp at h
    · simp at h
  · simp at h

theorem range_from_val {v : alloc.vec.Vec Std.U8} {t : Std.Usize} {s : Slice Std.U8}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) v
      { start := t } = ok s) :
    s.val = v.val.drop t.val ∧ t.val ≤ v.val.length := by
  simp only [alloc.vec.Vec.index,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index] at h
  split at h
  · rename_i hle
    cases Result.ok_injective h
    exact ⟨by simp; rfl, hle⟩
  · simp at h

/-- A `Vec<u8>` read through `[..]` is its own bytes. -/
theorem vec_index_full {v : alloc.vec.Vec Std.U8} {s : Slice Std.U8}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFullSlice Std.U8) v () = ok s) :
    absBytes s = absChunk v := by
  simp only [alloc.vec.Vec.index,
    core.slice.index.SliceIndexRangeFullSlice.index, Result.ok.injEq] at h
  subst h
  rfl

@[simp] theorem absChunk_size (c : alloc.vec.Vec Std.U8) :
    (absChunk c).size = c.val.length := by
  simp [absChunk, ByteArray.size]

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
        | .ok (st, c, n, t) => pure (.ok (st, (c, n, t)))) := by
  refine SimStreamD.of_wrap_id ?_ (fun _ => rfl) (fun _ => rfl)
  rw [frontend.export_c.chunk_step] at h
  obtain ⟨i0, hi0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i4, hi4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have e0 : i0.val = total.val := cast_u128_val (by decide) hi0
  have e2 : i2.val = buf0.val.length := by
    rw [cast_u128_val usize_numBits_le hi2]; simp
  have e3 : i3.val = i0.val + i2.val := ConRon.Refine.Nat.uadd_val hi3
  have e4 := usize_size_val hi4
  simp only [SimStreamD, chunkStep]
  split at h
  · rename_i hge
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have ho := Result.ok_injective h; subst ho
    have hge' : absU total + (absBytes buf0).size ≥ USize.size := by
      rw [absBytes_size]; simp only [absU]; scalar_tac
    rw [if_pos hge']
    have hk := size_error_refines hp
    intro k hk'
    rw [hk.1] at hk'
    exact Or.inl ⟨sizeError.1, lst, by rw [hk.2]; rfl, hk'⟩
  · rename_i hlt
    have hlt' : ¬ absU total + (absBytes buf0).size ≥ USize.size := by
      rw [absBytes_size]; simp only [absU]; scalar_tac
    rw [if_neg hlt']
    obtain ⟨buf, hbuf, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨s, hs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨r, ar1, st1⟩, hf, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbufv : absChunk buf =
        (if (absChunk carry).isEmpty then absBytes buf0 else absChunk carry ++ absBytes buf0) := by
      split at hbuf
      · rename_i h0
        have hv := to_vec_u8_val hbuf
        have hc : carry.val.length = 0 := by scalar_tac
        have : (absChunk carry).isEmpty = true := by
          simp only [ByteArray.isEmpty, absChunk_size]; simp [hc]
        rw [if_pos this]
        simp only [absChunk, absBytes, hv]
      · rename_i h0
        have hv := extend_u8_val hbuf
        have hc : carry.val.length ≠ 0 := by scalar_tac
        have : (absChunk carry).isEmpty = false := by
          simp only [ByteArray.isEmpty, absChunk_size]; simp [hc]
        rw [if_neg (by simp [this])]
        apply ByteArray.ext
        simp [absChunk, absBytes, hv, ByteArray.data_append]
    rw [← hbufv]
    have hF := feed_chunk_loop_refines hsc hmr 0#usize rst lst rsd lsd line_no _ hrel hinv hd hi hf
    rw [vec_index_full hs] at hF
    have h00 : absPos 0#usize = 0 := rfl
    rw [h00] at hF
    simp only [SimStreamD] at hF
    simp only [am_run_bind', StateT.run_pure, except_pure_bind]
    cases r with
    | Ok p =>
      obtain ⟨line_no2, tail⟩ := p
      obtain ⟨lsd', lst', hx, hd', hi', hrel', hinv', hext'⟩ := hF
      rw [hx]
      obtain ⟨s1, hs1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i7, hi7, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i8, hi8, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have ho := Result.ok_injective h; subst ho
      obtain ⟨hs1v, htl⟩ := range_from_val hs1
      have hvv := to_vec_u8_val hv
      have e7 : i7.val = buf0.val.length := by rw [cast_u64_usize hi7]; simp
      have e8 : i8.val = total.val + i7.val := ConRon.Refine.Nat.uadd_val hi8
      have hE : (absChunk buf).extract (absPos tail).toNat (absChunk buf).size =
          absChunk v := by
        apply ByteArray.ext
        simp [absChunk, hvv, hs1v, ByteArray.data_extract, List.map_drop]
        simp [ByteArray.size]; omega
      have hN : absU total + (absBytes buf0).size = absU i8 := by
        simp only [absU, e8, e7, absBytes_size]
      refine ⟨lsd', lst', ?_, hd', hi', hrel', hinv', hext'⟩
      simp only [except_ok_bind]
      rw [hE, hN]
      rfl
    | Err e =>
      have ho := Result.ok_injective h; subst ho
      exact StreamErrSim.bind hF _ (fun _ _ => rfl)

/-- **`chunk_finish` refines `chunkFinish`** (`ExportC.lean:815-820`) — the end
of the stream: the carried tail, if any, is its last line. -/
theorem chunk_finish_refines {G : Type} {inst : frontend.types.Modeller G}
    {m : G} {lmd : Arena.Frontend.Modeller} {pers rst lst rsd lsd carry line_no o}
    (hsc : ScanSpec) (hmr : ModellerRefines inst m lmd)
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hd : StateDRel rsd lsd) (hi : StateDInv rsd)
    (h : frontend.export_c.chunk_finish inst pers m rst rsd carry line_no = ok o) :
    SimStreamRel ParseResultDRel pers lst o
      (chunkFinish lmd lsd (absBytes carry) (absU line_no)) := by
  rw [frontend.export_c.chunk_finish] at h
  simp only [SimStreamRel]
  split at h
  · rename_i hlen
    obtain ⟨prd, hprd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have ho := Result.ok_injective h; subst ho
    have hempty : (absBytes carry).isEmpty = true := by
      simp only [ByteArray.isEmpty, absBytes_size]
      have : carry.val.length = 0 := by scalar_tac
      simp [this]
    refine ⟨ParseResultD.ofState lsd, lst, ?_, parse_result_of_state_refines hd hprd,
      hrel, hinv, Ext.refl _⟩
    simp only [chunkFinish, hempty]
    rfl
  · rename_i hlen
    have hne : (absBytes carry).isEmpty = false := by
      simp only [ByteArray.isEmpty, absBytes_size]
      have : carry.val.length ≠ 0 := by scalar_tac
      simp [this]
    obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨r, ar1, st1⟩, hap, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hA := apply_final_line_refines hsc hmr hrel hinv hd hi hap
    have hl : absU i1 = absU line_no + 1 := absU_add_one hi1
    have h0 : absPos 0#usize = 0 := rfl
    rw [hl, h0] at hA
    have hrun : (chunkFinish lmd lsd (absBytes carry) (absU line_no)).run lst =
        (applyFinalLine lmd lsd (absBytes carry) 0 (absU line_no + 1)).run lst >>=
          fun p => (match p.1 with
            | .error e => (pure (.error e) : AM (Except (Arena.CheckError × Nat) ParseResultD))
            | .ok st => pure (.ok (.ofState st))).run p.2 := by
      simp only [chunkFinish, hne]
      rfl
    rw [hrun]
    simp only [SimStreamD] at hA
    cases r with
    | Ok u =>
      simp only at hA
      obtain ⟨prd, hprd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have ho := Result.ok_injective h; subst ho
      obtain ⟨lsd', lst', hx, hd', hi', hrel', hinv', hext'⟩ := hA
      obtain ⟨b, hb, hfb⟩ := stream_unwrap_ok hx (fun st => (st, ())) (fun _ => rfl)
        (fun _ => rfl)
      simp only [Prod.mk.injEq] at hfb
      obtain ⟨rfl, -⟩ := hfb
      refine ⟨ParseResultD.ofState b, lst', ?_, parse_result_of_state_refines hd' hprd,
        hrel', hinv', hext'⟩
      rw [hb]; rfl
    | Err e =>
      simp only at hA
      have ho := Result.ok_injective h; subst ho
      have hA' : StreamErrSim e
          ((applyFinalLine lmd lsd (absBytes carry) 0 (absU line_no + 1)).run lst) :=
        stream_unwrap_err hA (fun st => (st, ())) (fun _ => rfl) (fun _ => rfl)
      exact StreamErrSim.bind hA' _ (fun _ _ => rfl)

/-! ## The tier's first top statement -/

/-- **`parse_chunks`'s loop refines `parseChunksGo`** (task #97-P5-Front) —
from chunk `i`, the twin's fold over the chunks not yet read.  The loop the
Rust's `while i < n` becomes under `-loops-to-rec`; its step is
`chunk_step_refines` and its exit `chunk_finish_refines`. -/
theorem parse_chunks_loop_refines {G : Type} {inst : frontend.types.Modeller G}
    {m : G} {lmd : Arena.Frontend.Modeller} {pers chunks}
    (hsc : ScanSpec) (hmr : ModellerRefines inst m lmd) :
    ∀ (i : Std.Usize) (rst : arena.monad.AState) (lst : AState)
      (rsd : frontend.export_c.StateD) (lsd : Arena.Frontend.StateD)
      (carry : alloc.vec.Vec Std.U8) (line_no total : Std.U64) (o),
      AStateRel pers rst lst → AStateInv pers rst → StateDRel rsd lsd → StateDInv rsd →
      frontend.export_c.parse_chunks_loop inst pers m rst chunks rsd carry line_no total
        (alloc.vec.Vec.len chunks) i = ok o →
      SimStreamRel ParseResultDRel pers lst o
        (parseChunksGo lmd lsd (absChunk carry) (absU line_no) (absU total)
          ((absChunks chunks).drop i.val)) := by
  suffices H : ∀ (k : Nat) (i : Std.Usize) (rst : arena.monad.AState) (lst : AState)
      (rsd : frontend.export_c.StateD) (lsd : Arena.Frontend.StateD)
      (carry : alloc.vec.Vec Std.U8) (line_no total : Std.U64) (o),
      chunks.val.length - i.val = k →
      AStateRel pers rst lst → AStateInv pers rst → StateDRel rsd lsd → StateDInv rsd →
      frontend.export_c.parse_chunks_loop inst pers m rst chunks rsd carry line_no total
        (alloc.vec.Vec.len chunks) i = ok o →
      SimStreamRel ParseResultDRel pers lst o
        (parseChunksGo lmd lsd (absChunk carry) (absU line_no) (absU total)
          ((absChunks chunks).drop i.val)) from
    fun i rst lst rsd lsd carry line_no total o => H _ i rst lst rsd lsd carry line_no total o rfl
  intro k
  induction k with
  | zero =>
    intro i rst lst rsd lsd carry line_no total o hk hrel hinv hd hi h
    rw [frontend.export_c.parse_chunks_loop] at h
    rw [if_neg (by scalar_tac)] at h
    obtain ⟨s, hs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hF := chunk_finish_refines hsc hmr hrel hinv hd hi h
    rw [vec_index_full hs] at hF
    have hnil : (absChunks chunks).drop i.val = [] := by
      simp only [absChunks, List.drop_eq_nil_iff, List.length_map]; omega
    rw [hnil]
    exact hF
  | succ k ih =>
    intro i rst lst rsd lsd carry line_no total o hk hrel hinv hd hi h
    rw [frontend.export_c.parse_chunks_loop] at h
    rw [if_pos (by scalar_tac)] at h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨s, hs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨r, ar1, st1⟩, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hC := chunk_step_refines hsc hmr hrel hinv hd hi hc
    rw [vec_index_full hs] at hC
    have hvi := vec_index_some hv
    have hcons : (absChunks chunks).drop i.val =
        absChunk v :: (absChunks chunks).drop (i.val + 1) := by
      simp only [absChunks]
      rw [List.drop_eq_getElem_cons (by simp; scalar_tac)]
      simp only [List.getElem_map]
      have := List.getElem?_eq_some_iff.mp hvi
      obtain ⟨_, hx⟩ := this
      rw [hx]
    rw [hcons]
    simp only [SimStreamD] at hC
    simp only [SimStreamRel, parseChunksGo, am_run_bind']
    cases r with
    | Ok t =>
      obtain ⟨c2, l, t1⟩ := t
      obtain ⟨lsd', lst', hx, hd', hi', hrel', hinv', hext'⟩ := hC
      obtain ⟨⟨st2, c3, n3, t3⟩, hb, hfb⟩ := stream_unwrap_ok hx
        (fun q => (q.1, q.2.1, q.2.2.1, q.2.2.2)) (fun _ => rfl) (fun _ => rfl)
      simp only [Prod.mk.injEq] at hfb
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hfb
      obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi1v : i1.val = i.val + 1 := usize_add_one_inv hi1
      have hR := ih i1 ar1 lst' st1 st2 c2 l t1 o (by omega) hrel' hinv' hd' hi' h
      rw [hi1v] at hR
      rw [hb]
      simp only [except_ok_bind]
      simp only [SimStreamRel] at hR
      rcases o with ⟨r2, st'⟩
      cases r2 with
      | Ok r =>
        obtain ⟨w, l2, hx2, hR2, hr2, hi2, he2⟩ := hR
        exact ⟨w, l2, hx2, hR2, hr2, hi2, Ext.trans hext' he2⟩
      | Err p => exact hR
    | Err e =>
      have ho := Result.ok_injective h; subst ho
      have hC' := stream_unwrap_err hC (fun q => (q.1, q.2.1, q.2.2.1, q.2.2.2))
        (fun _ => rfl) (fun _ => rfl)
      exact StreamErrSim.bind hC' _ (fun _ _ => rfl)

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
      (parseChunks lmd (absChunks chunks) in_model census) := by
  rw [frontend.export_c.parse_chunks] at h
  obtain ⟨⟨r, e⟩, hs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hS := state_d_init_refines hrel hinv hs
  simp only [SimRel] at hS
  simp only [SimStreamRel, parseChunks, am_run_bind']
  cases r with
  | Err e1 =>
    have ho := Result.ok_injective h; subst ho
    exact StreamErrSim.of_throw (n := 0#u64) hS
  | Ok v =>
    obtain ⟨lsd, lst1, hx1, ⟨hd1, hi1⟩, hrel1, hinv1, hext1⟩ := hS
    rw [hx1]
    simp only [except_ok_bind]
    have hL := parse_chunks_loop_refines hsc hmr 0#usize (withStore rst e) lst1 v lsd
      (alloc.vec.Vec.new Std.U8) 0#u64 0#u64 o hrel1 hinv1 hd1 hi1 h
    have hc : absChunk (alloc.vec.Vec.new Std.U8) = .empty := rfl
    have h0 : absU (0#u64) = 0 := rfl
    rw [hc, h0] at hL
    simp only [SimStreamRel] at hL
    rcases o with ⟨r2, st'⟩
    cases r2 with
    | Ok r =>
      obtain ⟨w, l2, hx2, hR2, hr2, hi2, he2⟩ := hL
      exact ⟨w, l2, hx2, hR2, hr2, hi2, Ext.trans hext1 he2⟩
    | Err p => exact hL

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
    SimStream absPreludeIx pers lst o (builtinPreludeE lmd) := by
  rw [frontend.prelude.builtin_prelude_e] at h
  obtain ⟨text, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r, ar1⟩, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hP := parse_bytes_refines hsc hmr hrel hinv hp
  have htext : absBytes (alloc.vec.Vec.deref text) = preludeText := by
    rw [← builtin_prelude_text_refines ht]; simp [absBytes, absChunk, alloc.vec.Vec.deref]
  rw [htext] at hP
  simp only [SimStreamRel] at hP ⊢
  simp only [builtinPreludeE, am_run_bind']
  cases r with
  | Ok r1 =>
    have ho := Result.ok_injective h; subst ho
    obtain ⟨v, lst', hx, hR, hrel', hinv', hext'⟩ := hP
    refine ⟨absPreludeIx { decls := r1.decls }, lst', ?_, rfl, hrel', hinv', hext'⟩
    rw [hx]
    simp only [except_ok_bind, absPreludeIx, hR.decls]
    rfl
  | Err e =>
    have ho := Result.ok_injective h; subst ho
    exact StreamErrSim.bind hP _ (fun _ _ => rfl)

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

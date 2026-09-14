/-
`ConRon.Refine.Frontend.ChunksR` — **the top of the parse, exact against
con-leche** (task #87, phase 3).

Phase 1's `ConRon/Refine/Frontend/Chunks.lean` proved the port's parser *well
formed* — `apply_line_wf`, `feed_chunk_wf`, `parse_bytes_wf`,
`parse_chunks_wf`, `builtin_prelude_e_wf`, statements about the port alone.
This file proves the same five functions **exact**: for the same bytes the
port's parse is con-leche's `parseChunks` of the abstracted chunks, and it
fails where con-leche fails.

Port: `crates/con-ron-core/src/frontend/export_c.rs:2399-2710` and
`crates/con-ron-core/src/frontend/prelude.rs`.
con-leche: `ConLeche/Frontend/ExportC.lean:732-935` and
`ConLeche/Frontend/Prelude.lean`.

## What this file gives the rest of the tier

* `ModellerRefines` — **the canonical hypothesis about the unverified
  modeller**, the exactness twin of `Frontend.ModellerWF`
  (`Refine/Frontend/Base.lean`).
* `absParseResultD` — `export_c::ParseResultD` as con-leche's — and
  `ParseResultSim`, the relation actually claimed of it.
* `ParseErrSim` / `ParseSim` — the parse tier's outcome vocabulary, over
  `Except (CheckError × Nat)`, in the shape `Refine/Abs.lean`'s
  `ErrSim`/`OutP` fixed for the checker.
* `ApplyLineSim` — `Refine/Frontend/StateDR.lean`'s `LineOutV` with the state
  carried out of the port's `&mut` argument rather than out of the value.
* `ParseIngredients R inst g` — the lower tier's lemmas as named `Prop`s, one
  field per lemma, in the shape `Refine/IndSpec.lean` fixed at task #56.
* `parse_chunks_refines` — **the lemma the whole task's headline composes
  with** — and `builtin_prelude_e_refines`, its prelude twin.

## The one use of con-leche's `Scan/Equiv` tier

con-leche's `applyFinalLine` and `feedChunk` read lines with `scanLineSpec`,
the naive reference of `ConLeche/Frontend/Scan/Naive.lean`; a `@[csimp]`,
`ConLeche.Frontend.scanLineSpec_eq_scanLineFwd`
(`ConLeche/Frontend/Scan/Equiv.lean:1002`), makes `scanLineFwd` what the
*compiler* runs, and the port is a port of `scanLineFwd`.  The equation is
used in **one** lemma, `scanLineSpec_eq_fwd` below, whose only users are
`applyFinalLine_eq` and `feedChunk_eq` — the two unfolding lemmas every other
proof in this file goes through.  That is the only use of con-leche's whole
`Scan/Equiv` tier in the port's proof.

## The port's own reader failure, and the port bug it turned up

`scan_types::ErrTag::IndexOverflow` is con-ron's own tag (`scan_types.rs`'s
module note, deviation 1; `Refine/Frontend/Abs.lean`'s note): the port reads a
stream index into a `u64` and refuses one that does not fit, where con-leche
reads a `Nat` and cannot fail.  `absErrTag` sends it to `none`, so
`ScanErrSim` claims nothing there.

Above the scanner that was **not** free.  `apply_final_line` and `feed_chunk`
used to render every reader failure with `core_types::internal(…)`, and
`absErrKind (Internal _) = some .internal`: the `.Err` half of this file's
lemmas would then have asserted that con-leche throws, which for an
`IndexOverflow` is false — con-leche's reader returns `.ok` on the same bytes.
Task #87 fixed the port (`export_c::scan_err_to_check`, which spells an
`IndexOverflow` as `core_types::native(…)` and every other tag as
`internal(…)`), and the error halves below are unconditional again.

What the **accept** direction still needs is one fact about the reader, and it
is a `ParseIngredients` field: `scan_line_fwd_tail`, *"a reader failure with no
newline ahead is an incomplete tail for con-leche's reader too"*.  `feed_chunk`
answers `Ok (line_no, i)` there — the bytes are a cut line, not a malformed one
— and con-leche's `feedChunk` answers `(st, lineNo, i)` whether its own reader
failed or stopped at `0`.  Without it the port's own `IndexOverflow` could hide
a disagreement in the accept direction as well.

## `sorry` count in this file: 0
-/
import ConRon.Refine.Frontend.StateDR
import ConRon.Refine.Frontend.Abs
import ConRon.Refine.HashMapWF
import ConLeche.Frontend.Prelude
import ConLeche.Frontend.Scan.Equiv

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

/-! ## The unverified modeller, exactly

`Frontend.ModellerWF` (`Refine/Frontend/Base.lean`) is phase 1's one line
about `in_model_rec::Modeller`: whatever `generate` returns is well formed.
This is its phase-3 twin: whatever `generate` returns is what
`ConLeche.Frontend.InModel.generate` returns.

The block is abstracted by `Refine/Frontend/StateDR.lean`'s `absBlockRec`; the
**context** is not.  The port's `ModelCtx` holds three `ron::HashMap`s and
con-leche's `InModel.Ctx` three *functions* (`InModel/Mutual.lean:103-108`),
so the bridge is a relation, and it is built out of the parse state —
`export_c::state_model_ctx` against con-leche's inline
`{ tbl := fun n => st.constTypes[n]?, … }` (`ExportC.lean:603-607`).  That
relation belongs with `StateDRel`, so `ModellerRefines` takes it as a
parameter and this file never names a field of either context. -/

/-- **The residue, exactly** (DESIGN.md §3's ruling of 2026-09-13: *"leave the
modeller unverified if you can; rumors are that upstream can actually get rid
of it"*).  The exactness twin of `Frontend.ModellerWF`: at related contexts and
the same block, `in_model_rec::Modeller::generate` returns what
`ConLeche.Frontend.InModel.generate` (`ConLeche/Frontend/InModel.lean:39-45`)
returns, and declines where it declines.

The decline's *text* is not compared — the port carries `Vec<u32>` code points
and con-leche a `String`, and DESIGN.md §3.1's ruling is that message strings
never are.  Like `ModellerWF` it is a promise about a *function argument*, and
it disappears the day upstream drops the modeller. -/
def ModellerRefines {G : Type} (inst : frontend.in_model_rec.Modeller G) (g : G)
    (CtxRel : frontend.in_model_rec.ModelCtx →
      ConLeche.Frontend.InModel.Ctx → Prop) : Prop :=
  ∀ ctx lctx b o, CtxRel ctx lctx → inst.generate g ctx b = ok o →
    (∀ ds, o = .Ok ds →
      ConLeche.Frontend.InModel.generate lctx (absBlockRec b)
        = .ok (ds.val.map absDeclaration)) ∧
    (∀ m, o = .Err m →
      ∃ s, ConLeche.Frontend.InModel.generate lctx (absBlockRec b) = .error s)

/-! ## The parse result

`export_c::ParseResultD` has **six** fields against con-leche's **seven**
(`ExportC.lean:730-753`).  con-leche's `inModelGen` — *"the in-process
modeller's generated records per block, keyed by the block's ordinal among the
stream's `inductive` records (for the debug dump only)"* — has no port
counterpart at all (`export_c.rs`'s `StateD` note: *"`inModelGen`, the debug
dump's field, is not ported"*, the same field `StateDRel` leaves
unconstrained), so **`absParseResultD` puts `#[]` there**.  That is this
file's one abstraction deviation, and `ParseResultSim` carries no clause for
the field. -/

/-- The census's declines, names and reasons (`ExportC.lean:752-753`). -/
def absInModelDeclined (v : alloc.vec.Vec (name.Name × alloc.vec.Vec Std.U32)) :
    List (ConLeche.Name × String) :=
  v.val.map fun p => (absName p.1, absString p.2)

/-- **`export_c::ParseResultD` as con-leche's** (`ExportC.lean:730-753`), field
for field, with `inModelGen := #[]` — the debug dump's field, which the port
does not have. -/
def absParseResultD (r : frontend.export_c.ParseResultD) :
    ConLeche.Frontend.ParseResultD :=
  { decls := (r.decls.val.map absDeclaration).toArray
    projRewrites := (absNames r.proj_rewrites).toArray
    inModelled := (absNames r.in_modelled).toArray
    genRecords := r.gen_records.val
    genOwner := Std.HashMap.ofList
      ((HashMap.al_v r.gen_owner).map fun p => (absName p.1, absName p.2))
    inModelGen := #[]
    inModelDeclined := (absInModelDeclined r.in_model_declined).toArray }

/-- **What a parse result claims**, field by field.

Four fields are claimed exactly.  `genOwner` is a `ron::HashMap` against a
`Std.HashMap` and is claimed the way `Refine/FEnv.lean` claims its index — by
`HashMap.RelOn`, lookup for lookup, which is all a hash table can be compared
at.  `inModelDeclined` pairs a name with a *reason*, and reasons are never
compared (DESIGN.md §3.1), so only the names are.  `inModelGen` has no clause:
the port has no such field. -/
structure ParseResultSim (r : frontend.export_c.ParseResultD)
    (x : ConLeche.Frontend.ParseResultD) : Prop where
  decls : (absParseResultD r).decls = x.decls
  projRewrites : (absParseResultD r).projRewrites = x.projRewrites
  inModelled : (absParseResultD r).inModelled = x.inModelled
  genRecords : (absParseResultD r).genRecords = x.genRecords
  genOwner : HashMap.RelOn (fun _ => True) r.gen_owner x.genOwner absName absName
  inModelDeclined :
    (absParseResultD r).inModelDeclined.map Prod.fst = x.inModelDeclined.map Prod.fst

/-! ## The parse tier's outcome

Both drivers end in `Except (CheckError × Nat) _`: con-leche's error is the
checker error **paired with the line it was read at**, and the port's is
`(CheckError, u64)`.  The full-outcome convention of DESIGN.md §3 applies
unchanged, with the line claimed alongside the kind — the port's `u64` line
counter cannot have wrapped in a run that returned `ok`, since Aeneas's `+`
fails rather than wrapping. -/

/-- *"If the port's parse error has a con-leche kind, con-leche throws there,
at that kind and at the same line."*  A `Native` error claims nothing, exactly
as `Refine/Abs.lean`'s `ErrSim` — which is where an `ErrTag::IndexOverflow`
lands since `export_c::scan_err_to_check`. -/
def ParseErrSim {γ : Type} (e : kernel.core_types.CheckError × Std.U64)
    (x : Except (ConLeche.CheckError × Nat) γ) : Prop :=
  ∀ k, absErrKind e.1 = some k →
    ∃ le, x = .error le ∧ lErrKind le.1 = k ∧ le.2 = e.2.val

/-- A mirrored error: con-leche throws at the kind the port's error abstracts
to, at the same line. -/
theorem ParseErrSim.mk {γ : Type} {e : kernel.core_types.CheckError × Std.U64}
    {x : Except (ConLeche.CheckError × Nat) γ} {le : ConLeche.CheckError × Nat}
    (hx : x = .error le) (hk : absErrKind e.1 = some (lErrKind le.1))
    (hl : le.2 = e.2.val) : ParseErrSim e x := by
  intro k hk'
  exact ⟨le, hx, by rw [hk] at hk'; exact Option.some_injective _ hk', hl⟩

/-- The port's own failure claims nothing. -/
theorem ParseErrSim.of_none {γ : Type} {e : kernel.core_types.CheckError × Std.U64}
    {x : Except (ConLeche.CheckError × Nat) γ} (h : absErrKind e.1 = none) :
    ParseErrSim e x := by intro k hk; rw [h] at hk; simp at hk

/-- `ParseErrSim` transported forward: whatever con-leche throws at `x` it
throws at `y`.  The caller's move — a `do` block throws exactly what its first
failing step threw. -/
theorem ParseErrSim.trans {γ δ : Type} {e : kernel.core_types.CheckError × Std.U64}
    {x : Except (ConLeche.CheckError × Nat) γ}
    {y : Except (ConLeche.CheckError × Nat) δ} (h : ParseErrSim e x)
    (hxy : ∀ le, x = .error le → y = .error le) : ParseErrSim e y := by
  intro k hk
  obtain ⟨le, hx, hk', hl⟩ := h k hk
  exact ⟨le, hxy le hx, hk', hl⟩

/-- **The full outcome**, in the shape of `Refine/Abs.lean`'s `OutP`: a
*relation* on the accept side — the parse's values are related, not
abstracted, because a parse state has no functional abstraction (`StateDRel`'s
note) — and `ParseErrSim` on the error side. -/
def ParseSim {α β : Type} (A : α → β → Prop)
    (o : core.result.Result α (kernel.core_types.CheckError × Std.U64))
    (x : Except (ConLeche.CheckError × Nat) β) : Prop :=
  match o with
  | .Ok r => ∃ y, x = .ok y ∧ A r y
  | .Err e => ParseErrSim e x

theorem ParseSim.ok {α β : Type} {A : α → β → Prop} {r : α} {y : β}
    {x : Except (ConLeche.CheckError × Nat) β} (hx : x = .ok y) (hA : A r y) :
    ParseSim A (.Ok r) x := ⟨y, hx, hA⟩

theorem ParseSim.err {α β : Type} {A : α → β → Prop}
    {e : kernel.core_types.CheckError × Std.U64}
    {x : Except (ConLeche.CheckError × Nat) β} (h : ParseErrSim e x) :
    ParseSim A (.Err e) x := h

/-! ## What `apply_line` claims

`Refine/Frontend/StateDR.lean`'s `LineOutV` is the outcome of a port function
whose con-leche twin is `M (β ⊕ RecordVerdict)`; `apply_line` is that with the
state coming out of the port's `&mut StateD` rather than out of the value, so
the `.Ok` arm is an existential over the related con-leche state rather than an
abstraction of the returned one.  The two error arms are `LineOutV`'s,
verbatim. -/

/-- **What `apply_line` claims** (`ConLeche/Frontend/ExportC.lean:713-726`
`applyLine`). -/
def ApplyLineSim (R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop)
    (o : core.result.Result Unit frontend.export_c.LineErr)
    (st' : frontend.export_c.StateD)
    (x : ConLeche.Frontend.M
      (ConLeche.Frontend.StateD ⊕ ConLeche.Frontend.RecordVerdict)) : Prop :=
  match o with
  | .Ok _ => ∃ lst, x = .ok (.inl lst) ∧ R st' lst
  | .Err (.Msg _) => ∃ s, x = .error s
  | .Err (.Verdict v) =>
    ∃ lv, x = .ok (.inr lv) ∧ lVerdictKind lv = absVerdictKind v

/-! ## The lower tier, as named hypotheses

The pattern of `Refine/IndSpec.lean` (task #56): one `Prop` field per lemma
this file consumes, each stated exactly as the owning file proves it, so that
the two can be written at the same time and the consumer never reads the
producer.  The owners are

| field | file |
|---|---|
| `scan_line_fwd`, `scan_line_fwd_tail`, `newline_from` | `Refine/Frontend/ScanLine.lean` |
| `apply_line` | `Refine/Frontend/IndR.lean` |
| `state_d_init`, `parse_result_of_state` | `Refine/Frontend/StateDR.lean` |

`R` is `StateDRel`; the structure is parametric in it so that nothing in this
file has to name a field of `export_c::StateD`. -/

/-- **What the parser's lower tier owes this file.** -/
structure ParseIngredients
    (R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop)
    {G : Type} (inst : frontend.in_model_rec.Modeller G) (g : G) : Prop where
  /-- `scan_fast::scan_line_fwd` refines `ConLeche.Frontend.scanLineFwd`
  (`ConLeche/Frontend/Scan/Fast.lean:2622-2638`), full outcome. -/
  scan_line_fwd : ∀ (b : Slice Std.U8) (i : Std.Usize)
      (o : core.result.Result (frontend.scan_types.LineRec × Std.Usize)
        frontend.scan_types.ScanErr),
      frontend.scan_fast.scan_line_fwd b i = ok o →
      ScanSim absLineRec o (ConLeche.Frontend.scanLineFwd (absBytes b) (absPos i))
  /-- **A reader failure with no newline ahead is an incomplete tail for
  con-leche's reader too.**  This is what pays for the port's own
  `ErrTag::IndexOverflow` in the ACCEPT direction (module note): `feed_chunk`
  answers `Ok (line_no, i)` there, and con-leche's `feedChunk` answers
  `(st, lineNo, i)` whether its own reader failed or stopped at `0`. -/
  scan_line_fwd_tail : ∀ (b : Slice Std.U8) (i : Std.Usize)
      (e : frontend.scan_types.ScanErr),
      frontend.scan_fast.scan_line_fwd b i = ok (.Err e) →
      frontend.scan_fast.newline_from b i = ok false →
      (∃ le, ConLeche.Frontend.scanLineFwd (absBytes b) (absPos i) = .err le) ∨
      (∃ r, ConLeche.Frontend.scanLineFwd (absBytes b) (absPos i) = .ok r 0)
  /-- `scan_fast::newline_from` refines `ConLeche.Frontend.newlineFrom`
  (`ConLeche/Frontend/Scan/Fast.lean:2639-2646`). -/
  newline_from : ∀ (b : Slice Std.U8) (i : Std.Usize) (r : Bool),
      frontend.scan_fast.newline_from b i = ok r →
      r = ConLeche.Frontend.newlineFrom (absBytes b) (absPos i)
  /-- `export_c::apply_line` refines `ConLeche.Frontend.applyLine`
  (`ConLeche/Frontend/ExportC.lean:713-726`), full outcome. -/
  apply_line : ∀ (st st' : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (r : frontend.scan_types.LineRec)
      (o : core.result.Result Unit frontend.export_c.LineErr),
      R st lst → frontend.export_c.apply_line inst g st r = ok (o, st') →
      ApplyLineSim R o st' (ConLeche.Frontend.applyLine lst (absLineRec r))
  /-- `export_c::state_d_init` refines `ConLeche.Frontend.StateD.init`
  (`ConLeche/Frontend/ExportC.lean:755-758`). -/
  state_d_init : ∀ (im ce : Bool) (st : frontend.export_c.StateD),
      frontend.export_c.state_d_init im ce = ok st →
      R st (ConLeche.Frontend.StateD.init im ce)
  /-- `export_c::parse_result_of_state` refines
  `ConLeche.Frontend.ParseResultD.ofState` (`ConLeche/Frontend/ExportC.lean:760-763`). -/
  parse_result_of_state : ∀ (st : frontend.export_c.StateD)
      (lst : ConLeche.Frontend.StateD) (r : frontend.export_c.ParseResultD),
      R st lst → frontend.export_c.parse_result_of_state st = ok r →
      ParseResultSim r (ConLeche.Frontend.ParseResultD.ofState lst)

/-! ## The bridge to `scanLineFwd`

**The one use of con-leche's `Scan/Equiv` tier.**  `applyFinalLine` and
`feedChunk` read their lines with `scanLineSpec`, the naive reference; the
`@[csimp]` `ConLeche.Frontend.scanLineSpec_eq_scanLineFwd`
(`ConLeche/Frontend/Scan/Equiv.lean:1002`) is what makes `scanLineFwd` the
function the compiler runs, and the port is a port of `scanLineFwd`.  This is
the only lemma of the whole tier that names `scanLineSpec`. -/

/-- con-leche's line reader is the one the port ports
(`ConLeche/Frontend/Scan/Equiv.lean:1002`, `@[csimp]`). -/
theorem scanLineSpec_eq_fwd (b : ByteArray) (i : USize) :
    ConLeche.Frontend.scanLineSpec b i = ConLeche.Frontend.scanLineFwd b i :=
  congrFun (congrFun ConLeche.Frontend.scanLineSpec_eq_scanLineFwd b) i

/-- `ConLeche/Frontend/ExportC.lean:765-775` `applyFinalLine`, with its reader
rewritten to the one the port ports. -/
theorem applyFinalLine_eq (lst : ConLeche.Frontend.StateD) (b : ByteArray)
    (i : USize) (ln : Nat) :
    ConLeche.Frontend.applyFinalLine lst b i ln =
      (match ConLeche.Frontend.scanLineFwd b i with
       | .err e =>
         .error (.internal (ConLeche.Frontend.ScanErr.render ⟨e.offset - i.toNat, e.what⟩), ln)
       | .ok r _ =>
         match ConLeche.Frontend.applyLine lst r with
         | .error msg => .error (.internal msg, ln)
         | .ok (.inr v) => .error (v.toError, ln)
         | .ok (.inl st) => .ok st) := by
  rw [ConLeche.Frontend.applyFinalLine, scanLineSpec_eq_fwd]
  rfl

/-- `ConLeche/Frontend/ExportC.lean:777-811` `feedChunk`, one step unfolded and
its reader rewritten to the one the port ports. -/
theorem feedChunk_eq (lst : ConLeche.Frontend.StateD) (b : ByteArray)
    (i : USize) (ln : Nat) :
    ConLeche.Frontend.feedChunk lst b i ln =
      (if _h : i < b.usize then
        match ConLeche.Frontend.scanLineFwd b i with
        | .err e =>
          if ConLeche.Frontend.newlineFrom b i then
            .error (.internal (ConLeche.Frontend.ScanErr.render ⟨e.offset - i.toNat, e.what⟩), ln + 1)
          else .ok (lst, ln, i)
        | .ok r j =>
          if j == 0 then .ok (lst, ln, i)
          else
            match ConLeche.Frontend.applyLine lst r with
            | .error msg => .error (.internal msg, ln + 1)
            | .ok (.inr v) => .error (v.toError, ln + 1)
            | .ok (.inl st) =>
              if _hj : i < j then ConLeche.Frontend.feedChunk st b j (ln + 1)
              else .error (.internal "the line scanner made no progress", ln + 1)
      else .ok (lst, ln, i)) := by
  rw [ConLeche.Frontend.feedChunk, scanLineSpec_eq_fwd]
  rfl

/-! ## Positions, two facts the loops need -/

/-- A position the port calls zero is con-leche's zero. -/
theorem absPos_eq_zero {j : Std.Usize} : absPos j = 0 ↔ j.val = 0 := by
  constructor
  · intro h; have := congrArg USize.toNat h; simpa using this
  · intro h; apply USize.toNat_inj.mp; simp [h]

/-- The port's order on positions is con-leche's. -/
theorem absPos_lt {i j : Std.Usize} : absPos i < absPos j ↔ i.val < j.val := by
  rw [USize.lt_iff_toNat_lt, absPos_toNat, absPos_toNat]

/-! ## The last line

`export_c::apply_final_line` (`ConLeche/Frontend/ExportC.lean:765-775`
`applyFinalLine`): scan and apply the LAST line of a stream, the one no
newline ends.  A syntactic failure is reported at its offset in the line —
`export_c::rel_offset` against con-leche's `e.offset - i.toNat` — and neither
offset is compared, since both are folded into a message. -/

/-- **`export_c::apply_final_line`, accept direction**
(`ConLeche/Frontend/ExportC.lean:765-775` `applyFinalLine`). -/
theorem apply_final_line_refines
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g)
    {st st' : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {b : Slice Std.U8} {i : Std.Usize} {ln : Std.U64} (hst : R st lst)
    (h : frontend.export_c.apply_final_line inst g st b i ln = ok (.Ok (), st')) :
    ∃ lst', ConLeche.Frontend.applyFinalLine lst (absBytes b) (absPos i) ln.val
        = .ok lst' ∧ R st' lst' := by
  rw [frontend.export_c.apply_final_line.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  have hsim := ing.scan_line_fwd b i r hr
  rw [applyFinalLine_eq]
  split at h
  · rename_i p
    obtain ⟨r1, j⟩ := p
    simp only [uncurry_apply_pair, bind_eq_ok_iff] at h
    obtain ⟨⟨r2, st1⟩, happ, h⟩ := h
    simp only [uncurry_apply_pair] at h
    have hal := ing.apply_line st st1 lst r1 r2 hst happ
    split at h
    · rw [show ConLeche.Frontend.scanLineFwd (absBytes b) (absPos i)
            = .ok (absLineRec r1) (absPos j) from hsim]
      simp only [ApplyLineSim] at hal
      obtain ⟨lst2, hlst2, hrel⟩ := hal
      simp only [hlst2]
      simp only [Result.ok.injEq, Prod.mk.injEq] at h
      exact ⟨lst2, rfl, h.2 ▸ hrel⟩
    · exfalso; revert h
      simp [bind_eq_ok_iff, frontend.export_c.line_err_to_check]
  · exfalso; revert h
    simp [bind_eq_ok_iff]

/-! ## The file's main loop

`export_c::feed_chunk` (`ConLeche/Frontend/ExportC.lean:777-811` `feedChunk`):
every COMPLETE line of the chunk from `i`, applied in order.

`feed_chunk_loop` is `partial_fixpoint` and has no induction principle, so the
statement goes by strong induction on the same `Nat` measure phase 1 used
(`Refine/Frontend/Chunks.lean`'s `feed_chunk_loop_wf`): the loop jumps the byte
index to the reader's `j`, and what makes the measure decrease is the code's
own no-progress guard.  con-leche's `feedChunk` is well founded on
`b.size - i.toNat`, the same measure, and `feedChunk_eq` unfolds one step of
it, so the two recursions are stepped together. -/

private theorem feed_chunk_loop_refines
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g) (N : Nat) :
    ∀ (st st' : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (b : Slice Std.U8) (i : Std.Usize) (ln : Std.U64) (p : Std.U64 × Std.Usize),
      R st lst → (Slice.len b).val - i.val = N →
      frontend.export_c.feed_chunk_loop inst g st b i ln = ok (.Ok p, st') →
      ∃ lst', ConLeche.Frontend.feedChunk lst (absBytes b) (absPos i) ln.val
          = .ok (lst', p.1.val, absPos p.2) ∧ R st' lst' := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro st st' lst b i ln p hst hN h
    rw [frontend.export_c.feed_chunk_loop.eq_def] at h
    simp only [] at h
    rw [feedChunk_eq]
    split at h
    · rename_i hlt
      rw [dif_pos (show absPos i < (absBytes b).usize from
        absPos_lt_usize.mpr (by scalar_tac))]
      simp only [bind_eq_ok_iff] at h
      obtain ⟨r, hr, h⟩ := h
      have hsim := ing.scan_line_fwd b i r hr
      split at h
      · rename_i q
        obtain ⟨r1, j⟩ := q
        simp only [uncurry_apply_pair] at h
        have hscan : ConLeche.Frontend.scanLineFwd (absBytes b) (absPos i)
            = .ok (absLineRec r1) (absPos j) := hsim
        split at h
        · rename_i hj0
          have hjz : absPos j = 0 := by rw [hj0]; rfl
          simp only [hscan, hjz, beq_self_eq_true, if_true]
          simp only [Result.ok.injEq, Prod.mk.injEq,
            core.result.Result.Ok.injEq] at h
          exact ⟨lst, by rw [← h.1], h.2 ▸ hst⟩
        · rename_i hj0
          have hjnz : (absPos j == 0) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq, absPos_eq_zero]
            intro hc; exact hj0 (by scalar_tac)
          simp only [hscan, hjnz, Bool.false_eq_true, if_false]
          simp only [bind_eq_ok_iff] at h
          obtain ⟨⟨r2, st1⟩, happ, h⟩ := h
          simp only [uncurry_apply_pair] at h
          have hal := ing.apply_line st st1 lst r1 r2 hst happ
          split at h
          · simp only [ApplyLineSim] at hal
            obtain ⟨lst2, hlst2, hrel⟩ := hal
            simp only [hlst2]
            split at h
            · exfalso; revert h; simp [bind_eq_ok_iff]
            · rename_i hge
              simp only [bind_eq_ok_iff] at h
              obtain ⟨ln1, hln1, h⟩ := h
              rw [dif_pos (show absPos i < absPos j from
                absPos_lt.mpr (by scalar_tac))]
              obtain ⟨lst', hfc, hrel'⟩ :=
                ih ((Slice.len b).val - j.val) (by scalar_tac) st1 st' lst2 b j ln1 p
                  hrel rfl h
              refine ⟨lst', ?_, hrel'⟩
              rw [show ln.val + 1 = ln1.val from (HashMap.uscalar_add_eq hln1).symm]
              exact hfc
          · exfalso; revert h
            simp [bind_eq_ok_iff, frontend.export_c.line_err_to_check]
      · rename_i e
        simp only [bind_eq_ok_iff] at h
        obtain ⟨b1, hb1, h⟩ := h
        split at h
        · exfalso; revert h; simp [bind_eq_ok_iff]
        · rename_i hb1f
          rw [show b1 = false by simpa using hb1f] at hb1
          simp only [Result.ok.injEq, Prod.mk.injEq,
            core.result.Result.Ok.injEq] at h
          have hnl : ConLeche.Frontend.newlineFrom (absBytes b) (absPos i) = false :=
            (ing.newline_from b i false hb1).symm
          rcases ing.scan_line_fwd_tail b i e hr hb1 with ⟨le, hle⟩ | ⟨r0, hr0⟩
          · rw [hle]
            simp only [hnl, Bool.false_eq_true, if_false]
            exact ⟨lst, by rw [← h.1], h.2 ▸ hst⟩
          · rw [hr0]
            simp only [beq_self_eq_true, if_true]
            exact ⟨lst, by rw [← h.1], h.2 ▸ hst⟩
    · rename_i hge
      rw [dif_neg (show ¬ (absPos i < (absBytes b).usize) from
        fun hc => absurd (absPos_lt_usize.mp hc) (by scalar_tac))]
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      exact ⟨lst, by rw [← h.1], h.2 ▸ hst⟩

/-- **`export_c::feed_chunk`, accept direction**
(`ConLeche/Frontend/ExportC.lean:777-811` `feedChunk`). -/
theorem feed_chunk_refines
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g)
    {st st' : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {b : Slice Std.U8} {i : Std.Usize} {ln : Std.U64} {p : Std.U64 × Std.Usize}
    (hst : R st lst)
    (h : frontend.export_c.feed_chunk inst g st b i ln = ok (.Ok p, st')) :
    ∃ lst', ConLeche.Frontend.feedChunk lst (absBytes b) (absPos i) ln.val
        = .ok (lst', p.1.val, absPos p.2) ∧ R st' lst' :=
  feed_chunk_loop_refines ing _ st st' lst b i ln p hst rfl h

/-! ## The size guard, and the bytes a `Slice` abstracts to

`export_c::size_error` (`ConLeche/Frontend/ExportC.lean:816-825` `sizeError`):
an input of `USize.size` bytes or more is refused before any of it is read.
The port drops con-leche's interpolated byte count (`size_error`'s note: no
`u64` renders `2^64`), which costs nothing — messages are never compared. -/

/-- A `Slice`'s length is below `Usize.max`, so the guard con-leche states over
`b.size` can never fire for a slice the port handed us. -/
private theorem absBytes_size_lt (b : Slice Std.U8) : (absBytes b).size < USize.size := by
  rw [absBytes_size]
  have h1 : b.val.length ≤ Std.Usize.max := Slice.property b
  have h2 : (Std.Usize.max : Nat) < USize.size := by
    rw [Std.Usize.max_def, Std.Usize.numBits_def]
    simp only [USize.size, Std.UScalarTy.numBits]
    have hp : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
    omega
  omega

/-- **`export_c::size_error` mirrors `ConLeche.Frontend.sizeError`**
(`ConLeche/Frontend/ExportC.lean:816-825`): the same kind
(`.notImplemented`) at the same line (`0`). -/
theorem size_error_refines {γ : Type} {p : kernel.core_types.CheckError × Std.U64}
    {x : Except (ConLeche.CheckError × Nat) γ}
    (h : frontend.export_c.size_error = ok p)
    (hx : x = .error ConLeche.Frontend.sizeError) : ParseErrSim p x := by
  rw [frontend.export_c.size_error] at h
  simp only [bind_eq_ok_iff, kernel.core_types.not_implemented, Result.ok.injEq] at h
  obtain ⟨s, -, v, -, y, hy, hp⟩ := h
  subst hy; subst hp
  exact ParseErrSim.mk hx (by simp [absErrKind, lErrKind, ConLeche.Frontend.sizeError])
    (by simp [ConLeche.Frontend.sizeError])

/-! ## The wholesale parse

`export_c::parse_bytes` (`ConLeche/Frontend/ExportC.lean:827-839` `parseBytes`):
the whole input fed at once, then the last line.

**One intermediate definition** (the escape hatch DESIGN.md's task-#87 brief
allows, recorded in the task report): con-leche writes the last line *inline*
in `parseBytes`'s `do` block while the port factors it out as
`export_c::parse_bytes_final` — §3.4's rule that a Rust function has one loop
and one shape.  `parseBytesFinal` is that fragment of con-leche, written out,
and `parseBytes_eq` is the equivalence proof: `parseBytes` **is** its size
guard, `feedChunk`, and `parseBytesFinal`. -/

/-- The cited tail of `parseBytes` (`ConLeche/Frontend/ExportC.lean:834-838`),
which the port factors out as `export_c::parse_bytes_final`. -/
def parseBytesFinal (lst : ConLeche.Frontend.StateD) (b : ByteArray) (tail : USize)
    (ln : Nat) : Except (ConLeche.CheckError × Nat) ConLeche.Frontend.ParseResultD :=
  if tail < b.usize then do
    let st ← ConLeche.Frontend.applyFinalLine lst b tail (ln + 1)
    return ConLeche.Frontend.ParseResultD.ofState st
  else return ConLeche.Frontend.ParseResultD.ofState lst

/-- The equivalence proof for `parseBytesFinal`: con-leche's `parseBytes` is
its guard, `feedChunk` and that fragment. -/
theorem parseBytes_eq (b : ByteArray) (im ce : Bool) :
    ConLeche.Frontend.parseBytes b im ce =
      (if b.size ≥ USize.size then .error ConLeche.Frontend.sizeError
       else do
         let (st, lineNo, tail) ← ConLeche.Frontend.feedChunk (.init im ce) b 0 0
         parseBytesFinal st b tail lineNo) := by
  rw [ConLeche.Frontend.parseBytes]
  rfl

/-- **`export_c::parse_bytes_final`, accept direction**
(`ConLeche/Frontend/ExportC.lean:834-838`, the cited tail of `parseBytes`). -/
theorem parse_bytes_final_refines
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g)
    {st : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {b : Slice Std.U8} {tail : Std.Usize} {ln : Std.U64}
    {r : frontend.export_c.ParseResultD} (hst : R st lst)
    (h : frontend.export_c.parse_bytes_final inst g st b tail ln = ok (.Ok r)) :
    ∃ x, parseBytesFinal lst (absBytes b) (absPos tail) ln.val = .ok x ∧
      ParseResultSim r x := by
  rw [frontend.export_c.parse_bytes_final.eq_def] at h
  simp only [] at h
  rw [parseBytesFinal]
  split at h
  · rename_i hlt
    rw [if_pos (absPos_lt_usize.mpr (by scalar_tac))]
    simp only [bind_eq_ok_iff] at h
    obtain ⟨i1, hi1, ⟨rr, st1⟩, hfin, h⟩ := h
    simp only [uncurry_apply_pair] at h
    split at h
    · obtain ⟨lst', hafl, hrel⟩ := apply_final_line_refines ing hst hfin
      rw [show ln.val + 1 = i1.val from (HashMap.uscalar_add_eq hi1).symm]
      simp only [hafl]
      simp only [bind_eq_ok_iff, Result.ok.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨prd, hprd, hr⟩ := h
      exact ⟨_, rfl, hr ▸ ing.parse_result_of_state st1 lst' prd hrel hprd⟩
    · exfalso; revert h; simp
  · rw [if_neg (fun hc => absurd (absPos_lt_usize.mp hc) (by scalar_tac))]
    simp only [bind_eq_ok_iff, Result.ok.injEq, core.result.Result.Ok.injEq] at h
    obtain ⟨prd, hprd, hr⟩ := h
    exact ⟨_, rfl, hr ▸ ing.parse_result_of_state st lst prd hst hprd⟩

/-- **`export_c::parse_bytes`, accept direction**
(`ConLeche/Frontend/ExportC.lean:827-839` `parseBytes`): the whole input fed at
once, then the last line. -/
theorem parse_bytes_refines
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g) {b : Slice Std.U8} {im ce : Bool}
    {r : frontend.export_c.ParseResultD}
    (h : frontend.export_c.parse_bytes inst g b im ce = ok (.Ok r)) :
    ∃ x, ConLeche.Frontend.parseBytes (absBytes b) im ce = .ok x ∧
      ParseResultSim r x := by
  rw [frontend.export_c.parse_bytes.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨i1, -, i2, -, h⟩ := h
  rw [parseBytes_eq, if_neg (by have := absBytes_size_lt b; omega)]
  split at h
  · exfalso; revert h; simp [bind_eq_ok_iff]
  · simp only [bind_eq_ok_iff] at h
    obtain ⟨st, hinit, ⟨rr, st1⟩, hfeed, h⟩ := h
    simp only [uncurry_apply_pair] at h
    split at h
    · rename_i q
      obtain ⟨ln, tail⟩ := q
      obtain ⟨lst1, hfc, hrel⟩ :=
        feed_chunk_refines ing (ing.state_d_init im ce st hinit) hfeed
      simp only [show absPos (0#usize) = 0 from rfl,
        show ((0#u64 : Std.U64)).val = 0 from rfl] at hfc
      simp only [hfc]
      exact parse_bytes_final_refines ing hrel h
    · exfalso; revert h; simp

/-! ## The end of the stream

`export_c::chunk_finish` (`ConLeche/Frontend/ExportC.lean:867-874`
`chunkFinish`): the carried tail, if any, is the stream's last line. -/

/-- A slice is empty exactly when the bytes it abstracts to are. -/
private theorem absBytes_isEmpty (b : Slice Std.U8) :
    (absBytes b).isEmpty = true ↔ Slice.len b = 0#usize := by
  simp only [ByteArray.isEmpty, absBytes_size, beq_iff_eq]
  constructor
  · intro h; scalar_tac
  · intro h; scalar_tac

/-- **`export_c::chunk_finish`, accept direction**
(`ConLeche/Frontend/ExportC.lean:867-874` `chunkFinish`). -/
theorem chunk_finish_refines
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g)
    {st : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {carry : Slice Std.U8} {ln : Std.U64} {r : frontend.export_c.ParseResultD}
    (hst : R st lst)
    (h : frontend.export_c.chunk_finish inst g st carry ln = ok (.Ok r)) :
    ∃ x, ConLeche.Frontend.chunkFinish lst (absBytes carry) ln.val = .ok x ∧
      ParseResultSim r x := by
  rw [frontend.export_c.chunk_finish.eq_def] at h
  simp only [] at h
  rw [ConLeche.Frontend.chunkFinish]
  split at h
  · rename_i he
    rw [if_pos ((absBytes_isEmpty carry).mpr he)]
    simp only [bind_eq_ok_iff, Result.ok.injEq, core.result.Result.Ok.injEq] at h
    obtain ⟨prd, hprd, hr⟩ := h
    exact ⟨_, rfl, hr ▸ ing.parse_result_of_state st lst prd hst hprd⟩
  · rename_i he
    rw [if_neg (fun hc => he ((absBytes_isEmpty carry).mp hc))]
    simp only [bind_eq_ok_iff] at h
    obtain ⟨i1, hi1, ⟨rr, st1⟩, hfin, h⟩ := h
    simp only [uncurry_apply_pair] at h
    split at h
    · obtain ⟨lst', hafl, hrel⟩ := apply_final_line_refines ing hst hfin
      rw [show ln.val + 1 = i1.val from (HashMap.uscalar_add_eq hi1).symm,
        show absPos (0#usize) = 0 from rfl] at *
      simp only [hafl]
      simp only [bind_eq_ok_iff, Result.ok.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨prd, hprd, hr⟩ := h
      exact ⟨_, rfl, hr ▸ ing.parse_result_of_state st1 lst' prd hrel hprd⟩
    · exfalso; revert h; simp

end ConRon.Refine.Frontend

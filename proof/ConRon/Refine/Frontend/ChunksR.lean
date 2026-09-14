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
* `parse_chunks_refines` / `parse_chunks_refines_err` — **the lemma the whole
  task's headline composes with**, both halves — and
  `builtin_prelude_e_refines`, its prelude twin.

Everything in this file is *proved*; the six `ParseIngredients` fields are the
only residue, and fields 5 and 6 are discharged here
(`parse_result_state_d_init`, `parse_result_of_state_sim`) against
`Refine/Frontend/StateDR.lean`.

## One intermediate definition

`parseBytesFinal`, con-leche's last-line fragment written out, because
`parseBytes` writes it inline in a `do` block while the port factors it out as
`export_c::parse_bytes_final` (DESIGN.md §3.4's one-loop-one-shape rule).
`parseBytes_eq` is its equivalence proof: `parseBytes` **is** its size guard,
`feedChunk` and `parseBytesFinal`, by `rfl`.  That is the task brief's escape
hatch, used once.

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
import ConRon.Refine.Frontend.Chunks
import ConRon.Refine.Frontend.StateDR
import ConRon.Refine.Frontend.Abs
import ConRon.Refine.Frontend.ScanKit
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

/-- **What a parse result claims**, field by field — the six clauses
`Refine/Frontend/StateDR.lean`'s `parse_result_of_state_refines` proves,
spelled here in the same order and the same shape so that the
`ParseIngredients` field below is a one-line `⟨…⟩` from it.  (`StateDR.lean`
cannot name this structure: it is *below* this file.)

`absParseResultD` above is the same six fields as a value, in `Array` form;
the clauses are stated in `List` form because that is what `StateDRel`'s own
clauses are.  `genOwner` is a `ron::HashMap` against a `Std.HashMap` and is
claimed the way `Refine/FEnv.lean` claims its index — by `HashMap.RelOn`,
lookup for lookup — and, as everywhere at a `Name` key, only for well-formed
names (`Refine/HashMapWF.lean`'s note).  `inModelGen` has no clause: the port
has no such field. -/
structure ParseResultSim (r : frontend.export_c.ParseResultD)
    (x : ConLeche.Frontend.ParseResultD) : Prop where
  decls : r.decls.val.map absDeclaration = x.decls.toList
  projRewrites : r.proj_rewrites.val.map absName = x.projRewrites.toList
  inModelled : r.in_modelled.val.map absName = x.inModelled.toList
  genRecords : r.gen_records.val = x.genRecords
  genOwner : HashMap.RelOn NameWF r.gen_owner x.genOwner absName absName
  inModelDeclined : r.in_model_declined.val.map absNameStr = x.inModelDeclined.toList

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

-- `absPos_lt` is `Refine/Frontend/ScanKit.lean`'s, which this file imports:
-- that file owns every `absByte`/`absPos`/`absU32` bridge (`Refine/README.md`).

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

/-! ## Bytes: the bridge `chunk_step` and `concat_bytes` need

The port carries the chunk buffer as a `Vec<u8>` and cuts its tail with
`buf[tail..]`; con-leche carries a `ByteArray` and cuts it with
`ByteArray.extract`.  These lemmas are the whole bridge. -/

/-- A `ByteArray` is its data. -/
private theorem byteArray_eq_of_data {x y : ByteArray} (h : x.data = y.data) : x = y := by
  cases x; cases y; simpa using h

/-- `ByteArray.append` on the underlying arrays. -/
private theorem byteArray_mk_append (a b : Array UInt8) :
    (⟨a⟩ : ByteArray) ++ (⟨b⟩ : ByteArray) = ⟨a ++ b⟩ :=
  byteArray_eq_of_data (by rw [ByteArray.data_append])

/-- `absBytes` of a concatenation is the concatenation. -/
private theorem absBytes_append_val {s : Slice Std.U8} {c : alloc.vec.Vec Std.U8}
    {b : Slice Std.U8} (h : s.val = c.val ++ b.val) :
    absBytes s = absChunk c ++ absBytes b := by
  rw [absBytes, absChunk, absBytes, h, byteArray_mk_append]
  simp

/-- `absBytes` only reads the element list, so a `Vec` and the slice of all of
it abstract to the same bytes. -/
private theorem absBytes_of_val {s : Slice Std.U8} {c : alloc.vec.Vec Std.U8}
    (h : s.val = c.val) : absBytes s = absChunk c := by
  rw [absBytes, absChunk, h]

/-- Cutting the tail: the port's `buf[tail..]` is con-leche's
`buf.extract tail.toNat buf.size`. -/
private theorem absChunk_drop {v : alloc.vec.Vec Std.U8} {s : Slice Std.U8}
    {t : Std.Usize} (h : v.val = s.val.drop t.val) :
    absChunk v = (absBytes s).extract t.val (absBytes s).size := by
  apply byteArray_eq_of_data
  rw [ByteArray.data_extract]
  simp only [absChunk, absBytes, ByteArray.size, h]
  apply Array.toList_inj.mp
  simp [List.extract_eq_take_drop]

/-! ## The clone the port's `Vec` operations go through

`alloc::slice::to_vec` and `Vec::extend_from_slice` are modelled through
`Slice.clone`, and `u8`'s `Clone` is the identity, so both are the plain list
operations. -/

private theorem u8_list_clone (l : List Std.U8) :
    List.clone core.clone.CloneU8.clone l = ok ⟨l, rfl⟩ := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    show List.mapM_with_length _ (a :: t) = _
    rw [List.mapM_with_length,
      show List.mapM_with_length core.clone.CloneU8.clone t = ok ⟨t, rfl⟩ from ih]
    simp [pure]

private theorem u8_slice_clone (s : Slice Std.U8) :
    Slice.clone core.clone.CloneU8.clone s = ok s := by
  rw [Slice.clone, u8_list_clone]
  simp

private theorem u8_to_vec_val {s : Slice Std.U8} {v : alloc.vec.Vec Std.U8}
    (h : alloc.slice.Slice.to_vec core.clone.CloneU8 s = ok v) : v.val = s.val := by
  rw [alloc.slice.Slice.to_vec, u8_slice_clone] at h
  simp at h
  rw [← h]
  rfl

private theorem u8_extend_val {v : alloc.vec.Vec Std.U8} {s : Slice Std.U8}
    {w : alloc.vec.Vec Std.U8}
    (h : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s = ok w) :
    w.val = v.val ++ s.val := by
  rw [alloc.vec.Vec.extend_from_slice] at h
  split at h
  · split at h
    · rename_i s' hs'
      rw [u8_slice_clone, Result.match.ok] at hs'
      simp only [MatchResult.ok.injEq] at hs'
      subst hs'
      simp only [Result.ok.injEq] at h
      rw [← h, alloc.vec.Vec.from_val]
    · exfalso; revert h; simp
    · exfalso; revert h; simp
  · exfalso; revert h; simp


/-- A `usize` value fits a `u128`. -/
private theorem usize_val_lt_u128 (x : Std.Usize) :
    x.val < 340282366920938463463374607431768211456 := by
  have h1 : x.val ≤ Std.Usize.max := by scalar_tac
  have hm : (Std.Usize.max : Nat) < 340282366920938463463374607431768211456 := by
    rw [Std.Usize.max_def, Std.Usize.numBits_def]
    simp only [Std.UScalarTy.numBits]
    rcases System.Platform.numBits_eq with hn | hn <;> rw [hn] <;> norm_num
  omega

/-- A `u64` value fits a `u128`. -/
private theorem u64_val_lt_u128 (x : Std.U64) :
    x.val < 340282366920938463463374607431768211456 := by
  have h1 : x.val ≤ Std.U64.max := by scalar_tac
  have hm : (Std.U64.max : Nat) < 340282366920938463463374607431768211456 := by
    rw [Std.U64.max_def, Std.U64.numBits_def]
    norm_num
  omega

/-- Widening to `u128` keeps the value. -/
private theorem cast_u128_val {ty : Std.UScalarTy} (x : Std.UScalar ty)
    (h : x.val < 340282366920938463463374607431768211456) :
    (Std.UScalar.cast .U128 x).val = x.val := by
  rw [Std.UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by simpa [Std.UScalarTy.numBits] using h)

/-! ## The size guard's constant

`export_c::USIZE_SIZE` is `1u128 << usize::BITS` — the port's spelling of
`USize.size`, in `u128` because `1 << 64` does not fit the type it bounds
(`export_c.rs`'s note). -/

private theorem usize_size_val {c : Std.U128} (h : frontend.export_c.USIZE_SIZE = ok c) :
    c.val = USize.size := by
  simp only [frontend.export_c.USIZE_SIZE, HShiftLeft.hShiftLeft,
    Std.UScalar.shiftLeft_UScalar, Std.UScalar.shiftLeft] at h
  have hbits : (core.num.Usize.BITS).val = System.Platform.numBits := rfl
  rw [hbits] at h
  have hnb := System.Platform.numBits_eq
  rw [if_pos (show System.Platform.numBits < Std.UScalarTy.numBits .U128 by
    simp only [Std.UScalarTy.numBits]; omega)] at h
  simp only [Result.ok.injEq] at h
  rw [← h]
  simp only [Std.UScalar.val, USize.size]
  rcases hnb with hnb | hnb <;> rw [hnb] <;> rfl

/-! ## One chunk of the stream

`export_c::chunk_step` (`ConLeche/Frontend/ExportC.lean:848-865` `chunkStep`):
the carried incomplete tail in front of the new bytes, every complete line of
the buffer fed, and the new incomplete tail cut off for the next chunk. -/

/-- **`export_c::chunk_step`, accept direction**
(`ConLeche/Frontend/ExportC.lean:848-865` `chunkStep`). -/
theorem chunk_step_refines
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g)
    {st st' : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {carry : alloc.vec.Vec Std.U8} {ln total : Std.U64} {buf0 : Slice Std.U8}
    {q : (alloc.vec.Vec Std.U8) × Std.U64 × Std.U64} (hst : R st lst)
    (h : frontend.export_c.chunk_step inst g st carry ln total buf0 = ok (.Ok q, st')) :
    ∃ lst', ConLeche.Frontend.chunkStep lst (absChunk carry) ln.val total.val
        (absBytes buf0) = .ok (lst', absChunk q.1, q.2.1.val, q.2.2.val) ∧ R st' lst' := by
  rw [frontend.export_c.chunk_step.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨i, hi, i2, hi2, i3, hi3, i4, hi4, h⟩ := h
  rw [ConLeche.Frontend.chunkStep]
  split at h
  · exfalso; revert h; simp [bind_eq_ok_iff]
  · rename_i hguard
    simp only [lift_eq, Result.ok.injEq] at hi hi2
    have hsz : ¬ (total.val + (absBytes buf0).size ≥ USize.size) := by
      rw [absBytes_size]
      have hc := usize_size_val hi4
      have h3 := HashMap.uscalar_add_eq hi3
      have hlt : i3.val < i4.val := by scalar_tac
      have hiv : i.val = total.val := by
        rw [← hi]; exact cast_u128_val total (u64_val_lt_u128 total)
      have hi2v : i2.val = buf0.val.length := by
        rw [← hi2]
        exact cast_u128_val (Slice.len buf0) (usize_val_lt_u128 (Slice.len buf0))
      omega
    rw [if_neg hsz]
    simp only [bind_eq_ok_iff] at h
    obtain ⟨buf, hbuf, s, hs, ⟨rr, st1⟩, hfeed, h⟩ := h
    have hsval : s.val = buf.val := by
      simp only [alloc.vec.Vec.index,
        core.slice.index.SliceIndexRangeFullSlice.index, Result.ok.injEq] at hs
      rw [← hs]; rfl
    have hbufb : (if (absChunk carry).isEmpty then absBytes buf0
                  else absChunk carry ++ absBytes buf0) = absBytes s := by
      split at hbuf
      · rename_i hce
        rw [if_pos (by
          simp only [ByteArray.isEmpty, absChunk, ByteArray.size, beq_iff_eq]
          simp only [alloc.vec.Vec.len] at hce
          scalar_tac)]
        have hv : s.val = buf0.val := by rw [hsval, u8_to_vec_val hbuf]
        show absBytes buf0 = absBytes s
        rw [absBytes, absBytes, hv]
      · rename_i hce
        rw [if_neg (by
          simp only [ByteArray.isEmpty, absChunk, ByteArray.size, beq_iff_eq]
          simp only [alloc.vec.Vec.len] at hce
          intro hc; exact hce (by scalar_tac))]
        exact (absBytes_append_val (by rw [hsval, u8_extend_val hbuf])).symm
    rw [hbufb]
    simp only [uncurry_apply_pair] at h
    split at h
    · rename_i t
      obtain ⟨ln2, tail⟩ := t
      obtain ⟨lst', hfc, hrel⟩ := feed_chunk_refines ing hst hfeed
      simp only [show absPos (0#usize) = 0 from rfl] at hfc
      simp only [uncurry_apply_pair, bind_eq_ok_iff] at h
      obtain ⟨s1, hs1, v, hv, i7, hi7, i8, hi8, hq⟩ := h
      simp only [hfc]
      have hdrop : v.val = s.val.drop tail.val := by
        rw [u8_to_vec_val hv]
        simp only [alloc.vec.Vec.index,
          core.slice.index.SliceIndexRangeFromUsizeSlice.index] at hs1
        split at hs1
        · simp only [Result.ok.injEq] at hs1
          rw [← hs1]
          simp [Slice.drop, hsval, alloc.vec.Vec.val]
        · exfalso; revert hs1; simp
      simp only [Result.ok.injEq, Prod.mk.injEq,
        core.result.Result.Ok.injEq] at hq
      obtain ⟨hqv, hqst⟩ := hq
      subst hqv
      refine ⟨lst', ?_, hqst ▸ hrel⟩
      have h1 : (absBytes s).extract (absPos tail).toNat (absBytes s).size
          = absChunk v := by
        rw [absPos_toNat]; exact (absChunk_drop hdrop).symm
      have h3 : total.val + (absBytes buf0).size = i8.val := by
        rw [absBytes_size, HashMap.uscalar_add_eq hi8]
        simp only [lift_eq, Result.ok.injEq] at hi7
        have hi7v : i7.val = buf0.val.length := by rw [← hi7]; simp
        omega
      rw [h1, h3]
    · exfalso; revert h; simp

/-! ## The chunk fold

`export_c::parse_chunks` (`ConLeche/Frontend/ExportC.lean:882-901` `parseChunks`):
`chunk_step` folded over the list of chunks, `chunk_finish` at its end.
con-leche's `go` recurses over the list while the port's `while i < n` indexes
the `Vec`, so the two are lined up at `(absChunks chunks).drop i.val`, with the
measure `n - i` phase 1's `parse_chunks_loop_wf` used. -/

/-- The image of a `Vec` read at `i`, as the head of the abstracted tail
(`Refine/Frontend/IndR.lean` and `Refine/Frontend/ProjRecR.lean` keep their own
copies; this file is below neither). -/
private theorem chunks_drop_map_index {α β : Type} {v : alloc.vec.Vec α}
    {i : Std.Usize} {x : α} (f : α → β)
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    i.val < v.val.length ∧
      (v.val.map f).drop i.val = f x :: (v.val.map f).drop (i.val + 1) := by
  have hg := ExprOps.vec_index_getElem? h
  have hlt : i.val < v.val.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
  have hx : v.val[i.val] = x := by
    rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
  refine ⟨hlt, ?_⟩
  rw [List.drop_eq_getElem_cons (by simpa using hlt)]
  simp [hx]

private theorem parse_chunks_loop_refines
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g) (N : Nat) :
    ∀ (chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (st : frontend.export_c.StateD)
      (lst : ConLeche.Frontend.StateD) (carry : alloc.vec.Vec Std.U8)
      (ln total : Std.U64) (n i : Std.Usize) (r : frontend.export_c.ParseResultD),
      R st lst → n.val = chunks.val.length → n.val - i.val = N →
      frontend.export_c.parse_chunks_loop inst g chunks st carry ln total n i
        = ok (.Ok r) →
      ∃ x, ConLeche.Frontend.parseChunks.go lst (absChunk carry) ln.val total.val
          ((absChunks chunks).drop i.val) = .ok x ∧ ParseResultSim r x := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro chunks st lst carry ln total n i r hst hn hN h
    rw [frontend.export_c.parse_chunks_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨v, hv, s, hs, ⟨rr, st1⟩, hstepr, h⟩ := h
      obtain ⟨hilt, hdrop⟩ := chunks_drop_map_index absChunk hv
      rw [absChunks, hdrop, ConLeche.Frontend.parseChunks.go]
      have hsb : absBytes s = absChunk v := by
        apply absBytes_of_val
        simp only [alloc.vec.Vec.index,
          core.slice.index.SliceIndexRangeFullSlice.index, Result.ok.injEq] at hs
        rw [← hs]; rfl
      rw [← hsb]
      simp only [uncurry_apply_pair] at h
      split at h
      · rename_i t
        obtain ⟨c2, l, t1⟩ := t
        obtain ⟨lst1, hcs, hrel⟩ := chunk_step_refines ing hst hstepr
        rw [hcs]
        simp only [uncurry_apply_pair, bind_eq_ok_iff] at h
        obtain ⟨i1, hi1, h⟩ := h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        have hres := ih (n.val - i1.val) (by scalar_tac) chunks st1 lst1 c2 l t1 n i1 r
          hrel hn rfl h
        rw [hi1v] at hres
        exact hres
      · exfalso; revert h; simp
    · rename_i hge
      simp only [bind_eq_ok_iff] at h
      obtain ⟨s, hs, h⟩ := h
      have hnil : (absChunks chunks).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absChunks, List.length_map]
        scalar_tac
      rw [hnil, ConLeche.Frontend.parseChunks.go]
      have hsb : absBytes s = absChunk carry := by
        apply absBytes_of_val
        simp only [alloc.vec.Vec.index,
          core.slice.index.SliceIndexRangeFullSlice.index, Result.ok.injEq] at hs
        rw [← hs]; rfl
      rw [← hsb]
      exact chunk_finish_refines ing hst h

/-- **The streaming parse, exact against con-leche**
(`ConLeche/Frontend/ExportC.lean:882-901` `parseChunks`) — *the lemma the whole
task's headline composes with*: for any cutting of the input into chunks, what
the port's parse hands back is what `parseChunks` of the abstracted chunks
hands back, field for field. -/
theorem parse_chunks_refines
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g)
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)} {im ce : Bool}
    {r : frontend.export_c.ParseResultD}
    (h : frontend.export_c.parse_chunks inst g chunks im ce = ok (.Ok r)) :
    ∃ x, ConLeche.Frontend.parseChunks (absChunks chunks) im ce = .ok x ∧
      ParseResultSim r x := by
  rw [frontend.export_c.parse_chunks.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨st, hinit, h⟩ := h
  rw [ConLeche.Frontend.parseChunks]
  have hres := parse_chunks_loop_refines ing _ chunks st
    (ConLeche.Frontend.StateD.init im ce) (alloc.vec.Vec.new Std.U8) 0#u64 0#u64
    (alloc.vec.Vec.len chunks) 0#usize r (ing.state_d_init im ce st hinit)
    (by simp [alloc.vec.Vec.len]) rfl h
  rw [show absChunk (alloc.vec.Vec.new Std.U8) = ByteArray.empty from rfl] at hres
  simpa using hres

/-! ## The bytes of a list of chunks

`export_c::concat_bytes` (`ConLeche/Frontend/ExportC.lean:876-880`
`concatBytes`): what the chunks a handle hands out add up to.  Nothing in the
port's pipeline calls it — it is what con-leche's `parseChunks_ok_parseBytes`
is stated over — but the port carries it, so the tier states it. -/

private theorem concat_bytes_loop_refines (N : Nat) :
    ∀ (chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (out : alloc.vec.Vec Std.U8)
      (n i : Std.Usize) (v : alloc.vec.Vec Std.U8),
      n.val = chunks.val.length → n.val - i.val = N →
      frontend.export_c.concat_bytes_loop chunks out n i = ok v →
      absChunk v = absChunk out ++
        ConLeche.Frontend.concatBytes ((absChunks chunks).drop i.val) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro chunks out n i v hn hN h
    rw [frontend.export_c.concat_bytes_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, hc, s, hs, out1, hout1, i1, hi1, h⟩ := h
      obtain ⟨hilt, hdrop⟩ := chunks_drop_map_index absChunk hc
      have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
      have hsb : absBytes s = absChunk c := by
        apply absBytes_of_val
        simp only [alloc.vec.Vec.index,
          core.slice.index.SliceIndexRangeFullSlice.index, Result.ok.injEq] at hs
        rw [← hs]; rfl
      have hout : absChunk out1 = absChunk out ++ absChunk c := by
        rw [← hsb]
        exact absBytes_append_val (u8_extend_val hout1)
      have hres := ih (n.val - i1.val) (by scalar_tac) chunks out1 n i1 v hn rfl h
      simp only [absChunks] at hres hdrop ⊢
      rw [hres, hout, hi1v, hdrop, ConLeche.Frontend.concatBytes,
        ByteArray.append_assoc]
    · rename_i hge
      simp only [Result.ok.injEq] at h
      have hnil : (absChunks chunks).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absChunks, List.length_map]
        scalar_tac
      rw [hnil, ConLeche.Frontend.concatBytes, ← h]
      exact ByteArray.append_empty.symm

/-- **`export_c::concat_bytes` refines `ConLeche.Frontend.concatBytes`**
(`ConLeche/Frontend/ExportC.lean:876-880`). -/
theorem concat_bytes_refines {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    {v : alloc.vec.Vec Std.U8} (h : frontend.export_c.concat_bytes chunks = ok v) :
    absChunk v = ConLeche.Frontend.concatBytes (absChunks chunks) := by
  rw [frontend.export_c.concat_bytes] at h
  have hres := concat_bytes_loop_refines _ chunks (alloc.vec.Vec.new Std.U8)
    (alloc.vec.Vec.len chunks) 0#usize v (by simp [alloc.vec.Vec.len]) rfl h
  rw [hres, show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero,
    show absChunk (alloc.vec.Vec.new Std.U8) = ByteArray.empty from rfl,
    ByteArray.empty_append]

/-! ## The built-in prelude

`prelude::builtin_prelude_e` (`ConLeche/Frontend/Prelude.lean:64-68`
`builtinPreludeE`).  **Parametric in the bytes**, the shape tasks #74/#75 used
for the pins and task #85 for `conron.*_parsed`: the port's prelude constant is
a generated `[u8; 16 922]` and con-leche's is an `include_str`, and identifying
the two in the kernel is out of reach (`AENEAS_FINDINGS.md` §3.8 — a string
constant of that size expands quadratically).  So the statement names the
port's constant only through its own run, and **evaluates nothing**. -/

/-- **`prelude::builtin_prelude_e`, accept direction, at the bytes the port's
constant holds** (`ConLeche/Frontend/Prelude.lean:64-68` `builtinPreludeE`).
con-leche's `builtinPreludeE` is `(fun r => ⟨r.decls⟩) <$> parseExportD
builtinPreludeText`; this is the same map at whatever bytes
`prelude_text::prelude_text()` returns. -/
theorem builtin_prelude_e_refines
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {M : Type} {inst : frontend.in_model_rec.Modeller M} {m : M}
    (ing : ParseIngredients R inst m) {pre : frontend.prepare.PreludeIx}
    (h : frontend.prelude.builtin_prelude_e inst m = ok (.Ok pre)) :
    ∃ text x, frontend.prelude_text.prelude_text = ok text ∧
      ConLeche.Frontend.parseBytes (absChunk text) true false = .ok x ∧
      pre.decls.val.map absDeclaration = x.decls.toList := by
  rw [frontend.prelude.builtin_prelude_e.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨text, htext, r, hr, h⟩ := h
  have hsb : absBytes (alloc.vec.Vec.deref text) = absChunk text := by
    apply absBytes_of_val
    simp [alloc.vec.Vec.deref]
  split at h
  · rename_i r1
    obtain ⟨x, hx, hsim⟩ := parse_bytes_refines ing hr
    refine ⟨text, x, htext, by rw [← hsb]; exact hx, ?_⟩
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h
    rw [← h]
    exact hsim.decls
  · exfalso; revert h; simp

/-! ## The wholesale parse of a string

`export_c::parse_export_d` (`ConLeche/Frontend/ExportC.lean:841-846`
`parseExportD`): `parse_bytes` of the argument's UTF-8.  Stated **at the bytes**
rather than at the string, for the reason the prelude is: the port's `&str` is
Aeneas's `Str`, whose `toStr` is the string's UTF-8 (`parse_export_d`'s own
note), and identifying an extracted `Str` constant with a Lean `String` costs
what `AENEAS_FINDINGS.md` §3.8 measures. `parse_export_d` has one caller inside
the core and it is the prelude, which goes through `parse_bytes` directly. -/

/-- **`export_c::parse_export_d`, accept direction**
(`ConLeche/Frontend/ExportC.lean:841-846` `parseExportD`). -/
theorem parse_export_d_refines
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g) {contents : Str} {im ce : Bool}
    {r : frontend.export_c.ParseResultD}
    (h : frontend.export_c.parse_export_d inst g contents im ce = ok (.Ok r)) :
    ∃ s x, core.str.Str.as_bytes contents = ok s ∧
      ConLeche.Frontend.parseBytes (absBytes s) im ce = .ok x ∧ ParseResultSim r x := by
  rw [frontend.export_c.parse_export_d] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨s, hs, h⟩ := h
  obtain ⟨x, hx, hsim⟩ := parse_bytes_refines ing h
  exact ⟨s, x, hs, hx, hsim⟩


/-! ## The error direction

The full-outcome convention of DESIGN.md §3, the other half: where the port's
parse returns an `.Err` whose kind `absErrKind` can name, con-leche throws at
that kind and at the same line.

Everything turns on `export_c::scan_err_to_check`, the arm task #87 added to
the port: a reader failure at a tag con-leche's reader also has becomes an
`internal`, and the port's own `ErrTag::IndexOverflow` becomes a `native`,
which `absErrKind` sends to `none` — so the claim is vacuous exactly where the
two readers may disagree (the module note). -/

/-- **`export_c::scan_err_to_check`, read as a kind.**  A mirrored tag gives an
`internal`; `ErrTag::IndexOverflow` gives a `native`, which claims nothing. -/
private theorem scan_err_to_check_mirror {e : frontend.scan_types.ScanErr}
    {ce : kernel.core_types.CheckError} {k : ErrKind}
    (h : frontend.export_c.scan_err_to_check e = ok ce)
    (hk : absErrKind ce = some k) :
    k = .internal ∧ ∃ t, absErrTag e.what = some t := by
  rw [frontend.export_c.scan_err_to_check] at h
  split at h <;>
    (rename_i he
     simp only [bind_eq_ok_iff, kernel.core_types.internal, kernel.core_types.native,
       Result.ok.injEq] at h
     obtain ⟨v, -, hce⟩ := h
     subst hce) <;>
    simp_all [absErrKind, absErrTag]

/-- **`export_c::line_err_to_check`, read as a kind and a line.**  The message
arm is con-leche's `throw`, the verdict arm con-leche's own `.inr`, and both
land at the line the record was read at. -/
private theorem line_err_to_check_mirror {γ : Type}
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {st' : frontend.export_c.StateD} {le : frontend.export_c.LineErr}
    {ln : Std.U64} {p : kernel.core_types.CheckError × Std.U64}
    {x : ConLeche.Frontend.M (ConLeche.Frontend.StateD ⊕ ConLeche.Frontend.RecordVerdict)}
    {f : ConLeche.Frontend.StateD → Except (ConLeche.CheckError × Nat) γ}
    (h : frontend.export_c.line_err_to_check le ln = ok p)
    (hsim : ApplyLineSim R (.Err le) st' x) :
    ParseErrSim p
      (match x with
       | .error msg => .error (.internal msg, ln.val)
       | .ok (.inr v) => .error (v.toError, ln.val)
       | .ok (.inl st) => f st) := by
  cases le with
  | Msg m =>
    obtain ⟨s, hs⟩ := hsim
    simp only [frontend.export_c.line_err_to_check, bind_eq_ok_iff,
      kernel.core_types.internal, Result.ok.injEq] at h
    obtain ⟨ce, hce, hp⟩ := h
    subst hce; subst hp
    rw [hs]
    exact ParseErrSim.mk rfl rfl rfl
  | Verdict v =>
    obtain ⟨lv, hlv, hkind⟩ := hsim
    rw [hlv]
    cases v with
    | Declined w =>
      cases lv with
      | declined s =>
        simp only [frontend.export_c.line_err_to_check,
          frontend.export.record_verdict_to_error, bind_eq_ok_iff,
          kernel.core_types.not_implemented, Result.ok.injEq] at h
        obtain ⟨ce, hce, hp⟩ := h
        subst hce; subst hp
        exact ParseErrSim.mk rfl rfl rfl
      | invalid s => exact absurd hkind (by simp [lVerdictKind, absVerdictKind])
    | Invalid w =>
      cases lv with
      | declined s => exact absurd hkind (by simp [lVerdictKind, absVerdictKind])
      | invalid s =>
        simp only [frontend.export_c.line_err_to_check,
          frontend.export.record_verdict_to_error, bind_eq_ok_iff,
          kernel.core_types.invalid, Result.ok.injEq] at h
        obtain ⟨ce, hce, hp⟩ := h
        subst hce; subst hp
        exact ParseErrSim.mk rfl rfl rfl

/-- **`export_c::apply_final_line`, error direction**
(`ConLeche/Frontend/ExportC.lean:765-775` `applyFinalLine`). -/
theorem apply_final_line_refines_err
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g)
    {st st' : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {b : Slice Std.U8} {i : Std.Usize} {ln : Std.U64}
    {p : kernel.core_types.CheckError × Std.U64} (hst : R st lst)
    (h : frontend.export_c.apply_final_line inst g st b i ln = ok (.Err p, st')) :
    ParseErrSim p
      (ConLeche.Frontend.applyFinalLine lst (absBytes b) (absPos i) ln.val) := by
  rw [frontend.export_c.apply_final_line.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨r, hr, h⟩ := h
  have hsim := ing.scan_line_fwd b i r hr
  rw [applyFinalLine_eq]
  split at h
  · rename_i q
    obtain ⟨r1, j⟩ := q
    simp only [uncurry_apply_pair, bind_eq_ok_iff] at h
    obtain ⟨⟨r2, st1⟩, happ, h⟩ := h
    simp only [uncurry_apply_pair] at h
    have hal := ing.apply_line st st1 lst r1 r2 hst happ
    split at h
    · exfalso; revert h; simp
    · rename_i le
      simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨p1, hp1, hp, -⟩ := h
      simp only [core.result.Result.Err.injEq] at hp
      subst hp
      simp only [show ConLeche.Frontend.scanLineFwd (absBytes b) (absPos i)
            = .ok (absLineRec r1) (absPos j) from hsim]
      exact line_err_to_check_mirror (f := fun st => .ok st) hp1 hal
  · rename_i se
    rw [bind_eq_ok_iff] at h
    obtain ⟨i1, -, h⟩ := h
    rw [bind_eq_ok_iff] at h
    obtain ⟨ce, hce, h⟩ := h
    simp only [Result.ok.injEq, Prod.mk.injEq,
      core.result.Result.Err.injEq] at h
    obtain ⟨hp, -⟩ := h
    subst hp
    intro k hk
    obtain ⟨hkint, t, ht⟩ := scan_err_to_check_mirror hce hk
    have hscan : ConLeche.Frontend.scanLineFwd (absBytes b) (absPos i)
        = .err ⟨se.offset.val, t⟩ :=
      hsim ⟨se.offset.val, t⟩ (by rw [absScanErr, ht]; rfl)
    rw [hscan]
    exact ⟨_, rfl, hkint.symm, rfl⟩


private theorem feed_chunk_loop_refines_err
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g) (N : Nat) :
    ∀ (st st' : frontend.export_c.StateD) (lst : ConLeche.Frontend.StateD)
      (b : Slice Std.U8) (i : Std.Usize) (ln : Std.U64)
      (p : kernel.core_types.CheckError × Std.U64),
      R st lst → (Slice.len b).val - i.val = N →
      frontend.export_c.feed_chunk_loop inst g st b i ln = ok (.Err p, st') →
      ParseErrSim p (ConLeche.Frontend.feedChunk lst (absBytes b) (absPos i) ln.val) := by
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
        · exfalso; revert h; simp
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
            · rename_i hge
              rw [dif_neg (show ¬ (absPos i < absPos j) from
                fun hc => absurd (absPos_lt.mp hc) (by scalar_tac))]
              rw [bind_eq_ok_iff] at h
              obtain ⟨s, -, h⟩ := h
              rw [bind_eq_ok_iff] at h
              obtain ⟨v, -, h⟩ := h
              rw [bind_eq_ok_iff] at h
              obtain ⟨ce, hce, h⟩ := h
              rw [bind_eq_ok_iff] at h
              obtain ⟨i2, hi2, h⟩ := h
              simp only [Result.ok.injEq, Prod.mk.injEq,
                core.result.Result.Err.injEq] at h
              obtain ⟨hp, -⟩ := h
              subst hp
              simp only [kernel.core_types.internal, Result.ok.injEq] at hce
              subst hce
              exact ParseErrSim.mk rfl rfl
                (by simp [HashMap.uscalar_add_eq hi2])
            · rename_i hge
              rw [dif_pos (show absPos i < absPos j from absPos_lt.mpr (by scalar_tac))]
              simp only [bind_eq_ok_iff] at h
              obtain ⟨ln1, hln1, h⟩ := h
              have hres := ih ((Slice.len b).val - j.val) (by scalar_tac) st1 st' lst2 b j
                ln1 p hrel rfl h
              rw [show ln.val + 1 = ln1.val from (HashMap.uscalar_add_eq hln1).symm]
              exact hres
          · rename_i le
            rw [bind_eq_ok_iff] at h
            obtain ⟨i2, hi2, h⟩ := h
            rw [bind_eq_ok_iff] at h
            obtain ⟨p1, hp1, h⟩ := h
            simp only [Result.ok.injEq, Prod.mk.injEq,
              core.result.Result.Err.injEq] at h
            obtain ⟨hp, -⟩ := h
            subst hp
            rw [show ln.val + 1 = i2.val from (HashMap.uscalar_add_eq hi2).symm]
            exact line_err_to_check_mirror
              (f := fun st => if _hj : absPos i < absPos j then
                ConLeche.Frontend.feedChunk st (absBytes b) (absPos j) (i2.val)
              else .error (.internal "the line scanner made no progress", i2.val))
              hp1 hal
      · rename_i se
        simp only [bind_eq_ok_iff] at h
        obtain ⟨b1, hb1, h⟩ := h
        split at h
        · rename_i hb1t
          rw [show b1 = true by simpa using hb1t] at hb1
          rw [bind_eq_ok_iff] at h
          obtain ⟨i2, -, h⟩ := h
          rw [bind_eq_ok_iff] at h
          obtain ⟨ce, hce, h⟩ := h
          rw [bind_eq_ok_iff] at h
          obtain ⟨i3, hi3, h⟩ := h
          simp only [Result.ok.injEq, Prod.mk.injEq,
            core.result.Result.Err.injEq] at h
          obtain ⟨hp, -⟩ := h
          subst hp
          intro k hk
          obtain ⟨hkint, t, ht⟩ := scan_err_to_check_mirror hce hk
          have hscan : ConLeche.Frontend.scanLineFwd (absBytes b) (absPos i)
              = .err ⟨se.offset.val, t⟩ :=
            hsim ⟨se.offset.val, t⟩ (by rw [absScanErr, ht]; rfl)
          have hnl : ConLeche.Frontend.newlineFrom (absBytes b) (absPos i) = true :=
            (ing.newline_from b i true hb1).symm
          rw [hscan]
          simp only [hnl, if_true]
          exact ⟨_, rfl, hkint.symm, by simp [HashMap.uscalar_add_eq hi3]⟩
        · exfalso; revert h; simp
    · exfalso; revert h; simp

/-- **`export_c::feed_chunk`, error direction**
(`ConLeche/Frontend/ExportC.lean:777-811` `feedChunk`). -/
theorem feed_chunk_refines_err
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g)
    {st st' : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {b : Slice Std.U8} {i : Std.Usize} {ln : Std.U64}
    {p : kernel.core_types.CheckError × Std.U64} (hst : R st lst)
    (h : frontend.export_c.feed_chunk inst g st b i ln = ok (.Err p, st')) :
    ParseErrSim p (ConLeche.Frontend.feedChunk lst (absBytes b) (absPos i) ln.val) :=
  feed_chunk_loop_refines_err ing _ st st' lst b i ln p hst rfl h


/-- Error propagation through a bind, the move every arm makes. -/
theorem ParseErrSim.bind {γ δ : Type} {e : kernel.core_types.CheckError × Std.U64}
    {x : Except (ConLeche.CheckError × Nat) γ} (h : ParseErrSim e x)
    (f : γ → Except (ConLeche.CheckError × Nat) δ) : ParseErrSim e (x >>= f) :=
  h.trans (fun le hx => by rw [hx]; rfl)

/-- **`export_c::parse_bytes_final`, error direction**
(`ConLeche/Frontend/ExportC.lean:834-838`, the cited tail of `parseBytes`). -/
theorem parse_bytes_final_refines_err
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g)
    {st : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {b : Slice Std.U8} {tail : Std.Usize} {ln : Std.U64}
    {p : kernel.core_types.CheckError × Std.U64} (hst : R st lst)
    (h : frontend.export_c.parse_bytes_final inst g st b tail ln = ok (.Err p)) :
    ParseErrSim p (parseBytesFinal lst (absBytes b) (absPos tail) ln.val) := by
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
    · exfalso; revert h; simp
    · simp only [Result.ok.injEq, core.result.Result.Err.injEq] at h
      subst h
      rw [show ln.val + 1 = i1.val from (HashMap.uscalar_add_eq hi1).symm]
      exact (apply_final_line_refines_err ing hst hfin).bind _
  · exfalso; revert h; simp

/-- **`export_c::parse_bytes`, error direction**
(`ConLeche/Frontend/ExportC.lean:827-839` `parseBytes`).  The size guard cannot
fire on a `Slice` — a slice's length is at most `Usize.max` — so the port's
`.Err` is con-leche's, line for line. -/
theorem parse_bytes_refines_err
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g) {b : Slice Std.U8} {im ce : Bool}
    {p : kernel.core_types.CheckError × Std.U64}
    (h : frontend.export_c.parse_bytes inst g b im ce = ok (.Err p)) :
    ParseErrSim p (ConLeche.Frontend.parseBytes (absBytes b) im ce) := by
  rw [frontend.export_c.parse_bytes.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨i1, hi1, i2, hi2, h⟩ := h
  rw [parseBytes_eq, if_neg (by have := absBytes_size_lt b; omega)]
  simp only [lift_eq, Result.ok.injEq] at hi1
  split at h
  · exfalso
    rename_i hguard
    have hc := usize_size_val hi2
    have hsz := absBytes_size_lt b
    rw [absBytes_size] at hsz
    have hi1v : i1.val = b.val.length := by
      rw [← hi1]; exact cast_u128_val (Slice.len b) (usize_val_lt_u128 (Slice.len b))
    have : i1.val ≥ i2.val := by scalar_tac
    omega
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
      exact parse_bytes_final_refines_err ing hrel h
    · simp only [Result.ok.injEq, core.result.Result.Err.injEq] at h
      subst h
      have hfe := feed_chunk_refines_err ing (ing.state_d_init im ce st hinit) hfeed
      simp only [show absPos (0#usize) = 0 from rfl,
        show ((0#u64 : Std.U64)).val = 0 from rfl] at hfe
      exact hfe.bind _

/-- **`export_c::chunk_finish`, error direction**
(`ConLeche/Frontend/ExportC.lean:867-874` `chunkFinish`). -/
theorem chunk_finish_refines_err
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g)
    {st : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {carry : Slice Std.U8} {ln : Std.U64}
    {p : kernel.core_types.CheckError × Std.U64} (hst : R st lst)
    (h : frontend.export_c.chunk_finish inst g st carry ln = ok (.Err p)) :
    ParseErrSim p (ConLeche.Frontend.chunkFinish lst (absBytes carry) ln.val) := by
  rw [frontend.export_c.chunk_finish.eq_def] at h
  simp only [] at h
  rw [ConLeche.Frontend.chunkFinish]
  split at h
  · exfalso; revert h; simp
  · rename_i he
    rw [if_neg (fun hc => he ((absBytes_isEmpty carry).mp hc))]
    simp only [bind_eq_ok_iff] at h
    obtain ⟨i1, hi1, ⟨rr, st1⟩, hfin, h⟩ := h
    simp only [uncurry_apply_pair] at h
    split at h
    · exfalso; revert h; simp
    · simp only [Result.ok.injEq, core.result.Result.Err.injEq] at h
      subst h
      rw [show ln.val + 1 = i1.val from (HashMap.uscalar_add_eq hi1).symm]
      have hafl := apply_final_line_refines_err ing hst hfin
      simp only [show absPos (0#usize) = 0 from rfl] at hafl
      exact hafl.trans (fun le hx => by rw [hx])

set_option maxRecDepth 20000 in
/-- **`export_c::chunk_step`, error direction**
(`ConLeche/Frontend/ExportC.lean:848-865` `chunkStep`). -/
theorem chunk_step_refines_err
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g)
    {st st' : frontend.export_c.StateD} {lst : ConLeche.Frontend.StateD}
    {carry : alloc.vec.Vec Std.U8} {ln total : Std.U64} {buf0 : Slice Std.U8}
    {p : kernel.core_types.CheckError × Std.U64} (hst : R st lst)
    (h : frontend.export_c.chunk_step inst g st carry ln total buf0 = ok (.Err p, st')) :
    ParseErrSim p (ConLeche.Frontend.chunkStep lst (absChunk carry) ln.val total.val
      (absBytes buf0)) := by
  rw [frontend.export_c.chunk_step.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨i, hi, i2, hi2, i3, hi3, i4, hi4, h⟩ := h
  rw [ConLeche.Frontend.chunkStep]
  simp only [lift_eq, Result.ok.injEq] at hi hi2
  have hc := usize_size_val hi4
  have h3 := HashMap.uscalar_add_eq hi3
  have hiv : i.val = total.val := by
    rw [← hi]; exact cast_u128_val total (u64_val_lt_u128 total)
  have hi2v : i2.val = buf0.val.length := by
    rw [← hi2]
    exact cast_u128_val (Slice.len buf0) (usize_val_lt_u128 (Slice.len buf0))
  split at h
  · rename_i hguard
    have hge : i4.val ≤ i3.val := (Std.UScalar.le_equiv _ _).mp hguard
    rw [if_pos (by rw [absBytes_size]; omega)]
    rw [bind_eq_ok_iff] at h
    obtain ⟨se, hse, h⟩ := h
    simp only [Result.ok.injEq, Prod.mk.injEq,
      core.result.Result.Err.injEq] at h
    obtain ⟨hp, -⟩ := h
    subst hp
    exact size_error_refines hse rfl
  · rename_i hguard
    have hlt : i3.val < i4.val := by
      by_contra hcc
      exact hguard ((Std.UScalar.le_equiv _ _).mpr (by omega))
    have hsz : ¬ (total.val + (absBytes buf0).size ≥ USize.size) := by
      rw [absBytes_size]; omega
    rw [if_neg hsz]
    clear hsz hlt hc h3 hiv hi2v hi hi2 hi3 hi4 hguard
    simp only [bind_eq_ok_iff] at h
    obtain ⟨buf, hbuf, s, hs, ⟨rr, st1⟩, hfeed, h⟩ := h
    have hsval : s.val = buf.val := by
      simp only [alloc.vec.Vec.index,
        core.slice.index.SliceIndexRangeFullSlice.index, Result.ok.injEq] at hs
      rw [← hs]; rfl
    have hbufb : (if (absChunk carry).isEmpty then absBytes buf0
                  else absChunk carry ++ absBytes buf0) = absBytes s := by
      split at hbuf
      · rename_i hce
        rw [if_pos (by
          simp only [ByteArray.isEmpty, absChunk, ByteArray.size, beq_iff_eq]
          simp only [alloc.vec.Vec.len] at hce
          scalar_tac)]
        have hv : s.val = buf0.val := by rw [hsval, u8_to_vec_val hbuf]
        show absBytes buf0 = absBytes s
        rw [absBytes, absBytes, hv]
      · rename_i hce
        rw [if_neg (by
          simp only [ByteArray.isEmpty, absChunk, ByteArray.size, beq_iff_eq]
          simp only [alloc.vec.Vec.len] at hce
          intro hc; exact hce (by scalar_tac))]
        exact (absBytes_append_val (by rw [hsval, u8_extend_val hbuf])).symm
    rw [hbufb]
    simp only [uncurry_apply_pair] at h
    split at h
    · rename_i t
      obtain ⟨ln2, tail⟩ := t
      exfalso; revert h
      simp [bind_eq_ok_iff]
    · simp only [Result.ok.injEq, Prod.mk.injEq,
        core.result.Result.Err.injEq] at h
      obtain ⟨hp, -⟩ := h
      subst hp
      have hfe := feed_chunk_refines_err ing hst hfeed
      simp only [show absPos (0#usize) = 0 from rfl] at hfe
      exact hfe.trans (fun le hx => by simp only [hx])

private theorem parse_chunks_loop_refines_err
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g) (N : Nat) :
    ∀ (chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (st : frontend.export_c.StateD)
      (lst : ConLeche.Frontend.StateD) (carry : alloc.vec.Vec Std.U8)
      (ln total : Std.U64) (n i : Std.Usize)
      (p : kernel.core_types.CheckError × Std.U64),
      R st lst → n.val = chunks.val.length → n.val - i.val = N →
      frontend.export_c.parse_chunks_loop inst g chunks st carry ln total n i
        = ok (.Err p) →
      ParseErrSim p (ConLeche.Frontend.parseChunks.go lst (absChunk carry) ln.val
        total.val ((absChunks chunks).drop i.val)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro chunks st lst carry ln total n i p hst hn hN h
    rw [frontend.export_c.parse_chunks_loop.eq_def] at h
    split at h
    · rename_i hlt
      simp only [bind_eq_ok_iff] at h
      obtain ⟨v, hv, s, hs, ⟨rr, st1⟩, hstepr, h⟩ := h
      obtain ⟨hilt, hdrop⟩ := chunks_drop_map_index absChunk hv
      rw [absChunks, hdrop, ConLeche.Frontend.parseChunks.go]
      have hsb : absBytes s = absChunk v := by
        apply absBytes_of_val
        simp only [alloc.vec.Vec.index,
          core.slice.index.SliceIndexRangeFullSlice.index, Result.ok.injEq] at hs
        rw [← hs]; rfl
      rw [← hsb]
      simp only [uncurry_apply_pair] at h
      split at h
      · rename_i t
        obtain ⟨c2, l, t1⟩ := t
        obtain ⟨lst1, hcs, hrel⟩ := chunk_step_refines ing hst hstepr
        rw [hcs]
        simp only [uncurry_apply_pair, bind_eq_ok_iff] at h
        obtain ⟨i1, hi1, h⟩ := h
        have hi1v : i1.val = i.val + 1 := HashMap.uscalar_add_eq hi1
        have hres := ih (n.val - i1.val) (by scalar_tac) chunks st1 lst1 c2 l t1 n i1 p
          hrel hn rfl h
        rw [hi1v] at hres
        exact hres
      · simp only [Result.ok.injEq, core.result.Result.Err.injEq] at h
        subst h
        exact (chunk_step_refines_err ing hst hstepr).trans (fun le hx => by rw [hx])
    · rename_i hge
      simp only [bind_eq_ok_iff] at h
      obtain ⟨s, hs, h⟩ := h
      have hnil : (absChunks chunks).drop i.val = [] := by
        apply List.drop_eq_nil_of_le
        simp only [absChunks, List.length_map]
        scalar_tac
      rw [hnil, ConLeche.Frontend.parseChunks.go]
      have hsb : absBytes s = absChunk carry := by
        apply absBytes_of_val
        simp only [alloc.vec.Vec.index,
          core.slice.index.SliceIndexRangeFullSlice.index, Result.ok.injEq] at hs
        rw [← hs]; rfl
      rw [← hsb]
      exact chunk_finish_refines_err ing hst h

/-- **The streaming parse, error direction**
(`ConLeche/Frontend/ExportC.lean:882-901` `parseChunks`): the port's parse fails
at the kind and the line con-leche's fails at. -/
theorem parse_chunks_refines_err
    {R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop}
    {G : Type} {inst : frontend.in_model_rec.Modeller G} {g : G}
    (ing : ParseIngredients R inst g)
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)} {im ce : Bool}
    {p : kernel.core_types.CheckError × Std.U64}
    (h : frontend.export_c.parse_chunks inst g chunks im ce = ok (.Err p)) :
    ParseErrSim p (ConLeche.Frontend.parseChunks (absChunks chunks) im ce) := by
  rw [frontend.export_c.parse_chunks.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨st, hinit, h⟩ := h
  rw [ConLeche.Frontend.parseChunks]
  have hres := parse_chunks_loop_refines_err ing _ chunks st
    (ConLeche.Frontend.StateD.init im ce) (alloc.vec.Vec.new Std.U8) 0#u64 0#u64
    (alloc.vec.Vec.len chunks) 0#usize p (ing.state_d_init im ce st hinit)
    (by simp [alloc.vec.Vec.len]) rfl h
  rw [show absChunk (alloc.vec.Vec.new Std.U8) = ByteArray.empty from rfl] at hres
  simpa using hres


/-! ## The two fields `Refine/Frontend/StateDR.lean` discharges

Fields 5 and 6 of `ParseIngredients` at `R := StateDRel`, so that the shapes
are checked here rather than in the instance the coordinator writes. -/

/-- `ParseIngredients.state_d_init` at `StateDRel`. -/
theorem parse_result_state_d_init {im ce : Bool} {st : frontend.export_c.StateD}
    (h : frontend.export_c.state_d_init im ce = ok st) :
    StateDRel st (ConLeche.Frontend.StateD.init im ce) := state_d_init_refines h

/-- `ParseIngredients.parse_result_of_state` at `StateDRel`: `ParseResultSim`
is `Refine/Frontend/StateDR.lean`'s six clauses, in order. -/
theorem parse_result_of_state_sim {st : frontend.export_c.StateD}
    {lst : ConLeche.Frontend.StateD} {r : frontend.export_c.ParseResultD}
    (hrel : StateDRel st lst) (h : frontend.export_c.parse_result_of_state st = ok r) :
    ParseResultSim r (ConLeche.Frontend.ParseResultD.ofState lst) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := parse_result_of_state_refines hrel h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

The headline and its prelude twin: Lean's own three axioms and nothing else.
Nothing here evaluates the scanner's key table or the prelude text — the
prelude statement is parametric in the bytes and `parse_bytes_refines` holds
for every byte slice — so the census is the one phase 1 pinned for
`Refine/Frontend/Chunks.lean`'s three headlines. -/

/-- info: 'ConRon.Refine.Frontend.parse_chunks_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_chunks_refines

/-- info: 'ConRon.Refine.Frontend.parse_bytes_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_bytes_refines

/-- info: 'ConRon.Refine.Frontend.builtin_prelude_e_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms builtin_prelude_e_refines

/-- info: 'ConRon.Refine.Frontend.parse_chunks_refines_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parse_chunks_refines_err

end ConRon.Refine.Frontend

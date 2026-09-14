/-
`ConRon.Refine.Frontend.ChunksR` — **the top of the parse, exact against
con-leche** (task #87, phase 3).

Phase 1's `ConRon/Refine/Frontend/Chunks.lean` proved the port's parser *well
formed* — `apply_line_wf`, `feed_chunk_wf`, `parse_bytes_wf`,
`parse_chunks_wf`, `builtin_prelude_e_wf`, statements about the port alone.
This file proves the same five functions **exact**: for the same bytes, the
port's parse is con-leche's `parseChunks` of the abstracted chunks, and it
errors where con-leche errors.

Port: `crates/con-ron-core/src/frontend/export_c.rs:2399-2710` and
`crates/con-ron-core/src/frontend/prelude.rs`.
con-leche: `ConLeche/Frontend/ExportC.lean:732-935` and
`ConLeche/Frontend/Prelude.lean`.

## What this file gives the rest of the tier

* `ModellerRefines` — **the canonical hypothesis about the unverified
  modeller** (the exactness twin of `Frontend.ModellerWF`,
  `Refine/Frontend/Base.lean`).  `Refine/Frontend/IndR.lean` declares a local
  copy while this file is being written; they are to be unified on this one.
* `absParseResultD` — `export_c::ParseResultD` as con-leche's, and
  `ParseResultSim`, the relation actually claimed of it.
* `ParseErrSim` / `ParseSim` / `ParseOk` — the parse tier's outcome vocabulary,
  over `Except (CheckError × Nat)`.
* `LineErrSim` / `ApplyLineSim` — the `M`-and-verdict relation `apply_line`
  is stated in.  **`Refine/Frontend/StateDR.lean` owns this**; it is declared
  here only because this file had to be stated before that one existed.
* `ParseIngredients R inst g` — the lower tier's lemmas as named `Prop`s, one
  field per lemma, in the shape `Refine/IndSpec.lean` fixed at task #56.
* `parse_chunks_refines` — **the lemma the whole task's headline composes
  with**.

## The one use of con-leche's `Scan/Equiv` tier

con-leche's `applyFinalLine` and `feedChunk` read lines with `scanLineSpec`,
the naive reference of `ConLeche/Frontend/Scan/Naive.lean`; a `@[csimp]`,
`ConLeche.Frontend.scanLineSpec_eq_scanLineFwd`
(`ConLeche/Frontend/Scan/Equiv.lean:1002`), makes `scanLineFwd` what the
*compiler* runs, and the port is a port of `scanLineFwd`.  `scanLineSpec` is
rewritten to `scanLineFwd` **exactly twice** — in `applyFinalLine_scan` and
`feedChunk_scan` below, the two unfolding lemmas every other proof in the
parser's phase-3 tier goes through — and nowhere else.  That is the only use
of con-leche's whole `Scan/Equiv` tier in the port's proof.

## The port's own scanner failure, and what it costs the error direction

`scan_types::ErrTag::IndexOverflow` is con-ron's own tag (`scan_types.rs`'s
module note, deviation 1; `Refine/Frontend/Abs.lean`'s note): the port reads a
stream index into a `u64` and refuses one that does not fit, where con-leche
reads a `Nat` and cannot fail.  `absErrTag` sends it to `none`, so
`ScanErrSim` claims nothing there — which is right at the scanner.

**Above the scanner it is not free.**  `apply_final_line` and `feed_chunk`
render *every* scan error through `scan_err_render` into
`core_types::internal(…)`, and `absErrKind (Internal _) = some .internal`: a
full-outcome `.Err` claim at those two sites therefore asserts that con-leche
throws, which for an `IndexOverflow` is false (con-leche's reader returns
`.ok` on the same bytes).  So:

* the **accept** direction is unconditional, and needs one extra fact of the
  scanner — `ParseIngredients.scan_line_fwd_tail`, *"a reader failure with no
  newline ahead is an incomplete tail for con-leche's reader too"* — which is
  what makes the port's `Ok (line_no, i)` agree with con-leche's;
* the **error** direction is stated under `ScanMirrors b`, *"on this buffer
  the port's line reader never fails at a tag con-leche does not have"*.

`ScanMirrors` disappears the day the port spells an `IndexOverflow` as
`core_types::native(…)` rather than `internal(…)` in those two arms — the
standard vocabulary then covers it with no proof change.  Reported to the
coordinator; a Rust change is not this file's to make.

## `sorry` count in this file: 0
-/
import ConRon.Refine.Frontend.Abs
import ConRon.Refine.HashMapWF
import ConLeche.Frontend.Prelude
import ConLeche.Frontend.Scan.Equiv

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.Frontend

/-! ## The unverified modeller, exactly

`Frontend.ModellerWF` (`Refine/Frontend/Base.lean`) is phase 1's one line about
`in_model_rec::Modeller`: whatever `generate` returns is well formed.  This is
its phase-3 twin: whatever `generate` returns is what
`ConLeche.Frontend.InModel.generate` returns.

The block is abstracted here (`absBlockRec`); the **context** is not.  The
port's `ModelCtx` holds three `ron::HashMap`s and con-leche's `InModel.Ctx`
three *functions* (`InModel/Mutual.lean:103-108`), so the bridge is a relation
and it is built out of the parse state — `export_c::state_model_ctx` against
con-leche's inline `{ tbl := fun n => st.constTypes[n]?, … }`
(`ExportC.lean:603-607`).  That relation belongs with `StateDRel`, so
`ModellerRefines` takes it as a parameter and this file never names a field of
either record. -/

/-- `in_model_rec::IndTypeRec` (`ConLeche/Frontend/InModel/Mutual.lean:66-73`). -/
def absInModelIndTypeRec (t : frontend.in_model_rec.IndTypeRec) :
    ConLeche.Frontend.InModel.IndTypeRec :=
  { cv := absConstantVal t.cv, nP := t.n_p.val, nIdx := t.n_idx.val,
    ctors := absNames t.ctors, isRec := t.is_rec, isReflexive := t.is_reflexive,
    numNested := t.num_nested.val }

/-- `in_model_rec::IndCtorRec` (`ConLeche/Frontend/InModel/Mutual.lean:76-80`). -/
def absInModelIndCtorRec (c : frontend.in_model_rec.IndCtorRec) :
    ConLeche.Frontend.InModel.IndCtorRec :=
  { cv := absConstantVal c.cv, nP := c.n_p.val, nF := c.n_f.val }

/-- `in_model_rec::IndRecRec` (`ConLeche/Frontend/InModel/Mutual.lean:84-91`). -/
def absInModelIndRecRec (r : frontend.in_model_rec.IndRecRec) :
    ConLeche.Frontend.InModel.IndRecRec :=
  { cv := absConstantVal r.cv, nP := r.n_p.val, nM := r.n_m.val, nm := r.nm.val,
    nI := r.n_i.val, rules := r.rules.val.map absRecRule }

/-- `in_model_rec::BlockRec` (`ConLeche/Frontend/InModel/Mutual.lean:94-99`). -/
def absBlockRec (b : frontend.in_model_rec.BlockRec) :
    ConLeche.Frontend.InModel.BlockRec :=
  { types := b.types.val.map absInModelIndTypeRec,
    ctors := b.ctors.val.map absInModelIndCtorRec,
    recs := b.recs.val.map absInModelIndRecRec }

/-- **The residue, exactly** (DESIGN.md §3's ruling of 2026-09-13: *"leave the
modeller unverified if you can"*).  The exactness twin of
`Frontend.ModellerWF`: at related contexts and the same block,
`in_model_rec::Modeller::generate` returns what
`ConLeche.Frontend.InModel.generate` returns, and declines where it declines.

The decline's *text* is not compared — the port carries `Vec<u32>` code points
and con-leche a `String`, and DESIGN.md §3.1's ruling is that message strings
never are.  `CtxRel` is the context bridge `Refine/Frontend/StateDR.lean`
builds out of `StateDRel`; nothing here reads a field of either context. -/
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
dump's field, is not ported"*), so **`absParseResultD` puts `#[]` there**.
That is this file's one abstraction deviation, and `ParseResultSim` below
carries no clause for the field: nothing downstream of the parse reads it. -/

/-- The census's declines, names and reasons (`Types.lean:250-251`). -/
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
unchanged, with the line number claimed alongside the kind. -/

/-- *"If the port's parse error has a con-leche kind, con-leche throws there,
at that kind and at the same line."*  A `Native` error claims nothing, exactly
as `Refine/Abs.lean`'s `ErrSim`. -/
def ParseErrSim {γ : Type} (e : kernel.core_types.CheckError × Std.U64)
    (x : Except (ConLeche.CheckError × Nat) γ) : Prop :=
  ∀ k, absErrKind e.1 = some k →
    ∃ le, x = .error le ∧ lErrKind le.1 = k ∧ le.2 = e.2.val

theorem ParseErrSim.mk {γ : Type} {e : kernel.core_types.CheckError × Std.U64}
    {x : Except (ConLeche.CheckError × Nat) γ} {le : ConLeche.CheckError × Nat}
    (hx : x = .error le) (hk : absErrKind e.1 = some (lErrKind le.1))
    (hl : le.2 = e.2.val) : ParseErrSim e x := by
  intro k hk'
  exact ⟨le, hx, by rw [hk] at hk'; exact Option.some_injective _ hk', hl⟩

theorem ParseErrSim.of_none {γ : Type} {e : kernel.core_types.CheckError × Std.U64}
    {x : Except (ConLeche.CheckError × Nat) γ} (h : absErrKind e.1 = none) :
    ParseErrSim e x := by intro k hk; rw [h] at hk; simp at hk

/-- **The accept half**, which is what the headline composes with: a port run
that returned a value is con-leche's, under `A`. -/
def ParseOk {α β : Type} (A : α → β → Prop)
    (o : core.result.Result α (kernel.core_types.CheckError × Std.U64))
    (x : Except (ConLeche.CheckError × Nat) β) : Prop :=
  ∀ r, o = .Ok r → ∃ y, x = .ok y ∧ A r y

/-- **The full outcome**: the accept half, and the mirrored error. -/
def ParseSim {α β : Type} (A : α → β → Prop)
    (o : core.result.Result α (kernel.core_types.CheckError × Std.U64))
    (x : Except (ConLeche.CheckError × Nat) β) : Prop :=
  ParseOk A o x ∧ ∀ e, o = .Err e → ParseErrSim e x

theorem ParseSim.ok {α β : Type} {A : α → β → Prop}
    {o : core.result.Result α (kernel.core_types.CheckError × Std.U64)}
    {x : Except (ConLeche.CheckError × Nat) β} (h : ParseSim A o x) :
    ParseOk A o x := h.1

/-! ## The `M`-and-verdict relation `apply_line` is stated in

**`Refine/Frontend/StateDR.lean` owns this.**  It is declared here because
this file had to be stated before that one existed; the coordinator unifies
the two.

con-leche's `applyLine` answers `M (StateD ⊕ RecordVerdict)`, i.e.
`Except String (StateD ⊕ RecordVerdict)` (`Export.lean:117`): a `throw` is the
parser's own message, and `.inr` is the record's verdict — a positive DECLINE
or a REJECT (`Export.lean:77-84`).  The port folds both into one
`export_c::LineErr` (`export_c.rs:165-168`) and resolves it against the line
with `line_err_to_check`.  Messages are never compared (DESIGN.md §3.1). -/

/-- `export_c::LineErr` against con-leche's `M`-and-verdict outcome. -/
def LineErrSim (e : frontend.export_c.LineErr)
    (x : ConLeche.Frontend.M
      (ConLeche.Frontend.StateD ⊕ ConLeche.Frontend.RecordVerdict)) : Prop :=
  match e with
  | .Msg _ => ∃ s, x = .error s
  | .Verdict (.Declined _) => ∃ s, x = .ok (.inr (.declined s))
  | .Verdict (.Invalid _) => ∃ s, x = .ok (.inr (.invalid s))

/-- **What `apply_line` claims** (`ExportC.lean:713-726` `applyLine`): the
state on success, the mirrored `M`-and-verdict outcome on failure. -/
def ApplyLineSim (R : frontend.export_c.StateD → ConLeche.Frontend.StateD → Prop)
    (o : core.result.Result Unit frontend.export_c.LineErr)
    (st' : frontend.export_c.StateD)
    (x : ConLeche.Frontend.M
      (ConLeche.Frontend.StateD ⊕ ConLeche.Frontend.RecordVerdict)) : Prop :=
  match o with
  | .Ok _ => ∃ lst, x = .ok (.inl lst) ∧ R st' lst
  | .Err e => LineErrSim e x

/-! ## The port's own reader failure

See the module note.  `ScanMirrors b` is *"on this buffer the port's line
reader never fails at a tag con-leche's has no counterpart for"*; it is the
hypothesis every **error** half in this file carries, and it is exactly what a
Rust change in `apply_final_line`/`feed_chunk`'s scan-error arms would make
unnecessary. -/

/-- *"The port's line reader never fails at its own tag on this buffer."* -/
def ScanMirrors (b : Slice Std.U8) : Prop :=
  ∀ i e, frontend.scan_fast.scan_line_fwd b i = ok (.Err e) →
    absErrTag e.what ≠ none

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

`R` is `StateDRel`, the parse state's relation; the structure is parametric in
it so that this file does not have to name a field of `export_c::StateD`. -/

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
the only lemma of this file that names `scanLineSpec`, and every other proof
goes through it. -/

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

end ConRon.Refine.Frontend

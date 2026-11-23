import ConRon.MainTheorem.Driver

/-!
# `ConRon.MainTheorem.CompareJson` — the walk of the extracted driver at `--compare -- C S`

**Task #171, lane F, slice 3a** (DESIGN.md §3.9).  The walk of `driver::cli::run_args` at the
argument list `["--compare", "--", c, s]`: an exit 0 there read the file `c` (so `fs` has it),
and its calls are one premise per step of `ConRon.MainTheorem.Stages.model_exists_compare`, at the
binary's start values and the embedded pins, with the challenge's chunks concatenating to the
file's bytes (`CompareJsonStages`).

| lemma | function |
|---|---|
| `fileChunks_file` | `export_c::parse_source` over `checker_io::FileChunks`: the file exists |
| `read_export_ok` | `compare_json::read_export` |
| `help_wanted_compare`, `parse_args_compare` | `cli::help_wanted`, `cli::parse_args` |
| `compare_verdict_zero`, `solution_failed_ne` | `compare_json::compare_verdict`, `solution_failed` |
| `compare_json_zero` | `compare_json::compare_json` |
| `compare_args_zero`, `run_args_compare` | `compare_json::compare_args`, `cli::run_args` |
-/

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon

open ConRon.Refine2 ConRon.Refine2.Frontend ConRon.Refine2.Frontend.Olean ConRon.MainTheorem.Stages

set_option autoImplicit false

/-! ## The stream's reads, when no file is given -/

section Reads

variable {S : Type} {io : frontend.checker_io.CheckerIo S} {fs : ConLeche.FS}

/-- **A parse over the file's reads, to an `Ok` with no read failure, read the file**: its
first read answered, so the snapshot has the file. -/
theorem fileChunks_file (hfs : AnswersAs io fs) {s : S} {file : alloc.vec.Vec Std.U32}
    {q : System.FilePath} (hq : PathRel file q)
    {pers : arena.store.PersTier} {ar ar' : arena.monad.AState} {r}
    {src' : frontend.checker_io.FileChunks S}
    (h : frontend.export_c.parse_source (fileSrc io) pers ar
      { fs := s, path := file, off := 0#u64, reads := 0#usize, err := none } = ok (.Ok r, ar', src'))
    (herr : src'.err = none) :
    ∃ b, fs.file q = some b := by
  rw [frontend.export_c.parse_source] at h
  obtain ⟨⟨r0, e0⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r0 with
  | Err e1 =>
    have := Result.ok_injective h
    simp at this
  | Ok v =>
    obtain ⟨buf, src1, hn, hcase⟩ := parse_source_loop_inv h
    obtain ⟨len, -, r, hr, hread⟩ := next_chunk_inv rfl hn
    rcases hread with ⟨e, rfl, hnil, he⟩ | ⟨rfl, -⟩
    · exfalso
      rcases hcase with ⟨-, ho⟩ | ⟨hne, -⟩
      · have ho' : src' = src1 := ho
        rw [ho', he] at herr; exact absurd herr (by simp)
      · exact hne hnil
    · obtain ⟨whole, hw, -⟩ := (hfs s).read_range hq _ len buf hr
      exact ⟨whole, hw⟩

/-- **A lean4export file read and parsed** (`compare_json::read_export`, `Ok`): the file is in
the snapshot, the reads are its chunks, each nonempty, then an empty one, they concatenate to
its bytes, and the parse is `parse_source` over them. -/
theorem read_export_ok (hfs : AnswersAs io fs) {s : S} {file : alloc.vec.Vec Std.U32}
    {q : System.FilePath} (hq : PathRel file q)
    {pers : arena.store.PersTier} {ar ar' : arena.monad.AState} {v : Bool} {r}
    (h : driver.compare_json.read_export io s pers ar file v = ok (.Ok r, ar')) :
    ∃ b, fs.file q = some b ∧ ∃ (chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8))
      (src' : frontend.checker_io.FileChunks S),
      ReadsAs (fileSrc io) { fs := s, path := file, off := 0#u64, reads := 0#usize, err := none }
        chunks.val ∧
      frontend.export_c.parse_source (fileSrc io) pers ar
        { fs := s, path := file, off := 0#u64, reads := 0#usize, err := none } = ok (.Ok r, ar', src') ∧
      ConLeche.Frontend.concatBytes (absChunks chunks) = b := by
  rw [driver.compare_json.read_export] at h
  obtain ⟨⟨read, ar1, src'⟩, h3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨fs', path', off', reads', err'⟩ := src'
  cases err' with
  | some m =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have := Result.ok_injective h
    simp at this
  | none =>
  cases read with
  | Err p =>
    obtain ⟨e, line⟩ := p
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have := Result.ok_injective h
    simp at this
  | Ok r1 =>
  have := Result.ok_injective h
  simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  obtain ⟨b, hb⟩ := fileChunks_file hfs hq h3 rfl
  obtain ⟨chunks, hreads, hcat⟩ := fileChunks_parse hfs hq hb h3 rfl
  exact ⟨b, hb, chunks, _, hreads, h3, hcat⟩

end Reads

/-! ## The argument list `["--compare", "--", c, s]` -/

section Cli

/-- A `cps_beq` against a different word answers `false`. -/
theorem beq_ne {d : alloc.vec.Vec Std.U32} {sl : Slice Std.U32} {bb : Bool}
    (h : frontend.text.cps_beq d sl = ok bb) (hne : d.val ≠ sl.val) : bb = false := by
  cases bb
  · rfl
  · exact absurd ((cps_beq_val h).mp rfl) hne

/-- The code points of `--compare`. -/
abbrev cpsCompare : List Std.U32 :=
  [45#u32, 45#u32, 99#u32, 111#u32, 109#u32, 112#u32, 97#u32, 114#u32, 101#u32]

/-- `["--compare", "--", c, s]`'s `argv`. -/
theorem argv_compare {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {c s : String}
    (h : ArgvOf argv ["--compare", "--", c, s]) :
    ∃ w d cf sf, argv.val = [w, d, cf, sf] ∧ w.val = cpsCompare ∧ d.val = [45#u32, 45#u32] ∧
      cf.val.map UScalar.val = c.toList.map Char.toNat ∧
      sf.val.map UScalar.val = s.toList.map Char.toNat := by
  unfold ArgvOf at h
  rcases hv : argv.val with _ | ⟨w, _ | ⟨d, _ | ⟨cf, _ | ⟨sf, _ | ⟨g, l⟩⟩⟩⟩⟩ <;> rw [hv] at h <;>
    simp at h
  refine ⟨w, d, cf, sf, rfl, vals_eq ?_, vals_eq ?_, h.2.2.1, h.2.2.2⟩
  · rw [h.1]; rfl
  · rw [h.2.1]; rfl

/-- **No `--help` before the `--`.** -/
theorem help_wanted_compare {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {w d cf sf}
    (hv : argv.val = [w, d, cf, sf]) (hw : w.val = cpsCompare) (hd : d.val = [45#u32, 45#u32])
    {b : Bool} (h : driver.cli.help_wanted argv = ok b) : b = false := by
  rw [driver.cli.help_wanted, driver.cli.help_wanted_loop] at h
  have hl := alloc.vec.Vec.len_val argv
  have hlen : (alloc.vec.Vec.len argv).val = 4 := by rw [hl]; simp [alloc.vec.Vec.length, hv]
  rw [ite_eq_right (by scalar_tac)] at h
  rw [vec_index_some (x := w) (by simp [hv]), bind_ok] at h
  simp only [lift, bind_ok] at h
  obtain ⟨b0, hb0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [beq_ne hb0 (by rw [hw]; simp [driver.cli.W_END, Array.to_slice])] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [beq_ne hb1 (by rw [hw]; simp [driver.cli.W_HELP, Array.to_slice])] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hi2v : i2.val = 1 := by rw [add_ok_val hi2]; rfl
  rw [driver.cli.help_wanted_loop, ite_eq_right (by scalar_tac),
    vec_index_some (x := d) (by simp [hv, hi2v]), bind_ok] at h
  simp only [lift, bind_ok] at h
  obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have : b2 = true := (cps_beq_val hb2).mpr (by rw [hd, w_end_val])
  simp only [this, ite_true] at h
  exact (Result.ok_injective h).symm

/-- **`parse_one` at `--compare`**: the flag set, nothing else read. -/
theorem parse_one_compare {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {w}
    (hw0 : argv.val[0]? = some w) (hw : w.val = cpsCompare) {a a' : driver.cli.Args}
    (h : driver.cli.parse_one a argv 0#usize = ok a') :
    a' = { a with compare := true } := by
  rw [driver.cli.parse_one, vec_index_some (x := w) hw0, bind_ok] at h
  simp only [lift, bind_ok] at h
  iterate 7
    obtain ⟨bb, hbb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [beq_ne hbb (by
      rw [hw]
      simp [driver.cli.W_VERIFIED, driver.cli.W_TRUSTED, driver.cli.W_PROGRESS,
        driver.cli.W_OLEAN, driver.cli.W_CHECK_GRAPH, driver.cli.W_MODULE,
        driver.cli.W_MODULAR, Array.to_slice])] at h
    simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨bb, hbb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have : bb = true := (cps_beq_val hbb).mpr (by
    rw [hw]; simp [driver.cli.W_COMPARE, Array.to_slice])
  simp only [this, ite_true] at h
  exact (Result.ok_injective h).symm

/-- **The parse of `["--compare", "--", c, s]`**: every default but `--compare`, and the two
files. -/
theorem parse_args_compare {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {w d cf sf}
    (hv : argv.val = [w, d, cf, sf]) (hw : w.val = cpsCompare) (hd : d.val = [45#u32, 45#u32])
    {a : driver.cli.Args} (h : driver.cli.parse_args argv = ok a) :
    a.bad = none ∧ a.check_graph = false ∧ a.olean = false ∧ a.compare = true ∧
      a.search_path.val = [] ∧ a.constants.val = [] ∧ a.module = false ∧ a.modular = false ∧
      a.scheduled = false ∧ a.trusted_path.val = [] ∧ a.verified = true ∧
      ∃ cf' sf', a.files.val = [cf', sf'] ∧ cf'.val = cf.val ∧
        sf'.val = sf.val := by
  rw [driver.cli.parse_args, driver.cli.args_default] at h
  obtain ⟨a0, ha0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n, -, ha0⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha0
  have ha0' := (Result.ok_injective ha0).symm
  subst ha0'
  rw [driver.cli.parse_args_loop] at h
  have hl := alloc.vec.Vec.len_val argv
  have hlen : (alloc.vec.Vec.len argv).val = 4 := by rw [hl]; simp [alloc.vec.Vec.length, hv]
  rw [ite_eq_right (by scalar_tac)] at h
  rw [vec_index_some (x := w) (by simp [hv]), bind_ok] at h
  simp only [lift, bind_ok] at h
  obtain ⟨bb, hbb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [beq_ne hbb (by rw [hw]; simp [driver.cli.W_END, Array.to_slice])] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨a1, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain rfl := parse_one_compare (by simp [hv]) hw h1
  obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hi2v : i2.val = 1 := by rw [add_ok_val hi2]; rfl
  rw [driver.cli.parse_args_loop, ite_eq_right (by scalar_tac),
    vec_index_some (x := d) (by simp [hv, hi2v]), bind_ok] at h
  simp only [lift, bind_ok] at h
  obtain ⟨bb2, hbb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have : bb2 = true := (cps_beq_val hbb2).mpr (by rw [hd, w_end_val])
  simp only [this, ite_true] at h
  obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hi3v : i3.val = 2 := by rw [add_ok_val hi3, hi2v]; rfl
  -- the files: `cf` and `sf`, copied
  rw [driver.cli.push_files, driver.cli.push_files_loop] at hv1
  rw [ite_eq_left (by scalar_tac), vec_index_some (x := cf) (by simp [hv, hi3v]), bind_ok] at hv1
  obtain ⟨cf', hcf', hv1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hv1
  obtain ⟨out1, hout1, hv1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hv1
  obtain ⟨i4, hi4, hv1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hv1
  have hi4v : i4.val = 3 := by rw [add_ok_val hi4, hi3v]; rfl
  rw [driver.cli.push_files_loop, ite_eq_left (by scalar_tac),
    vec_index_some (x := sf) (by simp [hv, hi4v]), bind_ok] at hv1
  obtain ⟨sf', hsf', hv1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hv1
  obtain ⟨out2, hout2, hv1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hv1
  obtain ⟨i5, hi5, hv1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hv1
  have hi5v : i5.val = 4 := by rw [add_ok_val hi5, hi4v]; rfl
  rw [driver.cli.push_files_loop, ite_eq_right (by scalar_tac)] at hv1
  have hv1' := (Result.ok_injective hv1).symm
  subst hv1'
  rw [driver.cli.closed] at h
  simp only [core.option.Option.is_some, Option.isSome_none, Bool.false_eq_true, ite_false] at h
  have ha := (Result.ok_injective h).symm
  subst ha
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, cf', sf', ?_,
    str_copy_val hcf', str_copy_val hsf'⟩
  rw [push_val hout2, push_val hout1]
  rfl

/-- The path of an argument's code points is the argument. -/
theorem pathRel_arg {f f' : alloc.vec.Vec Std.U32} {file : String}
    (hf' : f'.val = f.val) (hf : f.val.map UScalar.val = file.toList.map Char.toNat) :
    PathRel f' ⟨file⟩ := by
  refine Or.inr (Or.inr ?_)
  congr 1
  simp only [ConRon.Refine.absString, hf']
  rw [show f.val.map (fun c => Char.ofNat c.val) = (f.val.map UScalar.val).map Char.ofNat by
    simp, hf, List.map_map]
  simp [Function.comp_def, Char.ofNat_toNat]

end Cli

/-! ## The comparison of two lean4export files -/

section CompareJson

variable {S : Type} {io : frontend.checker_io.CheckerIo S} {fs : ConLeche.FS}

/-- A failed read's exit code is not 0. -/
theorem read_export_err_ne {s : S} {pers ar file v} {c : Std.U8} {ar' : arena.monad.AState}
    (h : driver.compare_json.read_export io s pers ar file v = ok (.Err c, ar')) : c.val ≠ 0 := by
  rw [driver.compare_json.read_export] at h
  obtain ⟨⟨read, ar1, src'⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨fs', path', off', reads', err'⟩ := src'
  cases err' with
  | some m =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Err.injEq] at this
    rw [← this.1]
    decide
  | none =>
  cases read with
  | Err p =>
    obtain ⟨e, line⟩ := p
    obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Err.injEq] at this
    rw [← this.1]
    exact exit_code_ne hc0
  | Ok r1 =>
    have := Result.ok_injective h
    simp at this

/-- **The verdict on the challenge, 0**: its check phase accepted. -/
theorem compare_verdict_zero {s s' : S} {pers st ds_s prep recs sol v rc sl rs ver} {c : Std.U8}
    (h : driver.compare_json.compare_verdict io s pers st ds_s prep recs sol v rc sl rs ver
      = ok (c, s'))
    (hc : c.val = 0) : ∃ ix, v = .Ok ix := by
  cases v with
  | Ok ix => exact ⟨ix, rfl⟩
  | Err p =>
    exfalso
    rw [driver.compare_json.compare_verdict] at h
    obtain ⟨e, i⟩ := p
    obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact code_ne h (exit_code_ne hc0) hc

/-- The solution's failed check is never 0. -/
theorem solution_failed_ne {s s' : S} {pers st ds e i sl ver} {c : Std.U8}
    (h : driver.compare_json.solution_failed io s pers st ds e i sl ver = ok (c, s'))
    (hc : c.val = 0) : False := by
  rw [driver.compare_json.solution_failed] at h
  obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  exact code_ne h (exit_code_ne hc0) hc

end CompareJson

/-- **What an exit 0 of `--compare -- C S` ran**: the staged lemmas' step premises, in the binary's
order, at its start values and the embedded pins, with the challenge's chunks concatenating to
the challenge file's bytes `bC` — every premise of `compare_json_model_of_stages`. -/
inductive CompareJsonStages (bC : ByteArray) : Prop where
  | intro {st1 st2 st3 st4 st5 st6 st7 st9 st10 st11 : arena.monad.AState}
      {pre : frontend.prepare.PreludeIx}
      {Sc : Type} {sinst : frontend.export_c.ChunkSource Sc} {srcC srcC' srcS srcS' : Sc}
      {chunksC chunksS : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
      {rC rS : frontend.export_c.ParseResultD} {preC : frontend.prepare.PreludeIx}
      {prepS : frontend.prepare.Prepared}
      {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
      {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {maxNatSize : ron.nat.Nat}
      {ixS : arena.stream_index.IStreamIndex} {tierS : arena.store.PersTier}
      {frozenS : arena.store.EStore} {prepC : frontend.prepare.Prepared}
      {recsC : alloc.vec.Vec arena.env.IDeclaration} {sol : arena.justify.Solution}
      {ixC : arena.stream_index.IStreamIndex} {tierC : arena.store.PersTier}
      {frozenC : arena.store.EStore}
      (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
      (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
      (hreadsC : ReadsAs sinst srcC chunksC.val) (hreadsS : ReadsAs sinst srcS chunksS.val)
      (hbC : ConLeche.Frontend.concatBytes (absChunks chunksC) = bC)
      (h3 : frontend.export_c.parse_source sinst emptyTier st2 srcC = ok (.Ok rC, st3, srcC'))
      (h3S : frontend.export_c.parse_source sinst emptyTier st3 srcS = ok (.Ok rS, st4, srcS'))
      (hdup : frontend.prepare.prelude_ix_dup pre = ok preC)
      (h4S : frontend.prepare.prepare_d
        frontend.nat_op_ground.DeclUsedConsts.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts
        emptyTier st4 pre rS.decls () = ok (.Ok prepS, st5))
      (hpins : kernel.pins_decode.decode_embedded = ok (.Ok pins))
      (h5 : arena.checker.intern_all_pins emptyTier st5 pins maxNatSize = ok (.Ok ipins, st6))
      (h6S : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st6 e prepS.decls 0#usize) = ok (.Ok ixS, st7))
      (h7S : arena.checker.freeze_tier st7.store ixS = ok (tierS, frozenS))
      (h8S : ParallelAll prepS.decls.length (arena.checker.worker_state st7.pins)
        (jobStep tierS .Verified ipins prepS.decls))
      (h4 : frontend.prepare.prepare_d
        frontend.nat_op_ground.DeclUsedConsts.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts
        emptyTier st7 preC rC.decls () = ok (.Ok prepC, st9))
      (hside : arena.justify.side_records emptyTier st9 prepC.decls 0#usize
        (alloc.vec.Vec.new _) = ok (.Ok recsC, st10))
      (hsol : arena.justify.solution_of ixS recsC = ok sol)
      (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st10 e recsC 0#usize) = ok (.Ok ixC, st11))
      (h7 : arena.checker.freeze_tier st11.store ixC = ok (tierC, frozenC))
      (h8 : ParallelAll recsC.length (arena.checker.worker_state st11.pins)
        (jobStepSol tierC .Verified ipins (some sol) recsC)) :
      CompareJsonStages bC

section CompareJson

variable {S : Type} {io : frontend.checker_io.CheckerIo S} {fs : ConLeche.FS}

/-- **The comparison of two lean4export files, 0** (`compare_json::compare_json` at
`--verified`, the embedded pins): the challenge's file is in the snapshot, and the run's calls
are the staged lemmas' step premises (`CompareJsonStages`). -/
theorem compare_json_zero (hfs : AnswersAs io fs) (hpool : PoolSound io) {s s' : S}
    {a : driver.cli.Args} (hver : a.verified = true)
    {chal sl : alloc.vec.Vec Std.U32} {qc qs : System.FilePath}
    (hqc : PathRel chal qc) (hqs : PathRel sl qs) {c : Std.U8}
    (h : driver.compare_json.compare_json io s a chal sl = ok (c, s')) (hc : c.val = 0) :
    ∃ bC, fs.file qc = some bC ∧ CompareJsonStages bC := by
  rw [driver.compare_json.compare_json] at h
  simp only [hver, ite_true, bind_ok] at h
  rw [startState_eq, bind_ok, emptyTier_eq, bind_ok] at h
  obtain ⟨⟨r0, st1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r0 with
  | Err e =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (by decide) hc).elim
  | Ok u =>
  obtain ⟨⟨r1, st2⟩, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r1 with
  | Err p =>
    obtain ⟨e, line⟩ := p
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (by decide) hc).elim
  | Ok pre =>
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r2, st3⟩, hrc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r2 with
  | Err c0 => exact (code_ne h (read_export_err_ne hrc) hc).elim
  | Ok rC =>
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r4, st4⟩, hrs, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r4 with
  | Err c0 => exact (code_ne h (read_export_err_ne hrs) hc).elim
  | Ok rS =>
  obtain ⟨preC, hdup, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r6, st5⟩, h4S, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r6 with
  | Err e =>
    obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (exit_code_ne hc0) hc).elim
  | Ok prepS =>
  have h := hoisted_bind h
  obtain ⟨o, hpr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases o with
  | none => exact (code_ne h (by decide) hc).elim
  | some ps =>
  have hpins := embedded_pins_ok hpr
  obtain ⟨⟨r7, st6⟩, h5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r7 with
  | Err e =>
    obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (exit_code_ne hc0) hc).elim
  | Ok ipins =>
  obtain ⟨⟨jobs, io2⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r8, io3, st8⟩, hph, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r8 with
  | Err p =>
    obtain ⟨e, i⟩ := p
    exact (solution_failed_ne h hc).elim
  | Ok ixS =>
  obtain ⟨st7, tierS, frozenS, h6S, h7S, h8S, rfl⟩ := check_phase_ok hpool hph
  obtain ⟨⟨r9, st9⟩, h4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r9 with
  | Err e =>
    obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (exit_code_ne hc0) hc).elim
  | Ok prepC =>
  have h := hoisted_bind h
  obtain ⟨⟨r10, st10⟩, hside, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r10 with
  | Err e =>
    obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (exit_code_ne hc0) hc).elim
  | Ok recsC =>
  obtain ⟨sol, hsol, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨verdict, io4, st12⟩, hph2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨ixC, rfl⟩ := compare_verdict_zero h hc
  obtain ⟨st11, tierC, frozenC, h6, h7, h8, -⟩ := check_phase_ok hpool hph2
  obtain ⟨bC, hbC, chunksC, srcC', hreadsC, h3, hcatC⟩ := read_export_ok hfs hqc hrc
  obtain ⟨bS, -, chunksS, srcS', hreadsS, h3S, -⟩ := read_export_ok hfs hqs hrs
  exact ⟨bC, hbC, CompareJsonStages.intro h1 h2 hreadsC hreadsS hcatC h3 h3S hdup h4S hpins h5
    h6S h7S h8S h4 hside hsol h6 h7 h8⟩

/-- **`compare_args` at two files and no `--olean` flag, 0**: the usage checks passed, and the
run is `compare_json` of the two. -/
theorem compare_args_zero {s s' : S} {a : driver.cli.Args}
    (hsp : a.search_path.val = []) (hcon : a.constants.val = []) (hmod : a.module = false)
    (hmods : a.modular = false) (hsch : a.scheduled = false) (htp : a.trusted_path.val = [])
    {cf sf : alloc.vec.Vec Std.U32} (hfiles : a.files.val = [cf, sf]) {c : Std.U8}
    (h : driver.compare_json.compare_args io s a = ok (c, s')) (hc : c.val = 0) :
    driver.compare_json.compare_json io s a cf sf = ok (c, s') := by
  have hlen0 : ∀ {α : Type} {v : alloc.vec.Vec α}, v.val = [] → ¬ alloc.vec.Vec.len v > 0#usize := by
    intro α v hv0 hgt
    have := alloc.vec.Vec.len_val v
    simp [alloc.vec.Vec.length, hv0] at this
    scalar_tac
  have hfl := alloc.vec.Vec.len_val a.files
  have hfl2 : (alloc.vec.Vec.len a.files).val = 2 := by
    rw [hfl]; simp [alloc.vec.Vec.length, hfiles]
  rw [driver.compare_json.compare_args] at h
  simp only [hmod, hmods, hsch, Bool.false_eq_true, ite_false,
    ite_eq_right (hlen0 hsp), ite_eq_right (hlen0 hcon), ite_eq_right (hlen0 htp)] at h
  rw [ite_eq_right (by simp; scalar_tac), vec_index_some (x := cf) (by simp [hfiles]), bind_ok,
    vec_index_some (x := sf) (by simp [hfiles]), bind_ok] at h
  obtain ⟨bb, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases bb with
  | true =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (by decide) hc).elim
  | false => simpa using h

end CompareJson

/-! ## The run of `["--compare", "--", c, s]` -/

/-- **An exit 0 of `["--compare", "--", c, s]`** (`cli::run_args`): the verified driver
compared the two files, at `--verified` and the embedded pins; the challenge's file is in the
snapshot and its calls are the staged lemmas' step premises. -/
theorem run_args_compare {S : Type} {io : frontend.checker_io.CheckerIo S} {fs : ConLeche.FS}
    (hfs : AnswersAs io fs) (hpool : PoolSound io) {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    {c s : String} (hargv : ArgvOf argv ["--compare", "--", c, s]) {x x' : S} {code : Std.U8}
    (h : driver.cli.run_args io x argv = ok (code, x')) (hc : code.val = 0) :
    ∃ bC, fs.file c = some bC ∧ CompareJsonStages bC := by
  obtain ⟨w, d, cf, sf, hv, hw, hd, hcf, hsf⟩ := argv_compare hargv
  rw [driver.cli.run_args] at h
  obtain ⟨hw', hhw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [help_wanted_compare hv hw hd hhw] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨a, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hbad, hcg, hol, hcmp, hsp, hcon, hmod, hmods, hsch, htp, hver, cf', sf',
    hfiles, hcf', hsf'⟩ := parse_args_compare hv hw hd ha
  simp only [hbad, hcg, hol, hcmp, Bool.false_eq_true, ite_false, ite_true] at h
  have h := compare_args_zero hsp hcon hmod hmods hsch htp hfiles h hc
  exact compare_json_zero hfs hpool hver (pathRel_arg hcf' hcf) (pathRel_arg hsf' hsf) h hc

/-- **The run premise, unpacked**: every exit 0 of con-ron at `["--compare", "--", c, s]` read
the file `c`, and is one of `CompareJsonStages`'s on its bytes. -/
theorem compare_json_stages_of_canGive {c s : String} {fs : ConLeche.FS}
    (h : CanGiveConforming ["--compare", "--", c, s] fs 0) :
    ∃ bC, fs.file c = some bC ∧ CompareJsonStages bC := by
  obtain ⟨S, io, x, x', argv, code, hfs, hpool, -, hargv, hrun, hc⟩ := h
  exact run_args_compare hfs hpool hargv hrun (by simpa using hc)

end ConRon

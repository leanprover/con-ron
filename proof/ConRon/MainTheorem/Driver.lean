import ConRon.MainTheorem.Stages

/-!
# `ConRon.MainTheorem.Driver` — the walk of the extracted driver at `-- <file>`

**Task #171, lane D, slice 1** (DESIGN.md §3.9).  The binary's `main` is plumbing around the
extracted `driver::cli::run_args`, generic over the trait `frontend::checker_io::CheckerIo`
(the port of con-leche's class `CheckerIO`).  This module states what the walks assume of an
instance — its file operations answer as one snapshot of the files at every state
(`AnswersAs`), its worker map keeps the pool's contract for every job (`PoolSound`), its code
map answers each job's code (`CodesSound`); the model instance of `MainTheorem/Model.lean` has
all three, as theorems — and walks
the Aeneas model of `run_args` at the argument list `["--", file]`: an exit 0 there is one
premise per step of the staged lemma (`ConRon.MainTheorem.Stages.model_exists_embedded`'s `h1` … `h8`, at the
binary's start values, the embedded pins), with the chunks the reads returned concatenating to
the file's bytes (`run_args_json`).

One lemma per driver function, each an inversion ("if `f …` answers this, then these facts"),
as `Stages.lean`'s are:

| lemma | function |
|---|---|
| `fileChunks_loop` | `export_c::parse_source`'s loop over `checker_io::FileChunks` |
| `help_wanted_end`, `parse_args_end` | `cli::help_wanted`, `cli::parse_args` at `["--", f]` |
| `check_phase_ok` | `check_main::check_phase` |
| `verdict_of_zero` | `check_main::verdict_of` |
| `check_main_zero` | `check_main::check_main` |
| `run_args_json` | `cli::run_args` |
-/

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon

open ConRon.Refine2 ConRon.Refine2.Frontend ConRon.Refine2.Frontend.Olean ConRon.MainTheorem.Stages

/-! ## What the walks assume of an instance -/

/-- **The instance's file operations answer as the snapshot `fs`, at every state**: at the
paths the driver asks (`PathRel`), each operation that answers gives `fs`'s answer
(`Stages.lean`'s `SnapshotOf`, at every state of the instance).  A failing operation claims
nothing: it gives the driver no exit 0. -/
def AnswersAs {S : Type} (io : frontend.checker_io.CheckerIo S) (fs : ConLeche.FS) : Prop :=
  ∀ s : S, SnapshotOf io.CheckerFsInst s fs

/-- A job's step at a `Nat` position, as `ParallelAll` takes it: the `Step`'s at the position
as a `usize` (a position past one is a panic), reading files through the instance at `io`. -/
def stepAt {I S St : Type} (inst : frontend.checker_io.Step St I S) (st : St) (io : I)
    (x : S) (k : Nat) :
    Result ((core.result.Result Unit (kernel.core_types.CheckError × Std.U64)) × S) :=
  if h : k < 2 ^ UScalarTy.Usize.numBits then
    inst.step st io x (UScalar.ofNatCore (ty := .Usize) k h)
  else fail .panic

/-- **The instance's worker map keeps the pool's contract, for every job**: an `Ok` of
`par_map_workers` over `n` positions is `ParallelAll` (`Refine2/Checker/Jobs.lean`) of the
job's `init` and `step`, the steps reading files at the state the map was called in. -/
def PoolSound {I : Type} (io : frontend.checker_io.CheckerIo I) : Prop :=
  ∀ {S St : Type} (inst : frontend.checker_io.Step St I S) (st : St) (s : I)
    (n w : Std.Usize) (s' : I),
    io.par_map_workers inst s st n w = ok (.Ok (), s') →
    ParallelAll n.val (inst.init st) (stepAt inst st s)

/-- **The instance's code map keeps its contract, for every job**: an `Ok` of `par_map_codes`
over `n` positions answers, at each position, the job's exit code there, the job reading files
and notifying at the state the map was called in. -/
def CodesSound {I : Type} (io : frontend.checker_io.CheckerIo I) : Prop :=
  ∀ {St : Type} (inst : frontend.checker_io.CodeStep St I) (st : St) (s : I)
    (n w : Std.Usize) (cs : alloc.vec.Vec Std.U8) (s' : I),
    io.par_map_codes inst s st n w = ok (.Ok cs, s') →
    cs.val.length = n.val ∧ ∀ (k : Std.Usize), k.val < n.val →
      inst.code st s k = ok (cs.val[k.val]!)

/-- **`argv` is the argument list `args`**: each string's code points, in order (con-ron's
string representation, `absString`'s inverse).  A relation rather than a function: a `Vec` is
at most `usize::MAX` long, and a list that does not fit has no `argv`. -/
def ArgvOf (argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)) (args : List String) : Prop :=
  argv.val.map (fun a => a.val.map UScalar.val) = args.map (fun s => s.toList.map Char.toNat)

/-- **An exit code `c` of the extracted driver at the argument list `args`, at SOME instance that
conforms to the snapshot `fs`**: its file operations answer as `fs` at every state, and its two
maps keep their contracts.  The walks are proved from this instance-generic form; the main
theorems' `ConRon.CanGive` (`MainTheorem/Model.lean`) is the driver at one instance, the model
`Model.snapshotIo fs`, which conforms (`CanGive.conforming`). -/
def CanGiveConforming (args : List String) (fs : ConLeche.FS) (c : UInt8) : Prop :=
  ∃ (S : Type) (io : frontend.checker_io.CheckerIo S) (s s' : S)
    (argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)) (c' : Std.U8),
    AnswersAs io fs ∧ PoolSound io ∧ CodesSound io ∧ ArgvOf argv args ∧
    driver.cli.run_args io s argv = ok (c', s') ∧ c'.val = c.toNat

/-! ## Arithmetic and bytes -/

/-- A `usize`/`u64` sum that answers is the sum of the values. -/
theorem add_ok_val {ty : UScalarTy} {x y z : UScalar ty} (h : x + y = ok z) :
    z.val = x.val + y.val := by
  have := UScalar.add_equiv x y
  rw [h] at this
  simp at this
  exact this.2.1

/-- A `usize`/`u64` product that answers is the product of the values. -/
theorem mul_ok_val {ty : UScalarTy} {x y z : UScalar ty} (h : x * y = ok z) :
    z.val = x.val * y.val := by
  have := UScalar.mul_equiv x y
  have h' : UScalar.mul x y = ok z := h
  rw [h'] at this
  simp at this
  exact this.2.1

/-- The chunk size is positive. -/
theorem chunk_size_pos {i : Std.Usize} (h : frontend.export_c.CHUNK_SIZE = ok i) :
    0 < i.val := by
  rw [frontend.export_c.CHUNK_SIZE] at h
  obtain ⟨j, hj, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [mul_ok_val h, mul_ok_val hj]
  simp

/-- A cast up that answers keeps the value. -/
theorem cast_u64_val (i : Std.Usize) (hi : i.val < 2 ^ 64) :
    (UScalar.cast .U64 i).val = i.val := by
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by simpa using hi)

/-- An empty read is the end of the file: past it, nothing is left. -/
theorem extract_end {b : ByteArray} {off len : Nat} (hlen : 0 < len)
    (h : (b.extract off (min (off + len) b.size)).size = 0) :
    b.extract off b.size = ByteArray.empty := by
  rw [ByteArray.size_extract] at h
  rw [ByteArray.extract_eq_empty_iff]
  omega

/-- A read and the rest of the file are the rest from the read's start. -/
theorem extract_cut {b : ByteArray} {off mid : Nat} (h1 : off ≤ mid) (h2 : mid ≤ b.size) :
    b.extract off mid ++ b.extract mid b.size = b.extract off b.size := by
  rw [ByteArray.extract_append_extract]
  congr 1 <;> omega

/-! ## The stream's reads -/

/-- **One turn of the reader loop** (any chunk source): the read, then either the end (an empty
buffer, the loop's answer from the source after it) or a nonempty buffer, whose step is an error
or the loop again. -/
theorem parse_source_loop_inv {Sc : Type} {inst : frontend.export_c.ChunkSource Sc}
    {pers : arena.store.PersTier} {ar : arena.monad.AState} {src : Sc}
    {st : frontend.export_c.StateD} {carry : alloc.vec.Vec Std.U8} {line total : Std.U64} {o}
    (h : frontend.export_c.parse_source_loop inst pers ar src st carry line total = ok o) :
    ∃ buf src1, inst.next_chunk src = ok (buf, src1) ∧
      ((buf.val = [] ∧ o.2.2 = src1) ∨
       (buf.val ≠ [] ∧ ((∃ e, o.1 = .Err e) ∨
         ∃ ar1 st1 c2 l t1,
           frontend.export_c.parse_source_loop inst pers ar1 src1 st1 c2 l t1 = ok o))) := by
  rw [frontend.export_c.parse_source_loop] at h
  obtain ⟨⟨buf, src1⟩, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  refine ⟨buf, src1, hn, ?_⟩
  change (if alloc.vec.Vec.len buf = 0#usize then _ else _) = ok o at h
  by_cases h0 : alloc.vec.Vec.len buf = 0#usize
  · left
    have hl := alloc.vec.Vec.len_val buf
    rw [h0] at hl
    refine ⟨List.eq_nil_of_length_eq_zero (by simpa using hl.symm), ?_⟩
    rw [ite_eq_left h0] at h
    obtain ⟨s, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨r, ar1⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
  · right
    have hne : buf.val ≠ [] := by
      intro hb
      apply h0
      have hl := alloc.vec.Vec.len_val buf
      have : buf.val.length = 0 := by rw [hb]; rfl
      scalar_tac
    refine ⟨hne, ?_⟩
    rw [ite_eq_right h0] at h
    obtain ⟨s, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨r, ar1, st1⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r with
    | Err e =>
      left
      exact ⟨e, by rw [← Result.ok_injective h]⟩
    | Ok t =>
      right
      obtain ⟨c2, l, t1⟩ := t
      exact ⟨ar1, st1, c2, l, t1, h⟩

section Reads

variable {S : Type} {io : frontend.checker_io.CheckerIo S} {fs : ConLeche.FS}

/-- The stream's chunk source at the instance (`FileChunks`). -/
abbrev fileSrc (io : frontend.checker_io.CheckerIo S) :=
  frontend.checker_io.FileChunks.Insts.Con_ron_coreFrontendExport_cChunkSource io.CheckerFsInst

/-- **One read of the stream** (`FileChunks::next_chunk`, no failure kept yet): the positional
read at the source's offset, of a positive length; a failure, kept, and an empty buffer; or the
bytes handed out, the offset past them and the read counted. -/
theorem next_chunk_inv {src : frontend.checker_io.FileChunks S} (herr : src.err = none)
    {buf : alloc.vec.Vec Std.U8} {src1 : frontend.checker_io.FileChunks S}
    (h : (fileSrc io).next_chunk src = ok (buf, src1)) :
    ∃ len : Std.U64, 0 < len.val ∧ ∃ r,
      io.CheckerFsInst.read_range src.fs src.path src.off len = ok r ∧
      ((∃ e, r = .Err e ∧ buf.val = [] ∧ src1.err = some e) ∨
       (r = .Ok buf ∧ src1.fs = src.fs ∧ src1.path = src.path ∧ src1.err = none ∧
         src1.off.val = src.off.val + buf.length ∧ src1.reads.val = src.reads.val + 1)) := by
  simp only [frontend.checker_io.FileChunks.Insts.Con_ron_coreFrontendExport_cChunkSource.next_chunk,
    herr] at h
  obtain ⟨i, hi, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hpos := chunk_size_pos hi
  have hi64 : i.val < 2 ^ 64 := by
    rw [frontend.export_c.CHUNK_SIZE] at hi
    obtain ⟨j, hj, hi⟩ := ConRon.Refine.bind_eq_ok_iff.mp hi
    rw [mul_ok_val hi, mul_ok_val hj]
    simp
  simp only [lift, bind_ok] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  refine ⟨UScalar.cast .U64 i, by rw [cast_u64_val i hi64]; exact hpos, r, hr, ?_⟩
  cases r with
  | Err e =>
    left
    have := Result.ok_injective h
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨e, rfl, rfl, rfl⟩
  | Ok v =>
    right
    obtain ⟨i4, h4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i5, h5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have := Result.ok_injective h
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    have hv := alloc.vec.Vec.len_val v
    have hv64 : (alloc.vec.Vec.len v).val < 2 ^ 64 := by
      have hb := (alloc.vec.Vec.len v).hBounds
      have : UScalarTy.Usize.numBits ≤ 64 := by
        simp only [UScalarTy.numBits]
        rcases System.Platform.numBits_eq with h | h <;> omega
      exact lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) this)
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
    · rw [add_ok_val h4, cast_u64_val _ hv64, hv]
    · rw [add_ok_val h5]
      rfl

/-- **The stream parse over the file's reads, to an `Ok` with no read failure**: the source's
reads are chunks of `b` from the source's offset to the end, each nonempty, then an empty one
(`ReadsAs`), with fewer reads than a `usize` counts. -/
theorem fileChunks_loop (hfs : AnswersAs io fs) {s : S} {file : alloc.vec.Vec Std.U32}
    {q : System.FilePath} (hq : PathRel file q) {b : ByteArray} (hb : fs.file q = some b) :
    ∀ (k : Nat) (src : frontend.checker_io.FileChunks S), b.size - src.off.val = k →
      src.fs = s → src.path = file → src.err = none → src.off.val ≤ b.size →
      ∀ {pers ar st carry line total o},
        frontend.export_c.parse_source_loop (fileSrc io) pers ar src st carry line total
          = ok o →
        (∃ r, o.1 = .Ok r) → o.2.2.err = none →
        ∃ cs : List (alloc.vec.Vec Std.U8), ReadsAs (fileSrc io) src cs ∧
          ConLeche.Frontend.concatBytes (cs.map absChunk) = b.extract src.off.val b.size ∧
          src.reads.val + cs.length < 2 ^ UScalarTy.Usize.numBits := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro src hk hsrc hpath herr hle pers ar st carry line total o hrun hok herr'
  obtain ⟨buf, src1, hn, hcase⟩ := parse_source_loop_inv hrun
  obtain ⟨len, hlen, r, hr, hread⟩ := next_chunk_inv herr hn
  rcases hread with ⟨e, rfl, hnil, he⟩ | ⟨rfl, hfs1, hpath1, herr1, hoff1, hreads1⟩
  · -- a failed read: it is kept, the buffer is empty, and the loop ends with it
    exfalso
    rcases hcase with ⟨-, ho⟩ | ⟨hne, -⟩
    · rw [ho, he] at herr'; exact absurd herr' (by simp)
    · exact hne hnil
  · -- the bytes read are the file's
    rw [hsrc, hpath] at hr
    obtain ⟨whole, hw, hbytes⟩ := (hfs s).read_range hq src.off len buf hr
    rw [hb] at hw
    cases hw
    have hsz : buf.length = (b.extract src.off.val (min (src.off.val + len.val) b.size)).size := by
      rw [← hbytes]
      simp [absBytes, alloc.vec.Vec.deref, alloc.vec.Vec.length, ByteArray.size]
    rw [ByteArray.size_extract] at hsz
    have hr1 : src1.reads.val < 2 ^ UScalarTy.Usize.numBits := src1.reads.hBounds
    rcases hcase with ⟨hnil, ho⟩ | ⟨hne, ⟨e', he'⟩ | ⟨ar1, st1, c2, l, t1, h1⟩⟩
    · -- the end: an empty read
      refine ⟨[], ⟨buf, src1, hn, hnil⟩, ?_, by simp only [List.length_nil]; omega⟩
      have : (b.extract src.off.val (min (src.off.val + len.val) b.size)).size = 0 := by
        rw [ByteArray.size_extract]
        have : buf.length = 0 := by simp [alloc.vec.Vec.length, hnil]
        omega
      rw [extract_end hlen this]
      rfl
    · obtain ⟨r0, hr0⟩ := hok
      rw [hr0] at he'
      cases he'
    · -- a nonempty read, then the loop from the source after it
      have hpos : 0 < buf.length := by
        simp only [alloc.vec.Vec.length]
        exact List.length_pos_of_ne_nil hne
      have hk' : b.size - src1.off.val < k := by omega
      obtain ⟨cs, hcs, hcat, hcnt⟩ := ih _ hk' src1 rfl (by rw [hfs1, hsrc])
        (by rw [hpath1, hpath]) herr1 (by omega) h1 hok herr'
      refine ⟨buf :: cs, ⟨hne, src1, hn, hcs⟩, ?_, by simp only [List.length_cons]; omega⟩
      simp only [List.map_cons, ConLeche.Frontend.concatBytes]
      rw [hcat, hoff1]
      have hchunk : absChunk buf = b.extract src.off.val (src.off.val + buf.length) := by
        rw [show absChunk buf = absBytes (alloc.vec.Vec.deref buf) by
          simp [absChunk, absBytes, alloc.vec.Vec.deref], hbytes]
        congr 1
        omega
      rw [hchunk, extract_cut (by omega) (by omega)]

set_option autoImplicit false

/-- **The stream parse over the file**, from the offset 0, to an `Ok` with no read failure kept:
its reads are chunks of the file, each nonempty, then an empty one, and they concatenate to the
file's bytes. -/
theorem fileChunks_parse (hfs : AnswersAs io fs) {s : S} {file : alloc.vec.Vec Std.U32}
    {q : System.FilePath} (hq : PathRel file q) {b : ByteArray} (hb : fs.file q = some b)
    {pers : arena.store.PersTier} {ar ar' : arena.monad.AState} {r}
    {src' : frontend.checker_io.FileChunks S}
    (h : frontend.export_c.parse_source (fileSrc io) pers ar
      { fs := s, path := file, off := 0#u64, reads := 0#usize, err := none } = ok (.Ok r, ar', src'))
    (herr : src'.err = none) :
    ∃ chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      ReadsAs (fileSrc io) { fs := s, path := file, off := 0#u64, reads := 0#usize, err := none }
        chunks.val ∧
      ConLeche.Frontend.concatBytes (absChunks chunks) = b := by
  rw [frontend.export_c.parse_source] at h
  obtain ⟨⟨r0, e0⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r0 with
  | Err e1 =>
    have := Result.ok_injective h
    simp at this
  | Ok v =>
    obtain ⟨cs, hcs, hcat, hcnt⟩ := fileChunks_loop hfs hq hb _ _ rfl rfl rfl rfl (by simp) h
      ⟨r, rfl⟩ herr
    have hlen : cs.length ≤ Std.Usize.max := by
      simp at hcnt
      scalar_tac
    refine ⟨alloc.vec.Vec.from cs hlen, by rw [alloc.vec.Vec.from_val]; exact hcs, ?_⟩
    simp only [absChunks, alloc.vec.Vec.from_val]
    rw [hcat]
    simp

end Reads

/-! ## The argument list `["--", file]` -/

section Cli

theorem vals_eq {l m : List Std.U32} (h : l.map UScalar.val = m.map UScalar.val) : l = m :=
  (List.map_injective_iff.mpr (fun _ _ h => UScalar.eq_of_val_eq h)) h

theorem vec_index_ok {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize}
    (hi : i.val < v.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok v.val[i.val] := by
  simp only [alloc.vec.Vec.index_slice_index]
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec v i hi)
  rw [hy, hyv]

theorem vec_index_some {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : v.val[i.val]? = some x) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp h
  rw [vec_index_ok hi, hx]

/-- `["--", file]`'s `argv`: two words, `--` and the file's code points. -/
theorem argv_end {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {file : String}
    (h : ArgvOf argv ["--", file]) :
    ∃ d f, argv.val = [d, f] ∧ d.val = [45#u32, 45#u32] ∧
      f.val.map UScalar.val = file.toList.map Char.toNat := by
  unfold ArgvOf at h
  rcases hv : argv.val with _ | ⟨d, _ | ⟨f, _ | ⟨g, l⟩⟩⟩ <;> rw [hv] at h <;> simp at h
  refine ⟨d, f, rfl, vals_eq ?_, h.2⟩
  rw [h.1]
  rfl

/-- The word `--` as the parser compares it. -/
theorem w_end_val : (Array.to_slice driver.cli.W_END).val = [45#u32, 45#u32] := by
  simp [driver.cli.W_END, Array.to_slice]

/-- `cps_beq` of `--` against `--`. -/
theorem beq_end {d : alloc.vec.Vec Std.U32} (hd : d.val = [45#u32, 45#u32]) {sl : Slice Std.U32}
    (hsl : lift (Array.to_slice driver.cli.W_END) = ok sl) {bb : Bool}
    (h : frontend.text.cps_beq d sl = ok bb) : bb = true := by
  have hsl' : sl = Array.to_slice driver.cli.W_END := (Result.ok_injective hsl).symm
  rw [cps_beq_val h, hd, hsl', w_end_val]

/-- **No `--help` before the `--`.** -/
theorem help_wanted_end {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {d f}
    (hv : argv.val = [d, f]) (hd : d.val = [45#u32, 45#u32]) {hw : Bool}
    (h : driver.cli.help_wanted argv = ok hw) : hw = false := by
  rw [driver.cli.help_wanted, driver.cli.help_wanted_loop] at h
  have hl := alloc.vec.Vec.len_val argv
  have hlen : (alloc.vec.Vec.len argv).val = 2 := by rw [hl]; simp [alloc.vec.Vec.length, hv]
  rw [ite_eq_right (by scalar_tac)] at h
  rw [vec_index_some (x := d) (by simp [hv]), bind_ok] at h
  obtain ⟨sl, hsl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨bb, hbb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [beq_end hd hsl hbb] at h
  exact (Result.ok_injective h).symm

/-- `Vec::push` appends. -/
theorem push_val {α : Type} {v r : alloc.vec.Vec α} {x : α} (h : alloc.vec.Vec.push v x = ok r) :
    r.val = v.val ++ [x] := by
  unfold alloc.vec.Vec.push at h
  dsimp only at h
  split at h
  · rw [← Result.ok_injective h, alloc.vec.Vec.from_val, List.concat_eq_append]
  · exact absurd h (by simp)

/-- `str_copy_from`'s loop copies the rest. -/
theorem str_copy_from_loop_val (s : alloc.vec.Vec Std.U32) :
    ∀ (k : Nat) (o : alloc.vec.Vec Std.U32) (i : Std.Usize), s.length - i.val = k →
      ∀ {t}, kernel.expr.str_copy_from_loop s o i = ok t → t.val = o.val ++ s.val.drop i.val := by
  intro k
  induction k with
  | zero =>
    intro o i hk t h
    rw [kernel.expr.str_copy_from_loop] at h
    have hl := alloc.vec.Vec.len_val s
    rw [ite_eq_left (by scalar_tac)] at h
    rw [← Result.ok_injective h, List.drop_eq_nil_of_le (by simp [alloc.vec.Vec.length] at hk; omega)]
    simp
  | succ k ih =>
    intro o i hk t h
    rw [kernel.expr.str_copy_from_loop] at h
    have hl := alloc.vec.Vec.len_val s
    have hlt : i.val < s.length := by omega
    rw [ite_eq_right (by scalar_tac)] at h
    rw [vec_index_ok hlt, bind_ok] at h
    obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi3v := add_ok_val hi3
    rw [ih o1 i3 (by simp at hi3v; omega) h, push_val ho1, hi3v,
      List.drop_eq_getElem_cons (i := i.val) hlt]
    simp

/-- `str_copy` copies. -/
theorem str_copy_val {s t : alloc.vec.Vec Std.U32} (h : kernel.expr.str_copy s = ok t) :
    t.val = s.val := by
  rw [kernel.expr.str_copy, kernel.expr.str_copy_from] at h
  rw [str_copy_from_loop_val s _ _ _ rfl h]
  simp

/-- **The parse of `["--", f]`**: every default, and the one file `f`. -/
theorem parse_args_end {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {d f}
    (hv : argv.val = [d, f]) (hd : d.val = [45#u32, 45#u32]) {a : driver.cli.Args}
    (h : driver.cli.parse_args argv = ok a) :
    a.bad = none ∧ a.check_graph = false ∧ a.olean = false ∧ a.compare = false ∧
      a.search_path.val = [] ∧ a.constants.val = [] ∧ a.module = false ∧ a.modular = false ∧
      a.scheduled = false ∧ a.trusted_path.val = [] ∧ a.verified = true ∧
      ∃ f', a.files.val = [f'] ∧ f'.val = f.val := by
  rw [driver.cli.parse_args, driver.cli.args_default] at h
  obtain ⟨a0, ha0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n, -, ha0⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha0
  have ha0' := (Result.ok_injective ha0).symm
  subst ha0'
  rw [driver.cli.parse_args_loop] at h
  have hl := alloc.vec.Vec.len_val argv
  have hlen : (alloc.vec.Vec.len argv).val = 2 := by rw [hl]; simp [alloc.vec.Vec.length, hv]
  rw [ite_eq_right (by scalar_tac)] at h
  rw [vec_index_some (x := d) (by simp [hv]), bind_ok] at h
  obtain ⟨sl, hsl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨bb, hbb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [beq_end hd hsl hbb, ite_eq_left rfl] at h
  obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hi2v : i2.val = 1 := by rw [add_ok_val hi2]; rfl
  -- the files: `f`, copied
  rw [driver.cli.push_files, driver.cli.push_files_loop] at hv1
  rw [ite_eq_left (by scalar_tac), vec_index_some (x := f) (by simp [hv, hi2v]), bind_ok] at hv1
  obtain ⟨f', hf', hv1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hv1
  obtain ⟨out1, hout1, hv1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hv1
  obtain ⟨i3, hi3, hv1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hv1
  have hi3v : i3.val = 2 := by rw [add_ok_val hi3, hi2v]; rfl
  rw [driver.cli.push_files_loop, ite_eq_right (by scalar_tac)] at hv1
  have hv1' := (Result.ok_injective hv1).symm
  subst hv1'
  rw [driver.cli.closed] at h
  simp only [core.option.Option.is_some, Option.isSome_none, Bool.false_eq_true, ite_false] at h
  have ha := (Result.ok_injective h).symm
  subst ha
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, f', ?_, str_copy_val hf'⟩
  rw [push_val hout1]
  rfl

end Cli

/-! ## The check of a lean4export file -/

section CheckMain

variable {S : Type} {io : frontend.checker_io.CheckerIo S} {fs : ConLeche.FS}

/-- `PersTier::empty()` is the staged lemmas' `emptyTier`. -/
theorem emptyTier_eq : arena.store.PersTier.empty = ok emptyTier := by
  simp only [arena.store.PersTier.empty, arena.store.Tbl.empty, arena.store.ETables.empty,
    arena.store.LsTables.empty, arena.store.LTables.empty, arena.store.NTables.empty,
    arena.stream_index.stream_index_empty, ron.hashmap2.HashMap2.new, arena.cons_map.ConsMap.new,
    bind_ok]
  rfl

/-- An exit code that is not 0. -/
theorem code_ne {a c : Std.U8} {x y : S} (h : ok (a, x) = ok (c, y)) (ha : a.val ≠ 0)
    (hc : c.val = 0) : False := by
  have := Result.ok_injective h
  simp only [Prod.mk.injEq] at this
  rw [← this.1] at hc
  exact ha hc

/-- A `CheckError`'s exit code is never 0. -/
theorem exit_code_ne {e : kernel.core_types.CheckError} {c : Std.U8}
    (h : driver.check_main.exit_code e = ok c) : c.val ≠ 0 := by
  cases e <;> simp only [driver.check_main.exit_code] at h <;> rw [← Result.ok_injective h] <;>
    decide

/-- **The verdict, 0**: the check phase accepted. -/
theorem verdict_of_zero {s s' : S} {pers st ds v fr verified} {c : Std.U8}
    (h : driver.check_main.verdict_of io s pers st ds v fr verified = ok (c, s'))
    (hc : c.val = 0) : ∃ ix, v = .Ok ix := by
  cases v with
  | Ok ix => exact ⟨ix, rfl⟩
  | Err p =>
    exfalso
    rw [driver.check_main.verdict_of] at h
    obtain ⟨e, i⟩ := p
    obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact code_ne h (exit_code_ne hc0) hc

/-- **The pin list**: the embedded text's, decoded. -/
theorem embedded_pins_ok {F : Type} {wn : frontend.checker_io.WorkerNotes F} {fsv : F} {ps}
    (h : driver.check_main.embedded_pins wn fsv = ok (some ps)) :
    kernel.pins_decode.decode_embedded = ok (.Ok ps) := by
  rw [driver.check_main.embedded_pins] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Ok ps' => rw [hr, Option.some.inj (Result.ok_injective h)]
  | Err e =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h

/-- **The check phase, accepted** (`check_main::check_phase`, with the solution `sol`): the
staged lemmas' `h6`, `h7` and `h8` — the index from the empty one, the tier frozen, and the worker
map's contract at the driver's job (`ParallelAll` at `jobStepSol`) — and the thaw hands back
the index and the state the index build left (`freeze_tier_ok`). -/
theorem check_phase_ok (hpool : PoolSound io) {s s' : S}
    {pers st mode ipins sol ds jobs fr syn ix st'}
    (h : driver.check_main.check_phase io s pers st mode ipins sol ds jobs fr syn
      = ok (.Ok ix, s', st')) :
    ∃ st1 tier frozen,
      (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index pers st e ds 0#usize) = ok (.Ok ix, st1) ∧
      arena.checker.freeze_tier st1.store ix = ok (tier, frozen) ∧
      ParallelAll ds.length (arena.checker.worker_state st1.pins)
        (jobStepSol tier mode ipins sol ds) ∧ st' = st1 := by
  rw [driver.check_main.check_phase] at h
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r, st1⟩, hbi, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r with
  | Err e =>
    have := Result.ok_injective h
    simp at this
  | Ok ix0 =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨workers, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨tier, frozen⟩, hfz, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨r1, io1⟩, hpar, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨⟨ix1, e1⟩, hth, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [(freeze_tier_ok hfz).2] at hth
    have hth' := Result.ok_injective hth
    simp only [Prod.mk.injEq] at hth'
    obtain ⟨rfl, rfl⟩ := hth'
    cases r1 with
    | Err p =>
      obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have := Result.ok_injective h
      simp at this
    | Ok u =>
      obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hres := Result.ok_injective h
      simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at hres
      obtain ⟨rfl, -, rfl⟩ := hres
      refine ⟨st1, tier, frozen, by rw [hii, bind_ok]; exact hbi, hfz, ?_, rfl⟩
      have hpa := hpool _ _ s _ _ io1 hpar
      rw [alloc.vec.Vec.len_val] at hpa
      have hstep : stepAt (driver.check_main.JobStep.Insts.Con_ron_coreFrontendChecker_ioStepFAState
          io.CheckerFsInst) { tier, mode, pins := ipins, apins := st1.pins, sol, ds } s
          = jobStepSol tier mode ipins sol ds := by
        funext x k
        simp only [stepAt, jobStepSol,
          driver.check_main.JobStep.Insts.Con_ron_coreFrontendChecker_ioStepFAState.step,
          lift, bind_ok]
      rw [hstep] at hpa
      exact hpa

/-- **What an exit 0 of `-- <file>` ran**: the staged lemmas' step premises, in the binary's order,
at its start values and the embedded pins, with the chunks the reads returned concatenating to
the file's bytes `b` — every premise of `ConRon.MainTheorem.Stages.model_exists_embedded` and
`no_False_declaration_embedded`. -/
inductive JsonStages (b : ByteArray) : Prop where
  | intro {st1 st2 st3 st4 st5 st6 : arena.monad.AState} {pre : frontend.prepare.PreludeIx}
      {Sc : Type} {sinst : frontend.export_c.ChunkSource Sc} {src src' : Sc}
      {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)} {r : frontend.export_c.ParseResultD}
      {prepared : frontend.prepare.Prepared}
      {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
      {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {maxNatSize : ron.nat.Nat}
      {ix : arena.stream_index.IStreamIndex} {tier : arena.store.PersTier}
      {frozen : arena.store.EStore}
      (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
      (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
      (hreads : ReadsAs sinst src chunks.val)
      (h3 : frontend.export_c.parse_source sinst emptyTier st2 src = ok (.Ok r, st3, src'))
      (h4 : frontend.prepare.prepare_d
        frontend.nat_op_ground.DeclUsedConsts.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts
        emptyTier st3 pre r.decls () = ok (.Ok prepared, st4))
      (hpins : kernel.pins_decode.decode_embedded = ok (.Ok pins))
      (h5 : arena.checker.intern_all_pins emptyTier st4 pins maxNatSize = ok (.Ok ipins, st5))
      (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st5 e prepared.decls 0#usize) = ok (.Ok ix, st6))
      (h7 : arena.checker.freeze_tier st6.store ix = ok (tier, frozen))
      (h8 : ParallelAll prepared.decls.length (arena.checker.worker_state st6.pins)
        (jobStep tier .Verified ipins prepared.decls))
      (hcat : ConLeche.Frontend.concatBytes (absChunks chunks) = b) :
      JsonStages b

/-- The hoist's receipt changes no state: past it, the run goes on from the same state. -/
theorem hoisted_bind {α β : Type} {c : Prop} [Decidable c] {m : Result Unit} {st : α}
    {f : α → Result β} {v : β}
    (h : (do let x ← (if c then (do m; ok st) else ok st); f x) = ok v) : f st = ok v := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, hy⟩ := ConRon.Refine.bind_eq_ok_iff.mp hy
    rw [Result.ok_injective hy]
    exact h
  · rw [ite_eq_right hc, bind_ok] at h
    exact h

/-- **The check of a lean4export file, 0** (`check_main::check_main` at `--verified`, the
embedded pins): its calls are the staged lemmas' step premises (`JsonStages`). -/
theorem check_main_zero (hfs : AnswersAs io fs) (hpool : PoolSound io) {s s' : S}
    {a : driver.cli.Args} (hver : a.verified = true)
    {file : alloc.vec.Vec Std.U32} {q : System.FilePath}
    (hq : PathRel file q) {b : ByteArray} (hb : fs.file q = some b) {c : Std.U8}
    (h : driver.check_main.check_main io s a file = ok (c, s')) (hc : c.val = 0) :
    JsonStages b := by
  rw [driver.check_main.check_main] at h
  simp only [hver, ite_true, bind_ok] at h
  rw [startState_eq, bind_ok, emptyTier_eq, bind_ok] at h
  obtain ⟨⟨r0, st1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r0 with
  | Err e =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (by decide) hc).elim
  | Ok u =>
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r1, st2⟩, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r1 with
  | Err p =>
    obtain ⟨e, line⟩ := p
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (by decide) hc).elim
  | Ok pre =>
  obtain ⟨⟨read, st3, src'⟩, h3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨fs', path', off', reads', err'⟩ := src'
  cases err' with
  | some m =>
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (by decide) hc).elim
  | none =>
  cases read with
  | Err p =>
    obtain ⟨e, line⟩ := p
    obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (exit_code_ne hc0) hc).elim
  | Ok r =>
  obtain ⟨⟨r2, st4⟩, h4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r2 with
  | Err e =>
    obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (exit_code_ne hc0) hc).elim
  | Ok prepared =>
  have h := hoisted_bind h
  obtain ⟨o, hpr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases o with
  | none => exact (code_ne h (by decide) hc).elim
  | some ps =>
  have hpins := embedded_pins_ok hpr
  obtain ⟨⟨r3, st6⟩, h5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases r3 with
  | Err e =>
    obtain ⟨c0, hc0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact (code_ne h (exit_code_ne hc0) hc).elim
  | Ok ipins =>
  obtain ⟨⟨jobs, io2⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨verdict, io3, st7⟩, hph, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨ix, rfl⟩ := verdict_of_zero h hc
  obtain ⟨st8, tier, frozen, h6, h7, h8, -⟩ := check_phase_ok hpool hph
  obtain ⟨chunks, hreads, hcat⟩ := fileChunks_parse hfs hq hb h3 rfl
  exact JsonStages.intro h1 h2 hreads h3 h4 hpins h5 h6 h7 h8 hcat

end CheckMain

/-! ## The run of `["--", file]` -/

/-- **An exit 0 of `["--", file]`** (`cli::run_args`): the verified driver checked the file, at
`--verified` and the embedded pins, and its calls are the staged lemmas' step premises with the
chunks read concatenating to the file's bytes. -/
theorem run_args_json {S : Type} {io : frontend.checker_io.CheckerIo S} {fs : ConLeche.FS}
    (hfs : AnswersAs io fs) (hpool : PoolSound io) {argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    {file : String} (hargv : ArgvOf argv ["--", file]) {s s' : S} {c : Std.U8}
    (h : driver.cli.run_args io s argv = ok (c, s')) (hc : c.val = 0) {b : ByteArray}
    (hb : fs.file file = some b) : JsonStages b := by
  obtain ⟨d, f, hv, hd, hf⟩ := argv_end hargv
  rw [driver.cli.run_args] at h
  obtain ⟨hw, hhw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [help_wanted_end hv hd hhw] at h
  simp only [Bool.false_eq_true, ite_false] at h
  obtain ⟨a, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hbad, hcg, hol, hcmp, hsp, hcon, hmod, hmods, hsch, htp, hver, f', hfiles, hf'⟩ :=
    parse_args_end hv hd ha
  have hlen0 : ∀ {α : Type} {v : alloc.vec.Vec α}, v.val = [] → ¬ alloc.vec.Vec.len v > 0#usize := by
    intro α v hv0 hgt
    have := alloc.vec.Vec.len_val v
    simp [alloc.vec.Vec.length, hv0] at this
    scalar_tac
  have hfl := alloc.vec.Vec.len_val a.files
  have hfl1 : (alloc.vec.Vec.len a.files).val = 1 := by
    rw [hfl]; simp [alloc.vec.Vec.length, hfiles]
  simp only [hbad, hcg, hol, hcmp, hmod, hmods, hsch, Bool.false_eq_true, ite_false,
    ite_eq_right (hlen0 hsp), ite_eq_right (hlen0 hcon), ite_eq_right (hlen0 htp)] at h
  rw [ite_eq_right (by scalar_tac), ite_eq_right (by simp; scalar_tac),
    vec_index_some (x := f') (by simp [hfiles]), bind_ok] at h
  -- the file's path is the file
  have hq : PathRel f' ⟨file⟩ := by
    refine Or.inr (Or.inr ?_)
    congr 1
    simp only [ConRon.Refine.absString, hf']
    rw [show f.val.map (fun c => Char.ofNat c.val) = (f.val.map UScalar.val).map Char.ofNat by
      simp, hf, List.map_map]
    simp [Function.comp_def, Char.ofNat_toNat]
  exact check_main_zero hfs hpool hver hq hb h hc

/-- **The run premise, unpacked**: every exit 0 of con-ron at `["--", file]` is one of
`JsonStages`'s, on the file's bytes. -/
theorem json_stages_of_canGive {file : String} {fs : ConLeche.FS} {b : ByteArray}
    (h : CanGiveConforming ["--", file] fs 0) (hb : fs.file file = some b) : JsonStages b := by
  obtain ⟨S, io, s, s', argv, c, hfs, hpool, -, hargv, hrun, hc⟩ := h
  exact run_args_json hfs hpool hargv hrun (by simpa using hc) hb

end ConRon

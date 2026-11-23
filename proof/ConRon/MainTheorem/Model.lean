import ConRon.MainTheorem.Driver

/-!
# `ConRon.MainTheorem.Model` — the model instance of `CheckerIo`, con-ron's `ModelIO`

**Task #171, slice 6** (DESIGN.md §3.9).  con-leche states its main theorems in a model of its
class `CheckerIO`, `ModelIO` (`ConLeche/Frontend/CheckerIO.lean`): the file operations answer
from a snapshot `FS`, and `liftIO` may have any outcome.  This module is con-ron's: ONE instance
of the trait `frontend::checker_io::CheckerIo`, `snapshotIo fs`, built from a snapshot
`fs : ConLeche.FS`, whose state is an oracle (`Tape`):

* **the file operations answer from `fs`**, by definition, at the path's string
  (`absString`).  A path that is not a well-formed string (`StrWF`), or whose spellings of one
  request (`PathRel`: the Rust's `mod_file_of` against upstream's `modFile`) name different
  things in `fs`, fails.  The two spellings are one string on the binary's platform, but not in
  the logic: `System.FilePath`'s `/` reads `System.Platform.isWindows`, which is opaque;
* **every escape that answers a value takes its answer from the oracle**, so every value of its
  type is a possible answer (`liftIO`'s "any outcome"): the help's and the scheduler's exit
  codes, the hardware thread count, the copies' error (`worker_copies`, a `&self` escape: its
  answer is the oracle's function of the call's arguments).  An escape answering a value moves
  the tape on; a notification changes nothing;
* **the worker map** folds each job's step over the claims the oracle picks, worker by worker,
  and answers `Ok` when the claims cover every position, increase, and every step answers
  `Ok`; **the code map** runs the job at each position in order and answers the codes.

`AnswersAs (snapshotIo fs) fs`, `PoolSound (snapshotIo fs)` and `CodesSound (snapshotIo fs)`
are then theorems (`snapshotIo_answersAs`, `snapshotIo_poolSound`, `snapshotIo_codesSound`),
and `ConRon.CanGive args fs c` — an exit code `c` of the extracted driver at `args` at this
instance, from some oracle — gives the instance-generic `CanGiveConforming` the walks are proved
from (`CanGive.conforming`).

What a run of the binary must satisfy to be one of the model's runs is the module doc of
`ConRon/MainTheorem.lean` (and OVERVIEW §3.1), the counterpart of `CheckerIO.lean`'s.
-/

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Model

open ConRon.Refine (absString StrWF)
open ConRon.Refine2 ConRon.Refine2.Frontend ConRon.Refine2.Frontend.Olean ConRon.MainTheorem.Stages

/-! ## Strings and bytes as the port holds them -/

theorem char_lt_u32 (c : Char) : c.toNat < 2 ^ UScalarTy.U32.numBits :=
  show c.val.toNat < 2 ^ 32 from UInt32.toNat_lt _

theorem byte_lt_u8 (x : UInt8) : x.toNat < 2 ^ UScalarTy.U8.numBits :=
  show x.toNat < 2 ^ 8 from UInt8.toNat_lt _

/-- A string's code points, as the port stores a string, where they fit a `Vec`. -/
def codesOf (s : String) : Option (alloc.vec.Vec Std.U32) :=
  if h : (s.toList.map fun c => UScalar.ofNatCore (ty := .U32) c.toNat (char_lt_u32 c)).length
      ≤ Usize.max then
    some (alloc.vec.Vec.from _ h)
  else none

/-- A string's code points are a well-formed string, and the string. -/
theorem codesOf_some {s : String} {v : alloc.vec.Vec Std.U32} (h : codesOf s = some v) :
    absString v = s ∧ StrWF v := by
  unfold codesOf at h
  split at h
  · cases h
    refine ⟨?_, ?_⟩
    · simp only [absString, alloc.vec.Vec.from_val, List.map_map, Function.comp_def,
        UScalar.ofNatCore_val_eq, Char.ofNat_toNat, List.map_id', String.ofList_toList]
    · intro c hc
      simp only [alloc.vec.Vec.from_val, List.mem_map] at hc
      obtain ⟨x, -, rfl⟩ := hc
      rw [UScalar.ofNatCore_val_eq]
      exact x.valid
  · cases h

/-- A file's bytes, as the port holds them, where they fit a `Vec`. -/
def bytesOf (b : ByteArray) : Option (alloc.vec.Vec Std.U8) :=
  if h : (b.data.toList.map fun x => UScalar.ofNatCore (ty := .U8) x.toNat (byte_lt_u8 x)).length
      ≤ Usize.max then
    some (alloc.vec.Vec.from _ h)
  else none

/-- The bytes as the port holds them are the file's. -/
theorem bytesOf_some {b : ByteArray} {v : alloc.vec.Vec Std.U8} (h : bytesOf b = some v) :
    absBytes (alloc.vec.Vec.deref v) = b := by
  unfold bytesOf at h
  split at h
  · cases h
    have : (alloc.vec.Vec.deref (alloc.vec.Vec.from _ ‹_›)).val
        = b.data.toList.map fun x => UScalar.ofNatCore (ty := .U8) x.toNat (byte_lt_u8 x) := by
      simp [alloc.vec.Vec.deref]
    cases b with
    | mk data =>
      simp only [absBytes, this, List.map_map, Function.comp_def, absByte,
        UScalar.ofNatCore_val_eq, UInt8.ofNat_toNat, List.map_id', Array.toArray_toList]
  · cases h

/-- A file's size as a `u64`, where it fits. -/
def sizeOf (b : ByteArray) : Option Std.U64 :=
  if h : b.size < 2 ^ UScalarTy.U64.numBits then some (UScalar.ofNatCore b.size h) else none

theorem sizeOf_some {b : ByteArray} {s : Std.U64} (h : sizeOf b = some s) : s.val = b.size := by
  unfold sizeOf at h
  split at h
  · cases h
    exact UScalar.ofNatCore_val_eq _
  · cases h

/-! ## The snapshot's answers -/

/-- **`p` names one thing in `fs`**: a well-formed string, and every spelling of the request
(`PathRel`) has, in `fs`, the real path and the directory flag of the string's. -/
def Spelled (fs : ConLeche.FS) (p : alloc.vec.Vec Std.U32) : Prop :=
  StrWF p ∧ ∀ q, PathRel p q → fs.real q = fs.real ⟨absString p⟩ ∧ fs.dir q = fs.dir ⟨absString p⟩

/-- **A file operation's answer at `p`**: `f`'s, at the path's string, where `p` names one
thing in `fs` and `f` answers; a failure otherwise. -/
noncomputable def answerAt {α : Type} (fs : ConLeche.FS) (p : alloc.vec.Vec Std.U32)
    (f : System.FilePath → Option α) : core.result.Result α (alloc.vec.Vec Std.U32) :=
  open Classical in
  if Spelled fs p then
    match f ⟨absString p⟩ with
    | some a => .Ok a
    | none => .Err (alloc.vec.Vec.new Std.U32)
  else .Err (alloc.vec.Vec.new Std.U32)

theorem answerAt_ok {α : Type} {fs : ConLeche.FS} {p : alloc.vec.Vec Std.U32}
    {f : System.FilePath → Option α} {a : α} (h : answerAt fs p f = .Ok a) :
    Spelled fs p ∧ f ⟨absString p⟩ = some a := by
  unfold answerAt at h
  split at h
  · refine ⟨‹_›, ?_⟩
    split at h
    · cases h; assumption
    · cases h
  · cases h

/-- Every spelling of a request that names one thing has the string's bytes. -/
theorem spelled_file {fs : ConLeche.FS} {p : alloc.vec.Vec Std.U32} {q : System.FilePath}
    (hs : Spelled fs p) (hq : PathRel p q) : fs.file q = fs.file ⟨absString p⟩ := by
  simp only [ConLeche.FS.file, (hs.2 q hq).1]

/-! ## The oracle -/

/-- **The oracle**: an answer for every value-answering escape, the `n`-th call's at `n`; the
worker map's claims, worker by worker, and its failure where the claims do not cover the jobs;
and the copies' answer as a function of the call's arguments. -/
structure Oracle where
  /-- `print_help`'s exit code -/
  help : Nat → Std.U8
  /-- `run_schedule`'s exit code -/
  schedule : Nat → Std.U8
  /-- `hardware_jobs`'s count -/
  hardware : Nat → Std.U64
  /-- the worker map's claims: each worker's positions, in claim order -/
  claims : Nat → List (List Nat)
  /-- the worker map's failure where the claims do not cover the jobs in increasing order -/
  poolErr : Nat → kernel.core_types.CheckError × Std.U64
  /-- `worker_copies`'s answer: the error that kept the lines from being made, the store -/
  copies : Option kernel.name.Name → kernel.name.Name → arena.store.PersTier →
    arena.monad.AState → alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx) →
    frontend.modular.worker.WorkerRead → Option kernel.core_types.CheckError × arena.monad.AState

/-- **The model's state**: the oracle, and how many of its answers the run has taken. -/
structure Tape where
  oracle : Oracle
  next : Nat

/-- The tape after one answer. -/
def Tape.tick (o : Tape) : Tape := { o with next := o.next + 1 }

/-! ## The two maps -/

/-- **A worker's fold over its claims**: `step` from `s` over `ks` in order, to the first
failure (`some`), or none. -/
def foldClaims {S E : Type} (step : S → Nat → Result (core.result.Result Unit E × S)) :
    S → List Nat → Result (Option E)
  | _, [] => ok none
  | s, k :: ks => do
    let (r, s') ← step s k
    match r with
    | .Ok () => foldClaims step s' ks
    | .Err e => ok (some e)

/-- **The workers**: each from `init`, folding its claims, to the first failure, or none. -/
def runWorkers {S E : Type} (init : Result S)
    (step : S → Nat → Result (core.result.Result Unit E × S)) :
    List (List Nat) → Result (Option E)
  | [] => ok none
  | w :: ws => do
    let s₀ ← init
    let r ← foldClaims step s₀ w
    match r with
    | some e => ok (some e)
    | none => runWorkers init step ws

/-- **The worker map at the oracle's claims**: when they cover `0..n`, each worker's in
increasing order, the workers' folds; a failure otherwise. -/
def workerMap {S E : Type} (n : Nat) (parts : List (List Nat)) (err : E) (init : Result S)
    (step : S → Nat → Result (core.result.Result Unit E × S)) :
    Result (core.result.Result Unit E) :=
  if (∀ k < n, ∃ w ∈ parts, k ∈ w) ∧ ∀ w ∈ parts, w.Pairwise (· < ·) then do
    let r ← runWorkers init step parts
    match r with
    | none => ok (.Ok ())
    | some e => ok (.Err e)
  else ok (.Err err)

/-- A job's code at a `Nat` position, as the code map runs it: the `CodeStep`'s at the position
as a `usize`. -/
def codeAt {I St : Type} (inst : frontend.checker_io.CodeStep St I) (st : St) (io : I) (k : Nat) :
    Result Std.U8 :=
  if h : k < 2 ^ UScalarTy.Usize.numBits then
    inst.code st io (UScalar.ofNatCore (ty := .Usize) k h)
  else fail .panic

/-- **The codes of the jobs at `0..n`**, in order. -/
def codesUpTo (code : Nat → Result Std.U8) : Nat → Result (List Std.U8)
  | 0 => ok []
  | k + 1 => do
    let l ← codesUpTo code k
    let c ← code k
    ok (l ++ [c])

/-! ## The instance -/

/-- **The file operations of the snapshot `fs`**: each `fs`'s answer at the path's string
(`answerAt`); the read's two notifications nothing. -/
noncomputable def snapshotFs (fs : ConLeche.FS) : frontend.checker_io.CheckerFs Tape where
  path_exists _ p := ok (answerAt fs p fun q => some (fs.real q).isSome)
  is_dir _ p := ok (answerAt fs p fun q => some (fs.dir q))
  real_path _ p := ok (answerAt fs p fun q => (fs.real q).bind fun r => codesOf r.toString)
  read_bin_file _ p := ok (answerAt fs p fun q => (fs.file q).bind bytesOf)
  read_range _ p off len := ok (answerAt fs p fun q => (fs.file q).bind fun b =>
    bytesOf (b.extract off.val (min (off.val + len.val) b.size)))
  file_size _ p := ok (answerAt fs p fun q => (fs.file q).bind sizeOf)
  read_notes_say _ _ := ok ()
  read_notes_module_loaded _ _ _ := ok ()

/-- **A module worker's lines**: notifications, but `worker_copies`, the oracle's. -/
def oracleNotes : frontend.checker_io.WorkerNotes Tape where
  worker_note _ _ := ok ()
  module_starts _ _ _ := ok ()
  worker_read_done _ _ _ _ := ok ()
  worker_hoisted _ _ _ _ _ := ok ()
  worker_verdict_failure _ _ _ _ _ _ _ _ := ok ()
  worker_copies o who m pers st x w := ok (o.oracle.copies who m pers st x w)

/-- **The model instance**: `fs`'s file operations, the oracle's escapes, the two maps as their
contracts say, every notification nothing. -/
noncomputable def snapshotIo (fs : ConLeche.FS) : frontend.checker_io.CheckerIo Tape where
  CheckerFsInst := snapshotFs fs
  WorkerNotesInst := oracleNotes
  par_map_workers inst o st n _ := do
    let r ← workerMap n.val (o.oracle.claims o.next) (o.oracle.poolErr o.next) (inst.init st)
      (stepAt inst st o)
    ok (r, o.tick)
  par_map_codes inst o st n _ := do
    let l ← codesUpTo (codeAt inst st o) n.val
    if h : l.length ≤ Usize.max then ok (.Ok (alloc.vec.Vec.from l h), o)
    else ok (.Err (alloc.vec.Vec.new Std.U32), o)
  print_help o := ok (o.oracle.help o.next, o.tick)
  run_schedule o _ _ _ := ok (o.oracle.schedule o.next, o.tick)
  hardware_jobs o := ok (o.oracle.hardware o.next, o.tick)
  keep_heap o _ _ _ := ok o
  keep_solution o _ _ _ := ok o
  usage _ _ := ok ()
  note _ _ := ok ()
  read_starts _ _ _ := ok ()
  hoisted _ _ _ _ := ok ()
  index_starts _ := ok ()
  parse_done _ _ _ _ _ _ := ok ()
  check_starts _ _ _ := ok ()
  check_done _ _ _ := ok ()
  oleans_read_starts _ _ _ := ok ()
  read_notes_begin _ _ := ok ()
  read_notes_end _ := ok ()
  graph_accepted _ _ := ok ()
  verdict_failure _ _ _ _ _ _ _ := ok ()
  solution_failure _ _ _ _ _ _ _ _ := ok ()
  compare_accepted _ _ _ _ _ _ _ _ _ := ok ()

/-! ## The model meets the walks' premises -/

/-- **The model answers as its snapshot**, at every state. -/
theorem snapshotIo_answersAs (fs : ConLeche.FS) : AnswersAs (snapshotIo fs) fs := by
  intro s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q hq b h
    obtain ⟨hs, ha⟩ := answerAt_ok (Result.ok_injective h)
    cases ha
    rw [(hs.2 q hq).1]
  · intro p q hq b h
    obtain ⟨hs, ha⟩ := answerAt_ok (Result.ok_injective h)
    cases ha
    rw [(hs.2 q hq).2]
  · intro p q hq r h
    obtain ⟨hs, ha⟩ := answerAt_ok (Result.ok_injective h)
    obtain ⟨r', hr', hc⟩ := Option.bind_eq_some_iff.mp ha
    obtain ⟨h1, h2⟩ := codesOf_some hc
    refine ⟨?_, h2⟩
    rw [(hs.2 q hq).1, hr', h1]
  · intro p q hq b h
    obtain ⟨hs, ha⟩ := answerAt_ok (Result.ok_injective h)
    obtain ⟨w, hw, hb⟩ := Option.bind_eq_some_iff.mp ha
    rw [spelled_file hs hq, hw, bytesOf_some hb]
  · intro p q hq off len b h
    obtain ⟨hs, ha⟩ := answerAt_ok (Result.ok_injective h)
    obtain ⟨w, hw, hb⟩ := Option.bind_eq_some_iff.mp ha
    exact ⟨w, by rw [spelled_file hs hq, hw], bytesOf_some hb⟩
  · intro p q hq z h
    obtain ⟨hs, ha⟩ := answerAt_ok (Result.ok_injective h)
    obtain ⟨w, hw, hz⟩ := Option.bind_eq_some_iff.mp ha
    exact ⟨w, by rw [spelled_file hs hq, hw], sizeOf_some hz⟩

/-- A fold to no failure is a fold with every step `Ok`. -/
theorem foldClaims_none {S E : Type} {step : S → Nat → Result (core.result.Result Unit E × S)} :
    ∀ {s : S} {ks : List Nat}, foldClaims step s ks = ok none → FoldAllOk step s ks
  | _, [], _ => trivial
  | s, k :: ks, h => by
    simp only [foldClaims] at h
    obtain ⟨⟨r, s'⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r with
    | Ok u => cases u; exact ⟨s', h1, foldClaims_none h⟩
    | Err e => cases Result.ok_injective h

/-- Workers to no failure: each from `init`, every step `Ok`. -/
theorem runWorkers_none {S E : Type} {init : Result S}
    {step : S → Nat → Result (core.result.Result Unit E × S)} :
    ∀ {parts : List (List Nat)}, runWorkers init step parts = ok none →
      ∀ w ∈ parts, ∃ s₀, init = ok s₀ ∧ FoldAllOk step s₀ w
  | [], _ => by simp
  | w :: ws, h => by
    simp only [runWorkers] at h
    obtain ⟨s₀, h0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨r, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r with
    | some e => cases Result.ok_injective h
    | none =>
      intro w' hw'
      rcases List.mem_cons.mp hw' with rfl | hw'
      · exact ⟨s₀, h0, foldClaims_none h1⟩
      · exact runWorkers_none h w' hw'

/-- The worker map's `Ok` is the pool's contract at the oracle's claims. -/
theorem workerMap_ok {S E : Type} {n : Nat} {parts : List (List Nat)} {err : E}
    {init : Result S} {step : S → Nat → Result (core.result.Result Unit E × S)}
    (h : workerMap n parts err init step = ok (.Ok ())) : ParallelAll n init step := by
  unfold workerMap at h
  split at h
  · rename_i hc
    obtain ⟨r, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases r with
    | some e => cases Result.ok_injective h
    | none =>
      have hw := runWorkers_none h1
      exact ⟨parts, hc.1, fun w hw' => ⟨hc.2 w hw', hw w hw'⟩⟩
  · cases Result.ok_injective h

/-- **The model's worker map keeps the pool's contract**, for every job. -/
theorem snapshotIo_poolSound (fs : ConLeche.FS) : PoolSound (snapshotIo fs) := by
  intro S St inst st s n w s' h
  simp only [snapshotIo] at h
  obtain ⟨r, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Result.ok_injective h)
  exact workerMap_ok h1

/-- The codes up to `n` are `n` codes, each the job's at its position. -/
theorem codesUpTo_ok {code : Nat → Result Std.U8} :
    ∀ {n : Nat} {l : List Std.U8}, codesUpTo code n = ok l →
      l.length = n ∧ ∀ k < n, code k = ok l[k]!
  | 0, l, h => by
    simp only [codesUpTo] at h
    cases Result.ok_injective h
    exact ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | n + 1, l, h => by
    simp only [codesUpTo] at h
    obtain ⟨l', h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨c, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    obtain ⟨hlen, hk⟩ := codesUpTo_ok h1
    refine ⟨by simp [hlen], fun k hkn => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hkn with hk' | rfl
    · rw [hk k hk']
      congr 1
      rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
        List.getElem?_append_left (by omega)]
    · rw [h2]
      congr 1
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp [hlen]

/-- **The model's code map answers each job's code**, for every job. -/
theorem snapshotIo_codesSound (fs : ConLeche.FS) : CodesSound (snapshotIo fs) := by
  intro St inst st s n w cs s' h
  simp only [snapshotIo] at h
  obtain ⟨l, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨h2, -⟩ := Prod.mk.inj (Result.ok_injective h)
    cases h2
    obtain ⟨hlen, hk⟩ := codesUpTo_ok h1
    refine ⟨by simp [hlen], fun k hk' => ?_⟩
    have := hk k.val hk'
    simp only [codeAt, k.hBounds, ↓reduceDIte] at this
    simp only [alloc.vec.Vec.from_val]
    rw [← this]
    congr 1
  · cases (Prod.mk.inj (Result.ok_injective h)).1

end ConRon.Model

namespace ConRon

/-- **An exit code `c` of con-ron at the argument list `args`, on the files `fs`**: the
extracted driver `driver::cli::run_args` returns `c` at the model instance of the snapshot `fs`
(`Model.snapshotIo fs`), from some oracle.  The counterpart of con-leche's
`ModelIO.CanGive (Driver.runArgs args) fs c`. -/
def CanGive (args : List String) (fs : ConLeche.FS) (c : UInt8) : Prop :=
  ∃ (argv : alloc.vec.Vec (alloc.vec.Vec Std.U32)) (o o' : Model.Tape) (c' : Std.U8),
    ArgvOf argv args ∧ driver.cli.run_args (Model.snapshotIo fs) o argv = ok (c', o') ∧
      c'.val = c.toNat

/-- **The model conforms**: an exit code at the model instance is one at an instance that
answers as the snapshot and keeps the two maps' contracts. -/
theorem CanGive.conforming {args : List String} {fs : ConLeche.FS} {c : UInt8}
    (h : CanGive args fs c) : CanGiveConforming args fs c :=
  have ⟨argv, o, o', c', hargv, hrun, hc⟩ := h
  ⟨Model.Tape, Model.snapshotIo fs, o, o', argv, c', Model.snapshotIo_answersAs fs,
    Model.snapshotIo_poolSound fs, Model.snapshotIo_codesSound fs, hargv, hrun, hc⟩

end ConRon

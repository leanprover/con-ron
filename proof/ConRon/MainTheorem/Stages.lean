import ConRon.Bridge.Stages
import ConRon.Refine2.Checker.Top
import ConRon.Refine2.Frontend.Top
import ConRon.Refine2.Frontend.Prepare
import ConRon.Refine2.Checker.Pins
import ConRon.Refine2.Checker.Init
import ConRon.Refine2.Checker.PinsWF
import ConRon.Refine2.Checker.Phased
import ConRon.Refine2.Frontend.Source
import ConRon.Bridge.Inductives.Decl
import ConLeche.MainTheorem
import ConRon.Refine2.Frontend.Olean.ReadOleans
import ConRon.Bridge.Compare.Stages
import ConRon.Bridge.Compare.StagesOleans
import ConRon.Refine2.Checker.Mates
import ConRon.Refine2.Frontend.Compare
import ConRon.Bridge.Modular.Stages
import ConRon.Refine2.Modular.Graph
import ConRon.Bridge.Modular.Home
import ConRon.Bridge.Modular.ReachGo
import ConRon.Refine2.Modular.WorkerRead
import ConRon.Refine2.Modular.ReachCheck
import ConRon.Refine2.Checker.PoolFrom

/-!
# `ConRon.MainTheorem.Stages` — the staged lemmas: Theorem 2 ∘ Theorem 1 ∘ con-leche

The main theorems (`ConRon/MainTheorem.lean`) are proved from these lemmas.  Each states, for
one mode of the binary, what follows from the verified calls the driver makes in that mode:
one premise per call, in the driver's order, each starting from the state the previous one
left and the first from the binary's own start values.  The driver walks of
`MainTheorem/*.lean` take an exit 0 of the extracted driver `run_args` to exactly these
premises, and `MainTheorem/Conclusions.lean` turns the conclusions here into con-leche's words.
This is the one module that imports both `ConRon.Bridge` (Theorem 1, (B) ⇒ (A)) and
`ConRon.Refine2` (Theorem 2, (C) ⇒ (B)):

* `model_exists` / `no_False_declaration` — a lean4export file (`driver::check_main`);
* `no_False_oleans` / `model_exists_oleans` — the same on `--olean` (`check_main::check_oleans`);
* `model_exists_compare` / `no_False_compare` and `model_exists_oleans_compare` /
  `no_False_oleans_compare` — a challenge checked with its axioms justified by a solution
  (`driver::compare_json`, `driver::compare`; §4b and §4c), about the challenge alone;
* `model_modular` and its compared forms — the graph check and a module's worker
  (`driver::graph`, `driver::worker`, `driver::modular`, `driver::compare_module`).

The calls are marked `// ConRon.MainTheorem.Stages: <premise>` in the driver's Rust.

## The pipeline, stage by stage

On a lean4export file the driver (`crates/con-ron-core/src/driver/check_main.rs`) calls, in
this order, on one `AState` made from `AState::empty()` and one `PersTier::empty()`:

    intern_reserved_pins → builtin_prelude_e → parse_source (FileChunks)
      → prepare_d → decode_embedded → intern_all_pins → (the check phase)

**The check phase** (`check_main::check_phase`) builds the stream's index from the records
(`stream_index::build_index`), freezes the tier with the index in it (`checker::freeze_tier`),
runs every record's job on the instance's worker map, and thaws the tier.  The lemmas take one
premise per step (`h6` the index, `h7` the freeze, `h8` the map), which `poolAccepts_intro`
assembles into `Refine2/Checker/Phased.lean`'s `PoolAccepts`.  `h8` is the worker map's
contract (`PoolSound`) at the driver's step (`ParallelAll` at `jobStep`): index lists, one per
worker, covering every job, each in increasing order, and for each a fold of `run_job` over its
indices from `worker_state`, accepting.

The proof:

1. **Theorem 2, per stage** — `Refine2`'s `…_refines` lemmas walk the Rust runs
   into twin runs from the twin's own start state `AState.init EStore.empty`,
   related at every step (`AStateRel₀`/`AStateInv`: lockstep); `rust_stages`;
2. **Theorem 1** — `Bridge/Stages.lean` takes the twin runs:
   `Arena.pooledAccepts_bridge` makes the check phase's accept con-leche's pure
   fold `checkDeclsPure` accepting the denoted stream at `streamEnv` of it;
3. **con-leche** — `checkDeclsPure_sound_of` turns the pure accept into a model,
   and `no_proof_of_False_pure` refutes a `False` theorem in the stream.

## The named hypotheses

The lemmas start from the binary's own start values (`startState` =
`AState::empty()`, `emptyTier` = `PersTier::empty()`) and name the call the
driver makes at each step.  Beside `[ConLeche.SetTheory V]`, the file's shape
`hfalse` and the one premise per call (`h1`…`h5`, `hpins`, `h6`…`h8`), what
they assume is exactly:

* `hreads : ReadsAs sinst src chunks.val` — the reads are the chunks: the driver
  parses with the verified reader loop `parse_source` over `FileChunks`, and
  `Refine2/Frontend/Source.lean`'s `parse_source_eq` makes that `parse_chunks` over
  the chunks the reads hand out; the walk proves the reads are the file's bytes in
  the snapshot (`fileChunks_loop`);
* on `--olean`, `hsnap : SnapshotOf finst fsv F` — the file instance answers as
  one snapshot `F`.

`hpins` is the premise for the binary's pin step: the pin list is what the verified
decoder read, at any text (as con-leche's theorems hold at every pin list);
`model_exists_embedded` / `no_False_declaration_embedded` fix the text to the embedded
`PINS_TEXT`.
-/

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.MainTheorem.Stages

set_option autoImplicit false

universe w

/-! ## 1. The Rust side: the stages, walked into the twin by Theorem 2 -/

section Rust

open ConRon.Refine2 ConRon.Refine2.Frontend

/-- **The Rust pipeline, walked into the twin.**  Accepting Rust runs from the driver's start
state give accepting twin runs from the twin's, at the abstracted values, with the Rust's final
state related to the twin's.  Theorem 2's top lemmas, one per stage, all lockstep (`AStateRel₀`,
no precondition on the twin). -/
theorem rust_stages
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    {text : Slice Std.U8}
    (hdec : kernel.pins_decode.decode text = ok (.Ok pins))
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    {pers : arena.store.PersTier} {est : arena.store.EStore}
    (hfz : pers.frozen = false)
    {st0 st1 st2 st3 st4 st5 st6 : arena.monad.AState}
    {pre : frontend.prepare.PreludeIx} {r : frontend.export_c.ParseResultD}
    {ds : alloc.vec.Vec arena.env.IDeclaration}
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ix : arena.stream_index.IStreamIndex}
    (hest : arena.store.EStore.empty = ok est)
    (hst0 : arena.monad.AState.init est = ok st0)
    (h1 : arena.pins.intern_reserved_pins pers st0 = ok (.Ok (), st1))
    (h2 : frontend.prelude.builtin_prelude_e pers st1 = ok (.Ok pre, st2))
    {Sc : Type} {sinst : frontend.export_c.ChunkSource Sc} {src src' : Sc}
    (hreads : ReadsAs sinst src chunks.val)
    (h3 : frontend.export_c.parse_source sinst pers st2 src = ok (.Ok r, st3, src'))
    (h4 : frontend.prepare.prepare_prelude pers st3 pre r.decls = ok (.Ok ds, st4))
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins pers st4 pins maxNatSize = ok (.Ok ipins, st5))
    (h6 : PoolAccepts pers st5 .Verified ipins ds ix st6) :
    ∃ (sA sB sC sD sE sF : ConRon.Arena.AState)
      (rv : ConRon.Arena.Frontend.ParseResultD) (I : ConRon.Arena.IStreamIndex),
      ConRon.Arena.internReservedPins
          (ConRon.Arena.AState.init ConRon.Arena.EStore.empty) = .ok ((), sA) ∧
      ConRon.Arena.Frontend.builtinPreludeE sA = .ok (.ok (absPreludeIx pre), sB) ∧
      ConRon.Arena.Frontend.parseChunks (absChunks chunks) sB = .ok (.ok rv, sC) ∧
      ConRon.Arena.Frontend.preparePrelude (absPreludeIx pre) rv.decls sC
          = .ok ((absIDeclL ds).toArray, sD) ∧
      ConRon.Arena.internAllPins (ConRon.Refine.absPins pins)
          (ConRon.Refine.Nat.toNat maxNatSize) sD
          = .ok (absINatOpPinSetL ipins, sE) ∧
      ConRon.Arena.PooledAccepts .verified (absINatOpPinSetL ipins)
          (absIDeclL ds).toArray sE I sF ∧
      AStateRel₀ pers st6 sF := by
  obtain ⟨hrel0, hinv0, -⟩ := init_rel (pers := pers) hfz hest hst0
  -- 1. the reserved pins
  obtain ⟨sA, hA, hrelA, hinvA⟩ :=
    (intern_reserved_pins_refines hrel0 hinv0 h1).dest
  -- 2. the prelude
  obtain ⟨preL, sB, hB, hpreL, hrelB, hinvB⟩ :=
    builtin_prelude_e_refines scanSpec hrelA hinvA h2
  subst hpreL
  -- 3. the stream: the reader loop IS `parse_chunks` over the chunks read
  have h3' := parse_source_eq hreads h3
  obtain ⟨rv, sC, hC, hrv, hrelC, hinvC⟩ :=
    parse_chunks_refines scanSpec hrelB hinvB h3'
  -- 4. the preparation
  obtain ⟨sD, hD, hrelD, hinvD⟩ :=
    (prepare_prelude_refines hrelC hinvC h4).apply
  have hdecls : rv.decls = absIDeclArr r.decls := hrv.decls
  have hD' : ConRon.Arena.Frontend.preparePrelude (absPreludeIx pre) rv.decls sC
      = .ok ((absIDeclL ds).toArray, sD) := by
    rw [hdecls]; exact hD
  -- 5. the startup pin walk
  obtain ⟨sE, hE, hrelE, hinvE⟩ :=
    (intern_all_pins_refines hrelD hinvD
      (ConRon.Refine.PinsWF.decode_wf_refine2 hdec) h5).dest
  -- 6. the check phase, as the binary runs it, pool and all
  obtain ⟨I, sF, hF, hrelF, -⟩ := pool_accepts_refines hrelE hinvE hfz h6
  exact ⟨sA, sB, sC, sD, sE, sF, rv, I, hA, hB, hC, hD', hE, hF, hrelF⟩

end Rust

/-! ## The `.olean` path at the Rust

The driver's calls on `--olean` are `rust_stages`'s, the stream's two replaced: the roots' names
interned one by one (`check_main::intern_names`), and `records::read_oleans` over the store, at
the instance's file operations; the preparation reads what a record uses off the
read (`prepare_d` at the `OleanRead`), and each theorem's job reads its value from its file. -/

section RustOleans

open ConRon.Refine2 ConRon.Refine2.Frontend ConRon.Refine2.Frontend.Olean

/-- **The instance answers as one snapshot `F`**, at the paths the reader asks (`PathRel`): the file
seam's premise, as `ReadsAs` is the stream's.  Each answer the instance gives is `F`'s; a failing
operation claims nothing, since it gives the reader no accept. -/
structure SnapshotOf {Fs : Type} (inst : frontend.checker_io.CheckerFs Fs) (fsv : Fs)
    (F : ConLeche.FS) : Prop where
  path_exists : ∀ {p q}, PathRel p q → ∀ b, inst.path_exists fsv p = ok (.Ok b) →
    b = (F.real q).isSome
  is_dir : ∀ {p q}, PathRel p q → ∀ b, inst.is_dir fsv p = ok (.Ok b) → b = F.dir q
  real_path : ∀ {p q}, PathRel p q → ∀ r, inst.real_path fsv p = ok (.Ok r) →
    F.real q = some ⟨ConRon.Refine.absString r⟩ ∧ ConRon.Refine.StrWF r
  read_bin_file : ∀ {p q}, PathRel p q → ∀ b, inst.read_bin_file fsv p = ok (.Ok b) →
    F.file q = some (absBytes (alloc.vec.Vec.deref b))
  read_range : ∀ {p q}, PathRel p q → ∀ off len b, inst.read_range fsv p off len = ok (.Ok b) →
    ∃ whole, F.file q = some whole ∧ absBytes (alloc.vec.Vec.deref b) =
      whole.extract off.val (min (off.val + len.val) whole.size)
  file_size : ∀ {p q}, PathRel p q → ∀ s, inst.file_size fsv p = ok (.Ok s) →
    ∃ whole, F.file q = some whole ∧ s.val = whole.size

/-- The instance of a snapshot answers as the snapshot's record. -/
theorem fsRel_of_snapshot {Fs : Type} {inst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    {F : ConLeche.FS} (h : SnapshotOf inst fsv F) :
    FsRel inst fsv (ConRon.Bridge.Frontend.Olean.modelFs F) where
  pathExists := fun hp b hb => by
    rw [h.path_exists hp b hb]
    rfl
  isDir := fun hp b hb => by
    rw [h.is_dir hp b hb]
    rfl
  realPath := fun hp r hr => by
    obtain ⟨h1, h2⟩ := h.real_path hp r hr
    simp only [ConRon.Bridge.Frontend.Olean.modelFs, h1]
    exact ⟨trivial, h2⟩
  readBinFile := fun hp b hb => by
    simp only [ConRon.Bridge.Frontend.Olean.modelFs, h.read_bin_file hp b hb]
  readRange := fun hp off len b hb => by
    obtain ⟨whole, h1, h2⟩ := h.read_range hp off len b hb
    simp only [ConRon.Bridge.Frontend.Olean.modelFs, h1, h2]
  fileSize := fun hp s hs => by
    obtain ⟨whole, h1, h2⟩ := h.file_size hp s hs
    simp only [ConRon.Bridge.Frontend.Olean.modelFs, h1, h2]

/-- **The driver's loop over the roots** (`check_main::intern_names`): each name interned, the
next from the state the last left.  A name's strings are code points (`NameWF`); the command line's
are, by `parse_mod_name`. -/
def InternRoots (pers : arena.store.PersTier) :
    arena.monad.AState → List kernel.name.Name → List arena.handle.NIdx → arena.monad.AState → Prop
  | st, [], [], st' => st' = st
  | st, n :: ns, h :: hs, st' => ConRon.Refine.NameWF n ∧
      ∃ st₁, arena.monad.intern_name pers st n = ok (.Ok h, st₁) ∧ InternRoots pers st₁ ns hs st'
  | _, _, _, _ => False

theorem internRoots_refines {pers : arena.store.PersTier} :
    ∀ (names : List kernel.name.Name) (roots : List arena.handle.NIdx)
      {st st' : arena.monad.AState} {lst : ConRon.Arena.AState},
      InternRoots pers st names roots st' → AStateRel₀ pers st lst → AStateInv pers st →
      ∃ lst', (names.map ConRon.Refine.absName).mapM ConRon.Arena.internName lst
          = .ok (roots.map absNIdx, lst') ∧ AStateRel₀ pers st' lst' ∧ AStateInv pers st'
  | [], [], st, st', lst, h, hrel, hinv => by
    obtain rfl : st' = st := h
    exact ⟨lst, rfl, hrel, hinv⟩
  | [], _ :: _, _, _, _, h, _, _ => h.elim
  | _ :: _, [], _, _, _, h, _, _ => h.elim
  | n :: ns, x :: xs, st, st', lst, h, hrel, hinv => by
    obtain ⟨hwf, st₁, h1, h2⟩ := h
    obtain ⟨hS, -⟩ := intern_name_run'₀ n hwf hrel hinv h1
    obtain ⟨lst₁, hl, hrel₁, hinv₁⟩ := hS.apply
    obtain ⟨lst', hl', hrel', hinv'⟩ := internRoots_refines ns xs h2 hrel₁ hinv₁
    refine ⟨lst', ?_, hrel', hinv'⟩
    simp only [List.map_cons, List.mapM_cons]
    have hl2 : ConRon.Arena.internName (ConRon.Refine.absName n) lst = .ok (absNIdx x, lst₁) := hl
    simp only [Bind.bind, StateT.bind, hl2, Except.bind, hl']
    rfl

/-- **The Rust pipeline on `--olean`, walked into the twin**: `rust_stages`, the parse replaced by
the interned roots and the reader, at the snapshot's record. -/
theorem rust_stages_oleans (hT2 : ReadOleansRefines)
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    {text : Slice Std.U8}
    (hdec : kernel.pins_decode.decode text = ok (.Ok pins))
    {pers : arena.store.PersTier} {est : arena.store.EStore}
    (hfz : pers.frozen = false)
    {st0 st1 st2 st4 st5 st6 : arena.monad.AState}
    {pre : frontend.prepare.PreludeIx} {rd : frontend.olean.records.OleanRead}
    {prepared : frontend.prepare.Prepared}
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ix : arena.stream_index.IStreamIndex}
    (hest : arena.store.EStore.empty = ok est)
    (hst0 : arena.monad.AState.init est = ok st0)
    (h1 : arena.pins.intern_reserved_pins pers st0 = ok (.Ok (), st1))
    (h2 : frontend.prelude.builtin_prelude_e pers st1 = ok (.Ok pre, st2))
    {names : List kernel.name.Name} {roots : alloc.vec.Vec arena.handle.NIdx}
    {stR : arena.monad.AState} (hroots : InternRoots pers st2 names roots.val stR)
    {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs} {F : ConLeche.FS}
    (hsnap : SnapshotOf finst fsv F)
    {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {store3 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv pers stR.store ⟨dirs, alloc.vec.Vec.new _⟩ roots none false false
      = ok (.Ok rd, store3))
    (h4 : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts pers { stR with store := store3 } pre rd.decls rd
      = ok (.Ok prepared, st4))
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins pers st4 pins maxNatSize = ok (.Ok ipins, st5))
    (h6 : OleanPoolAccepts finst fsv pers st5 .Verified ipins prepared.decls rd.pins rd.values ⟨dirs, alloc.vec.Vec.new _⟩ ix st6) :
    ∃ (sA sB sB' sC sD sE sF : ConRon.Arena.AState) (rd' : ConRon.Arena.Frontend.Olean.OleanRead)
      (I : ConRon.Arena.IStreamIndex),
      ConRon.Arena.internReservedPins
          (ConRon.Arena.AState.init ConRon.Arena.EStore.empty) = .ok ((), sA) ∧
      ConRon.Arena.Frontend.builtinPreludeE sA = .ok (.ok (absPreludeIx pre), sB) ∧
      (names.map ConRon.Refine.absName).mapM ConRon.Arena.internName sB
          = .ok (roots.val.map absNIdx, sB') ∧
      ConRon.Arena.Frontend.Olean.readOleans (ConRon.Bridge.Frontend.Olean.modelFs F)
          (absSearchPath dirs) (roots.val.map absNIdx).toArray none false false sB' = .ok (.ok rd', sC) ∧
      ConRon.Arena.Frontend.prepareD (absPreludeIx pre) rd'.decls rd'.usedOf sC
          = .ok (absPrepared prepared, sD) ∧
      ConRon.Arena.internAllPins (ConRon.Refine.absPins pins)
          (ConRon.Refine.Nat.toNat maxNatSize) sD
          = .ok (absINatOpPinSetL ipins, sE) ∧
      ConRon.Arena.PooledOleanAccepts (ConRon.Bridge.Frontend.Olean.modelFs F) rd'.pins
          (absSearchPath dirs) rd'.values .verified (absINatOpPinSetL ipins)
          (absIDeclL prepared.decls).toArray sE I sF ∧
      AStateRel₀ pers st6 sF := by
  obtain ⟨hrel0, hinv0, -⟩ := init_rel (pers := pers) hfz hest hst0
  obtain ⟨sA, hA, hrelA, hinvA⟩ :=
    (intern_reserved_pins_refines hrel0 hinv0 h1).dest
  obtain ⟨preL, sB, hB, hpreL, hrelB, hinvB⟩ :=
    builtin_prelude_e_refines scanSpec hrelA hinvA h2
  subst hpreL
  obtain ⟨sB', hR, hrelR, hinvR⟩ := internRoots_refines names roots.val hroots hrelB hinvB
  have hfs := fsRel_of_snapshot hsnap
  obtain ⟨rd', sC, hC, hrd, hrelC, hinvC⟩ := hT2 hfs hrelR hinvR h3
  obtain ⟨sD, hD, hrelD, hinvD⟩ :=
    (prepare_d_refines (olean_read_used_rel hrd) hrelC hinvC h4).apply
  have hdecls : absIDeclArr rd.decls = rd'.decls := by
    simp [absIDeclArr, hrd.decls]
  rw [hdecls] at hD
  obtain ⟨sE, hE, hrelE, hinvE⟩ :=
    (intern_all_pins_refines hrelD hinvD
      (ConRon.Refine.PinsWF.decode_wf_refine2 hdec) h5).dest
  obtain ⟨I, sF, hF, hrelF, -⟩ :=
    olean_pool_accepts_refines (values' := rd'.values) hfs hrd.values hrelE hinvE hfz h6
  rw [hrd.pins] at hF
  exact ⟨sA, sB, sB', sC, sD, sE, sF, rd', I, hA, hB, hR, hC, hD, hE, hF, hrelF⟩

end RustOleans

/-! ## 3. The binary's start values, and what its records denote

The driver starts every run from `AState::empty()` (which is
`AState::init(EStore::empty())`) and `PersTier::empty()`.  The Aeneas model of each is a `Result` that is
`ok`; `startState` and `emptyTier` are those values, written out: every table and
map empty, every flag down, no pins.  `startState_eq` checks the first against the
Aeneas model by unfolding it, for `startState_init`, which the proof reads;
`emptyTier` is read off `PersTier::empty` by eye. -/

section Defs

open ConRon.Refine2 ConRon.Refine2.Frontend

/-- `HashMap2::new()` (`ron/hashmap2.rs`): no entries, no slots, epoch 1. -/
def emptyMap (K V : Type) : ron.hashmap2.HashMap2 K V :=
  { num_entries := 0#usize, max_load := 0#usize, epoch := 1#u32, fit_hw := 0#usize,
    slots := alloc.vec.Vec.new _ }

/-- `ConsMap::new()` (`arena/cons_map.rs`): no entries, no slots, epoch 1. -/
def emptyCons (I : Type) : arena.cons_map.ConsMap I :=
  { num_entries := 0#usize, max_load := 0#usize, epoch := 1#u16, fit_hw := 0#usize,
    slots := alloc.vec.Vec.new _ }

/-- `Tbl::empty()` (`arena/store.rs`): no rows, an empty index. -/
def emptyTbl (A I D : Type) : arena.store.Tbl A I D :=
  { rows := alloc.vec.Vec.new _, cons := emptyCons I }

/-- `NTables::empty()`: the name tables, every one empty. -/
def emptyNTables : arena.store.NTables :=
  { anons := emptyTbl _ _ _, strs := emptyTbl _ _ _, nums := emptyTbl _ _ _ }

/-- `LTables::empty()`: the level tables, every one empty. -/
def emptyLTables : arena.store.LTables :=
  { zeros := emptyTbl _ _ _, succs := emptyTbl _ _ _, maxs := emptyTbl _ _ _,
    imaxs := emptyTbl _ _ _, params := emptyTbl _ _ _ }

/-- `LsTables::empty()`: the level-list table, empty. -/
def emptyLsTables : arena.store.LsTables := { lists := emptyTbl _ _ _ }

/-- `ETables::empty()`: the expression tables, every one empty. -/
def emptyETables : arena.store.ETables :=
  { bvars := emptyTbl _ _ _, fvars := emptyTbl _ _ _, sorts := emptyTbl _ _ _,
    consts := emptyTbl _ _ _, apps := emptyTbl _ _ _, lams := emptyTbl _ _ _,
    foralls := emptyTbl _ _ _, lets := emptyTbl _ _ _, lits := emptyTbl _ _ _,
    projs := emptyTbl _ _ _ }

/-- `stream_index_empty()` (`arena/stream_index.rs`): no constants, no tables, no records, not
frozen. -/
def emptyIndex : arena.stream_index.IStreamIndex :=
  { consts := alloc.vec.Vec.new _, idx := emptyMap _ _, tables := alloc.vec.Vec.new _,
    tbls := emptyMap _ _, firsts := alloc.vec.Vec.new _, next := 0#u64,
    lits := alloc.vec.Vec.new _, nat_from := none, str_from := none }

/-- **The binary's persistent tier**, `PersTier::empty()`: the tier every stage up to the check phase is handed — not
frozen, its four table sets, every table empty, and the empty stream index. -/
def emptyTier : arena.store.PersTier :=
  { frozen := false, n := emptyNTables, l := emptyLTables, ls := emptyLsTables,
    e := emptyETables, env := emptyIndex }

/-- **The binary's start state**, `AState::empty()`, which is `AState::init(EStore::empty())`: a store whose four layers (names,
levels, level lists, expressions) have both tiers empty and the scratch flag down,
empty memo tables and caches, and no pins (`startState_eq`). -/
def startState : arena.monad.AState :=
  { store :=
      { lss :=
          { ls :=
              { ns := { pers := emptyNTables, scr := emptyNTables,
                        scratch_on := false },
                pers := emptyLTables, scr := emptyLTables,
                scratch_on := false },
            pers := emptyLsTables, scr := emptyLsTables,
            scratch_on := false },
        pers := emptyETables, scr := emptyETables,
        scratch_on := false },
    memos :=
      { inst1_c := emptyMap _ _, inst_l_c := emptyMap _ _, lift_c := emptyMap _ _,
        abs1_c := emptyMap _ _,
        inst1_l_c := emptyMap _ _, inst_lp_c := emptyMap _ _,
        bvar_b_c := emptyMap _ _, fvar_b_c := emptyMap _ _, inst_lp_l_c := emptyMap _ _,
        inst_lp_ls_c := emptyMap _ _, lp_def_c := emptyMap _ _, crf_c := emptyMap _ _,
        hlbi_c := emptyMap _ _ },
    caches :=
      { whnf_core_c := emptyMap _ _, whnf_core_cheap_c := emptyMap _ _,
        whnf_c := emptyMap _ _, infer_c := emptyMap _ _,
        infer_io_c := emptyMap _ _, defeq_c := emptyMap _ _,
        lvl_eq_c := emptyMap _ _, lvls_eq_c := emptyMap _ _, const_ty_c := emptyMap _ _,
        const_val_c := emptyMap _ _, rule_body_c := emptyMap _ _, read_l_c := emptyMap _ _,
        read_n_c := emptyMap _ _, read_ls_c := emptyMap _ _,
        eager_memos :=
          { whnf_core_c := emptyMap _ _, whnf_core_cheap_c := emptyMap _ _,
            whnf_c := emptyMap _ _, infer_c := emptyMap _ _,
            infer_io_c := emptyMap _ _, defeq_c := emptyMap _ _ } },
    pins :=
      { names := alloc.vec.Vec.new _, reserved := alloc.vec.Vec.new _,
        empty_levels := { word := 0#u32 }, zero_level := { word := 0#u32 },
        sort_one := { word := 0#u32 },
        max_nat_size := { limbs := .from [134217728#u64] (by scalar_tac) } } }

/-- `max_nat_size_default` is the one-limb `2^27` of `startState`'s pins. -/
theorem max_nat_size_default_eq :
    arena.pins.max_nat_size_default = ok { limbs := .from [134217728#u64] (by scalar_tac) } := by
  rw [arena.pins.max_nat_size_default, ron.nat.from_u64, ite_eq_right (by decide),
    alloc.vec.Vec.push.eq_def]
  dsimp only
  split
  · simp
  · exfalso
    obtain ⟨w, hw, -⟩ := ConRon.Refine.vec_singleton (134217728#u64)
    rw [alloc.vec.Vec.push.eq_def] at hw
    simp_all

theorem startState_eq : arena.monad.AState.empty = ok startState := by
  simp only [arena.monad.AState.empty, arena.store.Tbl.empty, arena.store.ETables.empty,
    arena.store.LsTables.empty, arena.store.LTables.empty, arena.store.NTables.empty,
    arena.store.NStore.empty, arena.store.LStore.empty, arena.store.LsStore.empty,
    arena.store.EStore.empty, ron.hashmap2.HashMap2.new, arena.cons_map.ConsMap.new,
    arena.monad.AState.init, arena.monad.Memos.empty, arena.core_state.Caches.empty,
    arena.core_state.ModeMemos.empty, arena.pins.Pins.empty, arena.handle.LsIdx.of_word, arena.handle.LIdx.of_word,
    arena.handle.EIdx.of_word, max_nat_size_default_eq, bind_ok]
  rfl

/-- `startState` is `AState::init(EStore::empty())`, the form `rust_stages`
takes. -/
theorem startState_init : ∃ est, arena.store.EStore.empty = ok est ∧
    arena.monad.AState.init est = ok startState := by
  have h := startState_eq
  rw [arena.monad.AState.empty] at h
  exact ConRon.Refine.bind_eq_ok_iff.mp h

/-- **What the Rust's records denote**: the Rust's final state `st`, read through the twin,
holds records `ds` that denote con-leche's stream `dsP`, and `env` is the environment of that
stream (`streamEnv`: every record's constants and tables, in order).  Theorem 2 relates the Rust
state to a twin state (`AStateRel`, at the binary's `emptyTier`), and Theorem 1's `denoteDecls`
reads the records in that twin store.  (The arena has no abstraction FUNCTION from the Rust's
store to con-leche's terms — the store is abstracted by a relation — so the records' meaning can
only be spelled through the twin.) -/
def RustDenotes (ds : alloc.vec.Vec arena.env.IDeclaration) (st : arena.monad.AState)
    (env : ConLeche.Env) : Prop :=
  ∃ (lst : ConRon.Arena.AState) (dsP : List ConLeche.Declaration),
    AStateRel emptyTier st lst ∧ ConRon.Bridge.denoteDecls lst.store (absIDeclL ds) = some dsP ∧
      env = ConLeche.streamEnv dsP

/-- **What the Rust's records denote on `--olean`**: `RustDenotes`, each theorem's reference
replaced by a value (`fillDecl`): the records of an `--olean` run hold a reference where a
theorem's value is, and each theorem's job reads the value from its file. -/
def RustDenotesFilled (ds : alloc.vec.Vec arena.env.IDeclaration) (st : arena.monad.AState)
    (env : ConLeche.Env) : Prop :=
  ∃ (lst : ConRon.Arena.AState) (dsP : List ConLeche.Declaration) (val : Nat → ConLeche.Expr),
    AStateRel emptyTier st lst ∧ ConRon.Bridge.denoteDecls lst.store (absIDeclL ds) = some dsP ∧
      env = ConLeche.streamEnv
        (dsP.map (ConLeche.Cached.fillDecl (ConRon.Bridge.fillRef val)))

/-- `prepare::prepare_d` at `DeclUsedConsts`, the call the driver makes on a stream
(`check_main::check_main`), is `prepare_prelude`'s body: `prepare_prelude` is its `.decls`. -/
theorem prepare_prelude_of_prepare_d {pers : arena.store.PersTier}
    {st st' : arena.monad.AState} {pre : frontend.prepare.PreludeIx}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {p : frontend.prepare.Prepared}
    (h : frontend.prepare.prepare_d frontend.nat_op_ground.DeclUsedConsts.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts pers st pre ds () = ok (.Ok p, st')) :
    frontend.prepare.prepare_prelude pers st pre ds = ok (.Ok p.decls, st') := by
  rw [frontend.prepare.prepare_prelude, h]
  simp only [bind_ok]
  rfl

/-- `pins_decode::decode_embedded()`, the call the driver's
`check_main::embedded_pins` makes, is `decode` of some text. -/
theorem decode_of_decode_embedded
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (h : kernel.pins_decode.decode_embedded = ok (.Ok pins)) :
    ∃ text, kernel.pins_decode.decode text = ok (.Ok pins) := by
  rw [kernel.pins_decode.decode_embedded] at h
  obtain ⟨text, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  exact ⟨text, h⟩

end Defs

/-! ## 4. The staged lemmas of a lean4export file

Each takes one premise per call the verified driver's `check_main::check_main` makes, in its
order, each starting from the state the previous one left and the first from the binary's own
start values; `MainTheorem/Driver.lean`'s `check_main_zero` takes an exit 0 to exactly these
premises (`JsonStages`).

| premise | the driver's call (`driver/check_main.rs`) |
|---|---|
| `startState`, `emptyTier` | `check_main`'s `AState::empty()`, `PersTier::empty()` |
| `h1` | `check_main`'s `pins::intern_reserved_pins` |
| `h2` | `check_main`'s `prelude::builtin_prelude_e` |
| `hreads`, `h3` | `check_main`'s `export_c::parse_source` over `FileChunks`, the positional reads of the file |
| `h4` | `check_main`'s `prepare::prepare_d` at `DeclUsedConsts` |
| `hpins` | `embedded_pins`: `pins_decode::decode_embedded()`, `decode` of the embedded `PINS_TEXT` (the `_embedded` forms below name it) |
| `h5` | `check_main`'s `checker::intern_all_pins` at `--max-nat-size`'s value (default `pins::max_nat_size_default()`); the lemmas hold at every `maxNatSize` |
| `h6` | `check_phase`'s `stream_index::build_index(…, stream_index_empty(), ds, 0)` at `CheckMode::Verified` |
| `h7` | `check_phase`'s `checker::freeze_tier` |
| `h8` | `check_phase`'s worker map `par_map_workers` over `JobStep` (`init` `checker::worker_state`, `step` `checker::run_job`); `thaw_tier` then restores the store |

`h8` is not one equation: the worker map is the instance's, so `h8` states its contract
(`PoolSound`, OVERVIEW §3.1) at the driver's step, `Refine2/Checker/Phased.lean`'s `ParallelAll` at `jobStep`: some lists of record
positions, one per worker, together covering every position, each in increasing order, and
for each list the worker's run, `worker_state st6.pins` and then `run_job` on each position
in order, every step answering `Ok(())`.  A job is not asked to be claimed once.  Each job is a
fact about the worker's state at its position: the earlier records' jobs give the fold's
prefix (`Bridge/Checker/Pooled.lean`'s `pooled_fold`).

The lemmas hold at every chunk source whose reads are `chunks`, and every pin text `hpins`
decodes, as con-leche's theorems hold at every pin list.

`hpins` is stated about `decode` of a free text rather than about `decode_embedded` because
naming the embedded constant `PINS_TEXT` costs the census one axiom,
`kernel.pins_text.PINS_TEXT._native.decide.ax_1` — the one Aeneas's `toStr` spends on that
constant's DEFINITION (AENEAS_FINDINGS.md §3.8; `Refine2/Checker/PinsWF.lean`'s census),
nothing this proof evaluates.  `model_exists_embedded` / `no_False_declaration_embedded` are
the lemmas with `decode_embedded` itself in the premise, and carry that axiom.

**`--olean`.**  `no_False_oleans` and `model_exists_oleans` take the same calls with the
stream's replaced, as `check_main::check_oleans` makes them (`MainTheorem/Oleans.lean`'s
`check_oleans_zero` is the walk):

| premise | the driver's call (`driver/check_main.rs`) |
|---|---|
| `hroots` | `intern_names`: `monad::intern_name` on each root |
| `hsnap`, `h3` | `check_oleans`'s `records::read_oleans` at the instance's file operations, whose answers are one snapshot's |
| `h4` | `check_oleans`'s `prepare::prepare_d` at the `OleanRead` |
| `h8` | `check_phase_olean`'s worker map over `OleanJobStep`, `init` `(worker_state, value_cache_empty)` and `step` `olean_job` |

`h4` starts from the state `hroots` left with the store `h3` left: the reader takes the store
alone.  `hcl`, `hv`, `hmem`, `hk`, `hty` are upstream's, by the specification (`InClosure`,
`ViewOf`: `decodeModuleSpec`).  `--constant` is outside them, as a run from `constants =
none`.  Each is its `_of` form, which takes Theorem 2 at the reader as `hT2 :
ReadOleansRefines` (`Refine2/Frontend/Olean/Contract.lean`), at `read_oleans_refines`. -/

section Headline

open ConRon.Refine2 ConRon.Refine2.Frontend ConRon.Refine2.Frontend.Olean

/-- con-leche: ConLeche/MainTheorem.lean:102 model_exists —
**THE MAIN THEOREM FOR THE RUST CHECKER** (DESIGN.md §1, §8.2): the environment of every stream
the Rust checker accepts has a model, in every set theory.

con-leche's reads `(accepted : checkDecls .verified pins maxNatSize ds = .ok env) : Nonempty (Model V env)`;
here the accepting run is the binary's calls, one premise each (§4's table), and the environment
is the one the Rust's records denote (`RustDenotes`).

Composition only: `rust_stages` (Theorem 2), `stages_model` (Theorem 1 + con-leche). -/
theorem model_exists (V : Type w) [ConLeche.SetTheory V]
    {st1 st2 st3 st4 st5 st6 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    {Sc : Type} {sinst : frontend.export_c.ChunkSource Sc} {src src' : Sc}
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    (hreads : ReadsAs sinst src chunks.val)
    {r : frontend.export_c.ParseResultD}
    (h3 : frontend.export_c.parse_source sinst emptyTier st2 src = ok (.Ok r, st3, src'))
    {prepared : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d frontend.nat_op_ground.DeclUsedConsts.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier st3 pre r.decls () = ok (.Ok prepared, st4))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins maxNatSize = ok (.Ok ipins, st5))
    {ix : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st5 e prepared.decls 0#usize) = ok (.Ok ix, st6))
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store ix = ok (tier, frozen))
    (h8 : ParallelAll prepared.decls.length (arena.checker.worker_state st6.pins)
      (jobStep tier .Verified ipins prepared.decls)) :
    ∃ env, RustDenotes prepared.decls st6 env ∧ Nonempty (ConLeche.Model V env) := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  -- Theorem 1's two tier specs, discharged
  have hk : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel :=
    ConRon.Bridge.CoreSpec.of_core
  have hind : ConRon.Bridge.IndSpec :=
    ConRon.Bridge.Inductives.indSpec_of_bridge
  obtain ⟨sA, sB, sC, sD, sE, sF, rv, I, hA, hB, hC, hD, hE, hF, hrelF⟩ :=
    rust_stages hpins rfl hest hst0 h1 h2 hreads h3 (prepare_prelude_of_prepare_d h4) h5
      (poolAccepts_intro h6 h7 h8)
  obtain ⟨hwfF, dsP, hden, ⟨hmod⟩⟩ := ConRon.Bridge.stages_model V hk hind hA hB hC hD hE hF
  exact ⟨_, ⟨sF, dsP, hrelF.of₀ hwfF, by simpa using hden, rfl⟩,
    ⟨ConLeche.Model.Model.ofEnvModelM hmod⟩⟩

/-- con-leche: ConLeche/MainTheorem.lean:116 no_False_declaration — **A FILE THAT DECLARES A
THEOREM OF TYPE `False` IS REJECTED BY THE RUST CHECKER**: the binary's calls (§4's table)
cannot all succeed on it.

con-leche's concludes `∃ e, (do …; checkDecls .verified pins maxNatSize ds) = .error e` about its own
pipeline; the binary's is not one function (the pool is a contract, `h8`), so the letter here has
the same premises as `model_exists` and concludes `False`.

Composition only: `rust_stages` (Theorem 2), `stages_no_False` (Theorem 1 + con-leche). -/
theorem no_False_declaration (V : Type w) [ConLeche.SetTheory V]
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    (hfalse : ConLeche.jsonWithTheoremFalse (absChunks chunks))
    {st1 st2 st3 st4 st5 st6 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    {Sc : Type} {sinst : frontend.export_c.ChunkSource Sc} {src src' : Sc}
    (hreads : ReadsAs sinst src chunks.val)
    {r : frontend.export_c.ParseResultD}
    (h3 : frontend.export_c.parse_source sinst emptyTier st2 src = ok (.Ok r, st3, src'))
    {prepared : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d frontend.nat_op_ground.DeclUsedConsts.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier st3 pre r.decls () = ok (.Ok prepared, st4))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins maxNatSize = ok (.Ok ipins, st5))
    {ix : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st5 e prepared.decls 0#usize) = ok (.Ok ix, st6))
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store ix = ok (tier, frozen))
    (h8 : ParallelAll prepared.decls.length (arena.checker.worker_state st6.pins)
      (jobStep tier .Verified ipins prepared.decls)) :
    False := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  have hk : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel :=
    ConRon.Bridge.CoreSpec.of_core
  have hind : ConRon.Bridge.IndSpec :=
    ConRon.Bridge.Inductives.indSpec_of_bridge
  obtain ⟨sA, sB, sC, sD, sE, sF, rv, I, hA, hB, hC, hD, hE, hF, -⟩ :=
    rust_stages hpins rfl hest hst0 h1 h2 hreads h3 (prepare_prelude_of_prepare_d h4) h5
      (poolAccepts_intro h6 h7 h8)
  exact ConRon.Bridge.stages_no_False V hk hind (pins := ConRon.Refine.absPins pins) hfalse
    hA hB hC hD hE hF

/-- `model_exists` with the pin premise the driver's own call,
`pins_decode::decode_embedded()` (`check_main::embedded_pins`).  Its census adds
`kernel.pins_text.PINS_TEXT._native.decide.ax_1` (§4's note). -/
theorem model_exists_embedded (V : Type w) [ConLeche.SetTheory V]
    {st1 st2 st3 st4 st5 st6 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    {Sc : Type} {sinst : frontend.export_c.ChunkSource Sc} {src src' : Sc}
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    (hreads : ReadsAs sinst src chunks.val)
    {r : frontend.export_c.ParseResultD}
    (h3 : frontend.export_c.parse_source sinst emptyTier st2 src = ok (.Ok r, st3, src'))
    {prepared : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d frontend.nat_op_ground.DeclUsedConsts.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier st3 pre r.decls () = ok (.Ok prepared, st4))
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode_embedded = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins maxNatSize = ok (.Ok ipins, st5))
    {ix : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st5 e prepared.decls 0#usize) = ok (.Ok ix, st6))
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store ix = ok (tier, frozen))
    (h8 : ParallelAll prepared.decls.length (arena.checker.worker_state st6.pins)
      (jobStep tier .Verified ipins prepared.decls)) :
    ∃ env, RustDenotes prepared.decls st6 env ∧ Nonempty (ConLeche.Model V env) :=
  have ⟨_, hdec⟩ := decode_of_decode_embedded hpins
  model_exists V h1 h2 hreads h3 h4 hdec h5 h6 h7 h8

/-- `no_False_declaration` with the pin premise the driver's own call,
`pins_decode::decode_embedded()` (`check_main::embedded_pins`).  Its census adds
`kernel.pins_text.PINS_TEXT._native.decide.ax_1` (§4's note). -/
theorem no_False_declaration_embedded (V : Type w) [ConLeche.SetTheory V]
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    (hfalse : ConLeche.jsonWithTheoremFalse (absChunks chunks))
    {st1 st2 st3 st4 st5 st6 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    {Sc : Type} {sinst : frontend.export_c.ChunkSource Sc} {src src' : Sc}
    (hreads : ReadsAs sinst src chunks.val)
    {r : frontend.export_c.ParseResultD}
    (h3 : frontend.export_c.parse_source sinst emptyTier st2 src = ok (.Ok r, st3, src'))
    {prepared : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d frontend.nat_op_ground.DeclUsedConsts.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier st3 pre r.decls () = ok (.Ok prepared, st4))
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode_embedded = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins maxNatSize = ok (.Ok ipins, st5))
    {ix : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st5 e prepared.decls 0#usize) = ok (.Ok ix, st6))
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store ix = ok (tier, frozen))
    (h8 : ParallelAll prepared.decls.length (arena.checker.worker_state st6.pins)
      (jobStep tier .Verified ipins prepared.decls)) :
    False :=
  have ⟨_, hdec⟩ := decode_of_decode_embedded hpins
  no_False_declaration V hfalse h1 h2 hreads h3 h4 hdec h5 h6 h7 h8

/-- con-leche: ConLeche/MainTheorem.lean:166 main_oleans_no_False — **A CLOSURE THAT HOLDS A
THEOREM OF TYPE `False` IS REJECTED BY THE RUST CHECKER'S `--olean`**: on a snapshot `F` of the
files (`hsnap`), where the private view of a module of the closure of the roots, by con-leche's
specification (`InClosure`, `ViewOf`: nothing about the fast parser), holds a theorem of type
`False`, the binary's calls cannot all succeed.  `hT2` is Theorem 2 at the reader,
`Refine2/Frontend/Olean/Contract.lean`.

Composition only: `rust_stages_oleans` (Theorem 2), `stagesO_no_False` (Theorem 1). -/
theorem no_False_oleans_of (hT2 : ReadOleansRefines)
    (V : Type w) [ConLeche.SetTheory V] {F : ConLeche.FS}
    {m : ConLeche.Name} {d : ConLeche.Frontend.Olean.ModDecoded}
    {c : ConLeche.Frontend.Olean.CEntryF ConLeche.Name ConLeche.Expr} {v : ConLeche.Expr}
    {all : List ConLeche.Name}
    {names : List kernel.name.Name} {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    (hcl : ConLeche.Frontend.Olean.InClosure (ConRon.Refine2.Frontend.Olean.absSearchPath dirs) F
      (names.map ConRon.Refine.absName).toArray m)
    (hv : ConLeche.Frontend.Olean.ViewOf (ConRon.Refine2.Frontend.Olean.absSearchPath dirs) F m d)
    (hmem : c ∈ d.constants) (hk : c.kind = .thm v all)
    (hty : c.type = .const ConLeche.falseName [])
    {st1 st2 stR st4 st5 st6 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    {roots : alloc.vec.Vec arena.handle.NIdx}
    (hroots : InternRoots emptyTier st2 names roots.val stR)
    {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    (hsnap : SnapshotOf finst fsv F)
    {rd : frontend.olean.records.OleanRead} {store3 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store ⟨dirs, alloc.vec.Vec.new _⟩ roots none false false
      = ok (.Ok rd, store3))
    {prepared : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier { stR with store := store3 } pre rd.decls rd
      = ok (.Ok prepared, st4))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins maxNatSize = ok (.Ok ipins, st5))
    {ix : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st5 e prepared.decls 0#usize) = ok (.Ok ix, st6))
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store ix = ok (tier, frozen))
    (h8 : ParallelAll prepared.decls.length (oleanWorkerInit st6.pins)
      (oleanJobStep finst fsv tier .Verified ipins prepared.decls rd.pins rd.values ⟨dirs, alloc.vec.Vec.new _⟩)) :
    False := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  have hkc : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel :=
    ConRon.Bridge.CoreSpec.of_core
  have hind : ConRon.Bridge.IndSpec :=
    ConRon.Bridge.Inductives.indSpec_of_bridge
  obtain ⟨sA, sB, sB', sC, sD, sE, sF, rd', I, hA, hB, hR, hC, hD, hE, hF, -⟩ :=
    rust_stages_oleans hT2 hpins rfl hest hst0 h1 h2 hroots hsnap h3 h4 h5
      (oleanPoolAccepts_intro h6 h7 h8)
  exact ConRon.Bridge.stagesO_no_False V hkc hind (pins := ConRon.Refine.absPins pins) hcl hv
    hmem hk hty hA hB hR hC hD hE hF

/-- con-leche: ConLeche/Model/Fold.lean:306 checkDeclsPure_sound_of — **the environment of
every stream the Rust checker's `--olean` accepts has a model**, in every set theory, on a
snapshot of the files: the records' stream with each theorem's reference replaced by a value
(`RustDenotesFilled`).  `hT2` as in `no_False_oleans_of`.  Upstream states no model theorem
for `--olean`; this is `model_exists` at the filled stream. -/
theorem model_exists_oleans_of (hT2 : ReadOleansRefines)
    (V : Type w) [ConLeche.SetTheory V] {F : ConLeche.FS}
    {names : List kernel.name.Name} {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    {st1 st2 stR st4 st5 st6 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    {roots : alloc.vec.Vec arena.handle.NIdx}
    (hroots : InternRoots emptyTier st2 names roots.val stR)
    {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    (hsnap : SnapshotOf finst fsv F)
    {rd : frontend.olean.records.OleanRead} {store3 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store ⟨dirs, alloc.vec.Vec.new _⟩ roots none false false
      = ok (.Ok rd, store3))
    {prepared : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier { stR with store := store3 } pre rd.decls rd
      = ok (.Ok prepared, st4))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins maxNatSize = ok (.Ok ipins, st5))
    {ix : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st5 e prepared.decls 0#usize) = ok (.Ok ix, st6))
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store ix = ok (tier, frozen))
    (h8 : ParallelAll prepared.decls.length (oleanWorkerInit st6.pins)
      (oleanJobStep finst fsv tier .Verified ipins prepared.decls rd.pins rd.values ⟨dirs, alloc.vec.Vec.new _⟩)) :
    ∃ env, RustDenotesFilled prepared.decls st6 env ∧ Nonempty (ConLeche.Model V env) := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  have hkc : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel :=
    ConRon.Bridge.CoreSpec.of_core
  have hind : ConRon.Bridge.IndSpec :=
    ConRon.Bridge.Inductives.indSpec_of_bridge
  obtain ⟨sA, sB, sB', sC, sD, sE, sF, rd', I, hA, hB, hR, hC, hD, hE, hF, hrelF⟩ :=
    rust_stages_oleans hT2 hpins rfl hest hst0 h1 h2 hroots hsnap h3 h4 h5
      (oleanPoolAccepts_intro h6 h7 h8)
  obtain ⟨hwfF, dsP, val, hden, ⟨hmod⟩⟩ :=
    ConRon.Bridge.stagesO_model V hkc hind (F := F) (pins := ConRon.Refine.absPins pins)
      hA hB hR hC hD hE hF
  exact ⟨_, ⟨sF, dsP, val, hrelF.of₀ hwfF, by simpa using hden, rfl⟩,
    ⟨ConLeche.Model.Model.ofEnvModelM hmod⟩⟩

/-- con-leche: ConLeche/MainTheorem.lean:166 main_oleans_no_False — **A CLOSURE THE RUST
CHECKER'S `--olean` ACCEPTS HOLDS NO PROOF OF `False`**: if a module of the import closure of
the roots, read by the specification (`InClosure`, `ViewOf`), holds a theorem whose type is
`False`, the binary's calls cannot all succeed.  The files are a premise: `hsnap`, the instance
answers as one snapshot `F`.

Composition only: `no_False_oleans_of` at `read_oleans_refines` (Theorem 2 at the reader). -/
theorem no_False_oleans (V : Type w) [ConLeche.SetTheory V] {F : ConLeche.FS}
    {m : ConLeche.Name} {d : ConLeche.Frontend.Olean.ModDecoded}
    {c : ConLeche.Frontend.Olean.CEntryF ConLeche.Name ConLeche.Expr} {v : ConLeche.Expr}
    {all : List ConLeche.Name}
    {names : List kernel.name.Name} {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    (hcl : ConLeche.Frontend.Olean.InClosure (ConRon.Refine2.Frontend.Olean.absSearchPath dirs) F
      (names.map ConRon.Refine.absName).toArray m)
    (hv : ConLeche.Frontend.Olean.ViewOf (ConRon.Refine2.Frontend.Olean.absSearchPath dirs) F m d)
    (hmem : c ∈ d.constants) (hk : c.kind = .thm v all)
    (hty : c.type = .const ConLeche.falseName [])
    {st1 st2 stR st4 st5 st6 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    {roots : alloc.vec.Vec arena.handle.NIdx}
    (hroots : InternRoots emptyTier st2 names roots.val stR)
    {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    (hsnap : SnapshotOf finst fsv F)
    {rd : frontend.olean.records.OleanRead} {store3 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store ⟨dirs, alloc.vec.Vec.new _⟩ roots none false false
      = ok (.Ok rd, store3))
    {prepared : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier { stR with store := store3 } pre rd.decls rd
      = ok (.Ok prepared, st4))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins maxNatSize = ok (.Ok ipins, st5))
    {ix : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st5 e prepared.decls 0#usize) = ok (.Ok ix, st6))
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store ix = ok (tier, frozen))
    (h8 : ParallelAll prepared.decls.length (oleanWorkerInit st6.pins)
      (oleanJobStep finst fsv tier .Verified ipins prepared.decls rd.pins rd.values ⟨dirs, alloc.vec.Vec.new _⟩)) :
    False :=
  no_False_oleans_of read_oleans_refines V hcl hv hmem hk hty h1 h2 hroots hsnap h3 h4 hpins
    h5 h6 h7 h8

/-- con-leche: ConLeche/Model/Fold.lean:306 checkDeclsPure_sound_of — **the environment of
every stream the Rust checker's `--olean` accepts has a model**, in every set theory, on a
snapshot of the files (`hsnap`).

Composition only: `model_exists_oleans_of` at `read_oleans_refines` (Theorem 2 at the reader). -/
theorem model_exists_oleans (V : Type w) [ConLeche.SetTheory V] {F : ConLeche.FS}
    {names : List kernel.name.Name} {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    {st1 st2 stR st4 st5 st6 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    {roots : alloc.vec.Vec arena.handle.NIdx}
    (hroots : InternRoots emptyTier st2 names roots.val stR)
    {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    (hsnap : SnapshotOf finst fsv F)
    {rd : frontend.olean.records.OleanRead} {store3 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store ⟨dirs, alloc.vec.Vec.new _⟩ roots none false false
      = ok (.Ok rd, store3))
    {prepared : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier { stR with store := store3 } pre rd.decls rd
      = ok (.Ok prepared, st4))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins maxNatSize = ok (.Ok ipins, st5))
    {ix : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st5 e prepared.decls 0#usize) = ok (.Ok ix, st6))
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store ix = ok (tier, frozen))
    (h8 : ParallelAll prepared.decls.length (oleanWorkerInit st6.pins)
      (oleanJobStep finst fsv tier .Verified ipins prepared.decls rd.pins rd.values ⟨dirs, alloc.vec.Vec.new _⟩)) :
    ∃ env, RustDenotesFilled prepared.decls st6 env ∧ Nonempty (ConLeche.Model V env) :=
  model_exists_oleans_of read_oleans_refines V h1 h2 hroots hsnap h3 h4 hpins h5 h6 h7 h8

end Headline

/-! ## 4b. The compared run: `--compare -- C S`

A challenge file `C` checked with its axioms justified by a solution file `S`
(`driver/compare_json.rs`'s `compare_json`), one premise per call, in its order, on the one
state from the binary's start values (`MainTheorem/CompareJson.lean`'s `compare_json_zero` is
the walk):

| premise | `compare_json`'s call |
|---|---|
| `startState`, `emptyTier` | `AState::empty()`, `&PersTier::empty()` |
| `h1`, `h2` | `intern_reserved_pins`, `prelude::builtin_prelude_e` (`start`) |
| `hreadsC`, `h3` | `read_export` on `C`: `export_c::parse_source` over `FileChunks` |
| `hreadsS`, `h3S` | the same on `S`, into the same store |
| `hdup` | `prepare::prelude_ix_dup`: the challenge's copy of the prelude |
| `h4S` | `prepare::prepare_d` on `S`'s records at `DeclUsedConsts` |
| `hpins`, `h5` | `check_main::embedded_pins`, `checker::intern_all_pins` |
| `h6S`, `h7S`, `h8S` | the solution's `check_main::check_phase` at `sol = None`: `build_index`, `freeze_tier`, the worker map over `run_job`; `thaw_tier` then hands back the index `ixS` and the store `st7` exactly (`freeze_tier_ok`) |
| `h4` | `prepare::prepare_d` on `C`'s records at the copy `preC` |
| `hside` | `justify::side_records` (each hole the axiom of its statement) |
| `hsol` | `justify::solution_of(ixS, &recsC)` |
| `h6`, `h7`, `h8` | the challenge's `check_phase` at `sol = Some(&sol)` |

The conclusion is about the challenge alone, as upstream's `main_compare_json_model`: the
records its check phase checks (`recsC`) denote a stream whose environment has a model;
`no_False_compare`: a challenge file declaring a theorem of type `False` is not accepted.  The
solution's run is a premise like any other call.  The theorems hold at every chunk source
whose reads are the two files' chunks and at every pin text `hpins` decodes. -/

section Compare

open ConRon.Refine2 ConRon.Refine2.Frontend

/-- **The compared run's Rust pipeline, walked into the twin**: `rust_stages` with the second
parse, the solution's check phase, the challenge's preparation at the prelude's copy
(`prelude_ix_dup_abs`), its side records (`side_records_ls`), the solution
(`solution_of_rel`) and its check phase at it (`pool_accepts_sol_refines`). -/
theorem rust_stages_compare
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    {text : Slice Std.U8}
    (hdec : kernel.pins_decode.decode text = ok (.Ok pins))
    {chunksC chunksS : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    {pers : arena.store.PersTier} {est : arena.store.EStore}
    (hfz : pers.frozen = false)
    {st0 st1 st2 st3 st4 st5 st6 st7 st9 st10 st11 : arena.monad.AState}
    {pre preC : frontend.prepare.PreludeIx} {rC rS : frontend.export_c.ParseResultD}
    {dsS dsC recsC : alloc.vec.Vec arena.env.IDeclaration}
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ixS ixC : arena.stream_index.IStreamIndex} {sol : arena.justify.Solution}
    (hest : arena.store.EStore.empty = ok est)
    (hst0 : arena.monad.AState.init est = ok st0)
    (h1 : arena.pins.intern_reserved_pins pers st0 = ok (.Ok (), st1))
    (h2 : frontend.prelude.builtin_prelude_e pers st1 = ok (.Ok pre, st2))
    {Sc : Type} {sinst : frontend.export_c.ChunkSource Sc} {srcC srcC' srcS srcS' : Sc}
    (hreadsC : ReadsAs sinst srcC chunksC.val) (hreadsS : ReadsAs sinst srcS chunksS.val)
    (h3 : frontend.export_c.parse_source sinst pers st2 srcC = ok (.Ok rC, st3, srcC'))
    (h3S : frontend.export_c.parse_source sinst pers st3 srcS = ok (.Ok rS, st4, srcS'))
    (hdup : frontend.prepare.prelude_ix_dup pre = ok preC)
    (h4S : frontend.prepare.prepare_prelude pers st4 pre rS.decls = ok (.Ok dsS, st5))
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins pers st5 pins maxNatSize = ok (.Ok ipins, st6))
    (h6S : PoolAccepts pers st6 .Verified ipins dsS ixS st7)
    (h4 : frontend.prepare.prepare_prelude pers st7 preC rC.decls = ok (.Ok dsC, st9))
    (hside : arena.justify.side_records pers st9 dsC 0#usize (alloc.vec.Vec.new _) =
      ok (.Ok recsC, st10))
    (hsol : arena.justify.solution_of ixS recsC = ok sol)
    (h6 : PoolAcceptsSol pers st10 .Verified ipins (some sol) recsC ixC st11) :
    ∃ (sA sB sC sC' sD sE sF sG sH sI : ConRon.Arena.AState)
      (rvC rvS : ConRon.Arena.Frontend.ParseResultD) (IS IC : ConRon.Arena.IStreamIndex),
      ConRon.Arena.internReservedPins
          (ConRon.Arena.AState.init ConRon.Arena.EStore.empty) = .ok ((), sA) ∧
      ConRon.Arena.Frontend.builtinPreludeE sA = .ok (.ok (absPreludeIx pre), sB) ∧
      ConRon.Arena.Frontend.parseChunks (absChunks chunksC) sB = .ok (.ok rvC, sC) ∧
      ConRon.Arena.Frontend.parseChunks (absChunks chunksS) sC = .ok (.ok rvS, sC') ∧
      ConRon.Arena.Frontend.preparePrelude (absPreludeIx pre) rvS.decls sC'
          = .ok ((absIDeclL dsS).toArray, sD) ∧
      ConRon.Arena.internAllPins (ConRon.Refine.absPins pins)
          (ConRon.Refine.Nat.toNat maxNatSize) sD
          = .ok (absINatOpPinSetL ipins, sE) ∧
      ConRon.Arena.PooledAccepts .verified (absINatOpPinSetL ipins)
          (absIDeclL dsS).toArray sE IS sF ∧
      ConRon.Arena.Frontend.preparePrelude (absPreludeIx pre) rvC.decls sF
          = .ok ((absIDeclL dsC).toArray, sG) ∧
      ConRon.Arena.sideRecordsGo [] (absIDeclL dsC) sG = .ok (absIDeclL recsC, sH) ∧
      ConRon.Arena.PooledAcceptsJ .verified (absINatOpPinSetL ipins)
          (some (ConRon.Arena.solutionOf IS (absIDeclL recsC))) (absIDeclL recsC).toArray
          sH IC sI ∧
      AStateRel₀ pers st10 sH := by
  obtain ⟨hrel0, hinv0, -⟩ := init_rel (pers := pers) hfz hest hst0
  -- 1. the reserved pins, 2. the prelude
  obtain ⟨sA, hA, hrelA, hinvA⟩ :=
    (intern_reserved_pins_refines hrel0 hinv0 h1).dest
  obtain ⟨preL, sB, hB, hpreL, hrelB, hinvB⟩ :=
    builtin_prelude_e_refines scanSpec hrelA hinvA h2
  subst hpreL
  -- 3. the two files, into the one store
  obtain ⟨rvC, sC, hC, hrvC, hrelC, hinvC⟩ :=
    parse_chunks_refines scanSpec hrelB hinvB (parse_source_eq hreadsC h3)
  obtain ⟨rvS, sC', hCS, hrvS, hrelCS, hinvCS⟩ :=
    parse_chunks_refines scanSpec hrelC hinvC (parse_source_eq hreadsS h3S)
  -- 4. the solution's preparation, 5. the pins
  obtain ⟨sD, hD, hrelD, hinvD⟩ :=
    (prepare_prelude_refines hrelCS hinvCS h4S).apply
  have hD' : ConRon.Arena.Frontend.preparePrelude (absPreludeIx pre) rvS.decls sC'
      = .ok ((absIDeclL dsS).toArray, sD) := by
    rw [hrvS.decls]; exact hD
  obtain ⟨sE, hE, hrelE, hinvE⟩ :=
    (intern_all_pins_refines hrelD hinvD
      (ConRon.Refine.PinsWF.decode_wf_refine2 hdec) h5).dest
  -- 6. the solution's check phase
  obtain ⟨IS, sF, hF, hrelF, hIS⟩ := pool_accepts_refines hrelE hinvE hfz h6S
  have hinvF : AStateInv pers st7 := by
    obtain ⟨_, _, hB', -⟩ := h6S
    exact (build_index_empty_refines hrelE hinvE hB').choose_spec.choose_spec.2.2.1
  -- 7. the challenge's preparation, at the prelude's copy
  obtain ⟨sG, hG, hrelG, hinvG⟩ :=
    (prepare_prelude_refines hrelF hinvF h4).apply
  have hG' : ConRon.Arena.Frontend.preparePrelude (absPreludeIx pre) rvC.decls sF
      = .ok ((absIDeclL dsC).toArray, sG) := by
    rw [← prelude_ix_dup_abs hdup, hrvC.decls]; exact hG
  -- 8. its side records, 9. the solution
  obtain ⟨recsL, sH, hH, hrecs, hrelH, hinvH⟩ :=
    side_records_ls dsC 0#usize st9 sG (alloc.vec.Vec.new _) hrelG hinvG _ _ hside
  have hrecs' : recsL = absIDeclL recsC := hrecs
  subst hrecs'
  have hH' : ConRon.Arena.sideRecordsGo [] (absIDeclL dsC) sG = .ok (absIDeclL recsC, sH) := by
    exact hH
  have hJ : OptSolRel (some sol) (some (ConRon.Arena.solutionOf IS (absIDeclL recsC))) :=
    solution_of_rel hIS hsol
  -- 10. the challenge's check phase, at the solution
  obtain ⟨IC, sI, hI, -, -, -⟩ := pool_accepts_sol_refines hJ hrelH hinvH hfz h6
  exact ⟨sA, sB, sC, sC', sD, sE, sF, sG, sH, sI, rvC, rvS, IS, IC, hA, hB, hC, hCS, hD', hE,
    hF, hG', hH', hI, hrelH⟩

end Compare

section RustOleansCompare

open ConRon.Refine2 ConRon.Refine2.Frontend ConRon.Refine2.Frontend.Olean

/-- **The compared `--olean` run's Rust pipeline, walked into the twin**: `rust_stages_oleans`
with the two names, the challenge's read (lenient, with its homes) and preparation at the
prelude's copy, its holes (`hole_records_ls`), the solution's read (lenient) and preparation,
its check phase, the challenge's side records, the solution and the challenge's check phase at
it (`olean_pool_accepts_sol_refines`).  `hT2` is the reader's Theorem 2, as in
`rust_stages_oleans`. -/
theorem rust_stages_oleans_compare (hT2 : ReadOleansRefines)
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    {text : Slice Std.U8}
    (hdec : kernel.pins_decode.decode text = ok (.Ok pins))
    {pers : arena.store.PersTier} {est : arena.store.EStore}
    (hfz : pers.frozen = false)
    {st0 st1 st2 st4 st4h st5 st6 st7 st10 st11 : arena.monad.AState}
    {pre : frontend.prepare.PreludeIx} {F : ConLeche.FS}
    (hest : arena.store.EStore.empty = ok est)
    (hst0 : arena.monad.AState.init est = ok st0)
    (h1 : arena.pins.intern_reserved_pins pers st0 = ok (.Ok (), st1))
    (h2 : frontend.prelude.builtin_prelude_e pers st1 = ok (.Ok pre, st2))
    {c s : kernel.name.Name} {ch sh : arena.handle.NIdx} {stR1 stR : arena.monad.AState}
    (hwfC : ConRon.Refine.NameWF c) (hwfS : ConRon.Refine.NameWF s)
    (hnC : arena.monad.intern_name pers st2 c = ok (.Ok ch, stR1))
    (hnS : arena.monad.intern_name pers stR1 s = ok (.Ok sh, stR))
    {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    (hsnap : SnapshotOf finst fsv F)
    {cr sr : frontend.olean.files.Roots} {rootsC rootsS : alloc.vec.Vec arena.handle.NIdx}
    (hrC : rootsC.val = [ch]) (hrS : rootsS.val = [sh])
    {rdC rdS : frontend.olean.records.OleanRead} {store3 store5 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv pers stR.store cr rootsC none true true
      = ok (.Ok rdC, store3))
    {preC : frontend.prepare.PreludeIx}
    (hdup : frontend.prepare.prelude_ix_dup pre = ok preC)
    {prepC : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts pers { stR with store := store3 } preC rdC.decls rdC
      = ok (.Ok prepC, st4))
    {holed : alloc.vec.Vec arena.env.IDeclaration}
    (hhole : frontend.compare.hole_records frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts rdC pers st4 prepC.decls 0#usize (alloc.vec.Vec.new _)
      = ok (.Ok holed, st4h))
    (h3S : frontend.olean.records.read_oleans finst fsv pers st4h.store sr rootsS none true false
      = ok (.Ok rdS, store5))
    {prepS : frontend.prepare.Prepared}
    (h4S : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts pers { st4h with store := store5 } pre rdS.decls rdS
      = ok (.Ok prepS, st5))
    {maxNatSize : ron.nat.Nat} {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    (h5 : arena.checker.intern_all_pins pers st5 pins maxNatSize = ok (.Ok ipins, st6))
    {ixS ixC : arena.stream_index.IStreamIndex}
    (h6S : OleanPoolAccepts finst fsv pers st6 .Verified ipins prepS.decls rdS.pins rdS.values sr
      ixS st7)
    {recsC : alloc.vec.Vec arena.env.IDeclaration}
    (hside : arena.justify.side_records pers st7 holed 0#usize (alloc.vec.Vec.new _) =
      ok (.Ok recsC, st10))
    {sol : arena.justify.Solution}
    (hsol : arena.justify.solution_of ixS recsC = ok sol)
    (h6 : OleanPoolAcceptsSol finst fsv pers st10 .Verified ipins recsC rdC.pins rdC.values cr
      (some sol) ixC st11) :
    ∃ (sA sB sB₁ sB₂ sC sD sD' sC₂ sD₂ sE sF sH sI : ConRon.Arena.AState)
      (rdC' rdS' : ConRon.Arena.Frontend.Olean.OleanRead) (IS IC : ConRon.Arena.IStreamIndex),
      ConRon.Arena.internReservedPins
          (ConRon.Arena.AState.init ConRon.Arena.EStore.empty) = .ok ((), sA) ∧
      ConRon.Arena.Frontend.builtinPreludeE sA = .ok (.ok (absPreludeIx pre), sB) ∧
      ConRon.Arena.internName (ConRon.Refine.absName c) sB = .ok (absNIdx ch, sB₁) ∧
      ConRon.Arena.internName (ConRon.Refine.absName s) sB₁ = .ok (absNIdx sh, sB₂) ∧
      ConRon.Arena.Frontend.Olean.readOleans (ConRon.Bridge.Frontend.Olean.modelFs F)
          (absRoots cr) #[absNIdx ch] none true true sB₂ = .ok (.ok rdC', sC) ∧
      ConRon.Arena.Frontend.prepareD (absPreludeIx pre) rdC'.decls rdC'.usedOf sC
          = .ok (absPrepared prepC, sD) ∧
      ConRon.Arena.Frontend.holeRecordsGo rdC'.usedOf [] (absPrepared prepC).decls.toList sD
          = .ok (absIDeclL holed, sD') ∧
      ConRon.Arena.Frontend.Olean.readOleans (ConRon.Bridge.Frontend.Olean.modelFs F)
          (absRoots sr) #[absNIdx sh] none true false sD' = .ok (.ok rdS', sC₂) ∧
      ConRon.Arena.Frontend.prepareD (absPreludeIx pre) rdS'.decls rdS'.usedOf sC₂
          = .ok (absPrepared prepS, sD₂) ∧
      ConRon.Arena.internAllPins (ConRon.Refine.absPins pins)
          (ConRon.Refine.Nat.toNat maxNatSize) sD₂
          = .ok (absINatOpPinSetL ipins, sE) ∧
      ConRon.Arena.PooledOleanAccepts (ConRon.Bridge.Frontend.Olean.modelFs F) rdS'.pins
          (absRoots sr) rdS'.values .verified (absINatOpPinSetL ipins)
          (absPrepared prepS).decls sE IS sF ∧
      ConRon.Arena.sideRecordsGo [] (absIDeclL holed) sF = .ok (absIDeclL recsC, sH) ∧
      ConRon.Arena.PooledOleanAcceptsJ (ConRon.Bridge.Frontend.Olean.modelFs F) rdC'.pins
          (absRoots cr) rdC'.values .verified (absINatOpPinSetL ipins)
          (some (ConRon.Arena.solutionOf IS (absIDeclL recsC))) (absIDeclL recsC).toArray
          sH IC sI ∧
      AStateRel₀ pers st10 sH := by
  obtain ⟨hrel0, hinv0, -⟩ := init_rel (pers := pers) hfz hest hst0
  obtain ⟨sA, hA, hrelA, hinvA⟩ :=
    (intern_reserved_pins_refines hrel0 hinv0 h1).dest
  obtain ⟨preL, sB, hB, hpreL, hrelB, hinvB⟩ :=
    builtin_prelude_e_refines scanSpec hrelA hinvA h2
  subst hpreL
  -- the two names
  obtain ⟨sB₁, hRC, hrelB₁, hinvB₁⟩ := (intern_name_run'₀ c hwfC hrelB hinvB hnC).1.apply
  obtain ⟨sB₂, hRS, hrelB₂, hinvB₂⟩ := (intern_name_run'₀ s hwfS hrelB₁ hinvB₁ hnS).1.apply
  have hfs := fsRel_of_snapshot hsnap
  have hrootsC : absNIdxArr rootsC = #[absNIdx ch] := by simp [absNIdxArr, hrC]
  have hrootsS : absNIdxArr rootsS = #[absNIdx sh] := by simp [absNIdxArr, hrS]
  -- the challenge: its read, its preparation at the copy, its holes
  obtain ⟨rdC', sC, hC, hrdC, hrelC, hinvC⟩ := hT2 hfs hrelB₂ hinvB₂ h3
  rw [hrootsC] at hC
  obtain ⟨sD, hD, hrelD, hinvD⟩ :=
    (prepare_d_refines (olean_read_used_rel hrdC) hrelC hinvC h4).apply
  have hdeclsC : absIDeclArr rdC.decls = rdC'.decls := by simp [absIDeclArr, hrdC.decls]
  rw [hdeclsC, prelude_ix_dup_abs hdup] at hD
  obtain ⟨holedL, sD', hH, hholed, hrelD', hinvD'⟩ :=
    hole_records_ls (olean_read_used_rel hrdC) prepC.decls 0#usize st4 sD
      (alloc.vec.Vec.new _) hrelD hinvD _ _ hhole
  have hholed' : holedL = absIDeclL holed := hholed
  subst hholed'
  -- the solution: its read and preparation, the pins, its check phase
  obtain ⟨rdS', sC₂, hCS, hrdS, hrelC₂, hinvC₂⟩ := hT2 hfs hrelD' hinvD' h3S
  rw [hrootsS] at hCS
  obtain ⟨sD₂, hDS, hrelD₂, hinvD₂⟩ :=
    (prepare_d_refines (olean_read_used_rel hrdS) hrelC₂ hinvC₂ h4S).apply
  have hdeclsS : absIDeclArr rdS.decls = rdS'.decls := by simp [absIDeclArr, hrdS.decls]
  rw [hdeclsS] at hDS
  obtain ⟨sE, hE, hrelE, hinvE⟩ :=
    (intern_all_pins_refines hrelD₂ hinvD₂
      (ConRon.Refine.PinsWF.decode_wf_refine2 hdec) h5).dest
  obtain ⟨IS, sF, hF, hrelF, hIS⟩ :=
    olean_pool_accepts_refines (values' := rdS'.values) hfs hrdS.values hrelE hinvE hfz h6S
  rw [hrdS.pins] at hF
  have hinvF : AStateInv pers st7 := by
    obtain ⟨_, _, hB', -⟩ := h6S
    exact (build_index_empty_refines hrelE hinvE hB').choose_spec.choose_spec.2.2.1
  -- the challenge's side records, the solution, its check phase
  obtain ⟨recsL, sH, hSd, hrecs, hrelH, hinvH⟩ :=
    side_records_ls holed 0#usize st7 sF (alloc.vec.Vec.new _) hrelF hinvF _ _ hside
  have hrecs' : recsL = absIDeclL recsC := hrecs
  subst hrecs'
  have hJ : OptSolRel (some sol) (some (ConRon.Arena.solutionOf IS (absIDeclL recsC))) :=
    solution_of_rel hIS hsol
  obtain ⟨IC, sI, hI, -, -, -⟩ :=
    olean_pool_accepts_sol_refines (values' := rdC'.values) hJ hfs hrdC.values hrelH hinvH hfz h6
  rw [hrdC.pins] at hI
  exact ⟨sA, sB, sB₁, sB₂, sC, sD, sD', sC₂, sD₂, sE, sF, sH, sI, rdC', rdS', IS, IC, hA, hB,
    hRC, hRS, hC, hD, hH, hCS, hDS, hE, hF, hSd, hI, hrelH⟩

end RustOleansCompare

section HeadlineCompare

open ConRon.Refine2 ConRon.Refine2.Frontend

/-- con-leche: ConLeche/MainTheorem.lean:63 main_compare_json_model — **AN ACCEPTED COMPARISON'S
CHALLENGE HAS A MODEL**: the binary's calls on `--compare -- C S` (§4b's table) accepting, the
records the challenge's check phase checks — `C`'s prepared records, each hole the axiom of its
statement — denote a stream whose environment has a model, in every set theory.  Nothing is
concluded about the solution, whose run is a premise.

Composition only: `rust_stages_compare` (Theorem 2), `stagesC_model` (Theorem 1 + con-leche's
comparison soundness over the mixed run). -/
theorem model_exists_compare (V : Type w) [ConLeche.SetTheory V]
    {st1 st2 st3 st4 st5 st6 st7 st9 st10 st11 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    {Sc : Type} {sinst : frontend.export_c.ChunkSource Sc} {srcC srcC' srcS srcS' : Sc}
    {chunksC chunksS : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    (hreadsC : ReadsAs sinst srcC chunksC.val) (hreadsS : ReadsAs sinst srcS chunksS.val)
    {rC rS : frontend.export_c.ParseResultD}
    (h3 : frontend.export_c.parse_source sinst emptyTier st2 srcC = ok (.Ok rC, st3, srcC'))
    (h3S : frontend.export_c.parse_source sinst emptyTier st3 srcS = ok (.Ok rS, st4, srcS'))
    {preC : frontend.prepare.PreludeIx}
    (hdup : frontend.prepare.prelude_ix_dup pre = ok preC)
    {prepS : frontend.prepare.Prepared}
    (h4S : frontend.prepare.prepare_d frontend.nat_op_ground.DeclUsedConsts.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier st4 pre rS.decls () = ok (.Ok prepS, st5))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st5 pins maxNatSize = ok (.Ok ipins, st6))
    {ixS : arena.stream_index.IStreamIndex}
    (h6S : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st6 e prepS.decls 0#usize) = ok (.Ok ixS, st7))
    {tierS : arena.store.PersTier} {frozenS : arena.store.EStore}
    (h7S : arena.checker.freeze_tier st7.store ixS = ok (tierS, frozenS))
    (h8S : ParallelAll prepS.decls.length (arena.checker.worker_state st7.pins)
      (jobStep tierS .Verified ipins prepS.decls))
    {prepC : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d frontend.nat_op_ground.DeclUsedConsts.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier st7 preC rC.decls () = ok (.Ok prepC, st9))
    {recsC : alloc.vec.Vec arena.env.IDeclaration}
    (hside : arena.justify.side_records emptyTier st9 prepC.decls 0#usize (alloc.vec.Vec.new _) =
      ok (.Ok recsC, st10))
    {sol : arena.justify.Solution}
    (hsol : arena.justify.solution_of ixS recsC = ok sol)
    {ixC : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st10 e recsC 0#usize) = ok (.Ok ixC, st11))
    {tierC : arena.store.PersTier} {frozenC : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st11.store ixC = ok (tierC, frozenC))
    (h8 : ParallelAll recsC.length (arena.checker.worker_state st11.pins)
      (jobStepSol tierC .Verified ipins (some sol) recsC)) :
    ∃ env, RustDenotes recsC st10 env ∧ Nonempty (ConLeche.Model V env) := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  have hk : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel :=
    ConRon.Bridge.CoreSpec.of_core
  have hind : ConRon.Bridge.IndSpec :=
    ConRon.Bridge.Inductives.indSpec_of_bridge
  obtain ⟨sA, sB, sC, sC', sD, sE, sF, sG, sH, sI, rvC, rvS, IS, IC, hA, hB, hC, hCS, hD, hE,
      hF, hG, hH, hI, hrelH⟩ :=
    rust_stages_compare hpins rfl hest hst0 h1 h2 hreadsC hreadsS h3 h3S hdup
      (prepare_prelude_of_prepare_d h4S) h5 (poolAccepts_intro h6S h7S h8S)
      (prepare_prelude_of_prepare_d h4) hside hsol (poolAcceptsSol_intro h6 h7 h8)
  obtain ⟨hwfH, rcC, preCU, dsP, -, -, hden, ⟨hmod⟩⟩ :=
    ConRon.Bridge.stagesC_model V hk hind hA hB hC hCS hD hE hF hG
      hH hI
  exact ⟨_, ⟨sH, dsP, hrelH.of₀ hwfH, hden, rfl⟩,
    ⟨ConLeche.Model.Model.ofEnvModelM hmod⟩⟩

/-- con-leche: ConLeche/MainTheorem.lean:63 main_compare_json_model — **A COMPARISON WHOSE
CHALLENGE FILE DECLARES A THEOREM OF TYPE `False` IS REJECTED**: the binary's calls on
`--compare -- C S` (§4b's table) cannot all succeed when `C` declares one, whatever `S` is.

Composition only: `rust_stages_compare` (Theorem 2), `stagesC_no_False` (Theorem 1 +
con-leche). -/
theorem no_False_compare (V : Type w) [ConLeche.SetTheory V]
    {chunksC chunksS : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    (hfalse : ConLeche.jsonWithTheoremFalse (absChunks chunksC))
    {st1 st2 st3 st4 st5 st6 st7 st9 st10 st11 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    {Sc : Type} {sinst : frontend.export_c.ChunkSource Sc} {srcC srcC' srcS srcS' : Sc}
    (hreadsC : ReadsAs sinst srcC chunksC.val) (hreadsS : ReadsAs sinst srcS chunksS.val)
    {rC rS : frontend.export_c.ParseResultD}
    (h3 : frontend.export_c.parse_source sinst emptyTier st2 srcC = ok (.Ok rC, st3, srcC'))
    (h3S : frontend.export_c.parse_source sinst emptyTier st3 srcS = ok (.Ok rS, st4, srcS'))
    {preC : frontend.prepare.PreludeIx}
    (hdup : frontend.prepare.prelude_ix_dup pre = ok preC)
    {prepS : frontend.prepare.Prepared}
    (h4S : frontend.prepare.prepare_d frontend.nat_op_ground.DeclUsedConsts.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier st4 pre rS.decls () = ok (.Ok prepS, st5))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st5 pins maxNatSize = ok (.Ok ipins, st6))
    {ixS : arena.stream_index.IStreamIndex}
    (h6S : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st6 e prepS.decls 0#usize) = ok (.Ok ixS, st7))
    {tierS : arena.store.PersTier} {frozenS : arena.store.EStore}
    (h7S : arena.checker.freeze_tier st7.store ixS = ok (tierS, frozenS))
    (h8S : ParallelAll prepS.decls.length (arena.checker.worker_state st7.pins)
      (jobStep tierS .Verified ipins prepS.decls))
    {prepC : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d frontend.nat_op_ground.DeclUsedConsts.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier st7 preC rC.decls () = ok (.Ok prepC, st9))
    {recsC : alloc.vec.Vec arena.env.IDeclaration}
    (hside : arena.justify.side_records emptyTier st9 prepC.decls 0#usize (alloc.vec.Vec.new _) =
      ok (.Ok recsC, st10))
    {sol : arena.justify.Solution}
    (hsol : arena.justify.solution_of ixS recsC = ok sol)
    {ixC : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st10 e recsC 0#usize) = ok (.Ok ixC, st11))
    {tierC : arena.store.PersTier} {frozenC : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st11.store ixC = ok (tierC, frozenC))
    (h8 : ParallelAll recsC.length (arena.checker.worker_state st11.pins)
      (jobStepSol tierC .Verified ipins (some sol) recsC)) :
    False := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  have hk : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel :=
    ConRon.Bridge.CoreSpec.of_core
  have hind : ConRon.Bridge.IndSpec :=
    ConRon.Bridge.Inductives.indSpec_of_bridge
  obtain ⟨sA, sB, sC, sC', sD, sE, sF, sG, sH, sI, rvC, rvS, IS, IC, hA, hB, hC, hCS, hD, hE,
      hF, hG, hH, hI, -⟩ :=
    rust_stages_compare hpins rfl hest hst0 h1 h2 hreadsC hreadsS h3 h3S hdup
      (prepare_prelude_of_prepare_d h4S) h5 (poolAccepts_intro h6S h7S h8S)
      (prepare_prelude_of_prepare_d h4) hside hsol (poolAcceptsSol_intro h6 h7 h8)
  exact ConRon.Bridge.stagesC_no_False V hk hind (pins := ConRon.Refine.absPins pins) hfalse
    hA hB hC hCS hD hE hF hG hH hI

end HeadlineCompare

/-! ## 4c. The compared `--olean` run: `--olean --compare -- C S`

`compare_oleans` (`driver/compare.rs`), the calls of `no_False_oleans` with the read replaced
by the compared run's two (`MainTheorem/CompareOleans.lean`'s `compare_oleans_zero` is the walk):

| premise | `compare_oleans`'s call |
|---|---|
| `hnC`, `hnS` | `monad::intern_name` on `C`, then on `S` |
| `hsnap`, `h3` | `records::read_oleans` of `C`'s closure at the challenge's lookup `cr`, lenient, with its homes (`foreign_constant`, driver-side, then checks none of them is foreign) |
| `hdup`, `h4` | `prelude_ix_dup`; `prepare::prepare_d` at the challenge's read |
| `hhole` | `frontend::compare::hole_records`: each theorem whose file marks it a hole, the axiom of its statement |
| `h3S`, `h4S` | `read_oleans` of `S`'s closure at the solution's lookup `sr`, lenient; its `prepare_d` |
| `hpins`, `h5` | the pins, as §4 |
| `h6S`, `h7S`, `h8S` | the solution's check phase (`olean_job` at `sol = None`); `thaw_tier` hands back `ixS` and `st7` |
| `hside`, `hsol` | `justify::side_records`, `justify::solution_of(ixS, &recsC)` |
| `h6`, `h7`, `h8` | the challenge's check phase, `olean_job` at `Some(&sol)` |

As in §4, `hcl`, `hv`, `hmem`, `hk`, `hty` are upstream's specification of the files, here of
the challenge's closure read through `cr`; the conclusion is about the challenge alone.  Both
reads are at `constants = none`: a run with `--constant` is outside the theorems.  `hrC`/`hrS`
say the driver's root vectors are the one interned name each. -/

section HeadlineOleansCompare

open ConRon.Refine2 ConRon.Refine2.Frontend ConRon.Refine2.Frontend.Olean

/-- con-leche: ConLeche/MainTheorem.lean:88 main_compare_model — **A COMPARED `--olean` RUN
WHOSE CHALLENGE'S CLOSURE HOLDS A THEOREM OF TYPE `False` IS REJECTED**: the binary's calls on
`--olean --compare -- C S` (§4c's table) cannot all succeed when a module of `C`'s import
closure, read by the specification through the challenge's lookup, holds a theorem whose type is
`False`.  `hT2` is the reader's Theorem 2 (`ReadOleansRefines`).

Composition only: `rust_stages_oleans_compare` (Theorem 2), `stagesOC_no_False` (Theorem 1 +
con-leche). -/
theorem no_False_oleans_compare_of (hT2 : ReadOleansRefines)
    (V : Type w) [ConLeche.SetTheory V] {F : ConLeche.FS}
    {m : ConLeche.Name} {d : ConLeche.Frontend.Olean.ModDecoded}
    {cc : ConLeche.Frontend.Olean.CEntryF ConLeche.Name ConLeche.Expr} {v : ConLeche.Expr}
    {all : List ConLeche.Name} {c : kernel.name.Name} {cr : frontend.olean.files.Roots}
    (hcl : ConLeche.Frontend.Olean.InClosure (absRoots cr) F #[ConRon.Refine.absName c] m)
    (hv : ConLeche.Frontend.Olean.ViewOf (absRoots cr) F m d)
    (hmem : cc ∈ d.constants) (hk : cc.kind = .thm v all)
    (hty : cc.type = .const ConLeche.falseName [])
    {st1 st2 st4 st4h st5 st6 st7 st10 st11 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    {s : kernel.name.Name} {ch sh : arena.handle.NIdx} {stR1 stR : arena.monad.AState}
    (hwfC : ConRon.Refine.NameWF c) (hwfS : ConRon.Refine.NameWF s)
    (hnC : arena.monad.intern_name emptyTier st2 c = ok (.Ok ch, stR1))
    (hnS : arena.monad.intern_name emptyTier stR1 s = ok (.Ok sh, stR))
    {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    (hsnap : SnapshotOf finst fsv F)
    {sr : frontend.olean.files.Roots} {rootsC rootsS : alloc.vec.Vec arena.handle.NIdx}
    (hrC : rootsC.val = [ch]) (hrS : rootsS.val = [sh])
    {rdC rdS : frontend.olean.records.OleanRead} {store3 store5 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store cr rootsC none true true
      = ok (.Ok rdC, store3))
    {preC : frontend.prepare.PreludeIx}
    (hdup : frontend.prepare.prelude_ix_dup pre = ok preC)
    {prepC : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier { stR with store := store3 } preC rdC.decls rdC
      = ok (.Ok prepC, st4))
    {holed : alloc.vec.Vec arena.env.IDeclaration}
    (hhole : frontend.compare.hole_records frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts rdC emptyTier st4 prepC.decls 0#usize (alloc.vec.Vec.new _)
      = ok (.Ok holed, st4h))
    (h3S : frontend.olean.records.read_oleans finst fsv emptyTier st4h.store sr rootsS none true false
      = ok (.Ok rdS, store5))
    {prepS : frontend.prepare.Prepared}
    (h4S : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier { st4h with store := store5 } pre rdS.decls rdS
      = ok (.Ok prepS, st5))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st5 pins maxNatSize = ok (.Ok ipins, st6))
    {ixS : arena.stream_index.IStreamIndex}
    (h6S : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st6 e prepS.decls 0#usize) = ok (.Ok ixS, st7))
    {tierS : arena.store.PersTier} {frozenS : arena.store.EStore}
    (h7S : arena.checker.freeze_tier st7.store ixS = ok (tierS, frozenS))
    (h8S : ParallelAll prepS.decls.length (oleanWorkerInit st7.pins)
      (oleanJobStep finst fsv tierS .Verified ipins prepS.decls rdS.pins rdS.values sr))
    {recsC : alloc.vec.Vec arena.env.IDeclaration}
    (hside : arena.justify.side_records emptyTier st7 holed 0#usize (alloc.vec.Vec.new _) =
      ok (.Ok recsC, st10))
    {sol : arena.justify.Solution}
    (hsol : arena.justify.solution_of ixS recsC = ok sol)
    {ixC : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st10 e recsC 0#usize) = ok (.Ok ixC, st11))
    {tierC : arena.store.PersTier} {frozenC : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st11.store ixC = ok (tierC, frozenC))
    (h8 : ParallelAll recsC.length (oleanWorkerInit st11.pins)
      (oleanJobStepSol finst fsv tierC .Verified ipins recsC rdC.pins rdC.values cr (some sol))) :
    False := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  have hkc : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel :=
    ConRon.Bridge.CoreSpec.of_core
  have hind : ConRon.Bridge.IndSpec :=
    ConRon.Bridge.Inductives.indSpec_of_bridge
  obtain ⟨sA, sB, sB₁, sB₂, sC, sD, sD', sC₂, sD₂, sE, sF, sH, sI, rdC', rdS', IS, IC, hA, hB,
      hRC, hRS, hC, hD, hH, hCS, hDS, hE, hF, hSd, hI, hrelH⟩ :=
    rust_stages_oleans_compare hT2 hpins rfl hest hst0 h1 h2 hwfC hwfS hnC hnS hsnap hrC hrS h3
      hdup h4 hhole h3S h4S h5 (oleanPoolAccepts_intro h6S h7S h8S) hside hsol
      (oleanPoolAcceptsSol_intro h6 h7 h8)
  exact ConRon.Bridge.stagesOC_no_False V hkc hind rfl rfl (pins := ConRon.Refine.absPins pins)
    hcl hv hmem hk hty hA hB hRC hRS hC hD hH hCS hDS hE hF hSd hI

/-- con-leche: ConLeche/MainTheorem.lean:88 main_compare_model — **AN ACCEPTED COMPARED `--olean`
RUN'S CHALLENGE HAS A MODEL**: the binary's calls on `--olean --compare -- C S` (§4c's table)
accepting, the records the challenge's check phase checks, each theorem's reference replaced by
a value (`RustDenotesFilled`), denote a stream whose environment has a model.  `hT2` as in
`no_False_oleans_compare_of`.

Composition only: `rust_stages_oleans_compare` (Theorem 2), `stagesOC_model` (Theorem 1 +
con-leche). -/
theorem model_exists_oleans_compare_of (hT2 : ReadOleansRefines)
    (V : Type w) [ConLeche.SetTheory V] {F : ConLeche.FS}
    {st1 st2 st4 st4h st5 st6 st7 st10 st11 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    {c s : kernel.name.Name} {ch sh : arena.handle.NIdx} {stR1 stR : arena.monad.AState}
    (hwfC : ConRon.Refine.NameWF c) (hwfS : ConRon.Refine.NameWF s)
    (hnC : arena.monad.intern_name emptyTier st2 c = ok (.Ok ch, stR1))
    (hnS : arena.monad.intern_name emptyTier stR1 s = ok (.Ok sh, stR))
    {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    (hsnap : SnapshotOf finst fsv F)
    {cr sr : frontend.olean.files.Roots} {rootsC rootsS : alloc.vec.Vec arena.handle.NIdx}
    (hrC : rootsC.val = [ch]) (hrS : rootsS.val = [sh])
    {rdC rdS : frontend.olean.records.OleanRead} {store3 store5 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store cr rootsC none true true
      = ok (.Ok rdC, store3))
    {preC : frontend.prepare.PreludeIx}
    (hdup : frontend.prepare.prelude_ix_dup pre = ok preC)
    {prepC : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier { stR with store := store3 } preC rdC.decls rdC
      = ok (.Ok prepC, st4))
    {holed : alloc.vec.Vec arena.env.IDeclaration}
    (hhole : frontend.compare.hole_records frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts rdC emptyTier st4 prepC.decls 0#usize (alloc.vec.Vec.new _)
      = ok (.Ok holed, st4h))
    (h3S : frontend.olean.records.read_oleans finst fsv emptyTier st4h.store sr rootsS none true false
      = ok (.Ok rdS, store5))
    {prepS : frontend.prepare.Prepared}
    (h4S : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier { st4h with store := store5 } pre rdS.decls rdS
      = ok (.Ok prepS, st5))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st5 pins maxNatSize = ok (.Ok ipins, st6))
    {ixS : arena.stream_index.IStreamIndex}
    (h6S : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st6 e prepS.decls 0#usize) = ok (.Ok ixS, st7))
    {tierS : arena.store.PersTier} {frozenS : arena.store.EStore}
    (h7S : arena.checker.freeze_tier st7.store ixS = ok (tierS, frozenS))
    (h8S : ParallelAll prepS.decls.length (oleanWorkerInit st7.pins)
      (oleanJobStep finst fsv tierS .Verified ipins prepS.decls rdS.pins rdS.values sr))
    {recsC : alloc.vec.Vec arena.env.IDeclaration}
    (hside : arena.justify.side_records emptyTier st7 holed 0#usize (alloc.vec.Vec.new _) =
      ok (.Ok recsC, st10))
    {sol : arena.justify.Solution}
    (hsol : arena.justify.solution_of ixS recsC = ok sol)
    {ixC : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st10 e recsC 0#usize) = ok (.Ok ixC, st11))
    {tierC : arena.store.PersTier} {frozenC : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st11.store ixC = ok (tierC, frozenC))
    (h8 : ParallelAll recsC.length (oleanWorkerInit st11.pins)
      (oleanJobStepSol finst fsv tierC .Verified ipins recsC rdC.pins rdC.values cr (some sol))) :
    ∃ env, RustDenotesFilled recsC st10 env ∧ Nonempty (ConLeche.Model V env) := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  have hkc : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel :=
    ConRon.Bridge.CoreSpec.of_core
  have hind : ConRon.Bridge.IndSpec :=
    ConRon.Bridge.Inductives.indSpec_of_bridge
  obtain ⟨sA, sB, sB₁, sB₂, sC, sD, sD', sC₂, sD₂, sE, sF, sH, sI, rdC', rdS', IS, IC, hA, hB,
      hRC, hRS, hC, hD, hH, hCS, hDS, hE, hF, hSd, hI, hrelH⟩ :=
    rust_stages_oleans_compare hT2 hpins rfl hest hst0 h1 h2 hwfC hwfS hnC hnS hsnap hrC hrS h3
      hdup h4 hhole h3S h4S h5 (oleanPoolAccepts_intro h6S h7S h8S) hside hsol
      (oleanPoolAcceptsSol_intro h6 h7 h8)
  obtain ⟨hwfH, dsP, val, hden, ⟨hmod⟩⟩ :=
    ConRon.Bridge.stagesOC_model V hkc hind rfl rfl (pins := ConRon.Refine.absPins pins)
      hA hB hRC hRS hC hD hH hCS hDS hE hF hSd hI
  exact ⟨_, ⟨sH, dsP, val, hrelH.of₀ hwfH, hden, rfl⟩,
    ⟨ConLeche.Model.Model.ofEnvModelM hmod⟩⟩

/-- con-leche: ConLeche/MainTheorem.lean:88 main_compare_model — `no_False_oleans_compare_of`
at the reader's Theorem 2, `read_oleans_refines`. -/
theorem no_False_oleans_compare (V : Type w) [ConLeche.SetTheory V] {F : ConLeche.FS}
    {m : ConLeche.Name} {d : ConLeche.Frontend.Olean.ModDecoded}
    {cc : ConLeche.Frontend.Olean.CEntryF ConLeche.Name ConLeche.Expr} {v : ConLeche.Expr}
    {all : List ConLeche.Name} {c : kernel.name.Name} {cr : frontend.olean.files.Roots}
    (hcl : ConLeche.Frontend.Olean.InClosure (absRoots cr) F #[ConRon.Refine.absName c] m)
    (hv : ConLeche.Frontend.Olean.ViewOf (absRoots cr) F m d)
    (hmem : cc ∈ d.constants) (hk : cc.kind = .thm v all)
    (hty : cc.type = .const ConLeche.falseName [])
    {st1 st2 st4 st4h st5 st6 st7 st10 st11 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    {s : kernel.name.Name} {ch sh : arena.handle.NIdx} {stR1 stR : arena.monad.AState}
    (hwfC : ConRon.Refine.NameWF c) (hwfS : ConRon.Refine.NameWF s)
    (hnC : arena.monad.intern_name emptyTier st2 c = ok (.Ok ch, stR1))
    (hnS : arena.monad.intern_name emptyTier stR1 s = ok (.Ok sh, stR))
    {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    (hsnap : SnapshotOf finst fsv F)
    {sr : frontend.olean.files.Roots} {rootsC rootsS : alloc.vec.Vec arena.handle.NIdx}
    (hrC : rootsC.val = [ch]) (hrS : rootsS.val = [sh])
    {rdC rdS : frontend.olean.records.OleanRead} {store3 store5 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store cr rootsC none true true
      = ok (.Ok rdC, store3))
    {preC : frontend.prepare.PreludeIx}
    (hdup : frontend.prepare.prelude_ix_dup pre = ok preC)
    {prepC : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier { stR with store := store3 } preC rdC.decls rdC
      = ok (.Ok prepC, st4))
    {holed : alloc.vec.Vec arena.env.IDeclaration}
    (hhole : frontend.compare.hole_records frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts rdC emptyTier st4 prepC.decls 0#usize (alloc.vec.Vec.new _)
      = ok (.Ok holed, st4h))
    (h3S : frontend.olean.records.read_oleans finst fsv emptyTier st4h.store sr rootsS none true false
      = ok (.Ok rdS, store5))
    {prepS : frontend.prepare.Prepared}
    (h4S : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier { st4h with store := store5 } pre rdS.decls rdS
      = ok (.Ok prepS, st5))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st5 pins maxNatSize = ok (.Ok ipins, st6))
    {ixS : arena.stream_index.IStreamIndex}
    (h6S : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st6 e prepS.decls 0#usize) = ok (.Ok ixS, st7))
    {tierS : arena.store.PersTier} {frozenS : arena.store.EStore}
    (h7S : arena.checker.freeze_tier st7.store ixS = ok (tierS, frozenS))
    (h8S : ParallelAll prepS.decls.length (oleanWorkerInit st7.pins)
      (oleanJobStep finst fsv tierS .Verified ipins prepS.decls rdS.pins rdS.values sr))
    {recsC : alloc.vec.Vec arena.env.IDeclaration}
    (hside : arena.justify.side_records emptyTier st7 holed 0#usize (alloc.vec.Vec.new _) =
      ok (.Ok recsC, st10))
    {sol : arena.justify.Solution}
    (hsol : arena.justify.solution_of ixS recsC = ok sol)
    {ixC : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st10 e recsC 0#usize) = ok (.Ok ixC, st11))
    {tierC : arena.store.PersTier} {frozenC : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st11.store ixC = ok (tierC, frozenC))
    (h8 : ParallelAll recsC.length (oleanWorkerInit st11.pins)
      (oleanJobStepSol finst fsv tierC .Verified ipins recsC rdC.pins rdC.values cr (some sol))) :
    False :=
  no_False_oleans_compare_of read_oleans_refines V hcl hv hmem hk hty h1 h2 hwfC hwfS hnC hnS
    hsnap hrC hrS h3 hdup h4 hhole h3S h4S hpins h5 h6S h7S h8S hside hsol h6 h7 h8

/-- con-leche: ConLeche/MainTheorem.lean:88 main_compare_model — `model_exists_oleans_compare_of`
at the reader's Theorem 2, `read_oleans_refines`. -/
theorem model_exists_oleans_compare (V : Type w) [ConLeche.SetTheory V] {F : ConLeche.FS}
    {st1 st2 st4 st4h st5 st6 st7 st10 st11 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    {c s : kernel.name.Name} {ch sh : arena.handle.NIdx} {stR1 stR : arena.monad.AState}
    (hwfC : ConRon.Refine.NameWF c) (hwfS : ConRon.Refine.NameWF s)
    (hnC : arena.monad.intern_name emptyTier st2 c = ok (.Ok ch, stR1))
    (hnS : arena.monad.intern_name emptyTier stR1 s = ok (.Ok sh, stR))
    {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    (hsnap : SnapshotOf finst fsv F)
    {cr sr : frontend.olean.files.Roots} {rootsC rootsS : alloc.vec.Vec arena.handle.NIdx}
    (hrC : rootsC.val = [ch]) (hrS : rootsS.val = [sh])
    {rdC rdS : frontend.olean.records.OleanRead} {store3 store5 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store cr rootsC none true true
      = ok (.Ok rdC, store3))
    {preC : frontend.prepare.PreludeIx}
    (hdup : frontend.prepare.prelude_ix_dup pre = ok preC)
    {prepC : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier { stR with store := store3 } preC rdC.decls rdC
      = ok (.Ok prepC, st4))
    {holed : alloc.vec.Vec arena.env.IDeclaration}
    (hhole : frontend.compare.hole_records frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts rdC emptyTier st4 prepC.decls 0#usize (alloc.vec.Vec.new _)
      = ok (.Ok holed, st4h))
    (h3S : frontend.olean.records.read_oleans finst fsv emptyTier st4h.store sr rootsS none true false
      = ok (.Ok rdS, store5))
    {prepS : frontend.prepare.Prepared}
    (h4S : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier { st4h with store := store5 } pre rdS.decls rdS
      = ok (.Ok prepS, st5))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st5 pins maxNatSize = ok (.Ok ipins, st6))
    {ixS : arena.stream_index.IStreamIndex}
    (h6S : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st6 e prepS.decls 0#usize) = ok (.Ok ixS, st7))
    {tierS : arena.store.PersTier} {frozenS : arena.store.EStore}
    (h7S : arena.checker.freeze_tier st7.store ixS = ok (tierS, frozenS))
    (h8S : ParallelAll prepS.decls.length (oleanWorkerInit st7.pins)
      (oleanJobStep finst fsv tierS .Verified ipins prepS.decls rdS.pins rdS.values sr))
    {recsC : alloc.vec.Vec arena.env.IDeclaration}
    (hside : arena.justify.side_records emptyTier st7 holed 0#usize (alloc.vec.Vec.new _) =
      ok (.Ok recsC, st10))
    {sol : arena.justify.Solution}
    (hsol : arena.justify.solution_of ixS recsC = ok sol)
    {ixC : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st10 e recsC 0#usize) = ok (.Ok ixC, st11))
    {tierC : arena.store.PersTier} {frozenC : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st11.store ixC = ok (tierC, frozenC))
    (h8 : ParallelAll recsC.length (oleanWorkerInit st11.pins)
      (oleanJobStepSol finst fsv tierC .Verified ipins recsC rdC.pins rdC.values cr (some sol))) :
    ∃ env, RustDenotesFilled recsC st10 env ∧ Nonempty (ConLeche.Model V env) :=
  model_exists_oleans_compare_of read_oleans_refines V h1 h2 hwfC hwfS hnC hnS hsnap hrC hrS h3
    hdup h4 hhole h3S h4S hpins h5 h6S h7S h8S hside hsol h6 h7 h8

end HeadlineOleansCompare

/-! ## 6. The modular runs: `--check-graph`, `--olean --module`, `--olean --modular`

Upstream's modular theorem (`ConLeche/MainTheorem.lean` `main_modular`, `main_modular_one`) is over
the graph check and one worker per module of the headers' closure; its proof assembles the
worker's accepts into an accepted run over the closure (`Driver.Compose.closure_sees_isModel`).
The driver (`driver/graph.rs`, `driver/worker.rs`, `driver/modular.rs`,
`driver/compare_module.rs`) runs each call below from fresh start values; the premises are its
calls, marked `ConRon.MainTheorem.Stages:` there (`MainTheorem/Modular.lean` and
`MainTheorem/CompareModular.lean` are the walks). -/

section RustModular

open ConRon.Refine2 ConRon.Refine2.Frontend ConRon.Refine2.Frontend.Olean

/-- **The graph check at the Rust** (`graph::check_graph`, and `--modular`'s first step): the
reserved pins, the reader's pins, the roots interned and `graph::graph_of` with no import added,
on a snapshot `F`, give upstream's `checkGraphG_ok` facts: the closure `CC` of upstream's nodes,
each module's imports its header's, the roots in it, a one-to-one rank decreasing along every
import, every module in the headers' closure of the roots.  Theorem 2 (`graph_of_refines`) then
Theorem 1 (`graphStage_run`). -/
theorem rust_graph {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    {F : ConLeche.FS} (hsnap : SnapshotOf finst fsv F)
    {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {names : List kernel.name.Name}
    {st1 stR : arena.monad.AState} {store2 store3 : arena.store.EStore}
    {pk : frontend.olean.spec.OleanPins} {roots : alloc.vec.Vec arena.handle.NIdx}
    {c : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    (hpk : frontend.olean.spec.olean_pins emptyTier st1.store = ok (.Ok pk, store2))
    (hroots : InternRoots emptyTier { st1 with store := store2 } names roots.val stR)
    (hgraph : frontend.modular.graph.graph_of finst fsv pk emptyTier stR.store
      ⟨dirs, alloc.vec.Vec.new _⟩ roots none = ok (.Ok c, store3)) :
    ∃ (CC : List ConLeche.Driver.Graph.Node) (rk : ConLeche.Name → Nat),
      (∀ e ∈ CC, ConLeche.ModelIO.CanGive
        (ConLeche.Frontend.Olean.moduleImports (absSearchPath dirs) e.1) F (.ok e.2)) ∧
      (∀ r ∈ names.map ConRon.Refine.absName, r ∈ CC.map (·.1)) ∧
      (∀ e ∈ CC, ∀ i ∈ e.2, i.module ∈ CC.map (·.1) ∧ rk i.module < rk e.1) ∧
      (CC.map fun e => rk e.1).Nodup ∧
      (∀ e ∈ CC, ConLeche.Frontend.Olean.HdrClosure (absSearchPath dirs) F
        (names.map ConRon.Refine.absName) e.1) := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  obtain ⟨hrel0, hinv0, -⟩ := init_rel (pers := emptyTier) rfl hest hst0
  obtain ⟨sA, hA, hrelA, hinvA⟩ := (intern_reserved_pins_refines hrel0 hinv0 h1).dest
  obtain ⟨pk', sB, hB, rfl, hrelB, hinvB⟩ := olean_pins_refines hrelA hinvA _ _ hpk
  obtain ⟨sC, hC, hrelC, hinvC⟩ := internRoots_refines names roots.val hroots hrelB hinvB
  obtain ⟨C, sD, hD, rfl, -, -⟩ :=
    ConRon.Refine2.Modular.graph_of_refines (fsRel_of_snapshot hsnap) hrelC hinvC _ _ hgraph
  exact ConRon.Bridge.Modular.graphStage_run rfl hA hB hC hD

/-- The binary's empty index is a well-formed base over nothing. -/
theorem emptyTier_base : ConRon.Refine2.BaseRel emptyTier.env {} ∧ ConRon.Refine2.BaseOK emptyTier :=
  ⟨ixEmpty_rel.baseRel {} rfl rfl rfl, StreamIndexRel.baseOK (pers := emptyTier) ixEmpty_rel⟩

/-- **A worker run at the Rust** (`worker::check_module`, one module, no import added): from the
binary's start values, the reserved pins, the module's name interned, the pins interned, phases
1–4 (`worker::worker_read`), the jobs' records, the index over them, the freeze, the inferred
flags on a fresh worker, and the pool over the own jobs from `start`, on a snapshot `F`, give
upstream's accepted worker at the module.  Theorem 2 per call, then `workerStage_run`. -/
theorem rust_worker_gen (hR : ConRon.Bridge.Modular.ReachRunHyp)
    {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    {F : ConLeche.FS} (hsnap : SnapshotOf finst fsv F)
    {sp : frontend.olean.files.Roots} (hsp : (absRoots sp).bare = absRoots sp)
    {mName : kernel.name.Name} {rest : List kernel.name.Name}
    {st1 st2 st3 st4 st5 : arena.monad.AState} {m : arena.handle.NIdx} {hs : List arena.handle.NIdx}
    {x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)}
    {xC : Array ConLeche.Frontend.Olean.ImportRec}
    (hx : ∀ st : ConRon.Arena.EStore, ConRon.Bridge.Frontend.ListRel
        (ConRon.Bridge.Frontend.Olean.NR st) (absNIdx m :: hs.map absNIdx)
        (ConRon.Refine.absName mName :: rest.map ConRon.Refine.absName) →
      ConRon.Bridge.Frontend.Olean.ImpsD st (absImports x) xC)
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    (hroot : InternRoots emptyTier st1 (mName :: rest) (m :: hs) st2)
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st2 pins maxNatSize = ok (.Ok ipins, st3))
    {w : frontend.modular.worker.WorkerRead}
    (hwork : frontend.modular.worker.worker_read finst fsv emptyTier st3 sp ipins m x
      = ok (.Ok w, st4))
    {ds : alloc.vec.Vec arena.env.IDeclaration}
    (hds : frontend.modular.worker.worker_decls w = ok ds)
    {ix : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st4 e ds 0#usize) = ok (.Ok ix, st5))
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st5.store ix = ok (tier, frozen))
    {ws ws' : arena.monad.AState}
    (hws : arena.checker.worker_state st5.pins = ok ws)
    (hinfer : frontend.modular.reach.infer_flags tier ws w.reach.ctx w.reach.pending = ok (.Ok (), ws'))
    (h8 : ParallelAll (ds.length - w.start.val) (oleanWorkerInit st5.pins)
      (fun c k => oleanJobStepSol finst fsv tier .Verified ipins ds w.pins w.values
        sp none c (w.start.val + k))) :
    ConLeche.Driver.WorkerAccepted (ConRon.Refine.absPins pins) (absRoots sp) F
      (ConRon.Refine.absName mName) 1 xC := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  obtain ⟨hrel0, hinv0, -⟩ := init_rel (pers := emptyTier) rfl hest hst0
  obtain ⟨sA, hA, hrelA, hinvA⟩ := (intern_reserved_pins_refines hrel0 hinv0 h1).dest
  obtain ⟨sB, hB, hrelB, hinvB⟩ := internRoots_refines (mName :: rest) (m :: hs) hroot hrelA hinvA
  obtain ⟨sC, hC, hrelC, hinvC⟩ :=
    (intern_all_pins_refines hrelB hinvB (ConRon.Refine.PinsWF.decode_wf_refine2 hpins) h5).dest
  have hfs := fsRel_of_snapshot hsnap
  obtain ⟨w', sD, hD, hwr, hrelD, hinvD⟩ :=
    ConRon.Refine2.Modular.worker_read_refines hfs emptyTier_base.1 emptyTier_base.2 hrelC hinvC
      _ ipins m x w st4 hwork
  have hdecls := ConRon.Refine2.Modular.worker_decls_eq hwr.reach.ctx.symm hwr.own.symm hds
  -- the index, the freeze, the fresh worker, the inferred flags
  rw [stream_index_empty_eq, bind_ok] at h6
  obtain ⟨I, sE, hE, hrelE, hinvE, hIrel, hIfr⟩ := build_index_empty_refines hrelD hinvD h6
  obtain ⟨htier, -⟩ := freeze_tier_ok h7
  subst htier
  obtain ⟨hidle, hinvW⟩ := worker_state_rel ix hrelE hinvE rfl hws
  obtain ⟨w₁, hF, -, -⟩ := ConRon.Refine2.Modular.infer_flags_la hidle hinvW rfl ⟨hIrel, hIfr⟩
    (hwr.reach.pending.imp fun _ _ h => h) hinfer
  -- the pool
  obtain ⟨I', sE', hP, -, -, -⟩ := olean_pool_accepts_from_sol_refines (values' := w'.values)
    (sol := none) (J := none) trivial hfs hwr.values hrelD hinvD rfl
    (oleanPoolAcceptsFromSol_intro (by rw [stream_index_empty_eq, bind_ok]; exact h6) h7 h8)
  -- one index: the build is a function
  obtain ⟨parts, hbuild, hrest⟩ := hP
  have hEq := hbuild.symm.trans hE
  simp only [Except.ok.injEq, Prod.mk.injEq] at hEq
  obtain ⟨hI1, hI2⟩ := hEq
  rw [hI1, hI2] at hbuild hrest
  have hdecls' : (absIDeclL ds).toArray = ConRon.Arena.Modular.workerDecls w' := hdecls
  rw [hdecls'] at hbuild hrest
  rw [← hwr.pins, ← hwr.start] at hrest
  have hP' : ConRon.Arena.PooledOleanAcceptsFromJ (ConRon.Bridge.Frontend.Olean.modelFs F) w'.pins
      (absRoots sp) w'.values .verified (absINatOpPinSetL ipins) none
      w'.start (ConRon.Arena.Modular.workerDecls w') sD I sE :=
    ⟨parts, hbuild, hrest⟩
  have hctxE : (absIDeclL w.reach.ctx).toArray = w'.reach.ctx := hwr.reach.ctx.symm
  rw [hctxE] at hF
  exact ConRon.Bridge.Modular.workerStage_run ConRon.Bridge.CoreSpec.of_core
    ConRon.Bridge.Inductives.indSpec_of_bridge ConRon.Bridge.Modular.Home.homeHyp_holds hR hsp
    (names := rest.map ConRon.Refine.absName) (hs := hs.map absNIdx) hA
    (by simpa only [List.map_cons] using hB) (fun h => hx _ h) hC hD hP' hF

/-- `rust_worker_gen` with no import added, at a search path: a module's worker under
`--olean --module` / `--olean --modular`. -/
theorem rust_worker_of (hR : ConRon.Bridge.Modular.ReachRunHyp)
    {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    {F : ConLeche.FS} (hsnap : SnapshotOf finst fsv F)
    {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {mName : kernel.name.Name}
    {st1 st2 st3 st4 st5 : arena.monad.AState} {m : arena.handle.NIdx}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    (hroot : InternRoots emptyTier st1 [mName] [m] st2)
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins emptyTier st2 pins maxNatSize = ok (.Ok ipins, st3))
    {w : frontend.modular.worker.WorkerRead}
    (hwork : frontend.modular.worker.worker_read finst fsv emptyTier st3 ⟨dirs, alloc.vec.Vec.new _⟩
      ipins m (alloc.vec.Vec.new _) = ok (.Ok w, st4))
    {ds : alloc.vec.Vec arena.env.IDeclaration}
    (hds : frontend.modular.worker.worker_decls w = ok ds)
    {ix : arena.stream_index.IStreamIndex}
    (h6 : (do
        let e ← arena.stream_index.stream_index_empty
        arena.stream_index.build_index emptyTier st4 e ds 0#usize) = ok (.Ok ix, st5))
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st5.store ix = ok (tier, frozen))
    {ws ws' : arena.monad.AState}
    (hws : arena.checker.worker_state st5.pins = ok ws)
    (hinfer : frontend.modular.reach.infer_flags tier ws w.reach.ctx w.reach.pending = ok (.Ok (), ws'))
    (h8 : ParallelAll (ds.length - w.start.val) (oleanWorkerInit st5.pins)
      (fun c k => oleanJobStepSol finst fsv tier .Verified ipins ds w.pins w.values
        ⟨dirs, alloc.vec.Vec.new _⟩ none c (w.start.val + k))) :
    ConLeche.Driver.WorkerAccepted (ConRon.Refine.absPins pins) (absSearchPath dirs) F
      (ConRon.Refine.absName mName) 1 #[] :=
  rust_worker_gen hR hsnap (sp := ⟨dirs, alloc.vec.Vec.new _⟩) rfl (rest := []) (hs := [])
    (x := alloc.vec.Vec.new _) (xC := #[]) (fun _ _ => rfl) h1 hroot hpins h5 hwork hds h6 h7 hws hinfer h8

/-- con-leche: ConLeche/MainTheorem.lean:109 main_modular — **AN ACCEPTED MODULAR CHECK HAS A
FAMILY OF MODELS**: on a snapshot `F` of the files (`hsnap`), where the graph check of the root
`r` succeeds (`h1g`, `hpk`, `hroots`, `hgraph`: `graph::check_graph`) and, for every module of the
headers' closure, the worker's calls succeed, each from the binary's start values (`hwork`:
`worker::check_module`, one premise per call; `--olean --module` per module, or all of them in one
process under `--olean --modular`), every module of the closure of `r`, by the specification
(`InClosure`), has a model of its constants (`moduleConstants`), and the models agree on what the
modules see of each other (`Sees`).  The pins are one decoded list (`hpins`).  `hR` is Theorem 1 at
the reach.

Composition: `rust_graph`, `rust_worker_of` per module, upstream's `closure_sees_isModel`. -/
theorem model_modular_of (hR : ConRon.Bridge.Modular.ReachRunHyp)
    (V : Type w) [ConLeche.SetTheory V] {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs}
    {fsv : Fs} {F : ConLeche.FS} (hsnap : SnapshotOf finst fsv F)
    {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {rName : kernel.name.Name}
    {g1 gR : arena.monad.AState} {gstore2 gstore3 : arena.store.EStore}
    {pk : frontend.olean.spec.OleanPins} {groots : alloc.vec.Vec arena.handle.NIdx}
    {c : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
    (h1g : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), g1))
    (hpk : frontend.olean.spec.olean_pins emptyTier g1.store = ok (.Ok pk, gstore2))
    (hroots : InternRoots emptyTier { g1 with store := gstore2 } [rName] groots.val gR)
    (hgraph : frontend.modular.graph.graph_of finst fsv pk emptyTier gR.store
      ⟨dirs, alloc.vec.Vec.new _⟩ groots none = ok (.Ok c, gstore3))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    (hwork : ∀ m', ConLeche.Frontend.Olean.HdrClosure (absSearchPath dirs) F
        [ConRon.Refine.absName rName] m' →
      ∃ (mName : kernel.name.Name), ConRon.Refine.absName mName = m' ∧
      ∃ (st1 st2 st3 st4 st5 : arena.monad.AState) (m : arena.handle.NIdx)
        (ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet) (maxNatSize : ron.nat.Nat)
        (w : frontend.modular.worker.WorkerRead) (ds : alloc.vec.Vec arena.env.IDeclaration)
        (ix : arena.stream_index.IStreamIndex) (tier : arena.store.PersTier)
        (frozen : arena.store.EStore) (ws ws' : arena.monad.AState),
        arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1) ∧
        InternRoots emptyTier st1 [mName] [m] st2 ∧
        arena.checker.intern_all_pins emptyTier st2 pins maxNatSize = ok (.Ok ipins, st3) ∧
        frontend.modular.worker.worker_read finst fsv emptyTier st3 ⟨dirs, alloc.vec.Vec.new _⟩
          ipins m (alloc.vec.Vec.new _) = ok (.Ok w, st4) ∧
        frontend.modular.worker.worker_decls w = ok ds ∧
        (do
          let e ← arena.stream_index.stream_index_empty
          arena.stream_index.build_index emptyTier st4 e ds 0#usize) = ok (.Ok ix, st5) ∧
        arena.checker.freeze_tier st5.store ix = ok (tier, frozen) ∧
        arena.checker.worker_state st5.pins = ok ws ∧
        frontend.modular.reach.infer_flags tier ws w.reach.ctx w.reach.pending = ok (.Ok (), ws') ∧
        ParallelAll (ds.length - w.start.val) (oleanWorkerInit st5.pins)
          (fun c k => oleanJobStepSol finst fsv tier .Verified ipins ds w.pins w.values
            ⟨dirs, alloc.vec.Vec.new _⟩ none c (w.start.val + k))) :
    ∃ model : ConLeche.Name → (ConLeche.Name → List Nat → V),
      (∀ m, ConLeche.Frontend.Olean.InClosure (absSearchPath dirs) F #[ConRon.Refine.absName rName] m →
        ConLeche.IsModel V (model m) (ConLeche.Frontend.Olean.moduleConstants (absSearchPath dirs) F m)) ∧
      (∀ m n m', ConLeche.Frontend.Olean.InClosure (absSearchPath dirs) F #[ConRon.Refine.absName rName] m →
        ConLeche.Frontend.Olean.Sees (absSearchPath dirs) F m n m' → model m n = model m' n) := by
  obtain ⟨CC, rk, good, hr, edges, inj, hhdr⟩ := rust_graph hsnap h1g hpk hroots hgraph
  refine ConLeche.Driver.Compose.closure_sees_isModel (pins := ConRon.Refine.absPins pins) V CC rk good edges inj (fun M hM => ?_)
    (hr _ List.mem_cons_self)
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
  obtain ⟨mName, hmn, st1, st2, st3, st4, st5, m, ipins, maxNatSize, w, ds, ix, tier, frozen, ws, ws',
    w1, w2, w3, w4, w5, w6, w7, w8, w9, w10⟩ := hwork e.1 (hhdr e he)
  rw [← hmn]
  exact ⟨1, rust_worker_of hR hsnap w1 w2 hpins w3 w4 w5 w6 w7 w8 w9 w10⟩

/-- **The graph check of a compared run at the Rust** (`compare_module::check_graph_cmp`): the reserved
pins, the reader's pins, the challenge and the solution interned, `graph::graph_of` over the
solution's lookup from the challenge, the solution added to its header; on a snapshot `F`,
upstream's facts at the added imports (`cmpExtra`). -/
theorem rust_graph_cmp {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs} {fsv : Fs}
    {F : ConLeche.FS} (hsnap : SnapshotOf finst fsv F)
    {spR : frontend.olean.files.Roots} (hsp : (absRoots spR).bare = absRoots spR)
    {cName sName : kernel.name.Name}
    {st1 stR : arena.monad.AState} {store2 store3 : arena.store.EStore}
    {pk : frontend.olean.spec.OleanPins} {c s : arena.handle.NIdx}
    {roots : alloc.vec.Vec arena.handle.NIdx} (hrv : roots.val = [c])
    {cg : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    (hpk : frontend.olean.spec.olean_pins emptyTier st1.store = ok (.Ok pk, store2))
    (hroots : InternRoots emptyTier { st1 with store := store2 } [cName, sName] [c, s] stR)
    (hgraph : frontend.modular.graph.graph_of finst fsv pk emptyTier stR.store spR roots (some (c, s))
      = ok (.Ok cg, store3)) :
    ∃ (CC : List ConLeche.Driver.Graph.Node) (rk : ConLeche.Name → Nat),
      (∀ e ∈ CC, ConLeche.Driver.Graph.NodeOk (absRoots spR) F
        (ConLeche.Driver.Graph.cmpExtra (ConRon.Refine.absName cName) (ConRon.Refine.absName sName)) e) ∧
      ConRon.Refine.absName cName ∈ CC.map (·.1) ∧
      (∀ e ∈ CC, ∀ i ∈ e.2, i.module ∈ CC.map (·.1) ∧ rk i.module < rk e.1) ∧
      (CC.map fun e => rk e.1).Nodup ∧
      (∀ e ∈ CC, ConLeche.Frontend.Olean.HdrClosure (absRoots spR) F
        [ConRon.Refine.absName cName, ConRon.Refine.absName sName] e.1) := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  obtain ⟨hrel0, hinv0, -⟩ := init_rel (pers := emptyTier) rfl hest hst0
  obtain ⟨sA, hA, hrelA, hinvA⟩ := (intern_reserved_pins_refines hrel0 hinv0 h1).dest
  obtain ⟨pk', sB, hB, rfl, hrelB, hinvB⟩ := olean_pins_refines hrelA hinvA _ _ hpk
  obtain ⟨sC, hC, hrelC, hinvC⟩ := internRoots_refines [cName, sName] [c, s] hroots hrelB hinvB
  obtain ⟨C, sD, hD, rfl, -, -⟩ :=
    ConRon.Refine2.Modular.graph_of_refines (fsRel_of_snapshot hsnap) hrelC hinvC _ _ hgraph
  rw [hrv] at hD
  exact ConRon.Bridge.Modular.graphStageCmp_run hsp hA hB hC hD

/-- The lookup of a compared run is a lookup with no root resolved. -/
theorem solRoots_bare (r : ConLeche.Driver.CmpReq) : r.solRoots.bare = r.solRoots := by
  unfold ConLeche.Driver.CmpReq.solRoots
  split <;> rfl

/-- The compared challenge's added import, read back. -/
theorem solImport_impsD {st : ConRon.Arena.EStore} {sH : arena.handle.NIdx} {S : ConLeche.Name}
    (hs : ConRon.Arena.denoteN st.ns (absNIdx sH) = some S)
    {xi : frontend.olean.spec.ImportF arena.handle.NIdx}
    (hxi : frontend.modular.graph.solution_import sH = ok xi)
    {x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)} (hx : x.val = [xi]) :
    ConRon.Bridge.Frontend.Olean.ImpsD st (absImports x) #[ConLeche.Driver.Graph.solutionImport S] := by
  have e := ConRon.Refine2.Modular.solution_import_eq hxi
  simp only [ConRon.Bridge.Frontend.Olean.ImpsD, hx, List.map_cons, List.map_nil,
    List.mapM_cons, List.mapM_nil]
  rw [show absImportF absNIdx xi = ConRon.Arena.Modular.solutionImport (absNIdx sH) from e]
  simp [ConRon.Bridge.Frontend.Olean.denoteImport, ConRon.Arena.Modular.solutionImport,
    ConLeche.Driver.Graph.solutionImport, ConLeche.Frontend.Olean.ImportF.mapM, hs]

/-- **Every module of a compared run's graph is an accepted worker** at the imports the run adds
(`cmpExtra`): the compare worker at the challenge (`hcmp`), a plain worker at every other module
(`hwork`), each from the binary's start values over the solution's lookup. -/
theorem acc_compare (hR : ConRon.Bridge.Modular.ReachRunHyp) {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs}
    {fsv : Fs} {F : ConLeche.FS} (hsnap : SnapshotOf finst fsv F)
    {tdirs ddirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {cName sName : kernel.name.Name}
    {spR : frontend.olean.files.Roots}
    (hsr : absRoots spR = (⟨ConRon.Refine.absName cName, ConRon.Refine.absName sName,
      absSearchPath tdirs, absSearchPath ddirs, none⟩ : ConLeche.Driver.CmpReq).solRoots)
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    (hwork : ∀ m', ConLeche.Frontend.Olean.HdrClosure (absRoots spR) F
        [ConRon.Refine.absName cName, ConRon.Refine.absName sName] m' →
      m' ≠ ConRon.Refine.absName cName →
      ∃ (mName : kernel.name.Name), ConRon.Refine.absName mName = m' ∧
      ∃ (m : arena.handle.NIdx) (st1 st2 st3 st4 st5 : arena.monad.AState) (ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
        (maxNatSize : ron.nat.Nat) (w : frontend.modular.worker.WorkerRead)
        (ds : alloc.vec.Vec arena.env.IDeclaration) (ix : arena.stream_index.IStreamIndex)
        (tier : arena.store.PersTier) (frozen : arena.store.EStore) (ws ws' : arena.monad.AState),
        arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1) ∧
        InternRoots emptyTier st1 [mName] [m] st2 ∧
        arena.checker.intern_all_pins emptyTier st2 pins maxNatSize = ok (.Ok ipins, st3) ∧
        frontend.modular.worker.worker_read finst fsv emptyTier st3 spR ipins m (alloc.vec.Vec.new _) = ok (.Ok w, st4) ∧
        frontend.modular.worker.worker_decls w = ok ds ∧
        (do
          let e ← arena.stream_index.stream_index_empty
          arena.stream_index.build_index emptyTier st4 e ds 0#usize) = ok (.Ok ix, st5) ∧
        arena.checker.freeze_tier st5.store ix = ok (tier, frozen) ∧
        arena.checker.worker_state st5.pins = ok ws ∧
        frontend.modular.reach.infer_flags tier ws w.reach.ctx w.reach.pending = ok (.Ok (), ws') ∧
        ParallelAll (ds.length - w.start.val) (oleanWorkerInit st5.pins)
          (fun c k => oleanJobStepSol finst fsv tier .Verified ipins ds w.pins w.values
            spR none c (w.start.val + k)))
    (hcmp : ∃ (c sH : arena.handle.NIdx) (xi : frontend.olean.spec.ImportF arena.handle.NIdx)
        (x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)) (st1 st2 st3 st4 st5 : arena.monad.AState) (ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
        (maxNatSize : ron.nat.Nat) (w : frontend.modular.worker.WorkerRead)
        (ds : alloc.vec.Vec arena.env.IDeclaration) (ix : arena.stream_index.IStreamIndex)
        (tier : arena.store.PersTier) (frozen : arena.store.EStore) (ws ws' : arena.monad.AState),
        arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1) ∧
        InternRoots emptyTier st1 [cName, sName] [c, sH] st2 ∧
        frontend.modular.graph.solution_import sH = ok xi ∧ x.val = [xi] ∧
        arena.checker.intern_all_pins emptyTier st2 pins maxNatSize = ok (.Ok ipins, st3) ∧
        frontend.modular.worker.worker_read finst fsv emptyTier st3 spR ipins c x = ok (.Ok w, st4) ∧
        frontend.modular.worker.worker_decls w = ok ds ∧
        (do
          let e ← arena.stream_index.stream_index_empty
          arena.stream_index.build_index emptyTier st4 e ds 0#usize) = ok (.Ok ix, st5) ∧
        arena.checker.freeze_tier st5.store ix = ok (tier, frozen) ∧
        arena.checker.worker_state st5.pins = ok ws ∧
        frontend.modular.reach.infer_flags tier ws w.reach.ctx w.reach.pending = ok (.Ok (), ws') ∧
        ParallelAll (ds.length - w.start.val) (oleanWorkerInit st5.pins)
          (fun c k => oleanJobStepSol finst fsv tier .Verified ipins ds w.pins w.values
            spR none c (w.start.val + k)))
    {Cg : List ConLeche.Driver.Graph.Node}
    (hhdr : ∀ e ∈ Cg, ConLeche.Frontend.Olean.HdrClosure (absRoots spR) F
        [ConRon.Refine.absName cName, ConRon.Refine.absName sName] e.1) :
    ∀ M ∈ Cg.map (·.1), ∃ jobs, ConLeche.Driver.WorkerAccepted (ConRon.Refine.absPins pins)
      (absRoots spR) F M jobs
      (ConLeche.Driver.Graph.cmpExtra (ConRon.Refine.absName cName) (ConRon.Refine.absName sName) M) := by
  have hsp : (absRoots spR).bare = absRoots spR := by rw [hsr]; exact solRoots_bare _
  intro M hM
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
  by_cases hC : e.1 = ConRon.Refine.absName cName
  · rw [hC]
    obtain ⟨c, sH, xi, x, st1, st2, st3, st4, st5, ipins, maxNatSize, w, ds, ix, tier, frozen, ws,
      ws', w1, w2, wsol, wx, w3, w4, w5, w6, w7, w8, w9, w10⟩ := hcmp
    refine ⟨1, ?_⟩
    have hx : ConLeche.Driver.Graph.cmpExtra (ConRon.Refine.absName cName) (ConRon.Refine.absName sName)
        (ConRon.Refine.absName cName) = #[ConLeche.Driver.Graph.solutionImport (ConRon.Refine.absName sName)] := by
      simp [ConLeche.Driver.Graph.cmpExtra]
    rw [hx]
    exact rust_worker_gen hR hsnap hsp (rest := [sName]) (hs := [sH])
      (fun st h => by
        cases h with
        | cons _ h' =>
          cases h' with
          | cons hs _ => exact solImport_impsD hs wsol wx)
      w1 w2 hpins w3 w4 w5 w6 w7 w8 w9 w10
  · obtain ⟨mName, hmn, m, st1, st2, st3, st4, st5, ipins, maxNatSize, w, ds, ix, tier, frozen, ws,
      ws', w1, w2, w3, w4, w5, w6, w7, w8, w9, w10⟩ := hwork e.1 (hhdr e he) hC
    refine ⟨1, ?_⟩
    have hx : ConLeche.Driver.Graph.cmpExtra (ConRon.Refine.absName cName) (ConRon.Refine.absName sName)
        e.1 = #[] := by
      simp [ConLeche.Driver.Graph.cmpExtra, hC]
    rw [hx, ← hmn]
    exact rust_worker_gen hR hsnap hsp (rest := []) (hs := []) (x := alloc.vec.Vec.new _)
      (fun _ _ => rfl) w1 w2 hpins w3 w4 w5 w6 w7 w8 w9 w10

/-- con-leche: ConLeche/MainTheorem.lean:143 main_modular_compare — **AN ACCEPTED MODULAR
COMPARISON'S CHALLENGE CLOSURE HAS A FAMILY OF MODELS**: on a snapshot `F` where the compared
graph check succeeds (`h1g` … `hgraph`: `compare_module::check_graph_cmp`, over the solution's lookup
`spR`, `hsr`), the worker's calls succeed at every module of the headers' closure of the challenge
`C` and the solution `S` but `C` (`hwork`), and the compare worker's at `C` (`hcmp`: `import all`
of `S` added to its header), each from the binary's start values, then on every snapshot that
agrees with `F` under the challenge's directories, every module of the closure of `C` through
them has a model of its constants, and the models agree on what the modules see of each other.
`hR` is Theorem 1 at the reach.

Composition: `rust_graph_cmp`, `acc_compare`, upstream's `compare_sees_isModel`. -/
theorem model_modular_compare_of (hR : ConRon.Bridge.Modular.ReachRunHyp)
    (V : Type w) [ConLeche.SetTheory V] {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs}
    {fsv : Fs} {F : ConLeche.FS} (hsnap : SnapshotOf finst fsv F)
    {tdirs ddirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {cName sName : kernel.name.Name}
    {spR : frontend.olean.files.Roots}
    (hsr : absRoots spR = (⟨ConRon.Refine.absName cName, ConRon.Refine.absName sName,
      absSearchPath tdirs, absSearchPath ddirs, none⟩ : ConLeche.Driver.CmpReq).solRoots)
    {g1 gR : arena.monad.AState} {gstore2 gstore3 : arena.store.EStore}
    {pk : frontend.olean.spec.OleanPins} {gc gs : arena.handle.NIdx}
    {groots : alloc.vec.Vec arena.handle.NIdx} (hgr : groots.val = [gc])
    {cg : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
    (h1g : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), g1))
    (hpk : frontend.olean.spec.olean_pins emptyTier g1.store = ok (.Ok pk, gstore2))
    (hroots : InternRoots emptyTier { g1 with store := gstore2 } [cName, sName] [gc, gs] gR)
    (hgraph : frontend.modular.graph.graph_of finst fsv pk emptyTier gR.store spR groots
      (some (gc, gs)) = ok (.Ok cg, gstore3))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    (hwork : ∀ m', ConLeche.Frontend.Olean.HdrClosure (absRoots spR) F
        [ConRon.Refine.absName cName, ConRon.Refine.absName sName] m' →
      m' ≠ ConRon.Refine.absName cName →
      ∃ (mName : kernel.name.Name), ConRon.Refine.absName mName = m' ∧
      ∃ (m : arena.handle.NIdx) (st1 st2 st3 st4 st5 : arena.monad.AState) (ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
        (maxNatSize : ron.nat.Nat) (w : frontend.modular.worker.WorkerRead)
        (ds : alloc.vec.Vec arena.env.IDeclaration) (ix : arena.stream_index.IStreamIndex)
        (tier : arena.store.PersTier) (frozen : arena.store.EStore) (ws ws' : arena.monad.AState),
        arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1) ∧
        InternRoots emptyTier st1 [mName] [m] st2 ∧
        arena.checker.intern_all_pins emptyTier st2 pins maxNatSize = ok (.Ok ipins, st3) ∧
        frontend.modular.worker.worker_read finst fsv emptyTier st3 spR ipins m (alloc.vec.Vec.new _) = ok (.Ok w, st4) ∧
        frontend.modular.worker.worker_decls w = ok ds ∧
        (do
          let e ← arena.stream_index.stream_index_empty
          arena.stream_index.build_index emptyTier st4 e ds 0#usize) = ok (.Ok ix, st5) ∧
        arena.checker.freeze_tier st5.store ix = ok (tier, frozen) ∧
        arena.checker.worker_state st5.pins = ok ws ∧
        frontend.modular.reach.infer_flags tier ws w.reach.ctx w.reach.pending = ok (.Ok (), ws') ∧
        ParallelAll (ds.length - w.start.val) (oleanWorkerInit st5.pins)
          (fun c k => oleanJobStepSol finst fsv tier .Verified ipins ds w.pins w.values
            spR none c (w.start.val + k)))
    (hcmp : ∃ (c sH : arena.handle.NIdx) (xi : frontend.olean.spec.ImportF arena.handle.NIdx)
        (x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)) (st1 st2 st3 st4 st5 : arena.monad.AState) (ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
        (maxNatSize : ron.nat.Nat) (w : frontend.modular.worker.WorkerRead)
        (ds : alloc.vec.Vec arena.env.IDeclaration) (ix : arena.stream_index.IStreamIndex)
        (tier : arena.store.PersTier) (frozen : arena.store.EStore) (ws ws' : arena.monad.AState),
        arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1) ∧
        InternRoots emptyTier st1 [cName, sName] [c, sH] st2 ∧
        frontend.modular.graph.solution_import sH = ok xi ∧ x.val = [xi] ∧
        arena.checker.intern_all_pins emptyTier st2 pins maxNatSize = ok (.Ok ipins, st3) ∧
        frontend.modular.worker.worker_read finst fsv emptyTier st3 spR ipins c x = ok (.Ok w, st4) ∧
        frontend.modular.worker.worker_decls w = ok ds ∧
        (do
          let e ← arena.stream_index.stream_index_empty
          arena.stream_index.build_index emptyTier st4 e ds 0#usize) = ok (.Ok ix, st5) ∧
        arena.checker.freeze_tier st5.store ix = ok (tier, frozen) ∧
        arena.checker.worker_state st5.pins = ok ws ∧
        frontend.modular.reach.infer_flags tier ws w.reach.ctx w.reach.pending = ok (.Ok (), ws') ∧
        ParallelAll (ds.length - w.start.val) (oleanWorkerInit st5.pins)
          (fun c k => oleanJobStepSol finst fsv tier .Verified ipins ds w.pins w.values
            spR none c (w.start.val + k))) :
    ∀ fs', ConLeche.FS.AgreeUnder (ConLeche.Driver.trustedOr (absSearchPath tdirs) (absSearchPath ddirs))
        F fs' →
      ∃ model : ConLeche.Name → (ConLeche.Name → List Nat → V),
        (∀ m, ConLeche.Frontend.Olean.InClosure
            (ConLeche.Driver.trustedOr (absSearchPath tdirs) (absSearchPath ddirs) : ConLeche.Frontend.Olean.Roots)
            fs' #[ConRon.Refine.absName cName] m →
          ConLeche.IsModel V (model m) (ConLeche.Frontend.Olean.moduleConstants
            (ConLeche.Driver.trustedOr (absSearchPath tdirs) (absSearchPath ddirs) : ConLeche.Frontend.Olean.Roots) fs' m)) ∧
        (∀ m n m', ConLeche.Frontend.Olean.InClosure
            (ConLeche.Driver.trustedOr (absSearchPath tdirs) (absSearchPath ddirs) : ConLeche.Frontend.Olean.Roots)
            fs' #[ConRon.Refine.absName cName] m →
          ConLeche.Frontend.Olean.Sees
            (ConLeche.Driver.trustedOr (absSearchPath tdirs) (absSearchPath ddirs) : ConLeche.Frontend.Olean.Roots)
            fs' m n m' → model m n = model m' n) := by
  have hsp : (absRoots spR).bare = absRoots spR := by rw [hsr]; exact solRoots_bare _
  obtain ⟨Cg, rk, good, hC, edges, inj, hhdr⟩ := rust_graph_cmp hsnap hsp hgr h1g hpk hroots hgraph
  have acc := acc_compare hR hsnap hsr hpins hwork hcmp hhdr
  rw [hsr] at good hhdr acc
  exact ConLeche.Driver.Compose.compare_sees_isModel V Cg rk good hC edges inj hhdr acc

/-- con-leche: ConLeche/MainTheorem.lean:183 main_modular_compare_no_False — **NO ACCEPTED MODULAR
COMPARISON'S CHALLENGE MODULE HOLDS A CONSTANT OF TYPE `False`**: under the premises of
`model_modular_compare_of`, a module of the challenge's closure through its own directories holds
no constant of type `False` in its private part (what it sees through its solution included).

Composition: `rust_graph_cmp`, `acc_compare`, upstream's `compare_no_False`. -/
theorem no_False_modular_compare_of (hR : ConRon.Bridge.Modular.ReachRunHyp)
    (V : Type w) [ConLeche.SetTheory V] {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs}
    {fsv : Fs} {F : ConLeche.FS} (hsnap : SnapshotOf finst fsv F)
    {tdirs ddirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {cName sName : kernel.name.Name}
    {spR : frontend.olean.files.Roots}
    (hsr : absRoots spR = (⟨ConRon.Refine.absName cName, ConRon.Refine.absName sName,
      absSearchPath tdirs, absSearchPath ddirs, none⟩ : ConLeche.Driver.CmpReq).solRoots)
    {g1 gR : arena.monad.AState} {gstore2 gstore3 : arena.store.EStore}
    {pk : frontend.olean.spec.OleanPins} {gc gs : arena.handle.NIdx}
    {groots : alloc.vec.Vec arena.handle.NIdx} (hgr : groots.val = [gc])
    {cg : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
    (h1g : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), g1))
    (hpk : frontend.olean.spec.olean_pins emptyTier g1.store = ok (.Ok pk, gstore2))
    (hroots : InternRoots emptyTier { g1 with store := gstore2 } [cName, sName] [gc, gs] gR)
    (hgraph : frontend.modular.graph.graph_of finst fsv pk emptyTier gR.store spR groots
      (some (gc, gs)) = ok (.Ok cg, gstore3))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    (hwork : ∀ m', ConLeche.Frontend.Olean.HdrClosure (absRoots spR) F
        [ConRon.Refine.absName cName, ConRon.Refine.absName sName] m' →
      m' ≠ ConRon.Refine.absName cName →
      ∃ (mName : kernel.name.Name), ConRon.Refine.absName mName = m' ∧
      ∃ (m : arena.handle.NIdx) (st1 st2 st3 st4 st5 : arena.monad.AState) (ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
        (maxNatSize : ron.nat.Nat) (w : frontend.modular.worker.WorkerRead)
        (ds : alloc.vec.Vec arena.env.IDeclaration) (ix : arena.stream_index.IStreamIndex)
        (tier : arena.store.PersTier) (frozen : arena.store.EStore) (ws ws' : arena.monad.AState),
        arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1) ∧
        InternRoots emptyTier st1 [mName] [m] st2 ∧
        arena.checker.intern_all_pins emptyTier st2 pins maxNatSize = ok (.Ok ipins, st3) ∧
        frontend.modular.worker.worker_read finst fsv emptyTier st3 spR ipins m (alloc.vec.Vec.new _) = ok (.Ok w, st4) ∧
        frontend.modular.worker.worker_decls w = ok ds ∧
        (do
          let e ← arena.stream_index.stream_index_empty
          arena.stream_index.build_index emptyTier st4 e ds 0#usize) = ok (.Ok ix, st5) ∧
        arena.checker.freeze_tier st5.store ix = ok (tier, frozen) ∧
        arena.checker.worker_state st5.pins = ok ws ∧
        frontend.modular.reach.infer_flags tier ws w.reach.ctx w.reach.pending = ok (.Ok (), ws') ∧
        ParallelAll (ds.length - w.start.val) (oleanWorkerInit st5.pins)
          (fun c k => oleanJobStepSol finst fsv tier .Verified ipins ds w.pins w.values
            spR none c (w.start.val + k)))
    (hcmp : ∃ (c sH : arena.handle.NIdx) (xi : frontend.olean.spec.ImportF arena.handle.NIdx)
        (x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)) (st1 st2 st3 st4 st5 : arena.monad.AState) (ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
        (maxNatSize : ron.nat.Nat) (w : frontend.modular.worker.WorkerRead)
        (ds : alloc.vec.Vec arena.env.IDeclaration) (ix : arena.stream_index.IStreamIndex)
        (tier : arena.store.PersTier) (frozen : arena.store.EStore) (ws ws' : arena.monad.AState),
        arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1) ∧
        InternRoots emptyTier st1 [cName, sName] [c, sH] st2 ∧
        frontend.modular.graph.solution_import sH = ok xi ∧ x.val = [xi] ∧
        arena.checker.intern_all_pins emptyTier st2 pins maxNatSize = ok (.Ok ipins, st3) ∧
        frontend.modular.worker.worker_read finst fsv emptyTier st3 spR ipins c x = ok (.Ok w, st4) ∧
        frontend.modular.worker.worker_decls w = ok ds ∧
        (do
          let e ← arena.stream_index.stream_index_empty
          arena.stream_index.build_index emptyTier st4 e ds 0#usize) = ok (.Ok ix, st5) ∧
        arena.checker.freeze_tier st5.store ix = ok (tier, frozen) ∧
        arena.checker.worker_state st5.pins = ok ws ∧
        frontend.modular.reach.infer_flags tier ws w.reach.ctx w.reach.pending = ok (.Ok (), ws') ∧
        ParallelAll (ds.length - w.start.val) (oleanWorkerInit st5.pins)
          (fun c k => oleanJobStepSol finst fsv tier .Verified ipins ds w.pins w.values
            spR none c (w.start.val + k)))
    {m : ConLeche.Name} {ci : ConLeche.ConstantInfo}
    (hcl : ConLeche.Frontend.Olean.InClosure
      (ConLeche.Driver.trustedOr (absSearchPath tdirs) (absSearchPath ddirs) : ConLeche.Frontend.Olean.Roots)
      F #[ConRon.Refine.absName cName] m)
    (hci : ConLeche.Frontend.Olean.InModulePart
      (ConLeche.Driver.trustedOr (absSearchPath tdirs) (absSearchPath ddirs) : ConLeche.Frontend.Olean.Roots)
      F m .private ci)
    (hty : ci.type = .const ConLeche.falseName []) : False := by
  have hsp : (absRoots spR).bare = absRoots spR := by rw [hsr]; exact solRoots_bare _
  obtain ⟨Cg, rk, good, hC, edges, inj, hhdr⟩ := rust_graph_cmp hsnap hsp hgr h1g hpk hroots hgraph
  have acc := acc_compare hR hsnap hsr hpins hwork hcmp hhdr
  rw [hsr] at good hhdr acc
  exact ConLeche.Driver.Compose.compare_no_False V Cg rk good hC edges inj hhdr acc hcl hci hty

/-- con-leche: ConLeche/MainTheorem.lean:109 main_modular — `model_modular_of` at Theorem 1 of the
reach (`reachRunHyp_holds`): **an accepted modular check has a family of models**, its premises
the calls of the graph check and of every module's worker alone. -/
theorem model_modular (V : Type w) [ConLeche.SetTheory V] {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs}
    {fsv : Fs} {F : ConLeche.FS} (hsnap : SnapshotOf finst fsv F)
    {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {rName : kernel.name.Name}
    {g1 gR : arena.monad.AState} {gstore2 gstore3 : arena.store.EStore}
    {pk : frontend.olean.spec.OleanPins} {groots : alloc.vec.Vec arena.handle.NIdx}
    {c : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
    (h1g : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), g1))
    (hpk : frontend.olean.spec.olean_pins emptyTier g1.store = ok (.Ok pk, gstore2))
    (hroots : InternRoots emptyTier { g1 with store := gstore2 } [rName] groots.val gR)
    (hgraph : frontend.modular.graph.graph_of finst fsv pk emptyTier gR.store
      ⟨dirs, alloc.vec.Vec.new _⟩ groots none = ok (.Ok c, gstore3))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    (hwork : ∀ m', ConLeche.Frontend.Olean.HdrClosure (absSearchPath dirs) F
        [ConRon.Refine.absName rName] m' →
      ∃ (mName : kernel.name.Name), ConRon.Refine.absName mName = m' ∧
      ∃ (st1 st2 st3 st4 st5 : arena.monad.AState) (m : arena.handle.NIdx)
        (ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet) (maxNatSize : ron.nat.Nat)
        (w : frontend.modular.worker.WorkerRead) (ds : alloc.vec.Vec arena.env.IDeclaration)
        (ix : arena.stream_index.IStreamIndex) (tier : arena.store.PersTier)
        (frozen : arena.store.EStore) (ws ws' : arena.monad.AState),
        arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1) ∧
        InternRoots emptyTier st1 [mName] [m] st2 ∧
        arena.checker.intern_all_pins emptyTier st2 pins maxNatSize = ok (.Ok ipins, st3) ∧
        frontend.modular.worker.worker_read finst fsv emptyTier st3 ⟨dirs, alloc.vec.Vec.new _⟩
          ipins m (alloc.vec.Vec.new _) = ok (.Ok w, st4) ∧
        frontend.modular.worker.worker_decls w = ok ds ∧
        (do
          let e ← arena.stream_index.stream_index_empty
          arena.stream_index.build_index emptyTier st4 e ds 0#usize) = ok (.Ok ix, st5) ∧
        arena.checker.freeze_tier st5.store ix = ok (tier, frozen) ∧
        arena.checker.worker_state st5.pins = ok ws ∧
        frontend.modular.reach.infer_flags tier ws w.reach.ctx w.reach.pending = ok (.Ok (), ws') ∧
        ParallelAll (ds.length - w.start.val) (oleanWorkerInit st5.pins)
          (fun c k => oleanJobStepSol finst fsv tier .Verified ipins ds w.pins w.values
            ⟨dirs, alloc.vec.Vec.new _⟩ none c (w.start.val + k))) :
    ∃ model : ConLeche.Name → (ConLeche.Name → List Nat → V),
      (∀ m, ConLeche.Frontend.Olean.InClosure (absSearchPath dirs) F #[ConRon.Refine.absName rName] m →
        ConLeche.IsModel V (model m) (ConLeche.Frontend.Olean.moduleConstants (absSearchPath dirs) F m)) ∧
      (∀ m n m', ConLeche.Frontend.Olean.InClosure (absSearchPath dirs) F #[ConRon.Refine.absName rName] m →
        ConLeche.Frontend.Olean.Sees (absSearchPath dirs) F m n m' → model m n = model m' n) :=
  model_modular_of ConRon.Bridge.Modular.reachRunHyp_holds V hsnap h1g hpk hroots hgraph hpins hwork

/-- con-leche: ConLeche/MainTheorem.lean:143 main_modular_compare — `model_modular_compare_of`
at Theorem 1 of the reach: **an accepted modular comparison's challenge closure has a family of
models**. -/
theorem model_modular_compare (V : Type w) [ConLeche.SetTheory V] {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs}
    {fsv : Fs} {F : ConLeche.FS} (hsnap : SnapshotOf finst fsv F)
    {tdirs ddirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {cName sName : kernel.name.Name}
    {spR : frontend.olean.files.Roots}
    (hsr : absRoots spR = (⟨ConRon.Refine.absName cName, ConRon.Refine.absName sName,
      absSearchPath tdirs, absSearchPath ddirs, none⟩ : ConLeche.Driver.CmpReq).solRoots)
    {g1 gR : arena.monad.AState} {gstore2 gstore3 : arena.store.EStore}
    {pk : frontend.olean.spec.OleanPins} {gc gs : arena.handle.NIdx}
    {groots : alloc.vec.Vec arena.handle.NIdx} (hgr : groots.val = [gc])
    {cg : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
    (h1g : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), g1))
    (hpk : frontend.olean.spec.olean_pins emptyTier g1.store = ok (.Ok pk, gstore2))
    (hroots : InternRoots emptyTier { g1 with store := gstore2 } [cName, sName] [gc, gs] gR)
    (hgraph : frontend.modular.graph.graph_of finst fsv pk emptyTier gR.store spR groots
      (some (gc, gs)) = ok (.Ok cg, gstore3))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    (hwork : ∀ m', ConLeche.Frontend.Olean.HdrClosure (absRoots spR) F
        [ConRon.Refine.absName cName, ConRon.Refine.absName sName] m' →
      m' ≠ ConRon.Refine.absName cName →
      ∃ (mName : kernel.name.Name), ConRon.Refine.absName mName = m' ∧
      ∃ (m : arena.handle.NIdx) (st1 st2 st3 st4 st5 : arena.monad.AState) (ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
        (maxNatSize : ron.nat.Nat) (w : frontend.modular.worker.WorkerRead)
        (ds : alloc.vec.Vec arena.env.IDeclaration) (ix : arena.stream_index.IStreamIndex)
        (tier : arena.store.PersTier) (frozen : arena.store.EStore) (ws ws' : arena.monad.AState),
        arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1) ∧
        InternRoots emptyTier st1 [mName] [m] st2 ∧
        arena.checker.intern_all_pins emptyTier st2 pins maxNatSize = ok (.Ok ipins, st3) ∧
        frontend.modular.worker.worker_read finst fsv emptyTier st3 spR ipins m (alloc.vec.Vec.new _) = ok (.Ok w, st4) ∧
        frontend.modular.worker.worker_decls w = ok ds ∧
        (do
          let e ← arena.stream_index.stream_index_empty
          arena.stream_index.build_index emptyTier st4 e ds 0#usize) = ok (.Ok ix, st5) ∧
        arena.checker.freeze_tier st5.store ix = ok (tier, frozen) ∧
        arena.checker.worker_state st5.pins = ok ws ∧
        frontend.modular.reach.infer_flags tier ws w.reach.ctx w.reach.pending = ok (.Ok (), ws') ∧
        ParallelAll (ds.length - w.start.val) (oleanWorkerInit st5.pins)
          (fun c k => oleanJobStepSol finst fsv tier .Verified ipins ds w.pins w.values
            spR none c (w.start.val + k)))
    (hcmp : ∃ (c sH : arena.handle.NIdx) (xi : frontend.olean.spec.ImportF arena.handle.NIdx)
        (x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)) (st1 st2 st3 st4 st5 : arena.monad.AState) (ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
        (maxNatSize : ron.nat.Nat) (w : frontend.modular.worker.WorkerRead)
        (ds : alloc.vec.Vec arena.env.IDeclaration) (ix : arena.stream_index.IStreamIndex)
        (tier : arena.store.PersTier) (frozen : arena.store.EStore) (ws ws' : arena.monad.AState),
        arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1) ∧
        InternRoots emptyTier st1 [cName, sName] [c, sH] st2 ∧
        frontend.modular.graph.solution_import sH = ok xi ∧ x.val = [xi] ∧
        arena.checker.intern_all_pins emptyTier st2 pins maxNatSize = ok (.Ok ipins, st3) ∧
        frontend.modular.worker.worker_read finst fsv emptyTier st3 spR ipins c x = ok (.Ok w, st4) ∧
        frontend.modular.worker.worker_decls w = ok ds ∧
        (do
          let e ← arena.stream_index.stream_index_empty
          arena.stream_index.build_index emptyTier st4 e ds 0#usize) = ok (.Ok ix, st5) ∧
        arena.checker.freeze_tier st5.store ix = ok (tier, frozen) ∧
        arena.checker.worker_state st5.pins = ok ws ∧
        frontend.modular.reach.infer_flags tier ws w.reach.ctx w.reach.pending = ok (.Ok (), ws') ∧
        ParallelAll (ds.length - w.start.val) (oleanWorkerInit st5.pins)
          (fun c k => oleanJobStepSol finst fsv tier .Verified ipins ds w.pins w.values
            spR none c (w.start.val + k))) :
    ∀ fs', ConLeche.FS.AgreeUnder (ConLeche.Driver.trustedOr (absSearchPath tdirs) (absSearchPath ddirs))
        F fs' →
      ∃ model : ConLeche.Name → (ConLeche.Name → List Nat → V),
        (∀ m, ConLeche.Frontend.Olean.InClosure
            (ConLeche.Driver.trustedOr (absSearchPath tdirs) (absSearchPath ddirs) : ConLeche.Frontend.Olean.Roots)
            fs' #[ConRon.Refine.absName cName] m →
          ConLeche.IsModel V (model m) (ConLeche.Frontend.Olean.moduleConstants
            (ConLeche.Driver.trustedOr (absSearchPath tdirs) (absSearchPath ddirs) : ConLeche.Frontend.Olean.Roots) fs' m)) ∧
        (∀ m n m', ConLeche.Frontend.Olean.InClosure
            (ConLeche.Driver.trustedOr (absSearchPath tdirs) (absSearchPath ddirs) : ConLeche.Frontend.Olean.Roots)
            fs' #[ConRon.Refine.absName cName] m →
          ConLeche.Frontend.Olean.Sees
            (ConLeche.Driver.trustedOr (absSearchPath tdirs) (absSearchPath ddirs) : ConLeche.Frontend.Olean.Roots)
            fs' m n m' → model m n = model m' n) :=
  model_modular_compare_of ConRon.Bridge.Modular.reachRunHyp_holds V hsnap hsr hgr h1g hpk hroots hgraph hpins hwork hcmp

/-- con-leche: ConLeche/MainTheorem.lean:183 main_modular_compare_no_False —
`no_False_modular_compare_of` at Theorem 1 of the reach: **no accepted modular comparison's
challenge module holds a constant of type `False`**. -/
theorem no_False_modular_compare (V : Type w) [ConLeche.SetTheory V] {Fs : Type} {finst : frontend.checker_io.CheckerFs Fs}
    {fsv : Fs} {F : ConLeche.FS} (hsnap : SnapshotOf finst fsv F)
    {tdirs ddirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {cName sName : kernel.name.Name}
    {spR : frontend.olean.files.Roots}
    (hsr : absRoots spR = (⟨ConRon.Refine.absName cName, ConRon.Refine.absName sName,
      absSearchPath tdirs, absSearchPath ddirs, none⟩ : ConLeche.Driver.CmpReq).solRoots)
    {g1 gR : arena.monad.AState} {gstore2 gstore3 : arena.store.EStore}
    {pk : frontend.olean.spec.OleanPins} {gc gs : arena.handle.NIdx}
    {groots : alloc.vec.Vec arena.handle.NIdx} (hgr : groots.val = [gc])
    {cg : alloc.vec.Vec (arena.handle.NIdx × alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx))}
    (h1g : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), g1))
    (hpk : frontend.olean.spec.olean_pins emptyTier g1.store = ok (.Ok pk, gstore2))
    (hroots : InternRoots emptyTier { g1 with store := gstore2 } [cName, sName] [gc, gs] gR)
    (hgraph : frontend.modular.graph.graph_of finst fsv pk emptyTier gR.store spR groots
      (some (gc, gs)) = ok (.Ok cg, gstore3))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    (hwork : ∀ m', ConLeche.Frontend.Olean.HdrClosure (absRoots spR) F
        [ConRon.Refine.absName cName, ConRon.Refine.absName sName] m' →
      m' ≠ ConRon.Refine.absName cName →
      ∃ (mName : kernel.name.Name), ConRon.Refine.absName mName = m' ∧
      ∃ (m : arena.handle.NIdx) (st1 st2 st3 st4 st5 : arena.monad.AState) (ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
        (maxNatSize : ron.nat.Nat) (w : frontend.modular.worker.WorkerRead)
        (ds : alloc.vec.Vec arena.env.IDeclaration) (ix : arena.stream_index.IStreamIndex)
        (tier : arena.store.PersTier) (frozen : arena.store.EStore) (ws ws' : arena.monad.AState),
        arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1) ∧
        InternRoots emptyTier st1 [mName] [m] st2 ∧
        arena.checker.intern_all_pins emptyTier st2 pins maxNatSize = ok (.Ok ipins, st3) ∧
        frontend.modular.worker.worker_read finst fsv emptyTier st3 spR ipins m (alloc.vec.Vec.new _) = ok (.Ok w, st4) ∧
        frontend.modular.worker.worker_decls w = ok ds ∧
        (do
          let e ← arena.stream_index.stream_index_empty
          arena.stream_index.build_index emptyTier st4 e ds 0#usize) = ok (.Ok ix, st5) ∧
        arena.checker.freeze_tier st5.store ix = ok (tier, frozen) ∧
        arena.checker.worker_state st5.pins = ok ws ∧
        frontend.modular.reach.infer_flags tier ws w.reach.ctx w.reach.pending = ok (.Ok (), ws') ∧
        ParallelAll (ds.length - w.start.val) (oleanWorkerInit st5.pins)
          (fun c k => oleanJobStepSol finst fsv tier .Verified ipins ds w.pins w.values
            spR none c (w.start.val + k)))
    (hcmp : ∃ (c sH : arena.handle.NIdx) (xi : frontend.olean.spec.ImportF arena.handle.NIdx)
        (x : alloc.vec.Vec (frontend.olean.spec.ImportF arena.handle.NIdx)) (st1 st2 st3 st4 st5 : arena.monad.AState) (ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
        (maxNatSize : ron.nat.Nat) (w : frontend.modular.worker.WorkerRead)
        (ds : alloc.vec.Vec arena.env.IDeclaration) (ix : arena.stream_index.IStreamIndex)
        (tier : arena.store.PersTier) (frozen : arena.store.EStore) (ws ws' : arena.monad.AState),
        arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1) ∧
        InternRoots emptyTier st1 [cName, sName] [c, sH] st2 ∧
        frontend.modular.graph.solution_import sH = ok xi ∧ x.val = [xi] ∧
        arena.checker.intern_all_pins emptyTier st2 pins maxNatSize = ok (.Ok ipins, st3) ∧
        frontend.modular.worker.worker_read finst fsv emptyTier st3 spR ipins c x = ok (.Ok w, st4) ∧
        frontend.modular.worker.worker_decls w = ok ds ∧
        (do
          let e ← arena.stream_index.stream_index_empty
          arena.stream_index.build_index emptyTier st4 e ds 0#usize) = ok (.Ok ix, st5) ∧
        arena.checker.freeze_tier st5.store ix = ok (tier, frozen) ∧
        arena.checker.worker_state st5.pins = ok ws ∧
        frontend.modular.reach.infer_flags tier ws w.reach.ctx w.reach.pending = ok (.Ok (), ws') ∧
        ParallelAll (ds.length - w.start.val) (oleanWorkerInit st5.pins)
          (fun c k => oleanJobStepSol finst fsv tier .Verified ipins ds w.pins w.values
            spR none c (w.start.val + k)))
    {m : ConLeche.Name} {ci : ConLeche.ConstantInfo}
    (hcl : ConLeche.Frontend.Olean.InClosure
      (ConLeche.Driver.trustedOr (absSearchPath tdirs) (absSearchPath ddirs) : ConLeche.Frontend.Olean.Roots)
      F #[ConRon.Refine.absName cName] m)
    (hci : ConLeche.Frontend.Olean.InModulePart
      (ConLeche.Driver.trustedOr (absSearchPath tdirs) (absSearchPath ddirs) : ConLeche.Frontend.Olean.Roots)
      F m .private ci)
    (hty : ci.type = .const ConLeche.falseName []) : False :=
  no_False_modular_compare_of ConRon.Bridge.Modular.reachRunHyp_holds V hsnap hsr hgr h1g hpk hroots hgraph hpins hwork hcmp hcl hci hty

end RustModular

/-! ## 5. The census

`#print axioms` of the roots: con-leche's own three axioms and nothing else — no `sorryAx`, no
`native_decide`.  The named hypotheses of the module note are the whole ledger: they are
hypotheses of the statements, not axioms of the environment, so this census does not list
them. -/

/-- info: 'ConRon.MainTheorem.Stages.model_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_exists

/-- info: 'ConRon.MainTheorem.Stages.no_False_declaration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_False_declaration

/-- info: 'ConRon.MainTheorem.Stages.model_exists_embedded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 kernel.pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms model_exists_embedded

/-- info: 'ConRon.MainTheorem.Stages.no_False_declaration_embedded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 kernel.pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms no_False_declaration_embedded

/-- info: 'ConRon.MainTheorem.Stages.no_False_oleans_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_False_oleans_of

/-- info: 'ConRon.MainTheorem.Stages.model_exists_oleans_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_exists_oleans_of

/-- info: 'ConRon.MainTheorem.Stages.no_False_oleans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_False_oleans

/-- info: 'ConRon.MainTheorem.Stages.model_exists_oleans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_exists_oleans

/-- info: 'ConRon.MainTheorem.Stages.model_exists_compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_exists_compare

/-- info: 'ConRon.MainTheorem.Stages.no_False_compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_False_compare

/-- info: 'ConRon.MainTheorem.Stages.no_False_oleans_compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_False_oleans_compare

/-- info: 'ConRon.MainTheorem.Stages.model_exists_oleans_compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_exists_oleans_compare

/-- info: 'ConRon.MainTheorem.Stages.model_modular_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_modular_of

/-- info: 'ConRon.MainTheorem.Stages.model_modular_compare_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_modular_compare_of

/-- info: 'ConRon.MainTheorem.Stages.no_False_modular_compare_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_False_modular_compare_of

/-- info: 'ConRon.MainTheorem.Stages.model_modular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_modular

/-- info: 'ConRon.MainTheorem.Stages.model_modular_compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_modular_compare

/-- info: 'ConRon.MainTheorem.Stages.no_False_modular_compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_False_modular_compare

end ConRon.MainTheorem.Stages

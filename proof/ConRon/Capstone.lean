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

/-!
# `ConRon.Capstone` — THE COMPOSITION: Theorem 2 ∘ Theorem 1 ∘ con-leche

DESIGN.md §8.2's last line: *"Capstones for the binary = Theorem 2 ∘
Theorem 1 ∘ con-leche."*  This is the one module that imports both
`ConRon.Bridge` (Theorem 1, (B) ⇒ (A)) and `ConRon.Refine2` (Theorem 2,
(C) ⇒ (B)), and it states the binary's headline theorems:

* `ConRon.Capstone.model_exists` — the environment of every stream the Aeneas
  model of the Rust pipeline accepts has a model in every set theory;
* `ConRon.Capstone.no_False_declaration` — a file that declares a theorem of
  type `False` is never accepted by it;
* `no_False_oleans` / `model_exists_oleans` — the same on `--olean`.

**They are the campaign's root theorems** (task #97-COMPOSE): the sorry
frontier is measured as their dependency closure, and §5's census prints their
axioms.  What they assume is exactly their premises, listed below.

## The pipeline, stage by stage

The binary (`crates/con-ron/src/bin/con-ron.rs`) is an unverified driver
around the extracted core functions and the pin decoder, in this order, on
one `AState` made from `EStore::empty()` and one `PersTier::empty()`:

    intern_reserved_pins → builtin_prelude_e → parse_source
      → prepare_d → (decode) → intern_all_pins → (the check phase)

**The check phase is the one the binary's driver runs, pool and all**
(`driver::check_decls_driver`): it builds the stream's index from the records
(`stream_index::build_index`), freezes the tier with the index in it
(`checker::freeze_tier`), runs every record's job on `pool::parallel_all`, and
thaws the tier.  The headlines take one premise per step (`h6` the index, `h7`
the freeze, `h8` the pool), which `poolAccepts_intro` assembles into
`Refine2/Checker/Phased.lean`'s `PoolAccepts`.  `h8` is the contract of the generic
combinator `pool::parallel_all` at the driver's two verified closures (`ParallelAll`
at `jobStep`): index lists, one per worker, covering every job, each in increasing
order, and for each a fold of `run_job` over its indices from `worker_state`,
accepting.  That contract is the pool's trusted claim (OVERVIEW §8.2): control flow of
`pool.rs`, nothing about the checker.

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

The headlines start from the binary's own start values (`startState` =
`AState::empty()`, `emptyTier` = `PersTier::empty()`) and name the call the
binary makes at each step.  Beside `[ConLeche.SetTheory V]`, the file's shape
`hfalse` and the one premise per call (`h1`…`h5`, `hpins`, `h6`…`h8`), what
they assume is exactly:

* `hreads : ReadsAs sinst src chunks.val` — the reads are the chunks: the binary
  parses with the verified reader loop `parse_source` over the driver's file
  handle, and `Refine2/Frontend/Source.lean`'s `parse_source_eq` makes that
  `parse_chunks` over the chunks the handle hands out; that the handle hands out
  the file's bytes, in order, is the input seam;
* on `--olean`, `hsnap : SnapshotOf finst fsv F` — the file instance answers as
  one snapshot `F`.

`hpins` is the premise for the binary's pin step: the pin list is what the verified
decoder read, at any text (as con-leche's theorems hold at every pin list);
`model_exists_embedded` / `no_False_declaration_embedded` fix the text to the embedded
`PINS_TEXT`.
-/

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Capstone

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
interned one by one (`bin/con-ron.rs`, `olean_fs::read_request`), and `records::read_oleans` over
the store, at the instance `olean_fs::StdFs`; the preparation reads what a record uses off the
read (`prepare_d` at the `OleanRead`), and each theorem's job reads its value from its file. -/

section RustOleans

open ConRon.Refine2 ConRon.Refine2.Frontend ConRon.Refine2.Frontend.Olean

/-- **The instance answers as one snapshot `F`**, at the paths the reader asks (`PathRel`): the file
seam's premise, as `ReadsAs` is the stream's.  Each answer the instance gives is `F`'s; a failing
operation claims nothing, since it gives the reader no accept. -/
structure SnapshotOf {Fs : Type} (inst : frontend.olean.files.OleanFs Fs) (fsv : Fs)
    (F : ConLeche.FS) : Prop where
  path_exists : ∀ {p q}, PathRel p q → ∀ b, inst.path_exists fsv p = ok (.Ok b) →
    b = (F.real q).isSome
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
theorem fsRel_of_snapshot {Fs : Type} {inst : frontend.olean.files.OleanFs Fs} {fsv : Fs}
    {F : ConLeche.FS} (h : SnapshotOf inst fsv F) :
    FsRel inst fsv (ConRon.Bridge.Frontend.Olean.modelFs F) where
  pathExists := fun hp b hb => by
    rw [h.path_exists hp b hb]
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

/-- **The driver's loop over the roots** (`olean_fs::OleanRequest::intern`): each name interned, the
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
    {Fs : Type} {finst : frontend.olean.files.OleanFs Fs} {fsv : Fs} {F : ConLeche.FS}
    (hsnap : SnapshotOf finst fsv F)
    {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {store3 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv pers stR.store dirs roots none
      = ok (.Ok rd, store3))
    (h4 : frontend.prepare.prepare_d frontend.olean.records.OleanRead.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts pers { stR with store := store3 } pre rd.decls rd
      = ok (.Ok prepared, st4))
    {maxNatSize : ron.nat.Nat}
    (h5 : arena.checker.intern_all_pins pers st4 pins maxNatSize = ok (.Ok ipins, st5))
    (h6 : OleanPoolAccepts finst fsv pers st5 .Verified ipins prepared.decls rd.pins rd.values dirs ix st6) :
    ∃ (sA sB sB' sC sD sE sF : ConRon.Arena.AState) (rd' : ConRon.Arena.Frontend.Olean.OleanRead)
      (I : ConRon.Arena.IStreamIndex),
      ConRon.Arena.internReservedPins
          (ConRon.Arena.AState.init ConRon.Arena.EStore.empty) = .ok ((), sA) ∧
      ConRon.Arena.Frontend.builtinPreludeE sA = .ok (.ok (absPreludeIx pre), sB) ∧
      (names.map ConRon.Refine.absName).mapM ConRon.Arena.internName sB
          = .ok (roots.val.map absNIdx, sB') ∧
      ConRon.Arena.Frontend.Olean.readOleans (ConRon.Bridge.Frontend.Olean.modelFs F)
          (absSearchPath dirs) (roots.val.map absNIdx).toArray none sB' = .ok (.ok rd', sC) ∧
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

`check_main` starts from `AState::empty()` (`bin/con-ron.rs:332`, which is
`AState::init(EStore::empty())`) and `&PersTier::empty()`
(`bin/con-ron.rs:339`).  The Aeneas model of each is a `Result` that is
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

/-- `stream_index_empty()` (`arena/stream_index.rs`): no constants, no tables, no records. -/
def emptyIndex : arena.stream_index.IStreamIndex :=
  { consts := alloc.vec.Vec.new _, idx := emptyMap _ _, tables := alloc.vec.Vec.new _,
    tbls := emptyMap _ _, firsts := alloc.vec.Vec.new _, next := 0#u64 }

/-- **The binary's persistent tier**, `&PersTier::empty()`
(`bin/con-ron.rs:339`): the tier every stage up to the check phase is handed — not
frozen, its four table sets, every table empty, and the empty stream index. -/
def emptyTier : arena.store.PersTier :=
  { frozen := false, n := emptyNTables, l := emptyLTables, ls := emptyLsTables,
    e := emptyETables, env := emptyIndex }

/-- **The binary's start state**, `AState::empty()` (`bin/con-ron.rs:332`),
which is `AState::init(EStore::empty())`: a store whose four layers (names,
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
        inst_lp_ls_c := emptyMap _ _, lp_def_c := emptyMap _ _, crf_c := emptyMap _ _ },
    caches :=
      { whnf_core_c := emptyMap _ _, whnf_core_cheap_c := emptyMap _ _,
        whnf_c := emptyMap _ _, infer_c := emptyMap _ _,
        infer_io_c := emptyMap _ _, defeq_c := emptyMap _ _,
        lvl_eq_c := emptyMap _ _, lvls_eq_c := emptyMap _ _, const_ty_c := emptyMap _ _,
        const_val_c := emptyMap _ _, rule_rhs_c := emptyMap _ _, read_l_c := emptyMap _ _,
        read_n_c := emptyMap _ _, read_ls_c := emptyMap _ _,
        eager_memos :=
          { whnf_core_c := emptyMap _ _, whnf_core_cheap_c := emptyMap _ _,
            whnf_c := emptyMap _ _, infer_c := emptyMap _ _,
            infer_io_c := emptyMap _ _, defeq_c := emptyMap _ _ } },
    pins :=
      { names := alloc.vec.Vec.new _, reserved := alloc.vec.Vec.new _,
        empty_levels := { word := 0#u32 }, zero_level := { word := 0#u32 },
        sort_one := { word := 0#u32 } } }

theorem startState_eq : arena.monad.AState.empty = ok startState := by
  simp only [arena.monad.AState.empty, arena.store.Tbl.empty, arena.store.ETables.empty,
    arena.store.LsTables.empty, arena.store.LTables.empty, arena.store.NTables.empty,
    arena.store.NStore.empty, arena.store.LStore.empty, arena.store.LsStore.empty,
    arena.store.EStore.empty, ron.hashmap2.HashMap2.new, arena.cons_map.ConsMap.new,
    arena.monad.AState.init, arena.monad.Memos.empty, arena.core_state.Caches.empty,
    arena.core_state.ModeMemos.empty, arena.pins.Pins.empty, arena.handle.LsIdx.of_word, arena.handle.LIdx.of_word,
    arena.handle.EIdx.of_word, bind_ok]
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
      env = ConLeche.Cached.streamEnv dsP

/-- **What the Rust's records denote on `--olean`**: `RustDenotes`, each theorem's reference
replaced by a value (`fillDecl`): the records of an `--olean` run hold a reference where a
theorem's value is, and each theorem's job reads the value from its file. -/
def RustDenotesFilled (ds : alloc.vec.Vec arena.env.IDeclaration) (st : arena.monad.AState)
    (env : ConLeche.Env) : Prop :=
  ∃ (lst : ConRon.Arena.AState) (dsP : List ConLeche.Declaration) (val : Nat → ConLeche.Expr),
    AStateRel emptyTier st lst ∧ ConRon.Bridge.denoteDecls lst.store (absIDeclL ds) = some dsP ∧
      env = ConLeche.Cached.streamEnv
        (dsP.map (ConLeche.Cached.fillDecl (ConRon.Bridge.fillRef val)))

/-- `prepare::prepare_d` at `DeclUsedConsts`, the call the binary makes on a stream
(`bin/con-ron.rs:445`), is `prepare_prelude`'s body: `prepare_prelude` is its `.decls`. -/
theorem prepare_prelude_of_prepare_d {pers : arena.store.PersTier}
    {st st' : arena.monad.AState} {pre : frontend.prepare.PreludeIx}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {p : frontend.prepare.Prepared}
    (h : frontend.prepare.prepare_d frontend.nat_op_ground.DeclUsedConsts.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts pers st pre ds () = ok (.Ok p, st')) :
    frontend.prepare.prepare_prelude pers st pre ds = ok (.Ok p.decls, st') := by
  rw [frontend.prepare.prepare_prelude, h]
  simp only [bind_ok]
  rfl

/-- `pins_decode::decode_embedded()`, the call the binary's
`driver::pins_for_run` makes (`driver.rs:299`), is `decode` of some text. -/
theorem decode_of_decode_embedded
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (h : kernel.pins_decode.decode_embedded = ok (.Ok pins)) :
    ∃ text, kernel.pins_decode.decode text = ok (.Ok pins) := by
  rw [kernel.pins_decode.decode_embedded] at h
  obtain ⟨text, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  exact ⟨text, h⟩

end Defs

/-! ## 4. The headline theorems

Each takes one premise per call the binary's `check_main` makes, in its order, each starting
from the state the previous one left and the first from the binary's own start values.
`check_main` itself is not verified: a reader walks through it and finds each verified call as
one premise.

| premise | `check_main`'s call |
|---|---|
| `startState`, `emptyTier` | `bin/con-ron.rs:332` `AState::empty()`, `:339` `&PersTier::empty()` |
| `h1` | `bin/con-ron.rs:348` `arena::pins::intern_reserved_pins` |
| `h2` | `bin/con-ron.rs:367` `prelude::builtin_prelude_e` |
| `hreads`, `h3` | `bin/con-ron.rs:396` `driver::parse_export_stream_d`, which is `driver.rs:961`'s `export_c::parse_source` over the file's handle |
| `h4` | `bin/con-ron.rs:445` `prepare::prepare_d` at `DeclUsedConsts` |
| `hpins` | `bin/con-ron.rs:467` `driver::pins_for_run`, whose default is `driver.rs:311` `pins_decode::decode_embedded()`, which is `decode` of the embedded `PINS_TEXT` (the `_embedded` corollaries below name it) |
| `h5` | `bin/con-ron.rs:504` `checker::intern_all_pins` at `--max-nat-size`'s value (`driver::max_nat_size_arg`, default `pins::max_nat_size_default()`); the theorems hold at every `maxNatSize` |
| `h6` | `bin/con-ron.rs:516`/`:518` `driver::check_decls_driver` at `CheckMode::Verified` (`:325`), the index: `driver.rs:540` `stream_index::build_index(…, stream_index_empty(), ds, 0)` |
| `h7` | the same, the boundary: `driver.rs:548` `checker::freeze_tier` |
| `h8` | the same, the check phase: `driver.rs:554` `pool::parallel_all` with `init` `checker::worker_state` and `step` `checker::run_job` (`thaw_tier` at `:569` restores the store) |

`h8` is not one equation: `parallel_all` is not extracted, so `h8` states its contract
(the pool's trusted claim, `pool.rs`'s note, OVERVIEW §8.2) at the driver's two verified
closures, `Refine2/Checker/Phased.lean`'s `ParallelAll` at `jobStep`: some lists of record
positions, one per worker, together covering every position, each in increasing order, and
for each list the worker's run, `worker_state st6.pins` and then `run_job` on each position
in order, every step answering `Ok(())`.  A job is not asked to be claimed once.  Each job is a
fact about the worker's state at its position: the earlier records' jobs give the fold's
prefix (`Bridge/Checker/Pooled.lean`'s `pooled_fold`).

The theorems hold at every chunk source whose reads are `chunks`, and every pin text
`hpins` decodes, as con-leche's hold at every pin list.  **`--pins FILE`** (read by the
unverified `con_ron_dump::parse_pins`) and **`--no-pins`** do not call the decoder, so runs
with them are outside the theorems.

`hpins` is stated about `decode` of a free text rather than about `decode_embedded` because
naming the embedded constant `PINS_TEXT` costs the census one axiom,
`kernel.pins_text.PINS_TEXT._native.decide.ax_1` — the one Aeneas's `toStr` spends on that
constant's DEFINITION (AENEAS_FINDINGS.md §3.8; `Refine2/Checker/PinsWF.lean`'s census),
nothing this proof evaluates.  `model_exists_embedded` / `no_False_declaration_embedded` are
the headlines with `decode_embedded` itself in the premise, and carry that axiom.

**`--olean`.**  `no_False_oleans` and `model_exists_oleans` take the same calls with the
stream's replaced, as `Input::Oleans` runs them (`olean_fs::read_request`):

| premise | the binary's call |
|---|---|
| `hroots` | `olean_fs.rs:270` `monad::intern_name` on each root |
| `hsnap`, `h3` | `olean_fs.rs:294` `records::read_oleans` at `olean_fs::StdFs`, whose answers are one snapshot's |
| `h4` | `bin/con-ron.rs:446` `prepare::prepare_d` at the `OleanRead` |
| `h8` | `bin/con-ron.rs:509`/`:511` `driver::check_decls_driver_with`, `init` `(worker_state, value_cache_empty)` and `step` `driver::olean_job` |

`h4` starts from the state `hroots` left with the store `h3` left: the reader takes the store
alone.  `hcl`, `hv`, `hmem`, `hk`, `hty` are upstream's, by the specification (`InClosure`,
`ViewOf`: `decodeModuleSpec`).  `--constant` is outside them, as a run from `constants =
none`.  Each is its `_of` form, which takes Theorem 2 at the reader as `hT2 :
ReadOleansRefines` (`Refine2/Frontend/Olean/Contract.lean`), at `read_oleans_refines`. -/

section Headline

open ConRon.Refine2 ConRon.Refine2.Frontend ConRon.Refine2.Frontend.Olean

/-- con-leche: ConLeche/MainTheorem.lean:98 model_exists —
**THE MAIN THEOREM FOR THE RUST CHECKER** (DESIGN.md §1, §8.2): the environment of every stream
the Rust checker accepts has a model, in every set theory.

con-leche's reads `(accepted : checkDecls .verified pins ds = .ok env) : Nonempty (Model V env)`;
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

/-- con-leche: ConLeche/MainTheorem.lean:112 no_False_declaration — **A FILE THAT DECLARES A
THEOREM OF TYPE `False` IS REJECTED BY THE RUST CHECKER**: the binary's calls (§4's table)
cannot all succeed on it.

con-leche's concludes `∃ e, (do …; checkDecls .verified pins ds) = .error e` about its own
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

/-- `model_exists` with the pin premise the binary's own call,
`pins_decode::decode_embedded()` (`driver.rs:311`).  Its census adds
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

/-- `no_False_declaration` with the pin premise the binary's own call,
`pins_decode::decode_embedded()` (`driver.rs:311`).  Its census adds
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

/-- con-leche: ConLeche/MainTheorem.lean:161 main_oleans_no_False — **A CLOSURE THAT HOLDS A
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
    {Fs : Type} {finst : frontend.olean.files.OleanFs Fs} {fsv : Fs}
    (hsnap : SnapshotOf finst fsv F)
    {rd : frontend.olean.records.OleanRead} {store3 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store dirs roots none
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
      (oleanJobStep finst fsv tier .Verified ipins prepared.decls rd.pins rd.values dirs)) :
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
    {Fs : Type} {finst : frontend.olean.files.OleanFs Fs} {fsv : Fs}
    (hsnap : SnapshotOf finst fsv F)
    {rd : frontend.olean.records.OleanRead} {store3 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store dirs roots none
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
      (oleanJobStep finst fsv tier .Verified ipins prepared.decls rd.pins rd.values dirs)) :
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

/-- con-leche: ConLeche/MainTheorem.lean:161 main_oleans_no_False — **A CLOSURE THE RUST
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
    {Fs : Type} {finst : frontend.olean.files.OleanFs Fs} {fsv : Fs}
    (hsnap : SnapshotOf finst fsv F)
    {rd : frontend.olean.records.OleanRead} {store3 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store dirs roots none
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
      (oleanJobStep finst fsv tier .Verified ipins prepared.decls rd.pins rd.values dirs)) :
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
    {Fs : Type} {finst : frontend.olean.files.OleanFs Fs} {fsv : Fs}
    (hsnap : SnapshotOf finst fsv F)
    {rd : frontend.olean.records.OleanRead} {store3 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store dirs roots none
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
      (oleanJobStep finst fsv tier .Verified ipins prepared.decls rd.pins rd.values dirs)) :
    ∃ env, RustDenotesFilled prepared.decls st6 env ∧ Nonempty (ConLeche.Model V env) :=
  model_exists_oleans_of read_oleans_refines V h1 h2 hroots hsnap h3 h4 hpins h5 h6 h7 h8

end Headline

/-! ## 5. The census

`#print axioms` of the roots: con-leche's own three axioms and nothing else — no `sorryAx`, no
`native_decide`.  The named hypotheses of the module note are the whole ledger: they are
hypotheses of the statements, not axioms of the environment, so this census does not list
them. -/

/-- info: 'ConRon.Capstone.model_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_exists

/-- info: 'ConRon.Capstone.no_False_declaration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_False_declaration

/-- info: 'ConRon.Capstone.model_exists_embedded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 kernel.pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms model_exists_embedded

/-- info: 'ConRon.Capstone.no_False_declaration_embedded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 kernel.pins_text.PINS_TEXT._native.decide.ax_1] -/
#guard_msgs in #print axioms no_False_declaration_embedded

/-- info: 'ConRon.Capstone.no_False_oleans_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_False_oleans_of

/-- info: 'ConRon.Capstone.model_exists_oleans_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_exists_oleans_of

/-- info: 'ConRon.Capstone.no_False_oleans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_False_oleans

/-- info: 'ConRon.Capstone.model_exists_oleans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_exists_oleans

end ConRon.Capstone

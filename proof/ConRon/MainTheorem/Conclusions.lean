import ConRon.MainTheorem.Stages
import ConRon.MainTheorem.PureStored
import ConLeche.Verify.Frontend.StreamModel

/-!
# `ConRon.MainTheorem.Conclusions` — the staged lemmas, concluding in con-leche's words

con-leche's main theorems (`ConLeche/MainTheorem.lean`) conclude in the vocabulary of its
specification: `parseChunks [b]`, `IsModel`, `constantsOf`, `Olean.closureConstants`,
`jsonWithTheoremFalse`.  The staged lemmas (`MainTheorem/Stages.lean` §4) end at the twin's
denotation instead (`RustDenotes … ∧ Nonempty (Model V env)`).  Each theorem here has the step
premises of one staged lemma, the pins the binary's embedded ones (the `_embedded` forms),
and con-leche's conclusion verbatim:

| here | its staged premises | con-leche's conclusion |
|---|---|---|
| `json_model_of_stages` | `model_exists_embedded` | `main_json_model` |
| `json_no_False_of_stages` | `no_False_declaration_embedded` | `main_no_False` |
| `compare_json_model_of_stages` | `model_exists_compare` | `main_compare_json_model` |
| `oleans_model_of_stages` | `model_exists_oleans` | `main_oleans` |
| `compare_model_of_stages` | `model_exists_oleans_compare` | `main_compare_model` |

**The bytes.**  The reader hands out chunks; con-leche speaks of the file's bytes `b`.  The json
theorems take `concatBytes (absChunks chunks) = b` — the chunks, put together, are the file —
and con-leche's own `parseChunks_single_of_concat` moves the parse to `[b]`.  The driver's
positional reads (each chunk the slice `b.extract off (off+csz)`, until an empty read) discharge
it (`concatBytes_readsFrom`'s shape).

**The arguments.**  con-leche's `--olean` conclusions name the search path by the argument string
(`Driver.searchPathOf dirs`, `trustedOr`) and the roots by `parseModName`; here they are the
Rust's own (`absSearchPath dirs`, `absName`), which the driver's argument parser bridges.

The proofs are composition: the staged lemmas' Theorem 2 walks (`rust_stages*`), then
`MainTheorem/PureStored.lean`'s stage lemmas, which are con-leche's `json_isModel`,
`compare_json_isModel`, `oleans_isModel` and `compare_isModel` re-proved at the PURE accept
Theorem 1 gives.
-/

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.MainTheorem.Stages
open ConRon.Refine2 ConRon.Refine2.Frontend ConRon.Refine2.Frontend.Olean
open ConLeche (IsModel constantsOf jsonWithTheoremFalse FS)
open ConLeche.Frontend (parseChunks concatBytes)
open ConLeche.Frontend.Olean (closureConstants)

namespace ConRon.MainTheorem

set_option autoImplicit false

universe w

/-- con-leche: ConLeche/MainTheorem.lean:47 main_json_model — **an accepted file's records have
a model**, con-leche's conclusion at the binary's calls on `-- <file>` (`model_exists_embedded`'s
premises): the chunks the reader handed out, put together, are the file's bytes `b`
(`hb`), and `b` parses (`parseChunks [b]`) to records that have a model in every set theory.

`rust_stages` (Theorem 2), `stages_isModel` (Theorem 1 + `model_exists`'s proof at the pure
accept), and `parseChunks_single_of_concat` (the chunk boundary is invisible). -/
theorem json_model_of_stages (V : Type w) [ConLeche.SetTheory V]
    {st1 st2 st3 st4 st5 st6 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    {Sc : Type} {sinst : frontend.export_c.ChunkSource Sc} {src src' : Sc}
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    (hreads : ReadsAs sinst src chunks.val)
    {b : ByteArray} (hb : concatBytes (absChunks chunks) = b)
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
    ∃ r, parseChunks [b] = .ok r ∧ ∃ model, IsModel V model (· ∈ constantsOf r.decls.toList) := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  have hk : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel := ConRon.Bridge.CoreSpec.of_core
  have hind : ConRon.Bridge.IndSpec := ConRon.Bridge.Inductives.indSpec_of_bridge
  obtain ⟨_, hdec⟩ := decode_of_decode_embedded hpins
  obtain ⟨sA, sB, sC, sD, sE, sF, rv, I, hA, hB, hC, hD, hE, hF, -⟩ :=
    rust_stages hdec rfl hest hst0 h1 h2 hreads h3 (prepare_prelude_of_prepare_d h4) h5
      (poolAccepts_intro h6 h7 h8)
  obtain ⟨r, hr, hm⟩ := ConRon.Bridge.stages_isModel V hk hind hA hB hC hD hE hF
  exact ⟨r, ConLeche.Frontend.parseChunks_single_of_concat hb hr, hm⟩

/-- con-leche: ConLeche/MainTheorem.lean:55 main_no_False — **no accepted file declares a
theorem of type `False`**: the binary's calls on `-- <file>` cannot all succeed on chunks that
put together are a `jsonWithTheoremFalse` file `b`.

`no_False_declaration_embedded` at the chunks, the file's shape read through `concatBytes`. -/
theorem json_no_False_of_stages (V : Type w) [ConLeche.SetTheory V]
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    {b : ByteArray} (hb : concatBytes (absChunks chunks) = b) (hF : jsonWithTheoremFalse [b])
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
    False := by
  have hfalse : jsonWithTheoremFalse (absChunks chunks) := by
    have e : concatBytes [b] = b := by simp [concatBytes]
    unfold jsonWithTheoremFalse at hF ⊢
    rw [hb]
    rw [e] at hF
    exact hF
  exact no_False_declaration_embedded V hfalse h1 h2 hreads h3 h4 hpins h5 h6 h7 h8

/-- con-leche: ConLeche/MainTheorem.lean:63 main_compare_json_model — **an accepted comparison's
challenge file has a model**, con-leche's conclusion at the binary's calls on `--compare -- C S`
(`model_exists_compare`'s premises, the pins the embedded ones): the challenge's chunks put
together are its bytes `bC` (`hbC`), and `bC` parses to records that have a model in every set
theory.  (con-leche's `fs.file c = some bC` is the driver's, lane D's.)

`rust_stages_compare` (Theorem 2), `stagesC_isModel` (Theorem 1 + `solution_model_exists`'s
proof at the pure solution accept and the mixed challenge run). -/
theorem compare_json_model_of_stages (V : Type w) [ConLeche.SetTheory V]
    {st1 st2 st3 st4 st5 st6 st7 st9 st10 st11 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e emptyTier st1 = ok (.Ok pre, st2))
    {Sc : Type} {sinst : frontend.export_c.ChunkSource Sc} {srcC srcC' srcS srcS' : Sc}
    {chunksC chunksS : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    (hreadsC : ReadsAs sinst srcC chunksC.val) (hreadsS : ReadsAs sinst srcS chunksS.val)
    {bC : ByteArray} (hbC : concatBytes (absChunks chunksC) = bC)
    {rC rS : frontend.export_c.ParseResultD}
    (h3 : frontend.export_c.parse_source sinst emptyTier st2 srcC = ok (.Ok rC, st3, srcC'))
    (h3S : frontend.export_c.parse_source sinst emptyTier st3 srcS = ok (.Ok rS, st4, srcS'))
    {preC : frontend.prepare.PreludeIx}
    (hdup : frontend.prepare.prelude_ix_dup pre = ok preC)
    {prepS : frontend.prepare.Prepared}
    (h4S : frontend.prepare.prepare_d frontend.nat_op_ground.DeclUsedConsts.Insts.Con_ron_coreFrontendNat_op_groundUsedConsts emptyTier st4 pre rS.decls () = ok (.Ok prepS, st5))
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode_embedded = ok (.Ok pins))
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
    ∃ rC, parseChunks [bC] = .ok rC ∧ ∃ model, IsModel V model (· ∈ constantsOf rC.decls.toList) := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  have hk : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel := ConRon.Bridge.CoreSpec.of_core
  have hind : ConRon.Bridge.IndSpec := ConRon.Bridge.Inductives.indSpec_of_bridge
  obtain ⟨_, hdec⟩ := decode_of_decode_embedded hpins
  obtain ⟨sA, sB, sC, sC', sD, sE, sF, sG, sH, sI, rvC, rvS, IS, IC, hA, hB, hC, hCS, hD, hE,
      hF, hG, hH, hI, -⟩ :=
    rust_stages_compare hdec rfl hest hst0 h1 h2 hreadsC hreadsS h3 h3S hdup
      (prepare_prelude_of_prepare_d h4S) h5 (poolAccepts_intro h6S h7S h8S)
      (prepare_prelude_of_prepare_d h4) hside hsol (poolAcceptsSol_intro h6 h7 h8)
  obtain ⟨r, hr, hm⟩ := ConRon.Bridge.stagesC_isModel V hk hind hA hB hC hCS hD hE hF hG hH hI
  exact ⟨r, ConLeche.Frontend.parseChunks_single_of_concat hbC hr, hm⟩

/-- con-leche: ConLeche/MainTheorem.lean:77 main_oleans — **an accepted module's closure has a
model**, con-leche's conclusion at the binary's calls on `--olean` (`model_exists_oleans`'s
premises, the pins the embedded ones): every constant of the private views of the closure of the
roots, read by the specification through the search path `dirs` (`closureConstants`), is in a
model, in every set theory.  (con-leche's `searchPathOf dirs` and `parseModName root` are the
driver's argument strings, lane D's: here the search path and the roots are the Rust's own.)

`rust_stages_oleans` (Theorem 2), `stagesO_isModel` (Theorem 1 + `oleans_isModel`'s proof at the
pure accept, the reader's cover of the closure from `readOleans_run`). -/
theorem oleans_model_of_stages (V : Type w) [ConLeche.SetTheory V] {F : ConLeche.FS}
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
    (h8 : ParallelAll prepared.decls.length (oleanWorkerInit st6.pins)
      (oleanJobStep finst fsv tier .Verified ipins prepared.decls rd.pins rd.values ⟨dirs, alloc.vec.Vec.new _⟩)) :
    ∃ model, IsModel V model
      (closureConstants (absSearchPath dirs) F (names.map ConRon.Refine.absName).toArray) := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  have hk : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel := ConRon.Bridge.CoreSpec.of_core
  have hind : ConRon.Bridge.IndSpec := ConRon.Bridge.Inductives.indSpec_of_bridge
  obtain ⟨_, hdec⟩ := decode_of_decode_embedded hpins
  obtain ⟨sA, sB, sB', sC, sD, sE, sF, rd', I, hA, hB, hR, hC, hD, hE, hF, -⟩ :=
    rust_stages_oleans read_oleans_refines hdec rfl hest hst0 h1 h2 hroots hsnap h3 h4 h5
      (oleanPoolAccepts_intro h6 h7 h8)
  exact ConRon.Bridge.stagesO_isModel V hk hind (pins := ConRon.Refine.absPins pins)
    hA hB hR hC hD hE hF

/-- con-leche: ConLeche/MainTheorem.lean:88 main_compare_model — **an accepted comparison's
challenge closure has a model**, con-leche's conclusion at the binary's calls on `--olean
--compare -- C S` (`model_exists_oleans_compare`'s premises, the pins the embedded ones, and the
challenge's lookup the search path `dirs` with no fallback, as the driver's `chalRoots` builds
it): on every snapshot `fs'` that agrees with the run's under `dirs`, the constants of the
closure of `C` read through `dirs` have a model.  (con-leche's `trustedOr (searchPathOf T)
(searchPathOf D)` is the driver's, lane D's.)

`rust_stages_oleans_compare` (Theorem 2), `stagesOC_isModel` (Theorem 1 + `compare_isModel`'s
proof at the pure solution accept and the mixed challenge run). -/
theorem compare_model_of_stages (V : Type w) [ConLeche.SetTheory V] {F : ConLeche.FS}
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
    {dirs : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {sr : frontend.olean.files.Roots} {rootsC rootsS : alloc.vec.Vec arena.handle.NIdx}
    (hrC : rootsC.val = [ch]) (hrS : rootsS.val = [sh])
    {rdC rdS : frontend.olean.records.OleanRead} {store3 store5 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store ⟨dirs, alloc.vec.Vec.new _⟩ rootsC none true true
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
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode_embedded = ok (.Ok pins))
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
      (oleanJobStepSol finst fsv tierC .Verified ipins recsC rdC.pins rdC.values ⟨dirs, alloc.vec.Vec.new _⟩
        (some sol))) :
    ∀ fs', FS.AgreeUnder (absSearchPath dirs) F fs' →
      ∃ model, IsModel V model
        (closureConstants (absSearchPath dirs) fs' #[ConRon.Refine.absName c]) := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  have hk : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel := ConRon.Bridge.CoreSpec.of_core
  have hind : ConRon.Bridge.IndSpec := ConRon.Bridge.Inductives.indSpec_of_bridge
  obtain ⟨_, hdec⟩ := decode_of_decode_embedded hpins
  obtain ⟨sA, sB, sB₁, sB₂, sC, sD, sD', sC₂, sD₂, sE, sF, sH, sI, rdC', rdS', IS, IC, hA, hB,
      hRC, hRS, hC, hD, hH, hCS, hDS, hE, hF, hSd, hI, -⟩ :=
    rust_stages_oleans_compare read_oleans_refines hdec rfl hest hst0 h1 h2 hwfC hwfS hnC hnS
      hsnap hrC hrS h3 hdup h4 hhole h3S h4S h5 (oleanPoolAccepts_intro h6S h7S h8S) hside hsol
      (oleanPoolAcceptsSol_intro h6 h7 h8)
  exact ConRon.Bridge.stagesOC_isModel V hk hind (crp := absSearchPath dirs) rfl
    (pins := ConRon.Refine.absPins pins) hA hB hRC hRS hC hD hH hCS hDS hE hF hSd hI

end ConRon.MainTheorem

import ConRon.Bridge.Frontend.Capstone
import ConRon.Refine2.Checker.Top
import ConRon.Refine2.Frontend.Top
import ConRon.Refine2.Frontend.Prepare
import ConRon.Refine2.Checker.Pins
import ConRon.Refine2.Checker.Init
import ConRon.Refine2.Checker.PinsWF
import ConRon.Refine2.Checker.Phased
import ConRon.Bridge.Checker.Phased
import ConRon.Refine2.Frontend.Source
import ConRon.Bridge.Inductives.Decl
import ConLeche.MainTheorem
import ConRon.Bridge.Checker.Pins
import ConRon.Bridge.Frontend.Prepare
import ConRon.Bridge.Frontend.Olean.Records
import ConRon.Refine2.Frontend.Olean.ReadOleans

/-!
# `ConRon.Capstone` — THE COMPOSITION: Theorem 2 ∘ Theorem 1 ∘ con-leche

DESIGN.md §8.2's last line: *"Capstones for the binary = Theorem 2 ∘
Theorem 1 ∘ con-leche."*  This is the one module that imports both
`ConRon.Bridge` (Theorem 1, (B) ⇒ (A)) and `ConRon.Refine2` (Theorem 2,
(C) ⇒ (B)), and it states the binary's two headline theorems in the shape
the original campaign used (`conron.model_exists` /
`conron.no_False_declaration`, `proof/ConRon/RefineOld/Main.lean`):

* `ConRon.Capstone.model_exists` — every environment the Aeneas model of the
  Rust pipeline accepts has a model in every set theory;
* `ConRon.Capstone.no_False_declaration` — a file that declares a theorem of
  type `False` is never accepted by it.

**They are the campaign's root theorems** (task #97-COMPOSE): the sorry
frontier is measured as the dependency closure of these two, and it is
EMPTY since `arena` `db1131f1` (task #97-MILESTONE): both depend on
`[propext, Classical.choice, Quot.sound]` only (§5's census).  What they
still assume is exactly their premises, listed below.

## The pipeline, stage by stage

The binary (`crates/con-ron/src/bin/con-ron.rs`) is an unverified driver
around six extracted core functions and the pin decoder, in this order, on
one `AState` made from `EStore::empty()` and one `PersTier::empty()`:

    intern_reserved_pins → builtin_prelude_e → parse_source
      → prepare_prelude → (decode) → intern_all_pins → (the declaration fold)

The headlines (§4) take one premise per call, from the binary's own start
values `startState`/`emptyTier` (§3); §4's table maps each premise to its line
of `check_main`.

and the twin runs the same six stages (`Arena/Main.lean`'s
`runPipelineHead`/`runPipelineTail` drive them for `con-ron-lean`).  **The sixth stage is the fold the
binary's driver runs, pool and all** (task #97-P5-POOL):
`driver::check_decls_driver` runs phase A with the heartbeat as its hook,
freezes the tier, runs phase B on `pool::parallel_all`, and thaws the tier.
The headlines take one premise per step (`h6` phase A, `hord` the jobs' order, `h7` the
freeze, `hlayer` the value checks' layer, `h8` phase B), which `poolAccepts_intro` assembles
into `Refine2/Checker/Phased.lean`'s `PoolAccepts`.  Phase B's premise `h8` is the contract
of the generic combinator `pool::parallel_all` with the driver's two verified closures
(`ParallelAll` at `jobStep`): index lists, one per worker, covering every job, and for each
a fold of `run_job` over its indices from `worker_state`, accepting.  That contract is the
pool's trusted claim (OVERVIEW §8.2): control flow of `pool.rs`, nothing about the checker.
The theorems hold for EVERY install hook, so they cover the plain run and
`--progress` alike.  `pool_accepts_refines` relates the stage to the twin's
`Arena.PooledAccepts`, and `Bridge/Checker/Phased.lean`'s
`Arena.pooledAccepts_bridge` carries that to the pure fold.  So the
statement takes the six Rust RUNS as premises (that the binary's
`check_main` makes exactly these calls, in this order, is the one trusted
line, exactly as it was for the original campaign), and the proof is:

1. **Theorem 2, per stage** — `Refine2`'s six `…_refines` lemmas walk the
   Rust runs into six TWIN runs from the twin's own start state
   `AState.init EStore.empty`, related at every step (`AStateRel₀`/
   `AStateInv`: lockstep);
2. **Theorem 1** — the twin runs feed `Arena.pooledAccepts_bridge`, whose
   pure fold accepts the denoted stream: con-leche's
   `checkDeclsPure_sound_of` gives the model, and
   `no_False_theorem_accepted_pure` refutes a `False` theorem in the stream
   (`stages_no_False`, through the pure fold);
3. **con-leche** — `checkDeclsPure_sound_of` turns the pure accept into a
   model.

Every step is an existing theorem; what this file adds is glue: the Rust
runs threaded through `Sim₀`/`SimStream`/`SimFold`, and the one twin-store
fact the composition needs from Theorem 1 — `StoreWF` at the headline's
`AStateRel` (`stages_storeWF`) — read off its stage lemmas.  Theorem 2 itself
carries no fact about the twin's store (task #97-T2-AUDIT).

## The named hypotheses

Since task #98-HEADLINE the headlines start from the binary's own start
values (`startState` = `AState::empty()`, `emptyTier` = `PersTier::empty()`)
instead of quantifying over a start state with `hpers`/`hest`/`hst0`
equations, name the call the binary makes at each step (`prepare_d`, not
`prepare_prelude`).  Beside `[ConLeche.SetTheory V]`, the file's shape
`hfalse` and the one premise per call (`h1`…`h5`, `hpins`, `h6`…`h8`, `hord`, `hlayer`), what
they assume is exactly:

* `hreads : ReadsAs sinst src chunks.val` — the reads are the chunks
  (task #97-P5-Driver): the binary parses with the verified reader loop
  `parse_source` over the driver's file handle, and
  `Refine2/Frontend/Source.lean`'s `parse_source_eq` makes that
  `parse_chunks` over the chunks the handle hands out; that the handle hands
  out the file's bytes, in order, is the input seam — the one seam left.

Former hypotheses, now theorems or gone (DESIGN.md's task #97-COMPOSE and
#98-HEADLINE sections tag each with its owning lane):

* ~~`InitRel`~~ — the Rust start state is related to the twin's: a theorem
  since task #97-P5-Top (`Refine2/Checker/Init.lean`'s `init_rel`);
* ~~`hk : CoreSpec Arena.checkFuel`~~ — Theorem 1's Core tier
  spec: a theorem since task #97-P3-Core round 6
  (`Bridge/Checker/Hyp.lean`'s `CoreSpec.of_core`);
* ~~`hind : IndSpec`~~ — Theorem 1's inductive tier spec:
  `Bridge/Inductives/Decl.lean`'s `indSpec_of_bridge` since task #97-P3-Ind
  round 8 (the stage lemmas below still take it as a parameter);
* ~~`hbytes`~~ — the prelude's bytes are con-leche's: not needed since task
  #98-HEADLINE.  con-leche's `preparePrelude` puts the prelude's records into
  the checked stream, so soundness holds whatever the prelude parses to
  (`Bridge/Frontend/Prepare.lean`'s `builtinPreludeE_run` is parametric in
  the bytes).  The gate `scripts/gen-prelude-lean.sh --check` stays, as the
  claim that con-ron ships con-leche's prelude;
* ~~`hsc : ScanSpec`~~ — Theorem 2's scanner seam: a theorem since task
  #97-P5-Front (`Refine2/Frontend/Scan/Spec.lean`'s `scanSpec`);
* ~~`hpers`, `hest`, `hst0`~~ — the start state and tier were universally
  quantified with three equations; since task #98-HEADLINE they are the
  constants `startState`/`emptyTier` (`startState_eq`);
* `hdec` is now `hpins`, the premise for the binary's pin step: the pin list
  is what the verified decoder read, at any text (as con-leche's theorems
  hold at every pin list); `model_exists_embedded` /
  `no_False_declaration_embedded` fix the text to the embedded `PINS_TEXT`;
-/

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Capstone

set_option autoImplicit false

universe w

/-! ## 1. The twin side: the stages, from the driver's start state

Theorem 2 hands us the pipeline's stages one at a time, and the glue lemmas
below take Theorem 1's stage lemmas (`Bridge/Frontend/**`, `Bridge/Checker/**`)
step by step: the stages carry the frame facts Theorem 2 needs at
the fold's entry and the fold's start invariant Theorem 1 needs
(`stages_frame`), and the file's `False` theorem into the denoted stream
(`stages_false_mem`). -/

section Twin

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge ConRon.Bridge.Frontend

/-- con-leche: ConLeche/Verify/Cached/BridgeC.lean:609 checkDeclStepC_run —
**the stages' frame, up to the fold**: after the first five stages from the
driver's start state, the scratch tier is closed, the fold's start invariant
holds, and the pins
and the prepared stream denote. -/
theorem stages_frame {chunks : List ByteArray} {pins : List NatOpPinSet}
    {sA sB sC sD sE : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks chunks sB = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins sD = .ok (ipins, sE)) :
    sE.store.scratchOn = false ∧
      FoldOK Env.empty (mkIFEnv IEnv.empty) sE ∧
      PinsDenote sE.store ipins pins ∧ PersPinSets ipins ∧
      (∀ x ∈ ds.toList, PersDecl x) ∧
      ∃ dsP, denoteDecls sE.store ds.toList = some dsP := by
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  have hoff0 : (AState.init EStore.empty).store.scratchOn = false := rfl
  have hc0 : (AState.init EStore.empty).caches = Caches.empty := rfl
  obtain ⟨hokA, -, hpinsA, hppA, hoffA, -, hcachesA⟩ :=
    internReservedPins_run hok0 hoff0 hA
  obtain ⟨hstep1, hpersPre, preC, hrelPre⟩ :=
    builtinPreludeE_run hokA hoffA hpinsA hB
  obtain ⟨hstep2, hpersR, rc, -, hrelR⟩ :=
    parseChunks_run hstep1.ok
      (by rw [hstep1.scratch, hoffA]) (hpinsA.mono hstep1.ext hstep1.pins) hC
  obtain ⟨hstep3, hpersDs, hclPrep⟩ :=
    preparePrelude_run (preC := preC) hstep2.ok
      (by rw [hstep2.scratch, hstep1.scratch, hoffA])
      (hpinsA.mono (hstep1.trans hstep2).ext (hstep1.trans hstep2).pins)
      (denoteDeclArray_ext hstep2.ext hrelPre) hpersPre
      hrelR.decls hpersR hD
  have hoff3 : sD.store.scratchOn = false := by
    rw [hstep3.scratch, hstep2.scratch, hstep1.scratch]; exact hoffA
  obtain ⟨hokP, hxP, hpinsP, hppP, hipins, hpps, hoffP, hcachesP, -⟩ :=
    internAllPins_run hstep3.ok
      (hpinsA.mono ((hstep1.ext.trans hstep2.ext).trans hstep3.ext)
        (by rw [hstep3.pins, hstep2.pins, hstep1.pins]))
      (hppA.mono (by rw [hstep3.pins, hstep2.pins, hstep1.pins])) hoff3 hE
  refine ⟨hoffP, FoldOK_of_start hokP hpinsP hppP
      (((CacheOK.of_empty (s := sA) (by rw [hcachesA]; exact hc0)).monoF
            ((hstep1.ext.trans hstep2.ext).trans hstep3.ext)
            ((hstep1.cframe.trans hstep2.cframe).trans hstep3.cframe)).mono
        hxP hcachesP),
    hipins, hpps, fun x hx => hpersDs x (by simpa using hx), _,
    denoteDeclArray_iff.mp (denoteDeclArray_ext hxP hclPrep)⟩

/-- con-leche: ConLeche/Model/Fold.lean:254 checkDeclsPure_sound_of — **the
model at (B), at the pipeline**: the binary runs the
two-phase fold with a pool in phase B, after `internAllPins`, as its driver
does (`Arena.PooledAccepts`, task #97-P5-POOL).  `stages_frame`, then
`Arena.pooledAccepts_bridge`, then con-leche.  The environment denotes in the
phase-A state, which the Rust's thawed store is related to. -/
theorem stages_model (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    {chunks : List ByteArray} {pins : List NatOpPinSet}
    {sA sB sC sD sE sF : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet} {fe' : IFEnv}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks chunks sB = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins sD = .ok (ipins, sE))
    (hF : Arena.PooledAccepts .verified ipins ds sE fe' sF) :
    ∃ env', denoteFEnv sF.store fe' = some env' ∧
      Nonempty (ConLeche.Model.EnvModelM V env') := by
  obtain ⟨-, hfold, hipins, hpps, hpd, dsP, hden⟩ :=
    stages_frame hA hB hC hD hE
  obtain ⟨env', F', hdenF, hpure⟩ :=
    Arena.pooledAccepts_bridge hk hind hpps hfold hipins hpd hden hF
  exact ⟨env', hdenF,
    ConLeche.Model.checkDeclsPure_sound_of (V := V) (pins := pins) hpure⟩

/-- con-leche: ConLeche/MainTheorem.lean:110 no_False_declaration — **the
stages' stream carries the file's `False` theorem**: after the first five
stages, the prepared stream denotes, and a file that declares a theorem of
type `False` puts one in the denoted stream.  `stages_frame`'s steps with the
pure parse kept (`parseChunks_run`'s fourth conjunct), then con-leche's
`parseChunks_jsonWithTheoremFalse` and `mem_preparePrelude`, stopped before
the fold. -/
theorem stages_false_mem {chunks : List ByteArray} {pins : List NatOpPinSet}
    (hfalse : ConLeche.jsonWithTheoremFalse chunks)
    {sA sB sC sD sE : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks chunks sB = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins sD = .ok (ipins, sE)) :
    ∃ dsP cv vl, denoteDecls sE.store ds.toList = some dsP ∧
      cv.type = .const ConLeche.falseName [] ∧ Declaration.thmDecl cv vl ∈ dsP := by
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  have hoff0 : (AState.init EStore.empty).store.scratchOn = false := rfl
  obtain ⟨hokA, -, hpinsA, hppA, hoffA, -, -⟩ :=
    internReservedPins_run hok0 hoff0 hA
  obtain ⟨hstep1, hpersPre, preC, hrelPre⟩ :=
    builtinPreludeE_run hokA hoffA hpinsA hB
  obtain ⟨hstep2, hpersR, rc, hclR, hrelR⟩ :=
    parseChunks_run hstep1.ok
      (by rw [hstep1.scratch, hoffA]) (hpinsA.mono hstep1.ext hstep1.pins) hC
  obtain ⟨hstep3, -, hclPrep⟩ :=
    preparePrelude_run (preC := preC) hstep2.ok
      (by rw [hstep2.scratch, hstep1.scratch, hoffA])
      (hpinsA.mono (hstep1.trans hstep2).ext (hstep1.trans hstep2).pins)
      (denoteDeclArray_ext hstep2.ext hrelPre) hpersPre
      hrelR.decls hpersR hD
  have hoff3 : sD.store.scratchOn = false := by
    rw [hstep3.scratch, hstep2.scratch, hstep1.scratch]; exact hoffA
  obtain ⟨-, hxP, -⟩ :=
    internAllPins_run hstep3.ok
      (hpinsA.mono ((hstep1.ext.trans hstep2.ext).trans hstep3.ext)
        (by rw [hstep3.pins, hstep2.pins, hstep1.pins]))
      (hppA.mono (by rw [hstep3.pins, hstep2.pins, hstep1.pins])) hoff3 hE
  obtain ⟨cv, vl, hty, hmem⟩ :=
    ConLeche.Frontend.parseChunks_jsonWithTheoremFalse hfalse hclR
  exact ⟨_, cv, vl, denoteDeclArray_iff.mp (denoteDeclArray_ext hxP hclPrep), hty,
    by simpa using ConLeche.Frontend.mem_preparePrelude (pre := preC) hmem⟩

/-- con-leche: ConLeche/MainTheorem.lean:110 no_False_declaration — **a pooled
accept of a file declaring a `False` theorem is impossible, at (B)**:
`stages_frame` and `stages_false_mem`, then `Arena.pooledAccepts_bridge` (the
pure fold accepts the stream), then `no_False_theorem_accepted_pure` — through
the pure fold, because the pooled phase B is not one twin walk (task
#97-P5-POOL). -/
theorem stages_no_False (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    {chunks : List ByteArray} {pins : List NatOpPinSet}
    (hfalse : ConLeche.jsonWithTheoremFalse chunks)
    {sA sB sC sD sE sF : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet} {fe' : IFEnv}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks chunks sB = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins sD = .ok (ipins, sE))
    (hF : Arena.PooledAccepts .verified ipins ds sE fe' sF) :
    False := by
  obtain ⟨-, hfold, hipins, hpps, hpd, dsP, hden⟩ :=
    stages_frame hA hB hC hD hE
  obtain ⟨dsP', cv, vl, hden', hty, hmem⟩ :=
    stages_false_mem (pins := pins) hfalse hA hB hC hD hE
  rw [hden] at hden'
  cases hden'
  obtain ⟨env', F', -, hpure⟩ :=
    Arena.pooledAccepts_bridge hk hind hpps hfold hipins hpd hden hF
  exact ConRon.Bridge.Frontend.no_False_theorem_accepted_pure V hmem hty hpure

/-- con-leche: none — **the fold's end state is well formed** (Theorem 1).
Theorem 2 is a lockstep refinement and its relation `AStateRel₀` carries no
fact about the twin's store (task #97-T2-AUDIT); the headline states the full
`AStateRel`, whose one extra clause, `StoreWF`, is Theorem 1's: phase A's frame
(`installFold_frame`), which reads no environment, and the pooled fold hands the
phase-A state back. -/
theorem stages_storeWF
    {chunks : List ByteArray} {pins : List NatOpPinSet}
    {sA sB sC sD sE sF : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet} {fe' : IFEnv}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hC : parseChunks chunks sB = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins sD = .ok (ipins, sE))
    (hF : Arena.PooledAccepts .verified ipins ds sE fe' sF) :
    StoreWF sF.store := by
  obtain ⟨-, hfold, hipins, hpps, hpd, dsP, hden⟩ :=
    stages_frame hA hB hC hD hE
  obtain ⟨n, pend, D, -, hA', -⟩ := hF
  obtain ⟨hR, -, -⟩ := installFold_frame ds.toList dsP _ _ sE sF
    ⟨hfold.check, hfold.persPins⟩ hpd hden hA'
  exact hR.bdy.check.state.wf

/-! ### The `.olean` path: the same stages, the parse replaced by the reader -/

/-- con-leche: ConLeche/Verify/Cached/BridgeC.lean:609 checkDeclStepC_run — **the frame up to the
fold**, whatever the parse was: `stages_frame`, its parse a premise. -/
theorem stages_frame_of {pins : List NatOpPinSet}
    {sA sB sC sD sE : AState} {pre : PreludeIx} {r : ParseResultD} {dsR : Array Declaration}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hstep2 : ParseStep sB sC) (hpersR : PersParseResult r)
    (hdenR : denoteDeclArray sC.store r.decls = some dsR)
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins sD = .ok (ipins, sE)) :
    sE.store.scratchOn = false ∧
      FoldOK Env.empty (mkIFEnv IEnv.empty) sE ∧
      PinsDenote sE.store ipins pins ∧ PersPinSets ipins ∧
      (∀ x ∈ ds.toList, PersDecl x) ∧
      ∃ preC : ConLeche.Frontend.PreludeIx, denoteDecls sE.store ds.toList
        = some (ConLeche.Frontend.preparePrelude preC dsR).toList := by
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  have hoff0 : (AState.init EStore.empty).store.scratchOn = false := rfl
  have hc0 : (AState.init EStore.empty).caches = Caches.empty := rfl
  obtain ⟨hokA, -, hpinsA, hppA, hoffA, -, hcachesA⟩ :=
    internReservedPins_run hok0 hoff0 hA
  obtain ⟨hstep1, hpersPre, preC, hrelPre⟩ :=
    builtinPreludeE_run hokA hoffA hpinsA hB
  obtain ⟨hstep3, hpersDs, hclPrep⟩ :=
    preparePrelude_run (preC := preC) hstep2.ok
      (by rw [hstep2.scratch, hstep1.scratch, hoffA])
      (hpinsA.mono (hstep1.trans hstep2).ext (hstep1.trans hstep2).pins)
      (denoteDeclArray_ext hstep2.ext hrelPre) hpersPre
      hdenR hpersR hD
  have hoff3 : sD.store.scratchOn = false := by
    rw [hstep3.scratch, hstep2.scratch, hstep1.scratch]; exact hoffA
  obtain ⟨hokP, hxP, hpinsP, hppP, hipins, hpps, hoffP, hcachesP, -⟩ :=
    internAllPins_run hstep3.ok
      (hpinsA.mono ((hstep1.ext.trans hstep2.ext).trans hstep3.ext)
        (by rw [hstep3.pins, hstep2.pins, hstep1.pins]))
      (hppA.mono (by rw [hstep3.pins, hstep2.pins, hstep1.pins])) hoff3 hE
  refine ⟨hoffP, FoldOK_of_start hokP hpinsP hppP
      (((CacheOK.of_empty (s := sA) (by rw [hcachesA]; exact hc0)).monoF
            ((hstep1.ext.trans hstep2.ext).trans hstep3.ext)
            ((hstep1.cframe.trans hstep2.cframe).trans hstep3.cframe)).mono
        hxP hcachesP),
    hipins, hpps, fun x hx => hpersDs x (by simpa using hx), preC,
    denoteDeclArray_iff.mp (denoteDeclArray_ext hxP hclPrep)⟩

/-- con-leche: none — the driver's names interned: the handles denote them. -/
theorem internNames_run {s : AState} (hok : StateOK s) (hoff : s.store.scratchOn = false) :
    ∀ (names : List ConLeche.Name) {hs : List NIdx} {s' : AState},
      names.mapM ConRon.Arena.internName s = .ok (hs, s') →
      ParseStep s s' ∧ ConRon.Bridge.Frontend.ListRel (ConRon.Bridge.Frontend.Olean.NR s'.store) hs names
  | [], hs, s', h => by
    simp only [List.mapM_nil] at h
    obtain ⟨hv, hsx⟩ := AM.pure_ok h
    cases hv
    subst hsx
    exact ⟨ParseStep.refl hok, .nil⟩
  | n :: ns, hs, s', h => by
    simp only [List.mapM_cons] at h
    obtain ⟨x, s₁, h1, h⟩ := AM.bind_ok h
    obtain ⟨hst1, hd⟩ := internName_sstep hok h1
    have hst1' := (hst1.toIStep hoff).toParse hoff
    obtain ⟨xs, s₂, h2, h⟩ := AM.bind_ok h
    obtain ⟨hv, hsx⟩ := AM.pure_ok h
    cases hv
    subst hsx
    obtain ⟨hst2, hr⟩ := internNames_run hst1'.ok (by rw [hst1'.scratch]; exact hoff) ns h2
    exact ⟨hst1'.trans hst2, .cons (denoteN_ext hd hst2.ext) hr⟩

/-- con-leche: ConLeche/MainTheorem.lean:163 main_oleans_no_False — **a pooled accept of a closure
that holds a `False` theorem is impossible, at (B)**: the twin's read on the snapshot,
`readOleans_run`, puts the theorem in the stream; `stages_frame_of` carries it to the fold;
the fold's accept is con-leche's, which refutes it. -/
theorem stagesO_no_False (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    {F : ConLeche.FS} {sp : ConLeche.Frontend.Olean.SearchPath} {names : List ConLeche.Name}
    {m : ConLeche.Name} {d : ConLeche.Frontend.Olean.ModDecoded}
    {c : ConLeche.Frontend.Olean.CEntryF ConLeche.Name Expr} {v : Expr} {all : List ConLeche.Name}
    (hcl : ConLeche.Frontend.Olean.InClosure sp F names.toArray m)
    (hv : ConLeche.Frontend.Olean.ViewOf sp F m d) (hmem : c ∈ d.constants)
    (hkind : c.kind = .thm v all) (hty : c.type = .const ConLeche.falseName [])
    {pins : List NatOpPinSet} {roots : List NIdx}
    {sA sB sB' sC sD sE sF : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet} {fe' : IFEnv}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hR : names.mapM ConRon.Arena.internName sB = .ok (roots, sB'))
    (hC : ConRon.Arena.Frontend.Olean.readOleans (ConRon.Bridge.Frontend.Olean.modelFs F) sp
      roots.toArray none sB' = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins sD = .ok (ipins, sE))
    (hF : Arena.PooledAccepts .verified ipins ds sE fe' sF) :
    False := by
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  have hoff0 : (AState.init EStore.empty).store.scratchOn = false := rfl
  obtain ⟨hokA, -, hpinsA, -, hoffA, -, -⟩ := internReservedPins_run hok0 hoff0 hA
  obtain ⟨hstep1, -, -, -⟩ := builtinPreludeE_run hokA hoffA hpinsA hB
  have hoffB : sB.store.scratchOn = false := by rw [hstep1.scratch]; exact hoffA
  obtain ⟨hstR, hnr⟩ := internNames_run hstep1.ok hoffB names hR
  obtain ⟨hstC, hpersR, dsR, hdenR, hthm⟩ := ConRon.Bridge.Frontend.Olean.readOleans_run
    (roots := roots.toArray) (rootsC := names.toArray) hstR.ok (by rw [hstR.scratch]; exact hoffB)
    (hpinsA.mono (hstep1.trans hstR).ext (hstep1.trans hstR).pins) (by simpa using hnr) hC
  obtain ⟨-, hfold, hipins, hpps, hpd, preC, hden⟩ :=
    stages_frame_of (pins := pins) hA hB (hstR.trans hstC) hpersR hdenR hD hE
  obtain ⟨env', F', -, hpure⟩ :=
    Arena.pooledAccepts_bridge hk hind hpps hfold hipins hpd hden hF
  obtain ⟨v', hd⟩ := hthm hcl hv hmem hkind
  have hm' := ConLeche.Frontend.mem_preparePrelude (pre := preC) hd
  exact ConRon.Bridge.Frontend.no_False_theorem_accepted_pure V (by simpa using hm') hty hpure

/-- con-leche: ConLeche/Model/Fold.lean:254 checkDeclsPure_sound_of — **the model at (B), on the
`.olean` path**. -/
theorem stagesO_model (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec)
    {F : ConLeche.FS} {sp : ConLeche.Frontend.Olean.SearchPath} {names : List ConLeche.Name}
    {pins : List NatOpPinSet} {roots : List NIdx}
    {sA sB sB' sC sD sE sF : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet} {fe' : IFEnv}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE sA = .ok (.ok pre, sB))
    (hR : names.mapM ConRon.Arena.internName sB = .ok (roots, sB'))
    (hC : ConRon.Arena.Frontend.Olean.readOleans (ConRon.Bridge.Frontend.Olean.modelFs F) sp
      roots.toArray none sB' = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins sD = .ok (ipins, sE))
    (hF : Arena.PooledAccepts .verified ipins ds sE fe' sF) :
    StoreWF sF.store ∧ ∃ env', denoteFEnv sF.store fe' = some env' ∧
      Nonempty (ConLeche.Model.EnvModelM V env') := by
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  have hoff0 : (AState.init EStore.empty).store.scratchOn = false := rfl
  obtain ⟨hokA, -, hpinsA, -, hoffA, -, -⟩ := internReservedPins_run hok0 hoff0 hA
  obtain ⟨hstep1, -, -, -⟩ := builtinPreludeE_run hokA hoffA hpinsA hB
  have hoffB : sB.store.scratchOn = false := by rw [hstep1.scratch]; exact hoffA
  obtain ⟨hstR, hnr⟩ := internNames_run hstep1.ok hoffB names hR
  obtain ⟨hstC, hpersR, dsR, hdenR, -⟩ := ConRon.Bridge.Frontend.Olean.readOleans_run
    (roots := roots.toArray) (rootsC := names.toArray) hstR.ok (by rw [hstR.scratch]; exact hoffB)
    (hpinsA.mono (hstep1.trans hstR).ext (hstep1.trans hstR).pins) (by simpa using hnr) hC
  obtain ⟨-, hfold, hipins, hpps, hpd, preC, hden⟩ :=
    stages_frame_of (pins := pins) hA hB (hstR.trans hstC) hpersR hdenR hD hE
  obtain ⟨env', F', hdenF, hpure⟩ :=
    Arena.pooledAccepts_bridge hk hind hpps hfold hipins hpd hden hF
  refine ⟨?_, env', hdenF, ConLeche.Model.checkDeclsPure_sound_of (V := V) (pins := pins) hpure⟩
  obtain ⟨n, pend, D, -, hA', -⟩ := hF
  obtain ⟨hR', -, -⟩ := installFold_frame ds.toList _ _ _ sE sF
    ⟨hfold.check, hfold.persPins⟩ hpd hden hA'
  exact hR'.bdy.check.state.wf

end Twin

/-! ## 2. The Rust side: the six stages, walked into the twin by Theorem 2 -/

section Rust

open ConRon.Refine2 ConRon.Refine2.Frontend

/-- **The Rust pipeline, walked into the twin.**  Six accepting Rust runs from
the driver's start state give six accepting twin runs from the twin's, at the
abstracted values, with the Rust's final state related to the twin's and the
Rust's environment related to the twin's.

Theorem 2's six top lemmas, one per stage, all lockstep (`AStateRel₀`, no
precondition on the twin: task #97-T2-LOCKSTEP lane Checker deleted `BrOK`
and ruling 2's `DeclResolves`). -/
theorem rust_stages
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    {text : Slice Std.U8}
    (hdec : kernel.pins_decode.decode text = ok (.Ok pins))
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    {pers : arena.store.PersTier} {est : arena.store.EStore}
    (hfz : pers.frozen = false) (hpe : PersEnvEmpty pers)
    {st0 st1 st2 st3 st4 st5 st6 : arena.monad.AState}
    {pre : frontend.prepare.PreludeIx} {r : frontend.export_c.ParseResultD}
    {ds : alloc.vec.Vec arena.env.IDeclaration}
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {fe : arena.env.IFEnv}
    (hest : arena.store.EStore.empty = ok est)
    (hst0 : arena.monad.AState.init est = ok st0)
    (h1 : arena.pins.intern_reserved_pins pers st0 = ok (.Ok (), st1))
    (h2 : frontend.prelude.builtin_prelude_e pers st1 = ok (.Ok pre, st2))
    {Sc : Type} {sinst : frontend.export_c.ChunkSource Sc} {src src' : Sc}
    (hreads : ReadsAs sinst src chunks.val)
    (h3 : frontend.export_c.parse_source sinst pers st2 src = ok (.Ok r, st3, src'))
    (h4 : frontend.prepare.prepare_prelude pers st3 pre r.decls = ok (.Ok ds, st4))
    (h5 : arena.checker.intern_all_pins pers st4 pins = ok (.Ok ipins, st5))
    {Hk : Type} {hinst : arena.checker.InstallHook Hk} {hook : Hk}
    (h6 : PoolAccepts hinst pers st5 .Verified ipins ds hook fe st6) :
    ∃ (sA sB sC sD sE sF : ConRon.Arena.AState)
      (rv : ConRon.Arena.Frontend.ParseResultD) (lfe : ConRon.Arena.IFEnv),
      ConRon.Arena.internReservedPins
          (ConRon.Arena.AState.init ConRon.Arena.EStore.empty) = .ok ((), sA) ∧
      ConRon.Arena.Frontend.builtinPreludeE sA = .ok (.ok (absPreludeIx pre), sB) ∧
      ConRon.Arena.Frontend.parseChunks (absChunks chunks) sB = .ok (.ok rv, sC) ∧
      ConRon.Arena.Frontend.preparePrelude (absPreludeIx pre) rv.decls sC
          = .ok ((absIDeclL ds).toArray, sD) ∧
      ConRon.Arena.internAllPins (ConRon.Refine.absPins pins) sD
          = .ok (absINatOpPinSetL ipins, sE) ∧
      ConRon.Arena.PooledAccepts .verified (absINatOpPinSetL ipins)
          (absIDeclL ds).toArray sE lfe sF ∧
      AStateRel₀ pers st6 sF ∧ IFEnvOwn fe lfe := by
  -- the reader is an owned store's (task #98-FREEZE): `hfz`
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
  -- 6. the fold, as the binary runs it, pool and all
  obtain ⟨lfe, sF, hF, hfe, hrelF⟩ := pool_accepts_refines (mode := .Verified) (ds := ds)
    (pins := ipins) hrelE hinvE hfz hpe h6
  exact ⟨sA, sB, sC, sD, sE, sF, rv, lfe, hA, hB, hC, hD', hE, hF, hrelF, hfe⟩

end Rust

/-! ## The `.olean` path at the Rust

The driver's calls on `--olean` are `rust_stages`'s, the stream's two replaced: the roots' names
interned one by one (`bin/con-ron.rs`, `olean_fs::read_request`), and `records::read_oleans` over
the store, at the instance `olean_fs::StdFs`. -/

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
    (hfz : pers.frozen = false) (hpe : PersEnvEmpty pers)
    {st0 st1 st2 st3 st4 st5 st6 : arena.monad.AState}
    {pre : frontend.prepare.PreludeIx} {r : frontend.export_c.ParseResultD}
    {ds : alloc.vec.Vec arena.env.IDeclaration}
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {fe : arena.env.IFEnv}
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
      = ok (.Ok r, store3))
    (hst3 : st3 = { stR with store := store3 })
    (h4 : frontend.prepare.prepare_prelude pers st3 pre r.decls = ok (.Ok ds, st4))
    (h5 : arena.checker.intern_all_pins pers st4 pins = ok (.Ok ipins, st5))
    {Hk : Type} {hinst : arena.checker.InstallHook Hk} {hook : Hk}
    (h6 : PoolAccepts hinst pers st5 .Verified ipins ds hook fe st6) :
    ∃ (sA sB sB' sC sD sE sF : ConRon.Arena.AState)
      (rv : ConRon.Arena.Frontend.ParseResultD) (lfe : ConRon.Arena.IFEnv),
      ConRon.Arena.internReservedPins
          (ConRon.Arena.AState.init ConRon.Arena.EStore.empty) = .ok ((), sA) ∧
      ConRon.Arena.Frontend.builtinPreludeE sA = .ok (.ok (absPreludeIx pre), sB) ∧
      (names.map ConRon.Refine.absName).mapM ConRon.Arena.internName sB
          = .ok (roots.val.map absNIdx, sB') ∧
      ConRon.Arena.Frontend.Olean.readOleans (ConRon.Bridge.Frontend.Olean.modelFs F)
          (absSearchPath dirs) (roots.val.map absNIdx).toArray none sB' = .ok (.ok rv, sC) ∧
      ConRon.Arena.Frontend.preparePrelude (absPreludeIx pre) rv.decls sC
          = .ok ((absIDeclL ds).toArray, sD) ∧
      ConRon.Arena.internAllPins (ConRon.Refine.absPins pins) sD
          = .ok (absINatOpPinSetL ipins, sE) ∧
      ConRon.Arena.PooledAccepts .verified (absINatOpPinSetL ipins)
          (absIDeclL ds).toArray sE lfe sF ∧
      AStateRel₀ pers st6 sF ∧ IFEnvOwn fe lfe := by
  subst hst3
  obtain ⟨hrel0, hinv0, -⟩ := init_rel (pers := pers) hfz hest hst0
  obtain ⟨sA, hA, hrelA, hinvA⟩ :=
    (intern_reserved_pins_refines hrel0 hinv0 h1).dest
  obtain ⟨preL, sB, hB, hpreL, hrelB, hinvB⟩ :=
    builtin_prelude_e_refines scanSpec hrelA hinvA h2
  subst hpreL
  obtain ⟨sB', hR, hrelR, hinvR⟩ := internRoots_refines names roots.val hroots hrelB hinvB
  obtain ⟨rv, sC, hC, hrv, hrelC, hinvC⟩ := hT2 (fsRel_of_snapshot hsnap) hrelR hinvR h3
  obtain ⟨sD, hD, hrelD, hinvD⟩ :=
    (prepare_prelude_refines hrelC hinvC h4).apply
  have hdecls : rv.decls = absIDeclArr r.decls := hrv.decls
  have hD' : ConRon.Arena.Frontend.preparePrelude (absPreludeIx pre) rv.decls sC
      = .ok ((absIDeclL ds).toArray, sD) := by
    rw [hdecls]; exact hD
  obtain ⟨sE, hE, hrelE, hinvE⟩ :=
    (intern_all_pins_refines hrelD hinvD
      (ConRon.Refine.PinsWF.decode_wf_refine2 hdec) h5).dest
  obtain ⟨lfe, sF, hF, hfe, hrelF⟩ := pool_accepts_refines (mode := .Verified) (ds := ds)
    (pins := ipins) hrelE hinvE hfz hpe h6
  exact ⟨sA, sB, sB', sC, sD, sE, sF, rv, lfe, hA, hB, hR, hC, hD', hE, hF, hrelF, hfe⟩

end RustOleans

/-! ## 3. The binary's start values, and what its environment denotes

`check_main` starts from `AState::empty()` (`bin/con-ron.rs:360`, which is
`AState::init(EStore::empty())`) and `&PersTier::empty()`
(`bin/con-ron.rs:370`).  The Aeneas model of each is a `Result` that is
`ok`; `startState` and `emptyTier` are those values, written out (task
#98-H8): every table and map empty, every flag down, no pins.  `startState_eq`
checks the first against the Aeneas model by unfolding it, for `startState_init`, which
the proof reads; `emptyTier` is read off `PersTier::empty` by eye.  So
the headlines' first premise starts from them rather than from universally
quantified states with equations about them. -/

section Defs

open ConRon.Refine2 ConRon.Refine2.Frontend

/-- `HashMap2::new()` (`ron/hashmap2.rs`): no entries, no slots, epoch 1. -/
def emptyMap (K V : Type) : ron.hashmap2.HashMap2 K V :=
  { num_entries := 0#usize, max_load := 0#usize, epoch := 1#u32, fit_hw := 0#usize,
    slots := alloc.vec.Vec.new _ }

/-- `Tbl::empty()` (`arena/store.rs`): no rows, an empty index. -/
def emptyTbl (A I D : Type) : arena.store.Tbl A I D :=
  { rows := alloc.vec.Vec.new _, cons := emptyMap A I }

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

/-- **The binary's persistent tier**, `&PersTier::empty()`
(`bin/con-ron.rs:370`): the tier every stage up to phase B is handed — not
frozen, its four table sets, every table empty, and the empty environment layer. -/
def emptyTier : arena.store.PersTier :=
  { frozen := false, n := emptyNTables, l := emptyLTables, ls := emptyLsTables,
    e := emptyETables, env := layer00 }

/-- **The binary's start state**, `AState::empty()` (`bin/con-ron.rs:360`),
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
    arena.store.EStore.empty, ron.hashmap2.HashMap2.new,
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

/-- **What the Rust's environment denotes**: the Rust's final state `st` and
environment `fe`, read through the twin, denote the con-leche environment
`env`.  Theorem 2 relates the Rust state to a twin state (`AStateRel`, at
the binary's `emptyTier`) and the Rust environment to a twin environment
(`IFEnvOwn`, what phase A hands the driver: an index of its own, with no frozen base),
and Theorem 1's `denoteFEnv` reads that twin environment in
that twin store.  (The arena has no abstraction FUNCTION from the Rust's
store to con-leche's `Env` — the store is abstracted by a relation — so the
Rust environment's meaning can only be spelled through the twin.) -/
def RustDenotes (fe : arena.env.IFEnv) (st : arena.monad.AState)
    (env : ConLeche.Env) : Prop :=
  ∃ (lst : ConRon.Arena.AState) (lfe : ConRon.Arena.IFEnv),
    AStateRel emptyTier st lst ∧ IFEnvOwn fe lfe ∧
    ConRon.Bridge.denoteFEnv lst.store lfe = some env

/-- `prepare::prepare_d`, the call the binary makes (`bin/con-ron.rs:454`),
is `prepare_prelude`'s body: `prepare_prelude` is its `.decls`. -/
theorem prepare_prelude_of_prepare_d {pers : arena.store.PersTier}
    {st st' : arena.monad.AState} {pre : frontend.prepare.PreludeIx}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {p : frontend.prepare.Prepared}
    (h : frontend.prepare.prepare_d pers st pre ds = ok (.Ok p, st')) :
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

/-! ## 4. The two headline theorems

Both take one premise per call the binary's `check_main` makes, in its order,
each starting from the state the previous one left and the first from the
binary's own start values.  `check_main` itself is not verified: a reader
walks through it and finds each verified call as one premise.

| premise | `check_main`'s call |
|---|---|
| `startState`, `emptyTier` | `bin/con-ron.rs:360` `AState::empty()`, `:370` `&PersTier::empty()` |
| `h1` | `bin/con-ron.rs:379` `arena::pins::intern_reserved_pins` |
| `h2` | `bin/con-ron.rs:392` `prelude::builtin_prelude_e` |
| `hreads`, `h3` | `bin/con-ron.rs:415` `driver::parse_export_stream_d`, which is `driver.rs:991`'s `export_c::parse_source` over the file's handle |
| `h4` | `bin/con-ron.rs:454` `prepare::prepare_d` |
| `hpins` | `bin/con-ron.rs:474` `driver::pins_for_run`, whose default is `driver.rs:299` `pins_decode::decode_embedded()`, which is `decode` of the embedded `PINS_TEXT` (the `_embedded` corollaries below name it) |
| `h5` | `bin/con-ron.rs:500` `checker::intern_all_pins` |
| `h6` | `bin/con-ron.rs:517`/`:520` `driver::check_decls_driver` at `CheckMode::Verified` (`:353`), phase A: `driver.rs:594` `checker::install_fold_hooked(…, checker::fold_start(), ds, 0, obs)` |
| `hord` | the same: `driver.rs:603` `checker::job_order` |
| `h7` | the same, the boundary: `driver.rs:612` `checker::freeze_tier` |
| `hlayer` | the same: `driver.rs:613` `checker::check_layer` |
| `h8` | the same, phase B: `driver.rs:620` `pool::parallel_all` with `init` `checker::worker_state` and `step` `checker::run_job` on `order[k]` (`thaw_tier` at `:637` restores the store) |

`h8` is not one equation: `parallel_all` is not extracted, so `h8` states its contract
(the pool's trusted claim, `pool.rs`'s note, OVERVIEW §8.2) at the driver's two verified
closures, `Refine2/Checker/Phased.lean`'s `ParallelAll` at `jobStep`: some lists of job
indices, one per worker, together covering every index below `order.length`, and for
each list the worker's run, `worker_state st6.pins` and then `run_job` on each `order[k]`
in order, every step answering `Ok(())`.  Nothing more is asked of the lists than
coverage: not that a job is claimed once, nor in increasing order.  Each job is a fact
about the phase-A state's worker, whatever else its worker ran (`Bridge/Checker/Frame.lean`).

The theorems hold at every install hook (the heartbeat or
`driver::Silent`), every chunk source whose reads are `chunks`, and every pin
text `hpins` decodes, as
con-leche's hold at every pin list.  **`--pins FILE`** (read by the
unverified `con_ron_dump::parse_pins`) and **`--no-pins`** do not call the
decoder, so runs with them are outside the theorems.

`hpins` is stated about `decode` of a free text rather than about
`decode_embedded` because naming the embedded constant `PINS_TEXT` costs the
census one axiom, `kernel.pins_text.PINS_TEXT._native.decide.ax_1` — the one
Aeneas's `toStr` spends on that constant's DEFINITION (AENEAS_FINDINGS.md
§3.8; `Refine2/Checker/PinsWF.lean`'s census), nothing this proof evaluates.
`model_exists_embedded` / `no_False_declaration_embedded` are the headlines
with `decode_embedded` itself in the premise, and carry that axiom.

**`--olean`.**  `no_False_oleans` and `model_exists_oleans` take the same calls with the
stream's two replaced, as `Input::Oleans` runs them (`olean_fs::read_request`):

| premise | the binary's call |
|---|---|
| `hroots` | `olean_fs::OleanRequest::intern`: `monad::intern_name` on each root |
| `hsnap`, `h3` | `records::read_oleans` at `olean_fs::StdFs`, whose answers are one snapshot's |

`h4` starts from the state `hroots` left with the store `h3` left: the reader takes the store
alone.  `hcl`, `hv`, `hmem`, `hk`, `hty` are upstream's, by the specification (`InClosure`, `ViewOf`:
`decodeModuleSpec`).  `--constant` is outside them, as a run from `constants = none`.  Each is its `_of` form, which
takes Theorem 2 at the reader as `hT2 : ReadOleansRefines` (`Refine2/Frontend/Olean/Contract.lean`),
at `read_oleans_refines`. -/

section Headline

open ConRon.Refine2 ConRon.Refine2.Frontend

/-- con-leche: ConLeche/MainTheorem.lean:96 model_exists —
**THE MAIN THEOREM FOR THE RUST CHECKER** (DESIGN.md §1, §8.2): every
environment the Rust checker accepts has a model, in every set theory.

con-leche's reads `(accepted : checkDecls .verified pins ds = .ok env) :
Nonempty (Model V env)`; here the accepting run is the binary's calls, one
premise each (§4's table), and the environment is the one the Rust's `fe`
denotes (`RustDenotes`).  One premise is a seam by design: `hreads` (the
chunk source hands out `chunks`).

Composition only: `rust_stages` (Theorem 2), `stages_model` (Theorem 1 +
con-leche), `stages_storeWF`. -/
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
    (h4 : frontend.prepare.prepare_d emptyTier st3 pre r.decls = ok (.Ok prepared, st4))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins = ok (.Ok ipins, st5))
    {Hk : Type} {hinst : arena.checker.InstallHook Hk} {hook : Hk}
    {n : Std.U64} {fe : arena.env.IFEnv} {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {blocks : alloc.vec.Vec arena.checker.BlockCheck}
    (h6 : (do
        let t ← arena.checker.fold_start
        arena.checker.install_fold_hooked hinst emptyTier st5 .Verified ipins t
          prepared.decls 0#usize hook)
      = ok (.Ok (n, fe, pend, blocks), st6))
    {order : alloc.vec.Vec (Bool × Std.U64)}
    (hord : arena.checker.job_order pend blocks = ok order)
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store fe = ok (tier, frozen))
    {layer : arena.env.IFEnv}
    (hlayer : arena.checker.check_layer = ok layer)
    (h8 : ParallelAll order.length (arena.checker.worker_state st6.pins)
      (jobStep tier .Verified layer pend blocks order)) :
    ∃ env, RustDenotes fe st6 env ∧ Nonempty (ConLeche.Model V env) := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  -- Theorem 1's two tier specs, discharged (tasks #97-P3-Core, #97-P3-Ind)
  have hk : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel :=
    ConRon.Bridge.CoreSpec.of_core
  have hind : ConRon.Bridge.IndSpec :=
    ConRon.Bridge.Inductives.indSpec_of_bridge hk
  obtain ⟨sA, sB, sC, sD, sE, sF, rv, lfe, hA, hB, hC, hD, hE, hF, hrelF, hfe⟩ :=
    rust_stages hpins rfl (persEnvEmpty_of_eq rfl) hest hst0 h1 h2
      hreads h3 (prepare_prelude_of_prepare_d h4) h5 (poolAccepts_intro h6 hord h7 hlayer h8)
  obtain ⟨env, hden, ⟨hmod⟩⟩ := stages_model V hk hind hA hB hC hD hE hF
  -- the relation's `StoreWF` clause is Theorem 1's (Theorem 2 is lockstep)
  have hwfF := stages_storeWF hA hB hC hD hE hF
  exact ⟨env, ⟨sF, lfe, hrelF.of₀ hwfF, hfe, hden⟩,
    ⟨ConLeche.Model.Model.ofEnvModelM hmod⟩⟩

/-- con-leche: ConLeche/MainTheorem.lean:110 no_False_declaration — **A FILE
THAT DECLARES A THEOREM OF TYPE `False` IS REJECTED BY THE RUST CHECKER**:
the binary's calls (§4's table) cannot all succeed on it.

con-leche's concludes `∃ e, (do …; checkDecls .verified pins ds) = .error e`
about its own pipeline; the binary's is not one function (the pool is a
contract, `h8`), so the letter here has the same premises as `model_exists` and
concludes `False`.

Composition only: `rust_stages` (Theorem 2) turns the Rust runs into twin
runs, the last the pooled fold; `stages_no_False` (Theorem 1) turns that into
the pure fold's accept of a stream holding the file's `False` theorem, which
con-leche's `no_proof_of_False_pure` refutes
(`no_False_theorem_accepted_pure`). -/
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
    (h4 : frontend.prepare.prepare_d emptyTier st3 pre r.decls = ok (.Ok prepared, st4))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins = ok (.Ok ipins, st5))
    {Hk : Type} {hinst : arena.checker.InstallHook Hk} {hook : Hk}
    {n : Std.U64} {fe : arena.env.IFEnv} {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {blocks : alloc.vec.Vec arena.checker.BlockCheck}
    (h6 : (do
        let t ← arena.checker.fold_start
        arena.checker.install_fold_hooked hinst emptyTier st5 .Verified ipins t
          prepared.decls 0#usize hook)
      = ok (.Ok (n, fe, pend, blocks), st6))
    {order : alloc.vec.Vec (Bool × Std.U64)}
    (hord : arena.checker.job_order pend blocks = ok order)
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store fe = ok (tier, frozen))
    {layer : arena.env.IFEnv}
    (hlayer : arena.checker.check_layer = ok layer)
    (h8 : ParallelAll order.length (arena.checker.worker_state st6.pins)
      (jobStep tier .Verified layer pend blocks order)) :
    False := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  have hk : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel :=
    ConRon.Bridge.CoreSpec.of_core
  have hind : ConRon.Bridge.IndSpec :=
    ConRon.Bridge.Inductives.indSpec_of_bridge hk
  obtain ⟨sA, sB, sC, sD, sE, sF, rv, lfe, hA, hB, hC, hD, hE, hF, -, -⟩ :=
    rust_stages hpins rfl (persEnvEmpty_of_eq rfl) hest hst0 h1 h2
      hreads h3 (prepare_prelude_of_prepare_d h4) h5 (poolAccepts_intro h6 hord h7 hlayer h8)
  exact stages_no_False V hk hind (pins := ConRon.Refine.absPins pins) hfalse
    hA hB hC hD hE hF

/-- `model_exists` with the pin premise the binary's own call,
`pins_decode::decode_embedded()` (`driver.rs:299`).  Its census adds
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
    (h4 : frontend.prepare.prepare_d emptyTier st3 pre r.decls = ok (.Ok prepared, st4))
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode_embedded = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins = ok (.Ok ipins, st5))
    {Hk : Type} {hinst : arena.checker.InstallHook Hk} {hook : Hk}
    {n : Std.U64} {fe : arena.env.IFEnv} {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {blocks : alloc.vec.Vec arena.checker.BlockCheck}
    (h6 : (do
        let t ← arena.checker.fold_start
        arena.checker.install_fold_hooked hinst emptyTier st5 .Verified ipins t
          prepared.decls 0#usize hook)
      = ok (.Ok (n, fe, pend, blocks), st6))
    {order : alloc.vec.Vec (Bool × Std.U64)}
    (hord : arena.checker.job_order pend blocks = ok order)
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store fe = ok (tier, frozen))
    {layer : arena.env.IFEnv}
    (hlayer : arena.checker.check_layer = ok layer)
    (h8 : ParallelAll order.length (arena.checker.worker_state st6.pins)
      (jobStep tier .Verified layer pend blocks order)) :
    ∃ env, RustDenotes fe st6 env ∧ Nonempty (ConLeche.Model V env) :=
  have ⟨_, hdec⟩ := decode_of_decode_embedded hpins
  model_exists V h1 h2 hreads h3 h4 hdec h5 h6 hord h7 hlayer h8

/-- `no_False_declaration` with the pin premise the binary's own call,
`pins_decode::decode_embedded()` (`driver.rs:299`).  Its census adds
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
    (h4 : frontend.prepare.prepare_d emptyTier st3 pre r.decls = ok (.Ok prepared, st4))
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode_embedded = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins = ok (.Ok ipins, st5))
    {Hk : Type} {hinst : arena.checker.InstallHook Hk} {hook : Hk}
    {n : Std.U64} {fe : arena.env.IFEnv} {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {blocks : alloc.vec.Vec arena.checker.BlockCheck}
    (h6 : (do
        let t ← arena.checker.fold_start
        arena.checker.install_fold_hooked hinst emptyTier st5 .Verified ipins t
          prepared.decls 0#usize hook)
      = ok (.Ok (n, fe, pend, blocks), st6))
    {order : alloc.vec.Vec (Bool × Std.U64)}
    (hord : arena.checker.job_order pend blocks = ok order)
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store fe = ok (tier, frozen))
    {layer : arena.env.IFEnv}
    (hlayer : arena.checker.check_layer = ok layer)
    (h8 : ParallelAll order.length (arena.checker.worker_state st6.pins)
      (jobStep tier .Verified layer pend blocks order)) :
    False :=
  have ⟨_, hdec⟩ := decode_of_decode_embedded hpins
  no_False_declaration V hfalse h1 h2 hreads h3 h4 hdec h5 h6 hord h7 hlayer h8

/-- con-leche: ConLeche/MainTheorem.lean:163 main_oleans_no_False — **A CLOSURE THAT HOLDS A THEOREM
OF TYPE `False` IS REJECTED BY THE RUST CHECKER'S `--olean`**: on a snapshot `F` of the files (`hsnap`),
where the private view of a module of the closure of the roots, by con-leche's specification
(`InClosure`, `ViewOf`: nothing about the fast parser), holds a theorem of type `False`, the binary's
calls cannot all succeed.  `hT2` is Theorem 2 at the reader, `Refine2/Frontend/Olean/Contract.lean`.

Composition only: `rust_stages_oleans` (Theorem 2), `stagesO_no_False` (Theorem 1). -/
theorem no_False_oleans_of (hT2 : ConRon.Refine2.Frontend.Olean.ReadOleansRefines)
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
    {r : frontend.export_c.ParseResultD} {store3 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store dirs roots none
      = ok (.Ok r, store3))
    {prepared : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d emptyTier { stR with store := store3 } pre r.decls
      = ok (.Ok prepared, st4))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins = ok (.Ok ipins, st5))
    {Hk : Type} {hinst : arena.checker.InstallHook Hk} {hook : Hk}
    {n : Std.U64} {fe : arena.env.IFEnv} {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {blocks : alloc.vec.Vec arena.checker.BlockCheck}
    (h6 : (do
        let t ← arena.checker.fold_start
        arena.checker.install_fold_hooked hinst emptyTier st5 .Verified ipins t
          prepared.decls 0#usize hook)
      = ok (.Ok (n, fe, pend, blocks), st6))
    {order : alloc.vec.Vec (Bool × Std.U64)}
    (hord : arena.checker.job_order pend blocks = ok order)
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store fe = ok (tier, frozen))
    {layer : arena.env.IFEnv}
    (hlayer : arena.checker.check_layer = ok layer)
    (h8 : ParallelAll order.length (arena.checker.worker_state st6.pins)
      (jobStep tier .Verified layer pend blocks order)) :
    False := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  have hkc : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel :=
    ConRon.Bridge.CoreSpec.of_core
  have hind : ConRon.Bridge.IndSpec :=
    ConRon.Bridge.Inductives.indSpec_of_bridge hkc
  obtain ⟨sA, sB, sB', sC, sD, sE, sF, rv, lfe, hA, hB, hR, hC, hD, hE, hF, -, -⟩ :=
    rust_stages_oleans hT2 hpins rfl (persEnvEmpty_of_eq rfl) hest hst0 h1 h2 hroots hsnap h3 rfl
      (prepare_prelude_of_prepare_d h4) h5 (poolAccepts_intro h6 hord h7 hlayer h8)
  exact stagesO_no_False V hkc hind (pins := ConRon.Refine.absPins pins) hcl hv hmem hk hty
    hA hB hR hC hD hE hF

/-- con-leche: ConLeche/MainTheorem.lean:96 model_exists — **every environment the Rust checker's
`--olean` accepts has a model**, in every set theory, on a snapshot of the files.  `hT2` as in
`no_False_oleans_of`. -/
theorem model_exists_oleans_of (hT2 : ConRon.Refine2.Frontend.Olean.ReadOleansRefines)
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
    {r : frontend.export_c.ParseResultD} {store3 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store dirs roots none
      = ok (.Ok r, store3))
    {prepared : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d emptyTier { stR with store := store3 } pre r.decls
      = ok (.Ok prepared, st4))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins = ok (.Ok ipins, st5))
    {Hk : Type} {hinst : arena.checker.InstallHook Hk} {hook : Hk}
    {n : Std.U64} {fe : arena.env.IFEnv} {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {blocks : alloc.vec.Vec arena.checker.BlockCheck}
    (h6 : (do
        let t ← arena.checker.fold_start
        arena.checker.install_fold_hooked hinst emptyTier st5 .Verified ipins t
          prepared.decls 0#usize hook)
      = ok (.Ok (n, fe, pend, blocks), st6))
    {order : alloc.vec.Vec (Bool × Std.U64)}
    (hord : arena.checker.job_order pend blocks = ok order)
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store fe = ok (tier, frozen))
    {layer : arena.env.IFEnv}
    (hlayer : arena.checker.check_layer = ok layer)
    (h8 : ParallelAll order.length (arena.checker.worker_state st6.pins)
      (jobStep tier .Verified layer pend blocks order)) :
    ∃ env, RustDenotes fe st6 env ∧ Nonempty (ConLeche.Model V env) := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  have hkc : ConRon.Bridge.CoreSpec ConRon.Arena.checkFuel :=
    ConRon.Bridge.CoreSpec.of_core
  have hind : ConRon.Bridge.IndSpec :=
    ConRon.Bridge.Inductives.indSpec_of_bridge hkc
  obtain ⟨sA, sB, sB', sC, sD, sE, sF, rv, lfe, hA, hB, hR, hC, hD, hE, hF, hrelF, hfe⟩ :=
    rust_stages_oleans hT2 hpins rfl (persEnvEmpty_of_eq rfl) hest hst0 h1 h2 hroots hsnap h3 rfl
      (prepare_prelude_of_prepare_d h4) h5 (poolAccepts_intro h6 hord h7 hlayer h8)
  obtain ⟨hwfF, env, hden, ⟨hmod⟩⟩ :=
    stagesO_model V hkc hind (F := F) (pins := ConRon.Refine.absPins pins) hA hB hR hC hD hE hF
  exact ⟨env, ⟨sF, lfe, hrelF.of₀ hwfF, hfe, hden⟩, ⟨ConLeche.Model.Model.ofEnvModelM hmod⟩⟩

/-- con-leche: ConLeche/MainTheorem.lean:163 main_oleans_no_False — **A CLOSURE THE RUST CHECKER'S
`--olean` ACCEPTS HOLDS NO PROOF OF `False`**: if a module of the import closure of the roots, read by
the specification (`InClosure`, `ViewOf`), holds a theorem whose type is `False`, the binary's calls
cannot all succeed.  The files are a premise: `hsnap`, the instance answers as one snapshot `F`.

Composition only: `no_False_oleans_of` at `read_oleans_refines` (Theorem 2 at the reader). -/
theorem no_False_oleans
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
    {r : frontend.export_c.ParseResultD} {store3 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store dirs roots none
      = ok (.Ok r, store3))
    {prepared : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d emptyTier { stR with store := store3 } pre r.decls
      = ok (.Ok prepared, st4))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins = ok (.Ok ipins, st5))
    {Hk : Type} {hinst : arena.checker.InstallHook Hk} {hook : Hk}
    {n : Std.U64} {fe : arena.env.IFEnv} {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {blocks : alloc.vec.Vec arena.checker.BlockCheck}
    (h6 : (do
        let t ← arena.checker.fold_start
        arena.checker.install_fold_hooked hinst emptyTier st5 .Verified ipins t
          prepared.decls 0#usize hook)
      = ok (.Ok (n, fe, pend, blocks), st6))
    {order : alloc.vec.Vec (Bool × Std.U64)}
    (hord : arena.checker.job_order pend blocks = ok order)
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store fe = ok (tier, frozen))
    {layer : arena.env.IFEnv}
    (hlayer : arena.checker.check_layer = ok layer)
    (h8 : ParallelAll order.length (arena.checker.worker_state st6.pins)
      (jobStep tier .Verified layer pend blocks order)) :
    False :=
  no_False_oleans_of ConRon.Refine2.Frontend.Olean.read_oleans_refines V hcl hv hmem hk hty h1 h2 hroots
    hsnap h3 h4 hpins h5 h6 hord h7 hlayer h8

/-- con-leche: ConLeche/MainTheorem.lean:96 model_exists — **every environment the Rust checker's
`--olean` accepts has a model**, in every set theory, on a snapshot of the files (`hsnap`).

Composition only: `model_exists_oleans_of` at `read_oleans_refines` (Theorem 2 at the reader). -/
theorem model_exists_oleans
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
    {r : frontend.export_c.ParseResultD} {store3 : arena.store.EStore}
    (h3 : frontend.olean.records.read_oleans finst fsv emptyTier stR.store dirs roots none
      = ok (.Ok r, store3))
    {prepared : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d emptyTier { stR with store := store3 } pre r.decls
      = ok (.Ok prepared, st4))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins = ok (.Ok ipins, st5))
    {Hk : Type} {hinst : arena.checker.InstallHook Hk} {hook : Hk}
    {n : Std.U64} {fe : arena.env.IFEnv} {pend : alloc.vec.Vec arena.checker.PendingCheck}
    {blocks : alloc.vec.Vec arena.checker.BlockCheck}
    (h6 : (do
        let t ← arena.checker.fold_start
        arena.checker.install_fold_hooked hinst emptyTier st5 .Verified ipins t
          prepared.decls 0#usize hook)
      = ok (.Ok (n, fe, pend, blocks), st6))
    {order : alloc.vec.Vec (Bool × Std.U64)}
    (hord : arena.checker.job_order pend blocks = ok order)
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store fe = ok (tier, frozen))
    {layer : arena.env.IFEnv}
    (hlayer : arena.checker.check_layer = ok layer)
    (h8 : ParallelAll order.length (arena.checker.worker_state st6.pins)
      (jobStep tier .Verified layer pend blocks order)) :
    ∃ env, RustDenotes fe st6 env ∧ Nonempty (ConLeche.Model V env) :=
  model_exists_oleans_of ConRon.Refine2.Frontend.Olean.read_oleans_refines V h1 h2 hroots hsnap h3 h4 hpins
    h5 h6 hord h7 hlayer h8

end Headline

/-! ## 5. The census

`#print axioms` of the two roots: con-leche's own three axioms and nothing
else — no `sorryAx` (since `arena` `db1131f1`, task #97-MILESTONE), no
`native_decide`.  The named hypotheses of the module note are the whole
ledger: they are hypotheses of the statements, not axioms of the
environment, so this census does not list them. -/

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

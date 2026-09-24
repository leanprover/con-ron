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

and the twin's `Arena.runPipeline` (`Arena/Main.lean`) is the same six
stages with `installThenCheck` last.  **The sixth stage is the fold the
binary's driver runs, pool and all** (task #97-P5-POOL):
`driver::check_decls_driver` runs phase A with the heartbeat as its hook,
freezes the tier, runs phase B on `pool::parallel_all`, and thaws the tier.
The headlines take one premise per step (`h6` phase A, `h7` the freeze, `h8`
phase B), which `poolAccepts_intro` assembles into
`Refine2/Checker/Phased.lean`'s `PoolAccepts`.  Phase B's premise is
`ParallelAll`, the contract of the generic combinator `pool::parallel_all`
with the driver's two verified closures (`worker_state`, `check_pending`):
every pending record claimed by exactly one worker, each worker folding
`check_pending` over its claims on one `worker_state`, every step
accepting.  That contract is the pool's trusted claim (OVERVIEW §8.2):
control flow of `pool.rs`, nothing about the checker; `PoolAccepts.toParts`
turns it into one accepting `check_pending_worker` per worker.  The sequential walk
`check_decls_phased` is one such pool (`poolAccepts_of_check_decls_phased`).
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
   (`stages_no_False`, `Arena.no_False_declaration_pipeline`'s route through
   the pure fold);
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
`prepare_prelude`), and take the flags as parameters.  Beside
`[ConLeche.SetTheory V]`, the file's shape `hfalse` and the one premise per
call (`h1`…`h5`, `hpins`, `h6`…`h8`), what they assume is exactly:

* `hmr : ModellerRefines inst m inProcessModeller` — the Rust modeller
  against the twin's (the modeller seam, by design): the unextracted
  `crates/con-ron/src/in_model/`, a port of con-leche's `InModel.generate`,
  answers what the twin's `inProcessModeller` (which CALLS con-leche's
  `generate`) answers;
* `hreads : ReadsAs sinst src chunks.val` — the reads are the chunks
  (task #97-P5-Driver): the binary parses with the verified reader loop
  `parse_source` over the driver's file handle, and
  `Refine2/Frontend/Source.lean`'s `parse_source_eq` makes that
  `parse_chunks` over the chunks the handle hands out; that the handle hands
  out the file's bytes, in order, is the input seam, as `hmr` is the
  modeller's.

Former hypotheses, now theorems or gone (DESIGN.md's task #97-COMPOSE and
#98-HEADLINE sections tag each with its owning lane):

* ~~`InitRel`~~ — the Rust start state is related to the twin's: a theorem
  since task #97-P5-Top (`Refine2/Checker/Init.lean`'s `init_rel`);
* ~~`hk : CoreSpec .verified Arena.checkFuel`~~ — Theorem 1's Core tier
  spec: a theorem since task #97-P3-Core round 6
  (`Bridge/Checker/Hyp.lean`'s `CoreSpec.of_core`);
* ~~`hind : IndSpec .verified`~~ — Theorem 1's inductive tier spec:
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
  constants `startState`/`emptyTier` (`startState_eq`, `emptyTier_eq`);
* `hdec` is now `hpins`, the premise for the binary's pin step: the pin list
  is what the verified decoder read, at any text (as con-leche's theorems
  hold at every pin list); `model_exists_embedded` /
  `no_False_declaration_embedded` fix the text to the embedded `PINS_TEXT`;
* ~~`in_model = true`, `census = false`~~ — the two environment flags
  (`CON_LECHE_INMODEL`, `CON_LECHE_INMODEL_CENSUS`; task #97-COMPOSE's
  mismatch 4): parameters since task #98-HEADLINE, so a run with either flag
  set is inside the theorems.
-/

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Capstone

set_option autoImplicit false

universe w

/-! ## 1. The twin side: the stages, from the driver's start state

`Bridge/Frontend/Capstone.lean`'s `Arena.no_False_declaration_pipeline` is
stated about `Arena.runPipeline` as a whole; Theorem 2 hands us its stages
one at a time.  The glue lemmas below are that proof's own steps, re-used
rather than re-proved: the stages carry the frame facts Theorem 2 needs at
the fold's entry and the fold's start invariant Theorem 1 needs
(`stages_frame`), and the file's `False` theorem into the denoted stream
(`stages_false_mem`). -/

section Twin

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge ConRon.Bridge.Frontend

/-- con-leche: none — an `AM` bind whose first half is known to accept is
its second half at the first half's result. -/
theorem AM.bind_of_ok {α β : Type} {x : AM α} {f : α → AM β} {s s₁ : AState}
    {a : α} (h : x s = .ok (a, s₁)) : (x >>= f) s = f a s₁ := by
  rw [ConRon.Bridge.AM.bind_apply, h]; rfl

/-- con-leche: ConLeche/Verify/Cached/BridgeC.lean:609 checkDeclStepC_run —
**the stages' frame, up to the fold**: after the first five stages from the
driver's start state, the scratch tier is closed, the fold's start invariant
holds, and the pins
and the prepared stream denote.  `Arena.no_False_declaration_pipeline`'s own
steps, stopped before the fold. -/
theorem stages_frame {chunks : List ByteArray} {pins : List NatOpPinSet} {im ce : Bool}
    {sA sB sC sD sE : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE inProcessModeller sA = .ok (.ok pre, sB))
    (hC : parseChunks inProcessModeller chunks im ce sB = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins sD = .ok (ipins, sE)) :
    sE.store.scratchOn = false ∧
      FoldOK .verified Env.empty (mkIFEnv IEnv.empty) sE ∧
      PinsDenote sE.store ipins pins ∧ PersPinSets ipins ∧
      (∀ x ∈ ds.toList, PersDecl x) ∧
      ∃ dsP, denoteDecls sE.store ds.toList = some dsP := by
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  have hoff0 : (AState.init EStore.empty).store.scratchOn = false := rfl
  have hc0 : (AState.init EStore.empty).caches = Caches.empty := rfl
  obtain ⟨hokA, -, hpinsA, hppA, hoffA, -, hcachesA⟩ :=
    internReservedPins_run hok0 hoff0 hA
  have hrbA : ReadCachesOK sA := ReadCachesOK.ofEmpty (by rw [hcachesA]; exact hc0)
  obtain ⟨hstep1, hpersPre, hnPre, preC, hrelPre⟩ :=
    builtinPreludeE_run inProcessModeller_wf inProcessModeller_refines
      hokA hoffA hpinsA hrbA hB
  obtain ⟨hstep2, hpersR, rc, -, hrelR⟩ :=
    parseChunks_run inProcessModeller_wf inProcessModeller_refines hstep1.ok
      (by rw [hstep1.scratch, hoffA]) (hpinsA.mono hstep1.ext hstep1.pins)
      (hrbA.step hstep1) hC
  obtain ⟨hstep3, hpersDs, -, hclPrep⟩ :=
    preparePrelude_run (preC := preC) hstep2.ok
      (by rw [hstep2.scratch, hstep1.scratch, hoffA])
      (hpinsA.mono (hstep1.trans hstep2).ext (hstep1.trans hstep2).pins)
      (denoteDeclArray_ext hstep2.ext hrelPre) hpersPre
      (hnPre.mono hstep2.ext) hrelR.decls hpersR hrelR.projNamed hD
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
    (hk : CoreSpec .verified Arena.checkFuel) (hind : IndSpec .verified)
    {chunks : List ByteArray} {pins : List NatOpPinSet} {im ce : Bool}
    {sA sB sC sD sE sF : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet} {fe' : IFEnv}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE inProcessModeller sA = .ok (.ok pre, sB))
    (hC : parseChunks inProcessModeller chunks im ce sB = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins sD = .ok (ipins, sE))
    (hF : Arena.PooledAccepts .verified ipins ds sE fe' sF) :
    ∃ env', denoteFEnv sF.store fe' = some env' ∧
      Nonempty (ConLeche.Model.EnvModelM V .verified env') := by
  obtain ⟨-, hfold, hipins, hpps, hpd, dsP, hden⟩ :=
    stages_frame hA hB hC hD hE
  obtain ⟨env', F', hdenF, hpure⟩ :=
    Arena.pooledAccepts_bridge rfl hk hind hpps hfold hipins hpd hden hF
  exact ⟨env', hdenF,
    ConLeche.Model.checkDeclsPure_sound_of (V := V) (pins := pins) rfl hpure⟩

/-- con-leche: ConLeche/MainTheorem.lean:110 no_False_declaration — **the
stages' stream carries the file's `False` theorem**: after the first five
stages, the prepared stream denotes, and a file that declares a theorem of
type `False` puts one in the denoted stream.  `stages_frame`'s steps with the
pure parse kept (`parseChunks_run`'s fourth conjunct), then con-leche's
`parseChunks_jsonWithTheoremFalse` and `mem_preparePrelude` — the steps
`Arena.no_False_declaration_pipeline` takes, stopped before the fold. -/
theorem stages_false_mem {chunks : List ByteArray} {pins : List NatOpPinSet} {im ce : Bool}
    (hfalse : ConLeche.jsonWithTheoremFalse chunks)
    {sA sB sC sD sE : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE inProcessModeller sA = .ok (.ok pre, sB))
    (hC : parseChunks inProcessModeller chunks im ce sB = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins sD = .ok (ipins, sE)) :
    ∃ dsP cv vl, denoteDecls sE.store ds.toList = some dsP ∧
      cv.type = .const ConLeche.falseName [] ∧ Declaration.thmDecl cv vl ∈ dsP := by
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  have hoff0 : (AState.init EStore.empty).store.scratchOn = false := rfl
  have hc0 : (AState.init EStore.empty).caches = Caches.empty := rfl
  obtain ⟨hokA, -, hpinsA, hppA, hoffA, -, hcachesA⟩ :=
    internReservedPins_run hok0 hoff0 hA
  have hrbA : ReadCachesOK sA := ReadCachesOK.ofEmpty (by rw [hcachesA]; exact hc0)
  obtain ⟨hstep1, hpersPre, hnPre, preC, hrelPre⟩ :=
    builtinPreludeE_run inProcessModeller_wf inProcessModeller_refines
      hokA hoffA hpinsA hrbA hB
  obtain ⟨hstep2, hpersR, rc, hclR, hrelR⟩ :=
    parseChunks_run inProcessModeller_wf inProcessModeller_refines hstep1.ok
      (by rw [hstep1.scratch, hoffA]) (hpinsA.mono hstep1.ext hstep1.pins)
      (hrbA.step hstep1) hC
  obtain ⟨hstep3, -, -, hclPrep⟩ :=
    preparePrelude_run (preC := preC) hstep2.ok
      (by rw [hstep2.scratch, hstep1.scratch, hoffA])
      (hpinsA.mono (hstep1.trans hstep2).ext (hstep1.trans hstep2).pins)
      (denoteDeclArray_ext hstep2.ext hrelPre) hpersPre
      (hnPre.mono hstep2.ext) hrelR.decls hpersR hrelR.projNamed hD
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
pure fold accepts the stream), then `no_False_theorem_accepted_pure`.  The
route `Arena.no_False_declaration_pipeline` takes, through the pure fold
rather than through `Arena.runPipeline` — the pooled phase B is not one twin
walk, so there is no `runPipeline` run to refute (task #97-P5-POOL). -/
theorem stages_no_False (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec .verified Arena.checkFuel) (hind : IndSpec .verified)
    {chunks : List ByteArray} {pins : List NatOpPinSet} {im ce : Bool}
    (hfalse : ConLeche.jsonWithTheoremFalse chunks)
    {sA sB sC sD sE sF : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet} {fe' : IFEnv}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE inProcessModeller sA = .ok (.ok pre, sB))
    (hC : parseChunks inProcessModeller chunks im ce sB = .ok (.ok r, sC))
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
    Arena.pooledAccepts_bridge rfl hk hind hpps hfold hipins hpd hden hF
  exact ConRon.Bridge.Frontend.no_False_theorem_accepted_pure V rfl hmem hty hpure

/-- con-leche: none — **the fold's end state is well formed** (Theorem 1).
Theorem 2 is a lockstep refinement and its relation `AStateRel₀` carries no
fact about the twin's store (task #97-T2-AUDIT); the headline states the full
`AStateRel`, whose one extra clause, `StoreWF`, is Theorem 1's:
phase A's `annotFold_bridge` (the first step of `Arena.pooledAccepts_bridge`)
ends at `FoldOK`, whose `CheckOK` carries `StateOK`, and the pooled fold hands
the phase-A state back. -/
theorem stages_storeWF
    (hk : CoreSpec .verified Arena.checkFuel) (hind : IndSpec .verified)
    {chunks : List ByteArray} {pins : List NatOpPinSet} {im ce : Bool}
    {sA sB sC sD sE sF : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet} {fe' : IFEnv}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE inProcessModeller sA = .ok (.ok pre, sB))
    (hC : parseChunks inProcessModeller chunks im ce sB = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins sD = .ok (ipins, sE))
    (hF : Arena.PooledAccepts .verified ipins ds sE fe' sF) :
    StoreWF sF.store := by
  obtain ⟨-, hfold, hipins, hpps, hpd, dsP, hden⟩ :=
    stages_frame hA hB hC hD hE
  obtain ⟨n, pend, -, hA', -⟩ := hF
  obtain ⟨env₁, pendP, hok₁, -⟩ :=
    Arena.annotFold_bridge rfl hk hind hpps ds.toList dsP Env.empty 0 n
      (mkIFEnv IEnv.empty) fe' #[] pend [] sE sF hfold List.nodup_nil hipins hpd hden
      .nil hA'
  exact hok₁.check.state.wf

end Twin

/-! ## 2. The Rust side: the six stages, walked into the twin by Theorem 2 -/

section Rust

open ConRon.Refine2 ConRon.Refine2.Frontend

/-- **The start state** (task #97-COMPOSE's mismatch 2, a named hypothesis
until task #97-P5-Top).  The Rust driver's `AState::init(EStore::empty())`,
read through `PersTier::empty()`, is related to the twin driver's
`AState.init EStore.empty` and satisfies the Rust-side invariant —
`Refine2/Checker/Init.lean`'s `init_rel`. -/
def InitRel : Prop :=
  ∀ (pers : arena.store.PersTier) (est : arena.store.EStore)
    (st : arena.monad.AState),
    arena.store.PersTier.empty = ok pers → arena.store.EStore.empty = ok est →
    arena.monad.AState.init est = ok st →
    AStateRel₀ pers st (ConRon.Arena.AState.init ConRon.Arena.EStore.empty) ∧
      AStateInv pers st

theorem initRel : InitRel := fun _ _ _ _ hest hst =>
  ⟨(init_rel hest hst).1, (init_rel hest hst).2.1⟩

/-- **The Rust pipeline, walked into the twin.**  Six accepting Rust runs from
the driver's start state give six accepting twin runs from the twin's, at the
abstracted values, with the Rust's final state related to the twin's and the
Rust's environment related to the twin's.

Theorem 2's six top lemmas, one per stage, all lockstep (`AStateRel₀`, no
precondition on the twin: task #97-T2-LOCKSTEP lane Checker deleted `BrOK`
and ruling 2's `DeclResolves`). -/
theorem rust_stages
    (hk : ConRon.Bridge.CoreSpec .verified ConRon.Arena.checkFuel)
    (hind : ConRon.Bridge.IndSpec .verified)
    {G : Type} {inst : frontend.types.Modeller G} {m : G}
    (hmr : ConRon.Refine2.Frontend.ModellerRefines inst m
      ConRon.Arena.Frontend.inProcessModeller)
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    {text : Slice Std.U8}
    (hdec : kernel.pins_decode.decode text = ok (.Ok pins))
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)} {inModel census : Bool}
    {pers : arena.store.PersTier} {est : arena.store.EStore}
    {st0 st1 st2 st3 st4 st5 st6 : arena.monad.AState}
    {pre : frontend.prepare.PreludeIx} {r : frontend.export_c.ParseResultD}
    {ds : alloc.vec.Vec arena.env.IDeclaration}
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {fe : arena.env.IFEnv}
    (hpers : arena.store.PersTier.empty = ok pers)
    (hest : arena.store.EStore.empty = ok est)
    (hst0 : arena.monad.AState.init est = ok st0)
    (h1 : arena.pins.intern_reserved_pins pers st0 = ok (.Ok (), st1))
    (h2 : frontend.prelude.builtin_prelude_e inst pers m st1 = ok (.Ok pre, st2))
    {Sc : Type} {sinst : frontend.export_c.ChunkSource Sc} {src src' : Sc}
    (hreads : ReadsAs sinst src chunks.val)
    (h3 : frontend.export_c.parse_source inst sinst pers m st2 src inModel census
      = ok (.Ok r, st3, src'))
    (h4 : frontend.prepare.prepare_prelude pers st3 pre r.decls = ok (.Ok ds, st4))
    (h5 : arena.checker.intern_all_pins pers st4 pins = ok (.Ok ipins, st5))
    {Hk : Type} {hinst : arena.checker.InstallHook Hk} {hook : Hk}
    (h6 : PoolAccepts hinst pers st5 .Verified ipins ds hook fe st6) :
    ∃ (sA sB sC sD sE sF : ConRon.Arena.AState)
      (rv : ConRon.Arena.Frontend.ParseResultD) (lfe : ConRon.Arena.IFEnv),
      ConRon.Arena.internReservedPins
          (ConRon.Arena.AState.init ConRon.Arena.EStore.empty) = .ok ((), sA) ∧
      ConRon.Arena.Frontend.builtinPreludeE ConRon.Arena.Frontend.inProcessModeller sA
          = .ok (.ok (absPreludeIx pre), sB) ∧
      ConRon.Arena.Frontend.parseChunks ConRon.Arena.Frontend.inProcessModeller
          (absChunks chunks) inModel census sB = .ok (.ok rv, sC) ∧
      ConRon.Arena.Frontend.preparePrelude (absPreludeIx pre) rv.decls sC
          = .ok ((absIDeclL ds).toArray, sD) ∧
      ConRon.Arena.internAllPins (ConRon.Refine.absPins pins) sD
          = .ok (absINatOpPinSetL ipins, sE) ∧
      ConRon.Arena.PooledAccepts .verified (absINatOpPinSetL ipins)
          (absIDeclL ds).toArray sE lfe sF ∧
      AStateRel₀ pers st6 sF ∧ IFEnvRel fe lfe := by
  obtain ⟨hrel0, hinv0, -⟩ := init_rel (pers := pers) hest hst0
  -- 1. the reserved pins
  obtain ⟨sA, hA, hrelA, hinvA⟩ :=
    (intern_reserved_pins_refines hrel0 hinv0 h1).dest
  -- 2. the prelude
  obtain ⟨preL, sB, hB, hpreL, hrelB, hinvB⟩ :=
    builtin_prelude_e_refines scanSpec hmr hrelA hinvA h2
  subst hpreL
  -- 3. the stream: the reader loop IS `parse_chunks` over the chunks read
  have h3' := parse_source_eq hreads h3
  obtain ⟨rv, sC, hC, hrv, hrelC, hinvC⟩ :=
    parse_chunks_refines scanSpec hmr hrelB hinvB h3'
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
    (pins := ipins) hrelE hinvE h6
  exact ⟨sA, sB, sC, sD, sE, sF, rv, lfe, hA, hB, hC, hD', hE, hF, hrelF, hfe⟩

end Rust

/-! ## 3. The binary's start values, and what its environment denotes

`check_main` starts from `AState::empty()` (`bin/con-ron.rs:373`, which is
`AState::init(EStore::empty())`) and `&PersTier::empty()`
(`bin/con-ron.rs:381`).  The Aeneas model of each is a `Result` that is
`ok`; `startState` and `emptyTier` are those values, so the headlines' first
premise starts from them rather than from universally quantified states with
equations about them. -/

section Defs

open ConRon.Refine2 ConRon.Refine2.Frontend

theorem astate_empty_ok : ∃ st, arena.monad.AState.empty = ok st := by
  simp only [arena.monad.AState.empty, arena.store.Tbl.empty, arena.store.ETables.empty,
    arena.store.LsTables.empty, arena.store.LTables.empty, arena.store.NTables.empty,
    arena.store.NStore.empty, arena.store.LStore.empty, arena.store.LsStore.empty,
    arena.store.EStore.empty, ron.hashmap2.HashMap2.new,
    arena.monad.AState.init, arena.monad.Memos.empty, arena.core_state.Caches.empty,
    arena.pins.Pins.empty, arena.handle.LsIdx.of_word, arena.handle.LIdx.of_word,
    arena.handle.EIdx.of_word, bind_tc_ok]
  exact ⟨_, rfl⟩

/-- **The binary's start state**, `AState::empty()` (`bin/con-ron.rs:373`):
the value the Aeneas model of it returns (`astate_empty_ok`: it is `ok`). -/
noncomputable def startState : arena.monad.AState := Classical.choose astate_empty_ok

theorem startState_eq : arena.monad.AState.empty = ok startState :=
  Classical.choose_spec astate_empty_ok

theorem persTier_empty_ok : ∃ pers, arena.store.PersTier.empty = ok pers := by
  simp only [arena.store.PersTier.empty, arena.store.Tbl.empty, arena.store.ETables.empty,
    arena.store.LsTables.empty, arena.store.LTables.empty, arena.store.NTables.empty,
    ron.hashmap2.HashMap2.new, bind_tc_ok]
  exact ⟨_, rfl⟩

/-- **The binary's persistent tier**, `&PersTier::empty()`
(`bin/con-ron.rs:381`): the tier every stage up to phase B is handed. -/
noncomputable def emptyTier : arena.store.PersTier := Classical.choose persTier_empty_ok

theorem emptyTier_eq : arena.store.PersTier.empty = ok emptyTier :=
  Classical.choose_spec persTier_empty_ok

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
(`IFEnvRel`), and Theorem 1's `denoteFEnv` reads that twin environment in
that twin store.  (The arena has no abstraction FUNCTION from the Rust's
store to con-leche's `Env` — the store is abstracted by a relation — so the
Rust environment's meaning can only be spelled through the twin.) -/
def RustDenotes (fe : arena.env.IFEnv) (st : arena.monad.AState)
    (env : ConLeche.Env) : Prop :=
  ∃ (lst : ConRon.Arena.AState) (lfe : ConRon.Arena.IFEnv),
    AStateRel emptyTier st lst ∧ IFEnvRel fe lfe ∧
    ConRon.Bridge.denoteFEnv lst.store lfe = some env

/-- `prepare::prepare_d`, the call the binary makes (`bin/con-ron.rs:522`),
is `prepare_prelude`'s body: `prepare_prelude` is its `.decls`. -/
theorem prepare_prelude_of_prepare_d {pers : arena.store.PersTier}
    {st st' : arena.monad.AState} {pre : frontend.prepare.PreludeIx}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {p : frontend.prepare.Prepared}
    (h : frontend.prepare.prepare_d pers st pre ds = ok (.Ok p, st')) :
    frontend.prepare.prepare_prelude pers st pre ds = ok (.Ok p.decls, st') := by
  rw [frontend.prepare.prepare_prelude, h]
  simp only [bind_tc_ok]
  rfl

/-- `pins_decode::decode_embedded()`, the call the binary's
`driver::pins_for_run` makes (`driver.rs:296`), is `decode` of some text. -/
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
| `startState`, `emptyTier` | `bin/con-ron.rs:373` `AState::empty()`, `:381` `&PersTier::empty()` |
| `h1` | `bin/con-ron.rs:390` `arena::pins::intern_reserved_pins` |
| `h2` | `bin/con-ron.rs:408` `prelude::builtin_prelude_e` |
| `hreads`, `h3` | `bin/con-ron.rs:432` `driver::parse_export_stream_d`, which is `driver.rs:948`'s `export_c::parse_source` over the file's handle; the flags are read at `bin/con-ron.rs:425-426` |
| `h4` | `bin/con-ron.rs:522` `prepare::prepare_d` |
| `hpins` | `bin/con-ron.rs:542` `driver::pins_for_run`, whose default is `driver.rs:296` `pins_decode::decode_embedded()`, which is `decode` of the embedded `PINS_TEXT` (the `_embedded` corollaries below name it) |
| `h5` | `bin/con-ron.rs:569` `checker::intern_all_pins` |
| `h6` | `bin/con-ron.rs:586`/`:589` `driver::check_decls_driver` at `CheckMode::Verified` (`:366`), phase A: `driver.rs:566` `checker::annot_fold_hooked(…, checker::fold_start(), ds, 0, obs)` |
| `h7` | the same, the boundary: `driver.rs:582` `checker::freeze_tier` |
| `h8` | the same, phase B: `driver.rs:596` `pool::parallel_all` with `init` `checker::worker_state` and `step` `checker::check_pending` (`thaw_tier` at `:613` restores the store) |

`h8` is a predicate, not an equation: `parallel_all` is not extracted, and
`Refine2/Checker/Phased.lean`'s `ParallelAll` states its contract, generic
in the state and the step (the pool's trusted claim, OVERVIEW §8.2), here at
the driver's two verified closures (`pendingStep` is the step's model).  The theorems hold at
both flags `inModel`/`census` (`CON_LECHE_INMODEL`,
`CON_LECHE_INMODEL_CENSUS`), every install hook (the heartbeat or
`driver::Silent`), every chunk source whose reads are `chunks`, and every
modeller that refines the twin's, and at every pin text `hpins` decodes, as
con-leche's hold at every pin list.  **`--pins FILE`** (read by the
unverified `con_ron_dump::parse_pins`) and **`--no-pins`** do not call the
decoder, so runs with them are outside the theorems.

`hpins` is stated about `decode` of a free text rather than about
`decode_embedded` because naming the embedded constant `PINS_TEXT` costs the
census one axiom, `kernel.pins_text.PINS_TEXT._native.decide.ax_1` — the one
Aeneas's `toStr` spends on that constant's DEFINITION (AENEAS_FINDINGS.md
§3.8; `Refine2/Checker/PinsWF.lean`'s census), nothing this proof evaluates.
`model_exists_embedded` / `no_False_declaration_embedded` are the headlines
with `decode_embedded` itself in the premise, and carry that axiom. -/

section Headline

open ConRon.Refine2 ConRon.Refine2.Frontend

/-- con-leche: ConLeche/MainTheorem.lean:96 model_exists —
**THE MAIN THEOREM FOR THE RUST CHECKER** (DESIGN.md §1, §8.2): every
environment the Rust checker accepts has a model, in every set theory.

con-leche's reads `(accepted : checkDecls .verified pins ds = .ok env) :
Nonempty (Model V env)`; here the accepting run is the binary's calls, one
premise each (§4's table), and the environment is the one the Rust's `fe`
denotes (`RustDenotes`).  Two premises are seams by design: `hmr` (the
unextracted Rust modeller `crates/con-ron/src/in_model/` answers what the
twin's `inProcessModeller`, which CALLS con-leche's `generate`, answers) and
`hreads` (the chunk source hands out `chunks`).

Composition only: `rust_stages` (Theorem 2), `stages_model` (Theorem 1 +
con-leche), `stages_storeWF`. -/
theorem model_exists (V : Type w) [ConLeche.SetTheory V]
    {G : Type} {inst : frontend.types.Modeller G} {m : G}
    (hmr : ModellerRefines inst m ConRon.Arena.Frontend.inProcessModeller)
    {st1 st2 st3 st4 st5 st6 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e inst emptyTier m st1 = ok (.Ok pre, st2))
    {Sc : Type} {sinst : frontend.export_c.ChunkSource Sc} {src src' : Sc}
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    (hreads : ReadsAs sinst src chunks.val)
    {inModel census : Bool} {r : frontend.export_c.ParseResultD}
    (h3 : frontend.export_c.parse_source inst sinst emptyTier m st2 src inModel census
      = ok (.Ok r, st3, src'))
    {prepared : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d emptyTier st3 pre r.decls = ok (.Ok prepared, st4))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins = ok (.Ok ipins, st5))
    {Hk : Type} {hinst : arena.checker.InstallHook Hk} {hook : Hk}
    {n : Std.U64} {fe : arena.env.IFEnv} {pend : alloc.vec.Vec arena.checker.PendingCheck}
    (h6 : (do
        let t ← arena.checker.fold_start
        arena.checker.annot_fold_hooked hinst emptyTier st5 .Verified ipins t
          prepared.decls 0#usize hook)
      = ok (.Ok (n, fe, pend), st6))
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store = ok (.Ok tier, frozen))
    (h8 : ParallelAll pend.length (arena.checker.worker_state st6.pins)
      (pendingStep tier .Verified fe pend)) :
    ∃ env, RustDenotes fe st6 env ∧ Nonempty (ConLeche.Model V env) := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  -- Theorem 1's two tier specs, discharged (tasks #97-P3-Core, #97-P3-Ind)
  have hk : ConRon.Bridge.CoreSpec .verified ConRon.Arena.checkFuel :=
    ConRon.Bridge.CoreSpec.of_core rfl
  have hind : ConRon.Bridge.IndSpec .verified :=
    ConRon.Bridge.Inductives.indSpec_of_bridge rfl hk
  obtain ⟨sA, sB, sC, sD, sE, sF, rv, lfe, hA, hB, hC, hD, hE, hF, hrelF, hfe⟩ :=
    rust_stages hk hind hmr hpins emptyTier_eq hest hst0 h1 h2
      hreads h3 (prepare_prelude_of_prepare_d h4) h5 (poolAccepts_intro h6 h7 h8)
  obtain ⟨env, hden, ⟨hmod⟩⟩ := stages_model V hk hind hA hB hC hD hE hF
  -- the relation's `StoreWF` clause is Theorem 1's (Theorem 2 is lockstep)
  have hwfF := stages_storeWF hk hind hA hB hC hD hE hF
  exact ⟨env, ⟨sF, lfe, hrelF.of₀ hwfF, hfe, hden⟩,
    ⟨ConLeche.Model.Model.ofEnvModelM hmod⟩⟩

/-- con-leche: ConLeche/MainTheorem.lean:110 no_False_declaration — **A FILE
THAT DECLARES A THEOREM OF TYPE `False` IS REJECTED BY THE RUST CHECKER**:
the binary's calls (§4's table) cannot all succeed on it.

con-leche's concludes `∃ e, (do …; checkDecls .verified pins ds) = .error e`
about its own pipeline; the binary's is not one function (the pool is a
predicate), so the letter here has the same premises as `model_exists` and
concludes `False`.

Composition only: `rust_stages` (Theorem 2) turns the Rust runs into twin
runs, the last the pooled fold; `stages_no_False` (Theorem 1) turns that into
the pure fold's accept of a stream holding the file's `False` theorem, which
con-leche's `no_proof_of_False_pure` refutes
(`no_False_theorem_accepted_pure`). -/
theorem no_False_declaration (V : Type w) [ConLeche.SetTheory V]
    {G : Type} {inst : frontend.types.Modeller G} {m : G}
    (hmr : ModellerRefines inst m ConRon.Arena.Frontend.inProcessModeller)
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    (hfalse : ConLeche.jsonWithTheoremFalse (absChunks chunks))
    {st1 st2 st3 st4 st5 st6 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e inst emptyTier m st1 = ok (.Ok pre, st2))
    {Sc : Type} {sinst : frontend.export_c.ChunkSource Sc} {src src' : Sc}
    (hreads : ReadsAs sinst src chunks.val)
    {inModel census : Bool} {r : frontend.export_c.ParseResultD}
    (h3 : frontend.export_c.parse_source inst sinst emptyTier m st2 src inModel census
      = ok (.Ok r, st3, src'))
    {prepared : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d emptyTier st3 pre r.decls = ok (.Ok prepared, st4))
    {pinText : Slice Std.U8} {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode pinText = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins = ok (.Ok ipins, st5))
    {Hk : Type} {hinst : arena.checker.InstallHook Hk} {hook : Hk}
    {n : Std.U64} {fe : arena.env.IFEnv} {pend : alloc.vec.Vec arena.checker.PendingCheck}
    (h6 : (do
        let t ← arena.checker.fold_start
        arena.checker.annot_fold_hooked hinst emptyTier st5 .Verified ipins t
          prepared.decls 0#usize hook)
      = ok (.Ok (n, fe, pend), st6))
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store = ok (.Ok tier, frozen))
    (h8 : ParallelAll pend.length (arena.checker.worker_state st6.pins)
      (pendingStep tier .Verified fe pend)) :
    False := by
  obtain ⟨est, hest, hst0⟩ := startState_init
  have hk : ConRon.Bridge.CoreSpec .verified ConRon.Arena.checkFuel :=
    ConRon.Bridge.CoreSpec.of_core rfl
  have hind : ConRon.Bridge.IndSpec .verified :=
    ConRon.Bridge.Inductives.indSpec_of_bridge rfl hk
  obtain ⟨sA, sB, sC, sD, sE, sF, rv, lfe, hA, hB, hC, hD, hE, hF, -, -⟩ :=
    rust_stages hk hind hmr hpins emptyTier_eq hest hst0 h1 h2
      hreads h3 (prepare_prelude_of_prepare_d h4) h5 (poolAccepts_intro h6 h7 h8)
  exact stages_no_False V hk hind (pins := ConRon.Refine.absPins pins) hfalse
    hA hB hC hD hE hF

/-- `model_exists` with the pin premise the binary's own call,
`pins_decode::decode_embedded()` (`driver.rs:296`).  Its census adds
`kernel.pins_text.PINS_TEXT._native.decide.ax_1` (§4's note). -/
theorem model_exists_embedded (V : Type w) [ConLeche.SetTheory V]
    {G : Type} {inst : frontend.types.Modeller G} {m : G}
    (hmr : ModellerRefines inst m ConRon.Arena.Frontend.inProcessModeller)
    {st1 st2 st3 st4 st5 st6 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e inst emptyTier m st1 = ok (.Ok pre, st2))
    {Sc : Type} {sinst : frontend.export_c.ChunkSource Sc} {src src' : Sc}
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    (hreads : ReadsAs sinst src chunks.val)
    {inModel census : Bool} {r : frontend.export_c.ParseResultD}
    (h3 : frontend.export_c.parse_source inst sinst emptyTier m st2 src inModel census
      = ok (.Ok r, st3, src'))
    {prepared : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d emptyTier st3 pre r.decls = ok (.Ok prepared, st4))
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode_embedded = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins = ok (.Ok ipins, st5))
    {Hk : Type} {hinst : arena.checker.InstallHook Hk} {hook : Hk}
    {n : Std.U64} {fe : arena.env.IFEnv} {pend : alloc.vec.Vec arena.checker.PendingCheck}
    (h6 : (do
        let t ← arena.checker.fold_start
        arena.checker.annot_fold_hooked hinst emptyTier st5 .Verified ipins t
          prepared.decls 0#usize hook)
      = ok (.Ok (n, fe, pend), st6))
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store = ok (.Ok tier, frozen))
    (h8 : ParallelAll pend.length (arena.checker.worker_state st6.pins)
      (pendingStep tier .Verified fe pend)) :
    ∃ env, RustDenotes fe st6 env ∧ Nonempty (ConLeche.Model V env) :=
  have ⟨_, hdec⟩ := decode_of_decode_embedded hpins
  model_exists V hmr h1 h2 hreads h3 h4 hdec h5 h6 h7 h8

/-- `no_False_declaration` with the pin premise the binary's own call,
`pins_decode::decode_embedded()` (`driver.rs:296`).  Its census adds
`kernel.pins_text.PINS_TEXT._native.decide.ax_1` (§4's note). -/
theorem no_False_declaration_embedded (V : Type w) [ConLeche.SetTheory V]
    {G : Type} {inst : frontend.types.Modeller G} {m : G}
    (hmr : ModellerRefines inst m ConRon.Arena.Frontend.inProcessModeller)
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    (hfalse : ConLeche.jsonWithTheoremFalse (absChunks chunks))
    {st1 st2 st3 st4 st5 st6 : arena.monad.AState}
    (h1 : arena.pins.intern_reserved_pins emptyTier startState = ok (.Ok (), st1))
    {pre : frontend.prepare.PreludeIx}
    (h2 : frontend.prelude.builtin_prelude_e inst emptyTier m st1 = ok (.Ok pre, st2))
    {Sc : Type} {sinst : frontend.export_c.ChunkSource Sc} {src src' : Sc}
    (hreads : ReadsAs sinst src chunks.val)
    {inModel census : Bool} {r : frontend.export_c.ParseResultD}
    (h3 : frontend.export_c.parse_source inst sinst emptyTier m st2 src inModel census
      = ok (.Ok r, st3, src'))
    {prepared : frontend.prepare.Prepared}
    (h4 : frontend.prepare.prepare_d emptyTier st3 pre r.decls = ok (.Ok prepared, st4))
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hpins : kernel.pins_decode.decode_embedded = ok (.Ok pins))
    {ipins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    (h5 : arena.checker.intern_all_pins emptyTier st4 pins = ok (.Ok ipins, st5))
    {Hk : Type} {hinst : arena.checker.InstallHook Hk} {hook : Hk}
    {n : Std.U64} {fe : arena.env.IFEnv} {pend : alloc.vec.Vec arena.checker.PendingCheck}
    (h6 : (do
        let t ← arena.checker.fold_start
        arena.checker.annot_fold_hooked hinst emptyTier st5 .Verified ipins t
          prepared.decls 0#usize hook)
      = ok (.Ok (n, fe, pend), st6))
    {tier : arena.store.PersTier} {frozen : arena.store.EStore}
    (h7 : arena.checker.freeze_tier st6.store = ok (.Ok tier, frozen))
    (h8 : ParallelAll pend.length (arena.checker.worker_state st6.pins)
      (pendingStep tier .Verified fe pend)) :
    False :=
  have ⟨_, hdec⟩ := decode_of_decode_embedded hpins
  no_False_declaration V hmr hfalse h1 h2 hreads h3 h4 hdec h5 h6 h7 h8

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

end ConRon.Capstone

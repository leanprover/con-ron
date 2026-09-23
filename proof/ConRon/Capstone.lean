import ConRon.Bridge.Frontend.Capstone
import ConRon.Refine2.Checker.Top
import ConRon.Refine2.Frontend.Top
import ConRon.Refine2.Frontend.Prepare
import ConRon.Refine2.Checker.Pins
import ConRon.Refine2.Checker.Init
import ConRon.Refine2.Checker.PinsWF

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
frontier is measured as the dependency closure of these two.

## The pipeline, stage by stage

The binary (`crates/con-ron/src/bin/con-ron.rs`) is an unverified driver
around six extracted core functions, in this order, on one `AState` made
from `EStore::empty()` and one `PersTier::empty()`:

    intern_reserved_pins → builtin_prelude_e → parse_chunks
      → prepare_prelude → intern_all_pins → install_then_check

and the twin's `Arena.runPipeline` (`Arena/Main.lean`) is the same six
stages.  So the statement takes the six Rust RUNS as hypotheses (the driver's
calling order is the one trusted line, exactly as it was for the original
campaign), and the proof is:

1. **Theorem 2, per stage** — `Refine2`'s six `…_refines` lemmas walk the
   Rust runs into six TWIN runs from the twin's own start state
   `AState.init EStore.empty`, related at every step (`AStateRel`/
   `AStateInv`);
2. **Theorem 1** — the twin runs are exactly `Arena.runPipeline`'s, so
   `Arena.no_False_declaration_pipeline` refutes the accept; for the model,
   the same stages feed `Arena.installThenCheck_bridge`;
3. **con-leche** — `checkDeclsPure_sound_of` turns the pure accept into a
   model.

Every step is an existing theorem; what this file adds is glue: the Rust
runs threaded through `Sim`/`SimStream`/`SimFold`, the twin runs reassembled
into `runPipelineM`, and the twin frame facts (`scratchOn = false`) that
Theorem 2's `BrOK` asks for, read off Theorem 1's stage lemmas.

## The named hypotheses

Beyond the `sorry`s of the tiers, the composition carries these, and they
are the campaign's remaining obligations that are NOT `sorry`s (DESIGN.md's
task #97-COMPOSE section tags each with its owning lane):

* ~~`InitRel`~~ — the Rust start state is related to the twin's: a theorem
  since task #97-P5-Top (`Refine2/Checker/Init.lean`'s `init_rel`);
* `hk : CoreSpec .verified Arena.checkFuel`, `hind : IndSpec .verified` —
  Theorem 1's two tier specs (as on `Arena.no_False_declaration_pipeline`);
* `hbytes` — the prelude gate (`scripts/gen-prelude-lean.sh --check`);
* `hsc : ScanSpec` — Theorem 2's scanner seam, discharged only in the
  out-of-build `RefineOld/Frontend/`;
* `hmr : Refine2.Frontend.ModellerRefines inst m inProcessModeller` — the
  Rust modeller against the twin's (the modeller seam, by design);
* `hdec : kernel.pins_decode.decode text = ok (.Ok pins)` — the pin list is
  what the port's decoder read (it was `hwf`, the list's well-formedness,
  until task #97-P5-Top ported `RefineOld/PinsWF.lean`'s `decode_wf` to
  `Refine2/Checker/PinsWF.lean`); the binary's `pins_for_run` choosing the
  text is driver code;
* `hfn : FrozenNative` — the frozen-tier guard (`Refine2/Promote/Promote.lean`,
  task #97-P5-Top): the two promotion lemmas without their `PersUnfrozen`
  side condition, which is what they become once the pending Rust commit
  makes `M_FROZEN` a `Native` decline.
-/

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Capstone

set_option autoImplicit false

universe w

/-! ## 1. The twin side: the stages, from the driver's start state

`Bridge/Frontend/Capstone.lean`'s `Arena.no_False_declaration_pipeline` is
stated about `Arena.runPipeline` as a whole; Theorem 2 hands us its stages
one at a time.  Two glue lemmas bridge that: the stages reassemble into
`runPipelineM` (§1a), and the stages carry the frame facts Theorem 2's
`install_then_check_refines` needs at its entry and the fold's start
invariant Theorem 1's `installThenCheck_bridge` needs (§1b).  Both are the
`_pipeline` proof's own steps, re-used rather than re-proved. -/

section Twin

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge ConRon.Bridge.Frontend

/-- con-leche: none — an `AM` bind whose first half is known to accept is
its second half at the first half's result. -/
theorem AM.bind_of_ok {α β : Type} {x : AM α} {f : α → AM β} {s s₁ : AState}
    {a : α} (h : x s = .ok (a, s₁)) : (x >>= f) s = f a s₁ := by
  rw [ConRon.Bridge.AM.bind_apply, h]; rfl

/-- con-leche: Main.lean:461-711 checkMain — **the six stages ARE the
pipeline**: accepting twin runs of `internReservedPins`, `builtinPreludeE`,
`parseChunks`, `preparePrelude`, `internAllPins` and `installThenCheck`, from
`AState.init EStore.empty`, are an accepting `Arena.runPipeline`. -/
theorem runPipeline_ok_of_stages {chunks : List ByteArray}
    {pins : List NatOpPinSet}
    {sA sB sC sD sE sF : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet} {fe' : IFEnv}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE inProcessModeller sA = .ok (.ok pre, sB))
    (hC : parseChunks inProcessModeller chunks true false sB = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins sD = .ok (ipins, sE))
    (hF : installThenCheck .verified ipins ds sE = .ok (.ok fe', sF)) :
    ∃ n, Arena.runPipeline chunks .verified pins = .ok n := by
  rw [parseChunks] at hC
  obtain ⟨st, sB', hinit, hgo⟩ := ConRon.Bridge.AM.bind_ok hC
  have hhead : runPipelineHead inProcessModeller (AState.init EStore.empty)
      = .ok (.ok (pre, st), sB') := by
    rw [runPipelineHead, AM.bind_of_ok hA, AM.bind_of_ok hB]
    show (StateD.init true false >>= fun x => pure (Except.ok (pre, x))) sB = _
    rw [AM.bind_of_ok hinit]; rfl
  have htail : runPipelineTail .verified pins pre r sC
      = .ok (.ok (r.decls.size - r.genRecords), sF) := by
    rw [runPipelineTail, AM.bind_of_ok hD, AM.bind_of_ok hE, AM.bind_of_ok hF]
    rfl
  have hm : (runPipelineM inProcessModeller .verified pins chunks).run
      (AState.init EStore.empty) = .ok (.ok (r.decls.size - r.genRecords), sF) := by
    show runPipelineM inProcessModeller .verified pins chunks
      (AState.init EStore.empty) = _
    rw [runPipelineM, AM.bind_of_ok hhead]
    show (parseChunksGo inProcessModeller st .empty 0 0 chunks >>= fun x =>
        match x with
        | .error (e, n) => pure (.error (Frontend.atLine e n))
        | .ok r => runPipelineTail .verified pins pre r) sB' = _
    rw [AM.bind_of_ok hgo]
    exact htail
  exact ⟨r.decls.size - r.genRecords, by rw [Arena.runPipeline, hm]⟩

/-- con-leche: ConLeche/Verify/Cached/BridgeC.lean:609 checkDeclStepC_run —
**the stages' frame, up to the fold**: after the first five stages from the
driver's start state, the scratch tier is closed (Theorem 2's `BrOK` asks for
it at `install_then_check`), the fold's start invariant holds, and the pins
and the prepared stream denote.  `Arena.no_False_declaration_pipeline`'s own
steps, stopped before the fold. -/
theorem stages_frame {chunks : List ByteArray} {pins : List NatOpPinSet}
    (hbytes : preludeText = ConLeche.Frontend.builtinPreludeText.toUTF8)
    {sA sB sC sD sE : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE inProcessModeller sA = .ok (.ok pre, sB))
    (hC : parseChunks inProcessModeller chunks true false sB = .ok (.ok r, sC))
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
  obtain ⟨hstep1, hpersPre, hnPre, preC, -, hrelPre⟩ :=
    builtinPreludeE_run inProcessModeller_wf inProcessModeller_refines hbytes
      hokA hoffA hB
  obtain ⟨hstep2, hpersR, rc, -, hrelR⟩ :=
    parseChunks_run inProcessModeller_wf inProcessModeller_refines hstep1.ok
      (by rw [hstep1.scratch, hoffA]) hC
  obtain ⟨hstep3, hpersDs, -, hclPrep⟩ :=
    preparePrelude_run (preC := preC) hstep2.ok
      (by rw [hstep2.scratch, hstep1.scratch, hoffA])
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
model at (B), at the pipeline**: `Bridge/Checker/Capstone.lean`'s
`Arena.model_exists` is stated at the PURE fold; the binary runs the
two-phase one, after `internAllPins`.  `stages_frame`, then
`Arena.installThenCheck_bridge`, then con-leche. -/
theorem stages_model (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec .verified Arena.checkFuel) (hind : IndSpec .verified)
    (hbytes : preludeText = ConLeche.Frontend.builtinPreludeText.toUTF8)
    {chunks : List ByteArray} {pins : List NatOpPinSet}
    {sA sB sC sD sE sF : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {ipins : List INatOpPinSet} {fe' : IFEnv}
    (hA : internReservedPins (AState.init EStore.empty) = .ok ((), sA))
    (hB : builtinPreludeE inProcessModeller sA = .ok (.ok pre, sB))
    (hC : parseChunks inProcessModeller chunks true false sB = .ok (.ok r, sC))
    (hD : preparePrelude pre r.decls sC = .ok (ds, sD))
    (hE : internAllPins pins sD = .ok (ipins, sE))
    (hF : installThenCheck .verified ipins ds sE = .ok (.ok fe', sF)) :
    ∃ env', denoteFEnv sF.store fe' = some env' ∧
      Nonempty (ConLeche.Model.EnvModelM V .verified env') := by
  obtain ⟨-, hfold, hipins, hpps, hpd, dsP, hden⟩ :=
    stages_frame hbytes hA hB hC hD hE
  obtain ⟨env', F', hdenF, hpure⟩ :=
    Arena.installThenCheck_bridge rfl hk hind hpps hfold hipins hpd hden hF
  exact ⟨env', hdenF,
    ConLeche.Model.checkDeclsPure_sound_of (V := V) (pins := pins) rfl hpure⟩

end Twin

/-! ## 2. The Rust side: the six stages, walked into the twin by Theorem 2 -/

section Rust

open ConRon.Refine2 ConRon.Refine2.Frontend

/-- **The start state** (task #97-COMPOSE's mismatch 2, a named hypothesis
until task #97-P5-Top).  The Rust driver's `AState::init(EStore::empty())`,
read through `PersTier::empty()`, is related to the twin driver's
`AState.init EStore.empty` and satisfies the Rust-side invariant —
`Refine2/Checker/Init.lean`'s `init_rel`, which also gives the two flag facts
the first stage needs (`PersUnfrozen`, scratch closed). -/
def InitRel : Prop :=
  ∀ (pers : arena.store.PersTier) (est : arena.store.EStore)
    (st : arena.monad.AState),
    arena.store.PersTier.empty = ok pers → arena.store.EStore.empty = ok est →
    arena.monad.AState.init est = ok st →
    AStateRel pers st (ConRon.Arena.AState.init ConRon.Arena.EStore.empty) ∧
      AStateInv pers st

theorem initRel : InitRel := fun _ _ _ _ hest hst =>
  ⟨(init_rel hest hst).1, (init_rel hest hst).2.1⟩

/-- **The Rust pipeline, walked into the twin.**  Six accepting Rust runs from
the driver's start state give six accepting twin runs from the twin's, at the
abstracted values, with the Rust's final state related to the twin's and the
Rust's environment related to the twin's.

Theorem 2's six top lemmas, one per stage, and `BrOK` at the fold's entry from
`stages_frame` (the twin's frame: the scratch tier is closed after the
startup walk) and `AStateRel.storeWF`. -/
theorem rust_stages
    (hfn : FrozenNative)
    (hbytes : ConRon.Arena.Frontend.preludeText =
      ConLeche.Frontend.builtinPreludeText.toUTF8)
    (hsc : ScanSpec)
    {G : Type} {inst : frontend.types.Modeller G} {m : G}
    (hmr : ConRon.Refine2.Frontend.ModellerRefines inst m
      ConRon.Arena.Frontend.inProcessModeller)
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    {text : Slice Std.U8}
    (hdec : kernel.pins_decode.decode text = ok (.Ok pins))
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
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
    (h3 : frontend.export_c.parse_chunks inst pers m st2 chunks true false
      = ok (.Ok r, st3))
    (h4 : frontend.prepare.prepare_prelude pers st3 pre r.decls = ok (.Ok ds, st4))
    (h5 : arena.checker.intern_all_pins pers st4 pins = ok (.Ok ipins, st5))
    (h6 : arena.checker.install_then_check pers st5 .Verified ipins ds
      = ok (.Ok fe, st6)) :
    ∃ (sA sB sC sD sE sF : ConRon.Arena.AState)
      (rv : ConRon.Arena.Frontend.ParseResultD) (lfe : ConRon.Arena.IFEnv),
      ConRon.Arena.internReservedPins
          (ConRon.Arena.AState.init ConRon.Arena.EStore.empty) = .ok ((), sA) ∧
      ConRon.Arena.Frontend.builtinPreludeE ConRon.Arena.Frontend.inProcessModeller sA
          = .ok (.ok (absPreludeIx pre), sB) ∧
      ConRon.Arena.Frontend.parseChunks ConRon.Arena.Frontend.inProcessModeller
          (absChunks chunks) true false sB = .ok (.ok rv, sC) ∧
      ConRon.Arena.Frontend.preparePrelude (absPreludeIx pre) rv.decls sC
          = .ok ((absIDeclL ds).toArray, sD) ∧
      ConRon.Arena.internAllPins (ConRon.Refine.absPins pins) sD
          = .ok (absINatOpPinSetL ipins, sE) ∧
      ConRon.Arena.installThenCheck .verified (absINatOpPinSetL ipins)
          (absIDeclL ds).toArray sE = .ok (.ok lfe, sF) ∧
      AStateRel pers st6 sF ∧ IFEnvRel fe lfe := by
  obtain ⟨hrel0, hinv0, hfr0, -⟩ := init_rel (pers := pers) hest hst0
  -- 1. the reserved pins
  obtain ⟨sA, hA, hrelA, hinvA, -, -⟩ :=
    (intern_reserved_pins_refines hrel0 hinv0 hfr0 h1).dest
  -- 2. the prelude
  obtain ⟨preL, sB, hB, hpreL, hrelB, hinvB, -⟩ :=
    builtin_prelude_e_refines hsc hmr hrelA hinvA h2
  subst hpreL
  -- 3. the stream
  obtain ⟨rv, sC, hC, hrv, hrelC, hinvC, -⟩ :=
    parse_chunks_refines hsc hmr hrelB hinvB h3
  -- 4. the preparation
  obtain ⟨sD, hD, hrelD, hinvD, -, -⟩ :=
    (prepare_prelude_refines hrelC hinvC h4).dest
  -- 5. the startup pin walk
  obtain ⟨sE, hE, hrelE, hinvE, -, -⟩ :=
    (intern_all_pins_refines hrelD hinvD
      (ConRon.Refine.PinsWF.decode_wf_refine2 hdec) h5).dest
  -- the fold's entry: the twin's scratch tier is closed there
  have hdecls : rv.decls = absIDeclArr r.decls := hrv.decls
  have hD' : ConRon.Arena.Frontend.preparePrelude (absPreludeIx pre) rv.decls sC
      = .ok ((absIDeclL ds).toArray, sD) := by
    rw [hdecls]; exact hD
  have hoff : sE.store.scratchOn = false :=
    (stages_frame (pins := ConRon.Refine.absPins pins) hbytes hA hB hC
      hD' hE).1
  -- 6. the fold
  have hF := install_then_check_refines hrelE hinvE ⟨hrelE.storeWF, hoff⟩ hfn h6
  obtain ⟨lfe, sF, hF, hfe, hrelF, -, -⟩ := hF
  exact ⟨sA, sB, sC, sD, sE, sF, rv, lfe, hA, hB, hC, hD', hE, hF, hrelF, hfe⟩

end Rust

/-! ## 3. The two headline theorems -/

section Headline

open ConRon.Refine2 ConRon.Refine2.Frontend

/-- con-leche: ConLeche/Model/Fold.lean:254 checkDeclsPure_sound_of —
**THE MAIN THEOREM FOR THE RUST CHECKER** (DESIGN.md §1, §8.2): every
environment the Aeneas model of the Rust pipeline accepts has a model, in
every set theory.

The environment is the Rust's own `IFEnv`, read through the twin: Theorem 2
relates it (`IFEnvRel`) to a twin environment in a twin state related to the
Rust's final state (`AStateRel`), and Theorem 1's denotation of that twin
environment is what the model is of.  (The arena has no Rust-level
abstraction FUNCTION to con-leche's `Env` — the store is abstracted by a
relation — so "the model of the Rust environment" can only be spelled through
the twin.  The original campaign's `absEnv e` has no counterpart.)

Composition only: `rust_stages` (Theorem 2), `stages_model` (Theorem 1 +
con-leche). -/
theorem model_exists (V : Type w) [ConLeche.SetTheory V]
    (hfn : FrozenNative)
    (hk : ConRon.Bridge.CoreSpec .verified ConRon.Arena.checkFuel)
    (hind : ConRon.Bridge.IndSpec .verified)
    (hbytes : ConRon.Arena.Frontend.preludeText =
      ConLeche.Frontend.builtinPreludeText.toUTF8)
    (hsc : ScanSpec)
    {G : Type} {inst : frontend.types.Modeller G} {m : G}
    (hmr : ConRon.Refine2.Frontend.ModellerRefines inst m
      ConRon.Arena.Frontend.inProcessModeller)
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    {text : Slice Std.U8}
    (hdec : kernel.pins_decode.decode text = ok (.Ok pins))
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
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
    (h3 : frontend.export_c.parse_chunks inst pers m st2 chunks true false
      = ok (.Ok r, st3))
    (h4 : frontend.prepare.prepare_prelude pers st3 pre r.decls = ok (.Ok ds, st4))
    (h5 : arena.checker.intern_all_pins pers st4 pins = ok (.Ok ipins, st5))
    (h6 : arena.checker.install_then_check pers st5 .Verified ipins ds
      = ok (.Ok fe, st6)) :
    ∃ (lst : ConRon.Arena.AState) (lfe : ConRon.Arena.IFEnv) (env : ConLeche.Env),
      AStateRel pers st6 lst ∧ IFEnvRel fe lfe ∧
      ConRon.Bridge.denoteFEnv lst.store lfe = some env ∧
      Nonempty (ConLeche.Model.EnvModelM V .verified env) := by
  obtain ⟨sA, sB, sC, sD, sE, sF, rv, lfe, hA, hB, hC, hD, hE, hF, hrelF, hfe⟩ :=
    rust_stages hfn hbytes hsc hmr hdec hpers hest hst0 h1 h2 h3 h4 h5 h6
  obtain ⟨env, hden, hmod⟩ := stages_model V hk hind hbytes hA hB hC hD hE hF
  exact ⟨sF, lfe, env, hrelF, hfe, hden, hmod⟩

/-- con-leche: ConLeche/MainTheorem.lean:110 no_False_declaration — **A FILE
THAT DECLARES A THEOREM OF TYPE `False` IS REJECTED BY THE RUST CHECKER**:
the Aeneas model of the Rust pipeline does not accept it.  The same letter as
`conron.no_False_declaration` (`proof/ConRon/RefineOld/Main.lean:730`), at
(C).

Composition only: `rust_stages` (Theorem 2) turns the six Rust runs into six
twin runs, `runPipeline_ok_of_stages` reassembles them into an accepting
`Arena.runPipeline`, and Theorem 1's `Arena.no_False_declaration_pipeline`
(which is con-leche's `no_proof_of_False_pure` through the bridge) refutes
it. -/
theorem no_False_declaration (V : Type w) [ConLeche.SetTheory V]
    (hfn : FrozenNative)
    (hk : ConRon.Bridge.CoreSpec .verified ConRon.Arena.checkFuel)
    (hind : ConRon.Bridge.IndSpec .verified)
    (hbytes : ConRon.Arena.Frontend.preludeText =
      ConLeche.Frontend.builtinPreludeText.toUTF8)
    (hsc : ScanSpec)
    {G : Type} {inst : frontend.types.Modeller G} {m : G}
    (hmr : ConRon.Refine2.Frontend.ModellerRefines inst m
      ConRon.Arena.Frontend.inProcessModeller)
    {pins : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    {text : Slice Std.U8}
    (hdec : kernel.pins_decode.decode text = ok (.Ok pins))
    {chunks : alloc.vec.Vec (alloc.vec.Vec Std.U8)}
    (hfalse : ConLeche.jsonWithTheoremFalse (absChunks chunks))
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
    (h3 : frontend.export_c.parse_chunks inst pers m st2 chunks true false
      = ok (.Ok r, st3))
    (h4 : frontend.prepare.prepare_prelude pers st3 pre r.decls = ok (.Ok ds, st4))
    (h5 : arena.checker.intern_all_pins pers st4 pins = ok (.Ok ipins, st5))
    (h6 : arena.checker.install_then_check pers st5 .Verified ipins ds
      = ok (.Ok fe, st6)) :
    False := by
  obtain ⟨sA, sB, sC, sD, sE, sF, rv, lfe, hA, hB, hC, hD, hE, hF, -, -⟩ :=
    rust_stages hfn hbytes hsc hmr hdec hpers hest hst0 h1 h2 h3 h4 h5 h6
  obtain ⟨n, hn⟩ := runPipeline_ok_of_stages hA hB hC hD hE hF
  obtain ⟨e, he⟩ := ConRon.Bridge.Frontend.Arena.no_False_declaration_pipeline V
    hk hind hbytes (ConRon.Refine.absPins pins) (absChunks chunks) hfalse
  rw [hn] at he
  exact nomatch he

end Headline

/-! ## 4. The census

`#print axioms` of the two roots: `sorryAx` is the tiers' open leaves, and
the named hypotheses above are the rest of the ledger. -/

/-- info: 'ConRon.Capstone.model_exists' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms model_exists

/-- info: 'ConRon.Capstone.no_False_declaration' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms no_False_declaration

end ConRon.Capstone

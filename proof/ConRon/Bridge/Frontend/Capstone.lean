/-
# `ConRon.Bridge.Frontend.Capstone` — **the byte-level capstone at (B)**

DESIGN §8.2: *"the capstones are the same letters as today's
`conron.no_False_declaration`, at (B)."*  This module is that letter — the
one a reader can check without knowing what an `Env` is:

> a file whose chunks are one of the shapes `ConLeche.jsonWithTheoremFalse`
> describes is never accepted by the Lean arena checker.

`Bridge/Checker/Capstone.lean` is the letter at the FOLD (`Arena.model_exists`
and its two corollaries, at a declaration list); this one is the letter at the
BYTES, and the distance between them is exactly this tier: the parse's
exactness, the preparation's, and the prelude.

## The assembly, four steps, one theorem each

The original campaign's `conron.no_False_declaration`
(`proof/ConRon/RefineOld/Main.lean:730`) is four steps and this is the same
four, with the arena's own theorems in place of the port's:

| step | the original | here |
|---|---|---|
| 1. the parse holds the record | `parse_chunks_refines_of_modeller` + `ParseResultSim.decls` | `Bridge/Frontend/Chunks.lean`'s `parseChunks_exact` |
| 2. the preparation keeps it | `prepare_prelude_refines` + `mem_preparePrelude` | `Bridge/Frontend/Prepare.lean`'s `mem_preparePrelude_denote` |
| 3. the twin's accept is con-leche's | `check_decls_verified_refines_ok` | `Bridge/Checker/Split.lean`'s `Arena.installThenCheck_bridge` |
| 4. con-leche refutes it | `ConLeche.no_False_theorem_accepted` | `checkDeclsPure_thmDecl_const` + `ConLeche.Model.no_proof_of_False_pure` |

**Step 4 is the one that is not a transport**, and §3 below says why: con-leche
states its stream ingredient at the CACHED fold (`Cached.checkDecls_thmDecl_const`,
`Verify/Cached/StreamThm.lean:183`) and the arena's bridge lands on the PURE
one, so the pure-tier twin of that one lemma has to be stated here.

## Two savings the arena rewrite buys this statement

**No `absChunks`.**  `Arena.Frontend.parseChunks` takes `List ByteArray` and so
does con-leche's, so the hypothesis is literally
`ConLeche.jsonWithTheoremFalse chunks` where the original had to write
`ConLeche.jsonWithTheoremFalse (Frontend.absChunks chunks)`.

**No scanner tier.**  The twin CALLS `scanLineFwd`; the port had to
re-implement it, and proving the re-implementation right was five files and
~15 000 lines with two standing obligations (`Utf8DecodeSpec`,
`UnescapeSpec`).  Neither obligation exists here.

## The named hypotheses

Four, and every one of them is a hypothesis of the STATEMENT rather than an
axiom of the environment — which is what makes "four named hypotheses" a
checkable claim (`#print axioms` in `Bridge/Frontend/Axioms.lean` shows none
of them):

* `hk : CoreSpec .verified Arena.checkFuel` — the Core tier's
  (`Bridge/Core/**`; its `knot` field is already discharged by
  `Bridge/Core/Induction.lean`'s `knot_spec_checkFuel`);
* `hind : IndSpec .verified` — the Inductives tier's;
* `hmw : ModellerWF md` and `hmr : ModellerRefines md` — the seam's two
  promises (`Bridge/Frontend/Modeller.lean`), the twins of
  `conron.no_False_declaration`'s own `hgen` and `hmr`.  At the instantiation
  the driver runs they are THEOREMS (`inProcessModeller_wf`,
  `inProcessModeller_refines`), because that instantiation delegates to
  con-leche's own generator — which is why
  `Arena.no_False_declaration_pipeline` carries neither.
-/
import ConRon.Bridge.Frontend.Prepare
import ConRon.Arena.Main
import ConLeche.MainTheorem

namespace ConRon.Bridge.Frontend

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend

universe w

/-! ## 1. The post-parse state

`Bridge/Checker/Capstone.lean`'s §8 asks the frontend tier for three things.
Two are `Bridge/Frontend/Chunks.lean`'s `parseChunks_exact` (the denotation
and the persistence); the third is this. -/

/-- con-leche: ConLeche/Verify/Cached/BridgeC.lean:609 checkDeclStepC_run —
**the fold's start invariant, at the post-parse state**: the state the driver
hands `installThenCheck` satisfies `FoldOK` at the empty environment.

Its four halves, and what each costs:

* `CheckOK` — `StateOK` is `ParseStep`'s, `PinsOK` is
  `Bridge/Checker/Pins.lean`'s `internReservedPins_run`, `CacheOK` is
  vacuous at the empty per-declaration tables the parse never writes
  (`ParseStep.caches`), and `IFEnvOK Env.empty (mkIFEnv IEnv.empty)` is
  `Bridge/Checker/Inv.lean`'s `IFEnvOK_of_denote` at the empty index;
* `EnvWF Env.empty` — immediate;
* `PersPins` — `internReservedPins_run`, carried by `PinsOK.mono`;
* `PersIFEnv` / `IFEnvCoh` / `denoteFEnv … = some Env.empty` — all three are
  `rfl`-level at `mkIFEnv IEnv.empty`.

`sorry`: the four halves as listed, over `internReservedPins_run` (which is
the Checker tier's own item 13) and `ParseStep`'s frame.  Task
#97-P3-Frontend's sorry list, item 23. -/
theorem FoldOK_post_parse {μ : CheckMode} {s s' : AState}
    (hpins : PinsOK s) (hpp : PersPins s) (hstep : ParseStep s s') :
    FoldOK μ Env.empty (mkIFEnv IEnv.empty) s' := by
  sorry

/-! ## 2. The pure fold's stream ingredient

con-leche proves *"an accepted stream that declares a theorem of a bare
constant type leaves a constant of that type in the environment"* at the
CACHED fold (`Cached.checkDecls_thmDecl_const`, `Verify/Cached/StreamThm.lean:183`,
through `installRun_thmDecl_const` and `annotStepC_thm_consts`).  The arena's
bridge (`Bridge/Checker/Fold.lean`, `Bridge/Checker/Split.lean`) lands on
`ConLeche.checkDeclsPure`, so the pure twin of that lemma is what this
capstone needs and it is the one thing on the path con-leche does not already
have.

**It is a con-leche-tier lemma, not an arena one**, and it belongs beside the
original — the note is here so that whoever takes it knows where it goes. -/

/-- con-leche: ConLeche/Verify/Cached/StreamThm.lean:183 checkDecls_thmDecl_const
— **the same lemma at the PURE fold**: an accepted `checkDeclsPure` run of a
stream that declares a theorem of a bare constant type leaves a constant of
that type in the environment.

`sorry`: the `foldlM` induction over `checkDecl`, with the `thmDecl` arm
pushing `ConstantInfo.thmInfo ⟨cv.name, cv.levelParams, .const n ls⟩ value`
(con-leche's `annotStepC_thm_consts` is that step at the cached tier, and
`annotate_const_of_miss` is why the annotated type of a bare constant is
itself) and the rest of the fold only extending the constant list
(`installRun_trace`'s `PushChain` at the pure tier).  Task #97-P3-Frontend's
sorry list, item 24. -/
theorem checkDeclsPure_thmDecl_const {μ : CheckMode} {F : Nat}
    {pins : List NatOpPinSet} {ds : List Declaration} {env' : Env}
    {cv : ConstantVal} {value : Expr} {n : ConLeche.Name} {ls : List Level}
    (hty : cv.type = .const n ls) (hmem : Declaration.thmDecl cv value ∈ ds)
    (h : ConLeche.checkDeclsPure μ (ConLeche.fueledOps μ F) pins ds = .ok env') :
    ∃ c ∈ env'.consts, c.toConstantVal.type = .const n ls := by
  sorry

/-- con-leche: ConLeche/Verify/Cached/StreamThm.lean:207 no_False_theorem_accepted
— **the same letter at the PURE fold**: a stream that declares a theorem of
type `False` is never accepted.  con-leche's own two steps, at the pure tier:
the record's constant survives the run, and in the model of the main theorem
its type denotes the empty set. -/
theorem no_False_theorem_accepted_pure (V : Type w) [ConLeche.SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {pins : List NatOpPinSet} {ds : List Declaration} {env' : Env}
    {cv : ConstantVal} {value : Expr}
    (hmem : Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = .const ConLeche.falseName [])
    (h : ConLeche.checkDeclsPure μ (ConLeche.fueledOps μ F) pins ds = .ok env') :
    False := by
  obtain ⟨c, hc, hcty⟩ := checkDeclsPure_thmDecl_const hty hmem h
  exact ConLeche.Model.no_proof_of_False_pure (V := V) (pins := pins) hμ h c hc hcty

/-! ## 3. The capstone, prelude-parametric -/

/-- con-leche: ConLeche/MainTheorem.lean:110 no_False_declaration —
**A FILE THAT DECLARES A THEOREM OF TYPE `False` IS REJECTED BY THE LEAN ARENA
CHECKER** (DESIGN §8.2's capstone, at (B)), the same letter as
`conron.no_False_declaration` (`proof/ConRon/RefineOld/Main.lean:730`).

Parametric in the prelude, as the original is: `hpre` is the twin's own parse
of *some* prelude bytes, never identified with con-leche's `builtinPreludeE`
(`Arena.no_False_declaration_prelude` is the instance at the one the binary
ships).  The reason is the original's: `mem_preparePrelude` holds for *every*
`pre`, so the statement is prelude-parametric for free.

It carries `hk`, `hind` (the Core and Inductives tiers'), `hmw`, `hmr` (the
modeller's two promises), the four runs of the twin's own pipeline, and **no
hypothesis about well-formedness at all** — `StateOK` at the start and the
scratch tier being closed are the driver's, and everything downstream of them
is a theorem of this tier.

`sorry`: the four steps of the module note, composed.  Every ingredient is
stated; what is open is what each ingredient is open on.  Task
#97-P3-Frontend's sorry list, item 25. -/
theorem Arena.no_False_declaration (V : Type w) [ConLeche.SetTheory V]
    {md : Modeller} (hmw : ModellerWF md) (hmr : ModellerRefines md)
    (hk : CoreSpec .verified Arena.checkFuel) (hind : IndSpec .verified)
    {chunks : List ByteArray}
    (hfalse : ConLeche.jsonWithTheoremFalse chunks)
    {pins : List NatOpPinSet} {ipins : List INatOpPinSet}
    {preBytes : ByteArray} {im ce : Bool}
    {s0 s1 s2 s3 s4 : AState} {preR : ParseResultD} {r : ParseResultD}
    {ds : Array IDeclaration} {fe' : IFEnv}
    (hok0 : StateOK s0) (hoff0 : s0.store.scratchOn = false)
    (hpins0 : PinsOK s0) (hpp0 : PersPins s0)
    (hipins : PinsDenote s3.store ipins pins) (hpps : PersPinSets ipins)
    (hpre : parseBytes md preBytes true false s0 = .ok (.ok preR, s1))
    (hparse : parseChunks md chunks im ce s1 = .ok (.ok r, s2))
    (hprep : preparePrelude ⟨preR.decls⟩ r.decls s2 = .ok (ds, s3))
    (hrun : Arena.installThenCheck .verified ipins ds s3 = .ok (.ok fe', s4)) :
    False := by
  sorry

/-- con-leche: ConLeche/MainTheorem.lean:110 no_False_declaration —
`Arena.no_False_declaration` at the prelude the binary ships,
`Arena/Frontend/Prelude.lean`'s `builtinPreludeE`.  The pairing is the
original's (`conron.no_False_declaration` /
`conron.no_False_declaration_prelude`, `RefineOld/Main.lean:730` / `:782`).

The extra hypothesis `hbytes` is the PRELUDE GATE, not a proof obligation:
`Arena/Frontend/PreludeText.lean`'s committed constant is generated from
con-leche's own `pins/leanprover-lean4-v4.33.0.prelude.ndjson` by
`scripts/gen-prelude-lean.sh`, and `scripts/gen-prelude-lean.sh --check` is
step 11 of `scripts/gates.sh`.  Naming it as a hypothesis is what keeps the
axiom census at Lean's own three — the same move the original made for
`PINS_TEXT`, and the reason its `_prelude` pair cost nothing.

`sorry`: `builtinPreludeE_run` in place of `hpre`, then
`Arena.no_False_declaration`.  Task #97-P3-Frontend's sorry list, item 25. -/
theorem Arena.no_False_declaration_prelude (V : Type w) [ConLeche.SetTheory V]
    {md : Modeller} (hmw : ModellerWF md) (hmr : ModellerRefines md)
    (hk : CoreSpec .verified Arena.checkFuel) (hind : IndSpec .verified)
    (hbytes : preludeText = ConLeche.Frontend.builtinPreludeText.toUTF8)
    {chunks : List ByteArray}
    (hfalse : ConLeche.jsonWithTheoremFalse chunks)
    {pins : List NatOpPinSet} {ipins : List INatOpPinSet} {im ce : Bool}
    {s0 s1 s2 s3 s4 : AState} {pre : PreludeIx} {r : ParseResultD}
    {ds : Array IDeclaration} {fe' : IFEnv}
    (hok0 : StateOK s0) (hoff0 : s0.store.scratchOn = false)
    (hpins0 : PinsOK s0) (hpp0 : PersPins s0)
    (hipins : PinsDenote s3.store ipins pins) (hpps : PersPinSets ipins)
    (hpre : builtinPreludeE md s0 = .ok (.ok pre, s1))
    (hparse : parseChunks md chunks im ce s1 = .ok (.ok r, s2))
    (hprep : preparePrelude pre r.decls s2 = .ok (ds, s3))
    (hrun : Arena.installThenCheck .verified ipins ds s3 = .ok (.ok fe', s4)) :
    False := by
  sorry

/-! ## 4. The capstone at the seam

`Arena/Main.lean`'s own module note names `runPipeline` **THE ONE SEAM**:

    runPipeline : List ByteArray → CheckMode → List NatOpPinSet
                → Except CheckError Nat

Everything below the command line is that function, so a statement about it is
a statement about the binary's accept path with nothing left between — which
is exactly the shape con-leche's own `no_False_declaration`
(`ConLeche/MainTheorem.lean:110`) has, and which the original campaign could
NOT have, because the port's driver is an unverified Rust crate and its
calling order had to stay a trusted line ("the driver: that `con_ron::driver`
calls `parse_chunks`, `prepare_prelude` and `check_decls` on the stream it was
handed, in this order").

**Here that line is gone**: `runPipeline` is the composition, in Lean, and the
theorem is about it.  That is the strongest form of the capstone the arena
rewrite can state at (B), and the modeller's two promises are not hypotheses
of it — `runPipeline` fixes `Frontend.inProcessModeller`, which delegates to
con-leche's own generator (`Bridge/Frontend/Modeller.lean`'s
`inProcessModeller_wf` / `_refines`). -/

/-- con-leche: ConLeche/MainTheorem.lean:110 no_False_declaration — **THE
BYTE-LEVEL CAPSTONE, AT THE SEAM**: a file whose chunks are one of the shapes
`jsonWithTheoremFalse` describes makes the Lean arena checker's whole pipeline
— the reserved pins, the built-in prelude, the streaming parse, the
preparation and the two-phase fold — return an error.

Two named hypotheses (`CoreSpec`, `IndSpec`) and one gate (`hbytes`, the
prelude's committed bytes; `scripts/gen-prelude-lean.sh --check`, step 10 of
`scripts/gates.sh`).

`sorry`: `runPipelineM` unfolded into its three stages
(`internReservedPins_run`, `builtinPreludeE_run`, `parseChunksGo_run` after
`StateD_init_run`, `preparePrelude_run`, `internAllPins_run`,
`Arena.installThenCheck_bridge`), then `Arena.no_False_declaration_prelude`.
Task #97-P3-Frontend's sorry list, item 26 — the tier's headline. -/
theorem Arena.no_False_declaration_pipeline (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec .verified Arena.checkFuel) (hind : IndSpec .verified)
    (hbytes : preludeText = ConLeche.Frontend.builtinPreludeText.toUTF8)
    (pins : List NatOpPinSet) (chunks : List ByteArray)
    (hfalse : ConLeche.jsonWithTheoremFalse chunks) :
    ∃ e, Arena.runPipeline chunks .verified pins = .error e := by
  sorry

end ConRon.Bridge.Frontend

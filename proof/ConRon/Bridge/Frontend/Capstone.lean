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
re-implement it, and proving the re-implementation right was seven files and
17 479 lines with two standing obligations (`Utf8DecodeSpec`,
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
  `Bridge/Checker/Pins.lean`'s `internReservedPins_run`, `CacheOK` is the
  fourth hypothesis, and `IFEnvOK Env.empty (mkIFEnv IEnv.empty)` is
  `Bridge/Checker/Inv.lean`'s `IFEnvOK_of_denote` at the empty index;
* `EnvWF Env.empty` — immediate;
* `PersPins` — `internReservedPins_run`, carried by `PinsOK.mono`;
* `PersIFEnv` / `IFEnvCoh` / `denoteFEnv … = some Env.empty` — all three are
  `rfl`-level at `mkIFEnv IEnv.empty`.

**The fourth hypothesis is the driver's own start**, and it was missing from
the round-one statement: what the parse gives is that the per-declaration
tables did not MOVE, not that they were empty.  `AState.init` sets them empty
(`Arena/Monad.lean:146`), so the driver has it; a statement about an arbitrary
start state has to say so.

*(Task #97-P3-Frame turned it from `s.caches = Caches.empty` into `CacheOK`
itself.  The parse is not cache-neutral after all — the owner census compares
two levels, see `Bridge/Frontend/Rel.lean`'s frame note — so "the tables are
empty" does not survive a `ParseStep`, while `CacheOK` does, through
`CheckOK.monoF`.  `CacheOK.of_empty` is what the driver reaches it with and is
one line at each of the two call sites.)* -/
theorem FoldOK_of_start {μ : CheckMode} {s : AState} (hok : StateOK s)
    (hpins : PinsOK s) (hpp : PersPins s) (hc : CacheOK μ Env.empty s) :
    FoldOK μ Env.empty (mkIFEnv IEnv.empty) s where
  check :=
    { state := hok
      caches := hc
      pins := hpins
      ienv := IFEnvOK_of_denote (μ := μ) hok rfl
        (by intro t hn
            simp [mkIFEnv, IEnv.empty] at hn) rfl }
  envWF := by intro c hc'; exact absurd hc' (by simp [Env.empty])
  persPins := hpp
  persEnv := { env := by intro c hc'; simp [mkIFEnv, IEnv.empty] at hc'
               idx := by intro n p hn; simp [mkIFEnv, mkIFEnvGo, IEnv.empty] at hn }
  coh := rfl
  denote := rfl

/-- con-leche: ConLeche/Verify/Cached/BridgeC.lean:609 checkDeclStepC_run —
`FoldOK_of_start` at the far end of a `ParseStep`: the parse only interns, so
the pin table, the per-declaration caches and the persistence all stand
still. -/
theorem FoldOK_post_parse {μ : CheckMode} {s s' : AState}
    (hpins : PinsOK s) (hpp : PersPins s) (hc : s.caches = Caches.empty)
    (hstep : ParseStep s s') :
    FoldOK μ Env.empty (mkIFEnv IEnv.empty) s' :=
  FoldOK_of_start hstep.ok (hpins.mono hstep.ext hstep.pins)
    (hpp.mono hstep.pins)
    ((CacheOK.of_empty hc).monoF hstep.ext hstep.cframe)

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

/-- con-leche: ConLeche/Kernel/Core.lean:1818 annotateBody — **a bare constant
annotates to itself**, at the PURE knot.  con-leche's `annotate_const_of_miss`
(`Verify/Cached/StreamThm.lean:61`) is this fact at the CACHED knot, where it
costs an argument about the annotation memo missing the key (the step's own
`flushC` is what makes the hit branch unreachable).  The pure knot has no
memo, so the equation is `rfl` at every non-zero fuel and vacuous at zero,
where the knot's base case throws. -/
theorem annotateCore_const {μ : CheckMode} {env : Env} {F : Nat}
    {n : ConLeche.Name} {ls : List Level} {j : Expr}
    (h : ConLeche.annotateCore μ env F 0 (.const n ls) = .ok j) :
    j = .const n ls := by
  cases F with
  | zero =>
    exact absurd h (by
      simp [ConLeche.annotateCore, ConLeche.pureFns, ConLeche.coreKnot,
        throw, throwThe, MonadExceptOf.throw])
  | succ f =>
    have he : ConLeche.annotateCore μ env (f + 1) 0 (Expr.const n ls)
        = .ok (Expr.const n ls) := rfl
    rw [he] at h
    exact (Except.ok.inj h).symm

/-- con-leche: ConLeche/Kernel/Checker.lean:630 checkDeclsPure — **every
PREFIX of an accepted pure run is an accepted pure run**, at the same mode,
the same ops and the same fuel.

`checkDeclsPure` is `ds.foldlM (checkDecl …) Env.empty` and nothing else, so
this is `List.foldlM_append` read left to right.  The CACHED fold is not of
that shape — `Cached.checkDecls` runs two phases over the whole array and
phase B pends every value phase A installed — which is why con-leche's own
stream lemma has to carry the installed constant to the END of the run
(`installRun_trace`'s `PushChain`) and this tier does not. -/
theorem checkDeclsPure_prefix {μ : CheckMode} {F : Nat}
    {pins : List NatOpPinSet} {ds₁ ds₂ : List Declaration} {env' : Env}
    (h : ConLeche.checkDeclsPure μ (ConLeche.fueledOps μ F) pins (ds₁ ++ ds₂)
      = .ok env') :
    ∃ env₁, ConLeche.checkDeclsPure μ (ConLeche.fueledOps μ F) pins ds₁
      = .ok env₁ := by
  simp only [ConLeche.checkDeclsPure, List.foldlM_append, Bind.bind,
    Except.bind] at h ⊢
  cases h₁ : List.foldlM (ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pins)
      Env.empty ds₁ with
  | error e => rw [h₁] at h; exact nomatch h
  | ok env₁ => exact ⟨env₁, rfl⟩

/-- con-leche: ConLeche/Verify/Cached/StreamThm.lean:183 checkDecls_thmDecl_const
— **the same lemma at the PURE fold**: an accepted `checkDeclsPure` run of a
stream that declares a theorem of a bare constant type has an accepted PREFIX
RUN whose environment holds a constant of that type.

The conclusion is the prefix's and not the whole run's, and that is the pure
tier's own saving over con-leche's cached one (`checkDeclsPure_prefix` above):
the record's step is itself the end of an accepted run, so the constant never
has to be carried past it.  What survives of the cached proof is its first two
ingredients — *the annotation of a bare constant is the constant*
(`annotateCore_const`) and *a theorem record is never dropped*
(`declThmRun_of`'s `env₂ = ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ value ::
env.consts⟩`) — and the third, the `PushChain`, is not needed at all.

**It is still a con-leche-tier lemma** and belongs beside the original: the
whole statement is about con-leche's own functions and mentions no handle.
The upstream ask is this file's §5 note. -/
theorem checkDeclsPure_thmDecl_const {μ : CheckMode} {F : Nat}
    {pins : List NatOpPinSet} {ds : List Declaration} {env' : Env}
    {cv : ConstantVal} {value : Expr} {n : ConLeche.Name} {ls : List Level}
    (hty : cv.type = .const n ls) (hmem : Declaration.thmDecl cv value ∈ ds)
    (h : ConLeche.checkDeclsPure μ (ConLeche.fueledOps μ F) pins ds = .ok env') :
    ∃ ds₀ env₀,
      ConLeche.checkDeclsPure μ (ConLeche.fueledOps μ F) pins ds₀ = .ok env₀ ∧
        ∃ c ∈ env₀.consts, c.toConstantVal.type = .const n ls := by
  -- the stream around the record
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hmem
  -- the accepted run of `pre ++ [the record]`
  have hsplit : pre ++ Declaration.thmDecl cv value :: post
      = (pre ++ [Declaration.thmDecl cv value]) ++ post := by simp
  rw [hsplit] at h
  obtain ⟨env₀, h₀⟩ := checkDeclsPure_prefix h
  refine ⟨pre ++ [Declaration.thmDecl cv value], env₀, h₀, ?_⟩
  -- the record's own step, at the environment the prefix left
  simp only [ConLeche.checkDeclsPure, List.foldlM_append, List.foldlM_cons,
    List.foldlM_nil, Bind.bind, Except.bind] at h₀
  cases h₁ : List.foldlM (ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pins)
      Env.empty pre with
  | error e => rw [h₁] at h₀; exact nomatch h₀
  | ok env₁ =>
  rw [h₁] at h₀
  simp only [] at h₀
  cases h₂ : ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pins env₁
      (.thmDecl cv value) with
  | error e => rw [h₂] at h₀; exact nomatch h₀
  | ok env₂ =>
  rw [h₂] at h₀
  simp only [pure, Except.pure, Except.ok.injEq] at h₀
  subst h₀
  -- `DeclThmRun`: the annotated header, and the constant it pushes
  obtain ⟨type', value', hcv, -, -, henv⟩ :=
    ConLeche.Semantics.declThmRun_of (pins := pins) h₂
  obtain ⟨-, -, -, -, -, -, hann, -, -, -⟩ := hcv
  rw [hty] at hann
  obtain rfl : type' = .const n ls := annotateCore_const hann
  refine ⟨ConstantInfo.thmInfo ⟨cv.name, cv.levelParams, .const n ls⟩ value,
    ?_, rfl⟩
  rw [henv]
  exact List.mem_cons_self

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
  obtain ⟨ds₀, env₀, h₀, c, hc, hcty⟩ := checkDeclsPure_thmDecl_const hty hmem h
  exact ConLeche.Model.no_proof_of_False_pure (V := V) (pins := pins) hμ h₀ c hc hcty

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

The four steps of the module note, composed.  Every ingredient is a theorem
of this tier or of the Checker tier; what is open in the composition is what
each ingredient is open on, and nothing more. -/
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
    (hpins0 : PinsOK s0) (hpp0 : PersPins s0) (hcache0 : s0.caches = Caches.empty)
    (hipins : PinsDenote s3.store ipins pins) (hpps : PersPinSets ipins)
    (hpre : parseBytes md preBytes true false s0 = .ok (.ok preR, s1))
    (hparse : parseChunks md chunks im ce s1 = .ok (.ok r, s2))
    (hprep : preparePrelude ⟨preR.decls⟩ r.decls s2 = .ok (ds, s3))
    (hrun : Arena.installThenCheck .verified ipins ds s3 = .ok (.ok fe', s4)) :
    False := by
  -- 1. the prelude's parse and the stream's parse
  obtain ⟨hstep1, hpersPre, preC, -, hrelPre⟩ :=
    parseBytes_run hmw hmr hok0 hoff0 hpre
  obtain ⟨hstep2, hpersR, rc, hclR, hrelR⟩ :=
    parseChunks_run hmw hmr hstep1.ok (by rw [hstep1.scratch, hoff0]) hparse
  -- 2. the preparation
  obtain ⟨hstep3, hpersDs, -, hclPrep⟩ :=
    preparePrelude_run (pre := ⟨preR.decls⟩) (preC := ⟨preC.decls⟩) hstep2.ok
      (by rw [hstep2.scratch, hstep1.scratch, hoff0])
      (denoteDeclArray_ext hstep2.ext hrelPre.decls) hpersPre
      (hrelPre.projNamed.mono hstep2.ext) hrelR.decls
      hpersR hrelR.projNamed hprep
  -- 3. the fold
  obtain ⟨env', F', -, hcheck⟩ :=
    Arena.installThenCheck_bridge rfl hk hind hpps
      (FoldOK_post_parse hpins0 hpp0 hcache0
        ((hstep1.trans hstep2).trans hstep3))
      hipins (fun x hx => hpersDs x (by simpa using hx))
      (denoteDeclArray_iff.mp hclPrep) hrun
  -- 4. con-leche refutes it
  obtain ⟨cv, vl, hty, hmem⟩ :=
    ConLeche.Frontend.parseChunks_jsonWithTheoremFalse hfalse hclR
  exact no_False_theorem_accepted_pure V rfl
    (by
      simpa using ConLeche.Frontend.mem_preparePrelude
        (pre := ⟨preC.decls⟩) hmem)
    hty hcheck

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

`builtinPreludeE_run` in place of `hpre`, then
`Arena.no_False_declaration`. -/
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
    (hpins0 : PinsOK s0) (hpp0 : PersPins s0) (hcache0 : s0.caches = Caches.empty)
    (hipins : PinsDenote s3.store ipins pins) (hpps : PersPinSets ipins)
    (hpre : builtinPreludeE md s0 = .ok (.ok pre, s1))
    (hparse : parseChunks md chunks im ce s1 = .ok (.ok r, s2))
    (hprep : preparePrelude pre r.decls s2 = .ok (ds, s3))
    (hrun : Arena.installThenCheck .verified ipins ds s3 = .ok (.ok fe', s4)) :
    False := by
  obtain ⟨hstep1, hpersPre, hnPre, preC, -, hrelPre⟩ :=
    builtinPreludeE_run hmw hmr hbytes hok0 hoff0 hpre
  obtain ⟨hstep2, hpersR, rc, hclR, hrelR⟩ :=
    parseChunks_run hmw hmr hstep1.ok (by rw [hstep1.scratch, hoff0]) hparse
  obtain ⟨hstep3, hpersDs, -, hclPrep⟩ :=
    preparePrelude_run (preC := preC) hstep2.ok
      (by rw [hstep2.scratch, hstep1.scratch, hoff0])
      (denoteDeclArray_ext hstep2.ext hrelPre) hpersPre
      (hnPre.mono hstep2.ext) hrelR.decls
      hpersR hrelR.projNamed hprep
  obtain ⟨env', F', -, hcheck⟩ :=
    Arena.installThenCheck_bridge rfl hk hind hpps
      (FoldOK_post_parse hpins0 hpp0 hcache0
        ((hstep1.trans hstep2).trans hstep3))
      hipins (fun x hx => hpersDs x (by simpa using hx))
      (denoteDeclArray_iff.mp hclPrep) hrun
  obtain ⟨cv, vl, hty, hmem⟩ :=
    ConLeche.Frontend.parseChunks_jsonWithTheoremFalse hfalse hclR
  exact no_False_theorem_accepted_pure V rfl
    (by simpa using ConLeche.Frontend.mem_preparePrelude (pre := preC) hmem)
    hty hcheck

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
prelude's committed bytes; `scripts/gen-prelude-lean.sh --check`, step 11 of
`scripts/gates.sh`) — **and nothing else**.  Round 2 carried a third,
`InternAllPinsFrame`, for the one conjunct `internAllPins_run` did not state;
task #97-P3-Checker-2 landed the strengthening (`s'.caches = s.caches ∧
s'.memos = s.memos`), so the definition and the hypothesis are gone.
**The modeller's two promises are not hypotheses**: `runPipeline` fixes
`Frontend.inProcessModeller`, and `inProcessModeller_wf` / `_refines` are
theorems about it.

`runPipelineM` unfolded into its stages — `internReservedPins`,
`builtinPreludeE`, `StateD.init`, `parseChunksGo`, `preparePrelude`,
`internAllPins`, `installThenCheck` — and then the four steps of §3's table.
The one place it is NOT `Arena.no_False_declaration_prelude` applied is the
`internAllPins` step, which the letter above does not have between the
preparation and the fold; the fold's start invariant is re-established at the
state that walk leaves, off that walk's own `caches` frame.

The start state is `AState.init EStore.empty`, so `StateOK`, the closed
scratch tier and the empty caches are all `Arena/WFProofs.lean`'s
`EStore.empty_wf` and `rfl`: **this letter takes no hypothesis about
well-formedness at all.** -/
theorem Arena.no_False_declaration_pipeline (V : Type w) [ConLeche.SetTheory V]
    (hk : CoreSpec .verified Arena.checkFuel) (hind : IndSpec .verified)
    (hbytes : preludeText = ConLeche.Frontend.builtinPreludeText.toUTF8)
    (pins : List NatOpPinSet) (chunks : List ByteArray)
    (hfalse : ConLeche.jsonWithTheoremFalse chunks) :
    ∃ e, Arena.runPipeline chunks .verified pins = .error e := by
  by_cases hex : ∃ e, Arena.runPipeline chunks .verified pins = .error e
  · exact hex
  exfalso
  cases hres : Arena.runPipeline chunks .verified pins with
  | error e => exact hex ⟨e, hres⟩
  | ok n =>
  rw [ConRon.Arena.runPipeline] at hres
  cases hm : (ConRon.Arena.runPipelineM Frontend.inProcessModeller .verified pins
      chunks).run (AState.init EStore.empty) with
  | error e2 => rw [hm] at hres; exact absurd hres (by simp)
  | ok q =>
  obtain ⟨res, sF⟩ := q
  rw [hm] at hres
  simp only [] at hres
  -- the start state
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  have hoff0 : (AState.init EStore.empty).store.scratchOn = false := rfl
  have hc0 : (AState.init EStore.empty).caches = Caches.empty := rfl
  -- the head: the reserved pins, the prelude, the initial parse state
  rw [ConRon.Arena.runPipelineM] at hm
  obtain ⟨hd, s1, hhead, hrest⟩ := AM.bind_ok hm
  cases hd with
  | error p2 =>
    simp only [] at hrest
    obtain ⟨hv, -⟩ := AM.pure_ok hrest
    rw [hv] at hres; exact absurd hres (by simp)
  | ok pr =>
  obtain ⟨pre, st0⟩ := pr
  simp only [] at hrest
  obtain ⟨pd, s2, hgo, hrest2⟩ := AM.bind_ok hrest
  cases pd with
  | error p3 =>
    simp only [] at hrest2
    obtain ⟨hv, -⟩ := AM.pure_ok hrest2
    rw [hv] at hres; exact absurd hres (by simp)
  | ok r0 =>
  simp only [] at hrest2
  -- unfold the head
  rw [ConRon.Arena.runPipelineHead] at hhead
  obtain ⟨u, sA, hpinsrun0, hhead2⟩ := AM.bind_ok hhead
  obtain ⟨hokA, hxA, hpinsA, hppA, hoffA, hmemosA, hcachesA⟩ :=
    internReservedPins_run hok0 hoff0 hpinsrun0
  obtain ⟨y, sB, hprel, hhead3⟩ := AM.bind_ok hhead2
  cases y with
  | error e3 =>
    simp only [] at hhead3
    exact absurd (AM.pure_ok hhead3).1 (by simp)
  | ok preIx =>
  simp only [] at hhead3
  obtain ⟨st1, sC, hinit, hhead4⟩ := AM.bind_ok hhead3
  obtain ⟨hv4, hs4⟩ := AM.pure_ok hhead4
  simp only [Except.ok.injEq, Prod.mk.injEq] at hv4
  obtain ⟨hpre', hst'⟩ := hv4
  subst hpre'; subst hst'; subst hs4
  -- the parse, reassembled from `StateD.init` and `parseChunksGo`
  have hparse : parseChunks Frontend.inProcessModeller chunks true false sB
      = .ok (.ok r0, s2) := by
    rw [parseChunks, AM.bind_apply, hinit]
    exact hgo
  -- the tail: the preparation, the pins, the fold
  rw [ConRon.Arena.runPipelineTail] at hrest2
  obtain ⟨ds, s3, hprep, htail2⟩ := AM.bind_ok hrest2
  obtain ⟨ipins, s3', hpinsrun, htail3⟩ := AM.bind_ok htail2
  obtain ⟨z, s4, hcheck, htail4⟩ := AM.bind_ok htail3
  cases z with
  | error p5 =>
    simp only [] at htail4
    obtain ⟨hv, -⟩ := AM.pure_ok htail4
    rw [hv] at hres; exact absurd hres (by simp)
  | ok fe' =>
  -- §3's four steps, with the pin walk in the middle
  obtain ⟨hstep1, hpersPre, hnPre, preC, -, hrelPre⟩ :=
    builtinPreludeE_run inProcessModeller_wf inProcessModeller_refines hbytes
      hokA hoffA hprel
  obtain ⟨hstep2, hpersR, rc, hclR, hrelR⟩ :=
    parseChunks_run inProcessModeller_wf inProcessModeller_refines hstep1.ok
      (by rw [hstep1.scratch, hoffA]) hparse
  obtain ⟨hstep3, hpersDs, -, hclPrep⟩ :=
    preparePrelude_run (preC := preC) hstep2.ok
      (by rw [hstep2.scratch, hstep1.scratch, hoffA])
      (denoteDeclArray_ext hstep2.ext hrelPre) hpersPre
      (hnPre.mono hstep2.ext) hrelR.decls hpersR hrelR.projNamed hprep
  have hoff3 : s3.store.scratchOn = false := by
    rw [hstep3.scratch, hstep2.scratch, hstep1.scratch]; exact hoffA
  obtain ⟨hokP, hxP, hpinsP, hppP, hipins, hpps, -, hcachesP, -⟩ :=
    internAllPins_run hstep3.ok
      (hpinsA.mono ((hstep1.ext.trans hstep2.ext).trans hstep3.ext)
        (by rw [hstep3.pins, hstep2.pins, hstep1.pins]))
      (hppA.mono (by rw [hstep3.pins, hstep2.pins, hstep1.pins])) hoff3 hpinsrun
  obtain ⟨env', F', -, hfinal⟩ :=
    Arena.installThenCheck_bridge rfl hk hind hpps
      (FoldOK_of_start hokP hpinsP hppP
        (((CacheOK.of_empty (s := sA) (by rw [hcachesA]; exact hc0)).monoF
              ((hstep1.ext.trans hstep2.ext).trans hstep3.ext)
              ((hstep1.cframe.trans hstep2.cframe).trans hstep3.cframe)).mono
          hxP hcachesP))
      hipins (fun x hx => hpersDs x (by simpa using hx))
      (denoteDeclArray_iff.mp (denoteDeclArray_ext hxP hclPrep)) hcheck
  obtain ⟨cv, vl, hty, hmem⟩ :=
    ConLeche.Frontend.parseChunks_jsonWithTheoremFalse hfalse hclR
  exact no_False_theorem_accepted_pure V rfl
    (by simpa using ConLeche.Frontend.mem_preparePrelude (pre := preC) hmem)
    hty hfinal

end ConRon.Bridge.Frontend

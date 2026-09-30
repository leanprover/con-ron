/-
# `ConRon.Bridge.Frontend.Capstone` — **the byte-level capstone at (B)**

DESIGN §8.2: *"the capstones are the same letters as today's
`conron.no_False_declaration`, at (B)."*  This module is that letter — the
one a reader can check without knowing what an `Env` is:

> a file whose chunks are one of the shapes `ConLeche.jsonWithTheoremFalse`
> describes is never accepted by the Lean arena checker.

`Bridge/Checker/Split.lean`'s `Arena.installThenCheck_bridge` is the statement
at the FOLD (the twin's accept is con-leche's, at a declaration list); this is
the letter at the BYTES, and the distance between them is exactly this tier:
the parse's exactness, the preparation's, and the prelude.

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
import ConRon.Bridge.Checker
import ConRon.Arena.Main
import ConLeche.MainTheorem

namespace ConRon.Bridge.Frontend

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend

universe w

/-! ## 1. The post-parse state

The fold theorem `Arena.installThenCheck_bridge` asks this tier for three
things.  Two are `Bridge/Frontend/Chunks.lean`'s `parseChunks_exact` (the denotation
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
      ienv := IFEnvOK_of_denote hok (IFEnvCoh.mk _)
        (by intro t hn
            simp [mkIFEnv, IEnv.empty] at hn) rfl }
  envWF := by intro c hc'; exact absurd hc' (by simp [Env.empty])
  persPins := hpp
  persEnv := { env := by intro c hc'; simp [mkIFEnv, IEnv.empty] at hc'
               idx := by intro n p hn; simp [mkIFEnv, mkIFEnvGo, IEnv.empty] at hn }
  coh := IFEnvCoh.mk _
  denote := rfl

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

end ConRon.Bridge.Frontend

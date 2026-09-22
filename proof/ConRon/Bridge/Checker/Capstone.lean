/-
# `ConRon.Bridge.Checker.Capstone` — the letters, at (B)

DESIGN §8.2: *"the capstones are the same letters as today's
`conron.no_False_declaration`, at (B)."*  This module is those letters, and it
is the one module of the tier that imports con-leche's `Model/*`.

`Model/Fold.lean:254`'s `checkDeclsPure_sound_of` and `:308`'s
`no_proof_of_False_pure` take an accepting `checkDeclsPure` run at ONE fuel
and give the model, *with zero further model-tier work* (the history report's
"THE JOIN POINT").  `Bridge/Checker/Fold.lean`'s `Arena.checkDeclsPure_bridge`
produces exactly that run, so the capstone is a two-line composition — which
is the point: the whole of the arena rewrite hangs off one obligation, and
here is the hook.

## The two named hypotheses

`KnotSpec μ F` and `IndSpec μ` (`Bridge/Checker/Hyp.lean`) travel to the
capstone as hypotheses, exactly as the original campaign's
`conron.model_exists` (`proof/ConRon/RefineOld/Main.lean:174`) carried
`hk : Core.KnotSpec .Verified IndAbs.checkFuelU` and
`hind : IndRoutesSpec .Verified`.  They are the Core tier's and the
Inductives tier's theorems; the two tiers discharge them and the capstone's
statement does not change.

## What the frontend tier owes this module

Four hypotheses here are about the STATE the fold starts in, and every one of
them is the driver's (`Arena/Main.lean`) and the parser's to establish:

* `FoldOK μ Env.empty (mkIFEnv IEnv.empty) s` — the state after
  `internReservedPins` and the parse, at the empty environment;
* `PinsDenote s.store pins pinsP` and `PersPinSets pins` — what
  `internAllPins` leaves (`Bridge/Checker/Pins.lean`);
* `denoteDecls s.store ds = some dsP` and `∀ x ∈ ds, PersDecl x` — the
  parser tier's exactness, DESIGN §8.2's `denoteDecls (Arena.parse chunks) =
  parseChunks chunks` with the persistence clause added (the parse runs with
  the scratch tier closed, so it is free).
-/
import ConRon.Bridge.Checker.Fold
import ConLeche.Model.Fold

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

universe w

/-- con-leche: ConLeche/Model/Fold.lean:254 checkDeclsPure_sound_of —
**THE CAPSTONE, at (B)**: every environment the Lean arena checker accepts has
a model in every set theory.

`ConLeche.Model.checkDeclsPure_sound_of` at
`Arena.checkDeclsPure_bridge`'s run.  The two named hypotheses are the Core
tier's (`KnotSpec`) and the Inductives tier's (`IndSpec`); everything else is
input-level or the frontend's (module note). -/
theorem Arena.model_exists (V : Type w) [ConLeche.SetTheory V]
    {μ : CheckMode} {F : Nat} {pins : List INatOpPinSet}
    {pinsP : List NatOpPinSet} {ds : List IDeclaration}
    {dsP : List Declaration} {fe' : IFEnv} {s s' : AState}
    (hμ : μ.verifiedChecks = true)
    (hk : KnotSpec μ F) (hind : IndSpec μ)
    (hpp : PersPinSets pins)
    (hok : FoldOK μ Env.empty (mkIFEnv IEnv.empty) s)
    (hpins : PinsDenote s.store pins pinsP)
    (hpd : ∀ x ∈ ds, PersDecl x) (hden : denoteDecls s.store ds = some dsP)
    (hrun : Arena.checkDeclsPure μ pins ds s = .ok (fe', s')) :
    ∃ env', denoteFEnv s'.store fe' = some env' ∧
      Nonempty (ConLeche.Model.EnvModelM V μ env') := by
  obtain ⟨env', F', hok', _, hpure⟩ :=
    Arena.checkDeclsPure_bridge hμ hk hind hpp hok hpins hpd hden hrun
  exact ⟨env', hok'.denote, ConLeche.Model.checkDeclsPure_sound_of
    (V := V) (pins := pinsP) hμ hpure⟩

/-- con-leche: ConLeche/Model/Fold.lean:308 no_proof_of_False_pure — **the
capstone's corollary, at (B)**: an environment the Lean arena checker accepts
holds no constant of type `False`.

The same letter as `conron.no_proof_of_False`
(`proof/ConRon/RefineOld/Main.lean:195`), at (B) instead of at the Rust. -/
theorem Arena.no_proof_of_False (V : Type w) [ConLeche.SetTheory V]
    {μ : CheckMode} {F : Nat} {pins : List INatOpPinSet}
    {pinsP : List NatOpPinSet} {ds : List IDeclaration}
    {dsP : List Declaration} {fe' : IFEnv} {s s' : AState}
    (hμ : μ.verifiedChecks = true)
    (hk : KnotSpec μ F) (hind : IndSpec μ)
    (hpp : PersPinSets pins)
    (hok : FoldOK μ Env.empty (mkIFEnv IEnv.empty) s)
    (hpins : PinsDenote s.store pins pinsP)
    (hpd : ∀ x ∈ ds, PersDecl x) (hden : denoteDecls s.store ds = some dsP)
    (hrun : Arena.checkDeclsPure μ pins ds s = .ok (fe', s')) :
    ∃ env', denoteFEnv s'.store fe' = some env' ∧
      ∀ c ∈ env'.consts, c.toConstantVal.type = .const ConLeche.falseName [] →
        False := by
  obtain ⟨env', F', hok', _, hpure⟩ :=
    Arena.checkDeclsPure_bridge hμ hk hind hpp hok hpins hpd hden hrun
  exact ⟨env', hok'.denote,
    ConLeche.Model.no_proof_of_False_pure (V := V) (pins := pinsP) hμ hpure⟩

/-- con-leche: ConLeche/Model/Fold.lean:291 no_proof_of_Empty_pure — the same
letter about `Empty`. -/
theorem Arena.no_proof_of_Empty (V : Type w) [ConLeche.SetTheory V]
    {μ : CheckMode} {F : Nat} {pins : List INatOpPinSet}
    {pinsP : List NatOpPinSet} {ds : List IDeclaration}
    {dsP : List Declaration} {fe' : IFEnv} {s s' : AState}
    (hμ : μ.verifiedChecks = true)
    (hk : KnotSpec μ F) (hind : IndSpec μ)
    (hpp : PersPinSets pins)
    (hok : FoldOK μ Env.empty (mkIFEnv IEnv.empty) s)
    (hpins : PinsDenote s.store pins pinsP)
    (hpd : ∀ x ∈ ds, PersDecl x) (hden : denoteDecls s.store ds = some dsP)
    (hrun : Arena.checkDeclsPure μ pins ds s = .ok (fe', s')) :
    ∃ env', denoteFEnv s'.store fe' = some env' ∧
      ∀ c ∈ env'.consts, c.toConstantVal.type = .const ConLeche.emptyName [] →
        False := by
  obtain ⟨env', F', hok', _, hpure⟩ :=
    Arena.checkDeclsPure_bridge hμ hk hind hpp hok hpins hpd hden hrun
  exact ⟨env', hok'.denote,
    ConLeche.Model.no_proof_of_Empty_pure (V := V) (pins := pinsP) hμ hpure⟩

end ConRon.Bridge

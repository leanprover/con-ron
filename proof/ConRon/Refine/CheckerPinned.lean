import ConRon.Refine.StdAxioms
import ConRon.Refine.TrustAxioms
import ConRon.Refine.BasisPins
import ConRon.Refine.FEnv

/-! # Task #56's imported hypotheses, discharged

The declaration-checker tier was written by several agents at once, so each
file names what it needs of a *sibling* file as a `Prop` and takes it as a
hypothesis — task #49's `CoreKPinned.lean` idiom, and for the same reason: it
keeps every seam visible and keeps the files independent.  This file is where
the three such `Prop`s are discharged, once the siblings exist.

| hypothesis | where it is used | what discharges it |
|---|---|---|
| `StdAxioms.EqBasisPinned` | `std_axiom_ok_refines` | `BasisPins.eq_basis_pinned_refines` |
| `TrustAxioms.MatchesPinSpec` | the compiler-trust guards | `StdAxioms.matches_pin_fast_eq_matches_pin` |
| `TrustAxioms.BasisPinsSpec` | `reducePinGuardF` and friends | `BasisPins.eq_basis_pinned_refines`/`nat_basis_pinned_refines` |

Note what the table says about task #24's second stub: `basis_pins.rs` is no
longer `false`-answering (task #27 rewrote it against task #22's generated
table), so all three are *proved*, not assumed — nothing in the tier rests on
an axiom or a `sorry` for them.

`sorry` count in this file: 0.
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.FEnv

namespace ConRon.Refine

/-- `Refine/StdAxioms.lean`'s hypothesis, from `Refine/BasisPins.lean`. -/
theorem eqBasisPinned {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe) : StdAxioms.EqBasisPinned fe lfe :=
  fun _ h => BasisPins.eq_basis_pinned_refines hrel hwf h

/-- `Refine/TrustAxioms.lean`'s first hypothesis, from `Refine/StdAxioms.lean`:
the executed `matchesPinFast` is the specification `matchesPin`. -/
theorem matchesPinSpec : TrustAxioms.MatchesPinSpec :=
  fun _ _ _ hcv hpin h => StdAxioms.matches_pin_fast_eq_matches_pin hcv hpin h

/-- `Refine/TrustAxioms.lean`'s second hypothesis, from
`Refine/BasisPins.lean`: the two exactly-compared basis pins. -/
theorem basisPinsSpec {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe) : TrustAxioms.BasisPinsSpec fe lfe where
  eqPinned _ h := BasisPins.eq_basis_pinned_refines hrel hwf h
  natPinned _ h := BasisPins.nat_basis_pinned_refines hrel hwf h

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

One `sorry` reaches this file — `Refine/BasisPins.lean`'s `basis_decls_a_wf`,
the `ConstantInfosWF` of task #22's generated table — and it reaches it only
through `eq_basis_pinned_refines`'s use of the pinned `eqA`.  Written down
rather than hidden, as `Refine/CheckerDecl.lean`'s census is. -/

/-- info: 'ConRon.Refine.matchesPinSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms matchesPinSpec

end ConRon.Refine

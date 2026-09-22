/-
# `ConRon.Bridge.Checker` — Theorem 1's declaration-checker tier

DESIGN §8.2's Theorem 1 at con-leche's join point (the history report's §5.2):
per declaration, in `checkDeclsPure`'s fold, and at the capstone.

In dependency order:

* `Bridge/Checker/Inv.lean` — the fold-step invariant `FoldOK`, and the
  declaration layer's transport across a `dropScratch`;
* `Bridge/Checker/Hyp.lean` — the two named hypotheses, `KnotSpec` (the Core
  tier's) and `IndSpec` (the Inductives tier's);
* `Bridge/Checker/Decl.lean` — `checkDecl`'s seven arms, one theorem each,
  and `PinsDenote`;
* `Bridge/Checker/Mono.lean` — one fuel for the whole fold, from con-leche's
  `FueledM`;
* `Bridge/Checker/Fold.lean` — **`Arena.checkDecl_bridge`**,
  `Arena.checkDeclStep_bridge` and **`Arena.checkDeclsPure_bridge`**;
* `Bridge/Checker/Capstone.lean` — **`Arena.model_exists`** and the two
  letters, through `Model/Fold.lean`'s `checkDeclsPure_sound_of`;
* `Bridge/Checker/Base.lean`, `Canon.lean`, `Basis.lean`, `Pins.lean` — the
  specs of `Arena/{CheckerBase,Canon,Basis,StdAxioms,TrustAxioms,Pins,
  NatOpPinSet,Intern}.lean`;
* `Bridge/Checker/Split.lean` — the install/check seam and
  `Arena.installThenCheck_bridge`, the binary's own fold;
* `Bridge/Checker/Axioms.lean` — the trust census.
-/
import ConRon.Bridge.Checker.Inv
import ConRon.Bridge.Checker.Hyp
import ConRon.Bridge.Checker.Decl
import ConRon.Bridge.Checker.Mono
import ConRon.Bridge.Checker.Fold
import ConRon.Bridge.Checker.Capstone
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Checker.Pins
import ConRon.Bridge.Checker.Split
import ConRon.Bridge.Checker.Axioms

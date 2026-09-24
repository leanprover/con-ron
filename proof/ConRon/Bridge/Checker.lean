/-
# `ConRon.Bridge.Checker` — Theorem 1's declaration-checker tier

DESIGN §8.2's Theorem 1 at con-leche's join point (the history report's §5.2):
per declaration, in `checkDeclsPure`'s fold, and at the capstone.

In dependency order:

* `Bridge/Checker/Inv.lean` — the fold-step invariant `FoldOK`, and the
  declaration layer's transport across a `dropScratch`;
* `Bridge/Checker/Names.lean` — the reserved-name list interned
  (`reservedBasisNames_run`), the two readers under it and the three
  equations a consumer of its answer needs.  It sits beside `Inv.lean`
  rather than inside `Base.lean` because **`Bridge/Inductives/Rel.lean`
  imports it too**: `structPartsCore?` and `nativeShape?` test
  `reserved.contains`, and the inductive tier cannot import `Base.lean`
  (task #97-P3-Layout);
* `Bridge/Checker/Hyp.lean` — the two named hypotheses, `KnotSpec` (the Core
  tier's) and `IndSpec` (the Inductives tier's);
* `Bridge/Checker/Decl.lean` — what an arm concludes (`DeclOut`) and what
  relates the two pin lists (`PinsDenote`);
* `Bridge/Checker/Arms.lean` — **`checkDecl`'s seven arms**, one theorem each.
  They sit above `Base.lean` / `DeclVal.lean` / `Basis.lean` because that is
  where their content is, and those three import `Decl.lean`;
* `Bridge/Checker/Mono.lean` — one fuel for the whole fold, from con-leche's
  `FueledM`;
* `Bridge/Checker/Fold.lean` — **`Arena.checkDecl_bridge`** (the sequential
  fold and its capstone letters were deleted by task #97-T2-CLEANUP; the
  binary's fold is `Split.lean`'s and `Phased.lean`'s);
* `Bridge/Checker/Base.lean`, `Canon.lean`, `Basis.lean`, `Pins.lean`,
  `DeclVal.lean` — the specs of `Arena/{CheckerBase,Canon,Basis,StdAxioms,
  TrustAxioms,Pins,NatOpPinSet,Intern,DeclCheck}.lean`;
* `Bridge/Checker/DeclWF.lean` — the pure checker's steps keep `EnvWF` and
  push no projection table off the inductive route (the pinned blocks'
  `ConstWF`, by evaluation); `Bridge/Checker/DivMod.lean` — the
  `Nat.div`/`Nat.mod` pin-variant gate.
* `Bridge/Checker/Split.lean` — the install/check seam and
  `Arena.installThenCheck_bridge`, the binary's own fold;
* `Bridge/Checker/Axioms.lean` — the trust census.
-/
import ConRon.Bridge.Checker.Inv
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Checker.Hyp
import ConRon.Bridge.Checker.Decl
import ConRon.Bridge.Checker.Arms
import ConRon.Bridge.Checker.Mono
import ConRon.Bridge.Checker.Fold
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Checker.Pins
import ConRon.Bridge.Checker.DeclVal
import ConRon.Bridge.Checker.DivMod
import ConRon.Bridge.Checker.DeclWF
import ConRon.Bridge.Checker.Nodup
import ConRon.Bridge.Checker.Split
import ConRon.Bridge.Checker.Axioms

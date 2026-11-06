/-
# `ConRon.Bridge.Checker` — Theorem 1's declaration-checker tier

DESIGN §8.2's Theorem 1 at con-leche's join point: per declaration, in the check phase the
driver runs (the stream's index, then one job per record on a pool of workers), and at the
capstone.

In dependency order:

* `Bridge/Checker/Inv.lean` — the invariant a check runs from (`FoldOK`, `StepOK`), what a
  lookup reads, and the declaration layer's transport across a `dropScratch`;
* `Bridge/Checker/Names.lean`, `NatOpNames.lean` — the reserved-name list and the certified
  operations' name lists interned;
* `Bridge/Checker/Hyp.lean` — the two named hypotheses, `CoreSpec` (the Core tier's,
  discharged by `CoreSpec.of_core`) and `IndSpec` (the Inductives tier's);
* `Bridge/Checker/Decl.lean` — what an arm concludes (`DeclOut`) and what relates the two pin
  lists (`PinsDenote`);
* `Bridge/Checker/Base.lean`, `Canon.lean`, `Basis.lean`, `Pins.lean`, `TypePins.lean`,
  `DeclVal.lean`, `DivMod.lean` — the specs of the declaration checker's stages;
* `Bridge/Checker/Arms.lean` — **`checkDecl`'s six arms**; `Bridge/Checker/Fold.lean` —
  **`Arena.checkDecl_bridge`**;
* `Bridge/Checker/Pushes.lean` — con-leche's pure `checkDecl` pushes what the record says, at
  fresh names;
* `Bridge/Checker/StreamIndex.lean`, `Index.lean`, `Install.lean` — the stream's index denotes
  con-leche's, and a view of it is the environment of the records before the position;
* `Bridge/Checker/Pooled.lean`, `PooledOleans.lean` — every job passing is con-leche's fold
  accepting, the stream's records and an `--olean` run's;
* `Bridge/Checker/Pool.lean` — **`Arena.pooledAccepts_bridge`**, the theorem the capstone uses;
* `Bridge/Checker/Mono.lean` — one fuel for a fold; `Bridge/Checker/Axioms.lean` — the trust
  census.
-/
module

public import ConRon.Bridge.Checker.Inv
public import ConRon.Bridge.Checker.Names
public import ConRon.Bridge.Checker.NatOpNames
public import ConRon.Bridge.Checker.Hyp
public import ConRon.Bridge.Checker.Decl
public import ConRon.Bridge.Checker.Arms
public import ConRon.Bridge.Checker.Mono
public import ConRon.Bridge.Checker.Fold
public import ConRon.Bridge.Checker.Base
public import ConRon.Bridge.Checker.Canon
public import ConRon.Bridge.Checker.Basis
public import ConRon.Bridge.Checker.Pins
public import ConRon.Bridge.Checker.TypePins
public import ConRon.Bridge.Checker.DeclVal
public import ConRon.Bridge.Checker.DivMod
public import ConRon.Bridge.Checker.Pushes
public import ConRon.Bridge.Checker.StreamIndex
public import ConRon.Bridge.Checker.Index
public import ConRon.Bridge.Checker.Install
public import ConRon.Bridge.Checker.Pooled
public import ConRon.Bridge.Checker.PooledOleans
public import ConRon.Bridge.Checker.Pool
public import ConRon.Bridge.Checker.Axioms

public section

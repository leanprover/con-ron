# The twins census — what (B) has to mirror, module by module

Task #97 P2, 2026-09-20.  DESIGN.md §8 is the design; this is the WORK
LIST it implies, at con-leche pin `c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0`.

It exists so that P2b–P2e can be handed out with exact contents: every
top-level definition of every con-leche module (B) must mirror, with its
line range at that pin, its signature, what class of work it is, and —
for the ones that carry a term — the twin's intended signature.

## How to read it

**The three classes.**

* **(T)** — a term crosses its signature or its body: `Expr`, `Level`,
  `Name`, `Declaration` or `ConstantInfo` — or one of the con-leche
  records that carry a term in a FIELD and need a handle twin for exactly
  the same reason (`ConstantVal`, whose `type` is an `Expr`; `RecRule`,
  whose `rhs` is; `ProjEntry`, `ProjTable`, `IndCaps`, `InductiveType`,
  `Constructor`; and `Env`/`FEnv`, which are indexes of them).  It needs a
  HANDLE TWIN in `AM := StateT AState (Except CheckError)`: the same body
  with `view` where it matched, `intern` where it built, and handle
  equality where it compared (§8.3, §8.4).
* **(P)** — pure data with no term inside: `CheckMode`,
  `ReducibilityHint`, `BasisKind`, the fuel constants, the literal
  arithmetic.  COPIED VERBATIM; the bridge's obligation for one of these
  is `rfl`.
* **(S)** — skipped in the current Rust port, with the reason
  `scripts/provenance-skip.txt` gives.  A skip is a fact about the RUST
  port, so it is a strong hint and not a ruling: elaboration-time meta
  code and `Prop`-only apparatus are skipped for the arena too, but a
  driver-only renderer may still be wanted in (B), whose driver prints
  con-leche's lines.  Every (S) row carries its reason and, in brackets,
  the class it would otherwise have, so the phase's agent can judge.

**The twin signature** is the MECHANICAL transliteration and nothing more:
`Expr ↦ EIdx`, `Level ↦ LIdx`, `List Level ↦ LsIdx`, `Name ↦ NIdx`,
`ConstantInfo ↦ IConstantInfo`, `Declaration ↦ IDeclaration`,
`Env ↦ IEnv`, `RecRule ↦ IRecRule`, `ProjEntry ↦ IProjEntry`,
`CoreFns m ↦ CoreFns`, `NatOpPinSet ↦ INatOpPinSet` (its sixteen fields
are terms), the `(ops : CheckerOps m)` binder DROPPED — §8.2 rules the
plug-in out, (B) calls its own bodies — and the RESULT — the last
component of the arrow
chain — wrapped in `AM` (the knot's `m τ` becomes `AM τ`; a pure result
becomes `AM τ` too, because `view` reads the state).

It is a starting point to be argued with, not a specification.  Three
places it is knowingly too crude, and each is real work rather than a
transcription error:

* a predicate that reads only a derived word (`piResultIsProp`,
  `Expr.hasLooseBVars`) wants `AState → Bool` or a plain `UInt32` test
  and no monad at all — §8.3's whole point about derived arrays;
* a memo threaded as an explicit `Std.HashMap (Expr × Nat) Expr`
  argument-and-result pair (all of `ExprOps`' `…Go` family) becomes a
  field of `AState`, so the twin loses the pair and the `AM` carries it;
* `List Expr` in an argument position is usually a SPINE, and §8.3 leaves
  open whether spines are `List EIdx` or an interned `LsIdx`-like slice —
  P2a decides by measurement;
* the frontend's own `M` (`Frontend/Export.lean:117`, `Except`-shaped over
  the same `CheckError`) shows up in P2e as `AM (M τ)`, which is one monad
  too many: the twin collapses it into `AM`, and the `RecordVerdict ↦
  CheckError` mapping goes with it.

**Regenerating.**  The ranges are a pin-relative fact, exactly as a
provenance citation is; they move with `lake update con-leche`.
`scripts/provenance.py locate <path> <decl>` relocates any single row by
name, and a whole-file re-extraction is `_tmp/t97/census.py` +
`_tmp/t97/gencensus.py`.

## Totals per phase

| phase | decls | lines | (T) decls / lines | (P) decls / lines | (S) decls / lines |
|---|---:|---:|---|---|---|
| **P2a** | 72 | 759 | 47 / 653 | 15 / 58 | 10 / 48 |
| **P2b** | 81 | 1005 | 70 / 972 | 0 / 0 | 11 / 33 |
| **P2c** | 236 | 3940 | 190 / 3385 | 31 / 362 | 15 / 193 |
| **P2d** | 423 | 5407 | 366 / 5052 | 17 / 129 | 40 / 226 |
| **P2e** | 82 | 1265 | 53 / 979 | 27 / 270 | 2 / 16 |
| **all five** | **894** | **12376** | 726 / 11041 | 90 / 819 | 78 / 516 |

The line counts are con-leche's *definitional block* lines, doc comment
included — `scripts/progress.py`'s unit, so the census and the ledger
agree.  DESIGN.md §8.6 budgets (B) at ~12 k lines; 12376 lines of con-leche
source to mirror is the independent estimate that budget can be checked
against, and it says the budget is about right for a one-for-one
transliteration with no room for the store's own apparatus — which is
P2a's, and is counted in P2a's row only as the `Name`/`Level`/`Expr`
representation it replaces.

`ConLeche/Kernel/NatOpPins.lean` has NO top-level definitional
declaration: its pin variants and `natOpPinSets` are spliced by the
`#load_natop_pins` elaborator (`NatOpPins.lean:62-65`) out of the
committed `pins/<toolchain>.json` dumps.  The twin decodes the same dumps
into the persistent tier, so the work is real and the row is empty; the
shape to decode into is `NatOpPinSet`, listed under P2d.

## Per-file totals

| phase | module | block lines | decls | T | P | S |
|---|---|---:|---:|---:|---:|---:|
| P2a | `ConLeche/Kernel/Name.lean` | 45 | 5 | 3 | 0 | 2 |
| P2a | `ConLeche/Kernel/Level.lean` | 254 | 25 | 23 | 1 | 1 |
| P2a | `ConLeche/Kernel/Expr.lean` | 460 | 42 | 21 | 14 | 7 |
| P2b | `ConLeche/Kernel/ExprOps.lean` | 1005 | 81 | 70 | 0 | 11 |
| P2c | `ConLeche/Kernel/PropWhen.lean` | 267 | 24 | 16 | 6 | 2 |
| P2c | `ConLeche/Kernel/PropRead.lean` | 99 | 10 | 9 | 1 | 0 |
| P2c | `ConLeche/Kernel/Env.lean` | 628 | 41 | 27 | 14 | 0 |
| P2c | `ConLeche/Kernel/FEnv.lean` | 104 | 14 | 14 | 0 | 0 |
| P2c | `ConLeche/Kernel/Core.lean` | 2660 | 127 | 117 | 10 | 0 |
| P2c | `ConLeche/Kernel/CoreIO.lean` | 38 | 3 | 0 | 0 | 3 |
| P2c | `ConLeche/Kernel/CoreGated.lean` | 115 | 9 | 0 | 0 | 9 |
| P2c | `ConLeche/Kernel/TypeChecker.lean` | 29 | 8 | 7 | 0 | 1 |
| P2d | `ConLeche/Kernel/CheckerBase.lean` | 263 | 20 | 17 | 3 | 0 |
| P2d | `ConLeche/Kernel/Checker.lean` | 587 | 22 | 21 | 1 | 0 |
| P2d | `ConLeche/Kernel/CheckerSplit.lean` | 76 | 6 | 4 | 2 | 0 |
| P2d | `ConLeche/Kernel/CheckerGated.lean` | 13 | 2 | 0 | 0 | 2 |
| P2d | `ConLeche/Kernel/DeclCheck.lean` | 739 | 40 | 39 | 0 | 1 |
| P2d | `ConLeche/Kernel/Canon.lean` | 139 | 13 | 13 | 0 | 0 |
| P2d | `ConLeche/Kernel/StdAxioms.lean` | 215 | 24 | 24 | 0 | 0 |
| P2d | `ConLeche/Kernel/TrustAxioms.lean` | 110 | 27 | 26 | 0 | 1 |
| P2d | `ConLeche/Kernel/TrustPins.lean` | 4 | 2 | 2 | 0 | 0 |
| P2d | `ConLeche/Kernel/NatOpPinSet.lean` | 24 | 1 | 1 | 0 | 0 |
| P2d | `ConLeche/Kernel/Basis.lean` | 26 | 3 | 3 | 0 | 0 |
| P2d | `ConLeche/Kernel/BasisA.lean` | 8 | 1 | 1 | 0 | 0 |
| P2d | `ConLeche/Kernel/BasisGen.lean` | 197 | 33 | 0 | 0 | 33 |
| P2d | `ConLeche/Kernel/Basis/Builder.lean` | 54 | 21 | 21 | 0 | 0 |
| P2d | `ConLeche/Kernel/Basis/Empty.lean` | 13 | 3 | 3 | 0 | 0 |
| P2d | `ConLeche/Kernel/Basis/Eq.lean` | 39 | 5 | 5 | 0 | 0 |
| P2d | `ConLeche/Kernel/Basis/False.lean` | 13 | 3 | 3 | 0 | 0 |
| P2d | `ConLeche/Kernel/Basis/Names.lean` | 70 | 26 | 26 | 0 | 0 |
| P2d | `ConLeche/Kernel/Basis/Nat.lean` | 41 | 8 | 8 | 0 | 0 |
| P2d | `ConLeche/Kernel/Basis/PUnit.lean` | 26 | 5 | 5 | 0 | 0 |
| P2d | `ConLeche/Kernel/Basis/Quot.lean` | 83 | 11 | 11 | 0 | 0 |
| P2d | `ConLeche/Kernel/Inductives/Modeled.lean` | 775 | 23 | 23 | 0 | 0 |
| P2d | `ConLeche/Kernel/Inductives/NativeInstall.lean` | 363 | 19 | 16 | 2 | 1 |
| P2d | `ConLeche/Kernel/Inductives/NativeInstallF.lean` | 101 | 5 | 5 | 0 | 0 |
| P2d | `ConLeche/Kernel/Inductives/NativeParts.lean` | 501 | 34 | 28 | 6 | 0 |
| P2d | `ConLeche/Kernel/Inductives/StructInstall.lean` | 54 | 2 | 2 | 0 | 0 |
| P2d | `ConLeche/Kernel/Inductives/StructInstallF.lean` | 65 | 5 | 4 | 1 | 0 |
| P2d | `ConLeche/Kernel/Inductives/StructParts.lean` | 410 | 34 | 32 | 0 | 2 |
| P2d | `ConLeche/Kernel/Inductives/SumInstall.lean` | 239 | 14 | 12 | 2 | 0 |
| P2d | `ConLeche/Kernel/Inductives/SumInstallF.lean` | 119 | 8 | 8 | 0 | 0 |
| P2d | `ConLeche/Kernel/Inductives/SumParts.lean` | 40 | 3 | 3 | 0 | 0 |
| P2e | `ConLeche/Frontend/Export.lean` | 15 | 3 | 0 | 3 | 0 |
| P2e | `ConLeche/Frontend/ExportC.lean` | 803 | 45 | 23 | 22 | 0 |
| P2e | `ConLeche/Frontend/Prepare.lean` | 65 | 10 | 8 | 0 | 2 |
| P2e | `ConLeche/Frontend/ProjRec.lean` | 260 | 16 | 16 | 0 | 0 |
| P2e | `ConLeche/Frontend/NatOpGround.lean` | 111 | 6 | 6 | 0 | 0 |
| P2e | `ConLeche/Frontend/Prelude.lean` | 11 | 2 | 0 | 2 | 0 |

## The `view` inventory — every structural match on a term

Each body below consumes an `Expr`, a `Level` or a `Name` STRUCTURALLY:
a match arm on its constructors.  In the twin every such arm becomes a
`view` of the handle — one tag decode and one array read (§8.3) — so this
is the list of bodies whose SHAPE changes and not merely their types, and
the list the bridge's `denote`-commutation lemmas are written for.  A
cascade of arms is one `view` and a `match` on its result; a body that
matches in several places appears once, with the union of the
constructors it names.

A `Level` match is the one place the rule is NOT `view`: §8.3's lesson 4
keeps the `Level` ALGORITHMS on transient `Level` trees read back from
`LIdx` (memoised per declaration, levels being small) and interns only
the representation, so a `Level` arm below is a match on a read-back tree
and costs the bridge a readback lemma instead of a commutation one.  A
`Name` match is rarer still and is almost always the error-text path.

`inductive`/`structure` declarations are NOT listed: their `|` lines
declare constructors, they do not consume one.

### `ConLeche/Kernel/Name.lean`

* `ofLeanName` (97-101) — Name `.anonymous` `.num` `.str`
* `toString` (103-108) — Name `.anonymous` `.num` `.str`

### `ConLeche/Kernel/Level.lean`

* `subst` (26-37) — Level `.imax` `.max` `.param` `.succ` `.zero`
* `allParamsDefined` (39-44) — Level `.imax` `.max` `.param` `.succ` `.zero`
* `isNeverZero` (46-55) — Level `.imax` `.max` `.param` `.succ` `.zero`
* `combining` (57-62) — Level `.succ` `.zero`
* `simplify` (64-77) — Level `.imax` `.max` `.param` `.succ` `.zero`
* `rest` (90-108) — Level `.imax` `.max` `.param` `.succ` `.zero`
* `imaxRules` (110-120) — Level `.imax`
* `isNonZero` (175-183) — Level `.imax` `.max` `.param` `.succ` `.zero`
* `zeronessOf` (185-195) — Level `.imax` `.max` `.param` `.succ` `.zero`
* `Name.isModelSuffix` (218-221) — Name `.str`
* `Name.isProjFnShape` (223-230) — Name `.num`
* `Expr.instantiateLevelParams` (232-249) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `Expr.allLevelParamsDefined` (251-268) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `Expr.allLevelParamsDefinedGo` (299-332) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`

### `ConLeche/Kernel/Expr.lean`

* `levelHasParam` (114-122) — Level `.imax` `.max` `.param` `.succ` `.zero`
* `beqRecursive` (729-737) — **Expr** `.app` `.forallE` `.fvar` `.lam` `.letE` `.proj`
* `beqGo` (818-949) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`

### `ConLeche/Kernel/ExprOps.lean`

* `instantiate1` (29-45) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `instantiate1Go` (80-116) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `instantiateList` (191-235) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `instantiateListGo` (267-303) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `liftLooseBVarsGo` (430-466) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `resetMeta` (552-559) — **Expr** `.app` `.forallE` `.fvar` `.lam` `.letE` `.proj`
* `resetMetaGo` (579-615) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `instantiate1Lift` (718-739) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `sizeB` (741-748) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `abstract1` (760-776) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `abstractRange` (778-808) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `sizeF` (810-819) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `fvarLeaves` (821-833) — **Expr** `.app` `.forallE` `.fvar` `.lam` `.letE` `.proj`
* `looseBVarsBounded` (863-877) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `isLam` (879-885) — **Expr** `.lam`
* `lamPw` (887-894) — **Expr** `.lam`
* `forallPw` (896-902) — **Expr** `.forallE`
* `hasFvar` (904-913) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `getAppFn` (915-918) — **Expr** `.app`
* `getAppArgs` (920-923) — **Expr** `.app`
* `renameConsts` (930-956) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `renameConstsGo` (999-1036) — **Expr** `.app` `.const` `.forallE` `.fvar` `.lam` `.letE` `.proj`
* `piResult` (1134-1138) — **Expr** `.forallE`
* `instPis` (1140-1144) — **Expr** `.forallE`
* `fvarTypeD` (1210-1215) — **Expr** `.fvar`
* `piArity` (1269-1272) — **Expr** `.forallE`
* `resultSort` (1274-1278) — **Expr** `.forallE` `.sort`
* `_root_.ConLeche.Expr.bvarBound` (1293-1303) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `_root_.ConLeche.Expr.fvarRange` (1312-1323) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `bvarBoundGo` (1368-1392) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `fvarRangeGo` (1397-1422) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `abstract1Go` (1789-1833) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `lowerBVarsGo` (2012-2049) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `instantiate1LiftGo` (2222-2261) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `_root_.ConLeche.Level.hasParam` (2399-2406) — Level `.imax` `.max` `.param` `.succ` `.zero`
* `_root_.ConLeche.Expr.hasLevelParam` (2420-2435) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `Expr.instLPGo` (2564-2603) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`

### `ConLeche/Kernel/PropWhen.lean`

* `cmp` (75-85) — Name `.anonymous` `.num` `.str`

### `ConLeche/Kernel/PropRead.lean`

* `numArgs` (58-61) — **Expr** `.app`
* `headTypePW` (73-90) — **Expr** `.const` `.fvar`
* `typeSortPW` (92-103) — **Expr** `.forallE` `.sort`
* `headProofPW` (105-122) — **Expr** `.const` `.forallE` `.fvar` `.lit` `.sort`
* `proofPW` (124-134) — **Expr** `.lam`

### `ConLeche/Kernel/Env.lean`

* `Expr.piSortTeleLen?` (572-586) — **Expr** `.forallE` `.sort`

### `ConLeche/Kernel/Core.lean`

* `isCtorApp` (155-162) — **Expr** `.const`
* `piResultIsProp` (164-171) — **Expr** `.sort`
* `piResultZ` (173-181) — **Expr** `.sort`
* `piResultNeverZero` (183-191) — **Expr** `.sort`
* `isUnitLikeTy` (206-243) — **Expr** `.const`
* `unfoldDefinition` (245-264) — **Expr** `.const`
* `unfoldableHead` (266-279) — **Expr** `.const`
* `headHint` (281-290) — **Expr** `.const`
* `sameConstHeads` (292-301) — **Expr** `.app` `.const`
* `natSuccOk` (323-332) — **Expr** `.forallE`
* `Expr.constsResolve` (344-369) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `litToCtorIfNat` (371-376) — **Expr** `.lit`
* `rawNatLit?` (378-383) — **Expr** `.const` `.lit`
* `listTyOk` (426-437) — **Expr** `.forallE`
* `listNilTyOk` (439-450) — **Expr** `.forallE`
* `listConsTyOk` (452-469) — **Expr** `.forallE`
* `charOfNatTyOk` (471-480) — **Expr** `.forallE`
* `stringOfListTyOk` (482-492) — **Expr** `.forallE`
* `Expr.isBoolTrue` (561-566) — **Expr** `.const`
* `Expr.quickPair` (568-580) — **Expr** `.forallE` `.lam` `.lit` `.sort`
* `Expr.substConst0` (723-729) — **Expr** `.app` `.const`
* `Expr.substConstAll` (731-747) — **Expr** `.app` `.const` `.forallE` `.lam` `.letE` `.proj`
* `natOpTyPinned` (761-776) — **Expr** `.forallE`
* `reduceNat` (811-863) — **Expr** `.app`
* `iotaCerts` (865-897) — **Expr** `.forallE`
* `piResidual` (899-904) — **Expr** `.forallE`
* `proofIrrel` (935-966) — **Expr** `.sort`
* `propIrrel` (968-1010) — **Expr** `.sort`
* `structEtaCertWith` (1066-1138) — **Expr** `.const`
* `etaCtorShape` (1140-1151) — **Expr** `.const`
* `structUnitCert` (1178-1206) — **Expr** `.const`
* `etaCert` (1208-1233) — **Expr** `.forallE`
* `majorToCtor` (1311-1493) — **Expr** `.const`
* `litMajorToCtor` (1495-1507) — **Expr** `.lit`
* `projLitToCtor` (1509-1523) — **Expr** `.lit`
* `recRuleKOf` (1525-1540) — **Expr** `.const`
* `recRuleEtaOf` (1542-1568) — **Expr** `.const`
* `iotaRec` (1719-1832) — **Expr** `.const`
* `whnfCoreBody` (1930-2019) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `ensureSort` (2068-2074) — **Expr** `.sort`
* `inferBody` (2076-2241) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `inferBodyIO` (2243-2371) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `defeqSpine` (2387-2406) — **Expr** `.const`
* `defeqStep` (2408-2668) — **Expr** `.app` `.const` `.forallE` `.fvar` `.lam` `.lit` `.proj` `.sort`
* `annotateBody` (2773-2893) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`

### `ConLeche/Kernel/CoreGated.lean`

* `whnfCoreBodyGated` (61-115) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`

### `ConLeche/Kernel/CheckerBase.lean`

* `isEqHead` (208-211) — **Expr** `.const`
* `eqHeadLevel` (213-220) — **Expr** `.const`
* `piResultSort` (249-254) — **Expr** `.sort`
* `checkProjShape` (257-272) — **Expr** `.const`

### `ConLeche/Kernel/DeclCheck.lean`

* `Expr.constsResolveF` (37-58) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `Expr.constsResolveFGo` (89-124) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `natOpTyPinnedF` (219-231) — **Expr** `.forallE`
* `checkEtaThmF` (344-382) — **Expr** `.app`
* `checkUnitThmF` (384-414) — **Expr** `.app`
* `nestedRuleShapeF` (575-599) — **Expr** `.const`
* `checkIotaThmNF` (601-685) — **Expr** `.const`
* `checkProjIotaF` (797-836) — **Expr** `.app`

### `ConLeche/Kernel/Canon.lean`

* `canonLevel` (27-34) — Level `.imax` `.max` `.param` `.succ` `.zero`
* `canonExpr` (36-65) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `canonExprEqFast` (126-146) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`

### `ConLeche/Kernel/StdAxioms.lean`

* `Expr.erasePw` (62-113) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `Expr.erasePwEq` (139-153) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `iffRecIntro` (222-227) — **Expr** `.app`
* `nonemptyIntroRaw` (258-264) — **Expr** `.app`
* `nonemptyRecRaw` (266-278) — **Expr** `.app`

### `ConLeche/Kernel/BasisGen.lean`

* `qName` (109-112) — Name `.anonymous` `.num` `.str`
* `qLevel` (117-122) — Level `.imax` `.max` `.param` `.succ` `.zero`
* `qExpr` (142-156) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`

### `ConLeche/Kernel/Basis/Nat.lean`

* `natRecSucc` (39-44) — **Expr** `.app`

### `ConLeche/Kernel/Basis/Quot.lean`

* `quotIndMk` (79-83) — **Expr** `.app`

### `ConLeche/Kernel/Inductives/Modeled.lean`

* `nestedRuleShape` (151-190) — **Expr** `.const`
* `checkIotaThmN` (192-317) — **Expr** `.const`
* `checkProjIota` (513-563) — **Expr** `.app`
* `checkEtaThm` (586-642) — **Expr** `.app`
* `checkUnitThm` (644-680) — **Expr** `.app`

### `ConLeche/Kernel/Inductives/NativeInstall.lean`

* `Expr.mentionsFvarGo` (221-257) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`

### `ConLeche/Kernel/Inductives/NativeParts.lean`

* `recPositivity` (89-111) — **Expr** `.const` `.forallE`
* `Expr.piBinders` (147-154) — **Expr** `.forallE`

### `ConLeche/Kernel/Inductives/StructParts.lean`

* `Expr.hasLooseBVarB` (371-390) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `Expr.hasLooseBVarBGo` (442-478) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `Expr.mentionsConst` (773-782) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`
* `Expr.mentionsConstGo` (814-849) — **Expr** `.app` `.bvar` `.const` `.forallE` `.fvar` `.lam` `.letE` `.lit` `.proj` `.sort`

### `ConLeche/Kernel/Inductives/SumInstall.lean`

* `whnfTelescope` (45-68) — **Expr** `.forallE` `.sort`
* `normPosDom` (141-175) — **Expr** `.forallE`

### `ConLeche/Frontend/ExportC.lean`

* `parseNameEntryD` (228-237) — Name `.num` `.str`
* `parseLevelEntryD` (239-247) — Level `.imax` `.max` `.param` `.succ`
* `parseExprEntryD` (249-279) — **Expr** `.app` `.bvar` `.const` `.forallE` `.lam` `.letE` `.proj` `.sort`
* `indPiTeleLen` (338-344) — **Expr** `.forallE`
* `validateIndD` (406-558) — **Expr** `.sort`

### `ConLeche/Frontend/ProjRec.lean`

* `isProjIotaName` (113-118) — Name `.str`
* `projIotaLevel` (120-125) — **Expr** `.const`
* `occursConst` (127-136) — **Expr** `.app` `.const` `.forallE` `.lam` `.letE` `.proj`
* `occursConstGo` (180-225) — **Expr** `.bvar` `.const` `.fvar` `.lit` `.sort`
* `lamBody` (233-237) — **Expr** `.lam`
* `stripPisAll` (239-245) — **Expr** `.forallE`
* `instPisOpen` (251-257) — **Expr** `.forallE`
* `headIs` (271-277) — **Expr** `.const`
* `projRecValue` (279-330) — **Expr** `.forallE`

### `ConLeche/Frontend/NatOpGround.lean`

* `usedConstsGo` (54-77) — **Expr** `.app` `.const` `.forallE` `.fvar` `.lam` `.letE` `.proj`

## The `==` inventory — where index equality replaces structural equality

DESIGN.md §8.3: exactness (`denote` injective) is a SOUNDNESS obligation,
not a performance property, and this is the list that says why.  Names are
compared for INEQUALITY throughout the checker, and `defeqBody`'s `a == b`
shortcut — which only ever returns `true` — would still send the arena
down an arm the pure run never took if two handles could denote one term.
Every line below is a place where the twin writes `h₁ == h₂` on handles
and owes the bridge `denote h₁ = denote h₂ ↔ h₁ = h₂` for the sort of
handle it compares.

Listed per declaration, with the con-leche line numbers of the
comparisons (`==`, `!=`, `.beq`) inside its block.  Only (T) declarations
are listed: a comparison inside a (P) block compares data the twin copies
verbatim, and `rfl` discharges it.

### `ConLeche/Kernel/Name.lean`

* `Name.beqPtr` (51-59) — 1 line: 58
* `Name.beq` (70-74) — 1 line: 74

### `ConLeche/Kernel/Level.lean`

* `isEquiv` (142-161) — 1 line: 159

### `ConLeche/Kernel/Expr.lean`

* `Level.beqPtr` (60-67) — 1 line: 66
* `Level.beq` (76-79) — 1 line: 79
* `probeHit` (804-816) — 1 line: 812
* `beqGo` (818-949) — 6 lines: 832, 833, 839, 874, 878, 933
* `beqMemo` (955-960) — 1 line: 959

### `ConLeche/Kernel/ExprOps.lean`

* `recRulePlain` (1227-1242) — 1 line: 1240
* `bvarB` (1427-1432) — 1 line: 1432
* `fvarB` (1434-1439) — 1 line: 1439
* `hasFvarFast` (1707-1708) — 1 line: 1708
* `exprPtrBEq` (2382-2388) — 1 line: 2388

### `ConLeche/Kernel/PropWhen.lean`

* `holds` (691-700) — 3 lines: 698, 699, 700

### `ConLeche/Kernel/Env.lean`

* `indParamsOk` (588-621) — 1 line: 620
* `find?` (686-687) — 1 line: 687

### `ConLeche/Kernel/Core.lean`

* `piResultIsProp` (164-171) — 1 line: 170
* `isUnitLikeTy` (206-243) — 2 lines: 235, 241
* `unfoldableHead` (266-279) — 1 line: 277
* `sameConstHeads` (292-301) — 1 line: 299
* `natIndOk` (311-315) — 1 line: 314
* `natZeroOk` (317-321) — 1 line: 320
* `natSuccOk` (323-332) — 1 line: 330
* `stringTyOk` (410-416) — 1 line: 415
* `charTyOk` (418-424) — 1 line: 423
* `listTyOk` (426-437) — 1 line: 434
* `listNilTyOk` (439-450) — 1 line: 447
* `listConsTyOk` (452-469) — 2 lines: 465, 466
* `charOfNatTyOk` (471-480) — 1 line: 478
* `stringOfListTyOk` (482-492) — 2 lines: 489, 490
* `Expr.isBoolTrue` (561-566) — 1 line: 565
* `natOpCod` (749-759) — 3 lines: 754, 757, 759
* `natOpTyPinned` (761-776) — 2 lines: 769, 774
* `etaCtorShape` (1140-1151) — 1 line: 1149
* `etaCert` (1208-1233) — 1 line: 1229
* `ProjEntry.fireOk` (1264-1290) — 2 lines: 1288, 1290
* `andRescueSlotsOf` (1292-1305) — 1 line: 1303
* `recRuleKOf` (1525-1540) — 1 line: 1537
* `recRuleEtaOf` (1542-1568) — 2 lines: 1564, 1565
* `iotaRec` (1719-1832) — 1 line: 1758
* `inferBody` (2076-2241) — 5 lines: 2128, 2168, 2178, 2220, 2223
* `inferBodyIO` (2243-2371) — 5 lines: 2291, 2307, 2313, 2355, 2358
* `defeqStep` (2408-2668) — 9 lines: 2431, 2440, 2550, 2555, 2558, 2587, 2609, 2617, 2653

### `ConLeche/Kernel/CheckerBase.lean`

* `domsMatchAux` (121-128) — 1 line: 127
* `domsMatchAuxA` (142-151) — 1 line: 150
* `checkAnnotList` (192-206) — 1 line: 204
* `isEqHead` (208-211) — 1 line: 210
* `checkProjShape` (257-272) — 1 line: 268
* `checkProjRule` (274-311) — 1 line: 288

### `ConLeche/Kernel/Checker.lean`

* `divModEnvGuard` (277-290) — 3 lines: 284, 286, 289

### `ConLeche/Kernel/DeclCheck.lean`

* `natOpCodF` (209-217) — 3 lines: 212, 215, 217
* `natOpTyPinnedF` (219-231) — 2 lines: 224, 229
* `divModEnvGuardF` (310-319) — 3 lines: 313, 315, 318
* `checkEtaThmF` (344-382) — 8 lines: 352, 353, 356, 363, 368, 369, 371, 379
* `checkUnitThmF` (384-414) — 7 lines: 390, 391, 397, 402, 407, 408, 411
* `ctorResidualOkF` (416-428) — 1 line: 426
* `indBlockCapsF` (430-441) — 1 line: 440
* `checkMemberValF` (487-505) — 1 line: 501
* `checkIotaThmF` (507-573) — 3 lines: 529, 533, 536
* `nestedRuleShapeF` (575-599) — 2 lines: 589, 590
* `checkIotaThmNF` (601-685) — 4 lines: 628, 632, 638, 674
* `checkProjTyF` (748-761) — 1 line: 752
* `checkProjRuleF` (763-795) — 1 line: 776
* `checkProjIotaF` (797-836) — 2 lines: 825, 827

### `ConLeche/Kernel/Canon.lean`

* `canonNameMap` (67-73) — 1 line: 71
* `canonExprEqFast` (126-146) — 6 lines: 129, 130, 131, 133, 143, 145
* `ConstantVal.canonEqFast` (201-206) — 1 line: 204
* `canonRulesEqFast` (224-231) — 1 line: 229
* `ConstantInfo.canonEqFast` (254-273) — 4 lines: 260, 267, 269, 272

### `ConLeche/Kernel/StdAxioms.lean`

* `ConstantVal.matchesPin` (115-117) — 1 line: 117
* `Expr.erasePwEq` (139-153) — 6 lines: 142, 143, 144, 145, 151, 152

### `ConLeche/Kernel/Basis.lean`

* `basisPinHit` (60-71) — 1 line: 70

### `ConLeche/Kernel/Inductives/Modeled.lean`

* `checkIotaThm` (55-149) — 3 lines: 96, 100, 103
* `nestedRuleShape` (151-190) — 2 lines: 180, 181
* `checkIotaThmN` (192-317) — 4 lines: 240, 244, 252, 305
* `checkMemberVal` (373-401) — 1 line: 397
* `projBack` (457-464) — 1 line: 462
* `projFwd` (466-473) — 1 line: 471
* `checkProjTy` (497-511) — 1 line: 502
* `checkProjIota` (513-563) — 2 lines: 549, 551
* `checkEtaThm` (586-642) — 8 lines: 603, 604, 608, 615, 620, 624, 626, 639
* `checkUnitThm` (644-680) — 7 lines: 653, 654, 660, 665, 670, 672, 677
* `ctorTargetsFam` (682-710) — 1 line: 709
* `indBlockCaps` (724-735) — 1 line: 734
* `ctorResidualOk` (744-779) — 1 line: 777

### `ConLeche/Kernel/Inductives/NativeInstall.lean`

* `nativeCapsAt` (59-98) — 3 lines: 90, 94, 96
* `Expr.mentionsFvar` (139-141) — 1 line: 141
* `Expr.mentionsFvarGo` (221-257) — 1 line: 236
* `nativeOpenedOk` (388-433) — 7 lines: 408, 409, 410, 422, 424, 425, 426
* `nativeFieldsOk` (435-445) — 2 lines: 440, 444
* `checkNativeRec` (465-502) — 1 line: 478
* `checkNativeTable` (504-519) — 1 line: 515
* `classifyFixKinds` (539-554) — 2 lines: 550, 552
* `checkNativePass` (556-574) — 1 line: 574

### `ConLeche/Kernel/Inductives/NativeInstallF.lean`

* `nativeOpenedOkF` (22-59) — 7 lines: 34, 35, 36, 48, 50, 51, 52
* `nativeFieldsOkF` (61-69) — 2 lines: 64, 68
* `checkNativeRecF` (87-115) — 1 line: 92
* `checkNativeTableF` (117-126) — 1 line: 122

### `ConLeche/Kernel/Inductives/NativeParts.lean`

* `recFamOk` (78-87) — 3 lines: 84, 85, 86
* `recPositivity` (89-111) — 4 lines: 102, 103, 105, 110
* `nativeRulePrefixOk` (394-445) — 2 lines: 433, 441
* `nativeRulesOk` (447-475) — 3 lines: 464, 468, 471
* `nativeCounts?` (501-523) — 1 line: 523
* `nativeRecPinOk` (525-549) — 3 lines: 542, 543, 546
* `nativeShape?` (562-614) — 6 lines: 580, 581, 582, 583, 594, 607

### `ConLeche/Kernel/Inductives/StructParts.lean`

* `structCtorResidOk` (196-202) — 3 lines: 200, 201, 202
* `structShape` (246-281) — 6 lines: 262, 263, 268, 269, 275, 279
* `structPartsCore?` (283-329) — 10 lines: 293, 294, 295, 296, 297, 298, 300, 304, 311, 321
* `Expr.hasLooseBVar` (356-369) — 1 line: 359
* `Expr.hasLooseBVarB` (371-390) — 1 line: 380
* `Expr.hasLooseBVarBGo` (442-478) — 1 line: 447
* `Expr.mentionsConst` (773-782) — 2 lines: 777, 782
* `Expr.mentionsConstGo` (814-849) — 2 lines: 820, 847

### `ConLeche/Kernel/Inductives/SumInstall.lean`

* `checkSumInd` (96-112) — 1 line: 109
* `checkStructFieldSortsI` (114-139) — 1 line: 135
* `normCtorVal` (190-205) — 1 line: 204
* `checkSumCtor` (207-253) — 2 lines: 242, 243

### `ConLeche/Kernel/Inductives/SumInstallF.lean`

* `checkSumIndF` (32-43) — 1 line: 40
* `checkStructFieldSortsIF` (45-61) — 1 line: 57
* `checkStructFieldSortsIFA` (63-81) — 1 line: 77
* `normCtorValF` (83-95) — 1 line: 94
* `checkSumCtorF` (97-128) — 2 lines: 119, 120

### `ConLeche/Kernel/Inductives/SumParts.lean`

* `InductiveShape.withSort` (112-119) — 1 line: 119

### `ConLeche/Frontend/ExportC.lean`

* `projRewriteD` (291-302) — 1 line: 300
* `validateIndD` (406-558) — 13 lines: 434, 462, 480, 485, 496, 518, 530, 535, 538, 541, 545, 553, 555

### `ConLeche/Frontend/ProjRec.lean`

* `projIotaLevel` (120-125) — 1 line: 124
* `occursConst` (127-136) — 1 line: 130
* `occursConstB` (151-178) — 1 line: 153
* `occursConstGo` (180-225) — 1 line: 184
* `headIs` (271-277) — 1 line: 276
* `projRecValue` (279-330) — 1 line: 286
* `projRecOwners` (332-370) — 5 lines: 364, 366, 367, 368, 369

### `ConLeche/Frontend/NatOpGround.lean`

* `hoistTargets` (106-136) — 1 line: 135
* `applyHoist` (138-162) — 1 line: 159

## The work lists

One block per module, in the order the phase should take them (con-leche's
own file order, which is its dependency order).  Each row is

```
<class> <first line>-<last line> <block lines>  <con-leche signature>
                       ↳ <the twin's intended signature>
```

and the line range is the definitional block, attributes and doc comment
included — the same range `scripts/provenance.py` cites, so a row is a
citation body once a name is put after it.

## P2a — the stores and the representation (the store agent's; listed here for completeness)

`Name`/`Level`/`Expr`: the handle words, the per-constructor arrays, the derived words and the cons tables of §8.3.  Everything below programs against what this phase freezes.

**Read this phase's twin column as informational only.**  P2a does not transliterate these three modules; it REPLACES them — the inductives become per-constructor arrays plus a tagged handle word, `beqPtr` becomes index equality, and `Expr.data`'s packed word becomes the derived array.  So `inductive Name ↳ inductive NIdx` below is the mechanical rule running past the end of its usefulness.  What the rows are good for is the INVENTORY: which of con-leche's smart constructors, field accessors and cached-word readers the store API has to offer, so that P2b-P2e find every one of them already there.

**72 declarations, 759 con-leche lines: 47 (T), 15 (P), 10 (S).**

### `ConLeche/Kernel/Name.lean` — 5 decls, 45 lines (3T 0P 2S)

```
T       26-45     20L  inductive Name
                       ↳ inductive NIdx
T       51-59      9L  def Name.beqPtr (a b : Name) : Bool
                       ↳ def NIdx.beqPtr (a b : NIdx) : AM Bool
T       70-74      5L  def Name.beq (a b : Name) : Bool
                       ↳ def NIdx.beq (a b : NIdx) : AM Bool
S(T)    97-101     5L  def ofLeanName : Lean.Name → Name
                       ↳ Rust port skips it: Conversion from `Lean.Name`, used by con-leche's elaboration-time code (the pins, the tests); the Rust core has no `Lean.Name`.
S(T)   103-108     6L  protected def toString : Name → String
                       ↳ Rust port skips it: A `Name`'s display string, for messages and the driver's output.
```

### `ConLeche/Kernel/Level.lean` — 25 decls, 254 lines (23T 1P 1S)

```
T       26-37     12L  def subst (ks : List Name) (vs : List Level) : Level → Level
                       ↳ def subst (ks : List NIdx) (vs : LsIdx) : LIdx → AM LIdx
T       39-44      6L  def allParamsDefined (params : List Name) : Level → Bool
                       ↳ def allParamsDefined (params : List NIdx) : LIdx → AM Bool
T       46-55     10L  def isNeverZero : Level → Bool
                       ↳ def isNeverZero : LIdx → AM Bool
T       57-62      6L  def combining : Level → Level → Level
                       ↳ def combining : LIdx → LIdx → AM LIdx
T       64-77     14L  def simplify : Level → Level
                       ↳ def simplify : LIdx → AM LIdx
T       81-88      8L  def leqCore (fuel : Nat) (l r : Level) (diff : Int) : Option Bool
                       ↳ def leqCore (fuel : Nat) (l r : LIdx) (diff : Int) : AM (Option Bool)
T       90-108    19L  def rest (fuel : Nat) (l r : Level) (diff : Int) : Option Bool
                       ↳ def rest (fuel : Nat) (l r : LIdx) (diff : Int) : AM (Option Bool)
T      110-120    11L  def imaxRules (fuel : Nat) (l r : Level) (diff : Int) : Option Bool
                       ↳ def imaxRules (fuel : Nat) (l r : LIdx) (diff : Int) : AM (Option Bool)
T      122-130     9L  def byCases (fuel : Nat) (p : Name) (l r : Level) (diff : Int) : Option Bool
                       ↳ def byCases (fuel : Nat) (p : NIdx) (l r : LIdx) (diff : Int) : AM (Option Bool)
P      134-136     3L  def defaultFuel : Nat
T      138-140     3L  def leq (l r : Level) : Option Bool
                       ↳ def leq (l r : LIdx) : AM (Option Bool)
T      142-161    20L  def isEquiv (l r : Level) : Option Bool
                       ↳ def isEquiv (l r : LIdx) : AM (Option Bool)
T      163-169     7L  def isEquivList : List Level → List Level → Option Bool
                       ↳ def isEquivList : LsIdx → LsIdx → AM (Option Bool)
T      171-173     3L  def isZero (l : Level) : Bool
                       ↳ def isZero (l : LIdx) : AM Bool
T      175-183     9L  def isNonZero : Level → Bool
                       ↳ def isNonZero : LIdx → AM Bool
T      185-195    11L  def zeronessOf : Level → PropWhen
                       ↳ def zeronessOf : LIdx → AM PropWhen
T      197-207    11L  def substPW (ks : List Name) (vs : List Level) (pw : PropWhen) : PropWhen
                       ↳ def substPW (ks : List NIdx) (vs : LsIdx) (pw : PropWhen) : AM PropWhen
T      213-216     4L  def Name.nodup : List Name → Bool
                       ↳ def NIdx.nodup : List NIdx → AM Bool
T      218-221     4L  def Name.isModelSuffix : Name → Bool
                       ↳ def NIdx.isModelSuffix : NIdx → AM Bool
T      223-230     8L  def Name.isProjFnShape : Name → Bool
                       ↳ def NIdx.isProjFnShape : NIdx → AM Bool
T      232-249    18L  def Expr.instantiateLevelParams (ks : List Name) (us : List Level) : Expr → Expr
                       ↳ def EIdx.instantiateLevelParams (ks : List NIdx) (us : LsIdx) : EIdx → AM EIdx
T      251-268    18L  def Expr.allLevelParamsDefined (params : List Name) : Expr → Bool
                       ↳ def EIdx.allLevelParamsDefined (params : List NIdx) : EIdx → AM Bool
S(T)   279-281     3L  def LPMemoInv (params : List Name) (memo : Std.HashMap Expr Bool) : Prop
                       ↳ Rust port skips it: A `Prop`-valued memo invariant, as `ExprOps.lean`'s.
T      299-332    34L  def Expr.allLevelParamsDefinedGo (params : List Name) (memo : Std.HashMap Expr Bool) : Expr → Bool × Std.HashMap Expr Bool
                       ↳ def EIdx.allLevelParamsDefinedGo (params : List NIdx) (memo : Std.HashMap EIdx Bool) : EIdx → AM (Bool × Std.HashMap EIdx Bool)
T      405-407     3L  def Expr.allLevelParamsDefinedFast (params : List Name) (e : Expr) : Bool
                       ↳ def EIdx.allLevelParamsDefinedFast (params : List NIdx) (e : EIdx) : AM Bool
```

### `ConLeche/Kernel/Expr.lean` — 42 decls, 460 lines (21T 14P 7S)

```
T       35-54     20L  inductive Level
                       ↳ inductive LIdx
T       60-67      8L  def Level.beqPtr (a b : Level) : Bool
                       ↳ def LIdx.beqPtr (a b : LIdx) : AM Bool
T       76-79      4L  def Level.beq (a b : Level) : Bool
                       ↳ def LIdx.beq (a b : LIdx) : AM Bool
P       93-104    12L  structure BinderMeta where
P      108-112     5L  inductive Literal
T      114-122     9L  def levelHasParam : Level → Bool
                       ↳ def levelHasParam : LIdx → AM Bool
T      124-127     4L  def levelsHaveParam : List Level → Bool
                       ↳ def levelsHaveParam : LsIdx → AM Bool
T      129-134     6L  def levelHash (u : Level) : UInt64
                       ↳ def levelHash (u : LIdx) : AM UInt64
T      136-139     4L  def levelsHash : List Level → UInt64
                       ↳ def levelsHash : LsIdx → AM UInt64
P      173-175     3L  def satRange : Nat
P      177-182     6L  def packData (h b f : UInt64) (lp : Bool) : UInt64
P      184-185     2L  def hashOfData (w : UInt64) : UInt64
P      187-188     2L  def bvarOfData (w : UInt64) : UInt64
P      190-191     2L  def fvarOfData (w : UInt64) : UInt64
P      193-194     2L  def lpOfData (w : UInt64) : Bool
P      196-197     2L  def hash32 (w : UInt64) : UInt64
P      199-200     2L  def satSucc (n : Nat) : UInt64
P      202-206     5L  def satPred (x : UInt64) : UInt64
T      285-403   119L  inductive Expr
                       ↳ inductive EIdx
T      417-421     5L  def hash (e : Expr) : UInt64
                       ↳ def hash (e : EIdx) : AM UInt64
T      423-425     3L  def hasLP (e : Expr) : Bool
                       ↳ def hasLP (e : EIdx) : AM Bool
T      427-428     2L  def bvarBRaw (e : Expr) : Nat
                       ↳ def bvarBRaw (e : EIdx) : AM Nat
T      430-431     2L  def fvarBRaw (e : Expr) : Nat
                       ↳ def fvarBRaw (e : EIdx) : AM Nat
T      729-737     9L  def beqRecursive : Expr → Bool
                       ↳ def beqRecursive : EIdx → AM Bool
T      739-749    11L  structure EqPair where
                       ↳ structure EqPair where
S(P)   751-753     3L  def EqPair.dflt : EqPair
                       ↳ Rust port skips it: The default a probe reads on a miss; the port's `probe_hit` reads an `Option` from `ron::HashMap`, so it needs no default.
P      755-756     2L  abbrev BeqMap
P      758-765     8L  def beqKey (pa pb : USize) : Nat
S(P)   767-773     7L  def beqBudget : Nat
                       ↳ Rust port skips it: The node budget before the memo table is materialised; the port's `beq` runs the identity and computed-word guards BEFORE it allocates, so the budget has nothing left to buy (task #30 measured it).
S(T)   775-780     6L  structure BeqRes (a b : Expr) where
                       ↳ Rust port skips it: The raw result of one node's comparison, carrying a `Decidable (a = b)`; the port returns a `bool` and its decision is proved, not carried.
S(T)   782-786     5L  abbrev BeqOut (a b : Expr)
                       ↳ Rust port skips it: `Squash (BeqRes …)` — the subsingleton wrapper that makes `withPtrAddr`'s side condition discharge; a `bool` here.
S(T)   788-790     3L  def BeqOut.mk {a b : Expr} (d : Decidable (a = b)) (fuel : Nat) (map : Option BeqMap) : BeqOut a b
                       ↳ Rust port skips it: The constructor of that wrapper.
S(P)   792-797     6L  def withAddr {α : Type u} {β : Type v} [Subsingleton β] (a : α) (k : USize → β) : β
                       ↳ Rust port skips it: `withPtrAddr` into a subsingleton — an address primitive Aeneas cannot model; `expr::ptr_eq` (§3.2's `Rc` axiom) is what the port has instead.
S(T)   799-802     4L  def ptrDec (a b : Expr) : Decidable (a = b)
                       ↳ Rust port skips it: Identity decided by the pointer test; `expr::ptr_eq` is both this and `withAddr`.
T      804-816    13L  def probeHit (m : BeqMap) (key : Nat) (pa pb : USize) (a b : Expr) : { h : Bool // h = true → a = b }
                       ↳ def probeHit (m : BeqMap) (key : Nat) (pa pb : USize) (a b : EIdx) : AM ({ h : Bool // h = true → a = b })
T      818-949   132L  def beqGo (fuel : Nat) (map : Option BeqMap) (a b : @& Expr) : BeqOut a b
                       ↳ def beqGo (fuel : Nat) (map : Option BeqMap) (a b : @& EIdx) : AM (BeqOut a b)
T      951-953     3L  def beqDec (a b : Expr) : Decidable (a = b)
                       ↳ def beqDec (a b : EIdx) : AM (Decidable (a = b))
T      955-960     6L  def beqMemo (a b : Expr) : Bool
                       ↳ def beqMemo (a b : EIdx) : AM Bool
T      972-976     5L  def beq (a b : Expr) : Bool
                       ↳ def beq (a b : EIdx) : AM Bool
P     1022-1023    2L  def bvarPoolSize : Nat
T     1025-1026    2L  def bvarPool : Array Expr
                       ↳ def bvarPool : AM (Array EIdx)
T     1028-1031    4L  def mkBvar (i : Nat) : Expr
                       ↳ def mkBvar (i : Nat) : AM EIdx
```

## P2b — the `ExprOps` twins, with memo

`instantiate` / `abstract` / `lift` / `instantiateLevelParams` and the spine and field helpers, each with its cutoff off a derived field (§8.3's lesson 20) and a cache cleared at every top-level call, so the substitution vector is not in the key.

**81 declarations, 1005 con-leche lines: 70 (T), 0 (P), 11 (S).**

### `ConLeche/Kernel/ExprOps.lean` — 81 decls, 1005 lines (70T 0P 11S)

```
T       29-45     17L  def instantiate1 (e : Expr) (v : Expr) (d : Nat := 0) : Expr
                       ↳ def instantiate1 (e : EIdx) (v : EIdx) (d : Nat := 0) : AM EIdx
S(T)    60-62      3L  def Inst1MemoInv (v : Expr) (memo : Std.HashMap (Expr × Nat) Expr) : Prop
                       ↳ Rust port skips it: A memo invariant, `Prop`-valued ("every recorded answer is the real one"): the specification the port's memo is proved against, not code.
T       80-116    37L  def instantiate1Go (v : Expr) (memo : Std.HashMap (Expr × Nat) Expr) (e : Expr) (d : Nat) : Expr × Std.HashMap (Expr × Nat) Expr
                       ↳ def instantiate1Go (v : EIdx) (memo : Std.HashMap (EIdx × Nat) EIdx) (e : EIdx) (d : Nat) : AM (EIdx × Std.HashMap (EIdx × Nat) EIdx)
T      182-184     3L  def instantiate1Fast (e v : Expr) (d : Nat := 0) : Expr
                       ↳ def instantiate1Fast (e v : EIdx) (d : Nat := 0) : AM EIdx
T      191-235    45L  def instantiateList (e : Expr) (vs : List Expr) (d : Nat := 0) : Expr
                       ↳ def instantiateList (e : EIdx) (vs : List EIdx) (d : Nat := 0) : AM EIdx
S(T)   247-249     3L  def InstLMemoInv (vs : List Expr) (memo : Std.HashMap (Expr × Nat) Expr) : Prop
                       ↳ Rust port skips it: A `Prop`-valued memo invariant, as `Inst1MemoInv`.
T      267-303    37L  def instantiateListGo (vs : List Expr) (memo : Std.HashMap (Expr × Nat) Expr) (e : Expr) (d : Nat) : Expr × Std.HashMap (Expr × Nat) Expr
                       ↳ def instantiateListGo (vs : List EIdx) (memo : Std.HashMap (EIdx × Nat) EIdx) (e : EIdx) (d : Nat) : AM (EIdx × Std.HashMap (EIdx × Nat) EIdx)
T      371-373     3L  def instantiateListFast (e : Expr) (vs : List Expr) (d : Nat := 0) : Expr
                       ↳ def instantiateListFast (e : EIdx) (vs : List EIdx) (d : Nat := 0) : AM EIdx
T      380-400    21L  def liftLooseBVars (amount : Nat) : (cutoff : Nat) → Expr → Expr
                       ↳ def liftLooseBVars (amount : Nat) : (cutoff : Nat) → EIdx → AM EIdx
S(T)   410-412     3L  def LiftMemoInv (amount : Nat) (memo : Std.HashMap (Expr × Nat) Expr) : Prop
                       ↳ Rust port skips it: A `Prop`-valued memo invariant, as `Inst1MemoInv`.
T      430-466    37L  def liftLooseBVarsGo (amount : Nat) (memo : Std.HashMap (Expr × Nat) Expr) (e : Expr) (c : Nat) : Expr × Std.HashMap (Expr × Nat) Expr
                       ↳ def liftLooseBVarsGo (amount : Nat) (memo : Std.HashMap (EIdx × Nat) EIdx) (e : EIdx) (c : Nat) : AM (EIdx × Std.HashMap (EIdx × Nat) EIdx)
T      532-534     3L  def liftLooseBVarsFast (amount c : Nat) (e : Expr) : Expr
                       ↳ def liftLooseBVarsFast (amount c : Nat) (e : EIdx) : AM EIdx
T      552-559     8L  def resetMeta : Expr → Expr
                       ↳ def resetMeta : EIdx → AM EIdx
S(T)   561-563     3L  def ResetMemoInv (memo : Std.HashMap Expr Expr) : Prop
                       ↳ Rust port skips it: A `Prop`-valued memo invariant, as `Inst1MemoInv`.
T      579-615    37L  def resetMetaGo (memo : Std.HashMap Expr Expr) : Expr → Expr × Std.HashMap Expr Expr
                       ↳ def resetMetaGo (memo : Std.HashMap EIdx EIdx) : EIdx → AM (EIdx × Std.HashMap EIdx EIdx)
T      687-688     2L  def resetMetaFast (e : Expr) : Expr
                       ↳ def resetMetaFast (e : EIdx) : AM EIdx
T      694-716    23L  def lowerBVars (amount : Nat) : (cutoff : Nat) → Expr → Expr
                       ↳ def lowerBVars (amount : Nat) : (cutoff : Nat) → EIdx → AM EIdx
T      718-739    22L  def instantiate1Lift (e : Expr) (v : Expr) (d : Nat := 0) : Expr
                       ↳ def instantiate1Lift (e : EIdx) (v : EIdx) (d : Nat := 0) : AM EIdx
T      741-748     8L  def sizeB : Expr → Nat
                       ↳ def sizeB : EIdx → AM Nat
T      760-776    17L  def abstract1 (e : Expr) (d : Nat) (k : Nat := 0) : Expr
                       ↳ def abstract1 (e : EIdx) (d : Nat) (k : Nat := 0) : AM EIdx
T      778-808    31L  def abstractRange (e : Expr) (d k : Nat) (c : Nat := 0) : Expr
                       ↳ def abstractRange (e : EIdx) (d k : Nat) (c : Nat := 0) : AM EIdx
T      810-819    10L  def sizeF : Expr → Nat
                       ↳ def sizeF : EIdx → AM Nat
T      821-833    13L  def fvarLeaves : Expr → List (Nat × Expr)
                       ↳ def fvarLeaves : EIdx → AM (List (Nat × EIdx))
T      835-861    27L  def wscopedB : (d : Nat) → Expr → Bool
                       ↳ def wscopedB : (d : Nat) → EIdx → AM Bool
T      863-877    15L  def looseBVarsBounded (k : Nat) : Expr → Bool
                       ↳ def looseBVarsBounded (k : Nat) : EIdx → AM Bool
T      879-885     7L  def isLam : Expr → Bool
                       ↳ def isLam : EIdx → AM Bool
T      887-894     8L  def lamPw : Expr → Option PropWhen
                       ↳ def lamPw : EIdx → AM (Option PropWhen)
T      896-902     7L  def forallPw : Expr → Option PropWhen
                       ↳ def forallPw : EIdx → AM (Option PropWhen)
T      904-913    10L  def hasFvar : Expr → Bool
                       ↳ def hasFvar : EIdx → AM Bool
T      915-918     4L  def getAppFn : Expr → Expr
                       ↳ def getAppFn : EIdx → AM EIdx
T      920-923     4L  def getAppArgs : Expr → List Expr
                       ↳ def getAppArgs : EIdx → AM (List EIdx)
T      925-928     4L  def mkAppN (f : Expr) : List Expr → Expr
                       ↳ def mkAppN (f : EIdx) : List EIdx → AM EIdx
T      930-956    27L  def renameConsts (f : Name → Name) : Expr → Expr
                       ↳ def renameConsts (f : NIdx → NIdx) : EIdx → AM EIdx
S(T)   980-982     3L  def RenameMemoInv (f : Name → Name) (memo : Std.HashMap Expr Expr) : Prop
                       ↳ Rust port skips it: A `Prop`-valued memo invariant, as `Inst1MemoInv`.
T      999-1036   38L  def renameConstsGo (f : Name → Name) (memo : Std.HashMap Expr Expr) : Expr → Expr × Std.HashMap Expr Expr
                       ↳ def renameConstsGo (f : NIdx → NIdx) (memo : Std.HashMap EIdx EIdx) : EIdx → AM (EIdx × Std.HashMap EIdx EIdx)
T     1109-1111    3L  def renameConstsFast (f : Name → Name) (e : Expr) : Expr
                       ↳ def renameConstsFast (f : NIdx → NIdx) (e : EIdx) : AM EIdx
T     1118-1124    7L  def stripLams : Nat → Expr → Option (List (Expr × BinderMeta) × Expr)
                       ↳ def stripLams : Nat → EIdx → AM (Option (List (EIdx × BinderMeta) × EIdx))
T     1126-1132    7L  def stripPis : Nat → Expr → Option (List (Expr × BinderMeta) × Expr)
                       ↳ def stripPis : Nat → EIdx → AM (Option (List (EIdx × BinderMeta) × EIdx))
T     1134-1138    5L  def piResult : Expr → Expr
                       ↳ def piResult : EIdx → AM EIdx
T     1140-1144    5L  def instPis : Expr → List Expr → Option Expr
                       ↳ def instPis : EIdx → List EIdx → AM (Option EIdx)
T     1146-1154    9L  def instPisAt : List Expr → Expr → Option (List Expr × Expr)
                       ↳ def instPisAt : List EIdx → EIdx → AM (Option (List EIdx × EIdx))
T     1156-1162    7L  def instLamsAt : List Expr → Expr → Option (List Expr × Expr)
                       ↳ def instLamsAt : List EIdx → EIdx → AM (Option (List EIdx × EIdx))
T     1179-1188   10L  def instPisAtFGo (acc : List Expr) : List Expr → Expr → Option (List Expr × Expr)
                       ↳ def instPisAtFGo (acc : List EIdx) : List EIdx → EIdx → AM (Option (List EIdx × EIdx))
T     1190-1194    5L  def instPisAtF (args : List Expr) (e : Expr) : Option (List Expr × Expr)
                       ↳ def instPisAtF (args : List EIdx) (e : EIdx) : AM (Option (List EIdx × EIdx))
T     1196-1202    7L  def instLamsAtFGo (acc : List Expr) : List Expr → Expr → Option (List Expr × Expr)
                       ↳ def instLamsAtFGo (acc : List EIdx) : List EIdx → EIdx → AM (Option (List EIdx × EIdx))
T     1204-1208    5L  def instLamsAtF (args : List Expr) (e : Expr) : Option (List Expr × Expr)
                       ↳ def instLamsAtF (args : List EIdx) (e : EIdx) : AM (Option (List EIdx × EIdx))
T     1210-1215    6L  def fvarTypeD : Expr → Expr
                       ↳ def fvarTypeD : EIdx → AM EIdx
T     1217-1225    9L  def instSpine : List Expr → Nat → Expr → Expr
                       ↳ def instSpine : List EIdx → Nat → EIdx → AM EIdx
T     1227-1242   16L  def recRulePlain (recTy : Expr) (mI rP cnP : Nat) : Bool
                       ↳ def recRulePlain (recTy : EIdx) (mI rP cnP : Nat) : AM Bool
T     1244-1259   16L  def pisToLams : Nat → Expr → Expr → Option Expr
                       ↳ def pisToLams : Nat → EIdx → EIdx → AM (Option EIdx)
T     1261-1267    7L  def replacePiBody : Nat → Expr → Expr → Option Expr
                       ↳ def replacePiBody : Nat → EIdx → EIdx → AM (Option EIdx)
T     1269-1272    4L  def piArity : Expr → Nat
                       ↳ def piArity : EIdx → AM Nat
T     1274-1278    5L  def resultSort : Expr → Option Level
                       ↳ def resultSort : EIdx → AM (Option LIdx)
T     1293-1303   11L  def _root_.ConLeche.Expr.bvarBound : Expr → Nat
                       ↳ def _root_.ConLeche.EIdx.bvarBound : EIdx → AM Nat
T     1312-1323   12L  def _root_.ConLeche.Expr.fvarRange : Expr → Nat
                       ↳ def _root_.ConLeche.EIdx.fvarRange : EIdx → AM Nat
T     1368-1392   25L  def bvarBoundGo (memo : Std.HashMap Expr Nat) (e : Expr) : Nat × Std.HashMap Expr Nat
                       ↳ def bvarBoundGo (memo : Std.HashMap EIdx Nat) (e : EIdx) : AM (Nat × Std.HashMap EIdx Nat)
T     1394-1395    2L  def bvarBoundMemo (e : Expr) : Nat
                       ↳ def bvarBoundMemo (e : EIdx) : AM Nat
T     1397-1422   26L  def fvarRangeGo (memo : Std.HashMap Expr Nat) (e : Expr) : Nat × Std.HashMap Expr Nat
                       ↳ def fvarRangeGo (memo : Std.HashMap EIdx Nat) (e : EIdx) : AM (Nat × Std.HashMap EIdx Nat)
T     1424-1425    2L  def fvarRangeMemo (e : Expr) : Nat
                       ↳ def fvarRangeMemo (e : EIdx) : AM Nat
T     1427-1432    6L  def bvarB (e : Expr) : Nat
                       ↳ def bvarB (e : EIdx) : AM Nat
T     1434-1439    6L  def fvarB (e : Expr) : Nat
                       ↳ def fvarB (e : EIdx) : AM Nat
S(T)  1494-1496    3L  def MemoBInv (memo : Std.HashMap Expr Nat) : Prop
                       ↳ Rust port skips it: A `Prop`-valued memo invariant, as `Inst1MemoInv`.
S(T)  1615-1617    3L  def MemoFInv (memo : Std.HashMap Expr Nat) : Prop
                       ↳ Rust port skips it: A `Prop`-valued memo invariant, as `Inst1MemoInv`.
T     1707-1708    2L  def hasFvarFast (e : Expr) : Bool
                       ↳ def hasFvarFast (e : EIdx) : AM Bool
T     1716-1717    2L  def looseBVarsBoundedFast (k : Nat) (e : Expr) : Bool
                       ↳ def looseBVarsBoundedFast (k : Nat) (e : EIdx) : AM Bool
S(T)  1769-1771    3L  def Abs1MemoInv (d : Nat) (memo : Std.HashMap (Expr × Nat) Expr) : Prop
                       ↳ Rust port skips it: A `Prop`-valued memo invariant, as `Inst1MemoInv`.
T     1789-1833   45L  def abstract1Go (d : Nat) (memo : Std.HashMap (Expr × Nat) Expr) (e : Expr) (k : Nat) : Expr × Std.HashMap (Expr × Nat) Expr
                       ↳ def abstract1Go (d : Nat) (memo : Std.HashMap (EIdx × Nat) EIdx) (e : EIdx) (k : Nat) : AM (EIdx × Std.HashMap (EIdx × Nat) EIdx)
T     1927-1929    3L  def abstract1Fast (e : Expr) (d : Nat) (k : Nat := 0) : Expr
                       ↳ def abstract1Fast (e : EIdx) (d : Nat) (k : Nat := 0) : AM EIdx
S(T)  1992-1994    3L  def LowerMemoInv (amount : Nat) (memo : Std.HashMap (Expr × Nat) Expr) : Prop
                       ↳ Rust port skips it: A `Prop`-valued memo invariant, as `Inst1MemoInv`.
T     2012-2049   38L  def lowerBVarsGo (amount : Nat) (memo : Std.HashMap (Expr × Nat) Expr) (e : Expr) (c : Nat) : Expr × Std.HashMap (Expr × Nat) Expr
                       ↳ def lowerBVarsGo (amount : Nat) (memo : Std.HashMap (EIdx × Nat) EIdx) (e : EIdx) (c : Nat) : AM (EIdx × Std.HashMap (EIdx × Nat) EIdx)
T     2144-2146    3L  def lowerBVarsFast (amount : Nat) (c : Nat) (e : Expr) : Expr
                       ↳ def lowerBVarsFast (amount : Nat) (c : Nat) (e : EIdx) : AM EIdx
S(T)  2202-2204    3L  def Inst1LMemoInv (v : Expr) (memo : Std.HashMap (Expr × Nat) Expr) : Prop
                       ↳ Rust port skips it: A `Prop`-valued memo invariant, as `Inst1MemoInv`.
T     2222-2261   40L  def instantiate1LiftGo (v : Expr) (memo : Std.HashMap (Expr × Nat) Expr) (e : Expr) (d : Nat) : Expr × Std.HashMap (Expr × Nat) Expr
                       ↳ def instantiate1LiftGo (v : EIdx) (memo : Std.HashMap (EIdx × Nat) EIdx) (e : EIdx) (d : Nat) : AM (EIdx × Std.HashMap (EIdx × Nat) EIdx)
T     2356-2358    3L  def instantiate1LiftFast (e : Expr) (v : Expr) (d : Nat := 0) : Expr
                       ↳ def instantiate1LiftFast (e : EIdx) (v : EIdx) (d : Nat := 0) : AM EIdx
T     2365-2378   14L  def instPisAtLift : List Expr → Expr → Option Expr
                       ↳ def instPisAtLift : List EIdx → EIdx → AM (Option EIdx)
T     2382-2388    7L  def exprPtrBEq (a b : Expr) : Bool
                       ↳ def exprPtrBEq (a b : EIdx) : AM Bool
T     2399-2406    8L  def _root_.ConLeche.Level.hasParam : Level → Bool
                       ↳ def _root_.ConLeche.LIdx.hasParam : LIdx → AM Bool
T     2420-2435   16L  def _root_.ConLeche.Expr.hasLevelParam : Expr → Bool
                       ↳ def _root_.ConLeche.EIdx.hasLevelParam : EIdx → AM Bool
S(T)  2544-2546    3L  def ILPMemoInv (ks : List Name) (us : List Level) (memo : Std.HashMap Expr Expr) : Prop
                       ↳ Rust port skips it: A `Prop`-valued memo invariant, as `Inst1MemoInv`.
T     2564-2603   40L  def Expr.instLPGo (ks : List Name) (us : List Level) (memo : Std.HashMap Expr Expr) (e : Expr) : Expr × Std.HashMap Expr Expr
                       ↳ def EIdx.instLPGo (ks : List NIdx) (us : LsIdx) (memo : Std.HashMap EIdx EIdx) (e : EIdx) : AM (EIdx × Std.HashMap EIdx EIdx)
T     2718-2720    3L  def Expr.instLPFast (ks : List Name) (us : List Level) (e : Expr) : Expr
                       ↳ def EIdx.instLPFast (ks : List NIdx) (us : LsIdx) (e : EIdx) : AM EIdx
```

## P2c — the `Core` twins: six bodies, the knot, the caches, the per-declaration bracket

`whnfCore` / `whnf` / `infer` / `inferIO` / `defeq` / `annotate`, the `CoreFns` record over handles tied by `coreKnot` at fuel, and the environment index the six read (`Env`/`FEnv`, and the `PropWhen` annotation lattice they carry).

**236 declarations, 3940 con-leche lines: 190 (T), 31 (P), 15 (S).**

### `ConLeche/Kernel/PropWhen.lean` — 24 decls, 267 lines (16T 6P 2S)

```
T       75-85     11L  def cmp : Name → Name → Ordering
                       ↳ def cmp : NIdx → NIdx → AM Ordering
T      201-202     2L  abbrev Sorted (ps : List Name) : Prop
                       ↳ abbrev Sorted (ps : List NIdx) : AM Prop
T      212-222    11L  def merge : List Name → List Name → List Name
                       ↳ def merge : List NIdx → List NIdx → AM (List NIdx)
T      288-291     4L  def canon (ps : List Name) : List Name
                       ↳ def canon (ps : List NIdx) : AM (List NIdx)
T      360-384    25L  private inductive PropWhenRepr
                       ↳ inductive PropWhenRepr
T      386-415    30L  structure PropWhen where
                       ↳ structure PropWhen where
P      437-444     8L  private def equivR : PropWhenRepr → PropWhenRepr → Bool
P      449-453     5L  def decEq (a b : PropWhen) : Decidable (a = b)
P      457-459     3L  def hash' (pw : PropWhen) : UInt64
P      470-473     4L  def never : PropWhen
T      480-487     8L  private def ofSorted : (ps : List Name) → Sorted ps → PropWhen
                       ↳ def ofSorted : (ps : List NIdx) → Sorted ps → AM PropWhen
T      489-495     7L  private def two' (p q : Name) : PropWhen
                       ↳ def two' (p q : NIdx) : AM PropWhen
T      497-507    11L  def ifAllZero : List Name → PropWhen
                       ↳ def ifAllZero : List NIdx → AM PropWhen
T      509-518    10L  def toList (pw : PropWhen) : List Name
                       ↳ def toList (pw : PropWhen) : AM (List NIdx)
T      520-525     6L  def toList? (pw : PropWhen) : Option (List Name)
                       ↳ def toList? (pw : PropWhen) : AM (Option (List NIdx))
S(T)   643-660    18L  def casesZ {motive : PropWhen → Sort u} (never : motive .never) (ifAllZero : (ps : List Name) → motive (PropWhen.ifAllZero ps)) : (pw : PropWhen) → motive pw
                       ↳ Rust port skips it: The registered `cases`/`induction` eliminator of `PropWhen` — an elaboration-time device for writing proofs against the two-constructor view, with no run-time content.
S(T)   662-680    19L  def reprPrec' (pw : PropWhen) (prec : Nat) : Std.Format
                       ↳ Rust port skips it: The `Repr` instance's renderer, kept byte-identical for `#eval (repr …)` of a stored pin.
T      691-700    10L  def holds (φ : Name → Nat) (pw : PropWhen) : Bool
                       ↳ def holds (φ : NIdx → Nat) (pw : PropWhen) : AM Bool
P      716-738    23L  def isNever (pw : PropWhen) : Bool
T      751-759     9L  def hasParams (pw : PropWhen) : Bool
                       ↳ def hasParams (pw : PropWhen) : AM Bool
T      778-789    12L  def paramsDefined (params : List Name) (pw : PropWhen) : Bool
                       ↳ def paramsDefined (params : List NIdx) (pw : PropWhen) : AM Bool
P      861-874    14L  def inter (a b : PropWhen) : PropWhen
T      938-941     4L  def bindZ.go (f : Name → PropWhen) : List Name → PropWhen
                       ↳ def bindZ.go (f : NIdx → PropWhen) : List NIdx → AM PropWhen
T      943-955    13L  def bindZ (f : Name → PropWhen) (pw : PropWhen) : PropWhen
                       ↳ def bindZ (f : NIdx → PropWhen) (pw : PropWhen) : AM PropWhen
```

### `ConLeche/Kernel/PropRead.lean` — 10 decls, 99 lines (9T 1P 0S)

```
T       44-56     13L  def peelNeverPis : Nat → Expr → Option Expr
                       ↳ def peelNeverPis : Nat → EIdx → AM (Option EIdx)
T       58-61      4L  def numArgs : Expr → Nat
                       ↳ def numArgs : EIdx → AM Nat
T       65-71      7L  def residualPW : Option Expr → Option PropWhen
                       ↳ def residualPW : Option EIdx → AM (Option PropWhen)
T       73-90     18L  def headTypePW (find? : Name → Option ConstantInfo) : Expr → Nat → Option PropWhen
                       ↳ def headTypePW (find? : NIdx → Option IConstantInfo) : EIdx → Nat → AM (Option PropWhen)
T       92-103    12L  def typeSortPW (find? : Name → Option ConstantInfo) (T : Expr) : Option PropWhen
                       ↳ def typeSortPW (find? : NIdx → Option IConstantInfo) (T : EIdx) : AM (Option PropWhen)
T      105-122    18L  def headProofPW (find? : Name → Option ConstantInfo) : Expr → Option PropWhen
                       ↳ def headProofPW (find? : NIdx → Option IConstantInfo) : EIdx → AM (Option PropWhen)
T      124-134    11L  def proofPW (find? : Name → Option ConstantInfo) (a : Expr) : Option PropWhen
                       ↳ def proofPW (find? : NIdx → Option IConstantInfo) (a : EIdx) : AM (Option PropWhen)
P      136-139     4L  def PropWhen.isProp (pw : PropWhen) : Bool
T      141-146     6L  def notProofFast (find? : Name → Option ConstantInfo) (a : Expr) : Bool
                       ↳ def notProofFast (find? : NIdx → Option IConstantInfo) (a : EIdx) : AM Bool
T      148-153     6L  def isProofFast (find? : Name → Option ConstantInfo) (a : Expr) : Bool
                       ↳ def isProofFast (find? : NIdx → Option IConstantInfo) (a : EIdx) : AM Bool
```

### `ConLeche/Kernel/Env.lean` — 41 decls, 628 lines (27T 14P 0S)

```
P       20-62     43L  inductive CheckMode
P       64-71      8L  def CheckMode.ttChecks : CheckMode → Bool
P       73-84     12L  def CheckMode.verifiedChecks : CheckMode → Bool
P       86-111    26L  def CheckMode.betaGate : CheckMode → Bool
P      113-132    20L  def CheckMode.ioGate : CheckMode → Bool
P      134-165    32L  def CheckMode.certs : CheckMode → Bool
P      167-175     9L  def CheckMode.betaSkip (mode : CheckMode) (pw : PropWhen) : Bool
P      177-184     8L  def CheckMode.ioSkip (mode : CheckMode) (pw : PropWhen) : Bool
T      186-191     6L  structure ConstantVal where
                       ↳ structure IConstantVal where
T      193-237    45L  inductive RecRuleFire
                       ↳ inductive RecRuleFire
T      239-282    44L  structure RecRule where
                       ↳ structure IRecRule where
T      284-291     8L  def RecRule.compareParams (rl : RecRule) : Bool
                       ↳ def IRecRule.compareParams (rl : IRecRule) : AM Bool
P      302-312    11L  inductive ReducibilityHint
P      316-324     9L  def lt : ReducibilityHint → ReducibilityHint → Bool
P      326-336    11L  def sameRegular : ReducibilityHint → ReducibilityHint → Bool
P      340-344     5L  inductive BasisKind
T      347-374    28L  structure IndCaps where
                       ↳ structure IIndCaps where
T      376-431    56L  structure ProjTable where
                       ↳ structure ProjTable where
T      433-452    20L  structure ProjEntry where
                       ↳ structure IProjEntry where
T      454-458     5L  def ProjTable.entry (tbl : ProjTable) (i : Nat) : ProjEntry
                       ↳ def ProjTable.entry (tbl : ProjTable) (i : Nat) : AM IProjEntry
T      460-486    27L  inductive ConstantInfo
                       ↳ inductive IConstantInfo
P      488-499    12L  inductive QuotKind
P      501-504     4L  def QuotKind.slot : QuotKind → Nat
T      506-560    55L  inductive Declaration
                       ↳ inductive IDeclaration
T      564-568     5L  def name : Declaration → Name
                       ↳ def name : IDeclaration → AM NIdx
T      572-586    15L  def Expr.piSortTeleLen? : Expr → Option Nat
                       ↳ def EIdx.piSortTeleLen? : EIdx → AM (Option Nat)
T      588-621    34L  def indParamsOk (nP : Nat) (block : List ConstantInfo) : Bool
                       ↳ def indParamsOk (nP : Nat) (block : List IConstantInfo) : AM Bool
T      623-629     7L  def projFnName (T : Name) (i : Nat) : Name
                       ↳ def projFnName (T : NIdx) (i : Nat) : AM NIdx
T      631-635     5L  def projTableName (T : Name) : Name
                       ↳ def projTableName (T : NIdx) : AM NIdx
T      639-642     4L  def toConstantVal : ConstantInfo → ConstantVal
                       ↳ def toConstantVal : IConstantInfo → AM IConstantVal
T      644-644     1L  def name (c : ConstantInfo) : Name
                       ↳ def name (c : IConstantInfo) : AM NIdx
T      646-651     6L  def isTowerEntry : ConstantInfo → Bool
                       ↳ def isTowerEntry : IConstantInfo → AM Bool
T      653-653     1L  def type (c : ConstantInfo) : Expr
                       ↳ def type (c : IConstantInfo) : AM EIdx
T      659-670    12L  def names : Declaration → List Name
                       ↳ def names : IDeclaration → AM (List NIdx)
T      674-679     6L  structure Env where
                       ↳ structure IEnv where
T      683-684     2L  def empty : Env
                       ↳ def empty : AM IEnv
T      686-687     2L  def find? (env : Env) (n : Name) : Option ConstantInfo
                       ↳ def find? (env : IEnv) (n : NIdx) : AM (Option IConstantInfo)
T      689-695     7L  def findProj? (env : Env) (T : Name) (i : Nat) : Option ProjEntry
                       ↳ def findProj? (env : IEnv) (T : NIdx) (i : Nat) : AM (Option IProjEntry)
T      715-718     4L  def ConstantInfo.isRecInfo : ConstantInfo → Bool
                       ↳ def IConstantInfo.isRecInfo : IConstantInfo → AM Bool
T      720-725     6L  def recsFormSuffix : List ConstantInfo → Bool
                       ↳ def recsFormSuffix : List IConstantInfo → AM Bool
T      786-792     7L  instance blockRecSuffixDec (block : List ConstantInfo) : Decidable (block = block.filter (fun ci => match ci with
                       ↳ instance blockRecSuffixDec (block : List IConstantInfo) : AM (Decidable (block = block.filter (fun ci => match ci with)
```

### `ConLeche/Kernel/FEnv.lean` — 14 decls, 104 lines (14T 0P 0S)

```
T       29-49     21L  structure FEnv where
                       ↳ structure IFEnv where
T       51-60     10L  def mkFEnvGo : List ConstantInfo → Nat × Std.HashMap Name (Nat × ConstantInfo)
                       ↳ def mkFEnvGo : List IConstantInfo → AM (Nat × Std.HashMap NIdx (Nat × IConstantInfo))
T       62-66      5L  def mkFEnv (env : Env) : FEnv
                       ↳ def mkFEnv (env : IEnv) : AM IFEnv
T       70-75      6L  def find? (fe : FEnv) (n : Name) : Option ConstantInfo
                       ↳ def find? (fe : IFEnv) (n : NIdx) : AM (Option IConstantInfo)
T       77-80      4L  def restrictTo (fe : FEnv) (k : Nat) : FEnv
                       ↳ def restrictTo (fe : IFEnv) (k : Nat) : AM IFEnv
T       82-89      8L  def push (fe : FEnv) (ci : ConstantInfo) : FEnv
                       ↳ def push (fe : IFEnv) (ci : IConstantInfo) : AM IFEnv
T       91-95      5L  def findProj? (fe : FEnv) (T : Name) (i : Nat) : Option ProjEntry
                       ↳ def findProj? (fe : IFEnv) (T : NIdx) (i : Nat) : AM (Option IProjEntry)
T       97-99      3L  def towerSlotsAllF (fe : FEnv) (T : Name) (nF : Nat) : Bool
                       ↳ def towerSlotsAllF (fe : IFEnv) (T : NIdx) (nF : Nat) : AM Bool
T      101-103     3L  def andRescueSlotsF (fe : FEnv) (ctor : Name) (nP : Nat) (ust : List Level) : Bool
                       ↳ def andRescueSlotsF (fe : IFEnv) (ctor : NIdx) (nP : Nat) (ust : LsIdx) : AM Bool
T      105-110     6L  def recSlotsAllF (fe : FEnv) (T : Name) (nF : Nat) : Bool
                       ↳ def recSlotsAllF (fe : IFEnv) (T : NIdx) (nF : Nat) : AM Bool
T      116-119     4L  def natLitSupportedF (fe : FEnv) : Bool
                       ↳ def natLitSupportedF (fe : IFEnv) : AM Bool
T      121-130    10L  def strLitSupportedF (fe : FEnv) : Bool
                       ↳ def strLitSupportedF (fe : IFEnv) : AM Bool
T      132-145    14L  def natOpGuardF (fe : FEnv) (c : Name) : Bool
                       ↳ def natOpGuardF (fe : IFEnv) (c : NIdx) : AM Bool
T      147-151     5L  def natOpStoredF (fe : FEnv) (c : Name) : Bool
                       ↳ def natOpStoredF (fe : IFEnv) (c : NIdx) : AM Bool
```

### `ConLeche/Kernel/Core.lean` — 127 decls, 2660 lines (117T 10P 0S)

```
P       47-66     20L  inductive CheckError
P       74-74      1L  abbrev CheckM
T       76-96     21L  def unknownConstError (n : Name) : CheckError
                       ↳ def unknownConstError (n : NIdx) : AM CheckError
T       98-124    27L  structure CoreFns (m : Type → Type u) where
                       ↳ structure CoreFns (m : Type → Type u) where
P      126-132     7L  def CoreFns.ioView {m : Type → Type u} (r : CoreFns m) : CoreFns m
P      145-148     4L  def liftFueled (what : String) : Option α → m α
T      150-153     4L  def projModelName (T : Name) (i : Nat) : Name
                       ↳ def projModelName (T : NIdx) (i : Nat) : AM NIdx
T      155-162     8L  def isCtorApp (env : Env) (e : Expr) : Bool
                       ↳ def isCtorApp (env : IEnv) (e : EIdx) : AM Bool
T      164-171     8L  def piResultIsProp (e : Expr) : Bool
                       ↳ def piResultIsProp (e : EIdx) : AM Bool
T      173-181     9L  def piResultZ (e : Expr) : PropWhen
                       ↳ def piResultZ (e : EIdx) : AM PropWhen
T      183-191     9L  def piResultNeverZero (lps : List Name) (us : List Level) (e : Expr) : Bool
                       ↳ def piResultNeverZero (lps : List NIdx) (us : LsIdx) (e : EIdx) : AM Bool
T      193-204    12L  def capsNeverZero (lps : List Name) (us : List Level) (caps : IndCaps) : Bool
                       ↳ def capsNeverZero (lps : List NIdx) (us : LsIdx) (caps : IIndCaps) : AM Bool
T      206-243    38L  def isUnitLikeTy (env : Env) : Expr → Bool
                       ↳ def isUnitLikeTy (env : IEnv) : EIdx → AM Bool
T      245-264    20L  def unfoldDefinition (env : Env) (e : Expr) : Option Expr
                       ↳ def unfoldDefinition (env : IEnv) (e : EIdx) : AM (Option EIdx)
T      266-279    14L  def unfoldableHead (env : Env) (e : Expr) : Bool
                       ↳ def unfoldableHead (env : IEnv) (e : EIdx) : AM Bool
T      281-290    10L  def headHint (env : Env) (e : Expr) : ReducibilityHint
                       ↳ def headHint (env : IEnv) (e : EIdx) : AM ReducibilityHint
T      292-301    10L  def sameConstHeads : Expr → Expr → Bool
                       ↳ def sameConstHeads : EIdx → EIdx → AM Bool
T      303-309     7L  def natLitToConstructor (n : Nat) : Expr
                       ↳ def natLitToConstructor (n : Nat) : AM EIdx
T      311-315     5L  def natIndOk : Option ConstantInfo → Bool
                       ↳ def natIndOk : Option IConstantInfo → AM Bool
T      317-321     5L  def natZeroOk : Option ConstantInfo → Bool
                       ↳ def natZeroOk : Option IConstantInfo → AM Bool
T      323-332    10L  def natSuccOk : Option ConstantInfo → Bool
                       ↳ def natSuccOk : Option IConstantInfo → AM Bool
T      334-342     9L  def natLitSupported (env : Env) : Bool
                       ↳ def natLitSupported (env : IEnv) : AM Bool
T      344-369    26L  def Expr.constsResolve (env : Env) : Expr → Bool
                       ↳ def EIdx.constsResolve (env : IEnv) : EIdx → AM Bool
T      371-376     6L  def litToCtorIfNat (env : Env) : Expr → Expr
                       ↳ def litToCtorIfNat (env : IEnv) : EIdx → AM EIdx
T      378-383     6L  def rawNatLit? : Expr → Option Nat
                       ↳ def rawNatLit? : EIdx → AM (Option Nat)
T      397-408    12L  def strLitToConstructor (s : String) : Expr
                       ↳ def strLitToConstructor (s : String) : AM EIdx
T      410-416     7L  def stringTyOk : Option ConstantInfo → Bool
                       ↳ def stringTyOk : Option IConstantInfo → AM Bool
T      418-424     7L  def charTyOk : Option ConstantInfo → Bool
                       ↳ def charTyOk : Option IConstantInfo → AM Bool
T      426-437    12L  def listTyOk : Option ConstantInfo → Bool
                       ↳ def listTyOk : Option IConstantInfo → AM Bool
T      439-450    12L  def listNilTyOk : Option ConstantInfo → Bool
                       ↳ def listNilTyOk : Option IConstantInfo → AM Bool
T      452-469    18L  def listConsTyOk : Option ConstantInfo → Bool
                       ↳ def listConsTyOk : Option IConstantInfo → AM Bool
T      471-480    10L  def charOfNatTyOk : Option ConstantInfo → Bool
                       ↳ def charOfNatTyOk : Option IConstantInfo → AM Bool
T      482-492    11L  def stringOfListTyOk : Option ConstantInfo → Bool
                       ↳ def stringOfListTyOk : Option IConstantInfo → AM Bool
T      494-512    19L  def strLitSupported (env : Env) : Bool
                       ↳ def strLitSupported (env : IEnv) : AM Bool
T      542-542     1L  def natPredName : Name
                       ↳ def natPredName : AM NIdx
T      543-543     1L  def natAddName : Name
                       ↳ def natAddName : AM NIdx
T      544-544     1L  def natSubName : Name
                       ↳ def natSubName : AM NIdx
T      545-545     1L  def natMulName : Name
                       ↳ def natMulName : AM NIdx
T      546-546     1L  def natPowName : Name
                       ↳ def natPowName : AM NIdx
T      547-547     1L  def natBeqName : Name
                       ↳ def natBeqName : AM NIdx
T      548-548     1L  def natBleName : Name
                       ↳ def natBleName : AM NIdx
T      549-549     1L  def natDivName : Name
                       ↳ def natDivName : AM NIdx
T      550-550     1L  def natModName : Name
                       ↳ def natModName : AM NIdx
T      551-551     1L  def natGcdName : Name
                       ↳ def natGcdName : AM NIdx
T      552-552     1L  def natLandName : Name
                       ↳ def natLandName : AM NIdx
T      553-553     1L  def natLorName : Name
                       ↳ def natLorName : AM NIdx
T      554-554     1L  def natXorName : Name
                       ↳ def natXorName : AM NIdx
T      555-555     1L  def natShiftLeftName : Name
                       ↳ def natShiftLeftName : AM NIdx
T      556-556     1L  def natShiftRightName : Name
                       ↳ def natShiftRightName : AM NIdx
T      557-557     1L  def boolName : Name
                       ↳ def boolName : AM NIdx
T      558-558     1L  def boolTrueName : Name
                       ↳ def boolTrueName : AM NIdx
T      559-559     1L  def boolFalseName : Name
                       ↳ def boolFalseName : AM NIdx
T      561-566     6L  def Expr.isBoolTrue : Expr → Bool
                       ↳ def EIdx.isBoolTrue : EIdx → AM Bool
T      568-580    13L  def Expr.quickPair : Expr → Expr → Bool
                       ↳ def EIdx.quickPair : EIdx → EIdx → AM Bool
T      582-590     9L  def natOpNames : List Name
                       ↳ def natOpNames : AM (List NIdx)
T      592-607    16L  def natDivModNames : List Name
                       ↳ def natDivModNames : AM (List NIdx)
T      609-632    24L  def natOpDeps (c : Name) : List Name
                       ↳ def natOpDeps (c : NIdx) : AM (List NIdx)
T      634-663    30L  def natOpEquations (d : Nat) (c : Name) : List (Expr × Expr)
                       ↳ def natOpEquations (d : Nat) (c : NIdx) : AM (List (EIdx × EIdx))
T      665-691    27L  def natOpResult (c : Name) (a b : Nat) : Option Expr
                       ↳ def natOpResult (c : NIdx) (a b : Nat) : AM (Option EIdx)
T      693-709    17L  def natOpGuard (env : Env) (c : Name) : Bool
                       ↳ def natOpGuard (env : IEnv) (c : NIdx) : AM Bool
T      711-721    11L  def natOpWfNames : List Name
                       ↳ def natOpWfNames : AM (List NIdx)
T      723-729     7L  def Expr.substConst0 (n : Name) (r : Expr) : Expr → Expr
                       ↳ def EIdx.substConst0 (n : NIdx) (r : EIdx) : EIdx → AM EIdx
T      731-747    17L  def Expr.substConstAll (n : Name) (r : Expr) : Expr → Expr
                       ↳ def EIdx.substConstAll (n : NIdx) (r : EIdx) : EIdx → AM EIdx
T      749-759    11L  def natOpCod (env : Env) (c : Name) (e : Expr) : Bool
                       ↳ def natOpCod (env : IEnv) (c : NIdx) (e : EIdx) : AM Bool
T      761-776    16L  def natOpTyPinned (env : Env) (c : Name) (ty : Expr) : Bool
                       ↳ def natOpTyPinned (env : IEnv) (c : NIdx) (ty : EIdx) : AM Bool
T      778-784     7L  def natOpStoredOk (env : Env) (n : Name) : Bool
                       ↳ def natOpStoredOk (env : IEnv) (n : NIdx) : AM Bool
T      786-809    24L  def natOpStored (env : Env) (c : Name) : Bool
                       ↳ def natOpStored (env : IEnv) (c : NIdx) : AM Bool
T      811-863    53L  def reduceNat (r : CoreFns m) (env : Env) (depth : Nat) (e : Expr) : m (Option Expr)
                       ↳ def reduceNat (r : CoreFns) (env : IEnv) (depth : Nat) (e : EIdx) : AM (Option EIdx)
T      865-897    33L  def iotaCerts (r : CoreFns m) (env : Env) (depth : Nat) (lic : Bool) : Expr → List Expr → m Bool
                       ↳ def iotaCerts (r : CoreFns) (env : IEnv) (depth : Nat) (lic : Bool) : EIdx → List EIdx → AM Bool
T      899-904     6L  def piResidual : Expr → List Expr → Option Expr
                       ↳ def piResidual : EIdx → List EIdx → AM (Option EIdx)
T      906-915    10L  def defEqList (r : CoreFns m) (env : Env) (depth : Nat) : List Expr → List Expr → m Bool
                       ↳ def defEqList (r : CoreFns) (env : IEnv) (depth : Nat) : List EIdx → List EIdx → AM Bool
T      917-933    17L  def iotaIndexOk (r : CoreFns m) (env : Env) (depth : Nat) (mI rP cnP : Nat) (tyCtor : Expr) (margs idx : List Expr) : m Bool
                       ↳ def iotaIndexOk (r : CoreFns) (env : IEnv) (depth : Nat) (mI rP cnP : Nat) (tyCtor : EIdx) (margs idx : List EIdx) : AM Bool
T      935-966    32L  def proofIrrel (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) : m Bool
                       ↳ def proofIrrel (r : CoreFns) (env : IEnv) (depth : Nat) (a b : EIdx) : AM Bool
T      968-1010   43L  def propIrrel (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) : m Bool
                       ↳ def propIrrel (r : CoreFns) (env : IEnv) (depth : Nat) (a b : EIdx) : AM Bool
T     1012-1035   24L  def structEtaProjCerts (r : CoreFns m) (env : Env) (depth : Nat) (T : Name) (us' : List Level) (targs : List Expr) (b : Expr) (lpsT : List Name) : List Nat → m Bool
                       ↳ def structEtaProjCerts (r : CoreFns) (env : IEnv) (depth : Nat) (T : NIdx) (us' : LsIdx) (targs : List EIdx) (b : EIdx) (lpsT : List NIdx) : List Nat → AM Bool
T     1037-1042    6L  def towerSlotsAll (env : Env) (T : Name) (nF : Nat) : Bool
                       ↳ def towerSlotsAll (env : IEnv) (T : NIdx) (nF : Nat) : AM Bool
T     1044-1052    9L  def recSlotsAll (env : Env) (T : Name) (nF : Nat) : Bool
                       ↳ def recSlotsAll (env : IEnv) (T : NIdx) (nF : Nat) : AM Bool
T     1054-1064   11L  def etaProjs (env : Env) (T : Name) (us : List Level) (targs : List Expr) (b : Expr) (nF : Nat) : List Expr
                       ↳ def etaProjs (env : IEnv) (T : NIdx) (us : LsIdx) (targs : List EIdx) (b : EIdx) (nF : Nat) : AM (List EIdx)
T     1066-1138   73L  def structEtaCertWith (r : CoreFns m) (env : Env) (depth : Nat) (a b wtb : Expr) : m Bool
                       ↳ def structEtaCertWith (r : CoreFns) (env : IEnv) (depth : Nat) (a b wtb : EIdx) : AM Bool
T     1140-1151   12L  def etaCtorShape (env : Env) (a : Expr) : Bool
                       ↳ def etaCtorShape (env : IEnv) (a : EIdx) : AM Bool
T     1153-1176   24L  def structEtaCert (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) : m Bool
                       ↳ def structEtaCert (r : CoreFns) (env : IEnv) (depth : Nat) (a b : EIdx) : AM Bool
T     1178-1206   29L  def structUnitCert (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) : m Bool
                       ↳ def structUnitCert (r : CoreFns) (env : IEnv) (depth : Nat) (a b : EIdx) : AM Bool
T     1208-1233   26L  def etaCert (mode : CheckMode) (r : CoreFns m) (_env : Env) (depth : Nat) (ty₁ body₁ : Expr) (m₁ : BinderMeta) (b : Expr) : m Bool
                       ↳ def etaCert (mode : CheckMode) (r : CoreFns) (_env : IEnv) (depth : Nat) (ty₁ body₁ : EIdx) (m₁ : BinderMeta) (b : EIdx) : AM Bool
T     1235-1245   11L  def stuckIrrel (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) : m Bool
                       ↳ def stuckIrrel (r : CoreFns) (env : IEnv) (depth : Nat) (a b : EIdx) : AM Bool
T     1247-1255    9L  def etaFabArgs (T : Name) (ust : List Level) (targs : List Expr) (major : Expr) (nF : Nat) : List Expr
                       ↳ def etaFabArgs (T : NIdx) (ust : LsIdx) (targs : List EIdx) (major : EIdx) (nF : Nat) : AM (List EIdx)
T     1257-1262    6L  def etaFabArgsE (env : Env) (T : Name) (ust : List Level) (targs : List Expr) (major : Expr) (nF : Nat) : List Expr
                       ↳ def etaFabArgsE (env : IEnv) (T : NIdx) (ust : LsIdx) (targs : List EIdx) (major : EIdx) (nF : Nat) : AM (List EIdx)
T     1264-1290   27L  def ProjEntry.fireOk (entry : ProjEntry) (us : List Level) : Bool
                       ↳ def IProjEntry.fireOk (entry : IProjEntry) (us : LsIdx) : AM Bool
T     1292-1305   14L  def andRescueSlotsOf (findProj? : Name → Nat → Option ProjEntry) (ctor : Name) (nP : Nat) (ust : List Level) : Bool
                       ↳ def andRescueSlotsOf (findProj? : NIdx → Nat → Option IProjEntry) (ctor : NIdx) (nP : Nat) (ust : LsIdx) : AM Bool
T     1307-1309    3L  def andRescueSlots (env : Env) (ctor : Name) (nP : Nat) (ust : List Level) : Bool
                       ↳ def andRescueSlots (env : IEnv) (ctor : NIdx) (nP : Nat) (ust : LsIdx) : AM Bool
T     1311-1493  183L  def majorToCtor (r : CoreFns m) (env : Env) (depth : Nat) (_recName : Name) (rules : List RecRule) (major : Expr) : m Expr
                       ↳ def majorToCtor (r : CoreFns) (env : IEnv) (depth : Nat) (_recName : NIdx) (rules : List IRecRule) (major : EIdx) : AM EIdx
T     1495-1507   13L  def litMajorToCtor (r : CoreFns m) (env : Env) (depth : Nat) : Expr → m Expr
                       ↳ def litMajorToCtor (r : CoreFns) (env : IEnv) (depth : Nat) : EIdx → AM EIdx
T     1509-1523   15L  def projLitToCtor (r : CoreFns m) (env : Env) (depth : Nat) : Expr → m Expr
                       ↳ def projLitToCtor (r : CoreFns) (env : IEnv) (depth : Nat) : EIdx → AM EIdx
T     1525-1540   16L  def recRuleKOf (find? : Name → Option ConstantInfo) (ctor : Name) : Bool
                       ↳ def recRuleKOf (find? : NIdx → Option IConstantInfo) (ctor : NIdx) : AM Bool
T     1542-1568   27L  def recRuleEtaOf (find? : Name → Option ConstantInfo) (recName ctor : Name) : Bool
                       ↳ def recRuleEtaOf (find? : NIdx → Option IConstantInfo) (recName ctor : NIdx) : AM Bool
T     1570-1580   11L  def recRuleBits (find? : Name → Option ConstantInfo) (recName : Name) (rl : RecRule) : RecRule
                       ↳ def recRuleBits (find? : NIdx → Option IConstantInfo) (recName : NIdx) (rl : IRecRule) : AM IRecRule
T     1619-1631   13L  def projFnRule (find? : Name → Option ConstantInfo) (T ctorName : Name) (pty : Expr) (nP nF i : Nat) (rhsA : Expr) : RecRule
                       ↳ def projFnRule (find? : NIdx → Option IConstantInfo) (T ctorName : NIdx) (pty : EIdx) (nP nF i : Nat) (rhsA : EIdx) : AM IRecRule
T     1649-1656    8L  def recRuleK (rules : List RecRule) : Bool
                       ↳ def recRuleK (rules : List IRecRule) : AM Bool
T     1658-1695   38L  def prepareMajor (r : CoreFns m) (env : Env) (depth : Nat) (recName : Name) (rules : List RecRule) (major : Expr) : m Expr
                       ↳ def prepareMajor (r : CoreFns) (env : IEnv) (depth : Nat) (recName : NIdx) (rules : List IRecRule) (major : EIdx) : AM EIdx
T     1697-1717   21L  def recFireComparands (rl : RecRule) (lps : List Name) (us : List Level) (cvjLps : List Name) (args : List Expr) (rP : Nat) : List Level × List Expr
                       ↳ def recFireComparands (rl : IRecRule) (lps : List NIdx) (us : LsIdx) (cvjLps : List NIdx) (args : List EIdx) (rP : Nat) : AM (LsIdx × List EIdx)
T     1719-1832  114L  def iotaRec (r : CoreFns m) (env : Env) (depth : Nat) (e : Expr) : m (Option Expr)
                       ↳ def iotaRec (r : CoreFns) (env : IEnv) (depth : Nat) (e : EIdx) : AM (Option EIdx)
T     1834-1843   10L  def ProjEntry.typeAt (entry : ProjEntry) (us : List Level) (targs : List Expr) (pe : Expr) : Expr
                       ↳ def IProjEntry.typeAt (entry : IProjEntry) (us : LsIdx) (targs : List EIdx) (pe : EIdx) : AM EIdx
T     1845-1880   36L  def projCert (r : CoreFns m) (env : Env) (depth : Nat) (lic : Bool) (c : Name) (us : List Level) (args : List Expr) : m Bool
                       ↳ def projCert (r : CoreFns) (env : IEnv) (depth : Nat) (lic : Bool) (c : NIdx) (us : LsIdx) (args : List EIdx) : AM Bool
T     1882-1894   13L  def projCertAt (r : CoreFns m) (env : Env) (depth : Nat) (verified lic : Bool) (c : Name) (us : List Level) (args : List Expr) : m Bool
                       ↳ def projCertAt (r : CoreFns) (env : IEnv) (depth : Nat) (verified lic : Bool) (c : NIdx) (us : LsIdx) (args : List EIdx) : AM Bool
P     1896-1928   33L  def betaGateFires (mode : CheckMode) (pw : PropWhen) : Bool
T     1930-2019   90L  def whnfCoreBody (r : CoreFns m) (env : Env) : Nat → Expr → m Expr
                       ↳ def whnfCoreBody (r : CoreFns) (env : IEnv) : Nat → EIdx → AM EIdx
T     2021-2029    9L  def whnfCoreLoopFuel : Nat
                       ↳ def whnfCoreLoopFuel : AM Nat
P     2031-2038    8L  def whnfLoopFuel : Nat
T     2040-2055   16L  def whnfStep (r : CoreFns m) (env : Env) (depth : Nat) (k : Expr → m Expr) (e : Expr) : m Expr
                       ↳ def whnfStep (r : CoreFns) (env : IEnv) (depth : Nat) (k : EIdx → AM EIdx) (e : EIdx) : AM EIdx
T     2057-2062    6L  def whnfLoop (r : CoreFns m) (env : Env) (depth : Nat) : Nat → Expr → m Expr
                       ↳ def whnfLoop (r : CoreFns) (env : IEnv) (depth : Nat) : Nat → EIdx → AM EIdx
T     2064-2066    3L  def whnfBody (r : CoreFns m) (env : Env) : Nat → Expr → m Expr
                       ↳ def whnfBody (r : CoreFns) (env : IEnv) : Nat → EIdx → AM EIdx
T     2068-2074    7L  def ensureSort (r : CoreFns m) (_env : Env) (depth : Nat) (e : Expr) : m Level
                       ↳ def ensureSort (r : CoreFns) (_env : IEnv) (depth : Nat) (e : EIdx) : AM LIdx
T     2076-2241  166L  def inferBody (r : CoreFns m) (env : Env) : Nat → Expr → m Expr
                       ↳ def inferBody (r : CoreFns) (env : IEnv) : Nat → EIdx → AM EIdx
T     2243-2371  129L  def inferBodyIO (r : CoreFns m) (env : Env) : Nat → Expr → m Expr
                       ↳ def inferBodyIO (r : CoreFns) (env : IEnv) : Nat → EIdx → AM EIdx
T     2373-2385   13L  def boolTrueShortcut (r : CoreFns m) (depth : Nat) (a : Expr) : m Bool
                       ↳ def boolTrueShortcut (r : CoreFns) (depth : Nat) (a : EIdx) : AM Bool
T     2387-2406   20L  def defeqSpine (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) : m Bool
                       ↳ def defeqSpine (r : CoreFns) (env : IEnv) (depth : Nat) (a b : EIdx) : AM Bool
T     2408-2668  261L  def defeqStep (r : CoreFns m) (env : Env) (depth : Nat) (k : Bool → Expr → Expr → m Bool) (pi : Bool) (a b : Expr) : m Bool
                       ↳ def defeqStep (r : CoreFns) (env : IEnv) (depth : Nat) (k : Bool → EIdx → EIdx → AM Bool) (pi : Bool) (a b : EIdx) : AM Bool
T     2670-2675    6L  def defeqLoop (r : CoreFns m) (env : Env) (depth : Nat) : Nat → Bool → Expr → Expr → m Bool
                       ↳ def defeqLoop (r : CoreFns) (env : IEnv) (depth : Nat) : Nat → Bool → EIdx → EIdx → AM Bool
P     2677-2681    5L  def defeqLoopFuel : Nat
T     2683-2686    4L  def defeqBody (r : CoreFns m) (env : Env) : Nat → Expr → Expr → m Bool
                       ↳ def defeqBody (r : CoreFns) (env : IEnv) : Nat → EIdx → EIdx → AM Bool
T     2688-2697   10L  def isPropType (r : CoreFns m) (env : Env) (depth : Nat) (ty : Expr) : m Bool
                       ↳ def isPropType (r : CoreFns) (env : IEnv) (depth : Nat) (ty : EIdx) : AM Bool
P     2713-2714    2L  def pwWritten (pw : PropWhen) : Bool
P     2716-2722    7L  def annotBinderMeta (pw? : Option PropWhen) (mb : BinderMeta) : BinderMeta
T     2724-2755   32L  def annotPwPi (r : CoreFns m) (env : Env) (depth : Nat) (body' : Expr) : m PropWhen
                       ↳ def annotPwPi (r : CoreFns) (env : IEnv) (depth : Nat) (body' : EIdx) : AM PropWhen
T     2757-2771   15L  def annotPwLam (r : CoreFns m) (env : Env) (depth : Nat) (body' : Expr) : m PropWhen
                       ↳ def annotPwLam (r : CoreFns) (env : IEnv) (depth : Nat) (body' : EIdx) : AM PropWhen
T     2773-2893  121L  def annotateBody (r : CoreFns m) (env : Env) : Nat → Expr → m Expr
                       ↳ def annotateBody (r : CoreFns) (env : IEnv) : Nat → EIdx → AM EIdx
T     2897-2936   40L  def coreKnot {m : Type → Type} [Monad m] [MonadExceptOf CheckError m] (mode : CheckMode) (env : Env) (wrap : CoreFns m → CoreFns m) : Nat → CoreFns m
                       ↳ def coreKnot {m : Type → Type} [Monad m] [MonadExceptOf CheckError m] (mode : CheckMode) (env : IEnv) (wrap : CoreFns → CoreFns) : Nat → AM CoreFns
P     2938-2941    4L  def checkFuel : Nat
```

### `ConLeche/Kernel/CoreIO.lean` — 3 decls, 38 lines (0T 0P 3S)

```
S(T)    91-119    29L  def coreKnotIO (env : Env) : Nat → CoreFns m
                       ↳ Rust port skips it: The io-grade knot variant: the port's `infer_at_i` carries the io grade as a runtime flag (task #18's deviation 4), so `coreKnotIO`/`pureFnsIO`/`inferTypeCoreIO` have no second spelling.
S(T)   121-124     4L  def pureFnsIO (env : Env) : Nat → CoreFns CheckM
                       ↳ Rust port skips it: The io-grade knot variant: the port's `infer_at_i` carries the io grade as a runtime flag (task #18's deviation 4), so `coreKnotIO`/`pureFnsIO`/`inferTypeCoreIO` have no second spelling.
S(T)   126-130     5L  def inferTypeCoreIO (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Expr
                       ↳ Rust port skips it: The io-grade knot variant: the port's `infer_at_i` carries the io grade as a runtime flag (task #18's deviation 4), so `coreKnotIO`/`pureFnsIO`/`inferTypeCoreIO` have no second spelling.
```

### `ConLeche/Kernel/CoreGated.lean` — 9 decls, 115 lines (0T 0P 9S)

```
S(T)    61-115    55L  def whnfCoreBodyGated (r : CoreFns m) (env : Env) : Nat → Expr → m Expr
                       ↳ Rust port skips it: The gated (proof-tier) variants of `Kernel/Core.lean`'s bodies and knot: not executed by the shipped path, and the port has one knot, the cached one (`cached::core_c`).
S(T)   117-150    34L  def coreKnotGated (env : Env) : Nat → CoreFns m
                       ↳ Rust port skips it: The gated (proof-tier) variants of `Kernel/Core.lean`'s bodies and knot: not executed by the shipped path, and the port has one knot, the cached one (`cached::core_c`).
S(T)   152-155     4L  def pureFnsGated (env : Env) : Nat → CoreFns CheckM
                       ↳ Rust port skips it: The gated (proof-tier) variants of `Kernel/Core.lean`'s bodies and knot: not executed by the shipped path, and the port has one knot, the cached one (`cached::core_c`).
S(T)   157-159     3L  def whnfCoreGated (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Expr
                       ↳ Rust port skips it: The gated (proof-tier) variants of `Kernel/Core.lean`'s bodies and knot: not executed by the shipped path, and the port has one knot, the cached one (`cached::core_c`).
S(T)   161-163     3L  def whnfGated (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Expr
                       ↳ Rust port skips it: The gated (proof-tier) variants of `Kernel/Core.lean`'s bodies and knot: not executed by the shipped path, and the port has one knot, the cached one (`cached::core_c`).
S(T)   165-168     4L  def inferTypeCoreGated (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Expr
                       ↳ Rust port skips it: The gated (proof-tier) variants of `Kernel/Core.lean`'s bodies and knot: not executed by the shipped path, and the port has one knot, the cached one (`cached::core_c`).
S(T)   170-173     4L  def isDefEqCoreGated (env : Env) (fuel depth : Nat) (a b : Expr) : CheckM Bool
                       ↳ Rust port skips it: The gated (proof-tier) variants of `Kernel/Core.lean`'s bodies and knot: not executed by the shipped path, and the port has one knot, the cached one (`cached::core_c`).
S(T)   175-178     4L  def annotateCoreGated (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Expr
                       ↳ Rust port skips it: The gated (proof-tier) variants of `Kernel/Core.lean`'s bodies and knot: not executed by the shipped path, and the port has one knot, the cached one (`cached::core_c`).
S(T)   180-183     4L  def ensureSortCoreGated (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Level
                       ↳ Rust port skips it: The gated (proof-tier) variants of `Kernel/Core.lean`'s bodies and knot: not executed by the shipped path, and the port has one knot, the cached one (`cached::core_c`).
```

### `ConLeche/Kernel/TypeChecker.lean` — 8 decls, 29 lines (7T 0P 1S)

```
S(T)    23-25      3L  def pureFns (env : Env) : Nat → CoreFns CheckM
                       ↳ Rust port skips it: The PURE knot at `CheckM`; §3.1 gives the port one knot — the cached one it executes (`cached::core_c`) — and `kernel/type_checker.rs`'s module note records the deviation, with every refinement lemma stated against `coreKnotI`.
T       27-29      3L  def whnfCore (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Expr
                       ↳ def whnfCore (env : IEnv) (fuel depth : Nat) (e : EIdx) : AM EIdx
T       31-33      3L  def whnf (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Expr
                       ↳ def whnf (env : IEnv) (fuel depth : Nat) (e : EIdx) : AM EIdx
T       35-38      4L  def inferTypeCore (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Expr
                       ↳ def inferTypeCore (env : IEnv) (fuel depth : Nat) (e : EIdx) : AM EIdx
T       40-46      7L  def inferTypeIO (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Expr
                       ↳ def inferTypeIO (env : IEnv) (fuel depth : Nat) (e : EIdx) : AM EIdx
T       48-50      3L  def isDefEqCore (env : Env) (fuel depth : Nat) (a b : Expr) : CheckM Bool
                       ↳ def isDefEqCore (env : IEnv) (fuel depth : Nat) (a b : EIdx) : AM Bool
T       52-54      3L  def annotateCore (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Expr
                       ↳ def annotateCore (env : IEnv) (fuel depth : Nat) (e : EIdx) : AM EIdx
T       56-58      3L  def ensureSortCore (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Level
                       ↳ def ensureSortCore (env : IEnv) (fuel depth : Nat) (e : EIdx) : AM LIdx
```

## P2d — `DeclCheck` / `Checker` / `CheckerBase` / `Canon` / pins / `Inductives`

the declaration check, the install routes (basis, struct, sum, native), the axiom lists, the `Nat`-operation pin gate and the canonicalisation.

**423 declarations, 5407 con-leche lines: 366 (T), 17 (P), 40 (S).**

### `ConLeche/Kernel/CheckerBase.lean` — 20 decls, 263 lines (17T 3P 0S)

```
T       25-53     29L  structure CheckerOps (m : Type → Type) where
                       ↳ structure CheckerOps (m : Type → Type) where
P       57-66     10L  def fueledOps (F : Nat) : CheckerOps CheckM
P       68-69      2L  def pureOps : CheckerOps CheckM
T       71-91     21L  def unresolvedConstsError (where_ : String) (e : Expr) : CheckError
                       ↳ def unresolvedConstsError (where_ : String) (e : EIdx) : AM CheckError
T       95-119    25L  def checkConstantVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal) : m ConstantVal
                       ↳ def checkConstantVal (env : IEnv) (cv : IConstantVal) : AM IConstantVal
T      121-128     8L  def domsMatchAux (g : Nat → Expr → Expr) (bs₁ bs₂ : List (Expr × BinderMeta)) (o₁ o₂ n : Nat) : Bool
                       ↳ def domsMatchAux (g : Nat → EIdx → EIdx) (bs₁ bs₂ : List (EIdx × BinderMeta)) (o₁ o₂ n : Nat) : AM Bool
T      130-140    11L  def openPisAtFvars : Nat → Expr → Nat → Option (List Expr × Expr)
                       ↳ def openPisAtFvars : Nat → EIdx → Nat → AM (Option (List EIdx × EIdx))
T      142-151    10L  def domsMatchAuxA (g : Nat → Expr → Expr) (bs₁ bs₂ : Array (Expr × BinderMeta)) (o₁ o₂ n : Nat) : Bool
                       ↳ def domsMatchAuxA (g : Nat → EIdx → EIdx) (bs₁ bs₂ : Array (EIdx × BinderMeta)) (o₁ o₂ n : Nat) : AM Bool
T      153-167    15L  def openPisAtFvarsFGo (acc : List Expr) : Nat → Expr → Nat → Option (List Expr × Expr)
                       ↳ def openPisAtFvarsFGo (acc : List EIdx) : Nat → EIdx → Nat → AM (Option (List EIdx × EIdx))
T      169-176     8L  def openPisAtFvarsF (n : Nat) (e : Expr) (i : Nat) : Option (List Expr × Expr)
                       ↳ def openPisAtFvarsF (n : Nat) (e : EIdx) (i : Nat) : AM (Option (List EIdx × EIdx))
T      178-190    13L  def checkTypedList (ops : CheckerOps m) (env : Env) (depth : Nat) : List Expr → List Expr → m Unit
                       ↳ def checkTypedList (env : IEnv) (depth : Nat) : List EIdx → List EIdx → AM Unit
T      192-206    15L  def checkAnnotList (ops : CheckerOps m) (env : Env) (depth : Nat) : List Expr → m Unit
                       ↳ def checkAnnotList (env : IEnv) (depth : Nat) : List EIdx → AM Unit
T      208-211     4L  def isEqHead : Expr → Bool
                       ↳ def isEqHead : EIdx → AM Bool
T      213-220     8L  def eqHeadLevel : Expr → Level
                       ↳ def eqHeadLevel : EIdx → AM LIdx
T      222-231    10L  def checkDefEqList (ops : CheckerOps m) (env : Env) (depth : Nat) : List Expr → List Expr → m Unit
                       ↳ def checkDefEqList (env : IEnv) (depth : Nat) : List EIdx → List EIdx → AM Unit
P      233-239     7L  def unwrapOr {α : Type} (o : Option α) (err : CheckError) : m α
T      241-247     7L  def Env.findCV? (env : Env) (n : Name) : Option ConstantVal
                       ↳ def IEnv.findCV? (env : IEnv) (n : NIdx) : AM (Option IConstantVal)
T      249-254     6L  def piResultSort (e : Expr) : Option Level
                       ↳ def piResultSort (e : EIdx) : AM (Option LIdx)
T      257-272    16L  def checkProjShape (pty ctorTy : Expr) (nP nF : Nat) : m Unit
                       ↳ def checkProjShape (pty ctorTy : EIdx) (nP nF : Nat) : AM Unit
T      274-311    38L  def checkProjRule (ops : CheckerOps m) (env' : Env) (pty : Expr) (cvj : ConstantVal) (lps : List Name) (nP nF i : Nat) : m Expr
                       ↳ def checkProjRule (env' : IEnv) (pty : EIdx) (cvj : IConstantVal) (lps : List NIdx) (nP nF i : Nat) : AM EIdx
```

### `ConLeche/Kernel/Checker.lean` — 22 decls, 587 lines (21T 1P 0S)

```
T       26-30      5L  def installBasisDecl (env : Env) (ci : ConstantInfo) : m Env
                       ↳ def installBasisDecl (env : IEnv) (ci : IConstantInfo) : AM IEnv
T       32-50     19L  def checkDefnVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint) : m Env
                       ↳ def checkDefnVal (env : IEnv) (cv : IConstantVal) (value : EIdx) (hint : ReducibilityHint) : AM IEnv
T       52-82     31L  def checkThmVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal) (value : Expr) : m Env
                       ↳ def checkThmVal (env : IEnv) (cv : IConstantVal) (value : EIdx) : AM IEnv
T       84-107    24L  def checkOpaqueVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal) (value : Expr) : m Env
                       ↳ def checkOpaqueVal (env : IEnv) (cv : IConstantVal) (value : EIdx) : AM IEnv
T      108-116     9L  def certifyNatEqs (ops : CheckerOps m) (env : Env) : List (Expr × Expr) → m Bool
                       ↳ def certifyNatEqs (env : IEnv) : List (EIdx × EIdx) → AM Bool
T      118-130    13L  def divModDeclPin (ps : NatOpPinSet) (c : Name) : Expr
                       ↳ def divModDeclPin (ps : INatOpPinSet) (c : NIdx) : AM EIdx
T      132-142    11L  def divModCertProofs (ps : NatOpPinSet) (c : Name) : List Expr
                       ↳ def divModCertProofs (ps : INatOpPinSet) (c : NIdx) : AM (List EIdx)
T      144-222    79L  def divModCertStmts (c : Name) : List (List Expr × Expr)
                       ↳ def divModCertStmts (c : NIdx) : AM (List (List EIdx × EIdx))
T      224-237    14L  def divModCertApplied (proofS : Expr) (hyps : List Expr) : Expr
                       ↳ def divModCertApplied (proofS : EIdx) (hyps : List EIdx) : AM EIdx
T      239-250    12L  def divModCertGuard (env : Env) (c : Name) (annVal : Expr) (hyps : List Expr) (eqE proof : Expr) : Bool
                       ↳ def divModCertGuard (env : IEnv) (c : NIdx) (annVal : EIdx) (hyps : List EIdx) (eqE proof : EIdx) : AM Bool
T      252-275    24L  def checkDivModCerts (ops : CheckerOps m) (env : Env) (c : Name) (annVal : Expr) : List (List Expr × Expr) → List Expr → m Bool
                       ↳ def checkDivModCerts (env : IEnv) (c : NIdx) (annVal : EIdx) : List (List EIdx × EIdx) → List EIdx → AM Bool
T      277-290    14L  def divModEnvGuard (env2 : Env) (c : Name) : Bool
                       ↳ def divModEnvGuard (env2 : IEnv) (c : NIdx) : AM Bool
T      292-297     6L  def divModPinGuard (ps : NatOpPinSet) (env : Env) (c : Name) : Bool
                       ↳ def divModPinGuard (ps : INatOpPinSet) (env : IEnv) (c : NIdx) : AM Bool
T      299-306     8L  def divModCertsGuard (ps : NatOpPinSet) (env : Env) (c : Name) (annVal : Expr) : Bool
                       ↳ def divModCertsGuard (ps : INatOpPinSet) (env : IEnv) (c : NIdx) (annVal : EIdx) : AM Bool
T      308-328    21L  def checkDivModPinAt (ops : CheckerOps m) (env : Env) (c : Name) (value' : Expr) (ps : NatOpPinSet) : m Bool
                       ↳ def checkDivModPinAt (env : IEnv) (c : NIdx) (value' : EIdx) (ps : INatOpPinSet) : AM Bool
P      330-336     7L  def divModAttemptReason (ps : NatOpPinSet) : Option CheckError → String
T      338-360    23L  def checkDivModPinLoop (ops : CheckerOps m) (env : Env) (c : Name) (value' : Expr) : List NatOpPinSet → List String → m Unit
                       ↳ def checkDivModPinLoop (env : IEnv) (c : NIdx) (value' : EIdx) : List INatOpPinSet → List String → AM Unit
T      362-388    27L  def checkDivModPin (ops : CheckerOps m) (pins : List NatOpPinSet) (env env2 : Env) (c : Name) : m Unit
                       ↳ def checkDivModPin (pins : List INatOpPinSet) (env env2 : IEnv) (c : NIdx) : AM Unit
T      390-425    36L  def checkReducePin (ops : CheckerOps m) (env env2 : Env) (c : Name) (value : Expr) : m Unit
                       ↳ def checkReducePin (env env2 : IEnv) (c : NIdx) (value : EIdx) : AM Unit
T      427-437    11L  def checkBasisDecl (env : Env) (kind : BasisKind) : m Env
                       ↳ def checkBasisDecl (env : IEnv) (kind : BasisKind) : AM IEnv
T      439-626   188L  def checkDecl (ops : CheckerOps m) (pins : List NatOpPinSet) (env : Env) (d : Declaration) : m Env
                       ↳ def checkDecl (pins : List INatOpPinSet) (env : IEnv) (d : IDeclaration) : AM IEnv
T      628-632     5L  def checkDeclsPure (ops : CheckerOps m) (pins : List NatOpPinSet) (ds : List Declaration) : m Env
                       ↳ def checkDeclsPure (pins : List INatOpPinSet) (ds : List IDeclaration) : AM IEnv
```

### `ConLeche/Kernel/CheckerSplit.lean` — 6 decls, 76 lines (4T 2P 0S)

```
P       36-42      7L  inductive ValueKind
P       44-48      5L  def ValueKind.word : ValueKind → String
T       50-59     10L  structure ValueGroup where
                       ↳ structure ValueGroup where
T       64-85     22L  def installConstantVal (ops : CheckerOps m) (env : Env) (cv : ConstantVal) : m ConstantVal
                       ↳ def installConstantVal (env : IEnv) (cv : IConstantVal) : AM IConstantVal
T       87-100    14L  def installValue (ops : CheckerOps m) (env : Env) (cv : ConstantVal) (value : Expr) : m Expr
                       ↳ def installValue (env : IEnv) (cv : IConstantVal) (value : EIdx) : AM EIdx
T      102-119    18L  def checkValueGroup (ops : CheckerOps m) (env : Env) (g : ValueGroup) : m Unit
                       ↳ def checkValueGroup (env : IEnv) (g : ValueGroup) : AM Unit
```

### `ConLeche/Kernel/CheckerGated.lean` — 2 decls, 13 lines (0T 0P 2S)

```
S(P)    27-37     11L  def fueledOpsGated (F : Nat) : CheckerOps CheckM
                       ↳ Rust port skips it: The gated `CheckerOps` instantiations (`fueledOpsGated`, `pureOpsGated`): the proof tier's variants of `fueledOps`/`pureOps`, which `kernel::type_checker` has once.
S(P)    39-40      2L  def pureOpsGated : CheckerOps CheckM
                       ↳ Rust port skips it: The gated `CheckerOps` instantiations (`fueledOpsGated`, `pureOpsGated`): the proof tier's variants of `fueledOps`/`pureOps`, which `kernel::type_checker` has once.
```

### `ConLeche/Kernel/DeclCheck.lean` — 40 decls, 739 lines (39T 0P 1S)

```
T       33-35      3L  def FEnv.findCV? (fe : FEnv) (n : Name) : Option ConstantVal
                       ↳ def IFEnv.findCV? (fe : IFEnv) (n : NIdx) : AM (Option IConstantVal)
T       37-58     22L  def Expr.constsResolveF (fe : FEnv) : Expr → Bool
                       ↳ def EIdx.constsResolveF (fe : IFEnv) : EIdx → AM Bool
S(T)    70-72      3L  def CRFMemoInv (fe : FEnv) (memo : Std.HashMap Expr Bool) : Prop
                       ↳ Rust port skips it: A `Prop`-valued memo invariant, as `ExprOps.lean`'s.
T       89-124    36L  def Expr.constsResolveFGo (fe : FEnv) (memo : Std.HashMap Expr Bool) : Expr → Bool × Std.HashMap Expr Bool
                       ↳ def EIdx.constsResolveFGo (fe : IFEnv) (memo : Std.HashMap EIdx Bool) : EIdx → AM (Bool × Std.HashMap EIdx Bool)
T      197-199     3L  def Expr.constsResolveFFast (fe : FEnv) (e : Expr) : Bool
                       ↳ def EIdx.constsResolveFFast (fe : IFEnv) (e : EIdx) : AM Bool
T      209-217     9L  def natOpCodF (fe : FEnv) (c : Name) (e : Expr) : Bool
                       ↳ def natOpCodF (fe : IFEnv) (c : NIdx) (e : EIdx) : AM Bool
T      219-231    13L  def natOpTyPinnedF (fe : FEnv) (c : Name) (ty : Expr) : Bool
                       ↳ def natOpTyPinnedF (fe : IFEnv) (c : NIdx) (ty : EIdx) : AM Bool
T      233-238     6L  def natOpStoredOkF (fe : FEnv) (n : Name) : Bool
                       ↳ def natOpStoredOkF (fe : IFEnv) (n : NIdx) : AM Bool
T      240-270    31L  def stdAxiomOkF (fe : FEnv) (cvA : ConstantVal) : Bool
                       ↳ def stdAxiomOkF (fe : IFEnv) (cvA : IConstantVal) : AM Bool
T      272-280     9L  def trustCompilerOkF (fe : FEnv) (cvA : ConstantVal) : Bool
                       ↳ def trustCompilerOkF (fe : IFEnv) (cvA : IConstantVal) : AM Bool
T      282-286     5L  def reduceStoredOkF (fe : FEnv) (c : Name) : Bool
                       ↳ def reduceStoredOkF (fe : IFEnv) (c : NIdx) : AM Bool
T      288-294     7L  def reduceElemOkF (fe : FEnv) (c : Name) : Bool
                       ↳ def reduceElemOkF (fe : IFEnv) (c : NIdx) : AM Bool
T      296-302     7L  def ofReduceAxOkF (fe : FEnv) (cvA : ConstantVal) : Bool
                       ↳ def ofReduceAxOkF (fe : IFEnv) (cvA : IConstantVal) : AM Bool
T      304-308     5L  def reducePinGuardF (fe : FEnv) (c : Name) : Bool
                       ↳ def reducePinGuardF (fe : IFEnv) (c : NIdx) : AM Bool
T      310-319    10L  def divModEnvGuardF (fe2 : FEnv) (c : Name) : Bool
                       ↳ def divModEnvGuardF (fe2 : IFEnv) (c : NIdx) : AM Bool
T      321-330    10L  def divModCertGuardF (fe : FEnv) (c : Name) (annVal : Expr) (hyps : List Expr) (eqE proof : Expr) : Bool
                       ↳ def divModCertGuardF (fe : IFEnv) (c : NIdx) (annVal : EIdx) (hyps : List EIdx) (eqE proof : EIdx) : AM Bool
T      332-336     5L  def divModPinGuardF (ps : NatOpPinSet) (fe : FEnv) (c : Name) : Bool
                       ↳ def divModPinGuardF (ps : INatOpPinSet) (fe : IFEnv) (c : NIdx) : AM Bool
T      338-342     5L  def divModCertsGuardF (ps : NatOpPinSet) (fe : FEnv) (c : Name) (annVal : Expr) : Bool
                       ↳ def divModCertsGuardF (ps : INatOpPinSet) (fe : IFEnv) (c : NIdx) (annVal : EIdx) : AM Bool
T      344-382    39L  def checkEtaThmF (fe : FEnv) (T ctorName : Name) (lps : List Name) (nP nF : Nat) : Bool
                       ↳ def checkEtaThmF (fe : IFEnv) (T ctorName : NIdx) (lps : List NIdx) (nP nF : Nat) : AM Bool
T      384-414    31L  def checkUnitThmF (fe : FEnv) (T : Name) (lps : List Name) (nP : Nat) : Bool
                       ↳ def checkUnitThmF (fe : IFEnv) (T : NIdx) (lps : List NIdx) (nP : Nat) : AM Bool
T      416-428    13L  def ctorResidualOkF (fe : FEnv) (T ctorName : Name) (lps : List Name) (nP nF : Nat) (eta : Bool) : Bool
                       ↳ def ctorResidualOkF (fe : IFEnv) (T ctorName : NIdx) (lps : List NIdx) (nP nF : Nat) (eta : Bool) : AM Bool
T      430-441    12L  def indBlockCapsF (fe : FEnv) (cvT cvC : ConstantVal) (nP nF : Nat) : IndCaps
                       ↳ def indBlockCapsF (fe : IFEnv) (cvT cvC : IConstantVal) (nP nF : Nat) : AM IIndCaps
T      463-485    23L  def checkConstantValF (ops : CheckerOps m) (fe : FEnv) (cv : ConstantVal) : m ConstantVal
                       ↳ def checkConstantValF (fe : IFEnv) (cv : IConstantVal) : AM IConstantVal
T      487-505    19L  def checkMemberValF (ops : CheckerOps m) (blockNames : List Name) (fe : FEnv) (cv : ConstantVal) : m ConstantVal
                       ↳ def checkMemberValF (blockNames : List NIdx) (fe : IFEnv) (cv : IConstantVal) : AM IConstantVal
T      507-573    67L  def checkIotaThmF (ops : CheckerOps m) (fe' feSelf : FEnv) (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr) (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal) (cnP cnF : Nat) (rhsA : Expr) : m Unit
                       ↳ def checkIotaThmF (fe' feSelf : IFEnv) (f : NIdx → NIdx) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx) (mI rP j : Nat) (r : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat) (rhsA : EIdx) : AM Unit
T      575-599    25L  def nestedRuleShapeF (fe' feSelf : FEnv) (cvName : Name) (lps : List Name) (tyA : Expr) (mI rP cnP j : Nat) : Option (List Level × List Expr)
                       ↳ def nestedRuleShapeF (fe' feSelf : IFEnv) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx) (mI rP cnP j : Nat) : AM (Option (LsIdx × List EIdx))
T      601-685    85L  def checkIotaThmNF (ops : CheckerOps m) (fe' feSelf : FEnv) (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr) (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal) (cnP cnF : Nat) (rhsA : Expr) : m RecRuleFire
                       ↳ def checkIotaThmNF (fe' feSelf : IFEnv) (f : NIdx → NIdx) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx) (mI rP j : Nat) (r : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat) (rhsA : EIdx) : AM RecRuleFire
T      687-716    30L  def checkIotaRuleF (ops : CheckerOps m) (fe' feSelf : FEnv) (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr) (mI rP j : Nat) (r : RecRule) : m RecRule
                       ↳ def checkIotaRuleF (fe' feSelf : IFEnv) (f : NIdx → NIdx) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx) (mI rP j : Nat) (r : IRecRule) : AM IRecRule
T      718-727    10L  def checkIotaRulesF (ops : CheckerOps m) (fe' feSelf : FEnv) (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr) (mI rP : Nat) : Nat → List RecRule → m (List RecRule)
                       ↳ def checkIotaRulesF (fe' feSelf : IFEnv) (f : NIdx → NIdx) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx) (mI rP : Nat) : Nat → List IRecRule → AM (List IRecRule)
T      729-746    18L  def checkProjLookupsF (fe : FEnv) (T ctorName : Name) (lps : List Name) (nP nF i : Nat) : m (ConstantVal × ConstantVal)
                       ↳ def checkProjLookupsF (fe : IFEnv) (T ctorName : NIdx) (lps : List NIdx) (nP nF i : Nat) : AM (IConstantVal × IConstantVal)
T      748-761    14L  def checkProjTyF (fe : FEnv) (T ctorName : Name) (lps : List Name) (mty : Expr) (nP nF : Nat) : m Expr
                       ↳ def checkProjTyF (fe : IFEnv) (T ctorName : NIdx) (lps : List NIdx) (mty : EIdx) (nP nF : Nat) : AM EIdx
T      763-795    33L  def checkProjRuleF (ops : CheckerOps m) (fe : FEnv) (pty : Expr) (cvj : ConstantVal) (lps : List Name) (nP nF i : Nat) : m Expr
                       ↳ def checkProjRuleF (fe : IFEnv) (pty : EIdx) (cvj : IConstantVal) (lps : List NIdx) (nP nF i : Nat) : AM EIdx
T      797-836    40L  def checkProjIotaF (ops : CheckerOps m) (fe : FEnv) (T ctorName : Name) (lps : List Name) (cvj : ConstantVal) (nP nF i : Nat) : m Unit
                       ↳ def checkProjIotaF (fe : IFEnv) (T ctorName : NIdx) (lps : List NIdx) (cvj : IConstantVal) (nP nF i : Nat) : AM Unit
T      838-853    16L  def checkDefnValF (ops : CheckerOps m) (fe : FEnv) (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint) : m FEnv
                       ↳ def checkDefnValF (fe : IFEnv) (cv : IConstantVal) (value : EIdx) (hint : ReducibilityHint) : AM IFEnv
T      855-859     5L  def installBasisDeclF (fe : FEnv) (ci : ConstantInfo) : m FEnv
                       ↳ def installBasisDeclF (fe : IFEnv) (ci : IConstantInfo) : AM IFEnv
T      861-875    15L  def checkDivModCertsF (ops : CheckerOps m) (fe : FEnv) (c : Name) (annVal : Expr) : List (List Expr × Expr) → List Expr → m Bool
                       ↳ def checkDivModCertsF (fe : IFEnv) (c : NIdx) (annVal : EIdx) : List (List EIdx × EIdx) → List EIdx → AM Bool
T      877-885     9L  def checkDivModPinAtF (ops : CheckerOps m) (fe : FEnv) (c : Name) (value' : Expr) (ps : NatOpPinSet) : m Bool
                       ↳ def checkDivModPinAtF (fe : IFEnv) (c : NIdx) (value' : EIdx) (ps : INatOpPinSet) : AM Bool
T      887-901    15L  def checkDivModPinLoopF (ops : CheckerOps m) (fe : FEnv) (c : Name) (value' : Expr) : List NatOpPinSet → List String → m Unit
                       ↳ def checkDivModPinLoopF (fe : IFEnv) (c : NIdx) (value' : EIdx) : List INatOpPinSet → List String → AM Unit
T      903-913    11L  def checkDivModPinF (ops : CheckerOps m) (pins : List NatOpPinSet) (fe fe2 : FEnv) (c : Name) : m Unit
                       ↳ def checkDivModPinF (pins : List INatOpPinSet) (fe fe2 : IFEnv) (c : NIdx) : AM Unit
T      915-934    20L  def checkReducePinF (ops : CheckerOps m) (fe fe2 : FEnv) (c : Name) (value : Expr) : m Unit
                       ↳ def checkReducePinF (fe fe2 : IFEnv) (c : NIdx) (value : EIdx) : AM Unit
```

### `ConLeche/Kernel/Canon.lean` — 13 decls, 139 lines (13T 0P 0S)

```
T       27-34      8L  def canonLevel (m : Name → Name) : Level → Level
                       ↳ def canonLevel (m : NIdx → NIdx) : LIdx → AM LIdx
T       36-65     30L  def canonExpr (m : Name → Name) : Expr → Expr
                       ↳ def canonExpr (m : NIdx → NIdx) : EIdx → AM EIdx
T       67-73      7L  def canonNameMap (ps : List Name) : Name → Name
                       ↳ def canonNameMap (ps : List NIdx) : NIdx → AM NIdx
T       75-80      6L  def ConstantVal.canon (cv : ConstantVal) : ConstantVal
                       ↳ def IConstantVal.canon (cv : IConstantVal) : AM IConstantVal
T       82-97     16L  def ConstantInfo.canon (ci : ConstantInfo) : ConstantInfo
                       ↳ def IConstantInfo.canon (ci : IConstantInfo) : AM IConstantInfo
T      126-146    21L  def canonExprEqFast (m m' : Name → Name) : Expr → Expr → Bool
                       ↳ def canonExprEqFast (m m' : NIdx → NIdx) : EIdx → EIdx → AM Bool
T      195-199     5L  def ConstantVal.canonEq (cv cv' : ConstantVal) : Bool
                       ↳ def IConstantVal.canonEq (cv cv' : IConstantVal) : AM Bool
T      201-206     6L  def ConstantVal.canonEqFast (cv cv' : ConstantVal) : Bool
                       ↳ def IConstantVal.canonEqFast (cv cv' : IConstantVal) : AM Bool
T      224-231     8L  def canonRulesEqFast (m m' : Name → Name) : List RecRule → List RecRule → Bool
                       ↳ def canonRulesEqFast (m m' : NIdx → NIdx) : List IRecRule → List IRecRule → AM Bool
T      250-252     3L  def ConstantInfo.canonEq (ci ci' : ConstantInfo) : Bool
                       ↳ def IConstantInfo.canonEq (ci ci' : IConstantInfo) : AM Bool
T      254-273    20L  def ConstantInfo.canonEqFast : ConstantInfo → ConstantInfo → Bool
                       ↳ def IConstantInfo.canonEqFast : IConstantInfo → IConstantInfo → AM Bool
T      289-292     4L  def canonEqList (xs ys : List ConstantInfo) : Bool
                       ↳ def canonEqList (xs ys : List IConstantInfo) : AM Bool
T      294-298     5L  def canonEqListFast : List ConstantInfo → List ConstantInfo → Bool
                       ↳ def canonEqListFast : List IConstantInfo → List IConstantInfo → AM Bool
```

### `ConLeche/Kernel/StdAxioms.lean` — 24 decls, 215 lines (24T 0P 0S)

```
T       38-39      2L  def propextName : Name
                       ↳ def propextName : AM NIdx
T       41-42      2L  def choiceName : Name
                       ↳ def choiceName : AM NIdx
T       44-45      2L  def iffName : Name
                       ↳ def iffName : AM NIdx
T       47-48      2L  def iffIntroName : Name
                       ↳ def iffIntroName : AM NIdx
T       50-51      2L  def iffRecName : Name
                       ↳ def iffRecName : AM NIdx
T       53-54      2L  def nonemptyName : Name
                       ↳ def nonemptyName : AM NIdx
T       56-57      2L  def nonemptyIntroName : Name
                       ↳ def nonemptyIntroName : AM NIdx
T       59-60      2L  def nonemptyRecName : Name
                       ↳ def nonemptyRecName : AM NIdx
T       62-113    52L  def Expr.erasePw : Expr → Expr
                       ↳ def EIdx.erasePw : EIdx → AM EIdx
T      115-117     3L  def ConstantVal.matchesPin (cv pin : ConstantVal) : Bool
                       ↳ def IConstantVal.matchesPin (cv pin : IConstantVal) : AM Bool
T      139-153    15L  def Expr.erasePwEq : Expr → Expr → Bool
                       ↳ def EIdx.erasePwEq : EIdx → EIdx → AM Bool
T      197-201     5L  def ConstantVal.matchesPinFast (cv pin : ConstantVal) : Bool
                       ↳ def IConstantVal.matchesPinFast (cv pin : IConstantVal) : AM Bool
T      208-210     3L  def iffRaw : ConstantInfo
                       ↳ def iffRaw : AM IConstantInfo
T      212-220     9L  def iffIntroRaw : ConstantInfo
                       ↳ def iffIntroRaw : AM IConstantInfo
T      222-227     6L  def iffRecIntro : Expr
                       ↳ def iffRecIntro : AM EIdx
T      229-239    11L  def iffRecRaw : ConstantInfo
                       ↳ def iffRecRaw : AM IConstantInfo
T      241-243     3L  def iffFamily : List ConstantInfo
                       ↳ def iffFamily : AM (List IConstantInfo)
T      245-252     8L  def propextRaw : ConstantVal
                       ↳ def propextRaw : AM IConstantVal
T      254-256     3L  def nonemptyRaw : ConstantInfo
                       ↳ def nonemptyRaw : AM IConstantInfo
T      258-264     7L  def nonemptyIntroRaw : ConstantInfo
                       ↳ def nonemptyIntroRaw : AM IConstantInfo
T      266-278    13L  def nonemptyRecRaw : ConstantInfo
                       ↳ def nonemptyRecRaw : AM IConstantInfo
T      280-282     3L  def nonemptyFamily : List ConstantInfo
                       ↳ def nonemptyFamily : AM (List IConstantInfo)
T      284-289     6L  def choiceRaw : ConstantVal
                       ↳ def choiceRaw : AM IConstantVal
T      313-364    52L  def stdAxiomOk (env : Env) (cvA : ConstantVal) : Bool
                       ↳ def stdAxiomOk (env : IEnv) (cvA : IConstantVal) : AM Bool
```

### `ConLeche/Kernel/TrustAxioms.lean` — 27 decls, 110 lines (26T 0P 1S)

```
T       51-52      2L  def trueName : Name
                       ↳ def trueName : AM NIdx
T       54-55      2L  def trueIntroName : Name
                       ↳ def trueIntroName : AM NIdx
T       57-58      2L  def trustCompilerName : Name
                       ↳ def trustCompilerName : AM NIdx
T       60-61      2L  def reduceNatName : Name
                       ↳ def reduceNatName : AM NIdx
T       63-64      2L  def reduceBoolName : Name
                       ↳ def reduceBoolName : AM NIdx
T       66-67      2L  def ofReduceNatName : Name
                       ↳ def ofReduceNatName : AM NIdx
T       69-70      2L  def ofReduceBoolName : Name
                       ↳ def ofReduceBoolName : AM NIdx
T       72-73      2L  def reduceOpNames : List Name
                       ↳ def reduceOpNames : AM (List NIdx)
T       75-77      3L  def ofReduceOp (n : Name) : Name
                       ↳ def ofReduceOp (n : NIdx) : AM NIdx
T       88-89      2L  def trueCvA : ConstantVal
                       ↳ def trueCvA : AM IConstantVal
T       91-92      2L  def trueIntroCvA : ConstantVal
                       ↳ def trueIntroCvA : AM IConstantVal
T       94-95      2L  def trustCompilerA : ConstantVal
                       ↳ def trustCompilerA : AM IConstantVal
T       97-98      2L  def boolCvA : ConstantVal
                       ↳ def boolCvA : AM IConstantVal
T      100-102     3L  def reduceElemName (c : Name) : Name
                       ↳ def reduceElemName (c : NIdx) : AM NIdx
T      104-106     3L  def reduceElemTy (c : Name) : Expr
                       ↳ def reduceElemTy (c : NIdx) : AM EIdx
T      108-110     3L  def reduceOpRaw (c : Name) : ConstantVal
                       ↳ def reduceOpRaw (c : NIdx) : AM IConstantVal
T      112-122    11L  def ofReduceRaw (n : Name) : ConstantVal
                       ↳ def ofReduceRaw (n : NIdx) : AM IConstantVal
S(T)   134-137     4L  private def trustPinEnv : List ConstantInfo
                       ↳ Rust port skips it: The private environment `#annotate_pins` is run over while `TrustAxioms.lean` elaborates; what the port carries is the annotated pins that command produces, which `trust_axioms.rs` holds.
T      148-150     3L  def reduceOpCvA (c : Name) : ConstantVal
                       ↳ def reduceOpCvA (c : NIdx) : AM IConstantVal
T      152-154     3L  def ofReducePinA (n : Name) : ConstantVal
                       ↳ def ofReducePinA (n : NIdx) : AM IConstantVal
T      158-169    12L  def trustCompilerOk (env : Env) (cvA : ConstantVal) : Bool
                       ↳ def trustCompilerOk (env : IEnv) (cvA : IConstantVal) : AM Bool
T      171-177     7L  def reduceStoredOk (env : Env) (c : Name) : Bool
                       ↳ def reduceStoredOk (env : IEnv) (c : NIdx) : AM Bool
T      179-186     8L  def reduceElemOk (env : Env) (c : Name) : Bool
                       ↳ def reduceElemOk (env : IEnv) (c : NIdx) : AM Bool
T      188-198    11L  def ofReduceAxOk (env : Env) (cvA : ConstantVal) : Bool
                       ↳ def ofReduceAxOk (env : IEnv) (cvA : IConstantVal) : AM Bool
T      202-207     6L  def reduceDeclPin (c : Name) : Expr
                       ↳ def reduceDeclPin (c : NIdx) : AM EIdx
T      209-213     5L  def reducePinGuard (env : Env) (c : Name) : Bool
                       ↳ def reducePinGuard (env : IEnv) (c : NIdx) : AM Bool
T      215-218     4L  def reduceCertVar (c : Name) : Expr
                       ↳ def reduceCertVar (c : NIdx) : AM EIdx
```

### `ConLeche/Kernel/TrustPins.lean` — 2 decls, 4 lines (2T 0P 0S)

```
T       42-43      2L  def reduceBoolDeclPin : Expr
                       ↳ def reduceBoolDeclPin : AM EIdx
T       45-46      2L  def reduceNatDeclPin : Expr
                       ↳ def reduceNatDeclPin : AM EIdx
```

### `ConLeche/Kernel/NatOpPinSet.lean` — 1 decls, 24 lines (1T 0P 0S)

```
T       28-51     24L  structure NatOpPinSet where
                       ↳ structure INatOpPinSet where
```

### `ConLeche/Kernel/Basis.lean` — 3 decls, 26 lines (3T 0P 0S)

```
T       40-47      8L  def BasisKind.decls : BasisKind → List ConstantInfo
                       ↳ def BasisKind.decls : BasisKind → AM (List IConstantInfo)
T       60-71     12L  def basisPinHit (block : List ConstantInfo) : Option BasisKind
                       ↳ def basisPinHit (block : List IConstantInfo) : AM (Option BasisKind)
T       73-78      6L  def quotPinHit (k : QuotKind) (cv : ConstantVal) : Bool
                       ↳ def quotPinHit (k : QuotKind) (cv : IConstantVal) : AM Bool
```

### `ConLeche/Kernel/BasisA.lean` — 1 decls, 8 lines (1T 0P 0S)

```
T       50-57      8L  def BasisKind.declsA : BasisKind → List ConstantInfo
                       ↳ def BasisKind.declsA : BasisKind → AM (List IConstantInfo)
```

### `ConLeche/Kernel/BasisGen.lean` — 33 decls, 197 lines (0T 0P 33S)

```
S(T)    94-96      3L  private def qBool : Bool → Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)    98-100     3L  private def qList (ty : Lean.Expr) (xs : List Lean.Expr) : Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   102-102     1L  private def nameTy : Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   103-103     1L  private def levelTy : Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   104-104     1L  private def exprTy : Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   105-105     1L  private def recRuleTy : Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   106-106     1L  private def constantInfoTy : Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   107-107     1L  private def constantValTy : Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   109-112     4L  private def qName : ConLeche.Name → Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   114-115     2L  private def qNames (ns : List ConLeche.Name) : Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   117-122     6L  private def qLevel : ConLeche.Level → Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   124-125     2L  private def qLevels (us : List ConLeche.Level) : Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   127-133     7L  private def qPropWhen (pw : ConLeche.PropWhen) : Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   135-136     2L  private def qBinderMeta (m : ConLeche.BinderMeta) : Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   138-140     3L  private def qLiteral : ConLeche.Literal → Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   142-156    15L  private def qExpr : ConLeche.Expr → Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   158-160     3L  private def qConstantVal (cv : ConLeche.ConstantVal) : Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   162-167     6L  private def qRecRuleFire : ConLeche.RecRuleFire → Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   169-173     5L  private def qRecRule (r : ConLeche.RecRule) : Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   175-179     5L  private def qIndCaps (c : ConLeche.IndCaps) : Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   181-184     4L  private def qReducibilityHint : ConLeche.ReducibilityHint → Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   186-203    18L  private def qConstantInfo : ConLeche.ConstantInfo → CoreM Lean.Expr
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   207-238    32L  def annotateInfo (env : ConLeche.Env) (ci : ConLeche.ConstantInfo) : ConLeche.CheckM ConLeche.ConstantInfo
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   240-244     5L  def annotateVal (env : ConLeche.Env) (cv : ConLeche.ConstantVal) : ConLeche.CheckM ConLeche.ConstantVal
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   252-253     2L  private unsafe def evalInfoUnsafe (stx : Syntax) : TermElabM ConLeche.ConstantInfo
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   255-257     3L  private def evalInfo (_stx : Syntax) : TermElabM ConLeche.ConstantInfo
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   259-260     2L  private unsafe def evalValUnsafe (stx : Syntax) : TermElabM ConLeche.ConstantVal
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   262-264     3L  private def evalVal (_stx : Syntax) : TermElabM ConLeche.ConstantVal
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   266-268     3L  private unsafe def evalEnvUnsafe (stx : Syntax) : TermElabM (List ConLeche.ConstantInfo)
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   270-272     3L  private def evalEnv (_stx : Syntax) : TermElabM (List ConLeche.ConstantInfo)
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   276-291    16L  private def splice (declName : Lean.Name) (ty value : Lean.Expr) : TermElabM Unit
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   311-328    18L  def elabAnnotateBasis : CommandElab
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
S(T)   330-345    16L  def elabAnnotatePins : CommandElab
                       ↳ Rust port skips it: The `#annotate_basis`/`#annotate_pins` elaborators and their `Qq` quotations — meta code that runs while con-leche elaborates; its *results* are carried as generated source (`kernel/basis_tables.rs`, task #22) and as the annotated pins in `std_axioms`/`trust_axioms`.
```

### `ConLeche/Kernel/Basis/Builder.lean` — 21 decls, 54 lines (21T 0P 0S)

```
T       41-42      2L  def bn (s : String) : Name
                       ↳ def bn (s : String) : AM NIdx
T       44-45      2L  def uN : Name
                       ↳ def uN : AM NIdx
T       47-48      2L  def u : Level
                       ↳ def u : AM LIdx
T       50-51      2L  def vN : Name
                       ↳ def vN : AM NIdx
T       53-54      2L  def v : Level
                       ↳ def v : AM LIdx
T       56-58      3L  def u1N : Name
                       ↳ def u1N : AM NIdx
T       60-61      2L  def u1 : Level
                       ↳ def u1 : AM LIdx
T       63-64      2L  def bv (i : Nat) : Expr
                       ↳ def bv (i : Nat) : AM EIdx
T       66-67      2L  def srt (u : Level) : Expr
                       ↳ def srt (u : LIdx) : AM EIdx
T       69-70      2L  def prop : Expr
                       ↳ def prop : AM EIdx
T       72-73      2L  def type1 : Expr
                       ↳ def type1 : AM EIdx
T       75-76      2L  def cnst (n : Name) (us : List Level := []) : Expr
                       ↳ def cnst (n : NIdx) (us : LsIdx := []) : AM EIdx
T       85-88      4L  def pi (_x : String) (ty body : Expr) : Expr
                       ↳ def pi (_x : String) (ty body : EIdx) : AM EIdx
T       90-93      4L  def piI (_x : String) (ty body : Expr) : Expr
                       ↳ def piI (_x : String) (ty body : EIdx) : AM EIdx
T       95-97      3L  def piA (ty body : Expr) : Expr
                       ↳ def piA (ty body : EIdx) : AM EIdx
T       99-101     3L  def lm (_x : String) (ty body : Expr) : Expr
                       ↳ def lm (_x : String) (ty body : EIdx) : AM EIdx
T      103-106     4L  def lmI (_x : String) (ty body : Expr) : Expr
                       ↳ def lmI (_x : String) (ty body : EIdx) : AM EIdx
T      108-109     2L  def ap2 (f a b : Expr) : Expr
                       ↳ def ap2 (f a b : EIdx) : AM EIdx
T      111-112     2L  def ap3 (f a b c : Expr) : Expr
                       ↳ def ap3 (f a b c : EIdx) : AM EIdx
T      114-115     2L  def ap4 (f a b c d : Expr) : Expr
                       ↳ def ap4 (f a b c d : EIdx) : AM EIdx
T      117-121     5L  def rule (ctor : Name) (nfields : Nat) (rhs : Expr) : RecRule
                       ↳ def rule (ctor : NIdx) (nfields : Nat) (rhs : EIdx) : AM IRecRule
```

### `ConLeche/Kernel/Basis/Empty.lean` — 3 decls, 13 lines (3T 0P 0S)

```
T       21-23      3L  def emptyRaw : ConstantInfo
                       ↳ def emptyRaw : AM IConstantInfo
T       25-32      8L  def emptyRecRaw : ConstantInfo
                       ↳ def emptyRecRaw : AM IConstantInfo
T       34-35      2L  def emptyBasis : List ConstantInfo
                       ↳ def emptyBasis : AM (List IConstantInfo)
```

### `ConLeche/Kernel/Basis/Eq.lean` — 5 decls, 39 lines (5T 0P 0S)

```
T       22-28      7L  def eqRaw : ConstantInfo
                       ↳ def eqRaw : AM IConstantInfo
T       30-36      7L  def eqReflRaw : ConstantInfo
                       ↳ def eqReflRaw : AM IConstantInfo
T       38-42      5L  def eqRecMotive : Expr
                       ↳ def eqRecMotive : AM EIdx
T       44-61     18L  def eqRecRaw : ConstantInfo
                       ↳ def eqRecRaw : AM IConstantInfo
T       63-64      2L  def eqBasis : List ConstantInfo
                       ↳ def eqBasis : AM (List IConstantInfo)
```

### `ConLeche/Kernel/Basis/False.lean` — 3 decls, 13 lines (3T 0P 0S)

```
T       38-40      3L  def falseRaw : ConstantInfo
                       ↳ def falseRaw : AM IConstantInfo
T       42-49      8L  def falseRecRaw : ConstantInfo
                       ↳ def falseRecRaw : AM IConstantInfo
T       51-52      2L  def falseBasis : List ConstantInfo
                       ↳ def falseBasis : AM (List IConstantInfo)
```

### `ConLeche/Kernel/Basis/Names.lean` — 26 decls, 70 lines (26T 0P 0S)

```
T       17-18      2L  def eqName : Name
                       ↳ def eqName : AM NIdx
T       20-21      2L  def eqReflName : Name
                       ↳ def eqReflName : AM NIdx
T       23-24      2L  def punitName : Name
                       ↳ def punitName : AM NIdx
T       26-29      4L  def punitRecName : Name
                       ↳ def punitRecName : AM NIdx
T       31-32      2L  def natName : Name
                       ↳ def natName : AM NIdx
T       34-35      2L  def natZeroName : Name
                       ↳ def natZeroName : AM NIdx
T       37-38      2L  def natSuccName : Name
                       ↳ def natSuccName : AM NIdx
T       40-41      2L  def punitUnitName : Name
                       ↳ def punitUnitName : AM NIdx
T       43-43      1L  def emptyName : Name
                       ↳ def emptyName : AM NIdx
T       45-49      5L  def falseName : Name
                       ↳ def falseName : AM NIdx
T       51-52      2L  def quotName : Name
                       ↳ def quotName : AM NIdx
T       54-55      2L  def quotMkName : Name
                       ↳ def quotMkName : AM NIdx
T       57-58      2L  def quotLiftName : Name
                       ↳ def quotLiftName : AM NIdx
T       60-61      2L  def quotIndName : Name
                       ↳ def quotIndName : AM NIdx
T       63-64      2L  def quotSoundName : Name
                       ↳ def quotSoundName : AM NIdx
T       73-74      2L  def stringName : Name
                       ↳ def stringName : AM NIdx
T       76-77      2L  def stringOfListName : Name
                       ↳ def stringOfListName : AM NIdx
T       79-80      2L  def listName : Name
                       ↳ def listName : AM NIdx
T       82-83      2L  def listNilName : Name
                       ↳ def listNilName : AM NIdx
T       85-86      2L  def listConsName : Name
                       ↳ def listConsName : AM NIdx
T       88-89      2L  def charName : Name
                       ↳ def charName : AM NIdx
T       91-97      7L  def andName : Name
                       ↳ def andName : AM NIdx
T       99-100     2L  def andIntroName : Name
                       ↳ def andIntroName : AM NIdx
T      102-103     2L  def charOfNatName : Name
                       ↳ def charOfNatName : AM NIdx
T      105-115    11L  def reservedBasisNames : List Name
                       ↳ def reservedBasisNames : AM (List NIdx)
T      130-131     2L  def sorryAxName : Name
                       ↳ def sorryAxName : AM NIdx
```

### `ConLeche/Kernel/Basis/Nat.lean` — 8 decls, 41 lines (8T 0P 0S)

```
T       21-22      2L  def natT : Expr
                       ↳ def natT : AM EIdx
T       24-26      3L  def natRaw : ConstantInfo
                       ↳ def natRaw : AM IConstantInfo
T       28-30      3L  def natZeroRaw : ConstantInfo
                       ↳ def natZeroRaw : AM IConstantInfo
T       32-34      3L  def natSuccRaw : ConstantInfo
                       ↳ def natSuccRaw : AM IConstantInfo
T       36-37      2L  def natRecMotive : Expr
                       ↳ def natRecMotive : AM EIdx
T       39-44      6L  def natRecSucc : Expr
                       ↳ def natRecSucc : AM EIdx
T       46-65     20L  def natRecRaw : ConstantInfo
                       ↳ def natRecRaw : AM IConstantInfo
T       67-68      2L  def natBasis : List ConstantInfo
                       ↳ def natBasis : AM (List IConstantInfo)
```

### `ConLeche/Kernel/Basis/PUnit.lean` — 5 decls, 26 lines (5T 0P 0S)

```
T       24-29      6L  def punitRaw : ConstantInfo
                       ↳ def punitRaw : AM IConstantInfo
T       31-33      3L  def punitUnitRaw : ConstantInfo
                       ↳ def punitUnitRaw : AM IConstantInfo
T       35-37      3L  def punitRecMotive : Expr
                       ↳ def punitRecMotive : AM EIdx
T       39-50     12L  def punitRecRaw : ConstantInfo
                       ↳ def punitRecRaw : AM IConstantInfo
T       52-53      2L  def punitBasis : List ConstantInfo
                       ↳ def punitBasis : AM (List IConstantInfo)
```

### `ConLeche/Kernel/Basis/Quot.lean` — 11 decls, 83 lines (11T 0P 0S)

```
T       26-28      3L  def quotRel : Expr
                       ↳ def quotRel : AM EIdx
T       30-34      5L  def quotRaw : ConstantInfo
                       ↳ def quotRaw : AM IConstantInfo
T       36-42      7L  def quotMkRaw : ConstantInfo
                       ↳ def quotMkRaw : AM IConstantInfo
T       44-45      2L  def quotLiftF : Expr
                       ↳ def quotLiftF : AM EIdx
T       47-53      7L  def quotLiftH : Expr
                       ↳ def quotLiftH : AM EIdx
T       55-72     18L  def quotLiftRaw : ConstantInfo
                       ↳ def quotLiftRaw : AM IConstantInfo
T       74-77      4L  def quotIndMotive : Expr
                       ↳ def quotIndMotive : AM EIdx
T       79-83      5L  def quotIndMk : Expr
                       ↳ def quotIndMk : AM EIdx
T       85-100    16L  def quotIndRaw : ConstantInfo
                       ↳ def quotIndRaw : AM IConstantInfo
T      102-114    13L  def quotSoundRaw : ConstantInfo
                       ↳ def quotSoundRaw : AM IConstantInfo
T      116-118     3L  def quotBasis : List ConstantInfo
                       ↳ def quotBasis : AM (List IConstantInfo)
```

### `ConLeche/Kernel/Inductives/Modeled.lean` — 23 decls, 775 lines (23T 0P 0S)

```
T       31-53     23L  def checkIotaSidesTy (ops : CheckerOps m) (envSelf : Env) (depth : Nat) (alphaS lhsS rhsS : Expr) (ℓA : Level) (cvName : Name) : m Unit
                       ↳ def checkIotaSidesTy (envSelf : IEnv) (depth : Nat) (alphaS lhsS rhsS : EIdx) (ℓA : LIdx) (cvName : NIdx) : AM Unit
T       55-149    95L  def checkIotaThm (ops : CheckerOps m) (env' envSelf : Env) (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr) (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal) (cnP cnF : Nat) (rhsA : Expr) : m Unit
                       ↳ def checkIotaThm (env' envSelf : IEnv) (f : NIdx → NIdx) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx) (mI rP j : Nat) (r : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat) (rhsA : EIdx) : AM Unit
T      151-190    40L  def nestedRuleShape (env' envSelf : Env) (cvName : Name) (lps : List Name) (tyA : Expr) (mI rP cnP j : Nat) : Option (List Level × List Expr)
                       ↳ def nestedRuleShape (env' envSelf : IEnv) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx) (mI rP cnP j : Nat) : AM (Option (LsIdx × List EIdx))
T      192-317   126L  def checkIotaThmN (ops : CheckerOps m) (env' envSelf : Env) (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr) (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal) (cnP cnF : Nat) (rhsA : Expr) : m RecRuleFire
                       ↳ def checkIotaThmN (env' envSelf : IEnv) (f : NIdx → NIdx) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx) (mI rP j : Nat) (r : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat) (rhsA : EIdx) : AM RecRuleFire
T      319-360    42L  def checkIotaRule (ops : CheckerOps m) (env' envSelf : Env) (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr) (mI rP j : Nat) (r : RecRule) : m RecRule
                       ↳ def checkIotaRule (env' envSelf : IEnv) (f : NIdx → NIdx) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx) (mI rP j : Nat) (r : IRecRule) : AM IRecRule
T      362-371    10L  def checkIotaRules (ops : CheckerOps m) (env' envSelf : Env) (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr) (mI rP : Nat) : Nat → List RecRule → m (List RecRule)
                       ↳ def checkIotaRules (env' envSelf : IEnv) (f : NIdx → NIdx) (cvName : NIdx) (lps : List NIdx) (tyA : EIdx) (mI rP : Nat) : Nat → List IRecRule → AM (List IRecRule)
T      373-401    29L  def checkMemberVal (ops : CheckerOps m) (blockNames : List Name) (env' : Env) (cv : ConstantVal) : m ConstantVal
                       ↳ def checkMemberVal (blockNames : List NIdx) (env' : IEnv) (cv : IConstantVal) : AM IConstantVal
T      403-414    12L  def checkIndMember (ops : CheckerOps m) (blockNames : List Name) (caps : IndCaps) (env' : Env) (ci : ConstantInfo) : m Env
                       ↳ def checkIndMember (blockNames : List NIdx) (caps : IIndCaps) (env' : IEnv) (ci : IConstantInfo) : AM IEnv
T      416-433    18L  def provisionRecs (ops : CheckerOps m) (blockNames : List Name) : Env → List ConstantInfo → m (Env × List (ConstantVal × Nat × Nat × List RecRule))
                       ↳ def provisionRecs (blockNames : List NIdx) : IEnv → List IConstantInfo → AM (IEnv × List (IConstantVal × Nat × Nat × List IRecRule))
T      435-455    21L  def checkIndRecs (ops : CheckerOps m) (blockNames : List Name) (env₂ : Env) (recs : List ConstantInfo) : m Env
                       ↳ def checkIndRecs (blockNames : List NIdx) (env₂ : IEnv) (recs : List IConstantInfo) : AM IEnv
T      457-464     8L  def projBack (T ctor : Name) (nF : Nat) : Name → Name
                       ↳ def projBack (T ctor : NIdx) (nF : Nat) : NIdx → AM NIdx
T      466-473     8L  def projFwd (T ctor : Name) (nF : Nat) : Name → Name
                       ↳ def projFwd (T ctor : NIdx) (nF : Nat) : NIdx → AM NIdx
T      475-495    21L  def checkProjLookups (env' : Env) (T ctorName : Name) (lps : List Name) (nP nF i : Nat) : m (ConstantVal × ConstantVal)
                       ↳ def checkProjLookups (env' : IEnv) (T ctorName : NIdx) (lps : List NIdx) (nP nF i : Nat) : AM (IConstantVal × IConstantVal)
T      497-511    15L  def checkProjTy (env' : Env) (T ctorName : Name) (lps : List Name) (mty : Expr) (nP nF : Nat) : m Expr
                       ↳ def checkProjTy (env' : IEnv) (T ctorName : NIdx) (lps : List NIdx) (mty : EIdx) (nP nF : Nat) : AM EIdx
T      513-563    51L  def checkProjIota (ops : CheckerOps m) (env' envSelf : Env) (T ctorName : Name) (lps : List Name) (cvj : ConstantVal) (nP nF i : Nat) : m Unit
                       ↳ def checkProjIota (env' envSelf : IEnv) (T ctorName : NIdx) (lps : List NIdx) (cvj : IConstantVal) (nP nF i : Nat) : AM Unit
T      565-584    20L  def checkProjFn (ops : CheckerOps m) (env' : Env) (T ctorName : Name) (lps : List Name) (nP nF i : Nat) : m Env
                       ↳ def checkProjFn (env' : IEnv) (T ctorName : NIdx) (lps : List NIdx) (nP nF i : Nat) : AM IEnv
T      586-642    57L  def checkEtaThm (env' : Env) (T ctorName : Name) (lps : List Name) (nP nF : Nat) : Bool
                       ↳ def checkEtaThm (env' : IEnv) (T ctorName : NIdx) (lps : List NIdx) (nP nF : Nat) : AM Bool
T      644-680    37L  def checkUnitThm (env' : Env) (T : Name) (lps : List Name) (nP : Nat) : Bool
                       ↳ def checkUnitThm (env' : IEnv) (T : NIdx) (lps : List NIdx) (nP : Nat) : AM Bool
T      682-710    29L  def ctorTargetsFam (ctorTy : Expr) (T : Name) (lps : List Name) (nP nF : Nat) : Bool
                       ↳ def ctorTargetsFam (ctorTy : EIdx) (T : NIdx) (lps : List NIdx) (nP nF : Nat) : AM Bool
T      712-722    11L  def installProjFnStep (ops : CheckerOps m) (T ctorName : Name) (lps : List Name) (nP nF : Nat) (e : Env) (i : Nat) : m Env
                       ↳ def installProjFnStep (T ctorName : NIdx) (lps : List NIdx) (nP nF : Nat) (e : IEnv) (i : Nat) : AM IEnv
T      724-735    12L  def indBlockCaps (env : Env) (cvT cvC : ConstantVal) (nP nF : Nat) : IndCaps
                       ↳ def indBlockCaps (env : IEnv) (cvT cvC : IConstantVal) (nP nF : Nat) : AM IIndCaps
T      744-779    36L  def ctorResidualOk (env' : Env) (T ctorName : Name) (lps : List Name) (nP nF : Nat) (eta : Bool) : Bool
                       ↳ def ctorResidualOk (env' : IEnv) (T ctorName : NIdx) (lps : List NIdx) (nP nF : Nat) (eta : Bool) : AM Bool
T      781-834    54L  def checkModeled (ops : CheckerOps m) (env : Env) (block : List ConstantInfo) : m Env
                       ↳ def checkModeled (env : IEnv) (block : List IConstantInfo) : AM IEnv
```

### `ConLeche/Kernel/Inductives/NativeInstall.lean` — 19 decls, 363 lines (16T 2P 1S)

```
T       59-98     40L  def nativeCapsAt (p : InductiveShape) (isRec : Bool) : IndCaps
                       ↳ def nativeCapsAt (p : InductiveShape) (isRec : Bool) : AM IIndCaps
P      100-103     4L  def nativeIsRec (kinds : List (List RecFieldKind)) : Bool
T      105-108     4L  def nativeCaps (p : NativeParts) : IndCaps
                       ↳ def nativeCaps (p : NativeParts) : AM IIndCaps
P      110-128    19L  def nativeRawRec (p : NativeParts) : Bool
T      139-141     3L  def Expr.mentionsFvar (q : Nat) (e : Expr) : Bool
                       ↳ def EIdx.mentionsFvar (q : Nat) (e : EIdx) : AM Bool
S(T)   194-196     3L  def MentionsFvarMemoInv (q : Nat) (memo : Std.HashMap Expr Bool) : Prop
                       ↳ Rust port skips it: A `Prop`-valued memo invariant, as `ExprOps.lean`'s.
T      214-219     6L  def Expr.mentionsFvarIns (e : Expr) (r : Bool × Std.HashMap Expr Bool) : Bool × Std.HashMap Expr Bool
                       ↳ def EIdx.mentionsFvarIns (e : EIdx) (r : Bool × Std.HashMap EIdx Bool) : AM (Bool × Std.HashMap EIdx Bool)
T      221-257    37L  def Expr.mentionsFvarGo (q : Nat) (memo : Std.HashMap Expr Bool) (e : Expr) : Bool × Std.HashMap Expr Bool
                       ↳ def EIdx.mentionsFvarGo (q : Nat) (memo : Std.HashMap EIdx Bool) (e : EIdx) : AM (Bool × Std.HashMap EIdx Bool)
T      379-381     3L  def Expr.mentionsFvarFast (q : Nat) (e : Expr) : Bool
                       ↳ def EIdx.mentionsFvarFast (q : Nat) (e : EIdx) : AM Bool
T      388-433    46L  def nativeOpenedOk (env₀ : Env) (T : Name) (lps : List Name) (nP nIdx : Nat) (cty : Expr) (nF : Nat) (ks : List RecFieldKind) : Bool
                       ↳ def nativeOpenedOk (env₀ : IEnv) (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (cty : EIdx) (nF : Nat) (ks : List RecFieldKind) : AM Bool
T      435-445    11L  def nativeFieldsOk (env₀ : Env) (T : Name) (lps : List Name) (nP nIdx : Nat) (ctorsA : List (ConstantVal × Nat)) (kinds : List (List RecFieldKind)) : Bool
                       ↳ def nativeFieldsOk (env₀ : IEnv) (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (ctorsA : List (IConstantVal × Nat)) (kinds : List (List RecFieldKind)) : AM Bool
T      447-463    17L  def checkNativeRules (envR : Env) (rlps : List Name) (T : Name) (lps : List Name) (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr) (ctors : List (Name × Nat × Expr × List Nat)) (recC : Name) (rlvls : List Level) : Nat → Nat → m (List Expr)
                       ↳ def checkNativeRules (envR : IEnv) (rlps : List NIdx) (T : NIdx) (lps : List NIdx) (elim : NIdx) (large : Bool) (nP nIdx : Nat) (tty : EIdx) (ctors : List (NIdx × Nat × EIdx × List Nat)) (recC : NIdx) (rlvls : LsIdx) : Nat → Nat → AM (List EIdx)
T      465-502    38L  def checkNativeRec (ops : CheckerOps m) (env : Env) (p : NativeParts) (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) : m (ConstantVal × List Expr)
                       ↳ def checkNativeRec (env : IEnv) (p : NativeParts) (cvTa : IConstantVal) (ctorsA : List (IConstantVal × Nat)) : AM (IConstantVal × List EIdx)
T      504-519    16L  def checkNativeTable (p : NativeParts) (ctorsA : List (ConstantVal × Nat)) (sortss : List (List Level)) (env : Env) : m Env
                       ↳ def checkNativeTable (p : NativeParts) (ctorsA : List (IConstantVal × Nat)) (sortss : List (LsIdx)) (env : IEnv) : AM IEnv
T      521-537    17L  structure NativePass (E : Type) where
                       ↳ structure NativePass (E : Type) where
T      539-554    16L  def classifyFixKinds (T : Name) (lps : List Name) (nP nIdx : Nat) (ctorsA : List (ConstantVal × Nat)) : m (List (List RecFieldKind))
                       ↳ def classifyFixKinds (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (ctorsA : List (IConstantVal × Nat)) : AM (List (List RecFieldKind))
T      556-574    19L  def checkNativePass (ops : CheckerOps m) (env : Env) (p₀ : NativeParts) (isRec : Bool) : m (NativePass Env × Bool)
                       ↳ def checkNativePass (env : IEnv) (p₀ : NativeParts) (isRec : Bool) : AM (NativePass IEnv × Bool)
T      576-611    36L  def checkNativeTail (ops : CheckerOps m) (env : Env) (q : NativePass Env) : m Env
                       ↳ def checkNativeTail (env : IEnv) (q : NativePass IEnv) : AM IEnv
T      613-640    28L  def checkNative (ops : CheckerOps m) (env : Env) (p₀ : NativeParts) : m Env
                       ↳ def checkNative (env : IEnv) (p₀ : NativeParts) : AM IEnv
```

### `ConLeche/Kernel/Inductives/NativeInstallF.lean` — 5 decls, 101 lines (5T 0P 0S)

```
T       22-59     38L  def nativeOpenedOkF (w : StructWalkers) (fe₀ : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat) (cty : Expr) (nF : Nat) (ks : List RecFieldKind) : Bool
                       ↳ def nativeOpenedOkF (w : StructWalkers) (fe₀ : IFEnv) (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (cty : EIdx) (nF : Nat) (ks : List RecFieldKind) : AM Bool
T       61-69      9L  def nativeFieldsOkF (w : StructWalkers) (fe₀ : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat) (ctorsA : List (ConstantVal × Nat)) (kinds : List (List RecFieldKind)) : Bool
                       ↳ def nativeFieldsOkF (w : StructWalkers) (fe₀ : IFEnv) (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (ctorsA : List (IConstantVal × Nat)) (kinds : List (List RecFieldKind)) : AM Bool
T       71-85     15L  def checkNativeRulesF (w : StructWalkers) (feR : FEnv) (rlps : List Name) (T : Name) (lps : List Name) (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr) (ctors : List (Name × Nat × Expr × List Nat)) (recC : Name) (rlvls : List Level) : Nat → Nat → m (List Expr)
                       ↳ def checkNativeRulesF (w : StructWalkers) (feR : IFEnv) (rlps : List NIdx) (T : NIdx) (lps : List NIdx) (elim : NIdx) (large : Bool) (nP nIdx : Nat) (tty : EIdx) (ctors : List (NIdx × Nat × EIdx × List Nat)) (recC : NIdx) (rlvls : LsIdx) : Nat → Nat → AM (List EIdx)
T       87-115    29L  def checkNativeRecF (ops : CheckerOps m) (w : StructWalkers) (fe : FEnv) (p : NativeParts) (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) : m (ConstantVal × List Expr)
                       ↳ def checkNativeRecF (w : StructWalkers) (fe : IFEnv) (p : NativeParts) (cvTa : IConstantVal) (ctorsA : List (IConstantVal × Nat)) : AM (IConstantVal × List EIdx)
T      117-126    10L  def checkNativeTableF (w : StructWalkers) (p : NativeParts) (ctorsA : List (ConstantVal × Nat)) (sortss : List (List Level)) (fe : FEnv) : m FEnv
                       ↳ def checkNativeTableF (w : StructWalkers) (p : NativeParts) (ctorsA : List (IConstantVal × Nat)) (sortss : List (LsIdx)) (fe : IFEnv) : AM IFEnv
```

### `ConLeche/Kernel/Inductives/NativeParts.lean` — 34 decls, 501 lines (28T 6P 0S)

```
P       60-76     17L  inductive RecFieldKind
T       78-87     10L  def recFamOk (T : Name) (lps : List Name) (nP nIdx o : Nat) (e : Expr) : Bool
                       ↳ def recFamOk (T : NIdx) (lps : List NIdx) (nP nIdx o : Nat) (e : EIdx) : AM Bool
T       89-111    23L  def recPositivity (T : Name) (lps : List Name) (nP nIdx o : Nat) : Expr → Nat → RecFieldKind
                       ↳ def recPositivity (T : NIdx) (lps : List NIdx) (nP nIdx o : Nat) : EIdx → Nat → AM RecFieldKind
T      113-116     4L  def recFieldKind (T : Name) (lps : List Name) (nP nIdx o : Nat) (dom : Expr) : RecFieldKind
                       ↳ def recFieldKind (T : NIdx) (lps : List NIdx) (nP nIdx o : Nat) (dom : EIdx) : AM RecFieldKind
T      118-145    28L  def recCtorKinds (T : Name) (lps : List Name) (nP nIdx : Nat) (c : ConstantVal × Nat) : Option (List RecFieldKind)
                       ↳ def recCtorKinds (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (c : IConstantVal × Nat) : AM (Option (List RecFieldKind))
T      147-154     8L  def Expr.piBinders : Expr → List (Expr × BinderMeta) × Expr
                       ↳ def EIdx.piBinders : EIdx → AM (List (EIdx × BinderMeta) × EIdx)
T      156-161     6L  def structFieldTeleOf (cty : Expr) (nP nF i : Nat) : List (Expr × BinderMeta)
                       ↳ def structFieldTeleOf (cty : EIdx) (nP nF i : Nat) : AM (List (EIdx × BinderMeta))
T      163-169     7L  def structFieldIdxOf (cty : Expr) (nP nF i : Nat) : List Expr
                       ↳ def structFieldIdxOf (cty : EIdx) (nP nF i : Nat) : AM (List EIdx)
P      171-175     5L  def recIdxOf (ks : List RecFieldKind) : List Nat
P      177-192    16L  structure NativeParts extends InductiveShape where
P      194-199     6L  def NativeParts.complete (p₀ : NativeParts) (p₁ : InductiveShape) : NativeParts
T      230-235     6L  def structRecPrefixAt (nP n nF e : Nat) : List Expr
                       ↳ def structRecPrefixAt (nP n nF e : Nat) : AM (List EIdx)
T      237-244     8L  def structIdxAt (nF o i l m : Nat) (e : Expr) : Expr
                       ↳ def structIdxAt (nF o i l m : Nat) (e : EIdx) : AM EIdx
T      246-252     7L  def structTeleAt (nF o i l : Nat) (pw : PropWhen) (tele : List (Expr × BinderMeta)) : List (Expr × BinderMeta)
                       ↳ def structTeleAt (nF o i l : Nat) (pw : PropWhen) (tele : List (EIdx × BinderMeta)) : AM (List (EIdx × BinderMeta))
T      254-255     2L  def structTeleVars (m : Nat) : List Expr
                       ↳ def structTeleVars (m : Nat) : AM (List EIdx)
T      257-260     4L  def Expr.mkPisOf : List (Expr × BinderMeta) → Expr → Expr
                       ↳ def EIdx.mkPisOf : List (EIdx × BinderMeta) → EIdx → AM EIdx
T      261-263     3L  def Expr.mkLamsOf : List (Expr × BinderMeta) → Expr → Expr
                       ↳ def EIdx.mkLamsOf : List (EIdx × BinderMeta) → EIdx → AM EIdx
T      265-277    13L  def structIhApp (recC : Name) (rlvls : List Level) (pw : PropWhen) (nP n nF i : Nat) (tele : List (Expr × BinderMeta)) (idx : List Expr) : Expr
                       ↳ def structIhApp (recC : NIdx) (rlvls : LsIdx) (pw : PropWhen) (nP n nF i : Nat) (tele : List (EIdx × BinderMeta)) (idx : List EIdx) : AM EIdx
T      279-288    10L  def structRuleBodyR (recC : Name) (rlvls : List Level) (pw : PropWhen) (nP n nF j : Nat) (recIdx : List Nat) (teleOf : Nat → List (Expr × BinderMeta)) (idxOf : Nat → List Expr) : Expr
                       ↳ def structRuleBodyR (recC : NIdx) (rlvls : LsIdx) (pw : PropWhen) (nP n nF j : Nat) (recIdx : List Nat) (teleOf : Nat → List (EIdx × BinderMeta)) (idxOf : Nat → List EIdx) : AM EIdx
T      290-305    16L  def structIhPis (nF o : Nat) (pw : PropWhen) (teleOf : Nat → List (Expr × BinderMeta)) (idxOf : Nat → List Expr) : List Nat → Nat → Expr → Expr
                       ↳ def structIhPis (nF o : Nat) (pw : PropWhen) (teleOf : Nat → List (EIdx × BinderMeta)) (idxOf : Nat → List EIdx) : List Nat → Nat → EIdx → AM EIdx
T      307-320    14L  def structMinorTyR (C : Name) (lps : List Name) (nP nF o : Nat) (pw : PropWhen) (cty : Expr) (recIdx : List Nat) : Option Expr
                       ↳ def structMinorTyR (C : NIdx) (lps : List NIdx) (nP nF o : Nat) (pw : PropWhen) (cty : EIdx) (recIdx : List Nat) : AM (Option EIdx)
T      322-330     9L  def structMinorsPisR (lps : List Name) (nP : Nat) (pw : PropWhen) : List (Name × Nat × Expr × List Nat) → Nat → Expr → Option Expr
                       ↳ def structMinorsPisR (lps : List NIdx) (nP : Nat) (pw : PropWhen) : List (NIdx × Nat × EIdx × List Nat) → Nat → EIdx → AM (Option EIdx)
T      332-339     8L  def structMinorsLamsR (lps : List Name) (nP : Nat) (pw : PropWhen) : List (Name × Nat × Expr × List Nat) → Nat → Expr → Option Expr
                       ↳ def structMinorsLamsR (lps : List NIdx) (nP : Nat) (pw : PropWhen) : List (NIdx × Nat × EIdx × List Nat) → Nat → EIdx → AM (Option EIdx)
T      341-362    22L  def structRecTyR (T : Name) (lps : List Name) (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr) (ctors : List (Name × Nat × Expr × List Nat)) : Option Expr
                       ↳ def structRecTyR (T : NIdx) (lps : List NIdx) (elim : NIdx) (large : Bool) (nP nIdx : Nat) (tty : EIdx) (ctors : List (NIdx × Nat × EIdx × List Nat)) : AM (Option EIdx)
T      364-386    23L  def structRecRhsR (T : Name) (lps : List Name) (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr) (ctors : List (Name × Nat × Expr × List Nat)) (recC : Name) (rlvls : List Level) (j : Nat) : Option Expr
                       ↳ def structRecRhsR (T : NIdx) (lps : List NIdx) (elim : NIdx) (large : Bool) (nP nIdx : Nat) (tty : EIdx) (ctors : List (NIdx × Nat × EIdx × List Nat)) (recC : NIdx) (rlvls : LsIdx) (j : Nat) : AM (Option EIdx)
T      388-392     5L  def nativeCtors4 (ctorsA : List (ConstantVal × Nat)) (kinds : List (List RecFieldKind)) : List (Name × Nat × Expr × List Nat)
                       ↳ def nativeCtors4 (ctorsA : List (IConstantVal × Nat)) (kinds : List (List RecFieldKind)) : AM (List (NIdx × Nat × EIdx × List Nat))
T      394-445    52L  def nativeRulePrefixOk (recTy : Expr) (nP n j nF : Nat) (rhs : Expr) : Bool
                       ↳ def nativeRulePrefixOk (recTy : EIdx) (nP n j nF : Nat) (rhs : EIdx) : AM Bool
T      447-475    29L  def nativeRulesOk (recC : Name) (rlvls : List Level) (pw : PropWhen) (nP n : Nat) (cs : List (ConstantVal × Nat)) (kinds : List (List RecFieldKind)) (rhss : List Expr) (recTy : Expr) : Bool
                       ↳ def nativeRulesOk (recC : NIdx) (rlvls : LsIdx) (pw : PropWhen) (nP n : Nat) (cs : List (IConstantVal × Nat)) (kinds : List (List RecFieldKind)) (rhss : List EIdx) (recTy : EIdx) : AM Bool
T      501-523    23L  def nativeCounts? (nPd : Nat) (cvT : ConstantVal) (cs : List (ConstantVal × Nat × Nat)) (mI rP : Nat) : Option (Nat × Nat)
                       ↳ def nativeCounts? (nPd : Nat) (cvT : IConstantVal) (cs : List (IConstantVal × Nat × Nat)) (mI rP : Nat) : AM (Option (Nat × Nat))
T      525-549    25L  def nativeRecPinOk (p : InductiveShape) (block : List ConstantInfo) : Bool
                       ↳ def nativeRecPinOk (p : InductiveShape) (block : List IConstantInfo) : AM Bool
P      551-560    10L  def nativeRecLpsOk (p : InductiveShape) : Bool
T      562-614    53L  def nativeShape? (nPd : Nat) (block : List ConstantInfo) : Option InductiveShape
                       ↳ def nativeShape? (nPd : Nat) (block : List IConstantInfo) : AM (Option InductiveShape)
P      616-622     7L  def NativeParts.withKinds (p : NativeParts) (ks : List (List RecFieldKind)) : NativeParts
T      631-652    22L  def nativeParts? (nPd : Nat) (block : List ConstantInfo) : Option NativeParts
                       ↳ def nativeParts? (nPd : Nat) (block : List IConstantInfo) : AM (Option NativeParts)
```

### `ConLeche/Kernel/Inductives/StructInstall.lean` — 2 decls, 54 lines (2T 0P 0S)

```
T       32-51     20L  def checkStructDomsAt (ops : CheckerOps m) (env : Env) (off : Nat) (fvs doms : List Expr) : Nat → m Unit
                       ↳ def checkStructDomsAt (env : IEnv) (off : Nat) (fvs doms : List EIdx) : Nat → AM Unit
T       53-86     34L  def checkStructProjTable (T C : Name) (lps : List Name) (nP nF : Nat) (resSort : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal) (env : Env) : m Env
                       ↳ def checkStructProjTable (T C : NIdx) (lps : List NIdx) (nP nF : Nat) (resSort : LIdx) (guards : LsIdx) (off : Nat) (cvCa : IConstantVal) (env : IEnv) : AM IEnv
```

### `ConLeche/Kernel/Inductives/StructInstallF.lean` — 5 decls, 65 lines (4T 1P 0S)

```
T       27-36     10L  def checkStructDomsAtF (ops : CheckerOps m) (fe : FEnv) (off : Nat) (fvs doms : List Expr) : Nat → m Unit
                       ↳ def checkStructDomsAtF (fe : IFEnv) (off : Nat) (fvs doms : List EIdx) : Nat → AM Unit
T       38-48     11L  def checkStructDomsAtFA (ops : CheckerOps m) (fe : FEnv) (off : Nat) (fvs doms : Array Expr) : Nat → m Unit
                       ↳ def checkStructDomsAtFA (fe : IFEnv) (off : Nat) (fvs doms : Array EIdx) : Nat → AM Unit
T       50-67     18L  structure StructWalkers where
                       ↳ structure StructWalkers where
P       69-71      3L  def StructWalkers.plain : StructWalkers
T       73-95     23L  def checkStructProjTableF (w : StructWalkers) (T C : Name) (lps : List Name) (nP nF : Nat) (resSort : Level) (guards : List Level) (off : Nat) (cvCa : ConstantVal) (fe : FEnv) : m FEnv
                       ↳ def checkStructProjTableF (w : StructWalkers) (T C : NIdx) (lps : List NIdx) (nP nF : Nat) (resSort : LIdx) (guards : LsIdx) (off : Nat) (cvCa : IConstantVal) (fe : IFEnv) : AM IFEnv
```

### `ConLeche/Kernel/Inductives/StructParts.lean` — 34 decls, 410 lines (32T 0P 2S)

```
T       82-86      5L  def structFam (T : Name) (lps : List Name) (nP o : Nat) : Expr
                       ↳ def structFam (T : NIdx) (lps : List NIdx) (nP o : Nat) : AM EIdx
T       88-94      7L  def structCtorSpine (C : Name) (lps : List Name) (nP nF : Nat) : Expr
                       ↳ def structCtorSpine (C : NIdx) (lps : List NIdx) (nP nF : Nat) : AM EIdx
T       96-99      4L  def structRuleBody (nF : Nat) : Expr
                       ↳ def structRuleBody (nF : Nat) : AM EIdx
T      134-137     4L  def structPsAt (o nP : Nat) : List Expr
                       ↳ def structPsAt (o nP : Nat) : AM (List EIdx)
T      139-142     4L  def structElimLevel (elim : Name) (large : Bool) : Level
                       ↳ def structElimLevel (elim : NIdx) (large : Bool) : AM LIdx
T      144-150     7L  def structCtorSpineAt (C : Name) (lps : List Name) (o nP nF : Nat) : Expr
                       ↳ def structCtorSpineAt (C : NIdx) (lps : List NIdx) (o nP nF : Nat) : AM EIdx
T      152-158     7L  def Expr.replacePisPw (pw : PropWhen) : Nat → Expr → Expr → Option Expr
                       ↳ def EIdx.replacePisPw (pw : PropWhen) : Nat → EIdx → EIdx → AM (Option EIdx)
T      160-167     8L  def Expr.pisToLamsPw (pw : PropWhen) : Nat → Expr → Expr → Option Expr
                       ↳ def EIdx.pisToLamsPw (pw : PropWhen) : Nat → EIdx → EIdx → AM (Option EIdx)
T      189-194     6L  def structFamI (T : Name) (lps : List Name) (nP nIdx e o : Nat) : Expr
                       ↳ def structFamI (T : NIdx) (lps : List NIdx) (nP nIdx e o : Nat) : AM EIdx
T      196-202     7L  def structCtorResidOk (T : Name) (lps : List Name) (nP o nIdx : Nat) (cbody : Expr) : Bool
                       ↳ def structCtorResidOk (T : NIdx) (lps : List NIdx) (nP o nIdx : Nat) (cbody : EIdx) : AM Bool
T      204-211     8L  def structMotiveTyI (T : Name) (lps : List Name) (nP nIdx : Nat) (ℓ : Level) (itele : Expr) : Option Expr
                       ↳ def structMotiveTyI (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (ℓ : LIdx) (itele : EIdx) : AM (Option EIdx)
T      213-244    32L  structure StructParts where
                       ↳ structure StructParts where
T      246-281    36L  def structShape (T C : Name) (lps : List Name) (elim : Name) (large : Bool) (nP nF : Nat) (tty cty rty : Expr) : Bool
                       ↳ def structShape (T C : NIdx) (lps : List NIdx) (elim : NIdx) (large : Bool) (nP nF : Nat) (tty cty rty : EIdx) : AM Bool
T      283-329    47L  def structPartsCore? (block : List ConstantInfo) : Option StructParts
                       ↳ def structPartsCore? (block : List IConstantInfo) : AM (Option StructParts)
T      331-337     7L  def structProjPs (nP : Nat) : List Expr
                       ↳ def structProjPs (nP : Nat) : AM (List EIdx)
T      339-345     7L  def structProjArgP (T : Name) (j : Nat) : Expr
                       ↳ def structProjArgP (T : NIdx) (j : Nat) : AM EIdx
T      347-354     8L  def structProjResidP (T : Name) (nP : Nat) (cty : Expr) : Nat → Option Expr
                       ↳ def structProjResidP (T : NIdx) (nP : Nat) (cty : EIdx) : Nat → AM (Option EIdx)
T      356-369    14L  def Expr.hasLooseBVar : Nat → Expr → Bool
                       ↳ def EIdx.hasLooseBVar : Nat → EIdx → AM Bool
T      371-390    20L  def Expr.hasLooseBVarB (i : Nat) (e : Expr) : Bool
                       ↳ def EIdx.hasLooseBVarB (i : Nat) (e : EIdx) : AM Bool
S(T)   415-417     3L  def LooseBVarMemoInv (memo : Std.HashMap (Expr × Nat) Bool) : Prop
                       ↳ Rust port skips it: A `Prop`-valued memo invariant, as `ExprOps.lean`'s.
T      435-440     6L  def Expr.hasLooseBVarBIns (e : Expr) (i : Nat) (r : Bool × Std.HashMap (Expr × Nat) Bool) : Bool × Std.HashMap (Expr × Nat) Bool
                       ↳ def EIdx.hasLooseBVarBIns (e : EIdx) (i : Nat) (r : Bool × Std.HashMap (EIdx × Nat) Bool) : AM (Bool × Std.HashMap (EIdx × Nat) Bool)
T      442-478    37L  def Expr.hasLooseBVarBGo (memo : Std.HashMap (Expr × Nat) Bool) (i : Nat) (e : Expr) : Bool × Std.HashMap (Expr × Nat) Bool
                       ↳ def EIdx.hasLooseBVarBGo (memo : Std.HashMap (EIdx × Nat) Bool) (i : Nat) (e : EIdx) : AM (Bool × Std.HashMap (EIdx × Nat) Bool)
T      624-626     3L  def Expr.hasLooseBVarBFast (i : Nat) (e : Expr) : Bool
                       ↳ def EIdx.hasLooseBVarBFast (i : Nat) (e : EIdx) : AM Bool
T      633-641     9L  def structUsedLater (cty : Expr) (nP j : Nat) : Bool
                       ↳ def structUsedLater (cty : EIdx) (nP j : Nat) : AM Bool
T      643-656    14L  def structProjGuards (cty : Expr) (nP nF : Nat) (sorts : List Level) : List Level
                       ↳ def structProjGuards (cty : EIdx) (nP nF : Nat) (sorts : LsIdx) : AM LsIdx
T      669-674     6L  def structUsedLaterGo (memo : Std.HashMap (Expr × Nat) Bool) (cty : Expr) (nP j : Nat) : Bool × Std.HashMap (Expr × Nat) Bool
                       ↳ def structUsedLaterGo (memo : Std.HashMap (EIdx × Nat) Bool) (cty : EIdx) (nP j : Nat) : AM (Bool × Std.HashMap (EIdx × Nat) Bool)
T      685-692     8L  def structUsedLaterList (cty : Expr) (nP : Nat) : Std.HashMap (Expr × Nat) Bool → Nat → Nat → List Bool
                       ↳ def structUsedLaterList (cty : EIdx) (nP : Nat) : Std.HashMap (EIdx × Nat) Bool → Nat → Nat → AM (List Bool)
T      722-732    11L  def structProjGuardsFast (cty : Expr) (nP nF : Nat) (sorts : List Level) : List Level
                       ↳ def structProjGuardsFast (cty : EIdx) (nP nF : Nat) (sorts : LsIdx) : AM LsIdx
T      748-766    19L  def structProjBodiesGo (T : Name) : Nat → Nat → Expr → Option (List Expr)
                       ↳ def structProjBodiesGo (T : NIdx) : Nat → Nat → EIdx → AM (Option (List EIdx))
T      768-771     4L  def structProjBodies (T : Name) (nP nF : Nat) (cty : Expr) : Option (Array Expr)
                       ↳ def structProjBodies (T : NIdx) (nP nF : Nat) (cty : EIdx) : AM (Option (Array EIdx))
T      773-782    10L  def Expr.mentionsConst (T : Name) : Expr → Bool
                       ↳ def EIdx.mentionsConst (T : NIdx) : EIdx → AM Bool
S(T)   795-797     3L  def MentionsMemoInv (T : Name) (memo : Std.HashMap Expr Bool) : Prop
                       ↳ Rust port skips it: A `Prop`-valued memo invariant, as `ExprOps.lean`'s.
T      814-849    36L  def Expr.mentionsConstGo (T : Name) (memo : Std.HashMap Expr Bool) : Expr → Bool × Std.HashMap Expr Bool
                       ↳ def EIdx.mentionsConstGo (T : NIdx) (memo : Std.HashMap EIdx Bool) : EIdx → AM (Bool × Std.HashMap EIdx Bool)
T      922-924     3L  def Expr.mentionsConstFast (T : Name) (e : Expr) : Bool
                       ↳ def EIdx.mentionsConstFast (T : NIdx) (e : EIdx) : AM Bool
```

### `ConLeche/Kernel/Inductives/SumInstall.lean` — 14 decls, 239 lines (12T 2P 0S)

```
T       45-68     24L  def whnfTelescope (ops : CheckerOps m) (env : Env) : Nat → Nat → Expr → m (List (Expr × BinderMeta) × Level)
                       ↳ def whnfTelescope (env : IEnv) : Nat → Nat → EIdx → AM (List (EIdx × BinderMeta) × LIdx)
T       70-78      9L  def closeTelescope : List (Expr × BinderMeta) → Nat → Expr → Expr
                       ↳ def closeTelescope : List (EIdx × BinderMeta) → Nat → EIdx → AM EIdx
T       80-94     15L  def checkSumTele (ops : CheckerOps m) (env : Env) (cv : ConstantVal) (n : Nat) (cvTa₀ : ConstantVal) : m (ConstantVal × Level)
                       ↳ def checkSumTele (env : IEnv) (cv : IConstantVal) (n : Nat) (cvTa₀ : IConstantVal) : AM (IConstantVal × LIdx)
T       96-112    17L  def checkSumInd (ops : CheckerOps m) (env : Env) (p : InductiveShape) (capsOf : InductiveShape → IndCaps) : m (Env × ConstantVal × InductiveShape)
                       ↳ def checkSumInd (env : IEnv) (p : InductiveShape) (capsOf : InductiveShape → IIndCaps) : AM (IEnv × IConstantVal × InductiveShape)
T      114-139    26L  def checkStructFieldSortsI (ops : CheckerOps m) (env : Env) (isProp large : Bool) (s : Level) (nP : Nat) (fvs idxArgs : List Expr) : Nat → m (List Level)
                       ↳ def checkStructFieldSortsI (env : IEnv) (isProp large : Bool) (s : LIdx) (nP : Nat) (fvs idxArgs : List EIdx) : Nat → AM (LsIdx)
T      141-175    35L  def normPosDom (ops : CheckerOps m) (env : Env) (T : Name) : Nat → Nat → Expr → m Expr
                       ↳ def normPosDom (env : IEnv) (T : NIdx) : Nat → Nat → EIdx → AM EIdx
T      177-188    12L  def normFieldDoms (ops : CheckerOps m) (env : Env) (T : Name) : Nat → Nat → Expr → m (List (Expr × BinderMeta) × Expr)
                       ↳ def normFieldDoms (env : IEnv) (T : NIdx) : Nat → Nat → EIdx → AM (List (EIdx × BinderMeta) × EIdx)
T      190-205    16L  def normCtorVal (ops : CheckerOps m) (env : Env) (T : Name) (nP nF : Nat) (cvC cvCa : ConstantVal) : m ConstantVal
                       ↳ def normCtorVal (env : IEnv) (T : NIdx) (nP nF : Nat) (cvC cvCa : IConstantVal) : AM IConstantVal
T      207-253    47L  def checkSumCtor (ops : CheckerOps m) (env₀ env : Env) (T : Name) (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool) (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) : m (ConstantVal × List Level)
                       ↳ def checkSumCtor (env₀ env : IEnv) (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (isProp large : Bool) (cvC : IConstantVal) (nF : Nat) (cvTa : IConstantVal) : AM (IConstantVal × LsIdx)
T      255-267    13L  def checkSumCtors (ops : CheckerOps m) (env₀ env : Env) (T : Name) (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool) (cvTa : ConstantVal) : List (ConstantVal × Nat) → m (List (ConstantVal × Nat) × List (List Level))
                       ↳ def checkSumCtors (env₀ env : IEnv) (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (isProp large : Bool) (cvTa : IConstantVal) : List (IConstantVal × Nat) → AM (List (IConstantVal × Nat) × List (LsIdx))
T      269-272     4L  def consSumCtors (nP : Nat) : List (ConstantVal × Nat) → Env → Env
                       ↳ def consSumCtors (nP : Nat) : List (IConstantVal × Nat) → IEnv → AM IEnv
T      274-290    17L  def sumRules (find? : Name → Option ConstantInfo) (recName : Name) (nP mI rP : Nat) (recTy : Expr) : List (ConstantVal × Nat) → List Expr → List RecRule
                       ↳ def sumRules (find? : NIdx → Option IConstantInfo) (recName : NIdx) (nP mI rP : Nat) (recTy : EIdx) : List (IConstantVal × Nat) → List EIdx → AM (List IRecRule)
P      292-294     3L  def InductiveShape.rulePrefix (p : InductiveShape) : Nat
P      295-295     1L  def InductiveShape.majorIdx (p : InductiveShape) : Nat
```

### `ConLeche/Kernel/Inductives/SumInstallF.lean` — 8 decls, 119 lines (8T 0P 0S)

```
T       20-30     11L  def checkSumTeleF (ops : CheckerOps m) (fe : FEnv) (cv : ConstantVal) (n : Nat) (cvTa₀ : ConstantVal) : m (ConstantVal × Level)
                       ↳ def checkSumTeleF (fe : IFEnv) (cv : IConstantVal) (n : Nat) (cvTa₀ : IConstantVal) : AM (IConstantVal × LIdx)
T       32-43     12L  def checkSumIndF (ops : CheckerOps m) (fe : FEnv) (p : InductiveShape) (capsOf : InductiveShape → IndCaps) : m (FEnv × ConstantVal × InductiveShape)
                       ↳ def checkSumIndF (fe : IFEnv) (p : InductiveShape) (capsOf : InductiveShape → IIndCaps) : AM (IFEnv × IConstantVal × InductiveShape)
T       45-61     17L  def checkStructFieldSortsIF (ops : CheckerOps m) (fe : FEnv) (isProp large : Bool) (s : Level) (nP : Nat) (fvs idxArgs : List Expr) : Nat → m (List Level)
                       ↳ def checkStructFieldSortsIF (fe : IFEnv) (isProp large : Bool) (s : LIdx) (nP : Nat) (fvs idxArgs : List EIdx) : Nat → AM (LsIdx)
T       63-81     19L  def checkStructFieldSortsIFA (ops : CheckerOps m) (fe : FEnv) (isProp large : Bool) (s : Level) (nP : Nat) (fvs : Array Expr) (idxArgs : List Expr) : Nat → m (List Level)
                       ↳ def checkStructFieldSortsIFA (fe : IFEnv) (isProp large : Bool) (s : LIdx) (nP : Nat) (fvs : Array EIdx) (idxArgs : List EIdx) : Nat → AM (LsIdx)
T       83-95     13L  def normCtorValF (ops : CheckerOps m) (fe : FEnv) (T : Name) (nP nF : Nat) (cvC cvCa : ConstantVal) : m ConstantVal
                       ↳ def normCtorValF (fe : IFEnv) (T : NIdx) (nP nF : Nat) (cvC cvCa : IConstantVal) : AM IConstantVal
T       97-128    32L  def checkSumCtorF (ops : CheckerOps m) (fe₀ fe : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool) (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) : m (ConstantVal × List Level)
                       ↳ def checkSumCtorF (fe₀ fe : IFEnv) (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (isProp large : Bool) (cvC : IConstantVal) (nF : Nat) (cvTa : IConstantVal) : AM (IConstantVal × LsIdx)
T      130-140    11L  def checkSumCtorsF (ops : CheckerOps m) (fe₀ fe : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool) (cvTa : ConstantVal) : List (ConstantVal × Nat) → m (List (ConstantVal × Nat) × List (List Level))
                       ↳ def checkSumCtorsF (fe₀ fe : IFEnv) (T : NIdx) (lps : List NIdx) (nP nIdx : Nat) (resSort : LIdx) (isProp large : Bool) (cvTa : IConstantVal) : List (IConstantVal × Nat) → AM (List (IConstantVal × Nat) × List (LsIdx))
T      142-145     4L  def consSumCtorsF (nP : Nat) : List (ConstantVal × Nat) → FEnv → FEnv
                       ↳ def consSumCtorsF (nP : Nat) : List (IConstantVal × Nat) → IFEnv → AM IFEnv
```

### `ConLeche/Kernel/Inductives/SumParts.lean` — 3 decls, 40 lines (3T 0P 0S)

```
T       78-101    24L  structure InductiveShape where
                       ↳ structure InductiveShape where
T      103-110     8L  def sumSplit : List ConstantInfo → Option (List (ConstantVal × Nat × Nat) × ConstantVal × Nat × Nat × List RecRule)
                       ↳ def sumSplit : List IConstantInfo → AM (Option (List (IConstantVal × Nat × Nat) × IConstantVal × Nat × Nat × List IRecRule))
T      112-119     8L  def InductiveShape.withSort (p : InductiveShape) (s : Level) : InductiveShape
                       ↳ def InductiveShape.withSort (p : InductiveShape) (s : LIdx) : AM InductiveShape
```

## P2e — the parser into the store

`ExportC` over the store (`Scan` unchanged), the record assembly, the preparation, the projection rewrite, the ground hoist and the built-in prelude.

**82 declarations, 1265 con-leche lines: 53 (T), 27 (P), 2 (S).**

### `ConLeche/Frontend/Export.lean` — 3 decls, 15 lines (0T 3P 0S)

```
P       71-79      9L  inductive RecordVerdict
P       81-85      5L  def RecordVerdict.toError : RecordVerdict → CheckError
P      117-117     1L  abbrev M
```

### `ConLeche/Frontend/ExportC.lean` — 45 decls, 803 lines (23T 22P 0S)

```
T       78-134    57L  structure StateD where
                       ↳ structure StateD where
T      135-153    19L  def noteDecl (st : StateD) (d : Declaration) : StateD
                       ↳ def noteDecl (st : StateD) (d : IDeclaration) : AM StateD
T      155-162     8L  def pushDecl (st : StateD) (d : Declaration) : StateD
                       ↳ def pushDecl (st : StateD) (d : IDeclaration) : AM StateD
T      164-167     4L  def StateD.name (st : StateD) (i : Nat) : M Name
                       ↳ def StateD.name (st : StateD) (i : Nat) : AM (M NIdx)
T      169-172     4L  def StateD.level (st : StateD) (i : Nat) : M Level
                       ↳ def StateD.level (st : StateD) (i : Nat) : AM (M LIdx)
T      174-177     4L  def StateD.expr (st : StateD) (i : Nat) : M Expr
                       ↳ def StateD.expr (st : StateD) (i : Nat) : AM (M EIdx)
T      179-189    11L  def getDeclD (st : StateD) (i : Nat) : M Expr
                       ↳ def getDeclD (st : StateD) (i : Nat) : AM (M EIdx)
P      191-194     4L  def parsePwD (st : StateD) : PwRec → M PropWhen
P      207-209     3L  def reboundError (what : String) (i : Nat) : String
P      211-220    10L  def StateD.freshName (st : @& StateD) (i : Nat) : M Unit
P      221-222     2L  def StateD.freshLevel (st : @& StateD) (i : Nat) : M Unit
P      223-224     2L  def StateD.freshExpr (st : @& StateD) (i : Nat) : M Unit
T      228-237    10L  def parseNameEntryD (st : StateD) (i : Nat) : NameRec → M StateD
                       ↳ def parseNameEntryD (st : StateD) (i : Nat) : NameRec → AM (M StateD)
T      239-247     9L  def parseLevelEntryD (st : StateD) (i : Nat) (r : LevelRec) : M StateD
                       ↳ def parseLevelEntryD (st : StateD) (i : Nat) (r : LevelRec) : AM (M StateD)
T      249-279    31L  def parseExprEntryD (st : StateD) (i : Nat) (r : ExprRec) : M StateD
                       ↳ def parseExprEntryD (st : StateD) (i : Nat) (r : ExprRec) : AM (M StateD)
T      283-289     7L  def parseCVD (st : StateD) (cv : CVRec) : M ConstantVal
                       ↳ def parseCVD (st : StateD) (cv : CVRec) : AM (M IConstantVal)
T      291-302    12L  def projRewriteD (st : StateD) (cv : ConstantVal) (vl : Expr) : Option Expr
                       ↳ def projRewriteD (st : StateD) (cv : IConstantVal) (vl : EIdx) : AM (Option EIdx)
T      304-317    14L  def noteProjIota (st : StateD) (cvp : ConstantVal) : StateD
                       ↳ def noteProjIota (st : StateD) (cvp : IConstantVal) : AM StateD
T      319-326     8L  def pushGenD (st : StateD) (d : Declaration) : StateD
                       ↳ def pushGenD (st : StateD) (d : IDeclaration) : AM StateD
T      328-336     9L  def noteGen (st : StateD) (d : Declaration) (T0 : Name) : StateD
                       ↳ def noteGen (st : StateD) (d : IDeclaration) (T0 : NIdx) : AM StateD
T      338-344     7L  def indPiTeleLen : Expr → Nat
                       ↳ def indPiTeleLen : EIdx → AM Nat
T      346-349     4L  def parseRuleD (st : StateD) (ru : RuleRec) : M RecRule
                       ↳ def parseRuleD (st : StateD) (ru : RuleRec) : AM (M IRecRule)
P      351-375    25L  def blockRecOf (st : StateD) (types : List IndTypeRec) (ctors : List IndCtorRec) (recs : List IndRecRec) : M InModel.BlockRec
T      377-396    20L  def registerProjOwners (st : StateD) (tys : List IndTypeRec) (cts : List IndCtorRec) (rcs : List IndRecRec) (block : List ConstantInfo) : M StateD
                       ↳ def registerProjOwners (st : StateD) (tys : List IndTypeRec) (cts : List IndCtorRec) (rcs : List IndRecRec) (block : List IConstantInfo) : AM (M StateD)
T      398-404     7L  def pushGenList (st : StateD) : List Declaration → Name → StateD
                       ↳ def pushGenList (st : StateD) : List IDeclaration → NIdx → AM StateD
T      406-558   153L  def validateIndD (st : @& StateD) (tys : List IndTypeRec) (cts : List IndCtorRec) (rcs : List IndRecRec) : M (RecordVerdict ⊕ (List IndCtorRec × Nat))
                       ↳ def validateIndD (st : @& StateD) (tys : List IndTypeRec) (cts : List IndCtorRec) (rcs : List IndRecRec) : AM (M (RecordVerdict ⊕ (List IndCtorRec × Nat)))
T      560-623    64L  def installIndD (st : StateD) (tys : List IndTypeRec) (cts : List IndCtorRec) (rcs : List IndRecRec) (nPd : Nat) : M (StateD ⊕ RecordVerdict)
                       ↳ def installIndD (st : StateD) (tys : List IndTypeRec) (cts : List IndCtorRec) (rcs : List IndRecRec) (nPd : Nat) : AM (M (StateD ⊕ RecordVerdict))
T      625-697    73L  def processLineCoreD (st : StateD) (d : DeclRec) : M (StateD ⊕ RecordVerdict)
                       ↳ def processLineCoreD (st : StateD) (d : DeclRec) : AM (M (StateD ⊕ RecordVerdict))
P      699-711    13L  def applyDeclD (st : StateD) (d : DeclRec) : M (StateD ⊕ RecordVerdict)
P      713-726    14L  def applyLine (st : StateD) (r : LineRec) : M (StateD ⊕ RecordVerdict)
T      730-753    24L  structure ParseResultD where
                       ↳ structure ParseResultD where
P      755-758     4L  def StateD.init (inModel : Bool) (census : Bool := false) : StateD
P      760-763     4L  def ParseResultD.ofState (st : StateD) : ParseResultD
P      765-775    11L  def applyFinalLine (st : StateD) (b : @& ByteArray) (i : USize) (lineNo : Nat) : Except (CheckError × Nat) StateD
P      777-811    35L  def feedChunk (st : StateD) (b : @& ByteArray) (i : USize) (lineNo : Nat) : Except (CheckError × Nat) (StateD × Nat × USize)
P      813-814     2L  def chunkSize : USize
P      816-825    10L  def sizeError : CheckError × Nat
P      827-839    13L  def parseBytes (b : ByteArray) (inModel : Bool := true) (census : Bool := false) : Except (CheckError × Nat) ParseResultD
P      841-846     6L  def parseExportD (contents : String) (inModel : Bool := true) (census : Bool := false) : Except (CheckError × Nat) ParseResultD
P      848-865    18L  def chunkStep (st : StateD) (carry : ByteArray) (lineNo total : Nat) (buf0 : ByteArray) : Except (CheckError × Nat) (StateD × ByteArray × Nat × Nat)
P      867-874     8L  def chunkFinish (st : StateD) (carry : ByteArray) (lineNo : Nat) : Except (CheckError × Nat) ParseResultD
P      876-880     5L  def concatBytes : List ByteArray → ByteArray
P      882-901    20L  def parseChunks (chunks : List ByteArray) (inModel : Bool := true) (census : Bool := false) : Except (CheckError × Nat) ParseResultD
P      903-931    29L  partial def parseExportHandleD (h : IO.FS.Handle) (inModel : Bool := true) (census : Bool := false) (chunk : USize := chunkSize) : IO (Except (CheckError × Nat) ParseResultD)
P      933-938     6L  def parseExportStreamD (path : System.FilePath) (inModel : Bool := true) (census : Bool := false) (chunk : USize := chunkSize) : IO (Except (CheckError × Nat) ParseResultD)
```

### `ConLeche/Frontend/Prepare.lean` — 10 decls, 65 lines (8T 0P 2S)

```
T       83-88      6L  structure PreludeIx where
                       ↳ structure PreludeIx where
T       90-93      4L  def preludeKey (d : Declaration) : Name
                       ↳ def preludeKey (d : IDeclaration) : AM NIdx
T      109-110     2L  def declares (n : Name) (d : Declaration) : Bool
                       ↳ def declares (n : NIdx) (d : IDeclaration) : AM Bool
S(T)   112-119     8L  def pickSpec (n : Name) : List Declaration → Option Declaration × List Declaration
                       ↳ Rust port skips it: The `List` specification of `pick`, which con-leche proves `pick` equal to; no caller on the run path, and its `d :: ds'` is `Vec::insert` (task #50). `prepare.rs`'s test module carries it as an executable check of `pick_idx`.
T      121-124     4L  def pick (n : Name) (ds : Array Declaration) : Option Declaration × Array Declaration
                       ↳ def pick (n : NIdx) (ds : Array IDeclaration) : AM (Option IDeclaration × Array IDeclaration)
T      126-135    10L  def frontOf (acc : Array Declaration) : List Declaration → Array Declaration → Array Declaration × Array Declaration
                       ↳ def frontOf (acc : Array IDeclaration) : List IDeclaration → Array IDeclaration → AM (Array IDeclaration × Array IDeclaration)
S(T)   137-144     8L  def frontSpec : List Declaration → List Declaration → List Declaration × List Declaration
                       ↳ Rust port skips it: The `List` specification of `frontOf`, as `pickSpec`.
T      148-157    10L  structure Prepared where
                       ↳ structure Prepared where
T      159-163     5L  def prepareD (pre : PreludeIx) (ds : Array Declaration) : Prepared
                       ↳ def prepareD (pre : PreludeIx) (ds : Array IDeclaration) : AM Prepared
T      165-172     8L  def preparePrelude (pre : PreludeIx) (ds : Array Declaration) : Array Declaration
                       ↳ def preparePrelude (pre : PreludeIx) (ds : Array IDeclaration) : AM (Array IDeclaration)
```

### `ConLeche/Frontend/ProjRec.lean` — 16 decls, 260 lines (16T 0P 0S)

```
T       83-104    22L  structure ProjRecOwner where
                       ↳ structure ProjRecOwner where
T      106-111     6L  def projIotaName (T : Name) (i : Nat) : Name
                       ↳ def projIotaName (T : NIdx) (i : Nat) : AM NIdx
T      113-118     6L  def isProjIotaName : Name → Bool
                       ↳ def isProjIotaName : NIdx → AM Bool
T      120-125     6L  def projIotaLevel (ty : Expr) : Option Level
                       ↳ def projIotaLevel (ty : EIdx) : AM (Option LIdx)
T      127-136    10L  def occursConst (n : Name) : Expr → Bool
                       ↳ def occursConst (n : NIdx) : EIdx → AM Bool
T      151-178    28L  def occursConstB (n : Name) : Nat → Expr → Option Bool × Nat
                       ↳ def occursConstB (n : NIdx) : Nat → EIdx → AM (Option Bool × Nat)
T      180-225    46L  def occursConstGo (n : Name) (seen : Std.HashSet Expr) : Expr → Bool × Std.HashSet Expr
                       ↳ def occursConstGo (n : NIdx) (seen : Std.HashSet EIdx) : EIdx → AM (Bool × Std.HashSet EIdx)
T      227-231     5L  def occursConstFast (n : Name) (e : Expr) : Bool
                       ↳ def occursConstFast (n : NIdx) (e : EIdx) : AM Bool
T      233-237     5L  def lamBody : Expr → Expr
                       ↳ def lamBody : EIdx → AM EIdx
T      239-245     7L  def stripPisAll : Expr → List (Expr × BinderMeta) × Expr
                       ↳ def stripPisAll : EIdx → AM (List (EIdx × BinderMeta) × EIdx)
T      247-249     3L  def mkLams (bs : List (Expr × BinderMeta)) (body : Expr) : Expr
                       ↳ def mkLams (bs : List (EIdx × BinderMeta)) (body : EIdx) : AM EIdx
T      251-257     7L  def instPisOpen : Expr → List Expr → Option Expr
                       ↳ def instPisOpen : EIdx → List EIdx → AM (Option EIdx)
T      259-269    11L  def buildBinders (mk : Expr → Option Expr) : Nat → Expr → Option (List Expr × Expr)
                       ↳ def buildBinders (mk : EIdx → Option EIdx) : Nat → EIdx → AM (Option (List EIdx × EIdx))
T      271-277     7L  def headIs (T : Name) (e : Expr) : Bool
                       ↳ def headIs (T : NIdx) (e : EIdx) : AM Bool
T      279-330    52L  def projRecValue (o : ProjRecOwner) (ℓ : Level) (ty val : Expr) (i : Nat) : Option Expr
                       ↳ def projRecValue (o : ProjRecOwner) (ℓ : LIdx) (ty val : EIdx) (i : Nat) : AM (Option EIdx)
T      332-370    39L  def projRecOwners (block : List ConstantInfo) (types : List (Name × List Name × Expr × Nat × Nat × List Name × Bool)) (ctors : List (Name × Nat × Expr)) (recs : List (Name × List Name × Expr × Nat × Nat)) : List ProjRecOwner
                       ↳ def projRecOwners (block : List IConstantInfo) (types : List (NIdx × List NIdx × EIdx × Nat × Nat × List NIdx × Bool)) (ctors : List (NIdx × Nat × EIdx)) (recs : List (NIdx × List NIdx × EIdx × Nat × Nat)) : AM (List ProjRecOwner)
```

### `ConLeche/Frontend/NatOpGround.lean` — 6 decls, 111 lines (6T 0P 0S)

```
T       54-77     24L  def usedConstsGo (seen : Std.HashSet Expr) (acc : Array Name) (e : Expr) : Std.HashSet Expr × Array Name
                       ↳ def usedConstsGo (seen : Std.HashSet EIdx) (acc : Array NIdx) (e : EIdx) : AM (Std.HashSet EIdx × Array NIdx)
T       79-95     17L  def _root_.ConLeche.Declaration.usedConsts : Declaration → Array Name
                       ↳ def _root_.ConLeche.IDeclaration.usedConsts : IDeclaration → AM (Array NIdx)
T       97-104     8L  def isNatOpRecord : Declaration → Option Name
                       ↳ def isNatOpRecord : IDeclaration → AM (Option NIdx)
T      106-136    31L  def hoistTargets (ds : Array Declaration) : Std.HashMap Nat Nat
                       ↳ def hoistTargets (ds : Array IDeclaration) : AM (Std.HashMap Nat Nat)
T      138-162    25L  def applyHoist (ds : Array Declaration) (target : Std.HashMap Nat Nat) : Array Declaration × Array Name
                       ↳ def applyHoist (ds : Array IDeclaration) (target : Std.HashMap Nat Nat) : AM (Array IDeclaration × Array NIdx)
T      164-169     6L  def hoistNatOpGround (ds : Array Declaration) : Array Declaration × Array Name
                       ↳ def hoistNatOpGround (ds : Array IDeclaration) : AM (Array IDeclaration × Array NIdx)
```

### `ConLeche/Frontend/Prelude.lean` — 2 decls, 11 lines (0T 2P 0S)

```
P       57-62      6L  def builtinPreludeText : String
P       64-68      5L  def builtinPreludeE : Except (CheckError × Nat) PreludeIx
```

---

Counts: **894** declarations over **12376** con-leche lines; **163** bodies
match a term structurally and need `view`; **293** comparison lines need
index equality.

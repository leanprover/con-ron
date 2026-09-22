/-
# `ConRon.Bridge.Inductives` — Theorem 1's inductive tier (index)

DESIGN §8.2's **Theorem 1** at `Arena/Inductives.lean` and the ten modules
under it — the `.indDecl` arm of con-leche's `checkDecl`
(`ConLeche/Kernel/Checker.lean:564-600`) and the two routes behind it.  This
tier discharges the hypothesis `Bridge/Checker/Hyp.lean` names `IndSpec`.

## The modules, in dependency order

| module | what |
|---|---|
| `Inductives/Rel.lean` | the two frames (`PStep`, `CoreStep`), the two statement shapes (`PSpec`, `CSpec`), the answer relations, the record relations, `InstRel` and `IndOut` |
| `Inductives/StructParts.lean` | the generators: families, spines, Π→λ, the structure recogniser, the projection bodies, the two memoised predicates |
| `Inductives/SumParts.lean` | `sumSplit` and `InductiveShape.withSort` |
| `Inductives/NativeParts.lean` | the positivity classification and the GENERATED recursor (`structRecTyR` / `structRecRhsR`), the rule checks, the two recognisers |
| `Inductives/StructInstall.lean` | the parameter domains and the projection TABLE |
| `Inductives/SumInstall.lean` | the direct install's stages: telescope, caps, field sorts, positivity normalisation, constructors, rules |
| `Inductives/NativeInstall.lean` | the fixpoint route: the two-pass install |
| `Inductives/Modeled.lean` | the modeled route: iota certificates, member checks, projection functions, capability theorems |
| `Inductives/Decl.lean` | `checkIndDecl_bridge` — the arm — and `indSpec_of_bridge` |
| `Inductives/Axioms.lean` | the trust census |

## Two grades, and the rule for which a twin gets

A twin that calls the knot (`inferTypeCore`, `isDefEqCore`, `whnf`,
`annotateCore`, `ensureSortCore`) is CORE grade: its statement is a `CSpec`,
its invariant `CheckOK`, its frame `CoreStep`, and it takes `CoreSpec` as a
hypothesis.  Everything else is PURE grade: `PSpec`, `StateOK`, `PStep`, and
task #97-P3-0 §2's rule that such a theorem must not mention the caches.

## The tier's one finding

`IndSpec` as `Bridge/Checker/Hyp.lean` states it asks for `PersIFEnv fe'`,
which is **false** for this arm (the route runs with the scratch tier open),
and does NOT ask for `Pushed fe fe'`, which its own consumer `DeclOut` needs.
`Bridge/Inductives/Decl.lean`'s module note writes the correction out;
`IndOut` is the corrected conclusion and `checkIndDecl_bridge` is proved at
it.
-/
import ConRon.Bridge.Inductives.Rel
import ConRon.Bridge.Inductives.StructParts
import ConRon.Bridge.Inductives.SumParts
import ConRon.Bridge.Inductives.NativeParts
import ConRon.Bridge.Inductives.StructInstall
import ConRon.Bridge.Inductives.SumInstall
import ConRon.Bridge.Inductives.NativeInstall
import ConRon.Bridge.Inductives.Modeled
import ConRon.Bridge.Inductives.Decl
import ConRon.Bridge.Inductives.Axioms

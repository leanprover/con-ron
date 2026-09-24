/-
# `ConRon.Arena.Inductives.StructInstallF` — the `F` names
(DESIGN.md §8, task #97d-2)

`ConLeche/Kernel/Inductives/StructInstallF.lean` is `StructInstall.lean`'s two
functions over an `FEnv`, plus the `StructWalkers` record the cached driver
fills with its memoised walks.  The arena has ONE environment type (task #97c's
deviation 1), so the `F` twins ARE `Arena/Inductives/StructInstall.lean`'s;
what is left for this module is the `F`-suffixed NAMES as `abbrev`s — the same
functions, so nothing can drift, and a reader coming from con-leche's cached
tier finds the name being looked for.  `Arena/FEnv.lean` is the same
arrangement for `Core.lean`.

**`StructWalkers` has no twin.**  It is a record of two FUNCTION VALUES —
`resolve : FEnv → Expr → Bool` and `projBodies : Name → Nat → Nat → Expr →
Option (Array Expr)` — whose only purpose is to let con-leche's cached driver
substitute memoised walks for the pure ones at run time
(`ConLeche.Cached.structWalkersC`; the equality `structWalkersC_eq_plain` is
what makes the substitution invisible).  The arena has no such seam: its
`constsResolve` and `structProjBodies` ARE the memoised walks, there is one of
each, and a record of two closures is exactly what DESIGN §3.4 forbids in code
Aeneas must translate.  So `StructWalkers` and `StructWalkers.plain` are
census class (P) here — apparatus of the tier the port does not have — and
every `w.resolve` / `w.projBodies` of the `F` files is the arena's own
function at the call site.
-/
import ConRon.Arena.Inductives.StructInstall

namespace ConRon.Arena

/-- con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:27-36 checkStructDomsAtF
`checkStructDomsAt` through the index — the same function; see the module
note. -/
abbrev checkStructDomsAtF := @checkStructDomsAt

/-- con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:38-48 checkStructDomsAtFA
`checkStructDomsAtF` over arrays — the same function at `List.toArray`; see
the module note. -/
abbrev checkStructDomsAtFA := @checkStructDomsAt

/-- con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:73-95 checkStructProjTableF
`checkStructProjTable` through the index — the same function; see the module
note. -/
abbrev checkStructProjTableF := @checkStructProjTable

end ConRon.Arena

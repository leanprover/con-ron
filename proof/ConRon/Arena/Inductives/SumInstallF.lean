/-
# `ConRon.Arena.Inductives.SumInstallF` — the `F` names
(DESIGN.md §8, task #97d-2)

`ConLeche/Kernel/Inductives/SumInstallF.lean` is `SumInstall.lean`'s stages
over an `FEnv`.  The arena has ONE environment type (task #97c's deviation 1),
so the `F` twins ARE `Arena/Inductives/SumInstall.lean`'s; this module carries
the `F`-suffixed NAMES as `abbrev`s, as `Arena/Inductives/StructInstallF.lean`
and `Arena/FEnv.lean` do.

`checkSumIndF`'s `capsOf` argument became `isRec : Bool` at the twin — the
module note of `SumInstall.lean` says why — so the `abbrev` has that
signature.
-/
import ConRon.Arena.Inductives.SumInstall

namespace ConRon.Arena

/-- con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:20-30 checkSumTeleF
`checkSumTele` through the index — the same function. -/
abbrev checkSumTeleF := @checkSumTele

/-- con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:32-43 checkSumIndF
-- con-leche: CHANGED since 3ca9e2fe — re-port, re-test, re-prove SumInstallF.checkSumIndF_bridge, then delete this line
`checkSumInd` through the index — the same function. -/
abbrev checkSumIndF := @checkSumInd

/-- con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:32-48 checkStructFieldSortsIF
`checkStructFieldSortsI` through the index — the same function. -/
abbrev checkStructFieldSortsIF := @checkStructFieldSortsI

/-- con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:50-68 checkStructFieldSortsIFA
`checkStructFieldSortsIF` over an array of field variables — the same function
at `List.toArray`. -/
abbrev checkStructFieldSortsIFA := @checkStructFieldSortsI

/-- con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:83-95 normCtorValF
-- con-leche: CHANGED since 3ca9e2fe — re-port, re-test, re-prove SumInstallF.normCtorValF_bridge, then delete this line
`normCtorVal` through the index — the same function. -/
abbrev normCtorValF := @normCtorVal

/-- con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:70-100 checkSumCtorF
-- con-leche: CHANGED since 3ca9e2fe — re-port, re-test, re-prove SumInstallF.checkSumCtorF_bridge, then delete this line
`checkSumCtor` through the index — the same function. -/
abbrev checkSumCtorF := @checkSumCtor

/-- con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:102-112 checkSumCtorsF
`checkSumCtors` through the index — the same function. -/
abbrev checkSumCtorsF := @checkSumCtors

/-- con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:114-117 consSumCtorsF
`consSumCtors` through the index — the same function. -/
abbrev consSumCtorsF := @consSumCtors

end ConRon.Arena

/-
# `ConRon.Arena.Inductives.NativeInstallF` — the `F` names
(DESIGN.md §8, task #97d-2)

`ConLeche/Kernel/Inductives/NativeInstallF.lean` is `NativeInstall.lean`'s five
`StructWalkers`-taking functions over an `FEnv`.  The arena has ONE environment
type and no `StructWalkers` seam (task #97c's deviation 1 and
`Arena/Inductives/StructInstallF.lean`'s note), so the `F` twins ARE
`Arena/Inductives/NativeInstall.lean`'s; this module carries the `F`-suffixed
NAMES as `abbrev`s.
-/
import ConRon.Arena.Inductives.NativeInstall

namespace ConRon.Arena

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:22-59 nativeOpenedOkF
`nativeOpenedOk` through the index — the same function. -/
abbrev nativeOpenedOkF := @nativeOpenedOk

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:61-69 nativeFieldsOkF
`nativeFieldsOk` through the index — the same function. -/
abbrev nativeFieldsOkF := @nativeFieldsOk

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:71-85 checkNativeRulesF
`checkNativeRules` through the index — the same function. -/
abbrev checkNativeRulesF := @checkNativeRules

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:87-115 checkNativeRecF
`checkNativeRec` through the index — the same function. -/
abbrev checkNativeRecF := @checkNativeRec

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:117-126 checkNativeTableF
`checkNativeTable` through the index — the same function. -/
abbrev checkNativeTableF := @checkNativeTable

end ConRon.Arena

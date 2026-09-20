/-
# `ConRon.Arena.FEnv` — the indexed environment's guard twins

con-leche's `ConLeche/Kernel/FEnv.lean` is fourteen declarations: the
indexed environment `FEnv` and its five operations, and the seven
`F`-suffixed guard twins that read the environment *through the index*
rather than through the association list.

**The arena splits them the other way round, and this module records why.**

* The environment half — `IFEnv`, `mkIFEnvGo`, `mkIFEnv`, `find?`,
  `restrictTo`, `push`, `findProj?` — is in `Arena/Env.lean` (task #97e),
  because the arena has ONE environment type and the declaration layer is
  where it belongs.
* The guard half is in `Arena/Core.lean`, as the ONE twin of each con-leche
  PAIR (`natLitSupported` / `natLitSupportedF`, and its six siblings).
  con-leche needs two spellings because its kernel tier reads `Env` and its
  `Cached` tier reads `FEnv`; the arena's checker reads `IFEnv` and nothing
  else (DESIGN §8.3, lesson 13), so the two collapse.

The import order forces the split: con-leche's `FEnv.lean` imports
`Core.lean`, while the arena's `Core.lean` has to CALL the guards from
inside `whnfCoreBody` and `inferBody`.  So the bodies are where the guards
must be defined, and what is left for this module is the seven `F`-suffixed
NAMES — which P2d, the census and anyone reading con-leche's `Cached` tier
beside the arena will look for.  They are `abbrev`s, so they are the same
function and no second definition exists to drift.
-/
import ConRon.Arena.Core

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/FEnv.lean:97-99 FEnv.towerSlotsAllF —
`towerSlotsAll` through the index; the arena's `towerSlotsAll` already is
that (see the module note). -/
abbrev IFEnv.towerSlotsAllF (fe : IFEnv) (T : NIdx) (nF : Nat) : AM Bool :=
  towerSlotsAll fe T nF

/-- con-leche: ConLeche/Kernel/FEnv.lean:101-103 FEnv.andRescueSlotsF —
`andRescueSlots` through the index. -/
abbrev IFEnv.andRescueSlotsF (fe : IFEnv) (ctor : NIdx) (nP : Nat)
    (ust : LsIdx) : AM Bool :=
  andRescueSlots fe ctor nP ust

/-- con-leche: ConLeche/Kernel/FEnv.lean:105-110 FEnv.recSlotsAllF —
`recSlotsAll` through the index. -/
abbrev IFEnv.recSlotsAllF (fe : IFEnv) (T : NIdx) (nF : Nat) : AM Bool :=
  recSlotsAll fe T nF

/-- con-leche: ConLeche/Kernel/FEnv.lean:116-119 natLitSupportedF —
`natLitSupported` through the index. -/
abbrev natLitSupportedF (fe : IFEnv) : AM Bool := natLitSupported fe

/-- con-leche: ConLeche/Kernel/FEnv.lean:121-130 strLitSupportedF —
`strLitSupported` through the index. -/
abbrev strLitSupportedF (fe : IFEnv) : AM Bool := strLitSupported fe

/-- con-leche: ConLeche/Kernel/FEnv.lean:132-145 natOpGuardF — `natOpGuard`
through the index. -/
abbrev natOpGuardF (fe : IFEnv) (c : NIdx) : AM Bool := natOpGuard fe c

/-- con-leche: ConLeche/Kernel/FEnv.lean:147-151 natOpStoredF —
`natOpStored` through the index (con-leche's task #161 item B3). -/
abbrev natOpStoredF (fe : IFEnv) (c : NIdx) : AM Bool := natOpStored fe c

end ConRon.Arena

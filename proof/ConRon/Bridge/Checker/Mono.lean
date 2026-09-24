/-
# `ConRon.Bridge.Checker.Mono` — one fuel for the whole fold

DESIGN §8.2 states Theorem 1 per declaration, at **some** fuel:

    ∃ F, ConLeche.checkDecl μ (fueledOps μ F) pins (denoteEnv st) … = .ok …

and its fold at **one** fuel for the whole stream, because that is what
`Model/Fold.lean:254 checkDeclsPure_sound_of` takes:

    ∃ F, checkDeclsPure μ (fueledOps μ F) pins ds = .ok env'

The two are reconciled by fuel MONOTONICITY, and con-leche already has it —
just one layer down.  `ConLeche/Verify/Fueled.lean`'s `FueledM` is the subtype
of fuel-indexed pure computations that are monotone (its `property` field),
`ConLeche/Verify/BridgeDecl.lean:997`'s `checkDecl_datF` says that
`checkDecl` at the fueled record, read at fuel `F`, IS `checkDecl` at
`fueledOps μ F`, and the two together give exactly what the fold needs.

This is the history report's fine print 2 in its constructive form: the
statement is at `fueledOps μ F` specifically, so a per-step `F` has to be
raised to a common one, and the raise is one `max` per step.

**The import.**  This module is the only one of the tier that reaches past
con-leche's `Kernel/*` into its `Verify/*` (task #97-P3-0's import rule).  It
takes exactly two declarations — `checkDecl_datF` and `FueledM`'s subtype
property — and the capstone module takes `Model/Fold.lean`.  Both are
prebuilt in con-leche's `.lake`, so neither costs elaboration here.
-/
import ConRon.Bridge.Checker.Decl
import ConLeche.Verify.BridgeDecl

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:997 checkDecl_datF
con-leche: ConLeche/Verify/Fueled.lean:32-34 FueledM
**`checkDecl` is monotone in the fuel**: a declaration accepted at `F` is
accepted at every larger fuel, with the same environment.  `checkDecl` at the
fueled record is monotone by construction (`FueledM` is the subtype of
monotone families), and `checkDecl_datF` identifies its fuel-`F` reading with
`checkDecl` at `fueledOps μ F`. -/
theorem checkDecl_mono {μ : CheckMode} {pins : List NatOpPinSet}
    {env env' : Env} {d : Declaration} {F F' : Nat} (hle : F ≤ F')
    (h : ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pins env d = .ok env') :
    ConLeche.checkDecl μ (ConLeche.fueledOps μ F') pins env d = .ok env' := by
  rw [← ConLeche.checkDecl_datF (mode := μ) (pins := pins)] at h ⊢
  exact (ConLeche.checkDecl μ (ConLeche.fueledOpsM μ) pins env d).property hle h

end ConRon.Bridge

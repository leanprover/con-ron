/-
# `ConRon.Arena.CoreIO` — the io knot (the leaf lane), over handles

The twin of `ConLeche/Kernel/CoreIO.lean`.  `whnfCore` / `whnf` / `defeq` /
`annotate` are the *full* knot's at the same fuel — the io lane consumes the
certified reduction and definitional equality and never supplies them — and
`infer` is `inferBodyIO` tied to the io knot one level down.  The full knot
never mentions this one: that asymmetry is con-leche's mode-provenance
discipline, and it survives the change of representation unchanged.

**Class (S) in the census, twinned anyway.**  con-leche's Rust port skips
these three ("the port's `infer_at_i` carries the io grade as a runtime
flag"), because the Rust has one knot.  The arena has one knot too — the
memoized `coreKnot` — so this lane is, here as in con-leche, the *statement
subject* the io claims will be phrased at rather than a thing the checker
runs.  It is twinned because P3 will need it to state the knot equations,
and because it costs twelve lines.

**No memo.**  con-leche's leaf lane is unmemoized (it is a specification,
not an executed core), and so is this one: adding a table here would give
the io grade two of them and break DESIGN §8.3's lesson 9 ("a hit in one
grade never serves another") in the other direction.
-/
import ConRon.Arena.FEnv

namespace ConRon.Arena

open ConLeche

/-- con-leche: ConLeche/Kernel/CoreIO.lean:91-119 coreKnotIO — **the io
knot** (the leaf lane).  Its own `inferIO` slot is the io body again: the io
grade is idempotent, there being nothing below io to select. -/
def coreKnotIO (mode : CheckMode) (fe : IFEnv) : Nat → CoreFnsA
  | 0 =>
    { whnfCore := fun _ _ => fail (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => fail (.internal "fuel exhausted: whnf")
      infer := fun _ _ => fail (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => fail (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => fail (.internal "fuel exhausted: annotate")
      inferIO := fun _ _ => fail (.internal "fuel exhausted: infer") }
  | fuel + 1 =>
    { whnfCore := (coreKnot mode fe id (fuel + 1)).whnfCore
      whnf := (coreKnot mode fe id (fuel + 1)).whnf
      defeq := (coreKnot mode fe id (fuel + 1)).defeq
      annotate := (coreKnot mode fe id (fuel + 1)).annotate
      infer := fun d e => inferBodyIO mode (coreKnotIO mode fe fuel) fe d e
      inferIO := fun d e => inferBodyIO mode (coreKnotIO mode fe fuel) fe d e }

/-- con-leche: ConLeche/Kernel/CoreIO.lean:121-124 pureFnsIO — the io core,
tied at `AM`: the specification the `InferClaimIO` family is stated at. -/
def pureFnsIO (mode : CheckMode) (fe : IFEnv) : Nat → CoreFnsA :=
  coreKnotIO mode fe

/-- con-leche: ConLeche/Kernel/CoreIO.lean:126-130 inferTypeCoreIO —
infer-only (io-grade) type inference, fueled: the io lane's single entry
point. -/
def inferTypeCoreIO (mode : CheckMode) (fe : IFEnv) (fuel depth : Nat)
    (e : EIdx) : AM EIdx :=
  (pureFnsIO mode fe fuel).infer depth e

end ConRon.Arena

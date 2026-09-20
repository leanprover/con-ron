/-
# The P2s spike: the three subjects

Three (B) twins of rising complexity, each mirroring con-leche's pure
definition clause by clause (DESIGN §8.6, `P2s SPIKE`):

1. `instantiate1A` — `ConLeche/Kernel/ExprOps.lean:33` (`instantiate1`) over
   handles, with `:81`'s memo (`instantiate1Go`) and the derived-word cutoff
   DESIGN §8.3 asks for ("instantiate returns at `bvarB ≤ offset`");
2. `whnfCoreAppArm` — the `app`-of-`lam` β case of
   `ConLeche/Kernel/Core.lean:1935` (`whnfCoreBody`), with the knot record
   abstracted as a `CoreFnsA` over handles exactly as con-leche's body takes
   `r : CoreFns m`;
3. `memoWhnfCore` — `ConLeche/Cached/CoreC.lean:1877` (`memoEI`) at the
   `whnfCore` table.

The invariants are con-leche's, transported through `denoteE`: `StateOK` is
`ISOK`'s `wf` clause (`Verify/SimI.lean:54`), `Inst1MemoA` is
`Inst1MemoInv` (`Kernel/ExprOps.lean:62`), and `WhnfMemoOK` is `ISOK`'s
`whnfC` clause — including its `∃ F, ∀ d` shape (the history report's
lesson 8: memo keys carry no ambient depth).
-/
import ConRon.Arena.Spike.Base

namespace ConRon.Arena.Spike

open ConLeche Std.Do

/-! ## Pure side-conditions this spike needs from con-leche

Two lemmas about `ConLeche.Expr` alone; both are the *pure* justification of
an arena cutoff, and neither mentions a store. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33 instantiate1 — **the cutoff's
licence**: a term with no loose `bvar` at or above the cursor is its own
instantiation.  DESIGN §8.3's "instantiate returns at `bvarB ≤ offset`". -/
theorem instantiate1_of_bvarBound_le {v : Expr} :
    ∀ (e : Expr) (d : Nat), e.bvarBound ≤ d → e.instantiate1 v d = e := by
  intro e
  induction e with
  | bvar i =>
    intro d h
    simp only [Expr.bvarBound] at h
    simp only [Expr.instantiate1, if_neg (show ¬ i = d by omega), if_neg (show ¬ i > d by omega)]
  | fvar _ _ _ | sort _ | const _ _ | lit _ => intro d _; simp [Expr.instantiate1]
  | app f a ihf iha =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [Expr.instantiate1, ihf d h.1, iha d h.2]
  | lam ty b m iht ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [Expr.instantiate1, iht d h.1, ihb (d + 1) (by omega)]
  | forallE ty b m iht ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [Expr.instantiate1, iht d h.1, ihb (d + 1) (by omega)]
  | letE ty w b iht ihw ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp [Expr.instantiate1, iht d h.1.1, ihw d h.1.2, ihb (d + 1) (by omega)]
  | proj n i e ih => intro d h; simp only [Expr.bvarBound] at h; simp [Expr.instantiate1, ih d h]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1454 bvarBRaw_exact — the cutoff
as the arena tests it: the *packed* field, below saturation, licenses the
early return. -/
theorem instantiate1_of_raw_le {v : Expr} {e : Expr} {d : Nat}
    (hsat : e.bvarBRaw < satRange) (hle : e.bvarBRaw ≤ d) :
    e.instantiate1 v d = e :=
  instantiate1_of_bvarBound_le e d (by rw [← Expr.bvarBRaw_exact e hsat]; exact hle)

/-! ## The state invariant -/

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the state invariant, cut
to the spike's one clause: the arena is well formed. -/
structure StateOK (s : AState) : Prop where
  wf : StoreWF s.store

/-- con-leche: ConLeche/Kernel/ExprOps.lean:62 Inst1MemoInv — the
`instantiate1` memo's invariant, transported through `denoteE`: every
recorded answer is the real one, at the key's own cursor.  The substituted
handle does not appear: the invariant speaks of denotations, so `ve` is
enough. -/
def Inst1MemoA (ve : Expr) (s : AState) : Prop :=
  ∀ (k : EIdx × Nat) (r : EIdx), s.inst1C[k]? = some r →
    ∃ e, denoteE s.store k.1 = some e ∧
      denoteE s.store r = some (e.instantiate1 ve k.2)

/-! ## Subject 1 — `instantiate1`, over handles, memoized

`ConLeche/Kernel/ExprOps.lean:81` (`instantiate1Go`) clause for clause: the
five leaf kinds answer without touching the memo, everything else probes the
memo, runs the body one level down and inserts.  Two deviations, both forced
by the representation and both named in DESIGN §8.3/§8.4:

* **the derived-word cutoff** comes first (lesson 20) — the pure walk has no
  cheap way to ask "does this subtree mention `bvar ≥ d`?", the arena reads
  it off `Expr.data` in `O(1)`;
* **fuel**, because a handle DAG has no structural order the elaborator can
  see (§8.4: "fuel as an explicit `Nat`").  Exhaustion is a failure, and
  Theorem 1 claims nothing on failure — con-leche's `SimAt` shape. -/
def instantiate1A (v : EIdx) : Nat → EIdx → Nat → AM EIdx
  | 0, _, _ => fail (.internal "fuel exhausted: instantiate1")
  | fuel + 1, h, d => do
    let der ← derivedE h
    let b := (bvarOfData der).toNat
    if b < satRange && b ≤ d then
      pure h
    else
      match ← view h with
      | .bvar i =>
        if i = d then pure v
        else if i > d then internE (.bvar (i - 1))
        else pure h
      | .fvar _ _ => pure h
      | .sort _ => pure h
      | .const _ _ => pure h
      | .lit _ => pure h
      | .app f a => do
        match ← inst1Get (h, d) with
        | some r => pure r
        | none => do
          let f' ← instantiate1A v fuel f d
          let a' ← instantiate1A v fuel a d
          let r ← internE (.app f' a')
          inst1Set (h, d) r
          pure r
      | .lam ty body m => do
        match ← inst1Get (h, d) with
        | some r => pure r
        | none => do
          let t ← instantiate1A v fuel ty d
          let b' ← instantiate1A v fuel body (d + 1)
          let r ← internE (.lam t b' m)
          inst1Set (h, d) r
          pure r
      | .forallE ty body m => do
        match ← inst1Get (h, d) with
        | some r => pure r
        | none => do
          let t ← instantiate1A v fuel ty d
          let b' ← instantiate1A v fuel body (d + 1)
          let r ← internE (.forallE t b' m)
          inst1Set (h, d) r
          pure r
      | .letE ty val body => do
        match ← inst1Get (h, d) with
        | some r => pure r
        | none => do
          let t ← instantiate1A v fuel ty d
          let w ← instantiate1A v fuel val d
          let b' ← instantiate1A v fuel body (d + 1)
          let r ← internE (.letE t w b')
          inst1Set (h, d) r
          pure r
      | .proj n i sub => do
        match ← inst1Get (h, d) with
        | some r => pure r
        | none => do
          let u ← instantiate1A v fuel sub d
          let r ← internE (.proj n i u)
          inst1Set (h, d) r
          pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:120 instantiate1 (the `@[csimp]`
entry point) — the top-level call: the memo is fresh before and dropped
after, because it depends on the substituted term. -/
def instantiate1Top (v : EIdx) (fuel : Nat) (h : EIdx) : AM EIdx := do
  inst1Clear
  let r ← instantiate1A v fuel h 0
  inst1Clear
  pure r

/-! ## Subject 2 — the `app`-of-`lam` β arm of `whnfCoreBody`

`ConLeche/Kernel/Core.lean:1935`.  The knot is a hypothesis, exactly as
con-leche's body takes `r : CoreFns m`: `CoreFnsA` is `CoreFns` over handles,
with only the three slots this arm calls. -/

/-- con-leche: ConLeche/Kernel/Core.lean:97 CoreFns — the knot record over
handles, cut to the slots the β arm calls. -/
structure CoreFnsA where
  whnfCore : Nat → EIdx → AM EIdx
  inferIO : Nat → EIdx → AM EIdx
  defeq : Nat → EIdx → EIdx → AM Bool

/-- con-leche: ConLeche/Kernel/Core.lean:1941 whnfCoreBody (the `.app` arm) —
head-normalize the function, and if it is a λ, β-reduce behind the argument
certificate.  The non-λ head (ι, the stuck application) is out of the spike's
scope and is a `notImplemented` here; partial correctness means the bridge
claims nothing there. -/
def whnfCoreAppArm (mode : CheckMode) (r : CoreFnsA) (fuel : Nat) (depth : Nat)
    (f a : EIdx) : AM EIdx := do
  let hf ← r.whnfCore depth f
  match ← view hf with
  | .lam ty body mb =>
    if betaGateFires mode mb.pw then
      let ob ← instantiate1Top a fuel body
      r.whnfCore depth ob
    else
      let ta ← r.inferIO depth a
      if ← r.defeq depth ta ty then
        let ob ← instantiate1Top a fuel body
        r.whnfCore depth ob
      else
        internE (.app hf a)
  | _ => fail (.notImplemented "spike: only the β arm of whnfCore")

/-! ## Subject 3 — the memo-probing wrapper

`ConLeche/Cached/CoreC.lean:1877` (`memoEI`) at the `whnfCore` table. -/

/-- con-leche: ConLeche/Cached/CoreC.lean:1877 memoEI — probe the `whnfCore`
memo, run the body one fuel down on a miss, insert. -/
def memoWhnfCore (f : Nat → EIdx → AM EIdx) : Nat → EIdx → AM EIdx :=
  fun d h => do
    match ← whnfCoreGet h with
    | some r => pure r
    | none =>
      let r ← f d h
      whnfCoreSet h r
      pure r

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK (the `whnfC` clause) — the
`whnfCore` memo's invariant.  **Lesson 8 verbatim**: the key carries no
ambient depth, and the entry is justified by a depth-universal fact at *some*
fuel.  `pw` stands for con-leche's `(fueledFns μ env F).whnfCore`. -/
def WhnfMemoOK (pw : Nat → Nat → Expr → CheckM Expr) (s : AState) : Prop :=
  ∀ (i j : EIdx), s.whnfCoreC[i]? = some j →
    ∃ a b, denoteE s.store i = some a ∧ denoteE s.store j = some b ∧
      ∃ F, ∀ d, pw F d a = .ok b

end ConRon.Arena.Spike

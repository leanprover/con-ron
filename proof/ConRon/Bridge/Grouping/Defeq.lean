import ConRon.Bridge.Grouping.Core5

/-!
`defeqStep`'s two tails as their own definitions — verbatim copies of
`Arena/Core.lean`'s blocks, exactly as `Bridge/Core/Arms/Defeq.lean`'s
`dqCongrA` / `dqTailA` are, so that `mvcgen` meets the big two-view `match`
on its own.  `defeqStep_eq_tail` says `defeqStep` is its prefix followed by
`dqTailG`, by `rfl`.
-/

namespace ConRon.Bridge.Grouping

set_option mvcgen.warning false
set_option autoImplicit false

open ConRon.Arena Std.Do

/-- con-leche: ConLeche/Kernel/Core.lean:1579-1701 defeqStep — the congruence
half of the twin's `defeqStep`, verbatim (`Bridge/Core/Arms/Defeq.lean`'s
`dqCongrA`). -/
def dqCongrG (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (a' b' : EIdx) : AM Bool := do
  match ← view a', ← view b' with
  | .sort u, .sort v => liftFueled "level comparison" (← lvlEq? u v)
  | .lit l₁, .lit l₂ => pure (l₁ == l₂)
  -- a packed literal against a constructor form: compare shape-directed
  | .lit (.natVal n), .const c us => do
    let el ← emptyLevels
    let nz ← pinNatZero
    if c = nz ∧ us = el then pure (n == 0)
    else stuckIrrel mode r fe depth a' b'
  | .const c us, .lit (.natVal n) => do
    let el ← emptyLevels
    let nz ← pinNatZero
    if c = nz ∧ us = el then pure (n == 0)
    else stuckIrrel mode r fe depth a' b'
  | .lit (.natVal nn), .app f x => do
    match nn with
    | k' + 1 => do
      if f.tag == ETag.const then
        match ← view f with
        | .const c us => do
          let el ← emptyLevels
          let ns ← pinNatSucc
          if c = ns ∧ us = el then do
            let l ← internE (.lit (.natVal k'))
            r.defeq depth l x
          else stuckIrrel mode r fe depth a' b'
        | _ => stuckIrrel mode r fe depth a' b'
      else stuckIrrel mode r fe depth a' b'
    | _ => stuckIrrel mode r fe depth a' b'
  | .app f x, .lit (.natVal nn) => do
    match nn with
    | k' + 1 => do
      if f.tag == ETag.const then
        match ← view f with
        | .const c us => do
          let el ← emptyLevels
          let ns ← pinNatSucc
          if c = ns ∧ us = el then do
            let l ← internE (.lit (.natVal k'))
            r.defeq depth x l
          else stuckIrrel mode r fe depth a' b'
        | _ => stuckIrrel mode r fe depth a' b'
      else stuckIrrel mode r fe depth a' b'
    | _ => stuckIrrel mode r fe depth a' b'
  -- a string literal against a unary `String.ofList` application
  | .lit (.strVal st), .app fo _ => do
    if fo.tag == ETag.const then
      match ← view fo with
      | .const cO usO => do
        let el ← emptyLevels
        let sl ← pinStringOfList
        if cO = sl ∧ usO = el ∧ (← strLitSupported fe) then do
          let c ← strLitToConstructor st
          r.defeq depth c b'
        else stuckIrrel mode r fe depth a' b'
      | _ => stuckIrrel mode r fe depth a' b'
    else stuckIrrel mode r fe depth a' b'
  | .app fo _, .lit (.strVal st) => do
    if fo.tag == ETag.const then
      match ← view fo with
      | .const cO usO => do
        let el ← emptyLevels
        let sl ← pinStringOfList
        if cO = sl ∧ usO = el ∧ (← strLitSupported fe) then do
          let c ← strLitToConstructor st
          r.defeq depth a' c
        else stuckIrrel mode r fe depth a' b'
      | _ => stuckIrrel mode r fe depth a' b'
    else stuckIrrel mode r fe depth a' b'
  | .fvar i _, .fvar j _ =>
    if i == j then pure true else stuckIrrel mode r fe depth a' b'
  | .const n us, .const n' us' => do
    if n = n' then do
      if ← liftFueled "level comparison" (← lvlsEq? us us') then pure true
      else stuckIrrel mode r fe depth a' b'
    else stuckIrrel mode r fe depth a' b'
  -- binder congruence, BATCHED (task #97-P6-14); the annotation comparison
  -- runs LAST, innermost binder first
  | .forallE ty₁ body₁ m₁, .forallE ty₂ body₂ m₂ =>
    defeqBinders mode r depth ty₁ body₁ m₁ ty₂ body₂ m₂ false
  | .lam ty₁ body₁ m₁, .lam ty₂ body₂ m₂ =>
    defeqBinders mode r depth ty₁ body₁ m₁ ty₂ body₂ m₂ true
  | .app _ _, .app _ _ => do
    -- stuck applications: **spine-wise** congruence (official's
    -- `is_def_eq_app`), never a recursion on the partial applications
    let aa ← getAppArgs coreWalkFuel a'
    let bb ← getAppArgs coreWalkFuel b'
    if aa.length = bb.length then do
      let fa ← getAppFn coreWalkFuel a'
      let fb ← getAppFn coreWalkFuel b'
      if ← r.defeq depth fa fb then do
        if ← defEqList r fe depth aa bb then pure true
        else stuckIrrel mode r fe depth a' b'
      else stuckIrrel mode r fe depth a' b'
    else stuckIrrel mode r fe depth a' b'
  | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ => do
    if s₁ == s₂ && i₁ == i₂ then do
      if ← r.defeq depth e₁ e₂ then pure true
      else stuckIrrel mode r fe depth a' b'
    else stuckIrrel mode r fe depth a' b'
  -- one-sided λ: eta, else the stuck fallbacks
  | .lam ty₁ body₁ m₁, _ => do
    if ← etaCert mode r fe depth ty₁ body₁ m₁ b' then pure true
    else stuckIrrel mode r fe depth a' b'
  | _, .lam ty₂ body₂ m₂ => do
    if ← etaCert mode r fe depth ty₂ body₂ m₂ a' then pure true
    else stuckIrrel mode r fe depth a' b'
  -- distinct whnf-stuck head symbols
  | _, _ => stuckIrrel mode r fe depth a' b'

/-- con-leche: ConLeche/Kernel/Core.lean:1526-1578 defeqStep — **the twin's
lazy-delta half**, verbatim, with the congruence half as `dqCongrG`. -/
def dqTailG (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (k : Bool → EIdx → EIdx → AM Bool) (a' b' : EIdx) : AM Bool := do
  let ua ← unfoldableHead fe a'
  let ub ← unfoldableHead fe b'
  match ua, ub with
  | true, false =>
    match ← unfoldDefinition fe a' with
    | some a₂ => k false a₂ b'
    | none => pure false
  | false, true =>
    match ← unfoldDefinition fe b' with
    | some b₂ => k false a' b₂
    | none => pure false
  | true, true => do
    let ha ← headHint fe a'
    let hb ← headHint fe b'
    if ConLeche.ReducibilityHint.lt hb ha then
      match ← unfoldDefinition fe a' with
      | some a₂ => k false a₂ b'
      | none => pure false
    else if ConLeche.ReducibilityHint.lt ha hb then
      match ← unfoldDefinition fe b' with
      | some b₂ => k false a' b₂
      | none => pure false
    else if ConLeche.ReducibilityHint.sameRegular ha hb && (← sameConstHeads a' b') then do
      -- same constant at equal *regular* hints: cheap congruence first
      if ← defeqSpine r fe depth a' b' then pure true
      else
        match ← unfoldDefinition fe a', ← unfoldDefinition fe b' with
        | some a₂, some b₂ => k false a₂ b₂
        | _, _ => pure false
    else
      match ← unfoldDefinition fe a', ← unfoldDefinition fe b' with
      | some a₂, some b₂ => k false a₂ b₂
      | _, _ => pure false
  | false, false => dqCongrG mode r fe depth a' b'


set_option maxHeartbeats 4000000 in
#keeps dqCongrG

/-- `defeqStep` is its entry and literal groups followed by `dqTailG`: the
tail below the second `reduceNat` IS `dqTailG`'s body (`rfl`). -/
theorem defeqStep_eq_tail (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (k : Bool → EIdx → EIdx → AM Bool) (pi : Bool) (a b : EIdx) :
    defeqStep mode r fe depth k pi a b = (do
      if a == b then pure true else do
      let sc ←
        if pi && (← isBoolTrue b) && !(← hasFvarFast coreWalkFuel a) then
          boolTrueShortcut r depth a
        else pure false
      if sc then pure true else do
      let a' ← r.whnfCore depth a
      let b' ← r.whnfCore depth b
      if a' == b' then pure true else do
      let pir ←
        if pi && !(quickPair a' b') then propIrrel r fe depth a' b'
        else pure false
      if pir then pure true else do
      let nf ← defeqNoFvars a' b'
      match ← (if nf then reduceNat r fe depth a' else pure none) with
      | some a₂ => k true a₂ b'
      | none =>
      match ← (if nf then reduceNat r fe depth b' else pure none) with
      | some b₂ => k true a' b₂
      | none => dqTailG mode r fe depth k a' b') := rfl

@[spec] theorem dqTailG_keeps (k : EStore) (p : Pins) {mode r fe depth}
    {kk : Bool → EIdx → EIdx → AM Bool} {a b} (hr : FnsKeep r)
    (hk : ∀ pi a b, ⦃fun s => ⌜Inv k p s⌝⦄ kk pi a b ⦃⇓? _r s => ⌜Inv k p s⌝⦄) :
    ⦃fun s => ⌜Inv k p s⌝⦄ dqTailG mode r fe depth kk a b ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  keeps_step dqTailG

set_option maxHeartbeats 4000000 in
@[spec] theorem defeqStep_keeps (k : EStore) (p : Pins) {mode r fe depth}
    {kk : Bool → EIdx → EIdx → AM Bool} {pi a b} (hr : FnsKeep r)
    (hk : ∀ pi a b, ⦃fun s => ⌜Inv k p s⌝⦄ kk pi a b ⦃⇓? _r s => ⌜Inv k p s⌝⦄) :
    ⦃fun s => ⌜Inv k p s⌝⦄ defeqStep mode r fe depth kk pi a b ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  rw [defeqStep_eq_tail]
  keeps_step

@[spec] theorem defeqLoop_keeps (k : EStore) (p : Pins) {mode r fe depth}
    (n : Nat) (pi : Bool) (a b : EIdx) (hr : FnsKeep r) :
    ⦃fun s => ⌜Inv k p s⌝⦄ defeqLoop mode r fe depth n pi a b ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
  induction n generalizing pi a b with
  | zero => keeps_step defeqLoop
  | succ n ih => exact defeqStep_keeps k p hr ih


#keeps defeqBody

end ConRon.Bridge.Grouping

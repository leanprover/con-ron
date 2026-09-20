/-
# `ConRon.Arena.ExprOps` — the `ExprOps` twins (DESIGN.md §8.6 P2b)

`ConLeche/Kernel/ExprOps.lean`, clause for clause, over handles: 70 (T)
declarations of the census (`Arena/CENSUS.md`, "P2b — the `ExprOps` twins,
with memo"), written in the Rust-shaped style of DESIGN §8.4 — no `for`, no
`mut`, explicit recursion with fuel where con-leche recurses structurally on
`Expr`, detach before update at every mutation, one `def` per intended Rust
function.

## The four rules this module is written by

1. **`view` where con-leche matched, `intern` where it built, handle equality
   where it compared** (§8.3).  A leaf arm that con-leche writes as
   `| .fvar idx ty => .fvar idx ty` is `pure h` here: the node is already in
   the store and `denoteE` is injective, so rebuilding it would be the same
   handle.

2. **Fuel.**  A handle DAG has no structural order the elaborator can see, so
   every walk over the DAG takes an explicit `fuel : Nat` as its FIRST
   argument and `fail`s when it runs out.  Exhaustion is a failure and
   Theorem 1 claims nothing on failure (con-leche's `SimAt` shape), so the
   fuel is invisible above this module.  A recursion that is structural on
   something else — a `Nat` binder count (`stripPis`), a `List` of arguments
   (`mkAppN`), a transient `Level` tree (`internLevel`) — takes no fuel.

3. **The memo lives in the state** (§8.3 "Caches").  con-leche threads it as
   an argument-and-result pair (`instantiate1Go v memo e d`); here it is a
   field of `AState`, keyed `(EIdx, cursor)` as nanoda keys it, and dropped
   at the top-level entry — which is why the substituted term is not in the
   key.  Each `…Fast` entry is con-leche's `(…Go v {} e d).1`: clear, walk,
   clear.

4. **One `def` per constructor arm** for the nine walks that intern
   (task #97s round 2, the elaboration recipe): each arm's `grind` then sees
   that arm's fifteen verification conditions instead of sixty, which is
   10.6 s of elaboration per function instead of 185 s.  Walks that return a
   `Bool`, a `Nat` or a list intern nothing, produce no `Ext` chain, and stay
   single `def`s.

## The cutoffs (§8.3 lesson 20)

Every traversal that con-leche cuts off on a derived field cuts off here on
the same one, read in `O(1)` off the derived column instead of recomputed:

| walk | cutoff | con-leche's licence |
|---|---|---|
| `instantiate1Go` | `bvarBRaw < satRange && bvarBRaw ≤ d` | `bvarBRaw_exact` + task #97s's `instantiate1_of_bvarBound_le` |
| `abstract1Go` | `fvarB ≤ d` | `abstract1_of_fvarRange_le` |
| `lowerBVarsGo` | `bvarB ≤ c + amount` | `lowerBVars_of_bvarBound_le` |
| `instantiate1LiftGo` | `bvarB ≤ d` | `instantiate1Lift_of_bvarBound_le` |
| `instLPGo` | `hasLP = false` | `Expr.instantiateLevelParams_eq_self` |

`instantiate1Go`'s is the one cutoff con-leche does NOT have (its
`instantiate1Go` walks unconditionally); DESIGN §8.3 asks for it by name and
task #97s proved its licence, so the arena takes it.  `instantiateList`,
`liftLooseBVars`, `resetMeta` and `renameConsts` have no cutoff in con-leche
and none here: a cutoff not in the original needs its own pure lemma, and the
two that would earn one (`liftLooseBVars` at `bvarB ≤ c`, `instantiateList`
at `bvarB ≤ d`) are recorded for P2g rather than invented here.

## Levels are read back, not twinned (§8.3 lesson 4)

`instLPGo` is the only twin that touches a level ALGORITHM.  It reads the
substitution's names and levels back out of the store once, at the top-level
entry, runs con-leche's own `Level.subst` / `Level.substPW` on the transient
trees, and re-interns the result.  `Level.hasParam` and `Expr.hasLevelParam`
are not walks at all here: both are exactly the derived bit the store already
carries.
-/
import ConRon.Arena.Monad

namespace ConRon.Arena

open ConLeche

/-! ## `instantiate1` — `ExprOps.lean:29-45`, `:80-116`, `:182-184`

One twin for all three: the pure walk is the specification, `instantiate1Go`
is what executes, and the arena has one function.  Six arms, a memo and the
derived-word cutoff. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:29-45 instantiate1 — the `bvar`
arm.  `else .bvar i` is `pure h`: the node is already interned and `denoteE`
is injective, so rebuilding it yields the same handle. -/
def inst1Bvar (v h : EIdx) (d i : Nat) : AM EIdx :=
  if i = d then pure v
  else if i > d then internE (.bvar (i - 1))
  else pure h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the `app`
arm: probe the memo, recurse into both children, intern, record. -/
def inst1App (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat) (f a : EIdx) :
    AM EIdx := do
  match ← inst1Get (h, d) with
  | some r => pure r
  | none => do
    let f' ← rec f d
    let a' ← rec a d
    let r ← internE (.app f' a')
    inst1Set (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the `lam`
arm; the body's cursor is one deeper. -/
def inst1Lam (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat)
    (ty body : EIdx) (m : BinderMeta) : AM EIdx := do
  match ← inst1Get (h, d) with
  | some r => pure r
  | none => do
    let t ← rec ty d
    let b ← rec body (d + 1)
    let r ← internE (.lam t b m)
    inst1Set (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the
`forallE` arm. -/
def inst1Forall (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat)
    (ty body : EIdx) (m : BinderMeta) : AM EIdx := do
  match ← inst1Get (h, d) with
  | some r => pure r
  | none => do
    let t ← rec ty d
    let b ← rec body (d + 1)
    let r ← internE (.forallE t b m)
    inst1Set (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the `letE`
arm: three children, the body one cursor deeper. -/
def inst1Let (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat)
    (ty val body : EIdx) : AM EIdx := do
  match ← inst1Get (h, d) with
  | some r => pure r
  | none => do
    let t ← rec ty d
    let w ← rec val d
    let b ← rec body (d + 1)
    let r ← internE (.letE t w b)
    inst1Set (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go — the `proj`
arm. -/
def inst1Proj (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat)
    (n : NIdx) (i : Nat) (sub : EIdx) : AM EIdx := do
  match ← inst1Get (h, d) with
  | some r => pure r
  | none => do
    let u ← rec sub d
    let r ← internE (.proj n i u)
    inst1Set (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:29-45 instantiate1
con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go
The dispatcher: the derived-word cutoff (`bvarB ≤ d`, read off the packed
word in `O(1)`), the view, and one call per arm. -/
def instantiate1Go (v : EIdx) : Nat → EIdx → Nat → AM EIdx
  | 0, _, _ => fail (.internal "fuel exhausted: instantiate1")
  | fuel + 1, h, d => do
    let der ← derivedE h
    let b := (bvarOfData der).toNat
    if b < satRange && b ≤ d then
      pure h
    else
      match ← view h with
      | .bvar i => inst1Bvar v h d i
      | .fvar _ _ => pure h
      | .sort _ => pure h
      | .const _ _ => pure h
      | .lit _ => pure h
      | .app f a => inst1App (instantiate1Go v fuel) h d f a
      | .lam ty body m => inst1Lam (instantiate1Go v fuel) h d ty body m
      | .forallE ty body m => inst1Forall (instantiate1Go v fuel) h d ty body m
      | .letE ty val body => inst1Let (instantiate1Go v fuel) h d ty val body
      | .proj n i sub => inst1Proj (instantiate1Go v fuel) h d n i sub

/-- con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast — the
top-level entry: `(instantiate1Go v {} e d).1`, i.e. the memo is fresh before
and dropped after, because it depends on the substituted term. -/
def instantiate1Fast (fuel : Nat) (e v : EIdx) (d : Nat := 0) : AM EIdx := do
  inst1Clear
  let r ← instantiate1Go v fuel e d
  inst1Clear
  pure r

/-! ## `instantiateList` — `ExprOps.lean:191-235`, `:267-303`, `:371-373`

**Two** twins, not one: `instantiateListGo`'s `bvar` arm calls the PURE
`instantiateList` (`ExprOps.lean:288`), because that arm recurses into the
replacement with a *shorter* list and the memo is keyed for the outer one. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList — the
unmemoized bulk instantiation.  con-leche's termination measure is
`(vs.length, sizeOf e)`; the arena's single fuel counter decreases on both
kinds of recursive call, which is the same order flattened. -/
def instantiateList : List EIdx → Nat → EIdx → Nat → AM EIdx
  | _, 0, _, _ => fail (.internal "fuel exhausted: instantiateList")
  | vs, fuel + 1, h, d => do
    match ← view h with
    | .bvar j =>
      if j < d then pure h
      else if hlt : j - d < vs.length then
        instantiateList (vs.take (j - d)) fuel vs[j - d] d
      else internE (.bvar (j - vs.length))
    | .fvar _ _ => pure h
    | .sort _ => pure h
    | .const _ _ => pure h
    | .lit _ => pure h
    | .app f a => do
      let f' ← instantiateList vs fuel f d
      let a' ← instantiateList vs fuel a d
      internE (.app f' a')
    | .lam ty body m => do
      let t ← instantiateList vs fuel ty d
      let b ← instantiateList vs fuel body (d + 1)
      internE (.lam t b m)
    | .forallE ty body m => do
      let t ← instantiateList vs fuel ty d
      let b ← instantiateList vs fuel body (d + 1)
      internE (.forallE t b m)
    | .letE ty val body => do
      let t ← instantiateList vs fuel ty d
      let w ← instantiateList vs fuel val d
      let b ← instantiateList vs fuel body (d + 1)
      internE (.letE t w b)
    | .proj n i sub => do
      let u ← instantiateList vs fuel sub d
      internE (.proj n i u)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
`app` arm. -/
def instLApp (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat) (f a : EIdx) :
    AM EIdx := do
  match ← instLGet (h, d) with
  | some r => pure r
  | none => do
    let f' ← rec f d
    let a' ← rec a d
    let r ← internE (.app f' a')
    instLSet (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
`lam` arm. -/
def instLLam (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat)
    (ty body : EIdx) (m : BinderMeta) : AM EIdx := do
  match ← instLGet (h, d) with
  | some r => pure r
  | none => do
    let t ← rec ty d
    let b ← rec body (d + 1)
    let r ← internE (.lam t b m)
    instLSet (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
`forallE` arm. -/
def instLForall (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat)
    (ty body : EIdx) (m : BinderMeta) : AM EIdx := do
  match ← instLGet (h, d) with
  | some r => pure r
  | none => do
    let t ← rec ty d
    let b ← rec body (d + 1)
    let r ← internE (.forallE t b m)
    instLSet (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
`letE` arm. -/
def instLLet (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat)
    (ty val body : EIdx) : AM EIdx := do
  match ← instLGet (h, d) with
  | some r => pure r
  | none => do
    let t ← rec ty d
    let w ← rec val d
    let b ← rec body (d + 1)
    let r ← internE (.letE t w b)
    instLSet (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
`proj` arm. -/
def instLProj (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat)
    (n : NIdx) (i : Nat) (sub : EIdx) : AM EIdx := do
  match ← instLGet (h, d) with
  | some r => pure r
  | none => do
    let u ← rec sub d
    let r ← internE (.proj n i u)
    instLSet (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
memoized bulk instantiation.  The `bvar` arm delegates to the pure walk
above, exactly as con-leche's does. -/
def instantiateListGo (vs : List EIdx) : Nat → EIdx → Nat → AM EIdx
  | 0, _, _ => fail (.internal "fuel exhausted: instantiateList")
  | fuel + 1, h, d => do
    match ← view h with
    | .bvar _ => instantiateList vs fuel h d
    | .fvar _ _ => pure h
    | .sort _ => pure h
    | .const _ _ => pure h
    | .lit _ => pure h
    | .app f a => instLApp (instantiateListGo vs fuel) h d f a
    | .lam ty body m => instLLam (instantiateListGo vs fuel) h d ty body m
    | .forallE ty body m => instLForall (instantiateListGo vs fuel) h d ty body m
    | .letE ty val body => instLLet (instantiateListGo vs fuel) h d ty val body
    | .proj n i sub => instLProj (instantiateListGo vs fuel) h d n i sub

/-- con-leche: ConLeche/Kernel/ExprOps.lean:371-373 instantiateListFast — the
top-level entry. -/
def instantiateListFast (fuel : Nat) (e : EIdx) (vs : List EIdx) (d : Nat := 0) :
    AM EIdx := do
  instLClear
  let r ← instantiateListGo vs fuel e d
  instLClear
  pure r

/-! ## `liftLooseBVars` — `ExprOps.lean:380-400`, `:430-466`, `:532-534` -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:380-400 liftLooseBVars — the
`bvar` arm. -/
def liftBvar (amount : Nat) (h : EIdx) (c i : Nat) : AM EIdx :=
  if i ≥ c then internE (.bvar (i + amount)) else pure h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo — the
`app` arm. -/
def liftApp (rec : EIdx → Nat → AM EIdx) (h : EIdx) (c : Nat) (a b : EIdx) :
    AM EIdx := do
  match ← liftGet (h, c) with
  | some r => pure r
  | none => do
    let a' ← rec a c
    let b' ← rec b c
    let r ← internE (.app a' b')
    liftSet (h, c) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo — the
`lam` arm. -/
def liftLam (rec : EIdx → Nat → AM EIdx) (h : EIdx) (c : Nat)
    (ty body : EIdx) (m : BinderMeta) : AM EIdx := do
  match ← liftGet (h, c) with
  | some r => pure r
  | none => do
    let t ← rec ty c
    let b ← rec body (c + 1)
    let r ← internE (.lam t b m)
    liftSet (h, c) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo — the
`forallE` arm. -/
def liftForall (rec : EIdx → Nat → AM EIdx) (h : EIdx) (c : Nat)
    (ty body : EIdx) (m : BinderMeta) : AM EIdx := do
  match ← liftGet (h, c) with
  | some r => pure r
  | none => do
    let t ← rec ty c
    let b ← rec body (c + 1)
    let r ← internE (.forallE t b m)
    liftSet (h, c) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo — the
`letE` arm. -/
def liftLet (rec : EIdx → Nat → AM EIdx) (h : EIdx) (c : Nat)
    (ty val body : EIdx) : AM EIdx := do
  match ← liftGet (h, c) with
  | some r => pure r
  | none => do
    let t ← rec ty c
    let w ← rec val c
    let b ← rec body (c + 1)
    let r ← internE (.letE t w b)
    liftSet (h, c) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo — the
`proj` arm. -/
def liftProj (rec : EIdx → Nat → AM EIdx) (h : EIdx) (c : Nat)
    (n : NIdx) (i : Nat) (sub : EIdx) : AM EIdx := do
  match ← liftGet (h, c) with
  | some r => pure r
  | none => do
    let u ← rec sub c
    let r ← internE (.proj n i u)
    liftSet (h, c) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:380-400 liftLooseBVars
con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo
Bump every loose bound variable `≥ cutoff` by `amount`. -/
def liftLooseBVarsGo (amount : Nat) : Nat → EIdx → Nat → AM EIdx
  | 0, _, _ => fail (.internal "fuel exhausted: liftLooseBVars")
  | fuel + 1, h, c => do
    match ← view h with
    | .bvar i => liftBvar amount h c i
    | .fvar _ _ => pure h
    | .sort _ => pure h
    | .const _ _ => pure h
    | .lit _ => pure h
    | .app a b => liftApp (liftLooseBVarsGo amount fuel) h c a b
    | .lam ty body m => liftLam (liftLooseBVarsGo amount fuel) h c ty body m
    | .forallE ty body m => liftForall (liftLooseBVarsGo amount fuel) h c ty body m
    | .letE ty val body => liftLet (liftLooseBVarsGo amount fuel) h c ty val body
    | .proj n i sub => liftProj (liftLooseBVarsGo amount fuel) h c n i sub

/-- con-leche: ConLeche/Kernel/ExprOps.lean:532-534 liftLooseBVarsFast — the
top-level entry. -/
def liftLooseBVarsFast (fuel amount c : Nat) (e : EIdx) : AM EIdx := do
  liftClear
  let r ← liftLooseBVarsGo amount fuel e c
  liftClear
  pure r

/-! ## `resetMeta` — `ExprOps.lean:552-559`, `:579-615`, `:687-688`

The memo has no cursor in con-leche; the arena keys it at `0` so that every
handle-valued memo has one invariant (see `Memos`). -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo — the `fvar`
arm: the annotation is descended into. -/
def resetFvar (rec : EIdx → AM EIdx) (h : EIdx) (i : Nat) (ty : EIdx) : AM EIdx := do
  match ← resetGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← rec ty
    let r ← internE (.fvar i t)
    resetSet (h, 0) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo — the `app`
arm. -/
def resetApp (rec : EIdx → AM EIdx) (h : EIdx) (f a : EIdx) : AM EIdx := do
  match ← resetGet (h, 0) with
  | some r => pure r
  | none => do
    let f' ← rec f
    let a' ← rec a
    let r ← internE (.app f' a')
    resetSet (h, 0) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:552-559 resetMeta — the `lam` arm:
the binder's prop-ness datum is reset to the parse placeholder. -/
def resetLam (rec : EIdx → AM EIdx) (h : EIdx) (ty body : EIdx) : AM EIdx := do
  match ← resetGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← rec ty
    let b ← rec body
    let r ← internE (.lam t b ⟨.never⟩)
    resetSet (h, 0) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:552-559 resetMeta — the `forallE`
arm. -/
def resetForall (rec : EIdx → AM EIdx) (h : EIdx) (ty body : EIdx) : AM EIdx := do
  match ← resetGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← rec ty
    let b ← rec body
    let r ← internE (.forallE t b ⟨.never⟩)
    resetSet (h, 0) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo — the `letE`
arm. -/
def resetLet (rec : EIdx → AM EIdx) (h : EIdx) (ty val body : EIdx) : AM EIdx := do
  match ← resetGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← rec ty
    let w ← rec val
    let b ← rec body
    let r ← internE (.letE t w b)
    resetSet (h, 0) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo — the `proj`
arm. -/
def resetProj (rec : EIdx → AM EIdx) (h : EIdx) (n : NIdx) (i : Nat)
    (sub : EIdx) : AM EIdx := do
  match ← resetGet (h, 0) with
  | some r => pure r
  | none => do
    let u ← rec sub
    let r ← internE (.proj n i u)
    resetSet (h, 0) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:552-559 resetMeta
con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo
Reset every binder's prop-ness datum to the parse placeholder. -/
def resetMetaGo : Nat → EIdx → AM EIdx
  | 0, _ => fail (.internal "fuel exhausted: resetMeta")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ => pure h
    | .sort _ => pure h
    | .const _ _ => pure h
    | .lit _ => pure h
    | .fvar i ty => resetFvar (resetMetaGo fuel) h i ty
    | .app f a => resetApp (resetMetaGo fuel) h f a
    | .lam ty body _ => resetLam (resetMetaGo fuel) h ty body
    | .forallE ty body _ => resetForall (resetMetaGo fuel) h ty body
    | .letE ty val body => resetLet (resetMetaGo fuel) h ty val body
    | .proj n i sub => resetProj (resetMetaGo fuel) h n i sub

/-- con-leche: ConLeche/Kernel/ExprOps.lean:687-688 resetMetaFast — the
top-level entry. -/
def resetMetaFast (fuel : Nat) (e : EIdx) : AM EIdx := do
  resetClear
  let r ← resetMetaGo fuel e
  resetClear
  pure r

/-! ## The measures and the scope predicates -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:741-748 sizeB — node count with
`fvar` a leaf (its annotated type ignored): the termination measure for
recursion into instantiated binder bodies.  A `Nat`-valued walk interns
nothing, so it is one `def` and not six. -/
def sizeB : Nat → EIdx → AM Nat
  | 0, _ => fail (.internal "fuel exhausted: sizeB")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lit _ => pure 1
    | .app f a => do
      let x ← sizeB fuel f
      let y ← sizeB fuel a
      pure (x + y + 1)
    | .lam ty body _ | .forallE ty body _ => do
      let x ← sizeB fuel ty
      let y ← sizeB fuel body
      pure (x + y + 1)
    | .letE ty val body => do
      let x ← sizeB fuel ty
      let y ← sizeB fuel val
      let z ← sizeB fuel body
      pure (x + y + z + 1)
    | .proj _ _ sub => do
      let x ← sizeB fuel sub
      pure (x + 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:778-808 abstractRange — bulk
abstraction: close `k` binders in one traversal.  Unmemoized in con-leche and
unmemoized here. -/
def abstractRange : Nat → EIdx → Nat → Nat → Nat → AM EIdx
  | 0, _, _, _, _ => fail (.internal "fuel exhausted: abstractRange")
  | fuel + 1, h, d, k, c => do
    match ← view h with
    | .bvar _ => pure h
    | .fvar idx _ =>
      if d ≤ idx ∧ idx < d + k then internE (.bvar (c + (d + k - 1 - idx)))
      else pure h
    | .sort _ => pure h
    | .const _ _ => pure h
    | .lit _ => pure h
    | .app f a => do
      let f' ← abstractRange fuel f d k c
      let a' ← abstractRange fuel a d k c
      internE (.app f' a')
    | .lam ty body m => do
      let t ← abstractRange fuel ty d k c
      let b ← abstractRange fuel body d k (c + 1)
      internE (.lam t b m)
    | .forallE ty body m => do
      let t ← abstractRange fuel ty d k c
      let b ← abstractRange fuel body d k (c + 1)
      internE (.forallE t b m)
    | .letE ty val body => do
      let t ← abstractRange fuel ty d k c
      let w ← abstractRange fuel val d k c
      let b ← abstractRange fuel body d k (c + 1)
      internE (.letE t w b)
    | .proj n i sub => do
      let u ← abstractRange fuel sub d k c
      internE (.proj n i u)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:810-819 sizeF — full node count,
`fvar` annotations included. -/
def sizeF : Nat → EIdx → AM Nat
  | 0, _ => fail (.internal "fuel exhausted: sizeF")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ | .sort _ | .const _ _ | .lit _ => pure 1
    | .fvar _ ty => do
      let x ← sizeF fuel ty
      pure (x + 1)
    | .app f a => do
      let x ← sizeF fuel f
      let y ← sizeF fuel a
      pure (x + y + 1)
    | .lam ty body _ | .forallE ty body _ => do
      let x ← sizeF fuel ty
      let y ← sizeF fuel body
      pure (x + y + 1)
    | .letE ty val body => do
      let x ← sizeF fuel ty
      let y ← sizeF fuel val
      let z ← sizeF fuel body
      pure (x + y + z + 1)
    | .proj _ _ sub => do
      let x ← sizeF fuel sub
      pure (x + 1)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:821-833 fvarLeaves — all reachable
`fvar` leaves, hereditarily through their annotations. -/
def fvarLeaves : Nat → EIdx → AM (List (Nat × EIdx))
  | 0, _ => fail (.internal "fuel exhausted: fvarLeaves")
  | fuel + 1, h => do
    match ← view h with
    | .fvar idx ty => do
      let rest ← fvarLeaves fuel ty
      pure ((idx, ty) :: rest)
    | .app f a => do
      let x ← fvarLeaves fuel f
      let y ← fvarLeaves fuel a
      pure (x ++ y)
    | .lam ty b _ | .forallE ty b _ => do
      let x ← fvarLeaves fuel ty
      let y ← fvarLeaves fuel b
      pure (x ++ y)
    | .letE t v b => do
      let x ← fvarLeaves fuel t
      let y ← fvarLeaves fuel v
      let z ← fvarLeaves fuel b
      pure (x ++ y ++ z)
    | .proj _ _ sub => fvarLeaves fuel sub
    | .bvar _ | .sort _ | .const _ _ | .lit _ => pure []

/-- con-leche: ConLeche/Kernel/ExprOps.lean:835-861 wscopedB — the scope
check: every reachable `fvar` index is below `d`, hereditarily through
annotations.  con-leche's `&&` is short-circuiting, and so is the explicit
`if` chain here. -/
def wscopedB : Nat → Nat → EIdx → AM Bool
  | 0, _, _ => fail (.internal "fuel exhausted: wscopedB")
  | fuel + 1, d, h => do
    match ← view h with
    | .fvar idx ty =>
      if idx < d then wscopedB fuel idx ty else pure false
    | .app f a => do
      let x ← wscopedB fuel d f
      if x then wscopedB fuel d a else pure false
    | .lam ty body _ => do
      let x ← wscopedB fuel d ty
      if x then wscopedB fuel d body else pure false
    | .forallE ty body _ => do
      let x ← wscopedB fuel d ty
      if x then wscopedB fuel d body else pure false
    | .letE ty val body => do
      let x ← wscopedB fuel d ty
      if x then
        let y ← wscopedB fuel d val
        if y then wscopedB fuel d body else pure false
      else pure false
    | .proj _ _ sub => wscopedB fuel d sub
    | .bvar _ | .sort _ | .const _ _ | .lit _ => pure true

/-- con-leche: ConLeche/Kernel/ExprOps.lean:863-877 looseBVarsBounded — the
pure walk.  It is the SPECIFICATION; what executes is the `O(1)` field read
`looseBVarsBoundedFast` below, exactly as in con-leche (the `@[csimp]`
pair). -/
def looseBVarsBounded : Nat → Nat → EIdx → AM Bool
  | 0, _, _ => fail (.internal "fuel exhausted: looseBVarsBounded")
  | fuel + 1, k, h => do
    match ← view h with
    | .bvar i => pure (i < k)
    | .fvar _ _ => pure true
    | .sort _ | .const _ _ | .lit _ => pure true
    | .app f a => do
      let x ← looseBVarsBounded fuel k f
      if x then looseBVarsBounded fuel k a else pure false
    | .lam ty body _ | .forallE ty body _ => do
      let x ← looseBVarsBounded fuel k ty
      if x then looseBVarsBounded fuel (k + 1) body else pure false
    | .letE ty val body => do
      let x ← looseBVarsBounded fuel k ty
      if x then
        let y ← looseBVarsBounded fuel k val
        if y then looseBVarsBounded fuel (k + 1) body else pure false
      else pure false
    | .proj _ _ sub => looseBVarsBounded fuel k sub

/-! ## The one-node readers

Each is a single `view` and a test: no recursion, no fuel. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:879-885 isLam — is the expression
a λ? -/
def isLam (h : EIdx) : AM Bool := do
  match ← view h with
  | .lam _ _ _ => pure true
  | _ => pure false

/-- con-leche: ConLeche/Kernel/ExprOps.lean:887-894 lamPw — a λ node's
prop-ness annotation, `none` off λs.  `PropWhen` is a value and not a term,
so it crosses the signature unchanged. -/
def lamPw (h : EIdx) : AM (Option PropWhen) := do
  match ← view h with
  | .lam _ _ m => pure (some m.pw)
  | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:896-902 forallPw — the ∀ twin of
`lamPw`. -/
def forallPw (h : EIdx) : AM (Option PropWhen) := do
  match ← view h with
  | .forallE _ _ m => pure (some m.pw)
  | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:904-913 hasFvar — the pure walk;
what executes is `hasFvarFast` below (the fvar-range field read). -/
def hasFvar : Nat → EIdx → AM Bool
  | 0, _ => fail (.internal "fuel exhausted: hasFvar")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ | .sort _ | .const _ _ | .lit _ => pure false
    | .fvar _ _ => pure true
    | .app f a => do
      let x ← hasFvar fuel f
      if x then pure true else hasFvar fuel a
    | .lam ty body _ | .forallE ty body _ => do
      let x ← hasFvar fuel ty
      if x then pure true else hasFvar fuel body
    | .letE ty val body => do
      let x ← hasFvar fuel ty
      if x then pure true else do
        let y ← hasFvar fuel val
        if y then pure true else hasFvar fuel body
    | .proj _ _ sub => hasFvar fuel sub

/-! ## Application spines -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:915-918 getAppFn — the head of an
application spine. -/
def getAppFn : Nat → EIdx → AM EIdx
  | 0, _ => fail (.internal "fuel exhausted: getAppFn")
  | fuel + 1, h => do
    match ← view h with
    | .app f _ => getAppFn fuel f
    | _ => pure h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:920-923 getAppArgs — the arguments
of an application spine, outermost last. -/
def getAppArgs : Nat → EIdx → AM (List EIdx)
  | 0, _ => fail (.internal "fuel exhausted: getAppArgs")
  | fuel + 1, h => do
    match ← view h with
    | .app f a => do
      let as ← getAppArgs fuel f
      pure (as ++ [a])
    | _ => pure []

/-- con-leche: ConLeche/Kernel/ExprOps.lean:925-928 mkAppN — apply to a list
of arguments.  Structural on the list, so no fuel. -/
def mkAppN (f : EIdx) : List EIdx → AM EIdx
  | [] => pure f
  | a :: as => do
    let g ← internE (.app f a)
    mkAppN g as

/-! ## `renameConsts` — `ExprOps.lean:930-956`, `:999-1036`, `:1109-1111`

The renaming is a function on NAME HANDLES, not on names: the census's
mechanical column says so, and it is what the call site (the modeled-block
contract, which compares a block's types against their `_model` counterparts)
can supply — the bridge's obligation is that the handle map denotes
con-leche's name map. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:999-1036 renameConstsGo — the
`fvar` arm: the annotation is descended into. -/
def renameFvar (rec : EIdx → AM EIdx) (h : EIdx) (i : Nat) (ty : EIdx) : AM EIdx := do
  match ← renameGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← rec ty
    let r ← internE (.fvar i t)
    renameSet (h, 0) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:999-1036 renameConstsGo — the
`app` arm. -/
def renameApp (rec : EIdx → AM EIdx) (h : EIdx) (a b : EIdx) : AM EIdx := do
  match ← renameGet (h, 0) with
  | some r => pure r
  | none => do
    let a' ← rec a
    let b' ← rec b
    let r ← internE (.app a' b')
    renameSet (h, 0) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:999-1036 renameConstsGo — the
`lam` arm. -/
def renameLam (rec : EIdx → AM EIdx) (h : EIdx) (ty body : EIdx)
    (m : BinderMeta) : AM EIdx := do
  match ← renameGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← rec ty
    let b ← rec body
    let r ← internE (.lam t b m)
    renameSet (h, 0) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:999-1036 renameConstsGo — the
`forallE` arm. -/
def renameForall (rec : EIdx → AM EIdx) (h : EIdx) (ty body : EIdx)
    (m : BinderMeta) : AM EIdx := do
  match ← renameGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← rec ty
    let b ← rec body
    let r ← internE (.forallE t b m)
    renameSet (h, 0) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:999-1036 renameConstsGo — the
`letE` arm. -/
def renameLet (rec : EIdx → AM EIdx) (h : EIdx) (ty val body : EIdx) : AM EIdx := do
  match ← renameGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← rec ty
    let w ← rec val
    let b ← rec body
    let r ← internE (.letE t w b)
    renameSet (h, 0) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:999-1036 renameConstsGo — the
`proj` arm.  Task #175 wiring W5: a `.proj` node's struct name is NOT
renamed. -/
def renameProj (rec : EIdx → AM EIdx) (h : EIdx) (n : NIdx) (i : Nat)
    (sub : EIdx) : AM EIdx := do
  match ← renameGet (h, 0) with
  | some r => pure r
  | none => do
    let u ← rec sub
    let r ← internE (.proj n i u)
    renameSet (h, 0) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:930-956 renameConsts
con-leche: ConLeche/Kernel/ExprOps.lean:999-1036 renameConstsGo
Rename constants throughout; levels, binders and `proj` struct names
untouched.  The `const` arm is a leaf here as it is in con-leche (it rebuilds
one node and does not recurse), so it is not memoized. -/
def renameConstsGo (f : NIdx → NIdx) : Nat → EIdx → AM EIdx
  | 0, _ => fail (.internal "fuel exhausted: renameConsts")
  | fuel + 1, h => do
    match ← view h with
    | .bvar _ => pure h
    | .sort _ => pure h
    | .lit _ => pure h
    | .const n us => internE (.const (f n) us)
    | .fvar i ty => renameFvar (renameConstsGo f fuel) h i ty
    | .app a b => renameApp (renameConstsGo f fuel) h a b
    | .lam ty body m => renameLam (renameConstsGo f fuel) h ty body m
    | .forallE ty body m => renameForall (renameConstsGo f fuel) h ty body m
    | .letE ty val body => renameLet (renameConstsGo f fuel) h ty val body
    | .proj n i sub => renameProj (renameConstsGo f fuel) h n i sub

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1109-1111 renameConstsFast — the
top-level entry. -/
def renameConstsFast (fuel : Nat) (f : NIdx → NIdx) (e : EIdx) : AM EIdx := do
  renameClear
  let r ← renameConstsGo f fuel e
  renameClear
  pure r

/-! ## Telescopes -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1118-1124 stripLams — strip `k`
leading λs.  The recursion is structural on `k`, so no fuel. -/
def stripLams : Nat → EIdx → AM (Option (List (EIdx × BinderMeta) × EIdx))
  | 0, h => pure (some ([], h))
  | k + 1, h => do
    match ← view h with
    | .lam ty b m => do
      let r ← stripLams k b
      pure (r.map fun p => ((ty, m) :: p.1, p.2))
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1126-1132 stripPis — strip `k`
leading `∀`s. -/
def stripPis : Nat → EIdx → AM (Option (List (EIdx × BinderMeta) × EIdx))
  | 0, h => pure (some ([], h))
  | k + 1, h => do
    match ← view h with
    | .forallE ty b m => do
      let r ← stripPis k b
      pure (r.map fun p => ((ty, m) :: p.1, p.2))
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1134-1138 piResult — the body of a
syntactic `∀`-telescope. -/
def piResult : Nat → EIdx → AM EIdx
  | 0, _ => fail (.internal "fuel exhausted: piResult")
  | fuel + 1, h => do
    match ← view h with
    | .forallE _ b _ => piResult fuel b
    | _ => pure h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1140-1144 instPis — instantiate a
`∀`-telescope with arguments, in order.  Structural on the argument list; the
fuel is the one `instantiate1Fast` needs. -/
def instPis (fuel : Nat) : EIdx → List EIdx → AM (Option EIdx)
  | e, [] => pure (some e)
  | h, a :: as => do
    match ← view h with
    | .forallE _ body _ => do
      let b ← instantiate1Fast fuel body a 0
      instPis fuel b as
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1146-1154 instPisAt — instantiate
the leading `∀`-binders at the given arguments, returning each binder's
domain with the fully instantiated residual.  con-leche's `Option.map` over a
pure body becomes an explicit `match`: the body is monadic here. -/
def instPisAt (fuel : Nat) : List EIdx → EIdx → AM (Option (List EIdx × EIdx))
  | [], e => pure (some ([], e))
  | a :: as, h => do
    match ← view h with
    | .forallE dom body _ => do
      let b ← instantiate1Fast fuel body a 0
      match ← instPisAt fuel as b with
      | some p => pure (some (dom :: p.1, p.2))
      | none => pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1156-1162 instLamsAt — `instPisAt`
for λ-binders. -/
def instLamsAt (fuel : Nat) : List EIdx → EIdx → AM (Option (List EIdx × EIdx))
  | [], e => pure (some ([], e))
  | a :: as, h => do
    match ← view h with
    | .lam dom body _ => do
      let b ← instantiate1Fast fuel body a 0
      match ← instLamsAt fuel as b with
      | some p => pure (some (dom :: p.1, p.2))
      | none => pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1179-1188 instPisAtFGo — the core
of `instPisAtF`: `acc` holds the pending substitutions, innermost binder
first. -/
def instPisAtFGo (fuel : Nat) :
    List EIdx → List EIdx → EIdx → AM (Option (List EIdx × EIdx))
  | acc, [], e => do
    let r ← instantiateListFast fuel e acc 0
    pure (some ([], r))
  | acc, a :: as, h => do
    match ← view h with
    | .forallE dom body _ => do
      match ← instPisAtFGo fuel (a :: acc) as body with
      | some p => do
        let d ← instantiateListFast fuel dom acc 0
        pure (some (d :: p.1, p.2))
      | none => pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1190-1194 instPisAtF — one-pass
`instPisAt`. -/
def instPisAtF (fuel : Nat) (args : List EIdx) (e : EIdx) :
    AM (Option (List EIdx × EIdx)) := do
  match ← instPisAtFGo fuel [] args e with
  | some r => pure (some r)
  | none => instPisAt fuel args e

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1196-1202 instLamsAtFGo — the λ
counterpart of `instPisAtFGo`. -/
def instLamsAtFGo (fuel : Nat) :
    List EIdx → List EIdx → EIdx → AM (Option (List EIdx × EIdx))
  | acc, [], e => do
    let r ← instantiateListFast fuel e acc 0
    pure (some ([], r))
  | acc, a :: as, h => do
    match ← view h with
    | .lam dom body _ => do
      match ← instLamsAtFGo fuel (a :: acc) as body with
      | some p => do
        let d ← instantiateListFast fuel dom acc 0
        pure (some (d :: p.1, p.2))
      | none => pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1204-1208 instLamsAtF — one-pass
`instLamsAt`. -/
def instLamsAtF (fuel : Nat) (args : List EIdx) (e : EIdx) :
    AM (Option (List EIdx × EIdx)) := do
  match ← instLamsAtFGo fuel [] args e with
  | some r => pure (some r)
  | none => instLamsAt fuel args e

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1210-1215 fvarTypeD — the type
annotation of a free-variable leaf (the expression itself otherwise). -/
def fvarTypeD (h : EIdx) : AM EIdx := do
  match ← view h with
  | .fvar _ ty => pure ty
  | _ => pure h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1217-1225 instSpine — instantiate
a telescope-context expression at an argument spine. -/
def instSpine (fuel : Nat) : List EIdx → Nat → EIdx → AM EIdx
  | [], _, e => pure e
  | a :: as, t, e => do
    let e' ← instantiate1Fast fuel e a t
    instSpine fuel as (t - 1) e'

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1227-1242 recRulePlain — the
comparand `(List.range cnP).map (fun k => Expr.bvar (mI - 1 - k))`, interned.
Structural on the count, so no fuel. -/
def bvarRange (mI : Nat) : Nat → Nat → AM (List EIdx)
  | 0, _ => pure []
  | n + 1, k => do
    let b ← internE (.bvar (mI - 1 - k))
    let rest ← bvarRange mI n (k + 1)
    pure (b :: rest)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1227-1242 recRulePlain — a
recursor rule is canonical when its constructor's parameters are exactly the
recursor's own leading arguments.  The `==` on the argument prefix is index
equality (the `==` inventory's line 1240): exactness makes it the structural
comparison con-leche writes. -/
def recRulePlain (fuel : Nat) (recTy : EIdx) (mI rP cnP : Nat) : AM Bool := do
  if !(decide (cnP ≤ rP) && decide (rP ≤ mI)) then
    pure false
  else
    match ← stripPis mI recTy with
    | some p => do
      match ← view p.2 with
      | .forallE dom _ _ => do
        let args ← getAppArgs fuel dom
        let want ← bvarRange mI cnP 0
        pure (args.take cnP == want)
      | _ => pure false
    | none => pure false

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1244-1259 pisToLams — convert the
first `k` `∀`-binders into λ-binders over a body; the copied binder metadata
keeps only the display info, so the result carries the parse placeholder and
every consumer must annotate it. -/
def pisToLams : Nat → EIdx → EIdx → AM (Option EIdx)
  | 0, _, body => pure (some body)
  | k + 1, h, body => do
    match ← view h with
    | .forallE ty rest _ => do
      match ← pisToLams k rest body with
      | some b => do
        let r ← internE (.lam ty b ⟨.never⟩)
        pure (some r)
      | none => pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1261-1267 replacePiBody — replace
the body under the first `k` `∀`-binders, domains and prop-ness data kept. -/
def replacePiBody : Nat → EIdx → EIdx → AM (Option EIdx)
  | 0, _, b => pure (some b)
  | k + 1, h, b => do
    match ← view h with
    | .forallE ty rest m => do
      match ← replacePiBody k rest b with
      | some r => do
        let x ← internE (.forallE ty r ⟨m.pw⟩)
        pure (some x)
      | none => pure none
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1269-1272 piArity — the length of
the leading `∀`-telescope. -/
def piArity : Nat → EIdx → AM Nat
  | 0, _ => fail (.internal "fuel exhausted: piArity")
  | fuel + 1, h => do
    match ← view h with
    | .forallE _ b _ => do
      let n ← piArity fuel b
      pure (n + 1)
    | _ => pure 0

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1274-1278 resultSort — the result
sort at the end of a `∀`-telescope. -/
def resultSort : Nat → EIdx → AM (Option LIdx)
  | 0, _ => fail (.internal "fuel exhausted: resultSort")
  | fuel + 1, h => do
    match ← view h with
    | .forallE _ b _ => resultSort fuel b
    | .sort u => pure (some u)
    | _ => pure none

/-! ## The packed range fields and their saturated-branch recomputations

`ExprOps.lean:1293-1303`, `:1312-1323`, `:1368-1425`, `:1427-1439`.  The
arena reads both ranges in `O(1)` off the derived column; only on the
saturated branch (a bound at or above `satRange = 32767`) does it walk, and
that walk is memoized exactly as con-leche's is. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1293-1303 Expr.bvarBound
con-leche: ConLeche/Kernel/ExprOps.lean:1368-1392 bvarBoundGo
The memoized exact loose-bvar bound.  con-leche's `bvarBound` is the pure
specification and `bvarBoundGo` the memoized walk; the arena has one
function.  The memo is probed for every node, leaves included, as con-leche
probes it. -/
def bvarBoundGo : Nat → EIdx → AM Nat
  | 0, _ => fail (.internal "fuel exhausted: bvarBound")
  | fuel + 1, h => do
    match ← bvarBGet h with
    | some r => pure r
    | none => do
      let r ← (do
        match ← view h with
        | .bvar i => pure (i + 1)
        | .fvar _ _ | .sort _ | .const _ _ | .lit _ => pure 0
        | .app f a => do
          let x ← bvarBoundGo fuel f
          let y ← bvarBoundGo fuel a
          pure (max x y)
        | .lam ty body _ | .forallE ty body _ => do
          let x ← bvarBoundGo fuel ty
          let y ← bvarBoundGo fuel body
          pure (max x (y - 1))
        | .letE ty val body => do
          let x ← bvarBoundGo fuel ty
          let y ← bvarBoundGo fuel val
          let z ← bvarBoundGo fuel body
          pure (max (max x y) (z - 1))
        | .proj _ _ sub => bvarBoundGo fuel sub)
      bvarBSet h r
      pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1394-1395 bvarBoundMemo — the
top-level entry of the memoized walk. -/
def bvarBoundMemo (fuel : Nat) (e : EIdx) : AM Nat := do
  bvarBClear
  let r ← bvarBoundGo fuel e
  bvarBClear
  pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1312-1323 Expr.fvarRange
con-leche: ConLeche/Kernel/ExprOps.lean:1397-1422 fvarRangeGo
The memoized exact fvar range (`fvar` annotations are not descended into,
matching the abstraction traversals). -/
def fvarRangeGo : Nat → EIdx → AM Nat
  | 0, _ => fail (.internal "fuel exhausted: fvarRange")
  | fuel + 1, h => do
    match ← fvarBGet h with
    | some r => pure r
    | none => do
      let r ← (do
        match ← view h with
        | .fvar idx _ => pure (idx + 1)
        | .bvar _ | .sort _ | .const _ _ | .lit _ => pure 0
        | .app f a => do
          let x ← fvarRangeGo fuel f
          let y ← fvarRangeGo fuel a
          pure (max x y)
        | .lam ty body _ | .forallE ty body _ => do
          let x ← fvarRangeGo fuel ty
          let y ← fvarRangeGo fuel body
          pure (max x y)
        | .letE ty val body => do
          let x ← fvarRangeGo fuel ty
          let y ← fvarRangeGo fuel val
          let z ← fvarRangeGo fuel body
          pure (max (max x y) z)
        | .proj _ _ sub => fvarRangeGo fuel sub)
      fvarBSet h r
      pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1424-1425 fvarRangeMemo — the
top-level entry of the memoized walk. -/
def fvarRangeMemo (fuel : Nat) (e : EIdx) : AM Nat := do
  fvarBClear
  let r ← fvarRangeGo fuel e
  fvarBClear
  pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1427-1432 bvarB — **the
loose-bvar bound the checker reads**: the packed field, or — on the saturated
branch alone — the exact memoized recomputation.  `==` on `Nat`, so the
`==` inventory's line 1432 is not a handle comparison. -/
def bvarB (fuel : Nat) (e : EIdx) : AM Nat := do
  let der ← derivedE e
  let r := (bvarOfData der).toNat
  if r == satRange then bvarBoundMemo fuel e else pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1434-1439 fvarB — **the fvar range
the checker reads**: the packed field, or the exact memoized recomputation on
the saturated branch. -/
def fvarB (fuel : Nat) (e : EIdx) : AM Nat := do
  let der ← derivedE e
  let r := (fvarOfData der).toNat
  if r == satRange then fvarRangeMemo fuel e else pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1707-1708 hasFvarFast — the
executed `hasFvar`: the fvar-range field read. -/
def hasFvarFast (fuel : Nat) (e : EIdx) : AM Bool := do
  let r ← fvarB fuel e
  pure (r != 0)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1716-1717 looseBVarsBoundedFast —
the executed `looseBVarsBounded`: the loose-bvar field read. -/
def looseBVarsBoundedFast (fuel k : Nat) (e : EIdx) : AM Bool := do
  let r ← bvarB fuel e
  pure (decide (r ≤ k))

/-! ## `abstract1` — `ExprOps.lean:760-776`, `:1789-1833`, `:1927-1929`

The fvar-range cutoff comes first: a node whose whole subtree mentions no
`fvar` at or above `d` is its own abstraction. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1789-1833 abstract1Go — the `app`
arm. -/
def abs1App (rec : EIdx → Nat → AM EIdx) (h : EIdx) (k : Nat) (f a : EIdx) :
    AM EIdx := do
  match ← abs1Get (h, k) with
  | some r => pure r
  | none => do
    let f' ← rec f k
    let a' ← rec a k
    let r ← internE (.app f' a')
    abs1Set (h, k) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1789-1833 abstract1Go — the `lam`
arm; the abstraction target moves one binder deeper in the body. -/
def abs1Lam (rec : EIdx → Nat → AM EIdx) (h : EIdx) (k : Nat)
    (ty body : EIdx) (m : BinderMeta) : AM EIdx := do
  match ← abs1Get (h, k) with
  | some r => pure r
  | none => do
    let t ← rec ty k
    let b ← rec body (k + 1)
    let r ← internE (.lam t b m)
    abs1Set (h, k) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1789-1833 abstract1Go — the
`forallE` arm. -/
def abs1Forall (rec : EIdx → Nat → AM EIdx) (h : EIdx) (k : Nat)
    (ty body : EIdx) (m : BinderMeta) : AM EIdx := do
  match ← abs1Get (h, k) with
  | some r => pure r
  | none => do
    let t ← rec ty k
    let b ← rec body (k + 1)
    let r ← internE (.forallE t b m)
    abs1Set (h, k) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1789-1833 abstract1Go — the `letE`
arm. -/
def abs1Let (rec : EIdx → Nat → AM EIdx) (h : EIdx) (k : Nat)
    (ty val body : EIdx) : AM EIdx := do
  match ← abs1Get (h, k) with
  | some r => pure r
  | none => do
    let t ← rec ty k
    let w ← rec val k
    let b ← rec body (k + 1)
    let r ← internE (.letE t w b)
    abs1Set (h, k) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1789-1833 abstract1Go — the `proj`
arm. -/
def abs1Proj (rec : EIdx → Nat → AM EIdx) (h : EIdx) (k : Nat)
    (n : NIdx) (i : Nat) (sub : EIdx) : AM EIdx := do
  match ← abs1Get (h, k) with
  | some r => pure r
  | none => do
    let u ← rec sub k
    let r ← internE (.proj n i u)
    abs1Set (h, k) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:760-776 abstract1
con-leche: ConLeche/Kernel/ExprOps.lean:1789-1833 abstract1Go
Close a binder body: replace `fvar d …` leaves by `bvar k`, bumping `k` under
binders.  `fvar` annotations are not descended into. -/
def abstract1Go (d : Nat) : Nat → EIdx → Nat → AM EIdx
  | 0, _, _ => fail (.internal "fuel exhausted: abstract1")
  | fuel + 1, h, k => do
    let fb ← fvarB fuel h
    if fb ≤ d then
      pure h
    else
      match ← view h with
      | .bvar _ => pure h
      | .fvar idx _ => if idx = d then internE (.bvar k) else pure h
      | .sort _ => pure h
      | .const _ _ => pure h
      | .lit _ => pure h
      | .app f a => abs1App (abstract1Go d fuel) h k f a
      | .lam ty body m => abs1Lam (abstract1Go d fuel) h k ty body m
      | .forallE ty body m => abs1Forall (abstract1Go d fuel) h k ty body m
      | .letE ty val body => abs1Let (abstract1Go d fuel) h k ty val body
      | .proj n i sub => abs1Proj (abstract1Go d fuel) h k n i sub

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1927-1929 abstract1Fast — the
top-level entry. -/
def abstract1Fast (fuel : Nat) (e : EIdx) (d : Nat) (k : Nat := 0) : AM EIdx := do
  abs1Clear
  let r ← abstract1Go d fuel e k
  abs1Clear
  pure r

/-! ## `lowerBVars` — `ExprOps.lean:694-716`, `:2012-2049`, `:2144-2146` -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:694-716 lowerBVars — the `bvar`
arm. -/
def lowerBvar (amount : Nat) (h : EIdx) (c i : Nat) : AM EIdx :=
  if i ≥ c + amount then internE (.bvar (i - amount)) else pure h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2012-2049 lowerBVarsGo — the `app`
arm. -/
def lowerApp (rec : EIdx → Nat → AM EIdx) (h : EIdx) (c : Nat) (f a : EIdx) :
    AM EIdx := do
  match ← lowerGet (h, c) with
  | some r => pure r
  | none => do
    let f' ← rec f c
    let a' ← rec a c
    let r ← internE (.app f' a')
    lowerSet (h, c) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2012-2049 lowerBVarsGo — the `lam`
arm. -/
def lowerLam (rec : EIdx → Nat → AM EIdx) (h : EIdx) (c : Nat)
    (ty body : EIdx) (m : BinderMeta) : AM EIdx := do
  match ← lowerGet (h, c) with
  | some r => pure r
  | none => do
    let t ← rec ty c
    let b ← rec body (c + 1)
    let r ← internE (.lam t b m)
    lowerSet (h, c) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2012-2049 lowerBVarsGo — the
`forallE` arm. -/
def lowerForall (rec : EIdx → Nat → AM EIdx) (h : EIdx) (c : Nat)
    (ty body : EIdx) (m : BinderMeta) : AM EIdx := do
  match ← lowerGet (h, c) with
  | some r => pure r
  | none => do
    let t ← rec ty c
    let b ← rec body (c + 1)
    let r ← internE (.forallE t b m)
    lowerSet (h, c) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2012-2049 lowerBVarsGo — the
`letE` arm. -/
def lowerLet (rec : EIdx → Nat → AM EIdx) (h : EIdx) (c : Nat)
    (ty val body : EIdx) : AM EIdx := do
  match ← lowerGet (h, c) with
  | some r => pure r
  | none => do
    let t ← rec ty c
    let w ← rec val c
    let b ← rec body (c + 1)
    let r ← internE (.letE t w b)
    lowerSet (h, c) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2012-2049 lowerBVarsGo — the
`proj` arm. -/
def lowerProj (rec : EIdx → Nat → AM EIdx) (h : EIdx) (c : Nat)
    (n : NIdx) (i : Nat) (sub : EIdx) : AM EIdx := do
  match ← lowerGet (h, c) with
  | some r => pure r
  | none => do
    let u ← rec sub c
    let r ← internE (.proj n i u)
    lowerSet (h, c) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:694-716 lowerBVars
con-leche: ConLeche/Kernel/ExprOps.lean:2012-2049 lowerBVarsGo
Lower every loose bound variable `≥ cutoff + amount` by `amount`, with
con-leche's own `bvarB ≤ c + amount` cutoff. -/
def lowerBVarsGo (amount : Nat) : Nat → EIdx → Nat → AM EIdx
  | 0, _, _ => fail (.internal "fuel exhausted: lowerBVars")
  | fuel + 1, h, c => do
    let bb ← bvarB fuel h
    if bb ≤ c + amount then
      pure h
    else
      match ← view h with
      | .bvar i => lowerBvar amount h c i
      | .fvar _ _ => pure h
      | .sort _ => pure h
      | .const _ _ => pure h
      | .lit _ => pure h
      | .app f a => lowerApp (lowerBVarsGo amount fuel) h c f a
      | .lam ty body m => lowerLam (lowerBVarsGo amount fuel) h c ty body m
      | .forallE ty body m => lowerForall (lowerBVarsGo amount fuel) h c ty body m
      | .letE ty val body => lowerLet (lowerBVarsGo amount fuel) h c ty val body
      | .proj n i sub => lowerProj (lowerBVarsGo amount fuel) h c n i sub

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2144-2146 lowerBVarsFast — the
top-level entry. -/
def lowerBVarsFast (fuel amount c : Nat) (e : EIdx) : AM EIdx := do
  lowerClear
  let r ← lowerBVarsGo amount fuel e c
  lowerClear
  pure r

/-! ## `instantiate1Lift` — `ExprOps.lean:718-739`, `:2222-2261`, `:2356-2358`

The general capture-avoiding substitution: unlike `instantiate1`, the
replacement's own loose `bvar`s are lifted past the binders crossed on the
way, which is what makes it usable on let-values. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:718-739 instantiate1Lift — the
`bvar` arm; the `i = d` case lifts the replacement by the binder depth. -/
def inst1LBvar (fuel : Nat) (v h : EIdx) (d i : Nat) : AM EIdx :=
  if i = d then liftLooseBVarsFast fuel d 0 v
  else if i > d then internE (.bvar (i - 1))
  else pure h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2222-2261 instantiate1LiftGo — the
`app` arm. -/
def inst1LApp (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat) (f a : EIdx) :
    AM EIdx := do
  match ← inst1LGet (h, d) with
  | some r => pure r
  | none => do
    let f' ← rec f d
    let a' ← rec a d
    let r ← internE (.app f' a')
    inst1LSet (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2222-2261 instantiate1LiftGo — the
`lam` arm. -/
def inst1LLam (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat)
    (ty body : EIdx) (m : BinderMeta) : AM EIdx := do
  match ← inst1LGet (h, d) with
  | some r => pure r
  | none => do
    let t ← rec ty d
    let b ← rec body (d + 1)
    let r ← internE (.lam t b m)
    inst1LSet (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2222-2261 instantiate1LiftGo — the
`forallE` arm. -/
def inst1LForall (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat)
    (ty body : EIdx) (m : BinderMeta) : AM EIdx := do
  match ← inst1LGet (h, d) with
  | some r => pure r
  | none => do
    let t ← rec ty d
    let b ← rec body (d + 1)
    let r ← internE (.forallE t b m)
    inst1LSet (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2222-2261 instantiate1LiftGo — the
`letE` arm. -/
def inst1LLet (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat)
    (ty val body : EIdx) : AM EIdx := do
  match ← inst1LGet (h, d) with
  | some r => pure r
  | none => do
    let t ← rec ty d
    let w ← rec val d
    let b ← rec body (d + 1)
    let r ← internE (.letE t w b)
    inst1LSet (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2222-2261 instantiate1LiftGo — the
`proj` arm. -/
def inst1LProj (rec : EIdx → Nat → AM EIdx) (h : EIdx) (d : Nat)
    (n : NIdx) (i : Nat) (sub : EIdx) : AM EIdx := do
  match ← inst1LGet (h, d) with
  | some r => pure r
  | none => do
    let u ← rec sub d
    let r ← internE (.proj n i u)
    inst1LSet (h, d) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:718-739 instantiate1Lift
con-leche: ConLeche/Kernel/ExprOps.lean:2222-2261 instantiate1LiftGo
Replace `bvar d` by `v`, lifting `v`'s loose `bvar`s past the binders crossed
on the way, with con-leche's own `bvarB ≤ d` cutoff. -/
def instantiate1LiftGo (v : EIdx) : Nat → EIdx → Nat → AM EIdx
  | 0, _, _ => fail (.internal "fuel exhausted: instantiate1Lift")
  | fuel + 1, h, d => do
    let bb ← bvarB fuel h
    if bb ≤ d then
      pure h
    else
      match ← view h with
      | .bvar i => inst1LBvar fuel v h d i
      | .fvar _ _ => pure h
      | .sort _ => pure h
      | .const _ _ => pure h
      | .lit _ => pure h
      | .app f a => inst1LApp (instantiate1LiftGo v fuel) h d f a
      | .lam ty body m => inst1LLam (instantiate1LiftGo v fuel) h d ty body m
      | .forallE ty body m => inst1LForall (instantiate1LiftGo v fuel) h d ty body m
      | .letE ty val body => inst1LLet (instantiate1LiftGo v fuel) h d ty val body
      | .proj n i sub => inst1LProj (instantiate1LiftGo v fuel) h d n i sub

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2356-2358 instantiate1LiftFast —
the top-level entry. -/
def instantiate1LiftFast (fuel : Nat) (e v : EIdx) (d : Nat := 0) : AM EIdx := do
  inst1LClear
  let r ← instantiate1LiftGo v fuel e d
  inst1LClear
  pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2365-2378 instPisAtLift —
instantiate the leading `∀`-binders at *open* arguments. -/
def instPisAtLift (fuel : Nat) : List EIdx → EIdx → AM (Option EIdx)
  | [], e => pure (some e)
  | a :: as, h => do
    match ← view h with
    | .forallE _ body _ => do
      let b ← instantiate1LiftFast fuel body a 0
      instPisAtLift fuel as b
    | _ => pure none

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2382-2388 exprPtrBEq — structural
expression equality with a physical-equality shortcut.  In the arena it IS
index equality: `denoteE` is injective (`denoteE_inj`, task #97a), so two
handles denote one term exactly when they are the same handle, and the
pointer test and the structural test collapse into one machine-word
comparison.  No state is read, so this twin takes no monad — the census's
mechanical `AM Bool` is too crude here, as it says of every derived-word
predicate. -/
def exprPtrBEq (a b : EIdx) : Bool := a == b

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2399-2406 Level.hasParam — whether
a level mentions any parameter.  con-leche walks the level; the arena reads
the bit the level store already carries (`LDer.hasParam`, exact by
`LStore.derived_exact`), which is DESIGN §8.3's level-substitution cutoff in
`O(1)`. -/
def LIdx.hasParam (h : LIdx) : AM Bool := do
  let d ← derivedL h
  pure d.hasParam

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2420-2435 Expr.hasLevelParam —
whether an expression mentions any level parameter.  Again a field read: this
is exactly the `hasLP` bit of the packed derived word, and
`Expr.hasLP_eq` is con-leche's own proof that the two agree. -/
def EIdx.hasLevelParam (h : EIdx) : AM Bool := do
  let der ← derivedE h
  pure (lpOfData der)

/-! ## `instantiateLevelParams` — `ExprOps.lean:2564-2603`, `:2718-2720`

**The one twin that touches a level algorithm** (DESIGN §8.3 lesson 4).  The
substitution's names and levels are read back ONCE, at the entry, and the
walk then runs con-leche's own `Level.subst` and `Level.substPW` on transient
trees and re-interns the result.  The twin's `ks`/`us` are therefore
`List Name` and `List Level`, not `List NIdx` and `LsIdx` as the census's
mechanical column has them — that column's rule stops where lesson 4
starts. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2564-2603 Expr.instLPGo — the
`fvar` arm: the annotation is descended into. -/
def instLPFvar (rec : EIdx → AM EIdx) (h : EIdx) (i : Nat) (ty : EIdx) : AM EIdx := do
  match ← instLPGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← rec ty
    let r ← internE (.fvar i t)
    instLPSet (h, 0) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2564-2603 Expr.instLPGo — the
`app` arm. -/
def instLPApp (rec : EIdx → AM EIdx) (h : EIdx) (f a : EIdx) : AM EIdx := do
  match ← instLPGet (h, 0) with
  | some r => pure r
  | none => do
    let f' ← rec f
    let a' ← rec a
    let r ← internE (.app f' a')
    instLPSet (h, 0) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2564-2603 Expr.instLPGo — the
`lam` arm; the binder's prop-ness datum is substituted into as well. -/
def instLPLam (ks : List ConLeche.Name) (us : List Level) (rec : EIdx → AM EIdx)
    (h : EIdx) (ty body : EIdx) (m : BinderMeta) : AM EIdx := do
  match ← instLPGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← rec ty
    let b ← rec body
    let r ← internE (.lam t b ⟨Level.substPW ks us m.pw⟩)
    instLPSet (h, 0) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2564-2603 Expr.instLPGo — the
`forallE` arm. -/
def instLPForall (ks : List ConLeche.Name) (us : List Level) (rec : EIdx → AM EIdx)
    (h : EIdx) (ty body : EIdx) (m : BinderMeta) : AM EIdx := do
  match ← instLPGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← rec ty
    let b ← rec body
    let r ← internE (.forallE t b ⟨Level.substPW ks us m.pw⟩)
    instLPSet (h, 0) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2564-2603 Expr.instLPGo — the
`letE` arm. -/
def instLPLet (rec : EIdx → AM EIdx) (h : EIdx) (ty val body : EIdx) : AM EIdx := do
  match ← instLPGet (h, 0) with
  | some r => pure r
  | none => do
    let t ← rec ty
    let w ← rec val
    let b ← rec body
    let r ← internE (.letE t w b)
    instLPSet (h, 0) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2564-2603 Expr.instLPGo — the
`proj` arm. -/
def instLPProj (rec : EIdx → AM EIdx) (h : EIdx) (n : NIdx) (i : Nat)
    (sub : EIdx) : AM EIdx := do
  match ← instLPGet (h, 0) with
  | some r => pure r
  | none => do
    let u ← rec sub
    let r ← internE (.proj n i u)
    instLPSet (h, 0) r
    pure r

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2564-2603 Expr.instLPGo —
substitute level parameters throughout an expression, with con-leche's own
`hasLP = false` cutoff (the whole subtree is level-parameter free, so the
substitution is the identity on it).  `.sort` and `.const` read their levels
back, run `Level.subst` on the transient trees and re-intern; nothing else in
this module touches a level. -/
def instLPGo (ks : List ConLeche.Name) (us : List Level) : Nat → EIdx → AM EIdx
  | 0, _ => fail (.internal "fuel exhausted: instantiateLevelParams")
  | fuel + 1, h => do
    let der ← derivedE h
    if !(lpOfData der) then
      pure h
    else
      match ← view h with
      | .bvar _ => pure h
      | .lit _ => pure h
      | .sort u => do
        let l ← readLevel u
        let l' ← internLevel (Level.subst ks us l)
        internE (.sort l')
      | .const n vs => do
        let ls ← readLevels vs
        let vs' ← internLevels (ls.map (Level.subst ks us))
        internE (.const n vs')
      | .fvar i ty => instLPFvar (instLPGo ks us fuel) h i ty
      | .app f a => instLPApp (instLPGo ks us fuel) h f a
      | .lam ty body m => instLPLam ks us (instLPGo ks us fuel) h ty body m
      | .forallE ty body m => instLPForall ks us (instLPGo ks us fuel) h ty body m
      | .letE ty val body => instLPLet (instLPGo ks us fuel) h ty val body
      | .proj n i sub => instLPProj (instLPGo ks us fuel) h n i sub

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2718-2720 Expr.instLPFast — the
top-level entry: read the substitution back out of the store once, walk, drop
the memo. -/
def instLPFast (fuel : Nat) (ks : List NIdx) (us : LsIdx) (e : EIdx) : AM EIdx := do
  let ksP ← ks.mapM readName
  let usP ← readLevels us
  instLPClear
  let r ← instLPGo ksP usP fuel e
  instLPClear
  pure r

end ConRon.Arena

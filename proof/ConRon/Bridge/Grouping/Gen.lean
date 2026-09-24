import ConRon.Bridge.Grouping.Store
import ConRon.Bridge.Peel

/-!
# `ConRon.Bridge.Grouping.Gen` — the frame invariant and its generators

Task #98-GROUP.  `Inv k p s`: the scratch tier is open (all four flags), the
persistent tiers are `k` (read as `s.store.enableScratch`) and the pin table
is `p`.  Every function phase B's check reaches keeps it: each gets one
`@[spec]` Hoare triple `⦃Inv k p⦄ f x₀ … xₙ ⦃⇓? _ => Inv k p⦄`.  The triples
are uniform, so three commands state and prove them:

* `#keeps f g …` — a non-recursive function: `mvcgen [f]`;
* `#keeps_ind f i` — structural recursion on the `i`-th explicit argument
  (default: the one named `fuel`, else the first `Nat`);
* `#keeps_fuel Go [Arm₁, …]` — a fuel walk with template rule 9's
  `Go_zero` / `Go_succ` equations and its arms unfolded inline.

A function that takes the core record `r : CoreFnsA` gets the hypothesis
`FnsKeep r` (every slot keeps the invariant), which the proof unpacks.
-/

namespace ConRon.Bridge.Grouping

open ConRon.Arena Std.Do

/-- The frame invariant: scratch open, the persistent tiers `k`, the pins `p`. -/
def Inv (k : EStore) (p : Pins) (s : AState) : Prop :=
  AllOn s.store ∧ s.store.enableScratch = k ∧ s.pins = p

@[simp] theorem Inv_mk {k : EStore} {p : Pins} {st m c q} :
    Inv k p ⟨st, m, c, q⟩ ↔ AllOn st ∧ st.enableScratch = k ∧ q = p := Iff.rfl

/-- Every slot of a core record keeps the invariant. -/
structure FnsKeep (r : CoreFnsA) : Prop where
  whnfCore : ∀ (k : EStore) (p : Pins) d e,
    ⦃fun s => ⌜Inv k p s⌝⦄ r.whnfCore d e ⦃⇓? _r s => ⌜Inv k p s⌝⦄
  whnf : ∀ (k : EStore) (p : Pins) d e,
    ⦃fun s => ⌜Inv k p s⌝⦄ r.whnf d e ⦃⇓? _r s => ⌜Inv k p s⌝⦄
  infer : ∀ (k : EStore) (p : Pins) d e,
    ⦃fun s => ⌜Inv k p s⌝⦄ r.infer d e ⦃⇓? _r s => ⌜Inv k p s⌝⦄
  defeq : ∀ (k : EStore) (p : Pins) d a b,
    ⦃fun s => ⌜Inv k p s⌝⦄ r.defeq d a b ⦃⇓? _r s => ⌜Inv k p s⌝⦄
  annotate : ∀ (k : EStore) (p : Pins) d e,
    ⦃fun s => ⌜Inv k p s⌝⦄ r.annotate d e ⦃⇓? _r s => ⌜Inv k p s⌝⦄
  inferIO : ∀ (k : EStore) (p : Pins) d e,
    ⦃fun s => ⌜Inv k p s⌝⦄ r.inferIO d e ⦃⇓? _r s => ⌜Inv k p s⌝⦄

theorem FnsKeep.ioView {r : CoreFnsA} (h : FnsKeep r) : FnsKeep r.ioView :=
  ⟨h.whnfCore, h.whnf, h.inferIO, h.defeq, h.annotate, h.inferIO⟩

/-- Close a frame verification condition. -/
macro "grp_close" : tactic => `(tactic| (
  simp only [Inv] at *
  bridge_peel
  subst_vars
  simp_all (config := { zetaDelta := true })))

open Lean Elab Tactic Meta in
/-- `keeps_step f …` — unpack every `FnsKeep` hypothesis into its six slot
triples, name every local Hoare triple (induction hypotheses included), run
`mvcgen [f …, those]`, and close what is left with `grp_close`. -/
elab "keeps_step " fs:ident* : tactic => do
  let mut goal ← getMainGoal
  -- unpack `FnsKeep r`
  let lctx ← goal.withContext getLCtx
  let mut j := 0
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← goal.withContext <| whnfR (← instantiateMVars d.type)
    if ty.isAppOf ``FnsKeep then
      for fld in [``FnsKeep.whnfCore, ``FnsKeep.whnf, ``FnsKeep.infer, ``FnsKeep.defeq,
                  ``FnsKeep.annotate, ``FnsKeep.inferIO] do
        let pf ← goal.withContext <| mkAppM fld #[mkFVar d.fvarId]
        let pty ← goal.withContext <| inferType pf
        let (_, g') ← goal.note (Name.mkSimple s!"fk{j}") pf pty
        goal := g'
        j := j + 1
  -- name every triple
  let lctx ← goal.withContext getLCtx
  let mut ids : Array Ident := fs
  let mut i := 0
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).headBeta
    let ty ← Core.transform ty (pre := fun e => match e with
      | .letE _ _ v b _ => return .visit (b.instantiate1 v)
      | .app .. => return if e.isHeadBetaTarget then .visit e.headBeta else .continue
      | _ => return .continue)
    let isT ← goal.withContext <| forallTelescope ty fun _ b =>
      return b.headBeta.getAppFn.isConstOf ``Std.Do.Triple
    if isT then
      let nm := Name.mkSimple s!"ihk{i}"
      i := i + 1
      goal ← goal.replaceLocalDeclDefEq d.fvarId ty
      goal ← goal.rename d.fvarId nm
      ids := ids.push (mkIdent nm)
  replaceMainGoal [goal]
  let lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    ids.mapM fun a => `(Lean.Parser.Tactic.simpLemma| $a:ident)
  evalTactic (← `(tactic| mvcgen [$lemmas,*]))
  evalTactic (← `(tactic| all_goals grp_close))

open Lean Elab Command Meta in
/-- The explicit arguments of a function (`x0 …`), the index of the one named
`fuel` (or of the first `Nat`), and the indices of the `CoreFnsA` ones. -/
def keepsArgs (n : Name) (fuelName : Name := `fuel) :
    CommandElabM (Array Ident × Option Nat × Array Nat) := do
  let ci ← getConstInfo n
  liftTermElabM <| forallTelescope ci.type fun xs _ => do
    let mut out : Array Ident := #[]
    let mut fi : Option Nat := none
    let mut firstNat : Option Nat := none
    let mut rs : Array Nat := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo == .default then
        let i := out.size
        let t ← instantiateMVars d.type
        if d.userName == fuelName then fi := some i
        if firstNat.isNone && t.isConstOf ``Nat then firstNat := some i
        if t.isConstOf ``CoreFnsA then rs := rs.push i
        out := out.push (mkIdent (Name.mkSimple s!"x{i}"))
    return (out, fi.orElse fun _ => firstNat, rs)

open Lean Elab Command Meta in
/-- The statement's binders: the arguments, then `FnsKeep` of each record. -/
def keepsBinders (xs : Array Ident) (rs : Array Nat) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
  let mut bs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  bs := bs.push (← `(Lean.Parser.Term.bracketedBinderF| (k : EStore)))
  bs := bs.push (← `(Lean.Parser.Term.bracketedBinderF| (p : Pins)))
  for x in xs do
    bs := bs.push (← `(Lean.Parser.Term.bracketedBinderF| {$x}))
  for i in rs do
    let x := xs[i]!
    bs := bs.push (← `(Lean.Parser.Term.bracketedBinderF| (_ : FnsKeep $x)))
  return bs

open Lean Elab Command Meta in
/-- `#keeps f g …` — one `@[spec]` frame triple per non-recursive function. -/
elab "#keeps " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let (xs, _, rs) ← keepsArgs n
    let bs ← keepsBinders xs rs
    let thm := mkIdent ((n.replacePrefix `ConRon.Arena .anonymous).appendAfter "_keeps")
    let fn := mkIdent n
    let app ← `($fn $xs*)
    let cmd ← `(command|
      @[spec] theorem $thm $bs* :
          ⦃fun s => ⌜Inv k p s⌝⦄ $app ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
        keeps_step $fn:ident)
    elabCommand cmd

open Lean Elab Command Meta in
/-- `#keeps_fuel Go [Arm₁, …]` — a fuel-indexed walk and its arms (the
`Go_zero` / `Go_succ` equation lemmas of template rule 9): by induction on
the fuel, the arms unfolded inline. -/
elab "#keeps_fuel " go:ident " [" arms:ident,* "]" : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload go
  let (xs, some fi, rs) ← keepsArgs n | throwError "no fuel argument"
  let bs ← keepsBinders xs rs
  let others : Array Ident := ((Array.range xs.size).filter (· != fi)).map (fun i => xs[i]!)
  let xf := xs[fi]!
  let thm := mkIdent ((n.replacePrefix `ConRon.Arena .anonymous).appendAfter "_keeps")
  let fn := mkIdent n
  let z := mkIdent (n.appendAfter "_zero")
  let sc := mkIdent (n.appendAfter "_succ")
  let app ← `($fn $xs*)
  let armIds : Array Ident := arms.getElems
  let cmd ← `(command|
    @[spec] theorem $thm $bs* :
        ⦃fun s => ⌜Inv k p s⌝⦄ $app ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
      induction $xf:ident generalizing $others* with
      | zero => rw [$z:ident]; keeps_step
      | succ n ih =>
        rw [$sc:ident]
        keeps_step $armIds*)
  elabCommand cmd

open Lean Elab Command Meta in
/-- `#keeps_ind f i` — a structurally recursive function, by induction on its
`i`-th explicit argument (default: the one named `fuel`, else the first
`Nat`): `keeps_step f` in every case. -/
elab "#keeps_ind " go:ident idx?:(num)? : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload go
  let (xs, fi?, rs) ← keepsArgs n
  let bs ← keepsBinders xs rs
  let fi ← match idx? with
    | some i => pure i.getNat
    | none => match fi? with
      | some i => pure i
      | none => throwError "no Nat argument"
  let others : Array Ident := ((Array.range xs.size).filter (· != fi)).map (fun i => xs[i]!)
  let xf := xs[fi]!
  let thm := mkIdent ((n.replacePrefix `ConRon.Arena .anonymous).appendAfter "_keeps")
  let fn := mkIdent n
  let app ← `($fn $xs*)
  let cmd ← if others.isEmpty then `(command|
    @[spec] theorem $thm $bs* :
        ⦃fun s => ⌜Inv k p s⌝⦄ $app ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
      induction $xf:ident
      all_goals keeps_step $fn:ident)
    else `(command|
    @[spec] theorem $thm $bs* :
        ⦃fun s => ⌜Inv k p s⌝⦄ $app ⦃⇓? _r s => ⌜Inv k p s⌝⦄ := by
      induction $xf:ident generalizing $others*
      all_goals keeps_step $fn:ident)
  elabCommand cmd

end ConRon.Bridge.Grouping

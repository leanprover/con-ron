/-
# `ConRon.Refine2.Tactic.Attr` — the `@[lockstep]` attribute and the `lockstep_simp` set

Task #97-T2-TACTIC.  Registration only: an environment extension must be
declared in a module *before* the one that uses it, so the attribute lives
here and the judgements, rules and tactic in `Tactic/Lockstep.lean`.

`@[lockstep]` files a lemma under the HEAD CONSTANT of the Rust computation in
its conclusion (`LS pers R (arena.monad.view_app pers st h) lst x` is filed
under `arena.monad.view_app`).  That is Aeneas `progress`'s keying — the
program being stepped, not the goal as a whole — with a `NameMap` in place of
a discrimination tree, because every Rust callee is a constant application.
-/
import Lean

open Lean Meta

namespace ConRon.Refine2.Lockstep

/-- The judgement heads and the position of the Rust computation among their
arguments. -/
def judgementRustArg? (e : Expr) : Option Expr :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn.constName? with
  | some `ConRon.Refine2.Lockstep.LS => args[4]?
  | some `ConRon.Refine2.Lockstep.LSR => args[4]?
  | some `ConRon.Refine2.Lockstep.LSV => args[4]?
  | some `ConRon.Refine2.Lockstep.LSW => args[1]?
  | some `ConRon.Refine2.Lockstep.LSP => args[1]?
  | some `ConRon.Refine2.Lockstep.LSS => args[4]?
  | some `ConRon.Refine2.Lockstep.LSM => args[5]?
  | some `ConRon.Refine2.Lockstep.LSRM => args[5]?
  | _ => none

/-- The key a Rust computation is filed under: its head constant. -/
def rustKey? (m : Expr) : Option Name :=
  m.getAppFn.constName?

/-- An entry of the `@[lockstep]` index: a lemma filed under a key with a
priority, or a lemma erased from its key (`attribute [-lockstep] foo`). -/
inductive LSEntry where
  | add (k n : Name) (prio : Nat)
  | erase (k n : Name)
  deriving Inhabited

initialize lockstepExt :
    SimpleScopedEnvExtension LSEntry (NameMap (Array (Name × Nat))) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun m e => match e with
      | .add k n p => m.insert k (((m.getD k #[]).filter (·.1 != n)).push (n, p))
      | .erase k n => m.insert k ((m.getD k #[]).filter (·.1 != n))
  }

/-- The key of a lemma, from its statement. -/
def lemmaKey (ty : Expr) : MetaM Name := do
  forallTelescope ty fun _ concl => do
    let concl ← instantiateMVars concl
    let some m := judgementRustArg? concl
      | throwError "@[lockstep]: the conclusion is not a lockstep judgement \
          (LS/LSR/LSV/LSW/LSP):{indentExpr concl}"
    let some k := rustKey? m
      | throwError "@[lockstep]: the Rust computation has no head constant:{indentExpr m}"
    return k

/-- **Which lemma for a Rust head is tried first** (task #97-T2-TACTIC round 3,
the Inductives Modeled lane's `IndModWF`).  Candidates are tried in order and
the first that closes wins, so with two lemmas for one Rust function the order
decides.  The order is:

1. local hypotheses (an induction hypothesis, a knot slot);
2. `@[lockstep]` lemmas by PRIORITY, highest first: `@[lockstep high]`,
   `@[lockstep 2000]`, `attribute [local lockstep high] foo` (the priority
   syntax of `@[simp]`; the default is `default` = 1000, `low` = 100);
3. at equal priority, a lemma of a region namespace the file `open`s
   (`open …Lockstep.PB`) before the others;
4. then the order of registration (import order; a re-registration, e.g. a
   `local` one at another priority, moves the lemma to the end of its key).

`attribute [-lockstep] foo` removes `foo` from its key (for the rest of the
section or file, like any attribute erasure).  So a lemma that proves MORE
than an imported one of the same Rust head (its answer with a
well-formedness conjunct) is registered `@[lockstep high]` where it is
declared, or `attribute [local lockstep high]` in the one file that needs it. -/
initialize registerBuiltinAttribute {
  name := `lockstep
  descr := "a lockstep correspondence lemma, keyed on its Rust callee; \
    `@[lockstep high]` / `@[lockstep <n>]` sets its priority"
  add := fun decl stx kind => do
    let info ← getConstInfo decl
    let k ← (lemmaKey info.type).run' {} {}
    let prio ← getAttrParamOptPrio stx[1]
    lockstepExt.add (.add k decl prio) kind
  erase := fun decl => do
    let info ← getConstInfo decl
    let k ← (lemmaKey info.type).run' {} {}
    lockstepExt.add (.erase k decl) .local
}

/-- The lemmas filed under a key with their priorities, in registration
order. -/
def lockstepLemmasPrio (k : Name) : CoreM (Array (Name × Nat)) := do
  return (lockstepExt.getState (← getEnv)).getD k #[]

/-- The lemmas filed under a key, in registration order. -/
def lockstepLemmas (k : Name) : CoreM (Array Name) := do
  return (← lockstepLemmasPrio k).map (·.1)

end ConRon.Refine2.Lockstep

/-- The abstraction equations the twin side reduces with after a Rust split. -/
register_simp_attr lockstep_simp

/-- Rust helpers the core tactic (`Refine2/Core/LS/Tactic.lean`) unfolds in
place instead of stepping over with a lemma: the port's fragments of one twin
function (task #97-P5-Core round 5). -/
register_simp_attr lockstep_inline

/-- Twin-side rewriting rules `lockstep_core` tries when the twin's next action
is a whole-node `view` and the port's is a typed projection: each is tried and
kept only if the port's next step then goes through (task #97-P5-Core round 5). -/
register_simp_attr lockstep_twin

/-- Twin equations used ONLY to check that a callee spec's twin action is the
goal's (`lockstep_congr`, the `x' = x` premise of every bind rule), never to
rewrite the twin program itself (task #97-T2-TACTIC round 3).  The
accumulator-versus-`List.mapM` equations (`xs.mapM (fun e => f …) = FSpec xs`,
the Inductives lane's `mapM_structIdxAt_eq`) belong here: a caller's
`xs.mapM` meets a callee spec stated at `FSpec` (a `…_twin0` companion), while
a caller whose callee is stated at the `mapM` form keeps it — registered
`lockstep_simp`, the equation rewrote such a twin away from its callee's
statement (`struct_minor_ty_r`). -/
register_simp_attr lockstep_congr_simp

/-- Answer relations the zip splits although they are `def`s (task
#97-T2-TACTIC round 3, the Inductives Parts lane's `WOutRel`): a relation that
unfolds REDUCIBLY to a conjunction (an `abbrev`) is split at every step and
leaf anyway; `@[lockstep_rel] def R … := A ∧ B` has the same effect for a
`def`, which other proofs keep folded. -/
register_simp_attr lockstep_rel

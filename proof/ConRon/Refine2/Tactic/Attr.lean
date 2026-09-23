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

initialize lockstepExt :
    SimpleScopedEnvExtension (Name × Name) (NameMap (Array Name)) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun m (k, n) => m.insert k ((m.getD k #[]).push n)
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

initialize registerBuiltinAttribute {
  name := `lockstep
  descr := "a lockstep correspondence lemma, keyed on its Rust callee"
  add := fun decl _stx kind => do
    let info ← getConstInfo decl
    let k ← (lemmaKey info.type).run' {} {}
    lockstepExt.add (k, decl) kind
}

/-- The lemmas filed under a key. -/
def lockstepLemmas (k : Name) : CoreM (Array Name) := do
  return (lockstepExt.getState (← getEnv)).getD k #[]

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

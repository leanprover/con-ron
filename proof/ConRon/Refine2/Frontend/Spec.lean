/-
# `ConRon.Refine2.Frontend.Spec` — the twin side of the port's own splits

**Task #97-P5-Frontend**, and `Refine2/Checker/Spec.lean`'s pattern at this
tier (task #97-P5-Checker's finding 11: *"one collected transcription file per
tier, with `_unfold` equations, and no edit to the twin"*).

DESIGN §3.4 splits a Rust function wherever a `let`-bound handle outlives a
`match` arm, wherever an arm would end in a branch, and wherever a `view`'s
loan would still be alive at an intern (extraction rules 5-7).  The frontend
is split that way wherever a twin `do` block has more structure than one Rust
body can carry — `proj_rec::proj_rec_value` alone is six functions for one
48-line block — and the split halves have no twin to be stated against.

This file is the twin side of those halves, written as twin-side `def`s in
`AM`, transcribed from `Arena/Frontend/ExportC.lean` clause for clause, with
an `_unfold` equation per family saying that the named twin IS its
transcription composed.  **Nothing under `Arena/` is edited to make the
refinement convenient**, which is the standing rule for a twin (DESIGN §8.4);
a reader checks these against the twin, not against a proof.

The `_unfold`s are `rfl`-shaped in the sense task #97-P5-Checker's §6 means:
each is a `do`-block equation in `StateT AState (Except CheckError)`, which
needs that section's rule-10 reduction discipline.  They are open here for the
same reason they were open there.

## `sorry` count in this file: 0

Round 3 (task #97-T2-LOCKSTEP lane Frontend): the `projRecValue` / owner-census
transcriptions and their six `_unfold`s are deleted — they predated the twin's
tag-first reads and were no longer the twin; `proj_rec_value` and
`proj_rec_owners` are proved against the twin directly, the port's splits
unfolded in place (`lockstep_inline`).

**Task #105** (con-leche's `uniform-inds` merge) deletes the projection
rewrite (`ProjRec.lean`, upstream and here) and the in-process modeller
(`noteIndBlocks`/`installGen`, `Modeller`): `mkProjMotiveAt`/`mkProjMinorAt`
(the rewrite's split halves), `noteDeclEntries`/`noteEntries`/
`noteDecl_unfold` (the pushed-record bookkeeping `pushDecl` no longer does
first) and `noteIndBlocks`/`installGen` are gone with them, and
`installIndD_unfold` restates the now much shorter `installIndD`: build the
block (`indBlockOf`, unchanged), push it — no owner table, no block record, no
modeller gate.
-/
import ConRon.Refine2.Frontend.NatOpGround

open Aeneas Aeneas.Std Result

namespace ConRon.Refine2.Frontend

open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IdTable NameRec LevelRec ExprRec PwRec CVRec HintsRec RuleRec
  IndTypeRec IndCtorRec IndRecRec DeclRec LineRec)

/-! ## `export_c`'s own splits

The value halves of the two entry writers that the twin spells inline.
`RefineOld/Frontend/StateDR.lean` needed exactly the same two escape-hatch
definitions for the `Expr`-tree port (`parseExprRecD` / `parseLevelRecD`, and
its `parseExprEntryD_eq` / `parseLevelEntryD_eq` equivalences).

**Task #105** deletes `ProjRec.lean` upstream (`mkProjMotiveAt`/
`mkProjMinorAt`, the projection rewrite's split halves, go with it) and the
in-process modeller (`noteDecl`'s constants-and-heights bookkeeping —
`noteDeclEntries`/`noteEntries`/`noteDecl_unfold` — is gone: `pushDecl` no
longer runs it first). -/

/-- The value half of `parseLevelEntryD`, which the twin writes inline. -/
def parseLevelRecD (st : StateD) : ConLeche.Frontend.LevelRec → AM LNodeView
  | .succ u => do pure (.succ (← st.level u))
  | .max a b => do pure (.max (← st.level a) (← st.level b))
  | .imax a b => do pure (.imax (← st.level a) (← st.level b))
  | .param n => do pure (.param (← st.name n))

theorem parseLevelEntryD_unfold (st : StateD) (i : Nat) (r : ConLeche.Frontend.LevelRec) :
    parseLevelEntryD st i r = (do
      st.freshLevel i
      let l ← internLNode (← parseLevelRecD st r)
      pure { st with levels := st.levels.insert i l }) := by
  cases r <;> simp only [parseLevelEntryD, parseLevelRecD, bind_assoc, pure_bind]

/-- The value half of `parseExprEntryD`, which the twin writes inline. -/
def parseExprRecD (st : StateD) : ConLeche.Frontend.ExprRec → AM EIdx
  | .bvar k => internE (.bvar k)
  | .sort u => do internE (.sort (← st.level u))
  | .const n us => do
    let nm ← st.name n
    let ls ← us.mapM st.level
    let lsh ← internLsNode ls
    internE (.const nm lsh)
  | .app f a => do internE (.app (← st.expr f) (← st.expr a))
  | .lam ty bd pw => do
    internE (.lam (← st.expr ty) (← st.expr bd) ⟨← parsePwD st pw⟩)
  | .forallE ty bd pw => do
    internE (.forallE (← st.expr ty) (← st.expr bd) ⟨← parsePwD st pw⟩)
  | .letE ty vl bd => do
    internE (.letE (← st.expr ty) (← st.expr vl) (← st.expr bd))
  | .proj tn ix s => do internE (.proj (← st.name tn) ix (← st.expr s))
  | .natVal n => internE (.lit (.natVal n))
  | .strVal s => internE (.lit (.strVal s))

theorem parseExprEntryD_unfold (st : StateD) (i : Nat) (r : ConLeche.Frontend.ExprRec) :
    parseExprEntryD st i r = (do
      st.freshExpr i
      let e ← parseExprRecD st r
      pure { st with exprs := st.exprs.insert i e }) := by
  cases r <;> simp only [parseExprEntryD, parseExprRecD, bind_assoc]

/-- The twin's `types ++ ctors ++ recs` of `installIndD`, which the port
factors out as `ind_block_of`. -/
def indBlockOf (st : StateD) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) : AM (List IConstantInfo) := do
  let types ← tys.mapM fun t => do
    pure (IConstantInfo.indInfo (← parseCVD st t.cv) {})
  let ctors ← cts.mapM fun c => do
    pure (IConstantInfo.ctorInfo (← parseCVD st c.cv) c.numParams c.numFields)
  let recs ← rcs.mapM fun r => do
    let rules ← r.rules.mapM (parseRuleD st)
    pure (IConstantInfo.recInfo (← parseCVD st r.cv)
      (r.numParams + r.numMotives + r.numMinors + r.numIndices)
      (r.numParams + r.numMotives + r.numMinors) rules)
  pure (types ++ ctors ++ recs)

/-- **`installIndD_unfold`.**  Task #105 deletes the projection-owner table
(`registerProjOwners`), the block record (`blockRecOf`/`noteIndBlocks`) and
the modeller gate (`installGen`, `Modeller`) that used to follow
`indBlockOf` here: every block installs through the kernel's uniform
installer now, so the parser has nothing left to do but push it. -/
theorem installIndD_unfold (st : StateD) (tys : List IndTypeRec)
    (cts : List IndCtorRec) (rcs : List IndRecRec) (nPd : Nat) :
    installIndD st tys cts rcs nPd = (do
      let block ← indBlockOf st tys cts rcs
      pushDecl st (.indDecl block nPd)) := by
  simp only [installIndD, indBlockOf, bind_assoc, pure_bind]

end ConRon.Refine2.Frontend

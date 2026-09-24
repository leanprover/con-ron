/-
# `ConRon.Arena.Frontend.InModel` — the modeller seam, instantiated
(DESIGN.md §8.2, task #97e part 2)

`Arena/Frontend/Types.lean`'s

    structure Modeller where
      generate : Ctx → BlockRec → AM (Except String (List IDeclaration))

is DESIGN §8.2's `Modeller`: the one-method seam at which a mutual or nested
inductive block's `_model` family is produced.  Task #97e part 1 shipped
`declineModeller`, which declines every block the seam is asked about; that is
what stopped the `Init` parse at line 78 503, where `Lean.Syntax` reaches it.

**This module instantiates the seam by DELEGATION**: it reads the block's
handles back to `Expr`/`Name`/`Level`, calls **con-leche's own generator**
verbatim, and interns the declarations it returns into the persistent tier.

    con-leche: ConLeche/Frontend/InModel.lean:39-45 generate — called, not twinned

**Why that is the right instantiation, and not a shortcut.**

* **It is exact by construction.**  The generated records are con-leche's own
  records: the readback IS the denotation (`Arena/Frontend/Readback.lean`) and
  the intern IS its inverse, so the block this seam produces is the block
  con-leche produces on the same input.  A twin of the generator would have to
  be *argued* to agree with it; this one cannot disagree.
* **It claims no soundness, because the seam claims none.**  DESIGN §8.2
  puts the modeller outside the verified surface, and con-leche's own module
  doc says why: "a wrong record is rejected or declined by the fold, never
  accepted.  Its correctness decides only *coverage*."  So the layer this
  module adds is unverified, and it is unverified in exactly the place the
  design already says is unverified — no theorem moves.
* **It is BOUNDED.**  One block at a time, and only a block `wants` routes
  here (mutual, or nested): con-leche's `InModel.wants` reads counts and no
  term, and it stays the plain function `Arena/Frontend/Types.lean` has.  The
  stream is never read back.
* **The Rust keeps its own port.**  `crates/con-ron-core/src/frontend/
  in_model_rec.rs` is (C)'s unverified modeller and stays what it is; the
  delegation is (B)'s, where con-leche is a library the same binary can call.
  When (B) is measured against con-leche (P2g) this is the honest
  instantiation, because both sides then run the same generator.

**The memo, again.**  Both directions go through
`Arena/Frontend/Readback.lean`'s memoised families, for the reason its module
note gives: an unmemoised readback unfolds the DAG, which on con-leche's own
`tower_struct` fixture does not finish.

**Closures live here and nowhere below.**  `ConLeche.Frontend.InModel.Ctx`'s
three fields are functions `Name → …`, so `ctxOf` builds three closures over a
store snapshot.  DESIGN §3.4 forbids a closure in code Aeneas must translate;
nothing in this module is translated — it is the seam's *instantiation*, and
(C) supplies its own.
-/
import ConRon.Arena.Frontend.Readback
import ConRon.Arena.Frontend.Types
import ConLeche.Frontend.InModel

namespace ConRon.Arena.Frontend

open ConLeche
open ConRon.Arena

/-! ## The block, read back -/

/-- con-leche: none — the memoised denotation of one type former of a parsed
block (`Arena/Frontend/Types.lean`'s `MIndTypeRec` ↦ con-leche's own
`InModel.IndTypeRec`). -/
def denoteMTypeGo (st : EStore) (m : DMemo) (t : MIndTypeRec) :
    Option (DMemo × ConLeche.Frontend.InModel.IndTypeRec) :=
  match denoteCVGo st m t.cv, denoteNList st.ns t.ctors with
  | some (m, cv), some cs =>
    some (m, ⟨cv, t.nP, t.nIdx, cs, t.isRec, t.isReflexive, t.numNested⟩)
  | _, _ => none

/-- con-leche: none — the memoised denotation of a type-former list. -/
def denoteMTypesGo (st : EStore) (m : DMemo) :
    List MIndTypeRec → Option (DMemo × List ConLeche.Frontend.InModel.IndTypeRec)
  | [] => some (m, [])
  | t :: ts =>
    match denoteMTypeGo st m t with
    | some (m, x) =>
      match denoteMTypesGo st m ts with
      | some (m, xs) => some (m, x :: xs)
      | none => none
    | none => none

/-- con-leche: none — the memoised denotation of one constructor record. -/
def denoteMCtorGo (st : EStore) (m : DMemo) (c : MIndCtorRec) :
    Option (DMemo × ConLeche.Frontend.InModel.IndCtorRec) :=
  match denoteCVGo st m c.cv with
  | some (m, cv) => some (m, ⟨cv, c.nP, c.nF⟩)
  | none => none

/-- con-leche: none — the memoised denotation of a constructor list. -/
def denoteMCtorsGo (st : EStore) (m : DMemo) :
    List MIndCtorRec → Option (DMemo × List ConLeche.Frontend.InModel.IndCtorRec)
  | [] => some (m, [])
  | c :: cs =>
    match denoteMCtorGo st m c with
    | some (m, x) =>
      match denoteMCtorsGo st m cs with
      | some (m, xs) => some (m, x :: xs)
      | none => none
    | none => none

/-- con-leche: none — the memoised denotation of one recursor record. -/
def denoteMRecGo (st : EStore) (m : DMemo) (r : MIndRecRec) :
    Option (DMemo × ConLeche.Frontend.InModel.IndRecRec) :=
  match denoteCVGo st m r.cv with
  | some (m, cv) =>
    match denoteRulesGo st m r.rules with
    | some (m, rules) => some (m, ⟨cv, r.nP, r.nM, r.nm, r.nI, rules⟩)
    | none => none
  | none => none

/-- con-leche: none — the memoised denotation of a recursor list. -/
def denoteMRecsGo (st : EStore) (m : DMemo) :
    List MIndRecRec → Option (DMemo × List ConLeche.Frontend.InModel.IndRecRec)
  | [] => some (m, [])
  | r :: rs =>
    match denoteMRecGo st m r with
    | some (m, x) =>
      match denoteMRecsGo st m rs with
      | some (m, xs) => some (m, x :: xs)
      | none => none
    | none => none

/-- con-leche: none — the memoised denotation of a parsed inductive block: the
argument con-leche's generator takes.  One memo for the whole block, so the
sharing between its types, constructors and recursors survives the readback. -/
def denoteBlockRecGo (st : EStore) (m : DMemo) (b : BlockRec) :
    Option (DMemo × ConLeche.Frontend.InModel.BlockRec) :=
  match denoteMTypesGo st m b.types with
  | some (m, ts) =>
    match denoteMCtorsGo st m b.ctors with
    | some (m, cs) =>
      match denoteMRecsGo st m b.recs with
      | some (m, rs) => some (m, ⟨ts, cs, rs⟩)
      | none => none
    | none => none
  | none => none

/-- con-leche: none — the block, read back at a fresh memo. -/
def denoteBlockRec (st : EStore) (b : BlockRec) :
    Option ConLeche.Frontend.InModel.BlockRec :=
  match denoteBlockRecGo st ∅ b with
  | some (_, x) => some x
  | none => none

/-! ## The context, read back

con-leche's `Ctx` is three FUNCTIONS of a `Name`, so the bridge is three
closures: map the name to its handle by probing the name store
(`nameHandle?`, pure), ask the arena's own `Ctx`, and read the answer back.  A
name the store has never interned is a name no declaration carries, so `none`
/ `0` is the right answer there and not a failure. -/

/-- con-leche: none — the arena's `Ctx` as con-leche's, over a store
snapshot: the declared types of the constants pushed so far, their definitional
heights, and the parsed inductive blocks by member type name. -/
def ctxOf (st : EStore) (ctx : Ctx) : ConLeche.Frontend.InModel.Ctx :=
  { tbl := fun n =>
      match nameHandle? st.ns n with
      | none => none
      | some h =>
        match ctx.tbl h with
        | none => none
        | some (lps, ty) =>
          match denoteNList st.ns lps, denoteEShared st ty with
          | some lpsP, some tyP => some (lpsP, tyP)
          | _, _ => none
    heights := fun n =>
      match nameHandle? st.ns n with
      | none => 0
      | some h => ctx.heights h
    blocks := fun n =>
      match nameHandle? st.ns n with
      | none => none
      | some h =>
        match ctx.blocks h with
        | none => none
        | some b => denoteBlockRec st b }

/-! ## The seam -/

/-- con-leche: ConLeche/Frontend/InModel.lean:39-45 generate — **the modeller,
by delegation**: the block read back, con-leche's own `InModel.generate` run on
it, and the declarations it returns interned into the persistent tier.  The
module note argues why this is the instantiation (B) should have; the short
version is that it cannot disagree with con-leche, and that the seam is
unverified by design either way.

A decline is con-leche's own decline, with con-leche's own reason string, so
`installIndD`'s `.declined` verdict names the residual class con-leche names.

**A block that does not read back is a DECLINE, not a throw** (task
#97-T2-LOCKSTEP lane Frontend round 3, the coordinator's ruling c1): the port
(`crates/con-ron/src/in_model.rs`) answers `Err("arena: dangling handle in a
modelled block")` there, which the parse books as a decline, and this twin
threw `internal`.  Theorem 1 never reaches the arm (`BlockRecRel` makes the
block read back); Theorem 2's `ModellerRefines` does. -/
def inProcessModeller : Modeller :=
  ⟨fun ctx b => do
    let s ← get
    match denoteBlockRec s.store b with
    | none => pure (.error "arena: dangling handle in a modelled block")
    | some bP =>
      match ConLeche.Frontend.InModel.generate (ctxOf s.store ctx) bP with
      | .error why => pure (.error why)
      | .ok ds => do
        let (_, hs) ← internDecls ∅ ds
        pure (.ok hs)⟩

end ConRon.Arena.Frontend

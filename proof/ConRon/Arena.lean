/-
# `ConRon.Arena` — the arena checker (B) of DESIGN.md §8

Task #97 phase P2a delivers the *store layer*: the handles, the four
per-constructor interned stores, their denotation into con-leche's own
`Name`/`Level`/`Expr`, and the well-formedness predicate and exactness
theorems that every later module programs against.

The arena's own verification lives beside the implementation (con-leche's
lesson 27, `_tmp/t97/conleche-arena-history.md` §6.27): `WF.lean` and
`WFProofs.lean` import `Handle`/`Store`/`Denote` and nothing else — in
particular nothing from `ConRon.Refine`.
-/
module

public import ConRon.Arena.Handle
public import ConRon.Arena.Store
public import ConRon.Arena.Denote
public import ConRon.Arena.WF
public import ConRon.Arena.WFSkip
public import ConRon.Arena.WFProofs
public import ConRon.Arena.StoreTest
public import ConRon.Arena.Monad
public import ConRon.Arena.ExprOps
public import ConRon.Arena.ExprOpsTest
public import ConRon.Arena.Env
public import ConRon.Arena.Frontend.Types
public import ConRon.Arena.Frontend.Readback
public import ConRon.Arena.Frontend.ExportC
public import ConRon.Arena.Frontend.Prepare
public import ConRon.Arena.Frontend.PreludeText
public import ConRon.Arena.Frontend.Prelude
public import ConRon.Arena.PropRead
public import ConRon.Arena.Core
public import ConRon.Arena.CoreIO
public import ConRon.Arena.CoreTest
public import ConRon.Arena.Intern
public import ConRon.Arena.Canon
public import ConRon.Arena.StdAxioms
public import ConRon.Arena.TrustAxioms
public import ConRon.Arena.Basis
public import ConRon.Arena.NatOpPinSet
public import ConRon.Arena.CheckerBase
public import ConRon.Arena.CheckerSplit
public import ConRon.Arena.Promote
public import ConRon.Arena.PersistentRun
public import ConRon.Arena.PromoteExt
public import ConRon.Arena.DeclCheck
public import ConRon.Arena.Inductives.StructParts
public import ConRon.Arena.Inductives.StructInstall
public import ConRon.Arena.Inductives.SumInstall
public import ConRon.Arena.Inductives.FieldTele
public import ConRon.Arena.Inductives.Positivity
public import ConRon.Arena.Inductives.BlockParts
public import ConRon.Arena.Inductives.BlockRec
public import ConRon.Arena.Inductives.ClassRead
public import ConRon.Arena.Inductives.BlockInstall
public import ConRon.Arena.Inductives.RecCheck
public import ConRon.Arena.Inductives.GenRec
public import ConRon.Arena.Inductives.BlockTail
public import ConRon.Arena.CheckDecl
public import ConRon.Arena.InductivesTest
public import ConRon.Arena.Checker
public import ConRon.Arena.Phased
public import ConRon.Arena.CheckerTest
public import ConRon.Arena.Frontend.NatOpGround
-- the driver: no proof imports it, so the root does, to keep it in `lake build`
public import ConRon.Arena.Main

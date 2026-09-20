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
import ConRon.Arena.Handle
import ConRon.Arena.Store
import ConRon.Arena.Denote
import ConRon.Arena.WF
import ConRon.Arena.WFProofs
import ConRon.Arena.StoreTest
import ConRon.Arena.Monad
import ConRon.Arena.ExprOps
import ConRon.Arena.ExprOpsTest
import ConRon.Arena.Env
import ConRon.Arena.Frontend.Types
import ConRon.Arena.Frontend.Readback
import ConRon.Arena.Frontend.ProjRec
import ConRon.Arena.Frontend.ProjRecTest
import ConRon.Arena.Frontend.InModel
import ConRon.Arena.Frontend.ExportC
import ConRon.Arena.Frontend.Prepare
import ConRon.Arena.Frontend.PreludeText
import ConRon.Arena.Frontend.Prelude
import ConRon.Arena.PropRead
import ConRon.Arena.Core
import ConRon.Arena.FEnv
import ConRon.Arena.CoreIO
import ConRon.Arena.CoreGated
import ConRon.Arena.CoreTest
import ConRon.Arena.Intern
import ConRon.Arena.Canon
import ConRon.Arena.StdAxioms
import ConRon.Arena.TrustAxioms
import ConRon.Arena.Basis
import ConRon.Arena.NatOpPinSet
import ConRon.Arena.CheckerBase
import ConRon.Arena.CheckerSplit
import ConRon.Arena.DeclCheck
import ConRon.Arena.Inductives.StructParts
import ConRon.Arena.Inductives.Base
import ConRon.Arena.Inductives.SumParts
import ConRon.Arena.Inductives.Modeled
import ConRon.Arena.Inductives.StructInstall
import ConRon.Arena.Inductives.StructInstallF
import ConRon.Arena.Inductives.SumInstall
import ConRon.Arena.Inductives.SumInstallF
import ConRon.Arena.Inductives.NativeParts
import ConRon.Arena.Inductives.NativeInstall
import ConRon.Arena.Inductives.NativeInstallF
import ConRon.Arena.Inductives
import ConRon.Arena.InductivesTest
import ConRon.Arena.Checker
import ConRon.Arena.CheckerGated
import ConRon.Arena.CheckerTest
import ConRon.Arena.Frontend.NatOpGround

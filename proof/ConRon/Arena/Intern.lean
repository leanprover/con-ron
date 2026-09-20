/-
# `ConRon.Arena.Intern` — con-leche's pinned VALUES into the store

DESIGN §8.3, lesson 4 ("intern the representation, not the algorithm") applied
to the checker's PINNED DATA.

Three families of con-leche declaration are pure `Expr` / `ConstantInfo`
*values* written out by hand or spliced by an elaborator, and nothing about
them is an algorithm:

* the basis blocks (`ConLeche/Kernel/Basis*.lean`, `BasisKind.declsA` — the
  annotated `Eq`, `Nat`, `PUnit`, `Empty`, `False` and `Quot` pins);
* the standard- and compiler-trust axiom pins (`ConLeche/Kernel/StdAxioms.lean`,
  `ConLeche/Kernel/TrustAxioms.lean`, `ConLeche/Kernel/TrustPins.lean`);
* the `Nat`-operation pin variants (`ConLeche/Kernel/NatOpPins.lean`'s
  `natOpPinSets`, sixteen `Expr` fields each).

A handle twin of one of these would be the same tree spelled with `internE`
instead of `Expr.app`, and nothing would be gained: DESIGN §8.7's ruling is
that (B) IMPORTS con-leche's representation-free data rather than copying it.
So what this module provides is the ONE walk that puts such a value into the
store — `internExpr`, `internCV`, `internCI` and their list forms — and the
twins above it (`Arena/Basis.lean`, `Arena/StdAxioms.lean`,
`Arena/TrustAxioms.lean`, `Arena/NatOpPinSet.lean`) are one line each.

**The tier matters.**  A pin interned while the scratch tier is live would go
with the tier, and the environment would hold a dangling handle.  DESIGN §8.6
P2d says the pins are interned "at startup — a one-time tree walk", i.e. into
the PERSISTENT tier, and `internAllPins` (`Arena/Checker.lean`) is that
startup: after it every pin node is in the persistent cons table, so a later
`intern` of the same node — whatever tier is live — probes persistent first
and hands back the persistent handle (DESIGN §8.3: "`intern` probes the
persistent table, then the scratch one").

**No fuel.**  Every walk here is structural on a con-leche VALUE — a tree, not
a DAG of handles — exactly as `Monad.lean`'s `internName` and `internLevel`
are.  The Rust transliteration is a recursive function over the generated
constant tables (`crates/con-ron-core/src/kernel/basis_tables.rs`, task #22).
-/
import ConRon.Arena.Env
import ConLeche.Kernel.Basis
import ConLeche.Kernel.BasisA

namespace ConRon.Arena

open ConLeche

/-! ## Terms -/

/-- con-leche: ConLeche/Kernel/Expr.lean:343-353 Expr — intern a transient
`ConLeche.Expr` tree, bottom up.  Structural on the value, so no fuel; the
children are interned before the node, which is what `EStore.intern` needs
(`ViewOK`). -/
def internExpr : ConLeche.Expr → AM EIdx
  | .bvar i => internE (.bvar i)
  | .fvar idx ty => do
    let t ← internExpr ty
    internE (.fvar idx t)
  | .sort u => do
    let hu ← internLevel u
    internE (.sort hu)
  | .const n us => do
    let hn ← internName n
    let hus ← internLevels us
    internE (.const hn hus)
  | .app f a => do
    let hf ← internExpr f
    let ha ← internExpr a
    internE (.app hf ha)
  | .lam ty body m => do
    let ht ← internExpr ty
    let hb ← internExpr body
    internE (.lam ht hb m)
  | .forallE ty body m => do
    let ht ← internExpr ty
    let hb ← internExpr body
    internE (.forallE ht hb m)
  | .letE ty val body => do
    let ht ← internExpr ty
    let hv ← internExpr val
    let hb ← internExpr body
    internE (.letE ht hv hb)
  | .lit l => internE (.lit l)
  | .proj s i e => do
    let hs ← internName s
    let he ← internExpr e
    internE (.proj hs i he)

/-- con-leche: none — intern a list of transient terms.  DESIGN §3.4 forbids
the closure a `xs.mapM internExpr` would take, and its rule for a `List`
recursion is a helper, so this is one. -/
def internExprList : List ConLeche.Expr → AM (List EIdx)
  | [] => pure []
  | e :: es => do
    let h ← internExpr e
    let hs ← internExprList es
    pure (h :: hs)

/-- con-leche: none — intern an ARRAY of transient terms (a projection
table's bodies).  The list walk followed by `List.toArray`, so the recursion
is still the `List` one DESIGN §3.4 asks for. -/
def internExprArray (es : Array ConLeche.Expr) : AM (Array EIdx) := do
  let hs ← internExprList es.toList
  pure hs.toArray

/-! ## Names and levels, as lists -/

/-- con-leche: none — intern a list of transient names (a constant's level
parameters). -/
def internNameList : List ConLeche.Name → AM (List NIdx)
  | [] => pure []
  | n :: ns => do
    let h ← internName n
    let hs ← internNameList ns
    pure (h :: hs)

/-- con-leche: none — intern a list of transient levels as a list of level
HANDLES (a projection table's guards), not as an interned list node. -/
def internLevelsList : List Level → AM (List LIdx) := internLevelList

/-! ## The declaration layer -/

/-- con-leche: ConLeche/Kernel/Env.lean:186-191 ConstantVal — intern a
transient `ConstantVal` into `IConstantVal`. -/
def internCV (cv : ConstantVal) : AM IConstantVal := do
  let n ← internName cv.name
  let lps ← internNameList cv.levelParams
  let ty ← internExpr cv.type
  pure ⟨n, lps, ty⟩

/-- con-leche: ConLeche/Kernel/Env.lean:193-237 RecRuleFire — intern a stored
rule's firing mode.  The parse and the pins write `.inert`; `.nested`'s level
and pin lists are interned like any other. -/
def internFire : RecRuleFire → AM IRecRuleFire
  | .inert => pure .inert
  | .plain => pure .plain
  | .nested lvls pins => do
    let hl ← internLevelList lvls
    let hp ← internExprList pins
    pure (.nested hl hp)

/-- con-leche: ConLeche/Kernel/Env.lean:239-282 RecRule — intern one iota
rule. -/
def internRecRule (rl : RecRule) : AM IRecRule := do
  let c ← internName rl.ctor
  let f ← internFire rl.fire
  let rhs ← internExpr rl.rhs
  pure ⟨c, rl.nfields, rl.ctorParams, f, rhs, rl.k, rl.eta, rl.paramsBlind⟩

/-- con-leche: none — intern a list of iota rules. -/
def internRecRules : List RecRule → AM (List IRecRule)
  | [] => pure []
  | r :: rs => do
    let h ← internRecRule r
    let hs ← internRecRules rs
    pure (h :: hs)

/-- con-leche: ConLeche/Kernel/Env.lean:347-374 IndCaps — intern an inductive
type's capabilities.  `sortZ` is con-leche's own `PropWhen` (DESIGN §8.7: the
store's binder metadata already carries one), so only `etaCtor` moves. -/
def internCaps (caps : IndCaps) : AM IIndCaps := do
  let ec ← internName caps.etaCtor
  pure { eta := caps.eta, etaCtor := ec, etaParams := caps.etaParams,
         etaFields := caps.etaFields, unitlike := caps.unitlike,
         unitParams := caps.unitParams, ruleK := caps.ruleK,
         sortZ := caps.sortZ }

/-- con-leche: ConLeche/Kernel/Env.lean:376-431 ProjTable — intern a
projection table.  `IProjTable.tableName` is the one field con-leche's record
does not have (task #97e's note), and the value it takes here is what
con-leche COMPUTES in `ConstantInfo.toConstantVal`: `projTableName
structName`. -/
def internProjTable (tbl : ProjTable) : AM IProjTable := do
  let sn ← internName tbl.structName
  let tn ← projTableName sn
  let lps ← internNameList tbl.levelParams
  let ct ← internName tbl.ctor
  let ss ← internLevel tbl.structSort
  let bodies ← internExprArray tbl.bodies
  let guards ← internLevelsList tbl.guards
  pure ⟨sn, tn, lps, tbl.numParams, ct, tbl.numFields, ss, bodies, guards,
    tbl.off⟩

/-- con-leche: ConLeche/Kernel/Env.lean:460-486 ConstantInfo — intern a stored
constant, constructor for constructor. -/
def internCI : ConstantInfo → AM IConstantInfo
  | .axiomInfo v => do pure (.axiomInfo (← internCV v))
  | .defnInfo v value hint => do
    let cv ← internCV v
    let hv ← internExpr value
    pure (.defnInfo cv hv hint)
  | .thmInfo v value => do
    let cv ← internCV v
    let hv ← internExpr value
    pure (.thmInfo cv hv)
  | .indInfo v caps => do
    let cv ← internCV v
    let hc ← internCaps caps
    pure (.indInfo cv hc)
  | .ctorInfo v nP nF => do pure (.ctorInfo (← internCV v) nP nF)
  | .recInfo v mI rP rules => do
    let cv ← internCV v
    let hr ← internRecRules rules
    pure (.recInfo cv mI rP hr)
  | .projInfo tbl => do pure (.projInfo (← internProjTable tbl))

/-- con-leche: none — intern a list of stored constants (a basis block). -/
def internCIList : List ConstantInfo → AM (List IConstantInfo)
  | [] => pure []
  | ci :: cs => do
    let h ← internCI ci
    let hs ← internCIList cs
    pure (h :: hs)

end ConRon.Arena

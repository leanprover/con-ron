/-
# Executable checks on the store layer (task #97 P2a)

`#guard`s, not proofs: these run the real `intern`/`view`/`derived`/
`dropScratch` on hand-built terms and compare against con-leche's own
functions.  They are the cheapest possible guard against the class of bug the
proofs cannot see — a `derOfView` formula that is *self-consistently* wrong,
or a tag constant that collides.

Everything here is kernel-reduced, so it is a claim the build checks, not an
`#eval` print.
-/
import ConRon.Arena.Denote

namespace ConRon.Arena

open ConLeche

/-! ## A hand-built arena

`Sort 0`, `Sort 1`, the name `foo`, `foo.{0}` and a few applications, interned
into the persistent tier. -/

/-- con-leche: none — the P2a fixture: an arena plus the handles the checks
below name.  Built with explicit `let`s, in the order the parser would. -/
private def fixture :
    EStore × LIdx × LIdx × NIdx × LsIdx × EIdx × EIdx × EIdx × EIdx :=
  let st := EStore.empty
  let (st, z) := st.internLevel .zero
  let (st, one) := st.internLevel (.succ z)
  let (st, anon) := st.internName .anonymous
  let (st, foo) := st.internName (.str anon "foo")
  let (st, us) := st.internLevels [z]
  let (st, s0) := st.intern (.sort z)
  let (st, s1) := st.intern (.sort one)
  let (st, c) := st.intern (.const foo us)
  let (st, ap) := st.intern (.app c s0)
  (st, z, one, foo, us, s0, s1, c, ap)

private def fst : EStore := fixture.1
private def hZ : LIdx := fixture.2.1
private def hOne : LIdx := fixture.2.2.1
private def hFoo : NIdx := fixture.2.2.2.1
private def hUs : LsIdx := fixture.2.2.2.2.1
private def hS0 : EIdx := fixture.2.2.2.2.2.1
private def hS1 : EIdx := fixture.2.2.2.2.2.2.1
private def hC : EIdx := fixture.2.2.2.2.2.2.2.1
private def hAp : EIdx := fixture.2.2.2.2.2.2.2.2

/-- The con-leche values the fixture's handles are supposed to denote. -/
private def eS0 : Expr := .sort .zero
private def eS1 : Expr := .sort (.succ .zero)
private def nFoo : ConLeche.Name := .str .anonymous "foo"
private def eC : Expr := .const nFoo [.zero]
private def eAp : Expr := .app eC eS0

/-! ## The handle layout round-trips -/

#guard hS0.tag == ETag.sort
#guard hAp.tag == ETag.app
#guard hC.tag == ETag.const
#guard hS0.isPersistent
#guard hAp.isPersistent
#guard hS0.index == 0
#guard hS1.index == 1

/-! ## Interning is hash-consing: the same node gives the same handle -/

#guard
  let (st, a) := fst.intern (.app hC hS0)
  let (_, b) := st.intern (.app hC hS0)
  a == b && a == hAp

#guard
  let (_, a) := fst.intern (.sort hZ)
  a == hS0

#guard (fst.internLevel (.succ hZ)).2 == hOne
#guard (fst.internName (.str (fst.internName .anonymous).2 "foo")).2 == hFoo

/-! ## Cross-tier dedup: a persistent node is never re-interned into scratch -/

#guard
  let st := fst.enableScratch
  let (_, a) := st.intern (.app hC hS0)
  a == hAp && a.isPersistent

#guard
  let st := fst.enableScratch
  let (st, a) := st.intern (.app hS0 hS0)
  let (_, b) := st.intern (.app hS0 hS0)
  a == b && !a.isPersistent

/-! ## `view` decodes what was interned -/

#guard fst.view hAp == some (.app hC hS0)
#guard fst.view hS0 == some (.sort hZ)
#guard fst.view hC == some (.const hFoo hUs)

/-! ## The denotation is con-leche's own value -/

#guard denoteE fst hS0 == some eS0
#guard denoteE fst hS1 == some eS1
#guard denoteE fst hC == some eC
#guard denoteE fst hAp == some eAp
#guard denoteN fst.ns hFoo == some nFoo
#guard denoteLs fst.lss hUs == some [Level.zero]

/-! ## The derived column IS `ConLeche.Expr.data` of the denotation

This is `derived_exact` (`WFProofs.lean`) computed on both sides: the arena's
`O(1)` recurrence against con-leche's `@[computed_field]`. -/

#guard fst.derived hS0 == eS0.data
#guard fst.derived hS1 == eS1.data
#guard fst.derived hC == eC.data
#guard fst.derived hAp == eAp.data
#guard fst.ns.derived hFoo == nFoo.hashData
#guard (fst.ls.derived hZ).hash == Level.zero.hashData
#guard (fst.ls.derived hOne).hash == (Level.succ .zero).hashData
#guard (fst.lss.derived hUs).hash == levelsHash [Level.zero]
#guard (fst.lss.derived hUs).hasParam == levelsHaveParam [Level.zero]

/-! ### A binder, a bvar and a `letE`, whose `data` exercises the ranges -/

private def fixture2 : EStore × EIdx × EIdx :=
  let st := fst
  let (st, b0) := st.intern (.bvar 0)
  let (st, lam) := st.intern (.lam hS0 b0 ⟨.never⟩)
  (st, b0, lam)

private def st2 : EStore := fixture2.1
private def hB0 : EIdx := fixture2.2.1
private def hLam : EIdx := fixture2.2.2

private def eB0 : Expr := .bvar 0
private def eLam : Expr := .lam eS0 eB0 ⟨.never⟩

#guard denoteE st2 hB0 == some eB0
#guard denoteE st2 hLam == some eLam
#guard st2.derived hB0 == eB0.data
#guard st2.derived hLam == eLam.data

/-! ## `dropScratch` invalidates scratch handles and keeps persistent ones -/

private def fixture3 : EStore × EIdx :=
  let st := fst.enableScratch
  let (st, a) := st.intern (.app hS0 hS0)
  (st, a)

private def st3 : EStore := fixture3.1
private def hScr : EIdx := fixture3.2

#guard !hScr.isPersistent
#guard denoteE st3 hScr == some (.app eS0 eS0)
#guard denoteE st3 hAp == some eAp

#guard denoteE st3.dropScratch hScr == none
#guard st3.dropScratch.view hScr == none
#guard denoteE st3.dropScratch hAp == some eAp
#guard st3.dropScratch.view hAp == fst.view hAp
#guard st3.dropScratch.scratchOn == false

/-! A persistent handle's *bits* are unchanged by the bracket — the point of
putting the tier bit above the index (DESIGN §8.3, con-leche's lesson 6). -/
#guard (fst.enableScratch.intern (.sort hZ)).2.word == hS0.word

end ConRon.Arena

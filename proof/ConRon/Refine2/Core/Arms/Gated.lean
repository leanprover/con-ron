/-
# `ConRon.Refine2.Core.Arms.Gated` — the gated body at a stuck tag

**Task #97-P5-Arms**, amended by task #97-P5-Core-2.  This was
`BodyRel.stuckGatedCore`, the only field of either relation that mentions no
Rust at all: a statement about the TWIN,

    whnfCoreStuckTag h = true → (whnfCoreBodyGated mode r lfe d h).run lst
                                  = .ok (h, lst)

and it exists because task #97-P6-7's lever 2 hoisted the "the answer IS the
argument" test out of `whnfCoreBody` in the PORT — `knot_whnf_core` answers
`Ok(e.dup2())` off `whnf_core_stuck_tag` before it even looks at the lane —
while the twin hoisted it into the memoized slot only, so `coreKnotGated`'s
`whnfCore` slot is `whnfCoreBodyGated … d e` with no such test.  Task
#97-P5-Core's finding 12 names the pair; this is its first half, and
`whnfCoreStuckTag`'s own doc comment states exactly this as the obligation.

**It is no longer a `BodyRel` field.**  Task #97-P5-Arms §11(b)'s second
one-line twin change (made by task #97-P5-Core-2) put the stuck-tag test in
`coreKnotGated`'s `| fuel + 1 =>` branch only, so both reduction slots now
test exactly where the port's `knot_*` do and `Core/Induction.lean` reads the
agreement off `coreKnotGated_succ_whnfCore_stuck` instead.  The fact below is
nonetheless true and stays proved: it is what the gated body's first clause
claims, and a gated-lane claims tower will want it.

**What it needed** is `Core/Arms/Sort.lean`'s `EStore_view_tagOf`: the four
tags the stuck test excludes (`app`, `proj`, `letE`, `bvar`) are exactly the
four views `whnfCoreBodyGated` does NOT answer with `pure e`, so the proof is
"the tag decides the view" plus a six-way `rfl`.  `StoreWF` is **not** used —
finding 15 again.
-/
import ConRon.Refine2.Core.Arms.Sort

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

set_option maxRecDepth 4000

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine2.ExprOps (EResolves)

/-- The four tags `whnfCoreStuckTag` rules out, as four disequalities. -/
theorem whnfCoreStuckTag_ne {h : EIdx} (hst : whnfCoreStuckTag h = true) :
    h.tag ≠ ETag.app ∧ h.tag ≠ ETag.proj ∧ h.tag ≠ ETag.letE ∧
      h.tag ≠ ETag.bvar := by
  rw [whnfCoreStuckTag] at hst
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hx <;> rw [hx] at hst <;> simp at hst

/-- **The gated lane's `whnfCore` body is the identity at a stuck tag.**  It
was `BodyRel.stuckGatedCore` until task #97-P5-Core-2; the gated `whnfCore` body
returns its argument at exactly the six views the port's hoisted tag test
accepts. -/
theorem bodyRel_stuckGatedCore {mode : ConLeche.CheckMode} {lfe : IFEnv}
    {h : EIdx} {d : Nat} {lst : AState}
    (_hwf : StoreWF lst.store) (hres : EResolves lst h)
    (hst : whnfCoreStuckTag h = true) (r : CoreFnsA) :
    (whnfCoreBodyGated mode r lfe d h).run lst = .ok (h, lst) := by
  obtain ⟨ne_app, ne_proj, ne_let, ne_bvar⟩ := whnfCoreStuckTag_ne hst
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hres
  have htag := EStore_view_tagOf hv
  show ((do
      let w ← Arena.view h
      match w with
      | .sort _ | .fvar _ _ | .forallE _ _ _ | .lam _ _ _ | .const _ _
      | .lit _ => pure h
      | .app f a => do
        let f' ← r.whnfCore d f
        whnfCoreAppGated mode r lfe d h (f' == f) f' a
      | .proj sn i pe => do
        let e0 ← r.whnf d pe
        let e' ← projLitToCtor r lfe d e0
        match ← lfe.findProj? sn i with
        | some entry => do
          let hh ← getAppFn coreWalkFuel e'
          if hh.tag == ETag.const then
            match ← Arena.view hh with
            | .const c us => do
              let args ← getAppArgs coreWalkFuel e'
              match ← viewLsLen us with
              | none => failDanglingLs
              | some usl =>
              let fok ← entry.fireOk us
              if c = entry.ctor ∧ i < entry.numFields ∧
                  args.length = entry.numParams + entry.numFields ∧
                  usl = entry.levelParams.length ∧ fok = true then do
                let b0 ← internE (.bvar 0)
                let arg := args.getD (entry.numParams + i) b0
                if ← projCertAt r lfe d mode.verifiedChecks mode.betaGate c us
                    args then
                  r.whnfCore d arg
                else internE (.proj sn i e')
              else internE (.proj sn i e')
            | _ => internE (.proj sn i e')
          else internE (.proj sn i e')
        | none => internE (.proj sn i e')
      | .letE _ _ _ =>
        Arena.fail (.internal "whnfCore: `let` in an annotated expression")
      | .bvar _ =>
        Arena.fail (.notImplemented "whnf beyond the supported fragment"))
      : AM EIdx).run lst = _
  rw [am_run_bind,
    show (Arena.view h).run lst
        = (match lst.store.view h with
           | some w => Except.ok (w, lst)
           | none => Except.error (Arena.CheckError.internal
               "arena: dangling expression handle")) from by
      show ((match lst.store.view h with
              | some w => (pure w : AM ENodeView)
              | none => Arena.fail
                  (.internal "arena: dangling expression handle")).run lst) = _
      cases lst.store.view h <;> rfl,
    hv]
  cases v with
  | sort _ => rfl
  | fvar _ _ => rfl
  | forallE _ _ _ => rfl
  | lam _ _ _ => rfl
  | const _ _ => rfl
  | lit _ => rfl
  | app _ _ => exact absurd htag ne_app
  | proj _ _ _ => exact absurd htag ne_proj
  | letE _ _ _ => exact absurd htag ne_let
  | bvar _ => exact absurd htag ne_bvar

section Axioms

/-- info: 'ConRon.Refine2.bodyRel_stuckGatedCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bodyRel_stuckGatedCore

end Axioms

end ConRon.Refine2

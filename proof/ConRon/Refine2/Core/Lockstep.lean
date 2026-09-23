/-
# `ConRon.Refine2.Core.Lockstep` — the knot's lockstep outcome, locally

**Task #97-P5-Core round 4.**  `AOut` over `AStateRel₀` and without `Ext`: the
shape the Core tier's `KnotRel`/`BodyRel` are stated at since the
coordinator's ruling (i) moved `StoreWF` and `Ext` out of Theorem 2.  The
tier-wide versions belong to the foundation agent of the lockstep migration
(`Refine2/Shape.lean`); these carry a `K` prefix so that the two cannot
collide, and they are retired in favour of the tier's own when it lands.
-/
import ConRon.Refine2.Shape

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The lockstep outcome

`AOut` over `AStateRel₀` and without `Ext` or a `WF` slot: what a Theorem-2
statement concludes once the twin's own invariants (`StoreWF`, and `Ext`,
which is a statement about denotation) are Theorem 1's.  The Core tier's
`KnotRel`/`BodyRel` are stated with it; `KSim.toSim` is the projection back
for a consumer that still wants `Sim`, given the twin's two facts from
elsewhere. -/

/-- The lockstep obligation a Rust outcome puts on the twin's run. -/
def KOut {α β : Type} (A : α → β) (pers : arena.store.PersTier)
    (o : core.result.Result α kernel.core_types.CheckError)
    (st' : arena.monad.AState)
    (x : Except Arena.CheckError (β × AState)) : Prop :=
  match o with
  | .Ok r => ∃ lst', x = .ok (A r, lst') ∧ AStateRel₀ pers st' lst' ∧
      AStateInv pers st'
  | .Err e => AErrSim e x

theorem KOut.ok {α β : Type} {A : α → β} {r : α}
    {pers : arena.store.PersTier} {lst' : AState} {st' : arena.monad.AState}
    {x : Except Arena.CheckError (β × AState)}
    (hx : x = .ok (A r, lst')) (hrel : AStateRel₀ pers st' lst')
    (hinv : AStateInv pers st') : KOut A pers (.Ok r) st' x :=
  ⟨lst', hx, hrel, hinv⟩

theorem KOut.err {α β : Type} {A : α → β} {e : kernel.core_types.CheckError}
    {pers : arena.store.PersTier} {st' : arena.monad.AState}
    {x : Except Arena.CheckError (β × AState)} (h : AErrSim e x) :
    KOut A pers (.Err e) st' x := h

theorem KOut.of_eq {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {o : core.result.Result α kernel.core_types.CheckError}
    {st' : arena.monad.AState} {x y : Except Arena.CheckError (β × AState)}
    (h : KOut A pers o st' x) (hxy : y = x) : KOut A pers o st' y := by
  rw [hxy]; exact h

/-- Every `AOut` is a lockstep outcome. -/
theorem AOut.toK {α β : Type} {A : α → β} {WF : α → Prop}
    {pers : arena.store.PersTier} {lst : AState}
    {o : core.result.Result α kernel.core_types.CheckError}
    {st' : arena.monad.AState} {x : Except Arena.CheckError (β × AState)}
    (h : AOut A WF pers lst o st' x) : KOut A pers o st' x := by
  cases o with
  | Err e => exact h
  | Ok r =>
    obtain ⟨lst', hx, h1, h2, -⟩ := h
    exact ⟨lst', hx, h1.to₀, h2⟩

/-- The lockstep simulation statement for a state-threading Rust function. -/
def KSim {α β : Type} (A : α → β) (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result α kernel.core_types.CheckError × arena.monad.AState)
    (x : AM β) : Prop :=
  KOut A pers o.1 o.2 (x.run lst)

theorem KSim.apply {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {lst : AState} {r : α} {st' : arena.monad.AState} {x : AM β}
    (h : KSim A pers lst (.Ok r, st') x) :
    ∃ lst', x.run lst = .ok (A r, lst') ∧ AStateRel₀ pers st' lst' ∧
      AStateInv pers st' := h

theorem KSim.apply_err {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {lst : AState} {e : kernel.core_types.CheckError} {st' : arena.monad.AState}
    {x : AM β} (h : KSim A pers lst (.Err e, st') x) : AErrSim e (x.run lst) := h

theorem Sim.toK {α β : Type} {A : α → β} {WF : α → Prop}
    {pers : arena.store.PersTier} {lst : AState}
    {o : core.result.Result α kernel.core_types.CheckError × arena.monad.AState}
    {x : AM β} (h : Sim A WF pers lst o x) : KSim A pers lst o x := AOut.toK h

/-- **The projection back to `Sim`**, for a consumer that still wants
`AStateRel` and `Ext`: the twin's two facts about its own run — the store it
ends at is well formed and extends the one it started at — are supplied from
outside (Theorem 1), not threaded through the lockstep statement. -/
theorem KSim.toSim {α β : Type} {A : α → β} {WF : α → Prop}
    {pers : arena.store.PersTier} {lst : AState}
    {o : core.result.Result α kernel.core_types.CheckError × arena.monad.AState}
    {x : AM β} (h : KSim A pers lst o x)
    (htw : ∀ b lst', x.run lst = .ok (b, lst') →
      StoreWF lst'.store ∧ Ext lst.store lst'.store)
    (hwf : ∀ r, o.1 = .Ok r → WF r) : Sim A WF pers lst o x := by
  obtain ⟨o1, o2⟩ := o
  cases o1 with
  | Err e => exact h
  | Ok r =>
    obtain ⟨lst', hx, h1, h2⟩ := h
    obtain ⟨hw, he⟩ := htw _ _ hx
    exact ⟨lst', hx, h1.of₀ hw, h2, he, hwf r rfl⟩

/-- The lockstep outcome of a twin action that cannot fail and answers `()`. -/
def KSimS (pers : arena.store.PersTier) (lst : AState)
    (st' : arena.monad.AState) (x : AM Unit) : Prop :=
  ∃ lst', x.run lst = .ok ((), lst') ∧ AStateRel₀ pers st' lst' ∧
    AStateInv pers st'

theorem KSimS.mk {pers : arena.store.PersTier} {lst lst' : AState}
    {st' : arena.monad.AState} {x : AM Unit}
    (hx : x.run lst = .ok ((), lst')) (hrel : AStateRel₀ pers st' lst')
    (hinv : AStateInv pers st') : KSimS pers lst st' x := ⟨lst', hx, hrel, hinv⟩

theorem KSimS.apply {pers : arena.store.PersTier} {lst : AState}
    {st' : arena.monad.AState} {x : AM Unit} (h : KSimS pers lst st' x) :
    ∃ lst', x.run lst = .ok ((), lst') ∧ AStateRel₀ pers st' lst' ∧
      AStateInv pers st' := h

end ConRon.Refine2

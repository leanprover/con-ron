/-
TEMPORARY (task #97-T2-TACTIC): a verbatim copy of the lockstep definitions
slice (`AStateRel₀`, `AOut₀`, `Sim₀`, `SimS₀`) the parallel migration lane is
landing in `AbsState.lean`/`Shape.lean`.  Deleted when that slice is on `arena`.
-/
import ConRon.Refine2.Shape

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine2
open ConRon.Arena

structure AStateRel₀ (pers : arena.store.PersTier) (rs : arena.monad.AState)
    (ls : AState) : Prop where
  store : StoreRel pers rs.store ls.store
  memos : MemosRel rs.memos ls.memos
  caches : CachesRel rs.caches ls.caches
  pins : PinsRel rs.pins ls.pins

theorem AStateRel.to₀ {pers : arena.store.PersTier} {rs : arena.monad.AState}
    {ls : AState} (h : AStateRel pers rs ls) : AStateRel₀ pers rs ls :=
  ⟨h.store, h.memos, h.caches, h.pins⟩

def AOut₀ {α β : Type} (A : α → β) (pers : arena.store.PersTier)
    (o : core.result.Result α kernel.core_types.CheckError)
    (st' : arena.monad.AState)
    (x : Except Arena.CheckError (β × AState)) : Prop :=
  match o with
  | .Ok r => ∃ lst', x = .ok (A r, lst') ∧ AStateRel₀ pers st' lst' ∧
      AStateInv pers st'
  | .Err e => AErrSim e x

def Sim₀ {α β : Type} (A : α → β) (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result α kernel.core_types.CheckError × arena.monad.AState)
    (x : AM β) : Prop :=
  AOut₀ A pers o.1 o.2 (x.run lst)

def SimS₀ (pers : arena.store.PersTier) (lst : AState)
    (st' : arena.monad.AState) (x : AM Unit) : Prop :=
  ∃ lst', x.run lst = .ok ((), lst') ∧ AStateRel₀ pers st' lst' ∧
    AStateInv pers st'

end ConRon.Refine2

import ConRon.Refine2.Core.LS.Prims
open ConRon.Arena
namespace ConRon.Refine2.Lockstep

theorem EStore_view_of_tag_app (st : EStore) (i : EIdx) (hi : i.tag = ETag.app) :
    st.view i = (st.viewApp i).map (fun p => ENodeView.app p.1 p.2) := by
  have key : ∀ t : ETables, t.get i = (t.getApp i).map (fun p => ENodeView.app p.1 p.2) := by
    intro t
    simp only [ETables.get, ETables.getApp, hi, Option.map_map]
    simp (config := {decide := true}) only [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app,
      ETag.isBind, ETag.lam, ETag.forallE, if_false, if_true]
    rfl
  rw [EStore.view, EStore.viewApp,
    if_neg (by rw [ETag.isBind, hi]; simp [ETag.lam, ETag.forallE, ETag.app])]
  by_cases hp : i.isPersistent
  · rw [if_pos hp, if_pos hp, EStore.persGetApp]; exact key _
  · rw [if_neg hp, if_neg hp]
    by_cases hs : st.scratchOn
    · rw [if_pos hs, if_pos hs]; exact key _
    · rw [if_neg hs, if_neg hs]; rfl
end ConRon.Refine2.Lockstep

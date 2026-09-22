import ConRon.Arena

namespace ConRon.Arena
open ConLeche

def promoteNNodeSpec' (m : PMemo) (fuel : Nat) : NNodeView → AM (PMemo × NIdx)
  | .anonymous => do pure (m, ← internPersistentN .anonymous)
  | .str p s => do
    let (m, p) ← promoteN m fuel p
    pure (m, ← internPersistentN (.str p s))
  | .num p n => do
    let (m, p) ← promoteN m fuel p
    pure (m, ← internPersistentN (.num p n))

theorem promoteN_unfold' (m : PMemo) (fuel : Nat) (h : NIdx) :
    promoteN m (fuel + 1) h = (do
      if h.isPersistent then pure (m, h)
      else
        match m.nM[h]? with
        | some r => pure (m, r)
        | none => do
          let (m, r) ← promoteNNodeSpec' m fuel (← viewN h)
          pure ({ m with nM := m.nM.insert h r }, r)) := by
  rw [promoteN]
  split
  · rfl
  · cases hm : m.nM[h]? with
    | some r => simp only [hm]
    | none =>
      simp only [hm]
      congr 1
      funext v
      cases v <;> simp only [promoteNNodeSpec', bind_assoc, pure_bind]

end ConRon.Arena

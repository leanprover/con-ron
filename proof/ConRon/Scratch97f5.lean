import ConRon.Bridge.Frontend.Lines
namespace ConRon.Bridge.Frontend
set_option autoImplicit false
open ConLeche ConRon.Arena ConRon.Arena.Frontend

example {s s' : AState} {sd sd' : StateD}
    {block : List IConstantInfo} {nP : Nat}
    (hrun : noteDecl sd (.indDecl block nP) s = .ok (sd', s')) : True := by
  rw [noteDecl] at hrun
  obtain ⟨cvs, s₁, hcvs, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hv2, hst2⟩ := AM.pure_ok hrest
  trace_state
  trivial

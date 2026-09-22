/-!
The spec layer: the `@[spec]` theorems of the primitives, plus `_exact` and
`_run`, so the fixture exercises every recognised suffix.
-/

namespace ConRon.Bridge

@[spec] theorem derivedE_spec (s₀ : AState) (h : EIdx) : True := by trivial

@[spec] theorem viewApp_spec (s₀ : AState) (h : EIdx) : True := by trivial

@[spec] theorem internE_specV (s₀ : AState) (v : ENodeView) : True := by trivial

theorem exprPtrBEq_exact {a b : EIdx} : True := by trivial

theorem isBoolTrue_spec (s₀ : AState) (h : EIdx) : True := by trivial

theorem flushCaches_run {s s' : AState} : True := by trivial

theorem iotaRec_spec (h : EIdx) : True := by
  sorry

theorem promoteN_spec (n : NIdx) : True := by
  sorry

/-- An unrecognised suffix on a twin that has nothing else: `PMemo.empty`
reads "unstated", and the self-check counts it. -/
theorem PMemo.empty_ext : True := by trivial

end ConRon.Bridge

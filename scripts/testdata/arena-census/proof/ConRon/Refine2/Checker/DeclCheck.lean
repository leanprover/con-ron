namespace ConRon.Refine2

theorem check_decl_refines {pd : IDeclaration} : True := by
  sorry

theorem check_decls_pure_refines {ds : List IDeclaration} : True := by
  sorry

/-- The `_no_claim` shape: stated AND closed, flagged `N` in the table. -/
theorem rebound_error_no_claim {n : NIdx} : True := by trivial

theorem builtin_prelude_text_refines : True := by
  sorry

end ConRon.Refine2

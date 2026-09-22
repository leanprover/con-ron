/-!
The store tier's spec layer, whose lemmas are `_abs` and `_run` rather than
`_refines`.  A twin whose only Refine2 theorem has this shape reads "T2
unstated", and the T2 self-check line is what says a theorem naming the
function exists after all.
-/

namespace ConRon.Refine2

theorem estore_view_app_abs {i : EIdx} : True := by trivial

theorem derived_e_run {h : EIdx} : True := by trivial

end ConRon.Refine2

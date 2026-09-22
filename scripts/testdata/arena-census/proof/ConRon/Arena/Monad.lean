namespace ConRon.Arena

/-- The derived word reader. -/
@[inline] def derivedE (h : EIdx) : AM UInt64 := pure 0

/-- The monadic `app` projection. -/
@[inline] def viewApp (h : EIdx) : AM (Option (EIdx × EIdx)) := pure none

/-- The node intern, whose bridge theorem is the `_specV` spelling. -/
def internE (v : ENodeView) : AM EIdx := pure default

end ConRon.Arena

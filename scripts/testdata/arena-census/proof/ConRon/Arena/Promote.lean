namespace ConRon.Arena

/-- The promotion memo. -/
def PMemo.empty : PMemo := {}

/-- The name promotion. -/
def promoteN (n : NIdx) : AM NIdx := pure n

end ConRon.Arena

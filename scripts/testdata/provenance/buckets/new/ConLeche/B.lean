namespace ConLeche

/-- Five moves. -/
def five : Nat := 5

/-- Six moves, and its doc says so. -/
def six : Nat := 6

/-- Seven moves and changes. -/
def seven : Nat := 7 + 0

namespace Bar

/-- Eight's namesake, in another namespace. -/
def helper : Nat := 80

end Bar

/-- Twelve, in a file that is deleted. -/
def twelve : Nat := 12

end ConLeche

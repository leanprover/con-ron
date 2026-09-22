namespace ConRon.Arena

/-- (P) The walk fuel. -/
def coreWalkFuel : Nat := 4000000000

/-- The `Bool.true` guard. -/
def isBoolTrue (h : EIdx) : AM Bool := pure false

/-- The per-declaration cache flush. -/
def flushCaches : AM Unit := pure ()

/-- The iota rule: cited by two Rust functions, one of which has no lemma. -/
def iotaRec (h : EIdx) : AM (Option EIdx) := pure none

end ConRon.Arena

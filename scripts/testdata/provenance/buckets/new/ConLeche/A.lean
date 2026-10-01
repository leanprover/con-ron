namespace ConLeche

/-- A new declaration up front. -/
def zero : Nat := 0

/-- One. -/
def one : Nat := 1

/-- Two, reworded. -/
def two : Nat := 2

def three : Nat := 3  -- an end-of-line comment, reworded

/-- Four. -/
def four : Nat := 4 + 0

inductive Expr where
  | a

/-- The trap (task #98): renamed upstream, and `Expr` is a prefix of it. -/
def Expr.beqGoX : Expr → Bool
  | .a => true

/-- `subst` with a `where` clause, reworded. -/
def subst (n : Nat) : Nat := go n
where
  go (n : Nat) : Nat := n

end ConLeche

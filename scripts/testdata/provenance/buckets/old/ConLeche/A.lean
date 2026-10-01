namespace ConLeche

/-- One. -/
def one : Nat := 1

/-- Two. -/
def two : Nat := 2

def three : Nat := 3  -- an end-of-line comment

/-- Four. -/
def four : Nat := 4

/-- Five moves. -/
def five : Nat := 5

/-- Six moves, doc changes. -/
def six : Nat := 6

/-- Seven moves and changes. -/
def seven : Nat := 7

namespace Foo

/-- Eight. -/
def helper : Nat := 8

end Foo

/-- Nine is deleted. -/
def nine : Nat := 9

inductive Expr where
  | a

/-- The trap (task #98): renamed upstream, and `Expr` is a prefix of it. -/
def Expr.beqGo : Expr → Bool
  | .a => true

/-- `subst` with a `where` clause. -/
def subst (n : Nat) : Nat := go n
where
  go (n : Nat) : Nat := n

end ConLeche

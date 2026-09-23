/-
The calibration fixture of `#sorry_frontier` (task #97-FRONTIER): a closure
whose frontier, fan-ins and reaches are known by hand.

* `a`, `b` and `f` (its `decreasing_by`, which lands in an auxiliary
  `f.proof_*`/`f._unary` constant and must be reported as `f`) are the frontier;
* `d` and `e` reach `sorryAx` only through `a` (fan-in 2), `g` only through
  `f` (fan-in 1), `c` through both `a` and `b` (fan-in to neither);
* reach counts the owner itself: `a` is reached by `a c d e top`.
-/
import ConRon.Tools.Frontier

namespace ConRon.Tools.FrontierTest

#guard_msgs (drop warning) in
theorem a : 1 = 1 := sorry
#guard_msgs (drop warning) in
theorem b : 2 = 2 := sorry
theorem c : 1 = 1 ∧ 2 = 2 := ⟨a, b⟩
theorem d : 1 = 1 := a
theorem e : 1 = 1 := d
#guard_msgs (drop warning) in
def f (n : Nat) : Nat := if n = 0 then 0 else f (n - 1)
decreasing_by sorry
theorem g : f 0 = 0 := by unfold f; simp
theorem clean : 3 = 3 := rfl
theorem top : (1 = 1 ∧ 2 = 2) ∧ 1 = 1 ∧ f 0 = 0 ∧ 3 = 3 := ⟨c, e, g, clean⟩

/--
info: frontier ConRon.Tools.FrontierTest.top: 3 items in 1 modules, 8 tainted decls; top ConRon.Tools.FrontierTest.a (fan-in 2, reach 5); dead weight 0
  axioms: [propext, sorryAx, Quot.sound]
  non-standard axioms: none
  opened 9 constants (the sorry-tainted part of the closure)
  per module:
       3  ConRon/Tools/FrontierTest.lean
  top 3 by fan-in — fan-in, reach; then the item's module: lines, and the direct-sorry decls OFF the frontier in that module / its lane (large = the item is a sorried top whose subtree is not yet in the closure):
        2     5     45L    0    0  ConRon.Tools.FrontierTest.a  ConRon/Tools/FrontierTest.lean:16
        1     3     45L    0    0  ConRon.Tools.FrontierTest.f  ConRon/Tools/FrontierTest.lean:23
        0     3     45L    0    0  ConRon.Tools.FrontierTest.b  ConRon/Tools/FrontierTest.lean:18
-/
#guard_msgs in
#sorry_frontier top

end ConRon.Tools.FrontierTest

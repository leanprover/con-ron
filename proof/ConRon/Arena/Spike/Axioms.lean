/-
# The spike's axiom check (task #97s)

`#print axioms` on the two theorems experiment A closed.  Measured:

* `memoWhnfCore_spec` (experiment A, subject 3) and `memoWhnfCore_run_hand`
  (experiment B) are **sorry-free**;
* `instantiate1A_spec` and `instantiate1Top_spec` (subject 1) depend on
  `sorryAx` *today*, through `EStore.intern_spec` — whose `intern_wf` half
  is one of task #97a's thirteen open store lemmas.  Nothing the spike wrote
  is open: `ExpA.lean` and `ExpA3.lean` contain no `sorry`.
-/
import ConRon.Arena.Spike.ExpA3
import ConRon.Arena.Spike.ExpB

namespace ConRon.Arena.Spike

#print axioms instantiate1A_spec
#print axioms instantiate1Top_spec
#print axioms memoWhnfCore_spec
#print axioms memoWhnfCore_run_hand

end ConRon.Arena.Spike

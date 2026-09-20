/-
# The spike's axiom check (task #97s)

`#print axioms` on everything the spike closed.  Measured:

* **round 2's theorems are all sorry-free** — `instantiate1_C1`,
  `instantiate1_C2`, `instantiate1_D`, `instantiate1_D_of_C1_C2`,
  `whnfCoreAppArm_spec` and `ExpAFast`'s three — `propext`,
  `Classical.choice`, `Quot.sound` and nothing else.  None of them goes
  through task #97a's `EStore`;
* `memoWhnfCore_spec` (experiment A, subject 3) and `memoWhnfCore_run_hand`
  (experiment B) are sorry-free;
* `instantiate1A_spec` and `instantiate1Top_spec` (subject 1, over the real
  `EStore`) are sorry-free too since task #97a closed `EStore.intern_spec`.
  The whole spike is sorry-free.
* **round 3's two C1 variants are sorry-free** — `instantiate1_C1_idiom`
  (the task-#70/#71 refinement idiom) and `bvar_demo` (Aeneas's `step*`).
-/
import ConRon.Arena.Spike.ExpA2
import ConRon.Arena.Spike.ExpA3
import ConRon.Arena.Spike.ExpB
import ConRon.Arena.Spike.ExpCD
import ConRon.Arena.Spike.ExpAFast
import ConRon.Arena.Spike.ExpC1Step

namespace ConRon.Arena.Spike

#print axioms instantiate1A_spec
#print axioms instantiate1Top_spec
#print axioms memoWhnfCore_spec
#print axioms memoWhnfCore_run_hand
#print axioms whnfCoreAppArm_spec

-- round 2: experiments C1, C2 and D, and the composition that makes them
-- a comparison
#print axioms instantiate1_C1
#print axioms instantiate1_C2
#print axioms instantiate1_D
#print axioms instantiate1_D_of_C1_C2

-- round 2: the elaboration recipe
#print axioms Fast.instantiate1B_spec
#print axioms Fast.instantiate1BTop_spec
#print axioms Fast.instantiate1BTop_run

-- round 3: C1 by the `Refine`-tier idiom, and the `step*` demonstration
#print axioms instantiate1_C1_idiom
#print axioms instantiate1_C1_idiom_wf
#print axioms bvar_demo

end ConRon.Arena.Spike

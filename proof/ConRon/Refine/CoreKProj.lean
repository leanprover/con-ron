/-
`FEnv.findProj?`, derived (task #49, `CORE_PLAN.md` step 4).

`CoreKBase.lean`'s `FindAgree` is *find*-agreement only, so the projection-table
read the `core_k.rs` shape guards and the projection inference clauses do —
`fenv::find_proj` — has to be derived from it rather than assumed.  That needs
two `env.rs` refinements, `proj_table_name` (in `CoreKBase.lean`) and
`proj_table_entry` (here), and then the three `fenv.rs` index walks that sit on
top of `find_proj`/`find`.

**TO BE UNIFIED WITH TASK #46**: `env::proj_table_entry` belongs in
`Refine/Env.lean` and `fenv::find_proj`/`tower_slots_all_f`/`rec_slots_all_f`
in `Refine/FEnv.lean`.  They are here because step 4 cannot be stated without
them and steps 1 and 2 are being landed in parallel.
-/
import ConRon.Refine.CoreKBase
import ConLeche.Kernel.FEnv

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine

/-! ## The two index walks over `find_proj`/`find`

`fenv::tower_slots_all_f` and `fenv::rec_slots_all_f` are the `(List.range nF).all`
of the cited `FEnv.lean:98-110`, as the index recursion §3.4 asks for; the
`*_from` lemmas are stated on `List.range' j (nF - j)` in the task-#5 shape. -/

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

end ConRon.Refine

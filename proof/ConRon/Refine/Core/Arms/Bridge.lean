/-
# The two `StateC` ingredients, discharged where they can be (task #55)

`Refine/StateC.lean` (task #52) left two things as *named hypotheses* rather
than duplicating other files' work:

* **`InstantiateListRefines`** — the memoised `instantiate_list` walk refines
  `ExprC.instantiateList`.  Task #51 owned the statement and left it a `sorry`;
  **task #54 closed it**, so it is now a theorem and this file discharges the
  hypothesis once, for every arm that calls `inst_list_m`.
* **`InstLevelParamsRefines`** — likewise for `inst_level_params`.

`InstCSize` (`StateC.lean:96`) is the *third* ingredient and it is **not**
dischargeable here: it is `StateRel`'s missing `len` clause, and `StateRel` —
a lookup agreement, `∀ k, (toFun m k).map absV = s[absK k]?` — does not imply
it (a `Std.HashMap` may hold keys outside `absK`'s image without contradicting
any lookup).  StateC.lean's own note says where it belongs: *"to be unified
into `State.lean`'s `StateRel`"*.  Until it is, an arm that calls
`inst_list_m` cannot thread it, because `Sim` carries `StateRel`/`StateWF` and
nothing else — see the task #55 entry in DESIGN.md and the `sorry` notes in
`Arms/App.lean` and the spine files.
-/
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.ExprOpsCSubst
import ConRon.Refine.ExprOpsCAbs

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

/-- `Refine/StateC.lean:762`'s hypothesis, discharged from task #54's
`ExprOpsC.instantiate_list_refines`. -/
theorem instantiateListRefines : StateC.InstantiateListRefines := by
  intro e vs d r he hvs h
  exact ExprOpsC.instantiate_list_refines he hvs h

/-- `Refine/StateC.lean:777`'s hypothesis, discharged from task #51/#54's
`ExprOpsC.inst_level_params_refines`. -/
theorem instLevelParamsRefines : StateC.InstLevelParamsRefines := by
  intro ks us e r hks hus he h
  exact ExprOpsC.inst_level_params_refines hks hus he h

end ConRon.Refine.Core

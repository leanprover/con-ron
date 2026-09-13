import ConRon.Refine.IndAbs
import ConRon.Refine.ExprOpsSpine
import ConRon.Refine.ExprOpsSubst
import ConRon.Refine.ExprOpsFields
import ConRon.Refine.ExprOpsMeta
import ConRon.Refine.CoreKBase
import ConRon.Refine.CoreKVec
import ConRon.Refine.BasisNames

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.kernel.inductives
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Probe
#check @ConRon.Refine.ExprOps.absBinders
#check @ConRon.Refine.ExprOps.BindersWF
#check @ConRon.Refine.ExprOps.vec_index_expr
#check @ConRon.Refine.ExprOps.vec_index_getElem?
#check @ConRon.Refine.HashMap.uscalar_add_eq
#check @ConRon.Refine.ExprOps.absExprs_push
#check @ConRon.Refine.ExprOps.exprsWF_push
#check @ConLeche.structPsAt
#check @ConLeche.structProjBodies
#check @ConRon.Refine.ExprOps.MemoInv
#check @ConRon.Refine.ExprOps.absKey
#check @ConRon.Refine.CoreK.append_exprs_refines
#check @ConRon.Refine.CoreK.expr_singleton_refines
#check @ConRon.Refine.CoreKBase.str_lit_step
#check @ConRon.Refine.BasisNames.reserved_basis_names_refines
end ConRon.Refine.Probe

/-
# `ConRon.Refine2.Promote.Intern` — Theorem 2 for `arena::intern`

**Task #97-P5-Checker**, deliverable 1's first half (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/intern.rs`: con-leche's pinned VALUES into the
store — the basis blocks, the standard- and compiler-trust axiom pins and the
`Nat`-operation pin variants, which DESIGN §8.7 rules (B) IMPORTS rather than
copies, so that the twins above this module (`Arena/Basis.lean`,
`Arena/StdAxioms.lean`, `Arena/TrustAxioms.lean`, `Arena/NatOpPinSet.lean`)
are one line each: *the con-leche constant, interned*.

## The twin is two modules, not one

`Arena/Intern.lean` is five wrappers; the WALK is
`Arena/Frontend/Readback.lean`'s intern direction (`internExprGo`,
`internCV`, `internCI`, `internCIList`, `internDecl`), because the modeller
seam needs exactly the same direction and wrote it memoised.  So the
`_go`-shaped Rust functions are stated against `Frontend.*` and the five
fresh-memo entries against `Arena/Intern.lean`'s own wrappers.

## The one thing this tier's statements need that no earlier tier did

**Every argument is a con-leche VALUE**, and `Refine/Abs.lean`'s abstractions
of those are exact on WELL-FORMED values only — `absName` on a `Name` whose
strings are valid code points, `absExpr` on an `Expr` whose literals and
binder metadata are, and so on up to `ConstantInfoWF` and `DeclarationWF`.
That is the same restriction `TblRel`'s `RelOn P` carries (task #97-P5-0's
rule 4) and it is why `EMemoRel`'s `P` is `ExprWF`.  Each statement therefore
carries the WF of its own subject; the callers are the pin modules, and
`Refine/Pins*.lean` is where a pin's well-formedness is proved — so the
obligation lands where it is already discharged.

## What these lemmas wait on

`Refine2/Specs.lean`'s **four transient walks** — `intern_name`,
`intern_level`, `intern_level_list`, `intern_levels` — and `intern_e` with its
per-constructor entries; task #97-P5-1 §8 lists all of them among the
thirty-two still open, and every proof here is the twin's clause peel over
them.  Nothing here waits on an idea.
-/
import ConRon.Refine2.Checker.Shape
import ConRon.Arena.Intern

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine (ExprWF ExprsWF NameWF NamesWF LevelWF LevelsWF
  ConstantValWF ConstantInfoWF ConstantInfosWF DeclarationWF RecRuleWF
  RecRulesWF IndCapsWF ProjTableWF RecRuleFireWF)
open ConRon.Refine.HashMap2 (Inv RelOn)

/-! ## The memo itself -/

/-- `arena::intern::memo_empty` is the twin's `(∅ : EMemo)`. -/
theorem memo_empty_refines {o}
    (hrun : arena.intern.memo_empty = ok o) :
    EMemoRel o (∅ : Frontend.EMemo) := by
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := kernel.expr.Expr.Insts.Con_ron_coreRonHashmapHashable) hrun
  exact ⟨ConRon.Refine.HashMap2.RelOn_empty hnone, hinv⟩

/-- `arena::intern::memo_get` is the twin's `m[e]?` — the probe extraction
rule 5 gave its own function. -/
theorem memo_get_refines {rm lm} {e : kernel.expr.Expr} {o}
    (hm : EMemoRel rm lm) (hwf : ExprWF e)
    (hrun : arena.intern.memo_get rm e = ok o) :
    o.map absEIdx = lm[ConRon.Refine.absExpr e]? := by
  sorry

/-! ## The expression walk

`Frontend.internExprGo`'s ten clauses: four leaves that do not touch the memo
(`bvar`, `sort`, `const`, `lit` — the store's own cons table already answers a
repeat in `O(1)`) and six compounds that probe it. -/

/-- `intern_expr_go` ⊑ `Frontend.internExprGo`. -/
theorem intern_expr_go_refines {pers st lst rm lm} {e : kernel.expr.Expr} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ExprWF e)
    (hrun : arena.intern.intern_expr_go pers st rm e = ok o) :
    SimEM absEIdx pers lst o (Frontend.internExprGo lm (ConRon.Refine.absExpr e)) := by
  sorry

/-- `intern_expr_node` is task #97-P6-2's Rust-only split of `intern_expr_go`'s
six compound arms past the probe (extraction rule 5: the `view`'s loans are
dead at the memo's join), so it is stated against the twin's own arm at a
MISS — which is the clause `intern_expr_go_refines` peels. -/
theorem intern_expr_node_refines {pers st lst rm lm} {e : kernel.expr.Expr} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ExprWF e)
    (hmiss : lm[ConRon.Refine.absExpr e]? = none)
    (hrun : arena.intern.intern_expr_node pers st rm e = ok o) :
    SimEM absEIdx pers lst o (Frontend.internExprGo lm (ConRon.Refine.absExpr e)) := by
  sorry

/-- `intern_expr` ⊑ `Arena.internExpr` — the fresh-memo entry. -/
theorem intern_expr_refines {pers st lst} {e : kernel.expr.Expr} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st) (hwf : ExprWF e)
    (hrun : arena.intern.intern_expr pers st e = ok o) :
    Sim absEIdx (fun _ => True) pers lst o (internExpr (ConRon.Refine.absExpr e)) := by
  sorry

/-- `intern_expr_list_go` ⊑ `Frontend.internExprList` at the cursor. -/
theorem intern_expr_list_go_refines {pers st lst rm lm}
    {es : alloc.vec.Vec kernel.expr.Expr} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ExprsWF es)
    (hrun : arena.intern.intern_expr_list_go pers st rm es i out = ok o) :
    SimEM (fun v => absEIdxL out ++ absEIdxL v) pers lst o
      (do let (m, hs) ← Frontend.internExprList lm (absExprLFrom es i)
          pure (m, absEIdxL out ++ hs)) := by
  sorry

/-- `intern_expr_list` ⊑ `Arena.internExprList`. -/
theorem intern_expr_list_refines {pers st lst}
    {es : alloc.vec.Vec kernel.expr.Expr} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st) (hwf : ExprsWF es)
    (hrun : arena.intern.intern_expr_list pers st es = ok o) :
    Sim absEIdxL (fun _ => True) pers lst o
      (internExprList (ConRon.Refine.absExprs es)) := by
  sorry

/-! ## The two handle-list walks that carry no memo

A name and a level are interned through `arena::monad`'s own cons tables, so
these two are plain `Sim`s at the cursor. -/

/-- `intern_name_list_go` ⊑ `Frontend.internNameList` at the cursor. -/
theorem intern_name_list_go_refines {pers st lst}
    {ns : alloc.vec.Vec kernel.name.Name} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hwf : NamesWF ns)
    (hrun : arena.intern.intern_name_list_go pers st ns i out = ok o) :
    Sim (fun v => absNIdxL out ++ absNIdxL v) (fun _ => True) pers lst o
      (do pure (absNIdxL out ++ (← Frontend.internNameList (absNameLFrom ns i)))) := by
  sorry

/-- `intern_name_list` ⊑ `Frontend.internNameList`. -/
theorem intern_name_list_refines {pers st lst}
    {ns : alloc.vec.Vec kernel.name.Name} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st) (hwf : NamesWF ns)
    (hrun : arena.intern.intern_name_list pers st ns = ok o) :
    Sim absNIdxL (fun _ => True) pers lst o
      (Frontend.internNameList (ConRon.Refine.absNames ns)) := by
  sorry

/-- `intern_level_list_go` ⊑ `Arena.internLevelList` at the cursor. -/
theorem intern_level_list_go_refines {pers st lst}
    {us : alloc.vec.Vec kernel.level.Level} {i : Std.Usize}
    {out : alloc.vec.Vec arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hwf : LevelsWF us)
    (hrun : arena.intern.intern_level_list_go pers st us i out = ok o) :
    Sim (fun v => absLIdxL out ++ absLIdxL v) (fun _ => True) pers lst o
      (do pure (absLIdxL out ++ (← internLevelList (absLevelLFrom us i)))) := by
  sorry

/-! ## The declaration layer

`Frontend/Readback.lean`'s intern direction, record for record.  The memo is
threaded through everything that can hold a term, and NOT through
`intern_caps` (an `IndCaps` holds one name and no term). -/

/-- `intern_cv_go` ⊑ `Frontend.internCV`. -/
theorem intern_cv_go_refines {pers st lst rm lm} {cv : kernel.env.ConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ConstantValWF cv)
    (hrun : arena.intern.intern_cv_go pers st rm cv = ok o) :
    SimEM absIConstantVal pers lst o
      (Frontend.internCV lm (ConRon.Refine.absConstantVal cv)) := by
  sorry

/-- `intern_cv` ⊑ `Arena.internCV`. -/
theorem intern_cv_refines {pers st lst} {cv : kernel.env.ConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hwf : ConstantValWF cv)
    (hrun : arena.intern.intern_cv pers st cv = ok o) :
    Sim absIConstantVal (fun _ => True) pers lst o
      (internCV (ConRon.Refine.absConstantVal cv)) := by
  sorry

/-- `intern_fire` ⊑ `Frontend.internFire`. -/
theorem intern_fire_refines {pers st lst rm lm} {f : kernel.env.RecRuleFire} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : RecRuleFireWF f)
    (hrun : arena.intern.intern_fire pers st rm f = ok o) :
    SimEM absIRecRuleFire pers lst o
      (Frontend.internFire lm (ConRon.Refine.absFire f)) := by
  sorry

/-- `intern_rule` ⊑ `Frontend.internRule`. -/
theorem intern_rule_refines {pers st lst rm lm} {rl : kernel.env.RecRule} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : RecRuleWF rl)
    (hrun : arena.intern.intern_rule pers st rm rl = ok o) :
    SimEM absIRecRule pers lst o
      (Frontend.internRule lm (ConRon.Refine.absRecRule rl)) := by
  sorry

/-- `intern_rules` ⊑ `Frontend.internRules` at the cursor. -/
theorem intern_rules_refines {pers st lst rm lm}
    {rs : alloc.vec.Vec kernel.env.RecRule} {i : Std.Usize}
    {out : alloc.vec.Vec arena.env.IRecRule} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : RecRulesWF rs)
    (hrun : arena.intern.intern_rules pers st rm rs i out = ok o) :
    SimEM (fun v => absIRecRuleL out ++ absIRecRuleL v) pers lst o
      (do let (m, hs) ← Frontend.internRules lm (absRecRuleLFrom rs i)
          pure (m, absIRecRuleL out ++ hs)) := by
  sorry

/-- `intern_caps` ⊑ `Frontend.internCaps` — no memo: an `IndCaps` holds one
name and no term. -/
theorem intern_caps_refines {pers st lst} {c : kernel.env.IndCaps} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st) (hwf : IndCapsWF c)
    (hrun : arena.intern.intern_caps pers st c = ok o) :
    Sim absIIndCaps (fun _ => True) pers lst o
      (Frontend.internCaps (ConRon.Refine.absIndCaps c)) := by
  sorry

/-- `intern_proj_table` ⊑ `Frontend.internProjTable`. -/
theorem intern_proj_table_refines {pers st lst rm lm}
    {t : kernel.env.ProjTable} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ProjTableWF t)
    (hrun : arena.intern.intern_proj_table pers st rm t = ok o) :
    SimEM absIProjTable pers lst o
      (Frontend.internProjTable lm (ConRon.Refine.absProjTable t)) := by
  sorry

/-- `intern_proj_table_rest` is the Rust-only tail of `intern_proj_table` past
its two name interns (extraction rule 5), so it is stated against the same
twin with those two handles already in hand. -/
theorem intern_proj_table_rest_refines {pers st lst rm lm}
    {t : kernel.env.ProjTable} {sn tn : arena.handle.NIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ProjTableWF t)
    (hrun : arena.intern.intern_proj_table_rest pers st rm t sn tn = ok o) :
    SimEM absIProjTable pers lst o
      (Frontend.internProjTable lm (ConRon.Refine.absProjTable t)) := by
  sorry

/-- `intern_ci_go` ⊑ `Frontend.internCI` — the seven `ConstantInfo`
constructors. -/
theorem intern_ci_go_refines {pers st lst rm lm} {c : kernel.env.ConstantInfo} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ConstantInfoWF c)
    (hrun : arena.intern.intern_ci_go pers st rm c = ok o) :
    SimEM absIConstantInfo pers lst o
      (Frontend.internCI lm (ConRon.Refine.absConstantInfo c)) := by
  sorry

/-- `intern_ci` ⊑ `Arena.internCI`. -/
theorem intern_ci_refines {pers st lst} {c : kernel.env.ConstantInfo} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hwf : ConstantInfoWF c)
    (hrun : arena.intern.intern_ci pers st c = ok o) :
    Sim absIConstantInfo (fun _ => True) pers lst o
      (internCI (ConRon.Refine.absConstantInfo c)) := by
  sorry

/-- `intern_ci_list_go` ⊑ `Frontend.internCIList` at the cursor. -/
theorem intern_ci_list_go_refines {pers st lst rm lm}
    {cs : alloc.vec.Vec kernel.env.ConstantInfo} {i : Std.Usize}
    {out : alloc.vec.Vec arena.env.IConstantInfo} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ConstantInfosWF cs)
    (hrun : arena.intern.intern_ci_list_go pers st rm cs i out = ok o) :
    SimEM (fun v => absICIL out ++ absICIL v) pers lst o
      (do let (m, hs) ← Frontend.internCIList lm (absCIListFrom cs i)
          pure (m, absICIL out ++ hs)) := by
  sorry

/-- `intern_ci_list` ⊑ `Arena.internCIList` — the block at ONE memo, so that
the sharing between a block's members survives. -/
theorem intern_ci_list_refines {pers st lst}
    {cs : alloc.vec.Vec kernel.env.ConstantInfo} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hwf : ConstantInfosWF cs)
    (hrun : arena.intern.intern_ci_list pers st cs = ok o) :
    Sim absICIL (fun _ => True) pers lst o
      (internCIList (ConRon.Refine.absConstantInfos cs)) := by
  sorry

/-- `intern_decl` ⊑ `Frontend.internDecl` — the seven `Declaration`
constructors. -/
theorem intern_decl_refines {pers st lst rm lm} {d : kernel.env.Declaration} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : DeclarationWF d)
    (hrun : arena.intern.intern_decl pers st rm d = ok o) :
    SimEM absIDeclaration pers lst o
      (Frontend.internDecl lm (ConRon.Refine.absDeclaration d)) := by
  sorry

/-- `intern_decls_go` ⊑ `Frontend.internDecls` at the cursor. -/
theorem intern_decls_go_refines {pers st lst rm lm}
    {ds : alloc.vec.Vec kernel.env.Declaration} {i : Std.Usize}
    {out : alloc.vec.Vec arena.env.IDeclaration} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hm : EMemoRel rm lm) (hwf : ∀ d ∈ ds.val, DeclarationWF d)
    (hrun : arena.intern.intern_decls_go pers st rm ds i out = ok o) :
    SimEM (fun v => absIDeclL out ++ absIDeclL v) pers lst o
      (do let (m, hs) ← Frontend.internDecls lm (absDeclLFrom ds i)
          pure (m, absIDeclL out ++ hs)) := by
  sorry

/-- `intern_decls` ⊑ `Frontend.internDecls` at a fresh memo. -/
theorem intern_decls_refines {pers st lst}
    {ds : alloc.vec.Vec kernel.env.Declaration} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hwf : ∀ d ∈ ds.val, DeclarationWF d)
    (hrun : arena.intern.intern_decls pers st ds = ok o) :
    Sim absIDeclL (fun _ => True) pers lst o
      (do pure (← Frontend.internDecls ∅ (ds.val.map ConRon.Refine.absDeclaration)).2) := by
  sorry


/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.memo_empty_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms memo_empty_refines

end ConRon.Refine2

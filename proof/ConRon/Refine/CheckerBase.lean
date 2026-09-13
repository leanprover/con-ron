import ConRon.Refine.TypeChecker
import ConRon.Refine.CoreKShapes
import ConRon.Refine.PropRead
import ConRon.Refine.BasisNames
import ConLeche.Kernel.DeclCheck

/-! # `kernel::checker_base` — the declaration checker's common ground (task #56)

`CORE_PLAN.md` step 7.  `ConLeche/Kernel/CheckerBase.lean` (292 lines) holds
the one check every declaration kind runs first (`checkConstantVal`), the
strategy-independent telescope helpers every install path shares
(`domsMatchAux`/`domsMatchAuxA`, `openPisAtFvars`/`openPisAtFvarsFGo`/
`openPisAtFvarsF`, `checkTypedList`, `checkAnnotList`, `checkDefEqList`,
`isEqHead`, `eqHeadLevel`, `unwrapOr`, `Env.findCV?`, `piResultSort`) and the
projection-rule stages (`checkProjShape`, `checkProjRule`).  All 26 public
functions of `crates/con-ron-core/src/kernel/checker_base.rs` are covered.

## The deviations of task #24 that the statements below encode

1. **`CheckerOps` is cited, not ported.**  con-leche writes the declaration
   checker once against `ops : CheckerOps m`; DESIGN.md §3.1's knot ruling
   drops the record and calls its slots by name through
   `kernel::type_checker`.  Every lemma here is therefore stated at
   `ConLeche.Cached.sharedOpsC`, spelled `TypeChecker.lops mode lfe`, and
   reaches the core only through `Refine/TypeChecker.lean`'s entry-point
   lemmas and the five `sharedOpsC_*` slot equalities.
2. **The `F`-twins collapse** (task #18's deviation 3): `checkConstantValF`,
   `checkProjRuleF` and `FEnv.findCV?` are the *same* Rust functions as their
   `Env` originals, so the statements are against the indexed twins; the
   `Env`-taking helpers (`checkTypedList`, `checkAnnotList`, `checkDefEqList`)
   are instantiated at `lfe.env`, which every `sharedOpsC` slot ignores.
3. **`domsMatchAux` is monomorphic at the identity view** — the `DomView`
   dictionary replaces the `g : Nat → Expr → Expr` argument (§3.4 forbids the
   closure) and `DomIdent` is the only instance this module passes, so the
   statement is at `fun _ e => e`.  The `Array` twin `domsMatchAuxA` is the
   same Rust function; `doms_match_aux_refines_array` is that second reading,
   and `domsMatchAuxA_ident`/`domsMatchAux_ident` are the two sides of
   con-leche's `domsMatchAuxA_eq` at the identity view.
4. **The long `do` blocks are split** (task #24's deviation 7):
   `check_constant_val`/`check_constant_val_after_annot`, and `check_proj_rule`
   into four (`proj_rule_wf`, `check_proj_rule_shape`,
   `check_proj_rule_certs`).  The tails have no con-leche name, so they are
   refined against the *tails* of the cited `do` block, written out here as
   `constantValTail` / `projRuleShapeTail` / `projRuleCertsTail` with their
   line ranges, plus one `*_at_annot` bridge lemma per split point saying that
   the cited whole *is* the tail once the head guards passed.
5. **Two-list recursions became one-index recursions with three arms**
   (task #14's point 7), so `check_typed_list_from` and
   `check_def_eq_list_from` are refined against the cited `List` recursion run
   on the two `drop i` suffixes.
6. **`fv :: fvs` is `expr_ops::cons_expr`** in `openPisAtFvars` and
   `openPisAtFvarsFGo`, and `fvs.map Expr.fvarTypeD` is `fvar_types`, which
   con-leche spells inline; both are equations, not weakenings.
7. **`level::name_nodup` had no lemma.**  `Name.nodup`
   (`ConLeche/Kernel/Level.lean:213-216`) is spelled in `level.rs` and
   `Refine/Level.lean` never needed it; `checkConstantVal` does, so it is
   proved here (`name_nodup_from_refines`/`name_nodup_refines`) — **to be
   moved to `Refine/Level.lean`**.  So is `wf_forall_inv`, which belongs
   beside `Refine/CoreKGuards.lean`'s three `wf_*_inv` lemmas.

## The two assumptions

Any lemma that runs a core entry point takes `core_k.check_fuel = ok fuel` and
`Core.Wrappers mode fuel`, exactly as `Refine/TypeChecker.lean` does; task #55
discharges them, and **nothing here proves anything about `cached::core_c`**.

The second is this file's own: `decl_check::consts_resolve_f_fast` belongs to
`Refine/DeclCheck.lean`, a sibling task-#56 file this one may not import, so
the two guards that call it (`check_constant_val_after_annot`,
`proj_rule_wf`, and hence `check_constant_val` and `check_proj_rule`) take
`ConstsResolveFSpec` — the named `Prop` below — as a hypothesis.

`sorry` count in this file: 0.
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.CheckerBase

/-- `expr::dup` is the identity in the model (DESIGN.md §3.2); `Refine/State.lean`
has the same lemma `@[local simp]`. -/
@[local simp] theorem expr_dup_eq (e : expr.Expr) : expr.dup e = ok e := by
  obtain ⟨r⟩ := e; simp [expr.dup]

/-! ## `level::name_nodup` — the one leaf `Refine/Level.lean` left

`Name.nodup` (`ConLeche/Kernel/Level.lean:213-216`) is spelled in `level.rs`
but was not needed before `checkConstantVal`; its index recursion tests the
*tail*, which is `name::contains_from` at `i + 1`. -/

/-- `ConLeche/Kernel/Level.lean:213-216` — `level::name_nodup_from` refines
`Name.nodup` of the suffix from `i`. -/
theorem name_nodup_from_refines {ns : alloc.vec.Vec name.Name} (hns : NamesWF ns) :
    ∀ k (i : Std.Usize), ns.val.length - i.val ≤ k → ∀ b : Bool,
      level.name_nodup_from ns i = ok b →
      b = ConLeche.Name.nodup ((absNames ns).drop i.val) := by
  intro k
  induction k with
  | zero =>
    intro i h b hb
    rw [level.name_nodup_from.eq_def] at hb; simp only [] at hb
    rw [if_pos (by scalar_tac)] at hb
    rw [absNames, ← List.map_drop, List.drop_eq_nil_of_le (by scalar_tac)]
    simp only [List.map_nil, show ConLeche.Name.nodup ([] : List ConLeche.Name) = true from rfl]
    simpa using hb.symm
  | succ k ih =>
    intro i h b hb
    rw [level.name_nodup_from.eq_def] at hb; simp only [] at hb
    split at hb
    · rw [absNames, ← List.map_drop, List.drop_eq_nil_of_le (by scalar_tac)]
      simp only [List.map_nil, show ConLeche.Name.nodup ([] : List ConLeche.Name) = true from rfl]
      simpa using hb.symm
    · rename_i hlt
      have hb2 : i.val < ns.val.length := by scalar_tac
      have hmax : i.val + 1 ≤ Std.Usize.max := by have := ns.slice.property; scalar_tac
      obtain ⟨w, hw, hwv⟩ := usize_add_ok hmax
      simp only [alloc.vec.Vec.index_slice_index, bind_eq_ok_iff] at hb
      obtain ⟨i2, hi2, y, hy, c, hc, hb⟩ := hb
      have hi2v : i2.val = i.val + 1 := by
        rw [hw] at hi2; simp only [Result.ok.injEq] at hi2; rw [← hi2, hwv]
      have hyv : y = ns.val[i.val] := by
        obtain ⟨y', hy', hy'v⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec ns i hb2)
        rw [hy'] at hy; simp only [Result.ok.injEq] at hy; rw [← hy, hy'v]
      subst hyv
      have hyWF : NameWF ns.val[i.val] := hns _ (List.getElem_mem hb2)
      have hcabs := Name.contains_from_refines hns hyWF ns.val.length i2 (by scalar_tac) c hc
      rw [hi2v] at hcabs
      have hcc : (List.map absName (List.drop (i.val + 1) ns.val)).contains
            (absName ns.val[i.val]) = c := by
        rw [hcabs, Bool.eq_iff_iff, decide_eq_true_iff, List.contains_iff_mem]
      rw [absNames, ← List.map_drop, List.drop_eq_getElem_cons hb2]
      simp only [List.map_cons, ConLeche.Name.nodup]
      rw [hcc]
      cases c with
      | true => simp only [Bool.not_true, Bool.false_and]; simpa using hb.symm
      | false =>
        simp only [Bool.false_eq_true, if_false] at hb
        have hih := ih i2 (by scalar_tac) b hb
        rw [hi2v, absNames, ← List.map_drop] at hih
        simpa using hih

/-- `ConLeche/Kernel/Level.lean:213-216` — `level::name_nodup` refines
`Name.nodup`. -/
theorem name_nodup_refines {ns : alloc.vec.Vec name.Name} {b : Bool}
    (hns : NamesWF ns) (h : level.name_nodup ns = ok b) :
    b = ConLeche.Name.nodup (absNames ns) := by
  rw [level.name_nodup] at h
  have hh := name_nodup_from_refines hns ns.val.length 0#usize (by scalar_tac) b h
  simpa using hh

/-! ## A missing `Expr` inversion

**To be moved to `Refine/Expr.lean`** beside the other `*_inv` lemmas, exactly
as `Refine/CoreKGuards.lean`'s three are: `openPisAtFvars` cases on a node's
kind, which throws the `ExprWF` derivation away. -/

/-- A well-formed `ForallE` node has well-formed parts. -/
theorem wf_forall_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64}
    {ty bo : expr.Expr} {m : expr.BinderMeta} (hk : e = .mk (.mk d (.ForallE ty bo m))) :
    ExprWF ty ∧ ExprWF bo ∧ BinderMetaWF m := by
  cases he with
  | @bvar i _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1; simp at hk
  | @fvar idx ty1 _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1; simp at hk
  | @sort u1 _ _ h1 => obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1; simp at hk
  | @mk_const n1 us1 _ _ _ h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1; simp at hk
  | @app f1 a1 _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1; simp at hk
  | @lam ty1 bo1 m1 _ _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1; simp at hk
  | @forall_e ty1 bo1 m1 _ hty hbo hm h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq,
      expr.ExprKind.ForallE.injEq] at hk
    obtain ⟨-, rfl, rfl, rfl⟩ := hk
    exact ⟨hty, hbo, hm⟩
  | @let_e ty1 v1 bo1 _ _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1; simp at hk
  | @lit l _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1; simp at hk
  | @proj s i x _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1; simp at hk

/-! ## The state-free readers

`unwrapOr`, `Env.findCV?`/`FEnv.findCV?`, `piResultSort`, `isEqHead` and
`eqHeadLevel` touch neither the state nor the core, so each is a plain
equality (DESIGN.md §3.5's pure shape). -/

/-- `ConLeche/Kernel/CheckerBase.lean:211-217 unwrapOr` — the port's
`Result`-valued spelling: an `.Ok a` says the option *was* `some a`, which is
the clause con-leche's `pure a` reads.  (The port is generic in the payload,
so this is the statement at every abstraction at once: `unwrapOr (o.map f)`
is `pure (f a)` as soon as `o = some a`.)  Its call sites are
`DeclCheck.lean`'s iota-theorem mirrors, which the port does not have yet. -/
theorem unwrap_or_refines {T : Type} {o : Option T} {err : core_types.CheckError} {a : T}
    (h : checker_base.unwrap_or o err = ok (.Ok a)) : o = some a := by
  cases o with
  | none => simp [checker_base.unwrap_or] at h
  | some x => simp only [checker_base.unwrap_or, Result.ok.injEq,
      core.result.Result.Ok.injEq] at h; rw [h]

/-- `ConLeche/Kernel/CheckerBase.lean:219-225 Env.findCV?`,
`ConLeche/Kernel/DeclCheck.lean:33-35 FEnv.findCV?` — the stored constant as a
`ConstantVal`.  Stated against the indexed twin, which is what the port reads
(task #18's deviation 3). -/
theorem find_cv_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {n : name.Name}
    {o : Option env.ConstantVal} (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe)
    (hn : NameWF n) (h : checker_base.find_cv fe n = ok o) :
    o.map absConstantVal = ConLeche.FEnv.findCV? lfe (absName n) ∧
      ∀ cv, o = some cv → ConstantValWF cv := by
  rw [checker_base.find_cv] at h
  obtain ⟨oi, hoi, h⟩ := bind_eq_ok_iff.mp h
  have hfind := FEnv.find_refines hrel hwf hn hoi
  cases oi with
  | none =>
    simp only [Result.ok.injEq] at h
    subst h
    refine ⟨?_, by simp⟩
    rw [ConLeche.FEnv.findCV?, ← hfind]; simp
  | some ci =>
    obtain ⟨cv, hcv, h⟩ := bind_eq_ok_iff.mp h
    simp only [Result.ok.injEq] at h
    subst h
    have hciwf : ConstantInfoWF ci := FEnv.find_wf hwf hn hoi ci rfl
    obtain ⟨habs, hwfcv⟩ := PropRead.to_constant_val_refines hciwf hcv
    refine ⟨?_, ?_⟩
    · rw [ConLeche.FEnv.findCV?, ← hfind]
      simp only [Option.map_some, habs]
    · intro cv' hcv'; simp only [Option.some.injEq] at hcv'; rw [← hcv']; exact hwfcv

/-- `ConLeche/Kernel/CheckerBase.lean:227-232 piResultSort` — the result sort
of a syntactic pi telescope. -/
theorem pi_result_sort_refines {e : expr.Expr} {o : Option level.Level}
    (he : ExprWF e) (h : checker_base.pi_result_sort e = ok o) :
    o.map absLevel = ConLeche.piResultSort (absExpr e) ∧
      ∀ u, o = some u → LevelWF u := by
  rw [checker_base.pi_result_sort] at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs, hrwf⟩ := ExprOps.pi_result_refines he hr
  obtain ⟨nd⟩ := r
  obtain ⟨d, k⟩ := nd
  rw [ConLeche.piResultSort, ← habs]
  cases k with
  | «Sort» u =>
    simp only [arc_deref_eq, ExprOps.node_kind, level_dup_eq, bind_tc_ok,
      Result.ok.injEq] at h
    subst h
    refine ⟨by simp, ?_⟩
    intro u' hu'
    simp only [Option.some.injEq] at hu'
    rw [← hu']
    exact CoreK.wf_sort_inv hrwf rfl
  | _ =>
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok, Result.ok.injEq] at h
    subst h
    exact ⟨by simp, by simp⟩

/-- con-leche compares names with `==`; `Refine/Name.lean` states `name::beq`
with `decide`.  The two agree (`Name`'s `BEq` is lawful). -/
theorem decide_eq_beq_name (a b : ConLeche.Name) : decide (a = b) = (a == b) := by
  rw [Bool.eq_iff_iff]; simp

/-- `ConLeche/Kernel/CheckerBase.lean:186-189 isEqHead` — the pinned equality
former at one level. -/
theorem is_eq_head_refines {e : expr.Expr} {b : Bool} (he : ExprWF e)
    (h : checker_base.is_eq_head e = ok b) : b = ConLeche.isEqHead (absExpr e) := by
  obtain ⟨nd⟩ := e
  obtain ⟨d, k⟩ := nd
  rw [checker_base.is_eq_head] at h
  cases k with
  | Const c us =>
    obtain ⟨hcwf, huswf⟩ := CoreK.wf_const_inv he rfl
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    rw [absExpr_mk, absExprKind, absLevels]
    split at h
    · rename_i hlen
      have hl1 : us.val.length = 1 := by scalar_tac
      obtain ⟨m, hm, hb⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hmabs, hmwf⟩ := BasisNames.eq_name_refines hm
      rcases hv : us.val with _ | ⟨u0, us'⟩
      · rw [hv] at hl1; simp at hl1
      · cases us' with
        | cons v vs => rw [hv] at hl1; simp at hl1
        | nil =>
          rw [Name.beq_refines hcwf hmwf hb, hmabs]
          simp [ConLeche.isEqHead, decide_eq_beq_name]
    · rename_i hlen
      have hl1 : us.val.length ≠ 1 := by scalar_tac
      simp only [Result.ok.injEq] at h
      rw [← h]
      rcases hv : us.val with _ | ⟨u0, us'⟩
      · simp [ConLeche.isEqHead]
      · cases us' with
        | nil => rw [hv] at hl1; simp at hl1
        | cons v vs => simp [ConLeche.isEqHead]
  | _ =>
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.isEqHead]

/-- `ConLeche/Kernel/CheckerBase.lean:191-198 eqHeadLevel` — the level an
equality head carries; off shape it is `.zero`. -/
theorem eq_head_level_refines {e : expr.Expr} {u : level.Level} (he : ExprWF e)
    (h : checker_base.eq_head_level e = ok u) :
    absLevel u = ConLeche.eqHeadLevel (absExpr e) ∧ LevelWF u := by
  obtain ⟨nd⟩ := e
  obtain ⟨d, k⟩ := nd
  rw [checker_base.eq_head_level] at h
  cases k with
  | Const c us =>
    obtain ⟨hcwf, huswf⟩ := CoreK.wf_const_inv he rfl
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    rw [absExpr_mk, absExprKind, absLevels]
    split at h
    · rename_i hlen
      have hl1 : us.val.length = 1 := by scalar_tac
      obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.index_usize_spec us 0#usize (by scalar_tac))
      simp only [alloc.vec.Vec.index_slice_index, hy, level_dup_eq, bind_tc_ok,
        Result.ok.injEq] at h
      subst h
      have hywf : LevelWF y := by
        rw [hyv]; exact huswf _ (List.getElem_mem (by scalar_tac))
      obtain ⟨u0, hv⟩ : ∃ u0, us.val = [u0] := by
        rcases hh : us.val with _ | ⟨x, t⟩
        · rw [hh] at hl1; simp at hl1
        · cases t with
          | nil => exact ⟨x, rfl⟩
          | cons z zs => rw [hh] at hl1; simp at hl1
      have hy0 : y = u0 := by
        have h1 : us.val[0]? = some y := by
          rw [hyv, List.getElem?_eq_getElem (by scalar_tac)]; simp
        rw [hv] at h1; simpa using h1.symm
      subst hy0
      rw [hv]
      exact ⟨by simp [ConLeche.eqHeadLevel], hywf⟩
    · rename_i hlen
      have hl1 : us.val.length ≠ 1 := by scalar_tac
      refine ⟨?_, Level.zero_wf h⟩
      rw [Level.zero_refines h]
      rcases hv : us.val with _ | ⟨u0, us'⟩
      · simp [ConLeche.eqHeadLevel]
      · cases us' with
        | nil => rw [hv] at hl1; simp at hl1
        | cons v vs => simp [ConLeche.eqHeadLevel]
  | _ =>
    simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
    exact ⟨by rw [Level.zero_refines h]; simp [ConLeche.eqHeadLevel], Level.zero_wf h⟩

/-! ## `domsMatchAux` at the identity view, and its `Array` twin

Task #24's deviation 1: the cited `g : Nat → Expr → Expr` is a closure §3.4
forbids, so the port replaces it with a `DomView` dictionary and passes
`DomIdent` — `fun _ e => e` — at every call site in this scope.  The cited
`Array` twin `domsMatchAuxA` (`CheckerBase.lean:120-129`) is the *same* Rust
function, and `domsMatchAuxA_eq` is the equation between them; both readings
are stated below. -/

/-- con-leche compares terms with `==`; `Refine/Expr.lean` states `expr::beq`
with `decide`.  The two agree. -/
theorem decide_eq_beq_expr (a b : ConLeche.Expr) : decide (a = b) = (a == b) := by
  rw [Bool.eq_iff_iff]; simp

/-- The cited `(List.range n).all` body, at the identity view. -/
def domsStep (bs₁ bs₂ : List (ConLeche.Expr × ConLeche.BinderMeta)) (o₁ o₂ i : Nat) : Bool :=
  match bs₁[o₁ + i]?, bs₂[o₂ + i]? with
  | some b₁, some b₂ => b₁.1 == b₂.1
  | _, _ => false

/-- `domsMatchAux` at the identity view *is* `domsStep`'s `List.range` fold. -/
theorem domsMatchAux_ident (bs₁ bs₂ : List (ConLeche.Expr × ConLeche.BinderMeta))
    (o₁ o₂ n : Nat) :
    ConLeche.domsMatchAux (fun _ e => e) bs₁ bs₂ o₁ o₂ n
      = (List.range n).all (domsStep bs₁ bs₂ o₁ o₂) := rfl

/-- `domsMatchAuxA` at the identity view is the same fold over the arrays. -/
theorem domsMatchAuxA_ident (bs₁ bs₂ : List (ConLeche.Expr × ConLeche.BinderMeta))
    (o₁ o₂ n : Nat) :
    ConLeche.domsMatchAuxA (fun _ e => e) bs₁.toArray bs₂.toArray o₁ o₂ n
      = (List.range n).all (domsStep bs₁ bs₂ o₁ o₂) := by
  rw [ConLeche.domsMatchAuxA]
  simp only [List.getElem?_toArray]
  rfl

/-- `DomIdent`'s one method is the cited `fun _ e => e` (`expr::dup` is the
identity in the model, DESIGN.md §3.2). -/
theorem dom_ident_view_refines {i : Std.U64} {e r : expr.Expr}
    (h : checker_base.DomIdent.Insts.Con_ron_coreKernelChecker_baseDomView.view () i e = ok r) :
    r = e := by
  rw [checker_base.DomIdent.Insts.Con_ron_coreKernelChecker_baseDomView.view] at h
  exact Expr.dup_eq h

/-- Indexing a binder vector: the abstracted list agrees at the same index. -/
theorem vec_index_binder {bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {i : Std.Usize} {p : expr.Expr × expr.BinderMeta} (hbs : ExprOps.BindersWF bs)
    (h : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice (expr.Expr × expr.BinderMeta)) bs i = ok p) :
    ExprWF p.1 ∧ (ExprOps.absBinders bs)[i.val]?
      = some (absExpr p.1, absBinderMeta p.2) := by
  have hg := ExprOps.vec_index_getElem? h
  have hlt : i.val < bs.val.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
  have hx : bs.val[i.val] = p := by
    rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
  refine ⟨(hbs p (by rw [← hx]; exact List.getElem_mem hlt)).1, ?_⟩
  rw [ExprOps.absBinders, List.getElem?_map, hg]
  rfl

/-- `ConLeche/Kernel/CheckerBase.lean:99-106 domsMatchAux` — the index
recursion behind `doms_match_aux`, at the positions from `i` on. -/
theorem doms_match_aux_from_refines
    {bs1 bs2 : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    (hb1 : ExprOps.BindersWF bs1) (hb2 : ExprOps.BindersWF bs2) :
    ∀ (N : Nat) (o1 o2 n i : Std.U64), n.val - i.val ≤ N → ∀ b : Bool,
      checker_base.doms_match_aux_from
        checker_base.DomIdent.Insts.Con_ron_coreKernelChecker_baseDomView () bs1 bs2 o1 o2 n i
        = ok b →
      b = (List.range' i.val (n.val - i.val)).all
            (domsStep (ExprOps.absBinders bs1) (ExprOps.absBinders bs2) o1.val o2.val) := by
  have hlen1 : (ExprOps.absBinders bs1).length = bs1.val.length := by simp [ExprOps.absBinders]
  have hlen2 : (ExprOps.absBinders bs2).length = bs2.val.length := by simp [ExprOps.absBinders]
  intro N
  induction N with
  | zero =>
    intro o1 o2 n i hN b h
    rw [checker_base.doms_match_aux_from.eq_def] at h
    simp only [] at h
    rw [if_pos (by scalar_tac)] at h
    rw [show n.val - i.val = 0 by omega]
    simpa using h.symm
  | succ N ih =>
    intro o1 o2 n i hN b h
    rw [checker_base.doms_match_aux_from.eq_def] at h
    simp only [] at h
    split at h
    · rw [show n.val - i.val = 0 by scalar_tac]
      simpa using h.symm
    · rename_i hlt
      have hltv : i.val < n.val := by scalar_tac
      simp only [lift_eq, bind_tc_ok] at h
      obtain ⟨j1, hj1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨j2, hj2, h⟩ := bind_eq_ok_iff.mp h
      have hj1v : j1.val = o1.val + i.val := HashMap.uscalar_add_eq hj1
      have hj2v : j2.val = o2.val + i.val := HashMap.uscalar_add_eq hj2
      have hc1 : (Std.UScalar.cast .U64 (alloc.vec.Vec.len bs1) : Std.U64).val
          = bs1.val.length := by rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
      have hc2 : (Std.UScalar.cast .U64 (alloc.vec.Vec.len bs2) : Std.U64).val
          = bs2.val.length := by rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
      rw [show n.val - i.val = (n.val - i.val - 1) + 1 by omega, List.range'_succ,
        List.all_cons]
      split at h
      · rename_i hge
        have hnone : (ExprOps.absBinders bs1)[o1.val + i.val]? = none :=
          List.getElem?_eq_none (by rw [hlen1]; scalar_tac)
        simp only [domsStep, hnone]
        simpa using h.symm
      · rename_i hlt1
        split at h
        · rename_i hge
          have hnone : (ExprOps.absBinders bs2)[o2.val + i.val]? = none :=
            List.getElem?_eq_none (by rw [hlen2]; scalar_tac)
          simp only [domsStep, hnone]
          rcases hs : (ExprOps.absBinders bs1)[o1.val + i.val]? with _ | q <;>
            simpa using h.symm
        · rename_i hlt2
          obtain ⟨p2, hp2, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨e2, m2⟩ := p2
          obtain ⟨viewed, hview, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨p1, hp1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨e1, m1⟩ := p1
          obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
          have hi5 : ((Std.UScalar.cast .Usize j2 : Std.Usize)).val = j2.val :=
            ExprOps.u64_cast_usize_val_of_lt (n := bs2.val.length)
              (by have := bs2.slice.property; scalar_tac) (by scalar_tac)
          have hi6 : ((Std.UScalar.cast .Usize j1 : Std.Usize)).val = j1.val :=
            ExprOps.u64_cast_usize_val_of_lt (n := bs1.val.length)
              (by have := bs1.slice.property; scalar_tac) (by scalar_tac)
          obtain ⟨hw2, hg2⟩ := vec_index_binder hb2 hp2
          obtain ⟨hw1, hg1⟩ := vec_index_binder hb1 hp1
          rw [hi5, hj2v] at hg2
          rw [hi6, hj1v] at hg1
          rw [dom_ident_view_refines hview] at hc
          have hcv := Expr.beq_refines hw1 hw2 hc
          simp only [domsStep, hg1, hg2, ← decide_eq_beq_expr, ← hcv]
          cases c with
          | false =>
            simp only [Bool.false_eq_true, if_false] at h
            simpa using h.symm
          | true =>
            simp only [reduceIte] at h
            obtain ⟨i7, hi7, h⟩ := bind_eq_ok_iff.mp h
            have hi7v : i7.val = i.val + 1 := HashMap.uscalar_add_eq hi7
            have hih := ih o1 o2 n i7 (by omega) b h
            rw [hi7v, show n.val - (i.val + 1) = n.val - i.val - 1 by omega] at hih
            simpa using hih

/-- `ConLeche/Kernel/CheckerBase.lean:99-106 domsMatchAux` — the wrapper, at
the identity view. -/
theorem doms_match_aux_refines
    {bs1 bs2 : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {o1 o2 n : Std.U64} {b : Bool}
    (hb1 : ExprOps.BindersWF bs1) (hb2 : ExprOps.BindersWF bs2)
    (h : checker_base.doms_match_aux
      checker_base.DomIdent.Insts.Con_ron_coreKernelChecker_baseDomView () bs1 bs2 o1 o2 n
      = ok b) :
    b = ConLeche.domsMatchAux (fun _ e => e)
      (ExprOps.absBinders bs1) (ExprOps.absBinders bs2) o1.val o2.val n.val := by
  rw [checker_base.doms_match_aux] at h
  have hh := doms_match_aux_from_refines hb1 hb2 n.val o1 o2 n 0#u64 (by scalar_tac) b h
  rw [domsMatchAux_ident, List.range_eq_range']
  simpa using hh

/-- `ConLeche/Kernel/CheckerBase.lean:120-129 domsMatchAuxA` — the `Array`
twin is the same Rust function (task #24's `F`/`Array` collapse); this is the
reading `checkProjRuleF` consumes. -/
theorem doms_match_aux_refines_array
    {bs1 bs2 : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {o1 o2 n : Std.U64} {b : Bool}
    (hb1 : ExprOps.BindersWF bs1) (hb2 : ExprOps.BindersWF bs2)
    (h : checker_base.doms_match_aux
      checker_base.DomIdent.Insts.Con_ron_coreKernelChecker_baseDomView () bs1 bs2 o1 o2 n
      = ok b) :
    b = ConLeche.domsMatchAuxA (fun _ e => e)
      (ExprOps.absBinders bs1).toArray (ExprOps.absBinders bs2).toArray
      o1.val o2.val n.val := by
  rw [domsMatchAuxA_ident, ← domsMatchAux_ident]
  exact doms_match_aux_refines hb1 hb2 h

/-! ## `fvs.map Expr.fvarTypeD`

con-leche writes the map inline in `checkProjRule`/`checkIotaThm`; §3.4 forbids
the closure, so the port has `fvar_types`. -/

/-- `checker_base::fvar_types_from` — the accumulating index recursion. -/
theorem fvar_types_from_refines {fvs : alloc.vec.Vec expr.Expr} (hfvs : ExprsWF fvs) :
    ∀ (N : Nat) (i : Std.Usize) (out r : alloc.vec.Vec expr.Expr),
      fvs.val.length - i.val ≤ N → ExprsWF out →
      checker_base.fvar_types_from fvs i out = ok r →
      absExprs r = absExprs out ++ ((absExprs fvs).drop i.val).map ConLeche.Expr.fvarTypeD
        ∧ ExprsWF r := by
  intro N
  induction N with
  | zero =>
    intro i out r hN hout h
    rw [checker_base.fvar_types_from.eq_def] at h
    simp only [] at h
    rw [if_pos (by scalar_tac)] at h
    rw [← Result.ok_injective h]
    refine ⟨?_, hout⟩
    rw [show (absExprs fvs).drop i.val = [] from
      List.drop_eq_nil_of_le (by simp only [absExprs, List.length_map]; scalar_tac)]
    simp
  | succ N ih =>
    intro i out r hN hout h
    rw [checker_base.fvar_types_from.eq_def] at h
    simp only [] at h
    split at h
    · rw [← Result.ok_injective h]
      refine ⟨?_, hout⟩
      rw [show (absExprs fvs).drop i.val = [] from
        List.drop_eq_nil_of_le (by simp only [absExprs, List.length_map]; scalar_tac)]
      simp
    · rename_i hlt
      obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨t, ht, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hlti, hxwf, hdrop⟩ := ExprOps.vec_index_expr hfvs hx
      obtain ⟨htabs, htwf⟩ := ExprOps.fvar_type_d_refines hxwf ht
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      have hout1v : absExprs out1 = absExprs out ++ [absExpr t] := by
        rw [absExprs, absExprs, vec_push_val hout1]; simp
      have hout1wf : ExprsWF out1 := by
        intro y hy
        rw [vec_push_val hout1] at hy
        rcases List.mem_append.1 hy with h1 | h1
        · exact hout y h1
        · simp only [List.mem_singleton] at h1; rw [h1]; exact htwf
      obtain ⟨habs, hwf⟩ := ih i2 out1 r (by omega) hout1wf h
      refine ⟨?_, hwf⟩
      rw [habs, hout1v, hi2v, hdrop]
      simp [htabs]

/-- `checker_base::fvar_types` — `fvs.map Expr.fvarTypeD`. -/
theorem fvar_types_refines {fvs r : alloc.vec.Vec expr.Expr} (hfvs : ExprsWF fvs)
    (h : checker_base.fvar_types fvs = ok r) :
    absExprs r = (absExprs fvs).map ConLeche.Expr.fvarTypeD ∧ ExprsWF r := by
  rw [checker_base.fvar_types] at h
  obtain ⟨habs, hwf⟩ := fvar_types_from_refines hfvs fvs.val.length 0#usize _ r
    (by scalar_tac) ExprOps.exprsWF_new h
  refine ⟨?_, hwf⟩
  rw [habs]
  simp [absExprs, alloc.vec.Vec.new]

/-! ## `openPisAtFvars` and its one-pass twin

Task #24's deviation 6: `fv :: fvs` is `expr_ops::cons_expr`, a fresh vector
filled front to back (`O(width)` where Lean's cons is `O(1)`), and the `acc`
of the one-pass walk is copied on the way down for the same reason. -/

/-- `ConLeche/Kernel/CheckerBase.lean:108-118 openPisAtFvars` — open the first
`n` `∀`-binders at fresh free variables. -/
theorem open_pis_at_fvars_refines :
    ∀ (N : Nat) (n : Std.U64) (e : expr.Expr) (i : Std.U64)
      (r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)),
      n.val = N → ExprWF e →
      checker_base.open_pis_at_fvars n e i = ok r →
      (Option.map (fun p => (absExprs p.1, absExpr p.2)) r
        = ConLeche.openPisAtFvars n.val (absExpr e) i.val)
      ∧ (∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2) := by
  intro N
  induction N with
  | zero =>
    intro n e i r hN he h
    rw [checker_base.open_pis_at_fvars.eq_def] at h
    rw [if_pos (by scalar_tac)] at h
    simp only [expr_dup_eq, bind_tc_ok, Result.ok.injEq] at h
    rw [← h, hN]
    refine ⟨by simp [ConLeche.openPisAtFvars, absExprs, alloc.vec.Vec.new], ?_⟩
    intro p hp
    simp only [Option.some.injEq] at hp
    rw [← hp]
    exact ⟨ExprOps.exprsWF_new, he⟩
  | succ N ih =>
    intro n e i r hN he h
    rw [checker_base.open_pis_at_fvars.eq_def] at h
    rw [if_neg (by scalar_tac)] at h
    obtain ⟨nd⟩ := e
    obtain ⟨d, k⟩ := nd
    rw [hN, absExpr_mk]
    cases k with
    | ForallE dom body m =>
      obtain ⟨hdom, hbody, hm⟩ := wf_forall_inv he rfl
      simp only [arc_deref_eq, ExprOps.node_kind, expr_dup_eq, bind_tc_ok] at h
      obtain ⟨fv, hfv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨opened, hopened, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      have hfvwf : ExprWF fv := Expr.fvar_wf hdom hfv
      have hfvabs : absExpr fv = .fvar i.val (absExpr dom) := Expr.fvar_refines hfv
      obtain ⟨hoabs, howf⟩ := ExprOps.instantiate1_refines hbody hfvwf hopened
      have hn1v : n1.val = n.val - 1 := HashMap.uscalar_sub_eq hn1
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      obtain ⟨habs, hwf⟩ := ih n1 opened i2 o (by omega) howf ho
      rw [hn1v, hi2v, hoabs, show ((0#u64 : Std.U64)).val = 0 from rfl,
        show n.val - 1 = N by omega] at habs
      simp only [absExprKind, ConLeche.openPisAtFvars, ← hfvabs, ← habs]
      cases o with
      | none =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact ⟨by simp, by simp⟩
      | some q =>
        obtain ⟨fvs, b⟩ := q
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        simp only [Result.ok.injEq] at h
        obtain ⟨hfvswf, hbwf⟩ := hwf (fvs, b) rfl
        obtain ⟨hvabs, hvwf⟩ := ExprOps.cons_expr_refines hfvwf hfvswf hv
        rw [← h]
        refine ⟨by simp [hvabs], ?_⟩
        intro p hp
        simp only [Option.some.injEq] at hp
        rw [← hp]
        exact ⟨hvwf, hbwf⟩
    | _ =>
      simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
      rw [← Result.ok_injective h]
      exact ⟨by simp [absExprKind, ConLeche.openPisAtFvars], by simp⟩

/-- `ConLeche/Kernel/CheckerBase.lean:131-145 openPisAtFvarsFGo` — the one-pass
core: one `instantiateList` per domain instead of one whole-telescope
`instantiate1` per binder.  `acc` holds the already-created fvars, innermost
binder first. -/
theorem open_pis_at_fvars_f_go_refines :
    ∀ (N : Nat) (acc : alloc.vec.Vec expr.Expr) (n : Std.U64) (e : expr.Expr) (i : Std.U64)
      (r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)),
      n.val = N → ExprsWF acc → ExprWF e →
      checker_base.open_pis_at_fvars_f_go acc n e i = ok r →
      (Option.map (fun p => (absExprs p.1, absExpr p.2)) r
        = ConLeche.openPisAtFvarsFGo (absExprs acc) n.val (absExpr e) i.val)
      ∧ (∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2) := by
  intro N
  induction N with
  | zero =>
    intro acc n e i r hN hacc he h
    rw [checker_base.open_pis_at_fvars_f_go.eq_def] at h
    rw [if_pos (by scalar_tac)] at h
    obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨habs1, hwf1⟩ := ExprOps.instantiate_list_fast_refines he hacc he1
    simp only [Result.ok.injEq] at h
    rw [← h, hN]
    refine ⟨?_, ?_⟩
    · simp only [ConLeche.openPisAtFvarsFGo, Option.map_some, habs1,
        show ((0#u64 : Std.U64)).val = 0 from rfl]
      simp [absExprs, alloc.vec.Vec.new]
    · intro p hp
      simp only [Option.some.injEq] at hp
      rw [← hp]
      exact ⟨ExprOps.exprsWF_new, hwf1⟩
  | succ N ih =>
    intro acc n e i r hN hacc he h
    rw [checker_base.open_pis_at_fvars_f_go.eq_def] at h
    rw [if_neg (by scalar_tac)] at h
    obtain ⟨nd⟩ := e
    obtain ⟨d, k⟩ := nd
    rw [hN, absExpr_mk]
    cases k with
    | ForallE dom body m =>
      obtain ⟨hdom, hbody, hm⟩ := wf_forall_inv he rfl
      simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨fv, hfv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨acc2, hacc2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨habs1, hwf1⟩ := ExprOps.instantiate_list_fast_refines hdom hacc he1
      have hfvwf : ExprWF fv := Expr.fvar_wf hwf1 hfv
      have hfvabs : absExpr fv = .fvar i.val (absExpr e1) := Expr.fvar_refines hfv
      obtain ⟨hacc2abs, hacc2wf⟩ := ExprOps.cons_expr_refines hfvwf hacc hacc2
      have hn1v : n1.val = n.val - 1 := HashMap.uscalar_sub_eq hn1
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      obtain ⟨habs, hwf⟩ := ih acc2 n1 body i2 o (by omega) hacc2wf hbody ho
      rw [hn1v, hi2v, hacc2abs, show n.val - 1 = N by omega] at habs
      rw [habs1, show ((0#u64 : Std.U64)).val = 0 from rfl] at hfvabs
      simp only [absExprKind, ConLeche.openPisAtFvarsFGo, ← hfvabs, ← habs]
      cases o with
      | none =>
        simp only [Result.ok.injEq] at h
        rw [← h]
        exact ⟨by simp, by simp⟩
      | some q =>
        obtain ⟨fvs, b⟩ := q
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        simp only [Result.ok.injEq] at h
        obtain ⟨hfvswf, hbwf⟩ := hwf (fvs, b) rfl
        obtain ⟨hvabs, hvwf⟩ := ExprOps.cons_expr_refines hfvwf hfvswf hv
        rw [← h]
        refine ⟨by simp [hvabs], ?_⟩
        intro p hp
        simp only [Option.some.injEq] at hp
        rw [← hp]
        exact ⟨hvwf, hbwf⟩
    | _ =>
      simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
      rw [← Result.ok_injective h]
      exact ⟨by simp [absExprKind, ConLeche.openPisAtFvarsFGo], by simp⟩

/-- `ConLeche/Kernel/CheckerBase.lean:147-154 openPisAtFvarsF` — **the executed
one**: the one-pass walk with the cited fallback. -/
theorem open_pis_at_fvars_f_refines {n : Std.U64} {e : expr.Expr} {i : Std.U64}
    {r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)} (he : ExprWF e)
    (h : checker_base.open_pis_at_fvars_f n e i = ok r) :
    (Option.map (fun p => (absExprs p.1, absExpr p.2)) r
      = ConLeche.openPisAtFvarsF n.val (absExpr e) i.val)
    ∧ (∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2) := by
  rw [checker_base.open_pis_at_fvars_f] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ :=
    open_pis_at_fvars_f_go_refines n.val _ n e i o rfl ExprOps.exprsWF_new he ho
  rw [ConLeche.openPisAtFvarsF]
  rw [show absExprs (alloc.vec.Vec.new expr.Expr) = [] from rfl] at hoabs
  rw [← hoabs]
  cases o with
  | none =>
    simp only [Option.map_none]
    exact open_pis_at_fvars_refines n.val n e i r rfl he h
  | some q =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    exact ⟨by simp, howf⟩

/-! ## `checkProjShape` — stage 2b, and state-free

The cited definition is monad-polymorphic but touches neither the state nor
the core, so it is run here at `ConLeche.Cached.CheckCM` — the monad the
executed checker uses — and leaves the state where it found it. -/

/-- `ConLeche/Kernel/CheckerBase.lean:235-250 checkProjShape` — the projection
type's parameter telescope is syntactically the constructor's, and the
constructor's residual is the family applied to exactly the parameters. -/
theorem check_proj_shape_refines {pty ctor_ty : expr.Expr} {n_p n_f : Std.U64}
    (hp : ExprWF pty) (hc : ExprWF ctor_ty)
    (h : checker_base.check_proj_shape pty ctor_ty n_p n_f = ok (.Ok ())) :
    ∀ lst : ConLeche.Cached.CState,
      (ConLeche.checkProjShape (m := ConLeche.Cached.CheckCM)
        (absExpr pty) (absExpr ctor_ty) n_p.val n_f.val).run lst = .ok ((), lst) := by
  intro lst
  rw [checker_base.check_proj_shape] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨habs1, -⟩ := ExprOps.strip_pis_refines hp ho
  cases o with
  | none => simp at h
  | some q1 =>
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    have hi1v : i1.val = n_p.val + n_f.val := HashMap.uscalar_add_eq hi1
    obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨habs2, hwf2⟩ := ExprOps.strip_pis_refines hc ho1
    rw [hi1v] at habs2
    cases o1 with
    | none => simp at h
    | some q2 =>
      obtain ⟨cbinders, cbody⟩ := q2
      obtain ⟨-, hcbodywf⟩ := hwf2 (cbinders, cbody) rfl
      obtain ⟨args, hargs, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hargsabs, hargswf⟩ := ExprOps.get_app_args_refines hcbodywf hargs
      simp only [lift_eq, bind_tc_ok] at h
      split at h
      · simp at h
      · rename_i hne
        have hlen : args.val.length = n_p.val := by
          have hcast : (Std.UScalar.cast .U64 (alloc.vec.Vec.len args) : Std.U64).val
              = args.val.length := by
            rw [ExprOps.usize_cast_u64_val, alloc.vec.Vec.len_val]
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
          rw [← hcast, hne]
        obtain ⟨f, hf, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hfabs, hfwf⟩ := ExprOps.get_app_fn_refines hcbodywf hf
        obtain ⟨nd⟩ := f
        obtain ⟨df, kf⟩ := nd
        rw [ConLeche.checkProjShape]
        simp only [← habs1, ← habs2, Option.map_some]
        cases kf with
        | Const cn cus =>
          rw [absExpr_mk, absExprKind] at hfabs
          simp only [← hargsabs, ← hfabs]
          have : (absExprs args).length = n_p.val := by
            simp only [absExprs, List.length_map]; exact hlen
          simp [this]
          rfl
        | _ =>
          simp only [arc_deref_eq, ExprOps.node_kind, bind_tc_ok] at h
          simp at h

/-! ## The three list walks

Task #24's deviation 5: the cited two-`List` recursions became one index
recursion with three arms (both exhausted, both in range, or the arity throw),
so each is refined against the cited recursion run on the two `drop i`
suffixes.  The `ops` record is `sharedOpsC` (`Refine/TypeChecker.lean`'s
`lops`), and the `Env` argument every slot ignores is `lfe.env` — which is
exactly why the port can pass the index alone (task #24's note 3).

Each walk needs one *run* lemma per arm of the cited definition, in the
`Refine/StateC.lean` style: the state monad's `do` is unfolded once, against a
known first step. -/

open ConLeche.Cached in
/-- `checkDefEqList` on two exhausted lists. -/
theorem checkDefEqList_nil {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {d : Nat} {lst : CState} :
    (ConLeche.checkDefEqList ops lenv d [] []).run lst = .ok ((), lst) := rfl

open ConLeche.Cached in
/-- `checkDefEqList`'s step, at a comparison that succeeded. -/
theorem checkDefEqList_cons {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {d : Nat} {a b : ConLeche.Expr} {xs ys : List ConLeche.Expr} {lst lst' : CState}
    (hstep : (ops.isDefEq lenv d a b).run lst = .ok (true, lst')) :
    (ConLeche.checkDefEqList ops lenv d (a :: xs) (b :: ys)).run lst
      = (ConLeche.checkDefEqList ops lenv d xs ys).run lst' := by
  rw [ConLeche.checkDefEqList]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show (ops.isDefEq lenv d a b) lst = Except.ok (true, lst') from hstep]
  rfl

open ConLeche.Cached in
/-- `checkTypedList` on two exhausted lists. -/
theorem checkTypedList_nil {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {d : Nat} {lst : CState} :
    (ConLeche.checkTypedList ops lenv d [] []).run lst = .ok ((), lst) := rfl

open ConLeche.Cached in
/-- `checkTypedList`'s step, at an inference and a comparison that succeeded. -/
theorem checkTypedList_cons {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {d : Nat} {a t ty : ConLeche.Expr} {xs ts : List ConLeche.Expr}
    {lst lst1 lst2 : CState}
    (hinf : (ops.inferType lenv d a).run lst = .ok (ty, lst1))
    (hdef : (ops.isDefEq lenv d ty t).run lst1 = .ok (true, lst2)) :
    (ConLeche.checkTypedList ops lenv d (a :: xs) (t :: ts)).run lst
      = (ConLeche.checkTypedList ops lenv d xs ts).run lst2 := by
  rw [ConLeche.checkTypedList]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show (ops.inferType lenv d a) lst = Except.ok (ty, lst1) from hinf]
  simp only [Except.bind]
  rw [show (ops.isDefEq lenv d ty t) lst1 = Except.ok (true, lst2) from hdef]
  rfl

open ConLeche.Cached in
/-- `checkAnnotList` on an exhausted list. -/
theorem checkAnnotList_nil {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {d : Nat} {lst : CState} :
    (ConLeche.checkAnnotList ops lenv d []).run lst = .ok ((), lst) := rfl

open ConLeche.Cached in
/-- `checkAnnotList`'s step, at an annotation that reproduced its input. -/
theorem checkAnnotList_cons {ops : ConLeche.CheckerOps CheckCM} {lenv : ConLeche.Env}
    {d : Nat} {a aA : ConLeche.Expr} {xs : List ConLeche.Expr} {lst lst1 : CState}
    (hann : (ops.annotate lenv d a).run lst = .ok (aA, lst1)) (heq : (aA == a) = true) :
    (ConLeche.checkAnnotList ops lenv d (a :: xs)).run lst
      = (ConLeche.checkAnnotList ops lenv d xs).run lst1 := by
  rw [ConLeche.checkAnnotList]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show (ops.annotate lenv d a) lst = Except.ok (aA, lst1) from hann]
  simp only [Except.bind, heq]
  rfl

/-- A `drop` past the end is the empty list, on the abstracted side. -/
theorem absExprs_drop_nil {xs : alloc.vec.Vec expr.Expr} {i : Std.Usize}
    (h : xs.val.length ≤ i.val) : (absExprs xs).drop i.val = [] :=
  List.drop_eq_nil_of_le (by simp only [absExprs, List.length_map]; omega)

/-- `ConLeche/Kernel/CheckerBase.lean:200-209 checkDefEqList` — the index
recursion, on the two suffixes at the cursor. -/
theorem check_def_eq_list_from_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {xs ys : alloc.vec.Vec expr.Expr} (hxs : ExprsWF xs) (hys : ExprsWF ys) :
    ∀ (N : Nat) (i : Std.Usize) (st st' : cached.state_c.CState) (fe : fenv.FEnv)
      (depth : Std.U64),
      xs.val.length - i.val ≤ N → StateWF st → FEnvWF fe →
      checker_base.check_def_eq_list_from mode st fe depth xs ys i = ok (.Ok (), st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ∃ lst', (ConLeche.checkDefEqList (TypeChecker.lops mode lfe) lfe.env depth.val
            ((absExprs xs).drop i.val) ((absExprs ys).drop i.val)).run lst = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st' := by
  intro N
  induction N with
  | zero =>
    intro i st st' fe depth hN hsw hfw h lst lfe hsr hfr
    rw [checker_base.check_def_eq_list_from.eq_def] at h
    simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len xs by scalar_tac)] at h
    split at h
    · rename_i hy
      simp only [Result.ok.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨lst, ?_, hsr, hsw⟩
      rw [absExprs_drop_nil (by scalar_tac), absExprs_drop_nil (by scalar_tac)]
      exact checkDefEqList_nil
    · rw [if_pos (show i >= alloc.vec.Vec.len xs by scalar_tac)] at h
      simp [bind_eq_ok_iff] at h
  | succ N ih =>
    intro i st st' fe depth hN hsw hfw h lst lfe hsr hfr
    rw [checker_base.check_def_eq_list_from.eq_def] at h
    simp only [] at h
    by_cases hix : i.val ≥ xs.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len xs by scalar_tac)] at h
      split at h
      · rename_i hy
        simp only [Result.ok.injEq] at h
        obtain ⟨-, rfl⟩ := h
        refine ⟨lst, ?_, hsr, hsw⟩
        rw [absExprs_drop_nil (by scalar_tac), absExprs_drop_nil (by scalar_tac)]
        exact checkDefEqList_nil
      · rw [if_pos (show i >= alloc.vec.Vec.len xs by scalar_tac)] at h
        simp [bind_eq_ok_iff] at h
    · rw [if_neg (show ¬ i >= alloc.vec.Vec.len xs by scalar_tac),
        if_neg (show ¬ i >= alloc.vec.Vec.len xs by scalar_tac)] at h
      split at h
      · simp [bind_eq_ok_iff] at h
      · rename_i hy
        obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨rr, st1⟩ := q
        obtain ⟨hltx, hewf, hdropx⟩ := ExprOps.vec_index_expr hxs he
        obtain ⟨hlty, he1wf, hdropy⟩ := ExprOps.vec_index_expr hys he1
        cases rr with
        | Err er => simp at h
        | Ok ok1 =>
          cases ok1 with
          | false => simp [bind_eq_ok_iff] at h
          | true =>
            simp only [reduceIte] at h
            obtain ⟨i4, hi4, h⟩ := bind_eq_ok_iff.mp h
            have hi4v : i4.val = i.val + 1 := HashMap.uscalar_add_eq hi4
            obtain ⟨lst1, hrun, hsr1, hsw1⟩ :=
              (TypeChecker.is_def_eq_core_refines hfuel hk).ok st fe depth e e1 true st1
                hsw hfw hewf he1wf hq lst lfe hsr hfr
            have hstep : ((TypeChecker.lops mode lfe).isDefEq lfe.env depth.val
                (absExpr e) (absExpr e1)).run lst = .ok (true, lst1) := by
              rw [TypeChecker.sharedOpsC_isDefEq]; exact hrun
            obtain ⟨lst2, hrun2, hsr2, hsw2⟩ :=
              ih i4 st1 st' fe depth (by omega) hsw1 hfw h lst1 lfe hsr1 hfr
            refine ⟨lst2, ?_, hsr2, hsw2⟩
            rw [hdropx, hdropy, checkDefEqList_cons hstep, ← hi4v]
            exact hrun2

/-- `ConLeche/Kernel/CheckerBase.lean:200-209 checkDefEqList` — the pairwise
definitional-equality check of two spines. -/
theorem check_def_eq_list_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {depth : Std.U64}
    {xs ys : alloc.vec.Vec expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hxs : ExprsWF xs) (hys : ExprsWF ys)
    (h : checker_base.check_def_eq_list mode st fe depth xs ys = ok (.Ok (), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkDefEqList (TypeChecker.lops mode lfe) lfe.env depth.val
          (absExprs xs) (absExprs ys)).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  intro lst lfe hsr hfr
  rw [checker_base.check_def_eq_list] at h
  obtain ⟨lst', hrun, rest⟩ :=
    check_def_eq_list_from_refines hfuel hk hxs hys xs.val.length 0#usize st st' fe depth
      (by scalar_tac) hsw hfw h lst lfe hsr hfr
  exact ⟨lst', by simpa using hrun, rest⟩

/-- `ConLeche/Kernel/CheckerBase.lean:156-168 checkTypedList` — the index
recursion, on the two suffixes at the cursor. -/
theorem check_typed_list_from_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {xs ts : alloc.vec.Vec expr.Expr} (hxs : ExprsWF xs) (hts : ExprsWF ts) :
    ∀ (N : Nat) (i : Std.Usize) (st st' : cached.state_c.CState) (fe : fenv.FEnv)
      (depth : Std.U64),
      xs.val.length - i.val ≤ N → StateWF st → FEnvWF fe →
      checker_base.check_typed_list_from mode st fe depth xs ts i = ok (.Ok (), st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ∃ lst', (ConLeche.checkTypedList (TypeChecker.lops mode lfe) lfe.env depth.val
            ((absExprs xs).drop i.val) ((absExprs ts).drop i.val)).run lst = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st' := by
  intro N
  induction N with
  | zero =>
    intro i st st' fe depth hN hsw hfw h lst lfe hsr hfr
    rw [checker_base.check_typed_list_from.eq_def] at h
    simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len xs by scalar_tac)] at h
    split at h
    · rename_i hy
      simp only [Result.ok.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨lst, ?_, hsr, hsw⟩
      rw [absExprs_drop_nil (by scalar_tac), absExprs_drop_nil (by scalar_tac)]
      exact checkTypedList_nil
    · rw [if_pos (show i >= alloc.vec.Vec.len xs by scalar_tac)] at h
      simp [bind_eq_ok_iff] at h
  | succ N ih =>
    intro i st st' fe depth hN hsw hfw h lst lfe hsr hfr
    rw [checker_base.check_typed_list_from.eq_def] at h
    simp only [] at h
    by_cases hix : i.val ≥ xs.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len xs by scalar_tac)] at h
      split at h
      · rename_i hy
        simp only [Result.ok.injEq] at h
        obtain ⟨-, rfl⟩ := h
        refine ⟨lst, ?_, hsr, hsw⟩
        rw [absExprs_drop_nil (by scalar_tac), absExprs_drop_nil (by scalar_tac)]
        exact checkTypedList_nil
      · rw [if_pos (show i >= alloc.vec.Vec.len xs by scalar_tac)] at h
        simp [bind_eq_ok_iff] at h
    · rw [if_neg (show ¬ i >= alloc.vec.Vec.len xs by scalar_tac),
        if_neg (show ¬ i >= alloc.vec.Vec.len xs by scalar_tac)] at h
      split at h
      · simp [bind_eq_ok_iff] at h
      · rename_i hy
        obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨rr, st1⟩ := q
        obtain ⟨hltx, hewf, hdropx⟩ := ExprOps.vec_index_expr hxs he
        cases rr with
        | Err er => simp at h
        | Ok ty =>
          obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨q2, hq2, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨rr2, st2⟩ := q2
          obtain ⟨hltt, he1wf, hdropt⟩ := ExprOps.vec_index_expr hts he1
          obtain ⟨lst1, hrun, hsr1, hsw1, htywf⟩ :=
            (TypeChecker.infer_type_core_refines hfuel hk).ok st fe depth e ty st1
              hsw hfw hewf hq lst lfe hsr hfr
          cases rr2 with
          | Err er => simp at h
          | Ok ok1 =>
            cases ok1 with
            | false => simp [bind_eq_ok_iff] at h
            | true =>
              simp only [reduceIte] at h
              obtain ⟨i5, hi5, h⟩ := bind_eq_ok_iff.mp h
              have hi5v : i5.val = i.val + 1 := HashMap.uscalar_add_eq hi5
              obtain ⟨lst2, hrun2, hsr2, hsw2⟩ :=
                (TypeChecker.is_def_eq_core_refines hfuel hk).ok st1 fe depth ty e1 true st2
                  hsw1 hfw htywf he1wf hq2 lst1 lfe hsr1 hfr
              have hinf : ((TypeChecker.lops mode lfe).inferType lfe.env depth.val
                  (absExpr e)).run lst = .ok (absExpr ty, lst1) := by
                rw [TypeChecker.sharedOpsC_inferType]; exact hrun
              have hdef : ((TypeChecker.lops mode lfe).isDefEq lfe.env depth.val
                  (absExpr ty) (absExpr e1)).run lst1 = .ok (true, lst2) := by
                rw [TypeChecker.sharedOpsC_isDefEq]; exact hrun2
              obtain ⟨lst3, hrun3, hsr3, hsw3⟩ :=
                ih i5 st2 st' fe depth (by omega) hsw2 hfw h lst2 lfe hsr2 hfr
              refine ⟨lst3, ?_, hsr3, hsw3⟩
              rw [hdropx, hdropt, checkTypedList_cons hinf hdef, ← hi5v]
              exact hrun3

/-- `ConLeche/Kernel/CheckerBase.lean:156-168 checkTypedList` — each
expression's inferred type against the corresponding expected type. -/
theorem check_typed_list_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {depth : Std.U64}
    {xs ts : alloc.vec.Vec expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hxs : ExprsWF xs) (hts : ExprsWF ts)
    (h : checker_base.check_typed_list mode st fe depth xs ts = ok (.Ok (), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkTypedList (TypeChecker.lops mode lfe) lfe.env depth.val
          (absExprs xs) (absExprs ts)).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  intro lst lfe hsr hfr
  rw [checker_base.check_typed_list] at h
  obtain ⟨lst', hrun, rest⟩ :=
    check_typed_list_from_refines hfuel hk hxs hts xs.val.length 0#usize st st' fe depth
      (by scalar_tac) hsw hfw h lst lfe hsr hfr
  exact ⟨lst', by simpa using hrun, rest⟩

/-- `ConLeche/Kernel/CheckerBase.lean:170-184 checkAnnotList` — the index
recursion, on the suffix at the cursor. -/
theorem check_annot_list_from_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {xs : alloc.vec.Vec expr.Expr} (hxs : ExprsWF xs) :
    ∀ (N : Nat) (i : Std.Usize) (st st' : cached.state_c.CState) (fe : fenv.FEnv)
      (depth : Std.U64),
      xs.val.length - i.val ≤ N → StateWF st → FEnvWF fe →
      checker_base.check_annot_list_from mode st fe depth xs i = ok (.Ok (), st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
        ∃ lst', (ConLeche.checkAnnotList (TypeChecker.lops mode lfe) lfe.env depth.val
            ((absExprs xs).drop i.val)).run lst = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st' := by
  intro N
  induction N with
  | zero =>
    intro i st st' fe depth hN hsw hfw h lst lfe hsr hfr
    rw [checker_base.check_annot_list_from.eq_def] at h
    simp only [] at h
    rw [if_pos (show i >= alloc.vec.Vec.len xs by scalar_tac)] at h
    simp only [Result.ok.injEq] at h
    obtain ⟨-, rfl⟩ := h
    refine ⟨lst, ?_, hsr, hsw⟩
    rw [absExprs_drop_nil (by scalar_tac)]
    exact checkAnnotList_nil
  | succ N ih =>
    intro i st st' fe depth hN hsw hfw h lst lfe hsr hfr
    rw [checker_base.check_annot_list_from.eq_def] at h
    simp only [] at h
    split at h
    · simp only [Result.ok.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨lst, ?_, hsr, hsw⟩
      rw [absExprs_drop_nil (by scalar_tac)]
      exact checkAnnotList_nil
    · rename_i hlt
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨rr, st1⟩ := q
      obtain ⟨hltx, hewf, hdropx⟩ := ExprOps.vec_index_expr hxs he
      cases rr with
      | Err er => simp at h
      | Ok aA =>
        obtain ⟨lst1, hrun, hsr1, hsw1, hawf⟩ :=
          (TypeChecker.annotate_core_refines hfuel hk).ok st fe depth e aA st1
            hsw hfw hewf hq lst lfe hsr hfr
        obtain ⟨c, hc, h⟩ := bind_eq_ok_iff.mp h
        have hcv := Expr.beq_refines hawf hewf hc
        cases c with
        | false => simp [bind_eq_ok_iff] at h
        | true =>
          simp only [reduceIte] at h
          obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
          have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
          have hann : ((TypeChecker.lops mode lfe).annotate lfe.env depth.val
              (absExpr e)).run lst = .ok (absExpr aA, lst1) := by
            rw [TypeChecker.sharedOpsC_annotate]; exact hrun
          have heq : (absExpr aA == absExpr e) = true := by
            rw [← decide_eq_beq_expr, ← hcv]
          obtain ⟨lst2, hrun2, hsr2, hsw2⟩ :=
            ih i2 st1 st' fe depth (by omega) hsw1 hfw h lst1 lfe hsr1 hfr
          refine ⟨lst2, ?_, hsr2, hsw2⟩
          rw [hdropx, checkAnnotList_cons hann heq, ← hi2v]
          exact hrun2

/-- `ConLeche/Kernel/CheckerBase.lean:170-184 checkAnnotList` — each
expression is a fixed point of the annotation pass. -/
theorem check_annot_list_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {depth : Std.U64}
    {xs : alloc.vec.Vec expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hxs : ExprsWF xs)
    (h : checker_base.check_annot_list mode st fe depth xs = ok (.Ok (), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkAnnotList (TypeChecker.lops mode lfe) lfe.env depth.val
          (absExprs xs)).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' := by
  intro lst lfe hsr hfr
  rw [checker_base.check_annot_list] at h
  obtain ⟨lst', hrun, rest⟩ :=
    check_annot_list_from_refines hfuel hk hxs xs.val.length 0#usize st st' fe depth
      (by scalar_tac) hsw hfw h lst lfe hsr hfr
  exact ⟨lst', by simpa using hrun, rest⟩


/-! ## `checkConstantVal` — the one check every declaration kind runs first

This is the only function in the module that reaches the core, so it carries
the knot hypotheses; and it is the only one that reads
`decl_check::consts_resolve_f_fast`, whose refinement belongs to
`Refine/DeclCheck.lean` — a sibling task-#56 file this one may not import.
That fact is named here as a `Prop` and travels as a hypothesis, so the
dependency is visible in every statement that needs it. -/

/-- **What `Refine/DeclCheck.lean` owes this file.**
`decl_check::consts_resolve_f_fast` refines `Expr.constsResolveF`
(`ConLeche/Kernel/DeclCheck.lean:197-204`, the `@[csimp]` twin of the spec
walk). -/
def ConstsResolveFSpec : Prop :=
  ∀ (fe : fenv.FEnv) (lfe : ConLeche.FEnv) (e : expr.Expr) (b : Bool),
    FEnvRel fe lfe → FEnvWF fe → ExprWF e →
    decl_check.consts_resolve_f_fast fe e = ok b →
    b = ConLeche.Expr.constsResolveF lfe (absExpr e)

open ConLeche.Cached in
/-- The tail of `checkConstantValF` past the annotation
(`CheckerBase.lean:91-97`, `DeclCheck.lean:479-485`), written out because the
port splits the `do` there (task #24's deviation 7: the annotation's
state-threading call must be a tail call). -/
def constantValTail (ops : ConLeche.CheckerOps CheckCM) (lfe : ConLeche.FEnv)
    (cv : ConLeche.ConstantVal) (type : ConLeche.Expr) : CheckCM ConLeche.ConstantVal := do
  unless ConLeche.Expr.allLevelParamsDefined cv.levelParams type do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless ConLeche.Expr.constsResolveF lfe type do
    throw (.invalid s!"unknown constant in type of {cv.name}")
  let stype ← ops.inferType lfe.env 0 type
  let _u ← ops.ensureSort lfe.env 0 stype
  pure { cv with type := type }

open ConLeche.Cached in
/-- The tail, run: both guards held and both core calls succeeded. -/
theorem constantValTail_run {ops : ConLeche.CheckerOps CheckCM} {lfe : ConLeche.FEnv}
    {cv : ConLeche.ConstantVal} {type stype : ConLeche.Expr} {u : ConLeche.Level}
    {lst lst1 lst2 : CState}
    (h1 : ConLeche.Expr.allLevelParamsDefined cv.levelParams type = true)
    (h2 : ConLeche.Expr.constsResolveF lfe type = true)
    (hinf : (ops.inferType lfe.env 0 type).run lst = .ok (stype, lst1))
    (hsort : (ops.ensureSort lfe.env 0 stype).run lst1 = .ok (u, lst2)) :
    (constantValTail ops lfe cv type).run lst
      = .ok ({ cv with type := type }, lst2) := by
  rw [constantValTail]
  simp only [h1, h2, reduceIte, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]
  rw [show (ops.inferType lfe.env 0 type) lst = Except.ok (stype, lst1) from hinf]
  simp only []
  rw [show (ops.ensureSort lfe.env 0 stype) lst1 = Except.ok (u, lst2) from hsort]

open ConLeche.Cached in
/-- `checkConstantValF` at a run whose six syntactic guards passed and whose
annotation succeeded: it *is* the tail, on the post-annotation state. -/
theorem checkConstantValF_at_annot {ops : ConLeche.CheckerOps CheckCM}
    {lfe : ConLeche.FEnv} {cv : ConLeche.ConstantVal} {type : ConLeche.Expr}
    {lst lst1 : CState}
    (h1 : (lfe.find? cv.name).isSome = false)
    (h2 : ConLeche.reservedBasisNames.contains cv.name = false)
    (h3 : cv.name.isProjFnShape = false)
    (h4 : ConLeche.Name.nodup cv.levelParams = true)
    (h5 : cv.type.looseBVarsBounded 0 = true)
    (h6 : cv.type.hasFvar = false)
    (hann : (ops.annotate lfe.env 0 cv.type).run lst = .ok (type, lst1)) :
    (ConLeche.checkConstantValF ops lfe cv).run lst
      = (constantValTail ops lfe cv type).run lst1 := by
  rw [ConLeche.checkConstantValF, constantValTail]
  simp only [h1, h2, h3, h4, h5, h6, Bool.false_eq_true, if_false, if_true,
    eq_self_iff_true, reduceIte, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure]
  rw [show (ops.annotate lfe.env 0 cv.type) lst = Except.ok (type, lst1) from hann]
  rfl

/-- `ConLeche/Kernel/CheckerBase.lean:73-97 checkConstantVal`,
`ConLeche/Kernel/DeclCheck.lean:463-485 checkConstantValF` — the tail past the
annotation: the level-parameter and resolution guards on the annotated type,
the type's own sort, and the record update `{ cv with type := type }`. -/
theorem check_constant_val_after_annot_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hcr : ConstsResolveFSpec)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {cv cv' : env.ConstantVal}
    {ty : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hty : ExprWF ty)
    (h : checker_base.check_constant_val_after_annot mode st fe cv ty = ok (.Ok cv', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (constantValTail (TypeChecker.lops mode lfe) lfe
          (absConstantVal cv) (absExpr ty)).run lst
          = .ok (absConstantVal cv', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv' := by
  intro lst lfe hsr hfr
  obtain ⟨hnwf, hlpwf, htywf⟩ := hcv
  rw [checker_base.check_constant_val_after_annot] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbabs := ExprOps.all_level_params_defined_fast_refines hlpwf hty hb
  split at h
  · rename_i hbt
    subst hbt
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1abs := hcr fe lfe ty b1 hfr hfw hty hb1
    split at h
    · rename_i hb1t
      subst hb1t
      obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r1, st1⟩ := q
      cases r1 with
      | Err er => simp at h
      | Ok stype =>
        obtain ⟨lst1, hrun1, hsr1, hsw1, hstwf⟩ :=
          (TypeChecker.infer_type_core_refines hfuel hk).ok st fe 0#u64 ty stype st1
            hsw hfw hty hq lst lfe hsr hfr
        obtain ⟨q2, hq2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r2, st2⟩ := q2
        cases r2 with
        | Err er => simp at h
        | Ok u =>
          obtain ⟨lst2, hrun2, hsr2, hsw2, huwf⟩ :=
            (TypeChecker.ensure_sort_core_refines hfuel hk).ok st1 fe 0#u64 stype u st2
              hsw1 hfw hstwf hq2 lst1 lfe hsr1 hfr
          obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
          simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
          obtain ⟨hcveq, rfl⟩ := h
          have hvv : v.val = cv.level_params.val := PropWhen.names_copy_val hv
          have hnv : n = cv.name := by simpa using hn.symm
          have hinf : ((TypeChecker.lops mode lfe).inferType lfe.env 0
              (absExpr ty)).run lst = .ok (absExpr stype, lst1) := by
            rw [TypeChecker.sharedOpsC_inferType]
            exact hrun1
          have hsort : ((TypeChecker.lops mode lfe).ensureSort lfe.env 0
              (absExpr stype)).run lst1 = .ok (absLevel u, lst2) := by
            rw [TypeChecker.sharedOpsC_ensureSort]
            exact hrun2
          have hvabs : absNames v = absNames cv.level_params := by
            rw [absNames, absNames, hvv]
          refine ⟨lst2, ?_, hsr2, hsw2, ?_⟩
          · rw [constantValTail_run (cv := absConstantVal cv)
              (by simp only [absConstantVal]; rw [← hbabs])
              (by rw [← hb1abs]) hinf hsort, ← hcveq]
            simp only [absConstantVal, hnv, hvabs]
          · rw [← hcveq]
            refine ⟨by rw [hnv]; exact hnwf, ?_, hty⟩
            intro x hx; exact hlpwf x (by rw [hvv] at hx; exact hx)
    · simp [bind_eq_ok_iff] at h
  · simp [bind_eq_ok_iff] at h

/-- `ConLeche/Kernel/CheckerBase.lean:73-97 checkConstantVal`,
`ConLeche/Kernel/DeclCheck.lean:463-485 checkConstantValF` — the checks common
to all declarations: fresh name, no reserved basis name, no reserved projection
shape, well-formed universe parameters, and a type that is a type and mentions
only declared parameters.  The result is the constant with its type
**annotated**; the guards run on the annotated type. -/
theorem check_constant_val_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hcr : ConstsResolveFSpec)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {cv cv' : env.ConstantVal}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv)
    (h : checker_base.check_constant_val mode st fe cv = ok (.Ok cv', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkConstantValF (TypeChecker.lops mode lfe) lfe
          (absConstantVal cv)).run lst = .ok (absConstantVal cv', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv' := by
  intro lst lfe hsr hfr
  obtain ⟨hnwf, hlpwf, htywf⟩ := hcv
  rw [checker_base.check_constant_val] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  have hfind := FEnv.find_refines hfr hfw hnwf ho
  cases o with
  | some ci => simp [core.option.Option.is_some, bind_eq_ok_iff] at h
  | none =>
    simp only [core.option.Option.is_some, Bool.false_eq_true, if_false] at h
    have h1 : ((lfe.find? (absName cv.name)).isSome) = false := by
      rw [← hfind]; simp
    obtain ⟨rv, hrv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hrvabs, hrvwf⟩ := BasisNames.reserved_basis_names_refines hrv
    have hb1abs := Name.contains_refines hrvwf hnwf hb1
    rw [hrvabs] at hb1abs
    split at h
    · simp [bind_eq_ok_iff] at h
    · rename_i hb1f
      have h2 : ConLeche.reservedBasisNames.contains (absName cv.name) = false := by
        rw [← hb1abs]; simpa using hb1f
      obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
      have hb2abs := CoreK.name_is_proj_fn_shape_refines hnwf hb2
      split at h
      · simp [bind_eq_ok_iff] at h
      · rename_i hb2f
        have h3 : (absName cv.name).isProjFnShape = false := by
          rw [← hb2abs]; simpa using hb2f
        obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
        have hb3abs := name_nodup_refines hlpwf hb3
        split at h
        · rename_i hb3t
          obtain ⟨b4, hb4, h⟩ := bind_eq_ok_iff.mp h
          have hb4abs := ExprOps.loose_bvars_bounded_refines htywf hb4
          rw [show ((0#u64 : Std.U64)).val = 0 from rfl] at hb4abs
          split at h
          · rename_i hb4t
            obtain ⟨b5, hb5, h⟩ := bind_eq_ok_iff.mp h
            have hb5abs := ExprOps.has_fvar_refines htywf hb5
            split at h
            · simp [bind_eq_ok_iff] at h
            · rename_i hb5f
              obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨r1, st1⟩ := q
              cases r1 with
              | Err er => simp at h
              | Ok ty =>
                obtain ⟨lst1, hrun1, hsr1, hsw1, htyawf⟩ :=
                  (TypeChecker.annotate_core_refines hfuel hk).ok st fe 0#u64 cv.ty ty st1
                    hsw hfw htywf hq lst lfe hsr hfr
                obtain ⟨lst2, hrun2, hsr2, hsw2, hcv'wf⟩ :=
                  check_constant_val_after_annot_refines hfuel hk hcr hsw1 hfw
                    ⟨hnwf, hlpwf, htywf⟩ htyawf h lst1 lfe hsr1 hfr
                refine ⟨lst2, ?_, hsr2, hsw2, hcv'wf⟩
                have hann : ((TypeChecker.lops mode lfe).annotate lfe.env 0
                    (absExpr cv.ty)).run lst = .ok (absExpr ty, lst1) := by
                  rw [TypeChecker.sharedOpsC_annotate]; exact hrun1
                rw [checkConstantValF_at_annot (cv := absConstantVal cv) h1 h2 h3 ?_ ?_ ?_ hann]
                · exact hrun2
                · simp only [absConstantVal]; rw [← hb3abs]; exact hb3t
                · simp only [absConstantVal]; rw [← hb4abs]; exact hb4t
                · simp only [absConstantVal]; rw [← hb5abs]; simpa using hb5f
          · simp [bind_eq_ok_iff] at h
        · simp [bind_eq_ok_iff] at h

/-! ## The projection stages

`checkProjRuleF` is one long `do`; the port splits it at the annotation and
again at each guard group (task #24's deviation 7), so the three tails have no
con-leche name of their own.  They are refined against the *tails* of the cited
`do` block, written out here with their line ranges — the indexed mirror's
spelling throughout, since it is the mirror's one-pass walkers the port calls
(`openPisAtFvarsF`, `instPisAtF`, `instLamsAtF`, `domsMatchAuxA`). -/

open ConLeche.Cached in
/-- The frame walks and the definitional parameter/domain pins, the tail of
`checkProjRuleF` from `CheckerBase.lean:277` / `DeclCheck.lean:783` on. -/
def projRuleCertsTail (ops : ConLeche.CheckerOps CheckCM) (lfe : ConLeche.FEnv)
    (pty : ConLeche.Expr) (cvj : ConLeche.ConstantVal) (nP nF : Nat)
    (rhsA : ConLeche.Expr) : CheckCM ConLeche.Expr := do
  let some (fvsP, _) := ConLeche.openPisAtFvarsF nP pty 0
    | throw (.notImplemented "projection type telescope")
  let some (cdomsP, crestP) := ConLeche.Expr.instPisAtF fvsP cvj.type
    | throw (.notImplemented "projection constructor telescope")
  ConLeche.checkDefEqList ops lfe.env (nP + nF) (fvsP.map ConLeche.Expr.fvarTypeD) cdomsP
  let some (xFvs, _) := ConLeche.openPisAtFvarsF nF crestP nP
    | throw (.notImplemented "projection constructor telescope")
  let some (ldoms, _) := ConLeche.Expr.instLamsAtF (fvsP ++ xFvs) rhsA
    | throw (.notImplemented "projection rule telescope")
  ConLeche.checkDefEqList ops lfe.env (nP + nF)
    ((fvsP ++ xFvs).map ConLeche.Expr.fvarTypeD) ldoms
  let _rhsTy ← ops.inferType lfe.env 0 rhsA
  pure rhsA

open ConLeche.Cached in
/-- The syntactic stage past the well-formedness guard, the tail of
`checkProjRuleF` from `CheckerBase.lean:264` / `DeclCheck.lean:774` on. -/
def projRuleShapeTail (ops : ConLeche.CheckerOps CheckCM) (lfe : ConLeche.FEnv)
    (pty : ConLeche.Expr) (cvj : ConLeche.ConstantVal) (nP nF i : Nat)
    (rhsA : ConLeche.Expr) : CheckCM ConLeche.Expr := do
  let some (rbinders, rrbody) := rhsA.stripLams (nP + nF)
    | throw (.notImplemented "projection rule telescope")
  unless rrbody == ConLeche.Expr.bvar (nF - 1 - i) do
    throw (.notImplemented "projection rule body")
  let some (cbindersR, _) := cvj.type.stripPis (nP + nF)
    | throw (.notImplemented "projection constructor telescope")
  unless ConLeche.domsMatchAuxA (fun _ e => e) rbinders.toArray cbindersR.toArray
      0 0 (nP + nF) do
    throw (.notImplemented "projection rule domain mismatch")
  projRuleCertsTail ops lfe pty cvj nP nF rhsA

/-- `ConLeche/Kernel/CheckerBase.lean:252-289 checkProjRule`,
`ConLeche/Kernel/DeclCheck.lean:763-795 checkProjRuleF` — the annotated rule's
four-way well-formedness conjunction (`:261-262` / `:771-772`), which the port
spells as an `if` nest. -/
theorem proj_rule_wf_refines (hcr : ConstsResolveFSpec)
    {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {rhs_a : expr.Expr}
    {lps : alloc.vec.Vec name.Name} {b : Bool}
    (hfr : FEnvRel fe lfe) (hfw : FEnvWF fe) (hrwf : ExprWF rhs_a) (hlps : NamesWF lps)
    (h : checker_base.proj_rule_wf fe rhs_a lps = ok b) :
    b = (ConLeche.Expr.allLevelParamsDefined (absNames lps) (absExpr rhs_a) &&
      ConLeche.Expr.constsResolveF lfe (absExpr rhs_a) &&
      (absExpr rhs_a).looseBVarsBounded 0 && !(absExpr rhs_a).hasFvar) := by
  rw [checker_base.proj_rule_wf] at h
  obtain ⟨b0, hb0, h⟩ := bind_eq_ok_iff.mp h
  have h0 := ExprOps.all_level_params_defined_fast_refines hlps hrwf hb0
  split at h
  · rename_i ht0
    subst ht0
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have h1 := hcr fe lfe rhs_a b1 hfr hfw hrwf hb1
    split at h
    · rename_i ht1
      subst ht1
      obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
      have h2 := ExprOps.loose_bvars_bounded_refines hrwf hb2
      rw [show ((0#u64 : Std.U64)).val = 0 from rfl] at h2
      split at h
      · rename_i ht2
        subst ht2
        obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
        have h3 := ExprOps.has_fvar_refines hrwf hb3
        simp only [Result.ok.injEq] at h
        rw [← h, ← h0, ← h1, ← h2, ← h3]
        simp
      · rename_i hf2
        simp only [Result.ok.injEq] at h
        rw [← h, ← h0, ← h1, ← h2]
        have hb2f : b2 = false := by simpa using hf2
        simp [hb2f]
    · rename_i hf1
      simp only [Result.ok.injEq] at h
      rw [← h, ← h0, ← h1]
      have hb1f : b1 = false := by simpa using hf1
      simp [hb1f]
  · rename_i hf0
    simp only [Result.ok.injEq] at h
    rw [← h, ← h0]
    have hb0f : b0 = false := by simpa using hf0
    simp [hb0f]


open ConLeche.Cached in
/-- The certificate tail, run: the four telescope walks found their shapes and
both comparison lists and the inference succeeded. -/
theorem projRuleCertsTail_run {ops : ConLeche.CheckerOps CheckCM} {lfe : ConLeche.FEnv}
    {pty rhsA : ConLeche.Expr} {cvj : ConLeche.ConstantVal} {nP nF : Nat}
    {fvsP cdomsP xFvs ldoms : List ConLeche.Expr}
    {x1 crestP x2 x3 rhsTy : ConLeche.Expr} {lst lst1 lst2 lst3 : CState}
    (h1 : ConLeche.openPisAtFvarsF nP pty 0 = some (fvsP, x1))
    (h2 : ConLeche.Expr.instPisAtF fvsP cvj.type = some (cdomsP, crestP))
    (hd1 : (ConLeche.checkDefEqList ops lfe.env (nP + nF)
      (fvsP.map ConLeche.Expr.fvarTypeD) cdomsP).run lst = .ok ((), lst1))
    (h3 : ConLeche.openPisAtFvarsF nF crestP nP = some (xFvs, x2))
    (h4 : ConLeche.Expr.instLamsAtF (fvsP ++ xFvs) rhsA = some (ldoms, x3))
    (hd2 : (ConLeche.checkDefEqList ops lfe.env (nP + nF)
      ((fvsP ++ xFvs).map ConLeche.Expr.fvarTypeD) ldoms).run lst1 = .ok ((), lst2))
    (hinf : (ops.inferType lfe.env 0 rhsA).run lst2 = .ok (rhsTy, lst3)) :
    (projRuleCertsTail ops lfe pty cvj nP nF rhsA).run lst = .ok (rhsA, lst3) := by
  rw [projRuleCertsTail]
  simp only [h1, h2, h3, h4, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]
  rw [show (ConLeche.checkDefEqList ops lfe.env (nP + nF)
    (fvsP.map ConLeche.Expr.fvarTypeD) cdomsP) lst = Except.ok ((), lst1) from hd1]
  simp only []
  rw [show (ConLeche.checkDefEqList ops lfe.env (nP + nF)
    ((fvsP ++ xFvs).map ConLeche.Expr.fvarTypeD) ldoms) lst1 = Except.ok ((), lst2) from hd2]
  simp only []
  rw [show (ops.inferType lfe.env 0 rhsA) lst2 = Except.ok (rhsTy, lst3) from hinf]

/-- `ConLeche/Kernel/CheckerBase.lean:252-289 checkProjRule`,
`ConLeche/Kernel/DeclCheck.lean:763-795 checkProjRuleF` — the frame walks and
the definitional parameter/domain pins, then the rule's own inference.

The `r` the port returns is `rhs_a` itself; the inferred type is discarded on
both sides. -/
theorem check_proj_rule_certs_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {pty rhs_a r : expr.Expr}
    {cvj : env.ConstantVal} {n_p n_f : Std.U64}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hpty : ExprWF pty) (hcvj : ConstantValWF cvj)
    (hrhs : ExprWF rhs_a)
    (h : checker_base.check_proj_rule_certs mode st fe pty cvj n_p n_f rhs_a
      = ok (.Ok r, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (projRuleCertsTail (TypeChecker.lops mode lfe) lfe (absExpr pty)
          (absConstantVal cvj) n_p.val n_f.val (absExpr rhs_a)).run lst
          = .ok (absExpr r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r := by
  intro lst lfe hsr hfr
  obtain ⟨-, -, hcvjty⟩ := hcvj
  rw [checker_base.check_proj_rule_certs] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ := open_pis_at_fvars_f_refines hpty ho
  cases o with
  | none => simp [bind_eq_ok_iff] at h
  | some p =>
    obtain ⟨fvs_p, y1⟩ := p
    obtain ⟨hfvspwf, hy1wf⟩ := howf (fvs_p, y1) rfl
    obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨h1abs, h1wf⟩ := ExprOps.inst_pis_at_f_refines hfvspwf hcvjty ho1
    cases o1 with
    | none => simp [bind_eq_ok_iff] at h
    | some p1 =>
      obtain ⟨cdoms_p, crest_p⟩ := p1
      obtain ⟨hcdomswf, hcrestwf⟩ := h1wf (cdoms_p, crest_p) rfl
      obtain ⟨ptypes, hptypes, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hptabs, hptwf⟩ := fvar_types_refines hfvspwf hptypes
      obtain ⟨ii, hii, h⟩ := bind_eq_ok_iff.mp h
      have hiiv : ii.val = n_p.val + n_f.val := HashMap.uscalar_add_eq hii
      obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r0, st1⟩ := q
      cases r0 with
      | Err er => simp at h
      | Ok _u0 =>
        obtain ⟨lst1, hrun1, hsr1, hsw1⟩ :=
          check_def_eq_list_refines hfuel hk hsw hfw hptwf hcdomswf hq lst lfe hsr hfr
        obtain ⟨o2, ho2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨h2abs, h2wf⟩ := open_pis_at_fvars_f_refines hcrestwf ho2
        cases o2 with
        | none => simp [bind_eq_ok_iff] at h
        | some p2 =>
          obtain ⟨x_fvs, y2⟩ := p2
          obtain ⟨hxfvswf, hy2wf⟩ := h2wf (x_fvs, y2) rfl
          obtain ⟨frame, hframe, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hfrabs, hfrwf⟩ := CoreK.append_exprs_refines hfvspwf hxfvswf hframe
          obtain ⟨o3, ho3, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨h3abs, h3wf⟩ := ExprOps.inst_lams_at_f_refines hfrwf hrhs ho3
          cases o3 with
          | none => simp [bind_eq_ok_iff] at h
          | some p3 =>
            obtain ⟨ldoms, y3⟩ := p3
            obtain ⟨hldomswf, hy3wf⟩ := h3wf (ldoms, y3) rfl
            obtain ⟨ftypes, hftypes, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hftabs, hftwf⟩ := fvar_types_refines hfrwf hftypes
            obtain ⟨q2, hq2, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨r1, st2⟩ := q2
            cases r1 with
            | Err er => simp at h
            | Ok _u1 =>
              obtain ⟨lst2, hrun2, hsr2, hsw2⟩ :=
                check_def_eq_list_refines hfuel hk hsw1 hfw hftwf hldomswf hq2
                  lst1 lfe hsr1 hfr
              obtain ⟨q3, hq3, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨r2, st3⟩ := q3
              cases r2 with
              | Err er => simp at h
              | Ok rhsty =>
                obtain ⟨lst3, hrun3, hsr3, hsw3, -⟩ :=
                  (TypeChecker.infer_type_core_refines hfuel hk).ok st2 fe 0#u64 rhs_a rhsty st3
                    hsw2 hfw hrhs hq3 lst2 lfe hsr2 hfr
                simp at h
                obtain ⟨rfl, rfl⟩ := h
                refine ⟨lst3, ?_, hsr3, hsw3, hrhs⟩
                rw [show ((0#u64 : Std.U64)).val = 0 from rfl] at hrun3 hoabs
                rw [hiiv] at hrun1 hrun2
                rw [hptabs] at hrun1
                rw [hftabs, hfrabs] at hrun2
                have e1 : ConLeche.openPisAtFvarsF n_p.val (absExpr pty) 0
                    = some (absExprs fvs_p, absExpr y1) := by rw [← hoabs]; rfl
                have e2 : ConLeche.Expr.instPisAtF (absExprs fvs_p)
                    (absConstantVal cvj).type
                    = some (absExprs cdoms_p, absExpr crest_p) := by
                  simp only [absConstantVal]; rw [← h1abs]; rfl
                have e3 : ConLeche.openPisAtFvarsF n_f.val (absExpr crest_p) n_p.val
                    = some (absExprs x_fvs, absExpr y2) := by rw [← h2abs]; rfl
                have e4 : ConLeche.Expr.instLamsAtF
                    (absExprs fvs_p ++ absExprs x_fvs) (absExpr rhs_a)
                    = some (absExprs ldoms, absExpr y3) := by
                  rw [← hfrabs, ← h3abs]; rfl
                have hinf : ((TypeChecker.lops mode lfe).inferType lfe.env 0
                    (absExpr rhs_a)).run lst2 = .ok (absExpr rhsty, lst3) := by
                  rw [TypeChecker.sharedOpsC_inferType]; exact hrun3
                exact projRuleCertsTail_run e1 e2 hrun1 e3 e4 hrun2 hinf


open ConLeche.Cached in
/-- The shape tail, run: the λ telescope, the body and the domain comparison
all held, so the whole is the certificate tail. -/
theorem projRuleShapeTail_run {ops : ConLeche.CheckerOps CheckCM} {lfe : ConLeche.FEnv}
    {pty rhsA rrbody x : ConLeche.Expr} {cvj : ConLeche.ConstantVal} {nP nF i : Nat}
    {rbinders cbindersR : List (ConLeche.Expr × ConLeche.BinderMeta)} {lst : CState}
    (h1 : rhsA.stripLams (nP + nF) = some (rbinders, rrbody))
    (h2 : (rrbody == ConLeche.Expr.bvar (nF - 1 - i)) = true)
    (h3 : cvj.type.stripPis (nP + nF) = some (cbindersR, x))
    (h4 : ConLeche.domsMatchAuxA (fun _ e => e) rbinders.toArray cbindersR.toArray
      0 0 (nP + nF) = true) :
    (projRuleShapeTail ops lfe pty cvj nP nF i rhsA).run lst
      = (projRuleCertsTail ops lfe pty cvj nP nF rhsA).run lst := by
  rw [projRuleShapeTail]
  simp only [h1, h2, h3, h4, reduceIte, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure]

open ConLeche.Cached in
/-- `checkProjRuleF` at a run whose head guards passed and whose annotation
succeeded: it *is* the shape tail, on the post-annotation state. -/
theorem checkProjRuleF_at_annot {ops : ConLeche.CheckerOps CheckCM} {lfe : ConLeche.FEnv}
    {pty rhs rhsA : ConLeche.Expr} {cvj : ConLeche.ConstantVal} {lps : List ConLeche.Name}
    {nP nF i : Nat} {lst lst1 : CState}
    (h1 : ConLeche.Expr.pisToLams (nP + nF) cvj.type (ConLeche.Expr.bvar (nF - 1 - i))
      = some rhs)
    (h2 : (!rhs.hasFvar && rhs.looseBVarsBounded 0) = true)
    (hann : (ops.annotate lfe.env 0 rhs).run lst = .ok (rhsA, lst1))
    (h3 : (ConLeche.Expr.allLevelParamsDefined lps rhsA &&
      ConLeche.Expr.constsResolveF lfe rhsA &&
      rhsA.looseBVarsBounded 0 && !rhsA.hasFvar) = true) :
    (ConLeche.checkProjRuleF ops lfe pty cvj lps nP nF i).run lst
      = (projRuleShapeTail ops lfe pty cvj nP nF i rhsA).run lst1 := by
  rw [ConLeche.checkProjRuleF, projRuleShapeTail]
  simp only [h1, h2, reduceIte, StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure, StateT.pure, Except.pure]
  rw [show (ops.annotate lfe.env 0 rhs) lst = Except.ok (rhsA, lst1) from hann]
  simp only [h3, reduceIte, Except.bind]
  rfl

/-- `ConLeche/Kernel/CheckerBase.lean:252-289 checkProjRule`,
`ConLeche/Kernel/DeclCheck.lean:763-795 checkProjRuleF` — the syntactic stage
past the annotation: the rule's λ telescope, its body `bvar (nF - 1 - i)`, and
its domains against the constructor's (`domsMatchAuxA`).

The cited body is `bvar (nF - 1 - i)`; the port computes it as
`sub_nat nF (1 + i)`, which is the same truncated subtraction. -/
theorem check_proj_rule_shape_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {pty rhs_a r : expr.Expr}
    {cvj : env.ConstantVal} {n_p n_f i : Std.U64}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hpty : ExprWF pty) (hcvj : ConstantValWF cvj)
    (hrhs : ExprWF rhs_a)
    (h : checker_base.check_proj_rule_shape mode st fe pty cvj n_p n_f i rhs_a
      = ok (.Ok r, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (projRuleShapeTail (TypeChecker.lops mode lfe) lfe (absExpr pty)
          (absConstantVal cvj) n_p.val n_f.val i.val (absExpr rhs_a)).run lst
          = .ok (absExpr r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r := by
  intro lst lfe hsr hfr
  have hcvjty : ExprWF cvj.ty := hcvj.2.2
  rw [checker_base.check_proj_rule_shape] at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  have hi1v : i1.val = n_p.val + n_f.val := HashMap.uscalar_add_eq hi1
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ := ExprOps.strip_lams_refines hrhs ho
  rw [hi1v] at hoabs
  cases o with
  | none => simp [bind_eq_ok_iff] at h
  | some p =>
    obtain ⟨rbinders, rrbody⟩ := p
    have hrbwf : ExprOps.BindersWF rbinders := (howf (rbinders, rrbody) rfl).1
    have hrrwf : ExprWF rrbody := (howf (rbinders, rrbody) rfl).2
    obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨eb, heb, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    have hi2v : i2.val = 1 + i.val := HashMap.uscalar_add_eq hi2
    have hi3v : i3.val = n_f.val - 1 - i.val := by
      rw [ExprOps.sub_nat_val hi3, hi2v]; omega
    have hebabs : absExpr eb = ConLeche.Expr.bvar (n_f.val - 1 - i.val) := by
      rw [Expr.bvar_refines heb, hi3v]
    have hbabs := Expr.beq_refines hrrwf (Expr.bvar_wf heb) hb
    split at h
    · rename_i hbt
      subst hbt
      obtain ⟨o1, ho1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨h1abs, h1wf⟩ := ExprOps.strip_pis_refines hcvjty ho1
      rw [hi1v] at h1abs
      cases o1 with
      | none => simp [bind_eq_ok_iff] at h
      | some p1 =>
        obtain ⟨cbinders_r, y⟩ := p1
        have hcbwf : ExprOps.BindersWF cbinders_r := (h1wf (cbinders_r, y) rfl).1
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have hb1abs := doms_match_aux_refines_array hrbwf hcbwf hb1
        rw [hi1v, show ((0#u64 : Std.U64)).val = 0 from rfl] at hb1abs
        split at h
        · rename_i hb1t
          obtain ⟨lst', hrun, rest⟩ :=
            check_proj_rule_certs_refines hfuel hk hsw hfw hpty hcvj hrhs h lst lfe hsr hfr
          refine ⟨lst', ?_, rest⟩
          have e1 : (absExpr rhs_a).stripLams (n_p.val + n_f.val)
              = some (ExprOps.absBinders rbinders, absExpr rrbody) := by
            rw [← hoabs]; rfl
          have e3 : (absConstantVal cvj).type.stripPis (n_p.val + n_f.val)
              = some (ExprOps.absBinders cbinders_r, absExpr y) := by
            simp only [absConstantVal]; rw [← h1abs]; rfl
          have e2 : (absExpr rrbody == ConLeche.Expr.bvar (n_f.val - 1 - i.val)) = true := by
            rw [← hebabs, ← decide_eq_beq_expr, ← hbabs]
          have e4 : ConLeche.domsMatchAuxA (fun _ e => e)
              (ExprOps.absBinders rbinders).toArray (ExprOps.absBinders cbinders_r).toArray
              0 0 (n_p.val + n_f.val) = true := by
            rw [← hb1abs]; exact hb1t
          rw [projRuleShapeTail_run e1 e2 e3 e4]
          exact hrun
        · simp [bind_eq_ok_iff] at h
    · simp [bind_eq_ok_iff] at h

/-- `ConLeche/Kernel/CheckerBase.lean:252-289 checkProjRule`,
`ConLeche/Kernel/DeclCheck.lean:763-795 checkProjRuleF` — stage 3: the
reduction rule, λ over the constructor telescope returning field `i`,
annotated, with its λ-domains the constructor's.

The four-way well-formedness conjunction is `proj_rule_wf`, so this lemma
carries `ConstsResolveFSpec` too. -/
theorem check_proj_rule_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hcr : ConstsResolveFSpec)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {pty r : expr.Expr}
    {cvj : env.ConstantVal} {lps : alloc.vec.Vec name.Name} {n_p n_f i : Std.U64}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hpty : ExprWF pty) (hcvj : ConstantValWF cvj)
    (hlps : NamesWF lps)
    (h : checker_base.check_proj_rule mode st fe pty cvj lps n_p n_f i = ok (.Ok r, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.checkProjRuleF (TypeChecker.lops mode lfe) lfe (absExpr pty)
          (absConstantVal cvj) (absNames lps) n_p.val n_f.val i.val).run lst
          = .ok (absExpr r, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF r := by
  intro lst lfe hsr hfr
  have hcvjty : ExprWF cvj.ty := hcvj.2.2
  rw [checker_base.check_proj_rule] at h
  obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
  have hi1v : i1.val = n_p.val + n_f.val := HashMap.uscalar_add_eq hi1
  obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨i3, hi3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨eb, heb, h⟩ := bind_eq_ok_iff.mp h
  have hi2v : i2.val = 1 + i.val := HashMap.uscalar_add_eq hi2
  have hi3v : i3.val = n_f.val - 1 - i.val := by
    rw [ExprOps.sub_nat_val hi3, hi2v]; omega
  have hebabs : absExpr eb = ConLeche.Expr.bvar (n_f.val - 1 - i.val) := by
    rw [Expr.bvar_refines heb, hi3v]
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hoabs, howf⟩ :=
    ExprOps.pis_to_lams_refines i1.val i1 cvj.ty eb o rfl hcvjty (Expr.bvar_wf heb) ho
  rw [hi1v, hebabs] at hoabs
  cases o with
  | none => simp [bind_eq_ok_iff] at h
  | some rhs =>
    have hrhswf : ExprWF rhs := howf rhs rfl
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    have hbabs := ExprOps.has_fvar_refines hrhswf hb
    split at h
    · simp [bind_eq_ok_iff] at h
    · rename_i hbf
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      have hb1abs := ExprOps.loose_bvars_bounded_refines hrhswf hb1
      rw [show ((0#u64 : Std.U64)).val = 0 from rfl] at hb1abs
      split at h
      · rename_i hb1t
        obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r0, st1⟩ := q
        cases r0 with
        | Err er => simp at h
        | Ok rhs_a =>
          obtain ⟨lst1, hrun1, hsr1, hsw1, hrawf⟩ :=
            (TypeChecker.annotate_core_refines hfuel hk).ok st fe 0#u64 rhs rhs_a st1
              hsw hfw hrhswf hq lst lfe hsr hfr
          obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
          have hb2abs := proj_rule_wf_refines hcr hfr hfw hrawf hlps hb2
          split at h
          · rename_i hb2t
            obtain ⟨lst2, hrun2, rest⟩ :=
              check_proj_rule_shape_refines hfuel hk hsw1 hfw hpty hcvj hrawf h
                lst1 lfe hsr1 hfr
            refine ⟨lst2, ?_, rest⟩
            have hann : ((TypeChecker.lops mode lfe).annotate lfe.env 0
                (absExpr rhs)).run lst = .ok (absExpr rhs_a, lst1) := by
              rw [TypeChecker.sharedOpsC_annotate]
              rw [show ((0#u64 : Std.U64)).val = 0 from rfl] at hrun1
              exact hrun1
            have e1 : ConLeche.Expr.pisToLams (n_p.val + n_f.val)
                (absConstantVal cvj).type
                (ConLeche.Expr.bvar (n_f.val - 1 - i.val)) = some (absExpr rhs) := by
              simp only [absConstantVal]; rw [← hoabs]; rfl
            have e2 : (!(absExpr rhs).hasFvar && (absExpr rhs).looseBVarsBounded 0)
                = true := by
              rw [← hbabs, ← hb1abs]
              simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
              exact ⟨by simpa using hbf, hb1t⟩
            have e3 : (ConLeche.Expr.allLevelParamsDefined (absNames lps) (absExpr rhs_a) &&
                ConLeche.Expr.constsResolveF lfe (absExpr rhs_a) &&
                (absExpr rhs_a).looseBVarsBounded 0 && !(absExpr rhs_a).hasFvar) = true := by
              rw [← hb2abs]; exact hb2t
            rw [checkProjRuleF_at_annot e1 e2 hann e3]
            exact hrun2
          · simp [bind_eq_ok_iff] at h
      · simp [bind_eq_ok_iff] at h

end ConRon.Refine.CheckerBase

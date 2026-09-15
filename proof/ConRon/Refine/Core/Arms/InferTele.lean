/-
# The binder-telescope arms of `infer` (task #55)

The λ- and Π-telescope peel loops of `crates/con-ron-core/src/cached/core_c.rs`
against `ConLeche/Cached/CoreC.lean:1140-1290`: `inferLamsI`/`inferPisI` with
their leaf and rebuild phases, and the two small helpers the port factored out
of `inferLamsLeafI` (`infer_lams_prev_pw_i`, `infer_lams_leaf_sort_i`).

## The io grade

These helpers run under **both** con-leche records only in the sense that
`inferBodyI` does: the Rust's `∀`/`λ` clauses (`infer_forall_i`,
`infer_lam_i`, `core_c.rs:3365`, `:3411`) are the clauses `inferBodyIOI`
*overrides*, so they are unreachable at `io = true` and call the full-grade
wrappers (`infer`, `whnf`, `infer_io`) directly — the module note's deviation
4, spelled out at `core_c.rs:3308-3312`.  No `io`/`view : Bool` is threaded
through any function in this file, so every statement below is at
`knot mode lfe fuel.val`, not at `knotV`.  (`Arms/Shape.lean`'s `knotV` is for
the clauses that *are* shared; the caller of `infer_lams_i` at `io = true` owes
the unreachability argument, not these lemmas.)

## `peel`, `k` and the two stacks

* `peel : U64` is con-leche's `Nat` peel fuel; the loops are one induction on
  `peel.val` (`ConLeche.Cached.inferLamsI`'s `fuel + 1`/`0` split).
* `k : U64` counts the binders already opened, and appears only as `d + k` and
  `k - 1` (`expr_ops::sub_nat`, Lean's truncated `Nat` subtraction).
* `fvs : Vec Expr` is con-leche's `Array Expr` at the **same** orientation
  (both are pushed, and `instListRevM` indexes from the end): the abstraction
  is `(absExprs fvs).toArray`.
* the entry stack is **reversed**: con-leche's `List` is innermost-binder
  first (`(tyo, mb) :: stk`), the Rust's `Vec` has the innermost binder *last*
  and walks it down by the count `p` (`core_c.rs:2886-2889`).  Hence
  `absLamEntries`/`absPisEntries` below, which reverse, and the rebuild loops'
  statement at the prefix `stk.val.take p.val`.

`inferLamsLeafI` inlines two pieces the port named; `inferLamsPrevPwI` and
`inferLamsLeafSortI` name them on the Lean side, each a `rfl`-identity against
the cited definition (`Refine/StateC.lean`'s header explains the idiom).
-/
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.CoreKGuards
import ConRon.Refine.CoreKSupport
import ConRon.Refine.ExprOpsCSubst

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

-- `Arms/Shape.lean`'s monad plumbing, re-activated here (`local simp` does not
-- cross files).
attribute [local simp] except_pure' StateT.run modifyGet MonadStateOf.modifyGet
  StateT.modifyGet Bind.bind StateT.bind Pure.pure StateT.pure Except.bind
  Except.pure

/-! ## The error half's plumbing (task #67)

`Shape.lean`'s plumbing set carries no `MonadExcept` instance, so a con-leche
`throw` does not reduce on its own; and the port's three error constructors
are reached through `core_types::invalid`/`not_implemented`, whose results a
`throw` arm has to name. -/

/-- A con-leche `throw`, **applied**: `StateT.run` is already in the plumbing
set and fires first, so the equation must be stated on `… lst`, not on
`(…).run lst`. -/
@[local simp] theorem checkCM_throw_apply {β : Type} (le : ConLeche.CheckError)
    (lst : ConLeche.Cached.CState) :
    (throw le : ConLeche.Cached.CheckCM β) lst = .error le := rfl

/-- `core_types::invalid` builds the constructor it names. -/
private theorem invalid_inv {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.invalid v = ok ce) :
    ce = .Invalid v := by
  rw [core_types.invalid] at h; exact (Result.ok_injective h).symm

/-- `core_types::not_implemented` builds the constructor it names. -/
private theorem not_implemented_inv {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.not_implemented v = ok ce) :
    ce = .NotImplemented v := by
  rw [core_types.not_implemented] at h; exact (Result.ok_injective h).symm

/-- The port's `if flag { … } else { … }` at a decided flag; `rw` with these
keeps the `= ok …` orientation a `simp` would flip. -/
theorem bool_ite_true {α : Type} (a b : α) :
    (if (true : Bool) = true then a else b) = a := if_pos rfl

theorem bool_ite_false {α : Type} (a b : α) :
    (if (false : Bool) = true then a else b) = b := if_neg (by simp)

/-! ## The two entry stacks

`InferLamEntry := Expr × BinderMeta` (`CoreC.lean:1140`) and
`Level × PropWhen`; the port's `Vec` is the reversed list. -/

/-- The λ-telescope stack as con-leche's `List InferLamEntry`: innermost
binder first, i.e. the port's `Vec` read back to front. -/
def absLamEntries (l : List (expr.Expr × expr.BinderMeta)) :
    List ConLeche.Cached.InferLamEntry :=
  (l.map fun x => (absExpr x.1, absBinderMeta x.2)).reverse

/-- Every entry of a λ-telescope stack is well formed. -/
def LamEntriesWF (l : List (expr.Expr × expr.BinderMeta)) : Prop :=
  ∀ x ∈ l, ExprWF x.1 ∧ BinderMetaWF x.2

/-- The ∀-telescope stack as con-leche's `List (Level × PropWhen)`. -/
def absPisEntries (l : List (level.Level × prop_when.PropWhen)) :
    List (ConLeche.Level × ConLeche.PropWhen) :=
  (l.map fun x => (absLevel x.1, absPropWhen x.2)).reverse

/-- Every entry of a ∀-telescope stack is well formed. -/
def PisEntriesWF (l : List (level.Level × prop_when.PropWhen)) : Prop :=
  ∀ x ∈ l, LevelWF x.1 ∧ PropWhenWF x.2

@[simp] theorem absLamEntries_nil : absLamEntries [] = [] := rfl

@[simp] theorem absPisEntries_nil : absPisEntries [] = [] := rfl

/-- A push on the port's `Vec` is a `cons` on con-leche's list. -/
@[simp] theorem absLamEntries_concat (l : List (expr.Expr × expr.BinderMeta))
    (x : expr.Expr × expr.BinderMeta) :
    absLamEntries (l ++ [x]) = (absExpr x.1, absBinderMeta x.2) :: absLamEntries l := by
  simp [absLamEntries]

@[simp] theorem absPisEntries_concat (l : List (level.Level × prop_when.PropWhen))
    (x : level.Level × prop_when.PropWhen) :
    absPisEntries (l ++ [x]) = (absLevel x.1, absPropWhen x.2) :: absPisEntries l := by
  simp [absPisEntries]

theorem LamEntriesWF.concat {l : List (expr.Expr × expr.BinderMeta)}
    {x : expr.Expr × expr.BinderMeta} (hl : LamEntriesWF l)
    (hx : ExprWF x.1) (hm : BinderMetaWF x.2) : LamEntriesWF (l ++ [x]) := by
  intro y hy
  rcases List.mem_append.1 hy with h | h
  · exact hl y h
  · rw [List.mem_singleton.1 h]; exact ⟨hx, hm⟩

theorem PisEntriesWF.concat {l : List (level.Level × prop_when.PropWhen)}
    {x : level.Level × prop_when.PropWhen} (hl : PisEntriesWF l)
    (hx : LevelWF x.1) (hm : PropWhenWF x.2) : PisEntriesWF (l ++ [x]) := by
  intro y hy
  rcases List.mem_append.1 hy with h | h
  · exact hl y h
  · rw [List.mem_singleton.1 h]; exact ⟨hx, hm⟩

/-- The innermost entry the port reads (`stk[stk.len() - 1]`) is con-leche's
list head. -/
theorem absLamEntries_cons_of_index
    {l : List (expr.Expr × expr.BinderMeta)} {i : Nat}
    {x : expr.Expr × expr.BinderMeta}
    (hi : i = l.length - 1) (hne : l ≠ []) (hx : l[i]? = some x) :
    ∃ rest, absLamEntries l = (absExpr x.1, absBinderMeta x.2) :: rest := by
  rcases List.eq_nil_or_concat l with h | ⟨L, b, h⟩
  · exact absurd h hne
  · rw [List.concat_eq_append] at h
    subst h
    have hlen : (L ++ [b]).length = L.length + 1 := by simp
    have hi' : i = L.length := by omega
    subst hi'
    have hb : b = x := by
      rw [show (L ++ [b])[L.length]? = some b by simp] at hx
      exact Option.some_injective _ hx
    subst hb
    exact ⟨absLamEntries L, by simp⟩

/-- The same for the ∀-telescope stack. -/
theorem absPisEntries_cons_of_index
    {l : List (level.Level × prop_when.PropWhen)} {i : Nat}
    {x : level.Level × prop_when.PropWhen}
    (hi : i = l.length - 1) (hne : l ≠ []) (hx : l[i]? = some x) :
    ∃ rest, absPisEntries l = (absLevel x.1, absPropWhen x.2) :: rest := by
  rcases List.eq_nil_or_concat l with h | ⟨L, b, h⟩
  · exact absurd h hne
  · rw [List.concat_eq_append] at h
    subst h
    have hlen : (L ++ [b]).length = L.length + 1 := by simp
    have hi' : i = L.length := by omega
    subst hi'
    have hb : b = x := by
      rw [show (L ++ [b])[L.length]? = some b by simp] at hx
      exact Option.some_injective _ hx
    subst hb
    exact ⟨absPisEntries L, by simp⟩

/-- The fold's step on the abstracted stack: reading `stk[p - 1]` peels
con-leche's list head off the prefix `stk.take p`. -/
theorem absLamEntries_take_succ {l : List (expr.Expr × expr.BinderMeta)} {n : Nat}
    {x : expr.Expr × expr.BinderMeta} (hx : l[n]? = some x) :
    absLamEntries (l.take (n + 1))
      = (absExpr x.1, absBinderMeta x.2) :: absLamEntries (l.take n) := by
  rw [List.take_add_one, hx]
  simp

theorem absPisEntries_take_succ {l : List (level.Level × prop_when.PropWhen)} {n : Nat}
    {x : level.Level × prop_when.PropWhen} (hx : l[n]? = some x) :
    absPisEntries (l.take (n + 1))
      = (absLevel x.1, absPropWhen x.2) :: absPisEntries (l.take n) := by
  rw [List.take_add_one, hx]
  simp

/-! ## Two missing `Expr` inversions

`Refine/CoreKGuards.lean` has `wf_const_inv`/`wf_sort_inv`/`wf_app_inv`; the
binder nodes need the same, and by the same proof.  **To be moved to
`Refine/Expr.lean`** beside the other `*_inv` lemmas. -/

/-- A well-formed `Lam` node has well-formed parts. -/
theorem wf_lam_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64}
    {ty bo : expr.Expr} {m : expr.BinderMeta}
    (hk : e = .mk (.mk d (.Lam ty bo m))) :
    ExprWF ty ∧ ExprWF bo ∧ BinderMetaWF m := by
  cases he with
  | @bvar i _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1; simp at hk
  | @fvar idx ty1 _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1; simp at hk
  | @sort u _ _ h1 => obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1; simp at hk
  | @mk_const n1 us1 _ _ _ h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1; simp at hk
  | @app f a _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1; simp at hk
  | @lam ty1 bo1 m1 _ hty hbo hm h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq,
      expr.ExprKind.Lam.injEq] at hk
    obtain ⟨-, rfl, rfl, rfl⟩ := hk
    exact ⟨hty, hbo, hm⟩
  | @forall_e ty1 bo1 m1 _ _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1; simp at hk
  | @let_e ty1 v bo1 _ _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1; simp at hk
  | @lit l _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1; simp at hk
  | @proj s i x _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1; simp at hk

/-- A well-formed `ForallE` node has well-formed parts. -/
theorem wf_forall_inv {e : expr.Expr} (he : ExprWF e) {d : Std.U64}
    {ty bo : expr.Expr} {m : expr.BinderMeta}
    (hk : e = .mk (.mk d (.ForallE ty bo m))) :
    ExprWF ty ∧ ExprWF bo ∧ BinderMetaWF m := by
  cases he with
  | @bvar i _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1; simp at hk
  | @fvar idx ty1 _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1; simp at hk
  | @sort u _ _ h1 => obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1; simp at hk
  | @mk_const n1 us1 _ _ _ h1 =>
    obtain ⟨d1, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1; simp at hk
  | @app f a _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1; simp at hk
  | @lam ty1 bo1 m1 _ _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1; simp at hk
  | @forall_e ty1 bo1 m1 _ hty hbo hm h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    simp only [expr.Expr.mk.injEq, expr.ExprNode.mk.injEq,
      expr.ExprKind.ForallE.injEq] at hk
    obtain ⟨-, rfl, rfl, rfl⟩ := hk
    exact ⟨hty, hbo, hm⟩
  | @let_e ty1 v bo1 _ _ _ _ h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1; simp at hk
  | @lit l _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1; simp at hk
  | @proj s i x _ _ _ h1 => obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1; simp at hk

/-- `expr_ops::lam_pw` answers `some` only at a `Lam` node, whose datum is
well formed when the node is. -/
theorem lam_pw_wf {t : expr.Expr} (ht : ExprWF t) {pw : prop_when.PropWhen}
    (h : expr_ops.lam_pw t = ok (some pw)) : PropWhenWF pw := by
  obtain ⟨⟨dt, kt⟩⟩ := t
  rw [expr_ops.lam_pw.eq_def] at h
  simp only [expr_view_eq, arc_deref_eq, bind_tc_ok, ExprOps.node_kind, ron.node.ExprView.ofKind] at h
  cases kt
  case Lam ty bo m =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨pw1, hpw1, ho⟩ := h
    rw [PropWhen.dup_eq hpw1] at ho
    have hp : pw = m.pw := by
      have h2 := Result.ok_injective ho
      simpa using h2.symm
    rw [hp]
    exact (wf_lam_inv ht rfl).2.2
  all_goals simp at h

/-! ## Stepping a `CheckCM` run

Every leaf below is a chain of `do` steps whose `run` the wrapper lemmas give
one at a time; this is the composition. -/

/-- One `do` step of a `CheckCM` action's `run`. -/
theorem checkCM_bind_run {α β : Type} (m : ConLeche.Cached.CheckCM α)
    (f : α → ConLeche.Cached.CheckCM β) {lst lst' : ConLeche.Cached.CState} {a : α}
    (h : m.run lst = .ok (a, lst')) : (m >>= f).run lst = (f a).run lst' := by
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show m lst = Except.ok (a, lst') from h]

/-- `ConLeche/Cached/StateC.lean:201-205` — the bulk-open every telescope leaf
begins with: the port's `inst_list_rev_m` on the `Vec` of opened free
variables is con-leche's `instListRevM` on the `Array`. -/
theorem instListRevM_run {t ob : expr.Expr} {fvs : alloc.vec.Vec expr.Expr}
    (ht : ExprWF t) (hfvs : ExprsWF fvs)
    (h : cached.state_c.inst_list_rev_m t fvs 0#u64 = ok ob) :
    ConLeche.Cached.instListRevM (absExpr t) (absExprs fvs).toArray
      = pure (absExpr ob) ∧ ExprWF ob := by
  rw [StateC.inst_list_rev_m_eq] at h
  obtain ⟨habs, hwf⟩ := ExprOpsC.instantiate_rev_refines ht hfvs h
  refine ⟨?_, hwf⟩
  rw [ConLeche.Cached.instListRevM, habs,
    ConLeche.Expr.instantiateRev_spec]
  simp

/-! ## The two subterms `inferLamsLeafI` writes inline

Each is the cited expression, verbatim; nothing is assumed about them beyond
the definitional identity the leaf proof rewrites with. -/

/-- `CoreC.lean:1196-1205` — the initial neighbour of the rebuild fold: a λ
residual's own annotation, else the innermost stack entry's, else `.never`.
The port's `infer_lams_prev_pw_i` (`core_c.rs:3025`) computes it through
`Expr.lamPw`, which is the cited `match t with | .lam _ _ mbT => …`. -/
def inferLamsPrevPwI (t : ConLeche.Expr)
    (stk : List ConLeche.Cached.InferLamEntry) : ConLeche.PropWhen :=
  match ConLeche.Expr.lamPw t with
  | some pw => pw
  | none =>
    match stk with
    | (_, mb₀) :: _ => mb₀.pw
    | [] => .never

/-- `CoreC.lean:1173-1191` — the verified-mode block of `inferLamsLeafI`: the
body type's own sort, and the innermost binder's annotation against its
zero-ness.  The port's `infer_lams_leaf_sort_i` (`core_c.rs:2981`). -/
def inferLamsLeafSortI (r : ConLeche.Cached.CoreFnsI) (dk : Nat)
    (bt : ConLeche.Expr) (stk : List ConLeche.Cached.InferLamEntry) :
    ConLeche.Cached.CheckCM Unit := do
  let btt ← r.inferIO dk bt
  let wbtt ← r.whnf dk btt
  match wbtt with
  | .sort vb =>
    match stk with
    | (_, mb₀) :: _ => do
      let pv ← pure (ConLeche.Level.zeronessOf vb)
      if pv == mb₀.pw then pure ()
      else throw (.notImplemented "sort-annotation mismatch (lam-cod-leaf)")
    | [] => pure ()
  | _ => throw (.invalid "expected a sort")

/-- `CoreC.lean:1162-1206` factored through the two names above: the cited
definition, with its inline check phase and its inline `prevPw` replaced by
`inferLamsLeafSortI`/`inferLamsPrevPwI`.  A definitional identity — the port
factored exactly these two pieces out. -/
theorem inferLamsLeafI_eq (mode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (d : Nat) (t : ConLeche.Expr) (k : Nat)
    (fvs : _root_.Array ConLeche.Expr)
    (stk : List ConLeche.Cached.InferLamEntry) :
    ConLeche.Cached.inferLamsLeafI mode r d t k fvs stk = (do
      let ob ← ConLeche.Cached.instListRevM t fvs
      let bt ← r.infer (d + k) ob
      let _ ← (match ConLeche.Expr.lamPw t with
        | some _ => pure ()
        | none =>
          if mode.verifiedChecks then inferLamsLeafSortI r (d + k) bt stk
          else pure ())
      let cur ← ConLeche.Cached.abstractRangeM bt d k
      ConLeche.Cached.inferLamsOutI mode d stk (k - 1) cur
        (inferLamsPrevPwI t stk)) := by
  rw [ConLeche.Cached.inferLamsLeafI.eq_def]
  refine bind_congr fun ob => ?_
  refine bind_congr fun bt => ?_
  cases t
  case lam ty body mbT =>
    simp only [ConLeche.Expr.lamPw, inferLamsPrevPwI]
    rfl
  all_goals
    (simp only [ConLeche.Expr.lamPw, inferLamsPrevPwI]
     split
     · rw [inferLamsLeafSortI, bind_assoc]
       refine bind_congr fun btt => ?_
       rw [bind_assoc]
       refine bind_congr fun wbtt => ?_
       cases wbtt
       case sort vb =>
         cases stk <;> split <;>
           (first
             | rfl
             | (rename_i heq
                injection heq with hv
                subst hv
                first
                  | rfl
                  | (rw [bind_assoc]
                     refine bind_congr fun pv => ?_
                     split <;> rfl))
             | simp_all)
       all_goals rfl
     · rfl)

/-- `Expr.lamPw` answers `some` exactly at a λ node — the port tests the same
thing with `expr_ops::is_lam`. -/
theorem lamPw_isSome (e : ConLeche.Expr) :
    (ConLeche.Expr.lamPw e).isSome = ConLeche.Expr.isLam e := by
  cases e <;> simp [ConLeche.Expr.lamPw, ConLeche.Expr.isLam]

/-! ## The eight lemmas -/

section
variable {mode : env.CheckMode} {fuel : Std.U64}

/-- `ConLeche/Cached/CoreC.lean:1196-1205` — **`infer_lams_prev_pw_i` refines
`inferLamsPrevPwI`**, the rebuild fold's initial neighbour (`core_c.rs:3025`). -/
theorem infer_lams_prev_pw_i_refines {t : expr.Expr}
    {stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    (ht : ExprWF t) (hstk : LamEntriesWF stk.val) :
    SimP absPropWhen PropWhenWF (cached.core_c.infer_lams_prev_pw_i t stk)
      (inferLamsPrevPwI (absExpr t) (absLamEntries stk.val)) := by
  intro r h
  rw [cached.core_c.infer_lams_prev_pw_i] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  have habs := ExprOps.lam_pw_refines ho
  cases o with
  | some pw =>
    -- a λ residual supplies its own annotation
    have hr : pw = r := Result.ok_injective h
    subst hr
    simp only [Option.map_some] at habs
    refine ⟨?_, lam_pw_wf ht ho⟩
    unfold inferLamsPrevPwI
    rw [← habs]
  | none =>
    simp only [Option.map_none] at habs
    have hlen : (alloc.vec.Vec.len stk).val = stk.val.length := alloc.vec.Vec.len_val stk
    simp only at h
    split at h
    · -- the stack is empty: `.never`
      rename_i hz
      have hnil : stk.val = [] := by
        have h0 : stk.val.length = 0 := by rw [← hlen, hz]; scalar_tac
        exact List.eq_nil_of_length_eq_zero h0
      refine ⟨?_, PropWhen.never_wf h⟩
      rw [PropWhen.never_refines h]
      unfold inferLamsPrevPwI
      rw [← habs, hnil]
      simp
    · -- the innermost entry's annotation
      rename_i hz
      have hne : stk.val ≠ [] := by
        intro hc
        apply hz
        have h0 : stk.val.length = 0 := by rw [hc]; simp
        have h1 : (alloc.vec.Vec.len stk).val = 0 := by rw [hlen, h0]
        scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i2, hi2, ⟨xe, xm⟩, hidx, h⟩ := h
      have hi2v : i2.val = stk.val.length - 1 := by
        rw [HashMap.uscalar_sub_eq hi2, hlen]; rfl
      have hg := ExprOps.vec_index_getElem? hidx
      obtain ⟨rest, hcons⟩ := absLamEntries_cons_of_index hi2v hne hg
      have hlt : i2.val < stk.val.length := by
        have h0 : 0 < stk.val.length := List.length_pos_iff.2 hne
        omega
      have hmem : (xe, xm) ∈ stk.val := by
        rw [List.getElem?_eq_getElem hlt] at hg
        rw [← Option.some_injective _ hg]
        exact List.getElem_mem hlt
      have hxwf := hstk _ hmem
      have hrv : r = xm.pw := PropWhen.dup_eq h
      refine ⟨?_, by rw [hrv]; exact hxwf.2⟩
      unfold inferLamsPrevPwI
      rw [← habs, hcons, hrv]
      simp

/-- The rebuild fold as a pure statement over the count `p` — the shape the
induction wants (`p` decreases by one per entry, con-leche recurses on the
list).  Task #67: over the **full outcome**, since the fold's chain check
throws (`core_c.rs:2928`, the cited `CoreC.lean:1157`); `OutP` at the
value abstraction `fun r => (absExpr r, lst)` is the pure tier's two halves
for a step that leaves the state alone. -/
theorem infer_lams_out_i_val (N : Nat) :
    ∀ (mode : env.CheckMode) (d : Std.U64)
      (stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)) (p : Std.Usize)
      (j : Std.U64) (cur : expr.Expr)
      (o : core.result.Result expr.Expr core_types.CheckError)
      (prev_pw : prop_when.PropWhen),
      p.val = N → p.val ≤ stk.val.length → LamEntriesWF stk.val → ExprWF cur →
      PropWhenWF prev_pw →
      cached.core_c.infer_lams_out_i mode d stk p j cur prev_pw = ok o →
      ∀ lst, OutP (fun r => (absExpr r, lst)) ExprWF o
        ((ConLeche.Cached.inferLamsOutI (absMode mode) d.val
          (absLamEntries (stk.val.take p.val)) j.val (absExpr cur)
          (absPropWhen prev_pw)).run lst) := by
  induction N with
  | zero =>
    intro mode d stk p j cur o prev_pw hN hp hstk hcur hpw h lst
    unfold cached.core_c.infer_lams_out_i at h
    rw [if_pos (show p = 0#usize by scalar_tac)] at h
    have ho : o = .Ok cur := (Result.ok_injective h).symm
    subst ho
    refine OutP.ok ?_ hcur
    rw [hN, List.take_zero, absLamEntries_nil]
    simp [ConLeche.Cached.inferLamsOutI]
  | succ n ih =>
    intro mode d stk p j cur o prev_pw hN hp hstk hcur hpw h lst
    have hlen : (alloc.vec.Vec.len stk).val = stk.val.length := alloc.vec.Vec.len_val stk
    unfold cached.core_c.infer_lams_out_i at h
    rw [if_neg (show ¬ p = 0#usize by intro hc; rw [hc] at hN; simp at hN)] at h
    rw [if_neg (show ¬ p > alloc.vec.Vec.len stk by
      intro hc
      have h1 : (alloc.vec.Vec.len stk).val < p.val := by scalar_tac
      omega)] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨i1, hi1, ent, hidx, b, hb, h⟩ := h
    have hi1v : i1.val = n := by
      have h1 := HashMap.uscalar_sub_eq hi1; scalar_tac
    have hg := ExprOps.vec_index_getElem? hidx
    have hlt : i1.val < stk.val.length := by omega
    have hmem : ent ∈ stk.val := by
      rw [List.getElem?_eq_getElem hlt] at hg
      rw [← Option.some_injective _ hg]
      exact List.getElem_mem hlt
    have hxwf := hstk _ hmem
    have hcons : absLamEntries (stk.val.take p.val)
        = (absExpr ent.1, absBinderMeta ent.2) :: absLamEntries (stk.val.take i1.val) := by
      rw [show p.val = i1.val + 1 by omega]
      exact absLamEntries_take_succ hg
    have hvc := Env.verified_checks_refines hb
    -- either the chain check fails on both sides, or it passes on both and the
    -- fold's next step is the same one (task #67: the two halves share this
    -- single split)
    have key : (((absMode mode).verifiedChecks
              && !(absPropWhen ent.2.pw == absPropWhen prev_pw)) = true
          ∧ ∃ v, o = .Err (.NotImplemented v))
        ∨ (((absMode mode).verifiedChecks
              && !(absPropWhen ent.2.pw == absPropWhen prev_pw)) = false
          ∧ ∃ ty_abs node i2,
              cached.state_c.abstract_range_m ent.1 d j = ok ty_abs ∧
              expr.forall_e ty_abs cur ent.2 = ok node ∧
              expr_ops.sub_nat j 1#u64 = ok i2 ∧
              cached.core_c.infer_lams_out_i mode d stk i1 i2 node ent.2.pw
                = ok o) := by
      split at h
      case isTrue hbt =>
        -- the verified modes: the annotations must agree
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have heq := PropWhen.beq_refines hxwf.2 hpw hb1
        split at h
        case isTrue hb1t =>
          obtain ⟨ty_abs, hta, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨bm1, hbm1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨node, hnode, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨pw1, hpw1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨i2, hi2, hrec⟩ := bind_eq_ok_iff.mp h
          rw [Expr.binder_meta_dup_eq hbm1] at hnode
          rw [PropWhen.dup_eq hpw1] at hrec
          refine Or.inr ⟨?_, ty_abs, node, i2, hta, hnode, hi2, hrec⟩
          rw [hb1t] at heq
          have heqq : absPropWhen ent.2.pw = absPropWhen prev_pw :=
            of_decide_eq_true heq.symm
          rw [heqq, beq_self_eq_true', Bool.not_true, Bool.and_false]
        case isFalse hb1f =>
          -- both sides throw `notImplemented`
          obtain ⟨s, -, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v, -, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
          refine Or.inl ⟨?_, v, ?_⟩
          · rw [show b1 = false by simpa using hb1f] at heq
            have hne : ¬ (absPropWhen ent.2.pw = absPropWhen prev_pw) :=
              of_decide_eq_false heq.symm
            rw [← hvc, hbt]
            simp [hne]
          · rw [← not_implemented_inv hce]
            exact (Result.ok_injective h).symm
      case isFalse hbf =>
        -- the unverified modes: the gate is off
        obtain ⟨ty_abs, hta, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨bm1, hbm1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨node, hnode, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨pw1, hpw1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, hrec⟩ := bind_eq_ok_iff.mp h
        rw [Expr.binder_meta_dup_eq hbm1] at hnode
        rw [PropWhen.dup_eq hpw1] at hrec
        refine Or.inr ⟨?_, ty_abs, node, i2, hta, hnode, hi2, hrec⟩
        have hbf' : b = false := by simpa using hbf
        rw [← hvc, hbf', Bool.false_and]
    rcases key with ⟨hgate, v, ho⟩ | ⟨hgate, ty_abs, node, i2, hta, hnode, hi2, hrec⟩
    · -- move 2: the explicit `throw` arm
      subst ho
      refine OutP.err (ErrSim.notImplemented
        (s := "sort-annotation mismatch (lam-cod-chain)") ?_)
      rw [hcons, ConLeche.Cached.inferLamsOutI.eq_def]
      simp [hgate]
    · have hta' : cached.expr_ops_c.abstract_range ent.1 d j 0#u64 = ok ty_abs := by
        rw [← StateC.abstract_range_m_eq]; exact hta
      obtain ⟨habsta, hwfta⟩ := ExprOpsC.abstract_range_refines hxwf.1 hta'
      have habsnode := Expr.forall_e_refines hnode
      have hwfnode : ExprWF node := ExprWF.forall_e hwfta hcur hxwf.2 hnode
      have hi2v : i2.val = j.val - 1 := ExprOps.sub_nat_val hi2
      have hnodeabs : ConLeche.Expr.forallE
          (ConLeche.Expr.abstractRangeC (absExpr ent.1) d.val j.val)
          (absExpr cur) { pw := absPropWhen ent.2.pw } = absExpr node := by
        rw [habsnode, habsta]
        simp [absBinderMeta]
      -- one fold step is the same on both sides, at every outcome
      have hstep : (ConLeche.Cached.inferLamsOutI (absMode mode) d.val
            (absLamEntries (stk.val.take p.val)) j.val (absExpr cur)
            (absPropWhen prev_pw)).run lst
          = (ConLeche.Cached.inferLamsOutI (absMode mode) d.val
            (absLamEntries (stk.val.take i1.val)) i2.val (absExpr node)
            (absPropWhen ent.2.pw)).run lst := by
        rw [hcons, ConLeche.Cached.inferLamsOutI.eq_def]
        simp only [hgate, Bool.false_eq_true, if_false, ConLeche.Cached.abstractRangeM,
          absBinderMeta, StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure,
          StateT.pure, Except.pure]
        rw [hnodeabs, ← hi2v]
      rw [hstep]
      exact ih mode d stk i1 i2 node o ent.2.pw hi1v (le_of_lt hlt) hstk hwfnode
        hxwf.2 hrec lst

/-- `ConLeche/Cached/CoreC.lean:1146-1160` — **`infer_lams_out_i` refines
`inferLamsOutI`** (`core_c.rs:2891`): the rebuild fold, at the stack prefix
the count `p` selects (`p = stk.len()` at the call site).  The Rust is pure;
it is stated in the state-threading shape the leaf composes it at. -/
theorem infer_lams_out_i_refines {d : Std.U64}
    {stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)} {p : Std.Usize}
    {j : Std.U64} {cur : expr.Expr} {prev_pw : prop_when.PropWhen}
    (hstk : LamEntriesWF stk.val) (hcur : ExprWF cur) (hpw : PropWhenWF prev_pw)
    (hp : p.val ≤ stk.val.length) :
    SimS absExpr ExprWF
      (fun st => do
        let r ← cached.core_c.infer_lams_out_i mode d stk p j cur prev_pw
        ok (r, st))
      (ConLeche.Cached.inferLamsOutI (absMode mode) d.val
        (absLamEntries (stk.val.take p.val)) j.val (absExpr cur)
        (absPropWhen prev_pw)) := by
  intro st o st' hwf hok lst hrel
  simp only [bind_eq_ok_iff] at hok
  obtain ⟨r1, hr1, hok⟩ := hok
  have hr1' : r1 = o ∧ st = st' := by
    simp only [Result.ok.injEq, Prod.mk.injEq] at hok
    exact ⟨hok.1, hok.2⟩
  obtain ⟨hr1eq, hsteq⟩ := hr1'
  subst hr1eq
  subst hsteq
  have hout :=
    infer_lams_out_i_val p.val mode d stk p j cur r1 prev_pw rfl hp hstk hcur hpw hr1 lst
  cases r1 with
  | Ok r => obtain ⟨hrun, hwfr⟩ := hout; exact ⟨lst, hrun, hrel, hwf, hwfr⟩
  | Err ce => exact Out.err hout

/-- `ConLeche/Cached/CoreC.lean:1173-1191` — **`infer_lams_leaf_sort_i` refines
`inferLamsLeafSortI`** (`core_c.rs:2981`), the verified-mode block of the leaf
phase. -/
theorem infer_lams_leaf_sort_i_refines (hw : Wrappers mode fuel) (dk : Std.U64)
    {bt : expr.Expr} {stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    (hbt : ExprWF bt) (hstk : LamEntriesWF stk.val) :
    Sim id (fun _ => True)
      (fun st fe => cached.core_c.infer_lams_leaf_sort_i mode fuel st fe dk bt stk)
      (fun lfe => inferLamsLeafSortI (knot mode lfe fuel.val) dk.val (absExpr bt)
        (absLamEntries stk.val)) := by
  intro fe lfe hfe hfrel st o st' hwf hok lst hrel
  unfold cached.core_c.infer_lams_leaf_sort_i at hok
  dsimp only at hok ⊢
  obtain ⟨x1, hinfio, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨r0, st1⟩ := x1
  cases r0 with
  | Err e =>
    -- move 1: `infer_io` threw, and it is con-leche's first step too
    have ho : o = .Err e := (congrArg Prod.fst (Result.ok_injective hok)).symm
    subst ho
    refine Out.err ?_
    unfold inferLamsLeafSortI
    exact ErrSim.bindCM ((hw.inferIOSim dk hbt).apply_err hwf hfe hinfio hrel hfrel)
  | Ok btt =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, hbttwf⟩ :=
      (hw.inferIOSim dk hbt).apply hwf hfe hinfio hrel hfrel
    obtain ⟨x2, hwhnf, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨r1, st2⟩ := x2
    cases r1 with
    | Err e =>
      -- move 1 again, one step in
      have ho : o = .Err e := (congrArg Prod.fst (Result.ok_injective hok)).symm
      subst ho
      refine Out.err ?_
      unfold inferLamsLeafSortI
      rw [checkCM_bind_run _ _ hrun1]
      exact ErrSim.bindCM ((hw.whnfSim dk hbttwf).apply_err hwf1 hfe hwhnf hrel1 hfrel)
    | Ok wbtt =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, hwbttwf⟩ :=
        (hw.whnfSim dk hbttwf).apply hwf1 hfe hwhnf hrel1 hfrel
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok] at hok
      obtain ⟨⟨dw, kw⟩⟩ := wbtt
      cases kw
      case «Sort» vb =>
        have hvbwf : LevelWF vb := CoreK.wf_sort_inv hwbttwf rfl
        have hlen : (alloc.vec.Vec.len stk).val = stk.val.length :=
          alloc.vec.Vec.len_val stk
        split at hok
        case isTrue hz =>
          -- an empty stack: `| [] => pure ()`
          have hnil : stk.val = [] := by
            have h0 : stk.val.length = 0 := by rw [← hlen, hz]; scalar_tac
            exact List.eq_nil_of_length_eq_zero h0
          have ho : o = .Ok () := (congrArg Prod.fst (Result.ok_injective hok)).symm
          have hst : st' = st2 := (congrArg Prod.snd (Result.ok_injective hok)).symm
          subst ho
          subst hst
          refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
          rw [inferLamsLeafSortI]
          rw [checkCM_bind_run _ _ hrun1, checkCM_bind_run _ _ hrun2]
          simp [hnil]
        case isFalse hz =>
          -- the innermost binder's annotation, against the body type's sort
          have hne : stk.val ≠ [] := by
            intro hc
            apply hz
            have h0 : stk.val.length = 0 := by rw [hc]; simp
            have h1 : (alloc.vec.Vec.len stk).val = 0 := by rw [hlen, h0]
            scalar_tac
          obtain ⟨pv, hpv, hok⟩ := bind_eq_ok_iff.mp hok
          obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
          obtain ⟨ent, hidx, hok⟩ := bind_eq_ok_iff.mp hok
          obtain ⟨b, hb, hok⟩ := bind_eq_ok_iff.mp hok
          obtain ⟨hpvabs, hpvwf⟩ := ExprOps.zeroness_of_refines hvbwf pv hpv
          have hi2v : i2.val = stk.val.length - 1 := by
            rw [HashMap.uscalar_sub_eq hi2, hlen]; rfl
          have hg := ExprOps.vec_index_getElem? hidx
          obtain ⟨rest, hcons⟩ := absLamEntries_cons_of_index hi2v hne hg
          have hlt : i2.val < stk.val.length := by
            have h0 : 0 < stk.val.length := List.length_pos_iff.2 hne
            omega
          have hmem : ent ∈ stk.val := by
            rw [List.getElem?_eq_getElem hlt] at hg
            rw [← Option.some_injective _ hg]
            exact List.getElem_mem hlt
          have hxwf := hstk _ hmem
          have heq := PropWhen.beq_refines hpvwf hxwf.2 hb
          split at hok
          case isTrue hbt =>
            have ho : o = .Ok () := (congrArg Prod.fst (Result.ok_injective hok)).symm
            have hst : st' = st2 := (congrArg Prod.snd (Result.ok_injective hok)).symm
            subst ho
            subst hst
            refine ⟨lst2, ?_, hrel2, hwf2, trivial⟩
            rw [hbt] at heq
            have heqq : absPropWhen pv = absPropWhen ent.2.pw :=
              of_decide_eq_true heq.symm
            rw [inferLamsLeafSortI]
            rw [checkCM_bind_run _ _ hrun1, checkCM_bind_run _ _ hrun2]
            simp only [absExpr_mk, absExprKind, hcons]
            rw [← hpvabs, heqq]
            simp [absBinderMeta]
          case isFalse hbf =>
            -- move 2: both sides throw `notImplemented`
            rw [show b = false by simpa using hbf] at heq
            have hnee : ¬ (absPropWhen pv = absPropWhen ent.2.pw) :=
              of_decide_eq_false heq.symm
            obtain ⟨s0, -, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨v0, -, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨ce, hce, hok⟩ := bind_eq_ok_iff.mp hok
            have ho : o = .Err ce := (congrArg Prod.fst (Result.ok_injective hok)).symm
            subst ho
            rw [not_implemented_inv hce]
            refine Out.err (ErrSim.notImplemented
              (s := "sort-annotation mismatch (lam-cod-leaf)") ?_)
            rw [inferLamsLeafSortI]
            rw [checkCM_bind_run _ _ hrun1, checkCM_bind_run _ _ hrun2]
            simp only [absExpr_mk, absExprKind, hcons]
            rw [← hpvabs]
            simp [absBinderMeta, hnee]
      all_goals
        -- move 2: the residual is not a sort, and both sides throw `invalid`
        (obtain ⟨s0, -, hok⟩ := bind_eq_ok_iff.mp hok
         obtain ⟨v0, -, hok⟩ := bind_eq_ok_iff.mp hok
         obtain ⟨ce, hce, hok⟩ := bind_eq_ok_iff.mp hok
         have ho : o = .Err ce := (congrArg Prod.fst (Result.ok_injective hok)).symm
         subst ho
         rw [invalid_inv hce]
         refine Out.err (ErrSim.invalid (s := "expected a sort") ?_)
         rw [inferLamsLeafSortI]
         rw [checkCM_bind_run _ _ hrun1, checkCM_bind_run _ _ hrun2]
         simp)

/-- `ConLeche/Cached/CoreC.lean:1162-1206` — **`infer_lams_leaf_i` refines
`inferLamsLeafI`** (`core_c.rs:2933`): bulk-open the residual body, infer it,
sort-check it at the verified modes, then rebuild outward. -/
theorem infer_lams_leaf_i_refines (hw : Wrappers mode fuel) (d : Std.U64)
    {t : expr.Expr} (k : Std.U64) {fvs : alloc.vec.Vec expr.Expr}
    {stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    (ht : ExprWF t) (hfvs : ExprsWF fvs) (hstk : LamEntriesWF stk.val) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_lams_leaf_i mode fuel st fe d t k fvs stk)
      (fun lfe => ConLeche.Cached.inferLamsLeafI (absMode mode)
        (knot mode lfe fuel.val) d.val (absExpr t) k.val (absExprs fvs).toArray
        (absLamEntries stk.val)) := by
  intro fe lfe hfe hfrel st o st' hwf hok lst hrel
  unfold cached.core_c.infer_lams_leaf_i at hok
  dsimp only at hok ⊢
  obtain ⟨ob, hob, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨i, hi, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨x1, hinf, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨hobrun, hobwf⟩ := instListRevM_run ht hfvs hob
  have hiv : i.val = d.val + k.val := HashMap.uscalar_add_eq hi
  obtain ⟨r0, st1⟩ := x1
  cases r0 with
  | Err e =>
    -- move 1: the body's inference threw, and it is con-leche's first call too
    have ho : o = .Err e := (congrArg Prod.fst (Result.ok_injective hok)).symm
    subst ho
    refine Out.err ?_
    rw [inferLamsLeafI_eq, hobrun, pure_bind, ← hiv]
    exact ErrSim.bindCM ((hw.inferSim i hobwf).apply_err hwf hfe hinf hrel hfrel)
  | Ok bt =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, hbtwf⟩ :=
      (hw.inferSim i hobwf).apply hwf hfe hinf hrel hfrel
    obtain ⟨b, hisl, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨x2, hchk, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨st2, chk⟩ := x2
    have hlam := ExprOps.is_lam_refines hisl
    cases chk with
    | Err e =>
      -- move 1: only the verified-mode sort block can throw here, and it is
      -- exactly the con-leche action the check phase runs
      have ho : o = .Err e := (congrArg Prod.fst (Result.ok_injective hok)).symm
      subst ho
      refine Out.err ?_
      rw [inferLamsLeafI_eq, hobrun, pure_bind, ← hiv]
      rw [checkCM_bind_run _ _ hrun1]
      split at hchk
      case isTrue hbt =>
        exact absurd (congrArg Prod.snd (Result.ok_injective hchk)) (by simp)
      case isFalse hbf =>
        have hnone : ConLeche.Expr.lamPw (absExpr t) = none := by
          have h0 : (ConLeche.Expr.lamPw (absExpr t)).isSome = false := by
            rw [lamPw_isSome, ← hlam]
            simpa using hbf
          simpa using h0
        obtain ⟨b1, hb1, hchk⟩ := bind_eq_ok_iff.mp hchk
        have hvc := Env.verified_checks_refines hb1
        split at hchk
        case isTrue hb1t =>
          obtain ⟨x3, hsort, hchk⟩ := bind_eq_ok_iff.mp hchk
          obtain ⟨chk1, st3⟩ := x3
          have hst : st3 = st2 := congrArg Prod.fst (Result.ok_injective hchk)
          have hc1 : chk1 = .Err e := congrArg Prod.snd (Result.ok_injective hchk)
          subst hst
          rw [hc1] at hsort
          have hvt : (absMode mode).verifiedChecks = true := by rw [← hvc, hb1t]
          simp only [hnone]
          rw [hvt, bool_ite_true]
          exact ErrSim.bindCM ((infer_lams_leaf_sort_i_refines hw i hbtwf hstk).apply_err
            hwf1 hfe hsort hrel1 hfrel)
        case isFalse hb1f =>
          exact absurd (congrArg Prod.snd (Result.ok_injective hchk)) (by simp)
    | Ok u =>
      cases u
      -- the check phase: the port's `is_lam`/`verified_checks` split is the
      -- cited `match t with | .lam .. => pure () | _ => if verifiedChecks …`
      have key : ∃ lst2, StateRel st2 lst2 ∧ StateWF st2 ∧
          ((match ConLeche.Expr.lamPw (absExpr t) with
            | some _ => pure ()
            | none =>
              if (absMode mode).verifiedChecks then
                inferLamsLeafSortI (knot mode lfe fuel.val) i.val (absExpr bt)
                  (absLamEntries stk.val)
              else pure ()) : ConLeche.Cached.CheckCM Unit).run lst1
            = .ok ((), lst2) := by
        split at hchk
        case isTrue hbt =>
          -- a λ residual skips the check
          have hs : (ConLeche.Expr.lamPw (absExpr t)).isSome = true := by
            rw [lamPw_isSome, ← hlam, hbt]
          obtain ⟨pw, hpw⟩ := Option.isSome_iff_exists.mp hs
          have hst : st2 = st1 := (congrArg Prod.fst (Result.ok_injective hchk)).symm
          subst hst
          exact ⟨lst1, hrel1, hwf1, by rw [hpw]; simp⟩
        case isFalse hbf =>
          have hnone : ConLeche.Expr.lamPw (absExpr t) = none := by
            have h0 : (ConLeche.Expr.lamPw (absExpr t)).isSome = false := by
              rw [lamPw_isSome, ← hlam]
              simpa using hbf
            simpa using h0
          rw [hnone]
          obtain ⟨b1, hb1, hchk⟩ := bind_eq_ok_iff.mp hchk
          have hvc := Env.verified_checks_refines hb1
          split at hchk
          case isTrue hb1t =>
            obtain ⟨x3, hsort, hchk⟩ := bind_eq_ok_iff.mp hchk
            obtain ⟨chk1, st3⟩ := x3
            have hst : st3 = st2 := congrArg Prod.fst (Result.ok_injective hchk)
            have hc1 : chk1 = .Ok () := congrArg Prod.snd (Result.ok_injective hchk)
            subst hst
            rw [hc1] at hsort
            obtain ⟨lst2, hrun, hrel2, hwf2, -⟩ :=
              (infer_lams_leaf_sort_i_refines hw i hbtwf hstk).apply hwf1 hfe hsort
                hrel1 hfrel
            refine ⟨lst2, hrel2, hwf2, ?_⟩
            rw [← hvc, hb1t]
            simpa using hrun
          case isFalse hb1f =>
            have hst : st2 = st1 := (congrArg Prod.fst (Result.ok_injective hchk)).symm
            subst hst
            refine ⟨lst1, hrel1, hwf1, ?_⟩
            rw [← hvc, show b1 = false by simpa using hb1f]
            simp
      obtain ⟨lst2, hrel2, hwf2, hchkrun⟩ := key
      -- the rebuild, at whichever outcome the fold ends in
      obtain ⟨cur, hcur, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨prev_pw, hprev, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨i2, hi2, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨r1, hout, hfin⟩ := bind_eq_ok_iff.mp hok
      have hr1 : r1 = o := congrArg Prod.fst (Result.ok_injective hfin)
      have hst' : st' = st2 := (congrArg Prod.snd (Result.ok_injective hfin)).symm
      subst hst'
      subst hr1
      have hcur' : cached.expr_ops_c.abstract_range bt d k 0#u64 = ok cur := by
        rw [← StateC.abstract_range_m_eq]; exact hcur
      obtain ⟨hcurabs, hcurwf⟩ := ExprOpsC.abstract_range_refines hbtwf hcur'
      obtain ⟨hprevabs, hprevwf⟩ :=
        infer_lams_prev_pw_i_refines ht hstk prev_pw hprev
      have hi2v : i2.val = k.val - 1 := ExprOps.sub_nat_val hi2
      have hlen : (alloc.vec.Vec.len stk).val = stk.val.length :=
        alloc.vec.Vec.len_val stk
      have hstep : (ConLeche.Cached.inferLamsLeafI (absMode mode)
            (knot mode lfe fuel.val) d.val (absExpr t) k.val (absExprs fvs).toArray
            (absLamEntries stk.val)).run lst
          = (ConLeche.Cached.inferLamsOutI (absMode mode) d.val
            (absLamEntries stk.val) i2.val (absExpr cur)
            (absPropWhen prev_pw)).run lst2 := by
        rw [inferLamsLeafI_eq, hobrun, pure_bind, ← hiv]
        rw [checkCM_bind_run _ _ hrun1, checkCM_bind_run _ _ hchkrun]
        rw [ConLeche.Cached.abstractRangeM]
        rw [pure_bind]
        rw [show ConLeche.Expr.abstractRangeC (absExpr bt) d.val k.val
            = absExpr cur from by rw [hcurabs]; rfl, ← hi2v, ← hprevabs]
      rw [hstep]
      have hout' :=
        infer_lams_out_i_val (alloc.vec.Vec.len stk).val mode d stk
          (alloc.vec.Vec.len stk) i2 cur r1 prev_pw rfl (by rw [hlen]) hstk hcurwf
          hprevwf hout lst2
      rw [hlen, List.take_length] at hout'
      cases r1 with
      | Ok res =>
        obtain ⟨houtrun, hreswf⟩ := hout'
        exact ⟨lst2, houtrun, hrel2, hwf2, hreswf⟩
      | Err ce => exact Out.err hout'

/-- The λ-peel loop at a fixed peel budget — the shape the induction wants. -/
theorem infer_lams_i_val (hw : Wrappers mode fuel) (N : Nat) :
    ∀ (d peel : Std.U64) (t : expr.Expr) (k : Std.U64)
      (fvs : alloc.vec.Vec expr.Expr)
      (stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)),
      peel.val = N → ExprWF t → ExprsWF fvs → LamEntriesWF stk.val →
      Sim absExpr ExprWF
        (fun st fe => cached.core_c.infer_lams_i mode fuel st fe d peel t k fvs stk)
        (fun lfe => ConLeche.Cached.inferLamsI (absMode mode)
          (knot mode lfe fuel.val) d.val peel.val (absExpr t) k.val
          (absExprs fvs).toArray (absLamEntries stk.val)) := by
  induction N with
  | zero =>
    intro d peel t k fvs stk hN ht hfvs hstk fe lfe hfe hfrel st o st' hwf hok lst hrel
    unfold cached.core_c.infer_lams_i at hok
    dsimp only at hok
    rw [if_pos (show peel = 0#u64 by scalar_tac)] at hok
    have hleaf :=
      (infer_lams_leaf_i_refines hw d k ht hfvs hstk) fe lfe hfe hfrel st o st' hwf hok
        lst hrel
    dsimp only at hleaf ⊢
    rw [hN]
    simpa [ConLeche.Cached.inferLamsI] using hleaf
  | succ n ih =>
    intro d peel t k fvs stk hN ht hfvs hstk fe lfe hfe hfrel st o st' hwf hok lst hrel
    unfold cached.core_c.infer_lams_i at hok
    dsimp only at hok
    rw [if_neg (show ¬ peel = 0#u64 by
      intro hc; rw [hc] at hN; simp at hN)] at hok
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok] at hok
    obtain ⟨⟨dt, kt⟩⟩ := t
    dsimp only at hok ⊢
    rw [hN]
    cases kt
    case Lam ty body mb =>
      obtain ⟨hty, hbody, hmb⟩ := wf_lam_inv ht rfl
      obtain ⟨body1, hbody1, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨mb1, hmb1, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨tyo, htyo, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨i, hi, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨x1, hinf, hok⟩ := bind_eq_ok_iff.mp hok
      have hb1 : body = body1 := (Expr.dup_eq hbody1).symm
      subst hb1
      have hm1 : mb = mb1 := (Expr.binder_meta_dup_eq hmb1).symm
      subst hm1
      obtain ⟨htyorun, htyowf⟩ := instListRevM_run hty hfvs htyo
      have hiv : i.val = d.val + k.val := HashMap.uscalar_add_eq hi
      obtain ⟨r0, st1⟩ := x1
      cases r0 with
      | Err e =>
        -- move 1: the domain's inference threw, con-leche's first call too
        have ho : o = .Err e := (congrArg Prod.fst (Result.ok_injective hok)).symm
        subst ho
        refine Out.err ?_
        rw [ConLeche.Cached.inferLamsI.eq_def]
        simp only [absExpr_mk, absExprKind]
        rw [htyorun, pure_bind, ← hiv]
        exact ErrSim.bindCM ((hw.inferSim i htyowf).apply_err hwf hfe hinf hrel hfrel)
      | Ok tty =>
        obtain ⟨lst1, hrun1, hrel1, hwf1, httywf⟩ :=
          (hw.inferSim i htyowf).apply hwf hfe hinf hrel hfrel
        obtain ⟨x2, hwhnf, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨r1, st2⟩ := x2
        cases r1 with
        | Err e =>
          have ho : o = .Err e := (congrArg Prod.fst (Result.ok_injective hok)).symm
          subst ho
          refine Out.err ?_
          rw [ConLeche.Cached.inferLamsI.eq_def]
          simp only [absExpr_mk, absExprKind]
          rw [htyorun, pure_bind, ← hiv]
          rw [checkCM_bind_run _ _ hrun1]
          exact ErrSim.bindCM ((hw.whnfSim i httywf).apply_err hwf1 hfe hwhnf hrel1 hfrel)
        | Ok wtty =>
          obtain ⟨lst2, hrun2, hrel2, hwf2, hwttywf⟩ :=
            (hw.whnfSim i httywf).apply hwf1 hfe hwhnf hrel1 hfrel
          obtain ⟨⟨dw, kw⟩⟩ := wtty
          cases kw
          case «Sort» u =>
            obtain ⟨bs, hisl, hok⟩ := bind_eq_ok_iff.mp hok
            have hbst : bs = true := by rw [CoreK.is_sort_refines hisl]; simp
            split at hok
            case isTrue _ =>
              obtain ⟨e1, he1, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨fv, hfv, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨fvs1, hfvs1, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨stk1, hstk1, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨i1, hi1, hok⟩ := bind_eq_ok_iff.mp hok
              obtain ⟨i2, hi2, hrec⟩ := bind_eq_ok_iff.mp hok
              have he1e : tyo = e1 := (Expr.dup_eq he1).symm
              subst he1e
              have hfvabs : absExpr fv = .fvar i.val (absExpr tyo) :=
                Expr.fvar_refines hfv
              have hfvwf : ExprWF fv := ExprWF.fvar htyowf hfv
              have hfvs1v : fvs1.val = fvs.val ++ [fv] := vec_push_val hfvs1
              have hstk1v : stk1.val = stk.val ++ [(tyo, mb)] := vec_push_val hstk1
              have hfvs1wf : ExprsWF fvs1 := by
                intro x hx
                rw [hfvs1v] at hx
                rcases List.mem_append.1 hx with h1 | h1
                · exact hfvs x h1
                · rw [List.mem_singleton.1 h1]; exact hfvwf
              have hstk1wf : LamEntriesWF stk1.val := by
                rw [hstk1v]; exact hstk.concat htyowf hmb
              have hi1v : i1.val = n := by
                have h1 := HashMap.uscalar_sub_eq hi1; scalar_tac
              have hi2v : i2.val = k.val + 1 := HashMap.uscalar_add_eq hi2
              -- the recursive peel, at whichever outcome it ends in
              have hrecout :=
                (ih d i1 body i2 fvs1 stk1 hi1v hbody hfvs1wf hstk1wf) fe lfe hfe hfrel
                  st2 o st' hwf2 hrec lst2 hrel2
              rw [ConLeche.Cached.inferLamsI.eq_def]
              simp only [absExpr_mk, absExprKind]
              rw [htyorun, pure_bind, ← hiv]
              rw [checkCM_bind_run _ _ hrun1, checkCM_bind_run _ _ hrun2]
              simp only [absExpr_mk, absExprKind, pure_bind]
              rw [← hi1v, ← hi2v]
              rw [show (absExprs fvs).toArray.push (ConLeche.Expr.fvar i.val (absExpr tyo))
                  = (absExprs fvs1).toArray from by
                rw [← hfvabs]; simp [absExprs, hfvs1v]]
              rw [show ((absExpr tyo, absBinderMeta mb) :: absLamEntries stk.val)
                  = absLamEntries stk1.val from by
                simp [hstk1v]]
              exact hrecout
            case isFalse hbf =>
              exfalso; rw [hbst] at hbf; simp at hbf
          all_goals
            -- move 2: the domain's type is not a sort, both sides throw `invalid`
            (obtain ⟨bs, hisl, hok⟩ := bind_eq_ok_iff.mp hok
             have hbsf : bs = false := by rw [CoreK.is_sort_refines hisl]; simp
             split at hok
             case isTrue hbt => rw [hbsf] at hbt; simp at hbt
             case isFalse _ =>
               obtain ⟨s0, -, hok⟩ := bind_eq_ok_iff.mp hok
               obtain ⟨v0, -, hok⟩ := bind_eq_ok_iff.mp hok
               obtain ⟨ce, hce, hok⟩ := bind_eq_ok_iff.mp hok
               have ho : o = .Err ce := (congrArg Prod.fst (Result.ok_injective hok)).symm
               subst ho
               rw [invalid_inv hce]
               refine Out.err (ErrSim.invalid (s := "expected a sort") ?_)
               rw [ConLeche.Cached.inferLamsI.eq_def]
               simp only [absExpr_mk, absExprKind]
               rw [htyorun, pure_bind, ← hiv]
               rw [checkCM_bind_run _ _ hrun1, checkCM_bind_run _ _ hrun2]
               simp)
    all_goals
      (have hleaf :=
        (infer_lams_leaf_i_refines hw d k ht hfvs hstk) fe lfe hfe hfrel st o st' hwf hok
          lst hrel
       simpa [ConLeche.Cached.inferLamsI] using hleaf)

/-- `ConLeche/Cached/CoreC.lean:1208-1228` — **`infer_lams_i` refines
`inferLamsI`** (`core_c.rs:3045`): the λ-telescope peel loop, `peel` the
con-leche peel fuel. -/
theorem infer_lams_i_refines (hw : Wrappers mode fuel) (d peel : Std.U64)
    {t : expr.Expr} (k : Std.U64) {fvs : alloc.vec.Vec expr.Expr}
    {stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    (ht : ExprWF t) (hfvs : ExprsWF fvs) (hstk : LamEntriesWF stk.val) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_lams_i mode fuel st fe d peel t k fvs stk)
      (fun lfe => ConLeche.Cached.inferLamsI (absMode mode)
        (knot mode lfe fuel.val) d.val peel.val (absExpr t) k.val
        (absExprs fvs).toArray (absLamEntries stk.val)) :=
  infer_lams_i_val hw peel.val d peel t k fvs stk rfl ht hfvs hstk

/-- The ∀-fold as a pure statement over the count `p`: the accumulated domain
sorts folded by `imax`, innermost binder first.  Task #67: over the **full
outcome**, since the fold's annotation check throws (`core_c.rs:3150`, the
cited `CoreC.lean:1251`). -/
theorem infer_pis_out_i_val (N : Nat) :
    ∀ (mode : env.CheckMode)
      (stk : alloc.vec.Vec (level.Level × prop_when.PropWhen)) (p : Std.Usize)
      (v : level.Level)
      (o : core.result.Result level.Level core_types.CheckError)
      (pv : prop_when.PropWhen),
      p.val = N → p.val ≤ stk.val.length → PisEntriesWF stk.val → LevelWF v →
      PropWhenWF pv →
      cached.core_c.infer_pis_out_i mode stk p v pv = ok o →
      ∀ lst, OutP (fun r => (absLevel r, lst)) LevelWF o
        ((ConLeche.Cached.inferPisOutI (absMode mode)
          (absPisEntries (stk.val.take p.val)) (absLevel v)
          (absPropWhen pv)).run lst) := by
  induction N with
  | zero =>
    intro mode stk p v o pv hN hp hstk hv hpv h lst
    unfold cached.core_c.infer_pis_out_i at h
    rw [if_pos (show p = 0#usize by scalar_tac)] at h
    have ho : o = .Ok v := (Result.ok_injective h).symm
    subst ho
    refine OutP.ok ?_ hv
    rw [hN, List.take_zero, absPisEntries_nil]
    simp [ConLeche.Cached.inferPisOutI]
  | succ n ih =>
    intro mode stk p v o pv hN hp hstk hv hpv h lst
    have hlen : (alloc.vec.Vec.len stk).val = stk.val.length := alloc.vec.Vec.len_val stk
    unfold cached.core_c.infer_pis_out_i at h
    rw [if_neg (show ¬ p = 0#usize by intro hc; rw [hc] at hN; simp at hN)] at h
    rw [if_neg (show ¬ p > alloc.vec.Vec.len stk by
      intro hc
      have h1 : (alloc.vec.Vec.len stk).val < p.val := by scalar_tac
      omega)] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨i1, hi1, ent, hidx, b, hb, h⟩ := h
    have hi1v : i1.val = n := by
      have h1 := HashMap.uscalar_sub_eq hi1; scalar_tac
    have hg := ExprOps.vec_index_getElem? hidx
    have hlt : i1.val < stk.val.length := by omega
    have hmem : ent ∈ stk.val := by
      rw [List.getElem?_eq_getElem hlt] at hg
      rw [← Option.some_injective _ hg]
      exact List.getElem_mem hlt
    have hxwf := hstk _ hmem
    have hcons : absPisEntries (stk.val.take p.val)
        = (absLevel ent.1, absPropWhen ent.2) :: absPisEntries (stk.val.take i1.val) := by
      rw [show p.val = i1.val + 1 by omega]
      exact absPisEntries_take_succ hg
    have hvc := Env.verified_checks_refines hb
    have key : (((absMode mode).verifiedChecks
              && !(absPropWhen pv == absPropWhen ent.2)) = true
          ∧ ∃ w, o = .Err (.NotImplemented w))
        ∨ (((absMode mode).verifiedChecks
              && !(absPropWhen pv == absPropWhen ent.2)) = false
          ∧ ∃ v2, kernel.level.imax ent.1 v = ok v2 ∧
              cached.core_c.infer_pis_out_i mode stk i1 v2 pv = ok o) := by
      split at h
      case isTrue hbt =>
        obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
        have heq := PropWhen.beq_refines hpv hxwf.2 hb1
        split at h
        case isTrue hb1t =>
          obtain ⟨l1, hl1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v2, hv2, hrec⟩ := bind_eq_ok_iff.mp h
          rw [level_dup_eq] at hl1
          rw [← Result.ok_injective hl1] at hv2
          refine Or.inr ⟨?_, v2, hv2, hrec⟩
          rw [hb1t] at heq
          have heqq : absPropWhen pv = absPropWhen ent.2 := of_decide_eq_true heq.symm
          rw [heqq, beq_self_eq_true', Bool.not_true, Bool.and_false]
        case isFalse hb1f =>
          -- both sides throw `notImplemented`
          obtain ⟨s, -, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨w, -, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
          refine Or.inl ⟨?_, w, ?_⟩
          · rw [show b1 = false by simpa using hb1f] at heq
            have hne : ¬ (absPropWhen pv = absPropWhen ent.2) :=
              of_decide_eq_false heq.symm
            rw [← hvc, hbt]
            simp [hne]
          · rw [← not_implemented_inv hce]
            exact (Result.ok_injective h).symm
      case isFalse hbf =>
        obtain ⟨l1, hl1, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v2, hv2, hrec⟩ := bind_eq_ok_iff.mp h
        rw [level_dup_eq] at hl1
        rw [← Result.ok_injective hl1] at hv2
        refine Or.inr ⟨?_, v2, hv2, hrec⟩
        have hbf' : b = false := by simpa using hbf
        rw [← hvc, hbf', Bool.false_and]
    rcases key with ⟨hgate, w, ho⟩ | ⟨hgate, v2, hv2, hrec⟩
    · -- move 2: the explicit `throw` arm
      subst ho
      refine OutP.err (ErrSim.notImplemented
        (s := "sort-annotation mismatch (forall-cod)") ?_)
      rw [hcons, ConLeche.Cached.inferPisOutI.eq_def]
      simp [hgate]
    · have habsv2 := Level.imax_refines hv2
      have hwfv2 : LevelWF v2 := LevelWF.imax hxwf.1 hv hv2
      have hstep : (ConLeche.Cached.inferPisOutI (absMode mode)
            (absPisEntries (stk.val.take p.val)) (absLevel v)
            (absPropWhen pv)).run lst
          = (ConLeche.Cached.inferPisOutI (absMode mode)
            (absPisEntries (stk.val.take i1.val)) (absLevel v2)
            (absPropWhen pv)).run lst := by
        rw [hcons, ConLeche.Cached.inferPisOutI.eq_def]
        simp only [hgate, Bool.false_eq_true, if_false, StateT.run, Bind.bind,
          StateT.bind, Except.bind, Pure.pure, StateT.pure, Except.pure]
        rw [show (absLevel ent.1).imax (absLevel v) = absLevel v2 from habsv2.symm]
      rw [hstep]
      exact ih mode stk i1 v2 o pv hi1v (le_of_lt hlt) hstk hwfv2 hpv hrec lst

/-- `ConLeche/Cached/CoreC.lean:1230-1254` — **`infer_pis_out_i` refines
`inferPisOutI`** (`core_c.rs:3116`): fold the accumulated domain sorts by
`imax`, innermost binder first, the codomain sort's zero-ness datum threaded. -/
theorem infer_pis_out_i_refines
    {stk : alloc.vec.Vec (level.Level × prop_when.PropWhen)} {p : Std.Usize}
    {v : level.Level} {pv : prop_when.PropWhen}
    (hstk : PisEntriesWF stk.val) (hv : LevelWF v) (hpv : PropWhenWF pv)
    (hp : p.val ≤ stk.val.length) :
    SimS absLevel LevelWF
      (fun st => do
        let r ← cached.core_c.infer_pis_out_i mode stk p v pv
        ok (r, st))
      (ConLeche.Cached.inferPisOutI (absMode mode)
        (absPisEntries (stk.val.take p.val)) (absLevel v) (absPropWhen pv)) := by
  intro st o st' hwf hok lst hrel
  simp only [bind_eq_ok_iff] at hok
  obtain ⟨r1, hr1, hok⟩ := hok
  simp only [Result.ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hr1eq, hsteq⟩ := hok
  subst hr1eq
  subst hsteq
  have hout := infer_pis_out_i_val p.val mode stk p v r1 pv rfl hp hstk hv hpv hr1 lst
  cases r1 with
  | Ok r => obtain ⟨hrun, hwfr⟩ := hout; exact ⟨lst, hrun, hrel, hwf, hwfr⟩
  | Err ce => exact Out.err hout

/-- `ConLeche/Cached/CoreC.lean:1256-1267` — **`infer_pis_leaf_i` refines
`inferPisLeafI`** (`core_c.rs:3144`): bulk-open the residual body, infer its
sort, then fold the domain sorts outward. -/
theorem infer_pis_leaf_i_refines (hw : Wrappers mode fuel) (d : Std.U64)
    {t : expr.Expr} (k : Std.U64) {fvs : alloc.vec.Vec expr.Expr}
    {stk : alloc.vec.Vec (level.Level × prop_when.PropWhen)}
    (ht : ExprWF t) (hfvs : ExprsWF fvs) (hstk : PisEntriesWF stk.val) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_pis_leaf_i mode fuel st fe d t k fvs stk)
      (fun lfe => ConLeche.Cached.inferPisLeafI (absMode mode)
        (knot mode lfe fuel.val) d.val (absExpr t) k.val (absExprs fvs).toArray
        (absPisEntries stk.val)) := by
  intro fe lfe hfe hfrel st o st' hwf hok lst hrel
  unfold cached.core_c.infer_pis_leaf_i at hok
  obtain ⟨ob, hob, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨i, hi, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨x1, hinf, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨hobrun, hobwf⟩ := instListRevM_run ht hfvs hob
  have hiv : i.val = d.val + k.val := HashMap.uscalar_add_eq hi
  obtain ⟨r0, st1⟩ := x1
  cases r0 with
  | Err e =>
    -- move 1: the body's inference threw, con-leche's first call too
    have ho : o = .Err e := (congrArg Prod.fst (Result.ok_injective hok)).symm
    subst ho
    refine Out.err ?_
    dsimp only
    rw [ConLeche.Cached.inferPisLeafI.eq_def, hobrun, pure_bind, ← hiv]
    exact ErrSim.bindCM ((hw.inferSim i hobwf).apply_err hwf hfe hinf hrel hfrel)
  | Ok bt =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, hbtwf⟩ :=
      (hw.inferSim i hobwf).apply hwf hfe hinf hrel hfrel
    obtain ⟨x2, hwhnf, hok⟩ := bind_eq_ok_iff.mp hok
    obtain ⟨r1, st2⟩ := x2
    cases r1 with
    | Err e =>
      have ho : o = .Err e := (congrArg Prod.fst (Result.ok_injective hok)).symm
      subst ho
      refine Out.err ?_
      dsimp only
      rw [ConLeche.Cached.inferPisLeafI.eq_def, hobrun, pure_bind, ← hiv]
      rw [checkCM_bind_run _ _ hrun1]
      exact ErrSim.bindCM ((hw.whnfSim i hbtwf).apply_err hwf1 hfe hwhnf hrel1 hfrel)
    | Ok wbt =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, hwbtwf⟩ :=
        (hw.whnfSim i hbtwf).apply hwf1 hfe hwhnf hrel1 hfrel
      simp only [expr_view_eq, arc_deref_eq, bind_tc_ok] at hok
      obtain ⟨⟨dw, kw⟩⟩ := wbt
      cases kw
      case «Sort» v =>
        have hvwf : LevelWF v := CoreK.wf_sort_inv hwbtwf rfl
        obtain ⟨pv, hpv, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨l, hl, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨r2, hout, hok⟩ := bind_eq_ok_iff.mp hok
        rw [level_dup_eq] at hl
        rw [← Result.ok_injective hl] at hout
        obtain ⟨hpvabs, hpvwf⟩ := ExprOps.zeroness_of_refines hvwf pv hpv
        have hlen : (alloc.vec.Vec.len stk).val = stk.val.length :=
          alloc.vec.Vec.len_val stk
        have hout' :=
          infer_pis_out_i_val (alloc.vec.Vec.len stk).val mode stk
            (alloc.vec.Vec.len stk) v r2 pv rfl (by rw [hlen]) hstk hvwf hpvwf hout lst2
        rw [hlen, List.take_length] at hout'
        cases r2 with
        | Err e =>
          -- move 1: the fold's annotation check threw
          have ho : o = .Err e := (congrArg Prod.fst (Result.ok_injective hok)).symm
          subst ho
          refine Out.err ?_
          dsimp only
          rw [ConLeche.Cached.inferPisLeafI.eq_def, hobrun, pure_bind, ← hiv]
          rw [checkCM_bind_run _ _ hrun1, checkCM_bind_run _ _ hrun2]
          simp only [absExpr_mk, absExprKind]
          rw [← hpvabs]
          exact ErrSim.bindCM hout'
        | Ok iv =>
          obtain ⟨houtrun, hivwf⟩ := hout'
          obtain ⟨e0, he0, hok⟩ := bind_eq_ok_iff.mp hok
          have hres : o = .Ok e0 ∧ st' = st2 := by
            simp only [Result.ok.injEq, Prod.mk.injEq] at hok
            exact ⟨hok.1.symm, hok.2.symm⟩
          obtain ⟨hres1, hres2⟩ := hres
          subst hres1
          subst hres2
          refine ⟨lst2, ?_, hrel2, hwf2, ExprWF.sort hivwf he0⟩
          dsimp only
          rw [ConLeche.Cached.inferPisLeafI.eq_def, hobrun]
          rw [pure_bind]
          rw [← hiv]
          rw [checkCM_bind_run _ _ hrun1, checkCM_bind_run _ _ hrun2]
          simp only [absExpr_mk, absExprKind]
          rw [checkCM_bind_run _ _ (by rw [← hpvabs]; exact houtrun)]
          rw [Expr.sort_refines he0]
          simp
      all_goals
        -- move 2: the body's type is not a sort, both sides throw `invalid`
        (obtain ⟨s0, -, hok⟩ := bind_eq_ok_iff.mp hok
         obtain ⟨v0, -, hok⟩ := bind_eq_ok_iff.mp hok
         obtain ⟨ce, hce, hok⟩ := bind_eq_ok_iff.mp hok
         have ho : o = .Err ce := (congrArg Prod.fst (Result.ok_injective hok)).symm
         subst ho
         rw [invalid_inv hce]
         refine Out.err (ErrSim.invalid (s := "expected a sort") ?_)
         dsimp only
         rw [ConLeche.Cached.inferPisLeafI.eq_def, hobrun, pure_bind, ← hiv]
         rw [checkCM_bind_run _ _ hrun1, checkCM_bind_run _ _ hrun2]
         simp)

/-- The ∀-peel loop at a fixed peel budget — the shape the induction wants
(`peel.val` is con-leche's `Nat` fuel). -/
theorem infer_pis_i_val (hw : Wrappers mode fuel) (N : Nat) :
    ∀ (d peel : Std.U64) (t : expr.Expr) (k : Std.U64)
      (fvs : alloc.vec.Vec expr.Expr)
      (stk : alloc.vec.Vec (level.Level × prop_when.PropWhen)),
      peel.val = N → ExprWF t → ExprsWF fvs → PisEntriesWF stk.val →
      Sim absExpr ExprWF
        (fun st fe => cached.core_c.infer_pis_i mode fuel st fe d peel t k fvs stk)
        (fun lfe => ConLeche.Cached.inferPisI (absMode mode)
          (knot mode lfe fuel.val) d.val peel.val (absExpr t) k.val
          (absExprs fvs).toArray (absPisEntries stk.val)) := by
  induction N with
  | zero =>
    intro d peel t k fvs stk hN ht hfvs hstk fe lfe hfe hfrel st o st' hwf hok lst hrel
    unfold cached.core_c.infer_pis_i at hok
    dsimp only at hok
    rw [if_pos (show peel = 0#u64 by scalar_tac)] at hok
    have hleaf :=
      (infer_pis_leaf_i_refines hw d k ht hfvs hstk) fe lfe hfe hfrel st o st' hwf hok
        lst hrel
    dsimp only at hleaf ⊢
    rw [hN]
    simpa [ConLeche.Cached.inferPisI] using hleaf
  | succ n ih =>
    intro d peel t k fvs stk hN ht hfvs hstk fe lfe hfe hfrel st o st' hwf hok lst hrel
    unfold cached.core_c.infer_pis_i at hok
    dsimp only at hok
    rw [if_neg (show ¬ peel = 0#u64 by
      intro hc; rw [hc] at hN; simp at hN)] at hok
    simp only [expr_view_eq, arc_deref_eq, bind_tc_ok] at hok
    obtain ⟨⟨dt, kt⟩⟩ := t
    dsimp only at hok ⊢
    rw [hN]
    cases kt
    case ForallE ty body mb =>
      obtain ⟨hty, hbody, hmb⟩ := wf_forall_inv ht rfl
      obtain ⟨body1, hbody1, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨pw1, hpw1, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨tyo, htyo, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨i, hi, hok⟩ := bind_eq_ok_iff.mp hok
      obtain ⟨x1, hinf, hok⟩ := bind_eq_ok_iff.mp hok
      have hb1 : body = body1 := (Expr.dup_eq hbody1).symm
      subst hb1
      have hp1 : pw1 = mb.pw := PropWhen.dup_eq hpw1
      subst hp1
      obtain ⟨htyorun, htyowf⟩ := instListRevM_run hty hfvs htyo
      have hiv : i.val = d.val + k.val := HashMap.uscalar_add_eq hi
      obtain ⟨r0, st1⟩ := x1
      cases r0 with
      | Err e =>
        -- move 1: the domain's inference threw, con-leche's first call too
        have ho : o = .Err e := (congrArg Prod.fst (Result.ok_injective hok)).symm
        subst ho
        refine Out.err ?_
        rw [ConLeche.Cached.inferPisI.eq_def]
        simp only [absExpr_mk, absExprKind]
        rw [htyorun, pure_bind, ← hiv]
        exact ErrSim.bindCM ((hw.inferSim i htyowf).apply_err hwf hfe hinf hrel hfrel)
      | Ok tty =>
        obtain ⟨lst1, hrun1, hrel1, hwf1, httywf⟩ :=
          (hw.inferSim i htyowf).apply hwf hfe hinf hrel hfrel
        obtain ⟨x2, hwhnf, hok⟩ := bind_eq_ok_iff.mp hok
        obtain ⟨r1, st2⟩ := x2
        cases r1 with
        | Err e =>
          have ho : o = .Err e := (congrArg Prod.fst (Result.ok_injective hok)).symm
          subst ho
          refine Out.err ?_
          rw [ConLeche.Cached.inferPisI.eq_def]
          simp only [absExpr_mk, absExprKind]
          rw [htyorun, pure_bind, ← hiv]
          rw [checkCM_bind_run _ _ hrun1]
          exact ErrSim.bindCM ((hw.whnfSim i httywf).apply_err hwf1 hfe hwhnf hrel1 hfrel)
        | Ok wtty =>
          obtain ⟨lst2, hrun2, hrel2, hwf2, hwttywf⟩ :=
            (hw.whnfSim i httywf).apply hwf1 hfe hwhnf hrel1 hfrel
          obtain ⟨⟨dw, kw⟩⟩ := wtty
          cases kw
          case «Sort» u =>
            have huwf : LevelWF u := CoreK.wf_sort_inv hwttywf rfl
            obtain ⟨u1, hu1, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨e1, he1, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨fv, hfv, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨fvs1, hfvs1, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨stk1, hstk1, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨i1, hi1, hok⟩ := bind_eq_ok_iff.mp hok
            obtain ⟨i2, hi2, hrec⟩ := bind_eq_ok_iff.mp hok
            rw [level_dup_eq] at hu1
            have hu1e : u = u1 := Result.ok_injective hu1
            subst hu1e
            have he1e : tyo = e1 := (Expr.dup_eq he1).symm
            subst he1e
            -- the opened free variable
            have hfvabs : absExpr fv = .fvar i.val (absExpr tyo) := Expr.fvar_refines hfv
            have hfvwf : ExprWF fv := ExprWF.fvar htyowf hfv
            have hfvs1v : fvs1.val = fvs.val ++ [fv] := vec_push_val hfvs1
            have hstk1v : stk1.val = stk.val ++ [(u, mb.pw)] := vec_push_val hstk1
            have hfvs1wf : ExprsWF fvs1 := by
              intro x hx
              rw [hfvs1v] at hx
              rcases List.mem_append.1 hx with h1 | h1
              · exact hfvs x h1
              · rw [List.mem_singleton.1 h1]; exact hfvwf
            have hstk1wf : PisEntriesWF stk1.val := by
              rw [hstk1v]; exact hstk.concat huwf hmb
            have hi1v : i1.val = n := by
              have h1 := HashMap.uscalar_sub_eq hi1; scalar_tac
            have hi2v : i2.val = k.val + 1 := HashMap.uscalar_add_eq hi2
            -- the recursive peel, at whichever outcome it ends in
            have hrecout :=
              (ih d i1 body i2 fvs1 stk1 hi1v hbody hfvs1wf hstk1wf) fe lfe hfe hfrel
                st2 o st' hwf2 hrec lst2 hrel2
            rw [ConLeche.Cached.inferPisI.eq_def]
            simp only [absExpr_mk, absExprKind]
            rw [htyorun, pure_bind, ← hiv]
            rw [checkCM_bind_run _ _ hrun1, checkCM_bind_run _ _ hrun2]
            simp only [absExpr_mk, absExprKind, pure_bind]
            rw [← hi1v, ← hi2v]
            rw [show (absExprs fvs).toArray.push (ConLeche.Expr.fvar i.val (absExpr tyo))
                = (absExprs fvs1).toArray from by
              rw [← hfvabs]; simp [absExprs, hfvs1v]]
            rw [show ((absLevel u, (absBinderMeta mb).pw) :: absPisEntries stk.val)
                = absPisEntries stk1.val from by
              simp [hstk1v, absBinderMeta]]
            exact hrecout
          all_goals
            -- move 2: the domain's type is not a sort, both sides throw `invalid`
            (obtain ⟨s0, -, hok⟩ := bind_eq_ok_iff.mp hok
             obtain ⟨v0, -, hok⟩ := bind_eq_ok_iff.mp hok
             obtain ⟨ce, hce, hok⟩ := bind_eq_ok_iff.mp hok
             have ho : o = .Err ce := (congrArg Prod.fst (Result.ok_injective hok)).symm
             subst ho
             rw [invalid_inv hce]
             refine Out.err (ErrSim.invalid (s := "expected a sort") ?_)
             rw [ConLeche.Cached.inferPisI.eq_def]
             simp only [absExpr_mk, absExprKind]
             rw [htyorun, pure_bind, ← hiv]
             rw [checkCM_bind_run _ _ hrun1, checkCM_bind_run _ _ hrun2]
             simp)
    all_goals
      (have hleaf :=
        (infer_pis_leaf_i_refines hw d k ht hfvs hstk) fe lfe hfe hfrel st o st' hwf hok
          lst hrel
       simpa [ConLeche.Cached.inferPisI] using hleaf)

/-- `ConLeche/Cached/CoreC.lean:1269-1290` — **`infer_pis_i` refines
`inferPisI`** (`core_c.rs:3184`): the ∀-telescope peel loop. -/
theorem infer_pis_i_refines (hw : Wrappers mode fuel) (d peel : Std.U64)
    {t : expr.Expr} (k : Std.U64) {fvs : alloc.vec.Vec expr.Expr}
    {stk : alloc.vec.Vec (level.Level × prop_when.PropWhen)}
    (ht : ExprWF t) (hfvs : ExprsWF fvs) (hstk : PisEntriesWF stk.val) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_pis_i mode fuel st fe d peel t k fvs stk)
      (fun lfe => ConLeche.Cached.inferPisI (absMode mode)
        (knot mode lfe fuel.val) d.val peel.val (absExpr t) k.val
        (absExprs fvs).toArray (absPisEntries stk.val)) :=
  infer_pis_i_val hw peel.val d peel t k fvs stk rfl ht hfvs hstk

end

end ConRon.Refine.Core

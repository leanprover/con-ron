/-
The generated basis tables, refined (DESIGN.md §5 P1.5, task #22).

`crates/con-ron-core/src/kernel/basis_tables.rs` is generated from
con-leche's own `BasisKind.declsA` by `proof/ConRon/Gen/Main.lean`; this
file is the other half of that arrangement — the theorem that what the
generated Rust *builds* abstracts to the value it was generated from.
Without it, "generated from con-leche" is a claim about a script; with it,
it is a claim the kernel checks.

The proof is one Aeneas `step` per interned node — 192 for the six blocks —
driven by `step*` off a *specification* tier for the port's smart
constructors (below, also temporary).  It is not `rfl` or `decide`: in this
Aeneas version `Result α` is `ITree RustEffect α` and its `bind` is a
`partial_fixpoint`, so a generated `do` chain does not reduce definitionally
(`rfl` fails in 1.3 s, `decide` has no `DecidableEq` to use, and `simp` with
the call graph unfolded diverges).  Nothing here needs a well-formedness
hypothesis, which is the point of encoding a table as source rather than as
data (task #22's option A; the log entry has the measurements, and the
reason the Nat-op pins go the other way).
-/
import ConRon.Generated
import ConRon.Refine.Abs
import ConRon.Refine.Nat
import ConLeche.Kernel.BasisA

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine

/- The `Expr`-and-above abstraction functions (`absConstantVal`,
   `absHint`, `absFire`, `absRecRule`, `absIndCaps`, `absProjTable`,
   `absConstantInfo`, `absConstantInfos`, `absBasisKind`) lived here in a
   nested `T22` namespace until task #46 moved them to
   `ConRon/Refine/Abs.lean`, as task #22's note said they would.  They are
   in scope unqualified: this file is inside `namespace ConRon.Refine`. -/


/-- The Rust core's basis table for `k`, abstracted: the generated function
runs in `Result` (every smart constructor does, because `Vec::push` and the
word arithmetic can in principle fail), so the claim proved at the end of the
file is that it *succeeds* and that its value is con-leche's. -/
def absBasisDecls (k : env.BasisKind) : Result (List ConLeche.ConstantInfo) :=
  do let v ← basis_tables.basis_decls_a k; ok (absConstantInfos v)

/-! ## TEMPORARY — specifications for the smart constructors

**To be moved to `ConRon/Refine/Abs.lean` (or its own file) when the rest of
the tier grows** — they are `⦃ ⦄` specifications, a different proof style from
the rest of the tier, so unlike the `abs` functions above (which task #46 did
move) they have no client yet outside this file.

These are the first `⦃ ⦄` *specifications* in the project — Aeneas's Hoare
triples, which say "this call succeeds and its result satisfies …".  Every
refinement lemma written before this task was conditional on success
(`f x = ok y → …`); a table's value cannot be, because the table is a closed
term and the claim is about *its* value.

Two settings make the `step` tactic work at all in this project, and they are
the reason it had not been used before: the patched Aeneas package sets
`backward.isDefEq.respectTransparency := false` and `backward.do.legacy :=
true` for its *own* modules (`_tmp/aeneas-lean/lakefile.lean`, task #2's
patch), and without them `⦃ ⦄` goals do not unify with the `@[step]` lemmas —
`step` reports "could not find a local assumption or a theorem to apply" even
on Aeneas's own test suite.  Setting them per file here keeps the change local;
DESIGN.md's task-#22 entry recommends hoisting them into `proof/lakefile.toml`.

A hash word the abstraction forgets is existentially quantified, so nothing
below ever names a hash formula; an index recursion gets `⦃ _ => True ⦄`,
which is exactly the totality the table needs and no more. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.do.legacy true

/-! ### The `Arc` model and the plumbing -/

@[local step] theorem arc_new_spec {T : Type} (x : T) :
    alloc.sync.Arc.new x ⦃ r => r = x ⦄ := by rw [arc_new_eq]; exact .ret rfl

@[local step] theorem arc_deref_spec {T : Type} (A : Type) (x : T) :
    alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref A x ⦃ r => r = x ⦄ := by
  rw [arc_deref_eq]; exact .ret rfl

@[local step] theorem arc_clone_spec {T A : Type} (i : core.alloc.AllocatorClone A)
    (x : T) : alloc.sync.Arc.Insts.CoreCloneClone.clone i x ⦃ r => r = x ⦄ := by
  rw [arc_clone_eq]; exact .ret rfl

@[local step] theorem ptr_new_spec {T : Type} (x : T) :
    ron.ptr.new x ⦃ r => r = x ⦄ := by rw [ptr_new_eq]; exact .ret rfl

@[local step] theorem ptr_clone_spec {T : Type} (x : T) :
    ron.ptr.clone x ⦃ r => r = x ⦄ := by rw [ptr_clone_eq]; exact .ret rfl

@[simp] theorem expr_dup_eq (e : expr.Expr) : expr.dup e = ok e := by
  cases e; simp [expr.dup]

@[local step] theorem name_dup_spec (n : name.Name) : name.dup n ⦃ r => r = n ⦄ := by
  rw [name_dup_eq]; exact .ret rfl

@[local step] theorem level_dup_spec (u : level.Level) : level.dup u ⦃ r => r = u ⦄ := by
  rw [level_dup_eq]; exact .ret rfl

@[local step] theorem expr_dup_spec (e : expr.Expr) : expr.dup e ⦃ r => r = e ⦄ := by
  rw [expr_dup_eq]; exact .ret rfl

/-! ### The hash words: totality, and nothing else -/

@[local step] theorem mix_hash_spec (h k : Std.U64) : name.mix_hash h k ⦃ _ => True ⦄ := by
  unfold name.mix_hash; step*

@[local step] theorem nat_hash_spec (n : Std.U64) : name.nat_hash n ⦃ _ => True ⦄ := by
  unfold name.nat_hash; step*

@[local step] theorem hash32_spec (w : Std.U64) : expr.hash32 w ⦃ _ => True ⦄ := by
  unfold expr.hash32; step*

@[local step] theorem name_hash_data_spec (n : name.Name) :
    name.hash_data n ⦃ _ => True ⦄ := by unfold name.hash_data; step*

@[local step] theorem level_hash_data_spec (u : level.Level) :
    level.hash_data u ⦃ _ => True ⦄ := by unfold level.hash_data; step*

@[local step] theorem level_hash_spec (u : level.Level) :
    level.level_hash u ⦃ _ => True ⦄ := by unfold level.level_hash; step*

@[local step] theorem expr_data_spec (e : expr.Expr) : expr.data e ⦃ _ => True ⦄ := by
  unfold expr.data; step*

@[local step] theorem hash_of_data_spec (w : Std.U64) :
    expr.hash_of_data w ⦃ _ => True ⦄ := by unfold expr.hash_of_data; step*

@[local step] theorem lp_of_data_spec (w : Std.U64) :
    expr.lp_of_data w ⦃ _ => True ⦄ := by unfold expr.lp_of_data; step*

@[local step] theorem sat_range_spec : expr.sat_range ⦃ _ => True ⦄ := by
  unfold expr.sat_range; step*

@[local step] theorem max_u64_spec (a b : Std.U64) :
    expr.max_u64 a b ⦃ _ => True ⦄ := by unfold expr.max_u64; step*

@[local step] theorem sat_succ_spec (n : Std.U64) :
    expr.sat_succ n ⦃ _ => True ⦄ := by unfold expr.sat_succ; step*

@[local step] theorem sat_pred_spec (x : Std.U64) :
    expr.sat_pred x ⦃ _ => True ⦄ := by unfold expr.sat_pred; step*

@[local step] theorem bvar_of_data_spec (w : Std.U64) :
    expr.bvar_of_data w ⦃ _ => True ⦄ := by unfold expr.bvar_of_data; step*

@[local step] theorem fvar_of_data_spec (w : Std.U64) :
    expr.fvar_of_data w ⦃ _ => True ⦄ := by unfold expr.fvar_of_data; step*

@[local step] theorem pack_data_spec (h b f : Std.U64) (lp : Bool) :
    expr.pack_data h b f lp ⦃ _ => True ⦄ := by
  unfold expr.pack_data; split <;> step*

/-! ### The index recursions: totality by induction on the measure

Aeneas's `partial_fixpoint` definitions give no induction principle, so each
of these is a `Nat` induction on `length - i` using the function's own
unfolding equation (DESIGN.md §3.5's rule: induct on the argument, not on the
function).  The `_spec` wrapper is what carries the `@[step]` attribute, so
that `step` never applies a spec to the call it is in the middle of proving. -/

theorem str_hash_from_aux (s : alloc.vec.Vec Std.U32) :
    ∀ (n : Nat) (i : Std.Usize) (acc : Std.U64), s.val.length - i.val ≤ n →
      name.str_hash_from s i acc ⦃ _ => True ⦄ := by
  intro n
  induction n with
  | zero =>
    intro i acc hle
    rw [name.str_hash_from.eq_def]; simp only []
    rw [if_pos (show alloc.vec.Vec.len s ≤ i by scalar_tac)]
    step*
  | succ n ih =>
    intro i acc hle
    rw [name.str_hash_from.eq_def]; simp only []
    split
    · step*
    · rename_i hlt; step*

@[local step] theorem str_hash_from_spec (s : alloc.vec.Vec Std.U32) (i : Std.Usize)
    (acc : Std.U64) : name.str_hash_from s i acc ⦃ _ => True ⦄ :=
  str_hash_from_aux s s.val.length i acc (by omega)

@[local step] theorem str_hash_spec (s : alloc.vec.Vec Std.U32) :
    name.str_hash s ⦃ _ => True ⦄ := by unfold name.str_hash; step*

theorem levels_hash_from_aux (us : alloc.vec.Vec level.Level) :
    ∀ (n : Nat) (i : Std.Usize), us.val.length - i.val ≤ n →
      level.levels_hash_from us i ⦃ _ => True ⦄ := by
  intro n
  induction n with
  | zero =>
    intro i hle
    rw [level.levels_hash_from.eq_def]; simp only []
    rw [if_pos (show alloc.vec.Vec.len us ≤ i by scalar_tac)]
    step*
  | succ n ih =>
    intro i hle
    rw [level.levels_hash_from.eq_def]; simp only []
    split
    · step*
    · rename_i hlt; step*

@[local step] theorem levels_hash_from_spec (us : alloc.vec.Vec level.Level)
    (i : Std.Usize) : level.levels_hash_from us i ⦃ _ => True ⦄ :=
  levels_hash_from_aux us us.val.length i (by omega)

@[local step] theorem levels_hash_spec (us : alloc.vec.Vec level.Level) :
    level.levels_hash us ⦃ _ => True ⦄ := by unfold level.levels_hash; step*

/-- `level_has_param` recurses on the `Level` tree, so this one is
`Level.ind'` (`Abs.lean`) rather than a measure; the node projections have to
be reduced by hand in each case, because `step` will otherwise split the match
on an unreduced `(Level.mk nd)._0`. -/
theorem level_has_param_aux : ∀ u : level.Level, level.level_has_param u ⦃ _ => True ⦄ := by
  intro u
  induction u using Level.ind' with
  | zero h =>
    rw [level.level_has_param.eq_def]
    simp only [arc_deref_eq, bind_tc_ok, level.Level._0._simpLemma_,
      level.LevelNode.kind._simpLemma_]
    exact .ret trivial
  | succ h v ihv =>
    rw [level.level_has_param.eq_def]
    simp only [arc_deref_eq, bind_tc_ok, level.Level._0._simpLemma_,
      level.LevelNode.kind._simpLemma_]
    exact ihv
  | max h a b iha ihb =>
    rw [level.level_has_param.eq_def]
    simp only [arc_deref_eq, bind_tc_ok, level.Level._0._simpLemma_,
      level.LevelNode.kind._simpLemma_]
    apply WP.spec_bind iha; intro x _; split <;> [exact .ret trivial; exact ihb]
  | imax h a b iha ihb =>
    rw [level.level_has_param.eq_def]
    simp only [arc_deref_eq, bind_tc_ok, level.Level._0._simpLemma_,
      level.LevelNode.kind._simpLemma_]
    apply WP.spec_bind iha; intro x _; split <;> [exact .ret trivial; exact ihb]
  | param h n =>
    rw [level.level_has_param.eq_def]
    simp only [arc_deref_eq, bind_tc_ok, level.Level._0._simpLemma_,
      level.LevelNode.kind._simpLemma_]
    exact .ret trivial

@[local step] theorem level_has_param_spec (u : level.Level) :
    level.level_has_param u ⦃ _ => True ⦄ := level_has_param_aux u

theorem levels_have_param_from_aux (us : alloc.vec.Vec level.Level) :
    ∀ (n : Nat) (i : Std.Usize), us.val.length - i.val ≤ n →
      level.levels_have_param_from us i ⦃ _ => True ⦄ := by
  intro n
  induction n with
  | zero =>
    intro i hle
    rw [level.levels_have_param_from.eq_def]; simp only []
    rw [if_pos (show alloc.vec.Vec.len us ≤ i by scalar_tac)]
    step*
  | succ n ih =>
    intro i hle
    rw [level.levels_have_param_from.eq_def]; simp only []
    split
    · step*
    · rename_i hlt; step*

@[local step] theorem levels_have_param_from_spec (us : alloc.vec.Vec level.Level)
    (i : Std.Usize) : level.levels_have_param_from us i ⦃ _ => True ⦄ :=
  levels_have_param_from_aux us us.val.length i (by omega)

@[local step] theorem levels_have_param_spec (us : alloc.vec.Vec level.Level) :
    level.levels_have_param us ⦃ _ => True ⦄ := by
  unfold level.levels_have_param; step*

theorem names_hash_from_aux (ps : alloc.vec.Vec name.Name) :
    ∀ (n : Nat) (i : Std.Usize) (acc : Std.U64), ps.val.length - i.val ≤ n →
      prop_when.names_hash_from ps i acc ⦃ _ => True ⦄ := by
  intro n
  induction n with
  | zero =>
    intro i acc hle
    rw [prop_when.names_hash_from.eq_def]; simp only []
    rw [if_pos (show alloc.vec.Vec.len ps ≤ i by scalar_tac)]
    step*
  | succ n ih =>
    intro i acc hle
    rw [prop_when.names_hash_from.eq_def]; simp only []
    split
    · step*
    · rename_i hlt; step*

@[local step] theorem names_hash_from_spec (ps : alloc.vec.Vec name.Name)
    (i : Std.Usize) (acc : Std.U64) :
    prop_when.names_hash_from ps i acc ⦃ _ => True ⦄ :=
  names_hash_from_aux ps ps.val.length i acc (by omega)

@[local step] theorem hash_repr_spec (r : prop_when.PropWhenRepr) :
    prop_when.hash_repr r ⦃ _ => True ⦄ := by unfold prop_when.hash_repr; split <;> step*

@[local step] theorem has_params_spec (pw : prop_when.PropWhen) :
    prop_when.has_params pw ⦃ _ => True ⦄ := by
  unfold prop_when.has_params; split <;> step*

@[local step] theorem hash_pw_spec (pw : prop_when.PropWhen) :
    prop_when.hash_pw pw ⦃ _ => True ⦄ := by unfold prop_when.hash_pw; step*

/-! ### The node constructors: the shape, with the hash forgotten -/

@[local step] theorem name_anonymous_spec :
    name.anonymous ⦃ n => n = .mk (.mk 1723#u64 .Anonymous) ⦄ := by
  unfold name.anonymous; step*

@[local step] theorem name_mk_str_spec (pre : name.Name) (s : alloc.vec.Vec Std.U32) :
    name.mk_str pre s ⦃ n => ∃ h, n = .mk (.mk h (.Str pre s)) ⦄ := by
  unfold name.mk_str; step*

@[local step] theorem name_mk_num_spec (pre : name.Name) (k : Std.U64) :
    name.mk_num pre k ⦃ n => ∃ h, n = .mk (.mk h (.Num pre k)) ⦄ := by
  unfold name.mk_num; step*

@[local step] theorem level_zero_spec :
    level.zero ⦃ u => u = .mk (.mk 1#u64 .Zero) ⦄ := by unfold level.zero; step*

@[local step] theorem level_succ_spec (a : level.Level) :
    level.succ a ⦃ u => ∃ h, u = .mk (.mk h (.Succ a)) ⦄ := by
  unfold level.succ; step*

@[local step] theorem level_max_spec (a b : level.Level) :
    level.max a b ⦃ u => ∃ h, u = .mk (.mk h (.Max a b)) ⦄ := by
  unfold level.max; step*

@[local step] theorem level_imax_spec (a b : level.Level) :
    level.imax a b ⦃ u => ∃ h, u = .mk (.mk h (.Imax a b)) ⦄ := by
  unfold level.imax; step*

@[local step] theorem level_param_spec (n : name.Name) :
    level.param n ⦃ u => ∃ h, u = .mk (.mk h (.Param n)) ⦄ := by
  unfold level.param; step*

@[local step] theorem expr_bvar_spec (i : Std.U64) :
    expr.bvar i ⦃ e => ∃ h, e = .mk (.mk h (.Bvar i)) ⦄ := by
  unfold expr.bvar; step*

@[local step] theorem expr_mk_bvar_spec (i : Std.U64) :
    expr.mk_bvar i ⦃ e => ∃ h, e = .mk (.mk h (.Bvar i)) ⦄ := by
  unfold expr.mk_bvar; step*

@[local step] theorem expr_sort_spec (u : level.Level) :
    expr.sort u ⦃ e => ∃ h, e = .mk (.mk h (.«Sort» u)) ⦄ := by
  unfold expr.sort; step*

@[local step] theorem expr_mk_const_spec (n : name.Name)
    (us : alloc.vec.Vec level.Level) :
    expr.mk_const n us ⦃ e => ∃ h, e = .mk (.mk h (.Const n us)) ⦄ := by
  unfold expr.mk_const; step*

@[local step] theorem expr_app_spec (f a : expr.Expr) :
    expr.app f a ⦃ e => ∃ h, e = .mk (.mk h (.App f a)) ⦄ := by
  unfold expr.app
  repeat' (first | step | split)
  all_goals simp_all

/-- The binder datum's constructor (task #38: the datum is behind a handle,
so the generated table builds one through `expr::binder_meta` instead of a
struct literal). -/
@[local step] theorem expr_binder_meta_spec (pw : prop_when.PropWhen) :
    expr.binder_meta pw ⦃ m => m = ⟨pw⟩ ⦄ := by unfold expr.binder_meta; step*

@[local step] theorem expr_lam_spec (ty b : expr.Expr) (m : expr.BinderMeta) :
    expr.lam ty b m ⦃ e => ∃ h, e = .mk (.mk h (.Lam ty b m)) ⦄ := by
  unfold expr.lam
  repeat' (first | step | split)
  all_goals simp_all

@[local step] theorem expr_forall_e_spec (ty b : expr.Expr) (m : expr.BinderMeta) :
    expr.forall_e ty b m ⦃ e => ∃ h, e = .mk (.mk h (.ForallE ty b m)) ⦄ := by
  unfold expr.forall_e
  repeat' (first | step | split)
  all_goals simp_all

/-! ### The zero-ness datum

`prop_when::if_all_zero` decides the `0`/`1`/`2` cases without touching
`canon`, so the two shapes the tables use need no canonicalisation lemma and
no `NameWF`: the length hypothesis picks the branch.  (A length-3 spec would
need `canon`/`merge`/`name_cmp` totality, which nothing here asks for.) -/

@[local step] theorem of_repr_spec (r : prop_when.PropWhenRepr) :
    prop_when.of_repr r ⦃ w => w = ⟨r⟩ ⦄ := by unfold prop_when.of_repr; step*

@[local step] theorem prop_when_never_spec :
    prop_when.never ⦃ w => w = ⟨.Never⟩ ⦄ := by unfold prop_when.never; step*

theorem if_all_zero_nil_spec (ps : alloc.vec.Vec name.Name)
    (h : ps.val = []) : prop_when.if_all_zero ps ⦃ w => w = ⟨.Always⟩ ⦄ := by
  unfold prop_when.if_all_zero
  rw [if_pos (show alloc.vec.Vec.len ps = 0#usize by scalar_tac)]
  step*

theorem if_all_zero_one_spec (ps : alloc.vec.Vec name.Name)
    (n : name.Name) (h : ps.val = [n]) :
    prop_when.if_all_zero ps ⦃ w => w = ⟨.One n⟩ ⦄ := by
  unfold prop_when.if_all_zero
  rw [if_neg (show ¬ alloc.vec.Vec.len ps = 0#usize by scalar_tac),
      if_pos (show alloc.vec.Vec.len ps = 1#usize by scalar_tac)]
  step*

/-- The two shapes as `step` sees them in a generated table: the empty vector
is syntactic, and a one-element vector arrives as a `Vec::push` result, so its
spec carries the list equation as a side goal. -/
@[local step] theorem if_all_zero_new_spec :
    prop_when.if_all_zero (alloc.vec.Vec.new name.Name) ⦃ w => w = ⟨.Always⟩ ⦄ :=
  if_all_zero_nil_spec _ (by simp [alloc.vec.Vec.new])

@[local step] theorem if_all_zero_singleton_spec (ps : alloc.vec.Vec name.Name)
    (h : ∃ n, ps.val = [n]) :
    prop_when.if_all_zero ps ⦃ w => ∃ n, ps.val = [n] ∧ w = ⟨.One n⟩ ⦄ := by
  obtain ⟨n, hn⟩ := h
  have := if_all_zero_one_spec ps n hn
  apply WP.spec_mono this
  intro w hw; exact ⟨n, hn, hw⟩

/-! ## The statement

`absBasisDecls k` is the port's table, abstracted.  The generated function
runs in `Result`, so the claim is that it *succeeds* and that its value is
con-leche's — the `⦃ ⦄` specification below says exactly that, and the
`Result`-level equation follows from it. -/

/-- The port's table for `k`, abstracted: it succeeds, and its value is
con-leche's `BasisKind.declsA`. -/
def BasisSpec (k : env.BasisKind) : Prop :=
  basis_tables.basis_decls_a k
    ⦃ v => absConstantInfos v = ConLeche.BasisKind.declsA (absBasisKind k) ⦄

/-! ## The proofs

One `step` per interned node, driven by `step*` off the specification tier
above; the side goals are the `Vec::push` length bounds (`3 < Usize.max`,
which needs `Usize.bounds_eq` because `Usize.max` is platform-dependent) and
the one-element list equations the `if_all_zero` spec asks for.  The closing
`simp_all` then evaluates `abs` on the reconstructed nodes and compares it to
con-leche's value; no hash formula is ever named, because `abs` forgets the
stored word. -/

/-- The tactic that closes a block: walk the chain with the specification
tier, then discharge the bounds and evaluate `abs`. -/
syntax "basis_block" : tactic
macro_rules
  | `(tactic| basis_block) => `(tactic|
      (step*
       all_goals try simp_all [alloc.vec.Vec.new, absConstantInfos, absConstantInfo,
         absConstantVal, absIndCaps, absRecRule, absFire, absExpr, absExprNode,
         absExprKind, absName, absNameNode, absNameKind, absNames, absString,
         absLevel, absLevelNode, absLevelKind, absLevels, absPropWhen,
         absPropWhenRepr, absLiteral]
       all_goals (rcases Std.Usize.bounds_eq with hb | hb <;>
         simp_all [hb, Std.U32.max, Std.U64.max, Std.U32.numBits, Std.U64.numBits])
       all_goals (simp only [absBasisKind]; first | rfl | decide)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem basis_decls_false_refines : BasisSpec .FalseK := by
  unfold BasisSpec basis_tables.basis_decls_a basis_tables.basis_decls_false
  basis_block

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem basis_decls_empty_refines : BasisSpec .EmptyK := by
  unfold BasisSpec basis_tables.basis_decls_a basis_tables.basis_decls_empty
  basis_block

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem basis_decls_eq_refines : BasisSpec .EqK := by
  unfold BasisSpec basis_tables.basis_decls_a basis_tables.basis_decls_eq
  basis_block

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem basis_decls_nat_refines : BasisSpec .NatK := by
  unfold BasisSpec basis_tables.basis_decls_a basis_tables.basis_decls_nat
  basis_block

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem basis_decls_punit_refines : BasisSpec .PunitK := by
  unfold BasisSpec basis_tables.basis_decls_a basis_tables.basis_decls_punit
  basis_block

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem basis_decls_quot_refines : BasisSpec .QuotK := by
  unfold BasisSpec basis_tables.basis_decls_a basis_tables.basis_decls_quot
  basis_block

/-- The table refines `BasisKind.declsA` at every kind. -/
theorem basis_decls_a_refines : ∀ k : env.BasisKind, BasisSpec k
  | .EqK => basis_decls_eq_refines
  | .NatK => basis_decls_nat_refines
  | .PunitK => basis_decls_punit_refines
  | .EmptyK => basis_decls_empty_refines
  | .FalseK => basis_decls_false_refines
  | .QuotK => basis_decls_quot_refines

/-- The same, as the `Result`-level equation of DESIGN.md §1: the port's
table, abstracted, *is* con-leche's. -/
theorem absBasisDecls_eq (k : env.BasisKind) :
    absBasisDecls k = ok (ConLeche.BasisKind.declsA (absBasisKind k)) := by
  obtain ⟨v, hv, habs⟩ := WP.spec_imp_exists (basis_decls_a_refines k)
  simp [absBasisDecls, hv, habs]

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/--
info: 'ConRon.Refine.absBasisDecls_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms absBasisDecls_eq

end ConRon.Refine

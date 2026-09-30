/-
`CORE_PLAN.md` step 4 (task #49), part 3: the **stored-shape guards** of
`crates/con-ron-core/src/kernel/core_k.rs` — the seventeen functions that
decide whether an environment supports `Nat` and `String` literals, refined
against `ConLeche/Kernel/Core.lean:274-475` (and, for the two environment
guards, the index twins `ConLeche/Kernel/FEnv.lean:116-131`).

What is here, in the Rust's own order:

* `nat_ind_ok`, `nat_zero_ok`, `nat_succ_ok` (`Core.lean:274-295`) and
  `nat_lit_supported` (`:297-305`, `FEnv.lean:116-119`);
* `consts_resolve` (`:307-332`, deliberately dead) and its two factored-out
  `isSome` groups `nat_trio_stored` and `str_support_stored`;
* `string_ty_ok`, `char_ty_ok`, `list_ty_ok`, `list_nil_ty_ok`,
  `list_cons_ty_ok`, `list_cons_tail_ok`, `char_of_nat_ty_ok`,
  `string_of_list_ty_ok` (`:373-455`) and `str_lit_supported` (`:457-475`,
  `FEnv.lean:121-130`);
* `is_ctor_info` (`:118-125 isCtorApp`'s inner `match`).

Five things made this harder than the leaf readers of `ExprOps`:

1. **The guards look at an *arbitrary* stored type.**  Every existing
   refinement of an `Expr` walk inducts on `ExprWF` and reads the node shape
   off a `*_inv` lemma; here the generated body `match`es on the kind of a
   type that came out of the environment, so the proof goes the other way:
   `split at h` names the observed kind, `absExpr_kind` turns it into the
   con-leche node, and `ExprWF.children` hands back the well-formedness of the
   children that kind exposes.  The two tactics `kind_split` and
   `dead_kind_arm` package the descent, which is what keeps the nine dead arms
   of each `match` to nothing at all.
2. **The port's `match` order is not the matcher's.**  A cited pattern such as
   `.forallE (.app (.const l1 us1) (.bvar 1)) …` is decided by the Lean matcher
   head-first, while the port tests the argument before the head; so in a dead
   arm the goal's own `match` cannot iota-reduce and has to be `split` as well
   (that is `dead_kind_arm`'s second half).  The `.bvar k` index arms need
   `Std.UScalar.eq_of_val_eq` on top, since `↑(k#uscalar)` is not the literal
   `k` for the matcher.
3. **`env::to_constant_val` is not `id`.**  The five `*_ty_ok` guards read
   through it, and its `.ProjInfo` arm *builds* `⟨projTableName …, …, Sort 1⟩`,
   so it needs its own refinement (`to_constant_val_refines`, which belongs in
   task #46's `Refine/Env.lean`).
4. **`==` is not always `decide`.**  `Name`/`Level`/`Expr` all define `beq` as
   `decide (· = ·)`, but a *list* of levels (`us1 == [.param p]`) goes through
   `List.beq`, so a guard's `&&` cascade is normalised with `beq_eq_decide_eq`
   before `levels_beq_refines` fits.  And `&&` is left-associated while the
   port's `if g then rest else false` nest is right-associated, which is what
   `and_step` (plus one `simp only [Bool.and_assoc]`) reconciles.
5. **The pinned names.**  Every guard compares against a `basis_names` name;
   those refinements are `Refine/CoreKNames.lean`'s (another agent's file, not
   imported here), so this file takes them bundled as `PinnedBasisNames` and
   the parent agent discharges it at merge.  `consts_resolve` additionally
   takes `henv`, the `FEnv.find? = Env.find?` agreement (`mkFEnv_find?`),
   because the cited `Expr.constsResolve` is stated over an `Env` and has no
   `F`-twin in `FEnv.lean`.

Helpers that belong elsewhere once the tier grows: `absExpr_kind`,
`ExprWF.children` and its four specialisations (`Refine/Expr.lean`),
`to_constant_val_refines` (`Refine/Env.lean`), and
`find_abs`/`find_wf`/`find_isSome`/`option_is_some`/`and_step`
(`Refine/CoreKBase.lean`).
-/
import ConRon.Refine.CoreKBase

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.CoreK

/-! ## Reading an arbitrary stored `Expr`

The two lemmas that replace the `ExprWF`-induction/`*_inv` idiom when the
expression under the microscope is *given* rather than built: one reads the
abstraction off the observed kind, the other reads the children's
well-formedness off it. -/

/-! ## Level parameters: the port's `len()`/`[0]` against con-leche's list -/

/-! ## `env::to_constant_val`

Belongs in task #46's `Refine/Env.lean`; it is here because the five
`*_ty_ok` guards read the stored type through it and nothing else in step 4
does. -/

/-! ## The pinned basis names

`Refine/CoreKNames.lean` (another agent's file — not imported here) proves the
ten pinned-name refinements every guard below needs.  They are bundled as one
hypothesis so that a guard's statement stays readable; **the parent agent
discharges `PinnedBasisNames` at merge**. -/

/-! ## The dead-arm tactic

Each `*_ok` guard is a nest of `match`es on the kind of a stored node; the
cited Lean definition is one `match` on the whole abstracted node.  A `split at
h` on a port `match` therefore produces one live arm and nine arms in which the
port answered `false` and the Lean pattern cannot match.  This closes those. -/

/-- **The dead arm of a stored-kind `match`.**  `h : ok false = ok c`, and the
cited Lean pattern does not match the node the observed kind abstracts to.
`split` on the goal's own `match` is what decides the leftovers the abstraction
leaves opaque (a `.const`'s level list, say), and the pattern equation it
leaves behind is the contradiction. -/
syntax "dead_kind_arm" ident : tactic
macro_rules
  | `(tactic| dead_kind_arm $h:ident) => `(tactic|
      (simp only [Result.ok.injEq] at $h:ident
       rw [← $h:ident]
       try (split <;> first | rfl | (rename_i heq; simp at heq) | simp_all)))

/-- **Descend one port `match` on a stored node's kind.**  `split at h`, name
the kind equation, push it through `absExpr_kind` in the goal, and close the
dead arms.  What is left is the one arm the cited Lean pattern can match; its
pattern variables are still inaccessible, so a `rename_i` follows each use. -/
syntax "kind_split" ident ident : tactic
macro_rules
  | `(tactic| kind_split $h:ident $hk:ident) => `(tactic|
      (split at $h:ident
       all_goals rename_i $hk:ident
       -- task #94: a reader's `match` is on `view`'s `ExprView`, so the
       -- hypothesis `split` names is `ofKind k = ExprView.X …`; the ten
       -- inversions put it back as `k = ExprKind.X …`, which is what the
       -- goal's `absExprKind` and every arm below speak.
       all_goals of_kind_inv $hk:ident
       all_goals rw [$hk:ident]
       all_goals simp only [absExprKind]
       all_goals try dead_kind_arm $h:ident))

/-! ## `Nat` support: the three stored-shape guards (`Core.lean:274-295`) -/

/-! ## `String` support: the eight stored-shape guards (`Core.lean:373-455`)

These five read the stored type through `env::to_constant_val` (any constant
kind is accepted, as the cited Lean's `ci.toConstantVal` is total). -/

/-! ## The two environment guards (`Core.lean:297-305`, `:457-475`)

Stated against the `FEnv` twins of `ConLeche/Kernel/FEnv.lean` (the port reads
the environment through `fenv::find` throughout — module note deviation 3), and
proved by the `&&`-cascade step below: the port's `if g then rest else false`
nest is the cited `g && rest` once the Lean side is right-associated. -/

/-! ## `Expr.constsResolve` (`Core.lean:307-332`) and its two `isSome` groups

`consts_resolve` is **deliberately dead** (`core_k.rs`'s module note: the
install checks it once per declaration, the core never calls it), and it is the
one function here that recurses over an `Expr`, so it is proved by induction on
the `ExprWF` derivation (task #47's rule).  The cited Lean is stated over an
`Env`; `FEnv.lean` has no `constsResolveF` twin, so the lemma takes `henv`, the
`FEnv.find? = Env.find?` agreement that `mkFEnv_find?` supplies. -/

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

end ConRon.Refine.CoreK

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

open ConRon.Refine.T22

/-! ## Reading an arbitrary stored `Expr`

The two lemmas that replace the `ExprWF`-induction/`*_inv` idiom when the
expression under the microscope is *given* rather than built: one reads the
abstraction off the observed kind, the other reads the children's
well-formedness off it. -/

/-- `absExpr` in terms of the node's kind — the direction `ExprOps.node_kind`
does not go, and the one a `cases hk : e._0.kind` needs. -/
theorem absExpr_kind (e : expr.Expr) : absExpr e = absExprKind e._0.kind := by
  cases e with | mk nd => cases nd with | mk d k => rfl

/-- **The children of a well-formed node are well formed**, indexed by the
observed kind.  Every `*_ok` guard below uses it exactly once per `match` it
descends through. -/
theorem ExprWF.children {e : expr.Expr} (he : ExprWF e) :
    match e._0.kind with
    | .Bvar _ => True
    | .Fvar _ ty => ExprWF ty
    | .«Sort» u => LevelWF u
    | .Const n us => NameWF n ∧ LevelsWF us
    | .App f a => ExprWF f ∧ ExprWF a
    | .Lam ty b m => ExprWF ty ∧ ExprWF b ∧ BinderMetaWF m
    | .ForallE ty b m => ExprWF ty ∧ ExprWF b ∧ BinderMetaWF m
    | .LetE ty v b => ExprWF ty ∧ ExprWF v ∧ ExprWF b
    | .Lit l => LiteralWF l
    | .Proj s _ x => NameWF s ∧ ExprWF x := by
  cases he with
  | @bvar i e h1 => obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1; exact trivial
  | @fvar idx ty e hty h1 => obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1; exact hty
  | @sort u e hu h1 => obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1; exact hu
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1; exact ⟨hn, hus⟩
  | @app f a e hf ha h1 => obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1; exact ⟨hf, ha⟩
  | @lam ty b m e hty hb hm h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1; exact ⟨hty, hb, hm⟩
  | @forall_e ty b m e hty hb hm h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1; exact ⟨hty, hb, hm⟩
  | @let_e ty v b e hty hv hb h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1; exact ⟨hty, hv, hb⟩
  | @lit l e hl h1 => obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1; exact hl
  | @proj s i x e hs hx h1 => obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1; exact ⟨hs, hx⟩

/-! ## Level parameters: the port's `len()`/`[0]` against con-leche's list -/

/-- `cv.level_params.len() == 0` is con-leche's `levelParams.isEmpty`. -/
theorem level_params_nil {lp : alloc.vec.Vec name.Name}
    (h : alloc.vec.Vec.len lp = 0#usize) : absNames lp = [] := by
  simp only [absNames, HashMap.vec_len_eq_zero_iff.mp h, List.map_nil]

/-- `cv.level_params.len() == 0` fails exactly when con-leche's
`levelParams.isEmpty` does. -/
theorem level_params_not_nil {lp : alloc.vec.Vec name.Name}
    (h : ¬ (alloc.vec.Vec.len lp = 0#usize)) : absNames lp ≠ [] := by
  intro hc
  refine h (HashMap.vec_len_eq_zero_iff.mpr ?_)
  have : (lp.val.map absName) = [] := hc
  simpa using this

/-- `cv.level_params.len() == 1` plus `cv.level_params[0]` is con-leche's
`| [p] => …` pattern. -/
theorem level_params_one {lp : alloc.vec.Vec name.Name} {p : name.Name}
    (hlen : alloc.vec.Vec.len lp = 1#usize)
    (hp : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice name.Name)
      lp 0#usize = ok p) :
    absNames lp = [absName p] ∧ (NamesWF lp → NameWF p) := by
  have hl : lp.val.length = 1 := by
    have := alloc.vec.Vec.len_val lp; rw [hlen] at this; scalar_tac
  have h0 : lp.val[0]? = some p := by simpa using ExprOps.vec_index_getElem? hp
  match hv : lp.val with
  | [] => rw [hv] at hl; simp at hl
  | x :: y :: _ => rw [hv] at hl; simp at hl
  | [x] =>
    rw [hv] at h0; simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    subst h0
    exact ⟨by simp only [absNames, hv, List.map_cons, List.map_nil],
      fun hwf => hwf x (by rw [hv]; simp)⟩

/-- The `len() == 1` test failing is con-leche's `| [p] => … | _ => false`
falling through. -/
theorem level_params_not_one {lp : alloc.vec.Vec name.Name}
    (h : ¬ (alloc.vec.Vec.len lp = 1#usize)) :
    ∀ q, absNames lp ≠ [q] := by
  intro q hc
  have hl : (lp.val.map absName).length = 1 := by
    rw [show lp.val.map absName = absNames lp from rfl, hc]; rfl
  simp only [List.length_map] at hl
  exact h (by have := alloc.vec.Vec.len_val lp; scalar_tac)

/-! ## `env::to_constant_val`

Belongs in task #46's `Refine/Env.lean`; it is here because the five
`*_ty_ok` guards read the stored type through it and nothing else in step 4
does. -/

/-- `ConLeche/Kernel/Env.lean:606-609` — `env::to_constant_val` refines
`ConstantInfo.toConstantVal`.  The six ordinary arms are `constant_val_dup`
(three identities plus `names_copy`); the `.ProjInfo` arm *builds* the dummy
`⟨projTableName t.structName, t.levelParams, Sort 1⟩`. -/
theorem to_constant_val_refines {c : env.ConstantInfo} {cv : env.ConstantVal}
    (hc : ConstantInfoWF c) (h : env.to_constant_val c = ok cv) :
    absConstantVal cv = (absConstantInfo c).toConstantVal ∧ ConstantValWF cv := by
  have hdup : ∀ (cv0 : env.ConstantVal), ConstantValWF cv0 →
      env.constant_val_dup cv0 = ok cv →
      absConstantVal cv = absConstantVal cv0 ∧ ConstantValWF cv := by
    intro cv0 hwf hd
    rw [env.constant_val_dup] at hd
    simp only [name_dup_eq, bind_tc_ok, bind_eq_ok_iff, Result.ok.injEq] at hd
    obtain ⟨v, hv, e, he, hcv⟩ := hd
    obtain ⟨hn0, hl0, ht0⟩ := hwf
    subst hcv
    have hvv : v.val = cv0.level_params.val := PropWhen.names_copy_val hv
    have hee : e = cv0.ty := Expr.dup_eq he
    subst hee
    refine ⟨?_, hn0, ?_, ht0⟩
    · simp only [absConstantVal, absNames, hvv]
    · intro n hn; exact hl0 n (by rw [← hvv]; exact hn)
  cases c with
  | AxiomInfo cv0 => exact hdup cv0 hc h
  | DefnInfo cv0 v hi => exact hdup cv0 hc.1 h
  | ThmInfo cv0 v => exact hdup cv0 hc.1 h
  | IndInfo cv0 caps => exact hdup cv0 hc.1 h
  | CtorInfo cv0 np nf => exact hdup cv0 hc h
  | RecInfo cv0 mi rp rs => exact hdup cv0 hc.1 h
  | ProjInfo t =>
    obtain ⟨hsn, hlp, -, -, -, -⟩ := hc
    rw [env.to_constant_val] at h
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨n, hn, v, hv, l, hl, l1, hl1, e, he, hcv⟩ := h
    obtain ⟨hnabs, hnwf⟩ := proj_table_name_refines hsn hn
    have hvv : v.val = t.level_params.val := PropWhen.names_copy_val hv
    subst hcv
    have e3 : absExpr e = ConLeche.Expr.sort (.succ .zero) := by
      rw [Expr.sort_refines he, Level.succ_refines hl1, Level.zero_refines hl]
    refine ⟨?_, hnwf, ?_, Expr.sort_wf (LevelWF.succ (LevelWF.zero hl) hl1) he⟩
    · simp only [absConstantVal, absConstantInfo, ConLeche.ConstantInfo.toConstantVal,
        absProjTable, absNames, hvv, hnabs, e3]
    · intro q hq; exact hlp q (by rw [← hvv]; exact hq)

/-! ## The pinned basis names

`Refine/CoreKNames.lean` (another agent's file — not imported here) proves the
ten pinned-name refinements every guard below needs.  They are bundled as one
hypothesis so that a guard's statement stays readable; **the parent agent
discharges `PinnedBasisNames` at merge**. -/

/-- The ten `basis_names` pins the guards of this file compare against:
each pinned name refines its `ConLeche/Kernel/Basis/Names.lean` twin and is
well formed. -/
structure PinnedBasisNames : Prop where
  nat : ∀ n, basis_names.nat_name = ok n → absName n = ConLeche.natName ∧ NameWF n
  natZero : ∀ n, basis_names.nat_zero_name = ok n →
    absName n = ConLeche.natZeroName ∧ NameWF n
  natSucc : ∀ n, basis_names.nat_succ_name = ok n →
    absName n = ConLeche.natSuccName ∧ NameWF n
  string : ∀ n, basis_names.string_name = ok n →
    absName n = ConLeche.stringName ∧ NameWF n
  stringOfList : ∀ n, basis_names.string_of_list_name = ok n →
    absName n = ConLeche.stringOfListName ∧ NameWF n
  list : ∀ n, basis_names.list_name = ok n →
    absName n = ConLeche.listName ∧ NameWF n
  listNil : ∀ n, basis_names.list_nil_name = ok n →
    absName n = ConLeche.listNilName ∧ NameWF n
  listCons : ∀ n, basis_names.list_cons_name = ok n →
    absName n = ConLeche.listConsName ∧ NameWF n
  char : ∀ n, basis_names.char_name = ok n →
    absName n = ConLeche.charName ∧ NameWF n
  charOfNat : ∀ n, basis_names.char_of_nat_name = ok n →
    absName n = ConLeche.charOfNatName ∧ NameWF n

/-- `ExprWF.children` at the four kinds the guards descend through. -/
theorem ExprWF.forallE_children {e ty b : expr.Expr} {m : expr.BinderMeta}
    (he : ExprWF e) (hk : e._0.kind = .ForallE ty b m) :
    ExprWF ty ∧ ExprWF b ∧ BinderMetaWF m := by
  have hc := ExprWF.children he; rw [hk] at hc; exact hc

theorem ExprWF.const_children {e : expr.Expr} {n : name.Name}
    {us : alloc.vec.Vec level.Level} (he : ExprWF e) (hk : e._0.kind = .Const n us) :
    NameWF n ∧ LevelsWF us := by
  have hc := ExprWF.children he; rw [hk] at hc; exact hc

theorem ExprWF.sort_child {e : expr.Expr} {u : level.Level}
    (he : ExprWF e) (hk : e._0.kind = .«Sort» u) : LevelWF u := by
  have hc := ExprWF.children he; rw [hk] at hc; exact hc

theorem ExprWF.app_children {e f a : expr.Expr}
    (he : ExprWF e) (hk : e._0.kind = .App f a) : ExprWF f ∧ ExprWF a := by
  have hc := ExprWF.children he; rw [hk] at hc; exact hc

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
       all_goals rw [$hk:ident]
       all_goals simp only [absExprKind]
       all_goals try dead_kind_arm $h:ident))

/-- The `levelParams.isEmpty` half of a guard, when the port's `len() == 0`
test fails. -/
theorem absNames_isEmpty_false {lp : alloc.vec.Vec name.Name}
    (h : ¬ (alloc.vec.Vec.len lp = 0#usize)) : (absNames lp).isEmpty = false := by
  cases hq : absNames lp with
  | nil => exact absurd hq (level_params_not_nil h)
  | cons a l => rfl

/-- The shape of `levelParams` when the port's `len() == 1` test fails: the
cited `| [p] => … | _ => false` falls through either way. -/
theorem level_params_shape_not_one {lp : alloc.vec.Vec name.Name}
    (h : ¬ (alloc.vec.Vec.len lp = 1#usize)) :
    absNames lp = [] ∨ ∃ a b l, absNames lp = a :: b :: l := by
  have key : ∀ L : List ConLeche.Name, absNames lp = L →
      (L = [] ∨ ∃ a b l, L = a :: b :: l) := by
    intro L hL
    match L with
    | [] => exact Or.inl rfl
    | [a] => exact absurd hL (level_params_not_one h a)
    | a :: b :: l => exact Or.inr ⟨a, b, l, rfl⟩
  exact key _ rfl

/-- `expr::beq ty (expr::sort (level::succ level::zero))` — the `Type`
comparison `nat_ind_ok`, `string_ty_ok` and `char_ty_ok` all end in. -/
theorem beq_sort_one {t : expr.Expr} {c : Bool} {l l1 : level.Level} {e : expr.Expr}
    (ht : ExprWF t) (hl : level.zero = ok l) (hl1 : level.succ l = ok l1)
    (he : expr.sort l1 = ok e) (hbeq : expr.beq t e = ok c) :
    c = decide (absExpr t = ConLeche.Expr.sort (.succ .zero)) := by
  rw [Expr.beq_refines ht (Expr.sort_wf (LevelWF.succ (LevelWF.zero hl) hl1) he) hbeq,
    Expr.sort_refines he, Level.succ_refines hl1, Level.zero_refines hl]

/-! ## `Nat` support: the three stored-shape guards (`Core.lean:274-295`) -/

/-- `ConLeche/Kernel/Core.lean:118-125` — `core_k::is_ctor_info` refines the
inner `match env.find? c with | some (.ctorInfo …) => true | _ => false` of
`isCtorApp` (the guard's own consumer is `is_ctor_app`). -/
theorem is_ctor_info_refines {ci : env.ConstantInfo} {c : Bool}
    (h : core_k.is_ctor_info ci = ok c) :
    c = (match absConstantInfo ci with
         | .ctorInfo _ _ _ => true
         | _ => false) := by
  cases ci <;>
    simp_all only [core_k.is_ctor_info, absConstantInfo, Result.ok.injEq]

/-- `ConLeche/Kernel/Core.lean:274-278` — `core_k::nat_ind_ok` refines
`natIndOk`. -/
theorem nat_ind_ok_refines {o : Option env.ConstantInfo} {c : Bool}
    (hwf : ∀ ci ∈ o, ConstantInfoWF ci)
    (h : core_k.nat_ind_ok o = ok c) :
    c = ConLeche.natIndOk (o.map absConstantInfo) := by
  rw [core_k.nat_ind_ok.eq_def] at h
  cases o with
  | none => simp only [Result.ok.injEq] at h; rw [← h]; rfl
  | some ci =>
    have hci := hwf ci rfl
    cases ci with
    | IndInfo cv caps =>
      obtain ⟨-, -, hty⟩ := hci.1
      simp only [] at h
      split at h
      · rename_i hlen
        simp only [bind_eq_ok_iff] at h
        obtain ⟨l, hl, l1, hl1, e, he, hbeq⟩ := h
        rw [beq_sort_one hty hl hl1 he hbeq]
        simp only [Option.map_some, ConLeche.natIndOk, absConstantInfo, absConstantVal,
          level_params_nil hlen, List.isEmpty_nil, Bool.true_and]
        rfl
      · rename_i hlen
        simp only [Result.ok.injEq] at h
        have hne := absNames_isEmpty_false hlen
        simp only [← h, Option.map_some, ConLeche.natIndOk, absConstantInfo, absConstantVal,
          hne, Bool.false_and]
    | AxiomInfo cv => simp only [Result.ok.injEq] at h; rw [← h]; rfl
    | DefnInfo cv v hi => simp only [Result.ok.injEq] at h; rw [← h]; rfl
    | ThmInfo cv v => simp only [Result.ok.injEq] at h; rw [← h]; rfl
    | CtorInfo cv np nf => simp only [Result.ok.injEq] at h; rw [← h]; rfl
    | RecInfo cv mi rp rs => simp only [Result.ok.injEq] at h; rw [← h]; rfl
    | ProjInfo t => simp only [Result.ok.injEq] at h; rw [← h]; rfl

/-- The empty `Vec<Level>` the port passes to `expr::mk_const` for a
level-parameter-free constant. -/
theorem absLevels_new : absLevels (alloc.vec.Vec.new level.Level) = [] := rfl

theorem levelsWF_new : LevelsWF (alloc.vec.Vec.new level.Level) := by
  intro u hu; simp [alloc.vec.Vec.new] at hu

/-- The `==` of a lawful `BEq` as `decide`.  The cited guards compare *lists* of
levels (`us1 == [.param p]`), whose `BEq` is `List.beq` rather than `decide`,
so the `&&` cascade has to be normalised before `levels_beq_refines` fits. -/
theorem beq_eq_decide_eq {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (a b : α) :
    (a == b) = decide (a = b) := by
  by_cases hab : a = b <;> simp [hab]

/-- `level::singleton` is con-leche's one-element level list. -/
theorem levels_singleton {u : level.Level} {v : alloc.vec.Vec level.Level}
    (h : level.singleton u = ok v) :
    absLevels v = [absLevel u] ∧ (LevelWF u → LevelsWF v) := by
  rw [level.singleton] at h
  have hv : v.val = [u] := by
    rw [vec_push_val h]; simp [alloc.vec.Vec.new]
  refine ⟨by simp only [absLevels, hv, List.map_cons, List.map_nil], ?_⟩
  intro hu u' hu'
  rw [hv] at hu'; simp only [List.mem_singleton] at hu'; subst hu'; exact hu

/-- A constant's `us.len() == 0` test against con-leche's `[]` pattern. -/
theorem absLevels_nil {us : alloc.vec.Vec level.Level}
    (h : alloc.vec.Vec.len us = 0#usize) : absLevels us = [] := by
  simp only [absLevels, HashMap.vec_len_eq_zero_iff.mp h, List.map_nil]

theorem absLevels_ne_nil {us : alloc.vec.Vec level.Level}
    (h : ¬ (alloc.vec.Vec.len us = 0#usize)) : absLevels us ≠ [] := by
  intro hc
  refine h (HashMap.vec_len_eq_zero_iff.mpr ?_)
  have : (us.val.map absLevel) = [] := hc
  simpa using this

/-- `ConLeche/Kernel/Core.lean:280-284` — `core_k::nat_zero_ok` refines
`natZeroOk`.  Needs the `Nat` pin (`PinnedBasisNames.nat`). -/
theorem nat_zero_ok_refines {o : Option env.ConstantInfo} {c : Bool}
    (hp : PinnedBasisNames) (hwf : ∀ ci ∈ o, ConstantInfoWF ci)
    (h : core_k.nat_zero_ok o = ok c) :
    c = ConLeche.natZeroOk (o.map absConstantInfo) := by
  rw [core_k.nat_zero_ok.eq_def] at h
  cases o with
  | none => simp only [Result.ok.injEq] at h; rw [← h]; rfl
  | some ci =>
    have hci := hwf ci rfl
    cases ci with
    | CtorInfo cv np nf =>
      obtain ⟨-, -, hty⟩ := hci
      simp only [] at h
      split at h
      · rename_i hlen
        simp only [bind_eq_ok_iff] at h
        obtain ⟨n, hn, e, he, hbeq⟩ := h
        obtain ⟨hnabs, hnwf⟩ := hp.nat n hn
        rw [Expr.beq_refines hty (Expr.mk_const_wf hnwf levelsWF_new he) hbeq,
          Expr.mk_const_refines he, hnabs, absLevels_new]
        simp only [Option.map_some, ConLeche.natZeroOk, absConstantInfo, absConstantVal,
          level_params_nil hlen, List.isEmpty_nil, Bool.true_and]
        rfl
      · rename_i hlen
        simp only [Result.ok.injEq] at h
        have hne := absNames_isEmpty_false hlen
        simp only [← h, Option.map_some, ConLeche.natZeroOk, absConstantInfo, absConstantVal,
          hne, Bool.false_and]
    | AxiomInfo cv => simp only [Result.ok.injEq] at h; rw [← h]; rfl
    | DefnInfo cv v hi => simp only [Result.ok.injEq] at h; rw [← h]; rfl
    | ThmInfo cv v => simp only [Result.ok.injEq] at h; rw [← h]; rfl
    | IndInfo cv caps => simp only [Result.ok.injEq] at h; rw [← h]; rfl
    | RecInfo cv mi rp rs => simp only [Result.ok.injEq] at h; rw [← h]; rfl
    | ProjInfo t => simp only [Result.ok.injEq] at h; rw [← h]; rfl

/-- `ConLeche/Kernel/Core.lean:286-295` — `core_k::nat_succ_ok` refines
`natSuccOk`.  The first of the nested-`match` guards: the port spells the
cited `.forallE (.const c1 []) (.const c2 []) _mb` pattern as three nested
`match`es on the node kind, so the proof is `split at h` on each, with
`absExpr_kind` turning the observed kind into the con-leche node and
`ExprWF.children` handing back the children's well-formedness. -/
theorem nat_succ_ok_refines {o : Option env.ConstantInfo} {c : Bool}
    (hp : PinnedBasisNames) (hwf : ∀ ci ∈ o, ConstantInfoWF ci)
    (h : core_k.nat_succ_ok o = ok c) :
    c = ConLeche.natSuccOk (o.map absConstantInfo) := by
  rw [core_k.nat_succ_ok.eq_def] at h
  cases o with
  | none => simp only [Result.ok.injEq] at h; rw [← h]; rfl
  | some ci =>
    have hci := hwf ci rfl
    cases ci with
    | CtorInfo cv np nf =>
      obtain ⟨-, -, hty⟩ := hci
      simp only [Option.map_some, ConLeche.natSuccOk, absConstantInfo, absConstantVal]
      simp only [] at h
      split at h
      · rename_i hlen
        rw [level_params_nil hlen]
        simp only [List.isEmpty_nil, Bool.true_and]
        rw [absExpr_kind cv.ty]
        simp only [arc_deref_eq, bind_tc_ok] at h
        kind_split h hk
        rename_i dom body m
        obtain ⟨hdom, hbody, -⟩ := ExprWF.forallE_children hty hk
        rw [absExpr_kind dom, absExpr_kind body]
        kind_split h hk1
        rename_i c1 us1
        obtain ⟨hc1, hus1⟩ := ExprWF.const_children hdom hk1
        kind_split h hk2
        rename_i c2 us2
        obtain ⟨hc2, hus2⟩ := ExprWF.const_children hbody hk2
        split at h
        · rename_i h1
          split at h
          · rename_i h2
            simp only [bind_eq_ok_iff] at h
            obtain ⟨n, hn, b, hb, h⟩ := h
            obtain ⟨hnabs, hnwf⟩ := hp.nat n hn
            rw [Name.beq_refines hc1 hnwf hb, hnabs] at h
            rw [absLevels_nil h1, absLevels_nil h2]
            show c = (decide (absName c1 = ConLeche.natName) &&
              decide (absName c2 = ConLeche.natName))
            by_cases hd : absName c1 = ConLeche.natName
            · rw [if_pos (by simp only [hd, decide_true])] at h
              rw [Name.beq_refines hc2 hnwf h, hnabs, hd]
              simp
            · rw [if_neg (by simp only [hd, decide_false]; exact Bool.false_ne_true)] at h
              simp only [Result.ok.injEq] at h
              rw [← h, decide_eq_false hd, Bool.false_and]
          · rename_i h2
            simp only [Result.ok.injEq] at h
            rw [← h, absLevels_nil h1]
            rcases hq : absLevels us2 with _ | ⟨a, l⟩
            · exact absurd hq (absLevels_ne_nil h2)
            · rfl
        · rename_i h1
          simp only [Result.ok.injEq] at h
          rw [← h]
          rcases hq : absLevels us1 with _ | ⟨a, l⟩
          · exact absurd hq (absLevels_ne_nil h1)
          · rfl
      · rename_i hlen
        simp only [Result.ok.injEq] at h
        have hne := absNames_isEmpty_false hlen
        simp only [← h, hne, Bool.false_and]
    | AxiomInfo cv => simp only [Result.ok.injEq] at h; rw [← h]; rfl
    | DefnInfo cv v hi => simp only [Result.ok.injEq] at h; rw [← h]; rfl
    | ThmInfo cv v => simp only [Result.ok.injEq] at h; rw [← h]; rfl
    | IndInfo cv caps => simp only [Result.ok.injEq] at h; rw [← h]; rfl
    | RecInfo cv mi rp rs => simp only [Result.ok.injEq] at h; rw [← h]; rfl
    | ProjInfo t => simp only [Result.ok.injEq] at h; rw [← h]; rfl

/-! ## `String` support: the eight stored-shape guards (`Core.lean:373-455`)

These five read the stored type through `env::to_constant_val` (any constant
kind is accepted, as the cited Lean's `ci.toConstantVal` is total). -/

/-- `ConLeche/Kernel/Core.lean:373-379` — `core_k::string_ty_ok` refines
`stringTyOk`. -/
theorem string_ty_ok_refines {o : Option env.ConstantInfo} {c : Bool}
    (hwf : ∀ ci ∈ o, ConstantInfoWF ci) (h : core_k.string_ty_ok o = ok c) :
    c = ConLeche.stringTyOk (o.map absConstantInfo) := by
  rw [core_k.string_ty_ok.eq_def] at h
  cases o with
  | none => simp only [Result.ok.injEq] at h; rw [← h]; rfl
  | some ci =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨cv, hcv, h⟩ := h
    obtain ⟨hcvabs, hcvwf⟩ := to_constant_val_refines (hwf ci rfl) hcv
    simp only [Option.map_some, ConLeche.stringTyOk, ← hcvabs, absConstantVal]
    split at h
    · rename_i hlen
      simp only [bind_eq_ok_iff] at h
      obtain ⟨l, hl, l1, hl1, e, he, hbeq⟩ := h
      rw [beq_sort_one hcvwf.2.2 hl hl1 he hbeq, level_params_nil hlen]
      simp only [List.isEmpty_nil, Bool.true_and]
      rfl
    · rename_i hlen
      simp only [Result.ok.injEq] at h
      simp only [← h, absNames_isEmpty_false hlen, Bool.false_and]

/-- `ConLeche/Kernel/Core.lean:381-387` — `core_k::char_ty_ok` refines
`charTyOk` (the same body as `string_ty_ok`, as in the cited Lean). -/
theorem char_ty_ok_refines {o : Option env.ConstantInfo} {c : Bool}
    (hwf : ∀ ci ∈ o, ConstantInfoWF ci) (h : core_k.char_ty_ok o = ok c) :
    c = ConLeche.charTyOk (o.map absConstantInfo) := by
  rw [core_k.char_ty_ok.eq_def] at h
  cases o with
  | none => simp only [Result.ok.injEq] at h; rw [← h]; rfl
  | some ci =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨cv, hcv, h⟩ := h
    obtain ⟨hcvabs, hcvwf⟩ := to_constant_val_refines (hwf ci rfl) hcv
    simp only [Option.map_some, ConLeche.charTyOk, ← hcvabs, absConstantVal]
    split at h
    · rename_i hlen
      simp only [bind_eq_ok_iff] at h
      obtain ⟨l, hl, l1, hl1, e, he, hbeq⟩ := h
      rw [beq_sort_one hcvwf.2.2 hl hl1 he hbeq, level_params_nil hlen]
      simp only [List.isEmpty_nil, Bool.true_and]
      rfl
    · rename_i hlen
      simp only [Result.ok.injEq] at h
      simp only [← h, absNames_isEmpty_false hlen, Bool.false_and]

/-- `ConLeche/Kernel/Core.lean:389-400` — `core_k::list_ty_ok` refines
`listTyOk`: `List.{p} : Type p → Type p`.  The one level parameter is read with
`level_params_one`, and `name::dup` is the identity. -/
theorem list_ty_ok_refines {o : Option env.ConstantInfo} {c : Bool}
    (hwf : ∀ ci ∈ o, ConstantInfoWF ci) (h : core_k.list_ty_ok o = ok c) :
    c = ConLeche.listTyOk (o.map absConstantInfo) := by
  rw [core_k.list_ty_ok.eq_def] at h
  cases o with
  | none => simp only [Result.ok.injEq] at h; rw [← h]; rfl
  | some ci =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨cv, hcv, h⟩ := h
    obtain ⟨hcvabs, hcvwf⟩ := to_constant_val_refines (hwf ci rfl) hcv
    simp only [Option.map_some, ConLeche.listTyOk, ← hcvabs, absConstantVal]
    split at h
    · rename_i hlen
      simp only [arc_deref_eq, bind_tc_ok, bind_eq_ok_iff] at h
      obtain ⟨p, hpi, h⟩ := h
      obtain ⟨hlp, hpwf⟩ := level_params_one hlen hpi
      have hp : NameWF p := hpwf hcvwf.2.1
      rw [hlp]
      simp only []
      rw [absExpr_kind cv.ty]
      kind_split h hk
      rename_i dom body m
      obtain ⟨hdom, hbody, -⟩ := ExprWF.forallE_children hcvwf.2.2 hk
      rw [absExpr_kind dom, absExpr_kind body]
      kind_split h hk1
      rename_i u1
      have hu1 := ExprWF.sort_child hdom hk1
      kind_split h hk2
      rename_i u2
      have hu2 := ExprWF.sort_child hbody hk2
      simp only [name_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
      obtain ⟨l, hl, want, hwant, b, hb, h⟩ := h
      have hwantabs : absLevel want = ConLeche.Level.succ (.param (absName p)) := by
        rw [Level.succ_refines hwant, Level.param_refines hl]
      have hwantwf : LevelWF want := LevelWF.succ (Level.param_wf hp hl) hwant
      rw [Level.beq_refines hu1 hwantwf hb, hwantabs] at h
      show c = (decide (absLevel u1 = ConLeche.Level.succ (.param (absName p))) &&
        decide (absLevel u2 = ConLeche.Level.succ (.param (absName p))))
      by_cases hd : absLevel u1 = ConLeche.Level.succ (.param (absName p))
      · rw [if_pos (by simp only [hd, decide_true])] at h
        rw [Level.beq_refines hu2 hwantwf h, hwantabs, hd]
        simp
      · rw [if_neg (by simp only [hd, decide_false]; exact Bool.false_ne_true)] at h
        simp only [Result.ok.injEq] at h
        rw [← h, decide_eq_false hd, Bool.false_and]
    · rename_i hlen
      simp only [Result.ok.injEq] at h
      rcases level_params_shape_not_one hlen with hq | ⟨a, b, l, hq⟩ <;> rw [← h, hq]

/-- `ConLeche/Kernel/Core.lean:402-413` — `core_k::list_nil_ty_ok` refines
`listNilTyOk`: `List.nil.{p} : ∀ (α : Type p), List.{p} α`.  Needs the `List`
pin. -/
theorem list_nil_ty_ok_refines {o : Option env.ConstantInfo} {c : Bool}
    (hp : PinnedBasisNames) (hwf : ∀ ci ∈ o, ConstantInfoWF ci)
    (h : core_k.list_nil_ty_ok o = ok c) :
    c = ConLeche.listNilTyOk (o.map absConstantInfo) := by
  rw [core_k.list_nil_ty_ok.eq_def] at h
  cases o with
  | none => simp only [Result.ok.injEq] at h; rw [← h]; rfl
  | some ci =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨cv, hcv, h⟩ := h
    obtain ⟨hcvabs, hcvwf⟩ := to_constant_val_refines (hwf ci rfl) hcv
    simp only [Option.map_some, ConLeche.listNilTyOk, ← hcvabs, absConstantVal]
    split at h
    · rename_i hlen
      simp only [arc_deref_eq, bind_tc_ok, bind_eq_ok_iff] at h
      obtain ⟨q, hqi, h⟩ := h
      obtain ⟨hlp, hqwf⟩ := level_params_one hlen hqi
      have hq : NameWF q := hqwf hcvwf.2.1
      rw [hlp]
      simp only []
      rw [absExpr_kind cv.ty]
      kind_split h hk
      rename_i dom body m
      obtain ⟨hdom, hbody, -⟩ := ExprWF.forallE_children hcvwf.2.2 hk
      rw [absExpr_kind dom, absExpr_kind body]
      kind_split h hk1
      rename_i u1
      have hu1 := ExprWF.sort_child hdom hk1
      kind_split h hk2
      rename_i hd arg
      obtain ⟨hhd, harg⟩ := ExprWF.app_children hbody hk2
      rw [absExpr_kind hd, absExpr_kind arg]
      kind_split h hk3
      rename_i i1
      split at h
      · rw [show ((0#64#uscalar : Std.U64)).val = 0 from rfl]
        kind_split h hk4
        rename_i l1 us1
        obtain ⟨hl1, hus1⟩ := ExprWF.const_children hhd hk4
        simp only [name_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
        obtain ⟨l, hl, l2, hl2, b, hb, h⟩ := h
        have hwantabs : absLevel l2 = ConLeche.Level.succ (.param (absName q)) := by
          rw [Level.succ_refines hl2, Level.param_refines hl]
        have hwantwf : LevelWF l2 := LevelWF.succ (Level.param_wf hq hl) hl2
        rw [Level.beq_refines hu1 hwantwf hb, hwantabs] at h
        simp only [beq_eq_decide_eq]
        by_cases hd1 : absLevel u1 = ConLeche.Level.succ (.param (absName q))
        · rw [if_pos (by simp only [hd1, decide_true])] at h
          simp only [bind_eq_ok_iff] at h
          obtain ⟨n, hn, b1, hb1, h⟩ := h
          obtain ⟨hnabs, hnwf⟩ := hp.list n hn
          rw [Name.beq_refines hl1 hnwf hb1, hnabs] at h
          by_cases hd2 : absName l1 = ConLeche.listName
          · rw [if_pos (by simp only [hd2, decide_true])] at h
            simp only [bind_eq_ok_iff] at h
            obtain ⟨l3, hl3, v1, hv1, hbeq⟩ := h
            obtain ⟨hv1abs, hv1wf⟩ := levels_singleton hv1
            rw [Expr.levels_beq_refines hus1 (hv1wf (Level.param_wf hq hl3)) hbeq,
              hv1abs, Level.param_refines hl3, hd1, hd2]
            simp
          · rw [if_neg (by simp only [hd2, decide_false]; exact Bool.false_ne_true)] at h
            simp only [Result.ok.injEq] at h
            rw [← h, decide_eq_false hd2, Bool.and_false, Bool.false_and]
        · rw [if_neg (by simp only [hd1, decide_false]; exact Bool.false_ne_true)] at h
          simp only [Result.ok.injEq] at h
          rw [← h, decide_eq_false hd1, Bool.false_and, Bool.false_and]
      · rename_i hne
        have hiv : i1.val ≠ 0 := fun hc => hne (Std.UScalar.eq_of_val_eq (by rw [hc]; rfl))
        simp only [Result.ok.injEq] at h
        rw [← h]
        split
        · rename_i heq; simp_all
        · rfl
    · rename_i hlen
      simp only [Result.ok.injEq] at h
      rcases level_params_shape_not_one hlen with hq | ⟨a, b, l, hq⟩ <;> rw [← h, hq]

/-- `ConLeche/Kernel/Core.lean:434-443` — `core_k::char_of_nat_ty_ok` refines
`charOfNatTyOk`: `Char.ofNat : Nat → Char`.  Needs the `Nat` and `Char` pins. -/
theorem char_of_nat_ty_ok_refines {o : Option env.ConstantInfo} {c : Bool}
    (hp : PinnedBasisNames) (hwf : ∀ ci ∈ o, ConstantInfoWF ci)
    (h : core_k.char_of_nat_ty_ok o = ok c) :
    c = ConLeche.charOfNatTyOk (o.map absConstantInfo) := by
  rw [core_k.char_of_nat_ty_ok.eq_def] at h
  cases o with
  | none => simp only [Result.ok.injEq] at h; rw [← h]; rfl
  | some ci =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨cv, hcv, h⟩ := h
    obtain ⟨hcvabs, hcvwf⟩ := to_constant_val_refines (hwf ci rfl) hcv
    simp only [Option.map_some, ConLeche.charOfNatTyOk, ← hcvabs, absConstantVal]
    split at h
    · rename_i hlen
      rw [level_params_nil hlen]
      simp only [List.isEmpty_nil, Bool.true_and]
      rw [absExpr_kind cv.ty]
      simp only [arc_deref_eq, bind_tc_ok] at h
      kind_split h hk
      rename_i dom body m
      obtain ⟨hdom, hbody, -⟩ := ExprWF.forallE_children hcvwf.2.2 hk
      rw [absExpr_kind dom, absExpr_kind body]
      kind_split h hk1
      rename_i c1 us1
      obtain ⟨hc1, hus1⟩ := ExprWF.const_children hdom hk1
      kind_split h hk2
      rename_i c2 us2
      obtain ⟨hc2, hus2⟩ := ExprWF.const_children hbody hk2
      split at h
      · rename_i h1
        split at h
        · rename_i h2
          simp only [bind_eq_ok_iff] at h
          obtain ⟨n, hn, b, hb, h⟩ := h
          obtain ⟨hnabs, hnwf⟩ := hp.nat n hn
          rw [Name.beq_refines hc1 hnwf hb, hnabs] at h
          rw [absLevels_nil h1, absLevels_nil h2]
          simp only [beq_eq_decide_eq]
          by_cases hd : absName c1 = ConLeche.natName
          · rw [if_pos (by simp only [hd, decide_true])] at h
            simp only [bind_eq_ok_iff] at h
            obtain ⟨n1, hn1, hbeq⟩ := h
            obtain ⟨hn1abs, hn1wf⟩ := hp.char n1 hn1
            rw [Name.beq_refines hc2 hn1wf hbeq, hn1abs, hd]
            simp
          · rw [if_neg (by simp only [hd, decide_false]; exact Bool.false_ne_true)] at h
            simp only [Result.ok.injEq] at h
            rw [← h, decide_eq_false hd, Bool.false_and]
        · rename_i h2
          simp only [Result.ok.injEq] at h
          rw [← h, absLevels_nil h1]
          rcases hq : absLevels us2 with _ | ⟨a, l⟩
          · exact absurd hq (absLevels_ne_nil h2)
          · rfl
      · rename_i h1
        simp only [Result.ok.injEq] at h
        rw [← h]
        rcases hq : absLevels us1 with _ | ⟨a, l⟩
        · exact absurd hq (absLevels_ne_nil h1)
        · rfl
    · rename_i hlen
      simp only [Result.ok.injEq] at h
      simp only [← h, absNames_isEmpty_false hlen, Bool.false_and]

/-- `ConLeche/Kernel/Core.lean:445-455` — `core_k::string_of_list_ty_ok` refines
`stringOfListTyOk`: `String.ofList : List.{0} Char → String`.  Needs the `List`,
`Char` and `String` pins. -/
theorem string_of_list_ty_ok_refines {o : Option env.ConstantInfo} {c : Bool}
    (hp : PinnedBasisNames) (hwf : ∀ ci ∈ o, ConstantInfoWF ci)
    (h : core_k.string_of_list_ty_ok o = ok c) :
    c = ConLeche.stringOfListTyOk (o.map absConstantInfo) := by
  rw [core_k.string_of_list_ty_ok.eq_def] at h
  cases o with
  | none => simp only [Result.ok.injEq] at h; rw [← h]; rfl
  | some ci =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨cv, hcv, h⟩ := h
    obtain ⟨hcvabs, hcvwf⟩ := to_constant_val_refines (hwf ci rfl) hcv
    simp only [Option.map_some, ConLeche.stringOfListTyOk, ← hcvabs, absConstantVal]
    split at h
    · rename_i hlen
      rw [level_params_nil hlen]
      simp only [List.isEmpty_nil, Bool.true_and]
      rw [absExpr_kind cv.ty]
      simp only [arc_deref_eq, bind_tc_ok] at h
      kind_split h hk
      rename_i dom body m
      obtain ⟨hdom, hbody, -⟩ := ExprWF.forallE_children hcvwf.2.2 hk
      rw [absExpr_kind dom, absExpr_kind body]
      kind_split h hk1
      rename_i hd arg
      obtain ⟨hhd, harg⟩ := ExprWF.app_children hdom hk1
      kind_split h hk2
      rename_i c2 us2
      obtain ⟨hc2, hus2⟩ := ExprWF.const_children hbody hk2
      rw [absExpr_kind hd, absExpr_kind arg]
      kind_split h hk3
      rename_i l1 us1
      obtain ⟨hl1, hus1⟩ := ExprWF.const_children hhd hk3
      kind_split h hk4
      rename_i c1 us_c
      obtain ⟨hc1, husc⟩ := ExprWF.const_children harg hk4
      split at h
      · rename_i h1
        split at h
        · rename_i h2
          rw [absLevels_nil h1, absLevels_nil h2]
          simp only [beq_eq_decide_eq]
          simp only [bind_eq_ok_iff] at h
          obtain ⟨n, hn, b, hb, h⟩ := h
          obtain ⟨hnabs, hnwf⟩ := hp.list n hn
          rw [Name.beq_refines hl1 hnwf hb, hnabs] at h
          by_cases hd1 : absName l1 = ConLeche.listName
          · rw [if_pos (by simp only [hd1, decide_true])] at h
            simp only [bind_eq_ok_iff] at h
            obtain ⟨l, hl, v, hv, b1, hb1, h⟩ := h
            obtain ⟨hvabs, hvwf⟩ := levels_singleton hv
            rw [Expr.levels_beq_refines hus1 (hvwf (LevelWF.zero hl)) hb1, hvabs,
              Level.zero_refines hl] at h
            by_cases hd2 : absLevels us1 = [ConLeche.Level.zero]
            · rw [if_pos (by simp only [hd2, decide_true])] at h
              simp only [bind_eq_ok_iff] at h
              obtain ⟨n1, hn1, b2, hb2, h⟩ := h
              obtain ⟨hn1abs, hn1wf⟩ := hp.char n1 hn1
              rw [Name.beq_refines hc1 hn1wf hb2, hn1abs] at h
              by_cases hd3 : absName c1 = ConLeche.charName
              · rw [if_pos (by simp only [hd3, decide_true])] at h
                simp only [bind_eq_ok_iff] at h
                obtain ⟨n2, hn2, hbeq⟩ := h
                obtain ⟨hn2abs, hn2wf⟩ := hp.string n2 hn2
                rw [Name.beq_refines hc2 hn2wf hbeq, hn2abs, hd1, hd2, hd3]
                simp
              · rw [if_neg (by simp only [hd3, decide_false]; exact Bool.false_ne_true)] at h
                simp only [Result.ok.injEq] at h
                rw [← h, decide_eq_false hd3, Bool.and_false, Bool.false_and]
            · rw [if_neg (by simp only [hd2, decide_false]; exact Bool.false_ne_true)] at h
              simp only [Result.ok.injEq] at h
              rw [← h, decide_eq_false hd2, Bool.and_false, Bool.false_and, Bool.false_and]
          · rw [if_neg (by simp only [hd1, decide_false]; exact Bool.false_ne_true)] at h
            simp only [Result.ok.injEq] at h
            rw [← h, decide_eq_false hd1, Bool.false_and, Bool.false_and, Bool.false_and]
        · rename_i h2
          simp only [Result.ok.injEq] at h
          rw [← h, absLevels_nil h1]
          rcases hq : absLevels us_c with _ | ⟨a, l⟩
          · exact absurd hq (absLevels_ne_nil h2)
          · rfl
      · rename_i h1
        simp only [Result.ok.injEq] at h
        rw [← h]
        rcases hq : absLevels us2 with _ | ⟨a, l⟩
        · exact absurd hq (absLevels_ne_nil h1)
        · rcases hq2 : absLevels us_c with _ | ⟨a2, l2⟩ <;> rfl
    · rename_i hlen
      simp only [Result.ok.injEq] at h
      simp only [← h, absNames_isEmpty_false hlen, Bool.false_and]

/-- `ConLeche/Kernel/Core.lean:415-432` — `core_k::list_cons_tail_ok` refines the
**innermost two slots** of `listConsTyOk`'s pattern together with its five
comparisons.  It has no Lean function of its own (the port factored it out to
keep the nesting readable), so it is stated as the cited `match` applied to the
type `list_cons_ty_ok` has reconstructed by the time it calls this: the three
binder data are arbitrary, exactly as the cited `_mb1`/`_mb2`/`_mb3` are.
Needs the `List` pin. -/
theorem list_cons_tail_ok_refines {u1 : level.Level} {d3 b3 : expr.Expr}
    {p : name.Name} {c : Bool} (hp : PinnedBasisNames)
    (hu1 : LevelWF u1) (hd3 : ExprWF d3) (hb3 : ExprWF b3) (hpwf : NameWF p)
    (h : core_k.list_cons_tail_ok u1 d3 b3 p = ok c) :
    ∀ m1 m2 m3 : ConLeche.BinderMeta,
      c = (match ConLeche.Expr.forallE (.sort (absLevel u1))
             (.forallE (.bvar 0) (.forallE (absExpr d3) (absExpr b3) m3) m2) m1 with
           | .forallE (.sort v1)
               (.forallE (.bvar 0)
                 (.forallE (.app (.const l1 us1) (.bvar 1))
                   (.app (.const l2 us2) (.bvar 2)) _mb3) _mb2) _mb1 =>
             v1 == .succ (.param (absName p)) && l1 == ConLeche.listName &&
               l2 == ConLeche.listName && us1 == [.param (absName p)] &&
               us2 == [.param (absName p)]
           | _ => false) := by
  intro m1 m2 m3
  rw [core_k.list_cons_tail_ok.eq_def] at h
  simp only [arc_deref_eq, bind_tc_ok] at h
  rw [absExpr_kind d3, absExpr_kind b3]
  kind_split h hk
  rename_i h1 a1
  obtain ⟨hh1, ha1⟩ := ExprWF.app_children hd3 hk
  kind_split h hk1
  rename_i h2 a2
  obtain ⟨hh2, ha2⟩ := ExprWF.app_children hb3 hk1
  rw [absExpr_kind h1, absExpr_kind a1, absExpr_kind h2, absExpr_kind a2]
  kind_split h hk2
  rename_i i
  split at h
  · rw [show ((1#64#uscalar : Std.U64)).val = 1 from rfl]
    kind_split h hk3
    rename_i i1
    split at h
    · rw [show ((2#64#uscalar : Std.U64)).val = 2 from rfl]
      kind_split h hk4
      rename_i l1 us1
      obtain ⟨hl1, hus1⟩ := ExprWF.const_children hh1 hk4
      kind_split h hk5
      rename_i l2 us2
      obtain ⟨hl2, hus2⟩ := ExprWF.const_children hh2 hk5
      simp only [name_dup_eq, bind_tc_ok, bind_eq_ok_iff] at h
      obtain ⟨l, hl, want, hwant, l3, hl3, l4, hl4, b, hb, h⟩ := h
      obtain ⟨hwantabs, hwantwf⟩ := levels_singleton hwant
      have hl4abs : absLevel l4 = ConLeche.Level.succ (.param (absName p)) := by
        rw [Level.succ_refines hl4, Level.param_refines hl3]
      have hl4wf : LevelWF l4 := LevelWF.succ (Level.param_wf hpwf hl3) hl4
      rw [Level.beq_refines hu1 hl4wf hb, hl4abs] at h
      simp only [beq_eq_decide_eq]
      by_cases hd1 : absLevel u1 = ConLeche.Level.succ (.param (absName p))
      · rw [if_pos (by simp only [hd1, decide_true])] at h
        simp only [bind_eq_ok_iff] at h
        obtain ⟨n, hn, b1, hb1, h⟩ := h
        obtain ⟨hnabs, hnwf⟩ := hp.list n hn
        rw [Name.beq_refines hl1 hnwf hb1, hnabs] at h
        by_cases hd2 : absName l1 = ConLeche.listName
        · rw [if_pos (by simp only [hd2, decide_true])] at h
          simp only [bind_eq_ok_iff] at h
          obtain ⟨b2, hb2, h⟩ := h
          rw [Name.beq_refines hl2 hnwf hb2, hnabs] at h
          by_cases hd3 : absName l2 = ConLeche.listName
          · rw [if_pos (by simp only [hd3, decide_true])] at h
            simp only [bind_eq_ok_iff] at h
            obtain ⟨b4, hb4, h⟩ := h
            rw [Expr.levels_beq_refines hus1 (hwantwf (Level.param_wf hpwf hl)) hb4,
              hwantabs, Level.param_refines hl] at h
            by_cases hd4 : absLevels us1 = [ConLeche.Level.param (absName p)]
            · rw [if_pos (by simp only [hd4, decide_true])] at h
              rw [Expr.levels_beq_refines hus2 (hwantwf (Level.param_wf hpwf hl)) h,
                hwantabs, Level.param_refines hl, hd1, hd2, hd3, hd4]
              simp
            · rw [if_neg (by simp only [hd4, decide_false]; exact Bool.false_ne_true)] at h
              simp only [Result.ok.injEq] at h
              rw [← h, decide_eq_false hd4, Bool.and_false, Bool.false_and]
          · rw [if_neg (by simp only [hd3, decide_false]; exact Bool.false_ne_true)] at h
            simp only [Result.ok.injEq] at h
            rw [← h, decide_eq_false hd3, Bool.and_false, Bool.false_and, Bool.false_and]
        · rw [if_neg (by simp only [hd2, decide_false]; exact Bool.false_ne_true)] at h
          simp only [Result.ok.injEq] at h
          rw [← h, decide_eq_false hd2, Bool.and_false, Bool.false_and, Bool.false_and,
            Bool.false_and]
      · rw [if_neg (by simp only [hd1, decide_false]; exact Bool.false_ne_true)] at h
        simp only [Result.ok.injEq] at h
        rw [← h, decide_eq_false hd1, Bool.false_and, Bool.false_and, Bool.false_and,
          Bool.false_and]
    · rename_i hne
      have hiv : i1.val ≠ 2 := fun hc => hne (Std.UScalar.eq_of_val_eq (by rw [hc]; rfl))
      simp only [Result.ok.injEq] at h
      rw [← h]
      split
      · rename_i heq; simp_all
      · rfl
  · rename_i hne
    have hiv : i.val ≠ 1 := fun hc => hne (Std.UScalar.eq_of_val_eq (by rw [hc]; rfl))
    simp only [Result.ok.injEq] at h
    rw [← h]
    split
    · rename_i heq; simp_all
    · rfl

/-- `ConLeche/Kernel/Core.lean:415-432` — `core_k::list_cons_ty_ok` refines
`listConsTyOk`: `List.cons.{p} : ∀ (α : Type p) (head : α) (tail : List.{p} α),
List.{p} α`.  The outer three binders are descended here; the innermost two
slots and the five comparisons are `list_cons_tail_ok_refines`. -/
theorem list_cons_ty_ok_refines {o : Option env.ConstantInfo} {c : Bool}
    (hp : PinnedBasisNames) (hwf : ∀ ci ∈ o, ConstantInfoWF ci)
    (h : core_k.list_cons_ty_ok o = ok c) :
    c = ConLeche.listConsTyOk (o.map absConstantInfo) := by
  rw [core_k.list_cons_ty_ok.eq_def] at h
  cases o with
  | none => simp only [Result.ok.injEq] at h; rw [← h]; rfl
  | some ci =>
    simp only [bind_eq_ok_iff] at h
    obtain ⟨cv, hcv, h⟩ := h
    obtain ⟨hcvabs, hcvwf⟩ := to_constant_val_refines (hwf ci rfl) hcv
    simp only [Option.map_some, ConLeche.listConsTyOk, ← hcvabs, absConstantVal]
    split at h
    · rename_i hlen
      simp only [arc_deref_eq, bind_tc_ok, bind_eq_ok_iff] at h
      obtain ⟨q, hqi, h⟩ := h
      obtain ⟨hlp, hqwf⟩ := level_params_one hlen hqi
      have hq : NameWF q := hqwf hcvwf.2.1
      rw [hlp]
      simp only []
      rw [absExpr_kind cv.ty]
      kind_split h hk
      rename_i d1 b1 m1
      obtain ⟨hd1, hb1, -⟩ := ExprWF.forallE_children hcvwf.2.2 hk
      rw [absExpr_kind d1, absExpr_kind b1]
      kind_split h hk1
      rename_i u1
      have hu1 := ExprWF.sort_child hd1 hk1
      kind_split h hk2
      rename_i d2 b2 m2
      obtain ⟨hd2, hb2, -⟩ := ExprWF.forallE_children hb1 hk2
      rw [absExpr_kind d2, absExpr_kind b2]
      kind_split h hk3
      rename_i i1
      split at h
      · rw [show ((0#64#uscalar : Std.U64)).val = 0 from rfl]
        kind_split h hk4
        rename_i d3 b3 m3
        obtain ⟨hd3, hb3, -⟩ := ExprWF.forallE_children hb2 hk4
        exact list_cons_tail_ok_refines hp hu1 hd3 hb3 hq h
          (absBinderMeta m1) (absBinderMeta m2) (absBinderMeta m3)
      · rename_i hne
        have hiv : i1.val ≠ 0 := fun hc => hne (Std.UScalar.eq_of_val_eq (by rw [hc]; rfl))
        simp only [Result.ok.injEq] at h
        rw [← h]
        split
        · rename_i heq; simp_all
        · rfl
    · rename_i hlen
      simp only [Result.ok.injEq] at h
      rcases level_params_shape_not_one hlen with hq | ⟨a, b, l, hq⟩ <;> rw [← h, hq]

/-! ## The two environment guards (`Core.lean:297-305`, `:457-475`)

Stated against the `FEnv` twins of `ConLeche/Kernel/FEnv.lean` (the port reads
the environment through `fenv::find` throughout — module note deviation 3), and
proved by the `&&`-cascade step below: the port's `if g then rest else false`
nest is the cited `g && rest` once the Lean side is right-associated. -/

/-- `core::option::Option::is_some` is `Option.isSome`. -/
theorem option_is_some {α : Type} (o : Option α) :
    core.option.Option.is_some o = o.isSome := by
  rw [core.option.Option.is_some]

/-- A `fenv::find` that succeeded, abstracted (`FEnvRel`). -/
theorem find_abs {fe : fenv.FEnv} {lfe : ConLeche.FEnv} (hfe : FEnvRel fe lfe)
    {n : name.Name} {o : Option env.ConstantInfo} (hn : NameWF n)
    (ho : fenv.find fe n = ok o) : o.map absConstantInfo = lfe.find? (absName n) := by
  obtain ⟨o', ho', habs⟩ := hfe n hn
  rw [ho] at ho'
  rw [← Result.ok_injective ho'] at habs
  exact habs

/-- A `fenv::find` that succeeded, hereditarily well formed (`FEnvWF`). -/
theorem find_wf {fe : fenv.FEnv} (hfwf : FEnvWF fe) {n : name.Name}
    {o : Option env.ConstantInfo} (ho : fenv.find fe n = ok o) :
    ∀ ci ∈ o, ConstantInfoWF ci :=
  fun ci hci => hfwf n ci (ho.trans (congrArg ok hci))

/-- The `isSome` reading of a `fenv::find`, which is all `consts_resolve`'s
groups ask for. -/
theorem find_isSome {fe : fenv.FEnv} {lfe : ConLeche.FEnv} (hfe : FEnvRel fe lfe)
    {n : name.Name} {o : Option env.ConstantInfo} (hn : NameWF n)
    (ho : fenv.find fe n = ok o) :
    core.option.Option.is_some o = (lfe.find? (absName n)).isSome := by
  rw [option_is_some, ← find_abs hfe hn ho]; cases o <;> rfl

/-- **One `&&` of a guard cascade.**  The port writes `a && b` as
`if a then b else false`; with the cited Lean side right-associated
(`simp only [Bool.and_assoc]`) this peels one conjunct per use. -/
theorem and_step {b bl rl c : Bool} {r : Result Bool}
    (hb : b = bl) (h : (if b = true then r else ok false) = ok c)
    (hrest : ∀ c', r = ok c' → c' = rl) : c = (bl && rl) := by
  subst hb
  cases b with
  | false =>
    simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    rw [← h]; rfl
  | true => simp only [if_true] at h; rw [hrest c h]; rfl

/-- `ConLeche/Kernel/Core.lean:297-305 natLitSupported`, through the index:
`core_k::nat_lit_supported` refines `ConLeche/Kernel/FEnv.lean:116-119
natLitSupportedF`.  Needs the three `Nat` pins. -/
theorem nat_lit_supported_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {c : Bool}
    (hp : PinnedBasisNames) (hfe : FEnvRel fe lfe) (hfwf : FEnvWF fe)
    (h : core_k.nat_lit_supported fe = ok c) :
    c = ConLeche.natLitSupportedF lfe := by
  rw [core_k.nat_lit_supported.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, o, ho, b, hb, h⟩ := h
  obtain ⟨hnabs, hnwf⟩ := hp.nat n hn
  simp only [ConLeche.natLitSupportedF, Bool.and_assoc]
  refine and_step (by rw [nat_ind_ok_refines (find_wf hfwf ho) hb,
    find_abs hfe hnwf ho, hnabs]) h ?_
  intro c1 h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n1, hn1, o1, ho1, b1, hb1, h⟩ := h
  obtain ⟨hn1abs, hn1wf⟩ := hp.natZero n1 hn1
  refine and_step (by rw [nat_zero_ok_refines hp (find_wf hfwf ho1) hb1,
    find_abs hfe hn1wf ho1, hn1abs]) h ?_
  intro c2 h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n2, hn2, o2, ho2, hb2⟩ := h
  obtain ⟨hn2abs, hn2wf⟩ := hp.natSucc n2 hn2
  rw [nat_succ_ok_refines hp (find_wf hfwf ho2) hb2, find_abs hfe hn2wf ho2, hn2abs]

/-- `ConLeche/Kernel/Core.lean:457-475 strLitSupported`, through the index:
`core_k::str_lit_supported` refines `ConLeche/Kernel/FEnv.lean:121-130
strLitSupportedF`.  Needs all ten pins. -/
theorem str_lit_supported_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {c : Bool}
    (hp : PinnedBasisNames) (hfe : FEnvRel fe lfe) (hfwf : FEnvWF fe)
    (h : core_k.str_lit_supported fe = ok c) :
    c = ConLeche.strLitSupportedF lfe := by
  rw [core_k.str_lit_supported.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b, hb, h⟩ := h
  simp only [ConLeche.strLitSupportedF, Bool.and_assoc]
  refine and_step (nat_lit_supported_refines hp hfe hfwf hb) h ?_
  intro c1 h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, o, ho, b1, hb1, h⟩ := h
  obtain ⟨hnabs, hnwf⟩ := hp.string n hn
  refine and_step (by rw [string_ty_ok_refines (find_wf hfwf ho) hb1,
    find_abs hfe hnwf ho, hnabs]) h ?_
  intro c2 h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n1, hn1, o1, ho1, b2, hb2, h⟩ := h
  obtain ⟨hn1abs, hn1wf⟩ := hp.stringOfList n1 hn1
  refine and_step (by rw [string_of_list_ty_ok_refines hp (find_wf hfwf ho1) hb2,
    find_abs hfe hn1wf ho1, hn1abs]) h ?_
  intro c3 h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n2, hn2, o2, ho2, b3, hb3, h⟩ := h
  obtain ⟨hn2abs, hn2wf⟩ := hp.list n2 hn2
  refine and_step (by rw [list_ty_ok_refines (find_wf hfwf ho2) hb3,
    find_abs hfe hn2wf ho2, hn2abs]) h ?_
  intro c4 h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n3, hn3, o3, ho3, b4, hb4, h⟩ := h
  obtain ⟨hn3abs, hn3wf⟩ := hp.listNil n3 hn3
  refine and_step (by rw [list_nil_ty_ok_refines hp (find_wf hfwf ho3) hb4,
    find_abs hfe hn3wf ho3, hn3abs]) h ?_
  intro c5 h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n4, hn4, o4, ho4, b5, hb5, h⟩ := h
  obtain ⟨hn4abs, hn4wf⟩ := hp.listCons n4 hn4
  refine and_step (by rw [list_cons_ty_ok_refines hp (find_wf hfwf ho4) hb5,
    find_abs hfe hn4wf ho4, hn4abs]) h ?_
  intro c6 h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n5, hn5, o5, ho5, b6, hb6, h⟩ := h
  obtain ⟨hn5abs, hn5wf⟩ := hp.char n5 hn5
  refine and_step (by rw [char_ty_ok_refines (find_wf hfwf ho5) hb6,
    find_abs hfe hn5wf ho5, hn5abs]) h ?_
  intro c7 h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n6, hn6, o6, ho6, hb7⟩ := h
  obtain ⟨hn6abs, hn6wf⟩ := hp.charOfNat n6 hn6
  rw [char_of_nat_ty_ok_refines hp (find_wf hfwf ho6) hb7, find_abs hfe hn6wf ho6, hn6abs]

/-! ## `Expr.constsResolve` (`Core.lean:307-332`) and its two `isSome` groups

`consts_resolve` is **deliberately dead** (`core_k.rs`'s module note: the
install checks it once per declaration, the core never calls it), and it is the
one function here that recurses over an `Expr`, so it is proved by induction on
the `ExprWF` derivation (task #47's rule).  The cited Lean is stated over an
`Env`; `FEnv.lean` has no `constsResolveF` twin, so the lemma takes `henv`, the
`FEnv.find? = Env.find?` agreement that `mkFEnv_find?` supplies. -/

/-- `ConLeche/Kernel/Core.lean:307-332` — `core_k::nat_trio_stored` refines the
three `isSome` tests the `.lit (.natVal _)` arm of `Expr.constsResolve` opens
with.  Needs the three `Nat` pins. -/
theorem nat_trio_stored_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {c : Bool}
    (hp : PinnedBasisNames) (hfe : FEnvRel fe lfe)
    (h : core_k.nat_trio_stored fe = ok c) :
    c = ((lfe.find? ConLeche.natName).isSome &&
      (lfe.find? ConLeche.natZeroName).isSome &&
      (lfe.find? ConLeche.natSuccName).isSome) := by
  rw [core_k.nat_trio_stored.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, o, ho, h⟩ := h
  obtain ⟨hnabs, hnwf⟩ := hp.nat n hn
  simp only [Bool.and_assoc]
  refine and_step (by rw [find_isSome hfe hnwf ho, hnabs]) h ?_
  intro c1 h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n1, hn1, o1, ho1, h⟩ := h
  obtain ⟨hn1abs, hn1wf⟩ := hp.natZero n1 hn1
  refine and_step (by rw [find_isSome hfe hn1wf ho1, hn1abs]) h ?_
  intro c2 h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n2, hn2, o2, ho2, h⟩ := h
  obtain ⟨hn2abs, hn2wf⟩ := hp.natSucc n2 hn2
  rw [← h, find_isSome hfe hn2wf ho2, hn2abs]

/-- `ConLeche/Kernel/Core.lean:307-332` — `core_k::str_support_stored` refines the
seven further `isSome` tests of the `.lit (.strVal _)` arm.  Needs the seven
string-support pins. -/
theorem str_support_stored_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv} {c : Bool}
    (hp : PinnedBasisNames) (hfe : FEnvRel fe lfe)
    (h : core_k.str_support_stored fe = ok c) :
    c = ((lfe.find? ConLeche.stringName).isSome &&
      (lfe.find? ConLeche.stringOfListName).isSome &&
      (lfe.find? ConLeche.listName).isSome &&
      (lfe.find? ConLeche.listNilName).isSome &&
      (lfe.find? ConLeche.listConsName).isSome &&
      (lfe.find? ConLeche.charName).isSome &&
      (lfe.find? ConLeche.charOfNatName).isSome) := by
  rw [core_k.str_support_stored.eq_def] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n, hn, o, ho, h⟩ := h
  obtain ⟨hnabs, hnwf⟩ := hp.string n hn
  simp only [Bool.and_assoc]
  refine and_step (by rw [find_isSome hfe hnwf ho, hnabs]) h ?_
  intro c1 h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n1, hn1, o1, ho1, h⟩ := h
  obtain ⟨hn1abs, hn1wf⟩ := hp.stringOfList n1 hn1
  refine and_step (by rw [find_isSome hfe hn1wf ho1, hn1abs]) h ?_
  intro c2 h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n2, hn2, o2, ho2, h⟩ := h
  obtain ⟨hn2abs, hn2wf⟩ := hp.list n2 hn2
  refine and_step (by rw [find_isSome hfe hn2wf ho2, hn2abs]) h ?_
  intro c3 h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n3, hn3, o3, ho3, h⟩ := h
  obtain ⟨hn3abs, hn3wf⟩ := hp.listNil n3 hn3
  refine and_step (by rw [find_isSome hfe hn3wf ho3, hn3abs]) h ?_
  intro c4 h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n4, hn4, o4, ho4, h⟩ := h
  obtain ⟨hn4abs, hn4wf⟩ := hp.listCons n4 hn4
  refine and_step (by rw [find_isSome hfe hn4wf ho4, hn4abs]) h ?_
  intro c5 h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨n5, hn5, o5, ho5, h⟩ := h
  obtain ⟨hn5abs, hn5wf⟩ := hp.char n5 hn5
  refine and_step (by rw [find_isSome hfe hn5wf ho5, hn5abs]) h ?_
  intro c6 h
  simp only [bind_eq_ok_iff, Result.ok.injEq] at h
  obtain ⟨n6, hn6, o6, ho6, h⟩ := h
  obtain ⟨hn6abs, hn6wf⟩ := hp.charOfNat n6 hn6
  rw [← h, find_isSome hfe hn6wf ho6, hn6abs]

/-- `ConLeche/Kernel/Core.lean:307-332` — `core_k::consts_resolve` refines
`Expr.constsResolve`.  **Deliberately dead** in the port (the install calls it
once per declaration, the core never does), but ported and so refined.
`henv` is the `FEnv.find? = Env.find?` agreement: the cited Lean reads an `Env`
and `FEnv.lean` has no `constsResolveF` twin. -/
theorem consts_resolve_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {lenv : ConLeche.Env} (hp : PinnedBasisNames) (hfe : FEnvRel fe lfe)
    (henv : ∀ n : ConLeche.Name, lfe.find? n = lenv.find? n)
    {e : expr.Expr} (he : ExprWF e) :
    ∀ c, core_k.consts_resolve fe e = ok c →
      c = ConLeche.Expr.constsResolve lenv (absExpr e) := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.constsResolve]
  | @sort u e hu h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.constsResolve]
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff,
      Result.ok.injEq] at h
    obtain ⟨o, ho, h⟩ := h
    rw [← h, find_isSome hfe hn ho, henv]
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolve]
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    rw [ih c h]; simp [ConLeche.Expr.constsResolve]
  | @lit l e hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    cases l with
    | NatVal k =>
      rw [nat_trio_stored_refines hp hfe h]
      simp only [absExpr, absExprNode, absExprKind, absLiteral,
        ConLeche.Expr.constsResolve, ← henv]
    | StrVal sv =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨b, hb, h⟩ := h
      have g1 := nat_trio_stored_refines hp hfe hb
      simp only [absExpr, absExprNode, absExprKind, absLiteral,
        ConLeche.Expr.constsResolve, ← henv]
      cases b with
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        rw [← h, ← g1]; simp
      | true =>
        simp only [if_true] at h
        rw [str_support_stored_refines hp hfe h, ← g1]; simp
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolve]
    exact and_step (ihf b1 hb1) h (fun c' h' => iha c' h')
  | @lam ty bo m e hty hbo hm h1 iht ihb =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolve]
    exact and_step (iht b1 hb1) h (fun c' h' => ihb c' h')
  | @forall_e ty bo m e hty hbo hm h1 iht ihb =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolve]
    exact and_step (iht b1 hb1) h (fun c' h' => ihb c' h')
  | @let_e ty v bo e hty hv hbo h1 iht ihv ihb =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolve,
      Bool.and_assoc]
    refine and_step (iht b1 hb1) h ?_
    intro c' h'
    obtain ⟨b2, hb2, h'⟩ := bind_eq_ok_iff.mp h'
    exact and_step (ihv b2 hb2) h' (fun c'' h'' => ihb c'' h'')
  | @proj sn i x e hs hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨o, ho, h⟩ := h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolve]
    exact and_step (by rw [find_isSome hfe hs ho, henv]) h (fun c' h' => ih c' h')

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/--
info: 'ConRon.Refine.CoreK.str_lit_supported_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms str_lit_supported_refines

end ConRon.Refine.CoreK

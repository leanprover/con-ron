/-
`CORE_PLAN.md` step 4, the shared foundation (task #49): the plumbing the
refinement of `kernel/core_k.rs`, `kernel/prop_read.rs` and
`kernel/basis_names.rs` needs before any of their functions can be stated.

Two things live here and nowhere else in the `CoreK*` family:

* **`core_types::code_points`**, the port's spelling of a Lean string literal
  (DESIGN.md §3.3): `code_points_val` says the copy is the slice, and
  `str_lit_step`/`num_lit_step` package the two-or-three-bind body that every
  pinned name in `basis_names.rs` and `core_k.rs` has.
* **`FindAgree`/`FindWF`**, the *find-agreement* projection of task #46's
  `FEnv.FEnvRel`/`FEnv.FEnvWF`, with the two bridge lemmas.  `core_k.rs` and
  `prop_read.rs` read the environment only through `fenv::find` and
  `fenv::find_proj`, so find-agreement is the whole of the relation they
  depend on, and stating step 4 over it rather than over the full three-clause
  relation makes the step's theorems stronger.  The section below says why at
  length; `PinnedName`/`PinnedNames`, the statement of a pinned name and of a
  pinned name table, are there too.
-/
import ConRon.Generated
import ConRon.Refine.Abs
import ConRon.Refine.Name
import ConRon.Refine.Level
import ConRon.Refine.PropWhen
import ConRon.Refine.Expr
import ConRon.Refine.ExprOps
import ConRon.Refine.ExprOpsFields
import ConRon.Refine.ExprOpsSubst
import ConRon.Refine.ExprOpsSpine
import ConRon.Refine.ExprOpsMeta
import ConRon.Refine.BasisTables
import ConRon.Refine.Env
import ConRon.Refine.FEnv
import ConLeche.Kernel.FEnv
import ConLeche.Kernel.Basis.Names

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine

/-! ## Slices and string literals -/

/-- `Slice::index_usize` when it succeeds: the model's slice really does have
that element at that index. -/
theorem slice_index_getElem? {α : Type} {s : Slice α} {i : Std.Usize} {x : α}
    (h : Slice.index_usize s i = ok x) : s.val[i.val]? = some x := by
  rw [Slice.index_usize] at h
  have hb : s[i]? = s.val[i.val]? := rfl
  rcases hi : s.val[i.val]? with _ | y
  · rw [hb, hi] at h; simp at h
  · rw [hb, hi] at h
    exact congrArg some (Result.ok_injective h)

/-- The index recursion behind `core_types::code_points`: it copies
`codes[i..]` onto the accumulator. -/
theorem code_points_from_val (N : Nat) :
    ∀ (codes : Slice Std.U32) (i : Std.Usize) (out r : alloc.vec.Vec Std.U32),
      codes.val.length - i.val = N →
      core_types.code_points_from codes i out = ok r →
      r.val = out.val ++ codes.val.drop i.val := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro codes i out r hN h
    rw [core_types.code_points_from.eq_def] at h
    dsimp only at h
    split at h
    · have hlen : codes.val.length ≤ i.val := by
        have := Slice.len_val codes; scalar_tac
      rw [← Result.ok_injective h, List.drop_eq_nil_of_le hlen]; simp
    · simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hidx, out1, hpush, i2, hi2, hrec⟩ := h
      have hg := slice_index_getElem? hidx
      have hlt : i.val < codes.val.length := by
        have := Slice.len_val codes; scalar_tac
      have hx : codes.val[i.val] = x := by
        rw [List.getElem?_eq_getElem hlt] at hg; exact Option.some_injective _ hg
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      rw [ih (codes.val.length - i2.val) (by omega) codes i2 out1 r rfl hrec,
        vec_push_val hpush, hi2v, List.drop_eq_getElem_cons hlt, hx]
      simp

/-- `core_types::code_points` is the slice it copies (DESIGN.md §3.3: a Lean
string literal is a `const [u32; N]` plus this copy). -/
theorem code_points_val {codes : Slice Std.U32} {r : alloc.vec.Vec Std.U32}
    (h : core_types.code_points codes = ok r) : r.val = codes.val := by
  rw [core_types.code_points] at h
  rw [code_points_from_val _ codes 0#usize _ r rfl h]
  simp [alloc.vec.Vec.with_capacity, show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

/-- A code-point list as a Lean `String`, i.e. `absString` on the list rather
than on the `Vec` (the pinned names are stated against the `const` array, whose
`val` is a list). -/
def absCodes (l : List Std.U32) : String := String.ofList (l.map fun c => Char.ofNat c.val)

theorem absString_eq (v : alloc.vec.Vec Std.U32) : absString v = absCodes v.val := rfl

/-- **The pinned-name step.**  `name::mk_str pre (code_points S)` — the body of
every `basis_names` function and of every pinned name in `core_k.rs` — refines
`pre.str s` and builds a well-formed name, provided the literal's code points
are valid `Char`s (which `decide` settles on any concrete `S`). -/
theorem str_lit_step {k : Std.Usize} {S : Array Std.U32 k} {L : List Std.U32}
    {v : Slice Std.U32} {w : alloc.vec.Vec Std.U32} {pre n : name.Name}
    (hprewf : NameWF pre)
    (hv : lift (Array.to_slice S) = ok v)
    (hw : core_types.code_points v = ok w)
    (hmk : name.mk_str pre w = ok n)
    (hSL : S.val = L)
    (hvalid : ∀ c ∈ L, Nat.isValidChar c.val) :
    absName n = .str (absName pre) (absCodes L) ∧ NameWF n := by
  simp only [lift_eq, Result.ok.injEq] at hv
  subst hv
  have hwv : w.val = L := by
    rw [code_points_val hw, Array.val_to_slice, hSL]
  refine ⟨?_, NameWF.str hprewf ?_ hmk⟩
  · rw [Name.mk_str_refines hmk, absString_eq, hwv]
  · intro c hc; exact hvalid c (by rw [← hwv]; exact hc)

/-! ## The pinned names, as a statement

`PinnedName f ln` is exactly what `Refine/BasisNames.lean` and
`Refine/CoreKNames.lean` prove of a pinned `Name`-valued constant, and
`PinnedNames` the same for a pinned `Vec<Name>` table.  They live here because
every `CoreK*` file that compares against a pin states its dependency in this
shape, and `Refine/CoreKPinned.lean` discharges them. -/

/-- "`f` is the port's spelling of the pinned con-leche name `ln`, and the name
it builds is well formed." -/
def PinnedName (f : Result name.Name) (ln : ConLeche.Name) : Prop :=
  ∀ n : name.Name, f = ok n → absName n = ln ∧ NameWF n

/-- The same for a pinned `Vec<Name>` table. -/
def PinnedNames (f : Result (alloc.vec.Vec name.Name)) (l : List ConLeche.Name) : Prop :=
  ∀ v, f = ok v → absNames v = l ∧ NamesWF v

/-- The numeric-suffix step (`name::mk_num`), the same way. -/
theorem num_lit_step {pre n : name.Name} {m : Std.U64}
    (hprewf : NameWF pre) (hmk : name.mk_num pre m = ok n) :
    absName n = .num (absName pre) m.val ∧ NameWF n :=
  ⟨Name.mk_num_refines hmk, NameWF.num hprewf hmk⟩

/-! # What this step takes from tasks #46 and #50, and the one thing it states
differently

`CORE_PLAN.md` steps 1 and 2 have landed: the `env`-record abstractions
(`absConstantVal`, `absConstantInfo`, `absProjEntry`, `absProjTable`,
`absRecRule(s)`, `absHint`, `absMode`, `absEnv`) and the hereditary
well-formedness predicates (`ConstantValWF` ... `ConstantInfoWF`, `EnvWF`) are
`Refine/Abs.lean`'s, `kernel::env`'s refinements are `Refine/Env.lean`'s and
`kernel::fenv`'s are `Refine/FEnv.lean`'s.  This file defines none of them any
more; the local copies task #49 needed while #46 was in flight are gone.

**The one thing step 4 states differently: `FindAgree`, not `FEnv.FEnvRel`.**
`core_k.rs` and `prop_read.rs` read the environment through exactly two calls,
`fenv::find` and `fenv::find_proj` (`core_k.rs`'s module note, deviation 3).  So
the hypothesis every lemma of the `CoreK*` family carries is *find-agreement* —
strictly weaker than task #46's three-clause `FEnv.FEnvRel`, which also fixes
`visible_below`, `absEnv fe.env` and the index's `HashMap.RelOn`, none of which
anything here reads.  Stating step 4 over the weaker hypothesis makes its
theorems stronger and keeps them independent of how the index is built;
`FindAgree.of_rel` and `FindWF.of_wf` below turn task #46's relation and
invariant into them in one step, which is all step 6's knot needs.  (`FindWF`
is the same projection of `FEnv.FEnvWF`: what a lookup hands back is a
well-formed record, which is what a result used as a *term* needs.) -/

/-- **Find-agreement**: whatever `fenv::find` answers abstracts to whatever
`ConLeche.FEnv.find?` answers.  The projection of `FEnv.FEnvRel` that
`core_k.rs`/`prop_read.rs` read; `FindAgree.of_rel` is the bridge. -/
def FindAgree (fe : fenv.FEnv) (lfe : ConLeche.FEnv) : Prop :=
  ∀ (n : name.Name) (o : Option env.ConstantInfo), NameWF n →
    fenv.find fe n = ok o → o.map absConstantInfo = lfe.find? (absName n)

/-- **Find-well-formedness**: whatever `fenv::find` answers is a well-formed
stored record.  The projection of `FEnv.FEnvWF` that step 4 reads. -/
def FindWF (fe : fenv.FEnv) : Prop :=
  ∀ (n : name.Name) (ci : env.ConstantInfo), NameWF n →
    fenv.find fe n = ok (some ci) → ConstantInfoWF ci

/-- Task #46's relation gives find-agreement (`FEnv.find_refines`). -/
theorem FindAgree.of_rel {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FEnv.FEnvRel fe lfe) (hwf : FEnv.FEnvWF fe) : FindAgree fe lfe :=
  fun _ _ hn h => FEnv.find_refines hrel hwf hn h

/-- Task #46's invariant gives find-well-formedness (`FEnv.find_wf`). -/
theorem FindWF.of_wf {fe : fenv.FEnv} (hwf : FEnv.FEnvWF fe) : FindWF fe :=
  fun _ _ hn h => FEnv.find_wf hwf hn h _ rfl

/-- The two directions of `FindAgree`, in the form a guard's proof uses them: a
hit abstracts to a hit, a miss to a miss. -/
theorem FindAgree.find_some {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (h : FindAgree fe lfe) {n : name.Name} {ci : env.ConstantInfo}
    (hn : NameWF n) (hf : fenv.find fe n = ok (some ci)) :
    lfe.find? (absName n) = some (absConstantInfo ci) := by
  simpa using (h n (some ci) hn hf).symm

theorem FindAgree.find_none {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (h : FindAgree fe lfe) {n : name.Name}
    (hn : NameWF n) (hf : fenv.find fe n = ok none) :
    lfe.find? (absName n) = none := by
  simpa using (h n none hn hf).symm

/-! ## Three `kernel::env` readings, paired

Task #46's `Refine/Env.lean` proves each of these as two lemmas, a refinement
and a well-formedness.  Every guard in the `CoreK*` family consumes them
together (`obtain ⟨habs, hwf⟩ := …`), so they are paired here once rather than
at forty call sites.  No new content: each is the conjunction of two of
`Refine/Env.lean`'s. -/

/-- `ConLeche/Kernel/Env.lean:602` — `env::proj_table_name` refines
`projTableName` and builds a well-formed name. -/
theorem proj_table_name_refines {t n : name.Name} (ht : NameWF t)
    (h : env.proj_table_name t = ok n) :
    absName n = ConLeche.projTableName (absName t) ∧ NameWF n :=
  ⟨Env.proj_table_name_refines h, Env.proj_table_name_wf ht h⟩

/-- `ConLeche/Kernel/Env.lean:596` — `env::proj_fn_name` refines `projFnName`
and builds a well-formed name. -/
theorem proj_fn_name_refines {t n : name.Name} {i : Std.U64} (ht : NameWF t)
    (h : env.proj_fn_name t i = ok n) :
    absName n = ConLeche.projFnName (absName t) i.val ∧ NameWF n :=
  ⟨Env.proj_fn_name_refines h, Env.proj_fn_name_wf ht h⟩

/-- `env::default_expr` is Lean's `default : Expr` (`.bvar 0`), well formed. -/
theorem default_expr_refines {e : expr.Expr} (h : env.default_expr = ok e) :
    absExpr e = default ∧ ExprWF e :=
  ⟨Env.default_expr_refines h, Env.default_expr_wf h⟩

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/--
info: 'ConRon.Refine.str_lit_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms str_lit_step

end ConRon.Refine

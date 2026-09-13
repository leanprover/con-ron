/-
`CORE_PLAN.md` step 4, the shared foundation (task #49): the plumbing the
refinement of `kernel/core_k.rs`, `kernel/prop_read.rs` and
`kernel/basis_names.rs` needs before any of their functions can be stated.

Three things live here and nowhere else in the `CoreK*` family:

* **`core_types::code_points`**, the port's spelling of a Lean string literal
  (DESIGN.md §3.3): `code_points_val` says the copy is the slice, and
  `str_lit_step`/`num_lit_step` package the two-or-three-bind body that every
  pinned name in `basis_names.rs` and `core_k.rs` has.
* **The `env`-record abstractions and well-formedness predicates.**  Task #46
  (`CORE_PLAN.md` step 1) is writing `absConstantInfo`, `absEnv` and friends
  into `Refine/Abs.lean` and `Refine/Env.lean`.  Until that lands, the
  `ConstantInfo` half is taken from `Refine/BasisTables.lean`'s `T22`
  namespace (task #22's copies, which task #20's merge left in place) and the
  two records `T22` does not have -- `ProjEntry` and `CheckMode` -- plus the
  whole `*WF` family are defined below, under a section marked
  **TO BE UNIFIED WITH TASK #46**.
* **`FEnvRel`/`FEnvWF`**, likewise minimal and likewise marked: `FEnvRel` is
  *find-agreement only* (`CORE_PLAN.md`'s full relation adds `visible_below`
  and `absEnv fe.env = lfe.env`, which nothing in this step reads), and the
  `findProj?` agreement is **derived** from it rather than assumed, through
  local refinements of `env::proj_table_name` and `env::proj_table_entry`.
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

/-! # TO BE UNIFIED WITH TASK #46

Everything from here to the end of the file is the minimum `CORE_PLAN.md` step
4 needs of steps 1 and 2, written locally because those steps are being landed
in parallel (`Refine/Abs.lean`'s `absConstantInfo`/`absEnv`, `Refine/Env.lean`,
`Refine/FEnv.lean`).  On merge: delete the `absProjEntry`/`absCheckMode`
definitions and the `*WF` family in favour of `Abs.lean`'s, and replace
`FEnvRel`/`FEnvWF` by `Refine/FEnv.lean`'s (whose `find` clause is this one,
plus the `visible_below` and `absEnv` clauses nothing here reads).  The
`open T22` below goes away with `BasisTables.lean`'s own `T22` section. -/

open ConRon.Refine.T22

/-- `ConLeche/Kernel/Env.lean:447` — `ProjEntry`.  (`T22` has every other
`env` record; this one no lemma needed before task #49.) -/
def absProjEntry (e : env.ProjEntry) : ConLeche.ProjEntry where
  structName := absName e.struct_name
  idx := e.idx.val
  levelParams := absNames e.level_params
  numParams := e.num_params.val
  ctor := absName e.ctor
  numFields := e.num_fields.val
  body := absExpr e.body
  fieldSort := absLevel e.field_sort
  structSort := absLevel e.struct_sort
  off := e.off.val

/-- `ConLeche/Kernel/Env.lean:69` — `CheckMode`. -/
def absCheckMode : env.CheckMode → ConLeche.CheckMode
  | .Verified => .verified
  | .Trusted => .trusted

/-! ## The well-formedness predicates of the stored records

Hereditary, in the task-#5/#17 style: a stored record is well formed when every
`Name`/`Level`/`Expr`/`PropWhen` in it is.  Plain conjunctions, not inductive
predicates: unlike `Name`/`Level`/`Expr` these records have no smart
constructor whose stored derived word needs pinning. -/

def ConstantValWF (cv : env.ConstantVal) : Prop :=
  NameWF cv.name ∧ NamesWF cv.level_params ∧ ExprWF cv.ty

def RecRuleFireWF : env.RecRuleFire → Prop
  | .Inert => True
  | .Plain => True
  | .Nested us es => LevelsWF us ∧ ExprsWF es

def RecRuleWF (r : env.RecRule) : Prop :=
  NameWF r.ctor ∧ RecRuleFireWF r.fire ∧ ExprWF r.rhs

def RecRulesWF (rs : alloc.vec.Vec env.RecRule) : Prop := ∀ r ∈ rs.val, RecRuleWF r

def IndCapsWF (c : env.IndCaps) : Prop := NameWF c.eta_ctor ∧ PropWhenWF c.sort_z

def ProjTableWF (t : env.ProjTable) : Prop :=
  NameWF t.struct_name ∧ NamesWF t.level_params ∧ NameWF t.ctor ∧
    LevelWF t.struct_sort ∧ ExprsWF t.bodies ∧ LevelsWF t.guards

def ProjEntryWF (e : env.ProjEntry) : Prop :=
  NameWF e.struct_name ∧ NamesWF e.level_params ∧ NameWF e.ctor ∧
    ExprWF e.body ∧ LevelWF e.field_sort ∧ LevelWF e.struct_sort

def ConstantInfoWF : env.ConstantInfo → Prop
  | .AxiomInfo cv => ConstantValWF cv
  | .DefnInfo cv v _ => ConstantValWF cv ∧ ExprWF v
  | .ThmInfo cv v => ConstantValWF cv ∧ ExprWF v
  | .IndInfo cv c => ConstantValWF cv ∧ IndCapsWF c
  | .CtorInfo cv _ _ => ConstantValWF cv
  | .RecInfo cv _ _ rs => ConstantValWF cv ∧ RecRulesWF rs
  | .ProjInfo t => ProjTableWF t

/-! ## `FEnvRel` and `FEnvWF` -/

/-- **The minimal environment relation**: `fenv::find` agrees with
`ConLeche.FEnv.find?` under `absName` and `absConstantInfo`.  This is the one
clause `core_k.rs`/`prop_read.rs` read — every environment access in those two
modules is a `fenv::find` (module note deviation 3) or a `fenv::find_proj`,
and the latter is *derived* below. -/
def FEnvRel (fe : fenv.FEnv) (lfe : ConLeche.FEnv) : Prop :=
  ∀ n : name.Name, NameWF n →
    ∃ o : Option env.ConstantInfo,
      fenv.find fe n = ok o ∧ o.map absConstantInfo = lfe.find? (absName n)

/-- Every stored constant is well formed.  Hereditary in the §3.5 sense: what
a lookup hands back may be used as a term. -/
def FEnvWF (fe : fenv.FEnv) : Prop :=
  ∀ (n : name.Name) (ci : env.ConstantInfo),
    fenv.find fe n = ok (some ci) → ConstantInfoWF ci

/-- The two directions of `FEnvRel`, in the form a guard's proof uses them: a
hit abstracts to a hit, a miss to a miss. -/
theorem FEnvRel.find_some {fe lfe} (h : FEnvRel fe lfe) {n ci}
    (hn : NameWF n) (hf : fenv.find fe n = ok (some ci)) :
    lfe.find? (absName n) = some (absConstantInfo ci) := by
  obtain ⟨o, ho, habs⟩ := h n hn
  rw [hf] at ho; rw [← Result.ok_injective ho] at habs
  exact habs.symm

theorem FEnvRel.find_none {fe lfe} (h : FEnvRel fe lfe) {n}
    (hn : NameWF n) (hf : fenv.find fe n = ok none) :
    lfe.find? (absName n) = none := by
  obtain ⟨o, ho, habs⟩ := h n hn
  rw [hf] at ho; rw [← Result.ok_injective ho] at habs
  exact habs.symm

/-- `fenv::find` is total on a related environment: the useful direction when a
guard has to be run before its result is inspected. -/
theorem FEnvRel.find_ok {fe lfe} (h : FEnvRel fe lfe) {n} (hn : NameWF n) :
    ∃ o, fenv.find fe n = ok o := by
  obtain ⟨o, ho, _⟩ := h n hn; exact ⟨o, ho⟩

/-! ## `env::proj_table_name` and `env::proj_table_entry`, and `find_proj`

Three refinements that belong in task #46's `Refine/Env.lean`; they are here
because `FEnvRel` is find-agreement only and the `findProj?` agreement has to
come from somewhere. -/

/-- `ConLeche/Kernel/Env.lean:602` — `env::proj_table_name` refines
`projTableName`. -/
theorem proj_table_name_refines {t n : name.Name} (ht : NameWF t)
    (h : env.proj_table_name t = ok n) :
    absName n = ConLeche.projTableName (absName t) ∧ NameWF n := by
  rw [env.proj_table_name] at h
  simp only [bind_eq_ok_iff, name_dup_eq, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨s, hs, v, hv, n1, hmk, hnum⟩ := h
  obtain ⟨h1, h1wf⟩ := str_lit_step ht hs hv hmk
    (L := [112#u32, 114#u32, 111#u32, 106#u32, 84#u32, 97#u32, 98#u32, 108#u32, 101#u32])
    (by simp [env.PROJ_TABLE_STR]) (by decide)
  obtain ⟨h2, h2wf⟩ := num_lit_step h1wf hnum
  exact ⟨by rw [h2, h1]; rfl, h2wf⟩

/-- `env::default_expr` refines Lean's `default : Expr` (`.bvar 0`). -/
theorem default_expr_refines {e : expr.Expr} (h : env.default_expr = ok e) :
    absExpr e = default ∧ ExprWF e := by
  rw [env.default_expr] at h
  exact ⟨by rw [Expr.bvar_refines h]; rfl, Expr.bvar_wf h⟩

/-- A `Vec<RecRule>` as con-leche's rule list. -/
def absRecRules (rs : alloc.vec.Vec env.RecRule) : List ConLeche.RecRule :=
  rs.val.map absRecRule

/-! ## Axiom census (DESIGN.md §5, the P3 gate) -/

/--
info: 'ConRon.Refine.proj_table_name_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms proj_table_name_refines

end ConRon.Refine

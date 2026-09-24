/-
# `ConRon.Refine2.Inductives.Shape` — the inductive tier's abstractions

**Task #97-P5-Ind** (DESIGN.md §8.2, Theorem 2), the shared base of
`Refine2/Inductives/**`.  `Refine2/Shape.lean` and
`Refine2/Checker/Shape.lean` carry the statement shapes this tier uses
(`Sim`, `SimR`, `SimRE`, `SimP`, `SimRel`, and `ExprOps/Read.lean`'s
`WOut` / `LOut` for the two memo-threading walks); what this file adds is the
**data**: the six records `arena::inductives` has that no earlier tier
abstracts, and the containers its functions carry.

## The records

| Rust | twin | note |
|---|---|---|
| `sum_parts::InductiveShape` | `InductiveShape` | field for field |
| `struct_parts::StructParts` | `StructParts` | field for field |
| `native_parts::RecFieldKind` | `RecFieldKind` | five constructors, twinned rather than imported (`Arena/Inductives/NativeParts.lean`'s module note) |
| `native_parts::NativeParts` | `NativeParts` | the twin `extends InductiveShape`; the port has a `shape` FIELD, which is the one record-shape difference of the tier |
| `native_install::NativePass` | `NativePass` | its `env₁` is an `IFEnv`, so the record RELATES and does not abstract |
| `modeled::RenameBy` | a `List (NIdx × NIdx)` | **finding 15** below |

**Finding 15 — the last higher-order argument of the crate is not one.**
Task #97-P5-0's finding 6 gave `arena::expr_ops::rename_consts` a relation
(`RenameRel`) because the Rust's one-method `NIdxToNIdx` trait stands against
a twin that takes a TOTAL FUNCTION `NIdx → NIdx`.  At the modeled route the
twin does not take a function either: `Arena/Inductives/Modeled.lean`'s module
note says the renaming maps are precomputed TABLES and `renameBy tbl` is their
lookup, because building a name over handles means interning one.  So
`RenameBy` and the twin's `List (NIdx × NIdx)` relate as CONTAINERS —
`absRenameBy` is an ordinary abstraction function, and the `RenameRel`
hypothesis the `expr_ops` statements carry is discharged at every call site of
this tier by `rename_by_rel` (`Refine2/Inductives/Modeled.lean`).

## The containers

Every one is a `Vec` against the container the twin chose, and — as in
`Refine2/Checker/Shape.lean` — the `…From` family is DESIGN §3.4's standing
`List`-as-cursor deviation: where the twin recurses structurally on a `List`,
the Rust takes the whole `Vec` and an index.
-/
import ConRon.Refine2.Checker.KnotHyp
import ConRon.Refine2.Tactic.Prims
import ConRon.Refine2.Inductives.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The scalar and handle containers -/

/-- A `Vec<u64>` as the twin's `List Nat` — `recIdxOf`'s recursive-field
positions. -/
def absNatL (v : alloc.vec.Vec Std.U64) : List Nat := v.val.map absU

def absNatLFrom (v : alloc.vec.Vec Std.U64) (i : Std.Usize) : List Nat :=
  (v.val.drop i.val).map absU

/-- A `Vec<bool>` as the twin's `List Bool` — `structUsedLaterList`'s
answers. -/
def absBoolL (v : alloc.vec.Vec Bool) : List Bool := v.val

def absBoolLFrom (v : alloc.vec.Vec Bool) (i : Std.Usize) : List Bool :=
  v.val.drop i.val

/-- A `Vec<Vec<LIdx>>` as the twin's `List (List LIdx)` — the fields' sorts,
one list per constructor. -/
def absLIdxLL (v : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx)) :
    List (List LIdx) := v.val.map absLIdxL

def absLIdxLLFrom (v : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx))
    (i : Std.Usize) : List (List LIdx) := (v.val.drop i.val).map absLIdxL

/-- A `Vec<(EIdx, BinderMeta)>` as the twin's `List (EIdx × BinderMeta)` —
`piBinders`' telescope.  `Refine2/Checker/Shape.lean`'s `absBinderArr` is the
same `Vec` read as `domsMatchAux`' `Array`; both readings occur in this tier,
which is task #97-P5-0's finding 5 met again. -/
def absBinderL (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    List (EIdx × ConLeche.BinderMeta) :=
  v.val.map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)

def absBinderLFrom (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta))
    (i : Std.Usize) : List (EIdx × ConLeche.BinderMeta) :=
  (v.val.drop i.val).map fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)

/-! ## The constructor spines -/

/-- `Vec<(IConstantVal, u64)>` as the twin's `List (IConstantVal × Nat)` — the
constructors with their field counts (`InductiveShape.ctors`). -/
def absCtorsL (v : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    List (IConstantVal × Nat) := v.val.map fun p => (absIConstantVal p.1, absU p.2)

def absCtorsLFrom (v : alloc.vec.Vec (arena.env.IConstantVal × Std.U64))
    (i : Std.Usize) : List (IConstantVal × Nat) :=
  (v.val.drop i.val).map fun p => (absIConstantVal p.1, absU p.2)

/-- `Vec<(IConstantVal, u64, u64)>` as the twin's
`List (IConstantVal × Nat × Nat)` — `sumSplit`'s constructors, with their
parameter AND field counts. -/
def absCtors3L (v : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64)) :
    List (IConstantVal × Nat × Nat) :=
  v.val.map fun p => (absIConstantVal p.1, absU p.2.1, absU p.2.2)

def absCtors3LFrom (v : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64))
    (i : Std.Usize) : List (IConstantVal × Nat × Nat) :=
  (v.val.drop i.val).map fun p => (absIConstantVal p.1, absU p.2.1, absU p.2.2)

/-- `Vec<(NIdx, u64, EIdx, Vec<u64>)>` as the twin's
`List (NIdx × Nat × EIdx × List Nat)` — `nativeCtors4`'s output: the
constructors zipped with their recursive-field positions. -/
def absCtors4L
    (v : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))) : List (NIdx × Nat × EIdx × List Nat) :=
  v.val.map fun p => (absNIdx p.1, absU p.2.1, absEIdx p.2.2.1, absNatL p.2.2.2)

def absCtors4LFrom
    (v : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))) (i : Std.Usize) :
    List (NIdx × Nat × EIdx × List Nat) :=
  (v.val.drop i.val).map fun p =>
    (absNIdx p.1, absU p.2.1, absEIdx p.2.2.1, absNatL p.2.2.2)

/-- `Vec<(IConstantVal, u64, u64, Vec<IRecRule>)>` as the twin's
`List (IConstantVal × Nat × Nat × List IRecRule)` — `provisionRecs`' answer. -/
def absRecsL
    (v : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64 ×
      (alloc.vec.Vec arena.env.IRecRule))) :
    List (IConstantVal × Nat × Nat × List IRecRule) :=
  v.val.map fun p =>
    (absIConstantVal p.1, absU p.2.1, absU p.2.2.1, p.2.2.2.val.map absIRecRule)

def absRecsLFrom
    (v : alloc.vec.Vec (arena.env.IConstantVal × Std.U64 × Std.U64 ×
      (alloc.vec.Vec arena.env.IRecRule))) (i : Std.Usize) :
    List (IConstantVal × Nat × Nat × List IRecRule) :=
  (v.val.drop i.val).map fun p =>
    (absIConstantVal p.1, absU p.2.1, absU p.2.2.1, p.2.2.2.val.map absIRecRule)

/-! ## The renaming table (finding 15) -/

/-- `Vec<(NIdx, NIdx)>` as the twin's `List (NIdx × NIdx)` — the rename tables
of `Arena/Inductives/Modeled.lean`'s `blockRenameTable`, `projBack` and
`projFwd`. -/
def absRenameTbl (v : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx)) :
    List (NIdx × NIdx) := v.val.map fun p => (absNIdx p.1, absNIdx p.2)

def absRenameTblFrom (v : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx))
    (i : Std.Usize) : List (NIdx × NIdx) :=
  (v.val.drop i.val).map fun p => (absNIdx p.1, absNIdx p.2)

/-- **`arena::inductives::modeled::RenameBy` is the twin's table, boxed** —
finding 15 of the module note. -/
def absRenameBy (r : arena.inductives.modeled.RenameBy) : List (NIdx × NIdx) :=
  absRenameTbl r.tbl

/-! ## The five records -/

/-- `arena::inductives::sum_parts::InductiveShape`. -/
def absInductiveShape (p : arena.inductives.sum_parts.InductiveShape) :
    InductiveShape :=
  ⟨absIConstantVal p.cv_t, absCtorsL p.ctors, absU p.n_p, absU p.n_idx,
    absIConstantVal p.cv_r, absNIdx p.elim, absLIdx p.res_sort, absEIdxL p.rhss,
    p.large, p.is_prop⟩

/-- `arena::inductives::struct_parts::StructParts`. -/
def absStructParts (p : arena.inductives.struct_parts.StructParts) : StructParts :=
  ⟨absIConstantVal p.cv_t, absIConstantVal p.cv_c, absU p.n_p, absU p.n_f,
    absIConstantVal p.cv_r, absNIdx p.elim, absLIdx p.res_sort, absEIdx p.rhs,
    p.large, p.is_prop⟩

/-- The rule's fields, abstracted (`rfl`; registered `lockstep_simp` LOCALLY by
the files that need them — `PrimsModeled.lean` has the modeled route's own
copies under the unsuffixed names). -/
theorem absIRecRule_ctor_eq (r : arena.env.IRecRule) :
    (absIRecRule r).ctor = absNIdx r.ctor := rfl
theorem absIRecRule_nfields_eq (r : arena.env.IRecRule) :
    (absIRecRule r).nfields = absU r.nfields := rfl
theorem absIRecRule_rhs_eq (r : arena.env.IRecRule) :
    (absIRecRule r).rhs = absEIdx r.rhs := rfl

/-- `arena::inductives::native_parts::RecFieldKind`. -/
def absRecFieldKind : arena.inductives.native_parts.RecFieldKind → RecFieldKind
  | .Ordinary => .ordinary
  | .Recursive => .recursive
  | .Reflexive => .reflexive
  | .Negative => .negative
  | .Unsupported => .unsupported

def absKindL (v : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind) :
    List RecFieldKind := v.val.map absRecFieldKind

def absKindLFrom (v : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)
    (i : Std.Usize) : List RecFieldKind := (v.val.drop i.val).map absRecFieldKind

def absKindLL
    (v : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)) :
    List (List RecFieldKind) := v.val.map absKindL

def absKindLLFrom
    (v : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind))
    (i : Std.Usize) : List (List RecFieldKind) := (v.val.drop i.val).map absKindL

/-- `arena::inductives::native_parts::NativeParts` — **the one record-shape
difference of this tier**: the twin `extends InductiveShape` where the port
carries a `shape` field, so the abstraction crosses that boundary here and
`toInductiveShape` is what every consumer of the twin's record reads. -/
def absNativeParts (p : arena.inductives.native_parts.NativeParts) : NativeParts :=
  ⟨absInductiveShape p.shape, absKindLL p.kinds, p.rec_pinned⟩

/-- `arena::inductives::native_install::NativePass`.  Its `env1` field is an
`IFEnv`, which RELATES rather than abstracts (`Refine2/AbsState.lean`'s
`IFEnvRel`), so the record needs a relation and not a function. -/
structure NativePassRel (r : arena.inductives.native_install.NativePass)
    (l : NativePass) : Prop where
  env₁ : IFEnvRel r.env1 l.env₁
  env₁Inv : IFEnvInv r.env1
  cvTa : l.cvTa = absIConstantVal r.cv_ta
  p : l.p = absNativeParts r.p
  ctorsA : l.ctorsA = absCtorsL r.ctors_a
  sortss : l.sortss = absLIdxLL r.sortss

/-! ## Rule 11 at a COUNTED recursion — the tier's four list closers

DESIGN §3.4 turns every `List` operation of a twin into a named cursor
recursion in the port, and `Refine2/Inductives/Spec.lean` transcribes the twin
side the same way.  So an `_unfold` equation about a twin that calls
`List.allM`, `List.mapM` or `(List.range n).allM` has to say *"the library
fold IS the counted recursion"*, and that is one induction each rather than
one per call site.  Task #97-P5-Checker's **rule 11** (`am_bind_congr` and
`twin_reduce`, `Refine2/Checker/Shape.lean`) is what the step of each needs:
`congr 1` eta-expands the state function instead of peeling the bind.

The four are stated against an ARBITRARY `G` with its two clauses as
hypotheses, so a caller supplies `G := <its transcription>` and discharges
both by `rfl` — which is what makes them one lemma for the whole tier rather
than one per unfold. -/

/-- **The two-sided bind peel.**  `am_bind_congr` asks the two `do` blocks to
agree on the action they bind; an `_unfold` whose twin calls a LIBRARY fold
where the transcription calls the counted recursion does not, and the four
`*_counted` lemmas below are exactly the proof that the two heads agree.
Splitting the bind in two keeps the counted lemma's `F` determined BY THE
GOAL, which matters: a `have` that restates the twin's lambda gets its own
matcher constant and neither `rw` nor `simp` then fires (round 2 met this at
`recCtorKinds` and called it "`range_mapM_counted` will not `rw` into the
reduced matcher arm"). -/
theorem am_bind_congr₂ {α β : Type} {x y : AM α} {f g : α → AM β}
    (hxy : x = y) (h : ∀ a, f a = g a) : (x >>= f) = (y >>= g) := by
  rw [hxy, funext h]

/-- `List.allM` IS the cursor recursion that transcribes it. -/
theorem list_allM_counted {α : Type} (F : α → AM Bool) (G : List α → AM Bool)
    (h0 : G [] = pure true)
    (hs : ∀ a l, G (a :: l) = (do if ← F a then G l else pure false)) :
    ∀ l, l.allM F = G l := by
  intro l
  induction l with
  | nil => rw [h0]; rfl
  | cons a l ih =>
    rw [hs]
    simp only [List.allM, ih]
    refine am_bind_congr _ ?_
    intro b
    cases b <;> rfl

/-- `(List.range' i m).allM` IS the counted recursion that transcribes it —
and `List.range n` is `List.range' 0 n`. -/
theorem range_allM_counted (F : Nat → AM Bool) (G : Nat → Nat → AM Bool)
    (h0 : ∀ i, G 0 i = pure true)
    (hs : ∀ m i, G (m + 1) i = (do if ← F i then G m (i + 1) else pure false)) :
    ∀ m i, (List.range' i m).allM F = G m i := by
  intro m
  induction m with
  | zero => intro i; rw [h0]; rfl
  | succ m ih =>
    intro i
    rw [hs]
    simp only [List.range'_succ, List.allM, ih]
    refine am_bind_congr _ ?_
    intro b
    cases b <;> rfl

/-- `(List.range' i m).mapM` IS the counted recursion that transcribes it. -/
theorem range_mapM_counted {γ : Type} (F : Nat → AM γ) (G : Nat → Nat → AM (List γ))
    (h0 : ∀ i, G 0 i = pure [])
    (hs : ∀ m i, G (m + 1) i = (do let a ← F i; let rest ← G m (i + 1); pure (a :: rest))) :
    ∀ m i, (List.range' i m).mapM F = G m i := by
  intro m
  induction m with
  | zero => intro i; rw [h0]; rfl
  | succ m ih =>
    intro i
    rw [hs]
    simp only [List.range'_succ, List.mapM_cons, ih]

/-- `List.mapM` IS the cursor recursion that transcribes it. -/
theorem list_mapM_counted {α γ : Type} (F : α → AM γ) (G : List α → AM (List γ))
    (h0 : G [] = pure [])
    (hs : ∀ a l, G (a :: l) = (do let b ← F a; let rest ← G l; pure (b :: rest))) :
    ∀ l, l.mapM F = G l := by
  intro l
  induction l with
  | nil => rw [h0]; rfl
  | cons a l ih => rw [hs]; simp only [List.mapM_cons, ih]

/-- **The memo walks' arm peel.**  A twin that writes
`let r ← match v with …; pure (ins h r)` has its continuation pushed into
every arm by the `do` elaborator, while the transcription binds once; rule 11's
`simp only` cannot bridge that (the two matchers are different constants), so
the arms are peeled by hand.  Three walks of this tier have exactly this
shape at one, two and three nested binds, and this is the one tactic that
closes all three. -/
syntax "pair_peel" : tactic
macro_rules
  | `(tactic| pair_peel) =>
    `(tactic| first
        | rfl
        | (refine am_bind_congr _ ?_
           intro __p
           obtain ⟨__b, __m⟩ := __p
           cases __b <;> (try twin_reduce) <;>
             (first
               | rfl
               | (refine am_bind_congr _ ?_
                  intro __q
                  obtain ⟨__b2, __m2⟩ := __q
                  cases __b2 <;> (try twin_reduce) <;>
                    (first
                      | rfl
                      | (refine am_bind_congr _ ?_
                         intro __r
                         obtain ⟨__b3, __m3⟩ := __r
                         cases __b3 <;> (try twin_reduce) <;> rfl))))))

/-- **The generic peel.**  `twin_reduce` puts both sides in right-associated
`bind` form; what is then left of a join point is `(match x with …) >>= k`
against `match x with | … => … >>= k`, which `split` closes — but only once
`am_bind_congr` has stripped the lambda that binds `x`.  Alternating the two
until nothing applies is the recipe, and it is what the deep `_unfold`s of
this tier need beyond rule 11's `simp only`. -/
syntax "twin_peel" : tactic
macro_rules
  | `(tactic| twin_peel) =>
    `(tactic| repeat' first
        | rfl
        | (refine am_bind_congr _ ?_; intro __x)
        | split)

/-! ## The state-free cursor recursion, and the `arena::env` copies

`cursor_induction`, `vec_cursor_copy` and the record copies' identity lemmas
(`i_constant_val_dup_abs` … `i_rec_rules_dup_abs`) moved down to
`Refine2/Dup.lean` (task #97-P5-Front round 2), so the frontend tier can cite
them. -/

/-! ### The boolean scans, once

The copier's sibling: a cursor recursion that answers a `Bool`.  Two
polarities occur in this tier — `all` (a default of `true` past the end, `false`
at the first element that fails) and `any` (`false` past the end, `true` at the
first hit) — and between them they are every `*_contains`, `*_any`, `*_seen`
and `*_pin_ok` of the tier. -/

/-- The scan that answers `true` past the end and stops at the first failure. -/
theorem vec_cursor_all {α : Type} (xs : alloc.vec.Vec α) (p : α → Bool)
    (F : Std.Usize → Result Bool)
    (hstop : ∀ (i : Std.Usize) (o : Bool),
      xs.val.length ≤ i.val → F i = ok o → o = true)
    (hstep : ∀ (i : Std.Usize) (x : α) (o : Bool),
      xs.val[i.val]? = some x → F i = ok o →
      (p x = true ∧ ∃ j : Std.Usize, j.val = i.val + 1 ∧ F j = ok o) ∨
      (p x = false ∧ o = false)) :
    ∀ (i : Std.Usize) (o : Bool), F i = ok o → o = (xs.val.drop i.val).all p := by
  intro i o h
  refine cursor_induction (fun i : Std.Usize => i.val) xs.val.length
    (fun i (_ : Unit) => ∀ o, F i = ok o → o = (xs.val.drop i.val).all p) ?_ ?_ i () o h
  · intro i _ hn o h
    rw [hstop i o hn h, List.drop_eq_nil_of_le hn]
    rfl
  · intro i _ hi ih o h
    obtain ⟨x, hx⟩ : ∃ x, xs.val[i.val]? = some x :=
      ⟨xs.val[i.val], List.getElem?_eq_getElem hi⟩
    obtain ⟨hb, hxv⟩ := List.getElem?_eq_some_iff.mp hx
    rw [List.drop_eq_getElem_cons hb, hxv, List.all_cons]
    rcases hstep i x o hx h with ⟨hp, j, hj, hF⟩ | ⟨hp, ho⟩
    · rw [ih j () hj o hF, hj, hp, Bool.true_and]
    · rw [ho, hp, Bool.false_and]

/-- The scan that answers `false` past the end and stops at the first hit. -/
theorem vec_cursor_any {α : Type} (xs : alloc.vec.Vec α) (p : α → Bool)
    (F : Std.Usize → Result Bool)
    (hstop : ∀ (i : Std.Usize) (o : Bool),
      xs.val.length ≤ i.val → F i = ok o → o = false)
    (hstep : ∀ (i : Std.Usize) (x : α) (o : Bool),
      xs.val[i.val]? = some x → F i = ok o →
      (p x = true ∧ o = true) ∨
      (p x = false ∧ ∃ j : Std.Usize, j.val = i.val + 1 ∧ F j = ok o)) :
    ∀ (i : Std.Usize) (o : Bool), F i = ok o → o = (xs.val.drop i.val).any p := by
  intro i o h
  refine cursor_induction (fun i : Std.Usize => i.val) xs.val.length
    (fun i (_ : Unit) => ∀ o, F i = ok o → o = (xs.val.drop i.val).any p) ?_ ?_ i () o h
  · intro i _ hn o h
    rw [hstop i o hn h, List.drop_eq_nil_of_le hn]
    rfl
  · intro i _ hi ih o h
    obtain ⟨x, hx⟩ : ∃ x, xs.val[i.val]? = some x :=
      ⟨xs.val[i.val], List.getElem?_eq_getElem hi⟩
    obtain ⟨hb, hxv⟩ := List.getElem?_eq_some_iff.mp hx
    rw [List.drop_eq_getElem_cons hb, hxv, List.any_cons]
    rcases hstep i x o hx h with ⟨hp, ho⟩ | ⟨hp, j, hj, hF⟩
    · rw [ho, hp, Bool.true_or]
    · rw [ih j () hj o hF, hj, hp, Bool.false_or]

-- `nidx_eq2_abs` / `eidx_eq2_abs` moved down to `Refine2/Checker/Shape.lean`
-- (task #97-P5-Checker round 4).

/-- **`arena::env::nidx_vec_contains` ⊑ `List.contains`.** -/
theorem nidx_vec_contains_abs {ns : alloc.vec.Vec arena.handle.NIdx}
    {n : arena.handle.NIdx} {o : Bool}
    (h : arena.env.nidx_vec_contains ns n = ok o) :
    o = (absNIdxL ns).contains (absNIdx n) := by
  rw [arena.env.nidx_vec_contains] at h
  have key : ∀ (i : Std.Usize) (o : Bool),
      arena.env.nidx_vec_contains_from ns i n = ok o →
      o = (ns.val.drop i.val).any fun m => absNIdx m == absNIdx n := by
    refine vec_cursor_any ns _ (fun i => arena.env.nidx_vec_contains_from ns i n) ?_ ?_
    · intro i o hn h
      rw [arena.env.nidx_vec_contains_from.eq_def] at h
      rw [if_pos (show i ≥ alloc.vec.Vec.len ns by scalar_tac), Result.ok.injEq] at h
      rw [h]
    · intro i x o hx h
      have hlt : i.val < ns.val.length := (List.getElem?_eq_some_iff.mp hx).1
      rw [arena.env.nidx_vec_contains_from.eq_def] at h
      rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ns by scalar_tac)] at h
      obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hnx : n1 = x := by
        have h1 := vec_index_some hn1; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
      subst hnx
      have hbv : b = (absNIdx n1 == absNIdx n) := nidx_eq2_abs hb
      cases hbb : b
      · rw [hbb] at h hbv
        rw [if_neg (by simp)] at h
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        exact Or.inr ⟨hbv.symm, i2, absSz_add_one hi2, h⟩
      · rw [hbb] at h hbv
        rw [if_pos (by simp), Result.ok.injEq] at h
        exact Or.inl ⟨hbv.symm, h.symm⟩
  rw [key 0#usize o h, show ((0#usize : Std.Usize)).val = 0 by scalar_tac,
    List.drop_zero, absNIdxL]
  have hcomm : (fun m => absNIdx m == absNIdx n) = (fun x => absNIdx n == absNIdx x) := by
    funext m
    by_cases hm : absNIdx m = absNIdx n
    · simp [hm]
    · have hm' : ¬ absNIdx n = absNIdx m := fun hc => hm hc.symm
      simp [hm, hm']
  rw [hcomm]
  simp only [List.contains_eq_any_beq, List.any_map, Function.comp_def]


open Lockstep in
@[lockstep] theorem nidx_vec_contains_twin (ns : alloc.vec.Vec arena.handle.NIdx)
    (n : arena.handle.NIdx) :
    LSP (arena.env.nidx_vec_contains ns n)
      (fun o => o = (absNIdxL ns).contains (absNIdx n)) :=
  fun _ h => nidx_vec_contains_abs h

/-- **`arena::core::nidx_vec_beq` ⊑ `==` on the abstraction.** -/
theorem nidx_vec_beq_abs {a b : alloc.vec.Vec arena.handle.NIdx} {o : Bool}
    (h : arena.core.nidx_vec_beq a b = ok o) :
    o = (absNIdxL a == absNIdxL b) := by
  rw [arena.core.nidx_vec_beq] at h
  by_cases hl : alloc.vec.Vec.len a = alloc.vec.Vec.len b
  · have hlv : a.val.length = b.val.length := by scalar_tac
    rw [if_pos hl] at h
    have key : ∀ (i : Std.Usize) (o : Bool),
        arena.core.nidx_vec_beq_from a b i = ok o →
        o = ((a.val.drop i.val).map absNIdx == (b.val.drop i.val).map absNIdx) := by
      intro i o hh
      refine cursor_induction (fun i : Std.Usize => i.val) a.val.length
        (fun i (_ : Unit) => ∀ o, arena.core.nidx_vec_beq_from a b i = ok o →
          o = ((a.val.drop i.val).map absNIdx == (b.val.drop i.val).map absNIdx))
        ?_ ?_ i () o hh
      · intro i _ hn o h
        rw [arena.core.nidx_vec_beq_from.eq_def] at h
        rw [if_pos (show i ≥ alloc.vec.Vec.len a by scalar_tac), Result.ok.injEq] at h
        rw [← h, List.drop_eq_nil_of_le hn,
          List.drop_eq_nil_of_le (show b.val.length ≤ i.val by omega)]
        simp
      · intro i _ hi ih o h
        rw [arena.core.nidx_vec_beq_from.eq_def] at h
        rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
        obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨ha1, ha2⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hn)
        obtain ⟨hb1', hb2⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hn1)
        rw [List.drop_eq_getElem_cons ha1, List.drop_eq_getElem_cons hb1',
          ha2, hb2, List.map_cons, List.map_cons]
        have hbv : b1 = (absNIdx n == absNIdx n1) := nidx_eq2_abs hb1
        cases hbb : b1
        · rw [hbb] at h hbv
          rw [if_neg (by simp), Result.ok.injEq] at h
          rw [← h]
          simp only [List.cons_beq_cons, ← hbv]
          simp
        · rw [hbb] at h hbv
          rw [if_pos (by simp)] at h
          obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
          rw [ih i2 () hi2v o h, hi2v]
          simp only [List.cons_beq_cons, ← hbv]
          simp
    rw [key 0#usize o h]
    simp [absNIdxL, show ((0#usize : Std.Usize)).val = 0 by scalar_tac]
  · rw [if_neg hl, Result.ok.injEq] at h
    have hlv : a.val.length ≠ b.val.length := by
      intro hc; exact hl (by scalar_tac)
    have hne : absNIdxL a ≠ absNIdxL b := by
      intro hc
      exact hlv (by simpa [absNIdxL] using congrArg List.length hc)
    rw [← h, eq_comm]
    exact beq_eq_false_iff_ne.mpr hne

/-- **A filtered `List.range`, read from a cursor on**, is the filter of the
range that starts there.  `recIdxOf` is such a filter and the port's
`rec_idx_of` walks it from a cursor, so this is what lets the walk's induction
be stated at `List.range'`. -/
theorem filter_range_filter_ge (P : Nat → Bool) (n i : Nat) :
    (((List.range n).filter P).filter fun j => decide (i ≤ j))
      = (List.range' i (n - i)).filter P := by
  rcases Nat.lt_or_ge n i with h | h
  · rw [show n - i = 0 by omega]
    simp only [List.range'_zero, List.filter_nil]
    refine List.filter_eq_nil_iff.mpr ?_
    intro j hj
    have hj' : j ∈ List.range n := List.mem_of_mem_filter hj
    rw [List.mem_range] at hj'
    simp only [decide_eq_true_eq]
    omega
  · have hsplit : List.range n = List.range' 0 i ++ List.range' i (n - i) := by
      rw [List.range_eq_range']
      have hap : List.range' 0 i 1 ++ List.range' (0 + 1 * i) (n - i) 1
          = List.range' 0 (i + (n - i)) 1 := List.range'_append
      simp only [Nat.zero_add, Nat.one_mul] at hap
      rw [hap, show i + (n - i) = n by omega]
    rw [hsplit, List.filter_append, List.filter_append]
    have h1 : (List.filter P (List.range' 0 i)).filter (fun j => decide (i ≤ j)) = [] := by
      refine List.filter_eq_nil_iff.mpr ?_
      intro j hj
      have hj' : j ∈ List.range' 0 i := List.mem_of_mem_filter hj
      rw [List.mem_range'_1] at hj'
      simp only [decide_eq_true_eq]
      omega
    have h2 : (List.filter P (List.range' i (n - i))).filter (fun j => decide (i ≤ j))
        = List.filter P (List.range' i (n - i)) := by
      refine List.filter_eq_self.mpr ?_
      intro j hj
      have hj' : j ∈ List.range' i (n - i) := List.mem_of_mem_filter hj
      rw [List.mem_range'_1] at hj'
      simp only [decide_eq_true_eq]
      omega
    rw [h1, h2, List.nil_append]

/-- **`native_parts::nidx_cons_from` copies a `Vec<NIdx>` onto an accumulator.**
It sits here rather than beside its `_refines` because `native_rec_lps_ok`
needs it and stands EARLIER in `native_parts.rs`, and DESIGN §3.4 keeps the
port's order in the `_refines` file. -/
theorem nidx_cons_from_map {ns : alloc.vec.Vec arena.handle.NIdx} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.handle.NIdx),
      arena.inductives.native_parts.nidx_cons_from ns i out = ok o →
      o.val.map absNIdx = out.val.map absNIdx ++ (ns.val.drop i.val).map absNIdx := by
  refine vec_cursor_copy ns absNIdx absNIdx
    (arena.inductives.native_parts.nidx_cons_from ns) ?_ ?_
  · intro i out o hn h
    rw [arena.inductives.native_parts.nidx_cons_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ns by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    have hlt : i.val < ns.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.inductives.native_parts.nidx_cons_from.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ns by scalar_tac)] at h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnx : n1 = x := by
      have h1 := vec_index_some hn1; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hnx
    exact ⟨i2, n2, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [dupId_nidx _ _ hn2], h⟩

/-- `native_parts::nidx_cons` is the twin's `n :: ns`. -/
theorem nidx_cons_abs {n : arena.handle.NIdx} {ns o : alloc.vec.Vec arena.handle.NIdx}
    (h : arena.inductives.native_parts.nidx_cons n ns = ok o) :
    o.val.map absNIdx = absNIdx n :: ns.val.map absNIdx := by
  rw [arena.inductives.native_parts.nidx_cons] at h
  obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨out, hout, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [nidx_cons_from_map 0#usize out o h]
  simp [ConRon.Refine.vec_push_val hout, alloc.vec.Vec.new, dupId_nidx _ _ hn1,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

/-! ### The declaration copies, and the two readers of a block member

`arena::inductives::modeled` filters and copies a block, so it needs
`i_constant_info_dup` to be the identity on the abstraction and
`i_constant_info_name` to be the twin's `.name`.  `is_rec_info_abs` restates
`Refine2/Checker/Base.lean`'s `is_rec_info_refines`, which is TRUE but stands
above this tier in the module graph (`Checker/Top.lean` imports the inductives,
not the other way round), so it cannot be cited here. -/

-- `i_ind_caps_dup_abs`, `i_proj_table_dup_abs` and `i_constant_info_dup_abs`
-- moved down to `Refine2/Dup.lean` (task #97-P5-Front round 2).

-- `i_constant_info_name_abs` moved down to `Refine2/Checker/Shape.lean`
-- (task #97-P5-Checker round 4).

/-- `arena::checker_base::is_rec_info` ⊑ `isRecInfo`, restated for this tier. -/
theorem is_rec_info_abs {ci : arena.env.IConstantInfo} {o : Bool}
    (h : arena.checker_base.is_rec_info ci = ok o) :
    o = isRecInfo (absIConstantInfo ci) := by
  rw [arena.checker_base.is_rec_info.eq_def] at h
  cases ci <;> (rw [← Result.ok_injective h]; rfl)

/-! ## The STATEFUL cursor recursion, once (round 4; lockstep since task #97-T2-LOCKSTEP)

Round 3 factored the state-free cursor out (`vec_cursor_copy`); the stateful
half of the tier is the same recursion with the store threaded through it —
`if <past the bound> then ok out else <a Sim₀ callee>; push; recurse`.  The
two declarations below are that recursion factored out, so an instance owes
only its own two arms.

Under the lockstep shapes (`AStateRel₀`/`Sim₀`, task #97-T2-LOCKSTEP) there is
nothing to carry across the step: round 4's side condition `Q` (the frozen
tier flag) and its `Ext` re-basing (`AOut.ext_left`) are both gone. -/

/-- **The tier's stateful copier, once.**  `F` runs one `Sim₀` step at the
cursor, pushes its answer and recurses; the answer, READ THROUGH THE
ABSTRACTION, is the accumulator followed by the twin's remaining list action.
The twin side is given as `step`/`rest` indexed by the cursor's VALUE, because
half of this tier's stateful cursors count (`struct_ps_at_from` counts `k` up
to `n_p`) rather than index a `Vec`; `sim_vec_cursor_copy` below is the `Vec`
specialisation. -/
theorem sim_cursor_copy {ι β δ : Type} {pers : arena.store.PersTier}
    (val : ι → Nat) (n : Nat) (f : β → δ)
    (step : Nat → AM δ) (rest : Nat → AM (List δ))
    (F : arena.monad.AState → ι → alloc.vec.Vec β →
      Result ((core.result.Result (alloc.vec.Vec β) kernel.core_types.CheckError)
        × arena.monad.AState))
    (hnil : ∀ m, n ≤ m → rest m = pure [])
    (hcons : ∀ m, m < n →
      rest m = (do let u ← step m; let r ← rest (m + 1); pure (u :: r)))
    (hstop : ∀ st i out o, n ≤ val i → F st i out = ok o →
      o = (core.result.Result.Ok out, st))
    (hstep : ∀ st lst (i : ι) out o, val i < n →
      AStateRel₀ pers st lst → AStateInv pers st → F st i out = ok o →
      ∃ (r : core.result.Result β kernel.core_types.CheckError)
        (st1 : arena.monad.AState),
        Sim₀ f pers lst (r, st1) (step (val i)) ∧
        (∀ u, r = core.result.Result.Ok u →
          ∃ (j : ι) (out1 : alloc.vec.Vec β),
          val j = val i + 1 ∧ out1.val = out.val ++ [u] ∧
            F st1 j out1 = ok o) ∧
        (∀ e, r = core.result.Result.Err e →
          o = (core.result.Result.Err e, st1))) :
    ∀ (i : ι) (out : alloc.vec.Vec β) (st : arena.monad.AState)
      (lst : AState) o,
      AStateRel₀ pers st lst → AStateInv pers st → F st i out = ok o →
      Sim₀ (fun v : alloc.vec.Vec β => v.val.map f) pers lst o
        (do pure (out.val.map f ++ (← rest (val i)))) := by
  refine cursor_induction val n
    (fun i out => ∀ st lst o, AStateRel₀ pers st lst → AStateInv pers st →
      F st i out = ok o →
      Sim₀ (fun v : alloc.vec.Vec β => v.val.map f) pers lst o
        (do pure (out.val.map f ++ (← rest (val i))))) ?_ ?_
  · intro i out hn st lst o hrel hinv h
    rw [hstop st i out o hn h]
    refine Sim₀.mk (AOut₀.ok ?_ hrel hinv)
    simp only [hnil _ hn, am_run_bind]
    simp
    rfl
  · intro i out hi ih st lst o hrel hinv h
    obtain ⟨r, st1, hsim, hok, herr⟩ := hstep st lst i out o hi hrel hinv h
    cases r with
    | Ok u =>
      obtain ⟨lst1, hrun, hrel1, hinv1⟩ := Sim₀.apply hsim
      obtain ⟨j, out1, hj, hout1, hF⟩ := hok u rfl
      have hih := ih j out1 hj st1 lst1 o hrel1 hinv1 hF
      refine Sim₀.mk ?_
      have key : (do pure (out.val.map f ++ (← rest (val i))) : AM (List δ)).run lst
          = (do pure (out1.val.map f ++ (← rest (val j))) : AM (List δ)).run lst1 := by
        rw [hcons _ hi, hj]
        simp only [am_run_bind, hrun, hout1, bind_assoc, List.map_append,
          List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
          List.nil_append]
        rfl
      rw [key]
      exact Sim₀.dest hih
    | Err e =>
      rw [herr e rfl]
      refine AOut₀.err ?_
      rw [hcons _ hi]
      simp only [am_run_bind]
      exact AErrSim.bind (AErrSim.bind (Sim₀.apply_err hsim) _) _

/-- `sim_cursor_copy` at a `Vec` cursor: the step reads `xs` at the cursor and
the twin's remaining action is `G` at the abstracted suffix.  `dflt` is only
the `getD` witness the `Nat`-indexed `step` needs off the end; no conclusion
mentions it. -/
theorem sim_vec_cursor_copy {α α' β δ : Type} {pers : arena.store.PersTier}
    (xs : alloc.vec.Vec α) (dflt : α) (a : α → α') (f : β → δ)
    (g : α' → AM δ) (G : List α' → AM (List δ))
    (F : arena.monad.AState → Std.Usize → alloc.vec.Vec β →
      Result ((core.result.Result (alloc.vec.Vec β) kernel.core_types.CheckError)
        × arena.monad.AState))
    (hnil : G [] = pure [])
    (hcons : ∀ x l, G (x :: l) = (do let u ← g x; let r ← G l; pure (u :: r)))
    (hstop : ∀ st (i : Std.Usize) out o, xs.val.length ≤ i.val → F st i out = ok o →
      o = (core.result.Result.Ok out, st))
    (hstep : ∀ st lst (i : Std.Usize) x out o, xs.val[i.val]? = some x →
      AStateRel₀ pers st lst → AStateInv pers st → F st i out = ok o →
      ∃ (r : core.result.Result β kernel.core_types.CheckError)
        (st1 : arena.monad.AState),
        Sim₀ f pers lst (r, st1) (g (a x)) ∧
        (∀ u, r = core.result.Result.Ok u →
          ∃ (j : Std.Usize) (out1 : alloc.vec.Vec β),
          j.val = i.val + 1 ∧ out1.val = out.val ++ [u] ∧
            F st1 j out1 = ok o) ∧
        (∀ e, r = core.result.Result.Err e →
          o = (core.result.Result.Err e, st1))) :
    ∀ (i : Std.Usize) (out : alloc.vec.Vec β) (st : arena.monad.AState)
      (lst : AState) o,
      AStateRel₀ pers st lst → AStateInv pers st → F st i out = ok o →
      Sim₀ (fun v : alloc.vec.Vec β => v.val.map f) pers lst o
        (do pure (out.val.map f ++ (← G ((xs.val.drop i.val).map a)))) := by
  refine sim_cursor_copy (fun i : Std.Usize => i.val) xs.val.length f
    (fun m => g (a (xs.val.getD m dflt)))
    (fun m => G ((xs.val.drop m).map a)) F ?_ ?_ hstop ?_
  · intro m hm
    rw [List.drop_eq_nil_of_le hm]; simpa using hnil
  · intro m hm
    have hb : m < xs.val.length := hm
    rw [List.drop_eq_getElem_cons hb]
    simp only [List.map_cons, hcons, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hb, Option.getD_some]
  · intro st lst i out o hi hrel hinv h
    obtain ⟨x, hx⟩ : ∃ x, xs.val[i.val]? = some x :=
      ⟨xs.val[i.val], List.getElem?_eq_getElem hi⟩
    have hxv : xs.val.getD i.val dflt = x := by
      simp [List.getD_eq_getElem?_getD, hx]
    rw [hxv]
    exact hstep st lst i x out o hx hrel hinv h

/-! ## The two memo-threading walks' answer relations (task #97-T2-LOCKSTEP)

The tier's three memoised walks (`hasLooseBVarBGo`, `mentionsConstGo`,
`mentionsFvarGo`) answer `(Bool × memo)` on both sides.  Their lockstep
statement is `SimRel₀` at the relation below — the answer bit equal and the two
memos related — which is `ExprOps/Read.lean`'s `WOut`/`LOut` without the
`Ext`/`StoreWF` those carried. -/

/-- The `(handle, depth)`-keyed memo walk's answer relation. -/
def WOutRel (r : Bool × ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool)
    (v : Bool × Std.HashMap (EIdx × Nat) Bool) : Prop :=
  r.1 = v.1 ∧ ExprOps.WMemoRel r.2 v.2

/-- The handle-keyed memo walk's answer relation. -/
def LOutRel (r : Bool × ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
    (v : Bool × Std.HashMap EIdx Bool) : Prop :=
  r.1 = v.1 ∧ ExprOps.LMemoRel r.2 v.2

attribute [simp] absNatL absNatLFrom absBoolL absBoolLFrom absLIdxLL absLIdxLLFrom
  absBinderL absBinderLFrom absCtorsL absCtorsLFrom absCtors3L absCtors3LFrom
  absCtors4L absCtors4LFrom absRecsL absRecsLFrom absRenameTbl
  absRenameTblFrom absRenameBy absInductiveShape absStructParts absRecFieldKind
  absKindL absKindLFrom absKindLL absKindLLFrom absNativeParts

/-! ## Rust-only copies, for the `lockstep` tactic (task #97-T2-LOCKSTEP lane
Inductives round 3)

The two copies `arena::checker::check_ind_decl` makes before it moves its
arguments into the tier: each is the identity on the abstraction. -/

open Lockstep in
@[lockstep] theorem check_mode_dup_spec (m : kernel.env.CheckMode) :
    LSP (kernel.env.check_mode_dup m) (fun o => o = m) := by
  intro o h
  cases m <;> simp only [kernel.env.check_mode_dup, Result.ok.injEq] at h <;> exact h.symm

open Lockstep in
@[lockstep] theorem i_constant_infos_dup_spec (cs : alloc.vec.Vec arena.env.IConstantInfo) :
    LSP (arena.env.i_constant_infos_dup cs) (fun o => absICIL o = absICIL cs) :=
  fun _ h => i_constant_infos_dup_abs h

/-! ## The error constructors, for the `lockstep` tactic

The port builds a decline's error as `invalid (code_points M_…)` (or
`not_implemented`/`internal`) and then `fail`s with it; the twin fails with the
kind and a message string.  The kinds are what `AErrSim` compares, so each
constructor is a Rust-only step whose spec is the constructor itself. -/

open Lockstep in
@[lockstep] theorem core_types_invalid_ls (m : alloc.vec.Vec Std.U32) :
    LSP (kernel.core_types.invalid m) (fun e => e = .Invalid m) := by
  intro e h; simp only [kernel.core_types.invalid, Result.ok.injEq] at h; exact h.symm

open Lockstep in
@[lockstep] theorem core_types_not_implemented_ls (m : alloc.vec.Vec Std.U32) :
    LSP (kernel.core_types.not_implemented m) (fun e => e = .NotImplemented m) := by
  intro e h; simp only [kernel.core_types.not_implemented, Result.ok.injEq] at h
  exact h.symm

open Lockstep in
@[lockstep] theorem core_types_internal_ls (m : alloc.vec.Vec Std.U32) :
    LSP (kernel.core_types.internal m) (fun e => e = .Internal m) := by
  intro e h; simp only [kernel.core_types.internal, Result.ok.injEq] at h; exact h.symm

/-! ## The tier's side-goal extension

A twin `if` over values the port computed in Rust-only steps is decided by
their `TwinEq` facts; those are stated at the port's cursor forms
(`absCtors3LFrom cs 0`, `absNIdxL v`), the twin's at its list forms, so the
tier's extension unfolds `TwinEq` and the abstractions and asks `simp_all`. -/

macro_rules
  | `(tactic| lockstep_side_ext) =>
    `(tactic| ((try simp only [Lockstep.TwinEq] at *); first
      | (simp_all [absNIdxL, absCtors3L, absCtors3LFrom, absCtorsL, absCtorsLFrom,
          absIConstantVal, absICIL, absICILFrom, absEIdxL, absEIdxLFrom, NNodeViewWF]; done)
      | (simp_all [absStructParts, absInductiveShape, absNativeParts, absIRecRule]; done)))

/-- The Core front doors (`Refine2/Checker/KnotHyp.lean`) take `CoreCtx vis rf
lf`; the tier carries `IFEnvRelI rf lf` and, at a split counter, `absU vis =
lf.visibleBelow` — `IFEnvInv.coreCtx`/`coreCtxSelf` turn those into it. -/
macro_rules
  | `(tactic| lockstep_side_ext) =>
    `(tactic| first
      | (apply IFEnvInv.coreCtxSelf <;> first
          | (apply IFEnvRelI.rel; assumption) | (apply IFEnvRelI.inv; assumption))
      | (apply IFEnvInv.coreCtx <;> first
          | (apply IFEnvRelI.rel; assumption) | (apply IFEnvRelI.inv; assumption)
          | assumption | (checker_env_facts; simp_all; done)))


-- A twin `if` whose test a `TwinEq` rewrote to a literal.
attribute [lockstep_simp] ite_true ite_false

/-! ## Two environment-record constants -/

open Lockstep in
/-- `i_ind_caps_default` is the twin's `{}` (the zero word is `default`, the
empty `if_all_zero` is `.ifAllZero []`). -/
@[lockstep] theorem i_ind_caps_default_twin :
    LSP arena.env.i_ind_caps_default (fun o => TwinEq ({} : IIndCaps) (absIIndCaps o)) := by
  intro o h
  simp only [arena.env.i_ind_caps_default, arena.handle.NIdx.of_word,
    kernel.prop_when.if_all_zero, kernel.prop_when.of_repr, alloc.vec.Vec.new,
    alloc.vec.Vec.len] at h
  simp at h
  rw [if_pos (by rfl)] at h
  simp at h
  subst h
  simp [TwinEq, absIIndCaps]
  rfl

open Lockstep in
/-- `checker_base::recs_form_suffix` from the cursor `0`
(`Refine2/Checker/Base.lean`'s `recs_form_suffix_refines`). -/
@[lockstep] theorem recs_form_suffix_twin0 (block : alloc.vec.Vec arena.env.IConstantInfo) :
    LSP (arena.checker_base.recs_form_suffix block 0#usize)
      (fun o => TwinEq (recsFormSuffix (absICIL block)) o) := by
  intro o h
  have h' := recs_form_suffix_refines h
  simpa [TwinEq, absICILFrom, absICIL] using h'.symm

/-! ## The environment index's readers, as `TwinEq`s

`ifenv_find`/`find_ci` read the Rust index; the twin's `find?` is the same
lookup (`ifenv_find_abs`, `Refine2/Core/Arms/Delta.lean`).  The twin
environment is fixed by the `CoreCtx` side goal, which the tier's side
extension discharges from `IFEnvRelI` (and the split counter). -/

open Lockstep in
@[lockstep] theorem ifenv_find_twin {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    (n : arena.handle.NIdx) (hctx : CoreCtx vis rf lf) :
    LSP (arena.env.ifenv_find vis rf n)
      (fun o => TwinEq (lf.find? (absNIdx n)) (o.map absIConstantInfo)) :=
  fun _ h => (ifenv_find_abs hctx h).symm

open Lockstep in
@[lockstep] theorem find_ci_twin {vis : Std.U64} {rf : arena.env.IFEnv} {lf : IFEnv}
    (n : arena.handle.NIdx) (hctx : CoreCtx vis rf lf) :
    LSP (arena.env.find_ci vis rf n)
      (fun o => TwinEq (lf.find? (absNIdx n)) (o.map absIConstantInfo)) := by
  intro o h
  rw [arena.env.find_ci] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hf := ifenv_find_abs hctx hr
  cases r with
  | none =>
    obtain rfl := (Result.ok_injective h).symm
    exact hf.symm
  | some ci =>
    obtain ⟨ii, hii, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain rfl := (Result.ok_injective h).symm
    rw [← hf]
    simp [TwinEq, i_constant_info_dup_abs hii]

-- `lf.restrictTo (absU vis)` at the split counter IS `lf` (`hvis`): the
-- checker tier's statements are at the restriction, the tier's twins at `lf`.
macro_rules
  | `(tactic| lockstep_side_ext) =>
    `(tactic| (simp only [IFEnv.restrictTo] at *; checker_env_facts; simp_all; done))

/-! ## The cursor recipe in `LS` form (task #97-T2-LOCKSTEP lane Inductives round 4)

The Rust walks a `Vec` by an index, the twin recurses structurally on the
list from that index (DESIGN §3.4's `List`-as-cursor deviation).  `ls_cursor`
is the induction once: a caller proves the stop case and the step case, each
by unfolding one equation on each side and `lockstep`, with the induction
hypothesis in the context for the recursive call. -/

open Lockstep in
theorem ls_cursor {α β γ δ : Type} {pers : arena.store.PersTier} {R : γ → δ → Prop}
    (xs : alloc.vec.Vec α) (a : α → β) (G : List β → AM δ)
    (F : arena.monad.AState → Std.Usize →
      Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState))
    (hstop : ∀ st lst (i : Std.Usize), xs.val.length ≤ i.val →
      AStateRel₀ pers st lst → AStateInv pers st → LS pers R (F st i) lst (G []))
    (hstep : ∀ st lst (i : Std.Usize) (hb : i.val < xs.val.length),
      AStateRel₀ pers st lst → AStateInv pers st →
      (∀ st' lst' (j : Std.Usize), j.val = i.val + 1 →
        AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers R (F st' j) lst' (G ((xs.val.drop j.val).map a))) →
      LS pers R (F st i) lst (G (a xs.val[i.val] :: (xs.val.drop (i.val + 1)).map a))) :
    ∀ (i : Std.Usize) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers R (F st i) lst (G ((xs.val.drop i.val).map a)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) xs.val.length
    (fun i (_ : Unit) => ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers R (F st i) lst (G ((xs.val.drop i.val).map a))) ?_ ?_ i ()
  · intro i _ hn st lst hrel hinv
    rw [List.drop_eq_nil_of_le hn, List.map_nil]
    exact hstop st lst i hn hrel hinv
  · intro i _ hi ih st lst hrel hinv
    rw [List.drop_eq_getElem_cons hi, List.map_cons]
    exact hstep st lst i hi hrel hinv (fun st' lst' j hj => ih j () hj st' lst')

open Lockstep in
/-- `ls_cursor` with an accumulator the Rust threads through the cursor walk
(`out`, pushed at each step) and the twin's statement names
(`absXL out ++ (← FSpec (the rest))`): the induction hypothesis is
quantified over the accumulator too. -/
theorem ls_cursor_acc {α β γ δ ω : Type} {pers : arena.store.PersTier} {R : γ → δ → Prop}
    (xs : alloc.vec.Vec α) (a : α → β) (G : ω → List β → AM δ)
    (F : arena.monad.AState → Std.Usize → ω →
      Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState))
    (hstop : ∀ st lst (i : Std.Usize) w, xs.val.length ≤ i.val →
      AStateRel₀ pers st lst → AStateInv pers st → Lockstep.LS pers R (F st i w) lst (G w []))
    (hstep : ∀ st lst (i : Std.Usize) w (hb : i.val < xs.val.length),
      AStateRel₀ pers st lst → AStateInv pers st →
      (∀ st' lst' (j : Std.Usize) w', j.val = i.val + 1 →
        AStateRel₀ pers st' lst' → AStateInv pers st' →
        Lockstep.LS pers R (F st' j w') lst' (G w' ((xs.val.drop j.val).map a))) →
      Lockstep.LS pers R (F st i w) lst
        (G w (a xs.val[i.val] :: (xs.val.drop (i.val + 1)).map a))) :
    ∀ (i : Std.Usize) st lst w, AStateRel₀ pers st lst → AStateInv pers st →
      Lockstep.LS pers R (F st i w) lst (G w ((xs.val.drop i.val).map a)) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) xs.val.length
    (fun i (_ : Unit) => ∀ st lst w, AStateRel₀ pers st lst → AStateInv pers st →
      Lockstep.LS pers R (F st i w) lst (G w ((xs.val.drop i.val).map a))) ?_ ?_ i ()
  · intro i _ hn st lst w hrel hinv
    rw [List.drop_eq_nil_of_le hn, List.map_nil]
    exact hstop st lst i w hn hrel hinv
  · intro i _ hi ih st lst w hrel hinv
    rw [List.drop_eq_getElem_cons hi, List.map_cons]
    exact hstep st lst i w hi hrel hinv (fun st' lst' j w' hj => ih j () hj st' lst' w')

/-! ## The cursor abstractions at `0` (for the `lockstep` side tier)

A caller's twin names the whole list (`absXL v`); the callee's statement is at
the cursor (`absXLFrom v i`) and the port calls it at `0#usize`. -/

@[lockstep_simp] theorem absNIdxLFrom_zero (v) : absNIdxLFrom v 0#usize = absNIdxL v := by
  simp [absNIdxLFrom, absNIdxL]

@[lockstep_simp] theorem absEIdxLFrom_zero (v) : absEIdxLFrom v 0#usize = absEIdxL v := by
  simp [absEIdxLFrom, absEIdxL]

@[lockstep_simp] theorem absLIdxLFrom_zero (v) : absLIdxLFrom v 0#usize = absLIdxL v := by
  simp [absLIdxLFrom, absLIdxL]

@[lockstep_simp] theorem absICILFrom_zero (v) : absICILFrom v 0#usize = absICIL v := by
  simp [absICILFrom, absICIL]

@[lockstep_simp] theorem absNatLFrom_zero (v) : absNatLFrom v 0#usize = absNatL v := by
  simp [absNatLFrom, absNatL]

@[lockstep_simp] theorem absBoolLFrom_zero (v) : absBoolLFrom v 0#usize = absBoolL v := by
  simp [absBoolLFrom, absBoolL]

@[lockstep_simp] theorem absLIdxLLFrom_zero (v) : absLIdxLLFrom v 0#usize = absLIdxLL v := by
  simp [absLIdxLLFrom, absLIdxLL]

@[lockstep_simp] theorem absBinderLFrom_zero (v) : absBinderLFrom v 0#usize = absBinderL v := by
  simp [absBinderLFrom, absBinderL]

@[lockstep_simp] theorem absCtorsLFrom_zero (v) : absCtorsLFrom v 0#usize = absCtorsL v := by
  simp [absCtorsLFrom, absCtorsL]

@[lockstep_simp] theorem absCtors3LFrom_zero (v) : absCtors3LFrom v 0#usize = absCtors3L v := by
  simp [absCtors3LFrom, absCtors3L]

@[lockstep_simp] theorem absCtors4LFrom_zero (v) : absCtors4LFrom v 0#usize = absCtors4L v := by
  simp [absCtors4LFrom, absCtors4L]

@[lockstep_simp] theorem absRecsLFrom_zero (v) : absRecsLFrom v 0#usize = absRecsL v := by
  simp [absRecsLFrom, absRecsL]

@[lockstep_simp] theorem absRenameTblFrom_zero (v) : absRenameTblFrom v 0#usize = absRenameTbl v := by
  simp [absRenameTblFrom, absRenameTbl]

@[lockstep_simp] theorem absKindLFrom_zero (v) : absKindLFrom v 0#usize = absKindL v := by
  simp [absKindLFrom, absKindL]

@[lockstep_simp] theorem absKindLLFrom_zero (v) : absKindLLFrom v 0#usize = absKindLL v := by
  simp [absKindLLFrom, absKindLL]

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.list_allM_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms list_allM_counted

/-- info: 'ConRon.Refine2.vec_cursor_copy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms vec_cursor_copy

/-- info: 'ConRon.Refine2.vec_cursor_any' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms vec_cursor_any

/-- info: 'ConRon.Refine2.nidx_vec_beq_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nidx_vec_beq_abs

/-- info: 'ConRon.Refine2.i_constant_info_dup_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms i_constant_info_dup_abs

/-- info: 'ConRon.Refine2.sim_cursor_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sim_cursor_copy

/-- info: 'ConRon.Refine2.sim_vec_cursor_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sim_vec_cursor_copy

open Lockstep in
/-- `arena::core::nidx_vec_beq` is `==` on the abstracted name lists, for the
Native/Struct/Sum files (`PrimsModeled.lean`'s `nidx_vec_beq_spec` is the same
fact, visible to the modeled route only). -/
@[lockstep] theorem core_nidx_vec_beq_twin (a b : alloc.vec.Vec arena.handle.NIdx) :
    LSP (arena.core.nidx_vec_beq a b) (fun o => o = (absNIdxL a == absNIdxL b)) :=
  fun _ h => nidx_vec_beq_abs h

open Lockstep in
/-- `kernel::expr::binder_meta_dup` is the identity (a Rust-only copy). -/
@[lockstep] theorem binder_meta_dup_spec (m : kernel.expr.BinderMeta) :
    LSP (kernel.expr.binder_meta_dup m) (fun a => a = m) :=
  fun _ h => ConRon.Refine.Expr.binder_meta_dup_eq h

end ConRon.Refine2

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

/-! ## Rule 11 at a COUNTED recursion — the tier's three list closers

DESIGN §3.4 turns every `List` operation of a twin into a named cursor
recursion in the port, and `Refine2/Inductives/Spec.lean` transcribes the twin
side the same way.  So an `_unfold` equation about a twin that calls
`List.allM`, `List.mapM` or `(List.range n).allM` has to say *"the library
fold IS the counted recursion"*, and that is one induction each rather than
one per call site.  Task #97-P5-Checker's **rule 11** (`am_bind_congr` and
`twin_reduce`, `Refine2/Checker/Shape.lean`) is what the step of each needs:
`congr 1` eta-expands the state function instead of peeling the bind.

The three are stated against an ARBITRARY `G` with its two clauses as
hypotheses, so a caller supplies `G := <its transcription>` and discharges
both by `rfl` — which is what makes them one lemma for the whole tier rather
than one per unfold. -/

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

attribute [simp] absNatL absNatLFrom absBoolL absBoolLFrom absLIdxLL absLIdxLLFrom
  absBinderL absBinderLFrom absCtorsL absCtorsLFrom absCtors3L absCtors3LFrom
  absCtors4L absCtors4LFrom absRecsL absRecsLFrom absRenameTbl
  absRenameTblFrom absRenameBy absInductiveShape absStructParts absRecFieldKind
  absKindL absKindLFrom absKindLL absKindLLFrom absNativeParts

end ConRon.Refine2

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

/-! ## The state-free cursor recursion, once

DESIGN §3.4's third rule turns every `List` operation of a twin into a named
cursor recursion over a `Vec`, and the state-free half of this tier is that
recursion fifty-odd times: `if i ≥ len then ok out else <read, transform,
push>; f (i+1) out'`.  Round 2 wrote the measure induction out by hand twice
(`kinds_copy`, `u64_vec_dup`) and measured it at thirty lines; the two
declarations below are that induction factored out, so an instance owes only
its own two arms.

`cursor_induction` is the induction itself and says nothing about `Vec`s —
any recursion whose cursor moves up by one towards a fixed bound is an
instance.  `vec_cursor_copy` is the specialisation every *copier* of the tier
wants: read the source at the cursor, push ONE element computed from it, and
the answer is the accumulator followed by the image of what is left. -/

/-- **The cursor recursion's induction principle.**  A property that holds
past the bound and is preserved backwards by a single step of the cursor holds
everywhere.  The step gets its induction hypothesis for *every* `j` whose
value is `i + 1`, not for one chosen `j`, because the port's `i + 1#usize` is
a `Result` and the successor is only known through `absSz_add_one`. -/
theorem cursor_induction {ι : Type} {γ : Sort u} (val : ι → Nat) (n : Nat)
    (P : ι → γ → Prop)
    (hbase : ∀ (i : ι) (a : γ), n ≤ val i → P i a)
    (hstep : ∀ (i : ι) (a : γ), val i < n →
      (∀ (j : ι) (b : γ), val j = val i + 1 → P j b) → P i a) :
    ∀ (i : ι) (a : γ), P i a := by
  have key : ∀ (k : Nat) (i : ι) (a : γ), n - val i ≤ k → P i a := by
    intro k
    induction k with
    | zero => intro i a hk; exact hbase i a (by omega)
    | succ k ih =>
      intro i a hk
      by_cases h : n ≤ val i
      · exact hbase i a h
      · exact hstep i a (by omega) (fun j b hj => ih j b (by omega))
  intro i a
  exact key (n - val i) i a (Nat.le_refl _)

/-- **The tier's copier, once.**  `F` reads `xs` at the cursor, pushes one
element computed from it, and recurses; the answer, READ THROUGH THE
ABSTRACTION, is the accumulator followed by the image of the suffix.  A caller
supplies the two arms — `hstop` (past the end the accumulator comes back
unchanged) and `hstep` (one element in, one element out, and the pushed
element abstracts to the source element's image) — and gets the measure
induction for free.  The two abstractions `f` and `g` are separate because the
port's element type is often narrower than the source's (`ctors_of` drops a
field, `rhss_of` keeps one), and the conclusion is stated at `List.map`
because every `absXL` of this file is exactly that. -/
theorem vec_cursor_copy {α β δ : Type} (xs : alloc.vec.Vec α) (f : β → δ) (g : α → δ)
    (F : Std.Usize → alloc.vec.Vec β → Result (alloc.vec.Vec β))
    (hstop : ∀ (i : Std.Usize) (out o : alloc.vec.Vec β),
      xs.val.length ≤ i.val → F i out = ok o → o.val = out.val)
    (hstep : ∀ (i : Std.Usize) (x : α) (out o : alloc.vec.Vec β),
      xs.val[i.val]? = some x → F i out = ok o →
      ∃ (j : Std.Usize) (y : β) (out1 : alloc.vec.Vec β),
        j.val = i.val + 1 ∧ out1.val = out.val ++ [y] ∧ f y = g x ∧ F j out1 = ok o) :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec β), F i out = ok o →
      o.val.map f = out.val.map f ++ (xs.val.drop i.val).map g := by
  refine cursor_induction (fun i : Std.Usize => i.val) xs.val.length
    (fun i out => ∀ o, F i out = ok o →
      o.val.map f = out.val.map f ++ (xs.val.drop i.val).map g) ?_ ?_
  · intro i out hn o h
    rw [hstop i out o hn h, List.drop_eq_nil_of_le hn]
    simp
  · intro i out hi ih o h
    obtain ⟨x, hx⟩ : ∃ x, xs.val[i.val]? = some x :=
      ⟨xs.val[i.val], List.getElem?_eq_getElem hi⟩
    obtain ⟨hb, hxv⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨j, y, out1, hj, hout1, hfy, hF⟩ := hstep i x out o hx h
    rw [ih j out1 hj o hF, hout1, hj, List.drop_eq_getElem_cons hb, hxv]
    simp [hfy]

/-- **`arena::env::i_constant_val_dup` is the identity on the abstraction.**
Three `dup2`s and `nidx_vec_dup`, all four of them identities
(`Refine2/Inv.lean`'s `DupId` rows and `Core/Arms/Delta.lean`'s
`nidx_vec_dup_val`).  Six functions of this tier copy a constructor record
and every one of them goes through this. -/
theorem i_constant_val_dup_abs {cv o : arena.env.IConstantVal}
    (h : arena.env.i_constant_val_dup cv = ok o) :
    absIConstantVal o = absIConstantVal cv := by
  rw [arena.env.i_constant_val_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have ho := Result.ok_injective h
  subst ho
  simp only [absIConstantVal, dupId_nidx _ _ hn, dupId_eidx _ _ he,
    nidx_vec_dup_val hv]

/-! ### The four `arena::env` copies this tier inherits

`nidx_vec_dup` and `lidx_vec_dup` already have their identity lemmas
(`Core/Arms/Delta.lean`, `Refine2/Specs.lean`); the other two are stated here,
as the first two instances of `vec_cursor_copy`, because `inductive_shape_dup`
and every `IRecRule` copier of this tier goes through them. -/

private theorem eidx_vec_dup_from_map {es : alloc.vec.Vec arena.handle.EIdx} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.handle.EIdx),
      arena.env.eidx_vec_dup_from es i out = ok o →
      o.val.map id = out.val.map id ++ (es.val.drop i.val).map id := by
  refine vec_cursor_copy es id id (arena.env.eidx_vec_dup_from es) ?_ ?_
  · intro i out o hn h
    rw [arena.env.eidx_vec_dup_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len es by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    have hlt : i.val < es.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.env.eidx_vec_dup_from.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len es by scalar_tac)] at h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hex : e = x := by
      have h1 := vec_index_some he; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    exact ⟨i2, e1, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [← hex, dupId_eidx _ _ he1], h⟩

/-- **`arena::env::eidx_vec_dup` is the identity on the value.** -/
theorem eidx_vec_dup_val {es r : alloc.vec.Vec arena.handle.EIdx}
    (h : arena.env.eidx_vec_dup es = ok r) : r.val = es.val := by
  rw [arena.env.eidx_vec_dup] at h
  have h2 := eidx_vec_dup_from_map 0#usize _ r h
  simpa [alloc.vec.Vec.with_capacity,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using h2

/-- `arena::env::i_rec_rule_fire_dup` is the identity on the abstraction. -/
theorem i_rec_rule_fire_dup_abs {f o : arena.env.IRecRuleFire}
    (h : arena.env.i_rec_rule_fire_dup f = ok o) :
    absIRecRuleFire o = absIRecRuleFire f := by
  rw [arena.env.i_rec_rule_fire_dup.eq_def] at h
  cases f with
  | Inert => rw [Result.ok_injective h]
  | Plain => rw [Result.ok_injective h]
  | Nested lvls pins =>
    simp only [] at h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    simp only [absIRecRuleFire, lidx_vec_dup_eq (by rw [arena.env.lidx_vec_dup] at hv; exact hv),
      eidx_vec_dup_val hv1]

/-- `arena::env::i_rec_rule_dup` is the identity on the abstraction. -/
theorem i_rec_rule_dup_abs {r o : arena.env.IRecRule}
    (h : arena.env.i_rec_rule_dup r = ok o) : absIRecRule o = absIRecRule r := by
  rw [arena.env.i_rec_rule_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨irf, hirf, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]
  simp only [absIRecRule, dupId_nidx _ _ hn, dupId_eidx _ _ he,
    i_rec_rule_fire_dup_abs hirf]

private theorem i_rec_rules_dup_from_map {rs : alloc.vec.Vec arena.env.IRecRule} :
    ∀ (i : Std.Usize) (out o : alloc.vec.Vec arena.env.IRecRule),
      arena.env.i_rec_rules_dup_from rs i out = ok o →
      o.val.map absIRecRule
        = out.val.map absIRecRule ++ (rs.val.drop i.val).map absIRecRule := by
  refine vec_cursor_copy rs absIRecRule absIRecRule
    (arena.env.i_rec_rules_dup_from rs) ?_ ?_
  · intro i out o hn h
    rw [arena.env.i_rec_rules_dup_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len rs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    have hlt : i.val < rs.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.env.i_rec_rules_dup_from.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len rs by scalar_tac)] at h
    obtain ⟨ir, hir, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨ir1, hir1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hex : ir = x := by
      have h1 := vec_index_some hir; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    exact ⟨i2, ir1, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [← hex, i_rec_rule_dup_abs hir1], h⟩

/-- **`arena::env::i_rec_rules_dup` is the identity on the abstraction.** -/
theorem i_rec_rules_dup_abs {rs r : alloc.vec.Vec arena.env.IRecRule}
    (h : arena.env.i_rec_rules_dup rs = ok r) :
    r.val.map absIRecRule = rs.val.map absIRecRule := by
  rw [arena.env.i_rec_rules_dup] at h
  have h2 := i_rec_rules_dup_from_map 0#usize _ r h
  simpa [alloc.vec.Vec.with_capacity,
    show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using h2

attribute [simp] absNatL absNatLFrom absBoolL absBoolLFrom absLIdxLL absLIdxLLFrom
  absBinderL absBinderLFrom absCtorsL absCtorsLFrom absCtors3L absCtors3LFrom
  absCtors4L absCtors4LFrom absRecsL absRecsLFrom absRenameTbl
  absRenameTblFrom absRenameBy absInductiveShape absStructParts absRecFieldKind
  absKindL absKindLFrom absKindLL absKindLLFrom absNativeParts

/-! ## The axiom census -/

/-- info: 'ConRon.Refine2.list_allM_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms list_allM_counted

end ConRon.Refine2

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

/-- **A handle comparison IS the abstraction's.**  `eq2` on an `NIdx` is word
equality and `absNIdx` is injective, so the port's test and the twin's `==`
agree at both signs. -/
theorem nidx_eq2_abs {a b : arena.handle.NIdx} {o : Bool}
    (h : arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = ok o) :
    o = (absNIdx a == absNIdx b) := by
  rw [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  rw [← Result.ok_injective h]
  by_cases hab : a = b
  · subst hab; simp
  · have h1 : a.word ≠ b.word := by
      intro hc; exact hab (by cases a; cases b; simp_all)
    have h2 : absNIdx a ≠ absNIdx b := fun hc => hab (absNIdx_inj hc)
    simp [h1, h2]

/-- The same at an `EIdx`. -/
theorem eidx_eq2_abs {a b : arena.handle.EIdx} {o : Bool}
    (h : arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = ok o) :
    o = (absEIdx a == absEIdx b) := by
  rw [arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  rw [← Result.ok_injective h]
  by_cases hab : a = b
  · subst hab; simp
  · have h1 : a.word ≠ b.word := by
      intro hc; exact hab (by cases a; cases b; simp_all)
    have h2 : absEIdx a ≠ absEIdx b := fun hc => hab (absEIdx_inj hc)
    simp [h1, h2]

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

/-- `arena::env::i_ind_caps_dup` is the identity on the abstraction. -/
theorem i_ind_caps_dup_abs {c o : arena.env.IIndCaps}
    (h : arena.env.i_ind_caps_dup c = ok o) : absIIndCaps o = absIIndCaps c := by
  rw [arena.env.i_ind_caps_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨pw, hpw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]
  simp only [absIIndCaps, dupId_nidx _ _ hn, ConRon.Refine.PropWhen.dup_eq hpw]

/-- `arena::env::i_proj_table_dup` is the identity on the abstraction. -/
theorem i_proj_table_dup_abs {t o : arena.env.IProjTable}
    (h : arena.env.i_proj_table_dup t = ok o) : absIProjTable o = absIProjTable t := by
  rw [arena.env.i_proj_table_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n2, hn2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v2, hv2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h]
  simp only [absIProjTable, dupId_nidx _ _ hn, dupId_nidx _ _ hn1,
    dupId_nidx _ _ hn2, dupId_lidx _ _ hl, nidx_vec_dup_val hv,
    eidx_vec_dup_val hv1,
    lidx_vec_dup_eq (by rw [arena.env.lidx_vec_dup] at hv2; exact hv2)]

/-- **`arena::env::i_constant_info_dup` is the identity on the abstraction.** -/
theorem i_constant_info_dup_abs {c o : arena.env.IConstantInfo}
    (h : arena.env.i_constant_info_dup c = ok o) :
    absIConstantInfo o = absIConstantInfo c := by
  rw [arena.env.i_constant_info_dup.eq_def] at h
  cases c with
  | AxiomInfo cv =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    simp only [absIConstantInfo, i_constant_val_dup_abs hiv]
  | DefnInfo cv v hint =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨rh, hrh, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    have hrhv : rh = hint := by
      rw [kernel.env.reducibility_hint_dup.eq_def] at hrh
      cases hint <;> simp only [] at hrh <;> exact (Result.ok_injective hrh).symm
    simp only [absIConstantInfo, i_constant_val_dup_abs hiv, dupId_eidx _ _ he, hrhv]
  | ThmInfo cv v =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    simp only [absIConstantInfo, i_constant_val_dup_abs hiv, dupId_eidx _ _ he]
  | IndInfo cv caps =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨ic, hic, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    simp only [absIConstantInfo, i_constant_val_dup_abs hiv, i_ind_caps_dup_abs hic]
  | CtorInfo cv a b =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    simp only [absIConstantInfo, i_constant_val_dup_abs hiv]
  | RecInfo cv a b rs =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    simp only [absIConstantInfo, i_constant_val_dup_abs hiv, i_rec_rules_dup_abs hv]
  | ProjInfo t =>
    obtain ⟨it, hit, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
    simp only [absIConstantInfo, i_proj_table_dup_abs hit]

/-- `arena::env::i_constant_info_name` is the twin's `IConstantInfo.name`. -/
theorem i_constant_info_name_abs {c : arena.env.IConstantInfo}
    {o : arena.handle.NIdx} (h : arena.env.i_constant_info_name c = ok o) :
    absNIdx o = (absIConstantInfo c).name := by
  rw [arena.env.i_constant_info_name.eq_def] at h
  cases c <;> simp only [absIConstantInfo, IConstantInfo.name, absIConstantVal,
    absIProjTable, dupId_nidx _ _ h]

/-- `arena::checker_base::is_rec_info` ⊑ `isRecInfo`, restated for this tier. -/
theorem is_rec_info_abs {ci : arena.env.IConstantInfo} {o : Bool}
    (h : arena.checker_base.is_rec_info ci = ok o) :
    o = isRecInfo (absIConstantInfo ci) := by
  rw [arena.checker_base.is_rec_info.eq_def] at h
  cases ci <;> (rw [← Result.ok_injective h]; rfl)

attribute [simp] absNatL absNatLFrom absBoolL absBoolLFrom absLIdxLL absLIdxLLFrom
  absBinderL absBinderLFrom absCtorsL absCtorsLFrom absCtors3L absCtors3LFrom
  absCtors4L absCtors4LFrom absRecsL absRecsLFrom absRenameTbl
  absRenameTblFrom absRenameBy absInductiveShape absStructParts absRecFieldKind
  absKindL absKindLFrom absKindLL absKindLLFrom absNativeParts

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

end ConRon.Refine2

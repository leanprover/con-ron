/-
# `ConRon.Refine2.ExprOps.Pure` — Theorem 2 on the state-free slice of `expr_ops`

**Deliverable 2 of task #97 P5, the part that mentions no store.**  DESIGN.md
§8.2's Theorem 2 for the **22 functions of
`crates/con-ron-core/src/arena/expr_ops.rs` that take neither
`pers: &PersTier` nor an `AState`** — the copying combinators DESIGN §3.3's
deviation 5 and §3.4's no-closure rule force on the port, the three memo
probe/insert pairs extraction rule 5 splits out, and the two level-list
helpers of lesson 4's readback.

These are the cheapest lemmas of the campaign and they are worth isolating:
they carry **no `Sim`, no `AOut` and no `AErrSim`**, because the Rust
functions are `Result R`-valued with no state at all.  The statement is
therefore DESIGN §3.5's original exact-result one —
`f args = ok r → twin (abs args) = abs r` — which `Refine2/Shape.lean` names
`SimP` and which reads better written out.

## What the twin is, per group

| Rust | twin | statement |
|---|---|---|
| `eidx_copy_upto`, `take_eidx`, `last_eidx` | `Arena.{eidxCopyUpto,takeEidx,lastEidx}` | a named `def`, so an equation between `Array EIdx`s |
| `cons_eidx`, `snoc_eidx_of`, `cons_binder`, `binder_copy_from`, `fvl_copy_from`, `fvl_append` | **no named twin** — the twin gets `::` and `++` for free | the LIST equation the call sites use |
| `eidx_take_beq`, `eidx_prefix_beq` | the twin's `args.take want.length == want` | a `↔` on the abstracted lists |
| `wscoped_memo_{get,set}`, `fvl_{seen,record}`, `leaves_sub_{get,set}` | a `Std.HashMap` probe and insert | **relation in, relation out** (`Refine/HashMap2WF.lean`'s `RelOn`) — a `Std.HashMap` is not recoverable from a probe agreement, exactly as `Refine2/AbsStore.lean`'s note says of the cons tables |
| `leaf_mem`, `leaf_mem_from` | `Arena.leafMem` | an equation, the cursor becoming a `List.drop` |
| `expr_ptr_beq` | `Arena.exprPtrBEq` | an equation |
| `subst_level_list{,_from}` | `Arena.substLevelList` | an equation, under `NameWF`/`LevelWF` (the `Level.subst` inside is exact only there — `Refine/Level.lean`'s `subst_use`) |

## What it found

**Three things, and the third is the only one that is not bookkeeping.**

1. **The cursor recursions are one shape and it is `Refine2/Inv.lean`'s.**
   Six of the 22 are `partial_fixpoint` index recursions over a `Vec`
   (`eidx_copy_upto`, `eidx_prefix_beq`, `binder_copy_from`, `fvl_copy_from`,
   `leaf_mem_from`, `subst_level_list_from`).  Each is closed by the same
   ~14-line step: a `Nat` induction on a bound for `len - i`, `eq_def` on the
   recursion, `if_pos`/`if_neg` at `alloc.vec.Vec.len`, and
   `List.drop_eq_getElem_cons` to line the twin's list clause up with the
   Rust's indexed read.  That is round 3's "fuel shape step, twelve lines",
   at a `Vec` cursor instead of a fuel counter, and it is **per function**
   here as it is there.
2. **`Vec::with_capacity` and `Vec::new` are both `[]`**, so the three
   entry points (`take_eidx`, `cons_eidx`, `snoc_eidx_of`) reduce to their
   `_from` helper at `out = []` and cost two lines each.  The capacity is the
   representation difference DESIGN §3.2 says the refinement absorbs, and
   here it absorbs to nothing at all.
3. **The push-order deviation is invisible at this level and must be.**
   `fvar_leaves_go` pushes where the twin conses, so the two lists are each
   other's reverse (the Rust's own doc says so) — but that is
   `fvar_leaves_go`'s deviation, not `fvl_copy_from`'s: the copier is order
   preserving and its lemma says so.  `leaf_mem`, the only reader of the
   accumulated list, is order blind, which is what makes the deviation sound;
   stating `fvl_copy_from`'s lemma order-preservingly leaves that argument to
   the walk's own lemma instead of smuggling it in here.

## Two twin-side lemmas

`eidxCopyUpto_toList` and `leafMem_append` are facts about the TWIN alone (no
Rust in sight).  They are here rather than in `ConRon/Arena/` because they
exist only to state and use these lemmas; Theorem 1's own needs are P3's.
-/
import ConRon.Refine2.Shape
import ConRon.Arena.ExprOps

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.ExprOps

open ConRon.Arena
open ConRon.Refine2
open ConRon.Refine (NameWF LevelWF absName absLevel absNames absLevels
  absBinderMeta)
open ConRon.Refine.HashMap (Eq2Fwd DupId)
open ConRon.Refine.HashMap2 (Inv KeysOk RelOn toFun)

/-! ## The abstractions this slice needs

Four container abstractions, each a `map` over the `Vec`'s list.  The `Array`
form is only for the three functions whose twin really is an `Array`
(`eidxCopyUpto` and its two entry points); everything else states the list. -/

/-- A `Vec<EIdx>` as the twin's `List EIdx`. -/
def absEIdxL (v : alloc.vec.Vec arena.handle.EIdx) : List EIdx := v.val.map absEIdx

/-- A `Vec<EIdx>` as the twin's `Array EIdx` (`eidxCopyUpto`'s container). -/
def absEIdxArr (v : alloc.vec.Vec arena.handle.EIdx) : Array EIdx :=
  (absEIdxL v).toArray

/-- A `Vec<(EIdx, BinderMeta)>` as the twin's `List (EIdx × BinderMeta)` — the
`stripLams`/`stripPis` telescope. -/
def absBinderL (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    List (EIdx × ConLeche.BinderMeta) :=
  v.val.map (fun p => (absEIdx p.1, absBinderMeta p.2))

/-- A `Vec<(u64, EIdx)>` as the twin's `List (Nat × EIdx)` — the `fvar`-leaf
list. -/
def absFvlL (v : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) : List (Nat × EIdx) :=
  v.val.map (fun p => (absU p.1, absEIdx p.2))

/-- A `Vec<Level>` as the twin's `List Level` — `Refine/Abs.lean`'s
`absLevels`, named here for symmetry with the three above. -/
abbrev absLevelL (v : alloc.vec.Vec kernel.level.Level) : List ConLeche.Level :=
  absLevels v

@[simp] theorem absEIdxArr_toList (v) : (absEIdxArr v).toList = absEIdxL v := by
  simp [absEIdxArr]

@[simp] theorem absEIdxArr_size (v) : (absEIdxArr v).size = v.val.length := by
  simp [absEIdxArr, absEIdxL]

@[simp] theorem absEIdxL_length (v) : (absEIdxL v).length = v.val.length := by
  simp [absEIdxL]

@[simp] theorem absBinderL_length (v) : (absBinderL v).length = v.val.length := by
  simp [absBinderL]

@[simp] theorem absFvlL_length (v) : (absFvlL v).length = v.val.length := by
  simp [absFvlL]

/-- The three entry points hand their helper an empty accumulator: both
`Vec::with_capacity` and `Vec::new` are `[]` in the model. -/
@[simp] theorem with_capacity_val {α : Type} (n : Std.Usize) :
    (alloc.vec.Vec.with_capacity α n).val = [] := by
  simp [alloc.vec.Vec.with_capacity]

@[simp] theorem usize_zero_val : ((0#usize : Std.Usize)).val = 0 := by scalar_tac

/-- The twin's array size at the Rust's own `Vec::len`, so that a caller
never has to normalise `↑(Vec.len xs)` first. -/
theorem absEIdxArr_size_len (v : alloc.vec.Vec arena.handle.EIdx) :
    (alloc.vec.Vec.len v).val = (absEIdxArr v).size := by
  simp [absEIdxArr, absEIdxL]

@[simp] theorem absEIdxArr_with_capacity (n : Std.Usize) :
    absEIdxArr (alloc.vec.Vec.with_capacity arena.handle.EIdx n) = #[] := by
  simp [absEIdxArr, absEIdxL]

/-- `Refine/HashMap.lean`'s `vec_index_eq` without the `[Inhabited α]` it asks
for: a generated pair type has no `Inhabited` instance, and `getElem?` needs
none.  (`Refine2/Specs.lean` carries the same four lines under the name
`vec_index_some`; this copy is local so that the two files stay independent
while both are moving.) -/
theorem vecIndexSome {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    v.val[i.val]? = some x := by
  rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize] at h
  rcases hi : v.val[i.val]? with _ | y
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h; simp at h
  · rw [show v[i.val]? = v.val[i.val]? from rfl, hi] at h
    simp only [Result.ok.injEq] at h
    rw [h]

/-- The element at a read index, as an equation on the list. -/
theorem vecIndexAt {α : Type} {v : alloc.vec.Vec α} {i : Std.Usize} {x : α}
    (h : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok x) :
    ∃ hb : i.val < v.val.length, v.val[i.val] = x := by
  have hs := vecIndexSome h
  obtain ⟨hb, hq⟩ := List.getElem?_eq_some_iff.mp hs
  exact ⟨hb, hq⟩

/-! ## Two twin-side lemmas -/

/-- **What `eidxCopyUpto` computes**: the window `[i, k)` of `xs` appended to
the accumulator.  A fact about the twin alone; it is what lets the copying
cons/snoc lemmas below be stated as `::` and `++` rather than as another
`eidxCopyUpto`. -/
theorem eidxCopyUpto_toList (xs : Array EIdx) :
    ∀ (n k i : Nat) (out : Array EIdx), k ≤ i + n →
      (eidxCopyUpto xs k i out).toList
        = out.toList ++ (xs.toList.drop i).take (k - i) := by
  intro n
  induction n with
  | zero =>
    intro k i out hn
    rw [eidxCopyUpto, dif_neg (by omega)]
    rw [show k - i = 0 by omega]
    simp
  | succ n ih =>
    intro k i out hn
    by_cases hc : i < k ∧ i < xs.size
    · rw [eidxCopyUpto, dif_pos hc]
      rw [ih k (i + 1) (out.push xs[i]) (by omega)]
      have hd : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hc.2)]
        simp
      rw [hd, show k - i = (k - (i + 1)) + 1 by omega, List.take_succ_cons]
      simp
    · rw [eidxCopyUpto, dif_neg hc]
      have : (xs.toList.drop i).take (k - i) = [] := by
        rcases Nat.lt_or_ge i k with h1 | h1
        · have h2 : xs.size ≤ i := by
            by_contra hx
            exact hc ⟨h1, by omega⟩
          rw [List.drop_eq_nil_of_le (by simpa using h2)]
          simp
        · rw [show k - i = 0 by omega]; simp
      rw [this]
      simp

/-- `eidxCopyUpto` over the WHOLE of `xs`. -/
theorem eidxCopyUpto_all (xs out : Array EIdx) :
    (eidxCopyUpto xs xs.size 0 out).toList = out.toList ++ xs.toList := by
  rw [eidxCopyUpto_toList xs xs.size xs.size 0 out (by omega)]
  simp

/-- **`leafMem` is order blind and append blind**, which is what a membership
base wants: this is the clause the cursor recursion's lemma lands in. -/
theorem leafMem_cons (p : Nat × EIdx) (rest : List (Nat × EIdx)) (idx : Nat)
    (ty : EIdx) :
    leafMem (p :: rest) idx ty = ((p.1 == idx && p.2 == ty) || leafMem rest idx ty) := by
  obtain ⟨i, t⟩ := p
  rw [leafMem]

/-! ## `eidx_copy_upto` and its three entry points -/

/-- **The cursor shape step**, once: an induction on a bound for `k - i`, the
`eq_def` of the `partial_fixpoint`, and the two `Vec.len` tests.  Five more of
this file's lemmas are the same fourteen lines at a different body. -/
theorem eidx_copy_upto_aux (xs : alloc.vec.Vec arena.handle.EIdx) (k : Std.Usize) :
    ∀ (n : Nat) (i : Std.Usize) (out r : alloc.vec.Vec arena.handle.EIdx),
      k.val ≤ i.val + n →
      arena.expr_ops.eidx_copy_upto xs k i out = ok r →
      (eidxCopyUpto (absEIdxArr xs) k.val i.val (absEIdxArr out)).toList
        = absEIdxL r := by
  intro n
  induction n with
  | zero =>
    intro i out r hn h
    rw [arena.expr_ops.eidx_copy_upto.eq_def] at h
    rw [if_pos (show i ≥ k by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [eidxCopyUpto, dif_neg (by omega)]
    simp
  | succ n ih =>
    intro i out r hn h
    rw [arena.expr_ops.eidx_copy_upto.eq_def] at h
    by_cases hk : i.val ≥ k.val
    · rw [if_pos (show i ≥ k by scalar_tac), Result.ok.injEq] at h
      subst h
      rw [eidxCopyUpto, dif_neg (by omega)]
      simp
    · rw [if_neg (show ¬ i ≥ k by scalar_tac)] at h
      by_cases hx : i.val ≥ xs.val.length
      · rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
        subst h
        rw [eidxCopyUpto, dif_neg (by simp; omega)]
        simp
      · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
        have hxi : i.val < xs.val.length := by omega
        obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨hb, hev⟩ := vecIndexAt he
        have hee : e1 = e := dupId_eidx e e1 he1
        have hpv : out1.val = out.val ++ [e1] := ConRon.Refine.vec_push_val hout1
        have hi2v : i2.val = i.val + 1 :=
          (ConRon.Refine.Nat.uadd_val hi2).trans (by simp)
        rw [eidxCopyUpto,
          dif_pos (show i.val < k.val ∧ i.val < (absEIdxArr xs).size from
            ⟨by omega, by simpa using hxi⟩)]
        have hih := ih i2 out1 r (by omega) h
        rw [hi2v] at hih
        rw [← hih]
        congr 1
        apply Array.ext'
        simp [absEIdxArr, absEIdxL, hpv, hee, ← hev]

theorem eidx_copy_upto_refines {xs : alloc.vec.Vec arena.handle.EIdx}
    {k i : Std.Usize} {out r : alloc.vec.Vec arena.handle.EIdx}
    (h : arena.expr_ops.eidx_copy_upto xs k i out = ok r) :
    (eidxCopyUpto (absEIdxArr xs) k.val i.val (absEIdxArr out)).toList = absEIdxL r :=
  eidx_copy_upto_aux xs k k.val i out r (by omega) h

theorem take_eidx_refines {xs : alloc.vec.Vec arena.handle.EIdx} {k : Std.Usize}
    {r : alloc.vec.Vec arena.handle.EIdx}
    (h : arena.expr_ops.take_eidx xs k = ok r) :
    (takeEidx (absEIdxArr xs) k.val).toList = absEIdxL r := by
  rw [arena.expr_ops.take_eidx] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have he := eidx_copy_upto_refines h
  rw [absEIdxArr_with_capacity, usize_zero_val] at he
  rw [takeEidx, he]

theorem last_eidx_refines {xs : alloc.vec.Vec arena.handle.EIdx} {k : Std.Usize}
    {r : alloc.vec.Vec arena.handle.EIdx}
    (h : arena.expr_ops.last_eidx xs k = ok r) :
    (lastEidx (absEIdxArr xs) k.val).toList = absEIdxL r := by
  rw [arena.expr_ops.last_eidx] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨m, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hnv : n.val = if k.val < xs.val.length then xs.val.length - k.val else 0 := by
    by_cases hc : k.val < xs.val.length
    · rw [if_pos (show k < alloc.vec.Vec.len xs by scalar_tac)] at hn
      obtain ⟨-, hv⟩ := ConRon.Refine.Nat.usub_val hn
      rw [if_pos hc]; simpa using hv
    · rw [if_neg (show ¬ k < alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at hn
      subst hn
      rw [if_neg hc]; simp
  have he := eidx_copy_upto_refines h
  rw [absEIdxArr_with_capacity] at he
  simp only [alloc.vec.Vec.len_val] at he
  rw [lastEidx, absEIdxArr_size, ← hnv]
  exact he

/-! ## The copying cons and snoc: no named twin, so the LIST equation -/

theorem cons_eidx_refines {a : arena.handle.EIdx}
    {xs r : alloc.vec.Vec arena.handle.EIdx}
    (h : arena.expr_ops.cons_eidx a xs = ok r) :
    absEIdxL r = absEIdx a :: absEIdxL xs := by
  rw [arena.expr_ops.cons_eidx] at h
  obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hee : e = a := dupId_eidx a e he
  have hpv : out1.val = [e] := by
    have hp := ConRon.Refine.vec_push_val hout1
    simpa using hp
  have hc := eidx_copy_upto_refines h
  rw [absEIdxArr_size_len xs, usize_zero_val, eidxCopyUpto_all] at hc
  rw [← hc]
  simp [absEIdxArr, absEIdxL, hpv, hee]

theorem snoc_eidx_of_refines {xs r : alloc.vec.Vec arena.handle.EIdx}
    {y : arena.handle.EIdx}
    (h : arena.expr_ops.snoc_eidx_of xs y = ok r) :
    absEIdxL r = absEIdxL xs ++ [absEIdx y] := by
  rw [arena.expr_ops.snoc_eidx_of] at h
  obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hee : e = y := dupId_eidx y e he
  have hc := eidx_copy_upto_refines hout1
  rw [absEIdxArr_size_len xs, usize_zero_val, absEIdxArr_with_capacity,
    eidxCopyUpto_all] at hc
  have hout : out1.val.map absEIdx = xs.val.map absEIdx := by
    have hq := hc.symm
    simpa [absEIdxArr, absEIdxL] using hq
  have hrv : r.val = out1.val ++ [e] := ConRon.Refine.vec_push_val h
  simp [absEIdxL, hrv, hee, hout]

/-! ## The prefix comparison -/

/-- The cursor form: `want`'s entries from `i` on agree with `args`'. -/
theorem eidx_prefix_beq_aux (args want : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (n : Nat) (i : Std.Usize) (r : Bool),
      want.val.length ≤ i.val + n →
      arena.expr_ops.eidx_prefix_beq args want i = ok r →
      (r = true ↔ ∀ j, i.val ≤ j → j < want.val.length →
        (absEIdxL args)[j]? = (absEIdxL want)[j]?) := by
  intro n
  induction n with
  | zero =>
    intro i r hn h
    rw [arena.expr_ops.eidx_prefix_beq.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len want by scalar_tac), Result.ok.injEq] at h
    subst h
    simp only [true_iff]
    intro j hj1 hj2
    omega
  | succ n ih =>
    intro i r hn h
    rw [arena.expr_ops.eidx_prefix_beq.eq_def] at h
    by_cases hw : i.val ≥ want.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len want by scalar_tac), Result.ok.injEq] at h
      subst h
      simp only [true_iff]
      intro j hj1 hj2
      omega
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len want by scalar_tac)] at h
      have hwi : i.val < want.val.length := by omega
      obtain ⟨a, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨w, hw2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hab, hav⟩ := vecIndexAt ha
      obtain ⟨hwb, hwv⟩ := vecIndexAt hw2
      have hbv : b = decide (a = w) := eidx_eq2 a w b trivial trivial hb
      have hkey : (absEIdxL args)[i.val]? = (absEIdxL want)[i.val]? ↔ a = w := by
        rw [absEIdxL, absEIdxL, List.getElem?_map, List.getElem?_map,
          List.getElem?_eq_getElem hab, List.getElem?_eq_getElem hwb, hav, hwv]
        simp only [Option.map_some, Option.some.injEq]
        exact ⟨fun hc => absEIdx_inj hc, fun hc => by rw [hc]⟩
      by_cases hc : a = w
      · rw [hbv, decide_eq_true hc, if_pos rfl] at h
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 :=
          (ConRon.Refine.Nat.uadd_val hi2).trans (by simp)
        have hih := ih i2 r (by omega) h
        rw [hih]
        constructor
        · intro hall j hj1 hj2
          rcases Nat.lt_or_ge j i.val with h1 | h1
          · omega
          · rcases Nat.eq_or_lt_of_le h1 with h2 | h2
            · rw [← h2]; exact hkey.mpr hc
            · exact hall j (by omega) hj2
        · intro hall j hj1 hj2
          exact hall j (by omega) hj2
      · rw [hbv, decide_eq_false hc, if_neg (by simp), Result.ok.injEq] at h
        subst h
        simp only [Bool.false_eq_true, false_iff]
        intro hall
        exact hc (hkey.mp (hall i.val (by omega) hwi))

theorem eidx_prefix_beq_refines {args want : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize} {r : Bool}
    (h : arena.expr_ops.eidx_prefix_beq args want i = ok r) :
    r = true ↔ ∀ j, i.val ≤ j → j < want.val.length →
      (absEIdxL args)[j]? = (absEIdxL want)[j]? :=
  eidx_prefix_beq_aux args want want.val.length i r (by omega) h

/-- The twin's `args.take want.length == want`: the port's length test plus
the elementwise walk. -/
theorem eidx_take_beq_refines {args want : alloc.vec.Vec arena.handle.EIdx}
    {r : Bool} (h : arena.expr_ops.eidx_take_beq args want = ok r) :
    r = true ↔ (absEIdxL args).take (absEIdxL want).length = absEIdxL want := by
  rw [arena.expr_ops.eidx_take_beq] at h
  by_cases hc : args.val.length < want.val.length
  · rw [if_pos (show alloc.vec.Vec.len args < alloc.vec.Vec.len want by scalar_tac),
      Result.ok.injEq] at h
    subst h
    simp only [Bool.false_eq_true, false_iff]
    intro heq
    have h1 := congrArg List.length heq
    simp only [List.length_take, absEIdxL_length] at h1
    omega
  · rw [if_neg (show ¬ alloc.vec.Vec.len args < alloc.vec.Vec.len want by scalar_tac)] at h
    rw [eidx_prefix_beq_refines h]
    simp only [absEIdxL_length]
    constructor
    · intro hall
      apply List.ext_getElem?
      intro j
      rcases Nat.lt_or_ge j want.val.length with h1 | h1
      · rw [List.getElem?_take_of_lt h1, hall j (by simp) h1]
      · rw [List.getElem?_eq_none (by simp; omega),
          List.getElem?_eq_none (by simp; omega)]
    · intro heq j hj1 hj2
      have hq : ((absEIdxL args).take want.val.length)[j]? = (absEIdxL want)[j]? := by
        rw [heq]
      rw [List.getElem?_take_of_lt hj2] at hq
      exact hq

/-! ## `take_eidx_n`: the prefix at a machine-word count -/

theorem take_eidx_n_from_aux (xs : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (k : Nat) (c : Std.U64) (i : Std.Usize) (out r : alloc.vec.Vec arena.handle.EIdx),
      xs.val.length ≤ i.val + k →
      arena.expr_ops.take_eidx_n_from xs c i out = ok r →
      absEIdxL r = absEIdxL out ++ ((absEIdxL xs).drop i.val).take c.val := by
  intro k
  induction k with
  | zero =>
    intro c i out r hk h
    rw [arena.expr_ops.take_eidx_n_from.eq_def] at h
    have hd : (absEIdxL xs).drop i.val = [] := List.drop_eq_nil_of_le (by simp [absEIdxL]; omega)
    rw [hd]
    split at h
    · rw [Result.ok.injEq] at h; subst h; simp
    · rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
      subst h; simp
  | succ k ih =>
    intro c i out r hk h
    rw [arena.expr_ops.take_eidx_n_from.eq_def] at h
    split at h
    · rename_i hc
      rw [Result.ok.injEq] at h; subst h; subst hc; simp
    · rename_i hc
      by_cases hx : i.val ≥ xs.val.length
      · rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
        subst h
        rw [List.drop_eq_nil_of_le (by simp [absEIdxL]; omega)]
        simp
      · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
        have hxi : i.val < xs.val.length := by omega
        obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨c2, hc2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨hb, hpv⟩ := vecIndexAt he
        have hee : e1 = e := dupId_eidx e e1 he1
        have hov : out1.val = out.val ++ [e1] := ConRon.Refine.vec_push_val hout1
        have hc0 : c.val ≠ 0 := fun h0 => hc (Std.UScalar.eq_of_val_eq (by simpa using h0))
        have hc2v : c2.val = c.val - 1 := (ConRon.Refine.Nat.usub_val hc2).2
        have hi2v : i2.val = i.val + 1 :=
          (ConRon.Refine.Nat.uadd_val hi2).trans (by simp)
        have hih := ih c2 i2 out1 r (by omega) h
        rw [hih, hi2v, hc2v]
        have hd : (absEIdxL xs).drop i.val
            = absEIdx e :: (absEIdxL xs).drop (i.val + 1) := by
          rw [List.drop_eq_getElem_cons (by simpa [absEIdxL] using hxi)]
          simp only [absEIdxL, List.getElem_map, hpv]
        have hob : absEIdxL out1 = absEIdxL out ++ [absEIdx e] := by
          simp [absEIdxL, hov, hee]
        rw [hd, hob]
        obtain ⟨c', hc'⟩ : ∃ c', c.val = c' + 1 := ⟨c.val - 1, by omega⟩
        rw [hc', List.take_succ_cons]
        simp

theorem take_eidx_n_refines {xs : alloc.vec.Vec arena.handle.EIdx} {c : Std.U64}
    {r : alloc.vec.Vec arena.handle.EIdx}
    (h : arena.expr_ops.take_eidx_n xs c = ok r) :
    absEIdxL r = (absEIdxL xs).take c.val := by
  rw [arena.expr_ops.take_eidx_n] at h
  have := take_eidx_n_from_aux xs xs.val.length c 0#usize _ r (by simp) h
  simpa [absEIdxL] using this

/-! ## The binder telescope's cons -/

theorem binder_copy_from_aux
    (xs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) :
    ∀ (n : Nat) (i : Std.Usize)
      (out r : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)),
      xs.val.length ≤ i.val + n →
      arena.expr_ops.binder_copy_from xs i out = ok r →
      absBinderL r = absBinderL out ++ (absBinderL xs).drop i.val := by
  intro n
  induction n with
  | zero =>
    intro i out r hn h
    rw [arena.expr_ops.binder_copy_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le (by simp; omega)]
    simp
  | succ n ih =>
    intro i out r hn h
    rw [arena.expr_ops.binder_copy_from.eq_def] at h
    by_cases hx : i.val ≥ xs.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le (by simp; omega)]
      simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
      have hxi : i.val < xs.val.length := by omega
      obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨e, bm⟩ := p
      obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨bm1, hbm1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hb, hpv⟩ := vecIndexAt hp
      have hee : e1 = e := dupId_eidx e e1 he1
      have hbb : bm1 = bm := ConRon.Refine.Expr.binder_meta_dup_eq hbm1
      have hov : out1.val = out.val ++ [(e1, bm1)] := ConRon.Refine.vec_push_val hout1
      have hi2v : i2.val = i.val + 1 :=
        (ConRon.Refine.Nat.uadd_val hi2).trans (by simp)
      have hih := ih i2 out1 r (by omega) h
      rw [hih, hi2v]
      have hd : (absBinderL xs).drop i.val
          = (absEIdx e, absBinderMeta bm) :: (absBinderL xs).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hxi)]
        simp only [absBinderL, List.getElem_map, hpv]
      have hob : absBinderL out1
          = absBinderL out ++ [(absEIdx e, absBinderMeta bm)] := by
        simp [absBinderL, hov, hee, hbb]
      rw [hd, hob]
      simp

theorem binder_copy_from_refines
    {xs out r : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {i : Std.Usize}
    (h : arena.expr_ops.binder_copy_from xs i out = ok r) :
    absBinderL r = absBinderL out ++ (absBinderL xs).drop i.val :=
  binder_copy_from_aux xs xs.val.length i out r (by omega) h

theorem cons_binder_refines {ty : arena.handle.EIdx} {m : kernel.expr.BinderMeta}
    {xs r : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    (h : arena.expr_ops.cons_binder ty m xs = ok r) :
    absBinderL r = (absEIdx ty, absBinderMeta m) :: absBinderL xs := by
  rw [arena.expr_ops.cons_binder] at h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨bm, hbm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨out, hout, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hee : e = ty := dupId_eidx ty e he
  have hbb : bm = m := ConRon.Refine.Expr.binder_meta_dup_eq hbm
  have hov : out.val = [(e, bm)] := ConRon.Refine.push_new_val hout
  rw [binder_copy_from_refines h]
  simp [absBinderL, hov, hee, hbb]

/-! ## The `fvar`-leaf list's append -/

theorem fvl_copy_from_aux (xs : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)) :
    ∀ (n : Nat) (i : Std.Usize)
      (out r : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)),
      xs.val.length ≤ i.val + n →
      arena.expr_ops.fvl_copy_from xs i out = ok r →
      absFvlL r = absFvlL out ++ (absFvlL xs).drop i.val := by
  intro n
  induction n with
  | zero =>
    intro i out r hn h
    rw [arena.expr_ops.fvl_copy_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le (by simp; omega)]
    simp
  | succ n ih =>
    intro i out r hn h
    rw [arena.expr_ops.fvl_copy_from.eq_def] at h
    by_cases hx : i.val ≥ xs.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le (by simp; omega)]
      simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)] at h
      have hxi : i.val < xs.val.length := by omega
      obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, e⟩ := p
      obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hb, hpv⟩ := vecIndexAt hp
      have hee : e1 = e := dupId_eidx e e1 he1
      have hov : out1.val = out.val ++ [(i2, e1)] := ConRon.Refine.vec_push_val hout1
      have hi3v : i3.val = i.val + 1 :=
        (ConRon.Refine.Nat.uadd_val hi3).trans (by simp)
      have hih := ih i3 out1 r (by omega) h
      rw [hih, hi3v]
      have hd : (absFvlL xs).drop i.val
          = (absU i2, absEIdx e) :: (absFvlL xs).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hxi)]
        simp only [absFvlL, List.getElem_map, hpv]
      have hob : absFvlL out1 = absFvlL out ++ [(absU i2, absEIdx e)] := by
        simp [absFvlL, hov, hee]
      rw [hd, hob]
      simp

theorem fvl_copy_from_refines
    {xs out r : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)} {i : Std.Usize}
    (h : arena.expr_ops.fvl_copy_from xs i out = ok r) :
    absFvlL r = absFvlL out ++ (absFvlL xs).drop i.val :=
  fvl_copy_from_aux xs xs.val.length i out r (by omega) h

theorem fvl_append_refines {x y r : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)}
    (h : arena.expr_ops.fvl_append x y = ok r) :
    absFvlL r = absFvlL x ++ absFvlL y := by
  rw [arena.expr_ops.fvl_append] at h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h1 := fvl_copy_from_refines hv
  have h2 := fvl_copy_from_refines h
  rw [h2, h1]
  simp [absFvlL]

/-! ## The three memo probe/insert pairs

Relation in, relation out.  Each `get` is `Refine/HashMap2WF.lean`'s
`Rel_get_wf` at the key predicate `True` (the keys are handles and a `u64`
cursor, so `Refine2/AbsState.lean`'s `eidxNat_eq2` / `eidx_eq2` are
unrestricted), and each `insert` is `Rel_insert_wf` plus the `Inv` its first
component carries. -/

/-! ## The memo relations (finding 2, and finding 3 for `SeenRel`) -/

/-- `wscoped_b_go`'s memo, keyed on `(handle, depth)`. -/
def WMemoRel (rm : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool)
    (lm : Std.HashMap (EIdx × Nat) Bool) : Prop :=
  RelOn (fun _ => True) rm lm absEIdxNat id ∧
    Inv arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable rm

/-- `leaves_sub_go`'s memo, keyed on the handle alone (`bl` is fixed for the
call, which is why it is not in the key). -/
def LMemoRel (rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
    (lm : Std.HashMap EIdx Bool) : Prop :=
  RelOn (fun _ => True) rm lm absEIdx id ∧
    Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable rm

/-- `fvar_leaves_go`'s `seen` set.  **Membership, not value** (finding 3): the
Rust's table is `bool`-valued and the twin's `Unit`-valued, and no reader
looks at either value — which is what `RelOn` at the value abstraction
`fun _ => ()` says, and stating it that way (rather than as an `isSome`
agreement) is what lets `Refine/HashMap2WF.lean`'s kit apply unchanged. -/
def SeenRel (rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
    (lm : Std.HashMap EIdx Unit) : Prop :=
  RelOn (fun _ => True) rm lm absEIdx (fun _ => ()) ∧
    Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable rm

theorem wscoped_memo_get_refines
    {memo : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lmemo : Std.HashMap (EIdx × Nat) Bool} {k : arena.monad.EIdxNat}
    {o : Option Bool}
    (hinv : Inv arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable memo)
    (hkeys : KeysOk (fun _ => True) memo)
    (hrel : RelOn (fun _ => True) memo lmemo absEIdxNat id)
    (h : arena.expr_ops.wscoped_memo_get memo k = ok o) :
    lmemo[absEIdxNat k]? = o := by
  rw [arena.expr_ops.wscoped_memo_get] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hg := ConRon.Refine.HashMap2.Rel_get_wf eidxNat_eq2 hinv hkeys hrel trivial hr
  cases hrc : r with
  | none =>
    rw [hrc] at h hg
    have h2 : (none : Option Bool) = o := Result.ok_injective h
    rw [← h2, ← hg]; rfl
  | some b =>
    rw [hrc] at h hg
    have h2 : some b = o := Result.ok_injective h
    rw [← h2, ← hg]; rfl

theorem wscoped_memo_set_refines
    {memo m' : ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool}
    {lmemo : Std.HashMap (EIdx × Nat) Bool} {k : arena.monad.EIdxNat} {r : Bool}
    (hinv : Inv arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable memo)
    (hkeys : KeysOk (fun _ => True) memo)
    (hrel : RelOn (fun _ => True) memo lmemo absEIdxNat id)
    (h : arena.expr_ops.wscoped_memo_set memo k r = ok m') :
    RelOn (fun _ => True) m' (lmemo.insert (absEIdxNat k) r) absEIdxNat id ∧
      Inv arena.monad.EIdxNat.Insts.Con_ron_coreRonHashmapHashable m' ∧
      KeysOk (fun _ => True) m' := by
  rw [arena.expr_ops.wscoped_memo_set] at h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨old, m2⟩ := p
  have h2 : m2 = m' := Result.ok_injective h
  subst h2
  have hinj : ∀ a b : arena.monad.EIdxNat, True → True →
      absEIdxNat a = absEIdxNat b → a = b := by
    intro a b _ _ hab
    obtain ⟨⟨wa⟩, da⟩ := a; obtain ⟨⟨wb⟩, db⟩ := b
    simp only [absEIdxNat, absEIdx, Prod.mk.injEq, Idx.ofWord.injEq] at hab
    have hw : wa = wb := absU32_inj hab.1
    have hd : da = db := Std.UScalar.eq_imp _ _ hab.2
    rw [hw, hd]
  obtain ⟨hrel', hkeys'⟩ :=
    ConRon.Refine.HashMap2.Rel_insert_wf eidxNat_eq2 hinj hinv hkeys hrel trivial hp
  refine ⟨hrel', ?_, hkeys'⟩
  exact (ConRon.Refine.HashMap2.insert_refines_wf eidxNat_eq2 hinv hkeys trivial hp).1

theorem fvl_seen_refines {seen : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lseen : Std.HashMap EIdx Unit} {h0 : arena.handle.EIdx} {b : Bool}
    (hinv : Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable seen)
    (hkeys : KeysOk (fun _ => True) seen)
    (hrel : RelOn (fun _ => True) seen lseen absEIdx (fun _ => ()))
    (h : arena.expr_ops.fvl_seen seen h0 = ok b) :
    b = lseen.contains (absEIdx h0) := by
  rw [arena.expr_ops.fvl_seen] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hg := ConRon.Refine.HashMap2.Rel_get_wf eidx_eq2 hinv hkeys hrel trivial hr
  rw [Std.HashMap.contains_eq_isSome_getElem?, ← hg]
  cases hrc : r with
  | none =>
    rw [hrc] at h
    have h2 : false = b := Result.ok_injective h
    rw [← h2]; simp
  | some v =>
    rw [hrc] at h
    have h2 : true = b := Result.ok_injective h
    rw [← h2]; simp

theorem fvl_record_refines {seen m' : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lseen : Std.HashMap EIdx Unit} {h0 : arena.handle.EIdx}
    (hinv : Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable seen)
    (hkeys : KeysOk (fun _ => True) seen)
    (hrel : RelOn (fun _ => True) seen lseen absEIdx (fun _ => ()))
    (h : arena.expr_ops.fvl_record seen h0 = ok m') :
    RelOn (fun _ => True) m' (lseen.insert (absEIdx h0) ()) absEIdx (fun _ => ()) ∧
      Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable m' ∧
      KeysOk (fun _ => True) m' := by
  rw [arena.expr_ops.fvl_record] at h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨old, m2⟩ := p
  have h2 : m2 = m' := Result.ok_injective h
  subst h2
  have hee : e = h0 := dupId_eidx h0 e he
  subst hee
  have hinj : ∀ a b : arena.handle.EIdx, True → True → absEIdx a = absEIdx b → a = b :=
    fun a b _ _ hab => absEIdx_inj hab
  obtain ⟨hrel', hkeys'⟩ :=
    ConRon.Refine.HashMap2.Rel_insert_wf eidx_eq2 hinj hinv hkeys hrel trivial hp
  refine ⟨hrel', ?_, hkeys'⟩
  exact (ConRon.Refine.HashMap2.insert_refines_wf eidx_eq2 hinv hkeys trivial hp).1

theorem leaves_sub_get_refines
    {memo : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lmemo : Std.HashMap EIdx Bool} {h0 : arena.handle.EIdx} {o : Option Bool}
    (hinv : Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable memo)
    (hkeys : KeysOk (fun _ => True) memo)
    (hrel : RelOn (fun _ => True) memo lmemo absEIdx id)
    (h : arena.expr_ops.leaves_sub_get memo h0 = ok o) :
    lmemo[absEIdx h0]? = o := by
  rw [arena.expr_ops.leaves_sub_get] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hg := ConRon.Refine.HashMap2.Rel_get_wf eidx_eq2 hinv hkeys hrel trivial hr
  cases hrc : r with
  | none =>
    rw [hrc] at h hg
    have h2 : (none : Option Bool) = o := Result.ok_injective h
    rw [← h2, ← hg]; rfl
  | some b =>
    rw [hrc] at h hg
    have h2 : some b = o := Result.ok_injective h
    rw [← h2, ← hg]; rfl

theorem leaves_sub_set_refines
    {memo m' : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lmemo : Std.HashMap EIdx Bool} {h0 : arena.handle.EIdx} {r : Bool}
    (hinv : Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable memo)
    (hkeys : KeysOk (fun _ => True) memo)
    (hrel : RelOn (fun _ => True) memo lmemo absEIdx id)
    (h : arena.expr_ops.leaves_sub_set memo h0 r = ok m') :
    RelOn (fun _ => True) m' (lmemo.insert (absEIdx h0) r) absEIdx id ∧
      Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable m' ∧
      KeysOk (fun _ => True) m' := by
  rw [arena.expr_ops.leaves_sub_set] at h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨old, m2⟩ := p
  have h2 : m2 = m' := Result.ok_injective h
  subst h2
  have hee : e = h0 := dupId_eidx h0 e he
  subst hee
  have hinj : ∀ a b : arena.handle.EIdx, True → True → absEIdx a = absEIdx b → a = b :=
    fun a b _ _ hab => absEIdx_inj hab
  obtain ⟨hrel', hkeys'⟩ :=
    ConRon.Refine.HashMap2.Rel_insert_wf eidx_eq2 hinj hinv hkeys hrel trivial hp
  refine ⟨hrel', ?_, hkeys'⟩
  exact (ConRon.Refine.HashMap2.insert_refines_wf eidx_eq2 hinv hkeys trivial hp).1

/-! ## The leaf-membership test -/

theorem leaf_mem_from_aux (bl : alloc.vec.Vec (Std.U64 × arena.handle.EIdx))
    (idx : Std.U64) (ty : arena.handle.EIdx) :
    ∀ (n : Nat) (i : Std.Usize) (r : Bool),
      bl.val.length ≤ i.val + n →
      arena.expr_ops.leaf_mem_from bl idx ty i = ok r →
      leafMem ((absFvlL bl).drop i.val) (absU idx) (absEIdx ty) = r := by
  intro n
  induction n with
  | zero =>
    intro i r hn h
    rw [arena.expr_ops.leaf_mem_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len bl by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le (by simp; omega), leafMem]
  | succ n ih =>
    intro i r hn h
    rw [arena.expr_ops.leaf_mem_from.eq_def] at h
    by_cases hx : i.val ≥ bl.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len bl by scalar_tac), Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le (by simp; omega), leafMem]
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len bl by scalar_tac)] at h
      have hxi : i.val < bl.val.length := by omega
      obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, e⟩ := p
      obtain ⟨hb, hpv⟩ := vecIndexAt hp
      have hd : (absFvlL bl).drop i.val
          = (absU i2, absEIdx e) :: (absFvlL bl).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hxi)]
        simp only [absFvlL, List.getElem_map, hpv]
      rw [hd, leafMem_cons]
      rcases ConRon.Refine.HashMap2.ite_eq_ok h with ⟨hc, h⟩ | ⟨hc, h⟩
      · obtain ⟨b, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hbv : b = decide (e = ty) := eidx_eq2 e ty b trivial trivial hb2
        rcases ConRon.Refine.HashMap2.ite_eq_ok h with ⟨hc2, h⟩ | ⟨hc2, h⟩
        · have hee : e = ty := by
            rw [hbv] at hc2
            exact of_decide_eq_true hc2
          have h2 : true = r := Result.ok_injective h
          rw [← h2]
          subst hc; subst hee
          simp
        · have hne : ¬ (e = ty) := by
            intro hcc
            exact hc2 (by rw [hbv, decide_eq_true hcc])
          obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hi3v : i3.val = i.val + 1 :=
            (ConRon.Refine.Nat.uadd_val hi3).trans (by simp)
          have hih := ih i3 r (by omega) h
          rw [hi3v] at hih
          rw [hih]
          have hne' : absEIdx e ≠ absEIdx ty := fun hcc => hne (absEIdx_inj hcc)
          simp [hne']
      · obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi3v : i3.val = i.val + 1 :=
          (ConRon.Refine.Nat.uadd_val hi3).trans (by simp)
        have hih := ih i3 r (by omega) h
        rw [hi3v] at hih
        rw [hih]
        have hne : absU i2 ≠ absU idx := by
          intro hcc
          exact hc (Std.UScalar.eq_imp _ _ hcc)
        simp [hne]

theorem leaf_mem_from_refines {bl : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)}
    {idx : Std.U64} {ty : arena.handle.EIdx} {i : Std.Usize} {r : Bool}
    (h : arena.expr_ops.leaf_mem_from bl idx ty i = ok r) :
    leafMem ((absFvlL bl).drop i.val) (absU idx) (absEIdx ty) = r :=
  leaf_mem_from_aux bl idx ty bl.val.length i r (by omega) h

theorem leaf_mem_refines {bl : alloc.vec.Vec (Std.U64 × arena.handle.EIdx)}
    {idx : Std.U64} {ty : arena.handle.EIdx} {r : Bool}
    (h : arena.expr_ops.leaf_mem bl idx ty = ok r) :
    leafMem (absFvlL bl) (absU idx) (absEIdx ty) = r := by
  rw [arena.expr_ops.leaf_mem] at h
  have hr := leaf_mem_from_refines h
  simpa using hr

/-! ## Handle equality -/

theorem expr_ptr_beq_refines {a b : arena.handle.EIdx} {r : Bool}
    (h : arena.expr_ops.expr_ptr_beq a b = ok r) :
    exprPtrBEq (absEIdx a) (absEIdx b) = r := by
  rw [arena.expr_ops.expr_ptr_beq] at h
  have hbv : r = decide (a = b) := eidx_eq2 a b r trivial trivial h
  rw [exprPtrBEq, hbv]
  by_cases hc : a = b
  · subst hc; simp
  · have hne : absEIdx a ≠ absEIdx b := fun hcc => hc (absEIdx_inj hcc)
    simp [hc, hne]

/-! ## The level-list substitution

The one pair of this file that needs a well-formedness hypothesis: the
`Level.subst` inside is exact only on well-formed levels and keys
(`Refine/Level.lean`'s `subst_use`), which is `Refine/Abs.lean`'s
`NameWF`/`LevelWF`. -/

theorem subst_level_list_from_aux
    (ks : alloc.vec.Vec kernel.name.Name) (us vs : alloc.vec.Vec kernel.level.Level)
    (hks : ∀ k ∈ ks.val, NameWF k) (hus : ∀ u ∈ us.val, LevelWF u)
    (hvs : ∀ v ∈ vs.val, LevelWF v) :
    ∀ (n : Nat) (i : Std.Usize) (out r : alloc.vec.Vec kernel.level.Level),
      vs.val.length ≤ i.val + n →
      arena.expr_ops.subst_level_list_from ks us vs i out = ok r →
      absLevels r = absLevels out ++
        substLevelList (absNames ks) (absLevels us) ((absLevels vs).drop i.val) := by
  intro n
  induction n with
  | zero =>
    intro i out r hn h
    rw [arena.expr_ops.subst_level_list_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len vs by scalar_tac), Result.ok.injEq] at h
    subst h
    rw [List.drop_eq_nil_of_le (by simp [absLevels]; omega), substLevelList]
    simp
  | succ n ih =>
    intro i out r hn h
    rw [arena.expr_ops.subst_level_list_from.eq_def] at h
    by_cases hx : i.val ≥ vs.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len vs by scalar_tac), Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le (by simp [absLevels]; omega), substLevelList]
      simp
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len vs by scalar_tac)] at h
      have hxi : i.val < vs.val.length := by omega
      obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨l1, hl1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hb, hlv⟩ := vecIndexAt hl
      have hlwf : LevelWF l := by
        rw [← hlv]; exact hvs _ (List.getElem_mem hb)
      obtain ⟨hsub, -⟩ := ConRon.Refine.Level.subst_use hl1 hlwf hks hus
      have hov : out1.val = out.val ++ [l1] := ConRon.Refine.vec_push_val hout1
      have hi2v : i2.val = i.val + 1 :=
        (ConRon.Refine.Nat.uadd_val hi2).trans (by simp)
      have hih := ih i2 out1 r (by omega) h
      rw [hih, hi2v]
      have hd : (absLevels vs).drop i.val
          = absLevel l :: (absLevels vs).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa [absLevels] using hxi)]
        simp only [absLevels, List.getElem_map, hlv]
      have hob : absLevels out1
          = absLevels out ++
            [ConLeche.Level.subst (absNames ks) (absLevels us) (absLevel l)] := by
        simp [absLevels, hov, hsub, absNames]
      rw [hd, substLevelList, hob]
      simp

theorem subst_level_list_from_refines
    {ks : alloc.vec.Vec kernel.name.Name} {us vs out r : alloc.vec.Vec kernel.level.Level}
    {i : Std.Usize}
    (hks : ∀ k ∈ ks.val, NameWF k) (hus : ∀ u ∈ us.val, LevelWF u)
    (hvs : ∀ v ∈ vs.val, LevelWF v)
    (h : arena.expr_ops.subst_level_list_from ks us vs i out = ok r) :
    absLevels r = absLevels out ++
      substLevelList (absNames ks) (absLevels us) ((absLevels vs).drop i.val) :=
  subst_level_list_from_aux ks us vs hks hus hvs vs.val.length i out r (by omega) h

theorem subst_level_list_refines
    {ks : alloc.vec.Vec kernel.name.Name} {us vs r : alloc.vec.Vec kernel.level.Level}
    (hks : ∀ k ∈ ks.val, NameWF k) (hus : ∀ u ∈ us.val, LevelWF u)
    (hvs : ∀ v ∈ vs.val, LevelWF v)
    (h : arena.expr_ops.subst_level_list ks us vs = ok r) :
    absLevels r = substLevelList (absNames ks) (absLevels us) (absLevels vs) := by
  rw [arena.expr_ops.subst_level_list] at h
  have hr := subst_level_list_from_refines hks hus hvs h
  simpa [absLevels, usize_zero_val] using hr

/-! ## Axiom census (DESIGN.md §5's P3/P5 gate)

Three representative lemmas: the cursor shape step, the relational memo
insert and the one lemma with a well-formedness hypothesis.  Lean's own three
axioms and nothing else — in particular no `sorryAx` and no `bv_decide`
axiom, which is what `Refine2/Idiom.lean`'s `attribute [-grind]` line is
there to keep true. -/

/-- info: 'ConRon.Refine2.ExprOps.eidx_copy_upto_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eidx_copy_upto_refines

/--
info: 'ConRon.Refine2.ExprOps.fvl_record_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fvl_record_refines

/-- info: 'ConRon.Refine2.ExprOps.subst_level_list_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subst_level_list_refines

end ConRon.Refine2.ExprOps

/-! ## Shared abstractions of the `ExprOps` tier (namespace `ConRon.Refine2`)

Moved here from `ExprOps/Mut.lean` (task #97-T2-LOCKSTEP lane ExprOps) so that
`Refine2/Tactic/Prims.lean` can state its primitive pairs without importing
the walks it is the vocabulary of. -/

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The handle-vector abstractions

Three readings of one Rust type.  `Vec<EIdx>` is the twin's `Array EIdx` where
it is a substitution ACCUMULATOR (task #97-P6-15's push order) and its
`List EIdx` where it is an argument SPINE (con-leche's own shape); a `_from`
cursor companion reads the spine from the cursor on. -/

/-- A `Vec<EIdx>` as the twin's push-order `Array EIdx`. -/
def absEIdxArr (v : alloc.vec.Vec arena.handle.EIdx) : Array EIdx :=
  (v.val.map absEIdx).toArray

/-- A `Vec<EIdx>` as the twin's `List EIdx`. -/
def absEIdxList (v : alloc.vec.Vec arena.handle.EIdx) : List EIdx :=
  v.val.map absEIdx

/-- A `Vec<EIdx>` read from a cursor on — DESIGN §3.4's standing
`List`-as-cursor deviation, and the only abstraction here that mentions one. -/
def absEIdxListFrom (v : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) :
    List EIdx := (v.val.drop i.val).map absEIdx

/-- A `Vec<NIdx>` as the twin's `List NIdx` (`instLPFast`'s level-parameter
names, which the arena keeps as handles). -/
def absNIdxList (v : alloc.vec.Vec arena.handle.NIdx) : List NIdx :=
  v.val.map absNIdx

/-- `Option<EIdx>`. -/
def absOptE (o : Option arena.handle.EIdx) : Option EIdx := o.map absEIdx

/-- `Option<(Vec<EIdx>, EIdx)>` — the domain list and the residual that
`inst_pis_at` and its three siblings answer. -/
def absOptArgsE (o : Option (alloc.vec.Vec arena.handle.EIdx × arena.handle.EIdx)) :
    Option (List EIdx × EIdx) :=
  o.map fun p => (absEIdxList p.1, absEIdx p.2)

attribute [simp] absEIdxArr absEIdxList absEIdxListFrom absNIdxList absOptE
  absOptArgsE

@[simp] theorem absEIdxArr_size (v : alloc.vec.Vec arena.handle.EIdx) :
    (absEIdxArr v).size = v.val.length := by
  simp [absEIdxArr]

theorem absEIdxArr_get (v : alloc.vec.Vec arena.handle.EIdx) (k : Nat)
    (h : k < v.val.length) :
    (absEIdxArr v)[k]'(by simpa using h) = absEIdx (v.val[k]) := by
  simp [absEIdxArr]


/-- The memo key: `eidx_nat_key` is the pair. -/
theorem eidx_nat_key_abs {h : arena.handle.EIdx} {d : Std.U64}
    {k : arena.monad.EIdxNat} (hk : arena.monad.eidx_nat_key h d = ok k) :
    absEIdxNat k = (absEIdx h, absU d) := by
  rw [arena.monad.eidx_nat_key] at hk
  obtain ⟨e, he, hk⟩ := ConRon.Refine.bind_eq_ok_iff.mp hk
  have hee : e = h := dupId_eidx h e he
  have hkk : ({ h := e, d := d } : arena.monad.EIdxNat) = k := Result.ok_injective hk
  rw [← hkk, hee]; rfl

/-- A cursor below the length reads the element and moves on. -/
theorem listFrom_cons (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize)
    (hi : i.val < args.val.length) :
    absEIdxListFrom args i =
      absEIdx args.val[i.val] :: (args.val.drop (i.val + 1)).map absEIdx := by
  simp only [absEIdxListFrom]
  rw [List.drop_eq_getElem_cons hi]
  rfl

theorem listFrom_nil (args : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize)
    (hi : args.val.length ≤ i.val) : absEIdxListFrom args i = [] := by
  simp only [absEIdxListFrom]
  rw [List.drop_eq_nil_of_le hi]; rfl

/-- `subst_level_list` hands back well-formed levels. -/
theorem subst_level_list_from_wf
    (ks : alloc.vec.Vec kernel.name.Name) (us vs : alloc.vec.Vec kernel.level.Level)
    (hks : ∀ k ∈ ks.val, ConRon.Refine.NameWF k)
    (hus : ∀ u ∈ us.val, ConRon.Refine.LevelWF u)
    (hvs : ∀ v ∈ vs.val, ConRon.Refine.LevelWF v) :
    ∀ (n : Nat) (i : Std.Usize) (out r : alloc.vec.Vec kernel.level.Level),
      vs.val.length ≤ i.val + n → (∀ v ∈ out.val, ConRon.Refine.LevelWF v) →
      arena.expr_ops.subst_level_list_from ks us vs i out = ok r →
      ∀ v ∈ r.val, ConRon.Refine.LevelWF v := by
  intro n
  induction n with
  | zero =>
    intro i out r hn hout h
    rw [arena.expr_ops.subst_level_list_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len vs by scalar_tac), Result.ok.injEq] at h
    rw [← h]; exact hout
  | succ n ih =>
    intro i out r hn hout h
    rw [arena.expr_ops.subst_level_list_from.eq_def] at h
    by_cases hx : i.val ≥ vs.val.length
    · rw [if_pos (show i ≥ alloc.vec.Vec.len vs by scalar_tac), Result.ok.injEq] at h
      rw [← h]; exact hout
    · rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len vs by scalar_tac)] at h
      obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨l1, hl1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨hb, hlv⟩ := ExprOps.vecIndexAt hl
      have hlwf : ConRon.Refine.LevelWF l := by
        rw [← hlv]; exact hvs _ (List.getElem_mem hb)
      obtain ⟨-, hwf1⟩ := ConRon.Refine.Level.subst_use hl1 hlwf hks hus
      have hov : out1.val = out.val ++ [l1] := ConRon.Refine.vec_push_val hout1
      have hi2v : i2.val = i.val + 1 :=
        (ConRon.Refine.Nat.uadd_val hi2).trans (by simp)
      refine ih i2 out1 r (by omega) ?_ h
      intro v hv
      rw [hov] at hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hout v hv
      · simp at hv; rw [hv]; exact hwf1

theorem subst_level_list_wf {ks : alloc.vec.Vec kernel.name.Name}
    {us vs r : alloc.vec.Vec kernel.level.Level}
    (hks : ∀ k ∈ ks.val, ConRon.Refine.NameWF k)
    (hus : ∀ u ∈ us.val, ConRon.Refine.LevelWF u)
    (hvs : ∀ v ∈ vs.val, ConRon.Refine.LevelWF v)
    (h : arena.expr_ops.subst_level_list ks us vs = ok r) :
    ∀ v ∈ r.val, ConRon.Refine.LevelWF v := by
  rw [arena.expr_ops.subst_level_list] at h
  exact subst_level_list_from_wf ks us vs hks hus hvs vs.val.length _ _ _ (by scalar_tac)
    (by intro v hv; simp at hv) h

end ConRon.Refine2

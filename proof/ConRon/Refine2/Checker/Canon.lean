/-
# `ConRon.Refine2.Checker.Canon` — Theorem 2 for `arena::canon`

**Task #97-P5-Checker**, deliverable 2 (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/canon.rs` against
`proof/ConRon/Arena/Canon.lean`: con-leche's canonical-form agreement, decided
in LOCKSTEP on two handles rather than by building two canonical terms.
`canonLevel` and `canonExpr` preserve every node's constructor, so the two
canonical forms are equal iff the originals agree constructor by constructor
down to their leaves — which is what the descent tests, and what makes the
whole module allocation-free except for `canon_names`.

## Three shapes in one file, and the split is the state

* `canon_names{,_go}` and the four `*canon_eq*` entries **intern** the
  numbered parameter names, so they thread the state: `Sim`.
* `canon_level_eq`, `canon_expr_eq` and their companions only `view`:
  `Refine2/Checker/Shape.lean`'s **`SimRE`** — a reader that can decline
  (the fuel arm is `Internal`, one of the three mirrored kinds).
* the ten `*_beq` are **pure**, and each is the twin's derived `DecidableEq`
  at the abstraction — `o = decide (abs a = abs b)`, which is the `Eq2Fwd`
  shape of task #97-P5-0's rule 4 met at the declaration layer instead of at
  a cons key.

## What is Rust-only here

`canon_name_map_from`, `canon_level_eq_at`, `canon_expr_eq_at`,
`canon_expr_eq_two`, `canon_eq_cv_and_rules`, `canon_eq_cv_and_value` and the
ten `*_beq`.  The `_at`/`_two` four are task #97-P6-2's extraction rule 5
(a `view`'s loans dead at the join, and the two-child arms' pair in the twin's
order); the `_beq` ten are DESIGN §3.4's "no `deriving DecidableEq` in code
Aeneas must translate", so they are hand-written comparisons against a derived
instance.  Each is stated against the twin's own arm or its `==`.

## What these lemmas wait on

`Specs.lean`'s `view`, `view_l`, `view_ls` (closed) and `intern_n_node`
(open).  The shape step is the fuel peel at `canon_level_eq` and
`canon_expr_eq`, the `Nat`-count recursion at `canon_names_go` and a
`Vec`-cursor measure induction at the five list walks.

## The pure group, closed (task #97-P5-Checker round 3)

Eight of the ten `*_beq` are closed, and they wait on nothing — which is why
they went first once `Refine2/Specs.lean` reached zero and the file became
workable.  **Two templates carry all eight:**

* `*_vec_beq_aux` — the cursor recursion at a handle vector, measure
  `|a| - i`, leaf `Eq2` + `abs*_inj`.  Written once for `eidx` and cloned
  verbatim to `lidx`, `nidx` and `i_rec_rules` (whose leaf is
  `i_rec_rule_beq` instead of an `Eq2`).
* `beq_chain` / `beq_chain'` — ONE link of the port's short-circuit
  conjunction, `if b then <rest> else false` against the twin's `∧`.  A
  record comparison is that folded over the fields, with `mk.injEq` turning
  the twin's `DecidableEq` into the conjunction.  `beq_chain` takes a `Bool`
  test with its abstraction equation; `beq_chain'` takes a decidable
  PROPOSITION with an `Iff` to the twin's form (`absU_iff` for a scalar
  field).

The one place the two conjunctions are not in the same ORDER is
`i_rec_rule_beq`: the port compares `rhs` LAST (it is `i_rec_rule_eq_but_rhs`
and then the right-hand side) where the twin's record has it fifth, so that
proof ends in `decide_eq_decide` and `tauto` over the same set of conjuncts.

**What is left of the group**: `i_ind_caps_beq`, `i_proj_table_beq` and
`i_constant_info_beq`.  All three are `beq_chain` folds like the two closed
ones; `i_ind_caps_beq`'s last link needs `kernel::prop_when::beq` against
`absPropWhen`, which this file does not yet have.
-/
import ConRon.Refine2.Checker.Pins

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The pure comparisons

Ten of them, and every one is the twin's derived `DecidableEq` at the
abstraction.  The five `*_vec_beq` are cursor recursions over two `Vec`s and
are stated at the two lists from the cursor on. -/

/-! ### The three handle-vector comparisons, and the one induction they share

`eidx_vec_beq` / `lidx_vec_beq` / `nidx_vec_beq` are the same function at
three handle types: a cursor recursion whose leaf is the handle's `Eq2` and
whose measure is `|a| - i`.  The Rust tests `i >= a.len()` and `i >= b.len()`
in both branches — the nested repeat of the first test is dead, and `if_pos`
at the branch's own hypothesis is what kills it — so the four outcomes are
*both past the end* (`true`), *one past* (`false` twice) and *both live*
(the leaf, then the recursion).

`abs*_inj` (`Refine2/AbsStore.lean`) is what turns the `Eq2`'s word
comparison into the twin's `DecidableEq` at the abstraction: `Eq2Fwd` one way
and injectivity the other, which is task #97-P5-0's rule 4 met at a handle
rather than at a cons key. -/

theorem eidx_eq2_abs {e e1 : arena.handle.EIdx} {b1 : Bool}
    (h : arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 e e1 = ok b1) :
    b1 = decide (absEIdx e = absEIdx e1) := by
  rw [arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  rw [← Result.ok_injective h]
  obtain ⟨w⟩ := e; obtain ⟨w'⟩ := e1
  by_cases hw : w = w'
  · subst hw; simp
  · simp only [hw, decide_false]
    refine (decide_eq_false ?_).symm
    intro hc
    exact hw (arena.handle.EIdx.mk.injEq .. ▸ absEIdx_inj hc)

private theorem eidx_vec_beq_aux (n : Nat) :
    ∀ {a b : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o : Bool},
      a.val.length - i.val = n →
      arena.canon.eidx_vec_beq a b i = ok o →
      o = decide (absEIdxLFrom a i = absEIdxLFrom b i) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b i o hn hrun
    rw [arena.canon.eidx_vec_beq.eq_def] at hrun
    dsimp only at hrun
    have hla := alloc.vec.Vec.len_val a
    have hlb := alloc.vec.Vec.len_val b
    by_cases ha : i ≥ a.len
    · have hae : a.val.length ≤ i.val := by scalar_tac
      rw [if_pos ha] at hrun
      by_cases hb : i ≥ b.len
      · have hbe : b.val.length ≤ i.val := by scalar_tac
        rw [if_pos hb] at hrun
        rw [← Result.ok_injective hrun]
        simp [absEIdxLFrom, List.drop_eq_nil_of_le hae, List.drop_eq_nil_of_le hbe]
      · have hbl : i.val < b.val.length := by scalar_tac
        rw [if_neg hb, if_pos ha] at hrun
        rw [← Result.ok_injective hrun]
        simp only [absEIdxLFrom, List.drop_eq_nil_of_le hae,
          List.drop_eq_getElem_cons hbl, List.map_nil, List.map_cons]
        simp
    · have hal : i.val < a.val.length := by scalar_tac
      rw [if_neg ha, if_neg ha] at hrun
      by_cases hb : i ≥ b.len
      · have hbe : b.val.length ≤ i.val := by scalar_tac
        rw [if_pos hb] at hrun
        rw [← Result.ok_injective hrun]
        simp only [absEIdxLFrom, List.drop_eq_nil_of_le hbe,
          List.drop_eq_getElem_cons hal, List.map_nil, List.map_cons]
        simp
      · have hbl : i.val < b.val.length := by scalar_tac
        rw [if_neg hb] at hrun
        obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨b1, hb1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨hlt, hev⟩ := ConRon.Refine.ExprOps.vec_index_val he
        obtain ⟨hlt1, hev1⟩ := ConRon.Refine.ExprOps.vec_index_val he1
        have hb1v := eidx_eq2_abs hb1
        by_cases hc : b1 = true
        · rw [if_pos hc] at hrun
          obtain ⟨i5, hi5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi5v : i5.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi5
          have hrec := ih (a.val.length - i5.val) (by omega) (i := i5) rfl hrun
          rw [hc] at hb1v
          have heq : absEIdx a.val[i.val] = absEIdx b.val[i.val] := by
            rw [← hev, ← hev1]; exact of_decide_eq_true hb1v.symm
          rw [hrec]
          simp only [absEIdxLFrom, hi5v, List.drop_eq_getElem_cons hal,
            List.drop_eq_getElem_cons hbl, List.map_cons, List.cons.injEq,
            heq, true_and]
        · simp only [Bool.not_eq_true] at hc
          rw [hc] at hrun hb1v
          rw [if_neg (by simp)] at hrun
          rw [← Result.ok_injective hrun]
          have hne : ¬ (absEIdx a.val[i.val] = absEIdx b.val[i.val]) := by
            rw [← hev, ← hev1]; exact of_decide_eq_false hb1v.symm
          simp only [absEIdxLFrom, List.drop_eq_getElem_cons hal,
            List.drop_eq_getElem_cons hbl, List.map_cons, List.cons.injEq]
          simp [hne]

theorem lidx_eq2_abs {e e1 : arena.handle.LIdx} {b1 : Bool}
    (h : arena.handle.LIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 e e1 = ok b1) :
    b1 = decide (absLIdx e = absLIdx e1) := by
  rw [arena.handle.LIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  rw [← Result.ok_injective h]
  obtain ⟨w⟩ := e; obtain ⟨w'⟩ := e1
  by_cases hw : w = w'
  · subst hw; simp
  · simp only [hw, decide_false]
    refine (decide_eq_false ?_).symm
    intro hc
    exact hw (arena.handle.LIdx.mk.injEq .. ▸ absLIdx_inj hc)

private theorem lidx_vec_beq_aux (n : Nat) :
    ∀ {a b : alloc.vec.Vec arena.handle.LIdx} {i : Std.Usize} {o : Bool},
      a.val.length - i.val = n →
      arena.canon.lidx_vec_beq a b i = ok o →
      o = decide (absLIdxLFrom a i = absLIdxLFrom b i) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b i o hn hrun
    rw [arena.canon.lidx_vec_beq.eq_def] at hrun
    dsimp only at hrun
    have hla := alloc.vec.Vec.len_val a
    have hlb := alloc.vec.Vec.len_val b
    by_cases ha : i ≥ a.len
    · have hae : a.val.length ≤ i.val := by scalar_tac
      rw [if_pos ha] at hrun
      by_cases hb : i ≥ b.len
      · have hbe : b.val.length ≤ i.val := by scalar_tac
        rw [if_pos hb] at hrun
        rw [← Result.ok_injective hrun]
        simp [absLIdxLFrom, List.drop_eq_nil_of_le hae, List.drop_eq_nil_of_le hbe]
      · have hbl : i.val < b.val.length := by scalar_tac
        rw [if_neg hb, if_pos ha] at hrun
        rw [← Result.ok_injective hrun]
        simp only [absLIdxLFrom, List.drop_eq_nil_of_le hae,
          List.drop_eq_getElem_cons hbl, List.map_nil, List.map_cons]
        simp
    · have hal : i.val < a.val.length := by scalar_tac
      rw [if_neg ha, if_neg ha] at hrun
      by_cases hb : i ≥ b.len
      · have hbe : b.val.length ≤ i.val := by scalar_tac
        rw [if_pos hb] at hrun
        rw [← Result.ok_injective hrun]
        simp only [absLIdxLFrom, List.drop_eq_nil_of_le hbe,
          List.drop_eq_getElem_cons hal, List.map_nil, List.map_cons]
        simp
      · have hbl : i.val < b.val.length := by scalar_tac
        rw [if_neg hb] at hrun
        obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨b1, hb1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨hlt, hev⟩ := ConRon.Refine.ExprOps.vec_index_val he
        obtain ⟨hlt1, hev1⟩ := ConRon.Refine.ExprOps.vec_index_val he1
        have hb1v := lidx_eq2_abs hb1
        by_cases hc : b1 = true
        · rw [if_pos hc] at hrun
          obtain ⟨i5, hi5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi5v : i5.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi5
          have hrec := ih (a.val.length - i5.val) (by omega) (i := i5) rfl hrun
          rw [hc] at hb1v
          have heq : absLIdx a.val[i.val] = absLIdx b.val[i.val] := by
            rw [← hev, ← hev1]; exact of_decide_eq_true hb1v.symm
          rw [hrec]
          simp only [absLIdxLFrom, hi5v, List.drop_eq_getElem_cons hal,
            List.drop_eq_getElem_cons hbl, List.map_cons, List.cons.injEq,
            heq, true_and]
        · simp only [Bool.not_eq_true] at hc
          rw [hc] at hrun hb1v
          rw [if_neg (by simp)] at hrun
          rw [← Result.ok_injective hrun]
          have hne : ¬ (absLIdx a.val[i.val] = absLIdx b.val[i.val]) := by
            rw [← hev, ← hev1]; exact of_decide_eq_false hb1v.symm
          simp only [absLIdxLFrom, List.drop_eq_getElem_cons hal,
            List.drop_eq_getElem_cons hbl, List.map_cons, List.cons.injEq]
          simp [hne]

theorem nidx_eq2_abs {e e1 : arena.handle.NIdx} {b1 : Bool}
    (h : arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 e e1 = ok b1) :
    b1 = decide (absNIdx e = absNIdx e1) := by
  rw [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  rw [← Result.ok_injective h]
  obtain ⟨w⟩ := e; obtain ⟨w'⟩ := e1
  by_cases hw : w = w'
  · subst hw; simp
  · simp only [hw, decide_false]
    refine (decide_eq_false ?_).symm
    intro hc
    exact hw (arena.handle.NIdx.mk.injEq .. ▸ absNIdx_inj hc)

private theorem nidx_vec_beq_aux (n : Nat) :
    ∀ {a b : alloc.vec.Vec arena.handle.NIdx} {i : Std.Usize} {o : Bool},
      a.val.length - i.val = n →
      arena.canon.nidx_vec_beq a b i = ok o →
      o = decide (absNIdxLFrom a i = absNIdxLFrom b i) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b i o hn hrun
    rw [arena.canon.nidx_vec_beq.eq_def] at hrun
    dsimp only at hrun
    have hla := alloc.vec.Vec.len_val a
    have hlb := alloc.vec.Vec.len_val b
    by_cases ha : i ≥ a.len
    · have hae : a.val.length ≤ i.val := by scalar_tac
      rw [if_pos ha] at hrun
      by_cases hb : i ≥ b.len
      · have hbe : b.val.length ≤ i.val := by scalar_tac
        rw [if_pos hb] at hrun
        rw [← Result.ok_injective hrun]
        simp [absNIdxLFrom, List.drop_eq_nil_of_le hae, List.drop_eq_nil_of_le hbe]
      · have hbl : i.val < b.val.length := by scalar_tac
        rw [if_neg hb, if_pos ha] at hrun
        rw [← Result.ok_injective hrun]
        simp only [absNIdxLFrom, List.drop_eq_nil_of_le hae,
          List.drop_eq_getElem_cons hbl, List.map_nil, List.map_cons]
        simp
    · have hal : i.val < a.val.length := by scalar_tac
      rw [if_neg ha, if_neg ha] at hrun
      by_cases hb : i ≥ b.len
      · have hbe : b.val.length ≤ i.val := by scalar_tac
        rw [if_pos hb] at hrun
        rw [← Result.ok_injective hrun]
        simp only [absNIdxLFrom, List.drop_eq_nil_of_le hbe,
          List.drop_eq_getElem_cons hal, List.map_nil, List.map_cons]
        simp
      · have hbl : i.val < b.val.length := by scalar_tac
        rw [if_neg hb] at hrun
        obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨b1, hb1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨hlt, hev⟩ := ConRon.Refine.ExprOps.vec_index_val he
        obtain ⟨hlt1, hev1⟩ := ConRon.Refine.ExprOps.vec_index_val he1
        have hb1v := nidx_eq2_abs hb1
        by_cases hc : b1 = true
        · rw [if_pos hc] at hrun
          obtain ⟨i5, hi5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi5v : i5.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi5
          have hrec := ih (a.val.length - i5.val) (by omega) (i := i5) rfl hrun
          rw [hc] at hb1v
          have heq : absNIdx a.val[i.val] = absNIdx b.val[i.val] := by
            rw [← hev, ← hev1]; exact of_decide_eq_true hb1v.symm
          rw [hrec]
          simp only [absNIdxLFrom, hi5v, List.drop_eq_getElem_cons hal,
            List.drop_eq_getElem_cons hbl, List.map_cons, List.cons.injEq,
            heq, true_and]
        · simp only [Bool.not_eq_true] at hc
          rw [hc] at hrun hb1v
          rw [if_neg (by simp)] at hrun
          rw [← Result.ok_injective hrun]
          have hne : ¬ (absNIdx a.val[i.val] = absNIdx b.val[i.val]) := by
            rw [← hev, ← hev1]; exact of_decide_eq_false hb1v.symm
          simp only [absNIdxLFrom, List.drop_eq_getElem_cons hal,
            List.drop_eq_getElem_cons hbl, List.map_cons, List.cons.injEq]
          simp [hne]
/-- `eidx_vec_beq` at the cursor is `==` on the two remaining handle lists. -/
theorem eidx_vec_beq_refines {a b : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize} {o : Bool}
    (hrun : arena.canon.eidx_vec_beq a b i = ok o) :
    o = decide (absEIdxLFrom a i = absEIdxLFrom b i) :=
  eidx_vec_beq_aux _ rfl hrun

/-- `lidx_vec_beq` at the cursor. -/
theorem lidx_vec_beq_refines {a b : alloc.vec.Vec arena.handle.LIdx}
    {i : Std.Usize} {o : Bool}
    (hrun : arena.canon.lidx_vec_beq a b i = ok o) :
    o = decide (absLIdxLFrom a i = absLIdxLFrom b i) :=
  lidx_vec_beq_aux _ rfl hrun

/-- `nidx_vec_beq` at the cursor. -/
theorem nidx_vec_beq_refines {a b : alloc.vec.Vec arena.handle.NIdx}
    {i : Std.Usize} {o : Bool}
    (hrun : arena.canon.nidx_vec_beq a b i = ok o) :
    o = decide (absNIdxLFrom a i = absNIdxLFrom b i) :=
  nidx_vec_beq_aux _ rfl hrun

/-- `i_rec_rule_fire_beq` ⊑ `==` on `IRecRuleFire`.  Nine cases, eight of them
the constructor tags; the ninth is the two handle vectors, in the twin's
order. -/
theorem i_rec_rule_fire_beq_refines {a b : arena.env.IRecRuleFire} {o : Bool}
    (hrun : arena.canon.i_rec_rule_fire_beq a b = ok o) :
    o = decide (absIRecRuleFire a = absIRecRuleFire b) := by
  rw [arena.canon.i_rec_rule_fire_beq.eq_def] at hrun
  cases a
  case Nested l1 p1 =>
    cases b
    case Nested l2 p2 =>
      obtain ⟨b1, hb1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have h1 := lidx_vec_beq_refines hb1
      by_cases hc : b1 = true
      · rw [if_pos hc] at hrun
        rw [hc] at h1
        have hl : absLIdxLFrom l1 0#usize = absLIdxLFrom l2 0#usize :=
          of_decide_eq_true h1.symm
        have hl' : List.map absLIdx l1.val = List.map absLIdx l2.val := by
          simpa [absLIdxLFrom] using hl
        rw [eidx_vec_beq_refines hrun]
        simp [absIRecRuleFire, absEIdxLFrom, hl']
      · simp only [Bool.not_eq_true] at hc
        rw [hc] at hrun h1
        rw [if_neg (by simp)] at hrun
        rw [← Result.ok_injective hrun]
        have hl : ¬ (absLIdxLFrom l1 0#usize = absLIdxLFrom l2 0#usize) :=
          of_decide_eq_false h1.symm
        have hl' : ¬ (List.map absLIdx l1.val = List.map absLIdx l2.val) := by
          simpa [absLIdxLFrom] using hl
        simp [absIRecRuleFire, hl']
    all_goals (rw [← Result.ok_injective hrun]; simp [absIRecRuleFire])
  all_goals (cases b <;> (rw [← Result.ok_injective hrun]; simp [absIRecRuleFire]))

/-! ### The short-circuit conjunction, once

`i_constant_val_beq` and the four record comparisons below are a chain of
`if b then <rest> else false` over the record's fields, where the twin's
`DecidableEq` is the conjunction of the same tests.  `beq_chain` is that one
link, and each comparison is it folded over the fields with `mk.injEq`
turning the twin's record equality into the conjunction. -/

private theorem beq_chain {b1 : Bool} {P Q : Prop} [Decidable P] [Decidable Q]
    {x : Result Bool} {o : Bool}
    (h1 : b1 = decide P)
    (hrun : (if b1 = true then x else ok false) = ok o)
    (hx : ∀ o', x = ok o' → o' = decide Q) :
    o = decide (P ∧ Q) := by
  by_cases hb : b1 = true
  · rw [if_pos hb] at hrun
    rw [hx o hrun]
    rw [hb] at h1
    have hP : P := of_decide_eq_true h1.symm
    simp [hP]
  · simp only [Bool.not_eq_true] at hb
    rw [hb] at hrun h1
    rw [if_neg (by simp)] at hrun
    rw [← Result.ok_injective hrun]
    have hP : ¬ P := of_decide_eq_false h1.symm
    simp [hP]

/-- The chain's last link: a `Decidable` test returned as it is. -/
private theorem beq_last {P : Prop} [Decidable P] {o : Bool}
    (h : (ok (decide P) : Result Bool) = ok o) : o = decide P :=
  (Result.ok_injective h).symm

/-- The same link where the Rust's test is a decidable PROPOSITION rather than
a `Bool` — a scalar or flag field compared directly — and the twin's conjunct
is that proposition through the abstraction. -/
private theorem beq_chain' {P P' Q : Prop} [Decidable P] [Decidable P']
    [Decidable Q] {x : Result Bool} {o : Bool} (hPP : P ↔ P')
    (hrun : (if P then x else ok false) = ok o)
    (hx : ∀ o', x = ok o' → o' = decide Q) :
    o = decide (P' ∧ Q) := by
  by_cases hP : P
  · rw [if_pos hP] at hrun
    rw [hx o hrun]
    simp [hPP.mp hP]
  · rw [if_neg hP] at hrun
    rw [← Result.ok_injective hrun]
    have hP' : ¬ P' := fun h => hP (hPP.mpr h)
    simp [hP']

/-- `absU` is injective on `u64`, as an `Iff` for `beq_chain'`. -/
private theorem absU_iff {x y : Std.U64} : (x = y) ↔ (absU x = absU y) :=
  ⟨fun h => by rw [h], fun h => absU_inj_u64 h⟩

/-- `i_constant_val_beq` ⊑ `==` on `IConstantVal`. -/
theorem i_constant_val_beq_refines {a b : arena.env.IConstantVal} {o : Bool}
    (hrun : arena.canon.i_constant_val_beq a b = ok o) :
    o = decide (absIConstantVal a = absIConstantVal b) := by
  rw [arena.canon.i_constant_val_beq] at hrun
  obtain ⟨b1, hb1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  simp only [absIConstantVal, IConstantVal.mk.injEq]
  refine beq_chain (nidx_eq2_abs hb1) hrun ?_
  intro o1 h
  obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h2 := nidx_vec_beq_refines hb2
  simp only [absNIdxLFrom] at h2
  refine beq_chain (by simpa using h2) h ?_
  intro o2 h'
  exact eidx_eq2_abs h'

/-- `i_rec_rule_eq_but_rhs_refines`, stated HERE because `i_rec_rule_beq`
consumes it and the file keeps the port's declaration order for its public
statements. -/
private theorem i_rec_rule_eq_but_rhs_aux {r r2 : arena.env.IRecRule} {o : Bool}
    (hrun : arena.canon.i_rec_rule_eq_but_rhs r r2 = ok o) :
    o = decide ({ absIRecRule r with rhs := default } =
      { absIRecRule r2 with rhs := default }) := by
  rw [arena.canon.i_rec_rule_eq_but_rhs] at hrun
  obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  simp only [absIRecRule, IRecRule.mk.injEq, true_and]
  refine beq_chain (nidx_eq2_abs hb) hrun ?_
  intro o1 h
  refine beq_chain' absU_iff h ?_
  intro o2 h
  refine beq_chain' absU_iff h ?_
  intro o3 h
  obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  refine beq_chain (i_rec_rule_fire_beq_refines hb1) h ?_
  intro o4 h
  refine beq_chain' Iff.rfl h ?_
  intro o5 h
  refine beq_chain' Iff.rfl h ?_
  intro o6 h
  exact beq_last h

/-- `i_rec_rule_beq` ⊑ `==` on `IRecRule`. -/
theorem i_rec_rule_beq_refines {a b : arena.env.IRecRule} {o : Bool}
    (hrun : arena.canon.i_rec_rule_beq a b = ok o) :
    o = decide (absIRecRule a = absIRecRule b) := by
  rw [arena.canon.i_rec_rule_beq] at hrun
  obtain ⟨b1, hb1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have key : o = decide (({ absIRecRule a with rhs := default } =
      { absIRecRule b with rhs := default }) ∧ absEIdx a.rhs = absEIdx b.rhs) :=
    beq_chain (i_rec_rule_eq_but_rhs_aux hb1) hrun
      (fun _ h => eidx_eq2_abs h)
  -- the port compares `rhs` LAST and the twin's record has it fifth, so the
  -- two conjunctions are the same set in a different order
  rw [key, decide_eq_decide]
  simp only [absIRecRule, IRecRule.mk.injEq, true_and]
  tauto

private theorem i_rec_rules_beq_aux (n : Nat) :
    ∀ {a b : alloc.vec.Vec arena.env.IRecRule} {i : Std.Usize} {o : Bool},
      a.val.length - i.val = n →
      arena.canon.i_rec_rules_beq a b i = ok o →
      o = decide (absIRecRuleLFrom a i = absIRecRuleLFrom b i) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b i o hn hrun
    rw [arena.canon.i_rec_rules_beq.eq_def] at hrun
    dsimp only at hrun
    have hla := alloc.vec.Vec.len_val a
    have hlb := alloc.vec.Vec.len_val b
    by_cases ha : i ≥ a.len
    · have hae : a.val.length ≤ i.val := by scalar_tac
      rw [if_pos ha] at hrun
      by_cases hb : i ≥ b.len
      · have hbe : b.val.length ≤ i.val := by scalar_tac
        rw [if_pos hb] at hrun
        rw [← Result.ok_injective hrun]
        simp [absIRecRuleLFrom, List.drop_eq_nil_of_le hae, List.drop_eq_nil_of_le hbe]
      · have hbl : i.val < b.val.length := by scalar_tac
        rw [if_neg hb, if_pos ha] at hrun
        rw [← Result.ok_injective hrun]
        simp only [absIRecRuleLFrom, List.drop_eq_nil_of_le hae,
          List.drop_eq_getElem_cons hbl, List.map_nil, List.map_cons]
        simp
    · have hal : i.val < a.val.length := by scalar_tac
      rw [if_neg ha, if_neg ha] at hrun
      by_cases hb : i ≥ b.len
      · have hbe : b.val.length ≤ i.val := by scalar_tac
        rw [if_pos hb] at hrun
        rw [← Result.ok_injective hrun]
        simp only [absIRecRuleLFrom, List.drop_eq_nil_of_le hbe,
          List.drop_eq_getElem_cons hal, List.map_nil, List.map_cons]
        simp
      · have hbl : i.val < b.val.length := by scalar_tac
        rw [if_neg hb] at hrun
        obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨b1, hb1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨hlt, hev⟩ := ConRon.Refine.ExprOps.vec_index_val he
        obtain ⟨hlt1, hev1⟩ := ConRon.Refine.ExprOps.vec_index_val he1
        have hb1v := i_rec_rule_beq_refines hb1
        by_cases hc : b1 = true
        · rw [if_pos hc] at hrun
          obtain ⟨i5, hi5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have hi5v : i5.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi5
          have hrec := ih (a.val.length - i5.val) (by omega) (i := i5) rfl hrun
          rw [hc] at hb1v
          have heq : absIRecRule a.val[i.val] = absIRecRule b.val[i.val] := by
            rw [← hev, ← hev1]; exact of_decide_eq_true hb1v.symm
          rw [hrec]
          simp only [absIRecRuleLFrom, hi5v, List.drop_eq_getElem_cons hal,
            List.drop_eq_getElem_cons hbl, List.map_cons, List.cons.injEq,
            heq, true_and]
        · simp only [Bool.not_eq_true] at hc
          rw [hc] at hrun hb1v
          rw [if_neg (by simp)] at hrun
          rw [← Result.ok_injective hrun]
          have hne : ¬ (absIRecRule a.val[i.val] = absIRecRule b.val[i.val]) := by
            rw [← hev, ← hev1]; exact of_decide_eq_false hb1v.symm
          simp only [absIRecRuleLFrom, List.drop_eq_getElem_cons hal,
            List.drop_eq_getElem_cons hbl, List.map_cons, List.cons.injEq]
          simp [hne]

/-- `i_rec_rules_beq` at the cursor. -/
theorem i_rec_rules_beq_refines {a b : alloc.vec.Vec arena.env.IRecRule}
    {i : Std.Usize} {o : Bool}
    (hrun : arena.canon.i_rec_rules_beq a b i = ok o) :
    o = decide (absIRecRuleLFrom a i = absIRecRuleLFrom b i) :=
  i_rec_rules_beq_aux _ rfl hrun

/-- `i_ind_caps_beq` ⊑ `==` on `IIndCaps`. -/
theorem i_ind_caps_beq_refines {a b : arena.env.IIndCaps} {o : Bool}
    (hrun : arena.canon.i_ind_caps_beq a b = ok o) :
    o = decide (absIIndCaps a = absIIndCaps b) := by
  sorry

/-- `i_proj_table_beq` ⊑ `==` on `IProjTable`. -/
theorem i_proj_table_beq_refines {t t2 : arena.env.IProjTable} {o : Bool}
    (hrun : arena.canon.i_proj_table_beq t t2 = ok o) :
    o = decide (absIProjTable t = absIProjTable t2) := by
  sorry

/-- `i_constant_info_beq` ⊑ `==` on `IConstantInfo`. -/
theorem i_constant_info_beq_refines {a b : arena.env.IConstantInfo} {o : Bool}
    (hrun : arena.canon.i_constant_info_beq a b = ok o) :
    o = decide (absIConstantInfo a = absIConstantInfo b) := by
  sorry

/-- `i_rec_rule_eq_but_rhs` is the twin's `{ r with rhs := default } == { r'
with rhs := default }` — the record comparison at a common right-hand side,
which is how `canonRulesEq` compares the other fields without interning
anything. -/
theorem i_rec_rule_eq_but_rhs_refines {r r2 : arena.env.IRecRule} {o : Bool}
    (hrun : arena.canon.i_rec_rule_eq_but_rhs r r2 = ok o) :
    o = decide ({ absIRecRule r with rhs := default } =
      { absIRecRule r2 with rhs := default }) :=
  i_rec_rule_eq_but_rhs_aux hrun

/-! ## The renaming the parameter list induces -/

/-- `canon_name_map_from` ⊑ `canonNameMap` from the cursor on. -/
theorem canon_name_map_from_refines {ps cs : alloc.vec.Vec arena.handle.NIdx}
    {n : arena.handle.NIdx} {i : Std.Usize} {o}
    (hrun : arena.canon.canon_name_map_from ps cs n i = ok o) :
    absNIdx o = canonNameMap (absNIdxLFrom ps i)
      (absNIdxLFrom cs i) (absNIdx n) := by
  sorry

/-- `canon_name_map` ⊑ `canonNameMap`: the `i`-th parameter becomes the `i`-th
numbered name, anything else is left alone. -/
theorem canon_name_map_refines {ps cs : alloc.vec.Vec arena.handle.NIdx}
    {n : arena.handle.NIdx} {o}
    (hrun : arena.canon.canon_name_map ps cs n = ok o) :
    absNIdx o = canonNameMap (absNIdxL ps) (absNIdxL cs) (absNIdx n) := by
  sorry

/-! ## The numbered names

`canon_names_go` counts UP so the list comes out in index order; no fuel,
because it is structural on the count.  It INTERNS, so it is a `Sim`. -/

/-- `canon_names_go` ⊑ `canonNamesGo`, with the Rust's accumulator in front. -/
theorem canon_names_go_refines {pers st lst} {i n : Std.U64}
    {out : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_names_go pers st i n out = ok o) :
    Sim (fun v => absNIdxL out ++ absNIdxL v) (fun _ => True) pers lst o
      (do pure (absNIdxL out ++ (← canonNamesGo (absU i) (absU n)))) := by
  sorry

/-- `canon_names` ⊑ `canonNames`. -/
theorem canon_names_refines {pers st lst} {n : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_names pers st n = ok o) :
    Sim absNIdxL (fun _ => True) pers lst o (canonNames (absU n)) := by
  sorry

/-! ## The two node transcriptions

`canon_level_eq_at` and `canon_expr_eq_at` are the twin's `match ← view a,
← view b with` bodies past the two `view`s.  Each is transcribed here at the
twin's node views and tied to the twin by an `_unfold` equation — the shape
`Refine2/ExprOps/Read.lean` wrote for `wscopedBGo`, and the shape
`Refine2/Promote/Promote.lean` wrote for the three `promote_*_node`. -/

/-- `canonLevelEq`'s five matching arms and its catch-all. -/
def canonLevelEqAtSpec (ps ps' cs : List NIdx) (fuel : Nat) :
    LNodeView → LNodeView → AM Bool
  | .zero, .zero => pure true
  | .succ a, .succ b => canonLevelEq ps ps' cs fuel a b
  | .max a b, .max a' b' => do
    if ← canonLevelEq ps ps' cs fuel a a' then canonLevelEq ps ps' cs fuel b b'
    else pure false
  | .imax a b, .imax a' b' => do
    if ← canonLevelEq ps ps' cs fuel a a' then canonLevelEq ps ps' cs fuel b b'
    else pure false
  | .param n, .param n' =>
    pure (canonNameMap ps cs n == canonNameMap ps' cs n')
  | _, _ => pure false

/-- `canonExprEq`'s ten matching arms and its catch-all. -/
def canonExprEqAtSpec (ps ps' cs : List NIdx) (fuel : Nat) :
    ENodeView → ENodeView → AM Bool
  | .bvar i, .bvar j => pure (i == j)
  | .fvar i t, .fvar j t' =>
    if i == j then canonExprEq ps ps' cs fuel t t' else pure false
  | .sort u, .sort v => canonLevelEq ps ps' cs fuel u v
  | .const n us, .const n' us' =>
    if n == n' then canonLevelsEq ps ps' cs fuel us us' else pure false
  | .app f x, .app f' x' => do
    if ← canonExprEq ps ps' cs fuel f f' then canonExprEq ps ps' cs fuel x x'
    else pure false
  | .lam t bd _, .lam t' bd' _ => do
    if ← canonExprEq ps ps' cs fuel t t' then canonExprEq ps ps' cs fuel bd bd'
    else pure false
  | .forallE t bd _, .forallE t' bd' _ => do
    if ← canonExprEq ps ps' cs fuel t t' then canonExprEq ps ps' cs fuel bd bd'
    else pure false
  | .letE t v bd, .letE t' v' bd' => do
    if ← canonExprEq ps ps' cs fuel t t' then
      if ← canonExprEq ps ps' cs fuel v v' then canonExprEq ps ps' cs fuel bd bd'
      else pure false
    else pure false
  | .lit l, .lit l' => pure (l == l')
  | .proj s i e, .proj s' i' e' =>
    if s == s' && i == i' then canonExprEq ps ps' cs fuel e e' else pure false
  | _, _ => pure false

/-- `canonLevelEq` in terms of its transcription. -/
theorem canonLevelEq_unfold (ps ps' cs : List NIdx) (fuel : Nat) (u v : LIdx) :
    canonLevelEq ps ps' cs (fuel + 1) u v =
      (do canonLevelEqAtSpec ps ps' cs fuel (← viewL u) (← viewL v)) := by
  sorry

/-- `canonExprEq` in terms of its transcription. -/
theorem canonExprEq_unfold (ps ps' cs : List NIdx) (fuel : Nat) (a b : EIdx) :
    canonExprEq ps ps' cs (fuel + 1) a b =
      (do canonExprEqAtSpec ps ps' cs fuel (← view a) (← view b)) := by
  sorry

/-! ## Levels

Read-only: the twin `view`s and compares, and the only failure is the fuel
arm's `Internal`. -/

/-- `canon_level_eq` ⊑ `canonLevelEq`. -/
theorem canon_level_eq_refines {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {u v : arena.handle.LIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_level_eq pers st ps ps2 cs fuel u v = ok o) :
    SimRE id lst o
      (canonLevelEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absLIdx u) (absLIdx v)) := by
  sorry

/-- `canon_level_eq_at` is `canon_level_eq`'s arm past the two `view`s
(extraction rule 5), stated against the twin's `match` at the two views. -/
theorem canon_level_eq_at_refines {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {a b : arena.store.LNodeView} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_level_eq_at pers st ps ps2 cs fuel a b = ok o) :
    SimRE id lst o
      (canonLevelEqAtSpec (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absLNodeView a) (absLNodeView b)) := by
  sorry

/-- `canon_level_list_eq` ⊑ `canonLevelListEq` at the cursor. -/
theorem canon_level_list_eq_refines {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {us vs : alloc.vec.Vec arena.handle.LIdx} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_level_list_eq pers st ps ps2 cs fuel us vs i = ok o) :
    SimRE id lst o
      (canonLevelListEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absLIdxLFrom us i) (absLIdxLFrom vs i)) := by
  sorry

/-- `canon_levels_eq` ⊑ `canonLevelsEq`, at two interned universe-argument
LIST handles. -/
theorem canon_levels_eq_refines {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {us vs : arena.handle.LsIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_levels_eq pers st ps ps2 cs fuel us vs = ok o) :
    SimRE id lst o
      (canonLevelsEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absLsIdx us) (absLsIdx vs)) := by
  sorry

/-! ## Terms

The binder metadata is NOT compared, exactly as con-leche's clause does not:
`canonExpr` writes `⟨.never⟩` on both sides. -/

/-- `canon_expr_eq` ⊑ `canonExprEq`. -/
theorem canon_expr_eq_refines {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {a b : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_expr_eq pers st ps ps2 cs fuel a b = ok o) :
    SimRE id lst o
      (canonExprEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absEIdx a) (absEIdx b)) := by
  sorry

/-- `canon_expr_eq_at` is `canon_expr_eq`'s arm past the two `view`s. -/
theorem canon_expr_eq_at_refines {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {va vb : arena.store.ENodeView} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_expr_eq_at pers st ps ps2 cs fuel va vb = ok o) :
    SimRE id lst o
      (canonExprEqAtSpec (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absENodeView va) (absENodeView vb)) := by
  sorry

/-- `canon_expr_eq_two` is the two-child arms' pair of descents, in the twin's
order and with its short-circuit. -/
theorem canon_expr_eq_two_refines {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {a a2 b b2 : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_expr_eq_two pers st ps ps2 cs fuel a a2 b b2 = ok o) :
    SimRE id lst o
      (do
        if ← canonExprEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
            (absEIdx a) (absEIdx b) then
          canonExprEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
            (absEIdx a2) (absEIdx b2)
        else pure false) := by
  sorry

/-- `canon_rules_eq` ⊑ `canonRulesEq` at the cursor. -/
theorem canon_rules_eq_refines {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {rs rs2 : alloc.vec.Vec arena.env.IRecRule} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_rules_eq pers st ps ps2 cs fuel rs rs2 i = ok o) :
    SimRE id lst o
      (canonRulesEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absIRecRuleLFrom rs i) (absIRecRuleLFrom rs2 i)) := by
  sorry

/-! ## Constants

These four INTERN (`canonNames`), so they thread the state. -/

/-- `i_constant_val_canon_eq` ⊑ `IConstantVal.canonEq`.  The numbered
level-parameter lists are equal exactly when they are equally long, which is
why the length test stands in for comparing them — and why ONE `canonNames`
serves both sides. -/
theorem i_constant_val_canon_eq_refines {pers st lst}
    {cv cv2 : arena.env.IConstantVal} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.i_constant_val_canon_eq pers st cv cv2 = ok o) :
    Sim id (fun _ => True) pers lst o
      ((absIConstantVal cv).canonEq (absIConstantVal cv2)) := by
  sorry

/-- `canon_eq_cv_and_rules` is `i_constant_info_canon_eq`'s `.recInfo` arm
past its two scalar tests (extraction rule 5). -/
theorem canon_eq_cv_and_rules_refines {pers st lst}
    {cv cv2 : arena.env.IConstantVal}
    {rs rs2 : alloc.vec.Vec arena.env.IRecRule} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_eq_cv_and_rules pers st cv cv2 rs rs2 = ok o) :
    Sim id (fun _ => True) pers lst o
      (do
        if ← (absIConstantVal cv).canonEq (absIConstantVal cv2) then do
          let cs ← canonNames (absIConstantVal cv).levelParams.length
          canonRulesEq (absIConstantVal cv).levelParams
            (absIConstantVal cv2).levelParams cs coreWalkFuel
            (absIRecRuleL rs) (absIRecRuleL rs2)
        else pure false) := by
  sorry

/-- `canon_eq_cv_and_value` is the `.defnInfo` / `.thmInfo` arms' shared tail. -/
theorem canon_eq_cv_and_value_refines {pers st lst}
    {cv cv2 : arena.env.IConstantVal} {v v2 : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_eq_cv_and_value pers st cv cv2 v v2 = ok o) :
    Sim id (fun _ => True) pers lst o
      (do
        if ← (absIConstantVal cv).canonEq (absIConstantVal cv2) then do
          let cs ← canonNames (absIConstantVal cv).levelParams.length
          canonExprEq (absIConstantVal cv).levelParams
            (absIConstantVal cv2).levelParams cs coreWalkFuel
            (absEIdx v) (absEIdx v2)
        else pure false) := by
  sorry

/-- `i_constant_info_canon_eq` ⊑ `IConstantInfo.canonEq`.  `.indInfo`'s
capabilities are not compared (`canon` resets both to `{}`), and a projection
table is compared as it stands. -/
theorem i_constant_info_canon_eq_refines {pers st lst}
    {ci ci2 : arena.env.IConstantInfo} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.i_constant_info_canon_eq pers st ci ci2 = ok o) :
    Sim id (fun _ => True) pers lst o
      ((absIConstantInfo ci).canonEq (absIConstantInfo ci2)) := by
  sorry

/-- `canon_eq_list` ⊑ `canonEqList` at the cursor — two blocks are the same,
member for member, up to the canonical form. -/
theorem canon_eq_list_refines {pers st lst}
    {xs ys : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_eq_list pers st xs ys i = ok o) :
    Sim id (fun _ => True) pers lst o
      (canonEqList (absICILFrom xs i) (absICILFrom ys i)) := by
  sorry

end ConRon.Refine2

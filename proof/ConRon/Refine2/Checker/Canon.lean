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
  numbered parameter names, so they thread the state: `Sim₀`.
* `canon_level_eq`, `canon_expr_eq` and their companions only `view`:
  **`LSR`**, a reader that can decline (the fuel arm is `Internal`).
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

## Closed, by `lockstep` (task #97-T2-LOCKSTEP lane Checker Canon)

Every statement here is proved; the file has no `sorry`.  The walks are the
shared tactic's recipe: the fuel peels at `canon_level_eq`/`canon_expr_eq`
are one induction each over the walk and its node fragment (the shape of
`Checker/Axioms.lean`'s `erase_pw_eq`), the three cursor walks and
`canon_names_go` an `_aux` induction on what is left, every case one
`lockstep`.  The readers are `LSR` (`&AState` in the Rust); the interning
entries keep their `Sim₀` statements, proved from private `LS` forms.  One
divergence was fixed in the twin: `IConstantInfo.canonEq`'s `.defnInfo` arm
compared the common data (which interns the numbered names) before the
hints, where the port tests the hints first.

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

`i_ind_caps_beq`, `i_proj_table_beq` and `i_constant_info_beq` followed
(lane Inductives Modeled, slices 2–3), the last two at canonical Rust data.
-/
import ConRon.Refine2.Checker.Pins
import ConRon.Refine.BasisPins

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
rather than at a cons key.

`nidx_eq2_abs_decide` / `eidx_eq2_abs_decide` are `Refine2/Checker/Shape.lean`'s
(task #97-P5-Checker round 4 merged this file's private copies with
`Refine2/Inductives/Shape.lean`'s public ones there); `lidx_eq2_abs` is this
file's own, having no twin elsewhere. -/

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
        have hb1v := eidx_eq2_abs_decide hb1
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

private theorem lidx_eq2_abs {e e1 : arena.handle.LIdx} {b1 : Bool}
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
        have hb1v := nidx_eq2_abs_decide hb1
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
  refine beq_chain (nidx_eq2_abs_decide hb1) hrun ?_
  intro o1 h
  obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h2 := nidx_vec_beq_refines hb2
  simp only [absNIdxLFrom] at h2
  refine beq_chain (by simpa using h2) h ?_
  intro o2 h'
  exact eidx_eq2_abs_decide h'

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
  refine beq_chain (nidx_eq2_abs_decide hb) hrun ?_
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
      (fun _ h => eidx_eq2_abs_decide h)
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

/-- `i_ind_caps_beq` ⊑ `==` on `IIndCaps`, at canonical `sort_z`s
(`PropWhenWF`, the erased subtype invariant `IConstantInfoWF` carries).  The
port compares two `PropWhen`s by REPRESENTATION (`prop_when::beq`, i.e.
`equiv_r`), the twin by value; they agree exactly on canonical data
(`PropWhen.beq_iff`): `Many [p]` and `One p` abstract to the same value. -/
theorem i_ind_caps_beq_refines {a b : arena.env.IIndCaps} {o : Bool}
    (ha : ConRon.Refine.PropWhenWF a.sort_z) (hb : ConRon.Refine.PropWhenWF b.sort_z)
    (hrun : arena.canon.i_ind_caps_beq a b = ok o) :
    o = decide (absIIndCaps a = absIIndCaps b) := by
  rw [arena.canon.i_ind_caps_beq] at hrun
  simp only [absIIndCaps, IIndCaps.mk.injEq]
  refine beq_chain' Iff.rfl hrun ?_
  intro o1 h
  obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  refine beq_chain (nidx_eq2_abs_decide hb1) h ?_
  intro o2 h
  refine beq_chain' absU_iff h ?_
  intro o3 h
  refine beq_chain' absU_iff h ?_
  intro o4 h
  refine beq_chain' Iff.rfl h ?_
  intro o5 h
  refine beq_chain' absU_iff h ?_
  intro o6 h
  refine beq_chain' Iff.rfl h ?_
  intro o7 h
  have hiff := ConRon.Refine.PropWhen.beq_iff (ConRon.Refine.PropWhen.wf_shape ha)
    (ConRon.Refine.PropWhen.wf_shape hb) h
  cases o7
  · exact (decide_eq_false (fun hc => by simpa using hiff.mpr hc)).symm
  · exact (decide_eq_true (hiff.mp rfl)).symm

/-- `i_proj_table_beq` ⊑ `==` on `IProjTable`. -/
theorem i_proj_table_beq_refines {t t2 : arena.env.IProjTable} {o : Bool}
    (hrun : arena.canon.i_proj_table_beq t t2 = ok o) :
    o = decide (absIProjTable t = absIProjTable t2) := by
  rw [arena.canon.i_proj_table_beq] at hrun
  simp only [absIProjTable, IProjTable.mk.injEq]
  obtain ⟨b1, hb1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  refine beq_chain (nidx_eq2_abs_decide hb1) hrun ?_
  intro o1 h
  obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  refine beq_chain (nidx_eq2_abs_decide hb2) h ?_
  intro o2 h
  obtain ⟨b3, hb3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h3 := nidx_vec_beq_refines hb3
  simp only [absNIdxLFrom] at h3
  refine beq_chain (by simpa using h3) h ?_
  intro o3 h
  refine beq_chain' absU_iff h ?_
  intro o4 h
  obtain ⟨b5, hb5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  refine beq_chain (nidx_eq2_abs_decide hb5) h ?_
  intro o5 h
  refine beq_chain' absU_iff h ?_
  intro o6 h
  obtain ⟨b7, hb7, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  refine beq_chain (lidx_eq2_abs hb7) h ?_
  intro o7 h
  obtain ⟨b8, hb8, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h8 := eidx_vec_beq_refines hb8
  simp only [absEIdxLFrom] at h8
  refine beq_chain (by simpa using h8) h ?_
  intro o8 h
  obtain ⟨b9, hb9, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h9 := lidx_vec_beq_refines hb9
  simp only [absLIdxLFrom] at h9
  refine beq_chain (by simpa using h9) h ?_
  intro o9 h
  rw [beq_last h]
  exact decide_eq_decide.mpr absU_iff

/-- An interned constant's capabilities keep their `sort_z` (`intern_caps`
copies it with `prop_when::dup`): canonical input, canonical output. -/
theorem intern_ci_go_caps_wf {pers st m} {c : kernel.env.ConstantInfo}
    {ci : arena.env.IConstantInfo} {s' m'}
    (hc : ∀ v c2, c = .IndInfo v c2 → ConRon.Refine.PropWhenWF c2.sort_z)
    (h : arena.intern.intern_ci_go pers st m c = ok (.Ok ci, s', m')) :
    ∀ v caps, ci = .IndInfo v caps → ConRon.Refine.PropWhenWF caps.sort_z := by
  intro v caps hci
  subst hci
  cases c <;> simp only [arena.intern.intern_ci_go] at h <;>
    obtain ⟨⟨r, s1, m1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h <;>
    cases r <;> simp [ConRon.Refine.bind_eq_ok_iff] at h
  all_goals (obtain ⟨a, a1, h⟩ := h)
  all_goals first
    | (obtain ⟨b, h2, h⟩ := h
       cases a <;> simp [ConRon.Refine.bind_eq_ok_iff] at h)
    | (obtain ⟨h2, h⟩ := h
       cases a <;> simp at h
       obtain ⟨-, hc2, -, -⟩ := h
       subst hc2
       simp only [arena.intern.intern_caps, ConRon.Refine.bind_eq_ok_iff] at h2
       obtain ⟨⟨r, s2⟩, h3, h2⟩ := h2
       cases r <;> simp [ConRon.Refine.bind_eq_ok_iff] at h2
       obtain ⟨pw, hpw, h2⟩ := h2
       have hd := ConRon.Refine.PropWhen.dup_eq hpw
       subst hd
       obtain ⟨hcaps, -⟩ := h2
       rw [← hcaps]
       exact hc _ _ rfl)


/-- A pinned constant the port interns (`m >>= intern_ci`, `m` one of
`kernel::basis_pins`' builders) is canonical Rust data (`IConstantInfoWF`):
con-leche's constant, built by the smart constructors (`ConstantInfoWF`). -/
theorem intern_pinned_wf {pers st} {m : Result kernel.env.ConstantInfo}
    {ci : arena.env.IConstantInfo} {s'}
    (hm : ∀ c, m = ok c → ConRon.Refine.ConstantInfoWF c)
    (h : (m >>= fun c => arena.intern.intern_ci pers st c) = ok (.Ok ci, s')) :
    IConstantInfoWF ci := by
  obtain ⟨c, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hwf := hm c hc
  rw [arena.intern.intern_ci] at h
  obtain ⟨mm, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨⟨r, s1, m1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h' : (core.result.Result.Ok ci, s') = (r, s1) := (Result.ok_injective h).symm
  simp only [Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  cases ci with
  | IndInfo v caps =>
    refine intern_ci_go_caps_wf ?_ h1 v caps rfl
    intro v c2 hc2
    subst hc2
    exact hwf.2.2
  | _ => trivial

/-- The pinned `Eq` basis is canonical Rust data. -/
theorem eq_a_wf {pers st} {ci : arena.env.IConstantInfo} {s'}
    (h : arena.std_axioms.eq_a pers st = ok (.Ok ci, s')) : IConstantInfoWF ci := by
  rw [arena.std_axioms.eq_a] at h
  exact intern_pinned_wf (fun _ hc => (ConRon.Refine.BasisPins.eq_a_refines hc).2) h

/-- The pinned `Nat` is canonical Rust data. -/
theorem nat_a_wf {pers st} {ci : arena.env.IConstantInfo} {s'}
    (h : arena.std_axioms.nat_a pers st = ok (.Ok ci, s')) : IConstantInfoWF ci := by
  rw [arena.std_axioms.nat_a] at h
  exact intern_pinned_wf (fun _ hc => (ConRon.Refine.BasisPins.nat_a_refines hc).2) h

/-- `PartialEq` on `u64`, lifted, is `decide` of the abstracted equation. -/
private theorem u64_eq_lift {x y : Std.U64} {b : Bool}
    (h : lift (core.cmp.impls.PartialEqU64.eq x y) = ok b) : b = decide (x = y) := by
  simp only [lift, core.cmp.impls.PartialEqU64.eq, Result.ok.injEq] at h
  exact h.symm

/-- `i_constant_info_beq` ⊑ `==` on `IConstantInfo`, at canonical Rust data
(`IConstantInfoWF`; the `IndInfo` arm compares `sort_z` by representation). -/
theorem i_constant_info_beq_refines {a b : arena.env.IConstantInfo} {o : Bool}
    (ha : IConstantInfoWF a) (hb : IConstantInfoWF b)
    (hrun : arena.canon.i_constant_info_beq a b = ok o) :
    o = decide (absIConstantInfo a = absIConstantInfo b) := by
  cases a <;> cases b <;> simp only [arena.canon.i_constant_info_beq, Result.ok.injEq] at hrun <;>
    (try (subst hrun; simp [absIConstantInfo]; done))
  case AxiomInfo.AxiomInfo x y =>
    rw [i_constant_val_beq_refines hrun]
    simp [absIConstantInfo]
  case DefnInfo.DefnInfo x v hh y w hh2 =>
    simp only [absIConstantInfo, IConstantInfo.defnInfo.injEq]
    obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    refine beq_chain (i_constant_val_beq_refines hb1) h ?_
    intro o1 h
    obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine beq_chain (eidx_eq2_abs_decide hb2) h ?_
    intro o2 h
    exact ConRon.Refine.Env.reducibility_hint_beq_refines h
  case ThmInfo.ThmInfo x v y w =>
    simp only [absIConstantInfo, IConstantInfo.thmInfo.injEq]
    obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    refine beq_chain (i_constant_val_beq_refines hb1) h ?_
    intro o1 h
    exact eidx_eq2_abs_decide h
  case IndInfo.IndInfo x c y d =>
    simp only [absIConstantInfo, IConstantInfo.indInfo.injEq]
    obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    refine beq_chain (i_constant_val_beq_refines hb1) h ?_
    intro o1 h
    exact i_ind_caps_beq_refines ha hb h
  case CtorInfo.CtorInfo x p f y q g =>
    simp only [absIConstantInfo, IConstantInfo.ctorInfo.injEq]
    obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    refine beq_chain (i_constant_val_beq_refines hb1) h ?_
    intro o1 h
    obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine beq_chain ((u64_eq_lift hb2).trans (decide_eq_decide.mpr absU_iff)) h ?_
    intro o2 h
    exact (u64_eq_lift h).trans (decide_eq_decide.mpr absU_iff)
  case RecInfo.RecInfo x m p rs y n q ss =>
    simp only [absIConstantInfo, IConstantInfo.recInfo.injEq]
    obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    refine beq_chain (i_constant_val_beq_refines hb1) h ?_
    intro o1 h
    obtain ⟨b2, hb2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine beq_chain ((u64_eq_lift hb2).trans (decide_eq_decide.mpr absU_iff)) h ?_
    intro o2 h
    obtain ⟨b3, hb3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    refine beq_chain ((u64_eq_lift hb3).trans (decide_eq_decide.mpr absU_iff)) h ?_
    intro o3 h
    have h4 := i_rec_rules_beq_refines h
    simpa [absIRecRuleLFrom] using h4
  case ProjInfo.ProjInfo t u =>
    rw [i_proj_table_beq_refines hrun]
    simp [absIConstantInfo]

/-- `i_rec_rule_eq_but_rhs` is the twin's `{ r with rhs := default } == { r'
with rhs := default }` — the record comparison at a common right-hand side,
which is how `canonRulesEq` compares the other fields without interning
anything. -/
theorem i_rec_rule_eq_but_rhs_refines {r r2 : arena.env.IRecRule} {o : Bool}
    (hrun : arena.canon.i_rec_rule_eq_but_rhs r r2 = ok o) :
    o = decide ({ absIRecRule r with rhs := default } =
      { absIRecRule r2 with rhs := default }) :=
  i_rec_rule_eq_but_rhs_aux hrun

/-! ## The renaming the parameter list induces

`canonNameMap` at a cons: the head parameter either matches (the first
numbered name, or `n` itself past the end of a short `cs`) or the lookup
moves one step down BOTH lists — which is the Rust's one cursor. -/

theorem canonNameMap_cons (p : NIdx) (ps cs : List NIdx) (n : NIdx) :
    canonNameMap (p :: ps) cs n =
      if p == n then cs.headD n else canonNameMap ps cs.tail n := by
  unfold canonNameMap
  rw [List.findIdx?_cons]
  by_cases h : (p == n) = true
  · simp only [h, if_true]; cases cs <;> rfl
  · simp only [h, Bool.false_eq_true, if_false]
    cases hf : ps.findIdx? (fun q => q == n) <;> simp

theorem canonNameMap_nil (cs : List NIdx) (n : NIdx) : canonNameMap [] cs n = n := by
  simp [canonNameMap]

private theorem canon_name_map_from_aux (k : Nat) :
    ∀ {ps cs : alloc.vec.Vec arena.handle.NIdx} {n : arena.handle.NIdx} {i : Std.Usize} {o},
      ps.val.length - i.val = k →
      arena.canon.canon_name_map_from ps cs n i = ok o →
      absNIdx o = canonNameMap (absNIdxLFrom ps i) (absNIdxLFrom cs i) (absNIdx n) := by
  induction k with
  | zero =>
    intro ps cs n i o hk hrun
    rw [arena.canon.canon_name_map_from, if_pos (by scalar_tac)] at hrun
    simp only [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2, Result.ok.injEq] at hrun
    subst hrun
    rw [absNIdxLFrom, List.drop_eq_nil_of_le (by omega), List.map_nil, canonNameMap_nil]
  | succ m ih =>
    intro ps cs n i o hk hrun
    have hl : i.val < ps.val.length := by omega
    rw [arena.canon.canon_name_map_from, if_neg (by scalar_tac)] at hrun
    obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨b1, hb1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨hlt, hev⟩ := ConRon.Refine.ExprOps.vec_index_val he
    have hb := nidx_eq2_abs hb1
    rw [absNIdxLFrom, List.drop_eq_getElem_cons hl, List.map_cons, canonNameMap_cons, ← hev,
      ← hb]
    have htail : ((cs.val.drop i.val).map absNIdx).tail =
        (cs.val.drop (i.val + 1)).map absNIdx := by
      rw [← List.map_tail, List.tail_drop]
    cases b1 with
    | true =>
      simp only [if_true] at hrun ⊢
      by_cases hc : i < cs.len
      · rw [if_pos hc] at hrun
        obtain ⟨e2, he2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨hlt2, hev2⟩ := ConRon.Refine.ExprOps.vec_index_val he2
        simp only [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2,
          Result.ok.injEq] at hrun
        subst hrun
        have hcl : i.val < cs.val.length := by scalar_tac
        rw [absNIdxLFrom, List.drop_eq_getElem_cons hcl, List.map_cons, List.headD_cons, hev2]
      · rw [if_neg hc] at hrun
        simp only [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2,
          Result.ok.injEq] at hrun
        subst hrun
        rw [absNIdxLFrom, List.drop_eq_nil_of_le (by scalar_tac)]
        rfl
    | false =>
      simp only [Bool.false_eq_true, if_false] at hrun ⊢
      obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
      rw [ih (by omega) hrun, absNIdxLFrom, absNIdxLFrom, absNIdxLFrom, hi2v, htail]

/-- `canon_name_map_from` ⊑ `canonNameMap` from the cursor on. -/
theorem canon_name_map_from_refines {ps cs : alloc.vec.Vec arena.handle.NIdx}
    {n : arena.handle.NIdx} {i : Std.Usize} {o}
    (hrun : arena.canon.canon_name_map_from ps cs n i = ok o) :
    absNIdx o = canonNameMap (absNIdxLFrom ps i)
      (absNIdxLFrom cs i) (absNIdx n) :=
  canon_name_map_from_aux _ rfl hrun

/-- `canon_name_map` ⊑ `canonNameMap`: the `i`-th parameter becomes the `i`-th
numbered name, anything else is left alone. -/
theorem canon_name_map_refines {ps cs : alloc.vec.Vec arena.handle.NIdx}
    {n : arena.handle.NIdx} {o}
    (hrun : arena.canon.canon_name_map ps cs n = ok o) :
    absNIdx o = canonNameMap (absNIdxL ps) (absNIdxL cs) (absNIdx n) := by
  rw [arena.canon.canon_name_map] at hrun
  simpa [absNIdxLFrom, absNIdxL] using canon_name_map_from_refines hrun

/-! ## This file's primitive pairs

Value steps the walks below need, `local` so no other tier sees a second
copy: `Checker/Axioms.lean` (which imports this file) has the global
`literal_beq_spec`, `Inductives/Prims.lean` the global `intern_n_node_ls`. -/

open Lockstep in
@[local lockstep] private theorem canon_name_map_spec (ps cs : alloc.vec.Vec arena.handle.NIdx)
    (n : arena.handle.NIdx) :
    LSP (arena.canon.canon_name_map ps cs n)
      (fun o => absNIdx o = canonNameMap (absNIdxL ps) (absNIdxL cs) (absNIdx n)) :=
  fun _ h => canon_name_map_refines h

open Lockstep in
/-- `kernel::expr::literal_beq` is the twin's `==` on well-formed literals. -/
@[local lockstep] private theorem canon_literal_beq_spec {a b : kernel.expr.Literal}
    (ha : ConRon.Refine.LiteralWF a) (hb : ConRon.Refine.LiteralWF b) :
    LSP (kernel.expr.literal_beq a b)
      (fun c => c = (ConRon.Refine.absLiteral a == ConRon.Refine.absLiteral b)) := by
  intro c h
  rw [ConRon.Refine.Expr.literal_beq_refines ha hb h]
  cases h' : decide (ConRon.Refine.absLiteral a = ConRon.Refine.absLiteral b) <;> simp_all

private theorem canon_u64_decide_eq_val_beq (a b : Std.U64) :
    decide (a = b) = (a.val == b.val) := by
  cases h : decide (a = b) <;> simp_all [UScalar.eq_equiv]

open Lockstep in
/-- `PartialEq` on `u64`, lifted, is the twin's `==` on the abstracted values. -/
@[local lockstep] private theorem canon_u64_eq_lift_spec (x y : Std.U64) :
    LSP (lift (core.cmp.impls.PartialEqU64.eq x y)) (fun b => b = (absU x == absU y)) := by
  intro b h
  simp only [lift, core.cmp.impls.PartialEqU64.eq, Result.ok.injEq] at h
  subst h
  cases hh : decide (x = y) <;> simp_all [absU, UScalar.eq_equiv]

open Lockstep in
@[local lockstep] private theorem canon_hint_beq_spec (h h2 : kernel.env.ReducibilityHint) :
    LSP (kernel.env.reducibility_hint_beq h h2)
      (fun b => b = (ConRon.Refine.absHint h == ConRon.Refine.absHint h2)) := by
  intro b hb
  rw [ConRon.Refine.Env.reducibility_hint_beq_refines hb]
  exact (beq_eq_decide _ _).symm

open Lockstep in
@[local lockstep] private theorem canon_proj_table_beq_spec (t t2 : arena.env.IProjTable) :
    LSP (arena.canon.i_proj_table_beq t t2)
      (fun b => b = (absIProjTable t == absIProjTable t2)) := by
  intro b hb
  rw [i_proj_table_beq_refines hb]
  exact (beq_eq_decide _ _).symm

open Lockstep in
@[local lockstep] private theorem canon_rec_rule_eq_but_rhs_spec (r r2 : arena.env.IRecRule) :
    LSP (arena.canon.i_rec_rule_eq_but_rhs r r2)
      (fun o => o = ({ absIRecRule r with rhs := default } ==
        { absIRecRule r2 with rhs := default })) := by
  intro o h
  rw [i_rec_rule_eq_but_rhs_refines h]
  exact (beq_eq_decide _ _).symm

@[local lockstep_simp] private theorem canon_absIRecRule_rhs (r : arena.env.IRecRule) :
    (absIRecRule r).rhs = absEIdx r.rhs := rfl

open Lockstep in
@[local lockstep] private theorem canon_intern_n_anon_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a)
      (arena.monad.intern_n_node pers st .Anonymous) lst
      (Arena.internNNode .anonymous) :=
  LS.ofSim₀ fun _ h => intern_n_node_run₀ hrel hinv .Anonymous trivial h

open Lockstep in
@[local lockstep] private theorem canon_intern_n_num_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (a : arena.handle.NIdx) (i : Std.U64) :
    LS pers (fun a b => b = absNIdx a)
      (arena.monad.intern_n_node pers st (.Num a i)) lst
      (Arena.internNNode (.num (absNIdx a) (absU i))) :=
  LS.ofSim₀ fun _ h => intern_n_node_run₀ hrel hinv (.Num a i) trivial h

/-! ## The numbered names

`canon_names_go` counts UP so the list comes out in index order; no fuel,
because it is structural on the count.  It INTERNS, so it is a `Sim`.  The
port pushes onto an accumulator where the twin conses after its recursive
call, so the statement carries the accumulator in the twin. -/

open Lockstep in
private theorem canon_names_go_aux (k : Nat) :
    ∀ {pers st lst} {i n : Std.U64} {out : alloc.vec.Vec arena.handle.NIdx},
      n.val = k → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absNIdxL a)
        (arena.canon.canon_names_go pers st i n out) lst
        (do pure (absNIdxL out ++ (← canonNamesGo (absU i) k))) := by
  induction k with
  | zero =>
    intro pers st lst i n out hn hrel hinv
    rw [arena.canon.canon_names_go, if_pos (by scalar_tac), canonNamesGo]
    lockstep
  | succ m ih =>
    intro pers st lst i n out hn hrel hinv
    rw [arena.canon.canon_names_go, if_neg (by scalar_tac), canonNamesGo]
    simp only [bind_assoc, pure_bind]
    lockstep

/-- `canon_names_go` ⊑ `canonNamesGo`, with the Rust's accumulator in front. -/
theorem canon_names_go_refines {pers st lst} {i n : Std.U64}
    {out : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_names_go pers st i n out = ok o) :
    Sim₀ absNIdxL pers lst o
      (do pure (absNIdxL out ++ (← canonNamesGo (absU i) (absU n)))) :=
  Lockstep.LS.toSim₀ (canon_names_go_aux _ rfl hrel hinv) hrun

open Lockstep in
@[local lockstep] private theorem canon_names_lsc {pers st lst} {n : Std.U64}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdxL a) (arena.canon.canon_names pers st n) lst
      (canonNames (absU n)) := by
  have h := canon_names_go_aux n.val (i := 0#u64)
    (out := alloc.vec.Vec.new arena.handle.NIdx) rfl hrel hinv
  rw [arena.canon.canon_names, canonNames]
  simpa [absNIdxL] using h

/-- `canon_names` ⊑ `canonNames`. -/
theorem canon_names_refines {pers st lst} {n : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_names pers st n = ok o) :
    Sim₀ absNIdxL pers lst o (canonNames (absU n)) :=
  Lockstep.LS.toSim₀ (canon_names_lsc hrel hinv) hrun

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
  rw [canonLevelEq]
  congr 1

/-- `canonExprEq` in terms of its transcription. -/
theorem canonExprEq_unfold (ps ps' cs : List NIdx) (fuel : Nat) (a b : EIdx) :
    canonExprEq ps ps' cs (fuel + 1) a b =
      (do canonExprEqAtSpec ps ps' cs fuel (← view a) (← view b)) := by
  rw [canonExprEq]
  congr 1

/-! ## Levels

Read-only: the twin `view`s and compares, and the only failure is the fuel
arm's `Internal`.  The Rust reads the store only (`&AState`), so the
statements are `LSR` (the old `SimRE` forms were `sorry`, and asked for more:
the twin's state unchanged).  The walk and its node fragment are one fuel
induction, the shape of `Checker/Axioms.lean`'s `erase_pw_eq`. -/

open Lockstep in
private def CanonLevelEqAt (k : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState},
    AStateRel₀ pers st lst → AStateInv pers st →
    ∀ (ps ps2 cs : alloc.vec.Vec arena.handle.NIdx) (fuel : Std.U64)
      (u v : arena.handle.LIdx), fuel.val = k →
      LSR pers (fun a b => b = id a)
        (arena.canon.canon_level_eq pers st ps ps2 cs fuel u v) st lst
        (canonLevelEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) k (absLIdx u) (absLIdx v))

open Lockstep in
private def CanonLevelEqNodeAt (k : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState},
    AStateRel₀ pers st lst → AStateInv pers st →
    ∀ (ps ps2 cs : alloc.vec.Vec arena.handle.NIdx) (fuel : Std.U64)
      (a b : arena.store.LNodeView), fuel.val = k →
      LSR pers (fun a b => b = id a)
        (arena.canon.canon_level_eq_at pers st ps ps2 cs fuel a b) st lst
        (canonLevelEqAtSpec (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) k
          (absLNodeView a) (absLNodeView b))

open Lockstep in
private theorem canon_level_eq_node_of {k : Nat} (h1 : CanonLevelEqAt k) :
    CanonLevelEqNodeAt k := by
  intro pers st lst hrel hinv ps ps2 cs fuel a b hn
  have h1' := @h1 pers
  apply LSR.of_LS
  cases a <;> cases b <;> simp only [arena.canon.canon_level_eq_at, absLNodeView,
    canonLevelEqAtSpec] <;> lockstep

open Lockstep in
private theorem canon_level_eq_aux (k : Nat) : CanonLevelEqAt k := by
  induction k with
  | zero =>
    intro pers st lst hrel hinv ps ps2 cs fuel u v hn
    apply LSR.of_LS
    rw [arena.canon.canon_level_eq, canonLevelEq]
    lockstep
  | succ m ih =>
    have ih' : CanonLevelEqNodeAt m := canon_level_eq_node_of ih
    intro pers st lst hrel hinv ps ps2 cs fuel u v hn
    have ih'' := @ih' pers
    apply LSR.of_LS
    rw [arena.canon.canon_level_eq, canonLevelEq_unfold]
    lockstep

open Lockstep in
/-- `canon_level_eq` ⊑ `canonLevelEq`. -/
@[lockstep] theorem canon_level_eq_ls {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {u v : arena.handle.LIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a)
      (arena.canon.canon_level_eq pers st ps ps2 cs fuel u v) st lst
      (canonLevelEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absLIdx u) (absLIdx v)) :=
  canon_level_eq_aux _ hrel hinv ps ps2 cs fuel u v rfl

open Lockstep in
/-- `canon_level_eq_at` is `canon_level_eq`'s arm past the two `view`s
(extraction rule 5), stated against the twin's `match` at the two views. -/
@[lockstep] theorem canon_level_eq_at_ls {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {a b : arena.store.LNodeView}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a)
      (arena.canon.canon_level_eq_at pers st ps ps2 cs fuel a b) st lst
      (canonLevelEqAtSpec (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absLNodeView a) (absLNodeView b)) :=
  canon_level_eq_node_of (canon_level_eq_aux _) hrel hinv ps ps2 cs fuel a b rfl

open Lockstep in
private theorem canon_level_list_eq_aux (n : Nat) :
    ∀ {pers st lst} {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
      {us vs : alloc.vec.Vec arena.handle.LIdx} {i : Std.Usize},
      us.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = id a)
        (arena.canon.canon_level_list_eq pers st ps ps2 cs fuel us vs i) st lst
        (canonLevelListEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
          (absLIdxLFrom us i) (absLIdxLFrom vs i)) := by
  induction n with
  | zero =>
    intro pers st lst ps ps2 cs fuel us vs i hn hrel hinv
    apply LSR.of_LS
    rw [arena.canon.canon_level_list_eq, if_pos (by scalar_tac), absLIdxLFrom,
      vecFrom_nil _ _ _ (by omega)]
    by_cases hv : vs.val.length ≤ i.val
    · rw [if_pos (by scalar_tac), absLIdxLFrom, vecFrom_nil _ _ _ hv]
      simp only [canonLevelListEq]
      lockstep
    · rw [if_neg (by scalar_tac), if_pos (by scalar_tac), absLIdxLFrom,
        vecFrom_cons _ _ _ (by omega)]
      simp only [canonLevelListEq]
      lockstep
  | succ m ih =>
    intro pers st lst ps ps2 cs fuel us vs i hn hrel hinv
    apply LSR.of_LS
    rw [arena.canon.canon_level_list_eq, if_neg (by scalar_tac), if_neg (by scalar_tac),
      absLIdxLFrom, vecFrom_cons _ _ _ (by omega)]
    by_cases hv : vs.val.length ≤ i.val
    · rw [if_pos (by scalar_tac), absLIdxLFrom, vecFrom_nil _ _ _ hv]
      simp only [canonLevelListEq]
      lockstep
    · rw [if_neg (by scalar_tac), absLIdxLFrom, vecFrom_cons _ _ _ (by omega)]
      simp only [canonLevelListEq]
      lockstep

open Lockstep in
/-- `canon_level_list_eq` ⊑ `canonLevelListEq` at the cursor. -/
@[lockstep] theorem canon_level_list_eq_ls {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {us vs : alloc.vec.Vec arena.handle.LIdx} {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a)
      (arena.canon.canon_level_list_eq pers st ps ps2 cs fuel us vs i) st lst
      (canonLevelListEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absLIdxLFrom us i) (absLIdxLFrom vs i)) :=
  canon_level_list_eq_aux _ rfl hrel hinv

open Lockstep in
/-- `canon_levels_eq` ⊑ `canonLevelsEq`, at two interned universe-argument
LIST handles. -/
@[lockstep] theorem canon_levels_eq_ls {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {us vs : arena.handle.LsIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a)
      (arena.canon.canon_levels_eq pers st ps ps2 cs fuel us vs) st lst
      (canonLevelsEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absLsIdx us) (absLsIdx vs)) := by
  apply LSR.of_LS
  rw [arena.canon.canon_levels_eq, canonLevelsEq]
  lockstep

/-! ## Terms

The binder metadata is NOT compared, exactly as con-leche's clause does not:
`canonExpr` writes `⟨.never⟩` on both sides.  The node fragment takes its two
views as values, so it owes their `EViewMetaWF` (the literal arm's
`literal_beq` is exact only on well-formed literals; the views come from
`view_ls`, which supplies it).  The pair fragment's statement compared `a`
with `b` where the Rust compares `a` with `a2` (its callers pass `(f, f2, x,
x2)`); corrected, as `erase_pw_eq_two`'s was. -/

open Lockstep in
private def CanonExprEqAt (k : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState},
    AStateRel₀ pers st lst → AStateInv pers st →
    ∀ (ps ps2 cs : alloc.vec.Vec arena.handle.NIdx) (fuel : Std.U64)
      (a b : arena.handle.EIdx), fuel.val = k →
      LSR pers (fun a b => b = id a)
        (arena.canon.canon_expr_eq pers st ps ps2 cs fuel a b) st lst
        (canonExprEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) k (absEIdx a) (absEIdx b))

open Lockstep in
private def CanonExprEqTwoAt (k : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState},
    AStateRel₀ pers st lst → AStateInv pers st →
    ∀ (ps ps2 cs : alloc.vec.Vec arena.handle.NIdx) (fuel : Std.U64)
      (a a2 b b2 : arena.handle.EIdx), fuel.val = k →
      LSR pers (fun a b => b = id a)
        (arena.canon.canon_expr_eq_two pers st ps ps2 cs fuel a a2 b b2) st lst
        (do
          if ← canonExprEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) k
              (absEIdx a) (absEIdx a2) then
            canonExprEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) k (absEIdx b) (absEIdx b2)
          else pure false)

open Lockstep in
private def CanonExprEqNodeAt (k : Nat) : Prop :=
  ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState},
    AStateRel₀ pers st lst → AStateInv pers st →
    ∀ (ps ps2 cs : alloc.vec.Vec arena.handle.NIdx) (fuel : Std.U64)
      (va vb : arena.store.ENodeView), fuel.val = k →
      EViewMetaWF va → EViewMetaWF vb →
      LSR pers (fun a b => b = id a)
        (arena.canon.canon_expr_eq_at pers st ps ps2 cs fuel va vb) st lst
        (canonExprEqAtSpec (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) k
          (absENodeView va) (absENodeView vb))

open Lockstep in
private theorem canon_expr_eq_two_of {k : Nat} (h1 : CanonExprEqAt k) :
    CanonExprEqTwoAt k := by
  intro pers st lst hrel hinv ps ps2 cs fuel a a2 b b2 hn
  have h1' := @h1 pers
  apply LSR.of_LS
  rw [arena.canon.canon_expr_eq_two]
  lockstep

open Lockstep in
private theorem canon_expr_eq_node_of {k : Nat} (h1 : CanonExprEqAt k) :
    CanonExprEqNodeAt k := by
  have h2 : CanonExprEqTwoAt k := canon_expr_eq_two_of h1
  intro pers st lst hrel hinv ps ps2 cs fuel va vb hn hva hvb
  have h1' := @h1 pers
  have h2' := @h2 pers
  apply LSR.of_LS
  cases va <;> cases vb <;> simp only [arena.canon.canon_expr_eq_at, absENodeView,
    canonExprEqAtSpec, ← canon_u64_decide_eq_val_beq] at hva hvb ⊢ <;> lockstep

open Lockstep in
private theorem canon_expr_eq_aux (k : Nat) : CanonExprEqAt k := by
  induction k with
  | zero =>
    intro pers st lst hrel hinv ps ps2 cs fuel a b hn
    apply LSR.of_LS
    rw [arena.canon.canon_expr_eq, canonExprEq]
    lockstep
  | succ m ih =>
    have ih' : CanonExprEqNodeAt m := canon_expr_eq_node_of ih
    intro pers st lst hrel hinv ps ps2 cs fuel a b hn
    have ih'' := @ih' pers
    apply LSR.of_LS
    rw [arena.canon.canon_expr_eq, canonExprEq_unfold]
    lockstep

open Lockstep in
/-- `canon_expr_eq` ⊑ `canonExprEq`. -/
@[lockstep] theorem canon_expr_eq_ls {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {a b : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a)
      (arena.canon.canon_expr_eq pers st ps ps2 cs fuel a b) st lst
      (canonExprEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absEIdx a) (absEIdx b)) :=
  canon_expr_eq_aux _ hrel hinv ps ps2 cs fuel a b rfl

open Lockstep in
/-- `canon_expr_eq_at` is `canon_expr_eq`'s arm past the two `view`s, at
well-formed views. -/
@[lockstep] theorem canon_expr_eq_at_ls {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {va vb : arena.store.ENodeView}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hva : EViewMetaWF va) (hvb : EViewMetaWF vb) :
    LSR pers (fun a b => b = id a)
      (arena.canon.canon_expr_eq_at pers st ps ps2 cs fuel va vb) st lst
      (canonExprEqAtSpec (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absENodeView va) (absENodeView vb)) :=
  canon_expr_eq_node_of (canon_expr_eq_aux _) hrel hinv ps ps2 cs fuel va vb rfl hva hvb

open Lockstep in
/-- `canon_expr_eq_two` is the two-child arms' pair of descents, in the twin's
order and with its short-circuit. -/
@[lockstep] theorem canon_expr_eq_two_ls {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {a a2 b b2 : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a)
      (arena.canon.canon_expr_eq_two pers st ps ps2 cs fuel a a2 b b2) st lst
      (do
        if ← canonExprEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
            (absEIdx a) (absEIdx a2) then
          canonExprEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
            (absEIdx b) (absEIdx b2)
        else pure false) :=
  canon_expr_eq_two_of (canon_expr_eq_aux _) hrel hinv ps ps2 cs fuel a a2 b b2 rfl

open Lockstep in
private theorem canon_rules_eq_aux (n : Nat) :
    ∀ {pers st lst} {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
      {rs rs2 : alloc.vec.Vec arena.env.IRecRule} {i : Std.Usize},
      rs.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = id a)
        (arena.canon.canon_rules_eq pers st ps ps2 cs fuel rs rs2 i) st lst
        (canonRulesEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
          (absIRecRuleLFrom rs i) (absIRecRuleLFrom rs2 i)) := by
  induction n with
  | zero =>
    intro pers st lst ps ps2 cs fuel rs rs2 i hn hrel hinv
    apply LSR.of_LS
    rw [arena.canon.canon_rules_eq, if_pos (by scalar_tac), absIRecRuleLFrom,
      vecFrom_nil _ _ _ (by omega)]
    by_cases hv : rs2.val.length ≤ i.val
    · rw [if_pos (by scalar_tac), absIRecRuleLFrom, vecFrom_nil _ _ _ hv]
      simp only [canonRulesEq]
      lockstep
    · rw [if_neg (by scalar_tac), if_pos (by scalar_tac), absIRecRuleLFrom,
        vecFrom_cons _ _ _ (by omega)]
      simp only [canonRulesEq]
      lockstep
  | succ m ih =>
    intro pers st lst ps ps2 cs fuel rs rs2 i hn hrel hinv
    apply LSR.of_LS
    rw [arena.canon.canon_rules_eq, if_neg (by scalar_tac), if_neg (by scalar_tac),
      absIRecRuleLFrom, vecFrom_cons _ _ _ (by omega)]
    by_cases hv : rs2.val.length ≤ i.val
    · rw [if_pos (by scalar_tac), absIRecRuleLFrom, vecFrom_nil _ _ _ hv]
      simp only [canonRulesEq]
      lockstep
    · rw [if_neg (by scalar_tac), absIRecRuleLFrom, vecFrom_cons _ _ _ (by omega)]
      simp only [canonRulesEq]
      lockstep

open Lockstep in
/-- `canon_rules_eq` ⊑ `canonRulesEq` at the cursor. -/
@[lockstep] theorem canon_rules_eq_ls {pers st lst}
    {ps ps2 cs : alloc.vec.Vec arena.handle.NIdx} {fuel : Std.U64}
    {rs rs2 : alloc.vec.Vec arena.env.IRecRule} {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = id a)
      (arena.canon.canon_rules_eq pers st ps ps2 cs fuel rs rs2 i) st lst
      (canonRulesEq (absNIdxL ps) (absNIdxL ps2) (absNIdxL cs) (absU fuel)
        (absIRecRuleLFrom rs i) (absIRecRuleLFrom rs2 i)) :=
  canon_rules_eq_aux _ rfl hrel hinv

/-! ## Constants

These INTERN (`canonNames`), so they thread the state.  Each public `_refines`
is `Sim₀` (`Inductives/Prims.lean` wraps them as `@[lockstep]`); the `LS`
forms the zip uses are this file's private `_lsc`. -/

open Lockstep in
@[local lockstep] private theorem i_constant_val_canon_eq_lsc {pers st lst}
    {cv cv2 : arena.env.IConstantVal}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.canon.i_constant_val_canon_eq pers st cv cv2) lst
      ((absIConstantVal cv).canonEq (absIConstantVal cv2)) := by
  rw [arena.canon.i_constant_val_canon_eq, IConstantVal.canonEq]
  simp only [absIConstantVal, ← core_walk_fuel_abs]
  lockstep

/-- `i_constant_val_canon_eq` ⊑ `IConstantVal.canonEq`.  The numbered
level-parameter lists are equal exactly when they are equally long, which is
why the length test stands in for comparing them — and why ONE `canonNames`
serves both sides. -/
theorem i_constant_val_canon_eq_refines {pers st lst}
    {cv cv2 : arena.env.IConstantVal} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.i_constant_val_canon_eq pers st cv cv2 = ok o) :
    Sim₀ id pers lst o
      ((absIConstantVal cv).canonEq (absIConstantVal cv2)) :=
  Lockstep.LS.toSim₀ (i_constant_val_canon_eq_lsc hrel hinv) hrun

open Lockstep in
@[local lockstep] private theorem canon_eq_cv_and_rules_lsc {pers st lst}
    {cv cv2 : arena.env.IConstantVal}
    {rs rs2 : alloc.vec.Vec arena.env.IRecRule}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a)
      (arena.canon.canon_eq_cv_and_rules pers st cv cv2 rs rs2) lst
      (do
        if ← (absIConstantVal cv).canonEq (absIConstantVal cv2) then do
          let cs ← canonNames (absIConstantVal cv).levelParams.length
          canonRulesEq (absIConstantVal cv).levelParams
            (absIConstantVal cv2).levelParams cs coreWalkFuel
            (absIRecRuleL rs) (absIRecRuleL rs2)
        else pure false) := by
  rw [arena.canon.canon_eq_cv_and_rules]
  simp only [absIConstantVal, ← core_walk_fuel_abs]
  lockstep

/-- `canon_eq_cv_and_rules` is `i_constant_info_canon_eq`'s `.recInfo` arm
past its two scalar tests (extraction rule 5). -/
theorem canon_eq_cv_and_rules_refines {pers st lst}
    {cv cv2 : arena.env.IConstantVal}
    {rs rs2 : alloc.vec.Vec arena.env.IRecRule} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_eq_cv_and_rules pers st cv cv2 rs rs2 = ok o) :
    Sim₀ id pers lst o
      (do
        if ← (absIConstantVal cv).canonEq (absIConstantVal cv2) then do
          let cs ← canonNames (absIConstantVal cv).levelParams.length
          canonRulesEq (absIConstantVal cv).levelParams
            (absIConstantVal cv2).levelParams cs coreWalkFuel
            (absIRecRuleL rs) (absIRecRuleL rs2)
        else pure false) :=
  Lockstep.LS.toSim₀ (canon_eq_cv_and_rules_lsc hrel hinv) hrun

open Lockstep in
@[local lockstep] private theorem canon_eq_cv_and_value_lsc {pers st lst}
    {cv cv2 : arena.env.IConstantVal} {v v2 : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a)
      (arena.canon.canon_eq_cv_and_value pers st cv cv2 v v2) lst
      (do
        if ← (absIConstantVal cv).canonEq (absIConstantVal cv2) then do
          let cs ← canonNames (absIConstantVal cv).levelParams.length
          canonExprEq (absIConstantVal cv).levelParams
            (absIConstantVal cv2).levelParams cs coreWalkFuel
            (absEIdx v) (absEIdx v2)
        else pure false) := by
  rw [arena.canon.canon_eq_cv_and_value]
  simp only [absIConstantVal, ← core_walk_fuel_abs]
  lockstep

/-- `canon_eq_cv_and_value` is the `.defnInfo` / `.thmInfo` arms' shared tail. -/
theorem canon_eq_cv_and_value_refines {pers st lst}
    {cv cv2 : arena.env.IConstantVal} {v v2 : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_eq_cv_and_value pers st cv cv2 v v2 = ok o) :
    Sim₀ id pers lst o
      (do
        if ← (absIConstantVal cv).canonEq (absIConstantVal cv2) then do
          let cs ← canonNames (absIConstantVal cv).levelParams.length
          canonExprEq (absIConstantVal cv).levelParams
            (absIConstantVal cv2).levelParams cs coreWalkFuel
            (absEIdx v) (absEIdx v2)
        else pure false) :=
  Lockstep.LS.toSim₀ (canon_eq_cv_and_value_lsc hrel hinv) hrun

open Lockstep in
/-- One `lockstep` per pair of constructors.  The `.defnInfo` arm zips only
since the twin tests the hints first, as the port does (task #97-T2-LOCKSTEP
lane Checker Canon). -/
@[local lockstep] private theorem i_constant_info_canon_eq_lsc {pers st lst}
    {ci ci2 : arena.env.IConstantInfo}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.canon.i_constant_info_canon_eq pers st ci ci2) lst
      ((absIConstantInfo ci).canonEq (absIConstantInfo ci2)) := by
  cases ci <;> cases ci2 <;>
    simp only [arena.canon.i_constant_info_canon_eq, absIConstantInfo,
      IConstantInfo.canonEq] <;> lockstep

/-- `i_constant_info_canon_eq` ⊑ `IConstantInfo.canonEq`.  `.indInfo`'s
capabilities are not compared (`canon` resets both to `{}`), and a projection
table is compared as it stands. -/
theorem i_constant_info_canon_eq_refines {pers st lst}
    {ci ci2 : arena.env.IConstantInfo} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.i_constant_info_canon_eq pers st ci ci2 = ok o) :
    Sim₀ id pers lst o
      ((absIConstantInfo ci).canonEq (absIConstantInfo ci2)) :=
  Lockstep.LS.toSim₀ (i_constant_info_canon_eq_lsc hrel hinv) hrun

open Lockstep in
private theorem canon_eq_list_aux (n : Nat) :
    ∀ {pers st lst} {xs ys : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize},
      xs.val.length - i.val = n → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = id a)
        (arena.canon.canon_eq_list pers st xs ys i) lst
        (canonEqList (absICILFrom xs i) (absICILFrom ys i)) := by
  induction n with
  | zero =>
    intro pers st lst xs ys i hn hrel hinv
    rw [arena.canon.canon_eq_list, if_pos (by scalar_tac), absICILFrom,
      vecFrom_nil _ _ _ (by omega)]
    by_cases hv : ys.val.length ≤ i.val
    · rw [if_pos (by scalar_tac), absICILFrom, vecFrom_nil _ _ _ hv]
      simp only [canonEqList]
      lockstep
    · rw [if_neg (by scalar_tac), if_pos (by scalar_tac), absICILFrom,
        vecFrom_cons _ _ _ (by omega)]
      simp only [canonEqList]
      lockstep
  | succ m ih =>
    intro pers st lst xs ys i hn hrel hinv
    rw [arena.canon.canon_eq_list, if_neg (by scalar_tac), if_neg (by scalar_tac),
      absICILFrom, vecFrom_cons _ _ _ (by omega)]
    by_cases hv : ys.val.length ≤ i.val
    · rw [if_pos (by scalar_tac), absICILFrom, vecFrom_nil _ _ _ hv]
      simp only [canonEqList]
      lockstep
    · rw [if_neg (by scalar_tac), absICILFrom, vecFrom_cons _ _ _ (by omega)]
      simp only [canonEqList]
      lockstep

/-- `canon_eq_list` ⊑ `canonEqList` at the cursor — two blocks are the same,
member for member, up to the canonical form. -/
theorem canon_eq_list_refines {pers st lst}
    {xs ys : alloc.vec.Vec arena.env.IConstantInfo} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.canon.canon_eq_list pers st xs ys i = ok o) :
    Sim₀ id pers lst o
      (canonEqList (absICILFrom xs i) (absICILFrom ys i)) :=
  Lockstep.LS.toSim₀ (canon_eq_list_aux _ rfl hrel hinv) hrun

end ConRon.Refine2

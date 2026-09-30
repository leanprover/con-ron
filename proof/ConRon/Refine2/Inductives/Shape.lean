/-
# `ConRon.Refine2.Inductives.Shape` — the inductive tier's abstractions

**Task #97-P5-Ind** (DESIGN.md §8.2, Theorem 2), the shared base of
`Refine2/Inductives/**`, lowered by task #105 below the checker tier (it
imports `Checker/Shape`, `ExprOps/Mut`, `Tactic/Prims` and nothing that needs
the Core knot; the environment readers and the `CoreCtx` side alternatives
moved up to `Inductives/Prims.lean`).  `Refine2/Shape.lean` and
`Refine2/Checker/Shape.lean` carry the statement shapes; this file adds the
containers the tier's functions carry and the cursor recipes.  The uniform
route's records are abstracted in `Inductives/Abs.lean`.

## The containers

Every one is a `Vec` against the container the twin chose, and — as in
`Refine2/Checker/Shape.lean` — the `…From` family is DESIGN §3.4's standing
`List`-as-cursor deviation: where the twin recurses structurally on a `List`,
the Rust takes the whole `Vec` and an index.
-/
import ConRon.Refine2.Checker.Shape
import ConRon.Refine2.ExprOps.Mut
import ConRon.Refine2.Tactic.Prims
import ConRon.Refine2.Inductives.FieldTele

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

/-- A `Vec<Vec<LIdx>>` as the twin's `List (List LIdx)` — the fields' sorts,
one list per constructor. -/
def absLIdxLL (v : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx)) :
    List (List LIdx) := v.val.map absLIdxL

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

/-! ## `IRecRule`'s fields -/

theorem absIRecRule_ctor_eq (r : arena.env.IRecRule) :
    (absIRecRule r).ctor = absNIdx r.ctor := rfl
theorem absIRecRule_nfields_eq (r : arena.env.IRecRule) :
    (absIRecRule r).nfields = absU r.nfields := rfl
theorem absIRecRule_rhs_eq (r : arena.env.IRecRule) :
    (absIRecRule r).rhs = absEIdx r.rhs := rfl


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

/-! ### The declaration copies -/

-- `i_ind_caps_dup_abs`, `i_proj_table_dup_abs` and `i_constant_info_dup_abs`
-- moved down to `Refine2/Dup.lean` (task #97-P5-Front round 2).

-- `i_constant_info_name_abs` moved down to `Refine2/Checker/Shape.lean`
-- (task #97-P5-Checker round 4).

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
    simp only [hnil _ hn, am_run_bind']
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
        simp only [am_run_bind', hrun, hout1, bind_assoc, List.map_append,
          List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
          List.nil_append]
        rfl
      rw [key]
      exact Sim₀.dest hih
    | Err e =>
      rw [herr e rfl]
      refine AOut₀.err ?_
      rw [hcons _ hi]
      simp only [am_run_bind']
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

/-- The `(handle, depth)`-keyed memo walk's answer relation.  `@[lockstep_rel]`,
so the zip splits a related answer (`splitRels`) where a walk's continuation
matches on it. -/
@[lockstep_rel] def WOutRel (r : Bool × ron.hashmap2.HashMap2 arena.monad.EIdxNat Bool)
    (v : Bool × Std.HashMap (EIdx × Nat) Bool) : Prop :=
  r.1 = v.1 ∧ ExprOps.WMemoRel r.2 v.2

attribute [simp] absNatL absNatLFrom absBoolL absLIdxLL absBinderL absBinderLFrom
  absCtorsL absCtorsLFrom absCtors3L absCtors3LFrom absRecsL absRecsLFrom

/-! ## Rust-only copies, for the `lockstep` tactic (task #97-T2-LOCKSTEP lane
Inductives round 3)

The two copies `arena::checker::check_ind_decl` makes before it moves its
arguments into the tier: each is the identity on the abstraction. -/

/-! ## The tier's side-goal extension

A twin `if` over values the port computed in Rust-only steps is decided by
their `TwinEq` facts; those are stated at the port's cursor forms
(`absCtors3LFrom cs 0`, `absNIdxL v`), the twin's at its list forms, so the
tier's extension unfolds `TwinEq` and the abstractions and asks `simp_all`. -/

macro_rules
  | `(tactic| lockstep_side_ext) =>
    `(tactic| ((try simp only [Lockstep.TwinEq] at *); first
      | (simp_all [absNIdxL, absCtors3L, absCtors3LFrom, absCtorsL, absCtorsLFrom,
          absIConstantVal, absICIL, absICILFrom, absEIdxL, absEIdxLFrom, NNodeViewWF]; done)))

namespace IndSide

/-- Round 5's side alternatives, SCOPED: active only in the files that
`open scoped ConRon.Refine2.IndSide` (the lane's own), so the lanes that import
this tier (`Frontend/ProjRec.lean`) do not pay for them on every failing side
goal. -/
scoped macro_rules
  | `(tactic| lockstep_side_ext) =>
    `(tactic| ((try simp only [Lockstep.TwinEq] at *); first
      | (simp_all [absIRecRule]; done)
      -- a Rust-computed Bool against the twin's conjunction whose other
      -- conjuncts the port tested before (a length the context pins)
      | (simp only [ExprOps.absEIdxL, absEIdxL, List.length_map, alloc.vec.Vec.len] at *
         simp_all; done)
      -- a memo walk's answer bit, read off its `WOutRel`/`LOutRel`
      | (simp only [WOutRel, LOutRel] at *; simp_all; done)
      -- a `usize` cast of a `u64` the port bounded before (a length, a count):
      -- the overflow arm of the cast's spec is contradictory
      | (casesm* (_ : Nat) = _ ∨ Std.Usize.max < _
         all_goals first
           | (exfalso; scalar_tac)
           | (simp_all [absNIdxL, absEIdxL, absEIdxLFrom, absCtorsL, absCtorsLFrom]; done)
           | (simp_all [absBinderL, List.getElem?_map, List.getElem?_eq_getElem]
              subst_vars; simp_all; done)
           | (simp_all [absBinderL, List.getElem_map, etag_forallE_abs, etag_sort_abs,
               etag_lam_abs, etag_app_abs, etag_const_abs, absU32_eq_forallE_iff,
               forallE_eq_absU32_iff]; done))))

end IndSide

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

@[lockstep_simp] theorem absICILFrom_zero (v) : absICILFrom v 0#usize = absICIL v := by
  simp [absICILFrom, absICIL]

@[lockstep_simp] theorem absNatLFrom_zero (v) : absNatLFrom v 0#usize = absNatL v := by
  simp [absNatLFrom, absNatL]

@[lockstep_simp] theorem absBinderLFrom_zero (v) : absBinderLFrom v 0#usize = absBinderL v := by
  simp [absBinderLFrom, absBinderL]

@[lockstep_simp] theorem absCtorsLFrom_zero (v) : absCtorsLFrom v 0#usize = absCtorsL v := by
  simp [absCtorsLFrom, absCtorsL]

@[lockstep_simp] theorem absCtors3LFrom_zero (v) : absCtors3LFrom v 0#usize = absCtors3L v := by
  simp [absCtors3LFrom, absCtors3L]

@[lockstep_simp] theorem absRecsLFrom_zero (v) : absRecsLFrom v 0#usize = absRecsL v := by
  simp [absRecsLFrom, absRecsL]

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
/-- `kernel::expr::binder_meta_dup` is the identity (a Rust-only copy). -/
@[lockstep] theorem binder_meta_dup_spec (m : kernel.expr.BinderMeta) :
    LSP (kernel.expr.binder_meta_dup m) (fun a => a = m) :=
  fun _ h => ConRon.Refine.Expr.binder_meta_dup_eq h

/-- `arena::core::append_eidx_from` appends `ys` from the cursor on. -/
theorem append_eidx_from_abs {xs ys : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize}
    {o : alloc.vec.Vec arena.handle.EIdx}
    (hrun : arena.core.append_eidx_from xs ys i = ok o) :
    absEIdxL o = absEIdxL xs ++ (ys.val.drop i.val).map absEIdx := by
  simp only [absEIdxL]
  refine vec_cursor_copy ys absEIdx absEIdx
    (fun i out => arena.core.append_eidx_from out ys i) ?_ ?_ i xs o hrun
  · intro i out o hn h
    rw [arena.core.append_eidx_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ys by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.core.append_eidx_from.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ys by
      have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, e1, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [dupId_eidx _ _ he1], h⟩

open Lockstep in
/-- `arena::core::append_eidx` is the twin's `++`. -/
@[lockstep] theorem append_eidx_twin (xs ys : alloc.vec.Vec arena.handle.EIdx) :
    LSP (arena.core.append_eidx xs ys)
      (fun o => TwinEq (absEIdxL xs ++ absEIdxL ys) (absEIdxL o)) := by
  intro o h
  rw [arena.core.append_eidx] at h
  have := append_eidx_from_abs h
  simp only [absEIdxL] at this
  simp only [Lockstep.TwinEq, absEIdxL, this]
  simp

/-- `arena::core::drop_eidx_from` copies `xs` from the cursor on. -/
theorem drop_eidx_from_abs {xs : alloc.vec.Vec arena.handle.EIdx} {k : Std.Usize}
    {out o : alloc.vec.Vec arena.handle.EIdx}
    (hrun : arena.core.drop_eidx_from xs k out = ok o) :
    absEIdxL o = absEIdxL out ++ (xs.val.drop k.val).map absEIdx := by
  simp only [absEIdxL]
  refine vec_cursor_copy xs absEIdx absEIdx
    (fun i out => arena.core.drop_eidx_from xs i out) ?_ ?_ k out o hrun
  · intro i out o hn h
    rw [arena.core.drop_eidx_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [arena.core.drop_eidx_from.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by
      have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact ⟨i2, e1, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1,
      by rw [dupId_eidx _ _ he1], h⟩

/-- `arena::core::drop_eidx_n_from` drops `n` more from the cursor on. -/
theorem drop_eidx_n_from_abs {xs : alloc.vec.Vec arena.handle.EIdx} :
    ∀ (m : Nat) (n : Std.U64) (i : Std.Usize) (o : alloc.vec.Vec arena.handle.EIdx),
      n.val = m → arena.core.drop_eidx_n_from xs n i = ok o →
      absEIdxL o = (xs.val.drop (i.val + n.val)).map absEIdx := by
  intro m
  induction m with
  | zero =>
    intro n i o hn h
    rw [arena.core.drop_eidx_n_from.eq_def, if_pos (by scalar_tac)] at h
    rw [drop_eidx_from_abs h, hn]
    simp [absEIdxL, alloc.vec.Vec.new]
  | succ m ih =>
    intro n i o hn h
    rw [arena.core.drop_eidx_n_from.eq_def, if_neg (by scalar_tac)] at h
    by_cases hi : i ≥ alloc.vec.Vec.len xs
    · rw [if_pos hi, Result.ok.injEq] at h
      subst h
      rw [List.drop_eq_nil_of_le (by simp [alloc.vec.Vec.len] at hi; omega)]
      simp [absEIdxL, alloc.vec.Vec.new]
    · rw [if_neg hi] at h
      obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h1 := ConRon.Refine.Nat.usub_val hn1
      have h2 := ConRon.Refine.Nat.uadd_val hi1
      simp only [alloc.vec.Vec.len] at hi
      rw [ih n1 i1 o (by simp at h1 h2 ⊢; omega) h]
      congr 2
      simp at h1 h2 ⊢; omega

open Lockstep in
/-- `arena::core::drop_eidx_n` is the twin's `List.drop`. -/
@[lockstep] theorem drop_eidx_n_twin (xs : alloc.vec.Vec arena.handle.EIdx) (n : Std.U64) :
    LSP (arena.core.drop_eidx_n xs n)
      (fun o => TwinEq ((absEIdxL xs).drop (absU n)) (absEIdxL o)) := by
  intro o h
  rw [arena.core.drop_eidx_n] at h
  rw [Lockstep.TwinEq, drop_eidx_n_from_abs _ n 0#usize o rfl h]
  simp [absEIdxL, List.map_drop, absU]

open Lockstep in
/-- `arena::core::drop_eidx` is the twin's `List.drop`. -/
@[lockstep] theorem drop_eidx_twin (xs : alloc.vec.Vec arena.handle.EIdx) (k : Std.Usize) :
    LSP (arena.core.drop_eidx xs k)
      (fun o => TwinEq ((absEIdxL xs).drop k.val) (absEIdxL o)) := by
  intro o h
  rw [arena.core.drop_eidx] at h
  rw [Lockstep.TwinEq, drop_eidx_from_abs h]
  simp [absEIdxL, List.map_drop, alloc.vec.Vec.new]


/-! ## Round 5 slice 2: the counted recipe with an accumulator, the domain read -/

open Lockstep in
/-- The COUNTED cursor recursion with an accumulator: the port walks a `u64`
cursor `i` up to `n` pushing onto `w`, the twin recurses on the count
`n - i` from `i`.  A caller proves the stop and the step case, each by
unfolding one equation on each side and `lockstep`, the induction hypothesis
(at `i + 1`, any accumulator) in the context. -/
theorem ls_counted {γ δ ω : Type} {pers : arena.store.PersTier} {R : γ → δ → Prop}
    (n : Std.U64) (G : ω → Nat → Nat → AM δ)
    (F : arena.monad.AState → Std.U64 → ω →
      Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState))
    (hstop : ∀ st lst (i : Std.U64) w, n.val ≤ i.val →
      AStateRel₀ pers st lst → AStateInv pers st → LS pers R (F st i w) lst (G w 0 i.val))
    (hstep : ∀ st lst (i : Std.U64) w (m : Nat), i.val < n.val → n.val - i.val = m + 1 →
      AStateRel₀ pers st lst → AStateInv pers st →
      (∀ st' lst' (j : Std.U64) w', j.val = i.val + 1 →
        AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers R (F st' j w') lst' (G w' m j.val)) →
      LS pers R (F st i w) lst (G w (m + 1) i.val)) :
    ∀ (i : Std.U64) st lst w, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers R (F st i w) lst (G w (n.val - i.val) i.val) := by
  suffices H : ∀ (m : Nat) (i : Std.U64) st lst w, n.val - i.val = m →
      AStateRel₀ pers st lst → AStateInv pers st → LS pers R (F st i w) lst (G w m i.val) by
    intro i st lst w hrel hinv; exact H _ i st lst w rfl hrel hinv
  intro m
  induction m with
  | zero =>
    intro i st lst w hm hrel hinv
    exact hstop st lst i w (by omega) hrel hinv
  | succ m ih =>
    intro i st lst w hm hrel hinv
    exact hstep st lst i w m (by omega) hm hrel hinv
      (fun st' lst' j w' hj hrel' hinv' => ih j st' lst' w' (by omega) hrel' hinv')

/-- The port's `dom := if k < len then v[k].0 else EIdx(0)` against the
twin's `(cbs.getD k default).1`: `lockstep` zips both reads (task
#97-T2-TACTIC round 3: the pair read by structure eta, `EIdx(0)` by
`eidx_of_word_spec`); left is the twin's `getD` off the end. -/
macro "ind_dom_finish" : tactic => `(tactic|
  (first | rw [binderL_getD_fst_of_ge] | rw [absBinderL_getD_fst_of_ge]
   · lockstep; done
   · scalar_tac))

open Lockstep in
/-- The twin of an `LS` judgement may be replaced by an equal one (the
accumulator step: the induction hypothesis's `A (out.push b) ++ rest` against
the step's `A out ++ f b :: rest`). -/
theorem LS.twin_eq {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x y : AM β} (h : LS pers R m lst x) (e : x = y) : LS pers R m lst y :=
  e ▸ h

/-- `takeEidx` is `List.take` on the array's list (the tier's copy of the
Core regions' `takeEidx_toList'`, which is region-local). -/
theorem ind_takeEidx_toList (xs : Array EIdx) (k : Nat) :
    (takeEidx xs k).toList = xs.toList.take k := by
  rw [takeEidx, ExprOps.eidxCopyUpto_toList xs k k 0 #[] (by omega)]
  simp

/-- The port's `take_eidx_n` fact (stated by `Tactic/Prims.lean` at arrays)
read at the tier's lists. -/
theorem absEIdxL_of_takeEidx {a b : alloc.vec.Vec arena.handle.EIdx} {n : Nat}
    (h : ExprOps.absEIdxArr a = takeEidx (ExprOps.absEIdxArr b) n) :
    absEIdxL a = (absEIdxL b).take n := by
  have := congrArg Array.toList h
  rw [ind_takeEidx_toList] at this
  simpa [ExprOps.absEIdxArr, ExprOps.absEIdxL, absEIdxL] using this

open Lockstep in
/-- `arena::expr_ops::take_eidx_n` is the twin's `List.take` (`drop_eidx_n_twin`'s
sibling; not `@[lockstep]`: a caller registers it `local lockstep high` ahead
of the array-level `take_eidx_n_spec`). -/
theorem take_eidx_n_twin (xs : alloc.vec.Vec arena.handle.EIdx) (n : Std.U64) :
    LSP (arena.expr_ops.take_eidx_n xs n)
      (fun r => TwinEq ((absEIdxL xs).take (absU n)) (absEIdxL r)) := by
  intro r h
  have := absEIdxL_of_takeEidx (take_eidx_n_spec xs n r h)
  simpa [TwinEq, absU] using this.symm

/-! ## Round 6: a binder telescope the port re-interns is well formed

`intern_e_{lam,forall_e}_wf_ls` need `PropWhenWF` of the datum (the erased
subtype invariant of con-leche's `PropWhen`).  The telescopes the tier's
builders re-intern are made by `struct_tele_at` from one `pw`, so the fact is
carried as `TeleWF` — a named predicate, not a `∀`, so the side tactic (which
clears `∀` hypotheses) keeps it in the context. -/

/-- Every binder datum of the telescope is well formed. -/
def TeleWF (v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) : Prop :=
  ∀ p ∈ v.val, ConRon.Refine.PropWhenWF p.2.pw

theorem TeleWF.new : TeleWF (alloc.vec.Vec.new (arena.handle.EIdx × kernel.expr.BinderMeta)) := by
  intro p hp; simp [alloc.vec.Vec.new] at hp

theorem TeleWF.push {v w : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {x : arena.handle.EIdx × kernel.expr.BinderMeta}
    (hw : w.val = v.val ++ [x]) (hv : TeleWF v) (hx : ConRon.Refine.PropWhenWF x.2.pw) :
    TeleWF w := by
  intro p hp
  rw [hw, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact hv p hp
  · exact hx

theorem TeleWF.get {v : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    (hv : TeleWF v) (k : Nat) (hk : k < v.val.length) :
    ConRon.Refine.PropWhenWF (v.val[k]).2.pw :=
  hv _ (List.getElem_mem hk)

namespace Lockstep

/-- A twin-only `map` on the answer: the Rust computation's relation to `x`
carried to `x`'s image. -/
theorem LS.twin_map {α β γ : Type} {pers : arena.store.PersTier} {R₁ : α → β → Prop}
    {R : α → γ → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} {f : β → γ}
    (h : LS pers R₁ m lst x) (hR : ∀ a b, R₁ a b → R a (f b)) :
    LS pers R m lst (x >>= fun b => Pure.pure (f b)) := by
  intro o st' hm
  have h1 := h o st' hm
  cases o with
  | Err e => exact errSim_bind h1
  | Ok a =>
    obtain ⟨b, lst', hx, hR1, h2, h3⟩ := h1
    exact ⟨f b, lst', by rw [StateT.run_bind, hx]; rfl, hR _ _ hR1, h2, h3⟩

end Lockstep

/-! ## `unwrapOr` at a constructor

The port matches the `Option` itself where the twin `unwrapOr`s it.  Scoped:
`open scoped ConRon.Refine2.IndInstPrims`, or registered `local`. -/

namespace IndInstPrims

@[scoped lockstep_simp] theorem unwrapOr_some' {α : Type} (a : α) (e : Arena.CheckError) :
    unwrapOr (some a) e = pure a := rfl

@[scoped lockstep_simp] theorem unwrapOr_none' {α : Type} (e : Arena.CheckError) :
    unwrapOr (none : Option α) e = Arena.fail e := rfl

end IndInstPrims

namespace IndSide

/-- Round 6's side alternative: a telescope's `TeleWF` after a `push`, and a
read datum's `PropWhenWF` out of a `TeleWF` telescope. -/
scoped macro_rules
  | `(tactic| lockstep_side_ext) =>
    `(tactic| first
      | (refine TeleWF.push (by assumption) (by assumption) ?_; simp_all; done)
      | (subst_vars; first
          | exact TeleWF.get (by assumption) _ (by scalar_tac)
          | (simp_all; done)))

end IndSide

end ConRon.Refine2

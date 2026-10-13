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

theorem absIRecRule_nfields_eq (r : arena.env.IRecRule) :
    (absIRecRule r).nfields = absU r.nfields := rfl


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
    rw [ite_eq_left hl] at h
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
        rw [ite_eq_left (show i ≥ alloc.vec.Vec.len a by scalar_tac), Result.ok.injEq] at h
        rw [← h, List.drop_eq_nil_of_le hn,
          List.drop_eq_nil_of_le (show b.val.length ≤ i.val by omega)]
        simp
      · intro i _ hi ih o h
        rw [arena.core.nidx_vec_beq_from.eq_def] at h
        rw [ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len a by scalar_tac)] at h
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
          rw [ite_eq_right (by simp), Result.ok.injEq] at h
          rw [← h]
          simp only [List.cons_beq_cons, ← hbv]
          simp
        · rw [hbb] at h hbv
          rw [ite_eq_left (by simp)] at h
          obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
          rw [ih i2 () hi2v o h, hi2v]
          simp only [List.cons_beq_cons, ← hbv]
          simp
    rw [key 0#usize o h]
    simp [absNIdxL, show ((0#usize : Std.Usize)).val = 0 by scalar_tac]
  · rw [ite_eq_right hl, Result.ok.injEq] at h
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

end ConRon.Refine2

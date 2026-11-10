/-
# `ConRon.Refine2.Promote.Prims` — `@[lockstep]` primitive pairs above the core

`Tactic/Prims.lean`'s pairs, for what the tiers above the core step over that
the core does not: the level and level-list views, the expression view with its
key predicate, the tier-bit tests, and the Rust-only copies of the record value
types.  Every lemma is an existing `Refine2/Specs.lean` statement put in the
judgement shape `Tactic/Lockstep.lean` steps with.

**The expression view carries the Rust view's key predicate** (`ENodeViewWF`):
the cons key of a `Lit` is a literal, and the abstraction is exact on
well-formed ones only.  It is a fact about the RUST store alone (`StoreInv`'s
`nodesP`), so it is a legitimate lockstep premise.
-/
import ConRon.Refine2.Checker.Shape
import ConRon.Refine2.Tactic.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The expression view's key predicate, from the Rust store alone -/

/- One `ETables::get` arm whose view carries no value: well formed by
`ENodeViewWF`'s catch-all. -/
set_option hygiene false in
local macro "vwf_triv" : tactic => `(tactic| (
    obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases p with
    | none => simp at h
    | some r =>
      try dsimp only at h
      repeat (rust_bind_guard h; obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h)
      have h' := Result.ok_injective h
      simp only [Option.some.injEq] at h'
      subst h'; trivial))

/-! ## The port's cursor recursion, as a twin helper

Every `_from` / `_go` cursor of these two tiers is the same Rust shape: at the
cursor's end answer the accumulator, else step the element, push its answer,
and recurse at `i + 1`.  The twins are plain `List` recursions that CONS the
answer onto the recursive result.  `pmapFrom` is the cursor recursion spelled
over the twin's `List` (the accumulator threaded, the call a tail call), so
that a cursor lemma is a zip; `pmapFrom_acc` / `pmapFrom_eq` tie it back to
the twin's own list function. -/

/-- A state-threading list map with an accumulator, over the twin's monad. -/
def pmapFrom {σ γ δ : Type} (f : σ → γ → AM (σ × δ)) (m : σ) (acc : List δ) :
    List γ → AM (σ × List δ)
  | [] => pure (m, acc)
  | x :: xs => do
    let (m, y) ← f m x
    pmapFrom f m (acc ++ [y]) xs


/-- The twin's cons-recursion is `pmapFrom` at the empty accumulator. -/
theorem pmapFrom_cons_eq {σ γ δ : Type} (f : σ → γ → AM (σ × δ))
    (F : σ → List γ → AM (σ × List δ))
    (hnil : ∀ m, F m [] = pure (m, []))
    (hcons : ∀ m x xs, F m (x :: xs) =
      (do let (m, y) ← f m x; let (m, ys) ← F m xs; pure (m, y :: ys))) :
    ∀ (l : List γ) (m : σ) (acc : List δ),
      pmapFrom f m acc l = (do let (m, ys) ← F m l; pure (m, acc ++ ys)) := by
  intro l
  induction l with
  | nil => intro m acc; simp [pmapFrom, hnil]
  | cons x xs ih =>
    intro m acc
    simp only [pmapFrom, hcons, bind_assoc]
    congr 1
    funext p
    obtain ⟨m', y⟩ := p
    simp only
    rw [ih m' (acc ++ [y])]
    simp [List.append_assoc]

theorem vecFrom_nil {α β : Type} (v : alloc.vec.Vec α) (f : α → β) (i : Std.Usize)
    (hi : v.val.length ≤ i.val) : (v.val.drop i.val).map f = [] := by
  rw [List.drop_eq_nil_of_le hi]; rfl

theorem vecFrom_cons {α β : Type} (v : alloc.vec.Vec α) (f : α → β) (i : Std.Usize)
    (hi : i.val < v.val.length) :
    (v.val.drop i.val).map f = f v.val[i.val] :: (v.val.drop (i.val + 1)).map f := by
  rw [List.drop_eq_getElem_cons hi]; rfl

namespace Lockstep

/-! ## Conversions -/

/-- A reader stated as `AOut₀` at the state it reads is an `LSR`. -/
theorem LSR.ofAOut₀ {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {m : Result (core.result.Result α kernel.core_types.CheckError)}
    {st : arena.monad.AState} {lst : AState} {x : AM β}
    (h : ∀ o, m = ok o → AOut₀ A pers o st (x.run lst)) :
    LSR pers (fun a b => b = A a) m st lst x := by
  intro o hm
  have := h o hm
  cases o with
  | Err e => exact this
  | Ok a =>
    obtain ⟨lst', hx, h1, h2⟩ := this
    exact ⟨A a, lst', hx, rfl, h1, h2⟩

/-! ## The level and level-list views -/

@[lockstep] theorem view_l_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.LIdx) :
    LSR pers (fun a b => b = absLNodeView a) (arena.monad.view_l pers st h)
      st lst (Arena.viewL (absLIdx h)) :=
  LSR.ofAOut₀ fun _ hr => view_l_run₀ hrel hinv hr

@[lockstep] theorem view_lsv_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.LsIdx) :
    LSR pers (fun a b => b = absLsNodeView a) (arena.monad.view_ls pers st h)
      st lst (Arena.viewLs (absLsIdx h)) :=
  LSR.ofAOut₀ fun _ hr => view_ls_run₀ hrel hinv hr

attribute [lockstep_simp] absNNodeView absLNodeView absLsNodeView absLIdxL absNIdxL absEIdxL

/-! ## Rust-only copies of the value types the records carry -/

@[lockstep] theorem rhint_dup_spec (h1 : kernel.env.ReducibilityHint) :
    LSP (kernel.env.reducibility_hint_dup h1) (fun r => r = h1) := by
  intro r h
  cases h1 <;> simp only [kernel.env.reducibility_hint_dup, Result.ok.injEq] at h <;>
    exact h.symm

/-- `arena::env::i_ind_caps_dup` is the identity. -/
@[lockstep] theorem i_ind_caps_dup_spec (c : arena.env.IIndCaps) :
    LSP (arena.env.i_ind_caps_dup c) (fun o => o = c) := by
  intro o h
  rw [arena.env.i_ind_caps_dup] at h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h,
    alloc.vec.Vec.ext _ _ (nidx_vec_dup_val hv), alloc.vec.Vec.ext _ _ (nidx_vec_dup_val hv1)]

@[lockstep] theorem basis_kind_dup_spec (k : kernel.env.BasisKind) :
    LSP (kernel.env.basis_kind_dup k) (fun r => r = k) := by
  intro r h
  cases k <;> simp only [kernel.env.basis_kind_dup, Result.ok.injEq] at h <;> exact h.symm


end Lockstep

end ConRon.Refine2

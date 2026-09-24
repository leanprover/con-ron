/-
# `ConRon.Refine2.Promote.Prims` — the promote tier's `@[lockstep]` primitive pairs

Task #97-T2-LOCKSTEP lane Promote.  `Tactic/Prims.lean`'s pairs, for what
the promotion walk steps over that no earlier tier did: the name/level/list
views, the four persistent interns, the tier-bit tests, `dup2` at the three
small handle kinds, and the promotion memo's eight primitives.  Every lemma
is an existing `Refine2/Specs.lean` / `Promote/Promote.lean` statement put in
the judgement shape `Tactic/Lockstep.lean` steps with.

**The views carry the Rust view's key predicate** (`NNodeViewWF`,
`ENodeViewWF`): the persistent interns take it (the cons key of a `Str`
name is a string, of a `Lit` a literal, of a binder a `PropWhen`, and the
abstraction is exact on well-formed ones only), and a promotion re-interns
exactly what it viewed.  It is a fact about the RUST store alone
(`StoreInv`'s `nodesP`), so it is a legitimate lockstep premise.
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
      repeat (obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h)
      have h' := Result.ok_injective h
      simp only [Option.some.injEq] at h'
      subst h'; trivial))

theorem etables_get_wf {rt} (hinv : ETablesInv rt)
    {i : arena.handle.EIdx} {o : Option arena.store.ENodeView}
    (h : arena.store.ETables.get rt i = ok o) : ∀ v, o = some v → ENodeViewWF v := by
  intro v hv
  subst hv
  rw [arena.store.ETables.get] at h
  obtain ⟨t, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · vwf_triv
  split at h
  · vwf_triv
  split at h
  · vwf_triv
  split at h
  · vwf_triv
  split at h
  · vwf_triv
  obtain ⟨b, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · simp at h
  split at h
  · vwf_triv
  split at h
  · obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hnwf := tbl_node_wf hinv.lits hp
    cases p with
    | none => simp at h
    | some r =>
      try dsimp only at h
      obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h' := Result.ok_injective h
      simp only [Option.some.injEq] at h'
      subst h'
      show ConRon.Refine.LiteralWF l
      rw [ConRon.Refine.Expr.literal_dup_eq hl]
      exact hnwf r rfl
  split at h
  · vwf_triv
  · simp at h

/-- **The Rust store's view is well formed** — `StoreInv`'s `nodesP` at the
two tables whose records carry a value (`lits`, `bms`). -/
theorem estore_view_wf {pers rs} (hinv : StoreInv pers rs)
    {i : arena.handle.EIdx} {o : Option arena.store.ENodeView}
    (h : arena.store.EStore.view rs pers i = ok o) :
    ∀ v, o = some v → ENodeViewWF v := by
  rw [arena.store.EStore.view] at h
  obtain ⟨t, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨b, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases q with
    | none => rw [← Result.ok_injective h]; intro v hv; simp at hv
    | some tr =>
      obtain ⟨ty, body, bm⟩ := tr
      simp only at h
      obtain ⟨ev, hev, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [← Result.ok_injective h]
      intro v hv; simp only [Option.some.injEq] at hv; subst hv
      rw [arena.store.EStore.view_bind] at hq
      obtain ⟨q1, -, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq
      cases q1 with
      | none => cases Result.ok_injective hq
      | some t1 =>
        obtain ⟨e0, e1, bmi⟩ := t1
        simp only at hq
        obtain ⟨q2, hq2, hq⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq
        cases q2 with
        | none => cases Result.ok_injective hq
        | some m =>
          simp only [Result.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hq
          obtain ⟨-, -, rfl⟩ := hq
          have hpw := estore_view_bm_wf hinv hq2 m rfl
          rw [arena.store.e_bind_view] at hev
          split at hev
          · cases Result.ok_injective hev; exact hpw
          · cases Result.ok_injective hev; exact hpw
  · obtain ⟨b1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    split at h
    · rw [arena.store.EStore.pers_get] at h
      have hp := hinv.perst
      rw [rPersE] at hp
      split at h <;> rename_i hs
      · rw [if_pos hs] at hp; exact etables_get_wf hp h
      · rw [if_neg hs] at hp; exact etables_get_wf hp h
    · split at h
      · exact etables_get_wf hinv.scrt h
      · rw [← Result.ok_injective h]; intro v hv; simp at hv

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

theorem pmapFrom_acc {σ γ δ : Type} (f : σ → γ → AM (σ × δ)) :
    ∀ (l : List γ) (m : σ) (acc : List δ),
      pmapFrom f m acc l = (do let (m, ys) ← pmapFrom f m [] l; pure (m, acc ++ ys)) := by
  intro l
  induction l with
  | nil => intro m acc; simp [pmapFrom]
  | cons x xs ih =>
    intro m acc
    simp only [pmapFrom, bind_assoc, List.nil_append]
    congr 1
    funext p
    obtain ⟨m', y⟩ := p
    simp only
    rw [ih m' (acc ++ [y]), ih m' [y]]
    simp [bind_assoc, List.append_assoc]

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
    simp [bind_assoc, List.append_assoc]

theorem vecFrom_nil {α β : Type} (v : alloc.vec.Vec α) (f : α → β) (i : Std.Usize)
    (hi : v.val.length ≤ i.val) : (v.val.drop i.val).map f = [] := by
  rw [List.drop_eq_nil_of_le hi]; rfl

theorem vecFrom_cons {α β : Type} (v : alloc.vec.Vec α) (f : α → β) (i : Std.Usize)
    (hi : i.val < v.val.length) :
    (v.val.drop i.val).map f = f v.val[i.val] :: (v.val.drop (i.val + 1)).map f := by
  rw [List.drop_eq_getElem_cons hi]; rfl

/-- A `usize` cast up to `u64` is exact (the platform word is at most 64
bits). -/
theorem usize_cast_u64_val (i : Std.Usize) : (UScalar.cast .U64 i).val = i.val := by
  apply UScalar.cast_val_mod_pow_of_inBounds_eq
  have h3 : Std.Usize.max < 2 ^ UScalarTy.Usize.numBits := by
    rw [Std.Usize.max_def, Std.Usize.numBits_def]
    have : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
    omega
  have h4 : 2 ^ UScalarTy.Usize.numBits ≤ 2 ^ UScalarTy.U64.numBits := by
    apply Nat.pow_le_pow_right (by decide)
    rw [UScalarTy.Usize_numBits_eq, UScalarTy.U64_numBits_eq]
    cases System.Platform.numBits_eq with
    | inl h => rw [h]; decide
    | inr h => rw [h]
  have := i.hBounds
  scalar_tac

/-! ## A frozen state and its tier, read as ONE state (task #98-FREEZE)

Promotion runs inside a declaration bracket: it READS the frozen state `st`
(its scratch tier, and its persistent tables through the tier) and WRITES the
tier `t` the bracket owns, through `&mut PersTier`.  The judgement it is
proved in (`LST`) needs a state to relate at every step: `glue t st` is `st`
with the tables it is read at through `t` put back as its own, read through
any stand-in that is not `frozen` — the same data, so the relation and the
reads are unchanged (`glue_rel`, `view_glue`).  It is a proof device: the
Rust never builds it. -/

/-- `st`'s store with the tables it is read at through `t` as its own. -/
def glueE (t : arena.store.PersTier) (s : arena.store.EStore) : arena.store.EStore :=
  { s with
    lss := { s.lss with
      ls := { s.lss.ls with
        ns := { s.lss.ls.ns with pers := rPersN t s.lss.ls.ns },
        pers := rPersL t s.lss.ls },
      pers := rPersLs t s.lss },
    pers := rPersE t s }

/-- A frozen state and its tier, as one state. -/
def glue (t : arena.store.PersTier) (st : arena.monad.AState) : arena.monad.AState :=
  { st with store := glueE t st.store }

/-- The four scratch tiers are on: a frozen store's shape (`StoreInv.frz`). -/
def ScratchOn (s : arena.store.EStore) : Prop :=
  s.scratch_on = true ∧ s.lss.scratch_on = true ∧ s.lss.ls.scratch_on = true ∧
    s.lss.ls.ns.scratch_on = true

theorem ScratchOn.of_inv {t : arena.store.PersTier} {st : arena.monad.AState}
    (hinv : AStateInv t st) (ht : t.frozen = true) : ScratchOn st.store :=
  ⟨hinv.store.frz ht, hinv.store.lss.frz ht, hinv.store.lss.lvl.frz ht,
    hinv.store.lss.lvl.ns.frz ht⟩

/-- **The glued state is related, through a stand-in, exactly as the frozen
state is through its tier.** -/
theorem glue_rel {P t : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (hP : P.frozen = false) : AStateRel₀ P (glue t st) lst ↔ AStateRel₀ t st lst := by
  have hN : rPersN P (glueE t st.store).lss.ls.ns = rPersN t st.store.lss.ls.ns := by
    simp [rPersN, glueE, hP]
  have hL : rPersL P (glueE t st.store).lss.ls = rPersL t st.store.lss.ls := by
    simp [rPersL, glueE, hP]
  have hLs : rPersLs P (glueE t st.store).lss = rPersLs t st.store.lss := by
    simp [rPersLs, glueE, hP]
  have hE : rPersE P (glueE t st.store) = rPersE t st.store := by
    simp [rPersE, glueE, hP]
  constructor
  · intro h
    obtain ⟨⟨⟨⟨⟨np, ns, non⟩, lp, ls, lon⟩, lsp, lss, lson⟩, ep, es, eon⟩, m, c, pn⟩ := h
    exact ⟨⟨⟨⟨⟨hN ▸ np, ns, non⟩, hL ▸ lp, ls, lon⟩, hLs ▸ lsp, lss, lson⟩, hE ▸ ep, es, eon⟩,
      m, c, pn⟩
  · intro h
    obtain ⟨⟨⟨⟨⟨np, ns, non⟩, lp, ls, lon⟩, lsp, lss, lson⟩, ep, es, eon⟩, m, c, pn⟩ := h
    exact ⟨⟨⟨⟨⟨hN ▸ np, ns, non⟩, hL ▸ lp, ls, lon⟩, hLs ▸ lsp, lss, lson⟩, hE ▸ ep, es, eon⟩,
      m, c, pn⟩

/-- **The invariant, likewise** — back from the glued state given the frozen
store's scratch tiers on (its `frz` is then the frozen store's). -/
theorem glue_inv {P t : arena.store.PersTier} {st : arena.monad.AState}
    (hP : P.frozen = false) (hsc : ScratchOn st.store) :
    AStateInv P (glue t st) ↔ AStateInv t st := by
  have hN : rPersN P (glueE t st.store).lss.ls.ns = rPersN t st.store.lss.ls.ns := by
    simp [rPersN, glueE, hP]
  have hL : rPersL P (glueE t st.store).lss.ls = rPersL t st.store.lss.ls := by
    simp [rPersL, glueE, hP]
  have hLs : rPersLs P (glueE t st.store).lss = rPersLs t st.store.lss := by
    simp [rPersLs, glueE, hP]
  have hE : rPersE P (glueE t st.store) = rPersE t st.store := by
    simp [rPersE, glueE, hP]
  obtain ⟨s0, s1, s2, s3⟩ := hsc
  have hoff : ∀ {b : Bool}, P.frozen = true → b = true := fun h => by
    rw [hP] at h; cases h
  constructor
  · intro h
    obtain ⟨⟨⟨⟨⟨np, ns, -⟩, lp, ls, -⟩, lsp, lss, -⟩, ep, es, -⟩, m, c⟩ := h
    exact ⟨⟨⟨⟨⟨hN ▸ np, ns, fun _ => s3⟩, hL ▸ lp, ls, fun _ => s2⟩, hLs ▸ lsp, lss,
      fun _ => s1⟩, hE ▸ ep, es, fun _ => s0⟩, m, c⟩
  · intro h
    obtain ⟨⟨⟨⟨⟨np, ns, -⟩, lp, ls, -⟩, lsp, lss, -⟩, ep, es, -⟩, m, c⟩ := h
    exact ⟨⟨⟨⟨⟨hN ▸ np, ns, hoff⟩, hL ▸ lp, ls, hoff⟩, hLs ▸ lsp, lss, hoff⟩, hE ▸ ep, es,
      hoff⟩, m, c⟩

/-! ### The reads of a frozen state are the glued state's -/

theorem view_n_glue {P t : arena.store.PersTier} {st : arena.monad.AState}
    {h : arena.handle.NIdx} (hP : P.frozen = false) :
    arena.monad.view_n t st h = arena.monad.view_n P (glue t st) h := by
  simp only [arena.monad.view_n, arena.store.EStore.ns, arena.store.NStore.view,
    arena.store.NStore.pers_get, glue, glueE, rPersN, hP]
  cases t.frozen <;> simp

theorem view_l_glue {P t : arena.store.PersTier} {st : arena.monad.AState}
    {h : arena.handle.LIdx} (hP : P.frozen = false) :
    arena.monad.view_l t st h = arena.monad.view_l P (glue t st) h := by
  simp only [arena.monad.view_l, arena.store.EStore.ls, arena.store.LStore.view,
    arena.store.LStore.pers_get, glue, glueE, rPersL, hP]
  cases t.frozen <;> simp

theorem view_ls_glue {P t : arena.store.PersTier} {st : arena.monad.AState}
    {h : arena.handle.LsIdx} (hP : P.frozen = false) :
    arena.monad.view_ls t st h = arena.monad.view_ls P (glue t st) h := by
  simp only [arena.monad.view_ls, arena.store.EStore.ls_s, arena.store.LsStore.view,
    arena.store.LsStore.pers_get, glue, glueE, rPersLs, hP]
  cases t.frozen <;> simp

theorem view_glue {P t : arena.store.PersTier} {st : arena.monad.AState}
    {h : arena.handle.EIdx} (hP : P.frozen = false) :
    arena.monad.view t st h = arena.monad.view P (glue t st) h := by
  simp only [arena.monad.view, arena.store.EStore.view, arena.store.EStore.view_bind,
    arena.store.EStore.view_bind_i, arena.store.EStore.view_bm,
    arena.store.EStore.pers_get, arena.store.EStore.pers_get_bind,
    arena.store.EStore.pers_get_bm, glue, glueE, rPersE, hP]
  cases t.frozen <;> simp

/-! ### A promote-intern keeps the tier frozen -/

theorem intern_persistent_n_frozen {t st v r t'}
    (h : arena.monad.intern_persistent_n t st v = ok (r, t')) : t'.frozen = t.frozen := by
  rw [arena.monad.intern_persistent_n, arena.store.PersTier.intern_n] at h
  repeat' (first
    | (obtain ⟨-, rfl⟩ := (by simpa only [Prod.mk.injEq] using Result.ok_injective h :
        _ ∧ _); rfl)
    | (obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; try dsimp only at h)
    | split at h)

theorem intern_persistent_l_frozen {t st v r t'}
    (h : arena.monad.intern_persistent_l t st v = ok (r, t')) : t'.frozen = t.frozen := by
  rw [arena.monad.intern_persistent_l, arena.store.PersTier.intern_l] at h
  repeat' (first
    | (obtain ⟨-, rfl⟩ := (by simpa only [Prod.mk.injEq] using Result.ok_injective h :
        _ ∧ _); rfl)
    | (obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; try dsimp only at h)
    | split at h)

theorem intern_persistent_ls_frozen {t st v r t'}
    (h : arena.monad.intern_persistent_ls t st v = ok (r, t')) : t'.frozen = t.frozen := by
  rw [arena.monad.intern_persistent_ls, arena.store.PersTier.intern_ls] at h
  repeat' (first
    | (obtain ⟨-, rfl⟩ := (by simpa only [Prod.mk.injEq] using Result.ok_injective h :
        _ ∧ _); rfl)
    | (obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; try dsimp only at h)
    | split at h)

theorem pertier_intern_bm_frozen {t m r t'}
    (h : arena.store.PersTier.intern_bm t m = ok (r, t')) : t'.frozen = t.frozen := by
  rw [arena.store.PersTier.intern_bm] at h
  repeat' (first
    | (obtain ⟨-, rfl⟩ := (by simpa only [Prod.mk.injEq] using Result.ok_injective h :
        _ ∧ _); rfl)
    | (obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h; try dsimp only at h)
    | split at h)

theorem pertier_intern_bm_of_view_frozen {t v r t'}
    (h : arena.store.PersTier.intern_bm_of_view t v = ok (r, t')) : t'.frozen = t.frozen := by
  cases v <;> simp only [arena.store.PersTier.intern_bm_of_view] at h <;>
    first
    | (obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
       first
       | exact pertier_intern_bm_frozen h
       | (obtain ⟨-, rfl⟩ := (by simpa only [Prod.mk.injEq] using Result.ok_injective h :
            _ ∧ _); rfl))

theorem intern_persistent_e_frozen {t st v r t'}
    (h : arena.monad.intern_persistent_e t st v = ok (r, t')) : t'.frozen = t.frozen := by
  rw [arena.monad.intern_persistent_e, arena.store.PersTier.intern_e] at h
  obtain ⟨⟨r1, t1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h1f : t1.frozen = t.frozen := pertier_intern_bm_of_view_frozen h1
  rw [← h1f]
  clear h1
  cases r1 with
  | Err e =>
    simp only [Aeneas.Std.uncurry, Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; rfl
  | Ok mi =>
    simp only [Aeneas.Std.uncurry] at h
    obtain ⟨o, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases o with
    | some i =>
      simp only [Aeneas.Std.uncurry, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; rfl
    | none =>
      simp only [Aeneas.Std.uncurry] at h
      obtain ⟨b, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      split at h
      · obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        simp only [Aeneas.Std.uncurry, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h; rfl
      · obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨⟨_, _⟩, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        simp only [Aeneas.Std.uncurry, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h; rfl

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

/-- A reader's `LSR`, its relation strengthened by a fact about the Rust
answer alone. -/
theorem LSR.withWF {α β : Type} {R : α → β → Prop} {P : α → Prop}
    {pers : arena.store.PersTier}
    {m : Result (core.result.Result α kernel.core_types.CheckError)}
    {st : arena.monad.AState} {lst : AState} {x : AM β}
    (h : LSR pers R m st lst x) (hP : ∀ a, m = ok (.Ok a) → P a) :
    LSR pers (fun a b => R a b ∧ P a) m st lst x := by
  intro o hm
  have := h o hm
  cases o with
  | Err e => exact this
  | Ok a =>
    obtain ⟨b, lst', hx, hR, h1, h2⟩ := this
    exact ⟨b, lst', hx, ⟨hR, hP a hm⟩, h1, h2⟩

/-- A reader's `LSR`, its relation weakened. -/
theorem LSR.mono {α β : Type} {R R' : α → β → Prop}
    {pers : arena.store.PersTier}
    {m : Result (core.result.Result α kernel.core_types.CheckError)}
    {st : arena.monad.AState} {lst : AState} {x : AM β}
    (h : LSR pers R m st lst x) (hR : ∀ a b, R a b → R' a b) :
    LSR pers R' m st lst x := by
  intro o hm
  have := h o hm
  cases o with
  | Err e => exact this
  | Ok a =>
    obtain ⟨b, lst', hx, hr, h1, h2⟩ := this
    exact ⟨b, lst', hx, hR a b hr, h1, h2⟩

/-- The promotion tier's statement shape from the judgement. -/
theorem LS.toSimPM {α β : Type} {R : α → β → Prop} {pers : arena.store.PersTier}
    {m : Result (core.result.Result (arena.promote.PMemo × α) kernel.core_types.CheckError ×
      arena.monad.AState)}
    {lst : AState} {x : AM (PMemo × β)} {o}
    (h : LS pers (fun r v => PMemoRel r.1 v.1 ∧ R r.2 v.2) m lst x) (hm : m = ok o) :
    SimPM R pers lst o x := by
  obtain ⟨o, st'⟩ := o
  have := h o st' hm
  show POut R pers lst o st' (x.run lst)
  cases o with
  | Err e => exact this
  | Ok a =>
    obtain ⟨⟨m', v⟩, lst', hx, ⟨hM, hR⟩, h1, h2⟩ := this
    exact ⟨m', v, lst', hx, hR, hM, h1, h2⟩

/-! ## The name, level and level-list views -/

@[lockstep] theorem view_n_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.NIdx) :
    LSR pers (fun a b => b = absNNodeView a ∧ NNodeViewWF a) (arena.monad.view_n pers st h)
      st lst (Arena.viewN (absNIdx h)) := by
  refine LSR.withWF (LSR.ofAOut₀ fun _ hr => view_n_run₀ hrel hinv hr) ?_
  intro a ha
  rw [arena.monad.view_n] at ha
  obtain ⟨n, hn, ha⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha
  rw [arena.store.EStore.ns] at hn
  obtain rfl : n = st.store.lss.ls.ns := (Result.ok_injective hn).symm
  obtain ⟨v, hv, ha⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha
  have hwf := nstore_view_wf hinv.store.lss.lvl.ns hv
  cases v with
  | none =>
    obtain ⟨_, -, ha⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha
    obtain ⟨_, -, ha⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha
    cases fail_run ha
  | some w =>
    cases Result.ok_injective ha
    exact hwf _ rfl

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

/-- `view` with the Rust view's key predicate.  Filed AFTER `view_ls`, so a
proof that needs the predicate takes this one as a local hypothesis (local
candidates are tried first). -/
theorem view_wf_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSR pers (fun a b => b = absENodeView a ∧ ENodeViewWF a) (arena.monad.view pers st h)
      st lst (Arena.view (absEIdx h)) := by
  refine LSR.mono (LSR.withWF (view_ls hrel hinv h) ?_) (fun _ _ h => ⟨h.1.2, h.2⟩)
  intro a ha
  rw [arena.monad.view] at ha
  obtain ⟨q, hq, ha⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha
  have hwf := estore_view_wf hinv.store hq
  cases q with
  | none =>
    obtain ⟨_, -, ha⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha
    obtain ⟨_, -, ha⟩ := ConRon.Refine.bind_eq_ok_iff.mp ha
    cases fail_run ha
  | some w =>
    cases Result.ok_injective ha
    exact hwf _ rfl

attribute [lockstep_simp] absNNodeView absLNodeView absLsNodeView absLIdxL absNIdxL absEIdxL

/-! ## The reads and the four persistent interns of a promotion

Stated at the glued state, the reader a stand-in `P` (not `frozen`): the
views read what the frozen state reads through its tier (`view_*_glue`), and
a promote-intern grows the tier and keeps it frozen, so the relation after it
is the glued state's at the grown tier (`LST`, the tier in the answer). -/

@[lockstep] theorem view_n_glue_ls {P t st lst} (hP : P.frozen = false)
    (hrel : AStateRel₀ P (glue t st) lst) (hinv : AStateInv P (glue t st))
    (h : arena.handle.NIdx) :
    LSR P (fun a b => b = absNNodeView a ∧ NNodeViewWF a) (arena.monad.view_n t st h)
      (glue t st) lst (Arena.viewN (absNIdx h)) := by
  rw [view_n_glue hP]; exact view_n_ls hrel hinv h

@[lockstep] theorem view_l_glue_ls {P t st lst} (hP : P.frozen = false)
    (hrel : AStateRel₀ P (glue t st) lst) (hinv : AStateInv P (glue t st))
    (h : arena.handle.LIdx) :
    LSR P (fun a b => b = absLNodeView a) (arena.monad.view_l t st h)
      (glue t st) lst (Arena.viewL (absLIdx h)) := by
  rw [view_l_glue hP]; exact view_l_ls hrel hinv h

@[lockstep] theorem view_ls_glue_ls {P t st lst} (hP : P.frozen = false)
    (hrel : AStateRel₀ P (glue t st) lst) (hinv : AStateInv P (glue t st))
    (h : arena.handle.LsIdx) :
    LSR P (fun a b => b = absLsNodeView a) (arena.monad.view_ls t st h)
      (glue t st) lst (Arena.viewLs (absLsIdx h)) := by
  rw [view_ls_glue hP]; exact view_lsv_ls hrel hinv h

@[lockstep] theorem view_glue_ls {P t st lst} (hP : P.frozen = false)
    (hrel : AStateRel₀ P (glue t st) lst) (hinv : AStateInv P (glue t st))
    (h : arena.handle.EIdx) :
    LSR P (fun a b => b = absENodeView a ∧ ENodeViewWF a) (arena.monad.view t st h)
      (glue t st) lst (Arena.view (absEIdx h)) := by
  rw [view_glue hP]; exact view_wf_ls hrel hinv h

/-- One promote-intern, from its `run₀` at the frozen state and its tier. -/
private theorem pint_lst {α β : Type} {A : α → β} {P t : arena.store.PersTier}
    {st : arena.monad.AState} {lst : AState} {x : AM β}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.store.PersTier)}
    (hP : P.frozen = false) (ht : t.frozen = true) (hsc : ScratchOn st.store)
    (hfr : ∀ r t', m = ok (r, t') → t'.frozen = t.frozen)
    (hrun : ∀ r t', m = ok (r, t') → AOut₀ A t' r st (x.run lst)) :
    LST P (fun p b => b = A p.1 ∧ p.2.frozen = true) (fun t' => glue t' st) m lst x := by
  intro o st' hm
  obtain ⟨⟨r, t'⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have hf : t'.frozen = true := (hfr r t' h1).trans ht
  have h := hrun r t' h1
  have h2' := Result.ok_injective h2
  cases r with
  | Err e =>
    simp only [packTOut, Prod.mk.injEq] at h2'
    obtain ⟨rfl, rfl⟩ := h2'
    exact h
  | Ok a =>
    simp only [packTOut, Prod.mk.injEq] at h2'
    obtain ⟨rfl, rfl⟩ := h2'
    obtain ⟨lst', hx, h3, h4⟩ := h
    exact ⟨A a, lst', hx, ⟨rfl, hf⟩, (glue_rel hP).mpr h3, (glue_inv hP hsc).mpr h4⟩

@[lockstep] theorem intern_persistent_e_lst {P t st lst} (hP : P.frozen = false)
    (ht : t.frozen = true) (hsc : ScratchOn st.store)
    (hrel : AStateRel₀ P (glue t st) lst) (hinv : AStateInv P (glue t st))
    (v : arena.store.ENodeView) (hvwf : ENodeViewWF v) :
    LST P (fun p b => b = absEIdx p.1 ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.monad.intern_persistent_e t st v) lst
      (Arena.internPersistentE (absENodeView v)) :=
  pint_lst hP ht hsc (fun _ _ h => intern_persistent_e_frozen h)
    (fun _ _ h => intern_persistent_e_run₀ ((glue_rel hP).mp hrel)
      ((glue_inv hP hsc).mp hinv) ht v hvwf h)

@[lockstep] theorem intern_persistent_n_lst {P t st lst} (hP : P.frozen = false)
    (ht : t.frozen = true) (hsc : ScratchOn st.store)
    (hrel : AStateRel₀ P (glue t st) lst) (hinv : AStateInv P (glue t st))
    (v : arena.store.NNodeView) (hvwf : NNodeViewWF v) :
    LST P (fun p b => b = absNIdx p.1 ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.monad.intern_persistent_n t st v) lst
      (Arena.internPersistentN (absNNodeView v)) :=
  pint_lst hP ht hsc (fun _ _ h => intern_persistent_n_frozen h)
    (fun _ _ h => intern_persistent_n_run₀ ((glue_rel hP).mp hrel)
      ((glue_inv hP hsc).mp hinv) ht v hvwf h)

@[lockstep] theorem intern_persistent_l_lst {P t st lst} (hP : P.frozen = false)
    (ht : t.frozen = true) (hsc : ScratchOn st.store)
    (hrel : AStateRel₀ P (glue t st) lst) (hinv : AStateInv P (glue t st))
    (v : arena.store.LNodeView) :
    LST P (fun p b => b = absLIdx p.1 ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.monad.intern_persistent_l t st v) lst
      (Arena.internPersistentL (absLNodeView v)) :=
  pint_lst hP ht hsc (fun _ _ h => intern_persistent_l_frozen h)
    (fun _ _ h => intern_persistent_l_run₀ ((glue_rel hP).mp hrel)
      ((glue_inv hP hsc).mp hinv) ht v h)

@[lockstep] theorem intern_persistent_ls_lst {P t st lst} (hP : P.frozen = false)
    (ht : t.frozen = true) (hsc : ScratchOn st.store)
    (hrel : AStateRel₀ P (glue t st) lst) (hinv : AStateInv P (glue t st))
    (v : alloc.vec.Vec arena.handle.LIdx) :
    LST P (fun p b => b = absLsIdx p.1 ∧ p.2.frozen = true) (fun t' => glue t' st)
      (arena.monad.intern_persistent_ls t st v) lst
      (Arena.internPersistentLs (absLsNodeView v)) :=
  pint_lst hP ht hsc (fun _ _ h => intern_persistent_ls_frozen h)
    (fun _ _ h => intern_persistent_ls_run₀ ((glue_rel hP).mp hrel)
      ((glue_inv hP hsc).mp hinv) ht v h)

/-! ## Tier bits and `dup2` at the small handle kinds -/

@[lockstep] theorem eidx_is_persistent_spec (h : arena.handle.EIdx) :
    LSP (arena.handle.EIdx.is_persistent h) (fun b => (absEIdx h).isPersistent = b) :=
  fun _ hb => eidx_is_persistent_abs hb

@[lockstep] theorem nidx_is_persistent_spec (h : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.is_persistent h) (fun b => (absNIdx h).isPersistent = b) :=
  fun _ hb => nidx_is_persistent_abs hb

@[lockstep] theorem lidx_is_persistent_spec (h : arena.handle.LIdx) :
    LSP (arena.handle.LIdx.is_persistent h) (fun b => (absLIdx h).isPersistent = b) :=
  fun _ hb => lidx_is_persistent_abs hb

@[lockstep] theorem lsidx_is_persistent_spec (h : arena.handle.LsIdx) :
    LSP (arena.handle.LsIdx.is_persistent h) (fun b => (absLsIdx h).isPersistent = b) :=
  fun _ hb => lsidx_is_persistent_abs hb

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
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨pw, hpw, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← Result.ok_injective h, dupId_nidx _ _ hn, ConRon.Refine.PropWhen.dup_eq hpw]

@[lockstep] theorem basis_kind_dup_spec (k : kernel.env.BasisKind) :
    LSP (kernel.env.basis_kind_dup k) (fun r => r = k) := by
  intro r h
  cases k <;> simp only [kernel.env.basis_kind_dup, Result.ok.injEq] at h <;> exact h.symm

@[lockstep] theorem quot_kind_dup_spec (k : kernel.env.QuotKind) :
    LSP (kernel.env.quot_kind_dup k) (fun r => r = k) := by
  intro r h
  cases k <;> simp only [kernel.env.quot_kind_dup, Result.ok.injEq] at h <;> exact h.symm

end Lockstep

end ConRon.Refine2

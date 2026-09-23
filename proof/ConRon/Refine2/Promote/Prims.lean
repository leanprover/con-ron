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
  refine LSR.withWF (view_ls hrel hinv h) ?_
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

/-! ## The four persistent interns -/

@[lockstep] theorem intern_persistent_e_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (v : arena.store.ENodeView) (hvwf : ENodeViewWF v) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_persistent_e pers st v) lst
      (Arena.internPersistentE (absENodeView v)) :=
  LS.ofSim₀ fun _ h => intern_persistent_e_run₀ hrel hinv v hvwf h

@[lockstep] theorem intern_persistent_n_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (v : arena.store.NNodeView) (hvwf : NNodeViewWF v) :
    LS pers (fun a b => b = absNIdx a) (arena.monad.intern_persistent_n pers st v) lst
      (Arena.internPersistentN (absNNodeView v)) :=
  LS.ofSim₀ fun _ h => intern_persistent_n_run₀ hrel hinv v hvwf h

@[lockstep] theorem intern_persistent_l_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (v : arena.store.LNodeView) :
    LS pers (fun a b => b = absLIdx a) (arena.monad.intern_persistent_l pers st v) lst
      (Arena.internPersistentL (absLNodeView v)) :=
  LS.ofSim₀ fun _ h => intern_persistent_l_run₀ hrel hinv v h

@[lockstep] theorem intern_persistent_ls_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (v : alloc.vec.Vec arena.handle.LIdx) :
    LS pers (fun a b => b = absLsIdx a) (arena.monad.intern_persistent_ls pers st v) lst
      (Arena.internPersistentLs (absLsNodeView v)) :=
  LS.ofSim₀ fun _ h => intern_persistent_ls_run₀ hrel hinv v h

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

@[lockstep] theorem dup2_nidx (h : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun e he => dupId_nidx _ _ he

@[lockstep] theorem dup2_lidx (h : arena.handle.LIdx) :
    LSP (arena.handle.LIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun e he => dupId_lidx _ _ he

@[lockstep] theorem dup2_lsidx (h : arena.handle.LsIdx) :
    LSP (arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun e he => dupId_lsidx _ _ he

end Lockstep

end ConRon.Refine2

/-
# `ConRon.Refine2.Frontend.Olean.Shape` — the shape of the reader's lemmas

**Task #142, Theorem 2.**  A reader function takes the bare store and answers `RdErr`
where the twin's answers `AM (Option β)`, so that the three outcomes pair up:

| the Rust returns | the twin's run |
|---|---|
| `Ok a` | `some b`, `R a b`, in a related state |
| `Err Bad` | `none`, in a related state |
| `Err (Err e)` | throws, at the same kind (`AErrSim`) |

That is `RS`, with the relation between the states a premise of the judgement, so
that a bind threads it and a lemma states none.  `CS` is the same at a function whose
error channel is `CheckError` and whose twin answers `AM β`.  `RdP` is the pure form,
for a read of the memo: no state on either side.

`Rel` carries what the state relation asks of a reader's value: nothing about the
twin's store.  The relation's post-state is `withStore st s'`: the reader does not
touch the rest of `AState`.
-/
import ConRon.Refine2.Frontend.Olean.Region
import ConRon.Refine2.Frontend.Top
import ConRon.Arena.Frontend.Olean.Records

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena

/-! ## The pins and the answers -/

/-- `spec::OleanPins`, as the twin's. -/
def absPins (pk : frontend.olean.spec.OleanPins) : Arena.Frontend.Olean.OleanPins where
  anon := absNIdx pk.anon
  zero := absLIdx pk.zero
  nil := absLsIdx pk.nil
  nNat := absNIdx pk.n_nat
  nCharOfNat := absNIdx pk.n_char_of_nat
  nStringOfList := absNIdx pk.n_string_of_list
  nEq := absNIdx pk.n_eq
  nQuot := absNIdx pk.n_quot
  nQuotMk := absNIdx pk.n_quot_mk
  nQuotLift := absNIdx pk.n_quot_lift
  nQuotInd := absNIdx pk.n_quot_ind

/-- The answer relation of a value with an abstraction. -/
@[reducible] def EqA {α β : Type} (A : α → β) : α → β → Prop := fun a b => b = A a

/-! ## `RS`: a store-threading read -/

/-- What a Rust read's outcome claims of a twin run. -/
def RdOut {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop)
    (st' : arena.monad.AState) (o : core.result.Result α frontend.olean.spec.RdErr)
    (y : Except Arena.CheckError (Option β × AState)) : Prop :=
  match o with
  | .Ok a => ∃ b lst', y = .ok (some b, lst') ∧ R a b ∧ AStateRel₀ pers st' lst' ∧ AStateInv pers st'
  | .Err .Bad => ∃ lst', y = .ok (none, lst') ∧ AStateRel₀ pers st' lst' ∧ AStateInv pers st'
  | .Err (.Err e) => AErrSim e y

/-- **The lockstep judgement of a read**: from related states, the Rust read `m`, over
the store `st.store`, and the twin's `x`. -/
def RS {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop)
    (st : arena.monad.AState) (lst : AState)
    (m : Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore))
    (x : AM (Option β)) : Prop :=
  AStateRel₀ pers st lst → AStateInv pers st →
    ∀ o s', m = ok (o, s') → RdOut pers R (withStore st s') o (x.run lst)

theorem withStore_self (st : arena.monad.AState) : withStore st st.store = st := rfl

theorem am_run_pure {α : Type} (a : α) (lst : AState) :
    (pure a : AM α).run lst = .ok (a, lst) := rfl

theorem am_bind_ok {β δ : Type} {x : AM β} {g : β → AM δ} {lst lst' : AState} {b : β}
    (hx : x.run lst = .ok (b, lst')) : (x >>= g).run lst = (g b).run lst' := by
  rw [StateT.run_bind, hx]; rfl

/-- A leaf: the value, and no store change. -/
theorem RS.some {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {a : α} {b : β} (hR : R a b) :
    RS pers R st lst (ok (.Ok a, st.store)) (pure (some b)) := by
  intro hrel hinv o s' h
  cases Result.ok_injective h
  exact ⟨b, lst, rfl, hR, hrel, hinv⟩

/-- A leaf: upstream's `none`. -/
theorem RS.none {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} :
    RS pers R st lst (ok (.Err .Bad, st.store)) (pure Option.none : AM (Option β)) := by
  intro hrel hinv o s' h
  cases Result.ok_injective h
  exact ⟨lst, rfl, hrel, hinv⟩

/-- A step of the Rust alone: a pure read, whose answer the twin's pure expression
takes from the equation. -/
theorem RS.pure_step {α β γ : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {f : Result γ}
    {k : γ → Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore)}
    {x : AM (Option β)} (h : ∀ a, f = ok a → RS pers R st lst (k a) x) :
    RS pers R st lst (Std.bind f k) x := by
  intro hrel hinv o s' hm
  obtain ⟨a, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact h a h1 hrel hinv o s' h2

/-- `ok v` on the Rust side. -/
theorem RS.ok_bind {α β γ : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {v : γ}
    {k : γ → Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore)}
    {x : AM (Option β)} (h : RS pers R st lst (k v) x) :
    RS pers R st lst (Std.bind (ok v) k) x := by
  rw [bind_ok]; exact h

/-- **The bind of two reads**: the first's `Ok` feeds the second, its failures are the
answer, and the twin's `match ← x with | none => pure none | some b => g b`. -/
theorem RS.bind {α₁ β₁ α β : Type} {pers : arena.store.PersTier} {R₁ : α₁ → β₁ → Prop}
    {R : α → β → Prop} {st : arena.monad.AState} {lst : AState}
    {f : Result (core.result.Result α₁ frontend.olean.spec.RdErr × arena.store.EStore)}
    {k : core.result.Result α₁ frontend.olean.spec.RdErr × arena.store.EStore →
      Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore)}
    {x : AM (Option β₁)} {g : β₁ → AM (Option β)}
    (hf : RS pers R₁ st lst f x)
    (he : ∀ e s1, k (.Err e, s1) = ok (.Err e, s1))
    (hk : ∀ a b s1 lst1, R₁ a b → RS pers R (withStore st s1) lst1 (k (.Ok a, s1)) (g b)) :
    RS pers R st lst (Std.bind f k)
      (do match ← x with
          | Option.none => pure Option.none
          | Option.some b => g b) := by
  intro hrel hinv o s' hm
  obtain ⟨⟨r, s1⟩, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have h1 := hf hrel hinv r s1 hf1
  cases r with
  | Ok a =>
    obtain ⟨b, lst1, hx, hR, hrel1, hinv1⟩ := h1
    rw [am_bind_ok hx]
    exact hk a b s1 lst1 hR hrel1 hinv1 o s' hk1
  | Err e =>
    rw [he e s1] at hk1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hk1)
    cases e with
    | Bad =>
      obtain ⟨lst1, hx, hrel1, hinv1⟩ := h1
      rw [am_bind_ok hx]
      exact ⟨lst1, rfl, hrel1, hinv1⟩
    | Err e =>
      intro k' hk'
      obtain ⟨le, hle, hkk⟩ := h1 k' hk'
      refine ⟨le, ?_, hkk⟩
      rw [StateT.run_bind, hle]; rfl

/-- The tail of a read: the twin's run moved along an equation. -/
theorem RS.of_eq {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState}
    {m : Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore)}
    {x y : AM (Option β)} (h : RS pers R st lst m x) (hxy : y = x) : RS pers R st lst m y := by
  rw [hxy]; exact h

/-- A weaker answer relation. -/
theorem RS.mono {α β : Type} {pers : arena.store.PersTier} {R R' : α → β → Prop}
    {st : arena.monad.AState} {lst : AState}
    {m : Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore)}
    {x : AM (Option β)} (h : RS pers R st lst m x) (hR : ∀ a b, R a b → R' a b) :
    RS pers R' st lst m x := by
  intro hrel hinv o s' hm
  have h1 := h hrel hinv o s' hm
  cases o with
  | Ok a =>
    obtain ⟨b, lst1, hx, hr, h2, h3⟩ := h1
    exact ⟨b, lst1, hx, hR _ _ hr, h2, h3⟩
  | Err e =>
    cases e with
    | Bad => exact h1
    | Err e => exact h1

/-- A Rust `if`, against the twin's `if` on the same test, split by the caller. -/
theorem RS.pure_none_of {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {m} (h : m = ok ((.Err .Bad : core.result.Result α frontend.olean.spec.RdErr), st.store)) :
    RS pers R st lst m (pure Option.none : AM (Option β)) := by
  rw [h]; exact RS.none

/-! ## `RdP`: a pure read -/

/-- A read of the memo: no state on either side, and only `Bad` for a failure. -/
def RdP {α β : Type} (R : α → β → Prop) (o : core.result.Result α frontend.olean.spec.RdErr)
    (y : Option β) : Prop :=
  match o with
  | .Ok a => ∃ b, y = some b ∧ R a b
  | .Err .Bad => y = Option.none
  | .Err (.Err _) => False

/-! ## `CS`: a function whose error channel is `CheckError` -/

/-- **The lockstep judgement of a function over the store with `CheckError`.** -/
def CS {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop)
    (st : arena.monad.AState) (lst : AState)
    (m : Result (core.result.Result α kernel.core_types.CheckError × arena.store.EStore))
    (x : AM β) : Prop :=
  AStateRel₀ pers st lst → AStateInv pers st →
    ∀ o s', m = ok (o, s') →
      match o with
      | .Ok a => ∃ b lst', x.run lst = .ok (b, lst') ∧ R a b ∧
          AStateRel₀ pers (withStore st s') lst' ∧ AStateInv pers (withStore st s')
      | .Err e => AErrSim e (x.run lst)

/-- The Rust `Ok` with no store change against the twin's `pure`. -/
theorem CS.pure {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {a : α} {b : β} (hR : R a b) :
    CS pers R st lst (ok (.Ok a, st.store)) (Pure.pure b) := by
  intro hrel hinv o s' h
  cases Result.ok_injective h
  exact ⟨b, lst, rfl, hR, hrel, hinv⟩

theorem CS.pure_step {α β γ : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {f : Result γ}
    {k : γ → Result (core.result.Result α kernel.core_types.CheckError × arena.store.EStore)}
    {x : AM β} (h : ∀ a, f = ok a → CS pers R st lst (k a) x) :
    CS pers R st lst (Std.bind f k) x := by
  intro hrel hinv o s' hm
  obtain ⟨a, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact h a h1 hrel hinv o s' h2

/-- The bind of two `CS`s. -/
theorem CS.bind {α₁ β₁ α β : Type} {pers : arena.store.PersTier} {R₁ : α₁ → β₁ → Prop}
    {R : α → β → Prop} {st : arena.monad.AState} {lst : AState}
    {f : Result (core.result.Result α₁ kernel.core_types.CheckError × arena.store.EStore)}
    {k : core.result.Result α₁ kernel.core_types.CheckError × arena.store.EStore →
      Result (core.result.Result α kernel.core_types.CheckError × arena.store.EStore)}
    {x : AM β₁} {g : β₁ → AM β}
    (hf : CS pers R₁ st lst f x)
    (he : ∀ e s1, k (.Err e, s1) = ok (.Err e, s1))
    (hk : ∀ a b s1 lst1, R₁ a b → CS pers R (withStore st s1) lst1 (k (.Ok a, s1)) (g b)) :
    CS pers R st lst (Std.bind f k) (x >>= g) := by
  intro hrel hinv o s' hm
  obtain ⟨⟨r, s1⟩, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have h1 := hf hrel hinv r s1 hf1
  cases r with
  | Ok a =>
    obtain ⟨b, lst1, hx, hR, hrel1, hinv1⟩ := h1
    rw [am_bind_ok hx]
    exact hk a b s1 lst1 hR hrel1 hinv1 o s' hk1
  | Err e =>
    rw [he e s1] at hk1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hk1)
    show AErrSim e _
    rw [StateT.run_bind]
    exact AErrSim.bind h1 _

/-! ## The interns -/

/-- `intern_name`, in the reader's channel. -/
theorem RS.intern_name {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {v : arena.store.NNodeView} (hv : NNodeViewWF v) :
    RS pers (EqA absNIdx) st lst
      (do
        let (r1, ar1) ← arena.store.EStore.intern_name st.store pers v
        let r2 ← frontend.olean.spec.rd_of r1
        ok (r2, ar1))
      (do pure (Option.some (← internNNode (absNNodeView v)))) := by
  intro hrel hinv o s' h
  obtain ⟨⟨r1, ar1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨r2, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
  have hS := intern_n_node_run₀ hrel hinv v hv (o := (r1, withStore st ar1))
    (by rw [arena.monad.intern_n_node, h1]; simp only [bind_ok]; rfl)
  cases r1 with
  | Ok a =>
    cases Result.ok_injective (show ok (.Ok a) = ok r2 from h2)
    obtain ⟨lst1, hx, hrel1, hinv1⟩ := Sim₀.apply hS
    rw [am_bind_ok hx]
    exact ⟨_, lst1, rfl, rfl, hrel1, hinv1⟩
  | Err e =>
    cases Result.ok_injective (show ok (.Err (.Err e)) = ok r2 from h2)
    have := Sim₀.apply_err hS
    show AErrSim e _
    rw [StateT.run_bind]
    exact AErrSim.bind this _

/-- `intern_level`, in the reader's channel. -/
theorem RS.intern_level {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {v : arena.store.LNodeView} :
    RS pers (EqA absLIdx) st lst
      (do
        let (r1, ar1) ← arena.store.EStore.intern_level st.store pers v
        let r2 ← frontend.olean.spec.rd_of r1
        ok (r2, ar1))
      (do pure (Option.some (← internLNode (absLNodeView v)))) := by
  intro hrel hinv o s' h
  obtain ⟨⟨r1, ar1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨r2, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
  have hS := intern_l_node_run₀ hrel hinv v (o := (r1, withStore st ar1))
    (by rw [arena.monad.intern_l_node, h1]; simp only [bind_ok]; rfl)
  cases r1 with
  | Ok a =>
    cases Result.ok_injective (show ok (.Ok a) = ok r2 from h2)
    obtain ⟨lst1, hx, hrel1, hinv1⟩ := Sim₀.apply hS
    rw [am_bind_ok hx]
    exact ⟨_, lst1, rfl, rfl, hrel1, hinv1⟩
  | Err e =>
    cases Result.ok_injective (show ok (.Err (.Err e)) = ok r2 from h2)
    have := Sim₀.apply_err hS
    show AErrSim e _
    rw [StateT.run_bind]
    exact AErrSim.bind this _

/-- `intern_levels`, in the reader's channel. -/
theorem RS.intern_levels {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {v : alloc.vec.Vec arena.handle.LIdx} :
    RS pers (EqA absLsIdx) st lst
      (do
        let (r1, ar1) ← arena.store.EStore.intern_levels st.store pers v
        let r2 ← frontend.olean.spec.rd_of r1
        ok (r2, ar1))
      (do pure (Option.some (← internLsNode (absLsNodeView v)))) := by
  intro hrel hinv o s' h
  obtain ⟨⟨r1, ar1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨r2, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
  have hS := intern_ls_node_run₀ hrel hinv v (o := (r1, withStore st ar1))
    (by rw [arena.monad.intern_ls_node, h1]; simp only [bind_ok]; rfl)
  cases r1 with
  | Ok a =>
    cases Result.ok_injective (show ok (.Ok a) = ok r2 from h2)
    obtain ⟨lst1, hx, hrel1, hinv1⟩ := Sim₀.apply hS
    rw [am_bind_ok hx]
    exact ⟨_, lst1, rfl, rfl, hrel1, hinv1⟩
  | Err e =>
    cases Result.ok_injective (show ok (.Err (.Err e)) = ok r2 from h2)
    have := Sim₀.apply_err hS
    show AErrSim e _
    rw [StateT.run_bind]
    exact AErrSim.bind this _

/-- `intern`, in the reader's channel. -/
theorem RS.intern {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {v : arena.store.ENodeView} (hlit : ∀ l, v = .Lit l → ConRon.Refine.LiteralWF l) :
    RS pers (EqA absEIdx) st lst
      (do
        let (r1, ar1) ← arena.store.EStore.intern st.store pers v
        let r2 ← frontend.olean.spec.rd_of r1
        ok (r2, ar1))
      (do pure (Option.some (← internE (absENodeView v)))) := by
  intro hrel hinv o s' h
  obtain ⟨⟨r1, ar1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨r2, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
  have hS := intern_e_run₀ hrel hinv v hlit (o := (r1, withStore st ar1))
    (by rw [arena.monad.intern_e, h1]; simp only [bind_ok]; rfl)
  cases r1 with
  | Ok a =>
    cases Result.ok_injective (show ok (.Ok a) = ok r2 from h2)
    obtain ⟨lst1, hx, hrel1, hinv1⟩ := Sim₀.apply hS
    rw [am_bind_ok hx]
    exact ⟨_, lst1, rfl, rfl, hrel1, hinv1⟩
  | Err e =>
    cases Result.ok_injective (show ok (.Err (.Err e)) = ok r2 from h2)
    have := Sim₀.apply_err hS
    show AErrSim e _
    rw [StateT.run_bind]
    exact AErrSim.bind this _

/-! ## The handles -/

theorem nidx_dup2_ok {h x : arena.handle.NIdx}
    (e : arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h = ok x) : x = h :=
  (Result.ok_injective (show ok h = ok x from e)).symm

theorem lidx_dup2_ok {h x : arena.handle.LIdx}
    (e : arena.handle.LIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h = ok x) : x = h :=
  (Result.ok_injective (show ok h = ok x from e)).symm

theorem lsidx_dup2_ok {h x : arena.handle.LsIdx}
    (e : arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h = ok x) : x = h :=
  (Result.ok_injective (show ok h = ok x from e)).symm

theorem eidx_dup2_ok {h x : arena.handle.EIdx}
    (e : arena.handle.EIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h = ok x) : x = h :=
  (Result.ok_injective (show ok h = ok x from e)).symm

end ConRon.Refine2.Frontend.Olean

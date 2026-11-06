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
import ConRon.Refine2.Frontend.Types
import ConRon.Refine2.Frontend.Scan.WF
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

/-! ## Fields and scalars -/

theorem fld_0 {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g x : Std.U64}
    (h : frontend.olean.region.region_fld bs g 0#u64 = ok x) : (absRegion bs r).fld g.val 0 = absWord x :=
  (region_fld_eq bs h).symm

theorem fld_1 {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g x : Std.U64}
    (h : frontend.olean.region.region_fld bs g 1#u64 = ok x) : (absRegion bs r).fld g.val 1 = absWord x :=
  (region_fld_eq bs h).symm

theorem fld_2 {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g x : Std.U64}
    (h : frontend.olean.region.region_fld bs g 2#u64 = ok x) : (absRegion bs r).fld g.val 2 = absWord x :=
  (region_fld_eq bs h).symm

theorem fld_3 {bs : Slice Std.U8} {r : frontend.olean.region.Region} {g x : Std.U64}
    (h : frontend.olean.region.region_fld bs g 3#u64 = ok x) : (absRegion bs r).fld g.val 3 = absWord x :=
  (region_fld_eq bs h).symm

theorem word_eq_one {v : Std.U64} : (absWord v == 1) = true ↔ v = 1#u64 := by
  rw [beq_iff_eq]
  constructor
  · intro he
    have := congrArg UInt64.toNat he
    rw [absWord_toNat] at this
    exact UScalar.eq_of_val_eq (by rw [this]; rfl)
  · intro he; rw [he]; rfl

/-! ## Binds with the twin's continuation left whole

`RS.bind` spells the twin's `match`; a `match` the twin wrote elsewhere is another
matcher, which does not unify with a metavariable in its arms.  Here the continuation
is one function, and what it does at `none` is a premise. -/

/-- **The bind of two reads**, the twin's continuation left whole. -/
theorem RS.bind_of {α₁ β₁ α β : Type} {pers : arena.store.PersTier} {R₁ : α₁ → β₁ → Prop}
    {R : α → β → Prop} {st : arena.monad.AState} {lst : AState}
    {f : Result (core.result.Result α₁ frontend.olean.spec.RdErr × arena.store.EStore)}
    {k : core.result.Result α₁ frontend.olean.spec.RdErr × arena.store.EStore →
      Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore)}
    {x : AM (Option β₁)} {h : Option β₁ → AM (Option β)}
    (hf : RS pers R₁ st lst f x)
    (he : ∀ e s1, k (.Err e, s1) = ok (.Err e, s1))
    (h0 : h Option.none = pure Option.none)
    (hk : ∀ a b s1 lst1, R₁ a b →
      RS pers R (withStore st s1) lst1 (k (.Ok a, s1)) (h (Option.some b))) :
    RS pers R st lst (Std.bind f k) (x >>= h) := by
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
      rw [am_bind_ok hx, h0]
      exact ⟨lst1, rfl, hrel1, hinv1⟩
    | Err e =>
      intro k' hk'
      obtain ⟨le, hle, hkk⟩ := h1 k' hk'
      refine ⟨le, ?_, hkk⟩
      rw [StateT.run_bind, hle]; rfl

/-- `x >>= g` at `OptionT AM`, as `AM`'s bind. -/
theorem optionT_bind_eq {β₁ β : Type} (x : OptionT AM β₁) (g : β₁ → OptionT AM β) :
    (x >>= g) = ((show AM (Option β₁) from x) >>=
      fun o => match o with
        | Option.some a => (show AM (Option β) from g a)
        | Option.none => pure Option.none : AM (Option β)) := rfl

/-- **The bind of two reads**, the twin's at `OptionT AM`. -/
theorem RS.bindT {α₁ β₁ α β : Type} {pers : arena.store.PersTier} {R₁ : α₁ → β₁ → Prop}
    {R : α → β → Prop} {st : arena.monad.AState} {lst : AState}
    {f : Result (core.result.Result α₁ frontend.olean.spec.RdErr × arena.store.EStore)}
    {k : core.result.Result α₁ frontend.olean.spec.RdErr × arena.store.EStore →
      Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore)}
    {x : OptionT AM β₁} {g : β₁ → OptionT AM β}
    (hf : RS pers R₁ st lst f x)
    (he : ∀ e s1, k (.Err e, s1) = ok (.Err e, s1))
    (hk : ∀ a b s1 lst1, R₁ a b → RS pers R (withStore st s1) lst1 (k (.Ok a, s1)) (g b)) :
    RS pers R st lst (Std.bind f k) (x >>= g : OptionT AM β) := by
  rw [optionT_bind_eq]
  exact RS.bind_of hf he rfl hk

/-- A read, then the twin's `pure` of a function of its answer. -/
theorem RS.map_pure {α β γ : Type} {pers : arena.store.PersTier} {R₁ : α → β → Prop}
    {R : α → γ → Prop} {st : arena.monad.AState} {lst : AState}
    {m : Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore)}
    {x : OptionT AM β} {f : β → γ} (hx : RS pers R₁ st lst m x) (hR : ∀ a b, R₁ a b → R a (f b)) :
    RS pers R st lst m (x >>= fun b => pure (f b) : OptionT AM γ) := by
  rw [optionT_bind_eq]
  intro hrel hinv o s' hm
  have h1 := hx hrel hinv o s' hm
  cases o with
  | Ok a =>
    obtain ⟨b, lst1, hr, hR1, h2, h3⟩ := h1
    rw [am_bind_ok hr]
    exact ⟨f b, lst1, rfl, hR _ _ hR1, h2, h3⟩
  | Err e =>
    cases e with
    | Bad =>
      obtain ⟨lst1, hr, h2, h3⟩ := h1
      rw [am_bind_ok hr]
      exact ⟨lst1, rfl, h2, h3⟩
    | Err e =>
      intro k' hk'
      obtain ⟨le, hle, hkk⟩ := h1 k' hk'
      refine ⟨le, ?_, hkk⟩
      rw [StateT.run_bind, hle]; rfl

/-! ## An index loop against `List.mapM`

A Rust loop `while i < v.len() { … out.push(a); i += 1 }` that reads through the store,
against the twin's `List.mapM` at `OptionT AM`.  One lemma for every such loop; a loop
states its body once, with the rest of the walk a continuation. -/

/-- **An index loop is `List.mapM`.**  `loop` is the Rust loop with the store, the output
and the index as its arguments; `hdone` is its exit, `hstep` one turn, in which the rest of
the walk is any continuation `K` that the next turn refines. -/
theorem RS.vec_map {ξ ξ' α β : Type} {pers : arena.store.PersTier}
    {S : ξ → ξ' → Prop} {R : α → β → Prop}
    {src : List ξ} {xs : List ξ'} (hxs : List.Forall₂ S src xs) {t : ξ' → OptionT AM β}
    {loop : arena.store.EStore → alloc.vec.Vec α → Std.Usize →
      Result (core.result.Result (alloc.vec.Vec α) frontend.olean.spec.RdErr × arena.store.EStore)}
    (hdone : ∀ ar out i, src.length ≤ i.val → loop ar out i = ok (.Ok out, ar))
    (hstep : ∀ (i : Std.Usize) (out : alloc.vec.Vec α) x x' (K : β → OptionT AM (List β))
      (Rf : alloc.vec.Vec α → List β → Prop) (st : arena.monad.AState) (lst : AState),
      src[i.val]? = Option.some x → S x x' →
      (∀ a b s1 lst1 (out1 : alloc.vec.Vec α) (i1 : Std.Usize), R a b → out1.val = out.val ++ [a] →
        i1.val = i.val + 1 →
        RS pers Rf (withStore st s1) lst1 (loop s1 out1 i1) (K b)) →
      RS pers Rf st lst (loop st.store out i) (t x' >>= K : OptionT AM (List β)))
    {st : arena.monad.AState} {lst : AState} {out : alloc.vec.Vec α} {i : Std.Usize}
    (h0 : out.val = []) (hi : i.val = 0) :
    RS pers (fun v l => List.Forall₂ R v.val l) st lst (loop st.store out i) (xs.mapM t) := by
  have aux : ∀ {src1 : List ξ} {xs1 : List ξ'}, List.Forall₂ S src1 xs1 →
      ∀ (i : Std.Usize) (out : alloc.vec.Vec α) (pre : List β) (st : arena.monad.AState)
        (lst : AState), src.drop i.val = src1 → List.Forall₂ R out.val pre →
        RS pers (fun v l => List.Forall₂ R v.val (pre ++ l)) st lst (loop st.store out i)
          (xs1.mapM t) := by
    intro src1 xs1 hF
    induction hF with
    | nil =>
      intro i out pre st lst hd hpre
      rw [hdone _ _ _ (List.drop_eq_nil_iff.mp hd)]
      exact RS.some (by simpa using hpre)
    | @cons x x' src2 xs2 hS _ ih =>
      intro i out pre st lst hd hpre
      have hlt : i.val < src.length := by
        apply Classical.byContradiction
        intro hn
        rw [List.drop_eq_nil_of_le (by omega)] at hd
        cases hd
      rw [List.drop_eq_getElem_cons hlt] at hd
      obtain ⟨hx, hd2⟩ := List.cons.inj hd
      rw [List.mapM_cons]
      refine hstep i out x x' _ _ st lst (by rw [List.getElem?_eq_getElem hlt, hx]) hS ?_
      intro a b s1 lst1 out1 i1 hR ho hi1
      refine RS.map_pure (R₁ := fun v l => List.Forall₂ R v.val ((pre ++ [b]) ++ l))
        (ih i1 out1 (pre ++ [b]) (withStore st s1) lst1 (by rw [hi1]; exact hd2) ?_) ?_
      · rw [ho]; exact List.rel_append hpre (List.Forall₂.cons hR List.Forall₂.nil)
      · intro v l hv
        simpa using hv
  have := aux hxs i out [] st lst (by rw [hi]; rfl) (by rw [h0]; exact List.Forall₂.nil)
  simpa using this

/-- A list read elementwise by an abstraction. -/
theorem forall₂_eqA {α β : Type} {A : α → β} {l : List α} {l' : List β}
    (h : List.Forall₂ (EqA A) l l') : l.map A = l' := by
  induction h with
  | nil => rfl
  | cons hab _ ih => cases hab; simp [ih]

/-- The other way round. -/
theorem forall₂_of_map {α β : Type} {A : α → β} (l : List α) :
    List.Forall₂ (fun x y => A x = y) l (l.map A) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih => exact List.Forall₂.cons rfl ih

/-! ## The `seen` table: `HashMap2` against `Std.HashSet` -/

section SetRel

open ConRon.Refine.HashMap2 (Inv KeysOk toFun)
open ConRon.Refine.HashMap (Eq2Fwd)

variable {K K' : Type} [DecidableEq K] [BEq K'] [LawfulBEq K'] [Hashable K'] [LawfulHashable K']
  {hI : ron.hashmap.Hashable K} {eI : ron.hashmap.Eq2 K} {A : K → K'}

/-- **A `HashMap2` keyed by handles, as a set of what the handles stand for.** -/
structure SetRel (hI : ron.hashmap.Hashable K) (A : K → K')
    (m : ron.hashmap2.HashMap2 K Bool) (s : _root_.Std.HashSet K') : Prop where
  inv : Inv hI m
  mem : ∀ k, (toFun m k).isSome = s.contains (A k)

omit [LawfulBEq K'] [LawfulHashable K'] in
/-- `HashMap2::with_capacity`, against any empty set. -/
theorem SetRel.with_capacity {c : Std.Usize} {m : ron.hashmap2.HashMap2 K Bool} {n : Nat}
    (h : ron.hashmap2.HashMap2.with_capacity K Bool c = ok m) :
    SetRel hI A m (_root_.Std.HashSet.emptyWithCapacity n) := by
  obtain ⟨hinv, -, hnone⟩ := ConRon.Refine.HashMap2.with_capacity_refines (HashableInst := hI) h
  exact ⟨hinv, fun k => by rw [hnone]; simp⟩

omit [LawfulBEq K'] [LawfulHashable K'] in
/-- `contains_key` is `contains`. -/
theorem SetRel.contains_key {m : ron.hashmap2.HashMap2 K Bool} {s : _root_.Std.HashSet K'} {k : K}
    {b : Bool} (heq : Eq2Fwd eI (fun _ => True)) (hs : SetRel hI A m s)
    (h : ron.hashmap2.HashMap2.contains_key hI eI m k = ok b) : b = s.contains (A k) := by
  rw [ConRon.Refine.HashMap2.contains_key_refines_gen heq hs.inv (fun _ _ => trivial) trivial h]
  exact hs.mem k

/-- `insert` is `insert`. -/
theorem SetRel.insert {m m' : ron.hashmap2.HashMap2 K Bool} {s : _root_.Std.HashSet K'} {k : K}
    {v : Bool} {old : Option Bool} (heq : Eq2Fwd eI (fun _ => True))
    (hinj : Function.Injective A) (hs : SetRel hI A m s)
    (h : ron.hashmap2.HashMap2.insert hI eI m k v = ok (old, m')) :
    SetRel hI A m' (s.insert (A k)) := by
  obtain ⟨hinv, -, hupd, -⟩ :=
    ConRon.Refine.HashMap2.insert_refines_gen heq hs.inv (fun _ _ => trivial) trivial h
  refine ⟨hinv, fun k1 => ?_⟩
  rw [hupd, Function.update_apply, _root_.Std.HashSet.contains_insert]
  by_cases hk : k1 = k
  · subst hk; simp
  · have hne : (A k == A k1) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun he => hk (hinj he).symm
    rw [ite_eq_right hk, hne, Bool.false_or]
    exact hs.mem k1

end SetRel

end ConRon.Refine2.Frontend.Olean

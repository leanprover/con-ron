/-
# `ConRon.Bridge.Modular.Fuel` — `isPropCheap`'s head, exactly (task #166)

The clash rule's heads (`clashHeads`) decide which statements the worker reads, so the twin's
head of a statement must be upstream's, not only where it finds one.  Its walks take fuel
(`closureFuel`, 2^40), and a well formed store is far smaller: every table is capped
(`EWFAt.capP`/`capS`, at most 2^30 nodes), so the store holds fewer than 2^35 nodes, and every
expression it denotes is read back within that many steps (`denoteE` is `denoteEAux` at the node
count).  At fuel above the readback's, the twin's telescope and head are upstream's
(`isPropBody_exact`, `isPropHead_exact`), and so is the head (`isPropCheapHeadOf_run`).  Plain
induction on the readback's fuel, not `vcgen`.
-/
module

public import ConRon.Bridge.Modular.ReadsParts
public import ConRon.Bridge.Frontend.Olean.MergeAll

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (isPropBody isPropHead)

theorem tables_count_le {t : ETables} (h : ∀ v, t.sizeOf v ≤ v.cap) :
    t.count ≤ 10 * Idx.wideCap := by
  have h1 := h (.bvar 0)
  have h2 := h (.fvar 0 default)
  have h3 := h (.sort default)
  have h4 := h (.const default default)
  have h5 := h (.app default default)
  have h6 := h (.lam default default)
  have h7 := h (.forallE default default)
  have h8 := h (.letE default default default)
  have h9 := h (.lit default)
  have h10 := h (.proj default 0 default)
  simp only [ETables.sizeOf, ENodeView.cap] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  unfold ETables.count
  simp only [Idx.idxCap, Idx.wideCap] at *
  omega

/-- **A well formed store's node count is below the walks' fuel.** -/
theorem nodeCount_lt_closureFuel {st : EStore} (hwf : StoreWF st) :
    st.nodeCount + 1 ≤ ConLeche.Frontend.Olean.closureFuel := by
  obtain ⟨rk, hr⟩ := hwf
  have hp := tables_count_le hr.capP
  have hs := tables_count_le hr.capS
  unfold EStore.nodeCount EStore.persCount EStore.scrCount
  simp only [Idx.wideCap, ConLeche.Frontend.Olean.closureFuel] at *
  omega

/-- The readback at a fuel answers at every larger one. -/
theorem denoteEAux_le {st : EStore} {f : Nat} {e : EIdx} {eC : Expr}
    (h : denoteEAux st f e = some eC) (hf : f ≤ st.nodeCount + 1) : denoteE st e = some eC :=
  denoteEAux_mono st f _ e eC hf h

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap — **at fuel above the
readback's, the twin's telescope is upstream's** body. -/
theorem isPropBody_exact {s : AState} (hok : StateOK s) :
    ∀ (f fuel : Nat) {e b : EIdx} {eC : Expr} {s' : AState}, denoteEAux s.store f e = some eC →
      f ≤ fuel → isPropBody fuel e s = .ok (b, s') →
      ∃ f' ≤ f, denoteEAux s.store f' b = some (ConLeche.Frontend.Olean.isPropCheap.body eC)
  | 0, _, e, b, eC, s', hd, _, _ => by simp [denoteEAux] at hd
  | f + 1, 0, e, b, eC, s', hd, hle, _ => by omega
  | f + 1, fuel + 1, e, b, eC, s', hd, hle, h => by
    rw [isPropBody] at h
    obtain ⟨v, s₁, h1, h⟩ := AM.bind_ok h
    obtain ⟨hs1, hv⟩ := view_run h1
    subst hs1
    have hd' := hd
    simp only [denoteEAux, hv, Option.bind_some] at hd'
    cases v with
    | forallE t x =>
      simp only [opt2_eq_some_iff] at hd'
      obtain ⟨tC, xC, -, hx, rfl⟩ := hd'
      obtain ⟨f', hf', hb⟩ := isPropBody_exact hok f fuel hx (by omega) h
      exact ⟨f', by omega, by simpa [ConLeche.Frontend.Olean.isPropCheap.body] using hb⟩
    | bvar _ =>
      obtain ⟨rfl, -⟩ := AM.pure_ok h
      simp only [Option.some.injEq] at hd'; subst hd'
      exact ⟨f + 1, le_refl _, by simpa [ConLeche.Frontend.Olean.isPropCheap.body] using hd⟩
    | fvar _ _ =>
      obtain ⟨rfl, -⟩ := AM.pure_ok h
      refine ⟨f + 1, le_refl _, ?_⟩
      rw [hd]; cases eC <;> simp_all [ConLeche.Frontend.Olean.isPropCheap.body, Option.map]
    | sort _ =>
      obtain ⟨rfl, -⟩ := AM.pure_ok h
      refine ⟨f + 1, le_refl _, ?_⟩
      rw [hd]; cases eC <;> simp_all [ConLeche.Frontend.Olean.isPropCheap.body, Option.map]
    | const _ _ =>
      obtain ⟨rfl, -⟩ := AM.pure_ok h
      refine ⟨f + 1, le_refl _, ?_⟩
      rw [hd]; cases eC <;> simp_all [ConLeche.Frontend.Olean.isPropCheap.body, opt2_eq_some_iff]
    | app _ _ =>
      obtain ⟨rfl, -⟩ := AM.pure_ok h
      refine ⟨f + 1, le_refl _, ?_⟩
      rw [hd]; cases eC <;> simp_all [ConLeche.Frontend.Olean.isPropCheap.body, opt2_eq_some_iff]
    | lam _ _ =>
      obtain ⟨rfl, -⟩ := AM.pure_ok h
      refine ⟨f + 1, le_refl _, ?_⟩
      rw [hd]; cases eC <;> simp_all [ConLeche.Frontend.Olean.isPropCheap.body, opt2_eq_some_iff]
    | letE _ _ _ =>
      obtain ⟨rfl, -⟩ := AM.pure_ok h
      refine ⟨f + 1, le_refl _, ?_⟩
      rw [hd]; cases eC <;> simp_all [ConLeche.Frontend.Olean.isPropCheap.body, opt3_eq_some_iff]
    | lit _ =>
      obtain ⟨rfl, -⟩ := AM.pure_ok h
      refine ⟨f + 1, le_refl _, ?_⟩
      rw [hd]; cases eC <;> simp_all [ConLeche.Frontend.Olean.isPropCheap.body]
    | proj _ _ _ =>
      obtain ⟨rfl, -⟩ := AM.pure_ok h
      refine ⟨f + 1, le_refl _, ?_⟩
      rw [hd]; cases eC <;> simp_all [ConLeche.Frontend.Olean.isPropCheap.body, opt2_eq_some_iff]

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap — **at fuel above the
readback's, the twin finds no head only where upstream finds none.** -/
theorem isPropHead_exact {s : AState} (hok : StateOK s) :
    ∀ (f fuel : Nat) {e : EIdx} {eC : Expr} {k : Nat} {s' : AState}, denoteEAux s.store f e = some eC →
      f ≤ fuel → isPropHead fuel e k s = .ok (none, s') →
      ConLeche.Frontend.Olean.isPropCheap.head eC k = none
  | 0, _, e, eC, k, s', hd, _, _ => by simp [denoteEAux] at hd
  | f + 1, 0, e, eC, k, s', hd, hle, _ => by omega
  | f + 1, fuel + 1, e, eC, k, s', hd, hle, h => by
    rw [isPropHead] at h
    obtain ⟨v, s₁, h1, h⟩ := AM.bind_ok h
    obtain ⟨hs1, hv⟩ := view_run h1
    subst hs1
    simp only [denoteEAux, hv, Option.bind_some] at hd
    cases v with
    | app g a =>
      simp only [opt2_eq_some_iff] at hd
      obtain ⟨gC, aC, hg, -, rfl⟩ := hd
      have := isPropHead_exact hok f fuel hg (by omega) h
      simpa [ConLeche.Frontend.Olean.isPropCheap.head] using this
    | const _ _ => cases (AM.pure_ok h).1
    | bvar _ =>
      simp only [Option.some.injEq] at hd; subst hd; rfl
    | fvar _ _ => cases eC <;> simp_all [ConLeche.Frontend.Olean.isPropCheap.head, Option.map]
    | sort _ => cases eC <;> simp_all [ConLeche.Frontend.Olean.isPropCheap.head, Option.map]
    | lam _ _ => cases eC <;> simp_all [ConLeche.Frontend.Olean.isPropCheap.head, opt2_eq_some_iff]
    | forallE _ _ => cases eC <;> simp_all [ConLeche.Frontend.Olean.isPropCheap.head, opt2_eq_some_iff]
    | letE _ _ _ => cases eC <;> simp_all [ConLeche.Frontend.Olean.isPropCheap.head, opt3_eq_some_iff]
    | lit _ => simp only [Option.some.injEq] at hd; subst hd; rfl
    | proj _ _ _ => cases eC <;> simp_all [ConLeche.Frontend.Olean.isPropCheap.head, opt2_eq_some_iff]

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:45-47 isPropCheap.headOf — **the twin's head of
a statement is upstream's**, read back. -/
theorem isPropCheapHeadOf_run {s : AState} (hok : StateOK s) {ty : EIdx} {tyC : Expr}
    (hty : denoteE s.store ty = some tyC) {o : Option NIdx} {s' : AState}
    (h : ConRon.Arena.Frontend.Olean.isPropCheapHeadOf ty s = .ok (o, s')) :
    s' = s ∧ Option.Rel (fun n nC => denoteN s.store.ns n = some nC) o
      (ConLeche.Frontend.Olean.isPropCheap.headOf tyC) := by
  have hfuel := nodeCount_lt_closureFuel hok.wf
  unfold ConRon.Arena.Frontend.Olean.isPropCheapHeadOf at h
  obtain ⟨b, s₁, h1, h⟩ := AM.bind_ok h
  obtain ⟨hs1, bC, hb, hbd⟩ := isPropBody_run hok _ hty h1
  subst hs1
  obtain ⟨f', hf', hbe⟩ := isPropBody_exact hok _ _ hty hfuel h1
  have hbC : bC = ConLeche.Frontend.Olean.isPropCheap.body tyC :=
    Option.some.inj (hb.symm.trans (denoteEAux_le hbe (by omega)))
  subst hbC
  obtain ⟨o', s₂, h2, h⟩ := AM.bind_ok h
  have hs2 := isPropHead_state _ h2
  subst hs2
  unfold ConLeche.Frontend.Olean.isPropCheap.headOf
  rcases o' with _ | ⟨n, k⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    have := isPropHead_exact hok f' _ hbe (by omega) h2
    rw [this]; exact .none
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    obtain ⟨-, -, nC, hn, hhead⟩ := isPropHead_run hok _ hb h2
    rw [hhead]; exact .some hn

end ConRon.Bridge.Modular

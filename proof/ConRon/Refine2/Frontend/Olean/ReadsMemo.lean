/-
# `ConRon.Refine2.Frontend.Olean.ReadsMemo` — the memo of a read

**Task #166, Theorem 2.**  `reads.rs`'s memo reads against the twin's (`Arena/Frontend/Olean/
Reads.lean`): `memo_add`, `memo_add_all`, `memo_roots` grow the memo (`MemoS`: the memos related
by `SMRel`, the error channel `CheckError`); `memo_name`, `memo_expr` and the `MemoRead` pointer
read (`memo_read_rel`) are `RS` reads.
-/
import ConRon.Refine2.Frontend.Olean.ReadKinds

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.reads (memo_add memo_add_all memo_add_all_loop memo_roots memo_name memo_expr)
open frontend.olean.fast (K_NAME K_EXPR c_entry_names c_entry_exprs)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Refine.HashMap (uscalar_add_eq)
open ConLeche.Frontend.Olean (CEntryF)
open Arena.Frontend.Olean (memoAdd memoAddAll memoRoots memoName memoExpr memoRead entryMap)

/-! ## `MemoS`: a step that grows the memo -/

/-- **The lockstep judgement of a step that grows the memo**: from related states, the Rust's
`m` over `st.store` and the twin's `x`, the memos related by `SMRel`. -/
def MemoS (pers : arena.store.PersTier) (st : arena.monad.AState) (lst : AState)
    (m : Result (core.result.Result Unit kernel.core_types.CheckError × arena.store.EStore ×
      frontend.olean.sparse.SM)) (x : AM TSM) : Prop :=
  AStateRel₀ pers st lst → AStateInv pers st → ∀ o s' d', m = ok (o, s', d') →
    match o with
    | .Ok _ => ∃ t lst', x.run lst = .ok (t, lst') ∧ SMRel d' t ∧
        AStateRel₀ pers (withStore st s') lst' ∧ AStateInv pers (withStore st s')
    | .Err e => AErrSim e (x.run lst)

theorem MemoS.leaf {pers st lst} {d : frontend.olean.sparse.SM} {t : TSM} (h : SMRel d t) :
    MemoS pers st lst (ok (.Ok (), st.store, d)) (pure t) := by
  intro hrel hinv o s' d' hm
  cases Result.ok_injective hm
  exact ⟨t, lst, rfl, h, hrel, hinv⟩

theorem MemoS.pure_step {γ : Type} {pers st lst} {f : Result γ} {k} {x : AM TSM}
    (h : ∀ a, f = ok a → MemoS pers st lst (k a) x) : MemoS pers st lst (Std.bind f k) x := by
  intro hrel hinv o s' d' hm
  obtain ⟨a, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact h a h1 hrel hinv o s' d' h2

/-- **A step, then the rest.** -/
theorem MemoS.bind {pers st lst} {f} {x : AM TSM} {g : TSM → AM TSM}
    {KR : arena.store.EStore → frontend.olean.sparse.SM →
      Result (core.result.Result Unit kernel.core_types.CheckError × arena.store.EStore ×
        frontend.olean.sparse.SM)}
    (hf : MemoS pers st lst f x)
    (hk : ∀ s1 d1 t1 lst1, SMRel d1 t1 → MemoS pers (withStore st s1) lst1 (KR s1 d1) (g t1)) :
    MemoS pers st lst
      (do
        let (r1, ar1, d1) ← f
        match r1 with
        | .Ok _ => KR ar1 d1
        | .Err _ => ok (r1, ar1, d1))
      (x >>= g) := by
  intro hrel hinv o s' d' hm
  obtain ⟨⟨r1, ar1, d1⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have hF := hf hrel hinv r1 ar1 d1 h1
  cases r1 with
  | Ok u =>
    obtain ⟨b, lst1, hx, hR, h3, h4⟩ := hF
    rw [am_bind_ok hx]
    exact hk ar1 d1 b lst1 hR h3 h4 o s' d' h2
  | Err e =>
    cases Result.ok_injective h2
    show AErrSim e _
    rw [StateT.run_bind]
    exact AErrSim.bind hF _

/-! ## Into the memo -/

/-- **`memo_add` is `memoAdd`.** -/
theorem memo_add_refines {pk bs r pers st lst} {k : Std.U8} {d : frontend.olean.sparse.SM} {t : TSM}
    {v : Std.U64} (hr : RegionFits bs r) (hd : SMRel d t) :
    MemoS pers st lst (memo_add pk pers st.store bs r k d v)
      (memoAdd (absPins pk) (absRegion bs r) (absByte k) t (absWord v)) := by
  rw [memo_add, memoAdd]
  refine MemoS.pure_step fun o ho => ?_
  rw [← region_loc_eq bs ho]
  cases o with
  | none => exact MemoS.leaf hd
  | some c =>
    simp only [locOf, Option.map_some]
    refine MemoS.pure_step fun b hb => ?_
    intro hrel hinv o s' d' hm
    obtain ⟨⟨r1, ar1, d1⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
    have hF := s_go_ts (pk := pk) (pers := pers) hr (frontier_empty_rel hb) c.val (k := k) (g := c)
      (st := st) (lst := lst) rfl hd hrel hinv r1 ar1 d1 h1
    cases r1 with
    | Ok u =>
      obtain ⟨t1, lst1, hx, hR, h3, h4⟩ := hF
      cases Result.ok_injective h2
      rw [am_bind_ok hx]
      exact ⟨t1, lst1, rfl, hR, h3, h4⟩
    | Err e =>
      cases e with
      | Bad =>
        obtain ⟨lst1, hx, h3, h4⟩ := hF
        peel h2 as d2, hd2
        cases Result.ok_injective h2
        rw [am_bind_ok hx]
        exact ⟨{}, lst1, rfl, sm_empty_rel hd2, h3, h4⟩
      | Err e =>
        cases Result.ok_injective h2
        show AErrSim e _
        rw [StateT.run_bind]
        exact AErrSim.bind hF _

/-- **`memo_add_all`'s loop is `memoAddAll`** on what is left of the pointers. -/
theorem memo_add_all_loop_refines {pk bs r pers} {k : Std.U8} {vs : alloc.vec.Vec Std.U64}
    (hr : RegionFits bs r) :
    ∀ (n : Nat) (i : Std.Usize) (st : arena.monad.AState) (lst : AState) d t,
      vs.val.length - i.val ≤ n → SMRel d t →
      MemoS pers st lst (memo_add_all_loop pk pers st.store bs r k d vs i)
        (memoAddAll (absPins pk) (absRegion bs r) (absByte k) t ((vs.val.drop i.val).map absWord)) := by
  intro n
  induction n with
  | zero =>
    intro i st lst d t hn hd
    rw [memo_add_all_loop, ite_eq_right (by scalar_tac), List.drop_eq_nil_of_le (by omega)]
    exact MemoS.leaf hd
  | succ n ih =>
    intro i st lst d t hn hd
    rw [memo_add_all_loop]
    by_cases hi : i < alloc.vec.Vec.len vs
    · rw [ite_eq_left hi]
      have hlt : i.val < vs.val.length := by scalar_tac
      refine MemoS.pure_step fun x hx => ?_
      obtain ⟨_, he⟩ := List.getElem?_eq_some_iff.mp (ConRon.Refine.ExprOps.vec_index_getElem? hx)
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, he, memoAddAll]
      intro hrel hinv o s' d' hm
      obtain ⟨⟨r1, ar1, d1⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
      have hF := memo_add_refines (pk := pk) (k := k) (v := x) (st := st) (lst := lst) hr hd
        hrel hinv r1 ar1 d1 h1
      cases r1 with
      | Ok u =>
        obtain ⟨t1, lst1, hx1, hR, h3, h4⟩ := hF
        rw [am_bind_ok hx1]
        peel h2 as i3, hi3
        have hiv : i3.val = i.val + 1 := uscalar_add_eq hi3
        have := ih i3 (withStore st ar1) lst1 d1 t1 (by omega) hR h3 h4 o s' d' h2
        rw [hiv] at this
        exact this
      | Err e =>
        cases Result.ok_injective h2
        show AErrSim e _
        rw [StateT.run_bind]
        exact AErrSim.bind hF _
    · rw [ite_eq_right hi, List.drop_eq_nil_of_le (by scalar_tac)]
      exact MemoS.leaf hd

/-- **`memo_add_all` is `memoAddAll`.** -/
theorem memo_add_all_refines {pk bs r pers st lst} {k : Std.U8} {vs : alloc.vec.Vec Std.U64}
    {d : frontend.olean.sparse.SM} {t : TSM} (hr : RegionFits bs r) (hd : SMRel d t) :
    MemoS pers st lst (memo_add_all pk pers st.store bs r k d vs)
      (memoAddAll (absPins pk) (absRegion bs r) (absByte k) t (vs.val.map absWord)) := by
  rw [memo_add_all]
  have := memo_add_all_loop_refines (pk := pk) (pers := pers) (k := k) (vs := vs) hr _ 0#usize st lst
    d t (Nat.le_refl _) hd
  simpa using this

/-- **`memo_roots` is `memoRoots`.** -/
theorem memo_roots_refines {pk bs r pers st lst} {d : frontend.olean.sparse.SM} {t : TSM}
    {sk : frontend.olean.spec.CEntryF Std.U64 Std.U64} {sk' : CEntryF UInt64 UInt64}
    (hr : RegionFits bs r) (hd : SMRel d t) (hs : EV sk sk') :
    MemoS pers st lst (memo_roots pk pers st.store bs r d sk)
      (memoRoots (absPins pk) (absRegion bs r) t sk') := by
  rw [memo_roots, memoRoots]
  refine MemoS.pure_step fun ns hns => MemoS.pure_step fun es hes => ?_
  have en : ns.val.map absWord = sk'.names := by
    rw [c_entry_names_val hns]; simpa using namesL_abs hs
  have ee : es.val.map absWord = sk'.exprs := by
    rw [c_entry_exprs_val hes]; simpa using exprsL_abs hs
  rw [← en, ← ee, ← absByte_k_name, ← absByte_k_expr]
  exact MemoS.bind (memo_add_all_refines hr hd) fun s1 d1 t1 lst1 h1 => memo_add_all_refines hr h1

/-! ## Out of the memo -/

/-- **`memo_name` is `memoName`.** -/
theorem memo_name_refines {pk bs r pers st lst} {d : frontend.olean.sparse.SM} {t : TSM}
    {v : Std.U64} (hr : RegionFits bs r) (hd : SMRel d t) :
    RS pers (EqA absNIdx) st lst (memo_name pk pers st.store bs r d v)
      (memoName (absPins pk) (absRegion bs r) t (absWord v)) := by
  rw [memo_name, memoName]
  by_cases hv : v = 1#u64
  · rw [ite_eq_left hv, ite_eq_left (word_eq_one.mpr hv)]
    refine RS.pure_step fun n hn => ?_
    rw [nidx_dup2_ok hn]
    exact RS.some rfl
  · rw [ite_eq_right hv, ite_eq_right (fun he => hv (word_eq_one.mp he))]
    refine RS.pure_step fun o ho => ?_
    rw [← region_loc_eq bs ho]
    cases o with
    | none => exact RS.none
    | some c =>
      simp only [locOf, Option.map_some]
      refine RS.pure_step fun o1 ho1 => ?_
      have e := hd.names.get_eq ho1
      rw [← e]
      cases o1 with
      | none => exact sparse_name_p_refines hr
      | some n =>
        refine RS.pure_step fun n1 hn1 => ?_
        rw [nidx_dup2_ok hn1]
        exact RS.some rfl

/-- **`memo_expr` is `memoExpr`.** -/
theorem memo_expr_refines {pk bs r pers st lst} {d : frontend.olean.sparse.SM} {t : TSM}
    {v : Std.U64} (hr : RegionFits bs r) (hd : SMRel d t) :
    RS pers (EqA absEIdx) st lst (memo_expr pk pers st.store bs r d v)
      (memoExpr (absPins pk) (absRegion bs r) t (absWord v)) := by
  rw [memo_expr, memoExpr]
  refine RS.pure_step fun o ho => ?_
  rw [← region_loc_eq bs ho]
  cases o with
  | none => exact RS.none
  | some c =>
    simp only [locOf, Option.map_some]
    refine RS.pure_step fun o1 ho1 => ?_
    have e := hd.exprs.get_eq ho1
    rw [← e]
    cases o1 with
    | none => exact sparse_expr_p_refines hr
    | some x =>
      refine RS.pure_step fun x1 hx1 => ?_
      rw [eidx_dup_id _ _ hx1]
      exact RS.some rfl

/-- **`MemoRead` is the twin's `memoRead`.** -/
theorem memo_read_rel {pk bs r pers} {d : frontend.olean.sparse.SM} {t : TSM} (hr : RegionFits bs r)
    (hd : SMRel d t) :
    PtrRel frontend.olean.reads.MemoRead.Insts.Con_ron_coreFrontendOleanSpecPtrRead { st := d }
      (memoRead (absPins pk) (absRegion bs r) t) pk bs r pers where
  nm _ _ _ := memo_name_refines hr hd
  ex _ _ _ := memo_expr_refines hr hd

end ConRon.Refine2.Frontend.Olean

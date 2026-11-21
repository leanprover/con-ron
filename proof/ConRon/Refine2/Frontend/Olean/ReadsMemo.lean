/-
# `ConRon.Refine2.Frontend.Olean.ReadsMemo` — several constants read with one memo

**Task #166, Theorem 2.**  `reads.rs`'s memo reads against the twin's (`Arena/Frontend/Olean/
Reads.lean`): `memo_add`, `memo_add_all`, `memo_roots`, `memo_roots_all` grow the memo (`MemoS`:
the memos related by `SMRel`, the error channel `CheckError`); `memo_name`, `memo_expr` and the
`MemoRead` pointer read (`memo_read_rel`), `skels_at`, `entries_map`, `entries_at`, and `view.rs`'s
`read_entries` are `RS` reads.
-/
import ConRon.Refine2.Frontend.Olean.ReadKinds

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.reads (memo_add memo_add_all memo_add_all_loop memo_roots memo_roots_all
  memo_roots_all_loop memo_name memo_expr skels_at skels_at_loop entries_map entries_map_loop
  entries_at)
open frontend.olean.view (read_entries)
open frontend.olean.fast (K_NAME K_EXPR c_entry_names c_entry_exprs)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Refine.HashMap (uscalar_add_eq)
open ConLeche.Frontend.Olean (CEntryF)
open Arena.Frontend.Olean (memoAdd memoAddAll memoRoots memoRootsAll memoName memoExpr memoRead
  skelsAt entriesMap entriesAt readEntries entryMap)

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

/-- **`memo_roots_all`'s loop is `memoRootsAll`** on what is left of the skeletons. -/
theorem memo_roots_all_loop_refines {pk bs r pers}
    {sks : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {l : List (CEntryF UInt64 UInt64)} (hr : RegionFits bs r) (hl : List.Forall₂ EV sks.val l) :
    ∀ (n : Nat) (i : Std.Usize) (st : arena.monad.AState) (lst : AState) d t,
      sks.val.length - i.val ≤ n → SMRel d t →
      MemoS pers st lst (memo_roots_all_loop pk pers st.store bs r d sks i)
        (memoRootsAll (absPins pk) (absRegion bs r) t (l.drop i.val)) := by
  have hlen := hl.length_eq
  intro n
  induction n with
  | zero =>
    intro i st lst d t hn hd
    rw [memo_roots_all_loop, ite_eq_right (by scalar_tac), List.drop_eq_nil_of_le (by omega)]
    exact MemoS.leaf hd
  | succ n ih =>
    intro i st lst d t hn hd
    rw [memo_roots_all_loop]
    by_cases hi : i < alloc.vec.Vec.len sks
    · rw [ite_eq_left hi]
      have hlt : i.val < sks.val.length := by scalar_tac
      have hlt' : i.val < l.length := by omega
      refine MemoS.pure_step fun x hx => ?_
      obtain ⟨_, he⟩ := List.getElem?_eq_some_iff.mp (ConRon.Refine.ExprOps.vec_index_getElem? hx)
      have hEV : EV x l[i.val] := by
        rw [← he]; exact List.forall₂_iff_get.mp hl |>.2 _ hlt hlt'
      rw [List.drop_eq_getElem_cons hlt', memoRootsAll]
      refine MemoS.bind (memo_roots_refines hr hd hEV) fun s1 d1 t1 lst1 h1 =>
        MemoS.pure_step fun i3 hi3 => ?_
      have hiv : i3.val = i.val + 1 := uscalar_add_eq hi3
      have := ih i3 (withStore st s1) lst1 d1 t1 (by omega) h1
      rw [hiv] at this
      exact this
    · rw [ite_eq_right hi, List.drop_eq_nil_of_le (by scalar_tac)]
      exact MemoS.leaf hd

/-- **`memo_roots_all` is `memoRootsAll`.** -/
theorem memo_roots_all_refines {pk bs r pers st lst} {d : frontend.olean.sparse.SM} {t : TSM}
    {sks : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {l : List (CEntryF UInt64 UInt64)} (hr : RegionFits bs r) (hl : List.Forall₂ EV sks.val l)
    (hd : SMRel d t) :
    MemoS pers st lst (memo_roots_all pk pers st.store bs r d sks)
      (memoRootsAll (absPins pk) (absRegion bs r) t l) := by
  rw [memo_roots_all]
  have := memo_roots_all_loop_refines (pk := pk) (pers := pers) hr hl _ 0#usize st lst d t
    (Nat.le_refl _) hd
  simpa using this

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

/-! ## Several constants -/

/-- `skels_at`'s loop, with what it has so far. -/
theorem skels_at_loop_ps {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {consts : alloc.vec.Vec Std.U64} :
    ∀ (k : Nat) {i : Std.Usize} {out} {pre : List (CEntryF UInt64 UInt64)} {o} (lst : AState),
      consts.val.length - i.val ≤ k → List.Forall₂ EV out.val pre →
      skels_at_loop bs r consts out i = ok o →
      PSOut (fun v l => List.Forall₂ EV v.val (pre ++ l)) lst o
        ((skelsAt (absRegion bs r) ((consts.val.drop i.val).map (·.val))).run lst) := by
  intro k
  induction k with
  | zero =>
    intro i out pre o lst hk hpre h
    rw [skels_at_loop, ite_eq_right (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_eq_nil_of_le (by omega)]
    exact ⟨[], rfl, by simpa using hpre⟩
  | succ k ih =>
    intro i out pre o lst hk hpre h
    rw [skels_at_loop] at h
    by_cases hi : i < alloc.vec.Vec.len consts
    · rw [ite_eq_left hi] at h
      have hlt : i.val < consts.val.length := by scalar_tac
      peel h as c, hc
      obtain ⟨_, hce⟩ := vec_index_eq hc
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, ← hce, skelsAt]
      peel h as o1, ho1
      refine sat_elim (const_skel_eq (bs := bs) (r := r) ho1) (fun hA hy => ?_) (fun sk sk' hA hy hS => ?_)
      · subst hA
        rw [hy]
        cases Result.ok_injective h
        rfl
      subst hA
      rw [hy]
      dsimp only at h ⊢
      peel h as r1, hr1
      have hF := skel_fits_refines hS hr1 (lst := lst)
      cases r1 with
      | Ok u =>
        obtain ⟨hrun, hEV⟩ := hF
        rw [am_bind_ok hrun]
        peel h as out1, ho
        peel h as i3, hi3
        have hiv : i3.val = i.val + 1 := uscalar_add_eq hi3
        rw [← hiv]
        exact PSOut.cons (ih (i := i3) lst (by omega) (pre := pre ++ [sk'])
          (by rw [ConRon.Refine.vec_push_val ho]; exact List.rel_append hpre (List.Forall₂.cons hEV List.Forall₂.nil)) h)
          rfl (fun _ => rfl)
      | Err e =>
        cases Result.ok_injective h
        cases e with
        | Bad => exact hF.elim
        | Err e =>
          show AErrSim e _
          rw [StateT.run_bind]
          exact AErrSim.bind hF _
    · rw [ite_eq_right hi] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by scalar_tac)]
      exact ⟨[], rfl, by simpa using hpre⟩

/-- **`skels_at` is `skelsAt`.** -/
theorem skels_at_ps {bs : Slice Std.U8} {r : frontend.olean.region.Region}
    {cs : alloc.vec.Vec Std.U64} :
    PS (fun v l => List.Forall₂ EV v.val l) (skels_at bs r cs) (skelsAt (absRegion bs r) (cs.val.map (·.val))) := by
  intro o h lst
  rw [skels_at] at h
  have := skels_at_loop_ps (pre := []) _ lst (Nat.le_refl _) (by exact List.Forall₂.nil) h
  simpa using this

/-- `entriesMap` is `List.mapM` of `entryMap`, at `OptionT AM`. -/
theorem entriesMap_eq (rd : Arena.Frontend.Olean.PtrRead) :
    ∀ l : List (CEntryF UInt64 UInt64),
      entriesMap rd l = (l.mapM (m := OptionT AM) fun s => OptionT.mk (entryMap rd s))
  | [] => rfl
  | s :: ss => by
    rw [entriesMap, List.mapM_cons, ← entriesMap_eq rd ss, optionT_bind_eq]
    refine congrArg (entryMap rd s >>= ·) (funext fun o => ?_)
    cases o with
    | none => rfl
    | some e =>
      show _ = ((entriesMap rd ss : OptionT AM _) >>= fun es => pure (e :: es) : OptionT AM _)
      rw [optionT_bind_eq]
      refine congrArg (entriesMap rd ss >>= ·) (funext fun o => ?_)
      cases o <;> rfl

/-- **`entries_map` is `entriesMap`.** -/
theorem entries_map_refines {R : Type} {inst : frontend.olean.spec.PtrRead R} {rd : R}
    {t : Arena.Frontend.Olean.PtrRead} {pk bs r pers} (hp : PtrRel inst rd t pk bs r pers)
    {sks : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {l : List (CEntryF UInt64 UInt64)} (hl : List.Forall₂ EV sks.val l) (st lst) :
    RS pers (fun v l' => List.Forall₂ (EntryRel absNIdx absEIdx ValRel) v.val l') st lst
      (entries_map inst rd pk pers st.store bs r sks) (entriesMap t l) := by
  rw [entries_map, entriesMap_eq]
  refine RS.vec_map (R := EntryRel absNIdx absEIdx ValRel)
    (loop := fun ar out i => entries_map_loop inst rd pk pers ar bs r sks out i)
    hl ?_ ?_ (by simp) (by rfl)
  · intro ar out i hi
    show entries_map_loop inst rd pk pers ar bs r sks out i = _
    rw [entries_map_loop, ite_eq_right (by scalar_tac)]
  · intro i out x x' K Rf st lst hx hS hK
    show RS _ _ _ _ (entries_map_loop inst rd pk pers st.store bs r sks out i) _
    rw [entries_map_loop,
      ite_eq_left (by have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)]
    refine RS.pure_step fun y hy => ?_
    have hy3 := ConRon.Refine.ExprOps.vec_index_getElem? hy
    rw [hx] at hy3
    cases Option.some.inj hy3
    refine RS.bindT (c_entry_map_refines hp hS st lst) (fun _ _ => by rfl) fun a b s1 lst1 hR =>
      RS.pure_step fun out1 ho => RS.pure_step fun i3 hi3 => ?_
    exact hK a b s1 lst1 out1 i3 hR (ConRon.Refine.vec_push_val ho) (uscalar_add_eq hi3)

/-- **`entries_at` is `entriesAt`.** -/
theorem entries_at_refines {pk bs r pers st lst} {cs : alloc.vec.Vec Std.U64} (hr : RegionFits bs r) :
    RS pers (fun v l' => List.Forall₂ (EntryRel absNIdx absEIdx ValRel) v.val l') st lst
      (entries_at pk pers st.store bs r cs)
      (entriesAt (absPins pk) (absRegion bs r) (cs.val.map (·.val))) := by
  rw [entries_at, entriesAt]
  intro hrel hinv o s' hm
  obtain ⟨r1, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have hP := skels_at_ps (bs := bs) (r := r) (cs := cs) r1 h1 lst
  cases r1 with
  | Ok sks =>
    obtain ⟨l, hx, hR⟩ := hP
    rw [am_bind_ok hx]
    dsimp only at h2 ⊢
    peel h2 as d0, hd0
    obtain ⟨⟨r2, ar1, d1⟩, h3, h4⟩ := ConRon.Refine.bind_eq_ok_iff.mp h2
    have hM := memo_roots_all_refines (pk := pk) (pers := pers) (st := st) (lst := lst) hr hR
      (sm_empty_rel hd0) hrel hinv r2 ar1 d1 h3
    cases r2 with
    | Ok u =>
      obtain ⟨t1, lst1, hx1, hd1, h5, h6⟩ := hM
      rw [am_bind_ok hx1]
      exact entries_map_refines (memo_read_rel hr hd1) hR (withStore st ar1) lst1 h5 h6 o s' h4
    | Err e =>
      cases Result.ok_injective h4
      show AErrSim e _
      rw [StateT.run_bind]
      exact AErrSim.bind hM _
  | Err e =>
    cases Result.ok_injective h2
    cases e with
    | Bad =>
      refine ⟨lst, ?_, hrel, hinv⟩
      rw [am_bind_ok hP]
      rfl
    | Err e =>
      show AErrSim e _
      rw [StateT.run_bind]
      exact AErrSim.bind hP _

/-- **`read_entries` is `readEntries`.** -/
theorem read_entries_refines {pk pers st lst} {f : frontend.olean.view.ModFiles}
    {f' : ConLeche.Frontend.Olean.ModFiles} (hf : ModFilesRel f f')
    {level : frontend.olean.view.OLeanLevel} {cs : alloc.vec.Vec Std.U64} :
    RS pers (fun v l' => List.Forall₂ (EntryRel absNIdx absEIdx ValRel) v.val l') st lst
      (read_entries pk pers st.store f level cs)
      (readEntries (absPins pk) f' (absLevel level) (cs.val.map (·.val))) := by
  rw [read_entries, readEntries]
  refine RS.pure_step fun o ho => ?_
  have hv := mod_files_view_region_eq hf ho
  cases o with
  | none =>
    rw [show f'.viewRegion (absLevel level) = none from hv]
    exact RS.none
  | some p =>
    obtain ⟨vb, a⟩ := p
    dsimp only
    refine RS.pure_step fun bs hbs => RS.pure_step fun r hr => ?_
    obtain ⟨e, hfit⟩ := hv bs r hbs hr
    rw [e]
    exact entries_at_refines hfit

end ConRon.Refine2.Frontend.Olean

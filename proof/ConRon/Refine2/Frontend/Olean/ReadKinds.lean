/-
# `ConRon.Refine2.Frontend.Olean.ReadKinds` — the sparse reads, and a constant's kind's names

**Task #166, Theorem 2.**  `sparse.rs`'s `sparse_name_p`, `sparse_expr_p` (the `SparseRead`
pointer read, `sparse_read_rel`) and `sparse_entry`; `reads.rs`'s `entry_at`, `c_kind_names`,
`rule_names`, `kind_names_at`, `kinds_at`; `view.rs`'s `read_kinds` and `read_entry`: each `RS`
against its twin.
-/
import ConRon.Refine2.Frontend.Olean.Sparse
import ConRon.Refine2.Frontend.Olean.NamePos

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.sparse (sparse_name_p sparse_expr_p sparse_entry)
open frontend.olean.reads (c_kind_names rule_names rule_names_loop kind_names_at kinds_at
  kinds_at_loop entry_at)
open frontend.olean.view (read_kinds read_entry)
open frontend.olean.fast (K_NAME K_EXPR)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Refine.HashMap (uscalar_add_eq)
open ConLeche.Frontend.Olean (CKindF CEntryF)
open Arena.Frontend.Olean (sparseNameP sparseExprP sparseEntry kindNames kindNamesAt readKinds
  entryAt readEntry entryMap)

/-! ## The sparse pointer reads -/

/-- **`sparse_name_p` is `sparseNameP`.** -/
theorem sparse_name_p_refines {pk bs r pers st lst} {v : Std.U64} (hr : RegionFits bs r) :
    RS pers (EqA absNIdx) st lst (sparse_name_p pk pers st.store bs r v)
      (sparseNameP (absPins pk) (absRegion bs r) (absWord v)) := by
  rw [sparse_name_p, sparseNameP]
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
      refine RS.pure_step fun b hb => RS.pure_step fun d0 hd0 => ?_
      rw [← absByte_k_name]
      have hbr := frontier_empty_rel hb
      intro hrel hinv o s' hm
      obtain ⟨⟨r1, ar1, d1⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
      have hF := s_go_ts (pk := pk) (pers := pers) hr hbr c.val (k := K_NAME) (g := c) (st := st)
        (lst := lst) rfl (sm_empty_rel hd0) hrel hinv r1 ar1 d1 h1
      cases r1 with
      | Ok u =>
        obtain ⟨t1, lst1, hx, hR, h3, h4⟩ := hF
        rw [am_bind_ok hx]
        peel h2 as o1, ho1
        have e := lookup_eq nidx_dup_id hR.names hbr.names ho1
        dsimp only
        rw [← e]
        cases o1 with
        | none =>
          cases Result.ok_injective h2
          exact ⟨lst1, rfl, h3, h4⟩
        | some h =>
          cases Result.ok_injective h2
          exact ⟨_, lst1, rfl, rfl, h3, h4⟩
      | Err e =>
        cases Result.ok_injective h2
        cases e with
        | Bad =>
          obtain ⟨lst1, hx, h3, h4⟩ := hF
          rw [am_bind_ok hx]
          exact ⟨lst1, rfl, h3, h4⟩
        | Err e =>
          show AErrSim e _
          rw [StateT.run_bind]
          exact AErrSim.bind hF _

/-- **`sparse_expr_p` is `sparseExprP`.** -/
theorem sparse_expr_p_refines {pk bs r pers st lst} {v : Std.U64} (hr : RegionFits bs r) :
    RS pers (EqA absEIdx) st lst (sparse_expr_p pk pers st.store bs r v)
      (sparseExprP (absPins pk) (absRegion bs r) (absWord v)) := by
  rw [sparse_expr_p, sparseExprP]
  refine RS.pure_step fun o ho => ?_
  rw [← region_loc_eq bs ho]
  cases o with
  | none => exact RS.none
  | some c =>
    simp only [locOf, Option.map_some]
    refine RS.pure_step fun b hb => ?_
    exact frontier_expr_refines hr (frontier_empty_rel hb)

/-- The twin's sparse pointer read. -/
def sparseT (P : Arena.Frontend.Olean.OleanPins) (R : ConLeche.Frontend.Olean.Region) :
    Arena.Frontend.Olean.PtrRead :=
  ⟨sparseNameP P R, sparseExprP P R⟩

/-- **`SparseRead` is the twin's sparse read.** -/
theorem sparse_read_rel {pk bs r pers} (hr : RegionFits bs r) :
    PtrRel frontend.olean.sparse.SparseRead.Insts.Con_ron_coreFrontendOleanSpecPtrRead ()
      (sparseT (absPins pk) (absRegion bs r)) pk bs r pers where
  nm _ _ _ := sparse_name_p_refines hr
  ex _ _ _ := sparse_expr_p_refines hr

/-- **`sparse_entry` is `sparseEntry`.** -/
theorem sparse_entry_refines {pk bs r pers st lst} {c : frontend.olean.spec.CEntryF Std.U64 Std.U64}
    {c' : CEntryF UInt64 UInt64} (hr : RegionFits bs r) (hc : EntryRel absWord absWord ValRel c c') :
    RS pers (EntryRel absNIdx absEIdx ValRel) st lst (sparse_entry pk pers st.store bs r c)
      (sparseEntry (absPins pk) (absRegion bs r) c') := by
  rw [sparse_entry, sparseEntry]
  exact c_entry_map_refines (sparse_read_rel hr) hc st lst

/-- **A skeleton read, its numbers checked, then `k`**: `const_skel`, `skel_fits`, and the rest of
the read, against `constSkel`, `skelFits` and the twin's rest. -/
theorem RS.skel_then {β α : Type} {bs r pers st lst} {c : Std.U64} {R : α → β → Prop}
    {k : frontend.olean.spec.CEntryF Std.U64 Std.U64 → arena.store.EStore →
      Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore)}
    {K : CEntryF UInt64 UInt64 → AM (Option β)}
    (hk : ∀ s s' st lst, EntryRel absWord absWord ValRel s s' → RS pers R st lst (k s st.store) (K s'))
    :
    RS pers R st lst (do
        let o ← frontend.olean.spec.const_skel bs r c
        match o with
        | Option.none => ok (core.result.Result.Err frontend.olean.spec.RdErr.Bad, st.store)
        | Option.some s =>
          let r1 ← frontend.olean.spec.skel_fits s
          match r1 with
          | core.result.Result.Ok _ => k s st.store
          | core.result.Result.Err e => ok (core.result.Result.Err e, st.store))
      (match ConLeche.Frontend.Olean.constSkel (absRegion bs r) c.val with
        | Option.none => pure Option.none
        | Option.some s => do
          Arena.Frontend.Olean.skelFits s
          K s) := by
  refine RS.pure_step fun o ho => ?_
  refine sat_elim (const_skel_eq (bs := bs) (r := r) ho) (fun hA hy => ?_)
    (fun s s' hA hy hS => ?_)
  · subst hA; rw [hy]; exact RS.none
  · subst hA
    rw [hy]
    intro hrel hinv o1 s1 hm
    obtain ⟨r1, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
    have hF := skel_fits_refines hS h1 (lst := lst)
    cases r1 with
    | Ok u =>
      obtain ⟨hrun, hEV⟩ := hF
      show RdOut _ _ _ _ ((Arena.Frontend.Olean.skelFits s' >>= fun _ => K s').run lst)
      rw [am_bind_ok hrun]
      exact hk s s' st lst hEV hrel hinv o1 s1 h2
    | Err e =>
      cases Result.ok_injective h2
      cases e with
      | Bad => exact hF.elim
      | Err e =>
        show AErrSim e _
        rw [StateT.run_bind]
        exact AErrSim.bind hF _

/-- **`entry_at` is `entryAt`.** -/
theorem entry_at_refines {pk bs r pers st lst} {c : Std.U64} (hr : RegionFits bs r) :
    RS pers (EntryRel absNIdx absEIdx ValRel) st lst (entry_at pk pers st.store bs r c)
      (entryAt (absPins pk) (absRegion bs r) c.val) := by
  rw [entry_at, entryAt]
  exact RS.skel_then (k := fun s ar => sparse_entry pk pers ar bs r s)
    (K := fun s' => sparseEntry (absPins pk) (absRegion bs r) s') fun s s' st lst hs => sparse_entry_refines hr hs

/-! ## A kind's names -/

/-- **`rule_names` is `rules.mapM`** of the names, at `OptionT AM`: `q` is the twin's function on a
rule. -/
theorem rule_names_refines {R : Type} {inst : frontend.olean.spec.PtrRead R} {rd : R}
    {t : Arena.Frontend.Olean.PtrRead} {pk bs r pers} (hp : PtrRel inst rd t pk bs r pers)
    {rs : alloc.vec.Vec (Std.U64 × Std.U64 × Std.U64)} {l : List (UInt64 × Nat × UInt64)}
    (hl : List.Forall₂ (RuleRel absWord absWord ValRel) rs.val l)
    {q : UInt64 × Nat × UInt64 → OptionT AM (NIdx × Nat × Unit)}
    (hq : ∀ c n e, q (c, n, e) = (OptionT.mk (t.rdName c) >>= fun c' => pure (c', n, ())))
    (st lst) :
    RS pers (fun v l' => List.Forall₂ (RuleRel absNIdx (fun _ => ()) ValRel) v.val l') st lst
      (rule_names inst rd pk pers st.store bs r rs) (l.mapM (m := OptionT AM) q) := by
  rw [rule_names]
  refine RS.vec_map (R := RuleRel absNIdx (fun _ => ()) ValRel)
    (loop := fun ar out i => rule_names_loop inst rd pk pers ar bs r rs out i)
    hl ?_ ?_ (by simp) (by rfl)
  · intro ar out i hi
    show rule_names_loop inst rd pk pers ar bs r rs out i = _
    rw [rule_names_loop, ite_eq_right (by scalar_tac)]
  · intro i out x x' K Rf st lst hx hS hK
    show RS _ _ _ _ (rule_names_loop inst rd pk pers st.store bs r rs out i) _
    rw [rule_names_loop,
      ite_eq_left (by have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)]
    refine RS.pure_step fun y hy => ?_
    have hy3 := ConRon.Refine.ExprOps.vec_index_getElem? hy
    rw [hx] at hy3
    cases Option.some.inj hy3
    obtain ⟨c, n, e⟩ := x
    obtain ⟨c', n', e'⟩ := x'
    obtain ⟨hc, hn, he⟩ := hS
    cases hc; cases he; cases hn
    rw [hq]
    simp only [bind_assoc, pure_bind]
    refine RS.bindT (hp.nm st lst c) (fun _ _ => by rfl) fun a b s1 lst1 hR =>
      RS.pure_step fun out1 ho => RS.pure_step fun i3 hi3 => ?_
    cases hR
    exact hK (a, n, ()) (absNIdx a, n.val, ()) s1 lst1 out1 i3 ⟨rfl, rfl, rfl⟩
      (ConRon.Refine.vec_push_val ho) (uscalar_add_eq hi3)

/-- **`c_kind_names` is `kindNames`.** -/
theorem c_kind_names_refines {R : Type} {inst : frontend.olean.spec.PtrRead R} {rd : R}
    {t : Arena.Frontend.Olean.PtrRead} {pk bs r pers} (hp : PtrRel inst rd t pk bs r pers)
    {k : frontend.olean.spec.CKindF Std.U64 Std.U64} {k' : CKindF UInt64 UInt64}
    (hk : KindRel absWord absWord ValRel k k') (st lst) :
    RS pers KindNamesRel st lst (c_kind_names inst rd pk pers st.store bs r k) (kindNames t k') := by
  rw [kindNames]
  cases k <;> cases k' <;> try exact hk.elim
  all_goals simp only [c_kind_names, CKindF.mapM, OptionT.run, pure_bind]
  case Ax.ax u u' =>
    cases (show u = u' from hk)
    exact RS.some rfl
  case Defn.defn v h s v' h' s' =>
    obtain ⟨-, rfl, rfl, w⟩ := hk
    refine RS.pure_step fun hr hhr => RS.pure_step fun v1 hv1 => ?_
    rw [hints_dup_val hhr, ConRon.Refine.Expr.str_copy_eq hv1]
    exact RS.some ⟨rfl, rfl, rfl, w⟩
  case Thm.thm v all v' all' =>
    obtain ⟨-, hl⟩ := hk
    refine RS.bindT (names_map_refines hp hl st lst) (fun _ _ => by rfl)
      fun a2 b2 s2 lst2 hR2 => ?_
    exact RS.some ⟨rfl, hR2⟩
  case Opaq.opaq v u v' u' =>
    obtain ⟨-, rfl⟩ := hk
    exact RS.some ⟨rfl, rfl⟩
  case Quot.quot s s' =>
    obtain ⟨rfl, w⟩ := hk
    refine RS.pure_step fun v1 hv1 => ?_
    rw [ConRon.Refine.Expr.str_copy_eq hv1]
    exact RS.some ⟨rfl, w⟩
  case Induct.induct np ni all cs nn ir iu irf np' ni' all' cs' nn' ir' iu' irf' =>
    obtain ⟨h1, h2, hl1, hl2, h3, rfl, rfl, rfl⟩ := hk
    refine RS.bindT (names_map_refines hp hl1 st lst) (fun _ _ => by rfl)
      fun a b s1 lst1 hR => RS.bindT (names_map_refines hp hl2 (withStore st s1) lst1)
        (fun _ _ => by rfl) fun a2 b2 s2 lst2 hR2 => ?_
    exact RS.some ⟨h1, h2, hR, hR2, h3, rfl, rfl, rfl⟩
  case Ctor.ctor ind ci np nf iu ind' ci' np' nf' iu' =>
    obtain ⟨rfl, h1, h2, h3, rfl⟩ := hk
    refine RS.bindT (hp.nm st lst ind) (fun _ _ => by rfl) fun a b s1 lst1 hR => ?_
    cases hR
    exact RS.some ⟨rfl, h1, h2, h3, rfl⟩
  case Recur.recur all np ni nmo nmi rules k2 iu all' np' ni' nmo' nmi' rules' k2' iu' =>
    obtain ⟨hl1, h1, h2, h3, h4, hl2, rfl, rfl⟩ := hk
    refine RS.bindT (names_map_refines hp hl1 st lst) (fun _ _ => by rfl)
      fun a b s1 lst1 hR => RS.bindT
        (rule_names_refines hp hl2 (fun _ _ _ => rfl) (withStore st s1) lst1)
        (fun _ _ => by rfl) fun a2 b2 s2 lst2 hR2 => ?_
    exact RS.some ⟨hR, h1, h2, h3, h4, hR2, rfl, rfl⟩

/-- **`kind_names_at` is `kindNamesAt`.** -/
theorem kind_names_at_refines {pk bs r pers st lst} {c : Std.U64} (hr : RegionFits bs r) :
    RS pers KindNamesRel st lst (kind_names_at pk pers st.store bs r c)
      (kindNamesAt (absPins pk) (absRegion bs r) c.val) := by
  rw [kind_names_at, kindNamesAt]
  exact RS.skel_then
    (k := fun s ar => c_kind_names frontend.olean.sparse.SparseRead.Insts.Con_ron_coreFrontendOleanSpecPtrRead () pk pers ar bs r s.kind)
    (K := fun s' => kindNames (sparseT (absPins pk) (absRegion bs r)) s'.kind)
    fun s s' st lst hs => c_kind_names_refines (sparse_read_rel hr) hs.kind st lst

/-- **`kinds_at` is `cs.mapM kindNamesAt`**, at `OptionT AM`. -/
theorem kinds_at_refines {pk bs r pers} {cs : alloc.vec.Vec Std.U64} (hr : RegionFits bs r) (st lst) :
    RS pers (fun v l => List.Forall₂ KindNamesRel v.val l) st lst (kinds_at pk pers st.store bs r cs)
      ((cs.val.map (·.val)).mapM (m := OptionT AM) fun c =>
        OptionT.mk (kindNamesAt (absPins pk) (absRegion bs r) c)) := by
  rw [kinds_at]
  refine RS.vec_map (R := KindNamesRel)
    (loop := fun ar out i => kinds_at_loop pk pers ar bs r cs out i)
    (forall₂_of_map (A := fun v : Std.U64 => v.val) cs.val) ?_ ?_ (by simp) (by rfl)
  · intro ar out i hi
    show kinds_at_loop pk pers ar bs r cs out i = _
    rw [kinds_at_loop, ite_eq_right (by scalar_tac)]
  · intro i out x x' K Rf st lst hx hS hK
    cases hS
    show RS _ _ _ _ (kinds_at_loop pk pers st.store bs r cs out i) _
    rw [kinds_at_loop,
      ite_eq_left (by have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)]
    refine RS.pure_step fun y hy => ?_
    have hy3 := ConRon.Refine.ExprOps.vec_index_getElem? hy
    rw [hx] at hy3
    cases Option.some.inj hy3
    refine RS.bindT (kind_names_at_refines hr) (fun _ _ => by rfl) fun a b s1 lst1 hR =>
      RS.pure_step fun out1 ho => RS.pure_step fun i3 hi3 => ?_
    exact hK a b s1 lst1 out1 i3 hR (ConRon.Refine.vec_push_val ho) (uscalar_add_eq hi3)

/-! ## Off a view -/

/-- **`read_kinds` is `readKinds`.** -/
theorem read_kinds_refines {pk pers st lst} {f : frontend.olean.view.ModFiles}
    {f' : ConLeche.Frontend.Olean.ModFiles} (hf : ModFilesRel f f')
    {level : frontend.olean.view.OLeanLevel} {cs : alloc.vec.Vec Std.U64} :
    RS pers (fun v l => List.Forall₂ KindNamesRel v.val l) st lst
      (read_kinds pk pers st.store f level cs)
      (readKinds (absPins pk) f' (absLevel level) (cs.val.map (·.val))) := by
  rw [read_kinds, readKinds]
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
    exact kinds_at_refines hfit st lst

end ConRon.Refine2.Frontend.Olean

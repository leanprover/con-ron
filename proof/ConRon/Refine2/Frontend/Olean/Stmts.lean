/-
# `ConRon.Refine2.Frontend.Olean.Stmts` — the statements of some constants, read together

**Task #166, Theorem 2.**  `fast.rs`'s `stmts_roots`, `run_passes`, `stmts_read`, `stmts_fast`,
`reads.rs`'s `stmts_at` and `view.rs`'s `read_stmts` against the twin's `runPasses`,
`stmtsFast`, `stmtsAt`, `readStmts` (`RS`).  The twin reads the statements back out of the memo
in `Option`; `liftO` lifts that to `OptionT AM`, where the Rust's loop is `List.mapM`.
-/
import ConRon.Refine2.Frontend.Olean.FastMany
import ConRon.Refine2.Frontend.Olean.NamePos

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.fast (stmts_roots stmts_roots_loop run_passes stmts_read stmts_read_loop
  stmts_fast consts_skel)
open frontend.olean.reads (stmts_at)
open frontend.olean.view (read_stmts)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConRon.Refine.HashMap (uscalar_add_eq)
open ConLeche.Frontend.Olean (CEntryF)
open Arena.Frontend.Olean (runPasses stmtsFast stmtsAt readStmts constsSkel)

/-! ## `Option` in `OptionT AM` -/

/-- A pure `Option`, at `OptionT AM`. -/
def liftO {α : Type} (o : Option α) : OptionT AM α := OptionT.mk (pure o)

theorem liftO_mapM {α β : Type} (f : α → Option β) :
    ∀ l : List α, (l.mapM (m := OptionT AM) fun x => liftO (f x)) = liftO (l.mapM f)
  | [] => rfl
  | x :: xs => by
    rw [List.mapM_cons, List.mapM_cons, liftO_mapM f xs]
    cases f x with
    | none => rfl
    | some y =>
      show (liftO (some y) >>= fun a => liftO (xs.mapM f) >>= fun bs => pure (a :: bs)) = _
      cases xs.mapM f <;> rfl

/-! ## The roots -/

/-- **`stmts_roots`' names and expressions**: each skeleton's name and level parameters, and
its type. -/
theorem stmts_roots_val {sks : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {names exprs : alloc.vec.Vec Std.U64} (h : stmts_roots sks = ok (names, exprs)) :
    names.val = sks.val.flatMap (fun c => c.name :: c.level_params.val) ∧
      exprs.val = sks.val.map (·.ty) := by
  rw [stmts_roots] at h
  have hstep : ∀ (s : alloc.vec.Vec Std.U64 × alloc.vec.Vec Std.U64) (i : Std.Usize) o,
      stmts_roots_loop sks s.1 s.2 i = ok o → (sks.val.length ≤ i.val ∧ o = s) ∨
        ∃ (x : frontend.olean.spec.CEntryF Std.U64 Std.U64) (s1 : alloc.vec.Vec Std.U64 × alloc.vec.Vec Std.U64) (i1 : Std.Usize), sks.val[i.val]? = some x ∧
          (s1.1.val = s.1.val ++ (x.name :: x.level_params.val) ∧ s1.2.val = s.2.val ++ [x.ty]) ∧
          i1.val = i.val + 1 ∧ stmts_roots_loop sks s1.1 s1.2 i1 = ok o := by
    intro s i o h
    rw [stmts_roots_loop] at h
    by_cases hi : i < alloc.vec.Vec.len sks
    · right
      rw [ite_eq_left hi] at h
      peel h as x, hx
      peel h as n1, hn1
      peel h as n2, hn2
      peel h as e1, he1
      peel h as i1, hi1
      refine ⟨x, (n2, e1), i1, ConRon.Refine.ExprOps.vec_index_getElem? hx, ⟨?_, ?_⟩,
        uscalar_add_eq hi1, h⟩
      · rw [push_all_val hn2, ConRon.Refine.vec_push_val hn1]; simp
      · exact ConRon.Refine.vec_push_val he1
    · left
      rw [ite_eq_right hi] at h
      exact ⟨by scalar_tac, (Result.ok_injective h).symm⟩
  have e1 := append_loop0 (src := sks.val) (Ab := fun s : alloc.vec.Vec Std.U64 × alloc.vec.Vec Std.U64 => s.1.val)
    (f := fun x => x.name :: x.level_params.val)
    (loop := fun s i => stmts_roots_loop sks s.1 s.2 i)
    (fun s i o h => (hstep s i o h).imp id fun ⟨x, s1, i1, hx, ⟨h1, _⟩, hi, hl⟩ => ⟨x, s1, i1, hx, h1, hi, hl⟩)
    (s := (alloc.vec.Vec.new Std.U64, alloc.vec.Vec.with_capacity Std.U64 (alloc.vec.Vec.len sks)))
    (o := (names, exprs)) h
  have e2 := append_loop0 (src := sks.val) (Ab := fun s : alloc.vec.Vec Std.U64 × alloc.vec.Vec Std.U64 => s.2.val)
    (f := fun x => [x.ty])
    (loop := fun s i => stmts_roots_loop sks s.1 s.2 i)
    (fun s i o h => (hstep s i o h).imp id fun ⟨x, s1, i1, hx, ⟨_, h2⟩, hi, hl⟩ => ⟨x, s1, i1, hx, h2, hi, hl⟩)
    (s := (alloc.vec.Vec.new Std.U64, alloc.vec.Vec.with_capacity Std.U64 (alloc.vec.Vec.len sks)))
    (o := (names, exprs)) h
  refine ⟨by simpa using e1, ?_⟩
  simpa [flatMap_single] using e2

/-- The roots, as the twin's. -/
theorem stmts_roots_abs {sks : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {l : List (CEntryF UInt64 UInt64)} (hl : List.Forall₂ EV sks.val l)
    {names exprs : alloc.vec.Vec Std.U64} (h : stmts_roots sks = ok (names, exprs)) :
    names.val.map absWord = l.flatMap (fun s => s.name :: s.levelParams) ∧
      exprs.val.map absWord = l.map (·.type) := by
  obtain ⟨e1, e2⟩ := stmts_roots_val h
  rw [e1, e2]
  clear e1 e2 h
  generalize sks.val = L at hl ⊢
  induction hl with
  | nil => exact ⟨rfl, rfl⟩
  | @cons a b xs ys hab _ ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨?_, ?_⟩
    · simp only [List.flatMap_cons, List.map_append, List.map_cons, ih1, hab.«name»,
        ← hab.levelParams, List.cons_append]
    · simp only [List.map_cons, ih2, hab.type]

/-! ## The passes, and the statements read back -/

/-- **`run_passes` is `runPasses`.** -/
theorem run_passes_refines {pk bs r pers st lst} {names exprs : alloc.vec.Vec Std.U64}
    (hr : RegionFits bs r) :
    RS pers DSRel st lst (run_passes pk pers st.store bs r names exprs)
      (runPasses (absPins pk) (absRegion bs r) (names.val.map absWord) (exprs.val.map absWord)) := by
  rw [run_passes, runPasses]
  refine RS.bind_of (run_marked_refines hr) (fun _ _ => rfl) rfl fun a b s1 lst1 hR => ?_
  obtain ⟨n, m, d⟩ := a
  obtain ⟨n', m', d'⟩ := b
  exact RS.some hR.2.2.2

/-- One statement, read back out of the memo. -/
def stmtOf (pk : Arena.Frontend.Olean.OleanPins) (r : ConLeche.Frontend.Olean.Region)
    (st : TDS) (s : CEntryF UInt64 UInt64) : Option Arena.Frontend.Olean.StmtRec := do
  pure ⟨← st.nameOf pk r s.name, ← s.levelParams.mapM (st.nameOf pk r), ← st.exprOf r s.type⟩

/-- `stmtOf` at `OptionT AM`, read by read. -/
theorem liftO_stmtOf (pk : Arena.Frontend.Olean.OleanPins) (r : ConLeche.Frontend.Olean.Region)
    (st : TDS) (s : CEntryF UInt64 UInt64) :
    liftO (stmtOf pk r st s) =
      (OptionT.mk ((Arena.Frontend.Olean.DS.read pk r st).rdName s.name) >>= fun n =>
        (s.levelParams.mapM (m := OptionT AM) fun v =>
          OptionT.mk ((Arena.Frontend.Olean.DS.read pk r st).rdName v)) >>= fun lps =>
        OptionT.mk ((Arena.Frontend.Olean.DS.read pk r st).rdExpr s.type) >>= fun t =>
        pure (⟨n, lps, t⟩ : Arena.Frontend.Olean.StmtRec) : OptionT AM _) := by
  have e := liftO_mapM (st.nameOf pk r) s.levelParams
  simp only [liftO] at e
  show _ = (OptionT.mk (pure (st.nameOf pk r s.name)) >>= fun n =>
        (s.levelParams.mapM (m := OptionT AM) fun v => OptionT.mk (pure (st.nameOf pk r v))) >>= fun lps =>
        OptionT.mk (pure (st.exprOf r s.type)) >>= fun t =>
          pure (⟨n, lps, t⟩ : Arena.Frontend.Olean.StmtRec) : OptionT AM _)
  rw [e, stmtOf]
  cases st.nameOf pk r s.name <;> cases s.levelParams.mapM (st.nameOf pk r) <;>
    cases st.exprOf r s.type <;> rfl

/-- **`stmts_read` reads the statements back**: the twin's `sks.mapM` of `stmtOf`. -/
theorem stmts_read_refines {pk bs r pers} {d : frontend.olean.fast.DS} {t : TDS}
    (hr : RegionFits bs r) (hd : DSRel d t)
    {sks : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {l : List (CEntryF UInt64 UInt64)} (hl : List.Forall₂ EV sks.val l) (st lst) :
    RS pers (fun v l' => List.Forall₂ (EqA absStmtRec) v.val l') st lst
      (stmts_read d pk pers st.store bs r sks)
      (l.mapM (m := OptionT AM) fun s => liftO (stmtOf (absPins pk) (absRegion bs r) t s)) := by
  have hp := ds_ptr_rel (pk := pk) (pers := pers) hr hd
  rw [stmts_read]
  refine RS.vec_map (R := EqA absStmtRec)
    (loop := fun ar out i => stmts_read_loop d pk pers ar bs r sks out i)
    hl ?_ ?_ (by simp) (by rfl)
  · intro ar out i hi
    show stmts_read_loop d pk pers ar bs r sks out i = _
    rw [stmts_read_loop, ite_eq_right (by scalar_tac)]
  · intro i out x x' K Rf st lst hx hS hK
    show RS _ _ _ _ (stmts_read_loop d pk pers st.store bs r sks out i) _
    rw [stmts_read_loop,
      ite_eq_left (by have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)]
    refine RS.pure_step fun y hy => ?_
    have hy3 := ConRon.Refine.ExprOps.vec_index_getElem? hy
    rw [hx] at hy3
    cases Option.some.inj hy3
    rw [liftO_stmtOf, ← hS.«name», ← hS.type]
    simp only [bind_assoc, pure_bind]
    refine RS.bindT (hp.nm st lst x.name) (fun _ _ => by rfl) fun a b s1 lst1 hR =>
      RS.bindT (names_map_refines hp hS.levelParams (withStore st s1) lst1) (fun _ _ => by rfl)
        fun a2 b2 s2 lst2 hR2 => RS.bindT (hp.ex (withStore (withStore st s1) s2) lst2 x.ty)
          (fun _ _ => by rfl) fun a3 b3 s3 lst3 hR3 =>
            RS.pure_step fun out1 ho => RS.pure_step fun i3 hi3 => ?_
    cases hR; cases hR3
    have e : b2 = a2.val.map absNIdx := hR2.symm
    subst e
    exact hK _ _ s3 lst3 out1 i3 rfl (ConRon.Refine.vec_push_val ho) (uscalar_add_eq hi3)

/-- **`stmts_fast` is `stmtsFast`.** -/
theorem stmts_fast_refines {pk bs r pers st lst}
    {sks : alloc.vec.Vec (frontend.olean.spec.CEntryF Std.U64 Std.U64)}
    {l : List (CEntryF UInt64 UInt64)} (hr : RegionFits bs r) (hl : List.Forall₂ EV sks.val l) :
    RS pers (fun v l' => List.Forall₂ (EqA absStmtRec) v.val l') st lst
      (stmts_fast pk pers st.store bs r sks) (stmtsFast (absPins pk) (absRegion bs r) l) := by
  rw [stmts_fast, stmtsFast]
  refine RS.pure_step fun p hp => ?_
  obtain ⟨names, exprs⟩ := p
  obtain ⟨e1, e2⟩ := stmts_roots_abs hl hp
  rw [← e1, ← e2]
  refine RS.bind_of (run_passes_refines hr) (fun _ _ => rfl) rfl fun d t s1 lst1 hd => ?_
  have h := stmts_read_refines (pk := pk) (pers := pers) hr hd hl (withStore st s1) lst1
  rw [liftO_mapM] at h
  exact h

/-- **`stmts_at` is `stmtsAt`.** -/
theorem stmts_at_refines {pk bs r pers st lst} {cs : alloc.vec.Vec Std.U64} (hr : RegionFits bs r) :
    RS pers (fun v l' => List.Forall₂ (EqA absStmtRec) v.val l') st lst
      (stmts_at pk pers st.store bs r cs) (stmtsAt (absPins pk) (absRegion bs r) (cs.val.map (·.val))) := by
  rw [stmts_at, stmtsAt]
  intro hrel hinv o s' hm
  obtain ⟨r1, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have hP := consts_skel_ps (bs := bs) (r := r) (consts := cs) rfl r1 h1 lst
  cases r1 with
  | Ok sks =>
    obtain ⟨l, hx, hR⟩ := hP
    rw [am_bind_ok hx]
    exact stmts_fast_refines hr hR hrel hinv o s' h2
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

/-- **`read_stmts` is `readStmts`.** -/
theorem read_stmts_refines {pk pers st lst} {f : frontend.olean.view.ModFiles}
    {f' : ConLeche.Frontend.Olean.ModFiles} (hf : ModFilesRel f f')
    {level : frontend.olean.view.OLeanLevel} {cs : alloc.vec.Vec Std.U64} :
    RS pers (fun v l' => List.Forall₂ (EqA absStmtRec) v.val l') st lst
      (read_stmts pk pers st.store f level cs)
      (readStmts (absPins pk) f' (absLevel level) (cs.val.map (·.val))) := by
  rw [read_stmts, readStmts]
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
    exact stmts_at_refines hfit

end ConRon.Refine2.Frontend.Olean

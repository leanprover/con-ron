/-
# `ConRon.Refine2.Frontend.Olean.Present` — `olean/present.rs` against `Arena/Frontend/Olean/Present.lean`

**Task #166, Theorem 2.**  `entry_with`, `stmt_roots`, `stmt_with`: a read with the part's memo,
which the twin threads through its answer (`AM (SM × Option β)`) and the Rust through `&mut`.
`MRS` is `RS` with the memos related by `SMRel` in every outcome but a thrown error.
`record_of_entry` claims its accept: the records' error channel (`SimStreamRel`) admits the scan's
overflow, which no twin run mirrors.
-/
import ConRon.Refine2.Frontend.Olean.ReadsMemo
import ConRon.Refine2.Frontend.Olean.EmitWalk
import ConRon.Refine2.Frontend.Olean.Records
import ConRon.Refine2.Frontend.Olean.Files

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.present (entry_with stmt_roots stmt_with record_of_entry)
open frontend.olean.fast (K_NAME K_EXPR)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open ConLeche.Frontend.Olean (CEntryF CKindF)
open Arena.Frontend.Olean (entryWith stmtWith memoAdd memoAddAll memoRoots memoRead entryMap
  kindNames recordOfEntry)

/-! ## `MRS`: a read with the part's memo -/

/-- **The lockstep judgement of a read with the part's memo.** -/
def MRS {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop) (st : arena.monad.AState)
    (lst : AState)
    (m : Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore ×
      frontend.olean.sparse.SM)) (x : AM (TSM × Option β)) : Prop :=
  AStateRel₀ pers st lst → AStateInv pers st → ∀ o s' d', m = ok (o, s', d') →
    match o with
    | .Ok a => ∃ t b lst', x.run lst = .ok ((t, some b), lst') ∧ R a b ∧ SMRel d' t ∧
        AStateRel₀ pers (withStore st s') lst' ∧ AStateInv pers (withStore st s')
    | .Err .Bad => ∃ t lst', x.run lst = .ok ((t, none), lst') ∧ SMRel d' t ∧
        AStateRel₀ pers (withStore st s') lst' ∧ AStateInv pers (withStore st s')
    | .Err (.Err e) => AErrSim e (x.run lst)

theorem MRS.pure_step {α β γ : Type} {pers} {R : α → β → Prop} {st lst} {f : Result γ} {k}
    {x : AM (TSM × Option β)} (h : ∀ a, f = ok a → MRS pers R st lst (k a) x) :
    MRS pers R st lst (Std.bind f k) x := by
  intro hrel hinv o s' d' hm
  obtain ⟨a, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact h a h1 hrel hinv o s' d' h2

/-- A read whose memo is `d`, then the twin's pair. -/
theorem MRS.of_rs {α β : Type} {pers} {R : α → β → Prop} {st lst}
    {f : Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore)}
    {k : core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore →
      Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore ×
        frontend.olean.sparse.SM)}
    {y : AM (Option β)} {d : frontend.olean.sparse.SM} {t : TSM}
    (hf : RS pers R st lst f y) (hd : SMRel d t) (hk : ∀ o s, k (o, s) = ok (o, s, d)) :
    MRS pers R st lst (Std.bind f k) (y >>= fun r' => pure (t, r')) := by
  intro hrel hinv o s' d' hm
  obtain ⟨⟨r1, s1⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  rw [hk] at h2
  have hF := hf hrel hinv r1 s1 h1
  simp only [ok.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  cases r1 with
  | Ok a =>
    obtain ⟨b, lst1, hx, hR, h3, h4⟩ := hF
    rw [am_bind_ok hx]
    exact ⟨t, b, lst1, rfl, hR, hd, h3, h4⟩
  | Err e =>
    cases e with
    | Bad =>
      obtain ⟨lst1, hx, h3, h4⟩ := hF
      rw [am_bind_ok hx]
      exact ⟨t, lst1, rfl, hd, h3, h4⟩
    | Err e =>
      show AErrSim e _
      rw [StateT.run_bind]
      exact AErrSim.bind hF _

/-- **A read, then the rest**, the memo `d` held: the twin's at `OptionT AM`. -/
theorem MRS.bindT {α₁ β₁ α β : Type} {pers} {R₁ : α₁ → β₁ → Prop} {R : α → β → Prop} {st lst}
    {f : Result (core.result.Result α₁ frontend.olean.spec.RdErr × arena.store.EStore)}
    {k : core.result.Result α₁ frontend.olean.spec.RdErr × arena.store.EStore →
      Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore ×
        frontend.olean.sparse.SM)}
    {x : OptionT AM β₁} {g : β₁ → OptionT AM β} {d : frontend.olean.sparse.SM} {t : TSM}
    (hd : SMRel d t) (hf : RS pers R₁ st lst f x)
    (he : ∀ e s1, k (.Err e, s1) = ok (.Err e, s1, d))
    (hk : ∀ a b s1 lst1, R₁ a b →
      MRS pers R (withStore st s1) lst1 (k (.Ok a, s1)) ((g b : AM (Option β)) >>= fun r' => pure (t, r'))) :
    MRS pers R st lst (Std.bind f k) (((x >>= g : OptionT AM β) : AM (Option β)) >>= fun r' => pure (t, r')) := by
  intro hrel hinv o s' d' hm
  obtain ⟨⟨r1, s1⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have hF := hf hrel hinv r1 s1 h1
  rw [optionT_bind_eq, bind_assoc]
  cases r1 with
  | Ok a =>
    obtain ⟨b, lst1, hx, hR, h3, h4⟩ := hF
    rw [am_bind_ok hx]
    exact hk a b s1 lst1 hR h3 h4 o s' d' h2
  | Err e =>
    rw [he] at h2
    cases Result.ok_injective h2
    cases e with
    | Bad =>
      obtain ⟨lst1, hx, h3, h4⟩ := hF
      rw [am_bind_ok hx]
      exact ⟨t, lst1, rfl, hd, h3, h4⟩
    | Err e =>
      show AErrSim e _
      rw [StateT.run_bind]
      exact AErrSim.bind hF _

/-- The last read's answer. -/
theorem MRS.some {α β : Type} {pers} {R : α → β → Prop} {st lst} {a : α} {b : β}
    {d : frontend.olean.sparse.SM} {t : TSM} (hR : R a b) (hd : SMRel d t) :
    MRS pers R st lst (ok (.Ok a, st.store, d))
      (((pure b : OptionT AM β) : AM (Option β)) >>= fun r' => pure (t, r')) := by
  intro hrel hinv o s' d' hm
  cases Result.ok_injective hm
  exact ⟨t, b, lst, rfl, hR, hd, hrel, hinv⟩

/-- **A step that grows the memo, then the rest.** -/
theorem MRS.memo {α β : Type} {pers} {R : α → β → Prop} {st lst} {f} {x : AM TSM}
    {g : TSM → AM (TSM × Option β)}
    {KR : arena.store.EStore → frontend.olean.sparse.SM →
      Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore ×
        frontend.olean.sparse.SM)}
    (hf : MemoS pers st lst f x)
    (hk : ∀ s1 d1 t1 lst1, SMRel d1 t1 → MRS pers R (withStore st s1) lst1 (KR s1 d1) (g t1)) :
    MRS pers R st lst
      (do
        let (r2, ar1, st1) ← f
        match r2 with
        | .Ok _ => KR ar1 st1
        | .Err e => ok (.Err (.Err e), ar1, st1))
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

/-- **A skeleton read, its numbers checked, then `k`**, the memo `d` held where it declines. -/
theorem MRS.skel {α β : Type} {bs r pers st lst} {c : Std.U64} {R : α → β → Prop}
    {d : frontend.olean.sparse.SM} {t : TSM} (hd : SMRel d t)
    {k : frontend.olean.spec.CEntryF Std.U64 Std.U64 →
      Result (core.result.Result α frontend.olean.spec.RdErr × arena.store.EStore ×
        frontend.olean.sparse.SM)}
    {K : CEntryF UInt64 UInt64 → AM (TSM × Option β)}
    (hk : ∀ s s', EV s s' → MRS pers R st lst (k s) (K s')) :
    MRS pers R st lst (do
        let o ← frontend.olean.spec.const_skel bs r c
        match o with
        | Option.none => ok (core.result.Result.Err frontend.olean.spec.RdErr.Bad, st.store, d)
        | Option.some s =>
          let r1 ← frontend.olean.spec.skel_fits s
          match r1 with
          | core.result.Result.Ok _ => k s
          | core.result.Result.Err e => ok (core.result.Result.Err e, st.store, d))
      (match ConLeche.Frontend.Olean.constSkel (absRegion bs r) c.val with
        | Option.none => pure (t, Option.none)
        | Option.some s => do
          Arena.Frontend.Olean.skelFits s
          K s) := by
  refine MRS.pure_step fun o ho => ?_
  refine sat_elim (const_skel_eq (bs := bs) (r := r) ho) (fun hA hy => ?_)
    (fun s s' hA hy hS => ?_)
  · subst hA
    rw [hy]
    intro hrel hinv o s' d' hm
    cases Result.ok_injective hm
    exact ⟨t, lst, rfl, hd, hrel, hinv⟩
  · subst hA
    rw [hy]
    intro hrel hinv o1 s1 d1 hm
    obtain ⟨r1, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
    have hF := skel_fits_refines hS h1 (lst := lst)
    cases r1 with
    | Ok u =>
      obtain ⟨hrun, hEV⟩ := hF
      dsimp only
      rw [am_bind_ok hrun]
      exact hk s s' hEV hrel hinv o1 s1 d1 h2
    | Err e =>
      cases Result.ok_injective h2
      cases e with
      | Bad => exact hF.elim
      | Err e =>
        show AErrSim e _
        rw [StateT.run_bind]
        exact AErrSim.bind hF _

/-! ## The reads -/

/-- **`entry_with` is `entryWith`.** -/
theorem entry_with_refines {pk bs r pers st lst} {d : frontend.olean.sparse.SM} {t : TSM}
    {c : Std.U64} (hr : RegionFits bs r) (hd : SMRel d t) :
    MRS pers (EntryRel absNIdx absEIdx ValRel) st lst (entry_with pk pers st.store bs r d c)
      (entryWith (absPins pk) (absRegion bs r) t c.val) := by
  rw [entry_with, entryWith]
  refine MRS.skel hd fun s s' hs => ?_
  refine MRS.memo (memo_roots_refines hr hd hs) fun s1 d1 t1 lst1 h1 => ?_
  exact MRS.of_rs (c_entry_map_refines (memo_read_rel hr h1) hs _ lst1) h1 (fun _ _ => rfl)

/-- **`stmt_roots` is the twin's two memo steps**: the name and the level parameters, then the
type. -/
theorem stmt_roots_refines {pk bs r pers st lst} {d : frontend.olean.sparse.SM} {t : TSM}
    {sk : frontend.olean.spec.CEntryF Std.U64 Std.U64} {sk' : CEntryF UInt64 UInt64}
    (hr : RegionFits bs r) (hd : SMRel d t) (hs : EV sk sk') :
    MemoS pers st lst (stmt_roots pk pers st.store bs r d sk)
      (memoAddAll (absPins pk) (absRegion bs r) ConLeche.Frontend.Olean.kName t
          (sk'.name :: sk'.levelParams) >>= fun st =>
        memoAdd (absPins pk) (absRegion bs r) ConLeche.Frontend.Olean.kExpr st sk'.type) := by
  rw [stmt_roots]
  refine MemoS.pure_step fun i1 hi1 => MemoS.pure_step fun n1 hn1 => MemoS.pure_step fun n2 hn2 => ?_
  have en : n2.val.map absWord = sk'.name :: sk'.levelParams := by
    rw [push_all_val hn2, ConRon.Refine.vec_push_val hn1]
    simp only [alloc.vec.Vec.with_capacity, List.map_append, List.map_cons]
    rw [hs.«name», show List.map absWord sk.level_params.val = sk'.levelParams from hs.levelParams]
    rfl
  rw [← en, ← absByte_k_name, ← absByte_k_expr, ← hs.type]
  exact MemoS.bind (memo_add_all_refines hr hd) fun s1 d1 t1 lst1 h1 => memo_add_refines hr h1

/-- A statement and a kind's names, against the twin's. -/
def StmtKindRel (a : frontend.olean.spec.StmtRec × frontend.olean.spec.CKindF arena.handle.NIdx Unit)
    (b : Arena.Frontend.Olean.StmtRec × CKindF NIdx Unit) : Prop :=
  b.1 = absStmtRec a.1 ∧ KindNamesRel a.2 b.2

/-- **`stmt_with` is `stmtWith`.** -/
theorem stmt_with_refines {pk bs r pers st lst} {d : frontend.olean.sparse.SM} {t : TSM}
    {c : Std.U64} (hr : RegionFits bs r) (hd : SMRel d t) :
    MRS pers StmtKindRel st lst (stmt_with pk pers st.store bs r d c)
      (stmtWith (absPins pk) (absRegion bs r) t c.val) := by
  rw [stmt_with, stmtWith]
  refine MRS.skel hd fun s s' hs => ?_
  simp only [← bind_assoc]
  refine MRS.memo (stmt_roots_refines hr hd hs) fun s1 d1 t1 lst1 h1 => ?_
  have hp := memo_read_rel (pk := pk) (pers := pers) hr h1
  rw [← hs.«name», ← hs.type]
  refine MRS.bindT h1 (memo_name_refines hr h1) (fun _ _ => rfl) fun a b s2 lst2 hR => ?_
  refine MRS.bindT h1 (names_map_refines hp hs.levelParams _ lst2) (fun _ _ => rfl)
    fun a2 b2 s3 lst3 hR2 => ?_
  refine MRS.bindT h1 (memo_expr_refines hr h1) (fun _ _ => rfl) fun a3 b3 s4 lst4 hR3 => ?_
  refine MRS.bindT h1 (c_kind_names_refines hp hs.kind _ lst4) (fun _ _ => rfl)
    fun a4 b4 s5 lst5 hR4 => ?_
  cases hR; cases hR3
  have e : b2 = a2.val.map absNIdx := hR2.symm
  subst e
  exact MRS.some ⟨rfl, hR4⟩ h1

/-! ## A constant's record -/

/-- **`record_of_entry`'s accept is `recordOfEntry`.** -/
theorem record_of_entry_ok {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {c : frontend.olean.spec.CEntryF arena.handle.NIdx arena.handle.EIdx} {c' : CEntryF NIdx EIdx}
    (hc : EntryRel absNIdx absEIdx ValRel c c') {d : arena.env.IDeclaration}
    (h : record_of_entry pers st.store c = ok (.Ok d)) :
    ∃ lst', (recordOfEntry c').run lst = .ok (absIDeclaration d, lst') ∧
      AStateRel₀ pers st lst' ∧ AStateInv pers st := by
  rw [record_of_entry] at h
  peel h as hm, hhm
  peel h as nm, -
  peel h as em, hem
  have he := emit_one_rel (emit_new_rel hhm) (c' := { c := c' }) ⟨hc, by simp [alloc.vec.Vec.new]⟩ hem
  peel h as r, hr
  have hD := decls_of_rel hrel hinv he hr
  cases r with
  | Err p => cases Result.ok_injective h
  | Ok pr =>
    obtain ⟨v, lst', hx, hv, hrel', hinv'⟩ := hD
    dsimp only at h
    by_cases hl : alloc.vec.Vec.len pr.decls = 1#usize
    · rw [ite_eq_left hl] at h
      peel h as i1, hi1
      peel h as i2, hi2
      cases Result.ok_injective h
      refine ⟨lst', ?_, hrel', hinv'⟩
      have hl' : pr.decls.val.length = 1 := by
        have := congrArg UScalar.val hl
        simpa [alloc.vec.Vec.len] using this
      obtain ⟨x, hx1⟩ := List.length_eq_one_iff.mp hl'
      have hi := ConRon.Refine.ExprOps.vec_index_getElem? hi1
      rw [hx1] at hi
      cases (by simpa using hi : x = i1)
      have ev : v.decls.toList = [absIDeclaration i1] := by
        rw [hv.decls, absIDeclArr, hx1]; rfl
      rw [recordOfEntry, am_bind_ok hx]
      simp only [ev, i_declaration_dup_abs hi2]
      rfl
    · rw [ite_eq_right hl] at h
      exact absurd h (not_ok_of_err (by err_any))

end ConRon.Refine2.Frontend.Olean

/-
# `ConRon.Refine2.Frontend.Text` — two string builders and the store readback

**Task #97-T2-LOCKSTEP lane Frontend.**  `text::cat` and `text::u64_str` are
pure; the frontend's one place they are not a MESSAGE is `proj_iota_name`,
where `"proj_" ++ toString i` is a NAME component and is therefore compared.
Ported from `RefineOld/Frontend/ProjRecR.lean` / `ProjRec.lean` (task #87),
which proved the same two functions for the `Expr`-tree port: the functions
are untouched since (`crates/con-ron-core/src/frontend/text.rs`).

The second half is `arena::env::read_name` / `read_names` — the readback the
frontend's MESSAGES and its `pw` datum use (`show_name`, `parse_pw_d`,
`prepare`).  The monad-level `read_name` has its `Specs.lean` lemma; this
EStore-level twin of the same `denoteN` (fuel `node_count + 1`, the same
algorithm) had none.

## `sorry` count in this file: 0
-/
import ConRon.Refine2.Frontend.Abs

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend

open ConRon.Arena
open ConRon.Arena.Frontend

/-! ## `arena::env::read_name` — `denoteN` over a bare store -/

theorem env_dangling_name_kind {ce : kernel.core_types.CheckError}
    (h : arena.env.dangling_name = ok ce) : absAErrKind ce = some .internal := by
  rw [arena.env.dangling_name] at h
  simp only [lift, bind_tc_ok] at h
  obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [kernel.core_types.internal] at h
  cases Result.ok_injective h
  rfl

theorem env_read_name_at_abs {pers : arena.store.PersTier} {ar : arena.store.EStore}
    {ls : NStore} (hrel : NStoreRel pers ar.lss.ls.ns ls) :
    ∀ (n : Nat) (fuel : Std.U64) (i : arena.handle.NIdx) {o}, fuel.val = n →
      arena.env.read_name_at pers ar fuel i = ok o →
      match denoteNAux ls n (absNIdx i) with
      | some x => ∃ y, o = .Ok y ∧ ConRon.Refine.absName y = x
      | none => ∃ e, o = .Err e ∧ absAErrKind e = some .internal := by
  intro n
  induction n with
  | zero =>
    intro fuel i o hn hrun
    rw [arena.env.read_name_at, if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) :
      fuel = 0#u64)] at hrun
    obtain ⟨ce, hce, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases Result.ok_injective hrun
    exact ⟨ce, rfl, env_dangling_name_kind hce⟩
  | succ k ih =>
    intro fuel i o hn hrun
    rw [arena.env.read_name_at, if_neg (by intro hc; rw [hc] at hn; simp at hn)] at hrun
    obtain ⟨ns, hns, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.store.EStore.ns] at hns
    cases Result.ok_injective hns
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hview := nstore_view_abs hrel hv
    rw [denoteNAux, hview]
    cases v with
    | none =>
      obtain ⟨ce, hce, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases Result.ok_injective hrun
      exact ⟨ce, rfl, env_dangling_name_kind hce⟩
    | some nv =>
      cases nv with
      | Anonymous =>
        obtain ⟨nm, hnm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        cases Result.ok_injective hrun
        exact ⟨nm, rfl, ConRon.Refine.Name.anonymous_refines hnm⟩
      | Str p s =>
        obtain ⟨f1, hf1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hf1v : f1.val = k := by
          have h1 : f1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hf1).2
          rw [h1, hn]; rfl
        obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hih := ih f1 p hf1v hr
        simp only [Option.map_some, Option.bind_some, absNNodeView]
        cases hd : denoteNAux ls k (absNIdx p) with
        | none =>
          rw [hd] at hih
          obtain ⟨e, rfl, hek⟩ := hih
          cases Result.ok_injective hrun
          simp only [Option.map_none]
          exact ⟨e, rfl, hek⟩
        | some q =>
          rw [hd] at hih
          obtain ⟨y, rfl, hy⟩ := hih
          obtain ⟨nm, hnm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          cases Result.ok_injective hrun
          simp only [Option.map_some]
          refine ⟨nm, rfl, ?_⟩
          rw [ConRon.Refine.Name.mk_str_refines hnm, hy]
      | Num p m =>
        obtain ⟨f1, hf1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hf1v : f1.val = k := by
          have h1 : f1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hf1).2
          rw [h1, hn]; rfl
        obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hih := ih f1 p hf1v hr
        simp only [Option.map_some, Option.bind_some, absNNodeView]
        cases hd : denoteNAux ls k (absNIdx p) with
        | none =>
          rw [hd] at hih
          obtain ⟨e, rfl, hek⟩ := hih
          cases Result.ok_injective hrun
          simp only [Option.map_none]
          exact ⟨e, rfl, hek⟩
        | some q =>
          rw [hd] at hih
          obtain ⟨y, rfl, hy⟩ := hih
          obtain ⟨nm, hnm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          cases Result.ok_injective hrun
          simp only [Option.map_some]
          refine ⟨nm, rfl, ?_⟩
          rw [ConRon.Refine.Name.mk_num_refines hnm, hy]

/-- `arena::env::read_name_at`'s names are well formed: the store's own
invariant (`nstore_view_wf`) carries the cached code points. -/
theorem env_read_name_at_wf {pers : arena.store.PersTier} {ar : arena.store.EStore}
    (hinv : NStoreInv pers ar.lss.ls.ns) :
    ∀ (n : Nat) (fuel : Std.U64) (i : arena.handle.NIdx) {o}, fuel.val = n →
      arena.env.read_name_at pers ar fuel i = ok o →
      ∀ y, o = .Ok y → ConRon.Refine.NameWF y := by
  intro n
  induction n with
  | zero =>
    intro fuel i o hn hrun
    rw [arena.env.read_name_at, if_pos (Std.UScalar.eq_of_val_eq (by rw [hn]; rfl) :
      fuel = 0#u64)] at hrun
    obtain ⟨ce, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases Result.ok_injective hrun
    intro y hy; cases hy
  | succ k ih =>
    intro fuel i o hn hrun
    rw [arena.env.read_name_at, if_neg (by intro hc; rw [hc] at hn; simp at hn)] at hrun
    obtain ⟨ns, hns, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.store.EStore.ns] at hns
    cases Result.ok_injective hns
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hvw := nstore_view_wf hinv hv
    cases v with
    | none =>
      obtain ⟨ce, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      cases Result.ok_injective hrun
      intro y hy; cases hy
    | some nv =>
      have hnvw : NNodeViewWF nv := hvw nv rfl
      cases nv with
      | Anonymous =>
        obtain ⟨nm, hnm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        cases Result.ok_injective hrun
        intro y hy; cases hy
        exact ConRon.Refine.Name.anonymous_wf hnm
      | Str p s =>
        obtain ⟨f1, hf1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hf1v : f1.val = k := by
          have h1 : f1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hf1).2
          rw [h1, hn]; rfl
        obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hih := ih f1 p hf1v hr
        cases r with
        | Err e => cases Result.ok_injective hrun; intro y hy; cases hy
        | Ok q =>
          obtain ⟨nm, hnm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          cases Result.ok_injective hrun
          intro y hy; cases hy
          exact ConRon.Refine.Name.mk_str_wf (hih q rfl) hnvw hnm
      | Num p m =>
        obtain ⟨f1, hf1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hf1v : f1.val = k := by
          have h1 : f1.val = fuel.val - (1#u64 : Std.U64).val :=
            (ConRon.Refine.Nat.usub_val hf1).2
          rw [h1, hn]; rfl
        obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hih := ih f1 p hf1v hr
        cases r with
        | Err e => cases Result.ok_injective hrun; intro y hy; cases hy
        | Ok q =>
          obtain ⟨nm, hnm, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          cases Result.ok_injective hrun
          intro y hy; cases hy
          exact ConRon.Refine.Name.mk_num_wf (hih q rfl) hnm

theorem env_read_name_wf {pers : arena.store.PersTier} {ar : arena.store.EStore}
    (hinv : StoreInv pers ar) {h : arena.handle.NIdx} {o}
    (hrun : arena.env.read_name pers ar h = ok o) :
    ∀ y, o = .Ok y → ConRon.Refine.NameWF y := by
  rw [arena.env.read_name] at hrun
  obtain ⟨ns, hns, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.store.EStore.ns] at hns
  cases Result.ok_injective hns
  obtain ⟨c, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨c1, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨c2, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  exact env_read_name_at_wf hinv.lss.lvl.ns c2.val c2 h rfl hrun

/-- **`arena::env::read_name` is `denoteN`** (the twin's `readName`): the
same fuel, `node_count + 1`, and `Internal` exactly where the readback is
`none`. -/
theorem env_read_name_abs {pers : arena.store.PersTier} {ar : arena.store.EStore}
    {ls : EStore} (hrel : StoreRel pers ar ls) {h : arena.handle.NIdx} {o}
    (hrun : arena.env.read_name pers ar h = ok o) :
    match denoteN ls.ns (absNIdx h) with
    | some x => ∃ y, o = .Ok y ∧ ConRon.Refine.absName y = x
    | none => ∃ e, o = .Err e ∧ absAErrKind e = some .internal := by
  rw [arena.env.read_name] at hrun
  obtain ⟨ns, hns, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.store.EStore.ns] at hns
  cases Result.ok_injective hns
  obtain ⟨c, hc, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨c1, hc1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨c2, hc2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hnrel : NStoreRel pers ar.lss.ls.ns ls.ns := hrel.lss.lvl.ns
  have hcv := nstore_node_count_abs hnrel hc
  have hc1v : c1.val = c.val := by
    simp only [lift, Result.ok.injEq] at hc1
    rw [← hc1]; exact usize_cast_u64_val' c
  have hc2v : c2.val = ls.ns.nodeCount + 1 := by
    have := ConRon.Refine.Nat.uadd_val hc2
    rw [this, hc1v, hcv]; rfl
  rw [denoteN]
  exact env_read_name_at_abs hnrel _ c2 h hc2v hrun

/-- `arena::env::read_names_from`, at a cursor: `denoteNList` of the rest,
and every name read well formed. -/
theorem env_read_names_from_abs {pers : arena.store.PersTier} {ar : arena.store.EStore}
    {ls : EStore} (hrel : StoreRel pers ar ls) (hinv : StoreInv pers ar)
    {ks : alloc.vec.Vec arena.handle.NIdx} :
    ∀ k (i : Std.Usize) (out : alloc.vec.Vec kernel.name.Name),
      ks.length - i.val ≤ k → (∀ n ∈ out.val, ConRon.Refine.NameWF n) → ∀ {o},
      arena.env.read_names_from pers ar ks i out = ok o →
      match denoteNList ls.ns ((ks.val.drop i.val).map absNIdx) with
      | some xs => ∃ v, o = .Ok v ∧ v.val.map ConRon.Refine.absName
          = out.val.map ConRon.Refine.absName ++ xs ∧ ∀ n ∈ v.val, ConRon.Refine.NameWF n
      | none => ∃ e, o = .Err e ∧ absAErrKind e = some .internal := by
  intro k
  induction k with
  | zero =>
    intro i out hk hout o hrun
    rw [arena.env.read_names_from.eq_def] at hrun; simp only [] at hrun
    rw [if_pos (by scalar_tac)] at hrun
    rw [List.drop_eq_nil_of_le (by scalar_tac), List.map_nil]
    exact ⟨out, (Result.ok_injective hrun).symm, by simp, hout⟩
  | succ k ih =>
    intro i out hk hout o hrun
    rw [arena.env.read_names_from.eq_def] at hrun; simp only [] at hrun
    split at hrun
    · rw [List.drop_eq_nil_of_le (by scalar_tac), List.map_nil]
      exact ⟨out, (Result.ok_injective hrun).symm, by simp, hout⟩
    · rename_i hlt
      have hb : i.val < ks.length := by scalar_tac
      obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hnv : ks.val[i.val] = n := by
        have h1 : ks.val[i.val]? = some n := vec_index_some hn
        rw [List.getElem?_eq_getElem hb] at h1
        exact (Option.some.injEq _ _ ▸ h1)
      obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hra := env_read_name_abs hrel hr
      have hrw := env_read_name_wf hinv hr
      rw [List.drop_eq_getElem_cons hb, List.map_cons, denoteNList, hnv]
      cases hdn : denoteN ls.ns (absNIdx n) with
      | none =>
        rw [hdn] at hra
        obtain ⟨e, rfl, hek⟩ := hra
        simp only [opt2]
        exact ⟨e, (Result.ok_injective hrun).symm, hek⟩
      | some x =>
        rw [hdn] at hra
        obtain ⟨y, rfl, hy⟩ := hra
        obtain ⟨out1, hout1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := by
          have := ConRon.Refine.Nat.uadd_val hi2; simpa using this
        have hout1v : out1.val = out.val ++ [y] := ConRon.Refine.vec_push_val hout1
        have hih := ih i2 out1 (by scalar_tac) (by
          intro nn hnn
          rw [hout1v] at hnn
          rcases List.mem_append.mp hnn with hnn | hnn
          · exact hout nn hnn
          · rw [List.mem_singleton.mp hnn]; exact hrw y rfl) hrun
        rw [hi2v] at hih
        cases hdl : denoteNList ls.ns ((ks.val.drop (i.val + 1)).map absNIdx) with
        | none =>
          rw [hdl] at hih
          simp only [opt2]
          exact hih
        | some xs =>
          rw [hdl] at hih
          obtain ⟨v, rfl, hv, hvw⟩ := hih
          simp only [opt2]
          refine ⟨v, rfl, ?_, hvw⟩
          rw [hv, hout1v]
          simp only [List.map_append, List.map_cons, List.map_nil,
            List.append_assoc, List.cons_append, List.nil_append, hy]

/-- **`arena::env::read_names` is `denoteNList`**, its names well formed. -/
theorem env_read_names_abs {pers : arena.store.PersTier} {ar : arena.store.EStore}
    {ls : EStore} (hrel : StoreRel pers ar ls) (hinv : StoreInv pers ar)
    {ks : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.env.read_names pers ar ks = ok o) :
    match denoteNList ls.ns (ks.val.map absNIdx) with
    | some xs => ∃ v, o = .Ok v ∧ v.val.map ConRon.Refine.absName = xs ∧
        ∀ n ∈ v.val, ConRon.Refine.NameWF n
    | none => ∃ e, o = .Err e ∧ absAErrKind e = some .internal := by
  rw [arena.env.read_names] at hrun
  have hh := env_read_names_from_abs hrel hinv ks.length 0#usize _ (by scalar_tac)
    (by intro n hn; simp [alloc.vec.Vec.with_capacity] at hn) hrun
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hh
  cases hdl : denoteNList ls.ns (ks.val.map absNIdx) with
  | none => rw [hdl] at hh; exact hh
  | some xs =>
    rw [hdl] at hh
    obtain ⟨v, rfl, hv, hw⟩ := hh
    exact ⟨v, rfl, by simpa [alloc.vec.Vec.with_capacity] using hv, hw⟩

/-- The twin's `hs.mapM readName` is its `readNames hs`. -/
theorem mapM_readName_run_eq : ∀ (l : List NIdx) (lst : AState),
    (l.mapM readName).run lst = (Arena.readNames l).run lst
  | [], _ => rfl
  | h :: hs, lst => by
    rw [List.mapM_cons]
    show (do let x ← Arena.readName h; let xs ← hs.mapM readName; pure (x :: xs) : AM _).run lst
      = (do let x ← Arena.readName h; let xs ← Arena.readNames hs; pure (x :: xs) : AM _).run lst
    rw [am_run_bind', am_run_bind']
    cases (Arena.readName h).run lst with
    | error e => rfl
    | ok p =>
      show ((hs.mapM readName >>= fun xs => pure (p.1 :: xs)) : AM _).run p.2
        = ((Arena.readNames hs >>= fun xs => pure (p.1 :: xs)) : AM _).run p.2
      rw [am_run_bind', am_run_bind', mapM_readName_run_eq hs p.2]

/-- The twin's `hs.mapM readName` is `denoteNList`. -/
theorem mapM_readName_run (lst : AState) (l : List NIdx) :
    (l.mapM readName).run lst
      = match denoteNList lst.store.ns l with
        | some xs => Except.ok (xs, lst)
        | none => Except.error (.internal "arena: dangling name handle") := by
  rw [mapM_readName_run_eq]; exact readNames_run lst l

end ConRon.Refine2.Frontend

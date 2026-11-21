/-
# `ConRon.Refine2.Frontend.Compare` — `frontend/compare.rs` against `Arena/Frontend/Compare.lean`

**Task #165, Theorem 2.**  The name a record is found under (`rec_key_eq`), a theorem read as the
hole it is (`hole_record_ls`, `hole_records_ls`), the prelude's copy a compared run prepares its
second input with (`prelude_ix_dup_abs`), and the decision
whether a `--constant` name is no declaration of the challenge module (`foreign_constant_some`):
the Rust's answer is `Some` exactly where the twin's `foreignOf` is.  `rec_kind` and the text of
`foreign_constant`'s answer carry no theorem: they are messages, and a message is not compared.
-/
import ConRon.Refine2.Frontend.Olean.Contract
import ConRon.Refine2.Frontend.Olean.Emit
import ConRon.Refine2.Checker.Shape
import ConRon.Arena.Frontend.Compare
import ConRon.Refine2.Frontend.NatOpDeps
import ConRon.Refine2.Frontend.Prepare
import ConRon.Refine2.Frontend.NatOpGround
import ConRon.Refine2.Checker.Justify

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend

open ConRon.Arena
open ConRon.Refine2.Frontend.Olean (HomesRel not_lt_len lt_len usize_succ idx_cons)

/-- **`rec_key` is `recKey`.** -/
theorem rec_key_eq {d : arena.env.IDeclaration} {o : Option arena.handle.NIdx}
    (h : frontend.compare.rec_key d = ok o) :
    o.map absNIdx = ConRon.Arena.Frontend.recKey (absIDeclaration d) := by
  rw [frontend.compare.rec_key.eq_def] at h
  cases d with
  | AxiomDecl cv | DefnDecl cv _ _ | ThmDecl cv _ | OpaqueDecl cv _ | QuotDecl _ cv =>
    peel h as n, hn
    cases Result.ok_injective h
    rw [dupId_nidx _ _ hn]
    rfl
  | IndDecl b np =>
    simp only at h
    by_cases h0 : alloc.vec.Vec.len b = 0#usize
    · rw [ite_eq_left h0] at h
      cases Result.ok_injective h
      have he : b.val = [] := by
        have := congrArg UScalar.val h0
        simp only [alloc.vec.Vec.len] at this
        exact List.eq_nil_of_length_eq_zero (by simpa using this)
      simp [absIDeclaration, ConRon.Arena.Frontend.recKey, he]
    · rw [ite_eq_right h0] at h
      peel h as ii, hii
      peel h as n, hn
      cases Result.ok_injective h
      have hx := ConRon.Refine.ExprOps.vec_index_getElem? hii
      obtain ⟨x, xs, hb⟩ : ∃ x xs, b.val = x :: xs := by
        cases hbv : b.val with
        | nil => simp [hbv] at hx
        | cons x xs => exact ⟨x, xs, rfl⟩
      rw [hb] at hx
      cases Option.some.inj (by simpa using hx)
      simp [absIDeclaration, ConRon.Arena.Frontend.recKey, hb, i_constant_info_name_abs hn]

/-- **`foreign_at` is `foreignAt`.** -/
theorem foreign_at_eq {homes : ron.hashmap2.HashMap2 arena.handle.NIdx arena.handle.NIdx}
    {homes' : Std.HashMap NIdx NIdx} (hH : HomesRel homes homes') {ch c : arena.handle.NIdx}
    {b : Bool} (h : frontend.compare.foreign_at homes ch c = ok b) :
    b = ConRon.Arena.Frontend.foreignAt homes' (absNIdx ch) (absNIdx c) := by
  rw [frontend.compare.foreign_at.eq_def] at h
  peel h as o, ho
  have e := ConRon.Refine.HashMap2.Rel_get_wf nidx_eq2 hH.inv (anyNKeysOk _) hH.map trivial ho
  cases o with
  | none =>
    cases Result.ok_injective h
    simp [ConRon.Arena.Frontend.foreignAt, ← e]
  | some x =>
    simp only at h
    peel h as b1, hb1
    rw [ConRon.Refine2.Frontend.nidx_eq2_ok] at hb1
    cases Result.ok_injective hb1
    cases Result.ok_injective h
    simp only [ConRon.Arena.Frontend.foreignAt, ← e, Option.map_some]
    by_cases hx : absNIdx x = absNIdx ch <;> simp [hx]

/-- **`first_foreign` is `find? foreignAt`**, as a position. -/
theorem first_foreign_rel {homes : ron.hashmap2.HashMap2 arena.handle.NIdx arena.handle.NIdx}
    {homes' : Std.HashMap NIdx NIdx} (hH : HomesRel homes homes') {ch : arena.handle.NIdx}
    {cs : alloc.vec.Vec arena.handle.NIdx} {i : Std.Usize}
    (h : frontend.compare.first_foreign homes ch cs = ok i) :
    (i.val < cs.val.length ∧
        ((cs.val.map absNIdx).find? (ConRon.Arena.Frontend.foreignAt homes' (absNIdx ch))).isSome) ∨
      (cs.val.length ≤ i.val ∧
        (cs.val.map absNIdx).find? (ConRon.Arena.Frontend.foreignAt homes' (absNIdx ch)) = none) := by
  rw [frontend.compare.first_foreign] at h
  have key : ∀ (k : Nat) (j : Std.Usize), cs.val.length - j.val = k →
      frontend.compare.first_foreign_loop homes ch cs j = ok i →
      (i.val < cs.val.length ∧ (((cs.val.drop j.val).map absNIdx).find?
          (ConRon.Arena.Frontend.foreignAt homes' (absNIdx ch))).isSome) ∨
        (cs.val.length ≤ i.val ∧ ((cs.val.drop j.val).map absNIdx).find?
          (ConRon.Arena.Frontend.foreignAt homes' (absNIdx ch)) = none) := by
    intro k
    induction k with
    | zero =>
      intro j hk h
      rw [frontend.compare.first_foreign_loop, ite_eq_right (not_lt_len hk)] at h
      cases Result.ok_injective h
      refine Or.inr ⟨by omega, ?_⟩
      rw [ConRon.Refine2.Frontend.Olean.drop_stop hk]
      rfl
    | succ k ih =>
      intro j hk h
      rw [frontend.compare.first_foreign_loop, ite_eq_left (lt_len hk)] at h
      peel h as n, hn
      peel h as b, hb
      rw [idx_cons hn, List.map_cons, List.find?_cons, ← foreign_at_eq hH hb]
      cases b with
      | true =>
        rw [ite_eq_left rfl] at h
        cases Result.ok_injective h
        refine Or.inl ⟨?_, rfl⟩
        have := lt_len hk
        have : (alloc.vec.Vec.len cs).val = cs.val.length := by simp [alloc.vec.Vec.len]
        scalar_tac
      | false =>
        rw [ite_eq_right (by simp)] at h
        peel h as j1, hj1
        have := ih j1 (by rw [usize_succ hj1]; omega) h
        rw [usize_succ hj1] at this
        simpa using this
  simpa using key _ 0#usize rfl h

/-- **`foreign_constant` decides as `foreignConstant`**: `Some` exactly where a named constant
is no declaration of the challenge module, on homes related to the twin's. -/
theorem foreign_constant_some {pers : arena.store.PersTier} {ar : arena.store.EStore}
    {homes : ron.hashmap2.HashMap2 arena.handle.NIdx arena.handle.NIdx}
    {homes' : Std.HashMap NIdx NIdx} (hH : HomesRel homes homes')
    {cs : Option (alloc.vec.Vec arena.handle.NIdx)} {ch : arena.handle.NIdx}
    {o : Option (alloc.vec.Vec Std.U32)}
    (h : frontend.compare.foreign_constant pers ar cs ch homes = ok o) :
    o.isSome = (ConRon.Arena.Frontend.foreignOf (cs.map absNIdxArr) (absNIdx ch) homes').isSome := by
  rw [frontend.compare.foreign_constant.eq_def] at h
  cases cs with
  | none =>
    cases Result.ok_injective h
    rfl
  | some v =>
    simp only at h
    peel h as i, hi
    have hf := first_foreign_rel hH hi
    simp only [ConRon.Arena.Frontend.foreignOf, Option.map_some, Option.bind_some, absNIdxArr,
      List.find?_toArray]
    have hlv : (alloc.vec.Vec.len v).val = v.val.length := by simp [alloc.vec.Vec.len]
    rcases hf with ⟨hlt, hs⟩ | ⟨hle, hn⟩
    · rw [ite_eq_left (by scalar_tac)] at h
      rw [hs]
      revert h
      generalize frontend.compare.foreign_constant.M = M
      intro h
      peel h as s1, -
      peel h as v0, -
      peel h as n, -
      peel h as v1, -
      peel h as s2, -
      peel h as v2, -
      peel h as t, -
      peel h as v3, -
      peel h as t1, -
      peel h as o1, -
      cases o1 with
      | none =>
        simp only at h
        peel h as s3, -
        peel h as v4, -
        peel h as v5, -
        cases Result.ok_injective h
        rfl
      | some hh =>
        simp only at h
        peel h as s3, -
        peel h as v4, -
        peel h as v5, -
        peel h as s4, -
        peel h as v6, -
        peel h as v7, -
        peel h as v8, -
        cases Result.ok_injective h
        rfl
    · rw [ite_eq_right (by scalar_tac)] at h
      cases Result.ok_injective h
      rw [hn]
      rfl

/-! ## A theorem read as the hole it is -/

open Lockstep in
/-- **What a record mentions** in the lockstep shape: the Rust's `UsedConsts` call against the
twin's `used`, from the instance relation `UsedRel`. -/
theorem used_consts_ls {U : Type} {inst : frontend.nat_op_ground.UsedConsts U} {u : U}
    {used : IDeclaration → AM (Array NIdx)} {pers : arena.store.PersTier}
    (hu : UsedRel inst u used pers) {st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (d : arena.env.IDeclaration) :
    LS pers (fun a b => b = absNIdxArr a) (inst.used_consts u pers st d) lst
      (used (absIDeclaration d)) :=
  LS.ofSimRel₀ fun o hm => by
    have h := hu hrel hinv hm
    obtain ⟨r, st'⟩ := o
    cases r with
    | Ok a =>
      obtain ⟨lst', hx, h1, h2⟩ := h
      exact ⟨_, lst', hx, rfl, h1, h2⟩
    | Err e => exact h

open Lockstep in
/-- **`hole_record` ⊑ `holeRecord`**, at any `UsedConsts` instance the twin's `used` relates to. -/
theorem hole_record_ls {U : Type} {inst : frontend.nat_op_ground.UsedConsts U} {u : U}
    {used : IDeclaration → AM (Array NIdx)} {pers : arena.store.PersTier}
    (hu : UsedRel inst u used pers) {st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (d : arena.env.IDeclaration) :
    LS pers (fun a b => b = absIDeclaration a) (frontend.compare.hole_record inst u pers st d) lst
      (ConRon.Arena.Frontend.holeRecord used (absIDeclaration d)) := by
  have hU := @used_consts_ls U inst u used pers hu
  cases d <;> rw [frontend.compare.hole_record.eq_def] <;>
    simp only [absIDeclaration, ConRon.Arena.Frontend.holeRecord] <;> lockstep

open Lockstep in
/-- **`hole_records` ⊑ `holeRecordsGo`**, from the cursor on, onto `out`. -/
theorem hole_records_ls {U : Type} {inst : frontend.nat_op_ground.UsedConsts U} {u : U}
    {used : IDeclaration → AM (Array NIdx)} {pers : arena.store.PersTier}
    (hu : UsedRel inst u used pers) (ds : alloc.vec.Vec arena.env.IDeclaration) :
    ∀ (i : Std.Usize) st lst (out : alloc.vec.Vec arena.env.IDeclaration),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.val.map absIDeclaration)
        (frontend.compare.hole_records inst u pers st ds i out) lst
        (ConRon.Arena.Frontend.holeRecordsGo used (out.val.map absIDeclaration)
          ((ds.val.drop i.val).map absIDeclaration)) := by
  have hH := @hole_record_ls U inst u used pers hu
  refine ls_cursor_acc ds absIDeclaration
    (fun (w : alloc.vec.Vec arena.env.IDeclaration) L =>
      ConRon.Arena.Frontend.holeRecordsGo used (w.val.map absIDeclaration) L)
    (fun st i w => frontend.compare.hole_records inst u pers st ds i w) ?_ ?_
  · intro st lst i w hn hrel hinv
    rw [frontend.compare.hole_records.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len ds by scalar_tac),
      ConRon.Arena.Frontend.holeRecordsGo]
    lockstep
  · intro st lst i w hi hrel hinv ih
    rw [frontend.compare.hole_records.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ds by scalar_tac),
      ConRon.Arena.Frontend.holeRecordsGo]
    lockstep

/-! ## The prelude's copy -/

/-- `prelude_decls_dup` copies the records from the cursor on, onto `out`. -/
theorem prelude_decls_dup_abs (ds : alloc.vec.Vec arena.env.IDeclaration) :
    ∀ (K : Nat) (i : Std.Usize) (out r : alloc.vec.Vec arena.env.IDeclaration),
      ds.val.length - i.val = K → frontend.prepare.prelude_decls_dup ds i out = ok r →
      r.val.map absIDeclaration = (out.val ++ ds.val.drop i.val).map absIDeclaration := by
  intro K
  induction K with
  | zero =>
    intro i out r hk h
    rw [frontend.prepare.prelude_decls_dup.eq_def, ite_eq_left (show i ≥ alloc.vec.Vec.len ds by
      scalar_tac)] at h
    cases Result.ok_injective h
    rw [List.drop_of_length_le (by omega)]
    simp
  | succ K ih =>
    intro i out r hk h
    rw [frontend.prepare.prelude_decls_dup.eq_def, ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len ds by
      scalar_tac)] at h
    have hlt : i.val < ds.val.length := by omega
    obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hdv : ds.val[i.val]? = some d := vec_index_some hd
    obtain ⟨d', hd', h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hd'v := i_declaration_dup_abs hd'
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hout1v : out1.val = out.val ++ [d'] := ConRon.Refine.vec_push_val hout1
    obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi1v := ConRon.Refine.Nat.uadd_val hi1
    rw [ih i1 out1 r (by simp at hi1v; omega) h, hi1v, hout1v]
    have hdrop : ds.val.drop i.val = d :: ds.val.drop (i.val + 1) := by
      rw [List.drop_eq_getElem_cons hlt]
      simp [List.getElem?_eq_some_iff.mp hdv |>.2]
    simp [hdrop, hd'v]

/-- **`prelude_ix_dup` is the identity under the abstraction**: a compared run prepares its
second input with the same prelude. -/
theorem prelude_ix_dup_abs {pre o : frontend.prepare.PreludeIx}
    (h : frontend.prepare.prelude_ix_dup pre = ok o) : absPreludeIx o = absPreludeIx pre := by
  rw [frontend.prepare.prelude_ix_dup] at h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  have := prelude_decls_dup_abs pre.decls _ 0#usize _ v rfl hv
  simp only [show (alloc.vec.Vec.new arena.env.IDeclaration).val = [] from rfl, List.nil_append,
    show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at this
  simp [absPreludeIx, absIDeclArr, this]

end ConRon.Refine2.Frontend

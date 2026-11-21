/-
# `ConRon.Refine2.Frontend.Compare` — `frontend/compare.rs` against `Arena/Frontend/Compare.lean`

**Task #165, Theorem 2.**  The name a record is found under (`rec_key_eq`), and the decision
whether a `--constant` name is no declaration of the challenge module (`foreign_constant_some`):
the Rust's answer is `Some` exactly where the twin's `foreignOf` is.  `rec_kind` and the text of
`foreign_constant`'s answer carry no theorem: they are messages, and a message is not compared.
-/
import ConRon.Refine2.Frontend.Olean.Contract
import ConRon.Refine2.Frontend.Olean.Emit
import ConRon.Refine2.Checker.Shape
import ConRon.Arena.Frontend.Compare
import ConRon.Refine2.Frontend.NatOpDeps

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

end ConRon.Refine2.Frontend

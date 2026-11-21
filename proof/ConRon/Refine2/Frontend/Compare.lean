/-
# `ConRon.Refine2.Frontend.Compare` — `frontend/compare.rs` against `Arena/Frontend/Compare.lean`

**Task #165, Theorem 2.**  A theorem read as the hole it is (`hole_record_ls`,
`hole_records_ls`) and the prelude's copy a compared run prepares its second input with
(`prelude_ix_dup_abs`).  `rec_key`, `rec_kind` and `foreign_constant` carry no theorem: they
serve the driver's `--constant` selection and its messages, which no capstone states.
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
    (fun st i w => frontend.compare.hole_records_loop inst u pers st ds w i) ?_ ?_
  · intro st lst i w hn hrel hinv
    rw [frontend.compare.hole_records_loop.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len ds by scalar_tac),
      ConRon.Arena.Frontend.holeRecordsGo]
    lockstep
  · intro st lst i w hi hrel hinv ih
    rw [frontend.compare.hole_records_loop.eq_def,
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

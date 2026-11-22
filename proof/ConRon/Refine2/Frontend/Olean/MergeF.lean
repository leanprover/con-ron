/-
# `ConRon.Refine2.Frontend.Olean.MergeF` — `isPropCheap` and `subsumesInfo` over any `headTy`

**Task #166, Theorem 2.**  `merge.rs`'s `is_prop_cheap_f`, `is_prop_cheap_head_of`, `subsumes_f`
against the twin's `isPropCheapF`, `isPropCheapHeadOf`, `subsumesF` (`CR`, as `Merge.lean`'s
`is_prop_cheap_rel`/`subsumes_rel`).  The `HeadTy` instance is a parameter: the lemmas hold of any
instance whose `head_ty` agrees with the twin's function (`HeadTyRel`).
-/
import ConRon.Refine2.Frontend.Olean.Merge
import ConRon.Refine2.Frontend.Olean.NamePos

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.olean.merge (is_prop_cheap_f is_prop_cheap_head_of subsumes_f)

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena
open Arena.Frontend.Olean (isPropCheapF isPropCheapHeadOf subsumesF)

/-- **A `HeadTy` instance's `head_ty` is the twin's `headTy`.** -/
def HeadTyRel {H : Type} (inst : frontend.olean.merge.HeadTy H) (h : H)
    (headTy : NIdx → Option EIdx) : Prop :=
  ∀ n o, inst.head_ty h n = ok o → headTy (absNIdx n) = o.map absEIdx

/-- **`is_prop_cheap_f` is `isPropCheapF`.** -/
theorem is_prop_cheap_f_rel {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {H : Type} {inst : frontend.olean.merge.HeadTy H} {h : H} {headTy : NIdx → Option EIdx}
    (pk : frontend.olean.spec.OleanPins) (hH : HeadTyRel inst h headTy) (ty : arena.handle.EIdx) :
    CR pers Eq st lst (is_prop_cheap_f inst pk pers st.store h ty)
      (isPropCheapF (absPins pk) headTy (absEIdx ty)) := by
  rw [is_prop_cheap_f, isPropCheapF]
  refine CR.bind (is_prop_body_rel ty) (fun _ => rfl) fun b b' lst1 hb => ?_
  cases hb
  refine CR.bind (is_prop_head_rel b) (fun _ => rfl) fun o o' lst2 ho => ?_
  cases ho
  cases o with
  | none => exact CR.pure rfl
  | some p =>
    obtain ⟨n, k⟩ := p
    refine CR.pure_step fun o1 h1 => ?_
    dsimp only [absHead, Option.map]
    rw [hH n o1 h1]
    cases o1 with
    | none => exact CR.pure rfl
    | some t => exact is_prop_tail_rel pk t k

/-- **`is_prop_cheap_head_of` is `isPropCheapHeadOf`.** -/
theorem is_prop_cheap_head_of_rel {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState} (ty : arena.handle.EIdx) :
    CR pers (EqA (Option.map absNIdx)) st lst (is_prop_cheap_head_of pers st.store ty)
      (isPropCheapHeadOf (absEIdx ty)) := by
  rw [is_prop_cheap_head_of, isPropCheapHeadOf]
  refine CR.bind (is_prop_body_rel ty) (fun _ => rfl) fun b b' lst1 hb => ?_
  cases hb
  refine CR.bind (is_prop_head_rel b) (fun _ => rfl) fun o o' lst2 ho => ?_
  cases ho
  cases o with
  | none => exact CR.pure rfl
  | some p =>
    obtain ⟨n, k⟩ := p
    exact CR.pure rfl

/-- **`subsumes_f` is `subsumesF`**, of kinds related at any abstraction of their expressions. -/
theorem subsumes_f_rel {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
    {H : Type} {inst : frontend.olean.merge.HeadTy H} {h : H} {headTy : NIdx → Option EIdx}
    (pk : frontend.olean.spec.OleanPins) (hH : HeadTyRel inst h headTy)
    {E₁ E₁' E₂ E₂' : Type} {AE₁ : E₁ → E₁'} {AE₂ : E₂ → E₂'} {RN₁ RN₂ : NatRel}
    (cv1 cv2 : frontend.olean.spec.StmtRec)
    {k1 : frontend.olean.spec.CKindF arena.handle.NIdx E₁} {k1' : ConLeche.Frontend.Olean.CKindF NIdx E₁'}
    {k2 : frontend.olean.spec.CKindF arena.handle.NIdx E₂} {k2' : ConLeche.Frontend.Olean.CKindF NIdx E₂'}
    (hk1 : KindRel absNIdx AE₁ RN₁ k1 k1') (hk2 : KindRel absNIdx AE₂ RN₂ k2 k2') :
    CR pers Eq st lst (subsumes_f inst pk pers st.store h cv1 k1 cv2 k2)
      (subsumesF (absPins pk) headTy (absStmtRec cv1) k1' (absStmtRec cv2) k2') := by
  rw [frontend.olean.merge.subsumes_f.eq_def, Arena.Frontend.Olean.subsumesF.eq_def]
  refine CR.pure_step fun b hb => ?_
  have e1 : ((absStmtRec cv1).name == (absStmtRec cv2).name) = b := by
    rw [nidx_eq2_abs hb]; rfl
  rw [e1]
  cases b with
  | false => exact CR.pure rfl
  | true =>
    rw [ite_eq_left rfl]
    refine CR.pure_step fun b1 hb1 => ?_
    have e2 : ((absStmtRec cv1).type == (absStmtRec cv2).type) = b1 := by
      rw [eidx_eq2_abs hb1]; rfl
    rw [Bool.true_and, e2]
    cases b1 with
    | false => exact CR.pure rfl
    | true =>
      rw [ite_eq_left rfl]
      refine CR.pure_step fun b2 hb2 => ?_
      have e3 : ((absStmtRec cv1).levelParams == (absStmtRec cv2).levelParams) = b2 := by
        rw [nidx_list_eq_abs hb2]; rfl
      rw [Bool.true_and, e3]
      cases b2 with
      | false => exact CR.pure rfl
      | true =>
        rw [ite_eq_left rfl, ite_eq_left rfl]
        simp only [absStmtRec_type, absStmtRec_name]
        cases k1 <;> cases k1' <;> try exact (hk1 : False).elim
        case Ax.ax u1 u1' =>
          cases k2 <;> cases k2' <;> try first | exact (hk2 : False).elim | exact CR.pure rfl
          case Ax.ax u2 u2' =>
            cases (hk1 : u1 = u1')
            cases (hk2 : u2 = u2')
            cases u1 <;> cases u2 <;> first
              | exact CR.pure rfl
              | (simp only [↓reduceIte]; exact is_prop_cheap_f_rel pk hH _)
        case Thm.thm v a v' a' =>
          have ha : a.val.map absNIdx = a' := hk1.2
          cases k2 <;> cases k2' <;> try first | exact (hk2 : False).elim | exact CR.pure rfl
          case Ax.ax u2 u2' =>
            cases (hk2 : u2 = u2')
            subst ha
            dsimp only
            by_cases hl : a.val.length = 1
            · have hi : a.len = 1#usize := UScalar.eq_of_val_eq (by simpa [alloc.vec.Vec.len] using hl)
              obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl
              rw [ite_eq_left hi]
              refine CR.pure_step fun n hn => CR.pure_step fun b3 hb3 => ?_
              have hnx := ConRon.Refine.ExprOps.vec_index_getElem? hn
              rw [hx] at hnx
              cases (by simpa using hnx : x = n)
              have e : (List.map absNIdx a.val == [absNIdx cv2.name]) = b3 := by
                rw [nidx_eq2_abs hb3, hx]; simp
              rw [e]
              cases b3 <;> cases u2 <;> exact CR.pure rfl
            · rw [ite_eq_right (fun hi => hl (by
                have := congrArg UScalar.val hi
                simpa [alloc.vec.Vec.len] using this))]
              have e : (List.map absNIdx a.val == [absNIdx cv2.name]) = false := by
                rw [beq_eq_false_iff_ne]
                intro hc
                exact hl (by simpa using congrArg List.length hc)
              rw [e]
              exact CR.pure rfl
          case Thm.thm w d w' d' =>
            have hd : d.val.map absNIdx = d' := hk2.2
            refine CR.pure_step fun b3 hb3 => ?_
            rw [nidx_list_eq_abs hb3, ha, hd]
            exact CR.pure rfl
        all_goals exact CR.pure rfl

end ConRon.Refine2.Frontend.Olean

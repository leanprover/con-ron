/-
# `ConRon.Refine2.Core.LS.Infer` — region E: the inference bodies in lockstep

Task #97-P5-Core round 5, region E.  The Theorem-2 lockstep lemmas of
`arena::core`'s inference: the two bodies (`infer_body`, `infer_body_io`,
`BodyRel`'s `infer` / `inferIO` fields), the λ- and ∀-telescope loops
(`infer_lams`, `infer_pis` and their leaves), and the application spine
(`infer_spine`, `infer_spine_io`, `infer_app`, `infer_app_io_at`).
-/
import ConRon.Refine2.Core.LS.PrimsE

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep.PE

/-! ## Stubs (other regions' lemmas; deleted at merge) -/

/-- Region A2: `head_and_args` against `headAndArgs`. -/
@[lockstep] theorem stub_head_and_args_ls {pers st v lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = (absEIdx a.1, absEIdxArr a.2))
      (arena.core.head_and_args pers st v) st lst (headAndArgs (absEIdx v)) := by
  sorry


/-! ## The application spine -/

@[lockstep_simp] theorem absEIdxArr_getElem (v : alloc.vec.Vec arena.handle.EIdx) (i : Nat)
    (h : i < (absEIdxArr v).size) :
    (absEIdxArr v)[i] = absEIdx (v.val[i]'(by simpa [absEIdxArr] using h)) := by
  simp [absEIdxArr]

@[lockstep_simp] theorem absEIdxArr_size (v : alloc.vec.Vec arena.handle.EIdx) :
    (absEIdxArr v).size = v.val.length := by
  simp [absEIdxArr]

theorem infer_spine_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers vis st mode lane fu fe lfe depth ty acc args i lst},
      ExprOpsHyp pers → args.val.length - (i : Std.Usize).val = n →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.infer_spine pers vis st mode lane fu fe depth ty acc args i) lst
        (inferSpine (ConRon.Refine.absMode mode)
          (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
          (absEIdx ty) (absEIdxArr acc) (absEIdxArr args) (absSz i)) := by
  induction n with
  | zero =>
    intro pers vis st mode lane fu fe lfe depth ty acc args i lst hx hn hrel hinv hctx hf
    rw [arena.core.infer_spine, inferSpine, dif_neg (by simp [absEIdxArr, absSz]; omega)]
    lockstep_e
  | succ m ih =>
    intro pers vis st mode lane fu fe lfe depth ty acc args i lst hx hn hrel hinv hctx hf
    rw [arena.core.infer_spine, inferSpine, dif_pos (by simp [absEIdxArr, absSz]; omega)]
    lockstep_e


@[lockstep] theorem infer_spine_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth ty acc args i lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_spine pers vis st mode lane fu fe depth ty acc args i) lst
      (inferSpine (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth)
        (absEIdx ty) (absEIdxArr acc) (absEIdxArr args) (absSz i)) :=
  infer_spine_aux hk _ hx rfl hrel hinv hctx hf

@[lockstep] theorem infer_app_ls {f : Nat} (hk : KnotRel f)
    {pers vis st mode lane fu fe lfe depth e lst}
    (hx : ExprOpsHyp pers)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f) :
    LS pers (fun a b => b = absEIdx a)
      (arena.core.infer_app pers vis st mode lane fu fe depth e) lst
      (inferApp (ConRon.Refine.absMode mode)
        (laneKnot (ConRon.Refine.absMode mode) lfe lane f) lfe (absU depth) (absEIdx e)) := by
  rw [arena.core.infer_app, inferApp]
  lockstep_e
  all_goals trace_state
  all_goals sorry

section spineIO
attribute [local lockstep_simp] twin_ite_bind

theorem infer_spine_io_aux {f : Nat} (hk : KnotRel f) (n : Nat) :
    ∀ {pers vis st mode lane io fu fe lfe depth ty acc args i lst},
      ExprOpsHyp pers → args.val.length - (i : Std.Usize).val = n →
      AStateRel₀ pers st lst → AStateInv pers st → CoreCtx vis fe lfe → absU fu = f →
      LS pers (fun a b => b = absEIdx a)
        (arena.core.infer_spine_io pers vis st mode lane io fu fe depth ty acc args i) lst
        (inferSpineIO (ConRon.Refine.absMode mode)
          (laneKnotAt (ConRon.Refine.absMode mode) lfe lane io f) lfe (absU depth)
          (absEIdx ty) (absEIdxArr acc) (absEIdxArr args) (absSz i)) := by
  induction n with
  | zero =>
    intro pers vis st mode lane io fu fe lfe depth ty acc args i lst hx hn hrel hinv hctx hf
    rw [arena.core.infer_spine_io, inferSpineIO, dif_neg (by simp [absEIdxArr, absSz]; omega)]
    lockstep_e
  | succ m ih =>
    intro pers vis st mode lane io fu fe lfe depth ty acc args i lst hx hn hrel hinv hctx hf
    rw [arena.core.infer_spine_io, inferSpineIO, dif_pos (by simp [absEIdxArr, absSz]; omega)]
    lockstep_e

end spineIO

end ConRon.Refine2.Lockstep

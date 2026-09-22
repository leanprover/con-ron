/-
# `ConRon.Refine2.Inductives.NativeInstall` — Theorem 2 for `arena::inductives::native_install`

**Task #97-P5-Ind** (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/inductives/native_install.rs` against
`proof/ConRon/Arena/Inductives/NativeInstall.lean`: the capability record,
official's `is_rec`, the re-check of the field kinds on the opened annotated
constructors, the generated recursor and its rules, the projection table at a
structure-like block, and the two-pass install.

**Forty `pub fn`s against fifteen twin `def`s.**

## Finding 19 — the port does not COPY the environment where the twin does, and
three brackets stand in for the copies

Task #97-P6-5's lever 5 replaced `ifenv_dup` — `O(environment)`, once per
inductive block — by three devices, and each is a refinement obligation of
this module rather than a divergence:

* **`check_native_rec_rules` pushes the rule-less recursor as a BRACKET.**
  The twin writes `let feR := fe.push (.recInfo cvRa …)` and keeps `fe`; the
  port calls `ifenv_push_temp` before generating the rules and
  `ifenv_pop_temp` after, so the `&mut IFEnv` Aeneas gives back as a THIRD
  output component is the pre-call environment.  That is what
  `check_native_rec_refines` claims about it — `IFEnvRel o.2.2 lf` — and it is
  the only thing claimed: nothing downstream reads it except as `fe₂`.
* **`check_native_tail_kinds` lowers `visible_below` by one** instead of
  passing the pre-block environment: `env1` is that environment plus the type
  former at counter `vis - 1`, so hiding one row makes `find?` answer what the
  twin's `fe` answers at every name.  The statement therefore relates the
  LOWERED record to the twin's `fe`, and the equality of the two `find?`s is
  what its proof owes.
* **`check_native` brackets the whole first pass** with
  `ifenv_row` / `ifenv_pop_temp`, so the second pass starts at the twin's own
  `fe`.

**`KnotRel` at five sites** (`check_native_rec_defeq`'s infer/ensureSort/defeq,
`check_native_tail_sorts`' field sorts, and the two entries under
`check_native_pass`), and **finding 10's `hvis` at eleven**.
-/
import ConRon.Refine2.Inductives.NativeParts

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine2.ExprOps (LOut LMemoRel)

/-! ## The capability record -/

/-- `kinds_any_rec` ⊑ `ks.any fun k => k == .recursive || k == .reflexive` from
the cursor on. -/
theorem kinds_any_rec_refines
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind} {i : Std.Usize}
    {o} (hrun : arena.inductives.native_install.kinds_any_rec ks i = ok o) :
    o = (absKindLFrom ks i).any fun k => k == .recursive || k == .reflexive := by
  simp only [absKindLFrom, List.any_map, Function.comp_def]
  refine vec_cursor_any ks _
    (arena.inductives.native_install.kinds_any_rec ks) ?_ ?_ i o hrun
  · intro i o hn h
    rw [arena.inductives.native_install.kinds_any_rec.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ks by scalar_tac), Result.ok.injEq] at h
    rw [← h]
  · intro i x o hx h
    have hlt : i.val < ks.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.inductives.native_install.kinds_any_rec.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ks by scalar_tac)] at h
    obtain ⟨rfk, hrfk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hrx : rfk = x := by
      have h1 := vec_index_some hrfk; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hrx
    have hbv : b = (absRecFieldKind rfk == RecFieldKind.recursive) :=
      rec_field_kind_beq_refines hb
    cases hbb : b
    · rw [hbb] at h hbv
      rw [if_neg (by simp)] at h
      obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hb1v : b1 = (absRecFieldKind rfk == RecFieldKind.reflexive) :=
        rec_field_kind_beq_refines hb1
      cases hbb1 : b1
      · rw [hbb1] at h hb1v
        rw [if_neg (by simp)] at h
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        exact Or.inr ⟨by simp only [← hbv, ← hb1v, Bool.or_self], i2,
          absSz_add_one hi2, h⟩
      · rw [hbb1] at h hb1v
        rw [if_pos (by simp), Result.ok.injEq] at h
        exact Or.inl ⟨by simp only [← hbv, ← hb1v, Bool.false_or], h.symm⟩
    · rw [hbb] at h hbv
      rw [if_pos (by simp), Result.ok.injEq] at h
      exact Or.inl ⟨by simp only [← hbv, Bool.true_or], h.symm⟩

/-- `native_is_rec_from` ⊑ `nativeIsRec`'s outer `any` from the cursor on. -/
theorem native_is_rec_from_refines
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {i : Std.Usize} {o}
    (hrun : arena.inductives.native_install.native_is_rec_from kinds i = ok o) :
    o = (absKindLLFrom kinds i).any fun ks =>
      ks.any fun k => k == .recursive || k == .reflexive := by
  simp only [absKindLLFrom, List.any_map, Function.comp_def]
  refine vec_cursor_any kinds _
    (arena.inductives.native_install.native_is_rec_from kinds) ?_ ?_ i o hrun
  · intro i o hn h
    rw [arena.inductives.native_install.native_is_rec_from.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len kinds by scalar_tac), Result.ok.injEq] at h
    rw [← h]
  · intro i x o hx h
    have hlt : i.val < kinds.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.inductives.native_install.native_is_rec_from.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len kinds by scalar_tac)] at h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hvx : v = x := by
      have h1 := vec_index_some hv; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hvx
    have hbv : b = (absKindL v).any (fun k => k == .recursive || k == .reflexive) := by
      have h2 := kinds_any_rec_refines hb
      simpa [absKindLFrom, absKindL,
        show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using h2
    cases hbb : b
    · rw [hbb] at h hbv
      rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      exact Or.inr ⟨hbv.symm, i2, absSz_add_one hi2, h⟩
    · rw [hbb] at h hbv
      rw [if_pos (by simp), Result.ok.injEq] at h
      exact Or.inl ⟨hbv.symm, h.symm⟩

/-- `native_is_rec` ⊑ `nativeIsRec` — official's `is_rec` off the classified
kinds. -/
theorem native_is_rec_refines
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {o} (hrun : arena.inductives.native_install.native_is_rec kinds = ok o) :
    o = nativeIsRec (absKindLL kinds) := by
  rw [arena.inductives.native_install.native_is_rec] at hrun
  rw [nativeIsRec, native_is_rec_from_refines hrun]
  simp [absKindLLFrom, absKindLL, show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

/-- `native_caps` ⊑ `nativeCaps`. -/
theorem native_caps_refines {pers st lst}
    {p : arena.inductives.native_parts.NativeParts} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_install.native_caps pers st p = ok o) :
    Sim absIIndCaps (fun _ => True) pers lst o
      (nativeCaps (absNativeParts p)) := by
  sorry

/-- `any_dom_mentions` ⊑ `nativeRawRec`'s `anyM`, from the cursor on. -/
theorem any_dom_mentions_refines {pers st lst} {t : arena.handle.NIdx}
    {cbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_install.any_dom_mentions pers st t cbs i
      = ok o) :
    Sim id (fun _ => True) pers lst o
      (anyDomMentionsSpec (absNIdx t) (absBinderLFrom cbs i)) := by
  sorry

/-- `native_raw_rec` ⊑ `nativeRawRec` — **the syntactic reading of `is_rec`**
(con-leche's task #268). -/
theorem native_raw_rec_refines {pers st lst}
    {p : arena.inductives.native_parts.NativeParts} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_install.native_raw_rec pers st p = ok o) :
    Sim id (fun _ => True) pers lst o (nativeRawRec (absNativeParts p)) := by
  sorry

/-! ## `mentionsFvar` -/

/-- `mf_probe` ⊑ `memo[h]?`. -/
theorem mf_probe_refines {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} {k : arena.handle.EIdx} {o}
    (hm : LMemoRel rm lm)
    (hrun : arena.inductives.native_install.mf_probe rm k = ok o) :
    o = lm[absEIdx k]? := by
  rw [arena.inductives.native_install.mf_probe] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hmr, hminv⟩ := hm
  have hto := ConRon.Refine.HashMap2.get_refines_wf eidx_eq2 hminv
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hmr k trivial
  rw [← hrelk, ← hto]
  cases hrc : r with
  | none =>
    rw [hrc] at hrun
    have h2 : (none : Option Bool) = o := Result.ok_injective hrun
    subst h2
    rfl
  | some v =>
    rw [hrc] at hrun
    have h2 : some v = o := Result.ok_injective hrun
    subst h2
    rfl

/-- `mentions_fvar_ins` ⊑ `mentionsFvarIns` — one answer recorded. -/
theorem mentions_fvar_ins_refines {e : arena.handle.EIdx}
    {r : Bool × ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} {o}
    (hm : LMemoRel r.2 lm)
    (hrun : arena.inductives.native_install.mentions_fvar_ins e r = ok o) :
    o.1 = (mentionsFvarIns (absEIdx e) (r.1, lm)).1 ∧
      LMemoRel o.2 (mentionsFvarIns (absEIdx e) (r.1, lm)).2 := by
  obtain ⟨b, memo⟩ := r
  rw [arena.inductives.native_install.mentions_fvar_ins] at hrun
  obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, memo1⟩ := q
  have ho : (b, memo1) = o := Result.ok_injective hrun
  obtain ⟨hrel, hinv⟩ := hm
  have hee : e1 = e := dupId_eidx e e1 he1
  subst hee
  have hinj : ∀ a b : arena.handle.EIdx, True → True → absEIdx a = absEIdx b → a = b :=
    fun a b _ _ hab => absEIdx_inj hab
  obtain ⟨hrel', hkeys'⟩ :=
    ConRon.Refine.HashMap2.Rel_insert_wf eidx_eq2 hinj hinv
      ConRon.Refine.HashMap2.KeysOk_true hrel trivial hq
  have hinv' := (ConRon.Refine.HashMap2.insert_refines_wf eidx_eq2 hinv
    ConRon.Refine.HashMap2.KeysOk_true trivial hq).1
  rw [← ho]
  exact ⟨rfl, ⟨hrel', hinv'⟩⟩

/-- `mentions_fvar_node` ⊑ `mentionsFvarGo`'s arm dispatch. -/
theorem mentions_fvar_node_refines {pers st lst} {q : Std.U64}
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} {fuel : Std.U64} {v : arena.store.ENodeView} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st) (hm : LMemoRel rm lm)
    (hrun : arena.inductives.native_install.mentions_fvar_node pers st q rm fuel v
      = ok o) :
    LOut pers lst o.1 o.2
      ((mentionsFvarNodeSpec (absU q) lm (absU fuel)
        (absENodeView v)).run lst) := by
  sorry

/-- `mentions_fvar_go` ⊑ `mentionsFvarGo`. -/
theorem mentions_fvar_go_refines {pers st lst} {q : Std.U64}
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st) (hm : LMemoRel rm lm)
    (hrun : arena.inductives.native_install.mentions_fvar_go pers st q rm fuel h
      = ok o) :
    LOut pers lst o.1 o.2
      ((mentionsFvarGo (absU q) lm (absU fuel) (absEIdx h)).run lst) := by
  sorry

/-- `mentions_fvar` ⊑ `mentionsFvar` — one memoised walk from the empty
memo. -/
theorem mentions_fvar_refines {pers st lst} {q : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_install.mentions_fvar pers st q e = ok o) :
    Sim id (fun _ => True) pers lst o
      (mentionsFvar (absU q) (absEIdx e)) := by
  sorry

/-! ## The field kinds, re-checked on the opened constructors -/

/-- `later_mentions` ⊑ `nativeOpenedOk`'s `(xFvs.drop (i+1)).anyM`, from the
cursor on. -/
theorem later_mentions_refines {pers st lst} {q : Std.U64}
    {x_fvs : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_install.later_mentions pers st q x_fvs i
      = ok o) :
    Sim id (fun _ => True) pers lst o
      (laterMentionsSpec (absU q) (absEIdxLFrom x_fvs i)) := by
  sorry

/-- `native_field_unused_later` ⊑ `nativeOpenedOk`'s "unused later" clause. -/
theorem native_field_unused_later_refines {pers st lst} {n_p : Std.U64}
    {x_fvs : alloc.vec.Vec arena.handle.EIdx} {xrest : arena.handle.EIdx}
    {i : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_install.native_field_unused_later pers st n_p
      x_fvs xrest i = ok o) :
    Sim id (fun _ => True) pers lst o
      (nativeFieldUnusedLaterSpec (absU n_p) (absEIdxL x_fvs) (absEIdx xrest)
        (absU i)) := by
  sorry

/-- `native_fam_app_ok` ⊑ `nativeOpenedOk`'s family-application test. -/
theorem native_fam_app_ok_refines {pers st lst} {vis : Std.U64} {rf0 lf0}
    {n_p n_idx : Std.U64} {fvs_p : alloc.vec.Vec arena.handle.EIdx}
    {body hd : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf0 lf0) (hfinv : IFEnvInv rf0)
    (hvis : absU vis = lf0.visibleBelow)
    (hrun : arena.inductives.native_install.native_fam_app_ok pers vis st rf0 n_p
      n_idx fvs_p body hd = ok o) :
    Sim id (fun _ => True) pers lst o
      (nativeFamAppOkSpec lf0 (absU n_p) (absU n_idx) (absEIdxL fvs_p)
        (absEIdx body) (absEIdx hd)) := by
  sorry

/-- `native_field_recursive` ⊑ `nativeOpenedOk`'s `.recursive` arm. -/
theorem native_field_recursive_refines {pers st lst} {vis : Std.U64} {rf0 lf0}
    {n_p n_idx : Std.U64} {fvs_p x_fvs : alloc.vec.Vec arena.handle.EIdx}
    {xrest hd : arena.handle.EIdx} {i : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf0 lf0) (hfinv : IFEnvInv rf0)
    (hvis : absU vis = lf0.visibleBelow)
    (hrun : arena.inductives.native_install.native_field_recursive pers vis st rf0
      n_p n_idx fvs_p x_fvs xrest hd i = ok o) :
    Sim id (fun _ => True) pers lst o
      (nativeFieldRecursiveSpec lf0 (absU n_p) (absU n_idx) (absEIdxL fvs_p)
        (absEIdxL x_fvs) (absEIdx xrest) (absEIdx hd) (absU i)) := by
  sorry

/-- `native_field_reflexive` ⊑ `nativeOpenedOk`'s `.reflexive` arm. -/
theorem native_field_reflexive_refines {pers st lst} {vis : Std.U64} {rf0 lf0}
    {n_p n_idx : Std.U64} {fvs_p x_fvs : alloc.vec.Vec arena.handle.EIdx}
    {xrest hd : arena.handle.EIdx} {i : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf0 lf0) (hfinv : IFEnvInv rf0)
    (hvis : absU vis = lf0.visibleBelow)
    (hrun : arena.inductives.native_install.native_field_reflexive pers vis st rf0
      n_p n_idx fvs_p x_fvs xrest hd i = ok o) :
    Sim id (fun _ => True) pers lst o
      (nativeFieldReflexiveSpec lf0 (absU n_p) (absU n_idx) (absEIdxL fvs_p)
        (absEIdxL x_fvs) (absEIdx xrest) (absEIdx hd) (absU i)) := by
  sorry

/-- `native_fields_at` ⊑ `nativeOpenedOk`'s `(List.range nF).allM` from field
`i` on. -/
theorem native_fields_at_refines {pers st lst} {vis : Std.U64} {rf0 lf0}
    {n_p n_idx n_f : Std.U64}
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind}
    {fvs_p x_fvs : alloc.vec.Vec arena.handle.EIdx}
    {xrest hd : arena.handle.EIdx} {i : Std.U64} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf0 lf0) (hfinv : IFEnvInv rf0)
    (hvis : absU vis = lf0.visibleBelow)
    (hrun : arena.inductives.native_install.native_fields_at pers vis st rf0 n_p
      n_idx n_f ks fvs_p x_fvs xrest hd i = ok o) :
    Sim id (fun _ => True) pers lst o
      (nativeFieldsAtSpec lf0 (absU n_p) (absU n_idx) (absKindL ks)
        (absEIdxL fvs_p) (absEIdxL x_fvs) (absEIdx xrest) (absEIdx hd)
        (absU n_f - absU i) (absU i)) := by
  sorry

/-- `native_opened_ok` ⊑ `nativeOpenedOk` — the kinds the recogniser computed,
re-checked on the annotated constructor type OPENED at variables. -/
theorem native_opened_ok_refines {pers st lst} {vis : Std.U64} {rf0 lf0}
    {t : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64} {cty : arena.handle.EIdx} {n_f : Std.U64}
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf0 lf0) (hfinv : IFEnvInv rf0)
    (hvis : absU vis = lf0.visibleBelow)
    (hrun : arena.inductives.native_install.native_opened_ok pers vis st rf0 t lps
      n_p n_idx cty n_f ks = ok o) :
    Sim id (fun _ => True) pers lst o
      (nativeOpenedOk lf0 (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absEIdx cty) (absU n_f) (absKindL ks)) := by
  sorry

/-- `native_fields_ok_from` ⊑ `nativeFieldsOk`'s `allM` from constructor `j`
on. -/
theorem native_fields_ok_from_refines {pers st lst} {vis : Std.U64} {rf0 lf0}
    {t : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {j : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf0 lf0) (hfinv : IFEnvInv rf0)
    (hvis : absU vis = lf0.visibleBelow)
    (hrun : arena.inductives.native_install.native_fields_ok_from pers vis st rf0 t
      lps n_p n_idx ctors_a kinds j = ok o) :
    Sim id (fun _ => True) pers lst o
      (nativeFieldsOkFromSpec lf0 (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absCtorsLFrom ctors_a j) (absKindLLFrom kinds j)) := by
  sorry

/-- `native_fields_ok` ⊑ `nativeFieldsOk`. -/
theorem native_fields_ok_refines {pers st lst} {vis : Std.U64} {rf0 lf0}
    {t : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf0 lf0) (hfinv : IFEnvInv rf0)
    (hvis : absU vis = lf0.visibleBelow)
    (hrun : arena.inductives.native_install.native_fields_ok pers vis st rf0 t lps
      n_p n_idx ctors_a kinds = ok o) :
    Sim id (fun _ => True) pers lst o
      (nativeFieldsOk lf0 (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absCtorsL ctors_a) (absKindLL kinds)) := by
  sorry

/-! ## The recursor -/

/-- `native_rule_scoped` ⊑ `checkNativeRules`' four-conjunct scoping test. -/
theorem native_rule_scoped_refines {pers st lst} {vis : Std.U64} {rfR lfR}
    {rlps : alloc.vec.Vec arena.handle.NIdx} {rhs : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rfR lfR) (hfinv : IFEnvInv rfR)
    (hvis : absU vis = lfR.visibleBelow)
    (hrun : arena.inductives.native_install.native_rule_scoped pers vis st rfR rlps
      rhs = ok o) :
    Sim id (fun _ => True) pers lst o
      (nativeRuleScopedSpec lfR (absNIdxL rlps) (absEIdx rhs)) := by
  sorry

/-- `check_native_rules` ⊑ `checkNativeRules` from the `j`-th rule on, with the
accumulated right-hand sides in front. -/
theorem check_native_rules_refines {pers st lst} {vis : Std.U64} {rfR lfR}
    {rlps : alloc.vec.Vec arena.handle.NIdx} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {elim : arena.handle.NIdx}
    {large : Bool} {n_p n_idx : Std.U64} {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {rec_c : arena.handle.NIdx} {rlvls : arena.handle.LsIdx} {k j : Std.U64}
    {out : alloc.vec.Vec arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rfR lfR) (hfinv : IFEnvInv rfR)
    (hvis : absU vis = lfR.visibleBelow)
    (hrun : arena.inductives.native_install.check_native_rules pers vis st rfR rlps t
      lps elim large n_p n_idx tty ctors rec_c rlvls k j out = ok o) :
    Sim absEIdxL (fun _ => True) pers lst o
      (do pure (absEIdxL out ++
        (← checkNativeRules lfR (absNIdxL rlps) (absNIdx t) (absNIdxL lps)
          (absNIdx elim) large (absU n_p) (absU n_idx) (absEIdx tty)
          (absCtors4L ctors) (absNIdx rec_c) (absLsIdx rlvls) (absU k)
          (absU j)))) := by
  sorry

/-- `check_native_rec_rules` ⊑ `checkNativeRec`'s rule stage — **finding 19's
bracket**: the `&mut IFEnv` Aeneas returns as `o.2.2` is the pre-call
environment, because `ifenv_push_temp` / `ifenv_pop_temp` is the identity on
`fe`. -/
theorem check_native_rec_rules_refines {pers st lst} {rf lf}
    {p : arena.inductives.native_parts.NativeParts}
    {cv_ta : arena.env.IConstantVal}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {rec_ty : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.inductives.native_install.check_native_rec_rules pers st rf p cv_ta
      ctors rec_ty = ok o) :
    Sim (fun r => (absIConstantVal r.1, absEIdxL r.2)) (fun _ => True) pers lst
      (o.1, o.2.1)
      (checkNativeRecRulesSpec (absNativeParts p) (absIConstantVal cv_ta)
        (absCtors4L ctors) (absEIdx rec_ty) lf) ∧
      IFEnvRel o.2.2 lf := by
  sorry

/-- `check_native_rec_defeq` ⊑ `checkNativeRec`'s defeq stage. -/
theorem check_native_rec_defeq_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf lf} {p : arena.inductives.native_parts.NativeParts}
    {cv_ta : arena.env.IConstantVal}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {stream_ty rec_ty : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.native_install.check_native_rec_defeq pers st mode rf p
      cv_ta ctors stream_ty rec_ty = ok o) :
    Sim (fun r => (absIConstantVal r.1, absEIdxL r.2)) (fun _ => True) pers lst
      (o.1, o.2.1)
      (checkNativeRecDefeqSpec (ConRon.Refine.absMode mode) lf (absNativeParts p)
        (absIConstantVal cv_ta) (absCtors4L ctors) (absEIdx stream_ty)
        (absEIdx rec_ty)) ∧
      IFEnvRel o.2.2 lf := by
  sorry

/-- `check_native_rec_ty` ⊑ `checkNativeRec`'s type stage. -/
theorem check_native_rec_ty_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf lf} {p : arena.inductives.native_parts.NativeParts}
    {cv_ta : arena.env.IConstantVal}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {stream_ty : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.native_install.check_native_rec_ty pers st mode rf p
      cv_ta ctors_a stream_ty = ok o) :
    Sim (fun r => (absIConstantVal r.1, absEIdxL r.2)) (fun _ => True) pers lst
      (o.1, o.2.1)
      (checkNativeRecTySpec (ConRon.Refine.absMode mode) lf (absNativeParts p)
        (absIConstantVal cv_ta) (absCtorsL ctors_a) (absEIdx stream_ty)) ∧
      IFEnvRel o.2.2 lf := by
  sorry

/-- `check_native_rec` ⊑ `checkNativeRec` — stage 3: the recursor, generated
and compared. -/
theorem check_native_rec_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf lf} {p : arena.inductives.native_parts.NativeParts}
    {cv_ta : arena.env.IConstantVal}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.native_install.check_native_rec pers st mode rf p cv_ta
      ctors_a = ok o) :
    Sim (fun r => (absIConstantVal r.1, absEIdxL r.2)) (fun _ => True) pers lst
      (o.1, o.2.1)
      (checkNativeRec (ConRon.Refine.absMode mode) lf (absNativeParts p)
        (absIConstantVal cv_ta) (absCtorsL ctors_a)) ∧
      IFEnvRel o.2.2 lf := by
  sorry

/-- `check_native_table` ⊑ `checkNativeTable` — stage 4, the projection table
at a STRUCTURE-LIKE block. -/
theorem check_native_table_refines {pers st lst}
    {p : arena.inductives.native_parts.NativeParts}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {sortss : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx)} {rf lf} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf)
    (hrun : arena.inductives.native_install.check_native_table pers st p ctors_a
      sortss rf = ok o) :
    SimRel (fun r v => IFEnvRel r v) pers lst o
      (checkNativeTable (absNativeParts p) (absCtorsL ctors_a) (absLIdxLL sortss)
        lf) := by
  sorry

/-! ## The two-pass install -/

/-- `rec_ctor_kinds_all` ⊑ `recCtorKindsAll` from the cursor on, with the
accumulated kind lists in front. -/
theorem rec_ctor_kinds_all_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {i : Std.Usize}
    {out : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_install.rec_ctor_kinds_all pers st t lps n_p
      n_idx ctors_a i out = ok o) :
    Sim (Option.map absKindLL) (fun _ => True) pers lst o
      (do pure ((← recCtorKindsAllSpec (absNIdx t) (absNIdxL lps) (absU n_p)
        (absU n_idx) (absCtorsLFrom ctors_a i)).map
          fun r => absKindLL out ++ r)) := by
  sorry

/-- `kinds_any` ⊑ `ks.any (· == k)` from the cursor on. -/
theorem kinds_any_refines
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind}
    {k : arena.inductives.native_parts.RecFieldKind} {i : Std.Usize} {o}
    (hrun : arena.inductives.native_install.kinds_any ks k i = ok o) :
    o = (absKindLFrom ks i).any (· == absRecFieldKind k) := by
  simp only [absKindLFrom, List.any_map, Function.comp_def]
  refine vec_cursor_any ks _
    (arena.inductives.native_install.kinds_any ks k) ?_ ?_ i o hrun
  · intro i o hn h
    rw [arena.inductives.native_install.kinds_any.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ks by scalar_tac), Result.ok.injEq] at h
    rw [← h]
  · intro i x o hx h
    have hlt : i.val < ks.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.inductives.native_install.kinds_any.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ks by scalar_tac)] at h
    obtain ⟨rfk, hrfk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hrx : rfk = x := by
      have h1 := vec_index_some hrfk; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hrx
    have hbv : b = (absRecFieldKind rfk == absRecFieldKind k) :=
      rec_field_kind_beq_refines hb
    cases hbb : b
    · rw [hbb] at h hbv
      rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      exact Or.inr ⟨hbv.symm, i2, absSz_add_one hi2, h⟩
    · rw [hbb] at h hbv
      rw [if_pos (by simp), Result.ok.injEq] at h
      exact Or.inl ⟨hbv.symm, h.symm⟩

/-- `kindss_any` ⊑ `kinds.any fun ks => ks.any (· == k)` from the cursor on. -/
theorem kindss_any_refines
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {k : arena.inductives.native_parts.RecFieldKind} {i : Std.Usize} {o}
    (hrun : arena.inductives.native_install.kindss_any kinds k i = ok o) :
    o = (absKindLLFrom kinds i).any fun ks =>
      ks.any (· == absRecFieldKind k) := by
  simp only [absKindLLFrom, List.any_map, Function.comp_def]
  refine vec_cursor_any kinds _
    (arena.inductives.native_install.kindss_any kinds k) ?_ ?_ i o hrun
  · intro i o hn h
    rw [arena.inductives.native_install.kindss_any.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len kinds by scalar_tac), Result.ok.injEq] at h
    rw [← h]
  · intro i x o hx h
    have hlt : i.val < kinds.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.inductives.native_install.kindss_any.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len kinds by scalar_tac)] at h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hvx : v = x := by
      have h1 := vec_index_some hv; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hvx
    have hbv : b = (absKindL v).any (· == absRecFieldKind k) := by
      have h2 := kinds_any_refines hb
      simpa [absKindLFrom, absKindL,
        show ((0#usize : Std.Usize)).val = 0 by scalar_tac] using h2
    cases hbb : b
    · rw [hbb] at h hbv
      rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      exact Or.inr ⟨hbv.symm, i2, absSz_add_one hi2, h⟩
    · rw [hbb] at h hbv
      rw [if_pos (by simp), Result.ok.injEq] at h
      exact Or.inl ⟨hbv.symm, h.symm⟩

/-- `classify_fix_kinds` ⊑ `classifyFixKinds` — **the fields' kinds, classified
at install** (con-leche's task #210 Part D). -/
theorem classify_fix_kinds_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_install.classify_fix_kinds pers st t lps n_p
      n_idx ctors_a = ok o) :
    Sim absKindLL (fun _ => True) pers lst o
      (classifyFixKinds (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absCtorsL ctors_a)) := by
  sorry

/-- `check_native_pass_kinds` ⊑ `checkNativePass`'s tail. -/
theorem check_native_pass_kinds_refines {pers st lst} {rf1 lf1}
    {cv_ta : arena.env.IConstantVal}
    {p_c : arena.inductives.native_parts.NativeParts}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {sortss : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx)} {is_rec : Bool} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf1 lf1) (hfinv : IFEnvInv rf1)
    (hrun : arena.inductives.native_install.check_native_pass_kinds pers st rf1 cv_ta
      p_c ctors_a sortss is_rec = ok o) :
    SimRel (fun r v => NativePassRel r.1 v.1 ∧ v.2 = r.2) pers lst o
      (checkNativePassKindsSpec lf1 (absIConstantVal cv_ta) (absNativeParts p_c)
        (absCtorsL ctors_a) (absLIdxLL sortss) is_rec) := by
  sorry

/-- `check_native_pass` ⊑ `checkNativePass` — **one pass over the former and
the constructors** (con-leche's task #268) at a given `is_rec` verdict. -/
theorem check_native_pass_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf lf} {p0 : arena.inductives.native_parts.NativeParts} {is_rec : Bool} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.native_install.check_native_pass pers st mode rf p0
      is_rec = ok o) :
    SimRel (fun r v => NativePassRel r.1 v.1 ∧ v.2 = r.2) pers lst o
      (checkNativePass (ConRon.Refine.absMode mode) lf (absNativeParts p0)
        is_rec) := by
  sorry

/-- `check_native_tail_install` ⊑ `checkNativeTail`'s install stage. -/
theorem check_native_tail_install_refines {pers st lst}
    {mode : kernel.env.CheckMode} {rq : arena.inductives.native_install.NativePass}
    {lq : NativePass} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hq : NativePassRel rq lq) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.native_install.check_native_tail_install pers st mode rq
      = ok o) :
    SimRel (fun r v => IFEnvRel r v) pers lst o
      (checkNativeTailInstallSpec (ConRon.Refine.absMode mode) lq) := by
  sorry

/-- `check_native_tail_kinds` ⊑ `checkNativeTail`'s kind stage.  **Finding
19's visibility bound**: the port lowers `env1.visible_below` by one to hide
the type former's row, so the record it hands `nativeFieldsOk` relates to the
twin's PRE-BLOCK environment `lf`, which is what `hpre` says. -/
theorem check_native_tail_kinds_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rq : arena.inductives.native_install.NativePass} {lq : NativePass} {lf} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hq : NativePassRel rq lq) (hknot : KnotRel checkFuel)
    (hpre : ∀ n, lf.find? n =
      (if n = lq.p.cvT.name then none else lq.env₁.find? n))
    (hrun : arena.inductives.native_install.check_native_tail_kinds pers st mode rq
      = ok o) :
    SimRel (fun r v => IFEnvRel r v) pers lst o
      (checkNativeTailKindsSpec (ConRon.Refine.absMode mode) lf lq) := by
  sorry

/-- `check_native_tail_sorts` ⊑ `checkNativeTail`'s index-sort stage. -/
theorem check_native_tail_sorts_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rq : arena.inductives.native_install.NativePass} {lq : NativePass} {lf} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hq : NativePassRel rq lq) (hknot : KnotRel checkFuel)
    (hpre : ∀ n, lf.find? n =
      (if n = lq.p.cvT.name then none else lq.env₁.find? n))
    (hrun : arena.inductives.native_install.check_native_tail_sorts pers st mode rq
      = ok o) :
    SimRel (fun r v => IFEnvRel r v) pers lst o
      (checkNativeTailSortsSpec (ConRon.Refine.absMode mode) lf lq) := by
  sorry

/-- `check_native_tail` ⊑ `checkNativeTail` — **the install after the pass**
(con-leche's task #268). -/
theorem check_native_tail_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rq : arena.inductives.native_install.NativePass} {lq : NativePass} {lf} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hq : NativePassRel rq lq) (hknot : KnotRel checkFuel)
    (hpre : ∀ n, lf.find? n =
      (if n = lq.p.cvT.name then none else lq.env₁.find? n))
    (hrun : arena.inductives.native_install.check_native_tail pers st mode rq
      = ok o) :
    SimRel (fun r v => IFEnvRel r v) pers lst o
      (checkNativeTail (ConRon.Refine.absMode mode) lf lq) := by
  sorry

/-- `ctor_name_seen` ⊑ `(ctors.map (·.1.name)).contains n` from the cursor
on. -/
theorem ctor_name_seen_refines
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {i : Std.Usize}
    {n : arena.handle.NIdx} {o}
    (hrun : arena.inductives.native_install.ctor_name_seen ctors i n = ok o) :
    o = ((absCtorsLFrom ctors i).map (·.1.name)).contains (absNIdx n) := by
  simp only [absCtorsLFrom, List.map_map, List.contains_eq_any_beq, List.any_map,
    Function.comp_def, absIConstantVal]
  refine vec_cursor_any ctors _
    (fun i => arena.inductives.native_install.ctor_name_seen ctors i n) ?_ ?_ i o hrun
  · intro i o hn h
    rw [arena.inductives.native_install.ctor_name_seen.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ctors by scalar_tac), Result.ok.injEq] at h
    rw [← h]
  · intro i x o hx h
    have hlt : i.val < ctors.val.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [arena.inductives.native_install.ctor_name_seen.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ctors by scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨iv, nf⟩ := q
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv : b = (absNIdx n == absNIdx iv.name) := by
      rw [nidx_eq2_abs hb]
      by_cases hc : absNIdx iv.name = absNIdx n
      · simp [hc]
      · have hc' : ¬ absNIdx n = absNIdx iv.name := fun x => hc x.symm
        simp [hc, hc']
    cases hbb : b
    · rw [hbb] at h hbv
      rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      exact Or.inr ⟨hbv.symm, i2, absSz_add_one hi2, h⟩
    · rw [hbb] at h hbv
      rw [if_pos (by simp), Result.ok.injEq] at h
      exact Or.inl ⟨hbv.symm, h.symm⟩

/-- `ctor_names_nodup` ⊑ `(p₀.ctors.map (·.1.name)).Nodup` from the cursor
on. -/
theorem ctor_names_nodup_refines
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {i : Std.Usize} {o}
    (hrun : arena.inductives.native_install.ctor_names_nodup ctors i = ok o) :
    o = decide (((absCtorsLFrom ctors i).map (·.1.name)).Nodup) := by
  simp only [absCtorsLFrom, List.map_map, Function.comp_def, absIConstantVal]
  refine cursor_induction (fun i : Std.Usize => i.val) ctors.val.length
    (fun i (_ : Unit) => ∀ o,
      arena.inductives.native_install.ctor_names_nodup ctors i = ok o →
      o = decide (((ctors.val.drop i.val).map fun x => absNIdx x.1.name).Nodup))
    ?_ ?_ i () o hrun
  · intro i _ hn o h
    rw [arena.inductives.native_install.ctor_names_nodup.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ctors by scalar_tac), Result.ok.injEq] at h
    rw [← h, List.drop_eq_nil_of_le hn]
    simp
  · intro i _ hi ih o h
    rw [arena.inductives.native_install.ctor_names_nodup.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ctors by scalar_tac)] at h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨iv, nf⟩ := q
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
    obtain ⟨hqb, hqv⟩ := List.getElem?_eq_some_iff.mp (vec_index_some hq)
    have hbv : b = decide (absNIdx iv.name ∈
        (ctors.val.drop (i.val + 1)).map fun x => absNIdx x.1.name) := by
      have h2 := ctor_name_seen_refines hb
      rw [h2]
      simp [absCtorsLFrom, absIConstantVal, hi2v, Function.comp_def]
    rw [List.drop_eq_getElem_cons hqb, hqv, List.map_cons]
    cases hbb : b
    · rw [hbb] at h hbv
      rw [if_neg (by simp)] at h
      rw [ih i2 () hi2v o h, hi2v]
      have hmem : absNIdx iv.name ∉
          List.drop (i.val + 1) (ctors.val.map fun x => absNIdx x.1.name) := by
        have h3 := hbv.symm
        simp only [List.map_drop] at h3 ⊢
        simpa using h3
      simp [List.nodup_cons, hmem, Function.comp_def]
    · rw [hbb] at h hbv
      rw [if_pos (by simp), Result.ok.injEq] at h
      have hmem : absNIdx iv.name ∈
          List.drop (i.val + 1) (ctors.val.map fun x => absNIdx x.1.name) := by
        have h3 := hbv.symm
        simp only [List.map_drop] at h3 ⊢
        simpa using h3
      rw [← h]
      simp [List.nodup_cons, hmem, Function.comp_def]

/-- `check_native` ⊑ `checkNative` — check and install a **direct recursive
block**: the distinct names, the pass over the former and the constructors —
again where the record's syntactic reading overshot — and the install after
it. -/
theorem check_native_refines {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {p0 : arena.inductives.native_parts.NativeParts} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRel rf lf) (hfinv : IFEnvInv rf) (hknot : KnotRel checkFuel)
    (hrun : arena.inductives.native_install.check_native pers st mode rf p0 = ok o) :
    SimRel (fun r v => IFEnvRel r v) pers lst o
      (checkNative (ConRon.Refine.absMode mode) lf (absNativeParts p0)) := by
  sorry

end ConRon.Refine2

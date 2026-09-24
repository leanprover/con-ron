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

open scoped ConRon.Refine2.IndSide

open ConRon.Arena
open ConRon.Refine2.ExprOps (LMemoRel)

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

open Lockstep in
/-- `kinds_any_rec_twin` at the cursor `0` (and an empty accumulator): the
form a caller's twin has, so the `TwinEq` rewrites it. -/
@[lockstep] theorem kinds_any_rec_twin0
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind} :
    LSP (arena.inductives.native_install.kinds_any_rec ks 0#usize) (fun o => TwinEq ((absKindL ks).any fun k => k == .recursive || k == .reflexive) (o)) := by
  intro o h
  have h' := (kinds_any_rec_refines h).symm
  simpa [Lockstep.TwinEq, absKindLFrom, absKindL, alloc.vec.Vec.new] using h'

open Lockstep in
@[lockstep] theorem kinds_any_rec_twin
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind}
    {i : Std.Usize} :
    LSP (arena.inductives.native_install.kinds_any_rec ks i) (fun o => TwinEq ((absKindLFrom ks i).any fun k => k == .recursive || k == .reflexive) (o)) :=
  fun o h => (kinds_any_rec_refines h).symm

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

open Lockstep in
/-- `native_is_rec_from_twin` at the cursor `0` (and an empty accumulator): the
form a caller's twin has, so the `TwinEq` rewrites it. -/
@[lockstep] theorem native_is_rec_from_twin0
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)} :
    LSP (arena.inductives.native_install.native_is_rec_from kinds 0#usize) (fun o => TwinEq ((absKindLL kinds).any fun ks => ks.any fun k => k == .recursive || k == .reflexive) (o)) := by
  intro o h
  have h' := (native_is_rec_from_refines h).symm
  simpa [Lockstep.TwinEq, absKindLLFrom, absKindLL, alloc.vec.Vec.new] using h'

open Lockstep in
@[lockstep] theorem native_is_rec_from_twin
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {i : Std.Usize} :
    LSP (arena.inductives.native_install.native_is_rec_from kinds i) (fun o => TwinEq ((absKindLLFrom kinds i).any fun ks => ks.any fun k => k == .recursive || k == .reflexive) (o)) :=
  fun o h => (native_is_rec_from_refines h).symm

/-- `native_is_rec` ⊑ `nativeIsRec` — official's `is_rec` off the classified
kinds. -/
theorem native_is_rec_refines
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {o} (hrun : arena.inductives.native_install.native_is_rec kinds = ok o) :
    o = nativeIsRec (absKindLL kinds) := by
  rw [arena.inductives.native_install.native_is_rec] at hrun
  rw [nativeIsRec, native_is_rec_from_refines hrun]
  simp [absKindLLFrom, absKindLL, show ((0#usize : Std.Usize)).val = 0 by scalar_tac]

open Lockstep in
@[lockstep] theorem native_is_rec_twin
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)} :
    LSP (arena.inductives.native_install.native_is_rec kinds) (fun o => TwinEq (nativeIsRec (absKindLL kinds)) (o)) :=
  fun o h => (native_is_rec_refines h).symm

/-- `native_caps` ⊑ `nativeCaps`. -/
theorem native_caps_refines {pers st lst}
    {p : arena.inductives.native_parts.NativeParts} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_install.native_caps pers st p = ok o) :
    Sim₀ absIIndCaps pers lst o
      (nativeCaps (absNativeParts p)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.native_install.native_caps, nativeCaps]
  lockstep

open Lockstep in
@[lockstep] theorem native_caps_ls
    {pers st lst}
    {p : arena.inductives.native_parts.NativeParts}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absIIndCaps a) (arena.inductives.native_install.native_caps pers st p) lst
      (nativeCaps (absNativeParts p)) :=
  LS.ofSim₀ fun _ h => native_caps_refines hrel hinv h

/-- `any_dom_mentions` ⊑ `nativeRawRec`'s `anyM`, from the cursor on. -/
theorem any_dom_mentions_refines {pers st lst} {t : arena.handle.NIdx}
    {cbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_install.any_dom_mentions pers st t cbs i
      = ok o) :
    Sim₀ id pers lst o
      (anyDomMentionsSpec (absNIdx t) (absBinderLFrom cbs i)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  revert st lst hrel hinv hrun
  simp only [absBinderLFrom]
  intro st lst hrel hinv _
  refine ls_cursor cbs (fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2)) (anyDomMentionsSpec (absNIdx t))
    (fun st i => arena.inductives.native_install.any_dom_mentions pers st t cbs i) ?_ ?_ i st lst hrel hinv
  · intro st lst i hn hrel hinv
    try simp only []
    rw [arena.inductives.native_install.any_dom_mentions.eq_def, anyDomMentionsSpec]
    rw [if_pos (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep
  · intro st lst i hb hrel hinv ih
    try simp only []
    rw [arena.inductives.native_install.any_dom_mentions.eq_def, anyDomMentionsSpec]
    rw [if_neg (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep

open Lockstep in
@[lockstep] theorem any_dom_mentions_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {cbs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.native_install.any_dom_mentions pers st t cbs i) lst
      (anyDomMentionsSpec (absNIdx t) (absBinderLFrom cbs i)) :=
  LS.ofSim₀ fun _ h => any_dom_mentions_refines hrel hinv h

/-- `nativeRawRec`'s `anyM` IS `anyDomMentionsSpec` (the accumulator-free cursor
fold the port's `any_dom_mentions` twins). -/
theorem anyM_mentionsConst_eq (T : NIdx) (l : List (EIdx × ConLeche.BinderMeta)) :
    l.anyM (fun b => mentionsConst T b.1) = anyDomMentionsSpec T l := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    rw [List.anyM, anyDomMentionsSpec, ← ih]
    refine am_bind_congr _ ?_; intro c
    cases c <;> rfl

/-- `nativeRawRec` in the port's shape: the `anyM` from `nP` on only when the
telescope is longer than `nP` (off the end it is `false` either way). -/
theorem nativeRawRec_port (p : NativeParts) :
    nativeRawRec p = (match p.ctors with
      | [c] => do
        match ← stripPis (p.nP + c.2) c.1.type with
        | some (cbs, _) =>
          if p.nP < cbs.length then anyDomMentionsSpec p.cvT.name (cbs.drop p.nP)
          else pure false
        | none => pure false
      | _ => pure false) := by
  rw [nativeRawRec]
  rcases h : p.ctors with _ | ⟨c, _ | ⟨c2, rest⟩⟩
  · rfl
  · refine am_bind_congr _ ?_; intro r
    rcases r with _ | ⟨cbs, _⟩
    · rfl
    · simp only [anyM_mentionsConst_eq]
      split
      · rfl
      · rw [List.drop_eq_nil_of_le (by omega)]; rfl
  · rfl

/-- `native_raw_rec` ⊑ `nativeRawRec` — **the syntactic reading of `is_rec`**
(con-leche's task #268). -/
theorem native_raw_rec_refines {pers st lst}
    {p : arena.inductives.native_parts.NativeParts} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_install.native_raw_rec pers st p = ok o) :
    Sim₀ id pers lst o (nativeRawRec (absNativeParts p)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  rw [arena.inductives.native_install.native_raw_rec, nativeRawRec_port]
  simp only [absNativeParts, absInductiveShape, absCtorsL]
  rcases hc : p.shape.ctors.val with _ | ⟨c, _ | ⟨c2, rest⟩⟩
  · have hlen : alloc.vec.Vec.len p.shape.ctors ≠ 1#usize := by
      intro h1; have : (alloc.vec.Vec.len p.shape.ctors).val = 1 := by rw [h1]; rfl
      simp [alloc.vec.Vec.len, hc] at this
    simp only [bne_iff_ne, ne_eq, hlen, not_false_eq_true, if_true, List.map_nil]
    lockstep
  · have hlen : alloc.vec.Vec.len p.shape.ctors = 1#usize := by
      have : (alloc.vec.Vec.len p.shape.ctors).val = 1 := by simp [alloc.vec.Vec.len, hc]
      scalar_tac
    have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        (arena.env.IConstantVal × Std.U64)) p.shape.ctors 0#usize = ok c := by
      rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
      simp [hc]
    simp only [hlen, bne_self_eq_false, Bool.false_eq_true, if_false, hidx, List.map_cons,
      List.map_nil]
    lockstep
  · have hlen : alloc.vec.Vec.len p.shape.ctors ≠ 1#usize := by
      intro h1; have : (alloc.vec.Vec.len p.shape.ctors).val = 1 := by rw [h1]; rfl
      simp [alloc.vec.Vec.len, hc] at this
    simp only [bne_iff_ne, ne_eq, hlen, not_false_eq_true, if_true, List.map_cons]
    lockstep

open Lockstep in
@[lockstep] theorem native_raw_rec_ls
    {pers st lst}
    {p : arena.inductives.native_parts.NativeParts}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.native_install.native_raw_rec pers st p) lst
                       (nativeRawRec (absNativeParts p)) :=
  LS.ofSim₀ fun _ h => native_raw_rec_refines hrel hinv h

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

open Lockstep in
@[lockstep] theorem mf_probe_twin
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool}
    {k : arena.handle.EIdx}
    (hm : LMemoRel rm lm) :
    LSP (arena.inductives.native_install.mf_probe rm k) (fun o => TwinEq (lm[absEIdx k]?) (o)) :=
  fun o h => (mf_probe_refines hm h).symm

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
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hm : LMemoRel rm lm)
    (hrun : arena.inductives.native_install.mentions_fvar_node pers st q rm fuel v
      = ok o) :
    SimRel₀ LOutRel pers lst o
      (mentionsFvarNodeSpec (absU q) lm (absU fuel)
        (absENodeView v)) := by
  sorry

open Lockstep in
@[lockstep] theorem mentions_fvar_node_ls
    {pers st lst}
    {q : Std.U64}
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool}
    {fuel : Std.U64}
    {v : arena.store.ENodeView}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hm : LMemoRel rm lm) :
    LS pers LOutRel (arena.inductives.native_install.mentions_fvar_node pers st q rm fuel v) lst
      (mentionsFvarNodeSpec (absU q) lm (absU fuel)
        (absENodeView v)) :=
  LS.ofSimRel₀ fun _ h => mentions_fvar_node_refines hrel hinv hm h

/-- `mentions_fvar_go` ⊑ `mentionsFvarGo`. -/
theorem mentions_fvar_go_refines {pers st lst} {q : Std.U64}
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} {fuel : Std.U64} {h : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (hm : LMemoRel rm lm)
    (hrun : arena.inductives.native_install.mentions_fvar_go pers st q rm fuel h
      = ok o) :
    SimRel₀ LOutRel pers lst o
      (mentionsFvarGo (absU q) lm (absU fuel) (absEIdx h)) := by
  sorry

open Lockstep in
@[lockstep] theorem mentions_fvar_go_ls
    {pers st lst}
    {q : Std.U64}
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool}
    {fuel : Std.U64}
    {h : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hm : LMemoRel rm lm) :
    LS pers LOutRel (arena.inductives.native_install.mentions_fvar_go pers st q rm fuel h) lst
      (mentionsFvarGo (absU q) lm (absU fuel) (absEIdx h)) :=
  LS.ofSimRel₀ fun _ h => mentions_fvar_go_refines hrel hinv hm h

/-- `mentions_fvar` ⊑ `mentionsFvar` — one memoised walk from the empty
memo. -/
theorem mentions_fvar_refines {pers st lst} {q : Std.U64}
    {e : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_install.mentions_fvar pers st q e = ok o) :
    Sim₀ id pers lst o
      (mentionsFvar (absU q) (absEIdx e)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  rw [arena.inductives.native_install.mentions_fvar, mentionsFvar]
  lockstep

open Lockstep in
@[lockstep] theorem mentions_fvar_ls
    {pers st lst}
    {q : Std.U64}
    {e : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.native_install.mentions_fvar pers st q e) lst
      (mentionsFvar (absU q) (absEIdx e)) :=
  LS.ofSim₀ fun _ h => mentions_fvar_refines hrel hinv h

/-! ## The field kinds, re-checked on the opened constructors -/

/-- `later_mentions` ⊑ `nativeOpenedOk`'s `(xFvs.drop (i+1)).anyM`, from the
cursor on. -/
theorem later_mentions_refines {pers st lst} {q : Std.U64}
    {x_fvs : alloc.vec.Vec arena.handle.EIdx} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_install.later_mentions pers st q x_fvs i
      = ok o) :
    Sim₀ id pers lst o
      (laterMentionsSpec (absU q) (absEIdxLFrom x_fvs i)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  revert st lst hrel hinv hrun
  simp only [absEIdxLFrom]
  intro st lst hrel hinv _
  refine ls_cursor x_fvs absEIdx (laterMentionsSpec (absU q))
    (fun st i => arena.inductives.native_install.later_mentions pers st q x_fvs i)
    ?_ ?_ i st lst hrel hinv
  · intro st lst i hn hrel hinv
    rw [arena.inductives.native_install.later_mentions.eq_def, laterMentionsSpec]
    rw [if_pos (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep
  · intro st lst i hb hrel hinv ih
    rw [arena.inductives.native_install.later_mentions.eq_def, laterMentionsSpec]
    rw [if_neg (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep

open Lockstep in
@[lockstep] theorem later_mentions_ls
    {pers st lst}
    {q : Std.U64}
    {x_fvs : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.native_install.later_mentions pers st q x_fvs i) lst
      (laterMentionsSpec (absU q) (absEIdxLFrom x_fvs i)) :=
  LS.ofSim₀ fun _ h => later_mentions_refines hrel hinv h

/-- The twin's `unwrapOr xs[i]? e` as the port's bounds test. -/
theorem unwrapOr_getElem?_eq {α : Type} (l : List α) (i : Nat) (e : CheckError) :
    unwrapOr l[i]? e = (if h : i < l.length then pure l[i] else Arena.fail e) := by
  by_cases h : i < l.length
  · rw [dif_pos h, List.getElem?_eq_getElem h]; rfl
  · rw [dif_neg h, List.getElem?_eq_none (by omega)]; rfl

open Lockstep in
/-- `native_install::field_at` (the port's field read, a decline off the end)
against the twin's `unwrapOr xFvs[i]? (.internal …)`. -/
@[lockstep] theorem field_at_ls {pers st lst} {x_fvs : alloc.vec.Vec arena.handle.EIdx}
    {i : Std.U64} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absEIdx a) (arena.inductives.native_install.field_at x_fvs i) st lst
      (unwrapOr (absEIdxL x_fvs)[absU i]? (.internal "direct rec: field index")) := by
  apply LSR.of_LS
  rw [arena.inductives.native_install.field_at, unwrapOr_getElem?_eq]
  lockstep

/-- `nativeFieldUnusedLaterSpec` in the port's shape: the later-fields scan
only when there is a later field (off the end it is `false`, effect-free). -/
theorem nativeFieldUnusedLaterSpec_port (nP : Nat) (xFvs : List EIdx) (xrest : EIdx) (i : Nat) :
    nativeFieldUnusedLaterSpec nP xFvs xrest i =
      (if i + 1 < xFvs.length then nativeFieldUnusedLaterSpec nP xFvs xrest i
       else do pure !(← mentionsFvar (nP + i) xrest)) := by
  split
  · rfl
  · rw [nativeFieldUnusedLaterSpec, List.drop_eq_nil_of_le (by omega)]
    rfl

/-- `native_field_unused_later` ⊑ `nativeOpenedOk`'s "unused later" clause. -/
theorem native_field_unused_later_refines {pers st lst} {n_p : Std.U64}
    {x_fvs : alloc.vec.Vec arena.handle.EIdx} {xrest : arena.handle.EIdx}
    {i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_install.native_field_unused_later pers st n_p
      x_fvs xrest i = ok o) :
    Sim₀ id pers lst o
      (nativeFieldUnusedLaterSpec (absU n_p) (absEIdxL x_fvs) (absEIdx xrest)
        (absU i)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  rw [arena.inductives.native_install.native_field_unused_later, nativeFieldUnusedLaterSpec_port,
    nativeFieldUnusedLaterSpec]
  lockstep

open Lockstep in
@[lockstep] theorem native_field_unused_later_ls
    {pers st lst}
    {n_p : Std.U64}
    {x_fvs : alloc.vec.Vec arena.handle.EIdx}
    {xrest : arena.handle.EIdx}
    {i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = id a) (arena.inductives.native_install.native_field_unused_later pers st n_p x_fvs xrest i) lst
      (nativeFieldUnusedLaterSpec (absU n_p) (absEIdxL x_fvs) (absEIdx xrest)
        (absU i)) :=
  LS.ofSim₀ fun _ h => native_field_unused_later_refines hrel hinv h

/-- `nativeFamAppOkSpec` with its conjunction as the port's short-circuit
chain (`fna.eq2(hd) && eidx_vec_beq(pre, fvs_p) && len == nP + nIdx`). -/
theorem nativeFamAppOkSpec_port (fe₀ : IFEnv) (nP nIdx : Nat) (fvsP : List EIdx) (body hd : EIdx) :
    nativeFamAppOkSpec fe₀ nP nIdx fvsP body hd = (do
      let fn ← getAppFn coreWalkFuel body
      let args ← getAppArgs coreWalkFuel body
      if fn == hd then
        if args.take nP == fvsP then
          if args.length = nP + nIdx then idxArgsResolveSpec fe₀ (args.drop nP)
          else pure false
        else pure false
      else pure false) := by
  rw [nativeFamAppOkSpec]
  refine am_bind_congr _ ?_; intro fn
  refine am_bind_congr _ ?_; intro args
  by_cases h1 : (fn == hd) = true <;> by_cases h2 : (args.take nP == fvsP) = true <;>
    by_cases h3 : args.length = nP + nIdx <;> simp_all

/-- `native_fam_app_ok` ⊑ `nativeOpenedOk`'s family-application test. -/
theorem native_fam_app_ok_refines {pers st lst} {vis : Std.U64} {rf0 lf0}
    {n_p n_idx : Std.U64} {fvs_p : alloc.vec.Vec arena.handle.EIdx}
    {body hd : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf0 lf0)
    (hvis : absU vis = lf0.visibleBelow)
    (hrun : arena.inductives.native_install.native_fam_app_ok pers vis st rf0 n_p
      n_idx fvs_p body hd = ok o) :
    Sim₀ id pers lst o
      (nativeFamAppOkSpec lf0 (absU n_p) (absU n_idx) (absEIdxL fvs_p)
        (absEIdx body) (absEIdx hd)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  rw [arena.inductives.native_install.native_fam_app_ok, nativeFamAppOkSpec_port]
  lockstep
  all_goals
    exfalso
    have e := absEIdxL_of_takeEidx ‹ExprOps.absEIdxArr _ = takeEidx (ExprOps.absEIdxArr _) _›
    simp only [absEIdxL] at e
    simp_all

open Lockstep in
@[lockstep] theorem native_fam_app_ok_ls
    {pers st lst}
    {vis : Std.U64}
    {rf0 lf0}
    {n_p n_idx : Std.U64}
    {fvs_p : alloc.vec.Vec arena.handle.EIdx}
    {body hd : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf0 lf0)
    (hvis : absU vis = lf0.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.native_install.native_fam_app_ok pers vis st rf0 n_p n_idx fvs_p body hd) lst
      (nativeFamAppOkSpec lf0 (absU n_p) (absU n_idx) (absEIdxL fvs_p)
        (absEIdx body) (absEIdx hd)) :=
  LS.ofSim₀ fun _ h => native_fam_app_ok_refines hrel hinv hfe hvis h

/-- `native_field_recursive` ⊑ `nativeOpenedOk`'s `.recursive` arm. -/
theorem native_field_recursive_refines {pers st lst} {vis : Std.U64} {rf0 lf0}
    {n_p n_idx : Std.U64} {fvs_p x_fvs : alloc.vec.Vec arena.handle.EIdx}
    {xrest hd : arena.handle.EIdx} {i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf0 lf0)
    (hvis : absU vis = lf0.visibleBelow)
    (hrun : arena.inductives.native_install.native_field_recursive pers vis st rf0
      n_p n_idx fvs_p x_fvs xrest hd i = ok o) :
    Sim₀ id pers lst o
      (nativeFieldRecursiveSpec lf0 (absU n_p) (absU n_idx) (absEIdxL fvs_p)
        (absEIdxL x_fvs) (absEIdx xrest) (absEIdx hd) (absU i)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  rw [arena.inductives.native_install.native_field_recursive, nativeFieldRecursiveSpec]
  lockstep

open Lockstep in
@[lockstep] theorem native_field_recursive_ls
    {pers st lst}
    {vis : Std.U64}
    {rf0 lf0}
    {n_p n_idx : Std.U64}
    {fvs_p x_fvs : alloc.vec.Vec arena.handle.EIdx}
    {xrest hd : arena.handle.EIdx}
    {i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf0 lf0)
    (hvis : absU vis = lf0.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.native_install.native_field_recursive pers vis st rf0 n_p n_idx fvs_p x_fvs xrest hd i) lst
      (nativeFieldRecursiveSpec lf0 (absU n_p) (absU n_idx) (absEIdxL fvs_p)
        (absEIdxL x_fvs) (absEIdx xrest) (absEIdx hd) (absU i)) :=
  LS.ofSim₀ fun _ h => native_field_recursive_refines hrel hinv hfe hvis h

/-- `native_field_reflexive` ⊑ `nativeOpenedOk`'s `.reflexive` arm. -/
theorem native_field_reflexive_refines {pers st lst} {vis : Std.U64} {rf0 lf0}
    {n_p n_idx : Std.U64} {fvs_p x_fvs : alloc.vec.Vec arena.handle.EIdx}
    {xrest hd : arena.handle.EIdx} {i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf0 lf0)
    (hvis : absU vis = lf0.visibleBelow)
    (hrun : arena.inductives.native_install.native_field_reflexive pers vis st rf0
      n_p n_idx fvs_p x_fvs xrest hd i = ok o) :
    Sim₀ id pers lst o
      (nativeFieldReflexiveSpec lf0 (absU n_p) (absU n_idx) (absEIdxL fvs_p)
        (absEIdxL x_fvs) (absEIdx xrest) (absEIdx hd) (absU i)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  rw [arena.inductives.native_install.native_field_reflexive, nativeFieldReflexiveSpec]
  lockstep

open Lockstep in
@[lockstep] theorem native_field_reflexive_ls
    {pers st lst}
    {vis : Std.U64}
    {rf0 lf0}
    {n_p n_idx : Std.U64}
    {fvs_p x_fvs : alloc.vec.Vec arena.handle.EIdx}
    {xrest hd : arena.handle.EIdx}
    {i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf0 lf0)
    (hvis : absU vis = lf0.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.native_install.native_field_reflexive pers vis st rf0 n_p n_idx fvs_p x_fvs xrest hd i) lst
      (nativeFieldReflexiveSpec lf0 (absU n_p) (absU n_idx) (absEIdxL fvs_p)
        (absEIdxL x_fvs) (absEIdx xrest) (absEIdx hd) (absU i)) :=
  LS.ofSim₀ fun _ h => native_field_reflexive_refines hrel hinv hfe hvis h

/-- `native_fields_at` ⊑ `nativeOpenedOk`'s `(List.range nF).allM` from field
`i` on. -/
theorem native_fields_at_refines {pers st lst} {vis : Std.U64} {rf0 lf0}
    {n_p n_idx n_f : Std.U64}
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind}
    {fvs_p x_fvs : alloc.vec.Vec arena.handle.EIdx}
    {xrest hd : arena.handle.EIdx} {i : Std.U64} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf0 lf0)
    (hvis : absU vis = lf0.visibleBelow)
    (hrun : arena.inductives.native_install.native_fields_at pers vis st rf0 n_p
      n_idx n_f ks fvs_p x_fvs xrest hd i = ok o) :
    Sim₀ id pers lst o
      (nativeFieldsAtSpec lf0 (absU n_p) (absU n_idx) (absKindL ks)
        (absEIdxL fvs_p) (absEIdxL x_fvs) (absEIdx xrest) (absEIdx hd)
        (absU n_f - absU i) (absU i)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  refine ls_counted (ω := Unit) n_f
    (fun _ m j => nativeFieldsAtSpec lf0 (absU n_p) (absU n_idx) (absKindL ks)
      (absEIdxL fvs_p) (absEIdxL x_fvs) (absEIdx xrest) (absEIdx hd) m j)
    (fun st j _ => arena.inductives.native_install.native_fields_at pers vis st rf0 n_p
      n_idx n_f ks fvs_p x_fvs xrest hd j) ?_ ?_ i st lst () hrel hinv
  · intro st lst j _ hn hrel hinv
    rw [arena.inductives.native_install.native_fields_at.eq_def, nativeFieldsAtSpec]
    rw [if_pos (by scalar_tac)]
    lockstep
  · intro st lst j _ m hj hm hrel hinv ih
    rw [arena.inductives.native_install.native_fields_at.eq_def, nativeFieldsAtSpec]
    rw [if_neg (by scalar_tac)]
    lockstep

open Lockstep in
@[lockstep] theorem native_fields_at_ls
    {pers st lst}
    {vis : Std.U64}
    {rf0 lf0}
    {n_p n_idx n_f : Std.U64}
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind}
    {fvs_p x_fvs : alloc.vec.Vec arena.handle.EIdx}
    {xrest hd : arena.handle.EIdx}
    {i : Std.U64}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf0 lf0)
    (hvis : absU vis = lf0.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.native_install.native_fields_at pers vis st rf0 n_p n_idx n_f ks fvs_p x_fvs xrest hd i) lst
      (nativeFieldsAtSpec lf0 (absU n_p) (absU n_idx) (absKindL ks)
        (absEIdxL fvs_p) (absEIdxL x_fvs) (absEIdx xrest) (absEIdx hd)
        (absU n_f - absU i) (absU i)) :=
  LS.ofSim₀ fun _ h => native_fields_at_refines hrel hinv hfe hvis h

/-- `native_opened_ok` ⊑ `nativeOpenedOk` — the kinds the recogniser computed,
re-checked on the annotated constructor type OPENED at variables. -/
theorem native_opened_ok_refines {pers st lst} {vis : Std.U64} {rf0 lf0}
    {t : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64} {cty : arena.handle.EIdx} {n_f : Std.U64}
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf0 lf0)
    (hvis : absU vis = lf0.visibleBelow)
    (hrun : arena.inductives.native_install.native_opened_ok pers vis st rf0 t lps
      n_p n_idx cty n_f ks = ok o) :
    Sim₀ id pers lst o
      (nativeOpenedOk lf0 (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absEIdx cty) (absU n_f) (absKindL ks)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  rw [arena.inductives.native_install.native_opened_ok, nativeOpenedOk_unfold]
  lockstep

open Lockstep in
@[lockstep] theorem native_opened_ok_ls
    {pers st lst}
    {vis : Std.U64}
    {rf0 lf0}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {cty : arena.handle.EIdx}
    {n_f : Std.U64}
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf0 lf0)
    (hvis : absU vis = lf0.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.native_install.native_opened_ok pers vis st rf0 t lps n_p n_idx cty n_f ks) lst
      (nativeOpenedOk lf0 (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absEIdx cty) (absU n_f) (absKindL ks)) :=
  LS.ofSim₀ fun _ h => native_opened_ok_refines hrel hinv hfe hvis h

/-- `native_fields_ok_from` ⊑ `nativeFieldsOk`'s `allM` from constructor `j`
on. -/
theorem native_fields_ok_from_refines {pers st lst} {vis : Std.U64} {rf0 lf0}
    {t : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {j : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf0 lf0)
    (hvis : absU vis = lf0.visibleBelow)
    (hrun : arena.inductives.native_install.native_fields_ok_from pers vis st rf0 t
      lps n_p n_idx ctors_a kinds j = ok o) :
    Sim₀ id pers lst o
      (nativeFieldsOkFromSpec lf0 (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absCtorsLFrom ctors_a j) (absKindLLFrom kinds j)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  simp only [absCtorsLFrom, absKindLLFrom]
  refine ls_counted_sz (ω := Unit) ctors_a.val.length
    (fun _ _ j => nativeFieldsOkFromSpec lf0 (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
      ((ctors_a.val.drop j).map fun p => (absIConstantVal p.1, absU p.2))
      ((kinds.val.drop j).map absKindL))
    (fun st j _ => arena.inductives.native_install.native_fields_ok_from pers vis st rf0 t
      lps n_p n_idx ctors_a kinds j) ?_ ?_ j st lst () hrel hinv
  · intro st lst j _ hn hrel hinv
    rw [arena.inductives.native_install.native_fields_ok_from.eq_def,
      List.drop_eq_nil_of_le hn, List.map_nil, nativeFieldsOkFromSpec]
    rw [if_pos (by simp [alloc.vec.Vec.len]; scalar_tac)]
    lockstep
  · intro st lst j _ m hj hm hrel hinv ih
    rw [arena.inductives.native_install.native_fields_ok_from.eq_def,
      List.drop_eq_getElem_cons hj, List.map_cons]
    rw [if_neg (by simp [alloc.vec.Vec.len]; scalar_tac)]
    by_cases hk : j.val < kinds.val.length
    · rw [List.drop_eq_getElem_cons hk, List.map_cons, nativeFieldsOkFromSpec]
      lockstep
    · have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)) kinds j =
          fail .arrayOutOfBounds := by
        rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
        simp [List.getElem?_eq_none (by omega : kinds.val.length ≤ j.val)]
      rw [hidx]
      intro o st' h
      simp at h

open Lockstep in
@[lockstep] theorem native_fields_ok_from_ls
    {pers st lst}
    {vis : Std.U64}
    {rf0 lf0}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {j : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf0 lf0)
    (hvis : absU vis = lf0.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.native_install.native_fields_ok_from pers vis st rf0 t lps n_p n_idx ctors_a kinds j) lst
      (nativeFieldsOkFromSpec lf0 (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absCtorsLFrom ctors_a j) (absKindLLFrom kinds j)) :=
  LS.ofSim₀ fun _ h => native_fields_ok_from_refines hrel hinv hfe hvis h

/-- `nativeFieldsOk`'s `(List.range …).allM` from position `k` IS the cursor
transcription on the two lists from `k` (stated for any step function that
agrees with the twin's in range, so it rewrites the twin's own lambda). -/
theorem nativeFieldsOk_allM_from (fe₀ : IFEnv) (T : NIdx) (lps : List NIdx) (nP nIdx : Nat)
    (cs : List (IConstantVal × Nat)) (ks : List (List RecFieldKind))
    (hlen : cs.length = ks.length) (F : Nat → AM Bool)
    (hF : ∀ j (hc : j < cs.length) (hk : j < ks.length), F j =
      (if !(ks[j].length == cs[j].2) then pure false
       else nativeOpenedOk fe₀ T lps nP nIdx cs[j].1.type cs[j].2 ks[j])) :
    ∀ m k, cs.length - k = m →
      (List.range' k m).allM F =
      nativeFieldsOkFromSpec fe₀ T lps nP nIdx (cs.drop k) (ks.drop k) := by
  intro m
  induction m with
  | zero =>
    intro k hk
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ m ih =>
    intro k hk
    have hc : k < cs.length := by omega
    have hks : k < ks.length := by omega
    rw [List.range'_succ, List.drop_eq_getElem_cons hc, List.drop_eq_getElem_cons hks,
      nativeFieldsOkFromSpec, List.allM, hF k hc hks, ← ih (k + 1) (by omega)]
    by_cases h : (!(ks[k].length == cs[k].2)) = true
    · simp [h]
    · simp only [h, if_false, Bool.false_eq_true]
      refine am_bind_congr _ ?_; intro b
      cases b <;> rfl

/-- `nativeFieldsOk` IS the length test and the cursor transcription from `0`. -/
theorem nativeFieldsOk_port (fe₀ : IFEnv) (T : NIdx) (lps : List NIdx) (nP nIdx : Nat)
    (cs : List (IConstantVal × Nat)) (ks : List (List RecFieldKind)) :
    nativeFieldsOk fe₀ T lps nP nIdx cs ks =
      (if cs.length ≠ ks.length then pure false
       else nativeFieldsOkFromSpec fe₀ T lps nP nIdx cs ks) := by
  rw [nativeFieldsOk]
  by_cases h : cs.length = ks.length
  · rw [List.range_eq_range', nativeFieldsOk_allM_from fe₀ T lps nP nIdx cs ks h _ ?_ _ 0 (by omega)]
    · simp [h]
    · intro j hc hk
      simp [List.getElem?_eq_getElem hc, List.getElem?_eq_getElem hk]
  · simp [h]

/-- `native_fields_ok` ⊑ `nativeFieldsOk`. -/
theorem native_fields_ok_refines {pers st lst} {vis : Std.U64} {rf0 lf0}
    {t : arena.handle.NIdx} {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf0 lf0)
    (hvis : absU vis = lf0.visibleBelow)
    (hrun : arena.inductives.native_install.native_fields_ok pers vis st rf0 t lps
      n_p n_idx ctors_a kinds = ok o) :
    Sim₀ id pers lst o
      (nativeFieldsOk lf0 (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absCtorsL ctors_a) (absKindLL kinds)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  clear hrun
  rw [arena.inductives.native_install.native_fields_ok, nativeFieldsOk_port]
  lockstep

open Lockstep in
@[lockstep] theorem native_fields_ok_ls
    {pers st lst}
    {vis : Std.U64}
    {rf0 lf0}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf0 lf0)
    (hvis : absU vis = lf0.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.native_install.native_fields_ok pers vis st rf0 t lps n_p n_idx ctors_a kinds) lst
      (nativeFieldsOk lf0 (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absCtorsL ctors_a) (absKindLL kinds)) :=
  LS.ofSim₀ fun _ h => native_fields_ok_refines hrel hinv hfe hvis h

/-! ## The recursor -/

/-- `native_rule_scoped` ⊑ `checkNativeRules`' four-conjunct scoping test. -/
theorem native_rule_scoped_refines {pers st lst} {vis : Std.U64} {rfR lfR}
    {rlps : alloc.vec.Vec arena.handle.NIdx} {rhs : arena.handle.EIdx} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfR lfR)
    (hvis : absU vis = lfR.visibleBelow)
    (hrun : arena.inductives.native_install.native_rule_scoped pers vis st rfR rlps
      rhs = ok o) :
    Sim₀ id pers lst o
      (nativeRuleScopedSpec lfR (absNIdxL rlps) (absEIdx rhs)) := by
  refine Lockstep.LS.toSim₀ ?_ hrun
  rw [arena.inductives.native_install.native_rule_scoped, nativeRuleScopedSpec]
  lockstep

open Lockstep in
@[lockstep] theorem native_rule_scoped_ls
    {pers st lst}
    {vis : Std.U64}
    {rfR lfR}
    {rlps : alloc.vec.Vec arena.handle.NIdx}
    {rhs : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfR lfR)
    (hvis : absU vis = lfR.visibleBelow) :
    LS pers (fun a b => b = id a) (arena.inductives.native_install.native_rule_scoped pers vis st rfR rlps rhs) lst
      (nativeRuleScopedSpec lfR (absNIdxL rlps) (absEIdx rhs)) :=
  LS.ofSim₀ fun _ h => native_rule_scoped_refines hrel hinv hfe hvis h

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
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfR lfR)
    (hvis : absU vis = lfR.visibleBelow)
    (hrun : arena.inductives.native_install.check_native_rules pers vis st rfR rlps t
      lps elim large n_p n_idx tty ctors rec_c rlvls k j out = ok o) :
    Sim₀ absEIdxL pers lst o
      (do pure (absEIdxL out ++
        (← checkNativeRules lfR (absNIdxL rlps) (absNIdx t) (absNIdxL lps)
          (absNIdx elim) large (absU n_p) (absU n_idx) (absEIdx tty)
          (absCtors4L ctors) (absNIdx rec_c) (absLsIdx rlvls) (absU k)
          (absU j)))) := by
  sorry

open Lockstep in
@[lockstep] theorem check_native_rules_ls
    {pers st lst}
    {vis : Std.U64}
    {rfR lfR}
    {rlps : alloc.vec.Vec arena.handle.NIdx}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {elim : arena.handle.NIdx}
    {large : Bool}
    {n_p n_idx : Std.U64}
    {tty : arena.handle.EIdx}
    {ctors : alloc.vec.Vec (arena.handle.NIdx × Std.U64 × arena.handle.EIdx ×
      (alloc.vec.Vec Std.U64))}
    {rec_c : arena.handle.NIdx}
    {rlvls : arena.handle.LsIdx}
    {k j : Std.U64}
    {out : alloc.vec.Vec arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rfR lfR)
    (hvis : absU vis = lfR.visibleBelow) :
    LS pers (fun a b => b = absEIdxL a) (arena.inductives.native_install.check_native_rules pers vis st rfR rlps t lps elim large n_p n_idx tty ctors rec_c rlvls k j out) lst
      (do pure (absEIdxL out ++
        (← checkNativeRules lfR (absNIdxL rlps) (absNIdx t) (absNIdxL lps)
          (absNIdx elim) large (absU n_p) (absU n_idx) (absEIdx tty)
          (absCtors4L ctors) (absNIdx rec_c) (absLsIdx rlvls) (absU k)
          (absU j)))) :=
  LS.ofSim₀ fun _ h => check_native_rules_refines hrel hinv hfe hvis h

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
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hrun : arena.inductives.native_install.check_native_rec_rules pers st rf p cv_ta
      ctors rec_ty = ok o) :
    Sim₀ (fun r => (absIConstantVal r.1, absEIdxL r.2)) pers lst
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
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hrun : arena.inductives.native_install.check_native_rec_defeq pers st mode rf p
      cv_ta ctors stream_ty rec_ty = ok o) :
    Sim₀ (fun r => (absIConstantVal r.1, absEIdxL r.2)) pers lst
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
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hrun : arena.inductives.native_install.check_native_rec_ty pers st mode rf p
      cv_ta ctors_a stream_ty = ok o) :
    Sim₀ (fun r => (absIConstantVal r.1, absEIdxL r.2)) pers lst
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
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hrun : arena.inductives.native_install.check_native_rec pers st mode rf p cv_ta
      ctors_a = ok o) :
    Sim₀ (fun r => (absIConstantVal r.1, absEIdxL r.2)) pers lst
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
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hrun : arena.inductives.native_install.check_native_table pers st p ctors_a
      sortss rf = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkNativeTable (absNativeParts p) (absCtorsL ctors_a) (absLIdxLL sortss)
        lf) := by
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  clear hrun
  rw [arena.inductives.native_install.check_native_table, checkNativeTable.eq_def]
  simp only [absNativeParts, absInductiveShape, absCtorsL, absLIdxLL]
  have hne : ∀ {α : Type} (v : alloc.vec.Vec α), v.val.length ≠ 1 →
      alloc.vec.Vec.len v ≠ 1#usize := by
    intro α v h1 h; apply h1
    have : (alloc.vec.Vec.len v).val = 1 := by rw [h]; rfl
    simpa [alloc.vec.Vec.len] using this
  have hle1 : ∀ {α : Type} (v : alloc.vec.Vec α), v.val.length = 1 →
      alloc.vec.Vec.len v = 1#usize := by
    intro α v h1
    have : (alloc.vec.Vec.len v).val = 1 := by simpa [alloc.vec.Vec.len] using h1
    scalar_tac
  rcases hc : ctors_a.val with _ | ⟨c, _ | ⟨c2, rest⟩⟩
  · simp only [bne_iff_ne, ne_eq, hne ctors_a (by simp [hc]), not_false_eq_true, if_true,
      List.map_nil]
    lockstep
  rotate_left
  · simp only [bne_iff_ne, ne_eq, hne ctors_a (by simp [hc]), not_false_eq_true, if_true,
      List.map_cons]
    lockstep
  have hc1 := hle1 ctors_a (by simp [hc])
  have hidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      (arena.env.IConstantVal × Std.U64)) ctors_a 0#usize = ok c := by
    rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
    simp [hc]
  simp only [hc1, bne_self_eq_false, Bool.false_eq_true, if_false, hidx, List.map_cons,
    List.map_nil]
  rcases hs : sortss.val with _ | ⟨ss, _ | ⟨s2, srest⟩⟩
  · simp only [bne_iff_ne, ne_eq, hne sortss (by simp [hs]), not_false_eq_true, if_true,
      List.map_nil]
    lockstep
  rotate_left
  · simp only [bne_iff_ne, ne_eq, hne sortss (by simp [hs]), not_false_eq_true, if_true,
      List.map_cons]
    lockstep
  have hs1 := hle1 sortss (by simp [hs])
  have hsidx : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      (alloc.vec.Vec arena.handle.LIdx)) sortss 0#usize = ok ss := by
    rw [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize]
    simp [hs]
  simp only [hs1, bne_self_eq_false, Bool.false_eq_true, if_false, hsidx, List.map_cons,
    List.map_nil]
  lockstep

open Lockstep in
@[lockstep] theorem check_native_table_ls
    {pers st lst}
    {p : arena.inductives.native_parts.NativeParts}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {sortss : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx)}
    {rf lf}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI (arena.inductives.native_install.check_native_table pers st p ctors_a sortss rf) lst
      (checkNativeTable (absNativeParts p) (absCtorsL ctors_a) (absLIdxLL sortss)
        lf) :=
  LS.ofSimRel₀ fun _ h => check_native_table_refines hrel hinv hfe h

/-! ## The two-pass install -/

/-- `rec_ctor_kinds_all` ⊑ `recCtorKindsAll` from the cursor on, with the
accumulated kind lists in front. -/
theorem rec_ctor_kinds_all_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {i : Std.Usize}
    {out : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_install.rec_ctor_kinds_all pers st t lps n_p
      n_idx ctors_a i out = ok o) :
    Sim₀ (Option.map absKindLL) pers lst o
      (do pure ((← recCtorKindsAllSpec (absNIdx t) (absNIdxL lps) (absU n_p)
        (absU n_idx) (absCtorsLFrom ctors_a i)).map
          fun r => absKindLL out ++ r)) := by
  sorry

open Lockstep in
@[lockstep] theorem rec_ctor_kinds_all_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {i : Std.Usize}
    {out : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (Option.map absKindLL) a) (arena.inductives.native_install.rec_ctor_kinds_all pers st t lps n_p n_idx ctors_a i out) lst
      (do pure ((← recCtorKindsAllSpec (absNIdx t) (absNIdxL lps) (absU n_p)
        (absU n_idx) (absCtorsLFrom ctors_a i)).map
          fun r => absKindLL out ++ r)) :=
  LS.ofSim₀ fun _ h => rec_ctor_kinds_all_refines hrel hinv h

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

open Lockstep in
/-- `kinds_any_twin` at the cursor `0` (and an empty accumulator): the
form a caller's twin has, so the `TwinEq` rewrites it. -/
@[lockstep] theorem kinds_any_twin0
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind}
    {k : arena.inductives.native_parts.RecFieldKind} :
    LSP (arena.inductives.native_install.kinds_any ks k 0#usize) (fun o => TwinEq ((absKindL ks).any (· == absRecFieldKind k)) (o)) := by
  intro o h
  have h' := (kinds_any_refines h).symm
  simpa [Lockstep.TwinEq, absKindLFrom, absKindL, alloc.vec.Vec.new] using h'

open Lockstep in
@[lockstep] theorem kinds_any_twin
    {ks : alloc.vec.Vec arena.inductives.native_parts.RecFieldKind}
    {k : arena.inductives.native_parts.RecFieldKind}
    {i : Std.Usize} :
    LSP (arena.inductives.native_install.kinds_any ks k i) (fun o => TwinEq ((absKindLFrom ks i).any (· == absRecFieldKind k)) (o)) :=
  fun o h => (kinds_any_refines h).symm

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

open Lockstep in
/-- `kindss_any_twin` at the cursor `0` (and an empty accumulator): the
form a caller's twin has, so the `TwinEq` rewrites it. -/
@[lockstep] theorem kindss_any_twin0
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {k : arena.inductives.native_parts.RecFieldKind} :
    LSP (arena.inductives.native_install.kindss_any kinds k 0#usize) (fun o => TwinEq ((absKindLL kinds).any fun ks => ks.any (· == absRecFieldKind k)) (o)) := by
  intro o h
  have h' := (kindss_any_refines h).symm
  simpa [Lockstep.TwinEq, absKindLLFrom, absKindLL, alloc.vec.Vec.new] using h'

open Lockstep in
@[lockstep] theorem kindss_any_twin
    {kinds : alloc.vec.Vec (alloc.vec.Vec arena.inductives.native_parts.RecFieldKind)}
    {k : arena.inductives.native_parts.RecFieldKind}
    {i : Std.Usize} :
    LSP (arena.inductives.native_install.kindss_any kinds k i) (fun o => TwinEq ((absKindLLFrom kinds i).any fun ks => ks.any (· == absRecFieldKind k)) (o)) :=
  fun o h => (kindss_any_refines h).symm

/-- `classify_fix_kinds` ⊑ `classifyFixKinds` — **the fields' kinds, classified
at install** (con-leche's task #210 Part D). -/
theorem classify_fix_kinds_refines {pers st lst} {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx} {n_p n_idx : Std.U64}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.inductives.native_install.classify_fix_kinds pers st t lps n_p
      n_idx ctors_a = ok o) :
    Sim₀ absKindLL pers lst o
      (classifyFixKinds (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absCtorsL ctors_a)) := by
  sorry

open Lockstep in
@[lockstep] theorem classify_fix_kinds_ls
    {pers st lst}
    {t : arena.handle.NIdx}
    {lps : alloc.vec.Vec arena.handle.NIdx}
    {n_p n_idx : Std.U64}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absKindLL a) (arena.inductives.native_install.classify_fix_kinds pers st t lps n_p n_idx ctors_a) lst
      (classifyFixKinds (absNIdx t) (absNIdxL lps) (absU n_p) (absU n_idx)
        (absCtorsL ctors_a)) :=
  LS.ofSim₀ fun _ h => classify_fix_kinds_refines hrel hinv h

/-- `check_native_pass_kinds` ⊑ `checkNativePass`'s tail. -/
theorem check_native_pass_kinds_refines {pers st lst} {rf1 lf1}
    {cv_ta : arena.env.IConstantVal}
    {p_c : arena.inductives.native_parts.NativeParts}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {sortss : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx)} {is_rec : Bool} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf1 lf1)
    (hrun : arena.inductives.native_install.check_native_pass_kinds pers st rf1 cv_ta
      p_c ctors_a sortss is_rec = ok o) :
    SimRel₀ (fun r v => NativePassRel r.1 v.1 ∧ v.2 = r.2) pers lst o
      (checkNativePassKindsSpec lf1 (absIConstantVal cv_ta) (absNativeParts p_c)
        (absCtorsL ctors_a) (absLIdxLL sortss) is_rec) := by
  sorry

open Lockstep in
@[lockstep] theorem check_native_pass_kinds_ls
    {pers st lst}
    {rf1 lf1}
    {cv_ta : arena.env.IConstantVal}
    {p_c : arena.inductives.native_parts.NativeParts}
    {ctors_a : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {sortss : alloc.vec.Vec (alloc.vec.Vec arena.handle.LIdx)}
    {is_rec : Bool}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf1 lf1) :
    LS pers (fun r v => NativePassRel r.1 v.1 ∧ v.2 = r.2) (arena.inductives.native_install.check_native_pass_kinds pers st rf1 cv_ta p_c ctors_a sortss is_rec) lst
      (checkNativePassKindsSpec lf1 (absIConstantVal cv_ta) (absNativeParts p_c)
        (absCtorsL ctors_a) (absLIdxLL sortss) is_rec) :=
  LS.ofSimRel₀ fun _ h => check_native_pass_kinds_refines hrel hinv hfe h

/-- `check_native_pass` ⊑ `checkNativePass` — **one pass over the former and
the constructors** (con-leche's task #268) at a given `is_rec` verdict. -/
theorem check_native_pass_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rf lf} {p0 : arena.inductives.native_parts.NativeParts} {is_rec : Bool} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hrun : arena.inductives.native_install.check_native_pass pers st mode rf p0
      is_rec = ok o) :
    SimRel₀ (fun r v => NativePassRel r.1 v.1 ∧ v.2 = r.2) pers lst o
      (checkNativePass (ConRon.Refine.absMode mode) lf (absNativeParts p0)
        is_rec) := by
  refine Lockstep.LS.toSimRel₀ ?_ hrun
  rw [arena.inductives.native_install.check_native_pass, checkNativePass]
  lockstep

open Lockstep in
@[lockstep] theorem check_native_pass_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rf lf}
    {p0 : arena.inductives.native_parts.NativeParts}
    {is_rec : Bool}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers (fun r v => NativePassRel r.1 v.1 ∧ v.2 = r.2) (arena.inductives.native_install.check_native_pass pers st mode rf p0 is_rec) lst
      (checkNativePass (ConRon.Refine.absMode mode) lf (absNativeParts p0)
        is_rec) :=
  LS.ofSimRel₀ fun _ h => check_native_pass_refines hrel hinv hfe h

/-- `check_native_tail_install` ⊑ `checkNativeTail`'s install stage. -/
theorem check_native_tail_install_refines {pers st lst}
    {mode : kernel.env.CheckMode} {rq : arena.inductives.native_install.NativePass}
    {lq : NativePass} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hq : NativePassRel rq lq)
    (hrun : arena.inductives.native_install.check_native_tail_install pers st mode rq
      = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkNativeTailInstallSpec (ConRon.Refine.absMode mode) lq) := by
  sorry

open Lockstep in
@[lockstep] theorem check_native_tail_install_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rq : arena.inductives.native_install.NativePass}
    {lq : NativePass}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hq : NativePassRel rq lq) :
    LS pers IFEnvRelI (arena.inductives.native_install.check_native_tail_install pers st mode rq) lst
      (checkNativeTailInstallSpec (ConRon.Refine.absMode mode) lq) :=
  LS.ofSimRel₀ fun _ h => check_native_tail_install_refines hrel hinv hq h

/-- `check_native_tail_kinds` ⊑ `checkNativeTail`'s kind stage.  **Finding
19's visibility bound**: the port lowers `env1.visible_below` by one to hide
the type former's row (and, since task #97-T2-LOCKSTEP lane Inductives round 4,
hands `native_fields_ok` that LOWERED counter); the twin reads
`q.env₁.restrictTo (q.env₁.visibleBelow - 1)`, the same view.  No premise on
the twin's environment: `hpre` is gone. -/
theorem check_native_tail_kinds_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rq : arena.inductives.native_install.NativePass} {lq : NativePass} {lf} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hq : NativePassRel rq lq)
    (hrun : arena.inductives.native_install.check_native_tail_kinds pers st mode rq
      = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkNativeTailKindsSpec (ConRon.Refine.absMode mode) lf lq) := by
  sorry

open Lockstep in
@[lockstep] theorem check_native_tail_kinds_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rq : arena.inductives.native_install.NativePass}
    {lq : NativePass}
    {lf}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hq : NativePassRel rq lq) :
    LS pers IFEnvRelI (arena.inductives.native_install.check_native_tail_kinds pers st mode rq) lst
      (checkNativeTailKindsSpec (ConRon.Refine.absMode mode) lf lq) :=
  LS.ofSimRel₀ fun _ h => check_native_tail_kinds_refines hrel hinv hq h

/-- `check_native_tail_sorts` ⊑ `checkNativeTail`'s index-sort stage. -/
theorem check_native_tail_sorts_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rq : arena.inductives.native_install.NativePass} {lq : NativePass} {lf} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hq : NativePassRel rq lq)
    (hrun : arena.inductives.native_install.check_native_tail_sorts pers st mode rq
      = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkNativeTailSortsSpec (ConRon.Refine.absMode mode) lf lq) := by
  sorry

open Lockstep in
@[lockstep] theorem check_native_tail_sorts_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rq : arena.inductives.native_install.NativePass}
    {lq : NativePass}
    {lf}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hq : NativePassRel rq lq) :
    LS pers IFEnvRelI (arena.inductives.native_install.check_native_tail_sorts pers st mode rq) lst
      (checkNativeTailSortsSpec (ConRon.Refine.absMode mode) lf lq) :=
  LS.ofSimRel₀ fun _ h => check_native_tail_sorts_refines hrel hinv hq h

/-- `check_native_tail` ⊑ `checkNativeTail` — **the install after the pass**
(con-leche's task #268). -/
theorem check_native_tail_refines {pers st lst} {mode : kernel.env.CheckMode}
    {rq : arena.inductives.native_install.NativePass} {lq : NativePass} {lf} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hq : NativePassRel rq lq)
    (hrun : arena.inductives.native_install.check_native_tail pers st mode rq
      = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkNativeTail (ConRon.Refine.absMode mode) lf lq) := by
  sorry

open Lockstep in
@[lockstep] theorem check_native_tail_ls
    {pers st lst}
    {mode : kernel.env.CheckMode}
    {rq : arena.inductives.native_install.NativePass}
    {lq : NativePass}
    {lf}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hq : NativePassRel rq lq) :
    LS pers IFEnvRelI (arena.inductives.native_install.check_native_tail pers st mode rq) lst
      (checkNativeTail (ConRon.Refine.absMode mode) lf lq) :=
  LS.ofSimRel₀ fun _ h => check_native_tail_refines hrel hinv hq h

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

open Lockstep in
/-- `ctor_name_seen_twin` at the cursor `0` (and an empty accumulator): the
form a caller's twin has, so the `TwinEq` rewrites it. -/
@[lockstep] theorem ctor_name_seen_twin0
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {n : arena.handle.NIdx} :
    LSP (arena.inductives.native_install.ctor_name_seen ctors 0#usize n) (fun o => TwinEq (((absCtorsL ctors).map (·.1.name)).contains (absNIdx n)) (o)) := by
  intro o h
  have h' := (ctor_name_seen_refines h).symm
  simpa [Lockstep.TwinEq, absCtorsLFrom, absCtorsL, alloc.vec.Vec.new] using h'

open Lockstep in
@[lockstep] theorem ctor_name_seen_twin
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {i : Std.Usize}
    {n : arena.handle.NIdx} :
    LSP (arena.inductives.native_install.ctor_name_seen ctors i n) (fun o => TwinEq (((absCtorsLFrom ctors i).map (·.1.name)).contains (absNIdx n)) (o)) :=
  fun o h => (ctor_name_seen_refines h).symm

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

open Lockstep in
/-- `ctor_names_nodup_twin` at the cursor `0` (and an empty accumulator): the
form a caller's twin has, so the `TwinEq` rewrites it. -/
@[lockstep] theorem ctor_names_nodup_twin0
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)} :
    LSP (arena.inductives.native_install.ctor_names_nodup ctors 0#usize) (fun o => TwinEq (decide (((absCtorsL ctors).map (·.1.name)).Nodup)) (o)) := by
  intro o h
  have h' := (ctor_names_nodup_refines h).symm
  simpa [Lockstep.TwinEq, absCtorsLFrom, absCtorsL, alloc.vec.Vec.new] using h'

open Lockstep in
@[lockstep] theorem ctor_names_nodup_twin
    {ctors : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)}
    {i : Std.Usize} :
    LSP (arena.inductives.native_install.ctor_names_nodup ctors i) (fun o => TwinEq (decide (((absCtorsLFrom ctors i).map (·.1.name)).Nodup)) (o)) :=
  fun o h => (ctor_names_nodup_refines h).symm

/-- `check_native` ⊑ `checkNative` — check and install a **direct recursive
block**: the distinct names, the pass over the former and the constructors —
again where the record's syntactic reading overshot — and the install after
it. -/
theorem check_native_refines {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {p0 : arena.inductives.native_parts.NativeParts} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf)
    (hrun : arena.inductives.native_install.check_native pers st mode rf p0 = ok o) :
    SimRel₀ IFEnvRelI pers lst o
      (checkNative (ConRon.Refine.absMode mode) lf (absNativeParts p0)) := by
  sorry

open Lockstep in
@[lockstep] theorem check_native_ls {pers st lst} {mode : kernel.env.CheckMode} {rf lf}
    {p0 : arena.inductives.native_parts.NativeParts}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hfe : IFEnvRelI rf lf) :
    LS pers IFEnvRelI
      (arena.inductives.native_install.check_native pers st mode rf p0) lst
      (checkNative (ConRon.Refine.absMode mode) lf (absNativeParts p0)) :=
  LS.ofSimRel₀ fun _ h => check_native_refines hrel hinv hfe h

/-! ## The axiom census

The nine closed `_refines` of this module read `[propext, Classical.choice,
Quot.sound]` and nothing else; the dearest of the scans stands for them. -/

/-- info: 'ConRon.Refine2.ctor_names_nodup_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ctor_names_nodup_refines


end ConRon.Refine2

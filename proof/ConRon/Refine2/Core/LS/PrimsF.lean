/-
# `ConRon.Refine2.Core.LS.PrimsF` — region F's primitive pairs

Task #97-P5-Core round 5, region F (the `defeq` loop).  The `@[lockstep]`
pairs the `defeq` bodies need that no other file has: the three pin reads the
literal arms test against (restated over `AStateRel₀` from
`Refine2/Checker/Pins.lean`, whose proofs read only `hrel.pins`), and the
Rust-only scalar steps of the literal and binder arms.
-/
import ConRon.Refine2.Core.LS.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.PF

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

/-! ## The pin table, over `AStateRel₀` -/

/-- `Refine2/Checker/Pins.lean`'s `pin_at_refines`, over `AStateRel₀` (it reads
only `hrel.pins`). -/
theorem pin_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (i : Std.Usize) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_at st i) st lst (pinAt (absSz i)) := by
  intro o hrun
  rw [arena.pins.pin_at] at hrun
  have hnames := hrel.pins.names
  have hlen : lst.pins.names.size = st.pins.names.val.length := by
    have h := congrArg List.length hnames
    simpa using h
  have hrun2 : (Arena.pinAt (absSz i)).run lst
      = (if h : absSz i < lst.pins.names.size
         then Except.ok (lst.pins.names[absSz i], lst)
         else Except.error
           (Arena.CheckError.internal "arena: reserved-name pins not interned")) := by
    by_cases h : absSz i < lst.pins.names.size
    · rw [dif_pos h]
      show (Arena.pinAt (absSz i)) lst = _
      rw [Arena.pinAt]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, StateT.pure, Except.pure, Except.bind, dif_pos h]
    · rw [dif_neg h]
      show (Arena.pinAt (absSz i)) lst = _
      rw [Arena.pinAt]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, Except.pure, Except.bind, dif_neg h,
        Arena.fail, throwThe, MonadExceptOf.throw,
        Function.comp_apply, StateT.lift]
  split at hrun
  case isTrue hge =>
    obtain ⟨sl, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨cps, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.monad.fail] at hrun
    have h2 : core.result.Result.Err (T := arena.handle.NIdx)
        (kernel.core_types.CheckError.Internal cps) = o := Result.ok_injective hrun
    subst h2
    have hnl : ¬ (absSz i < lst.pins.names.size) := by
      rw [hlen]
      have hle : st.pins.names.val.length ≤ i.val := by scalar_tac
      show ¬ (i.val < st.pins.names.val.length)
      omega
    exact AErrSim.internal (s := "arena: reserved-name pins not interned")
      (by rw [hrun2, dif_neg hnl])
  case isFalse hlt =>
    obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨n1, hn1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 : core.result.Result.Ok n1 = o := Result.ok_injective hrun
    subst h2
    rw [dupId_nidx _ _ hn1]
    obtain ⟨hlt2, rfl⟩ := ConRon.Refine.ExprOps.vec_index_val hn
    have hlt3 : absSz i < lst.pins.names.size := by rw [hlen]; exact hlt2
    refine ⟨_, lst, ?_, rfl, hrel, hinv⟩
    show (Arena.pinAt (absSz i)).run lst = _
    rw [hrun2, dif_pos hlt3]
    have hi : lst.pins.names.toList[absSz i]? =
        (st.pins.names.val.map absNIdx)[absSz i]? := by rw [hnames]
    simp only [List.getElem?_map, Array.getElem?_toList] at hi
    have hsome : lst.pins.names[absSz i]? = some (absNIdx st.pins.names.val[absSz i]) := by
      simpa [hlt2] using hi
    rw [Array.getElem?_eq_getElem hlt3] at hsome
    rw [Option.some_inj.mp hsome]

@[lockstep] theorem pin_nat_zero_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_zero st) st lst pinNatZero := by
  have h := pin_at_ls hrel hinv arena.pins.PIN_NAT_ZERO
  have hc : absSz arena.pins.PIN_NAT_ZERO = Arena.PIN_NAT_ZERO := by
    show (arena.pins.PIN_NAT_ZERO).val = _
    rw [arena.pins.PIN_NAT_ZERO]; rfl
  rw [hc] at h
  rw [arena.pins.pin_nat_zero]; exact h

@[lockstep] theorem pin_nat_succ_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_succ st) st lst pinNatSucc := by
  have h := pin_at_ls hrel hinv arena.pins.PIN_NAT_SUCC
  have hc : absSz arena.pins.PIN_NAT_SUCC = Arena.PIN_NAT_SUCC := by
    show (arena.pins.PIN_NAT_SUCC).val = _
    rw [arena.pins.PIN_NAT_SUCC]; rfl
  rw [hc] at h
  rw [arena.pins.pin_nat_succ]; exact h

@[lockstep] theorem pin_string_of_list_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_string_of_list st) st lst
      pinStringOfList := by
  have h := pin_at_ls hrel hinv arena.pins.PIN_STRING_OF_LIST
  have hc : absSz arena.pins.PIN_STRING_OF_LIST = Arena.PIN_STRING_OF_LIST := by
    show (arena.pins.PIN_STRING_OF_LIST).val = _
    rw [arena.pins.PIN_STRING_OF_LIST]; rfl
  rw [hc] at h
  rw [arena.pins.pin_string_of_list]; exact h

/-! ## The `const` projection -/

attribute [lockstep_simp] absConstT

/-- `arena::monad::view_const` against `Arena.viewConst` — the typed
projection a tag-guarded `view` becomes (`LS.twin_view_const`). -/
@[lockstep] theorem view_const_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absConstT a) (arena.monad.view_const pers st h) st lst
      (Arena.viewConst (absEIdx h)) :=
  LSV.of_store_read (F := fun s => s.viewConst (absEIdx h)) (fun _ => rfl)
    (fun _ hr => by rw [arena.monad.view_const] at hr; exact estore_view_const_abs hrel.store hr)
    hrel hinv

/-! ## Handle equality: the port's `eq2` is the twin's `==`/`=`

Every handle kind is a word; `eq2` compares the words, and the abstraction is
injective.  The conclusions are in `decide` form, and the twin's `==` on a
handle (a `LawfulBEq`) is `decide` by `idx_beq_decide`. -/

@[lockstep_simp] theorem idx_beq_decide {k : IdxKind} (a b : Idx k) :
    (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

private theorem word_decide {k : IdxKind} {α : Type} (w : α → Std.U32)
    (A : α → Idx k) (hA : ∀ x, A x = ⟨absU32 (w x)⟩) (a b : α) :
    decide (w a = w b) = decide (A a = A b) := by
  simp only [decide_eq_decide, hA]
  constructor
  · intro h; rw [h]
  · intro h
    have := congrArg Idx.word h
    exact absU32_inj this

@[lockstep] theorem eidx_eq2_ls (a b : arena.handle.EIdx) :
    LSP (arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun r => r = decide (absEIdx a = absEIdx b)) := by
  intro r h
  rw [arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  cases Result.ok_injective h
  exact word_decide arena.handle.EIdx.word absEIdx (fun _ => rfl) a b

@[lockstep] theorem nidx_eq2_ls (a b : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun r => r = decide (absNIdx a = absNIdx b)) := by
  intro r h
  rw [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  cases Result.ok_injective h
  exact word_decide arena.handle.NIdx.word absNIdx (fun _ => rfl) a b

@[lockstep] theorem lsidx_eq2_ls (a b : arena.handle.LsIdx) :
    LSP (arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun r => r = decide (absLsIdx a = absLsIdx b)) := by
  intro r h
  rw [arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  cases Result.ok_injective h
  exact word_decide arena.handle.LsIdx.word absLsIdx (fun _ => rfl) a b

@[lockstep] theorem bmidx_eq2_ls (a b : arena.handle.BMIdx) :
    LSP (arena.handle.BMIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun r => r = decide (absBMIdx a = absBMIdx b)) := by
  intro r h
  rw [arena.handle.BMIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  cases Result.ok_injective h
  exact word_decide arena.handle.BMIdx.word absBMIdx (fun _ => rfl) a b

/-! ## Spine lengths -/

@[lockstep_simp] theorem absEIdxList_length' (v : alloc.vec.Vec arena.handle.EIdx) :
    (ExprOps.absEIdxList v).length = v.val.length := by
  simp [ExprOps.absEIdxList]

@[lockstep_simp] theorem vec_len_eq_iff {α : Type} (v w : alloc.vec.Vec α) :
    (v.len = w.len) = (v.val.length = w.val.length) := by
  apply propext
  constructor
  · intro h
    have := congrArg UScalar.val h
    simpa [alloc.vec.Vec.len_val] using this
  · intro h
    apply Aeneas.Std.UScalar.eq_imp
    simpa [alloc.vec.Vec.len_val] using h

end ConRon.Refine2.Lockstep.PF

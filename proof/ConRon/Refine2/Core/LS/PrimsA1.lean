/-
# `ConRon.Refine2.Core.LS.PrimsA1` — region A1's primitive pairs

Task #97-P5-Core round 5, region A1 (the environment / level / name leaves).
The `@[lockstep]` pairs the leaves below the Core tier need and no earlier
file states over the lockstep relation `AStateRel₀`:

* the pin table's readers (`arena::pins::pin_*` against `Arena.pin*`) —
  `Refine2/Checker/Pins.lean`'s proofs restated over `AStateRel₀` (they only
  read `hrel.pins`), as `LSR` reads;
* the level / name readbacks (`read_level_m`, `read_levels_m`, `read_name_m`,
  `read_names_m`) over `AStateRel₀`;
* the pure `kernel::level` operations as `LSP` facts against the twin's pure
  `Level` functions;
* handle `eq2`/`dup2` on `NIdx`/`LIdx`/`LsIdx`.
-/
import ConRon.Refine2.Core.LS.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.PA1

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep
open ConRon.Refine.HashMap (Eq2Fwd DupId)
open ConRon.Refine.HashMap2 (Inv KeysOk RelOn toFun sl_v)

/-! ## The pin table

`Refine2/Checker/Shape.lean`'s `SimRE` (a reader that can fail and returns no
state), under a local name so that this file does not import the Checker
tier. -/

def PinRE {α β : Type} (A : α → β) (lst : AState)
    (o : core.result.Result α kernel.core_types.CheckError) (x : AM β) : Prop :=
  match o with
  | .Ok r => x.run lst = .ok (A r, lst)
  | .Err e => AErrSim e (x.run lst)

theorem pinRE_lsr {α β : Type} {A : α → β} {pers st lst}
    {m : Result (core.result.Result α kernel.core_types.CheckError)} {x : AM β}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (h : ∀ o, m = ok o → PinRE A lst o x) : LSR pers (fun a b => b = A a) m st lst x := by
  intro o hm
  have := h o hm
  cases o with
  | Err e => exact this
  | Ok a => exact ⟨_, lst, this, rfl, hrel, hinv⟩

theorem pins_ready_run₀ {pers st lst} {o : Bool}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pins_ready st = ok o) :
    o = pinsReady lst := by
  rw [arena.pins.pins_ready] at hrun
  have hnames := hrel.pins.names
  have hlen : lst.pins.names.size = st.pins.names.val.length := by
    have h := congrArg List.length hnames
    simpa using h
  have h2 := Result.ok_injective hrun
  subst h2
  show _ = decide (lst.pins.names.size = Arena.pinCount)
  rw [hlen]
  have hcount : (arena.pins.PIN_COUNT).val = Arena.pinCount := by
    rw [arena.pins.PIN_COUNT]; rfl
  have : (alloc.vec.Vec.len st.pins.names).val = st.pins.names.val.length :=
    alloc.vec.Vec.len_val _
  simp only [decide_eq_decide]
  constructor
  · intro h; rw [← this, ← hcount, h]
  · intro h
    apply Aeneas.Std.UScalar.eq_imp
    rw [this, hcount, h]

/-- `pin_at` ⊑ `pinAt` — **the one lemma the forty-nine below are instances
of**: the bounds branch and then `PinsRel.names`. -/
theorem pin_at_run₀ {pers st lst} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_at st i = ok o) :
    PinRE absNIdx lst o (pinAt (absSz i)) := by
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
    show (Arena.pinAt (absSz i)).run lst = _
    rw [hrun2, dif_pos hlt3]
    have hi : lst.pins.names.toList[absSz i]? =
        (st.pins.names.val.map absNIdx)[absSz i]? := by rw [hnames]
    simp only [List.getElem?_map, Array.getElem?_toList] at hi
    have hsome : lst.pins.names[absSz i]? = some (absNIdx st.pins.names.val[absSz i]) := by
      simpa [hlt2] using hi
    rw [Array.getElem?_eq_getElem hlt3] at hsome
    rw [Option.some_inj.mp hsome]

/-- `pin_reserved` ⊑ `pinReserved` — the nineteen reserved basis names, off
the table.  `arena::core`'s `reserved_basis_names` used to build and intern
all nineteen on every call, which task #97-P6-4a's profile put at 1.1 % of
`Init`'s cycles in the `Name` construction alone. -/
theorem pin_reserved_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_reserved st = ok o) :
    PinRE absNIdxList lst o pinReserved := by
  rw [arena.pins.pin_reserved] at hrun
  obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hbr := pins_ready_run₀ hrel hinv hb
  have hrun2 : (Arena.pinReserved).run lst
      = (if Arena.pinsReady lst
         then Except.ok (lst.pins.reserved, lst)
         else Except.error
           (Arena.CheckError.internal "arena: reserved-name pins not interned")) := by
    by_cases h : Arena.pinsReady lst = true
    · rw [if_pos h]
      show (Arena.pinReserved) lst = _
      rw [Arena.pinReserved]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, StateT.pure, Except.pure, Except.bind, if_pos h]
    · simp only [Bool.not_eq_true] at h
      rw [if_neg (by simp [h])]
      show (Arena.pinReserved) lst = _
      rw [Arena.pinReserved]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, Except.pure, Except.bind, h, Bool.false_eq_true, if_false,
        Arena.fail, throwThe, MonadExceptOf.throw, Function.comp_apply, StateT.lift]
  split at hrun
  case isTrue hbt =>
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 := Result.ok_injective hrun
    subst h2
    show (Arena.pinReserved).run lst = _
    rw [hrun2, if_pos (by rw [← hbr, hbt]), hrel.pins.reserved]
    simp only [absNIdxList, nidx_vec_dup_val hv]
  case isFalse hbf =>
    obtain ⟨sl, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨cps, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.monad.fail] at hrun
    have h2 := Result.ok_injective hrun
    subst h2
    refine AErrSim.internal (s := "arena: reserved-name pins not interned") ?_
    rw [hrun2, if_neg (by simp only [← hbr]; simpa using hbf)]

/-- `arena::core::reserved_basis_names` ⊑ `reservedBasisNames` — both are the
pin-table read, `pin_reserved` against `pinReserved` (twin fix D5 of task
#97-T2-LOCKSTEP: the twin used to re-intern thirteen of the nineteen). -/
theorem reserved_basis_names_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.reserved_basis_names st = ok o) :
    PinRE absNIdxList lst o reservedBasisNames := by
  rw [arena.core.reserved_basis_names] at hrun
  exact pin_reserved_run₀ hrel hinv hrun

/-- `pin_empty_levels` ⊑ `pinEmptyLevels`. -/
theorem pin_empty_levels_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_empty_levels st = ok o) :
    PinRE absLsIdx lst o pinEmptyLevels := by
  rw [arena.pins.pin_empty_levels] at hrun
  obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hbr := pins_ready_run₀ hrel hinv hb
  have hrun2 : (Arena.pinEmptyLevels).run lst
      = (if Arena.pinsReady lst
         then Except.ok (lst.pins.emptyLevels, lst)
         else Except.error
           (Arena.CheckError.internal "arena: reserved-name pins not interned")) := by
    by_cases h : Arena.pinsReady lst = true
    · rw [if_pos h]
      show (Arena.pinEmptyLevels) lst = _
      rw [Arena.pinEmptyLevels]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, StateT.pure, Except.pure, Except.bind, if_pos h]
    · simp only [Bool.not_eq_true] at h
      rw [if_neg (by simp [h])]
      show (Arena.pinEmptyLevels) lst = _
      rw [Arena.pinEmptyLevels]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, Except.pure, Except.bind, h, Bool.false_eq_true, if_false,
        Arena.fail, throwThe, MonadExceptOf.throw, Function.comp_apply, StateT.lift]
  split at hrun
  case isTrue hbt =>
    obtain ⟨l, hl, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 := Result.ok_injective hrun
    subst h2
    rw [dupId_lsidx _ _ hl]
    show (Arena.pinEmptyLevels).run lst = _
    rw [hrun2, if_pos (by rw [← hbr, hbt]), hrel.pins.emptyLevels]
  case isFalse hbf =>
    obtain ⟨sl, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨cps, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.monad.fail] at hrun
    have h2 := Result.ok_injective hrun
    subst h2
    refine AErrSim.internal (s := "arena: reserved-name pins not interned") ?_
    rw [hrun2, if_neg (by simp only [← hbr]; simpa using hbf)]

/-- `pin_zero_level` ⊑ `pinZeroLevel`. -/
theorem pin_zero_level_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_zero_level st = ok o) :
    PinRE absLIdx lst o pinZeroLevel := by
  rw [arena.pins.pin_zero_level] at hrun
  obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hbr := pins_ready_run₀ hrel hinv hb
  have hrun2 : (Arena.pinZeroLevel).run lst
      = (if Arena.pinsReady lst
         then Except.ok (lst.pins.zeroLevel, lst)
         else Except.error
           (Arena.CheckError.internal "arena: reserved-name pins not interned")) := by
    by_cases h : Arena.pinsReady lst = true
    · rw [if_pos h]
      show (Arena.pinZeroLevel) lst = _
      rw [Arena.pinZeroLevel]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, StateT.pure, Except.pure, Except.bind, if_pos h]
    · simp only [Bool.not_eq_true] at h
      rw [if_neg (by simp [h])]
      show (Arena.pinZeroLevel) lst = _
      rw [Arena.pinZeroLevel]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, Except.pure, Except.bind, h, Bool.false_eq_true, if_false,
        Arena.fail, throwThe, MonadExceptOf.throw, Function.comp_apply, StateT.lift]
  split at hrun
  case isTrue hbt =>
    obtain ⟨l, hl, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 := Result.ok_injective hrun
    subst h2
    rw [dupId_lidx _ _ hl]
    show (Arena.pinZeroLevel).run lst = _
    rw [hrun2, if_pos (by rw [← hbr, hbt]), hrel.pins.zeroLevel]
  case isFalse hbf =>
    obtain ⟨sl, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨cps, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.monad.fail] at hrun
    have h2 := Result.ok_injective hrun
    subst h2
    refine AErrSim.internal (s := "arena: reserved-name pins not interned") ?_
    rw [hrun2, if_neg (by simp only [← hbr]; simpa using hbf)]

/-- `pin_sort_one` ⊑ `pinSortOne`. -/
theorem pin_sort_one_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_sort_one st = ok o) :
    PinRE absEIdx lst o pinSortOne := by
  rw [arena.pins.pin_sort_one] at hrun
  obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hbr := pins_ready_run₀ hrel hinv hb
  have hrun2 : (Arena.pinSortOne).run lst
      = (if Arena.pinsReady lst
         then Except.ok (lst.pins.sortOne, lst)
         else Except.error
           (Arena.CheckError.internal "arena: reserved-name pins not interned")) := by
    by_cases h : Arena.pinsReady lst = true
    · rw [if_pos h]
      show (Arena.pinSortOne) lst = _
      rw [Arena.pinSortOne]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, StateT.pure, Except.pure, Except.bind, if_pos h]
    · simp only [Bool.not_eq_true] at h
      rw [if_neg (by simp [h])]
      show (Arena.pinSortOne) lst = _
      rw [Arena.pinSortOne]
      simp only [Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Pure.pure, Except.pure, Except.bind, h, Bool.false_eq_true, if_false,
        Arena.fail, throwThe, MonadExceptOf.throw, Function.comp_apply, StateT.lift]
  split at hrun
  case isTrue hbt =>
    obtain ⟨l, hl, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 := Result.ok_injective hrun
    subst h2
    rw [dupId_eidx _ _ hl]
    show (Arena.pinSortOne).run lst = _
    rw [hrun2, if_pos (by rw [← hbr, hbt]), hrel.pins.sortOne]
  case isFalse hbf =>
    obtain ⟨sl, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨cps, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.monad.fail] at hrun
    have h2 := Result.ok_injective hrun
    subst h2
    refine AErrSim.internal (s := "arena: reserved-name pins not interned") ?_
    rw [hrun2, if_neg (by simp only [← hbr]; simpa using hbf)]

/-! ## The forty-nine named readers, one per slot

Each is `pin_at` at its own constant, and each lemma is `pin_at_run₀` after
that constant's value.  The order is `Arena/Pins.lean`'s, which is
`arena::pins`'s. -/

/-- `pin_eq` ⊑ `pinEq`, at slot `PIN_EQ`. -/
theorem pin_eq_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_eq st = ok o) :
    PinRE absNIdx lst o pinEq := by
  rw [arena.pins.pin_eq] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_EQ = Arena.PIN_EQ := by
    show (arena.pins.PIN_EQ).val = _
    rw [arena.pins.PIN_EQ]
    rfl
  rw [hc] at h
  exact h

/-- `pin_punit` ⊑ `pinPUnit`, at slot `PIN_PUNIT`. -/
theorem pin_punit_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_punit st = ok o) :
    PinRE absNIdx lst o pinPUnit := by
  rw [arena.pins.pin_punit] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_PUNIT = Arena.PIN_PUNIT := by
    show (arena.pins.PIN_PUNIT).val = _
    rw [arena.pins.PIN_PUNIT]
    rfl
  rw [hc] at h
  exact h

/-- `pin_punit_rec` ⊑ `pinPUnitRec`, at slot `PIN_PUNIT_REC`. -/
theorem pin_punit_rec_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_punit_rec st = ok o) :
    PinRE absNIdx lst o pinPUnitRec := by
  rw [arena.pins.pin_punit_rec] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_PUNIT_REC = Arena.PIN_PUNIT_REC := by
    show (arena.pins.PIN_PUNIT_REC).val = _
    rw [arena.pins.PIN_PUNIT_REC]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat` ⊑ `pinNat`, at slot `PIN_NAT`. -/
theorem pin_nat_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat st = ok o) :
    PinRE absNIdx lst o pinNat := by
  rw [arena.pins.pin_nat] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT = Arena.PIN_NAT := by
    show (arena.pins.PIN_NAT).val = _
    rw [arena.pins.PIN_NAT]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_zero` ⊑ `pinNatZero`, at slot `PIN_NAT_ZERO`. -/
theorem pin_nat_zero_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_zero st = ok o) :
    PinRE absNIdx lst o pinNatZero := by
  rw [arena.pins.pin_nat_zero] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_ZERO = Arena.PIN_NAT_ZERO := by
    show (arena.pins.PIN_NAT_ZERO).val = _
    rw [arena.pins.PIN_NAT_ZERO]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_succ` ⊑ `pinNatSucc`, at slot `PIN_NAT_SUCC`. -/
theorem pin_nat_succ_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_succ st = ok o) :
    PinRE absNIdx lst o pinNatSucc := by
  rw [arena.pins.pin_nat_succ] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_SUCC = Arena.PIN_NAT_SUCC := by
    show (arena.pins.PIN_NAT_SUCC).val = _
    rw [arena.pins.PIN_NAT_SUCC]
    rfl
  rw [hc] at h
  exact h

/-- `pin_quot_sound` ⊑ `pinQuotSound`, at slot `PIN_QUOT_SOUND`. -/
theorem pin_quot_sound_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_quot_sound st = ok o) :
    PinRE absNIdx lst o pinQuotSound := by
  rw [arena.pins.pin_quot_sound] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_QUOT_SOUND = Arena.PIN_QUOT_SOUND := by
    show (arena.pins.PIN_QUOT_SOUND).val = _
    rw [arena.pins.PIN_QUOT_SOUND]
    rfl
  rw [hc] at h
  exact h

/-- `pin_string` ⊑ `pinString`, at slot `PIN_STRING`. -/
theorem pin_string_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_string st = ok o) :
    PinRE absNIdx lst o pinString := by
  rw [arena.pins.pin_string] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_STRING = Arena.PIN_STRING := by
    show (arena.pins.PIN_STRING).val = _
    rw [arena.pins.PIN_STRING]
    rfl
  rw [hc] at h
  exact h

/-- `pin_string_of_list` ⊑ `pinStringOfList`, at slot `PIN_STRING_OF_LIST`. -/
theorem pin_string_of_list_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_string_of_list st = ok o) :
    PinRE absNIdx lst o pinStringOfList := by
  rw [arena.pins.pin_string_of_list] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_STRING_OF_LIST = Arena.PIN_STRING_OF_LIST := by
    show (arena.pins.PIN_STRING_OF_LIST).val = _
    rw [arena.pins.PIN_STRING_OF_LIST]
    rfl
  rw [hc] at h
  exact h

/-- `pin_list` ⊑ `pinList`, at slot `PIN_LIST`. -/
theorem pin_list_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_list st = ok o) :
    PinRE absNIdx lst o pinList := by
  rw [arena.pins.pin_list] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_LIST = Arena.PIN_LIST := by
    show (arena.pins.PIN_LIST).val = _
    rw [arena.pins.PIN_LIST]
    rfl
  rw [hc] at h
  exact h

/-- `pin_list_nil` ⊑ `pinListNil`, at slot `PIN_LIST_NIL`. -/
theorem pin_list_nil_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_list_nil st = ok o) :
    PinRE absNIdx lst o pinListNil := by
  rw [arena.pins.pin_list_nil] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_LIST_NIL = Arena.PIN_LIST_NIL := by
    show (arena.pins.PIN_LIST_NIL).val = _
    rw [arena.pins.PIN_LIST_NIL]
    rfl
  rw [hc] at h
  exact h

/-- `pin_list_cons` ⊑ `pinListCons`, at slot `PIN_LIST_CONS`. -/
theorem pin_list_cons_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_list_cons st = ok o) :
    PinRE absNIdx lst o pinListCons := by
  rw [arena.pins.pin_list_cons] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_LIST_CONS = Arena.PIN_LIST_CONS := by
    show (arena.pins.PIN_LIST_CONS).val = _
    rw [arena.pins.PIN_LIST_CONS]
    rfl
  rw [hc] at h
  exact h

/-- `pin_char` ⊑ `pinChar`, at slot `PIN_CHAR`. -/
theorem pin_char_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_char st = ok o) :
    PinRE absNIdx lst o pinChar := by
  rw [arena.pins.pin_char] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_CHAR = Arena.PIN_CHAR := by
    show (arena.pins.PIN_CHAR).val = _
    rw [arena.pins.PIN_CHAR]
    rfl
  rw [hc] at h
  exact h

/-- `pin_and` ⊑ `pinAnd`, at slot `PIN_AND`. -/
theorem pin_and_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_and st = ok o) :
    PinRE absNIdx lst o pinAnd := by
  rw [arena.pins.pin_and] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_AND = Arena.PIN_AND := by
    show (arena.pins.PIN_AND).val = _
    rw [arena.pins.PIN_AND]
    rfl
  rw [hc] at h
  exact h

/-- `pin_char_of_nat` ⊑ `pinCharOfNat`, at slot `PIN_CHAR_OF_NAT`. -/
theorem pin_char_of_nat_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_char_of_nat st = ok o) :
    PinRE absNIdx lst o pinCharOfNat := by
  rw [arena.pins.pin_char_of_nat] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_CHAR_OF_NAT = Arena.PIN_CHAR_OF_NAT := by
    show (arena.pins.PIN_CHAR_OF_NAT).val = _
    rw [arena.pins.PIN_CHAR_OF_NAT]
    rfl
  rw [hc] at h
  exact h

/-- `pin_sorry_ax` ⊑ `pinSorryAx`, at slot `PIN_SORRY_AX`. -/
theorem pin_sorry_ax_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_sorry_ax st = ok o) :
    PinRE absNIdx lst o pinSorryAx := by
  rw [arena.pins.pin_sorry_ax] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_SORRY_AX = Arena.PIN_SORRY_AX := by
    show (arena.pins.PIN_SORRY_AX).val = _
    rw [arena.pins.PIN_SORRY_AX]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_pred` ⊑ `pinNatPred`, at slot `PIN_NAT_PRED`. -/
theorem pin_nat_pred_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_pred st = ok o) :
    PinRE absNIdx lst o pinNatPred := by
  rw [arena.pins.pin_nat_pred] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_PRED = Arena.PIN_NAT_PRED := by
    show (arena.pins.PIN_NAT_PRED).val = _
    rw [arena.pins.PIN_NAT_PRED]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_add` ⊑ `pinNatAdd`, at slot `PIN_NAT_ADD`. -/
theorem pin_nat_add_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_add st = ok o) :
    PinRE absNIdx lst o pinNatAdd := by
  rw [arena.pins.pin_nat_add] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_ADD = Arena.PIN_NAT_ADD := by
    show (arena.pins.PIN_NAT_ADD).val = _
    rw [arena.pins.PIN_NAT_ADD]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_sub` ⊑ `pinNatSub`, at slot `PIN_NAT_SUB`. -/
theorem pin_nat_sub_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_sub st = ok o) :
    PinRE absNIdx lst o pinNatSub := by
  rw [arena.pins.pin_nat_sub] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_SUB = Arena.PIN_NAT_SUB := by
    show (arena.pins.PIN_NAT_SUB).val = _
    rw [arena.pins.PIN_NAT_SUB]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_mul` ⊑ `pinNatMul`, at slot `PIN_NAT_MUL`. -/
theorem pin_nat_mul_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_mul st = ok o) :
    PinRE absNIdx lst o pinNatMul := by
  rw [arena.pins.pin_nat_mul] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_MUL = Arena.PIN_NAT_MUL := by
    show (arena.pins.PIN_NAT_MUL).val = _
    rw [arena.pins.PIN_NAT_MUL]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_pow` ⊑ `pinNatPow`, at slot `PIN_NAT_POW`. -/
theorem pin_nat_pow_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_pow st = ok o) :
    PinRE absNIdx lst o pinNatPow := by
  rw [arena.pins.pin_nat_pow] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_POW = Arena.PIN_NAT_POW := by
    show (arena.pins.PIN_NAT_POW).val = _
    rw [arena.pins.PIN_NAT_POW]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_beq` ⊑ `pinNatBeq`, at slot `PIN_NAT_BEQ`. -/
theorem pin_nat_beq_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_beq st = ok o) :
    PinRE absNIdx lst o pinNatBeq := by
  rw [arena.pins.pin_nat_beq] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_BEQ = Arena.PIN_NAT_BEQ := by
    show (arena.pins.PIN_NAT_BEQ).val = _
    rw [arena.pins.PIN_NAT_BEQ]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_ble` ⊑ `pinNatBle`, at slot `PIN_NAT_BLE`. -/
theorem pin_nat_ble_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_ble st = ok o) :
    PinRE absNIdx lst o pinNatBle := by
  rw [arena.pins.pin_nat_ble] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_BLE = Arena.PIN_NAT_BLE := by
    show (arena.pins.PIN_NAT_BLE).val = _
    rw [arena.pins.PIN_NAT_BLE]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_div` ⊑ `pinNatDiv`, at slot `PIN_NAT_DIV`. -/
theorem pin_nat_div_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_div st = ok o) :
    PinRE absNIdx lst o pinNatDiv := by
  rw [arena.pins.pin_nat_div] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_DIV = Arena.PIN_NAT_DIV := by
    show (arena.pins.PIN_NAT_DIV).val = _
    rw [arena.pins.PIN_NAT_DIV]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_mod` ⊑ `pinNatMod`, at slot `PIN_NAT_MOD`. -/
theorem pin_nat_mod_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_mod st = ok o) :
    PinRE absNIdx lst o pinNatMod := by
  rw [arena.pins.pin_nat_mod] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_MOD = Arena.PIN_NAT_MOD := by
    show (arena.pins.PIN_NAT_MOD).val = _
    rw [arena.pins.PIN_NAT_MOD]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_gcd` ⊑ `pinNatGcd`, at slot `PIN_NAT_GCD`. -/
theorem pin_nat_gcd_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_gcd st = ok o) :
    PinRE absNIdx lst o pinNatGcd := by
  rw [arena.pins.pin_nat_gcd] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_GCD = Arena.PIN_NAT_GCD := by
    show (arena.pins.PIN_NAT_GCD).val = _
    rw [arena.pins.PIN_NAT_GCD]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_land` ⊑ `pinNatLand`, at slot `PIN_NAT_LAND`. -/
theorem pin_nat_land_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_land st = ok o) :
    PinRE absNIdx lst o pinNatLand := by
  rw [arena.pins.pin_nat_land] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_LAND = Arena.PIN_NAT_LAND := by
    show (arena.pins.PIN_NAT_LAND).val = _
    rw [arena.pins.PIN_NAT_LAND]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_lor` ⊑ `pinNatLor`, at slot `PIN_NAT_LOR`. -/
theorem pin_nat_lor_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_lor st = ok o) :
    PinRE absNIdx lst o pinNatLor := by
  rw [arena.pins.pin_nat_lor] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_LOR = Arena.PIN_NAT_LOR := by
    show (arena.pins.PIN_NAT_LOR).val = _
    rw [arena.pins.PIN_NAT_LOR]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_xor` ⊑ `pinNatXor`, at slot `PIN_NAT_XOR`. -/
theorem pin_nat_xor_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_xor st = ok o) :
    PinRE absNIdx lst o pinNatXor := by
  rw [arena.pins.pin_nat_xor] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_XOR = Arena.PIN_NAT_XOR := by
    show (arena.pins.PIN_NAT_XOR).val = _
    rw [arena.pins.PIN_NAT_XOR]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_shift_left` ⊑ `pinNatShiftLeft`, at slot `PIN_NAT_SHIFT_LEFT`. -/
theorem pin_nat_shift_left_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_shift_left st = ok o) :
    PinRE absNIdx lst o pinNatShiftLeft := by
  rw [arena.pins.pin_nat_shift_left] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_SHIFT_LEFT = Arena.PIN_NAT_SHIFT_LEFT := by
    show (arena.pins.PIN_NAT_SHIFT_LEFT).val = _
    rw [arena.pins.PIN_NAT_SHIFT_LEFT]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_shift_right` ⊑ `pinNatShiftRight`, at slot `PIN_NAT_SHIFT_RIGHT`. -/
theorem pin_nat_shift_right_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_shift_right st = ok o) :
    PinRE absNIdx lst o pinNatShiftRight := by
  rw [arena.pins.pin_nat_shift_right] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_SHIFT_RIGHT = Arena.PIN_NAT_SHIFT_RIGHT := by
    show (arena.pins.PIN_NAT_SHIFT_RIGHT).val = _
    rw [arena.pins.PIN_NAT_SHIFT_RIGHT]
    rfl
  rw [hc] at h
  exact h

/-- `pin_bool` ⊑ `pinBool`, at slot `PIN_BOOL`. -/
theorem pin_bool_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_bool st = ok o) :
    PinRE absNIdx lst o pinBool := by
  rw [arena.pins.pin_bool] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_BOOL = Arena.PIN_BOOL := by
    show (arena.pins.PIN_BOOL).val = _
    rw [arena.pins.PIN_BOOL]
    rfl
  rw [hc] at h
  exact h

/-- `pin_bool_true` ⊑ `pinBoolTrue`, at slot `PIN_BOOL_TRUE`. -/
theorem pin_bool_true_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_bool_true st = ok o) :
    PinRE absNIdx lst o pinBoolTrue := by
  rw [arena.pins.pin_bool_true] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_BOOL_TRUE = Arena.PIN_BOOL_TRUE := by
    show (arena.pins.PIN_BOOL_TRUE).val = _
    rw [arena.pins.PIN_BOOL_TRUE]
    rfl
  rw [hc] at h
  exact h

/-- `pin_bool_false` ⊑ `pinBoolFalse`, at slot `PIN_BOOL_FALSE`. -/
theorem pin_bool_false_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_bool_false st = ok o) :
    PinRE absNIdx lst o pinBoolFalse := by
  rw [arena.pins.pin_bool_false] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_BOOL_FALSE = Arena.PIN_BOOL_FALSE := by
    show (arena.pins.PIN_BOOL_FALSE).val = _
    rw [arena.pins.PIN_BOOL_FALSE]
    rfl
  rw [hc] at h
  exact h

/-- `pin_propext` ⊑ `pinPropext`, at slot `PIN_PROPEXT`. -/
theorem pin_propext_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_propext st = ok o) :
    PinRE absNIdx lst o pinPropext := by
  rw [arena.pins.pin_propext] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_PROPEXT = Arena.PIN_PROPEXT := by
    show (arena.pins.PIN_PROPEXT).val = _
    rw [arena.pins.PIN_PROPEXT]
    rfl
  rw [hc] at h
  exact h

/-- `pin_choice` ⊑ `pinChoice`, at slot `PIN_CHOICE`. -/
theorem pin_choice_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_choice st = ok o) :
    PinRE absNIdx lst o pinChoice := by
  rw [arena.pins.pin_choice] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_CHOICE = Arena.PIN_CHOICE := by
    show (arena.pins.PIN_CHOICE).val = _
    rw [arena.pins.PIN_CHOICE]
    rfl
  rw [hc] at h
  exact h

/-- `pin_iff` ⊑ `pinIff`, at slot `PIN_IFF`. -/
theorem pin_iff_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_iff st = ok o) :
    PinRE absNIdx lst o pinIff := by
  rw [arena.pins.pin_iff] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_IFF = Arena.PIN_IFF := by
    show (arena.pins.PIN_IFF).val = _
    rw [arena.pins.PIN_IFF]
    rfl
  rw [hc] at h
  exact h

/-- `pin_iff_intro` ⊑ `pinIffIntro`, at slot `PIN_IFF_INTRO`. -/
theorem pin_iff_intro_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_iff_intro st = ok o) :
    PinRE absNIdx lst o pinIffIntro := by
  rw [arena.pins.pin_iff_intro] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_IFF_INTRO = Arena.PIN_IFF_INTRO := by
    show (arena.pins.PIN_IFF_INTRO).val = _
    rw [arena.pins.PIN_IFF_INTRO]
    rfl
  rw [hc] at h
  exact h

/-- `pin_iff_rec` ⊑ `pinIffRec`, at slot `PIN_IFF_REC`. -/
theorem pin_iff_rec_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_iff_rec st = ok o) :
    PinRE absNIdx lst o pinIffRec := by
  rw [arena.pins.pin_iff_rec] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_IFF_REC = Arena.PIN_IFF_REC := by
    show (arena.pins.PIN_IFF_REC).val = _
    rw [arena.pins.PIN_IFF_REC]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nonempty` ⊑ `pinNonempty`, at slot `PIN_NONEMPTY`. -/
theorem pin_nonempty_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nonempty st = ok o) :
    PinRE absNIdx lst o pinNonempty := by
  rw [arena.pins.pin_nonempty] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NONEMPTY = Arena.PIN_NONEMPTY := by
    show (arena.pins.PIN_NONEMPTY).val = _
    rw [arena.pins.PIN_NONEMPTY]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nonempty_intro` ⊑ `pinNonemptyIntro`, at slot `PIN_NONEMPTY_INTRO`. -/
theorem pin_nonempty_intro_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nonempty_intro st = ok o) :
    PinRE absNIdx lst o pinNonemptyIntro := by
  rw [arena.pins.pin_nonempty_intro] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NONEMPTY_INTRO = Arena.PIN_NONEMPTY_INTRO := by
    show (arena.pins.PIN_NONEMPTY_INTRO).val = _
    rw [arena.pins.PIN_NONEMPTY_INTRO]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nonempty_rec` ⊑ `pinNonemptyRec`, at slot `PIN_NONEMPTY_REC`. -/
theorem pin_nonempty_rec_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nonempty_rec st = ok o) :
    PinRE absNIdx lst o pinNonemptyRec := by
  rw [arena.pins.pin_nonempty_rec] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_NONEMPTY_REC = Arena.PIN_NONEMPTY_REC := by
    show (arena.pins.PIN_NONEMPTY_REC).val = _
    rw [arena.pins.PIN_NONEMPTY_REC]
    rfl
  rw [hc] at h
  exact h

/-- `pin_true` ⊑ `pinTrue`, at slot `PIN_TRUE`. -/
theorem pin_true_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_true st = ok o) :
    PinRE absNIdx lst o pinTrue := by
  rw [arena.pins.pin_true] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_TRUE = Arena.PIN_TRUE := by
    show (arena.pins.PIN_TRUE).val = _
    rw [arena.pins.PIN_TRUE]
    rfl
  rw [hc] at h
  exact h

/-- `pin_true_intro` ⊑ `pinTrueIntro`, at slot `PIN_TRUE_INTRO`. -/
theorem pin_true_intro_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_true_intro st = ok o) :
    PinRE absNIdx lst o pinTrueIntro := by
  rw [arena.pins.pin_true_intro] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_TRUE_INTRO = Arena.PIN_TRUE_INTRO := by
    show (arena.pins.PIN_TRUE_INTRO).val = _
    rw [arena.pins.PIN_TRUE_INTRO]
    rfl
  rw [hc] at h
  exact h

/-- `pin_trust_compiler` ⊑ `pinTrustCompiler`, at slot `PIN_TRUST_COMPILER`. -/
theorem pin_trust_compiler_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_trust_compiler st = ok o) :
    PinRE absNIdx lst o pinTrustCompiler := by
  rw [arena.pins.pin_trust_compiler] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_TRUST_COMPILER = Arena.PIN_TRUST_COMPILER := by
    show (arena.pins.PIN_TRUST_COMPILER).val = _
    rw [arena.pins.PIN_TRUST_COMPILER]
    rfl
  rw [hc] at h
  exact h

/-- `pin_reduce_nat` ⊑ `pinReduceNat`, at slot `PIN_REDUCE_NAT`. -/
theorem pin_reduce_nat_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_reduce_nat st = ok o) :
    PinRE absNIdx lst o pinReduceNat := by
  rw [arena.pins.pin_reduce_nat] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_REDUCE_NAT = Arena.PIN_REDUCE_NAT := by
    show (arena.pins.PIN_REDUCE_NAT).val = _
    rw [arena.pins.PIN_REDUCE_NAT]
    rfl
  rw [hc] at h
  exact h

/-- `pin_reduce_bool` ⊑ `pinReduceBool`, at slot `PIN_REDUCE_BOOL`. -/
theorem pin_reduce_bool_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_reduce_bool st = ok o) :
    PinRE absNIdx lst o pinReduceBool := by
  rw [arena.pins.pin_reduce_bool] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_REDUCE_BOOL = Arena.PIN_REDUCE_BOOL := by
    show (arena.pins.PIN_REDUCE_BOOL).val = _
    rw [arena.pins.PIN_REDUCE_BOOL]
    rfl
  rw [hc] at h
  exact h

/-- `pin_of_reduce_nat` ⊑ `pinOfReduceNat`, at slot `PIN_OF_REDUCE_NAT`. -/
theorem pin_of_reduce_nat_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_of_reduce_nat st = ok o) :
    PinRE absNIdx lst o pinOfReduceNat := by
  rw [arena.pins.pin_of_reduce_nat] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_OF_REDUCE_NAT = Arena.PIN_OF_REDUCE_NAT := by
    show (arena.pins.PIN_OF_REDUCE_NAT).val = _
    rw [arena.pins.PIN_OF_REDUCE_NAT]
    rfl
  rw [hc] at h
  exact h

/-- `pin_of_reduce_bool` ⊑ `pinOfReduceBool`, at slot `PIN_OF_REDUCE_BOOL`. -/
theorem pin_of_reduce_bool_run₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_of_reduce_bool st = ok o) :
    PinRE absNIdx lst o pinOfReduceBool := by
  rw [arena.pins.pin_of_reduce_bool] at hrun
  have h := pin_at_run₀ hrel hinv hrun
  have hc : absSz arena.pins.PIN_OF_REDUCE_BOOL = Arena.PIN_OF_REDUCE_BOOL := by
    show (arena.pins.PIN_OF_REDUCE_BOOL).val = _
    rw [arena.pins.PIN_OF_REDUCE_BOOL]
    rfl
  rw [hc] at h
  exact h


/-! ### As `@[lockstep]` reads -/

@[lockstep] theorem pin_reserved_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdxList a) (arena.pins.pin_reserved st) st lst pinReserved :=
  pinRE_lsr hrel hinv fun _ h => pin_reserved_run₀ hrel hinv h

@[lockstep] theorem reserved_basis_names_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdxList a) (arena.core.reserved_basis_names st) st lst reservedBasisNames :=
  pinRE_lsr hrel hinv fun _ h => reserved_basis_names_run₀ hrel hinv h

@[lockstep] theorem pin_empty_levels_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absLsIdx a) (arena.pins.pin_empty_levels st) st lst pinEmptyLevels :=
  pinRE_lsr hrel hinv fun _ h => pin_empty_levels_run₀ hrel hinv h

@[lockstep] theorem pin_zero_level_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absLIdx a) (arena.pins.pin_zero_level st) st lst pinZeroLevel :=
  pinRE_lsr hrel hinv fun _ h => pin_zero_level_run₀ hrel hinv h

@[lockstep] theorem pin_sort_one_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absEIdx a) (arena.pins.pin_sort_one st) st lst pinSortOne :=
  pinRE_lsr hrel hinv fun _ h => pin_sort_one_run₀ hrel hinv h

@[lockstep] theorem pin_eq_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_eq st) st lst pinEq :=
  pinRE_lsr hrel hinv fun _ h => pin_eq_run₀ hrel hinv h

@[lockstep] theorem pin_punit_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_punit st) st lst pinPUnit :=
  pinRE_lsr hrel hinv fun _ h => pin_punit_run₀ hrel hinv h

@[lockstep] theorem pin_punit_rec_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_punit_rec st) st lst pinPUnitRec :=
  pinRE_lsr hrel hinv fun _ h => pin_punit_rec_run₀ hrel hinv h

@[lockstep] theorem pin_nat_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat st) st lst pinNat :=
  pinRE_lsr hrel hinv fun _ h => pin_nat_run₀ hrel hinv h

@[lockstep] theorem pin_nat_zero_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_zero st) st lst pinNatZero :=
  pinRE_lsr hrel hinv fun _ h => pin_nat_zero_run₀ hrel hinv h

@[lockstep] theorem pin_nat_succ_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_succ st) st lst pinNatSucc :=
  pinRE_lsr hrel hinv fun _ h => pin_nat_succ_run₀ hrel hinv h

@[lockstep] theorem pin_quot_sound_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_quot_sound st) st lst pinQuotSound :=
  pinRE_lsr hrel hinv fun _ h => pin_quot_sound_run₀ hrel hinv h

@[lockstep] theorem pin_string_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_string st) st lst pinString :=
  pinRE_lsr hrel hinv fun _ h => pin_string_run₀ hrel hinv h

@[lockstep] theorem pin_string_of_list_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_string_of_list st) st lst pinStringOfList :=
  pinRE_lsr hrel hinv fun _ h => pin_string_of_list_run₀ hrel hinv h

@[lockstep] theorem pin_list_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_list st) st lst pinList :=
  pinRE_lsr hrel hinv fun _ h => pin_list_run₀ hrel hinv h

@[lockstep] theorem pin_list_nil_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_list_nil st) st lst pinListNil :=
  pinRE_lsr hrel hinv fun _ h => pin_list_nil_run₀ hrel hinv h

@[lockstep] theorem pin_list_cons_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_list_cons st) st lst pinListCons :=
  pinRE_lsr hrel hinv fun _ h => pin_list_cons_run₀ hrel hinv h

@[lockstep] theorem pin_char_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_char st) st lst pinChar :=
  pinRE_lsr hrel hinv fun _ h => pin_char_run₀ hrel hinv h

@[lockstep] theorem pin_and_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_and st) st lst pinAnd :=
  pinRE_lsr hrel hinv fun _ h => pin_and_run₀ hrel hinv h

@[lockstep] theorem pin_char_of_nat_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_char_of_nat st) st lst pinCharOfNat :=
  pinRE_lsr hrel hinv fun _ h => pin_char_of_nat_run₀ hrel hinv h

@[lockstep] theorem pin_sorry_ax_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_sorry_ax st) st lst pinSorryAx :=
  pinRE_lsr hrel hinv fun _ h => pin_sorry_ax_run₀ hrel hinv h

@[lockstep] theorem pin_nat_pred_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_pred st) st lst pinNatPred :=
  pinRE_lsr hrel hinv fun _ h => pin_nat_pred_run₀ hrel hinv h

@[lockstep] theorem pin_nat_add_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_add st) st lst pinNatAdd :=
  pinRE_lsr hrel hinv fun _ h => pin_nat_add_run₀ hrel hinv h

@[lockstep] theorem pin_nat_sub_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_sub st) st lst pinNatSub :=
  pinRE_lsr hrel hinv fun _ h => pin_nat_sub_run₀ hrel hinv h

@[lockstep] theorem pin_nat_mul_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_mul st) st lst pinNatMul :=
  pinRE_lsr hrel hinv fun _ h => pin_nat_mul_run₀ hrel hinv h

@[lockstep] theorem pin_nat_pow_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_pow st) st lst pinNatPow :=
  pinRE_lsr hrel hinv fun _ h => pin_nat_pow_run₀ hrel hinv h

@[lockstep] theorem pin_nat_beq_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_beq st) st lst pinNatBeq :=
  pinRE_lsr hrel hinv fun _ h => pin_nat_beq_run₀ hrel hinv h

@[lockstep] theorem pin_nat_ble_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_ble st) st lst pinNatBle :=
  pinRE_lsr hrel hinv fun _ h => pin_nat_ble_run₀ hrel hinv h

@[lockstep] theorem pin_nat_div_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_div st) st lst pinNatDiv :=
  pinRE_lsr hrel hinv fun _ h => pin_nat_div_run₀ hrel hinv h

@[lockstep] theorem pin_nat_mod_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_mod st) st lst pinNatMod :=
  pinRE_lsr hrel hinv fun _ h => pin_nat_mod_run₀ hrel hinv h

@[lockstep] theorem pin_nat_gcd_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_gcd st) st lst pinNatGcd :=
  pinRE_lsr hrel hinv fun _ h => pin_nat_gcd_run₀ hrel hinv h

@[lockstep] theorem pin_nat_land_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_land st) st lst pinNatLand :=
  pinRE_lsr hrel hinv fun _ h => pin_nat_land_run₀ hrel hinv h

@[lockstep] theorem pin_nat_lor_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_lor st) st lst pinNatLor :=
  pinRE_lsr hrel hinv fun _ h => pin_nat_lor_run₀ hrel hinv h

@[lockstep] theorem pin_nat_xor_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_xor st) st lst pinNatXor :=
  pinRE_lsr hrel hinv fun _ h => pin_nat_xor_run₀ hrel hinv h

@[lockstep] theorem pin_nat_shift_left_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_shift_left st) st lst pinNatShiftLeft :=
  pinRE_lsr hrel hinv fun _ h => pin_nat_shift_left_run₀ hrel hinv h

@[lockstep] theorem pin_nat_shift_right_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nat_shift_right st) st lst pinNatShiftRight :=
  pinRE_lsr hrel hinv fun _ h => pin_nat_shift_right_run₀ hrel hinv h

@[lockstep] theorem pin_bool_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_bool st) st lst pinBool :=
  pinRE_lsr hrel hinv fun _ h => pin_bool_run₀ hrel hinv h

@[lockstep] theorem pin_bool_true_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_bool_true st) st lst pinBoolTrue :=
  pinRE_lsr hrel hinv fun _ h => pin_bool_true_run₀ hrel hinv h

@[lockstep] theorem pin_bool_false_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_bool_false st) st lst pinBoolFalse :=
  pinRE_lsr hrel hinv fun _ h => pin_bool_false_run₀ hrel hinv h

@[lockstep] theorem pin_propext_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_propext st) st lst pinPropext :=
  pinRE_lsr hrel hinv fun _ h => pin_propext_run₀ hrel hinv h

@[lockstep] theorem pin_choice_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_choice st) st lst pinChoice :=
  pinRE_lsr hrel hinv fun _ h => pin_choice_run₀ hrel hinv h

@[lockstep] theorem pin_iff_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_iff st) st lst pinIff :=
  pinRE_lsr hrel hinv fun _ h => pin_iff_run₀ hrel hinv h

@[lockstep] theorem pin_iff_intro_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_iff_intro st) st lst pinIffIntro :=
  pinRE_lsr hrel hinv fun _ h => pin_iff_intro_run₀ hrel hinv h

@[lockstep] theorem pin_iff_rec_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_iff_rec st) st lst pinIffRec :=
  pinRE_lsr hrel hinv fun _ h => pin_iff_rec_run₀ hrel hinv h

@[lockstep] theorem pin_nonempty_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nonempty st) st lst pinNonempty :=
  pinRE_lsr hrel hinv fun _ h => pin_nonempty_run₀ hrel hinv h

@[lockstep] theorem pin_nonempty_intro_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nonempty_intro st) st lst pinNonemptyIntro :=
  pinRE_lsr hrel hinv fun _ h => pin_nonempty_intro_run₀ hrel hinv h

@[lockstep] theorem pin_nonempty_rec_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_nonempty_rec st) st lst pinNonemptyRec :=
  pinRE_lsr hrel hinv fun _ h => pin_nonempty_rec_run₀ hrel hinv h

@[lockstep] theorem pin_true_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_true st) st lst pinTrue :=
  pinRE_lsr hrel hinv fun _ h => pin_true_run₀ hrel hinv h

@[lockstep] theorem pin_true_intro_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_true_intro st) st lst pinTrueIntro :=
  pinRE_lsr hrel hinv fun _ h => pin_true_intro_run₀ hrel hinv h

@[lockstep] theorem pin_trust_compiler_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_trust_compiler st) st lst pinTrustCompiler :=
  pinRE_lsr hrel hinv fun _ h => pin_trust_compiler_run₀ hrel hinv h

@[lockstep] theorem pin_reduce_nat_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_reduce_nat st) st lst pinReduceNat :=
  pinRE_lsr hrel hinv fun _ h => pin_reduce_nat_run₀ hrel hinv h

@[lockstep] theorem pin_reduce_bool_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_reduce_bool st) st lst pinReduceBool :=
  pinRE_lsr hrel hinv fun _ h => pin_reduce_bool_run₀ hrel hinv h

@[lockstep] theorem pin_of_reduce_nat_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_of_reduce_nat st) st lst pinOfReduceNat :=
  pinRE_lsr hrel hinv fun _ h => pin_of_reduce_nat_run₀ hrel hinv h

@[lockstep] theorem pin_of_reduce_bool_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_of_reduce_bool st) st lst pinOfReduceBool :=
  pinRE_lsr hrel hinv fun _ h => pin_of_reduce_bool_run₀ hrel hinv h

/-! ## Handle `dup2` / `eq2` (Rust-only steps) -/

@[lockstep] theorem dup2_nidx (h : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun e he => dupId_nidx _ _ he

@[lockstep] theorem dup2_lidx (h : arena.handle.LIdx) :
    LSP (arena.handle.LIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun e he => dupId_lidx _ _ he

@[lockstep] theorem dup2_lsidx (h : arena.handle.LsIdx) :
    LSP (arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun e he => dupId_lsidx _ _ he

@[lockstep] theorem eq2_nidx (a b : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun o => o = (absNIdx a == absNIdx b)) := by
  intro o h
  rw [arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  rw [← Result.ok_injective h]
  by_cases hab : a = b
  · subst hab; simp
  · have h1 : a.word ≠ b.word := by
      intro hc; exact hab (by cases a; cases b; simp_all)
    have h2 : absNIdx a ≠ absNIdx b := fun hc => hab (absNIdx_inj hc)
    simp [h1, h2]

@[lockstep] theorem eq2_lsidx (a b : arena.handle.LsIdx) :
    LSP (arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun o => o = (absLsIdx a == absLsIdx b)) := by
  intro o h
  rw [arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapEq2.eq2] at h
  rw [← Result.ok_injective h]
  by_cases hab : a = b
  · subst hab; simp
  · have h1 : a.word ≠ b.word := by
      intro hc; exact hab (by cases a; cases b; simp_all)
    have h2 : absLsIdx a ≠ absLsIdx b := fun hc => hab (absLsIdx_inj hc)
    simp [h1, h2]

/-! ## The projection-table entry -/

/-- `arena::env::IProjEntry` as the twin's `IProjEntry`, field for field. -/
def absIProjEntry (e : arena.env.IProjEntry) : IProjEntry :=
  ⟨absNIdx e.struct_name, absU e.idx, e.level_params.val.map absNIdx, absU e.num_params,
    absNIdx e.ctor, absU e.num_fields, absEIdx e.body, absLIdx e.field_sort,
    absLIdx e.struct_sort, absU e.off⟩

attribute [lockstep_simp] absIProjEntry

@[lockstep] theorem snoc_eidx_of_ls (xs : alloc.vec.Vec arena.handle.EIdx)
    (y : arena.handle.EIdx) :
    LSP (arena.expr_ops.snoc_eidx_of xs y)
      (fun r => TwinEq ((absEIdxList xs).toArray.push (absEIdx y)) (absEIdxArr r)) := by
  intro r h
  have h1 := ConRon.Refine2.ExprOps.snoc_eidx_of_refines h
  simp only [ConRon.Refine2.ExprOps.absEIdxL] at h1
  show _ = (r.val.map absEIdx).toArray
  rw [h1]
  simp [absEIdxList]

/-! ## Store readers the leaves need -/

attribute [lockstep_simp] absConstT

@[lockstep] theorem view_const_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = Option.map absConstT a) (arena.monad.view_const pers st h) st lst
      (Arena.viewConst (absEIdx h)) :=
  fun _ hr => ⟨_, lst, view_const_run₀ hrel hr, rfl, hrel, hinv⟩

@[lockstep] theorem view_ls_len_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.LsIdx) :
    LSV pers (fun a b => b = Option.map absSz a) (arena.monad.view_ls_len pers st h) st lst
      (Arena.viewLsLen (absLsIdx h)) :=
  fun _ hr => ⟨_, lst, view_ls_len_run₀ hrel hr, rfl, hrel, hinv⟩

@[lockstep] theorem fail_dangling_ls_spec (T : Type) :
    LSP (arena.monad.fail_dangling_ls T) (fun r => ∃ v, r = .Err (.Internal v)) := by
  intro r h
  rw [arena.monad.fail_dangling_ls] at h
  obtain ⟨s, _, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, _, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  exact ⟨v, fail_run h⟩

/-! ## The level / name readbacks over `AStateRel₀`

`Refine2/Specs.lean`'s `read_{name,level,levels,names}_m_run` and
`ExprOps/Mut.lean`'s `read_names_m_{from_,}wf`, restated over the lockstep
relation: the proofs read `hrel.caches` / `hrel.store` only, and the
conclusions are `Sim₀` (no `Ext`, no `WF` slot). -/

theorem read_name_m_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.NIdx} {o}
    (hrun : arena.monad.read_name_m pers st h = ok o) :
    Sim₀ ConRon.Refine.absName pers lst o
      (Arena.readNameM (absNIdx h)) := by
  rw [arena.monad.read_name_m] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf nidx_eq2 hinv.caches.readNC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.caches.readNC h trivial
  rw [← hto] at hrelk
  show AOut₀ _ pers o.1 o.2 _
  rw [readNameM_run]
  cases hrc : r with
  | some x =>
    rw [hrc] at hrun hrelk
    obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho : (core.result.Result.Ok n, st) = o := Result.ok_injective hrun
    rw [← ho]
    simp only [Option.map_some] at hrelk
    rw [← hrelk]
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
    rw [ConRon.Refine.Name.dup_refines hn]
  | none =>
    rw [hrc] at hrun hrelk
    simp only [Option.map_none] at hrelk
    rw [← hrelk]
    obtain ⟨ns, hns, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.store.EStore.ns] at hns
    have hns2 : ns = st.store.lss.ls.ns := (Result.ok_injective hns).symm
    subst hns2
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hd := denote_n_abs hrel.store.lss.lvl.ns hv
    have hdw := denote_n_wf hinv.store.lss.lvl.ns hv
    cases hvc : v with
    | none =>
      rw [hvc] at hrun hd
      obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hrre := fail_run hrr
      subst hrre
      have ho : ((core.result.Result.Err
        (kernel.core_types.CheckError.Internal w)), st) = o := Result.ok_injective hrun
      rw [← ho]
      show AErrSim _ _
      rw [EStore.ns, ← hd]
      exact AErrSim.internal rfl
    | some x =>
      rw [hvc] at hrun hd hdw
      obtain ⟨k1, hk1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨n2, hn2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨old, hm⟩ := p
      rw [dupId_nidx _ _ hk1] at hp
      have hn2e : n2 = x := (Result.ok_injective (by rw [← hn2]; simp)).symm
      subst hn2e
      have ho : (core.result.Result.Ok n2,
        ({ st with caches := { st.caches with read_n_c := hm } } :
          arena.monad.AState)) = o := Result.ok_injective hrun
      rw [← ho]
      obtain ⟨h1, h2⟩ := memo_insert_step nidx_eq2 absNIdx_inj hinv.caches.readNC
        hrel.caches.readNC hp
      have hins := ConRon.Refine.HashMap2.insert_refines_wf nidx_eq2
        hinv.caches.readNC ConRon.Refine.HashMap2.KeysOk_true trivial hp
      have hvals := memo_insert_vals h2 hins.2.2.1 hinv.caches.readNVals (hdw n2 rfl)
      show AOut₀ _ pers _ _ _
      rw [EStore.ns, ← hd]
      refine AOut₀.ok (lst' := { lst with caches := { lst.caches with
          readNC := lst.caches.readNC.insert (absNIdx h) (ConRon.Refine.absName n2) } })
        rfl
        { hrel with caches := { hrel.caches with readNC := h1 } }
        { hinv with caches := { hinv.caches with readNC := h2, readNVals := hvals } }

/-- `arena::monad::level_list_dup` is the identity on the list (DESIGN §3.2:
a `dup` is `Arc::clone`, and the model makes it the identity). -/

theorem read_level_m_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.LIdx} {o}
    (hrun : arena.monad.read_level_m pers st h = ok o) :
    Sim₀ ConRon.Refine.absLevel pers lst o
      (Arena.readLevelM (absLIdx h)) := by
  rw [arena.monad.read_level_m] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf lidx_eq2 hinv.caches.readLC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.caches.readLC h trivial
  rw [← hto] at hrelk
  show AOut₀ _ pers o.1 o.2 _
  rw [readLevelM_run]
  cases hrc : r with
  | some x =>
    rw [hrc] at hrun hrelk
    obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho : (core.result.Result.Ok n, st) = o := Result.ok_injective hrun
    rw [← ho]
    simp only [Option.map_some] at hrelk
    rw [← hrelk]
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
    have hne : n = x := by
      rw [ConRon.Refine.level_dup_eq] at hn; exact (Result.ok_injective hn).symm
    rw [hne]
  | none =>
    rw [hrc] at hrun hrelk
    simp only [Option.map_none] at hrelk
    rw [← hrelk]
    obtain ⟨ls0, hls0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.store.EStore.ls] at hls0
    have hls2 : ls0 = st.store.lss.ls := (Result.ok_injective hls0).symm
    subst hls2
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hd := denote_l_abs hrel.store.lss.lvl hv
    have hdw := denote_l_wf hinv.store.lss.lvl hv
    cases hvc : v with
    | none =>
      rw [hvc] at hrun hd
      obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hrre := fail_run hrr
      subst hrre
      have ho : ((core.result.Result.Err
        (kernel.core_types.CheckError.Internal w)), st) = o := Result.ok_injective hrun
      rw [← ho]
      show AErrSim _ _
      rw [EStore.ls, ← hd]
      exact AErrSim.internal rfl
    | some x =>
      rw [hvc] at hrun hd hdw
      obtain ⟨k1, hk1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨l3, hl3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨old, hm⟩ := p
      rw [dupId_lidx _ _ hk1] at hp
      have hl3e : l3 = x := by
        rw [ConRon.Refine.level_dup_eq] at hl3; exact (Result.ok_injective hl3).symm
      subst hl3e
      have ho : (core.result.Result.Ok l3,
        ({ st with caches := { st.caches with read_l_c := hm } } :
          arena.monad.AState)) = o := Result.ok_injective hrun
      rw [← ho]
      obtain ⟨h1, h2⟩ := memo_insert_step lidx_eq2 absLIdx_inj hinv.caches.readLC
        hrel.caches.readLC hp
      have hins := ConRon.Refine.HashMap2.insert_refines_wf lidx_eq2
        hinv.caches.readLC ConRon.Refine.HashMap2.KeysOk_true trivial hp
      have hvals := memo_insert_vals h2 hins.2.2.1 hinv.caches.readLVals (hdw l3 rfl)
      show AOut₀ _ pers _ _ _
      rw [EStore.ls, ← hd]
      refine AOut₀.ok (lst' := { lst with caches := { lst.caches with
          readLC := lst.caches.readLC.insert (absLIdx h) (ConRon.Refine.absLevel l3) } })
        rfl
        { hrel with caches := { hrel.caches with readLC := h1 } }
        { hinv with caches := { hinv.caches with readLC := h2, readLVals := hvals } }


theorem read_levels_m_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {h : arena.handle.LsIdx} {o}
    (hrun : arena.monad.read_levels_m pers st h = ok o) :
    Sim₀ ConRon.Refine.absLevels pers lst o
      (Arena.readLevelsM (absLsIdx h)) := by
  rw [arena.monad.read_levels_m] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf lsidx_eq2 hinv.caches.readLsC
    ConRon.Refine.HashMap2.KeysOk_true trivial hr
  have hrelk := hrel.caches.readLsC h trivial
  rw [← hto] at hrelk
  show AOut₀ _ pers o.1 o.2 _
  rw [readLevelsM_run]
  cases hrc : r with
  | some x =>
    rw [hrc] at hrun hrelk
    obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho : (core.result.Result.Ok n, st) = o := Result.ok_injective hrun
    rw [← ho]
    simp only [Option.map_some] at hrelk
    rw [← hrelk]
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
    show Except.ok (ConRon.Refine.absLevels x, lst)
      = Except.ok (ConRon.Refine.absLevels n, lst)
    rw [ConRon.Refine.absLevels, ConRon.Refine.absLevels, level_list_dup_val hn]
  | none =>
    rw [hrc] at hrun hrelk
    simp only [Option.map_none] at hrelk
    rw [← hrelk]
    obtain ⟨ls0, hls0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.store.EStore.ls_s] at hls0
    have hls2 : ls0 = st.store.lss := (Result.ok_injective hls0).symm
    subst hls2
    obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hd := denote_ls_abs hrel.store.lss hv
    have hdw := denote_ls_wf hinv.store.lss hv
    cases hvc : v with
    | none =>
      rw [hvc] at hrun hd
      obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨w, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨rr, hrr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hrre := fail_run hrr
      subst hrre
      have ho : ((core.result.Result.Err
        (kernel.core_types.CheckError.Internal w)), st) = o := Result.ok_injective hrun
      rw [← ho]
      show AErrSim _ _
      rw [← hd]
      exact AErrSim.internal rfl
    | some x =>
      rw [hvc] at hrun hd hdw
      obtain ⟨k1, hk1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨l3, hl3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨old, hm⟩ := p
      rw [dupId_lsidx _ _ hk1] at hp
      have ho : (core.result.Result.Ok x,
        ({ st with caches := { st.caches with read_ls_c := hm } } :
          arena.monad.AState)) = o := Result.ok_injective hrun
      rw [← ho]
      have hl3v : l3.val = x.val := level_list_dup_val hl3
      have hrelLs : RelOn (fun _ => True) st.caches.read_ls_c
          lst.caches.readLsC absLsIdx ConRon.Refine.absLevels := hrel.caches.readLsC
      obtain ⟨h1, h2⟩ := memo_insert_step lsidx_eq2 absLsIdx_inj hinv.caches.readLsC
        hrelLs hp
      have hins := ConRon.Refine.HashMap2.insert_refines_wf lsidx_eq2
        hinv.caches.readLsC ConRon.Refine.HashMap2.KeysOk_true trivial hp
      have hxw : ConRon.Refine.LevelsWF l3 := by
        intro u hu; rw [hl3v] at hu; exact hdw x rfl u hu
      have hvals := memo_insert_vals h2 hins.2.2.1 hinv.caches.readLsVals hxw
      have habs : ConRon.Refine.absLevels l3 = ConRon.Refine.absLevels x := by
        rw [ConRon.Refine.absLevels, ConRon.Refine.absLevels, hl3v]
      show AOut₀ _ pers _ _ _
      rw [← hd]
      refine AOut₀.ok (lst' := { lst with caches := { lst.caches with
          readLsC := lst.caches.readLsC.insert (absLsIdx h)
            (ConRon.Refine.absLevels x) } })
        rfl
        { hrel with caches := { hrel.caches with readLsC := habs ▸ h1 } }
        { hinv with caches := { hinv.caches with readLsC := h2, readLsVals := hvals } }

/-- The port's `read_names_m_from` carries an accumulator the twin does not;
this is what puts the two runs on the same footing. -/

theorem read_names_m_from_abs₀ {pers} {ks : alloc.vec.Vec arena.handle.NIdx} :
    ∀ k {st : arena.monad.AState} {lst : AState}, AStateRel₀ pers st lst →
      AStateInv pers st → ∀ (i : Std.Usize) (out : alloc.vec.Vec kernel.name.Name),
      ks.length - i.val ≤ k → ∀ {o},
      arena.monad.read_names_m_from pers st ks i out = ok o →
      AOut₀ (fun v : alloc.vec.Vec kernel.name.Name => v.val.map ConRon.Refine.absName)
        pers o.1 o.2
        (prependOut (out.val.map ConRon.Refine.absName)
          ((Arena.readNamesM ((ks.val.drop i.val).map absNIdx)).run lst)) := by
  intro k
  induction k with
  | zero =>
    intro st lst hrel hinv i out hk o hrun
    rw [arena.monad.read_names_m_from.eq_def] at hrun; simp only [] at hrun
    rw [if_pos (by scalar_tac)] at hrun
    rw [List.drop_eq_nil_of_le (by scalar_tac), List.map_nil]
    have ho : ((core.result.Result.Ok out : core.result.Result _ _), st) = o :=
      Result.ok_injective hrun
    rw [← ho]
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
    show prependOut _ (Except.ok (([] : List ConLeche.Name), lst)) = _
    show Except.ok (out.val.map ConRon.Refine.absName ++ [], lst) = _
    rw [List.append_nil]
  | succ k ih =>
    intro st lst hrel hinv i out hk o hrun
    rw [arena.monad.read_names_m_from.eq_def] at hrun; simp only [] at hrun
    split at hrun
    · rw [List.drop_eq_nil_of_le (by scalar_tac), List.map_nil]
      have ho : ((core.result.Result.Ok out : core.result.Result _ _), st) = o :=
        Result.ok_injective hrun
      rw [← ho]
      refine AOut₀.ok (lst' := lst) ?_ hrel hinv
      show prependOut _ (Except.ok (([] : List ConLeche.Name), lst)) = _
      show Except.ok (out.val.map ConRon.Refine.absName ++ [], lst) = _
      rw [List.append_nil]
    · rename_i hlt
      have hb : i.val < ks.length := by scalar_tac
      obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hnv : ks.val[i.val] = n := by
        have h1 : ks.val[i.val]? = some n := vec_index_some hn
        rw [List.getElem?_eq_getElem hb] at h1
        exact (Option.some.injEq _ _ ▸ h1)
      obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r, st1⟩ := p1
      have hstep := read_name_m_run₀ hrel hinv hp1
      rw [List.drop_eq_getElem_cons hb, List.map_cons, hnv, readNamesM_run_cons]
      cases hrc : r with
      | Err e =>
        rw [hrc] at hstep
        simp only [hrc] at hrun
        have herr : AErrSim e ((Arena.readNameM (absNIdx n)).run lst) := hstep
        have ho : ((core.result.Result.Err e : core.result.Result _ _), st1) = o :=
          Result.ok_injective hrun
        rw [← ho]
        refine AOut₀.err ?_
        intro kk hkk
        obtain ⟨le, hle, hk2⟩ := herr kk hkk
        exact ⟨le, by rw [hle]; rfl, hk2⟩
      | Ok x =>
        rw [hrc] at hstep
        simp only [hrc] at hrun
        obtain ⟨lst1, hx1, hrel1, hinv1⟩ := hstep
        rw [hx1]
        obtain ⟨out1, hout1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := by
          have := ConRon.Refine.Nat.uadd_val hi2; simpa using this
        have hout1v : out1.val = out.val ++ [x] := ConRon.Refine.vec_push_val hout1
        have hih := ih hrel1 hinv1 i2 out1 (by scalar_tac) hrun
        rw [hi2v] at hih
        show AOut₀ _ pers o.1 o.2
          (prependOut _ (((Arena.readNamesM
            ((ks.val.drop (i.val + 1)).map absNIdx)).run lst1).bind _))
        cases hy : (Arena.readNamesM ((ks.val.drop (i.val + 1)).map absNIdx)).run lst1 with
        | error e =>
          rw [hy] at hih
          cases hoc : o.1 with
          | Ok v =>
            rw [hoc] at hih
            obtain ⟨lst2, hcontra, -⟩ := hih
            exact absurd hcontra (by simp [prependOut])
          | Err e2 =>
            rw [hoc] at hih
            have herr : AErrSim e2 (prependOut (out1.val.map ConRon.Refine.absName)
              (Except.error e)) := hih
            refine AOut₀.err ?_
            intro kk hkk
            obtain ⟨le, hle, hk2⟩ := herr kk hkk
            refine ⟨le, ?_, hk2⟩
            have : (Except.error e : Except Arena.CheckError (List ConLeche.Name × AState))
                = Except.error le := by
              have := hle; simp only [prependOut] at this; exact this
            simp only [Except.error.injEq] at this
            rw [← this]; rfl
        | ok q =>
          rw [hy] at hih
          cases hoc : o.1 with
          | Err e2 =>
            rw [hoc] at hih
            have herr : AErrSim e2 (prependOut (out1.val.map ConRon.Refine.absName)
              (Except.ok q)) := hih
            refine AOut₀.err ?_
            intro kk hkk
            obtain ⟨le, hle, -⟩ := herr kk hkk
            simp only [prependOut] at hle
            exact absurd hle (by simp)
          | Ok v =>
            rw [hoc] at hih
            obtain ⟨lst2, hv2, hrel2, hinv2⟩ := hih
            simp only [prependOut, Except.ok.injEq, Prod.mk.injEq] at hv2
            refine AOut₀.ok (lst' := lst2) ?_ hrel2 hinv2
            show Except.ok (out.val.map ConRon.Refine.absName
              ++ (ConRon.Refine.absName x :: q.1), q.2) = _
            rw [← hv2.2]
            have hq1 : out1.val.map ConRon.Refine.absName ++ q.1
                = v.val.map ConRon.Refine.absName := hv2.1
            rw [hout1v] at hq1
            simp only [List.map_append, List.map_cons, List.map_nil,
              List.append_assoc, List.cons_append, List.nil_append] at hq1
            rw [hq1]

theorem read_names_m_run₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {ks : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.monad.read_names_m pers st ks = ok o) :
    Sim₀ ConRon.Refine.absNames pers lst o
      (Arena.readNamesM (ks.val.map absNIdx)) := by
  rw [arena.monad.read_names_m] at hrun
  have hh := read_names_m_from_abs₀ ks.length hrel hinv 0#usize
    (alloc.vec.Vec.new kernel.name.Name) (by scalar_tac) hrun
  simp only [show (0#usize : Std.Usize).val = 0 from rfl, List.drop_zero] at hh
  rw [show ((alloc.vec.Vec.new kernel.name.Name).val.map ConRon.Refine.absName)
        = ([] : List ConLeche.Name) from rfl, prependOut_nil] at hh
  exact hh


theorem read_names_m_from_wf₀ {pers} {ks : alloc.vec.Vec arena.handle.NIdx} :
    ∀ k {st : arena.monad.AState} {lst : AState}, AStateRel₀ pers st lst →
      AStateInv pers st → ∀ (i : Std.Usize) (out : alloc.vec.Vec kernel.name.Name),
      ks.length - i.val ≤ k → (∀ n ∈ out.val, ConRon.Refine.NameWF n) → ∀ {o},
      arena.monad.read_names_m_from pers st ks i out = ok o →
      (∀ v, o.1 = .Ok v → ∀ n ∈ v.val, ConRon.Refine.NameWF n) ∧
        o.2.store = st.store := by
  intro k
  induction k with
  | zero =>
    intro st lst hrel hinv i out hk hout o hrun
    rw [arena.monad.read_names_m_from.eq_def] at hrun; simp only [] at hrun
    rw [if_pos (by scalar_tac)] at hrun
    have ho : ((core.result.Result.Ok out : core.result.Result _ _), st) = o :=
      Result.ok_injective hrun
    rw [← ho]
    refine ⟨fun v hv => ?_, rfl⟩
    simp only [core.result.Result.Ok.injEq] at hv
    rw [← hv]; exact hout
  | succ k ih =>
    intro st lst hrel hinv i out hk hout o hrun
    rw [arena.monad.read_names_m_from.eq_def] at hrun; simp only [] at hrun
    split at hrun
    · have ho : ((core.result.Result.Ok out : core.result.Result _ _), st) = o :=
        Result.ok_injective hrun
      rw [← ho]
      refine ⟨fun v hv => ?_, rfl⟩
      simp only [core.result.Result.Ok.injEq] at hv
      rw [← hv]; exact hout
    · rename_i hlt
      obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨p1, hp1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r, st1⟩ := p1
      have hstep := read_name_m_run₀ hrel hinv hp1
      have hw := read_name_m_wf hinv hp1
      cases hrc : r with
      | Err e =>
        simp only [hrc] at hrun
        have ho : ((core.result.Result.Err e : core.result.Result _ _), st1) = o :=
          Result.ok_injective hrun
        rw [← ho]
        exact ⟨(by intro v hv; cases hv), hw.2⟩
      | Ok x =>
        rw [hrc] at hstep hw
        simp only [hrc] at hrun
        obtain ⟨lst1, -, hrel1, hinv1⟩ := hstep
        obtain ⟨out1, hout1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have hi2v : i2.val = i.val + 1 := by
          have := ConRon.Refine.Nat.uadd_val hi2; simpa using this
        have hout1v : out1.val = out.val ++ [x] := ConRon.Refine.vec_push_val hout1
        have hih := ih hrel1 hinv1 i2 out1 (by scalar_tac) (by
          intro nn hnn
          rw [hout1v] at hnn
          rcases List.mem_append.mp hnn with hnn | hnn
          · exact hout nn hnn
          · rw [List.mem_singleton.mp hnn]; exact hw.1 x rfl) hrun
        exact ⟨hih.1, hih.2.trans hw.2⟩

/-- `read_names_m`'s names are well formed, and the port's store does not
move. -/
theorem read_names_m_wf₀ {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {ks : alloc.vec.Vec arena.handle.NIdx} {o}
    (hrun : arena.monad.read_names_m pers st ks = ok o) :
    (∀ v, o.1 = .Ok v → ∀ n ∈ v.val, ConRon.Refine.NameWF n) ∧
      o.2.store = st.store := by
  rw [arena.monad.read_names_m] at hrun
  exact read_names_m_from_wf₀ ks.length hrel hinv 0#usize
    (alloc.vec.Vec.new kernel.name.Name) (by scalar_tac)
    (by intro n hn; exact absurd hn (by simp [alloc.vec.Vec.new])) hrun


/-! ### The readbacks as `@[lockstep]` steps

The answer relation carries the tree's well-formedness beside the value
equation (`WF a ∧ b = abs a`): the pure `kernel::level` operations below want
it, and `lockstep`'s tidy step keeps the first conjunct as a hypothesis and
substitutes the second. -/

theorem ls_ofSim₀WF {α β : Type} {A : α → β} {W : α → Prop} {pers lst}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {x : AM β} (h : ∀ o, m = ok o → Sim₀ A pers lst o x)
    (hw : ∀ o, m = ok o → ∀ a, o.1 = .Ok a → W a) :
    LS pers (fun a b => W a ∧ b = A a) m lst x := by
  intro o st' hm
  have h1 := h _ hm
  have h2 := hw _ hm
  cases o with
  | Err e => exact h1
  | Ok a =>
    obtain ⟨lst', hx, hr, hi⟩ := h1
    exact ⟨_, lst', hx, ⟨h2 a rfl, rfl⟩, hr, hi⟩

@[lockstep] theorem read_level_m_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.LIdx) :
    LS pers (fun a b => ConRon.Refine.LevelWF a ∧ b = ConRon.Refine.absLevel a)
      (arena.monad.read_level_m pers st h) lst (Arena.readLevelM (absLIdx h)) :=
  ls_ofSim₀WF (fun _ hm => read_level_m_run₀ hrel hinv hm)
    (fun _ hm => (read_level_m_wf hinv hm).1)

@[lockstep] theorem read_levels_m_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.LsIdx) :
    LS pers (fun a b => ConRon.Refine.LevelsWF a ∧ b = ConRon.Refine.absLevels a)
      (arena.monad.read_levels_m pers st h) lst (Arena.readLevelsM (absLsIdx h)) :=
  ls_ofSim₀WF (fun _ hm => read_levels_m_run₀ hrel hinv hm)
    (fun _ hm => (read_levels_m_wf hinv hm).1)

@[lockstep] theorem read_name_m_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.NIdx) :
    LS pers (fun a b => ConRon.Refine.NameWF a ∧ b = ConRon.Refine.absName a)
      (arena.monad.read_name_m pers st h) lst (Arena.readNameM (absNIdx h)) :=
  ls_ofSim₀WF (fun _ hm => read_name_m_run₀ hrel hinv hm)
    (fun _ hm => (read_name_m_wf hinv hm).1)

@[lockstep] theorem read_names_m_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ks : alloc.vec.Vec arena.handle.NIdx) :
    LS pers (fun a b => ConRon.Refine.NamesWF a ∧ b = ConRon.Refine.absNames a)
      (arena.monad.read_names_m pers st ks) lst (Arena.readNamesM (ks.val.map absNIdx)) :=
  ls_ofSim₀WF (fun _ hm => read_names_m_run₀ hrel hinv hm)
    (fun _ hm => (read_names_m_wf₀ hrel hinv hm).1)

/-! ## The pure `kernel::level` operations against the twin's `Level` functions

A constructed tree's fact is `WF u ∧ TwinEq <twin expr> (abs u)`: the twin
side is rewritten to the port's value, and the well-formedness stays in the
context for the next operation.  `lockstep`'s tidy step does not split a
conjunction whose second half is not an equation between a variable and a
term, so `Leaves.lean`'s `lockstep_a1` splits it. -/

@[lockstep] theorem is_equiv_ls (l r : kernel.level.Level) (hl : ConRon.Refine.LevelWF l)
    (hr : ConRon.Refine.LevelWF r) :
    LSP (kernel.level.is_equiv l r)
      (fun o => TwinEq (ConLeche.Level.isEquiv (ConRon.Refine.absLevel l)
        (ConRon.Refine.absLevel r)) (Option.map id o)) := by
  intro o h
  show _ = Option.map id o
  rw [Option.map_id]; show _ = o
  exact ConRon.Refine.Level.is_equiv_refines hl hr h

theorem is_equiv_list_from_refines (ls rs : alloc.vec.Vec kernel.level.Level)
    (hl : ConRon.Refine.LevelsWF ls) (hr : ConRon.Refine.LevelsWF rs) :
    ∀ k (i : Std.Usize), ls.length - i.val ≤ k → ∀ o,
      kernel.level.is_equiv_list_from ls rs i = ok o →
      ConLeche.Level.isEquivList ((ls.val.drop i.val).map ConRon.Refine.absLevel)
        ((rs.val.drop i.val).map ConRon.Refine.absLevel) = o := by
  intro k
  induction k with
  | zero =>
    intro i hk o h
    rw [kernel.level.is_equiv_list_from] at h
    have hge : i ≥ alloc.vec.Vec.len ls := by scalar_tac
    rw [List.drop_eq_nil_of_le (by scalar_tac)]
    simp only [hge, if_true] at h
    by_cases hr2 : i ≥ alloc.vec.Vec.len rs
    · simp only [hr2, if_true] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by scalar_tac)]; rfl
    · simp only [hr2, if_false, hge, if_true] at h
      cases Result.ok_injective h
      have hlt : i.val < rs.val.length := by scalar_tac
      rw [List.drop_eq_getElem_cons hlt]; rfl
  | succ k ih =>
    intro i hk o h
    rw [kernel.level.is_equiv_list_from] at h
    by_cases hge : i ≥ alloc.vec.Vec.len ls
    · rw [List.drop_eq_nil_of_le (by scalar_tac)]
      simp only [hge, if_true] at h
      by_cases hr2 : i ≥ alloc.vec.Vec.len rs
      · simp only [hr2, if_true] at h
        cases Result.ok_injective h
        rw [List.drop_eq_nil_of_le (by scalar_tac)]; rfl
      · simp only [hr2, if_false, hge, if_true] at h
        cases Result.ok_injective h
        have hlt : i.val < rs.val.length := by scalar_tac
        rw [List.drop_eq_getElem_cons hlt]; rfl
    · have hlt1 : i.val < ls.val.length := by scalar_tac
      rw [List.drop_eq_getElem_cons hlt1]
      simp only [hge, if_false] at h
      by_cases hr2 : i ≥ alloc.vec.Vec.len rs
      · simp only [hr2, if_true] at h
        cases Result.ok_injective h
        rw [List.drop_eq_nil_of_le (show rs.val.length ≤ i.val by scalar_tac)]; rfl
      · have hlt2 : i.val < rs.val.length := by scalar_tac
        rw [List.drop_eq_getElem_cons hlt2]
        simp only [hr2, if_false] at h
        obtain ⟨l, hlv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨r, hrv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨o1, ho1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨_, hl1⟩ := ConRon.Refine2.ExprOps.vecIndexAt hlv
        obtain ⟨_, hr1⟩ := ConRon.Refine2.ExprOps.vecIndexAt hrv
        have hwl : ConRon.Refine.LevelWF l := by
          rw [← hl1]; exact hl _ (List.getElem_mem _)
        have hwr : ConRon.Refine.LevelWF r := by
          rw [← hr1]; exact hr _ (List.getElem_mem _)
        have heq := ConRon.Refine.Level.is_equiv_refines hwl hwr ho1
        simp only [List.map_cons, ConLeche.Level.isEquivList]
        rw [hl1, hr1, heq]
        cases o1 with
        | none => cases Result.ok_injective h; rfl
        | some b =>
          cases b with
          | false => simp only [Bool.false_eq_true, if_false] at h; cases Result.ok_injective h; rfl
          | true =>
            simp only [if_true] at h
            obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            have hi2v : i2.val = i.val + 1 := ConRon.Refine.Nat.uadd_val hi2
            have := ih i2 (by scalar_tac) o h
            rw [hi2v] at this
            simpa using this

@[lockstep] theorem is_equiv_list_ls (ls rs : alloc.vec.Vec kernel.level.Level)
    (hl : ConRon.Refine.LevelsWF ls) (hr : ConRon.Refine.LevelsWF rs) :
    LSP (kernel.level.is_equiv_list ls rs)
      (fun o => TwinEq (ConLeche.Level.isEquivList (ConRon.Refine.absLevels ls)
        (ConRon.Refine.absLevels rs)) (Option.map id o)) := by
  intro o h
  show _ = Option.map id o
  rw [Option.map_id]; show _ = o
  rw [kernel.level.is_equiv_list] at h
  have := is_equiv_list_from_refines ls rs hl hr _ 0#usize (Nat.le_refl _) o h
  simpa [ConRon.Refine.absLevels] using this

@[lockstep] theorem level_subst_ls (ks : alloc.vec.Vec kernel.name.Name)
    (vs : alloc.vec.Vec kernel.level.Level) (l : kernel.level.Level)
    (hks : ConRon.Refine.NamesWF ks) (hvs : ConRon.Refine.LevelsWF vs)
    (hl : ConRon.Refine.LevelWF l) :
    LSP (kernel.level.subst ks vs l)
      (fun u => ConRon.Refine.LevelWF u ∧ TwinEq
        (ConLeche.Level.subst (ConRon.Refine.absNames ks) (ConRon.Refine.absLevels vs)
          (ConRon.Refine.absLevel l)) (ConRon.Refine.absLevel u)) := by
  intro u h
  obtain ⟨h1, h2⟩ := ConRon.Refine.Level.subst_refines hl hks hvs h
  exact ⟨h2, h1.symm⟩

@[lockstep] theorem level_param_ls (n : kernel.name.Name) (hn : ConRon.Refine.NameWF n) :
    LSP (kernel.level.param n)
      (fun u => ConRon.Refine.LevelWF u ∧
        TwinEq (.param (ConRon.Refine.absName n)) (ConRon.Refine.absLevel u)) :=
  fun _ h => ⟨ConRon.Refine.Level.param_wf' h hn, (ConRon.Refine.Level.param_refines h).symm⟩

@[lockstep] theorem level_zero_ls :
    LSP kernel.level.zero
      (fun u => ConRon.Refine.LevelWF u ∧ TwinEq .zero (ConRon.Refine.absLevel u)) :=
  fun _ h => ⟨ConRon.Refine.Level.zero_wf' h, (ConRon.Refine.Level.zero_refines h).symm⟩

@[lockstep] theorem level_subst_pw_ls (ks : alloc.vec.Vec kernel.name.Name)
    (vs : alloc.vec.Vec kernel.level.Level) (pw : kernel.prop_when.PropWhen)
    (hks : ConRon.Refine.NamesWF ks) (hvs : ConRon.Refine.LevelsWF vs)
    (hpw : ConRon.Refine.PropWhenWF pw) :
    LSP (kernel.level.subst_pw ks vs pw)
      (fun r => ConRon.Refine.PropWhenWF r ∧ TwinEq
        (ConLeche.Level.substPW (ConRon.Refine.absNames ks) (ConRon.Refine.absLevels vs)
          (ConRon.Refine.absPropWhen pw)) (ConRon.Refine.absPropWhen r)) := by
  intro r h
  obtain ⟨h1, h2⟩ := ConRon.Refine.ExprOps.subst_pw_refines hks hvs hpw h
  exact ⟨h2, h1.symm⟩

@[lockstep] theorem prop_when_is_never_ls (pw : kernel.prop_when.PropWhen) :
    LSP (kernel.prop_when.is_never pw)
      (fun b => b = ConLeche.PropWhen.isNever (ConRon.Refine.absPropWhen pw)) :=
  fun _ h => ConRon.Refine.PropWhen.is_never_refines h

/-! ## The Core memo tables: key, probe, capped write

(A `Bool`-valued probe states its answer as `id o`: a bare variable on the
right of a `TwinEq` would be SUBSTITUTED by `lockstep`'s tidy step, which
turns the port's `match o` into a match on the table lookup that the twin's
own `match` is not split with.)

`Core/Probes.lean`'s probe/write pair, at the four tables region A1's leaves
use (`lvlEqC`, `lvlsEqC`, `constTyC`, `ruleRhsC`), stated as `@[lockstep]`
steps: the key and the probe are Rust-only reads whose twin partner is a pure
expression (`TwinEq`), the write is an `LSW` against the twin's inline `set`. -/

theorem absLIdx_surj : Function.Surjective absLIdx := by
  intro i
  obtain ⟨w⟩ := i
  obtain ⟨x, hx⟩ := absU32_surj w
  exact ⟨⟨x⟩, by simp [absLIdx, hx]⟩

theorem absLIdxPair_surj : Function.Surjective absLIdxPair := by
  rintro ⟨a, b⟩
  obtain ⟨x, hx⟩ := absLIdx_surj a
  obtain ⟨y, hy⟩ := absLIdx_surj b
  exact ⟨⟨x, y⟩, by simp [absLIdxPair, hx, hy]⟩

theorem absLIdxPair_inj : Function.Injective absLIdxPair := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [absLIdxPair, Prod.mk.injEq] at h
  simp [absLIdx_inj h.1, absLIdx_inj h.2]

theorem absLsIdxPair_surj : Function.Surjective absLsIdxPair := by
  rintro ⟨a, b⟩
  obtain ⟨x, hx⟩ := absLsIdx_surj a
  obtain ⟨y, hy⟩ := absLsIdx_surj b
  exact ⟨⟨x, y⟩, by simp [absLsIdxPair, hx, hy]⟩

theorem absLsIdxPair_inj : Function.Injective absLsIdxPair := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [absLsIdxPair, Prod.mk.injEq] at h
  simp [absLsIdx_inj h.1, absLsIdx_inj h.2]

theorem absNNLsKey_surj : Function.Surjective absNNLsKey := by
  rintro ⟨a, b, c⟩
  obtain ⟨x, hx⟩ := absNIdx_surj a
  obtain ⟨y, hy⟩ := absNIdx_surj b
  obtain ⟨z, hz⟩ := absLsIdx_surj c
  exact ⟨⟨x, y, z⟩, by simp [absNNLsKey, hx, hy, hz]⟩

theorem absNNLsKey_inj : Function.Injective absNNLsKey := by
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h
  simp only [absNNLsKey, Prod.mk.injEq] at h
  simp [absNIdx_inj h.1, absNIdx_inj h.2.1, absLsIdx_inj h.2.2]

/-- The twin's capped memo insert, named (the twin writes it inline). -/
def capIns {K V : Type} [BEq K] [Hashable K] (m : _root_.Std.HashMap K V) (k : K) (v : V) :
    _root_.Std.HashMap K V :=
  (if m.size < cacheCap then m else ∅).insert k v

@[lockstep] theorem lidx_pair_ls (u v : arena.handle.LIdx) :
    LSP (arena.core_state.lidx_pair u v)
      (fun k => TwinEq (absLIdx u, absLIdx v) (absLIdxPair k)) := by
  intro k h
  rw [arena.core_state.lidx_pair] at h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [dupId_lidx _ _ hx, dupId_lidx _ _ hy]; rfl

@[lockstep] theorem lsidx_pair_ls (u v : arena.handle.LsIdx) :
    LSP (arena.core_state.lsidx_pair u v)
      (fun k => TwinEq (absLsIdx u, absLsIdx v) (absLsIdxPair k)) := by
  intro k h
  rw [arena.core_state.lsidx_pair] at h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [dupId_lsidx _ _ hx, dupId_lsidx _ _ hy]; rfl

@[lockstep] theorem nls_key_ls (n : arena.handle.NIdx) (us : arena.handle.LsIdx) :
    LSP (arena.core_state.nls_key n us)
      (fun k => TwinEq (absNIdx n, absLsIdx us) (absNLsKey k)) :=
  fun _ h => (nls_key_abs h).symm

@[lockstep] theorem nnls_key_ls (a b : arena.handle.NIdx) (us : arena.handle.LsIdx) :
    LSP (arena.core_state.nnls_key a b us)
      (fun k => TwinEq (absNIdx a, absNIdx b, absLsIdx us) (absNNLsKey k)) := by
  intro k h
  rw [arena.core_state.nnls_key] at h
  obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨z, hz, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [dupId_nidx _ _ hx, dupId_nidx _ _ hy, dupId_lsidx _ _ hz]; rfl

@[lockstep] theorem lvl_eq_probe_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.core_state.LIdxPair) :
    LSP (arena.core.lvl_eq_probe st k)
      (fun o => TwinEq (lst.caches.lvlEqC[absLIdxPair k]?) (Option.map id o)) := by
  intro o hrun
  rw [arena.core.lvl_eq_probe] at hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf lidxPair_eq2 hinv.caches.lvlEqC
    ConRon.Refine.HashMap2.KeysOk_true trivial hq
  have hrelk := hrel.caches.lvlEqC k trivial
  show lst.caches.lvlEqC[absLIdxPair k]? = Option.map id o
  rw [← hrelk, ← hto]
  cases q with
  | none => cases Result.ok_injective hrun; rfl
  | some _ => cases Result.ok_injective hrun; simp

@[lockstep] theorem lvl_eq_set_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.core_state.LIdxPair) (r : Bool) :
    LSW pers (arena.core.lvl_eq_set st k r) lst
      (set { lst with caches := { lst.caches with lvlEqC := capIns lst.caches.lvlEqC (absLIdxPair k) (r) } } : AM Unit) := by
  intro st' hrun
  rw [arena.core.lvl_eq_set] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hm, hfit, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm2⟩ := p
  have hst : st' = { st with caches := { st.caches with lvl_eq_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := cache_insert_step lidxPair_eq2 absLIdxPair_surj absLIdxPair_inj
    hinv.caches.lvlEqC hrel.caches.lvlEqC hn hfit hp
  exact ⟨(), _, rfl, trivial, { hrel with caches := { hrel.caches with lvlEqC := h1 } },
    { hinv with caches := { hinv.caches with lvlEqC := h2 } }⟩

@[lockstep] theorem lvls_eq_probe_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.core_state.LsIdxPair) :
    LSP (arena.core.lvls_eq_probe st k)
      (fun o => TwinEq (lst.caches.lvlsEqC[absLsIdxPair k]?) (Option.map id o)) := by
  intro o hrun
  rw [arena.core.lvls_eq_probe] at hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf lsidxPair_eq2 hinv.caches.lvlsEqC
    ConRon.Refine.HashMap2.KeysOk_true trivial hq
  have hrelk := hrel.caches.lvlsEqC k trivial
  show lst.caches.lvlsEqC[absLsIdxPair k]? = Option.map id o
  rw [← hrelk, ← hto]
  cases q with
  | none => cases Result.ok_injective hrun; rfl
  | some _ => cases Result.ok_injective hrun; simp

@[lockstep] theorem lvls_eq_set_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.core_state.LsIdxPair) (r : Bool) :
    LSW pers (arena.core.lvls_eq_set st k r) lst
      (set { lst with caches := { lst.caches with lvlsEqC := capIns lst.caches.lvlsEqC (absLsIdxPair k) (r) } } : AM Unit) := by
  intro st' hrun
  rw [arena.core.lvls_eq_set] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hm, hfit, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm2⟩ := p
  have hst : st' = { st with caches := { st.caches with lvls_eq_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := cache_insert_step lsidxPair_eq2 absLsIdxPair_surj absLsIdxPair_inj
    hinv.caches.lvlsEqC hrel.caches.lvlsEqC hn hfit hp
  exact ⟨(), _, rfl, trivial, { hrel with caches := { hrel.caches with lvlsEqC := h1 } },
    { hinv with caches := { hinv.caches with lvlsEqC := h2 } }⟩

@[lockstep] theorem const_ty_probe_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.core_state.NLsKey) :
    LSP (arena.core.const_ty_probe st k)
      (fun o => TwinEq (lst.caches.constTyC[absNLsKey k]?) (o.map absEIdx)) := by
  intro o hrun
  rw [arena.core.const_ty_probe] at hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf nlsKey_eq2 hinv.caches.constTyC
    ConRon.Refine.HashMap2.KeysOk_true trivial hq
  have hrelk := hrel.caches.constTyC k trivial
  show lst.caches.constTyC[absNLsKey k]? = o.map absEIdx
  rw [← hrelk, ← hto]
  cases q with
  | none => cases Result.ok_injective hrun; rfl
  | some x =>
    obtain ⟨y, hy, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases Result.ok_injective hrun
    rw [dupId_eidx _ _ hy]

@[lockstep] theorem const_ty_set_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.core_state.NLsKey) (r : arena.handle.EIdx) :
    LSW pers (arena.core.const_ty_set st k r) lst
      (set { lst with caches := { lst.caches with constTyC := capIns lst.caches.constTyC (absNLsKey k) (absEIdx r) } } : AM Unit) := by
  intro st' hrun
  rw [arena.core.const_ty_set] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hm, hfit, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm2⟩ := p
  rw [dupId_eidx _ _ he1] at hp
  have hst : st' = { st with caches := { st.caches with const_ty_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := cache_insert_step nlsKey_eq2 absNLsKey_surj absNLsKey_inj
    hinv.caches.constTyC hrel.caches.constTyC hn hfit hp
  exact ⟨(), _, rfl, trivial, { hrel with caches := { hrel.caches with constTyC := h1 } },
    { hinv with caches := { hinv.caches with constTyC := h2 } }⟩

@[lockstep] theorem rule_rhs_probe_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.core_state.NNLsKey) :
    LSP (arena.core.rule_rhs_probe st k)
      (fun o => TwinEq (lst.caches.ruleRhsC[absNNLsKey k]?) (o.map absEIdx)) := by
  intro o hrun
  rw [arena.core.rule_rhs_probe] at hrun
  obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hto := ConRon.Refine.HashMap2.get_refines_wf nnlsKey_eq2 hinv.caches.ruleRhsC
    ConRon.Refine.HashMap2.KeysOk_true trivial hq
  have hrelk := hrel.caches.ruleRhsC k trivial
  show lst.caches.ruleRhsC[absNNLsKey k]? = o.map absEIdx
  rw [← hrelk, ← hto]
  cases q with
  | none => cases Result.ok_injective hrun; rfl
  | some x =>
    obtain ⟨y, hy, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases Result.ok_injective hrun
    rw [dupId_eidx _ _ hy]

@[lockstep] theorem rule_rhs_set_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (k : arena.core_state.NNLsKey) (r : arena.handle.EIdx) :
    LSW pers (arena.core.rule_rhs_set st k r) lst
      (set { lst with caches := { lst.caches with ruleRhsC := capIns lst.caches.ruleRhsC (absNNLsKey k) (absEIdx r) } } : AM Unit) := by
  intro st' hrun
  rw [arena.core.rule_rhs_set] at hrun
  obtain ⟨n, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hm, hfit, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨p, hp, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨old, hm2⟩ := p
  rw [dupId_eidx _ _ he1] at hp
  have hst : st' = { st with caches := { st.caches with rule_rhs_c := hm2 } } :=
    (Result.ok_injective hrun).symm
  subst hst
  obtain ⟨h1, h2⟩ := cache_insert_step nnlsKey_eq2 absNNLsKey_surj absNNLsKey_inj
    hinv.caches.ruleRhsC hrel.caches.ruleRhsC hn hfit hp
  exact ⟨(), _, rfl, trivial, { hrel with caches := { hrel.caches with ruleRhsC := h1 } },
    { hinv with caches := { hinv.caches with ruleRhsC := h2 } }⟩

/-! ## Interns — pending the foundation's intern slice -/

@[lockstep] theorem intern_e_const_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : arena.handle.NIdx) (us : arena.handle.LsIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_const pers st n us) lst
      (Arena.internE (.const (absNIdx n) (absLsIdx us))) := by
  -- PENDING foundation intern slice (T2-LOCKSTEP slice 3)
  sorry

@[lockstep] theorem intern_level_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (l : kernel.level.Level) :
    LS pers (fun a b => b = absLIdx a) (arena.monad.intern_level pers st l) lst
      (Arena.internLevel (ConRon.Refine.absLevel l)) := by
  -- PENDING foundation intern slice (T2-LOCKSTEP slice 3)
  sorry

@[lockstep] theorem intern_ls_node_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (v : alloc.vec.Vec arena.handle.LIdx) :
    LS pers (fun a b => b = absLsIdx a) (arena.monad.intern_ls_node pers st v) lst
      (Arena.internLsNode (v.val.map absLIdx)) := by
  -- PENDING foundation intern slice (T2-LOCKSTEP slice 3)
  sorry

end ConRon.Refine2.Lockstep.PA1

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

/-! ## Interns — pending the foundation's intern slice -/

@[lockstep] theorem intern_e_const_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : arena.handle.NIdx) (us : arena.handle.LsIdx) :
    LS pers (fun a b => b = absEIdx a) (arena.monad.intern_e_const pers st n us) lst
      (Arena.internE (.const (absNIdx n) (absLsIdx us))) := by
  -- PENDING foundation intern slice (T2-LOCKSTEP slice 3)
  sorry

end ConRon.Refine2.Lockstep.PA1

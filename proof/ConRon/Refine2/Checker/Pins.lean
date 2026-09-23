/-
# `ConRon.Refine2.Checker.Pins` — Theorem 2 for `arena::pins` and `arena::nat_op_pin_set`

**Task #97-P5-Checker**, deliverable 2's first file (DESIGN.md §8.2).
`crates/con-ron-core/src/arena/{pins,nat_op_pin_set}.rs` against
`proof/ConRon/Arena/{Pins,NatOpPinSet}.lean`: the arena's own pin table — the
forty-nine reserved constant names, the nineteen reserved basis names, the
empty universe-argument list, the level `0` and the expression `Sort 1`, all
interned ONCE by the driver before the prelude — and the `Nat`-operation pin
variants interned beside them.

## Why the fifty-four readers are `SimRE` and not `Sim`

`pin_at(st, i)` takes `&AState` and returns `Result<NIdx, CheckError>`: it
reads the table and can DECLINE (task #97c's hazard, turned into a stop — an
unfilled table is empty, so a pin read before `intern_reserved_pins` raises
`Internal` rather than answering with a word that happens to parse as a
handle), but it never writes.  `Refine2/Shape.lean`'s `SimR` has no error arm
and its `Sim` wants a post-state; `Refine2/Checker/Shape.lean`'s **`SimRE`**
is the two halves put together, and this file is where it earns its keep
fifty-four times.

The `Internal` decline is one of the three MIRRORED kinds, so the claim is
real: the twin declines too, at the same kind, and the two bound tests agree
clause for clause (`i < names.size` on both sides, `names.size = pinCount` on
both sides).  `PinsRel.names` — `lp.names.toList = rp.names.val.map absNIdx`
— is the whole of the correspondence.

## `intern_reserved_pins` is the one WRITER

It is the driver's startup, and DESIGN §8.3's tier discipline is the reason
its statement matters: *after it every pin node is in the persistent cons
table, so a later `intern` of the same node — whatever tier is live — probes
persistent first and hands back the persistent handle*.  The proof is
`Specs.lean`'s `intern_name`, `intern_ls_node`, `intern_l_node` and
`intern_e_sort`, six in a row, then the `Pins` record written whole.

## What these lemmas wait on

`pin_at` and its forty-nine wrappers wait on **nothing below them** — they are
`PinsRel.names` plus a bounds test, which is why they are the cheapest group
of the tier.  `intern_reserved_pins` and the three `intern_pin_set*` wait on
`Specs.lean`'s four transient walks and its per-constructor interns (task
#97-P5-1 §8's thirty-two).
-/
import ConRon.Refine2.Promote.Promote
import ConRon.Refine.PinsAbs
import ConRon.Refine.ExprOpsSubst
import ConRon.Refine.BasisNames

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine (NameWF NamesWF ExprWF StrWF)

/-! ## The table's own two writers and its four readers -/

/-- `pin_names` is the twin's `pinNames`, a pure list of con-leche `Name`s
built by nineteen `basis_names` calls.  The `NamesWF` conjunct is what every
caller of `intern_name_list` owes (`Refine2/Promote/Intern.lean`'s note). -/
theorem pin_names_refines {o} (hrun : arena.pins.pin_names = ok o) :
    ConRon.Refine.absNames o = pinNames ∧ NamesWF o := by
  sorry

/-! ### The startup walk's glue (task #97-P5-Top) -/

/-- The two twin name-list walks are the same function. -/
theorem internNameList_eq_frontend :
    Arena.internNameList = Frontend.internNameList := by
  funext l
  induction l with
  | nil => rfl
  | cons n ns ih => simp only [Arena.internNameList, Frontend.internNameList, ih]

/-- The pin table's nineteen reserved names are con-leche's. -/
theorem reservedBasisNameValues_eq :
    reservedBasisNameValues = ConLeche.reservedBasisNames := by
  rfl

/-- `PersUnfrozen` survives a step that moves no flag. -/
theorem PersUnfrozen.of_flags {a b : arena.store.EStore} (h : PersUnfrozen a)
    (hf : FlagsEq a b) : PersUnfrozen b :=
  ⟨hf.eSh.trans h.e, hf.lssSh.trans h.lss, hf.lsSh.trans h.ls, hf.nsSh.trans h.ns⟩

theorem PersUnfrozen.frozenN {a : arena.store.EStore} (h : PersUnfrozen a) :
    a.lss.ls.ns.shared_on = true → a.lss.ls.ns.scratch_on = true := by
  intro hs; rw [h.ns] at hs; cases hs

theorem PersUnfrozen.frozenL {a : arena.store.EStore} (h : PersUnfrozen a) :
    a.lss.ls.shared_on = true → a.lss.ls.scratch_on = true := by
  intro hs; rw [h.ls] at hs; cases hs

theorem PersUnfrozen.frozenLs {a : arena.store.EStore} (h : PersUnfrozen a) :
    a.lss.shared_on = true → a.lss.scratch_on = true := by
  intro hs; rw [h.lss] at hs; cases hs

theorem PersUnfrozen.frozenE {a : arena.store.EStore} (h : PersUnfrozen a) :
    a.shared_on = true → a.scratch_on = true := by
  intro hs; rw [h.e] at hs; cases hs

/-- **`intern_reserved_pins` ⊑ `internReservedPins`** — the driver's startup:
every reserved constant interned into the PERSISTENT tier once, and the table
installed.  The scratch tier is closed when it runs (the module note says why
that matters), which is `rs.scratch_on = false` here and task #97-P5-1's
finding 8 read from the other side. -/
theorem intern_reserved_pins_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hfr : PersUnfrozen st.store)
    (hrun : arena.pins.intern_reserved_pins pers st = ok o) :
    Sim (fun _ : Unit => ()) (fun _ => True) pers lst o internReservedPins := by
  rw [arena.pins.intern_reserved_pins] at hrun
  unfold Sim
  rw [Arena.internReservedPins, internNameList_eq_frontend]
  -- 1. the forty-nine constant names
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hvabs, hvwf⟩ := pin_names_refines hv
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hS1 := intern_name_list_refines hrel hinv hfr.frozenN hvwf hq1
  have hfr1 := hfr.of_flags (intern_name_list_flags hrel hinv hfr.frozenN hvwf hq1)
  rw [← hvabs]
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut.errBind hS1
  | Ok hs =>
  obtain ⟨lst1, hx1, hrel1, hinv1, hext1, -⟩ := Sim.apply hS1
  rw [run_bind_ok hx1]
  refine AOut.rebase hext1 ?_
  -- 2. the nineteen reserved basis names
  obtain ⟨v1, hv1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hv1abs, hv1wf⟩ := ConRon.Refine.BasisNames.reserved_basis_names_refines hv1
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hS2 := intern_name_list_refines hrel1 hinv1 hfr1.frozenN hv1wf hq2
  have hfr2 := hfr1.of_flags (intern_name_list_flags hrel1 hinv1 hfr1.frozenN hv1wf hq2)
  rw [reservedBasisNameValues_eq, ← hv1abs]
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut.errBind hS2
  | Ok rs =>
  obtain ⟨lst2, hx2, hrel2, hinv2, hext2, -⟩ := Sim.apply hS2
  rw [run_bind_ok hx2]
  refine AOut.rebase hext2 ?_
  -- 3. the empty universe-argument list
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r3, st3⟩ := q3
  have hS3 := intern_ls_node_run hrel2 hinv2 hfr2.frozenLs
    (alloc.vec.Vec.new arena.handle.LIdx) (fun c hc => by simp [absLsNodeView] at hc) hq3
  have hfr3 := hfr2.of_flags (intern_ls_node_flags hq3)
  have hnil : absLsNodeView (alloc.vec.Vec.new arena.handle.LIdx) = [] := rfl
  rw [hnil] at hS3
  cases r3 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut.errBind hS3
  | Ok us =>
  obtain ⟨lst3, hx3, hrel3, hinv3, hext3, -⟩ := Sim.apply hS3
  rw [run_bind_ok hx3]
  refine AOut.rebase hext3 ?_
  -- 4. the level `0`
  obtain ⟨q4, hq4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r4, st4⟩ := q4
  have hv0 : lst3.store.ls.ViewOK (absLNodeView arena.store.LNodeView.Zero) := by
    constructor
    · intro c hc; simp [absLNodeView, LNodeView.lchildren] at hc
    · intro c hc; simp [absLNodeView, LNodeView.nchildren] at hc
  have hS4 := intern_l_node_run hrel3 hinv3 hfr3.frozenL arena.store.LNodeView.Zero hv0 hq4
  have hfr4 := hfr3.of_flags (intern_l_node_flags hq4)
  cases r4 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut.errBind hS4
  | Ok z =>
  obtain ⟨lst4, hx4, hrel4, hinv4, hext4, -⟩ := Sim.apply hS4
  rw [show Arena.internLNode LNodeView.zero
      = Arena.internLNode (absLNodeView arena.store.LNodeView.Zero) from rfl,
    run_bind_ok hx4]
  refine AOut.rebase hext4 ?_
  -- 5. the level `1`
  obtain ⟨l, hl, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hl' : l = z := dupId_lidx _ _ hl
  rw [hl'] at hrun
  obtain ⟨q5, hq5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r5, st5⟩ := q5
  have hlz : (Arena.internLevel ConLeche.Level.zero).run lst3
      = .ok (absLIdx z, lst4) := hx4
  obtain ⟨hdz, -, -⟩ := internLevel_run_denote _ hrel3.storeWF hlz
  obtain ⟨vz, hvz⟩ := denoteL_view hdz
  have hv1' : lst4.store.ls.ViewOK (absLNodeView (arena.store.LNodeView.Succ z)) := by
    constructor
    · intro c hc
      simp only [absLNodeView, LNodeView.lchildren, List.mem_singleton] at hc
      subst hc; rw [hvz]; rfl
    · intro c hc; simp [absLNodeView, LNodeView.nchildren] at hc
  have hS5 := intern_l_node_run hrel4 hinv4 hfr4.frozenL (arena.store.LNodeView.Succ z)
    hv1' hq5
  cases r5 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut.errBind hS5
  | Ok one =>
  obtain ⟨lst5, hx5, hrel5, hinv5, hext5, -⟩ := Sim.apply hS5
  rw [show (Arena.internLNode (.succ (absLIdx z)))
      = Arena.internLNode (absLNodeView (arena.store.LNodeView.Succ z)) from rfl,
    run_bind_ok hx5]
  refine AOut.rebase hext5 ?_
  -- 6. the expression `Sort 1`
  obtain ⟨q6, hq6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r6, st6⟩ := q6
  have hlo : (Arena.internLevel (ConLeche.Level.succ ConLeche.Level.zero)).run lst3
      = .ok (absLIdx one, lst5) := by
    show (Arena.internLevel ConLeche.Level.zero >>= fun hu =>
      Arena.internLNode (.succ hu)).run lst3 = _
    rw [run_bind_ok hlz]; exact hx5
  obtain ⟨hdo, -, -⟩ := internLevel_run_denote _ hrel3.storeWF hlo
  obtain ⟨vo, hvo⟩ := denoteL_view hdo
  have hv2 : lst5.store.ViewOK (.sort (absLIdx one)) := by
    constructor
    · intro c hc; simp [ENodeView.echildren] at hc
    · intro c hc; simp [ENodeView.nchildren] at hc
    · intro c hc
      simp only [ENodeView.lchildren, List.mem_singleton] at hc
      subst hc; rw [hvo]; rfl
    · intro c hc; simp [ENodeView.lschildren] at hc
  have hfr5 := hfr4.of_flags (intern_l_node_flags hq5)
  have hS6 := intern_e_sort_run hrel5 hinv5 hfr5.frozenE one
    (fun h => hchild_sort hrel5.storeWF h) hv2 hq6
  cases r6 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut.errBind hS6
  | Ok s1 =>
  obtain ⟨lst6, hx6, hrel6, hinv6, hext6, -⟩ := Sim.apply hS6
  rw [run_bind_ok hx6]
  refine AOut.rebase hext6 ?_
  -- 7. the table, written whole
  have ho := Result.ok_injective hrun
  subst ho
  refine AOut.ok (lst' := { lst6 with pins :=
      { names := (absNIdxL hs).toArray, reserved := absNIdxL rs,
        emptyLevels := absLsIdx us, zeroLevel := absLIdx z, sortOne := absEIdx s1 } })
    rfl ?_ ⟨hinv6.store, hinv6.memos, hinv6.caches⟩ (Ext.refl _) trivial
  exact ⟨hrel6.store, hrel6.memos, hrel6.caches,
    ⟨by simp [absNIdxL], rfl, rfl, rfl, rfl⟩, hrel6.storeWF⟩

/-- `pins_ready` ⊑ `pinsReady` — a length test, because an unfilled table is
EMPTY and not a sentinel handle. -/
theorem pins_ready_refines {pers st lst} {o : Bool}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
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
theorem pin_at_refines {pers st lst} {i : Std.Usize} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_at st i = ok o) :
    SimRE absNIdx lst o (pinAt (absSz i)) := by
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
theorem pin_reserved_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_reserved st = ok o) :
    SimRE absNIdxL lst o pinReserved := by
  sorry

/-- `pin_empty_levels` ⊑ `pinEmptyLevels`. -/
theorem pin_empty_levels_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_empty_levels st = ok o) :
    SimRE absLsIdx lst o pinEmptyLevels := by
  rw [arena.pins.pin_empty_levels] at hrun
  obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hbr := pins_ready_refines hrel hinv hb
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
theorem pin_zero_level_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_zero_level st = ok o) :
    SimRE absLIdx lst o pinZeroLevel := by
  rw [arena.pins.pin_zero_level] at hrun
  obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hbr := pins_ready_refines hrel hinv hb
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
theorem pin_sort_one_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_sort_one st = ok o) :
    SimRE absEIdx lst o pinSortOne := by
  rw [arena.pins.pin_sort_one] at hrun
  obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hbr := pins_ready_refines hrel hinv hb
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

Each is `pin_at` at its own constant, and each lemma is `pin_at_refines` after
that constant's value.  The order is `Arena/Pins.lean`'s, which is
`arena::pins`'s. -/

/-- `pin_eq` ⊑ `pinEq`, at slot `PIN_EQ`. -/
theorem pin_eq_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_eq st = ok o) :
    SimRE absNIdx lst o pinEq := by
  rw [arena.pins.pin_eq] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_EQ = Arena.PIN_EQ := by
    show (arena.pins.PIN_EQ).val = _
    rw [arena.pins.PIN_EQ]
    rfl
  rw [hc] at h
  exact h

/-- `pin_punit` ⊑ `pinPUnit`, at slot `PIN_PUNIT`. -/
theorem pin_punit_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_punit st = ok o) :
    SimRE absNIdx lst o pinPUnit := by
  rw [arena.pins.pin_punit] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_PUNIT = Arena.PIN_PUNIT := by
    show (arena.pins.PIN_PUNIT).val = _
    rw [arena.pins.PIN_PUNIT]
    rfl
  rw [hc] at h
  exact h

/-- `pin_punit_rec` ⊑ `pinPUnitRec`, at slot `PIN_PUNIT_REC`. -/
theorem pin_punit_rec_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_punit_rec st = ok o) :
    SimRE absNIdx lst o pinPUnitRec := by
  rw [arena.pins.pin_punit_rec] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_PUNIT_REC = Arena.PIN_PUNIT_REC := by
    show (arena.pins.PIN_PUNIT_REC).val = _
    rw [arena.pins.PIN_PUNIT_REC]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat` ⊑ `pinNat`, at slot `PIN_NAT`. -/
theorem pin_nat_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat st = ok o) :
    SimRE absNIdx lst o pinNat := by
  rw [arena.pins.pin_nat] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT = Arena.PIN_NAT := by
    show (arena.pins.PIN_NAT).val = _
    rw [arena.pins.PIN_NAT]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_zero` ⊑ `pinNatZero`, at slot `PIN_NAT_ZERO`. -/
theorem pin_nat_zero_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_zero st = ok o) :
    SimRE absNIdx lst o pinNatZero := by
  rw [arena.pins.pin_nat_zero] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_ZERO = Arena.PIN_NAT_ZERO := by
    show (arena.pins.PIN_NAT_ZERO).val = _
    rw [arena.pins.PIN_NAT_ZERO]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_succ` ⊑ `pinNatSucc`, at slot `PIN_NAT_SUCC`. -/
theorem pin_nat_succ_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_succ st = ok o) :
    SimRE absNIdx lst o pinNatSucc := by
  rw [arena.pins.pin_nat_succ] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_SUCC = Arena.PIN_NAT_SUCC := by
    show (arena.pins.PIN_NAT_SUCC).val = _
    rw [arena.pins.PIN_NAT_SUCC]
    rfl
  rw [hc] at h
  exact h

/-- `pin_quot_sound` ⊑ `pinQuotSound`, at slot `PIN_QUOT_SOUND`. -/
theorem pin_quot_sound_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_quot_sound st = ok o) :
    SimRE absNIdx lst o pinQuotSound := by
  rw [arena.pins.pin_quot_sound] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_QUOT_SOUND = Arena.PIN_QUOT_SOUND := by
    show (arena.pins.PIN_QUOT_SOUND).val = _
    rw [arena.pins.PIN_QUOT_SOUND]
    rfl
  rw [hc] at h
  exact h

/-- `pin_string` ⊑ `pinString`, at slot `PIN_STRING`. -/
theorem pin_string_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_string st = ok o) :
    SimRE absNIdx lst o pinString := by
  rw [arena.pins.pin_string] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_STRING = Arena.PIN_STRING := by
    show (arena.pins.PIN_STRING).val = _
    rw [arena.pins.PIN_STRING]
    rfl
  rw [hc] at h
  exact h

/-- `pin_string_of_list` ⊑ `pinStringOfList`, at slot `PIN_STRING_OF_LIST`. -/
theorem pin_string_of_list_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_string_of_list st = ok o) :
    SimRE absNIdx lst o pinStringOfList := by
  rw [arena.pins.pin_string_of_list] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_STRING_OF_LIST = Arena.PIN_STRING_OF_LIST := by
    show (arena.pins.PIN_STRING_OF_LIST).val = _
    rw [arena.pins.PIN_STRING_OF_LIST]
    rfl
  rw [hc] at h
  exact h

/-- `pin_list` ⊑ `pinList`, at slot `PIN_LIST`. -/
theorem pin_list_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_list st = ok o) :
    SimRE absNIdx lst o pinList := by
  rw [arena.pins.pin_list] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_LIST = Arena.PIN_LIST := by
    show (arena.pins.PIN_LIST).val = _
    rw [arena.pins.PIN_LIST]
    rfl
  rw [hc] at h
  exact h

/-- `pin_list_nil` ⊑ `pinListNil`, at slot `PIN_LIST_NIL`. -/
theorem pin_list_nil_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_list_nil st = ok o) :
    SimRE absNIdx lst o pinListNil := by
  rw [arena.pins.pin_list_nil] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_LIST_NIL = Arena.PIN_LIST_NIL := by
    show (arena.pins.PIN_LIST_NIL).val = _
    rw [arena.pins.PIN_LIST_NIL]
    rfl
  rw [hc] at h
  exact h

/-- `pin_list_cons` ⊑ `pinListCons`, at slot `PIN_LIST_CONS`. -/
theorem pin_list_cons_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_list_cons st = ok o) :
    SimRE absNIdx lst o pinListCons := by
  rw [arena.pins.pin_list_cons] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_LIST_CONS = Arena.PIN_LIST_CONS := by
    show (arena.pins.PIN_LIST_CONS).val = _
    rw [arena.pins.PIN_LIST_CONS]
    rfl
  rw [hc] at h
  exact h

/-- `pin_char` ⊑ `pinChar`, at slot `PIN_CHAR`. -/
theorem pin_char_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_char st = ok o) :
    SimRE absNIdx lst o pinChar := by
  rw [arena.pins.pin_char] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_CHAR = Arena.PIN_CHAR := by
    show (arena.pins.PIN_CHAR).val = _
    rw [arena.pins.PIN_CHAR]
    rfl
  rw [hc] at h
  exact h

/-- `pin_and` ⊑ `pinAnd`, at slot `PIN_AND`. -/
theorem pin_and_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_and st = ok o) :
    SimRE absNIdx lst o pinAnd := by
  rw [arena.pins.pin_and] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_AND = Arena.PIN_AND := by
    show (arena.pins.PIN_AND).val = _
    rw [arena.pins.PIN_AND]
    rfl
  rw [hc] at h
  exact h

/-- `pin_char_of_nat` ⊑ `pinCharOfNat`, at slot `PIN_CHAR_OF_NAT`. -/
theorem pin_char_of_nat_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_char_of_nat st = ok o) :
    SimRE absNIdx lst o pinCharOfNat := by
  rw [arena.pins.pin_char_of_nat] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_CHAR_OF_NAT = Arena.PIN_CHAR_OF_NAT := by
    show (arena.pins.PIN_CHAR_OF_NAT).val = _
    rw [arena.pins.PIN_CHAR_OF_NAT]
    rfl
  rw [hc] at h
  exact h

/-- `pin_sorry_ax` ⊑ `pinSorryAx`, at slot `PIN_SORRY_AX`. -/
theorem pin_sorry_ax_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_sorry_ax st = ok o) :
    SimRE absNIdx lst o pinSorryAx := by
  rw [arena.pins.pin_sorry_ax] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_SORRY_AX = Arena.PIN_SORRY_AX := by
    show (arena.pins.PIN_SORRY_AX).val = _
    rw [arena.pins.PIN_SORRY_AX]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_pred` ⊑ `pinNatPred`, at slot `PIN_NAT_PRED`. -/
theorem pin_nat_pred_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_pred st = ok o) :
    SimRE absNIdx lst o pinNatPred := by
  rw [arena.pins.pin_nat_pred] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_PRED = Arena.PIN_NAT_PRED := by
    show (arena.pins.PIN_NAT_PRED).val = _
    rw [arena.pins.PIN_NAT_PRED]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_add` ⊑ `pinNatAdd`, at slot `PIN_NAT_ADD`. -/
theorem pin_nat_add_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_add st = ok o) :
    SimRE absNIdx lst o pinNatAdd := by
  rw [arena.pins.pin_nat_add] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_ADD = Arena.PIN_NAT_ADD := by
    show (arena.pins.PIN_NAT_ADD).val = _
    rw [arena.pins.PIN_NAT_ADD]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_sub` ⊑ `pinNatSub`, at slot `PIN_NAT_SUB`. -/
theorem pin_nat_sub_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_sub st = ok o) :
    SimRE absNIdx lst o pinNatSub := by
  rw [arena.pins.pin_nat_sub] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_SUB = Arena.PIN_NAT_SUB := by
    show (arena.pins.PIN_NAT_SUB).val = _
    rw [arena.pins.PIN_NAT_SUB]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_mul` ⊑ `pinNatMul`, at slot `PIN_NAT_MUL`. -/
theorem pin_nat_mul_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_mul st = ok o) :
    SimRE absNIdx lst o pinNatMul := by
  rw [arena.pins.pin_nat_mul] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_MUL = Arena.PIN_NAT_MUL := by
    show (arena.pins.PIN_NAT_MUL).val = _
    rw [arena.pins.PIN_NAT_MUL]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_pow` ⊑ `pinNatPow`, at slot `PIN_NAT_POW`. -/
theorem pin_nat_pow_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_pow st = ok o) :
    SimRE absNIdx lst o pinNatPow := by
  rw [arena.pins.pin_nat_pow] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_POW = Arena.PIN_NAT_POW := by
    show (arena.pins.PIN_NAT_POW).val = _
    rw [arena.pins.PIN_NAT_POW]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_beq` ⊑ `pinNatBeq`, at slot `PIN_NAT_BEQ`. -/
theorem pin_nat_beq_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_beq st = ok o) :
    SimRE absNIdx lst o pinNatBeq := by
  rw [arena.pins.pin_nat_beq] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_BEQ = Arena.PIN_NAT_BEQ := by
    show (arena.pins.PIN_NAT_BEQ).val = _
    rw [arena.pins.PIN_NAT_BEQ]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_ble` ⊑ `pinNatBle`, at slot `PIN_NAT_BLE`. -/
theorem pin_nat_ble_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_ble st = ok o) :
    SimRE absNIdx lst o pinNatBle := by
  rw [arena.pins.pin_nat_ble] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_BLE = Arena.PIN_NAT_BLE := by
    show (arena.pins.PIN_NAT_BLE).val = _
    rw [arena.pins.PIN_NAT_BLE]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_div` ⊑ `pinNatDiv`, at slot `PIN_NAT_DIV`. -/
theorem pin_nat_div_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_div st = ok o) :
    SimRE absNIdx lst o pinNatDiv := by
  rw [arena.pins.pin_nat_div] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_DIV = Arena.PIN_NAT_DIV := by
    show (arena.pins.PIN_NAT_DIV).val = _
    rw [arena.pins.PIN_NAT_DIV]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_mod` ⊑ `pinNatMod`, at slot `PIN_NAT_MOD`. -/
theorem pin_nat_mod_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_mod st = ok o) :
    SimRE absNIdx lst o pinNatMod := by
  rw [arena.pins.pin_nat_mod] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_MOD = Arena.PIN_NAT_MOD := by
    show (arena.pins.PIN_NAT_MOD).val = _
    rw [arena.pins.PIN_NAT_MOD]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_gcd` ⊑ `pinNatGcd`, at slot `PIN_NAT_GCD`. -/
theorem pin_nat_gcd_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_gcd st = ok o) :
    SimRE absNIdx lst o pinNatGcd := by
  rw [arena.pins.pin_nat_gcd] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_GCD = Arena.PIN_NAT_GCD := by
    show (arena.pins.PIN_NAT_GCD).val = _
    rw [arena.pins.PIN_NAT_GCD]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_land` ⊑ `pinNatLand`, at slot `PIN_NAT_LAND`. -/
theorem pin_nat_land_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_land st = ok o) :
    SimRE absNIdx lst o pinNatLand := by
  rw [arena.pins.pin_nat_land] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_LAND = Arena.PIN_NAT_LAND := by
    show (arena.pins.PIN_NAT_LAND).val = _
    rw [arena.pins.PIN_NAT_LAND]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_lor` ⊑ `pinNatLor`, at slot `PIN_NAT_LOR`. -/
theorem pin_nat_lor_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_lor st = ok o) :
    SimRE absNIdx lst o pinNatLor := by
  rw [arena.pins.pin_nat_lor] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_LOR = Arena.PIN_NAT_LOR := by
    show (arena.pins.PIN_NAT_LOR).val = _
    rw [arena.pins.PIN_NAT_LOR]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_xor` ⊑ `pinNatXor`, at slot `PIN_NAT_XOR`. -/
theorem pin_nat_xor_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_xor st = ok o) :
    SimRE absNIdx lst o pinNatXor := by
  rw [arena.pins.pin_nat_xor] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_XOR = Arena.PIN_NAT_XOR := by
    show (arena.pins.PIN_NAT_XOR).val = _
    rw [arena.pins.PIN_NAT_XOR]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_shift_left` ⊑ `pinNatShiftLeft`, at slot `PIN_NAT_SHIFT_LEFT`. -/
theorem pin_nat_shift_left_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_shift_left st = ok o) :
    SimRE absNIdx lst o pinNatShiftLeft := by
  rw [arena.pins.pin_nat_shift_left] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_SHIFT_LEFT = Arena.PIN_NAT_SHIFT_LEFT := by
    show (arena.pins.PIN_NAT_SHIFT_LEFT).val = _
    rw [arena.pins.PIN_NAT_SHIFT_LEFT]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nat_shift_right` ⊑ `pinNatShiftRight`, at slot `PIN_NAT_SHIFT_RIGHT`. -/
theorem pin_nat_shift_right_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nat_shift_right st = ok o) :
    SimRE absNIdx lst o pinNatShiftRight := by
  rw [arena.pins.pin_nat_shift_right] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NAT_SHIFT_RIGHT = Arena.PIN_NAT_SHIFT_RIGHT := by
    show (arena.pins.PIN_NAT_SHIFT_RIGHT).val = _
    rw [arena.pins.PIN_NAT_SHIFT_RIGHT]
    rfl
  rw [hc] at h
  exact h

/-- `pin_bool` ⊑ `pinBool`, at slot `PIN_BOOL`. -/
theorem pin_bool_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_bool st = ok o) :
    SimRE absNIdx lst o pinBool := by
  rw [arena.pins.pin_bool] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_BOOL = Arena.PIN_BOOL := by
    show (arena.pins.PIN_BOOL).val = _
    rw [arena.pins.PIN_BOOL]
    rfl
  rw [hc] at h
  exact h

/-- `pin_bool_true` ⊑ `pinBoolTrue`, at slot `PIN_BOOL_TRUE`. -/
theorem pin_bool_true_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_bool_true st = ok o) :
    SimRE absNIdx lst o pinBoolTrue := by
  rw [arena.pins.pin_bool_true] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_BOOL_TRUE = Arena.PIN_BOOL_TRUE := by
    show (arena.pins.PIN_BOOL_TRUE).val = _
    rw [arena.pins.PIN_BOOL_TRUE]
    rfl
  rw [hc] at h
  exact h

/-- `pin_bool_false` ⊑ `pinBoolFalse`, at slot `PIN_BOOL_FALSE`. -/
theorem pin_bool_false_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_bool_false st = ok o) :
    SimRE absNIdx lst o pinBoolFalse := by
  rw [arena.pins.pin_bool_false] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_BOOL_FALSE = Arena.PIN_BOOL_FALSE := by
    show (arena.pins.PIN_BOOL_FALSE).val = _
    rw [arena.pins.PIN_BOOL_FALSE]
    rfl
  rw [hc] at h
  exact h

/-- `pin_propext` ⊑ `pinPropext`, at slot `PIN_PROPEXT`. -/
theorem pin_propext_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_propext st = ok o) :
    SimRE absNIdx lst o pinPropext := by
  rw [arena.pins.pin_propext] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_PROPEXT = Arena.PIN_PROPEXT := by
    show (arena.pins.PIN_PROPEXT).val = _
    rw [arena.pins.PIN_PROPEXT]
    rfl
  rw [hc] at h
  exact h

/-- `pin_choice` ⊑ `pinChoice`, at slot `PIN_CHOICE`. -/
theorem pin_choice_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_choice st = ok o) :
    SimRE absNIdx lst o pinChoice := by
  rw [arena.pins.pin_choice] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_CHOICE = Arena.PIN_CHOICE := by
    show (arena.pins.PIN_CHOICE).val = _
    rw [arena.pins.PIN_CHOICE]
    rfl
  rw [hc] at h
  exact h

/-- `pin_iff` ⊑ `pinIff`, at slot `PIN_IFF`. -/
theorem pin_iff_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_iff st = ok o) :
    SimRE absNIdx lst o pinIff := by
  rw [arena.pins.pin_iff] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_IFF = Arena.PIN_IFF := by
    show (arena.pins.PIN_IFF).val = _
    rw [arena.pins.PIN_IFF]
    rfl
  rw [hc] at h
  exact h

/-- `pin_iff_intro` ⊑ `pinIffIntro`, at slot `PIN_IFF_INTRO`. -/
theorem pin_iff_intro_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_iff_intro st = ok o) :
    SimRE absNIdx lst o pinIffIntro := by
  rw [arena.pins.pin_iff_intro] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_IFF_INTRO = Arena.PIN_IFF_INTRO := by
    show (arena.pins.PIN_IFF_INTRO).val = _
    rw [arena.pins.PIN_IFF_INTRO]
    rfl
  rw [hc] at h
  exact h

/-- `pin_iff_rec` ⊑ `pinIffRec`, at slot `PIN_IFF_REC`. -/
theorem pin_iff_rec_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_iff_rec st = ok o) :
    SimRE absNIdx lst o pinIffRec := by
  rw [arena.pins.pin_iff_rec] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_IFF_REC = Arena.PIN_IFF_REC := by
    show (arena.pins.PIN_IFF_REC).val = _
    rw [arena.pins.PIN_IFF_REC]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nonempty` ⊑ `pinNonempty`, at slot `PIN_NONEMPTY`. -/
theorem pin_nonempty_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nonempty st = ok o) :
    SimRE absNIdx lst o pinNonempty := by
  rw [arena.pins.pin_nonempty] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NONEMPTY = Arena.PIN_NONEMPTY := by
    show (arena.pins.PIN_NONEMPTY).val = _
    rw [arena.pins.PIN_NONEMPTY]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nonempty_intro` ⊑ `pinNonemptyIntro`, at slot `PIN_NONEMPTY_INTRO`. -/
theorem pin_nonempty_intro_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nonempty_intro st = ok o) :
    SimRE absNIdx lst o pinNonemptyIntro := by
  rw [arena.pins.pin_nonempty_intro] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NONEMPTY_INTRO = Arena.PIN_NONEMPTY_INTRO := by
    show (arena.pins.PIN_NONEMPTY_INTRO).val = _
    rw [arena.pins.PIN_NONEMPTY_INTRO]
    rfl
  rw [hc] at h
  exact h

/-- `pin_nonempty_rec` ⊑ `pinNonemptyRec`, at slot `PIN_NONEMPTY_REC`. -/
theorem pin_nonempty_rec_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_nonempty_rec st = ok o) :
    SimRE absNIdx lst o pinNonemptyRec := by
  rw [arena.pins.pin_nonempty_rec] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_NONEMPTY_REC = Arena.PIN_NONEMPTY_REC := by
    show (arena.pins.PIN_NONEMPTY_REC).val = _
    rw [arena.pins.PIN_NONEMPTY_REC]
    rfl
  rw [hc] at h
  exact h

/-- `pin_true` ⊑ `pinTrue`, at slot `PIN_TRUE`. -/
theorem pin_true_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_true st = ok o) :
    SimRE absNIdx lst o pinTrue := by
  rw [arena.pins.pin_true] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_TRUE = Arena.PIN_TRUE := by
    show (arena.pins.PIN_TRUE).val = _
    rw [arena.pins.PIN_TRUE]
    rfl
  rw [hc] at h
  exact h

/-- `pin_true_intro` ⊑ `pinTrueIntro`, at slot `PIN_TRUE_INTRO`. -/
theorem pin_true_intro_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_true_intro st = ok o) :
    SimRE absNIdx lst o pinTrueIntro := by
  rw [arena.pins.pin_true_intro] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_TRUE_INTRO = Arena.PIN_TRUE_INTRO := by
    show (arena.pins.PIN_TRUE_INTRO).val = _
    rw [arena.pins.PIN_TRUE_INTRO]
    rfl
  rw [hc] at h
  exact h

/-- `pin_trust_compiler` ⊑ `pinTrustCompiler`, at slot `PIN_TRUST_COMPILER`. -/
theorem pin_trust_compiler_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_trust_compiler st = ok o) :
    SimRE absNIdx lst o pinTrustCompiler := by
  rw [arena.pins.pin_trust_compiler] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_TRUST_COMPILER = Arena.PIN_TRUST_COMPILER := by
    show (arena.pins.PIN_TRUST_COMPILER).val = _
    rw [arena.pins.PIN_TRUST_COMPILER]
    rfl
  rw [hc] at h
  exact h

/-- `pin_reduce_nat` ⊑ `pinReduceNat`, at slot `PIN_REDUCE_NAT`. -/
theorem pin_reduce_nat_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_reduce_nat st = ok o) :
    SimRE absNIdx lst o pinReduceNat := by
  rw [arena.pins.pin_reduce_nat] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_REDUCE_NAT = Arena.PIN_REDUCE_NAT := by
    show (arena.pins.PIN_REDUCE_NAT).val = _
    rw [arena.pins.PIN_REDUCE_NAT]
    rfl
  rw [hc] at h
  exact h

/-- `pin_reduce_bool` ⊑ `pinReduceBool`, at slot `PIN_REDUCE_BOOL`. -/
theorem pin_reduce_bool_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_reduce_bool st = ok o) :
    SimRE absNIdx lst o pinReduceBool := by
  rw [arena.pins.pin_reduce_bool] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_REDUCE_BOOL = Arena.PIN_REDUCE_BOOL := by
    show (arena.pins.PIN_REDUCE_BOOL).val = _
    rw [arena.pins.PIN_REDUCE_BOOL]
    rfl
  rw [hc] at h
  exact h

/-- `pin_of_reduce_nat` ⊑ `pinOfReduceNat`, at slot `PIN_OF_REDUCE_NAT`. -/
theorem pin_of_reduce_nat_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_of_reduce_nat st = ok o) :
    SimRE absNIdx lst o pinOfReduceNat := by
  rw [arena.pins.pin_of_reduce_nat] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_OF_REDUCE_NAT = Arena.PIN_OF_REDUCE_NAT := by
    show (arena.pins.PIN_OF_REDUCE_NAT).val = _
    rw [arena.pins.PIN_OF_REDUCE_NAT]
    rfl
  rw [hc] at h
  exact h

/-- `pin_of_reduce_bool` ⊑ `pinOfReduceBool`, at slot `PIN_OF_REDUCE_BOOL`. -/
theorem pin_of_reduce_bool_refines {pers st lst} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_of_reduce_bool st = ok o) :
    SimRE absNIdx lst o pinOfReduceBool := by
  rw [arena.pins.pin_of_reduce_bool] at hrun
  have h := pin_at_refines hrel hinv hrun
  have hc : absSz arena.pins.PIN_OF_REDUCE_BOOL = Arena.PIN_OF_REDUCE_BOOL := by
    show (arena.pins.PIN_OF_REDUCE_BOOL).val = _
    rw [arena.pins.PIN_OF_REDUCE_BOOL]
    rfl
  rw [hc] at h
  exact h

/-! ## `arena::nat_op_pin_set` — the `Nat`-operation pin variants

DESIGN §8.6 P2d: *intern con-leche's `natOpPinSets` `Expr`s into the
persistent tier at startup — a one-time tree walk*.  Sixteen terms deep per
variant, and `Modeller`-style indirection is explicitly NOT wanted: the pins
are data the checker reads, not a seam. -/

/-- `intern_pin_set_proofs` is the Rust-only tail of `intern_pin_set` past its
eight pinned defining expressions (extraction rule 5 again — eight live
handles is more than the loan checker will carry across a second walk), so it
is stated against the same twin with those eight in hand. -/
theorem intern_pin_set_proofs_refines {pers st lst}
    {ps : kernel.nat_op_pins.NatOpPinSet}
    {dp mp gp lap lop xp slp srp : arena.handle.EIdx} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hwf : NatOpPinSetWF ps)
    (hrun : arena.nat_op_pin_set.intern_pin_set_proofs pers st ps dp mp gp lap
      lop xp slp srp = ok o) :
    Sim absINatOpPinSet (fun _ => True) pers lst o
      (do
        let dc ← internExprList (ConRon.Refine.absExprs ps.div_proofs)
        let mc ← internExprList (ConRon.Refine.absExprs ps.mod_proofs)
        let gc ← internExprList (ConRon.Refine.absExprs ps.gcd_proofs)
        let lac ← internExprList (ConRon.Refine.absExprs ps.land_proofs)
        let loc ← internExprList (ConRon.Refine.absExprs ps.lor_proofs)
        let xc ← internExprList (ConRon.Refine.absExprs ps.xor_proofs)
        let slc ← internExprList (ConRon.Refine.absExprs ps.shift_left_proofs)
        let src ← internExprList (ConRon.Refine.absExprs ps.shift_right_proofs)
        pure ⟨ConRon.Refine.absString ps.toolchain, absEIdx dp, absEIdx mp,
          absEIdx gp, absEIdx lap, absEIdx lop, absEIdx xp, absEIdx slp,
          absEIdx srp, dc, mc, gc, lac, loc, xc, slc, src⟩) := by
  sorry

/-- `intern_pin_set` ⊑ `internPinSet` — one variant, sixteen terms. -/
theorem intern_pin_set_refines {pers st lst}
    {ps : kernel.nat_op_pins.NatOpPinSet} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hwf : NatOpPinSetWF ps)
    (hrun : arena.nat_op_pin_set.intern_pin_set pers st ps = ok o) :
    Sim absINatOpPinSet (fun _ => True) pers lst o
      (internPinSet (ConRon.Refine.absNatOpPinSet ps)) := by
  sorry

/-- `intern_pin_sets` ⊑ `internPinSets` at the cursor — the variant LIST, in
the order the install gate tries them. -/
theorem intern_pin_sets_refines {pers st lst}
    {pss : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet} {i : Std.Usize}
    {out : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {o}
    (hrel : AStateRel pers st lst) (hinv : AStateInv pers st)
    (hwf : ∀ p ∈ pss.val, NatOpPinSetWF p)
    (hrun : arena.nat_op_pin_set.intern_pin_sets pers st pss i out = ok o) :
    Sim absINatOpPinSetL (fun _ => True)
      pers lst o
      (do pure (absINatOpPinSetL out ++
        (← internPinSets ((pss.val.drop i.val).map ConRon.Refine.absNatOpPinSet)))) := by
  sorry


/-! ## The axiom census

DESIGN.md §8.2's own discipline (task #97-P5-0 §8, task #97-P5-1 §7): every
CLOSED lemma of the tier is `#print axioms`-checked under `#guard_msgs`, and
every one reads `[propext, Classical.choice, Quot.sound]` and nothing else —
no `sorryAx` on a closed lemma, no `bv_decide` axiom anywhere.  `pin_at` is
the one this file's fifty-four readers all reduce to, so it is the row that
matters; three of the forty-nine wrappers and the three table readers stand
for the rest. -/

/-- info: 'ConRon.Refine2.pin_at_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pin_at_refines

/-- info: 'ConRon.Refine2.pins_ready_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pins_ready_refines

/-- info: 'ConRon.Refine2.pin_eq_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pin_eq_refines

/-- info: 'ConRon.Refine2.pin_nat_div_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pin_nat_div_refines

/-- info: 'ConRon.Refine2.pin_of_reduce_bool_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pin_of_reduce_bool_refines

/-- info: 'ConRon.Refine2.pin_empty_levels_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pin_empty_levels_refines

/-- info: 'ConRon.Refine2.pin_zero_level_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pin_zero_level_refines

/-- info: 'ConRon.Refine2.pin_sort_one_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pin_sort_one_refines

end ConRon.Refine2

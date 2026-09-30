/-
# `ConRon.Refine2.Inductives.Positivity` — Theorem 2 for `positivity`'s low part

**Task #105** (DESIGN.md §8.2, Theorem 2).  The functions of
`crates/con-ron-core/src/arena/inductives/positivity.rs` whose proofs need only
the store and `ExprOps` primitives, against their twins in
`proof/ConRon/Arena/Inductives/Positivity.lean`: the memoised walks
(`mentions_any_go`, `nest_occ_go`, `depth_go`, `replace_fvars_go`,
`replace_apps_go`), the telescope helpers, the read-back block and the pure
record copies.  The functions that reach the checker core (`whnf`,
`infer_type_core`, level comparison, environment lookups) and the `nest_pos`
block are in `PositivityNest.lean`.

## Shapes

* A Rust memo is a `HashMap2`, the twin's a `Std.HashMap`: related by
  `RelOn` + `Inv` (`ExprOps.LMemoRel` for the `bool` memos, `PEMemoRel` /
  `NMemoRel` below for the `EIdx`/`u64` ones), threaded through the answer.
* The Rust's `…_node` fragments are unfolded in place (they are the twin's
  inner `match`).
* A Rust index cursor is the twin's list operation from the cursor on.
-/
import ConRon.Refine2.Inductives.Abs
import ConRon.Arena.Inductives.Positivity

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open Lockstep
open scoped IndSide

/-! ## Helpers for Shape/Abs -/

/-- `CORE_WALK_FUEL = coreWalkFuel` (`Core/Arms/Delta.lean`'s
`core_walk_fuel_abs`, restated here below the core tier). -/
theorem pos_core_walk_fuel_abs : absU arena.core.CORE_WALK_FUEL = coreWalkFuel := by
  rw [arena.core.CORE_WALK_FUEL, Arena.coreWalkFuel]
  rfl

theorem pos_core_walk_fuel_val : (arena.core.CORE_WALK_FUEL).val = coreWalkFuel :=
  pos_core_walk_fuel_abs

attribute [local lockstep_simp] pos_core_walk_fuel_abs pos_core_walk_fuel_val

/-- `arena::pins::pins_ready` ⊑ `pinsReady` (`Core/LS/PrimsA1.lean`'s
`pins_ready_run₀`, restated below the core tier). -/
theorem pos_pins_ready_run₀ {pers st lst} {o : Bool}
    (hrel : AStateRel₀ pers st lst)
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

/-- `arena::core::zero_level` ⊑ `zeroLevel` (`Core/LS/Leaves.lean`'s
`zero_level_ls`, restated below the core tier; LOCAL to this file). -/
theorem pos_zero_level_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absLIdx a) (arena.core.zero_level st) st lst zeroLevel := by
  intro o hrun
  rw [arena.core.zero_level, arena.pins.pin_zero_level] at hrun
  rw [zeroLevel]
  obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hbr := pos_pins_ready_run₀ hrel hb
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
    refine ⟨_, lst, ?_, rfl, hrel, hinv⟩
    rw [hrun2, if_pos (by rw [← hbr, hbt]), hrel.pins.zeroLevel]
  case isFalse hbf =>
    obtain ⟨sl, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨cps, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.monad.fail] at hrun
    have h2 := Result.ok_injective hrun
    subst h2
    refine AErrSim.internal (s := "arena: reserved-name pins not interned") ?_
    rw [hrun2, if_neg (by simp only [← hbr]; simpa using hbf)]

attribute [local lockstep] pos_zero_level_ls
attribute [local lockstep_inline] arena.inductives.positivity.sort_zero

/-! ## The name-list scans -/

/-- `names_contain` ⊑ `List.contains` from the cursor on. -/
theorem names_contain_abs {ns : alloc.vec.Vec arena.handle.NIdx}
    {n : arena.handle.NIdx} :
    ∀ (i : Std.Usize) (o : Bool), arena.inductives.positivity.names_contain ns n i = ok o →
      o = (absNIdxLFrom ns i).contains (absNIdx n) := by
  have key : ∀ (i : Std.Usize) (o : Bool),
      arena.inductives.positivity.names_contain ns n i = ok o →
      o = (ns.val.drop i.val).any fun m => absNIdx m == absNIdx n := by
    refine vec_cursor_any ns _ (fun i => arena.inductives.positivity.names_contain ns n i) ?_ ?_
    · intro i o hn h
      rw [arena.inductives.positivity.names_contain.eq_def] at h
      rw [if_pos (show i ≥ alloc.vec.Vec.len ns by scalar_tac), Result.ok.injEq] at h
      rw [h]
    · intro i x o hx h
      have hlt : i.val < ns.val.length := (List.getElem?_eq_some_iff.mp hx).1
      rw [arena.inductives.positivity.names_contain.eq_def] at h
      rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ns by scalar_tac)] at h
      obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hnx : n1 = x := by
        have h1 := vec_index_some hn1; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
      subst hnx
      have hbv : b = (absNIdx n1 == absNIdx n) := nidx_eq2_abs hb
      cases hbb : b
      · rw [hbb] at h hbv
        rw [if_neg (by simp)] at h
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        exact Or.inr ⟨hbv.symm, i2, absSz_add_one hi2, h⟩
      · rw [hbb] at h hbv
        rw [if_pos (by simp), Result.ok.injEq] at h
        exact Or.inl ⟨hbv.symm, h.symm⟩
  intro i o h
  rw [key i o h, absNIdxLFrom]
  have hcomm : (fun m => absNIdx m == absNIdx n) = (fun x => absNIdx n == absNIdx x) := by
    funext m
    by_cases hm : absNIdx m = absNIdx n
    · simp [hm]
    · have hm' : ¬ absNIdx n = absNIdx m := fun hc => hm hc.symm
      simp [hm, hm']
  rw [hcomm]
  simp only [List.contains_eq_any_beq, List.any_map, Function.comp_def]

@[lockstep] theorem names_contain_twin (ns : alloc.vec.Vec arena.handle.NIdx)
    (n : arena.handle.NIdx) :
    LSP (arena.inductives.positivity.names_contain ns n 0#usize)
      (fun o => TwinEq ((absNIdxL ns).contains (absNIdx n)) o) := by
  intro o h
  rw [names_contain_abs _ o h, absNIdxLFrom_zero]; rfl

/-- `names_find_idx` ⊑ `List.findIdx?` from the cursor on (offset by the
cursor). -/
theorem names_find_idx_abs {ns : alloc.vec.Vec arena.handle.NIdx}
    {n : arena.handle.NIdx} :
    ∀ (i : Std.Usize) (o : Option Std.U64),
      arena.inductives.positivity.names_find_idx ns n i = ok o →
      o.map absU = ((absNIdxLFrom ns i).findIdx? (· == absNIdx n)).map (· + i.val) := by
  intro i
  refine cursor_induction (fun i : Std.Usize => i.val) ns.val.length
    (fun i (_ : Unit) => ∀ o, arena.inductives.positivity.names_find_idx ns n i = ok o →
      o.map absU = ((absNIdxLFrom ns i).findIdx? (· == absNIdx n)).map (· + i.val))
    ?_ ?_ i ()
  · intro i _ hn o h
    rw [arena.inductives.positivity.names_find_idx.eq_def] at h
    rw [if_pos (show i ≥ alloc.vec.Vec.len ns by scalar_tac), Result.ok.injEq] at h
    subst h
    simp [absNIdxLFrom, List.drop_eq_nil_of_le hn]
  · intro i _ hi ih o h
    rw [arena.inductives.positivity.names_find_idx.eq_def] at h
    rw [if_neg (show ¬ i ≥ alloc.vec.Vec.len ns by scalar_tac)] at h
    obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hx := vec_index_some hn1
    obtain ⟨hb', hxv⟩ := List.getElem?_eq_some_iff.mp hx
    have hbv : b = (absNIdx n1 == absNIdx n) := nidx_eq2_abs hb
    have hdrop : absNIdxLFrom ns i = absNIdx n1 :: (ns.val.drop (i.val + 1)).map absNIdx := by
      rw [absNIdxLFrom, List.drop_eq_getElem_cons hi, hxv, List.map_cons]
    rw [hdrop, List.findIdx?_cons]
    cases hbb : b
    · rw [hbb] at h hbv
      rw [if_neg (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := absSz_add_one hi2
      rw [ih i2 () hi2v o h, absNIdxLFrom, hi2v, ← hbv]
      simp only [Bool.false_eq_true, ↓reduceIte, Option.map_map]
      congr 1
      funext k; simp; omega
    · rw [hbb] at h hbv
      rw [if_pos (by simp)] at h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      simp only [lift, Result.ok.injEq] at hi2 h
      subst hi2 h
      simp only [← hbv, ↓reduceIte, Option.map_some, Nat.zero_add, absU]
      rw [Std.UScalar.cast_val_eq]
      congr 1
      refine Nat.mod_eq_of_lt ?_
      have h1 : i.val ≤ Std.Usize.max := by scalar_tac
      have hmax : Std.Usize.max = 2 ^ System.Platform.numBits - 1 := by
        simp only [Std.Usize.max, Std.Usize.numBits, Std.UScalarTy.Usize_numBits_eq]
      have h64 : 2 ^ System.Platform.numBits ≤ 2 ^ 64 := by
        rcases System.Platform.numBits_eq with h | h <;> rw [h]; decide
      have : Std.UScalarTy.U64.numBits = 64 := rfl
      rw [this]
      have hpos : 0 < 2 ^ System.Platform.numBits := Nat.two_pow_pos _
      omega

@[lockstep] theorem names_find_idx_twin (ns : alloc.vec.Vec arena.handle.NIdx)
    (n : arena.handle.NIdx) :
    LSP (arena.inductives.positivity.names_find_idx ns n 0#usize)
      (fun o => TwinEq ((absNIdxL ns).findIdx? (· == absNIdx n)) (o.map absU)) := by
  intro o h
  rw [TwinEq, names_find_idx_abs _ o h, absNIdxLFrom_zero]
  simp

/-! ## The `bool` memo probe -/

theorem memo_bool_probe_refines {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} {k : arena.handle.EIdx} {o}
    (hm : ExprOps.LMemoRel rm lm)
    (hrun : arena.inductives.positivity.memo_bool_probe rm k = ok o) :
    o = lm[absEIdx k]? := by
  rw [arena.inductives.positivity.memo_bool_probe] at hrun
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

@[lockstep] theorem memo_bool_probe_twin
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool}
    {k : arena.handle.EIdx}
    (hm : ExprOps.LMemoRel rm lm) :
    LSP (arena.inductives.positivity.memo_bool_probe rm k)
      (fun o => TwinEq (lm[absEIdx k]?) o) :=
  fun _o h => (memo_bool_probe_refines hm h).symm

/-! ## `mentions_any_go` / `mentions_any_const` -/

theorem mentions_any_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (names : alloc.vec.Vec arena.handle.NIdx)
      (rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
      (lm : Std.HashMap EIdx Bool) (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → ExprOps.LMemoRel rm lm →
      LSR pers (fun a b => ∃ m', ExprOps.LMemoRel a.2 m' ∧ b = (a.1, m'))
        (arena.inductives.positivity.mentions_any_go pers st names rm fuel h) st lst
        (mentionsAnyGo (absNIdxL names) lm n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst names rm lm fuel h hn hrel hinv hm
    apply LSR.of_LS
    rw [arena.inductives.positivity.mentions_any_go, mentionsAnyGo]
    lockstep
  | succ m ih =>
    intro pers st lst names rm lm fuel h hn hrel hinv hm
    apply LSR.of_LS
    rw [arena.inductives.positivity.mentions_any_go, mentionsAnyGo]
    unfold arena.inductives.positivity.mentions_any_node
    lockstep

@[lockstep] theorem mentions_any_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool} {lm : Std.HashMap EIdx Bool}
    (hm : ExprOps.LMemoRel rm lm) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => ∃ m', ExprOps.LMemoRel a.2 m' ∧ b = (a.1, m'))
      (arena.inductives.positivity.mentions_any_go pers st names rm fuel h) st lst
      (mentionsAnyGo (absNIdxL names) lm (absU fuel) (absEIdx h)) :=
  mentions_any_go_aux _ names rm lm fuel h rfl hrel hinv hm

/-- `mentions_any_const` ⊑ `mentionsAnyConst` — one memoised walk from the
empty memo. -/
@[lockstep] theorem mentions_any_const_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (e : arena.handle.EIdx) :
    LSR pers (fun a b => b = a)
      (arena.inductives.positivity.mentions_any_const pers st names e) st lst
      (mentionsAnyConst (absNIdxL names) (absEIdx e)) := by
  apply LSR.of_LS
  rw [arena.inductives.positivity.mentions_any_const, mentionsAnyConst]
  lockstep

/-- `member_idx_at` ⊑ `memberIdxAt?`. -/
@[lockstep] theorem member_idx_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (lvls : arena.handle.LsIdx) (e : arena.handle.EIdx) :
    LSR pers (fun a b => b = a.map absU)
      (arena.inductives.positivity.member_idx_at pers st names lvls e) st lst
      (memberIdxAt? (absNIdxL names) (absLsIdx lvls) (absEIdx e)) := by
  apply LSR.of_LS
  rw [arena.inductives.positivity.member_idx_at, memberIdxAt?]
  lockstep

/-! ## `close_telescope` -/

/-- `close_telescope` ⊑ `closeTelescope`, the telescope from the cursor on. -/
@[lockstep] theorem close_telescope_ls {pers}
    {bs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)}
    {body : arena.handle.EIdx} (hte : TeleWF bs) :
    ∀ (k : Std.Usize) (i : Std.U64) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a)
        (arena.inductives.positivity.close_telescope pers st bs k i body) lst
        (closeTelescope (absBinderLFrom bs k) (absU i) (absEIdx body)) := by
  intro k i st lst hrel hinv
  refine ls_cursor_acc bs (fun p => (absEIdx p.1, ConRon.Refine.absBinderMeta p.2))
    (fun (w : Std.U64) l => closeTelescope l (absU w) (absEIdx body))
    (fun st k w => arena.inductives.positivity.close_telescope pers st bs k w body)
    ?_ ?_ k st lst i hrel hinv
  · intro st lst k w hn hrel hinv
    rw [arena.inductives.positivity.close_telescope.eq_def,
      if_pos (show k ≥ alloc.vec.Vec.len bs by scalar_tac), closeTelescope]
    lockstep
  · intro st lst k w hk hrel hinv ih
    have ih' : ∀ st' lst' (j : Std.Usize) (w' : Std.U64), j.val = k.val + 1 →
        AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun a b => b = absEIdx a)
          (arena.inductives.positivity.close_telescope pers st' bs j w' body) lst'
          (closeTelescope (absBinderLFrom bs j) (absU w') (absEIdx body)) := ih
    clear ih
    have hpw := TeleWF.get hte k.val hk
    rw [arena.inductives.positivity.close_telescope.eq_def,
      if_neg (show ¬ k ≥ alloc.vec.Vec.len bs by scalar_tac), closeTelescope]
    lockstep

/-! ## `nest_occ_go` / `nest_occ` -/

theorem nest_occ_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (names : alloc.vec.Vec arena.handle.NIdx) (lo hi : Std.U64)
      (rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
      (lm : Std.HashMap EIdx Bool) (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → ExprOps.LMemoRel rm lm →
      LSR pers (fun a b => ∃ m', ExprOps.LMemoRel a.2 m' ∧ b = (a.1, m'))
        (arena.inductives.positivity.nest_occ_go pers st names lo hi rm fuel h) st lst
        (nestOccGo (absNIdxL names) (absU lo) (absU hi) lm n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst names lo hi rm lm fuel h hn hrel hinv hm
    apply LSR.of_LS
    rw [arena.inductives.positivity.nest_occ_go, nestOccGo]
    lockstep
  | succ m ih =>
    intro pers st lst names lo hi rm lm fuel h hn hrel hinv hm
    apply LSR.of_LS
    rw [arena.inductives.positivity.nest_occ_go, nestOccGo]
    unfold arena.inductives.positivity.nest_occ_node
    lockstep

@[lockstep] theorem nest_occ_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx) (lo hi : Std.U64)
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool} {lm : Std.HashMap EIdx Bool}
    (hm : ExprOps.LMemoRel rm lm) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => ∃ m', ExprOps.LMemoRel a.2 m' ∧ b = (a.1, m'))
      (arena.inductives.positivity.nest_occ_go pers st names lo hi rm fuel h) st lst
      (nestOccGo (absNIdxL names) (absU lo) (absU hi) lm (absU fuel) (absEIdx h)) :=
  nest_occ_go_aux _ names lo hi rm lm fuel h rfl hrel hinv hm

@[lockstep] theorem nest_occ_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx) (lo hi : Std.U64)
    (e : arena.handle.EIdx) :
    LSR pers (fun a b => b = a)
      (arena.inductives.positivity.nest_occ pers st names lo hi e) st lst
      (nestOcc (absNIdxL names) (absU lo) (absU hi) (absEIdx e)) := by
  apply LSR.of_LS
  rw [arena.inductives.positivity.nest_occ, nestOcc]
  lockstep

/-- `nest_occ_any` ⊑ `List.anyM (nestOcc …)` from the cursor on. -/
@[lockstep] theorem nest_occ_any_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx) (lo hi : Std.U64)
    (xs : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) :
    LSR pers (fun a b => b = a)
      (arena.inductives.positivity.nest_occ_any pers st names lo hi xs i) st lst
      ((absEIdxLFrom xs i).anyM fun x => nestOcc (absNIdxL names) (absU lo) (absU hi) x) := by
  refine cursor_induction (fun i : Std.Usize => i.val) xs.val.length
    (fun i (_ : Unit) => ∀ lst, AStateRel₀ pers st lst → LSR pers (fun a b => b = a)
      (arena.inductives.positivity.nest_occ_any pers st names lo hi xs i) st lst
      ((absEIdxLFrom xs i).anyM fun x => nestOcc (absNIdxL names) (absU lo) (absU hi) x))
    ?_ ?_ i () lst hrel
  · intro i _ hn lst hrel
    apply LSR.of_LS
    rw [arena.inductives.positivity.nest_occ_any.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), absEIdxLFrom,
      List.drop_eq_nil_of_le hn, List.map_nil, List.anyM]
    lockstep
  · intro i _ hlt ih lst hrel
    have ih' : ∀ j : Std.Usize, j.val = i.val + 1 → ∀ lst, AStateRel₀ pers st lst →
        LSR pers (fun a b => b = a)
        (arena.inductives.positivity.nest_occ_any pers st names lo hi xs j) st lst
        ((absEIdxLFrom xs j).anyM fun x => nestOcc (absNIdxL names) (absU lo) (absU hi) x) :=
      fun j hj => ih j () hj
    clear ih
    apply LSR.of_LS
    rw [arena.inductives.positivity.nest_occ_any.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac), absEIdxLFrom,
      List.drop_eq_getElem_cons hlt, List.map_cons, List.anyM]
    lockstep

/-- `nest_occ_any_binder` ⊑ `List.anyM (nestOcc … ·.1)` over a telescope from
the cursor on. -/
@[lockstep] theorem nest_occ_any_binder_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx) (lo hi : Std.U64)
    (bs : alloc.vec.Vec (arena.handle.EIdx × kernel.expr.BinderMeta)) (i : Std.Usize) :
    LSR pers (fun a b => b = a)
      (arena.inductives.positivity.nest_occ_any_binder pers st names lo hi bs i) st lst
      ((absBinderLFrom bs i).anyM fun b => nestOcc (absNIdxL names) (absU lo) (absU hi) b.1) := by
  suffices H : ∀ (i : Std.Usize) (u : Unit) lst, AStateRel₀ pers st lst →
      LSR pers (fun a b => b = a)
      (arena.inductives.positivity.nest_occ_any_binder pers st names lo hi bs i) st lst
      ((absBinderLFrom bs i).anyM fun b => nestOcc (absNIdxL names) (absU lo) (absU hi) b.1) from
    H i () lst hrel
  refine cursor_induction (fun i : Std.Usize => i.val) bs.val.length _ ?_ ?_
  · intro i _ hn lst hrel
    apply LSR.of_LS
    rw [arena.inductives.positivity.nest_occ_any_binder.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len bs by scalar_tac), absBinderLFrom,
      List.drop_eq_nil_of_le hn, List.map_nil, List.anyM]
    lockstep
  · intro i _ hlt ih lst hrel
    have ih' : ∀ j : Std.Usize, j.val = i.val + 1 → ∀ lst, AStateRel₀ pers st lst →
        LSR pers (fun a b => b = a)
        (arena.inductives.positivity.nest_occ_any_binder pers st names lo hi bs j) st lst
        ((absBinderLFrom bs j).anyM fun b => nestOcc (absNIdxL names) (absU lo) (absU hi) b.1) :=
      fun j hj => ih j () hj
    clear ih
    apply LSR.of_LS
    rw [arena.inductives.positivity.nest_occ_any_binder.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len bs by scalar_tac), absBinderLFrom,
      List.drop_eq_getElem_cons hlt, List.map_cons, List.anyM]
    lockstep

/-! ## `inst_pis_with` -/

/-- `inst_pis_with` ⊑ `instPisWith`, the arguments from the cursor on. -/
@[lockstep] theorem inst_pis_with_ls {pers}
    {args : alloc.vec.Vec arena.handle.EIdx} :
    ∀ (i : Std.Usize) (e : arena.handle.EIdx) st lst, AStateRel₀ pers st lst →
      AStateInv pers st →
      LS pers (fun a b => b = a.map absEIdx)
        (arena.inductives.positivity.inst_pis_with pers st args i e) lst
        (instPisWith (absEIdxLFrom args i) (absEIdx e)) := by
  intro i e st lst hrel hinv
  refine ls_cursor_acc args absEIdx
    (fun (w : arena.handle.EIdx) l => instPisWith l (absEIdx w))
    (fun st k w => arena.inductives.positivity.inst_pis_with pers st args k w)
    ?_ ?_ i st lst e hrel hinv
  · intro st lst k w hn hrel hinv
    rw [arena.inductives.positivity.inst_pis_with.eq_def,
      if_pos (show k ≥ alloc.vec.Vec.len args by scalar_tac), instPisWith]
    lockstep
  · intro st lst k w hk hrel hinv ih
    have ih' : ∀ st' lst' (j : Std.Usize) (w' : arena.handle.EIdx), j.val = k.val + 1 →
        AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun a b => b = a.map absEIdx)
          (arena.inductives.positivity.inst_pis_with pers st' args j w') lst'
          (instPisWith (absEIdxLFrom args j) (absEIdx w')) := ih
    clear ih
    rw [arena.inductives.positivity.inst_pis_with.eq_def,
      if_neg (show ¬ k ≥ alloc.vec.Vec.len args by scalar_tac), instPisWith]
    lockstep

/-! ## The `u64` and `EIdx` memos -/

/-- `depth_go`'s memo: handle to depth. -/
def NMemoRel (rm : ron.hashmap2.HashMap2 arena.handle.EIdx Std.U64)
    (lm : Std.HashMap EIdx Nat) : Prop :=
  ConRon.Refine.HashMap2.RelOn (fun _ => True) rm lm absEIdx absU ∧
    ConRon.Refine.HashMap2.Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable rm

/-- `replace_fvars_go`'s and `replace_apps_go`'s memo: handle to handle. -/
def PEMemoRel (rm : ron.hashmap2.HashMap2 arena.handle.EIdx arena.handle.EIdx)
    (lm : Std.HashMap EIdx EIdx) : Prop :=
  ConRon.Refine.HashMap2.RelOn (fun _ => True) rm lm absEIdx absEIdx ∧
    ConRon.Refine.HashMap2.Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable rm

@[lockstep] theorem depth_probe_twin
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Std.U64}
    {lm : Std.HashMap EIdx Nat} {k : arena.handle.EIdx} (hm : NMemoRel rm lm) :
    LSP (arena.inductives.positivity.depth_probe rm k)
      (fun o => TwinEq (lm[absEIdx k]?) (o.map absU)) := by
  intro o hrun
  rw [arena.inductives.positivity.depth_probe] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hg := ConRon.Refine.HashMap2.Rel_get_wf eidx_eq2 hm.2
    ConRon.Refine.HashMap2.KeysOk_true hm.1 trivial hr
  rw [TwinEq, ← hg]
  cases r with
  | none => cases Result.ok_injective hrun; rfl
  | some v => cases Result.ok_injective hrun; rfl

@[lockstep] theorem memo_e_probe_twin
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx arena.handle.EIdx}
    {lm : Std.HashMap EIdx EIdx} {k : arena.handle.EIdx} (hm : PEMemoRel rm lm) :
    LSP (arena.inductives.positivity.memo_e_probe rm k)
      (fun o => TwinEq (lm[absEIdx k]?) (o.map absEIdx)) := by
  intro o hrun
  rw [arena.inductives.positivity.memo_e_probe] at hrun
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hg := ConRon.Refine.HashMap2.Rel_get_wf eidx_eq2 hm.2
    ConRon.Refine.HashMap2.KeysOk_true hm.1 trivial hr
  rw [TwinEq, ← hg]
  cases r with
  | none => cases Result.ok_injective hrun; rfl
  | some v =>
    obtain ⟨e, he, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    cases Result.ok_injective hrun
    rw [dupId_eidx _ _ he]

@[lockstep] theorem hashmap2_insert_eidx_u64_spec
    {memo : ron.hashmap2.HashMap2 arena.handle.EIdx Std.U64}
    {lm : Std.HashMap EIdx Nat} (hm : NMemoRel memo lm) (k : arena.handle.EIdx)
    (r : Std.U64) :
    LSP (ron.hashmap2.HashMap2.insert arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable
        arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2 memo k r)
      (fun p => NMemoRel p.2 (lm.insert (absEIdx k) (absU r))) := by
  intro ⟨old, m'⟩ h
  have hinj : ∀ a b : arena.handle.EIdx, True → True → absEIdx a = absEIdx b → a = b :=
    fun a b _ _ hab => absEIdx_inj hab
  obtain ⟨hrel', -⟩ := ConRon.Refine.HashMap2.Rel_insert_wf eidx_eq2 hinj hm.2
    ConRon.Refine.HashMap2.KeysOk_true hm.1 trivial h
  exact ⟨hrel', (ConRon.Refine.HashMap2.insert_refines_wf eidx_eq2 hm.2
    ConRon.Refine.HashMap2.KeysOk_true trivial h).1⟩

@[lockstep] theorem hashmap2_insert_eidx_eidx_spec
    {memo : ron.hashmap2.HashMap2 arena.handle.EIdx arena.handle.EIdx}
    {lm : Std.HashMap EIdx EIdx} (hm : PEMemoRel memo lm) (k : arena.handle.EIdx)
    (r : arena.handle.EIdx) :
    LSP (ron.hashmap2.HashMap2.insert arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable
        arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2 memo k r)
      (fun p => PEMemoRel p.2 (lm.insert (absEIdx k) (absEIdx r))) := by
  intro ⟨old, m'⟩ h
  have hinj : ∀ a b : arena.handle.EIdx, True → True → absEIdx a = absEIdx b → a = b :=
    fun a b _ _ hab => absEIdx_inj hab
  obtain ⟨hrel', -⟩ := ConRon.Refine.HashMap2.Rel_insert_wf eidx_eq2 hinj hm.2
    ConRon.Refine.HashMap2.KeysOk_true hm.1 trivial h
  exact ⟨hrel', (ConRon.Refine.HashMap2.insert_refines_wf eidx_eq2 hm.2
    ConRon.Refine.HashMap2.KeysOk_true trivial h).1⟩

@[lockstep] theorem hashmap2_new_eidx_u64_spec :
    LSP (ron.hashmap2.HashMap2.new arena.handle.EIdx Std.U64) (fun m => NMemoRel m ∅) := by
  intro m h
  obtain ⟨hnInv, -, hnNone⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable) h
  exact ⟨ConRon.Refine.HashMap2.RelOn_empty hnNone, hnInv⟩

@[lockstep] theorem hashmap2_new_eidx_eidx_spec :
    LSP (ron.hashmap2.HashMap2.new arena.handle.EIdx arena.handle.EIdx)
      (fun m => PEMemoRel m ∅) := by
  intro m h
  obtain ⟨hnInv, -, hnNone⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable) h
  exact ⟨ConRon.Refine.HashMap2.RelOn_empty hnNone, hnInv⟩

/-! ## `depth_go` / `expr_depth` / `whnf_walk_fuel` -/

@[lockstep] theorem pos_max_u64_spec (a b : Std.U64) :
    LSP (arena.inductives.positivity.max_u64 a b) (fun r => r.val = max a.val b.val) := by
  intro r h
  rw [arena.inductives.positivity.max_u64] at h
  split at h <;> (have := Result.ok_injective h; subst this) <;> scalar_tac

theorem depth_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (rm : ron.hashmap2.HashMap2 arena.handle.EIdx Std.U64)
      (lm : Std.HashMap EIdx Nat) (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → NMemoRel rm lm →
      LSR pers (fun a b => ∃ m', NMemoRel a.2 m' ∧ b = (absU a.1, m'))
        (arena.inductives.positivity.depth_go pers st rm fuel h) st lst
        (depthGo lm n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm fuel h hn hrel hinv hm
    apply LSR.of_LS
    rw [arena.inductives.positivity.depth_go, depthGo]
    lockstep
  | succ m ih =>
    intro pers st lst rm lm fuel h hn hrel hinv hm
    apply LSR.of_LS
    rw [arena.inductives.positivity.depth_go, depthGo]
    unfold arena.inductives.positivity.depth_node
    lockstep

@[lockstep] theorem depth_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Std.U64} {lm : Std.HashMap EIdx Nat}
    (hm : NMemoRel rm lm) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LSR pers (fun a b => ∃ m', NMemoRel a.2 m' ∧ b = (absU a.1, m'))
      (arena.inductives.positivity.depth_go pers st rm fuel h) st lst
      (depthGo lm (absU fuel) (absEIdx h)) :=
  depth_go_aux _ rm lm fuel h rfl hrel hinv hm

theorem fuel_slack_val : (arena.inductives.positivity.FUEL_SLACK).val = fuelSlack := by
  rw [arena.inductives.positivity.FUEL_SLACK, fuelSlack]; rfl

attribute [local lockstep_simp] fuel_slack_val

@[lockstep] theorem expr_depth_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (e : arena.handle.EIdx) :
    LSR pers (fun a b => b = absU a)
      (arena.inductives.positivity.expr_depth pers st e) st lst (depth (absEIdx e)) := by
  apply LSR.of_LS
  rw [arena.inductives.positivity.expr_depth, depth]
  lockstep

@[lockstep] theorem whnf_walk_fuel_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (e : arena.handle.EIdx) :
    LSR pers (fun a b => b = absU a)
      (arena.inductives.positivity.whnf_walk_fuel pers st e) st lst
      (whnfWalkFuel (absEIdx e)) := by
  apply LSR.of_LS
  rw [arena.inductives.positivity.whnf_walk_fuel, whnfWalkFuel]
  lockstep

/-! ## The record copies (identities) -/

/-- The tier's copy loops, once: `F` pushes a copy of `xs[i]` (a `dup` that
is the identity) and recurses. -/
theorem vec_copy_id {α : Type} (xs : alloc.vec.Vec α)
    (F : Std.Usize → alloc.vec.Vec α → Result (alloc.vec.Vec α))
    (hstop : ∀ (i : Std.Usize) (out o : alloc.vec.Vec α),
      xs.val.length ≤ i.val → F i out = ok o → o.val = out.val)
    (hstep : ∀ (i : Std.Usize) (x : α) (out o : alloc.vec.Vec α),
      xs.val[i.val]? = some x → F i out = ok o →
      ∃ (j : Std.Usize) (out1 : alloc.vec.Vec α),
        j.val = i.val + 1 ∧ out1.val = out.val ++ [x] ∧ F j out1 = ok o) :
    ∀ (o : alloc.vec.Vec α), F 0#usize (alloc.vec.Vec.new α) = ok o → o = xs := by
  intro o h
  have := vec_cursor_copy xs id id F hstop
    (fun i x out o hx h => by
      obtain ⟨j, out1, hj, ho, hF⟩ := hstep i x out o hx h
      exact ⟨j, x, out1, hj, ho, rfl, hF⟩) 0#usize _ o h
  apply alloc.vec.Vec.ext
  simpa [alloc.vec.Vec.new] using this

@[lockstep] theorem nest_key_dup_spec (k : arena.inductives.positivity.NestKey) :
    LSP (arena.inductives.positivity.nest_key_dup k) (fun o => o = k) := by
  intro o h
  rw [arena.inductives.positivity.nest_key_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [dupId_nidx _ _ hn, dupId_lsidx _ _ hl, alloc.vec.Vec.ext _ _ (eidx_vec_dup_val hv)]

@[lockstep] theorem nest_hole_dup_spec (h : arena.inductives.positivity.NestHole) :
    LSP (arena.inductives.positivity.nest_hole_dup h) (fun o => o = h) := by
  intro o hh
  rw [arena.inductives.positivity.nest_hole_dup] at hh
  obtain ⟨k, hk, hh⟩ := ConRon.Refine.bind_eq_ok_iff.mp hh
  cases Result.ok_injective hh
  rw [nest_key_dup_spec _ _ hk]

@[lockstep] theorem nest_ctor_nf_dup_spec (e : arena.inductives.positivity.NestCtorNf) :
    LSP (arena.inductives.positivity.nest_ctor_nf_dup e) (fun o => o = e) := by
  intro o h
  rw [arena.inductives.positivity.nest_ctor_nf_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [dupId_nidx _ _ hn, dupId_lsidx _ _ hl, alloc.vec.Vec.ext _ _ (eidx_vec_dup_val hv),
    dupId_eidx _ _ ht]

@[lockstep] theorem nest_field_kind_dup_spec (k : arena.inductives.positivity.NestFieldKind) :
    LSP (arena.inductives.positivity.nest_field_kind_dup k) (fun o => o = k) := by
  intro o h
  cases k <;> simp only [arena.inductives.positivity.nest_field_kind_dup,
    Result.ok.injEq] at h <;> exact h.symm

/-- A copy loop whose element copy is the identity. -/
private theorem copy_loop_id {α : Type} (dup : α → Result α) (hd : ∀ x y, dup x = ok y → y = x)
    (xs : alloc.vec.Vec α) (F : Std.Usize → alloc.vec.Vec α → Result (alloc.vec.Vec α))
    (heq : ∀ i out, F i out = (if i ≥ alloc.vec.Vec.len xs then ok out else do
      let x ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) xs i
      let y ← dup x
      let out1 ← alloc.vec.Vec.push out y
      let i2 ← i + 1#usize
      F i2 out1)) :
    ∀ (o : alloc.vec.Vec α), F 0#usize (alloc.vec.Vec.new α) = ok o → o = xs := by
  refine vec_copy_id xs F ?_ ?_
  · intro i out o hn h
    rw [heq, if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), Result.ok.injEq] at h
    rw [h]
  · intro i x out o hx h
    rw [heq, if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by
      have := (List.getElem?_eq_some_iff.mp hx).1; scalar_tac)] at h
    obtain ⟨q, hq, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hqx : q = x := by
      have h1 := vec_index_some hq; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
    subst hqx
    obtain ⟨y, hy, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rw [hd _ _ hy] at hout1
    exact ⟨i2, out1, absSz_add_one hi2, ConRon.Refine.vec_push_val hout1, h⟩

@[lockstep] theorem nest_holes_dup_spec (hs : alloc.vec.Vec arena.inductives.positivity.NestHole) :
    LSP (arena.inductives.positivity.nest_holes_dup hs 0#usize
      (alloc.vec.Vec.new arena.inductives.positivity.NestHole)) (fun o => o = hs) :=
  copy_loop_id _ (fun x y h => nest_hole_dup_spec x y h) hs
    (arena.inductives.positivity.nest_holes_dup hs)
    (fun i out => by rw [arena.inductives.positivity.nest_holes_dup.eq_def])

@[lockstep] theorem nest_keys_dup_spec (ks : alloc.vec.Vec arena.inductives.positivity.NestKey) :
    LSP (arena.inductives.positivity.nest_keys_dup ks 0#usize
      (alloc.vec.Vec.new arena.inductives.positivity.NestKey)) (fun o => o = ks) :=
  copy_loop_id _ (fun x y h => nest_key_dup_spec x y h) ks
    (arena.inductives.positivity.nest_keys_dup ks)
    (fun i out => by rw [arena.inductives.positivity.nest_keys_dup.eq_def])

@[lockstep] theorem nest_ctor_nfs_dup_spec
    (es : alloc.vec.Vec arena.inductives.positivity.NestCtorNf) :
    LSP (arena.inductives.positivity.nest_ctor_nfs_dup es 0#usize
      (alloc.vec.Vec.new arena.inductives.positivity.NestCtorNf)) (fun o => o = es) :=
  copy_loop_id _ (fun x y h => nest_ctor_nf_dup_spec x y h) es
    (arena.inductives.positivity.nest_ctor_nfs_dup es)
    (fun i out => by rw [arena.inductives.positivity.nest_ctor_nfs_dup.eq_def])

@[lockstep] theorem u64_vec_dup_spec (xs : alloc.vec.Vec Std.U64) :
    LSP (arena.inductives.positivity.u64_vec_dup xs 0#usize (alloc.vec.Vec.new Std.U64))
      (fun o => o = xs) :=
  copy_loop_id (fun x => ok x) (fun x y h => (Result.ok_injective h).symm) xs
    (arena.inductives.positivity.u64_vec_dup xs)
    (fun i out => by rw [arena.inductives.positivity.u64_vec_dup.eq_def]; simp only [bind_tc_ok])

@[lockstep] theorem nest_ctx_dup_spec (c : arena.inductives.positivity.NestCtx) :
    LSP (arena.inductives.positivity.nest_ctx_dup c) (fun o => o = c) := by
  intro o h
  rw [arena.inductives.positivity.nest_ctx_dup] at h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v1, hv1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v2, hv2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v3, hv3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨li, hli, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [alloc.vec.Vec.ext _ _ (nidx_vec_dup_val hv), alloc.vec.Vec.ext _ _ (nidx_vec_dup_val hv1),
    u64_vec_dup_spec _ _ hv2, alloc.vec.Vec.ext _ _ (eidx_vec_dup_val hv3), dupId_lidx _ _ hl,
    dupId_lsidx _ _ hli]

@[lockstep] theorem nest_state_empty_spec :
    LSP arena.inductives.positivity.nest_state_empty
      (fun o => TwinEq ({} : NestState) (absNestState o)) := by
  intro o h
  rw [arena.inductives.positivity.nest_state_empty] at h
  cases Result.ok_injective h
  simp [TwinEq, absNestState, alloc.vec.Vec.new]

/-! ## The context's fields and the pure readers -/

@[lockstep_simp] theorem absNestCtx_names (c : arena.inductives.positivity.NestCtx) :
    (absNestCtx c).names = absNIdxL c.names := rfl
@[lockstep_simp] theorem absNestCtx_lps (c : arena.inductives.positivity.NestCtx) :
    (absNestCtx c).lps = absNIdxL c.lps := rfl
@[lockstep_simp] theorem absNestCtx_nP (c : arena.inductives.positivity.NestCtx) :
    (absNestCtx c).nP = absU c.n_p := rfl
@[lockstep_simp] theorem absNestCtx_nIdxs (c : arena.inductives.positivity.NestCtx) :
    (absNestCtx c).nIdxs = c.n_idxs.val.map absU := rfl
@[lockstep_simp] theorem absNestCtx_params (c : arena.inductives.positivity.NestCtx) :
    (absNestCtx c).params = absEIdxL c.params := rfl
@[lockstep_simp] theorem absNestCtx_sort (c : arena.inductives.positivity.NestCtx) :
    (absNestCtx c).sort = absLIdx c.sort := rfl
@[lockstep_simp] theorem absNestCtx_lvls (c : arena.inductives.positivity.NestCtx) :
    (absNestCtx c).lvls = absLsIdx c.lvls := rfl

@[lockstep_simp] theorem absNestCtx_hiAt (c : arena.inductives.positivity.NestCtx) (n : Nat) :
    (absNestCtx c).hiAt n = absU c.n_p + c.names.val.length + n := by
  simp [NestCtx.hiAt, absNestCtx, absNIdxL]

@[lockstep] theorem hi_at_spec (ctx : arena.inductives.positivity.NestCtx) (nf : Std.U64) :
    LSP (arena.inductives.positivity.hi_at ctx nf)
      (fun r => r.val = ctx.n_p.val + ctx.names.val.length + nf.val) := by
  intro r h
  rw [arena.inductives.positivity.hi_at] at h
  obtain ⟨a, ha, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have ha' := lift_cast_u64_of_usize _ a ha
  have hb' := ConRon.Refine.Nat.uadd_val hb
  have h' := ConRon.Refine.Nat.uadd_val h
  simp only [alloc.vec.Vec.len] at ha'
  scalar_tac

@[lockstep] theorem eidx_get_twin (xs : alloc.vec.Vec arena.handle.EIdx) (i : Std.U64) :
    LSP (arena.inductives.positivity.eidx_get xs i)
      (fun o => TwinEq ((absEIdxL xs)[absU i]?) (o.map absEIdx)) := by
  intro o h
  rw [arena.inductives.positivity.eidx_get] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hn' := lift_cast_u64_of_usize _ n hn
  simp only [alloc.vec.Vec.len] at hn'
  split at h
  · obtain ⟨k, hk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    rcases lift_cast_usize_of_u64 _ k hk with hk' | hk'
    · have hx := vec_index_some he
      rw [dupId_eidx _ _ he1]
      simp only [TwinEq, absEIdxL, List.getElem?_map, absU, ← hk', hx, Option.map_some]
    · exfalso; scalar_tac
  · cases Result.ok_injective h
    simp only [TwinEq, absEIdxL, Option.map_none]
    rw [List.getElem?_eq_none]
    simp only [List.length_map, absU]; scalar_tac

@[lockstep] theorem nest_key_map_twin (ds holes : alloc.vec.Vec arena.handle.EIdx) (i : Std.U64) :
    LSP (arena.inductives.positivity.nest_key_map ds holes i)
      (fun o => TwinEq (nestKeyMap (absEIdxL ds) (absEIdxL holes) (absU i)) (o.map absEIdx)) := by
  intro o h
  rw [arena.inductives.positivity.nest_key_map] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hn' := lift_cast_u64_of_usize _ n hn
  simp only [alloc.vec.Vec.len] at hn'
  split at h
  · have := eidx_get_twin ds i o h
    simp only [TwinEq] at this ⊢
    rw [← this, nestKeyMap, if_pos (by simp [absEIdxL, absU]; scalar_tac)]
  · obtain ⟨j, hj, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have := eidx_get_twin holes j o h
    have hj' := ConRon.Refine.Nat.usub_val hj
    simp only [TwinEq] at this ⊢
    rw [← this, nestKeyMap, if_neg (by simp [absEIdxL, absU]; scalar_tac)]
    congr 1
    simp only [absEIdxL, absU, List.length_map]; scalar_tac

theorem root_hole_spec (ctx : arena.inductives.positivity.NestCtx) (j : Std.Usize) :
    LSP (arena.inductives.positivity.root_hole ctx j)
      (fun o => ∃ n, ctx.names.val[j.val]? = some n ∧
        o = { key := { cname := n, lvls := ctx.lvls, ds := ctx.params }, base := ctx.n_p }) := by
  intro o h
  rw [arena.inductives.positivity.root_hole] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  refine ⟨n, vec_index_some hn, ?_⟩
  rw [dupId_nidx _ _ hn1, dupId_lsidx _ _ hl, alloc.vec.Vec.ext _ _ (eidx_vec_dup_val hv)]

@[lockstep] theorem nest_hole_at_twin (ctx : arena.inductives.positivity.NestCtx)
    (prog : alloc.vec.Vec arena.inductives.positivity.NestHole) (i : Std.U64) :
    LSP (arena.inductives.positivity.nest_hole_at ctx prog i)
      (fun o => TwinEq (nestHoleAt (absNestCtx ctx) (prog.val.map absNestHole) (absU i))
        (o.map absNestHole)) := by
  intro o h
  rw [arena.inductives.positivity.nest_hole_at] at h
  simp only [TwinEq, nestHoleAt, NestCtx.rootHoles, absNestCtx_nP, absNestCtx_names,
    absNestCtx_lvls, absNestCtx_params]
  split at h
  · rename_i hle
    rw [if_pos (by simp [absU]; scalar_tac)]
    obtain ⟨j, hj, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨k, hk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hj' := ConRon.Refine.Nat.usub_val hj
    have hk' := lift_cast_u64_of_usize _ k hk
    simp only [alloc.vec.Vec.len] at hk'
    split at h
    · rename_i hlt
      obtain ⟨j2, hj2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨nh, hnh, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      cases Result.ok_injective h
      rcases lift_cast_usize_of_u64 _ j2 hj2 with hj2' | hj2'
      · obtain ⟨n, hn, rfl⟩ := root_hole_spec ctx j2 nh hnh
        rw [List.getElem?_append_left (by simp [absNIdxL, absU]; scalar_tac)]
        simp only [List.getElem?_map, absNIdxL]
        have : absU i - absU ctx.n_p = j2.val := by simp [absU] at hj' ⊢; omega
        rw [this, hn]
        rfl
      · exfalso; scalar_tac
    · rename_i hge
      obtain ⟨j3, hj3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨l, hl, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hj3' := ConRon.Refine.Nat.usub_val hj3
      have hl' := lift_cast_u64_of_usize _ l hl
      simp only [alloc.vec.Vec.len] at hl'
      rw [List.getElem?_append_right (by simp [absNIdxL, absU]; scalar_tac)]
      simp only [List.length_map, absNIdxL, List.getElem?_map]
      have : absU i - absU ctx.n_p - ctx.names.val.length = j3.val := by
        simp only [absU]; scalar_tac
      rw [this]
      split at h
      · obtain ⟨j5, hj5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨nh, hnh, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        obtain ⟨nh1, hnh1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        cases Result.ok_injective h
        rw [nest_hole_dup_spec _ _ hnh1]
        rcases lift_cast_usize_of_u64 _ j5 hj5 with hj5' | hj5'
        · rw [← hj5', vec_index_some hnh]
        · exfalso; scalar_tac
      · cases Result.ok_injective h
        rw [List.getElem?_eq_none (by scalar_tac)]
  · cases Result.ok_injective h
    rw [if_neg (by simp [absU]; scalar_tac)]
    rfl

/-! ## The read-back block: `fv_map_at`, `replace_fvars*`, `nest_hole_img` -/

@[lockstep_simp] theorem absNestHole_key (h : arena.inductives.positivity.NestHole) :
    (absNestHole h).key = absNestKey h.key := rfl
@[lockstep_simp] theorem absNestHole_base (h : arena.inductives.positivity.NestHole) :
    (absNestHole h).base = absU h.base := rfl
@[lockstep_simp] theorem absNestKey_cname (k : arena.inductives.positivity.NestKey) :
    (absNestKey k).cname = absNIdx k.cname := rfl
@[lockstep_simp] theorem absNestKey_lvls (k : arena.inductives.positivity.NestKey) :
    (absNestKey k).lvls = absLsIdx k.lvls := rfl
@[lockstep_simp] theorem absNestKey_ds (k : arena.inductives.positivity.NestKey) :
    (absNestKey k).ds = absEIdxL k.ds := rfl

/-- The twin's `getD` of a mapped list at an in-range index. -/
theorem map_getD_of_lt {α β : Type} [Inhabited β] (f : α → β) (l : List α) (k j : Nat)
    (hj : j < l.length) (hjk : j = k) : (l.map f).getD k default = f (l[j]'hj) := by
  subst hjk
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  rfl

@[lockstep_simp] theorem absFvMap_holeImg (m : arena.inductives.positivity.HoleImgMap) :
    absFvMap (.HoleImg m) = .holeImg (absNestCtx m.ctx) (m.prog.val.map absNestHole) (absU m.n) :=
  rfl
@[lockstep_simp] theorem absFvMap_keyMap (ds holes : alloc.vec.Vec arena.handle.EIdx) :
    absFvMap (.KeyMap ds holes) = .keyMap (absEIdxL ds) (absEIdxL holes) := rfl
@[lockstep_simp] theorem absFvMap_erase : absFvMap .Erase = .erase := rfl
@[lockstep_simp] theorem absFvMap_canon (p : alloc.vec.Vec arena.handle.EIdx) :
    absFvMap (.Canon p) = .canon (absEIdxL p) := rfl

/-- `fv_map_at` at the three variants that do not read back. -/
theorem fv_map_at_flat_ls {pers} (f : arena.inductives.positivity.FvMap)
    (hf : ∀ m, f ≠ .HoleImg m) (i : Std.U64) :
    ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.map absEIdx)
        (arena.inductives.positivity.fv_map_at pers st f i) lst
        (fvMapAt (absFvMap f) (absU i)) := by
  intro st lst hrel hinv
  cases f with
  | HoleImg m => exact absurd rfl (hf m)
  | KeyMap ds holes =>
    rw [arena.inductives.positivity.fv_map_at, absFvMap_keyMap, fvMapAt]
    lockstep
  | Erase =>
    rw [arena.inductives.positivity.fv_map_at, absFvMap_erase, fvMapAt]
    lockstep
  | Canon p =>
    rw [arena.inductives.positivity.fv_map_at, absFvMap_canon, fvMapAt]
    lockstep

/-- `replace_fvars_go` ⊑ `replaceFVarsGo` at a map `f` whose `fv_map_at` is
related (the hypothesis `hA`, discharged per variant below). -/
theorem replace_fvars_go_of {pers} (f : arena.inductives.positivity.FvMap)
    (hA : ∀ (i : Std.U64) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.map absEIdx)
        (arena.inductives.positivity.fv_map_at pers st f i) lst
        (fvMapAt (absFvMap f) (absU i))) (n : Nat) :
    ∀ (rm : ron.hashmap2.HashMap2 arena.handle.EIdx arena.handle.EIdx)
      (lm : Std.HashMap EIdx EIdx) (fuel : Std.U64) (h : arena.handle.EIdx) st lst,
      fuel.val = n → PEMemoRel rm lm → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => ∃ m', PEMemoRel a.2 m' ∧ b = (absEIdx a.1, m'))
        (arena.inductives.positivity.replace_fvars_go pers st f rm fuel h) lst
        (replaceFVarsGo (absFvMap f) lm n (absEIdx h)) := by
  induction n with
  | zero =>
    intro rm lm fuel h st lst hn hm hrel hinv
    rw [arena.inductives.positivity.replace_fvars_go, replaceFVarsGo]
    lockstep
  | succ m ih =>
    intro rm lm fuel h st lst hn hm hrel hinv
    rw [arena.inductives.positivity.replace_fvars_go, replaceFVarsGo]
    unfold arena.inductives.positivity.replace_fvars_node
    lockstep

theorem replace_fvars_of {pers} (f : arena.inductives.positivity.FvMap)
    (hA : ∀ (i : Std.U64) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.map absEIdx)
        (arena.inductives.positivity.fv_map_at pers st f i) lst
        (fvMapAt (absFvMap f) (absU i))) (e : arena.handle.EIdx) :
    ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdx a)
        (arena.inductives.positivity.replace_fvars pers st f e) lst
        (replaceFVars (absFvMap f) (absEIdx e)) := by
  intro st lst hrel hinv
  have hB := replace_fvars_go_of f hA
  have hB' : ∀ (rm : ron.hashmap2.HashMap2 arena.handle.EIdx arena.handle.EIdx)
      (lm : Std.HashMap EIdx EIdx) (fuel : Std.U64) (h : arena.handle.EIdx) st lst,
      PEMemoRel rm lm → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => ∃ m', PEMemoRel a.2 m' ∧ b = (absEIdx a.1, m'))
        (arena.inductives.positivity.replace_fvars_go pers st f rm fuel h) lst
        (replaceFVarsGo (absFvMap f) lm (absU fuel) (absEIdx h)) :=
    fun rm lm fuel h st lst hm hrel hinv => hB _ rm lm fuel h st lst rfl hm hrel hinv
  clear hB
  rw [arena.inductives.positivity.replace_fvars, replaceFVars]
  lockstep

/-- `replace_fvars_list` ⊑ `List.mapM (replaceFVars f)` from the cursor on,
behind the accumulator. -/
theorem replace_fvars_list_of {pers} (f : arena.inductives.positivity.FvMap)
    (hA : ∀ (i : Std.U64) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.map absEIdx)
        (arena.inductives.positivity.fv_map_at pers st f i) lst
        (fvMapAt (absFvMap f) (absU i))) (xs : alloc.vec.Vec arena.handle.EIdx) :
    ∀ (i : Std.Usize) st lst (out : alloc.vec.Vec arena.handle.EIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdxL a)
        (arena.inductives.positivity.replace_fvars_list pers st f xs i out) lst
        (do
          let r ← (absEIdxLFrom xs i).mapM fun x => replaceFVars (absFvMap f) x
          pure (absEIdxL out ++ r)) := by
  have hC := replace_fvars_of f hA
  intro i st lst out hrel hinv
  refine ls_cursor_acc xs absEIdx
    (fun (w : alloc.vec.Vec arena.handle.EIdx) l => do
      let r ← l.mapM fun x => replaceFVars (absFvMap f) x
      pure (absEIdxL w ++ r))
    (fun st k w => arena.inductives.positivity.replace_fvars_list pers st f xs k w)
    ?_ ?_ i st lst out hrel hinv
  · intro st lst k w hn hrel hinv
    rw [arena.inductives.positivity.replace_fvars_list.eq_def,
      if_pos (show k ≥ alloc.vec.Vec.len xs by scalar_tac)]
    simp only [List.mapM_nil, pure_bind, List.append_nil]
    lockstep
  · intro st lst k w hk hrel hinv ih
    have ih' : ∀ st' lst' (j : Std.Usize) (w' : alloc.vec.Vec arena.handle.EIdx),
        j.val = k.val + 1 → AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun a b => b = absEIdxL a)
          (arena.inductives.positivity.replace_fvars_list pers st' f xs j w') lst'
          (do
            let r ← (absEIdxLFrom xs j).mapM fun x => replaceFVars (absFvMap f) x
            pure (absEIdxL w' ++ r)) := ih
    clear ih
    rw [arena.inductives.positivity.replace_fvars_list.eq_def,
      if_neg (show ¬ k ≥ alloc.vec.Vec.len xs by scalar_tac)]
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    lockstep

/-- `replace_fvars_list` from an empty accumulator at `0` IS `List.mapM`. -/
theorem replace_fvars_list_new_of {pers} (f : arena.inductives.positivity.FvMap)
    (hA : ∀ (i : Std.U64) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.map absEIdx)
        (arena.inductives.positivity.fv_map_at pers st f i) lst
        (fvMapAt (absFvMap f) (absU i))) (xs : alloc.vec.Vec arena.handle.EIdx) :
    ∀ st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdxL a)
        (arena.inductives.positivity.replace_fvars_list pers st f xs 0#usize
          (alloc.vec.Vec.new arena.handle.EIdx)) lst
        ((absEIdxL xs).mapM fun x => replaceFVars (absFvMap f) x) := by
  intro st lst hrel hinv
  have h := replace_fvars_list_of f hA xs 0#usize st lst (alloc.vec.Vec.new arena.handle.EIdx)
    hrel hinv
  have e : (do
      let r ← (absEIdxLFrom xs 0#usize).mapM fun x => replaceFVars (absFvMap f) x
      pure (absEIdxL (alloc.vec.Vec.new arena.handle.EIdx) ++ r) : AM _)
      = (absEIdxL xs).mapM fun x => replaceFVars (absFvMap f) x := by
    simp [absEIdxL, alloc.vec.Vec.new]
  rwa [e] at h

/-- **`nest_hole_img` ⊑ `nestHoleImg`**, by induction on the stack prefix's
length: the frame hole's parameters are read back through the map one frame
shorter, whose `fv_map_at` is this lemma one level down.  The prefix length is
at most the stack's (`n ≤ |prog|`, which every caller's `prog.len()` and the
recursion's `n - 1` keep): the Rust's `usize` cast of `n - 1` is then exact. -/
theorem nest_hole_img_aux {pers} (k : Nat) :
    ∀ (ctx : arena.inductives.positivity.NestCtx)
      (prog : alloc.vec.Vec arena.inductives.positivity.NestHole) (n i : Std.U64) st lst,
      n.val = k → n.val ≤ prog.val.length → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.map absEIdx)
        (arena.inductives.positivity.nest_hole_img pers st ctx prog n i) lst
        (nestHoleImg (absNestCtx ctx) (prog.val.map absNestHole) k (absU i)) := by
  induction k with
  | zero =>
    intro ctx prog n i st lst hn hnp hrel hinv
    rw [arena.inductives.positivity.nest_hole_img, if_pos (by scalar_tac), nestHoleImg]
    lockstep
    rw [absNIdxL, map_getD_of_lt absNIdx ctx.names.val _ _ (by assumption) (by scalar_tac)]
    lockstep
  | succ k ih =>
    intro ctx prog n i st lst hn hnp hrel hinv
    have hA : ∀ (m : arena.inductives.positivity.HoleImgMap), m.n.val = k →
        m.n.val ≤ m.prog.val.length →
        ∀ (i : Std.U64) st lst, AStateRel₀ pers st lst → AStateInv pers st →
        LS pers (fun a b => b = a.map absEIdx)
          (arena.inductives.positivity.fv_map_at pers st (.HoleImg m) i) lst
          (fvMapAt (absFvMap (.HoleImg m)) (absU i)) := by
      intro m hm hmp i st lst hrel hinv
      rw [arena.inductives.positivity.fv_map_at, absFvMap_holeImg, fvMapAt]
      rw [show absU m.n = k from hm]
      exact ih m.ctx m.prog m.n i st lst hm hmp hrel hinv
    have hD : ∀ (m : arena.inductives.positivity.HoleImgMap), m.n.val = k →
        m.n.val ≤ m.prog.val.length →
        ∀ (xs : alloc.vec.Vec arena.handle.EIdx) st lst,
        AStateRel₀ pers st lst → AStateInv pers st →
        LS pers (fun a b => b = absEIdxL a)
          (arena.inductives.positivity.replace_fvars_list pers st (.HoleImg m) xs 0#usize
            (alloc.vec.Vec.new arena.handle.EIdx)) lst
          ((absEIdxL xs).mapM fun x =>
            replaceFVars (.holeImg (absNestCtx m.ctx) (m.prog.val.map absNestHole) k) x) := by
      intro m hm hmp xs st lst hrel hinv
      have := replace_fvars_list_new_of (.HoleImg m) (hA m hm hmp) xs st lst hrel hinv
      rwa [absFvMap_holeImg, show absU m.n = k from hm] at this
    clear hA
    rw [arena.inductives.positivity.nest_hole_img, if_neg (by scalar_tac), nestHoleImg]
    iterate 4 lockstep_step
    · rw [if_pos (by simp only [beq_iff_eq]; scalar_tac)]
      lockstep_step
      rw [map_getD_of_lt absNestHole prog.val _ _ (by assumption)
        (by casesm* (_ : Nat) = _ ∨ Std.Usize.max < _ <;> scalar_tac)]
      lockstep
    · rw [if_neg (by simp only [beq_iff_eq]; scalar_tac)]
      exact ih ctx prog _ i st lst (by scalar_tac) (by scalar_tac) hrel hinv

/-- A read-back map's representation fact: a `HoleImg` map's prefix length is
at most its stack's (the only `HoleImg` the port builds is
`nest_ctor_nf`'s, at `prog.len()`, and `nest_hole_img`'s own, one shorter). -/
def FvMapWF : arena.inductives.positivity.FvMap → Prop
  | .HoleImg m => m.n.val ≤ m.prog.val.length
  | _ => True

@[lockstep] theorem nest_hole_img_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ctx : arena.inductives.positivity.NestCtx)
    (prog : alloc.vec.Vec arena.inductives.positivity.NestHole) (n i : Std.U64)
    (hnp : n.val ≤ prog.val.length) :
    LS pers (fun a b => b = a.map absEIdx)
      (arena.inductives.positivity.nest_hole_img pers st ctx prog n i) lst
      (nestHoleImg (absNestCtx ctx) (prog.val.map absNestHole) (absU n) (absU i)) :=
  nest_hole_img_aux _ ctx prog n i st lst rfl hnp hrel hinv

@[lockstep] theorem fv_map_at_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (f : arena.inductives.positivity.FvMap) (hwf : FvMapWF f)
    (i : Std.U64) :
    LS pers (fun a b => b = a.map absEIdx)
      (arena.inductives.positivity.fv_map_at pers st f i) lst
      (fvMapAt (absFvMap f) (absU i)) := by
  cases f with
  | HoleImg m =>
    rw [arena.inductives.positivity.fv_map_at, absFvMap_holeImg, fvMapAt]
    exact nest_hole_img_ls hrel hinv m.ctx m.prog m.n i hwf
  | _ => exact fv_map_at_flat_ls _ (by intro m h; cases h) i st lst hrel hinv

theorem fv_map_at_all {pers} (f : arena.inductives.positivity.FvMap) (hwf : FvMapWF f) :
    ∀ (i : Std.U64) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a.map absEIdx)
        (arena.inductives.positivity.fv_map_at pers st f i) lst
        (fvMapAt (absFvMap f) (absU i)) :=
  fun i _ _ hrel hinv => fv_map_at_ls hrel hinv f hwf i

@[lockstep] theorem replace_fvars_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (f : arena.inductives.positivity.FvMap) (hwf : FvMapWF f)
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx arena.handle.EIdx}
    {lm : Std.HashMap EIdx EIdx} (hm : PEMemoRel rm lm) (fuel : Std.U64)
    (h : arena.handle.EIdx) :
    LS pers (fun a b => ∃ m', PEMemoRel a.2 m' ∧ b = (absEIdx a.1, m'))
      (arena.inductives.positivity.replace_fvars_go pers st f rm fuel h) lst
      (replaceFVarsGo (absFvMap f) lm (absU fuel) (absEIdx h)) :=
  replace_fvars_go_of f (fv_map_at_all f hwf) _ rm lm fuel h st lst rfl hm hrel hinv

@[lockstep] theorem replace_fvars_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (f : arena.inductives.positivity.FvMap) (hwf : FvMapWF f)
    (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a)
      (arena.inductives.positivity.replace_fvars pers st f e) lst
      (replaceFVars (absFvMap f) (absEIdx e)) :=
  replace_fvars_of f (fv_map_at_all f hwf) e st lst hrel hinv

@[lockstep] theorem replace_fvars_list_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (f : arena.inductives.positivity.FvMap) (hwf : FvMapWF f)
    (xs : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize)
    (out : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdxL a)
      (arena.inductives.positivity.replace_fvars_list pers st f xs i out) lst
      (do
        let r ← (absEIdxLFrom xs i).mapM fun x => replaceFVars (absFvMap f) x
        pure (absEIdxL out ++ r)) :=
  replace_fvars_list_of f (fv_map_at_all f hwf) xs i st lst out hrel hinv

@[lockstep] theorem replace_fvars_list_new_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (f : arena.inductives.positivity.FvMap) (hwf : FvMapWF f)
    (xs : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdxL a)
      (arena.inductives.positivity.replace_fvars_list pers st f xs 0#usize
        (alloc.vec.Vec.new arena.handle.EIdx)) lst
      ((absEIdxL xs).mapM fun x => replaceFVars (absFvMap f) x) :=
  replace_fvars_list_new_of f (fv_map_at_all f hwf) xs st lst hrel hinv

/-! ## The whole-application abstraction: `ph_app`, `nest_canon_sub`, `app_hole` -/

/-- `ph_app` ⊑ `phApp?`: the Rust reads the placeholder `b + (n - 1)` at a
positive `n`, the twin `b + n'` at `n = n' + 1` — the same index. -/
theorem ph_app_aux (k : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (b : Std.U64) (e : arena.handle.EIdx) (n : Std.U64),
      n.val = k → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = a.map absConstT)
        (arena.inductives.positivity.ph_app pers st b e n) st lst
        (phApp? (absU b) (absEIdx e) k) := by
  induction k with
  | zero =>
    intro pers st lst b e n hn hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.positivity.ph_app, if_pos (by scalar_tac), phApp?]
    lockstep
  | succ k ih =>
    intro pers st lst b e n hn hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.positivity.ph_app, if_neg (by scalar_tac), phApp?]
    lockstep

@[lockstep] theorem ph_app_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (b : Std.U64) (e : arena.handle.EIdx) (n : Std.U64) :
    LSR pers (fun a b => b = a.map absConstT)
      (arena.inductives.positivity.ph_app pers st b e n) st lst
      (phApp? (absU b) (absEIdx e) (absU n)) :=
  ph_app_aux _ b e n rfl hrel hinv

@[lockstep] theorem nest_canon_sub_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (us : arena.handle.LsIdx) (n : Std.U64) (c : arena.handle.NIdx) (v : arena.handle.LsIdx) :
    LS pers (fun a b => b = a.map absEIdx)
      (arena.inductives.positivity.nest_canon_sub pers st names us n c v) lst
      (nestCanonSub (absNIdxL names) (absLsIdx us) (absU n) (absNIdx c) (absLsIdx v)) := by
  rw [arena.inductives.positivity.nest_canon_sub, nestCanonSub]
  lockstep

@[lockstep] theorem app_hole_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (us : arena.handle.LsIdx) (b n : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = a.map absEIdx)
      (arena.inductives.positivity.app_hole pers st names us b n e) lst
      (appHole? (absNIdxL names) (absLsIdx us) (absU b) (absU n) (absEIdx e)) := by
  rw [arena.inductives.positivity.app_hole, appHole?]
  lockstep

/-! ## `nest_phs` -/

/-- `nest_phs` ⊑ `(List.range' i (n - i)).mapM`, behind the accumulator. -/
theorem nest_phs_acc {pers} (n : Std.U64) :
    ∀ (i : Std.U64) st lst (out : alloc.vec.Vec arena.handle.EIdx),
      AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = absEIdxL a)
        (arena.inductives.positivity.nest_phs pers st n i out) lst
        (do
          let r ← (List.range' i.val (n.val - i.val)).mapM fun i => do
            let z ← zeroLevel
            let s ← internSortE z
            internFVarE i s
          pure (absEIdxL out ++ r)) := by
  refine ls_counted n
    (fun (w : alloc.vec.Vec arena.handle.EIdx) m i => do
      let r ← (List.range' i m).mapM fun i => do
        let z ← zeroLevel
        let s ← internSortE z
        internFVarE i s
      pure (absEIdxL w ++ r))
    (fun st i w => arena.inductives.positivity.nest_phs pers st n i w) ?_ ?_
  · intro st lst i w hn hrel hinv
    rw [arena.inductives.positivity.nest_phs.eq_def, if_pos (by scalar_tac)]
    simp only [List.range'_zero, List.mapM_nil, pure_bind, List.append_nil]
    lockstep
  · intro st lst i w m hi hm hrel hinv ih
    rw [arena.inductives.positivity.nest_phs.eq_def, if_neg (by scalar_tac)]
    simp only [List.range'_succ, List.mapM_cons, bind_assoc, pure_bind]
    lockstep

@[lockstep] theorem nest_phs_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : Std.U64) :
    LS pers (fun a b => b = absEIdxL a)
      (arena.inductives.positivity.nest_phs pers st n 0#u64
        (alloc.vec.Vec.new arena.handle.EIdx)) lst
      (nestPhs (absU n)) := by
  have h := nest_phs_acc n 0#u64 st lst (alloc.vec.Vec.new arena.handle.EIdx) hrel hinv
  have e : (do
      let r ← (List.range' (0#u64 : Std.U64).val (n.val - (0#u64 : Std.U64).val)).mapM fun i => do
        let z ← zeroLevel
        let s ← internSortE z
        internFVarE i s
      pure (absEIdxL (alloc.vec.Vec.new arena.handle.EIdx) ++ r) : AM _) = nestPhs (absU n) := by
    simp [nestPhs, absEIdxL, alloc.vec.Vec.new, List.range_eq_range']
  rwa [e] at h

/-! ## `replace_apps_go` / `replace_apps`, `nest_canon_crest`, `nest_crest` -/

theorem replace_apps_go_aux {pers} (names : alloc.vec.Vec arena.handle.NIdx)
    (us : arena.handle.LsIdx) (b n : Std.U64) (k : Nat) :
    ∀ (rm : ron.hashmap2.HashMap2 arena.handle.EIdx arena.handle.EIdx)
      (lm : Std.HashMap EIdx EIdx) (fuel : Std.U64) (h : arena.handle.EIdx) st lst,
      fuel.val = k → PEMemoRel rm lm → AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => ∃ m', PEMemoRel a.2 m' ∧ b = (absEIdx a.1, m'))
        (arena.inductives.positivity.replace_apps_go pers st names us b n rm fuel h) lst
        (replaceAppsGo (absNIdxL names) (absLsIdx us) (absU b) (absU n) lm k (absEIdx h)) := by
  induction k with
  | zero =>
    intro rm lm fuel h st lst hn hm hrel hinv
    rw [arena.inductives.positivity.replace_apps_go, replaceAppsGo]
    lockstep
  | succ m ih =>
    intro rm lm fuel h st lst hn hm hrel hinv
    rw [arena.inductives.positivity.replace_apps_go, replaceAppsGo]
    unfold arena.inductives.positivity.replace_apps_node
      arena.inductives.positivity.replace_apps_app
    lockstep

@[lockstep] theorem replace_apps_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (us : arena.handle.LsIdx) (b n : Std.U64)
    {rm : ron.hashmap2.HashMap2 arena.handle.EIdx arena.handle.EIdx}
    {lm : Std.HashMap EIdx EIdx} (hm : PEMemoRel rm lm) (fuel : Std.U64)
    (h : arena.handle.EIdx) :
    LS pers (fun a b => ∃ m', PEMemoRel a.2 m' ∧ b = (absEIdx a.1, m'))
      (arena.inductives.positivity.replace_apps_go pers st names us b n rm fuel h) lst
      (replaceAppsGo (absNIdxL names) (absLsIdx us) (absU b) (absU n) lm (absU fuel)
        (absEIdx h)) :=
  replace_apps_go_aux names us b n _ rm lm fuel h st lst rfl hm hrel hinv

@[lockstep] theorem replace_apps_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (us : arena.handle.LsIdx) (b n : Std.U64) (e : arena.handle.EIdx) :
    LS pers (fun a b => b = absEIdx a)
      (arena.inductives.positivity.replace_apps pers st names us b n e) lst
      (replaceApps (absNIdxL names) (absLsIdx us) (absU b) (absU n) (absEIdx e)) := by
  rw [arena.inductives.positivity.replace_apps, replaceApps]
  lockstep

@[lockstep] theorem nest_canon_crest_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (us : arena.handle.LsIdx) (n : Std.U64) (cty : arena.handle.EIdx) :
    LS pers (fun a b => b = a.map absEIdx)
      (arena.inductives.positivity.nest_canon_crest pers st names us n cty) lst
      (nestCanonCrest (absNIdxL names) (absLsIdx us) (absU n) (absEIdx cty)) := by
  rw [arena.inductives.positivity.nest_canon_crest, nestCanonCrest]
  lockstep

@[lockstep_simp] theorem fvMapWF_keyMap (a b : alloc.vec.Vec arena.handle.EIdx) :
    FvMapWF (.KeyMap a b) = True := rfl
@[lockstep_simp] theorem fvMapWF_erase : FvMapWF .Erase = True := rfl
@[lockstep_simp] theorem fvMapWF_canon (a : alloc.vec.Vec arena.handle.EIdx) :
    FvMapWF (.Canon a) = True := rfl

@[lockstep] theorem nest_crest_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (us : arena.handle.LsIdx) (ds holes : alloc.vec.Vec arena.handle.EIdx)
    (cty : arena.handle.EIdx) :
    LS pers (fun a b => b = a.map absEIdx)
      (arena.inductives.positivity.nest_crest pers st names us ds holes cty) lst
      (nestCrest (absNIdxL names) (absLsIdx us) (absEIdxL ds) (absEIdxL holes)
        (absEIdx cty)) := by
  rw [arena.inductives.positivity.nest_crest, nestCrest]
  lockstep

/-! ## The result head, the closedness scans, the walk stack -/

@[lockstep] theorem nest_res_head_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (e : arena.handle.EIdx) :
    LSR pers (fun a b => b = a)
      (arena.inductives.positivity.nest_res_head pers st e) st lst
      (nestResHead (absEIdx e)) := by
  apply LSR.of_LS
  rw [arena.inductives.positivity.nest_res_head, nestResHead]
  lockstep

/-- `nest_res_ok` — a fragment of `nestCtors`: the result headed by its hole
with hole-free indices, stated against that sub-expression of the twin. -/
@[lockstep] theorem nest_res_ok_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ctx : arena.inductives.positivity.NestCtx) (hi : Std.U64)
    (cur : arena.handle.EIdx) :
    LSR pers (fun a b => b = a)
      (arena.inductives.positivity.nest_res_ok pers st ctx hi cur) st lst
      (do
        if ← nestResHead (absEIdx cur) then do
          let args ← getAppArgs coreWalkFuel (absEIdx cur)
          let occ ← args.anyM fun x => nestOcc (absNIdxL ctx.names) (absU ctx.n_p) (absU hi) x
          pure !occ
        else pure false) := by
  apply LSR.of_LS
  rw [arena.inductives.positivity.nest_res_ok]
  lockstep

/-- `all_fvar_b_le` ⊑ `List.allM (fvarB · ≤ bound)` from the cursor on. -/
@[lockstep] theorem all_fvar_b_le_ls {pers} (ds : alloc.vec.Vec arena.handle.EIdx)
    (bound : Std.U64) :
    ∀ (i : Std.Usize) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.positivity.all_fvar_b_le pers st ds bound i) lst
        ((absEIdxLFrom ds i).allM fun x => do
          let b ← fvarB coreWalkFuel x
          pure (decide (b ≤ absU bound))) := by
  refine ls_cursor ds absEIdx
    (fun l => l.allM fun x => do
      let b ← fvarB coreWalkFuel x
      pure (decide (b ≤ absU bound)))
    (fun st i => arena.inductives.positivity.all_fvar_b_le pers st ds bound i) ?_ ?_
  · intro st lst i hn hrel hinv
    rw [arena.inductives.positivity.all_fvar_b_le.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len ds by scalar_tac), List.allM]
    lockstep
  · intro st lst i hi hrel hinv ih
    have ih' : ∀ st' lst' (j : Std.Usize), j.val = i.val + 1 →
        AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun a b => b = a)
          (arena.inductives.positivity.all_fvar_b_le pers st' ds bound j) lst'
          ((absEIdxLFrom ds j).allM fun x => do
            let b ← fvarB coreWalkFuel x
            pure (decide (b ≤ absU bound))) := ih
    clear ih
    rw [arena.inductives.positivity.all_fvar_b_le.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len ds by scalar_tac)]
    simp only [List.allM, bind_assoc, pure_bind]
    lockstep

/-- `params_closed` ⊑ `List.allM (bvarB · == 0 && fvarB · ≤ hi)` from the
cursor on, the `bvarB` read first. -/
@[lockstep] theorem params_closed_ls {pers} (xs : alloc.vec.Vec arena.handle.EIdx)
    (hi : Std.U64) :
    ∀ (i : Std.Usize) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.positivity.params_closed pers st xs hi i) lst
        ((absEIdxLFrom xs i).allM fun x => do
          let bb ← bvarB coreWalkFuel x
          if bb != 0 then pure false
          else do
            let fb ← fvarB coreWalkFuel x
            pure (decide (fb ≤ absU hi))) := by
  refine ls_cursor xs absEIdx
    (fun l => l.allM fun x => do
      let bb ← bvarB coreWalkFuel x
      if bb != 0 then pure false
      else do
        let fb ← fvarB coreWalkFuel x
        pure (decide (fb ≤ absU hi)))
    (fun st i => arena.inductives.positivity.params_closed pers st xs hi i) ?_ ?_
  · intro st lst i hn hrel hinv
    rw [arena.inductives.positivity.params_closed.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len xs by scalar_tac), List.allM]
    lockstep
  · intro st lst i hlt hrel hinv ih
    have ih' : ∀ st' lst' (j : Std.Usize), j.val = i.val + 1 →
        AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun a b => b = a)
          (arena.inductives.positivity.params_closed pers st' xs hi j) lst'
          ((absEIdxLFrom xs j).allM fun x => do
            let bb ← bvarB coreWalkFuel x
            if bb != 0 then pure false
            else do
              let fb ← fvarB coreWalkFuel x
              pure (decide (fb ≤ absU hi))) := ih
    clear ih
    rw [arena.inductives.positivity.params_closed.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len xs by scalar_tac)]
    simp only [List.allM, bind_assoc]
    lockstep

@[lockstep] theorem nest_walk_stack_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ctx : arena.inductives.positivity.NestCtx)
    (prog : alloc.vec.Vec arena.inductives.positivity.NestHole)
    (ds : alloc.vec.Vec arena.handle.EIdx) :
    LS pers (fun a b => b = a.val.map absNestHole)
      (arena.inductives.positivity.nest_walk_stack pers st ctx prog ds) lst
      (nestWalkStack (absNestCtx ctx) (prog.val.map absNestHole) (absEIdxL ds)) := by
  rw [arena.inductives.positivity.nest_walk_stack, nestWalkStack]
  lockstep

/-! ## Uniform occurrences' low part: `pi_doms_occ`, `nest_root_canon` -/

theorem pi_doms_occ_aux (k : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (names : alloc.vec.Vec arena.handle.NIdx) (lo hi n : Std.U64) (e : arena.handle.EIdx),
      n.val = k → AStateRel₀ pers st lst → AStateInv pers st →
      LSR pers (fun a b => b = a)
        (arena.inductives.positivity.pi_doms_occ pers st names lo hi n e) st lst
        (piDomsOcc (absNIdxL names) (absU lo) (absU hi) k (absEIdx e)) := by
  induction k with
  | zero =>
    intro pers st lst names lo hi n e hn hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.positivity.pi_doms_occ, if_pos (by scalar_tac), piDomsOcc]
    lockstep
  | succ k ih =>
    intro pers st lst names lo hi n e hn hrel hinv
    apply LSR.of_LS
    rw [arena.inductives.positivity.pi_doms_occ, if_neg (by scalar_tac), piDomsOcc]
    lockstep

@[lockstep] theorem pi_doms_occ_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (names : alloc.vec.Vec arena.handle.NIdx)
    (lo hi n : Std.U64) (e : arena.handle.EIdx) :
    LSR pers (fun a b => b = a)
      (arena.inductives.positivity.pi_doms_occ pers st names lo hi n e) st lst
      (piDomsOcc (absNIdxL names) (absU lo) (absU hi) (absU n) (absEIdx e)) :=
  pi_doms_occ_aux _ names lo hi n e rfl hrel hinv

@[lockstep] theorem nest_root_canon_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ctx : arena.inductives.positivity.NestCtx)
    (cv : arena.env.IConstantVal) :
    LS pers (fun a b => b = a.map absEIdx)
      (arena.inductives.positivity.nest_root_canon pers st ctx cv) lst
      (nestRootCanon (absNestCtx ctx) (absIConstantVal cv)) := by
  rw [arena.inductives.positivity.nest_root_canon, nestRootCanon]
  lockstep

/-! ## `nest_ctor_nf` -/

@[lockstep_simp] theorem fvMapWF_holeImg (m : arena.inductives.positivity.HoleImgMap) :
    FvMapWF (.HoleImg m) = (m.n.val ≤ m.prog.val.length) := rfl

@[lockstep] theorem nest_ctor_nf_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ctx : arena.inductives.positivity.NestCtx)
    (prog : alloc.vec.Vec arena.inductives.positivity.NestHole) (us : arena.handle.LsIdx)
    (ds : alloc.vec.Vec arena.handle.EIdx) (cv : arena.env.IConstantVal)
    (closed : arena.handle.EIdx) :
    LS pers (fun a b => b = absNestCtorNf a)
      (arena.inductives.positivity.nest_ctor_nf pers st ctx prog us ds cv closed) lst
      (nestCtorNf (absNestCtx ctx) (prog.val.map absNestHole) (absLsIdx us) (absEIdxL ds)
        (absIConstantVal cv) (absEIdx closed)) := by
  rw [arena.inductives.positivity.nest_ctor_nf, nestCtorNf]
  lockstep

/-! ## Uniform occurrences: `nest_uniform_ok`, `nest_uniform_member`, `nest_uniform` -/

/-- `arena::env::i_constant_val_dup` is the identity (a LOCAL restatement of
the Core/Checker tiers' `i_constant_val_dup_ls`). -/
theorem pos_i_constant_val_dup_spec (cv : arena.env.IConstantVal) :
    LSP (arena.env.i_constant_val_dup cv) (fun o => o = cv) := by
  intro o h
  rw [arena.env.i_constant_val_dup] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  rw [dupId_nidx _ _ hn, dupId_eidx _ _ he, alloc.vec.Vec.ext _ _ (nidx_vec_dup_val hv)]

attribute [local lockstep] pos_i_constant_val_dup_spec

@[lockstep] theorem nest_uniform_ok_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (ctx : arena.inductives.positivity.NestCtx)
    (cv : arena.env.IConstantVal) :
    LS pers (fun a b => b = a)
      (arena.inductives.positivity.nest_uniform_ok pers st ctx cv) lst
      (nestUniformOk (absNestCtx ctx) (absIConstantVal cv)) := by
  rw [arena.inductives.positivity.nest_uniform_ok, nestUniformOk]
  lockstep

/-- `nest_uniform_member` ⊑ `List.allM (nestUniformOk ctx ·.1)` from the
cursor on. -/
@[lockstep] theorem nest_uniform_member_ls {pers} (ctx : arena.inductives.positivity.NestCtx)
    (cs : alloc.vec.Vec (arena.env.IConstantVal × Std.U64)) :
    ∀ (i : Std.Usize) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun a b => b = a)
        (arena.inductives.positivity.nest_uniform_member pers st ctx cs i) lst
        ((absCtorsLFrom cs i).allM fun c => nestUniformOk (absNestCtx ctx) c.1) := by
  refine ls_cursor cs (fun p => (absIConstantVal p.1, absU p.2))
    (fun l => l.allM fun c => nestUniformOk (absNestCtx ctx) c.1)
    (fun st i => arena.inductives.positivity.nest_uniform_member pers st ctx cs i) ?_ ?_
  · intro st lst i hn hrel hinv
    rw [arena.inductives.positivity.nest_uniform_member.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len cs by scalar_tac), List.allM]
    lockstep
  · intro st lst i hi hrel hinv ih
    have ih' : ∀ st' lst' (j : Std.Usize), j.val = i.val + 1 →
        AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun a b => b = a)
          (arena.inductives.positivity.nest_uniform_member pers st' ctx cs j) lst'
          ((absCtorsLFrom cs j).allM fun c => nestUniformOk (absNestCtx ctx) c.1) := ih
    clear ih
    rw [arena.inductives.positivity.nest_uniform_member.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len cs by scalar_tac), List.allM]
    lockstep
    all_goals
      simp only [Bool.not_eq_true] at hc
      subst hc
      lockstep

/-- A member list's constructor lists. -/
def absCtorsLL (v : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64))) :
    List (List (IConstantVal × Nat)) := v.val.map absCtorsL

/-- `nest_uniform` ⊑ `nestUniform`, the members from the cursor on. -/
@[lockstep] theorem nest_uniform_ls {pers} (ctx : arena.inductives.positivity.NestCtx)
    (css : alloc.vec.Vec (alloc.vec.Vec (arena.env.IConstantVal × Std.U64))) :
    ∀ (i : Std.Usize) st lst, AStateRel₀ pers st lst → AStateInv pers st →
      LS pers (fun _ _ => True)
        (arena.inductives.positivity.nest_uniform pers st ctx css i) lst
        (nestUniform (absNestCtx ctx) ((css.val.drop i.val).map absCtorsL)) := by
  refine ls_cursor css absCtorsL (fun l => nestUniform (absNestCtx ctx) l)
    (fun st i => arena.inductives.positivity.nest_uniform pers st ctx css i) ?_ ?_
  · intro st lst i hn hrel hinv
    rw [arena.inductives.positivity.nest_uniform.eq_def,
      if_pos (show i ≥ alloc.vec.Vec.len css by scalar_tac), nestUniform]
    lockstep
  · intro st lst i hi hrel hinv ih
    have ih' : ∀ st' lst' (j : Std.Usize), j.val = i.val + 1 →
        AStateRel₀ pers st' lst' → AStateInv pers st' →
        LS pers (fun _ _ => True)
          (arena.inductives.positivity.nest_uniform pers st' ctx css j) lst'
          (nestUniform (absNestCtx ctx) ((css.val.drop j.val).map absCtorsL)) := ih
    clear ih
    rw [arena.inductives.positivity.nest_uniform.eq_def,
      if_neg (show ¬ i ≥ alloc.vec.Vec.len css by scalar_tac), nestUniform]
    lockstep

end ConRon.Refine2

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
  `RelOn` + `Inv` (`ExprOps.LMemoRel` for the `bool` memos, `EMemoRel` /
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

end ConRon.Refine2

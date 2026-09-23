/-
# `ConRon.Refine2.Frontend.NatOpGround` — `frontend/nat_op_ground.rs`

**Task #97-P5-Frontend.**  The ground hoist: every pinned `Nat` operation's
stream-certified ground moved ahead of it.  Twenty-seven `pub fn`s against
`Arena/Frontend/NatOpGround.lean`'s fourteen `def`s (plus its two `where`
families), and the 1.9× is the usual two things — `match` chains where the
twin writes a `do` block, and a loop-per-`for` because `-loops-to-rec` copies
the code after a loop into every exit of it.

## Three shapes this module needs that the rest of the tier does not

1. **A `Std.HashSet` on the twin's side.**  `usedConstsGo`'s `seen` is a
   `Std.HashSet EIdx` where `fvar_leaves_go`'s twin is a `Std.HashMap EIdx
   Unit`, so `Refine2/ExprOps/Read.lean`'s `SeenRel` does not fit and
   `HSetRel` below is it at a set — membership, not value, for finding 3's
   reason (no reader looks at either value).
2. **The walk returns its memo OUTSIDE the `Result` and its state not at
   all.**  `used_consts_go` is a READER of the store that moves the `seen`
   table through by value (task #97-P4e part 2's own arrangement: *"the memo
   travels by value, so the probe's borrow is dead before the descent mutates
   the table"*), so its outcome is `UOut` — `Refine2/Checker/Shape.lean`'s
   `SimBR` at another accumulator.
3. **`hoist_close`'s explicit stack has no decreasing measure in the model.**
   Task #87 §5 stopped at exactly this function for the `Expr`-tree port —
   *"`sp` goes up as well as down"* — and §18 of that task is where it finally
   fell, as a well-founded argument over "records not yet at their target".
   **The port's loop is UNFUELLED; the twin's is not, and the two do not share
   a measure.**  (Until task #97-P3-Frontend round 8 this note said they did:
   the twin then counted POPS with `ds.size * ds.size + 1`, which a record
   pushing one entry per reference — duplicates included — can exhaust, and
   the twin answered a truncated closure where this loop runs on.)  The twin
   now spends fuel only on a pop that MARKS a record (`hoistDropDone` drops the
   finished ones structurally), passes `ds.size`, and
   `Arena/Frontend/NatOpGround.lean`'s `hoistClosure_fuel_succ` proves that
   fuel sufficient: at least the pending count, one more unit changes nothing.
   So `hoist_close_refines` below is an induction on the port's loop carrying
   `hoistPending ≤ fuel`, with the fuel-0 `fail` unreachable — the
   well-founded argument of task #87 §18, with the twin's lemma as its
   measure.

## `sorry` count in this file: 0
-/
import ConRon.Refine2.Frontend.Prepare
import ConRon.Refine2.Checker.Base
import ConRon.Refine2.Frontend.NatOpDeps

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend

open ConRon.Arena
open ConRon.Arena.Frontend
open ConRon.Refine.HashMap2 (Inv RelOn toFun)

/-! ## The `seen` set and the two target maps -/

/-- `usedConstsGo`'s visited set: **membership, not value** — the port's table
is `bool`-valued and the twin's is a `Std.HashSet`. -/
def HSetRel (rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
    (ls : Std.HashSet EIdx) : Prop :=
  (∀ k, (toFun rm k).isSome = ls.contains (absEIdx k)) ∧
    Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable rm

/-- The name index, `NIdx ↦ the index of the record declaring it`. -/
def NameIdxRel (rm : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64)
    (lm : Std.HashMap NIdx Nat) : Prop :=
  RelOn anyN rm lm absNIdx absU ∧
    Inv arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable rm

/-- The target map, `record index ↦ the operation index it must precede`. -/
def TargetRel (rm : ron.hashmap2.HashMap2 Std.U64 Std.U64)
    (lm : Std.HashMap Nat Nat) : Prop :=
  RelOn (fun _ : Std.U64 => True) rm lm absU absU ∧
    Inv U64.Insts.Con_ron_coreRonHashmapHashable rm

/-! ## The two outcome shapes -/

/-- A `used_consts_*` walk that only READS the store: the accumulator
abstracted, the `seen` table related, no post-state. -/
def UOut (lst : AState)
    (o : core.result.Result (alloc.vec.Vec arena.handle.NIdx)
      kernel.core_types.CheckError ×
      ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
    (x : AM (Std.HashSet EIdx × Array NIdx)) : Prop :=
  match o.1 with
  | .Ok acc => ∃ s', x.run lst = .ok ((s', absNIdxArr acc), lst) ∧ HSetRel o.2 s'
  | .Err e => AErrSim e (x.run lst)

/-- The same, for the one walk that APPENDS (`used_consts_block` interns a
`toConstantVal`). -/
def UOutS (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result (alloc.vec.Vec arena.handle.NIdx)
      kernel.core_types.CheckError × arena.monad.AState ×
      ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
    (x : AM (Std.HashSet EIdx × Array NIdx)) : Prop :=
  match o.1 with
  | .Ok acc => ∃ s' lst', x.run lst = .ok ((s', absNIdxArr acc), lst') ∧
      HSetRel o.2.2 s' ∧ AStateRel₀ pers o.2.1 lst' ∧ AStateInv pers o.2.1
  | .Err e => AErrSim e (x.run lst)

/-! ## The three probes (task #97-P5-Front round 2)

`HashMap2::get` at the three key types of this module, each the table's
`toFun` with no side condition but its `Inv`. -/

theorem eidx_get {V : Type} {m : ron.hashmap2.HashMap2 arena.handle.EIdx V}
    (hinv : Inv arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable m)
    {k : arena.handle.EIdx} {r : Option V}
    (h : ron.hashmap2.HashMap2.get arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable
      arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2 m k = ok r) :
    r = toFun m k :=
  ConRon.Refine.HashMap2.get_refines_gen eidx_eq2 hinv (fun _ _ => trivial) trivial h

theorem u64_get {V : Type} {m : ron.hashmap2.HashMap2 Std.U64 V}
    (hinv : Inv U64.Insts.Con_ron_coreRonHashmapHashable m)
    {k : Std.U64} {r : Option V}
    (h : ron.hashmap2.HashMap2.get U64.Insts.Con_ron_coreRonHashmapHashable
      U64.Insts.Con_ron_coreRonHashmapEq2 m k = ok r) :
    r = toFun m k :=
  ConRon.Refine.HashMap2.get_refines_gen (P := fun _ => True) u64Eq2Fwd hinv (fun _ _ => trivial) trivial h

/-- A target-map probe, read through `TargetRel`. -/
theorem target_get {rm lm} (hr : TargetRel rm lm) {k : Std.U64} {r : Option Std.U64}
    (h : ron.hashmap2.HashMap2.get U64.Insts.Con_ron_coreRonHashmapHashable
      U64.Insts.Con_ron_coreRonHashmapEq2 rm k = ok r) :
    r.map absU = lm[absU k]? := by
  rw [u64_get hr.2 h]; exact hr.1 k trivial

/-! ## The visited set -/

/-- **`nat_op_ground::seen_has`** — membership in the visited set. -/
theorem seen_has_refines {rm ls e v} (hs : HSetRel rm ls)
    (h : frontend.nat_op_ground.seen_has rm e = ok v) :
    v = ls.contains (absEIdx e) := by
  rw [frontend.nat_op_ground.seen_has] at h
  obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [eidx_get hs.2 hr] at h
  rw [← hs.1 e]
  cases hto : toFun rm e <;> rw [hto] at h <;> simp only [Result.ok.injEq] at h <;>
    simp [← h]

/-! ## The constant walk

`usedConstsGo` over `view`, with `used_consts_node` and `used_consts_two` as
the port's two extra splits (extraction rule 5: the probe's borrow must be
dead before the descent mutates the table).  Neither has a twin, so both are
stated against the twin's own arm. -/

/-- An in-bounds `Vec` index answers the element. -/
theorem vec_index_ok_eq {α : Type} (v : alloc.vec.Vec α) (i : Std.Usize)
    (hi : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok v.val[i.val] := by
  simp only [alloc.vec.Vec.index_slice_index]
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec v i hi)
  rw [hy, hyv]

/-- The twin's `view` at a handle the port viewed: a read, at the same state. -/
theorem view_step {pers st lst} (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    {h : arena.handle.EIdx} {o} (hv : arena.monad.view pers st h = ok o) :
    match o with
    | .Ok v => (Arena.view (absEIdx h)).run lst = .ok (absENodeView v, lst)
    | .Err e => AErrSim e ((Arena.view (absEIdx h)).run lst) := by
  have hL := Lockstep.view_ls hrel hinv h o hv
  have hrun := Lockstep.view_run_of (absEIdx h) lst
  cases o with
  | Err e => exact hL
  | Ok v =>
    obtain ⟨b, lst', hx, hb, -, -⟩ := hL
    rw [hx, hb]
    rw [hrun] at hx
    split at hx
    · cases hx; rfl
    · cases hx

/-- The visited set's insert (the port records `true`). -/
theorem seen_insert_rel {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {ls : Std.HashSet EIdx} (hs : HSetRel rm ls) {e : arena.handle.EIdx} {old m'}
    (h : ron.hashmap2.HashMap2.insert arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable
      arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2 rm e true = ok (old, m')) :
    HSetRel m' (ls.insert (absEIdx e)) := by
  obtain ⟨hinv', -, htf, -⟩ := ConRon.Refine.HashMap2.insert_refines_gen eidx_eq2 hs.2
    ConRon.Refine.HashMap2.KeysOk_true trivial h
  refine ⟨fun k => ?_, hinv'⟩
  rw [htf, Std.HashSet.contains_insert]
  by_cases hk : k = e
  · subst hk; simp
  · have hne : (absEIdx e == absEIdx k) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact fun h' => hk (absEIdx_inj h').symm
    rw [Function.update_of_ne hk, hs.1 k, hne, Bool.false_or]

theorem absNIdxArr_push {acc : alloc.vec.Vec arena.handle.NIdx} {n acc'}
    (h : alloc.vec.Vec.push acc n = ok acc') :
    absNIdxArr acc' = (absNIdxArr acc).push (absNIdx n) := by
  simp [absNIdxArr, ConRon.Refine.vec_push_val h]

/-- The used-constants walk, every port split (`used_consts_node`,
`used_consts_two`) unfolded in place, by induction on the fuel. -/
theorem used_consts_go_aux {pers rst lst} (hrel : AStateRel₀ pers rst lst)
    (hinv : AStateInv pers rst) (N : Nat) :
    ∀ (seen : ron.hashmap2.HashMap2 arena.handle.EIdx Bool) (ls : Std.HashSet EIdx)
      (acc : alloc.vec.Vec arena.handle.NIdx) (fuel : Std.U64) (e : arena.handle.EIdx) o,
      fuel.val = N → HSetRel seen ls →
      frontend.nat_op_ground.used_consts_go pers rst seen acc fuel e = ok o →
      UOut lst o (usedConstsGo ls (absNIdxArr acc) N (absEIdx e)) := by
  induction N with
  | zero =>
    intro seen ls acc fuel e o hn hs h
    rw [frontend.nat_op_ground.used_consts_go, if_pos (by scalar_tac)] at h
    obtain ⟨sl, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases fail_run hr
    cases Result.ok_injective h
    exact AErrSim.internal rfl
  | succ k ih =>
    -- the two-child step, used by four arms
    have two : ∀ (seen : ron.hashmap2.HashMap2 arena.handle.EIdx Bool) (ls : Std.HashSet EIdx)
        (acc : alloc.vec.Vec arena.handle.NIdx) (fuel : Std.U64) (a b : arena.handle.EIdx) o,
        fuel.val = k → HSetRel seen ls →
        frontend.nat_op_ground.used_consts_two pers rst seen acc fuel a b = ok o →
        UOut lst o (do
          let (s, acc) ← usedConstsGo ls (absNIdxArr acc) k (absEIdx a)
          usedConstsGo s acc k (absEIdx b)) := by
      intro seen ls acc fuel a b o hn hs h
      rw [frontend.nat_op_ground.used_consts_two] at h
      obtain ⟨⟨r, seen1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h1 := ih seen ls acc fuel a _ hn hs hr
      unfold UOut at h1 ⊢
      rw [am_run_bind']
      cases r with
      | Err e =>
        cases Result.ok_injective h
        exact AErrSim.bind h1 _
      | Ok acc2 =>
        obtain ⟨s', hx, hs'⟩ := h1
        rw [hx, except_ok_bind]
        exact ih seen1 s' acc2 fuel b o hn hs' h
    intro seen ls acc fuel e o hn hs h
    rw [frontend.nat_op_ground.used_consts_go, if_neg (by scalar_tac)] at h
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv := seen_has_refines hs hb
    unfold usedConstsGo
    split at h
    · rename_i hbt
      cases Result.ok_injective h
      rw [if_pos (by rw [← hbv]; exact hbt)]
      exact ⟨ls, rfl, hs⟩
    · rename_i hbt
      rw [if_neg (by rw [← hbv]; exact hbt)]
      obtain ⟨e1, he1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      rw [dupId_eidx _ _ he1] at h
      obtain ⟨⟨old, seen1⟩, hins, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hs1 := seen_insert_rel hs hins
      obtain ⟨i, hi, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hiv : i.val = k := by
        have := (ConRon.Refine.Nat.usub_val hi).2; rw [this, hn]; rfl
      rw [frontend.nat_op_ground.used_consts_node] at h
      obtain ⟨r, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hV := view_step hrel hinv hr
      unfold UOut
      simp only []
      rw [am_run_bind']
      cases r with
      | Err er =>
        cases Result.ok_injective h
        exact AErrSim.bind hV _
      | Ok v =>
      rw [hV, except_ok_bind]
      cases v with
      | BVar _ => cases Result.ok_injective h; exact ⟨_, rfl, hs1⟩
      | «Sort» _ => cases Result.ok_injective h; exact ⟨_, rfl, hs1⟩
      | Lit _ => cases Result.ok_injective h; exact ⟨_, rfl, hs1⟩
      | Const n us =>
        obtain ⟨acc1, hacc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        cases Result.ok_injective h
        exact ⟨_, by simp only [absENodeView, absNIdxArr_push hacc1]; rfl, hs1⟩
      | FVar _ ty => exact ih seen1 _ acc i ty o hiv hs1 h
      | App f a => exact two seen1 _ acc i f a o hiv hs1 h
      | Lam ty b _ => exact two seen1 _ acc i ty b o hiv hs1 h
      | ForallE ty b _ => exact two seen1 _ acc i ty b o hiv hs1 h
      | LetE ty v b =>
        obtain ⟨⟨r1, seen2⟩, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have h2 := two seen1 _ acc i ty v _ hiv hs1 hr1
        unfold UOut at h2
        simp only [absENodeView]
        rw [← bind_assoc]
        rw [am_run_bind']
        cases r1 with
        | Err e =>
          cases Result.ok_injective h
          exact AErrSim.bind h2 _
        | Ok acc2 =>
          obtain ⟨s', hx, hs'⟩ := h2
          rw [hx, except_ok_bind]
          exact ih seen2 s' acc2 i b o hiv hs' h
      | Proj sn _ x =>
        obtain ⟨acc1, hacc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have := ih seen1 _ acc1 i x o hiv hs1 h
        simp only [absENodeView]
        rw [← absNIdxArr_push hacc1]
        exact this

/-- **`nat_op_ground::used_consts_go` refines `usedConstsGo`**
(`Arena/Frontend/NatOpGround.lean:50-71`). -/
theorem used_consts_go_refines {pers rst lst seen ls acc fuel e o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hs : HSetRel seen ls)
    (h : frontend.nat_op_ground.used_consts_go pers rst seen acc fuel e = ok o) :
    UOut lst o (usedConstsGo ls (absNIdxArr acc) (absU fuel) (absEIdx e)) :=
  used_consts_go_aux hrel hinv _ seen ls acc fuel e o rfl hs h

/-- **`arena::env::i_constant_info_to_constant_val` refines
`IConstantInfo.toConstantVal`** (`Arena/Env.lean:222-229`): six arms are a
copy, the `.projInfo` arm interns `Sort 1` in both, in the same order. -/
theorem i_constant_info_to_constant_val_refines {pers rst lst c o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : arena.env.i_constant_info_to_constant_val pers rst.store c = ok o) :
    Sim₀ absIConstantVal pers lst (o.1, withStore rst o.2)
      (absIConstantInfo c).toConstantVal := by
  have plain : ∀ v iv, arena.env.i_constant_val_dup v = ok iv →
      o = (.Ok iv, rst.store) →
      (absIConstantInfo c).toConstantVal = pure (absIConstantVal v) →
      Sim₀ absIConstantVal pers lst (o.1, withStore rst o.2)
        (absIConstantInfo c).toConstantVal := by
    intro v iv hiv ho hx
    subst ho
    refine AOut₀.ok (lst' := lst) ?_ hrel hinv
    rw [hx, i_constant_val_dup_abs hiv]; rfl
  cases c with
  | AxiomInfo v =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact plain v iv hiv (Result.ok_injective h).symm rfl
  | DefnInfo v _ _ =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact plain v iv hiv (Result.ok_injective h).symm rfl
  | ThmInfo v _ =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact plain v iv hiv (Result.ok_injective h).symm rfl
  | IndInfo v _ =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact plain v iv hiv (Result.ok_injective h).symm rfl
  | CtorInfo v _ _ =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact plain v iv hiv (Result.ok_injective h).symm rfl
  | RecInfo v _ _ _ =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    exact plain v iv hiv (Result.ok_injective h).symm rfl
  | ProjInfo tbl =>
    clear plain
    simp only [arena.env.i_constant_info_to_constant_val] at h
    show AOut₀ _ _ _ _ _
    simp only [absIConstantInfo, IConstantInfo.toConstantVal]
    -- 1. the level `0`
    obtain ⟨⟨r1, ar1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hS1 := intern_l_node_run₀ hrel hinv arena.store.LNodeView.Zero
      (o := (r1, withStore rst ar1))
      (by rw [arena.monad.intern_l_node, h1]; simp only [bind_tc_ok]; rfl)
    rw [show Arena.internLNode LNodeView.zero
        = Arena.internLNode (absLNodeView arena.store.LNodeView.Zero) from rfl]
    cases r1 with
    | Err e =>
      have ho := Result.ok_injective h
      subst ho
      exact AOut₀.errBind hS1
    | Ok z =>
    obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
    rw [run_bind_ok hx1]
    -- 2. the level `1`
    obtain ⟨⟨r2, ar2⟩, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hS2 := intern_l_node_run₀ hrel1 hinv1 (arena.store.LNodeView.Succ z)
      (o := (r2, withStore rst ar2))
      (by rw [arena.monad.intern_l_node]; rw [h2]; simp only [bind_tc_ok]; rfl)
    rw [show Arena.internLNode (.succ (absLIdx z))
        = Arena.internLNode (absLNodeView (arena.store.LNodeView.Succ z)) from rfl]
    cases r2 with
    | Err e =>
      have ho := Result.ok_injective h
      subst ho
      exact AOut₀.errBind hS2
    | Ok one =>
    obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
    rw [run_bind_ok hx2]
    -- 3. the expression `Sort 1`
    obtain ⟨⟨r3, ar3⟩, h3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hS3 := intern_e_sort_run₀ hrel2 hinv2 one
      (o := (r3, withStore rst ar3))
      (by rw [arena.monad.intern_e_sort]
          rw [show arena.store.EStore.intern_sort (withStore rst ar2).store pers one
              = arena.store.EStore.intern ar2 pers (arena.store.ENodeView.Sort one) from rfl,
            h3]
          simp only [bind_tc_ok]; rfl)
    rw [show Arena.internE (.sort (absLIdx one)) = Arena.internSortE (absLIdx one) from rfl]
    cases r3 with
    | Err e =>
      have ho := Result.ok_injective h
      subst ho
      exact AOut₀.errBind hS3
    | Ok ty =>
    obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hS3
    rw [run_bind_ok hx3]
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have ho := Result.ok_injective h
    subst ho
    refine AOut₀.ok (lst' := lst3) ?_ hrel3 hinv3
    show Except.ok _ = _
    simp only [absIConstantVal, absIProjTable, dupId_nidx _ _ hn, nidx_vec_dup_val hv]



/-- **`used_consts_rules` refines `usedConstsRules`**
(`Arena/Frontend/NatOpGround.lean:77-83`). -/
theorem used_consts_rules_refines {pers rst lst seen ls acc rules o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hs : HSetRel seen ls)
    (h : frontend.nat_op_ground.used_consts_rules pers rst seen acc rules = ok o) :
    UOut lst o (usedConstsRules ls (absNIdxArr acc) (absIRecRuleL rules)) := by
  rw [frontend.nat_op_ground.used_consts_rules] at h
  have key : ∀ (k : Nat) (i : Std.Usize) (seen : ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
      (ls : Std.HashSet EIdx) (out : alloc.vec.Vec arena.handle.NIdx) o,
      rules.val.length - i.val = k → HSetRel seen ls →
      frontend.nat_op_ground.used_consts_rules_loop pers rst seen rules out
        (alloc.vec.Vec.len rules) i = ok o →
      UOut lst o (usedConstsRules ls (absNIdxArr out) ((rules.val.drop i.val).map absIRecRule)) := by
    intro k
    induction k with
    | zero =>
      intro i seen ls out o hk hs h
      rw [frontend.nat_op_ground.used_consts_rules_loop, if_neg (by scalar_tac)] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by omega)]
      exact ⟨ls, rfl, hs⟩
    | succ k ih =>
      intro i seen ls out o hk hs h
      have hi : i.val < rules.val.length := by omega
      rw [frontend.nat_op_ground.used_consts_rules_loop, if_pos (by scalar_tac),
        vec_index_ok_eq rules i hi, bind_tc_ok] at h
      obtain ⟨⟨r, seen1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h1 := used_consts_go_refines hrel hinv hs hr
      rw [core_walk_fuel_abs] at h1
      rw [List.drop_eq_getElem_cons hi, List.map_cons]
      unfold UOut at h1 ⊢
      simp only [usedConstsRules]
      rw [am_run_bind']
      cases r with
      | Err e =>
        cases Result.ok_injective h
        exact AErrSim.bind h1 _
      | Ok a2 =>
        obtain ⟨s', hx, hs'⟩ := h1
        have hx' : (usedConstsGo ls (absNIdxArr out) coreWalkFuel (absIRecRule rules.val[i.val]).rhs).run lst
            = .ok ((s', absNIdxArr a2), lst) := hx
        rw [hx', except_ok_bind]
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi1v : i1.val = i.val + 1 := (ConRon.Refine.Nat.uadd_val hi1).trans (by simp)
        have := ih i1 seen1 s' a2 o (by omega) hs' h
        rw [hi1v] at this
        exact this
  have := key _ 0#usize seen ls acc o rfl hs h
  simpa [absIRecRuleL] using this

/-- **`used_consts_block` refines `usedConstsBlock`**
(`Arena/Frontend/NatOpGround.lean:86-96`).  The one walk of the group that
APPENDS: `toConstantVal` interns a `Sort 1` for a projection table. -/
theorem used_consts_block_refines {pers rst lst seen ls acc block o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hs : HSetRel seen ls)
    (h : frontend.nat_op_ground.used_consts_block pers rst seen acc block = ok o) :
    UOutS pers lst o (usedConstsBlock ls (absNIdxArr acc) (absICIL block)) := by
  rw [frontend.nat_op_ground.used_consts_block] at h
  have key : ∀ (k : Nat) (i : Std.Usize) (st : arena.monad.AState) (lst : AState)
      (seen : ron.hashmap2.HashMap2 arena.handle.EIdx Bool)
      (ls : Std.HashSet EIdx) (out : alloc.vec.Vec arena.handle.NIdx) o,
      block.val.length - i.val = k → AStateRel₀ pers st lst → AStateInv pers st →
      HSetRel seen ls →
      frontend.nat_op_ground.used_consts_block_loop pers st seen block out
        (alloc.vec.Vec.len block) i = ok o →
      UOutS pers lst o (usedConstsBlock ls (absNIdxArr out)
        ((block.val.drop i.val).map absIConstantInfo)) := by
    intro k
    induction k with
    | zero =>
      intro i st lst seen ls out o hk hrel hinv hs h
      rw [frontend.nat_op_ground.used_consts_block_loop, if_neg (by scalar_tac)] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le (by omega)]
      exact ⟨ls, lst, rfl, hs, hrel, hinv⟩
    | succ k ih =>
      intro i st lst seen ls out o hk hrel hinv hs h
      have hi : i.val < block.val.length := by omega
      rw [frontend.nat_op_ground.used_consts_block_loop, if_pos (by scalar_tac),
        vec_index_ok_eq block i hi, bind_tc_ok] at h
      obtain ⟨ci, hci, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hcia := i_constant_info_dup_abs hci
      obtain ⟨⟨r, e⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hT := i_constant_info_to_constant_val_refines hrel hinv hr
      rw [hcia] at hT
      rw [List.drop_eq_getElem_cons hi, List.map_cons]
      unfold UOutS
      simp only [usedConstsBlock]
      rw [am_run_bind']
      unfold Sim₀ at hT
      cases r with
      | Err e1 =>
        cases Result.ok_injective h
        exact AErrSim.bind hT _
      | Ok cv =>
      obtain ⟨lst1, hx1, hrel1, hinv1⟩ := hT
      rw [hx1, except_ok_bind]
      obtain ⟨⟨r1, seen1⟩, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hG := used_consts_go_refines hrel1 hinv1 hs hr1
      rw [core_walk_fuel_abs] at hG
      unfold UOut at hG
      rw [am_run_bind']
      cases r1 with
      | Err e2 =>
        cases Result.ok_injective h
        exact AErrSim.bind hG _
      | Ok a2 =>
      obtain ⟨s1, hx2, hs1⟩ := hG
      have hx2' : (usedConstsGo ls (absNIdxArr out) coreWalkFuel
          (absIConstantVal cv).type).run lst1 = .ok ((s1, absNIdxArr a2), lst1) := hx2
      rw [hx2', except_ok_bind]
      rcases hbi : block.val[i.val] with cvx | ⟨cvx, v, hint⟩ | ⟨cvx, v⟩ | ⟨cvx, caps⟩ |
        ⟨cvx, np, nf⟩ | ⟨cvx, mi, rp, rules⟩ | tbl
      all_goals rw [hbi] at h
      all_goals simp only [absIConstantInfo]
      case RecInfo =>
        obtain ⟨⟨r2, seen2⟩, hr2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hR := used_consts_rules_refines hrel1 hinv1 hs1 hr2
        unfold UOut at hR
        rw [am_run_bind']
        cases r2 with
        | Err e3 =>
          cases Result.ok_injective h
          exact AErrSim.bind hR _
        | Ok a3 =>
        obtain ⟨s2, hx3, hs2⟩ := hR
        have hx3' : (usedConstsRules s1 (absNIdxArr a2) (rules.val.map absIRecRule)).run lst1
            = .ok ((s2, absNIdxArr a3), lst1) := hx3
        rw [hx3', except_ok_bind]
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi1v : i1.val = i.val + 1 := (ConRon.Refine.Nat.uadd_val hi1).trans (by simp)
        have := ih i1 _ lst1 seen2 s2 a3 o (by omega) hrel1 hinv1 hs2 h
        rw [hi1v] at this
        exact this
      all_goals
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi1v : i1.val = i.val + 1 := (ConRon.Refine.Nat.uadd_val hi1).trans (by simp)
        have := ih i1 _ lst1 seen1 s1 a2 o (by omega) hrel1 hinv1 hs1 h
        rw [hi1v] at this
        simp only [pure_bind]
        exact this
  have := key _ 0#usize rst lst seen ls acc o rfl hrel hinv hs h
  simpa [absICIL] using this

/-- **`decl_used_consts_value`** — the cited three-arm case of
`IDeclaration.usedConsts` (a definition, a theorem, an opaque), which the port
factors out because the three arms share a body. -/
theorem decl_used_consts_value_refines {pers rst lst seen ls ty v o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hs : HSetRel seen ls)
    (h : frontend.nat_op_ground.decl_used_consts_value pers rst seen ty v = ok o) :
    UOut lst o (do
      let (s, acc) ← usedConstsGo ls #[] coreWalkFuel (absEIdx ty)
      usedConstsGo s acc coreWalkFuel (absEIdx v)) := by
  rw [frontend.nat_op_ground.decl_used_consts_value] at h
  obtain ⟨⟨r, seen1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have h1 := used_consts_go_refines hrel hinv hs hr
  rw [core_walk_fuel_abs] at h1
  have e0 : absNIdxArr (alloc.vec.Vec.new arena.handle.NIdx) = #[] := rfl
  rw [e0] at h1
  unfold UOut at h1 ⊢
  rw [am_run_bind']
  cases r with
  | Err e =>
    cases Result.ok_injective h
    exact AErrSim.bind h1 _
  | Ok acc =>
    obtain ⟨s', hx, hs'⟩ := h1
    rw [hx, except_ok_bind]
    have h2 := used_consts_go_refines hrel hinv hs' h
    rw [core_walk_fuel_abs] at h2
    exact h2

/-- **`decl_used_consts` refines `IDeclaration.usedConsts`**
(`Arena/Frontend/NatOpGround.lean:100-106`). -/
theorem decl_used_consts_refines {pers rst lst d o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.nat_op_ground.decl_used_consts pers rst d = ok o) :
    Sim₀ absNIdxArr pers lst o
      (IDeclaration.usedConsts (absIDeclaration d)) := by
  rw [frontend.nat_op_ground.decl_used_consts] at h
  obtain ⟨seen, hseen, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hs : HSetRel seen (∅ : Std.HashSet EIdx) := by
    obtain ⟨hi0, -, hnone⟩ := ConRon.Refine.HashMap2.new_refines
      (HashableInst := arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable) hseen
    exact ⟨fun k => by rw [hnone k]; simp, hi0⟩
  have e0 : absNIdxArr (alloc.vec.Vec.new arena.handle.NIdx) = #[] := rfl
  -- a read-only walk's answer, its second component
  have snd : ∀ {r : core.result.Result (alloc.vec.Vec arena.handle.NIdx)
      kernel.core_types.CheckError} {s1} {X : AM (Std.HashSet EIdx × Array NIdx)},
      UOut lst (r, s1) X →
      AOut₀ absNIdxArr pers r rst ((X >>= fun p => pure p.2).run lst) := by
    intro r s1 X hU
    unfold UOut at hU
    rw [am_run_bind']
    cases r with
    | Err e => exact AErrSim.bind hU _
    | Ok a =>
      obtain ⟨s', hx, -⟩ := hU
      rw [hx, except_ok_bind]
      exact ⟨lst, rfl, hrel, hinv⟩
  unfold Sim₀
  cases d with
  | AxiomDecl cv =>
    obtain ⟨⟨r, s1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    have hG := used_consts_go_refines hrel hinv hs hr
    rw [core_walk_fuel_abs, e0] at hG
    exact snd hG
  | DefnDecl cv v hint =>
    obtain ⟨⟨r, s1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    have hV := decl_used_consts_value_refines hrel hinv hs hr
    have := snd hV
    simp only [bind_assoc] at this
    exact this
  | ThmDecl cv v =>
    obtain ⟨⟨r, s1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    have hV := decl_used_consts_value_refines hrel hinv hs hr
    have := snd hV
    simp only [bind_assoc] at this
    exact this
  | OpaqueDecl cv v =>
    obtain ⟨⟨r, s1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    have hV := decl_used_consts_value_refines hrel hinv hs hr
    have := snd hV
    simp only [bind_assoc] at this
    exact this
  | BasisDecl _ =>
    cases Result.ok_injective h
    exact ⟨lst, rfl, hrel, hinv⟩
  | QuotDecl _ _ =>
    cases Result.ok_injective h
    exact ⟨lst, rfl, hrel, hinv⟩
  | IndDecl block _ =>
    obtain ⟨⟨r, st1, s1⟩, hr, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    cases Result.ok_injective h
    have hB := used_consts_block_refines hrel hinv hs hr
    rw [e0] at hB
    unfold UOutS at hB
    show AOut₀ absNIdxArr pers r st1 _
    simp only [absIDeclaration, IDeclaration.usedConsts]
    rw [am_run_bind']
    cases r with
    | Err e => exact AErrSim.bind hB _
    | Ok a =>
      obtain ⟨s', lst', hx, -, hrel', hinv'⟩ := hB
      have hx' : (usedConstsBlock ∅ #[] (List.map absIConstantInfo block.val)).run lst
          = .ok ((s', absNIdxArr a), lst') := hx
      rw [hx', except_ok_bind]
      exact ⟨lst', rfl, hrel', hinv'⟩

/-! ## The trigger set -/

/-- **`nidx_contains`** — `Vec<NIdx>` membership, the twin's `List.contains`. -/
theorem nidx_contains_refines {ns n v}
    (h : frontend.nat_op_ground.nidx_contains ns n = ok v) :
    v = (absNIdxL ns).contains (absNIdx n) := by
  rw [frontend.nat_op_ground.nidx_contains] at h
  have key : ∀ (i : Std.Usize) (_ : Unit) (v : Bool),
      frontend.nat_op_ground.nidx_contains_loop ns n (alloc.vec.Vec.len ns) i = ok v →
      v = ((ns.val.drop i.val).map absNIdx).contains (absNIdx n) := by
    refine cursor_induction (fun i : Std.Usize => i.val) ns.val.length
      (fun i _ => ∀ v, frontend.nat_op_ground.nidx_contains_loop ns n
        (alloc.vec.Vec.len ns) i = ok v →
        v = ((ns.val.drop i.val).map absNIdx).contains (absNIdx n)) ?_ ?_
    · intro i _ hn v h
      rw [frontend.nat_op_ground.nidx_contains_loop.eq_def] at h
      rw [if_neg (show ¬ i < alloc.vec.Vec.len ns by scalar_tac)] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le hn]; rfl
    · intro i _ hi ih v h
      rw [frontend.nat_op_ground.nidx_contains_loop.eq_def] at h
      rw [if_pos (show i < alloc.vec.Vec.len ns by scalar_tac)] at h
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hxv : ns.val[i.val]'hi = x := by
        have h1 := vec_index_some hx
        rw [List.getElem?_eq_getElem hi] at h1
        exact Option.some_injective _ h1
      rw [List.drop_eq_getElem_cons hi, hxv, List.map_cons, List.contains_cons,
        show (absNIdx n == absNIdx x) = (absNIdx x == absNIdx n) from by
          rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; exact eq_comm,
        ← nidx_eq2_abs hb]
      split at h
      · rename_i hbt
        cases Result.ok_injective h
        simp [hbt]
      · rename_i hbf
        obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        rw [ih i1 () (ConRon.Refine.Nat.uadd_val hi1) v h, ConRon.Refine.Nat.uadd_val hi1]
        simp [hbf]
  have := key 0#usize () v h
  simpa [absNIdxL] using this

/-! ## The pin readers over `AStateRel₀` (local)

`Refine2/Checker/Pins.lean`'s `pin_at_refines` and `Refine2/Checker/Base.lean`'s
`nat_op_names_refines` / `nat_div_mod_names_refines` read only `hrel.pins`,
but are stated over the deprecated `AStateRel`, and that lane is live.  These
are their lockstep copies (the same proofs, `AStateRel₀`, no `Ext`), for
`is_nat_op_record` below; they go when the Checker lane's migration lands. -/

theorem pin_at_refines₀ {pers st lst} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst)
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

/-- One pin slot, by its index. -/
theorem pin_slot₀ {pers st lst} {i : Std.Usize} {j : Nat} {o}
    (hrel : AStateRel₀ pers st lst) (hij : absSz i = j)
    (hrun : arena.pins.pin_at st i = ok o) : SimRE absNIdx lst o (pinAt j) := by
  have h := pin_at_refines₀ hrel hrun
  rw [hij] at h
  exact h

theorem nat_op_names_refines₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.nat_op_names st = ok o) :
    Sim₀ absNIdxL pers lst o natOpNames := by
  unfold natOpNames
  rw [arena.core.nat_op_names] at hrun
  unfold Sim₀
  obtain ⟨q0, hq0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_pred_name] at hq0
  obtain ⟨r0, hr0, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
  have hS0 := pin_slot₀ (j := Arena.PIN_NAT_PRED) hrel
    (by show (arena.pins.PIN_NAT_PRED).val = _; rw [arena.pins.PIN_NAT_PRED]; rfl)
    (by rw [arena.pins.pin_nat_pred] at hr0; exact hr0)
  obtain rfl := (Result.ok_injective hq0).symm
  cases r0 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natPredName) hS0)
  | Ok a0 =>
  rw [pin_ok (tw := natPredName) hS0]
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_add_name] at hq1
  obtain ⟨r1, hr1, hq1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq1
  have hS1 := pin_slot₀ (j := Arena.PIN_NAT_ADD) hrel
    (by show (arena.pins.PIN_NAT_ADD).val = _; rw [arena.pins.PIN_NAT_ADD]; rfl)
    (by rw [arena.pins.pin_nat_add] at hr1; exact hr1)
  obtain rfl := (Result.ok_injective hq1).symm
  cases r1 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natAddName) hS1)
  | Ok a1 =>
  rw [pin_ok (tw := natAddName) hS1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_sub_name] at hq2
  obtain ⟨r2, hr2, hq2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq2
  have hS2 := pin_slot₀ (j := Arena.PIN_NAT_SUB) hrel
    (by show (arena.pins.PIN_NAT_SUB).val = _; rw [arena.pins.PIN_NAT_SUB]; rfl)
    (by rw [arena.pins.pin_nat_sub] at hr2; exact hr2)
  obtain rfl := (Result.ok_injective hq2).symm
  cases r2 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natSubName) hS2)
  | Ok a2 =>
  rw [pin_ok (tw := natSubName) hS2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_mul_name] at hq3
  obtain ⟨r3, hr3, hq3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq3
  have hS3 := pin_slot₀ (j := Arena.PIN_NAT_MUL) hrel
    (by show (arena.pins.PIN_NAT_MUL).val = _; rw [arena.pins.PIN_NAT_MUL]; rfl)
    (by rw [arena.pins.pin_nat_mul] at hr3; exact hr3)
  obtain rfl := (Result.ok_injective hq3).symm
  cases r3 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natMulName) hS3)
  | Ok a3 =>
  rw [pin_ok (tw := natMulName) hS3]
  obtain ⟨q4, hq4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_pow_name] at hq4
  obtain ⟨r4, hr4, hq4⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq4
  have hS4 := pin_slot₀ (j := Arena.PIN_NAT_POW) hrel
    (by show (arena.pins.PIN_NAT_POW).val = _; rw [arena.pins.PIN_NAT_POW]; rfl)
    (by rw [arena.pins.pin_nat_pow] at hr4; exact hr4)
  obtain rfl := (Result.ok_injective hq4).symm
  cases r4 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natPowName) hS4)
  | Ok a4 =>
  rw [pin_ok (tw := natPowName) hS4]
  obtain ⟨q5, hq5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_beq_name] at hq5
  obtain ⟨r5, hr5, hq5⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq5
  have hS5 := pin_slot₀ (j := Arena.PIN_NAT_BEQ) hrel
    (by show (arena.pins.PIN_NAT_BEQ).val = _; rw [arena.pins.PIN_NAT_BEQ]; rfl)
    (by rw [arena.pins.pin_nat_beq] at hr5; exact hr5)
  obtain rfl := (Result.ok_injective hq5).symm
  cases r5 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natBeqName) hS5)
  | Ok a5 =>
  rw [pin_ok (tw := natBeqName) hS5]
  obtain ⟨q6, hq6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_ble_name] at hq6
  obtain ⟨r6, hr6, hq6⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq6
  have hS6 := pin_slot₀ (j := Arena.PIN_NAT_BLE) hrel
    (by show (arena.pins.PIN_NAT_BLE).val = _; rw [arena.pins.PIN_NAT_BLE]; rfl)
    (by rw [arena.pins.pin_nat_ble] at hr6; exact hr6)
  obtain rfl := (Result.ok_injective hq6).symm
  cases r6 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natBleName) hS6)
  | Ok a6 =>
  rw [pin_ok (tw := natBleName) hS6]
  obtain ⟨w0, hw0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w1, hw1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w2, hw2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w3, hw3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w4, hw4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w5, hw5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w6, hw6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain rfl := (Result.ok_injective hrun).symm
  have hv : w6.val = [a0, a1, a2, a3, a4, a5, a6] := by
    rw [push_nidx_val hw6, push_nidx_val hw5, push_nidx_val hw4, push_nidx_val hw3, push_nidx_val hw2, push_nidx_val hw1, push_nidx_val hw0]
    rfl
  refine ⟨lst, ?_, hrel, hinv⟩
  simp only [absNIdxL, hv, List.map_cons, List.map_nil]
  rfl

theorem nat_div_mod_names_refines₀ {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.nat_div_mod_names st = ok o) :
    Sim₀ absNIdxL pers lst o natDivModNames := by
  unfold natDivModNames
  rw [arena.core.nat_div_mod_names] at hrun
  unfold Sim₀
  obtain ⟨q0, hq0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_div_name] at hq0
  obtain ⟨r0, hr0, hq0⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq0
  have hS0 := pin_slot₀ (j := Arena.PIN_NAT_DIV) hrel
    (by show (arena.pins.PIN_NAT_DIV).val = _; rw [arena.pins.PIN_NAT_DIV]; rfl)
    (by rw [arena.pins.pin_nat_div] at hr0; exact hr0)
  obtain rfl := (Result.ok_injective hq0).symm
  cases r0 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natDivName) hS0)
  | Ok a0 =>
  rw [pin_ok (tw := natDivName) hS0]
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_mod_name] at hq1
  obtain ⟨r1, hr1, hq1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq1
  have hS1 := pin_slot₀ (j := Arena.PIN_NAT_MOD) hrel
    (by show (arena.pins.PIN_NAT_MOD).val = _; rw [arena.pins.PIN_NAT_MOD]; rfl)
    (by rw [arena.pins.pin_nat_mod] at hr1; exact hr1)
  obtain rfl := (Result.ok_injective hq1).symm
  cases r1 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natModName) hS1)
  | Ok a1 =>
  rw [pin_ok (tw := natModName) hS1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_gcd_name] at hq2
  obtain ⟨r2, hr2, hq2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq2
  have hS2 := pin_slot₀ (j := Arena.PIN_NAT_GCD) hrel
    (by show (arena.pins.PIN_NAT_GCD).val = _; rw [arena.pins.PIN_NAT_GCD]; rfl)
    (by rw [arena.pins.pin_nat_gcd] at hr2; exact hr2)
  obtain rfl := (Result.ok_injective hq2).symm
  cases r2 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natGcdName) hS2)
  | Ok a2 =>
  rw [pin_ok (tw := natGcdName) hS2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_land_name] at hq3
  obtain ⟨r3, hr3, hq3⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq3
  have hS3 := pin_slot₀ (j := Arena.PIN_NAT_LAND) hrel
    (by show (arena.pins.PIN_NAT_LAND).val = _; rw [arena.pins.PIN_NAT_LAND]; rfl)
    (by rw [arena.pins.pin_nat_land] at hr3; exact hr3)
  obtain rfl := (Result.ok_injective hq3).symm
  cases r3 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natLandName) hS3)
  | Ok a3 =>
  rw [pin_ok (tw := natLandName) hS3]
  obtain ⟨q4, hq4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_lor_name] at hq4
  obtain ⟨r4, hr4, hq4⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq4
  have hS4 := pin_slot₀ (j := Arena.PIN_NAT_LOR) hrel
    (by show (arena.pins.PIN_NAT_LOR).val = _; rw [arena.pins.PIN_NAT_LOR]; rfl)
    (by rw [arena.pins.pin_nat_lor] at hr4; exact hr4)
  obtain rfl := (Result.ok_injective hq4).symm
  cases r4 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natLorName) hS4)
  | Ok a4 =>
  rw [pin_ok (tw := natLorName) hS4]
  obtain ⟨q5, hq5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_xor_name] at hq5
  obtain ⟨r5, hr5, hq5⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq5
  have hS5 := pin_slot₀ (j := Arena.PIN_NAT_XOR) hrel
    (by show (arena.pins.PIN_NAT_XOR).val = _; rw [arena.pins.PIN_NAT_XOR]; rfl)
    (by rw [arena.pins.pin_nat_xor] at hr5; exact hr5)
  obtain rfl := (Result.ok_injective hq5).symm
  cases r5 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natXorName) hS5)
  | Ok a5 =>
  rw [pin_ok (tw := natXorName) hS5]
  obtain ⟨q6, hq6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_shift_left_name] at hq6
  obtain ⟨r6, hr6, hq6⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq6
  have hS6 := pin_slot₀ (j := Arena.PIN_NAT_SHIFT_LEFT) hrel
    (by show (arena.pins.PIN_NAT_SHIFT_LEFT).val = _; rw [arena.pins.PIN_NAT_SHIFT_LEFT]; rfl)
    (by rw [arena.pins.pin_nat_shift_left] at hr6; exact hr6)
  obtain rfl := (Result.ok_injective hq6).symm
  cases r6 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natShiftLeftName) hS6)
  | Ok a6 =>
  rw [pin_ok (tw := natShiftLeftName) hS6]
  obtain ⟨q7, hq7, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  rw [arena.core.nat_shift_right_name] at hq7
  obtain ⟨r7, hr7, hq7⟩ := ConRon.Refine.bind_eq_ok_iff.mp hq7
  have hS7 := pin_slot₀ (j := Arena.PIN_NAT_SHIFT_RIGHT) hrel
    (by show (arena.pins.PIN_NAT_SHIFT_RIGHT).val = _; rw [arena.pins.PIN_NAT_SHIFT_RIGHT]; rfl)
    (by rw [arena.pins.pin_nat_shift_right] at hr7; exact hr7)
  obtain rfl := (Result.ok_injective hq7).symm
  cases r7 with
  | Err e =>
    have hrun' : (ok (core.result.Result.Err e, st) : Result _) = ok o := hrun
    obtain rfl := (Result.ok_injective hrun').symm
    exact AOut₀.err (pin_err (tw := natShiftRightName) hS7)
  | Ok a7 =>
  rw [pin_ok (tw := natShiftRightName) hS7]
  obtain ⟨w0, hw0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w1, hw1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w2, hw2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w3, hw3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w4, hw4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w5, hw5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w6, hw6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨w7, hw7, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain rfl := (Result.ok_injective hrun).symm
  have hv : w7.val = [a0, a1, a2, a3, a4, a5, a6, a7] := by
    rw [push_nidx_val hw7, push_nidx_val hw6, push_nidx_val hw5, push_nidx_val hw4, push_nidx_val hw3, push_nidx_val hw2, push_nidx_val hw1, push_nidx_val hw0]
    rfl
  refine ⟨lst, ?_, hrel, hinv⟩
  simp only [absNIdxL, hv, List.map_cons, List.map_nil]
  rfl

/-- **`nat_op_ground::is_nat_op_record` refines `isNatOpRecord`**
(`Arena/Frontend/NatOpGround.lean:111-117`). -/
theorem is_nat_op_record_refines {pers rst lst d o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.nat_op_ground.is_nat_op_record rst d = ok o) :
    Sim₀ (Option.map absNIdx) pers lst o
      (isNatOpRecord (absIDeclaration d)) := by
  rw [frontend.nat_op_ground.is_nat_op_record.eq_def] at h
  have hnone : ∀ x : AM (Option NIdx), x = pure none →
      Sim₀ (Option.map absNIdx) pers lst (.Ok none, rst) x := by
    intro x hx; subst hx
    exact ⟨lst, rfl, hrel, hinv⟩
  cases d with
  | DefnDecl cv v hint =>
    dsimp only at h
    obtain ⟨⟨r, st1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hD := nat_div_mod_names_refines₀ hrel hinv h1
    simp only [Sim₀] at hD ⊢
    simp only [absIDeclaration, isNatOpRecord, am_run_bind']
    cases r with
    | Err e =>
      cases Result.ok_injective h
      exact AErrSim.bind hD _
    | Ok dsn =>
      obtain ⟨lst1, hx1, hrel1, hinv1⟩ := hD
      rw [hx1]; simp only [except_ok_bind]
      obtain ⟨⟨r1, st2⟩, h2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hN := nat_op_names_refines₀ hrel1 hinv1 h2
      simp only [Sim₀] at hN
      cases r1 with
      | Err e =>
        cases Result.ok_injective h
        exact AErrSim.bind hN _
      | Ok nsn =>
        obtain ⟨lst2, hx2, hrel2, hinv2⟩ := hN
        rw [hx2]; simp only [except_ok_bind]
        obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hbv := nidx_contains_refines hb
        split at h
        · rename_i hbt
          obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          cases Result.ok_injective h
          have hnv : n = cv.name := dupId_nidx _ _ hn
          subst hnv
          rw [hbt] at hbv
          refine ⟨lst2, ?_, hrel2, hinv2⟩
          simp only [absIConstantVal, ← hbv, Bool.true_or, if_true]; rfl
        · rename_i hbf
          obtain ⟨b1, hb1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hb1v := nidx_contains_refines hb1
          have hbv' : (absNIdxL dsn).contains (absNIdx cv.name) = false := by
            rw [← hbv]; simpa using hbf
          split at h
          · rename_i hb1t
            obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
            cases Result.ok_injective h
            have hnv : n = cv.name := dupId_nidx _ _ hn
            subst hnv
            rw [hb1t] at hb1v
            refine ⟨lst2, ?_, hrel2, hinv2⟩
            simp only [absIConstantVal, hbv', ← hb1v, Bool.false_or, if_true]; rfl
          · rename_i hb1f
            cases Result.ok_injective h
            have hb1v' : (absNIdxL nsn).contains (absNIdx cv.name) = false := by
              rw [← hb1v]; simpa using hb1f
            refine ⟨lst2, ?_, hrel2, hinv2⟩
            simp only [absIConstantVal, hbv', hb1v', Bool.false_or, Bool.false_eq_true,
              if_false]; rfl
  | AxiomDecl _ => cases Result.ok_injective h; exact hnone _ rfl
  | ThmDecl _ _ => cases Result.ok_injective h; exact hnone _ rfl
  | OpaqueDecl _ _ => cases Result.ok_injective h; exact hnone _ rfl
  | BasisDecl _ => cases Result.ok_injective h; exact hnone _ rfl
  | IndDecl _ _ => cases Result.ok_injective h; exact hnone _ rfl
  | QuotDecl _ _ => cases Result.ok_injective h; exact hnone _ rfl

/-! ## The name index -/

/-- **`hoist_name_index` refines `nameIndex ds ∅ 0`**
(`Arena/Frontend/NatOpGround.lean:133-139`), with `insertNames` its inner
loop — the port fuses the two, which is sound because the twin's inner loop
writes only `idx`. -/
theorem hoist_name_index_refines {ds m}
    (h : frontend.nat_op_ground.hoist_name_index ds = ok m) :
    NameIdxRel m (nameIndex (absIDeclArr ds) ∅ 0) := by
  rw [frontend.nat_op_ground.hoist_name_index] at h
  obtain ⟨m0, hm0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i0, -, n0⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.NIdx.Insts.Con_ron_coreRonHashmapHashable) hm0
  have hrel0 : NameIdxRel m0 ∅ := ⟨ConRon.Refine.HashMap2.RelOn_empty n0, i0⟩
  have hsz : ds.val.length < 2 ^ UScalarTy.U64.numBits := by
    have h2 := ds.property
    have h3 : Std.Usize.max < 2 ^ UScalarTy.Usize.numBits := by
      rw [Std.Usize.max_def, Std.Usize.numBits_def]
      have : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
      omega
    have h4 : 2 ^ UScalarTy.Usize.numBits ≤ 2 ^ UScalarTy.U64.numBits := by
      apply Nat.pow_le_pow_right (by decide)
      rw [UScalarTy.Usize_numBits_eq, UScalarTy.U64_numBits_eq]
      cases System.Platform.numBits_eq with
      | inl h => rw [h]; decide
      | inr h => rw [h]
    omega
  -- the inner loop: one record's names
  have hin : ∀ (i : Std.Usize) (ns : alloc.vec.Vec arena.handle.NIdx), i.val < ds.val.length →
      ∀ (j : Std.Usize) (idx : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64) lidx o,
      NameIdxRel idx lidx →
      frontend.nat_op_ground.hoist_name_index_loop0_loop0 idx i ns (alloc.vec.Vec.len ns) j
        = ok o →
      NameIdxRel o (insertNames lidx i.val ((ns.val.drop j.val).map absNIdx)) := by
    intro i ns hi
    refine cursor_induction (fun j : Std.Usize => j.val) ns.val.length
      (fun j (idx : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64) => ∀ lidx o,
        NameIdxRel idx lidx →
        frontend.nat_op_ground.hoist_name_index_loop0_loop0 idx i ns (alloc.vec.Vec.len ns) j
          = ok o →
        NameIdxRel o (insertNames lidx i.val ((ns.val.drop j.val).map absNIdx))) ?_ ?_
    · intro j idx hn lidx o hr h
      rw [frontend.nat_op_ground.hoist_name_index_loop0_loop0.eq_def] at h
      rw [if_neg (show ¬ j < alloc.vec.Vec.len ns by scalar_tac)] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le hn]; exact hr
    · intro j idx hj ih lidx o hr h
      rw [frontend.nat_op_ground.hoist_name_index_loop0_loop0.eq_def] at h
      rw [if_pos (show j < alloc.vec.Vec.len ns by scalar_tac)] at h
      obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨idx1, hidx1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨j1, hj1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hj1v : j1.val = j.val + 1 := by
        have := ConRon.Refine.Nat.uadd_val hj1; simpa using this
      have hnv : ns.val[j.val]'hj = n := by
        have h1 := vec_index_some hn
        rw [List.getElem?_eq_getElem hj] at h1
        exact Option.some_injective _ h1
      have hbv : b = lidx.contains (absNIdx n) := by
        rw [ConRon.Refine.HashMap2.contains_key_refines_wf nidx_eq2 hr.2 (anyNKeysOk _)
          trivial hb, Std.HashMap.contains_eq_isSome_getElem?, ← hr.1 n trivial]
        cases toFun idx n <;> rfl
      rw [List.drop_eq_getElem_cons hj, hnv, List.map_cons, insertNames]
      have hrec : NameIdxRel idx1 (if lidx.contains (absNIdx n) then lidx
          else lidx.insert (absNIdx n) i.val) := by
        split at hidx1
        · rename_i hbt
          cases Result.ok_injective hidx1
          rw [← hbv, hbt, if_pos rfl]; exact hr
        · rename_i hbf
          obtain ⟨n1, hn1, hidx1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hidx1
          obtain ⟨i1, hi1, hidx1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hidx1
          obtain ⟨⟨old, idx2⟩, hins, hidx1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hidx1
          cases Result.ok_injective hidx1
          have hn1v : n1 = n := dupId_nidx _ _ hn1
          subst hn1v
          have hi1v : i1.val = i.val := by
            simp only [lift, Result.ok.injEq] at hi1; subst hi1; exact usize_cast_u64_val' i
          have hbf' : lidx.contains (absNIdx n1) = false := by rw [← hbv]; simpa using hbf
          rw [hbf', if_neg (by simp)]
          obtain ⟨hR, -⟩ := ConRon.Refine.HashMap2.Rel_insert_wf nidx_eq2
            (fun a b _ _ e => absNIdx_inj e) hr.2 (anyNKeysOk _) hr.1 trivial hins
          obtain ⟨hI, -⟩ := ConRon.Refine.HashMap2.insert_refines_gen nidx_eq2 hr.2
            (anyNKeysOk _) trivial hins
          refine ⟨?_, hI⟩
          have : absU i1 = i.val := hi1v
          rw [← this]; exact hR
      have := ih j1 idx1 hj1v _ o hrec h
      rwa [hj1v] at this
  -- the outer loop: record by record
  have hout : ∀ (i : Std.Usize) (idx : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64) lidx o,
      NameIdxRel idx lidx →
      frontend.nat_op_ground.hoist_name_index_loop0 ds idx (alloc.vec.Vec.len ds) i = ok o →
      NameIdxRel o (nameIndex (absIDeclArr ds) lidx i.val) := by
    refine cursor_induction (fun i : Std.Usize => i.val) ds.val.length
      (fun i (idx : ron.hashmap2.HashMap2 arena.handle.NIdx Std.U64) => ∀ lidx o,
        NameIdxRel idx lidx →
        frontend.nat_op_ground.hoist_name_index_loop0 ds idx (alloc.vec.Vec.len ds) i = ok o →
        NameIdxRel o (nameIndex (absIDeclArr ds) lidx i.val)) ?_ ?_
    · intro i idx hn lidx o hr h
      rw [frontend.nat_op_ground.hoist_name_index_loop0.eq_def] at h
      rw [if_neg (show ¬ i < alloc.vec.Vec.len ds by scalar_tac)] at h
      cases Result.ok_injective h
      rw [nameIndex, dif_neg (by simp [absIDeclArr]; omega)]; exact hr
    · intro i idx hi ih lidx o hr h
      rw [frontend.nat_op_ground.hoist_name_index_loop0.eq_def] at h
      rw [if_pos (show i < alloc.vec.Vec.len ds by scalar_tac)] at h
      obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨ns, hns, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨idx1, hidx1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v : i2.val = i.val + 1 := by
        have := ConRon.Refine.Nat.uadd_val hi2; simpa using this
      have hdv : ds.val[i.val]'hi = d := by
        have h1 := vec_index_some hd
        rw [List.getElem?_eq_getElem hi] at h1
        exact Option.some_injective _ h1
      have hI := hin i ns hi 0#usize idx lidx idx1 hr hidx1
      have hlt : i.val < (absIDeclArr ds).size := by simpa [absIDeclArr] using hi
      rw [nameIndex, dif_pos hlt]
      have hnames : (absIDeclArr ds)[i.val].names = ns.val.map absNIdx := by
        rw [i_declaration_names_abs hns, ← hdv]; simp [absIDeclArr]
      rw [hnames]
      have := ih i2 idx1 hi2v _ o (by simpa using hI) h
      rwa [hi2v] at this
  exact hout 0#usize m0 ∅ m hrel0 h

/-- **`idx_get`** — the name index probe. -/
theorem idx_get_refines {rm lm n o} (hr : NameIdxRel rm lm)
    (h : frontend.nat_op_ground.idx_get rm n = ok o) :
    o.map absU = lm[absNIdx n]? := by
  rw [frontend.nat_op_ground.idx_get] at h
  obtain ⟨r, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hr' := nidx_get hr.2 hp
  rw [← hr.1 n trivial, ← hr']
  cases r <;> simp only [Result.ok.injEq] at h <;> rw [← h]

/-! ## The worklist

`hoist_close` is the twin's `hoistClosure` and `hoist_push_deps` its
`pushDeps`/`pushOne` pair; `stack_push_u64` is the port's explicit stack push,
which the twin writes as a `::`.  The port's `while` is unfuelled; the twin's
fuel counts marked records (`ds.size`, sufficient by `hoistClosure_fuel_succ`),
so the refinement is an induction on the port's loop with `hoistPending ≤
fuel` as the invariant (module note, item 3). -/

/-- **`target_done`** — *"record `k` already precedes `i`"*. -/
theorem target_done_refines {rm lm k i v} (hr : TargetRel rm lm)
    (h : frontend.nat_op_ground.target_done rm k i = ok v) :
    v = (match lm[absU k]? with | some t => decide (t ≤ absU i) | none => false) := by
  rw [frontend.nat_op_ground.target_done] at h
  obtain ⟨r, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← target_get hr hp]
  cases r with
  | none => simp only [Result.ok.injEq] at h; simp [← h]
  | some t =>
    simp only [Result.ok.injEq] at h
    rw [← h]
    simp only [Option.map_some, absU]
    rfl

/-- The port's explicit stack as the twin's list: the prefix below the stack
POINTER `sp` (the `Vec` is grown once and reused), **top first** — the port
pushes at `sp`, the END of the prefix, where the twin conses at the HEAD, so
the prefix is read reversed (task #97-P5-Front round 2, finding F6: the
statements read it unreversed, which is false as soon as the stack holds two
entries). -/
def absStack (stack : alloc.vec.Vec Std.U64) (sp : Std.Usize) : List Nat :=
  ((stack.val.take sp.val).map absU).reverse

/-- **`stack_push_u64`** — the explicit stack, against the twin's `::`. -/
theorem stack_push_u64_refines {stack sp x o}
    (h : frontend.nat_op_ground.stack_push_u64 stack sp x = ok o) :
    absStack o.1 o.2 = absU x :: absStack stack sp := by
  rw [frontend.nat_op_ground.stack_push_u64] at h
  obtain ⟨st1, hs1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  have hi1v : i1.val = sp.val + 1 := ConRon.Refine.Nat.uadd_val hi1
  have hst : st1.val.take (sp.val + 1) = stack.val.take sp.val ++ [x] := by
    split at hs1
    · rename_i hlt
      have hltv : sp.val < stack.val.length := by scalar_tac
      obtain ⟨p, hp, hs1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hs1
      obtain ⟨_, back⟩ := p
      cases Result.ok_injective hs1
      obtain ⟨-, -, hback⟩ := ConRon.Refine.HashMap.vec_index_mut_eq hp
      subst hback
      rw [alloc.vec.Vec.set_val_eq, List.take_add_one, List.take_set_of_le (le_refl _),
        List.getElem?_set_self hltv]
      rfl
    · rename_i hge
      have hgev : stack.val.length ≤ sp.val := by scalar_tac
      rw [ConRon.Refine.vec_push_val hs1, List.take_of_length_le (by simp; omega),
        List.take_of_length_le hgev]
  simp only [absStack, hi1v, hst, List.map_append, List.reverse_append]
  rfl

/-- **`hoist_push_deps` refines `hoistClosure.pushDeps`** followed by
`pushOne`: record `k`'s own dependencies that lie after `i`. -/
theorem hoist_push_deps_refines {rm lm used stack sp i k o}
    (hr : NameIdxRel rm lm)
    (h : frontend.nat_op_ground.hoist_push_deps rm used stack sp i k = ok o) :
    absStack o.1 o.2 =
      hoistClosure.pushOne lm (absU i) (absU k) (absNIdxL used) (absStack stack sp) := by
  rw [frontend.nat_op_ground.hoist_push_deps] at h
  have key : ∀ (u : Std.Usize) (q : alloc.vec.Vec Std.U64 × Std.Usize) o,
      frontend.nat_op_ground.hoist_push_deps_loop rm used i k q.1 q.2
        (alloc.vec.Vec.len used) u = ok o →
      absStack o.1 o.2 = hoistClosure.pushOne lm (absU i) (absU k)
        ((used.val.drop u.val).map absNIdx) (absStack q.1 q.2) := by
    refine cursor_induction (fun u : Std.Usize => u.val) used.val.length
      (fun u (q : alloc.vec.Vec Std.U64 × Std.Usize) => ∀ o, frontend.nat_op_ground.hoist_push_deps_loop rm used i k q.1 q.2
        (alloc.vec.Vec.len used) u = ok o →
        absStack o.1 o.2 = hoistClosure.pushOne lm (absU i) (absU k)
          ((used.val.drop u.val).map absNIdx) (absStack q.1 q.2)) ?_ ?_
    · intro u q hn o h
      rw [frontend.nat_op_ground.hoist_push_deps_loop.eq_def] at h
      rw [if_neg (show ¬ u < alloc.vec.Vec.len used by scalar_tac)] at h
      cases Result.ok_injective h
      rw [List.drop_eq_nil_of_le hn]; rfl
    · intro u q hu ih o h
      rw [frontend.nat_op_ground.hoist_push_deps_loop.eq_def] at h
      rw [if_pos (show u < alloc.vec.Vec.len used by scalar_tac)] at h
      obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨og, hog, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨⟨st1, sp1⟩, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨u1, hu1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hu1v : u1.val = u.val + 1 := by
        have := ConRon.Refine.Nat.uadd_val hu1; simpa using this
      have hxv : used.val[u.val]'hu = x := by
        have h1 := vec_index_some hx
        rw [List.getElem?_eq_getElem hu] at h1
        exact Option.some_injective _ h1
      have hg := idx_get_refines hr hog
      rw [ih u1 (st1, sp1) hu1v o h, hu1v, List.drop_eq_getElem_cons hu, hxv,
        List.map_cons]
      cases og with
      | none =>
        cases Result.ok_injective hm
        simp only [Option.map_none] at hg
        simp only [hoistClosure.pushOne, ← hg]
      | some m =>
        simp only [Option.map_some] at hg
        simp only [hoistClosure.pushOne, ← hg]
        replace hm : (if m > i then (if (m != k) = true then
            frontend.nat_op_ground.stack_push_u64 q.1 q.2 m else ok (q.1, q.2))
            else ok (q.1, q.2)) = ok (st1, sp1) := hm
        by_cases hmi : m > i
        · have hmi' : absU m > absU i := by simp only [absU]; scalar_tac
          rw [if_pos hmi] at hm
          by_cases hmk : m = k
          · subst hmk
            simp only [bne_self_eq_false, Bool.false_eq_true, if_false] at hm
            cases Result.ok_injective hm
            simp
          · have hmk' : (m != k) = true := by simpa using hmk
            rw [if_pos hmk'] at hm
            have hpush := stack_push_u64_refines hm
            have hmk'' : (absU m != absU k) = true := by
              simp only [absU, bne_iff_ne, ne_eq]
              intro e; apply hmk; exact UScalar.eq_of_val_eq e
            simp only [hpush, hmi', hmk'', decide_true, Bool.and_self, if_true]
        · have hmi' : ¬ absU m > absU i := by simp only [absU]; scalar_tac
          rw [if_neg hmi] at hm
          cases Result.ok_injective hm
          simp [hmi']
  have := key 0#usize (stack, sp) o h
  simpa [absNIdxL] using this

/-- The twin's name index holds record positions (a fact about the twin's own
`nameIndex`; `Bridge/Frontend/Prepare.lean`'s `nameIndex_lt`, restated here
because this tier does not import Theorem 1). -/
theorem nameIndex_lt' (ds : Array IDeclaration) :
    ∀ (n k : Nat) (idx : Std.HashMap NIdx Nat), ds.size - k = n →
      (∀ (x : NIdx) m, idx[x]? = some m → m < ds.size) →
      ∀ (x : NIdx) m, (nameIndex ds idx k)[x]? = some m → m < ds.size := by
  have hins : ∀ (i : Nat), i < ds.size → ∀ (ns : List NIdx) (idx : Std.HashMap NIdx Nat),
      (∀ (x : NIdx) m, idx[x]? = some m → m < ds.size) →
      ∀ (x : NIdx) m, (insertNames idx i ns)[x]? = some m → m < ds.size := by
    intro i hi ns
    induction ns with
    | nil => intro idx h; simpa [insertNames] using h
    | cons n ns ih =>
      intro idx h
      rw [insertNames]
      refine ih _ ?_
      split
      · exact h
      · intro x m hm
        rw [Std.HashMap.getElem?_insert] at hm
        split at hm
        · obtain rfl := Option.some.inj hm; exact hi
        · exact h x m hm
  intro n
  induction n with
  | zero =>
    intro k idx hn h
    rw [nameIndex, dif_neg (by omega)]
    exact h
  | succ n ih =>
    intro k idx hn h
    have hk : k < ds.size := by omega
    rw [nameIndex, dif_pos hk]
    exact ih (k + 1) _ (by omega) (hins k hk _ idx h)

/-- The target map across an insert. -/
theorem target_insert_rel {rm lm} (ht : TargetRel rm lm) {k v : Std.U64} {old m'}
    (h : ron.hashmap2.HashMap2.insert U64.Insts.Con_ron_coreRonHashmapHashable
      U64.Insts.Con_ron_coreRonHashmapEq2 rm k v = ok (old, m')) :
    TargetRel m' (lm.insert (absU k) (absU v)) :=
  memo_insert_step u64Eq2Fwd absU_inj_u64 ht.2 ht.1 h

/-- The explicit stack, popped: the top is the prefix's last element. -/
theorem absStack_pop {stack : alloc.vec.Vec Std.U64} {sp sp1 : Std.Usize}
    (hsp1 : sp1.val + 1 = sp.val) (hlt : sp1.val < stack.val.length) :
    absStack stack sp = absU stack.val[sp1.val] :: absStack stack sp1 := by
  have ht : stack.val.take sp.val = stack.val.take sp1.val ++ [stack.val[sp1.val]] := by
    rw [← hsp1, List.take_add_one, List.getElem?_eq_getElem hlt]; rfl
  simp only [absStack, ht, List.map_append, List.map_cons, List.map_nil, List.reverse_append]
  rfl

theorem absStack_zero {stack : alloc.vec.Vec Std.U64} {sp : Std.Usize} (h : sp.val = 0) :
    absStack stack sp = [] := by
  simp [absStack, h]

/-- Some record below `n` not done: the pending count is positive. -/
theorem hoistPending_pos {n : Nat} {target : Std.HashMap Nat Nat} {i k : Nat}
    (hk : k < n) (hnd : hoistDone target k i = false) : 0 < hoistPending n target i := by
  unfold hoistPending
  exact List.countP_pos_iff.mpr ⟨k, List.mem_range.mpr hk, by simp [hnd]⟩

/-- What `hoist_close` claims: its success and error arms against a twin run. -/
def HCOut (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result (ron.hashmap2.HashMap2 Std.U64 Std.U64)
      kernel.core_types.CheckError × arena.monad.AState)
    (x : AM (Std.HashMap Nat Nat)) : Prop :=
  (∀ t, o.1 = .Ok t → ∃ lt lst', x.run lst = .ok (lt, lst') ∧ TargetRel t lt ∧
      AStateRel₀ pers o.2 lst' ∧ AStateInv pers o.2) ∧
    (∀ e, o.1 = .Err e → AErrSim e (x.run lst))

theorem hoist_close_loop_aux {pers : arena.store.PersTier}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {rm lm} {i : Std.U64}
    (hr : NameIdxRel rm lm)
    (hidx : ∀ (x : NIdx) m, lm[x]? = some m → m < ds.val.length) :
    ∀ (n : Nat) (m : Nat) (st : arena.monad.AState) (lst : AState)
      (target : ron.hashmap2.HashMap2 Std.U64 Std.U64) (ltarget : Std.HashMap Nat Nat)
      (stack : alloc.vec.Vec Std.U64) (sp : Std.Usize) (F : Nat) o,
      hoistPending ds.val.length ltarget (absU i) ≤ n → sp.val ≤ m →
      hoistPending ds.val.length ltarget (absU i) ≤ F →
      (∀ x ∈ absStack stack sp, x < ds.val.length) →
      AStateRel₀ pers st lst → AStateInv pers st → TargetRel target ltarget →
      frontend.nat_op_ground.hoist_close_loop pers st ds rm i target stack sp = ok o →
      HCOut pers lst o (hoistClosure (absIDeclArr ds) lm (absU i) F ltarget
        (absStack stack sp)) := by
  have hsize : (absIDeclArr ds).size = ds.val.length := by simp [absIDeclArr]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro m
  induction m with
  | zero =>
    intro st lst target ltarget stack sp F o hpn hsp hpF hsN hrel hinv ht h
    rw [frontend.nat_op_ground.hoist_close_loop, if_neg (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [absStack_zero (by omega), hoistClosure]
    exact ⟨fun t ht' => by cases ht'; exact ⟨ltarget, lst, rfl, ht, hrel, hinv⟩,
      fun e he => by cases he⟩
  | succ m ihm =>
    intro st lst target ltarget stack sp F o hpn hsp hpF hsN hrel hinv ht h
    rw [frontend.nat_op_ground.hoist_close_loop] at h
    split at h
    swap
    · rename_i hsp0
      cases Result.ok_injective h
      rw [absStack_zero (by scalar_tac), hoistClosure]
      exact ⟨fun t ht' => by cases ht'; exact ⟨ltarget, lst, rfl, ht, hrel, hinv⟩,
        fun e he => by cases he⟩
    rename_i hsp0
    obtain ⟨sp1, hsp1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hsp1v : sp1.val + 1 = sp.val := by
      have := (ConRon.Refine.Nat.usub_val hsp1).2; scalar_tac
    obtain ⟨k, hk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hkb, hkv⟩ := ExprOps.vecIndexAt hk
    have hpop := absStack_pop (stack := stack) hsp1v hkb
    rw [hkv] at hpop
    rw [hpop] at hsN ⊢
    have hkN : absU k < ds.val.length := hsN _ List.mem_cons_self
    have hrest : ∀ x ∈ absStack stack sp1, x < ds.val.length :=
      fun x hx => hsN x (List.mem_cons_of_mem _ hx)
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hbv := target_done_refines ht hb
    have hbd : b = hoistDone ltarget (absU k) (absU i) := by
      rw [hbv]; rfl
    split at h
    · -- the record is already done: a pop the twin's `hoistDropDone` takes
      rename_i hbt
      have hdone : hoistDone ltarget (absU k) (absU i) = true := by rw [← hbd]; exact hbt
      have heq : hoistClosure (absIDeclArr ds) lm (absU i) F ltarget (absU k :: absStack stack sp1)
          = hoistClosure (absIDeclArr ds) lm (absU i) F ltarget (absStack stack sp1) := by
        conv => lhs; rw [hoistClosure]
        conv => rhs; rw [hoistClosure]
        simp only [hoistDropDone, hdone, if_true]
      rw [heq]
      exact ihm st lst target ltarget stack sp1 F o hpn (by omega) hpF hrest hrel hinv ht h
    · rename_i hbt
      have hnd : hoistDone ltarget (absU k) (absU i) = false := by
        rw [← hbd]; simpa using hbt
      have hpos := hoistPending_pos hkN hnd
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      obtain ⟨⟨old, target1⟩, hins, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have ht1 := target_insert_rel ht hins
      obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi1v : i1.val = k.val := by
        simp only [lift, Result.ok.injEq] at hi1
        subst hi1
        rw [UScalar.cast_val_eq]
        apply Nat.mod_eq_of_lt
        have h2 := ds.property
        have h3 : Std.Usize.max < 2 ^ UScalarTy.Usize.numBits := by
          rw [Std.Usize.max_def, Std.Usize.numBits_def]
          have : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
          omega
        have : k.val < ds.val.length := hkN
        omega
      have hkN' : i1.val < ds.val.length := by rw [hi1v]; exact hkN
      rw [vec_index_ok_eq ds i1 hkN', bind_tc_ok] at h
      obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hda := i_declaration_dup_abs hd
      obtain ⟨⟨r, st1⟩, hr1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hU := decl_used_consts_refines hrel hinv hr1
      rw [hda] at hU
      have hki : absU k = i1.val := hi1v.symm
      have hdsk : (absIDeclArr ds)[absU k]'(by rw [hsize]; exact hkN)
          = absIDeclaration ds.val[i1.val] := by
        simp only [absIDeclArr, List.getElem_toArray, List.getElem_map, hki]
      -- the twin's step
      have htw : hoistClosure (absIDeclArr ds) lm (absU i) (F' + 1) ltarget
          (absU k :: absStack stack sp1) = (do
            let ns ← IDeclaration.usedConsts (absIDeclaration ds.val[i1.val])
            hoistClosure (absIDeclArr ds) lm (absU i) F' (ltarget.insert (absU k) (absU i))
              (hoistClosure.pushOne lm (absU i) (absU k) ns.toList (absStack stack sp1))) := by
        rw [hoistClosure]
        simp only [hoistDropDone, hnd, Bool.false_eq_true, if_false]
        simp only [hoistClosure.pushDeps, dif_pos (show absU k < (absIDeclArr ds).size by
          rw [hsize]; exact hkN), hdsk, bind_assoc, pure_bind]
      rw [htw]
      unfold Sim₀ at hU
      constructor
      · intro t ht'
        cases r with
        | Err e => cases Result.ok_injective h; cases ht'
        | Ok used =>
          obtain ⟨lst1, hx1, hrel1, hinv1⟩ := hU
          obtain ⟨⟨stack1, sp2⟩, hpd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hpush := hoist_push_deps_refines hr hpd
          have hpend : hoistPending ds.val.length (ltarget.insert (absU k) (absU i)) (absU i)
              < hoistPending ds.val.length ltarget (absU i) := hoistPending_insert hkN hnd
          have hN2 : ∀ x ∈ absStack stack1 sp2, x < ds.val.length := by
            rw [hpush]
            have := hoistClosure_pushOne_lt (ds := absIDeclArr ds) (idx := lm) (i := absU i)
              (fun x m hm => by rw [hsize]; exact hidx x m hm) (absU k) (absNIdxL used)
              (absStack stack sp1) (fun x hx => by rw [hsize]; exact hrest x hx)
            intro x hx
            have := this x hx
            rwa [hsize] at this
          have IH := ihn _ (by omega) _ st1 lst1 target1 _ stack1 sp2 F' o
            le_rfl le_rfl (by omega) hN2 hrel1 hinv1 ht1 h
          rw [hpush] at IH
          rw [am_run_bind', hx1, except_ok_bind]
          have e1 : (absNIdxArr used).toList = absNIdxL used := by simp [absNIdxArr, absNIdxL]
          rw [e1]
          exact IH.1 t ht'
      · intro e he
        cases r with
        | Err e' =>
          cases Result.ok_injective h
          cases he
          rw [am_run_bind']
          exact AErrSim.bind hU _
        | Ok used =>
          obtain ⟨lst1, hx1, hrel1, hinv1⟩ := hU
          obtain ⟨⟨stack1, sp2⟩, hpd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hpush := hoist_push_deps_refines hr hpd
          have hpend : hoistPending ds.val.length (ltarget.insert (absU k) (absU i)) (absU i)
              < hoistPending ds.val.length ltarget (absU i) := hoistPending_insert hkN hnd
          have hN2 : ∀ x ∈ absStack stack1 sp2, x < ds.val.length := by
            rw [hpush]
            have := hoistClosure_pushOne_lt (ds := absIDeclArr ds) (idx := lm) (i := absU i)
              (fun x m hm => by rw [hsize]; exact hidx x m hm) (absU k) (absNIdxL used)
              (absStack stack sp1) (fun x hx => by rw [hsize]; exact hrest x hx)
            intro x hx
            have := this x hx
            rwa [hsize] at this
          have IH := ihn _ (by omega) _ st1 lst1 target1 _ stack1 sp2 F' o
            le_rfl le_rfl (by omega) hN2 hrel1 hinv1 ht1 h
          rw [hpush] at IH
          rw [am_run_bind', hx1, except_ok_bind]
          have e1 : (absNIdxArr used).toList = absNIdxL used := by simp [absNIdxArr, absNIdxL]
          rw [e1]
          exact IH.2 e he

/-- **`hoist_close` refines `hoistClosure`**
(`Arena/Frontend/NatOpGround.lean:171-199`), at the caller's fuel
`ds.size`: the name index holds record positions and the seed is one. -/
theorem hoist_close_refines {pers rst lst ds rm lm target ltarget j i o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hr : NameIdxRel rm lm) (ht : TargetRel target ltarget)
    (hidx : ∀ (x : NIdx) m, lm[x]? = some m → m < ds.val.length)
    (hj : absU j < ds.val.length)
    (h : frontend.nat_op_ground.hoist_close pers rst ds rm target j i = ok o) :
    HCOut pers lst o (hoistClosure (absIDeclArr ds) lm (absU i)
        (absIDeclArr ds).size ltarget [absU j]) := by
  rw [frontend.nat_op_ground.hoist_close] at h
  obtain ⟨stack, hstack, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hsv : stack.val = [j] := ConRon.Refine.push_new_val hstack
  have habs : absStack stack 1#usize = [absU j] := by simp [absStack, hsv]
  have hsize : (absIDeclArr ds).size = ds.val.length := by simp [absIDeclArr]
  have := hoist_close_loop_aux (i := i) hr hidx _ _ rst lst target ltarget stack 1#usize
    (absIDeclArr ds).size o le_rfl le_rfl
    (by rw [hsize]; unfold hoistPending; exact List.countP_le_length.trans (by simp))
    (by rw [habs]; intro x hx; simp at hx; subst hx; exact hj) hrel hinv ht h
  rwa [habs] at this

/-- The `for g in deps` loop of `hoist_targets_at` against `hoistDeps` on the
suffix of the dependency list from `k`. -/
theorem hoist_targets_at_loop_aux {pers : arena.store.PersTier}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {rm lm} {i : Std.U64}
    {gs : alloc.vec.Vec arena.handle.NIdx}
    (hr : NameIdxRel rm lm)
    (hidx : ∀ (x : NIdx) m, lm[x]? = some m → m < ds.val.length) :
    ∀ (n : Nat) (k : Std.Usize) (st : arena.monad.AState) (lst : AState)
      (target : ron.hashmap2.HashMap2 Std.U64 Std.U64) (ltarget : Std.HashMap Nat Nat) o,
      gs.val.length - k.val = n → k.val ≤ gs.val.length →
      AStateRel₀ pers st lst → AStateInv pers st → TargetRel target ltarget →
      frontend.nat_op_ground.hoist_targets_at_loop pers st ds rm i target gs
        (alloc.vec.Vec.len gs) k = ok o →
      HCOut pers lst o (hoistTargetsGo.hoistDeps (absIDeclArr ds) lm ltarget (absU i)
        ((absNIdxL gs).drop k.val)) := by
  intro n
  induction n with
  | zero =>
    intro k st lst target ltarget o hn hk hrel hinv ht h
    rw [frontend.nat_op_ground.hoist_targets_at_loop, if_neg (by scalar_tac)] at h
    cases Result.ok_injective h
    have hnil : (absNIdxL gs).drop k.val = [] := by
      simp only [absNIdxL, List.drop_eq_nil_iff, List.length_map]; omega
    rw [hnil, hoistTargetsGo.hoistDeps]
    exact ⟨fun t ht' => by cases ht'; exact ⟨ltarget, lst, rfl, ht, hrel, hinv⟩,
      fun e he => by cases he⟩
  | succ n ih =>
    intro k st lst target ltarget o hn hk hrel hinv ht h
    rw [frontend.nat_op_ground.hoist_targets_at_loop, if_pos (by scalar_tac)] at h
    obtain ⟨g, hg, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hgb, hgv⟩ := ExprOps.vecIndexAt hg
    have hdrop : (absNIdxL gs).drop k.val = absNIdx g :: (absNIdxL gs).drop (k.val + 1) := by
      rw [← hgv]
      simp only [absNIdxL]
      rw [List.drop_eq_getElem_cons (by simpa using hgb)]
      simp
    rw [hdrop, hoistTargetsGo.hoistDeps]
    obtain ⟨og, hog, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hgl := idx_get_refines hr hog
    cases og with
    | none =>
      have hlm : lm[absNIdx g]? = none := by rw [← hgl]; rfl
      simp only [hlm]
      obtain ⟨k1, hk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hk1v : k1.val = k.val + 1 := by have := ConRon.Refine.Nat.uadd_val hk1; simpa using this
      have IH := ih k1 st lst target ltarget o (by omega) (by omega) hrel hinv ht h
      rwa [hk1v] at IH
    | some j =>
      have hlm : lm[absNIdx g]? = some (absU j) := by rw [← hgl]; rfl
      simp only [hlm]
      simp only at h
      split at h
      · rename_i hji
        rw [if_pos (show absU j > absU i by show j.val > i.val; scalar_tac)]
        obtain ⟨⟨r, st1⟩, hc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have HC := hoist_close_refines hrel hinv hr ht hidx (hidx _ _ hlm) hc
        cases r with
        | Err e =>
          cases Result.ok_injective h
          refine ⟨fun t ht' => (by cases ht'), fun e' he => ?_⟩
          cases he
          rw [am_run_bind']
          exact AErrSim.bind (HC.2 e rfl) _
        | Ok t =>
          obtain ⟨lt, lst1, hx, ht1, hrel1, hinv1⟩ := HC.1 t rfl
          obtain ⟨k1, hk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hk1v : k1.val = k.val + 1 := by have := ConRon.Refine.Nat.uadd_val hk1; simpa using this
          have IH := ih k1 st1 lst1 t lt o (by omega) (by omega) hrel1 hinv1 ht1 h
          rw [hk1v] at IH
          unfold HCOut
          rw [am_run_bind', hx, except_ok_bind]
          exact IH
      · rename_i hji
        rw [if_neg (show ¬ absU j > absU i by show ¬ j.val > i.val; scalar_tac)]
        obtain ⟨k1, hk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hk1v : k1.val = k.val + 1 := by have := ConRon.Refine.Nat.uadd_val hk1; simpa using this
        have IH := ih k1 st lst target ltarget o (by omega) (by omega) hrel hinv ht h
        rwa [hk1v] at IH

/-- **`hoist_targets_at` refines `hoistTargetsGo.hoistDeps`** at one pinned
operation's `natOpDeps`.  Round 3 restated it in the `HCOut` shape of
`hoist_close_refines`, with that lemma's index bound `hidx`. -/
theorem hoist_targets_at_refines {pers rst lst ds rm lm target ltarget c i o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (hr : NameIdxRel rm lm) (ht : TargetRel target ltarget)
    (hidx : ∀ (x : NIdx) m, lm[x]? = some m → m < ds.val.length)
    (h : frontend.nat_op_ground.hoist_targets_at pers rst ds rm target c i = ok o) :
    HCOut pers lst o (do
        let deps ← natOpDeps (absNIdx c)
        hoistTargetsGo.hoistDeps (absIDeclArr ds) lm ltarget (absU i) deps) := by
  rw [frontend.nat_op_ground.hoist_targets_at] at h
  obtain ⟨⟨r, st1⟩, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have HD := nat_op_deps_ls hrel hinv c r st1 hd
  cases r with
  | Err e =>
    cases Result.ok_injective h
    refine ⟨fun t ht' => (by cases ht'), fun e' he => ?_⟩
    cases he
    rw [am_run_bind']
    exact AErrSim.bind HD _
  | Ok v =>
    obtain ⟨b, lst1, hx, rfl, hrel1, hinv1⟩ := HD
    have IH := hoist_targets_at_loop_aux (gs := v) (i := i) hr hidx _ 0#usize st1 lst1
      target ltarget o rfl (by simp) hrel1 hinv1 ht h
    unfold HCOut
    rw [am_run_bind', hx, except_ok_bind]
    exact IH

/-! ### The twin's target map stays within the stream

`hoist_targets_refines` promises its caller that every key and every value of
the twin's map is a record index.  That is a fact about the twin alone (it
inserts stack entries, which are name-index values, at loop indices), proved
here on the twin's runs. -/

/-- Every key and value of a target map is below `N`. -/
def TargetBound (N : Nat) (t : Std.HashMap Nat Nat) : Prop :=
  ∀ k tk, t[k]? = some tk → k < N ∧ tk < N

theorem targetBound_insert {N : Nat} {t : Std.HashMap Nat Nat} {k i : Nat}
    (h : TargetBound N t) (hk : k < N) (hi : i < N) : TargetBound N (t.insert k i) := by
  intro x tx hx
  rw [Std.HashMap.getElem?_insert] at hx
  by_cases hkx : k = x
  · subst hkx
    simp only [BEq.rfl, if_true, Option.some.injEq] at hx
    subst hx
    exact ⟨hk, hi⟩
  · have : (k == x) = false := by simpa using hkx
    rw [this] at hx
    exact h x tx hx

theorem hoistDropDone_mem {t : Std.HashMap Nat Nat} {i : Nat} :
    ∀ (L : List Nat) (x : Nat), x ∈ hoistDropDone t i L → x ∈ L
  | [], x, h => by simp [hoistDropDone] at h
  | k :: L, x, h => by
    unfold hoistDropDone at h
    split at h
    · exact List.mem_cons_of_mem _ (hoistDropDone_mem L x h)
    · exact h

private theorem am_pure_run_ok {α : Type} {a b : α} {s s' : AState}
    (h : (pure a : AM α).run s = .ok (b, s')) : a = b ∧ s = s' := by
  have h' : (Except.ok (a, s) : Except Arena.CheckError (α × AState)) = .ok (b, s') := h
  cases h'
  exact ⟨rfl, rfl⟩

private theorem am_fail_run_ok {α : Type} {e : Arena.CheckError} {b : α} {s s' : AState}
    (h : (Arena.fail e : AM α).run s = .ok (b, s')) : False := by
  have h' : (Except.error e : Except Arena.CheckError (α × AState)) = .ok (b, s') := h
  cases h'

theorem hoistClosure_bound {ds : Array IDeclaration} {idx : Std.HashMap NIdx Nat} {i : Nat}
    (hidx : ∀ (n : NIdx) m, idx[n]? = some m → m < ds.size) (hi : i < ds.size) :
    ∀ (fuel : Nat) (target : Std.HashMap Nat Nat) (L : List Nat) (s : AState)
      (t' : Std.HashMap Nat Nat) (s' : AState),
      TargetBound ds.size target → (∀ x ∈ L, x < ds.size) →
      (hoistClosure ds idx i fuel target L).run s = .ok (t', s') →
      TargetBound ds.size t' := by
  intro fuel
  induction fuel with
  | zero =>
    intro target L s t' s' ht hL h
    rw [hoistClosure] at h
    split at h
    · obtain ⟨rfl, -⟩ := am_pure_run_ok h; exact ht
    · exact (am_fail_run_ok h).elim
  | succ fuel ih =>
    intro target L s t' s' ht hL h
    rw [hoistClosure] at h
    split at h
    · obtain ⟨rfl, -⟩ := am_pure_run_ok h; exact ht
    · rename_i k rest hd
      have hkr : ∀ x ∈ k :: rest, x < ds.size :=
        fun x hx => hL x (hoistDropDone_mem L x (hd ▸ hx))
      obtain ⟨st, s1, hp, h⟩ := am_run_bind_ok h
      have hst : ∀ x ∈ st, x < ds.size := by
        unfold hoistClosure.pushDeps at hp
        split at hp
        · obtain ⟨ns, s2, -, hp⟩ := am_run_bind_ok hp
          obtain ⟨rfl, -⟩ := am_pure_run_ok hp
          exact hoistClosure_pushOne_lt hidx k _ rest
            (fun x hx => hkr x (List.mem_cons_of_mem _ hx))
        · obtain ⟨rfl, -⟩ := am_pure_run_ok hp
          exact fun x hx => hkr x (List.mem_cons_of_mem _ hx)
      exact ih _ _ _ _ _ (targetBound_insert ht (hkr k List.mem_cons_self) hi) hst h

theorem hoistDeps_bound {ds : Array IDeclaration} {idx : Std.HashMap NIdx Nat} {i : Nat}
    (hidx : ∀ (n : NIdx) m, idx[n]? = some m → m < ds.size) (hi : i < ds.size) :
    ∀ (deps : List NIdx) (target : Std.HashMap Nat Nat) (s : AState)
      (t' : Std.HashMap Nat Nat) (s' : AState),
      TargetBound ds.size target →
      (hoistTargetsGo.hoistDeps ds idx target i deps).run s = .ok (t', s') →
      TargetBound ds.size t' := by
  intro deps
  induction deps with
  | nil =>
    intro target s t' s' ht h
    rw [hoistTargetsGo.hoistDeps] at h
    obtain ⟨rfl, -⟩ := am_pure_run_ok h; exact ht
  | cons g gs ih =>
    intro target s t' s' ht h
    rw [hoistTargetsGo.hoistDeps] at h
    split at h
    · rename_i j hj
      split at h
      · obtain ⟨t1, s1, h1, h⟩ := am_run_bind_ok h
        have hb := hoistClosure_bound hidx hi _ _ _ _ _ _ ht
          (by intro x hx; simp at hx; subst hx; exact hidx _ _ hj) h1
        exact ih _ _ _ _ hb h
      · exact ih _ _ _ _ ht h
    · exact ih _ _ _ _ ht h

theorem hoistTargetsGo_bound {ds : Array IDeclaration} {idx : Std.HashMap NIdx Nat}
    (hidx : ∀ (n : NIdx) m, idx[n]? = some m → m < ds.size) :
    ∀ (n i : Nat) (target : Std.HashMap Nat Nat) (s : AState)
      (t' : Std.HashMap Nat Nat) (s' : AState),
      ds.size - i = n → TargetBound ds.size target →
      (hoistTargetsGo ds idx target i).run s = .ok (t', s') →
      TargetBound ds.size t' := by
  intro n
  induction n with
  | zero =>
    intro i target s t' s' hn ht h
    rw [hoistTargetsGo, dif_neg (by omega)] at h
    obtain ⟨rfl, -⟩ := am_pure_run_ok h; exact ht
  | succ n ih =>
    intro i target s t' s' hn ht h
    rw [hoistTargetsGo, dif_pos (by omega)] at h
    obtain ⟨r, s1, -, h⟩ := am_run_bind_ok h
    split at h
    · exact ih (i + 1) _ _ _ _ (by omega) ht h
    · obtain ⟨deps, s2, -, h⟩ := am_run_bind_ok h
      obtain ⟨t2, s3, h2, h⟩ := am_run_bind_ok h
      exact ih (i + 1) _ _ _ _ (by omega)
        (hoistDeps_bound hidx (by omega) _ _ _ _ _ ht h2) h

/-- The outer `for i in 0..n` loop of `hoist_targets` against `hoistTargetsGo`
from `i`. -/
theorem hoist_targets_loop_aux {pers : arena.store.PersTier}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {rm lm}
    (hr : NameIdxRel rm lm)
    (hidx : ∀ (x : NIdx) m, lm[x]? = some m → m < ds.val.length) :
    ∀ (n : Nat) (i : Std.Usize) (st : arena.monad.AState) (lst : AState)
      (target : ron.hashmap2.HashMap2 Std.U64 Std.U64) (ltarget : Std.HashMap Nat Nat) o,
      ds.val.length - i.val = n → i.val ≤ ds.val.length →
      AStateRel₀ pers st lst → AStateInv pers st → TargetRel target ltarget →
      frontend.nat_op_ground.hoist_targets_loop pers st ds rm target
        (alloc.vec.Vec.len ds) i = ok o →
      HCOut pers lst o (hoistTargetsGo (absIDeclArr ds) lm ltarget i.val) := by
  have hsize : (absIDeclArr ds).size = ds.val.length := by simp [absIDeclArr]
  intro n
  induction n with
  | zero =>
    intro i st lst target ltarget o hn hi hrel hinv ht h
    rw [frontend.nat_op_ground.hoist_targets_loop, if_neg (by scalar_tac)] at h
    cases Result.ok_injective h
    rw [hoistTargetsGo, dif_neg (by rw [hsize]; omega)]
    exact ⟨fun t ht' => by cases ht'; exact ⟨ltarget, lst, rfl, ht, hrel, hinv⟩,
      fun e he => by cases he⟩
  | succ n ih =>
    intro i st lst target ltarget o hn hi hrel hinv ht h
    rw [frontend.nat_op_ground.hoist_targets_loop, if_pos (by scalar_tac)] at h
    have hlt : i.val < (absIDeclArr ds).size := by rw [hsize]; omega
    rw [hoistTargetsGo, dif_pos hlt]
    obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨hib, hiv⟩ := ExprOps.vecIndexAt hi1
    obtain ⟨d, hd, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hdecl : (absIDeclArr ds)[i.val] = absIDeclaration d := by
      rw [i_declaration_dup_abs hd, ← hiv]; simp [absIDeclArr]
    rw [hdecl]
    obtain ⟨⟨r, st1⟩, hrec, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have S := is_nat_op_record_refines hrel hinv hrec
    cases r with
    | Err e =>
      cases Result.ok_injective h
      refine ⟨fun t ht' => (by cases ht'), fun e' he => ?_⟩
      cases he
      unfold Sim₀ at S
      rw [am_run_bind']
      exact AErrSim.bind S _
    | Ok oc =>
      obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply S
      unfold HCOut
      rw [am_run_bind', hx1, except_ok_bind]
      cases oc with
      | none =>
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := by
          have := ConRon.Refine.Nat.uadd_val hi2; simpa using this
        have IH := ih i2 st1 lst1 target ltarget o (by omega) (by omega) hrel1 hinv1 ht h
        rw [hi2v] at IH
        exact IH
      | some c =>
        obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have hi2v : absU i2 = i.val := by
          simp only [lift, Result.ok.injEq] at hi2; subst hi2
          show (UScalar.cast .U64 i).val = i.val
          rw [UScalar.cast_val_eq]
          apply Nat.mod_eq_of_lt
          have h3 : Std.Usize.max < 2 ^ 64 := by
            rw [Std.Usize.max_def, Std.Usize.numBits_def, UScalarTy.Usize_numBits_eq]
            cases System.Platform.numBits_eq with
            | inl h => rw [h]; decide
            | inr h => rw [h]; decide
          have h4 : UScalarTy.U64.numBits = 64 := rfl
          rw [h4]
          scalar_tac
        obtain ⟨⟨r1, st2⟩, hat, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
        have HA := hoist_targets_at_refines hrel1 hinv1 hr ht hidx hat
        rw [hi2v] at HA
        show HCOut pers lst1 o (do
          let deps ← natOpDeps (absNIdx c)
          let target ← hoistTargetsGo.hoistDeps (absIDeclArr ds) lm ltarget i.val deps
          hoistTargetsGo (absIDeclArr ds) lm target (i.val + 1))
        rw [← bind_assoc]
        cases r1 with
        | Err e =>
          cases Result.ok_injective h
          refine ⟨fun t ht' => (by cases ht'), fun e' he => ?_⟩
          cases he
          rw [am_run_bind']
          exact AErrSim.bind (HA.2 e rfl) _
        | Ok t =>
          obtain ⟨lt, lst2, hx2, ht2, hrel2, hinv2⟩ := HA.1 t rfl
          obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
          have hi3v : i3.val = i.val + 1 := by
            have := ConRon.Refine.Nat.uadd_val hi3; simpa using this
          have IH := ih i3 st2 lst2 t lt o (by omega) (by omega) hrel2 hinv2 ht2 h
          rw [hi3v] at IH
          unfold HCOut
          rw [am_run_bind', hx2, except_ok_bind]
          exact IH

/-- **`hoist_targets` refines `hoistTargets`**
(`Arena/Frontend/NatOpGround.lean:360-363`): the map from a record's index to
the earliest pinned-operation index it must precede.

Task #97-P5-Front round 2 (finding F8) restated the three worklist statements
(`hoist_close`, `hoist_targets_at`, this one) with their ERROR arm — they were
success-only, which leaves `hoist_nat_op_ground_refines`' `Sim` nothing for a
`decl_used_consts` failure — and this one with the index bound its caller's
`apply_hoist_refines` needs: every key and every target of the map is a record
index (the twin inserts only stack entries, which are name-index values, at
loop indices). -/
theorem hoist_targets_refines {pers rst lst ds o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.nat_op_ground.hoist_targets pers rst ds = ok o) :
    (∀ t, o.1 = .Ok t → ∃ lt lst',
      (hoistTargets (absIDeclArr ds)).run lst = .ok (lt, lst') ∧ TargetRel t lt ∧
      (∀ k tk, lt[k]? = some tk → k < (absIDeclArr ds).size ∧ tk < (absIDeclArr ds).size) ∧
      AStateRel₀ pers o.2 lst' ∧ AStateInv pers o.2) ∧
    (∀ e, o.1 = .Err e → AErrSim e ((hoistTargets (absIDeclArr ds)).run lst)) := by
  have hsize : (absIDeclArr ds).size = ds.val.length := by simp [absIDeclArr]
  rw [frontend.nat_op_ground.hoist_targets] at h
  obtain ⟨rm, hrm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hr := hoist_name_index_refines hrm
  obtain ⟨t0, ht0, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨i0, -, n0⟩ := ConRon.Refine.HashMap2.new_refines
    (HashableInst := U64.Insts.Con_ron_coreRonHashmapHashable) ht0
  have hT0 : TargetRel t0 ∅ := ⟨ConRon.Refine.HashMap2.RelOn_empty n0, i0⟩
  have hidx' := nameIndex_lt' (absIDeclArr ds) _ 0 ∅ rfl (by simp)
  have hidx : ∀ (x : NIdx) m, (nameIndex (absIDeclArr ds) ∅ 0)[x]? = some m →
      m < ds.val.length := fun x m hm => hsize ▸ hidx' x m hm
  have L := hoist_targets_loop_aux hr hidx _ 0#usize rst lst t0 ∅ o rfl (by simp)
    hrel hinv hT0 h
  refine ⟨fun t ht => ?_, fun e he => L.2 e he⟩
  obtain ⟨lt, lst', hx, hT, hrel', hinv'⟩ := L.1 t ht
  refine ⟨lt, lst', hx, hT, ?_, hrel', hinv'⟩
  exact hoistTargetsGo_bound hidx' _ 0 ∅ lst lt lst' rfl (by intro k tk hk; simp at hk) hx

/-! ## The reorder

Nine pure functions against the twin's five.  `apply_hoist`'s bucket pass is
`List.mergeSort` — task #87 §5's `hoistBuckets_eq_mergeSort`, the same
argument at handles: the keys are pairwise distinct because each carries its
own index, so `Pairwise` + `Perm` identifies the two orders. -/

/-- **`hoist_key` refines `hoistKey`** (`NatOpGround.lean:370-373`). -/
theorem hoist_key_refines {rm lm k o} (hr : TargetRel rm lm)
    (h : frontend.nat_op_ground.hoist_key rm k = ok o) :
    (absU o.1, absU o.2.1, absU o.2.2) = hoistKey lm (absU k) := by
  rw [frontend.nat_op_ground.hoist_key] at h
  obtain ⟨r, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hg := target_get hr hp
  simp only [hoistKey, ← hg]
  cases r with
  | none => cases Result.ok_injective h; rfl
  | some t => cases Result.ok_injective h; rfl

/-- **`hoist_lt` refines `hoistLt`** (`NatOpGround.lean:377-381`). -/
theorem hoist_lt_refines {rm lm a b v} (hr : TargetRel rm lm)
    (h : frontend.nat_op_ground.hoist_lt rm a b = ok v) :
    v = hoistLt lm (absU a) (absU b) := by
  rw [frontend.nat_op_ground.hoist_lt] at h
  obtain ⟨ka, hka, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨kb, hkb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have ea := hoist_key_refines hr hka
  have eb := hoist_key_refines hr hkb
  simp only [hoistLt, ← ea, ← eb]
  obtain ⟨a1, a2, a3⟩ := ka
  obtain ⟨b1, b2, b3⟩ := kb
  replace h : (if a1 < b1 then ok true else
      if a1 = b1 then (if a2 < b2 then ok true else if a2 = b2 then ok (decide (a3 < b3))
        else ok false) else ok false) = ok v := h
  simp only [absU]
  split at h
  next hl =>
    cases Result.ok_injective h
    have : a1.val < b1.val := by scalar_tac
    simp [this]
  next hl =>
    have hl' : ¬ a1.val < b1.val := by scalar_tac
    split at h
    next he =>
      have he' : a1.val = b1.val := by rw [he]
      split at h
      next hl2 =>
        cases Result.ok_injective h
        have : a2.val < b2.val := by scalar_tac
        simp [hl', he', this]
      next hl2 =>
        have hl2' : ¬ a2.val < b2.val := by scalar_tac
        split at h
        next he2 =>
          cases Result.ok_injective h
          have he2' : a2.val = b2.val := by rw [he2]
          simp [hl', he', hl2', he2']
        next he2 =>
          cases Result.ok_injective h
          have he2' : ¬ a2.val = b2.val := fun e => he2 (UScalar.eq_of_val_eq e)
          simp [hl', he', hl2', he2']
    next he =>
      cases Result.ok_injective h
      have he' : ¬ a1.val = b1.val := fun e => he (UScalar.eq_of_val_eq e)
      simp [hl', he']

/-- **`target_is`** — *"record `k`'s target is `t`"*, the port's own test. -/
theorem target_is_refines {rm lm k t v} (hr : TargetRel rm lm)
    (h : frontend.nat_op_ground.target_is rm k t = ok v) :
    v = (lm[absU k]? == some (absU t)) := by
  rw [frontend.nat_op_ground.target_is] at h
  obtain ⟨r, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [← target_get hr hp]
  cases r with
  | none => cases Result.ok_injective h; rfl
  | some tt =>
    cases Result.ok_injective h
    simp only [Option.map_some, absU]
    by_cases he : tt = t
    · subst he; simp
    · have : tt.val ≠ t.val := fun e => he (UScalar.eq_of_val_eq e)
      simp [he, this]

/-- **`hoist_moved_idxs`** — the indices the target map carries, in order. -/
theorem hoist_moved_idxs_refines {n rm lm v} (hr : TargetRel rm lm)
    (h : frontend.nat_op_ground.hoist_moved_idxs n rm = ok v) :
    v.val.map absU = (List.range n.val).filter (fun k => lm.contains k) := by
  rw [frontend.nat_op_ground.hoist_moved_idxs] at h
  have key : ∀ (k : Std.Usize) (out : alloc.vec.Vec Std.U64) v,
      frontend.nat_op_ground.hoist_moved_idxs_loop n rm out k = ok v →
      v.val.map absU = out.val.map absU ++
        (List.range' k.val (n.val - k.val)).filter (fun k => lm.contains k) := by
    refine cursor_induction (fun k : Std.Usize => k.val) n.val
      (fun k (out : alloc.vec.Vec Std.U64) => ∀ v,
        frontend.nat_op_ground.hoist_moved_idxs_loop n rm out k = ok v →
        v.val.map absU = out.val.map absU ++
          (List.range' k.val (n.val - k.val)).filter (fun k => lm.contains k)) ?_ ?_
    · intro k out hn v h
      rw [frontend.nat_op_ground.hoist_moved_idxs_loop.eq_def] at h
      rw [if_neg (show ¬ k < n by scalar_tac)] at h
      cases Result.ok_injective h
      simp [show n.val - k.val = 0 by omega]
    · intro k out hk ih v h
      rw [frontend.nat_op_ground.hoist_moved_idxs_loop.eq_def] at h
      rw [if_pos (show k < n by scalar_tac)] at h
      obtain ⟨i, hi, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨k1, hk1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hk1v : k1.val = k.val + 1 := by have := ConRon.Refine.Nat.uadd_val hk1; simpa using this
      have hiv : i.val = k.val := by
        simp only [lift, Result.ok.injEq] at hi; subst hi; exact usize_cast_u64_val' k
      have hbv : b = lm.contains k.val := by
        rw [ConRon.Refine.HashMap2.contains_key_refines_wf (P := fun _ => True) u64Eq2Fwd
          hr.2 (fun _ _ => trivial) trivial hb]
        have := hr.1 i trivial
        rw [Std.HashMap.contains_eq_isSome_getElem?, ← hiv]
        simp only [absU] at this
        rw [← this]; cases toFun rm i <;> rfl
      rw [ih k1 out1 hk1v v h, hk1v,
        show n.val - k.val = (n.val - (k.val + 1)) + 1 by omega, List.range'_succ,
        List.filter_cons]
      split at hout1
      · rename_i hbt
        obtain ⟨i1, hi1, hout1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hout1
        have hi1v : i1.val = k.val := by
          simp only [lift, Result.ok.injEq] at hi1; subst hi1; exact usize_cast_u64_val' k
        rw [ConRon.Refine.vec_push_val hout1]
        rw [hbv] at hbt
        simp [hbt, hi1v, absU]
      · rename_i hbf
        cases Result.ok_injective hout1
        rw [hbv] at hbf
        simp [hbf]
  have := key 0#usize _ v h
  simpa [alloc.vec.Vec.new, List.range_eq_range'] using this

/-! ## `hoist_order`: the bucket pass is the sort (ported from
`RefineOld/Frontend/PrepareR.lean`, task #87 §5) -/

/-- The port's bucket pass, as a list: at each position `t`, the moved records
targeted at `t` in index order, then `t` itself unless it moved. -/
def hoistBucketAt (s : Std.HashMap Nat Nat) (moved : List Nat) (t : Nat) : List Nat :=
  (moved.filter (fun k => s[k]? == some t)) ++ (if s.contains t then [] else [t])

def hoistBuckets (s : Std.HashMap Nat Nat) (moved : List Nat) (n : Nat) : List Nat :=
  (List.range n).flatMap (hoistBucketAt s moved)

/-- The key's strict order, as a `Prop`. -/
def hoistKeyLt (p q : Nat × Nat × Nat) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ (p.2.1 < q.2.1 ∨ (p.2.1 = q.2.1 ∧ p.2.2 < q.2.2)))

theorem hoistLt_iff (s : Std.HashMap Nat Nat) (a b : Nat) :
    hoistLt s a b = true ↔ hoistKeyLt (hoistKey s a) (hoistKey s b) := by
  rcases ha : s[a]? with _ | ta <;> rcases hb : s[b]? with _ | tb <;>
    simp [hoistLt, hoistKey, ha, hb, hoistKeyLt]

theorem hoistKey_some {s : Std.HashMap Nat Nat} {k t : Nat}
    (h : s[k]? = some t) : hoistKey s k = (t, 0, k) := by simp [hoistKey, h]

theorem hoistKey_none {s : Std.HashMap Nat Nat} {k : Nat}
    (h : s[k]? = none) : hoistKey s k = (k, 1, k) := by simp [hoistKey, h]

theorem hoistKey_third (s : Std.HashMap Nat Nat) (k : Nat) :
    (hoistKey s k).2.2 = k := by
  rw [hoistKey]; rcases s[k]? with _ | t <;> rfl

theorem hoistKeyLt_irrefl {p : Nat × Nat × Nat} : ¬ hoistKeyLt p p := by
  rw [hoistKeyLt]; omega

theorem hoistKeyLt_trans {p q r : Nat × Nat × Nat} (h1 : hoistKeyLt p q)
    (h2 : hoistKeyLt q r) : hoistKeyLt p r := by
  rw [hoistKeyLt] at h1 h2 ⊢; omega

theorem hoistKeyLt_total (s : Std.HashMap Nat Nat) {a b : Nat} (h : a ≠ b) :
    hoistKeyLt (hoistKey s a) (hoistKey s b) ∨ hoistKeyLt (hoistKey s b) (hoistKey s a) := by
  have ha := hoistKey_third s a
  have hb := hoistKey_third s b
  rw [hoistKeyLt, hoistKeyLt]
  omega

theorem hoist_le_iff (s : Std.HashMap Nat Nat) (a b : Nat) :
    (!hoistLt s b a) = true ↔ ¬ hoistKeyLt (hoistKey s b) (hoistKey s a) := by
  rw [Bool.not_eq_true', ← hoistLt_iff, Bool.not_eq_true]

theorem hoist_le_trans (s : Std.HashMap Nat Nat) (a b c : Nat)
    (h1 : (!hoistLt s b a) = true) (h2 : (!hoistLt s c b) = true) :
    (!hoistLt s c a) = true := by
  rw [hoist_le_iff] at h1 h2 ⊢
  intro hc
  rcases (by rw [hoistKeyLt] at *; omega : hoistKeyLt (hoistKey s c) (hoistKey s b)
      ∨ hoistKeyLt (hoistKey s b) (hoistKey s a)) with h | h
  · exact h2 h
  · exact h1 h

theorem hoist_le_total (s : Std.HashMap Nat Nat) (a b : Nat) :
    ((!hoistLt s b a) || (!hoistLt s a b)) = true := by
  by_cases h : hoistLt s b a = true
  · have hy : hoistLt s a b = false := by
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      rw [hoistLt_iff] at h hc
      exact hoistKeyLt_irrefl (hoistKeyLt_trans h hc)
    simp [hy]
  · simp only [Bool.not_eq_true] at h
    simp [h]

theorem hoist_le_antisymm (s : Std.HashMap Nat Nat) (a b : Nat)
    (h1 : (!hoistLt s b a) = true) (h2 : (!hoistLt s a b) = true) : a = b := by
  rw [hoist_le_iff] at h1 h2
  by_contra hne
  rcases hoistKeyLt_total s hne with h | h
  · exact h2 h
  · exact h1 h

theorem hoistBucketAt_key_fst {s : Std.HashMap Nat Nat} {moved : List Nat}
    {t x : Nat} (h : x ∈ hoistBucketAt s moved t) : (hoistKey s x).1 = t := by
  rw [hoistBucketAt] at h
  rcases List.mem_append.mp h with h | h
  · have := (List.mem_filter.mp h).2
    simp only [beq_iff_eq] at this
    rw [hoistKey_some this]
  · by_cases hc : s.contains t
    · rw [if_pos hc] at h; simp at h
    · rw [if_neg hc] at h
      rw [List.mem_singleton.mp h, hoistKey_none
        (show s[t]? = none from by
          rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
          simpa using hc)]

theorem hoistBucketAt_pairwise {s : Std.HashMap Nat Nat} {moved : List Nat}
    (hmoved : moved.Pairwise (· < ·)) (t : Nat) :
    (hoistBucketAt s moved t).Pairwise
      (fun a b => hoistKeyLt (hoistKey s a) (hoistKey s b)) := by
  rw [hoistBucketAt]
  refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
  · refine List.Pairwise.imp_of_mem ?_ (hmoved.filter _)
    intro a b hma hmb hab
    have ha : s[a]? = some t := by
      have := (List.mem_filter.mp hma).2; simpa using this
    have hb : s[b]? = some t := by
      have := (List.mem_filter.mp hmb).2; simpa using this
    rw [hoistKey_some ha, hoistKey_some hb]
    exact Or.inr ⟨rfl, Or.inr ⟨rfl, hab⟩⟩
  · split <;> simp
  · intro a ha b hb
    have hat : s[a]? = some t := by
      have := (List.mem_filter.mp ha).2; simpa using this
    by_cases hc : s.contains t
    · rw [if_pos hc] at hb; simp at hb
    · rw [if_neg hc] at hb
      have hbt : b = t := List.mem_singleton.mp hb
      have hnone : s[t]? = none := by
        rw [Std.HashMap.contains_eq_isSome_getElem?] at hc; simpa using hc
      rw [hoistKey_some hat, hbt, hoistKey_none hnone]
      exact Or.inr ⟨rfl, Or.inl Nat.zero_lt_one⟩

theorem hoistBuckets_pairwise {s : Std.HashMap Nat Nat}
    {moved : List Nat} (hmoved : moved.Pairwise (· < ·)) :
    ∀ n : Nat, (hoistBuckets s moved n).Pairwise
      (fun a b => hoistKeyLt (hoistKey s a) (hoistKey s b))
  | 0 => by rw [hoistBuckets]; simp
  | n + 1 => by
    rw [hoistBuckets, List.range_succ, List.flatMap_append]
    refine List.pairwise_append.mpr ⟨hoistBuckets_pairwise hmoved n,
      by simpa using hoistBucketAt_pairwise hmoved n, ?_⟩
    intro a ha b hb
    obtain ⟨t, ht, hat⟩ := List.mem_flatMap.mp ha
    rw [List.mem_range] at ht
    have h1 : (hoistKey s a).1 = t := hoistBucketAt_key_fst hat
    have h2 : (hoistKey s b).1 = n := hoistBucketAt_key_fst (by simpa using hb)
    rw [hoistKeyLt]; omega

theorem mem_hoistBuckets {s : Std.HashMap Nat Nat} {n x : Nat}
    (hb : ∀ k t, s[k]? = some t → k < n → t < n) :
    x ∈ hoistBuckets s ((List.range n).filter (fun k => s.contains k)) n ↔ x < n := by
  rw [hoistBuckets]
  constructor
  · intro h
    obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.mp h
    rw [List.mem_range] at ht
    rw [hoistBucketAt] at hxt
    rcases List.mem_append.mp hxt with h | h
    · have := (List.mem_filter.mp (List.mem_filter.mp h).1).1
      rwa [List.mem_range] at this
    · by_cases hc : s.contains t
      · rw [if_pos hc] at h; simp at h
      · rw [if_neg hc] at h; rw [List.mem_singleton.mp h]; exact ht
  · intro hx
    by_cases hc : s.contains x
    · obtain ⟨t, ht⟩ : ∃ t, s[x]? = some t := by
        rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
        rcases hx2 : s[x]? with _ | t
        · rw [hx2] at hc; simp at hc
        · exact ⟨t, rfl⟩
      refine List.mem_flatMap.mpr ⟨t, List.mem_range.mpr (hb x t ht hx), ?_⟩
      rw [hoistBucketAt]
      refine List.mem_append.mpr (Or.inl (List.mem_filter.mpr ⟨?_, by simp [ht]⟩))
      exact List.mem_filter.mpr ⟨List.mem_range.mpr hx, by simpa using hc⟩
    · refine List.mem_flatMap.mpr ⟨x, List.mem_range.mpr hx, ?_⟩
      rw [hoistBucketAt]
      exact List.mem_append.mpr (Or.inr (by rw [if_neg hc]; simp))

theorem hoistBuckets_nodup {s : Std.HashMap Nat Nat} {moved : List Nat}
    (hmoved : moved.Pairwise (· < ·)) (n : Nat) :
    (hoistBuckets s moved n).Nodup := by
  refine List.Pairwise.imp ?_ (hoistBuckets_pairwise hmoved n)
  intro a b hab hc
  rw [hc] at hab
  exact hoistKeyLt_irrefl hab

theorem hoistBuckets_perm {s : Std.HashMap Nat Nat} {n : Nat}
    (hb : ∀ k t, s[k]? = some t → k < n → t < n) :
    (hoistBuckets s ((List.range n).filter (fun k => s.contains k)) n).Perm
      (List.range n) := by
  refine (List.perm_ext_iff_of_nodup
    (hoistBuckets_nodup (List.pairwise_lt_range.filter _) n) (List.nodup_range)).mpr ?_
  intro x
  rw [mem_hoistBuckets hb, List.mem_range]

/-- **The bucket pass is the sort.** -/
theorem hoistBuckets_eq_mergeSort (s : Std.HashMap Nat Nat) (n : Nat)
    (hb : ∀ k t, s[k]? = some t → k < n → t < n) :
    hoistBuckets s ((List.range n).filter (fun k => s.contains k)) n
      = (List.range n).mergeSort (fun a b => !hoistLt s b a) := by
  refine List.Perm.eq_of_pairwise (le := fun a b => (!hoistLt s b a) = true)
    (fun a b _ _ h1 h2 => hoist_le_antisymm s a b h1 h2) ?_ ?_ ?_
  · refine List.Pairwise.imp ?_
      (hoistBuckets_pairwise (s := s) (List.pairwise_lt_range.filter _) n)
    intro a b hab
    rw [hoist_le_iff]
    intro hc
    exact hoistKeyLt_irrefl (hoistKeyLt_trans hab hc)
  · exact List.pairwise_mergeSort (hoist_le_trans s) (hoist_le_total s) _
  · exact (hoistBuckets_perm hb).trans (List.mergeSort_perm _ _).symm

/-- `hoist_order`'s inner loop: one bucket's moved records. -/
theorem hoist_order_inner_refines {rm lm} (hr : TargetRel rm lm)
    {moved : alloc.vec.Vec Std.U64} {t : Std.Usize} :
    ∀ (a : Std.Usize) (order : alloc.vec.Vec Std.U64) v,
      frontend.nat_op_ground.hoist_order_loop0_loop0 rm moved order t
        (alloc.vec.Vec.len moved) a = ok v →
      v.val.map absU = order.val.map absU ++
        ((moved.val.drop a.val).map absU).filter (fun k => lm[k]? == some t.val) := by
  refine cursor_induction (fun a : Std.Usize => a.val) moved.val.length
    (fun a (order : alloc.vec.Vec Std.U64) => ∀ v,
      frontend.nat_op_ground.hoist_order_loop0_loop0 rm moved order t
        (alloc.vec.Vec.len moved) a = ok v →
      v.val.map absU = order.val.map absU ++
        ((moved.val.drop a.val).map absU).filter (fun k => lm[k]? == some t.val)) ?_ ?_
  · intro a order hn v h
    rw [frontend.nat_op_ground.hoist_order_loop0_loop0.eq_def] at h
    rw [if_neg (show ¬ a < alloc.vec.Vec.len moved by scalar_tac)] at h
    cases Result.ok_injective h
    simp [List.drop_eq_nil_of_le hn]
  · intro a order hlt ih v h
    rw [frontend.nat_op_ground.hoist_order_loop0_loop0.eq_def] at h
    rw [if_pos (show a < alloc.vec.Vec.len moved by scalar_tac)] at h
    obtain ⟨kk, hkk, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨order1, horder1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨a1, ha1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have ha1v : a1.val = a.val + 1 := usize_add_one_inv ha1
    have hkx : moved.val[a.val]'hlt = kk := by
      have h1 := vec_index_some hkk
      rw [List.getElem?_eq_getElem hlt] at h1
      exact Option.some_injective _ h1
    have hi1v : i1.val = t.val := by
      simp only [lift, Result.ok.injEq] at hi1; subst hi1; exact usize_cast_u64_val' t
    have hbv := target_is_refines hr hb
    rw [ih a1 order1 ha1v v h, ha1v, List.drop_eq_getElem_cons hlt, hkx]
    simp only [List.map_cons, List.filter_cons]
    rw [hbv] at horder1
    simp only [absU, hi1v] at horder1 ⊢
    split at horder1
    · rename_i hbt
      rw [ConRon.Refine.vec_push_val horder1, if_pos hbt]
      simp [absU]
    · rename_i hbf
      cases Result.ok_injective horder1
      rw [if_neg hbf]

/-- `hoist_order`'s outer loop: the buckets from `t` on. -/
theorem hoist_order_outer_refines {rm lm} (hr : TargetRel rm lm)
    {moved : alloc.vec.Vec Std.U64} {n : Std.Usize} :
    ∀ (t : Std.Usize) (order : alloc.vec.Vec Std.U64) v,
      frontend.nat_op_ground.hoist_order_loop0 n rm moved order t = ok v →
      v.val.map absU = order.val.map absU ++
        (List.range' t.val (n.val - t.val)).flatMap
          (hoistBucketAt lm (moved.val.map absU)) := by
  refine cursor_induction (fun t : Std.Usize => t.val) n.val
    (fun t (order : alloc.vec.Vec Std.U64) => ∀ v,
      frontend.nat_op_ground.hoist_order_loop0 n rm moved order t = ok v →
      v.val.map absU = order.val.map absU ++
        (List.range' t.val (n.val - t.val)).flatMap
          (hoistBucketAt lm (moved.val.map absU))) ?_ ?_
  · intro t order hn v h
    rw [frontend.nat_op_ground.hoist_order_loop0.eq_def] at h
    rw [if_neg (show ¬ t < n by scalar_tac)] at h
    cases Result.ok_injective h
    simp [show n.val - t.val = 0 by omega]
  · intro t order hlt ih v h
    rw [frontend.nat_op_ground.hoist_order_loop0.eq_def] at h
    rw [if_pos (show t < n by scalar_tac)] at h
    obtain ⟨order1, horder1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨i, hi, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨order2, horder2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨t1, ht1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have ht1v : t1.val = t.val + 1 := usize_add_one_inv ht1
    have hiv : i.val = t.val := by
      simp only [lift, Result.ok.injEq] at hi; subst hi; exact usize_cast_u64_val' t
    have hbv : b = lm.contains t.val := by
      rw [ConRon.Refine.HashMap2.contains_key_refines_wf (P := fun _ => True) u64Eq2Fwd
        hr.2 (fun _ _ => trivial) trivial hb]
      have := hr.1 i trivial
      rw [Std.HashMap.contains_eq_isSome_getElem?, ← hiv]
      simp only [absU] at this
      rw [← this]; cases toFun rm i <;> rfl
    have h1 := hoist_order_inner_refines hr 0#usize order order1 horder1
    rw [show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero] at h1
    rw [ih t1 order2 ht1v v h, ht1v,
      show n.val - t.val = (n.val - (t.val + 1)) + 1 by omega, List.range'_succ,
      List.flatMap_cons, hoistBucketAt]
    split at horder2
    · rename_i hbt
      cases Result.ok_injective horder2
      rw [h1, if_pos (by rw [← hbv]; exact hbt)]
      simp
    · rename_i hbf
      obtain ⟨t4, ht4, hpush⟩ := ConRon.Refine.bind_eq_ok_iff.mp horder2
      have ht4v : t4.val = t.val := by
        simp only [lift, Result.ok.injEq] at ht4; subst ht4; exact usize_cast_u64_val' t
      rw [ConRon.Refine.vec_push_val hpush]
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [h1, if_neg (by rw [← hbv]; simpa using hbf)]
      simp [ht4v, absU]

/-- **`hoist_order`** — the sorted order `applyHoist` sorts by.  The port's
bucket pass against the twin's `List.mergeSort` (task #87 §5).  Two
hypotheses, both the call site's (task #97-P5-Front round 2, finding F7: the
statement had neither and was false without them): `moved` is
`hoist_moved_idxs`' answer, and every target of a record below `n` is below
`n` — a record whose target is `n` or more falls outside every bucket of the
port, where the twin's sort keeps it. -/
theorem hoist_order_refines {n rm lm moved v} (hr : TargetRel rm lm)
    (hm : moved.val.map absU = (List.range n.val).filter (fun k => lm.contains k))
    (hb : ∀ k t, lm[k]? = some t → k < n.val → t < n.val)
    (h : frontend.nat_op_ground.hoist_order n rm moved = ok v) :
    v.val.map absU =
      (List.range n.val).mergeSort (fun a b => !hoistLt lm b a) := by
  rw [frontend.nat_op_ground.hoist_order] at h
  have := hoist_order_outer_refines hr 0#usize _ v h
  rw [← hoistBuckets_eq_mergeSort lm n.val hb, ← hm]
  simpa [hoistBuckets, List.range_eq_range', alloc.vec.Vec.with_capacity] using this

/-- **`hoist_reorder` refines `reorder`** (`NatOpGround.lean:399-400`).  Task
#87 §5's precondition is the port's own: an out-of-range `order` entry makes
the port's read FAIL rather than read garbage — but only once the entry has
been cast to `usize`, and on a 32-bit target `as usize` truncates a `u64`, so
an entry of `2 ^ 32` or more would read a record the twin's `ds[k]?` does not
(task #97-P5-Front round 2, finding F9).  Hence `ho`, which the call site has:
`order` is a sort of `List.range ds.len()`. -/
theorem hoist_reorder_refines {ds order v}
    (ho : ∀ x ∈ order.val, x.val < ds.val.length)
    (h : frontend.nat_op_ground.hoist_reorder ds order = ok v) :
    absIDeclArr v = reorder (absIDeclArr ds) (order.val.map absU) := by
  rw [frontend.nat_op_ground.hoist_reorder] at h
  have hfold : ∀ (A : Array IDeclaration) (L : List Nat) (acc : Array IDeclaration),
      L.foldl (fun acc k => acc ++ (A[k]?).toArray) acc
        = acc ++ (L.flatMap fun k => (A[k]?).toList).toArray := by
    intro A
    intro L
    induction L with
    | nil => intro acc; simp
    | cons k L ih =>
      intro acc
      rw [List.foldl_cons, ih]
      cases hk : A[k]? <;> simp [hk]
  have key : ∀ (i : Std.Usize) (out : alloc.vec.Vec arena.env.IDeclaration) v,
      frontend.nat_op_ground.hoist_reorder_loop ds order (alloc.vec.Vec.len order) out i
        = ok v →
      v.val.map absIDeclaration = out.val.map absIDeclaration ++
        ((order.val.drop i.val).map absU).flatMap (fun k => ((absIDeclArr ds)[k]?).toList) := by
    refine cursor_induction (fun i : Std.Usize => i.val) order.val.length
      (fun i (out : alloc.vec.Vec arena.env.IDeclaration) => ∀ v,
        frontend.nat_op_ground.hoist_reorder_loop ds order (alloc.vec.Vec.len order) out i
          = ok v →
        v.val.map absIDeclaration = out.val.map absIDeclaration ++
          ((order.val.drop i.val).map absU).flatMap (fun k => ((absIDeclArr ds)[k]?).toList)) ?_ ?_
    · intro i out hn v h
      rw [frontend.nat_op_ground.hoist_reorder_loop.eq_def] at h
      rw [if_neg (show ¬ i < alloc.vec.Vec.len order by scalar_tac)] at h
      cases Result.ok_injective h
      simp [List.drop_eq_nil_of_le hn]
    · intro i out hi ih v h
      rw [frontend.nat_op_ground.hoist_reorder_loop.eq_def] at h
      rw [if_pos (show i < alloc.vec.Vec.len order by scalar_tac)] at h
      obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i3, hi3, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i4, hi4, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i5, hi5, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi5v : i5.val = i.val + 1 := by
        have := ConRon.Refine.Nat.uadd_val hi5; simpa using this
      have hi1v : order.val[i.val]'hi = i1 := by
        have h1 := vec_index_some hi1
        rw [List.getElem?_eq_getElem hi] at h1
        exact Option.some_injective _ h1
      have hi2v : i2.val = i1.val := by
        simp only [lift, Result.ok.injEq] at hi2; subst hi2
        rw [UScalar.cast_val_eq]
        apply Nat.mod_eq_of_lt
        have h1 := ho i1 (by rw [← hi1v]; exact List.getElem_mem hi)
        have h2 := ds.property
        have h3 : Std.Usize.max < 2 ^ UScalarTy.Usize.numBits := by
          rw [Std.Usize.max_def, Std.Usize.numBits_def]
          have : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
          omega
        omega
      have hi3v : ds.val[i2.val]? = some i3 := vec_index_some hi3
      have hA : (absIDeclArr ds)[i1.val]? = some (absIDeclaration i3) := by
        simp only [absIDeclArr, List.getElem?_toArray, List.getElem?_map, ← hi2v, hi3v]
        rfl
      rw [ih i5 out1 hi5v v h, hi5v, List.drop_eq_getElem_cons hi, hi1v,
        ConRon.Refine.vec_push_val hout1, List.map_cons, List.flatMap_cons,
        show absU i1 = i1.val from rfl, hA, List.map_append]
      simp [i_declaration_dup_abs hi4]
  have := key 0#usize _ v h
  simp only [alloc.vec.Vec.with_capacity, List.map_nil, List.nil_append,
    show ((0#usize : Std.Usize)).val = 0 by rfl, List.drop_zero] at this
  rw [reorder, hfold, Array.empty_append, absIDeclArr, this]
  simp [alloc.vec.Vec.new]

/-- **`hoist_moved_names` refines `movedNames`** (`NatOpGround.lean:385-392`). -/
theorem hoist_moved_names_refines {ds moved rm lm v} (hr : TargetRel rm lm)
    (hm : moved.val.map absU = (List.range (absIDeclArr ds).size).filter
      (fun k => lm.contains k))
    (h : frontend.nat_op_ground.hoist_moved_names ds moved = ok v) :
    absNIdxArr v = movedNames (absIDeclArr ds) lm #[] 0 := by
  rw [frontend.nat_op_ground.hoist_moved_names] at h
  let nm : Nat → List NIdx := fun k => (((absIDeclArr ds)[k]?).map IDeclaration.names).getD []
  -- the twin's recursion, as a list
  have htw : ∀ (d : Nat) (k : Nat) (acc : Array NIdx), (absIDeclArr ds).size - k = d →
      movedNames (absIDeclArr ds) lm acc k = acc ++
        (((List.range' k ((absIDeclArr ds).size - k)).filter
          (fun k => lm.contains k)).flatMap nm).toArray := by
    intro d
    induction d with
    | zero =>
      intro k acc hd
      rw [movedNames, dif_neg (by omega), hd]
      simp
    | succ d ih =>
      intro k acc hd
      have hk : k < (absIDeclArr ds).size := by omega
      rw [movedNames, dif_pos hk, ih (k + 1) _ (by omega),
        show (absIDeclArr ds).size - k = ((absIDeclArr ds).size - (k + 1)) + 1 by omega,
        List.range'_succ, List.filter_cons]
      have hnm : nm k = (absIDeclArr ds)[k].names := by
        have hk' : k < ds.val.length := by simpa [absIDeclArr] using hk
        simp [nm, absIDeclArr, List.getElem?_eq_getElem hk']
      by_cases hc : lm.contains k
      · simp [hc, hnm]
      · simp [hc]
  -- the inner copy
  have hin : ∀ (ns : alloc.vec.Vec arena.handle.NIdx) (j : Std.Usize)
      (out o : alloc.vec.Vec arena.handle.NIdx),
      frontend.nat_op_ground.hoist_moved_names_loop0_loop0 out ns (alloc.vec.Vec.len ns) j
        = ok o →
      o.val.map absNIdx = out.val.map absNIdx ++ (ns.val.drop j.val).map absNIdx := by
    intro ns
    refine vec_cursor_copy ns absNIdx absNIdx
      (fun j out => frontend.nat_op_ground.hoist_moved_names_loop0_loop0 out ns
        (alloc.vec.Vec.len ns) j) ?_ ?_
    · intro j out o hn h
      rw [frontend.nat_op_ground.hoist_moved_names_loop0_loop0.eq_def] at h
      rw [if_neg (show ¬ j < alloc.vec.Vec.len ns by scalar_tac)] at h
      rw [← Result.ok_injective h]
    · intro j x out o hx h
      have hlt : j.val < ns.val.length := (List.getElem?_eq_some_iff.mp hx).1
      rw [frontend.nat_op_ground.hoist_moved_names_loop0_loop0.eq_def] at h
      rw [if_pos (show j < alloc.vec.Vec.len ns by scalar_tac)] at h
      obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨j1, hj1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hnx : n = x := by
        have h1 := vec_index_some hn; rw [hx] at h1; exact (Option.some_inj.mp h1).symm
      subst hnx
      exact ⟨j1, n1, out1, absSz_add_one hj1, ConRon.Refine.vec_push_val hout1,
        by rw [dupId_nidx _ _ hn1], h⟩
  -- the outer loop
  have hout : ∀ (a : Std.Usize) (out o : alloc.vec.Vec arena.handle.NIdx),
      frontend.nat_op_ground.hoist_moved_names_loop0 ds moved out (alloc.vec.Vec.len moved) a
        = ok o →
      o.val.map absNIdx = out.val.map absNIdx ++
        ((moved.val.drop a.val).map absU).flatMap nm := by
    refine cursor_induction (fun a : Std.Usize => a.val) moved.val.length
      (fun a (out : alloc.vec.Vec arena.handle.NIdx) => ∀ o,
        frontend.nat_op_ground.hoist_moved_names_loop0 ds moved out (alloc.vec.Vec.len moved) a
          = ok o →
        o.val.map absNIdx = out.val.map absNIdx ++
          ((moved.val.drop a.val).map absU).flatMap nm) ?_ ?_
    · intro a out hn o h
      rw [frontend.nat_op_ground.hoist_moved_names_loop0.eq_def] at h
      rw [if_neg (show ¬ a < alloc.vec.Vec.len moved by scalar_tac)] at h
      cases Result.ok_injective h
      simp [List.drop_eq_nil_of_le hn]
    · intro a out ha ih o h
      rw [frontend.nat_op_ground.hoist_moved_names_loop0.eq_def] at h
      rw [if_pos (show a < alloc.vec.Vec.len moved by scalar_tac)] at h
      obtain ⟨i, hi, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i1, hi1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨ns, hns, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨out1, hout1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      obtain ⟨a1, ha1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have ha1v : a1.val = a.val + 1 := by
        have := ConRon.Refine.Nat.uadd_val ha1; simpa using this
      have hiv : moved.val[a.val]'ha = i := by
        have h1 := vec_index_some hi
        rw [List.getElem?_eq_getElem ha] at h1
        exact Option.some_injective _ h1
      have hilt : i.val < (absIDeclArr ds).size := by
        have hx : i.val ∈ moved.val.map absU :=
          List.mem_map.mpr ⟨i, by rw [← hiv]; exact List.getElem_mem ha, rfl⟩
        rw [hm, List.mem_filter, List.mem_range] at hx
        exact hx.1
      have hi1v : i1.val = i.val := by
        simp only [lift, Result.ok.injEq] at hi1; subst hi1
        rw [UScalar.cast_val_eq]
        apply Nat.mod_eq_of_lt
        have h2 := ds.property
        have h3 : Std.Usize.max < 2 ^ UScalarTy.Usize.numBits := by
          rw [Std.Usize.max_def, Std.Usize.numBits_def]
          have : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
          omega
        simp only [absIDeclArr, List.size_toArray, List.length_map] at hilt
        omega
      have hi2v : ds.val[i1.val]? = some i2 := vec_index_some hi2
      have hnm : nm i.val = ns.val.map absNIdx := by
        simp only [nm, absIDeclArr, List.getElem?_toArray, List.getElem?_map, ← hi1v, hi2v,
          Option.map_some, Option.getD_some]
        exact (i_declaration_names_abs hns).symm
      rw [ih a1 out1 ha1v o h, hin ns 0#usize out out1 hout1, ha1v,
        List.drop_eq_getElem_cons ha, hiv, List.map_cons, List.flatMap_cons, hnm]
      simp
  have := hout 0#usize _ v h
  simp only [alloc.vec.Vec.new, List.map_nil, List.nil_append, List.drop_zero,
    show ((0#usize : Std.Usize)).val = 0 by rfl] at this
  rw [htw _ 0 #[] rfl, absNIdxArr, this, hm]
  simp [List.range_eq_range']

/-- **`apply_hoist` refines `applyHoist`** (`NatOpGround.lean:404-408`).  Task
#87 §5's genuine precondition is the port's own and is free at the one call
site: every target of a record below `ds.len()` is below it
(`hoist_targets_refines` gives it).  Until task #97-P5-Front round 2 the note
said so and the statement did not carry it (finding F7). -/
theorem apply_hoist_refines {ds rm lm o} (hr : TargetRel rm lm)
    (hb : ∀ k t, lm[k]? = some t → k < (absIDeclArr ds).size → t < (absIDeclArr ds).size)
    (h : frontend.nat_op_ground.apply_hoist ds rm = ok o) :
    (absIDeclArr o.1, absNIdxArr o.2) = applyHoist (absIDeclArr ds) lm := by
  rw [frontend.nat_op_ground.apply_hoist] at h
  obtain ⟨moved, hm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨order, ho, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨out, hout, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨names, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  have hsz : (alloc.vec.Vec.len ds).val = (absIDeclArr ds).size := by
    simp [absIDeclArr, alloc.vec.Vec.len]
  have hM := hoist_moved_idxs_refines hr hm
  rw [hsz] at hM
  have hO := hoist_order_refines hr (by rw [hsz]; exact hM)
    (fun k t hk hlt => by rw [hsz] at hlt ⊢; exact hb k t hk hlt) ho
  rw [hsz] at hO
  have hR := hoist_reorder_refines (fun x hx => by
    have hx' : x.val ∈ order.val.map absU := List.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hO, List.mem_mergeSort, List.mem_range] at hx'
    simpa [absIDeclArr] using hx') hout
  have hN := hoist_moved_names_refines hr hM hn
  simp only [applyHoist, hR, hO, hN]

/-- **`hoist_nat_op_ground` refines `hoistNatOpGround`**
(`Arena/Frontend/NatOpGround.lean:413-417`) — **the hoist**, and one of the
tier's named deliverables. -/
theorem hoist_nat_op_ground_refines {pers rst lst ds o}
    (hrel : AStateRel₀ pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.nat_op_ground.hoist_nat_op_ground pers rst ds = ok o) :
    Sim₀ (fun p => (absIDeclArr p.1, absNIdxArr p.2)) pers lst o
      (hoistNatOpGround (absIDeclArr ds)) := by
  rw [frontend.nat_op_ground.hoist_nat_op_ground] at h
  obtain ⟨⟨r, st1⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨hOk, hErr⟩ := hoist_targets_refines hrel hinv h1
  simp only [Sim₀, hoistNatOpGround, am_run_bind']
  cases r with
  | Err e =>
    cases Result.ok_injective h
    exact AErrSim.bind (hErr e rfl) _
  | Ok t =>
    obtain ⟨lt, lst', hx, hT, hb, hrel', hinv'⟩ := hOk t rfl
    rw [hx]
    simp only [except_ok_bind]
    obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have hlen := (ConRon.Refine.HashMap2.len_refines hT.2 hn).1
    -- the twin's `isEmpty` is the port's `len () == 0`
    have hsize : (absIDeclArr ds).size < 2 ^ 64 := by
      have h1 := ds.property
      have h2 : Std.Usize.max < 2 ^ 64 := by
        rw [Std.Usize.max_def, Std.Usize.numBits_def, UScalarTy.Usize_numBits_eq]
        cases System.Platform.numBits_eq with
        | inl h => rw [h]; decide
        | inr h => rw [h]; decide
      simp only [absIDeclArr, List.size_toArray, List.length_map]
      omega
    have hemp : lt.isEmpty = true ↔ n = 0#usize := by
      constructor
      · intro he
        have hnone : ∀ k, ConRon.Refine.HashMap2.toFun t k = none := by
          intro k
          have := hT.1 k trivial
          rw [Std.HashMap.isEmpty_iff_forall_not_mem] at he
          rw [Std.HashMap.getElem?_eq_none (he _)] at this
          exact Option.map_eq_none_iff.mp this
        have hsl := ConRon.Refine.HashMap2.toFun_eq_none_iff.mp hnone
        rw [hsl] at hlen
        exact Std.UScalar.eq_of_val_eq (by simpa using hlen)
      · intro hn0
        subst hn0
        have hsl : ConRon.Refine.HashMap2.sl_v t = [] := by
          simpa using hlen.symm
        have hnone := ConRon.Refine.HashMap2.toFun_eq_none_iff.mpr hsl
        rw [Std.HashMap.isEmpty_iff_forall_not_mem]
        intro k hk
        rw [Std.HashMap.mem_iff_isSome_getElem?, Option.isSome_iff_exists] at hk
        obtain ⟨tk, htk⟩ := hk
        have hk64 : k < 2 ^ UScalarTy.U64.numBits := by
          have := (hb k tk htk).1; rw [UScalarTy.U64_numBits_eq]; omega
        have := hT.1 (UScalar.ofNatCore (ty := .U64) k hk64) trivial
        rw [hnone] at this
        have hv : absU (UScalar.ofNatCore (ty := .U64) k hk64) = k := by
          rfl
        rw [hv, htk] at this
        simp at this
    by_cases hn0 : n = 0#usize
    · rw [if_pos hn0] at h
      cases Result.ok_injective h
      rw [if_pos (hemp.mpr hn0)]
      exact ⟨lst', rfl, hrel', hinv'⟩
    · rw [if_neg hn0] at h
      obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      cases Result.ok_injective h
      have hne : ¬ lt.isEmpty = true := fun he => hn0 (hemp.mp he)
      rw [if_neg hne]
      have hA := apply_hoist_refines hT (fun k tk hk _ => (hb k tk hk).2) hp
      refine ⟨lst', ?_, hrel', hinv'⟩
      rw [← hA]; rfl


end ConRon.Refine2.Frontend

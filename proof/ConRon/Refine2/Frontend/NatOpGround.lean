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
   The twin makes it a FUELLED recursion (`hoistClosure`'s `ds.size * ds.size
   + 1`), so over handles the port and the twin agree on the measure and the
   lemma is a fuel induction rather than a well-founded one.  **That is a
   strict improvement on the original campaign and is worth recording**: the
   twin's fuel is the thing that buys it.

## `sorry` count in this file: 27
-/
import ConRon.Refine2.Frontend.Prepare

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
      HSetRel o.2.2 s' ∧ AStateRel pers o.2.1 lst' ∧ AStateInv pers o.2.1 ∧
      Ext lst.store lst'.store
  | .Err e => AErrSim e (x.run lst)

/-! ## The visited set -/

/-- **`nat_op_ground::seen_has`** — membership in the visited set. -/
theorem seen_has_refines {rm ls e v} (hs : HSetRel rm ls)
    (h : frontend.nat_op_ground.seen_has rm e = ok v) :
    v = ls.contains (absEIdx e) := by sorry

/-! ## The constant walk

`usedConstsGo` over `view`, with `used_consts_node` and `used_consts_two` as
the port's two extra splits (extraction rule 5: the probe's borrow must be
dead before the descent mutates the table).  Neither has a twin, so both are
stated against the twin's own arm. -/

/-- **`nat_op_ground::used_consts_go` refines `usedConstsGo`**
(`Arena/Frontend/NatOpGround.lean:50-71`). -/
theorem used_consts_go_refines {pers rst lst seen ls acc fuel e o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hs : HSetRel seen ls)
    (h : frontend.nat_op_ground.used_consts_go pers rst seen acc fuel e = ok o) :
    UOut lst o (usedConstsGo ls (absNIdxArr acc) (absU fuel) (absEIdx e)) := by
  sorry

/-- **`used_consts_node`** — the port-only split at a resolved view: the twin's
`match ← view e with` arms, inline. -/
theorem used_consts_node_refines {pers rst lst seen ls acc fuel e o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hs : HSetRel seen ls)
    (h : frontend.nat_op_ground.used_consts_node pers rst seen acc fuel e = ok o) :
    UOut lst o (usedConstsGo ls (absNIdxArr acc) (absU fuel + 1) (absEIdx e)) := by
  sorry

/-- **`used_consts_two`** — the twin's four identical two-child `match` nests,
as one function. -/
theorem used_consts_two_refines {pers rst lst seen ls acc fuel a b o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hs : HSetRel seen ls)
    (h : frontend.nat_op_ground.used_consts_two pers rst seen acc fuel a b = ok o) :
    UOut lst o (do
      let (s, acc) ← usedConstsGo ls (absNIdxArr acc) (absU fuel) (absEIdx a)
      usedConstsGo s acc (absU fuel) (absEIdx b)) := by sorry

/-- **`used_consts_rules` refines `usedConstsRules`**
(`Arena/Frontend/NatOpGround.lean:77-83`). -/
theorem used_consts_rules_refines {pers rst lst seen ls acc rules o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hs : HSetRel seen ls)
    (h : frontend.nat_op_ground.used_consts_rules pers rst seen acc rules = ok o) :
    UOut lst o (usedConstsRules ls (absNIdxArr acc) (absIRecRuleL rules)) := by
  sorry

/-- **`used_consts_block` refines `usedConstsBlock`**
(`Arena/Frontend/NatOpGround.lean:86-96`).  The one walk of the group that
APPENDS: `toConstantVal` interns a `Sort 1` for a projection table. -/
theorem used_consts_block_refines {pers rst lst seen ls acc block o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hs : HSetRel seen ls)
    (h : frontend.nat_op_ground.used_consts_block pers rst seen acc block = ok o) :
    UOutS pers lst o (usedConstsBlock ls (absNIdxArr acc) (absICIL block)) := by
  sorry

/-- **`decl_used_consts` refines `IDeclaration.usedConsts`**
(`Arena/Frontend/NatOpGround.lean:100-106`). -/
theorem decl_used_consts_refines {pers rst lst d o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.nat_op_ground.decl_used_consts pers rst d = ok o) :
    Sim absNIdxArr (fun _ => True) pers lst o
      (IDeclaration.usedConsts (absIDeclaration d)) := by sorry

/-- **`decl_used_consts_value`** — the cited three-arm case of
`IDeclaration.usedConsts` (a definition, a theorem, an opaque), which the port
factors out because the three arms share a body. -/
theorem decl_used_consts_value_refines {pers rst lst seen ls ty v o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hs : HSetRel seen ls)
    (h : frontend.nat_op_ground.decl_used_consts_value pers rst seen ty v = ok o) :
    UOut lst o (do
      let (s, acc) ← usedConstsGo ls #[] coreWalkFuel (absEIdx ty)
      usedConstsGo s acc coreWalkFuel (absEIdx v)) := by sorry

/-! ## The trigger set -/

/-- **`nat_op_ground::is_nat_op_record` refines `isNatOpRecord`**
(`Arena/Frontend/NatOpGround.lean:111-117`). -/
theorem is_nat_op_record_refines {pers rst lst d o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.nat_op_ground.is_nat_op_record rst d = ok o) :
    Sim (Option.map absNIdx) (fun _ => True) pers lst o
      (isNatOpRecord (absIDeclaration d)) := by sorry

/-- **`nidx_contains`** — `Vec<NIdx>` membership, the twin's `List.contains`. -/
theorem nidx_contains_refines {ns n v}
    (h : frontend.nat_op_ground.nidx_contains ns n = ok v) :
    v = (absNIdxL ns).contains (absNIdx n) := by sorry

/-! ## The name index -/

/-- **`hoist_name_index` refines `nameIndex ds ∅ 0`**
(`Arena/Frontend/NatOpGround.lean:133-139`), with `insertNames` its inner
loop — the port fuses the two, which is sound because the twin's inner loop
writes only `idx`. -/
theorem hoist_name_index_refines {ds m}
    (h : frontend.nat_op_ground.hoist_name_index ds = ok m) :
    NameIdxRel m (nameIndex (absIDeclArr ds) ∅ 0) := by sorry

/-- **`idx_get`** — the name index probe. -/
theorem idx_get_refines {rm lm n o} (hr : NameIdxRel rm lm)
    (h : frontend.nat_op_ground.idx_get rm n = ok o) :
    o.map absU = lm[absNIdx n]? := by sorry

/-! ## The worklist

`hoist_close` is the twin's `hoistClosure` and `hoist_push_deps` its
`pushDeps`/`pushOne` pair; `stack_push_u64` is the port's explicit stack push,
which the twin writes as a `::`.  The twin's fuel is `ds.size * ds.size + 1`
and the port's `while` is the same recursion under `-loops-to-rec`, so the
shape step is §6 of task #97-P5-2's fuel induction and not task #87 §18's
well-founded argument. -/

/-- **`target_done`** — *"record `k` already precedes `i`"*. -/
theorem target_done_refines {rm lm k i v} (hr : TargetRel rm lm)
    (h : frontend.nat_op_ground.target_done rm k i = ok v) :
    v = (match lm[absU k]? with | some t => decide (t ≤ absU i) | none => false) := by
  sorry

/-- **`stack_push_u64`** — the explicit stack, against the twin's `::`.  The
port's `sp` is the stack POINTER: the `Vec` is grown once and reused, so the
abstraction is the prefix below `sp`. -/
theorem stack_push_u64_refines {stack sp x o}
    (h : frontend.nat_op_ground.stack_push_u64 stack sp x = ok o) :
    (o.1.val.take o.2.val).map absU = absU x :: (stack.val.take sp.val).map absU := by
  sorry

/-- **`hoist_push_deps` refines `hoistClosure.pushDeps`** followed by
`pushOne`: record `k`'s own dependencies that lie after `i`. -/
theorem hoist_push_deps_refines {rm lm used stack sp i k o}
    (hr : NameIdxRel rm lm)
    (h : frontend.nat_op_ground.hoist_push_deps rm used stack sp i k = ok o) :
    (o.1.val.take o.2.val).map absU =
      hoistClosure.pushOne lm (absU i) (absNIdxL used)
        ((stack.val.take sp.val).map absU) := by sorry

/-- **`hoist_close` refines `hoistClosure`**
(`Arena/Frontend/NatOpGround.lean:156-166`). -/
theorem hoist_close_refines {pers rst lst ds rm lm target ltarget j i o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hr : NameIdxRel rm lm) (ht : TargetRel target ltarget)
    (h : frontend.nat_op_ground.hoist_close pers rst ds rm target j i = ok o) :
    ∀ t, o.1 = .Ok t → ∃ lt lst',
      (hoistClosure (absIDeclArr ds) lm (absU i)
        ((absIDeclArr ds).size * (absIDeclArr ds).size + 1) ltarget
        [absU j]).run lst = .ok (lt, lst') ∧ TargetRel t lt ∧
      AStateRel pers o.2 lst' ∧ AStateInv pers o.2 ∧ Ext lst.store lst'.store := by
  sorry

/-- **`hoist_targets_at` refines `hoistTargetsGo.hoistDeps`** at one pinned
operation's `natOpDeps`. -/
theorem hoist_targets_at_refines {pers rst lst ds rm lm target ltarget c i o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (hr : NameIdxRel rm lm) (ht : TargetRel target ltarget)
    (h : frontend.nat_op_ground.hoist_targets_at pers rst ds rm target c i = ok o) :
    ∀ t, o.1 = .Ok t → ∃ lt lst' deps,
      (natOpDeps (absNIdx c)).run lst = .ok (deps, lst') ∧
      (hoistTargetsGo.hoistDeps (absIDeclArr ds) lm ltarget (absU i) deps).run lst'
        = .ok (lt, lst') ∧ TargetRel t lt ∧
      AStateRel pers o.2 lst' ∧ AStateInv pers o.2 ∧ Ext lst.store lst'.store := by
  sorry

/-- **`hoist_targets` refines `hoistTargets`**
(`Arena/Frontend/NatOpGround.lean:208-211`): the map from a record's index to
the earliest pinned-operation index it must precede. -/
theorem hoist_targets_refines {pers rst lst ds o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.nat_op_ground.hoist_targets pers rst ds = ok o) :
    ∀ t, o.1 = .Ok t → ∃ lt lst',
      (hoistTargets (absIDeclArr ds)).run lst = .ok (lt, lst') ∧ TargetRel t lt ∧
      AStateRel pers o.2 lst' ∧ AStateInv pers o.2 ∧ Ext lst.store lst'.store := by
  sorry

/-! ## The reorder

Nine pure functions against the twin's five.  `apply_hoist`'s bucket pass is
`List.mergeSort` — task #87 §5's `hoistBuckets_eq_mergeSort`, the same
argument at handles: the keys are pairwise distinct because each carries its
own index, so `Pairwise` + `Perm` identifies the two orders. -/

/-- **`hoist_key` refines `hoistKey`** (`NatOpGround.lean:218-221`). -/
theorem hoist_key_refines {rm lm k o} (hr : TargetRel rm lm)
    (h : frontend.nat_op_ground.hoist_key rm k = ok o) :
    (absU o.1, absU o.2.1, absU o.2.2) = hoistKey lm (absU k) := by sorry

/-- **`hoist_lt` refines `hoistLt`** (`NatOpGround.lean:225-229`). -/
theorem hoist_lt_refines {rm lm a b v} (hr : TargetRel rm lm)
    (h : frontend.nat_op_ground.hoist_lt rm a b = ok v) :
    v = hoistLt lm (absU a) (absU b) := by sorry

/-- **`target_is`** — *"record `k`'s target is `t`"*, the port's own test. -/
theorem target_is_refines {rm lm k t v} (hr : TargetRel rm lm)
    (h : frontend.nat_op_ground.target_is rm k t = ok v) :
    v = (lm[absU k]? == some (absU t)) := by sorry

/-- **`hoist_moved_idxs`** — the indices the target map carries, in order. -/
theorem hoist_moved_idxs_refines {n rm lm v} (hr : TargetRel rm lm)
    (h : frontend.nat_op_ground.hoist_moved_idxs n rm = ok v) :
    v.val.map absU = (List.range n.val).filter (fun k => lm.contains k) := by sorry

/-- **`hoist_order`** — the sorted order `applyHoist` sorts by.  The port's
bucket pass against the twin's `List.mergeSort` (task #87 §5). -/
theorem hoist_order_refines {n rm lm moved v} (hr : TargetRel rm lm)
    (h : frontend.nat_op_ground.hoist_order n rm moved = ok v) :
    v.val.map absU =
      (List.range n.val).mergeSort (fun a b => !hoistLt lm b a) := by sorry

/-- **`hoist_reorder` refines `reorder`** (`NatOpGround.lean:247-248`).  Task
#87 §5's precondition is the port's own: an out-of-range `order` entry makes
the port's read FAIL rather than read garbage, so the lemma needs no
hypothesis on the permutation. -/
theorem hoist_reorder_refines {ds order v}
    (h : frontend.nat_op_ground.hoist_reorder ds order = ok v) :
    absIDeclArr v = reorder (absIDeclArr ds) (order.val.map absU) := by sorry

/-- **`hoist_moved_names` refines `movedNames`** (`NatOpGround.lean:233-240`). -/
theorem hoist_moved_names_refines {ds moved rm lm v} (hr : TargetRel rm lm)
    (hm : moved.val.map absU = (List.range (absIDeclArr ds).size).filter
      (fun k => lm.contains k))
    (h : frontend.nat_op_ground.hoist_moved_names ds moved = ok v) :
    absNIdxArr v = movedNames (absIDeclArr ds) lm #[] 0 := by sorry

/-- **`apply_hoist` refines `applyHoist`** (`NatOpGround.lean:252-256`).  Task
#87 §5's two genuine preconditions are the port's own and are free at the one
call site: every target key and value below `ds.len()`. -/
theorem apply_hoist_refines {ds rm lm o} (hr : TargetRel rm lm)
    (h : frontend.nat_op_ground.apply_hoist ds rm = ok o) :
    (absIDeclArr o.1, absNIdxArr o.2) = applyHoist (absIDeclArr ds) lm := by sorry

/-- **`hoist_nat_op_ground` refines `hoistNatOpGround`**
(`Arena/Frontend/NatOpGround.lean:261-265`) — **the hoist**, and one of the
tier's named deliverables. -/
theorem hoist_nat_op_ground_refines {pers rst lst ds o}
    (hrel : AStateRel pers rst lst) (hinv : AStateInv pers rst)
    (h : frontend.nat_op_ground.hoist_nat_op_ground pers rst ds = ok o) :
    Sim (fun p => (absIDeclArr p.1, absNIdxArr p.2)) (fun _ => True) pers lst o
      (hoistNatOpGround (absIDeclArr ds)) := by sorry


end ConRon.Refine2.Frontend

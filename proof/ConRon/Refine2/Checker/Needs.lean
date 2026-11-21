/-
# `ConRon.Refine2.Checker.Needs` — Theorem 2 for what a record reads

`arena::needs` against `Arena/Needs.lean` (con-leche's `Cached/Needs.lean`): the memoised walk
`needs_go` (fuel induction, one `lockstep` per case, as `mentions_const_go` in
`Checker/Leaves.lean`), the literal's names, and the walk's state through a constant's laws and a
table.  The walk's state is related by `NeedsRel`: the memo by `LMemoRel`, the names by
`absNIdx` elementwise.
-/
import ConRon.Refine2.Checker.Top
import ConRon.Arena.Needs

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The cursor append -/

/-- `nidx_append` ⊑ `nidxAppend`, by the distance to the end of `ns`. -/
theorem nidx_append_val (ns : alloc.vec.Vec arena.handle.NIdx) :
    ∀ (m : Nat) (acc : alloc.vec.Vec arena.handle.NIdx) (i stop : Std.Usize) {r},
      ns.val.length - i.val = m → arena.needs.nidx_append acc ns i stop = ok r →
      r.val.map absNIdx =
        nidxAppend (acc.val.map absNIdx) (ns.val.map absNIdx) i.val stop.val := by
  intro m
  induction m with
  | zero =>
    intro acc i stop r hm h
    rw [arena.needs.nidx_append.eq_def] at h
    simp only [nidxAppend]
    by_cases hs : i ≥ stop
    · simp only [hs, ↓reduceIte] at h
      cases Result.ok_injective h
      have : stop.val - i.val = 0 := by scalar_tac
      simp [this]
    · simp only [hs, ↓reduceIte] at h
      have hl : i ≥ alloc.vec.Vec.len ns := by scalar_tac
      simp only [hl, ↓reduceIte] at h
      cases Result.ok_injective h
      have : ns.val.length ≤ i.val := by scalar_tac
      simp [this]
  | succ m ih =>
    intro acc i stop r hm h
    rw [arena.needs.nidx_append.eq_def] at h
    simp only [nidxAppend]
    by_cases hs : i ≥ stop
    · simp only [hs, ↓reduceIte] at h
      cases Result.ok_injective h
      have : stop.val - i.val = 0 := by scalar_tac
      simp [this]
    · simp only [hs, ↓reduceIte] at h
      have hl : ¬ i ≥ alloc.vec.Vec.len ns := by scalar_tac
      simp only [hl, ↓reduceIte] at h
      have hlt : i.val < ns.val.length := by scalar_tac
      obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hnv : ns.val[i.val]? = some n := vec_index_some hn
      obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hn1v : n1 = n := dupId_nidx _ _ hn1
      obtain ⟨acc1, hacc1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hacc1v : acc1.val = acc.val ++ [n1] := ConRon.Refine.vec_push_val hacc1
      obtain ⟨i2, hi2, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have hi2v := ConRon.Refine.Nat.uadd_val hi2
      have := ih acc1 i2 stop (by simp at hi2v; omega) h
      rw [this, hacc1v, hn1v, hi2v]
      simp only [nidxAppend, List.map_append, List.map_cons, List.map_nil, List.append_assoc]
      congr 1
      have hd : (ns.val.map absNIdx).drop i.val =
          absNIdx n :: (ns.val.map absNIdx).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hlt)]
        simp [List.getElem?_eq_some_iff.mp hnv |>.2]
      have hk : stop.val - i.val = (stop.val - (i.val + 1)) + 1 := by scalar_tac
      rw [hd, hk, List.take_succ_cons]
      rfl

open Lockstep in
/-- `nidx_append` in the lockstep shape: a Rust-only value step, its answer the twin's
`nidxAppend`. -/
@[lockstep] theorem nidx_append_spec (acc ns : alloc.vec.Vec arena.handle.NIdx)
    (i stop : Std.Usize) :
    LSP (arena.needs.nidx_append acc ns i stop)
      (fun r => absNIdxList r = nidxAppend (absNIdxList acc) (absNIdxList ns) i.val stop.val) :=
  fun _ h => nidx_append_val ns _ acc i stop rfl h

/-! ## A literal's names -/

open Lockstep in
/-- `lit_needs` ⊑ `litNeeds`. -/
@[lockstep] theorem lit_needs_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (l : kernel.expr.Literal)
    (acc : alloc.vec.Vec arena.handle.NIdx) :
    LSR pers (fun a b => b = absNIdxList a) (arena.needs.lit_needs st l acc) st lst
      (litNeeds (ConRon.Refine.absLiteral l) (absNIdxList acc)) := by
  apply LSR.of_LS
  rw [arena.needs.lit_needs, litNeeds]
  lockstep_core

/-! ## The walk -/

/-- **The walk's state, related**: the memo by `LMemoRel`, the names elementwise. -/
abbrev NeedsOut (a : ron.hashmap2.HashMap2 arena.handle.EIdx Bool × alloc.vec.Vec arena.handle.NIdx)
    (b : Std.HashMap EIdx Bool × List NIdx) : Prop :=
  ∃ m', ExprOps.LMemoRel a.1 m' ∧ b = (m', absNIdxList a.2)

open Lockstep in
/-- `needs_go` ⊑ `needsGo`, by induction on the fuel. -/
theorem needs_go_aux (n : Nat) :
    ∀ {pers : arena.store.PersTier} {st : arena.monad.AState} {lst : AState}
      (rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool) (lm : Std.HashMap EIdx Bool)
      (acc : alloc.vec.Vec arena.handle.NIdx) (fuel : Std.U64) (h : arena.handle.EIdx),
      fuel.val = n → AStateRel₀ pers st lst → AStateInv pers st → ExprOps.LMemoRel rm lm →
      LS pers NeedsOut (arena.needs.needs_go pers st rm acc fuel h) lst
        (needsGo lm (absNIdxList acc) n (absEIdx h)) := by
  induction n with
  | zero =>
    intro pers st lst rm lm acc fuel h hn hrel hinv hm
    rw [arena.needs.needs_go, needsGo]
    lockstep
  | succ m ih =>
    intro pers st lst rm lm acc fuel h hn hrel hinv hm
    rw [arena.needs.needs_go, needsGo]
    unfold arena.needs.needs_node
    lockstep
    -- the `.const` arm: the Rust's `push` against the twin's `acc ++ [n]`
    exact LS.pure ⟨_, hm, by simp [absNIdxList, hP]⟩ hrel hinv

open Lockstep in
@[lockstep] theorem needs_go_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {rm : ron.hashmap2.HashMap2 arena.handle.EIdx Bool}
    {lm : Std.HashMap EIdx Bool} (hm : ExprOps.LMemoRel rm lm)
    (acc : alloc.vec.Vec arena.handle.NIdx) (fuel : Std.U64) (h : arena.handle.EIdx) :
    LS pers NeedsOut (arena.needs.needs_go pers st rm acc fuel h) lst
      (needsGo lm (absNIdxList acc) (absU fuel) (absEIdx h)) :=
  needs_go_aux _ rm lm acc fuel h rfl hrel hinv hm

/-! ## The walk's state -/

/-- **`arena::needs::NeedsSt` against the twin's `NeedsSt`**: the memo by `LMemoRel`, the
names elementwise. -/
structure NSRel (a : arena.needs.NeedsSt) (b : NeedsSt) : Prop where
  seen : ExprOps.LMemoRel a.seen b.seen
  acc : b.acc = absNIdxList a.acc

open Lockstep in
/-- `needs_st_empty` ⊑ `NeedsSt.empty`. -/
@[lockstep] theorem needs_st_empty_spec :
    LSP arena.needs.needs_st_empty (fun a => NSRel a NeedsSt.empty) := by
  intro a h
  rw [arena.needs.needs_st_empty] at h
  obtain ⟨hm, hhm, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  have hn := ConRon.Refine.HashMap2.new_refines
    (HashableInst := arena.handle.EIdx.Insts.Con_ron_coreRonHashmapHashable)
    (K := arena.handle.EIdx) (V := Bool) (m' := hm) hhm
  refine ⟨⟨fun k _ => ?_, hn.1⟩, ?_⟩
  · simp [NeedsSt.empty, hn.2.2 k]
  · simp [NeedsSt.empty, absNIdxList]

open Lockstep in
/-- `needs_expr` ⊑ `NeedsSt.expr`. -/
@[lockstep] theorem needs_expr_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {x : arena.needs.NeedsSt} {y : NeedsSt}
    (hm : NSRel x y) (e : arena.handle.EIdx) :
    LS pers NSRel (arena.needs.needs_expr pers st x e) lst
      (y.expr (absEIdx e)) := by
  obtain ⟨hs, ha⟩ := hm
  obtain ⟨ys, ya⟩ := y
  simp only at hs ha
  subst ha
  rw [arena.needs.needs_expr, NeedsSt.expr, ← core_walk_fuel_abs]
  lockstep
  exact LS.pure ⟨‹_›, rfl⟩ ‹_› ‹_›

open Lockstep in
/-- `needs_names` ⊑ `NeedsSt.names`. -/
@[lockstep] theorem needs_names_spec (x : arena.needs.NeedsSt) (ns : alloc.vec.Vec arena.handle.NIdx)
    {y : NeedsSt} (hm : NSRel x y) :
    LSP (arena.needs.needs_names x ns)
      (fun a => NSRel a (y.names (absNIdxList ns))) := by
  intro a h
  rw [arena.needs.needs_names] at h
  obtain ⟨v, hv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  refine ⟨hm.seen, ?_⟩
  rw [nidx_append_spec _ _ _ _ _ hv]
  simp [NeedsSt.names, absNIdxList, alloc.vec.Vec.len, hm.acc]

open Lockstep in
/-- `needs_name` ⊑ `NeedsSt.name`. -/
@[lockstep] theorem needs_name_spec (x : arena.needs.NeedsSt) (n : arena.handle.NIdx)
    {y : NeedsSt} (hm : NSRel x y) :
    LSP (arena.needs.needs_name x n)
      (fun a => NSRel a (y.name (absNIdx n))) := by
  intro a h
  rw [arena.needs.needs_name] at h
  obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨acc, hacc, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  cases Result.ok_injective h
  refine ⟨hm.seen, ?_⟩
  rw [dupId_nidx _ _ hn1] at hacc
  simp [NeedsSt.name, absNIdxList, ConRon.Refine.vec_push_val hacc, hm.acc]

open Lockstep in
/-- `needs_exprs` ⊑ `NeedsSt.exprs`, from the cursor on. -/
@[lockstep] theorem needs_exprs_ls {pers} (es : alloc.vec.Vec arena.handle.EIdx) (i : Std.Usize) :
    ∀ {st lst} (_hrel : AStateRel₀ pers st lst) (_hinv : AStateInv pers st)
      {x : arena.needs.NeedsSt} {y : NeedsSt} (_hm : NSRel x y),
      LS pers NSRel (arena.needs.needs_exprs pers st x es i) lst
        (y.exprs ((es.val.drop i.val).map absEIdx)) := by
  refine cursor_induction (fun i : Std.Usize => i.val) es.val.length
    (fun i (_ : Unit) => ∀ {st lst} (_hrel : AStateRel₀ pers st lst) (_hinv : AStateInv pers st)
      {x : arena.needs.NeedsSt} {y : NeedsSt} (_hm : NSRel x y),
      LS pers NSRel (arena.needs.needs_exprs pers st x es i) lst
        (y.exprs ((es.val.drop i.val).map absEIdx))) ?_ ?_ i ()
  · intro i _ hn st lst hrel hinv x y hm
    rw [arena.needs.needs_exprs.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len es by scalar_tac),
      List.drop_eq_nil_of_le hn, List.map_nil, NeedsSt.exprs]
    exact LS.pure hm hrel hinv
  · intro i _ hlt ih st lst hrel hinv x y hm
    have ih' : ∀ j : Std.Usize, j.val = i.val + 1 → ∀ {st lst} (_hrel : AStateRel₀ pers st lst)
        (_hinv : AStateInv pers st) {x : arena.needs.NeedsSt} {y : NeedsSt}
        (_hm : NSRel x y),
        LS pers NSRel (arena.needs.needs_exprs pers st x es j) lst
          (y.exprs ((es.val.drop j.val).map absEIdx)) :=
      fun j hj => ih j () hj
    clear ih
    rw [arena.needs.needs_exprs.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len es by scalar_tac),
      List.drop_eq_getElem_cons hlt, List.map_cons, NeedsSt.exprs]
    lockstep

open Lockstep in
/-- `needs_rule` ⊑ `NeedsSt.rule`. -/
@[lockstep] theorem needs_rule_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {x : arena.needs.NeedsSt} {y : NeedsSt}
    (hm : NSRel x y) (r : arena.env.IRecRule) :
    LS pers NSRel (arena.needs.needs_rule pers st x r) lst
      (y.rule (absIRecRule r)) := by
  rw [arena.needs.needs_rule, NeedsSt.rule]
  cases hf : r.fire <;> simp only [absIRecRule, hf, absIRecRuleFire] <;> lockstep

open Lockstep in
/-- `needs_rules` ⊑ `NeedsSt.rules`, from the cursor on. -/
@[lockstep] theorem needs_rules_ls {pers} (rs : alloc.vec.Vec arena.env.IRecRule) (i : Std.Usize) :
    ∀ {st lst} (_hrel : AStateRel₀ pers st lst) (_hinv : AStateInv pers st)
      {x : arena.needs.NeedsSt} {y : NeedsSt} (_hm : NSRel x y),
      LS pers NSRel (arena.needs.needs_rules pers st x rs i) lst
        (y.rules ((rs.val.drop i.val).map absIRecRule)) := by
  refine cursor_induction (fun i : Std.Usize => i.val) rs.val.length
    (fun i (_ : Unit) => ∀ {st lst} (_hrel : AStateRel₀ pers st lst) (_hinv : AStateInv pers st)
      {x : arena.needs.NeedsSt} {y : NeedsSt} (_hm : NSRel x y),
      LS pers NSRel (arena.needs.needs_rules pers st x rs i) lst
        (y.rules ((rs.val.drop i.val).map absIRecRule)))
    ?_ ?_ i ()
  · intro i _ hn st lst hrel hinv x y hm
    rw [arena.needs.needs_rules.eq_def,
      ite_eq_left (show i ≥ alloc.vec.Vec.len rs by scalar_tac),
      List.drop_eq_nil_of_le hn, List.map_nil, NeedsSt.rules]
    exact LS.pure hm hrel hinv
  · intro i _ hlt ih st lst hrel hinv x y hm
    have ih' : ∀ j : Std.Usize, j.val = i.val + 1 → ∀ {st lst} (_hrel : AStateRel₀ pers st lst)
        (_hinv : AStateInv pers st) {x : arena.needs.NeedsSt} {y : NeedsSt}
        (_hm : NSRel x y),
        LS pers NSRel (arena.needs.needs_rules pers st x rs j) lst
          (y.rules ((rs.val.drop j.val).map absIRecRule)) :=
      fun j hj => ih j () hj
    clear ih
    rw [arena.needs.needs_rules.eq_def,
      ite_eq_right (show ¬ i ≥ alloc.vec.Vec.len rs by scalar_tac),
      List.drop_eq_getElem_cons hlt, List.map_cons, NeedsSt.rules]
    lockstep

/-! ## A pinned constant's fast-path names -/

open Lockstep in
/-- `pin_footprint_reduce` ⊑ `pinFootprintReduce`. -/
@[lockstep] theorem pin_footprint_reduce_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : arena.handle.NIdx) (xs : alloc.vec.Vec arena.handle.NIdx) :
    LS pers (fun a b => b = absNIdxList a) (arena.needs.pin_footprint_reduce st n xs) lst
      (pinFootprintReduce (absNIdx n) (absNIdxList xs)) := by
  rw [arena.needs.pin_footprint_reduce, pinFootprintReduce]
  lockstep

open Lockstep in
/-- `pin_footprint_nat` ⊑ `pinFootprintNat`. -/
@[lockstep] theorem pin_footprint_nat_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : arena.handle.NIdx) (dms : alloc.vec.Vec arena.handle.NIdx) :
    LS pers (fun a b => b = absNIdxList a) (arena.needs.pin_footprint_nat st n dms) lst
      (pinFootprintNat (absNIdx n) (absNIdxList dms)) := by
  rw [arena.needs.pin_footprint_nat, pinFootprintNat]
  lockstep

open Lockstep in
/-- `pin_footprint` ⊑ `pinFootprint`. -/
@[lockstep] theorem pin_footprint_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (n : arena.handle.NIdx) :
    LS pers (fun a b => b = absNIdxList a) (arena.needs.pin_footprint st n) lst
      (pinFootprint (absNIdx n)) := by
  rw [arena.needs.pin_footprint, pinFootprint]
  lockstep

/-! ## A constant's laws, a table -/

open Lockstep in
/-- `needs_const` ⊑ `NeedsSt.const`. -/
@[lockstep] theorem needs_const_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {x : arena.needs.NeedsSt} {y : NeedsSt}
    (hm : NSRel x y) (ci : arena.env.IConstantInfo) :
    LS pers NSRel (arena.needs.needs_const pers st x ci) lst
      (y.const (absIConstantInfo ci)) := by
  rw [arena.needs.needs_const, NeedsSt.const]
  cases ci <;> simp only [absIConstantInfo] <;> lockstep

open Lockstep in
/-- `needs_table` ⊑ `NeedsSt.table`. -/
@[lockstep] theorem needs_table_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) {x : arena.needs.NeedsSt} {y : NeedsSt}
    (hm : NSRel x y) (t : arena.env.IProjTable) :
    LS pers NSRel (arena.needs.needs_table pers st x t) lst
      (y.table (absIProjTable t)) := by
  rw [arena.needs.needs_table, NeedsSt.table]
  lockstep

end ConRon.Refine2

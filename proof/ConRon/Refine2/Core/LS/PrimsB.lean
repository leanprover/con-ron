/-
# `ConRon.Refine2.Core.LS.PrimsB` — region B's primitive pairs (task #97-P5-Core round 5)

The `@[lockstep]` pairs `Core/LS/Lits.lean` (the literal guards, the literal
constructor forms and `reduceNat`) needs and that no shared prims file has:

* the pin table's readers over `AStateRel₀` (`pin_at_ls` and one wrapper per
  slot) — `Refine2/Checker/Pins.lean`'s `pin_at_refines` is the same proof over
  `AStateRel`, and reads only `hrel.pins`;
* `LS.of_read`: a Rust wrapper `let r ← read st; ok (r, st)` against the twin's
  read itself;
* handle equality (`NIdx`/`LsIdx`'s `eq2`) and `ron::nat`'s operations as
  Rust-only `LSP` facts, from `Refine/Nat.lean`;
* the two typed projections the region reads (`view_lit`, `view_const`), the
  literal one carrying the stored literal's `LiteralWF` (`StoreInv`'s
  `nodesP` at the `lits` table) — the representation fact every `ron::nat`
  operation on a literal needs;
* the store-level step `i_constant_info_to_constant_val` (`LSS`), from the
  foundation's `intern_l_node_run₀` / `intern_e_sort_run₀`;
* the `Vec` length tests the literal guards make (`vec_len_*`), as
  `lockstep_simp` equations against the twin's `isEmpty` / `length` tests.
-/
import ConRon.Refine2.Core.LS.Prims

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep.PB

open ConRon.Arena ConRon.Refine2 ConRon.Refine2.Lockstep

/-! ## A Rust read handed back with its state -/

/-- `do let r ← read; ok (r, st)` (every `*_name` wrapper, `nat_pred_name`
…) against the twin's read itself. -/
theorem LS.of_read {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError)}
    {st : arena.monad.AState} {lst : AState} {x : AM β}
    (h : LSR pers R m st lst x) :
    LS pers R (do let r ← m; ok (r, st)) lst x := by
  intro o st' hm
  obtain ⟨r, hr, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have h2 := Result.ok_injective hm
  simp only [Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  exact h _ hr

/-! ## The pin table -/

/-- `pin_at` against `pinAt`: the bounds test and `PinsRel.names`. -/
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

/-- One slot of the table. -/
theorem pin_slot_ls {pers st lst} {i : Std.Usize} {k : Nat} (hk : absSz i = k)
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a) (arena.pins.pin_at st i) st lst (pinAt k) := by
  rw [← hk]; exact pin_at_ls hrel hinv i

/-- The slot constants' values, one per reader (`irreducible` on the Rust side). -/
local macro "pin_slot" rust:ident twin:ident slot:ident : command =>
  `(@[lockstep] theorem $(Lean.mkIdent (rust.getId.componentsRev.head!.appendAfter "_ls")) {pers st lst}
        (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
        LSR pers (fun a b => b = absNIdx a) ($rust st) st lst $twin := by
      rw [$rust:ident, $twin:ident]
      exact pin_slot_ls (by show (($slot : Std.Usize)).val = _; rw [$slot:ident]; rfl) hrel hinv)

pin_slot arena.pins.pin_nat pinNat arena.pins.PIN_NAT
pin_slot arena.pins.pin_nat_zero pinNatZero arena.pins.PIN_NAT_ZERO
pin_slot arena.pins.pin_nat_succ pinNatSucc arena.pins.PIN_NAT_SUCC
pin_slot arena.pins.pin_string pinString arena.pins.PIN_STRING
pin_slot arena.pins.pin_string_of_list pinStringOfList arena.pins.PIN_STRING_OF_LIST
pin_slot arena.pins.pin_list pinList arena.pins.PIN_LIST
pin_slot arena.pins.pin_list_nil pinListNil arena.pins.PIN_LIST_NIL
pin_slot arena.pins.pin_list_cons pinListCons arena.pins.PIN_LIST_CONS
pin_slot arena.pins.pin_char pinChar arena.pins.PIN_CHAR
pin_slot arena.pins.pin_char_of_nat pinCharOfNat arena.pins.PIN_CHAR_OF_NAT
pin_slot arena.pins.pin_nat_pred pinNatPred arena.pins.PIN_NAT_PRED
pin_slot arena.pins.pin_nat_add pinNatAdd arena.pins.PIN_NAT_ADD
pin_slot arena.pins.pin_nat_sub pinNatSub arena.pins.PIN_NAT_SUB
pin_slot arena.pins.pin_nat_mul pinNatMul arena.pins.PIN_NAT_MUL
pin_slot arena.pins.pin_nat_pow pinNatPow arena.pins.PIN_NAT_POW
pin_slot arena.pins.pin_nat_beq pinNatBeq arena.pins.PIN_NAT_BEQ
pin_slot arena.pins.pin_nat_ble pinNatBle arena.pins.PIN_NAT_BLE
pin_slot arena.pins.pin_nat_div pinNatDiv arena.pins.PIN_NAT_DIV
pin_slot arena.pins.pin_nat_mod pinNatMod arena.pins.PIN_NAT_MOD
pin_slot arena.pins.pin_nat_gcd pinNatGcd arena.pins.PIN_NAT_GCD
pin_slot arena.pins.pin_nat_land pinNatLand arena.pins.PIN_NAT_LAND
pin_slot arena.pins.pin_nat_lor pinNatLor arena.pins.PIN_NAT_LOR
pin_slot arena.pins.pin_nat_xor pinNatXor arena.pins.PIN_NAT_XOR
pin_slot arena.pins.pin_nat_shift_left pinNatShiftLeft arena.pins.PIN_NAT_SHIFT_LEFT
pin_slot arena.pins.pin_nat_shift_right pinNatShiftRight arena.pins.PIN_NAT_SHIFT_RIGHT

/-! ## Handle equality -/

@[lockstep] theorem nidx_eq2_spec (a b : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun r => r = (absNIdx a == absNIdx b)) := by
  intro r h
  have := nidx_eq2 a b r trivial trivial h
  rw [this]
  by_cases hab : a = b
  · subst hab; simp
  · have : absNIdx a ≠ absNIdx b := fun hc => hab (absNIdx_inj hc)
    simp [hab, this]

@[lockstep] theorem lsidx_eq2_spec (a b : arena.handle.LsIdx) :
    LSP (arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun r => r = (absLsIdx a == absLsIdx b)) := by
  intro r h
  have := lsidx_eq2 a b r trivial trivial h
  rw [this]
  by_cases hab : a = b
  · subst hab; simp
  · have : absLsIdx a ≠ absLsIdx b := fun hc => hab (absLsIdx_inj hc)
    simp [hab, this]

@[lockstep] theorem eidx_eq2_spec (a b : arena.handle.EIdx) :
    LSP (arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun r => r = (absEIdx a == absEIdx b)) := by
  intro r h
  have := eidx_eq2 a b r trivial trivial h
  rw [this]
  by_cases hab : a = b
  · subst hab; simp
  · have : absEIdx a ≠ absEIdx b := fun hc => hab (absEIdx_inj hc)
    simp [hab, this]

@[lockstep] theorem dup2_nidx (h : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun e he => dupId_nidx _ _ he

@[lockstep] theorem dup2_lidx (h : arena.handle.LIdx) :
    LSP (arena.handle.LIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun e he => dupId_lidx _ _ he

@[lockstep] theorem dup2_lsidx (h : arena.handle.LsIdx) :
    LSP (arena.handle.LsIdx.Insts.Con_ron_coreRonHashmapDup.dup2 h) (fun e => e = h) :=
  fun e he => dupId_lsidx _ _ he

/-! ## `ron::nat`, as Rust-only facts about `Nat.toNat` -/

open ConRon.Refine.Nat in
@[lockstep] theorem nat_is_zero_spec (a : ron.nat.Nat) (ha : NatWF a) :
    LSP (ron.nat.is_zero a) (fun b => b = decide (toNat a = 0)) :=
  fun _ h => is_zero_refines ha h

open ConRon.Refine.Nat in
@[lockstep] theorem nat_clone_spec (a : ron.nat.Nat) :
    LSP (ron.nat.clone a) (fun n => (NatWF a → NatWF n) ∧ toNat n = toNat a) := by
  intro n h
  have := clone_refines h
  refine ⟨fun ha => ?_, this.2⟩
  unfold NatWF at *; rw [this.1]; exact ha

open ConRon.Refine.Nat in
@[lockstep] theorem nat_zero_spec :
    LSP ron.nat.zero (fun n => NatWF n ∧ toNat n = 0) :=
  fun _ h => (zero_refines h).symm

open ConRon.Refine.Nat in
@[lockstep] theorem nat_one_spec :
    LSP ron.nat.one (fun n => NatWF n ∧ toNat n = 1) :=
  fun _ h => (one_refines h).symm

open ConRon.Refine.Nat in
@[lockstep] theorem nat_from_u64_spec (x : Std.U64) :
    LSP (ron.nat.from_u64 x) (fun n => NatWF n ∧ toNat n = x.val) :=
  fun _ h => (from_u64_refines h).symm

open ConRon.Refine.Nat in
@[lockstep] theorem nat_to_u64_spec (a : ron.nat.Nat) (ha : NatWF a) :
    LSP (ron.nat.to_u64 a)
      (fun o => (∃ x : Std.U64, o = some x ∧ x.val = toNat a) ∨ (o = none ∧ 2 ^ 64 ≤ toNat a)) :=
  fun _ h => to_u64_refines ha h

open ConRon.Refine.Nat in
@[lockstep] theorem nat_beq_spec (a b : ron.nat.Nat) (ha : NatWF a) (hb : NatWF b) :
    LSP (ron.nat.beq a b) (fun r => r = decide (toNat a = toNat b)) :=
  fun _ h => beq_refines ha hb h

open ConRon.Refine.Nat in
@[lockstep] theorem nat_ble_spec (a b : ron.nat.Nat) (ha : NatWF a) (hb : NatWF b) :
    LSP (ron.nat.ble a b) (fun r => r = decide (toNat a ≤ toNat b)) :=
  fun _ h => ble_refines ha hb h

open ConRon.Refine.Nat in
@[lockstep] theorem nat_blt_spec (a b : ron.nat.Nat) (ha : NatWF a) (hb : NatWF b) :
    LSP (ron.nat.blt a b) (fun r => r = decide (toNat a < toNat b)) :=
  fun _ h => blt_refines ha hb h

open ConRon.Refine.Nat in
@[lockstep] theorem nat_add_spec (a b : ron.nat.Nat) :
    LSP (ron.nat.add a b) (fun c => NatWF c ∧ toNat c = toNat a + toNat b) :=
  fun _ h => (add_refines h).symm

open ConRon.Refine.Nat in
@[lockstep] theorem nat_sub_spec (a b : ron.nat.Nat) (ha : NatWF a) (hb : NatWF b) :
    LSP (ron.nat.sub a b) (fun c => NatWF c ∧ toNat c = toNat a - toNat b) :=
  fun _ h => (sub_refines ha hb h).symm

open ConRon.Refine.Nat in
@[lockstep] theorem nat_pred_spec (a : ron.nat.Nat) (ha : NatWF a) :
    LSP (ron.nat.pred a) (fun c => NatWF c ∧ toNat c = toNat a - 1) :=
  fun _ h => (pred_refines ha h).symm

open ConRon.Refine.Nat in
@[lockstep] theorem nat_mul_spec (a b : ron.nat.Nat) :
    LSP (ron.nat.mul a b) (fun c => NatWF c ∧ toNat c = toNat a * toNat b) :=
  fun _ h => (mul_refines h).symm

open ConRon.Refine.Nat in
@[lockstep] theorem nat_pow_spec (a : ron.nat.Nat) (e : Std.U64) :
    LSP (ron.nat.pow a e) (fun c => NatWF c ∧ toNat c = toNat a ^ e.val) :=
  fun _ h => (pow_refines _ a _ e rfl h).symm

open ConRon.Refine.Nat in
@[lockstep] theorem nat_div_spec (a b : ron.nat.Nat) (ha : NatWF a) (hb : NatWF b) :
    LSP (ron.nat.div a b) (fun c => NatWF c ∧ toNat c = toNat a / toNat b) :=
  fun _ h => (div_refines ha hb h).symm

open ConRon.Refine.Nat in
@[lockstep] theorem nat_modulo_spec (a b : ron.nat.Nat) (ha : NatWF a) (hb : NatWF b) :
    LSP (ron.nat.modulo a b) (fun c => NatWF c ∧ toNat c = toNat a % toNat b) :=
  fun _ h => (modulo_refines ha hb h).symm

open ConRon.Refine.Nat in
@[lockstep] theorem nat_gcd_spec (a b : ron.nat.Nat) (ha : NatWF a) (hb : NatWF b) :
    LSP (ron.nat.gcd a b) (fun c => NatWF c ∧ toNat c = Nat.gcd (toNat a) (toNat b)) :=
  fun _ h => (gcd_refines _ a b _ rfl ha hb h).symm

open ConRon.Refine.Nat in
@[lockstep] theorem nat_land_spec (a b : ron.nat.Nat) :
    LSP (ron.nat.land a b) (fun c => NatWF c ∧ toNat c = Nat.land (toNat a) (toNat b)) :=
  fun _ h => (land_refines h).symm

open ConRon.Refine.Nat in
@[lockstep] theorem nat_lor_spec (a b : ron.nat.Nat) :
    LSP (ron.nat.lor a b) (fun c => NatWF c ∧ toNat c = Nat.lor (toNat a) (toNat b)) :=
  fun _ h => (lor_refines h).symm

open ConRon.Refine.Nat in
@[lockstep] theorem nat_xor_spec (a b : ron.nat.Nat) :
    LSP (ron.nat.xor a b) (fun c => NatWF c ∧ toNat c = Nat.xor (toNat a) (toNat b)) :=
  fun _ h => (xor_refines h).symm

open ConRon.Refine.Nat in
@[lockstep] theorem nat_shift_left_spec (a : ron.nat.Nat) (k : Std.U64) :
    LSP (ron.nat.shift_left a k) (fun c => NatWF c ∧ toNat c = Nat.shiftLeft (toNat a) k.val) :=
  fun _ h => (shift_left_refines h).symm

open ConRon.Refine.Nat in
@[lockstep] theorem nat_shift_right_spec (a : ron.nat.Nat) (k : Std.U64) :
    LSP (ron.nat.shift_right a k) (fun c => NatWF c ∧ toNat c = Nat.shiftRight (toNat a) k.val) :=
  fun _ h => (shift_right_refines h).symm

@[lockstep] theorem literal_nat_spec (n : ron.nat.Nat) :
    LSP (kernel.expr.literal_nat n) (fun l => l = .NatVal n) := by
  intro l h
  rw [kernel.expr.literal_nat] at h
  simp only [ConRon.Refine.ptr_new_eq, bind_tc_ok] at h
  exact (Result.ok_injective h).symm

@[lockstep] theorem arc_deref_spec {T : Type} (A : Type) (x : alloc.sync.Arc T) :
    LSP (alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref A x) (fun y => y = x) :=
  fun _ h => (Result.ok_injective h).symm

/-! ## The typed projections -/

theorem etables_get_lit_abs {rt lt} (hrel : ETablesRel rt lt)
    {i : arena.handle.EIdx} {o}
    (h : arena.store.ETables.get_lit rt i = ok o) :
    lt.getLit (absEIdx i) = o.map ConRon.Refine.absLiteral := by
  rw [arena.store.ETables.get_lit] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hnode := tbl_node_abs hrel.lits hp
  rw [ETables.getLit, eidx_idxNat hn, hnode]
  cases hpc : p with
  | none =>
    rw [hpc] at h
    have h2 : (none : Option kernel.expr.Literal) = o := Result.ok_injective h
    subst h2
    rfl
  | some r =>
    rw [hpc] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h2 : some x = o := Result.ok_injective h
    subst h2
    rw [ConRon.Refine.Expr.literal_dup_eq hx]
    rfl

theorem etables_get_lit_wf {rt} (hinv : ETablesInv rt)
    {i : arena.handle.EIdx} {o}
    (h : arena.store.ETables.get_lit rt i = ok o) :
    ∀ l, o = some l → ConRon.Refine.LiteralWF l := by
  rw [arena.store.ETables.get_lit] at h
  obtain ⟨n, hn, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hwf := tbl_node_wf hinv.lits hp
  cases hpc : p with
  | none =>
    rw [hpc] at h
    have h2 : (none : Option kernel.expr.Literal) = o := Result.ok_injective h
    subst h2
    intro l hl; cases hl
  | some r =>
    rw [hpc] at h
    obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    have h2 : some x = o := Result.ok_injective h
    subst h2
    intro l hl
    cases hl
    rw [ConRon.Refine.Expr.literal_dup_eq hx]
    exact hwf r (by rw [hpc])

theorem estore_view_lit_abs {pers rs ls} (hrel : StoreRel pers rs ls)
    {i : arena.handle.EIdx} {o}
    (h : arena.store.EStore.view_lit rs pers i = ok o) :
    ls.viewLit (absEIdx i) = o.map ConRon.Refine.absLiteral := by
  rw [arena.store.EStore.view_lit] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  have hb2 := eidx_is_persistent_abs hb
  rw [EStore.viewLit]
  split at h <;> rename_i hbv
  · rw [if_pos (show (absEIdx i).isPersistent = true by rw [hb2, hbv]), EStore.persGetLit]
    rw [arena.store.EStore.pers_get_lit] at h
    have h3 : arena.store.ETables.get_lit (rPersE pers rs) i = ok o := by
      unfold rPersE
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact etables_get_lit_abs hrel.perst h3
  · rw [if_neg (show ¬ (absEIdx i).isPersistent = true by rw [hb2]; simpa using hbv),
      hrel.scratchOn]
    split at h <;> rename_i hs
    · rw [if_pos hs]
      exact etables_get_lit_abs hrel.scrt h
    · rw [if_neg hs]
      have h2 : (none : Option kernel.expr.Literal) = o := Result.ok_injective h
      subst h2
      rfl

theorem estore_view_lit_wf {pers rs} (hinv : StoreInv pers rs)
    {i : arena.handle.EIdx} {o}
    (h : arena.store.EStore.view_lit rs pers i = ok o) :
    ∀ l, o = some l → ConRon.Refine.LiteralWF l := by
  rw [arena.store.EStore.view_lit] at h
  obtain ⟨b, hb, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · rw [arena.store.EStore.pers_get_lit] at h
    have h3 : arena.store.ETables.get_lit (rPersE pers rs) i = ok o := by
      unfold rPersE
      split at h <;> rename_i hs
      · rw [if_pos hs]; exact h
      · rw [if_neg hs]; exact h
    exact etables_get_lit_wf hinv.perst h3
  · split at h
    · exact etables_get_lit_wf hinv.scrt h
    · have h2 : (none : Option kernel.expr.Literal) = o := Result.ok_injective h
      subst h2
      intro l hl; cases hl

set_option hygiene false in
/-- One non-literal arm of `ETables.get`: it cannot answer a `Lit`. -/
local macro "nonlit_arm" : tactic => `(tactic| (
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨p, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rcases p with _ | r
  · have := Result.ok_injective h; simp at this
  · simp only [ConRon.Refine.bind_eq_ok_iff] at h
    first
    | (have := Result.ok_injective h; simp at this)
    | (obtain ⟨_, -, h⟩ := h; have := Result.ok_injective h; simp at this)
    | (obtain ⟨_, -, _, -, h⟩ := h; have := Result.ok_injective h; simp at this)
    | (obtain ⟨_, -, _, -, _, -, h⟩ := h; have := Result.ok_injective h; simp at this)))

/-- The stored literal behind `ETables.get`'s `Lit` answer is well formed. -/
theorem etables_get_lit_wf' {rt} (hinv : ETablesInv rt) {i : arena.handle.EIdx}
    {l : kernel.expr.Literal}
    (h : arena.store.ETables.get rt i = ok (some (.Lit l))) :
    ConRon.Refine.LiteralWF l := by
  rw [arena.store.ETables.get] at h
  obtain ⟨t, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · nonlit_arm
  split at h
  · nonlit_arm
  split at h
  · nonlit_arm
  split at h
  · nonlit_arm
  split at h
  · nonlit_arm
  obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · have := Result.ok_injective h; simp at this
  split at h
  · nonlit_arm
  split at h
  · obtain ⟨_, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨p, hp, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rcases p with _ | r
    · have := Result.ok_injective h; simp at this
    · obtain ⟨x, hx, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 := Result.ok_injective h
      simp only [Option.some.injEq, arena.store.ENodeView.Lit.injEq] at h2
      subst h2
      rw [ConRon.Refine.Expr.literal_dup_eq hx]
      exact tbl_node_wf hinv.lits hp r rfl
  split at h
  · nonlit_arm
  · have := Result.ok_injective h; simp at this

/-- The literal behind `EStore.view`'s `Lit` answer is well formed. -/
theorem estore_view_lit_wf' {pers rs} (hinv : StoreInv pers rs) {i : arena.handle.EIdx}
    {l : kernel.expr.Literal}
    (h : arena.store.EStore.view rs pers i = ok (some (.Lit l))) :
    ConRon.Refine.LiteralWF l := by
  rw [arena.store.EStore.view] at h
  obtain ⟨t, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  obtain ⟨b, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨q, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    rcases q with _ | ⟨ty, bo, mm⟩
    · have := Result.ok_injective h; simp at this
    · obtain ⟨ev, hev, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
      have h2 := Result.ok_injective h
      simp only [Option.some.injEq] at h2
      subst h2
      rw [arena.store.e_bind_view] at hev
      split at hev <;> (have := Result.ok_injective hev; simp at this)
  · obtain ⟨b1, -, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    split at h
    · rw [arena.store.EStore.pers_get] at h
      have h3 : arena.store.ETables.get (rPersE pers rs) i = ok (some (.Lit l)) := by
        unfold rPersE
        split at h <;> rename_i hs
        · rw [if_pos hs]; exact h
        · rw [if_neg hs]; exact h
      exact etables_get_lit_wf' hinv.perst h3
    · split at h
      · exact etables_get_lit_wf' hinv.scrt h
      · have := Result.ok_injective h; simp at this

/-- `view` against `Arena.view`, with the `LiteralWF` of a `Lit` answer (the
`view_ls` of `Tactic/Prims.lean` plus the representation fact; a local
candidate where the WF is needed). -/
theorem view_wf_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSR pers (fun a b => (∀ l, a = .Lit l → ConRon.Refine.LiteralWF l) ∧ b = absENodeView a)
      (arena.monad.view pers st h) st lst (Arena.view (absEIdx h)) := by
  intro o hrun
  have h1 := view_ls hrel hinv h o hrun
  cases o with
  | Err e => exact h1
  | Ok v =>
    obtain ⟨b, lst', hx, hb, h2, h3⟩ := h1
    refine ⟨b, lst', hx, ⟨?_, hb.2⟩, h2, h3⟩
    intro l hl
    subst hl
    rw [arena.monad.view] at hrun
    obtain ⟨q, hq, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rcases q with _ | q
    · obtain ⟨s, _, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨w, _, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      rw [arena.monad.fail] at hrun
      cases Result.ok_injective hrun
    · have h4 := Result.ok_injective hrun
      simp only [core.result.Result.Ok.injEq] at h4
      subst h4
      exact estore_view_lit_wf' hinv.store hq

/-- `view_lit` against `viewLit`, with the stored literal's `LiteralWF`. -/
@[lockstep] theorem view_lit_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => (∀ l, a = some l → ConRon.Refine.LiteralWF l) ∧
        b = a.map ConRon.Refine.absLiteral)
      (arena.monad.view_lit pers st h) st lst (Arena.viewLit (absEIdx h)) := by
  intro o hrun
  rw [arena.monad.view_lit] at hrun
  exact ⟨_, lst, rfl, ⟨estore_view_lit_wf hinv.store hrun,
    estore_view_lit_abs hrel.store hrun⟩, hrel, hinv⟩

/-- `view_const` against `viewConst`. -/
@[lockstep] theorem view_const_ls {pers st lst} (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) (h : arena.handle.EIdx) :
    LSV pers (fun a b => b = a.map absConstT)
      (arena.monad.view_const pers st h) st lst (Arena.viewConst (absEIdx h)) := by
  intro o hrun
  rw [arena.monad.view_const] at hrun
  exact ⟨_, lst, rfl, estore_view_const_abs hrel.store hrun, hrel, hinv⟩

attribute [lockstep_simp] absConstT

/-! ## A store-level step: `i_constant_info_to_constant_val` -/

/-- `i_constant_info_to_constant_val` against `IConstantInfo.toConstantVal`, a
store-level step: six arms copy the record, the `projInfo` arm interns
`Sort 1` in both, in the same order (the port at store level, the twin through
the monad; `intern_l_node_run₀`/`intern_e_sort_run₀` are the two sides of one
intern). -/
@[lockstep] theorem i_constant_info_to_constant_val_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) (c : arena.env.IConstantInfo) :
    LSS pers (fun a b => b = absIConstantVal a)
      (arena.env.i_constant_info_to_constant_val pers st.store c) st lst
      (absIConstantInfo c).toConstantVal := by
  intro o s' hm
  have plain : ∀ v iv, arena.env.i_constant_val_dup v = ok iv →
      (o, s') = (.Ok iv, st.store) →
      (absIConstantInfo c).toConstantVal = pure (absIConstantVal v) →
      LOut pers (fun a b => b = absIConstantVal a) o { st with store := s' }
        ((absIConstantInfo c).toConstantVal.run lst) := by
    intro v iv hiv ho hx
    simp only [Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    refine ⟨_, lst, ?_, (i_constant_val_dup_abs hiv).symm, hrel, hinv⟩
    rw [hx]; rfl
  cases c with
  | AxiomInfo v =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
    exact plain v iv hiv (Result.ok_injective h).symm rfl
  | DefnInfo v _ _ =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
    exact plain v iv hiv (Result.ok_injective h).symm rfl
  | ThmInfo v _ =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
    exact plain v iv hiv (Result.ok_injective h).symm rfl
  | IndInfo v _ =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
    exact plain v iv hiv (Result.ok_injective h).symm rfl
  | CtorInfo v _ _ =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
    exact plain v iv hiv (Result.ok_injective h).symm rfl
  | RecInfo v _ _ _ =>
    obtain ⟨iv, hiv, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
    exact plain v iv hiv (Result.ok_injective h).symm rfl
  | ProjInfo tbl =>
    clear plain
    simp only [arena.env.i_constant_info_to_constant_val] at hm
    simp only [absIConstantInfo, IConstantInfo.toConstantVal]
    -- 1. the level `0`
    obtain ⟨⟨r1, ar1⟩, h1, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
    have hS1 : Sim₀ absLIdx pers lst (r1, { st with store := ar1 })
        (Arena.internLNode (absLNodeView arena.store.LNodeView.Zero)) :=
      intern_l_node_run₀ hrel hinv arena.store.LNodeView.Zero
        (by rw [arena.monad.intern_l_node, h1]; simp only [Aeneas.Std.bind_tc_ok]; rfl)
    rw [show Arena.internLNode LNodeView.zero
        = Arena.internLNode (absLNodeView arena.store.LNodeView.Zero) from rfl]
    cases r1 with
    | Err e =>
      cases Result.ok_injective hm
      exact errSim_bind (Sim₀.apply_err hS1)
    | Ok z =>
    obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
    rw [run_bind_ok hx1]
    -- 2. the level `1`
    obtain ⟨⟨r2, ar2⟩, h2, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
    have hS2 : Sim₀ absLIdx pers lst1 (r2, { st with store := ar2 })
        (Arena.internLNode (absLNodeView (arena.store.LNodeView.Succ z))) :=
      intern_l_node_run₀ hrel1 hinv1 (arena.store.LNodeView.Succ z)
        (by rw [arena.monad.intern_l_node]; rw [h2]; simp only [Aeneas.Std.bind_tc_ok]; rfl)
    rw [show Arena.internLNode (.succ (absLIdx z))
        = Arena.internLNode (absLNodeView (arena.store.LNodeView.Succ z)) from rfl]
    cases r2 with
    | Err e =>
      cases Result.ok_injective hm
      exact errSim_bind (Sim₀.apply_err hS2)
    | Ok one =>
    obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
    rw [run_bind_ok hx2]
    -- 3. the expression `Sort 1`
    obtain ⟨⟨r3, ar3⟩, h3, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
    have h3' : arena.store.EStore.intern_sort ar2 pers one = ok (r3, ar3) := by
      rw [arena.store.EStore.intern] at h3; exact h3
    have hS3 : Sim₀ absEIdx pers lst2 (r3, { st with store := ar3 })
        (Arena.internSortE (absLIdx one)) :=
      intern_e_sort_run₀ hrel2 hinv2 one
        (by rw [arena.monad.intern_e_sort]; rw [h3']; simp only [Aeneas.Std.bind_tc_ok]; rfl)
    rw [show Arena.internE (.sort (absLIdx one)) = Arena.internSortE (absLIdx one) from rfl]
    cases r3 with
    | Err e =>
      cases Result.ok_injective hm
      exact errSim_bind (Sim₀.apply_err hS3)
    | Ok ty =>
    obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hS3
    rw [run_bind_ok hx3]
    obtain ⟨n, hn, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
    obtain ⟨v, hv, hm⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
    cases Result.ok_injective hm
    refine ⟨_, lst3, rfl, ?_, hrel3, hinv3⟩
    simp only [absIConstantVal, absIProjTable, dupId_nidx _ _ hn, nidx_vec_dup_val hv]

attribute [lockstep_simp] absLNodeView absLsNodeView ConRon.Refine.absLiteral

-- local: the Checker lane reads `absIConstantVal` folded (its `absValueGroup`)
attribute [local lockstep_simp] absIConstantVal

@[lockstep_simp] theorem vec_len_eq_zero {α : Type} (v : alloc.vec.Vec α) :
    (alloc.vec.Vec.len v = 0#usize) = (v.val = []) := by
  apply propext; constructor
  · intro h
    have := congrArg Std.UScalar.val h
    rw [alloc.vec.Vec.len_val] at this
    exact List.eq_nil_of_length_eq_zero (by simpa using this)
  · intro h
    apply Std.UScalar.eq_of_val_eq
    rw [alloc.vec.Vec.len_val]
    simp [h]

@[lockstep_simp] theorem vec_len_bne_zero {α : Type} (v : alloc.vec.Vec α) :
    (alloc.vec.Vec.len v != 0#usize) = !(v.val.isEmpty) := by
  have e := vec_len_eq_zero v
  by_cases h : v.val = []
  · have h1 : alloc.vec.Vec.len v = 0#usize := e ▸ h
    rw [h1, h]; rfl
  · have h1 : alloc.vec.Vec.len v ≠ 0#usize := fun h1 => h (e ▸ h1)
    have h2 : v.val.isEmpty = false := by
      cases hv : v.val with
      | nil => exact absurd hv h
      | cons _ _ => rfl
    rw [h2, bne_iff_ne.mpr h1]; rfl

@[lockstep_simp] theorem vec_len_beq_zero {α : Type} (v : alloc.vec.Vec α) :
    (alloc.vec.Vec.len v == 0#usize) = v.val.isEmpty := by
  have h := vec_len_bne_zero v
  rw [bne] at h
  have := congrArg (fun b => !b) h
  simpa using this

@[lockstep_simp] theorem vec_len_bne_one {α : Type} (v : alloc.vec.Vec α) :
    (alloc.vec.Vec.len v != 1#usize) = !(decide (v.val.length = 1)) := by
  have hv : (alloc.vec.Vec.len v).val = v.val.length := alloc.vec.Vec.len_val v
  by_cases h : v.val.length = 1
  · have : alloc.vec.Vec.len v = 1#usize := Std.UScalar.eq_of_val_eq (by rw [hv, h]; rfl)
    rw [this]; simp [h]
  · have : alloc.vec.Vec.len v ≠ 1#usize := fun hc => h (by rw [← hv, hc]; rfl)
    simp [this, h]

attribute [lockstep_simp] List.isEmpty_map List.isEmpty_iff

end ConRon.Refine2.Lockstep.PB

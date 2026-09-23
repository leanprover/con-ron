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
* the intern prims the region calls (`intern_e_lit`, `intern_e_const`,
  `intern_e_sort`, `intern_l_node`, `intern_ls_node`,
  `i_constant_info_to_constant_val`), PENDING the foundation's intern slice.
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

/-! ## A tactic gap: the error arm of an inlined fragment in bind position

`lockstep_core` inlines a fragment (`nat_op_pins`, `bool_const`'s `if`) and
re-associates the binds it leaves; the step after that is a stateful bind
whose continuation is `(match y with … | Err e => ok (Err e, s)) >>= K`, so
its error arm, fed `(Err e, s)`, is `ok (Err e, s) >>= K`, which
`errArm`'s head normalisation (no `bind` of an `ok`) does not reduce, and the
step fails.  `lockstep_b` is `lockstep_core` with that bind step retried with
an error arm closed by `simp only [bind_tc_ok]` first.  The move belongs in
`Core/LS/Tactic.lean`'s `errArm`; it lives here because region agents do not
edit that file. -/

theorem errArm_of_eq {γ : Type} {m : Result (core.result.Result γ kernel.core_types.CheckError ×
      arena.monad.AState)} {e : kernel.core_types.CheckError} {st : arena.monad.AState}
    (h : m = ok (.Err e, st)) : ErrArm m e := by
  subst h; exact errArm_ok

open Lean Meta Elab Tactic in
/-- The robust error arm. -/
def errArmB (g : MVarId) (names : List Name) : TacticM Unit := do
  let (_, g') ← g.introN names.length names
  runClosed g' (evalT `(tactic| first
    | exact errArm_ok
    | (simp only [Aeneas.Std.bind_tc_ok]; exact errArm_ok)
    | (simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.uncurry_apply_pair]; exact errArm_ok)))

open Lean Meta Elab Tactic in
/-- A stateful / read bind with the robust error arm. -/
def bindB (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``LS 7 do throwError "lockstep_b: not an LS goal"
  let m := (ty.getArg! 4).headBeta
  unless m.isAppOfArity ``Bind.bind 6 do throwError "lockstep_b: not a bind"
  let f := m.getArg! 4
  match ← classify (← inferType f).appArg! with
  | .state =>
    let gs ← applyRule g ``LS.bind
    specCore (← pick gs `hf)
    runClosed (← pick gs `hx) (evalT `(tactic| lockstep_congr))
    errArmB (← pick gs `he) [`e, `st1]
    normAll (← cont (← pick gs `hk) [`a, `b, `st1, `lst1, `hR, `hrel, `hinv] (some `hR))
  | .read =>
    let gs ← applyRule g ``LSR.bind
    specCore (← pick gs `hf)
    runClosed (← pick gs `hx) (evalT `(tactic| lockstep_congr))
    errArmB (← pick gs `he) [`e]
    normAll (← cont (← pick gs `hk) [`a, `b, `lst1, `hR, `hrel, `hinv] (some `hR))
  | _ => throwError "lockstep_b: not a stateful bind"

open Lean Meta Elab Tactic in
elab "lockstep_b_bind" : tactic => do
  let g ← getMainGoal
  let others := (← getGoals).tail
  let rest ← bindB g
  setGoals (rest ++ others)

/-! ### A kernel-soundness gap: `ok v >>= k` is not `k v` by `rfl`

Aeneas's `Result` is an `ITree`, and `bind_tc_ok` is a THEOREM: the kernel
does not accept `ok v >>= k ≡ k v` (the elaborator's `isDefEq` does, which is
why the proof only fails at the kernel check).  `coreMove`'s `Result.ok` case
(`Core/LS/Tactic.lean`) replaces the goal by `k v` with `replaceTargetDefEq`,
and every proof through it dies with "(kernel) application type mismatch".
`LS.rust_ok_bind` is the propositional step; `lockstep_b` tries it first. -/

theorem LS.rust_ok_bind {γ α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {v : γ} {k : γ → Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} (h : LS pers R (k v) lst x) :
    LS pers R (ok v >>= k) lst x := by
  rw [Aeneas.Std.bind_tc_ok]; exact h

theorem LSP.rust_ok_bind {γ α : Type} {v : γ} {k : γ → Result α} {Q : α → Prop}
    (h : LSP (k v) Q) : LSP (ok v >>= k) Q := by
  rw [Aeneas.Std.bind_tc_ok]; exact h

open Lean Meta Elab Tactic in
elab "lockstep_b_okbind" : tactic => do
  let g ← getMainGoal
  let others := (← getGoals).tail
  let rest ← g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let some rp := rustPos ty | throwError "lockstep_b: not a judgement"
    let m := (ty.getArg! rp).headBeta
    unless m.isAppOfArity ``Bind.bind 6 && (m.getArg! 4).headBeta.isAppOfArity ``Result.ok 2 do
      throwError "lockstep_b: not an ok bind"
    let rule := if rp == 4 then ``LS.rust_ok_bind else ``LSP.rust_ok_bind
    let gs ← applyRule g rule
    normAll [← pick gs `h]
  setGoals (rest ++ others)

/-- **`lockstep_core` with the two moves above.** -/
macro "lockstep_b" : tactic =>
  `(tactic| repeat' (first | lockstep_b_okbind | lockstep_core_step | lockstep_b_bind))

end ConRon.Refine2.Lockstep.PB

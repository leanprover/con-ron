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
import ConRon.Refine.CoreKNames
import ConRon.Refine.StdAxioms
import ConRon.Refine.TrustAxioms
import ConRon.Refine2.Core.Arms.Delta

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine (NameWF NamesWF ExprWF StrWF)


namespace Lockstep

/-- A reader that can fail (`SimRE`) is an `LSR`.  Moved here from
`Checker/KnotHyp.lean` (task #97-T2-LOCKSTEP lane Checker round 2) so the pin
readers below can be filed as `@[lockstep]` specs. -/
theorem LSR.ofSimRE {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {m : Result (core.result.Result α kernel.core_types.CheckError)}
    {st : arena.monad.AState} {lst : AState} {x : AM β}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (h : ∀ o, m = ok o → SimRE A lst o x) : LSR pers (fun a b => b = A a) m st lst x := by
  intro o hm
  have := h _ hm
  cases o with
  | Err e => exact this
  | Ok a => exact ⟨A a, lst, this, rfl, hrel, hinv⟩

end Lockstep

/-! ## One pin read inside a name walk (task #97-P5-Top round 2)

`arena::core::nat_op_names` and its siblings are chains of pin reads
(`let (r, st1) ← nat_pred_name st; match r with …`), each a `SimRE` against the
twin's reader.  `pin_step` is one link: the decline propagates, and on success
the twin's bind continues at the SAME twin state, because a pin read writes
nothing. -/

theorem pin_ok {lst : AState} {β : Type} {a : arena.handle.NIdx} {tw : AM NIdx}
    {kt : NIdx → AM β} (hS : SimRE absNIdx lst (.Ok a) tw) :
    (tw >>= kt).run lst = (kt (absNIdx a)).run lst := by
  have hx : tw.run lst = .ok (absNIdx a, lst) := hS
  rw [am_run_bind', hx, except_ok_bind]

theorem pin_err {lst : AState} {β : Type} {e : kernel.core_types.CheckError}
    {tw : AM NIdx} {kt : NIdx → AM β} (hS : SimRE absNIdx lst (.Err e) tw) :
    AErrSim e ((tw >>= kt).run lst) := by
  rw [am_run_bind']
  exact AErrSim.bind hS _

/-- A name reader of the checker modules (`std_axioms::propext_name` …): one pin
read, the state handed back untouched. -/
theorem name_read_sim {pers : arena.store.PersTier} {st : arena.monad.AState}
    {lst : AState}
    {pin : Result (core.result.Result arena.handle.NIdx kernel.core_types.CheckError)}
    {tw : AM NIdx}
    {o : core.result.Result arena.handle.NIdx kernel.core_types.CheckError ×
      arena.monad.AState}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hS : ∀ r, pin = ok r → SimRE absNIdx lst r tw)
    (hrun : (do let r ← pin; ok (r, st)) = ok o) :
    Sim₀ absNIdx pers lst o tw := by
  obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain rfl := (Result.ok_injective hrun).symm
  have h := hS r hr
  cases r with
  | Err e => exact AOut₀.err h
  | Ok a => exact ⟨lst, h, hrel, hinv⟩

/-- `arena::core::push_nidx` is `Vec::push` (the handle `dup2` is the
identity). -/
theorem push_nidx_val {out w : alloc.vec.Vec arena.handle.NIdx} {n : arena.handle.NIdx}
    (h : arena.core.push_nidx out n = ok w) : w.val = out.val ++ [n] := by
  rw [arena.core.push_nidx] at h
  obtain ⟨n1, hn1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  rw [dupId_nidx _ _ hn1] at h
  exact ConRon.Refine.vec_push_val h

/-! ## The table's own two writers and its four readers -/

set_option maxRecDepth 20000 in
/-- `pin_names` is the twin's `pinNames`, a pure list of con-leche `Name`s
built by nineteen `basis_names` calls.  The `NamesWF` conjunct is what every
caller of `intern_name_list` owes (`Refine2/Promote/Intern.lean`'s note). -/
theorem pin_names_refines {o} (hrun : arena.pins.pin_names = ok o) :
    ConRon.Refine.absNames o = pinNames ∧ NamesWF o := by
  rw [arena.pins.pin_names] at hrun
  obtain ⟨n0, h0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o0, ho0, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n1, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o1, ho1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n2, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o2, ho2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n3, h3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o3, ho3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n4, h4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o4, ho4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n5, h5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o5, ho5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n6, h6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o6, ho6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n7, h7, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o7, ho7, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n8, h8, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o8, ho8, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n9, h9, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o9, ho9, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n10, h10, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o10, ho10, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n11, h11, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o11, ho11, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n12, h12, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o12, ho12, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n13, h13, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o13, ho13, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n14, h14, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o14, ho14, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n15, h15, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o15, ho15, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n16, h16, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o16, ho16, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n17, h17, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o17, ho17, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n18, h18, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o18, ho18, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n19, h19, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o19, ho19, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n20, h20, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o20, ho20, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n21, h21, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o21, ho21, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n22, h22, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o22, ho22, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n23, h23, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o23, ho23, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n24, h24, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o24, ho24, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n25, h25, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o25, ho25, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n26, h26, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o26, ho26, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n27, h27, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o27, ho27, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n28, h28, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o28, ho28, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n29, h29, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o29, ho29, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n30, h30, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o30, ho30, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n31, h31, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o31, ho31, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n32, h32, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o32, ho32, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n33, h33, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o33, ho33, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n34, h34, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o34, ho34, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n35, h35, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o35, ho35, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n36, h36, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o36, ho36, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n37, h37, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o37, ho37, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n38, h38, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o38, ho38, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n39, h39, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o39, ho39, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n40, h40, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o40, ho40, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n41, h41, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o41, ho41, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n42, h42, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o42, ho42, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n43, h43, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o43, ho43, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n44, h44, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o44, ho44, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n45, h45, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o45, ho45, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n46, h46, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o46, ho46, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n47, h47, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨o47, ho47, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨n48, h48, hlast⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨e0, f0⟩ := ConRon.Refine.BasisNames.eq_name_refines h0
  obtain ⟨e1, f1⟩ := ConRon.Refine.BasisNames.punit_name_refines h1
  obtain ⟨e2, f2⟩ := ConRon.Refine.BasisNames.punit_rec_name_refines h2
  obtain ⟨e3, f3⟩ := ConRon.Refine.BasisNames.nat_name_refines h3
  obtain ⟨e4, f4⟩ := ConRon.Refine.BasisNames.nat_zero_name_refines h4
  obtain ⟨e5, f5⟩ := ConRon.Refine.BasisNames.nat_succ_name_refines h5
  obtain ⟨e6, f6⟩ := ConRon.Refine.BasisNames.quot_sound_name_refines h6
  obtain ⟨e7, f7⟩ := ConRon.Refine.BasisNames.string_name_refines h7
  obtain ⟨e8, f8⟩ := ConRon.Refine.BasisNames.string_of_list_name_refines h8
  obtain ⟨e9, f9⟩ := ConRon.Refine.BasisNames.list_name_refines h9
  obtain ⟨e10, f10⟩ := ConRon.Refine.BasisNames.list_nil_name_refines h10
  obtain ⟨e11, f11⟩ := ConRon.Refine.BasisNames.list_cons_name_refines h11
  obtain ⟨e12, f12⟩ := ConRon.Refine.BasisNames.char_name_refines h12
  obtain ⟨e13, f13⟩ := ConRon.Refine.BasisNames.and_name_refines h13
  obtain ⟨e14, f14⟩ := ConRon.Refine.BasisNames.char_of_nat_name_refines h14
  obtain ⟨e15, f15⟩ := ConRon.Refine.BasisNames.sorry_ax_name_refines h15
  obtain ⟨e16, f16⟩ := ConRon.Refine.CoreK.nat_pred_name_refines h16
  obtain ⟨e17, f17⟩ := ConRon.Refine.CoreK.nat_add_name_refines h17
  obtain ⟨e18, f18⟩ := ConRon.Refine.CoreK.nat_sub_name_refines h18
  obtain ⟨e19, f19⟩ := ConRon.Refine.CoreK.nat_mul_name_refines h19
  obtain ⟨e20, f20⟩ := ConRon.Refine.CoreK.nat_pow_name_refines h20
  obtain ⟨e21, f21⟩ := ConRon.Refine.CoreK.nat_beq_name_refines h21
  obtain ⟨e22, f22⟩ := ConRon.Refine.CoreK.nat_ble_name_refines h22
  obtain ⟨e23, f23⟩ := ConRon.Refine.CoreK.nat_div_name_refines h23
  obtain ⟨e24, f24⟩ := ConRon.Refine.CoreK.nat_mod_name_refines h24
  obtain ⟨e25, f25⟩ := ConRon.Refine.CoreK.nat_gcd_name_refines h25
  obtain ⟨e26, f26⟩ := ConRon.Refine.CoreK.nat_land_name_refines h26
  obtain ⟨e27, f27⟩ := ConRon.Refine.CoreK.nat_lor_name_refines h27
  obtain ⟨e28, f28⟩ := ConRon.Refine.CoreK.nat_xor_name_refines h28
  obtain ⟨e29, f29⟩ := ConRon.Refine.CoreK.nat_shift_left_name_refines h29
  obtain ⟨e30, f30⟩ := ConRon.Refine.CoreK.nat_shift_right_name_refines h30
  obtain ⟨e31, f31⟩ := ConRon.Refine.CoreK.bool_name_refines h31
  obtain ⟨e32, f32⟩ := ConRon.Refine.CoreK.bool_true_name_refines h32
  obtain ⟨e33, f33⟩ := ConRon.Refine.CoreK.bool_false_name_refines h33
  obtain ⟨e34, f34⟩ := ConRon.Refine.StdAxioms.propext_name_refines h34
  obtain ⟨e35, f35⟩ := ConRon.Refine.StdAxioms.choice_name_refines h35
  obtain ⟨e36, f36⟩ := ConRon.Refine.StdAxioms.iff_name_refines h36
  obtain ⟨e37, f37⟩ := ConRon.Refine.StdAxioms.iff_intro_name_refines h37
  obtain ⟨e38, f38⟩ := ConRon.Refine.StdAxioms.iff_rec_name_refines h38
  obtain ⟨e39, f39⟩ := ConRon.Refine.StdAxioms.nonempty_name_refines h39
  obtain ⟨e40, f40⟩ := ConRon.Refine.StdAxioms.nonempty_intro_name_refines h40
  obtain ⟨e41, f41⟩ := ConRon.Refine.StdAxioms.nonempty_rec_name_refines h41
  obtain ⟨e42, f42⟩ := ConRon.Refine.TrustAxioms.true_name_refines h42
  obtain ⟨e43, f43⟩ := ConRon.Refine.TrustAxioms.true_intro_name_refines h43
  obtain ⟨e44, f44⟩ := ConRon.Refine.TrustAxioms.trust_compiler_name_refines h44
  obtain ⟨e45, f45⟩ := ConRon.Refine.TrustAxioms.reduce_nat_name_refines h45
  obtain ⟨e46, f46⟩ := ConRon.Refine.TrustAxioms.reduce_bool_name_refines h46
  obtain ⟨e47, f47⟩ := ConRon.Refine.TrustAxioms.of_reduce_nat_name_refines h47
  obtain ⟨e48, f48⟩ := ConRon.Refine.TrustAxioms.of_reduce_bool_name_refines h48
  have hval : o.val = [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
      n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31, n32, n33, n34,
      n35, n36, n37, n38, n39, n40, n41, n42, n43, n44, n45, n46, n47, n48] := by
    rw [ConRon.Refine.vec_push_val hlast, ConRon.Refine.vec_push_val ho47,
      ConRon.Refine.vec_push_val ho46, ConRon.Refine.vec_push_val ho45, ConRon.Refine.vec_push_val
      ho44, ConRon.Refine.vec_push_val ho43, ConRon.Refine.vec_push_val ho42,
      ConRon.Refine.vec_push_val ho41, ConRon.Refine.vec_push_val ho40, ConRon.Refine.vec_push_val
      ho39, ConRon.Refine.vec_push_val ho38, ConRon.Refine.vec_push_val ho37,
      ConRon.Refine.vec_push_val ho36, ConRon.Refine.vec_push_val ho35, ConRon.Refine.vec_push_val
      ho34, ConRon.Refine.vec_push_val ho33, ConRon.Refine.vec_push_val ho32,
      ConRon.Refine.vec_push_val ho31, ConRon.Refine.vec_push_val ho30, ConRon.Refine.vec_push_val
      ho29, ConRon.Refine.vec_push_val ho28, ConRon.Refine.vec_push_val ho27,
      ConRon.Refine.vec_push_val ho26, ConRon.Refine.vec_push_val ho25, ConRon.Refine.vec_push_val
      ho24, ConRon.Refine.vec_push_val ho23, ConRon.Refine.vec_push_val ho22,
      ConRon.Refine.vec_push_val ho21, ConRon.Refine.vec_push_val ho20, ConRon.Refine.vec_push_val
      ho19, ConRon.Refine.vec_push_val ho18, ConRon.Refine.vec_push_val ho17,
      ConRon.Refine.vec_push_val ho16, ConRon.Refine.vec_push_val ho15, ConRon.Refine.vec_push_val
      ho14, ConRon.Refine.vec_push_val ho13, ConRon.Refine.vec_push_val ho12,
      ConRon.Refine.vec_push_val ho11, ConRon.Refine.vec_push_val ho10, ConRon.Refine.vec_push_val
      ho9, ConRon.Refine.vec_push_val ho8, ConRon.Refine.vec_push_val ho7, ConRon.Refine.vec_push_val
      ho6, ConRon.Refine.vec_push_val ho5, ConRon.Refine.vec_push_val ho4, ConRon.Refine.vec_push_val
      ho3, ConRon.Refine.vec_push_val ho2, ConRon.Refine.vec_push_val ho1, ConRon.Refine.vec_push_val
      ho0]
    simp
  refine ⟨?_, ?_⟩
  · rw [ConRon.Refine.absNames, hval]
    simp only [List.map_cons, List.map_nil, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11,
      e12, e13, e14, e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30,
      e31, e32, e33, e34, e35, e36, e37, e38, e39, e40, e41, e42, e43, e44, e45, e46, e47, e48]
    rfl
  · intro x hx
    rw [hval] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with
      rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    exacts [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17,
      f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36,
      f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48]

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

/-- **`intern_reserved_pins` ⊑ `internReservedPins`** — the driver's startup:
every reserved constant interned into the PERSISTENT tier once, and the table
installed.  The scratch tier is closed when it runs (the module note says why
that matters), which is `rs.scratch_on = false` here and task #97-P5-1's
finding 8 read from the other side. -/
theorem intern_reserved_pins_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.intern_reserved_pins pers st = ok o) :
    Sim₀ (fun _ : Unit => ()) pers lst o internReservedPins := by
  rw [arena.pins.intern_reserved_pins] at hrun
  unfold Sim₀
  rw [Arena.internReservedPins, internNameList_eq_frontend]
  -- 1. the forty-nine constant names
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hvabs, hvwf⟩ := pin_names_refines hv
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hS1 := intern_name_list_refines hrel hinv hvwf hq1
  rw [← hvabs]
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS1
  | Ok hs =>
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
  rw [run_bind_ok hx1]
  -- 2. the nineteen reserved basis names
  obtain ⟨v1, hv1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨hv1abs, hv1wf⟩ := ConRon.Refine.BasisNames.reserved_basis_names_refines hv1
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hS2 := intern_name_list_refines hrel1 hinv1 hv1wf hq2
  rw [reservedBasisNameValues_eq, ← hv1abs]
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS2
  | Ok rs =>
  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
  rw [run_bind_ok hx2]
  -- 3. the empty universe-argument list
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r3, st3⟩ := q3
  have hS3 := intern_ls_node_run₀ hrel2 hinv2
    (alloc.vec.Vec.new arena.handle.LIdx) hq3
  have hnil : absLsNodeView (alloc.vec.Vec.new arena.handle.LIdx) = [] := rfl
  rw [hnil] at hS3
  cases r3 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS3
  | Ok us =>
  obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hS3
  rw [run_bind_ok hx3]
  -- 4. the level `0`
  obtain ⟨q4, hq4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r4, st4⟩ := q4
  have hS4 := intern_l_node_run₀ hrel3 hinv3 arena.store.LNodeView.Zero hq4
  cases r4 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS4
  | Ok z =>
  obtain ⟨lst4, hx4, hrel4, hinv4⟩ := Sim₀.apply hS4
  rw [show Arena.internLNode LNodeView.zero
      = Arena.internLNode (absLNodeView arena.store.LNodeView.Zero) from rfl,
    run_bind_ok hx4]
  -- 5. the level `1`
  obtain ⟨l, hl, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hl' : l = z := dupId_lidx _ _ hl
  rw [hl'] at hrun
  obtain ⟨q5, hq5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r5, st5⟩ := q5
  have hS5 := intern_l_node_run₀ hrel4 hinv4 (arena.store.LNodeView.Succ z) hq5
  cases r5 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS5
  | Ok one =>
  obtain ⟨lst5, hx5, hrel5, hinv5⟩ := Sim₀.apply hS5
  rw [show (Arena.internLNode (.succ (absLIdx z)))
      = Arena.internLNode (absLNodeView (arena.store.LNodeView.Succ z)) from rfl,
    run_bind_ok hx5]
  -- 6. the expression `Sort 1`
  obtain ⟨q6, hq6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r6, st6⟩ := q6
  have hS6 := intern_e_sort_run₀ hrel5 hinv5 one hq6
  cases r6 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS6
  | Ok s1 =>
  obtain ⟨lst6, hx6, hrel6, hinv6⟩ := Sim₀.apply hS6
  rw [run_bind_ok hx6]
  -- 7. the table, written whole
  have ho := Result.ok_injective hrun
  subst ho
  refine AOut₀.ok (lst' := { lst6 with pins :=
      { names := (absNIdxL hs).toArray, reserved := absNIdxL rs,
        emptyLevels := absLsIdx us, zeroLevel := absLIdx z, sortOne := absEIdx s1 } })
    rfl ?_ ⟨hinv6.store, hinv6.memos, hinv6.caches⟩
  exact ⟨hrel6.store, hrel6.memos, hrel6.caches,
    ⟨by simp [absNIdxL], rfl, rfl, rfl, rfl⟩⟩

open Lockstep in
@[lockstep] theorem intern_reserved_pins_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LS pers (fun a b => b = (fun _ : Unit => ()) a)
      (arena.pins.intern_reserved_pins pers st) lst
      internReservedPins :=
  LS.ofSim₀ fun _ h => intern_reserved_pins_refines hrel hinv h

/-- `pins_ready` ⊑ `pinsReady` — a length test, because an unfilled table is
EMPTY and not a sentinel handle. -/
theorem pins_ready_refines {pers st lst} {o : Bool}
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
theorem pin_at_refines {pers st lst} {i : Std.Usize} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_at_ls {pers st lst}
    {i : Std.Usize}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_at st i) st lst
      (pinAt (absSz i)) :=
  LSR.ofSimRE hrel hinv fun _ h => pin_at_refines hrel hinv h

/-- `pin_reserved` ⊑ `pinReserved` — the nineteen reserved basis names, off
the table.  `arena::core`'s `reserved_basis_names` used to build and intern
all nineteen on every call, which task #97-P6-4a's profile put at 1.1 % of
`Init`'s cycles in the `Name` construction alone. -/
theorem pin_reserved_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.pins.pin_reserved st = ok o) :
    SimRE absNIdxL lst o pinReserved := by
  rw [arena.pins.pin_reserved] at hrun
  obtain ⟨b, hb, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hbr := pins_ready_refines hrel hinv hb
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
    simp only [absNIdxL, nidx_vec_dup_val hv]
  case isFalse hbf =>
    obtain ⟨sl, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨cps, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [arena.monad.fail] at hrun
    have h2 := Result.ok_injective hrun
    subst h2
    refine AErrSim.internal (s := "arena: reserved-name pins not interned") ?_
    rw [hrun2, if_neg (by simp only [← hbr]; simpa using hbf)]

open Lockstep in
@[lockstep] theorem pin_reserved_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdxL a)
      (arena.pins.pin_reserved st) st lst
      pinReserved :=
  LSR.ofSimRE hrel hinv fun _ h => pin_reserved_refines hrel hinv h

/-- `arena::core::reserved_basis_names` ⊑ `reservedBasisNames` — both are the
pin-table read, `pin_reserved` against `pinReserved` (twin fix D5 of task
#97-T2-LOCKSTEP: the twin used to re-intern thirteen of the nineteen). -/
theorem reserved_basis_names_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hrun : arena.core.reserved_basis_names st = ok o) :
    SimRE absNIdxL lst o reservedBasisNames := by
  rw [arena.core.reserved_basis_names] at hrun
  exact pin_reserved_refines hrel hinv hrun

/-- `pin_empty_levels` ⊑ `pinEmptyLevels`. -/
theorem pin_empty_levels_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_empty_levels_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absLsIdx a)
      (arena.pins.pin_empty_levels st) st lst
      pinEmptyLevels :=
  LSR.ofSimRE hrel hinv fun _ h => pin_empty_levels_refines hrel hinv h

/-- `pin_zero_level` ⊑ `pinZeroLevel`. -/
theorem pin_zero_level_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_zero_level_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absLIdx a)
      (arena.pins.pin_zero_level st) st lst
      pinZeroLevel :=
  LSR.ofSimRE hrel hinv fun _ h => pin_zero_level_refines hrel hinv h

/-- `pin_sort_one` ⊑ `pinSortOne`. -/
theorem pin_sort_one_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_sort_one_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absEIdx a)
      (arena.pins.pin_sort_one st) st lst
      pinSortOne :=
  LSR.ofSimRE hrel hinv fun _ h => pin_sort_one_refines hrel hinv h

/-! ## The forty-nine named readers, one per slot

Each is `pin_at` at its own constant, and each lemma is `pin_at_refines` after
that constant's value.  The order is `Arena/Pins.lean`'s, which is
`arena::pins`'s. -/

/-- `pin_eq` ⊑ `pinEq`, at slot `PIN_EQ`. -/
theorem pin_eq_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_eq_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_eq st) st lst
      pinEq :=
  LSR.ofSimRE hrel hinv fun _ h => pin_eq_refines hrel hinv h

/-- `pin_punit` ⊑ `pinPUnit`, at slot `PIN_PUNIT`. -/
theorem pin_punit_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_punit_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_punit st) st lst
      pinPUnit :=
  LSR.ofSimRE hrel hinv fun _ h => pin_punit_refines hrel hinv h

/-- `pin_punit_rec` ⊑ `pinPUnitRec`, at slot `PIN_PUNIT_REC`. -/
theorem pin_punit_rec_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_punit_rec_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_punit_rec st) st lst
      pinPUnitRec :=
  LSR.ofSimRE hrel hinv fun _ h => pin_punit_rec_refines hrel hinv h

/-- `pin_nat` ⊑ `pinNat`, at slot `PIN_NAT`. -/
theorem pin_nat_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nat_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nat st) st lst
      pinNat :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_refines hrel hinv h

/-- `pin_nat_zero` ⊑ `pinNatZero`, at slot `PIN_NAT_ZERO`. -/
theorem pin_nat_zero_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nat_zero_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nat_zero st) st lst
      pinNatZero :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_zero_refines hrel hinv h

/-- `pin_nat_succ` ⊑ `pinNatSucc`, at slot `PIN_NAT_SUCC`. -/
theorem pin_nat_succ_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nat_succ_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nat_succ st) st lst
      pinNatSucc :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_succ_refines hrel hinv h

/-- `pin_quot_sound` ⊑ `pinQuotSound`, at slot `PIN_QUOT_SOUND`. -/
theorem pin_quot_sound_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_string_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_string st) st lst
      pinString :=
  LSR.ofSimRE hrel hinv fun _ h => pin_string_refines hrel hinv h

/-- `pin_string_of_list` ⊑ `pinStringOfList`, at slot `PIN_STRING_OF_LIST`. -/
theorem pin_string_of_list_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_string_of_list_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_string_of_list st) st lst
      pinStringOfList :=
  LSR.ofSimRE hrel hinv fun _ h => pin_string_of_list_refines hrel hinv h

/-- `pin_list` ⊑ `pinList`, at slot `PIN_LIST`. -/
theorem pin_list_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_list_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_list st) st lst
      pinList :=
  LSR.ofSimRE hrel hinv fun _ h => pin_list_refines hrel hinv h

/-- `pin_list_nil` ⊑ `pinListNil`, at slot `PIN_LIST_NIL`. -/
theorem pin_list_nil_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_list_nil_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_list_nil st) st lst
      pinListNil :=
  LSR.ofSimRE hrel hinv fun _ h => pin_list_nil_refines hrel hinv h

/-- `pin_list_cons` ⊑ `pinListCons`, at slot `PIN_LIST_CONS`. -/
theorem pin_list_cons_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_list_cons_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_list_cons st) st lst
      pinListCons :=
  LSR.ofSimRE hrel hinv fun _ h => pin_list_cons_refines hrel hinv h

/-- `pin_char` ⊑ `pinChar`, at slot `PIN_CHAR`. -/
theorem pin_char_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_char_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_char st) st lst
      pinChar :=
  LSR.ofSimRE hrel hinv fun _ h => pin_char_refines hrel hinv h

/-- `pin_and` ⊑ `pinAnd`, at slot `PIN_AND`. -/
theorem pin_and_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_and_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_and st) st lst
      pinAnd :=
  LSR.ofSimRE hrel hinv fun _ h => pin_and_refines hrel hinv h

/-- `pin_char_of_nat` ⊑ `pinCharOfNat`, at slot `PIN_CHAR_OF_NAT`. -/
theorem pin_char_of_nat_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_char_of_nat_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_char_of_nat st) st lst
      pinCharOfNat :=
  LSR.ofSimRE hrel hinv fun _ h => pin_char_of_nat_refines hrel hinv h

/-- `pin_sorry_ax` ⊑ `pinSorryAx`, at slot `PIN_SORRY_AX`. -/
theorem pin_sorry_ax_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_sorry_ax_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_sorry_ax st) st lst
      pinSorryAx :=
  LSR.ofSimRE hrel hinv fun _ h => pin_sorry_ax_refines hrel hinv h

/-- `pin_nat_pred` ⊑ `pinNatPred`, at slot `PIN_NAT_PRED`. -/
theorem pin_nat_pred_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nat_pred_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nat_pred st) st lst
      pinNatPred :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_pred_refines hrel hinv h

/-- `pin_nat_add` ⊑ `pinNatAdd`, at slot `PIN_NAT_ADD`. -/
theorem pin_nat_add_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nat_add_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nat_add st) st lst
      pinNatAdd :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_add_refines hrel hinv h

/-- `pin_nat_sub` ⊑ `pinNatSub`, at slot `PIN_NAT_SUB`. -/
theorem pin_nat_sub_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nat_sub_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nat_sub st) st lst
      pinNatSub :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_sub_refines hrel hinv h

/-- `pin_nat_mul` ⊑ `pinNatMul`, at slot `PIN_NAT_MUL`. -/
theorem pin_nat_mul_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nat_mul_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nat_mul st) st lst
      pinNatMul :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_mul_refines hrel hinv h

/-- `pin_nat_pow` ⊑ `pinNatPow`, at slot `PIN_NAT_POW`. -/
theorem pin_nat_pow_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nat_pow_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nat_pow st) st lst
      pinNatPow :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_pow_refines hrel hinv h

/-- `pin_nat_beq` ⊑ `pinNatBeq`, at slot `PIN_NAT_BEQ`. -/
theorem pin_nat_beq_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nat_beq_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nat_beq st) st lst
      pinNatBeq :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_beq_refines hrel hinv h

/-- `pin_nat_ble` ⊑ `pinNatBle`, at slot `PIN_NAT_BLE`. -/
theorem pin_nat_ble_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nat_ble_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nat_ble st) st lst
      pinNatBle :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_ble_refines hrel hinv h

/-- `pin_nat_div` ⊑ `pinNatDiv`, at slot `PIN_NAT_DIV`. -/
theorem pin_nat_div_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nat_div_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nat_div st) st lst
      pinNatDiv :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_div_refines hrel hinv h

/-- `pin_nat_mod` ⊑ `pinNatMod`, at slot `PIN_NAT_MOD`. -/
theorem pin_nat_mod_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nat_mod_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nat_mod st) st lst
      pinNatMod :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_mod_refines hrel hinv h

/-- `pin_nat_gcd` ⊑ `pinNatGcd`, at slot `PIN_NAT_GCD`. -/
theorem pin_nat_gcd_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nat_gcd_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nat_gcd st) st lst
      pinNatGcd :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_gcd_refines hrel hinv h

/-- `pin_nat_land` ⊑ `pinNatLand`, at slot `PIN_NAT_LAND`. -/
theorem pin_nat_land_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nat_land_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nat_land st) st lst
      pinNatLand :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_land_refines hrel hinv h

/-- `pin_nat_lor` ⊑ `pinNatLor`, at slot `PIN_NAT_LOR`. -/
theorem pin_nat_lor_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nat_lor_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nat_lor st) st lst
      pinNatLor :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_lor_refines hrel hinv h

/-- `pin_nat_xor` ⊑ `pinNatXor`, at slot `PIN_NAT_XOR`. -/
theorem pin_nat_xor_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nat_xor_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nat_xor st) st lst
      pinNatXor :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_xor_refines hrel hinv h

/-- `pin_nat_shift_left` ⊑ `pinNatShiftLeft`, at slot `PIN_NAT_SHIFT_LEFT`. -/
theorem pin_nat_shift_left_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nat_shift_left_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nat_shift_left st) st lst
      pinNatShiftLeft :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_shift_left_refines hrel hinv h

/-- `pin_nat_shift_right` ⊑ `pinNatShiftRight`, at slot `PIN_NAT_SHIFT_RIGHT`. -/
theorem pin_nat_shift_right_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nat_shift_right_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nat_shift_right st) st lst
      pinNatShiftRight :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nat_shift_right_refines hrel hinv h

/-- `pin_bool` ⊑ `pinBool`, at slot `PIN_BOOL`. -/
theorem pin_bool_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_bool_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_bool st) st lst
      pinBool :=
  LSR.ofSimRE hrel hinv fun _ h => pin_bool_refines hrel hinv h

/-- `pin_bool_true` ⊑ `pinBoolTrue`, at slot `PIN_BOOL_TRUE`. -/
theorem pin_bool_true_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_bool_true_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_bool_true st) st lst
      pinBoolTrue :=
  LSR.ofSimRE hrel hinv fun _ h => pin_bool_true_refines hrel hinv h

/-- `pin_bool_false` ⊑ `pinBoolFalse`, at slot `PIN_BOOL_FALSE`. -/
theorem pin_bool_false_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_bool_false_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_bool_false st) st lst
      pinBoolFalse :=
  LSR.ofSimRE hrel hinv fun _ h => pin_bool_false_refines hrel hinv h

/-- `pin_propext` ⊑ `pinPropext`, at slot `PIN_PROPEXT`. -/
theorem pin_propext_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_propext_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_propext st) st lst
      pinPropext :=
  LSR.ofSimRE hrel hinv fun _ h => pin_propext_refines hrel hinv h

/-- `pin_choice` ⊑ `pinChoice`, at slot `PIN_CHOICE`. -/
theorem pin_choice_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_choice_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_choice st) st lst
      pinChoice :=
  LSR.ofSimRE hrel hinv fun _ h => pin_choice_refines hrel hinv h

/-- `pin_iff` ⊑ `pinIff`, at slot `PIN_IFF`. -/
theorem pin_iff_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_iff_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_iff st) st lst
      pinIff :=
  LSR.ofSimRE hrel hinv fun _ h => pin_iff_refines hrel hinv h

/-- `pin_iff_intro` ⊑ `pinIffIntro`, at slot `PIN_IFF_INTRO`. -/
theorem pin_iff_intro_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_iff_intro_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_iff_intro st) st lst
      pinIffIntro :=
  LSR.ofSimRE hrel hinv fun _ h => pin_iff_intro_refines hrel hinv h

/-- `pin_iff_rec` ⊑ `pinIffRec`, at slot `PIN_IFF_REC`. -/
theorem pin_iff_rec_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_iff_rec_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_iff_rec st) st lst
      pinIffRec :=
  LSR.ofSimRE hrel hinv fun _ h => pin_iff_rec_refines hrel hinv h

/-- `pin_nonempty` ⊑ `pinNonempty`, at slot `PIN_NONEMPTY`. -/
theorem pin_nonempty_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nonempty_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nonempty st) st lst
      pinNonempty :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nonempty_refines hrel hinv h

/-- `pin_nonempty_intro` ⊑ `pinNonemptyIntro`, at slot `PIN_NONEMPTY_INTRO`. -/
theorem pin_nonempty_intro_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nonempty_intro_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nonempty_intro st) st lst
      pinNonemptyIntro :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nonempty_intro_refines hrel hinv h

/-- `pin_nonempty_rec` ⊑ `pinNonemptyRec`, at slot `PIN_NONEMPTY_REC`. -/
theorem pin_nonempty_rec_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_nonempty_rec_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_nonempty_rec st) st lst
      pinNonemptyRec :=
  LSR.ofSimRE hrel hinv fun _ h => pin_nonempty_rec_refines hrel hinv h

/-- `pin_true` ⊑ `pinTrue`, at slot `PIN_TRUE`. -/
theorem pin_true_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_true_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_true st) st lst
      pinTrue :=
  LSR.ofSimRE hrel hinv fun _ h => pin_true_refines hrel hinv h

/-- `pin_true_intro` ⊑ `pinTrueIntro`, at slot `PIN_TRUE_INTRO`. -/
theorem pin_true_intro_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_true_intro_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_true_intro st) st lst
      pinTrueIntro :=
  LSR.ofSimRE hrel hinv fun _ h => pin_true_intro_refines hrel hinv h

/-- `pin_trust_compiler` ⊑ `pinTrustCompiler`, at slot `PIN_TRUST_COMPILER`. -/
theorem pin_trust_compiler_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_trust_compiler_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_trust_compiler st) st lst
      pinTrustCompiler :=
  LSR.ofSimRE hrel hinv fun _ h => pin_trust_compiler_refines hrel hinv h

/-- `pin_reduce_nat` ⊑ `pinReduceNat`, at slot `PIN_REDUCE_NAT`. -/
theorem pin_reduce_nat_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_reduce_nat_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_reduce_nat st) st lst
      pinReduceNat :=
  LSR.ofSimRE hrel hinv fun _ h => pin_reduce_nat_refines hrel hinv h

/-- `pin_reduce_bool` ⊑ `pinReduceBool`, at slot `PIN_REDUCE_BOOL`. -/
theorem pin_reduce_bool_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_reduce_bool_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_reduce_bool st) st lst
      pinReduceBool :=
  LSR.ofSimRE hrel hinv fun _ h => pin_reduce_bool_refines hrel hinv h

/-- `pin_of_reduce_nat` ⊑ `pinOfReduceNat`, at slot `PIN_OF_REDUCE_NAT`. -/
theorem pin_of_reduce_nat_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_of_reduce_nat_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_of_reduce_nat st) st lst
      pinOfReduceNat :=
  LSR.ofSimRE hrel hinv fun _ h => pin_of_reduce_nat_refines hrel hinv h

/-- `pin_of_reduce_bool` ⊑ `pinOfReduceBool`, at slot `PIN_OF_REDUCE_BOOL`. -/
theorem pin_of_reduce_bool_refines {pers st lst} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
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

open Lockstep in
@[lockstep] theorem pin_of_reduce_bool_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdx a)
      (arena.pins.pin_of_reduce_bool st) st lst
      pinOfReduceBool :=
  LSR.ofSimRE hrel hinv fun _ h => pin_of_reduce_bool_refines hrel hinv h

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
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hwf : NatOpPinSetWF ps)
    (hrun : arena.nat_op_pin_set.intern_pin_set_proofs pers st ps dp mp gp lap
      lop xp slp srp = ok o) :
    Sim₀ absINatOpPinSet pers lst o
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
  rw [arena.nat_op_pin_set.intern_pin_set_proofs] at hrun
  unfold Sim₀
  obtain ⟨htc, -, -, -, -, -, -, -, -, hdc, hmc, hgc, hlac, hloc, hxc, hslc, hsrc⟩ := hwf
  have hrel0 := hrel
  have hinv0 := hinv
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hS1 := intern_expr_list_refines hrel0 hinv0 hdc hq1
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS1
  | Ok u1 =>
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
  rw [run_bind_ok hx1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hS2 := intern_expr_list_refines hrel1 hinv1 hmc hq2
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS2
  | Ok u2 =>
  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
  rw [run_bind_ok hx2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r3, st3⟩ := q3
  have hS3 := intern_expr_list_refines hrel2 hinv2 hgc hq3
  cases r3 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS3
  | Ok u3 =>
  obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hS3
  rw [run_bind_ok hx3]
  obtain ⟨q4, hq4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r4, st4⟩ := q4
  have hS4 := intern_expr_list_refines hrel3 hinv3 hlac hq4
  cases r4 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS4
  | Ok u4 =>
  obtain ⟨lst4, hx4, hrel4, hinv4⟩ := Sim₀.apply hS4
  rw [run_bind_ok hx4]
  obtain ⟨q5, hq5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r5, st5⟩ := q5
  have hS5 := intern_expr_list_refines hrel4 hinv4 hloc hq5
  cases r5 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS5
  | Ok u5 =>
  obtain ⟨lst5, hx5, hrel5, hinv5⟩ := Sim₀.apply hS5
  rw [run_bind_ok hx5]
  obtain ⟨q6, hq6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r6, st6⟩ := q6
  have hS6 := intern_expr_list_refines hrel5 hinv5 hxc hq6
  cases r6 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS6
  | Ok u6 =>
  obtain ⟨lst6, hx6, hrel6, hinv6⟩ := Sim₀.apply hS6
  rw [run_bind_ok hx6]
  obtain ⟨q7, hq7, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r7, st7⟩ := q7
  have hS7 := intern_expr_list_refines hrel6 hinv6 hslc hq7
  cases r7 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS7
  | Ok u7 =>
  obtain ⟨lst7, hx7, hrel7, hinv7⟩ := Sim₀.apply hS7
  rw [run_bind_ok hx7]
  obtain ⟨q8, hq8, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r8, st8⟩ := q8
  have hS8 := intern_expr_list_refines hrel7 hinv7 hsrc hq8
  cases r8 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS8
  | Ok u8 =>
  obtain ⟨lst8, hx8, hrel8, hinv8⟩ := Sim₀.apply hS8
  rw [run_bind_ok hx8]
  obtain ⟨v, hv, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hv' := ConRon.Refine.Expr.str_copy_eq hv
  subst hv'
  have ho := Result.ok_injective hrun
  subst ho
  exact AOut₀.ok rfl hrel8 hinv8

open Lockstep in
@[lockstep] theorem intern_pin_set_proofs_ls {pers st lst}
    {ps : kernel.nat_op_pins.NatOpPinSet}
    {dp mp gp lap lop xp slp srp : arena.handle.EIdx}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hwf : NatOpPinSetWF ps) :
    LS pers (fun a b => b = absINatOpPinSet a)
      (arena.nat_op_pin_set.intern_pin_set_proofs pers st ps dp mp gp lap
      lop xp slp srp) lst
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
          absEIdx srp, dc, mc, gc, lac, loc, xc, slc, src⟩) :=
  LS.ofSim₀ fun _ h => intern_pin_set_proofs_refines hrel hinv hwf h

/-- `intern_pin_set` ⊑ `internPinSet` — one variant, sixteen terms. -/
theorem intern_pin_set_refines {pers st lst}
    {ps : kernel.nat_op_pins.NatOpPinSet} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hwf : NatOpPinSetWF ps)
    (hrun : arena.nat_op_pin_set.intern_pin_set pers st ps = ok o) :
    Sim₀ absINatOpPinSet pers lst o
      (internPinSet (ConRon.Refine.absNatOpPinSet ps)) := by
  rw [arena.nat_op_pin_set.intern_pin_set] at hrun
  unfold Sim₀
  simp only [internPinSet, ConRon.Refine.absNatOpPinSet]
  obtain ⟨-, hdp, hmp, hgp, hlap, hlop, hxp, hslp, hsrp, -⟩ := id hwf
  have hrel0 := hrel
  have hinv0 := hinv
  obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r1, st1⟩ := q1
  have hS1 := intern_expr_refines hrel0 hinv0 hdp hq1
  cases r1 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS1
  | Ok u1 =>
  obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
  rw [run_bind_ok hx1]
  obtain ⟨q2, hq2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r2, st2⟩ := q2
  have hS2 := intern_expr_refines hrel1 hinv1 hmp hq2
  cases r2 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS2
  | Ok u2 =>
  obtain ⟨lst2, hx2, hrel2, hinv2⟩ := Sim₀.apply hS2
  rw [run_bind_ok hx2]
  obtain ⟨q3, hq3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r3, st3⟩ := q3
  have hS3 := intern_expr_refines hrel2 hinv2 hgp hq3
  cases r3 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS3
  | Ok u3 =>
  obtain ⟨lst3, hx3, hrel3, hinv3⟩ := Sim₀.apply hS3
  rw [run_bind_ok hx3]
  obtain ⟨q4, hq4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r4, st4⟩ := q4
  have hS4 := intern_expr_refines hrel3 hinv3 hlap hq4
  cases r4 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS4
  | Ok u4 =>
  obtain ⟨lst4, hx4, hrel4, hinv4⟩ := Sim₀.apply hS4
  rw [run_bind_ok hx4]
  obtain ⟨q5, hq5, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r5, st5⟩ := q5
  have hS5 := intern_expr_refines hrel4 hinv4 hlop hq5
  cases r5 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS5
  | Ok u5 =>
  obtain ⟨lst5, hx5, hrel5, hinv5⟩ := Sim₀.apply hS5
  rw [run_bind_ok hx5]
  obtain ⟨q6, hq6, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r6, st6⟩ := q6
  have hS6 := intern_expr_refines hrel5 hinv5 hxp hq6
  cases r6 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS6
  | Ok u6 =>
  obtain ⟨lst6, hx6, hrel6, hinv6⟩ := Sim₀.apply hS6
  rw [run_bind_ok hx6]
  obtain ⟨q7, hq7, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r7, st7⟩ := q7
  have hS7 := intern_expr_refines hrel6 hinv6 hslp hq7
  cases r7 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS7
  | Ok u7 =>
  obtain ⟨lst7, hx7, hrel7, hinv7⟩ := Sim₀.apply hS7
  rw [run_bind_ok hx7]
  obtain ⟨q8, hq8, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  obtain ⟨r8, st8⟩ := q8
  have hS8 := intern_expr_refines hrel7 hinv7 hsrp hq8
  cases r8 with
  | Err e =>
    have ho := Result.ok_injective hrun
    subst ho
    exact AOut₀.errBind hS8
  | Ok u8 =>
  obtain ⟨lst8, hx8, hrel8, hinv8⟩ := Sim₀.apply hS8
  rw [run_bind_ok hx8]
  exact intern_pin_set_proofs_refines hrel8 hinv8 hwf hrun

open Lockstep in
@[lockstep] theorem intern_pin_set_ls {pers st lst}
    {ps : kernel.nat_op_pins.NatOpPinSet}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hwf : NatOpPinSetWF ps) :
    LS pers (fun a b => b = absINatOpPinSet a)
      (arena.nat_op_pin_set.intern_pin_set pers st ps) lst
      (internPinSet (ConRon.Refine.absNatOpPinSet ps)) :=
  LS.ofSim₀ fun _ h => intern_pin_set_refines hrel hinv hwf h

/-- `internPinSets` of a cons behind an accumulated prefix, re-bracketed so
that the head's intern is the first step and the prefix grows by it. -/
private theorem internPinSets_cons_acc (L : List INatOpPinSet)
    (a : ConLeche.NatOpPinSet) (rest : List ConLeche.NatOpPinSet) :
    (do pure (L ++ (← internPinSets (a :: rest))) : AM (List INatOpPinSet))
      = (do
          let h ← internPinSet a
          (do pure ((L ++ [h]) ++ (← internPinSets rest)) : AM (List INatOpPinSet))) := by
  simp only [internPinSets, bind_assoc, pure_bind, List.append_assoc,
    List.singleton_append]

/-- The cursor's measure induction behind `intern_pin_sets_refines`. -/
private theorem intern_pin_sets_aux {pers : arena.store.PersTier}
    {pss : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    (hwf : ∀ p ∈ pss.val, NatOpPinSetWF p) (m : Nat) :
    ∀ {st lst} {i : Std.Usize}
      {out : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {o},
      pss.val.length - i.val = m →
      AStateRel₀ pers st lst → AStateInv pers st →
      arena.nat_op_pin_set.intern_pin_sets pers st pss i out = ok o →
      Sim₀ absINatOpPinSetL pers lst o
        (do pure (absINatOpPinSetL out ++
          (← internPinSets ((pss.val.drop i.val).map ConRon.Refine.absNatOpPinSet)))) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro st lst i out o hm hrel hinv hrun
    rw [arena.nat_op_pin_set.intern_pin_sets.eq_def] at hrun
    dsimp only at hrun
    unfold Sim₀
    have hl := alloc.vec.Vec.len_val pss
    by_cases hge : i ≥ pss.len
    · have hle : pss.val.length ≤ i.val := by scalar_tac
      rw [if_pos hge] at hrun
      have ho := Result.ok_injective hrun
      subst ho
      rw [List.drop_eq_nil_of_le hle]
      refine AOut₀.ok (lst' := lst) ?_ hrel hinv
      simp only [List.map_nil, internPinSets, List.append_nil, pure_bind]
      rfl
    · have hlt : i.val < pss.val.length := by scalar_tac
      rw [if_neg hge] at hrun
      obtain ⟨nops, hn, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨hlt', rfl⟩ := ConRon.Refine.ExprOps.vec_index_val hn
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, internPinSets_cons_acc]
      obtain ⟨q1, hq1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r1, st1⟩ := q1
      have hS1 := intern_pin_set_refines hrel hinv
        (hwf _ (List.getElem_mem hlt)) hq1
      cases r1 with
      | Err e =>
        have ho := Result.ok_injective hrun
        subst ho
        exact AOut₀.errBind hS1
      | Ok h =>
      obtain ⟨lst1, hx1, hrel1, hinv1⟩ := Sim₀.apply hS1
      rw [run_bind_ok hx1]
      obtain ⟨out1, hout1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨i2, hi2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hi2v : i2.val = i.val + 1 := ConRon.Refine.HashMap.uscalar_add_eq hi2
      have hrec := ih (pss.val.length - i2.val) (by omega) rfl hrel1 hinv1 hrun
      have hacc : absINatOpPinSetL out1 = absINatOpPinSetL out ++ [absINatOpPinSet h] := by
        simp only [absINatOpPinSetL, ConRon.Refine.vec_push_val hout1, List.map_append,
          List.map_cons, List.map_nil]
      rw [hacc, hi2v] at hrec
      exact hrec

/-- `intern_pin_sets` ⊑ `internPinSets` at the cursor — the variant LIST, in
the order the install gate tries them. -/
theorem intern_pin_sets_refines {pers st lst}
    {pss : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet} {i : Std.Usize}
    {out : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet} {o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hwf : ∀ p ∈ pss.val, NatOpPinSetWF p)
    (hrun : arena.nat_op_pin_set.intern_pin_sets pers st pss i out = ok o) :
    Sim₀ absINatOpPinSetL
      pers lst o
      (do pure (absINatOpPinSetL out ++
        (← internPinSets ((pss.val.drop i.val).map ConRon.Refine.absNatOpPinSet)))) := by
  exact intern_pin_sets_aux hwf _ rfl hrel hinv hrun


open Lockstep in
@[lockstep] theorem intern_pin_sets_ls {pers st lst}
    {pss : alloc.vec.Vec kernel.nat_op_pins.NatOpPinSet}
    {i : Std.Usize}
    {out : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    (hrel : AStateRel₀ pers st lst)
    (hinv : AStateInv pers st)
    (hwf : ∀ p ∈ pss.val, NatOpPinSetWF p) :
    LS pers (fun a b => b = absINatOpPinSetL a)
      (arena.nat_op_pin_set.intern_pin_sets pers st pss i out) lst
      (do pure (absINatOpPinSetL out ++
        (← internPinSets ((pss.val.drop i.val).map ConRon.Refine.absNatOpPinSet)))) :=
  LS.ofSim₀ fun _ h => intern_pin_sets_refines hrel hinv hwf h

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

/-- info: 'ConRon.Refine2.pin_reserved_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pin_reserved_refines

/-- info: 'ConRon.Refine2.pin_zero_level_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pin_zero_level_refines

/-- info: 'ConRon.Refine2.pin_sort_one_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pin_sort_one_refines


/-! ## The pinned-name readers as `@[lockstep]` specs (task #97-T2-LOCKSTEP lane Checker round 2)

Each Rust reader is one pin read with the state handed back; the twin is the
pin reader itself (`boolName := pinBool`). -/

open Lockstep in
@[lockstep] theorem nat_shift_right_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_shift_right_name st) lst natShiftRightName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv (fun _ hr => pin_nat_shift_right_refines hrel hinv hr)
    (by rw [arena.core.nat_shift_right_name] at h; exact h)

open Lockstep in
@[lockstep] theorem nat_shift_left_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_shift_left_name st) lst natShiftLeftName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv (fun _ hr => pin_nat_shift_left_refines hrel hinv hr)
    (by rw [arena.core.nat_shift_left_name] at h; exact h)

open Lockstep in
@[lockstep] theorem nat_xor_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_xor_name st) lst natXorName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv (fun _ hr => pin_nat_xor_refines hrel hinv hr)
    (by rw [arena.core.nat_xor_name] at h; exact h)

open Lockstep in
@[lockstep] theorem nat_lor_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_lor_name st) lst natLorName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv (fun _ hr => pin_nat_lor_refines hrel hinv hr)
    (by rw [arena.core.nat_lor_name] at h; exact h)

open Lockstep in
@[lockstep] theorem nat_land_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_land_name st) lst natLandName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv (fun _ hr => pin_nat_land_refines hrel hinv hr)
    (by rw [arena.core.nat_land_name] at h; exact h)

open Lockstep in
@[lockstep] theorem nat_gcd_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_gcd_name st) lst natGcdName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv (fun _ hr => pin_nat_gcd_refines hrel hinv hr)
    (by rw [arena.core.nat_gcd_name] at h; exact h)

open Lockstep in
@[lockstep] theorem nat_mod_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_mod_name st) lst natModName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv (fun _ hr => pin_nat_mod_refines hrel hinv hr)
    (by rw [arena.core.nat_mod_name] at h; exact h)

open Lockstep in
@[lockstep] theorem nat_div_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_div_name st) lst natDivName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv (fun _ hr => pin_nat_div_refines hrel hinv hr)
    (by rw [arena.core.nat_div_name] at h; exact h)

open Lockstep in
@[lockstep] theorem nat_ble_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_ble_name st) lst natBleName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv (fun _ hr => pin_nat_ble_refines hrel hinv hr)
    (by rw [arena.core.nat_ble_name] at h; exact h)

open Lockstep in
@[lockstep] theorem nat_beq_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_beq_name st) lst natBeqName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv (fun _ hr => pin_nat_beq_refines hrel hinv hr)
    (by rw [arena.core.nat_beq_name] at h; exact h)

open Lockstep in
@[lockstep] theorem nat_pow_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_pow_name st) lst natPowName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv (fun _ hr => pin_nat_pow_refines hrel hinv hr)
    (by rw [arena.core.nat_pow_name] at h; exact h)

open Lockstep in
@[lockstep] theorem nat_mul_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_mul_name st) lst natMulName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv (fun _ hr => pin_nat_mul_refines hrel hinv hr)
    (by rw [arena.core.nat_mul_name] at h; exact h)

open Lockstep in
@[lockstep] theorem nat_sub_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_sub_name st) lst natSubName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv (fun _ hr => pin_nat_sub_refines hrel hinv hr)
    (by rw [arena.core.nat_sub_name] at h; exact h)

open Lockstep in
@[lockstep] theorem nat_add_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_add_name st) lst natAddName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv (fun _ hr => pin_nat_add_refines hrel hinv hr)
    (by rw [arena.core.nat_add_name] at h; exact h)

open Lockstep in
@[lockstep] theorem nat_pred_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.nat_pred_name st) lst natPredName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv (fun _ hr => pin_nat_pred_refines hrel hinv hr)
    (by rw [arena.core.nat_pred_name] at h; exact h)

open Lockstep in
@[lockstep] theorem bool_false_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.bool_false_name st) lst boolFalseName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv (fun _ hr => pin_bool_false_refines hrel hinv hr)
    (by rw [arena.core.bool_false_name] at h; exact h)

open Lockstep in
@[lockstep] theorem bool_true_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.bool_true_name st) lst boolTrueName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv (fun _ hr => pin_bool_true_refines hrel hinv hr)
    (by rw [arena.core.bool_true_name] at h; exact h)

open Lockstep in
@[lockstep] theorem bool_name_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers (fun a b => b = absNIdx a) (arena.core.bool_name st) lst boolName :=
  LS.ofSim₀ fun _ h => name_read_sim hrel hinv (fun _ hr => pin_bool_refines hrel hinv hr)
    (by rw [arena.core.bool_name] at h; exact h)

open Lockstep in
@[lockstep] theorem zero_level_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absLIdx a) (arena.core.zero_level st) st lst zeroLevel :=
  LSR.ofSimRE hrel hinv fun _ h => pin_zero_level_refines hrel hinv (by rw [arena.core.zero_level] at h; exact h)

open Lockstep in
@[lockstep] theorem empty_levels_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absLsIdx a) (arena.core.empty_levels st) st lst emptyLevels :=
  LSR.ofSimRE hrel hinv fun _ h => pin_empty_levels_refines hrel hinv (by rw [arena.core.empty_levels] at h; exact h)

open Lockstep in
@[lockstep] theorem sort_one_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absEIdx a) (arena.core.sort_one st) st lst sortOne :=
  LSR.ofSimRE hrel hinv fun _ h => pin_sort_one_refines hrel hinv (by rw [arena.core.sort_one] at h; exact h)

open Lockstep in
@[lockstep] theorem reserved_basis_names_ls {pers st lst}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LSR pers (fun a b => b = absNIdxL a) (arena.core.reserved_basis_names st) st lst
      reservedBasisNames :=
  LSR.ofSimRE hrel hinv fun _ h => reserved_basis_names_refines hrel hinv h


namespace Lockstep

@[lockstep] theorem nidx_eq2_spec (a b : arena.handle.NIdx) :
    LSP (arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b)
      (fun o => o = (absNIdx a == absNIdx b)) :=
  fun _ h => nidx_eq2_abs h

@[lockstep] theorem i_constant_val_dup_spec (cv : arena.env.IConstantVal) :
    LSP (arena.env.i_constant_val_dup cv)
      (fun o => absIConstantVal o = absIConstantVal cv) :=
  fun _ h => i_constant_val_dup_abs h

@[lockstep] theorem reducibility_hint_dup_spec (h1 : kernel.env.ReducibilityHint) :
    LSP (kernel.env.reducibility_hint_dup h1) (fun r => r = h1) := by
  intro r h
  cases h1 <;> simp only [kernel.env.reducibility_hint_dup, Result.ok.injEq] at h <;>
    exact h.symm

end Lockstep

end ConRon.Refine2

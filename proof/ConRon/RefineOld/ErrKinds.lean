/-
**The two named error builders of con-leche's `sorryAx` ruling** (con-leche
task #292, vendored at task #83).

`sorryAx` is the one axiom the checker tolerates as a *declaration*: an export
declares it whenever the module it came from mentions `sorry`, so the record is
forwarded and installs nothing — and because there is no set model for it, any
*use* of the name is a positively detected unsupported feature, a DECLINE at
the record that uses it rather than a reject.  con-leche decides that at two
choke points and the port mirrors both:

* `ConLeche.unknownConstError` (`Kernel/Core.lean`) inside inference, where a
  constant fails to resolve — `core_k::unknown_const_error`;
* `ConLeche.unresolvedConstsError` (`Kernel/CheckerBase.lean`) at every guard
  that keeps unresolved constants out of a stored term —
  `checker_base::unresolved_consts_error`.

Both are stated as *kind* equations (`absErrKind` / `lErrKind`,
`Refine/Abs.lean`): the port drops the interpolated message (§3.1, messages
need not match), so what a `ErrSim` obligation above them needs is exactly
"the port's error stands for the kind con-leche throws at".

The file exists because the two lemmas need `mentions_const_refines`
(`Refine/IndStructParts.lean`) and are consumed by the whole checker tier,
which sits *beside* the inductive tier rather than above it.
-/
import ConRon.RefineOld.IndStructParts

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine

/-- `core_types::not_implemented` is the constructor (the checker tier's own
copy of this inversion is `private`). -/
theorem errKinds_not_implemented_val {v : alloc.vec.Vec Std.U32}
    {ce : kernel.core_types.CheckError}
    (h : kernel.core_types.not_implemented v = ok ce) : ce = .NotImplemented v := by
  rw [kernel.core_types.not_implemented] at h; exact (Result.ok_injective h).symm

/-- `core_types::invalid` is the constructor. -/
theorem errKinds_invalid_val {v : alloc.vec.Vec Std.U32}
    {ce : kernel.core_types.CheckError}
    (h : kernel.core_types.invalid v = ok ce) : ce = .Invalid v := by
  rw [kernel.core_types.invalid] at h; exact (Result.ok_injective h).symm

/-- **`core_k::unknown_const_error` refines `unknownConstError`**
(`ConLeche/Kernel/Core.lean:76-96`) at the kind: `sorryAx` declines, every
other unresolved name rejects. -/
theorem unknown_const_error_refines {n : name.Name}
    {ce : kernel.core_types.CheckError} (hn : NameWF n)
    (h : kernel.core_k.unknown_const_error n = ok ce) :
    absErrKind ce = some (lErrKind (ConLeche.unknownConstError (absName n))) := by
  rw [kernel.core_k.unknown_const_error] at h
  obtain ⟨n1, hn1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e1, w1⟩ := BasisNames.sorry_ax_name_refines hn1
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = (absName n == absName n1) := Name.beq_refines hn w1 hb
  rw [e1] at hbv
  rw [ConLeche.unknownConstError]
  cases hbc : b with
  | true =>
    rw [hbc] at h hbv
    simp only [if_pos] at h
    obtain ⟨s, -, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := bind_eq_ok_iff.mp h
    have heq : absName n = ConLeche.sorryAxName := by
      have := hbv.symm; simpa using this
    rw [if_pos heq, errKinds_not_implemented_val h]
    rfl
  | false =>
    rw [hbc] at h hbv
    simp only [Bool.false_eq_true, if_false] at h
    obtain ⟨s, -, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := bind_eq_ok_iff.mp h
    have hne : ¬ (absName n = ConLeche.sorryAxName) := by
      intro hc
      have : (absName n == ConLeche.sorryAxName) = true := by simp [hc]
      rw [← hbv] at this
      exact absurd this (by simp)
    rw [if_neg hne, errKinds_invalid_val h]
    rfl

/-- **`checker_base::unresolved_consts_error` refines
`unresolvedConstsError`** (`ConLeche/Kernel/CheckerBase.lean:71-91`) at the
kind, for every slot name `w` the cited message interpolates: a term that
mentions `sorryAx` declines, anything else rejects. -/
theorem unresolved_consts_error_refines {e : expr.Expr}
    {ce : kernel.core_types.CheckError} (he : ExprWF e)
    (h : kernel.checker_base.unresolved_consts_error e = ok ce) (w : String) :
    absErrKind ce = some (lErrKind (ConLeche.unresolvedConstsError w (absExpr e))) := by
  rw [kernel.checker_base.unresolved_consts_error] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e1, w1⟩ := BasisNames.sorry_ax_name_refines hn
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = ConLeche.Expr.mentionsConst (absName n) (absExpr e) :=
    StructParts.mentions_const_refines w1 he hb
  rw [e1] at hbv
  rw [ConLeche.unresolvedConstsError]
  cases hbc : b with
  | true =>
    rw [hbc] at h hbv
    simp only [if_pos] at h
    obtain ⟨s, -, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := bind_eq_ok_iff.mp h
    rw [if_pos hbv.symm, errKinds_not_implemented_val h]
    rfl
  | false =>
    rw [hbc] at h hbv
    simp only [Bool.false_eq_true, if_false] at h
    obtain ⟨s, -, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, -, h⟩ := bind_eq_ok_iff.mp h
    rw [if_neg (by rw [← hbv]; simp), errKinds_invalid_val h]
    rfl

end ConRon.Refine

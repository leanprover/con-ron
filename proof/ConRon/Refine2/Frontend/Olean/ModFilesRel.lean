/-
# `ConRon.Refine2.Frontend.Olean.ModFilesRel` — the relations of the file tier

**Task #142, Theorem 2.**  `ModFilesRel`: the files of a module against upstream's
`ModFiles`, with `PartFits` on every part.  `AS`: the judgement of a function that reaches a
file read.  A failing read of the instance claims nothing of the twin (`FsRel`), so such a
function claims its accept only: `Ok` in the Rust is a run of the twin, in related states,
and an `Err` claims nothing.
-/
import ConRon.Refine2.Frontend.Olean.Parts
import ConRon.Refine2.Frontend.Olean.FsRel
import ConRon.Refine2.Frontend.Olean.Shape

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Frontend.Olean

open ConRon.Arena

/-- **The files of a module, as upstream's**, every part as `part_of_bytes` leaves it. -/
structure ModFilesRel (f : frontend.olean.view.ModFiles) (f' : ConLeche.Frontend.Olean.ModFiles) :
    Prop where
  exported : f'.exported = absPart f.exported
  server : f'.server = f.server.map absPart
  «private» : f'.private = f.private_part.map absPart
  fitsE : PartFits f.exported
  fitsS : ∀ p, f.server = some p → PartFits p
  fitsP : ∀ p, f.private_part = some p → PartFits p

/-- **The accept of a function that reaches a file read**: the Rust's `Ok` over `st.store` is
a run of the twin, in related states.  An `Err` claims nothing. -/
def AS {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop)
    (st : arena.monad.AState) (lst : AState)
    (m : Result (core.result.Result α kernel.core_types.CheckError × arena.store.EStore))
    (x : AM β) : Prop :=
  AStateRel₀ pers st lst → AStateInv pers st →
    ∀ a s', m = ok (.Ok a, s') →
      ∃ b lst', x.run lst = .ok (b, lst') ∧ R a b ∧
        AStateRel₀ pers (withStore st s') lst' ∧ AStateInv pers (withStore st s')

/-- A full judgement gives its accept. -/
theorem AS.of_CS {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {m} {x : AM β} (h : CS pers R st lst m x) :
    AS pers R st lst (α := α) m x :=
  fun hrel hinv a s' hm => h hrel hinv (.Ok a) s' hm

/-- The Rust `Ok` with no store change against the twin's `pure`. -/
theorem AS.pure {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {a : α} {b : β} (hR : R a b) :
    AS pers R st lst (ok (.Ok a, st.store)) (Pure.pure b) :=
  AS.of_CS (CS.pure hR)

/-- A step of the Rust alone. -/
theorem AS.pure_step {α β γ : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {st : arena.monad.AState} {lst : AState} {f : Result γ}
    {k : γ → Result (core.result.Result α kernel.core_types.CheckError × arena.store.EStore)}
    {x : AM β} (h : ∀ a, f = ok a → AS pers R st lst (k a) x) :
    AS pers R st lst (Std.bind f k) x := by
  intro hrel hinv a s' hm
  obtain ⟨v, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact h v h1 hrel hinv a s' h2

/-- **The bind of two accepts**: the continuation carries an `Err` to an `Err`, which is all
that is asked of it. -/
theorem AS.bind {α₁ β₁ α β : Type} {pers : arena.store.PersTier} {R₁ : α₁ → β₁ → Prop}
    {R : α → β → Prop} {st : arena.monad.AState} {lst : AState}
    {f : Result (core.result.Result α₁ kernel.core_types.CheckError × arena.store.EStore)}
    {k : core.result.Result α₁ kernel.core_types.CheckError × arena.store.EStore →
      Result (core.result.Result α kernel.core_types.CheckError × arena.store.EStore)}
    {x : AM β₁} {g : β₁ → AM β}
    (hf : AS pers R₁ st lst f x)
    (he : ∀ e s1 a s', k (.Err e, s1) ≠ ok (.Ok a, s'))
    (hk : ∀ a b s1 lst1, R₁ a b → AS pers R (withStore st s1) lst1 (k (.Ok a, s1)) (g b)) :
    AS pers R st lst (Std.bind f k) (x >>= g) := by
  intro hrel hinv a s' hm
  obtain ⟨⟨r, s1⟩, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  cases r with
  | Ok a1 =>
    obtain ⟨b, lst1, hx, hR, hrel1, hinv1⟩ := hf hrel hinv a1 s1 hf1
    rw [am_bind_ok hx]
    exact hk a1 b s1 lst1 hR hrel1 hinv1 a s' hk1
  | Err e => exact absurd hk1 (he e s1 a s')

end ConRon.Refine2.Frontend.Olean

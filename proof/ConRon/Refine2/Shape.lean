/-
# `ConRon.Refine2.Shape` — the shape of a Theorem-2 lemma

**Deliverable 1 of task #97 P5, part 4.**  DESIGN.md §8.2: *"the Aeneas model
of the Rust `check_decls` accepting implies (B) accepting with the abstracted
state/result, over the whole outcome as today (`Sim`/`Out`/`ErrSim`; the
port's `Native` error claims nothing)"*; since task #98-NATIVE a `Native` claims
the twin's `.native` at the same point, like every other kind.  This file is
that sentence, for a
Rust function of the arena's one shape

    f (pers : PersTier) (st : AState) args :
      Result ((core.result.Result R CheckError) × AState)

— the state threaded as a RETURN VALUE, which is what task #97s round 2
measured and round 3 said the task-#70 idiom does not mind.

## The four outcomes, and what each claims

| Rust outcome | what the lemma claims about the twin |
|---|---|
| `.Ok r` | the twin's run ends `.ok` at the abstracted value, in a state related to the Rust's, with the Rust state's invariant re-established, `Ext` from the pre-state, and `WF r` |
| `.Err e` at any of the four constructors | the twin throws too, **at the same kind** — messages are never compared (DESIGN §3.1); a port `Native` is a twin `.native` at the same point (task #98-NATIVE) |
| an Aeneas `fail`/`div` | nothing: every lemma's hypothesis is `f … = ok …` |

## The lockstep ruling (task #97-T2-LOCKSTEP): `AOut₀`/`Sim₀`/`SimS₀`

Theorem 2 is a lockstep refinement: the Rust and the twin do the same
operations from related states, and the relation says only that the two sides
hold the same data in different representations (`AStateRel₀`).  **No
semantic invariant lives in Theorem 2**: `StoreWF` and `Ext` are Theorem 1's
(which proves `StoreWF` along its own run).  The statements are therefore
`AOut₀`/`Sim₀`/`SimS₀`, at the end of this file.  `AOut`/`Sim`/`SimS` below,
with their `AStateRel` (= `AStateRel₀ ∧ StoreWF`) and `Ext`, are
**deprecated shims** kept until every lane has moved (`Sim.to₀`,
`SimS.to₀` project a proved old statement onto the new one).  The next
paragraph is the old shapes' rationale, kept for the record: its premise,
that `orElseAttempt` resumes at the pre-attempt store where the port keeps the
appends, was divergence D4, fixed in the RUST (task #97-T2-LOCKSTEP D4, D4b: the
port restores a full copy of its pre-attempt state, `Checker/Base.lean`).

## Why `Ext` (historical), and why an existential state

**`Ext`** (`Arena/Denote.lean`'s, the conjunct con-leche's own `SimAt`
carries) is in the success arm because `orElseAttempt` needs it and nothing
else does: task #97-LC's ledger row says the twin's error arm resumes at the
pre-attempt store where the port keeps the attempt's unreachable appends, so
*"the difference is handle NUMBERING, never a denotation and never a verdict;
what the refinement owes at this seam is `Ext` rather than store equality"*.
Carrying it in every lemma's conclusion — it is free, `Ext.refl` for a
function that appends nothing and `Ext.trans` through a bind — is what makes
that seam statable when the checker tier reaches it.

**The existential twin state** is `RefineOld/State.lean`'s `Out`, for the same
reason: the cons tables and the memo tables are related by a probe agreement
(`Refine/HashMap2.lean`'s `RelOn`) and a `Std.HashMap` is not recoverable from
one, so the abstraction of the state is a relation and the twin's post-state
has to be quantified.  `AUTOMATION.md`'s rule about existentials in
CONCLUSIONS is why `AOut.ofRun` exists beside it.

## The error kinds

The twin's `CheckError` has the same four constructors as the port's, the
fourth being DESIGN §8.3's `native` ("the Rust raises `Native` at the limit,
the Lean `throw`s the same kind").  **All four are compared** (task
#98-NATIVE).  Until then a port `Native` claimed nothing (`absAErrKind` sent
it to `none`, and `AErrSim.native` discharged any twin outcome); every
`Native` the arena raises is now a capacity guard the twin raises `.native` at
too (`Arena/Monad.lean`'s interns, whose test is the port's `Tbl::full`), so
the escape is gone and a Rust `Native` is a twin `.native` at the same point.
DESIGN.md `### Task #98-NATIVE` has the site table.
-/
import ConRon.Refine2.AbsState

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

/-! ## The error, as its kind -/

/-- The twin's `CheckError` (`Arena/Monad.lean`) without its messages: the
four kinds a refinement lemma claims (`native` since task #98-NATIVE). -/
inductive AErrKind where
  | notImplemented
  | invalid
  | internal
  | native
  deriving DecidableEq, Repr

/-- The twin's error, as the kind it stands for.  (An `Option` for history's
sake: until task #98-NATIVE the twin's `native` stood for nothing.) -/
def lAErrKind : Arena.CheckError → Option AErrKind
  | .notImplemented _ => some .notImplemented
  | .invalid _ => some .invalid
  | .internal _ => some .internal
  | .native _ => some .native

/-- **The port's error, as the twin kind it stands for.**  Total: a port
`Native` stands for the twin's `native` (task #98-NATIVE). -/
def absAErrKind : kernel.core_types.CheckError → Option AErrKind
  | .NotImplemented _ => some .notImplemented
  | .Invalid _ => some .invalid
  | .Internal _ => some .internal
  | .Native _ => some .native

@[simp] theorem absAErrKind_invalid (m) :
    absAErrKind (.Invalid m) = some .invalid := rfl
@[simp] theorem absAErrKind_internal (m) :
    absAErrKind (.Internal m) = some .internal := rfl

@[simp] theorem lAErrKind_notImplemented (m) :
    lAErrKind (.notImplemented m) = some .notImplemented := rfl
@[simp] theorem lAErrKind_invalid (m) :
    lAErrKind (.invalid m) = some .invalid := rfl
@[simp] theorem lAErrKind_internal (m) :
    lAErrKind (.internal m) = some .internal := rfl
@[simp] theorem lAErrKind_native (m) : lAErrKind (.native m) = some .native := rfl

/-- **What a Rust error claims about the twin's outcome**: that the twin
throws too, at the same kind — for all four kinds (task #98-NATIVE; the
quantified shape is from when a `Native` abstracted to `none`). -/
def AErrSim {γ : Type} (e : kernel.core_types.CheckError)
    (x : Except Arena.CheckError γ) : Prop :=
  ∀ k, absAErrKind e = some k → ∃ le, x = .error le ∧ lAErrKind le = some k

/-- The mirrored case. -/
theorem AErrSim.mk {γ : Type} {e : kernel.core_types.CheckError}
    {x : Except Arena.CheckError γ} {le : Arena.CheckError}
    (hx : x = .error le) (hk : absAErrKind e = lAErrKind le) :
    AErrSim e x := by
  intro k hk'
  exact ⟨le, hx, by rw [← hk]; exact hk'⟩

theorem AErrSim.notImplemented {γ : Type} {x : Except Arena.CheckError γ} {m s}
    (hx : x = .error (.notImplemented s)) :
    AErrSim (.NotImplemented m) x := AErrSim.mk hx rfl

theorem AErrSim.invalid {γ : Type} {x : Except Arena.CheckError γ} {m s}
    (hx : x = .error (.invalid s)) : AErrSim (.Invalid m) x := AErrSim.mk hx rfl

theorem AErrSim.internal {γ : Type} {x : Except Arena.CheckError γ} {m s}
    (hx : x = .error (.internal s)) : AErrSim (.Internal m) x := AErrSim.mk hx rfl

/-- An error of the kind `absAErrKind e` names, as a twin throw. -/
theorem AErrSim.of_kind {γ : Type} {e : kernel.core_types.CheckError}
    {x : Except Arena.CheckError γ} {le : Arena.CheckError} {k : AErrKind}
    (hx : x = .error le) (he : absAErrKind e = some k) (hle : lAErrKind le = some k) :
    AErrSim e x := AErrSim.mk hx (by rw [he, hle])

/-- **Error propagation through a bind**, the move every arm makes. -/
theorem AErrSim.bind {γ δ : Type} {e : kernel.core_types.CheckError}
    {x : Except Arena.CheckError γ} (h : AErrSim e x)
    (f : γ → Except Arena.CheckError δ) : AErrSim e (x >>= f) := by
  intro k hk
  obtain ⟨le, hx, hle⟩ := h k hk
  exact ⟨le, by rw [hx]; rfl, hle⟩

/-- `AErrSim` transported forward: whatever the twin throws at `x` it throws
at `y` too.  The wrapper/caller move. -/
theorem AErrSim.trans {γ δ : Type} {e : kernel.core_types.CheckError}
    {x : Except Arena.CheckError γ} {y : Except Arena.CheckError δ}
    (h : AErrSim e x) (hxy : ∀ le, x = .error le → y = .error le) :
    AErrSim e y := by
  intro k hk
  obtain ⟨le, hx, hk'⟩ := h k hk
  exact ⟨le, hxy le hx, hk'⟩

theorem AErrSim.of_eq {γ : Type} {e : kernel.core_types.CheckError}
    {x y : Except Arena.CheckError γ} (h : AErrSim e x) (hxy : y = x) :
    AErrSim e y := by rw [hxy]; exact h

/-! ## `Sim` — the statement a Theorem-2 lemma is written with

One definition for the whole tier, over the Rust outcome PAIR the arena's
functions return (`(Result R CheckError) × AState`), so that a lemma's
conclusion is one application and the `@[grind →]` rules key on it. -/

/-- **The read-only simulation**, for the arena's state READERS (`monad::{view,
view_app, derived_e, inst1_get, …}` and the `store::*` projections under
them): the twin's action answers the abstracted value and leaves the state
alone.  `Result`-valued but never `Err`, so there is no error arm. -/
def SimR {α β : Type} (A : α → β) (lst : AState) (r : α) (x : AM β) : Prop :=
  x.run lst = .ok (A r, lst)

theorem SimR.apply {α β : Type} {A : α → β} {lst : AState} {r : α} {x : AM β}
    (h : SimR A lst r x) : x.run lst = .ok (A r, lst) := h

/-! ## The lockstep outcome (task #97-P5-Core round 4)

`AOut` over `AStateRel₀` and without `Ext` or a `WF` slot: what a Theorem-2
statement concludes once the twin's own invariants (`StoreWF`, and `Ext`,
which is a statement about denotation) are Theorem 1's.  The Core tier's
`KnotRel`/`BodyRel` are stated with it; `Sim₀.toSim` is the projection back
for a consumer that still wants `Sim`, given the twin's two facts from
elsewhere. -/

/-- The lockstep obligation a Rust outcome puts on the twin's run. -/
def AOut₀ {α β : Type} (A : α → β) (pers : arena.store.PersTier)
    (o : core.result.Result α kernel.core_types.CheckError)
    (st' : arena.monad.AState)
    (x : Except Arena.CheckError (β × AState)) : Prop :=
  match o with
  | .Ok r => ∃ lst', x = .ok (A r, lst') ∧ AStateRel₀ pers st' lst' ∧
      AStateInv pers st'
  | .Err e => AErrSim e x

theorem AOut₀.ok {α β : Type} {A : α → β} {r : α}
    {pers : arena.store.PersTier} {lst' : AState} {st' : arena.monad.AState}
    {x : Except Arena.CheckError (β × AState)}
    (hx : x = .ok (A r, lst')) (hrel : AStateRel₀ pers st' lst')
    (hinv : AStateInv pers st') : AOut₀ A pers (.Ok r) st' x :=
  ⟨lst', hx, hrel, hinv⟩

theorem AOut₀.err {α β : Type} {A : α → β} {e : kernel.core_types.CheckError}
    {pers : arena.store.PersTier} {st' : arena.monad.AState}
    {x : Except Arena.CheckError (β × AState)} (h : AErrSim e x) :
    AOut₀ A pers (.Err e) st' x := h

theorem AOut₀.of_eq {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {o : core.result.Result α kernel.core_types.CheckError}
    {st' : arena.monad.AState} {x y : Except Arena.CheckError (β × AState)}
    (h : AOut₀ A pers o st' x) (hxy : y = x) : AOut₀ A pers o st' y := by
  rw [hxy]; exact h

/-- The lockstep simulation statement for a state-threading Rust function. -/
def Sim₀ {α β : Type} (A : α → β) (pers : arena.store.PersTier) (lst : AState)
    (o : core.result.Result α kernel.core_types.CheckError × arena.monad.AState)
    (x : AM β) : Prop :=
  AOut₀ A pers o.1 o.2 (x.run lst)

theorem Sim₀.apply {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {lst : AState} {r : α} {st' : arena.monad.AState} {x : AM β}
    (h : Sim₀ A pers lst (.Ok r, st') x) :
    ∃ lst', x.run lst = .ok (A r, lst') ∧ AStateRel₀ pers st' lst' ∧
      AStateInv pers st' := h

theorem Sim₀.apply_err {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {lst : AState} {e : kernel.core_types.CheckError} {st' : arena.monad.AState}
    {x : AM β} (h : Sim₀ A pers lst (.Err e, st') x) : AErrSim e (x.run lst) := h

/-- The lockstep outcome of a twin action that cannot fail and answers `()`. -/
def SimS₀ (pers : arena.store.PersTier) (lst : AState)
    (st' : arena.monad.AState) (x : AM Unit) : Prop :=
  ∃ lst', x.run lst = .ok ((), lst') ∧ AStateRel₀ pers st' lst' ∧
    AStateInv pers st'

theorem SimS₀.mk {pers : arena.store.PersTier} {lst lst' : AState}
    {st' : arena.monad.AState} {x : AM Unit}
    (hx : x.run lst = .ok ((), lst')) (hrel : AStateRel₀ pers st' lst')
    (hinv : AStateInv pers st') : SimS₀ pers lst st' x := ⟨lst', hx, hrel, hinv⟩

theorem SimS₀.apply {pers : arena.store.PersTier} {lst : AState}
    {st' : arena.monad.AState} {x : AM Unit} (h : SimS₀ pers lst st' x) :
    ∃ lst', x.run lst = .ok ((), lst') ∧ AStateRel₀ pers st' lst' ∧
      AStateInv pers st' := h

/-! ## The lockstep shapes, completed (task #97-T2-LOCKSTEP step 1)

Task #97-T2-AUDIT's ruling: Theorem 2 is a lockstep refinement, so its
statements are `AOut₀`/`Sim₀`/`SimS₀` (above) over `AStateRel₀`, and nothing
about the twin's store (`StoreWF`, `Ext`) is carried.  `AOut`, `Sim`, `SimS`
and `AStateRel` stay as **deprecated shims** until every lane has moved; the
lemmas here are the rest of the kit a lane needs to move: the error arms, the
destructors, and the projections from the old shapes.  A result that wants a
well-formedness predicate states it through `SimRel₀`'s relation
(`Refine2/Checker/Shape.lean`), as `SimRel` already does. -/

theorem AOut₀.destErr {α β : Type} {A : α → β}
    {e : kernel.core_types.CheckError} {pers : arena.store.PersTier}
    {st' : arena.monad.AState} {x : Except Arena.CheckError (β × AState)}
    (h : AOut₀ A pers (.Err e) st' x) : AErrSim e x := h

theorem Sim₀.mk {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {lst : AState}
    {o : core.result.Result α kernel.core_types.CheckError × arena.monad.AState}
    {x : AM β} (h : AOut₀ A pers o.1 o.2 (x.run lst)) : Sim₀ A pers lst o x := h

theorem Sim₀.dest {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {lst : AState}
    {o : core.result.Result α kernel.core_types.CheckError × arena.monad.AState}
    {x : AM β} (h : Sim₀ A pers lst o x) : AOut₀ A pers o.1 o.2 (x.run lst) := h

end ConRon.Refine2

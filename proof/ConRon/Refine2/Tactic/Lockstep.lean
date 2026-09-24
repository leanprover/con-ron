/-
# `ConRon.Refine2.Tactic.Lockstep` — the lockstep judgement and the `lockstep` tactic

Task #97-T2-TACTIC.  Theorem 2 in its lockstep shape (task #97-T2-AUDIT §6)
relates two programs doing the same operations in the same order, over a
state relation that says only "the same data in two representations".  So a
proof of one `_refines` lemma is a ZIP of two do-blocks: peel one bind on each
side, close the correspondence of the two callees with a registered lemma,
continue with the related results.  This file makes that zip a tactic.

## The judgement

`LS pers R m lst x` — *every outcome of the Rust computation `m` is matched by
the twin action `x` run from `lst`*: an `Ok a` by an `ok (b, lst')` with
`R a b` in a related post-state, an `Err e` by the twin throwing at the same
kind (`AErrSim`).  It is `Sim₀` with a relation for the answer instead of an
abstraction function, and with the Rust equation moved into the judgement, so
that the Rust program is visible in the GOAL beside the twin (`LS.toSim₀` is the
bridge back).  Four companion judgements carry the other Rust callee shapes:

| judgement | Rust callee shape | example |
|---|---|---|
| `LS`  | `Result (Result α CheckError × AState)` — state threaded | `intern_e_app`, a recursive call |
| `LSR` | `Result (Result α CheckError)` — reads, may fail | `view` |
| `LSV` | `Result α` — reads, total | `lift_get`, `inst_list_cutoff` |
| `LSW` | `Result AState` — writes, total | `lift_set` |
| `LSP` | `Result α`, **Rust only** — no twin counterpart | `fuel - 1#u64`, `dup2`, `eidx_nat_key`, `fail` |
| `LSM` | `Result (Result α × AState × M)` — a memoised walk, memo beside the result | `consts_resolve_f_go`, `intern_expr_go` |
| `LSRM` | `Result (Result α × M)` — a memoised reader walk | `all_level_params_defined_go` |

## The tactic — modelled on Aeneas's `progress`, not on `mvcgen`

`progress`/`step` keys a spec lemma on the program being stepped (the head of
the next bind), applies it, and introduces the outputs; `mvcgen` computes a
weakest precondition over a whole `do` block and leaves verification
conditions.  Theorem 2 needs the first: the two programs are stepped in
lockstep, the next bind's callee picks the lemma, and every step ends in the
related results as hypotheses.  A VC generator would have to thread the twin
through a WP of the Rust (or the reverse), and a failure would show up as an
unprovable VC far from its cause; here a failure is a goal stuck at the very
bind where the two programs stop doing the same thing, which is the
divergence detector the task asked for.

`lockstep` repeats `lockstep_step` over every goal and leaves the goals it
cannot move.  One step looks at the RUST side first:

* an `if`/`match`/`uncurry` on a variable: split (`cases`), normalise heads;
* a bind `f >>= k`: the bind rule by `f`'s type (the table above); its spec
  premise is closed by a `@[lockstep]` lemma or a LOCAL HYPOTHESIS (the
  induction hypothesis, a knot slot) filed under `f`'s head constant, of the
  same judgement.  The spec's twin action is not unified with the goal's:
  the rules take `x' = x`, closed by `congr 1` and the side tactic, so
  `absU i1` against `absU c + 1` is a side goal, not a unification failure.
  A spec argument that only its TWIN side mentions (a message string, the
  div/mod loop's `tried` list) is not a side goal either: it is fixed by
  that `x' = x` check, by unification with the goal's twin action;
  A Rust-only value step with no lemma keeps its equation (`LS.bind_eq`) —
  unless the callee reads the Rust state, which must have a twin partner:
  then the step FAILS with "the Rust reads the state at `f` and no
  @[lockstep] lemma pairs it with the twin's next action".  That message is
  the divergence detector;
* a leaf `ok (.Ok a, st)` / `ok (.Err e, st)`: against the twin's `pure` /
  its throwing action;
* anything else: a tail call, closed by a spec directly.

The twin side moves only when the Rust cannot: `pure`/`get` binds, and an
`if` decided by the facts the Rust steps produced (cheap tier first, the last
Rust test's polarity first).  A twin `if` in bind position is distributed over
its continuation first; one nothing decides is split as a last resort.  After every step the heads of both programs are
normalised by DEFINITIONAL steps (`headNorm`: beta, `let`, `uncurry` at a
pair, a `match` on constructors) and the twin alone by `simp only
[lockstep_simp]` (the abstraction equations, the twin's arm definitions);
nothing traverses the whole remaining Rust program.  A goal no step moves is
tried once against `lockstep_contra` (a branch the context rules out).

Side goals go to `lockstep_side`: `assumption`, `rfl`, `simp only
[lockstep_simp(, *)]`, then `scalar_tac`/`simp_all`; an arithmetic goal
(`=`/`<`/`≤` on `Nat`) goes to `omega`/`scalar_tac` early.  **No `grind`**
anywhere; `simp (config := {decide := true})` is the one `decide` path, and
every sample is kernel-checked by the build (`#print axioms` in each file).
`lockstep_stats` prints and resets the per-alternative timings of the side
tactics (a tuning aid).

## How to use it (the recipe the lane briefs point to)

    theorem f_refines … (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
        (hrun : rust_f pers st args = ok o) : Sim₀ A pers lst o (twinF …) := by
      refine LS.toSim₀ ?_ hrun
      rw [rust_f, twinF]          -- or the twin's `_succ`/`_unfold` equation
      lockstep

* A recursive function: state the `_aux` over `n` with the conclusion in `LS`
  form, `induction n`, then per case `intro …; rw [rust_f, twin_zero/succ];
  lockstep`.  The induction hypothesis is found in the context.
* Twin arms that are separate (well-founded) definitions: `attribute [local
  lockstep_simp] armApp armLam …`.
* A callee from another lane: its lemma in `LS`/`LSR`/`LSV`/`LSW`/`LSP` form,
  tagged `@[lockstep]`, or taken as a hypothesis.
* A new primitive pair: one `@[lockstep]` lemma (`Tactic/Prims.lean` has the
  shapes; `LSV.of_store_read` is a store read in one line); a new condition
  correspondence: one `@[lockstep_simp]` equation (`absU32_beq_app`).
* A goal left over is either a missing lemma (the message names the Rust
  callee) or a divergence (the twin's next action is a different operation).

## The moves for a port split into fragments (task #97-P5-Core round 5)

`lockstep_step` first tries `coreMove`, then the zip step above.  `coreMove`
fires only where the zip step cannot, so every lemma `lockstep` closed before
closes the same way.  It covers the port's habit of writing one twin function
as several Rust functions and of re-packing values between binds:

* **a Rust callee that is not a call**: `ok v >>= k` is fed to `k v` by
  REWRITING (`LS.rust_ok_bind`, `bind_tc_ok`; Aeneas's `Result` bind is not
  definitionally `k v` for the kernel, so a `replaceTargetDefEq` there is
  accepted by the elaborator and rejected by the kernel); a `do` block is
  re-associated (`LS.rust_assoc`); an `if` is split (`LS.rust_ite_bind`); a
  `match` on a variable, a tuple pattern (`uncurry`) or a `match` on a pair's
  projection is a case split;
* **a fragment**: a Rust function registered `@[lockstep_inline]` is unfolded
  in place, on the Rust side only;
* **a store-level step** (`(Result α, EStore)`, the caller rebuilding
  `{ st with store := e }`): the judgement `LSS` and `LSS.bind`;
* **a read in tail position** (`f >>= fun o => ok (o, st)`): `LSR.tail_ls`;
* **a Rust-only step whose twin partner is a pure expression**: its `LSP`
  lemma concludes `TwinEq <twin expr> <abs of the Rust value>`, and the twin
  side is rewritten with every `TwinEq` in the context after every step;
* **a tag-guarded projection**: the port tests a handle's tag and reads the
  typed projection (`view_const`), the twin tests the same tag and reads the
  whole `view`.  Under the tag the view IS the projection (`tagView_*`, no
  `StoreWF`), and the `@[lockstep_twin]` rules (`LS.twin_view_*`) rewrite the
  twin to `viewC h >>= danglingOr …`; a rule is kept only if the port's next
  step then goes through.

The error arm of a bind is closed through an `ok (…) >>= k'` repack too
(`lockstep_errarm`).  `lockstep_core` is a synonym of `lockstep`.
-/
import ConRon.Refine2.Shape
import ConRon.Refine2.Tactic.Attr

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2

open ConRon.Arena

namespace Lockstep

/-! ## The judgements -/

/-- What a Rust outcome `o` in post-state `st'` claims about a twin run. -/
def LOut {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop)
    (o : core.result.Result α kernel.core_types.CheckError)
    (st' : arena.monad.AState) (y : Except Arena.CheckError (β × AState)) : Prop :=
  match o with
  | .Ok a => ∃ b lst', y = .ok (b, lst') ∧ R a b ∧ AStateRel₀ pers st' lst' ∧
      AStateInv pers st'
  | .Err e => AErrSim e y

/-- **The lockstep judgement** for a state-threading Rust computation. -/
def LS {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop)
    (m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState))
    (lst : AState) (x : AM β) : Prop :=
  ∀ o st', m = ok (o, st') → LOut pers R o st' (x.run lst)

/-- A Rust READ that may fail: the state is `st` before and after. -/
def LSR {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop)
    (m : Result (core.result.Result α kernel.core_types.CheckError))
    (st : arena.monad.AState) (lst : AState) (x : AM β) : Prop :=
  ∀ o, m = ok o → LOut pers R o st (x.run lst)

/-- A total Rust READ. -/
def LSV {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop)
    (m : Result α) (st : arena.monad.AState) (lst : AState) (x : AM β) : Prop :=
  ∀ a, m = ok a → LOut pers R (.Ok a) st (x.run lst)

/-- A total Rust WRITE, which returns the new state. -/
def LSW (pers : arena.store.PersTier) (m : Result arena.monad.AState)
    (lst : AState) (x : AM Unit) : Prop :=
  ∀ st', m = ok st' → LOut pers (fun _ _ => True) (.Ok ()) st' (x.run lst)

/-- A Rust-only step: what its answer satisfies. -/
def LSP {α : Type} (m : Result α) (P : α → Prop) : Prop :=
  ∀ a, m = ok a → P a

/-- The error arm of a Rust stateful bind: the continuation, fed an `Err e`,
returns `Err e` again (the generated `| Err _ => ok (r, st1)`). -/
def ErrArm {γ : Type}
    (m : Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState))
    (e : kernel.core_types.CheckError) : Prop :=
  ∀ o st', m = ok (o, st') → o = .Err e

/-! ## Bridges to the statement shapes -/

theorem LS.toSim₀ {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} {o}
    (h : LS pers (fun a b => b = A a) m lst x) (hm : m = ok o) : Sim₀ A pers lst o x := by
  obtain ⟨o, st'⟩ := o
  have := h o st' hm
  show AOut₀ A pers o st' (x.run lst)
  cases o with
  | Err e => exact this
  | Ok a =>
    obtain ⟨b, lst', hx, rfl, h1, h2⟩ := this
    exact ⟨lst', hx, h1, h2⟩

theorem LS.ofSim₀ {α β : Type} {A : α → β} {pers : arena.store.PersTier}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β}
    (h : ∀ o, m = ok o → Sim₀ A pers lst o x) : LS pers (fun a b => b = A a) m lst x := by
  intro o st' hm
  have := h _ hm
  cases o with
  | Err e => exact this
  | Ok a =>
    obtain ⟨lst', hx, h1, h2⟩ := this
    exact ⟨_, lst', hx, rfl, h1, h2⟩

theorem LSW.ofSimS₀ {pers : arena.store.PersTier} {m : Result arena.monad.AState}
    {lst : AState} {x : AM Unit}
    (h : ∀ st', m = ok st' → SimS₀ pers lst st' x) : LSW pers m lst x := by
  intro st' hm
  obtain ⟨lst', hx, h1, h2⟩ := h st' hm
  exact ⟨(), lst', hx, trivial, h1, h2⟩

/-! ## The bind rules

Each takes the spec of the Rust callee `f` against a twin action `x'`, and
`x' = x` for the twin action the goal actually binds. -/

theorem run_bind_ok {β δ : Type} {x : AM β} {g : β → AM δ} {lst lst' : AState} {b : β}
    (hx : x.run lst = .ok (b, lst')) : (x >>= g).run lst = (g b).run lst' := by
  rw [StateT.run_bind, hx]; rfl

theorem errSim_bind {β δ : Type} {e} {x : AM β} {g : β → AM δ} {lst : AState}
    (h : AErrSim e (x.run lst)) : AErrSim e ((x >>= g).run lst) := by
  rw [StateT.run_bind]; exact AErrSim.bind h _

theorem LS.bind {α γ β δ : Type} {pers : arena.store.PersTier}
    {R₁ : α → β → Prop} {R : γ → δ → Prop}
    {f : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {k : core.result.Result α kernel.core_types.CheckError × arena.monad.AState →
      Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x' x : AM β} {g : β → AM δ}
    (hf : LS pers R₁ f lst x') (hx : x' = x)
    (he : ∀ e st1, ErrArm (k (.Err e, st1)) e)
    (hk : ∀ a b st1 lst1, R₁ a b → AStateRel₀ pers st1 lst1 → AStateInv pers st1 →
      LS pers R (k (.Ok a, st1)) lst1 (g b)) :
    LS pers R (f >>= k) lst (x >>= g) := by
  subst hx
  intro o st' hm
  obtain ⟨⟨r, st1⟩, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have h1 := hf r st1 hf1
  cases r with
  | Err e =>
    have := he e st1 o st' hk1
    subst this
    exact errSim_bind h1
  | Ok a =>
    obtain ⟨b, lst1, hx1, hR, hrel, hinv⟩ := h1
    rw [run_bind_ok hx1]
    exact hk a b st1 lst1 hR hrel hinv o st' hk1

theorem LSR.bind {α γ β δ : Type} {pers : arena.store.PersTier}
    {R₁ : α → β → Prop} {R : γ → δ → Prop}
    {f : Result (core.result.Result α kernel.core_types.CheckError)}
    {st : arena.monad.AState}
    {k : core.result.Result α kernel.core_types.CheckError →
      Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x' x : AM β} {g : β → AM δ}
    (hf : LSR pers R₁ f st lst x') (hx : x' = x)
    (he : ∀ e, ErrArm (k (.Err e)) e)
    (hk : ∀ a b lst1, R₁ a b → AStateRel₀ pers st lst1 → AStateInv pers st →
      LS pers R (k (.Ok a)) lst1 (g b)) :
    LS pers R (f >>= k) lst (x >>= g) := by
  subst hx
  intro o st' hm
  obtain ⟨r, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have h1 := hf r hf1
  cases r with
  | Err e =>
    have := he e o st' hk1
    subst this
    exact errSim_bind h1
  | Ok a =>
    obtain ⟨b, lst1, hx1, hR, hrel, hinv⟩ := h1
    rw [run_bind_ok hx1]
    exact hk a b lst1 hR hrel hinv o st' hk1

theorem LSV.bind {α γ β δ : Type} {pers : arena.store.PersTier}
    {R₁ : α → β → Prop} {R : γ → δ → Prop}
    {f : Result α} {st : arena.monad.AState}
    {k : α → Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x' x : AM β} {g : β → AM δ}
    (hf : LSV pers R₁ f st lst x') (hx : x' = x)
    (hk : ∀ a b lst1, R₁ a b → AStateRel₀ pers st lst1 → AStateInv pers st →
      LS pers R (k a) lst1 (g b)) :
    LS pers R (f >>= k) lst (x >>= g) := by
  subst hx
  intro o st' hm
  obtain ⟨a, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  obtain ⟨b, lst1, hx1, hR, hrel, hinv⟩ := hf a hf1
  rw [run_bind_ok hx1]
  exact hk a b lst1 hR hrel hinv o st' hk1

theorem LSW.bind {γ δ : Type} {pers : arena.store.PersTier} {R : γ → δ → Prop}
    {f : Result arena.monad.AState}
    {k : arena.monad.AState →
      Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x' x : AM Unit} {g : Unit → AM δ}
    (hf : LSW pers f lst x') (hx : x' = x)
    (hk : ∀ st1 lst1, AStateRel₀ pers st1 lst1 → AStateInv pers st1 →
      LS pers R (k st1) lst1 (g ())) :
    LS pers R (f >>= k) lst (x >>= g) := by
  subst hx
  intro o st' hm
  obtain ⟨st1, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  obtain ⟨b, lst1, hx1, -, hrel, hinv⟩ := hf st1 hf1
  rw [run_bind_ok hx1]
  exact hk st1 lst1 hrel hinv o st' hk1

/-- A Rust-only step: the twin does nothing. -/
theorem LSP.bind {α γ δ : Type} {pers : arena.store.PersTier} {R : γ → δ → Prop}
    {f : Result α} {P : α → Prop}
    {k : α → Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM δ}
    (hf : LSP f P) (hk : ∀ a, P a → LS pers R (k a) lst x) :
    LS pers R (f >>= k) lst x := by
  intro o st' hm
  obtain ⟨a, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact hk a (hf a hf1) o st' hk1

/-- The fallback Rust-only step: keep the equation. -/
theorem LS.bind_eq {α γ δ : Type} {pers : arena.store.PersTier} {R : γ → δ → Prop}
    {f : Result α}
    {k : α → Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM δ}
    (hk : ∀ a, f = ok a → LS pers R (k a) lst x) :
    LS pers R (f >>= k) lst x := by
  intro o st' hm
  obtain ⟨a, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact hk a hf1 o st' hk1

/-- A tail call. -/
theorem LS.tail {α β : Type} {pers : arena.store.PersTier} {R₁ R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x' x : AM β}
    (hf : LS pers R₁ m lst x') (hx : x' = x) (hR : ∀ a b, R₁ a b → R a b) :
    LS pers R m lst x := by
  subst hx
  intro o st' hm
  have h := hf o st' hm
  cases o with
  | Err e => exact h
  | Ok a =>
    obtain ⟨b, lst', h1, h2, h3, h4⟩ := h
    exact ⟨b, lst', h1, hR _ _ h2, h3, h4⟩

/-! ## Leaves and branches -/

theorem LS.pure {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {a : α} {b : β} {st : arena.monad.AState} {lst : AState}
    (hR : R a b) (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st) :
    LS pers R (ok (.Ok a, st)) lst (Pure.pure b) := by
  intro o st' hm
  cases Result.ok_injective hm
  exact ⟨b, lst, rfl, hR, hrel, hinv⟩

theorem LS.err {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {e : kernel.core_types.CheckError} {st : arena.monad.AState} {lst : AState} {x : AM β}
    (h : AErrSim e (x.run lst)) :
    LS pers R (ok (.Err e, st)) lst x := by
  intro o st' hm
  cases Result.ok_injective hm
  exact h

theorem LS.ite {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {c : Prop} [Decidable c]
    {m₁ m₂ : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β}
    (h₁ : c → LS pers R m₁ lst x) (h₂ : ¬ c → LS pers R m₂ lst x) :
    LS pers R (if c then m₁ else m₂) lst x := by
  by_cases hc : c
  · rw [if_pos hc]; exact h₁ hc
  · rw [if_neg hc]; exact h₂ hc

theorem LS.twin_ite_pos {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {c : Prop} [Decidable c]
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x y : AM β} (hc : c) (h : LS pers R m lst x) :
    LS pers R m lst (if c then x else y) := by
  rw [if_pos hc]; exact h

theorem LS.twin_ite_neg {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {c : Prop} [Decidable c]
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x y : AM β} (hc : ¬ c) (h : LS pers R m lst y) :
    LS pers R m lst (if c then x else y) := by
  rw [if_neg hc]; exact h

/-- The twin's own error leaf. -/
theorem errSim_fail {γ : Type} {e : kernel.core_types.CheckError} {le : Arena.CheckError}
    {lst : AState} (hk : absAErrKind e = lAErrKind le) :
    AErrSim e ((Arena.fail le : AM γ).run lst) := AErrSim.mk rfl hk

theorem errSim_throw {γ : Type} {e : kernel.core_types.CheckError} {le : Arena.CheckError}
    {lst : AState} (hk : absAErrKind e = lAErrKind le) :
    AErrSim e ((throw le : AM γ).run lst) := AErrSim.mk rfl hk

theorem errArm_ok {γ : Type} {e : kernel.core_types.CheckError} {st : arena.monad.AState} :
    ErrArm (γ := γ) (ok (.Err e, st)) e := by
  intro o st' h; cases Result.ok_injective h; rfl

/-- An error arm that does Rust-only work before returning the error (the
Rust's `let st3 ← drop_scratch st2; ok (r, st3)` after a failed body: the twin
throws, and the error claims nothing about the state). -/
theorem errArm_bind {α γ : Type} {e : kernel.core_types.CheckError} {m : Result α}
    {k : α → Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState)}
    (h : ∀ a, ErrArm (k a) e) : ErrArm (m >>= k) e := by
  intro o st' hm
  obtain ⟨a, _, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  exact h a o st' h2

theorem uncurry_apply_proj {α β γ : Type} (f : α → β → γ) (p : α × β) :
    Aeneas.Std.uncurry f p = f p.1 p.2 := by
  obtain ⟨a, b⟩ := p; rfl

/-! ## The Rust-only judgement as a goal (state-free functions) -/

theorem LSP.bind' {α β : Type} {f : Result α} {P : α → Prop} {k : α → Result β}
    {Q : β → Prop} (hf : LSP f P) (hk : ∀ a, P a → LSP (k a) Q) : LSP (f >>= k) Q := by
  intro b hb
  obtain ⟨a, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb
  exact hk a (hf a h1) b h2

theorem LSP.bind_eq {α β : Type} {f : Result α} {k : α → Result β}
    {Q : β → Prop} (hk : ∀ a, f = ok a → LSP (k a) Q) : LSP (f >>= k) Q := by
  intro b hb
  obtain ⟨a, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hb
  exact hk a h1 b h2

theorem LSP.ite {α : Type} {c : Prop} [Decidable c] {m₁ m₂ : Result α} {Q : α → Prop}
    (h₁ : c → LSP m₁ Q) (h₂ : ¬ c → LSP m₂ Q) : LSP (if c then m₁ else m₂) Q := by
  by_cases hc : c
  · rw [if_pos hc]; exact h₁ hc
  · rw [if_neg hc]; exact h₂ hc

theorem LSP.ret {α : Type} {v : α} {Q : α → Prop} (h : Q v) : LSP (ok v) Q := by
  intro a ha; cases Result.ok_injective ha; exact h

theorem LSP.tail {α : Type} {m : Result α} {P Q : α → Prop}
    (hf : LSP m P) (hPQ : ∀ a, P a → Q a) : LSP m Q :=
  fun a ha => hPQ a (hf a ha)

/-! ## Pure Rust-only specs of the machine words -/

@[lockstep_simp] theorem u64_one_val : (1#u64 : Std.U64).val = 1 := rfl
@[lockstep_simp] theorem usize_one_val : (1#usize : Std.Usize).val = 1 := rfl
@[lockstep_simp] theorem u64_zero_val : (0#u64 : Std.U64).val = 0 := rfl

theorem LSP.u64_sub (x y : Std.U64) :
    LSP (x - y) (fun z => z.val = x.val - y.val ∧ y.val ≤ x.val) := by
  intro z h
  have := ConRon.Refine.Nat.usub_val h
  exact ⟨this.2, this.1⟩

theorem LSP.u64_add (x y : Std.U64) :
    LSP (x + y) (fun z => z.val = x.val + y.val) := by
  intro z h
  exact (ConRon.Refine.Nat.uadd_val h)

/-- A twin-only `pure` step. -/
theorem LS.twin_pure_bind {α β δ : Type} {pers : arena.store.PersTier} {R : α → δ → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {v : β} {g : β → AM δ} (h : LS pers R m lst (g v)) :
    LS pers R m lst (Pure.pure v >>= g) := by
  rw [pure_bind]; exact h

/-- The twin's tail action is a bind with `pure` (task #97-T2-LOCKSTEP lane
Checker): the Rust still has a bind to make — `drop_scratch` and then the leaf
— where the twin's program ENDS in the partner action (`…; dropScratch`). -/
theorem LS.twin_bind_pure {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} (h : LS pers R m lst (x >>= fun b => Pure.pure b)) :
    LS pers R m lst x := by
  rw [bind_pure] at h; exact h

/-- A twin-only `get`. -/
theorem LS.twin_get_bind {α δ : Type} {pers : arena.store.PersTier} {R : α → δ → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {g : AState → AM δ} (h : LS pers R m lst (g lst)) :
    LS pers R m lst (MonadState.get >>= g) := by
  intro o st' hm
  exact h o st' hm

/-! ## Task #97-P5-Core round 5: the moves for a port split into fragments

`lockstep` below tries these before the zip step (`coreMove`): a Rust callee
`ok v` (fed to its continuation by REWRITING, `bind_tc_ok`: Aeneas's `Result`
bind is not definitionally `k v` for the kernel), a Rust callee that is itself
a `do` block, an `if` or a `match` (a fragment unfolded in place), a fragment
registered `@[lockstep_inline]`, a store-level step (`LSS`), a read in tail
position (`LSR.tail_ls`), the `TwinEq` facts of Rust-only steps, and the
tag-guarded projections (`@[lockstep_twin]`).  None fires where the zip step
applies, so a lemma `lockstep` closed before is closed the same way. -/

theorem LS.rust_ok_bind {γ α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {v : γ}
    {k : γ → Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β} (h : LS pers R (k v) lst x) :
    LS pers R (ok v >>= k) lst x := by
  rw [bind_tc_ok]; exact h

theorem LSP.rust_ok_bind {γ α : Type} {v : γ} {k : γ → Result α} {Q : α → Prop}
    (h : LSP (k v) Q) : LSP (ok v >>= k) Q := by
  rw [bind_tc_ok]; exact h

theorem ErrArm.of_ok_bind {γ δ : Type} {v : δ}
    {k : δ → Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState)}
    {e : kernel.core_types.CheckError} (h : ErrArm (k v) e) : ErrArm (ok v >>= k) e := by
  rw [bind_tc_ok]; exact h

theorem errArm_of_eq {γ : Type} {e : kernel.core_types.CheckError} {st : arena.monad.AState}
    {m : Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState)}
    (h : m = ok (.Err e, st)) : ErrArm m e := by
  subst h; exact errArm_ok

/-- A Rust read in tail position: `f >>= fun o => ok (o, st)`. -/
theorem LSR.tail_ls {α β : Type} {pers : arena.store.PersTier} {R₁ R : α → β → Prop}
    {f : Result (core.result.Result α kernel.core_types.CheckError)}
    {st : arena.monad.AState} {lst : AState} {x' x : AM β}
    (hf : LSR pers R₁ f st lst x') (hx : x' = x) (hR : ∀ a b, R₁ a b → R a b) :
    LS pers R (f >>= fun o => ok (o, st)) lst x := by
  subst hx
  intro o st' hm
  obtain ⟨r, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective h2)
  have h := hf r h1
  cases r with
  | Err e => exact h
  | Ok a =>
    obtain ⟨b, lst', h1, h2, h3, h4⟩ := h
    exact ⟨b, lst', h1, hR _ _ h2, h3, h4⟩

/-- A read-shaped statement proved by the `LS` zip. -/
theorem LSR.of_LS {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError)}
    {st : arena.monad.AState} {lst : AState} {x : AM β}
    (h : LS pers R (m >>= fun o => ok (o, st)) lst x) : LSR pers R m st lst x := by
  intro o hm
  exact h o st (by rw [hm, bind_tc_ok])

/-! ## The store-level judgement -/

/-- A Rust step over the bare expression store: its outcome, in the state the
caller rebuilds from the returned store. -/
def LSS {α β : Type} (pers : arena.store.PersTier) (R : α → β → Prop)
    (m : Result (core.result.Result α kernel.core_types.CheckError × arena.store.EStore))
    (st : arena.monad.AState) (lst : AState) (x : AM β) : Prop :=
  ∀ o s', m = ok (o, s') → LOut pers R o { st with store := s' } (x.run lst)

theorem LSS.bind {α γ β δ : Type} {pers : arena.store.PersTier}
    {R₁ : α → β → Prop} {R : γ → δ → Prop}
    {f : Result (core.result.Result α kernel.core_types.CheckError × arena.store.EStore)}
    {st : arena.monad.AState}
    {k : core.result.Result α kernel.core_types.CheckError × arena.store.EStore →
      Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x' x : AM β} {g : β → AM δ}
    (hf : LSS pers R₁ f st lst x') (hx : x' = x)
    (he : ∀ e s', ErrArm (k (.Err e, s')) e)
    (hk : ∀ a b s' lst1, R₁ a b → AStateRel₀ pers { st with store := s' } lst1 →
      AStateInv pers { st with store := s' } →
      LS pers R (k (.Ok a, s')) lst1 (g b)) :
    LS pers R (f >>= k) lst (x >>= g) := by
  subst hx
  intro o st' hm
  obtain ⟨⟨r, s1⟩, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have h1 := hf r s1 hf1
  cases r with
  | Err e =>
    have := he e s1 o st' hk1
    subst this
    exact errSim_bind h1
  | Ok a =>
    obtain ⟨b, lst1, hx1, hR, hrel, hinv⟩ := h1
    rw [run_bind_ok hx1]
    exact hk a b s1 lst1 hR hrel hinv o st' hk1

/-- A tail call to a store-level step. -/
theorem LSS.tail {α β : Type} {pers : arena.store.PersTier} {R₁ R : α → β → Prop}
    {f : Result (core.result.Result α kernel.core_types.CheckError × arena.store.EStore)}
    {st : arena.monad.AState} {lst : AState} {x' x : AM β}
    (hf : LSS pers R₁ f st lst x') (hx : x' = x) (hR : ∀ a b, R₁ a b → R a b) :
    LS pers R (f >>= fun p => ok (p.1, { st with store := p.2 })) lst x := by
  subst hx
  intro o st' hm
  obtain ⟨⟨r, s1⟩, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  cases Result.ok_injective hk1
  have h := hf r s1 hf1
  cases r with
  | Err e => exact h
  | Ok a =>
    obtain ⟨b, lst', h1, h2, h3, h4⟩ := h
    exact ⟨b, lst', h1, hR _ _ h2, h3, h4⟩

/-! ## Walks that return their memo beside the `Result` (task #97-T2-TACTIC round 2)

A memoised Rust walk hands its memo back OUTSIDE the `Result` (a `&mut`
borrow comes back whatever happened): `(Result<T>, AState, M)` for a walk
that threads the state (`arena::intern`'s `intern_expr_go`,
`consts_resolve_f_go`), `(Result<T>, M)` for a reader
(`all_level_params_defined_go`).  Such a computation is not `LS`'s shape, but
it IS one after the memo moves into the answer: `packM`/`packRM` do that, and
`LSM`/`LSRM` are `LS` of the packed computation, with the answer relation on
`(answer, memo)`.  So the whole zip applies unchanged; the tactic unfolds an
`LSM`/`LSRM` goal to its `LS`, pushes `packM` through the Rust program
(`LS.packM_bind`, `_ok_ok`, `_ok_err`, `_ite`), and steps a memo walk as a
callee with `LS.bindM`/`LS.bindRM` or in tail position with `LS.tailM`/
`LS.tailRM`, its spec an `LSM`/`LSRM` lemma or hypothesis.  An error claims
nothing about the memo, as the twin throws. -/

/-- A state walk's outcome with its memo moved into the answer. -/
def packMemo {α M : Type} :
    core.result.Result α kernel.core_types.CheckError × arena.monad.AState × M →
    core.result.Result (α × M) kernel.core_types.CheckError × arena.monad.AState
  | (.Ok a, st, mm) => (.Ok (a, mm), st)
  | (.Err e, st, _) => (.Err e, st)

/-- A state walk with its memo moved into the answer. -/
def packM {α M : Type}
    (m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState × M)) :
    Result (core.result.Result (α × M) kernel.core_types.CheckError × arena.monad.AState) :=
  m >>= fun p => ok (packMemo p)

/-- A reader walk's outcome with its memo moved into the answer, at the state
`st` it read. -/
def packRMemo {α M : Type} (st : arena.monad.AState) :
    core.result.Result α kernel.core_types.CheckError × M →
    core.result.Result (α × M) kernel.core_types.CheckError × arena.monad.AState
  | (.Ok a, mm) => (.Ok (a, mm), st)
  | (.Err e, _) => (.Err e, st)

/-- A reader walk with its memo moved into the answer. -/
def packRM {α M : Type} (st : arena.monad.AState)
    (m : Result (core.result.Result α kernel.core_types.CheckError × M)) :
    Result (core.result.Result (α × M) kernel.core_types.CheckError × arena.monad.AState) :=
  m >>= fun p => ok (packRMemo st p)

/-- **The lockstep judgement of a memoised state walk**: `LS` of the walk with
its memo moved into the answer; `R` relates `(answer, memo)` to the twin's
answer (typically the twin's `(answer, memo)` pair). -/
def LSM {α β M : Type} (pers : arena.store.PersTier) (R : α × M → β → Prop)
    (m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState × M))
    (lst : AState) (x : AM β) : Prop :=
  LS pers R (packM m) lst x

/-- **The lockstep judgement of a memoised reader walk** at the state `st`. -/
def LSRM {α β M : Type} (pers : arena.store.PersTier) (R : α × M → β → Prop)
    (m : Result (core.result.Result α kernel.core_types.CheckError × M))
    (st : arena.monad.AState) (lst : AState) (x : AM β) : Prop :=
  LS pers R (packRM st m) lst x

theorem LSM.toLS {α β M : Type} {pers : arena.store.PersTier} {R : α × M → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState × M)}
    {lst : AState} {x : AM β} (h : LSM pers R m lst x) : LS pers R (packM m) lst x := h

/-- What an `LSM` says about one outcome, unpacked. -/
theorem LSM.apply {α β M : Type} {pers : arena.store.PersTier} {R : α × M → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState × M)}
    {lst : AState} {x : AM β} (h : LSM pers R m lst x) {o st' mm}
    (hm : m = ok (o, st', mm)) :
    match o with
    | .Ok a => ∃ b lst', x.run lst = .ok (b, lst') ∧ R (a, mm) b ∧ AStateRel₀ pers st' lst' ∧
        AStateInv pers st'
    | .Err e => AErrSim e (x.run lst) := by
  have := h (packMemo (o, st', mm)).1 (packMemo (o, st', mm)).2
    (by simp only [packM, hm, bind_tc_ok])
  cases o <;> exact this

/-- What an `LSRM` says about one outcome, unpacked. -/
theorem LSRM.apply {α β M : Type} {pers : arena.store.PersTier} {R : α × M → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × M)}
    {st : arena.monad.AState} {lst : AState} {x : AM β} (h : LSRM pers R m st lst x) {o mm}
    (hm : m = ok (o, mm)) :
    match o with
    | .Ok a => ∃ b lst', x.run lst = .ok (b, lst') ∧ R (a, mm) b ∧ AStateRel₀ pers st lst' ∧
        AStateInv pers st
    | .Err e => AErrSim e (x.run lst) := by
  have := h (packRMemo st (o, mm)).1 (packRMemo st (o, mm)).2
    (by simp only [packRM, hm, bind_tc_ok])
  cases o <;> exact this

/-- `LSM` from its outcomes. -/
theorem LSM.intro {α β M : Type} {pers : arena.store.PersTier} {R : α × M → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState × M)}
    {lst : AState} {x : AM β}
    (h : ∀ o st' mm, m = ok (o, st', mm) →
      match o with
      | .Ok a => ∃ b lst', x.run lst = .ok (b, lst') ∧ R (a, mm) b ∧
          AStateRel₀ pers st' lst' ∧ AStateInv pers st'
      | .Err e => AErrSim e (x.run lst)) : LSM pers R m lst x := by
  intro o st' hm
  obtain ⟨⟨r, st1, mm⟩, h1, h2⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have := h r st1 mm h1
  cases r with
  | Ok a =>
    cases Result.ok_injective h2
    obtain ⟨b, lst', hx, hR, h3, h4⟩ := this
    exact ⟨b, lst', hx, hR, h3, h4⟩
  | Err e => cases Result.ok_injective h2; exact this

/-! ### The Rust side of a packed walk -/

theorem LS.packM_bind {γ α β M : Type} {pers : arena.store.PersTier} {R : α × M → β → Prop}
    {f : Result γ}
    {k : γ → Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState × M)}
    {lst : AState} {x : AM β} (h : LS pers R (f >>= fun p => packM (k p)) lst x) :
    LS pers R (packM (f >>= k)) lst x := by
  unfold packM at h ⊢; rw [Aeneas.Std.bind_assoc_eq]; exact h

theorem LS.packM_ok_ok {α β M : Type} {pers : arena.store.PersTier} {R : α × M → β → Prop}
    {a : α} {st : arena.monad.AState} {mm : M} {lst : AState} {x : AM β}
    (h : LS pers R (ok (.Ok (a, mm), st)) lst x) :
    LS pers R (packM (ok (.Ok a, st, mm))) lst x := by
  unfold packM; rw [bind_tc_ok]; exact h

theorem LS.packM_ok_err {α β M : Type} {pers : arena.store.PersTier} {R : α × M → β → Prop}
    {e : kernel.core_types.CheckError} {st : arena.monad.AState} {mm : M} {lst : AState}
    {x : AM β} (h : LS pers R (ok (.Err e, st)) lst x) :
    LS pers R (packM (ok ((.Err e : core.result.Result α _), st, mm))) lst x := by
  unfold packM; rw [bind_tc_ok]; exact h

theorem LS.packM_ite {α β M : Type} {pers : arena.store.PersTier} {R : α × M → β → Prop}
    {c : Prop} [Decidable c]
    {a b : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState × M)}
    {lst : AState} {x : AM β}
    (h : LS pers R (if c then packM a else packM b) lst x) :
    LS pers R (packM (if c then a else b)) lst x := by
  by_cases hc : c
  · rw [if_pos hc] at h ⊢; exact h
  · rw [if_neg hc] at h ⊢; exact h

theorem LS.packRM_bind {γ α β M : Type} {pers : arena.store.PersTier} {R : α × M → β → Prop}
    {st : arena.monad.AState} {f : Result γ}
    {k : γ → Result (core.result.Result α kernel.core_types.CheckError × M)}
    {lst : AState} {x : AM β} (h : LS pers R (f >>= fun p => packRM st (k p)) lst x) :
    LS pers R (packRM st (f >>= k)) lst x := by
  unfold packRM at h ⊢; rw [Aeneas.Std.bind_assoc_eq]; exact h

theorem LS.packRM_ok_ok {α β M : Type} {pers : arena.store.PersTier} {R : α × M → β → Prop}
    {a : α} {st : arena.monad.AState} {mm : M} {lst : AState} {x : AM β}
    (h : LS pers R (ok (.Ok (a, mm), st)) lst x) :
    LS pers R (packRM st (ok (.Ok a, mm))) lst x := by
  unfold packRM; rw [bind_tc_ok]; exact h

theorem LS.packRM_ok_err {α β M : Type} {pers : arena.store.PersTier} {R : α × M → β → Prop}
    {e : kernel.core_types.CheckError} {st : arena.monad.AState} {mm : M} {lst : AState}
    {x : AM β} (h : LS pers R (ok (.Err e, st)) lst x) :
    LS pers R (packRM st (ok ((.Err e : core.result.Result α _), mm))) lst x := by
  unfold packRM; rw [bind_tc_ok]; exact h

theorem LS.packRM_ite {α β M : Type} {pers : arena.store.PersTier} {R : α × M → β → Prop}
    {st : arena.monad.AState} {c : Prop} [Decidable c]
    {a b : Result (core.result.Result α kernel.core_types.CheckError × M)}
    {lst : AState} {x : AM β}
    (h : LS pers R (if c then packRM st a else packRM st b) lst x) :
    LS pers R (packRM st (if c then a else b)) lst x := by
  by_cases hc : c
  · rw [if_pos hc] at h ⊢; exact h
  · rw [if_neg hc] at h ⊢; exact h

theorem ErrArm.packM_ok_err {α M : Type} {e : kernel.core_types.CheckError}
    {st : arena.monad.AState} {mm : M} :
    ErrArm (packM (ok ((.Err e : core.result.Result α _), st, mm))) e := by
  unfold packM; rw [bind_tc_ok]; exact errArm_ok

theorem ErrArm.packM_bind {γ α M : Type} {e : kernel.core_types.CheckError} {f : Result γ}
    {k : γ → Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState × M)}
    (h : ErrArm (f >>= fun p => packM (k p)) e) : ErrArm (packM (f >>= k)) e := by
  unfold packM at h ⊢; rw [Aeneas.Std.bind_assoc_eq]; exact h

theorem ErrArm.packRM_ok_err {α M : Type} {e : kernel.core_types.CheckError}
    {st : arena.monad.AState} {mm : M} :
    ErrArm (packRM st (ok ((.Err e : core.result.Result α _), mm))) e := by
  unfold packRM; rw [bind_tc_ok]; exact errArm_ok

theorem ErrArm.packRM_bind {γ α M : Type} {e : kernel.core_types.CheckError}
    {st : arena.monad.AState} {f : Result γ}
    {k : γ → Result (core.result.Result α kernel.core_types.CheckError × M)}
    (h : ErrArm (f >>= fun p => packRM st (k p)) e) : ErrArm (packRM st (f >>= k)) e := by
  unfold packRM at h ⊢; rw [Aeneas.Std.bind_assoc_eq]; exact h

/-! ### A memoised walk as a callee -/

/-- A memoised state walk as a callee (its memo comes back beside the result). -/
theorem LS.bindM {α γ β δ M : Type} {pers : arena.store.PersTier}
    {R₁ : α × M → β → Prop} {R : γ → δ → Prop}
    {f : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState × M)}
    {k : core.result.Result α kernel.core_types.CheckError × arena.monad.AState × M →
      Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x' x : AM β} {g : β → AM δ}
    (hf : LSM pers R₁ f lst x') (hx : x' = x)
    (he : ∀ e st1 mm, ErrArm (k (.Err e, st1, mm)) e)
    (hk : ∀ a mm b st1 lst1, R₁ (a, mm) b → AStateRel₀ pers st1 lst1 → AStateInv pers st1 →
      LS pers R (k (.Ok a, st1, mm)) lst1 (g b)) :
    LS pers R (f >>= k) lst (x >>= g) := by
  subst hx
  intro o st' hm
  obtain ⟨⟨r, st1, mm⟩, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have h1 := hf.apply hf1
  cases r with
  | Err e =>
    have := he e st1 mm o st' hk1
    subst this
    exact errSim_bind h1
  | Ok a =>
    obtain ⟨b, lst1, hx1, hR, hrel, hinv⟩ := h1
    rw [run_bind_ok hx1]
    exact hk a mm b st1 lst1 hR hrel hinv o st' hk1

/-- A memoised reader walk as a callee, reading at the current state `st`. -/
theorem LS.bindRM {α γ β δ M : Type} {pers : arena.store.PersTier}
    {R₁ : α × M → β → Prop} {R : γ → δ → Prop}
    {f : Result (core.result.Result α kernel.core_types.CheckError × M)}
    {st : arena.monad.AState}
    {k : core.result.Result α kernel.core_types.CheckError × M →
      Result (core.result.Result γ kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x' x : AM β} {g : β → AM δ}
    (hf : LSRM pers R₁ f st lst x') (hx : x' = x)
    (he : ∀ e mm, ErrArm (k (.Err e, mm)) e)
    (hk : ∀ a mm b lst1, R₁ (a, mm) b → AStateRel₀ pers st lst1 → AStateInv pers st →
      LS pers R (k (.Ok a, mm)) lst1 (g b)) :
    LS pers R (f >>= k) lst (x >>= g) := by
  subst hx
  intro o st' hm
  obtain ⟨⟨r, mm⟩, hf1, hk1⟩ := ConRon.Refine.bind_eq_ok_iff.mp hm
  have h1 := hf.apply hf1
  cases r with
  | Err e =>
    have := he e mm o st' hk1
    subst this
    exact errSim_bind h1
  | Ok a =>
    obtain ⟨b, lst1, hx1, hR, hrel, hinv⟩ := h1
    rw [run_bind_ok hx1]
    exact hk a mm b lst1 hR hrel hinv o st' hk1

/-- A memoised state walk in tail position of a packed walk. -/
theorem LS.tailM {α β M : Type} {pers : arena.store.PersTier} {R₁ R : α × M → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState × M)}
    {lst : AState} {x' x : AM β}
    (hf : LSM pers R₁ m lst x') (hx : x' = x) (hR : ∀ p b, R₁ p b → R p b) :
    LS pers R (packM m) lst x :=
  LS.tail hf hx hR

/-- A memoised reader walk in tail position of a packed reader walk. -/
theorem LS.tailRM {α β M : Type} {pers : arena.store.PersTier} {R₁ R : α × M → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × M)}
    {st : arena.monad.AState} {lst : AState} {x' x : AM β}
    (hf : LSRM pers R₁ m st lst x') (hx : x' = x) (hR : ∀ p b, R₁ p b → R p b) :
    LS pers R (packRM st m) lst x :=
  LS.tail hf hx hR

/-! ## Rust-side normalisation of an inlined fragment -/

theorem LS.rust_assoc {γ δ α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {b : Result γ} {g : γ → Result δ}
    {k : δ → Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β}
    (h : LS pers R (b >>= fun y => g y >>= k) lst x) :
    LS pers R ((b >>= g) >>= k) lst x := by
  rw [Aeneas.Std.bind_assoc_eq]; exact h

theorem LS.rust_ite_bind {γ α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {c : Prop} [Decidable c] {a b : Result γ}
    {k : γ → Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : AM β}
    (h₁ : c → LS pers R (a >>= k) lst x) (h₂ : ¬ c → LS pers R (b >>= k) lst x) :
    LS pers R ((if c then a else b) >>= k) lst x := by
  by_cases hc : c
  · rw [if_pos hc]; exact h₁ hc
  · rw [if_neg hc]; exact h₂ hc

theorem LSP.rust_assoc {γ δ α : Type} {b : Result γ} {g : γ → Result δ}
    {k : δ → Result α} {Q : α → Prop}
    (h : LSP (b >>= fun y => g y >>= k) Q) : LSP ((b >>= g) >>= k) Q := by
  rw [Aeneas.Std.bind_assoc_eq]; exact h

theorem LSP.rust_ite_bind {γ α : Type} {c : Prop} [Decidable c] {a b : Result γ}
    {k : γ → Result α} {Q : α → Prop}
    (h₁ : c → LSP (a >>= k) Q) (h₂ : ¬ c → LSP (b >>= k) Q) :
    LSP ((if c then a else b) >>= k) Q := by
  by_cases hc : c
  · rw [if_pos hc]; exact h₁ hc
  · rw [if_neg hc]; exact h₂ hc

/-! ## Twin-side moves -/

/-- A twin fact a Rust-only step established about a twin expression: the
twin side is rewritten left to right with it. -/
def TwinEq {α : Type} (a b : α) : Prop := a = b

theorem LS.twin_dite_pos {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {c : Prop} [Decidable c]
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : c → AM β} {y : ¬ c → AM β} (hc : c) (h : LS pers R m lst (x hc)) :
    LS pers R m lst (if h : c then x h else y h) := by
  rw [dif_pos hc]; exact h

theorem LS.twin_dite_neg {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {c : Prop} [Decidable c]
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : c → AM β} {y : ¬ c → AM β} (hc : ¬ c) (h : LS pers R m lst (y hc)) :
    LS pers R m lst (if h : c then x h else y h) := by
  rw [dif_neg hc]; exact h

/-! ### A twin `if` against a Rust bind (task #97-T2-TACTIC round 2)

The Rust takes a bind step while the twin still tests an `if`.  An `if` in
bind position (`(if c then a else b) >>= k`, e.g. the `… >>= pure` of a twin
`do` block's last line) is distributed over its continuation, so the twin
side is an `if` again and is decided like any other (`twin_ite_pos`/`neg`).
An `if` the context does not decide, where no step moves, is split: both
branches continue the zip, and the one a later Rust test rules out closes by
`lockstep_contra`.  Neither rule produces a bind with `pure`, so they cannot
cycle with `twin_bind_pure` (which is atomic in `rustStep`). -/

theorem LS.twin_ite_bind {α β γ : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {c : Prop} [Decidable c]
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {a b : AM γ} {k : γ → AM β}
    (h : LS pers R m lst (if c then a >>= k else b >>= k)) :
    LS pers R m lst ((if c then a else b) >>= k) := by
  by_cases hc : c
  · rw [if_pos hc] at h ⊢; exact h
  · rw [if_neg hc] at h ⊢; exact h

theorem LS.twin_dite_bind {α β γ : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {c : Prop} [Decidable c]
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {a : c → AM γ} {b : ¬ c → AM γ} {k : γ → AM β}
    (h : LS pers R m lst (if hc : c then a hc >>= k else b hc >>= k)) :
    LS pers R m lst ((if hc : c then a hc else b hc) >>= k) := by
  by_cases hc : c
  · rw [dif_pos hc] at h ⊢; exact h
  · rw [dif_neg hc] at h ⊢; exact h

theorem LS.twin_ite_split {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {c : Prop} [Decidable c]
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x y : AM β}
    (h₁ : c → LS pers R m lst x) (h₂ : ¬ c → LS pers R m lst y) :
    LS pers R m lst (if c then x else y) := by
  by_cases hc : c
  · rw [if_pos hc]; exact h₁ hc
  · rw [if_neg hc]; exact h₂ hc

theorem LS.twin_dite_split {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {c : Prop} [Decidable c]
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {x : c → AM β} {y : ¬ c → AM β}
    (h₁ : ∀ hc : c, LS pers R m lst (x hc)) (h₂ : ∀ hc : ¬ c, LS pers R m lst (y hc)) :
    LS pers R m lst (if hc : c then x hc else y hc) := by
  by_cases hc : c
  · rw [dif_pos hc]; exact h₁ hc
  · rw [dif_neg hc]; exact h₂ hc

/-! ### The tag-guarded projections -/

theorem tagView_const (st : EStore) (i : EIdx) (hi : i.tag = ETag.const) :
    st.view i = (st.viewConst i).map (fun p => ENodeView.const p.1 p.2) := by
  have key : ∀ t : ETables,
      t.get i = (t.getConst i).map (fun p => ENodeView.const p.1 p.2) := by
    intro t
    simp only [ETables.get, ETables.getConst, hi, Option.map_map]
    simp (config := {decide := true}) only [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app,
      ETag.isBind, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, if_false, if_true]
    rfl
  rw [EStore.view, EStore.viewConst,
    if_neg (by rw [ETag.isBind, hi]; simp [ETag.lam, ETag.forallE, ETag.const])]
  by_cases hp : i.isPersistent
  · rw [if_pos hp, if_pos hp, EStore.persGetConst]; exact key _
  · rw [if_neg hp, if_neg hp]
    by_cases hs : st.scratchOn
    · rw [if_pos hs, if_pos hs]; exact key _
    · rw [if_neg hs, if_neg hs]; rfl

theorem tagView_sort (st : EStore) (i : EIdx) (hi : i.tag = ETag.sort) :
    st.view i = (st.viewSort i).map ENodeView.sort := by
  have key : ∀ t : ETables, t.get i = (t.getSort i).map ENodeView.sort := by
    intro t
    simp only [ETables.get, ETables.getSort, hi, Option.map_map]
    simp (config := {decide := true}) only [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app,
      ETag.isBind, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, if_false, if_true]
    rfl
  rw [EStore.view, EStore.viewSort,
    if_neg (by rw [ETag.isBind, hi]; simp [ETag.lam, ETag.forallE, ETag.sort])]
  by_cases hp : i.isPersistent
  · rw [if_pos hp, if_pos hp, EStore.persGetSort]; exact key _
  · rw [if_neg hp, if_neg hp]
    by_cases hs : st.scratchOn
    · rw [if_pos hs, if_pos hs]; exact key _
    · rw [if_neg hs, if_neg hs]; rfl



theorem view_run_of (h : EIdx) (lst : AState) :
    (Arena.view h).run lst = (match lst.store.view h with
      | some v => Except.ok (v, lst)
      | none => Except.error (Arena.CheckError.internal "arena: dangling expression handle")) := by
  show ((match lst.store.view h with
          | some v => (pure v : AM ENodeView)
          | none => Arena.fail (.internal "arena: dangling expression handle")).run lst) = _
  cases lst.store.view h <;> rfl

/-- The twin's `match o with | none => failDanglingE | some p => k p`, named
once so that every rewrite produces the same term. -/
def danglingOr {γ δ : Type} (k : γ → AM δ) : Option γ → AM δ
  | none => failDanglingE
  | some p => k p

@[lockstep_simp] theorem danglingOr_none {γ δ : Type} (k : γ → AM δ) :
    danglingOr k none = failDanglingE := rfl
@[lockstep_simp] theorem danglingOr_some {γ δ : Type} (k : γ → AM δ) (p : γ) :
    danglingOr k (some p) = k p := rfl

/-- Under a tag, the view is a projection: the generic form. -/
theorem view_bind_of_proj {γ δ : Type} (h : EIdx) (Q : AM (Option γ)) (P : EStore → Option γ)
    (hQ : ∀ lst : AState, Q.run lst = .ok (P lst.store, lst))
    (C : γ → ENodeView) (hv : ∀ st : EStore, st.view h = (P st).map C)
    (g : ENodeView → AM δ) :
    (Arena.view h >>= g) = (Q >>= danglingOr fun p => g (C p)) := by
  funext lst
  show (Arena.view h >>= g).run lst = (Q >>= _).run lst
  rw [StateT.run_bind, StateT.run_bind, view_run_of, hv, hQ]
  cases P lst.store <;> rfl

@[lockstep_twin] theorem LS.twin_view_const {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {h : EIdx} {g : ENodeView → AM β} (ht : h.tag = ETag.const)
    (hls : LS pers R m lst (viewConst h >>= danglingOr fun p => g (.const p.1 p.2))) :
    LS pers R m lst (Arena.view h >>= g) := by
  rw [view_bind_of_proj h (viewConst h) (fun s => s.viewConst h) (fun _ => rfl)
    (fun p => .const p.1 p.2) (fun st => tagView_const st h ht)]
  exact hls

@[lockstep_twin] theorem LS.twin_view_sort {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {h : EIdx} {g : ENodeView → AM β} (ht : h.tag = ETag.sort)
    (hls : LS pers R m lst (viewSort h >>= danglingOr fun p => g (.sort p))) :
    LS pers R m lst (Arena.view h >>= g) := by
  rw [view_bind_of_proj h (viewSort h) (fun s => s.viewSort h) (fun _ => rfl)
    ENodeView.sort (fun st => tagView_sort st h ht)]
  exact hls

theorem EStore_viewConstName_eq (st : EStore) (i : EIdx) :
    st.viewConstName i = (st.viewConst i).map Prod.fst := by
  rw [EStore.viewConstName, EStore.viewConst]
  by_cases hp : i.isPersistent
  · rw [if_pos hp, if_pos hp, EStore.persGetConstName, EStore.persGetConst,
      ETables.getConstName, ETables.getConst, Option.map_map]; rfl
  · rw [if_neg hp, if_neg hp]
    by_cases hs : st.scratchOn
    · rw [if_pos hs, if_pos hs, ETables.getConstName, ETables.getConst, Option.map_map]; rfl
    · rw [if_neg hs, if_neg hs]; rfl

/-- The port reads the NAME of a `const`-tagged handle, the twin its whole
view, and uses only the name. -/
@[lockstep_twin] theorem LS.twin_view_const_name {α β : Type} {pers : arena.store.PersTier}
    {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {h : EIdx} {g : ENodeView → AM β} (ht : h.tag = ETag.const)
    (hg : ∀ c us, g (.const c us) = g (.const c ⟨0⟩))
    (hls : LS pers R m lst (viewConstName h >>= danglingOr fun c => g (.const c ⟨0⟩))) :
    LS pers R m lst (Arena.view h >>= g) := by
  have key : (Arena.view h >>= g) = (viewConstName h >>= danglingOr fun c => g (.const c ⟨0⟩)) := by
    funext lst
    show (Arena.view h >>= g).run lst = (viewConstName h >>= _).run lst
    rw [StateT.run_bind, StateT.run_bind, view_run_of, tagView_const _ h ht]
    show _ = ((danglingOr (fun c => g (.const c ⟨0⟩)) (lst.store.viewConstName h)).run lst)
    rw [EStore_viewConstName_eq]
    cases lst.store.viewConst h with
    | none => rfl
    | some p =>
      show (g (.const p.1 p.2)).run lst = (g (.const p.1 ⟨0⟩)).run lst
      rw [hg]
  rw [key]; exact hls

theorem tagView_app (st : EStore) (i : EIdx) (hi : i.tag = ETag.app) :
    st.view i = (st.viewApp i).map (fun p => ENodeView.app p.1 p.2) := by
  have key : ∀ t : ETables, t.get i = (t.getApp i).map (fun p => ENodeView.app p.1 p.2) := by
    intro t
    simp only [ETables.get, ETables.getApp, hi, Option.map_map]
    simp (config := {decide := true}) only [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app,
      ETag.isBind, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, if_false, if_true]
    rfl
  rw [EStore.view, EStore.viewApp,
    if_neg (by rw [ETag.isBind, hi]; simp [ETag.lam, ETag.forallE, ETag.app])]
  by_cases hp : i.isPersistent
  · rw [if_pos hp, if_pos hp, EStore.persGetApp]; exact key _
  · rw [if_neg hp, if_neg hp]
    by_cases hs : st.scratchOn
    · rw [if_pos hs, if_pos hs]; exact key _
    · rw [if_neg hs, if_neg hs]; rfl

theorem tagView_lit (st : EStore) (i : EIdx) (hi : i.tag = ETag.lit) :
    st.view i = (st.viewLit i).map ENodeView.lit := by
  have key : ∀ t : ETables, t.get i = (t.getLit i).map ENodeView.lit := by
    intro t
    simp only [ETables.get, ETables.getLit, hi, Option.map_map]
    simp (config := {decide := true}) only [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app,
      ETag.isBind, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, if_false, if_true]
    rfl
  rw [EStore.view, EStore.viewLit,
    if_neg (by rw [ETag.isBind, hi]; simp [ETag.lam, ETag.forallE, ETag.lit])]
  by_cases hp : i.isPersistent
  · rw [if_pos hp, if_pos hp, EStore.persGetLit]; exact key _
  · rw [if_neg hp, if_neg hp]
    by_cases hs : st.scratchOn
    · rw [if_pos hs, if_pos hs]; exact key _
    · rw [if_neg hs, if_neg hs]; rfl

theorem tagView_letE (st : EStore) (i : EIdx) (hi : i.tag = ETag.letE) :
    st.view i = (st.viewLet i).map (fun p => ENodeView.letE p.1 p.2.1 p.2.2) := by
  have key : ∀ t : ETables, t.get i = (t.getLet i).map (fun p => ENodeView.letE p.1 p.2.1 p.2.2) := by
    intro t
    simp only [ETables.get, ETables.getLet, hi, Option.map_map]
    simp (config := {decide := true}) only [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app,
      ETag.isBind, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, if_false, if_true]
    rfl
  rw [EStore.view, EStore.viewLet,
    if_neg (by rw [ETag.isBind, hi]; simp [ETag.lam, ETag.forallE, ETag.letE])]
  by_cases hp : i.isPersistent
  · rw [if_pos hp, if_pos hp, EStore.persGetLet]; exact key _
  · rw [if_neg hp, if_neg hp]
    by_cases hs : st.scratchOn
    · rw [if_pos hs, if_pos hs]; exact key _
    · rw [if_neg hs, if_neg hs]; rfl

theorem tagView_proj (st : EStore) (i : EIdx) (hi : i.tag = ETag.proj) :
    st.view i = (st.viewProj i).map (fun p => ENodeView.proj p.1 p.2.1 p.2.2) := by
  have key : ∀ t : ETables, t.get i = (t.getProj i).map (fun p => ENodeView.proj p.1 p.2.1 p.2.2) := by
    intro t
    simp only [ETables.get, ETables.getProj, hi, Option.map_map]
    simp (config := {decide := true}) only [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app,
      ETag.isBind, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, if_false, if_true]
    rfl
  rw [EStore.view, EStore.viewProj,
    if_neg (by rw [ETag.isBind, hi]; simp [ETag.lam, ETag.forallE, ETag.proj])]
  by_cases hp : i.isPersistent
  · rw [if_pos hp, if_pos hp, EStore.persGetProj]; exact key _
  · rw [if_neg hp, if_neg hp]
    by_cases hs : st.scratchOn
    · rw [if_pos hs, if_pos hs]; exact key _
    · rw [if_neg hs, if_neg hs]; rfl

theorem tagView_bvar (st : EStore) (i : EIdx) (hi : i.tag = ETag.bvar) :
    st.view i = (st.viewBVar i).map ENodeView.bvar := by
  have key : ∀ t : ETables, t.get i = (t.getBVar i).map ENodeView.bvar := by
    intro t
    simp only [ETables.get, ETables.getBVar, hi, Option.map_map]
    simp (config := {decide := true}) only [ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app,
      ETag.isBind, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj, if_false, if_true]
    rfl
  rw [EStore.view, EStore.viewBVar,
    if_neg (by rw [ETag.isBind, hi]; simp [ETag.lam, ETag.forallE, ETag.bvar])]
  by_cases hp : i.isPersistent
  · rw [if_pos hp, if_pos hp, EStore.persGetBVar]; exact key _
  · rw [if_neg hp, if_neg hp]
    by_cases hs : st.scratchOn
    · rw [if_pos hs, if_pos hs]; exact key _
    · rw [if_neg hs, if_neg hs]; rfl

theorem tagView_lam (st : EStore) (i : EIdx) (hi : i.tag = ETag.lam) :
    st.view i = (st.viewBind i).map (fun p => ENodeView.lam p.1 p.2.1 p.2.2) := by
  rw [EStore.view, if_pos (by rw [hi]; rfl)]
  cases st.viewBind i with
  | none => rfl
  | some p => obtain ⟨ty, b, m⟩ := p; simp [eBindView, hi]

theorem tagView_forallE (st : EStore) (i : EIdx) (hi : i.tag = ETag.forallE) :
    st.view i = (st.viewBind i).map (fun p => ENodeView.forallE p.1 p.2.1 p.2.2) := by
  rw [EStore.view, if_pos (by rw [hi]; rfl)]
  cases st.viewBind i with
  | none => rfl
  | some p =>
    obtain ⟨ty, b, m⟩ := p
    simp [eBindView, hi, ETag.forallE, ETag.lam]

@[lockstep_twin] theorem LS.twin_view_app {α β : Type} {pers : arena.store.PersTier}
    {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {h : EIdx} {g : ENodeView → AM β} (ht : h.tag = ETag.app)
    (hls : LS pers R m lst (viewApp h >>= danglingOr fun p => g ((fun p => ENodeView.app p.1 p.2) p))) :
    LS pers R m lst (Arena.view h >>= g) := by
  rw [view_bind_of_proj h (viewApp h) (fun s => s.viewApp h) (fun _ => rfl)
    (fun p => (fun p => ENodeView.app p.1 p.2) p) (fun st => tagView_app st h ht)]
  exact hls

@[lockstep_twin] theorem LS.twin_view_lit {α β : Type} {pers : arena.store.PersTier}
    {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {h : EIdx} {g : ENodeView → AM β} (ht : h.tag = ETag.lit)
    (hls : LS pers R m lst (viewLit h >>= danglingOr fun p => g (ENodeView.lit p))) :
    LS pers R m lst (Arena.view h >>= g) := by
  rw [view_bind_of_proj h (viewLit h) (fun s => s.viewLit h) (fun _ => rfl)
    (fun p => ENodeView.lit p) (fun st => tagView_lit st h ht)]
  exact hls

@[lockstep_twin] theorem LS.twin_view_letE {α β : Type} {pers : arena.store.PersTier}
    {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {h : EIdx} {g : ENodeView → AM β} (ht : h.tag = ETag.letE)
    (hls : LS pers R m lst (viewLet h >>= danglingOr fun p => g ((fun p => ENodeView.letE p.1 p.2.1 p.2.2) p))) :
    LS pers R m lst (Arena.view h >>= g) := by
  rw [view_bind_of_proj h (viewLet h) (fun s => s.viewLet h) (fun _ => rfl)
    (fun p => (fun p => ENodeView.letE p.1 p.2.1 p.2.2) p) (fun st => tagView_letE st h ht)]
  exact hls

@[lockstep_twin] theorem LS.twin_view_proj {α β : Type} {pers : arena.store.PersTier}
    {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {h : EIdx} {g : ENodeView → AM β} (ht : h.tag = ETag.proj)
    (hls : LS pers R m lst (viewProj h >>= danglingOr fun p => g ((fun p => ENodeView.proj p.1 p.2.1 p.2.2) p))) :
    LS pers R m lst (Arena.view h >>= g) := by
  rw [view_bind_of_proj h (viewProj h) (fun s => s.viewProj h) (fun _ => rfl)
    (fun p => (fun p => ENodeView.proj p.1 p.2.1 p.2.2) p) (fun st => tagView_proj st h ht)]
  exact hls

@[lockstep_twin] theorem LS.twin_view_bvar {α β : Type} {pers : arena.store.PersTier}
    {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {h : EIdx} {g : ENodeView → AM β} (ht : h.tag = ETag.bvar)
    (hls : LS pers R m lst (viewBVar h >>= danglingOr fun p => g (ENodeView.bvar p))) :
    LS pers R m lst (Arena.view h >>= g) := by
  rw [view_bind_of_proj h (viewBVar h) (fun s => s.viewBVar h) (fun _ => rfl)
    (fun p => ENodeView.bvar p) (fun st => tagView_bvar st h ht)]
  exact hls

@[lockstep_twin] theorem LS.twin_view_lam {α β : Type} {pers : arena.store.PersTier}
    {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {h : EIdx} {g : ENodeView → AM β} (ht : h.tag = ETag.lam)
    (hls : LS pers R m lst (viewBind h >>= danglingOr fun p => g ((fun p => ENodeView.lam p.1 p.2.1 p.2.2) p))) :
    LS pers R m lst (Arena.view h >>= g) := by
  rw [view_bind_of_proj h (viewBind h) (fun s => s.viewBind h) (fun _ => rfl)
    (fun p => (fun p => ENodeView.lam p.1 p.2.1 p.2.2) p) (fun st => tagView_lam st h ht)]
  exact hls

@[lockstep_twin] theorem LS.twin_view_forallE {α β : Type} {pers : arena.store.PersTier}
    {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {h : EIdx} {g : ENodeView → AM β} (ht : h.tag = ETag.forallE)
    (hls : LS pers R m lst (viewBind h >>= danglingOr fun p => g ((fun p => ENodeView.forallE p.1 p.2.1 p.2.2) p))) :
    LS pers R m lst (Arena.view h >>= g) := by
  rw [view_bind_of_proj h (viewBind h) (fun s => s.viewBind h) (fun _ => rfl)
    (fun p => (fun p => ENodeView.forallE p.1 p.2.1 p.2.2) p) (fun st => tagView_forallE st h ht)]
  exact hls

/-! ## The tactic -/

attribute [lockstep_simp] Aeneas.Std.uncurry_apply_pair not_false_eq_true not_true_eq_false
  Bool.false_eq_true Bool.true_eq_false eq_self_iff_true and_true true_and ne_eq


open Lean Meta Elab Tactic

/-- **Twin-side splits** (task #97-T2-TACTIC round 2, the Frontend lane): when
nothing decides a twin test (an `if`, a `match` on a term) and no step moves,
`lockstep` splits it only if the context rules out a branch
(`lockstep_contra` closes it); otherwise it STOPS there and hands the goal
back.  `set_option lockstep.twinSplit true` lets it split anyway and walk
every branch. -/
register_option lockstep.twinSplit : Bool := {
  defValue := false
  descr := "lockstep: split a twin test nothing decides even when no branch is ruled out"
}

/-- Is `t` a callee SPEC: a `∀`/`→` statement whose conclusion is a lockstep
judgement or a `Sim…` statement (an induction hypothesis, a knot slot)? -/
def isSpecHyp (t : Expr) : MetaM Bool := do
  let t := t.consumeMData
  unless t.isForall do return false
  forallTelescope t fun _ c => do
    let c := c.consumeMData
    if (judgementRustArg? c).isSome then return true
    match c.getAppFn.constName? with
    | some n => return (match n with
        | .str _ s => s.startsWith "Sim"
        | _ => false)
    | none => return false

/-- The context of a simp-based side tier: every callee SPEC hypothesis (an
induction hypothesis, a knot slot: a `∀`/`→` whose conclusion is a judgement,
`isSpecHyp`) cleared, because `simp [*]`/`simp_all` would use it as a
conditional rewrite rule and that search need not terminate (task
#97-T2-TACTIC round 2, the Frontend lane's `proj_rec_candidates_from`).  A `∀`
FACT (`∀ j, some v = some j → j < n`) stays: the side tiers need those.  The
goal itself is unchanged; a hypothesis something depends on stays. -/
def clearForallHyps : TacticM Unit := do
  let g ← getMainGoal
  let g ← g.withContext do
    let mut g := g
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      unless ← isSpecHyp t do continue
      g ← g.tryClear d.fvarId
    return g
  replaceMainGoal [g]

elab "lockstep_clear_foralls" : tactic => clearForallHyps

/-- Per-alternative timing of the side tactics (`lockstep_stats` prints it). -/
initialize statsRef : IO.Ref (Std.HashMap String (Nat × Nat × Nat × Nat)) ← IO.mkRef {}

initialize failRef : IO.Ref (Array Format) ← IO.mkRef #[]

def record (k : String) (ok : Bool) (ms : Nat) : IO Unit :=
  statsRef.modify fun m =>
    let (a, b, c, d) := m.getD k (0, 0, 0, 0)
    m.insert k (if ok then (a + 1, b + ms, c, d) else (a, b, c + 1, d + ms))

/-- Try the alternatives in order, timing each. -/
def firstTimed (label : String) (alts : List (TSyntax `tactic)) : TacticM Unit := do
  let s ← saveState
  let mut i := 0
  for t in alts do
    let t0 ← IO.monoMsNow
    try
      evalTactic t
      unless (← getUnsolvedGoals).isEmpty do throwError "left goals"
      record s!"{label}.{i}" true ((← IO.monoMsNow) - t0)
      return
    catch _ =>
      record s!"{label}.{i}" false ((← IO.monoMsNow) - t0)
      s.restore
    i := i + 1
  let fs ← failRef.get
  if fs.size < 40 then
    failRef.set (fs.push (f!"{label}: " ++ (← Meta.ppExpr (← instantiateMVars (← getMainTarget)))))
  throwError "{label}: no alternative closes the goal"

/-- **A tier the lanes extend** (task #97-T2-LOCKSTEP lane Checker): a side
goal that needs a lane's own relation facts (the checker tier's `IFEnvRel`
counters) — each lane adds one `macro_rules` alternative; the default fails,
so it costs nothing where no lane has one. -/
syntax "lockstep_side_ext" : tactic
macro_rules | `(tactic| lockstep_side_ext) => `(tactic| fail "lockstep_side_ext: no lane extension")

def sideCheap : TacticM (List (TSyntax `tactic)) := do return [
    ← `(tactic| assumption),
    ← `(tactic| rfl),
    ← `(tactic| (simp only [lockstep_simp]; done)),
    ← `(tactic| (apply Eq.symm; assumption)),
    ← `(tactic| (simp only [lockstep_simp, *]; done)),
    ← `(tactic| (simp (config := { decide := true }) only [lockstep_simp, *]; done)),
    -- an existential answer relation (a walk-local memo): its witness is the
    -- twin's memo, whose relation is in the context
    ← `(tactic| (refine ⟨_, ?_, rfl⟩; assumption)),
    -- two different tag constants (the twin tests its tags in another order)
    ← `(tactic| (simp (config := { decide := true }) only [lockstep_simp, *,
        arena.handle.ETAG_PROJ, arena.handle.ETAG_LIT,
        arena.handle.ETAG_LET_E, arena.handle.ETAG_FORALL_E, arena.handle.ETAG_LAM,
        arena.handle.ETAG_APP, arena.handle.ETAG_CONST, arena.handle.ETAG_SORT,
        arena.handle.ETAG_FVAR, arena.handle.ETAG_BVAR]; done))]

def sideDear : TacticM (List (TSyntax `tactic)) := do return [
    ← `(tactic| scalar_tac),
    ← `(tactic| (simp_all only [lockstep_simp]; done)),
    ← `(tactic| (simp_all (config := { decide := true }) only [lockstep_simp]; done)),
    ← `(tactic| (simp_all only [lockstep_simp, Bool.and_eq_true]; scalar_tac)),
    ← `(tactic| (simp_all; done)),
    ← `(tactic| lockstep_side_ext)]

/-- Side goals: the relation and the invariant at the current state, an
argument correspondence, a branch condition.  Cheap alternatives first. -/
elab "lockstep_side" : tactic => do
  -- closed by a hypothesis as it stands (a `∀` premise by the matching
  -- hypothesis): with the whole context
  let s ← saveState
  try
    evalTactic (← `(tactic| first | assumption | rfl | (apply Eq.symm; assumption)))
    if (← getUnsolvedGoals).isEmpty then return
    s.restore
  catch _ => s.restore
  -- every other tier without the `∀`/`→` hypotheses
  clearForallHyps
  -- an arithmetic correspondence (`absU i1 = m`) goes to `scalar_tac` early
  let ty ← whnfR (← instantiateMVars (← getMainTarget))
  let arith := (ty.isAppOfArity ``Eq 3 && (ty.getArg! 0).isConstOf ``Nat) ||
    ty.isAppOfArity ``LT.lt 4 || ty.isAppOfArity ``LE.le 4
  if arith then
    firstTimed "sideA" [← `(tactic| assumption), ← `(tactic| rfl),
      ← `(tactic| (simp only [lockstep_simp]; done)),
      ← `(tactic| (simp only [lockstep_simp] at *; omega)), ← `(tactic| scalar_tac),
      ← `(tactic| (simp_all only [lockstep_simp]; done)), ← `(tactic| (simp_all; done)),
      ← `(tactic| lockstep_side_ext)]
  else
    try firstTimed "side" ((← sideCheap) ++ (← sideDear))
    catch e =>
      -- two reads of one vector at indices the context proves equal (a cursor
      -- the Rust computes in machine words, the twin in `Nat`): tried only on
      -- an equation that mentions a vector read
      let isIdx := ty.isAppOfArity ``Eq 3 &&
        ((ty.find? fun t => t.isAppOf ``GetElem.getElem || t.isAppOf `ConRon.Arena.lastEidx).isSome)
      unless isIdx do throw e
      firstTimed "sideX" [← `(tactic| (congr <;> scalar_tac)),
        ← `(tactic| (simp only [lockstep_simp, *]; congr <;> scalar_tac))]

elab "lockstep_side_cheap" : tactic => do
  clearForallHyps
  firstTimed "side" (← sideCheap)

elab "lockstep_side_dear" : tactic => do
  clearForallHyps
  firstTimed "sideD" (← sideDear)

/-- A twin test the cheap tier could not decide: arithmetic, then the context. -/
elab "lockstep_side_ite" : tactic => do
  clearForallHyps
  firstTimed "sideI" [← `(tactic| scalar_tac), ← `(tactic| (simp_all only [lockstep_simp]; done)),
    ← `(tactic| lockstep_side_ext)]

elab "lockstep_stats" : tactic => do
  let m ← statsRef.get
  let rows := m.toList.toArray.qsort (fun a b => a.1 < b.1)
  let mut msg := m!"lockstep side-tactic statistics (label: ok n / ms, fail n / ms)"
  for (k, (a, b, c, d)) in rows do
    msg := msg ++ m!"\n{k}: ok {a} / {b} ms, fail {c} / {d} ms"
  for f in (← failRef.get) do
    msg := msg ++ m!"\nFAILED {f}"
  logInfo msg
  statsRef.set {}
  failRef.set #[]

/-- A branch the context rules out. -/
syntax "lockstep_contra" : tactic
elab_rules : tactic
  | `(tactic| lockstep_contra) => do
    clearForallHyps
    firstTimed "contra" [← `(tactic| (exfalso; scalar_tac)), ← `(tactic| (exfalso; simp_all))]

/-- The twin-action correspondence `x' = x` a bind rule leaves. -/
elab "lockstep_congr" : tactic => do
  firstTimed "congr" [← `(tactic| rfl), ← `(tactic| (congr 1 <;> lockstep_side)),
    ← `(tactic| (simp only [lockstep_simp] at *; done))]

/-- The twin's error leaf. -/
syntax "lockstep_errsim" : tactic
macro_rules
  | `(tactic| lockstep_errsim) => `(tactic| first
      | exact AErrSim.native _
      | (refine AErrSim.mk rfl ?_; rfl)
      | exact errSim_fail rfl
      | exact errSim_throw rfl
      | assumption
      | exact errSim_fail (by assumption)
      | exact errSim_throw (by assumption)
      | (simp only [lockstep_simp] at *; first | exact errSim_fail rfl | exact errSim_throw rfl))

/-- The error arm of a Rust bind: the continuation fed an `Err` gives it back,
possibly through an `ok (…) >>= k'` repack (`bind_tc_ok`). -/
syntax "lockstep_errarm" : tactic
macro_rules
  | `(tactic| lockstep_errarm) => `(tactic| first
      | exact errArm_ok
      | (show ErrArm (ok _ >>= _) _; rw [bind_tc_ok]; exact errArm_ok)
      | (apply errArm_of_eq; simp only [bind_tc_ok, Aeneas.Std.uncurry_apply_pair])
      | (intro o st2 h; simp only [Aeneas.Std.uncurry_apply_pair, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at h; all_goals first | exact h.1.symm | exact h.symm)
      | (refine errArm_bind fun _ => ?_; exact errArm_ok))

/-- Apply `rule` to `g` and return its new goals by binder name. -/
def applyRule (g : MVarId) (rule : Name) : MetaM (Array (Name × MVarId)) := do
  let c ← mkConstWithFreshMVarLevels rule
  let cty ← inferType c
  let (mvs, _, concl) ← forallMetaTelescope cty
  unless ← isDefEq concl (← g.getType) do
    throwError "lockstep: {rule} does not apply"
  g.assign (mkAppN c mvs)
  let names ← forallTelescope cty fun xs _ => xs.mapM fun x => x.fvarId!.getUserName
  return names.zip (mvs.map (·.mvarId!))

def pick (gs : Array (Name × MVarId)) (n : Name) : MetaM MVarId := do
  match gs.find? (·.1 == n) with
  | some (_, g) => return g
  | none => throwError "lockstep: no premise {n}"

/-- Run `tac` on `g` and return what it leaves. -/
def runOn (g : MVarId) (tac : TacticM Unit) : TacticM (List MVarId) := do
  setGoals [g]
  tac
  let gs ← getGoals
  gs.filterM fun g => return !(← g.isAssigned)

def runClosed (g : MVarId) (tac : TacticM Unit) : TacticM Unit := do
  let rest ← runOn g tac
  unless rest.isEmpty do
    throwError "lockstep: side goal left open:{indentD (MessageData.joinSep (rest.map MessageData.ofGoal) "\n")}"

def evalT (stx : TacticM (TSyntax `tactic)) : TacticM Unit := do evalTactic (← stx)

/-- Close a spec goal (a judgement about one Rust callee) with a `@[lockstep]`
lemma or a local hypothesis filed under the same head. -/
def specCore (g : MVarId) (after : TacticM Unit := pure ()) : TacticM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some m := judgementRustArg? ty
    | throwError "lockstep_spec: not a judgement{indentExpr ty}"
  let some k := rustKey? m.headBeta
    | throwError "lockstep_spec: no head constant{indentExpr m}"
  let mut cands : Array Expr := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let ok ← forallTelescope t fun _ c => pure <|
      c.getAppFn.constName? == ty.getAppFn.constName? &&
      match judgementRustArg? c with
      | some m' => rustKey? m'.headBeta == some k
      | none => false
    if ok then cands := cands.push d.toExpr
  -- lemmas from an `open`ed namespace first: a file that opens its own set
  -- of pairs (`open …Lockstep.PB`) gets those before any other module's.
  -- Only a region namespace BELOW `Lockstep` counts: `open Lockstep in`, which
  -- every tier writes, must not reorder the shared pairs
  let opens ← getOpenDecls
  let isOpen (n : Name) : Bool := opens.any fun
    | .simple ns _ => ns == n.getPrefix && ns != `ConRon.Refine2.Lockstep &&
        (`ConRon.Refine2.Lockstep).isPrefixOf ns
    | _ => false
  let ls ← lockstepLemmas k
  let ls := ls.filter isOpen ++ ls.filter (!isOpen ·)
  for n in ls do
    let c ← mkConstWithFreshMVarLevels n
    let same ← forallTelescope (← inferType c) fun _ concl =>
      pure (concl.getAppFn.constName? == ty.getAppFn.constName?)
    if same then cands := cands.push c
  if cands.isEmpty then
    throwError "lockstep: no @[lockstep] lemma for `{k}`"
  let s ← saveState
  let mut errs : Array MessageData := #[]
  for c in cands do
    try
      let gs ← g.apply c
      -- **Twin-only arguments** (task #97-T2-TACTIC round 2).  A premise that
      -- is not a proposition is an argument the Rust side did not determine:
      -- the twin's message string (`liftFueled what`, `unresolvedConstsError
      -- what`), the div/mod loop's `tried` list.  It is fixed by unifying the
      -- spec's twin action with the goal's (`after`, the `x' = x` check), not
      -- by the side tactic, whose `assumption` would take any term of its
      -- type.  A propositional premise that fails while it still mentions
      -- such an argument waits for the unification too.
      let dataGoals ← gs.filterM fun sg => return !(← isProp (← sg.getType))
      let pending (sg : MVarId) : MetaM Bool := do
        let t ← instantiateMVars (← sg.getType)
        dataGoals.anyM fun d => do
          if ← d.isAssigned then return false
          return (t.findMVar? (· == d)).isSome
      let mut deferred : Array MVarId := #[]
      for sg in gs do
        if ← sg.isAssigned then continue
        if dataGoals.contains sg then continue
        if ← pending sg then
          let s1 ← saveState
          try runClosed sg (evalT `(tactic| lockstep_side))
          catch _ => s1.restore; deferred := deferred.push sg
        else
          runClosed sg (evalT `(tactic| lockstep_side))
      -- the caller's check on this candidate's twin action (`x' = x`): a
      -- candidate whose twin action is not the goal's gives way to the next
      after
      for sg in deferred ++ dataGoals do
        if ← sg.isAssigned then continue
        runClosed sg (evalT `(tactic| lockstep_side))
      return
    catch e =>
      errs := errs.push m!"{c}: {e.toMessageData}"
      s.restore
  throwError "lockstep: no candidate for `{k}` closes{indentExpr ty}\n{MessageData.joinSep errs.toList "\n"}"

elab "lockstep_spec" : tactic => do
  let g ← getMainGoal
  let others := (← getGoals).tail
  specCore g
  setGoals others

/-- Head-normalise one side of a judgement, by definitional steps only: beta,
`let`, `uncurry` at a pair, and a `match` whose discriminants reduce to
constructors.  This is what `dsimp` would do at the head, without traversing
the (large) rest of the program. -/
partial def headNorm (e : Expr) : MetaM Expr := do
  let e := e.headBeta
  if let .letE _ _ v b _ := e then
    return ← headNorm (b.instantiate1 v)
  if e.isAppOfArity ``Aeneas.Std.uncurry 5 then
    let p ← whnfR e.appArg!
    if p.isAppOfArity ``Prod.mk 4 then
      return ← headNorm (mkApp2 (e.getArg! 3) (p.getArg! 2) (p.getArg! 3))
  if (← matchMatcherApp? e).isSome then
    match ← withTransparency .default (Meta.reduceMatcher? e) with
    | ReduceMatcherResult.reduced e' => return ← headNorm e'
    | _ => return e
  -- a packed memo walk: its Rust program is the argument
  if e.isAppOfArity ``packM 3 || e.isAppOfArity ``packRM 4 then
    let n := e.getAppNumArgs
    return mkAppN e.getAppFn (e.getAppArgs.set! (n - 1) (← headNorm e.appArg!))
  return e

/-- The twin side's `simp only [lockstep_simp]`, on the twin argument alone. -/
def simpTwin (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``LS 7 do return g
  let x := ty.getArg! 6
  let some ext ← getSimpExtension? `lockstep_simp | return g
  let thms ← ext.getTheorems
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simp x ctx
  if r.expr == x then return g
  let ty' := mkAppN ty.getAppFn (ty.getAppArgs.set! 6 r.expr)
  match r.proof? with
  | none => g.replaceTargetDefEq ty'
  | some pf =>
    let motive ← withLocalDeclD `z (← inferType x) fun z =>
      mkLambdaFVars #[z] (mkAppN ty.getAppFn (ty.getAppArgs.set! 6 z))
    let eq ← mkCongrArg motive pf
    g.replaceTargetEq ty' eq

/-- Head-normalise both sides of an `LS` / `LSP` goal. -/
def normGoal (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  if ty.isAppOfArity ``LS 7 then
    let m ← headNorm (ty.getArg! 4)
    let x ← headNorm (ty.getArg! 6)
    let ty' := mkAppN ty.getAppFn ((ty.getAppArgs.set! 4 m).set! 6 x)
    let g ← g.replaceTargetDefEq ty'
    simpTwin g
  else if ty.isAppOfArity ``LSP 3 then
    let m ← headNorm (ty.getArg! 1)
    g.replaceTargetDefEq (mkAppN ty.getAppFn (ty.getAppArgs.set! 1 m))
  else return g

/-- Clear the relation and invariant hypotheses about states the goal no
longer mentions: every side tactic pays for the context it sees. -/
def clearStale (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let mut g := g
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``AStateRel₀ 3 || t.isAppOfArity ``AStateInv 2 then
      let rs := t.getArg! 1
      let ls? := if t.isAppOfArity ``AStateRel₀ 3 then some (t.getArg! 2) else none
      let gone := (rs.isFVar && !ty.containsFVar rs.fvarId!) ||
        (match ls? with | some l => l.isFVar && !ty.containsFVar l.fvarId! | none => false)
      if gone then
        g ← (try g.clear d.fvarId catch _ => pure g)
  return g

/-- **Pair answers and conjunctive relations** (task #97-T2-LOCKSTEP lane
Checker).  A twin answer `b` of a pair type is taken apart (the twin's own
`let (x, y) ← …` then reduces), every relation hypothesis `hR` has its pair
projections reduced, a syntactic conjunction is split, and each equation
component is `subst`ed where it can be.  Only a syntactic `And` is split: a
named relation (`IFEnvRelI`) stays whole, because the specs take it whole. -/
partial def splitRels (g : MVarId) : TacticM MVarId := g.withContext do
  -- a pair-valued twin answer
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if d.userName.eraseMacroScopes == `b then
      let ty ← whnfR (← instantiateMVars d.type)
      if ty.isAppOfArity ``Prod 2 then
        let gs ← g.cases d.fvarId
        if h : gs.size = 1 then return ← splitRels gs[0].mvarId
  -- a relation hypothesis
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if d.userName.eraseMacroScopes == `hR then
      let hi := mkIdent `hR
      let hl := mkIdent `hRl
      let rest ← runOn g (evalT `(tactic| try dsimp only at $hi:ident))
      let [g1] := rest | return g
      let t ← g1.withContext do
        match (← getLCtx).findFromUserName? `hR with
        | some d => instantiateMVars d.type
        | none => pure (mkConst ``True)
      -- a relation constant that unfolds (reducibly) to a conjunction (a
      -- memo walk's `(answer, memo)` relation): unfold it, reduce the pair
      -- projections, and split as below
      let (g1, t) ← g1.withContext do
        if t.isAppOfArity ``And 2 then return (g1, t)
        let t' ← whnfR t
        unless t'.isAppOfArity ``And 2 do return (g1, t)
        let some d := (← getLCtx).findFromUserName? `hR | return (g1, t)
        let g1' ← g1.replaceLocalDeclDefEq d.fvarId t'
        let [g1''] ← runOn g1' (evalT `(tactic| try dsimp only at $hi:ident)) | return (g1', t')
        let t'' ← g1''.withContext do
          match (← getLCtx).findFromUserName? `hR with
          | some d => instantiateMVars d.type
          | none => pure t'
        return (g1'', t'')
      if t.isAppOfArity ``And 2 then
        let rest ← runOn g1 (evalT `(tactic| (obtain ⟨$hl:ident, $hi:ident⟩ := $hi:ident; try subst $hl:ident)))
        let [g2] := rest | return g1
        return ← splitRels g2
      else
        let rest ← runOn g1 (evalT `(tactic| first | subst $hi:ident | skip))
        let [g2] := rest | return g1
        return g2
  return g

/-- Tidy a continuation: `subst` the answer relation, normalise the heads. -/
def tidy (g : MVarId) (hR : Option Name) : TacticM (List MVarId) := do
  let rest ← runOn g do
    if let some h := hR then
      let hi := mkIdent h
      -- a `TwinEq` is a rewrite for the twin side, never a substitution
      let t? ← (← getMainGoal).withContext do
        match (← getLCtx).findFromUserName? h with
        | some d => return some (← instantiateMVars d.type).consumeMData
        | none => return none
      let isTE (e : Expr) := e.isAppOfArity ``TwinEq 3
      match t? with
      | some t =>
        if isTE t then pure ()
        else if t.isAppOfArity ``And 2 && (isTE (t.getArg! 1) || isTE (t.getArg! 0)) then
          evalT `(tactic| obtain ⟨_, _⟩ := $hi:ident)
        else
          evalT `(tactic| first
            | subst $hi:ident
            | (obtain ⟨_, $hi:ident⟩ := $hi:ident; subst $hi:ident)
            -- an existential answer relation (`∃ m', R a.2 m' ∧ b = (a.1, m')`)
            | (obtain ⟨_, _, $hi:ident⟩ := $hi:ident; subst $hi:ident)
            -- an equation between two terms (a memo key's abstraction): rewrite
            -- the Rust side with it, so a probe on it meets the twin's
            | rw [$hi:ident]
            | skip)
      | none => pure ()
  rest.mapM fun g => do clearStale (← normGoal (← splitRels g))

/-- The Rust computation's shape. -/
inductive RKind where
  | state | read | write | value
  /-- a memoised state walk, `(Result α, AState, M)` -/
  | memo
  /-- a memoised reader walk, `(Result α, M)` -/
  | rmemo

def classify (T : Expr) : MetaM RKind := do
  let T ← whnfR T
  if T.isAppOfArity ``Prod 2 && (T.getArg! 0).isAppOfArity ``core.result.Result 2 then
    let rest ← whnfR (T.getArg! 1)
    if rest.isAppOfArity ``Prod 2 then
      if (← whnfR (rest.getArg! 0)).isConstOf ``arena.monad.AState then
        return .memo
    if rest.isConstOf ``arena.monad.AState || rest.isConstOf ``arena.store.EStore then
      return .state
    return .rmemo
  if T.isAppOfArity ``core.result.Result 2 then return .read
  if T.isConstOf ``arena.monad.AState then return .write
  return .value

/-- Continue after a bind rule: intro the results, subst, tidy. -/
def cont (g : MVarId) (names : List Name) (hR : Option Name) : TacticM (List MVarId) := do
  let (_, g') ← g.introN names.length names
  tidy g' hR

/-- An error arm through a chain of `ok v >>= k` re-packs (an inlined
fragment's result re-matched by its caller, a swapped pair `ok (st, Err e)`),
each link fed by `bind_tc_ok`. -/
partial def errArmChain (g : MVarId) (depth : Nat := 0) : TacticM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let m ← headNorm (ty.getArg! 1)
  -- the callee of a bind is head-normalised too (a fragment's `let (r, s) :=
  -- (Err e, s)` and its `match` reduce definitionally)
  let m ← if m.isAppOfArity ``Bind.bind 6 then
      pure (mkAppN m.getAppFn (m.getAppArgs.set! 4 (← headNorm (m.getArg! 4))))
    else pure m
  let g ← g.replaceTargetDefEq (mkAppN ty.getAppFn (ty.getAppArgs.set! 1 m))
  -- a packed memo walk's error arm
  if m.isAppOfArity ``packM 3 || m.isAppOfArity ``packRM 4 then
    let isM := m.isAppOfArity ``packM 3
    let t := m.appArg!
    if t.isAppOfArity ``Result.ok 2 then
      return ← runClosed g (if isM then evalT `(tactic| exact ErrArm.packM_ok_err)
        else evalT `(tactic| exact ErrArm.packRM_ok_err))
    if depth < 16 && t.isAppOfArity ``Bind.bind 6 then
      let gs ← applyRule g (if isM then ``ErrArm.packM_bind else ``ErrArm.packRM_bind)
      return ← errArmChain (← pick gs `h) (depth + 1)
  if depth < 16 && m.isAppOfArity ``Bind.bind 6 then
    let f := m.getArg! 4
    if f.isAppOfArity ``Result.ok 2 then
      let gs ← applyRule g ``ErrArm.of_ok_bind
      return ← errArmChain (← pick gs `h) (depth + 1)
  runClosed g (evalT `(tactic| lockstep_errarm))

def errArm (g : MVarId) (names : List Name) : TacticM Unit := do
  let (_, g') ← g.introN names.length names
  errArmChain g'

/-- Drop the branches whose condition contradicts the context. -/
def contra (gs : List MVarId) : TacticM (List MVarId) := do
  let mut out := []
  for g in gs do
    let s ← saveState
    try
      runClosed g (evalT `(tactic| lockstep_contra))
    catch _ =>
      s.restore
      out := out ++ [g]
  return out

def isMatcherApp (e : Expr) : MetaM Bool := do
  return (← matchMatcherApp? e).isSome

/-- One step of a Rust-only (`LSP`) goal. -/
def stepPure (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let m := (ty.getArg! 1).headBeta
  if m.isAppOfArity ``ite 5 then
    let gs ← applyRule g ``LSP.ite
    let g1 ← cont (← pick gs `h₁) [`hc] (some `hc)
    let g2 ← cont (← pick gs `h₂) [`hc] none
    return g1 ++ g2
  if m.isAppOfArity ``Aeneas.Std.uncurry 5 then
    if let .fvar fv := m.appArg! then
      let subs ← g.cases fv
      let mut out := []
      for sg in subs do
        out := out ++ (← tidy sg.mvarId none)
      return out
    else
      let rest ← runOn g (evalT `(tactic| rw [uncurry_apply_proj]))
      match rest with
      | [g'] => return ← tidy g' none
      | _ => return rest
  if let some mapp ← matchMatcherApp? m then
    match mapp.discrs.find? (·.isFVar) with
    | some (.fvar fv) =>
      let subs ← g.cases fv
      let mut out := []
      for sg in subs do
        out := out ++ (← tidy sg.mvarId none)
      return out
    | _ => return ← runOn g (evalT `(tactic| split))
  if m.isAppOfArity ``Bind.bind 6 then
    let s ← saveState
    try
      let gs ← applyRule g ``LSP.bind'
      specCore (← pick gs `hf)
      return ← cont (← pick gs `hk) [`a, `hP] (some `hP)
    catch _ => s.restore
    let gs ← applyRule g ``LSP.bind_eq
    return ← cont (← pick gs `hk) [`a, `hf] none
  if m.isAppOfArity ``Result.ok 2 then
    let gs ← applyRule g ``LSP.ret
    runClosed (← pick gs `h) (evalT `(tactic| lockstep_side))
    return []
  let gs ← applyRule g ``LSP.tail
  specCore (← pick gs `hf)
  runClosed (← pick gs `hPQ) (evalT `(tactic| (intro _ hP; lockstep_side)))
  return []

/-- The term a twin `match` on `t` is cased on: `t` itself, or — when `t` is a
constructor application, which `cases` would only rebuild — the first of its
fields, left to right, that is not one (recursively). -/
partial def caseTarget? (t : Expr) (fvars := false) : MetaM (Option Expr) := do
  let t ← instantiateMVars t
  if t.isLit then return none
  if t.isFVar then return if fvars then some t else none
  if let .const n _ := t.getAppFn then
    if let some (.ctorInfo ci) := (← getEnv).find? n then
      for f in t.getAppArgs.extract ci.numParams t.getAppNumArgs do
        if let some r ← caseTarget? f fvars then return some r
      return none
  return some t

/-- The Rust side moves: a bind, a leaf, or a tail call. -/
partial def rustStep (g : MVarId) (m x : Expr) : TacticM (List MVarId) := g.withContext do
  if m.isAppOfArity ``Bind.bind 6 then
    let f := m.getArg! 4
    let kind ← classify (← inferType f).appArg!
    let s ← saveState
    -- the judgement-specific attempt's failure: for a read it is the one to
    -- report, not the `LSP` fallback's "no @[lockstep] lemma" (task
    -- #97-T2-TACTIC round 2, the Inductives Modeled lane)
    let firstErr ← IO.mkRef (none : Option Exception)
    try
      match kind with
      | .state =>
        let gs ← applyRule g ``LS.bind
        let hx ← pick gs `hx
        specCore (← pick gs `hf) (runClosed hx (evalT `(tactic| lockstep_congr)))
        errArm (← pick gs `he) [`e, `st1]
        return ← cont (← pick gs `hk) [`a, `b, `st1, `lst1, `hR, `hrel, `hinv] (some `hR)
      | .read =>
        let gs ← applyRule g ``LSR.bind
        let hx ← pick gs `hx
        specCore (← pick gs `hf) (runClosed hx (evalT `(tactic| lockstep_congr)))
        errArm (← pick gs `he) [`e]
        return ← cont (← pick gs `hk) [`a, `b, `lst1, `hR, `hrel, `hinv] (some `hR)
      | .write =>
        let gs ← applyRule g ``LSW.bind
        let hx ← pick gs `hx
        specCore (← pick gs `hf) (runClosed hx (evalT `(tactic| lockstep_congr)))
        return ← cont (← pick gs `hk) [`st1, `lst1, `hrel, `hinv] none
      | .value =>
        let gs ← applyRule g ``LSV.bind
        let hx ← pick gs `hx
        specCore (← pick gs `hf) (runClosed hx (evalT `(tactic| lockstep_congr)))
        return ← cont (← pick gs `hk) [`a, `b, `lst1, `hR, `hrel, `hinv] (some `hR)
      | .memo =>
        let gs ← applyRule g ``LS.bindM
        let hx ← pick gs `hx
        specCore (← pick gs `hf) (runClosed hx (evalT `(tactic| lockstep_congr)))
        errArm (← pick gs `he) [`e, `st1, `mm]
        return ← cont (← pick gs `hk) [`a, `mm, `b, `st1, `lst1, `hR, `hrel, `hinv] (some `hR)
      | .rmemo =>
        let gs ← applyRule g ``LS.bindRM
        let hx ← pick gs `hx
        specCore (← pick gs `hf) (runClosed hx (evalT `(tactic| lockstep_congr)))
        errArm (← pick gs `he) [`e, `mm]
        return ← cont (← pick gs `hk) [`a, `mm, `b, `lst1, `hR, `hrel, `hinv] (some `hR)
    catch e =>
      s.restore
      firstErr.set (some e)
      match kind with
      | .state | .write | .memo | .rmemo =>
        -- the twin ends in the partner action where the Rust still binds.
        -- Atomic: the bind is taken on the rewritten goal at once, or the
        -- rewrite is undone — a bare `x >>= pure` goal would be normalised back
        -- to `x` and `lockstep` would loop on it (task #97-T2-LOCKSTEP lane
        -- ExprOps: `inst_lp_fast_ls` never terminated).
        -- Not at a twin `if`: its partner is inside a branch, and the `if` is
        -- decided (or split) by `stepCore` once the Rust cannot move — taking
        -- it whole as the partner would bury it under the `>>= pure` (task
        -- #97-T2-TACTIC round 2, the Checker Base/Top lane's `chk_lockstep`).
        -- Nor at a twin `pure`: it has no partner action, and `LS.twin_pure_bind`
        -- unwraps `pure v >>= pure` again (task #97-P5-Core round 5).
        if !(x.isAppOfArity ``Bind.bind 6) && !(x.isAppOfArity ``ite 5) &&
            !(x.isAppOfArity ``dite 5) && !(x.isAppOfArity ``Pure.pure 4) then
          try
            let gs ← applyRule g ``LS.twin_bind_pure
            let g' ← pick gs `h
            let x' := (← instantiateMVars (← g'.getType)).getAppArgs.back!
            return ← rustStep g' m x'
          catch _ => s.restore
        throw e
      | _ => pure ()
    try
      let gs ← applyRule g ``LSP.bind
      specCore (← pick gs `hf)
      return ← cont (← pick gs `hk) [`a, `hP] (some `hP)
    catch e =>
      s.restore
      match kind with
      | .read => throw ((← firstErr.get).getD e)
      | _ => pure ()
    -- a Rust call that reads the state must have a twin partner
    for arg in f.getAppArgs do
      if (← whnfR (← inferType arg)).isConstOf ``arena.monad.AState then
        throwError "lockstep: the Rust reads the state at `{f.getAppFn}` and no \
          @[lockstep] lemma pairs it with the twin's next action{indentExpr x}"
    let gs ← applyRule g ``LS.bind_eq
    return ← cont (← pick gs `hk) [`a, `hf] none
  -- the leaves
  if m.isAppOfArity ``Result.ok 2 then
    let v := m.getArg! 1
    if v.isAppOfArity ``Prod.mk 4 then
      let r := v.getArg! 2
      if r.isAppOfArity ``core.result.Result.Ok 3 then
        let gs ← applyRule g ``LS.pure
        for n in [`hR, `hrel, `hinv] do
          let sg ← pick gs n
          -- a relation constant that unfolds (reducibly) to a conjunction
          let sg ← sg.withContext do
            let t ← instantiateMVars (← sg.getType)
            if t.isAppOfArity ``And 2 then return sg
            let t' ← whnfR t
            if t'.isAppOfArity ``And 2 then sg.replaceTargetDefEq t' else return sg
          runClosed sg (evalT `(tactic| lockstep_side))
        return []
      if r.isAppOfArity ``core.result.Result.Err 3 then
        let gs ← applyRule g ``LS.err
        runClosed (← pick gs `h) (evalT `(tactic| lockstep_errsim))
        return []
    throwError "lockstep: a Rust leaf the twin does not match{indentExpr (← g.getType)}"
  -- a tail call
  let gs ← applyRule g ``LS.tail
  let hx ← pick gs `hx
  specCore (← pick gs `hf) (runClosed hx (evalT `(tactic| lockstep_congr)))
  runClosed (← pick gs `hR) (evalT `(tactic| (intro _ _ h; first | exact h | (subst h; rfl) | lockstep_side)))
  return []


/-- One step. -/
def stepCore (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  if ty.isAppOfArity ``LSP 3 then return ← stepPure g
  unless ty.isAppOfArity ``LS 7 do throwError "lockstep: not an `LS` goal"
  let m := (ty.getArg! 4).headBeta
  let x := (ty.getArg! 6).headBeta
  -- the Rust side branches
  if m.isAppOfArity ``ite 5 then
    let gs ← applyRule g ``LS.ite
    let g1 ← cont (← pick gs `h₁) [`hc] (some `hc)
    let g2 ← cont (← pick gs `h₂) [`hc] none
    return g1 ++ g2
  if m.isAppOfArity ``Aeneas.Std.uncurry 5 then
    if let .fvar fv := m.appArg! then
      let subs ← g.cases fv
      let mut out := []
      for sg in subs do
        out := out ++ (← tidy sg.mvarId none)
      return out
    else
      let rest ← runOn g (evalT `(tactic| rw [uncurry_apply_proj]))
      match rest with
      | [g'] => return ← tidy g' none
      | _ => return rest
  if let some mapp ← matchMatcherApp? m then
    let d := mapp.discrs.find? (·.isFVar)
    match d with
    | some (.fvar fv) =>
      let subs ← g.cases fv
      let mut out := []
      for sg in subs do
        out := out ++ (← tidy sg.mvarId none)
      return out
    | _ => return ← runOn g (evalT `(tactic| split))
  -- the twin side, when it moves first
  if x.isAppOfArity ``ite 5 then
    let cheap ← `(tactic| lockstep_side_cheap)
    let dear ← `(tactic| lockstep_side_ite)
    -- polarity: the twin's test usually goes the way the last Rust test went
    let lastNeg ← do
      let mut r := false
      for d in (← getLCtx) do
        if d.userName.eraseMacroScopes == `hc then
          r := (← instantiateMVars d.type).isAppOfArity ``Not 1
      pure r
    let rules := if lastNeg then [``LS.twin_ite_neg, ``LS.twin_ite_pos]
      else [``LS.twin_ite_pos, ``LS.twin_ite_neg]
    let tryIte (tac : TSyntax `tactic) : TacticM (Option (List MVarId)) := do
      for rule in rules do
        let s ← saveState
        try
          let gs ← applyRule g rule
          runClosed (← pick gs `hc) (evalTactic tac)
          return some [← pick gs `h]
        catch _ => s.restore
      return none
    -- the fact that decides the twin's test is usually a Rust step away, so a
    -- Rust bind moves first (a Rust-only step does not need the twin)
    if m.isAppOfArity ``Bind.bind 6 then
      let s ← saveState
      try return ← rustStep g m x
      catch _ => s.restore
    if let some r ← tryIte cheap then return r
    if let some r ← tryIte dear then return r
  if x.isAppOfArity ``Bind.bind 6 then
    let a := (x.getArg! 4).headBeta
    if a.isAppOfArity ``Pure.pure 4 then
      let gs ← applyRule g ``LS.twin_pure_bind
      return ← tidy (← pick gs `h) none
    if a.isAppOfArity ``MonadState.get 3 then
      let gs ← applyRule g ``LS.twin_get_bind
      return ← tidy (← pick gs `h) none
    -- a twin `if` in bind position: distribute it over the continuation
    if a.isAppOfArity ``ite 5 then
      let gs ← applyRule g ``LS.twin_ite_bind
      return ← tidy (← pick gs `h) none
    if a.isAppOfArity ``dite 5 then
      let gs ← applyRule g ``LS.twin_dite_bind
      return ← tidy (← pick gs `h) none
  let s0 ← saveState
  try rustStep g m x
  catch e =>
    s0.restore
    -- a twin `if h : c` the cheap tier could not decide (`coreMove` tries only
    -- the cheap tier while the Rust side is a bind)
    if x.isAppOfArity ``dite 5 then
      let dear ← `(tactic| lockstep_side_ite)
      for rule in [``LS.twin_dite_pos, ``LS.twin_dite_neg] do
        let s ← saveState
        try
          let gs ← applyRule g rule
          runClosed (← pick gs `hc) (evalTactic dear)
          return [← pick gs `h]
        catch _ => s.restore
    -- a twin `match` on a TERM (an inline memo probe) the Rust decided by a test
    -- of its own: case on the term; the branch the Rust's test rules out closes
    -- by `lockstep_contra`
    -- A twin-side split is kept only if the context rules out a branch
    -- (`lockstep_contra` closes it), unless `lockstep.twinSplit` is set:
    -- otherwise the zip stops here and hands the goal back, rather than walk
    -- a dead branch (task #97-T2-TACTIC round 2, the Frontend lane).
    let anySplit := lockstep.twinSplit.get (← getOptions)
    let keep (out : List MVarId) : TacticM (Option (List MVarId)) := do
      let kept ← contra out
      if anySplit || kept.length ≤ 1 || kept.length < out.length then return some kept
      return none
    if let some mapp ← matchMatcherApp? x then
      -- a discriminant built from constructors (the Modeled lane's
      -- `some (match v with …), none, …`): `split` the match itself, which
      -- drops the alternatives the constructors rule out
      let isCtorApp (d : Expr) : MetaM Bool := do
        let some n := d.getAppFn.constName? | return false
        match (← getEnv).find? n with
        | some (.ctorInfo _) => return true
        | _ => return false
      if ← mapp.discrs.anyM (fun d => (isCtorApp d : MetaM Bool)) then
        let s1 ← saveState
        try
          let gs ← Lean.Meta.Split.splitMatch g x
          let mut out := []
          for sg in gs do
            out := out ++ (← tidy sg none)
          if let some kept ← keep out then return kept
          s1.restore
        catch _ => s1.restore
      -- the term to case on: a constructor application (`some
      -- (absIConstantInfo v)`) is not one — `cases` would rebuild it and this
      -- move would never end (the Inductives Modeled lane's `check_eta_thm`)
      -- — but its first field that is not; a stuck term in any discriminant
      -- first, a variable field second
      let mut target : Option Expr := none
      for fvars in [false, true] do
        if target.isSome then break
        for d in mapp.discrs do
          if d.isFVar then continue
          if let some t ← caseTarget? d fvars then
            target := some t
            break
      if let some t := target then
        let s1 ← saveState
        let stx ← Lean.Elab.Term.exprToSyntax t
        let rest ← runOn g (evalT `(tactic| cases _hdisc : $stx))
        let mut out := []
        for sg in rest do
          out := out ++ (← tidy sg none)
        if let some kept ← keep out then return kept
        s1.restore
    -- a twin `if` nothing decides and no step moves past: split it
    if x.isAppOfArity ``ite 5 || x.isAppOfArity ``dite 5 then
      let s1 ← saveState
      let gs ← applyRule g (if x.isAppOfArity ``ite 5 then ``LS.twin_ite_split
        else ``LS.twin_dite_split)
      let g1 ← cont (← pick gs `h₁) [`hc] (some `hc)
      let g2 ← cont (← pick gs `h₂) [`hc] (some `hc)
      if let some kept ← keep (g1 ++ g2) then return kept
      s1.restore
    throw e

/-- Is `n` registered `@[lockstep_inline]`? -/
def isInline (n : Name) : MetaM Bool := do
  let some ext ← getSimpExtension? `lockstep_inline | return false
  let thms ← ext.getTheorems
  if thms.isDeclToUnfold n then return true
  return thms.lemmaNames.toList.any fun o => match o with
    | .decl d .. => d.getPrefix == n
    | _ => false

/-- The registered twin-side rules. -/
def twinRules : MetaM (List Name) := do
  let some ext ← getSimpExtension? `lockstep_twin | return []
  let thms ← ext.getTheorems
  return thms.lemmaNames.toList.filterMap fun o => match o with
    | .decl d .. => some d
    | _ => none

/-- Replace argument `i` of the judgement `ty` (the goal of `g`) by `r.expr`. -/
def replaceArg (g : MVarId) (i : Nat) (r : Simp.Result) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let x := ty.getArg! i
  let ty' := mkAppN ty.getAppFn (ty.getAppArgs.set! i r.expr)
  match r.proof? with
  | none => g.replaceTargetDefEq ty'
  | some pf =>
    let motive ← withLocalDeclD `z (← inferType x) fun z =>
      mkLambdaFVars #[z] (mkAppN ty.getAppFn (ty.getAppArgs.set! i z))
    let eq ← mkCongrArg motive pf
    g.replaceTargetEq ty' eq

/-- The Rust argument's position in a judgement. -/
def rustPos (ty : Expr) : Option Nat :=
  if ty.isAppOfArity ``LS 7 then some 4
  else if ty.isAppOfArity ``LSP 3 then some 1
  else none

/-- Unfold the fragment `n` in the Rust argument only. -/
def unfoldRust (g : MVarId) (n : Name) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some i := rustPos ty | throwError "lockstep_core: not a judgement"
  let r ← Meta.unfold (ty.getArg! i) n
  if r.expr == ty.getArg! i then throwError "lockstep_core: {n} did not unfold"
  replaceArg g i r

/-- The `TwinEq` facts a hypothesis carries, through conjunctions. -/
partial def twinEqsOf (pf t : Expr) : MetaM (List (Expr × Expr)) := do
  let t := t.consumeMData
  if t.isAppOfArity ``TwinEq 3 then return [(pf, t)]
  if t.isAppOfArity ``And 2 then
    let l ← twinEqsOf (← mkAppM ``And.left #[pf]) (t.getArg! 0)
    let r ← twinEqsOf (← mkAppM ``And.right #[pf]) (t.getArg! 1)
    return l ++ r
  return []

/-- The twin side rewritten with the `TwinEq` facts of the context and
`lockstep_simp`. -/
def simpTwinEqs (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``LS 7 do return g
  -- the Rust's scalar facts `↑x = e` (a machine word's value), used to put
  -- each `TwinEq`'s left side in the twin's own spelling (`↑i` → `↑np + ↑k`)
  let mut scal : SimpTheorems := {}
  let mut anyScal := false
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if let some (_, l, _) := t.eq? then
      if l.isAppOfArity ``Aeneas.Std.UScalar.val 2 && l.appArg!.isFVar then
        scal ← scal.add (.fvar d.fvarId) #[] d.toExpr
        anyScal := true
  let sctx ← Simp.mkContext (simpTheorems := #[scal]) (congrTheorems := ← getSimpCongrTheorems)
  let some ext ← getSimpExtension? `lockstep_simp | return g
  let base ← ext.getTheorems
  let bctx ← Simp.mkContext (simpTheorems := #[base]) (congrTheorems := ← getSimpCongrTheorems)
  let mut thms : SimpTheorems := {}
  let mut any := false
  let mut i := 0
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    for (pf, te) in ← twinEqsOf d.toExpr t do
      let a := te.getArg! 1
      let b := te.getArg! 2
      let pfEq ← mkExpectedTypeHint pf (← mkEq a b)
      let mut rule := pfEq
      if anyScal then
        let (r, _) ← simp a sctx
        if r.expr != a then
          if let some p := r.proof? then
            rule ← mkEqTrans (← mkEqSymm p) pfEq
      thms ← thms.add (.fvar d.fvarId) #[] rule
      if rule != pfEq then
        thms ← thms.add (.fvar d.fvarId) #[] pfEq
      -- the `lockstep_simp` set normalises the twin's subterms before a rule
      -- sees the enclosing term (`absEIdxList xs` → `xs.val.map absEIdx`,
      -- `↑0#usize` → `0`), so each left side is offered in that normal form
      -- too (of the scalar-respelled side as well)
      let rt ← inferType rule
      let some (_, a1, _) := rt.eq? | pure ()
      -- (the respelled side only when it differs: one `simp` call per side)
      let sides := if a1 == a then [(a, pfEq)] else [(a, pfEq), (a1, rule)]
      for (lhs, prf) in sides do
        let (r, _) ← simp lhs bctx
        if r.expr != lhs then
          let pn ← match r.proof? with
            | some p => mkEqTrans (← mkEqSymm p) prf
            | none => mkExpectedTypeHint prf (← mkEq r.expr b)
          thms ← thms.add (.fvar d.fvarId) #[] pn
      any := true
  unless any do return g
  let x := ty.getArg! 6
  let ctx ← Simp.mkContext (simpTheorems := #[base, thms]) (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simp x ctx
  if r.expr == x then return g
  replaceArg g 6 r

def normAll (gs : List MVarId) : TacticM (List MVarId) :=
  gs.mapM fun g => do
    let g ← normGoal g
    let g ← simpTwinEqs g
    clearStale g

/-- Apply `rule`, run `tac` on the premise named `side` (if any), and return
the premise named `next`. -/
def applyWith (g : MVarId) (rule : Name) (side : List Name) (next : Name)
    (extra : List Name := []) : TacticM MVarId := do
  let gs ← applyRule g rule
  for s in side do
    runClosed (← pick gs s) (evalT `(tactic| lockstep_side))
  for s in extra do
    runClosed (← pick gs s) (evalT `(tactic| (intros; rfl)))
  pick gs next

/-- One Rust-side move of a packed memo walk `packM t` / `packRM st t`. -/
def packMove (g : MVarId) (m : Expr) : TacticM (List MVarId) := g.withContext do
  let isM := m.isAppOfArity ``packM 3
  let t ← headNorm m.appArg!
  if t.isAppOfArity ``Bind.bind 6 then
    let gs ← applyRule g (if isM then ``LS.packM_bind else ``LS.packRM_bind)
    return ← normAll [← pick gs `h]
  if t.isAppOfArity ``ite 5 then
    let gs ← applyRule g (if isM then ``LS.packM_ite else ``LS.packRM_ite)
    return ← normAll [← pick gs `h]
  if t.isAppOfArity ``Result.ok 2 then
    let v ← instantiateMVars t.appArg!
    if v.isAppOfArity ``Prod.mk 4 then
      let r := (v.getArg! 2).headBeta
      if r.isAppOf ``core.result.Result.Ok then
        let gs ← applyRule g (if isM then ``LS.packM_ok_ok else ``LS.packRM_ok_ok)
        return ← normAll [← pick gs `h]
      if r.isAppOf ``core.result.Result.Err then
        let gs ← applyRule g (if isM then ``LS.packM_ok_err else ``LS.packRM_ok_err)
        return ← normAll [← pick gs `h]
      if let .fvar fv := r then
        let subs ← g.cases fv
        return ← normAll (subs.toList.map (·.mvarId))
    throwError "lockstep: a packed Rust leaf with no constructor to read{indentExpr t}"
  if t.isAppOfArity ``Aeneas.Std.uncurry 5 then
    if let .fvar fv := t.appArg! then
      let subs ← g.cases fv
      return ← normAll (subs.toList.map (·.mvarId))
  if let some mapp ← matchMatcherApp? t then
    if let some (.fvar fv) := mapp.discrs.find? (·.isFVar) then
      let subs ← g.cases fv
      return ← normAll (subs.toList.map (·.mvarId))
    throwError "lockstep: a packed Rust `match` on a term{indentExpr t}"
  -- a memoised walk in tail position
  let gs ← applyRule g (if isM then ``LS.tailM else ``LS.tailRM)
  let hx ← pick gs `hx
  specCore (← pick gs `hf) (runClosed hx (evalT `(tactic| lockstep_congr)))
  runClosed (← pick gs `hR)
    (evalT `(tactic| (intro _ _ h; first | exact h | (subst h; rfl) | lockstep_side)))
  return []

/-- The Core tier's extra moves; `none` when none applies. -/
def coreMove (g : MVarId) : TacticM (Option (List MVarId)) := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some rp := rustPos ty | return none
  let isLS := rp == 4
  let m := (ty.getArg! rp).headBeta
  -- a packed memo walk (an unfolded `LSM`/`LSRM`): push the packing through
  if isLS && (m.isAppOfArity ``packM 3 || m.isAppOfArity ``packRM 4) then
    return some (← packMove g m)
  -- a tail call to a fragment
  if let some n := m.getAppFn.constName? then
    if ← isInline n then
      return some (← normAll [← unfoldRust g n])
  if m.isAppOfArity ``Bind.bind 6 then
    let f ← headNorm (m.getArg! 4)
    let k := m.getArg! 5
    if f != m.getArg! 4 then
      let m' := mkAppN m.getAppFn (m.getAppArgs.set! 4 f)
      let g' ← g.replaceTargetDefEq (mkAppN ty.getAppFn (ty.getAppArgs.set! rp m'))
      return some [g']
    if f.isAppOfArity ``Result.ok 2 then
      -- `ok v >>= k` is `k v` only propositionally (`bind_tc_ok`)
      let _ := k
      let gs ← applyRule g (if isLS then ``LS.rust_ok_bind else ``LSP.rust_ok_bind)
      return some (← normAll [← pick gs `h])
    if f.isAppOfArity ``Bind.bind 6 then
      let g' ← applyWith g (if isLS then ``LS.rust_assoc else ``LSP.rust_assoc) [] `h
      return some [g']
    if f.isAppOfArity ``ite 5 then
      let gs ← applyRule g (if isLS then ``LS.rust_ite_bind else ``LSP.rust_ite_bind)
      let g1 ← cont (← pick gs `h₁) [`hc] (some `hc)
      let g2 ← cont (← pick gs `h₂) [`hc] none
      return some (← normAll (g1 ++ g2))
    -- a tuple pattern `let (x, y) := p` in bind position
    if f.isAppOfArity ``Aeneas.Std.uncurry 5 then
      if let .fvar fv := f.appArg! then
        let subs ← g.cases fv
        return some (← normAll (subs.toList.map (·.mvarId)))
    if let some mapp ← matchMatcherApp? f then
      if let some (.fvar fv) := mapp.discrs.find? (·.isFVar) then
        let subs ← g.cases fv
        return some (← normAll (subs.toList.map (·.mvarId)))
      -- a `match` on a projection of a pair variable
      for d in mapp.discrs do
        let d ← instantiateMVars d
        for fv in (Lean.collectFVars {} d).fvarIds do
          if (← whnfR (← fv.getType)).isAppOf ``Prod then
            let subs ← g.cases fv
            return some (← normAll (subs.toList.map (·.mvarId)))
      -- a `match` on a TERM (a memo probe the twin makes inline): rewrite the
      -- term with the context's key equations (`absEIdxNat k = (h, d)`) so it
      -- is the twin's own, then case on it everywhere
      if isLS then
        if let some t0 := mapp.discrs[0]? then
          let mut g := g
          let mut t := t0
          for d in (← getLCtx) do
            if d.isImplementationDetail then continue
            let dty ← instantiateMVars d.type
            if dty.isAppOfArity ``Eq 3 then
              let lhs := dty.getArg! 1
              if !lhs.isFVar && (t.find? (· == lhs)).isSome then
                let hi := mkIdent d.userName
                let rest ← runOn g (evalT `(tactic| rw [$hi:ident]))
                if let [g'] := rest then
                  g := g'
                  let ty' ← instantiateMVars (← g.getType)
                  let m' := (ty'.getArg! 4).headBeta
                  if let some mapp' ← matchMatcherApp? (m'.getArg! 4).headBeta then
                    if let some t' := mapp'.discrs[0]? then t := t'
          let stx ← Lean.Elab.Term.exprToSyntax t
          let rest ← runOn g (evalT `(tactic| cases _hdisc : $stx))
          return some (← normAll rest)
    if let some n := f.getAppFn.constName? then
      if ← isInline n then
        return some (← normAll [← unfoldRust g n])
    -- a read in tail position: `f >>= fun o => ok (o, st)`
    if isLS then
      if let .read ← classify (← inferType f).appArg! then
        let s ← saveState
        try
          let gs ← applyRule g ``LSR.tail_ls
          let hx ← pick gs `hx
          specCore (← pick gs `hf) (runClosed hx (evalT `(tactic| lockstep_congr)))
          runClosed (← pick gs `hR)
            (evalT `(tactic| (intro _ _ h; first | exact h | (subst h; rfl) | lockstep_side)))
          return some []
        catch _ => s.restore
    -- a store-level step
    if isLS then
      let T ← whnfR (← inferType f)
      if T.isAppOfArity ``Result 1 then
        let P ← whnfR T.appArg!
        if P.isAppOfArity ``Prod 2 && (P.getArg! 1).isConstOf ``arena.store.EStore then
          let gs ← applyRule g ``LSS.bind
          -- the state the port rebuilds is not in the step's own type: read it
          -- off the store argument (`X.store`) or off the continuation's
          -- `{ store := s, … }` at that store
          let hf ← pick gs `hf
          let hfTy ← instantiateMVars (← hf.getType)
          let stM := hfTy.getArg! 5
          if stM.isMVar then
            let storeArg? ← f.getAppArgs.findM? fun a => do
              return (← whnfR (← inferType a)).isConstOf ``arena.store.EStore
            if let some sa := storeArg? then
              let sa ← instantiateMVars sa
              if sa.isAppOfArity ``arena.monad.AState.store 1 then
                discard <| isDefEq stM sa.appArg!
              else if let .proj _ 0 x := sa then
                discard <| isDefEq stM x
              else
                let k := m.getArg! 5
                let found := k.find? fun t =>
                  t.isAppOfArity ``arena.monad.AState.mk 4 && t.getArg! 0 == sa
                if let some t := found then discard <| isDefEq stM t
                else
                  -- a lookup on the store a previous step returned: the state
                  -- the continuation rebuilds, at this step's store
                  let any := k.find? fun t => t.isAppOfArity ``arena.monad.AState.mk 4
                  if let some t := any then
                    discard <| isDefEq stM (mkAppN t.getAppFn ((t.getAppArgs).set! 0 sa))
          let hx ← pick gs `hx
          specCore hf (runClosed hx (evalT `(tactic| lockstep_congr)))
          errArm (← pick gs `he) [`e, `s']
          return some (← normAll (← cont (← pick gs `hk) [`a, `b, `s', `lst1, `hR, `hrel, `hinv] (some `hR)))
  -- a tag-guarded projection on the Rust side against the twin's `view`
  if isLS && m.isAppOfArity ``Bind.bind 6 then
    let x := (ty.getArg! 6).headBeta
    let isProj := match (m.getArg! 4).getAppFn.constName? with
      | some n => n != ``arena.monad.view && n.getPrefix == (``arena.monad.view).getPrefix &&
          (match n with | .str _ s => s.startsWith "view_" | _ => false)
      | none => false
    if isProj && x.isAppOfArity ``Bind.bind 6 &&
        ((x.getArg! 4).headBeta.isAppOf ``Arena.view) then
      for rule in ← twinRules do
        let s ← saveState
        try
          let gs ← applyRule g rule
          for (n, sg) in gs do
            if ← sg.isAssigned then continue
            if n == `ht then runClosed sg (evalT `(tactic| lockstep_side))
            -- `hg`: the twin's continuation ignores the levels.  Checked at
            -- reducible transparency: a default `rfl` unfolds whatever the
            -- continuation calls on the levels, without bound (the Inductives
            -- Modeled lane's `nested_rule_shape_at` hung)
            else if n == `hg then
              runClosed sg (evalT `(tactic| (intros; first | with_reducible rfl | (dsimp only; done))))
          let g' ← pick gs `hls
          let g' ← normGoal g'
          -- keep the rule only if the port's projection now steps
          let rest ← stepCore g'
          return some (← normAll rest)
        catch _ => s.restore
  -- a twin `if h : c then … else …` (a `dite`), decided by the context
  if isLS then
    let x := (ty.getArg! 6).headBeta
    if x.isAppOfArity ``dite 5 then
      let cheap ← `(tactic| lockstep_side_cheap)
      let dear ← `(tactic| lockstep_side_ite)
      let sides := if m.isAppOfArity ``Bind.bind 6 then [cheap] else [cheap, dear]
      for side in sides do
        for rule in [``LS.twin_dite_pos, ``LS.twin_dite_neg] do
          let s ← saveState
          try
            let gs ← applyRule g rule
            runClosed (← pick gs `hc) (evalTactic side)
            return some (← normAll [← pick gs `h])
          catch _ => s.restore
  return none

/-- **One lockstep step** on the main goal. -/
elab "lockstep_step" : tactic => do
  let g ← getMainGoal
  -- a target wrapped in `mdata` (after `generalize`, `rcases`, `have`) is
  -- matched on its bare form
  let g ← g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let g ← if ty.consumeMData != ty then g.replaceTargetDefEq ty.consumeMData else pure g
    -- a memoised walk's judgement is `LS` of the packed walk
    let ty := ty.consumeMData
    if ty.isAppOfArity ``LSM 8 || ty.isAppOfArity ``LSRM 9 then
      match ← unfoldDefinition? ty with
      | some ty' => g.replaceTargetDefEq ty'
      | none => pure g
    else pure g
  let others := (← getGoals).tail
  let s ← saveState
  try
    match ← coreMove g with
    | some rest => setGoals (rest ++ others); return
    | none => pure ()
  catch _ => s.restore
  try
    let rest ← stepCore g
    let rest ← normAll rest
    setGoals (rest ++ others)
  catch e =>
    s.restore
    -- a stuck goal may be a branch the context rules out
    try
      runClosed g (evalT `(tactic| lockstep_contra))
      setGoals others
    catch _ =>
      s.restore
      throw e

/-- **The lockstep tactic**: step until every goal is closed or stuck. -/
macro "lockstep" : tactic => `(tactic| repeat' lockstep_step)

/-- Task #97-P5-Core round 5's name for `lockstep` (the moves it added now live
in `lockstep` itself); kept so the round's region files read unchanged. -/
macro "lockstep_core" : tactic => `(tactic| lockstep)

end Lockstep

end ConRon.Refine2

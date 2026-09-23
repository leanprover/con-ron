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

## The tactic (modelled on Aeneas's `progress`, see DESIGN task #97-T2-TACTIC)

`lockstep` repeats `lockstep_step` and stops at the first goal it cannot make
progress on.  One step looks at the RUST side of the goal:

* a bind `f >>= k`: pick the bind rule by `f`'s type, then close the rule's
  spec premise with a `@[lockstep]` lemma (or a local hypothesis — the
  induction hypothesis) keyed on `f`'s head constant.  The spec's TWIN action
  is not unified against the goal's: the rules take `x' = x` as a separate
  premise, closed by `congr` and the side tactic, so an argument that is the
  same number spelled differently (`absU i1` against `absU c + 1`) is a side
  goal rather than a unification failure;
* an `if`/`match`: split the Rust side, then reduce the twin's `if`/`match` on
  the facts that split produced;
* a leaf `ok (.Ok a, st)` / `ok (.Err e, st)`: close against the twin's `pure`
  / `throw`;
* anything else (a tail call): a spec lemma directly.

Side goals (relation, invariant, argument correspondence, conditions) go to
`lockstep_side`, which is `assumption`/`rfl`/`simp`/`scalar_tac`, in that
order.  **No `grind`** anywhere in the tactic.
-/
import ConRon.Refine2.Tactic.Tmp0
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

/-! ## Pure Rust-only specs of the machine words -/

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

/-- A twin-only `get`. -/
theorem LS.twin_get_bind {α δ : Type} {pers : arena.store.PersTier} {R : α → δ → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {g : AState → AM δ} (h : LS pers R m lst (g lst)) :
    LS pers R m lst (MonadState.get >>= g) := by
  intro o st' hm
  exact h o st' hm

/-! ## The tactic -/

attribute [lockstep_simp] Aeneas.Std.uncurry_apply_pair


open Lean Meta Elab Tactic

/-- Side goals: the relation and the invariant at the current state, an
argument correspondence, a branch condition. -/
syntax "lockstep_side" : tactic
macro_rules
  | `(tactic| lockstep_side) => `(tactic| first
      | assumption
      | rfl
      | (simp only [lockstep_simp] at *; first | assumption | rfl | done)
      | scalar_tac
      | (simp_all only [lockstep_simp]; done)
      | (simp_all; done))

/-- A branch the context rules out. -/
syntax "lockstep_contra" : tactic
macro_rules
  | `(tactic| lockstep_contra) => `(tactic| (exfalso; scalar_tac))

/-- The twin-action correspondence `x' = x` a bind rule leaves. -/
syntax "lockstep_congr" : tactic
macro_rules
  | `(tactic| lockstep_congr) => `(tactic| first
      | rfl
      | (congr 1 <;> lockstep_side)
      | (simp only [lockstep_simp] at *; done))

/-- The twin's error leaf. -/
syntax "lockstep_errsim" : tactic
macro_rules
  | `(tactic| lockstep_errsim) => `(tactic| first
      | exact AErrSim.native _
      | (refine AErrSim.mk rfl ?_; rfl)
      | exact errSim_fail rfl
      | exact errSim_throw rfl
      | assumption
      | (simp only [lockstep_simp] at *; first | exact errSim_fail rfl | exact errSim_throw rfl))

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
def specCore (g : MVarId) : TacticM Unit := g.withContext do
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
      match judgementRustArg? c with
      | some m' => rustKey? m'.headBeta == some k
      | none => false
    if ok then cands := cands.push d.toExpr
  for n in (← lockstepLemmas k) do
    cands := cands.push (← mkConstWithFreshMVarLevels n)
  if cands.isEmpty then
    throwError "lockstep: no @[lockstep] lemma for `{k}`"
  let s ← saveState
  let mut errs : Array MessageData := #[]
  for c in cands do
    try
      let gs ← g.apply c
      for sg in gs do
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

/-- Tidy a continuation: `subst` the answer relation, reduce the two bodies. -/
def tidy (g : MVarId) (hR : Option Name) : TacticM (List MVarId) := do
  runOn g do
    if let some h := hR then
      evalT `(tactic| try subst $(mkIdent h):ident)
    evalT `(tactic| try dsimp only)
    evalT `(tactic| try simp only [lockstep_simp])

/-- The Rust computation's shape. -/
inductive RKind where
  | state | read | write | value

def classify (T : Expr) : MetaM RKind := do
  let T ← whnfR T
  if T.isAppOfArity ``Prod 2 && (T.getArg! 0).isAppOfArity ``core.result.Result 2 then
    return .state
  if T.isAppOfArity ``core.result.Result 2 then return .read
  if T.isConstOf ``arena.monad.AState then return .write
  return .value

/-- Continue after a bind rule: intro the results, subst, tidy. -/
def cont (g : MVarId) (names : List Name) (hR : Option Name) : TacticM (List MVarId) := do
  let (_, g') ← g.introN names.length names
  tidy g' hR

def errArm (g : MVarId) (names : List Name) : TacticM Unit := do
  let (_, g') ← g.introN names.length names
  runClosed g' (evalT `(tactic| ((try dsimp only); (try simp only [lockstep_simp]); exact errArm_ok)))

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

/-- One step. -/
def stepCore (g : MVarId) : TacticM (List MVarId) := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``LS 7 do throwError "lockstep: not an `LS` goal"
  let m := (ty.getArg! 4).headBeta
  let x := (ty.getArg! 6).headBeta
  -- the Rust side branches
  if m.isAppOfArity ``ite 5 then
    let gs ← applyRule g ``LS.ite
    let g1 ← contra (← cont (← pick gs `h₁) [`hc] none)
    let g2 ← contra (← cont (← pick gs `h₂) [`hc] none)
    return g1 ++ g2
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
    let s ← saveState
    try
      let gs ← applyRule g ``LS.twin_ite_pos
      runClosed (← pick gs `hc) (evalT `(tactic| lockstep_side))
      return [← pick gs `h]
    catch _ =>
      s.restore
      let gs ← applyRule g ``LS.twin_ite_neg
      runClosed (← pick gs `hc) (evalT `(tactic| lockstep_side))
      return [← pick gs `h]
  if x.isAppOfArity ``Bind.bind 6 then
    let a := (x.getArg! 4).headBeta
    if a.isAppOfArity ``Pure.pure 4 then
      let gs ← applyRule g ``LS.twin_pure_bind
      return ← tidy (← pick gs `h) none
    if a.isAppOfArity ``MonadState.get 3 then
      let gs ← applyRule g ``LS.twin_get_bind
      return ← tidy (← pick gs `h) none
  -- the Rust side moves
  if m.isAppOfArity ``Bind.bind 6 then
    let f := m.getArg! 4
    let kind ← classify (← inferType f).appArg!
    let s ← saveState
    try
      match kind with
      | .state =>
        let gs ← applyRule g ``LS.bind
        specCore (← pick gs `hf)
        runClosed (← pick gs `hx) (evalT `(tactic| lockstep_congr))
        errArm (← pick gs `he) [`e, `st1]
        return ← cont (← pick gs `hk) [`a, `b, `st1, `lst1, `hR, `hrel, `hinv] (some `hR)
      | .read =>
        let gs ← applyRule g ``LSR.bind
        specCore (← pick gs `hf)
        runClosed (← pick gs `hx) (evalT `(tactic| lockstep_congr))
        errArm (← pick gs `he) [`e]
        return ← cont (← pick gs `hk) [`a, `b, `lst1, `hR, `hrel, `hinv] (some `hR)
      | .write =>
        let gs ← applyRule g ``LSW.bind
        specCore (← pick gs `hf)
        runClosed (← pick gs `hx) (evalT `(tactic| lockstep_congr))
        return ← cont (← pick gs `hk) [`st1, `lst1, `hrel, `hinv] none
      | .value =>
        let gs ← applyRule g ``LSV.bind
        specCore (← pick gs `hf)
        runClosed (← pick gs `hx) (evalT `(tactic| lockstep_congr))
        return ← cont (← pick gs `hk) [`a, `b, `lst1, `hR, `hrel, `hinv] (some `hR)
    catch e =>
      s.restore
      match kind with
      | .state | .write => throw e
      | _ => pure ()
    try
      let gs ← applyRule g ``LSP.bind
      specCore (← pick gs `hf)
      return ← cont (← pick gs `hk) [`a, `hP] (some `hP)
    catch e =>
      s.restore
      match kind with
      | .read => throw e
      | _ => pure ()
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
          runClosed (← pick gs n) (evalT `(tactic| lockstep_side))
        return []
      if r.isAppOfArity ``core.result.Result.Err 3 then
        let gs ← applyRule g ``LS.err
        runClosed (← pick gs `h) (evalT `(tactic| lockstep_errsim))
        return []
    throwError "lockstep: a Rust leaf the twin does not match{indentExpr ty}"
  -- a tail call
  let gs ← applyRule g ``LS.tail
  specCore (← pick gs `hf)
  runClosed (← pick gs `hx) (evalT `(tactic| lockstep_congr))
  runClosed (← pick gs `hR) (evalT `(tactic| (intro _ _ h; first | exact h | (subst h; rfl) | lockstep_side)))
  return []

/-- **One lockstep step** on the main goal. -/
elab "lockstep_step" : tactic => do
  let g ← getMainGoal
  let others := (← getGoals).tail
  let s ← saveState
  try
    let rest ← stepCore g
    setGoals (rest ++ others)
  catch e =>
    s.restore
    throw e

/-- **The lockstep tactic**: step until every goal is closed or stuck. -/
macro "lockstep" : tactic => `(tactic| repeat' lockstep_step)

end Lockstep

end ConRon.Refine2

/-
# `ConRon.Refine2.Core.LS.Tactic` — `lockstep` for the Core tier: fragments, store steps, projections

Task #97-P5-Core round 5.  `Tactic/Lockstep.lean`'s `lockstep` zips two
do-blocks bind by bind and closes each callee pair with a `@[lockstep]`
lemma.  The Core tier needs four more moves, all of them bookkeeping about
*where* the same operation is written, not about what it does:

1. **The port splits one twin function into fragments** (`whnf_core_proj`,
   `whnf_core_proj_at`, `whnf_core_proj_fire` are three Rust functions for
   the one `.proj` arm of `whnfCoreBody`).  A fragment carries
   `@[lockstep_inline]` and is UNFOLDED in place, on the Rust side only; the
   binds it leaves are re-associated (`LS.rust_assoc`), its `if` is split
   (`LS.rust_ite_bind`), its `match` on a variable is a case split, and its
   `ok v` feeds the continuation.
2. **A store-level Rust step** returns `(Result α, EStore)` and the caller
   rebuilds `{ st with store := e }` (`ifenv_find_proj`,
   `i_constant_info_to_constant_val`).  `LSS` is that judgement, and
   `LSS.bind` its rule.
3. **A Rust-only read whose twin partner is a pure expression**
   (`ifenv_find` against `IFEnv.find?`).  Its `@[lockstep]` `LSP` lemma
   concludes a `TwinEq a b`; the twin side is then rewritten with every
   `TwinEq` in the context after every step.
4. **A tag-guarded projection.**  The port tests a handle's tag and reads the
   typed projection (`view_const`); the twin tests the same tag and reads the
   whole view, matching on the constructor (task #97-P5-Core round 4's
   tag-first shape).  Under the tag, the view IS the projection
   (`EStore_view_of_tag_*`, no `StoreWF`), so `LS.twin_view_*` rewrites the
   twin's `view h >>= g` to `viewC h >>= …` and the zip continues.

`lockstep_core` is `lockstep` with these moves tried first.
-/
import ConRon.Refine2.Tactic.Prims
import ConRon.Refine2.Core.Arms.Delta

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Lockstep

open ConRon.Arena ConRon.Refine2

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

/-! ### The tag-guarded projections -/

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

theorem LS.twin_view_const {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {h : EIdx} {g : ENodeView → AM β} (ht : h.tag = ETag.const)
    (hls : LS pers R m lst (viewConst h >>= danglingOr fun p => g (.const p.1 p.2))) :
    LS pers R m lst (Arena.view h >>= g) := by
  rw [view_bind_of_proj h (viewConst h) (fun s => s.viewConst h) (fun _ => rfl)
    (fun p => .const p.1 p.2) (fun st => EStore_view_of_tag_const st h ht)]
  exact hls

theorem LS.twin_view_sort {α β : Type} {pers : arena.store.PersTier} {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {h : EIdx} {g : ENodeView → AM β} (ht : h.tag = ETag.sort)
    (hls : LS pers R m lst (viewSort h >>= danglingOr fun p => g (.sort p))) :
    LS pers R m lst (Arena.view h >>= g) := by
  rw [view_bind_of_proj h (viewSort h) (fun s => s.viewSort h) (fun _ => rfl)
    ENodeView.sort (fun st => EStore_view_of_tag_sort st h ht)]
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
theorem LS.twin_view_const_name {α β : Type} {pers : arena.store.PersTier}
    {R : α → β → Prop}
    {m : Result (core.result.Result α kernel.core_types.CheckError × arena.monad.AState)}
    {lst : AState} {h : EIdx} {g : ENodeView → AM β} (ht : h.tag = ETag.const)
    (hg : ∀ c us, g (.const c us) = g (.const c ⟨0⟩))
    (hls : LS pers R m lst (viewConstName h >>= danglingOr fun c => g (.const c ⟨0⟩))) :
    LS pers R m lst (Arena.view h >>= g) := by
  have key : (Arena.view h >>= g) = (viewConstName h >>= danglingOr fun c => g (.const c ⟨0⟩)) := by
    funext lst
    show (Arena.view h >>= g).run lst = (viewConstName h >>= _).run lst
    rw [StateT.run_bind, StateT.run_bind, view_run_of, EStore_view_of_tag_const _ h ht]
    show _ = ((danglingOr (fun c => g (.const c ⟨0⟩)) (lst.store.viewConstName h)).run lst)
    rw [EStore_viewConstName_eq]
    cases lst.store.viewConst h with
    | none => rfl
    | some p =>
      show (g (.const p.1 p.2)).run lst = (g (.const p.1 ⟨0⟩)).run lst
      rw [hg]
  rw [key]; exact hls

/-! ## The tactic -/

open Lean Meta Elab Tactic

/-- Is `n` registered `@[lockstep_inline]`? -/
def isInline (n : Name) : MetaM Bool := do
  let some ext ← getSimpExtension? `lockstep_inline | return false
  let thms ← ext.getTheorems
  if thms.isDeclToUnfold n then return true
  return thms.lemmaNames.toList.any fun o => match o with
    | .decl d .. => d.getPrefix == n
    | _ => false

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

/-- The twin side rewritten with the `TwinEq` facts of the context and
`lockstep_simp`. -/
def simpTwinEqs (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``LS 7 do return g
  let mut thms : SimpTheorems := {}
  let mut any := false
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``TwinEq 3 then
      let eqTy ← mkEq (t.getArg! 1) (t.getArg! 2)
      thms ← thms.add (.fvar d.fvarId) #[] (← mkExpectedTypeHint d.toExpr eqTy)
      any := true
  unless any do return g
  let some ext ← getSimpExtension? `lockstep_simp | return g
  let base ← ext.getTheorems
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

/-- The Core tier's extra moves; `none` when none applies. -/
def coreMove (g : MVarId) : TacticM (Option (List MVarId)) := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some rp := rustPos ty | return none
  let isLS := rp == 4
  let m := (ty.getArg! rp).headBeta
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
      let m' := (mkApp k (f.getArg! 1)).headBeta
      let g' ← g.replaceTargetDefEq (mkAppN ty.getAppFn (ty.getAppArgs.set! rp m'))
      return some (← normAll [g'])
    if f.isAppOfArity ``Bind.bind 6 then
      let g' ← applyWith g (if isLS then ``LS.rust_assoc else ``LSP.rust_assoc) [] `h
      return some [g']
    if f.isAppOfArity ``ite 5 then
      let gs ← applyRule g (if isLS then ``LS.rust_ite_bind else ``LSP.rust_ite_bind)
      let g1 ← cont (← pick gs `h₁) [`hc] (some `hc)
      let g2 ← cont (← pick gs `h₂) [`hc] none
      return some (← normAll (g1 ++ g2))
    if let some mapp ← matchMatcherApp? f then
      if let some (.fvar fv) := mapp.discrs.find? (·.isFVar) then
        let subs ← g.cases fv
        return some (← normAll (subs.toList.map (·.mvarId)))
    if let some n := f.getAppFn.constName? then
      if ← isInline n then
        return some (← normAll [← unfoldRust g n])
    -- a store-level step
    if isLS then
      let T ← whnfR (← inferType f)
      if T.isAppOfArity ``Result 1 then
        let P ← whnfR T.appArg!
        if P.isAppOfArity ``Prod 2 && (P.getArg! 1).isConstOf ``arena.store.EStore then
          let gs ← applyRule g ``LSS.bind
          specCore (← pick gs `hf)
          runClosed (← pick gs `hx) (evalT `(tactic| lockstep_congr))
          errArm (← pick gs `he) [`e, `s']
          return some (← normAll (← cont (← pick gs `hk) [`a, `b, `s', `lst1, `hR, `hrel, `hinv] (some `hR)))
  -- a tag-guarded projection on the Rust side against the twin's `view`
  if isLS && m.isAppOfArity ``Bind.bind 6 then
    let x := (ty.getArg! 6).headBeta
    if x.isAppOfArity ``Bind.bind 6 && ((x.getArg! 4).headBeta.isAppOf ``Arena.view) then
      let fn := (m.getArg! 4).getAppFn.constName?
      let rule? : Option (Name × List Name) := match fn with
        | some ``arena.monad.view_const => some (``LS.twin_view_const, [])
        | some ``arena.monad.view_sort => some (``LS.twin_view_sort, [])
        | some ``arena.monad.view_const_name => some (``LS.twin_view_const_name, [`hg])
        | _ => none
      if let some (rule, extra) := rule? then
        let g' ← applyWith g rule [`ht] `hls extra
        return some (← normAll [g'])
  return none

/-- One Core step: the extra moves first, then `lockstep_step`'s. -/
elab "lockstep_core_step" : tactic => do
  let g ← getMainGoal
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
    try
      runClosed g (evalT `(tactic| lockstep_contra))
      setGoals others
    catch _ =>
      s.restore
      throw e

/-- **`lockstep` for the Core tier.** -/
macro "lockstep_core" : tactic => `(tactic| repeat' lockstep_core_step)

end ConRon.Refine2.Lockstep

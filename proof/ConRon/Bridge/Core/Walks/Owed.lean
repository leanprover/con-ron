/-
# `ConRon.Bridge.Core.Walks.Owed` — the sixteen statements the round did not reach

Task #97-P3-CoreWalks.  DESIGN §8's `### Task #97-P3-Core` §6 ends with the
round's own estimate of where the next tier's work is:

> what the tier is waiting on … is a `BodySpec`-shaped theorem for the ~15
> `Arena/Core.lean` walks that are not knot slots (`iotaRec`, `projCertAt`,
> `projLitToCtor`, `propIrrel`, `stuckIrrel`, `etaCert`, `defeqSpine`,
> `defEqList`, `reduceNat`, `unfoldDefinition`, `annotPwPi`, `annotPwLam`,
> `IProjEntry.typeAt`, `lvlEq?`, the readbacks).  **It is bigger than the six
> bodies.**

This module is that list, **stated**.  `lvlEq?`/`lvlsEq?` and the readbacks
are `Bridge/Core/Walks/{Cached,Frame}.lean` and are CLOSED; `ensureSort` is
`Bridge/Core/EnsureSort.lean` and is CLOSED; `IProjEntry.typeAt` is the one
name of the list that is NOT here, and §3 says why; `isBoolTrue` is
`Bridge/Core/Walks/Guards.lean` and is CLOSED.  The sixteen below are what is
left of it, each with the con-leche function it refines named through
`Verify/Knot.lean`'s own `…Fueled` abbreviation, and each `sorry` with what
it is waiting on written at the site.

This is `Bridge/ExprOps/Owed.lean`'s role one tier up: a statement is not a
proof, but it is the interface, and the six body walks cannot be written
against a walk that has no statement.

## 0. The shape correction of task #97-P3-Core-2, and why it was forced

The first two statements of this module — `unfoldDefinition_spec` and
`reduceNat_spec`, the two `whnfBody_spec` consumes — took the subject's
denotation as an explicit `(x : Expr)` argument with a
`denoteE s₀.store e = some x` hypothesis.  **That shape cannot be used from a
caller that reaches the walk through another call**, and `whnfStep` is
exactly such a caller: it runs `r.whnfCore` first and hands `reduceNat` the
REDUCT, whose denotation is not known until the first call's postcondition is
in hand.  `mvcgen` must guess `x` when it applies the spec, it guesses the
only `Expr` in scope (the *original* subject), and the side goal it leaves —
`denoteE s.store <reduct> = some <original>` — is false.

The fix is task #97-P3-0's own **rule 4** (*"a precondition with no `Expr` in
it, so that a recursive call's side goal carries no metavariable"*) taken one
step further: the denotation goes into the hypothesis as an **existential**
(`∃ x, denoteE s₀.store e = some x ∧ Expr.WScoped d x`, which names no
metavariable) and out of the postcondition as a **universal** (`∀ x,
denoteE s₀.store e = some x → …`), which is the shape
`Bridge/Core/Walks/Cached.lean`'s closed exemplars already have and the shape
`Bridge/Core/Arms/Whnf.lean`'s `whnfLoop_spec` needs at every iteration.
The other fourteen statements below keep the explicit-argument shape for now;
each should move the day its caller is written, and the rule is: *a walk
whose subject is another walk's ANSWER must not take that answer's denotation
as an explicit argument.*

## 1. The three answer shapes, and which walk has which

`Bridge/Core/Walks/Spec.lean`'s relations, at the pure call with its fuel
abstracted:

| shape | walks |
|---|---|
| `SimOOp` — an `Option EIdx` answer | `reduceNat`, `iotaRec` |
| `SimEOp` — an `EIdx` answer | `projLitToCtor` |
| `SimBOp` — a `Bool` answer | `projCertAt`, `propIrrel`, `stuckIrrel`, `etaCert`, `defeqSpine`, `defEqList`, `isPropType` |
| `SimVOp` — any shared type | `annotPwPi`, `annotPwLam` (`PropWhen`), `headHint` (`ReducibilityHint`) |
| an EQUATION — the pure side takes no fuel | `unfoldDefinition`, `unfoldableHead`, `sameConstHeads` (and `isBoolTrue`, CLOSED in `Walks/Guards.lean`) |

**The last row is the cheap one and it is worth naming.**  Four walks of the
group (three here, `isBoolTrue` in `Walks/Guards.lean`) refine a con-leche
function that is not in `CheckM` at all
(`unfoldDefinition env e : Option Expr`, `unfoldableHead env e : Bool`,
`sameConstHeads a b : Bool`, `Expr.isBoolTrue e : Bool`), so there is no
`∃ F` and no fuel bookkeeping: the conclusion is an equation between the
arena's answer and con-leche's.  They are the first four of these to write.

## 2. What they are all waiting on, in one sentence each

Ten of the sixteen wait on an `ExprOps`-tier callee rule that this tier
does not import (`getAppFn`, `getAppArgs`, `mkAppN`, `instLPFast`,
`liftLooseBVars`, `typeSortPW`), one waits on §3's missing denotation, one on
`Bridge/Core/Walks/Cached.lean`'s `constValAt_spec` (itself waiting on
`instLPFast_spec`), one on the fuel merge (`defEqList_spec`'s note), and the
rest on nothing but the work.  The per-site notes say which.

## 3. `IProjEntry.typeAt`, and the one thing the tier is missing that is not
a proof

`IProjEntry.typeAt` cannot be STATED here, because **the projection table has
no denotation**: `Arena/Frontend/Readback.lean` has `denoteCI` for a
`IConstantInfo` and `denoteCV` for a `IConstantVal`, and nothing for an
`IProjEntry` (`Arena/Env.lean:150`, ten fields, four of them handles).  Its
`denoteProjEntry` is the one piece of *new* denotation machinery the Core
walks tier needs, and it belongs beside the other ten transports in
`Bridge/Rel.lean` — which this round does not edit.  Every `.proj` arm of
`whnfCoreBody` and `inferBody` waits on it, and so do `projCert`,
`projCertAt`'s guard and `IProjEntry.fireOk`.  **That is the tier's one
structural gap; everything else on this list is labour.**
-/
import ConRon.Bridge.Core.Walks.Spec
import ConRon.Bridge.ExprOps.Spine

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 0c. What the spine group needs and no tier had

The three walks of §1 read the head of an application, so each one is
`ExprOps/Spine.lean`'s `getAppFn_spec` over a `view`, and then the
ENVIRONMENT INDEX at the head's name.  **This is the first module of
`Bridge/Core/**` that imports the `ExprOps` tier** — task
#97-P3-CoreWalks left the three here for exactly that reason, and
`Bridge/ExprOps/**` reached zero `sorry` while the previous round ran, so
the import costs nothing and unblocks the cheap row whole.

Four facts were missing, in three groups.

1. **`viewLsLen` had no bridge to the denotation.**  Task #97-P6-10's length
   projection reads the stored record's own length and never rebuilds the
   list; nothing said that the number it answers IS the length of what the
   handle denotes.  `viewLen_of_denoteLs` is that, over two one-line
   projection equations.
2. **`denoteCI` does not change a constant's CONSTRUCTOR** — the fact task
   #97-P3-Core-2 proved at `projInfo` (`denoteCI_projInfo`), here at
   `defnInfo` and in both directions, because a walk that asks "is the head a
   DEFINITION?" needs the negative half as much as the positive one (the
   round's own rule, one rung down: *a walk that decides a guard needs the
   negative half*).
3. **The index's two halves, packaged.**  `env_defn_of_index` and
   `env_not_defn_of_index` are `IFEnvOK.hit` / `IFEnvOK.miss` plus
   `denoteN`'s functionality at one handle; every walk that reads
   `fe.find?` under a denoted name wants one of the two and neither is a
   one-liner at the site.

**And one measured finding about `simp`** that pays for itself three times
below: the match-equation lemmas of a con-leche `def` carry their negative
side conditions as hypotheses, and `simp only [ConLeche.unfoldableHead, hgf]`
DISCHARGES them from the local context.  So the "the head is not a stored
definition" arm of each of these walks is one `simp only` and no case bash —
`unfoldableHead_of_not_defn` and `headHint_of_not_defn` below are one line
each.  Where the match is on a PAIR (`sameConstHeads`) the discharger does
not fire and the arm needs `cases … <;> cases … <;> first | rfl | …`, which
is the whole difference between the two shapes. -/

theorem lsTables_getLen_eq (t : LsTables) (i : LsIdx) :
    t.getLen i = (t.get i).map List.length := by
  simp only [LsTables.getLen, LsTables.get]
  by_cases h : (i.tag == LsTag.list) = true
  · simp only [h, if_true]
    cases t.lists.node? i.idxNat <;> simp
  · simp only [Bool.not_eq_true] at h
    simp [h]

theorem lsStore_viewLen_eq (st : LsStore) (i : LsIdx) :
    st.viewLen i = (st.view i).map List.length := by
  simp only [LsStore.viewLen, LsStore.view, LsStore.persGetLen,
    lsTables_getLen_eq]
  by_cases hp : i.isPersistent = true
  · simp [hp]
  · simp only [Bool.not_eq_true] at hp
    by_cases hs : st.scratchOn = true
    · simp [hp, hs]
    · simp only [Bool.not_eq_true] at hs
      simp [hp, hs]

theorem viewLen_of_denoteLs {st : LsStore} {i : LsIdx} {us : List Level}
    (h : denoteLs st i = some us) : st.viewLen i = some us.length := by
  simp only [denoteLs] at h
  cases hv : st.view i with
  | none => rw [hv] at h; simp at h
  | some hs =>
    rw [hv] at h
    rw [lsStore_viewLen_eq, hv, Option.map_some, denoteLList_len h]

theorem denoteNList_len {st : NStore} :
    ∀ {hs : List NIdx} {xs : List ConLeche.Name},
      Frontend.denoteNList st hs = some xs → xs.length = hs.length
  | [], xs, h => by
    simp only [Frontend.denoteNList] at h
    obtain rfl := Option.some.inj h; rfl
  | a :: as, xs, h => by
    simp only [Frontend.denoteNList] at h
    cases ha : denoteN st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteNList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        simp [denoteNList_len has]

theorem denoteCI_defnInfo_inv {st : EStore} {v : IConstantVal} {e : EIdx}
    {hint : ReducibilityHint} {c : ConstantInfo}
    (h : Frontend.denoteCI st (.defnInfo v e hint) = some c) :
    ∃ cv x, Frontend.denoteCV st v = some cv ∧ denoteE st e = some x ∧
      c = .defnInfo cv x hint := by
  simp only [Frontend.denoteCI] at h
  cases hv : Frontend.denoteCV st v with
  | none => rw [hv] at h; simp at h
  | some cv =>
    cases he : denoteE st e with
    | none => rw [hv, he] at h; simp at h
    | some x =>
      rw [hv, he] at h
      exact ⟨cv, x, rfl, rfl, (Option.some.inj h).symm⟩


theorem denoteCV_inv {st : EStore} {v : IConstantVal} {c : ConstantVal}
    (h : Frontend.denoteCV st v = some c) :
    denoteN st.ns v.name = some c.name ∧
      Frontend.denoteNList st.ns v.levelParams = some c.levelParams ∧
      denoteE st v.type = some c.type := by
  simp only [Frontend.denoteCV] at h
  cases hn : denoteN st.ns v.name with
  | none => rw [hn] at h; simp at h
  | some n =>
    cases hl : Frontend.denoteNList st.ns v.levelParams with
    | none => rw [hn, hl] at h; simp at h
    | some lps =>
      cases ht : denoteE st v.type with
      | none => rw [hn, hl, ht] at h; simp at h
      | some ty =>
        rw [hn, hl, ht] at h
        obtain rfl := (Option.some.inj h).symm
        exact ⟨rfl, rfl, rfl⟩

theorem denoteCI_defn_inv {st : EStore} {ci : IConstantInfo} {cv : ConstantVal}
    {x : Expr} {hint : ReducibilityHint}
    (h : Frontend.denoteCI st ci = some (.defnInfo cv x hint)) :
    ∃ v e, ci = .defnInfo v e hint ∧ Frontend.denoteCV st v = some cv ∧
      denoteE st e = some x := by
  cases ci with
  | defnInfo v e hi =>
    obtain ⟨cv', x', hv, he, hc⟩ := denoteCI_defnInfo_inv h
    simp only [ConstantInfo.defnInfo.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact ⟨v, e, rfl, hv, he⟩
  | axiomInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hc⟩ := h; simp at hc
  | ctorInfo v nP nF =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hc⟩ := h; simp at hc
  | projInfo t =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hc⟩ := h; simp at hc
  | thmInfo v e =>
    simp only [Frontend.denoteCI] at h
    cases hv : Frontend.denoteCV st v with
    | none => rw [hv] at h; simp at h
    | some cvv =>
      cases he : denoteE st e with
      | none => rw [hv, he] at h; simp at h
      | some xx => rw [hv, he] at h; simp at h
  | indInfo v c =>
    simp only [Frontend.denoteCI] at h
    cases hv : Frontend.denoteCV st v with
    | none => rw [hv] at h; simp at h
    | some cvv =>
      cases hc : Frontend.denoteCaps st c with
      | none => rw [hv, hc] at h; simp at h
      | some cc => rw [hv, hc] at h; simp at h
  | recInfo v mI rP rs =>
    simp only [Frontend.denoteCI] at h
    cases hv : Frontend.denoteCV st v with
    | none => rw [hv] at h; simp at h
    | some cvv =>
      cases hr : Frontend.denoteRules st rs with
      | none => rw [hv, hr] at h; simp at h
      | some rr => rw [hv, hr] at h; simp at h

theorem denote_not_const {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} {v : ENodeView} (hv : st.view h = some v)
    (he : denoteE st h = some e)
    (hne : ∀ c us, v ≠ .const c us) : ∀ n us, e ≠ .const n us := by
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv he]; simp
  | fvar k t => obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv he; simp
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv he; simp
  | const n us => exact absurd rfl (hne n us)
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv he; simp
  | lam ty b m => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; simp
  | forallE ty b m =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv he; simp
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv he; simp
  | lit l => rw [denote_lit_inv hwf hv he]; simp
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv he; simp

theorem env_defn_of_index {s : AState} (hok : CheckOK mode env fe s)
    {c : NIdx} {nm : ConLeche.Name} {icv : IConstantVal} {value : EIdx}
    {hint : ReducibilityHint} (hn : denoteN s.store.ns c = some nm)
    (hfd : fe.find? c = some (.defnInfo icv value hint)) :
    ∃ dcv dval, Frontend.denoteCV s.store icv = some dcv ∧
      denoteE s.store value = some dval ∧
      env.find? nm = some (.defnInfo dcv dval hint) := by
  obtain ⟨nm', cc, hn', hci, hfind⟩ := hok.ienv.hit c _ hfd
  obtain rfl := Option.some.inj (hn'.symm.trans hn)
  obtain ⟨dcv, dval, hdcv, hdval, rfl⟩ := denoteCI_defnInfo_inv hci
  exact ⟨dcv, dval, hdcv, hdval, hfind⟩

theorem env_not_defn_of_index {s : AState} (hok : CheckOK mode env fe s)
    {c : NIdx} {nm : ConLeche.Name} (hn : denoteN s.store.ns c = some nm)
    (hnd : ∀ cv value hint, fe.find? c ≠ some (.defnInfo cv value hint)) :
    ∀ cv val hint, env.find? nm ≠ some (.defnInfo cv val hint) := by
  intro dcv dval dh hcon
  cases hf : fe.find? c with
  | none => rw [IFEnvOK.miss hok.state hok.ienv hn hf] at hcon; simp at hcon
  | some ci =>
    obtain ⟨nm', cc, hn', hci, hfind⟩ := hok.ienv.hit c ci hf
    obtain rfl := Option.some.inj (hn'.symm.trans hn)
    rw [hfind] at hcon
    obtain rfl := Option.some.inj hcon
    obtain ⟨v', e', rfl, _, _⟩ := denoteCI_defn_inv hci
    exact hnd v' e' dh hf


theorem unfoldableHead_of_not_defn {env : Env} {nm : ConLeche.Name} {x : Expr}
    {ls : List Level} (hgf : x.getAppFn = .const nm ls)
    (h : ∀ cv val hint, env.find? nm ≠ some (.defnInfo cv val hint)) :
    ConLeche.unfoldableHead env x = false := by
  simp only [ConLeche.unfoldableHead, hgf]

theorem unfoldableHead_of_not_const {env : Env} {x : Expr}
    (h : ∀ n us, x.getAppFn ≠ .const n us) :
    ConLeche.unfoldableHead env x = false := by
  simp only [ConLeche.unfoldableHead]

/-! ## 1. The three with an unfueled pure side

con-leche's comparand is a plain function of the environment, so the
conclusion is an equation and there is no fuel existential anywhere in the
statement.  These are the cheapest walks of the tier — their fourth,
`isBoolTrue`, is CLOSED in `Bridge/Core/Walks/Guards.lean`, and the three
here differ from it only by needing `getAppFn`.  **All three are CLOSED**
(task #97-P3-Core round 3), which is what the `ExprOps` import buys. -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:157-170 unfoldableHead —
**THEOREM 1 for `unfoldableHead`**: the delta step's DECISION, taken before
the unfolding is materialized.  **CLOSED** (round 3): six verification
conditions — `getAppFn_spec`'s two preconditions, the dangling-level-list
failure arm (free), the definition arm, the not-a-definition arm and the
not-a-constant arm. -/
theorem unfoldableHead_spec (s₀ : AState) (e : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store e = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.unfoldableHead fe e
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.unfoldableHead env x⌝⦄ := by
  have hfn := ExprOps.getAppFn_spec coreWalkFuel
  obtain ⟨rk, hrk⟩ := hok.state.wf
  mvcgen [ConRon.Arena.unfoldableHead, hfn]
  case vc1 => bridge_peel; subst_vars; exact hok.state
  case vc2 => bridge_peel; subst_vars; rw [hden]; rfl
  case vc3 => intro hf; exact False.elim hf
  case vc4 =>
    bridge_peel; subst_vars
    rename_i r c us icv value hint hfd usl s hlen hview hrel
    refine ⟨hok, rfl, rfl, ?_⟩
    obtain ⟨nm, ls, hgf, hn, hus⟩ :=
      denote_const_inv hok.state.wf hview (hrel x hden)
    obtain ⟨dcv, dval, hdcv, _, hfind⟩ := env_defn_of_index hok hn hfd
    have hul : usl = ls.length := by
      rw [viewLen_of_denoteLs hus] at hlen; exact Option.some.inj hlen
    obtain ⟨_, hlps, _⟩ := denoteCV_inv hdcv
    simp only [ConLeche.unfoldableHead, hgf, hfind, hul,
      denoteNList_len hlps]
  case vc5 =>
    bridge_peel; subst_vars
    rename_i r c us s hview hrel hnd
    refine ⟨hok, rfl, rfl, ?_⟩
    obtain ⟨nm, ls, hgf, hn, hus⟩ :=
      denote_const_inv hok.state.wf hview (hrel x hden)
    exact (unfoldableHead_of_not_defn hgf (env_not_defn_of_index hok hn hnd)).symm
  case vc6 =>
    bridge_peel; subst_vars
    rename_i r v hnc s hview hrel
    refine ⟨hok, rfl, rfl, ?_⟩
    exact (unfoldableHead_of_not_const
      (denote_not_const hok.state.wf hview (hrel x hden) hnc)).symm

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:172-181 headHint — **THEOREM 1
for `headHint`**: the reducibility hint of the constant at the head.
**CLOSED** (round 3).  The answer type is one both tiers share, so the
relation is `SimVOp`'s — here spelled as the equation it is, because
con-leche's `headHint` takes no fuel.  It is `unfoldableHead` minus the
level-list read: five verification conditions and the same three arms. -/
theorem headHint_of_not_defn {env : Env} {nm : ConLeche.Name} {x : Expr}
    {ls : List Level} (hgf : x.getAppFn = .const nm ls)
    (h : ∀ cv val hint, env.find? nm ≠ some (.defnInfo cv val hint)) :
    ConLeche.headHint env x = .opaque := by
  simp only [ConLeche.headHint, hgf]

theorem headHint_of_not_const {env : Env} {x : Expr}
    (h : ∀ n us, x.getAppFn ≠ .const n us) :
    ConLeche.headHint env x = .opaque := by
  simp only [ConLeche.headHint]

theorem headHint_spec (s₀ : AState) (e : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store e = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.headHint fe e
    ⦃⇓? h s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ h = ConLeche.headHint env x⌝⦄ := by
  have hfn := ExprOps.getAppFn_spec coreWalkFuel
  obtain ⟨rk, hrk⟩ := hok.state.wf
  mvcgen [ConRon.Arena.headHint, hfn]
  case vc1 => bridge_peel; subst_vars; exact hok.state
  case vc2 => bridge_peel; subst_vars; rw [hden]; rfl
  case vc3 =>
    bridge_peel; subst_vars
    rename_i r c us icv value hint hfd s hview hrel
    refine ⟨hok, rfl, rfl, ?_⟩
    obtain ⟨nm, ls, hgf, hn, _⟩ :=
      denote_const_inv hok.state.wf hview (hrel x hden)
    obtain ⟨dcv, dval, _, _, hfind⟩ := env_defn_of_index hok hn hfd
    simp only [ConLeche.headHint, hgf, hfind]
  case vc4 =>
    bridge_peel; subst_vars
    rename_i r c us s hview hrel hnd
    refine ⟨hok, rfl, rfl, ?_⟩
    obtain ⟨nm, ls, hgf, hn, _⟩ :=
      denote_const_inv hok.state.wf hview (hrel x hden)
    exact (headHint_of_not_defn hgf (env_not_defn_of_index hok hn hnd)).symm
  case vc5 =>
    bridge_peel; subst_vars
    rename_i r v hnc s hview hrel
    refine ⟨hok, rfl, rfl, ?_⟩
    exact (headHint_of_not_const
      (denote_not_const hok.state.wf hview (hrel x hden) hnc)).symm

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:183-192 sameConstHeads —
**THEOREM 1 for `sameConstHeads`**: the lazy-delta same-head short-circuit.
**CLOSED** (round 3), and it is DESIGN §8.3's *"index inequality IS
structural inequality"* at the NAME store: `beq_of_denoteN` turns the
arena's `==` on `NIdx` into con-leche's `==` on `Name`, in both directions
(`denoteN`'s functionality one way, `denoteN_inj` the other).  Nine
verification conditions, the most of the three, because the walk peels two
subjects. -/
theorem denote_not_app {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} {v : ENodeView} (hv : st.view h = some v)
    (he : denoteE st h = some e)
    (hne : ∀ f a, v ≠ .app f a) : ∀ f a, e ≠ .app f a := by
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv he]; simp
  | fvar k t => obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv he; simp
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv he; simp
  | const n us => obtain ⟨p, q, rfl, _, _⟩ := denote_const_inv hwf hv he; simp
  | app f a => exact absurd rfl (hne f a)
  | lam ty b m => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; simp
  | forallE ty b m =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv he; simp
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv he; simp
  | lit l => rw [denote_lit_inv hwf hv he]; simp
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv he; simp

theorem beq_of_denoteN {st : NStore} (hwf : NStoreWF st) {n₁ n₂ : NIdx}
    {nm₁ nm₂ : ConLeche.Name} (h1 : denoteN st n₁ = some nm₁)
    (h2 : denoteN st n₂ = some nm₂) : (n₁ == n₂) = (nm₁ == nm₂) := by
  by_cases h : n₁ = n₂
  · subst h
    rw [h1] at h2
    obtain rfl := Option.some.inj h2
    simp
  · have hne : nm₁ ≠ nm₂ := fun hc => h (denoteN_inj hwf h1 (hc ▸ h2))
    have e1 : (n₁ == n₂) = false := by simp only [beq_eq_false_iff_ne]; exact h
    have e2 : (nm₁ == nm₂) = false := by
      simp only [beq_eq_false_iff_ne]; exact hne
    rw [e1, e2]

theorem sameConstHeads_spec (s₀ : AState) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.sameConstHeads a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.sameConstHeads x y⌝⦄ := by
  have hfn := ExprOps.getAppFn_spec coreWalkFuel
  obtain ⟨rk, hrk⟩ := hok.state.wf
  mvcgen [ConRon.Arena.sameConstHeads, hfn]
  case vc1 => bridge_peel; subst_vars; exact hok.state
  case vc2 =>
    bridge_peel; subst_vars
    rename_i fa aa fb ab s hvb hva
    obtain ⟨ex, ea, hx, hdf, _⟩ := denote_app_inv hok.state.wf hva hda
    rw [hdf]; rfl
  case vc3 => bridge_peel; subst_vars; exact hok.state
  case vc4 =>
    bridge_peel; subst_vars
    rename_i fa aa fb ab ra ca usa s hvra hrela hvb hva
    obtain ⟨ey, eb, hy, hdf, _⟩ := denote_app_inv hok.state.wf hvb hdb
    rw [hdf]; rfl
  case vc5 =>
    bridge_peel; subst_vars
    rename_i fa aa fb ab ra ca usa rb cb usb s hvrb hrelb hvra hrela hvb hva
    obtain ⟨ex, ea, rfl, hdfa, _⟩ := denote_app_inv hok.state.wf hva hda
    obtain ⟨ey, eb, rfl, hdfb, _⟩ := denote_app_inv hok.state.wf hvb hdb
    obtain ⟨nma, lsa, hgfa, hna, _⟩ :=
      denote_const_inv hok.state.wf hvra (hrela ex hdfa)
    obtain ⟨nmb, lsb, hgfb, hnb, _⟩ :=
      denote_const_inv hok.state.wf hvrb (hrelb ey hdfb)
    refine ⟨hok, rfl, rfl, ?_⟩
    rw [beq_of_denoteN hrk.nsWF hna hnb]
    simp only [ConLeche.sameConstHeads, hgfa, hgfb]
  case vc6 =>
    bridge_peel; subst_vars
    rename_i fa aa fb ab ra ca usa rb vb hncb s hvrb hrelb hvra hrela hvb hva
    obtain ⟨ex, ea, rfl, hdfa, _⟩ := denote_app_inv hok.state.wf hva hda
    obtain ⟨ey, eb, rfl, hdfb, _⟩ := denote_app_inv hok.state.wf hvb hdb
    have hnc := denote_not_const hok.state.wf hvrb (hrelb ey hdfb) hncb
    refine ⟨hok, rfl, rfl, ?_⟩
    simp only [ConLeche.sameConstHeads]
    cases hgx : ex.getAppFn <;> cases hgy : ey.getAppFn <;>
      first | rfl | exact absurd hgy (hnc _ _)
  case vc7 =>
    bridge_peel; subst_vars
    rename_i fa aa fb ab ra va hnca s hvra hrela hvb hva
    obtain ⟨ex, ea, rfl, hdfa, _⟩ := denote_app_inv hok.state.wf hva hda
    obtain ⟨ey, eb, rfl, hdfb, _⟩ := denote_app_inv hok.state.wf hvb hdb
    have hnc := denote_not_const hok.state.wf hvra (hrela ex hdfa) hnca
    refine ⟨hok, rfl, rfl, ?_⟩
    simp only [ConLeche.sameConstHeads]
    cases hgx : ex.getAppFn <;> cases hgy : ey.getAppFn <;>
      first | rfl | exact absurd hgx (hnc _ _)
  case vc8 =>
    bridge_peel; subst_vars
    rename_i fa aa vb hnab s hvb hva
    obtain ⟨ex, ea, rfl, hdfa, _⟩ := denote_app_inv hok.state.wf hva hda
    have hna := denote_not_app hok.state.wf hvb hdb hnab
    refine ⟨hok, rfl, rfl, ?_⟩
    simp only [ConLeche.sameConstHeads]
    cases hy : y <;> first | rfl | exact absurd hy (hna _ _)
  case vc9 =>
    bridge_peel; subst_vars
    rename_i va hnaa s hva
    have hna := denote_not_app hok.state.wf hva hda hnaa
    refine ⟨hok, rfl, rfl, ?_⟩
    simp only [ConLeche.sameConstHeads]
    cases hx : x <;> cases hy : y <;> first | rfl | exact absurd hx (hna _ _)

/-! `isBoolTrue` was the fourth of this group and is **CLOSED** —
`Bridge/Core/Walks/Guards.lean`.  It was the cheapest of the seventeen (five
verification conditions, no `ExprOps` rule, no new denotation), and closing
it is this round's evidence that the row above really is the cheap one. -/

/-! ## 2. The delta step and the literal acceleration

`whnfStep`'s two callees (`Bridge/Core/Arms/Whnf.lean`'s `whnfLoop_delta`
and `whnfLoop_reduceNat` are their pure-side step lemmas, and both are
closed), which is why `whnfBody_spec` — the most reachable of the six body
walks — is still open. -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:136-155 unfoldDefinition —
**THEOREM 1 for `unfoldDefinition`**: unfold the (application of a)
definition at the head, one step.  The pure side takes no fuel, so the
conclusion is an equation through `denoteEO` (`Bridge/Rel.lean`).

**OPEN**: three callee rules — `getAppFn_spec`, `getAppArgs_spec` and
`mkAppN_spec` (all closed in `Bridge/ExprOps/Spine.lean`) — plus
`Bridge/Core/Walks/Cached.lean`'s `constValAt_spec`, which is itself waiting
on `ExprOps.instLPFast_spec`.  **This is the deepest chain on the list**, and
it is the reason `whnfBody_spec` cannot close before the `ExprOps` tier
does. -/
theorem unfoldDefinition_spec (s₀ : AState) (d : Nat) (e : EIdx)
    (hok : CheckOK mode env fe s₀)
    (hdw : ∃ x, denoteE s₀.store e = some x ∧ Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.unfoldDefinition fe e
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ x, denoteE s₀.store e = some x →
          denoteEO s'.store r = some (ConLeche.unfoldDefinition env x) ∧
          ∀ y, ConLeche.unfoldDefinition env x = some y →
            Expr.WScoped d y⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat — **THEOREM 1 for
`reduceNat`**: the literal acceleration, run in the `whnf` loop before
delta-unfolding.  The divergence audit's D15 is preserved by the twin (the
FIRST argument is head-normalised and, unless it is a literal, the step fails
without touching the second), so the two sides' CALL SEQUENCES agree and the
proof is a straight walk.

**OPEN**: `KnotSpec.whnf` at the two arguments (available), plus callee rules
for `rawNatLit?`, `natLitSupported`, `natOpStored`, `natBinOpName` and
`natOpResult` — five `Arena/Core.lean` walks of the state-only group that
this round did not reach either.  Nothing in it needs the `ExprOps`
tier. -/
theorem reduceNat_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (e : EIdx) (hok : CheckOK mode env fe s₀)
    (hdw : ∃ x, denoteE s₀.store e = some x ∧ Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.reduceNat (coreKnot mode fe id fuel) fe d e
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ x, denoteE s₀.store e = some x →
          SimOOp (fun F => ConLeche.reduceNatFueled mode env F d x) d
            s'.store r⌝⦄ := by
  sorry

/-! ## 3. The ι step and the projection rule

`whnfCoreBody`'s `.app` and `.proj` clauses' callees. -/

/-- con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec — **THEOREM 1 for
`iotaRec`**: one ι step at a recursor application, with the stuck-major
machinery under it.

**OPEN, and the largest single item of the tier**: `Arena/Core.lean`'s
`iotaRec` is `iotaRecAt` over `findRule`, and `iotaRecAt` is 85 lines over
`prepareMajor` (120 lines of `majorToCtor`), `recFireComparands`,
`ruleRhsAt` and `iotaCerts`.  Six knot-calling walks under one statement;
the corresponding con-leche tower is `Verify/Iota*.lean`.  Its `ruleRhsAt`
leg waits on `ExprOps.instLPFast_spec` like the other two instantiated
caches. -/
theorem iotaRec_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (e : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store e = some x)
    (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.iotaRec mode (coreKnot mode fe id fuel) fe d e
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimOOp (fun F => ConLeche.iotaRecFueled mode env F d x) d
          s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:742-756 projLitToCtor — **THEOREM 1
for `projLitToCtor`**: a string-literal scrutinee expands to its reduced
constructor form before the projection table is consulted.

**OPEN**: `strLitSupported`, `strLitToConstructor` and `litMajorToCtor` as
callee rules, plus `KnotSpec.whnf`.  `strLitToConstructor` builds a cons
spine in the store, so its rule is the first in this tier whose
postcondition is a genuine `Ext` rather than a store equation. -/
theorem projLitToCtor_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (h : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store h = some x)
    (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.projLitToCtor (coreKnot mode fe id fuel) fe d h
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimEOp (fun F => ConLeche.projLitToCtorFueled mode env F d x) d
          s'.store r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:949-961 projCertAt — **THEOREM 1 for
`projCertAt`**: the fire certificate of a projection, gated on
`mode.verifiedChecks`.

**OPEN**: the `verified = false` arm is `pure true` on both sides and is
free; the `true` arm is `projCert`, which reads the projection table and
therefore waits on §3's `denoteProjEntry`.  The argument list's denotation is
`Frontend.denoteEList`, which `Bridge/Rel.lean` already has. -/
theorem projCertAt_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (verified lic : Bool) (c : NIdx) (us : LsIdx)
    (args : List EIdx) (cn : ConLeche.Name) (ls : List Level)
    (xs : List Expr) (hok : CheckOK mode env fe s₀)
    (hc : denoteN s₀.store.ns c = some cn)
    (hus : denoteLs s₀.store.lss us = some ls)
    (hargs : Frontend.denoteEList s₀.store args = some xs) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.projCertAt (coreKnot mode fe id fuel) fe d verified lic c
        us args
    ⦃⇓? b s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp
          (fun F => ConLeche.projCertAtFueled mode env F d verified lic cn ls
            xs) b⌝⦄ := by
  sorry

/-! ## 4. The `defeq` body's five certificate walks

`Bridge/Core/Arms/Defeq.lean`'s `defeqBody_spec` names exactly these five as
the callee rules it is missing. -/

/-- con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel — **THEOREM 1 for
`propIrrel`**, the hoisted proof-irrelevance test.

**OPEN**: `notProofFast` as a callee rule (an `IFEnvOK` consequence over the
derived word), then `KnotSpec.inferIO` at both subjects and `KnotSpec.defeq`
at their types. -/
theorem propIrrel_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.propIrrel (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.propIrrelFueled mode env F d x y) r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel — **THEOREM 1 for
`stuckIrrel`**, the fallback at two stuck terms: structure-η in both
directions, then the unit certificate.

**OPEN**: `structEtaCert` and `structUnitCert` as callee rules, which are two
more knot-calling walks (`structEtaCertWith` is 70 lines and sits under
both). -/
theorem stuckIrrel_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.stuckIrrel mode (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.stuckIrrelFueled mode env F d x y) r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:505-530 etaCert — **THEOREM 1 for
`etaCert`**: η at a λ against a non-λ.

**OPEN**: the rebuild is `internE (.app (lift b) (.bvar 0))` under a binder,
so it needs `ExprOps.liftLooseBVars`'s spec (closed in
`Bridge/ExprOps/Subst.lean`) and `KnotSpec.defeq` one depth down.  The
statement's FOUR subjects are the λ's two children, its binder datum and the
comparand — `Bridge/Rel.lean`'s `RelE.lam` shape, at the level of a whole
walk. -/
theorem etaCert_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (ty₁ body₁ b : EIdx) (m₁ : BinderMeta)
    (t x y : Expr) (hok : CheckOK mode env fe s₀)
    (hdt : denoteE s₀.store ty₁ = some t)
    (hdx : denoteE s₀.store body₁ = some x)
    (hdy : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d (.lam t x m₁)) (hwb : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.etaCert mode (coreKnot mode fe id fuel) fe d ty₁ body₁ m₁ b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.etaCertFueled mode env F d t x m₁ y)
          r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1420-1439 defeqSpine — **THEOREM 1
for `defeqSpine`**: two applications of the same constant are defeq if their
universe arguments and their argument vectors are.

**OPEN**: `getAppFn_spec`/`getAppArgs_spec` (`ExprOps` tier), `lvlsEq?_spec`
(CLOSED, `Bridge/Core/Walks/Cached.lean`) and `defEqList_spec` below.  Three
of the four are in hand, which makes this the most nearly reachable of the
five. -/
theorem defeqSpine_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d x) (hwb : Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.defeqSpine (coreKnot mode fe id fuel) fe d a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.defeqSpineFueled mode env F d x y) r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList — **THEOREM 1 for
`defEqList`**: pairwise definitional equality of two argument vectors.

**OPEN**: a `List` induction over `KnotSpec.defeq` — no `ExprOps` rule and no
new denotation — **plus the fuel merge**.  The two subjects are LISTS, so
task #97-P3-0's finding 3 applies: they are quantified inside the relation
(here, by `Frontend.denoteEList` hypotheses at the entry) rather than taken
as `∀`s a recursive call would leave as metavariables.

**The fuel merge is the tier's one unpriced line item** (DESIGN §8's
`### Task #97-P3-CoreWalks` §6.1).  Task #97-P3-Core said con-leche's
`FueledM` wrapper is not needed here because the arena's side is a triple;
that is true of a BODY and false of a LOOP.  Each iteration of this
recursion hands out its own `∃ F` and they have to become one, which is
`Verify/Mono.lean`'s job — and con-leche has `isDefEqCore_mono` and
`pureFns_mono` but no `defEqList_mono`, because `FueledM` did its merging
for it.  Ten lines in `Verify/Mono.lean`'s own shape, owed by the bridge,
and the same debt sits unpaid under `whnfBody_spec`'s loop. -/
theorem defEqList_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (as bs : List EIdx) (xs ys : List Expr)
    (hok : CheckOK mode env fe s₀)
    (hda : Frontend.denoteEList s₀.store as = some xs)
    (hdb : Frontend.denoteEList s₀.store bs = some ys)
    (hwa : ∀ x ∈ xs, Expr.WScoped d x) (hwb : ∀ y ∈ ys, Expr.WScoped d y) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.defEqList (coreKnot mode fe id fuel) fe d as bs
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.defEqListFueled mode env F d xs ys)
          r⌝⦄ := by
  sorry

/-! ## 5. The annotation pass's three

`Bridge/Core/Arms/Annotate.lean`'s `annotateBody_spec` names `annotPwPi` and
`annotPwLam`; `isPropType` is under both. -/

/-- con-leche: ConLeche/Kernel/Core.lean:1721-1730 isPropType — **THEOREM 1
for `isPropType`**: is the annotated type a proposition?

**OPEN**: `KnotSpec.annotate` (available) then the head-symbol reader
`typeSortPW`, which is an `ExprOps` walk (`Bridge/ExprOps/Walks.lean`'s
group, closed) this tier does not import. -/
theorem isPropType_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (ty : EIdx) (t : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store ty = some t)
    (hw : Expr.WScoped d t) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.isPropType (coreKnot mode fe id fuel) fe d ty
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp
          (fun F => ConLeche.isPropType (ConLeche.pureFns mode env F) env d t)
          r⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1746-1777 annotPwPi — **THEOREM 1
for `annotPwPi`**: the `PropWhen` datum a ∀ binder is stamped with.

**OPEN**: `isPropType_spec` above, plus the head-symbol reader `forallPw`
(`ExprOps` tier).  `PropWhen` is a type both tiers share, so the answer
relation is `SimVOp` and nothing has to be denoted. -/
theorem annotPwPi_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (body' : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store body' = some x)
    (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.annotPwPi (coreKnot mode fe id fuel) fe d body'
    ⦃⇓? pw s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimVOp
          (fun F => ConLeche.annotPwPi (ConLeche.pureFns mode env F) env d x)
          pw⌝⦄ := by
  sorry

/-- con-leche: ConLeche/Kernel/Core.lean:1779-1793 annotPwLam — **THEOREM 1
for `annotPwLam`**: the same at a λ binder.

**OPEN**: `isPropType_spec` and the `lamPw` reader. -/
theorem annotPwLam_spec {fuel : Nat} (hsim : KnotSpec mode env fe fuel)
    (s₀ : AState) (d : Nat) (body' : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store body' = some x)
    (hw : Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄
      ConRon.Arena.annotPwLam (coreKnot mode fe id fuel) fe d body'
    ⦃⇓? pw s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimVOp
          (fun F => ConLeche.annotPwLam (ConLeche.pureFns mode env F) env d x)
          pw⌝⦄ := by
  sorry

end ConRon.Bridge.Core

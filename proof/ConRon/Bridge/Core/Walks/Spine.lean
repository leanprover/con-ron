/-
# `ConRon.Bridge.Core.Walks.Spine` — the non-slot walks that cannot sit on the knot-facing chain

Task #97-P3-Core round 3.  `Bridge/Core/Walks/Owed.lean` left four walks with
one note between them — *"no import of the `ExprOps` tier is made by
`Bridge/Core/Walks/**` this round, which is the only reason this is not
proved here"* — and `Bridge/ExprOps/**` reached zero `sorry` while round 2
ran.  **All four are closed here**: `unfoldableHead`, `headHint`,
`sameConstHeads` and `defeqSpine`, on `ExprOps/Spine.lean`'s `getAppFn_spec`
and `getAppArgs_spec`.

## Why this is a module of its own and not four theorems in `Owed.lean`

`lakefile.toml`'s `ConRonBridge` entry: *"Two modules of the `ExprOps` tier
cannot sit in ONE import closure — `grind` generates the same
`match`-auxiliary for an `Arena/ExprOps.lean` definition in each, and Lean
refuses the second."*  **The same clash reaches the Core tier through the
`ExprOps` import**, and it was found by building, not by reading:

    import ConRon.Bridge.Core.EnsureSort failed, environment already contains
    'ConRon.Arena.piResultIsProp.match_1.congr_eq_1._sparseCasesOn_2'
    from ConRon.Bridge.Core.Walks.Owed

`Bridge/Checker/Hyp.lean` imports `Core.EnsureSort` beside `Core.Induction`,
and `Core.Induction` reaches `Walks/Owed.lean` through the six `Arms/`
modules.  So the moment `Owed.lean` imports `ExprOps/Spine.lean`, the Checker
tier cannot be built — the derived congruence auxiliary of the `ENodeView`
match is generated in `EnsureSort.lean` and in the `ExprOps` closure, and the
two oleans both carry it.

The rule the round takes from it: **`Bridge/Core/**`'s knot-facing chain
(`Knot → Memo → Arms/* → Induction`) stays free of the `ExprOps` tier and of
`mvcgen` over `ensureSort`, and the walks that need either live in SIBLING
modules off it.**  A body walk that eventually needs one of these will
import this module beside `Owed.lean`; nothing on the chain has to.

**And this module is a workaround, not a fix.**  `Arena/Core.lean` calls
`ensureSort` from `inferBodyIO`'s `.forallE` arm, from `annotateBody` and
from `inferLamsLeafCheck`, so `Arms/{InferIO,Annotate,Infer}.lean` meet the
same wall the day those arms are written — and all three are ON the chain.
The auxiliary is *derived on demand*, so the real repair is to give it one
owner (force its derivation in `Bridge/Specs.lean`, which every module of
this library imports); DESIGN §8's `### Task #97-P3-Core-2` round 3
finding 18 books it.

## What is in here besides the four walks

The facts the four need and no tier had — the length projection of `viewLs`
bridged to the denotation, `denoteCI`'s constructor preservation at
`defnInfo` in both directions, the environment index's two halves packaged,
and the two "index equality IS structural equality" transfers at the name
store.  Their section notes are below.

One thing is here for the IMPORT's sake rather than the subject's:
`instantiate1Fast_specE`, which is `ExprOps/Inst1.lean`'s spec in answer
shape and is what `etaCert_spec` (open when this was written, closed since)
needed.  (`isPropType_spec` was the other; con-leche deleted `isPropType`,
task #105.)
-/
import ConRon.Bridge.Core.Walks.Owed
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.ExprOps.Spine

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
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

/-- con-leche: none — the LENGTH projection of one tier's `LsTables.get`:
the stored record's own length is the length of the list the handle decodes to
in that tier.  Task #97-P6-10 wrote the projection and nothing related it to
the list. -/
theorem lsTables_getLen_eq (t : LsTables) (i : LsIdx) :
    t.getLen i = (t.get i).map List.length := by
  simp only [LsTables.getLen, LsTables.get]
  by_cases h : (i.tag == LsTag.list) = true
  · simp only [h, ite_true]
    cases t.lists.node? i.idxNat <;> simp
  · simp only [Bool.not_eq_true] at h
    simp [h]

/-- con-leche: none — the same at the two-tier `LsStore`: one `if` chain
over the other. -/
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

/-- con-leche: none — **the length projection agrees with the
DENOTATION**: a level-list handle that denotes `us` answers `us.length`.  This
is what a walk comparing `viewLsLen` against con-leche's `us.length` needs and
what no tier had. -/
theorem viewLen_of_denoteLs {st : LsStore} {i : LsIdx} {us : List Level}
    (h : denoteLs st i = some us) : st.viewLen i = some us.length := by
  simp only [denoteLs] at h
  cases hv : st.view i with
  | none => rw [hv] at h; simp at h
  | some hs =>
    rw [hv] at h
    rw [lsStore_viewLen_eq, hv, Option.map_some, denoteLList_len h]

/-- con-leche: none — the same at the full VIEW: a level-list handle that
denotes `us` views as a list of `us.length` handles (`unfoldDefinition`
compares the view's length, not `viewLsLen`'s). -/
theorem view_len_of_denoteLs {st : LsStore} {i : LsIdx} {us : List Level}
    {v : LsNodeView} (h : denoteLs st i = some us) (hv : st.view i = some v) :
    v.length = us.length := by
  have hl := viewLen_of_denoteLs h
  rw [lsStore_viewLen_eq, hv, Option.map_some] at hl
  exact Option.some.inj hl

/-- con-leche: none — a denoting NAME-handle list keeps its length.
`Bridge/Rel.lean` has this at expression and level handles
(`denoteEList_len`, `denoteLList_len`) and not at names. -/
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

/-- con-leche: none — the denotation of a stored DEFINITION is a
definition, with the same reducibility hint and a denoting value. -/
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


/-! `denoteCV_inv` — the field-by-field inversion of `denoteCV` — moved down
to `Bridge/Core/Walks/Cached.lean` in round 4, where the three
instantiated-constant caches need it. -/

/-- con-leche: none — **and the other direction**: a stored constant that
DENOTES a definition IS one.  DESIGN §8.3's "the denotation does not change a
constant's constructor" (task #97-P3-Core-2 proved it at `projInfo`), here at
`defnInfo` — and this is the half a walk that decides "is the head
unfoldable?" needs, because it decides a GUARD. -/
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

/-- con-leche: none — a handle whose VIEW is not a `.const` denotes an
expression that is not a `.const`.  `Bridge/Core/Walks/Guards.lean`'s
`isBoolTrue_of_not_const` with the conclusion left general. -/
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

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the index's HIT
half at a definition**: a handle the index answers `defnInfo` at denotes a
name the environment answers `defnInfo` at, with the same hint. -/
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

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — **the index's MISS
half**, which is `IFEnvOK.miss` at a `find?` miss and `denoteCI_defn_inv` at a
hit on something that is not a definition.  A walk that decides whether the
head unfolds needs exactly this. -/
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


/-- con-leche: ConLeche/Kernel/CoreDefs.lean:157-170 unfoldableHead — the
negative arm, in ONE `simp only`: a con-leche `def`'s match-equation lemma
carries its negative side condition as a hypothesis and `simp` discharges it
from the local context.  (The round's measured finding; see §0c.) -/
theorem unfoldableHead_of_not_defn {env : Env} {nm : ConLeche.Name} {x : Expr}
    {ls : List Level} (hgf : x.getAppFn = .const nm ls)
    (h : ∀ cv val hint, env.find? nm ≠ some (.defnInfo cv val hint)) :
    ConLeche.unfoldableHead env x = false := by
  simp only [ConLeche.unfoldableHead, hgf]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:157-170 unfoldableHead — the
same at the outer match. -/
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
  to_wp; vcgen [ConRon.Arena.unfoldableHead, wp% hfn]
  all_goals (bridge_peel; subst_vars)
  -- `getAppFn_spec`'s two preconditions
  case vc5 => exact hok.state
  case vc6 => rw [hden]; rfl
  -- the definition arm
  case vc1 =>
    rename_i _ _ _ _ _ _ hfd _ usl hrel hview hlen
    refine ⟨hok, rfl, rfl, ?_⟩
    obtain ⟨nm, ls, hgf, hn, hus⟩ :=
      denote_const_inv hok.state.wf hview (hrel x hden)
    obtain ⟨dcv, dval, hdcv, _, hfind⟩ := env_defn_of_index hok hn hfd
    have hul : usl = ls.length := by
      rw [viewLen_of_denoteLs hus] at hlen; exact Option.some.inj hlen
    obtain ⟨_, hlps, _⟩ := denoteCV_inv hdcv
    simp only [ConLeche.unfoldableHead, hgf, hfind, hul,
      denoteNList_len hlps]
  -- the not-a-definition arm
  case vc2 =>
    rename_i _ _ _ _ hrel hview hnd
    refine ⟨hok, rfl, rfl, ?_⟩
    obtain ⟨nm, ls, hgf, hn, hus⟩ :=
      denote_const_inv hok.state.wf hview (hrel x hden)
    exact (unfoldableHead_of_not_defn hgf (env_not_defn_of_index hok hn hnd)).symm
  -- the not-a-constant arm
  case vc3 =>
    rename_i _ _ _ hnc hrel hview
    refine ⟨hok, rfl, rfl, ?_⟩
    exact (unfoldableHead_of_not_const
      (denote_not_const hok.state.wf hview (hrel x hden) hnc)).symm
  -- the tag-first `else` arm (task #97-P5-Core round 4): the head's view comes
  -- back from its denotation, and its tag is not `const`
  case vc4 =>
    have hr := (‹RelE Expr.getAppFn _ e _ _›) x hden
    obtain ⟨v, hv⟩ := denoteE_view hr
    refine ⟨hok, rfl, rfl, ?_⟩
    exact (unfoldableHead_of_not_const (denote_not_const hok.state.wf hv hr
      (fun c us hh => view_tagOf_ne hv (t := ETag.const) ‹_› (by rw [hh]; rfl)))).symm

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:136-155 unfoldDefinition —
**THEOREM 1 for `unfoldDefinition`**: unfold the (application of a)
definition at the head, one step.  The pure side takes no fuel, so the
conclusion is an equation through `denoteEO` (`Bridge/Rel.lean`).

**CLOSED** (round 4), and it moved here from `Walks/Owed.lean`: the spine
rules are the `ExprOps` tier's, the index facts are this module's, and the
delta step's value is `Walks/Cached.lean`'s `constValAt_spec'` — the ANSWER
shape, because the constant's name and levels come out of `getAppFn`/`view`.

**One precondition was missing and is repaired: `EnvWF env`.**  The
postcondition promises the unfolding is well-scoped at `d`, and that is
con-leche's `unfoldDefinition_WScoped` — whose own hypothesis is exactly
`EnvWF` (the stored VALUE is closed).  Without it the statement is false: a
definition whose stored value has a loose bound variable unfolds, in both
tiers, to a term that is not well-scoped, and nothing in `CheckOK` rules such
an environment out.  Its one caller, `Arms/Whnf.lean`'s `whnfBody_spec`,
already took `EnvWF`. -/
theorem unfoldDefinition_spec (henv : ConLeche.EnvWF env) (s₀ : AState)
    (d : Nat) (e : EIdx) (hok : CheckOK mode env fe s₀)
    (hdw : ∃ x, denoteE s₀.store e = some x ∧ Expr.WScoped d x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.unfoldDefinition fe e
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ x, denoteE s₀.store e = some x →
          denoteEO s'.store r = some (ConLeche.unfoldDefinition env x) ∧
          ∀ y, ConLeche.unfoldDefinition env x = some y →
            Expr.WScoped d y⌝⦄ := by
  obtain ⟨x, hden, hwx⟩ := hdw
  have hfn := ExprOps.getAppFn_spec coreWalkFuel
  have hargs := ExprOps.getAppArgs_spec coreWalkFuel
  have hmk := ExprOps.mkAppN_spec
  have hcv := fun (s : AState) (n : NIdx) (lps : List NIdx) (value : EIdx)
      (us : LsIdx) => constValAt_spec' (mode := mode) (env := env) (fe := fe)
        s n lps value us
  obtain ⟨rk, hrk⟩ := hok.state.wf
  to_wp; vcgen [ConRon.Arena.unfoldDefinition, wp% hfn, wp% hargs, wp% hmk, wp% hcv]
  all_goals (bridge_peel; subst_vars)
  all_goals (bridge_peel; subst_vars)
  -- the callees' preconditions
  case vc2 | vc5 | vc13 => apply CheckOK.state; assumption
  case vc7 => exact hok
  case vc14 => rw [hden]; rfl
  case vc6 => rw [denote_ext hden ‹Ext _ _›]; rfl
  case vc4 =>
    rw [(‹RelEL Expr.getAppArgs _ e _ _›) x (denote_ext hden ‹Ext _ _›)]; rfl
  case vc8 =>
    rename_i _ _ _ _ _ _ hfd _ _ _ hrel hview
    obtain ⟨nm, ls, _, hn, hus⟩ :=
      denote_const_inv hok.state.wf hview (hrel x hden)
    obtain ⟨dcv, dval, hdcv, hdval, hfind⟩ := env_defn_of_index hok hn hfd
    obtain ⟨_, hlps, _⟩ := denoteCV_inv hdcv
    exact ⟨nm, ls, dcv, dval, _, hn, hus, hlps, hdval, hfind⟩
  case vc3 =>
    rename_i _ _ _ _ _ _ hfd _ _ _ _ hrel hview _ _ _ _ hcvr
    obtain ⟨nm, ls, hgf, hn, hus⟩ :=
      denote_const_inv hok.state.wf hview (hrel x hden)
    obtain ⟨dcv, dval, _, _, hfind⟩ := env_defn_of_index hok hn hfd
    rw [hcvr nm ls dcv dval _ hn hus hfind]; rfl
  -- the definition UNFOLDS
  case vc1 =>
    rename_i _ _ _ _ _ _ hfd _ hlen _ _ hst3 hx13 _ _ hc13 hp13 hmkr hlsv hrel
      hview hck1 hargsr hx01 hp01 hcvr
    obtain ⟨nm, ls, hgf, hn, hus⟩ :=
      denote_const_inv hok.state.wf hview (hrel x hden)
    obtain ⟨dcv, dval, hdcv, _, hfind⟩ := env_defn_of_index hok hn hfd
    obtain ⟨_, hlps, _⟩ := denoteCV_inv hdcv
    have hv := hcvr nm ls dcv dval _ hn hus hfind
    have ha := hargsr x (denote_ext hden hx01)
    have hr := hmkr _ _ hv ha
    have hul : ls.length = dcv.levelParams.length := by
      rw [← view_len_of_denoteLs hus hlsv, hlen, denoteNList_len hlps]
    have hud : ConLeche.unfoldDefinition env x =
        some (Expr.mkAppN (dval.instantiateLevelParams dcv.levelParams ls)
          x.getAppArgs) := by
      simp only [ConLeche.unfoldDefinition, hgf, hfind, hul, ite_true]
    refine ⟨hck1.mono hst3 hx13 hc13 hp13, hx01.trans hx13, hp13.trans hp01,
      fun x' hx' => ?_⟩
    obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hden)
    refine ⟨by rw [hud]; simp only [denoteEO, hr, Option.map_some], ?_⟩
    intro y hy
    exact ConLeche.unfoldDefinition_WScoped henv hy hwx
  -- the level count does not match: both decline
  case vc9 =>
    rename_i _ _ _ _ _ _ hfd _ hlen hlsv hrel hview
    obtain ⟨nm, ls, hgf, hn, hus⟩ :=
      denote_const_inv hok.state.wf hview (hrel x hden)
    obtain ⟨dcv, dval, hdcv, _, hfind⟩ := env_defn_of_index hok hn hfd
    obtain ⟨_, hlps, _⟩ := denoteCV_inv hdcv
    have hul : ¬ ls.length = dcv.levelParams.length := by
      rw [← view_len_of_denoteLs hus hlsv, denoteNList_len hlps]; exact hlen
    have hud : ConLeche.unfoldDefinition env x = none := by
      simp only [ConLeche.unfoldDefinition, hgf, hfind, hul, ite_false]
    refine ⟨hok, Ext.refl _, rfl, fun x' hx' => ?_⟩
    obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hden)
    rw [hud]
    exact ⟨rfl, fun y hy => absurd hy (by simp)⟩
  -- the head is a constant but not a stored definition
  case vc10 =>
    rename_i _ _ _ _ hrel hview hnd
    obtain ⟨nm, ls, hgf, hn, _⟩ :=
      denote_const_inv hok.state.wf hview (hrel x hden)
    have hud : ConLeche.unfoldDefinition env x = none := by
      have h := env_not_defn_of_index hok hn hnd
      simp only [ConLeche.unfoldDefinition, hgf]
    refine ⟨hok, Ext.refl _, rfl, fun x' hx' => ?_⟩
    obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hden)
    rw [hud]
    exact ⟨rfl, fun y hy => absurd hy (by simp)⟩
  -- the head is not a constant
  case vc11 =>
    rename_i _ _ _ hnc hrel hview
    have hud : ConLeche.unfoldDefinition env x = none := by
      have h := denote_not_const hok.state.wf hview (hrel x hden) hnc
      simp only [ConLeche.unfoldDefinition]
    refine ⟨hok, Ext.refl _, rfl, fun x' hx' => ?_⟩
    obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hden)
    rw [hud]
    exact ⟨rfl, fun y hy => absurd hy (by simp)⟩
  -- the head's TAG is not `const` (task #97-P5-Core round 4's tag-first arm)
  case vc12 =>
    have hr := (‹RelE Expr.getAppFn _ e _ _›) x hden
    obtain ⟨v, hv⟩ := denoteE_view hr
    have hud : ConLeche.unfoldDefinition env x = none := by
      have h := denote_not_const hok.state.wf hv hr
        (fun c us hh => view_tagOf_ne hv (t := ETag.const) ‹_› (by rw [hh]; rfl))
      simp only [ConLeche.unfoldDefinition]
    refine ⟨hok, Ext.refl _, rfl, fun x' hx' => ?_⟩
    obtain rfl : x' = x := Option.some.inj (hx'.symm.trans hden)
    rw [hud]
    exact ⟨rfl, fun y hy => absurd hy (by simp)⟩

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

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:172-181 headHint — the
not-a-constant arm. -/
theorem headHint_of_not_const {env : Env} {x : Expr}
    (h : ∀ n us, x.getAppFn ≠ .const n us) :
    ConLeche.headHint env x = .opaque := by
  simp only [ConLeche.headHint]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:172-181 headHint — **THEOREM
1 for `headHint`**: the reducibility hint of the constant at the head.
**CLOSED** (round 3).  The answer type is one both tiers share, so the
relation is `SimVOp`'s — here spelled as the equation it is, because
con-leche's `headHint` takes no fuel.  Five verification conditions. -/
theorem headHint_spec (s₀ : AState) (e : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store e = some x) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.headHint fe e
    ⦃⇓? h s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ h = ConLeche.headHint env x⌝⦄ := by
  have hfn := ExprOps.getAppFn_spec coreWalkFuel
  obtain ⟨rk, hrk⟩ := hok.state.wf
  to_wp; vcgen [ConRon.Arena.headHint, wp% hfn]
  all_goals (bridge_peel; subst_vars)
  -- `getAppFn_spec`'s two preconditions
  case vc5 => exact hok.state
  case vc6 => rw [hden]; rfl
  -- the definition arm
  case vc1 =>
    rename_i _ _ _ _ _ _ _ hfd hrel hview
    refine ⟨hok, rfl, rfl, ?_⟩
    obtain ⟨nm, ls, hgf, hn, _⟩ :=
      denote_const_inv hok.state.wf hview (hrel x hden)
    obtain ⟨dcv, dval, _, _, hfind⟩ := env_defn_of_index hok hn hfd
    simp only [ConLeche.headHint, hgf, hfind]
  -- the not-a-definition arm
  case vc2 =>
    rename_i _ _ _ _ hrel hview hnd
    refine ⟨hok, rfl, rfl, ?_⟩
    obtain ⟨nm, ls, hgf, hn, _⟩ :=
      denote_const_inv hok.state.wf hview (hrel x hden)
    exact (headHint_of_not_defn hgf (env_not_defn_of_index hok hn hnd)).symm
  -- the not-a-constant arm
  case vc3 =>
    rename_i _ _ _ hnc hrel hview
    refine ⟨hok, rfl, rfl, ?_⟩
    exact (headHint_of_not_const
      (denote_not_const hok.state.wf hview (hrel x hden) hnc)).symm
  -- the tag-first `else` arm (task #97-P5-Core round 4)
  case vc4 =>
    have hr := (‹RelE Expr.getAppFn _ e _ _›) x hden
    obtain ⟨v, hv⟩ := denoteE_view hr
    refine ⟨hok, rfl, rfl, ?_⟩
    exact (headHint_of_not_const (denote_not_const hok.state.wf hv hr
      (fun c us hh => view_tagOf_ne hv (t := ETag.const) ‹_› (by rw [hh]; rfl)))).symm

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

/-- con-leche: none — a handle whose VIEW is not a `.forallE` denotes an
expression that is not a `.forallE` (the binder meta is carried verbatim, so
the two shapes coincide).  `etaCert`'s not-a-∀ exit. -/
theorem denote_not_forallE {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} {v : ENodeView} (hv : st.view h = some v)
    (he : denoteE st h = some e)
    (hne : ∀ ty b m, v = .forallE ty b m → False) :
    ∀ p q m, e ≠ .forallE p q m := by
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv he]; simp
  | fvar k t => obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv he; simp
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv he; simp
  | const n us => obtain ⟨p, q, rfl, _, _⟩ := denote_const_inv hwf hv he; simp
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv he; simp
  | lam ty b m => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; simp
  | forallE ty b m => exact absurd rfl (hne ty b m)
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv he; simp
  | lit l => rw [denote_lit_inv hwf hv he]; simp
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv he; simp

/-- con-leche: none — DESIGN §8.3's "index inequality IS structural
inequality" at the NAME store, as a `Bool` equation: `denoteN`'s
functionality one way, `denoteN_inj` the other. -/
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

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:183-192 sameConstHeads —
**THEOREM 1 for `sameConstHeads`**: the lazy-delta same-head short-circuit.
**CLOSED** (round 3).  Nine verification conditions, the most of the three,
because the walk peels two subjects; `beq_of_denoteN` is the guard. -/
theorem sameConstHeads_spec (s₀ : AState) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.sameConstHeads a b
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.sameConstHeads x y⌝⦄ := by
  have hfn := ExprOps.getAppFn_spec coreWalkFuel
  obtain ⟨rk, hrk⟩ := hok.state.wf
  to_wp; vcgen [ConRon.Arena.sameConstHeads, wp% hfn]
  -- Thirteen verification conditions since the twin tests the tags first
  -- (task #97-P5-Core round 4): the four callee preconditions, the verdict,
  -- and for each of the four tests its view-side catch-all AND its tag-side
  -- `else` (which recovers the view from the denotation).
  all_goals (bridge_peel; subst_vars)
  case vc4 | vc8 => exact hok.state
  case vc9 =>
    rename_i hva _
    obtain ⟨ex, ea, hx, hdf, _⟩ := denote_app_inv hok.state.wf hva hda
    rw [hdf]; rfl
  case vc5 =>
    rename_i hvb _
    obtain ⟨ey, eb, hy, hdf, _⟩ := denote_app_inv hok.state.wf hvb hdb
    rw [hdf]; rfl
  case vc1 =>
    rename_i hrelb hrela hva hvb hvra hvrb
    obtain ⟨ex, ea, rfl, hdfa, _⟩ := denote_app_inv hok.state.wf hva hda
    obtain ⟨ey, eb, rfl, hdfb, _⟩ := denote_app_inv hok.state.wf hvb hdb
    obtain ⟨nma, lsa, hgfa, hna, _⟩ :=
      denote_const_inv hok.state.wf hvra (hrela ex hdfa)
    obtain ⟨nmb, lsb, hgfb, hnb, _⟩ :=
      denote_const_inv hok.state.wf hvrb (hrelb ey hdfb)
    refine ⟨hok, rfl, rfl, ?_⟩
    rw [beq_of_denoteN hrk.nsWF hna hnb]
    simp only [ConLeche.sameConstHeads, hgfa, hgfb]
  case vc2 =>
    rename_i hncb hrelb hrela hva hvb hvra hvrb
    obtain ⟨ex, ea, rfl, hdfa, _⟩ := denote_app_inv hok.state.wf hva hda
    obtain ⟨ey, eb, rfl, hdfb, _⟩ := denote_app_inv hok.state.wf hvb hdb
    have hnc := denote_not_const hok.state.wf hvrb (hrelb ey hdfb) hncb
    refine ⟨hok, rfl, rfl, ?_⟩
    simp only [ConLeche.sameConstHeads]
    cases hgx : ex.getAppFn <;> cases hgy : ey.getAppFn <;>
      first | rfl | exact absurd hgy (hnc _ _)
  case vc3 =>
    rename_i htb hrelb hrela hva hvb hvra
    obtain ⟨ex, ea, rfl, hdfa, _⟩ := denote_app_inv hok.state.wf hva hda
    obtain ⟨ey, eb, rfl, hdfb, _⟩ := denote_app_inv hok.state.wf hvb hdb
    obtain ⟨vb, hvrb⟩ := denoteE_view (hrelb ey hdfb)
    have hnc := denote_not_const hok.state.wf hvrb (hrelb ey hdfb)
      (fun c us hh => view_tagOf_ne hvrb (t := ETag.const) htb (by rw [hh]; rfl))
    refine ⟨hok, rfl, rfl, ?_⟩
    simp only [ConLeche.sameConstHeads]
    cases hgx : ex.getAppFn <;> cases hgy : ey.getAppFn <;>
      first | rfl | exact absurd hgy (hnc _ _)
  case vc6 =>
    rename_i hnca hrela hva hvb hvra
    obtain ⟨ex, ea, rfl, hdfa, _⟩ := denote_app_inv hok.state.wf hva hda
    obtain ⟨ey, eb, rfl, hdfb, _⟩ := denote_app_inv hok.state.wf hvb hdb
    have hnc := denote_not_const hok.state.wf hvra (hrela ex hdfa) hnca
    refine ⟨hok, rfl, rfl, ?_⟩
    simp only [ConLeche.sameConstHeads]
    cases hgx : ex.getAppFn <;> cases hgy : ey.getAppFn <;>
      first | rfl | exact absurd hgx (hnc _ _)
  case vc7 =>
    rename_i hta hrela hva hvb
    obtain ⟨ex, ea, rfl, hdfa, _⟩ := denote_app_inv hok.state.wf hva hda
    obtain ⟨ey, eb, rfl, hdfb, _⟩ := denote_app_inv hok.state.wf hvb hdb
    obtain ⟨va, hvra⟩ := denoteE_view (hrela ex hdfa)
    have hnc := denote_not_const hok.state.wf hvra (hrela ex hdfa)
      (fun c us hh => view_tagOf_ne hvra (t := ETag.const) hta (by rw [hh]; rfl))
    refine ⟨hok, rfl, rfl, ?_⟩
    simp only [ConLeche.sameConstHeads]
    cases hgx : ex.getAppFn <;> cases hgy : ey.getAppFn <;>
      first | rfl | exact absurd hgx (hnc _ _)
  case vc10 =>
    rename_i hnab hva hvb
    obtain ⟨ex, ea, rfl, hdfa, _⟩ := denote_app_inv hok.state.wf hva hda
    have hna := denote_not_app hok.state.wf hvb hdb hnab
    refine ⟨hok, rfl, rfl, ?_⟩
    simp only [ConLeche.sameConstHeads]
    cases hy : y <;> first | rfl | exact absurd hy (hna _ _)
  case vc11 =>
    rename_i htb hva
    obtain ⟨ex, ea, rfl, hdfa, _⟩ := denote_app_inv hok.state.wf hva hda
    obtain ⟨vb, hvb⟩ := denoteE_view hdb
    have hna := denote_not_app hok.state.wf hvb hdb
      (fun f a hh => view_tagOf_ne hvb (t := ETag.app) htb (by rw [hh]; rfl))
    refine ⟨hok, rfl, rfl, ?_⟩
    simp only [ConLeche.sameConstHeads]
    cases hy : y <;> first | rfl | exact absurd hy (hna _ _)
  case vc12 =>
    rename_i hnaa hva
    have hna := denote_not_app hok.state.wf hva hda hnaa
    refine ⟨hok, rfl, rfl, ?_⟩
    simp only [ConLeche.sameConstHeads]
    cases hx : x <;> cases hy : y <;> first | rfl | exact absurd hx (hna _ _)
  case vc13 =>
    rename_i hta
    obtain ⟨va, hva⟩ := denoteE_view hda
    have hna := denote_not_app hok.state.wf hva hda
      (fun f a hh => view_tagOf_ne hva (t := ETag.app) hta (by rw [hh]; rfl))
    refine ⟨hok, rfl, rfl, ?_⟩
    simp only [ConLeche.sameConstHeads]
    cases hx : x <;> cases hy : y <;> first | rfl | exact absurd hx (hna _ _)


/-! ### `defeqSpine`, the walk that consumes the whole round

It is the first walk of the tier whose callee list is entirely made of
things this round or the last one closed: `getAppFn_spec` and
`getAppArgs_spec` (the `ExprOps` import, §0c), `lvlsEq?_spec` (round 2,
strengthened to the equation), and `defEqList_go` (above).  Twenty
verification conditions, sixteen of them the four `StateOK`/`isSome`
preconditions of the four spine reads. -/

/-- con-leche: none — `beq_of_denoteN` as a propositional equivalence,
which is what a guard written with `=` rather than `==` needs. -/
theorem name_eq_iff_of_denoteN {st : NStore} (hwf : NStoreWF st)
    {n₁ n₂ : NIdx} {nm₁ nm₂ : ConLeche.Name}
    (h1 : denoteN st n₁ = some nm₁) (h2 : denoteN st n₂ = some nm₂) :
    (n₁ = n₂) ↔ (nm₁ = nm₂) := by
  constructor
  · intro h; subst h; rw [h1] at h2; exact Option.some.inj h2
  · intro h; subst h; exact denoteN_inj hwf h1 h2

/-- con-leche: ConLeche/Kernel/Core.lean:1420-1439 defeqSpine — both
heads are the same constant, the spines have the same length and the universe
arguments agree, so the verdict is the spines'. -/
theorem defeqSpineFueled_const {F d : Nat} {x y : Expr} {n n' : ConLeche.Name}
    {us us' : List Level} {r : Bool}
    (hx : x.getAppFn = .const n us) (hy : y.getAppFn = .const n' us')
    (hc : n = n' ∧ x.getAppArgs.length = y.getAppArgs.length)
    (hlv : Level.isEquivList us us' = some true)
    (hr : ConLeche.defEqListFueled mode env F d x.getAppArgs y.getAppArgs
      = .ok r) :
    ConLeche.defeqSpineFueled mode env F d x y = .ok r := by
  simp only [ConLeche.defeqSpineFueled, ConLeche.defeqSpine, hx, hy,
    ite_eq_left hc, hlv]
  exact hr

/-- con-leche: ConLeche/Kernel/Core.lean:1420-1439 defeqSpine — an
INCONCLUSIVE level comparison declines, and so does a negative one: the
caller falls back to unfolding, so `false` is never final. -/
theorem defeqSpineFueled_lvl {F d : Nat} {x y : Expr} {n n' : ConLeche.Name}
    {us us' : List Level}
    (hx : x.getAppFn = .const n us) (hy : y.getAppFn = .const n' us')
    (hc : n = n' ∧ x.getAppArgs.length = y.getAppArgs.length)
    (hlv : ¬ (Level.isEquivList us us' = some true)) :
    ConLeche.defeqSpineFueled mode env F d x y = .ok false := by
  simp only [ConLeche.defeqSpineFueled, ConLeche.defeqSpine, hx, hy,
    ite_eq_left hc]
  cases hl : Level.isEquivList us us' with
  | none => rfl
  | some v =>
    cases v with
    | true => exact absurd hl hlv
    | false => rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1420-1439 defeqSpine —
different head names, or different spine lengths. -/
theorem defeqSpineFueled_ne {F d : Nat} {x y : Expr} {n n' : ConLeche.Name}
    {us us' : List Level}
    (hx : x.getAppFn = .const n us) (hy : y.getAppFn = .const n' us')
    (hc : ¬ (n = n' ∧ x.getAppArgs.length = y.getAppArgs.length)) :
    ConLeche.defeqSpineFueled mode env F d x y = .ok false := by
  simp only [ConLeche.defeqSpineFueled, ConLeche.defeqSpine, hx, hy,
    ite_eq_right hc]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1420-1439 defeqSpine — the
second head is not a constant. -/
theorem defeqSpineFueled_nc_right {F d : Nat} {x y : Expr}
    {n : ConLeche.Name} {us : List Level} (hx : x.getAppFn = .const n us)
    (hy : ∀ m vs, y.getAppFn ≠ .const m vs) :
    ConLeche.defeqSpineFueled mode env F d x y = .ok false := by
  simp only [ConLeche.defeqSpineFueled, ConLeche.defeqSpine, hx]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1420-1439 defeqSpine — nor is
the first. -/
theorem defeqSpineFueled_nc_left {F d : Nat} {x y : Expr}
    (hx : ∀ m vs, x.getAppFn ≠ .const m vs) :
    ConLeche.defeqSpineFueled mode env F d x y = .ok false := by
  simp only [ConLeche.defeqSpineFueled, ConLeche.defeqSpine]
  rfl

/-- con-leche: ConLeche/Kernel/Core.lean:1420-1439 defeqSpine — **THEOREM 1
for `defeqSpine`**: two applications of the same constant are defeq if their
universe arguments and their argument vectors are.  **CLOSED** (round 3).

Two of DESIGN §8.3's "index inequality IS structural inequality" in one
guard: the twin tests `n = n'` on `NIdx` where con-leche tests `Name`
equality (`name_eq_iff_of_denoteN`, both directions), and `aa.length =
bb.length` on handle lists where con-leche tests the denoted spines'
(`denoteEList_len`, both directions).  The walk DECLINES on either, so both
are needed at both signs — round 2's rule at a compound guard. -/
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
  have hfn := ExprOps.getAppFn_spec coreWalkFuel
  have hag := ExprOps.getAppArgs_spec coreWalkFuel
  have hdl := defEqList_go hsim d
  obtain ⟨rk, hrk⟩ := hok.state.wf
  to_wp; vcgen [ConRon.Arena.defeqSpine, wp% hfn, wp% hag, wp% lvlsEq?_spec (mode := mode) (env := env) (fe := fe), wp% hdl]
  all_goals (bridge_peel; subst_vars)
  -- the four spine reads' `StateOK`/`isSome` preconditions, and the two
  -- `CheckOK`s of `lvlsEq?` and the list comparison
  case vc8 | vc10 | vc14 | vc18 => exact hok.state
  case vc11 | vc19 => rw [hda]; rfl
  case vc9 | vc15 => rw [hdb]; rfl
  case vc6 => exact hok
  case vc2 => assumption
  -- heads, level lists and argument lists all agree
  case vc1 =>
    rename_i hlen hck1 hck hst1 hxt hpn1 hpn hrec hrelB hrelA hrelFb hrelFa
      hviewA hviewB hlvs
    obtain ⟨nma, lsa, hgfa, hna, husa⟩ :=
      denote_const_inv hok.state.wf hviewA (hrelFa x hda)
    obtain ⟨nmb, lsb, hgfb, hnb, husb⟩ :=
      denote_const_inv hok.state.wf hviewB (hrelFb y hdb)
    have hnn : nma = nmb := Option.some.inj (hna.symm.trans hnb)
    have hdaa := hrelA x hda
    have hdbb := hrelB y hdb
    have hlenX : x.getAppArgs.length = y.getAppArgs.length := by
      rw [denoteEList_len hdaa, denoteEList_len hdbb, hlen]
    obtain ⟨lus, lvs, hlu, hlv, hiso⟩ := hlvs
    rw [husa] at hlu; rw [husb] at hlv
    obtain rfl : lus = lsa := (Option.some.inj hlu).symm
    obtain rfl : lvs = lsb := (Option.some.inj hlv).symm
    refine ⟨hck, by rw [← hst1]; exact hxt, by rw [hpn, hpn1], ?_⟩
    obtain ⟨F, hF⟩ :=
      hrec x.getAppArgs y.getAppArgs (by rw [hst1]; exact hdaa)
        (by rw [hst1]; exact hdbb)
    exact ⟨F, defeqSpineFueled_const hgfa hgfb ⟨hnn, hlenX⟩ hiso.symm hF⟩
  -- the argument lists denote, in the state `lvlsEq?` left
  case vc3 =>
    rename_i _ hst _ hrelB hrelA _ _ _ _ _
    exact ⟨x.getAppArgs, by rw [hst]; exact hrelA x hda,
      fun z hz => hwa.getAppArgs z hz⟩
  case vc4 =>
    rename_i _ hst _ hrelB hrelA _ _ _ _ _
    exact ⟨y.getAppArgs, by rw [hst]; exact hrelB y hdb,
      fun z hz => hwb.getAppArgs z hz⟩
  -- the level lists differ
  case vc5 =>
    rename_i rv hnt hlen hck0 hst0 hpn0 hrelB hrelA hrelFb hrelFa hviewA hviewB
      hlvs
    obtain ⟨nma, lsa, hgfa, hna, husa⟩ :=
      denote_const_inv hok.state.wf hviewA (hrelFa x hda)
    obtain ⟨nmb, lsb, hgfb, hnb, husb⟩ :=
      denote_const_inv hok.state.wf hviewB (hrelFb y hdb)
    have hnn : nma = nmb := Option.some.inj (hna.symm.trans hnb)
    have hdaa := hrelA x hda
    have hdbb := hrelB y hdb
    have hlenX : x.getAppArgs.length = y.getAppArgs.length := by
      rw [denoteEList_len hdaa, denoteEList_len hdbb, hlen]
    obtain ⟨lus, lvs, hlu, hlv, hiso⟩ := hlvs
    rw [husa] at hlu; rw [husb] at hlv
    obtain rfl : lus = lsa := (Option.some.inj hlu).symm
    obtain rfl : lvs = lsb := (Option.some.inj hlv).symm
    refine ⟨hck0, by rw [hst0]; exact Ext.refl _, hpn0,
      ⟨0, defeqSpineFueled_lvl hgfa hgfb ⟨hnn, hlenX⟩
        (fun hc => hnt (hiso.trans hc))⟩⟩
  -- the head names or the arities differ
  case vc7 =>
    rename_i hne hrelB hrelA hrelFb hrelFa hviewA hviewB
    obtain ⟨nma, lsa, hgfa, hna, husa⟩ :=
      denote_const_inv hok.state.wf hviewA (hrelFa x hda)
    obtain ⟨nmb, lsb, hgfb, hnb, husb⟩ :=
      denote_const_inv hok.state.wf hviewB (hrelFb y hdb)
    have hdaa := hrelA x hda
    have hdbb := hrelB y hdb
    refine ⟨hok, Ext.refl _, rfl, ⟨0, defeqSpineFueled_ne hgfa hgfb ?_⟩⟩
    intro hc
    obtain ⟨h1, h2⟩ := hc
    refine hne ⟨(name_eq_iff_of_denoteN hrk.nsWF hna hnb).mpr h1, ?_⟩
    rw [← denoteEList_len hdaa, ← denoteEList_len hdbb]
    exact h2
  -- `b`'s head is not a constant
  case vc12 =>
    rename_i _ hncb hrelFb hrelFa hviewA hviewB
    obtain ⟨nma, lsa, hgfa, hna, husa⟩ :=
      denote_const_inv hok.state.wf hviewA (hrelFa x hda)
    exact ⟨hok, Ext.refl _, rfl,
      ⟨0, defeqSpineFueled_nc_right hgfa
        (denote_not_const hok.state.wf hviewB (hrelFb y hdb) hncb)⟩⟩
  -- `b`'s head does not carry the `const` TAG (round 4's tag-first arm)
  case vc13 =>
    rename_i htb hrelFb hrelFa hviewA
    obtain ⟨nma, lsa, hgfa, hna, husa⟩ :=
      denote_const_inv hok.state.wf hviewA (hrelFa x hda)
    obtain ⟨vb, hviewB⟩ := denoteE_view (hrelFb y hdb)
    exact ⟨hok, Ext.refl _, rfl,
      ⟨0, defeqSpineFueled_nc_right hgfa
        (denote_not_const hok.state.wf hviewB (hrelFb y hdb)
          (fun c us hh => view_tagOf_ne hviewB (t := ETag.const) htb
            (by rw [hh]; rfl)))⟩⟩
  -- `a`'s head is not a constant
  case vc16 =>
    rename_i _ hnca hrelFa hviewA
    exact ⟨hok, Ext.refl _, rfl,
      ⟨0, defeqSpineFueled_nc_left
        (denote_not_const hok.state.wf hviewA (hrelFa x hda) hnca)⟩⟩
  -- `a`'s head does not carry the `const` TAG
  case vc17 =>
    rename_i hta hrelFa
    obtain ⟨va, hviewA⟩ := denoteE_view (hrelFa x hda)
    exact ⟨hok, Ext.refl _, rfl,
      ⟨0, defeqSpineFueled_nc_left
        (denote_not_const hok.state.wf hviewA (hrelFa x hda)
          (fun c us hh => view_tagOf_ne hviewA (t := ETag.const) hta
            (by rw [hh]; rfl)))⟩⟩


/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt —
`Bridge/ExprOps/Inst1.lean`'s `instantiate1Fast_spec` with the substituted
value's denotation moved out of the argument list: IN as an existential (here
only `isSome`, since the walk does not need the value) and OUT as a
universal.  Four lines, and without it a caller that INTERNS the value cannot
apply the rule at all. -/
theorem instantiate1Fast_specE (fuel : Nat) (s₀ : AState) (e v : EIdx)
    (d : Nat) (hok : StateOK s₀) (hv : (denoteE s₀.store v).isSome = true)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ ConRon.Arena.instantiate1Fast fuel e v d
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.memos.inst1C = ∅ ∧
        ∀ ve, denoteE s₀.store v = some ve →
          ExprOps.Inst1At ve d s₀.store e s'.store r⌝⦄ := by
  obtain ⟨ve, hve⟩ := Option.isSome_iff_exists.mp hv
  have hb := ExprOps.instantiate1Fast_spec fuel s₀ e v d ve hok hve hden
  to_wp; vcgen [wp% hb]
  rename_i hpost
  obtain ⟨h1, h2, _hbm, h3, h4, h5, h6⟩ := hpost
  refine ⟨h1, h2, h3, h4, h5, fun w hw => ?_⟩
  rw [hve] at hw
  obtain rfl := (Option.some.inj hw).symm
  exact h6


/-- con-leche: ConLeche/Kernel/Core.lean:505-530 etaCert — **THEOREM 1 for
`etaCert`**: η at a λ against a non-λ.

**CLOSED** since (this note is round 3's, when it was the cheapest of the
ten open walks): its whole PURE side is
proved above (`etaCertFueled_nf`, `_dom`, `_body`, `_yes`) and so is the one
callee rule whose published shape it cannot use
(`instantiate1Fast_specE`, `Bridge/Core/Walks/Spine.lean`).  What is left is
twenty-three verification conditions on the arena side — the three knot calls
in their primed shape, two `internE`s with their `ViewOK` obligations, one
`instantiate1Fast`, and the well-scopedness of the opened body at `d + 1`
(con-leche's `WScoped.instantiate1` and `WScoped.mono` are exactly it).  The
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
  obtain ⟨hwt, hwx⟩ : Expr.WScoped d t ∧ Expr.WScoped d x := by
    simpa only [Expr.WScoped] using hwa
  have hio := hsim.inferIO'
  have hwh := hsim.whnf'
  have hdq := hsim.defeq'
  have hi1 := instantiate1Fast_specE coreWalkFuel
  to_wp; vcgen [ConRon.Arena.etaCert, wp% hio, wp% hwh, wp% hdq, wp% hi1]
  all_goals (bridge_peel; subst_vars)
  -- the sixteen callee preconditions
  case vc21 => exact hok
  case vc22 => exact ⟨y, hdy, hwb⟩
  case vc19 => assumption
  case vc20 =>
    rename_i s0 s1 hck1 hx01 hp10 hsio
    obtain ⟨v, hv, hw, _⟩ := hsio y hdy
    exact ⟨v, hv, hw⟩
  case vc14 => assumption
  case vc15 =>
    rename_i s0 s1 _ s2 _ _ _ hck1 hx01 hp10 hsio hck2 hx12 hp21 hswh hview
    obtain ⟨vtb, hvtb, _, _⟩ := hsio y hdy
    obtain ⟨vw, hvw, hwvw, _⟩ := hswh vtb hvtb
    obtain ⟨p, q, rfl, hp, _⟩ := denote_forallE_inv hck2.state.wf hview hvw
    simp only [Expr.WScoped] at hwvw
    exact ⟨p, hp, hwvw.1⟩
  case vc16 =>
    rename_i s0 s1 _ s2 _ _ _ hck1 hx01 hp10 hsio hck2 hx12 hp21 hswh hview
    exact ⟨t, denote_ext hdt (hx01.trans hx12), hwt⟩
  case vc11 =>
    rename_i s0 s1 _ s2 _ _ _ s3 hck1 hck3 hx01 hx23 hp10 hsio hp32 hck2 hx12
      hp21 hswh hview hsdq1
    exact hck3.state.wf
  case vc12 =>
    rename_i s0 s1 _ s2 _ _ _ s3 hck1 hck3 hx01 hx23 hp10 hsio hp32 hck2 hx12
      hp21 hswh hview hsdq1
    exact viewOK_fvar (by rw [denote_ext hdt ((hx01.trans hx12).trans hx23)]; rfl)
  case vc8 =>
    rename_i s0 s1 _ s2 _ _ _ s3 s4 hck1 hck3 hwf4 hx01 hx23 hx34 hp10 hsio hp32
      _ _ hc43 hp43 _ _ _ hfv hck2 hx12 hp21 hswh hview hsdq1
    exact ⟨hwf4⟩
  case vc9 =>
    rename_i s0 s1 _ s2 _ _ _ s3 s4 hck1 hck3 hwf4 hx01 hx23 hx34 hp10 hsio hp32
      _ _ hc43 hp43 _ _ _ hfv hck2 hx12 hp21 hswh hview hsdq1
    rw [hfv, denoteEView, denote_ext hdt (((hx01.trans hx12).trans hx23).trans hx34)]
    rfl
  case vc10 =>
    rename_i s0 s1 _ s2 _ _ _ s3 s4 hck1 hck3 hwf4 hx01 hx23 hx34 hp10 hsio hp32
      _ _ hc43 hp43 _ _ _ hfv hck2 hx12 hp21 hswh hview hsdq1
    rw [denote_ext hdx (((hx01.trans hx12).trans hx23).trans hx34)]; rfl
  case vc6 =>
    rename_i s0 s1 _ s2 _ _ _ s3 s4 s5 hck1 hck3 hwf4 hst5 hx01 hx23 hx34 hx45
      hp10 hsio hp32 _ hc54 _ hp54 hc43 _ hinst hp43 _ _ _ hfv hck2 hx12 hp21
      hswh hview hsdq1
    exact hst5.wf
  case vc7 =>
    rename_i s0 s1 _ s2 _ _ _ s3 s4 s5 hck1 hck3 hwf4 hst5 hx01 hx23 hx34 hx45
      hp10 hsio hp32 _ hc54 _ hp54 hc43 _ hinst hp43 _ _ _ hfv hck2 hx12 hp21
      hswh hview hsdq1
    have hx04 := ((hx01.trans hx12).trans hx23).trans hx34
    rw [denoteEView, denote_ext hdt hx04, Option.map_some] at hfv
    exact viewOK_app (by rw [denote_ext hdy (hx04.trans hx45)]; rfl)
      (by rw [denote_ext hfv hx45]; rfl)
  case vc3 =>
    rename_i s0 s1 _ s2 _ _ _ s3 s4 s5 s6 hck1 hck3 hwf4 hst5 hwf6 hx01 hx23
      hx34 hx45 hx56 hp10 hsio hp32 _ hc54 _ _ hp54 _ hc43 _ hinst hc65 hp43
      hp65 _ _ _ _ _ hfv _ hrhs hck2 hx12 hp21 hswh hview hsdq1
    exact ((hck3.mono ⟨hwf4⟩ hx34 hc43 hp43).mono hst5 hx45 hc54 hp54).mono
      ⟨hwf6⟩ hx56 hc65 hp65
  case vc4 =>
    rename_i s0 s1 _ s2 _ _ _ s3 s4 s5 s6 hck1 hck3 hwf4 hst5 hwf6 hx01 hx23
      hx34 hx45 hx56 hp10 hsio hp32 _ hc54 _ _ hp54 _ hc43 _ hinst hc65 hp43
      hp65 _ _ _ _ _ hfv _ hrhs hck2 hx12 hp21 hswh hview hsdq1
    have hx04 := ((hx01.trans hx12).trans hx23).trans hx34
    rw [denoteEView, denote_ext hdt hx04, Option.map_some] at hfv
    exact ⟨_, denote_ext (hinst _ hfv x (denote_ext hdx hx04)) hx56,
      Expr.WScoped.instantiate1 hwt 0 hwx⟩
  case vc5 =>
    rename_i s0 s1 _ s2 _ _ _ s3 s4 s5 s6 hck1 hck3 hwf4 hst5 hwf6 hx01 hx23
      hx34 hx45 hx56 hp10 hsio hp32 _ hc54 _ _ hp54 _ hc43 _ hinst hc65 hp43
      hp65 _ _ _ _ _ hfv _ hrhs hck2 hx12 hp21 hswh hview hsdq1
    have hx04 := ((hx01.trans hx12).trans hx23).trans hx34
    rw [denoteEView, denote_ext hdt hx04, Option.map_some] at hfv
    simp only [denoteEView, denote_ext hdy ((hx04.trans hx45).trans hx56),
      denote_ext hfv (hx45.trans hx56), opt2] at hrhs
    refine ⟨_, hrhs, ?_⟩
    simp only [Expr.WScoped]
    exact ⟨hwb.mono (Nat.le_succ d), Nat.lt_succ_self d, hwt⟩
  -- the opened bodies DISAGREE
  case vc1 =>
    rename_i s0 s1 _ s2 _ _ _ s3 s4 s5 s6 rb s7 hnb hck1 hck3 hwf4 hst5 hwf6
      hck7 hx01 hx23 hx34 hx45 hx56 hx67 hp10 hsio hp32 _ hc54 _ hp76 hsdq2 _
      hp54 _ hc43 _ hinst hc65 hp43 hp65 _ _ _ _ _ hfv _ hrhs hck2 hx12 hp21
      hswh hview hsdq1
    obtain ⟨vtb, hvtb, _, F1, hF1⟩ := hsio y hdy
    obtain ⟨vw, hvw, hwvw, F2, hF2⟩ := hswh vtb hvtb
    obtain ⟨p, q, rfl, hp, _⟩ := denote_forallE_inv hck2.state.wf hview hvw
    have ht2 := denote_ext hdt (hx01.trans hx12)
    obtain ⟨F3, hF3⟩ := hsdq1 p t hp ht2
    have hx04 := ((hx01.trans hx12).trans hx23).trans hx34
    rw [denoteEView, denote_ext hdt hx04, Option.map_some] at hfv
    have hlhs := hinst _ hfv x (denote_ext hdx hx04)
    have hx06 := (hx04.trans hx45).trans hx56
    simp only [denoteEView, denote_ext hdy hx06,
      denote_ext hfv (hx45.trans hx56), opt2] at hrhs
    obtain ⟨F4, hF4⟩ := hsdq2 _ _ (denote_ext hlhs hx56) hrhs
    have hck7' : CheckOK mode env fe _ := hck7
    refine ⟨hck7', (hx06.trans hx67), ?_, ?_⟩
    · rw [hp76, hp65, hp54, hp43, hp32, hp21, hp10]
    · obtain rfl : rb = false := by simpa using hnb
      exact ⟨F1 + F2 + F3 + F4, etaCertFueled_body
        (ConLeche.inferTypeIO_mono (by omega) hF1)
        (ConLeche.whnf_mono (by omega) hF2)
        (ConLeche.isDefEqCore_mono (by omega) hF3)
        (ConLeche.isDefEqCore_mono (by omega) hF4)⟩
  -- the CERTIFICATE (the regime-mismatch `fail` leaves no verification
  -- condition at all)
  case vc2 =>
    rename_i s0 s1 _ s2 _ _ _ s3 s4 s5 s6 rb s7 hnb hpw hck1 hck3 hwf4 hst5 hwf6
      hck7 hx01 hx23 hx34 hx45 hx56 hx67 hp10 hsio hp32 _ hc54 _ hp76 hsdq2 _
      hp54 _ hc43 _ hinst hc65 hp43 hp65 _ _ _ _ _ hfv _ hrhs hck2 hx12 hp21
      hswh hview hsdq1
    obtain ⟨vtb, hvtb, _, F1, hF1⟩ := hsio y hdy
    obtain ⟨vw, hvw, hwvw, F2, hF2⟩ := hswh vtb hvtb
    obtain ⟨p, q, rfl, hp, _⟩ := denote_forallE_inv hck2.state.wf hview hvw
    have ht2 := denote_ext hdt (hx01.trans hx12)
    obtain ⟨F3, hF3⟩ := hsdq1 p t hp ht2
    have hx04 := ((hx01.trans hx12).trans hx23).trans hx34
    rw [denoteEView, denote_ext hdt hx04, Option.map_some] at hfv
    have hlhs := hinst _ hfv x (denote_ext hdx hx04)
    have hx06 := (hx04.trans hx45).trans hx56
    simp only [denoteEView, denote_ext hdy hx06,
      denote_ext hfv (hx45.trans hx56), opt2] at hrhs
    obtain ⟨F4, hF4⟩ := hsdq2 _ _ (denote_ext hlhs hx56) hrhs
    have hck7' : CheckOK mode env fe _ := hck7
    refine ⟨hck7', (hx06.trans hx67), ?_, ?_⟩
    · rw [hp76, hp65, hp54, hp43, hp32, hp21, hp10]
    · obtain rfl : rb = true := by simpa using hnb
      exact ⟨F1 + F2 + F3 + F4, etaCertFueled_yes
        (ConLeche.inferTypeIO_mono (by omega) hF1)
        (ConLeche.whnf_mono (by omega) hF2)
        (ConLeche.isDefEqCore_mono (by omega) hF3)
        (ConLeche.isDefEqCore_mono (by omega) hF4) (by simpa using hpw)⟩
  -- the domains DISAGREE
  case vc13 =>
    rename_i s0 s1 _ s2 _ _ _ rb s3 hnb hck1 hck3 hx01 hx23 hp10 hsio hp32 hsdq1
      hck2 hx12 hp21 hswh hview
    obtain ⟨vtb, hvtb, _, F1, hF1⟩ := hsio y hdy
    obtain ⟨vw, hvw, hwvw, F2, hF2⟩ := hswh vtb hvtb
    obtain ⟨p, q, rfl, hp, _⟩ := denote_forallE_inv hck2.state.wf hview hvw
    have ht2 := denote_ext hdt (hx01.trans hx12)
    obtain ⟨F3, hF3⟩ := hsdq1 p t hp ht2
    obtain rfl : rb = false := by simpa using hnb
    refine ⟨hck3, ((hx01.trans hx12).trans hx23), by rw [hp32, hp21, hp10], ?_⟩
    exact ⟨F1 + F2 + F3, etaCertFueled_dom
      (ConLeche.inferTypeIO_mono (by omega) hF1)
      (ConLeche.whnf_mono (by omega) hF2)
      (ConLeche.isDefEqCore_mono (by omega) hF3)⟩
  -- the comparand's type does not reduce to a ∀
  case vc17 =>
    rename_i s0 s1 _ s2 _ hnf hck1 hx01 hp10 hsio hck2 hx12 hp21 hswh hview
    obtain ⟨vtb, hvtb, _, F1, hF1⟩ := hsio y hdy
    obtain ⟨vw, hvw, _, F2, hF2⟩ := hswh vtb hvtb
    refine ⟨hck2, hx01.trans hx12, by rw [hp21, hp10], ?_⟩
    exact ⟨F1 + F2, etaCertFueled_nf
      (ConLeche.inferTypeIO_mono (by omega) hF1)
      (ConLeche.whnf_mono (by omega) hF2)
      (denote_not_forallE hck2.state.wf ‹_› hvw hnf)⟩
  -- the comparand's type's whnf does not carry the `forallE` TAG (task
  -- #97-P5-Core round 4's tag-first arm)
  case vc18 =>
    rename_i s0 s1 s2 htag hck1 hck2 hx01 hx12 hp10 hsio hp21 hswh
    obtain ⟨vtb, hvtb, _, F1, hF1⟩ := hsio y hdy
    obtain ⟨vw, hvw, _, F2, hF2⟩ := hswh vtb hvtb
    obtain ⟨v, hv⟩ := denoteE_view hvw
    refine ⟨hck2, hx01.trans hx12, by rw [hp21, hp10], ?_⟩
    exact ⟨F1 + F2, etaCertFueled_nf
      (ConLeche.inferTypeIO_mono (by omega) hF1)
      (ConLeche.whnf_mono (by omega) hF2)
      (denote_not_forallE hck2.state.wf hv hvw
        (fun ty b m hh => view_tagOf_ne hv (t := ETag.forallE) htag
          (by rw [hh]; rfl)))⟩

/-! ## 5. A knot slot's answer, forgotten -/

/-- con-leche: none — a knot slot's answer, forgetting the pure run: the
existential a SECOND slot's precondition asks for.  The one-line bridge
between `Bridge/Core/Knot.lean`'s `SimE` and its primed slots'
`hdw` hypothesis. -/
theorem SimE.exists_denote {op : Nat → Nat → Expr → CheckM Expr} {d : Nat}
    {e : Expr} {st : EStore} {r : EIdx} (h : SimE op d e st r) :
    ∃ v, denoteE st r = some v ∧ Expr.WScoped d v := by
  obtain ⟨v, hv, hw, _⟩ := h; exact ⟨v, hv, hw⟩

/-! ## 6. The axiom census -/

section Census

#print axioms viewLen_of_denoteLs
#print axioms denoteNList_len
#print axioms denoteCI_defnInfo_inv
#print axioms denoteCI_defn_inv
#print axioms denoteCV_inv
#print axioms denote_not_const
#print axioms denote_not_app
#print axioms env_defn_of_index
#print axioms env_not_defn_of_index
#print axioms beq_of_denoteN
#print axioms name_eq_iff_of_denoteN
#print axioms instantiate1Fast_specE
/-! **The four closed walks of this module.** -/
#print axioms unfoldableHead_spec
#print axioms headHint_spec
#print axioms sameConstHeads_spec
#print axioms defeqSpine_spec
#print axioms view_len_of_denoteLs
#print axioms denote_not_forallE
#print axioms unfoldDefinition_spec
#print axioms etaCert_spec

end Census

end ConRon.Bridge.Core

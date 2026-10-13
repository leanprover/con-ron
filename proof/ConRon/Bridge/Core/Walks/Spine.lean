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
`ensureSort` from `inferBodyIO`'s `.forallE` arm and from the binder walks, so
`Arms/{InferIO,Infer}.lean` meet the same wall — and both are ON the chain.
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
import ConRon.Bridge.Frame

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

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
  | thmInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hc⟩ := h; simp at hc
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
  | lam ty b => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; simp
  | forallE ty b =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv he; simp
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv he; simp
  | lit l => rw [denote_lit_inv hwf hv he]; simp
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv he; simp


/-- con-leche: none — `denote_not_const` at the tag-first twin's `else` arm:
a handle whose TAG is not `const` denotes no constant (task #120: the shape
`bridge_fwd` instantiates from the arm's own hypotheses). -/
theorem denote_not_const_of_tag {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} (he : denoteE st h = some e)
    (ht : ¬ (h.tag == ETag.const) = true) : ∀ n us, e ≠ .const n us := by
  obtain ⟨v, hv⟩ := denoteE_view he
  exact denote_not_const hwf hv he
    (fun c us hh => view_tagOf_ne hv (t := ETag.const) ht (by rw [hh]; rfl))
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
    ⦃fun s => s = s₀⦄ ConRon.Arena.unfoldableHead fe e
    ⦃fun b s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.unfoldableHead env x; ⊤⦄ := by
  have hfn := ExprOps.getAppFn_spec coreWalkFuel
  vcgen [ConRon.Arena.unfoldableHead, hfn]
  all_goals (bridge_peel; subst_vars)
  bridge_frame
  bridge_fwd [env_defn_of_index, env_not_defn_of_index, denoteCV_inv, denote_not_const,
    denote_not_const_of_tag]
  bridge_frame
  -- the definition arm: the twin compares the level-list length it read
  vc_arm (hgf : Expr.getAppFn _ = .const _ _) (hfind : env.find? _ = some (.defnInfo _ _ _))
      (hlen : some _ = LsStore.viewLen _ _) (hus : denoteLs _ _ = some _)
      (hlps : Frontend.denoteNList _ _ = some _) =>
    rw [viewLen_of_denoteLs hus] at hlen
    simp only [ConLeche.unfoldableHead, hgf, hfind, Option.some.inj hlen,
      denoteNList_len hlps]
  -- the not-a-definition arm
  vc_arm (hgf : Expr.getAppFn _ = .const _ _)
      (hnd : ∀ cv val hint, env.find? _ ≠ some (.defnInfo cv val hint)) =>
    exact (unfoldableHead_of_not_defn hgf hnd).symm
  -- the not-a-constant arms (the view's catch-all and the tag-first `else`)
  vc_arm (hnc : ∀ n us, Expr.getAppFn _ ≠ .const n us) =>
    exact (unfoldableHead_of_not_const hnc).symm

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:136-155 unfoldDefinition — the
postcondition of a DECLINING arm, from con-leche's own `none` (task #120: one
`refine` for all four declining arms, whatever order `vcgen` hands them in). -/
theorem unfoldDefinition_none_post {st : EStore} {x : Expr} {d : Nat}
    (h : ConLeche.unfoldDefinition env x = none) :
    denoteEO st none = some (ConLeche.unfoldDefinition env x) ∧
      ∀ y, ConLeche.unfoldDefinition env x = some y → Expr.WScoped d y := by
  rw [h]; exact ⟨rfl, fun y hy => nomatch hy⟩

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
    ⦃fun s => s = s₀⦄ ConRon.Arena.unfoldDefinition fe e
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ x, denoteE s₀.store e = some x →
          denoteEO s'.store r = some (ConLeche.unfoldDefinition env x) ∧
          ∀ y, ConLeche.unfoldDefinition env x = some y →
            Expr.WScoped d y; ⊤⦄ := by
  obtain ⟨x, hden, hwx⟩ := hdw
  have hfn := ExprOps.getAppFn_spec coreWalkFuel
  have hargs := ExprOps.getAppArgs_spec coreWalkFuel
  have hmk := ExprOps.mkAppN_spec
  have hcv := fun (s : AState) (n : NIdx) (lps : List NIdx) (value : EIdx)
      (us : LsIdx) => constValAt_spec' (mode := mode) (env := env) (fe := fe)
        s n lps value us
  vcgen [ConRon.Arena.unfoldDefinition, hfn, hargs, hmk, hcv]
  all_goals (bridge_peel; subst_vars)
  all_goals (bridge_peel; subst_vars)
  bridge_frame
  bridge_fwd [env_defn_of_index, env_not_defn_of_index, denoteCV_inv, denote_not_const,
    denote_not_const_of_tag]
  bridge_frame
  -- the definition UNFOLDS
  vc_arm (hgf : Expr.getAppFn _ = .const _ _) (hfind : env.find? _ = some (.defnInfo _ _ _))
      (hlen : List.length _ = _) (hlsv : LsStore.view _ _ = some _)
      (hus : denoteLs _ _ = some _) (hlps : Frontend.denoteNList _ _ = some _)
      (hr : denoteE _ _ = some (Expr.mkAppN _ _)) =>
    have hul := (view_len_of_denoteLs hus hlsv).symm.trans
      (hlen.trans (denoteNList_len hlps).symm)
    refine ⟨?_, fun y hy => ConLeche.unfoldDefinition_WScoped henv hy hwx⟩
    simp only [ConLeche.unfoldDefinition, hgf, hfind, hul, ite_true, denoteEO, hr,
      Option.map_some]
  -- every other arm declines, and so does con-leche
  all_goals refine unfoldDefinition_none_post ?_
  -- the level count does not match
  vc_arm (hgf : Expr.getAppFn _ = .const _ _) (hfind : env.find? _ = some (.defnInfo _ _ _))
      (hlen : ¬ List.length _ = _) (hlsv : LsStore.view _ _ = some _)
      (hus : denoteLs _ _ = some _) (hlps : Frontend.denoteNList _ _ = some _) =>
    rw [view_len_of_denoteLs hus hlsv, ← denoteNList_len hlps] at hlen
    simp only [ConLeche.unfoldDefinition, hgf, hfind, hlen, ite_false]
  -- the head is a constant but not a stored definition
  vc_arm (hgf : Expr.getAppFn _ = .const _ _)
      (hnd : ∀ cv val hint, env.find? _ ≠ some (.defnInfo cv val hint)) =>
    simp only [ConLeche.unfoldDefinition, hgf]
  -- the head is not a constant
  vc_arm (hnc : ∀ n us, Expr.getAppFn _ ≠ .const n us) =>
    simp only [ConLeche.unfoldDefinition]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:172-181 headHint — **THEOREM 1
for `headHint`**: the reducibility hint of the constant at the head.
**CLOSED** (round 3).  The answer type is one both tiers share, so the
relation is an equation, because con-leche's `headHint` takes no fuel.  It is `unfoldableHead` minus the
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
relation is an equation, because con-leche's `headHint` takes no fuel.  Five verification conditions. -/
theorem headHint_spec (s₀ : AState) (e : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store e = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.headHint fe e
    ⦃fun h s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ h = ConLeche.headHint env x; ⊤⦄ := by
  have hfn := ExprOps.getAppFn_spec coreWalkFuel
  vcgen [ConRon.Arena.headHint, hfn]
  all_goals (bridge_peel; subst_vars)
  bridge_frame
  bridge_fwd [env_defn_of_index, env_not_defn_of_index, denote_not_const,
    denote_not_const_of_tag]
  bridge_frame
  -- the definition arm
  vc_arm (hgf : Expr.getAppFn _ = .const _ _) (hfind : env.find? _ = some (.defnInfo _ _ _)) =>
    simp only [ConLeche.headHint, hgf, hfind]
  -- the not-a-definition arm
  vc_arm (hgf : Expr.getAppFn _ = .const _ _)
      (hnd : ∀ cv val hint, env.find? _ ≠ some (.defnInfo cv val hint)) =>
    exact (headHint_of_not_defn hgf hnd).symm
  -- the not-a-constant arms (the view's catch-all and the tag-first `else`)
  vc_arm (hnc : ∀ n us, Expr.getAppFn _ ≠ .const n us) =>
    exact (headHint_of_not_const hnc).symm

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:183-192 sameConstHeads — the
second head is not a constant (task #120: the four declining arms as lemmas,
so that each arm is one `exact`). -/
theorem sameConstHeads_nc_right {f₁ a₁ f₂ a₂ : Expr}
    (h : ∀ n us, f₂.getAppFn ≠ .const n us) :
    ConLeche.sameConstHeads (.app f₁ a₁) (.app f₂ a₂) = false := by
  simp only [ConLeche.sameConstHeads]
  cases hgx : f₁.getAppFn <;> cases hgy : f₂.getAppFn <;>
    first | rfl | exact absurd hgy (h _ _)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:183-192 sameConstHeads — the
first head is not a constant. -/
theorem sameConstHeads_nc_left {f₁ a₁ y : Expr}
    (h : ∀ n us, f₁.getAppFn ≠ .const n us) :
    ConLeche.sameConstHeads (.app f₁ a₁) y = false := by
  cases y with
  | app f₂ a₂ =>
    simp only [ConLeche.sameConstHeads]
    cases hgx : f₁.getAppFn <;> cases f₂.getAppFn <;>
      first | rfl | exact absurd hgx (h _ _)
  | _ => simp only [ConLeche.sameConstHeads]

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:183-192 sameConstHeads — the
second subject is not an application. -/
theorem sameConstHeads_na_right {f₁ a₁ y : Expr} (h : ∀ f a, y ≠ .app f a) :
    ConLeche.sameConstHeads (.app f₁ a₁) y = false := by
  simp only [ConLeche.sameConstHeads]
  cases hy : y <;> first | rfl | exact absurd hy (h _ _)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:183-192 sameConstHeads — the
first subject is not an application. -/
theorem sameConstHeads_na_left {x y : Expr} (h : ∀ f a, x ≠ .app f a) :
    ConLeche.sameConstHeads x y = false := by
  simp only [ConLeche.sameConstHeads]
  cases hx : x <;> cases hy : y <;> first | rfl | exact absurd hx (h _ _)

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
  | lam ty b => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; simp
  | forallE ty b =>
    obtain ⟨p, q, rfl, _, _⟩ := denote_forallE_inv hwf hv he; simp
  | letE ty w b =>
    obtain ⟨p, q, r, rfl, _, _, _⟩ := denote_letE_inv hwf hv he; simp
  | lit l => rw [denote_lit_inv hwf hv he]; simp
  | proj n i sub => obtain ⟨p, q, rfl, _, _⟩ := denote_proj_inv hwf hv he; simp


/-- con-leche: none — `denote_not_app` at the tag-first `else` arm. -/
theorem denote_not_app_of_tag {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} (he : denoteE st h = some e)
    (ht : ¬ (h.tag == ETag.app) = true) : ∀ f a, e ≠ .app f a := by
  obtain ⟨v, hv⟩ := denoteE_view he
  exact denote_not_app hwf hv he
    (fun f a hh => view_tagOf_ne hv (t := ETag.app) ht (by rw [hh]; rfl))
/-- con-leche: none — a handle whose VIEW is not a `.forallE` denotes an
expression that is not a `.forallE`.  `etaCert`'s not-a-∀ exit. -/
theorem denote_not_forallE {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} {v : ENodeView} (hv : st.view h = some v)
    (he : denoteE st h = some e)
    (hne : ∀ ty b, v = .forallE ty b → False) :
    ∀ p q, e ≠ .forallE p q := by
  cases v with
  | bvar i => rw [denote_bvar_inv hwf hv he]; simp
  | fvar k t => obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hv he; simp
  | sort u => obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hv he; simp
  | const n us => obtain ⟨p, q, rfl, _, _⟩ := denote_const_inv hwf hv he; simp
  | app f a => obtain ⟨p, q, rfl, _, _⟩ := denote_app_inv hwf hv he; simp
  | lam ty b => obtain ⟨p, q, rfl, _, _⟩ := denote_lam_inv hwf hv he; simp
  | forallE ty b => exact absurd rfl (hne ty b)
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
    ⦃fun s => s = s₀⦄ ConRon.Arena.sameConstHeads a b
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.sameConstHeads x y; ⊤⦄ := by
  have hfn := ExprOps.getAppFn_spec coreWalkFuel
  obtain ⟨rk, hrk⟩ := hok.state.wf
  vcgen [ConRon.Arena.sameConstHeads, hfn]
  all_goals (bridge_peel; subst_vars)
  bridge_frame
  bridge_fwd [denote_not_const, denote_not_const_of_tag, denote_not_app,
    denote_not_app_of_tag]
  bridge_frame
  -- both heads are constants: the names compared by handle
  vc_arm (hgfa : Expr.getAppFn ?fa = .const ?na _) (hgfb : Expr.getAppFn ?fb = .const ?nb _)
      (hna : denoteN _ ?ca = some ?na) (hnb : denoteN _ ?cb = some ?nb)
      ⊢ (?ca == ?cb) = ConLeche.sameConstHeads (.app ?fa _) (.app ?fb _) =>
    rw [beq_of_denoteN hrk.nsWF hna hnb]
    simp only [ConLeche.sameConstHeads, hgfa, hgfb]
  -- a head is not a constant (by its view or by its tag)
  vc_arm (hnc : ∀ n us, Expr.getAppFn ?fb ≠ .const n us)
      ⊢ false = ConLeche.sameConstHeads (.app _ _) (.app ?fb _) =>
    exact (sameConstHeads_nc_right hnc).symm
  vc_arm (hnc : ∀ n us, Expr.getAppFn ?fa ≠ .const n us)
      ⊢ false = ConLeche.sameConstHeads (.app ?fa _) _ =>
    exact (sameConstHeads_nc_left hnc).symm
  -- a subject is not an application
  vc_arm (hna : ∀ f a, ?y ≠ .app f a) ⊢ false = ConLeche.sameConstHeads (.app _ _) ?y =>
    exact (sameConstHeads_na_right hna).symm
  vc_arm (hna : ∀ f a, ?x ≠ .app f a) ⊢ false = ConLeche.sameConstHeads ?x _ =>
    exact (sameConstHeads_na_left hna).symm

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
    ⦃fun s => s = s₀⦄
      ConRon.Arena.defeqSpine (coreKnot mode fe id fuel) fe d a b
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.defeqSpineFueled mode env F d x y) r; ⊤⦄ := by
  have hfn := ExprOps.getAppFn_spec coreWalkFuel
  have hag := ExprOps.getAppArgs_spec coreWalkFuel
  have hdl := defEqList_go hsim d
  have hwaa := hwa.getAppArgs
  have hwbb := hwb.getAppArgs
  obtain ⟨rk, hrk⟩ := hok.state.wf
  vcgen [ConRon.Arena.defeqSpine, hfn, hag, lvlsEq?_spec (mode := mode) (env := env) (fe := fe), hdl]
  all_goals (bridge_peel; subst_vars)
  bridge_frame
  bridge_fwd [denote_not_const, denote_not_const_of_tag]
  bridge_frame
  -- heads, level lists and argument lists all agree
  vc_arm (hgfa : Expr.getAppFn x = .const _ _) (hgfb : Expr.getAppFn y = .const _ _)
      (hlen : List.length _ = List.length _)
      (hxs : Frontend.denoteEList _ _ = some x.getAppArgs)
      (hys : Frontend.denoteEList _ _ = some y.getAppArgs)
      (hiso : some true = Level.isEquivList _ _)
      (hF : ConLeche.defEqList _ _ _ x.getAppArgs y.getAppArgs = .ok _) =>
    exact ⟨_, defeqSpineFueled_const hgfa hgfb
      ⟨rfl, by rw [denoteEList_len hxs, denoteEList_len hys, hlen]⟩ hiso.symm hF⟩
  -- the level lists differ
  vc_arm (hgfa : Expr.getAppFn x = .const _ _) (hgfb : Expr.getAppFn y = .const _ _)
      (hlen : List.length _ = List.length _)
      (hxs : Frontend.denoteEList _ _ = some x.getAppArgs)
      (hys : Frontend.denoteEList _ _ = some y.getAppArgs)
      (hnt : Level.isEquivList _ _ ≠ some true) =>
    exact ⟨0, defeqSpineFueled_lvl hgfa hgfb
      ⟨rfl, by rw [denoteEList_len hxs, denoteEList_len hys, hlen]⟩ hnt⟩
  -- the head names or the arities differ
  vc_arm (hgfa : Expr.getAppFn x = .const ?na _) (hgfb : Expr.getAppFn y = .const ?nb _)
      (hna : denoteN _ ?ca = some ?na) (hnb : denoteN _ ?cb = some ?nb)
      (hne : ¬ (?ca = ?cb ∧ _))
      (hxs : Frontend.denoteEList _ _ = some x.getAppArgs)
      (hys : Frontend.denoteEList _ _ = some y.getAppArgs) =>
    refine ⟨0, defeqSpineFueled_ne hgfa hgfb fun ⟨h1, h2⟩ =>
      hne ⟨(name_eq_iff_of_denoteN hrk.nsWF hna hnb).mpr h1, ?_⟩⟩
    rw [← denoteEList_len hxs, ← denoteEList_len hys]
    exact h2
  -- `b`'s head is not a constant (by its view or by its tag)
  vc_arm (hgfa : Expr.getAppFn x = .const _ _) (hnc : ∀ n us, Expr.getAppFn y ≠ .const n us) =>
    exact ⟨0, defeqSpineFueled_nc_right hgfa hnc⟩
  -- `a`'s head is not a constant
  vc_arm (hnc : ∀ n us, Expr.getAppFn x ≠ .const n us) =>
    exact ⟨0, defeqSpineFueled_nc_left hnc⟩

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt —
`Bridge/ExprOps/Inst1.lean`'s `instantiate1Fast_spec` with the substituted
value's denotation moved out of the argument list: IN as an existential (here
only `isSome`, since the walk does not need the value) and OUT as a
universal.  Four lines, and without it a caller that INTERNS the value cannot
apply the rule at all. -/
theorem instantiate1Fast_specE (fuel : Nat) (s₀ : AState) (e v : EIdx)
    (d : Nat) (hok : StateOK s₀) (hv : (denoteE s₀.store v).isSome = true)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.instantiate1Fast fuel e v d
    ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.memos.inst1C = ∅ ∧
        ∀ ve, denoteE s₀.store v = some ve →
          ExprOps.Inst1At ve d s₀.store e s'.store r; ⊤⦄ := by
  obtain ⟨ve, hve⟩ := Option.isSome_iff_exists.mp hv
  have hb := ExprOps.instantiate1Fast_spec fuel s₀ e v d ve hok hve hden
  vcgen [hb]
  bridge_peel
  bridge_frame
  vc_arm (h6 : ExprOps.Inst1At ve _ _ _ _ _) =>
    intro w hw
    obtain rfl := eq_of_eq_some hve hw
    exact h6


/-- con-leche: ConLeche/Kernel/ExprOps.lean:176-178 instantiate1Fast —
`instantiate1Fast_spec` at the tier's invariant (the `.letE` exit's ζ). -/
theorem instantiate1Fast_ok_spec (s₀ : AState) (b w : EIdx) (B W : Expr)
    (hok : CheckOK mode env fe s₀) (hdb : denoteE s₀.store b = some B)
    (hdw : denoteE s₀.store w = some W) :
    ⦃fun s => s = s₀⦄ instantiate1Fast coreWalkFuel b w 0
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧ denoteE s'.store r = some (B.instantiate1 W); ⊤⦄ :=
  triple_mono (ExprOps.instantiate1Fast_spec coreWalkFuel s₀ b w 0 W hok.state hdw
      (by rw [hdb]; rfl))
    (fun _ _ ⟨hst, hx, hc, hp, _, hrel⟩ =>
      ⟨hok.mono hst hx hc hp, hx, hp, hrel B hdb⟩)

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
    (s₀ : AState) (d : Nat) (ty₁ body₁ b : EIdx)
    (t x y : Expr) (hok : CheckOK mode env fe s₀)
    (hdt : denoteE s₀.store ty₁ = some t)
    (hdx : denoteE s₀.store body₁ = some x)
    (hdy : denoteE s₀.store b = some y)
    (hwa : Expr.WScoped d (.lam t x)) (hwb : Expr.WScoped d y) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.etaCert mode (coreKnot mode fe id fuel) fe d ty₁ body₁ b
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        SimBOp (fun F => ConLeche.etaCertFueled mode env F d t x y)
          r; ⊤⦄ := by
  have hwt : Expr.WScoped d t := by unfold Expr.WScoped at hwa; exact hwa.1
  have hwx : Expr.WScoped d x := by unfold Expr.WScoped at hwa; exact hwa.2
  have tpure : ∀ {s : AState} {v : Bool} {Q : Bool → AState → Prop}, Q v s →
      ⦃fun s' => s' = s⦄ (pure v : AM Bool) ⦃fun r s' => Q r s'; ⊤⦄ := by
    intro s v Q h
    vcgen
    subst_vars; exact h
  -- the guard: `ioNeutral` reads the spine head's tag
  have hneu : ⦃fun s => s = s₀⦄ ConRon.Arena.ioNeutral b
      ⦃fun r s' => s' = s₀ ∧ r = y.ioNeutral; ⊤⦄ := by
    unfold ConRon.Arena.ioNeutral
    refine triple_seq (ExprOps.getAppFn_spec coreWalkFuel s₀ b hok.state
      (by rw [hdy]; rfl)) ?_
    rintro hd s1 ⟨rfl, hrel⟩
    have hh := hrel y hdy
    obtain ⟨v, hv⟩ := denoteE_view hh
    have htag := EStore.tagOf_of_view hv
    rw [denoteE_view_eq hok.state.wf hv] at hh
    unfold Expr.ioNeutral
    generalize y.getAppFn = g at hh ⊢
    cases v <;>
      simp [htag, denoteEView, opt2_eq_some_iff, opt3_eq_some_iff,
        Option.map_eq_some_iff, ENodeView.tagOf, ETag.bvar, ETag.fvar,
        ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE,
        ETag.lit, ETag.proj] at hh ⊢ <;>
      first
        | (obtain ⟨_, _, _, _, _, _, rfl⟩ := hh; exact tpure ⟨rfl, rfl⟩)
        | (obtain ⟨_, _, _, _, rfl⟩ := hh; exact tpure ⟨rfl, rfl⟩)
        | (obtain ⟨_, _, _, rfl⟩ := hh; exact tpure ⟨rfl, rfl⟩)
        | (obtain ⟨_, _, rfl⟩ := hh; exact tpure ⟨rfl, rfl⟩)
        | (obtain ⟨_, rfl⟩ := hh; exact tpure ⟨rfl, rfl⟩)
        | (subst hh; exact tpure ⟨rfl, rfl⟩)
        | exact tpure ⟨rfl, rfl⟩
  unfold ConRon.Arena.etaCert
  refine triple_seq hneu ?_
  rintro nb s1 ⟨rfl, rfl⟩
  cases hn : y.ioNeutral
  · simp only [Bool.not_false, ite_true]
    exact tpure ⟨hok, Ext.refl _, rfl, 0, etaCertFueled_notNeutral hn⟩
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  -- the comparand's type, reduced
  refine triple_seq (hsim.inferIO s1 d b y hok hdy hwb) ?_
  rintro tb s2 ⟨hok2, hx2, hp2, vtb, hvtb, hwvtb, F1, hF1⟩
  refine triple_seq (hsim.whnf s2 d tb vtb hok2 hvtb hwvtb) ?_
  rintro w s3 ⟨hok3, hx3, hp3, vw, hvw, hwvw, F2, hF2⟩
  have hx03 := hx2.trans hx3
  obtain ⟨v, hv⟩ := denoteE_view hvw
  refine tag_view_bind_triple hv ?_
    (fun hne => by cases v <;> first | rfl | exact absurd rfl hne)
  cases v
  case forallE ty₂ cod₂ =>
    obtain ⟨p, q, rfl, hp, hq⟩ := denote_forallE_inv hok3.state.wf hv hvw
    have hwpq : Expr.WScoped d p ∧ Expr.WScoped d q := by
      simpa only [Expr.WScoped] using hwvw
    dsimp only
    -- the domains
    refine triple_seq (hsim.defeq s3 d ty₂ ty₁ p t hok3 hp
      (denote_ext hdt hx03) hwpq.1 hwt) ?_
    rintro bd s4 ⟨hok4, hx4, hp4, F3, hF3⟩
    cases bd
    · simp only [Bool.false_eq_true, ite_false]
      exact tpure ⟨hok4, hx03.trans hx4, by rw [hp4, hp3, hp2],
        F1 + F2 + F3, etaCertFueled_dom hn
          (ConLeche.inferTypeIO_mono (by omega) hF1)
          (ConLeche.whnf_mono (by omega) hF2)
          (ConLeche.isDefEqCore_mono (by omega) hF3)⟩
    simp only [ite_true]
    have hx04 := hx03.trans hx4
    -- the fresh variable
    have hdt4 := denote_ext hdt hx04
    refine triple_seq (internE_spec s4 (.fvar d ty₁) hok4.state.wf
      (viewOK_fvar (by rw [hdt4]; rfl))) ?_
    rintro fv s5 ⟨hwf5, hx5, -, -, hm5, hc5, hp5, -, hd5⟩
    have hok5 := hok4.mono ⟨hwf5⟩ hx5 hc5 hp5
    have hfv : denoteE s5.store fv = some (.fvar d t) := by
      rw [hd5]; simp [denoteEView, denote_ext hdt4 hx5]
    have hx05 := hx04.trans hx5
    -- the λ body, opened
    refine triple_seq (instantiate1Fast_ok_spec s5 body₁ fv x (.fvar d t) hok5
      (denote_ext hdx hx05) hfv) ?_
    rintro lhs s6 ⟨hok6, hx6, hp6, hlhs⟩
    have hx06 := hx05.trans hx6
    -- the comparand, applied
    have hfv6 := denote_ext hfv hx6
    refine triple_seq (internE_spec s6 (.app b fv) hok6.state.wf
      (viewOK_app (by rw [denote_ext hdy hx06]; rfl) (by rw [hfv6]; rfl))) ?_
    rintro rhs s7 ⟨hwf7, hx7, -, -, -, hc7, hp7, -, hd7⟩
    have hok7 := hok6.mono ⟨hwf7⟩ hx7 hc7 hp7
    have hrhs : denoteE s7.store rhs = some (.app y (.fvar d t)) := by
      rw [hd7]
      simp [denoteEView, denote_ext hdy (hx06.trans hx7), denote_ext hfv6 hx7,
        opt2]
    have hx07 := hx06.trans hx7
    have hwl : Expr.WScoped (d + 1) (x.instantiate1 (.fvar d t)) :=
      Expr.WScoped.instantiate1 hwt 0 hwx
    have hwr : Expr.WScoped (d + 1) (.app y (.fvar d t)) := by
      simp only [Expr.WScoped]
      exact ⟨hwb.mono (Nat.le_succ d), Nat.lt_succ_self d, hwt⟩
    -- the bodies
    refine triple_seq (hsim.defeq s7 (d + 1) lhs rhs _ _ hok7
      (denote_ext hlhs hx7) hrhs hwl hwr) ?_
    rintro bb s8 ⟨hok8, hx8, hp8, F4, hF4⟩
    have hx08 := hx07.trans hx8
    have hp80 : s8.pins = s1.pins := by
      rw [hp8, hp7, hp6, hp5, hp4, hp3, hp2]
    cases bb
    · simp only [Bool.not_false, ite_true]
      exact tpure ⟨hok8, hx08, hp80, F1 + F2 + F3 + F4, etaCertFueled_body hn
          (ConLeche.inferTypeIO_mono (by omega) hF1)
          (ConLeche.whnf_mono (by omega) hF2)
          (ConLeche.isDefEqCore_mono (by omega) hF3)
          (ConLeche.isDefEqCore_mono (by omega) hF4)⟩
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    cases hv : mode.verifiedChecks
    · simp only [Bool.false_eq_true, ite_false]
      exact tpure ⟨hok8, hx08, hp80, F1 + F2 + F3 + F4, etaCertFueled_trusted hn
          (ConLeche.inferTypeIO_mono (by omega) hF1)
          (ConLeche.whnf_mono (by omega) hF2)
          (ConLeche.isDefEqCore_mono (by omega) hF3)
          (ConLeche.isDefEqCore_mono (by omega) hF4) hv⟩
    simp only [ite_true]
    -- the λ/η tax: the λ body's full-grade type against the codomain
    refine triple_seq (hsim.infer s8 (d + 1) lhs _ hok8
      (denote_ext hlhs (hx7.trans hx8)) hwl) ?_
    rintro t₁ s9 ⟨hok9, hx9, hp9, vt₁, hvt₁, hwvt₁, F5, hF5⟩
    have hx39 := (hx4.trans hx5).trans
      ((hx6.trans hx7).trans (hx8.trans hx9))
    refine triple_seq (instantiate1Fast_ok_spec s9 cod₂ fv q (.fvar d t) hok9
      (denote_ext hq hx39) (denote_ext hfv
        ((hx6.trans hx7).trans (hx8.trans hx9)))) ?_
    rintro t₂ s10 ⟨hok10, hx10, hp10, ht₂⟩
    refine triple_mono (hsim.defeq s10 (d + 1) t₁ t₂ _ _ hok10
      (denote_ext hvt₁ hx10) ht₂ hwvt₁
      (Expr.WScoped.instantiate1 hwt 0 hwpq.2)) ?_
    rintro r s11 ⟨hok11, hx11, hp11, F6, hF6⟩
    refine ⟨hok11, ((hx08.trans hx9).trans hx10).trans hx11,
      by rw [hp11, hp10, hp9, hp80], F1 + F2 + F3 + F4 + F5 + F6, ?_⟩
    exact etaCertFueled_tax hn
      (ConLeche.inferTypeIO_mono (by omega) hF1)
      (ConLeche.whnf_mono (by omega) hF2)
      (ConLeche.isDefEqCore_mono (by omega) hF3)
      (ConLeche.isDefEqCore_mono (by omega) hF4) hv
      (ConLeche.inferTypeCore_mono (by omega) hF5)
      (ConLeche.isDefEqCore_mono (by omega) hF6)
  all_goals
    dsimp only
    exact tpure ⟨hok3, hx03, by rw [hp3, hp2], F1 + F2, etaCertFueled_nf hn
      (ConLeche.inferTypeIO_mono (by omega) hF1)
      (ConLeche.whnf_mono (by omega) hF2)
      (denote_not_forallE hok3.state.wf hv hvw (fun _ _ h => nomatch h))⟩

/-! ## 5. The axiom census -/

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

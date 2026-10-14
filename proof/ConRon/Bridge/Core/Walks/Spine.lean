/-
# `ConRon.Bridge.Core.Walks.Spine` — the non-slot walks over the `ExprOps` spine rules

The four walks whose theorems need the `ExprOps` tier's spine rules:
`unfoldableHead`, `headHint`, `sameConstHeads` and `defeqSpine`, on
`ExprOps/Spine.lean`'s `getAppFn_spec` and `getAppArgs_spec`, together with
`unfoldDefinition` and `etaCert`.  `Walks/Owed.lean` does not import the
`ExprOps` tier; a body walk that needs one of these imports this module
beside it.

## What is in here besides the four walks

The facts the four need — the length projection of `viewLs`
bridged to the denotation and `denoteCI`'s constructor preservation at
`defnInfo` — and the two "index equality IS structural equality" transfers at
the name store.  Their section notes are below.

**The proofs are `vcgen` and `grind`** (the calibration of the
dispatch walks): `sym only [bridge_grind] => vcgen [f, callee specs…] <;>
finish` for all six walk theorems.  What makes a
dispatch walk `grind`-shaped is `Bridge/Grind.lean` §5/§6 (views, tags and the
environment index as EQUATIONS over projections) and, here, ONE unconditional
equation per con-leche function the walks compare against
(`sameConstHeads_eq`, `unfoldableHead_eq`, `unfoldDefinition_eq`,
`headHint_eq`, `spineDefEq_eq`), so that `grind` never splits a `match`; two
callees are restated in that shape (`constValAt_specA`, `defEqList_goA`) and
one at the tier's invariant (`mkAppN_specC`).

One thing is here for the IMPORT's sake rather than the subject's:
`instantiate1Fast_specE`, which is `ExprOps/Inst1.lean`'s spec in answer
shape and is what `etaCert_spec` needs.
-/
import ConRon.Bridge.Core.Walks.Owed
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.ExprOps.Spine
import ConRon.Bridge.Grind

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 0c. What the spine group needs

The walks of §1 read the head of an application (`ExprOps/Spine.lean`'s
`getAppFn_spec` over a `view`) and then the ENVIRONMENT INDEX at the head's
name.  Two facts are stated here:

1. **`viewLsLen` against the denotation.**  The length projection reads the
   stored record's own length and never rebuilds the list;
   `viewLen_of_denoteLs` says that the number it answers IS the length of
   what the handle denotes, over two one-line projection equations.
2. **`denoteCI` keeps a constant's CONSTRUCTOR** at `defnInfo`
   (`denoteCI_defnInfo_inv`), and a handle whose tag is not `const` denotes
   no constant (`denote_not_const`). -/

/-- con-leche: none — the LENGTH projection of one tier's `LsTables.get`:
the stored record's own length is the length of the list the handle decodes to
in that tier. -/
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
is what a walk comparing `viewLsLen` against con-leche's `us.length` needs. -/
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

/-! ## The spine tier's vocabulary

`Bridge/Grind.lean` §6/§8's shape for what this module's walks read and the
generic vocabulary cannot see from its place in the import graph (the
lengths and the well-scopedness live in con-leche's `InferLemmas` and in §0c
above, `RelEA` in `ExprOps/Spine.lean`), and the two callees whose specs
this module restates (`constValAt_spec'`, `defEqList_go`): a named predicate
on the denotation terms, its extraction lemma at `some`. -/

/-- con-leche: none — a level-list handle's length reads (`viewLen`, and the
length of its view) agree with its denotation. -/
def LsLenAt (st : LsStore) (i : LsIdx) : Option (List Level) → Prop
  | some us => st.viewLen i = some us.length ∧ (st.view i).map List.length = some us.length
  | none => True

/-- con-leche: none — `viewLen_of_denoteLs` at the denotation term. -/
theorem lsLenAt (st : LsStore) (i : LsIdx) : LsLenAt st i (denoteLs st i) := by
  cases h : denoteLs st i with
  | none => trivial
  | some us =>
    have h1 := viewLen_of_denoteLs h
    exact ⟨h1, lsStore_viewLen_eq st i ▸ h1⟩
grind_pattern [bridge_grind] lsLenAt => denoteLs st i

/-- con-leche: none — `LsLenAt` at a denoting handle. -/
theorem LsLenAt.some {st : LsStore} {i : LsIdx} {us : List Level} (H : LsLenAt st i (some us)) :
    st.viewLen i = some us.length ∧ (st.view i).map List.length = some us.length := H
grind_pattern [bridge_grind] LsLenAt.some => LsLenAt st i (some us)

/-- con-leche: none — every element of a list is well-scoped at `d`. -/
def AllWS (d : Nat) (xs : List Expr) : Prop := ∀ x ∈ xs, Expr.WScoped d x

/-- con-leche: none — a well-scoped term's spine arguments are. -/
theorem allWS_getAppArgs {d : Nat} {x : Expr} (h : Expr.WScoped d x) : AllWS d x.getAppArgs :=
  h.getAppArgs
grind_pattern [bridge_grind] allWS_getAppArgs => Expr.WScoped d x, Expr.getAppArgs x

/-- con-leche: none — an optional list denotes and is well-scoped (a callee's
precondition on a handle list, as one atom). -/
def OptAllWS (d : Nat) : Option (List Expr) → Prop
  | some xs => AllWS d xs
  | none => False

/-- con-leche: none — `OptAllWS` at a denoting list. -/
@[bridge_grind =] theorem OptAllWS.some_eq (d : Nat) (xs : List Expr) :
    OptAllWS d (some xs) = AllWS d xs := rfl

/-- con-leche: none — a constant record's denotation, field by field (the
length of its level parameters included). -/
def DenoteCV (st : EStore) (v : IConstantVal) : Option ConstantVal → Prop
  | some c => denoteN st.ns v.name = some c.name ∧
      Frontend.denoteNList st.ns v.levelParams = some c.levelParams ∧
      v.levelParams.length = c.levelParams.length ∧ denoteE st v.type = some c.type
  | none => True

/-- con-leche: none — `denoteCV_inv` at the denotation term. -/
theorem denoteCVAt (st : EStore) (v : IConstantVal) :
    DenoteCV st v (Frontend.denoteCV st v) := by
  cases h : Frontend.denoteCV st v with
  | none => trivial
  | some c =>
    obtain ⟨h1, h2, h3⟩ := denoteCV_inv h
    exact ⟨h1, h2, (denoteNList_len h2).symm, h3⟩
grind_pattern [bridge_grind] denoteCVAt => Frontend.denoteCV st v

/-- con-leche: none — `DenoteCV` at a denoting record. -/
theorem DenoteCV.some {st : EStore} {v : IConstantVal} {c : ConstantVal}
    (H : DenoteCV st v (some c)) :
    denoteN st.ns v.name = some c.name ∧
      Frontend.denoteNList st.ns v.levelParams = some c.levelParams ∧
      v.levelParams.length = c.levelParams.length ∧ denoteE st v.type = some c.type := H
grind_pattern [bridge_grind] DenoteCV.some => DenoteCV st v (some c)

/-- con-leche: none — `RelEA`'s answer at optional subjects. -/
def MapRelA (F : Expr → List Expr → Expr) : Option Expr → Option (List Expr) → Option Expr → Prop
  | some e, some es, o => o = some (F e es)
  | _, _, _ => True

/-- con-leche: none — a `RelEA` answer is a `MapRelA` fact. -/
theorem RelEA.mapRel {F : Expr → List Expr → Expr} {st st' : EStore} {c : EIdx}
    {args : List EIdx} {r : EIdx} (h : ExprOps.RelEA F st c args st' r) :
    MapRelA F (denoteE st c) (Frontend.denoteEList st args) (denoteE st' r) := by
  cases hc : denoteE st c with
  | none => trivial
  | some e =>
  cases ha : Frontend.denoteEList st args with
  | none => trivial
  | some es => exact h e es hc ha
grind_pattern [bridge_grind] RelEA.mapRel => ExprOps.RelEA F st c args st' r

/-- con-leche: none — `MapRelA` at denoting subjects. -/
theorem MapRelA.some {F : Expr → List Expr → Expr} {e : Expr} {es : List Expr}
    {o : Option Expr} (H : MapRelA F (some e) (some es) o) : o = some (F e es) := H
grind_pattern [bridge_grind] MapRelA.some => MapRelA F (some e) (some es) o

/-- con-leche: ConLeche/Kernel/ExprOps.lean mkAppN — `ExprOps/Spine.lean`'s
`mkAppN_spec` at the tier's invariant (`CheckOK.mono`), so that `grind` need not
re-derive `CheckOK` from `StateOK` at every pair of states. -/
theorem mkAppN_specC (args : List EIdx) (s₀ : AState) (f : EIdx)
    (hok : CheckOK mode env fe s₀) (hf : (denoteE s₀.store f).isSome = true)
    (ha : (Frontend.denoteEList s₀.store args).isSome = true) :
    ⦃fun s => s = s₀⦄ mkAppN f args
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        ExprOps.RelEA Expr.mkAppN s₀.store f args s'.store r; ⊤⦄ :=
  triple_mono (ExprOps.mkAppN_spec args s₀ f hok.state hf ha)
    (fun _ _ ⟨hst, hx, _, hc, hp, hrel⟩ => ⟨hok.mono hst hx hc hp, hx, hp, hrel⟩)

/-- con-leche: none — an optional term, if present, is well-scoped. -/
def OptWScoped (d : Nat) : Option Expr → Prop
  | some y => Expr.WScoped d y
  | none => True

/-- con-leche: none — `OptWScoped` at a present term. -/
theorem OptWScoped.some {d : Nat} {y : Expr} (H : OptWScoped d (some y)) :
    Expr.WScoped d y := H
grind_pattern [bridge_grind] OptWScoped.some => OptWScoped d (some y)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:115-125 unfoldDefinition — the
unfolding of a well-scoped term is well-scoped (`unfoldDefinition_WScoped`,
whose hypothesis is `EnvWF`), at the con-leche call term. -/
theorem optWScoped_unfold (henv : ConLeche.EnvWF env) {d : Nat} {x : Expr}
    (hw : Expr.WScoped d x) : OptWScoped d (ConLeche.unfoldDefinition env x) := by
  cases h : ConLeche.unfoldDefinition env x with
  | none => trivial
  | some y => exact ConLeche.unfoldDefinition_WScoped henv h hw
grind_pattern [bridge_grind] optWScoped_unfold =>
  ConLeche.unfoldDefinition env x, Expr.WScoped d x

/-- con-leche: none — `constValAt`'s answer at the denotations of the name and
the levels: the definition's value, instantiated. -/
def ConstValPost (env : Env) (st : EStore) (r : EIdx) :
    Option ConLeche.Name → Option (List Level) → Prop
  | some nm, some ls => denoteE st r = some ((cDefnValue (env.find? nm)).instantiateLevelParams
      (cDefnVal (env.find? nm)).levelParams ls)
  | _, _ => True

/-- con-leche: none — `ConstValPost` at denoting subjects. -/
theorem ConstValPost.some {st : EStore} {r : EIdx} {nm : ConLeche.Name} {ls : List Level}
    (H : ConstValPost env st r (some nm) (some ls)) :
    denoteE st r = some ((cDefnValue (env.find? nm)).instantiateLevelParams
      (cDefnVal (env.find? nm)).levelParams ls) := H
grind_pattern [bridge_grind] ConstValPost.some => ConstValPost env st r (some nm) (some ls)

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:115-125 unfoldDefinition —
`Walks/Cached.lean`'s `constValAt_spec'` with the index's projections as its
precondition and `ConstValPost` as its answer (no `∃` to prove, no
`∀` to instantiate). -/
theorem constValAt_specA (s₀ : AState) (n : NIdx) (lps : List NIdx)
    (value : EIdx) (us : LsIdx) (hok : CheckOK mode env fe s₀)
    (hd : iDefn? (fe.find? n) = true) (hlps : (iDefnVal (fe.find? n)).levelParams = lps)
    (hval : iDefnValue (fe.find? n) = value)
    (hn : (denoteN s₀.store.ns n).isSome = true)
    (hus : (denoteLs s₀.store.lss us).isSome = true) :
    ⦃fun s => s = s₀⦄ constValAt n lps value us
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ConstValPost env s'.store r (denoteN s₀.store.ns n) (denoteLs s₀.store.lss us); ⊤⦄ := by
  obtain ⟨nm, hnm⟩ := Option.isSome_iff_exists.mp hn
  obtain ⟨ls, hls⟩ := Option.isSome_iff_exists.mp hus
  have hfa := indexAt hok n
  rw [hnm] at hfa
  obtain ⟨h1, -, h3, -⟩ := hfa
  obtain ⟨hcv, hve⟩ := h3 hd
  have hc := denoteCVAt s₀.store (iDefnVal (fe.find? n))
  rw [hcv] at hc
  obtain ⟨-, hlp, -, -⟩ := hc
  have hcd : cDefn? (env.find? nm) = true := h1.trans hd
  have hfe : env.find? nm = some (.defnInfo (cDefnVal (env.find? nm))
      (cDefnValue (env.find? nm)) (cDefnHint (env.find? nm))) := by
    revert hcd; generalize env.find? nm = o; intro hcd
    match o, hcd with
    | some (.defnInfo _ _ _), _ => rfl
  refine triple_mono (constValAt_spec' s₀ n lps value us hok
    ⟨nm, ls, _, _, _, hnm, hls, hlps ▸ hlp, hval ▸ hve, hfe⟩) ?_
  rintro r s' ⟨h1, h2, h3, h4⟩
  refine ⟨h1, h2, h3, ?_⟩
  rw [hnm, hls]
  exact h4 _ _ _ _ _ hnm hls hfe

/-! ## 1. The three with an unfueled pure side

con-leche's comparand is a plain function of the environment, so the
conclusion is an equation and there is no fuel existential anywhere in the
statement.  These are the cheapest walks of the tier — their fourth,
`isBoolTrue`, is in `Bridge/Core/Walks/Guards.lean`, and the three here
differ from it only by needing `getAppFn`, which is what the `ExprOps`
import buys. -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:134-140 unfoldableHead — the
function as ONE equation over tags and projections: the head is a
constant, the environment has a definition at its name, the level counts
agree. -/
@[bridge_grind =] theorem unfoldableHead_eq (x : Expr) : ConLeche.unfoldableHead env x =
    (exprTag x.getAppFn == ETag.const && cDefn? (env.find? (exprConstName x.getAppFn)) &&
      (exprConstLevels x.getAppFn).length ==
        (cDefnVal (env.find? (exprConstName x.getAppFn))).levelParams.length) := by
  simp only [ConLeche.unfoldableHead]
  generalize x.getAppFn = g
  cases g <;> try rfl
  rename_i n us
  simp only [exprConstName, exprConstLevels, exprTag]
  generalize env.find? n = o
  cases o with
  | none => rfl
  | some ci => cases ci <;> rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:115-125 unfoldDefinition — the
function as ONE equation: the unfolding exactly when the head is unfoldable
(`unfoldableHead_eq` rewrites the condition). -/
@[bridge_grind =] theorem unfoldDefinition_eq (x : Expr) : ConLeche.unfoldDefinition env x =
    if ConLeche.unfoldableHead env x = true then
      some (Expr.mkAppN ((cDefnValue (env.find? (exprConstName x.getAppFn))).instantiateLevelParams
        (cDefnVal (env.find? (exprConstName x.getAppFn))).levelParams (exprConstLevels x.getAppFn))
        x.getAppArgs)
    else none := by
  simp only [ConLeche.unfoldDefinition, ConLeche.unfoldableHead]
  split <;> rename_i hg
  · split
    · rename_i n us hfn
      simp only [hfn] at hg ⊢
      split at hg
      · rename_i cv value hint hf
        simp only [hf, exprConstName, exprConstLevels, cDefnValue, cDefnVal, beq_iff_eq] at hg ⊢
        simp only [hg, ite_true]
      · exact absurd hg (by simp)
    · rename_i hfn
      split at hg
      · rename_i n us h; exact absurd h (hfn n us)
      · exact absurd hg (by simp)
  · split
    · rename_i n us hfn
      simp only [hfn] at hg ⊢
      split
      · rename_i cv value hint hf
        simp only [hf, beq_iff_eq] at hg
        simp only [hg, ite_false]
      · rfl
    · rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:145-151 headHint — the function
as ONE equation: the hint at the head constant's name, `opaque` elsewhere. -/
@[bridge_grind =] theorem headHint_eq (x : Expr) : ConLeche.headHint env x =
    if exprTag x.getAppFn == ETag.const then cDefnHint (env.find? (exprConstName x.getAppFn))
    else .opaque := by
  simp only [ConLeche.headHint]
  generalize x.getAppFn = g
  cases g <;> rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:157-170 unfoldableHead —
**THEOREM 1 for `unfoldableHead`**: the delta step's DECISION, taken before
the unfolding is materialized.  Six verification
conditions — `getAppFn_spec`'s two preconditions, the dangling-level-list
failure arm (free), the definition arm, the not-a-definition arm and the
not-a-constant arm. -/
theorem unfoldableHead_spec (s₀ : AState) (e : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store e = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.unfoldableHead fe e
    ⦃fun b s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ b = ConLeche.unfoldableHead env x; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.unfoldableHead, ExprOps.getAppFn_spec coreWalkFuel] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:136-155 unfoldDefinition —
**THEOREM 1 for `unfoldDefinition`**: unfold the (application of a)
definition at the head, one step.  The pure side takes no fuel, so the
conclusion is an equation through `denoteEO` (`Bridge/Rel.lean`).

The spine rules are the `ExprOps` tier's, the index facts are this module's,
and the delta step's value is `constValAt_specA` — the ANSWER shape of
`Walks/Cached.lean`'s `constValAt_spec`, because the constant's name and
levels come out of `getAppFn`/`view`.

**The precondition `EnvWF env` is needed.**  The postcondition promises the unfolding is well-scoped at `d`, and that is
con-leche's `unfoldDefinition_WScoped` — whose own hypothesis is exactly
`EnvWF` (the stored VALUE is closed).  Without it the statement is false: a
definition whose stored value has a loose bound variable unfolds, in both
tiers, to a term that is not well-scoped, and nothing in `CheckOK` rules such
an environment out.  Its one caller, `Arms/Whnf.lean`'s `whnfBody_spec`,
takes `EnvWF` too. -/
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
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.unfoldDefinition, ExprOps.getAppFn_spec coreWalkFuel,
      ExprOps.getAppArgs_spec coreWalkFuel, mkAppN_specC (mode := mode) (env := env) (fe := fe),
      constValAt_specA (mode := mode) (env := env) (fe := fe)] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:172-181 headHint — **THEOREM
1 for `headHint`**: the reducibility hint of the constant at the head.
The answer type is one both tiers share, so the
relation is an equation, because con-leche's `headHint` takes no fuel.  Five verification conditions. -/
theorem headHint_spec (s₀ : AState) (e : EIdx) (x : Expr)
    (hok : CheckOK mode env fe s₀) (hden : denoteE s₀.store e = some x) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.headHint fe e
    ⦃fun h s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ h = ConLeche.headHint env x; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.headHint, ExprOps.getAppFn_spec coreWalkFuel] <;> finish

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:183-192 sameConstHeads —
**THEOREM 1 for `sameConstHeads`**: the lazy-delta same-head short-circuit.
It is DESIGN §8.3's *"index inequality IS
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

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:157-162 sameConstHeads — **the
function as ONE unconditional equation over tags and projections**: both
applications, both heads constants, the same name.  `grind`
rewrites the comparand with it and never splits the nested `match`. -/
@[bridge_grind =] theorem sameConstHeads_eq (x y : Expr) :
    ConLeche.sameConstHeads x y =
      (exprTag x == ETag.app && exprTag y == ETag.app &&
        exprTag (exprFn x).getAppFn == ETag.const &&
        exprTag (exprFn y).getAppFn == ETag.const &&
        exprConstName (exprFn x).getAppFn == exprConstName (exprFn y).getAppFn) := by
  cases x <;> cases y <;> try rfl
  rename_i f₁ a₁ f₂ a₂
  simp only [ConLeche.sameConstHeads, exprFn]
  generalize f₁.getAppFn = g₁
  generalize f₂.getAppFn = g₂
  cases g₁ <;> cases g₂ <;> rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:183-192 sameConstHeads —
**THEOREM 1 for `sameConstHeads`**: the lazy-delta same-head short-circuit.
Thirteen verification conditions, the most of the three, because the walk
peels two subjects.  The views and tags are `Bridge/Grind.lean` §6's
equations, the comparand is
`sameConstHeads_eq`, and the name guard is `idxOfName`'s congruence. -/
theorem sameConstHeads_spec (s₀ : AState) (a b : EIdx) (x y : Expr)
    (hok : CheckOK mode env fe s₀) (hda : denoteE s₀.store a = some x)
    (hdb : denoteE s₀.store b = some y) :
    ⦃fun s => s = s₀⦄ ConRon.Arena.sameConstHeads a b
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧ r = ConLeche.sameConstHeads x y; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.sameConstHeads, ExprOps.getAppFn_spec coreWalkFuel] <;> finish

/-! ### `defeqSpine`

Its callees are `getAppFn_spec` and `getAppArgs_spec` (the `ExprOps`
import, §0c), `lvlsEq?_spec` (at the equation, so at both signs), and
`defEqList_goA` (above).  Twenty
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

/-- con-leche: none — the list comparison's answer at optional subjects
(`defEqList_go`'s, as a named predicate on the two denotation terms). -/
def ListDefEq (mode : CheckMode) (env : Env) (d : Nat) :
    Option (List Expr) → Option (List Expr) → Bool → Prop
  | some xs, some ys, r => SimBOp (fun F => ConLeche.defEqListFueled mode env F d xs ys) r
  | _, _, _ => True

/-- con-leche: ConLeche/Kernel/Core.lean:1213-1222 defEqList — `Walks/Owed.lean`'s
`defEqList_go` with `OptAllWS` preconditions and a `ListDefEq` answer (no
`∃` to prove, no `∀` to instantiate). -/
theorem defEqList_goA {fuel : Nat} (hsim : KnotSpec mode env fe fuel) (d : Nat)
    (as bs : List EIdx) (s₀ : AState) (hok : CheckOK mode env fe s₀)
    (ha : OptAllWS d (Frontend.denoteEList s₀.store as))
    (hb : OptAllWS d (Frontend.denoteEList s₀.store bs)) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.defEqList (coreKnot mode fe id fuel) fe d as bs
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ListDefEq mode env d (Frontend.denoteEList s₀.store as)
          (Frontend.denoteEList s₀.store bs) r; ⊤⦄ := by
  cases hxa : Frontend.denoteEList s₀.store as with
  | none => rw [hxa] at ha; exact ha.elim
  | some xs =>
  cases hyb : Frontend.denoteEList s₀.store bs with
  | none => rw [hyb] at hb; exact hb.elim
  | some ys =>
  rw [hxa] at ha; rw [hyb] at hb
  refine triple_mono (defEqList_go hsim d as bs s₀ hok ⟨xs, hxa, ha⟩ ⟨ys, hyb, hb⟩) ?_
  rintro r s' ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, h4 xs ys hxa hyb⟩

/-- con-leche: ConLeche/Kernel/Core.lean:1291-1303 defeqSpine — `defeqSpine`'s
answer, named (the statement's `SimBOp (fun F => …)`, which `grind` must not
see as a `fun`). -/
def SpineDefEq (mode : CheckMode) (env : Env) (d : Nat) (x y : Expr) (r : Bool) : Prop :=
  SimBOp (fun F => ConLeche.defeqSpineFueled mode env F d x y) r

/-- con-leche: ConLeche/Kernel/Core.lean:1291-1303 defeqSpine — the answer as
ONE equation over tags and projections: the spines' comparison when the heads
are the same constant with level-equivalent universes and the spines have one
length, `false` otherwise (the fuel is the same on both sides). -/
@[bridge_grind =] theorem spineDefEq_eq (d : Nat) (x y : Expr) (r : Bool) :
    SpineDefEq mode env d x y r =
      (if (exprTag x.getAppFn == ETag.const && exprTag y.getAppFn == ETag.const &&
          exprConstName x.getAppFn == exprConstName y.getAppFn &&
          x.getAppArgs.length == y.getAppArgs.length &&
          Level.isEquivList (exprConstLevels x.getAppFn) (exprConstLevels y.getAppFn)
            == some true) = true
        then ListDefEq mode env d (some x.getAppArgs) (some y.getAppArgs) r else r = false) := by
  have hfalse : (∃ F : Nat, (pure false : CheckM Bool) = .ok r) = (r = false) :=
    propext ⟨fun ⟨_, h⟩ => (Except.ok.inj h).symm, fun h => ⟨0, h ▸ rfl⟩⟩
  have hnc : ∀ g : Expr, (∀ n us, g = .const n us → False) →
      (exprTag g == ETag.const) = false := by
    intro g hg; cases g <;> first | rfl | exact absurd rfl (hg _ _)
  simp only [SpineDefEq, SimBOp, ListDefEq, ConLeche.defeqSpineFueled,
    ConLeche.defEqListFueled, ConLeche.defeqSpine]
  split
  · rename_i n us hx
    split
    · rename_i n' us' hy
      simp only [hx, hy, exprTag, exprConstName, exprConstLevels, beq_self_eq_true,
        Bool.true_and]
      by_cases hc : n = n' ∧ x.getAppArgs.length = y.getAppArgs.length
      · obtain ⟨rfl, hl⟩ := hc
        simp only [hl, and_self, ite_true, beq_self_eq_true, Bool.true_and]
        cases Level.isEquivList us us' with
        | none => simp [hfalse]
        | some v => cases v <;> simp [hfalse]
      · simp only [hc, ite_false, hfalse]
        have : (n == n' && x.getAppArgs.length == y.getAppArgs.length) = false := by
          simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
          by_cases h1 : n = n'
          · exact Or.inr (fun h2 => hc ⟨h1, h2⟩)
          · exact Or.inl h1
        simp [this]
    · rename_i hy
      simp [hnc _ hy, hfalse]
  · rename_i hx
    simp [hnc _ hx, hfalse]

/-- con-leche: ConLeche/Kernel/Core.lean:1420-1439 defeqSpine — **THEOREM 1
for `defeqSpine`**: two applications of the same constant are defeq if their
universe arguments and their argument vectors are.

Two of DESIGN §8.3's "index inequality IS structural inequality" in one
guard: the twin tests `n = n'` on `NIdx` where con-leche tests `Name`
equality (`name_eq_iff_of_denoteN`, both directions), and `aa.length =
bb.length` on handle lists where con-leche tests the denoted spines'
(`denoteEList_len`, both directions).  The walk DECLINES on either, so both
are needed at both signs — `lvlEq?_spec`'s rule at a compound guard. -/
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
  show ⦃fun s => s = s₀⦄ _ ⦃fun r s' => _ ∧ _ ∧ _ ∧ SpineDefEq mode env d x y r; ⊤⦄
  sym only [bridge_grind] =>
    vcgen [ConRon.Arena.defeqSpine, ExprOps.getAppFn_spec coreWalkFuel,
      ExprOps.getAppArgs_spec coreWalkFuel, lvlsEq?_spec (mode := mode) (env := env) (fe := fe),
      defEqList_goA hsim d] <;> finish

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
  sym only [bridge_grind] =>
    vcgen [ExprOps.instantiate1Fast_spec fuel s₀ e v d ve hok hve hden] <;> finish

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

Its PURE side is `Walks/Owed.lean`'s step equations
(`etaCertFueled_notNeutral`, `_nf`, `_dom`, `_body`, `_trusted`, `_tax`),
and the one callee rule whose published shape it cannot use is restated
above (`instantiate1Fast_specE`).  The arena side is twenty-three
verification conditions — the three knot calls
in their primed shape, two `internE`s with their `ViewOK` obligations, one
`instantiate1Fast`, and the well-scopedness of the opened body at `d + 1`
(con-leche's `WScoped.instantiate1` and `WScoped.mono` are exactly it).  The
statement's FOUR subjects are the λ's two children, its binder datum and the
comparand — the `lam` step of an answer relation, at the level of a whole
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
#print axioms denoteCV_inv
#print axioms denote_not_const
#print axioms denote_not_app
#print axioms beq_of_denoteN
#print axioms name_eq_iff_of_denoteN
#print axioms instantiate1Fast_specE
/-! **The walks of this module.** -/
#print axioms unfoldableHead_spec
#print axioms headHint_spec
#print axioms sameConstHeads_spec
#print axioms defeqSpine_spec
#print axioms view_len_of_denoteLs
#print axioms denote_not_forallE
#print axioms unfoldDefinition_spec
#print axioms etaCert_spec
/-! The restated callees and the equations. -/
#print axioms constValAt_specA
#print axioms defEqList_goA
#print axioms mkAppN_specC
#print axioms unfoldDefinition_eq
#print axioms spineDefEq_eq
#print axioms sameConstHeads_eq

end Census

end ConRon.Bridge.Core

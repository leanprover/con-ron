/-
# `ConRon.Bridge.Specs` — one `@[spec]` theorem per `Monad.lean` primitive

The thing task #97s's spike exists to fix: **one spec theorem per (B)
primitive, in one shape**, so that the verification-condition generator
(`mvcgen` until task #111, `vcgen` since, on native `Std.WP` triples since
task #111 slice 2) can walk a twin's body without any store reasoning
appearing in the proof text.  The shape is the spike's
seven-rule template (DESIGN §8.6, `P2s SPIKE`, and task #97s's own section):

```lean
@[spec] theorem f_spec (s₀ : AState) (args…) (pre…) :
    ⦃fun s => s = s₀⦄ f args ⦃fun r s' => Post s₀ r s'; ⊤⦄
```

1. **the precondition is `s = s₀` and nothing else** — every real
   precondition is an ordinary hypothesis of the theorem, so `vcgen` turns it
   into a side goal instead of an entailment to discharge in the logic;
2. **exception postcondition `⊤` (partial correctness), never the default
   `⊥`** (`⦃P⦄ x ⦃Q⦄` is TOTAL correctness in `Std.WP`) — a (B) function may
   fail and Theorem 1 claims nothing then (con-leche's `SimAt`,
   `Verify/SimI.lean:244`);
3. **the postcondition names `s₀`**, the only way to state
   `Ext s₀.store s'.store` in a triple;
4. **"the subject denotes" is an `isSome`, never a named `Expr`**;
5. **the answer is a named relation** (`Bridge/Rel.lean`'s `RelE` family),
   never a bare `∀ e, … → …`;
6. **a memo insert's spec states that the INVARIANT is preserved**, not that
   the table grew — the single highest-value change of the spike;
7. **one named failure primitive** (`fail`), because a bare `throw` in
   `StateT σ (Except ε)` leaves `mvcgen` with universe metavariables.

## The frame conditions

`AState` has four fields and the `Memos` record has thirteen tables, so a
naive frame condition would be sixteen equations per spec.  Task #97b put the
per-call tables in ONE record and task #97c the per-declaration ones in
another for exactly this reason: every spec below frames the state in at most
four equations, and a memo write frames the other twelve tables with one
(`s'.memos = { s₀.memos with xC := … }`).

`Bridge/StateOK.lean`'s `CheckOK.mono` is what those equations buy: the whole
checker invariant crosses an `ExprOps` call on `Ext` plus
`s'.caches = s₀.caches` plus `s'.pins = s₀.pins`.

## What is NOT here, and why

* **`internPersistentE` / `…N` / `…L` / `…Ls`.**  `Arena/Store.lean`'s own
  note (the section "Interning into the PERSISTENT tier") states the
  obligation for the BRACKET and not for the operation: `internPersistent`
  breaks `fresh` transiently, and it is `promote … dropScratch` as a whole
  that takes `StoreWF` to `StoreWF`.  Its four specs therefore belong to the
  `Promote` tier, whose statement is that bracket, not to this file.
* **the eleven `internRebuilt*` faces of `ExprOps.lean`** are here, at the
  end: they are `internE` plus task #97-P6-5's upward cutoff, and every
  rebuilding walk goes through them.

## The closer

`bridge_vcs` at the end of this file is task #97s round 2's recipe: ONE
curated `grind` list, a `bridge_peel` in front of it, and a second stage that
puts the `RelE` transports back for the handful of verification conditions
that genuinely have to move an answer along the extension chain.  The arm
files erase the transports from `grind`'s set with `attribute [-grind]`
(round 2's item 1, worth 70 s → 11.5 s on the spike's one file), and because
`attribute [-grind]` does not travel through an import each of them repeats
the line.
-/
import ConRon.Bridge.StateOK
import ConRon.Bridge.StoreNested
import ConRon.Bridge.StoreBind
import ConRon.Arena.PersistentRun
import Std.WP
-- the `vcgen` syntax on v4.35.0-rc3 (lean4#15290 moves it to `Std.WP.Tactic`)
import Std.Tactic.Do

namespace ConRon.Bridge

set_option autoImplicit false
set_option experimental.vcgen true

open ConLeche ConRon.Arena Std.WP
open scoped Lean.Order

/-! ## The derived `match` auxiliaries, given an owner (task #97-P3-ExprOps
round 4)

**The clash `lakefile.toml` and `Bridge/Core/Walks/Spine.lean` both record.**
`grind` derives a congruence auxiliary for the `match` of an
`Arena/**` definition *on demand*, into whatever module first needs it, under
a deterministic PUBLIC name — `<f>.match_1.congr_eq_1._sparseCasesOn_2`.  Two
modules that each derive the same one cannot then sit in one import closure:

    import ConRon.Bridge.Core.EnsureSort failed, environment already contains
    'ConRon.Arena.piResultIsProp.match_1.congr_eq_1._sparseCasesOn_2'
    from ConRon.Bridge.Core.Walks.Owed

That is what forced `Bridge/Core/Walks/Spine.lean` into a sibling module off
the knot-facing chain, and what `Arms/{InferIO,Infer}` — both ON the chain and both
calling `ensureSort` — would hit next.

**The repair is to give the auxiliary ONE owner, and this file is it**: every
module of `ConRon/Bridge/**` imports it, and a derivation finds an imported
one and reuses it rather than adding a second.  That was measured, not
assumed: a module carrying `mvcgen [forallPw]` and importing a module
carrying only the two lines below re-uses the owner's auxiliary
(`getModuleIdxFor?` names the owner) and adds nothing.

**The spelling matters** (the `Refine2/Core/Eqns.lean` precedent).  What
forces the derivation is a `grind` on a goal whose head IS the matcher and
which cannot be closed without splitting it; a `grind` on `f x = f x`, or one
whose goal is `True`, closes first and derives nothing.  Hence the shape
below: the matcher at `motive := fun _ => Nat`, one branch `1`, the catch-all
`0`, and `≤ 1` as the claim.  It costs this file under a second per matcher
and it names no fact anyone has to maintain.

Add a line here when a new clash appears; the auxiliary's name in the error
message says which matcher to force. -/

/-- con-leche: none — `ConRon.Arena.isCtorApp`'s (`Core/Walks/Guards.lean`
against `Core/Walks/Spine.lean`). -/
theorem matchOwner_isCtorApp (x : ENodeView) :
    ConRon.Arena.isCtorApp.match_1 (motive := fun _ => Nat) x
      (fun _ _ => 1) (fun _ => 0) ≤ 1 := by
  grind

/-- con-leche: none — `ConRon.Arena.proofIrrel`'s (`Core/Walks/PropRead.lean`
against `Core/EnsureSort.lean`'s closure, task #105: the `.sort` view match
it shares with `ensureSort`). -/
theorem matchOwner_proofIrrel (x : ENodeView) :
    ConRon.Arena.proofIrrel.match_1 (motive := fun _ => Nat) x
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  grind

/-- con-leche: none — `ConRon.Arena.denoteLs`' (`Frontend` against
`Inductives`). -/
theorem matchOwner_denoteLs (x : Option LsNodeView) :
    ConRon.Arena.denoteLs.match_1 (motive := fun _ => Nat) x
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  grind

/-- con-leche: none — the five `instantiate1Arm*` probe matches, shared by
`ExprOps/{Abs,Inst1,Subst}.lean`.  They are the `Option` shape of a
memo probe and of a `viewApp`/`viewBind` projection, so every rebuilding
walk of the tier grinds over one. -/
theorem matchOwner_instantiate1ArmApp (x : Option (EIdx × EIdx)) :
    ConRon.Arena.instantiate1ArmApp.match_1 (motive := fun _ => Nat) x
      (fun _ => 1) (fun _ _ => 0) ≤ 1 := by
  grind

theorem matchOwner_instantiate1ArmApp3 (x : Option EIdx) :
    ConRon.Arena.instantiate1ArmApp.match_3 (motive := fun _ => Nat) x
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  grind

theorem matchOwner_instantiate1ArmBVar (x : Option Nat) :
    ConRon.Arena.instantiate1ArmBVar.match_1 (motive := fun _ => Nat) x
      (fun _ => 1) (fun _ => 0) ≤ 1 := by
  grind

theorem matchOwner_instantiate1ArmLet (x : Option (EIdx × EIdx × EIdx)) :
    ConRon.Arena.instantiate1ArmLet.match_1 (motive := fun _ => Nat) x
      (fun _ => 1) (fun _ _ _ => 0) ≤ 1 := by
  grind

theorem matchOwner_instantiate1ArmProj (x : Option (NIdx × Nat × EIdx)) :
    ConRon.Arena.instantiate1ArmProj.match_1 (motive := fun _ => Nat) x
      (fun _ => 1) (fun _ _ _ => 0) ≤ 1 := by
  grind

/-- con-leche: none — the two TEN-way `ENodeView` dispatch matches:
`fvarLeaves` (`ExprOps/{Leaves,Walks}.lean`) and `liftLooseBVarsGo`
(`ExprOps/{Abs,Ranges,Walks}.lean`).  Ten `congr_eq`s each, and one `grind`
derives all ten. -/
theorem matchOwner_fvarLeaves (x : ENodeView) :
    ConRon.Arena.fvarLeaves.match_1 (motive := fun _ => Nat) x
      (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1)
      (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ => 1) (fun _ => 1)
      (fun _ _ => 1) (fun _ => 0) ≤ 1 := by
  grind

theorem matchOwner_liftLooseBVarsGo (x : ENodeView) :
    ConRon.Arena.liftLooseBVarsGo.match_1 (motive := fun _ => Nat) x
      (fun _ => 1) (fun _ _ => 1) (fun _ => 1) (fun _ _ => 1) (fun _ => 1)
      (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ _ => 1)
      (fun _ _ _ => 0) ≤ 1 := by
  grind

/-! ## The failure primitives (template rule 7) -/

/-! ### The failure specs (task #111)

With a SCHEMATIC postcondition `Q`: a `fail` never returns and the
exception postcondition is `⊤`, so `fail` establishes any `Q` and the failing
branch of a twin leaves no verification condition at all.  The `mvcgen`-era
specs they replaced (task #111) had a `False` postcondition and left one
`False` barrel per failure site, closed under `mvcgen` by a `spec_fails`
macro; both are gone. -/

/-- con-leche: ConLeche/Kernel/Core.lean:53-72 CheckError — `fail` meets
every postcondition under partial correctness. -/
@[spec] theorem fail_wp {α : Type} (e : Arena.CheckError) (Q : α → AState → Prop) :
    ⦃fun _ => True⦄ (fail e : AM α) ⦃Q; ⊤⦄ :=
  AM.triple_of_run fun _ _ _ _ h => nomatch h

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — `failDanglingE`,
ditto. -/
@[spec] theorem failDanglingE_wp {α : Type} (Q : α → AState → Prop) :
    ⦃fun _ => True⦄ (failDanglingE : AM α) ⦃Q; ⊤⦄ :=
  AM.triple_of_run fun _ _ _ _ h => nomatch h

/-- con-leche: ConLeche/Kernel/Expr.lean:41-54 Level — `failDanglingLs`,
ditto. -/
@[spec] theorem failDanglingLs_wp {α : Type} (Q : α → AState → Prop) :
    ⦃fun _ => True⦄ (failDanglingLs : AM α) ⦃Q; ⊤⦄ :=
  AM.triple_of_run fun _ _ _ _ h => nomatch h

/-! ## The expression store: `view`, `derivedE`, `internE` -/

/-- con-leche: ConLeche/Kernel/Expr.lean:344-354 Expr — `view` does not touch
the state and returns the store's own decoding. -/
@[spec] theorem view_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => s = s₀⦄ view h
    ⦃fun v s' => s' = s₀ ∧ s₀.store.view h = some v; ⊤⦄ := by
  vcgen [view] with finish

/-- con-leche: none — **`view`, as a run**: it moves nothing and answers the
store's own decoding.  The first line of every walk of this tier. -/
theorem view_run {s s' : AState} {h : EIdx} {v : ENodeView}
    (hrun : view h s = .ok (v, s')) : s' = s ∧ s.store.view h = some v :=
  AM.of_run (P := fun t => t = s) rfl hrun (view_spec s h)

/-! ## Readback injectivity, handle equality and the view frame

Facts every tier reads about the denotation functions of
`Arena/Frontend/Readback.lean` and `Arena/Denote.lean`, stated once here. -/

/-- con-leche: none — `Frontend.denoteEList` is injective; the list twin of
`Arena/WFProofs.lean`'s `denoteE_inj` (the level tier's `denoteLList_inj` is
already there). -/
theorem denoteEList_inj {st : EStore} (hwf : StoreWF st) :
    ∀ (is js : List EIdx) (xs : List Expr),
      Frontend.denoteEList st is = some xs →
      Frontend.denoteEList st js = some xs → is = js := by
  intro is
  induction is with
  | nil =>
    intro js xs hi hj
    simp only [Frontend.denoteEList, Option.some.injEq] at hi
    subst hi
    cases js with
    | nil => rfl
    | cons b bs =>
      simp only [Frontend.denoteEList] at hj
      cases hb : denoteE st b with
      | none => rw [hb] at hj; simp at hj
      | some y =>
        cases hbs : Frontend.denoteEList st bs with
        | none => rw [hb, hbs] at hj; simp at hj
        | some ys => rw [hb, hbs] at hj; simp at hj
  | cons a as ih =>
    intro js xs hi hj
    simp only [Frontend.denoteEList] at hi
    cases ha : denoteE st a with
    | none => rw [ha] at hi; simp at hi
    | some x =>
      cases has : Frontend.denoteEList st as with
      | none => rw [ha, has] at hi; simp at hi
      | some xt =>
        rw [ha, has] at hi
        simp only [Option.some.injEq] at hi
        subst hi
        cases js with
        | nil => simp only [Frontend.denoteEList] at hj; simp at hj
        | cons b bs =>
          simp only [Frontend.denoteEList] at hj
          cases hb : denoteE st b with
          | none => rw [hb] at hj; simp at hj
          | some y =>
            cases hbs : Frontend.denoteEList st bs with
            | none => rw [hb, hbs] at hj; simp at hj
            | some yt =>
              rw [hb, hbs] at hj
              simp only [Option.some.injEq, List.cons.injEq] at hj
              obtain ⟨rfl, rfl⟩ := hj
              rw [denoteE_inj hwf ha hb, ih bs _ has hbs]

/-- con-leche: none — `Frontend.denoteNList` is injective; `denoteEList_inj`'s
twin at the NAME store, off `Arena/WFProofs.lean`'s `denoteN_inj`.  The
`.projInfo` comparison (`denoteProjTable_inj`) needs it at `levelParams`. -/
theorem denoteNList_inj {st : EStore} (hwf : StoreWF st) :
    ∀ (as bs : List NIdx) (xs : List ConLeche.Name),
      Frontend.denoteNList st.ns as = some xs →
      Frontend.denoteNList st.ns bs = some xs → as = bs := by
  obtain ⟨rk, hrk⟩ := hwf
  intro as
  induction as with
  | nil =>
    intro bs xs ha hb
    simp only [Frontend.denoteNList, Option.some.injEq] at ha
    subst ha
    cases bs with
    | nil => rfl
    | cons b bt =>
      simp only [Frontend.denoteNList] at hb
      cases hbh : denoteN st.ns b with
      | none => rw [hbh] at hb; simp at hb
      | some y =>
        cases hbt : Frontend.denoteNList st.ns bt with
        | none => rw [hbh, hbt] at hb; simp at hb
        | some ys => rw [hbh, hbt] at hb; simp at hb
  | cons a at_ ih =>
    intro bs xs ha hb
    simp only [Frontend.denoteNList] at ha
    cases hah : denoteN st.ns a with
    | none => rw [hah] at ha; simp at ha
    | some x =>
      cases hat : Frontend.denoteNList st.ns at_ with
      | none => rw [hah, hat] at ha; simp at ha
      | some xt =>
        rw [hah, hat] at ha
        simp only [Option.some.injEq] at ha
        subst ha
        cases bs with
        | nil => simp only [Frontend.denoteNList] at hb; simp at hb
        | cons b bt =>
          simp only [Frontend.denoteNList] at hb
          cases hbh : denoteN st.ns b with
          | none => rw [hbh] at hb; simp at hb
          | some y =>
            cases hbt : Frontend.denoteNList st.ns bt with
            | none => rw [hbh, hbt] at hb; simp at hb
            | some yt =>
              rw [hbh, hbt] at hb
              simp only [Option.some.injEq, List.cons.injEq] at hb
              obtain ⟨rfl, rfl⟩ := hb
              rw [denoteN_inj hrk.nsWF hah hbh, ih bt _ hat hbt]

/-- con-leche: none — a name-handle list and its denotation are equally
long. -/
theorem denoteNList_length {ns : NStore} :
    ∀ (hs : List NIdx) (xs : List ConLeche.Name),
      Frontend.denoteNList ns hs = some xs → hs.length = xs.length := by
  intro hs
  induction hs with
  | nil => intro xs h; simp only [Frontend.denoteNList, Option.some.injEq] at h
           subst h; rfl
  | cons a as ih =>
    intro xs h
    simp only [Frontend.denoteNList] at h
    cases ha : denoteN ns a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteNList ns as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [ih ys has]

/-- con-leche: none — DESIGN §8.3 at the expression store. -/
theorem beq_of_denoteE {st : EStore} (hwf : StoreWF st) {i j : EIdx}
    {x y : Expr} (hi : denoteE st i = some x) (hj : denoteE st j = some y) :
    (i == j) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · rintro rfl; rw [hi] at hj; exact Option.some.inj hj
  · rintro rfl; exact denoteE_inj hwf hi hj

/-- con-leche: none — a pinned name handle against a denoted one: the `==`
of the twin is con-leche's `==` of the names. -/
theorem beq_handle_eq {st : EStore} (hwf : StoreWF st) {c n : NIdx}
    {nm y : ConLeche.Name} (hn : denoteN st.ns c = some nm)
    (hy : denoteN st.ns n = some y) : (c == n) = (nm == y) := by
  obtain ⟨rk, hrk⟩ := hwf
  cases hb : c == n with
  | true =>
    obtain rfl := eq_of_beq hb
    rw [hn] at hy
    obtain rfl := Option.some.inj hy
    simp
  | false =>
    symm
    rw [beq_eq_false_iff_ne]
    intro heq
    subst heq
    have hne : (c == n) = true := beq_iff_eq.mpr (denoteN_inj hrk.nsWF hn hy)
    rw [hb] at hne
    exact absurd hne (by simp)

/-- con-leche: none — and so a handle-LIST comparison is a structural one. -/
theorem beq_of_denoteEList {st : EStore} (hwf : StoreWF st)
    {as bs : List EIdx} {xs ys : List Expr}
    (ha : Frontend.denoteEList st as = some xs)
    (hb : Frontend.denoteEList st bs = some ys) : (as == bs) = (xs == ys) := by
  cases h1 : as == bs with
  | true =>
    obtain rfl := eq_of_beq h1
    rw [ha] at hb
    obtain rfl := Option.some.inj hb
    simp
  | false =>
    symm
    rw [beq_eq_false_iff_ne]
    intro heq
    subst heq
    have hne : (as == bs) = true := beq_iff_eq.mpr (denoteEList_inj hwf _ _ _ ha hb)
    rw [h1] at hne
    exact absurd hne (by simp)

/-- con-leche: none — a universe-argument list handle that denotes has a
view. -/
theorem lsview_isSome_of_denote {st : LsStore} {c : LsIdx} {us : List Level}
    (hd : denoteLs st c = some us) : (st.view c).isSome = true := by
  obtain ⟨v, hv, _⟩ := denoteLs_view hd
  rw [hv]; rfl

/-- con-leche: none — the `fvar` index projection read means the type
projection reads too (one row of the `fvar` array): `TagFirst`'s
`viewFVarIdx_of_viewFVarTy`, the other way. -/
theorem viewFVarTy_of_viewFVarIdx {st : EStore} {i : EIdx} {k : Nat}
    (h : st.viewFVarIdx i = some k) : ∃ ty, st.viewFVarTy i = some ty := by
  unfold EStore.viewFVarIdx at h
  unfold EStore.viewFVarTy EStore.persGetFVarTy
  unfold EStore.persGetFVarIdx at h
  split at h
  · simp only [ETables.getFVarIdx, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, -⟩ := h
    exact ⟨r.ty, by simp [*, ETables.getFVarTy]⟩
  · split at h
    · simp only [ETables.getFVarIdx, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, -⟩ := h
      exact ⟨r.ty, by simp [*, ETables.getFVarTy]⟩
    · cases h

/-- con-leche: ConLeche/Kernel/Expr.lean:344-403 Expr — `derivedE` does not
touch the state and returns the packed word; with `EStore.derived_exact` that
word is `e.data` for the denoted `e`, which is what every cutoff reads. -/
@[spec] theorem derivedE_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => s = s₀⦄ derivedE h
    ⦃fun w s' => s' = s₀ ∧ w = s₀.store.derived h; ⊤⦄ := by
  vcgen [derivedE] with finish

/-! ### The two binder faces

`internLamE` / `internForallEE` do NOT go through `internNodeE`: they call
`EStore.internLam` / `internForallE` at the binder RECORD.
`Bridge/StoreBind.lean`'s `EStore.internBind_spec` is the store fact; the two
specs below are that fact under the monadic wrapper's own capacity branch.

Both wrappers PROBE FIRST, as `internNodeE` does, so each proof has two arms:
the cons HIT, where the store does not move and `EStore.view_of_findBind`
names the handle's view, and the MISS, which is `internBind_spec` at the tier
the append goes to. -/

theorem internLamE_spec_view (s₀ : AState) (ty b : EIdx)
    (hwf : StoreWF s₀.store) (hty : (s₀.store.view ty).isSome = true)
    (hb : (s₀.store.view b).isSome = true) :
    ⦃fun s => s = s₀⦄ internLamE ty b
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.lam ty b) ∧
        denoteE s'.store h = denoteEView s'.store (.lam ty b); ⊤⦄ := by
  vcgen [internLamE]
  -- **The cons HIT**: the probe comes first, so this arm answers the handle
  -- the `lams` table already holds and moves nothing.
  case vc1 =>
    rename_i hs i hfind
    subst hs
    have hview := EStore.view_of_findBind (tag := ETag.lam) hwf (by decide) hfind
    have heb : eBindView ETag.lam ty b = ENodeView.lam ty b := by
      simp [eBindView]
    rw [heb] at hview
    obtain ⟨rk, hwf'⟩ := hwf
    exact ⟨⟨rk, hwf'⟩, Ext.refl _, rfl, rfl, rfl, rfl, rfl, hview,
      denoteE_unfold hwf' hview⟩
  rename_i hs _hfind hcap
  subst hs
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    EStore.internBind_spec (tag := ETag.lam) hwf (by decide) hty hb hcap
  have heb : eBindView ETag.lam ty b = ENodeView.lam ty b := by
    simp [eBindView]
  rw [heb] at h5 h6
  exact ⟨h1, h2, h3, h4, rfl, rfl, rfl, h5, h6⟩

theorem internForallEE_spec_view (s₀ : AState) (ty b : EIdx)
    (hwf : StoreWF s₀.store) (hty : (s₀.store.view ty).isSome = true)
    (hb : (s₀.store.view b).isSome = true) :
    ⦃fun s => s = s₀⦄ internForallEE ty b
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.forallE ty b) ∧
        denoteE s'.store h = denoteEView s'.store (.forallE ty b); ⊤⦄ := by
  vcgen [internForallEE]
  case vc1 =>
    rename_i hs i hfind
    subst hs
    have hview :=
      EStore.view_of_findBind (tag := ETag.forallE) hwf (by decide) hfind
    have heb : eBindView ETag.forallE ty b = ENodeView.forallE ty b := by
      simp [eBindView, ETag.lam, ETag.forallE]
    rw [heb] at hview
    obtain ⟨rk, hwf'⟩ := hwf
    exact ⟨⟨rk, hwf'⟩, Ext.refl _, rfl, rfl, rfl, rfl, rfl, hview,
      denoteE_unfold hwf' hview⟩
  rename_i hs _hfind hcap
  subst hs
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    EStore.internBind_spec (tag := ETag.forallE) hwf (by decide) hty hb hcap
  have heb : eBindView ETag.forallE ty b = ENodeView.forallE ty b := by
    simp [eBindView, ETag.lam, ETag.forallE]
  rw [heb] at h5 h6
  exact ⟨h1, h2, h3, h4, rfl, rfl, rfl, h5, h6⟩

/-- con-leche: none — `internLamE_spec_view` at denoting children: the face
the node-building walks use. -/
@[spec] theorem internLamE_spec (s₀ : AState) (ty b : EIdx)
    (hwf : StoreWF s₀.store) (hty : (denoteE s₀.store ty).isSome = true)
    (hb : (denoteE s₀.store b).isSome = true) :
    ⦃fun s => s = s₀⦄ internLamE ty b
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.lam ty b) ∧
        denoteE s'.store h = denoteEView s'.store (.lam ty b); ⊤⦄ :=
  internLamE_spec_view s₀ ty b hwf (view_isSome hty) (view_isSome hb)

/-- con-leche: none — and the `forallE` face. -/
@[spec] theorem internForallEE_spec (s₀ : AState) (ty b : EIdx)
    (hwf : StoreWF s₀.store) (hty : (denoteE s₀.store ty).isSome = true)
    (hb : (denoteE s₀.store b).isSome = true) :
    ⦃fun s => s = s₀⦄ internForallEE ty b
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.forallE ty b) ∧
        denoteE s'.store h = denoteEView s'.store (.forallE ty b); ⊤⦄ :=
  internForallEE_spec_view s₀ ty b hwf (view_isSome hty) (view_isSome hb)

/-- con-leche: none — the two binder arms at a tag the caller carries.  One
spec, stated at `eBindView`, so that a walk whose binder clause is shared
between `lam` and `forallE` needs no case split (which is the whole point of
the tag-carrying form).  The children are asked to have VIEWS (what the
rebuilding walks hold of the handles their recursion answered). -/
@[spec] theorem internBindE_spec (s₀ : AState) (tag : UInt32) (ty b : EIdx)
    (hwf : StoreWF s₀.store) (htag : ETag.isBind tag = true)
    (hty : (s₀.store.view ty).isSome = true)
    (hb : (s₀.store.view b).isSome = true) :
    ⦃fun s => s = s₀⦄ internBindE tag ty b
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (eBindView tag ty b) ∧
        denoteE s'.store h = denoteEView s'.store (eBindView tag ty b); ⊤⦄ := by
  rcases ETag.isBind_eq htag with rfl | rfl
  · simpa [internBindE, eBindView] using internLamE_spec_view s₀ ty b hwf hty hb
  · simpa [internBindE, eBindView, ETag.lam, ETag.forallE] using
      internForallEE_spec_view s₀ ty b hwf hty hb

/-- con-leche: none — **the eight non-binder arms**: a handle for the node, the
store still well formed, the arena only grown, the three other state fields
untouched, and the three nested stores literally unchanged (so a name or level
handle that had a view still has one).

The capacity test is `internNodeE`'s own branch (DESIGN §8.3: "the Rust raises
`Native` at the limit, the Lean `throw`s the same kind"), which is what
discharges `EStore.intern_spec`'s `capOK` hypothesis without a precondition
here — task #97a follow-up 3 made `capOK` *literally* that branch condition
for exactly this reason; its datum half is vacuous at a non-binder view. -/
theorem internNodeE_spec (s₀ : AState) (w : ENodeView)
    (hwf : StoreWF s₀.store) (hv : s₀.store.ViewOK w) :
    ⦃fun s => s = s₀⦄ internNodeE w
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some w ∧
        denoteE s'.store h = denoteEView s'.store w; ⊤⦄ := by
  vcgen [internNodeE]
  -- **The cons HIT** (task #97-P5-1's finding 9, fixed in the twin at
  -- #97-P3-1): `internNodeE` probes before it tests the capacity, exactly as
  -- the Rust does, so this branch answers the handle the cons table already
  -- holds and moves nothing.  `EStore.view_of_find` is `StoreWF`'s own
  -- `consP`/`consS` clause read left to right — no capacity in it.
  case vc1 =>
    rename_i hs i hfind
    subst hs
    have hview := EStore.view_of_find hwf hfind
    obtain ⟨rk, hwf'⟩ := hwf
    exact ⟨⟨rk, hwf'⟩, Ext.refl _, rfl, rfl, rfl, rfl, rfl, hview,
      denoteE_unfold hwf' hview⟩
  rename_i hs _hfind hcap
  subst hs
  obtain ⟨h1, h2, h3, h4⟩ := EStore.intern_spec hwf hv hcap
  exact ⟨h1, h2, EStore.lss_intern _ _,
    EStore.scratchOn_intern _ _, rfl, rfl, rfl, h3, h4⟩

/-- con-leche: none — `AM.of_run`'s converse at a fixed pre-state: a
partial-correctness triple from a statement about every accepting run. -/
theorem AM.triple_of_run_at {α : Type} {x : AM α} {s₀ : AState}
    {Q : α → AState → Prop}
    (h : ∀ r s', x s₀ = .ok (r, s') → Q r s') :
    ⦃fun s => s = s₀⦄ x ⦃fun r s' => Q r s'; ⊤⦄ :=
  AM.triple_of_run fun _ r s' hs hx => by subst hs; exact h r s' hx

/-- con-leche: none — **the one spec that carries the arena**: a handle for
the node, the store still well formed, the arena only grown, the three other
state fields untouched, and the three nested stores literally unchanged (so a
name or level handle that had a view still has one).

`internE` is the Rust's dispatch — the two binder arms `internLamE` /
`internForallEE`, the eight others `internNodeE` (`internNodeE_spec`) — so
this is a case split over the two. -/
@[spec] theorem internE_spec (s₀ : AState) (w : ENodeView)
    (hwf : StoreWF s₀.store) (hv : s₀.store.ViewOK w) :
    ⦃fun s => s = s₀⦄ internE w
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some w ∧
        denoteE s'.store h = denoteEView s'.store w; ⊤⦄ := by
  cases w
  case lam ty b =>
    exact internLamE_spec_view s₀ ty b hwf
      (hv.expr ty (by simp [ENodeView.echildren]))
      (hv.expr b (by simp [ENodeView.echildren]))
  case forallE ty b =>
    exact internForallEE_spec_view s₀ ty b hwf
      (hv.expr ty (by simp [ENodeView.echildren]))
      (hv.expr b (by simp [ENodeView.echildren]))
  all_goals exact internNodeE_spec s₀ _ hwf hv

/-! ### The ten per-constructor faces of `internE`

`Store.lean`'s own words: "the equation the bridge owes is
`internCE (fields) = internE (.C fields)`, `rfl`".  So each spec is
`internE_spec` at that constructor, and the `unfold` is the whole proof. -/

@[spec] theorem internBVarE_spec (s₀ : AState) (i : Nat)
    (hwf : StoreWF s₀.store) :
    ⦃fun s => s = s₀⦄ internBVarE i
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.bvar i) ∧
        denoteE s'.store h = denoteEView s'.store (.bvar i); ⊤⦄ :=
  internE_spec s₀ (.bvar i) hwf viewOK_bvar

@[spec] theorem internFVarE_spec (s₀ : AState) (idx : Nat) (ty : EIdx)
    (hwf : StoreWF s₀.store) (hty : (denoteE s₀.store ty).isSome = true) :
    ⦃fun s => s = s₀⦄ internFVarE idx ty
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.fvar idx ty) ∧
        denoteE s'.store h = denoteEView s'.store (.fvar idx ty); ⊤⦄ :=
  internE_spec s₀ (.fvar idx ty) hwf (viewOK_fvar hty)

@[spec] theorem internSortE_spec (s₀ : AState) (u : LIdx)
    (hwf : StoreWF s₀.store) (hu : (s₀.store.ls.view u).isSome = true) :
    ⦃fun s => s = s₀⦄ internSortE u
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.sort u) ∧
        denoteE s'.store h = denoteEView s'.store (.sort u); ⊤⦄ :=
  internE_spec s₀ (.sort u) hwf (viewOK_sort hu)

@[spec] theorem internAppE_spec (s₀ : AState) (f a : EIdx)
    (hwf : StoreWF s₀.store) (hf : (denoteE s₀.store f).isSome = true)
    (ha : (denoteE s₀.store a).isSome = true) :
    ⦃fun s => s = s₀⦄ internAppE f a
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.app f a) ∧
        denoteE s'.store h = denoteEView s'.store (.app f a); ⊤⦄ :=
  internE_spec s₀ (.app f a) hwf (viewOK_app hf ha)

@[spec] theorem internLetEE_spec (s₀ : AState) (ty val b : EIdx)
    (hwf : StoreWF s₀.store) (hty : (denoteE s₀.store ty).isSome = true)
    (hval : (denoteE s₀.store val).isSome = true)
    (hb : (denoteE s₀.store b).isSome = true) :
    ⦃fun s => s = s₀⦄ internLetEE ty val b
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.letE ty val b) ∧
        denoteE s'.store h = denoteEView s'.store (.letE ty val b); ⊤⦄ :=
  internE_spec s₀ (.letE ty val b) hwf (viewOK_letE hty hval hb)

@[spec] theorem internProjE_spec (s₀ : AState) (n : NIdx) (i : Nat) (e : EIdx)
    (hwf : StoreWF s₀.store) (hn : (s₀.store.ns.view n).isSome = true)
    (he : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => s = s₀⦄ internProjE n i e
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.lss = s₀.store.lss ∧ s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.view h = some (.proj n i e) ∧
        denoteE s'.store h = denoteEView s'.store (.proj n i e); ⊤⦄ :=
  internE_spec s₀ (.proj n i e) hwf (viewOK_proj hn he)

/-! ## The per-constructor projections of `view` (tasks #97-P6-10, #97-P6-13)

Thirteen specs, all of the same shape: the state does not move and the answer
is the store's own projection.  `Bridge/Rel.lean`'s group 6 turns each into a
`view` fact at the tag the caller has already tested. -/

@[spec] theorem viewApp_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => s = s₀⦄ viewApp h
    ⦃fun r s' => s' = s₀ ∧ r = s₀.store.viewApp h; ⊤⦄ := by
  vcgen [viewApp] with finish

@[spec] theorem viewBVar_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => s = s₀⦄ viewBVar h
    ⦃fun r s' => s' = s₀ ∧ r = s₀.store.viewBVar h; ⊤⦄ := by
  vcgen [viewBVar] with finish

@[spec] theorem viewSort_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => s = s₀⦄ viewSort h
    ⦃fun r s' => s' = s₀ ∧ r = s₀.store.viewSort h; ⊤⦄ := by
  vcgen [viewSort] with finish

@[spec] theorem viewConst_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => s = s₀⦄ viewConst h
    ⦃fun r s' => s' = s₀ ∧ r = s₀.store.viewConst h; ⊤⦄ := by
  vcgen [viewConst] with finish

@[spec] theorem viewFVarIdx_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => s = s₀⦄ viewFVarIdx h
    ⦃fun r s' => s' = s₀ ∧ r = s₀.store.viewFVarIdx h; ⊤⦄ := by
  vcgen [viewFVarIdx] with finish

@[spec] theorem viewFVarTy_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => s = s₀⦄ viewFVarTy h
    ⦃fun r s' => s' = s₀ ∧ r = s₀.store.viewFVarTy h; ⊤⦄ := by
  vcgen [viewFVarTy] with finish

@[spec] theorem viewLet_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => s = s₀⦄ viewLet h
    ⦃fun r s' => s' = s₀ ∧ r = s₀.store.viewLet h; ⊤⦄ := by
  vcgen [viewLet] with finish

@[spec] theorem viewProj_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => s = s₀⦄ viewProj h
    ⦃fun r s' => s' = s₀ ∧ r = s₀.store.viewProj h; ⊤⦄ := by
  vcgen [viewProj] with finish

@[spec] theorem viewBind_spec (s₀ : AState) (h : EIdx) :
    ⦃fun s => s = s₀⦄ viewBind h
    ⦃fun r s' => s' = s₀ ∧ r = s₀.store.viewBind h; ⊤⦄ := by
  vcgen [viewBind] with finish

/-! ## The name store -/

@[spec] theorem viewN_spec (s₀ : AState) (h : NIdx) :
    ⦃fun s => s = s₀⦄ viewN h
    ⦃fun v s' => s' = s₀ ∧ s₀.store.ns.view h = some v; ⊤⦄ := by
  vcgen [viewN] with finish

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — **the readback IS the
denotation** (DESIGN §8.3 lesson 4), so this spec is an equation and not a
simulation. -/
@[spec] theorem readName_spec (s₀ : AState) (h : NIdx) :
    ⦃fun s => s = s₀⦄ readName h
    ⦃fun x s' => s' = s₀ ∧ denoteN s₀.store.ns h = some x; ⊤⦄ := by
  vcgen [readName] with finish

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — the readback of a name
LIST, by induction on the list (the recursion `readNames` itself takes). -/
@[spec] theorem readNames_spec (s₀ : AState) (hs : List NIdx) :
    ⦃fun s => s = s₀⦄ readNames hs
    ⦃fun xs s' => s' = s₀ ∧ Frontend.denoteNList s₀.store.ns hs = some xs; ⊤⦄ := by
  induction hs generalizing s₀ with
  | nil => vcgen [readNames]; try grind [Frontend.denoteNList]
  | cons a as ih =>
    vcgen [readNames, ih]
    all_goals (bridge_peel; subst_vars; grind [Frontend.denoteNList])

/-- con-leche: none — hash-cons a name node, through the nesting.  The store
half is `Bridge/StoreNested.lean`'s `EStore.internName_spec`; this is that
fact under the wrapper's own capacity branch. -/
@[spec] theorem internNNode_spec (s₀ : AState) (v : NNodeView)
    (hwf : StoreWF s₀.store) (hv : s₀.store.ns.ViewOK v) :
    ⦃fun s => s = s₀⦄ internNNode v
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.pers = s₀.store.pers ∧ s'.store.scr = s₀.store.scr ∧
        s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.ns.view h = some v ∧
        denoteN s'.store.ns h = denoteNView s'.store.ns v; ⊤⦄ := by
  vcgen [internNNode]
  -- **The cons HIT** (task #97-P5-1's finding 9): the wrapper probes before
  -- it tests the capacity, exactly as the Rust does.
  case vc1 =>
    rename_i hs i hfind
    subst hs
    obtain ⟨rk, hwf'⟩ := hwf
    obtain ⟨rkn, hnw⟩ := hwf'.nsWF
    have hview := NStore.view_of_find ⟨rkn, hnw⟩ hfind
    exact ⟨⟨rk, hwf'⟩, Ext.refl _, rfl, rfl, rfl, rfl, rfl, rfl, hview,
      denoteN_unfold hnw hview⟩
  rename_i hs _hfind hcap
  subst hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    EStore.internName_spec hwf hv (by exact hcap)
  exact ⟨h1, h2, h3, h4, h5, rfl, rfl, rfl, h6, h7⟩

/-- con-leche: ConLeche/Kernel/Name.lean:34-37 Name — intern a transient
name, by induction on the `Name` tree (the recursion `internName` takes: a
`Name` is a value, not a DAG, so no fuel). -/
@[spec] theorem internName_spec (s₀ : AState) (nm : ConLeche.Name)
    (hwf : StoreWF s₀.store) :
    ⦃fun s => s = s₀⦄ internName nm
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.pers = s₀.store.pers ∧ s'.store.scr = s₀.store.scr ∧
        s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        denoteN s'.store.ns h = some nm; ⊤⦄ := by
  induction nm generalizing s₀ with
  | anonymous =>
    vcgen [internName, internNNode_spec]
    all_goals (bridge_peel; subst_vars
               grind [denoteNView, Arena.NStore.ViewOK, NNodeView.children])
  | str p str ih =>
    vcgen [internName, ih, internNNode_spec]
    all_goals (bridge_peel; subst_vars
               grind [denoteNView, Arena.NStore.ViewOK, NNodeView.children,
                 nview_isSome_of_denote, Ext.trans])
  | num p k ih =>
    vcgen [internName, ih, internNNode_spec]
    all_goals (bridge_peel; subst_vars
               grind [denoteNView, Arena.NStore.ViewOK, NNodeView.children,
                 nview_isSome_of_denote, Ext.trans])

/-! ## The level store -/

@[spec] theorem viewL_spec (s₀ : AState) (h : LIdx) :
    ⦃fun s => s = s₀⦄ viewL h
    ⦃fun v s' => s' = s₀ ∧ s₀.store.ls.view h = some v; ⊤⦄ := by
  vcgen [viewL] with finish

/-- con-leche: ConLeche/Kernel/Level.lean:26-37 subst — **the level readback
IS `denoteL`** (DESIGN §8.3 lesson 4: "intern the representation, not the
algorithm"), which is what makes every level-algorithm obligation a pure
`Level` fact. -/
@[spec] theorem readLevel_spec (s₀ : AState) (h : LIdx) :
    ⦃fun s => s = s₀⦄ readLevel h
    ⦃fun u s' => s' = s₀ ∧ denoteL s₀.store.ls h = some u; ⊤⦄ := by
  vcgen [readLevel] with finish

@[spec] theorem internLNode_spec (s₀ : AState) (v : LNodeView)
    (hwf : StoreWF s₀.store) (hv : s₀.store.ls.ViewOK v) :
    ⦃fun s => s = s₀⦄ internLNode v
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.pers = s₀.store.pers ∧ s'.store.scr = s₀.store.scr ∧
        s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.ls.view h = some v ∧
        denoteL s'.store.ls h = denoteLView s'.store.ls v; ⊤⦄ := by
  vcgen [internLNode]
  -- **The cons HIT** (task #97-P5-1's finding 9): the wrapper probes before
  -- it tests the capacity, exactly as the Rust does.
  case vc1 =>
    rename_i hs i hfind
    subst hs
    obtain ⟨rk, hwf'⟩ := hwf
    obtain ⟨rkl, hlw⟩ := hwf'.lsWF
    have hview := LStore.view_of_find ⟨rkl, hlw⟩ hfind
    exact ⟨⟨rk, hwf'⟩, Ext.refl _, rfl, rfl, rfl, rfl, rfl, rfl, hview,
      denoteL_unfold hlw hview⟩
  rename_i hs _hfind hcap
  subst hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    EStore.internLevel_spec hwf hv (by exact hcap)
  exact ⟨h1, h2, h3, h4, h5, rfl, rfl, rfl, h6, h7⟩

/-! ## The level-list store -/

@[spec] theorem viewLs_spec (s₀ : AState) (h : LsIdx) :
    ⦃fun s => s = s₀⦄ viewLs h
    ⦃fun v s' => s' = s₀ ∧ s₀.store.lss.view h = some v; ⊤⦄ := by
  vcgen [viewLs] with finish

@[spec] theorem viewLsLen_spec (s₀ : AState) (h : LsIdx) :
    ⦃fun s => s = s₀⦄ viewLsLen h
    ⦃fun r s' => s' = s₀ ∧ r = s₀.store.lss.viewLen h; ⊤⦄ := by
  vcgen [viewLsLen] with finish

@[spec] theorem readLevels_spec (s₀ : AState) (h : LsIdx) :
    ⦃fun s => s = s₀⦄ readLevels h
    ⦃fun us s' => s' = s₀ ∧ denoteLs s₀.store.lss h = some us; ⊤⦄ := by
  vcgen [readLevels] with finish

@[spec] theorem internLsNode_spec (s₀ : AState) (v : LsNodeView)
    (hwf : StoreWF s₀.store) (hv : s₀.store.lss.ViewOK v) :
    ⦃fun s => s = s₀⦄ internLsNode v
    ⦃fun h s' => StoreWF s'.store ∧ Ext s₀.store s'.store ∧
        s'.store.pers = s₀.store.pers ∧ s'.store.scr = s₀.store.scr ∧
        s'.store.scratchOn = s₀.store.scratchOn ∧
        s'.memos = s₀.memos ∧ s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.store.lss.view h = some v ∧
        denoteLs s'.store.lss h = denoteLsView s'.store.lss v; ⊤⦄ := by
  vcgen [internLsNode]
  -- **The cons HIT** (task #97-P5-1's finding 9): the wrapper probes before
  -- it tests the capacity, exactly as the Rust does.
  case vc1 =>
    rename_i hs i hfind
    subst hs
    obtain ⟨rk, hwf'⟩ := hwf
    have hview := LsStore.view_of_find hwf'.lssWF hfind
    exact ⟨⟨rk, hwf'⟩, Ext.refl _, rfl, rfl, rfl, rfl, rfl, rfl, hview,
      denoteLs_unfold hview⟩
  rename_i hs _hfind hcap
  subst hs
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    EStore.internLevels_spec hwf hv (by exact hcap)
  exact ⟨h1, h2, h3, h4, h5, rfl, rfl, rfl, h6, h7⟩

/-! ## The readback memos (task #97-P6-13)

The obligation is a MEMO obligation and not a new algorithm: `denoteL`,
`denoteN` and `denoteLs` are functions of the store, so a hit answers with the
row the miss stored.  Which is why these three specs have the SAME conclusion
as their unmemoised siblings, plus the cache frame.

**The frame is a record EQUATION and not a table equation** (task
#97-P3-CoreWalks): `s'.caches = { s₀.caches with readLC := s'.caches.readLC }`
says in one line that the call moved this readback memo and *none of the
other thirteen tables*, which is what a caller rebuilding `CheckOK` needs and
what the first spelling of these three omitted.  Without it no walk of
`Arena/Core.lean` that reads a name, a level or a universe-argument list back
could keep the state invariant, and — since `[spec]` cannot be erased — a
caller could not prove the missing conjunct for itself either.  It costs
these three proofs one `rfl` each. -/

@[spec] theorem readLevelM_spec (s₀ : AState) (h : LIdx)
    (hc : ReadLCacheOK s₀.caches.readLC s₀.store) :
    ⦃fun s => s = s₀⦄ readLevelM h
    ⦃fun u s' => s'.store = s₀.store ∧ s'.memos = s₀.memos ∧
        s'.pins = s₀.pins ∧
        s'.caches = { s₀.caches with readLC := s'.caches.readLC } ∧
        denoteL s₀.store.ls h = some u ∧
        ReadLCacheOK s'.caches.readLC s'.store; ⊤⦄ := by
  dsimp only
  vcgen [readLevelM]
  all_goals (bridge_peel; subst_vars) <;>
    first
    | (refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> grind [ReadLCacheOK])
    | (intro hf; exact False.elim hf)
    | grind [ReadLCacheOK]

@[spec] theorem readNameM_spec (s₀ : AState) (h : NIdx)
    (hc : ReadNCacheOK s₀.caches.readNC s₀.store) :
    ⦃fun s => s = s₀⦄ readNameM h
    ⦃fun x s' => s'.store = s₀.store ∧ s'.memos = s₀.memos ∧
        s'.pins = s₀.pins ∧
        s'.caches = { s₀.caches with readNC := s'.caches.readNC } ∧
        denoteN s₀.store.ns h = some x ∧
        ReadNCacheOK s'.caches.readNC s'.store; ⊤⦄ := by
  dsimp only
  vcgen [readNameM]
  all_goals (bridge_peel; subst_vars) <;>
    first
    | (refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> grind [ReadNCacheOK])
    | (intro hf; exact False.elim hf)
    | grind [ReadNCacheOK]

@[spec] theorem readLevelsM_spec (s₀ : AState) (h : LsIdx)
    (hc : ReadLsCacheOK s₀.caches.readLsC s₀.store) :
    ⦃fun s => s = s₀⦄ readLevelsM h
    ⦃fun us s' => s'.store = s₀.store ∧ s'.memos = s₀.memos ∧
        s'.pins = s₀.pins ∧
        s'.caches = { s₀.caches with readLsC := s'.caches.readLsC } ∧
        denoteLs s₀.store.lss h = some us ∧
        ReadLsCacheOK s'.caches.readLsC s'.store; ⊤⦄ := by
  dsimp only
  vcgen [readLevelsM]
  all_goals (bridge_peel; subst_vars) <;>
    first
    | (refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> grind [ReadLsCacheOK])
    | (intro hf; exact False.elim hf)
    | grind [ReadLsCacheOK]

/-! ## The thirteen memo tables

Three specs per handle-valued table — probe, record, drop — and the record's
spec states that the INVARIANT is preserved (template rule 6): `MemoOK` in
*goal* position is skolemised by `grind` into `∀ k r, …` before any lemma can
fire, so the invariant has to arrive as a hypothesis.

The frame is one equation for the other twelve tables
(`s'.memos = { s₀.memos with xC := … }`), which is what putting them in a
record bought. -/

@[spec] theorem inst1Get_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => s = s₀⦄ inst1Get k
    ⦃fun r s' => s' = s₀ ∧ r = s₀.memos.inst1C[k]?; ⊤⦄ := by
  vcgen [inst1Get] with finish

@[spec] theorem inst1Set_spec (s₀ : AState) (ve : Expr) (k : EIdx × Nat)
    (r : EIdx) (hm : Inst1MemoA ve s₀)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelE (fun e => Expr.instantiate1 e ve k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => s = s₀⦄ inst1Set k r
    ⦃fun _u s' => s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with inst1C := s₀.memos.inst1C.insert k r } ∧
        Inst1MemoA ve s'; ⊤⦄ := by
  dsimp only
  vcgen [inst1Set]
  rename_i hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoOK.insert hm rfl hk hr⟩

@[spec] theorem inst1Clear_spec (s₀ : AState) :
    ⦃fun s => s = s₀⦄ inst1Clear
    ⦃fun _u s' => s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with inst1C := ∅ } ∧
        ∀ ve, Inst1MemoA ve s'; ⊤⦄ := by
  dsimp only
  vcgen [inst1Clear]
  rename_i hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, fun _ => MemoOK.of_empty rfl⟩

@[spec] theorem instLGet_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => s = s₀⦄ instLGet k
    ⦃fun r s' => s' = s₀ ∧ r = s₀.memos.instLC[k]?; ⊤⦄ := by
  vcgen [instLGet] with finish

@[spec] theorem instLClear_spec (s₀ : AState) :
    ⦃fun s => s = s₀⦄ instLClear
    ⦃fun _u s' => s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ s'.memos = { s₀.memos with instLC := ∅ } ∧
        ∀ ws, InstLMemoA ws s'; ⊤⦄ := by
  dsimp only
  vcgen [instLClear]
  rename_i hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, fun _ => MemoOK.of_empty rfl⟩

@[spec] theorem liftGet_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => s = s₀⦄ liftGet k
    ⦃fun r s' => s' = s₀ ∧ r = s₀.memos.liftC[k]?; ⊤⦄ := by
  vcgen [liftGet] with finish

@[spec] theorem liftClear_spec (s₀ : AState) :
    ⦃fun s => s = s₀⦄ liftClear
    ⦃fun _u s' => s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ s'.memos = { s₀.memos with liftC := ∅ } ∧
        ∀ amount, LiftMemoA amount s'; ⊤⦄ := by
  dsimp only
  vcgen [liftClear]
  rename_i hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, fun _ => MemoOK.of_empty rfl⟩

@[spec] theorem abs1Get_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => s = s₀⦄ abs1Get k
    ⦃fun r s' => s' = s₀ ∧ r = s₀.memos.abs1C[k]?; ⊤⦄ := by
  vcgen [abs1Get] with finish

@[spec] theorem abs1Clear_spec (s₀ : AState) :
    ⦃fun s => s = s₀⦄ abs1Clear
    ⦃fun _u s' => s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ s'.memos = { s₀.memos with abs1C := ∅ } ∧
        ∀ d, Abs1MemoA d s'; ⊤⦄ := by
  dsimp only
  vcgen [abs1Clear]
  rename_i hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, fun _ => MemoOK.of_empty rfl⟩

@[spec] theorem inst1LGet_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => s = s₀⦄ inst1LGet k
    ⦃fun r s' => s' = s₀ ∧ r = s₀.memos.inst1LC[k]?; ⊤⦄ := by
  vcgen [inst1LGet] with finish

@[spec] theorem inst1LClear_spec (s₀ : AState) :
    ⦃fun s => s = s₀⦄ inst1LClear
    ⦃fun _u s' => s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ s'.memos = { s₀.memos with inst1LC := ∅ } ∧
        ∀ ve, Inst1LMemoA ve s'; ⊤⦄ := by
  dsimp only
  vcgen [inst1LClear]
  rename_i hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, fun _ => MemoOK.of_empty rfl⟩

@[spec] theorem instLPGet_spec (s₀ : AState) (k : EIdx × Nat) :
    ⦃fun s => s = s₀⦄ instLPGet k
    ⦃fun r s' => s' = s₀ ∧ r = s₀.memos.instLPC[k]?; ⊤⦄ := by
  vcgen [instLPGet] with finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2720-2722 Expr.instLPFast — the
one `Clear` that drops THREE tables: `instLPFast`'s memo depends on `ks` and
`us`, and so do the two level-handle tables task #97-P6-13 added beside it. -/
@[spec] theorem instLPClear_spec (s₀ : AState) :
    ⦃fun s => s = s₀⦄ instLPClear
    ⦃fun _u s' => s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with instLPC := ∅, instLPLC := ∅, instLPLsC := ∅ } ∧
        (∀ ks us, InstLPMemoA ks us s') ∧ (∀ ks us, InstLPLMemoA ks us s') ∧
        ∀ ks us, InstLPLsMemoA ks us s'; ⊤⦄ := by
  dsimp only
  vcgen [instLPClear]
  rename_i hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, fun _ _ => MemoOK.of_empty rfl,
    fun _ _ => MemoLOK.of_empty rfl, fun _ _ => MemoLsOK.of_empty rfl⟩

@[spec] theorem instLPLGet_spec (s₀ : AState) (h : LIdx) :
    ⦃fun s => s = s₀⦄ instLPLGet h
    ⦃fun r s' => s' = s₀ ∧ r = s₀.memos.instLPLC[h]?; ⊤⦄ := by
  vcgen [instLPLGet] with finish

@[spec] theorem instLPLsGet_spec (s₀ : AState) (h : LsIdx) :
    ⦃fun s => s = s₀⦄ instLPLsGet h
    ⦃fun r s' => s' = s₀ ∧ r = s₀.memos.instLPLsC[h]?; ⊤⦄ := by
  vcgen [instLPLsGet] with finish

@[spec] theorem bvarBGet_spec (s₀ : AState) (k : EIdx) :
    ⦃fun s => s = s₀⦄ bvarBGet k
    ⦃fun r s' => s' = s₀ ∧ r = s₀.memos.bvarBC[k]?; ⊤⦄ := by
  vcgen [bvarBGet] with finish

@[spec] theorem bvarBSet_spec (s₀ : AState) (k : EIdx) (r : Nat)
    (hm : MemoBA s₀) (hk : (denoteE s₀.store k).isSome = true)
    (hr : RelV Expr.bvarBound s₀.store k r) :
    ⦃fun s => s = s₀⦄ bvarBSet k r
    ⦃fun _u s' => s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with bvarBC := s₀.memos.bvarBC.insert k r } ∧
        MemoBA s'; ⊤⦄ := by
  dsimp only
  vcgen [bvarBSet]
  rename_i hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoVOK.insert hm rfl hk hr⟩

@[spec] theorem bvarBClear_spec (s₀ : AState) :
    ⦃fun s => s = s₀⦄ bvarBClear
    ⦃fun _u s' => s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ s'.memos = { s₀.memos with bvarBC := ∅ } ∧
        MemoBA s'; ⊤⦄ := by
  dsimp only
  vcgen [bvarBClear]
  rename_i hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoVOK.of_empty rfl⟩

@[spec] theorem fvarBGet_spec (s₀ : AState) (k : EIdx) :
    ⦃fun s => s = s₀⦄ fvarBGet k
    ⦃fun r s' => s' = s₀ ∧ r = s₀.memos.fvarBC[k]?; ⊤⦄ := by
  vcgen [fvarBGet] with finish

@[spec] theorem fvarBSet_spec (s₀ : AState) (k : EIdx) (r : Nat)
    (hm : MemoFA s₀) (hk : (denoteE s₀.store k).isSome = true)
    (hr : RelV Expr.fvarRange s₀.store k r) :
    ⦃fun s => s = s₀⦄ fvarBSet k r
    ⦃fun _u s' => s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with fvarBC := s₀.memos.fvarBC.insert k r } ∧
        MemoFA s'; ⊤⦄ := by
  dsimp only
  vcgen [fvarBSet]
  rename_i hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoVOK.insert hm rfl hk hr⟩

@[spec] theorem fvarBClear_spec (s₀ : AState) :
    ⦃fun s => s = s₀⦄ fvarBClear
    ⦃fun _u s' => s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧ s'.memos = { s₀.memos with fvarBC := ∅ } ∧
        MemoFA s'; ⊤⦄ := by
  dsimp only
  vcgen [fvarBClear]
  rename_i hs
  subst hs
  exact ⟨rfl, rfl, rfl, rfl, MemoVOK.of_empty rfl⟩

/-! ### The bulk-instantiation cutoff (task #97f's deviation)

`instListCutoff` reads the packed loose-bvar bound off the derived column and
compares it with the cursor.  What its caller needs is the *positive*
direction — a `true` answer licenses the early return — so that is what the
spec says; a `false` answer licenses nothing and the walk recurses. -/

@[spec] theorem instListCutoff_spec (s₀ : AState) (h : EIdx) (d : Nat) :
    ⦃fun s => s = s₀⦄ instListCutoff h d
    ⦃fun r s' => s' = s₀ ∧ (r = true →
        (bvarOfData (s₀.store.derived h)).toNat < satRange ∧
        (bvarOfData (s₀.store.derived h)).toNat ≤ d); ⊤⦄ := by
  vcgen [instListCutoff] with finish

/-! ## The per-declaration bracket (DESIGN §8.3, "Drop")

`flushCaches` drops the fourteen per-declaration tables whole — which is
con-leche's own `flushC` (task #97f's amendment) — `dropScratch` does that and
drops the store's scratch tier with it, and `enterScratch` opens the tier and
clears the per-call `Memos` (whose keys the new tier may reuse).

`Caches.dropScratchEntries` stays in `Arena/CoreState.lean` as the
SPECIFICATION of a surviving row; `flushed ⊑ dropScratchEntries` as caches,
which is why flushing is sound and why the bridge only ever needs
`CacheOK.of_empty`. -/

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the EMPTY cache set
satisfies every clause, at every mode and every environment.  This is the
whole content of the flush's soundness: a dropped row is a cache miss and
nothing else. -/
theorem CacheOK.of_empty {mode : CheckMode} {env : Env} {s : AState}
    (h : s.caches = Caches.empty) : CacheOK mode env s where
  whnfCore := by intro i j hk; rw [h] at hk; simp [Caches.empty] at hk
  whnfCoreCheap := by intro i j hk; rw [h] at hk; simp [Caches.empty] at hk
  whnf := by intro i j hk; rw [h] at hk; simp [Caches.empty] at hk
  infer := by intro i j hk; rw [h] at hk; simp [Caches.empty] at hk
  inferIO := by intro i j hk; rw [h] at hk; simp [Caches.empty] at hk
  defeq := by intro k r hk; rw [h] at hk; simp [Caches.empty] at hk
  lvlEq := by intro k r hk; rw [h] at hk; simp [Caches.empty] at hk
  lvlsEq := by intro k r hk; rw [h] at hk; simp [Caches.empty] at hk
  constTy := by intro k i hk; rw [h] at hk; simp [Caches.empty] at hk
  constVal := by intro k i hk; rw [h] at hk; simp [Caches.empty] at hk
  ruleRhs := by intro k i hk; rw [h] at hk; simp [Caches.empty] at hk
  readL := by intro k u hk; rw [h] at hk; simp [Caches.empty] at hk
  readN := by intro k x hk; rw [h] at hk; simp [Caches.empty] at hk
  readLs := by intro k us hk; rw [h] at hk; simp [Caches.empty] at hk

/-! ## The pin table (task #97-P6-4a)

One spec per reader.  `pinAt`'s is the only one with content: the table is an
`Array` and its `i`-th slot denotes `pinNames`' `i`-th name, which is what
`PinsOK` says and `denoteNL_get` extracts. -/

/-- con-leche: none — the `i`-th slot of a denoting handle list denotes the
`i`-th name.  `PinsOK.names` is the list form; `pinAt` indexes. -/
theorem denoteNL_get {st : EStore} : ∀ (hs : List NIdx)
    (xs : List ConLeche.Name) (i : Nat) (n : NIdx) (x : ConLeche.Name),
    denoteNL st hs xs → hs[i]? = some n → xs[i]? = some x →
      denoteN st.ns n = some x := by
  intro hs
  induction hs with
  | nil => intro _ _ _ _ _ h1 _; simp at h1
  | cons a as ih =>
    intro xs i n x hd h1 h2
    cases xs with
    | nil => exact hd.elim
    | cons y ys =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
        subst h1; subst h2; exact hd.1
      | succ k =>
        simp only [List.getElem?_cons_succ] at h1 h2
        exact ih ys k n x hd.2 h1 h2

@[spec] theorem pinAt_spec (s₀ : AState) (i : Nat) (hp : PinsOK s₀) :
    ⦃fun s => s = s₀⦄ pinAt i
    ⦃fun n s' => s' = s₀ ∧ ∀ x, pinNames[i]? = some x →
        denoteN s₀.store.ns n = some x; ⊤⦄ := by
  vcgen [pinAt]
  rename_i hs hlt
  subst hs
  refine ⟨rfl, fun x hx => ?_⟩
  refine denoteNL_get s.pins.names.toList pinNames i _ x hp.names ?_ hx
  have hlt' : i < s.pins.names.toList.length := by simpa using hlt
  rw [List.getElem?_eq_getElem hlt']
  simp

@[spec] theorem pinReserved_spec (s₀ : AState) (hp : PinsOK s₀) :
    ⦃fun s => s = s₀⦄ pinReserved
    ⦃fun ns s' => s' = s₀ ∧ denoteNL s₀.store ns reservedBasisNameValues; ⊤⦄ := by
  vcgen [pinReserved]
  rename_i hs _hr
  subst hs
  exact ⟨rfl, hp.reserved⟩

@[spec] theorem pinEmptyLevels_spec (s₀ : AState) (hp : PinsOK s₀) :
    ⦃fun s => s = s₀⦄ pinEmptyLevels
    ⦃fun us s' => s' = s₀ ∧ denoteLs s₀.store.lss us = some []; ⊤⦄ := by
  vcgen [pinEmptyLevels]
  rename_i hs _hr
  subst hs
  exact ⟨rfl, hp.emptyLevels⟩

@[spec] theorem pinZeroLevel_spec (s₀ : AState) (hp : PinsOK s₀) :
    ⦃fun s => s = s₀⦄ pinZeroLevel
    ⦃fun u s' => s' = s₀ ∧ denoteL s₀.store.ls u = some .zero; ⊤⦄ := by
  vcgen [pinZeroLevel]
  rename_i hs _hr
  subst hs
  exact ⟨rfl, hp.zeroLevel⟩

@[spec] theorem pinSortOne_spec (s₀ : AState) (hp : PinsOK s₀) :
    ⦃fun s => s = s₀⦄ pinSortOne
    ⦃fun e s' => s' = s₀ ∧
        denoteE s₀.store e = some (.sort (.succ .zero)); ⊤⦄ := by
  vcgen [pinSortOne]
  rename_i hs _hr
  subst hs
  exact ⟨rfl, hp.sortOne⟩

/-! ## The closer

Task #97s round 2's recipe, item by item.  ONE curated `grind` list; a
`bridge_peel` in front of it, which is what lets `grind` see one state where
the verification condition shows seven; and a second stage that puts the
`RelE` transports back and raises the instance budget, for the verification
conditions that genuinely have to move an answer along the extension chain.

**The arm files erase the transports.**  `RelE.ext`, `.of_ext` and
`.retarget` close the answer relation under `Ext` in both directions, so every
intermediate store multiplies every answer already known — measured on the
spike's one file, 70 s against 11.5 s.  The `_step` lemmas of
`Bridge/Rel.lean` group 7 already carry the chain, so the transports are
redundant *and* explosive; `attribute [-grind] RelE.ext RelE.of_ext
RelE.retarget` at the top of each arm file is the single highest-value line in
it, and because `attribute [-grind]` does not travel through an import each
file repeats it. -/

/-- con-leche: none — **the uniform closer** for Theorem 1's verification
conditions.  ONE curated list, plus the walk's own pure function where a
walk's arms need it: `bridge_vcs [Expr.instantiate1]` is how `ExprOps/Inst1`
calls it.  The second stage puts the `RelE` transports back and raises the
instance budget, for the handful of verification conditions that genuinely
have to move an answer along the extension chain. -/
syntax "bridge_vcs" (" [" (Lean.Parser.Tactic.grindParam),* "]")? : tactic

macro_rules
  -- NOT `bridge_vcs []`: an empty splice expands to a leading comma and
  -- `grind` reports "unexpected grind parameter" (group C's finding).
  | `(tactic| bridge_vcs) => `(tactic| bridge_vcs [Ext.refl])
  | `(tactic| bridge_vcs [$ts,*]) => `(tactic| first
      | (intro hf; exact False.elim hf)
      | (bridge_peel
         subst_vars
         grind (instances := 1000) [$ts,*, StateOK, MemoOK.mono, MemoOK.insert, MemoOK.of_empty,
           MemoVOK.of_empty, MemoLOK.of_empty, MemoLsOK.of_empty,
           MemoVOK.insert, MemoLOK.mono, MemoLsOK.mono,
           Ext.trans, Ext.refl,
           viewOK_bvar, viewOK_lit, viewOK_fvar,
           viewOK_sort, viewOK_const, viewOK_app, viewOK_lam, viewOK_forallE,
           viewOK_letE, viewOK_proj, denoteEView,
           opt2_eq_some_iff, opt3_eq_some_iff, Option.isSome_iff_exists,
           Option.map_eq_some_iff])
      | (bridge_peel
         subst_vars
         grind (instances := 4000) [$ts,*, StateOK, MemoOK.mono, MemoOK.insert, MemoOK.of_empty,
           MemoVOK.of_empty, MemoLOK.of_empty, MemoLsOK.of_empty,
           MemoVOK.insert, MemoLOK.mono, MemoLsOK.mono,
           Ext.trans, Ext.refl,
           RelE.ext, RelE.of_ext, RelV.of_ext,
           viewOK_bvar, viewOK_lit, viewOK_fvar, viewOK_sort, viewOK_const,
           viewOK_app, viewOK_lam, viewOK_forallE, viewOK_letE, viewOK_proj,
           denoteEView, opt2_eq_some_iff, opt3_eq_some_iff,
           Option.isSome_iff_exists, Option.map_eq_some_iff]))

end ConRon.Bridge

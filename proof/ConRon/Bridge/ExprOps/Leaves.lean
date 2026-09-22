/-
# `ConRon.Bridge.ExprOps.Leaves` — Theorem 1 for the `fvar` leaf list

DESIGN §8.2's Theorem 1 at the four twins of `Arena/ExprOps.lean` that are
about the `fvar` LEAVES of a term — `fvarLeaves` (`:730`), `fvarLeavesGo`
(`:876`), `fvarLeavesFast` (`:906`) and `leafMem` (`:914`) — and the shared
layer its companion `ExprOps/Guards.lean` (the two memoized guards
`wscopedBGo`/`wscopedBFast` and `leavesSubGo`/`leafGuard`) is written
against.  Both are companions of `ExprOps/Walks.lean` (the unmemoized
`Bool`/`Nat` walks) and `ExprOps/Ranges.lean` (the packed range fields).

## What this file adds that `Bridge/Rel.lean` does not have

1. **A denotation for a leaf LIST.**  `fvarLeaves`'s answer is a
   `List (Nat × EIdx)` and con-leche's is a `List (Nat × Expr)`, so the
   answer relation is `RelFL` over `denoteLeaves` below — `RelEL`'s shape at
   a list of *pairs*, and with no target store because nothing here interns.
   **`denoteLeaves`, its equations, `denoteLeaves_append` and `RelFL` with
   its ten step lemmas morally belong in `Bridge/Rel.lean`.**

   The ten step lemmas are **not** decoration, and that is this file's one
   measured finding: `denoteLeaves_append` tagged `@[grind →]` and left to
   the closer does not terminate in any usable time (killed at 15 minutes on
   one file) — its three list variables let every pair of known
   `denoteLeaves` facts breed another, and the appended facts breed again.
   `ExprOps/Walks.lean`'s recipe ("`bridge_vcs [f, RelV]` closes everything")
   therefore does **not** extend to a list-valued answer: a list answer needs
   `ExprOps/Inst1.lean`'s per-arm `_step` shape, monomorphic at the walk's own
   pure function so that `@[grind →]` has a head symbol and the arms need no
   `next =>` block.  With them the file is fast again.

2. **A memo invariant for a table that is an ARGUMENT.**  `fvarLeavesGo`'s
   `seen` set and `Guards.lean`'s two memos are explicit arguments and not
   `AState` fields (their signatures say so: `Std.HashMap EIdx Unit`,
   `Std.HashMap (EIdx × Nat) Bool`, `Std.HashMap EIdx Bool`), so their
   invariants are hypotheses about those arguments and **not** any of
   `Bridge/StateOK.lean`'s thirteen.  They are stated in exactly StateOK's
   shape (`∀ k v, tbl[k]? = some v → …`); `MemoVDOK` below is the one generic
   shape `StateOK.lean` lacks (a cursor in the key, a representation-free
   value) with StateOK's own four lemmas, and **it belongs there**.

3. **The fvar-range cutoff's licence.**  Each memoized walk short-circuits
   on `fvarOfData (← derivedE h) == 0`, which is con-leche's own
   `e.fvarB == 0`.  `hasFvar_false_of_derived` is `EStore.derived_exact` plus
   `Expr.fvarBRaw_exact` plus `Expr.hasFvar_eq_false_iff`; the field cannot
   saturate at zero (`satRange` is 32767), so there is no saturated branch to
   consider and the walks may cut unconditionally on the packed read.

## Statements with no metavariable in them (template rule 4)

Every relation below quantifies the DENOTATIONS inside itself and takes
`isSome` as the precondition — `RelFL`'s own shape, and `LeavesEq` /
`SeenA` / `Guards.lean`'s `LSubAt` are written the same way.  This is not
style: `fvarLeavesFast`'s answer list is the base of `leafGuard`'s membership
test, so a spec that named the base list as a PARAMETER would hand
`mvcgen` a side goal `denoteLeaves s.store bl = some ?bl'` with a
metavariable in it, which the closer cannot take (task #97s template rule 4,
measured again here).

## The one gap: `fvarLeavesGo`'s `seen` set

`fvarLeavesGo`'s memo is a visited SET whose entries are `Unit`, and an entry
means *"this node's leaves are already in `acc`"* — a statement about the
ACCUMULATOR, not about the node.  con-leche says so at length
(`Cached/ExprOpsC.lean:1093-1128`, "the one walk of the tree whose memo is
not the `withExclusive` idiom, and why") and verifies it against a **gray**
invariant (`SeenInv`, `Verify/Cached/GuardsC.lean`): every key of `seen`
either has all its leaves in `acc` already or is being processed by an
ancestor of the current call.  The twin inserts `h` into `seen` BEFORE
walking its children, so the plain invariant is violated for exactly the
descent path, and discharging the gray case needs the acyclicity of the
store — `StoreWF`'s rank witness — as a second induction beside the fuel.
That is the one `sorry` here; `fvarLeavesFast_spec` consumes it and is
otherwise complete.

Because the answer is a SET and not a list — a shared subterm is walked once,
where `Expr.fvarLeaves` re-concatenates its leaves per occurrence — that
statement is membership equivalence and not list equality, and it is not a
weakening: `leafGuard`, the one consumer, uses the list only as a membership
base (`leafMem`), and `Guards.lean`'s `leavesSubSpec_congr` is what makes
that formally so.
-/
import ConRon.Bridge.Specs

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 2000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

attribute [-grind] RelE.ext RelE.of_ext RelE.retarget

/-! ## 1. The leaf list's denotation -/

/-- con-leche: none — a list of `fvar` leaves denotes, pointwise. -/
def denoteLeaves (st : EStore) : List (Nat × EIdx) → Option (List (Nat × Expr))
  | [] => some []
  | (i, t) :: rest =>
    match denoteE st t, denoteLeaves st rest with
    | some t', some rest' => some ((i, t') :: rest')
    | _, _ => none

/-- con-leche: none — `denoteLeaves` at the empty list. -/
theorem denoteLeaves_nil {st : EStore} : denoteLeaves st [] = some [] := rfl

/-- con-leche: none — `denoteLeaves` at a cons, with the child's denotation as
a hypothesis so nothing has to be guessed. -/
theorem denoteLeaves_cons {st : EStore} {i : Nat} {t : EIdx}
    {rest : List (Nat × EIdx)} {t' : Expr} {rest' : List (Nat × Expr)}
    (ht : denoteE st t = some t') (hr : denoteLeaves st rest = some rest') :
    denoteLeaves st ((i, t) :: rest) = some ((i, t') :: rest') := by
  simp only [denoteLeaves, ht, hr]

/-- con-leche: none — `denoteLeaves` commutes with `++`.  **Not a `grind`
rule**: see the module doc, item 1. -/
theorem denoteLeaves_append {st : EStore} :
    ∀ (xs ys : List (Nat × EIdx)) (xs' ys' : List (Nat × Expr)),
      denoteLeaves st xs = some xs' → denoteLeaves st ys = some ys' →
      denoteLeaves st (xs ++ ys) = some (xs' ++ ys') := by
  intro xs
  induction xs with
  | nil =>
    intro ys xs' ys' hx hy
    simp only [denoteLeaves] at hx
    obtain rfl := Option.some.inj hx
    simpa using hy
  | cons p ps ih =>
    intro ys xs' ys' hx hy
    obtain ⟨i, t⟩ := p
    simp only [denoteLeaves] at hx
    split at hx
    · rename_i t' rest' ht hrest
      obtain rfl := Option.some.inj hx
      simp only [List.cons_append, denoteLeaves, ht, ih ys rest' ys' hrest hy]
    · exact absurd hx (by simp)

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — the answer relation at a
LEAF-LIST result: `Bridge/Rel.lean`'s `RelEL` with `denoteEList` replaced by
`denoteLeaves` and the target store dropped. -/
def RelFL (f : Expr → List (Nat × Expr)) (st : EStore) (c : EIdx)
    (rs : List (Nat × EIdx)) : Prop :=
  ∀ e, denoteE st c = some e → denoteLeaves st rs = some (f e)

/-- con-leche: none — `RelFL`'s eliminator. -/
theorem RelFL.apply {f : Expr → List (Nat × Expr)} {st : EStore} {c : EIdx}
    {rs : List (Nat × EIdx)} {e : Expr} (h : RelFL f st c rs)
    (he : denoteE st c = some e) : denoteLeaves st rs = some (f e) := h e he

/-- con-leche: none — a leaf list that denotes has a denotation (the `isSome`
spelling, template rule 4). -/
theorem RelFL.isSome {f : Expr → List (Nat × Expr)} {st : EStore} {c : EIdx}
    {rs : List (Nat × EIdx)} (h : RelFL f st c rs)
    (hs : (denoteE st c).isSome = true) :
    (denoteLeaves st rs).isSome = true := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hs
  rw [h e he]; rfl

/-! ## 2. The generic memo invariant this tier needs and `StateOK.lean` lacks

`MemoVOK` is `StateOK.lean`'s handle-keyed, value-valued invariant, and
`Guards.lean`'s `leavesSubGo` memo is that shape.  `wscopedBGo`'s key carries
the CURSOR (its `fvar` arm descends at the annotation's own index, so the
answer is not a function of the node alone), which is `MemoOK`'s key with
`MemoVOK`'s value — a fourth shape, here with `StateOK.lean`'s four
lemmas. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1497-1499 MemoBInv — the generic
CURSOR-keyed, value-valued memo invariant. -/
def MemoVDOK {α : Type} (f : Nat → Expr → α)
    (tbl : Std.HashMap (EIdx × Nat) α) (st : EStore) : Prop :=
  ∀ (k : EIdx × Nat) (v : α), tbl[k]? = some v →
    ∃ e, denoteE st k.1 = some e ∧ v = f k.2 e

/-- con-leche: none — a dropped table satisfies the invariant. -/
theorem MemoVDOK.of_empty {α : Type} {f : Nat → Expr → α}
    {tbl : Std.HashMap (EIdx × Nat) α} {st : EStore} (h : tbl = ∅) :
    MemoVDOK f tbl st := by
  intro k v hk; rw [h] at hk; simp at hk

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1497-1499 MemoBInv — **the memo
hit**, delivered as the answer relation so the caller never unfolds the
invariant. -/
@[grind →] theorem MemoVDOK.get {α : Type} {f : Nat → Expr → α}
    {tbl : Std.HashMap (EIdx × Nat) α} {st : EStore} {k : EIdx × Nat} {v : α}
    (hm : MemoVDOK f tbl st) (hk : tbl[k]? = some v) :
    RelV (f k.2) st k.1 v := by
  intro e he
  obtain ⟨e', h1, h2⟩ := hm k v hk
  rw [he] at h1
  obtain rfl := Option.some.inj h1
  exact h2

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1503-1505 MemoBInv.insert — the
invariant-carrying insert (template rule 6). -/
theorem MemoVDOK.insert {α : Type} {f : Nat → Expr → α}
    {tbl tbl' : Std.HashMap (EIdx × Nat) α} {st : EStore} {k : EIdx × Nat}
    {v : α} (hm : MemoVDOK f tbl st) (hc : tbl' = tbl.insert k v)
    (hk : (denoteE st k.1).isSome = true) (hr : RelV (f k.2) st k.1 v) :
    MemoVDOK f tbl' st := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hk
  intro k' v' hk'
  rw [hc, Std.HashMap.getElem?_insert] at hk'
  split at hk'
  · rename_i hbeq
    cases hk'
    obtain rfl := eq_of_beq hbeq
    exact ⟨e, he, hr e he⟩
  · exact hm k' v' hk'

/-! ## 3. The pure facts behind the fvar-range cutoff

Two structural inductions on `Expr`, plus `Expr.hasFvar_eq_false_iff` and
`Expr.fvarBRaw_exact` to connect them to the packed field. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:821-833 fvarLeaves — an
`fvar`-free term has no reachable leaf.  (`hasFvar` answers `true` at an
`fvar` node without descending its annotation, and `fvarLeaves` produces only
at an `fvar` node, so the two agree on emptiness.) -/
theorem fvarLeaves_nil_of_hasFvar :
    ∀ e : Expr, e.hasFvar = false → Expr.fvarLeaves e = [] := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => intro _; simp [Expr.fvarLeaves]
  | fvar k t _ => intro h; simp [Expr.hasFvar] at h
  | app f a ihf iha =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Expr.fvarLeaves, ihf h.1, iha h.2]
  | lam ty b m iht ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Expr.fvarLeaves, iht h.1, ihb h.2]
  | forallE ty b m iht ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Expr.fvarLeaves, iht h.1, ihb h.2]
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Expr.fvarLeaves, iht h.1.1, ihv h.1.2, ihb h.2]
  | proj n i s ih =>
    intro h
    simp only [Expr.hasFvar] at h
    simp [Expr.fvarLeaves, ih h]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:835-861 wscopedB — an `fvar`-free
term is in scope at every depth.  This is `wscopedBP_cut`'s content at the
Kernel tier. -/
theorem wscopedB_of_hasFvar :
    ∀ (e : Expr) (d : Nat), e.hasFvar = false → Expr.wscopedB d e = true := by
  intro e
  induction e with
  | bvar _ | sort _ | const _ _ | lit _ => intro _ _; simp [Expr.wscopedB]
  | fvar k t _ => intro _ h; simp [Expr.hasFvar] at h
  | app f a ihf iha =>
    intro d h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Expr.wscopedB, ihf d h.1, iha d h.2]
  | lam ty b m iht ihb =>
    intro d h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Expr.wscopedB, iht d h.1, ihb d h.2]
  | forallE ty b m iht ihb =>
    intro d h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Expr.wscopedB, iht d h.1, ihb d h.2]
  | letE ty v b iht ihv ihb =>
    intro d h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Expr.wscopedB, iht d h.1.1, ihv d h.1.2, ihb d h.2]
  | proj n i s ih =>
    intro d h
    simp only [Expr.hasFvar] at h
    simp [Expr.wscopedB, ih d h]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1590 fvarBRaw_exact — the CUTOFF
as the arena tests it: a zero fvar-range field means an `fvar`-free term.  The
field cannot be saturated at zero (`satRange` is 32767), so no saturated
branch is possible here — which is why the three memoized walks may cut
unconditionally on the packed read. -/
theorem hasFvar_false_of_derived {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {e : Expr} (he : denoteE st h = some e)
    (h0 : (fvarOfData (st.derived h)).toNat = 0) : e.hasFvar = false := by
  have hd := EStore.derived_exact hwf he
  rw [hd] at h0
  have hraw : Expr.fvarBRaw e = 0 := h0
  have hlt : Expr.fvarBRaw e < satRange := by
    simp only [hraw, satRange]; omega
  exact Expr.hasFvar_eq_false_iff.mpr
    (by rw [← Expr.fvarBRaw_exact e hlt, hraw])

/-! ## 4. `RelFL`'s ten step lemmas, at `Expr.fvarLeaves`

`ExprOps/Inst1.lean`'s group-7 shape, monomorphic so that `@[grind →]` has a
head symbol and the ten arms of `fvarLeaves` need no `next =>` block.  The
`view` read is each rule's ematch pattern, which is what `mvcgen` hands the
arm. -/

@[grind →] theorem RelFL.bvar_step {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {i : Nat} (hview : st.view h = some (.bvar i)) :
    RelFL Expr.fvarLeaves st h [] := by
  intro e he
  rw [denote_bvar_inv hwf hview he]
  simp [Expr.fvarLeaves, denoteLeaves]

@[grind →] theorem RelFL.sort_step {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {u : LIdx} (hview : st.view h = some (.sort u)) :
    RelFL Expr.fvarLeaves st h [] := by
  intro e he
  obtain ⟨l, rfl, _⟩ := denote_sort_inv hwf hview he
  simp [Expr.fvarLeaves, denoteLeaves]

@[grind →] theorem RelFL.const_step {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {n : NIdx} {us : LsIdx} (hview : st.view h = some (.const n us)) :
    RelFL Expr.fvarLeaves st h [] := by
  intro e he
  obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hview he
  simp [Expr.fvarLeaves, denoteLeaves]

@[grind →] theorem RelFL.lit_step {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {l : ConLeche.Literal} (hview : st.view h = some (.lit l)) :
    RelFL Expr.fvarLeaves st h [] := by
  intro e he
  rw [denote_lit_inv hwf hview he]
  simp [Expr.fvarLeaves, denoteLeaves]

@[grind →] theorem RelFL.fvar_step {st : EStore} (hwf : StoreWF st)
    {h ty : EIdx} {k : Nat} {rest : List (Nat × EIdx)}
    (hview : st.view h = some (.fvar k ty))
    (hr : RelFL Expr.fvarLeaves st ty rest) :
    RelFL Expr.fvarLeaves st h ((k, ty) :: rest) := by
  intro e he
  obtain ⟨t, rfl, hdt⟩ := denote_fvar_inv hwf hview he
  have hp : Expr.fvarLeaves (.fvar k t) = (k, t) :: Expr.fvarLeaves t := by
    simp [Expr.fvarLeaves]
  rw [hp]
  exact denoteLeaves_cons hdt (hr t hdt)

@[grind →] theorem RelFL.app_step {st : EStore} (hwf : StoreWF st)
    {h f a : EIdx} {xs ys : List (Nat × EIdx)}
    (hview : st.view h = some (.app f a))
    (hf : RelFL Expr.fvarLeaves st f xs)
    (ha : RelFL Expr.fvarLeaves st a ys) :
    RelFL Expr.fvarLeaves st h (xs ++ ys) := by
  intro e he
  obtain ⟨ef, ea, rfl, hdf, hda⟩ := denote_app_inv hwf hview he
  have hp : Expr.fvarLeaves (.app ef ea) =
      Expr.fvarLeaves ef ++ Expr.fvarLeaves ea := by simp [Expr.fvarLeaves]
  rw [hp]
  exact denoteLeaves_append xs ys _ _ (hf ef hdf) (ha ea hda)

@[grind →] theorem RelFL.lam_step {st : EStore} (hwf : StoreWF st)
    {h ty b : EIdx} {m : BinderMeta} {xs ys : List (Nat × EIdx)}
    (hview : st.view h = some (.lam ty b m))
    (ht : RelFL Expr.fvarLeaves st ty xs)
    (hb : RelFL Expr.fvarLeaves st b ys) :
    RelFL Expr.fvarLeaves st h (xs ++ ys) := by
  intro e he
  obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_lam_inv hwf hview he
  have hp : Expr.fvarLeaves (.lam et eb m) =
      Expr.fvarLeaves et ++ Expr.fvarLeaves eb := by simp [Expr.fvarLeaves]
  rw [hp]
  exact denoteLeaves_append xs ys _ _ (ht et hdt) (hb eb hdb)

@[grind →] theorem RelFL.forallE_step {st : EStore} (hwf : StoreWF st)
    {h ty b : EIdx} {m : BinderMeta} {xs ys : List (Nat × EIdx)}
    (hview : st.view h = some (.forallE ty b m))
    (ht : RelFL Expr.fvarLeaves st ty xs)
    (hb : RelFL Expr.fvarLeaves st b ys) :
    RelFL Expr.fvarLeaves st h (xs ++ ys) := by
  intro e he
  obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_forallE_inv hwf hview he
  have hp : Expr.fvarLeaves (.forallE et eb m) =
      Expr.fvarLeaves et ++ Expr.fvarLeaves eb := by simp [Expr.fvarLeaves]
  rw [hp]
  exact denoteLeaves_append xs ys _ _ (ht et hdt) (hb eb hdb)

@[grind →] theorem RelFL.letE_step {st : EStore} (hwf : StoreWF st)
    {h ty v b : EIdx} {xs ys zs : List (Nat × EIdx)}
    (hview : st.view h = some (.letE ty v b))
    (ht : RelFL Expr.fvarLeaves st ty xs)
    (hv : RelFL Expr.fvarLeaves st v ys)
    (hb : RelFL Expr.fvarLeaves st b zs) :
    RelFL Expr.fvarLeaves st h (xs ++ ys ++ zs) := by
  intro e he
  obtain ⟨et, ev, eb, rfl, hdt, hdv, hdb⟩ := denote_letE_inv hwf hview he
  have hp : Expr.fvarLeaves (.letE et ev eb) =
      Expr.fvarLeaves et ++ Expr.fvarLeaves ev ++ Expr.fvarLeaves eb := by
    simp [Expr.fvarLeaves]
  rw [hp]
  exact denoteLeaves_append (xs ++ ys) zs _ _
    (denoteLeaves_append xs ys _ _ (ht et hdt) (hv ev hdv)) (hb eb hdb)

@[grind →] theorem RelFL.proj_step {st : EStore} (hwf : StoreWF st)
    {h sub : EIdx} {n : NIdx} {i : Nat} {rs : List (Nat × EIdx)}
    (hview : st.view h = some (.proj n i sub))
    (hs : RelFL Expr.fvarLeaves st sub rs) :
    RelFL Expr.fvarLeaves st h rs := by
  intro e he
  obtain ⟨nm, es, rfl, _, hds⟩ := denote_proj_inv hwf hview he
  have hp : Expr.fvarLeaves (.proj nm i es) = Expr.fvarLeaves es := by
    simp [Expr.fvarLeaves]
  rw [hp]
  exact hs es hds

/-! ## 5. `fvarLeaves` — `ExprOps.lean:730`

`Kernel/ExprOps.lean`'s unmemoized walk: the SPECIFICATION of
`fvarLeavesFast`.  Its answer is con-leche's exact list in con-leche's order,
which makes it the one leaf twin with an equality statement rather than a
membership one. -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `fvarLeaves`'s recursion. -/
structure FvarLeavesSpec (rec : EIdx → AM (List (Nat × EIdx))) : Prop where
  run : ∀ (s₁ : AState) (c : EIdx), StateOK s₁ →
      (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec c
    ⦃⇓? rs s' => ⌜s' = s₁ ∧ RelFL Expr.fvarLeaves s₁.store c rs⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:821-833 fvarLeaves — **THEOREM 1
for `fvarLeaves`**, at one level of the recursion. -/
theorem fvarLeaves_spec : ∀ fuel, FvarLeavesSpec (fvarLeaves fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h _ _
    mvcgen [fvarLeaves_zero]
    all_goals bridge_vcs [denoteLeaves_nil]
  | succ fuel ih =>
    constructor
    intro s₀ h hok hden
    have hrec := ih.run
    mvcgen [fvarLeaves_succ, fvarLeavesArmFVar, fvarLeavesArmApp, fvarLeavesArmBind, fvarLeavesArmLet, hrec]
    all_goals bridge_vcs [denoteLeaves_nil]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:821-833 fvarLeaves — the run
form. -/
theorem fvarLeaves_run {fuel : Nat} {s₀ s' : AState} {h : EIdx}
    {rs : List (Nat × EIdx)} (hok : StateOK s₀)
    (hden : (denoteE s₀.store h).isSome = true)
    (hrun : (fvarLeaves fuel h).run s₀ = Except.ok (rs, s')) :
    s' = s₀ ∧ RelFL Expr.fvarLeaves s₀.store h rs :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    ((fvarLeaves_spec fuel).run s₀ h hok hden)

/-! ## 6. `leafMem` — `ExprOps.lean:914`

**Not a monadic twin**: a pure `Bool` function on handles, and the one place
this tier needs `denoteE`'s INJECTIVITY.  con-leche compares the annotation
with `Expr.beq`; over handles it is handle equality, and the two tests agree
because `denoteE` is injective (`Arena/WFProofs.lean`'s `denoteE_inj`, DESIGN
§8.3's soundness obligation).  Stated against `List.contains`, which is what
`Kernel/Core.lean:586`'s guard uses and what con-leche's `leafMem` is. -/

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1157-1162 leafMem — **THEOREM 1
for `leafMem`**: the handle test is the term test. -/
theorem leafMem_spec {st : EStore} (hwf : StoreWF st) :
    ∀ (bl : List (Nat × EIdx)) (bl' : List (Nat × Expr)),
      denoteLeaves st bl = some bl' →
      ∀ (idx : Nat) (ty : EIdx) (t : Expr), denoteE st ty = some t →
        leafMem bl idx ty = bl'.contains (idx, t) := by
  intro bl
  induction bl with
  | nil =>
    intro bl' hb idx ty t _
    simp only [denoteLeaves] at hb
    obtain rfl := Option.some.inj hb
    simp [leafMem]
  | cons p ps ih =>
    intro bl' hb idx ty t ht
    obtain ⟨i, tt⟩ := p
    simp only [denoteLeaves] at hb
    split at hb
    · rename_i t0 rest' ht0 hrest
      obtain rfl := Option.some.inj hb
      have hkey : (tt = ty) ↔ (t0 = t) := by
        constructor
        · intro hc; subst hc; rw [ht] at ht0; exact (Option.some.inj ht0).symm
        · intro hc; subst hc; exact denoteE_inj hwf ht0 ht
      have hih := ih rest' hrest idx ty t ht
      simp only [leafMem, List.contains_cons, hih]
      grind
    · exact absurd hb (by simp)

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1157-1162 leafMem — the same,
keyed so the closer derives it itself.  **Two lemmas and not one equation**,
which is a finding of its own: with the equation as the conclusion the leaf
INDEX occurs nowhere in the antecedents, so `grind` reports *failed to find
patterns in the antecedents of the theorem* and the rule cannot be
registered.  Both twins that use `leafMem` TEST it (`if leafMem bl idx ty
then …`), so `mvcgen` hands the arm the verdict as a hypothesis and the
index is bound there. -/
@[grind →] theorem leafMem_of_true {st : EStore} (hwf : StoreWF st)
    {bl : List (Nat × EIdx)} {bl' : List (Nat × Expr)} {idx : Nat} {ty : EIdx}
    {t : Expr} (h : leafMem bl idx ty = true)
    (hb : denoteLeaves st bl = some bl') (ht : denoteE st ty = some t) :
    bl'.contains (idx, t) = true := by
  rw [← leafMem_spec hwf bl bl' hb idx ty t ht]; exact h

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1157-1162 leafMem — the negative
verdict, which is the `else` arm of both callers. -/
@[grind →] theorem leafMem_of_false {st : EStore} (hwf : StoreWF st)
    {bl : List (Nat × EIdx)} {bl' : List (Nat × Expr)} {idx : Nat} {ty : EIdx}
    {t : Expr} (h : leafMem bl idx ty = false)
    (hb : denoteLeaves st bl = some bl') (ht : denoteE st ty = some t) :
    bl'.contains (idx, t) = false := by
  rw [← leafMem_spec hwf bl bl' hb idx ty t ht]; exact h

/-! ## 7. `fvarLeavesGo` and `fvarLeavesFast` — `ExprOps.lean:876`, `:906`

The `seen`-set walk and its entry point: **the one gap of group C**.  See the
module doc's last section for what is missing and why.  Both statements are
metavariable-free (`SeenA` and `LeavesEq` quantify the denotations inside
themselves), which is what lets `ExprOps/Guards.lean`'s `leafGuard` consume
them through `mvcgen`. -/

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1130-1152 fvarLeavesGoC — the
`seen` set's invariant, MINUS the gray clause: a node the walk has finished
has all its leaves in the accumulator. -/
def SeenA (st : EStore) (acc : List (Nat × EIdx))
    (seen : Std.HashMap EIdx Unit) : Prop :=
  ∀ (k : EIdx), seen[k]?.isSome = true →
    ∀ e ea, denoteE st k = some e → denoteLeaves st acc = some ea →
      ∀ x ∈ Expr.fvarLeaves e, x ∈ ea

/-- con-leche: none — the empty `seen` set satisfies the invariant at every
accumulator. -/
theorem SeenA.of_empty {st : EStore} {acc : List (Nat × EIdx)}
    {seen : Std.HashMap EIdx Unit} (h : seen = ∅) : SeenA st acc seen := by
  intro k hk; rw [h] at hk; simp at hk

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1130-1152 fvarLeavesGoC — the
walk's ANSWER relation: the result list has exactly the members of the
accumulator plus the subject's leaves.  Membership and not list equality,
because the `seen` set collects a shared subterm's leaves once where
`Expr.fvarLeaves` re-concatenates them per occurrence. -/
def LeavesEq (st : EStore) (acc : List (Nat × EIdx)) (c : EIdx)
    (res : List (Nat × EIdx)) : Prop :=
  ∀ e ea r, denoteE st c = some e → denoteLeaves st acc = some ea →
    denoteLeaves st res = some r →
      ∀ x, x ∈ r ↔ (x ∈ ea ∨ x ∈ Expr.fvarLeaves e)

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `fvarLeavesGo`'s recursion. -/
structure FvarLeavesGoSpec (rec : List (Nat × EIdx) → Std.HashMap EIdx Unit →
    EIdx → AM (List (Nat × EIdx) × Std.HashMap EIdx Unit)) : Prop where
  run : ∀ (s₁ : AState) (acc : List (Nat × EIdx))
      (seen : Std.HashMap EIdx Unit) (c : EIdx), StateOK s₁ →
      (denoteLeaves s₁.store acc).isSome = true → SeenA s₁.store acc seen →
      (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec acc seen c
    ⦃⇓? p s' => ⌜s' = s₁ ∧ (denoteLeaves s₁.store p.1).isSome = true ∧
        SeenA s₁.store p.1 p.2 ∧ LeavesEq s₁.store acc c p.1⌝⦄

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1130-1152 fvarLeavesGoC —
**THEOREM 1 for the memoized `fvarLeaves`**, at one level of the recursion.

**OPEN — this file's one `sorry`** (task #97-P3-0 group C).  What is missing
is the GRAY half of con-leche's `SeenInv`: the twin inserts `h` into `seen`
before walking `h`'s children, so `SeenA` is false *for `h`* at both
recursive calls, and restoring it needs "`h` is not reachable from a child of
`h`" — `StoreWF`'s rank witness, as an induction beside the fuel.  The
`x ∈ r → x ∈ ea ∨ x ∈ fvarLeaves e` half of `LeavesEq` needs no invariant at
all (a skipped node only REMOVES elements) and is the half a follow-up can
land first; the converse is the one that needs the rank.  This is the only
statement in group C that is not a fuel induction over `Bridge/Specs.lean`'s
`@[spec]` set. -/
theorem fvarLeavesGo_spec :
    ∀ fuel, FvarLeavesGoSpec (fun acc seen => fvarLeavesGo acc seen fuel) := by
  sorry

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1154-1155 fvarLeavesC —
**THEOREM 1 for `fvarLeavesFast`**: the reachable `fvar` leaves, up to
membership (`LeavesEq` at the empty accumulator).  Complete except for
`fvarLeavesGo_spec`'s gray clause, which it consumes. -/
theorem fvarLeavesFast_spec (fuel : Nat) (s₀ : AState) (h : EIdx)
    (hok : StateOK s₀) (hden : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ fvarLeavesFast fuel h
    ⦃⇓? rs s' => ⌜s' = s₀ ∧ (denoteLeaves s₀.store rs).isSome = true ∧
        LeavesEq s₀.store [] h rs⌝⦄ := by
  have hr := (fvarLeavesGo_spec fuel).run
  mvcgen [fvarLeavesFast, hr]
  all_goals bridge_vcs [SeenA.of_empty, denoteLeaves_nil]

/-! ## The axiom check -/

#print axioms denoteLeaves_append
#print axioms fvarLeaves_nil_of_hasFvar
#print axioms wscopedB_of_hasFvar
#print axioms hasFvar_false_of_derived
#print axioms fvarLeaves_spec
#print axioms leafMem_spec

end ConRon.Bridge.ExprOps

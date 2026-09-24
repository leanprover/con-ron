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
`SeenOK` / `Guards.lean`'s `LSubAt` are written the same way.  This is not
style: `fvarLeavesFast`'s answer list is the base of `leafGuard`'s membership
test, so a spec that named the base list as a PARAMETER would hand
`mvcgen` a side goal `denoteLeaves s.store bl = some ?bl'` with a
metavariable in it, which the closer cannot take (task #97s template rule 4,
measured again here).

## `fvarLeavesGo`'s `seen` set, and the rank (task #97-P3-2)

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
store — `StoreWF`'s rank witness.

Task #97-P3-0 called that "a second induction beside the fuel" and left the
walk open.  It is **cheaper than a second induction**: the rank enters as a
second *parameter of the invariant* (`SeenOK`, §7 — a key is gray when its
rank is above the current subject's) and the fuel induction is unchanged.
`EWFAt.childOK`'s rank clause is the only part of `StoreWF` used, the rank
is quantified INSIDE `SeenOK` so no statement in the file grew an argument,
and `fvarLeavesFast_spec` — the one `ExprOps/Guards.lean` consumes — is
where it was.  **Nothing in this file is unproved.**

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

The `seen`-set walk and its entry point.  Both statements are
metavariable-free (`SeenOK` and `LeavesEq` quantify what they speak about
inside themselves), which is what lets `ExprOps/Guards.lean`'s `leafGuard`
consume them through `mvcgen`.

### The gray invariant, and where the rank comes in

`fvarLeavesGo`'s memo is a visited SET whose entries are `Unit`, and an entry
means *"this node's leaves are already in `acc`"* — a statement about the
ACCUMULATOR, not about the node.  The twin inserts `h` into `seen` BEFORE it
walks `h`'s children, so that plain reading is FALSE for every node on the
descent path, and con-leche's `SeenInv` (`Verify/Cached/GuardsC.lean`) says
instead: every key of `seen` either has all its leaves in `acc` already
(BLACK) or is being processed by an ancestor of the current call (GRAY).

**"an ancestor of the current call" is read off `StoreWF`'s rank** (DESIGN
§8.3: "`StoreWF st` carries an existential rank `r : EIdx → Nat` with every
child ranked below its parent") — a gray key is one whose rank is ABOVE the
current subject's, and `EWFAt.childOK` is the only clause of the store
invariant the argument uses.  Task #97-P3-0 called this "a second induction
beside the fuel"; it is cheaper than that, because the rank enters as a
second *parameter of the invariant* and not as a second recursion — the fuel
induction is unchanged.  The rank is quantified INSIDE `SeenOK` (over every
rank the store admits, `∀ rk, EWFAt st rk → …`), which is template rule 6's
shape and is what keeps `fvarLeavesFast_spec`'s statement — the one
`ExprOps/Guards.lean` consumes — exactly where it was.

The three moving parts, and the lemmas that make the descent go:

* `SeenOK st acc seen c` is the invariant at subject `c`.  `SeenOK.of_grow`
  re-establishes it at a CHILD of `c` once `c` has been inserted and some
  prefix of its children walked, and that is the whole gray argument: the
  child's rank is below `c`'s, `c` itself is therefore gray for the child,
  and every key that was gray for `c` is a fortiori gray for the child;
* `SeenGrow st acc' seen seen'` is what a completed call gives back: every
  key of the returned set is either BLACK now, or was already a key of the
  set the call was given.  Composed with the incoming `SeenOK` it rebuilds
  the invariant for the next sibling, and at the end of an arm it is what
  turns the node's own gray entry black — the node's leaves ARE in the
  accumulator once its children have been walked;
* `AccGrow st acc acc'` is the accumulator's monotonicity, which is what
  carries a BLACK key past a sibling's walk.  It comes out of `LeavesEq`.

Because the answer is a SET and not a list — a shared subterm is walked once,
where `Expr.fvarLeaves` re-concatenates its leaves per occurrence — the
answer relation is membership equivalence and not list equality, and it is
not a weakening: `leafGuard`, the one consumer, uses the list only as a
membership base (`leafMem`), and `Guards.lean`'s `leavesSubSpec_congr` is
what makes that formally so. -/

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1130-1152 fvarLeavesGoC — a node
is BLACK at an accumulator when every leaf of the term it denotes is already
in the accumulator's denotation.  This is con-leche's `SeenInv` at one key,
minus the gray disjunct. -/
def BlackA (st : EStore) (acc : List (Nat × EIdx)) (k : EIdx) : Prop :=
  ∀ e ea, denoteE st k = some e → denoteLeaves st acc = some ea →
    ∀ x ∈ Expr.fvarLeaves e, x ∈ ea

/-- con-leche: none — the accumulator only ever GROWS, in the membership
sense every statement here is up to.  The source's own `isSome` is a field
rather than a hypothesis at the use sites, because the growth statement is
vacuous without it. -/
structure AccGrow (st : EStore) (acc acc' : List (Nat × EIdx)) : Prop where
  src : (denoteLeaves st acc).isSome = true
  sub : ∀ ea ea', denoteLeaves st acc = some ea →
    denoteLeaves st acc' = some ea' → ∀ x ∈ ea, x ∈ ea'

/-- con-leche: none — `AccGrow` is reflexive at an accumulator that denotes. -/
theorem AccGrow.refl {st : EStore} {acc : List (Nat × EIdx)}
    (h : (denoteLeaves st acc).isSome = true) : AccGrow st acc acc :=
  ⟨h, fun ea ea' h1 h2 x hx => by rw [h1] at h2; exact (Option.some.inj h2) ▸ hx⟩

/-- con-leche: none — and transitive. -/
theorem AccGrow.trans {st : EStore} {a b c : List (Nat × EIdx)}
    (h1 : AccGrow st a b) (h2 : AccGrow st b c) : AccGrow st a c := by
  refine ⟨h1.src, fun ea ec hea hec x hx => ?_⟩
  obtain ⟨eb, heb⟩ := Option.isSome_iff_exists.mp h2.src
  exact h2.sub eb ec heb hec x (h1.sub ea eb hea heb x hx)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:821-833 fvarLeaves — the `fvar`
arm's own growth: it PUSHES its leaf before descending into the
annotation. -/
theorem AccGrow.cons {st : EStore} {acc : List (Nat × EIdx)} {i : Nat}
    {t : EIdx} (hacc : (denoteLeaves st acc).isSome = true)
    (ht : (denoteE st t).isSome = true) : AccGrow st acc ((i, t) :: acc) := by
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp ht
  obtain ⟨ea, hea⟩ := Option.isSome_iff_exists.mp hacc
  refine ⟨hacc, fun e1 e2 h1 h2 x hx => ?_⟩
  rw [hea] at h1
  obtain rfl := Option.some.inj h1
  rw [denoteLeaves_cons ht' hea] at h2
  obtain rfl := Option.some.inj h2
  exact List.mem_cons_of_mem _ hx

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1130-1152 fvarLeavesGoC — a black
key stays black as the accumulator grows. -/
theorem BlackA.mono {st : EStore} {acc acc' : List (Nat × EIdx)} {k : EIdx}
    (hb : BlackA st acc k) (hg : AccGrow st acc acc') : BlackA st acc' k := by
  intro e ea' he hea' x hx
  obtain ⟨ea, hea⟩ := Option.isSome_iff_exists.mp hg.src
  exact hg.sub ea ea' hea hea' x (hb e ea he hea x hx)

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1093-1128 fvarLeavesGoC — **the
`seen` set's invariant, gray clause included**: at subject `c`, every key is
either black at the accumulator or of strictly greater rank than `c`, i.e.
an ancestor of the current call.  The rank is quantified inside (template
rule 6), so this statement has no more parameters than the plain one had. -/
def SeenOK (st : EStore) (acc : List (Nat × EIdx))
    (seen : Std.HashMap EIdx Unit) (c : EIdx) : Prop :=
  ∀ (rk : EIdx → Nat), EWFAt st rk → ∀ (k : EIdx), seen[k]?.isSome = true →
    rk c < rk k ∨ BlackA st acc k

/-- con-leche: none — the empty `seen` set satisfies the invariant at every
accumulator and every subject. -/
theorem SeenOK.of_empty {st : EStore} {acc : List (Nat × EIdx)}
    {seen : Std.HashMap EIdx Unit} {c : EIdx} (h : seen = ∅) :
    SeenOK st acc seen c := by
  intro _ _ k hk; rw [h] at hk; simp at hk

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1093-1128 fvarLeavesGoC — **what
a completed call gives back**: every key of the returned set is black at the
returned accumulator, or was already a key of the set the call was given. -/
def SeenGrow (st : EStore) (acc' : List (Nat × EIdx))
    (seen seen' : Std.HashMap EIdx Unit) : Prop :=
  ∀ (k : EIdx), seen'[k]?.isSome = true →
    BlackA st acc' k ∨ seen[k]?.isSome = true

/-- con-leche: none — the branches that return the set untouched. -/
theorem SeenGrow.refl {st : EStore} {acc : List (Nat × EIdx)}
    {seen : Std.HashMap EIdx Unit} : SeenGrow st acc seen seen :=
  fun _ hk => Or.inr hk

/-- con-leche: none — a key of an insert is the inserted key or an old one. -/
theorem seen_insert_cases {seen : Std.HashMap EIdx Unit} {j k : EIdx}
    (h : (seen.insert k ())[j]?.isSome = true) :
    j = k ∨ seen[j]?.isSome = true := by
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i hbeq; exact Or.inl (eq_of_beq hbeq).symm
  · exact Or.inr h

/-- con-leche: none — inserting a BLACK key is a `SeenGrow` step; this is the
four leaf views and, after the recursion, the node itself. -/
theorem SeenGrow.of_insert {st : EStore} {acc : List (Nat × EIdx)}
    {seen : Std.HashMap EIdx Unit} {k : EIdx} (hb : BlackA st acc k) :
    SeenGrow st acc seen (seen.insert k ()) := by
  intro j hj
  rcases seen_insert_cases hj with rfl | hj2
  · exact Or.inl hb
  · exact Or.inr hj2

/-- con-leche: none — `SeenGrow` composes along an arm's sequence of calls. -/
theorem SeenGrow.trans {st : EStore} {a1 a2 : List (Nat × EIdx)}
    {s0 s1 s2 : Std.HashMap EIdx Unit} (h1 : SeenGrow st a1 s0 s1)
    (h2 : SeenGrow st a2 s1 s2) (hg : AccGrow st a1 a2) :
    SeenGrow st a2 s0 s2 := by
  intro k hk
  rcases h2 k hk with hb | hin
  · exact Or.inl hb
  · rcases h1 k hin with hb | hin2
    · exact Or.inl (hb.mono hg)
    · exact Or.inr hin2

/-- con-leche: none — the node's own gray entry goes black once its children
are walked: `SeenGrow` from the INSERTED set, plus blackness of the node,
gives `SeenGrow` from the set the arm was handed. -/
theorem SeenGrow.drop_insert {st : EStore} {acc : List (Nat × EIdx)}
    {seen seen' : Std.HashMap EIdx Unit} {k : EIdx}
    (h : SeenGrow st acc (seen.insert k ()) seen') (hb : BlackA st acc k) :
    SeenGrow st acc seen seen' := by
  intro j hj
  rcases h j hj with hbj | hin
  · exact Or.inl hbj
  · rcases seen_insert_cases hin with rfl | hin2
    · exact Or.inl hb
    · exact Or.inr hin2

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1093-1128 fvarLeavesGoC — **the
gray argument**, in one lemma: the node `h` has been inserted and some prefix
of its children walked, and the invariant holds again at the next child `ch`.
`EWFAt.childOK`'s rank clause is the only thing used, and it is used twice —
once to make `h` itself gray for `ch`, once to carry `h`'s own gray keys
down. -/
theorem SeenOK.of_grow {st : EStore} {acc acc' : List (Nat × EIdx)}
    {seen seen' : Std.HashMap EIdx Unit} {h ch : EIdx} {v : ENodeView}
    (hview : st.view h = some v) (hch : ch ∈ v.echildren)
    (hs : SeenOK st acc seen h)
    (hg : SeenGrow st acc' (seen.insert h ()) seen')
    (hga : AccGrow st acc acc') : SeenOK st acc' seen' ch := by
  intro rk hrk k hk
  rcases hg k hk with hb | hin
  · exact Or.inr hb
  · have hlt : rk ch < rk h := (hrk.childOK h v hview ch hch).2.1
    rcases seen_insert_cases hin with rfl | hin2
    · exact Or.inl hlt
    · rcases hs rk hrk k hin2 with hgt | hb
      · exact Or.inl (Nat.lt_trans hlt hgt)
      · exact Or.inr (hb.mono hga)

/-- con-leche: none — the invariant at the FIRST child, which is
`SeenOK.of_grow` with nothing walked yet. -/
theorem SeenOK.child {st : EStore} {acc : List (Nat × EIdx)}
    {seen : Std.HashMap EIdx Unit} {h ch : EIdx} {v : ENodeView}
    (hview : st.view h = some v) (hch : ch ∈ v.echildren)
    (hs : SeenOK st acc seen h) (hacc : (denoteLeaves st acc).isSome = true) :
    SeenOK st acc (seen.insert h ()) ch :=
  SeenOK.of_grow hview hch hs SeenGrow.refl (AccGrow.refl hacc)

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

/-- con-leche: none — the accumulator grew, which is what carries a black key
past a sibling's walk. -/
theorem LeavesEq.accGrow {st : EStore} {acc res : List (Nat × EIdx)}
    {c : EIdx} (h : LeavesEq st acc c res)
    (hc : (denoteE st c).isSome = true)
    (hacc : (denoteLeaves st acc).isSome = true) : AccGrow st acc res := by
  refine ⟨hacc, fun ea er hea her x hx => ?_⟩
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hc
  exact (h e ea er he hea her x).mpr (Or.inl hx)

/-- con-leche: none — a finished call's subject is BLACK at its own answer,
which is what turns the node's gray entry black. -/
theorem LeavesEq.black {st : EStore} {acc res : List (Nat × EIdx)}
    {c : EIdx} (h : LeavesEq st acc c res)
    (hacc : (denoteLeaves st acc).isSome = true) : BlackA st res c := by
  intro e er he her x hx
  obtain ⟨ea, hea⟩ := Option.isSome_iff_exists.mp hacc
  exact (h e ea er he hea her x).mpr (Or.inr hx)

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1130-1152 fvarLeavesGoC — the
SKIP branch: a black subject adds nothing. -/
theorem LeavesEq.of_black {st : EStore} {acc : List (Nat × EIdx)} {c : EIdx}
    (hb : BlackA st acc c) : LeavesEq st acc c acc := by
  intro e ea r he hea hr x
  rw [hea] at hr
  obtain rfl := Option.some.inj hr
  exact ⟨fun hx => Or.inl hx, fun hx => hx.elim id (hb e ea he hea x)⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:821-833 fvarLeaves — the CUTOFF
branch and the four leaf views: a subject with no leaves adds nothing. -/
theorem LeavesEq.of_nil {st : EStore} {acc : List (Nat × EIdx)} {c : EIdx}
    (h : ∀ e, denoteE st c = some e → Expr.fvarLeaves e = []) :
    LeavesEq st acc c acc := by
  intro e ea r he hea hr x
  rw [hea] at hr
  obtain rfl := Option.some.inj hr
  rw [h e he]
  simp

/-- con-leche: ConLeche/Kernel/ExprOps.lean:821-833 fvarLeaves — a subject
with no leaves is black at every accumulator. -/
theorem BlackA.of_nil {st : EStore} {acc : List (Nat × EIdx)} {c : EIdx}
    (h : ∀ e, denoteE st c = some e → Expr.fvarLeaves e = []) :
    BlackA st acc c := by
  intro e ea he _ x hx
  rw [h e he] at hx
  exact absurd hx (by simp)

/-- con-leche: none — a subject whose leaf list is `[]` under `RelFL` has no
leaves, which is the form the four `RelFL.*_step` rules deliver. -/
theorem fvarLeaves_eq_nil_of_relFL {st : EStore} {c : EIdx} {e : Expr}
    (h : RelFL Expr.fvarLeaves st c []) (he : denoteE st c = some e) :
    Expr.fvarLeaves e = [] := by
  have h2 := h e he
  simp only [denoteLeaves] at h2
  exact (Option.some.inj h2).symm

/-! ### `LeavesEq`'s six step lemmas

`RelFL`'s ten at the memoized walk's shape: the arm has walked its children
in sequence, threading the accumulator, and what it owes is the statement at
the node.  Each is one `denote_*_inv`, the pure clause of `Expr.fvarLeaves`
and `List.mem_append`. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:821-833 fvarLeaves — the `fvar`
arm, which PUSHES its own leaf before descending into the annotation. -/
theorem LeavesEq.fvar_step {st : EStore} (hwf : StoreWF st)
    {acc res : List (Nat × EIdx)} {h ty : EIdx} {idx : Nat}
    (hview : st.view h = some (.fvar idx ty))
    (h1 : LeavesEq st ((idx, ty) :: acc) ty res) : LeavesEq st acc h res := by
  intro e ea r he hea hr x
  obtain ⟨t, rfl, hdt⟩ := denote_fvar_inv hwf hview he
  have hcons : denoteLeaves st ((idx, ty) :: acc) = some ((idx, t) :: ea) :=
    denoteLeaves_cons hdt hea
  have hp : Expr.fvarLeaves (.fvar idx t) = (idx, t) :: Expr.fvarLeaves t := by
    simp [Expr.fvarLeaves]
  rw [hp, h1 t ((idx, t) :: ea) r hdt hcons hr x]
  simp only [List.mem_cons]
  grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:821-833 fvarLeaves — the `app`
arm. -/
theorem LeavesEq.app_step {st : EStore} (hwf : StoreWF st)
    {acc mid res : List (Nat × EIdx)} {h f a : EIdx}
    (hview : st.view h = some (.app f a))
    (h1 : LeavesEq st acc f mid) (h2 : LeavesEq st mid a res)
    (hmid : (denoteLeaves st mid).isSome = true) : LeavesEq st acc h res := by
  intro e ea r he hea hr x
  obtain ⟨ef, eb, rfl, hdf, hdb⟩ := denote_app_inv hwf hview he
  obtain ⟨em, hem⟩ := Option.isSome_iff_exists.mp hmid
  have hp : Expr.fvarLeaves (.app ef eb) =
      Expr.fvarLeaves ef ++ Expr.fvarLeaves eb := by simp [Expr.fvarLeaves]
  rw [hp, h2 eb em r hdb hem hr x, h1 ef ea em hdf hea hem x, List.mem_append]
  grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:821-833 fvarLeaves — the `lam`
arm. -/
theorem LeavesEq.lam_step {st : EStore} (hwf : StoreWF st)
    {acc mid res : List (Nat × EIdx)} {h ty b : EIdx} {m : BinderMeta}
    (hview : st.view h = some (.lam ty b m))
    (h1 : LeavesEq st acc ty mid) (h2 : LeavesEq st mid b res)
    (hmid : (denoteLeaves st mid).isSome = true) : LeavesEq st acc h res := by
  intro e ea r he hea hr x
  obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_lam_inv hwf hview he
  obtain ⟨em, hem⟩ := Option.isSome_iff_exists.mp hmid
  have hp : Expr.fvarLeaves (.lam et eb m) =
      Expr.fvarLeaves et ++ Expr.fvarLeaves eb := by simp [Expr.fvarLeaves]
  rw [hp, h2 eb em r hdb hem hr x, h1 et ea em hdt hea hem x, List.mem_append]
  grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:821-833 fvarLeaves — the
`forallE` arm. -/
theorem LeavesEq.forallE_step {st : EStore} (hwf : StoreWF st)
    {acc mid res : List (Nat × EIdx)} {h ty b : EIdx} {m : BinderMeta}
    (hview : st.view h = some (.forallE ty b m))
    (h1 : LeavesEq st acc ty mid) (h2 : LeavesEq st mid b res)
    (hmid : (denoteLeaves st mid).isSome = true) : LeavesEq st acc h res := by
  intro e ea r he hea hr x
  obtain ⟨et, eb, rfl, hdt, hdb⟩ := denote_forallE_inv hwf hview he
  obtain ⟨em, hem⟩ := Option.isSome_iff_exists.mp hmid
  have hp : Expr.fvarLeaves (.forallE et eb m) =
      Expr.fvarLeaves et ++ Expr.fvarLeaves eb := by simp [Expr.fvarLeaves]
  rw [hp, h2 eb em r hdb hem hr x, h1 et ea em hdt hea hem x, List.mem_append]
  grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:821-833 fvarLeaves — the `letE`
arm, three calls deep. -/
theorem LeavesEq.letE_step {st : EStore} (hwf : StoreWF st)
    {acc m1 m2 res : List (Nat × EIdx)} {h ty w b : EIdx}
    (hview : st.view h = some (.letE ty w b))
    (h1 : LeavesEq st acc ty m1) (h2 : LeavesEq st m1 w m2)
    (h3 : LeavesEq st m2 b res) (hm1 : (denoteLeaves st m1).isSome = true)
    (hm2 : (denoteLeaves st m2).isSome = true) : LeavesEq st acc h res := by
  intro e ea r he hea hr x
  obtain ⟨et, ew, eb, rfl, hdt, hdw, hdb⟩ := denote_letE_inv hwf hview he
  obtain ⟨e1, he1⟩ := Option.isSome_iff_exists.mp hm1
  obtain ⟨e2, he2⟩ := Option.isSome_iff_exists.mp hm2
  have hp : Expr.fvarLeaves (.letE et ew eb) =
      Expr.fvarLeaves et ++ Expr.fvarLeaves ew ++ Expr.fvarLeaves eb := by
    simp [Expr.fvarLeaves]
  rw [hp, h3 eb e2 r hdb he2 hr x, h2 ew e1 e2 hdw he1 he2 x,
    h1 et ea e1 hdt hea he1 x, List.mem_append, List.mem_append]
  grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:821-833 fvarLeaves — the `proj`
arm: the struct name is not a leaf. -/
theorem LeavesEq.proj_step {st : EStore} (hwf : StoreWF st)
    {acc res : List (Nat × EIdx)} {h sub : EIdx} {n : NIdx} {i : Nat}
    (hview : st.view h = some (.proj n i sub))
    (h1 : LeavesEq st acc sub res) : LeavesEq st acc h res := by
  intro e ea r he hea hr x
  obtain ⟨nm, es, rfl, _, hds⟩ := denote_proj_inv hwf hview he
  have hp : Expr.fvarLeaves (.proj nm i es) = Expr.fvarLeaves es := by
    simp [Expr.fvarLeaves]
  rw [hp]
  exact h1 es ea r hds hea hr x

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `fvarLeavesGo`'s recursion. -/
structure FvarLeavesGoSpec (rec : List (Nat × EIdx) → Std.HashMap EIdx Unit →
    EIdx → AM (List (Nat × EIdx) × Std.HashMap EIdx Unit)) : Prop where
  run : ∀ (s₁ : AState) (acc : List (Nat × EIdx))
      (seen : Std.HashMap EIdx Unit) (c : EIdx), StateOK s₁ →
      (denoteLeaves s₁.store acc).isSome = true → SeenOK s₁.store acc seen c →
      (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec acc seen c
    ⦃⇓? p s' => ⌜s' = s₁ ∧ (denoteLeaves s₁.store p.1).isSome = true ∧
        SeenGrow s₁.store p.1 seen p.2 ∧ LeavesEq s₁.store acc c p.1⌝⦄

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1130-1152 fvarLeavesGoC —
**THEOREM 1 for the memoized `fvarLeaves`**, at one level of the recursion,
by induction on the fuel.  The gray half of con-leche's `SeenInv` is
`SeenOK`'s rank disjunct and `SeenOK.of_grow` is the whole of the argument;
see the section header. -/
theorem fvarLeavesGo_spec :
    ∀ fuel, FvarLeavesGoSpec (fun acc seen => fvarLeavesGo acc seen fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ acc seen c _ _ _ _
    mvcgen [fvarLeavesGo_zero]
    all_goals bridge_vcs [denoteLeaves_nil]
  | succ fuel ih =>
    constructor
    intro s₀ acc seen c hok hacc hseen hden
    have hrec := ih.run
    mvcgen [fvarLeavesGo_succ, fvarLeavesGoArmApp, fvarLeavesGoArmBind,
      fvarLeavesGoArmLet, hrec]
    all_goals (bridge_peel; subst_vars)
    all_goals try bridge_vcs [denoteLeaves_nil]
    -- Twenty-four verification conditions survive the closer, in five shapes:
    -- the two early exits, the four leaf views, one `SeenOK` side goal per
    -- recursive call (nine of them) and one postcondition per arm (seven).
    -- **The cutoff**: a zero fvar-range field means no leaves at all.
    next hcut =>
      exact ⟨rfl, hacc, SeenGrow.refl, LeavesEq.of_nil fun e he =>
        fvarLeaves_nil_of_hasFvar e
          (hasFvar_false_of_derived hok.wf he (by simpa using hcut))⟩
    -- **The `seen` HIT**: the invariant's gray disjunct is `rk c < rk c`,
    -- which is what the rank is in the invariant for.
    next _ hhit _ _ =>
      obtain ⟨rk, hrk⟩ := hok.wf
      refine ⟨rfl, hacc, SeenGrow.refl, LeavesEq.of_black ?_⟩
      rcases hseen rk hrk c (by rw [hhit]; rfl) with hlt | hb
      · exact absurd hlt (Nat.lt_irrefl _)
      · exact hb
    -- **The four leaf views**: no leaves, so the node goes in BLACK.
    next hview _ =>
      exact ⟨rfl, hacc,
        SeenGrow.of_insert (BlackA.of_nil fun e he =>
          fvarLeaves_eq_nil_of_relFL (RelFL.bvar_step hok.wf hview) he),
        LeavesEq.of_nil fun e he =>
          fvarLeaves_eq_nil_of_relFL (RelFL.bvar_step hok.wf hview) he⟩
    next hview _ =>
      exact ⟨rfl, hacc,
        SeenGrow.of_insert (BlackA.of_nil fun e he =>
          fvarLeaves_eq_nil_of_relFL (RelFL.sort_step hok.wf hview) he),
        LeavesEq.of_nil fun e he =>
          fvarLeaves_eq_nil_of_relFL (RelFL.sort_step hok.wf hview) he⟩
    next hview _ =>
      exact ⟨rfl, hacc,
        SeenGrow.of_insert (BlackA.of_nil fun e he =>
          fvarLeaves_eq_nil_of_relFL (RelFL.const_step hok.wf hview) he),
        LeavesEq.of_nil fun e he =>
          fvarLeaves_eq_nil_of_relFL (RelFL.const_step hok.wf hview) he⟩
    next hview _ =>
      exact ⟨rfl, hacc,
        SeenGrow.of_insert (BlackA.of_nil fun e he =>
          fvarLeaves_eq_nil_of_relFL (RelFL.lit_step hok.wf hview) he),
        LeavesEq.of_nil fun e he =>
          fvarLeaves_eq_nil_of_relFL (RelFL.lit_step hok.wf hview) he⟩
    -- **The `fvar` arm**: its own leaf is pushed first, so its `AccGrow` is
    -- `AccGrow.cons` and its step lemma carries the pushed pair back out.
    next hview _ =>
      intro hs h1 h2 h3
      have hle := LeavesEq.fvar_step hok.wf hview h3
      exact ⟨hs, h1, h2.drop_insert (hle.black hacc), hle⟩
    next =>
      intro s hs hview
      subst hs
      exact Option.isSome_iff_exists.mpr
        ⟨_, denoteLeaves_cons
          (Option.isSome_iff_exists.mp (isSome_fvar hok.wf hview hden)).choose_spec
          (Option.isSome_iff_exists.mp hacc).choose_spec⟩
    next =>
      intro s hs hview
      subst hs
      exact SeenOK.of_grow hview (by simp [ENodeView.echildren]) hseen
        SeenGrow.refl (AccGrow.cons hacc (isSome_fvar hok.wf hview hden))
    -- **The `app` arm**: two calls, and `SeenOK.of_grow` at each.
    next hview _ =>
      exact SeenOK.child hview (by simp [ENodeView.echildren]) hseen hacc
    next hm1 hsg1 hle1 hview _ =>
      intro hs h1 h2 h3
      have hle := LeavesEq.app_step hok.wf hview hle1 h3 hm1
      refine ⟨hs, h1, ?_, hle⟩
      exact (SeenGrow.trans hsg1 h2
        (h3.accGrow (isSome_app hok.wf hview hden).2 hm1)).drop_insert
        (hle.black hacc)
    next hview _ =>
      intro s hs h1 h2 h3
      subst hs
      exact SeenOK.of_grow hview (by simp [ENodeView.echildren]) hseen h2
        (h3.accGrow (isSome_app hok.wf hview hden).1 hacc)
    -- **The binder arms**, `lam` then `forallE`; the twin shares one `def`
    -- and `mvcgen` still hands the two views separately.
    next hview _ =>
      exact SeenOK.child hview (by simp [ENodeView.echildren]) hseen hacc
    next hm1 hsg1 hle1 hview _ =>
      intro hs h1 h2 h3
      have hle := LeavesEq.lam_step hok.wf hview hle1 h3 hm1
      refine ⟨hs, h1, ?_, hle⟩
      exact (SeenGrow.trans hsg1 h2
        (h3.accGrow (isSome_lam hok.wf hview hden).2 hm1)).drop_insert
        (hle.black hacc)
    next hview _ =>
      intro s hs h1 h2 h3
      subst hs
      exact SeenOK.of_grow hview (by simp [ENodeView.echildren]) hseen h2
        (h3.accGrow (isSome_lam hok.wf hview hden).1 hacc)
    next hview _ =>
      exact SeenOK.child hview (by simp [ENodeView.echildren]) hseen hacc
    next hm1 hsg1 hle1 hview _ =>
      intro hs h1 h2 h3
      have hle := LeavesEq.forallE_step hok.wf hview hle1 h3 hm1
      refine ⟨hs, h1, ?_, hle⟩
      exact (SeenGrow.trans hsg1 h2
        (h3.accGrow (isSome_forallE hok.wf hview hden).2 hm1)).drop_insert
        (hle.black hacc)
    next hview _ =>
      intro s hs h1 h2 h3
      subst hs
      exact SeenOK.of_grow hview (by simp [ENodeView.echildren]) hseen h2
        (h3.accGrow (isSome_forallE hok.wf hview hden).1 hacc)
    -- **The `letE` arm**: three calls, so `SeenGrow.trans` twice.  Its second
    -- side goal arrives with the first call's facts already in the context
    -- (no `∀ s` to introduce), which the third's does have.
    next hview _ =>
      exact SeenOK.child hview (by simp [ENodeView.echildren]) hseen hacc
    next hm1 hsg1 hle1 hview _ =>
      exact SeenOK.of_grow hview (by simp [ENodeView.echildren]) hseen hsg1
        (hle1.accGrow (isSome_letE hok.wf hview hden).1 hacc)
    next hm2 hsg2 hle2 hm1 hsg1 hle1 hview _ =>
      intro hs h1 h2 h3
      have hg2 := hle2.accGrow (isSome_letE hok.wf hview hden).2.1 hm1
      have hle := LeavesEq.letE_step hok.wf hview hle1 hle2 h3 hm1 hm2
      refine ⟨hs, h1, ?_, hle⟩
      exact (SeenGrow.trans (SeenGrow.trans hsg1 hsg2 hg2) h2
        (h3.accGrow (isSome_letE hok.wf hview hden).2.2 hm2)).drop_insert
        (hle.black hacc)
    next hm1 hsg1 hle1 hview _ =>
      intro s hs h1 h2 h3
      subst hs
      have hg2 := h3.accGrow (isSome_letE hok.wf hview hden).2.1 hm1
      exact SeenOK.of_grow hview (by simp [ENodeView.echildren]) hseen
        (SeenGrow.trans hsg1 h2 hg2)
        ((hle1.accGrow (isSome_letE hok.wf hview hden).1 hacc).trans hg2)
    -- **The `proj` arm**: the struct name is not a leaf.
    next hview _ =>
      intro hs h1 h2 h3
      have hle := LeavesEq.proj_step hok.wf hview h3
      exact ⟨hs, h1, h2.drop_insert (hle.black hacc), hle⟩
    next =>
      intro s hs hview
      subst hs
      exact SeenOK.child hview (by simp [ENodeView.echildren]) hseen hacc


/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1154-1155 fvarLeavesC —
**THEOREM 1 for `fvarLeavesFast`**: the reachable `fvar` leaves, up to
membership (`LeavesEq` at the empty accumulator). -/
theorem fvarLeavesFast_spec (fuel : Nat) (s₀ : AState) (h : EIdx)
    (hok : StateOK s₀) (hden : (denoteE s₀.store h).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ fvarLeavesFast fuel h
    ⦃⇓? rs s' => ⌜s' = s₀ ∧ (denoteLeaves s₀.store rs).isSome = true ∧
        LeavesEq s₀.store [] h rs⌝⦄ := by
  have hr := (fvarLeavesGo_spec fuel).run
  mvcgen [fvarLeavesFast, hr]
  all_goals bridge_vcs [SeenOK.of_empty, denoteLeaves_nil]

/-! ## The axiom check -/

#print axioms denoteLeaves_append
#print axioms fvarLeaves_nil_of_hasFvar
#print axioms wscopedB_of_hasFvar
#print axioms hasFvar_false_of_derived
#print axioms fvarLeaves_spec
#print axioms leafMem_spec
#print axioms SeenOK.of_grow
#print axioms fvarLeavesGo_spec
#print axioms fvarLeavesFast_spec

end ConRon.Bridge.ExprOps

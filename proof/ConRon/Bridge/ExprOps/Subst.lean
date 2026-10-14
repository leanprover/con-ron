/-
# `ConRon.Bridge.ExprOps.Subst` — Theorem 1 for the SUBSTITUTING walks

DESIGN §8.2's Theorem 1 for group A of the `ExprOps` bridge tier (task
#97-P3-0): `instantiateList`, `liftLooseBVars`,
`instantiate1Lift`, `instPisAtLift` and the three pure `Array` helpers the
first of them consumes.  `ExprOps/Inst1.lean` was the exemplar and this file
keeps its shape — the `…Spec` record for one level of the recursion, the fuel
induction, the per-arm theorems of the tag-dispatching walks.

## The closer

Every verification condition is closed by

```lean
  sym only [bridge_grind, <the pure function's equations>] =>
    vcgen [<the program>, <callee specs as terms>] <;> finish
```

with no step lemma per arm: `grind` reads the answer relations as `MapRel`
facts on the denotation terms, a denotation's constructor from its tag
(`exprTag_*`) and its children from its view (`DenoteView`) — all
`Bridge/Grind.lean`'s — the pure function by its own equation lemmas, the
store chain by the order solver, the memo tables by
`MemoOK.le`/`.get`/`.insert_at`/`.of_empty`, and the derived-word
cutoffs as linear arithmetic over `DerivedBound` (§G; the word's bound field IS the
denotation's `bvarBound` below the saturation), so that each licence is one
lemma keyed by the cut subject's `bvarBound` (§H).

## What is here

| twin | `Arena/ExprOps.lean` | statement |
|---|---|---|
| `eidxCopyUpto` | :205 | `eidxCopyUpto_toList` |
| `takeEidx` | :221 | `takeEidx_toList`, `denoteEList_takeEidx` |
| `lastEidx` | :225 | `lastEidx_toList`, `denoteEList_lastEidx`, `InstLVec.last` |
| `instantiateList` | :431 | `InstLPureSpec`, `instListArm{App,Bind,Let,Proj,BVar}_spec`, `instantiateList_spec` |
| `instantiateListGo` | :558 | `InstLSpec`, `instListGoArm{App,Bind,Let,Proj}_spec`, `instantiateListGo_spec` |
| `instantiateListFast` | :670 | `instantiateListFast_spec`, `_run` |
| `liftLooseBVarsGo` | :491 | `LiftSpec`, `liftLooseBVarsGo_spec` |
| `liftLooseBVarsFast` | :552 | `liftLooseBVarsFast_spec`, `_run` |
| `instantiate1LiftGo` | :1779 | `Inst1LSpec`, `instantiate1LiftGo_spec` |
| `instantiate1LiftFast` | :1843 | `instantiate1LiftFast_spec`, `_run` |
| `instPisAtLift` | :3057 | `RelEO.instPisAtLift_{cons,none}`, `instPisAtLift_spec` |

## The four deviations from con-leche this group carries

1. **`instantiateList` / `instantiateListGo` carry a derived-word cutoff
   con-leche does not have** (task #97f; `ExprOps.lean`'s module note states
   the licence as `looseBVarsBounded d e → instantiateList e vs d = e`).  It is
   proved here as `instantiateList_of_bvarBound_le`, modelled on
   `Inst1.lean`'s `instantiate1_of_bvarBound_le`, and taken at the packed
   field by `instantiateList_of_raw_le` (`Expr.bvarBRaw_exact`).  The cutoff
   appears TWICE in the walk — at the node, and hoisted over the prefix copy
   at the replacement (task #97-P6-9) — and both uses are licensed by it.
2. **`liftLooseBVarsGo` likewise** (`bvarBRaw < satRange && bvarBRaw ≤ c`):
   `liftLooseBVars_of_bvarBound_le`, the same induction at a different offset.
3. **`instantiate1LiftGo`'s cutoff IS con-leche's own**, so its licence is
   QUOTED, not reproved: `Expr.instantiate1Lift_of_bvarBound_le`, wrapped as
   `Inst1LAt.cutoff`.
4. **The substitution vector is an `Array EIdx` in PUSH order** (task
   #97-P6-15, DESIGN §8.6's accumulator ruling): con-leche's `vs[j - d]` is the
   twin's entry `j - d` counted FROM THE END (`ExprOps.lean`'s own note,
   "con-leche's `[cf, s1]` is the twin's `#[s1, cf]`"; `ExprOpsTest.lean`'s
   `instantiateList` guards).  So the array's denotation is the **reverse** of
   the list `Expr.instantiateList` takes, and `InstLVec st vs ws :=
   Frontend.denoteEList st vs.toList = some ws.reverse` is that orientation,
   written down once.  `InstLVec.get` (slot `size - 1 - m` denotes `ws[m]`) and
   `InstLVec.last` (`lastEidx vs m` denotes `ws.take m`) are the two facts the
   `.bvar` arm consumes, and `reverse_drop_eq_take_reverse` is the list law
   behind the second.

## The arm split, at this file's two tag-dispatching walks (task #97-P3-2)

DESIGN §8.6's arm-split ruling, carried into the proof for `instantiateList`
and `instantiateListGo`: one theorem per constructor arm
(`instListArm…_spec`, `instListGoArm…_spec`), each taking the previous fuel
level's record as its induction hypothesis and its own tag hypothesis, and a
dispatcher whose `vcgen` list is the arm theorems.  The dispatcher's own
conditions are the derived-word cutoff and the catch-all leaf
(`instantiateList_leaf`); the `.bvar` arm's four branches are
`instantiateList_bvar_eq`'s two `if`s and the vector's indexed read
(`InstLVec.getElem_eq`, `InstLVec.last`).

## Two mechanical points

* **A spec parameter the program does not mention is left open by
  `vcgen`.**  `Bridge/Specs.lean`'s four memo-insert specs
  (`instLSet_spec`, `liftSet_spec`, `inst1LSet_spec`) take the
  walk's own parameter — `ws`, `amount`, `ve` — as an ordinary argument,
  which nothing in the program determines.  The generic specs make the PURE
  FUNCTION the parameter (`f : Nat → Expr → Expr`), registered
  `@[spec high]` (a later `@[spec]` does **not** override an earlier one for
  the same program), and each walk passes them INSTANTIATED in its `vcgen`
  list.  `liftSet_specG` carries the full note.
* **`bvarB` is not one of these twins**, and `instantiate1LiftGo` tests it.  Round 3 carried its Theorem 1 as a
  hypothesis `hbb : ∀ f, BvarBSpec (bvarB f)`; **round 4 discharged it**
  (`bvarB_bvarBSpec`) and deleted every binder, so the entry points and
  `instPisAtLift_spec` are callable with no hypothesis about `bvarB` at all.
  The discharge was not free: `Bridge/ExprOps/Ranges.lean` had to state the
  memo-frame conjunct `BvarBSpec` asks for and `bvarB_spec` did not
  (`s'.memos.inst1LC`) — see §4 of that round.
-/
import ConRon.Bridge.Specs
import ConRon.Bridge.ExprOps.Ranges
import ConRon.Bridge.Grind

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 4000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

/-! ## A. Three list facts core does not ship -/

/-- con-leche: none — dropping a prefix's length off a concatenation. -/
theorem drop_append_length {α : Type} :
    ∀ (l₁ l₂ : List α), (l₁ ++ l₂).drop l₁.length = l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; rfl
  | cons a as ih =>
    intro l₂
    simp only [List.length_cons, List.cons_append, List.drop_succ_cons]
    exact ih l₂

/-- con-leche: none — **the reversal law the push-order substitution vector
needs**: the LAST `m` entries of a list, reversed, are the FIRST `m` entries of
its reverse. -/
theorem reverse_drop_eq_take_reverse {α : Type} (l : List α) (m : Nat) :
    l.reverse.drop (l.length - m) = (l.take m).reverse := by
  have h1 : l.reverse = (l.drop m).reverse ++ (l.take m).reverse := by
    rw [← List.reverse_append, List.take_append_drop]
  have h2 : (l.drop m).reverse.length = l.length - m := by
    rw [List.length_reverse, List.length_drop]
  rw [h1, ← h2, drop_append_length]

/-! ## B. `Frontend.denoteEList`, pointwise

Four facts, in the shape `denoteEList_ext` (`Bridge/Rel.lean` group 6c) is
written in.  **They morally belong in `Bridge/Rel.lean`** next to
`denoteEList_ext`; task #97-P3-0 owns only this file, so they live here. -/

/-- con-leche: none — a denoting handle list has the length of its
denotation. -/
theorem denoteEList_length {st : EStore} :
    ∀ (l : List EIdx) (es : List Expr),
      Frontend.denoteEList st l = some es → es.length = l.length := by
  intro l
  induction l with
  | nil =>
    intro es h
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    simp [← h]
  | cons a as ih =>
    intro es h
    simp only [Frontend.denoteEList] at h
    cases ha : denoteE st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteEList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        simp only [Option.some.injEq] at h
        rw [← h]
        simp [ih ys has]

/-- con-leche: none — a prefix of a denoting handle list denotes the prefix. -/
theorem denoteEList_take {st : EStore} :
    ∀ (k : Nat) (l : List EIdx) (es : List Expr),
      Frontend.denoteEList st l = some es →
        Frontend.denoteEList st (l.take k) = some (es.take k) := by
  intro k
  induction k with
  | zero => intro l es _; simp [Frontend.denoteEList]
  | succ k ih =>
    intro l es h
    cases l with
    | nil =>
      simp only [Frontend.denoteEList, Option.some.injEq] at h
      simp [← h, Frontend.denoteEList]
    | cons a as =>
      simp only [Frontend.denoteEList] at h
      cases ha : denoteE st a with
      | none => rw [ha] at h; simp at h
      | some y =>
        cases has : Frontend.denoteEList st as with
        | none => rw [ha, has] at h; simp at h
        | some ys =>
          rw [ha, has] at h
          simp only [Option.some.injEq] at h
          subst h
          simp only [List.take_succ_cons, Frontend.denoteEList, ha, ih as ys has]

/-- con-leche: none — and a suffix denotes the suffix. -/
theorem denoteEList_drop {st : EStore} :
    ∀ (k : Nat) (l : List EIdx) (es : List Expr),
      Frontend.denoteEList st l = some es →
        Frontend.denoteEList st (l.drop k) = some (es.drop k) := by
  intro k
  induction k with
  | zero => intro l es h; simpa using h
  | succ k ih =>
    intro l es h
    cases l with
    | nil =>
      simp only [Frontend.denoteEList, Option.some.injEq] at h
      simp [← h, Frontend.denoteEList]
    | cons a as =>
      simp only [Frontend.denoteEList] at h
      cases ha : denoteE st a with
      | none => rw [ha] at h; simp at h
      | some y =>
        cases has : Frontend.denoteEList st as with
        | none => rw [ha, has] at h; simp at h
        | some ys =>
          rw [ha, has] at h
          simp only [Option.some.injEq] at h
          subst h
          simp only [List.drop_succ_cons]
          exact ih as ys has

/-- con-leche: none — the `i`-th slot of a denoting handle list denotes the
`i`-th entry of its denotation (`Specs.lean`'s `denoteNL_get` at the
EXPRESSION store, and with `getElem?` rather than a length hypothesis). -/
theorem denoteEList_getElem? {st : EStore} :
    ∀ (l : List EIdx) (es : List Expr),
      Frontend.denoteEList st l = some es → ∀ (i : Nat) (x : EIdx),
        l[i]? = some x → ∃ y, es[i]? = some y ∧ denoteE st x = some y := by
  intro l
  induction l with
  | nil => intro es _ i x hx; simp at hx
  | cons a as ih =>
    intro es h i x hx
    simp only [Frontend.denoteEList] at h
    cases ha : denoteE st a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteEList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        simp only [Option.some.injEq] at h
        subst h
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst hx
          exact ⟨y, rfl, ha⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx ⊢
          exact ih ys has i x hx

/-! ## C. The three pure `Array` helpers (`ExprOps.lean:205`, `:221`, `:225`)

`eidxCopyUpto`'s answer as a list, and the two windows the substituting walks
cut out of a push-order vector. -/

/-- con-leche: none — **Theorem 1 for `eidxCopyUpto`** (`ExprOps.lean:205`):
the copy appends the window `xs[i], …, xs[k-1]` to the accumulator.  It is
unconditional: the `i < xs.size` guard stops the copy at the array's end, and
`List.take` saturates there too. -/
theorem eidxCopyUpto_toList (xs : Array EIdx) (k : Nat) :
    ∀ (i : Nat) (out : Array EIdx),
      (eidxCopyUpto xs k i out).toList
        = out.toList ++ (xs.toList.drop i).take (k - i) := by
  intro i out
  induction i, out using eidxCopyUpto.induct xs k with
  | case1 i out h ih =>
    have hlt : i < xs.toList.length := by
      rw [Array.length_toList]; exact h.2
    rw [eidxCopyUpto, dite_eq_left h, ih, Array.toList_push,
      List.drop_eq_getElem_cons hlt, show k - i = (k - i - 1) + 1 from by omega,
      List.take_succ_cons]
    simp only [Array.getElem_toList, List.append_assoc, List.cons_append,
      List.nil_append, show k - i - 1 = k - (i + 1) from by omega]
  | case2 i out h =>
    rcases Nat.lt_or_ge i k with hk | hk
    · have hd : xs.toList.drop i = [] := by
        apply List.drop_eq_nil_of_le
        rw [Array.length_toList]; omega
      rw [eidxCopyUpto, dite_eq_right h, hd]
      simp
    · rw [eidxCopyUpto, dite_eq_right h, show k - i = 0 from by omega]
      simp

/-- con-leche: none — **Theorem 1 for `takeEidx`** (`ExprOps.lean:221`): the
first `k` slots, as a list. -/
theorem takeEidx_toList (xs : Array EIdx) (k : Nat) :
    (takeEidx xs k).toList = xs.toList.take k := by
  rw [takeEidx, eidxCopyUpto_toList]
  simp

/-- con-leche: none — **Theorem 1 for `lastEidx`** (`ExprOps.lean:225`): the
LAST `k` slots, as a list.  The `if` in the definition is `xs.size - k` in both
branches, which is why the answer has no case split. -/
theorem lastEidx_toList (xs : Array EIdx) (k : Nat) :
    (lastEidx xs k).toList = xs.toList.drop (xs.size - k) := by
  have hi : (if k < xs.size then xs.size - k else 0) = xs.size - k := by
    split <;> omega
  rw [lastEidx, eidxCopyUpto_toList, hi]
  simp only [List.nil_append]
  exact List.take_of_length_le (by simp)

/-! ## D. The push-order substitution vector (task #97-P6-15)

**The orientation, written down once.**  `vs : Array EIdx` is in PUSH order
(DESIGN §8.6's accumulator ruling): con-leche's `vs[j - d]` — the innermost
peeled binder's argument first — is this array's entry `j - d` counted FROM THE
END (`ExprOps.lean`'s own note, "con-leche's `[cf, s1]` is the twin's
`#[s1, cf]`", and `ExprOpsTest.lean`'s guards).  So the array's own denotation
is the REVERSE of the list `Expr.instantiateList` takes, and `InstLVec` is the
one place that reversal appears. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:211-235 instantiateList (the `vs`
argument) — the push-order vector `vs` denotes the pure walk's list `ws`. -/
def InstLVec (st : EStore) (vs : Array EIdx) (ws : List Expr) : Prop :=
  Frontend.denoteEList st vs.toList = some ws.reverse

/-- con-leche: none — the vector's length is the list's. -/
theorem InstLVec.length {st : EStore} {vs : Array EIdx} {ws : List Expr}
    (h : InstLVec st vs ws) : ws.length = vs.size := by
  have h2 := denoteEList_length vs.toList ws.reverse h
  rw [List.length_reverse, Array.length_toList] at h2
  exact h2

/-- con-leche: none — the vector still denotes after the arena grew. -/
theorem InstLVec.ext {st st' : EStore} {vs : Array EIdx} {ws : List Expr}
    (h : InstLVec st vs ws) (hx : Ext st st') : InstLVec st' vs ws :=
  denoteEList_ext hx _ _ h

/-- con-leche: ConLeche/Kernel/ExprOps.lean:228 instantiateList (the `.bvar`
arm's `vs.take (j - d)`) — **`lastEidx` is `List.take`, through the
reversal**: the last `m` slots of the push-order vector denote the pure walk's
`ws.take m`. -/
theorem InstLVec.last {st : EStore} {vs : Array EIdx} {ws : List Expr}
    (h : InstLVec st vs ws) (m : Nat) :
    InstLVec st (lastEidx vs m) (ws.take m) := by
  rw [InstLVec, lastEidx_toList, denoteEList_drop _ _ _ h, ← h.length,
    reverse_drop_eq_take_reverse]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:227 instantiateList (the `.bvar`
arm's `vs[j - d]`) — **the indexed read, through the reversal**: slot
`size - 1 - m` of the push-order vector denotes `ws[m]`. -/
theorem InstLVec.get {st : EStore} {vs : Array EIdx} {ws : List Expr}
    {m : Nat} {x : EIdx} (h : InstLVec st vs ws) (hm : m < vs.size)
    (hx : vs[vs.size - 1 - m]? = some x) :
    ∃ w, ws[m]? = some w ∧ denoteE st x = some w := by
  have hl := h.length
  obtain ⟨y, hy, hd⟩ :=
    denoteEList_getElem? vs.toList ws.reverse h (vs.size - 1 - m) x (by simpa using hx)
  refine ⟨y, ?_, hd⟩
  rw [List.getElem?_reverse (by omega),
    show ws.length - 1 - (vs.size - 1 - m) = m from by omega] at hy
  exact hy

/-! ## E. The two derived cutoffs' licences (task #97f's deviation)

`instantiateList` and `liftLooseBVars` carry a cutoff con-leche does NOT have
(`ExprOps.lean`'s module note, "The two derived cutoffs").  Its licence is the
analogue of `Inst1.lean`'s `instantiate1_of_bvarBound_le` and of con-leche's
own `instantiate1Lift_of_bvarBound_le`: the same induction at a different
offset. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:211-235 instantiateList — **the
first derived cutoff's licence**: a term with no loose `bvar` at or above the
cursor is its own bulk instantiation.  `looseBVarsBounded d e →
instantiateList e vs d = e`, which is what `ExprOps.lean`'s module note asks
P3 to discharge. -/
theorem instantiateList_of_bvarBound_le {ws : List Expr} :
    ∀ (e : Expr) (d : Nat), e.bvarBound ≤ d → e.instantiateList ws d = e := by
  intro e
  induction e with
  | bvar i =>
    intro d h
    simp only [Expr.bvarBound] at h
    have hi : i < d := by omega
    simp [Expr.instantiateList, hi]
  | fvar _ _ _ | sort _ | const _ _ | lit _ =>
    intro d _; simp [Expr.instantiateList]
  | app f a ihf iha =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    rw [Expr.instantiateList, ihf d h.1, iha d h.2]
  | lam ty b iht ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    rw [Expr.instantiateList, iht d h.1, ihb (d + 1) (by omega)]
  | forallE ty b iht ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    rw [Expr.instantiateList, iht d h.1, ihb (d + 1) (by omega)]
  | letE ty w b iht ihw ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    rw [Expr.instantiateList, iht d h.1.1, ihw d h.1.2, ihb (d + 1) (by omega)]
  | proj n i e ih =>
    intro d h
    simp only [Expr.bvarBound] at h
    rw [Expr.instantiateList, ih d h]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:386-400 liftLooseBVars — **the
second derived cutoff's licence**: a term with no loose `bvar` at or above the
cutoff is its own lift. -/
theorem liftLooseBVars_of_bvarBound_le {amount : Nat} :
    ∀ (e : Expr) (c : Nat), e.bvarBound ≤ c →
      Expr.liftLooseBVars amount c e = e := by
  intro e
  induction e with
  | bvar i =>
    intro c h
    simp only [Expr.bvarBound] at h
    simp [Expr.liftLooseBVars, show ¬ (i ≥ c) from by omega]
  | fvar _ _ _ | sort _ | const _ _ | lit _ =>
    intro c _; simp [Expr.liftLooseBVars]
  | app f a ihf iha =>
    intro c h
    simp only [Expr.bvarBound, Nat.max_le] at h
    rw [Expr.liftLooseBVars, ihf c h.1, iha c h.2]
  | lam ty b iht ihb =>
    intro c h
    simp only [Expr.bvarBound, Nat.max_le] at h
    rw [Expr.liftLooseBVars, iht c h.1, ihb (c + 1) (by omega)]
  | forallE ty b iht ihb =>
    intro c h
    simp only [Expr.bvarBound, Nat.max_le] at h
    rw [Expr.liftLooseBVars, iht c h.1, ihb (c + 1) (by omega)]
  | letE ty w b iht ihw ihb =>
    intro c h
    simp only [Expr.bvarBound, Nat.max_le] at h
    rw [Expr.liftLooseBVars, iht c h.1.1, ihw c h.1.2, ihb (c + 1) (by omega)]
  | proj n i e ih =>
    intro c h
    simp only [Expr.bvarBound] at h
    rw [Expr.liftLooseBVars, ih c h]

/-! ## F. The four answer relations -/

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — `instantiateList`'s answer
relation, at the pure walk's own list `ws` (the REVERSE of what the twin's
vector denotes — see `InstLVec`). -/
abbrev InstLAt (ws : List Expr) (d : Nat) : EStore → EIdx → EStore → EIdx → Prop :=
  RelE (fun e => e.instantiateList ws d)

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — `liftLooseBVars`' answer
relation. -/
abbrev LiftAt (amount c : Nat) : EStore → EIdx → EStore → EIdx → Prop :=
  RelE (Expr.liftLooseBVars amount c)

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — `instantiate1Lift`'s
answer relation. -/
abbrev Inst1LAt (ve : Expr) (d : Nat) : EStore → EIdx → EStore → EIdx → Prop :=
  RelE (fun e => e.instantiate1Lift ve d)

/-! ## G. The derived word's bound

The two derived cutoffs and `bvarB`'s packed branch read the derived word's
bound field; below the saturation it IS the denotation's `bvarBound`, as one
fact per handle whose word the program reads.  (The general vocabulary these
walks need — the answer relations as `MapRel`, the views and tags, the memo
invariant's uses — is `Bridge/Grind.lean`'s.) -/

/-- con-leche: none — the derived word's bound field, at a denoting handle:
below the saturation it IS the denotation's `bvarBound` (`bvarBRaw_exact` at
`EStore.derived_exact`).  The two derived cutoffs and `bvarB`'s packed branch
read exactly this. -/
def DerivedBound (st : EStore) (h : EIdx) : Option Expr → Prop
  | some e => (bvarOfData (st.derived h)).toNat < satRange →
      e.bvarBound = (bvarOfData (st.derived h)).toNat
  | none => True

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1485 bvarBRaw_exact — the
derived word's bound at every handle whose word the program reads. -/
theorem derivedBound {st : EStore} (hwf : StoreWF st) (h : EIdx) :
    DerivedBound st h (denoteE st h) := by
  cases he : denoteE st h with
  | none => trivial
  | some e =>
    intro hs
    rw [EStore.derived_exact hwf he] at hs ⊢
    exact (Expr.bvarBRaw_exact e hs).symm
grind_pattern [bridge_grind] derivedBound => bvarOfData (st.derived h), denoteE st h

/-- con-leche: none — `DerivedBound` at a denoting handle. -/
theorem DerivedBound.some {st : EStore} {h : EIdx} {e : Expr} (H : DerivedBound st h (some e)) :
    (bvarOfData (st.derived h)).toNat < satRange →
      e.bvarBound = (bvarOfData (st.derived h)).toNat := H
grind_pattern [bridge_grind] DerivedBound.some => DerivedBound st h (some e)

/-! ## H. This file's own vocabulary

The pure functions as `grind` reads them — the cutoffs' licences keyed by the
`bvarBound` term the cutoff created (so they fire at the cutoff's subject and
nowhere else: `Inst1.lean`'s finding that a loose licence spirals on the pure
function's own iterate), `instantiateList`'s `.bvar` clause and catch-all as
equations without a dependent `if`, `instPisAtLift`'s cons clause over the tag —
and the push-order vector's three facts. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:211-235 instantiateList — the
first derived cutoff's licence, keyed by the cut subject's bound. -/
theorem instantiateList_of_bvarBound_le' {ws : List Expr} {e : Expr} {d : Nat}
    (h : e.bvarBound ≤ d) : e.instantiateList ws d = e :=
  instantiateList_of_bvarBound_le e d h
grind_pattern [bridge_grind] instantiateList_of_bvarBound_le' =>
  Expr.bvarBound e, Expr.instantiateList e ws d

/-- con-leche: ConLeche/Kernel/ExprOps.lean:386-400 liftLooseBVars — the second
derived cutoff's licence, keyed likewise. -/
theorem liftLooseBVars_of_bvarBound_le' {amount : Nat} {e : Expr} {c : Nat}
    (h : e.bvarBound ≤ c) : Expr.liftLooseBVars amount c e = e :=
  liftLooseBVars_of_bvarBound_le e c h
grind_pattern [bridge_grind] liftLooseBVars_of_bvarBound_le' =>
  Expr.bvarBound e, Expr.liftLooseBVars amount c e

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2169 instantiate1Lift_of_bvarBound_le
— `instantiate1LiftGo`'s cutoff, con-leche's own, keyed likewise. -/
theorem instantiate1Lift_of_bvarBound_le' {e ve : Expr} {d : Nat}
    (h : e.bvarBound ≤ d) : e.instantiate1Lift ve d = e :=
  Expr.instantiate1Lift_of_bvarBound_le e ve d h
grind_pattern [bridge_grind] instantiate1Lift_of_bvarBound_le' =>
  Expr.bvarBound e, Expr.instantiate1Lift e ve d

/-- con-leche: ConLeche/Kernel/ExprOps.lean:207-211 instantiateList — the
`.bvar` clause as ONE equation, the replacement read with `getD` rather than
a dependent index. -/
theorem instantiateList_bvar_eq (ws : List Expr) (j d : Nat) :
    Expr.instantiateList (.bvar j) ws d =
      if j < d then .bvar j
      else if j - d < ws.length then
        Expr.instantiateList (ws.getD (j - d) (.bvar 0)) (ws.take (j - d)) d
      else .bvar (j - ws.length) := by
  rw [Expr.instantiateList]
  split
  · rfl
  · split
    · rename_i h; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl
    · rfl

/-- con-leche: ConLeche/Kernel/ExprOps.lean:212-223 instantiateList — the
CATCH-ALL arm: at none of the six tags the walk dispatches on, the function
is the identity. -/
theorem instantiateList_leaf {ws : List Expr} {d : Nat} {e : Expr}
    (h1 : exprTag e ≠ ETag.app) (h2 : exprTag e ≠ ETag.lam) (h3 : exprTag e ≠ ETag.forallE)
    (h4 : exprTag e ≠ ETag.letE) (h5 : exprTag e ≠ ETag.proj) (h6 : exprTag e ≠ ETag.bvar) :
    e.instantiateList ws d = e := by
  cases e <;> simp_all [exprTag, Expr.instantiateList]
grind_pattern [bridge_grind] instantiateList_leaf => exprTag e, Expr.instantiateList e ws d

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2178-2181 instPisAtLift — the cons
clause as ONE equation over the tag and the body projection. -/
theorem instPisAtLift_cons_eq (a : Expr) (as : List Expr) (e : Expr) :
    Expr.instPisAtLift (a :: as) e =
      if exprTag e = ETag.forallE then Expr.instPisAtLift as ((exprBody e).instantiate1Lift a)
      else none := by
  cases e <;> simp [Expr.instPisAtLift, exprTag, exprBody, ETag.forallE, ETag.bvar, ETag.fvar,
    ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.letE, ETag.lit, ETag.proj]

/-- con-leche: none — `InstLVec.ext` along the store order. -/
theorem InstLVec.le {st st' : EStore} {vs : Array EIdx} {ws : List Expr} (hx : st ≤ st')
    (h : InstLVec st vs ws) : InstLVec st' vs ws := h.ext hx
grind_pattern [bridge_grind] InstLVec.le => st ≤ st', InstLVec st vs ws

/-- con-leche: none — `InstLVec.length` as the vector's fact. -/
theorem InstLVec.length_eq {st : EStore} {vs : Array EIdx} {ws : List Expr}
    (h : InstLVec st vs ws) : ws.length = vs.size := h.length
grind_pattern [bridge_grind] InstLVec.length_eq => InstLVec st vs ws

grind_pattern [bridge_grind] InstLVec.last => InstLVec st vs ws, lastEidx vs m

/-- con-leche: ConLeche/Kernel/ExprOps.lean:227 instantiateList (the `.bvar`
arm's `vs[j - d]`) — `InstLVec.get` at the twin's own dependent array read, as
an equation. -/
theorem InstLVec.getElem_eq {st : EStore} {vs : Array EIdx} {ws : List Expr} {m : Nat}
    (h : InstLVec st vs ws) (hm : m < vs.size) (hi : vs.size - 1 - m < vs.size) :
    denoteE st vs[vs.size - 1 - m] = some (ws.getD m (.bvar 0)) := by
  obtain ⟨w, hw, hd⟩ := h.get hm (Array.getElem?_eq_getElem hi)
  rw [hd, List.getD_eq_getElem?_getD, hw]; rfl
grind_pattern [bridge_grind] InstLVec.getElem_eq =>
  InstLVec st vs ws, GetElem.getElem vs (vs.size - 1 - m) hi

/-! ## I. `bvarB`'s Theorem 1, as the two con-leche cutoffs consume it

`instantiate1LiftGo` tests con-leche's own `bvarB` — the
packed field, or the memoized recomputation on the saturated branch
(`Arena/ExprOps.lean:1486`).  **`bvarB` is not one of this file's thirteen
twins**: it belongs to the packed-range group.  Round 3 carried its Theorem 1
as a HYPOTHESIS so that `#print axioms` stayed clean while that group's file
was open; round 4 **discharged** it from `ExprOps/Ranges.lean`'s `bvarB_spec`
(`bvarB_bvarBSpec` below) and deleted the binders. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1429-1434 bvarB — Theorem 1 for
`bvarB`, in the shape the two cutoff walks need: the answer is
`Expr.bvarBound`, the store stands still, and the walk's own memo table is
untouched (`bvarBoundMemo` clears only `bvarBC`). -/
structure BvarBSpec (prog : EIdx → AM Nat) : Prop where
  run : ∀ (s₁ : AState) (c : EIdx), StateOK s₁ →
    (denoteE s₁.store c).isSome = true →
    ⦃fun s => s = s₁⦄ prog c
    ⦃fun r s' => StateOK s' ∧ StoreWF s'.store ∧ s'.store = s₁.store ∧
        s'.caches = s₁.caches ∧
        s'.pins = s₁.pins ∧
        s'.memos.inst1LC = s₁.memos.inst1LC ∧
        RelV Expr.bvarBound s₁.store c r; ⊤⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1429-1434 bvarB — **`BvarBSpec`,
discharged**, from `ExprOps/Ranges.lean`'s `bvarB_spec`: its five conjuncts
are `bvarB_spec`'s (the memo-frame one, `inst1LC`, was round 4's gap), and
`StateOK s'`/`StoreWF s'.store` are `hok` along `s'.store = s₁.store`. -/
theorem bvarB_bvarBSpec (fuel : Nat) : BvarBSpec (bvarB fuel) := by
  constructor
  intro s₁ c hok hden
  sym only [bridge_grind] => vcgen [bvarB_spec fuel] <;> finish

/-! ## J. Theorem 1 for `liftLooseBVars` -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:411-413 LiftMemoInv — **the memo
insert's spec, generic in the pure function**.

`Bridge/Specs.lean`'s `liftSet_spec` takes `amount : Nat` as an ordinary
parameter, and `amount` appears nowhere in the program `liftSet k r`: under
`mvcgen` the leftover argument was filled in by a context search (the
cutoff's own `bRaw` inside `liftLooseBVarsGo`'s arms — false side goals), and
under `vcgen` (task #111) it is simply left open.  So the pure function is the
parameter and each walk passes this spec INSTANTIATED in its `vcgen` list —
`liftSet_specG (f := fun c e => Expr.liftLooseBVars amount c e)`.
`@[spec high]`: a spec registered later does not override an earlier one for
the same program.  `dsimp only` first: the postcondition's record update
elaborates to `let __src := s0.memos; …`, which `vcgen` rejects (reproducer
`_tmp/corpus/vcgen-grind/vcgen-let-src-in-spec.lean`). -/
@[spec high] theorem liftSet_specG (s0 : AState) (f : Nat -> Expr -> Expr)
    (k : EIdx × Nat) (r : EIdx) (hm : MemoOK f s0.memos.liftC s0.store)
    (hk : (denoteE s0.store k.1).isSome = true)
    (hr : RelE (f k.2) s0.store k.1 s0.store r) :
    ⦃fun s => s = s0⦄ liftSet k r
    ⦃fun _u s' => s'.store = s0.store ∧ s'.caches = s0.caches ∧
        s'.pins = s0.pins ∧
        s'.memos = { s0.memos with liftC := s0.memos.liftC.insert k r } ∧
        MemoOK f s'.memos.liftC s'.store; ⊤⦄ := by
  dsimp only
  sym only [bridge_grind] => vcgen [liftSet] <;> finish

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `liftLooseBVarsGo`'s recursion.

The **one extra frame conjunct** over `Inst1.lean`'s shape is
`s'.memos.inst1LC = s₁.memos.inst1LC`: `instantiate1LiftGo`'s `.bvar` arm runs
`liftLooseBVarsFast` as a NESTED walk and has to carry `Inst1LMemoA ve` across
it, so this tier's one nested walk is exactly where `Inst1.lean`'s "the twelve
other per-call memo tables are NOT framed here" has to be paid. -/
structure LiftSpec (amount : Nat) (rec : EIdx → Nat → AM EIdx) : Prop where
  run : ∀ (s₁ : AState) (c : EIdx) (cc : Nat), StateOK s₁ → LiftMemoA amount s₁ →
    (denoteE s₁.store c).isSome = true →
    ⦃fun s => s = s₁⦄ rec c cc
    ⦃fun r s' => StateOK s' ∧ LiftMemoA amount s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        s'.memos.inst1LC = s₁.memos.inst1LC ∧
        LiftAt amount cc s₁.store c s'.store r; ⊤⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:380-400 liftLooseBVars
con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo
**THEOREM 1 for `liftLooseBVars`**, at one level of the recursion, by
induction on the fuel.

DEVIATION (task #97f): the twin carries the derived-word cutoff `bvarBRaw <
satRange && bvarBRaw ≤ c`, which con-leche's `liftLooseBVarsGo` does not have.
Its licence is `liftLooseBVars_of_bvarBound_le` above — the `ExprOps.lean`
module note's `looseBVarsBounded c e → liftLooseBVars e c amount = e`, proved
by induction on `Expr` at `Expr.bvarBRaw_exact`'s guard (`DerivedBound`).
Everything else is clause for clause.

The walk dispatches on the whole `view`, so its ten arms arrive with the node
view in hand: the leaves by their tag (`ENodeView.tagOf`) and `exprTag_*`,
the `bvar` arm by `liftLooseBVars`' own `if`, the five rebuilding arms by the
memo lemmas and the children's answers. -/
theorem liftLooseBVarsGo_spec (amount : Nat) :
    ∀ fuel, LiftSpec amount (liftLooseBVarsGo amount fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h c _ _ _
    sym only [bridge_grind] => vcgen [liftLooseBVarsGo_zero] <;> finish
  | succ fuel ih =>
    constructor
    intro s₀ h c hok hm hden
    sym only [bridge_grind, Expr.liftLooseBVars, ENodeView.tagOf] =>
      vcgen [liftLooseBVarsGo_succ, liftArmApp, liftArmLam, liftArmForallE,
        liftArmLet, liftArmProj, ih.run,
        liftSet_specG (f := fun c e => Expr.liftLooseBVars amount c e)] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:532-534 liftLooseBVarsFast —
**THEOREM 1 for `liftLooseBVars`, at the entry point**: clear, walk, clear. -/
theorem liftLooseBVarsFast_spec (fuel amount c : Nat) (s₀ : AState) (e : EIdx)
    (hok : StateOK s₀) (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => s = s₀⦄ liftLooseBVarsFast fuel amount c e
    ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.memos.liftC = ∅ ∧ s'.memos.inst1LC = s₀.memos.inst1LC ∧
        LiftAt amount c s₀.store e s'.store r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [liftLooseBVarsFast, (liftLooseBVarsGo_spec amount fuel).run] <;> finish

/-! ## K. Theorem 1 for `lowerBVars`, `instantiate1Lift` and `instPisAtLift` -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2205-2207 Inst1LMemoInv — the memo
insert's spec for `inst1LC`, generic in the pure function (see
`liftSet_specG`). -/
@[spec high] theorem inst1LSet_specG (s₀ : AState) (f : Nat → Expr → Expr)
    (k : EIdx × Nat) (r : EIdx) (hm : MemoOK f s₀.memos.inst1LC s₀.store)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelE (f k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => s = s₀⦄ inst1LSet k r
    ⦃fun _u s' => s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with inst1LC := s₀.memos.inst1LC.insert k r } ∧
        MemoOK f s'.memos.inst1LC s'.store; ⊤⦄ := by
  dsimp only
  sym only [bridge_grind] => vcgen [inst1LSet] <;> finish

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `instantiate1LiftGo`'s recursion. -/
structure Inst1LSpec (v : EIdx) (ve : Expr) (rec : EIdx → Nat → AM EIdx) :
    Prop where
  run : ∀ (s₁ : AState) (c : EIdx) (dd : Nat), StateOK s₁ →
    Inst1LMemoA ve s₁ → denoteE s₁.store v = some ve →
    (denoteE s₁.store c).isSome = true →
    ⦃fun s => s = s₁⦄ rec c dd
    ⦃fun r s' => StateOK s' ∧ Inst1LMemoA ve s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1LAt ve dd s₁.store c s'.store r; ⊤⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:718-739 instantiate1Lift
con-leche: ConLeche/Kernel/ExprOps.lean:2224-2263 instantiate1LiftGo
**THEOREM 1 for `instantiate1Lift`**, at one level of the recursion.

Two things make this the most interesting walk of the group:

1. the cutoff is again **con-leche's own** (`bvarB ≤ d`), quoted from
   `Expr.instantiate1Lift_of_bvarBound_le` (`ExprOps.lean:2169`) through
   `bvarB`'s answer (`RelV`, read as `MapRelV`);
2. it is the module's one **nested** walk: the `.bvar` arm at `i = d` answers
   `liftLooseBVarsFast fuel d 0 v`, so the proof consumes
   `liftLooseBVarsFast_spec` and needs its `inst1LC` frame conjunct to carry
   `Inst1LMemoA ve` across the nested call.

`bvarB` moves the STATE (it clears its own memo) and leaves the STORE alone,
so every arm proves its answer at a store equal to the one its statement
names: congruence closure, where the old closer needed two casts. -/
theorem instantiate1LiftGo_spec (v : EIdx) (ve : Expr) :
    ∀ fuel, Inst1LSpec v ve (instantiate1LiftGo v fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h d _ _ _ _
    sym only [bridge_grind] => vcgen [instantiate1LiftGo_zero] <;> finish
  | succ fuel ih =>
    constructor
    intro s₀ h d hok hm hv hden
    sym only [bridge_grind, Expr.instantiate1Lift, ENodeView.tagOf] =>
      vcgen [instantiate1LiftGo_succ, inst1LiftArmApp, inst1LiftArmLam,
        inst1LiftArmForallE, inst1LiftArmLet, inst1LiftArmProj, ih.run,
        (bvarB_bvarBSpec fuel).run,
        fun (s : AState) (e : EIdx) => liftLooseBVarsFast_spec fuel d 0 s e,
        inst1LSet_specG (f := fun dd e => Expr.instantiate1Lift e ve dd)] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2358-2360 instantiate1LiftFast —
**THEOREM 1 for `instantiate1Lift`, at the entry point**. -/
theorem instantiate1LiftFast_spec (fuel : Nat) (s₀ : AState) (e v : EIdx)
    (d : Nat) (ve : Expr) (hok : StateOK s₀)
    (hv : denoteE s₀.store v = some ve)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => s = s₀⦄ instantiate1LiftFast fuel e v d
    ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.memos.inst1LC = ∅ ∧ Inst1LAt ve d s₀.store e s'.store r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [instantiate1LiftFast, (instantiate1LiftGo_spec v ve fuel).run] <;> finish

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the same statement about
a RUN. -/
theorem instantiate1LiftFast_run {fuel : Nat} {s₀ s' : AState} {e v r : EIdx}
    {d : Nat} {ve : Expr} (hok : StateOK s₀)
    (hv : denoteE s₀.store v = some ve)
    (hden : (denoteE s₀.store e).isSome = true)
    (hrun : (instantiate1LiftFast fuel e v d).run s₀ = Except.ok (r, s')) :
    StateOK s' ∧ Ext s₀.store s'.store ∧
      s'.caches = s₀.caches ∧
      s'.pins = s₀.pins ∧ s'.memos.inst1LC = ∅ ∧
      Inst1LAt ve d s₀.store e s'.store r :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    (instantiate1LiftFast_spec fuel s₀ e v d ve hok hv hden)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2367-2380 instPisAtLift —
`instPisAtLift_spec` at a GIVEN denotation of the argument list (the
list is the induction's own parameter and its head and tail are split off
before `sym`, so that `vcgen`'s list takes the induction hypothesis at the
tail's denotation; the answer at the named function `Expr.instPisAtLift xs`,
no `fun`). -/
theorem instPisAtLift_specA (fuel : Nat) :
    ∀ (args : List EIdx) (xs : List Expr) (s₀ : AState) (c : EIdx), StateOK s₀ →
      Frontend.denoteEList s₀.store args = some xs →
      (denoteE s₀.store c).isSome = true →
      ⦃fun s => s = s₀⦄ instPisAtLift fuel args c
      ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧
          s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
          RelEO (Expr.instPisAtLift xs) s₀.store c s'.store r; ⊤⦄ := by
  intro args
  induction args with
  | nil =>
    intro xs s₀ c hok hxs hden
    sym only [bridge_grind, Frontend.denoteEList, Expr.instPisAtLift] =>
      vcgen [instPisAtLift] <;> finish
  | cons a as ih =>
    intro xs s₀ c hok hxs hden
    obtain ⟨ea, eas, ha, has, rfl⟩ := denoteEList_cons_inv hxs
    sym only [bridge_grind, instPisAtLift_cons_eq] =>
      vcgen [instPisAtLift, ih eas,
        fun (s : AState) (e : EIdx) => instantiate1LiftFast_spec fuel s e a 0 ea] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2367-2380 instPisAtLift —
**THEOREM 1 for `instPisAtLift`**: instantiate the leading `∀`-binders at
*open* arguments.  The answer is an OPTION of a handle, so the relation is
`Bridge/Rel.lean`'s `RelEO` (`none` is `none`: a non-`∀` head is a failure of
the pure function too, not of the monad).

The recursion is on the argument LIST, not on fuel, so there is no fuel
induction; the fuel is `instantiate1LiftFast`'s.  The argument list's
denotation sits in the POSTCONDITION (`∀ xs, denoteEList … = some xs → …`)
rather than as a parameter, for the callers' sake (a `List Expr` parameter the
program does not mention is left open by `vcgen`); `instPisAtLift_specA` is
the same at a given denotation. -/
theorem instPisAtLift_spec (fuel : Nat) :
    ∀ (args : List EIdx) (s₀ : AState) (c : EIdx), StateOK s₀ →
      (Frontend.denoteEList s₀.store args).isSome = true →
      (denoteE s₀.store c).isSome = true →
      ⦃fun s => s = s₀⦄ instPisAtLift fuel args c
      ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧
          s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
          ∀ xs, Frontend.denoteEList s₀.store args = some xs →
            RelEO (fun e => Expr.instPisAtLift xs e) s₀.store c s'.store r; ⊤⦄ := by
  intro args s₀ c hok hargs hden
  obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp hargs
  refine ⟨Triple.entails_wp_of_post (instPisAtLift_specA fuel args xs s₀ c hok hxs hden) ?_⟩
  rintro r s' ⟨h1, h2, h3, h4, h5⟩
  refine ⟨h1, h2, h3, h4, fun xs' hxs' => ?_⟩
  rw [hxs] at hxs'
  obtain rfl := Option.some.inj hxs'
  exact h5

/-! ## L. Theorem 1 for `instantiateList` -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:248-250 InstLMemoInv — the memo
insert's spec for `instLC`, generic in the pure function (see
`liftSet_specG`). -/
@[spec high] theorem instLSet_specG (s₀ : AState) (f : Nat → Expr → Expr)
    (k : EIdx × Nat) (r : EIdx) (hm : MemoOK f s₀.memos.instLC s₀.store)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelE (f k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => s = s₀⦄ instLSet k r
    ⦃fun _u s' => s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with instLC := s₀.memos.instLC.insert k r } ∧
        MemoOK f s'.memos.instLC s'.store; ⊤⦄ := by
  dsimp only
  sym only [bridge_grind] => vcgen [instLSet] <;> finish

/-! ### `instantiateList`, the unmemoized walk -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of the UNMEMOIZED `instantiateList`'s recursion.

Two departures from `Inst1.lean`'s `Inst1Spec`, both forced by this walk:

* the substitution VECTOR and the list it denotes are both parameters, tied
  by `InstLVec` (task #97-P6-15's push-order reversal).  The `.bvar` arm
  recurses at a SHORTER list, so it does not take this record as its
  induction hypothesis but the whole family `∀ m, InstLPureSpec (lastEidx vs
  m) (ws.take m) …` — which is why the fuel induction generalises over the
  vector;
* `s'.memos = s₁.memos` rather than a memo invariant: this walk is the
  unmemoized one and touches no table at all, and `instantiateListGo`'s
  `.bvar` branch needs exactly that frame to carry `InstLMemoA ws` across it.
 -/
structure InstLPureSpec (vs : Array EIdx) (ws : List Expr)
    (rec : EIdx → Nat → AM EIdx) : Prop where
  run : ∀ (s₁ : AState) (c : EIdx) (dd : Nat), StateOK s₁ →
    InstLVec s₁.store vs ws → (denoteE s₁.store c).isSome = true →
    ⦃fun s => s = s₁⦄ rec c dd
    ⦃fun r s' => StateOK s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧ s'.memos = s₁.memos ∧
        InstLAt ws dd s₁.store c s'.store r; ⊤⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList — the
`app` ARM: project, recurse into both children, rebuild. -/
theorem instListArmApp_spec (vs : Array EIdx) (ws : List Expr) (fuel : Nat)
    (ih : InstLPureSpec vs ws (instantiateList vs fuel)) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hvec : InstLVec s₁.store vs ws)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.app) = true) :
    ⦃fun s => s = s₁⦄ instListArmApp vs fuel c dd
    ⦃fun r s' => StateOK s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧ s'.memos = s₁.memos ∧
        InstLAt ws dd s₁.store c s'.store r; ⊤⦄ := by
  sym only [bridge_grind, Expr.instantiateList] =>
    vcgen [instListArmApp, ih.run] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList — the
BINDER ARM (`lam` and `forallE` in one, as the tag dispatch tests them). -/
theorem instListArmBind_spec (vs : Array EIdx) (ws : List Expr) (fuel : Nat)
    (ih : InstLPureSpec vs ws (instantiateList vs fuel)) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hvec : InstLVec s₁.store vs ws)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : ETag.isBind c.tag = true) :
    ⦃fun s => s = s₁⦄ instListArmBind vs fuel c dd
    ⦃fun r s' => StateOK s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧ s'.memos = s₁.memos ∧
        InstLAt ws dd s₁.store c s'.store r; ⊤⦄ := by
  sym only [bridge_grind, Expr.instantiateList] =>
    vcgen [instListArmBind, ih.run] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList — the
`letE` ARM; the body descends at `dd + 1`. -/
theorem instListArmLet_spec (vs : Array EIdx) (ws : List Expr) (fuel : Nat)
    (ih : InstLPureSpec vs ws (instantiateList vs fuel)) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hvec : InstLVec s₁.store vs ws)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.letE) = true) :
    ⦃fun s => s = s₁⦄ instListArmLet vs fuel c dd
    ⦃fun r s' => StateOK s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧ s'.memos = s₁.memos ∧
        InstLAt ws dd s₁.store c s'.store r; ⊤⦄ := by
  sym only [bridge_grind, Expr.instantiateList] =>
    vcgen [instListArmLet, ih.run] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList — the
`proj` ARM.  The struct NAME is carried unchanged, and its denotation comes
from `denote_eq_proj`'s existential, which `grind` cannot see through. -/
theorem instListArmProj_spec (vs : Array EIdx) (ws : List Expr) (fuel : Nat)
    (ih : InstLPureSpec vs ws (instantiateList vs fuel)) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hvec : InstLVec s₁.store vs ws)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.proj) = true) :
    ⦃fun s => s = s₁⦄ instListArmProj vs fuel c dd
    ⦃fun r s' => StateOK s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧ s'.memos = s₁.memos ∧
        InstLAt ws dd s₁.store c s'.store r; ⊤⦄ := by
  sym only [bridge_grind, Expr.instantiateList] =>
    vcgen [instListArmProj, ih.run] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:211-235 instantiateList — the
`bvar` ARM, the one arm of this walk that is not a congruence: it recurses
into the REPLACEMENT with the SHORTER vector `lastEidx vs (j - d)`, which is
why its induction hypothesis is the whole family `ih m` rather than one
record.  `InstLVec.get` is the indexed read through the push-order reversal
and `InstLVec.last` the shortened vector's denotation. -/
theorem instListArmBVar_spec (vs : Array EIdx) (ws : List Expr) (fuel : Nat)
    (ih : ∀ m, InstLPureSpec (lastEidx vs m) (ws.take m)
      (instantiateList (lastEidx vs m) fuel))
    (s₁ : AState) (c : EIdx) (dd : Nat) (hok : StateOK s₁)
    (hvec : InstLVec s₁.store vs ws)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.bvar) = true) :
    ⦃fun s => s = s₁⦄ instListArmBVar vs fuel c dd
    ⦃fun r s' => StateOK s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧ s'.memos = s₁.memos ∧
        InstLAt ws dd s₁.store c s'.store r; ⊤⦄ := by
  sym only [bridge_grind, instantiateList_bvar_eq] =>
    vcgen [instListArmBVar, fun m => (ih m).run] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList —
**THEOREM 1 for the unmemoized bulk instantiation**, by induction on the fuel,
generalised over the vector (which the `.bvar` arm shortens).

DEVIATION (task #97f): the derived-word cutoff `bvarBRaw < satRange &&
bvarBRaw ≤ d`, which con-leche does not have; licensed by
`instantiateList_of_bvarBound_le` above.  It appears TWICE — once at the node
and once, hoisted over the prefix copy (task #97-P6-9), at the replacement —
and `InstLAt.cutoff` / `InstLAt.bvar_cut` are the two licences.

DEVIATION (task #97-P6-15): the substitution vector is an `Array EIdx` in PUSH
order, so con-leche's `vs[j - d]` is the array's entry `j - d` FROM THE END and
the array's denotation is the REVERSE of con-leche's list.  `InstLVec` is that
orientation, written down once; `InstLVec.get` and `InstLVec.last` are the two
facts the `.bvar` arm consumes. -/
theorem instantiateList_spec :
    ∀ (fuel : Nat) (vs : Array EIdx) (ws : List Expr),
      InstLPureSpec vs ws (instantiateList vs fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    intro vs ws
    constructor
    intro s₀ h d _ _ _
    sym only [bridge_grind] => vcgen [instantiateList_zero] <;> finish
  | succ fuel ih =>
    intro vs ws
    constructor
    intro s₀ h d hok hvec hden
    sym only [bridge_grind] =>
      vcgen [instantiateList_succ, instListArmApp_spec vs ws fuel (ih vs ws),
        instListArmBind_spec vs ws fuel (ih vs ws), instListArmLet_spec vs ws fuel (ih vs ws),
        instListArmProj_spec vs ws fuel (ih vs ws),
        instListArmBVar_spec vs ws fuel (fun m => ih (lastEidx vs m) (ws.take m))] <;> finish

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of the MEMOIZED `instantiateListGo`'s recursion.  The memo table is
keyed for ONE substitution list (`InstLMemoA ws`) and this walk never shortens
it — the shortening `.bvar` arm is the unmemoized walk, called by name — so
the record carries the invariant where the pure walk carries a memo frame. -/
structure InstLSpec (vs : Array EIdx) (ws : List Expr)
    (rec : EIdx → Nat → AM EIdx) : Prop where
  run : ∀ (s₁ : AState) (c : EIdx) (dd : Nat), StateOK s₁ → InstLMemoA ws s₁ →
    InstLVec s₁.store vs ws → (denoteE s₁.store c).isSome = true →
    ⦃fun s => s = s₁⦄ rec c dd
    ⦃fun r s' => StateOK s' ∧ InstLMemoA ws s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        InstLAt ws dd s₁.store c s'.store r; ⊤⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
`app` ARM: probe, project, recurse into both children, rebuild, insert. -/
theorem instListGoArmApp_spec (vs : Array EIdx) (ws : List Expr) (fuel : Nat)
    (ih : InstLSpec vs ws (instantiateListGo vs fuel)) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hm : InstLMemoA ws s₁)
    (hvec : InstLVec s₁.store vs ws)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.app) = true) :
    ⦃fun s => s = s₁⦄ instListGoArmApp vs fuel c dd
    ⦃fun r s' => StateOK s' ∧ InstLMemoA ws s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        InstLAt ws dd s₁.store c s'.store r; ⊤⦄ := by
  sym only [bridge_grind, Expr.instantiateList] =>
    vcgen [instListGoArmApp, ih.run,
      instLSet_specG (f := fun dd e => Expr.instantiateList e ws dd)] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
BINDER ARM. -/
theorem instListGoArmBind_spec (vs : Array EIdx) (ws : List Expr) (fuel : Nat)
    (ih : InstLSpec vs ws (instantiateListGo vs fuel)) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hm : InstLMemoA ws s₁)
    (hvec : InstLVec s₁.store vs ws)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : ETag.isBind c.tag = true) :
    ⦃fun s => s = s₁⦄ instListGoArmBind vs fuel c dd
    ⦃fun r s' => StateOK s' ∧ InstLMemoA ws s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        InstLAt ws dd s₁.store c s'.store r; ⊤⦄ := by
  sym only [bridge_grind, Expr.instantiateList] =>
    vcgen [instListGoArmBind, ih.run,
      instLSet_specG (f := fun dd e => Expr.instantiateList e ws dd)] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
`letE` ARM; the body descends at `dd + 1`. -/
theorem instListGoArmLet_spec (vs : Array EIdx) (ws : List Expr) (fuel : Nat)
    (ih : InstLSpec vs ws (instantiateListGo vs fuel)) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hm : InstLMemoA ws s₁)
    (hvec : InstLVec s₁.store vs ws)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.letE) = true) :
    ⦃fun s => s = s₁⦄ instListGoArmLet vs fuel c dd
    ⦃fun r s' => StateOK s' ∧ InstLMemoA ws s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        InstLAt ws dd s₁.store c s'.store r; ⊤⦄ := by
  sym only [bridge_grind, Expr.instantiateList] =>
    vcgen [instListGoArmLet, ih.run,
      instLSet_specG (f := fun dd e => Expr.instantiateList e ws dd)] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
`proj` ARM.  The struct NAME is carried unchanged, and its denotation comes
from `denote_eq_proj`'s existential, which `grind` cannot see through. -/
theorem instListGoArmProj_spec (vs : Array EIdx) (ws : List Expr) (fuel : Nat)
    (ih : InstLSpec vs ws (instantiateListGo vs fuel)) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hm : InstLMemoA ws s₁)
    (hvec : InstLVec s₁.store vs ws)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.proj) = true) :
    ⦃fun s => s = s₁⦄ instListGoArmProj vs fuel c dd
    ⦃fun r s' => StateOK s' ∧ InstLMemoA ws s' ∧ Ext s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        InstLAt ws dd s₁.store c s'.store r; ⊤⦄ := by
  sym only [bridge_grind, Expr.instantiateList] =>
    vcgen [instListGoArmProj, ih.run,
      instLSet_specG (f := fun dd e => Expr.instantiateList e ws dd)] <;> finish

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo —
**THEOREM 1 for the memoized bulk instantiation**.  Its `.bvar` arm delegates
to the unmemoized walk above, exactly as con-leche's does, so the proof
consumes `instantiateList_spec` at the same fuel.  Same two deviations as the
unmemoized walk, same two licences. -/
theorem instantiateListGo_spec (vs : Array EIdx) (ws : List Expr) :
    ∀ fuel, InstLSpec vs ws (instantiateListGo vs fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h d _ _ _ _
    sym only [bridge_grind] => vcgen [instantiateListGo_zero] <;> finish
  | succ fuel ih =>
    constructor
    intro s₀ h d hok hm hvec hden
    sym only [bridge_grind] =>
      vcgen [instantiateListGo_succ, instListGoArmApp_spec vs ws fuel ih,
        instListGoArmBind_spec vs ws fuel ih, instListGoArmLet_spec vs ws fuel ih,
        instListGoArmProj_spec vs ws fuel ih, (instantiateList_spec fuel vs ws).run] <;> finish


/-- con-leche: ConLeche/Kernel/ExprOps.lean:371-373 instantiateListFast —
**THEOREM 1 for `instantiateList`, at the entry point**. -/
theorem instantiateListFast_spec (fuel : Nat) (s₀ : AState) (e : EIdx)
    (vs : Array EIdx) (d : Nat) (ws : List Expr) (hok : StateOK s₀)
    (hvec : InstLVec s₀.store vs ws)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => s = s₀⦄ instantiateListFast fuel e vs d
    ⦃fun r s' => StateOK s' ∧ Ext s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.memos.instLC = ∅ ∧ InstLAt ws d s₀.store e s'.store r; ⊤⦄ := by
  sym only [bridge_grind] =>
    vcgen [instantiateListFast, (instantiateListGo_spec vs ws fuel).run] <;> finish

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the same statement about
a RUN. -/
theorem instantiateListFast_run {fuel : Nat} {s₀ s' : AState} {e r : EIdx}
    {vs : Array EIdx} {d : Nat} {ws : List Expr} (hok : StateOK s₀)
    (hvec : InstLVec s₀.store vs ws)
    (hden : (denoteE s₀.store e).isSome = true)
    (hrun : (instantiateListFast fuel e vs d).run s₀ = Except.ok (r, s')) :
    StateOK s' ∧ Ext s₀.store s'.store ∧
      s'.caches = s₀.caches ∧
      s'.pins = s₀.pins ∧ s'.memos.instLC = ∅ ∧
      InstLAt ws d s₀.store e s'.store r :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    (instantiateListFast_spec fuel s₀ e vs d ws hok hvec hden)

/-! ## The axiom check

Every Theorem 1 of this file and the licences it rests on, so that nothing can
hide anywhere. -/

#print axioms instantiateList_of_bvarBound_le
#print axioms liftLooseBVars_of_bvarBound_le
#print axioms eidxCopyUpto_toList
#print axioms takeEidx_toList
#print axioms lastEidx_toList
#print axioms InstLVec.get
#print axioms InstLVec.last
#print axioms InstLVec.getElem_eq
#print axioms derivedBound
#print axioms instantiateList_bvar_eq
#print axioms instantiateList_leaf
#print axioms instPisAtLift_cons_eq
#print axioms liftSet_specG
#print axioms inst1LSet_specG
#print axioms instLSet_specG
#print axioms bvarB_bvarBSpec
#print axioms liftLooseBVarsGo_spec
#print axioms liftLooseBVarsFast_spec
#print axioms instantiate1LiftGo_spec
#print axioms instantiate1LiftFast_spec
#print axioms instantiate1LiftFast_run
#print axioms instPisAtLift_specA
#print axioms instPisAtLift_spec
#print axioms instListArmApp_spec
#print axioms instListArmBind_spec
#print axioms instListArmLet_spec
#print axioms instListArmProj_spec
#print axioms instListArmBVar_spec
#print axioms instantiateList_spec
#print axioms instListGoArmApp_spec
#print axioms instListGoArmBind_spec
#print axioms instListGoArmLet_spec
#print axioms instListGoArmProj_spec
#print axioms instantiateListGo_spec
#print axioms instantiateListFast_spec
#print axioms instantiateListFast_run

end ConRon.Bridge.ExprOps

/-
# `ConRon.Bridge.ExprOps.Subst` — Theorem 1 for the SUBSTITUTING walks

DESIGN §8.2's Theorem 1 for group A of the `ExprOps` bridge tier (task
#97-P3-0): `instantiateList`, `liftLooseBVars`, `lowerBVars`,
`instantiate1Lift`, `instPisAtLift` and the three pure `Array` helpers the
first of them consumes.  `ExprOps/Inst1.lean` is the exemplar and this file
copies its shape — the `…Spec` record for one level of the recursion, the fuel
induction, the per-arm `_step` lemmas, the `attribute [-grind]` line, the
`next =>` blocks.

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
| `lowerBVarsGo` | :1700 | `LowerSpec`, `lowerBVarsGo_spec` |
| `lowerBVarsFast` | :1761 | `lowerBVarsFast_spec`, `_run` |
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
3. **`lowerBVarsGo`'s and `instantiate1LiftGo`'s cutoffs ARE con-leche's own**,
   so their licences are QUOTED, not reproved:
   `Expr.lowerBVars_of_bvarBound_le` (`ConLeche/Kernel/ExprOps.lean:1959`) and
   `Expr.instantiate1Lift_of_bvarBound_le` (`:2169`), wrapped as
   `LowerAt.cutoff` and `Inst1LAt.cutoff`.
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
dispatcher whose `mvcgen` list is the arm theorems.  Two verification
conditions then survive each dispatcher — the derived-word cutoff and the
catch-all leaf — against the twenty-odd the inline body left, and the three
goals task #97-P3-0 recorded as open are closed:

* the `.bvar` arm's four branches, through `InstLAt.bvar_{below,cutV,recV,
  aboveV}` and `InstLVec.get'`;
* the binder arms' `internBindIE` side conditions, through `BMExt`
  (`Bridge/StoreBM.lean`) — the conjunct every `…Spec` record of this file's
  two walks now carries;
* `instPisAtLift`'s `cons` step, through `RelEO.instPisAtLift_cons` and
  `RelEO.instPisAtLift_none`.

**The unmemoized walk's arms differ in shape from the memoized walk's**: the
pure arms END with the intern, so `mvcgen` leaves its postcondition as the
goal's ANTECEDENTS and the block has to `intro` before it can `refine`; the
memoized arms end with `pure r` after the memo insert, so the same facts
arrive peeled into the context and the blocks read exactly like
`ExprOps/Inst1.lean`'s.

## The two mechanical findings this file adds to the recipe

* **A spec parameter the program does not mention is filled in by `mvcgen`
  from the local context.**  `Bridge/Specs.lean`'s four memo-insert specs
  (`instLSet_spec`, `liftSet_spec`, `lowerSet_spec`, `inst1LSet_spec`) take the
  walk's own parameter — `ws`, `amount`, `ve` — as an ordinary argument, and
  `mspec` has nothing to unify it against; in `liftLooseBVarsGo`'s arms it
  picks the cutoff's `bRaw`, and in the `proj` arm the projection index.  The
  fix, measured, is to make the PURE FUNCTION the parameter
  (`f : Nat → Expr → Expr`, uninhabited in the arm's context, so `mvcgen`
  leaves it as one verification condition the walk pins with a single `exact`)
  and to register the replacement `@[spec high]`, because a later `@[spec]`
  does **not** override an earlier one for the same program.  `liftSet_specG`
  carries the full note.
* **`bvarB` is not one of these thirteen twins**, and `lowerBVarsGo` /
  `instantiate1LiftGo` test it.  Round 3 carried its Theorem 1 as a
  hypothesis `hbb : ∀ f, BvarBSpec (bvarB f)`; **round 4 discharged it**
  (`bvarB_bvarBSpec`) and deleted every binder, so the four entry points and
  `instPisAtLift_spec` are callable with no hypothesis about `bvarB` at all.
  The discharge was not free: `Bridge/ExprOps/Ranges.lean` had to state the
  two memo-frame conjuncts `BvarBSpec` asks for and `bvarB_spec` did not
  (`s'.memos.lowerC` and `s'.memos.inst1LC`) — see §4 of that round.
* **`BMExt` is in every record of this file** (round 4).  `LiftSpec`,
  `LowerSpec` and `Inst1LSpec` stated `Ext` and not `BMExt`, where their
  siblings `InstLPureSpec` / `InstLSpec` state both — and
  `Bridge/Inductives/Rel.lean`'s `PStep` has a `bm` field, so a
  `PSpec`-grade twin that lifts could not produce a frame AT ALL
  (`structIdxAt_spec` and, through it, the Inductives tier's groups 3 and 4
  and `closeTelescope`).  The conjunct is threaded through the three records,
  `liftLooseBVarsFast`, `lowerBVarsFast`, `instantiate1LiftFast`,
  `instantiateListFast` (spec and run form each) and `instPisAtLift_spec`.
  It cost **one `BMExt.refl _` or one
  `by grind only [BMExt.trans, BMExt.refl]` per verification condition and
  nothing else**: `Bridge/Specs.lean`'s intern specs have carried `BMExt`
  since task #97-P3-1 §3, so the fact was already in every arm's context.
-/
import ConRon.Bridge.Specs
import ConRon.Bridge.ExprOps.Ranges

namespace ConRon.Bridge.ExprOps

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 4000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

/-! ### Attribute hygiene (task #97s round 2, item 1)

`RelE.ext`, `.of_ext` and `.retarget` close the answer relation under `Ext` in
both directions, so every intermediate store multiplies every answer already
known.  The `_step` lemmas below carry the whole chain, so the three are
redundant *and* explosive; `attribute [-grind]` does not travel through an
import, so every file of this tier repeats the line. -/
attribute [-grind] RelE.ext RelE.of_ext RelE.retarget


/-- con-leche: none — as `Inst1.lean`'s `sub_hyp`, under a different name
because two `macro "sub_hyp"` declarations in one import closure make the
token ambiguous. -/
macro "subst_hyp" : tactic => `(tactic| first
  | assumption
  | (symm; assumption)
  | grind only [Ext.trans, Ext.refl])

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
    rw [eidxCopyUpto, dif_pos h, ih, Array.toList_push,
      List.drop_eq_getElem_cons hlt, show k - i = (k - i - 1) + 1 from by omega,
      List.take_succ_cons]
    simp only [Array.getElem_toList, List.append_assoc, List.cons_append,
      List.nil_append, show k - i - 1 = k - (i + 1) from by omega]
  | case2 i out h =>
    rcases Nat.lt_or_ge i k with hk | hk
    · have hd : xs.toList.drop i = [] := by
        apply List.drop_eq_nil_of_le
        rw [Array.length_toList]; omega
      rw [eidxCopyUpto, dif_neg h, hd]
      simp
    · rw [eidxCopyUpto, dif_neg h, show k - i = 0 from by omega]
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
own `lowerBVars_of_bvarBound_le`: the same induction at a different offset. -/

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
  | lam ty b m iht ihb =>
    intro d h
    simp only [Expr.bvarBound, Nat.max_le] at h
    rw [Expr.instantiateList, iht d h.1, ihb (d + 1) (by omega)]
  | forallE ty b m iht ihb =>
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
  | lam ty b m iht ihb =>
    intro c h
    simp only [Expr.bvarBound, Nat.max_le] at h
    rw [Expr.liftLooseBVars, iht c h.1, ihb (c + 1) (by omega)]
  | forallE ty b m iht ihb =>
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

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1456 bvarBRaw_exact — the first
derived cutoff as the arena TESTS it. -/
theorem instantiateList_of_raw_le {ws : List Expr} {e : Expr} {d : Nat}
    (hsat : e.bvarBRaw < satRange) (hle : e.bvarBRaw ≤ d) :
    e.instantiateList ws d = e :=
  instantiateList_of_bvarBound_le e d
    (by rw [← Expr.bvarBRaw_exact e hsat]; exact hle)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1456 bvarBRaw_exact — the second
derived cutoff as the arena TESTS it. -/
theorem liftLooseBVars_of_raw_le {amount : Nat} {e : Expr} {c : Nat}
    (hsat : e.bvarBRaw < satRange) (hle : e.bvarBRaw ≤ c) :
    Expr.liftLooseBVars amount c e = e :=
  liftLooseBVars_of_bvarBound_le e c
    (by rw [← Expr.bvarBRaw_exact e hsat]; exact hle)

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

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — `lowerBVars`' answer
relation. -/
abbrev LowerAt (amount c : Nat) : EStore → EIdx → EStore → EIdx → Prop :=
  RelE (Expr.lowerBVars amount c)

/-- con-leche: ConLeche/Verify/SimI.lean:250 RelE — `instantiate1Lift`'s
answer relation. -/
abbrev Inst1LAt (ve : Expr) (d : Nat) : EStore → EIdx → EStore → EIdx → Prop :=
  RelE (fun e => e.instantiate1Lift ve d)

/-! ## G. The four cutoffs, as step lemmas

`Inst1.lean`'s finding: left as separate `grind` hints the cutoff sends the
closer into an ematching spiral on the pure function's own iterate, and as one
lemma whose pattern is the store read it fires once. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:211-235 instantiateList — the
DERIVED-word cutoff arm of `instantiateList`/`instantiateListGo`. -/
theorem InstLAt.cutoff {st : EStore} (hwf : StoreWF st) {h : EIdx} {d : Nat}
    {ws : List Expr} (hsat : (bvarOfData (st.derived h)).toNat < satRange)
    (hle : (bvarOfData (st.derived h)).toNat ≤ d) : InstLAt ws d st h st h := by
  intro e he
  show denoteE st h = some (e.instantiateList ws d)
  have hd := EStore.derived_exact hwf he
  rw [hd] at hsat hle
  rw [instantiateList_of_raw_le hsat hle]
  exact he

/-- con-leche: ConLeche/Kernel/ExprOps.lean:386-400 liftLooseBVars — the
DERIVED-word cutoff arm of `liftLooseBVarsGo`. -/
theorem LiftAt.cutoff {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {amount c : Nat} (hsat : (bvarOfData (st.derived h)).toNat < satRange)
    (hle : (bvarOfData (st.derived h)).toNat ≤ c) :
    LiftAt amount c st h st h := by
  intro e he
  show denoteE st h = some (Expr.liftLooseBVars amount c e)
  have hd := EStore.derived_exact hwf he
  rw [hd] at hsat hle
  rw [liftLooseBVars_of_raw_le hsat hle]
  exact he

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1959 lowerBVars_of_bvarBound_le —
`lowerBVarsGo`'s cutoff arm, which is con-leche's OWN cutoff: the licence is
quoted, not reproved.  The bound arrives as `bvarB`'s answer relation rather
than as a derived-word read, because that is what the twin tests. -/
theorem LowerAt.cutoff {st : EStore} {h : EIdx} {amount c bb : Nat}
    (hv : RelV Expr.bvarBound st h bb) (hle : bb ≤ c + amount) :
    LowerAt amount c st h st h := by
  intro e he
  show denoteE st h = some (Expr.lowerBVars amount c e)
  rw [Expr.lowerBVars_of_bvarBound_le e amount c (by rw [← hv e he]; exact hle)]
  exact he

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2169 instantiate1Lift_of_bvarBound_le
— `instantiate1LiftGo`'s cutoff arm, con-leche's own, quoted. -/
theorem Inst1LAt.cutoff {st : EStore} {h : EIdx} {ve : Expr} {d bb : Nat}
    (hv : RelV Expr.bvarBound st h bb) (hle : bb ≤ d) :
    Inst1LAt ve d st h st h := by
  intro e he
  show denoteE st h = some (e.instantiate1Lift ve d)
  rw [Expr.instantiate1Lift_of_bvarBound_le e ve d (by rw [← hv e he]; exact hle)]
  exact he


/-! ## G2. The leaf and `bvar` arms of a view-dispatching walk

`liftLooseBVarsGo`, `lowerBVarsGo` and `instantiate1LiftGo` dispatch on the
whole `view`, so their four leaf arms and their `bvar` arm arrive with the
view in hand and are closed by one lemma each rather than by the tag
calculus. -/

/-- con-leche: none — **the four LEAF arms, once**: a walk whose pure function
is the identity on the four leaf constructors answers the handle it was
given. -/
theorem RelE.leaf_view {f : Expr -> Expr} {st : EStore} (hwf : StoreWF st)
    {h : EIdx} {v : ENodeView} (hview : st.view h = some v)
    (hid : ∀ e, ((∃ k t, e = .fvar k t) ∨ (∃ u, e = .sort u) ∨
      (∃ n us, e = .const n us) ∨ ∃ l, e = .lit l) → f e = e)
    (hleaf : (∃ k t, v = .fvar k t) ∨ (∃ u, v = .sort u) ∨
      (∃ n us, v = .const n us) ∨ ∃ l, v = .lit l) : RelE f st h st h := by
  intro e he
  rcases hleaf with ⟨k, t, rfl⟩ | ⟨u, rfl⟩ | ⟨n, us, rfl⟩ | ⟨l, rfl⟩
  · obtain ⟨t', rfl, _⟩ := denote_fvar_inv hwf hview he
    rw [hid _ (Or.inl ⟨k, t', rfl⟩)]; exact he
  · obtain ⟨u', rfl, _⟩ := denote_sort_inv hwf hview he
    rw [hid _ (Or.inr (Or.inl ⟨u', rfl⟩))]; exact he
  · obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hwf hview he
    rw [hid _ (Or.inr (Or.inr (Or.inl ⟨nm, ls, rfl⟩)))]; exact he
  · obtain rfl := denote_lit_inv hwf hview he
    rw [hid _ (Or.inr (Or.inr (Or.inr ⟨l, rfl⟩)))]
    exact he

/-- con-leche: ConLeche/Kernel/ExprOps.lean:386-400 liftLooseBVars — the
identity on leaves. -/
theorem liftLooseBVars_leaf {amount c : Nat} {e : Expr}
    (h : (∃ k t, e = .fvar k t) ∨ (∃ u, e = .sort u) ∨
      (∃ n us, e = .const n us) ∨ ∃ l, e = .lit l) :
    Expr.liftLooseBVars amount c e = e := by
  rcases h with ⟨k, t, rfl⟩ | ⟨u, rfl⟩ | ⟨n, us, rfl⟩ | ⟨l, rfl⟩ <;>
    simp [Expr.liftLooseBVars]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:704-716 lowerBVars — the identity
on leaves. -/
theorem lowerBVars_leaf {amount c : Nat} {e : Expr}
    (h : (∃ k t, e = .fvar k t) ∨ (∃ u, e = .sort u) ∨
      (∃ n us, e = .const n us) ∨ ∃ l, e = .lit l) :
    Expr.lowerBVars amount c e = e := by
  rcases h with ⟨k, t, rfl⟩ | ⟨u, rfl⟩ | ⟨n, us, rfl⟩ | ⟨l, rfl⟩ <;>
    simp [Expr.lowerBVars]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:722-739 instantiate1Lift — the
identity on leaves. -/
theorem instantiate1Lift_leaf {ve : Expr} {d : Nat} {e : Expr}
    (h : (∃ k t, e = .fvar k t) ∨ (∃ u, e = .sort u) ∨
      (∃ n us, e = .const n us) ∨ ∃ l, e = .lit l) :
    e.instantiate1Lift ve d = e := by
  rcases h with ⟨k, t, rfl⟩ | ⟨u, rfl⟩ | ⟨n, us, rfl⟩ | ⟨l, rfl⟩ <;>
    simp [Expr.instantiate1Lift]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:211-235 instantiateList — the
identity on leaves. -/
theorem instantiateList_leaf {ws : List Expr} {d : Nat} {e : Expr}
    (h : (∃ k t, e = .fvar k t) ∨ (∃ u, e = .sort u) ∨
      (∃ n us, e = .const n us) ∨ ∃ l, e = .lit l) :
    e.instantiateList ws d = e := by
  rcases h with ⟨k, t, rfl⟩ | ⟨u, rfl⟩ | ⟨n, us, rfl⟩ | ⟨l, rfl⟩ <;>
    rw [Expr.instantiateList]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:387 liftLooseBVars — the `.bvar`
arm's LIFTING branch. -/
theorem LiftAt.bvar_up {st st' : EStore} {h r : EIdx} {amount c i : Nat}
    (hwf : StoreWF st) (hview : st.view h = some (.bvar i)) (hge : i ≥ c)
    (hr : denoteE st' r = denoteEView st' (.bvar (i + amount))) :
    LiftAt amount c st h st' r := by
  intro e he
  obtain rfl := denote_bvar_inv hwf hview he
  show denoteE st' r = some (Expr.liftLooseBVars amount c (.bvar i))
  rw [hr]
  simp [Expr.liftLooseBVars, hge, denoteEView]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:387 liftLooseBVars — the `.bvar`
arm's IDENTITY branch. -/
theorem LiftAt.bvar_self {st : EStore} {h : EIdx} {amount c i : Nat}
    (hwf : StoreWF st) (hview : st.view h = some (.bvar i)) (hlt : ¬ (i ≥ c)) :
    LiftAt amount c st h st h := by
  intro e he
  obtain rfl := denote_bvar_inv hwf hview he
  show denoteE st h = some (Expr.liftLooseBVars amount c (.bvar i))
  simp only [Expr.liftLooseBVars, if_neg hlt]
  exact he

/-- con-leche: ConLeche/Kernel/ExprOps.lean:705 lowerBVars — the `.bvar` arm's
LOWERING branch. -/
theorem LowerAt.bvar_down {st st' : EStore} {h r : EIdx} {amount c i : Nat}
    (hwf : StoreWF st) (hview : st.view h = some (.bvar i))
    (hge : i ≥ c + amount)
    (hr : denoteE st' r = denoteEView st' (.bvar (i - amount))) :
    LowerAt amount c st h st' r := by
  intro e he
  obtain rfl := denote_bvar_inv hwf hview he
  show denoteE st' r = some (Expr.lowerBVars amount c (.bvar i))
  rw [hr]
  simp [Expr.lowerBVars, hge, denoteEView]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:705 lowerBVars — the `.bvar` arm's
IDENTITY branch. -/
theorem LowerAt.bvar_self {st : EStore} {h : EIdx} {amount c i : Nat}
    (hwf : StoreWF st) (hview : st.view h = some (.bvar i))
    (hlt : ¬ (i ≥ c + amount)) : LowerAt amount c st h st h := by
  intro e he
  obtain rfl := denote_bvar_inv hwf hview he
  show denoteE st h = some (Expr.lowerBVars amount c (.bvar i))
  simp only [Expr.lowerBVars, if_neg hlt]
  exact he

/-- con-leche: ConLeche/Kernel/ExprOps.lean:724-726 instantiate1Lift — the
`.bvar` arm's SUBSTITUTING branch: the replacement's own loose `bvar`s are
lifted past the `d` binders crossed on the way, which is the nested
`liftLooseBVarsFast` call. -/
theorem Inst1LAt.bvar_subst {st st' : EStore} {h r : EIdx} {ve : Expr}
    {d i : Nat} (hwf : StoreWF st) (hview : st.view h = some (.bvar i))
    (heq : i = d) (hr : denoteE st' r = some (Expr.liftLooseBVars d 0 ve)) :
    Inst1LAt ve d st h st' r := by
  intro e he
  obtain rfl := denote_bvar_inv hwf hview he
  show denoteE st' r = some ((Expr.bvar i).instantiate1Lift ve d)
  simp only [Expr.instantiate1Lift, if_pos heq]
  exact hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:726 instantiate1Lift — the `.bvar`
arm's LOWERING branch. -/
theorem Inst1LAt.bvar_down {st st' : EStore} {h r : EIdx} {ve : Expr}
    {d i : Nat} (hwf : StoreWF st) (hview : st.view h = some (.bvar i))
    (hne : ¬ (i = d)) (hgt : i > d)
    (hr : denoteE st' r = denoteEView st' (.bvar (i - 1))) :
    Inst1LAt ve d st h st' r := by
  intro e he
  obtain rfl := denote_bvar_inv hwf hview he
  show denoteE st' r = some ((Expr.bvar i).instantiate1Lift ve d)
  rw [hr]
  simp [Expr.instantiate1Lift, hne, hgt, denoteEView]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:726 instantiate1Lift — the `.bvar`
arm's IDENTITY branch. -/
theorem Inst1LAt.bvar_self {st : EStore} {h : EIdx} {ve : Expr} {d i : Nat}
    (hwf : StoreWF st) (hview : st.view h = some (.bvar i))
    (hne : ¬ (i = d)) (hgt : ¬ (i > d)) : Inst1LAt ve d st h st h := by
  intro e he
  obtain rfl := denote_bvar_inv hwf hview he
  show denoteE st h = some ((Expr.bvar i).instantiate1Lift ve d)
  simp only [Expr.instantiate1Lift, if_neg hne, if_neg hgt]
  exact he

/-! ## H. The per-arm step lemmas

`Bridge/Rel.lean` group 7's generic `RelE.app` / `.lam` / `.forallE` / `.letE`
/ `.proj` with the pure clause discharged and the extension chain spelled out
in the shape `mvcgen` produces (task #97s round 2, item 3).

The three walks that dispatch on `view` (`liftLooseBVarsGo`, `lowerBVarsGo`,
`instantiate1LiftGo`) hand their arm the view DIRECTLY, so they need no `_tag`
variant and no `viewBM` detour — which is why they carry none of `Inst1.lean`'s
binder-arm gaps.  The two that dispatch on the TAG (`instantiateList`,
`instantiateListGo`) use `Inst1.lean`'s `_tag` shape. -/

section Steps
variable {st s1 s2 s3 s4 : EStore}

/-! ### `instantiateList` -/

theorem InstLAt.app_step {ws : List Expr} {d : Nat} {h f a rf ra r : EIdx}
    (hwf : StoreWF st) (htg : (h.tag == ETag.app) = true)
    (hva : some (f, a) = st.viewApp h)
    (hx1 : Ext st s1) (hf : InstLAt ws d st f s1 rf)
    (hx2 : Ext s1 s2) (ha : InstLAt ws d s1 a s2 ra)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) :
    InstLAt ws d st h s3 r :=
  RelE.app hwf (view_of_viewApp_tag htg hva.symm)
    (fun _ _ => by rw [Expr.instantiateList]) ((hf.ext hx2).ext hx3)
    ((ha.of_ext hx1).ext hx3) hr

theorem InstLAt.bind_step {ws : List Expr} {d : Nat} {h ty b rt rb r : EIdx}
    {m : BinderMeta} {tg : UInt32} (hwf : StoreWF st)
    (htg : ETag.isBind tg = true)
    (hview : st.view h = some (eBindView tg ty b m))
    (hx1 : Ext st s1) (ht : InstLAt ws d st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : InstLAt ws (d + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (eBindView tg rt rb m)) :
    InstLAt ws d st h s3 r := by
  rcases (show tg = ETag.lam ∨ tg = ETag.forallE by
      simp only [ETag.isBind, Bool.or_eq_true, beq_iff_eq] at htg; exact htg)
    with rfl | rfl
  · rw [eBindView] at hview hr; simp only [beq_self_eq_true, if_true] at hview hr
    exact RelE.lam hwf hview (fun _ _ => by rw [Expr.instantiateList])
      ((ht.ext hx2).ext hx3) ((hb.of_ext hx1).ext hx3) hr
  · rw [eBindView] at hview hr
    simp only [ETag.lam, ETag.forallE] at hview hr
    exact RelE.forallE hwf hview (fun _ _ => by rw [Expr.instantiateList])
      ((ht.ext hx2).ext hx3) ((hb.of_ext hx1).ext hx3) hr

theorem InstLAt.bind_step' {ws : List Expr} {d : Nat} {h ty b rt rb r : EIdx}
    {mi : BMIdx} {m : BinderMeta} {tg : UInt32} (hwf : StoreWF st)
    (htg : ETag.isBind tg = true) (htg2 : tg = h.tag)
    (hvb : some (ty, b, mi) = st.viewBindI h) (hbm : st.viewBM mi = some m)
    (hx1 : Ext st s1) (ht : InstLAt ws d st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : InstLAt ws (d + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (eBindView tg rt rb m)) :
    InstLAt ws d st h s3 r := by
  refine InstLAt.bind_step hwf htg ?_ hx1 ht hx2 hb hx3 hr
  rw [htg2] at htg ⊢
  exact view_of_viewBindI htg hvb.symm hbm

theorem InstLAt.letE_step {ws : List Expr} {d : Nat}
    {h ty w b rt rw rb r : EIdx} (hwf : StoreWF st)
    (htg : (h.tag == ETag.letE) = true) (hvl : some (ty, w, b) = st.viewLet h)
    (hx1 : Ext st s1) (ht : InstLAt ws d st ty s1 rt)
    (hx2 : Ext s1 s2) (hw : InstLAt ws d s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : InstLAt ws (d + 1) s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) :
    InstLAt ws d st h s4 r :=
  RelE.letE hwf (view_of_viewLet_tag htg hvl.symm)
    (fun _ _ _ => by rw [Expr.instantiateList])
    (((ht.ext hx2).ext hx3).ext hx4) (((hw.of_ext hx1).ext hx3).ext hx4)
    ((hb.of_ext (hx1.trans hx2)).ext hx4) hr

theorem InstLAt.proj_step {ws : List Expr} {d : Nat} {h sub rs r : EIdx}
    {n : NIdx} {i : Nat} {nm : ConLeche.Name} (hwf : StoreWF st)
    (htg : (h.tag == ETag.proj) = true)
    (hvp : some (n, i, sub) = st.viewProj h)
    (hx1 : Ext st s1) (hs : InstLAt ws d st sub s1 rs)
    (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs))
    (hn0 : denoteN st.ns n = some nm) : InstLAt ws d st h s2 r :=
  RelE.proj hwf (view_of_viewProj_tag htg hvp.symm)
    (fun _ => by rw [Expr.instantiateList]) (hs.ext hx2) hn0
    (denoteN_ext (denoteN_ext hn0 hx1) hx2) hr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:211-235 instantiateList — the
CATCH-ALL arm: a handle whose tag is none of the six the walk dispatches on
denotes a leaf, and `instantiateList` is the identity there. -/
theorem InstLAt.leaf {ws : List Expr} {d : Nat} {h : EIdx} {v : ENodeView}
    (hwf : StoreWF st) (hview : st.view h = some v)
    (happ : ¬ (h.tag = ETag.app)) (hbind : ETag.isBind h.tag = false)
    (hbvar : ¬ (h.tag = ETag.bvar)) (hlet : ¬ (h.tag = ETag.letE))
    (hproj : ¬ (h.tag = ETag.proj)) : InstLAt ws d st h st h := by
  intro e he
  show denoteE st h = some (e.instantiateList ws d)
  rcases denote_leaf_of_tag hwf hview happ hbind hbvar hlet hproj he with
    ⟨k, t, rfl⟩ | ⟨u, rfl⟩ | ⟨n, us, rfl⟩ | ⟨l, rfl⟩ <;>
    (rw [Expr.instantiateList]; exact he)

/-! ### `liftLooseBVars` -/

theorem LiftAt.app_step {amount c : Nat} {h f a rf ra r : EIdx}
    (hwf : StoreWF st) (hview : st.view h = some (.app f a))
    (hx1 : Ext st s1) (hf : LiftAt amount c st f s1 rf)
    (hx2 : Ext s1 s2) (ha : LiftAt amount c s1 a s2 ra)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) :
    LiftAt amount c st h s3 r :=
  RelE.app hwf hview (fun _ _ => rfl) ((hf.ext hx2).ext hx3)
    ((ha.of_ext hx1).ext hx3) hr

theorem LiftAt.lam_step {amount c : Nat} {h ty b rt rb r : EIdx}
    {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.lam ty b m))
    (hx1 : Ext st s1) (ht : LiftAt amount c st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : LiftAt amount (c + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.lam rt rb m)) :
    LiftAt amount c st h s3 r :=
  RelE.lam hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
    ((hb.of_ext hx1).ext hx3) hr

theorem LiftAt.forallE_step {amount c : Nat} {h ty b rt rb r : EIdx}
    {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.forallE ty b m))
    (hx1 : Ext st s1) (ht : LiftAt amount c st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : LiftAt amount (c + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.forallE rt rb m)) :
    LiftAt amount c st h s3 r :=
  RelE.forallE hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
    ((hb.of_ext hx1).ext hx3) hr

theorem LiftAt.letE_step {amount c : Nat} {h ty w b rt rw rb r : EIdx}
    (hwf : StoreWF st) (hview : st.view h = some (.letE ty w b))
    (hx1 : Ext st s1) (ht : LiftAt amount c st ty s1 rt)
    (hx2 : Ext s1 s2) (hw : LiftAt amount c s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : LiftAt amount (c + 1) s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) :
    LiftAt amount c st h s4 r :=
  RelE.letE hwf hview (fun _ _ _ => rfl) (((ht.ext hx2).ext hx3).ext hx4)
    (((hw.of_ext hx1).ext hx3).ext hx4)
    ((hb.of_ext (hx1.trans hx2)).ext hx4) hr

theorem LiftAt.proj_step {amount c : Nat} {h sub rs r : EIdx} {n : NIdx}
    {i : Nat} {nm : ConLeche.Name} (hwf : StoreWF st)
    (hview : st.view h = some (.proj n i sub))
    (hx1 : Ext st s1) (hs : LiftAt amount c st sub s1 rs)
    (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs))
    (hn0 : denoteN st.ns n = some nm) : LiftAt amount c st h s2 r :=
  RelE.proj hwf hview (fun _ => rfl) (hs.ext hx2) hn0
    (denoteN_ext (denoteN_ext hn0 hx1) hx2) hr

/-! ### `lowerBVars` -/

theorem LowerAt.app_step {amount c : Nat} {h f a rf ra r : EIdx}
    (hwf : StoreWF st) (hview : st.view h = some (.app f a))
    (hx1 : Ext st s1) (hf : LowerAt amount c st f s1 rf)
    (hx2 : Ext s1 s2) (ha : LowerAt amount c s1 a s2 ra)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) :
    LowerAt amount c st h s3 r :=
  RelE.app hwf hview (fun _ _ => rfl) ((hf.ext hx2).ext hx3)
    ((ha.of_ext hx1).ext hx3) hr

theorem LowerAt.lam_step {amount c : Nat} {h ty b rt rb r : EIdx}
    {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.lam ty b m))
    (hx1 : Ext st s1) (ht : LowerAt amount c st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : LowerAt amount (c + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.lam rt rb m)) :
    LowerAt amount c st h s3 r :=
  RelE.lam hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
    ((hb.of_ext hx1).ext hx3) hr

theorem LowerAt.forallE_step {amount c : Nat} {h ty b rt rb r : EIdx}
    {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.forallE ty b m))
    (hx1 : Ext st s1) (ht : LowerAt amount c st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : LowerAt amount (c + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.forallE rt rb m)) :
    LowerAt amount c st h s3 r :=
  RelE.forallE hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
    ((hb.of_ext hx1).ext hx3) hr

theorem LowerAt.letE_step {amount c : Nat} {h ty w b rt rw rb r : EIdx}
    (hwf : StoreWF st) (hview : st.view h = some (.letE ty w b))
    (hx1 : Ext st s1) (ht : LowerAt amount c st ty s1 rt)
    (hx2 : Ext s1 s2) (hw : LowerAt amount c s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : LowerAt amount (c + 1) s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) :
    LowerAt amount c st h s4 r :=
  RelE.letE hwf hview (fun _ _ _ => rfl) (((ht.ext hx2).ext hx3).ext hx4)
    (((hw.of_ext hx1).ext hx3).ext hx4)
    ((hb.of_ext (hx1.trans hx2)).ext hx4) hr

theorem LowerAt.proj_step {amount c : Nat} {h sub rs r : EIdx} {n : NIdx}
    {i : Nat} {nm : ConLeche.Name} (hwf : StoreWF st)
    (hview : st.view h = some (.proj n i sub))
    (hx1 : Ext st s1) (hs : LowerAt amount c st sub s1 rs)
    (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs))
    (hn0 : denoteN st.ns n = some nm) : LowerAt amount c st h s2 r :=
  RelE.proj hwf hview (fun _ => rfl) (hs.ext hx2) hn0
    (denoteN_ext (denoteN_ext hn0 hx1) hx2) hr

/-! ### `instantiate1Lift` -/

theorem Inst1LAt.app_step {ve : Expr} {d : Nat} {h f a rf ra r : EIdx}
    (hwf : StoreWF st) (hview : st.view h = some (.app f a))
    (hx1 : Ext st s1) (hf : Inst1LAt ve d st f s1 rf)
    (hx2 : Ext s1 s2) (ha : Inst1LAt ve d s1 a s2 ra)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) :
    Inst1LAt ve d st h s3 r :=
  RelE.app hwf hview (fun _ _ => rfl) ((hf.ext hx2).ext hx3)
    ((ha.of_ext hx1).ext hx3) hr

theorem Inst1LAt.lam_step {ve : Expr} {d : Nat} {h ty b rt rb r : EIdx}
    {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.lam ty b m))
    (hx1 : Ext st s1) (ht : Inst1LAt ve d st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : Inst1LAt ve (d + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.lam rt rb m)) :
    Inst1LAt ve d st h s3 r :=
  RelE.lam hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
    ((hb.of_ext hx1).ext hx3) hr

theorem Inst1LAt.forallE_step {ve : Expr} {d : Nat} {h ty b rt rb r : EIdx}
    {m : BinderMeta} (hwf : StoreWF st)
    (hview : st.view h = some (.forallE ty b m))
    (hx1 : Ext st s1) (ht : Inst1LAt ve d st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : Inst1LAt ve (d + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.forallE rt rb m)) :
    Inst1LAt ve d st h s3 r :=
  RelE.forallE hwf hview (fun _ _ => rfl) ((ht.ext hx2).ext hx3)
    ((hb.of_ext hx1).ext hx3) hr

theorem Inst1LAt.letE_step {ve : Expr} {d : Nat} {h ty w b rt rw rb r : EIdx}
    (hwf : StoreWF st) (hview : st.view h = some (.letE ty w b))
    (hx1 : Ext st s1) (ht : Inst1LAt ve d st ty s1 rt)
    (hx2 : Ext s1 s2) (hw : Inst1LAt ve d s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : Inst1LAt ve (d + 1) s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) :
    Inst1LAt ve d st h s4 r :=
  RelE.letE hwf hview (fun _ _ _ => rfl) (((ht.ext hx2).ext hx3).ext hx4)
    (((hw.of_ext hx1).ext hx3).ext hx4)
    ((hb.of_ext (hx1.trans hx2)).ext hx4) hr

theorem Inst1LAt.proj_step {ve : Expr} {d : Nat} {h sub rs r : EIdx} {n : NIdx}
    {i : Nat} {nm : ConLeche.Name} (hwf : StoreWF st)
    (hview : st.view h = some (.proj n i sub))
    (hx1 : Ext st s1) (hs : Inst1LAt ve d st sub s1 rs)
    (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs))
    (hn0 : denoteN st.ns n = some nm) : Inst1LAt ve d st h s2 r :=
  RelE.proj hwf hview (fun _ => rfl) (hs.ext hx2) hn0
    (denoteN_ext (denoteN_ext hn0 hx1) hx2) hr

end Steps


/-! ## H2. The store-equality casts, and the view-FIRST arm lemmas

`lowerBVarsGo` and `instantiate1LiftGo` read con-leche's `bvarB` before they
read the node, and `bvarB` moves the STATE (`bvarBoundMemo` clears its own
memo) while leaving the STORE alone.  Every arm of those two walks therefore
proves its answer at a store that is *equal* to, but not syntactically, the
one its statement names.  Two one-line casts absorb that, and the arm lemmas
below take the VIEW first so that `assumption` pins the store before it is
asked for that store's `StoreWF`. -/

/-- con-leche: none — retarget an answer relation's SOURCE store along an
equation (the `bvarB` shift, not an extension). -/
theorem RelE.src_eq {f : Expr -> Expr} {st st0 st' : EStore} {c r : EIdx}
    (heq : st0 = st) (h : RelE f st c st' r) : RelE f st0 c st' r := heq ▸ h

/-- con-leche: none — and its TARGET store. -/
theorem RelE.tgt_eq {f : Expr -> Expr} {st st' st2 : EStore} {c r : EIdx}
    (heq : st' = st2) (h : RelE f st c st' r) : RelE f st c st2 r := heq ▸ h

/-- con-leche: none — `RelE.leaf_view` with the view first. -/
theorem RelE.leaf_viewV {f : Expr -> Expr} {st : EStore} {h : EIdx}
    {v : ENodeView} (hview : st.view h = some v) (hwf : StoreWF st)
    (hid : ∀ e, ((∃ k t, e = .fvar k t) ∨ (∃ u, e = .sort u) ∨
      (∃ n us, e = .const n us) ∨ ∃ l, e = .lit l) → f e = e)
    (hleaf : (∃ k t, v = .fvar k t) ∨ (∃ u, v = .sort u) ∨
      (∃ n us, v = .const n us) ∨ ∃ l, v = .lit l) : RelE f st h st h :=
  RelE.leaf_view hwf hview hid hleaf

/-- con-leche: none — the `app` arm, view first. -/
theorem LowerAt.app_stepV {amount c : Nat} {st s1 s2 s3 : EStore}
    {h f a rf ra r : EIdx} (hview : st.view h = some (.app f a))
    (hwf : StoreWF st)
    (hx1 : Ext st s1) (hf : LowerAt amount c st f s1 rf)
    (hx2 : Ext s1 s2) (ha : LowerAt amount c s1 a s2 ra)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) :
    LowerAt amount c st h s3 r :=
  LowerAt.app_step hwf hview hx1 hf hx2 ha hx3 hr

/-- con-leche: none — the `lam` arm, view first. -/
theorem LowerAt.lam_stepV {amount c : Nat} {st s1 s2 s3 : EStore}
    {h ty b rt rb r : EIdx} {m : BinderMeta}
    (hview : st.view h = some (.lam ty b m)) (hwf : StoreWF st)
    (hx1 : Ext st s1) (ht : LowerAt amount c st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : LowerAt amount (c + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.lam rt rb m)) :
    LowerAt amount c st h s3 r :=
  LowerAt.lam_step hwf hview hx1 ht hx2 hb hx3 hr

/-- con-leche: none — the `forallE` arm, view first. -/
theorem LowerAt.forallE_stepV {amount c : Nat} {st s1 s2 s3 : EStore}
    {h ty b rt rb r : EIdx} {m : BinderMeta}
    (hview : st.view h = some (.forallE ty b m)) (hwf : StoreWF st)
    (hx1 : Ext st s1) (ht : LowerAt amount c st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : LowerAt amount (c + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.forallE rt rb m)) :
    LowerAt amount c st h s3 r :=
  LowerAt.forallE_step hwf hview hx1 ht hx2 hb hx3 hr

/-- con-leche: none — the `letE` arm, view first. -/
theorem LowerAt.letE_stepV {amount c : Nat} {st s1 s2 s3 s4 : EStore}
    {h ty w b rt rw rb r : EIdx}
    (hview : st.view h = some (.letE ty w b)) (hwf : StoreWF st)
    (hx1 : Ext st s1) (ht : LowerAt amount c st ty s1 rt)
    (hx2 : Ext s1 s2) (hw : LowerAt amount c s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : LowerAt amount (c + 1) s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) :
    LowerAt amount c st h s4 r :=
  LowerAt.letE_step hwf hview hx1 ht hx2 hw hx3 hb hx4 hr

/-- con-leche: none — the `proj` arm, view first. -/
theorem LowerAt.proj_stepV {amount c : Nat} {st s1 s2 : EStore}
    {h sub rs r : EIdx} {n : NIdx} {i : Nat} {nm : ConLeche.Name}
    (hview : st.view h = some (.proj n i sub)) (hwf : StoreWF st)
    (hx1 : Ext st s1) (hs : LowerAt amount c st sub s1 rs)
    (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs))
    (hn0 : denoteN st.ns n = some nm) : LowerAt amount c st h s2 r :=
  LowerAt.proj_step hwf hview hx1 hs hx2 hr hn0

/-- con-leche: none — the `app` arm, view first. -/
theorem Inst1LAt.app_stepV {ve : Expr} {d : Nat} {st s1 s2 s3 : EStore}
    {h f a rf ra r : EIdx} (hview : st.view h = some (.app f a))
    (hwf : StoreWF st)
    (hx1 : Ext st s1) (hf : Inst1LAt ve d st f s1 rf)
    (hx2 : Ext s1 s2) (ha : Inst1LAt ve d s1 a s2 ra)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.app rf ra)) :
    Inst1LAt ve d st h s3 r :=
  Inst1LAt.app_step hwf hview hx1 hf hx2 ha hx3 hr

/-- con-leche: none — the `lam` arm, view first. -/
theorem Inst1LAt.lam_stepV {ve : Expr} {d : Nat} {st s1 s2 s3 : EStore}
    {h ty b rt rb r : EIdx} {m : BinderMeta}
    (hview : st.view h = some (.lam ty b m)) (hwf : StoreWF st)
    (hx1 : Ext st s1) (ht : Inst1LAt ve d st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : Inst1LAt ve (d + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.lam rt rb m)) :
    Inst1LAt ve d st h s3 r :=
  Inst1LAt.lam_step hwf hview hx1 ht hx2 hb hx3 hr

/-- con-leche: none — the `forallE` arm, view first. -/
theorem Inst1LAt.forallE_stepV {ve : Expr} {d : Nat} {st s1 s2 s3 : EStore}
    {h ty b rt rb r : EIdx} {m : BinderMeta}
    (hview : st.view h = some (.forallE ty b m)) (hwf : StoreWF st)
    (hx1 : Ext st s1) (ht : Inst1LAt ve d st ty s1 rt)
    (hx2 : Ext s1 s2) (hb : Inst1LAt ve (d + 1) s1 b s2 rb)
    (hx3 : Ext s2 s3)
    (hr : denoteE s3 r = denoteEView s3 (.forallE rt rb m)) :
    Inst1LAt ve d st h s3 r :=
  Inst1LAt.forallE_step hwf hview hx1 ht hx2 hb hx3 hr

/-- con-leche: none — the `letE` arm, view first. -/
theorem Inst1LAt.letE_stepV {ve : Expr} {d : Nat} {st s1 s2 s3 s4 : EStore}
    {h ty w b rt rw rb r : EIdx}
    (hview : st.view h = some (.letE ty w b)) (hwf : StoreWF st)
    (hx1 : Ext st s1) (ht : Inst1LAt ve d st ty s1 rt)
    (hx2 : Ext s1 s2) (hw : Inst1LAt ve d s1 w s2 rw)
    (hx3 : Ext s2 s3) (hb : Inst1LAt ve (d + 1) s2 b s3 rb)
    (hx4 : Ext s3 s4)
    (hr : denoteE s4 r = denoteEView s4 (.letE rt rw rb)) :
    Inst1LAt ve d st h s4 r :=
  Inst1LAt.letE_step hwf hview hx1 ht hx2 hw hx3 hb hx4 hr

/-- con-leche: none — the `proj` arm, view first. -/
theorem Inst1LAt.proj_stepV {ve : Expr} {d : Nat} {st s1 s2 : EStore}
    {h sub rs r : EIdx} {n : NIdx} {i : Nat} {nm : ConLeche.Name}
    (hview : st.view h = some (.proj n i sub)) (hwf : StoreWF st)
    (hx1 : Ext st s1) (hs : Inst1LAt ve d st sub s1 rs)
    (hx2 : Ext s1 s2)
    (hr : denoteE s2 r = denoteEView s2 (.proj n i rs))
    (hn0 : denoteN st.ns n = some nm) : Inst1LAt ve d st h s2 r :=
  Inst1LAt.proj_step hwf hview hx1 hs hx2 hr hn0

/-- con-leche: none — `LowerAt.bvar_down`, view first. -/
theorem LowerAt.bvar_downV {st st' : EStore} {h r : EIdx} {amount c i : Nat}
    (hview : st.view h = some (.bvar i)) (hwf : StoreWF st)
    (hge : i ≥ c + amount)
    (hr : denoteE st' r = denoteEView st' (.bvar (i - amount))) :
    LowerAt amount c st h st' r := LowerAt.bvar_down hwf hview hge hr

/-- con-leche: none — `LowerAt.bvar_self`, view first. -/
theorem LowerAt.bvar_selfV {st : EStore} {h : EIdx} {amount c i : Nat}
    (hview : st.view h = some (.bvar i)) (hwf : StoreWF st)
    (hlt : ¬ (i ≥ c + amount)) : LowerAt amount c st h st h :=
  LowerAt.bvar_self hwf hview hlt

/-- con-leche: none — `Inst1LAt.bvar_subst`, view first. -/
theorem Inst1LAt.bvar_substV {st st' : EStore} {h r : EIdx} {ve : Expr}
    {d i : Nat} (hview : st.view h = some (.bvar i)) (hwf : StoreWF st)
    (heq : i = d) (hr : denoteE st' r = some (Expr.liftLooseBVars d 0 ve)) :
    Inst1LAt ve d st h st' r := Inst1LAt.bvar_subst hwf hview heq hr

/-- con-leche: none — `Inst1LAt.bvar_down`, view first. -/
theorem Inst1LAt.bvar_downV {st st' : EStore} {h r : EIdx} {ve : Expr}
    {d i : Nat} (hview : st.view h = some (.bvar i)) (hwf : StoreWF st)
    (hne : ¬ (i = d)) (hgt : i > d)
    (hr : denoteE st' r = denoteEView st' (.bvar (i - 1))) :
    Inst1LAt ve d st h st' r := Inst1LAt.bvar_down hwf hview hne hgt hr

/-- con-leche: none — `Inst1LAt.bvar_self`, view first. -/
theorem Inst1LAt.bvar_selfV {st : EStore} {h : EIdx} {ve : Expr} {d i : Nat}
    (hview : st.view h = some (.bvar i)) (hwf : StoreWF st)
    (hne : ¬ (i = d)) (hgt : ¬ (i > d)) : Inst1LAt ve d st h st h :=
  Inst1LAt.bvar_self hwf hview hne hgt

/-- con-leche: none — `Bridge/Rel.lean`'s `denote_eq_proj` with the VIEW
first, so that `assumption` pins the store before it is asked for that store's
`StoreWF` (the `bvarB` walks have two `StoreWF`s in scope). -/
theorem denote_eq_projV {st : EStore} {h : EIdx} {n : NIdx} {i : Nat}
    {sub : EIdx} (hw : st.view h = some (.proj n i sub)) (hwf : StoreWF st)
    (hd : (denoteE st h).isSome = true) :
    ∃ nm es, denoteE st h = some (.proj nm i es) ∧
      denoteN st.ns n = some nm ∧ denoteE st sub = some es :=
  denote_eq_proj hwf hw hd

/-! ## H3. `instantiateList`'s `.bvar` arm

The one arm of this group that is not a congruence: con-leche's `.bvar j`
clause recurses into the REPLACEMENT with the shorter list `vs.take (j - d)`,
and the twin adds the derived cutoff in front of that recursion (task
#97-P6-9, "the cutoff hoisted over the prefix copy").  Four branches, four
lemmas. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:225 instantiateList — `.bvar j`
with `j` BELOW the cursor: a bound variable of the term itself. -/
theorem InstLAt.bvar_below {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {ws : List Expr} {d j : Nat} (hview : st.view h = some (.bvar j))
    (hlt : j < d) : InstLAt ws d st h st h := by
  intro e he
  obtain rfl := denote_bvar_inv hwf hview he
  show denoteE st h = some ((Expr.bvar j).instantiateList ws d)
  rw [Expr.instantiateList, if_pos hlt]
  exact he

/-- con-leche: ConLeche/Kernel/ExprOps.lean:230 instantiateList — `.bvar j`
ABOVE the substituted range: the index drops by the vector's length. -/
theorem InstLAt.bvar_above {st st' : EStore} (hwf : StoreWF st) {h r : EIdx}
    {ws : List Expr} {d j n : Nat} (hview : st.view h = some (.bvar j))
    (hge : ¬ (j < d)) (hn : ¬ (j - d < n)) (hlen : ws.length = n)
    (hr : denoteE st' r = denoteEView st' (.bvar (j - n))) :
    InstLAt ws d st h st' r := by
  intro e he
  obtain rfl := denote_bvar_inv hwf hview he
  show denoteE st' r = some ((Expr.bvar j).instantiateList ws d)
  rw [Expr.instantiateList, if_neg hge,
    dif_neg (show ¬ (j - d < ws.length) from by omega), hr, denoteEView, hlen]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:227-228 instantiateList — `.bvar
j` INSIDE the range, with the twin's hoisted cutoff firing: the replacement is
its own instantiation, so the walk answers the replacement's handle. -/
theorem InstLAt.bvar_cut {st : EStore} (hwf : StoreWF st) {h vi : EIdx}
    {ws : List Expr} {d j : Nat} {w : Expr}
    (hview : st.view h = some (.bvar j)) (hge : ¬ (j < d))
    (hj : j - d < ws.length) (hwi : ws[j - d]? = some w)
    (hvi : denoteE st vi = some w)
    (hsat : (bvarOfData (st.derived vi)).toNat < satRange)
    (hle : (bvarOfData (st.derived vi)).toNat ≤ d) :
    InstLAt ws d st h st vi := by
  intro e he
  obtain rfl := denote_bvar_inv hwf hview he
  show denoteE st vi = some ((Expr.bvar j).instantiateList ws d)
  have hg : ws[j - d] = w := by
    rw [List.getElem?_eq_getElem hj] at hwi; exact Option.some.inj hwi
  rw [Expr.instantiateList, if_neg hge, dif_pos hj, hg]
  have hd := EStore.derived_exact hwf hvi
  rw [hd] at hsat hle
  rw [instantiateList_of_raw_le hsat hle]
  exact hvi

/-- con-leche: ConLeche/Kernel/ExprOps.lean:228 instantiateList — `.bvar j`
INSIDE the range, cutoff not firing: con-leche's own recursion into the
replacement at the shorter list. -/
theorem InstLAt.bvar_rec {st st' : EStore} (hwf : StoreWF st) {h vi r : EIdx}
    {ws : List Expr} {d j : Nat} {w : Expr}
    (hview : st.view h = some (.bvar j)) (hge : ¬ (j < d))
    (hj : j - d < ws.length) (hwi : ws[j - d]? = some w)
    (hvi : denoteE st vi = some w)
    (hrec : InstLAt (ws.take (j - d)) d st vi st' r) :
    InstLAt ws d st h st' r := by
  intro e he
  obtain rfl := denote_bvar_inv hwf hview he
  show denoteE st' r = some ((Expr.bvar j).instantiateList ws d)
  have hg : ws[j - d] = w := by
    rw [List.getElem?_eq_getElem hj] at hwi; exact Option.some.inj hwi
  rw [Expr.instantiateList, if_neg hge, dif_pos hj, hg]
  exact hrec w hvi

/-- con-leche: none — a denoting vector denotes SOME list, in the orientation
`InstLVec` fixes. -/
theorem InstLVec.of_isSome {st : EStore} {vs : Array EIdx}
    (h : (Frontend.denoteEList st vs.toList).isSome = true) :
    ∃ ws, InstLVec st vs ws := by
  obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp h
  exact ⟨xs.reverse, by rw [InstLVec, List.reverse_reverse]; exact hxs⟩

/-- con-leche: none — and the `isSome` travels with the arena. -/
theorem InstLVec.isSome_ext {st st' : EStore} {vs : Array EIdx}
    (h : (Frontend.denoteEList st vs.toList).isSome = true) (hx : Ext st st') :
    (Frontend.denoteEList st' vs.toList).isSome = true := by
  obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp h
  rw [denoteEList_ext hx _ _ hxs]; rfl

/-! ### The same four, at the arm's OWN hypotheses

`Inst1.lean`'s group-7 finding, at this walk's one non-congruence arm: the
twin's `.bvar` clause reads the vector with a DEPENDENT array access
(`vs[vs.size - 1 - (j - d)]'h`) and dispatches on the TAG, so the four lemmas
above arrive one reversal and one `?`-vs-`'h` conversion away from what the
verification condition holds.  Doing both inside the lemma is what makes each
branch one `exact`. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:227 instantiateList — `InstLVec.get`
at the twin's own DEPENDENT array read. -/
theorem InstLVec.get' {st : EStore} {vs : Array EIdx} {ws : List Expr}
    {m : Nat} (h : InstLVec st vs ws) (hm : m < vs.size) :
    ∃ w, ws[m]? = some w ∧
      denoteE st (vs[vs.size - 1 - m]'(by omega)) = some w :=
  h.get hm (by rw [Array.getElem?_eq_getElem])

/-- con-leche: ConLeche/Kernel/ExprOps.lean:227 instantiateList — and the
replacement therefore denotes, which is what the recursion's precondition
asks. -/
theorem InstLVec.isSome_get {st : EStore} {vs : Array EIdx} {ws : List Expr}
    {m : Nat} (h : InstLVec st vs ws) (hm : m < vs.size) :
    (denoteE st (vs[vs.size - 1 - m]'(by omega))).isSome = true := by
  obtain ⟨w, _, hvi⟩ := h.get' hm
  rw [hvi]; rfl

/-- con-leche: ConLeche/Kernel/ExprOps.lean:227-228 instantiateList —
`InstLAt.bvar_cut` at the arm's own hypotheses. -/
theorem InstLAt.bvar_cutV {st : EStore} (hwf : StoreWF st) {c : EIdx}
    {vs : Array EIdx} {ws : List Expr} {d j : Nat}
    (hvec : InstLVec st vs ws) (htg : (c.tag == ETag.bvar) = true)
    (hvb : some j = st.viewBVar c) (hge : ¬ (j < d)) (hsz : j - d < vs.size)
    (hsat : (bvarOfData
      (st.derived (vs[vs.size - 1 - (j - d)]'(by omega)))).toNat < satRange)
    (hle : (bvarOfData
      (st.derived (vs[vs.size - 1 - (j - d)]'(by omega)))).toNat ≤ d) :
    InstLAt ws d st c st (vs[vs.size - 1 - (j - d)]'(by omega)) := by
  obtain ⟨w, hw, hvi⟩ := hvec.get' hsz
  exact InstLAt.bvar_cut hwf (view_of_viewBVar_tag htg hvb.symm) hge
    (by rw [hvec.length]; exact hsz) hw hvi hsat hle

/-- con-leche: ConLeche/Kernel/ExprOps.lean:228 instantiateList —
`InstLAt.bvar_rec` at the arm's own hypotheses. -/
theorem InstLAt.bvar_recV {st st' : EStore} (hwf : StoreWF st) {c r : EIdx}
    {vs : Array EIdx} {ws : List Expr} {d j : Nat}
    (hvec : InstLVec st vs ws) (htg : (c.tag == ETag.bvar) = true)
    (hvb : some j = st.viewBVar c) (hge : ¬ (j < d)) (hsz : j - d < vs.size)
    (hrec : InstLAt (ws.take (j - d)) d st
      (vs[vs.size - 1 - (j - d)]'(by omega)) st' r) :
    InstLAt ws d st c st' r := by
  obtain ⟨w, hw, hvi⟩ := hvec.get' hsz
  exact InstLAt.bvar_rec hwf (view_of_viewBVar_tag htg hvb.symm) hge
    (by rw [hvec.length]; exact hsz) hw hvi hrec

/-- con-leche: ConLeche/Kernel/ExprOps.lean:230 instantiateList —
`InstLAt.bvar_above` at the arm's own hypotheses: the vector's SIZE is the
list's length, through `InstLVec.length`. -/
theorem InstLAt.bvar_aboveV {st st' : EStore} (hwf : StoreWF st) {c r : EIdx}
    {vs : Array EIdx} {ws : List Expr} {d j : Nat}
    (hvec : InstLVec st vs ws) (htg : (c.tag == ETag.bvar) = true)
    (hvb : some j = st.viewBVar c) (hge : ¬ (j < d))
    (hsz : ¬ (j - d < vs.size))
    (hr : denoteE st' r = denoteEView st' (.bvar (j - vs.size))) :
    InstLAt ws d st c st' r :=
  InstLAt.bvar_above hwf (view_of_viewBVar_tag htg hvb.symm) hge hsz
    hvec.length hr

/-! ## I. `bvarB`'s Theorem 1, as the two con-leche cutoffs consume it

`lowerBVarsGo` and `instantiate1LiftGo` test con-leche's own `bvarB` — the
packed field, or the memoized recomputation on the saturated branch
(`Arena/ExprOps.lean:1486`).  **`bvarB` is not one of this file's thirteen
twins**: it belongs to the packed-range group.  Round 3 carried its Theorem 1
as a HYPOTHESIS so that `#print axioms` stayed clean while that group's file
was open; round 4 **discharged** it from `ExprOps/Ranges.lean`'s `bvarB_spec`
(`bvarB_bvarBSpec` below) and deleted the binders. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1429-1434 bvarB — Theorem 1 for
`bvarB`, in the shape the two cutoff walks need: the answer is
`Expr.bvarBound`, the store stands still, and the walks' own memo tables are
untouched (`bvarBoundMemo` clears only `bvarBC`). -/
structure BvarBSpec (prog : EIdx → AM Nat) : Prop where
  run : ∀ (s₁ : AState) (c : EIdx), StateOK s₁ →
    (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ prog c
    ⦃⇓? r s' => ⌜StateOK s' ∧ StoreWF s'.store ∧ s'.store = s₁.store ∧
        s'.caches = s₁.caches ∧
        s'.pins = s₁.pins ∧ s'.memos.lowerC = s₁.memos.lowerC ∧
        s'.memos.inst1LC = s₁.memos.inst1LC ∧
        RelV Expr.bvarBound s₁.store c r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1429-1434 bvarB — **`BvarBSpec`,
discharged**, from `ExprOps/Ranges.lean`'s `bvarB_spec`.

Two of `BvarBSpec`'s eight conjuncts are free of the packed-range group's own
statement: `StateOK s'` and `StoreWF s'.store` are `hok` transported along
`s'.store = s₁.store`, because `Bridge/StateOK.lean`'s `StateOK` is the single
field `StoreWF s.store`.  The other six have to BE `bvarB_spec`'s, and the two
memo-frame ones (`lowerC`, `inst1LC`) were the gap round 4 closed: `bvarB`
clears and refills `memos.bvarBC` and touches no other table, and the whole
chain (`bvarBClear_spec`, `bvarBSet_spec`) hands back a RECORD update
`{ memos with bvarBC := _ }`, so both conjuncts are a projection away —
but only once the two `Ranges.lean` statements say so. -/
theorem bvarB_bvarBSpec (fuel : Nat) : BvarBSpec (bvarB fuel) := by
  constructor
  intro s₁ c hok hden
  have hr := bvarB_spec fuel
  mvcgen [hr]
  all_goals bridge_vcs [RelV]

/-! ## J. Theorem 1 for `liftLooseBVars` -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:411-413 LiftMemoInv — **the memo
insert's spec, generic in the pure function**, and the finding this file owes
the next round.

`Bridge/Specs.lean`'s `liftSet_spec` takes `amount : Nat` as an ordinary
parameter, and `amount` appears nowhere in the program `liftSet k r`.  `mspec`
therefore has nothing to unify it against and **discharges the leftover
argument by searching the local context for a `Nat`** — which, inside
`liftLooseBVarsGo`'s arms, is the cutoff's own `bRaw` (and inside the `proj`
arm, the projection index).  The arm's two side goals then come out as
`LiftMemoA bRaw s` and `RelE (Expr.liftLooseBVars bRaw c) …`, which are false.
Two things fix it and one does not:

* making `amount` IMPLICIT does not (measured: the same search runs);
* passing a specialised `liftSet_spec s amount` in `mvcgen`'s list does not
  (the `@[spec]`-registered theorem wins);
* making the pure function the parameter does: `f : Nat → Expr → Expr` has no
  inhabitant in the arm's context, so `mvcgen` leaves it as a verification
  condition of type `Nat → Expr → Expr`, which the walk pins with one
  `exact fun cc e => Expr.liftLooseBVars amount cc e`.

`@[spec high]` is the other half: a spec registered later does NOT override an
earlier one for the same program, and the priority is what makes this one
win. -/
@[spec high] theorem liftSet_specG (s0 : AState) (f : Nat -> Expr -> Expr)
    (k : EIdx × Nat) (r : EIdx) (hm : MemoOK f s0.memos.liftC s0.store)
    (hk : (denoteE s0.store k.1).isSome = true)
    (hr : RelE (f k.2) s0.store k.1 s0.store r) :
    ⦃fun s => ⌜s = s0⌝⦄ liftSet k r
    ⦃⇓? _u s' => ⌜s'.store = s0.store ∧ s'.caches = s0.caches ∧
        s'.pins = s0.pins ∧
        s'.memos = { s0.memos with liftC := s0.memos.liftC.insert k r } ∧
        MemoOK f s'.memos.liftC s'.store⌝⦄ := by
  unfold liftSet
  mvcgen
  all_goals (bridge_peel; subst_vars)
  all_goals exact ⟨rfl, rfl, rfl, rfl, MemoOK.insert hm rfl hk hr⟩

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
    ⦃fun s => ⌜s = s₁⌝⦄ rec c cc
    ⦃⇓? r s' => ⌜StateOK s' ∧ LiftMemoA amount s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        s'.memos.inst1LC = s₁.memos.inst1LC ∧
        LiftAt amount cc s₁.store c s'.store r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:380-400 liftLooseBVars
con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo
**THEOREM 1 for `liftLooseBVars`**, at one level of the recursion, by
induction on the fuel.

DEVIATION (task #97f): the twin carries the derived-word cutoff `bvarBRaw <
satRange && bvarBRaw ≤ c`, which con-leche's `liftLooseBVarsGo` does not have.
Its licence is `liftLooseBVars_of_bvarBound_le` above — the `ExprOps.lean`
module note's `looseBVarsBounded c e → liftLooseBVars e c amount = e`, proved
by induction on `Expr` at `Expr.bvarBRaw_exact`'s guard.  Everything else is
clause for clause.

Unlike `instantiate1Go`, this walk dispatches on the whole `view`, so its ten
arms arrive with the node view in hand: no `_tag` lemma, no `viewBM` detour,
and therefore none of `Inst1.lean`'s binder-arm gaps. -/
theorem liftLooseBVarsGo_spec (amount : Nat) :
    ∀ fuel, LiftSpec amount (liftLooseBVarsGo amount fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h c _ _ _
    mvcgen [liftLooseBVarsGo_zero]
    all_goals bridge_vcs [Expr.liftLooseBVars]
  | succ fuel ih =>
    constructor
    intro s₀ h c hok hm hden
    have hrec := ih.run
    mvcgen [liftLooseBVarsGo_succ, liftArmApp, liftArmLam, liftArmForallE, liftArmLet, liftArmProj, hrec]
    all_goals try exact fun cc e => Expr.liftLooseBVars amount cc e
    all_goals try bridge_vcs [Expr.liftLooseBVars]
    -- the derived-word cutoff
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, hm, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
        LiftAt.cutoff hok.wf (by grind) (by grind)⟩
    -- `bvar`, the branch that interns the lifted index
    next =>
      bridge_peel
      subst_vars
      refine fun hwf2 hx _hbm _hlss hmem hcc hpp _hvw hrr => ?_
      exact ⟨⟨hwf2⟩, MemoOK.mono hm hx (by rw [hmem]), hx, _hbm, hcc, hpp,
        by rw [hmem], LiftAt.bvar_up hok.wf (by subst_hyp) (by subst_hyp) hrr⟩
    -- `bvar`, the branch below the cutoff
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, hm, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
        LiftAt.bvar_self hok.wf (by subst_hyp) (by subst_hyp)⟩
    -- the four leaves
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, hm, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
        RelE.leaf_view hok.wf (by subst_hyp) (fun _ hh => liftLooseBVars_leaf hh)
          (by grind)⟩
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, hm, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
        RelE.leaf_view hok.wf (by subst_hyp) (fun _ hh => liftLooseBVars_leaf hh)
          (by grind)⟩
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, hm, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
        RelE.leaf_view hok.wf (by subst_hyp) (fun _ hh => liftLooseBVars_leaf hh)
          (by grind)⟩
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, hm, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
        RelE.leaf_view hok.wf (by subst_hyp) (fun _ hh => liftLooseBVars_leaf hh)
          (by grind)⟩
    -- `app`: the memo insert's answer, then the arm's postcondition
    next =>
      bridge_peel
      subst_vars
      refine RelE.retarget ?_ ?_ hden
      · exact LiftAt.app_step hok.wf (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp)
      · grind only [Ext.trans]
    next =>
      bridge_peel
      subst_vars
      refine ⟨by grind only [StateOK, StateOK.mk], by subst_hyp,
        by grind only [Ext.trans], by grind only [BMExt.trans, BMExt.refl],
        by grind, by grind, by grind, ?_⟩
      exact LiftAt.app_step hok.wf (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp)
    -- `lam`: the memo insert's answer, then the arm's postcondition
    next =>
      bridge_peel
      subst_vars
      refine RelE.retarget ?_ ?_ hden
      · exact LiftAt.lam_step hok.wf (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp)
      · grind only [Ext.trans]
    next =>
      bridge_peel
      subst_vars
      refine ⟨by grind only [StateOK, StateOK.mk], by subst_hyp,
        by grind only [Ext.trans], by grind only [BMExt.trans, BMExt.refl],
        by grind, by grind, by grind, ?_⟩
      exact LiftAt.lam_step hok.wf (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp)
    -- `forallE`: the memo insert's answer, then the arm's postcondition
    next =>
      bridge_peel
      subst_vars
      refine RelE.retarget ?_ ?_ hden
      · exact LiftAt.forallE_step hok.wf (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp)
      · grind only [Ext.trans]
    next =>
      bridge_peel
      subst_vars
      refine ⟨by grind only [StateOK, StateOK.mk], by subst_hyp,
        by grind only [Ext.trans], by grind only [BMExt.trans, BMExt.refl],
        by grind, by grind, by grind, ?_⟩
      exact LiftAt.forallE_step hok.wf (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp)
    -- `letE`: the memo insert's answer, then the arm's postcondition
    next =>
      bridge_peel
      subst_vars
      refine RelE.retarget ?_ ?_ hden
      · exact LiftAt.letE_step hok.wf (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp)
      · grind only [Ext.trans]
    next =>
      bridge_peel
      subst_vars
      refine ⟨by grind only [StateOK, StateOK.mk], by subst_hyp,
        by grind only [Ext.trans], by grind only [BMExt.trans, BMExt.refl],
        by grind, by grind, by grind, ?_⟩
      exact LiftAt.letE_step hok.wf (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp)
    -- `proj`: the memo insert's answer, then the arm's postcondition
    next =>
      bridge_peel
      subst_vars
      obtain ⟨nm, es, _, hn0, _⟩ :=
        denote_eq_proj hok.wf (h := h) (by subst_hyp) hden
      refine RelE.retarget ?_ ?_ hden
      · exact LiftAt.proj_step hok.wf (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) hn0
      · grind only [Ext.trans]
    next =>
      bridge_peel
      subst_vars
      obtain ⟨nm, es, _, hn0, _⟩ :=
        denote_eq_proj hok.wf (h := h) (by subst_hyp) hden
      refine ⟨by grind only [StateOK, StateOK.mk], by subst_hyp,
        by grind only [Ext.trans], by grind only [BMExt.trans, BMExt.refl],
        by grind, by grind, by grind, ?_⟩
      exact LiftAt.proj_step hok.wf (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) hn0

/-- con-leche: ConLeche/Kernel/ExprOps.lean:532-534 liftLooseBVarsFast —
**THEOREM 1 for `liftLooseBVars`, at the entry point**: clear, walk, clear. -/
theorem liftLooseBVarsFast_spec (fuel amount c : Nat) (s₀ : AState) (e : EIdx)
    (hok : StateOK s₀) (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ liftLooseBVarsFast fuel amount c e
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.memos.liftC = ∅ ∧ s'.memos.inst1LC = s₀.memos.inst1LC ∧
        LiftAt amount c s₀.store e s'.store r⌝⦄ := by
  have hr := (liftLooseBVarsGo_spec amount fuel).run
  mvcgen [liftLooseBVarsFast, hr]
  all_goals bridge_vcs [Expr.liftLooseBVars]

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the same statement about
a RUN, which is the form the tier above consumes. -/
theorem liftLooseBVarsFast_run {fuel amount c : Nat} {s₀ s' : AState}
    {e r : EIdx} (hok : StateOK s₀)
    (hden : (denoteE s₀.store e).isSome = true)
    (hrun : (liftLooseBVarsFast fuel amount c e).run s₀ = Except.ok (r, s')) :
    StateOK s' ∧ Ext s₀.store s'.store ∧ BMExt s₀.store s'.store ∧
      s'.caches = s₀.caches ∧
      s'.pins = s₀.pins ∧ s'.memos.liftC = ∅ ∧
      s'.memos.inst1LC = s₀.memos.inst1LC ∧
      LiftAt amount c s₀.store e s'.store r :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    (liftLooseBVarsFast_spec fuel amount c s₀ e hok hden)

/-! ## K. Theorem 1 for `lowerBVars`, `instantiate1Lift` and `instPisAtLift` -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1995-1997 LowerMemoInv — the memo
insert's spec for `lowerC`, generic in the pure function (see
`liftSet_specG`). -/
@[spec high] theorem lowerSet_specG (s₀ : AState) (f : Nat → Expr → Expr)
    (k : EIdx × Nat) (r : EIdx) (hm : MemoOK f s₀.memos.lowerC s₀.store)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelE (f k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ lowerSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with lowerC := s₀.memos.lowerC.insert k r } ∧
        MemoOK f s'.memos.lowerC s'.store⌝⦄ := by
  unfold lowerSet
  mvcgen
  all_goals (bridge_peel; subst_vars)
  all_goals exact ⟨rfl, rfl, rfl, rfl, MemoOK.insert hm rfl hk hr⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2205-2207 Inst1LMemoInv — the memo
insert's spec for `inst1LC`, generic in the pure function (see
`liftSet_specG`). -/
@[spec high] theorem inst1LSet_specG (s₀ : AState) (f : Nat → Expr → Expr)
    (k : EIdx × Nat) (r : EIdx) (hm : MemoOK f s₀.memos.inst1LC s₀.store)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelE (f k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ inst1LSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with inst1LC := s₀.memos.inst1LC.insert k r } ∧
        MemoOK f s'.memos.inst1LC s'.store⌝⦄ := by
  unfold inst1LSet
  mvcgen
  all_goals (bridge_peel; subst_vars)
  all_goals exact ⟨rfl, rfl, rfl, rfl, MemoOK.insert hm rfl hk hr⟩

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `lowerBVarsGo`'s recursion. -/
structure LowerSpec (amount : Nat) (rec : EIdx → Nat → AM EIdx) : Prop where
  run : ∀ (s₁ : AState) (c : EIdx) (cc : Nat), StateOK s₁ →
    LowerMemoA amount s₁ → (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec c cc
    ⦃⇓? r s' => ⌜StateOK s' ∧ LowerMemoA amount s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        LowerAt amount cc s₁.store c s'.store r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:694-716 lowerBVars
con-leche: ConLeche/Kernel/ExprOps.lean:2014-2051 lowerBVarsGo
**THEOREM 1 for `lowerBVars`**, at one level of the recursion.

The cutoff is **con-leche's own** (`bvarB ≤ c + amount`), so its licence is
QUOTED and not reproved: `Expr.lowerBVars_of_bvarBound_le`
(`ConLeche/Kernel/ExprOps.lean:1959`), wrapped as `LowerAt.cutoff`.

`bvarB_bvarBSpec` is `bvarB`'s Theorem 1, quoted (round 3 carried it as a
hypothesis, because `bvarB` — `Arena/ExprOps.lean:1486` — is not one of this
file's thirteen twins; see `BvarBSpec` above).  Its one cost in the proof is
that every arm's `view` read happens at the state `bvarB` returned, whose
store is *equal to* but not syntactically `s₁.store`; `RelE.src_eq` /
`RelE.tgt_eq` and the view-first arm lemmas absorb that. -/
theorem lowerBVarsGo_spec (amount : Nat) :
    ∀ fuel, LowerSpec amount (lowerBVarsGo amount fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h c _ _ _
    mvcgen [lowerBVarsGo_zero]
    all_goals bridge_vcs [Expr.lowerBVars]
  | succ fuel ih =>
    constructor
    intro s₀ h c hok hm hden
    have hrec := ih.run
    have hbbr := (bvarB_bvarBSpec fuel).run
    mvcgen [lowerBVarsGo_succ, lowerArmApp, lowerArmLam, lowerArmForallE, lowerArmLet, lowerArmProj, hrec, hbbr]
    all_goals try exact fun cc e => Expr.lowerBVars amount cc e
    all_goals try bridge_vcs [Expr.lowerBVars]
    all_goals clear hbbr
    -- the `bvarB` cutoff, which is con-leche's own
    next =>
      bridge_peel
      subst_vars
      refine ⟨by subst_hyp, by grind only [MemoOK.mono, Ext.refl],
        by grind only [Ext.refl], by grind only [BMExt.trans, BMExt.refl],
        by grind, by grind, ?_⟩
      exact RelE.tgt_eq (by subst_hyp)
        (LowerAt.cutoff (by subst_hyp) (by subst_hyp))
    -- `bvar`, the branch that interns the lowered index
    next =>
      bridge_peel
      subst_vars
      refine fun hwf2 hx _hbm _hlss _hmem _hcc _hpp _hvw hrr => ?_
      refine ⟨⟨hwf2⟩, by grind only [MemoOK.mono, Ext.trans, Ext.refl],
        by grind only [Ext.trans, Ext.refl],
        by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp)
        (LowerAt.bvar_downV (by subst_hyp) (by subst_hyp) (by subst_hyp) hrr)
    -- `bvar`, inside the window
    next =>
      bridge_peel
      subst_vars
      refine ⟨by subst_hyp, by grind only [MemoOK.mono, Ext.refl],
        by grind only [Ext.refl], by grind only [BMExt.trans, BMExt.refl],
        by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp)
        (LowerAt.bvar_selfV (by subst_hyp) (by subst_hyp) (by subst_hyp))
    -- the four leaves
    next =>
      bridge_peel
      subst_vars
      refine ⟨by subst_hyp, by grind only [MemoOK.mono, Ext.refl],
        by grind only [Ext.refl], by grind only [BMExt.trans, BMExt.refl],
        by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp)
        (RelE.leaf_viewV (by subst_hyp) (by subst_hyp)
          (fun _ hh => lowerBVars_leaf hh) (by grind))
    next =>
      bridge_peel
      subst_vars
      refine ⟨by subst_hyp, by grind only [MemoOK.mono, Ext.refl],
        by grind only [Ext.refl], by grind only [BMExt.trans, BMExt.refl],
        by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp)
        (RelE.leaf_viewV (by subst_hyp) (by subst_hyp)
          (fun _ hh => lowerBVars_leaf hh) (by grind))
    next =>
      bridge_peel
      subst_vars
      refine ⟨by subst_hyp, by grind only [MemoOK.mono, Ext.refl],
        by grind only [Ext.refl], by grind only [BMExt.trans, BMExt.refl],
        by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp)
        (RelE.leaf_viewV (by subst_hyp) (by subst_hyp)
          (fun _ hh => lowerBVars_leaf hh) (by grind))
    next =>
      bridge_peel
      subst_vars
      refine ⟨by subst_hyp, by grind only [MemoOK.mono, Ext.refl],
        by grind only [Ext.refl], by grind only [BMExt.trans, BMExt.refl],
        by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp)
        (RelE.leaf_viewV (by subst_hyp) (by subst_hyp)
          (fun _ hh => lowerBVars_leaf hh) (by grind))
    next =>
      bridge_peel
      subst_vars
      exact RelE.retarget (LowerAt.app_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp))
        (by grind only [Ext.trans]) (by grind)
    next =>
      bridge_peel
      subst_vars
      refine ⟨by grind only [StateOK, StateOK.mk],
        by grind only [MemoOK.mono, Ext.trans, Ext.refl],
        by grind only [Ext.trans, Ext.refl],
        by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp) (LowerAt.app_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp))
    next =>
      bridge_peel
      subst_vars
      exact RelE.retarget (LowerAt.lam_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp))
        (by grind only [Ext.trans]) (by grind)
    next =>
      bridge_peel
      subst_vars
      refine ⟨by grind only [StateOK, StateOK.mk],
        by grind only [MemoOK.mono, Ext.trans, Ext.refl],
        by grind only [Ext.trans, Ext.refl],
        by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp) (LowerAt.lam_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp))
    next =>
      bridge_peel
      subst_vars
      exact RelE.retarget (LowerAt.forallE_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp))
        (by grind only [Ext.trans]) (by grind)
    next =>
      bridge_peel
      subst_vars
      refine ⟨by grind only [StateOK, StateOK.mk],
        by grind only [MemoOK.mono, Ext.trans, Ext.refl],
        by grind only [Ext.trans, Ext.refl],
        by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp) (LowerAt.forallE_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp))
    next =>
      bridge_peel
      subst_vars
      exact RelE.retarget (LowerAt.letE_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp))
        (by grind only [Ext.trans]) (by grind)
    next =>
      bridge_peel
      subst_vars
      refine ⟨by grind only [StateOK, StateOK.mk],
        by grind only [MemoOK.mono, Ext.trans, Ext.refl],
        by grind only [Ext.trans, Ext.refl],
        by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp) (LowerAt.letE_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp))
    next =>
      bridge_peel
      subst_vars
      obtain ⟨nm, es, _, hn0, _⟩ :=
        denote_eq_projV (h := h) (by subst_hyp) (by subst_hyp) (by grind)
      exact RelE.retarget (LowerAt.proj_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) hn0)
        (by grind only [Ext.trans]) (by grind)
    next =>
      bridge_peel
      subst_vars
      obtain ⟨nm, es, _, hn0, _⟩ :=
        denote_eq_projV (h := h) (by subst_hyp) (by subst_hyp) (by grind)
      refine ⟨by grind only [StateOK, StateOK.mk],
        by grind only [MemoOK.mono, Ext.trans, Ext.refl],
        by grind only [Ext.trans, Ext.refl],
        by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp) (LowerAt.proj_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) hn0)

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of `instantiate1LiftGo`'s recursion. -/
structure Inst1LSpec (v : EIdx) (ve : Expr) (rec : EIdx → Nat → AM EIdx) :
    Prop where
  run : ∀ (s₁ : AState) (c : EIdx) (dd : Nat), StateOK s₁ →
    Inst1LMemoA ve s₁ → denoteE s₁.store v = some ve →
    (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ Inst1LMemoA ve s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        Inst1LAt ve dd s₁.store c s'.store r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:718-739 instantiate1Lift
con-leche: ConLeche/Kernel/ExprOps.lean:2224-2263 instantiate1LiftGo
**THEOREM 1 for `instantiate1Lift`**, at one level of the recursion.

Two things make this the most interesting walk of the group:

1. the cutoff is again **con-leche's own** (`bvarB ≤ d`), quoted from
   `Expr.instantiate1Lift_of_bvarBound_le` (`ExprOps.lean:2169`) and wrapped
   as `Inst1LAt.cutoff`;
2. it is the module's one **nested** walk: the `.bvar` arm at `i = d` answers
   `liftLooseBVarsFast fuel d 0 v`, so the proof consumes
   `liftLooseBVarsFast_spec` and needs its `inst1LC` frame conjunct to carry
   `Inst1LMemoA ve` across the nested call. -/
theorem instantiate1LiftGo_spec (v : EIdx) (ve : Expr) :
    ∀ fuel, Inst1LSpec v ve (instantiate1LiftGo v fuel) := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    intro s₀ h d _ _ _ _
    mvcgen [instantiate1LiftGo_zero]
    all_goals bridge_vcs [Expr.instantiate1Lift]
  | succ fuel ih =>
    constructor
    intro s₀ h d hok hm hv hden
    have hrec := ih.run
    have hbbr := (bvarB_bvarBSpec fuel).run
    have hlift := fun (s : AState) (e : EIdx) => liftLooseBVarsFast_spec fuel d 0 s e
    mvcgen [instantiate1LiftGo_succ, inst1LiftArmApp, inst1LiftArmLam, inst1LiftArmForallE, inst1LiftArmLet, inst1LiftArmProj, hrec, hbbr, hlift]
    all_goals try exact fun dd e => Expr.instantiate1Lift e ve dd
    all_goals try bridge_vcs [Expr.instantiate1Lift]
    all_goals clear hbbr hlift
    -- the `bvarB` cutoff, which is con-leche's own
    next =>
      bridge_peel
      subst_vars
      refine ⟨by subst_hyp, by grind only [MemoOK.mono, Ext.refl],
        by grind only [Ext.refl], by grind only [BMExt.trans, BMExt.refl],
        by grind, by grind, ?_⟩
      exact RelE.tgt_eq (by subst_hyp)
        (Inst1LAt.cutoff (by subst_hyp) (by subst_hyp))
    -- `bvar`, the SUBSTITUTING branch: the nested `liftLooseBVarsFast`
    next =>
      bridge_peel
      subst_vars
      refine fun hok2 hx _hbm2 _hcc _hpp _hlc _hilc hans => ?_
      refine ⟨hok2, by grind only [MemoOK.mono, Ext.trans, Ext.refl],
        by grind only [Ext.trans, Ext.refl],
        by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp)
        (Inst1LAt.bvar_substV (by subst_hyp) (by subst_hyp) (by subst_hyp)
          (hans ve (by grind)))
    -- `bvar`, the branch that interns the lowered index
    next =>
      bridge_peel
      subst_vars
      refine fun hwf2 hx _hbm _hlss _hmem _hcc _hpp _hvw hrr => ?_
      refine ⟨⟨hwf2⟩, by grind only [MemoOK.mono, Ext.trans, Ext.refl],
        by grind only [Ext.trans, Ext.refl],
        by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp)
        (Inst1LAt.bvar_downV (by subst_hyp) (by subst_hyp) (by subst_hyp)
          (by subst_hyp) hrr)
    -- `bvar`, below the cursor
    next =>
      bridge_peel
      subst_vars
      refine ⟨by subst_hyp, by grind only [MemoOK.mono, Ext.refl],
        by grind only [Ext.refl], by grind only [BMExt.trans, BMExt.refl],
        by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp)
        (Inst1LAt.bvar_selfV (by subst_hyp) (by subst_hyp) (by subst_hyp)
          (by subst_hyp))
    -- the four leaves
    next =>
      bridge_peel
      subst_vars
      refine ⟨by subst_hyp, by grind only [MemoOK.mono, Ext.refl],
        by grind only [Ext.refl], by grind only [BMExt.trans, BMExt.refl],
        by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp)
        (RelE.leaf_viewV (by subst_hyp) (by subst_hyp)
          (fun _ hh => instantiate1Lift_leaf hh) (by grind))
    next =>
      bridge_peel
      subst_vars
      refine ⟨by subst_hyp, by grind only [MemoOK.mono, Ext.refl],
        by grind only [Ext.refl], by grind only [BMExt.trans, BMExt.refl],
        by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp)
        (RelE.leaf_viewV (by subst_hyp) (by subst_hyp)
          (fun _ hh => instantiate1Lift_leaf hh) (by grind))
    next =>
      bridge_peel
      subst_vars
      refine ⟨by subst_hyp, by grind only [MemoOK.mono, Ext.refl],
        by grind only [Ext.refl], by grind only [BMExt.trans, BMExt.refl],
        by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp)
        (RelE.leaf_viewV (by subst_hyp) (by subst_hyp)
          (fun _ hh => instantiate1Lift_leaf hh) (by grind))
    next =>
      bridge_peel
      subst_vars
      refine ⟨by subst_hyp, by grind only [MemoOK.mono, Ext.refl],
        by grind only [Ext.refl], by grind only [BMExt.trans, BMExt.refl],
        by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp)
        (RelE.leaf_viewV (by subst_hyp) (by subst_hyp)
          (fun _ hh => instantiate1Lift_leaf hh) (by grind))
    next =>
      bridge_peel
      subst_vars
      exact RelE.retarget (Inst1LAt.app_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp))
        (by grind only [Ext.trans]) (by grind)
    next =>
      bridge_peel
      subst_vars
      refine ⟨by grind only [StateOK, StateOK.mk],
        by grind only [MemoOK.mono, Ext.trans, Ext.refl],
        by grind only [Ext.trans, Ext.refl],
        by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp) (Inst1LAt.app_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp))
    next =>
      bridge_peel
      subst_vars
      exact RelE.retarget (Inst1LAt.lam_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp))
        (by grind only [Ext.trans]) (by grind)
    next =>
      bridge_peel
      subst_vars
      refine ⟨by grind only [StateOK, StateOK.mk],
        by grind only [MemoOK.mono, Ext.trans, Ext.refl],
        by grind only [Ext.trans, Ext.refl],
        by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp) (Inst1LAt.lam_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp))
    next =>
      bridge_peel
      subst_vars
      exact RelE.retarget (Inst1LAt.forallE_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp))
        (by grind only [Ext.trans]) (by grind)
    next =>
      bridge_peel
      subst_vars
      refine ⟨by grind only [StateOK, StateOK.mk],
        by grind only [MemoOK.mono, Ext.trans, Ext.refl],
        by grind only [Ext.trans, Ext.refl],
        by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp) (Inst1LAt.forallE_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp))
    next =>
      bridge_peel
      subst_vars
      exact RelE.retarget (Inst1LAt.letE_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp))
        (by grind only [Ext.trans]) (by grind)
    next =>
      bridge_peel
      subst_vars
      refine ⟨by grind only [StateOK, StateOK.mk],
        by grind only [MemoOK.mono, Ext.trans, Ext.refl],
        by grind only [Ext.trans, Ext.refl],
        by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp) (Inst1LAt.letE_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp))
    next =>
      bridge_peel
      subst_vars
      obtain ⟨nm, es, _, hn0, _⟩ :=
        denote_eq_projV (h := h) (by subst_hyp) (by subst_hyp) (by grind)
      exact RelE.retarget (Inst1LAt.proj_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) hn0)
        (by grind only [Ext.trans]) (by grind)
    next =>
      bridge_peel
      subst_vars
      obtain ⟨nm, es, _, hn0, _⟩ :=
        denote_eq_projV (h := h) (by subst_hyp) (by subst_hyp) (by grind)
      refine ⟨by grind only [StateOK, StateOK.mk],
        by grind only [MemoOK.mono, Ext.trans, Ext.refl],
        by grind only [Ext.trans, Ext.refl],
        by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
      exact RelE.src_eq (by subst_hyp) (Inst1LAt.proj_stepV (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) hn0)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2146-2148 lowerBVarsFast —
**THEOREM 1 for `lowerBVars`, at the entry point**. -/
theorem lowerBVarsFast_spec (fuel amount c : Nat) (s₀ : AState) (e : EIdx)
    (hok : StateOK s₀)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ lowerBVarsFast fuel amount c e
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.memos.lowerC = ∅ ∧ LowerAt amount c s₀.store e s'.store r⌝⦄ := by
  have hr := (lowerBVarsGo_spec amount fuel).run
  mvcgen [lowerBVarsFast, hr]
  all_goals bridge_vcs [Expr.lowerBVars]

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the same statement about
a RUN. -/
theorem lowerBVarsFast_run {fuel amount c : Nat} {s₀ s' : AState} {e r : EIdx}
    (hok : StateOK s₀)
    (hden : (denoteE s₀.store e).isSome = true)
    (hrun : (lowerBVarsFast fuel amount c e).run s₀ = Except.ok (r, s')) :
    StateOK s' ∧ Ext s₀.store s'.store ∧ BMExt s₀.store s'.store ∧
      s'.caches = s₀.caches ∧
      s'.pins = s₀.pins ∧ s'.memos.lowerC = ∅ ∧
      LowerAt amount c s₀.store e s'.store r :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    (lowerBVarsFast_spec fuel amount c s₀ e hok hden)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2358-2360 instantiate1LiftFast —
**THEOREM 1 for `instantiate1Lift`, at the entry point**. -/
theorem instantiate1LiftFast_spec (fuel : Nat) (s₀ : AState) (e v : EIdx)
    (d : Nat) (ve : Expr) (hok : StateOK s₀)
    (hv : denoteE s₀.store v = some ve)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ instantiate1LiftFast fuel e v d
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.memos.inst1LC = ∅ ∧ Inst1LAt ve d s₀.store e s'.store r⌝⦄ := by
  have hr := (instantiate1LiftGo_spec v ve fuel).run
  mvcgen [instantiate1LiftFast, hr]
  all_goals bridge_vcs [Expr.instantiate1Lift]

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the same statement about
a RUN. -/
theorem instantiate1LiftFast_run {fuel : Nat} {s₀ s' : AState} {e v r : EIdx}
    {d : Nat} {ve : Expr} (hok : StateOK s₀)
    (hv : denoteE s₀.store v = some ve)
    (hden : (denoteE s₀.store e).isSome = true)
    (hrun : (instantiate1LiftFast fuel e v d).run s₀ = Except.ok (r, s')) :
    StateOK s' ∧ Ext s₀.store s'.store ∧ BMExt s₀.store s'.store ∧
      s'.caches = s₀.caches ∧
      s'.pins = s₀.pins ∧ s'.memos.inst1LC = ∅ ∧
      Inst1LAt ve d s₀.store e s'.store r :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    (instantiate1LiftFast_spec fuel s₀ e v d ve hok hv hden)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2377-2380 instPisAtLift — the
`cons` STEP: a `∀`-head is peeled, its body instantiated at the argument by
the nested `instantiate1LiftFast`, and the rest of the list consumed by the
recursion.  Stated as one lemma so that the walk's one structural
verification condition is a single `exact`. -/
theorem RelEO.instPisAtLift_cons {st s1 s2 : EStore} {c ty body r1 : EIdx}
    {m : BinderMeta} {r : Option EIdx} {ea : Expr} {eas : List Expr}
    (hwf : StoreWF st) (hview : st.view c = some (.forallE ty body m))
    (h1 : Inst1LAt ea 0 st body s1 r1)
    (h2 : RelEO (fun e => Expr.instPisAtLift eas e) s1 r1 s2 r) :
    RelEO (fun e => Expr.instPisAtLift (ea :: eas) e) st c s2 r := by
  intro e he
  obtain ⟨et, eb, rfl, _hdt, hdb⟩ := denote_forallE_inv hwf hview he
  exact h2 _ (h1 eb hdb)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2380 instPisAtLift — the `cons`
step at a NON-`∀` head: con-leche's own catch-all clause answers `none`, and
so does the twin. -/
theorem RelEO.instPisAtLift_none {st st' : EStore} (hwf : StoreWF st)
    {c : EIdx} {vw : ENodeView} (hview : st.view c = some vw)
    (hne : ∀ ty b m, vw ≠ .forallE ty b m) {ea : Expr} {eas : List Expr} :
    RelEO (fun e => Expr.instPisAtLift (ea :: eas) e) st c st' none := by
  intro e he
  rw [denoteE_view_eq hwf hview] at he
  show denoteEO st' none = some (Expr.instPisAtLift (ea :: eas) e)
  cases vw <;>
    simp_all only [denoteEView, denoteEO, ne_eq, reduceCtorEq, not_false_eq_true,
      forall_const, Option.map_eq_some_iff, opt2_eq_some_iff,
      opt3_eq_some_iff] <;>
    grind [Expr.instPisAtLift]

/-- con-leche: ConLeche/Kernel/ExprOps.lean:2367-2380 instPisAtLift —
**THEOREM 1 for `instPisAtLift`**: instantiate the leading `∀`-binders at
*open* arguments.  The answer is an OPTION of a handle, so the relation is
`Bridge/Rel.lean`'s `RelEO` (`none` is `none`: a non-`∀` head is a failure of
the pure function too, not of the monad).

The recursion is on the argument LIST, not on fuel, so there is no fuel
induction; the fuel is `instantiate1LiftFast`'s.  The argument list's
denotation sits in the POSTCONDITION (`∀ xs, denoteEList … = some xs → …`)
rather than as a parameter, for the reason `liftSet_specG` documents: a
`List Expr` parameter that the program does not mention is filled in by
`mvcgen`'s context search. -/
theorem instPisAtLift_spec (fuel : Nat) :
    ∀ (args : List EIdx) (s₀ : AState) (c : EIdx), StateOK s₀ →
      (Frontend.denoteEList s₀.store args).isSome = true →
      (denoteE s₀.store c).isSome = true →
      ⦃fun s => ⌜s = s₀⌝⦄ instPisAtLift fuel args c
      ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
          BMExt s₀.store s'.store ∧
          s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
          ∀ xs, Frontend.denoteEList s₀.store args = some xs →
            RelEO (fun e => Expr.instPisAtLift xs e) s₀.store c s'.store r⌝⦄ := by
  intro args
  induction args with
  | nil =>
    intro s₀ c hok _ hden
    mvcgen [instPisAtLift]
    all_goals bridge_vcs [Expr.instPisAtLift, RelEO, denoteEO,
      Frontend.denoteEList]
  | cons a as ih =>
    intro s₀ c hok hargs hden
    have hrec := ih
    obtain ⟨xs0, hxs0⟩ := Option.isSome_iff_exists.mp hargs
    simp only [Frontend.denoteEList] at hxs0
    split at hxs0
    · rename_i ea eas hea heas
      have hil := fun (s : AState) (e : EIdx) =>
        instantiate1LiftFast_spec fuel s e a 0 ea
      mvcgen [instPisAtLift, hrec, hil]
      all_goals try bridge_vcs [Expr.instPisAtLift, RelEO, denoteEO,
        Frontend.denoteEList]
      -- THREE verification conditions survive the closer: the `cons` step's
      -- own postcondition, the recursive call's `denoteEList` precondition at
      -- the store the nested lift left behind, and the non-`∀` head.
      next =>
        bridge_peel
        subst_vars
        intro hok2 hx2 hbm2 hcc hpp hans
        refine ⟨hok2, by grind only [Ext.trans],
          by grind only [BMExt.trans, BMExt.refl], by grind, by grind, ?_⟩
        intro xs hxs
        simp only [Frontend.denoteEList, hea, heas] at hxs
        obtain rfl := Option.some.inj hxs
        refine RelEO.instPisAtLift_cons hok.wf (by subst_hyp) (by subst_hyp) ?_
        exact hans _ (denoteEList_ext (by subst_hyp) _ _ heas)
      next =>
        bridge_peel
        subst_vars
        intro _ _ hx2 _ _ _ _ _
        rw [denoteEList_ext hx2 _ _ heas]
        rfl
      next =>
        bridge_peel
        subst_vars
        refine ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, ?_⟩
        intro xs hxs
        simp only [Frontend.denoteEList, hea, heas] at hxs
        obtain rfl := Option.some.inj hxs
        exact RelEO.instPisAtLift_none hok.wf (by assumption) (by assumption)
    · exact absurd hxs0 (by simp)

/-! ## L. Theorem 1 for `instantiateList` -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:248-250 InstLMemoInv — the memo
insert's spec for `instLC`, generic in the pure function (see
`liftSet_specG`). -/
@[spec high] theorem instLSet_specG (s₀ : AState) (f : Nat → Expr → Expr)
    (k : EIdx × Nat) (r : EIdx) (hm : MemoOK f s₀.memos.instLC s₀.store)
    (hk : (denoteE s₀.store k.1).isSome = true)
    (hr : RelE (f k.2) s₀.store k.1 s₀.store r) :
    ⦃fun s => ⌜s = s₀⌝⦄ instLSet k r
    ⦃⇓? _u s' => ⌜s'.store = s₀.store ∧ s'.caches = s₀.caches ∧
        s'.pins = s₀.pins ∧
        s'.memos = { s₀.memos with instLC := s₀.memos.instLC.insert k r } ∧
        MemoOK f s'.memos.instLC s'.store⌝⦄ := by
  unfold instLSet
  mvcgen
  all_goals (bridge_peel; subst_vars)
  all_goals exact ⟨rfl, rfl, rfl, rfl, MemoOK.insert hm rfl hk hr⟩

/-! ### The three `Array` twins at the DENOTATION -/

/-- con-leche: none — **Theorem 1 for `takeEidx` at the denotation**: the
first `k` slots of a denoting handle vector denote the first `k` terms.  This
is the list fact the substituting walks consume. -/
theorem denoteEList_takeEidx {st : EStore} {xs : Array EIdx} {es : List Expr}
    (h : Frontend.denoteEList st xs.toList = some es) (k : Nat) :
    Frontend.denoteEList st (takeEidx xs k).toList = some (es.take k) := by
  rw [takeEidx_toList]
  exact denoteEList_take k xs.toList es h

/-- con-leche: none — **Theorem 1 for `lastEidx` at the denotation**: the LAST
`k` slots of a denoting handle vector denote the last `k` terms.  Through
`InstLVec`'s reversal this is `List.take k` on the pure walk's list
(`InstLVec.last`), which is what con-leche's `vs.take (j - d)` is. -/
theorem denoteEList_lastEidx {st : EStore} {xs : Array EIdx} {es : List Expr}
    (h : Frontend.denoteEList st xs.toList = some es) (k : Nat) :
    Frontend.denoteEList st (lastEidx xs k).toList
      = some (es.drop (es.length - k)) := by
  rw [lastEidx_toList, denoteEList_length xs.toList es h]
  exact denoteEList_drop _ xs.toList es h

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

`BMExt` (task #97-P3-1, `Bridge/StoreBM.lean`) is the binder-datum store's own
extension, which `Ext` cannot say because a `BMIdx` denotes nothing; it is
what closes the binder arm, whose `internBindIE` precondition is asked at the
store the two recursive calls left behind. -/
structure InstLPureSpec (vs : Array EIdx) (ws : List Expr)
    (rec : EIdx → Nat → AM EIdx) : Prop where
  run : ∀ (s₁ : AState) (c : EIdx) (dd : Nat), StateOK s₁ →
    InstLVec s₁.store vs ws → (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧ s'.memos = s₁.memos ∧
        InstLAt ws dd s₁.store c s'.store r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList — the
`app` ARM: project, recurse into both children, rebuild. -/
theorem instListArmApp_spec (vs : Array EIdx) (ws : List Expr) (fuel : Nat)
    (ih : InstLPureSpec vs ws (instantiateList vs fuel)) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hvec : InstLVec s₁.store vs ws)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.app) = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ instListArmApp vs fuel c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧ s'.memos = s₁.memos ∧
        InstLAt ws dd s₁.store c s'.store r⌝⦄ := by
  have hrec := ih.run
  mvcgen [instListArmApp, hrec]
  all_goals try bridge_vcs [Expr.instantiateList, InstLVec.ext, InstLVec.length]
  -- ONE verification condition survives: `internAppE`'s postcondition, which
  -- arrives as an implication chain because the intern is the arm's ANSWER
  -- (there is no memo insert behind it — this is the unmemoized walk).
  next =>
    refine fun hwf2 hx _hbx _hlss _hmm _hcc _hpp _hvw hrr => ?_
    bridge_peel
    subst_vars
    refine ⟨⟨hwf2⟩, by grind only [Ext.trans],
      by grind only [BMExt.trans, BMExt.refl], by grind, by grind, by grind, ?_⟩
    exact InstLAt.app_step hok.wf (by subst_hyp) (by subst_hyp) (by subst_hyp)
      (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) hrr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList — the
BINDER ARM (`lam` and `forallE` in one, as the tag dispatch tests them).  The
datum survives the two recursive calls by `BMExt` (task #97-P3-1). -/
theorem instListArmBind_spec (vs : Array EIdx) (ws : List Expr) (fuel : Nat)
    (ih : InstLPureSpec vs ws (instantiateList vs fuel)) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hvec : InstLVec s₁.store vs ws)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : ETag.isBind c.tag = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ instListArmBind vs fuel c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧ s'.memos = s₁.memos ∧
        InstLAt ws dd s₁.store c s'.store r⌝⦄ := by
  have hrec := ih.run
  mvcgen [instListArmBind, hrec]
  all_goals try bridge_vcs [Expr.instantiateList, InstLVec.ext, InstLVec.length]
  -- the two recursive calls' subjects denote
  next =>
    bridge_peel
    subst_vars
    obtain ⟨mm, _hbm, _, hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by subst_hyp)
    exact (isSome_eBindView hok.wf hvw hden).1
  next =>
    bridge_peel
    subst_vars
    obtain ⟨mm, _hbm, _, hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by subst_hyp)
    have h2 := isSome_eBindView hok.wf hvw hden
    grind
  -- the arm's postcondition, through `internBindIE`'s answer
  next =>
    refine fun hwf2 hx _hbx _hlss _hscr _hmm _hcc _hpp hans => ?_
    bridge_peel
    subst_vars
    obtain ⟨mm, hbm, _htag0, _hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by subst_hyp)
    refine ⟨⟨hwf2⟩, by grind only [Ext.trans],
      by grind only [BMExt.trans, BMExt.refl], by grind, by grind, by grind, ?_⟩
    refine InstLAt.bind_step' hok.wf htg rfl (by subst_hyp) hbm
      (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp)
      (by subst_hyp) ?_
    grind
  -- `internBindIE`'s three side conditions.  The datum survives the two
  -- recursive calls by `BMExt` — the conjunct `Bridge/StoreBM.lean` exists
  -- for, and the reason task #97-P3-0 left this arm open.
  next =>
    bridge_peel
    subst_vars
    obtain ⟨mm, hbm, _htag0, _hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by subst_hyp)
    grind [BMExt.get]
  next =>
    bridge_peel
    subst_vars
    obtain ⟨mm, _hbm, _, hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by subst_hyp)
    have h2 := isSome_eBindView hok.wf hvw hden
    refine fun s _ _ _ _ _ _ _ => ?_
    exact view_isSome (by grind)
  next =>
    bridge_peel
    subst_vars
    obtain ⟨mm, _hbm, _, hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by subst_hyp)
    have h2 := isSome_eBindView hok.wf hvw hden
    refine fun s _ _ _ _ _ _ _ => ?_
    exact view_isSome (by grind)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList — the
`letE` ARM; the body descends at `dd + 1`. -/
theorem instListArmLet_spec (vs : Array EIdx) (ws : List Expr) (fuel : Nat)
    (ih : InstLPureSpec vs ws (instantiateList vs fuel)) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hvec : InstLVec s₁.store vs ws)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.letE) = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ instListArmLet vs fuel c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧ s'.memos = s₁.memos ∧
        InstLAt ws dd s₁.store c s'.store r⌝⦄ := by
  have hrec := ih.run
  mvcgen [instListArmLet, hrec]
  all_goals try bridge_vcs [Expr.instantiateList, InstLVec.ext, InstLVec.length]
  next =>
    refine fun hwf2 hx _hbx _hlss _hmm _hcc _hpp _hvw hrr => ?_
    bridge_peel
    subst_vars
    refine ⟨⟨hwf2⟩, by grind only [Ext.trans],
      by grind only [BMExt.trans, BMExt.refl], by grind, by grind, by grind, ?_⟩
    exact InstLAt.letE_step hok.wf (by subst_hyp) (by subst_hyp) (by subst_hyp)
      (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp)
      (by subst_hyp) (by subst_hyp) hrr

/-- con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList — the
`proj` ARM.  The struct NAME is carried unchanged, and its denotation comes
from `denote_eq_proj`'s existential, which `grind` cannot see through. -/
theorem instListArmProj_spec (vs : Array EIdx) (ws : List Expr) (fuel : Nat)
    (ih : InstLPureSpec vs ws (instantiateList vs fuel)) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hvec : InstLVec s₁.store vs ws)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.proj) = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ instListArmProj vs fuel c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧ s'.memos = s₁.memos ∧
        InstLAt ws dd s₁.store c s'.store r⌝⦄ := by
  have hrec := ih.run
  mvcgen [instListArmProj, hrec]
  all_goals try bridge_vcs [Expr.instantiateList, InstLVec.ext, InstLVec.length]
  next =>
    refine fun hwf2 hx _hbx _hlss _hmm _hcc _hpp _hvw hrr => ?_
    bridge_peel
    subst_vars
    obtain ⟨nm, es, _, hn0, _⟩ :=
      denote_eq_proj hok.wf (h := c)
        (view_of_viewProj_tag htg (by subst_hyp)) hden
    refine ⟨⟨hwf2⟩, by grind only [Ext.trans],
      by grind only [BMExt.trans, BMExt.refl], by grind, by grind, by grind, ?_⟩
    exact InstLAt.proj_step hok.wf (by subst_hyp) (by subst_hyp) (by subst_hyp)
      (by subst_hyp) (by subst_hyp) hrr hn0

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
    ⦃fun s => ⌜s = s₁⌝⦄ instListArmBVar vs fuel c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧ s'.memos = s₁.memos ∧
        InstLAt ws dd s₁.store c s'.store r⌝⦄ := by
  have hrec := fun (m : Nat) => (ih m).run
  mvcgen [instListArmBVar, hrec]
  all_goals try bridge_vcs [Expr.instantiateList, InstLVec.last,
    InstLVec.ext, InstLVec.length]
  -- `j < d`: a bound variable of the term itself.
  next =>
    bridge_peel
    subst_vars
    exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
      InstLAt.bvar_below hok.wf
        (view_of_viewBVar_tag (by subst_hyp) (by subst_hyp)) (by subst_hyp)⟩
  -- in range, the twin's HOISTED cutoff firing at the replacement.
  next =>
    bridge_peel
    subst_vars
    exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
      InstLAt.bvar_cutV hok.wf hvec htg (by subst_hyp) (by subst_hyp)
        (by subst_hyp) (by grind) (by grind)⟩
  -- in range, con-leche's own recursion into the replacement at the SHORTER
  -- vector.
  next =>
    refine fun hok2 hx hbx hcc hpp hmm hans => ?_
    bridge_peel
    subst_vars
    exact ⟨hok2, hx, hbx, hcc, hpp, hmm,
      InstLAt.bvar_recV hok.wf hvec htg (by subst_hyp) (by subst_hyp)
        (by subst_hyp) hans⟩
  -- that recursion's subject denotes.
  next =>
    refine fun s hs _ => ?_
    subst hs
    bridge_peel
    subst_vars
    exact InstLVec.isSome_get hvec (by subst_hyp)
  -- out of range: the index drops by the vector's length.
  next =>
    refine fun hwf2 hx hbx _hlss _hmm _hcc _hpp _hvw hrr => ?_
    bridge_peel
    subst_vars
    refine ⟨⟨hwf2⟩, by grind only [Ext.trans],
      by grind only [BMExt.trans, BMExt.refl], by grind, by grind, by grind, ?_⟩
    exact InstLAt.bvar_aboveV hok.wf hvec htg (by subst_hyp) (by subst_hyp)
      (by subst_hyp) hrr

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
    mvcgen [instantiateList_zero]
    all_goals bridge_vcs [Expr.instantiateList]
  | succ fuel ih =>
    intro vs ws
    constructor
    intro s₀ h d hok hvec hden
    have happ := instListArmApp_spec vs ws fuel (ih vs ws)
    have hbind := instListArmBind_spec vs ws fuel (ih vs ws)
    have hlet := instListArmLet_spec vs ws fuel (ih vs ws)
    have hproj := instListArmProj_spec vs ws fuel (ih vs ws)
    have hbvar := instListArmBVar_spec vs ws fuel
      (fun m => ih (lastEidx vs m) (ws.take m))
    mvcgen [instantiateList_succ, happ, hbind, hbvar, hlet, hproj]
    all_goals try bridge_vcs [Expr.instantiateList]
    -- TWO verification conditions survive the closer: the derived-word cutoff
    -- and the catch-all leaf.
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
        InstLAt.cutoff hok.wf (by grind) (by grind)⟩
    next =>
      bridge_peel
      subst_vars
      obtain ⟨e0, he0⟩ := Option.isSome_iff_exists.mp hden
      obtain ⟨vw, hvw⟩ := denoteE_view he0
      exact ⟨hok, Ext.refl _, BMExt.refl _, rfl, rfl, rfl,
        InstLAt.leaf hok.wf hvw (by grind) (by grind) (by grind) (by grind)
          (by grind)⟩

/-! ### `instantiateListGo`, the memoized walk -/

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — Theorem 1's statement for
one level of the MEMOIZED `instantiateListGo`'s recursion.  The memo table is
keyed for ONE substitution list (`InstLMemoA ws`) and this walk never shortens
it — the shortening `.bvar` arm is the unmemoized walk, called by name — so
the record carries the invariant where the pure walk carries a memo frame.
`BMExt` is here for the binder arm, exactly as in `InstLPureSpec`. -/
structure InstLSpec (vs : Array EIdx) (ws : List Expr)
    (rec : EIdx → Nat → AM EIdx) : Prop where
  run : ∀ (s₁ : AState) (c : EIdx) (dd : Nat), StateOK s₁ → InstLMemoA ws s₁ →
    InstLVec s₁.store vs ws → (denoteE s₁.store c).isSome = true →
    ⦃fun s => ⌜s = s₁⌝⦄ rec c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ InstLMemoA ws s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        InstLAt ws dd s₁.store c s'.store r⌝⦄

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
`app` ARM: probe, project, recurse into both children, rebuild, insert. -/
theorem instListGoArmApp_spec (vs : Array EIdx) (ws : List Expr) (fuel : Nat)
    (ih : InstLSpec vs ws (instantiateListGo vs fuel)) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hm : InstLMemoA ws s₁)
    (hvec : InstLVec s₁.store vs ws)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.app) = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ instListGoArmApp vs fuel c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ InstLMemoA ws s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        InstLAt ws dd s₁.store c s'.store r⌝⦄ := by
  have hrec := ih.run
  mvcgen [instListGoArmApp, hrec]
  all_goals try exact fun dd e => Expr.instantiateList e ws dd
  all_goals try bridge_vcs [Expr.instantiateList, InstLVec.ext, InstLVec.length]
  -- the memo insert's answer, then the arm's postcondition
  next =>
    bridge_peel
    subst_vars
    refine RelE.retarget ?_ ?_ hden
    · exact InstLAt.app_step hok.wf (by subst_hyp) (by subst_hyp)
        (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp)
        (by subst_hyp) (by subst_hyp)
    · grind only [Ext.trans]
  next =>
    bridge_peel
    subst_vars
    refine ⟨by grind only [StateOK, StateOK.mk], by subst_hyp,
      by grind only [Ext.trans], by grind only [BMExt.trans, BMExt.refl],
      by grind, by grind, ?_⟩
    exact InstLAt.app_step hok.wf (by subst_hyp) (by subst_hyp) (by subst_hyp)
      (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp)
      (by subst_hyp)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
BINDER ARM, the one `BMExt` exists for (task #97-P3-1). -/
theorem instListGoArmBind_spec (vs : Array EIdx) (ws : List Expr) (fuel : Nat)
    (ih : InstLSpec vs ws (instantiateListGo vs fuel)) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hm : InstLMemoA ws s₁)
    (hvec : InstLVec s₁.store vs ws)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : ETag.isBind c.tag = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ instListGoArmBind vs fuel c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ InstLMemoA ws s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        InstLAt ws dd s₁.store c s'.store r⌝⦄ := by
  have hrec := ih.run
  mvcgen [instListGoArmBind, hrec]
  all_goals try exact fun dd e => Expr.instantiateList e ws dd
  all_goals try bridge_vcs [Expr.instantiateList, InstLVec.ext, InstLVec.length]
  -- the two recursive calls' subjects denote
  next =>
    bridge_peel
    subst_vars
    obtain ⟨mm, _hbm, _, hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by subst_hyp)
    exact (isSome_eBindView hok.wf hvw hden).1
  next =>
    bridge_peel
    subst_vars
    obtain ⟨mm, _hbm, _, hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by subst_hyp)
    have h2 := isSome_eBindView hok.wf hvw hden
    grind
  -- `internBindIE`'s three side conditions.  The datum survives the two
  -- recursive calls by `BMExt` — the conjunct `Bridge/StoreBM.lean` exists
  -- for, and the reason task #97-P3-0 left this arm open.
  next =>
    bridge_peel
    subst_vars
    obtain ⟨mm, hbm, _htag0, _hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by subst_hyp)
    grind [BMExt.get]
  next =>
    bridge_peel
    subst_vars
    obtain ⟨mm, _hbm, _, hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by subst_hyp)
    have h2 := isSome_eBindView hok.wf hvw hden
    exact view_isSome (by grind)
  next =>
    bridge_peel
    subst_vars
    obtain ⟨mm, _hbm, _, hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by subst_hyp)
    have h2 := isSome_eBindView hok.wf hvw hden
    exact view_isSome (by grind)
  -- the memo insert's answer, then the arm's postcondition
  next =>
    bridge_peel
    subst_vars
    obtain ⟨mm, hbm, _htag0, _hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by subst_hyp)
    refine RelE.retarget ?_ ?_ hden
    · refine InstLAt.bind_step' hok.wf htg rfl (by subst_hyp) hbm
        (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp)
        (by subst_hyp) ?_
      grind
    · grind only [Ext.trans]
  next =>
    bridge_peel
    subst_vars
    obtain ⟨mm, hbm, _htag0, _hvw⟩ :=
      view_of_viewBindI_wf hok.wf (i := c) htg (by subst_hyp)
    refine ⟨by grind only [StateOK, StateOK.mk], by subst_hyp,
      by grind only [Ext.trans], by grind only [BMExt.trans, BMExt.refl],
      by grind, by grind, ?_⟩
    refine InstLAt.bind_step' hok.wf htg rfl (by subst_hyp) hbm
      (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp)
      (by subst_hyp) ?_
    grind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
`letE` ARM; the body descends at `dd + 1`. -/
theorem instListGoArmLet_spec (vs : Array EIdx) (ws : List Expr) (fuel : Nat)
    (ih : InstLSpec vs ws (instantiateListGo vs fuel)) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hm : InstLMemoA ws s₁)
    (hvec : InstLVec s₁.store vs ws)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.letE) = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ instListGoArmLet vs fuel c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ InstLMemoA ws s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        InstLAt ws dd s₁.store c s'.store r⌝⦄ := by
  have hrec := ih.run
  mvcgen [instListGoArmLet, hrec]
  all_goals try exact fun dd e => Expr.instantiateList e ws dd
  all_goals try bridge_vcs [Expr.instantiateList, InstLVec.ext, InstLVec.length]
  next =>
    bridge_peel
    subst_vars
    refine RelE.retarget ?_ ?_ hden
    · exact InstLAt.letE_step hok.wf (by subst_hyp) (by subst_hyp)
        (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp)
        (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp)
    · grind only [Ext.trans]
  next =>
    bridge_peel
    subst_vars
    refine ⟨by grind only [StateOK, StateOK.mk], by subst_hyp,
      by grind only [Ext.trans], by grind only [BMExt.trans, BMExt.refl],
      by grind, by grind, ?_⟩
    exact InstLAt.letE_step hok.wf (by subst_hyp) (by subst_hyp) (by subst_hyp)
      (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp)
      (by subst_hyp) (by subst_hyp) (by subst_hyp)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo — the
`proj` ARM.  The struct NAME is carried unchanged, and its denotation comes
from `denote_eq_proj`'s existential, which `grind` cannot see through. -/
theorem instListGoArmProj_spec (vs : Array EIdx) (ws : List Expr) (fuel : Nat)
    (ih : InstLSpec vs ws (instantiateListGo vs fuel)) (s₁ : AState)
    (c : EIdx) (dd : Nat) (hok : StateOK s₁) (hm : InstLMemoA ws s₁)
    (hvec : InstLVec s₁.store vs ws)
    (hden : (denoteE s₁.store c).isSome = true)
    (htg : (c.tag == ETag.proj) = true) :
    ⦃fun s => ⌜s = s₁⌝⦄ instListGoArmProj vs fuel c dd
    ⦃⇓? r s' => ⌜StateOK s' ∧ InstLMemoA ws s' ∧ Ext s₁.store s'.store ∧
        BMExt s₁.store s'.store ∧
        s'.caches = s₁.caches ∧ s'.pins = s₁.pins ∧
        InstLAt ws dd s₁.store c s'.store r⌝⦄ := by
  have hrec := ih.run
  mvcgen [instListGoArmProj, hrec]
  all_goals try exact fun dd e => Expr.instantiateList e ws dd
  all_goals try bridge_vcs [Expr.instantiateList, InstLVec.ext, InstLVec.length]
  next =>
    bridge_peel
    subst_vars
    obtain ⟨nm, es, _, hn0, _⟩ :=
      denote_eq_proj hok.wf (h := c)
        (view_of_viewProj_tag htg (by subst_hyp)) hden
    refine RelE.retarget ?_ ?_ hden
    · exact InstLAt.proj_step hok.wf (by subst_hyp) (by subst_hyp)
        (by subst_hyp) (by subst_hyp) (by subst_hyp) (by subst_hyp) hn0
    · grind only [Ext.trans]
  next =>
    bridge_peel
    subst_vars
    obtain ⟨nm, es, _, hn0, _⟩ :=
      denote_eq_proj hok.wf (h := c)
        (view_of_viewProj_tag htg (by subst_hyp)) hden
    refine ⟨by grind only [StateOK, StateOK.mk], by subst_hyp,
      by grind only [Ext.trans], by grind only [BMExt.trans, BMExt.refl],
      by grind, by grind, ?_⟩
    exact InstLAt.proj_step hok.wf (by subst_hyp) (by subst_hyp) (by subst_hyp)
      (by subst_hyp) (by subst_hyp) (by subst_hyp) hn0

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
    mvcgen [instantiateListGo_zero]
    all_goals bridge_vcs [Expr.instantiateList]
  | succ fuel ih =>
    constructor
    intro s₀ h d hok hm hvec hden
    have happ := instListGoArmApp_spec vs ws fuel ih
    have hbind := instListGoArmBind_spec vs ws fuel ih
    have hlet := instListGoArmLet_spec vs ws fuel ih
    have hproj := instListGoArmProj_spec vs ws fuel ih
    have hpure := (instantiateList_spec fuel vs ws).run
    mvcgen [instantiateListGo_succ, happ, hbind, hlet, hproj, hpure]
    all_goals try bridge_vcs [Expr.instantiateList]
    -- TWO verification conditions survive the closer: the derived-word cutoff
    -- and the catch-all leaf.  The `.bvar` branch is the UNMEMOIZED walk, by
    -- name, exactly as con-leche's is.
    next =>
      bridge_peel
      subst_vars
      exact ⟨hok, hm, Ext.refl _, BMExt.refl _, rfl, rfl,
        InstLAt.cutoff hok.wf (by grind) (by grind)⟩
    next =>
      bridge_peel
      subst_vars
      obtain ⟨e0, he0⟩ := Option.isSome_iff_exists.mp hden
      obtain ⟨vw, hvw⟩ := denoteE_view he0
      exact ⟨hok, hm, Ext.refl _, BMExt.refl _, rfl, rfl,
        InstLAt.leaf hok.wf hvw (by grind) (by grind) (by grind) (by grind)
          (by grind)⟩

/-- con-leche: ConLeche/Kernel/ExprOps.lean:371-373 instantiateListFast —
**THEOREM 1 for `instantiateList`, at the entry point**. -/
theorem instantiateListFast_spec (fuel : Nat) (s₀ : AState) (e : EIdx)
    (vs : Array EIdx) (d : Nat) (ws : List Expr) (hok : StateOK s₀)
    (hvec : InstLVec s₀.store vs ws)
    (hden : (denoteE s₀.store e).isSome = true) :
    ⦃fun s => ⌜s = s₀⌝⦄ instantiateListFast fuel e vs d
    ⦃⇓? r s' => ⌜StateOK s' ∧ Ext s₀.store s'.store ∧
        BMExt s₀.store s'.store ∧
        s'.caches = s₀.caches ∧ s'.pins = s₀.pins ∧
        s'.memos.instLC = ∅ ∧ InstLAt ws d s₀.store e s'.store r⌝⦄ := by
  have hr := (instantiateListGo_spec vs ws fuel).run
  mvcgen [instantiateListFast, hr]
  all_goals bridge_vcs [Expr.instantiateList, InstLVec.ext]

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — the same statement about
a RUN. -/
theorem instantiateListFast_run {fuel : Nat} {s₀ s' : AState} {e r : EIdx}
    {vs : Array EIdx} {d : Nat} {ws : List Expr} (hok : StateOK s₀)
    (hvec : InstLVec s₀.store vs ws)
    (hden : (denoteE s₀.store e).isSome = true)
    (hrun : (instantiateListFast fuel e vs d).run s₀ = Except.ok (r, s')) :
    StateOK s' ∧ Ext s₀.store s'.store ∧ BMExt s₀.store s'.store ∧
      s'.caches = s₀.caches ∧
      s'.pins = s₀.pins ∧ s'.memos.instLC = ∅ ∧
      InstLAt ws d s₀.store e s'.store r :=
  AM.of_run (P := fun s => s = s₀) rfl hrun
    (instantiateListFast_spec fuel s₀ e vs d ws hok hvec hden)

/-! ## The axiom check

Every theorem of this file, so that nothing can hide anywhere: since task
#97-P3-2 the module has no unproved goal, and the `instantiateList` pair —
the two walks whose three open goals the arm split closed — is checked by
name. -/

#print axioms instantiateList_of_bvarBound_le
#print axioms liftLooseBVars_of_bvarBound_le
#print axioms eidxCopyUpto_toList
#print axioms takeEidx_toList
#print axioms lastEidx_toList
#print axioms denoteEList_takeEidx
#print axioms denoteEList_lastEidx
#print axioms InstLVec.get
#print axioms InstLVec.last
#print axioms InstLAt.cutoff
#print axioms LiftAt.cutoff
#print axioms LowerAt.cutoff
#print axioms Inst1LAt.cutoff
#print axioms liftSet_specG
#print axioms lowerSet_specG
#print axioms inst1LSet_specG
#print axioms instLSet_specG
#print axioms bvarB_bvarBSpec
#print axioms liftLooseBVarsGo_spec
#print axioms liftLooseBVarsFast_spec
#print axioms liftLooseBVarsFast_run
#print axioms lowerBVarsGo_spec
#print axioms lowerBVarsFast_spec
#print axioms lowerBVarsFast_run
#print axioms instantiate1LiftGo_spec
#print axioms instantiate1LiftFast_spec
#print axioms instantiate1LiftFast_run
#print axioms instPisAtLift_spec
#print axioms RelEO.instPisAtLift_cons
#print axioms RelEO.instPisAtLift_none
#print axioms InstLVec.get'
#print axioms InstLAt.bvar_cutV
#print axioms InstLAt.bvar_recV
#print axioms InstLAt.bvar_aboveV
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

/-
# `ConRon.Bridge.Core.Walks.Cached` — the five cached verdict walks

Task #97-P3-CoreWalks, and **the exemplar of the tier**: the five walks of
`Arena/Core.lean` that are memo wrappers of their own rather than knot slots.
`Bridge/Core/Memo.lean` does the six knot slots; these five are the same
three-branch shape (probe, hit, miss-and-insert) over the five tables of
`CacheOK` that `Bridge/Core/Memo.lean` never touches:

| walk | table | con-leche |
|---|---|---|
| `lvlEq?` | `lvlEqC` | `ConLeche/Kernel/Level.lean:158-163 isEquiv` |
| `lvlsEq?` | `lvlsEqC` | `ConLeche/Kernel/Level.lean:165-172 isEquivList` |
| `constTyAt` | `constTyC` | none — DESIGN §8.3's instantiated-constant cache |
| `constValAt` | `constValC` | none — the delta step's expensive half |
| `ruleRhsAt` | `ruleRhsC` | none — the ι rule's right-hand side |

## The two halves, and why they land differently

The first two are **CLOSED**: their miss branch computes with `Level.isEquiv`
on trees read back from the store, and the readback's own obligation is
`Bridge/Core/Walks/Frame.lean`'s.  They are the first non-slot walks of
`Arena/Core.lean` to have a theorem at all.

The last three are **`sorry`**, and for one reason each time: the miss branch
is `instLPFast`, whose callee rule is `Bridge/ExprOps/Owed.lean`'s
`instLPFast_spec` and is itself `sorry` (task #97-P3-0's open list, item "the
eight of `ExprOps/Owed.lean`").  Their proofs are otherwise the first two's,
table for table — the five insert lemmas below are written for all of them.

**No module of `Bridge/Core/Walks/` imports `Bridge/ExprOps/`**, which is why
the three are stated here and not proved here: task #97-P3-1 re-stated that
tier against the split arms while this round ran, and a walk theorem that
named one of its theorems would have to move with it.  What each owes is
written at its `sorry`.

## The tier's recipe, in five steps

Read off `lvlEq?_spec` below; every cached walk follows it.

1. **`mvcgen [<the walk>]` and nothing else.**  `Bridge/Specs.lean`'s three
   readback specs are `@[spec]`, so `mvcgen` applies them by itself and each
   readback contributes its five conjuncts to the verification condition;
   `ReadbackFrame.ofReadL` (and its two siblings) folds them into one frame,
   and `.trans` composes the two.  *`mvcgen` cannot be made to prefer a
   theorem passed in its list over a registered `@[spec]` for the same
   function — measured — so the frame is assembled in the walk rather than
   delivered by a spec of its own.*
2. **The postcondition does not take the subjects' denotations as
   hypotheses.**  It says "*if* the walk answered `some b`, then the subjects
   denote and `Level.isEquiv` answers `b`" — task #97-P3-0's rule 4 at two
   subjects, and the reason is the hit branch: `LvlEqCacheOK` DELIVERS the
   denotations, it does not consume them.
3. **The five verification conditions are the three branches plus the two
   readbacks' preconditions**, and the two preconditions are
   `hok.caches.readL` and the same through the first frame.
4. **The insert is `LvlEqCacheOK.insert_capped`**, whose cap branch costs
   nothing — `Bridge/Core/Memo.lean`'s finding, here for the seventh time.
5. **The answer relation is not `Bridge/Core/Walks/Spec.lean`'s `SimVOp`.**
   The pure side of these five is not fueled at all (`Level.isEquiv` is a
   total function of two trees), so there is no `∃ F` and the conclusion is
   an equation.  That is the one structural difference between this group and
   every other group of the tier, and it is why this group is the cheap one.
-/
import ConRon.Bridge.Core.Walks.Frame
import ConRon.Bridge.Promote.Pers
import ConRon.Bridge.ExprOps.Owed

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option mvcgen.warning false
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.Do

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. The five insert lemmas

`Bridge/Core/Memo.lean`'s `EntryCacheOK.insert_capped` for the five tables it
does not touch.  Each is the same two-branch split on the cap, with the
empty-table case inlined. -/

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:51 CSOK.insertWhnfCoreC — the
level-verdict cache's insert, through the cap. -/
theorem LvlEqCacheOK.insert_capped {tbl : Std.HashMap (LIdx × LIdx) Bool}
    {st : EStore} (h : LvlEqCacheOK tbl st) {u v : LIdx} {lu lv : Level}
    {r : Bool} (hu : denoteL st.ls u = some lu)
    (hv : denoteL st.ls v = some lv) (heq : Level.isEquiv lu lv = some r) :
    LvlEqCacheOK ((if tbl.size < cacheCap then tbl else ∅).insert (u, v) r)
      st := by
  have key : ∀ (t : Std.HashMap (LIdx × LIdx) Bool), LvlEqCacheOK t st →
      LvlEqCacheOK (t.insert (u, v) r) st := by
    intro t ht k x hl
    rw [Std.HashMap.getElem?_insert] at hl
    split at hl
    · rename_i hbeq
      cases hl
      obtain rfl := eq_of_beq hbeq
      exact ⟨lu, lv, hu, hv, heq⟩
    · exact ht k x hl
  split
  · exact key _ h
  · exact key _ (by intro k x hl; simp at hl)

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:51 CSOK.insertWhnfCoreC — the
same at the universe-argument LIST verdict cache. -/
theorem LvlsEqCacheOK.insert_capped {tbl : Std.HashMap (LsIdx × LsIdx) Bool}
    {st : EStore} (h : LvlsEqCacheOK tbl st) {us vs : LsIdx}
    {lus lvs : List Level} {r : Bool}
    (hu : denoteLs st.lss us = some lus)
    (hv : denoteLs st.lss vs = some lvs)
    (heq : Level.isEquivList lus lvs = some r) :
    LvlsEqCacheOK
      ((if tbl.size < cacheCap then tbl else ∅).insert (us, vs) r) st := by
  have key : ∀ (t : Std.HashMap (LsIdx × LsIdx) Bool), LvlsEqCacheOK t st →
      LvlsEqCacheOK (t.insert (us, vs) r) st := by
    intro t ht k x hl
    rw [Std.HashMap.getElem?_insert] at hl
    split at hl
    · rename_i hbeq
      cases hl
      obtain rfl := eq_of_beq hbeq
      exact ⟨lus, lvs, hu, hv, heq⟩
    · exact ht k x hl
  split
  · exact key _ h
  · exact key _ (by intro k x hl; simp at hl)

/-- con-leche: none — the instantiated-constant TYPE cache's insert. -/
theorem ConstTyCacheOK.insert_capped {tbl : Std.HashMap (NIdx × LsIdx) EIdx}
    {st : EStore} (h : ConstTyCacheOK env tbl st) {n : NIdx} {us : LsIdx}
    {i : EIdx} {nm : ConLeche.Name} {ls : List Level} {ci : ConstantInfo}
    (hn : denoteN st.ns n = some nm) (hus : denoteLs st.lss us = some ls)
    (hf : env.find? nm = some ci)
    (hi : denoteE st i = some (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams ls)) :
    ConstTyCacheOK env
      ((if tbl.size < cacheCap then tbl else ∅).insert (n, us) i) st := by
  have key : ∀ (t : Std.HashMap (NIdx × LsIdx) EIdx),
      ConstTyCacheOK env t st → ConstTyCacheOK env (t.insert (n, us) i) st := by
    intro t ht k j hl
    rw [Std.HashMap.getElem?_insert] at hl
    split at hl
    · rename_i hbeq
      cases hl
      obtain rfl := eq_of_beq hbeq
      exact ⟨nm, ls, ci, hn, hus, hf, hi⟩
    · exact ht k j hl
  split
  · exact key _ h
  · exact key _ (by intro k j hl; simp at hl)

/-- con-leche: none — the instantiated-constant VALUE cache's insert. -/
theorem ConstValCacheOK.insert_capped {tbl : Std.HashMap (NIdx × LsIdx) EIdx}
    {st : EStore} (h : ConstValCacheOK env tbl st) {n : NIdx} {us : LsIdx}
    {i : EIdx} {nm : ConLeche.Name} {ls : List Level} {cv : ConstantVal}
    {value : Expr} {hint : ReducibilityHint}
    (hn : denoteN st.ns n = some nm) (hus : denoteLs st.lss us = some ls)
    (hf : env.find? nm = some (.defnInfo cv value hint))
    (hi : denoteE st i = some (value.instantiateLevelParams cv.levelParams ls)) :
    ConstValCacheOK env
      ((if tbl.size < cacheCap then tbl else ∅).insert (n, us) i) st := by
  have key : ∀ (t : Std.HashMap (NIdx × LsIdx) EIdx),
      ConstValCacheOK env t st →
      ConstValCacheOK env (t.insert (n, us) i) st := by
    intro t ht k j hl
    rw [Std.HashMap.getElem?_insert] at hl
    split at hl
    · rename_i hbeq
      cases hl
      obtain rfl := eq_of_beq hbeq
      exact ⟨nm, ls, cv, value, hint, hn, hus, hf, hi⟩
    · exact ht k j hl
  split
  · exact key _ h
  · exact key _ (by intro k j hl; simp at hl)

/-- con-leche: none — the ι rule right-hand-side cache's insert, at the
THREE-part key. -/
theorem RuleRhsCacheOK.insert_capped
    {tbl : Std.HashMap (NIdx × NIdx × LsIdx) EIdx} {st : EStore}
    (h : RuleRhsCacheOK env tbl st) {rn cn : NIdx} {us : LsIdx} {i : EIdx}
    {rnv cnv : ConLeche.Name} {ls : List Level} {cv : ConstantVal}
    {mi rp : Nat} {rules : List RecRule} {rl : RecRule}
    (hr : denoteN st.ns rn = some rnv) (hc : denoteN st.ns cn = some cnv)
    (hus : denoteLs st.lss us = some ls)
    (hf : env.find? rnv = some (.recInfo cv mi rp rules))
    (hrl : rules.find? (fun r => r.ctor == cnv) = some rl)
    (hi : denoteE st i = some (rl.rhs.instantiateLevelParams cv.levelParams ls)) :
    RuleRhsCacheOK env
      ((if tbl.size < cacheCap then tbl else ∅).insert (rn, cn, us) i) st := by
  have key : ∀ (t : Std.HashMap (NIdx × NIdx × LsIdx) EIdx),
      RuleRhsCacheOK env t st →
      RuleRhsCacheOK env (t.insert (rn, cn, us) i) st := by
    intro t ht k j hl
    rw [Std.HashMap.getElem?_insert] at hl
    split at hl
    · rename_i hbeq
      cases hl
      obtain rfl := eq_of_beq hbeq
      exact ⟨rnv, cnv, ls, cv, mi, rp, rules, rl, hr, hc, hus, hf, hrl, hi⟩
    · exact ht k j hl
  split
  · exact key _ h
  · exact key _ (by intro k j hl; simp at hl)

/-! ### `CacheOK` past one of the five

`Bridge/Core/Memo.lean`'s six per-table versions, for the two tables this
module closes: thirteen clauses that did not move plus the one that did. -/

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:51 CSOK.insertWhnfCoreC. -/
theorem CacheOK.insertLvlEq {s : AState} (hc : CacheOK mode env s)
    {u v : LIdx} {lu lv : Level} {r : Bool}
    (hu : denoteL s.store.ls u = some lu)
    (hv : denoteL s.store.ls v = some lv)
    (heq : Level.isEquiv lu lv = some r) :
    CacheOK mode env { s with caches := { s.caches with
      lvlEqC := (if s.caches.lvlEqC.size < cacheCap then s.caches.lvlEqC
        else ∅).insert (u, v) r } } :=
  { hc with lvlEq := LvlEqCacheOK.insert_capped hc.lvlEq hu hv heq }

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:51 CSOK.insertWhnfCoreC. -/
theorem CacheOK.insertLvlsEq {s : AState} (hc : CacheOK mode env s)
    {us vs : LsIdx} {lus lvs : List Level} {r : Bool}
    (hu : denoteLs s.store.lss us = some lus)
    (hv : denoteLs s.store.lss vs = some lvs)
    (heq : Level.isEquivList lus lvs = some r) :
    CacheOK mode env { s with caches := { s.caches with
      lvlsEqC := (if s.caches.lvlsEqC.size < cacheCap then s.caches.lvlsEqC
        else ∅).insert (us, vs) r } } :=
  { hc with lvlsEq := LvlsEqCacheOK.insert_capped hc.lvlsEq hu hv heq }

/-- con-leche: none — `CacheOK` past the instantiated-constant TYPE cache's
insert. -/
theorem CacheOK.insertConstTy {s : AState} (hc : CacheOK mode env s)
    {n : NIdx} {us : LsIdx} {i : EIdx} {nm : ConLeche.Name} {ls : List Level}
    {ci : ConstantInfo}
    (hn : denoteN s.store.ns n = some nm) (hus : denoteLs s.store.lss us = some ls)
    (hf : env.find? nm = some ci)
    (hi : denoteE s.store i = some (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams ls)) :
    CacheOK mode env { s with caches := { s.caches with
      constTyC := (if s.caches.constTyC.size < cacheCap then s.caches.constTyC
        else ∅).insert (n, us) i } } :=
  { hc with constTy := ConstTyCacheOK.insert_capped hc.constTy hn hus hf hi }

/-- con-leche: none — `CacheOK` past the instantiated-constant VALUE cache's
insert. -/
theorem CacheOK.insertConstVal {s : AState} (hc : CacheOK mode env s)
    {n : NIdx} {us : LsIdx} {i : EIdx} {nm : ConLeche.Name} {ls : List Level}
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hn : denoteN s.store.ns n = some nm) (hus : denoteLs s.store.lss us = some ls)
    (hf : env.find? nm = some (.defnInfo cv value hint))
    (hi : denoteE s.store i = some (value.instantiateLevelParams cv.levelParams ls)) :
    CacheOK mode env { s with caches := { s.caches with
      constValC := (if s.caches.constValC.size < cacheCap then s.caches.constValC
        else ∅).insert (n, us) i } } :=
  { hc with constVal := ConstValCacheOK.insert_capped hc.constVal hn hus hf hi }

/-- con-leche: none — `CacheOK` past the ι right-hand-side cache's insert. -/
theorem CacheOK.insertRuleRhs {s : AState} (hc : CacheOK mode env s)
    {rn cn : NIdx} {us : LsIdx} {i : EIdx}
    {rnv cnv : ConLeche.Name} {ls : List Level} {cv : ConstantVal}
    {mi rp : Nat} {rules : List RecRule} {rl : RecRule}
    (hr : denoteN s.store.ns rn = some rnv) (hcn : denoteN s.store.ns cn = some cnv)
    (hus : denoteLs s.store.lss us = some ls)
    (hf : env.find? rnv = some (.recInfo cv mi rp rules))
    (hrl : rules.find? (fun r => r.ctor == cnv) = some rl)
    (hi : denoteE s.store i = some (rl.rhs.instantiateLevelParams cv.levelParams ls)) :
    CacheOK mode env { s with caches := { s.caches with
      ruleRhsC := (if s.caches.ruleRhsC.size < cacheCap then s.caches.ruleRhsC
        else ∅).insert (rn, cn, us) i } } :=
  { hc with ruleRhs := RuleRhsCacheOK.insert_capped hc.ruleRhs hr hcn hus hf hrl hi }

/-! ## 2. `lvlEq?` — the tier's exemplar, CLOSED -/

/-- con-leche: ConLeche/Kernel/Level.lean:158-163 Level.isEquiv — **THEOREM 1
for `lvlEq?`**, the first `Arena/Core.lean` walk that is not a knot slot to
have one.

The verdict the walk answers **IS** `Level.isEquiv`'s at the two handles'
denotations — the `Option Bool` and not just its `some` half — and the state
keeps `CheckOK` with the store and the pins untouched.

*(Task #97-P3-Core-2 strengthened the last conjunct from "∀ b, r = some b →
…" to the equation.  The walk's `none` is `isEquiv`'s own `none` and nothing
else — `lvlEq?` returns the memo row or `Level.isEquiv lu lv` itself — and a
caller that must decide a GUARD off the verdict needs the negative half:
`IProjEntry.fireOk` fires the projection rule when the structure sort is NOT
provably zero, so a one-directional spec leaves the `none` case unrelatable.
`Bridge/Inductives/SumParts.lean`'s own note asks for the same thing, in its
words "`lvlEq?_spec` read at both signs".)* -/
theorem lvlEq?_spec (s₀ : AState) (u v : LIdx) (hok : CheckOK mode env fe s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ lvlEq? u v
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧
        ∃ lu lv, denoteL s₀.store.ls u = some lu ∧
          denoteL s₀.store.ls v = some lv ∧
          r = Level.isEquiv lu lv⌝⦄ := by
  mvcgen [lvlEq?]
  case vc1 =>
    bridge_peel; subst_vars
    rename_i hhit
    refine ⟨hok, rfl, rfl, ?_⟩
    obtain ⟨lu, lv, hu, hv, he⟩ := hok.caches.lvlEq (u, v) _ hhit
    exact ⟨lu, lv, hu, hv, he.symm⟩
  case vc2 => bridge_peel; subst_vars; exact hok.caches.readL
  case vc3 => bridge_peel; subst_vars; assumption
  case vc4 =>
    bridge_peel; subst_vars
    rename_i heq _s1 _mp1 _mp _sf hst1 hst2 hm1 hm2 hp1 hp2 hc1 hc2 hdu hL1
      hdv hL2
    have hf1 := ReadbackFrame.ofReadL hst1 hm1 hp1 hc1 hL1
    have hf2 := ReadbackFrame.ofReadL hst2 hm2 hp2 hc2 hL2
    have hf := hf1.trans hf2
    have hck := CheckOK.ofReadbackFrame hok hf
    refine ⟨CheckOK.ofCache hck
        (CacheOK.insertLvlEq hck.caches ?_ ?_ heq) rfl rfl,
      hf.store, hf.pins, ?_⟩
    · rw [hf.store]; exact hdu
    · rw [hf2.store]; exact hdv
    · exact ⟨_, _, hdu, by rw [← hf1.store]; exact hdv, heq.symm⟩
  case vc5 =>
    bridge_peel; subst_vars
    rename_i heq _sf hst1 hst2 hm1 hm2 hp1 hp2 hc1 hc2 hdu hL1 hdv hL2
    have hf1 := ReadbackFrame.ofReadL hst1 hm1 hp1 hc1 hL1
    have hf2 := ReadbackFrame.ofReadL hst2 hm2 hp2 hc2 hL2
    have hf := hf1.trans hf2
    exact ⟨CheckOK.ofReadbackFrame hok hf, hf.store, hf.pins,
      ⟨_, _, hdu, by rw [← hf1.store]; exact hdv, heq.symm⟩⟩

/-! ## 3. `lvlsEq?` — the same at two universe-argument lists, CLOSED -/

/-- con-leche: ConLeche/Kernel/Level.lean:165-172 Level.isEquivList —
**THEOREM 1 for `lvlsEq?`**.  Five verification conditions, the same five,
with `ReadbackFrame.ofReadLs` in place of `.ofReadL`. -/
theorem lvlsEq?_spec (s₀ : AState) (us vs : LsIdx)
    (hok : CheckOK mode env fe s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ lvlsEq? us vs
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧
        ∃ lus lvs, denoteLs s₀.store.lss us = some lus ∧
          denoteLs s₀.store.lss vs = some lvs ∧
          r = Level.isEquivList lus lvs⌝⦄ := by
  mvcgen [lvlsEq?]
  case vc1 =>
    bridge_peel; subst_vars
    rename_i hhit
    refine ⟨hok, rfl, rfl, ?_⟩
    obtain ⟨lu, lv, hu, hv, he⟩ := hok.caches.lvlsEq (us, vs) _ hhit
    exact ⟨lu, lv, hu, hv, he.symm⟩
  case vc2 => bridge_peel; subst_vars; exact hok.caches.readLs
  case vc3 => bridge_peel; subst_vars; assumption
  case vc4 =>
    bridge_peel; subst_vars
    rename_i heq _s1 _mp1 _mp _sf hst1 hst2 hm1 hm2 hp1 hp2 hc1 hc2 hdu hL1
      hdv hL2
    have hf1 := ReadbackFrame.ofReadLs hst1 hm1 hp1 hc1 hL1
    have hf2 := ReadbackFrame.ofReadLs hst2 hm2 hp2 hc2 hL2
    have hf := hf1.trans hf2
    have hck := CheckOK.ofReadbackFrame hok hf
    refine ⟨CheckOK.ofCache hck
        (CacheOK.insertLvlsEq hck.caches ?_ ?_ heq) rfl rfl,
      hf.store, hf.pins, ?_⟩
    · rw [hf.store]; exact hdu
    · rw [hf2.store]; exact hdv
    · exact ⟨_, _, hdu, by rw [← hf1.store]; exact hdv, heq.symm⟩
  case vc5 =>
    bridge_peel; subst_vars
    rename_i heq _sf hst1 hst2 hm1 hm2 hp1 hp2 hc1 hc2 hdu hL1 hdv hL2
    have hf1 := ReadbackFrame.ofReadLs hst1 hm1 hp1 hc1 hL1
    have hf2 := ReadbackFrame.ofReadLs hst2 hm2 hp2 hc2 hL2
    have hf := hf1.trans hf2
    exact ⟨CheckOK.ofReadbackFrame hok hf, hf.store, hf.pins,
      ⟨_, _, hdu, by rw [← hf1.store]; exact hdv, heq.symm⟩⟩

/-! ## 4. The three instantiated-constant caches

**OPEN**, all three, and for one reason: the miss branch is `instLPFast`,
whose callee rule is `Bridge/ExprOps/Owed.lean`'s `instLPFast_spec` — itself
`sorry` at task #97-P3-0's open list, and re-stated by task #97-P3-1's arm
split while this round ran.  The insert lemmas above are written; what each
proof needs is the one call's spec and nothing else. -/

/-- con-leche: none — **`CheckOK` past an `instLPFast` call**: the call's
record equation names the three readback tables it moves and frames the other
eleven, so the eleven transport along `Ext` and the three are the call's own
conjuncts. -/
theorem CheckOK.ofInstLP {s₀ s' : AState} (hok : CheckOK mode env fe s₀)
    (hst : StateOK s') (hx : Ext s₀.store s'.store)
    (hL : ReadLCacheOK s'.caches.readLC s'.store)
    (hLs : ReadLsCacheOK s'.caches.readLsC s'.store)
    (hN : ReadNCacheOK s'.caches.readNC s'.store)
    (hc : s'.caches = { s₀.caches with
      readLC := s'.caches.readLC, readNC := s'.caches.readNC,
      readLsC := s'.caches.readLsC })
    (hp : s'.pins = s₀.pins) : CheckOK mode env fe s' where
  state := hst
  caches :=
    { whnfCore := by rw [hc]; exact hok.caches.whnfCore.mono hx
      whnf := by rw [hc]; exact hok.caches.whnf.mono hx
      infer := by rw [hc]; exact hok.caches.infer.mono hx
      inferIO := by rw [hc]; exact hok.caches.inferIO.mono hx
      annot := by rw [hc]; exact hok.caches.annot.mono hx
      defeq := by rw [hc]; exact hok.caches.defeq.mono hx
      lvlEq := by rw [hc]; exact hok.caches.lvlEq.mono hx
      lvlsEq := by rw [hc]; exact hok.caches.lvlsEq.mono hx
      constTy := by rw [hc]; exact hok.caches.constTy.mono hx
      constVal := by rw [hc]; exact hok.caches.constVal.mono hx
      ruleRhs := by rw [hc]; exact hok.caches.ruleRhs.mono hx
      readL := hL
      readN := hN
      readLs := hLs }
  pins := hok.pins.mono hx hp
  ienv := hok.ienv.mono hx

/-- con-leche: none — the field-by-field inversion of `denoteCV`, which
is where `cv.levelParams` on the two sides meet.  (Moved down from
`Bridge/Core/Walks/Spine.lean`, round 4: the three instantiated-constant
caches need it.) -/
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

/-- con-leche: none — **THEOREM 1 for `constTyAt`** (DESIGN §8.3's
instantiated-constant TYPE cache).  **CLOSED** (round 4), on
`Bridge/ExprOps/Owed.lean`'s `instLPFast_spec` with its cache frame. -/
theorem constTyAt_spec (s₀ : AState) (cv : IConstantVal) (us : LsIdx)
    (nm : ConLeche.Name) (ls : List Level) (ci : ConstantInfo)
    (hok : CheckOK mode env fe s₀)
    (hn : denoteN s₀.store.ns cv.name = some nm)
    (hus : denoteLs s₀.store.lss us = some ls)
    (hf : env.find? nm = some ci)
    (hcv : Frontend.denoteCV s₀.store cv = some ci.toConstantVal) :
    ⦃fun s => ⌜s = s₀⌝⦄ constTyAt cv us
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteE s'.store r =
          some (ci.toConstantVal.type.instantiateLevelParams
            ci.toConstantVal.levelParams ls)⌝⦄ := by
  obtain ⟨_hnm, hlps, hty⟩ := denoteCV_inv hcv
  have hi := ExprOps.instLPFast_spec coreWalkFuel s₀ cv.levelParams us cv.type
    _ _ hok.state hok.caches.readN hok.caches.readL hok.caches.readLs hlps hus
    (by rw [hty]; rfl)
  mvcgen [constTyAt, hi]
  all_goals (bridge_peel; subst_vars)
  · -- the HIT: the row's own clause, at the three functional denotations
    rename_i r hhit
    refine ⟨hok, Ext.refl _, rfl, ?_⟩
    obtain ⟨nm', ls', ci', hn', hus', hf', hd⟩ := hok.caches.constTy _ r hhit
    obtain rfl := Option.some.inj (hn'.symm.trans hn)
    obtain rfl := Option.some.inj (hus'.symm.trans hus)
    obtain rfl := Option.some.inj (hf'.symm.trans hf)
    exact hd
  · -- the MISS: `instLPFast`, then the capped insert
    rename_i _ _ r s1 _ _ _ hst hL hLs hN hx _ hc hp _ hrel
    have hck := CheckOK.ofInstLP hok hst hx hL hLs hN hc hp
    have hd := hrel _ hty
    exact ⟨CheckOK.ofCache hck (CacheOK.insertConstTy hck.caches
        (denoteN_ext hn hx) (denoteLs_ext hus hx) hf hd) rfl rfl, hx, hp, hd⟩

/-- con-leche: none — **THEOREM 1 for `constValAt`** (the delta step's
expensive half, and the reason `unfoldDefinition` is not free).  **OPEN**:
needs `instLPFast_spec`. -/
theorem constValAt_spec (s₀ : AState) (n : NIdx) (lps : List NIdx)
    (value : EIdx) (us : LsIdx) (nm : ConLeche.Name) (ls : List Level)
    (cv : ConstantVal) (val : Expr) (hint : ReducibilityHint)
    (hok : CheckOK mode env fe s₀)
    (hn : denoteN s₀.store.ns n = some nm)
    (hus : denoteLs s₀.store.lss us = some ls)
    (hlps : Frontend.denoteNList s₀.store.ns lps = some cv.levelParams)
    (hval : denoteE s₀.store value = some val)
    (hfd : env.find? nm = some (.defnInfo cv val hint)) :
    ⦃fun s => ⌜s = s₀⌝⦄ constValAt n lps value us
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteE s'.store r =
          some (val.instantiateLevelParams cv.levelParams ls)⌝⦄ := by
  have hi := ExprOps.instLPFast_spec coreWalkFuel s₀ lps us value
    _ _ hok.state hok.caches.readN hok.caches.readL hok.caches.readLs hlps hus
    (by rw [hval]; rfl)
  mvcgen [constValAt, hi]
  all_goals (bridge_peel; subst_vars)
  · -- the HIT
    rename_i r hhit
    refine ⟨hok, Ext.refl _, rfl, ?_⟩
    obtain ⟨nm', ls', cv', val', hint', hn', hus', hf', hd⟩ :=
      hok.caches.constVal _ r hhit
    obtain rfl := Option.some.inj (hn'.symm.trans hn)
    obtain rfl := Option.some.inj (hus'.symm.trans hus)
    rw [hfd] at hf'
    cases hf'
    exact hd
  · -- the MISS
    rename_i _ _ r s1 _ _ _ hst hL hLs hN hx _ hc hp _ hrel
    have hck := CheckOK.ofInstLP hok hst hx hL hLs hN hc hp
    have hd := hrel _ hval
    exact ⟨CheckOK.ofCache hck (CacheOK.insertConstVal hck.caches
        (denoteN_ext hn hx) (denoteLs_ext hus hx) hfd hd) rfl rfl, hx, hp, hd⟩

/-- con-leche: none — `constValAt_spec` in ANSWER shape (round 3's rule: *a
walk whose subject is another walk's answer must not take that answer's
denotation as an explicit argument*).  The five denotations go IN as an
existential and come OUT as a universal, so a caller that reaches the walk
through `getAppFn`/`view` — `unfoldDefinition` — leaves no metavariable in the
side goal.  Four lines over the unprimed form and the functionality of each
denotation. -/
theorem constValAt_spec' (s₀ : AState) (n : NIdx) (lps : List NIdx)
    (value : EIdx) (us : LsIdx) (hok : CheckOK mode env fe s₀)
    (hpre : ∃ nm ls cv val hint, denoteN s₀.store.ns n = some nm ∧
      denoteLs s₀.store.lss us = some ls ∧
      Frontend.denoteNList s₀.store.ns lps = some cv.levelParams ∧
      denoteE s₀.store value = some val ∧
      env.find? nm = some (.defnInfo cv val hint)) :
    ⦃fun s => ⌜s = s₀⌝⦄ constValAt n lps value us
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ nm ls cv val hint, denoteN s₀.store.ns n = some nm →
          denoteLs s₀.store.lss us = some ls →
          env.find? nm = some (.defnInfo cv val hint) →
          denoteE s'.store r =
            some (val.instantiateLevelParams cv.levelParams ls)⌝⦄ := by
  obtain ⟨nm, ls, cv, val, hint, hn, hus, hlps, hval, hfd⟩ := hpre
  have h := constValAt_spec s₀ n lps value us nm ls cv val hint hok hn hus
    hlps hval hfd
  mvcgen [h]
  intro hck hx hp hd
  refine ⟨hck, hx, hp, fun nm' ls' cv' val' hint' hn' hus' hfd' => ?_⟩
  obtain rfl := Option.some.inj (hn.symm.trans hn')
  obtain rfl := Option.some.inj (hus.symm.trans hus')
  rw [hfd] at hfd'
  cases hfd'
  exact hd

/-- con-leche: none — **THEOREM 1 for `ruleRhsAt`** (an ι rule's right-hand
side at the recursor's universe instantiation).  **OPEN**: needs
`instLPFast_spec`. -/
theorem ruleRhsAt_spec (s₀ : AState) (recName ctor : NIdx) (lps : List NIdx)
    (rhs : EIdx) (us : LsIdx) (rnv cnv : ConLeche.Name) (ls : List Level)
    (cv : ConstantVal) (mi rp : Nat) (rules : List RecRule) (rl : RecRule)
    (hok : CheckOK mode env fe s₀)
    (hr : denoteN s₀.store.ns recName = some rnv)
    (hc : denoteN s₀.store.ns ctor = some cnv)
    (hus : denoteLs s₀.store.lss us = some ls)
    (hlps : Frontend.denoteNList s₀.store.ns lps = some cv.levelParams)
    (hrhs : denoteE s₀.store rhs = some rl.rhs)
    (hfr : env.find? rnv = some (.recInfo cv mi rp rules))
    (hrl : rules.find? (fun r => r.ctor == cnv) = some rl) :
    ⦃fun s => ⌜s = s₀⌝⦄ ruleRhsAt recName ctor lps rhs us
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteE s'.store r =
          some (rl.rhs.instantiateLevelParams cv.levelParams ls)⌝⦄ := by
  have hi := ExprOps.instLPFast_spec coreWalkFuel s₀ lps us rhs
    _ _ hok.state hok.caches.readN hok.caches.readL hok.caches.readLs hlps hus
    (by rw [hrhs]; rfl)
  mvcgen [ruleRhsAt, hi]
  all_goals (bridge_peel; subst_vars)
  · -- the HIT
    rename_i r hhit
    refine ⟨hok, Ext.refl _, rfl, ?_⟩
    obtain ⟨rn', cn', ls', cv', mi', rp', rules', rl', hr', hc', hus', hf', hrl', hd⟩ :=
      hok.caches.ruleRhs _ r hhit
    obtain rfl := Option.some.inj (hr'.symm.trans hr)
    obtain rfl := Option.some.inj (hc'.symm.trans hc)
    obtain rfl := Option.some.inj (hus'.symm.trans hus)
    rw [hfr] at hf'
    cases hf'
    rw [hrl] at hrl'
    cases hrl'
    exact hd
  · -- the MISS
    rename_i _ _ r s1 _ _ _ hst hL hLs hN hx _ hcc hp _ hrel
    have hck := CheckOK.ofInstLP hok hst hx hL hLs hN hcc hp
    have hd := hrel _ hrhs
    exact ⟨CheckOK.ofCache hck (CacheOK.insertRuleRhs hck.caches
        (denoteN_ext hr hx) (denoteN_ext hc hx) (denoteLs_ext hus hx) hfr hrl hd)
        rfl rfl, hx, hp, hd⟩



/-! ## 4b. `lvlEq?`'s FRAME, with no cache-content hypothesis (task #97-P3-Frame)

`lvlEq?_spec` above is the CORE grade's statement: `CheckOK` in, `CheckOK`
out.  It is the right statement for a caller that needs the VERDICT, because
the verdict a cache hit answers is `Level.isEquiv`'s only because
`LvlEqCacheOK` says so.

A caller at `StateOK` — `Bridge/Inductives/Rel.lean`'s `PStep`,
`Bridge/Frontend/Rel.lean`'s `ParseStep` — needs something else, and something
weaker: *which tables the call may have written*.  That is a fact about the
program text and not about any invariant, and `lvlEq?_frame` is it.  It is
what makes those two frames provable at `StateOK` now that task #97-P3-Frame
has widened their cache clause to `Bridge/StateOK.lean`'s `CacheFrame`, and it
is the concrete answer to "can the frame be carried at `StateOK`?": yes, and
this is it.

**Run form and not a triple, and the reason is the `[spec]` commitment.**
`Bridge/Specs.lean`'s `readLevelM_spec` is registered `@[spec]`, so `mvcgen`
applies it rather than unfolding `readLevelM`, and its hypothesis
(`ReadLCacheOK s₀.caches.readLC s₀.store`) then appears as a verification
condition a `StateOK`-graded proof cannot discharge.  A registered `[spec]`
cannot be erased (`attribute [-spec]` is rejected) and `mvcgen` cannot be made
to prefer a locally supplied theorem — `Frame.lean`'s note measured both.
Taking the two do-blocks apart by hand costs twenty lines and commits to
nothing.

**Why the two implications' hypotheses are at the INITIAL state.**  The frame
is NOT assembled as "the two readbacks, then the insert" by `CacheFrame.trans`,
because the insert's own `lvlEq` obligation needs the two handles'
DENOTATIONS, and those come from `readLevelM_spec` at `s` — a fact the
intermediate state's `ReadLCacheOK` does not re-deliver.  So the whole miss
branch is one `CacheFrame` whose implications quantify over `s`, and the
readbacks' half of it is the only part that composes. -/

section Frame

/-- con-leche: none — `get` moves nothing and answers the state.  (The
`ConRon.Bridge.Frontend` namespace has its own copy; this tier does not import
that module.) -/
theorem AM.get_ok {s s' t : AState} (h : (get : AM AState) s = .ok (t, s')) :
    t = s ∧ s' = s := by
  have he : ((s, s) : AState × AState) = (t, s') := Except.ok.inj h
  exact ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩

/-- con-leche: none — `set` answers `()` at the state it was handed. -/
theorem AM.set_ok {s s' t : AState} {u : Unit}
    (h : (set t : AM Unit) s = .ok (u, s')) : s' = t := by
  have he : (((), t) : Unit × AState) = (u, s') := Except.ok.inj h
  exact (congrArg Prod.snd he).symm

/-- con-leche: none — **`readLevelM`'s frame**, with no hypothesis: the
memoised readback moves the readback memo and nothing else, whatever is in it.
The `ReadLCacheOK` of `Bridge/Specs.lean`'s `readLevelM_spec` buys the
DENOTATION, not the frame. -/
theorem readLevelM_frame {s s' : AState} {h : LIdx} {l : Level}
    (hrun : readLevelM h s = .ok (l, s')) :
    s'.store = s.store ∧ s'.memos = s.memos ∧ s'.pins = s.pins ∧
      s'.caches = { s.caches with readLC := s'.caches.readLC } := by
  rw [readLevelM] at hrun
  obtain ⟨t, s₁, hget, hrest⟩ := AM.bind_ok hrun
  obtain ⟨ht, hs₁⟩ := AM.get_ok hget
  rw [ht, hs₁] at hrest
  cases hhit : s.caches.readLC[h]? with
  | some x =>
    rw [hhit] at hrest
    obtain ⟨-, hs⟩ := AM.pure_ok hrest
    rw [hs]
    exact ⟨rfl, rfl, rfl, rfl⟩
  | none =>
    rw [hhit] at hrest
    cases hd : denoteL s.store.ls h with
    | none => rw [hd] at hrest; exact absurd hrest (AM.Never.fail _ _ _ _)
    | some x =>
      rw [hd] at hrest
      obtain ⟨w, s₂, hset, hpure⟩ := AM.bind_ok hrest
      have hs₂ := AM.set_ok hset
      obtain ⟨-, hs⟩ := AM.pure_ok hpure
      rw [hs, hs₂]
      exact ⟨rfl, rfl, rfl, rfl⟩

/-- con-leche: none — `readLevelM`'s two CONTENT conjuncts, read off
`Bridge/Specs.lean`'s spec at a run.  Used only inside the implications of the
two frames below, where the hypothesis is available. -/
theorem readLevelM_denote {s s' : AState} {h : LIdx} {l : Level}
    (hrl : ReadLCacheOK s.caches.readLC s.store)
    (hrun : readLevelM h s = .ok (l, s')) :
    denoteL s.store.ls h = some l ∧
      ReadLCacheOK s'.caches.readLC s'.store := by
  have hq := AM.of_run (P := fun t => t = s) rfl hrun (readLevelM_spec s h hrl)
  exact ⟨hq.2.2.2.2.1, hq.2.2.2.2.2⟩

/-- con-leche: none — a `readLevelM` call IS a `CacheFrame`: the record
equation is the frame above, the `readL` implication is the spec's last
conjunct, and `lvlEqC` did not move at all. -/
theorem CacheFrame.ofReadLevelM {s s' : AState} {h : LIdx} {l : Level}
    (hrun : readLevelM h s = .ok (l, s')) : CacheFrame s s' := by
  obtain ⟨hst, -, -, hc⟩ := readLevelM_frame hrun
  have hle : s'.caches.lvlEqC = s.caches.lvlEqC := by rw [hc]
  exact
    { caches := by rw [hle]; exact hc
      readL := fun hrl => (readLevelM_denote hrl hrun).2
      lvlEq := fun _ h' => by rw [hle, hst]; exact h' }

/-- con-leche: ConLeche/Kernel/Level.lean:158-163 isEquiv — **`lvlEq?`'s
FRAME**, `Bridge/StateOK.lean`'s `CacheFrame` at the one walk it was written
for: the cached level comparison writes `readLC` (twice, through `readLevelM`)
and `lvlEqC`, no other per-declaration table, and neither the store, the
per-call memos nor the pin table.

The `lvlEq` implication takes BOTH invariants, and that is not slack: the row
the miss inserts is `Level.isEquiv` of what `readLevelM` answered, so a
poisoned `readLC` would poison `lvlEqC`.  `CacheFrame`'s shape is forced by
the program. -/
theorem lvlEq?_frame {s s' : AState} {u v : LIdx} {r : Option Bool}
    (hrun : lvlEq? u v s = .ok (r, s')) :
    s'.store = s.store ∧ s'.memos = s.memos ∧ s'.pins = s.pins ∧
      CacheFrame s s' := by
  rw [lvlEq?] at hrun
  obtain ⟨t, s₁, hget, hrest⟩ := AM.bind_ok hrun
  obtain ⟨ht, hs₁⟩ := AM.get_ok hget
  rw [ht, hs₁] at hrest
  cases hhit : s.caches.lvlEqC[(u, v)]? with
  | some b =>
    -- the HIT: the probe writes nothing
    rw [hhit] at hrest
    obtain ⟨-, hs⟩ := AM.pure_ok hrest
    rw [hs]
    exact ⟨rfl, rfl, rfl, CacheFrame.refl _⟩
  | none =>
    rw [hhit] at hrest
    obtain ⟨lu, s₂, hru, hrest2⟩ := AM.bind_ok hrest
    obtain ⟨lv, s₃, hrv, hrest3⟩ := AM.bind_ok hrest2
    obtain ⟨hst1, hm1, hp1, -⟩ := readLevelM_frame hru
    obtain ⟨hst2, hm2, hp2, -⟩ := readLevelM_frame hrv
    have hf12 : CacheFrame s s₃ :=
      (CacheFrame.ofReadLevelM hru).trans (CacheFrame.ofReadLevelM hrv)
    have hst : s₃.store = s.store := hst2.trans hst1
    have hm : s₃.memos = s.memos := hm2.trans hm1
    have hp : s₃.pins = s.pins := hp2.trans hp1
    cases heq : Level.isEquiv lu lv with
    | none =>
      -- fuel exhaustion on the pure side: never cached
      rw [heq] at hrest3
      obtain ⟨-, hs⟩ := AM.pure_ok hrest3
      rw [hs]
      exact ⟨hst, hm, hp, hf12⟩
    | some b =>
      rw [heq] at hrest3
      obtain ⟨t', s₄, hget', hrest4⟩ := AM.bind_ok hrest3
      obtain ⟨ht', hs₄⟩ := AM.get_ok hget'
      rw [ht', hs₄] at hrest4
      obtain ⟨w, s₅, hset, hpure⟩ := AM.bind_ok hrest4
      have hs₅ := AM.set_ok hset
      obtain ⟨-, hs⟩ := AM.pure_ok hpure
      rw [hs]
      -- the insert's own projections, read off the `set`
      have hstore5 : s₅.store = s₃.store := by rw [hs₅]
      have hmemos5 : s₅.memos = s₃.memos := by rw [hs₅]
      have hpins5 : s₅.pins = s₃.pins := by rw [hs₅]
      have hread5 : s₅.caches.readLC = s₃.caches.readLC := by rw [hs₅]
      have hlvl5 :
          s₅.caches.lvlEqC =
            (if s₃.caches.lvlEqC.size < cacheCap then s₃.caches.lvlEqC
              else ∅).insert (u, v) b := by
        rw [hs₅]
      have hc5 :
          s₅.caches =
            { s₃.caches with
              readLC := s₅.caches.readLC
              lvlEqC := s₅.caches.lvlEqC } := by
        rw [hs₅]
      refine ⟨hstore5.trans hst, hmemos5.trans hm, hpins5.trans hp,
        ?_, ?_, ?_⟩
      · -- the record equation: the readbacks moved `readLC`, the insert
        -- moved `lvlEqC`, and nothing else moved
        refine hc5.trans ?_
        rw [hf12.caches]
      · -- `readLC` does not move across the insert
        intro hrl
        rw [hread5, hstore5]
        exact hf12.readL hrl
      · -- the row the insert writes IS the verdict at the two denotations,
        -- which is where both hypotheses are spent
        intro hrl hle
        obtain ⟨hdu, hrl2⟩ := readLevelM_denote hrl hru
        obtain ⟨hdv, -⟩ := readLevelM_denote hrl2 hrv
        rw [hlvl5, hstore5]
        exact LvlEqCacheOK.insert_capped (hf12.lvlEq hrl hle)
          (by rw [hst]; exact hdu) (by rw [hst2]; exact hdv) heq

end Frame


/-! ## 5. The axiom census

DESIGN §8's gate for every tier of this library, at this module's closed
results and at `Bridge/Core/Walks/Frame.lean`'s (which it imports): the three
standard axioms and no `sorryAx`.  The three come in through `Std.HashMap`,
`Classical` in `Option`'s lemmas and `Quot` in `String`. -/

section Census

#print axioms ReadbackFrame.refl
#print axioms ReadbackFrame.trans
#print axioms ReadbackFrame.ext
#print axioms CacheOK.ofReadbackFrame
#print axioms CheckOK.ofReadbackFrame
#print axioms ReadbackFrame.ofReadL
#print axioms ReadbackFrame.ofReadN
#print axioms ReadbackFrame.ofReadLs

#print axioms LvlEqCacheOK.insert_capped
#print axioms LvlsEqCacheOK.insert_capped
#print axioms ConstTyCacheOK.insert_capped
#print axioms ConstValCacheOK.insert_capped
#print axioms RuleRhsCacheOK.insert_capped
#print axioms CacheOK.insertLvlEq
#print axioms CacheOK.insertLvlsEq

/-! **The tier's own result**: the first two non-slot walks of
`Arena/Core.lean` with a theorem, and both sorry-free. -/
#print axioms lvlEq?_spec
#print axioms lvlsEq?_spec

/-! **The frames task #97-P3-Frame owes `PStep` and `ParseStep`**, all four
closed: the `StateOK`-graded answer to "which tables may a level comparison
have written". -/
#print axioms readLevelM_frame
#print axioms readLevelM_denote
#print axioms CacheFrame.ofReadLevelM
#print axioms lvlEq?_frame

/-! The three instantiated-constant caches — CLOSED in round 4, on
`instLPFast_spec`'s cache frame. -/
#print axioms CheckOK.ofInstLP
#print axioms denoteCV_inv
#print axioms CacheOK.insertConstTy
#print axioms CacheOK.insertConstVal
#print axioms CacheOK.insertRuleRhs
#print axioms constTyAt_spec
#print axioms constValAt_spec
#print axioms constValAt_spec'
#print axioms ruleRhsAt_spec

end Census

end ConRon.Bridge.Core

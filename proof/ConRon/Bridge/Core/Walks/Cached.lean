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

The last three were **`sorry`** when this was written (all closed since),
and for one reason each time: the miss branch
is `instLPFast`, whose callee rule is `Bridge/ExprOps/Owed.lean`'s
`instLPFast_spec` and is itself `sorry` (task #97-P3-0's open list, item "the
eight of `ExprOps/Owed.lean`").  Their proofs are otherwise the first two's,
table for table — the five insert lemmas below are written for all of them.

**No module of `Bridge/Core/Walks/` imported `Bridge/ExprOps/`** then, which
is why the three were only stated here at first: task #97-P3-1 re-stated that
tier against the split arms while this round ran.  This module has imported
`Bridge/ExprOps/Owed.lean` since round 4 (the note before `CheckOK.ofInstLP`),
and the three are proved below.

## The tier's recipe, in five steps

Read off `lvlEq?_spec` below; every cached walk follows it.

1. **`sym only [bridge_grind] => vcgen [<the walk>] <;> finish`** (task
   #123).  `Bridge/Specs.lean`'s three readback specs are `@[spec]`, so
   `vcgen` applies them by itself and each readback contributes its five
   conjuncts to the verification condition; `CheckOK.ofReadL` (and its
   sibling), a `grind` rule keyed by the readback's cache record, carries
   `CheckOK` across each, and the hit and insert lemmas of §1 close the
   branches.
   *(Under `mvcgen`, which could not be made to prefer a theorem passed in its
   list over a registered `@[spec]` — measured — this was forced; `vcgen` can
   erase a registered spec per call, `vcgen [-readLevelM_spec, …]`, task
   #111, but the frame is still assembled in the walk.)*
2. **The postcondition does not take the subjects' denotations as
   hypotheses.**  It says "*if* the walk answered `some b`, then the subjects
   denote and `Level.isEquiv` answers `b`" — task #97-P3-0's rule 4 at two
   subjects, and the reason is the hit branch: `LvlEqCacheOK` DELIVERS the
   denotations, it does not consume them.
3. **The five verification conditions are the three branches plus the two
   readbacks' preconditions**, and the two preconditions are
   `CheckOK.readL' hok` (passed to `sym`) and the first readback's own post.
4. **The insert is `LvlEqCacheOK.insert`**, a plain insert since task
   #115 removed the cap.
5. **The answer relation is none of `Bridge/Core/Walks/Spec.lean`'s.**
   The pure side of these five is not fueled at all (`Level.isEquiv` is a
   total function of two trees), so there is no `∃ F` and the conclusion is
   an equation.  That is the one structural difference between this group and
   every other group of the tier, and it is why this group is the cheap one.
-/
import ConRon.Bridge.Core.Walks.Frame
import ConRon.Bridge.Promote.Pers
import ConRon.Bridge.ExprOps.Owed
import ConRon.Bridge.Grind

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {mode : CheckMode} {env : Env} {fe : IFEnv}

/-! ## 1. The five insert lemmas

`Bridge/Core/Memo.lean`'s `EntryCacheOK.insert` for the five tables it does
not touch. -/

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:51 CSOK.insertWhnfCoreC — the
level-verdict cache's insert. -/
theorem LvlEqCacheOK.insert {tbl : Std.HashMap (LIdx × LIdx) Bool}
    {st : EStore} (h : LvlEqCacheOK tbl st) {u v : LIdx} {lu lv : Level}
    {r : Bool} (hu : denoteL st.ls u = some lu)
    (hv : denoteL st.ls v = some lv) (heq : Level.isEquiv lu lv = some r) :
    LvlEqCacheOK (tbl.insert (u, v) r)
      st := by
  have key : ∀ (t : Std.HashMap (LIdx × LIdx) Bool), LvlEqCacheOK t st →
      LvlEqCacheOK (t.insert (u, v) r) st := by
    intro t ht k x hl
    rw [Std.HashMap.getElem?_insert] at hl
    split at hl
    next hbeq =>
      cases hl
      obtain rfl := eq_of_beq hbeq
      exact ⟨lu, lv, hu, hv, heq⟩
    next => exact ht k x hl
  exact key _ h

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:51 CSOK.insertWhnfCoreC — the
same at the universe-argument LIST verdict cache. -/
theorem LvlsEqCacheOK.insert {tbl : Std.HashMap (LsIdx × LsIdx) Bool}
    {st : EStore} (h : LvlsEqCacheOK tbl st) {us vs : LsIdx}
    {lus lvs : List Level} {r : Bool}
    (hu : denoteLs st.lss us = some lus)
    (hv : denoteLs st.lss vs = some lvs)
    (heq : Level.isEquivList lus lvs = some r) :
    LvlsEqCacheOK
      (tbl.insert (us, vs) r) st := by
  have key : ∀ (t : Std.HashMap (LsIdx × LsIdx) Bool), LvlsEqCacheOK t st →
      LvlsEqCacheOK (t.insert (us, vs) r) st := by
    intro t ht k x hl
    rw [Std.HashMap.getElem?_insert] at hl
    split at hl
    next hbeq =>
      cases hl
      obtain rfl := eq_of_beq hbeq
      exact ⟨lus, lvs, hu, hv, heq⟩
    next => exact ht k x hl
  exact key _ h

/-- con-leche: none — the instantiated-constant TYPE cache's insert. -/
theorem ConstTyCacheOK.insert {tbl : Std.HashMap (NIdx × LsIdx) EIdx}
    {st : EStore} (h : ConstTyCacheOK env tbl st) {n : NIdx} {us : LsIdx}
    {i : EIdx} {nm : ConLeche.Name} {ls : List Level} {ci : ConstantInfo}
    (hn : denoteN st.ns n = some nm) (hus : denoteLs st.lss us = some ls)
    (hf : env.find? nm = some ci)
    (hi : denoteE st i = some (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams ls)) :
    ConstTyCacheOK env
      (tbl.insert (n, us) i) st := by
  have key : ∀ (t : Std.HashMap (NIdx × LsIdx) EIdx),
      ConstTyCacheOK env t st → ConstTyCacheOK env (t.insert (n, us) i) st := by
    intro t ht k j hl
    rw [Std.HashMap.getElem?_insert] at hl
    split at hl
    next hbeq =>
      cases hl
      obtain rfl := eq_of_beq hbeq
      exact ⟨nm, ls, ci, hn, hus, hf, hi⟩
    next => exact ht k j hl
  exact key _ h

/-- con-leche: none — the instantiated-constant VALUE cache's insert. -/
theorem ConstValCacheOK.insert {tbl : Std.HashMap (NIdx × LsIdx) EIdx}
    {st : EStore} (h : ConstValCacheOK env tbl st) {n : NIdx} {us : LsIdx}
    {i : EIdx} {nm : ConLeche.Name} {ls : List Level} {cv : ConstantVal}
    {value : Expr} {hint : ReducibilityHint}
    (hn : denoteN st.ns n = some nm) (hus : denoteLs st.lss us = some ls)
    (hf : env.find? nm = some (.defnInfo cv value hint))
    (hi : denoteE st i = some (value.instantiateLevelParams cv.levelParams ls)) :
    ConstValCacheOK env
      (tbl.insert (n, us) i) st := by
  have key : ∀ (t : Std.HashMap (NIdx × LsIdx) EIdx),
      ConstValCacheOK env t st →
      ConstValCacheOK env (t.insert (n, us) i) st := by
    intro t ht k j hl
    rw [Std.HashMap.getElem?_insert] at hl
    split at hl
    next hbeq =>
      cases hl
      obtain rfl := eq_of_beq hbeq
      exact ⟨nm, ls, cv, value, hint, hn, hus, hf, hi⟩
    next => exact ht k j hl
  exact key _ h

/-- con-leche: none — the ι rule right-hand-side cache's insert, at the
THREE-part key. -/
theorem RuleRhsCacheOK.insert
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
      (tbl.insert (rn, cn, us) i) st := by
  have key : ∀ (t : Std.HashMap (NIdx × NIdx × LsIdx) EIdx),
      RuleRhsCacheOK env t st →
      RuleRhsCacheOK env (t.insert (rn, cn, us) i) st := by
    intro t ht k j hl
    rw [Std.HashMap.getElem?_insert] at hl
    split at hl
    next hbeq =>
      cases hl
      obtain rfl := eq_of_beq hbeq
      exact ⟨rnv, cnv, ls, cv, mi, rp, rules, rl, hr, hc, hus, hf, hrl, hi⟩
    next => exact ht k j hl
  exact key _ h

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
      lvlEqC := s.caches.lvlEqC.insert (u, v) r } } :=
  { hc with lvlEq := LvlEqCacheOK.insert hc.lvlEq hu hv heq }

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:51 CSOK.insertWhnfCoreC. -/
theorem CacheOK.insertLvlsEq {s : AState} (hc : CacheOK mode env s)
    {us vs : LsIdx} {lus lvs : List Level} {r : Bool}
    (hu : denoteLs s.store.lss us = some lus)
    (hv : denoteLs s.store.lss vs = some lvs)
    (heq : Level.isEquivList lus lvs = some r) :
    CacheOK mode env { s with caches := { s.caches with
      lvlsEqC := s.caches.lvlsEqC.insert (us, vs) r } } :=
  { hc with lvlsEq := LvlsEqCacheOK.insert hc.lvlsEq hu hv heq }

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
      constTyC := s.caches.constTyC.insert (n, us) i } } :=
  { hc with constTy := ConstTyCacheOK.insert hc.constTy hn hus hf hi }

/-- con-leche: none — `CacheOK` past the instantiated-constant VALUE cache's
insert. -/
theorem CacheOK.insertConstVal {s : AState} (hc : CacheOK mode env s)
    {n : NIdx} {us : LsIdx} {i : EIdx} {nm : ConLeche.Name} {ls : List Level}
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hn : denoteN s.store.ns n = some nm) (hus : denoteLs s.store.lss us = some ls)
    (hf : env.find? nm = some (.defnInfo cv value hint))
    (hi : denoteE s.store i = some (value.instantiateLevelParams cv.levelParams ls)) :
    CacheOK mode env { s with caches := { s.caches with
      constValC := s.caches.constValC.insert (n, us) i } } :=
  { hc with constVal := ConstValCacheOK.insert hc.constVal hn hus hf hi }

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
      ruleRhsC := s.caches.ruleRhsC.insert (rn, cn, us) i } } :=
  { hc with ruleRhs := RuleRhsCacheOK.insert hc.ruleRhs hr hcn hus hf hrl hi }

/-! ### The five caches' hit and insert, at `CheckOK` (tasks #120, #123)

The arms of the five cache walks as `grind` lemmas (task #123, the shape of
`Bridge/Core/Memo.lean`'s): a miss arm's `CheckOK` of the inserted state is
the insert lemma, whose conclusion is the state the verification condition
names (`vcgen` folds the twin's empty-then-insert into one record update),
and a hit arm's answer is the table's clause read at the probe — an `Ans`
atom about the probe (`Bridge/Grind.lean` §3), whose equation fires at the
`some` the arm matched.  The two level caches' lemmas are registered; the
three instantiated-constant caches' are passed to `sym` instantiated at the
walk's key (their key's denotation names the environment entry, and the ι
rule's `List.find?` is a `fun` over the constructor name, which no pattern
can bind — task #122's rule), with the key's denotations at the CALL's store
and the order to the current one. -/

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:51 CSOK.insertWhnfCoreC —
`CheckOK` past the level-verdict insert. -/
theorem CheckOK.insertLvlEq {s : AState} (h : CheckOK mode env fe s)
    {u v : LIdx} {lu lv : Level} {r : Bool}
    (hu : denoteL s.store.ls u = some lu) (hv : denoteL s.store.ls v = some lv)
    (heq : Level.isEquiv lu lv = some r) :
    CheckOK mode env fe { s with caches := { s.caches with
      lvlEqC := s.caches.lvlEqC.insert (u, v) r } } :=
  CheckOK.ofCache h (CacheOK.insertLvlEq h.caches hu hv heq) rfl rfl
grind_pattern [bridge_grind] CheckOK.insertLvlEq =>
  CheckOK mode env fe s, s.caches.lvlEqC.insert (u, v) r, Level.isEquiv lu lv

/-- con-leche: ConLeche/Verify/Cached/KnotC.lean:51 CSOK.insertWhnfCoreC —
the same at the level-list verdict cache. -/
theorem CheckOK.insertLvlsEq {s : AState} (h : CheckOK mode env fe s)
    {us vs : LsIdx} {lus lvs : List Level} {r : Bool}
    (hu : denoteLs s.store.lss us = some lus) (hv : denoteLs s.store.lss vs = some lvs)
    (heq : Level.isEquivList lus lvs = some r) :
    CheckOK mode env fe { s with caches := { s.caches with
      lvlsEqC := s.caches.lvlsEqC.insert (us, vs) r } } :=
  CheckOK.ofCache h (CacheOK.insertLvlsEq h.caches hu hv heq) rfl rfl
grind_pattern [bridge_grind] CheckOK.insertLvlsEq =>
  CheckOK mode env fe s, s.caches.lvlsEqC.insert (us, vs) r, Level.isEquivList lus lvs

/-- con-leche: none — `CheckOK` past the instantiated-constant TYPE insert,
the key's denotations at an earlier store `st₀`. -/
theorem CheckOK.insertConstTy {st₀ : EStore} {n : NIdx} {us : LsIdx}
    {nm : ConLeche.Name} {ls : List Level} {ci : ConstantInfo}
    (hn : denoteN st₀.ns n = some nm) (hus : denoteLs st₀.lss us = some ls)
    (hf : env.find? nm = some ci) {s : AState} {i : EIdx}
    (h : CheckOK mode env fe s) (hx : st₀ ≤ s.store)
    (hi : denoteE s.store i = some (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams ls)) :
    CheckOK mode env fe { s with caches := { s.caches with
      constTyC := s.caches.constTyC.insert (n, us) i } } :=
  CheckOK.ofCache h (CacheOK.insertConstTy h.caches (denoteN_ext hn hx)
    (denoteLs_ext hus hx) hf hi) rfl rfl

/-- con-leche: none — `CheckOK` past the instantiated-constant VALUE
insert. -/
theorem CheckOK.insertConstVal {st₀ : EStore} {n : NIdx} {us : LsIdx}
    {nm : ConLeche.Name} {ls : List Level} {cv : ConstantVal} {value : Expr}
    {hint : ReducibilityHint}
    (hn : denoteN st₀.ns n = some nm) (hus : denoteLs st₀.lss us = some ls)
    (hf : env.find? nm = some (.defnInfo cv value hint)) {s : AState} {i : EIdx}
    (h : CheckOK mode env fe s) (hx : st₀ ≤ s.store)
    (hi : denoteE s.store i = some (value.instantiateLevelParams cv.levelParams ls)) :
    CheckOK mode env fe { s with caches := { s.caches with
      constValC := s.caches.constValC.insert (n, us) i } } :=
  CheckOK.ofCache h (CacheOK.insertConstVal h.caches (denoteN_ext hn hx)
    (denoteLs_ext hus hx) hf hi) rfl rfl

/-- con-leche: none — `CheckOK` past the ι right-hand-side insert. -/
theorem CheckOK.insertRuleRhs {st₀ : EStore} {rn cn : NIdx} {us : LsIdx}
    {rnv cnv : ConLeche.Name} {ls : List Level} {cv : ConstantVal}
    {mi rp : Nat} {rules : List RecRule} {rl : RecRule}
    (hr : denoteN st₀.ns rn = some rnv) (hcn : denoteN st₀.ns cn = some cnv)
    (hus : denoteLs st₀.lss us = some ls)
    (hf : env.find? rnv = some (.recInfo cv mi rp rules))
    (hrl : rules.find? (fun r => r.ctor == cnv) = some rl) {s : AState} {i : EIdx}
    (h : CheckOK mode env fe s) (hx : st₀ ≤ s.store)
    (hi : denoteE s.store i = some (rl.rhs.instantiateLevelParams cv.levelParams ls)) :
    CheckOK mode env fe { s with caches := { s.caches with
      ruleRhsC := s.caches.ruleRhsC.insert (rn, cn, us) i } } :=
  CheckOK.ofCache h (CacheOK.insertRuleRhs h.caches (denoteN_ext hr hx)
    (denoteN_ext hcn hx) (denoteLs_ext hus hx) hf hrl hi) rfl rfl

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — a level-verdict HIT is
`Level.isEquiv`'s verdict at the two denotations (the clause at the probe). -/
theorem CheckOK.lvlEq_hit {s : AState} (h : CheckOK mode env fe s) (u v : LIdx) :
    Ans (fun r => ∃ lu lv, denoteL s.store.ls u = some lu ∧
      denoteL s.store.ls v = some lv ∧ some r = Level.isEquiv lu lv)
      (s.caches.lvlEqC[(u, v)]?) := fun r hhit => by
  obtain ⟨lu, lv, hu, hv, he⟩ := h.caches.lvlEq (u, v) r hhit
  exact ⟨lu, lv, hu, hv, he.symm⟩
grind_pattern [bridge_grind] CheckOK.lvlEq_hit =>
  CheckOK mode env fe s, s.caches.lvlEqC[(u, v)]?

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — the same at two
universe-argument lists. -/
theorem CheckOK.lvlsEq_hit {s : AState} (h : CheckOK mode env fe s) (us vs : LsIdx) :
    Ans (fun r => ∃ lus lvs, denoteLs s.store.lss us = some lus ∧
      denoteLs s.store.lss vs = some lvs ∧ some r = Level.isEquivList lus lvs)
      (s.caches.lvlsEqC[(us, vs)]?) := fun r hhit => by
  obtain ⟨lu, lv, hu, hv, he⟩ := h.caches.lvlsEq (us, vs) r hhit
  exact ⟨lu, lv, hu, hv, he.symm⟩
grind_pattern [bridge_grind] CheckOK.lvlsEq_hit =>
  CheckOK mode env fe s, s.caches.lvlsEqC[(us, vs)]?

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK (the `constTy` clause) — a
TYPE-cache HIT denotes the constant's type at the key's levels. -/
theorem CheckOK.constTy_hit {st₀ : EStore} {n : NIdx} {us : LsIdx}
    {nm : ConLeche.Name} {ls : List Level} {ci : ConstantInfo}
    (hn : denoteN st₀.ns n = some nm) (hus : denoteLs st₀.lss us = some ls)
    (hf : env.find? nm = some ci) {s : AState}
    (h : CheckOK mode env fe s) (hx : st₀ ≤ s.store) :
    Ans (fun i => denoteE s.store i = some (ci.toConstantVal.type.instantiateLevelParams
      ci.toConstantVal.levelParams ls)) (s.caches.constTyC[(n, us)]?) := fun i hhit => by
  obtain ⟨nm', ls', ci', hn', hus', hf', hd⟩ := h.caches.constTy _ i hhit
  obtain rfl := Option.some.inj ((denoteN_ext hn hx).symm.trans hn')
  obtain rfl := Option.some.inj ((denoteLs_ext hus hx).symm.trans hus')
  obtain rfl := Option.some.inj (hf.symm.trans hf')
  exact hd

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — a VALUE-cache HIT. -/
theorem CheckOK.constVal_hit {st₀ : EStore} {n : NIdx} {us : LsIdx}
    {nm : ConLeche.Name} {ls : List Level} {cv : ConstantVal} {val : Expr}
    {hint : ReducibilityHint}
    (hn : denoteN st₀.ns n = some nm) (hus : denoteLs st₀.lss us = some ls)
    (hf : env.find? nm = some (.defnInfo cv val hint)) {s : AState}
    (h : CheckOK mode env fe s) (hx : st₀ ≤ s.store) :
    Ans (fun i => denoteE s.store i = some (val.instantiateLevelParams cv.levelParams ls))
      (s.caches.constValC[(n, us)]?) := fun i hhit => by
  obtain ⟨nm', ls', cv', val', hint', hn', hus', hf', hd⟩ := h.caches.constVal _ i hhit
  obtain rfl := Option.some.inj ((denoteN_ext hn hx).symm.trans hn')
  obtain rfl := Option.some.inj ((denoteLs_ext hus hx).symm.trans hus')
  rw [hf] at hf'
  cases hf'
  exact hd

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — a rule-RHS-cache HIT. -/
theorem CheckOK.ruleRhs_hit {st₀ : EStore} {rn cn : NIdx} {us : LsIdx}
    {rnv cnv : ConLeche.Name} {ls : List Level} {cv : ConstantVal}
    {mi rp : Nat} {rules : List RecRule} {rl : RecRule}
    (hr : denoteN st₀.ns rn = some rnv) (hcn : denoteN st₀.ns cn = some cnv)
    (hus : denoteLs st₀.lss us = some ls)
    (hf : env.find? rnv = some (.recInfo cv mi rp rules))
    (hrl : rules.find? (fun r => r.ctor == cnv) = some rl) {s : AState}
    (h : CheckOK mode env fe s) (hx : st₀ ≤ s.store) :
    Ans (fun i => denoteE s.store i = some (rl.rhs.instantiateLevelParams cv.levelParams ls))
      (s.caches.ruleRhsC[(rn, cn, us)]?) := fun i hhit => by
  obtain ⟨rn', cn', ls', cv', mi', rp', rules', rl', hr', hc', hus', hf', hrl', hd⟩ :=
    h.caches.ruleRhs _ i hhit
  obtain rfl := Option.some.inj ((denoteN_ext hr hx).symm.trans hr')
  obtain rfl := Option.some.inj ((denoteN_ext hcn hx).symm.trans hc')
  obtain rfl := Option.some.inj ((denoteLs_ext hus hx).symm.trans hus')
  rw [hf] at hf'
  cases hf'
  rw [hrl] at hrl'
  cases hrl'
  exact hd

/-! ## 2. `lvlEq?` — the tier's exemplar, CLOSED -/

/-- con-leche: none — `CheckOK`'s level-readback table: the first
readback's precondition, passed to `sym` at the walk's initial state (as a
registered forward rule it would fire at every `CheckOK` of every walk). -/
theorem CheckOK.readL' {s : AState} (h : CheckOK mode env fe s) :
    ReadLCacheOK s.caches.readLC s.store := h.caches.readL

/-- con-leche: none — the same at the level-list readback table. -/
theorem CheckOK.readLs' {s : AState} (h : CheckOK mode env fe s) :
    ReadLsCacheOK s.caches.readLsC s.store := h.caches.readLs

/-- con-leche: none — `CheckOK` past ONE level readback (`readLevelM_spec`'s
frame conjuncts and its table's invariant); its pattern is the readback's
cache record, which names both states, and the invariant before. -/
theorem CheckOK.ofReadL {s0 s1 : AState} (h : CheckOK mode env fe s0)
    (hst : s1.store = s0.store) (hm : s1.memos = s0.memos) (hp : s1.pins = s0.pins)
    (hc : s1.caches = { s0.caches with readLC := s1.caches.readLC })
    (hL : ReadLCacheOK s1.caches.readLC s1.store) : CheckOK mode env fe s1 :=
  CheckOK.ofReadbackFrame h (ReadbackFrame.ofReadL hst hm hp hc hL)
grind_pattern [bridge_grind] CheckOK.ofReadL =>
  -- the readback's cache record (it names both states); the ascription is
  -- needed (`_tmp/corpus/vcgen-grind/struct-update-pattern.lean`)
  ({ s0.caches with readLC := s1.caches.readLC } : Caches), CheckOK mode env fe s0

/-- con-leche: none — the same past one level-LIST readback. -/
theorem CheckOK.ofReadLs {s0 s1 : AState} (h : CheckOK mode env fe s0)
    (hst : s1.store = s0.store) (hm : s1.memos = s0.memos) (hp : s1.pins = s0.pins)
    (hc : s1.caches = { s0.caches with readLsC := s1.caches.readLsC })
    (hL : ReadLsCacheOK s1.caches.readLsC s1.store) : CheckOK mode env fe s1 :=
  CheckOK.ofReadbackFrame h (ReadbackFrame.ofReadLs hst hm hp hc hL)
grind_pattern [bridge_grind] CheckOK.ofReadLs =>
  ({ s0.caches with readLsC := s1.caches.readLsC } : Caches), CheckOK mode env fe s0

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
    ⦃fun s => s = s₀⦄ lvlEq? u v
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧
        ∃ lu lv, denoteL s₀.store.ls u = some lu ∧
          denoteL s₀.store.ls v = some lv ∧
          r = Level.isEquiv lu lv; ⊤⦄ := by
  sym only [bridge_grind, CheckOK.readL' hok] =>
    vcgen [lvlEq?] <;> finish

/-- con-leche: ConLeche/Kernel/Level.lean:165-172 Level.isEquivList —
**THEOREM 1 for `lvlsEq?`**.  Five verification conditions, the same five,
with `CheckOK.ofReadLs` in place of `.ofReadL`. -/
theorem lvlsEq?_spec (s₀ : AState) (us vs : LsIdx)
    (hok : CheckOK mode env fe s₀) :
    ⦃fun s => s = s₀⦄ lvlsEq? us vs
    ⦃fun r s' => CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧
        ∃ lus lvs, denoteLs s₀.store.lss us = some lus ∧
          denoteLs s₀.store.lss vs = some lvs ∧
          r = Level.isEquivList lus lvs; ⊤⦄ := by
  sym only [bridge_grind, CheckOK.readLs' hok] =>
    vcgen [lvlsEq?] <;> finish

/-! ## 4. The three instantiated-constant caches — CLOSED (round 4)

The miss branch is `instLPFast`, and `Bridge/ExprOps/Owed.lean`'s
`instLPFast_spec` now carries the cache frame (a record equation naming
`readLC`/`readNC`/`readLsC`) and `ReadNCacheOK` — task #97-P3-1 round 4, the
answer to this tier's finding 19.  `CheckOK.ofInstLP` turns the two into
`CheckOK` past the call; the insert is the one above.  This module
imports `Bridge/ExprOps/Owed.lean` since round 4 (the derived-auxiliary wall
of finding 18 is gone). -/

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
      whnfCoreCheap := by rw [hc]; exact hok.caches.whnfCoreCheap.mono hx
      whnf := by rw [hc]; exact hok.caches.whnf.mono hx
      infer := by rw [hc]; exact hok.caches.infer.mono hx
      inferIO := by rw [hc]; exact hok.caches.inferIO.mono hx
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
grind_pattern [bridge_grind] CheckOK.ofInstLP =>
  CheckOK mode env fe s₀, ReadNCacheOK s'.caches.readNC s'.store

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
    ⦃fun s => s = s₀⦄ constTyAt cv us
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteE s'.store r =
          some (ci.toConstantVal.type.instantiateLevelParams
            ci.toConstantVal.levelParams ls); ⊤⦄ := by
  obtain ⟨_hnm, hlps, hty⟩ := denoteCV_inv hcv
  sym only [bridge_grind, CheckOK.insertConstTy (fe := fe) hn hus hf,
      → CheckOK.constTy_hit (fe := fe) hn hus hf] =>
    vcgen [constTyAt,
      ExprOps.instLPFast_spec coreWalkFuel s₀ cv.levelParams us cv.type
        _ _ hok.state hok.caches.readN hok.caches.readL hok.caches.readLs hlps hus
        (by rw [hty]; rfl)] <;> finish

/-- con-leche: none — `constTyAt_spec` in ANSWER shape: the constant comes
out of the environment index (`projCert` reads it off `fe.find?`), so its
denotation is not known when `vcgen` applies the spec. -/
theorem constTyAt_spec' (s₀ : AState) (cv : IConstantVal) (us : LsIdx)
    (hok : CheckOK mode env fe s₀)
    (hpre : ∃ nm ls ci, denoteN s₀.store.ns cv.name = some nm ∧
      denoteLs s₀.store.lss us = some ls ∧ env.find? nm = some ci ∧
      Frontend.denoteCV s₀.store cv = some ci.toConstantVal) :
    ⦃fun s => s = s₀⦄ constTyAt cv us
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ nm ls ci, denoteN s₀.store.ns cv.name = some nm →
          denoteLs s₀.store.lss us = some ls → env.find? nm = some ci →
          denoteE s'.store r =
            some (ci.toConstantVal.type.instantiateLevelParams
              ci.toConstantVal.levelParams ls); ⊤⦄ := by
  obtain ⟨nm, ls, ci, hn, hus, hf, hcv⟩ := hpre
  sym only [bridge_grind] =>
    vcgen [constTyAt_spec s₀ cv us nm ls ci hok hn hus hf hcv] <;> finish

/-- con-leche: none — **THEOREM 1 for `constValAt`** (the delta step's
expensive half, and the reason `unfoldDefinition` is not free).  **CLOSED**
(round 4). -/
theorem constValAt_spec (s₀ : AState) (n : NIdx) (lps : List NIdx)
    (value : EIdx) (us : LsIdx) (nm : ConLeche.Name) (ls : List Level)
    (cv : ConstantVal) (val : Expr) (hint : ReducibilityHint)
    (hok : CheckOK mode env fe s₀)
    (hn : denoteN s₀.store.ns n = some nm)
    (hus : denoteLs s₀.store.lss us = some ls)
    (hlps : Frontend.denoteNList s₀.store.ns lps = some cv.levelParams)
    (hval : denoteE s₀.store value = some val)
    (hfd : env.find? nm = some (.defnInfo cv val hint)) :
    ⦃fun s => s = s₀⦄ constValAt n lps value us
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteE s'.store r =
          some (val.instantiateLevelParams cv.levelParams ls); ⊤⦄ := by
  sym only [bridge_grind, CheckOK.insertConstVal (fe := fe) hn hus hfd,
      → CheckOK.constVal_hit (fe := fe) hn hus hfd] =>
    vcgen [constValAt,
      ExprOps.instLPFast_spec coreWalkFuel s₀ lps us value
        _ _ hok.state hok.caches.readN hok.caches.readL hok.caches.readLs hlps hus
        (by rw [hval]; rfl)] <;> finish

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
    ⦃fun s => s = s₀⦄ constValAt n lps value us
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        ∀ nm ls cv val hint, denoteN s₀.store.ns n = some nm →
          denoteLs s₀.store.lss us = some ls →
          env.find? nm = some (.defnInfo cv val hint) →
          denoteE s'.store r =
            some (val.instantiateLevelParams cv.levelParams ls); ⊤⦄ := by
  obtain ⟨nm, ls, cv, val, hint, hn, hus, hlps, hval, hfd⟩ := hpre
  sym only [bridge_grind] =>
    vcgen [constValAt_spec s₀ n lps value us nm ls cv val hint hok hn hus
      hlps hval hfd] <;> finish

/-- con-leche: none — **THEOREM 1 for `ruleRhsAt`** (an ι rule's right-hand
side at the recursor's universe instantiation).  **CLOSED** (round 4). -/
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
    ⦃fun s => s = s₀⦄ ruleRhsAt recName ctor lps rhs us
    ⦃fun r s' => CheckOK mode env fe s' ∧ Ext s₀.store s'.store ∧
        s'.pins = s₀.pins ∧
        denoteE s'.store r =
          some (rl.rhs.instantiateLevelParams cv.levelParams ls); ⊤⦄ := by
  sym only [bridge_grind, CheckOK.insertRuleRhs (fe := fe) hr hc hus hfr hrl,
      → CheckOK.ruleRhs_hit (fe := fe) hr hc hus hfr hrl] =>
    vcgen [ruleRhsAt,
      ExprOps.instLPFast_spec coreWalkFuel s₀ lps us rhs
        _ _ hok.state hok.caches.readN hok.caches.readL hok.caches.readLs hlps hus
        (by rw [hrhs]; rfl)] <;> finish

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
applied it rather than unfolding `readLevelM`, and its hypothesis
(`ReadLCacheOK s₀.caches.readLC s₀.store`) then appeared as a verification
condition a `StateOK`-graded proof cannot discharge.  A registered `[spec]`
cannot be erased globally (`attribute [-spec]` is rejected) and `mvcgen` could
not be made to prefer a locally supplied theorem — `Frame.lean`'s note
measured both.  (`vcgen` erases a spec PER CALL — `vcgen [lvlEq?,
-readLevelM_spec, readLevelM]` leaves no `ReadLCacheOK` condition, checked
by task #111 — so a triple form is now possible; the run form stays because
it is what `Bridge/Inductives/Rel.lean` consumes.)  Taking the two do-blocks
apart by hand costs twenty lines and commits to nothing.

**Why the two implications' hypotheses are at the INITIAL state.**  The frame
is NOT assembled as "the two readbacks, then the insert" by `CacheFrame.trans`,
because the insert's own `lvlEq` obligation needs the two handles'
DENOTATIONS, and those come from `readLevelM_spec` at `s` — a fact the
intermediate state's `ReadLCacheOK` does not re-deliver.  So the whole miss
branch is one `CacheFrame` whose implications quantify over `s`, and the
readbacks' half of it is the only part that composes. -/

section Frame

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
  have hn : s'.caches.readNC = s.caches.readNC := by rw [hc]
  have hls : s'.caches.readLsC = s.caches.readLsC := by rw [hc]
  exact
    { caches := by rw [hle, hn, hls]; exact hc
      readL := fun hrl => (readLevelM_denote hrl hrun).2
      lvlEq := fun _ h' => by rw [hle, hst]; exact h'
      readN := fun h' => by rw [hn, hst]; exact h'
      readLs := fun h' => by rw [hls, hst]; exact h' }

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
      have hreadN5 : s₅.caches.readNC = s₃.caches.readNC := by rw [hs₅]
      have hreadLs5 : s₅.caches.readLsC = s₃.caches.readLsC := by rw [hs₅]
      have hlvl5 :
          s₅.caches.lvlEqC =
            s₃.caches.lvlEqC.insert (u, v) b := by
        rw [hs₅]
      have hc5 :
          s₅.caches =
            { s₃.caches with
              readLC := s₅.caches.readLC
              lvlEqC := s₅.caches.lvlEqC } := by
        rw [hs₅]
      refine ⟨hstore5.trans hst, hmemos5.trans hm, hpins5.trans hp,
        ?_, ?_, ?_, ?_, ?_⟩
      · -- the record equation: the readbacks moved `readLC`, the insert
        -- moved `lvlEqC`, and nothing else moved
        refine hc5.trans ?_
        rw [hreadN5, hreadLs5]
        conv => lhs; rw [hf12.caches]
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
        exact LvlEqCacheOK.insert (hf12.lvlEq hrl hle)
          (by rw [hst]; exact hdu) (by rw [hst2]; exact hdv) heq
      · intro hn
        rw [hreadN5, hstore5]
        exact hf12.readN hn
      · intro hn
        rw [hreadLs5, hstore5]
        exact hf12.readLs hn

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

#print axioms LvlEqCacheOK.insert
#print axioms LvlsEqCacheOK.insert
#print axioms ConstTyCacheOK.insert
#print axioms ConstValCacheOK.insert
#print axioms RuleRhsCacheOK.insert
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
#print axioms constTyAt_spec'
#print axioms ruleRhsAt_spec

end Census

/-- con-leche: ConLeche/Verify/EnvWF.lean ConstWF — a stored constant's type
has no free variables, after any level instantiation (con-leche's own copy,
`Verify/InferLemmas.lean`'s `const_ty_hasFvar`, was retired upstream as
census-dead; the bridge's walks read it at the projection certificate, the
ι recursor's type and the η family's former). -/
theorem const_ty_hasFvar {env : Env} (henv : ConLeche.EnvWF env)
    {n : ConLeche.Name} {ci : ConstantInfo} (hf : env.find? n = some ci)
    (us : List Level) :
    (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams
      us).hasFvar = false := by
  have hwf := henv _ (List.mem_of_find?_eq_some hf)
  rw [Expr.hasFvar_instantiateLevelParams]
  exact hwf.1

end ConRon.Bridge.Core

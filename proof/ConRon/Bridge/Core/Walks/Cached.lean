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

1. **Open with `simp only [<the walk>, readLevelM_eq, …]`**, not with
   `mvcgen [<the walk>]`: `Bridge/Core/Walks/Frame.lean`'s module note says
   why (a registered `@[spec]` beats unfolding, and the frame is exactly what
   the registered one omits).
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

/-! ## 2. `lvlEq?` — the tier's exemplar, CLOSED -/

/-- con-leche: ConLeche/Kernel/Level.lean:158-163 Level.isEquiv — **THEOREM 1
for `lvlEq?`**, the first `Arena/Core.lean` walk that is not a knot slot to
have one.

The verdict the walk answers is `Level.isEquiv`'s at the two handles'
denotations, and the state keeps `CheckOK` with the store and the pins
untouched.  `none` is con-leche's own fuel exhaustion inside `isEquiv` and
claims nothing — which is why the last conjunct is an implication out of
`r = some b` rather than an equation on `r`. -/
theorem lvlEq?_spec (s₀ : AState) (u v : LIdx) (hok : CheckOK mode env fe s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ lvlEq? u v
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧
        ∀ b, r = some b → ∃ lu lv, denoteL s₀.store.ls u = some lu ∧
          denoteL s₀.store.ls v = some lv ∧
          Level.isEquiv lu lv = some b⌝⦄ := by
  simp only [lvlEq?, readLevelM_eq]
  mvcgen [readLevelMB_frame]
  case vc1 =>
    bridge_peel; subst_vars
    rename_i hhit
    refine ⟨hok, rfl, rfl, ?_⟩
    intro b hb
    obtain rfl := Option.some.inj hb
    exact hok.caches.lvlEq (u, v) _ hhit
  case vc2 => bridge_peel; subst_vars; exact hok.caches.readL
  case vc3 =>
    bridge_peel; subst_vars
    rename_i _ _ hf1
    exact (CheckOK.ofReadbackFrame hok hf1).caches.readL
  case vc4 =>
    bridge_peel; subst_vars
    rename_i heq _sf hdu hf1 hdv hf2
    have hf := hf1.trans hf2
    have hck := CheckOK.ofReadbackFrame hok hf
    refine ⟨CheckOK.ofCache hck
        (CacheOK.insertLvlEq hck.caches ?_ ?_ heq) rfl rfl,
      hf.store, hf.pins, ?_⟩
    · rw [hf.store]; exact hdu
    · rw [hf2.store]; exact hdv
    · intro b hb
      obtain rfl := Option.some.inj hb
      exact ⟨_, _, hdu, by rw [← hf1.store]; exact hdv, heq⟩
  case vc5 =>
    bridge_peel; subst_vars
    rename_i _heq _sf _hdu hf1 _hdv hf2
    have hf := hf1.trans hf2
    exact ⟨CheckOK.ofReadbackFrame hok hf, hf.store, hf.pins,
      fun b hb => absurd hb (by simp)⟩

/-! ## 3. `lvlsEq?` — the same at two universe-argument lists, CLOSED -/

/-- con-leche: ConLeche/Kernel/Level.lean:165-172 Level.isEquivList —
**THEOREM 1 for `lvlsEq?`**.  Five verification conditions, the same five,
with `readLevelsMB_frame` in place of `readLevelMB_frame`. -/
theorem lvlsEq?_spec (s₀ : AState) (us vs : LsIdx)
    (hok : CheckOK mode env fe s₀) :
    ⦃fun s => ⌜s = s₀⌝⦄ lvlsEq? us vs
    ⦃⇓? r s' => ⌜CheckOK mode env fe s' ∧ s'.store = s₀.store ∧
        s'.pins = s₀.pins ∧
        ∀ b, r = some b → ∃ lus lvs, denoteLs s₀.store.lss us = some lus ∧
          denoteLs s₀.store.lss vs = some lvs ∧
          Level.isEquivList lus lvs = some b⌝⦄ := by
  simp only [lvlsEq?, readLevelsM_eq]
  mvcgen [readLevelsMB_frame]
  case vc1 =>
    bridge_peel; subst_vars
    rename_i hhit
    refine ⟨hok, rfl, rfl, ?_⟩
    intro b hb
    obtain rfl := Option.some.inj hb
    exact hok.caches.lvlsEq (us, vs) _ hhit
  case vc2 => bridge_peel; subst_vars; exact hok.caches.readLs
  case vc3 =>
    bridge_peel; subst_vars
    rename_i _ _ hf1
    exact (CheckOK.ofReadbackFrame hok hf1).caches.readLs
  case vc4 =>
    bridge_peel; subst_vars
    rename_i heq _sf hdu hf1 hdv hf2
    have hf := hf1.trans hf2
    have hck := CheckOK.ofReadbackFrame hok hf
    refine ⟨CheckOK.ofCache hck
        (CacheOK.insertLvlsEq hck.caches ?_ ?_ heq) rfl rfl,
      hf.store, hf.pins, ?_⟩
    · rw [hf.store]; exact hdu
    · rw [hf2.store]; exact hdv
    · intro b hb
      obtain rfl := Option.some.inj hb
      exact ⟨_, _, hdu, by rw [← hf1.store]; exact hdv, heq⟩
  case vc5 =>
    bridge_peel; subst_vars
    rename_i _heq _sf _hdu hf1 _hdv hf2
    have hf := hf1.trans hf2
    exact ⟨CheckOK.ofReadbackFrame hok hf, hf.store, hf.pins,
      fun b hb => absurd hb (by simp)⟩

/-! ## 4. The three instantiated-constant caches

**OPEN**, all three, and for one reason: the miss branch is `instLPFast`,
whose callee rule is `Bridge/ExprOps/Owed.lean`'s `instLPFast_spec` — itself
`sorry` at task #97-P3-0's open list, and re-stated by task #97-P3-1's arm
split while this round ran.  The insert lemmas above are written; what each
proof needs is the one call's spec and nothing else. -/

/-- con-leche: none — **THEOREM 1 for `constTyAt`** (DESIGN §8.3's
instantiated-constant TYPE cache).  **OPEN**: needs
`Bridge/ExprOps/Owed.lean`'s `instLPFast_spec`, then
`ConstTyCacheOK.insert_capped` above and `lvlEq?_spec`'s five-verification-
condition shape. -/
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
  sorry

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
  sorry

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
  sorry

end ConRon.Bridge.Core

/-
# `ConRon.Bridge.Checker.Names` — the reserved-name list, and the two readers
under it

**Why this module exists** (task #97-P3-Layout).  `reservedBasisNames_run`
below is read by two tiers that do not see each other.  The checker tier's
`Bridge/Checker/Base.lean` uses it for `checkConstantVal_bridge`'s second
guard; the inductive tier's `Bridge/Inductives/StructParts.lean` needs it for
`structPartsCore?_spec`, `structPartsCore?_isSome` and `nativeShape?_spec` —
`structPartsCore?` tests `reserved.contains T`, `reserved.contains C` and
`reserved.contains cvR.name`, and `nativeShape?` tests two of the same.  It
used to live in `Base.lean`, which `Bridge/Inductives/**` does not import and
must not (the checker tier's `.indDecl` arm imports the inductive tier back),
so those three statements were blocked on an import wall with no missing
proof (task #97-P3-Ind round 5, §R5.5 item 1).

Restating it in the inductive tier was not an option: round 3 of the checker
tier measured `reservedBasisNames_run` at **63 seconds** in its first shape,
and the note on the theorem below is where that lesson is written down.  So
the theorem moved DOWN instead, to the one place both tiers already see —
`Bridge/Checker/Inv.lean` plus `Bridge/Specs.lean`, which is the common
prefix of `Bridge/Checker/Hyp.lean` (what `Base.lean` imports) and of
`Bridge/Inductives/Rel.lean`'s imports.

**What came with it**, because none of it can be restated any more cheaply
than the theorem itself:

| | |
|---|---|
| `pinAt_run` | the pin-table reader — six of the nineteen steps |
| `PinStep` and its three laws | the frame every step shares |
| `internName_run` | the intern — thirteen of the nineteen steps |
| `denoteNL_snoc` | the shape the note forbids, kept because the fact is right |
| `denoteNL_toList`, `reservedBasisNameValues_eq` | the two equations a CONSUMER of the answer needs |
| `denoteNList_contains` | and the third: a handle `List.contains` is a name `List.contains` |

Nothing else moved and no proof changed: `Base.lean` imports this module, so
every one of its old readers still reads the same theorem.

**The second move** (task #97-P3-Checker round 9, on the coordinator's
request): the two memoised front-door walks, `allLevelParamsDefined_run` and
`constsResolveFFast_run`, which the inductive tier's `checkStructProjTable`,
`checkProjTy`, `nestedRuleShape` and `nativeOpenedOk` statements (and through
them `checkNativeTable`, `nativeFieldsOk` and the projection-install chain)
read and could not import.  The whole cone came, verbatim, from `Base.lean`'s
section "The memoised DAG walks of the front door":

| | |
|---|---|
| `LPDMemoOK` and its two laws, `lpdClose`, `allLevelParamsDefinedGo_run` | the level-parameter walk |
| `readNames_run`, `readLevel_run`, `readLevels_run` | the three read-only readers it uses |
| `IFEnvOK.find_isSome`, `constsResolve_run` | the pure resolution walk |
| `CRMemoOK` and its two laws, `crLeaf`, `constsResolveFGo_run` | the memoised one |

It needs `viewE_run`, which lives in `Bridge/Checker/Hyp.lean`; that module is
already in both tiers' import prefix (`Base.lean` and `Bridge/Inductives/
Rel.lean` both import it) and imports nothing of this one, so this module now
imports it.
-/
import ConRon.Bridge.Checker.Inv
import ConRon.Bridge.Specs
import ConRon.Bridge.Checker.Hyp

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## The pin-table reader -/

/-- con-leche: none — `pinAt` in run form, off `Bridge/Specs.lean`'s triple.

It sat beside `PinStep` until round 4, which moved it above
`constsResolve_run` (whose literal arms read pins); task #97-P3-Layout brought
it back down here with the chain that needs it, and `Base.lean` imports this
module, so `constsResolve_run` still sees it. -/
theorem pinAt_run {i : Nat} {s s' : AState} {n : NIdx} {x : ConLeche.Name}
    (hp : PinsOK s) (hx : pinNames[i]? = some x)
    (hr : pinAt i s = .ok (n, s')) :
    s' = s ∧ denoteN s.store.ns n = some x := by
  have h := AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ ∀ y, pinNames[i]? = some y →
      denoteN s.store.ns r = some y) rfl hr (pinAt_spec s i hp)
  exact ⟨h.1, h.2 x hx⟩
/-! ## The reserved-name list, interned

`Arena/Core.lean`'s `reservedBasisNames` IS `Arena/Pins.lean`'s
`pinReserved`, as the port's `reserved_basis_names` is `pin_reserved` (task
#97-T2-LOCKSTEP step 1, twin fix D5; before it the twin re-interned thirteen
of the nineteen names on every call).  So its run lemma is
`pinReserved_spec` read at `PinsOK`, and the state does not move.

`PinStep` is kept as the lemma's frame (a table read is the reflexive step)
so that its readers did not change. -/

/-- con-leche: none — one more denoting handle at the end of a denoting list.

The chain below no longer uses it: an accumulated `hs ++ [h]` is what made
`reservedBasisNames_run` a 63-second theorem (see its note), so the rule for
this tier is to carry the per-step facts and assemble the list once.  It is
kept because the fact itself is right, and because the rule is easier to state
next to the shape it forbids. -/
theorem denoteNL_snoc {st : EStore} :
    ∀ (hs : List NIdx) (xs : List ConLeche.Name) (h : NIdx) (x : ConLeche.Name),
      denoteNL st hs xs → denoteN st.ns h = some x →
        denoteNL st (hs ++ [h]) (xs ++ [x]) := by
  intro hs
  induction hs with
  | nil =>
    intro xs h x hd hn
    cases xs with
    | nil => exact ⟨hn, trivial⟩
    | cons _ _ => exact hd.elim
  | cons a as ih =>
    intro xs h x hd hn
    cases xs with
    | nil => exact hd.elim
    | cons y ys => exact ⟨hd.1, ih ys h x hd.2 hn⟩

/-- con-leche: none — the frame a pin read or a name intern leaves: the store
only grew, and nothing else moved. -/
structure PinStep (s s' : AState) : Prop where
  wf : StoreWF s'.store
  ext : Ext s.store s'.store
  memos : s'.memos = s.memos
  caches : s'.caches = s.caches
  pins : s'.pins = s.pins

theorem PinStep.refl {s : AState} (h : StoreWF s.store) : PinStep s s :=
  ⟨h, Ext.refl _, rfl, rfl, rfl⟩

theorem PinStep.trans {a b c : AState} (h₁ : PinStep a b) (h₂ : PinStep b c) :
    PinStep a c :=
  ⟨h₂.wf, h₁.ext.trans h₂.ext, by rw [h₂.memos, h₁.memos],
    by rw [h₂.caches, h₁.caches], by rw [h₂.pins, h₁.pins]⟩

theorem PinStep.pinsOK {s s' : AState} (h : PinStep s s') (hp : PinsOK s) :
    PinsOK s' := hp.mono h.ext h.pins

/-- con-leche: none — `internName` in run form, off `Bridge/Specs.lean`'s
triple. -/
theorem internName_run {nm : ConLeche.Name} {s s' : AState} {n : NIdx}
    (hwf : StoreWF s.store) (hr : internName nm s = .ok (n, s')) :
    PinStep s s' ∧ denoteN s'.store.ns n = some nm := by
  have h := AM.of_run (P := fun t => t = s)
    (Q := fun r t => StoreWF t.store ∧ Ext s.store t.store ∧
        t.store.pers = s.store.pers ∧ t.store.scr = s.store.scr ∧
        t.store.scratchOn = s.store.scratchOn ∧
        t.memos = s.memos ∧ t.caches = s.caches ∧ t.pins = s.pins ∧
        denoteN t.store.ns r = some nm) rfl hr (internName_spec s nm hwf)
  obtain ⟨h1, h2, _, _, _, h6, h7, h8, h9⟩ := h
  exact ⟨⟨h1, h2, h6, h7, h8⟩, h9⟩

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames —
**the nineteen reserved names, as handles that denote them**, off the pin
table (`pinReserved_spec`): the state does not move, so the frame is
`PinStep.refl`, and the answer is `denoteNL` at con-leche's own list.

(Before twin fix D5 this was a nineteen-step chain, six pin reads and thirteen
interns, whose first shape cost 63 s by accumulating the list along the chain;
the lesson — never accumulate a list-indexed invariant along a do-block chain
— stands, and is written in DESIGN.md's task #97-P3-Checker-3.) -/
theorem reservedBasisNames_run {s s' : AState} {hs : List NIdx}
    (hwf : StoreWF s.store) (hp : PinsOK s)
    (hr : reservedBasisNames s = .ok (hs, s')) :
    PinStep s s' ∧ denoteNL s'.store hs reservedBasisNameValues := by
  simp only [Arena.reservedBasisNames] at hr
  have h := AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ denoteNL s.store r reservedBasisNameValues)
    rfl hr (pinReserved_spec s hp)
  obtain ⟨rfl, hd⟩ := h
  exact ⟨PinStep.refl hwf, hd⟩

/-! ## The name-list denotation, as a function -/

/-- con-leche: none — `denoteNL` (the relation `PinsOK` is stated with) and
`Frontend.denoteNList` (the function everything else is stated with) are the
same fact. -/
theorem denoteNL_toList {st : EStore} :
    ∀ (hs : List NIdx) (xs : List ConLeche.Name),
      denoteNL st hs xs → Frontend.denoteNList st.ns hs = some xs := by
  intro hs
  induction hs with
  | nil => intro xs h; cases xs with
    | nil => rfl
    | cons _ _ => exact h.elim
  | cons a as ih =>
    intro xs h
    cases xs with
    | nil => exact h.elim
    | cons y ys =>
      simp only [Frontend.denoteNList, h.1, ih ys h.2]

/-- con-leche: ConLeche/Kernel/Basis/Names.lean:109-119 reservedBasisNames —
the arena's copy of the reserved list IS con-leche's, on the nose. -/
theorem reservedBasisNameValues_eq :
    reservedBasisNameValues = ConLeche.reservedBasisNames := rfl
/-! ## The name-list denotation, at a membership test -/

/-- con-leche: none — **a handle comparison is a name comparison, at a LIST**:
`List.contains` over handles answers what `List.contains` over the denoted
names answers.  Both directions are needed and they come from different
places — `denoteN` is a function (handles equal ⇒ names equal) and it is
INJECTIVE (names equal ⇒ handles equal), which is DESIGN §8.3's soundness
obligation cashed. -/
theorem denoteNList_contains {st : EStore} (hwf : StoreWF st) :
    ∀ (ns : List NIdx) (xs : List ConLeche.Name),
      Frontend.denoteNList st.ns ns = some xs →
      ∀ (n : NIdx) (x : ConLeche.Name), denoteN st.ns n = some x →
        ns.contains n = xs.contains x := by
  obtain ⟨rk, hrk⟩ := hwf
  have hns : NStoreWF st.ns := hrk.nsWF
  intro ns
  induction ns with
  | nil => intro xs h n x _; simp only [Frontend.denoteNList, Option.some.injEq] at h
           subst h; rfl
  | cons a as ih =>
    intro xs h n x hx
    simp only [Frontend.denoteNList] at h
    cases ha : denoteN st.ns a with
    | none => rw [ha] at h; simp at h
    | some y =>
      cases has : Frontend.denoteNList st.ns as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        simp only [Option.some.injEq] at h
        subst h
        have hhead : (n == a) = (x == y) := by
          by_cases hae : a = n
          · subst hae
            rw [hx] at ha
            obtain rfl := Option.some.inj ha
            simp
          · have hae' : ¬ n = a := fun hh => hae hh.symm
            have hne' : ¬ x = y := by
              intro hxy; subst hxy
              exact hae (denoteN_inj hns ha hx)
            rw [beq_eq_false_iff_ne.mpr hae', beq_eq_false_iff_ne.mpr hne']
        simp only [List.contains_cons, hhead, ih ys has n x hx]

/-! ## The memoised DAG walks of the front door -/

/-- con-leche: ConLeche/Kernel/Level.lean:299-332 Expr.allLevelParamsDefinedGo
— the memo invariant of `allLevelParamsDefinedGo`: a recorded answer is the
real one.  `Bridge/StateOK.lean`'s `MemoVOK` shape at an explicitly threaded
table (the walk does not use `Monad.lean`'s `Memos`: its answer depends on the
parameter LIST, which is a per-call datum). -/
def LPDMemoOK (params : List ConLeche.Name) (tbl : Std.HashMap EIdx Bool)
    (st : EStore) : Prop :=
  ∀ k v, tbl[k]? = some v →
    ∃ e, denoteE st k = some e ∧ v = Expr.allLevelParamsDefined params e

/-! ### The three read-only readers, in run form -/

/-- con-leche: none — `readNames`'s inversion, off `Bridge/Specs.lean`'s
triple. -/
theorem readNames_run {hs : List NIdx} {xs : List ConLeche.Name}
    {s s' : AState} (hr : readNames hs s = .ok (xs, s')) :
    s' = s ∧ Frontend.denoteNList s.store.ns hs = some xs :=
  AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ Frontend.denoteNList s.store.ns hs = some r) rfl hr
    (readNames_spec s hs)

/-- con-leche: none — `readLevel`'s inversion. -/
theorem readLevel_run {h : LIdx} {u : Level} {s s' : AState}
    (hr : readLevel h s = .ok (u, s')) :
    s' = s ∧ denoteL s.store.ls h = some u :=
  AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ denoteL s.store.ls h = some r) rfl hr
    (readLevel_spec s h)

/-- con-leche: none — `readLevels`'s inversion. -/
theorem readLevels_run {h : LsIdx} {us : List Level} {s s' : AState}
    (hr : readLevels h s = .ok (us, s')) :
    s' = s ∧ denoteLs s.store.lss h = some us :=
  AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ denoteLs s.store.lss h = some r) rfl hr
    (readLevels_spec s h)

/-! ### The memo table's two laws

The walk threads its table explicitly, so the invariant is a hypothesis AND a
conclusion rather than a state clause: the empty table satisfies it, and an
insert of a CORRECT answer preserves it. -/

theorem LPDMemoOK.empty {params : List ConLeche.Name} {st : EStore} :
    LPDMemoOK params ∅ st := by
  intro k v hk; simp at hk

theorem LPDMemoOK.insert {params : List ConLeche.Name} {st : EStore}
    {tbl : Std.HashMap EIdx Bool} (hm : LPDMemoOK params tbl st) {h : EIdx}
    {e : Expr} (hd : denoteE st h = some e) {b : Bool}
    (hb : b = Expr.allLevelParamsDefined params e) :
    LPDMemoOK params (tbl.insert h b) st := by
  intro k v hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i heq
    obtain rfl := Option.some.inj hk
    obtain rfl := eq_of_beq heq
    exact ⟨e, hd, hb⟩
  · exact hm k v hk

/-- con-leche: none — **the memo insert is the last step of every arm**:
Lean's `do` elaborator copies the continuation into each branch, so each arm
ends "…, then record the answer".  Inverted once here rather than thirteen
times. -/
private theorem lpdClose {h : EIdx} {tbl' : Std.HashMap EIdx Bool} {b : Bool}
    {X : AM (Bool × Std.HashMap EIdx Bool)} {s s' : AState}
    (hk : (X >>= fun y =>
        (pure (y.1, y.2.insert h y.1) : AM (Bool × Std.HashMap EIdx Bool))) s
      = .ok ((b, tbl'), s')) :
    ∃ t2 s2, X s = .ok ((b, t2), s2) ∧ s' = s2 ∧ tbl' = t2.insert h b := by
  obtain ⟨q, s2, g, k⟩ := AM.bind_ok hk
  obtain ⟨b0, t0⟩ := q
  obtain ⟨hv, hs⟩ := AM.pure_ok k
  simp only [Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl⟩ := hv
  exact ⟨t0, s2, g, hs, rfl⟩

/-- con-leche: ConLeche/Kernel/Level.lean:299-332
Expr.allLevelParamsDefinedGo — **the memoised walk, one fuel level at a
time**.  The twin short-circuits where con-leche writes `&&`, which agrees
arm for arm, and the state never moves: `view`, `readLevel` and `readLevels`
are all read-only. -/
theorem allLevelParamsDefinedGo_run {params : List ConLeche.Name} :
    ∀ (fuel : Nat) {tbl tbl' : Std.HashMap EIdx Bool} {h : EIdx} {e : Expr}
      {b : Bool} {s s' : AState},
      StateOK s → LPDMemoOK params tbl s.store → denoteE s.store h = some e →
      allLevelParamsDefinedGo params tbl fuel h s = .ok ((b, tbl'), s') →
      s' = s ∧ b = Expr.allLevelParamsDefined params e ∧
        LPDMemoOK params tbl' s.store := by
  intro fuel
  induction fuel with
  | zero =>
    intro tbl tbl' h e b s s' _ _ _ hrun
    exact absurd hrun (AM.Never.fail _ _ _ _)
  | succ fuel ih =>
    intro tbl tbl' h e b s s' hok hm hd hrun
    have hwf : StoreWF s.store := hok.wf
    simp only [Arena.allLevelParamsDefinedGo] at hrun
    cases hhit : tbl[h]? with
    | some r =>
      rw [hhit] at hrun
      obtain ⟨hv, rfl⟩ := AM.pure_ok hrun
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      obtain ⟨e', hd', hr'⟩ := hm h b hhit
      rw [hd] at hd'
      obtain rfl := Option.some.inj hd'
      exact ⟨rfl, hr', hm⟩
    | none =>
      rw [hhit] at hrun
      obtain ⟨v, s2, g2, k2⟩ := AM.bind_ok (α := ENodeView) hrun
      obtain ⟨rfl, hv⟩ := viewE_run g2
      cases v with
      | bvar i =>
        obtain rfl := denote_bvar_inv hwf hv hd
        obtain ⟨t2, s3, gX, rfl, rfl⟩ := lpdClose k2
        obtain ⟨hq, rfl⟩ := AM.pure_ok gX
        simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        exact ⟨rfl, rfl, hm.insert hd rfl⟩
      | lit l =>
        obtain rfl := denote_lit_inv hwf hv hd
        obtain ⟨t2, s3, gX, rfl, rfl⟩ := lpdClose k2
        obtain ⟨hq, rfl⟩ := AM.pure_ok gX
        simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        exact ⟨rfl, rfl, hm.insert hd rfl⟩
      | sort u =>
        obtain ⟨l, rfl, hl⟩ := denote_sort_inv hwf hv hd
        obtain ⟨w, s3, g3, k3⟩ := AM.bind_ok (α := Level) k2
        obtain ⟨rfl, hw⟩ := readLevel_run g3
        rw [hl] at hw
        obtain rfl := Option.some.inj hw
        obtain ⟨t2, s4, gX, rfl, rfl⟩ := lpdClose k3
        obtain ⟨hq, rfl⟩ := AM.pure_ok gX
        simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        exact ⟨rfl, rfl, hm.insert hd rfl⟩
      | const n us =>
        obtain ⟨nm, ls, rfl, -, hls⟩ := denote_const_inv hwf hv hd
        obtain ⟨w, s3, g3, k3⟩ := AM.bind_ok (α := List Level) k2
        obtain ⟨rfl, hw⟩ := readLevels_run g3
        rw [hls] at hw
        obtain rfl := Option.some.inj hw
        obtain ⟨t2, s4, gX, rfl, rfl⟩ := lpdClose k3
        obtain ⟨hq, rfl⟩ := AM.pure_ok gX
        simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        exact ⟨rfl, rfl, hm.insert hd rfl⟩
      | fvar k t =>
        obtain ⟨xt, rfl, hxt⟩ := denote_fvar_inv hwf hv hd
        obtain ⟨t2, s3, gX, rfl, rfl⟩ := lpdClose k2
        obtain ⟨rfl, hb, hm2⟩ := ih hok hm hxt gX
        exact ⟨rfl, hb, hm2.insert hd hb⟩
      | proj n i sub =>
        obtain ⟨nm, xe, rfl, -, hxe⟩ := denote_proj_inv hwf hv hd
        obtain ⟨t2, s3, gX, rfl, rfl⟩ := lpdClose k2
        obtain ⟨rfl, hb, hm2⟩ := ih hok hm hxe gX
        exact ⟨rfl, hb, hm2.insert hd hb⟩
      | app f a =>
        obtain ⟨xf, xa, rfl, hxf, hxa⟩ := denote_app_inv hwf hv hd
        obtain ⟨q1, s3, g3, k3⟩ :=
          AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) k2
        obtain ⟨b1, tb1⟩ := q1
        obtain ⟨rfl, hb1, hm1⟩ := ih hok hm hxf g3
        rcases AM.ite_ok k3 with ⟨hc, k4⟩ | ⟨hc, k4⟩
        · obtain ⟨t2, s4, gX, rfl, rfl⟩ := lpdClose k4
          obtain ⟨rfl, hb2, hm2⟩ := ih hok hm1 hxa gX
          have hct : b1 = true := hc
          have hres : b = Expr.allLevelParamsDefined params (.app xf xa) := by
            simp only [Expr.allLevelParamsDefined, ← hb1, ← hb2, hct,
              Bool.true_and]
          exact ⟨rfl, hres, hm2.insert hd hres⟩
        · obtain ⟨t2, s4, gX, rfl, rfl⟩ := lpdClose k4
          obtain ⟨hq, rfl⟩ := AM.pure_ok gX
          simp only [Prod.mk.injEq] at hq
          obtain ⟨rfl, rfl⟩ := hq
          have hbf : b1 = false := by simpa using hc
          have hres : (false : Bool)
              = Expr.allLevelParamsDefined params (.app xf xa) := by
            simp only [Expr.allLevelParamsDefined, ← hb1, hbf, Bool.false_and]
          exact ⟨rfl, hres, hm1.insert hd hres⟩
      | lam t bd m =>
        obtain ⟨xt, xb, rfl, hxt, hxb⟩ := denote_lam_inv hwf hv hd
        obtain ⟨q1, s3, g3, k3⟩ :=
          AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) k2
        obtain ⟨b1, tb1⟩ := q1
        obtain ⟨rfl, hb1, hm1⟩ := ih hok hm hxt g3
        rcases AM.ite_ok k3 with ⟨hc, k4⟩ | ⟨hc, k4⟩
        · obtain ⟨t2, s4, gX, rfl, rfl⟩ := lpdClose k4
          obtain ⟨hq, rfl⟩ := AM.pure_ok gX
          simp only [Prod.mk.injEq] at hq
          obtain ⟨rfl, rfl⟩ := hq
          have hbf : b1 = false := by simpa using hc
          have hres : (false : Bool)
              = Expr.allLevelParamsDefined params (.lam xt xb m) := by
            simp only [Expr.allLevelParamsDefined, ← hb1, hbf, Bool.false_and]
          exact ⟨rfl, hres, hm1.insert hd hres⟩
        · obtain ⟨q2, s4, g4, k5⟩ :=
            AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) k4
          obtain ⟨b2, tb2⟩ := q2
          obtain ⟨rfl, hb2, hm2⟩ := ih hok hm1 hxb g4
          obtain ⟨t2, s5, gX, rfl, rfl⟩ := lpdClose k5
          obtain ⟨hq, rfl⟩ := AM.pure_ok gX
          simp only [Prod.mk.injEq] at hq
          obtain ⟨rfl, rfl⟩ := hq
          have hbt : b1 = true := by simpa using hc
          have hres : (b2 && ConLeche.PropWhen.paramsDefined params m.pw)
              = Expr.allLevelParamsDefined params (.lam xt xb m) := by
            simp only [Expr.allLevelParamsDefined, ← hb1, ← hb2, hbt,
              Bool.true_and]
          exact ⟨rfl, hres, hm2.insert hd hres⟩
      | forallE t bd m =>
        obtain ⟨xt, xb, rfl, hxt, hxb⟩ := denote_forallE_inv hwf hv hd
        obtain ⟨q1, s3, g3, k3⟩ :=
          AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) k2
        obtain ⟨b1, tb1⟩ := q1
        obtain ⟨rfl, hb1, hm1⟩ := ih hok hm hxt g3
        rcases AM.ite_ok k3 with ⟨hc, k4⟩ | ⟨hc, k4⟩
        · obtain ⟨t2, s4, gX, rfl, rfl⟩ := lpdClose k4
          obtain ⟨hq, rfl⟩ := AM.pure_ok gX
          simp only [Prod.mk.injEq] at hq
          obtain ⟨rfl, rfl⟩ := hq
          have hbf : b1 = false := by simpa using hc
          have hres : (false : Bool)
              = Expr.allLevelParamsDefined params (.forallE xt xb m) := by
            simp only [Expr.allLevelParamsDefined, ← hb1, hbf, Bool.false_and]
          exact ⟨rfl, hres, hm1.insert hd hres⟩
        · obtain ⟨q2, s4, g4, k5⟩ :=
            AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) k4
          obtain ⟨b2, tb2⟩ := q2
          obtain ⟨rfl, hb2, hm2⟩ := ih hok hm1 hxb g4
          obtain ⟨t2, s5, gX, rfl, rfl⟩ := lpdClose k5
          obtain ⟨hq, rfl⟩ := AM.pure_ok gX
          simp only [Prod.mk.injEq] at hq
          obtain ⟨rfl, rfl⟩ := hq
          have hbt : b1 = true := by simpa using hc
          have hres : (b2 && ConLeche.PropWhen.paramsDefined params m.pw)
              = Expr.allLevelParamsDefined params (.forallE xt xb m) := by
            simp only [Expr.allLevelParamsDefined, ← hb1, ← hb2, hbt,
              Bool.true_and]
          exact ⟨rfl, hres, hm2.insert hd hres⟩
      | letE t w bd =>
        obtain ⟨xt, xw, xb, rfl, hxt, hxw, hxb⟩ := denote_letE_inv hwf hv hd
        obtain ⟨q1, s3, g3, k3⟩ :=
          AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) k2
        obtain ⟨b1, tb1⟩ := q1
        obtain ⟨rfl, hb1, hm1⟩ := ih hok hm hxt g3
        rcases AM.ite_ok k3 with ⟨hc, k4⟩ | ⟨hc, k4⟩
        · obtain ⟨t2, s4, gX, rfl, rfl⟩ := lpdClose k4
          obtain ⟨hq, rfl⟩ := AM.pure_ok gX
          simp only [Prod.mk.injEq] at hq
          obtain ⟨rfl, rfl⟩ := hq
          have hbf : b1 = false := by simpa using hc
          have hres : (false : Bool)
              = Expr.allLevelParamsDefined params (.letE xt xw xb) := by
            simp only [Expr.allLevelParamsDefined, ← hb1, hbf, Bool.false_and]
          exact ⟨rfl, hres, hm1.insert hd hres⟩
        · obtain ⟨q2, s4, g4, k5⟩ :=
            AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) k4
          obtain ⟨b2, tb2⟩ := q2
          obtain ⟨rfl, hb2, hm2⟩ := ih hok hm1 hxw g4
          rcases AM.ite_ok k5 with ⟨hc2, k6⟩ | ⟨hc2, k6⟩
          · obtain ⟨t2, s5, gX, rfl, rfl⟩ := lpdClose k6
            obtain ⟨hq, rfl⟩ := AM.pure_ok gX
            simp only [Prod.mk.injEq] at hq
            obtain ⟨rfl, rfl⟩ := hq
            have hbt : b1 = true := by simpa using hc
            have hbf : b2 = false := by simpa using hc2
            have hres : (false : Bool)
                = Expr.allLevelParamsDefined params (.letE xt xw xb) := by
              simp only [Expr.allLevelParamsDefined, ← hb1, ← hb2, hbt, hbf,
                Bool.true_and, Bool.false_and]
            exact ⟨rfl, hres, hm2.insert hd hres⟩
          · obtain ⟨t2, s5, gX, rfl, rfl⟩ := lpdClose k6
            obtain ⟨rfl, hb3, hm3⟩ := ih hok hm2 hxb gX
            have hbt : b1 = true := by simpa using hc
            have hbt2 : b2 = true := by simpa using hc2
            have hres : b
                = Expr.allLevelParamsDefined params (.letE xt xw xb) := by
              simp only [Expr.allLevelParamsDefined, ← hb1, ← hb2, ← hb3, hbt,
                hbt2, Bool.true_and]
            exact ⟨rfl, hres, hm3.insert hd hres⟩

/-- con-leche: ConLeche/Kernel/Level.lean:405-407
Expr.allLevelParamsDefinedFast — **Theorem 1 for the front door's
level-parameter guard**: the memoised DAG walk answers what con-leche's
`allLevelParamsDefined` answers at the denoted parameter list.

**PROVED** (task #97-P3-Checker round 4): `readNames_run` and then
`allLevelParamsDefinedGo_run`'s fuel induction at the empty memo. -/
theorem allLevelParamsDefined_run {lps : List NIdx} {ks : List ConLeche.Name}
    {e : EIdx} {x : Expr} {r : Bool} {s s' : AState} (hok : StateOK s)
    (hlps : Frontend.denoteNList s.store.ns lps = some ks)
    (hd : denoteE s.store e = some x)
    (hrun : allLevelParamsDefined lps e s = .ok (r, s')) :
    s'.store = s.store ∧ s'.caches = s.caches ∧ s'.pins = s.pins ∧
      r = Expr.allLevelParamsDefined ks x := by
  simp only [Arena.allLevelParamsDefined] at hrun
  obtain ⟨ks2, s1, g1, k1⟩ := AM.bind_ok (α := List ConLeche.Name) hrun
  obtain ⟨rfl, hks⟩ := readNames_run g1
  rw [hlps] at hks
  obtain rfl := Option.some.inj hks
  obtain ⟨p, s2, g2, k2⟩ :=
    AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) k1
  obtain ⟨b, tb⟩ := p
  obtain ⟨rfl, hb, -⟩ :=
    allLevelParamsDefinedGo_run coreWalkFuel hok LPDMemoOK.empty hd g2
  obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
  exact ⟨rfl, rfl, rfl, hb⟩

/-! ### The environment lookup, both ways

`constsResolve` asks `fe.find?`; con-leche asks `env.find?`.  The two agree at
a handle that denotes, and BOTH directions are needed: the hit is
`IFEnvOK.hit` plus `denoteN`'s functionality, the miss is `IFEnvOK.miss`,
which is `denoteN`'s injectivity (DESIGN §8.3 lesson 13). -/

theorem IFEnvOK.find_isSome {env : Env} {fe : IFEnv} {s : AState}
    (hok : StateOK s) (h : IFEnvOK env fe s) {n : NIdx} {nm : ConLeche.Name}
    (hd : denoteN s.store.ns n = some nm) :
    (fe.find? n).isSome = (env.find? nm).isSome := by
  cases hf : fe.find? n with
  | none => rw [h.miss hok hd hf]; rfl
  | some ci =>
    obtain ⟨nm', c, hd', -, hfind⟩ := h.hit n ci hf
    rw [hd] at hd'
    obtain rfl := Option.some.inj hd'
    rw [hfind]; rfl

/-! ### `constsResolve` — the pure walk

`Arena/Core.lean`'s `constsResolve` is con-leche's `Expr.constsResolve`,
which is the SPECIFICATION the memoised walk below is measured against
(con-leche's `@[csimp]` pair).  The two literal arms read the pin table, so
this is a `PinsOK` theorem (round 3's `PSpecP` grade). -/

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:235-260 Expr.constsResolve — the
pure walk over handles is con-leche's over terms. -/
theorem constsResolve_run {env : Env} {fe : IFEnv} :
    ∀ (fuel : Nat) {h : EIdx} {e : Expr} {b : Bool} {s s' : AState},
      StateOK s → PinsOK s → IFEnvOK env fe s → denoteE s.store h = some e →
      constsResolve fe fuel h s = .ok (b, s') →
      s' = s ∧ b = Expr.constsResolve env e := by
  intro fuel
  induction fuel with
  | zero =>
    intro h e b s s' _ _ _ _ hrun
    exact absurd hrun (AM.Never.fail _ _ _ _)
  | succ fuel ih =>
    intro h e b s s' hok hp hie hd hrun
    have hwf : StoreWF s.store := hok.wf
    simp only [Arena.constsResolve] at hrun
    obtain ⟨v, s1, g1, k1⟩ := AM.bind_ok (α := ENodeView) hrun
    obtain ⟨rfl, hv⟩ := viewE_run g1
    cases v with
    | bvar i =>
      obtain rfl := denote_bvar_inv hwf hv hd
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k1
      exact ⟨rfl, rfl⟩
    | sort u =>
      obtain ⟨l, rfl, -⟩ := denote_sort_inv hwf hv hd
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k1
      exact ⟨rfl, rfl⟩
    | const n us =>
      obtain ⟨nm, ls, rfl, hn, -⟩ := denote_const_inv hwf hv hd
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k1
      exact ⟨rfl, hie.find_isSome hok hn⟩
    | fvar k t =>
      obtain ⟨xt, rfl, hxt⟩ := denote_fvar_inv hwf hv hd
      obtain ⟨rfl, hb⟩ := ih hok hp hie hxt k1
      exact ⟨rfl, hb⟩
    | proj n i sub =>
      obtain ⟨nm, xe, rfl, hn, hxe⟩ := denote_proj_inv hwf hv hd
      have hfs := hie.find_isSome hok hn
      rcases AM.ite_ok k1 with ⟨hc, k2⟩ | ⟨hc, k2⟩
      · obtain ⟨rfl, hb⟩ := ih hok hp hie hxe k2
        refine ⟨rfl, ?_⟩
        simp only [Expr.constsResolve, ← hfs, hc, Bool.true_and, hb]
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        refine ⟨rfl, ?_⟩
        have hcf : (env.find? nm).isSome = false := by rw [← hfs]; simpa using hc
        simp only [Expr.constsResolve, hcf, Bool.false_and]
    | app f a =>
      obtain ⟨xf, xa, rfl, hxf, hxa⟩ := denote_app_inv hwf hv hd
      obtain ⟨b1, s2, g2, k2⟩ := AM.bind_ok (α := Bool) k1
      obtain ⟨rfl, hb1⟩ := ih hok hp hie hxf g2
      rcases AM.ite_ok k2 with ⟨hc, k3⟩ | ⟨hc, k3⟩
      · obtain ⟨rfl, hb2⟩ := ih hok hp hie hxa k3
        exact ⟨rfl, by simp only [Expr.constsResolve, ← hb1, hc, Bool.true_and, hb2]⟩
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
        have hbf : b1 = false := by simpa using hc
        exact ⟨rfl, by simp only [Expr.constsResolve, ← hb1, hbf, Bool.false_and]⟩
    | lam t bd m =>
      obtain ⟨xt, xb, rfl, hxt, hxb⟩ := denote_lam_inv hwf hv hd
      obtain ⟨b1, s2, g2, k2⟩ := AM.bind_ok (α := Bool) k1
      obtain ⟨rfl, hb1⟩ := ih hok hp hie hxt g2
      rcases AM.ite_ok k2 with ⟨hc, k3⟩ | ⟨hc, k3⟩
      · obtain ⟨rfl, hb2⟩ := ih hok hp hie hxb k3
        exact ⟨rfl, by simp only [Expr.constsResolve, ← hb1, hc, Bool.true_and, hb2]⟩
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
        have hbf : b1 = false := by simpa using hc
        exact ⟨rfl, by simp only [Expr.constsResolve, ← hb1, hbf, Bool.false_and]⟩
    | forallE t bd m =>
      obtain ⟨xt, xb, rfl, hxt, hxb⟩ := denote_forallE_inv hwf hv hd
      obtain ⟨b1, s2, g2, k2⟩ := AM.bind_ok (α := Bool) k1
      obtain ⟨rfl, hb1⟩ := ih hok hp hie hxt g2
      rcases AM.ite_ok k2 with ⟨hc, k3⟩ | ⟨hc, k3⟩
      · obtain ⟨rfl, hb2⟩ := ih hok hp hie hxb k3
        exact ⟨rfl, by simp only [Expr.constsResolve, ← hb1, hc, Bool.true_and, hb2]⟩
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
        have hbf : b1 = false := by simpa using hc
        exact ⟨rfl, by simp only [Expr.constsResolve, ← hb1, hbf, Bool.false_and]⟩
    | letE t w bd =>
      obtain ⟨xt, xw, xb, rfl, hxt, hxw, hxb⟩ := denote_letE_inv hwf hv hd
      obtain ⟨b1, s2, g2, k2⟩ := AM.bind_ok (α := Bool) k1
      obtain ⟨rfl, hb1⟩ := ih hok hp hie hxt g2
      rcases AM.ite_ok k2 with ⟨hc, k3⟩ | ⟨hc, k3⟩
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
        have hbf : b1 = false := by simpa using hc
        exact ⟨rfl, by
          simp only [Expr.constsResolve, ← hb1, hbf, Bool.false_and]⟩
      · obtain ⟨b2, s3, g3, k4⟩ := AM.bind_ok (α := Bool) k3
        obtain ⟨rfl, hb2⟩ := ih hok hp hie hxw g3
        have hbt : b1 = true := by simpa using hc
        rcases AM.ite_ok k4 with ⟨hc2, k5⟩ | ⟨hc2, k5⟩
        · obtain ⟨rfl, hb3⟩ := ih hok hp hie hxb k5
          exact ⟨rfl, by
            simp only [Expr.constsResolve, ← hb1, ← hb2, hbt, hc2, Bool.true_and,
              hb3]⟩
        · obtain ⟨rfl, rfl⟩ := AM.pure_ok k5
          have hbf2 : b2 = false := by simpa using hc2
          exact ⟨rfl, by
            simp only [Expr.constsResolve, ← hb1, ← hb2, hbt, hbf2, Bool.true_and,
              Bool.false_and]⟩
    | lit l =>
      obtain rfl := denote_lit_inv hwf hv hd
      cases l with
      | natVal q =>
        obtain ⟨p1, u1, q1, w1⟩ := AM.bind_ok (α := NIdx) k1
        obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.natName) hp rfl q1
        obtain ⟨p2, u2, q2, w2⟩ := AM.bind_ok (α := NIdx) w1
        obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.natZeroName) hp rfl q2
        obtain ⟨p3, u3, q3, w3⟩ := AM.bind_ok (α := NIdx) w2
        obtain ⟨rfl, d3⟩ := pinAt_run (x := ConLeche.natSuccName) hp rfl q3
        obtain ⟨rfl, rfl⟩ := AM.pure_ok w3
        exact ⟨rfl, by
          simp only [Expr.constsResolve, hie.find_isSome hok d1,
            hie.find_isSome hok d2, hie.find_isSome hok d3]⟩
      | strVal q =>
        obtain ⟨p1, u1, q1, w1⟩ := AM.bind_ok (α := NIdx) k1
        obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.natName) hp rfl q1
        obtain ⟨p2, u2, q2, w2⟩ := AM.bind_ok (α := NIdx) w1
        obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.natZeroName) hp rfl q2
        obtain ⟨p3, u3, q3, w3⟩ := AM.bind_ok (α := NIdx) w2
        obtain ⟨rfl, d3⟩ := pinAt_run (x := ConLeche.natSuccName) hp rfl q3
        obtain ⟨p4, u4, q4, w4⟩ := AM.bind_ok (α := NIdx) w3
        obtain ⟨rfl, d4⟩ := pinAt_run (x := ConLeche.stringName) hp rfl q4
        obtain ⟨p5, u5, q5, w5⟩ := AM.bind_ok (α := NIdx) w4
        obtain ⟨rfl, d5⟩ := pinAt_run (x := ConLeche.stringOfListName) hp rfl q5
        obtain ⟨p6, u6, q6, w6⟩ := AM.bind_ok (α := NIdx) w5
        obtain ⟨rfl, d6⟩ := pinAt_run (x := ConLeche.listName) hp rfl q6
        obtain ⟨p7, u7, q7, w7⟩ := AM.bind_ok (α := NIdx) w6
        obtain ⟨rfl, d7⟩ := pinAt_run (x := ConLeche.listNilName) hp rfl q7
        obtain ⟨p8, u8, q8, w8⟩ := AM.bind_ok (α := NIdx) w7
        obtain ⟨rfl, d8⟩ := pinAt_run (x := ConLeche.listConsName) hp rfl q8
        obtain ⟨p9, u9, q9, w9⟩ := AM.bind_ok (α := NIdx) w8
        obtain ⟨rfl, d9⟩ := pinAt_run (x := ConLeche.charName) hp rfl q9
        obtain ⟨p10, u10, q10, w10⟩ := AM.bind_ok (α := NIdx) w9
        obtain ⟨rfl, d10⟩ := pinAt_run (x := ConLeche.charOfNatName) hp rfl q10
        obtain ⟨rfl, rfl⟩ := AM.pure_ok w10
        exact ⟨rfl, by
          simp only [Expr.constsResolve, hie.find_isSome hok d1,
            hie.find_isSome hok d2, hie.find_isSome hok d3,
            hie.find_isSome hok d4, hie.find_isSome hok d5,
            hie.find_isSome hok d6, hie.find_isSome hok d7,
            hie.find_isSome hok d8, hie.find_isSome hok d9,
            hie.find_isSome hok d10]⟩

/-! ### `constsResolveF` — the memoised walk

Same shape as `allLevelParamsDefinedGo_run`: an explicitly threaded table, its
invariant a hypothesis and a conclusion, and `lpdClose` for the insert every
arm ends with.  The four leaf constructors are NOT memoised (con-leche's
`…Go` calls the pure walk at them), so their arms are `constsResolve_run`
directly. -/

/-- con-leche: ConLeche/Kernel/DeclCheck.lean:89-124 Expr.constsResolveFGo —
the memo invariant: a recorded answer is the real one. -/
def CRMemoOK (env : Env) (tbl : Std.HashMap EIdx Bool) (st : EStore) : Prop :=
  ∀ k v, tbl[k]? = some v →
    ∃ e, denoteE st k = some e ∧ v = Expr.constsResolve env e

theorem CRMemoOK.empty {env : Env} {st : EStore} : CRMemoOK env ∅ st := by
  intro k v hk; simp at hk

theorem CRMemoOK.insert {env : Env} {st : EStore}
    {tbl : Std.HashMap EIdx Bool} (hm : CRMemoOK env tbl st) {h : EIdx}
    {e : Expr} (hd : denoteE st h = some e) {b : Bool}
    (hb : b = Expr.constsResolve env e) :
    CRMemoOK env (tbl.insert h b) st := by
  intro k v hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i heq
    obtain rfl := Option.some.inj hk
    obtain rfl := eq_of_beq heq
    exact ⟨e, hd, hb⟩
  · exact hm k v hk

/-- con-leche: none — the four UNMEMOISED leaf arms: the pure walk, and the
table untouched. -/
private theorem crLeaf {tbl tbl' : Std.HashMap EIdx Bool} {b : Bool}
    {X : AM Bool} {s s' : AState}
    (hx : (X >>= fun r =>
        (pure (r, tbl) : AM (Bool × Std.HashMap EIdx Bool))) s
      = .ok ((b, tbl'), s')) : X s = .ok (b, s') ∧ tbl' = tbl := by
  obtain ⟨r, s2, g2, k2⟩ := AM.bind_ok (α := Bool) hx
  obtain ⟨hq, hs⟩ := AM.pure_ok k2
  simp only [Prod.mk.injEq] at hq
  obtain ⟨rfl, rfl⟩ := hq
  subst hs
  exact ⟨g2, rfl⟩

/-- con-leche: ConLeche/Kernel/DeclCheck.lean:89-124 Expr.constsResolveFGo —
**the memoised walk is the pure one**. -/
theorem constsResolveFGo_run {env : Env} {fe : IFEnv} :
    ∀ (fuel : Nat) {tbl tbl' : Std.HashMap EIdx Bool} {h : EIdx} {e : Expr}
      {b : Bool} {s s' : AState},
      StateOK s → PinsOK s → IFEnvOK env fe s → CRMemoOK env tbl s.store →
      denoteE s.store h = some e →
      constsResolveFGo fe tbl fuel h s = .ok ((b, tbl'), s') →
      s' = s ∧ b = Expr.constsResolve env e ∧ CRMemoOK env tbl' s.store := by
  intro fuel
  induction fuel with
  | zero =>
    intro tbl tbl' h e b s s' _ _ _ _ _ hrun
    exact absurd hrun (AM.Never.fail _ _ _ _)
  | succ fuel ih =>
    intro tbl tbl' h e b s s' hok hp hie hm hd hrun
    have hwf : StoreWF s.store := hok.wf
    simp only [Arena.constsResolveFGo] at hrun
    obtain ⟨v, s1, g1, k1⟩ := AM.bind_ok (α := ENodeView) hrun
    obtain ⟨rfl, hv⟩ := viewE_run g1
    cases v with
    | bvar i =>
      obtain ⟨gP, rfl⟩ := crLeaf k1
      obtain ⟨rfl, hb⟩ := constsResolve_run coreWalkFuel hok hp hie hd gP
      exact ⟨rfl, hb, hm⟩
    | sort u =>
      obtain ⟨gP, rfl⟩ := crLeaf k1
      obtain ⟨rfl, hb⟩ := constsResolve_run coreWalkFuel hok hp hie hd gP
      exact ⟨rfl, hb, hm⟩
    | lit l =>
      obtain ⟨gP, rfl⟩ := crLeaf k1
      obtain ⟨rfl, hb⟩ := constsResolve_run coreWalkFuel hok hp hie hd gP
      exact ⟨rfl, hb, hm⟩
    | const n us =>
      obtain ⟨gP, rfl⟩ := crLeaf k1
      obtain ⟨rfl, hb⟩ := constsResolve_run coreWalkFuel hok hp hie hd gP
      exact ⟨rfl, hb, hm⟩
    | fvar k t =>
      obtain ⟨xt, rfl, hxt⟩ := denote_fvar_inv hwf hv hd
      cases hhit : tbl[h]? with
      | some r =>
        rw [hhit] at k1
        obtain ⟨hq, rfl⟩ := AM.pure_ok k1
        simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        obtain ⟨e', hd', hr'⟩ := hm h b hhit
        rw [hd] at hd'
        obtain rfl := Option.some.inj hd'
        exact ⟨rfl, hr', hm⟩
      | none =>
        rw [hhit] at k1
        obtain ⟨v2, s2, g2, k2⟩ := AM.bind_ok (α := ENodeView) k1
        obtain ⟨rfl, hv2⟩ := viewE_run g2
        rw [hv] at hv2
        obtain rfl := (Option.some.inj hv2).symm
        obtain ⟨t2, s3, gX, rfl, rfl⟩ := lpdClose k2
        obtain ⟨rfl, hb, hm2⟩ := ih hok hp hie hm hxt gX
        exact ⟨rfl, hb, hm2.insert hd hb⟩
    | proj n i sub =>
      obtain ⟨nm, xe, rfl, hn, hxe⟩ := denote_proj_inv hwf hv hd
      cases hhit : tbl[h]? with
      | some r =>
        rw [hhit] at k1
        obtain ⟨hq, rfl⟩ := AM.pure_ok k1
        simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        obtain ⟨e', hd', hr'⟩ := hm h b hhit
        rw [hd] at hd'
        obtain rfl := Option.some.inj hd'
        exact ⟨rfl, hr', hm⟩
      | none =>
        rw [hhit] at k1
        obtain ⟨v2, s2, g2, k2⟩ := AM.bind_ok (α := ENodeView) k1
        obtain ⟨rfl, hv2⟩ := viewE_run g2
        rw [hv] at hv2
        obtain rfl := (Option.some.inj hv2).symm
        obtain ⟨q1, s3, g3, k3⟩ :=
          AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) k2
        obtain ⟨b1, tb1⟩ := q1
        obtain ⟨rfl, hb1, hm1⟩ := ih hok hp hie hm hxe g3
        obtain ⟨t2, s4, gX, rfl, rfl⟩ := lpdClose k3
        obtain ⟨hq, rfl⟩ := AM.pure_ok gX
        simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        have hres : ((fe.find? n).isSome && b1)
            = Expr.constsResolve env (.proj nm i xe) := by
          simp only [Expr.constsResolve, hie.find_isSome hok hn, ← hb1]
        exact ⟨rfl, hres, hm1.insert hd hres⟩
    | app f a =>
      obtain ⟨xf, xa, rfl, hxf, hxa⟩ := denote_app_inv hwf hv hd
      cases hhit : tbl[h]? with
      | some r =>
        rw [hhit] at k1
        obtain ⟨hq, rfl⟩ := AM.pure_ok k1
        simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        obtain ⟨e', hd', hr'⟩ := hm h b hhit
        rw [hd] at hd'
        obtain rfl := Option.some.inj hd'
        exact ⟨rfl, hr', hm⟩
      | none =>
        rw [hhit] at k1
        obtain ⟨v2, s2, g2, k2⟩ := AM.bind_ok (α := ENodeView) k1
        obtain ⟨rfl, hv2⟩ := viewE_run g2
        rw [hv] at hv2
        obtain rfl := (Option.some.inj hv2).symm
        obtain ⟨q1, s3, g3, k3⟩ :=
          AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) k2
        obtain ⟨b1, tb1⟩ := q1
        obtain ⟨rfl, hb1, hm1⟩ := ih hok hp hie hm hxf g3
        obtain ⟨q2, s4, g4, k4⟩ :=
          AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) k3
        obtain ⟨b2, tb2⟩ := q2
        obtain ⟨rfl, hb2, hm2⟩ := ih hok hp hie hm1 hxa g4
        obtain ⟨t2, s5, gX, rfl, rfl⟩ := lpdClose k4
        obtain ⟨hq, rfl⟩ := AM.pure_ok gX
        simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        have hres : (b1 && b2) = Expr.constsResolve env (.app xf xa) := by
          simp only [Expr.constsResolve, ← hb1, ← hb2]
        exact ⟨rfl, hres, hm2.insert hd hres⟩
    | lam t bd m =>
      obtain ⟨xt, xb, rfl, hxt, hxb⟩ := denote_lam_inv hwf hv hd
      cases hhit : tbl[h]? with
      | some r =>
        rw [hhit] at k1
        obtain ⟨hq, rfl⟩ := AM.pure_ok k1
        simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        obtain ⟨e', hd', hr'⟩ := hm h b hhit
        rw [hd] at hd'
        obtain rfl := Option.some.inj hd'
        exact ⟨rfl, hr', hm⟩
      | none =>
        rw [hhit] at k1
        obtain ⟨v2, s2, g2, k2⟩ := AM.bind_ok (α := ENodeView) k1
        obtain ⟨rfl, hv2⟩ := viewE_run g2
        rw [hv] at hv2
        obtain rfl := (Option.some.inj hv2).symm
        obtain ⟨q1, s3, g3, k3⟩ :=
          AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) k2
        obtain ⟨b1, tb1⟩ := q1
        obtain ⟨rfl, hb1, hm1⟩ := ih hok hp hie hm hxt g3
        obtain ⟨q2, s4, g4, k4⟩ :=
          AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) k3
        obtain ⟨b2, tb2⟩ := q2
        obtain ⟨rfl, hb2, hm2⟩ := ih hok hp hie hm1 hxb g4
        obtain ⟨t2, s5, gX, rfl, rfl⟩ := lpdClose k4
        obtain ⟨hq, rfl⟩ := AM.pure_ok gX
        simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        have hres : (b1 && b2) = Expr.constsResolve env (.lam xt xb m) := by
          simp only [Expr.constsResolve, ← hb1, ← hb2]
        exact ⟨rfl, hres, hm2.insert hd hres⟩
    | forallE t bd m =>
      obtain ⟨xt, xb, rfl, hxt, hxb⟩ := denote_forallE_inv hwf hv hd
      cases hhit : tbl[h]? with
      | some r =>
        rw [hhit] at k1
        obtain ⟨hq, rfl⟩ := AM.pure_ok k1
        simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        obtain ⟨e', hd', hr'⟩ := hm h b hhit
        rw [hd] at hd'
        obtain rfl := Option.some.inj hd'
        exact ⟨rfl, hr', hm⟩
      | none =>
        rw [hhit] at k1
        obtain ⟨v2, s2, g2, k2⟩ := AM.bind_ok (α := ENodeView) k1
        obtain ⟨rfl, hv2⟩ := viewE_run g2
        rw [hv] at hv2
        obtain rfl := (Option.some.inj hv2).symm
        obtain ⟨q1, s3, g3, k3⟩ :=
          AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) k2
        obtain ⟨b1, tb1⟩ := q1
        obtain ⟨rfl, hb1, hm1⟩ := ih hok hp hie hm hxt g3
        obtain ⟨q2, s4, g4, k4⟩ :=
          AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) k3
        obtain ⟨b2, tb2⟩ := q2
        obtain ⟨rfl, hb2, hm2⟩ := ih hok hp hie hm1 hxb g4
        obtain ⟨t2, s5, gX, rfl, rfl⟩ := lpdClose k4
        obtain ⟨hq, rfl⟩ := AM.pure_ok gX
        simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        have hres : (b1 && b2) = Expr.constsResolve env (.forallE xt xb m) := by
          simp only [Expr.constsResolve, ← hb1, ← hb2]
        exact ⟨rfl, hres, hm2.insert hd hres⟩
    | letE t w bd =>
      obtain ⟨xt, xw, xb, rfl, hxt, hxw, hxb⟩ := denote_letE_inv hwf hv hd
      cases hhit : tbl[h]? with
      | some r =>
        rw [hhit] at k1
        obtain ⟨hq, rfl⟩ := AM.pure_ok k1
        simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        obtain ⟨e', hd', hr'⟩ := hm h b hhit
        rw [hd] at hd'
        obtain rfl := Option.some.inj hd'
        exact ⟨rfl, hr', hm⟩
      | none =>
        rw [hhit] at k1
        obtain ⟨v2, s2, g2, k2⟩ := AM.bind_ok (α := ENodeView) k1
        obtain ⟨rfl, hv2⟩ := viewE_run g2
        rw [hv] at hv2
        obtain rfl := (Option.some.inj hv2).symm
        obtain ⟨q1, s3, g3, k3⟩ :=
          AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) k2
        obtain ⟨b1, tb1⟩ := q1
        obtain ⟨rfl, hb1, hm1⟩ := ih hok hp hie hm hxt g3
        obtain ⟨q2, s4, g4, k4⟩ :=
          AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) k3
        obtain ⟨b2, tb2⟩ := q2
        obtain ⟨rfl, hb2, hm2⟩ := ih hok hp hie hm1 hxw g4
        obtain ⟨q3, s5, g5, k5⟩ :=
          AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) k4
        obtain ⟨b3, tb3⟩ := q3
        obtain ⟨rfl, hb3, hm3⟩ := ih hok hp hie hm2 hxb g5
        obtain ⟨t2, s6, gX, rfl, rfl⟩ := lpdClose k5
        obtain ⟨hq, rfl⟩ := AM.pure_ok gX
        simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        have hres : (b1 && b2 && b3)
            = Expr.constsResolve env (.letE xt xw xb) := by
          simp only [Expr.constsResolve, ← hb1, ← hb2, ← hb3]
        exact ⟨rfl, hres, hm3.insert hd hres⟩

/-- con-leche: ConLeche/Kernel/DeclCheck.lean:197-199 Expr.constsResolveFFast
— **Theorem 1 for the front door's unresolved-constant guard**: the memoised
DAG walk answers what con-leche's `Expr.constsResolve` answers at the denoted
environment.

**PROVED** (task #97-P3-Checker round 4): `constsResolveFGo_run`'s fuel
induction at the empty memo, over `constsResolve_run`'s pure walk at the four
unmemoised leaves.  `IFEnvOK.find_isSome` is the whole `.const`/`.proj`
content, and its MISS half is `denoteN_inj`. -/
theorem constsResolveFFast_run {μ : CheckMode} {env : Env} {fe : IFEnv}
    {e : EIdx} {x : Expr} {r : Bool} {s s' : AState}
    (hck : CheckOK μ env fe s) (hd : denoteE s.store e = some x)
    (hrun : constsResolveFFast fe e s = .ok (r, s')) :
    s'.store = s.store ∧ s'.caches = s.caches ∧ s'.pins = s.pins ∧
      r = Expr.constsResolve env x := by
  simp only [Arena.constsResolveFFast] at hrun
  obtain ⟨p, s1, g1, k1⟩ :=
    AM.bind_ok (α := Bool × Std.HashMap EIdx Bool) hrun
  obtain ⟨b, tb⟩ := p
  obtain ⟨rfl, hb, -⟩ := constsResolveFGo_run coreWalkFuel hck.state
    hck.pins hck.ienv CRMemoOK.empty hd g1
  obtain ⟨rfl, rfl⟩ := AM.pure_ok k1
  exact ⟨rfl, rfl, rfl, hb⟩

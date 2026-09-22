/-
# `ConRon.Bridge.Checker.Canon` — the pinned-block comparison

`Arena/Canon.lean` is the twin of `ConLeche/Kernel/Canon.lean`: alpha-and-
universe-renaming-insensitive comparison of a stream record against a pinned
one.  It is what recognises a `Nat` block, a quotient record and the
`Quot.sound` axiom, and it is the only comparison in the checker that is NOT
handle equality — a stream's universe parameter may be spelled differently
from the pin's, so the comparison canonicalises both sides against a generated
name list (`canonNames`).

**The bridge's shape is `RelV`'s** (`Bridge/Rel.lean`): the answer is a
`Bool`, which names no handle, so there is no target store and the tier's
cheapest shape applies — task #97-P3-0 §5's finding 1, *"the cheapest group is
the one with no target store"*.

**The one subtlety is the generated names.**  `canonNames n` interns `n` fresh
names and the comparison substitutes them for the two sides' parameters.  The
handles are fresh, so the comparison's answer depends on the store having
them; con-leche's `canonNames` builds the same `Name` values, so the twin's
answer is con-leche's provided the interned handles denote those values — an
instance of `Bridge/StoreNested.lean`'s `EStore.internName` spec and of
`denoteN`'s injectivity, once each.
-/
import ConRon.Bridge.Checker.Hyp

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-- con-leche: none — `internNNode` in run form, off `Bridge/Specs.lean`'s
triple.  `Base.lean`'s `internName_run` is the same three lines one layer up;
`canonNamesGo` calls the NODE intern directly, so it wants this one. -/
theorem internNNode_run {v : NNodeView} {s s' : AState} {h : NIdx}
    (hwf : StoreWF s.store) (hv : s.store.ns.ViewOK v)
    (hr : internNNode v s = .ok (h, s')) :
    StoreWF s'.store ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      denoteN s'.store.ns h = denoteNView s'.store.ns v := by
  have hq := AM.of_run (P := fun t => t = s)
    (Q := fun r t => StoreWF t.store ∧ Ext s.store t.store ∧
        t.store.pers = s.store.pers ∧ t.store.scr = s.store.scr ∧
        t.store.scratchOn = s.store.scratchOn ∧
        t.memos = s.memos ∧ t.caches = s.caches ∧ t.pins = s.pins ∧
        t.store.ns.view r = some v ∧
        denoteN t.store.ns r = denoteNView t.store.ns v)
    rfl hr (internNNode_spec s v hwf hv)
  obtain ⟨q1, q2, -, -, -, -, q7, q8, -, q10⟩ := hq
  exact ⟨q1, q2, q7, q8, q10⟩

/-- con-leche: ConLeche/Kernel/Canon.lean:67-73 canonNameMap — the generated
name list denotes con-leche's, and the handles are fresh.

**PROVED** (task #97-P3-Checker-3): the `Nat` recursion over
`internNNode_run` twice per step (`⟨⟩` and then `.num ⟨⟩ i`, which is what
`internName (.num .anonymous i)` is), with `List.range_succ_eq_map` lining the
counted-up index list up with the recursion's own `i + 1`.  No accumulator:
the step's `denoteN` is carried forward by `denoteN_ext` and the list is the
recursion's own cons. -/
theorem canonNamesGo_run : ∀ (n i : Nat) (r : List NIdx) (s s' : AState),
    StateOK s → canonNamesGo i n s = .ok (r, s') →
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      Frontend.denoteNList s'.store.ns r
        = some ((List.range n).map
            (fun k => ConLeche.Name.num .anonymous (i + k))) := by
  intro n
  induction n with
  | zero =>
    intro i r s s' hok hr
    simp only [Arena.canonNamesGo] at hr
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hr
    exact ⟨hok, Ext.refl _, rfl, rfl, rfl⟩
  | succ m ih =>
    intro i r s s' hok hr
    simp only [Arena.canonNamesGo] at hr
    obtain ⟨a, s1, g1, k1⟩ := AM.bind_ok hr
    obtain ⟨w1, x1, c1, p1, d1⟩ :=
      internNNode_run hok.wf
        (by intro c hc; simp [NNodeView.children] at hc) g1
    simp only [denoteNView] at d1
    obtain ⟨h, s2, g2, k2⟩ := AM.bind_ok k1
    obtain ⟨w2, x2, c2, p2, d2⟩ :=
      internNNode_run w1
        (by intro c hc
            simp only [NNodeView.children, List.mem_singleton] at hc
            subst hc
            exact nview_isSome_of_denote d1) g2
    have d1' : denoteN s2.store.ns a = some ConLeche.Name.anonymous :=
      denoteN_ext d1 x2
    simp only [denoteNView, d1', Option.map_some] at d2
    obtain ⟨hs, s3, g3, k3⟩ := AM.bind_ok k2
    obtain ⟨ok3, x3, c3, p3, d3⟩ := ih (i + 1) hs s2 s3 ⟨w2⟩ g3
    obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
    refine ⟨ok3, (x1.trans x2).trans x3, by rw [c3, c2, c1],
      by rw [p3, p2, p1], ?_⟩
    have hk : ∀ k : Nat, i + 1 + k = i + (k + 1) := fun k => by omega
    simp only [Frontend.denoteNList, denoteN_ext d2 x3, d3,
      List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def,
      Nat.add_zero, Nat.succ_eq_add_one, hk]

theorem canonNames_run {n : Nat} {r : List NIdx} {s s' : AState}
    (hok : StateOK s) (hrun : canonNames n s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧
      Frontend.denoteNList s'.store.ns r
        = some ((List.range n).map (fun i => ConLeche.Name.num .anonymous i)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := canonNamesGo_run n 0 r s s' hok hrun
  exact ⟨h1, h2, h3, h4, by simpa using h5⟩

/-- con-leche: ConLeche/Kernel/Canon.lean:198-201 ConstantVal.canonEq — the
handle comparison is the term comparison.

`sorry`: `canonExprEq`'s fuel induction (the `RelV` shape: a `Bool` answer,
no target store, so `bridge_vcs [canonExprEq, RelV]` is the closer task
#97-P3-0 §5 measures at zero hand work per arm), plus `canonNames_run`.  Task
#97-P3-Checker's sorry list, item 14. -/
theorem IConstantVal.canonEq_run {cv cv' : IConstantVal} {c c' : ConstantVal}
    {r : Bool} {s s' : AState} (hok : StateOK s)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hcv' : Frontend.denoteCV s.store cv' = some c')
    (hrun : IConstantVal.canonEq cv cv' s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.ConstantVal.canonEq c c' := by
  sorry

/-- con-leche: ConLeche/Kernel/Canon.lean:251-253 ConstantInfo.canonEq —
**the pinned-block comparison**, at a whole stored constant.  This is what
`checkDecl`'s `.axiomDecl` arm runs on `Quot.sound` and what `basisPinHit`
runs on a block's members.

`sorry`: seven constructor arms over `IConstantVal.canonEq_run` and
`canonRulesEq`.  Task #97-P3-Checker's sorry list, item 14. -/
theorem IConstantInfo.canonEq_run {ci ci' : IConstantInfo} {c c' : ConstantInfo}
    {r : Bool} {s s' : AState} (hok : StateOK s)
    (hci : Frontend.denoteCI s.store ci = some c)
    (hci' : Frontend.denoteCI s.store ci' = some c')
    (hrun : IConstantInfo.canonEq ci ci' s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.ConstantInfo.canonEq c c' := by
  sorry

/-- con-leche: none — `Frontend.denoteCIList`'s cons inversion.  (`Base.lean`
has the same three lines for `denoteEList` and sits above this module.) -/
theorem denoteCIList_cons {st : EStore} {a : IConstantInfo}
    {as : List IConstantInfo} {zs : List ConstantInfo}
    (h : Frontend.denoteCIList st (a :: as) = some zs) :
    ∃ x xs, Frontend.denoteCI st a = some x ∧
      Frontend.denoteCIList st as = some xs ∧ zs = x :: xs := by
  simp only [Frontend.denoteCIList] at h
  cases hx : Frontend.denoteCI st a with
  | none => rw [hx] at h; exact absurd h (by simp)
  | some x =>
    cases hxs : Frontend.denoteCIList st as with
    | none => rw [hx, hxs] at h; exact absurd h (by simp)
    | some xs =>
      rw [hx, hxs] at h
      simp only [Option.some.injEq] at h
      exact ⟨x, xs, rfl, rfl, h.symm⟩

/-- con-leche: ConLeche/Kernel/Canon.lean:291-293 canonEqList — the same at a
block.

**PROVED** (task #97-P3-Checker-3): the list induction over
`IConstantInfo.canonEq_run`, with con-leche's own `ConstantInfo.canonEq`
(a `decide` on the two canonical forms) driving both branches — an accepted
member makes the two `canon`s equal and peels one cons off each `map`, a
declined one makes the lists differ at the head. -/
theorem canonEqList_run_aux : ∀ (cs cs' : List IConstantInfo)
    (xs xs' : List ConstantInfo) (r : Bool) (s s' : AState), StateOK s →
    Frontend.denoteCIList s.store cs = some xs →
    Frontend.denoteCIList s.store cs' = some xs' →
    canonEqList cs cs' s = .ok (r, s') →
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.canonEqList xs xs' := by
  intro cs
  induction cs with
  | nil =>
    intro cs' xs xs' r s s' hok hcs hcs' hrun
    simp only [Frontend.denoteCIList, Option.some.injEq] at hcs
    subst hcs
    cases cs' with
    | nil =>
      simp only [Frontend.denoteCIList, Option.some.injEq] at hcs'
      subst hcs'
      simp only [Arena.canonEqList] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by simp [ConLeche.canonEqList]⟩
    | cons b bs =>
      obtain ⟨y, ys, -, -, rfl⟩ := denoteCIList_cons hcs'
      simp only [Arena.canonEqList] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by simp [ConLeche.canonEqList]⟩
  | cons a as ih =>
    intro cs' xs xs' r s s' hok hcs hcs' hrun
    obtain ⟨x, xt, hx, hxt, rfl⟩ := denoteCIList_cons hcs
    cases cs' with
    | nil =>
      simp only [Frontend.denoteCIList, Option.some.injEq] at hcs'
      subst hcs'
      simp only [Arena.canonEqList] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by simp [ConLeche.canonEqList]⟩
    | cons b bs =>
      obtain ⟨y, yt, hy, hyt, rfl⟩ := denoteCIList_cons hcs'
      simp only [Arena.canonEqList] at hrun
      obtain ⟨r1, s1, g1, k1⟩ := AM.bind_ok hrun
      obtain ⟨hok1, hx1, hc1, hp1, he1⟩ :=
        IConstantInfo.canonEq_run hok hx hy g1
      rcases AM.ite_ok k1 with ⟨hyes, k2⟩ | ⟨hno, k2⟩
      · obtain ⟨hok2, hx2, hc2, hp2, he2⟩ :=
          ih bs xt yt r s1 s' hok1 (denoteCIList_mono hx1 _ _ hxt)
            (denoteCIList_mono hx1 _ _ hyt) k2
        have hcan : ConLeche.ConstantInfo.canon x = ConLeche.ConstantInfo.canon y := by
          have := hyes
          rw [he1] at this
          simpa [ConLeche.ConstantInfo.canonEq] using this
        refine ⟨hok2, hx1.trans hx2, by rw [hc2, hc1], by rw [hp2, hp1], ?_⟩
        rw [he2]
        simp [ConLeche.canonEqList, hcan]
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        have hcan : ConLeche.ConstantInfo.canon x ≠ ConLeche.ConstantInfo.canon y := by
          intro hEq
          exact hno (by rw [he1]; simp [ConLeche.ConstantInfo.canonEq, hEq])
        refine ⟨hok1, hx1, hc1, hp1, ?_⟩
        simp [ConLeche.canonEqList, hcan]

theorem canonEqList_run {cs cs' : List IConstantInfo}
    {xs xs' : List ConstantInfo} {r : Bool} {s s' : AState} (hok : StateOK s)
    (hcs : Frontend.denoteCIList s.store cs = some xs)
    (hcs' : Frontend.denoteCIList s.store cs' = some xs')
    (hrun : canonEqList cs cs' s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.canonEqList xs xs' :=
  canonEqList_run_aux cs cs' xs xs' r s s' hok hcs hcs' hrun

end ConRon.Bridge

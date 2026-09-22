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

/-! ## The level store's readers and its inversions

`Bridge/Rel.lean` has the expression tier's ten `denote_*_inv` lemmas; the
LEVEL tier's five are wanted only by the lockstep comparison, so they are
here.  Each is three lines off `Arena/WFProofs.lean`'s `denoteL_unfold`,
exactly as the expression ones are off `denoteE_unfold`. -/

/-- con-leche: none — `viewL`'s inversion, off `Bridge/Specs.lean`'s triple
(`Bridge/Checker/Base.lean`'s `viewN_run` is the name tier's twin). -/
theorem viewL_run {h : LIdx} {s s' : AState} {v : LNodeView}
    (hr : viewL h s = .ok (v, s')) : s' = s ∧ s.store.ls.view h = some v :=
  AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ s.store.ls.view h = some r) rfl hr (viewL_spec s h)

/-- con-leche: none — trade the fuel for the rank once, at the top of each
level inversion. -/
theorem denoteL_view_eq {st : LStore} (hwf : LStoreWF st) {i : LIdx}
    {v : LNodeView} (hv : st.view i = some v) :
    denoteL st i = denoteLView st v := by
  obtain ⟨rk, hr⟩ := hwf; exact denoteL_unfold hr hv

theorem denoteL_zero_inv {st : LStore} (hwf : LStoreWF st) {i : LIdx}
    {x : Level} (hv : st.view i = some .zero) (hd : denoteL st i = some x) :
    x = .zero := by
  rw [denoteL_view_eq hwf hv, denoteLView] at hd; exact (Option.some.inj hd).symm

theorem denoteL_succ_inv {st : LStore} (hwf : LStoreWF st) {i a : LIdx}
    {x : Level} (hv : st.view i = some (.succ a)) (hd : denoteL st i = some x) :
    ∃ p, x = .succ p ∧ denoteL st a = some p := by
  rw [denoteL_view_eq hwf hv, denoteLView, Option.map_eq_some_iff] at hd
  obtain ⟨p, hp, rfl⟩ := hd; exact ⟨p, rfl, hp⟩

theorem denoteL_max_inv {st : LStore} (hwf : LStoreWF st) {i a b : LIdx}
    {x : Level} (hv : st.view i = some (.max a b))
    (hd : denoteL st i = some x) :
    ∃ p q, x = .max p q ∧ denoteL st a = some p ∧ denoteL st b = some q := by
  rw [denoteL_view_eq hwf hv, denoteLView, opt2_eq_some_iff] at hd
  obtain ⟨p, q, hp, hq, rfl⟩ := hd; exact ⟨p, q, rfl, hp, hq⟩

theorem denoteL_imax_inv {st : LStore} (hwf : LStoreWF st) {i a b : LIdx}
    {x : Level} (hv : st.view i = some (.imax a b))
    (hd : denoteL st i = some x) :
    ∃ p q, x = .imax p q ∧ denoteL st a = some p ∧ denoteL st b = some q := by
  rw [denoteL_view_eq hwf hv, denoteLView, opt2_eq_some_iff] at hd
  obtain ⟨p, q, hp, hq, rfl⟩ := hd; exact ⟨p, q, rfl, hp, hq⟩

theorem denoteL_param_inv {st : LStore} (hwf : LStoreWF st) {i : LIdx}
    {n : NIdx} {x : Level} (hv : st.view i = some (.param n))
    (hd : denoteL st i = some x) :
    ∃ nm, x = .param nm ∧ denoteN st.ns n = some nm := by
  rw [denoteL_view_eq hwf hv, denoteLView, Option.map_eq_some_iff] at hd
  obtain ⟨nm, hn, rfl⟩ := hd; exact ⟨nm, rfl, hn⟩

/-! ## The renaming, denoted

`canonNameMap ps cs n` is the arena's two-list lookup and
`ConLeche.canonNameMap psN nm` is con-leche's function value; the bridge
between them is one `findIdx?` agreement, and THAT is `denoteN`'s injectivity
at each element (DESIGN §8.3 lesson 13 again: a handle comparison is a name
comparison only because the readback is injective).

The interned numerals enter as a hypothesis rather than as
`canonNames_run`'s conclusion, because ONE `cs` serves BOTH sides of every
comparison (`Arena/Canon.lean`'s module note) and the two sides have different
parameter lists.  `CanonMapD` is that hypothesis, bundled. -/

/-- con-leche: none — **the renaming's data**: the parameter handles denote,
the numeral handles denote the numerals, and the two lists are equally long
(which is what `IConstantVal.canonEq`'s length test buys). -/
structure CanonMapD (ns : NStore) (ps cs : List NIdx)
    (psN : List ConLeche.Name) : Prop where
  params : Frontend.denoteNList ns ps = some psN
  nums : Frontend.denoteNList ns cs
    = some ((List.range cs.length).map (fun i => ConLeche.Name.num .anonymous i))
  len : ps.length = cs.length

/-- con-leche: none — `Frontend.denoteNList` transports across an `NExt`,
which is `Bridge/Rel.lean`'s `denoteNList_ext` at this spelling. -/
theorem CanonMapD.mono {st st' : EStore} (hx : Ext st st') {ps cs : List NIdx}
    {psN : List ConLeche.Name} (h : CanonMapD st.ns ps cs psN) :
    CanonMapD st'.ns ps cs psN where
  params := denoteNListE_ext hx _ _ h.params
  nums := denoteNListE_ext hx _ _ h.nums
  len := h.len

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

/-- con-leche: none — a name-handle list's `i`-th handle denotes the denoted
list's `i`-th name.  (`Bridge/Rel.lean` has the same three lines for `denoteE`
and `denoteL`; the name tier's copy is wanted only here.) -/
theorem denoteNList_get {ns : NStore} :
    ∀ (hs : List NIdx) (xs : List ConLeche.Name),
      Frontend.denoteNList ns hs = some xs → ∀ (i : Nat) (hi : i < hs.length),
        ∃ (hx : i < xs.length), denoteN ns hs[i] = some xs[i] := by
  intro hs
  induction hs with
  | nil => intro xs _ i hi; simp at hi
  | cons a as ih =>
    intro xs h i hi
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
        cases i with
        | zero => exact ⟨by simp, by simpa using ha⟩
        | succ k =>
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
          obtain ⟨hk, hd⟩ := ih ys has k hi
          exact ⟨by simpa using hk, by simpa using hd⟩

/-- con-leche: none — **the two `findIdx?`s are one**: the parameter handle
list finds `n` exactly where the denoted list finds `n`'s name.  The `→` half
is `denoteN`'s functionality and the `←` half its injectivity. -/
theorem canonFindIdx_denote {ns : NStore} (hns : NStoreWF ns) :
    ∀ (ps : List NIdx) (psN : List ConLeche.Name),
      Frontend.denoteNList ns ps = some psN →
      ∀ (n : NIdx) (nm : ConLeche.Name), denoteN ns n = some nm →
        ps.findIdx? (fun p => p == n) = psN.findIdx? (fun p => p == nm) := by
  intro ps
  induction ps with
  | nil =>
    intro psN h n nm _
    simp only [Frontend.denoteNList, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro psN h n nm hn
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
        have hhead : (a == n) = (y == nm) := by
          by_cases hae : a = n
          · subst hae
            rw [hn] at ha
            obtain rfl := Option.some.inj ha
            simp
          · have hne' : ¬ y = nm := by
              intro hxy; subst hxy
              exact hae (denoteN_inj hns ha hn)
            rw [beq_eq_false_iff_ne.mpr hae, beq_eq_false_iff_ne.mpr hne']
        simp only [List.findIdx?_cons, hhead, ih ys has n nm hn]

/-- con-leche: ConLeche/Kernel/Canon.lean:67-73 canonNameMap — **the renaming
commutes with the readback**: the handle the two-list lookup returns denotes
the name con-leche's function value returns. -/
theorem canonNameMap_denote {ns : NStore} (hns : NStoreWF ns)
    {ps cs : List NIdx} {psN : List ConLeche.Name} (hm : CanonMapD ns ps cs psN)
    {n : NIdx} {nm : ConLeche.Name} (hn : denoteN ns n = some nm) :
    denoteN ns (canonNameMap ps cs n) = some (ConLeche.canonNameMap psN nm) := by
  have hfi := canonFindIdx_denote hns ps psN hm.params n nm hn
  simp only [Arena.canonNameMap, ConLeche.canonNameMap, hfi]
  cases hidx : psN.findIdx? (fun p => p == nm) with
  | none => exact hn
  | some i =>
    have hlt : i < psN.length := (List.findIdx?_eq_some_iff_findIdx_eq.mp hidx).1
    have hps : ps.length = psN.length := denoteNList_length ps psN hm.params
    have hlen := hm.len
    have hcs : i < cs.length := by omega
    obtain ⟨hxi, hd⟩ := denoteNList_get cs _ hm.nums i hcs
    show denoteN ns (cs.getD i n) = some (ConLeche.Name.num .anonymous i)
    rw [← List.getElem_eq_getD (l := cs) (i := i) (h := hcs) n]
    simpa using hd

/-! ## `Level`'s `==`, as congruences

`ConLeche.Level`'s `BEq` is its own (`instBEqLevel`, not the `DecidableEq`
default), and `simp` does not take it apart, so the four shapes the lockstep
comparison needs are spelled out once.  `LawfulBEq Level` is what makes each
one two lines. -/

private theorem level_beq_false {a b : Level} (h : a ≠ b) : (a == b) = false :=
  beq_eq_false_iff_ne.mpr h

private theorem level_beq_succ {a b : Level} :
    (Level.succ a == Level.succ b) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h; injection h
  · intro h; rw [h]

private theorem level_beq_max {a b c d : Level} :
    (Level.max a b == Level.max c d) = (a == c && b == d) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h; injection h with h1 h2; exact ⟨h1, h2⟩
  · intro h; rw [h.1, h.2]

private theorem level_beq_imax {a b c d : Level} :
    (Level.imax a b == Level.imax c d) = (a == c && b == d) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h; injection h with h1 h2; exact ⟨h1, h2⟩
  · intro h; rw [h.1, h.2]

/-! ## The level comparison -/

/-- con-leche: ConLeche/Kernel/Canon.lean:27-34 canonLevel — **the lockstep
level comparison is the canonical-form comparison**: the twin descends the two
handles together and answers `canonLevel m u == canonLevel m' v` at the
denoted levels.

Twenty-five arms, of which twenty are the mismatch (`canonLevel` rewrites only
the `.param` leaf, so it preserves every node's constructor and two different
constructors can never become equal), four are the structural recursions and
the twenty-fifth is the renaming — which is `canonNameMap_denote` above and
`denoteN`'s injectivity, once each. -/
theorem canonLevelEq_run {ps ps' cs : List NIdx}
    {psN ps'N : List ConLeche.Name} :
    ∀ (fuel : Nat) {u v : LIdx} {x y : Level} {r : Bool} {s s' : AState},
      StateOK s → CanonMapD s.store.ns ps cs psN →
      CanonMapD s.store.ns ps' cs ps'N →
      denoteL s.store.ls u = some x → denoteL s.store.ls v = some y →
      canonLevelEq ps ps' cs fuel u v s = .ok (r, s') →
      s' = s ∧ r = (ConLeche.canonLevel (ConLeche.canonNameMap psN) x ==
        ConLeche.canonLevel (ConLeche.canonNameMap ps'N) y) := by
  intro fuel
  induction fuel with
  | zero =>
    intro u v x y r s s' _ _ _ _ _ hrun
    exact absurd hrun (AM.Never.fail _ _ _ _)
  | succ fuel ih =>
    intro u v x y r s s' hok hm hm' hx hy hrun
    obtain ⟨rk, hrk⟩ := hok.wf
    have hlw : LStoreWF s.store.ls := hrk.lsWF
    have hns : NStoreWF s.store.ns := hrk.nsWF
    simp only [Arena.canonLevelEq] at hrun
    obtain ⟨va, s1, g1, k1⟩ := AM.bind_ok hrun
    obtain ⟨rfl, hva⟩ := viewL_run g1
    obtain ⟨vb, s2, g2, k2⟩ := AM.bind_ok k1
    obtain ⟨rfl, hvb⟩ := viewL_run g2
    cases va with
    | zero =>
      obtain rfl := denoteL_zero_inv hlw hva hx
      cases vb with
      | zero =>
        obtain rfl := denoteL_zero_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonLevel]⟩
      | succ a2 =>
        obtain ⟨ya, rfl, hya⟩ := denoteL_succ_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
      | max a2 b2 =>
        obtain ⟨ya, yb, rfl, hya, hyb⟩ := denoteL_max_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
      | imax a2 b2 =>
        obtain ⟨ya, yb, rfl, hya, hyb⟩ := denoteL_imax_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
      | param n2 =>
        obtain ⟨yn, rfl, hyn⟩ := denoteL_param_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
    | succ a =>
      obtain ⟨xa, rfl, hxa⟩ := denoteL_succ_inv hlw hva hx
      cases vb with
      | zero =>
        obtain rfl := denoteL_zero_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
      | succ a2 =>
        obtain ⟨ya, rfl, hya⟩ := denoteL_succ_inv hlw hvb hy
        obtain ⟨rfl, he⟩ := ih hok hm hm' hxa hya k2
        exact ⟨rfl, by simp only [ConLeche.canonLevel, level_beq_succ, he]⟩
      | max a2 b2 =>
        obtain ⟨ya, yb, rfl, hya, hyb⟩ := denoteL_max_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
      | imax a2 b2 =>
        obtain ⟨ya, yb, rfl, hya, hyb⟩ := denoteL_imax_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
      | param n2 =>
        obtain ⟨yn, rfl, hyn⟩ := denoteL_param_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
    | max a b =>
      obtain ⟨xa, xb, rfl, hxa, hxb⟩ := denoteL_max_inv hlw hva hx
      cases vb with
      | zero =>
        obtain rfl := denoteL_zero_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
      | succ a2 =>
        obtain ⟨ya, rfl, hya⟩ := denoteL_succ_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
      | max a2 b2 =>
        obtain ⟨ya, yb, rfl, hya, hyb⟩ := denoteL_max_inv hlw hvb hy
        obtain ⟨c1, s3, g3, k3⟩ := AM.bind_ok k2
        obtain ⟨rfl, he1⟩ := ih hok hm hm' hxa hya g3
        rcases AM.ite_ok k3 with ⟨hc, k4⟩ | ⟨hc, k4⟩
        · obtain ⟨rfl, he2⟩ := ih hok hm hm' hxb hyb k4
          refine ⟨rfl, ?_⟩
          have h1 := eq_of_beq (he1 ▸ hc)
          simp only [ConLeche.canonLevel, level_beq_max, h1, beq_self_eq_true,
            Bool.true_and, he2]
        · obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
          refine ⟨rfl, ?_⟩
          have h1 : (ConLeche.canonLevel (ConLeche.canonNameMap psN) xa ==
              ConLeche.canonLevel (ConLeche.canonNameMap ps'N) ya) = false := by
            cases hb : (ConLeche.canonLevel (ConLeche.canonNameMap psN) xa ==
                ConLeche.canonLevel (ConLeche.canonNameMap ps'N) ya)
            · rfl
            · exact absurd (he1.trans hb) hc
          simp only [ConLeche.canonLevel, level_beq_max, h1, Bool.false_and]
      | imax a2 b2 =>
        obtain ⟨ya, yb, rfl, hya, hyb⟩ := denoteL_imax_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
      | param n2 =>
        obtain ⟨yn, rfl, hyn⟩ := denoteL_param_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
    | imax a b =>
      obtain ⟨xa, xb, rfl, hxa, hxb⟩ := denoteL_imax_inv hlw hva hx
      cases vb with
      | zero =>
        obtain rfl := denoteL_zero_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
      | succ a2 =>
        obtain ⟨ya, rfl, hya⟩ := denoteL_succ_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
      | max a2 b2 =>
        obtain ⟨ya, yb, rfl, hya, hyb⟩ := denoteL_max_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
      | imax a2 b2 =>
        obtain ⟨ya, yb, rfl, hya, hyb⟩ := denoteL_imax_inv hlw hvb hy
        obtain ⟨c1, s3, g3, k3⟩ := AM.bind_ok k2
        obtain ⟨rfl, he1⟩ := ih hok hm hm' hxa hya g3
        rcases AM.ite_ok k3 with ⟨hc, k4⟩ | ⟨hc, k4⟩
        · obtain ⟨rfl, he2⟩ := ih hok hm hm' hxb hyb k4
          refine ⟨rfl, ?_⟩
          have h1 := eq_of_beq (he1 ▸ hc)
          simp only [ConLeche.canonLevel, level_beq_imax, h1, beq_self_eq_true,
            Bool.true_and, he2]
        · obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
          refine ⟨rfl, ?_⟩
          have h1 : (ConLeche.canonLevel (ConLeche.canonNameMap psN) xa ==
              ConLeche.canonLevel (ConLeche.canonNameMap ps'N) ya) = false := by
            cases hb : (ConLeche.canonLevel (ConLeche.canonNameMap psN) xa ==
                ConLeche.canonLevel (ConLeche.canonNameMap ps'N) ya)
            · rfl
            · exact absurd (he1.trans hb) hc
          simp only [ConLeche.canonLevel, level_beq_imax, h1, Bool.false_and]
      | param n2 =>
        obtain ⟨yn, rfl, hyn⟩ := denoteL_param_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
    | param n =>
      obtain ⟨xn, rfl, hxn⟩ := denoteL_param_inv hlw hva hx
      cases vb with
      | zero =>
        obtain rfl := denoteL_zero_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
      | succ a2 =>
        obtain ⟨ya, rfl, hya⟩ := denoteL_succ_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
      | max a2 b2 =>
        obtain ⟨ya, yb, rfl, hya, hyb⟩ := denoteL_max_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
      | imax a2 b2 =>
        obtain ⟨ya, yb, rfl, hya, hyb⟩ := denoteL_imax_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, (level_beq_false (by simp [ConLeche.canonLevel])).symm⟩
      | param n2 =>
        obtain ⟨yn, rfl, hyn⟩ := denoteL_param_inv hlw hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        refine ⟨rfl, ?_⟩
        have hA := canonNameMap_denote hns hm hxn
        have hB := canonNameMap_denote hns hm' hyn
        simp only [ConLeche.canonLevel]
        rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Level.param.injEq]
        constructor
        · intro h
          rw [h, hB] at hA
          exact (Option.some.inj hA).symm
        · intro h
          exact denoteN_inj hns hA (h ▸ hB)

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

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

/-! ## The universe-argument lists -/

/-- con-leche: none — `List`'s `==`, as a congruence.  (The same three lines
as `level_beq_max`, at the list constructor; `simp` does not take a derived
`BEq` apart either.) -/
private theorem list_beq_cons {α : Type} [BEq α] [LawfulBEq α] {a b : α}
    {as bs : List α} : (a :: as == b :: bs) = ((a == b) && (as == bs)) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h; injection h with h1 h2; exact ⟨h1, h2⟩
  · intro h; rw [h.1, h.2]

/-- con-leche: none — `denoteLList`'s cons inversion (`Bridge/Checker/Canon.lean`'s
`denoteCIList_cons` at the level tier). -/
theorem denoteLList_cons {st : LStore} {a : LIdx} {as : List LIdx}
    {zs : List Level} (h : denoteLList st (a :: as) = some zs) :
    ∃ x xs, denoteL st a = some x ∧ denoteLList st as = some xs ∧ zs = x :: xs := by
  simp only [denoteLList, opt2_eq_some_iff] at h
  obtain ⟨x, xs, hx, hxs, rfl⟩ := h
  exact ⟨x, xs, hx, hxs, rfl⟩

/-- con-leche: ConLeche/Kernel/Canon.lean:126-146 canonExprEqFast — the
`.const` clause's universe-argument comparison, at two level-handle LISTS. -/
theorem canonLevelListEq_run {ps ps' cs : List NIdx}
    {psN ps'N : List ConLeche.Name} (fuel : Nat) :
    ∀ (us vs : List LIdx) {xs ys : List Level} {r : Bool} {s s' : AState},
      StateOK s → CanonMapD s.store.ns ps cs psN →
      CanonMapD s.store.ns ps' cs ps'N →
      denoteLList s.store.ls us = some xs →
      denoteLList s.store.ls vs = some ys →
      canonLevelListEq ps ps' cs fuel us vs s = .ok (r, s') →
      s' = s ∧ r = (xs.map (ConLeche.canonLevel (ConLeche.canonNameMap psN)) ==
        ys.map (ConLeche.canonLevel (ConLeche.canonNameMap ps'N))) := by
  intro us
  induction us with
  | nil =>
    intro vs xs ys r s s' hok hm hm' hxs hys hrun
    simp only [denoteLList, Option.some.injEq] at hxs
    subst hxs
    cases vs with
    | nil =>
      simp only [denoteLList, Option.some.injEq] at hys
      subst hys
      simp only [Arena.canonLevelListEq] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨rfl, by simp⟩
    | cons b bs =>
      obtain ⟨q, qs, -, -, rfl⟩ := denoteLList_cons hys
      simp only [Arena.canonLevelListEq] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨rfl, by simp⟩
  | cons a as ih =>
    intro vs xs ys r s s' hok hm hm' hxs hys hrun
    obtain ⟨x, xt, hx, hxt, rfl⟩ := denoteLList_cons hxs
    cases vs with
    | nil =>
      simp only [denoteLList, Option.some.injEq] at hys
      subst hys
      simp only [Arena.canonLevelListEq] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨rfl, by simp⟩
    | cons b bs =>
      obtain ⟨y, yt, hy, hyt, rfl⟩ := denoteLList_cons hys
      simp only [Arena.canonLevelListEq] at hrun
      obtain ⟨c1, s1, g1, k1⟩ := AM.bind_ok hrun
      obtain ⟨rfl, he1⟩ := canonLevelEq_run fuel hok hm hm' hx hy g1
      rcases AM.ite_ok k1 with ⟨hc, k2⟩ | ⟨hc, k2⟩
      · obtain ⟨rfl, he2⟩ := ih bs hok hm hm' hxt hyt k2
        refine ⟨rfl, ?_⟩
        have h1 := eq_of_beq (he1 ▸ hc)
        simp only [List.map_cons, list_beq_cons, h1, beq_self_eq_true,
          Bool.true_and, he2]
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        refine ⟨rfl, ?_⟩
        have h1 : (ConLeche.canonLevel (ConLeche.canonNameMap psN) x ==
            ConLeche.canonLevel (ConLeche.canonNameMap ps'N) y) = false := by
          cases hb : (ConLeche.canonLevel (ConLeche.canonNameMap psN) x ==
              ConLeche.canonLevel (ConLeche.canonNameMap ps'N) y)
          · rfl
          · exact absurd (he1.trans hb) hc
        simp only [List.map_cons, list_beq_cons, h1, Bool.false_and]

/-- con-leche: none — `denoteLs`'s view inversion. -/
theorem denoteLs_view_inv {st : LsStore} {i : LsIdx} {hs : LsNodeView}
    {xs : List Level} (hv : st.view i = some hs) (hd : denoteLs st i = some xs) :
    denoteLList st.ls hs = some xs := by
  simp only [denoteLs, hv] at hd; exact hd

/-- con-leche: none — `viewLs`'s inversion, off `Bridge/Specs.lean`'s
triple. -/
theorem viewLs_run {h : LsIdx} {s s' : AState} {v : LsNodeView}
    (hr : viewLs h s = .ok (v, s')) : s' = s ∧ s.store.lss.view h = some v :=
  AM.of_run (P := fun t => t = s)
    (Q := fun r t => t = s ∧ s.store.lss.view h = some r) rfl hr (viewLs_spec s h)

/-- con-leche: ConLeche/Kernel/Canon.lean:126-146 canonExprEqFast — the same
at two interned universe-argument list HANDLES. -/
theorem canonLevelsEq_run {ps ps' cs : List NIdx}
    {psN ps'N : List ConLeche.Name} {fuel : Nat} {us vs : LsIdx}
    {xs ys : List Level} {r : Bool} {s s' : AState}
    (hok : StateOK s) (hm : CanonMapD s.store.ns ps cs psN)
    (hm' : CanonMapD s.store.ns ps' cs ps'N)
    (hx : denoteLs s.store.lss us = some xs)
    (hy : denoteLs s.store.lss vs = some ys)
    (hrun : canonLevelsEq ps ps' cs fuel us vs s = .ok (r, s')) :
    s' = s ∧ r = (xs.map (ConLeche.canonLevel (ConLeche.canonNameMap psN)) ==
      ys.map (ConLeche.canonLevel (ConLeche.canonNameMap ps'N))) := by
  simp only [Arena.canonLevelsEq] at hrun
  obtain ⟨va, s1, g1, k1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, hva⟩ := viewLs_run g1
  obtain ⟨vb, s2, g2, k2⟩ := AM.bind_ok k1
  obtain ⟨rfl, hvb⟩ := viewLs_run g2
  exact canonLevelListEq_run fuel va vb hok hm hm'
    (denoteLs_view_inv hva hx) (denoteLs_view_inv hvb hy) k2

/-! ## The term comparison -/

/-- con-leche: ConLeche/Kernel/Canon.lean:126-146 canonExprEqFast — **the
lockstep term comparison is con-leche's**, arm for arm.

The bridge is to `canonExprEqFast` and NOT to `canonExpr … = canonExpr …`:
con-leche proves the two equivalent itself (`canonExprEqFast_iff`, a pure
`Expr` induction), and taking its word for that is what keeps this theorem a
transliteration instead of a second proof of the same fact.  A hundred arms,
of which ninety are the constructor mismatch and ten are con-leche's own
clauses. -/
theorem canonExprEq_run {ps ps' cs : List NIdx}
    {psN ps'N : List ConLeche.Name} :
    ∀ (fuel : Nat) {a b : EIdx} {x y : Expr} {r : Bool} {s s' : AState},
      StateOK s → CanonMapD s.store.ns ps cs psN →
      CanonMapD s.store.ns ps' cs ps'N →
      denoteE s.store a = some x → denoteE s.store b = some y →
      canonExprEq ps ps' cs fuel a b s = .ok (r, s') →
      s' = s ∧ r = ConLeche.canonExprEqFast (ConLeche.canonNameMap psN)
        (ConLeche.canonNameMap ps'N) x y := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b x y r s s' _ _ _ _ _ hrun
    exact absurd hrun (AM.Never.fail _ _ _ _)
  | succ fuel ih =>
    intro a b x y r s s' hok hm hm' hx hy hrun
    have hwf : StoreWF s.store := hok.wf
    obtain ⟨rk, hrk⟩ := hok.wf
    have hns : NStoreWF s.store.ns := hrk.nsWF
    simp only [Arena.canonExprEq] at hrun
    obtain ⟨va, s1, g1, k1⟩ := AM.bind_ok hrun
    obtain ⟨rfl, hva⟩ := viewE_run g1
    obtain ⟨vb, s2, g2, k2⟩ := AM.bind_ok k1
    obtain ⟨rfl, hvb⟩ := viewE_run g2
    cases va with
    | bvar iA =>
      obtain rfl := denote_bvar_inv hwf hva hx
      cases vb with
      | bvar iB =>
        obtain rfl := denote_bvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | fvar kB tB =>
        obtain ⟨yT, rfl, hyT⟩ := denote_fvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | sort uB =>
        obtain ⟨yU, rfl, hyU⟩ := denote_sort_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | const nB lB =>
        obtain ⟨yN, yL, rfl, hyN, hyL⟩ := denote_const_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | app fB aB =>
        obtain ⟨yF, yA, rfl, hyF, hyA⟩ := denote_app_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | lam tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_lam_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | forallE tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_forallE_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | letE tB wB bB =>
        obtain ⟨yT, yW, yB, rfl, hyT, hyW, hyB⟩ := denote_letE_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | lit qB =>
        obtain rfl := denote_lit_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | proj pB jB eB =>
        obtain ⟨yN, yE, rfl, hyN, hyE⟩ := denote_proj_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
    | fvar kA tA =>
      obtain ⟨xT, rfl, hxT⟩ := denote_fvar_inv hwf hva hx
      cases vb with
      | bvar iB =>
        obtain rfl := denote_bvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | fvar kB tB =>
        obtain ⟨yT, rfl, hyT⟩ := denote_fvar_inv hwf hvb hy
        rcases AM.ite_ok k2 with ⟨hc, k3⟩ | ⟨hc, k3⟩
        · obtain ⟨rfl, he⟩ := ih hok hm hm' hxT hyT k3
          exact ⟨rfl, by simp only [ConLeche.canonExprEqFast, hc, Bool.true_and, he]⟩
        · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
          have hcf : (kA == kB) = false := by simpa using hc
          exact ⟨rfl, by simp only [ConLeche.canonExprEqFast, hcf, Bool.false_and]⟩
      | sort uB =>
        obtain ⟨yU, rfl, hyU⟩ := denote_sort_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | const nB lB =>
        obtain ⟨yN, yL, rfl, hyN, hyL⟩ := denote_const_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | app fB aB =>
        obtain ⟨yF, yA, rfl, hyF, hyA⟩ := denote_app_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | lam tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_lam_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | forallE tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_forallE_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | letE tB wB bB =>
        obtain ⟨yT, yW, yB, rfl, hyT, hyW, hyB⟩ := denote_letE_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | lit qB =>
        obtain rfl := denote_lit_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | proj pB jB eB =>
        obtain ⟨yN, yE, rfl, hyN, hyE⟩ := denote_proj_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
    | sort uA =>
      obtain ⟨xU, rfl, hxU⟩ := denote_sort_inv hwf hva hx
      cases vb with
      | bvar iB =>
        obtain rfl := denote_bvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | fvar kB tB =>
        obtain ⟨yT, rfl, hyT⟩ := denote_fvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | sort uB =>
        obtain ⟨yU, rfl, hyU⟩ := denote_sort_inv hwf hvb hy
        obtain ⟨rfl, he⟩ := canonLevelEq_run fuel hok hm hm' hxU hyU k2
        exact ⟨rfl, by simp only [ConLeche.canonExprEqFast, he]⟩
      | const nB lB =>
        obtain ⟨yN, yL, rfl, hyN, hyL⟩ := denote_const_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | app fB aB =>
        obtain ⟨yF, yA, rfl, hyF, hyA⟩ := denote_app_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | lam tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_lam_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | forallE tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_forallE_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | letE tB wB bB =>
        obtain ⟨yT, yW, yB, rfl, hyT, hyW, hyB⟩ := denote_letE_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | lit qB =>
        obtain rfl := denote_lit_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | proj pB jB eB =>
        obtain ⟨yN, yE, rfl, hyN, hyE⟩ := denote_proj_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
    | const nA lA =>
      obtain ⟨xN, xL, rfl, hxN, hxL⟩ := denote_const_inv hwf hva hx
      cases vb with
      | bvar iB =>
        obtain rfl := denote_bvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | fvar kB tB =>
        obtain ⟨yT, rfl, hyT⟩ := denote_fvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | sort uB =>
        obtain ⟨yU, rfl, hyU⟩ := denote_sort_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | const nB lB =>
        obtain ⟨yN, yL, rfl, hyN, hyL⟩ := denote_const_inv hwf hvb hy
        rcases AM.ite_ok k2 with ⟨hc, k3⟩ | ⟨hc, k3⟩
        · obtain ⟨rfl, he⟩ := canonLevelsEq_run hok hm hm' hxL hyL k3
          refine ⟨rfl, ?_⟩
          obtain rfl := eq_of_beq hc
          rw [hxN] at hyN
          obtain rfl := Option.some.inj hyN
          simp only [ConLeche.canonExprEqFast, beq_self_eq_true, Bool.true_and, he]
        · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
          refine ⟨rfl, ?_⟩
          have hnm : (xN == yN) = false := by
            cases hb : (xN == yN)
            · rfl
            · exfalso
              have hyN' := hyN
              rw [← eq_of_beq hb] at hyN'
              exact hc (beq_iff_eq.mpr (denoteN_inj hns hxN hyN'))
          simp only [ConLeche.canonExprEqFast, hnm, Bool.false_and]
      | app fB aB =>
        obtain ⟨yF, yA, rfl, hyF, hyA⟩ := denote_app_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | lam tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_lam_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | forallE tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_forallE_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | letE tB wB bB =>
        obtain ⟨yT, yW, yB, rfl, hyT, hyW, hyB⟩ := denote_letE_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | lit qB =>
        obtain rfl := denote_lit_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | proj pB jB eB =>
        obtain ⟨yN, yE, rfl, hyN, hyE⟩ := denote_proj_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
    | app fA aA =>
      obtain ⟨xF, xA, rfl, hxF, hxA⟩ := denote_app_inv hwf hva hx
      cases vb with
      | bvar iB =>
        obtain rfl := denote_bvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | fvar kB tB =>
        obtain ⟨yT, rfl, hyT⟩ := denote_fvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | sort uB =>
        obtain ⟨yU, rfl, hyU⟩ := denote_sort_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | const nB lB =>
        obtain ⟨yN, yL, rfl, hyN, hyL⟩ := denote_const_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | app fB aB =>
        obtain ⟨yF, yA, rfl, hyF, hyA⟩ := denote_app_inv hwf hvb hy
        obtain ⟨c1, s3, g3, k3⟩ := AM.bind_ok k2
        obtain ⟨rfl, he1⟩ := ih hok hm hm' hxF hyF g3
        rcases AM.ite_ok k3 with ⟨hc, k4⟩ | ⟨hc, k4⟩
        · obtain ⟨rfl, he2⟩ := ih hok hm hm' hxA hyA k4
          refine ⟨rfl, ?_⟩
          have h1 := he1 ▸ hc
          simp only [ConLeche.canonExprEqFast, h1, Bool.true_and, he2]
        · obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
          refine ⟨rfl, ?_⟩
          have h1 : ConLeche.canonExprEqFast (ConLeche.canonNameMap psN)
              (ConLeche.canonNameMap ps'N) xF yF = false := by
            cases hb : ConLeche.canonExprEqFast (ConLeche.canonNameMap psN)
                (ConLeche.canonNameMap ps'N) xF yF
            · rfl
            · exact absurd (he1.trans hb) hc
          simp only [ConLeche.canonExprEqFast, h1, Bool.false_and]
      | lam tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_lam_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | forallE tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_forallE_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | letE tB wB bB =>
        obtain ⟨yT, yW, yB, rfl, hyT, hyW, hyB⟩ := denote_letE_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | lit qB =>
        obtain rfl := denote_lit_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | proj pB jB eB =>
        obtain ⟨yN, yE, rfl, hyN, hyE⟩ := denote_proj_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
    | lam tA bA mA =>
      obtain ⟨xT, xB, rfl, hxT, hxB⟩ := denote_lam_inv hwf hva hx
      cases vb with
      | bvar iB =>
        obtain rfl := denote_bvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | fvar kB tB =>
        obtain ⟨yT, rfl, hyT⟩ := denote_fvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | sort uB =>
        obtain ⟨yU, rfl, hyU⟩ := denote_sort_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | const nB lB =>
        obtain ⟨yN, yL, rfl, hyN, hyL⟩ := denote_const_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | app fB aB =>
        obtain ⟨yF, yA, rfl, hyF, hyA⟩ := denote_app_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | lam tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_lam_inv hwf hvb hy
        obtain ⟨c1, s3, g3, k3⟩ := AM.bind_ok k2
        obtain ⟨rfl, he1⟩ := ih hok hm hm' hxT hyT g3
        rcases AM.ite_ok k3 with ⟨hc, k4⟩ | ⟨hc, k4⟩
        · obtain ⟨rfl, he2⟩ := ih hok hm hm' hxB hyB k4
          refine ⟨rfl, ?_⟩
          have h1 := he1 ▸ hc
          simp only [ConLeche.canonExprEqFast, h1, Bool.true_and, he2]
        · obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
          refine ⟨rfl, ?_⟩
          have h1 : ConLeche.canonExprEqFast (ConLeche.canonNameMap psN)
              (ConLeche.canonNameMap ps'N) xT yT = false := by
            cases hb : ConLeche.canonExprEqFast (ConLeche.canonNameMap psN)
                (ConLeche.canonNameMap ps'N) xT yT
            · rfl
            · exact absurd (he1.trans hb) hc
          simp only [ConLeche.canonExprEqFast, h1, Bool.false_and]
      | forallE tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_forallE_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | letE tB wB bB =>
        obtain ⟨yT, yW, yB, rfl, hyT, hyW, hyB⟩ := denote_letE_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | lit qB =>
        obtain rfl := denote_lit_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | proj pB jB eB =>
        obtain ⟨yN, yE, rfl, hyN, hyE⟩ := denote_proj_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
    | forallE tA bA mA =>
      obtain ⟨xT, xB, rfl, hxT, hxB⟩ := denote_forallE_inv hwf hva hx
      cases vb with
      | bvar iB =>
        obtain rfl := denote_bvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | fvar kB tB =>
        obtain ⟨yT, rfl, hyT⟩ := denote_fvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | sort uB =>
        obtain ⟨yU, rfl, hyU⟩ := denote_sort_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | const nB lB =>
        obtain ⟨yN, yL, rfl, hyN, hyL⟩ := denote_const_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | app fB aB =>
        obtain ⟨yF, yA, rfl, hyF, hyA⟩ := denote_app_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | lam tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_lam_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | forallE tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_forallE_inv hwf hvb hy
        obtain ⟨c1, s3, g3, k3⟩ := AM.bind_ok k2
        obtain ⟨rfl, he1⟩ := ih hok hm hm' hxT hyT g3
        rcases AM.ite_ok k3 with ⟨hc, k4⟩ | ⟨hc, k4⟩
        · obtain ⟨rfl, he2⟩ := ih hok hm hm' hxB hyB k4
          refine ⟨rfl, ?_⟩
          have h1 := he1 ▸ hc
          simp only [ConLeche.canonExprEqFast, h1, Bool.true_and, he2]
        · obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
          refine ⟨rfl, ?_⟩
          have h1 : ConLeche.canonExprEqFast (ConLeche.canonNameMap psN)
              (ConLeche.canonNameMap ps'N) xT yT = false := by
            cases hb : ConLeche.canonExprEqFast (ConLeche.canonNameMap psN)
                (ConLeche.canonNameMap ps'N) xT yT
            · rfl
            · exact absurd (he1.trans hb) hc
          simp only [ConLeche.canonExprEqFast, h1, Bool.false_and]
      | letE tB wB bB =>
        obtain ⟨yT, yW, yB, rfl, hyT, hyW, hyB⟩ := denote_letE_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | lit qB =>
        obtain rfl := denote_lit_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | proj pB jB eB =>
        obtain ⟨yN, yE, rfl, hyN, hyE⟩ := denote_proj_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
    | letE tA wA bA =>
      obtain ⟨xT, xW, xB, rfl, hxT, hxW, hxB⟩ := denote_letE_inv hwf hva hx
      cases vb with
      | bvar iB =>
        obtain rfl := denote_bvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | fvar kB tB =>
        obtain ⟨yT, rfl, hyT⟩ := denote_fvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | sort uB =>
        obtain ⟨yU, rfl, hyU⟩ := denote_sort_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | const nB lB =>
        obtain ⟨yN, yL, rfl, hyN, hyL⟩ := denote_const_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | app fB aB =>
        obtain ⟨yF, yA, rfl, hyF, hyA⟩ := denote_app_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | lam tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_lam_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | forallE tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_forallE_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | letE tB wB bB =>
        obtain ⟨yT, yW, yB, rfl, hyT, hyW, hyB⟩ := denote_letE_inv hwf hvb hy
        obtain ⟨c1, s3, g3, k3⟩ := AM.bind_ok k2
        obtain ⟨rfl, he1⟩ := ih hok hm hm' hxT hyT g3
        rcases AM.ite_ok k3 with ⟨hc1, k4⟩ | ⟨hc1, k4⟩
        · obtain ⟨c2, s4, g4, k5⟩ := AM.bind_ok k4
          obtain ⟨rfl, he2⟩ := ih hok hm hm' hxW hyW g4
          rcases AM.ite_ok k5 with ⟨hc2, k6⟩ | ⟨hc2, k6⟩
          · obtain ⟨rfl, he3⟩ := ih hok hm hm' hxB hyB k6
            refine ⟨rfl, ?_⟩
            have h1 := he1 ▸ hc1
            have h2 := he2 ▸ hc2
            simp only [ConLeche.canonExprEqFast, h1, h2, Bool.and_self, Bool.true_and, he3]
          · obtain ⟨rfl, rfl⟩ := AM.pure_ok k6
            refine ⟨rfl, ?_⟩
            have h1 := he1 ▸ hc1
            have h2 : ConLeche.canonExprEqFast (ConLeche.canonNameMap psN)
                (ConLeche.canonNameMap ps'N) xW yW = false := by
              cases hb : ConLeche.canonExprEqFast (ConLeche.canonNameMap psN)
                  (ConLeche.canonNameMap ps'N) xW yW
              · rfl
              · exact absurd (he2.trans hb) hc2
            simp only [ConLeche.canonExprEqFast, h1, h2, Bool.true_and, Bool.false_and]
        · obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
          refine ⟨rfl, ?_⟩
          have h1 : ConLeche.canonExprEqFast (ConLeche.canonNameMap psN)
              (ConLeche.canonNameMap ps'N) xT yT = false := by
            cases hb : ConLeche.canonExprEqFast (ConLeche.canonNameMap psN)
                (ConLeche.canonNameMap ps'N) xT yT
            · rfl
            · exact absurd (he1.trans hb) hc1
          simp only [ConLeche.canonExprEqFast, h1, Bool.false_and]
      | lit qB =>
        obtain rfl := denote_lit_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | proj pB jB eB =>
        obtain ⟨yN, yE, rfl, hyN, hyE⟩ := denote_proj_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
    | lit qA =>
      obtain rfl := denote_lit_inv hwf hva hx
      cases vb with
      | bvar iB =>
        obtain rfl := denote_bvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | fvar kB tB =>
        obtain ⟨yT, rfl, hyT⟩ := denote_fvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | sort uB =>
        obtain ⟨yU, rfl, hyU⟩ := denote_sort_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | const nB lB =>
        obtain ⟨yN, yL, rfl, hyN, hyL⟩ := denote_const_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | app fB aB =>
        obtain ⟨yF, yA, rfl, hyF, hyA⟩ := denote_app_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | lam tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_lam_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | forallE tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_forallE_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | letE tB wB bB =>
        obtain ⟨yT, yW, yB, rfl, hyT, hyW, hyB⟩ := denote_letE_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | lit qB =>
        obtain rfl := denote_lit_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | proj pB jB eB =>
        obtain ⟨yN, yE, rfl, hyN, hyE⟩ := denote_proj_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
    | proj pA jA eA =>
      obtain ⟨xN, xE, rfl, hxN, hxE⟩ := denote_proj_inv hwf hva hx
      cases vb with
      | bvar iB =>
        obtain rfl := denote_bvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | fvar kB tB =>
        obtain ⟨yT, rfl, hyT⟩ := denote_fvar_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | sort uB =>
        obtain ⟨yU, rfl, hyU⟩ := denote_sort_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | const nB lB =>
        obtain ⟨yN, yL, rfl, hyN, hyL⟩ := denote_const_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | app fB aB =>
        obtain ⟨yF, yA, rfl, hyF, hyA⟩ := denote_app_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | lam tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_lam_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | forallE tB bB mB =>
        obtain ⟨yT, yB, rfl, hyT, hyB⟩ := denote_forallE_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | letE tB wB bB =>
        obtain ⟨yT, yW, yB, rfl, hyT, hyW, hyB⟩ := denote_letE_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | lit qB =>
        obtain rfl := denote_lit_inv hwf hvb hy
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        exact ⟨rfl, by simp [ConLeche.canonExprEqFast]⟩
      | proj pB jB eB =>
        obtain ⟨yN, yE, rfl, hyN, hyE⟩ := denote_proj_inv hwf hvb hy
        rcases AM.ite_ok k2 with ⟨hc, k3⟩ | ⟨hc, k3⟩
        · obtain ⟨rfl, he⟩ := ih hok hm hm' hxE hyE k3
          refine ⟨rfl, ?_⟩
          simp only [Bool.and_eq_true] at hc
          obtain rfl := eq_of_beq hc.1
          rw [hxN] at hyN
          obtain rfl := Option.some.inj hyN
          simp only [ConLeche.canonExprEqFast, beq_self_eq_true, hc.2, Bool.and_self,
            Bool.true_and, he]
        · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
          refine ⟨rfl, ?_⟩
          have hbad : ((xN == yN) && (jA == jB)) = false := by
            cases hb : (xN == yN)
            · simp
            · cases hb2 : (jA == jB)
              · simp
              · exfalso
                have hyN' := hyN
                rw [← eq_of_beq hb] at hyN'
                exact hc (by simp [denoteN_inj hns hxN hyN', hb2])
          simp only [ConLeche.canonExprEqFast, hbad, Bool.false_and]

/-! ## The recursor rules

`canonRulesEq` compares each rule's OTHER fields by record equality at a
common `rhs` and its right-hand side by the term walk.  Over handles the
record equality is a HANDLE record equality, so the bridge needs the readback
to be injective at each field a rule carries — `denoteN_inj` at `ctor`,
`denoteLList_inj`/`denoteEList_inj` inside a `.nested` firing mode. -/

/-- con-leche: none — `Frontend.denoteEList` is injective; the list twin of
`Arena/WFProofs.lean`'s `denoteE_inj` (the level tier's `denoteLList_inj` is
already there). -/
theorem denoteEList_inj {st : EStore} (hwf : StoreWF st) :
    ∀ (is js : List EIdx) (xs : List Expr),
      Frontend.denoteEList st is = some xs →
      Frontend.denoteEList st js = some xs → is = js := by
  intro is
  induction is with
  | nil =>
    intro js xs hi hj
    simp only [Frontend.denoteEList, Option.some.injEq] at hi
    subst hi
    cases js with
    | nil => rfl
    | cons b bs =>
      simp only [Frontend.denoteEList] at hj
      cases hb : denoteE st b with
      | none => rw [hb] at hj; simp at hj
      | some y =>
        cases hbs : Frontend.denoteEList st bs with
        | none => rw [hb, hbs] at hj; simp at hj
        | some ys => rw [hb, hbs] at hj; simp at hj
  | cons a as ih =>
    intro js xs hi hj
    simp only [Frontend.denoteEList] at hi
    cases ha : denoteE st a with
    | none => rw [ha] at hi; simp at hi
    | some x =>
      cases has : Frontend.denoteEList st as with
      | none => rw [ha, has] at hi; simp at hi
      | some xt =>
        rw [ha, has] at hi
        simp only [Option.some.injEq] at hi
        subst hi
        cases js with
        | nil => simp only [Frontend.denoteEList] at hj; simp at hj
        | cons b bs =>
          simp only [Frontend.denoteEList] at hj
          cases hb : denoteE st b with
          | none => rw [hb] at hj; simp at hj
          | some y =>
            cases hbs : Frontend.denoteEList st bs with
            | none => rw [hb, hbs] at hj; simp at hj
            | some yt =>
              rw [hb, hbs] at hj
              simp only [Option.some.injEq, List.cons.injEq] at hj
              obtain ⟨rfl, rfl⟩ := hj
              rw [denoteE_inj hwf ha hb, ih bs _ has hbs]

/-- con-leche: none — `Frontend.denoteNList` is injective; `denoteEList_inj`'s
twin at the NAME store, off `Arena/WFProofs.lean`'s `denoteN_inj`.  The
`.projInfo` comparison (`denoteProjTable_inj`) needs it at `levelParams`. -/
theorem denoteNList_inj {st : EStore} (hwf : StoreWF st) :
    ∀ (as bs : List NIdx) (xs : List ConLeche.Name),
      Frontend.denoteNList st.ns as = some xs →
      Frontend.denoteNList st.ns bs = some xs → as = bs := by
  obtain ⟨rk, hrk⟩ := hwf
  intro as
  induction as with
  | nil =>
    intro bs xs ha hb
    simp only [Frontend.denoteNList, Option.some.injEq] at ha
    subst ha
    cases bs with
    | nil => rfl
    | cons b bt =>
      simp only [Frontend.denoteNList] at hb
      cases hbh : denoteN st.ns b with
      | none => rw [hbh] at hb; simp at hb
      | some y =>
        cases hbt : Frontend.denoteNList st.ns bt with
        | none => rw [hbh, hbt] at hb; simp at hb
        | some ys => rw [hbh, hbt] at hb; simp at hb
  | cons a at_ ih =>
    intro bs xs ha hb
    simp only [Frontend.denoteNList] at ha
    cases hah : denoteN st.ns a with
    | none => rw [hah] at ha; simp at ha
    | some x =>
      cases hat : Frontend.denoteNList st.ns at_ with
      | none => rw [hah, hat] at ha; simp at ha
      | some xt =>
        rw [hah, hat] at ha
        simp only [Option.some.injEq] at ha
        subst ha
        cases bs with
        | nil => simp only [Frontend.denoteNList] at hb; simp at hb
        | cons b bt =>
          simp only [Frontend.denoteNList] at hb
          cases hbh : denoteN st.ns b with
          | none => rw [hbh] at hb; simp at hb
          | some y =>
            cases hbt : Frontend.denoteNList st.ns bt with
            | none => rw [hbh, hbt] at hb; simp at hb
            | some yt =>
              rw [hbh, hbt] at hb
              simp only [Option.some.injEq, List.cons.injEq] at hb
              obtain ⟨rfl, rfl⟩ := hb
              rw [denoteN_inj hrk.nsWF hah hbh, ih bt _ hat hbt]

/-- con-leche: none — `Frontend.denoteEArray` is injective: it is
`denoteEList` on `toList`, and `Array.toList` is injective. -/
theorem denoteEArray_inj {st : EStore} (hwf : StoreWF st) {as bs : Array EIdx}
    {xs : Array Expr} (ha : Frontend.denoteEArray st as = some xs)
    (hb : Frontend.denoteEArray st bs = some xs) : as = bs := by
  simp only [Frontend.denoteEArray] at ha hb
  cases ha' : Frontend.denoteEList st as.toList with
  | none => rw [ha'] at ha; simp at ha
  | some xa =>
    cases hb' : Frontend.denoteEList st bs.toList with
    | none => rw [hb'] at hb; simp at hb
    | some xb =>
      rw [ha'] at ha
      rw [hb'] at hb
      simp only [Option.some.injEq] at ha hb
      have hxx : xa = xb := by
        have h2 : xa.toArray = xb.toArray := by rw [ha, hb]
        simpa using congrArg Array.toList h2
      subst hxx
      have hl := denoteEList_inj hwf _ _ _ ha' hb'
      simpa using congrArg List.toArray hl

/-- con-leche: none — **the stored projection table is determined by its
denotation, ONCE `IProjTableOK` holds on both sides** (task #97-P3-Checker
round 5; round 4's fourth `.projInfo` site).  `Frontend.denoteProjTable` drops
`tableName`, so without `named` two tables differing only there denote the
same `ProjTable` and this is FALSE; with it, `tableName` is pinned to
`projTableName` of the denoted `structName` and `denoteN_inj` recovers it.
Every other field is either carried verbatim or injective. -/
theorem denoteProjTable_inj {st : EStore} (hwf : StoreWF st) {t t' : IProjTable}
    {T : ProjTable} (hok : IProjTableOK st t) (hok' : IProjTableOK st t')
    (h : Frontend.denoteProjTable st t = some T)
    (h' : Frontend.denoteProjTable st t' = some T) : t = t' := by
  obtain ⟨rk, hrk⟩ := hwf
  obtain ⟨sn, hsn, htn⟩ := hok.named
  obtain ⟨sn', hsn', htn'⟩ := hok'.named
  simp only [Frontend.denoteProjTable] at h h'
  split at h
  · rename_i a b c hsA hlA hcA
    split at h
    · rename_i d e f hssA hbA hgA
      split at h'
      · rename_i a' b' c' hsB hlB hcB
        split at h'
        · rename_i d' e' f' hssB hbB hgB
          simp only [Option.some.injEq] at h h'
          have heq := h.trans h'.symm
          simp only [ProjTable.mk.injEq] at heq
          obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ := heq
          subst q1; subst q2; subst q4; subst q6; subst q7; subst q8
          have f1 : t.structName = t'.structName := denoteN_inj hrk.nsWF hsA hsB
          have f2 : t.levelParams = t'.levelParams :=
            denoteNList_inj ⟨rk, hrk⟩ _ _ _ hlA hlB
          have f4 : t.ctor = t'.ctor := denoteN_inj hrk.nsWF hcA hcB
          have f6 : t.structSort = t'.structSort := denoteL_inj hrk.lsWF hssA hssB
          have f7 : t.bodies = t'.bodies := denoteEArray_inj ⟨rk, hrk⟩ hbA hbB
          have f8 : t.guards = t'.guards := denoteLList_inj hrk.lsWF _ _ _ hgA hgB
          have hsnA : sn = a := Option.some.inj (hsn.symm.trans hsA)
          have hsnB : sn' = a := Option.some.inj (hsn'.symm.trans hsB)
          have hss : sn = sn' := hsnA.trans hsnB.symm
          subst hss
          have f3 : t.tableName = t'.tableName := denoteN_inj hrk.nsWF htn htn'
          cases t
          cases t'
          simp only [IProjTable.mk.injEq]
          exact ⟨f1, f3, f2, q3, f4, q5, f6, f7, f8, q9⟩
        · exact absurd h' (by simp)
      · exact absurd h' (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- con-leche: none — a rule's firing mode is determined by its denotation:
the two leaves carry nothing, and `.nested`'s two handle lists are injective
(`denoteLList_inj`, `denoteEList_inj`). -/
theorem denoteFire_inj {st : EStore} (hwf : StoreWF st) {f g : IRecRuleFire}
    {F : RecRuleFire} (hf : Frontend.denoteFire st f = some F)
    (hg : Frontend.denoteFire st g = some F) : f = g := by
  obtain ⟨rk, hrk⟩ := hwf
  have hnest : ∀ (lvls : List LIdx) (pins : List EIdx) (G : RecRuleFire),
      Frontend.denoteFire st (.nested lvls pins) = some G →
      ∃ ls es, denoteLList st.ls lvls = some ls ∧
        Frontend.denoteEList st pins = some es ∧ G = .nested ls es := by
    intro lvls pins G h
    simp only [Frontend.denoteFire] at h
    cases hl : denoteLList st.ls lvls with
    | none => rw [hl] at h; simp at h
    | some ls =>
      cases he : Frontend.denoteEList st pins with
      | none => rw [hl, he] at h; simp at h
      | some es =>
        rw [hl, he] at h
        exact ⟨ls, es, rfl, rfl, (Option.some.inj h).symm⟩
  cases f with
  | inert =>
    simp only [Frontend.denoteFire, Option.some.injEq] at hf
    subst hf
    cases g with
    | inert => rfl
    | plain => simp only [Frontend.denoteFire] at hg; simp at hg
    | nested l2 p2 =>
      obtain ⟨u1, u2, u3, u4, hG⟩ := hnest l2 p2 _ hg; simp at hG
  | plain =>
    simp only [Frontend.denoteFire, Option.some.injEq] at hf
    subst hf
    cases g with
    | inert => simp only [Frontend.denoteFire] at hg; simp at hg
    | plain => rfl
    | nested l2 p2 =>
      obtain ⟨u1, u2, u3, u4, hG⟩ := hnest l2 p2 _ hg; simp at hG
  | nested l1 p1 =>
    obtain ⟨ls1, es1, hl1, he1, rfl⟩ := hnest l1 p1 _ hf
    cases g with
    | inert => simp only [Frontend.denoteFire, Option.some.injEq] at hg; simp at hg
    | plain => simp only [Frontend.denoteFire, Option.some.injEq] at hg; simp at hg
    | nested l2 p2 =>
      obtain ⟨ls2, es2, hl2, he2, hG⟩ := hnest l2 p2 _ hg
      simp only [RecRuleFire.nested.injEq] at hG
      obtain ⟨rfl, rfl⟩ := hG
      rw [denoteLList_inj hrk.lsWF l1 l2 ls1 hl1 hl2,
        denoteEList_inj ⟨rk, hrk⟩ p1 p2 es1 he1 he2]

/-- con-leche: none — `Frontend.denoteRule`'s inversion, field by field. -/
theorem denoteRule_inv {st : EStore} {rl : IRecRule} {R : RecRule}
    (h : Frontend.denoteRule st rl = some R) :
    denoteN st.ns rl.ctor = some R.ctor ∧
      Frontend.denoteFire st rl.fire = some R.fire ∧
      denoteE st rl.rhs = some R.rhs ∧ rl.nfields = R.nfields ∧
      rl.ctorParams = R.ctorParams ∧ rl.k = R.k ∧ rl.eta = R.eta ∧
      rl.paramsBlind = R.paramsBlind := by
  simp only [Frontend.denoteRule] at h
  cases hc : denoteN st.ns rl.ctor with
  | none => rw [hc] at h; simp at h
  | some c =>
    cases hf : Frontend.denoteFire st rl.fire with
    | none => rw [hc, hf] at h; simp at h
    | some f =>
      cases hr : denoteE st rl.rhs with
      | none => rw [hc, hf, hr] at h; simp at h
      | some x =>
        rw [hc, hf, hr] at h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- con-leche: none — `Frontend.denoteRules`'s cons inversion. -/
theorem denoteRules_cons {st : EStore} {a : IRecRule} {as : List IRecRule}
    {zs : List RecRule} (h : Frontend.denoteRules st (a :: as) = some zs) :
    ∃ x xs, Frontend.denoteRule st a = some x ∧
      Frontend.denoteRules st as = some xs ∧ zs = x :: xs := by
  simp only [Frontend.denoteRules] at h
  cases hx : Frontend.denoteRule st a with
  | none => rw [hx] at h; simp at h
  | some x =>
    cases hxs : Frontend.denoteRules st as with
    | none => rw [hx, hxs] at h; simp at h
    | some xs =>
      rw [hx, hxs] at h
      simp only [Option.some.injEq] at h
      exact ⟨x, xs, rfl, rfl, h.symm⟩

/-- con-leche: ConLeche/Kernel/Canon.lean:224-231 canonRulesEqFast — **the
record comparison at a common `rhs` is the same test on both sides**: the `→`
half is `denoteRule`'s functionality and the `←` half is the readback's
injectivity at `ctor` and `fire`, the rule's only two handle fields. -/
theorem canonRuleHead_eq {st : EStore} (hwf : StoreWF st) {r r' : IRecRule}
    {R R' : RecRule} (hr : Frontend.denoteRule st r = some R)
    (hr' : Frontend.denoteRule st r' = some R') :
    (({ r with rhs := default } : IRecRule) == { r' with rhs := default })
      = ((({ R with rhs := .bvar 0 } : RecRule)) == { R' with rhs := .bvar 0 }) := by
  obtain ⟨rk, hrk⟩ := hwf
  obtain ⟨hc, hf, -, hn, hp, hk, he, hb⟩ := denoteRule_inv hr
  obtain ⟨hc', hf', -, hn', hp', hk', he', hb'⟩ := denoteRule_inv hr'
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  obtain ⟨c1, n1, p1, f1, x1, k1, e1, b1⟩ := r
  obtain ⟨c2, n2, p2, f2, x2, k2, e2, b2⟩ := r'
  obtain ⟨C1, N1, P1, F1, X1, K1, E1, B1⟩ := R
  obtain ⟨C2, N2, P2, F2, X2, K2, E2, B2⟩ := R'
  simp only at hc hf hn hp hk he hb hc' hf' hn' hp' hk' he' hb'
  subst hn; subst hp; subst hk; subst he; subst hb
  subst hn'; subst hp'; subst hk'; subst he'; subst hb'
  constructor
  · intro h
    have q1 : c1 = c2 := congrArg IRecRule.ctor h
    have q2 : n1 = n2 := congrArg IRecRule.nfields h
    have q3 : p1 = p2 := congrArg IRecRule.ctorParams h
    have q4 : f1 = f2 := congrArg IRecRule.fire h
    have q5 : k1 = k2 := congrArg IRecRule.k h
    have q6 : e1 = e2 := congrArg IRecRule.eta h
    have q7 : b1 = b2 := congrArg IRecRule.paramsBlind h
    subst q1; subst q2; subst q3; subst q4; subst q5; subst q6; subst q7
    rw [hc] at hc'
    rw [hf] at hf'
    obtain rfl := Option.some.inj hc'
    obtain rfl := Option.some.inj hf'
    rfl
  · intro h
    have q1 : C1 = C2 := congrArg RecRule.ctor h
    have q2 : n1 = n2 := congrArg RecRule.nfields h
    have q3 : p1 = p2 := congrArg RecRule.ctorParams h
    have q4 : F1 = F2 := congrArg RecRule.fire h
    have q5 : k1 = k2 := congrArg RecRule.k h
    have q6 : e1 = e2 := congrArg RecRule.eta h
    have q7 : b1 = b2 := congrArg RecRule.paramsBlind h
    subst q1; subst q2; subst q3; subst q4; subst q5; subst q6; subst q7
    obtain rfl := denoteN_inj hrk.nsWF hc hc'
    obtain rfl := denoteFire_inj ⟨rk, hrk⟩ hf hf'
    rfl

/-- con-leche: ConLeche/Kernel/Canon.lean:224-231 canonRulesEqFast — the rule
list, in lockstep. -/
theorem canonRulesEq_run {ps ps' cs : List NIdx}
    {psN ps'N : List ConLeche.Name} (fuel : Nat) :
    ∀ (rs rs' : List IRecRule) {Rs Rs' : List RecRule} {r : Bool}
      {s s' : AState}, StateOK s → CanonMapD s.store.ns ps cs psN →
      CanonMapD s.store.ns ps' cs ps'N →
      Frontend.denoteRules s.store rs = some Rs →
      Frontend.denoteRules s.store rs' = some Rs' →
      canonRulesEq ps ps' cs fuel rs rs' s = .ok (r, s') →
      s' = s ∧ r = ConLeche.canonRulesEqFast (ConLeche.canonNameMap psN)
        (ConLeche.canonNameMap ps'N) Rs Rs' := by
  intro rs
  induction rs with
  | nil =>
    intro rs' Rs Rs' r s s' hok hm hm' hrs hrs' hrun
    simp only [Frontend.denoteRules, Option.some.injEq] at hrs
    subst hrs
    cases rs' with
    | nil =>
      simp only [Frontend.denoteRules, Option.some.injEq] at hrs'
      subst hrs'
      simp only [Arena.canonRulesEq] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨rfl, by simp [ConLeche.canonRulesEqFast]⟩
    | cons b bs =>
      obtain ⟨y, ys, -, -, rfl⟩ := denoteRules_cons hrs'
      simp only [Arena.canonRulesEq] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨rfl, by simp [ConLeche.canonRulesEqFast]⟩
  | cons a as ih =>
    intro rs' Rs Rs' r s s' hok hm hm' hrs hrs' hrun
    obtain ⟨X, Xs, hX, hXs, rfl⟩ := denoteRules_cons hrs
    cases rs' with
    | nil =>
      simp only [Frontend.denoteRules, Option.some.injEq] at hrs'
      subst hrs'
      simp only [Arena.canonRulesEq] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨rfl, by simp [ConLeche.canonRulesEqFast]⟩
    | cons b bs =>
      obtain ⟨Y, Ys, hY, hYs, rfl⟩ := denoteRules_cons hrs'
      have hhead := canonRuleHead_eq hok.wf hX hY
      obtain ⟨-, -, hXr, -⟩ := denoteRule_inv hX
      obtain ⟨-, -, hYr, -⟩ := denoteRule_inv hY
      simp only [Arena.canonRulesEq] at hrun
      rcases AM.ite_ok hrun with ⟨hc0, k1⟩ | ⟨hc0, k1⟩
      · obtain ⟨c1, s1, g1, k2⟩ := AM.bind_ok k1
        obtain ⟨rfl, he1⟩ := canonExprEq_run fuel hok hm hm' hXr hYr g1
        rcases AM.ite_ok k2 with ⟨hc, k3⟩ | ⟨hc, k3⟩
        · obtain ⟨rfl, he2⟩ := ih bs hok hm hm' hXs hYs k3
          refine ⟨rfl, ?_⟩
          have h1 := he1 ▸ hc
          simp only [ConLeche.canonRulesEqFast, ← hhead, hc0, h1, Bool.and_self,
            Bool.true_and, he2]
        · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
          refine ⟨rfl, ?_⟩
          have h1 : ConLeche.canonExprEqFast (ConLeche.canonNameMap psN)
              (ConLeche.canonNameMap ps'N) X.rhs Y.rhs = false := by
            cases hb : ConLeche.canonExprEqFast (ConLeche.canonNameMap psN)
                (ConLeche.canonNameMap ps'N) X.rhs Y.rhs
            · rfl
            · exact absurd (he1.trans hb) hc
          simp only [ConLeche.canonRulesEqFast, ← hhead, hc0, h1, Bool.and_false,
            Bool.false_and]
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k1
        refine ⟨rfl, ?_⟩
        have h0 : (({ X with rhs := .bvar 0 } : RecRule)
            == { Y with rhs := .bvar 0 }) = false := by
          rw [← hhead]
          simpa using hc0
        simp only [ConLeche.canonRulesEqFast, h0, Bool.false_and]

/-! ## The constants -/

/-- con-leche: ConLeche/Kernel/Canon.lean:75-80 ConstantVal.canon
con-leche: ConLeche/Kernel/Canon.lean:201-206 ConstantVal.canonEqFast
**the header comparison**: the name test is `denoteN`'s injectivity, the
length test is the readback's length preservation, and the type comparison is
`canonExprEq_run` at the numerals `canonNames` just interned. -/
theorem IConstantVal.canonEq_run {cv cv' : IConstantVal} {c c' : ConstantVal}
    {r : Bool} {s s' : AState} (hok : StateOK s)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hcv' : Frontend.denoteCV s.store cv' = some c')
    (hrun : IConstantVal.canonEq cv cv' s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.ConstantVal.canonEq c c' := by
  obtain ⟨rk, hrk⟩ := hok.wf
  have hns : NStoreWF s.store.ns := hrk.nsWF
  obtain ⟨hn, hlps, hty⟩ := denoteCV_inv hcv
  obtain ⟨hn', hlps', hty'⟩ := denoteCV_inv hcv'
  have hlenA : cv.levelParams.length = c.levelParams.length :=
    denoteNList_length _ _ hlps
  have hlenB : cv'.levelParams.length = c'.levelParams.length :=
    denoteNList_length _ _ hlps'
  have hnameEq : (cv.name == cv'.name) = (c.name == c'.name) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    constructor
    · intro h; rw [h, hn'] at hn; exact (Option.some.inj hn).symm
    · intro h; exact denoteN_inj hns hn (by rw [h]; exact hn')
  simp only [Arena.IConstantVal.canonEq] at hrun
  rw [ConLeche.ConstantVal.canonEq_eq_canonEqFast]
  rcases AM.ite_ok hrun with ⟨hc0, k1⟩ | ⟨hc0, k1⟩
  · obtain ⟨cs, s1, g1, k2⟩ := AM.bind_ok k1
    obtain ⟨hok1, hx1, hca1, hp1, hcsd⟩ := canonNames_run hok g1
    simp only [Bool.and_eq_true, beq_iff_eq] at hc0
    have hcslen : cs.length = cv.levelParams.length := by
      have := denoteNList_length _ _ hcsd
      simpa using this
    have hnums : Frontend.denoteNList s1.store.ns cs
        = some ((List.range cs.length).map
            (fun i => ConLeche.Name.num .anonymous i)) := by rw [hcslen]; exact hcsd
    have hmA : CanonMapD s1.store.ns cv.levelParams cs c.levelParams :=
      { params := denoteNListE_ext hx1 _ _ hlps
        nums := hnums
        len := hcslen.symm }
    have hmB : CanonMapD s1.store.ns cv'.levelParams cs c'.levelParams :=
      { params := denoteNListE_ext hx1 _ _ hlps'
        nums := hnums
        len := by rw [hcslen, hc0.2] }
    obtain ⟨rfl, he⟩ := canonExprEq_run coreWalkFuel hok1 hmA hmB
      (denote_ext hty hx1) (denote_ext hty' hx1) k2
    refine ⟨hok1, hx1, hca1, hp1, ?_⟩
    rw [he]
    have h1 : (c.name == c'.name) = true := by rw [← hnameEq, hc0.1]; simp
    have h2 : (c.levelParams.length == c'.levelParams.length) = true := by
      rw [← hlenA, ← hlenB, hc0.2]; simp
    simp only [ConLeche.ConstantVal.canonEqFast, h1, h2, Bool.and_self,
      Bool.true_and]
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k1
    refine ⟨hok, Ext.refl _, rfl, rfl, ?_⟩
    have hbad : ((c.name == c'.name) &&
        (c.levelParams.length == c'.levelParams.length)) = false := by
      rw [← hnameEq, ← hlenA, ← hlenB]
      simpa using hc0
    simp only [ConLeche.ConstantVal.canonEqFast, hbad, Bool.false_and]

/-! ### `Frontend.denoteCI`, inverted at each constructor -/

theorem denoteCI_axiom_inv {st : EStore} {v : IConstantVal} {c : ConstantInfo}
    (h : Frontend.denoteCI st (.axiomInfo v) = some c) :
    ∃ cv, c = .axiomInfo cv ∧ Frontend.denoteCV st v = some cv := by
  simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
  obtain ⟨cv, hcv, rfl⟩ := h; exact ⟨cv, rfl, hcv⟩

theorem denoteCI_ctor_inv {st : EStore} {v : IConstantVal} {nP nF : Nat}
    {c : ConstantInfo} (h : Frontend.denoteCI st (.ctorInfo v nP nF) = some c) :
    ∃ cv, c = .ctorInfo cv nP nF ∧ Frontend.denoteCV st v = some cv := by
  simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
  obtain ⟨cv, hcv, rfl⟩ := h; exact ⟨cv, rfl, hcv⟩

theorem denoteCI_proj_inv {st : EStore} {t : IProjTable} {c : ConstantInfo}
    (h : Frontend.denoteCI st (.projInfo t) = some c) :
    ∃ T, c = .projInfo T ∧ Frontend.denoteProjTable st t = some T := by
  simp only [Frontend.denoteCI, Option.map_eq_some_iff] at h
  obtain ⟨T, hT, rfl⟩ := h; exact ⟨T, rfl, hT⟩

theorem denoteCI_defn_inv {st : EStore} {v : IConstantVal} {e : EIdx}
    {hint : ReducibilityHint} {c : ConstantInfo}
    (h : Frontend.denoteCI st (.defnInfo v e hint) = some c) :
    ∃ cv x, c = .defnInfo cv x hint ∧ Frontend.denoteCV st v = some cv ∧
      denoteE st e = some x := by
  simp only [Frontend.denoteCI] at h
  cases hcv : Frontend.denoteCV st v with
  | none => rw [hcv] at h; simp at h
  | some cv =>
    cases he : denoteE st e with
    | none => rw [hcv, he] at h; simp at h
    | some x => rw [hcv, he] at h; exact ⟨cv, x, (Option.some.inj h).symm, rfl, rfl⟩

theorem denoteCI_thm_inv {st : EStore} {v : IConstantVal} {e : EIdx}
    {c : ConstantInfo} (h : Frontend.denoteCI st (.thmInfo v e) = some c) :
    ∃ cv x, c = .thmInfo cv x ∧ Frontend.denoteCV st v = some cv ∧
      denoteE st e = some x := by
  simp only [Frontend.denoteCI] at h
  cases hcv : Frontend.denoteCV st v with
  | none => rw [hcv] at h; simp at h
  | some cv =>
    cases he : denoteE st e with
    | none => rw [hcv, he] at h; simp at h
    | some x => rw [hcv, he] at h; exact ⟨cv, x, (Option.some.inj h).symm, rfl, rfl⟩

theorem denoteCI_ind_inv {st : EStore} {v : IConstantVal} {cap : IIndCaps}
    {c : ConstantInfo} (h : Frontend.denoteCI st (.indInfo v cap) = some c) :
    ∃ cv d, c = .indInfo cv d ∧ Frontend.denoteCV st v = some cv ∧
      Frontend.denoteCaps st cap = some d := by
  simp only [Frontend.denoteCI] at h
  cases hcv : Frontend.denoteCV st v with
  | none => rw [hcv] at h; simp at h
  | some cv =>
    cases hd : Frontend.denoteCaps st cap with
    | none => rw [hcv, hd] at h; simp at h
    | some d => rw [hcv, hd] at h; exact ⟨cv, d, (Option.some.inj h).symm, rfl, rfl⟩

theorem denoteCI_rec_inv {st : EStore} {v : IConstantVal} {mI rP : Nat}
    {rs : List IRecRule} {c : ConstantInfo}
    (h : Frontend.denoteCI st (.recInfo v mI rP rs) = some c) :
    ∃ cv Rs, c = .recInfo cv mI rP Rs ∧ Frontend.denoteCV st v = some cv ∧
      Frontend.denoteRules st rs = some Rs := by
  simp only [Frontend.denoteCI] at h
  cases hcv : Frontend.denoteCV st v with
  | none => rw [hcv] at h; simp at h
  | some cv =>
    cases hr : Frontend.denoteRules st rs with
    | none => rw [hcv, hr] at h; simp at h
    | some Rs => rw [hcv, hr] at h; exact ⟨cv, Rs, (Option.some.inj h).symm, rfl, rfl⟩

/-- con-leche: ConLeche/Kernel/Canon.lean:250-252 ConstantInfo.canonEq
con-leche: ConLeche/Kernel/Canon.lean:254-273 ConstantInfo.canonEqFast
**the pinned-block comparison**, at a whole stored constant.  This is what
`checkDecl`'s `.axiomDecl` arm runs on `Quot.sound` and what `basisPinHit`
runs on a block's members.

Forty-nine arms, forty-two of them the constructor mismatch.  Six of the seven
diagonal arms are `IConstantVal.canonEq_run` plus (where the constructor
carries one) `canonExprEq_run` or `canonRulesEq_run` at a freshly interned
numeral list.

**PROVED** (task #97-P3-Checker round 5), on the `hproj` hypothesis round 4
asked the coordinator for.  Round 4 left the `.projInfo`/`.projInfo` arm
`sorry` because it is FALSE without one: the arena compares two `IProjTable`s
by record equality and `Frontend.denoteProjTable` **drops `tableName`**, so
two tables that differ only there denote the same `ProjTable` and the twin
answers `false` where con-leche answers `true`.

`hproj` is the repair, and it is the SAME hypothesis `denoteCI_name_of`
(`Bridge/StateOK.lean`) and `IFEnvOK_of_denote` (`Bridge/Checker/Inv.lean`)
take at the same gap — the fourth of round 4's four named `.projInfo` sites.
It is stated at the WEAKEST shape the proof needs: both sides at once, so its
premise is unreachable unless BOTH constants are projection tables.  That
makes it free at every call site where either side has a known constructor —
`Bridge/Checker/Arms.lean`'s `.axiomDecl` arm discharges it with `nofun` on
the left premise alone — and it is discharged in general by
`IFEnvOK.proj` / `projTableOK_of_install`, since the install is the only place
a `.projInfo` row is made.

With it the arm is `denoteProjTable_inj`: `named` pins `tableName` to
`projTableName` of the denoted `structName` and every other field is injective
(`denoteN_inj`, `denoteNList_inj`, `denoteL_inj`, `denoteLList_inj`,
`denoteEArray_inj`), so record equality on the two handles IS record equality
on the two denotations. -/
theorem IConstantInfo.canonEq_run {ci ci' : IConstantInfo} {c c' : ConstantInfo}
    {r : Bool} {s s' : AState} (hok : StateOK s)
    (hproj : ∀ t t', ci = .projInfo t → ci' = .projInfo t' →
      IProjTableOK s.store t ∧ IProjTableOK s.store t')
    (hci : Frontend.denoteCI s.store ci = some c)
    (hci' : Frontend.denoteCI s.store ci' = some c')
    (hrun : IConstantInfo.canonEq ci ci' s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.ConstantInfo.canonEq c c' := by
  simp only [Arena.IConstantInfo.canonEq] at hrun
  cases ci with
  | axiomInfo vA =>
    obtain ⟨xV, rfl, hxV⟩ := denoteCI_axiom_inv hci
    cases ci' with
    | axiomInfo vB =>
      obtain ⟨yV, rfl, hyV⟩ := denoteCI_axiom_inv hci'
      obtain ⟨hok1, hx1, hca1, hp1, he⟩ :=
        IConstantVal.canonEq_run hok hxV hyV hrun
      refine ⟨hok1, hx1, hca1, hp1, ?_⟩
      rw [he, ConLeche.ConstantInfo.canonEq_eq_canonEqFast,
        ConLeche.ConstantVal.canonEq_eq_canonEqFast]
      rfl
    | defnInfo vB eB hB =>
      obtain ⟨yV, yE, rfl, hyV, hyE⟩ := denoteCI_defn_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | thmInfo vB eB =>
      obtain ⟨yV, yE, rfl, hyV, hyE⟩ := denoteCI_thm_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | indInfo vB capB =>
      obtain ⟨yV, yC, rfl, hyV, hyC⟩ := denoteCI_ind_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | ctorInfo vB nPB nFB =>
      obtain ⟨yV, rfl, hyV⟩ := denoteCI_ctor_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | recInfo vB mIB rPB rsB =>
      obtain ⟨yV, yR, rfl, hyV, hyR⟩ := denoteCI_rec_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | projInfo tB =>
      obtain ⟨yT, rfl, hyT⟩ := denoteCI_proj_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
  | defnInfo vA eA hA =>
    obtain ⟨xV, xE, rfl, hxV, hxE⟩ := denoteCI_defn_inv hci
    cases ci' with
    | axiomInfo vB =>
      obtain ⟨yV, rfl, hyV⟩ := denoteCI_axiom_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | defnInfo vB eB hB =>
      obtain ⟨yV, yE, rfl, hyV, hyE⟩ := denoteCI_defn_inv hci'
      obtain ⟨b1, s1, g1, k1⟩ := AM.bind_ok hrun
      obtain ⟨hok1, hx1, hca1, hp1, he1⟩ := IConstantVal.canonEq_run hok hxV hyV g1
      rw [ConLeche.ConstantVal.canonEq_eq_canonEqFast] at he1
      rcases AM.ite_ok k1 with ⟨hc1, k2⟩ | ⟨hc1, k2⟩
      · rcases AM.ite_ok k2 with ⟨hch, k3⟩ | ⟨hch, k3⟩
        · obtain ⟨cs, s2, g2, k9⟩ := AM.bind_ok k3
          obtain ⟨hok2, hx2, hca2, hp2, hcsd⟩ := canonNames_run hok1 g2
          obtain ⟨-, hlpsA, -⟩ := denoteCV_inv hxV
          obtain ⟨-, hlpsB, -⟩ := denoteCV_inv hyV
          have hcv1 : ConLeche.ConstantVal.canon xV = ConLeche.ConstantVal.canon yV :=
            (ConLeche.ConstantVal.canonEqFast_iff xV yV).mp (he1 ▸ hc1)
          have hlenAB : xV.levelParams.length = yV.levelParams.length := by
            have hq := congrArg (fun z => (ConLeche.ConstantVal.levelParams z).length) hcv1
            simpa [ConLeche.ConstantVal.canon] using hq
          have hlenA : vA.levelParams.length = xV.levelParams.length :=
            denoteNList_length _ _ hlpsA
          have hlenB : vB.levelParams.length = yV.levelParams.length :=
            denoteNList_length _ _ hlpsB
          have hcslen : cs.length = vA.levelParams.length := by
            have hq := denoteNList_length _ _ hcsd
            simpa using hq
          have hnums : Frontend.denoteNList s2.store.ns cs
              = some ((List.range cs.length).map
                  (fun i => ConLeche.Name.num .anonymous i)) := by rw [hcslen]; exact hcsd
          have hmA : CanonMapD s2.store.ns vA.levelParams cs xV.levelParams :=
            { params := denoteNListE_ext hx2 _ _ (denoteNListE_ext hx1 _ _ hlpsA)
              nums := hnums
              len := hcslen.symm }
          have hmB : CanonMapD s2.store.ns vB.levelParams cs yV.levelParams :=
            { params := denoteNListE_ext hx2 _ _ (denoteNListE_ext hx1 _ _ hlpsB)
              nums := hnums
              len := by omega }
          obtain ⟨rfl, he2⟩ := canonExprEq_run coreWalkFuel hok2 hmA hmB
            (denote_ext (denote_ext hxE hx1) hx2)
            (denote_ext (denote_ext hyE hx1) hx2) k9
          refine ⟨hok2, hx1.trans hx2, by rw [hca2, hca1], by rw [hp2, hp1], ?_⟩
          rw [he2, ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
          simp only [ConLeche.ConstantInfo.canonEqFast, ← he1, hc1, hch,
            Bool.true_and, Bool.and_true]
        · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
          refine ⟨hok1, hx1, hca1, hp1, ?_⟩
          rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
          have hbad : (hA == hB) = false := by simpa using hch
          simp only [ConLeche.ConstantInfo.canonEqFast, hbad, Bool.and_false]
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        refine ⟨hok1, hx1, hca1, hp1, ?_⟩
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        have hbad : ConLeche.ConstantVal.canonEqFast xV yV = false := by
          rw [← he1]; simpa using hc1
        simp only [ConLeche.ConstantInfo.canonEqFast, hbad, Bool.false_and]
    | thmInfo vB eB =>
      obtain ⟨yV, yE, rfl, hyV, hyE⟩ := denoteCI_thm_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | indInfo vB capB =>
      obtain ⟨yV, yC, rfl, hyV, hyC⟩ := denoteCI_ind_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | ctorInfo vB nPB nFB =>
      obtain ⟨yV, rfl, hyV⟩ := denoteCI_ctor_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | recInfo vB mIB rPB rsB =>
      obtain ⟨yV, yR, rfl, hyV, hyR⟩ := denoteCI_rec_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | projInfo tB =>
      obtain ⟨yT, rfl, hyT⟩ := denoteCI_proj_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
  | thmInfo vA eA =>
    obtain ⟨xV, xE, rfl, hxV, hxE⟩ := denoteCI_thm_inv hci
    cases ci' with
    | axiomInfo vB =>
      obtain ⟨yV, rfl, hyV⟩ := denoteCI_axiom_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | defnInfo vB eB hB =>
      obtain ⟨yV, yE, rfl, hyV, hyE⟩ := denoteCI_defn_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | thmInfo vB eB =>
      obtain ⟨yV, yE, rfl, hyV, hyE⟩ := denoteCI_thm_inv hci'
      obtain ⟨b1, s1, g1, k1⟩ := AM.bind_ok hrun
      obtain ⟨hok1, hx1, hca1, hp1, he1⟩ := IConstantVal.canonEq_run hok hxV hyV g1
      rw [ConLeche.ConstantVal.canonEq_eq_canonEqFast] at he1
      rcases AM.ite_ok k1 with ⟨hc1, k2⟩ | ⟨hc1, k2⟩
      · obtain ⟨cs, s2, g2, k9⟩ := AM.bind_ok k2
        obtain ⟨hok2, hx2, hca2, hp2, hcsd⟩ := canonNames_run hok1 g2
        obtain ⟨-, hlpsA, -⟩ := denoteCV_inv hxV
        obtain ⟨-, hlpsB, -⟩ := denoteCV_inv hyV
        have hcv1 : ConLeche.ConstantVal.canon xV = ConLeche.ConstantVal.canon yV :=
          (ConLeche.ConstantVal.canonEqFast_iff xV yV).mp (he1 ▸ hc1)
        have hlenAB : xV.levelParams.length = yV.levelParams.length := by
          have hq := congrArg (fun z => (ConLeche.ConstantVal.levelParams z).length) hcv1
          simpa [ConLeche.ConstantVal.canon] using hq
        have hlenA : vA.levelParams.length = xV.levelParams.length :=
          denoteNList_length _ _ hlpsA
        have hlenB : vB.levelParams.length = yV.levelParams.length :=
          denoteNList_length _ _ hlpsB
        have hcslen : cs.length = vA.levelParams.length := by
          have hq := denoteNList_length _ _ hcsd
          simpa using hq
        have hnums : Frontend.denoteNList s2.store.ns cs
            = some ((List.range cs.length).map
                (fun i => ConLeche.Name.num .anonymous i)) := by rw [hcslen]; exact hcsd
        have hmA : CanonMapD s2.store.ns vA.levelParams cs xV.levelParams :=
          { params := denoteNListE_ext hx2 _ _ (denoteNListE_ext hx1 _ _ hlpsA)
            nums := hnums
            len := hcslen.symm }
        have hmB : CanonMapD s2.store.ns vB.levelParams cs yV.levelParams :=
          { params := denoteNListE_ext hx2 _ _ (denoteNListE_ext hx1 _ _ hlpsB)
            nums := hnums
            len := by omega }
        obtain ⟨rfl, he2⟩ := canonExprEq_run coreWalkFuel hok2 hmA hmB
          (denote_ext (denote_ext hxE hx1) hx2)
          (denote_ext (denote_ext hyE hx1) hx2) k9
        refine ⟨hok2, hx1.trans hx2, by rw [hca2, hca1], by rw [hp2, hp1], ?_⟩
        rw [he2, ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp only [ConLeche.ConstantInfo.canonEqFast, ← he1, hc1, Bool.true_and]
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
        refine ⟨hok1, hx1, hca1, hp1, ?_⟩
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        have hbad : ConLeche.ConstantVal.canonEqFast xV yV = false := by
          rw [← he1]; simpa using hc1
        simp only [ConLeche.ConstantInfo.canonEqFast, hbad, Bool.false_and]
    | indInfo vB capB =>
      obtain ⟨yV, yC, rfl, hyV, hyC⟩ := denoteCI_ind_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | ctorInfo vB nPB nFB =>
      obtain ⟨yV, rfl, hyV⟩ := denoteCI_ctor_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | recInfo vB mIB rPB rsB =>
      obtain ⟨yV, yR, rfl, hyV, hyR⟩ := denoteCI_rec_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | projInfo tB =>
      obtain ⟨yT, rfl, hyT⟩ := denoteCI_proj_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
  | indInfo vA capA =>
    obtain ⟨xV, xC, rfl, hxV, hxC⟩ := denoteCI_ind_inv hci
    cases ci' with
    | axiomInfo vB =>
      obtain ⟨yV, rfl, hyV⟩ := denoteCI_axiom_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | defnInfo vB eB hB =>
      obtain ⟨yV, yE, rfl, hyV, hyE⟩ := denoteCI_defn_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | thmInfo vB eB =>
      obtain ⟨yV, yE, rfl, hyV, hyE⟩ := denoteCI_thm_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | indInfo vB capB =>
      obtain ⟨yV, yC, rfl, hyV, hyC⟩ := denoteCI_ind_inv hci'
      obtain ⟨hok1, hx1, hca1, hp1, he⟩ :=
        IConstantVal.canonEq_run hok hxV hyV hrun
      refine ⟨hok1, hx1, hca1, hp1, ?_⟩
      rw [he, ConLeche.ConstantInfo.canonEq_eq_canonEqFast,
        ConLeche.ConstantVal.canonEq_eq_canonEqFast]
      rfl
    | ctorInfo vB nPB nFB =>
      obtain ⟨yV, rfl, hyV⟩ := denoteCI_ctor_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | recInfo vB mIB rPB rsB =>
      obtain ⟨yV, yR, rfl, hyV, hyR⟩ := denoteCI_rec_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | projInfo tB =>
      obtain ⟨yT, rfl, hyT⟩ := denoteCI_proj_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
  | ctorInfo vA nPA nFA =>
    obtain ⟨xV, rfl, hxV⟩ := denoteCI_ctor_inv hci
    cases ci' with
    | axiomInfo vB =>
      obtain ⟨yV, rfl, hyV⟩ := denoteCI_axiom_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | defnInfo vB eB hB =>
      obtain ⟨yV, yE, rfl, hyV, hyE⟩ := denoteCI_defn_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | thmInfo vB eB =>
      obtain ⟨yV, yE, rfl, hyV, hyE⟩ := denoteCI_thm_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | indInfo vB capB =>
      obtain ⟨yV, yC, rfl, hyV, hyC⟩ := denoteCI_ind_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | ctorInfo vB nPB nFB =>
      obtain ⟨yV, rfl, hyV⟩ := denoteCI_ctor_inv hci'
      rcases AM.ite_ok hrun with ⟨hc0, k1⟩ | ⟨hc0, k1⟩
      · obtain ⟨hok1, hx1, hca1, hp1, he⟩ := IConstantVal.canonEq_run hok hxV hyV k1
        refine ⟨hok1, hx1, hca1, hp1, ?_⟩
        rw [he, ConLeche.ConstantInfo.canonEq_eq_canonEqFast,
          ConLeche.ConstantVal.canonEq_eq_canonEqFast]
        simp only [Bool.and_eq_true] at hc0
        simp only [ConLeche.ConstantInfo.canonEqFast, hc0.1, hc0.2, Bool.and_true]
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k1
        refine ⟨hok, Ext.refl _, rfl, rfl, ?_⟩
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        have hbad : ((nPA == nPB) && (nFA == nFB)) = false := by simpa using hc0
        simp only [ConLeche.ConstantInfo.canonEqFast]
        rw [Bool.and_assoc, hbad, Bool.and_false]
    | recInfo vB mIB rPB rsB =>
      obtain ⟨yV, yR, rfl, hyV, hyR⟩ := denoteCI_rec_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | projInfo tB =>
      obtain ⟨yT, rfl, hyT⟩ := denoteCI_proj_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
  | recInfo vA mIA rPA rsA =>
    obtain ⟨xV, xR, rfl, hxV, hxR⟩ := denoteCI_rec_inv hci
    cases ci' with
    | axiomInfo vB =>
      obtain ⟨yV, rfl, hyV⟩ := denoteCI_axiom_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | defnInfo vB eB hB =>
      obtain ⟨yV, yE, rfl, hyV, hyE⟩ := denoteCI_defn_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | thmInfo vB eB =>
      obtain ⟨yV, yE, rfl, hyV, hyE⟩ := denoteCI_thm_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | indInfo vB capB =>
      obtain ⟨yV, yC, rfl, hyV, hyC⟩ := denoteCI_ind_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | ctorInfo vB nPB nFB =>
      obtain ⟨yV, rfl, hyV⟩ := denoteCI_ctor_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | recInfo vB mIB rPB rsB =>
      obtain ⟨yV, yR, rfl, hyV, hyR⟩ := denoteCI_rec_inv hci'
      rcases AM.ite_ok hrun with ⟨hc0, kk⟩ | ⟨hc0, kk⟩
      · obtain ⟨b1, s1, g1, k1⟩ := AM.bind_ok kk
        obtain ⟨hok1, hx1, hca1, hp1, he1⟩ := IConstantVal.canonEq_run hok hxV hyV g1
        rw [ConLeche.ConstantVal.canonEq_eq_canonEqFast] at he1
        simp only [Bool.and_eq_true] at hc0
        rcases AM.ite_ok k1 with ⟨hc1, k2⟩ | ⟨hc1, k2⟩
        · obtain ⟨cs, s2, g2, k9⟩ := AM.bind_ok k2
          obtain ⟨hok2, hx2, hca2, hp2, hcsd⟩ := canonNames_run hok1 g2
          obtain ⟨-, hlpsA, -⟩ := denoteCV_inv hxV
          obtain ⟨-, hlpsB, -⟩ := denoteCV_inv hyV
          have hcv1 : ConLeche.ConstantVal.canon xV = ConLeche.ConstantVal.canon yV :=
            (ConLeche.ConstantVal.canonEqFast_iff xV yV).mp (he1 ▸ hc1)
          have hlenAB : xV.levelParams.length = yV.levelParams.length := by
            have hq := congrArg (fun z => (ConLeche.ConstantVal.levelParams z).length) hcv1
            simpa [ConLeche.ConstantVal.canon] using hq
          have hlenA : vA.levelParams.length = xV.levelParams.length :=
            denoteNList_length _ _ hlpsA
          have hlenB : vB.levelParams.length = yV.levelParams.length :=
            denoteNList_length _ _ hlpsB
          have hcslen : cs.length = vA.levelParams.length := by
            have hq := denoteNList_length _ _ hcsd
            simpa using hq
          have hnums : Frontend.denoteNList s2.store.ns cs
              = some ((List.range cs.length).map
                  (fun i => ConLeche.Name.num .anonymous i)) := by rw [hcslen]; exact hcsd
          have hmA : CanonMapD s2.store.ns vA.levelParams cs xV.levelParams :=
            { params := denoteNListE_ext hx2 _ _ (denoteNListE_ext hx1 _ _ hlpsA)
              nums := hnums
              len := hcslen.symm }
          have hmB : CanonMapD s2.store.ns vB.levelParams cs yV.levelParams :=
            { params := denoteNListE_ext hx2 _ _ (denoteNListE_ext hx1 _ _ hlpsB)
              nums := hnums
              len := by omega }
          obtain ⟨rfl, he2⟩ := canonRulesEq_run coreWalkFuel rsA rsB hok2 hmA hmB
            (denoteRules_ext hx2 _ _ (denoteRules_ext hx1 _ _ hxR))
            (denoteRules_ext hx2 _ _ (denoteRules_ext hx1 _ _ hyR)) k9
          refine ⟨hok2, hx1.trans hx2, by rw [hca2, hca1], by rw [hp2, hp1], ?_⟩
          rw [he2, ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
          simp only [ConLeche.ConstantInfo.canonEqFast, ← he1, hc1, hc0.1, hc0.2,
            Bool.true_and, Bool.and_self]
        · obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
          refine ⟨hok1, hx1, hca1, hp1, ?_⟩
          rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
          have hbad : ConLeche.ConstantVal.canonEqFast xV yV = false := by
            rw [← he1]; simpa using hc1
          simp only [ConLeche.ConstantInfo.canonEqFast, hbad, Bool.false_and]
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok kk
        refine ⟨hok, Ext.refl _, rfl, rfl, ?_⟩
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        have hbad : ((mIA == mIB) && (rPA == rPB)) = false := by simpa using hc0
        simp only [ConLeche.ConstantInfo.canonEqFast]
        cases hm : (mIA == mIB) <;> cases hp : (rPA == rPB) <;> simp_all
    | projInfo tB =>
      obtain ⟨yT, rfl, hyT⟩ := denoteCI_proj_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
  | projInfo tA =>
    obtain ⟨xT, rfl, hxT⟩ := denoteCI_proj_inv hci
    cases ci' with
    | axiomInfo vB =>
      obtain ⟨yV, rfl, hyV⟩ := denoteCI_axiom_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | defnInfo vB eB hB =>
      obtain ⟨yV, yE, rfl, hyV, hyE⟩ := denoteCI_defn_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | thmInfo vB eB =>
      obtain ⟨yV, yE, rfl, hyV, hyE⟩ := denoteCI_thm_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | indInfo vB capB =>
      obtain ⟨yV, yC, rfl, hyV, hyC⟩ := denoteCI_ind_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | ctorInfo vB nPB nFB =>
      obtain ⟨yV, rfl, hyV⟩ := denoteCI_ctor_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | recInfo vB mIB rPB rsB =>
      obtain ⟨yV, yR, rfl, hyV, hyR⟩ := denoteCI_rec_inv hci'
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨hok, Ext.refl _, rfl, rfl, by
        rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
        simp [ConLeche.ConstantInfo.canonEqFast]⟩
    | projInfo tB =>
      obtain ⟨yT, rfl, hyT⟩ := denoteCI_proj_inv hci'
      obtain ⟨hpA, hpB⟩ := hproj tA tB rfl rfl
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      refine ⟨hok, Ext.refl _, rfl, rfl, ?_⟩
      rw [ConLeche.ConstantInfo.canonEq_eq_canonEqFast]
      simp only [ConLeche.ConstantInfo.canonEqFast]
      cases htt : tA == tB with
      | true =>
        obtain rfl : tA = tB := by simpa using htt
        obtain rfl : xT = yT := Option.some.inj (hxT.symm.trans hyT)
        simp
      | false =>
        have hne : tA ≠ tB := by simpa using htt
        have : xT ≠ yT := by
          intro hEq
          subst hEq
          exact hne (denoteProjTable_inj hok.wf hpA hpB hxT hyT)
        simp [this]

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
declined one makes the lists differ at the head.

The `hproj` hypothesis is `IConstantInfo.canonEq_run`'s (task #97-P3-Checker
round 5) lifted to the two lists, at the same both-sides-at-once shape: its
premise is unreachable unless BOTH blocks contain a projection table, which no
pinned basis block does.  `IProjTableOK.mono` carries it along the fold. -/
theorem canonEqList_run_aux : ∀ (cs cs' : List IConstantInfo)
    (xs xs' : List ConstantInfo) (r : Bool) (s s' : AState), StateOK s →
    (∀ t t', IConstantInfo.projInfo t ∈ cs → IConstantInfo.projInfo t' ∈ cs' →
      IProjTableOK s.store t ∧ IProjTableOK s.store t') →
    Frontend.denoteCIList s.store cs = some xs →
    Frontend.denoteCIList s.store cs' = some xs' →
    canonEqList cs cs' s = .ok (r, s') →
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.canonEqList xs xs' := by
  intro cs
  induction cs with
  | nil =>
    intro cs' xs xs' r s s' hok hproj hcs hcs' hrun
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
    intro cs' xs xs' r s s' hok hproj hcs hcs' hrun
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
        IConstantInfo.canonEq_run hok
          (fun t t' ha hb => hproj t t' (by simp [ha]) (by simp [hb])) hx hy g1
      rcases AM.ite_ok k1 with ⟨hyes, k2⟩ | ⟨hno, k2⟩
      · obtain ⟨hok2, hx2, hc2, hp2, he2⟩ :=
          ih bs xt yt r s1 s' hok1
            (fun t t' ha hb =>
              ⟨(hproj t t' (List.mem_cons_of_mem _ ha)
                  (List.mem_cons_of_mem _ hb)).1.mono hx1,
               (hproj t t' (List.mem_cons_of_mem _ ha)
                  (List.mem_cons_of_mem _ hb)).2.mono hx1⟩)
            (denoteCIList_mono hx1 _ _ hxt)
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
    (hproj : ∀ t t', IConstantInfo.projInfo t ∈ cs →
      IConstantInfo.projInfo t' ∈ cs' →
      IProjTableOK s.store t ∧ IProjTableOK s.store t')
    (hcs : Frontend.denoteCIList s.store cs = some xs)
    (hcs' : Frontend.denoteCIList s.store cs' = some xs')
    (hrun : canonEqList cs cs' s = .ok (r, s')) :
    StateOK s' ∧ Ext s.store s'.store ∧ s'.caches = s.caches ∧
      s'.pins = s.pins ∧ r = ConLeche.canonEqList xs xs' :=
  canonEqList_run_aux cs cs' xs xs' r s s' hok hproj hcs hcs' hrun

end ConRon.Bridge

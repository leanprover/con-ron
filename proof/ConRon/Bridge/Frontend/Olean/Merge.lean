/-
# `ConRon.Bridge.Frontend.Olean.Merge` — the closure's constants merged

The twin's `Merged` holds a constant's position; its denotation is upstream's `Merged`, whose
map holds the constant (`MergedRel`).  A merge reads the store and changes nothing in it, so the
whole tier is at one store.

**A cheap test with fuel.**  `isPropCheap`'s walks take fuel here, and spent fuel is an answer,
`false`.  So the twin's `subsumes` may say `false` where upstream's says `true`, at two axioms of
one type, and nowhere else.  That cannot change the merge's arm: the twin's next question, whether
the other axiom may stand for this one, has the same answer on the same type, so the twin's run
goes on to its `fail` and claims nothing (`subsumes_run`, `mergeEntry_run`).
-/
module

public import ConRon.Arena.Frontend.Olean.Merge
public import ConRon.Bridge.Frontend.Olean.Closure
public import ConLeche.Verify.Frontend.Olean.Merge
import ConRon.Bridge.Specs

public section

namespace ConRon.Bridge.Frontend.Olean

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Arena.Frontend.Olean (OleanPins Merged Loaded CEntry subsumes isPropCheap isPropBody
  isPropHead isPropDrop mergeEntry mergeAll)
open ConLeche.Frontend.Olean (CEntryF CKindF bind_some_left)

/-! ## A constant, read back -/

/-- con-leche: ConLeche/Frontend/Olean/Spec.lean:299-305 CEntryF.mapM — the parts of a constant
read back. -/
theorem denoteCEntry_parts {st : EStore} {x : CEntry} {z : ConLeche.Frontend.Olean.CEntry}
    (h : denoteCEntry st x = some z) :
    denoteN st.ns x.c.name = some z.name ∧ x.c.levelParams.mapM (denoteN st.ns) = some z.levelParams ∧
      denoteE st x.c.type = some z.type ∧ x.c.kind.mapM (denoteN st.ns) (denoteE st) = some z.kind := by
  unfold denoteCEntry at h
  obtain ⟨e, h1, h⟩ := bind_some_left h
  obtain ⟨u, -, h⟩ := bind_some_left h
  simp only [pure, Option.some.injEq] at h
  subst h
  unfold denoteEntry CEntryF.mapM at h1
  obtain ⟨a, ha, h1⟩ := bind_some_left h1
  obtain ⟨b, hb, h1⟩ := bind_some_left h1
  obtain ⟨c, hc, h1⟩ := bind_some_left h1
  obtain ⟨d, hd, h1⟩ := bind_some_left h1
  simp only [pure, Option.some.injEq] at h1
  subst h1
  exact ⟨ha, hb, hc, hd⟩

theorem nameList_inj {st : EStore} (hw : NStoreWF st.ns) :
    ∀ {l l' : List NIdx} {zs : List ConLeche.Name}, l.mapM (denoteN st.ns) = some zs →
      l'.mapM (denoteN st.ns) = some zs → l = l'
  | [], [], _, _, _ => rfl
  | [], x :: l', zs, h, h' => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    simp only [List.mapM_cons] at h'
    obtain ⟨y, -, h'⟩ := bind_some_left h'
    obtain ⟨ys, -, h'⟩ := bind_some_left h'
    simp [pure] at h'
  | x :: l, [], zs, h, h' => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h'
    subst h'
    simp only [List.mapM_cons] at h
    obtain ⟨y, -, h⟩ := bind_some_left h
    obtain ⟨ys, -, h⟩ := bind_some_left h
    simp [pure] at h
  | x :: l, x' :: l', zs, h, h' => by
    simp only [List.mapM_cons] at h h'
    obtain ⟨y, hy, h⟩ := bind_some_left h
    obtain ⟨ys, hys, h⟩ := bind_some_left h
    obtain ⟨y', hy', h'⟩ := bind_some_left h'
    obtain ⟨ys', hys', h'⟩ := bind_some_left h'
    simp only [pure, Option.some.injEq] at h h'
    subst h
    injection h' with e1 e2
    subst e1
    subst e2
    rw [denoteN_inj hw hy hy', nameList_inj hw hys hys']

/-! ## The relation -/

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:54-57 Merged — **the twin's merge denotes
upstream's**: at a handle that denotes, the map holds what the position holds, read back. -/
structure MergedRel (st : EStore) (mg : Merged) (mgC : ConLeche.Frontend.Olean.Merged) : Prop where
  got : ∀ {n : NIdx} {nC : ConLeche.Name} {c : CEntry}, denoteN st.ns n = Option.some nC →
    mg.get n = Option.some c → ∃ cC, mgC.map[nC]? = Option.some cC ∧ denoteCEntry st c = Option.some cC
  absent : ∀ {n : NIdx} {nC : ConLeche.Name}, denoteN st.ns n = Option.some nC →
    mg.get n = Option.none → mgC.map[nC]? = Option.none
  contains : ∀ {n : NIdx} {nC : ConLeche.Name}, denoteN st.ns n = some nC →
    mg.map.contains n = mgC.map.contains nC
  order : ListRel (NR st) mg.order.toList mgC.order.toList
  /-- every key of the map denotes -/
  keys : ∀ {n : NIdx} {p : Nat × Nat}, mg.map[n]? = some p → (denoteN st.ns n).isSome
  /-- every key of upstream's map is a key's denotation -/
  keysC : ∀ {nC : ConLeche.Name} {c : ConLeche.Frontend.Olean.CEntry}, mgC.map[nC]? = some c →
    ∃ n, denoteN st.ns n = some nC ∧ mg.map.contains n = true

/-! ## `isPropCheap` -/

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap — the telescope, stripped
to some depth: what it leaves has the same result. -/
theorem isPropBody_run {s : AState} (hok : StateOK s) :
    ∀ (fuel : Nat) {e b : EIdx} {eC : Expr} {s' : AState}, denoteE s.store e = some eC →
      isPropBody fuel e s = .ok (b, s') →
      s' = s ∧ ∃ bC, denoteE s.store b = some bC ∧
        ConLeche.Frontend.Olean.isPropCheap.body eC = ConLeche.Frontend.Olean.isPropCheap.body bC
  | 0, e, b, eC, s', hd, h => by
    rw [isPropBody] at h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    cases hv
    exact ⟨hs, eC, hd, rfl⟩
  | fuel + 1, e, b, eC, s', hd, h => by
    rw [isPropBody] at h
    obtain ⟨v, s₁, h1, h⟩ := AM.bind_ok h
    obtain ⟨hs1, hv⟩ := view_run h1
    rw [hs1] at h
    have hden := denoteE_view_eq hok.wf hv
    cases v with
    | forallE t x =>
      rw [hden] at hd
      simp only [denoteEView, opt2_eq_some_iff] at hd
      obtain ⟨tC, xC, -, hx, rfl⟩ := hd
      obtain ⟨hs2, bC, hb, heq⟩ := isPropBody_run hok fuel hx h
      refine ⟨hs2, bC, hb, ?_⟩
      rw [← heq]
      simp [ConLeche.Frontend.Olean.isPropCheap.body]
    | bvar _ => obtain ⟨hv, hs⟩ := AM.pure_ok h; cases hv; exact ⟨hs, eC, hd, rfl⟩
    | fvar _ _ => obtain ⟨hv, hs⟩ := AM.pure_ok h; cases hv; exact ⟨hs, eC, hd, rfl⟩
    | sort _ => obtain ⟨hv, hs⟩ := AM.pure_ok h; cases hv; exact ⟨hs, eC, hd, rfl⟩
    | const _ _ => obtain ⟨hv, hs⟩ := AM.pure_ok h; cases hv; exact ⟨hs, eC, hd, rfl⟩
    | app _ _ => obtain ⟨hv, hs⟩ := AM.pure_ok h; cases hv; exact ⟨hs, eC, hd, rfl⟩
    | lam _ _ => obtain ⟨hv, hs⟩ := AM.pure_ok h; cases hv; exact ⟨hs, eC, hd, rfl⟩
    | letE _ _ _ => obtain ⟨hv, hs⟩ := AM.pure_ok h; cases hv; exact ⟨hs, eC, hd, rfl⟩
    | lit _ => obtain ⟨hv, hs⟩ := AM.pure_ok h; cases hv; exact ⟨hs, eC, hd, rfl⟩
    | proj _ _ _ => obtain ⟨hv, hs⟩ := AM.pure_ok h; cases hv; exact ⟨hs, eC, hd, rfl⟩

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap — the head constant, and an
expression with a head is not a telescope. -/
theorem isPropHead_run {s : AState} (hok : StateOK s) :
    ∀ (fuel : Nat) {e : EIdx} {eC : Expr} {k k' : Nat} {n : NIdx} {s' : AState},
      denoteE s.store e = some eC →
      isPropHead fuel e k s = .ok (some (n, k'), s') →
      s' = s ∧ ConLeche.Frontend.Olean.isPropCheap.body eC = eC ∧ ∃ nC, denoteN s.store.ns n = some nC ∧
        ConLeche.Frontend.Olean.isPropCheap.head eC k = some (nC, k')
  | 0, e, eC, k, k', n, s', hd, h => by
    rw [isPropHead] at h
    cases (AM.pure_ok h).1
  | fuel + 1, e, eC, k, k', n, s', hd, h => by
    rw [isPropHead] at h
    obtain ⟨v, s₁, h1, h⟩ := AM.bind_ok h
    obtain ⟨hs1, hv⟩ := view_run h1
    rw [hs1] at h
    have hden := denoteE_view_eq hok.wf hv
    rw [hden] at hd
    cases v with
    | app f a =>
      simp only [denoteEView, opt2_eq_some_iff] at hd
      obtain ⟨fC, aC, hf, -, rfl⟩ := hd
      obtain ⟨hs2, -, nC, hn, hh⟩ := isPropHead_run hok fuel hf h
      refine ⟨hs2, by simp [ConLeche.Frontend.Olean.isPropCheap.body], nC, hn, ?_⟩
      simpa [ConLeche.Frontend.Olean.isPropCheap.head] using hh
    | const m us =>
      obtain ⟨hv', hs⟩ := AM.pure_ok h
      simp only [Option.some.injEq, Prod.mk.injEq] at hv'
      obtain ⟨rfl, rfl⟩ := hv'
      simp only [denoteEView, opt2_eq_some_iff] at hd
      obtain ⟨nC, usC, hn, -, rfl⟩ := hd
      exact ⟨hs, by simp [ConLeche.Frontend.Olean.isPropCheap.body], nC, hn, by
        simp [ConLeche.Frontend.Olean.isPropCheap.head]⟩
    | bvar _ => cases (AM.pure_ok h).1
    | fvar _ _ => cases (AM.pure_ok h).1
    | sort _ => cases (AM.pure_ok h).1
    | lam _ _ => cases (AM.pure_ok h).1
    | forallE _ _ => cases (AM.pure_ok h).1
    | letE _ _ _ => cases (AM.pure_ok h).1
    | lit _ => cases (AM.pure_ok h).1
    | proj _ _ _ => cases (AM.pure_ok h).1

/-- con-leche: ConLeche/Frontend/Olean/Merge.lean:21-43 isPropCheap -/
theorem isPropDrop_run {s : AState} (hok : StateOK s) :
    ∀ (k : Nat) {e x : EIdx} {eC : Expr} {s' : AState}, denoteE s.store e = some eC →
      isPropDrop k e s = .ok (some x, s') →
      s' = s ∧ ∃ xC, denoteE s.store x = some xC ∧
        ConLeche.Frontend.Olean.isPropCheap.drop eC k = some xC
  | 0, e, x, eC, s', hd, h => by
    rw [isPropDrop] at h
    obtain ⟨hv, hs⟩ := AM.pure_ok h
    cases hv
    exact ⟨hs, eC, hd, by simp [ConLeche.Frontend.Olean.isPropCheap.drop]⟩
  | k + 1, e, x, eC, s', hd, h => by
    rw [isPropDrop] at h
    obtain ⟨v, s₁, h1, h⟩ := AM.bind_ok h
    obtain ⟨hs1, hv⟩ := view_run h1
    rw [hs1] at h
    have hden := denoteE_view_eq hok.wf hv
    rw [hden] at hd
    cases v with
    | forallE t b =>
      simp only [denoteEView, opt2_eq_some_iff] at hd
      obtain ⟨tC, bC, -, hb, rfl⟩ := hd
      obtain ⟨hs2, xC, hx, hdr⟩ := isPropDrop_run hok k hb h
      exact ⟨hs2, xC, hx, by simpa [ConLeche.Frontend.Olean.isPropCheap.drop] using hdr⟩
    | bvar _ => cases (AM.pure_ok h).1
    | fvar _ _ => cases (AM.pure_ok h).1
    | sort _ => cases (AM.pure_ok h).1
    | const _ _ => cases (AM.pure_ok h).1
    | app _ _ => cases (AM.pure_ok h).1
    | lam _ _ => cases (AM.pure_ok h).1
    | letE _ _ _ => cases (AM.pure_ok h).1
    | lit _ => cases (AM.pure_ok h).1
    | proj _ _ _ => cases (AM.pure_ok h).1


end ConRon.Bridge.Frontend.Olean

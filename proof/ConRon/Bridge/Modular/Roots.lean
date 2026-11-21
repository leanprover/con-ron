/-
# `ConRon.Bridge.Modular.Roots` — what a record reads, exactly (task #166)

The reach's roots are a LIST, and the reach's worklist starts from it in order, so the twin's
roots must be upstream's list, not a cover of it (`Bridge/Compare/Needs.lean` proves the cover the
justification needs).  Here the twin's walks are upstream's step for step: the memoised walk of an
expression's DAG (`needsGo_exact`: the twin's memo keyed by handle is upstream's keyed by the
expression, `NSeen`, as `Bridge/Frontend/Prepare.lean`'s `UCSeen`), a rule's, a constant's and a
table's names (`const_exact`, `table_exact`), a pinned constant's fast-path names
(`pinFootprint_exact`), and a record's reads (`recordReads_exact`).

Run style (the Checker tier's `AM.bind_ok` per bind), as the walks it mirrors.
-/
module

public import ConRon.Bridge.Modular.Worker
public import ConRon.Bridge.Compare.Needs
public import ConLeche.Driver.Reach
import ConRon.Bridge.Inductives.BlockShape
import ConRon.Bridge.Checker.NatOpNames
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Checker.Pins
import ConRon.Bridge.Specs
public import ConRon.Bridge.Checker.DivMod
import ConRon.Bridge.Compare.Justify
import ConRon.Bridge.Inductives.PosWalks

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Arena.Frontend (denoteNList)
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (CEntry Loaded)
open ConLeche.Frontend.Olean (Copy)

/-! ## The memo -/

/-- con-leche: ConLeche/Cached/Needs.lean:42-69 needsGo — **the two memos are one**, keyed by
handle and by the expression it denotes. -/
structure NSeen (st : EStore) (seen : Std.HashMap EIdx Bool) (seenP : Std.HashSet Expr) : Prop where
  fwd : ∀ h e, denoteE st h = some e → seen.contains h = true → seenP.contains e = true
  bwd : ∀ eP, seenP.contains eP = true → ∃ h, seen.contains h = true ∧ denoteE st h = some eP
  dom : ∀ h, seen.contains h = true → (denoteE st h).isSome = true

theorem NSeen.empty (st : EStore) : NSeen st ∅ ∅ where
  fwd := by intro h e _ hc; simp at hc
  bwd := by intro eP hc; simp at hc
  dom := by intro h hc; simp at hc

theorem NSeen.contains {st : EStore} (hwf : StoreWF st) {seen : Std.HashMap EIdx Bool}
    {seenP : Std.HashSet Expr} (hs : NSeen st seen seenP) {h : EIdx} {e : Expr}
    (he : denoteE st h = some e) : seen.contains h = seenP.contains e := by
  cases hc : seen.contains h with
  | true => exact (hs.fwd h e he hc).symm
  | false =>
    cases hp : seenP.contains e with
    | false => rfl
    | true =>
      obtain ⟨k, hk, hdk⟩ := hs.bwd e hp
      obtain rfl : k = h := Arena.denoteE_inj hwf hdk he
      rw [hk] at hc; exact absurd hc (by simp)

theorem NSeen.insert {st : EStore} {seen : Std.HashMap EIdx Bool} {seenP : Std.HashSet Expr}
    (hs : NSeen st seen seenP) {h : EIdx} {e : Expr} (he : denoteE st h = some e) :
    NSeen st (seen.insert h true) (seenP.insert e) where
  fwd := by
    intro k ek hk hc
    rw [Std.HashMap.contains_insert] at hc
    rw [Std.HashSet.contains_insert]
    rcases Bool.or_eq_true .. |>.mp hc with h1 | h2
    · have hhk : h = k := eq_of_beq h1
      subst hhk
      obtain rfl : e = ek := Option.some.inj (he.symm.trans hk)
      simp
    · rw [hs.fwd k ek hk h2]; simp
  bwd := by
    intro eP hc
    rw [Std.HashSet.contains_insert] at hc
    rcases Bool.or_eq_true .. |>.mp hc with h1 | h2
    · obtain rfl : e = eP := eq_of_beq h1
      exact ⟨h, by rw [Std.HashMap.contains_insert]; simp, he⟩
    · obtain ⟨k, hk, hdk⟩ := hs.bwd eP h2
      exact ⟨k, by rw [Std.HashMap.contains_insert, hk]; simp, hdk⟩
  dom := by
    intro k hk
    rw [Std.HashMap.contains_insert] at hk
    rcases Bool.or_eq_true .. |>.mp hk with h1 | h2
    · have hhk : h = k := eq_of_beq h1
      subst hhk; rw [he]; rfl
    · exact hs.dom k h2

/-- con-leche: none — **the walk's state read back**: the memo, and the names so far. -/
@[expose] def XRel (st : EStore) (x : Arena.NeedsSt) (xP : ConLeche.Cached.NeedsSt) : Prop :=
  NSeen st x.seen xP.1 ∧ denoteNList st.ns x.acc = some xP.2.toList

theorem XRel.empty (st : EStore) : XRel st Arena.NeedsSt.empty ({}, #[]) :=
  ⟨NSeen.empty st, rfl⟩

/-! ## Names -/

theorem denoteNL_append {st : EStore} :
    ∀ {a b : List NIdx} {A B : List ConLeche.Name}, denoteNL st a A → denoteNL st b B →
      denoteNL st (a ++ b) (A ++ B)
  | [], _, [], _, _, hb => hb
  | _ :: _, _, _ :: _, _, ⟨h1, h2⟩, hb => ⟨h1, denoteNL_append h2 hb⟩
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim

/-- `NeedsSt.names`, read back. -/
theorem names_exact {st : EStore} {x : Arena.NeedsSt} {xP : ConLeche.Cached.NeedsSt}
    (hx : XRel st x xP) {ns : List NIdx} {L : List ConLeche.Name}
    (hL : denoteNList st.ns ns = some L) : XRel st (x.names ns) (xP.names L) := by
  refine ⟨hx.1, ?_⟩
  simp only [Arena.NeedsSt.names, nidxAppend, List.drop_zero, Nat.sub_zero, List.take_length,
    ConLeche.Cached.NeedsSt.names, Array.toList_appendList]
  exact denoteNList_append' hx.2 hL

/-- `NeedsSt.name`, read back. -/
theorem name_exact {st : EStore} {x : Arena.NeedsSt} {xP : ConLeche.Cached.NeedsSt}
    (hx : XRel st x xP) {n : NIdx} {nm : ConLeche.Name} (hn : denoteN st.ns n = some nm) :
    XRel st (x.name n) (xP.names [nm]) := by
  refine ⟨hx.1, ?_⟩
  simp only [Arena.NeedsSt.name, ConLeche.Cached.NeedsSt.names, Array.toList_appendList]
  exact denoteNList_snoc hx.2 hn

/-- con-leche: ConLeche/Cached/Needs.lean:24-29 litNeeds — exactly. -/
theorem litNeeds_exact {s s' : AState} {l : Literal} {acc r : List NIdx} (hp : PinsOK s)
    {accP : List ConLeche.Name} (hacc : denoteNList s.store.ns acc = some accP)
    (hrun : Arena.litNeeds l acc s = .ok (r, s')) :
    s' = s ∧ denoteNList s.store.ns r = some (accP ++ ConLeche.Cached.litNeeds l) := by
  simp only [Arena.litNeeds] at hrun
  obtain ⟨ns, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hns⟩ := Inductives.litGuardNames_run hp h1
  subst hs1
  cases l with
  | natVal n =>
    obtain ⟨hr, hs⟩ := AM.pure_ok h2
    subst hr hs
    refine ⟨rfl, ?_⟩
    simp only [nidxAppend, List.drop_zero, Nat.sub_zero]
    exact denoteNList_append' hacc (denoteNL_toList _ _ (denoteNL_take 3 hns))
  | strVal str =>
    obtain ⟨hr, hs⟩ := AM.pure_ok h2
    subst hr hs
    refine ⟨rfl, ?_⟩
    simp only [nidxAppend, List.drop_zero, Nat.sub_zero, List.take_length]
    exact denoteNList_append' hacc (denoteNL_toList _ _ hns)

/-! ## The walk -/

/-- con-leche: ConLeche/Cached/Needs.lean:42-69 needsGo — **the twin's memoised walk is
upstream's**, the memos one (`NSeen`), the names the same list. -/
theorem needsGo_exact {s : AState} (hok : StateOK s) (hp : PinsOK s) :
    ∀ (fuel : Nat) {seen : Std.HashMap EIdx Bool} {acc : List NIdx}
      {seenP : Std.HashSet Expr} {accP : Array ConLeche.Name}
      {h : EIdx} {e : Expr} {r : Std.HashMap EIdx Bool × List NIdx} {s' : AState},
      NSeen s.store seen seenP → denoteNList s.store.ns acc = some accP.toList →
      denoteE s.store h = some e →
      Arena.needsGo seen acc fuel h s = .ok (r, s') →
      s' = s ∧ NSeen s.store r.1 (ConLeche.Cached.needsGo seenP accP e).1 ∧
        denoteNList s.store.ns r.2 = some (ConLeche.Cached.needsGo seenP accP e).2.toList := by
  have hwf : StoreWF s.store := hok.wf
  intro fuel
  induction fuel with
  | zero =>
    intro seen acc seenP accP h e r s' _ _ _ hrun
    rw [Arena.needsGo] at hrun
    exact absurd (AM.fail_ok hrun) (by simp)
  | succ fuel ih =>
    intro seen acc seenP accP h e r s' hseen hacc he hrun
    rw [Arena.needsGo] at hrun
    obtain ⟨v, s₁, hv, hrest⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hview⟩ := view_run hv
    rw [hs1] at hrest
    have hcont := hseen.contains hwf he
    -- a compound node: the memo's test, then the children and the node recorded (`rest`)
    have compound : ∀ (rest : AM (Std.HashMap EIdx Bool × List NIdx))
        (resP : Std.HashSet Expr × Array ConLeche.Name),
        (∀ (r' : Std.HashMap EIdx Bool × List NIdx) (s'' : AState), rest s = .ok (r', s'') →
          s'' = s ∧ NSeen s.store r'.1 resP.1 ∧ denoteNList s.store.ns r'.2 = some resP.2.toList) →
        (match seen[h]? with
          | some _ => pure (seen, acc)
          | none => rest : AM _) s = .ok (r, s') →
        s' = s ∧ NSeen s.store r.1 (if seenP.contains e then (seenP, accP) else resP).1 ∧
          denoteNList s.store.ns r.2 = some (if seenP.contains e then (seenP, accP) else resP).2.toList := by
      intro rest resP hbody hm
      cases hsh : seen[h]? with
      | some b =>
        rw [hsh] at hm
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hm
        have hc : seen.contains h = true := by
          rw [Std.HashMap.contains_eq_isSome_getElem?, hsh]; rfl
        rw [hcont] at hc
        simp only [hc, ↓reduceIte]
        exact ⟨by trivial, hseen, hacc⟩
      | none =>
        rw [hsh] at hm
        have hc : seen.contains h = false := by
          rw [Std.HashMap.contains_eq_isSome_getElem?, hsh]; rfl
        rw [hcont] at hc
        simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact hbody _ _ hm
    match v, hview with
    | .const m us, hview =>
      obtain ⟨mP, ls, rfl, hm, -⟩ := denote_const_inv hwf hview he
      simp only [] at hrest
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrest
      simp only [ConLeche.Cached.needsGo, Array.toList_push]
      exact ⟨by trivial, hseen, denoteNList_snoc hacc hm⟩
    | .bvar i, hview =>
      obtain rfl := denote_bvar_inv hwf hview he
      simp only [] at hrest
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrest
      simp only [ConLeche.Cached.needsGo]
      exact ⟨by trivial, hseen, hacc⟩
    | .sort u, hview =>
      obtain ⟨l, rfl, -⟩ := denote_sort_inv hwf hview he
      simp only [] at hrest
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrest
      simp only [ConLeche.Cached.needsGo]
      exact ⟨by trivial, hseen, hacc⟩
    | .lit l, hview =>
      obtain rfl := denote_lit_inv hwf hview he
      simp only [] at hrest
      obtain ⟨a, s₂, h1, h2⟩ := AM.bind_ok hrest
      obtain ⟨rfl, ha⟩ := litNeeds_exact hp hacc h1
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      simp only [ConLeche.Cached.needsGo, Array.toList_appendList]
      exact ⟨by trivial, hseen, ha⟩
    | .fvar k ty, hview =>
      obtain ⟨t, rfl, hdt⟩ := denote_fvar_inv hwf hview he
      try simp only [] at hrest
      simp only [ConLeche.Cached.needsGo]
      refine compound _ _ (fun r' s'' h1 => ?_) hrest
      obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok h1
      obtain ⟨sn1, ac1⟩ := p1
      obtain ⟨rfl, hs1, ha1⟩ := ih hseen hacc hdt hg1
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr1
      exact ⟨rfl, hs1.insert he, ha1⟩
    | .proj nn i sub, hview =>
      obtain ⟨nm, es, rfl, hnn, hsub⟩ := denote_proj_inv hwf hview he
      simp only [] at hrest
      simp only [ConLeche.Cached.needsGo]
      refine compound _ _ (fun r' s'' h1 => ?_) hrest
      obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok h1
      obtain ⟨sn1, ac1⟩ := p1
      obtain ⟨rfl, hs1, ha1⟩ := ih (accP := accP.push nm) hseen (by
        rw [Array.toList_push]; exact denoteNList_snoc hacc hnn) hsub hg1
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr1
      exact ⟨rfl, hs1.insert he, ha1⟩
    | .app f a, hview =>
      obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_app_inv hwf hview he
      simp only [] at hrest
      simp only [ConLeche.Cached.needsGo]
      refine compound _ _ (fun r' s'' h1 => ?_) hrest
      obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok h1
      obtain ⟨sn1, ac1⟩ := p1
      obtain ⟨rfl, hs1, ha1⟩ := ih hseen hacc hf hg1
      obtain ⟨p2, s₃, hg2, hr2⟩ := AM.bind_ok hr1
      obtain ⟨sn2, ac2⟩ := p2
      obtain ⟨rfl, hs2, ha2⟩ := ih hs1 ha1 ha hg2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr2
      exact ⟨rfl, hs2.insert he, ha2⟩
    | .lam ty body, hview =>
      obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_lam_inv hwf hview he
      simp only [] at hrest
      simp only [ConLeche.Cached.needsGo]
      refine compound _ _ (fun r' s'' h1 => ?_) hrest
      obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok h1
      obtain ⟨sn1, ac1⟩ := p1
      obtain ⟨rfl, hs1, ha1⟩ := ih hseen hacc hf hg1
      obtain ⟨p2, s₃, hg2, hr2⟩ := AM.bind_ok hr1
      obtain ⟨sn2, ac2⟩ := p2
      obtain ⟨rfl, hs2, ha2⟩ := ih hs1 ha1 ha hg2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr2
      exact ⟨rfl, hs2.insert he, ha2⟩
    | .forallE ty body, hview =>
      obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_forallE_inv hwf hview he
      simp only [] at hrest
      simp only [ConLeche.Cached.needsGo]
      refine compound _ _ (fun r' s'' h1 => ?_) hrest
      obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok h1
      obtain ⟨sn1, ac1⟩ := p1
      obtain ⟨rfl, hs1, ha1⟩ := ih hseen hacc hf hg1
      obtain ⟨p2, s₃, hg2, hr2⟩ := AM.bind_ok hr1
      obtain ⟨sn2, ac2⟩ := p2
      obtain ⟨rfl, hs2, ha2⟩ := ih hs1 ha1 ha hg2
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr2
      exact ⟨rfl, hs2.insert he, ha2⟩
    | .letE ty w body, hview =>
      obtain ⟨et, ew, eb, rfl, h1d, h2d, h3d⟩ := denote_letE_inv hwf hview he
      simp only [] at hrest
      simp only [ConLeche.Cached.needsGo]
      refine compound _ _ (fun r' s'' h1 => ?_) hrest
      obtain ⟨p1, s₂, hg1, hr1⟩ := AM.bind_ok h1
      obtain ⟨sn1, ac1⟩ := p1
      obtain ⟨rfl, hs1, ha1⟩ := ih hseen hacc h1d hg1
      obtain ⟨p2, s₃, hg2, hr2⟩ := AM.bind_ok hr1
      obtain ⟨sn2, ac2⟩ := p2
      obtain ⟨rfl, hs2, ha2⟩ := ih hs1 ha1 h2d hg2
      obtain ⟨p3, s₄, hg3, hr3⟩ := AM.bind_ok hr2
      obtain ⟨sn3, ac3⟩ := p3
      obtain ⟨rfl, hs3, ha3⟩ := ih hs2 ha2 h3d hg3
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr3
      exact ⟨rfl, hs3.insert he, ha3⟩

/-- con-leche: ConLeche/Cached/Needs.lean:74-75 NeedsSt.expr — exactly. -/
theorem expr_exact {s s' : AState} (hok : StateOK s) (hp : PinsOK s) {x y : Arena.NeedsSt}
    {xP : ConLeche.Cached.NeedsSt} {e : EIdx} {t : Expr} (hx : XRel s.store x xP)
    (he : denoteE s.store e = some t) (hrun : x.expr e s = .ok (y, s')) :
    s' = s ∧ XRel s.store y (xP.expr t) := by
  simp only [Arena.NeedsSt.expr] at hrun
  obtain ⟨r, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨rfl, i1, i2⟩ := needsGo_exact hok hp _ hx.1 hx.2 he h1
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
  exact ⟨rfl, i1, i2⟩

/-- `pins.foldl NeedsSt.expr`, exactly. -/
theorem exprs_exact {s : AState} (hok : StateOK s) (hp : PinsOK s) :
    ∀ (es : List EIdx) (ts : List Expr) (x : Arena.NeedsSt) (xP : ConLeche.Cached.NeedsSt)
      {y : Arena.NeedsSt} {s' : AState},
      XRel s.store x xP → Frontend.denoteEList s.store es = some ts →
      x.exprs es s = .ok (y, s') → s' = s ∧ XRel s.store y (ts.foldl ConLeche.Cached.NeedsSt.expr xP)
  | [], ts, x, xP, y, s', hx, hts, hrun => by
    simp only [Frontend.denoteEList, Option.some.injEq] at hts
    subst hts
    simp only [Arena.NeedsSt.exprs] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, hx⟩
  | e :: es, ts, x, xP, y, s', hx, hts, hrun => by
    obtain ⟨t, ts', he, hes, rfl⟩ := denoteEList_cons_inv hts
    simp only [Arena.NeedsSt.exprs] at hrun
    obtain ⟨x2, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨rfl, o1⟩ := expr_exact hok hp hx he h1
    exact exprs_exact hok hp es ts' x2 _ o1 hes h2

/-- con-leche: ConLeche/Cached/Needs.lean:80-85 NeedsSt.rule — exactly. -/
theorem rule_exact {s s' : AState} (hok : StateOK s) (hp : PinsOK s) {x y : Arena.NeedsSt}
    {xP : ConLeche.Cached.NeedsSt} {r : IRecRule} {R : RecRule} (hx : XRel s.store x xP)
    (hR : Frontend.denoteRule s.store r = some R) (hrun : x.rule r s = .ok (y, s')) :
    s' = s ∧ XRel s.store y (xP.rule R) := by
  obtain ⟨hc, hf, hrhs, -⟩ := denoteRule_inv hR
  simp only [Arena.NeedsSt.rule] at hrun
  obtain ⟨x1, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨rfl, o1⟩ := expr_exact hok hp hx hrhs h1
  have o2 := name_exact o1 hc
  unfold ConLeche.Cached.NeedsSt.rule
  cases hfr : r.fire with
  | nested lvls pins =>
    rw [hfr] at h2 hf
    rw [denoteFire_nested_opt] at hf
    simp only [opt2] at hf
    split at hf
    · next ls ps hls hps =>
      have hRf : R.fire = .nested ls ps := (Option.some.inj hf).symm
      rw [hRf]
      simp only at h2
      exact exprs_exact hok hp pins ps _ _ o2 hps h2
    · exact absurd hf (by simp)
  | plain =>
    rw [hfr] at h2 hf
    simp only [Frontend.denoteFire, Option.some.injEq] at hf
    rw [← hf]
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    exact ⟨rfl, o2⟩
  | levels lvls =>
    rw [hfr] at h2 hf
    simp only [Frontend.denoteFire, Option.map_eq_some_iff] at hf
    obtain ⟨_, -, hf⟩ := hf
    rw [← hf]
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    exact ⟨rfl, o2⟩

/-- `rules.foldl NeedsSt.rule`, exactly. -/
theorem rules_exact {s : AState} (hok : StateOK s) (hp : PinsOK s) :
    ∀ (rs : List IRecRule) (Rs : List RecRule) (x : Arena.NeedsSt) (xP : ConLeche.Cached.NeedsSt)
      {y : Arena.NeedsSt} {s' : AState},
      XRel s.store x xP → Frontend.denoteRules s.store rs = some Rs →
      x.rules rs s = .ok (y, s') → s' = s ∧ XRel s.store y (Rs.foldl ConLeche.Cached.NeedsSt.rule xP)
  | [], Rs, x, xP, y, s', hx, hRs, hrun => by
    simp only [Frontend.denoteRules, Option.some.injEq] at hRs
    subst hRs
    simp only [Arena.NeedsSt.rules] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, hx⟩
  | r :: rs, Rs, x, xP, y, s', hx, hRs, hrun => by
    obtain ⟨R, Rs', hR, hRs', rfl⟩ := denoteRules_cons hRs
    simp only [Arena.NeedsSt.rules] at hrun
    obtain ⟨x2, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨rfl, o1⟩ := rule_exact hok hp hx hR h1
    exact rules_exact hok hp rs Rs' x2 _ o1 hRs' h2

/-! ## A pinned constant's fast-path names, exactly -/

theorem pinFootprintReduce_exact {n : NIdx} {nm : ConLeche.Name} {xs r : List NIdx}
    {L : List ConLeche.Name} {s s' : AState} (hok : StateOK s) (hp : PinsOK s)
    (hn : denoteN s.store.ns n = some nm) (hxs : denoteNList s.store.ns xs = some L)
    (hrun : Arena.pinFootprintReduce n xs s = .ok (r, s')) :
    s' = s ∧ denoteNList s.store.ns r = some (L ++
        (if ConLeche.reduceOpNames.contains nm then [ConLeche.reduceElemName nm] else [])) := by
  simp only [Arena.pinFootprintReduce] at hrun
  obtain ⟨ns, s0, g0, r0⟩ := AM.bind_ok hrun
  obtain ⟨p0, d0⟩ := reduceOpNames_run hp g0
  subst s0
  have hc := denoteNL_contains hok.wf d0 hn
  rcases AM.ite_ok r0 with ⟨hb, k⟩ | ⟨hb, k⟩
  · obtain ⟨e, s1, g1, r1⟩ := AM.bind_ok k
    obtain ⟨p1, d1⟩ := reduceElemName_run hok hp hn g1
    subst s1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r1
    rw [hc] at hb
    rw [ite_eq_left hb]
    exact ⟨rfl, denoteNList_snoc hxs d1⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
    rw [hc] at hb
    rw [ite_eq_right hb, List.append_nil]
    exact ⟨rfl, hxs⟩

theorem pinFootprintNat_exact {n : NIdx} {nm : ConLeche.Name} {dms r : List NIdx}
    {s s' : AState} (hok : StateOK s) (hp : PinsOK s) (hn : denoteN s.store.ns n = some nm)
    (hdms : denoteNL s.store dms ConLeche.natDivModNames)
    (hrun : Arena.pinFootprintNat n dms s = .ok (r, s')) :
    s' = s ∧ denoteNList s.store.ns r = some
      (ConLeche.natOpDeps nm ++ [ConLeche.natName, ConLeche.natZeroName, ConLeche.natSuccName] ++
        (if nm = ConLeche.natBeqName || nm = ConLeche.natBleName ||
            ConLeche.natDivModNames.contains nm then
          [ConLeche.boolName, ConLeche.boolTrueName, ConLeche.boolFalseName] else [])) := by
  simp only [Arena.pinFootprintNat, Arena.natBeqName, Arena.pinNatBeq, Arena.natBleName,
    Arena.pinNatBle, Arena.boolName, Arena.pinBool, Arena.boolTrueName, Arena.pinBoolTrue,
    Arena.boolFalseName, Arena.pinBoolFalse] at hrun
  obtain ⟨deps, s0, g0, r0⟩ := AM.bind_ok hrun
  have p0 := natOpDeps_state hp g0
  obtain ⟨-, -, -, -, d0⟩ := natOpDeps_run hok hp hn g0
  subst s0
  obtain ⟨lits, s1, g1, r1⟩ := AM.bind_ok r0
  obtain ⟨p1, d1⟩ := Inductives.litGuardNames_run hp g1
  subst s1
  obtain ⟨be, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨p2, d2⟩ := pinAt_run (x := ConLeche.natBeqName) hp (by rfl) g2
  subst s2
  obtain ⟨bl, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨p3, d3⟩ := pinAt_run (x := ConLeche.natBleName) hp (by rfl) g3
  subst s3
  have hbase : denoteNList s.store.ns (nidxAppend deps lits 0 3) = some
      (ConLeche.natOpDeps nm ++ [ConLeche.natName, ConLeche.natZeroName, ConLeche.natSuccName]) := by
    simp only [nidxAppend, List.drop_zero, Nat.sub_zero]
    exact denoteNL_toList _ _ (denoteNL_append d0 (denoteNL_take 3 d1))
  have hcond : ((n == be || n == bl || dms.contains n) = true) ↔
      ((nm = ConLeche.natBeqName || nm = ConLeche.natBleName ||
        ConLeche.natDivModNames.contains nm) = true) := by
    rw [denoteNL_contains hok.wf hdms hn]
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_handle_iff hok.wf hn d2,
      beq_handle_iff hok.wf hn d3]
  rcases AM.ite_ok r3 with ⟨hb, k⟩ | ⟨hb, k⟩
  · obtain ⟨b, s4, g4, r4⟩ := AM.bind_ok k
    obtain ⟨p4, d4⟩ := pinAt_run (x := ConLeche.boolName) hp (by rfl) g4
    subst s4
    obtain ⟨bt, s5, g5, r5⟩ := AM.bind_ok r4
    obtain ⟨p5, d5⟩ := pinAt_run (x := ConLeche.boolTrueName) hp (by rfl) g5
    subst s5
    obtain ⟨bf, s6, g6, r6⟩ := AM.bind_ok r5
    obtain ⟨p6, d6⟩ := pinAt_run (x := ConLeche.boolFalseName) hp (by rfl) g6
    subst s6
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r6
    rw [ite_eq_left (hcond.mp hb)]
    refine ⟨rfl, ?_⟩
    have := denoteNList_snoc (denoteNList_snoc (denoteNList_snoc hbase d4) d5) d6
    simpa [List.append_assoc] using this
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
    rw [ite_eq_right (fun h => hb (hcond.mpr h)), List.append_nil]
    exact ⟨rfl, hbase⟩

/-- con-leche: ConLeche/Kernel/Install.lean:106-115 pinFootprint — **the names a pinned
constant's fast path reads, exactly**. -/
theorem pinFootprint_exact {n : NIdx} {nm : ConLeche.Name} {r : List NIdx}
    {s s' : AState} (hok : StateOK s) (hp : PinsOK s) (hn : denoteN s.store.ns n = some nm)
    (hrun : Arena.pinFootprint n s = .ok (r, s')) :
    s' = s ∧ denoteNList s.store.ns r = some (ConLeche.pinFootprint nm) := by
  simp only [Arena.pinFootprint] at hrun
  obtain ⟨ops, s0, g0, r0⟩ := AM.bind_ok hrun
  obtain ⟨p0, d0⟩ := natOpNames_run hp g0
  subst s0
  obtain ⟨dms, s1, g1, r1⟩ := AM.bind_ok r0
  obtain ⟨p1, d1⟩ := natDivModNames_run hp g1
  subst s1
  have hcond : ((ops.contains n || dms.contains n) = true) ↔
      ((ConLeche.natOpNames.contains nm || ConLeche.natDivModNames.contains nm) = true) := by
    rw [denoteNL_contains hok.wf d0 hn, denoteNL_contains hok.wf d1 hn]
  unfold ConLeche.pinFootprint
  rcases AM.ite_ok r1 with ⟨hb, k⟩ | ⟨hb, k⟩
  · obtain ⟨xs, s2, g2, r2⟩ := AM.bind_ok k
    obtain ⟨rfl, c2⟩ := pinFootprintNat_exact hok hp hn d1 g2
    obtain ⟨rfl, c3⟩ := pinFootprintReduce_exact hok hp hn c2 r2
    rw [ite_eq_left (hcond.mp hb)]
    exact ⟨rfl, c3⟩
  · obtain ⟨rfl, c3⟩ := pinFootprintReduce_exact hok hp hn rfl k
    rw [ite_eq_right (fun h => hb (hcond.mpr h))]
    exact ⟨rfl, by simpa using c3⟩

/-! ## A constant's, a table's and a record's reads, exactly -/

theorem constTail_exact {s s' : AState} (hok : StateOK s) (hp : PinsOK s)
    {x2 y : Arena.NeedsSt} {xP : ConLeche.Cached.NeedsSt} {n : NIdx} {nm : ConLeche.Name}
    (hx : XRel s.store x2 xP) (hn : denoteN s.store.ns n = some nm)
    (hrun : (do let fp ← Arena.pinFootprint n; pure (x2.names fp) : AM _) s = .ok (y, s')) :
    s' = s ∧ XRel s.store y (xP.names (ConLeche.pinFootprint nm)) := by
  obtain ⟨fp, s3, h5, h6⟩ := AM.bind_ok hrun
  obtain ⟨rfl, hfp⟩ := pinFootprint_exact hok hp hn h5
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h6
  exact ⟨rfl, names_exact hx hfp⟩

/-- con-leche: ConLeche/Cached/Needs.lean:87-95 NeedsSt.const — **what a constant's laws read,
exactly**. -/
theorem const_exact {s s' : AState} (hok : StateOK s) (hp : PinsOK s) {x y : Arena.NeedsSt}
    {xP : ConLeche.Cached.NeedsSt} {ci : IConstantInfo} {c : ConstantInfo}
    (hx : XRel s.store x xP) (hc : Frontend.denoteCI s.store ci = some c)
    (hrun : x.const ci s = .ok (y, s')) :
    s' = s ∧ XRel s.store y (xP.const c) := by
  obtain ⟨-, -, hty⟩ := denoteCV_inv (denoteCI_toConstantVal hc)
  have hn := denoteCI_name hc
  simp only [Arena.NeedsSt.const] at hrun
  obtain ⟨x1, s1, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨rfl, o1⟩ := expr_exact hok hp hx hty h1
  unfold ConLeche.Cached.NeedsSt.const
  cases ci with
  | defnInfo v e hint =>
    obtain ⟨cv, xv, rfl, -, hxv⟩ := denoteCI_defn_inv hc
    obtain ⟨x2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨rfl, o2⟩ := expr_exact hok hp o1 hxv h3
    exact constTail_exact hok hp o2 hn h4
  | recInfo v mI rP k rs =>
    obtain ⟨cv, Rs, rfl, -, hRs⟩ := denoteCI_rec_inv hc
    obtain ⟨x2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨rfl, o2⟩ := rules_exact hok hp rs Rs x1 _ o1 hRs h3
    exact constTail_exact hok hp o2 hn h4
  | indInfo v cap =>
    obtain ⟨cv, d, rfl, -, hd⟩ := denoteCI_ind_inv hc
    obtain ⟨x2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
    simp only [Frontend.denoteCaps] at hd
    split at hd
    · next all ctors hall hctors =>
      obtain rfl := (Option.some.inj hd).symm
      exact constTail_exact hok hp (names_exact o1 hall) hn h4
    · exact absurd hd (by simp)
  | axiomInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc
    obtain ⟨_, -, rfl⟩ := hc
    obtain ⟨x2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
    exact constTail_exact hok hp o1 hn h4
  | thmInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hc
    obtain ⟨_, -, rfl⟩ := hc
    obtain ⟨x2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
    exact constTail_exact hok hp o1 hn h4
  | ctorInfo v nP nF T =>
    obtain ⟨cv, rfl, -⟩ := denoteCI_ctor_inv hc
    obtain ⟨x2, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
    exact constTail_exact hok hp o1 hn h4

/-- con-leche: ConLeche/Cached/Needs.lean:97-99 NeedsSt.table — exactly. -/
theorem table_exact {s s' : AState} (hok : StateOK s) (hp : PinsOK s) {x y : Arena.NeedsSt}
    {xP : ConLeche.Cached.NeedsSt} {t : IProjTable} {pt : ProjTable} (hx : XRel s.store x xP)
    (ht : Frontend.denoteProjTable s.store t = some pt) (hrun : x.table t s = .ok (y, s')) :
    s' = s ∧ XRel s.store y (xP.table pt) := by
  rw [denoteProjTable_opt, denoteEArray_map] at ht
  simp only [opt2, opt3] at ht
  split at ht
  · next a b hab hb =>
    split at hab
    · next sn lps c hsn hlps hc =>
      obtain rfl := (Option.some.inj hab).symm
      simp only [Option.map_eq_some_iff] at hb
      obtain ⟨bs, hbs, rfl⟩ := hb
      obtain rfl := (Option.some.inj ht).symm
      simp only [Arena.NeedsSt.table] at hrun
      have o1 := name_exact (name_exact hx hsn) hc
      obtain ⟨rfl, o2⟩ := exprs_exact hok hp t.bodies.toList bs _ _ o1 hbs hrun
      refine ⟨rfl, ?_⟩
      unfold ConLeche.Cached.NeedsSt.table
      have e : (xP.names [sn, c]) = ((xP.names [sn]).names [c]) := by
        simp [ConLeche.Cached.NeedsSt.names]
      simpa [e] using o2
    · exact absurd hab (by simp)
  · exact absurd ht (by simp)

theorem recordReadsConsts_exact {s : AState} (hok : StateOK s) (hp : PinsOK s) :
    ∀ (cs : List IConstantInfo) (csP : List ConstantInfo) (x : Arena.NeedsSt)
      (xP : ConLeche.Cached.NeedsSt) {y : Arena.NeedsSt} {s' : AState},
      XRel s.store x xP → Frontend.denoteCIList s.store cs = some csP →
      Arena.Modular.recordReadsConsts x cs s = .ok (y, s') →
      s' = s ∧ XRel s.store y (csP.foldl ConLeche.Cached.NeedsSt.const xP)
  | [], csP, x, xP, y, s', hx, hcs, hrun => by
    simp only [Frontend.denoteCIList, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.Modular.recordReadsConsts] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, hx⟩
  | c :: cs, csP, x, xP, y, s', hx, hcs, hrun => by
    simp only [Frontend.denoteCIList] at hcs
    split at hcs
    · rename_i cP csP' hc hcs'
      cases hcs
      simp only [Arena.Modular.recordReadsConsts] at hrun
      obtain ⟨x2, s1, h1, h2⟩ := AM.bind_ok hrun
      obtain ⟨rfl, o1⟩ := const_exact hok hp hx hc h1
      exact recordReadsConsts_exact hok hp cs csP' x2 _ o1 hcs' h2
    · cases hcs

theorem recordReadsTables_exact {s : AState} (hok : StateOK s) (hp : PinsOK s) :
    ∀ (ts : List IProjTable) (tsP : List ProjTable) (x : Arena.NeedsSt)
      (xP : ConLeche.Cached.NeedsSt) {y : Arena.NeedsSt} {s' : AState},
      XRel s.store x xP → Frontend.denoteProjTableList s.store ts = some tsP →
      Arena.Modular.recordReadsTables x ts s = .ok (y, s') →
      s' = s ∧ XRel s.store y (tsP.foldl ConLeche.Cached.NeedsSt.table xP)
  | [], tsP, x, xP, y, s', hx, hts, hrun => by
    simp only [Frontend.denoteProjTableList, Option.some.injEq] at hts
    subst hts
    simp only [Arena.Modular.recordReadsTables] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, hx⟩
  | t :: ts, tsP, x, xP, y, s', hx, hts, hrun => by
    rw [denoteProjTableList_cons_opt, opt2_eq_some_iff] at hts
    obtain ⟨pt, tsP', h1, h2, rfl⟩ := hts
    simp only [Arena.Modular.recordReadsTables] at hrun
    obtain ⟨x2, s1, g1, g2⟩ := AM.bind_ok hrun
    obtain ⟨rfl, o1⟩ := table_exact hok hp hx h1 g1
    exact recordReadsTables_exact hok hp ts tsP' x2 _ o1 h2 g2

/-- con-leche: ConLeche/Driver/Reach.lean:90-94 recordReads — **what a record reads, upstream's
list**. -/
theorem recordReads_exact {s s' : AState} (hok : DriverOK s) (hoff : s.store.scratchOn = false)
    {d : IDeclaration} {dC : Declaration} (hp : PersDecl d)
    (hd : ConRon.Arena.Frontend.denoteDecl s.store d = some dC) {ns : List NIdx}
    (h : ConRon.Arena.Modular.recordReads d s = .ok (ns, s')) :
    DStep s s' ∧ denoteNList s'.store.ns ns = some (ConLeche.Cached.recordReads dC).toList := by
  unfold ConRon.Arena.Modular.recordReads at h
  obtain ⟨cs, s₁, h1, k1⟩ := AM.bind_ok h
  obtain ⟨hok1, hx1, hpins1, hoff1, hcs, -⟩ := constsSpec hok hoff hp hd h1
  obtain ⟨ts, s₂, h2, k2⟩ := AM.bind_ok k1
  obtain ⟨hok2, hx2, hpins2, hoff2, hts, -⟩ := tablesSpec hok1 hoff1 hp
    (denoteDecl_ext hx1 hd) h2
  obtain ⟨x, s₃, h3, k3⟩ := AM.bind_ok k2
  obtain ⟨rfl, o3⟩ := recordReadsConsts_exact hok2.state hok2.pins cs _ _ _
    (XRel.empty _) (denoteCIList_mono hx2 _ _ hcs) h3
  obtain ⟨y, s₄, h4, k4⟩ := AM.bind_ok k3
  obtain ⟨rfl, o4⟩ := recordReadsTables_exact hok2.state hok2.pins ts _ _ _ o3 hts h4
  obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
  exact ⟨⟨hok2, hx1.trans hx2, hpins2.trans hpins1, hoff2⟩, o4.2⟩

/-! ## A certified operation's pin ground, exactly -/

/-- con-leche: none — the ground walk's state read back. -/
@[expose] def GRel (st : EStore) (x : Std.HashSet EIdx × Array NIdx)
    (xP : Std.HashSet Expr × Array ConLeche.Name) : Prop :=
  UCSeen st x.1 xP.1 ∧ denoteNList st.ns x.2.toList = some xP.2.toList

/-- upstream's step of the ground walk. -/
@[expose] def goC (x : Std.HashSet Expr × Array ConLeche.Name) (e : Expr) :
    Std.HashSet Expr × Array ConLeche.Name :=
  ConLeche.Frontend.usedConstsGo x.1 x.2 e

theorem groundGo_exact {s s' : AState} (hok : StateOK s) {x y : Std.HashSet EIdx × Array NIdx}
    {xP : Std.HashSet Expr × Array ConLeche.Name} (hx : GRel s.store x xP) {e : EIdx} {t : Expr}
    (he : denoteE s.store e = some t) (h : Arena.Modular.groundGo x e s = .ok (y, s')) :
    s' = s ∧ GRel s.store y (goC xP t) := by
  unfold Arena.Modular.groundGo at h
  obtain ⟨y1, y2⟩ := y
  obtain ⟨rfl, h1, h2⟩ := usedConstsGo_run hok _ hx.1 hx.2 he h
  exact ⟨rfl, h1, h2⟩

theorem groundGoAll_exact {s : AState} (hok : StateOK s) :
    ∀ (es : List EIdx) (ts : List Expr) {x y : Std.HashSet EIdx × Array NIdx}
      {xP : Std.HashSet Expr × Array ConLeche.Name} {s' : AState},
      GRel s.store x xP → Frontend.denoteEList s.store es = some ts →
      Arena.Modular.groundGoAll x es s = .ok (y, s') → s' = s ∧ GRel s.store y (ts.foldl goC xP)
  | [], ts, x, y, xP, s', hx, hts, h => by
    simp only [Frontend.denoteEList, Option.some.injEq] at hts
    subst hts
    simp only [Arena.Modular.groundGoAll, List.foldlM_nil] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨rfl, hx⟩
  | e :: es, ts, x, y, xP, s', hx, hts, h => by
    obtain ⟨t, ts', he, hes, rfl⟩ := denoteEList_cons_inv hts
    simp only [Arena.Modular.groundGoAll, List.foldlM_cons] at h
    obtain ⟨x1, s1, h1, h2⟩ := AM.bind_ok h
    obtain ⟨rfl, o1⟩ := groundGo_exact hok hx he h1
    exact groundGoAll_exact hok es ts' o1 hes (by simpa [Arena.Modular.groundGoAll] using h2)

theorem groundStmts_go {s : AState} (hok : StateOK s) :
    ∀ (sts : List (List EIdx × EIdx)) (stsP : List (List Expr × Expr))
      {x y : Std.HashSet EIdx × Array NIdx} {xP : Std.HashSet Expr × Array ConLeche.Name}
      {s' : AState},
      GRel s.store x xP → StmtsDenote s.store sts stsP →
      sts.foldlM (m := AM) Arena.Modular.groundStmt x s = .ok (y, s') →
      s' = s ∧ GRel s.store y (stsP.foldl (fun x st => goC (st.1.foldl goC x) st.2) xP)
  | [], [], x, y, xP, s', hx, _, h => by
    simp only [List.foldlM_nil] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨rfl, hx⟩
  | (hs, e) :: sts, (xs, t) :: stsP, x, y, xP, s', hx, ⟨d1, d2, d3⟩, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨x1, s1, h1, h2⟩ := AM.bind_ok h
    simp only [Arena.Modular.groundStmt] at h1
    obtain ⟨x0, s0, g0, g1⟩ := AM.bind_ok h1
    obtain ⟨rfl, o0⟩ := groundGoAll_exact hok hs xs hx d1 g0
    obtain ⟨rfl, o1⟩ := groundGo_exact hok o0 d2 g1
    exact groundStmts_go hok sts stsP o1 d3 h2
  | [], _ :: _, _, _, _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, _, _, _, h, _ => h.elim

theorem typePins_go {s : AState} (hok : StateOK s) :
    ∀ (ps : List (NIdx × EIdx)) (psP : List (ConLeche.Name × Expr))
      {x y : Std.HashSet EIdx × Array NIdx} {xP : Std.HashSet Expr × Array ConLeche.Name}
      {s' : AState},
      GRel s.store x xP → TypePinsDenote s.store ps psP →
      ps.foldlM (m := AM) (fun x p => Arena.Modular.groundGo (x.1, x.2.push p.1) p.2) x s = .ok (y, s') →
      s' = s ∧ GRel s.store y (psP.foldl (fun x p => goC (x.1, x.2.push p.1) p.2) xP)
  | [], [], x, y, xP, s', hx, _, h => by
    simp only [List.foldlM_nil] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨rfl, hx⟩
  | p :: ps, q :: psP, x, y, xP, s', hx, ⟨d1, d2, d3⟩, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨x1, s1, h1, h2⟩ := AM.bind_ok h
    have hx' : GRel s.store (x.1, x.2.push p.1) (xP.1, xP.2.push q.1) :=
      ⟨hx.1, by simp only [Array.toList_push]; exact denoteNList_snoc hx.2 d1⟩
    obtain ⟨rfl, o1⟩ := groundGo_exact hok hx' d2 h1
    exact typePins_go hok ps psP o1 d3 h2
  | [], _ :: _, _, _, _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, _, _, _, h, _ => h.elim

theorem groundVariant_exact {s s' : AState} (hok : StateOK s) (hp : PinsOK s)
    {ps : INatOpPinSet} {psP : NatOpPinSet} (hps : PinSetDenote s.store ps psP)
    {c : NIdx} {nm : ConLeche.Name} (hn : denoteN s.store.ns c = some nm)
    {x y : Std.HashSet EIdx × Array NIdx} {xP : Std.HashSet Expr × Array ConLeche.Name}
    (hx : GRel s.store x xP) (h : Arena.Modular.groundVariant x ps c s = .ok (y, s')) :
    s' = s ∧ GRel s.store y
      ((ConLeche.divModTypePins psP nm).foldl (fun x p => goC (x.1, x.2.push p.1) p.2)
        ((ConLeche.divModCertProofs psP nm).foldl goC (goC xP (ConLeche.divModDeclPin psP nm)))) := by
  simp only [Arena.Modular.groundVariant] at h
  obtain ⟨p, s1, h1, k1⟩ := AM.bind_ok h
  obtain ⟨rfl, dp⟩ := divModDeclPin_run hok hp hps hn h1
  obtain ⟨x1, s2, h2, k2⟩ := AM.bind_ok k1
  obtain ⟨rfl, o1⟩ := groundGo_exact hok hx dp h2
  obtain ⟨cp, s3, h3, k3⟩ := AM.bind_ok k2
  obtain ⟨rfl, dcp⟩ := divModCertProofs_run hok hp hps hn h3
  obtain ⟨x2, s4, h4, k4⟩ := AM.bind_ok k3
  obtain ⟨rfl, o2⟩ := groundGoAll_exact hok cp _ o1 dcp h4
  obtain ⟨tp, s5, h5, k5⟩ := AM.bind_ok k4
  obtain ⟨rfl, dtp⟩ := divModTypePins_run hok hp hps hn h5
  exact typePins_go hok tp _ o2 dtp k5

theorem pinsFold_go {s : AState} (hok : StateOK s) (hp : PinsOK s) {c : NIdx} {nm : ConLeche.Name}
    (hn : denoteN s.store.ns c = some nm) :
    ∀ (pins : List INatOpPinSet) (pinsC : List NatOpPinSet)
      {x y : Std.HashSet EIdx × Array NIdx} {xP : Std.HashSet Expr × Array ConLeche.Name}
      {s' : AState},
      GRel s.store x xP → PinsDenote s.store pins pinsC →
      pins.foldlM (m := AM) (fun x ps => Arena.Modular.groundVariant x ps c) x s = .ok (y, s') →
      s' = s ∧ GRel s.store y (pinsC.foldl (fun x ps =>
        (ConLeche.divModTypePins ps nm).foldl (fun x p => goC (x.1, x.2.push p.1) p.2)
          ((ConLeche.divModCertProofs ps nm).foldl goC (goC x (ConLeche.divModDeclPin ps nm)))) xP)
  | [], [], x, y, xP, s', hx, _, h => by
    simp only [List.foldlM_nil] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨rfl, hx⟩
  | ps :: pins, q :: pinsC, x, y, xP, s', hx, ⟨d1, d2⟩, h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨x1, s1, h1, h2⟩ := AM.bind_ok h
    obtain ⟨rfl, o1⟩ := groundVariant_exact hok hp d1 hn hx h1
    exact pinsFold_go hok hp hn pins pinsC o1 d2 h2
  | [], _ :: _, _, _, _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, _, _, _, h, _ => h.elim

/-- con-leche: ConLeche/Driver/Worker.lean:53-66 pinGround — **a certified operation's pin
ground, upstream's list**, at the pin variants the twin's interned pins denote. -/
theorem pinGround_exact {s s' : AState} (hok : StateOK s) (hp : PinsOK s)
    {pins : List INatOpPinSet} {pinsC : List NatOpPinSet} (hpins : PinsDenote s.store pins pinsC)
    {c : NIdx} {nm : ConLeche.Name} (hn : denoteN s.store.ns c = some nm) {r : Array NIdx}
    (h : Arena.Modular.pinGround pins c s = .ok (r, s')) :
    IStepS s s' ∧ denoteNList s'.store.ns r.toList = some (ConLeche.Driver.pinGround pinsC nm).toList := by
  unfold Arena.Modular.pinGround at h
  obtain ⟨dms, s0, g0, k1⟩ := AM.bind_ok h
  obtain ⟨rfl, d0⟩ := natDivModNames_run hp g0
  have hc := denoteNL_contains hok.wf d0 hn
  unfold ConLeche.Driver.pinGround
  dsimp only at k1
  by_cases hb : dms.contains c = true
  · rw [ite_eq_right (by rw [hb]; decide)] at k1
    rw [hc] at hb
    rw [ite_eq_right (by rw [hb]; decide)]
    obtain ⟨u0, s1', g0', k1'⟩ := AM.bind_ok k1
    obtain ⟨-, rfl⟩ := AM.pure_ok g0'
    obtain ⟨eq, s1, g1, k2⟩ := AM.bind_ok k1'
    obtain ⟨rfl, deq⟩ := pinAt_run (x := ConLeche.eqName) hp (by rfl) g1
    obtain ⟨x, s2, g2, k3⟩ := AM.bind_ok k2
    simp only [Arena.Modular.groundStmts] at g2
    obtain ⟨sts, s3, g3, g4⟩ := AM.bind_ok g2
    obtain ⟨hst3, dsts⟩ := divModCertStmts_run hok hp hn g3
    have hx0 : GRel s3.store ({}, #[eq]) ({}, #[ConLeche.eqName]) :=
      ⟨UCSeen.empty, by simp [denoteNList, denoteN_ext deq hst3.ext]⟩
    obtain ⟨rfl, o1⟩ := groundStmts_go hst3.ok sts _ hx0 dsts g4
    obtain ⟨y, s4, g5, k4⟩ := AM.bind_ok k3
    obtain ⟨rfl, o2⟩ := pinsFold_go hst3.ok (hp.mono hst3.ext hst3.pins) (denoteN_ext hn hst3.ext)
      pins pinsC o1 (PinsDenote.mono hst3.ext _ _ hpins) g5
    obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
    exact ⟨hst3, o2.2⟩
  · rw [ite_eq_left (by simp only [Bool.not_eq_true] at hb; rw [hb]; rfl)] at k1
    rw [hc] at hb
    rw [ite_eq_left (by simp only [Bool.not_eq_true] at hb; rw [hb]; rfl)]
    obtain ⟨rfl, rfl⟩ := AM.pure_ok k1
    exact ⟨IStepS.refl hok, rfl⟩

/-! ## The reach's roots -/

theorem denoteNList_filter {st : NStore} {p : NIdx → Bool} {q : ConLeche.Name → Bool}
    (hpq : ∀ x y, denoteN st x = some y → p x = q y) :
    ∀ {xs : List NIdx} {ys : List ConLeche.Name}, denoteNList st xs = some ys →
      denoteNList st (xs.filter p) = some (ys.filter q)
  | [], ys, h => by simp only [denoteNList, Option.some.injEq] at h; subst h; rfl
  | x :: xs, ys, h => by
    simp only [denoteNList] at h
    split at h
    · rename_i y ys' hy hys
      cases h
      simp only [List.filter_cons, hpq x y hy]
      split
      · simp only [denoteNList, hy, denoteNList_filter hpq hys]
      · exact denoteNList_filter hpq hys
    · cases h

theorem setRel_foldl_insert {st : EStore} :
    ∀ {fp : List NIdx} {L : List ConLeche.Name} {t : Std.HashSet NIdx} {tC : Std.HashSet ConLeche.Name},
      denoteNList st.ns fp = some L → SetRel st t tC →
      SetRel st (fp.foldl (fun s n => s.insert n) t) (L.foldl (fun s n => s.insert n) tC)
  | [], L, t, tC, hfp, ht => by
    simp only [denoteNList, Option.some.injEq] at hfp
    subst hfp; exact ht
  | a :: l, L, t, tC, hfp, ht => by
    simp only [denoteNList] at hfp
    split at hfp
    · rename_i y ys hy hys
      cases hfp
      simp only [List.foldl_cons]
      exact setRel_foldl_insert hys (ht.insert hy)
    · cases hfp

theorem footprints_go {s : AState} (hok : StateOK s) (hp : PinsOK s)
    {cs : List CEntry} {csC : List ConLeche.Frontend.Olean.CEntry}
    (hrel : ListRel (fun c cC => denoteCEntry s.store c = some cC) cs csC) :
    ∀ {t : Std.HashSet NIdx} {tC : Std.HashSet ConLeche.Name} {r : Std.HashSet NIdx} {s' : AState},
      SetRel s.store t tC →
      cs.foldlM (m := AM) (fun s c => do
        pure ((← Arena.pinFootprint c.c.name).foldl (fun s n => s.insert n) s)) t s = .ok (r, s') →
      s' = s ∧ SetRel s.store r (csC.foldl
        (fun s c => (pinFootprint c.name).foldl (fun s n => s.insert n) s) tC) := by
  induction hrel with
  | nil =>
    intro t tC r s' ht h
    simp only [List.foldlM_nil] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨rfl, ht⟩
  | @cons c cC cs csC hc _ ih =>
    intro t tC r s' ht h
    simp only [List.foldlM_cons] at h
    obtain ⟨t1, s1, h1, h2⟩ := AM.bind_ok h
    obtain ⟨fp, s0, g0, g1⟩ := AM.bind_ok h1
    obtain ⟨hs0, hfp⟩ := pinFootprint_exact hok hp (denoteCEntry_parts hc).1 g0
    subst s0
    obtain ⟨hv, hs1⟩ := AM.pure_ok g1
    subst s1
    subst hv
    exact ih (setRel_foldl_insert hfp ht) h2

theorem foldl_app_shift {α β : Type} (f : α → Array β) :
    ∀ (l : List α) (a : Array β),
      l.foldl (fun acc x => acc ++ f x) a = a ++ l.foldl (fun acc x => acc ++ f x) #[]
  | [], a => by simp
  | x :: l, a => by
    simp only [List.foldl_cons]
    rw [foldl_app_shift f l (a ++ f x), foldl_app_shift f l (#[] ++ f x)]
    simp [Array.append_assoc]

/-- A skipping fold of appends is a fold of appends. -/
theorem foldl_skip_eq {α β : Type} (p : α → Bool) (g : α → Array β) (l : List α) (a : Array β) :
    l.foldl (fun acc x => if p x then acc else acc ++ g x) a =
      l.foldl (fun acc x => acc ++ (if p x then #[] else g x)) a := by
  congr 1
  funext acc x
  split <;> simp

theorem foldl_append_toList {α β : Type} (f : α → Array β) :
    ∀ (l : List α), (l.foldl (fun acc d => acc ++ f d) #[]).toList = (l.map fun x => (f x).toList).flatten
  | [] => rfl
  | x :: l => by
    rw [List.foldl_cons, foldl_app_shift f l (#[] ++ f x), Array.toList_append, foldl_append_toList f l]
    simp

theorem flatten_map_eq_foldl {α β : Type} (f : α → Array β) (l : Array α) :
    (l.map f).flatten = l.toList.foldl (fun acc d => acc ++ f d) #[] := by
  apply Array.toList_inj.mp
  rw [foldl_append_toList]
  simp [Array.toList_flatten, Function.comp_def]

theorem usesShift (l : List ConLeche.Frontend.Olean.CEntry) (A : Array ConLeche.Name) :
    l.foldl (fun acc (c : ConLeche.Frontend.Olean.CEntry) =>
      if c.skipped then acc else acc ++ c.uses.toArray) A =
    A ++ l.foldl (fun acc (c : ConLeche.Frontend.Olean.CEntry) =>
      if c.skipped then acc else acc ++ c.uses.toArray) #[] := by
  rw [foldl_skip_eq, foldl_skip_eq]
  exact foldl_app_shift _ l A

/-- The roots' first filter at a name, read back. -/
@[expose] def RootP (first : Std.HashMap NIdx Copy) (fp : Std.HashSet NIdx) (x : NIdx) : Bool :=
  first.contains x || !fp.contains x

@[expose] def RootPC (first : Std.HashMap ConLeche.Name Copy) (fp : Std.HashSet ConLeche.Name)
    (x : ConLeche.Name) : Bool :=
  first.contains x || !fp.contains x

theorem rootP_rel {st : EStore} (hw : NStoreWF st.ns) {first : Std.HashMap NIdx Copy}
    {firstC : Std.HashMap ConLeche.Name Copy} (hf : HMRel (· = ·) st first firstC)
    {fp : Std.HashSet NIdx} {fpC : Std.HashSet ConLeche.Name} (hfp : SetRel st fp fpC) :
    ∀ x y, denoteN st.ns x = some y → RootP first fp x = RootPC firstC fpC y := by
  intro x y hxy
  simp only [RootP, RootPC, HMRel.contains hw hf hxy, hfp.contains hw hxy]

theorem recordsRoots_go {ix : ConRon.Arena.Frontend.Olean.NameIndex} {fp : Std.HashSet NIdx}
    {firstC : Std.HashMap ConLeche.Name Copy} {fpC : Std.HashSet ConLeche.Name} :
    ∀ (l : List IDeclaration) {lC : List Declaration} (out : Array NIdx)
      (accU : Array ConLeche.Name) {s s' : AState} {r : Array NIdx},
      DriverOK s → s.store.scratchOn = false → HMRel (· = ·) s.store ix.first firstC →
      SetRel s.store fp fpC → (∀ d ∈ l, PersDecl d) → denoteDecls s.store l = some lC →
      denoteNList s.store.ns out.toList = some (accU.toList.filter (RootPC firstC fpC)) →
      l.foldlM (m := AM) (fun out d => do
        pure (Arena.Modular.pushUnpinned out ix fp (← Arena.Modular.recordReads d).toArray)) out s =
        .ok (r, s') →
      DStep s s' ∧ denoteNList s'.store.ns r.toList = some
        ((lC.foldl (fun acc d => acc ++ ConLeche.Cached.recordReads d) accU).toList.filter
          (RootPC firstC fpC))
  | [], lC, out, accU, s, s', r, hok, hoff, _, _, _, hl, ho, h => by
    simp only [denoteDecls, Option.some.injEq] at hl
    subst hl
    simp only [List.foldlM_nil] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨DStep.refl hok hoff, ho⟩
  | d :: l, lC, out, accU, s, s', r, hok, hoff, hf, hfp, hp, hl, ho, h => by
    simp only [denoteDecls] at hl
    split at hl
    · rename_i dC lC' hd hls
      cases hl
      simp only [List.foldlM_cons] at h
      obtain ⟨o1, s1, h1, h2⟩ := AM.bind_ok h
      obtain ⟨ns, s0, g0, g1⟩ := AM.bind_ok h1
      obtain ⟨hst0, hns⟩ := recordReads_exact hok hoff (hp d (List.mem_cons_self ..)) hd g0
      obtain ⟨hv1, hs01⟩ := AM.pure_ok g1
      subst s1
      subst hv1
      have hw := nsWF_of_StateOK hst0.ok.state
      have hf' := hf.ext hst0.ext (fun _ _ h => h)
      have hfp' := hfp.ext hst0.ext
      have ho1 : denoteNList s0.store.ns (Arena.Modular.pushUnpinned out ix fp ns.toArray).toList =
          some ((accU ++ ConLeche.Cached.recordReads dC).toList.filter (RootPC firstC fpC)) := by
        simp only [Arena.Modular.pushUnpinned, Array.toList_append, Array.toList_filter,
          List.filter_append]
        exact denoteNList_append' (denoteNList_ext hst0.ext.lss.ls.ns _ _ ho)
          (denoteNList_filter (rootP_rel hw hf' hfp') (by simpa using hns))
      obtain ⟨hst, hr⟩ := recordsRoots_go l _ (accU ++ ConLeche.Cached.recordReads dC) hst0.ok
        hst0.scratch hf' hfp' (fun x hx => hp x (List.mem_cons_of_mem _ hx))
        (denoteDecls_ext hst0.ext _ _ hls) ho1 h2
      exact ⟨hst0.trans hst, hr⟩
    · cases hl

theorem usesFold_go {st : EStore} (hw : NStoreWF st.ns) {ix : ConRon.Arena.Frontend.Olean.NameIndex}
    {fp : Std.HashSet NIdx} {firstC : Std.HashMap ConLeche.Name Copy}
    {fpC : Std.HashSet ConLeche.Name} (hf : HMRel (· = ·) st ix.first firstC)
    (hfp : SetRel st fp fpC) :
    ∀ {cs : List CEntry} {csC : List ConLeche.Frontend.Olean.CEntry},
      ListRel (fun c cC => denoteCEntry st c = some cC) cs csC →
      ∀ (out : Array NIdx) (accU : Array ConLeche.Name),
      denoteNList st.ns out.toList = some (accU.toList.filter (RootPC firstC fpC)) →
      denoteNList st.ns (cs.foldl (fun out (c : CEntry) =>
          if c.skipped then out else Arena.Modular.pushUnpinned out ix fp c.uses) out).toList =
        some ((csC.foldl (fun acc (c : ConLeche.Frontend.Olean.CEntry) =>
          if c.skipped then acc else acc ++ c.uses.toArray) accU).toList.filter (RootPC firstC fpC))
  | _, _, .nil, out, accU, ho => ho
  | c :: _, cC :: _, .cons hc hr, out, accU, ho => by
    simp only [List.foldl_cons]
    rw [denoteCEntry_skipped hc]
    refine usesFold_go hw hf hfp hr _ _ ?_
    split
    · exact ho
    · unfold denoteCEntry at hc
      obtain ⟨e, -, hc⟩ := ConLeche.Frontend.Olean.bind_some_left hc
      obtain ⟨u, hu, hc⟩ := ConLeche.Frontend.Olean.bind_some_left hc
      simp only [pure, Option.some.injEq] at hc
      subst hc
      simp only [Arena.Modular.pushUnpinned, Array.toList_append, Array.toList_filter,
        List.filter_append, toArray_toSubarray_toList]
      exact denoteNList_append' ho (denoteNList_filter (rootP_rel hw hf hfp)
        (by rw [denoteNList_eq_mapM]; exact hu))

theorem groundRoots_go {pins : List INatOpPinSet} {pinsC : List NatOpPinSet}
    {ix : ConRon.Arena.Frontend.Olean.NameIndex} {firstC : Std.HashMap ConLeche.Name Copy}
    (X : List ConLeche.Name) :
    ∀ (cs : List CEntry) {csC : List ConLeche.Frontend.Olean.CEntry} (out : Array NIdx)
      (gAcc : Array ConLeche.Name) {s s' : AState} {r : Array NIdx},
      StateOK s → PinsOK s → PinsDenote s.store pins pinsC → HMRel (· = ·) s.store ix.first firstC →
      ListRel (fun c cC => denoteCEntry s.store c = some cC) cs csC →
      denoteNList s.store.ns out.toList = some (X ++ gAcc.toList.filter firstC.contains) →
      cs.foldlM (m := AM) (fun out (c : CEntry) => do
        if c.skipped then pure out
        else pure (Arena.Modular.pushLoaded out ix (← Arena.Modular.pinGround pins c.c.name))) out s =
        .ok (r, s') →
      ParseStep s s' ∧ denoteNList s'.store.ns r.toList = some (X ++
        (csC.foldl (fun acc (c : ConLeche.Frontend.Olean.CEntry) =>
          if c.skipped then acc else acc ++ ConLeche.Driver.pinGround pinsC c.name) gAcc).toList.filter
          firstC.contains)
  | [], csC, out, gAcc, s, s', r, hok, _, _, _, hr, ho, h => by
    cases hr
    simp only [List.foldlM_nil] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨ParseStep.refl hok, ho⟩
  | c :: cs, _, out, gAcc, s, s', r, hok, hp, hpins, hf, .cons hc hr, ho, h => by
    rename_i cC csC
    simp only [List.foldlM_cons] at h
    obtain ⟨o1, s1, h1, h2⟩ := AM.bind_ok h
    simp only [List.foldl_cons]
    rw [← denoteCEntry_skipped hc]
    by_cases hsk : c.skipped = true
    · rw [ite_eq_left hsk] at h1
      obtain ⟨hv1, hs01⟩ := AM.pure_ok h1
      subst o1
      subst s1
      rw [ite_eq_left hsk]
      exact groundRoots_go X cs out gAcc hok hp hpins hf hr ho h2
    · rw [ite_eq_right hsk] at h1
      obtain ⟨g, s0, g0, g1⟩ := AM.bind_ok h1
      obtain ⟨hst0, hg⟩ := pinGround_exact hok hp hpins (denoteCEntry_parts hc).1 g0
      obtain ⟨hv1, hs01⟩ := AM.pure_ok g1
      subst o1
      subst s1
      rw [ite_eq_right hsk]
      have hst0' := hst0.toParse'
      have hw := nsWF_of_StateOK hst0'.ok
      have hf' := hf.ext hst0'.ext (fun _ _ h => h)
      have ho1 : denoteNList s0.store.ns (Arena.Modular.pushLoaded out ix g).toList =
          some (X ++ (gAcc ++ ConLeche.Driver.pinGround pinsC cC.name).toList.filter firstC.contains) := by
        simp only [Arena.Modular.pushLoaded, Array.toList_append, Array.toList_filter,
          List.filter_append, ← List.append_assoc]
        exact denoteNList_append' (denoteNList_ext hst0'.ext.lss.ls.ns _ _ ho)
          (denoteNList_filter (fun x y hxy => HMRel.contains hw hf' hxy) hg)
      obtain ⟨hst, hr'⟩ := groundRoots_go X cs _ _ hst0'.ok (hp.mono hst0'.ext hst0'.pins)
        (PinsDenote.mono hst0'.ext _ _ hpins) hf'
        (ListRel.mono' (fun _ _ h => denoteCEntry_ext hst0'.ext h) hr) ho1 h2
      exact ⟨hst0'.trans hst, hr'⟩

/-- con-leche: ConLeche/Driver/Worker.lean:68-85 ownRoots — **the reach's roots, upstream's
list**, at the pin list the twin's interned pins denote. -/
theorem ownRoots_exact {s s' : AState} (hok : DriverOK s) (hoff : s.store.scratchOn = false)
    {pins : List INatOpPinSet} {pinsC : List NatOpPinSet} (hpins : PinsDenote s.store pins pinsC)
    {ix : ConRon.Arena.Frontend.Olean.NameIndex} {ixC : ConLeche.Frontend.Olean.NameIndex}
    (hf : HMRel (· = ·) s.store ix.first ixC.first) {cs : Array CEntry}
    {lC : ConLeche.Frontend.Olean.Loaded}
    (hcs : ListRel (fun c cC => denoteCEntry s.store c = some cC) cs.toList lC.constants.toList)
    {ds : Array IDeclaration} {dsC : Array Declaration} (hp : PersDecls ds)
    (hd : denoteDeclArray s.store ds = some dsC) {r : Array NIdx}
    (h : Arena.Modular.ownRoots pins ix cs ds s = .ok (r, s')) :
    DStep s s' ∧ denoteNList s'.store.ns r.toList = some (ConLeche.Driver.ownRoots pinsC ixC lC dsC).toList := by
  have hw := nsWF_of_StateOK hok.state
  unfold Arena.Modular.ownRoots at h
  obtain ⟨fp, s1, h1, k1⟩ := AM.bind_ok h
  unfold Arena.Modular.footprints at h1
  rw [← Array.foldlM_toList] at h1
  obtain ⟨rfl, hfp⟩ := footprints_go hok.state hok.pins hcs (SetRel.empty _) h1
  obtain ⟨out, s2, h2, k2⟩ := AM.bind_ok k1
  unfold Arena.Modular.recordsRoots at h2
  rw [← Array.foldlM_toList] at h2
  obtain ⟨hst2, hout⟩ := recordsRoots_go ds.toList #[] #[] hok hoff hf hfp
    (fun d hd' => hp d (by simpa using hd')) (denoteDeclArray_iff.mp hd) rfl h2
  have hw2 := nsWF_of_StateOK hst2.ok.state
  have hf2 := hf.ext hst2.ext (fun _ _ h => h)
  have hfp2 := hfp.ext hst2.ext
  have hcs2 := ListRel.mono' (fun _ _ h => denoteCEntry_ext hst2.ext h) hcs
  have hout2 := usesFold_go hw2 hf2 hfp2 hcs2 out _ hout
  dsimp only at k2
  unfold Arena.Modular.groundRoots at k2
  rw [← Array.foldlM_toList] at k2
  obtain ⟨hst3, hr⟩ := groundRoots_go (X := _) cs.toList _ #[] hst2.ok.state hst2.ok.pins
    (PinsDenote.mono hst2.ext _ _ hpins) hf2 hcs2 (by simpa using hout2) k2
  refine ⟨hst2.trans (DStep.of_parse hst2.ok hst2.scratch hst3), ?_⟩
  rw [hr]
  congr 1
  unfold ConLeche.Driver.ownRoots
  simp only [Array.toList_append, Array.toList_filter]
  simp only [← Array.foldl_toList]
  rw [usesShift]
  simp only [Array.toList_append, List.filter_append, List.append_assoc]
  have hRP : ∀ (f : Std.HashMap ConLeche.Name Copy) (fp : Std.HashSet ConLeche.Name),
      RootPC f fp = fun x => f.contains x || !fp.contains x := fun _ _ => rfl
  rw [hRP, flatten_map_eq_foldl]

theorem copiesNames_go {s : AState} :
    ∀ (l : List IDeclaration) {lC : List Declaration} (out : Array NIdx) {X : List ConLeche.Name}
      {s' : AState} {r : Array NIdx},
      DriverOK s → s.store.scratchOn = false → (∀ d ∈ l, PersDecl d) →
      denoteDecls s.store l = some lC → denoteNList s.store.ns out.toList = some X →
      l.foldlM (m := AM) (fun out d => do pure (out ++ (← Arena.Modular.declNames d).toArray)) out s =
        .ok (r, s') →
      DStep s s' ∧ denoteNList s'.store.ns r.toList =
        some (X ++ (lC.flatMap fun d => ConLeche.Modular.declNames d))
  | [], lC, out, X, s', r, hok, hoff, _, hl, ho, h => by
    simp only [denoteDecls, Option.some.injEq] at hl
    subst hl
    simp only [List.foldlM_nil] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨DStep.refl hok hoff, by simpa using ho⟩
  | d :: l, lC, out, X, s', r, hok, hoff, hp, hl, ho, h => by
    simp only [denoteDecls] at hl
    split at hl
    · rename_i dC lC' hd hls
      cases hl
      simp only [List.foldlM_cons] at h
      obtain ⟨o1, s1, h1, h2⟩ := AM.bind_ok h
      obtain ⟨ns, s0, g0, g1⟩ := AM.bind_ok h1
      obtain ⟨hst0, hns⟩ := declNames_run hok hoff (hp d (List.mem_cons_self ..)) hd g0
      obtain ⟨rfl, rfl⟩ := AM.pure_ok g1
      obtain ⟨hst, hr⟩ := copiesNames_go l (out ++ ns.toArray) hst0.ok hst0.scratch
        (fun x hx => hp x (List.mem_cons_of_mem _ hx)) (denoteDecls_ext hst0.ext _ _ hls)
        (X := X ++ ConLeche.Modular.declNames dC)
        (by rw [Array.toList_append, List.toList_toArray]
            exact denoteNList_append' (denoteNList_ext hst0.ext.lss.ls.ns _ _ ho) hns) h2
      exact ⟨hst0.trans hst, by simpa [List.flatMap_cons, List.append_assoc] using hr⟩
    · cases hl

/-- con-leche: ConLeche/Driver/Worker.lean:143-153 rootsAt — **the reach's roots of a worker that
adds the imports `x`, upstream's list**. -/
theorem rootsAt_exact {s s' : AState} (hok : DriverOK s) (hoff : s.store.scratchOn = false)
    {pins : List INatOpPinSet} {pinsC : List NatOpPinSet} (hpins : PinsDenote s.store pins pinsC)
    {x : Array (ConLeche.Frontend.Olean.ImportF NIdx)} {xC : Array ConLeche.Frontend.Olean.ImportRec}
    (hx : ImpsD s.store x xC) {ix : ConRon.Arena.Frontend.Olean.NameIndex}
    {ixC : ConLeche.Frontend.Olean.NameIndex} (hf : HMRel (· = ·) s.store ix.first ixC.first)
    {l : Loaded} {lC : ConLeche.Frontend.Olean.Loaded} (hl : LoadedRel s.store l lC)
    {ds : Array IDeclaration} {dsC : Array Declaration} (hp : PersDecls ds)
    (hd : denoteDeclArray s.store ds = some dsC) {r : Array NIdx}
    (h : Arena.Modular.rootsAt pins x ix l.constants ds s = .ok (r, s')) :
    DStep s s' ∧ denoteNList s'.store.ns r.toList = some (ConLeche.Driver.rootsAt pinsC xC ixC lC dsC).toList := by
  have hw := nsWF_of_StateOK hok.state
  have hcs := listRel_of_mapM hl.constants
  unfold Arena.Modular.rootsAt at h
  unfold ConLeche.Driver.rootsAt
  rw [← (ImpsD.isEmpty hx)]
  by_cases he : x.isEmpty = true
  · rw [ite_eq_left he] at h ⊢
    simp only [bind_pure] at h
    exact ownRoots_exact hok hoff hpins hf hcs hp hd h
  · rw [ite_eq_right he] at h ⊢
    obtain ⟨u0, s0, g0, h⟩ := AM.bind_ok h
    obtain ⟨-, hs00⟩ := AM.pure_ok g0
    subst s0
    obtain ⟨own, s1, h1, k1⟩ := AM.bind_ok h
    unfold Arena.Modular.recsLoaded at h1
    rw [← Array.foldlM_toList] at h1
    obtain ⟨hst1, hp1, hr1⟩ := recsLoaded_go ds.toList #[] hok hoff hf
      (fun d hd' => hp d (by simpa using hd')) (fun _ h => by simp at h) (denoteDeclArray_iff.mp hd) rfl h1
    obtain ⟨out, s2, h2, k2⟩ := AM.bind_ok k1
    have hown : denoteDeclArray s1.store own = some (ConLeche.Driver.ownRecs xC ixC dsC) := by
      unfold ConLeche.Driver.ownRecs
      rw [ite_eq_right (by rw [← (ImpsD.isEmpty hx)]; exact he)]
      refine denoteDeclArray_iff.mpr ?_
      rw [hr1, Array.toList_filter]
      simp only [List.nil_append]
      congr 1
      try (apply List.filter_congr; intro d _; cases ConLeche.Driver.loadedRec ixC d <;> rfl)
    have hf1 := hf.ext hst1.ext (fun _ _ h => h)
    have hcsU : ListRel (fun c cC => denoteCEntry s1.store c = some cC)
        (Arena.Modular.unloadedConstants ix l.constants).toList
        (lC.constants.filter (!ixC.first.contains ·.name)).toList := by
      simp only [Arena.Modular.unloadedConstants, Array.toList_filter]
      exact listRel_filter (fun a b hab => by
        rw [HMRel.contains (nsWF_of_StateOK hst1.ok.state) hf1 (denoteCEntry_parts hab).1])
        (ListRel.mono' (fun _ _ h => denoteCEntry_ext hst1.ext h) hcs)
    obtain ⟨hst2, hout⟩ := ownRoots_exact hst1.ok hst1.scratch (PinsDenote.mono hst1.ext _ _ hpins)
      hf1 (lC := { lC with constants := lC.constants.filter (!ixC.first.contains ·.name) }) hcsU hp1
      hown h2
    obtain ⟨cps, s3, h3, k3⟩ := AM.bind_ok k2
    unfold Arena.Modular.recsLoaded at h3
    rw [← Array.foldlM_toList] at h3
    have hd2 := denoteDeclArray_iff.mp (denoteDeclArray_ext (hst1.ext.trans hst2.ext) hd)
    obtain ⟨hst3, hp3, hr3⟩ := recsLoaded_go (want := true) ds.toList #[] hst2.ok hst2.scratch
      (hf1.ext hst2.ext (fun _ _ h => h)) (fun d hd' => hp d (by simpa using hd'))
      (fun _ h => by simp at h) hd2 rfl h3
    rw [← Array.foldlM_toList] at k3
    obtain ⟨hst4, hr4⟩ := copiesNames_go cps.toList out hst3.ok hst3.scratch
      (fun d hd' => hp3 d (by simpa using hd')) hr3 (denoteNList_ext hst3.ext.lss.ls.ns _ _ hout) k3
    refine ⟨hst1.trans (hst2.trans (hst3.trans hst4)), ?_⟩
    rw [hr4]
    unfold ConLeche.Driver.copyRecs
    rw [ite_eq_right (by rw [← (ImpsD.isEmpty hx)]; exact he)]
    simp only [Array.toList_append, Array.toList_flatMap, Array.toList_filter, List.nil_append]
    try congr 2

/-! ## The holes of a compared challenge's own records -/

/-- con-leche: ConLeche/Driver/Worker.lean:242-248 isHoleRec — **a hole, upstream's test**, at a
`uses` that says what upstream's `usesC` says. -/
theorem isHoleRec_run {st0 : EStore} {uses : IDeclaration → AM (Array NIdx)}
    {usesC : Declaration → Array ConLeche.Name} (hU : UsedRel st0 uses usesC)
    {s s' : AState} (hx : Ext st0 s.store) (hok : StateOK s) (hp : PinsOK s)
    (hoff : s.store.scratchOn = false) {d : IDeclaration} {dC : Declaration}
    (hd : ConRon.Arena.Frontend.denoteDecl s.store d = some dC) {b : Bool}
    (h : Arena.Modular.isHoleRec uses d s = .ok (b, s')) :
    ParseStep s s' ∧ b = ConLeche.Driver.isHoleRec usesC dC := by
  have hsorry : ∀ {v : EIdx} {vP : Expr} {b : Bool} {s' : AState}, denoteE s.store v = some vP →
      Arena.Modular.usesSorry v s = .ok (b, s') →
      ParseStep s s' ∧ b = Expr.mentionsAnyConstC [ConLeche.sorryAxName] vP := by
    intro v vP b s' hv h
    simp only [Arena.Modular.usesSorry] at h
    obtain ⟨n, s1, h1, h2⟩ := AM.bind_ok h
    obtain ⟨hs1, hn⟩ := pinAt_run hp pinNames_eq_sorryAxName h1
    subst s1
    have hss : s' = s := by
      simp only [Arena.mentionsAnyConst] at h2
      obtain ⟨q, s2, g1, g2⟩ := AM.bind_ok h2
      obtain ⟨-, rfl⟩ := AM.pure_ok g2
      exact Inductives.mentionsAnyGo_state _ _ _ _ g1
    obtain ⟨-, hr⟩ := Inductives.mentionsAnyConst_spec [n] [ConLeche.sorryAxName] v vP s s' b hok
      ⟨by simp [ConRon.Arena.Frontend.denoteNList, hn], hv⟩ h2
    subst hss
    refine ⟨ParseStep.refl hok, ?_⟩
    rw [ConLeche.Expr.mentionsAnyConstC_spec]
    exact hr
  cases d with
  | axiomDecl cv =>
    simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cvP, hcv, rfl⟩ := hd
    simp only [Arena.Modular.isHoleRec] at h
    obtain ⟨r, s1, h1, h2⟩ := AM.bind_ok h
    obtain ⟨rfl, hr⟩ := builtinAxiomName_run hok hp (denoteCV_name hcv) h1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    exact ⟨ParseStep.refl hok, by simp [ConLeche.Driver.isHoleRec, hr]⟩
  | defnDecl cv v hint =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at hd
    split at hd
    · rename_i cvP vP hcv hv
      cases hd
      simp only [Arena.Modular.isHoleRec] at h
      exact hsorry hv h
    · cases hd
  | opaqueDecl cv v =>
    simp only [ConRon.Arena.Frontend.denoteDecl] at hd
    split at hd
    · rename_i cvP vP hcv hv
      cases hd
      simp only [Arena.Modular.isHoleRec] at h
      exact hsorry hv h
    · cases hd
  | thmDecl cv v =>
    simp only [Arena.Modular.isHoleRec] at h
    obtain ⟨us, s1, h1, h2⟩ := AM.bind_ok h
    obtain ⟨hst1, hus⟩ := hU hx hok hoff hd h1
    obtain ⟨n, s2, h3, h4⟩ := AM.bind_ok h2
    obtain ⟨hs2, hn⟩ := pinAt_run (hp.mono hst1.ext hst1.pins) pinNames_eq_sorryAxName h3
    subst s2
    obtain ⟨hb, hs'⟩ := AM.pure_ok h4
    subst s'
    subst hb
    refine ⟨hst1, ?_⟩
    have hdC : ∃ cvP vP, dC = .thmDecl cvP vP := by
      simp only [ConRon.Arena.Frontend.denoteDecl] at hd
      split at hd
      · cases hd; exact ⟨_, _, rfl⟩
      · cases hd
    obtain ⟨cvP, vP, rfl⟩ := hdC
    simp only [ConLeche.Driver.isHoleRec]
    rw [← Array.contains_toList, ← Array.contains_toList]
    exact ConRon.Bridge.Frontend.denoteNList_contains hst1.ok.wf hn _ _ hus
  | quotDecl k cv =>
    obtain ⟨cvP, rfl⟩ : ∃ cvP, dC = .quotDecl k cvP := by
      simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hd
      obtain ⟨cvP, -, rfl⟩ := hd
      exact ⟨cvP, rfl⟩
    simp only [Arena.Modular.isHoleRec] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨ParseStep.refl hok, rfl⟩
  | indDecl block nP =>
    obtain ⟨b', rfl⟩ : ∃ b', dC = .indDecl b' nP := by
      simp only [ConRon.Arena.Frontend.denoteDecl, Option.map_eq_some_iff] at hd
      obtain ⟨b', -, rfl⟩ := hd
      exact ⟨b', rfl⟩
    simp only [Arena.Modular.isHoleRec] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨ParseStep.refl hok, rfl⟩

theorem ownHoles_go {st0 : EStore} {uses : IDeclaration → AM (Array NIdx)}
    {usesC : Declaration → Array ConLeche.Name} (hU : UsedRel st0 uses usesC)
    {pk : ConRon.Arena.Frontend.Olean.OleanPins} {m : NIdx} {mC : ConLeche.Name} :
    ∀ (l : List IDeclaration) {lC : List Declaration} {s s' : AState},
      Ext st0 s.store → DriverOK s → s.store.scratchOn = false →
      denoteDecls s.store l = some lC →
      l.forM (Arena.Modular.ownHoleOk pk uses m) s = .ok ((), s') →
      DStep s s' ∧ lC.forM (ConLeche.Driver.ownHoleOk mC usesC) = .ok ()
  | [], lC, s, s', _, hok, hoff, hl, h => by
    simp only [denoteDecls, Option.some.injEq] at hl
    subst hl
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    exact ⟨DStep.refl hok hoff, rfl⟩
  | d :: l, lC, s, s', hx, hok, hoff, hl, h => by
    simp only [denoteDecls] at hl
    split at hl
    · rename_i dC lC' hd hls
      cases hl
      obtain ⟨u, s1, h1, h2⟩ := AM.bind_ok h
      simp only [Arena.Modular.ownHoleOk] at h1
      obtain ⟨b, s0, g0, g1⟩ := AM.bind_ok h1
      obtain ⟨hst0, hb⟩ := isHoleRec_run hU hx hok.state hok.pins hoff hd g0
      cases b with
      | true =>
        simp only [↓reduceIte] at g1
        obtain ⟨_, _, _, g2⟩ := AM.bind_ok g1
        obtain ⟨_, _, _, g3⟩ := AM.bind_ok g2
        exact absurd (AM.fail_ok g3) (by simp)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at g1
        obtain ⟨-, rfl⟩ := AM.pure_ok g1
        have hst0' := DStep.of_parse hok hoff hst0
        obtain ⟨hst, hr⟩ := ownHoles_go hU l (hx.trans hst0'.ext) hst0'.ok hst0'.scratch
          (denoteDecls_ext hst0'.ext _ _ hls) h2
        refine ⟨hst0'.trans hst, ?_⟩
        show (do ConLeche.Driver.ownHoleOk mC usesC dC; lC'.forM (ConLeche.Driver.ownHoleOk mC usesC)) = .ok ()
        simp only [ConLeche.Driver.ownHoleOk, ← hb, Bool.false_eq_true, ↓reduceIte]
        exact hr
    · cases hl

/-- con-leche: ConLeche/Driver/Worker.lean:265-269 ownHolesOk — **no hole among a compared
challenge's own records, upstream's accept**. -/
theorem ownHolesOk_run {s s' : AState} (hok : DriverOK s) (hoff : s.store.scratchOn = false)
    {pk : ConRon.Arena.Frontend.Olean.OleanPins} {m : NIdx} {mC : ConLeche.Name}
    {uses : IDeclaration → AM (Array NIdx)} {usesC : Declaration → Array ConLeche.Name}
    (hU : UsedRel s.store uses usesC)
    {x : Array (ConLeche.Frontend.Olean.ImportF NIdx)} {xC : Array ConLeche.Frontend.Olean.ImportRec}
    (hx : ImpsD s.store x xC) {ix : ConRon.Arena.Frontend.Olean.NameIndex}
    {ixC : ConLeche.Frontend.Olean.NameIndex} (hix : HMRel (· = ·) s.store ix.first ixC.first)
    {ds : Array IDeclaration} {dsC : Array Declaration} (hp : PersDecls ds)
    (hd : denoteDeclArray s.store ds = some dsC)
    (h : Arena.Modular.ownHolesOk pk uses m x ix ds s = .ok ((), s')) :
    DStep s s' ∧ ConLeche.Driver.ownHolesOk mC xC usesC ixC dsC = .ok () := by
  unfold Arena.Modular.ownHolesOk at h
  unfold ConLeche.Driver.ownHolesOk
  rw [← (ImpsD.isEmpty hx)]
  by_cases he : x.isEmpty = true
  · rw [ite_eq_left he] at h ⊢
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    exact ⟨DStep.refl hok hoff, rfl⟩
  · rw [ite_eq_right he] at h ⊢
    obtain ⟨u0, s0, g0, h⟩ := AM.bind_ok h
    obtain ⟨-, hs00⟩ := AM.pure_ok g0
    subst s0
    obtain ⟨own, s1, h1, h2⟩ := AM.bind_ok h
    have h1' : Arena.Modular.ownRecs x ix ds s = .ok (own, s1) := by
      unfold Arena.Modular.ownRecs; rw [ite_eq_right he]; exact h1
    obtain ⟨hst1, hp1, hr1⟩ := ownRecs_run hok hoff hx hix hp hd h1'
    unfold ConLeche.Driver.ownRecs at hr1
    rw [ite_eq_right (by rw [← (ImpsD.isEmpty hx)]; exact he)] at hr1
    obtain ⟨hst2, hr⟩ := ownHoles_go hU own.toList hst1.ext hst1.ok hst1.scratch
      (denoteDeclArray_iff.mp hr1) h2
    refine ⟨hst1.trans hst2, ?_⟩
    unfold ConLeche.Driver.ownRecs
    rw [ite_eq_right (by rw [← (ImpsD.isEmpty hx)]; exact he)]
    exact hr

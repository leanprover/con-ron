/-
# `ConRon.Bridge.Inductives.PosWalks` — Theorem 1 for the positivity walk's leaves

`Arena/Inductives/Positivity.lean`'s PURE-grade leaf twins against
`ConLeche/Kernel/Inductives/Positivity.lean` (task #105, lane B-IND): the
memoised occurrence tests (`mentionsAnyConst`, `nestOcc`, `piDomsOcc`), the
member lookup (`memberIdxAt?`), the input-derived fuel (`depth`,
`whnfWalkFuel`), the readback block (`fvMapAt`/`replaceFVarsGo`/
`replaceFVars`/`nestHoleImg` over the `FvMap` enum), the whole-application
abstraction (`phApp?`, `nestCanonSub`, `appHole?`, `replaceApps`), `nestPhs`
and the list/record helpers (`nestKeyMap`, `hiAt`, `rootHoles`, `nestHoleAt`,
`nestAcceptGroup`).

Every statement is `PSpec` (or `PSpecP` where the twin reads the `zeroLevel`
pin) with an exact answer.  The memo invariants are con-leche's
(`MentionsAnyMemoInv`, `NestOccMemoInv`, `ReplaceFVarsMemoInv`,
`ReplaceAppsMemoInv`) at handle keys through `denoteE`, as
`Bridge/Inductives/StructParts.lean`'s `MentionsMemoOK` is.

The module imports `Bridge/Inductives/Run.lean` only; the few run lemmas
`Bridge/Inductives/Rel.lean` also has (`zeroLevel_run`, `mkAppN_run`, …) are
restated in the `PW` namespace below, so that the two can be imported side by
side.
-/
import ConRon.Bridge.Inductives.Run
import ConRon.Bridge.ExprOps.TagFirst

namespace ConRon.Bridge.Inductives

set_option autoImplicit false
set_option mvcgen.warning false

open ConLeche ConRon.Arena ConRon.Bridge

namespace PW

/-! ## Local helpers (restated from `Bridge/Inductives/Rel.lean`, or new) -/

/-- con-leche: none — `Bridge/Inductives/Rel.lean`'s `zeroLevel_run`,
restated (that module is not in this one's import closure). -/
theorem zeroLevel_run {s s' : AState} {u : LIdx} (hp : PinsOK s)
    (hrun : Arena.zeroLevel s = .ok (u, s')) :
    s' = s ∧ denoteL s.store.ls u = some .zero := by
  simp only [Arena.zeroLevel] at hrun
  exact AM.of_run (P := fun t => t = s) rfl hrun (pinZeroLevel_spec s hp)

/-- con-leche: none — `internE` at an `.fvar`. -/
theorem internFVarE_run {s s' : AState} {k : Nat} {ty : EIdx} {tyP : Expr}
    {h : EIdx} (hok : StateOK s) (hty : denoteE s.store ty = some tyP)
    (hrun : internFVarE k ty s = .ok (h, s')) :
    PStep s s' ∧ denoteE s'.store h = some (.fvar k tyP) := by
  obtain ⟨hstep, hd⟩ := internE_run hok (viewOK_fvar (by rw [hty]; rfl)) hrun
  refine ⟨hstep, ?_⟩
  rw [hd]
  simp only [denoteEView, denote_ext hty hstep.ext, Option.map_some]

/-- con-leche: none — `internE` at a `.letE`. -/
theorem internLetEE_run {s s' : AState} {ty v b : EIdx} {tyP vP bP : Expr}
    {h : EIdx} (hok : StateOK s) (hty : denoteE s.store ty = some tyP)
    (hv : denoteE s.store v = some vP) (hb : denoteE s.store b = some bP)
    (hrun : internLetEE ty v b s = .ok (h, s')) :
    PStep s s' ∧ denoteE s'.store h = some (.letE tyP vP bP) := by
  obtain ⟨hstep, hd⟩ := internE_run hok
    (viewOK_letE (by rw [hty]; rfl) (by rw [hv]; rfl) (by rw [hb]; rfl)) hrun
  refine ⟨hstep, ?_⟩
  rw [hd]
  simp only [denoteEView, denote_ext hty hstep.ext, denote_ext hv hstep.ext,
    denote_ext hb hstep.ext, opt3]

/-- con-leche: none — the `Sort 0`-annotated free variable the canonical maps
build: `zeroLevel`, `internSortE`, `internFVarE`, in a row. -/
theorem fvarSort0_run {s s' : AState} {k : Nat} {h : EIdx} (hok : StateOK s)
    (hp : PinsOK s)
    (hrun : (do
      let z ← Arena.zeroLevel
      let so ← internSortE z
      internFVarE k so : AM EIdx) s = .ok (h, s')) :
    PStep s s' ∧ denoteE s'.store h = some (.fvar k (.sort .zero)) := by
  obtain ⟨z, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨rfl, hz⟩ := zeroLevel_run hp k1
  obtain ⟨so, s2, k2, z2⟩ := bindOk z1
  obtain ⟨p2, hso⟩ := internSortE_run hok hz k2
  obtain ⟨p3, hv⟩ := internFVarE_run p2.ok hso z2
  exact ⟨p2.trans p3, hv⟩

/-- con-leche: none — `Bridge/Inductives/Rel.lean`'s `mkAppN_run`,
restated. -/
theorem mkAppN_run : ∀ (args : List EIdx) (argsP : List Expr) {s s' : AState}
    {f : EIdx} {fP : Expr} {r : EIdx}, StateOK s →
    denoteE s.store f = some fP →
    Frontend.denoteEList s.store args = some argsP →
    ConRon.Arena.mkAppN f args s = .ok (r, s') →
    PStep s s' ∧ denoteE s'.store r = some (Expr.mkAppN fP argsP) := by
  intro args
  induction args with
  | nil =>
    intro argsP s s' f fP r hok hf hargs hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at hargs
    subst hargs
    simp only [ConRon.Arena.mkAppN, pure, StateT.pure, Except.pure] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ (Except.ok.inj hrun)
    exact ⟨PStep.refl hok, hf⟩
  | cons a as ih =>
    intro argsP s s' f fP r hok hf hargs hrun
    simp only [Frontend.denoteEList] at hargs
    cases ha : denoteE s.store a with
    | none => rw [ha] at hargs; simp at hargs
    | some x =>
      cases has : Frontend.denoteEList s.store as with
      | none => rw [ha, has] at hargs; simp at hargs
      | some xs =>
        rw [ha, has] at hargs
        obtain rfl := Option.some.inj hargs
        simp only [ConRon.Arena.mkAppN] at hrun
        obtain ⟨g, s₁, h1, h2⟩ := bindOk hrun
        obtain ⟨hstep1, hg⟩ := internAppE_run hok hf ha h1
        obtain ⟨hstep2, hr⟩ :=
          ih xs hstep1.ok hg (denoteEList_ext hstep1.ext _ _ has) h2
        exact ⟨hstep1.trans hstep2, hr⟩

/-- con-leche: none — `viewConst`, as a run. -/
theorem viewConst_run {s s' : AState} {h : EIdx} {r : Option (NIdx × LsIdx)}
    (hrun : viewConst h s = .ok (r, s')) : s' = s ∧ r = s.store.viewConst h :=
  AM.of_run (P := fun t => t = s) rfl hrun (viewConst_spec s h)

/-- con-leche: none — `viewApp`, as a run. -/
theorem viewApp_run {s s' : AState} {h : EIdx} {r : Option (EIdx × EIdx)}
    (hrun : viewApp h s = .ok (r, s')) : s' = s ∧ r = s.store.viewApp h :=
  AM.of_run (P := fun t => t = s) rfl hrun (viewApp_spec s h)

/-- con-leche: none — `viewFVarIdx`, as a run. -/
theorem viewFVarIdx_run {s s' : AState} {h : EIdx} {r : Option Nat}
    (hrun : viewFVarIdx h s = .ok (r, s')) : s' = s ∧ r = s.store.viewFVarIdx h :=
  AM.of_run (P := fun t => t = s) rfl hrun (viewFVarIdx_spec s h)

/-- con-leche: none — `viewBind`, as a run. -/
theorem viewBind_run {s s' : AState} {h : EIdx}
    {r : Option (EIdx × EIdx × BinderMeta)}
    (hrun : viewBind h s = .ok (r, s')) : s' = s ∧ r = s.store.viewBind h :=
  AM.of_run (P := fun t => t = s) rfl hrun (viewBind_spec s h)

/-- con-leche: none — a failing `failDanglingE` cannot have accepted. -/
theorem failDanglingE_ok {α : Type} {r : α} {s s' : AState}
    (h : (failDanglingE : AM α) s = .ok (r, s')) : False :=
  failOk h

/-- con-leche: none — **a denoting handle's tag is its view's**, with the
view's denotation. -/
theorem denote_view_tag {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr}
    (hd : denoteE st h = some e) :
    ∃ v, st.view h = some v ∧ h.tag = v.tagOf ∧ denoteEView st v = some e := by
  obtain ⟨v, hv⟩ := denoteE_view hd
  exact ⟨v, hv, EStore.tagOf_of_view hv, by rw [← denoteE_view_eq hwf hv]; exact hd⟩

theorem tag_const_of_denote {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {n : ConLeche.Name} {us : List Level}
    (hd : denoteE st h = some (.const n us)) : h.tag = ETag.const := by
  obtain ⟨v, _, ht, hv⟩ := denote_view_tag hwf hd
  rw [ht]
  cases v <;> simp_all [denoteEView, opt2_eq_some_iff, opt3_eq_some_iff] <;> rfl

theorem tag_app_of_denote {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {f a : Expr} (hd : denoteE st h = some (.app f a)) : h.tag = ETag.app := by
  obtain ⟨v, _, ht, hv⟩ := denote_view_tag hwf hd
  rw [ht]
  cases v <;> simp_all [denoteEView, opt2_eq_some_iff, opt3_eq_some_iff] <;> rfl

theorem tag_fvar_of_denote {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {k : Nat} {t : Expr} (hd : denoteE st h = some (.fvar k t)) :
    h.tag = ETag.fvar := by
  obtain ⟨v, _, ht, hv⟩ := denote_view_tag hwf hd
  rw [ht]
  cases v <;> simp_all [denoteEView, opt2_eq_some_iff, opt3_eq_some_iff] <;> rfl

theorem tag_forallE_of_denote {st : EStore} (hwf : StoreWF st) {h : EIdx}
    {d b : Expr} {m : BinderMeta} (hd : denoteE st h = some (.forallE d b m)) :
    h.tag = ETag.forallE := by
  obtain ⟨v, _, ht, hv⟩ := denote_view_tag hwf hd
  rw [ht]
  cases v <;> simp_all [denoteEView, opt2_eq_some_iff, opt3_eq_some_iff] <;> rfl

/-- con-leche: none — **a name-handle list's membership is the names'**,
through `beq_handle_eq` at each element. -/
theorem contains_handle_eq {st : EStore} (hwf : StoreWF st) {n : NIdx}
    {nm : ConLeche.Name} (hn : denoteN st.ns n = some nm) :
    ∀ {names : List NIdx} {namesP : List ConLeche.Name},
      Frontend.denoteNList st.ns names = some namesP →
      names.contains n = namesP.contains nm := by
  intro names
  induction names with
  | nil =>
    intro namesP h
    simp only [Frontend.denoteNList, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro namesP h
    simp only [Frontend.denoteNList] at h
    cases ha : denoteN st.ns a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : Frontend.denoteNList st.ns as with
      | none => rw [ha, has] at h; simp at h
      | some xs =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        simp only [List.contains_cons, beq_handle_eq hwf hn ha, ih has]

/-- con-leche: none — and so is its `findIdx?` lookup. -/
theorem findIdx_handle_eq {st : EStore} (hwf : StoreWF st) {n : NIdx}
    {nm : ConLeche.Name} (hn : denoteN st.ns n = some nm) :
    ∀ {names : List NIdx} {namesP : List ConLeche.Name},
      Frontend.denoteNList st.ns names = some namesP →
      names.findIdx? (· == n) = namesP.findIdx? (· == nm) := by
  intro names
  induction names with
  | nil =>
    intro namesP h
    simp only [Frontend.denoteNList, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro namesP h
    simp only [Frontend.denoteNList] at h
    cases ha : denoteN st.ns a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : Frontend.denoteNList st.ns as with
      | none => rw [ha, has] at h; simp at h
      | some xs =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        simp only [List.findIdx?_cons, beq_handle_eq hwf ha hn, ih has]

/-- con-leche: none — a denoting name-handle list has the names' length. -/
theorem denoteNList_length {st : NStore} :
    ∀ {names : List NIdx} {namesP : List ConLeche.Name},
      Frontend.denoteNList st names = some namesP → names.length = namesP.length := by
  intro names
  induction names with
  | nil =>
    intro namesP h
    simp only [Frontend.denoteNList, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro namesP h
    simp only [Frontend.denoteNList] at h
    cases ha : denoteN st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : Frontend.denoteNList st as with
      | none => rw [ha, has] at h; simp at h
      | some xs =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        simp [ih has]

/-- con-leche: none — a denoting name-handle list at an index. -/
theorem denoteNList_getElem? {st : NStore} :
    ∀ {names : List NIdx} {namesP : List ConLeche.Name},
      Frontend.denoteNList st names = some namesP → ∀ (j : Nat) (n : NIdx),
        names[j]? = some n → ∃ nm, namesP[j]? = some nm ∧ denoteN st n = some nm := by
  intro names
  induction names with
  | nil => intro namesP _ j n hj; simp at hj
  | cons a as ih =>
    intro namesP h j n hj
    simp only [Frontend.denoteNList] at h
    cases ha : denoteN st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : Frontend.denoteNList st as with
      | none => rw [ha, has] at h; simp at h
      | some xs =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          exact ⟨x, rfl, ha⟩
        | succ j =>
          simp only [List.getElem?_cons_succ] at hj ⊢
          exact ih has j n hj

/-- con-leche: none — a denoting expression-handle list has the terms'
length. -/
theorem denoteEList_length {st : EStore} :
    ∀ {hs : List EIdx} {xs : List Expr},
      Frontend.denoteEList st hs = some xs → hs.length = xs.length := by
  intro hs
  induction hs with
  | nil =>
    intro xs h
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro xs h
    simp only [Frontend.denoteEList] at h
    cases ha : denoteE st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : Frontend.denoteEList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        simp [ih has]

/-- con-leche: none — a denoting expression-handle list at an index, with the
`Option` carried both ways. -/
theorem denoteEList_getElem? {st : EStore} :
    ∀ {hs : List EIdx} {xs : List Expr},
      Frontend.denoteEList st hs = some xs → ∀ (j : Nat),
        (hs[j]? = none ↔ xs[j]? = none) ∧
        ∀ h, hs[j]? = some h → ∃ x, xs[j]? = some x ∧ denoteE st h = some x := by
  intro hs
  induction hs with
  | nil =>
    intro xs h j
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h
    simp
  | cons a as ih =>
    intro xs h j
    simp only [Frontend.denoteEList] at h
    cases ha : denoteE st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      cases has : Frontend.denoteEList st as with
      | none => rw [ha, has] at h; simp at h
      | some ys =>
        rw [ha, has] at h
        obtain rfl := Option.some.inj h
        cases j with
        | zero =>
          refine ⟨by simp, ?_⟩
          intro h' hj
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          exact ⟨x, rfl, ha⟩
        | succ j =>
          simp only [List.getElem?_cons_succ]
          exact ih has j

/-- con-leche: none — **a LEVEL-LIST-handle comparison is a structural
comparison**, at both signs: the interned list's handle is its identity
(`denoteLs_inj`, `Arena/WFProofs.lean`).  `memberIdxAt?` and `nestCanonSub`
compare a `const` node's level list against the block's this way. -/
theorem beq_lshandle_eq {st : EStore} (hwf : StoreWF st) {a b : LsIdx}
    {x y : List Level} (ha : denoteLs st.lss a = some x)
    (hb : denoteLs st.lss b = some y) : (a == b) = (x == y) := by
  obtain ⟨rk, hrk⟩ := hwf
  cases h1 : a == b with
  | true =>
    obtain rfl := eq_of_beq h1
    rw [ha] at hb
    obtain rfl := Option.some.inj hb
    simp
  | false =>
    symm
    rw [beq_eq_false_iff_ne]
    intro heq
    subst heq
    have hne : (a == b) = true := beq_iff_eq.mpr (denoteLs_inj hrk.lssWF ha hb)
    rw [h1] at hne
    exact absurd hne (by simp)

end PW

open PW

/-! ## `mentionsAnyConst` -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:62-64 MentionsAnyMemoInv
The handle-keyed memo of `mentionsAnyConst names`. -/
def MentionsAnyMemoOK (names : List ConLeche.Name) (tbl : Std.HashMap EIdx Bool)
    (st : EStore) : Prop :=
  ∀ (k : EIdx) (r : Bool), tbl[k]? = some r →
    ∃ e, denoteE st k = some e ∧ r = Expr.mentionsAnyConst names e

theorem MentionsAnyMemoOK.empty {names : List ConLeche.Name} {st : EStore} :
    MentionsAnyMemoOK names ∅ st := by
  intro k r h; simp at h

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:69-81
MentionsAnyMemoInv.insert -/
theorem MentionsAnyMemoOK.insert {names : List ConLeche.Name}
    {tbl : Std.HashMap EIdx Bool} {st : EStore} (hm : MentionsAnyMemoOK names tbl st)
    {h : EIdx} {hP : Expr} {r : Bool} (hd : denoteE st h = some hP)
    (heq : r = Expr.mentionsAnyConst names hP) :
    MentionsAnyMemoOK names (tbl.insert h r) st := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact ⟨hP, hd, heq⟩
  · exact hm k r' hk

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:84-119 Expr.mentionsAnyGo
The memoised walk computes the pure `mentionsAnyConst`.  The `.const` and
`.proj` arms test a name against the list: `contains_handle_eq`. -/
theorem mentionsAnyGo_spec (names : List NIdx) (namesP : List ConLeche.Name)
    (memo : Std.HashMap EIdx Bool) (fuel : Nat) (h : EIdx) (hP : Expr) :
    PSpec (fun st => Frontend.denoteNList st.ns names = some namesP ∧
        denoteE st h = some hP ∧ MentionsAnyMemoOK namesP memo st)
      (Arena.mentionsAnyGo names memo fuel h)
      (fun st r => r.1 = Expr.mentionsAnyConst namesP hP ∧
        MentionsAnyMemoOK namesP r.2 st) := by
  induction fuel generalizing memo h hP with
  | zero =>
    intro s₀ s' r hok _ hrun
    simp only [Arena.mentionsAnyGo] at hrun
    exact absurd hrun (fun hc => failOk hc)
  | succ fuel ih =>
    intro s₀ s' r hok hp hrun
    obtain ⟨hT, hd, hm⟩ := hp
    simp only [Arena.mentionsAnyGo] at hrun
    obtain ⟨v, s₁, hv, h2⟩ := bindOk hrun
    obtain ⟨hv0, hw⟩ := view_run hv
    rw [hv0] at h2
    have fin : ∀ {s₂ s₃ : AState} {b : Bool} {mm : Std.HashMap EIdx Bool}
        {r' : Bool × Std.HashMap EIdx Bool},
        PStep s₀ s₂ → b = Expr.mentionsAnyConst namesP hP →
        MentionsAnyMemoOK namesP mm s₂.store →
        (pure ((b, mm.insert h b) : Bool × Std.HashMap EIdx Bool) :
            AM (Bool × Std.HashMap EIdx Bool)) s₂ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ r'.1 = Expr.mentionsAnyConst namesP hP ∧
          MentionsAnyMemoOK namesP r'.2 s₃.store := by
      intro s₂ s₃ b mm r' hs hb hmm hz
      obtain ⟨rfl, rfl⟩ := pureOk hz
      exact ⟨hs, hb, MentionsAnyMemoOK.insert hmm (denote_ext hd hs.ext) hb⟩
    have hit : ∀ {s₃ : AState} {r₀ : Bool}
        {r' : Bool × Std.HashMap EIdx Bool},
        memo[h]? = some r₀ →
        (pure ((r₀, memo) : Bool × Std.HashMap EIdx Bool) :
            AM (Bool × Std.HashMap EIdx Bool)) s₀ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ r'.1 = Expr.mentionsAnyConst namesP hP ∧
          MentionsAnyMemoOK namesP r'.2 s₃.store := by
      intro s₃ r₀ r' hlk hz
      obtain ⟨rfl, rfl⟩ := pureOk hz
      obtain ⟨e, he, hre⟩ := hm h r₀ hlk
      obtain rfl := Option.some.inj (hd.symm.trans he)
      exact ⟨PStep.refl hok, hre, hm⟩
    cases v
    case bvar j =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain rfl := denote_bvar_inv hok.wf hw hd
      exact ⟨PStep.refl hok, rfl, hm⟩
    case sort u =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨l, rfl, _⟩ := denote_sort_inv hok.wf hw hd
      exact ⟨PStep.refl hok, rfl, hm⟩
    case lit l =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain rfl := denote_lit_inv hok.wf hw hd
      exact ⟨PStep.refl hok, rfl, hm⟩
    case const n us =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨nm, ls, rfl, hn, _⟩ := denote_const_inv hok.wf hw hd
      refine ⟨PStep.refl hok, ?_, hm⟩
      simp only [Expr.mentionsAnyConst]
      exact contains_handle_eq hok.wf hn hT
    case fvar k ty =>
      obtain ⟨t, rfl, hty⟩ := denote_fvar_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p, s₂, hin, hz⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p
        obtain ⟨hsA, hrA, hmA⟩ := ih memo ty t _ _ (b1, m1) hok ⟨hT, hty, hm⟩ hin
        exact fin hsA (by simp only [Expr.mentionsAnyConst]; exact hrA) hmA hz
    case app f a =>
      obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_app_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo f ef _ _ (b1, m1) hok ⟨hT, hf, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 a ea _ _ (b2, m2) hsA.ok
          ⟨denoteNListE_ext hsA.ext _ _ hT, denote_ext ha hsA.ext, hmA⟩ hc2
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn2
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin (hsA.trans hsB)
          (by simp only at hrA hrB; simp only [Expr.mentionsAnyConst, hrA, hrB]) hmB hz
    case lam ty b m =>
      obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_lam_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo ty et _ _ (b1, m1) hok ⟨hT, hty, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 b eb _ _ (b2, m2) hsA.ok
          ⟨denoteNListE_ext hsA.ext _ _ hT, denote_ext hbd hsA.ext, hmA⟩ hc2
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn2
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin (hsA.trans hsB)
          (by simp only at hrA hrB; simp only [Expr.mentionsAnyConst, hrA, hrB]) hmB hz
    case forallE ty b m =>
      obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_forallE_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo ty et _ _ (b1, m1) hok ⟨hT, hty, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 b eb _ _ (b2, m2) hsA.ok
          ⟨denoteNListE_ext hsA.ext _ _ hT, denote_ext hbd hsA.ext, hmA⟩ hc2
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn2
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin (hsA.trans hsB)
          (by simp only at hrA hrB; simp only [Expr.mentionsAnyConst, hrA, hrB]) hmB hz
    case letE lt lv lb =>
      obtain ⟨et, ev, eb, rfl, hty, hval, hbd⟩ := denote_letE_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo lt et _ _ (b1, m1) hok ⟨hT, hty, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 lv ev _ _ (b2, m2) hsA.ok
          ⟨denoteNListE_ext hsA.ext _ _ hT, denote_ext hval hsA.ext, hmA⟩ hc2
        obtain ⟨p3, sc, hc3, hn3⟩ := bindOk hn2
        obtain ⟨b3, m3⟩ := p3
        obtain ⟨hsC, hrC, hmC⟩ := ih m2 lb eb _ _ (b3, m3) hsB.ok
          ⟨denoteNListE_ext (hsA.ext.trans hsB.ext) _ _ hT,
           denote_ext hbd (hsA.ext.trans hsB.ext), hmB⟩ hc3
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn3
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin ((hsA.trans hsB).trans hsC)
          (by simp only at hrA hrB hrC; simp only [Expr.mentionsAnyConst, hrA, hrB, hrC])
          hmC hz
    case proj pn pk psub =>
      obtain ⟨nm, es, rfl, hn, hsub⟩ := denote_proj_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo psub es _ _ (b1, m1) hok ⟨hT, hsub, hm⟩ hc1
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn1
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin hsA
          (by simp only at hrA
              simp only [Expr.mentionsAnyConst, hrA, contains_handle_eq hok.wf hn hT])
          hmA hz

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:192-194 Expr.mentionsAnyConstFast
The entry, at an empty memo: the pure `mentionsAnyConst` (con-leche's
`@[csimp]` swaps the memoised walk in; the pure definition is the spec). -/
theorem mentionsAnyConst_spec (names : List NIdx) (namesP : List ConLeche.Name)
    (e : EIdx) (eP : Expr) :
    PSpec (fun st => Frontend.denoteNList st.ns names = some namesP ∧
        denoteE st e = some eP)
      (Arena.mentionsAnyConst names e) (RV (Expr.mentionsAnyConst namesP eP)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hT, hd⟩ := hp
  simp only [Arena.mentionsAnyConst] at hrun
  obtain ⟨q, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep, hr, _⟩ :=
    mentionsAnyGo_spec names namesP ∅ Arena.coreWalkFuel e eP s₀ s₁ q hok
      ⟨hT, hd, MentionsAnyMemoOK.empty⟩ h1
  obtain ⟨rfl, rfl⟩ := pureOk h2
  exact ⟨hstep, hr⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:201-207 memberIdxAt?
The member a head names at the block's levels: the level lists compare by
handle (`beq_lshandle_eq`), the names by `findIdx_handle_eq`. -/
theorem memberIdxAt?_spec (names : List NIdx) (namesP : List ConLeche.Name)
    (lvls : LsIdx) (lvlsP : List Level) (e : EIdx) (eP : Expr) :
    PSpec (fun st => Frontend.denoteNList st.ns names = some namesP ∧
        denoteLs st.lss lvls = some lvlsP ∧ denoteE st e = some eP)
      (Arena.memberIdxAt? names lvls e) (RV (ConLeche.memberIdxAt? namesP lvlsP eP)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hN, hL, hd⟩ := hp
  simp only [Arena.memberIdxAt?] at hrun
  by_cases htg : (e.tag == ETag.const) = true
  · rw [if_pos htg] at hrun
    obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨hs1, ho⟩ := viewConst_run h1
    subst hs1
    cases o with
    | none => exact absurd h2 (fun hc => failDanglingE_ok hc)
    | some p =>
      obtain ⟨n, us⟩ := p
      have hw := view_of_viewConst_tag htg ho.symm
      obtain ⟨nm, ls, rfl, hn, hls⟩ := denote_const_inv hok.wf hw hd
      dsimp only at h2
      have hb' := beq_lshandle_eq hok.wf hls hL
      by_cases hb : (us == lvls) = true
      · rw [if_pos hb] at h2
        obtain ⟨rfl, rfl⟩ := pureOk h2
        refine ⟨PStep.refl hok, ?_⟩
        rw [hb'] at hb
        show _ = ConLeche.memberIdxAt? namesP lvlsP (.const nm ls)
        simp only [ConLeche.memberIdxAt?, hb, if_true]
        exact findIdx_handle_eq hok.wf hn hN
      · rw [if_neg hb] at h2
        obtain ⟨rfl, rfl⟩ := pureOk h2
        refine ⟨PStep.refl hok, ?_⟩
        rw [hb'] at hb
        show _ = ConLeche.memberIdxAt? namesP lvlsP (.const nm ls)
        simp only [ConLeche.memberIdxAt?, hb]
        rfl
  · rw [if_neg htg] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨PStep.refl hok, ?_⟩
    show none = ConLeche.memberIdxAt? namesP lvlsP eP
    cases eP with
    | const c us => exact absurd (tag_const_of_denote hok.wf hd) (by simpa using htg)
    | _ => rfl

/-! ## `nestOcc` -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:379-380 NestOccMemoInv
The handle-keyed memo of `nestOcc names lo hi`. -/
def NestOccMemoOK (names : List ConLeche.Name) (lo hi : Nat)
    (tbl : Std.HashMap EIdx Bool) (st : EStore) : Prop :=
  ∀ (k : EIdx) (r : Bool), tbl[k]? = some r →
    ∃ e, denoteE st k = some e ∧ r = Expr.nestOcc names lo hi e

theorem NestOccMemoOK.empty {names : List ConLeche.Name} {lo hi : Nat} {st : EStore} :
    NestOccMemoOK names lo hi ∅ st := by
  intro k r h; simp at h

theorem NestOccMemoOK.insert {names : List ConLeche.Name} {lo hi : Nat}
    {tbl : Std.HashMap EIdx Bool} {st : EStore} (hm : NestOccMemoOK names lo hi tbl st)
    {h : EIdx} {hP : Expr} {r : Bool} (hd : denoteE st h = some hP)
    (heq : r = Expr.nestOcc names lo hi hP) :
    NestOccMemoOK names lo hi (tbl.insert h r) st := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact ⟨hP, hd, heq⟩
  · exact hm k r' hk

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:347-377 Expr.nestOccGo
The memoised, short-circuiting walk computes the pure `nestOcc`. -/
theorem nestOccGo_spec (names : List NIdx) (namesP : List ConLeche.Name) (lo hi : Nat)
    (memo : Std.HashMap EIdx Bool) (fuel : Nat) (h : EIdx) (hP : Expr) :
    PSpec (fun st => Frontend.denoteNList st.ns names = some namesP ∧
        denoteE st h = some hP ∧ NestOccMemoOK namesP lo hi memo st)
      (Arena.nestOccGo names lo hi memo fuel h)
      (fun st r => r.1 = Expr.nestOcc namesP lo hi hP ∧
        NestOccMemoOK namesP lo hi r.2 st) := by
  induction fuel generalizing memo h hP with
  | zero =>
    intro s₀ s' r hok _ hrun
    simp only [Arena.nestOccGo] at hrun
    exact absurd hrun (fun hc => failOk hc)
  | succ fuel ih =>
    intro s₀ s' r hok hp hrun
    obtain ⟨hT, hd, hm⟩ := hp
    simp only [Arena.nestOccGo] at hrun
    obtain ⟨v, s₁, hv, h2⟩ := bindOk hrun
    obtain ⟨hv0, hw⟩ := view_run hv
    rw [hv0] at h2
    have fin : ∀ {s₂ s₃ : AState} {b : Bool} {mm : Std.HashMap EIdx Bool}
        {r' : Bool × Std.HashMap EIdx Bool},
        PStep s₀ s₂ → b = Expr.nestOcc namesP lo hi hP →
        NestOccMemoOK namesP lo hi mm s₂.store →
        (pure ((b, mm.insert h b) : Bool × Std.HashMap EIdx Bool) :
            AM (Bool × Std.HashMap EIdx Bool)) s₂ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ r'.1 = Expr.nestOcc namesP lo hi hP ∧
          NestOccMemoOK namesP lo hi r'.2 s₃.store := by
      intro s₂ s₃ b mm r' hs hb hmm hz
      obtain ⟨rfl, rfl⟩ := pureOk hz
      exact ⟨hs, hb, NestOccMemoOK.insert hmm (denote_ext hd hs.ext) hb⟩
    have hit : ∀ {s₃ : AState} {r₀ : Bool}
        {r' : Bool × Std.HashMap EIdx Bool},
        memo[h]? = some r₀ →
        (pure ((r₀, memo) : Bool × Std.HashMap EIdx Bool) :
            AM (Bool × Std.HashMap EIdx Bool)) s₀ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ r'.1 = Expr.nestOcc namesP lo hi hP ∧
          NestOccMemoOK namesP lo hi r'.2 s₃.store := by
      intro s₃ r₀ r' hlk hz
      obtain ⟨rfl, rfl⟩ := pureOk hz
      obtain ⟨e, he, hre⟩ := hm h r₀ hlk
      obtain rfl := Option.some.inj (hd.symm.trans he)
      exact ⟨PStep.refl hok, hre, hm⟩
    cases v
    case bvar j =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain rfl := denote_bvar_inv hok.wf hw hd
      exact ⟨PStep.refl hok, rfl, hm⟩
    case sort u =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨l, rfl, _⟩ := denote_sort_inv hok.wf hw hd
      exact ⟨PStep.refl hok, rfl, hm⟩
    case lit l =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain rfl := denote_lit_inv hok.wf hw hd
      exact ⟨PStep.refl hok, rfl, hm⟩
    case fvar k ty =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨t, rfl, _⟩ := denote_fvar_inv hok.wf hw hd
      refine ⟨PStep.refl hok, ?_, hm⟩
      simp [Expr.nestOcc]
    case const n us =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨nm, ls, rfl, hn, _⟩ := denote_const_inv hok.wf hw hd
      refine ⟨PStep.refl hok, ?_, hm⟩
      simp only [Expr.nestOcc]
      exact contains_handle_eq hok.wf hn hT
    case app f a =>
      obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_app_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo f ef _ _ (b1, m1) hok ⟨hT, hf, hm⟩ hc1
        simp only at hrA
        cases b1
        · simp only [Bool.false_eq_true, if_false] at hn1
          obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
          obtain ⟨b2, m2⟩ := p2
          obtain ⟨hsB, hrB, hmB⟩ := ih m1 a ea _ _ (b2, m2) hsA.ok
            ⟨denoteNListE_ext hsA.ext _ _ hT, denote_ext ha hsA.ext, hmA⟩ hc2
          simp only at hrB
          exact fin (hsA.trans hsB) (by simp only [Expr.nestOcc, ← hrA, ← hrB]; rfl) hmB hn2
        · simp only [if_true] at hn1
          obtain ⟨y, sy, hy, hz⟩ := bindOk hn1
          obtain ⟨rfl, rfl⟩ := pureOk hy
          exact fin hsA (by simp only [Expr.nestOcc, ← hrA]; rfl) hmA hz
    case lam ty b m =>
      obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_lam_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo ty et _ _ (b1, m1) hok ⟨hT, hty, hm⟩ hc1
        simp only at hrA
        cases b1
        · simp only [Bool.false_eq_true, if_false] at hn1
          obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
          obtain ⟨b2, m2⟩ := p2
          obtain ⟨hsB, hrB, hmB⟩ := ih m1 b eb _ _ (b2, m2) hsA.ok
            ⟨denoteNListE_ext hsA.ext _ _ hT, denote_ext hbd hsA.ext, hmA⟩ hc2
          simp only at hrB
          exact fin (hsA.trans hsB) (by simp only [Expr.nestOcc, ← hrA, ← hrB]; rfl) hmB hn2
        · simp only [if_true] at hn1
          obtain ⟨y, sy, hy, hz⟩ := bindOk hn1
          obtain ⟨rfl, rfl⟩ := pureOk hy
          exact fin hsA (by simp only [Expr.nestOcc, ← hrA]; rfl) hmA hz
    case forallE ty b m =>
      obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_forallE_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo ty et _ _ (b1, m1) hok ⟨hT, hty, hm⟩ hc1
        simp only at hrA
        cases b1
        · simp only [Bool.false_eq_true, if_false] at hn1
          obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
          obtain ⟨b2, m2⟩ := p2
          obtain ⟨hsB, hrB, hmB⟩ := ih m1 b eb _ _ (b2, m2) hsA.ok
            ⟨denoteNListE_ext hsA.ext _ _ hT, denote_ext hbd hsA.ext, hmA⟩ hc2
          simp only at hrB
          exact fin (hsA.trans hsB) (by simp only [Expr.nestOcc, ← hrA, ← hrB]; rfl) hmB hn2
        · simp only [if_true] at hn1
          obtain ⟨y, sy, hy, hz⟩ := bindOk hn1
          obtain ⟨rfl, rfl⟩ := pureOk hy
          exact fin hsA (by simp only [Expr.nestOcc, ← hrA]; rfl) hmA hz
    case letE lt lv lb =>
      obtain ⟨et, ev, eb, rfl, hty, hval, hbd⟩ := denote_letE_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo lt et _ _ (b1, m1) hok ⟨hT, hty, hm⟩ hc1
        simp only at hrA
        cases b1
        · simp only [Bool.false_eq_true, if_false] at hn1
          obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
          obtain ⟨b2, m2⟩ := p2
          obtain ⟨hsB, hrB, hmB⟩ := ih m1 lv ev _ _ (b2, m2) hsA.ok
            ⟨denoteNListE_ext hsA.ext _ _ hT, denote_ext hval hsA.ext, hmA⟩ hc2
          simp only at hrB
          cases b2
          · simp only [Bool.false_eq_true, if_false] at hn2
            obtain ⟨p3, sc, hc3, hn3⟩ := bindOk hn2
            obtain ⟨b3, m3⟩ := p3
            obtain ⟨hsC, hrC, hmC⟩ := ih m2 lb eb _ _ (b3, m3) hsB.ok
              ⟨denoteNListE_ext (hsA.ext.trans hsB.ext) _ _ hT,
               denote_ext hbd (hsA.ext.trans hsB.ext), hmB⟩ hc3
            simp only at hrC
            exact fin ((hsA.trans hsB).trans hsC)
              (by simp only [Expr.nestOcc, ← hrA, ← hrB, ← hrC]; rfl) hmC hn3
          · simp only [if_true] at hn2
            obtain ⟨y, sy, hy, hz⟩ := bindOk hn2
            obtain ⟨rfl, rfl⟩ := pureOk hy
            exact fin (hsA.trans hsB) (by simp only [Expr.nestOcc, ← hrA, ← hrB]; rfl) hmB hz
        · simp only [if_true] at hn1
          obtain ⟨y, sy, hy, hz⟩ := bindOk hn1
          obtain ⟨rfl, rfl⟩ := pureOk hy
          exact fin hsA (by simp only [Expr.nestOcc, ← hrA]; rfl) hmA hz
    case proj pn pk psub =>
      obtain ⟨nm, es, rfl, hn, hsub⟩ := denote_proj_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo psub es _ _ (b1, m1) hok ⟨hT, hsub, hm⟩ hc1
        simp only at hrA
        exact fin hsA (by simp only [Expr.nestOcc, ← hrA]) hmA hn1

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:506-508 Expr.nestOccFast
The entry, at an empty memo: the pure `nestOcc`. -/
theorem nestOcc_spec (names : List NIdx) (namesP : List ConLeche.Name) (lo hi : Nat)
    (e : EIdx) (eP : Expr) :
    PSpec (fun st => Frontend.denoteNList st.ns names = some namesP ∧
        denoteE st e = some eP)
      (Arena.nestOcc names lo hi e) (RV (Expr.nestOcc namesP lo hi eP)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hT, hd⟩ := hp
  simp only [Arena.nestOcc] at hrun
  obtain ⟨q, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep, hr, _⟩ :=
    nestOccGo_spec names namesP lo hi ∅ Arena.coreWalkFuel e eP s₀ s₁ q hok
      ⟨hT, hd, NestOccMemoOK.empty⟩ h1
  obtain ⟨rfl, rfl⟩ := pureOk h2
  exact ⟨hstep, hr⟩

/-! ## `piDomsOcc` -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1543-1548 Expr.piDomsOcc
The first `n` binder domains, each through `nestOcc`. -/
theorem piDomsOcc_spec (names : List NIdx) (namesP : List ConLeche.Name) (lo hi : Nat) :
    ∀ (n : Nat) (e : EIdx) (eP : Expr),
    PSpec (fun st => Frontend.denoteNList st.ns names = some namesP ∧
        denoteE st e = some eP)
      (Arena.piDomsOcc names lo hi n e) (RV (Expr.piDomsOcc namesP lo hi n eP)) := by
  intro n
  induction n with
  | zero =>
    intro e eP s₀ s' r hok _ hrun
    simp only [Arena.piDomsOcc] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | succ n ih =>
    intro e eP s₀ s' r hok hp hrun
    obtain ⟨hT, hd⟩ := hp
    simp only [Arena.piDomsOcc] at hrun
    by_cases htg : (e.tag == ETag.forallE) = true
    · rw [if_pos htg] at hrun
      obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
      obtain ⟨hs1, ho⟩ := viewBind_run h1
      rw [hs1] at h2
      cases o with
      | none => exact absurd h2 (fun hc => failDanglingE_ok hc)
      | some p =>
        obtain ⟨d, b, m⟩ := p
        have hw := view_of_viewBind_tag_forallE htg ho.symm
        obtain ⟨dP, bP, rfl, hdd, hbd⟩ := denote_forallE_inv hok.wf hw hd
        dsimp only at h2
        obtain ⟨c, s₂, h3, h4⟩ := bindOk h2
        obtain ⟨p3, hc⟩ := nestOcc_spec names namesP lo hi d dP s₀ s₂ c hok ⟨hT, hdd⟩ h3
        simp only [RV] at hc
        subst hc
        by_cases hb : Expr.nestOcc namesP lo hi dP = true
        · rw [if_pos hb] at h4
          obtain ⟨rfl, rfl⟩ := pureOk h4
          exact ⟨p3, by simp [Expr.piDomsOcc, hb]⟩
        · rw [if_neg hb] at h4
          obtain ⟨p4, h5⟩ := ih b bP s₂ s' r p3.ok
            ⟨denoteNListE_ext p3.ext _ _ hT, denote_ext hbd p3.ext⟩ h4
          refine ⟨p3.trans p4, ?_⟩
          simp only [RV] at h5
          simp [Expr.piDomsOcc, hb, h5]
    · rw [if_neg htg] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      refine ⟨PStep.refl hok, ?_⟩
      show false = Expr.piDomsOcc namesP lo hi (n + 1) eP
      cases eP with
      | forallE d b m => exact absurd (tag_forallE_of_denote hok.wf hd) (by simpa using htg)
      | _ => rfl

/-! ## The input-derived fuel: `depth`, `whnfWalkFuel`

con-leche's `Expr.depth` IS its memoised walk (`(e.depthGo {}).1`, no pure
twin), so the reference here is a structural `depthS`, and both walks —
con-leche's on terms, the twin's on handles — are shown to compute it. -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:556-592 Expr.depth —
the depth the memoised walk computes, as a structural function: the longest
root-to-leaf path, `fvar` annotations not descended. -/
def depthS : Expr → Nat
  | .app f a => max (depthS f) (depthS a) + 1
  | .lam ty b _ => max (depthS ty) (depthS b) + 1
  | .forallE ty b _ => max (depthS ty) (depthS b) + 1
  | .letE ty v b => max (max (depthS ty) (depthS v)) (depthS b) + 1
  | .proj _ _ x => depthS x + 1
  | _ => 1

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:556-588 Expr.depthGo —
the memo invariant on con-leche's own walk. -/
def DepthMemoInv (memo : Std.HashMap Expr Nat) : Prop :=
  ∀ (k : Expr) (r : Nat), memo[k]? = some r → r = depthS k

theorem DepthMemoInv.insert {memo : Std.HashMap Expr Nat} (hm : DepthMemoInv memo)
    {e : Expr} {r : Nat} (heq : r = depthS e) : DepthMemoInv (memo.insert e r) := by
  intro e' r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm e' r' hk

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:556-588 Expr.depthGo —
**con-leche's memoised walk computes `depthS`**. -/
theorem depthGo_pure_spec :
    ∀ (e : Expr) (memo : Std.HashMap Expr Nat), DepthMemoInv memo →
      (Expr.depthGo memo e).1 = depthS e ∧ DepthMemoInv (Expr.depthGo memo e).2 := by
  intro e
  induction e with
  | bvar i => intro memo hm; exact ⟨rfl, hm⟩
  | sort u => intro memo hm; exact ⟨rfl, hm⟩
  | const n us => intro memo hm; exact ⟨rfl, hm⟩
  | lit l => intro memo hm; exact ⟨rfl, hm⟩
  | fvar i ty _ => intro memo hm; exact ⟨rfl, hm⟩
  | app a b iha ihb =>
    intro memo hm
    rw [Expr.depthGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iha memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [depthS, h1, h3], ?_⟩
      exact h4.insert (by simp [depthS, h1, h3])
  | lam ty body bi iht ihb =>
    intro memo hm
    rw [Expr.depthGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [depthS, h1, h3], ?_⟩
      exact h4.insert (by simp [depthS, h1, h3])
  | forallE ty body bi iht ihb =>
    intro memo hm
    rw [Expr.depthGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      refine ⟨by simp [depthS, h1, h3], ?_⟩
      exact h4.insert (by simp [depthS, h1, h3])
  | letE ty val body iht ihv ihb =>
    intro memo hm
    rw [Expr.depthGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihv _ h2
      obtain ⟨h5, h6⟩ := ihb _ h4
      refine ⟨by simp [depthS, h1, h3, h5], ?_⟩
      exact h6.insert (by simp [depthS, h1, h3, h5])
  | proj s i sub ih =>
    intro memo hm
    rw [Expr.depthGo]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := ih memo hm
      refine ⟨by simp [depthS, h1], ?_⟩
      exact h2.insert (by simp [depthS, h1])

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:590-592 Expr.depth —
con-leche's depth IS the structural one. -/
theorem depth_eq_depthS (e : Expr) : Expr.depth e = depthS e :=
  (depthGo_pure_spec e {} (fun k r h => by simp at h)).1

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:556-588 Expr.depthGo —
the twin's handle-keyed memo. -/
def DepthMemoOK (tbl : Std.HashMap EIdx Nat) (st : EStore) : Prop :=
  ∀ (k : EIdx) (r : Nat), tbl[k]? = some r → ∃ e, denoteE st k = some e ∧ r = depthS e

theorem DepthMemoOK.empty {st : EStore} : DepthMemoOK ∅ st := by
  intro k r h; simp at h

theorem DepthMemoOK.insert {tbl : Std.HashMap EIdx Nat} {st : EStore}
    (hm : DepthMemoOK tbl st) {h : EIdx} {hP : Expr} {r : Nat}
    (hd : denoteE st h = some hP) (heq : r = depthS hP) :
    DepthMemoOK (tbl.insert h r) st := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact ⟨hP, hd, heq⟩
  · exact hm k r' hk

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:556-588 Expr.depthGo
The twin's memoised walk computes `depthS`. -/
theorem depthGo_spec (memo : Std.HashMap EIdx Nat) (fuel : Nat) (h : EIdx) (hP : Expr) :
    PSpec (fun st => denoteE st h = some hP ∧ DepthMemoOK memo st)
      (Arena.depthGo memo fuel h)
      (fun st r => r.1 = depthS hP ∧ DepthMemoOK r.2 st) := by
  induction fuel generalizing memo h hP with
  | zero =>
    intro s₀ s' r hok _ hrun
    simp only [Arena.depthGo] at hrun
    exact absurd hrun (fun hc => failOk hc)
  | succ fuel ih =>
    intro s₀ s' r hok hp hrun
    obtain ⟨hd, hm⟩ := hp
    simp only [Arena.depthGo] at hrun
    obtain ⟨v, s₁, hv, h2⟩ := bindOk hrun
    obtain ⟨hv0, hw⟩ := view_run hv
    rw [hv0] at h2
    have fin : ∀ {s₂ s₃ : AState} {b : Nat} {mm : Std.HashMap EIdx Nat}
        {r' : Nat × Std.HashMap EIdx Nat},
        PStep s₀ s₂ → b = depthS hP → DepthMemoOK mm s₂.store →
        (pure ((b, mm.insert h b) : Nat × Std.HashMap EIdx Nat) :
            AM (Nat × Std.HashMap EIdx Nat)) s₂ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ r'.1 = depthS hP ∧ DepthMemoOK r'.2 s₃.store := by
      intro s₂ s₃ b mm r' hs hb hmm hz
      obtain ⟨rfl, rfl⟩ := pureOk hz
      exact ⟨hs, hb, DepthMemoOK.insert hmm (denote_ext hd hs.ext) hb⟩
    have hit : ∀ {s₃ : AState} {r₀ : Nat} {r' : Nat × Std.HashMap EIdx Nat},
        memo[h]? = some r₀ →
        (pure ((r₀, memo) : Nat × Std.HashMap EIdx Nat) :
            AM (Nat × Std.HashMap EIdx Nat)) s₀ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ r'.1 = depthS hP ∧ DepthMemoOK r'.2 s₃.store := by
      intro s₃ r₀ r' hlk hz
      obtain ⟨rfl, rfl⟩ := pureOk hz
      obtain ⟨e, he, hre⟩ := hm h r₀ hlk
      obtain rfl := Option.some.inj (hd.symm.trans he)
      exact ⟨PStep.refl hok, hre, hm⟩
    cases v
    case bvar j =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain rfl := denote_bvar_inv hok.wf hw hd
      exact ⟨PStep.refl hok, rfl, hm⟩
    case fvar k ty =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨t, rfl, _⟩ := denote_fvar_inv hok.wf hw hd
      exact ⟨PStep.refl hok, rfl, hm⟩
    case sort u =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨l, rfl, _⟩ := denote_sort_inv hok.wf hw hd
      exact ⟨PStep.refl hok, rfl, hm⟩
    case const n us =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hok.wf hw hd
      exact ⟨PStep.refl hok, rfl, hm⟩
    case lit l =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain rfl := denote_lit_inv hok.wf hw hd
      exact ⟨PStep.refl hok, rfl, hm⟩
    case app f a =>
      obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_app_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo f ef _ _ (b1, m1) hok ⟨hf, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 a ea _ _ (b2, m2) hsA.ok
          ⟨denote_ext ha hsA.ext, hmA⟩ hc2
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn2
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin (hsA.trans hsB)
          (by simp only at hrA hrB; simp only [depthS, hrA, hrB]) hmB hz
    case lam ty b m =>
      obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_lam_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo ty et _ _ (b1, m1) hok ⟨hty, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 b eb _ _ (b2, m2) hsA.ok
          ⟨denote_ext hbd hsA.ext, hmA⟩ hc2
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn2
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin (hsA.trans hsB)
          (by simp only at hrA hrB; simp only [depthS, hrA, hrB]) hmB hz
    case forallE ty b m =>
      obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_forallE_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo ty et _ _ (b1, m1) hok ⟨hty, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 b eb _ _ (b2, m2) hsA.ok
          ⟨denote_ext hbd hsA.ext, hmA⟩ hc2
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn2
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin (hsA.trans hsB)
          (by simp only at hrA hrB; simp only [depthS, hrA, hrB]) hmB hz
    case letE lt lv lb =>
      obtain ⟨et, ev, eb, rfl, hty, hval, hbd⟩ := denote_letE_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo lt et _ _ (b1, m1) hok ⟨hty, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 lv ev _ _ (b2, m2) hsA.ok
          ⟨denote_ext hval hsA.ext, hmA⟩ hc2
        obtain ⟨p3, sc, hc3, hn3⟩ := bindOk hn2
        obtain ⟨b3, m3⟩ := p3
        obtain ⟨hsC, hrC, hmC⟩ := ih m2 lb eb _ _ (b3, m3) hsB.ok
          ⟨denote_ext hbd (hsA.ext.trans hsB.ext), hmB⟩ hc3
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn3
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin ((hsA.trans hsB).trans hsC)
          (by simp only at hrA hrB hrC; simp only [depthS, hrA, hrB, hrC]) hmC hz
    case proj pn pk psub =>
      obtain ⟨nm, es, rfl, hn, hsub⟩ := denote_proj_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo psub es _ _ (b1, m1) hok ⟨hsub, hm⟩ hc1
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn1
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin hsA (by simp only at hrA; simp only [depthS, hrA]) hmA hz

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:590-592 Expr.depth
A term's depth: con-leche's memoised `Expr.depth`, exactly. -/
theorem depth_spec (e : EIdx) (eP : Expr) :
    PSpec (fun st => denoteE st e = some eP) (Arena.depth e) (RV (Expr.depth eP)) := by
  intro s₀ s' r hok hd hrun
  simp only [Arena.depth] at hrun
  obtain ⟨q, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep, hr, _⟩ :=
    depthGo_spec ∅ Arena.coreWalkFuel e eP s₀ s₁ q hok ⟨hd, DepthMemoOK.empty⟩ h1
  obtain ⟨rfl, rfl⟩ := pureOk h2
  exact ⟨hstep, by simp only [RV, depth_eq_depthS]; exact hr⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:594-596 whnfWalkFuel
The fuel of a walk through whnf: `depth + fuelSlack`, exactly. -/
theorem whnfWalkFuel_spec (e : EIdx) (eP : Expr) :
    PSpec (fun st => denoteE st e = some eP) (Arena.whnfWalkFuel e)
      (RV (ConLeche.whnfWalkFuel eP)) := by
  intro s₀ s' r hok hd hrun
  simp only [Arena.whnfWalkFuel] at hrun
  obtain ⟨d, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep, hr⟩ := depth_spec e eP s₀ s₁ d hok hd h1
  obtain ⟨rfl, rfl⟩ := pureOk h2
  simp only [RV] at hr
  exact ⟨hstep, by simp only [RV, ConLeche.whnfWalkFuel, hr]; rfl⟩

end ConRon.Bridge.Inductives

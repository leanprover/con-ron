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

/-- con-leche: none — the `fvar` index projection read means the type
projection reads too (one row of the `fvar` array): `TagFirst`'s
`viewFVarIdx_of_viewFVarTy`, the other way. -/
theorem viewFVarTy_of_viewFVarIdx {st : EStore} {i : EIdx} {k : Nat}
    (h : st.viewFVarIdx i = some k) : ∃ ty, st.viewFVarTy i = some ty := by
  unfold EStore.viewFVarIdx at h
  unfold EStore.viewFVarTy EStore.persGetFVarTy
  unfold EStore.persGetFVarIdx at h
  split at h
  · simp only [ETables.getFVarIdx, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, -⟩ := h
    exact ⟨r.ty, by simp [*, ETables.getFVarTy]⟩
  · split at h
    · simp only [ETables.getFVarIdx, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, -⟩ := h
      exact ⟨r.ty, by simp [*, ETables.getFVarTy]⟩
    · cases h

/-- con-leche: none — an `fvar`-tagged handle's index projection, with its
denotation: the term is that free variable. -/
theorem denote_of_viewFVarIdx {st : EStore} (hwf : StoreWF st) {a : EIdx} {j : Nat}
    {aP : Expr} (htg : (a.tag == ETag.fvar) = true) (hj : st.viewFVarIdx a = some j)
    (hd : denoteE st a = some aP) : ∃ t, aP = .fvar j t := by
  obtain ⟨ty, hty⟩ := viewFVarTy_of_viewFVarIdx hj
  have hw := view_of_viewFVar_tag htg hj hty
  obtain ⟨t, rfl, _⟩ := denote_fvar_inv hwf hw hd
  exact ⟨t, rfl⟩

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

/-! ## The records, read: `dCtx`, `dProg`, `nestKeyMap` -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:643-654 NestCtx —
`dCtx` taken apart. -/
theorem dCtx_inv {st : EStore} {fnd : ConLeche.Name → Option ConstantInfo}
    {c : Arena.NestCtx} {cP : ConLeche.NestCtx} (h : dCtx st fnd c = some cP) :
    ∃ namesP lpsP paramsP sortP,
      cP = ⟨namesP, lpsP, c.nP, c.nIdxs, paramsP, sortP, fnd⟩ ∧
      Frontend.denoteNList st.ns c.names = some namesP ∧
      Frontend.denoteNList st.ns c.lps = some lpsP ∧
      Frontend.denoteEList st c.params = some paramsP ∧
      denoteL st.ls c.sort = some sortP ∧
      denoteLs st.lss c.lvls = some (lpsP.map .param) := by
  simp only [dCtx] at h
  cases h1 : Frontend.denoteNList st.ns c.names with
  | none => rw [h1] at h; exact nomatch h
  | some a =>
  cases h2 : Frontend.denoteNList st.ns c.lps with
  | none => rw [h1, h2] at h; exact nomatch h
  | some b =>
  cases h3 : Frontend.denoteEList st c.params with
  | none => rw [h1, h2, h3] at h; exact nomatch h
  | some p =>
  cases h4 : denoteL st.ls c.sort with
  | none => rw [h1, h2, h3, h4] at h; exact nomatch h
  | some so =>
  cases h5 : denoteLs st.lss c.lvls with
  | none => rw [h1, h2, h3, h4, h5] at h; exact nomatch h
  | some l =>
  rw [h1, h2, h3, h4, h5] at h
  simp only [Option.bind_eq_bind, Option.bind_some] at h
  split at h
  · rename_i hl
    subst hl
    exact ⟨a, b, p, so, (Option.some.inj h).symm, rfl, rfl, rfl, rfl, rfl⟩
  · exact nomatch h

/-- con-leche: none — `Option`'s `mapM` keeps the length. -/
theorem mapM_option_length {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ys.length = xs.length := by
  intro xs
  induction xs with
  | nil => intro ys h; simp only [List.mapM_nil] at h; cases h; rfl
  | cons x xs ih =>
    intro ys h
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hx : f x with
    | none => rw [hx] at h; simp at h
    | some y =>
      rw [hx] at h
      cases hxs : xs.mapM f with
      | none => rw [hxs] at h; simp at h
      | some zs =>
        rw [hxs] at h
        simp only [Option.bind_some, Option.some.injEq] at h
        subst h
        simp [ih hxs]

/-- con-leche: none — `Option`'s `mapM` over a snoc. -/
theorem mapM_option_snoc {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {x : α} {ys : List β}, (xs ++ [x]).mapM f = some ys →
      ∃ zs y, ys = zs ++ [y] ∧ xs.mapM f = some zs ∧ f x = some y := by
  intro xs
  induction xs with
  | nil =>
    intro x ys h
    simp only [List.nil_append, List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
      Option.pure_def] at h
    cases hx : f x with
    | none => rw [hx] at h; simp at h
    | some y =>
      rw [hx] at h
      simp only [Option.bind_some, Option.some.injEq] at h
      subst h
      exact ⟨[], y, rfl, rfl, rfl⟩
  | cons a as ih =>
    intro x ys h
    simp only [List.cons_append, List.mapM_cons, Option.bind_eq_bind,
      Option.pure_def] at h
    cases ha : f a with
    | none => rw [ha] at h; simp at h
    | some b =>
      rw [ha] at h
      cases hr : (as ++ [x]).mapM f with
      | none => rw [hr] at h; simp at h
      | some rs =>
        rw [hr] at h
        simp only [Option.bind_some, Option.some.injEq] at h
        subst h
        obtain ⟨zs, y, rfl, hz, hy⟩ := ih hr
        refine ⟨b :: zs, y, rfl, ?_, hy⟩
        simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, ha, hz,
          Option.bind_some]

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:884-900 nestHoleImg
(`h :: prog`) — **the stack prefix of length `n + 1`, denoted, is its last
frame consed onto the prefix of length `n`**: the twin's list is outermost
first, con-leche's innermost first (`dProg` reverses). -/
theorem dProg_take_succ {st : EStore} {prog : List Arena.NestHole} {n : Nat}
    (hn : n < prog.length) {progP : List ConLeche.NestHole}
    (h : dProg st (prog.take (n + 1)) = some progP) :
    ∃ hP progP', progP = hP :: progP' ∧ dHole st prog[n] = some hP ∧
      dProg st (prog.take n) = some progP' ∧ progP'.length = n := by
  simp only [dProg, Option.map_eq_some_iff] at h ⊢
  obtain ⟨ys, hys, rfl⟩ := h
  rw [List.take_add_one, List.getElem?_eq_getElem hn, Option.toList_some] at hys
  obtain ⟨zs, y, rfl, hz, hy⟩ := mapM_option_snoc hys
  refine ⟨y, zs.reverse, by simp, hy, ⟨zs, hz, rfl⟩, ?_⟩
  rw [List.length_reverse, mapM_option_length hz, List.length_take]
  omega

/-- con-leche: none — a denoting handle list at an index, as the `Option`
lift of `RE`. -/
theorem getElem?_ROp {st : EStore} {hs : List EIdx} {xs : List Expr}
    (h : Frontend.denoteEList st hs = some xs) (j : Nat) :
    ROp RE xs[j]? st hs[j]? := by
  obtain ⟨hnone, hsome⟩ := denoteEList_getElem? h j
  cases hj : hs[j]? with
  | none => exact hnone.mp hj
  | some a =>
    obtain ⟨x, hx, hd⟩ := hsome a hj
    exact ⟨x, hx, hd⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1104-1108 nestKeyMap
The key's variable replacement, at handles: the `Option` lift of `RE`. -/
theorem nestKeyMap_rel {st : EStore} {ds holes : List EIdx} {dsP holesP : List Expr}
    (hds : Frontend.denoteEList st ds = some dsP)
    (hho : Frontend.denoteEList st holes = some holesP) (i : Nat) :
    ROp RE (ConLeche.nestKeyMap dsP holesP i) st (Arena.nestKeyMap ds holes i) := by
  simp only [Arena.nestKeyMap, ConLeche.nestKeyMap, denoteEList_length hds]
  split
  · exact getElem?_ROp hds i
  · exact getElem?_ROp hho _

/-! ## The readback block: `fvMapAt`, `replaceFVarsGo`, `replaceFVars`,
`nestHoleImg` -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:744-757 Expr.replaceFVars
(`f`) — **a twin `FvMap` stands for a pure map**, one clause per
instantiation con-leche writes:

* `.holeImg ctx prog n` is `nestHoleImg ctxP progP` at the denotation of the
  stack prefix of length `n` (`dProg` reverses it: the twin's stack is
  outermost first, con-leche's innermost first), `n ≤ prog.length`;
* `.keyMap ds holes` is `nestKeyMap dsP holesP`;
* `.erase` is `eraseFVarTys`' constant map to `fvar i (Sort 0)`;
* `.canon pfvs` is `targetCanonParams`' `fun i => pfvsP[i]?`.

The lookup `fnd` a `holeImg` context denotes at is existential: `nestHoleImg`
reads no environment. -/
def FvMapRel (st : EStore) : Arena.FvMap → (Nat → Option Expr) → Prop
  | .holeImg ctx prog n, fP => ∃ fnd ctxP progP, dCtx st fnd ctx = some ctxP ∧
      dProg st (prog.take n) = some progP ∧ n ≤ prog.length ∧
      fP = ConLeche.nestHoleImg ctxP progP
  | .keyMap ds holes, fP => ∃ dsP holesP, Frontend.denoteEList st ds = some dsP ∧
      Frontend.denoteEList st holes = some holesP ∧ fP = ConLeche.nestKeyMap dsP holesP
  | .erase, fP => fP = fun i => some (.fvar i (.sort .zero))
  | .canon pfvs, fP => ∃ pP, Frontend.denoteEList st pfvs = some pP ∧
      fP = fun i => pP[i]?

theorem FvMapRel.ext {st st' : EStore} (hx : Ext st st') {f : Arena.FvMap}
    {fP : Nat → Option Expr} (h : FvMapRel st f fP) : FvMapRel st' f fP := by
  cases f with
  | holeImg ctx prog n =>
    obtain ⟨fnd, ctxP, progP, h1, h2, h3, h4⟩ := h
    exact ⟨fnd, ctxP, progP, dCtx_ext fnd hx _ _ h1, dProg_ext hx _ _ h2, h3, h4⟩
  | keyMap ds holes =>
    obtain ⟨a, b, h1, h2, h3⟩ := h
    exact ⟨a, b, denoteEList_ext hx _ _ h1, denoteEList_ext hx _ _ h2, h3⟩
  | erase => exact h
  | canon pfvs =>
    obtain ⟨a, h1, h2⟩ := h
    exact ⟨a, denoteEList_ext hx _ _ h1, h2⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:764-765 ReplaceFVarsMemoInv
The handle-keyed memo of `replaceFVars fP`. -/
def RFMemoOK (fP : Nat → Option Expr) (tbl : Std.HashMap EIdx EIdx) (st : EStore) :
    Prop :=
  ∀ (k v : EIdx), tbl[k]? = some v →
    ∃ e, denoteE st k = some e ∧ denoteE st v = some (Expr.replaceFVars fP e)

theorem RFMemoOK.empty {fP : Nat → Option Expr} {st : EStore} : RFMemoOK fP ∅ st := by
  intro k v h; simp at h

theorem RFMemoOK.ext {fP : Nat → Option Expr} {tbl : Std.HashMap EIdx EIdx}
    {st st' : EStore} (hx : Ext st st') (h : RFMemoOK fP tbl st) : RFMemoOK fP tbl st' := by
  intro k v hk
  obtain ⟨e, h1, h2⟩ := h k v hk
  exact ⟨e, denote_ext h1 hx, denote_ext h2 hx⟩

theorem RFMemoOK.insert {fP : Nat → Option Expr} {tbl : Std.HashMap EIdx EIdx}
    {st : EStore} (hm : RFMemoOK fP tbl st) {h r : EIdx} {hP : Expr}
    (hd : denoteE st h = some hP) (hr : denoteE st r = some (Expr.replaceFVars fP hP)) :
    RFMemoOK fP (tbl.insert h r) st := by
  intro k v hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact ⟨hP, hd, hr⟩
  · exact hm k v hk

/-- con-leche: none — the statement `fvMapAt f` answers `fP`. -/
def FvMapAtSpec (f : Arena.FvMap) (fP : Nat → Option Expr) : Prop :=
  ∀ i, PSpecP (fun st => FvMapRel st f fP) (Arena.fvMapAt f i) (ROp RE (fP i))

/-- con-leche: none — the statement `nestHoleImg ctx prog n` answers
con-leche's at the denoted context and stack prefix. -/
def HoleImgSpec (ctx : Arena.NestCtx) (prog : List Arena.NestHole) (n : Nat) : Prop :=
  ∀ (i : Nat) (fnd : ConLeche.Name → Option ConstantInfo) (ctxP : ConLeche.NestCtx)
    (progP : List ConLeche.NestHole),
    PSpecP (fun st => dCtx st fnd ctx = some ctxP ∧ dProg st (prog.take n) = some progP ∧
        n ≤ prog.length)
      (Arena.nestHoleImg ctx prog n i) (ROp RE (ConLeche.nestHoleImg ctxP progP i))

/-- con-leche: none — `PStep` keeps `PinsOK`. -/
theorem PinsOK.ofPStep {s s' : AState} (hp : PinsOK s) (h : PStep s s') : PinsOK s' :=
  PinsOK.mono hp h.ext h.pins

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:744-757 Expr.replaceFVars
**`fvMapAt`, given its `holeImg` arm**: the four maps, variant by variant. -/
theorem fvMapAt_spec_of (f : Arena.FvMap) (fP : Nat → Option Expr)
    (hHI : ∀ ctx prog n, f = .holeImg ctx prog n → HoleImgSpec ctx prog n) :
    FvMapAtSpec f fP := by
  intro i s₀ s' r hok hpins hpre hrun
  cases f with
  | holeImg ctx prog n =>
    obtain ⟨fnd, ctxP, progP, h1, h2, h3, rfl⟩ := hpre
    rw [Arena.fvMapAt] at hrun
    exact hHI ctx prog n rfl i fnd ctxP progP s₀ s' r hok hpins ⟨h1, h2, h3⟩ hrun
  | keyMap ds holes =>
    obtain ⟨dsP, holesP, h1, h2, rfl⟩ := hpre
    rw [Arena.fvMapAt] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, nestKeyMap_rel h1 h2 i⟩
  | erase =>
    subst hpre
    rw [Arena.fvMapAt] at hrun
    obtain ⟨z, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨rfl, hz⟩ := zeroLevel_run hpins k1
    obtain ⟨so, s2, k2, z2⟩ := bindOk z1
    obtain ⟨p2, hso⟩ := internSortE_run hok hz k2
    obtain ⟨v, s3, k3, z3⟩ := bindOk z2
    obtain ⟨p3, hv⟩ := internFVarE_run p2.ok hso k3
    obtain ⟨rfl, rfl⟩ := pureOk z3
    exact ⟨p2.trans p3, _, rfl, hv⟩
  | canon pfvs =>
    obtain ⟨pP, h1, rfl⟩ := hpre
    rw [Arena.fvMapAt] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, getElem?_ROp h1 i⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:775-810 Expr.replaceFVarsGo
**The memoised walk, given `fvMapAt f`'s statement**: it computes
`replaceFVars fP`.  (`PSpecP`: the `.erase` map interns through the
`zeroLevel` pin.) -/
theorem replaceFVarsGo_spec_of (f : Arena.FvMap) (fP : Nat → Option Expr)
    (hfm : FvMapAtSpec f fP) :
    ∀ (fuel : Nat) (memo : Std.HashMap EIdx EIdx) (h : EIdx) (hP : Expr),
    PSpecP (fun st => FvMapRel st f fP ∧ denoteE st h = some hP ∧ RFMemoOK fP memo st)
      (Arena.replaceFVarsGo f memo fuel h)
      (fun st r => denoteE st r.1 = some (Expr.replaceFVars fP hP) ∧
        RFMemoOK fP r.2 st) := by
  intro fuel
  induction fuel with
  | zero =>
    intro memo h hP s₀ s' r hok _ _ hrun
    rw [Arena.replaceFVarsGo] at hrun
    exact absurd hrun (fun hc => failOk hc)
  | succ fuel ih =>
    intro memo h hP s₀ s' r hok hpins hp hrun
    obtain ⟨hF, hd, hm⟩ := hp
    rw [Arena.replaceFVarsGo] at hrun
    dsimp only at hrun
    obtain ⟨v, s₁, hv, h2⟩ := bindOk hrun
    obtain ⟨hv0, hw⟩ := view_run hv
    rw [hv0] at h2
    have fin : ∀ {s₂ s₃ : AState} {rr : EIdx} {mm : Std.HashMap EIdx EIdx}
        {r' : EIdx × Std.HashMap EIdx EIdx},
        PStep s₀ s₂ → denoteE s₂.store rr = some (Expr.replaceFVars fP hP) →
        RFMemoOK fP mm s₂.store →
        (pure ((rr, mm.insert h rr) : EIdx × Std.HashMap EIdx EIdx) :
            AM (EIdx × Std.HashMap EIdx EIdx)) s₂ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ denoteE s₃.store r'.1 = some (Expr.replaceFVars fP hP) ∧
          RFMemoOK fP r'.2 s₃.store := by
      intro s₂ s₃ rr mm r' hs hb hmm hz
      obtain ⟨rfl, rfl⟩ := pureOk hz
      exact ⟨hs, hb, RFMemoOK.insert hmm (denote_ext hd hs.ext) hb⟩
    have hit : ∀ {s₃ : AState} {r₀ : EIdx} {r' : EIdx × Std.HashMap EIdx EIdx},
        memo[h]? = some r₀ →
        (pure ((r₀, memo) : EIdx × Std.HashMap EIdx EIdx) :
            AM (EIdx × Std.HashMap EIdx EIdx)) s₀ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ denoteE s₃.store r'.1 = some (Expr.replaceFVars fP hP) ∧
          RFMemoOK fP r'.2 s₃.store := by
      intro s₃ r₀ r' hlk hz
      obtain ⟨rfl, rfl⟩ := pureOk hz
      obtain ⟨e, he, hre⟩ := hm h r₀ hlk
      obtain rfl := Option.some.inj (hd.symm.trans he)
      exact ⟨PStep.refl hok, hre, hm⟩
    cases v
    case bvar j =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain rfl := denote_bvar_inv hok.wf hw hd
      exact ⟨PStep.refl hok, hd, hm⟩
    case sort u =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨l, rfl, _⟩ := denote_sort_inv hok.wf hw hd
      exact ⟨PStep.refl hok, hd, hm⟩
    case lit l =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain rfl := denote_lit_inv hok.wf hw hd
      exact ⟨PStep.refl hok, hd, hm⟩
    case const n us =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hok.wf hw hd
      exact ⟨PStep.refl hok, hd, hm⟩
    case fvar k ty =>
      obtain ⟨t, rfl, _⟩ := denote_fvar_inv hok.wf hw hd
      obtain ⟨o, s₂, h3, h4⟩ := bindOk h2
      obtain ⟨p3, ho⟩ := hfm k s₀ s₂ o hok hpins hF h3
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := pureOk h4
        refine ⟨p3, ?_, hm.ext p3.ext⟩
        have : fP k = none := ho
        simp only [Expr.replaceFVars, this, Option.getD_none]
        exact denote_ext hd p3.ext
      | some a =>
        obtain ⟨rfl, rfl⟩ := pureOk h4
        obtain ⟨b, hb, hab⟩ := ho
        refine ⟨p3, ?_, hm.ext p3.ext⟩
        simp only [Expr.replaceFVars, hb, Option.getD_some]
        exact hab
    case app f a =>
      obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_app_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo f ef _ _ (a2, m1) hok hpins
          ⟨hF, hf, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 a ea _ _ (b2, m2) hsA.ok
          (PinsOK.ofPStep hpins hsA) ⟨hF.ext hsA.ext, denote_ext ha hsA.ext, hmA⟩ hc2
        obtain ⟨q, sc, hc3, hn3⟩ := bindOk hn2
        obtain ⟨hsC, hq⟩ := internAppE_run hsB.ok (denote_ext hrA hsB.ext) hrB hc3
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn3
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin ((hsA.trans hsB).trans hsC) (by rw [hq]; rfl) (hmB.ext hsC.ext) hz
    case lam ty b m =>
      obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_lam_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo ty et _ _ (a2, m1) hok hpins
          ⟨hF, hty, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 b eb _ _ (b2, m2) hsA.ok
          (PinsOK.ofPStep hpins hsA) ⟨hF.ext hsA.ext, denote_ext hbd hsA.ext, hmA⟩ hc2
        obtain ⟨q, sc, hc3, hn3⟩ := bindOk hn2
        obtain ⟨hsC, hq⟩ := internLamE_run hsB.ok (denote_ext hrA hsB.ext) hrB hc3
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn3
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin ((hsA.trans hsB).trans hsC) (by rw [hq]; rfl) (hmB.ext hsC.ext) hz
    case forallE ty b m =>
      obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_forallE_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo ty et _ _ (a2, m1) hok hpins
          ⟨hF, hty, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 b eb _ _ (b2, m2) hsA.ok
          (PinsOK.ofPStep hpins hsA) ⟨hF.ext hsA.ext, denote_ext hbd hsA.ext, hmA⟩ hc2
        obtain ⟨q, sc, hc3, hn3⟩ := bindOk hn2
        obtain ⟨hsC, hq⟩ := internForallEE_run hsB.ok (denote_ext hrA hsB.ext) hrB hc3
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn3
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin ((hsA.trans hsB).trans hsC) (by rw [hq]; rfl) (hmB.ext hsC.ext) hz
    case letE lt lv lb =>
      obtain ⟨et, ev, eb, rfl, hty, hval, hbd⟩ := denote_letE_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo lt et _ _ (a2, m1) hok hpins ⟨hF, hty, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 lv ev _ _ (b2, m2) hsA.ok
          (PinsOK.ofPStep hpins hsA) ⟨hF.ext hsA.ext, denote_ext hval hsA.ext, hmA⟩ hc2
        have hAB := hsA.trans hsB
        obtain ⟨p3, sc, hc3, hn3⟩ := bindOk hn2
        obtain ⟨c2, m3⟩ := p3
        obtain ⟨hsC, hrC, hmC⟩ := ih m2 lb eb _ _ (c2, m3) hsB.ok
          (PinsOK.ofPStep hpins hAB) ⟨hF.ext hAB.ext, denote_ext hbd hAB.ext, hmB⟩ hc3
        obtain ⟨q, sd, hc4, hn4⟩ := bindOk hn3
        obtain ⟨hsD, hq⟩ := internLetEE_run hsC.ok (denote_ext hrA (hsB.ext.trans hsC.ext))
          (denote_ext hrB hsC.ext) hrC hc4
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn4
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin ((hAB.trans hsC).trans hsD) (by rw [hq]; rfl) (hmC.ext hsD.ext) hz
    case proj pn pk psub =>
      obtain ⟨nm, es, rfl, hn, hsub⟩ := denote_proj_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo psub es _ _ (a2, m1) hok hpins ⟨hF, hsub, hm⟩ hc1
        obtain ⟨q, sc, hc3, hn3⟩ := bindOk hn1
        obtain ⟨hsC, hq⟩ := internProjE_run hsA.ok (denoteN_ext hn hsA.ext) hrA hc3
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn3
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin (hsA.trans hsC) (by rw [hq]; rfl) (hmA.ext hsC.ext) hz

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:875-877 Expr.replaceFVarsFast
The entry at an empty memo, given `fvMapAt f`'s statement. -/
theorem replaceFVars_spec_of (f : Arena.FvMap) (fP : Nat → Option Expr)
    (hfm : FvMapAtSpec f fP) (e : EIdx) (eP : Expr) :
    PSpecP (fun st => FvMapRel st f fP ∧ denoteE st e = some eP)
      (Arena.replaceFVars f e) (RE (Expr.replaceFVars fP eP)) := by
  intro s₀ s' r hok hpins hp hrun
  obtain ⟨hF, hd⟩ := hp
  rw [Arena.replaceFVars] at hrun
  obtain ⟨q, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep, hr, _⟩ := replaceFVarsGo_spec_of f fP hfm Arena.coreWalkFuel ∅ e eP
    s₀ s₁ q hok hpins ⟨hF, hd, RFMemoOK.empty⟩ h1
  obtain ⟨rfl, rfl⟩ := pureOk h2
  exact ⟨hstep, hr⟩

/-- con-leche: none — `List.mapM` of a pin-reading expression map over a
denoting handle list: the answer denotes the pure map, pointwise.  A store
invariant `Q` rides along (the map's own licence). -/
theorem mapM_RE_P {F : EIdx → AM EIdx} {G : Expr → Expr} (Q : EStore → Prop)
    (hQ : ∀ {st st' : EStore}, Ext st st' → Q st → Q st')
    (hF : ∀ (e : EIdx) (eP : Expr),
      PSpecP (fun st => Q st ∧ denoteE st e = some eP) (F e) (RE (G eP))) :
    ∀ (xs : List EIdx) (xsP : List Expr),
      PSpecP (fun st => Q st ∧ Frontend.denoteEList st xs = some xsP) (xs.mapM F)
        (REL (xsP.map G)) := by
  intro xs
  induction xs with
  | nil =>
    intro xsP s₀ s' r hok _ hp hrun
    obtain ⟨_, h⟩ := hp
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h
    simp only [List.mapM_nil] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons e es ih =>
    intro xsP s₀ s' r hok hpins hp hrun
    obtain ⟨hq, h⟩ := hp
    simp only [Frontend.denoteEList] at h
    cases he : denoteE s₀.store e with
    | none => rw [he] at h; simp at h
    | some eP =>
      cases hes : Frontend.denoteEList s₀.store es with
      | none => rw [he, hes] at h; simp at h
      | some esP =>
        rw [he, hes] at h
        obtain rfl := (Option.some.inj h).symm
        simp only [List.mapM_cons] at hrun
        obtain ⟨x, s1, k1, z1⟩ := bindOk hrun
        obtain ⟨p1, hx⟩ := hF e eP s₀ s1 x hok hpins ⟨hq, he⟩ k1
        obtain ⟨xs', s2, k2, z2⟩ := bindOk z1
        obtain ⟨p2, hxs⟩ := ih esP s1 s2 xs' p1.ok (PinsOK.ofPStep hpins p1)
          ⟨hQ p1.ext hq, denoteEList_ext p1.ext _ _ hes⟩ k2
        obtain ⟨rfl, rfl⟩ := pureOk z2
        refine ⟨p1.trans p2, ?_⟩
        show Frontend.denoteEList _ (x :: xs') = _
        have hxs' : Frontend.denoteEList _ xs' = some (esP.map G) := hxs
        simp only [Frontend.denoteEList, List.map_cons, denote_ext hx p2.ext, hxs']

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:521-528 NestKey —
`dKey` taken apart. -/
theorem dKey_inv {st : EStore} {k : Arena.NestKey} {kP : ConLeche.NestKey}
    (h : dKey st k = some kP) :
    denoteN st.ns k.cname = some kP.cname ∧ denoteLs st.lss k.lvls = some kP.lvls ∧
      Frontend.denoteEList st k.ds = some kP.ds := by
  simp only [dKey] at h
  cases h1 : denoteN st.ns k.cname with
  | none => rw [h1] at h; exact nomatch h
  | some c =>
  cases h2 : denoteLs st.lss k.lvls with
  | none => rw [h1, h2] at h; exact nomatch h
  | some us =>
  cases h3 : Frontend.denoteEList st k.ds with
  | none => rw [h1, h2, h3] at h; exact nomatch h
  | some ds =>
  rw [h1, h2, h3] at h
  obtain rfl := (Option.some.inj h).symm
  exact ⟨rfl, rfl, rfl⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:884-900 nestHoleImg
**The holes read back**, at every stack prefix: by induction on the prefix
length `n`, the frame case reading its parameters back through
`replaceFVars (.holeImg ctx prog n)` — whose `fvMapAt` is this statement at
`n`, the induction hypothesis. -/
theorem nestHoleImg_spec (ctx : Arena.NestCtx) (prog : List Arena.NestHole) :
    ∀ n, HoleImgSpec ctx prog n := by
  intro n
  induction n with
  | zero =>
    intro i fnd ctxP progP s₀ s' r hok hpins hp hrun
    obtain ⟨h1, h2, _⟩ := hp
    cases progP with
    | cons _ _ => simp [dProg] at h2
    | nil =>
    obtain ⟨namesP, lpsP, paramsP, sortP, rfl, hN, _, hPa, _, hLv⟩ := dCtx_inv h1
    have hlen := denoteNList_length hN
    rw [Arena.nestHoleImg] at hrun
    dsimp only at hrun
    have hiff : ((decide (ctx.nP ≤ i) && decide (i < ctx.hiAt 0)) = true) ↔
        (ctx.nP ≤ i ∧ i < ctx.nP + namesP.length + 0) := by
      simp [Arena.NestCtx.hiAt, hlen]
    by_cases hc : (decide (ctx.nP ≤ i) && decide (i < ctx.hiAt 0)) = true
    · rw [if_pos hc] at hrun
      obtain ⟨hlo, hhi⟩ := hiff.mp hc
      have hj : i - ctx.nP < ctx.names.length := by omega
      obtain ⟨nm, hnm, hn⟩ := denoteNList_getElem? hN (i - ctx.nP) _
        (List.getElem?_eq_getElem hj)
      have hg : ctx.names.getD (i - ctx.nP) default = ctx.names[i - ctx.nP] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rw [hg] at hrun
      obtain ⟨hd, s1, k1, z1⟩ := bindOk hrun
      obtain ⟨p1, hhd⟩ := internConstE_run hok hn hLv k1
      obtain ⟨q, s2, k2, z2⟩ := bindOk z1
      obtain ⟨p2, hq⟩ := mkAppN_run ctx.params paramsP p1.ok hhd
        (denoteEList_ext p1.ext _ _ hPa) k2
      obtain ⟨rfl, rfl⟩ := pureOk z2
      refine ⟨p1.trans p2, _, ?_, hq⟩
      have hgP : namesP.getD (i - ctx.nP) .anonymous = nm := by
        simp [List.getD_eq_getElem?_getD, hnm]
      simp only [ConLeche.nestHoleImg, ConLeche.NestCtx.hiAt, hgP]
      rw [if_pos ⟨hlo, hhi⟩]
    · rw [if_neg hc] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      refine ⟨PStep.refl hok, ?_⟩
      show ConLeche.nestHoleImg _ [] i = none
      simp only [ConLeche.nestHoleImg, ConLeche.NestCtx.hiAt]
      rw [if_neg (fun hh => hc (hiff.mpr hh))]
  | succ n ih =>
    intro i fnd ctxP progP s₀ s' r hok hpins hp hrun
    obtain ⟨h1, h2, h3⟩ := hp
    have hn : n < prog.length := by omega
    obtain ⟨hP, progP', rfl, hH, hprog', hlenP⟩ := dProg_take_succ hn h2
    obtain ⟨namesP, lpsP, paramsP, sortP, hctx, hN, _, _, _, _⟩ := dCtx_inv h1
    have hlen := denoteNList_length hN
    rw [Arena.nestHoleImg] at hrun
    dsimp only at hrun
    have hiff : (i == ctx.hiAt n) = true ↔ i = ctxP.hiAt progP'.length := by
      subst hctx
      simp [Arena.NestCtx.hiAt, ConLeche.NestCtx.hiAt, hlen, hlenP]
    by_cases hc : (i == ctx.hiAt n) = true
    · rw [if_pos hc] at hrun
      have hg : prog.getD n default = prog[n] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
      rw [hg] at hrun
      simp only [dHole, Option.map_eq_some_iff] at hH
      obtain ⟨kP, hk, rfl⟩ := hH
      obtain ⟨hcn, hcl, hcd⟩ := dKey_inv hk
      have hfm : FvMapAtSpec (.holeImg ctx prog n) (ConLeche.nestHoleImg ctxP progP') :=
        fvMapAt_spec_of _ _ (fun c p m heq => by cases heq; exact ih)
      obtain ⟨ds, s1, k1, z1⟩ := bindOk hrun
      obtain ⟨p1, hds⟩ := mapM_RE_P
        (fun st => FvMapRel st (.holeImg ctx prog n) (ConLeche.nestHoleImg ctxP progP'))
        (fun hx h => h.ext hx)
        (fun e eP => replaceFVars_spec_of _ _ hfm e eP) _ _ s₀ s1 ds hok hpins
        ⟨⟨fnd, ctxP, progP', h1, hprog', by omega, rfl⟩, hcd⟩ k1
      obtain ⟨hd, s2, k2, z2⟩ := bindOk z1
      obtain ⟨p2, hhd⟩ := internConstE_run p1.ok (denoteN_ext hcn p1.ext)
        (denoteLs_ext hcl p1.ext) k2
      obtain ⟨q, s3, k3, z3⟩ := bindOk z2
      obtain ⟨p3, hq⟩ := mkAppN_run ds _ p2.ok hhd (denoteEList_ext p2.ext _ _ hds) k3
      obtain ⟨rfl, rfl⟩ := pureOk z3
      refine ⟨(p1.trans p2).trans p3, _, ?_, hq⟩
      simp only [ConLeche.nestHoleImg]
      rw [if_pos (hiff.mp hc)]
    · rw [if_neg hc] at hrun
      obtain ⟨hs, hr⟩ := ih i fnd ctxP progP' s₀ s' r hok hpins ⟨h1, hprog', by omega⟩ hrun
      refine ⟨hs, ?_⟩
      have heq : ConLeche.nestHoleImg ctxP (hP :: progP') i =
          ConLeche.nestHoleImg ctxP progP' i := by
        simp only [ConLeche.nestHoleImg]
        rw [if_neg (fun hh => hc (hiff.mpr hh))]
      rw [heq]
      exact hr

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:744-757 Expr.replaceFVars
**`fvMapAt`**: every map answers its pure function. -/
theorem fvMapAt_spec (f : Arena.FvMap) (fP : Nat → Option Expr) : FvMapAtSpec f fP :=
  fvMapAt_spec_of f fP (fun ctx prog n _ => nestHoleImg_spec ctx prog n)

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:875-877 Expr.replaceFVarsFast
**`replaceFVars`**: the pure `Expr.replaceFVars` (con-leche's `@[csimp]`
swaps its memoised walk in; the structural definition is the spec). -/
theorem replaceFVars_spec (f : Arena.FvMap) (fP : Nat → Option Expr) (e : EIdx)
    (eP : Expr) :
    PSpecP (fun st => FvMapRel st f fP ∧ denoteE st e = some eP)
      (Arena.replaceFVars f e) (RE (Expr.replaceFVars fP eP)) :=
  replaceFVars_spec_of f fP (fvMapAt_spec f fP) e eP

/-! ## The whole-application abstraction: `phApp?`, `nestCanonSub`, `appHole?`,
`replaceApps`, `nestPhs` -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:917-923 Expr.phApp? —
a constant's name and level list, denoted. -/
abbrev RPh (p : ConLeche.Name × List Level) : EStore → NIdx × LsIdx → Prop :=
  fun st q => denoteN st.ns q.1 = some p.1 ∧ denoteLs st.lss q.2 = some p.2

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:917-923 Expr.phApp?
`e` is a constant applied to exactly the placeholders `fvar b, …`. -/
theorem phApp?_spec (b : Nat) :
    ∀ (n : Nat) (e : EIdx) (eP : Expr),
    PSpec (fun st => denoteE st e = some eP) (Arena.phApp? b e n)
      (ROp RPh (Expr.phApp? b eP n)) := by
  intro n
  induction n with
  | zero =>
    intro e eP s₀ s' r hok hd hrun
    simp only [Arena.phApp?] at hrun
    by_cases htg : (e.tag == ETag.const) = true
    · rw [if_pos htg] at hrun
      obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
      obtain ⟨hs1, ho⟩ := viewConst_run h1
      rw [hs1] at h2
      cases o with
      | none => exact absurd h2 (fun hc => failDanglingE_ok hc)
      | some p =>
        obtain ⟨c, us⟩ := p
        have hw := view_of_viewConst_tag htg ho.symm
        obtain ⟨nm, ls, rfl, hn, hls⟩ := denote_const_inv hok.wf hw hd
        dsimp only at h2
        obtain ⟨rfl, rfl⟩ := pureOk h2
        exact ⟨PStep.refl hok, (nm, ls), rfl, hn, hls⟩
    · rw [if_neg htg] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      refine ⟨PStep.refl hok, ?_⟩
      show Expr.phApp? b eP 0 = none
      cases eP with
      | const c us => exact absurd (tag_const_of_denote hok.wf hd) (by simpa using htg)
      | _ => simp [Expr.phApp?]
  | succ n ih =>
    intro e eP s₀ s' r hok hd hrun
    simp only [Arena.phApp?] at hrun
    by_cases htg : (e.tag == ETag.app) = true
    · rw [if_pos htg] at hrun
      obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
      obtain ⟨hs1, ho⟩ := viewApp_run h1
      rw [hs1] at h2
      cases o with
      | none => exact absurd h2 (fun hc => failDanglingE_ok hc)
      | some p =>
        obtain ⟨f, a⟩ := p
        have hw := view_of_viewApp_tag htg ho.symm
        obtain ⟨fP, aP, rfl, hf, ha⟩ := denote_app_inv hok.wf hw hd
        dsimp only at h2
        by_cases hta : (a.tag == ETag.fvar) = true
        · rw [if_pos hta] at h2
          obtain ⟨o2, s₂, h3, h4⟩ := bindOk h2
          obtain ⟨hs2, ho2⟩ := viewFVarIdx_run h3
          rw [hs2] at h4
          cases o2 with
          | none => exact absurd h4 (fun hc => failDanglingE_ok hc)
          | some j =>
            obtain ⟨t, rfl⟩ := denote_of_viewFVarIdx hok.wf hta ho2.symm ha
            dsimp only at h4
            by_cases hj : (j == b + n) = true
            · rw [if_pos hj] at h4
              have hj' : j = b + n := by simpa using hj
              have heq : Expr.phApp? b (.app fP (.fvar j t)) (n + 1) = Expr.phApp? b fP n := by
                simp [Expr.phApp?, hj']
              rw [heq]
              exact ih f fP s₀ s' r hok hf h4
            · rw [if_neg hj] at h4
              obtain ⟨rfl, rfl⟩ := pureOk h4
              refine ⟨PStep.refl hok, ?_⟩
              show Expr.phApp? b (.app fP (.fvar j t)) (n + 1) = none
              have hj' : ¬ j = b + n := by simpa using hj
              simp [Expr.phApp?, hj']
        · rw [if_neg hta] at h2
          obtain ⟨rfl, rfl⟩ := pureOk h2
          refine ⟨PStep.refl hok, ?_⟩
          show Expr.phApp? b (.app fP aP) (n + 1) = none
          cases aP with
          | fvar j t => exact absurd (tag_fvar_of_denote hok.wf ha) (by simpa using hta)
          | _ => rfl
    · rw [if_neg htg] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      refine ⟨PStep.refl hok, ?_⟩
      show Expr.phApp? b eP (n + 1) = none
      cases eP with
      | app f a => exact absurd (tag_app_of_denote hok.wf hd) (by simpa using htg)
      | _ => rfl

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1089-1095 nestCanonSub
Member `m` at the levels `us` to the canonical hole `fvar (n + m)`; the level
lists compare by handle (`beq_lshandle_eq`). -/
theorem nestCanonSub_spec (names : List NIdx) (namesP : List ConLeche.Name)
    (us : LsIdx) (usP : List Level) (n : Nat) (c : NIdx) (cP : ConLeche.Name)
    (v : LsIdx) (vP : List Level) :
    PSpecP (fun st => Frontend.denoteNList st.ns names = some namesP ∧
        denoteLs st.lss us = some usP ∧ denoteN st.ns c = some cP ∧
        denoteLs st.lss v = some vP)
      (Arena.nestCanonSub names us n c v)
      (ROp RE (ConLeche.nestCanonSub namesP usP n cP vP)) := by
  intro s₀ s' r hok hpins hp hrun
  obtain ⟨hN, hU, hC, hV⟩ := hp
  simp only [Arena.nestCanonSub] at hrun
  have hbv := beq_lshandle_eq hok.wf hV hU
  have hfi := findIdx_handle_eq hok.wf hC hN
  by_cases hb : (v == us) = true
  · rw [if_pos hb] at hrun
    have hbP : (vP == usP) = true := by rw [← hbv]; exact hb
    cases hm : names.findIdx? (· == c) with
    | none =>
      rw [hm] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      refine ⟨PStep.refl hok, ?_⟩
      show ConLeche.nestCanonSub namesP usP n cP vP = none
      simp only [ConLeche.nestCanonSub, hbP, if_true, ← hfi, hm, Option.map_none]
    | some m =>
      rw [hm] at hrun
      dsimp only at hrun
      obtain ⟨z, s1, k1, z1⟩ := bindOk hrun
      obtain ⟨rfl, hz⟩ := zeroLevel_run hpins k1
      obtain ⟨so, s2, k2, z2⟩ := bindOk z1
      obtain ⟨p2, hso⟩ := internSortE_run hok hz k2
      obtain ⟨q, s3, k3, z3⟩ := bindOk z2
      obtain ⟨p3, hq⟩ := internFVarE_run p2.ok hso k3
      obtain ⟨rfl, rfl⟩ := pureOk z3
      refine ⟨p2.trans p3, _, ?_, hq⟩
      simp only [ConLeche.nestCanonSub, hbP, if_true, ← hfi, hm, Option.map_some]
  · rw [if_neg hb] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨PStep.refl hok, ?_⟩
    have hbP : ¬ (vP == usP) = true := by rw [← hbv]; exact hb
    show ConLeche.nestCanonSub namesP usP n cP vP = none
    simp [ConLeche.nestCanonSub, hbP]

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:925-928 Expr.appHole?
The hole a whole application is replaced by, at `nestCanonSub`. -/
theorem appHole?_spec (names : List NIdx) (namesP : List ConLeche.Name)
    (us : LsIdx) (usP : List Level) (b n : Nat) (e : EIdx) (eP : Expr) :
    PSpecP (fun st => Frontend.denoteNList st.ns names = some namesP ∧
        denoteLs st.lss us = some usP ∧ denoteE st e = some eP)
      (Arena.appHole? names us b n e)
      (ROp RE (Expr.appHole? (ConLeche.nestCanonSub namesP usP n) b n eP)) := by
  intro s₀ s' r hok hpins hp hrun
  obtain ⟨hN, hU, hd⟩ := hp
  simp only [Arena.appHole?] at hrun
  obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨p1, ho⟩ := phApp?_spec b n e eP s₀ s₁ o hok hd h1
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk h2
    refine ⟨p1, ?_⟩
    have : Expr.phApp? b eP n = none := ho
    show Expr.appHole? _ b n eP = none
    simp only [Expr.appHole?, this, Option.bind_none]
  | some q =>
    obtain ⟨c, v⟩ := q
    obtain ⟨⟨cP, vP⟩, hph, hc, hv⟩ := ho
    dsimp only at h2
    obtain ⟨p2, hr⟩ := nestCanonSub_spec names namesP us usP n c cP v vP s₁ s' r p1.ok
      (PinsOK.ofPStep hpins p1)
      ⟨denoteNListE_ext p1.ext _ _ hN, denoteLs_ext hU p1.ext, hc, hv⟩ h2
    refine ⟨p1.trans p2, ?_⟩
    have heq : Expr.appHole? (ConLeche.nestCanonSub namesP usP n) b n eP =
        ConLeche.nestCanonSub namesP usP n cP vP := by
      simp only [Expr.appHole?, hph, Option.bind_some]
    rw [heq]
    exact hr

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:949-951 ReplaceAppsMemoInv
The handle-keyed memo of `replaceApps F b n`. -/
def RAMemoOK (F : ConLeche.Name → List Level → Option Expr) (b n : Nat)
    (tbl : Std.HashMap EIdx EIdx) (st : EStore) : Prop :=
  ∀ (k v : EIdx), tbl[k]? = some v →
    ∃ e, denoteE st k = some e ∧ denoteE st v = some (Expr.replaceApps F b n e)

theorem RAMemoOK.empty {F : ConLeche.Name → List Level → Option Expr} {b n : Nat}
    {st : EStore} : RAMemoOK F b n ∅ st := by
  intro k v h; simp at h

theorem RAMemoOK.ext {F : ConLeche.Name → List Level → Option Expr} {b n : Nat}
    {tbl : Std.HashMap EIdx EIdx} {st st' : EStore} (hx : Ext st st')
    (h : RAMemoOK F b n tbl st) : RAMemoOK F b n tbl st' := by
  intro k v hk
  obtain ⟨e, h1, h2⟩ := h k v hk
  exact ⟨e, denote_ext h1 hx, denote_ext h2 hx⟩

theorem RAMemoOK.insert {F : ConLeche.Name → List Level → Option Expr} {b n : Nat}
    {tbl : Std.HashMap EIdx EIdx} {st : EStore} (hm : RAMemoOK F b n tbl st)
    {h r : EIdx} {hP : Expr} (hd : denoteE st h = some hP)
    (hr : denoteE st r = some (Expr.replaceApps F b n hP)) :
    RAMemoOK F b n (tbl.insert h r) st := by
  intro k v hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact ⟨hP, hd, hr⟩
  · exact hm k v hk

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:966-1004 Expr.replaceAppsGo
The memoised whole-application replacement at `nestCanonSub namesP usP n`
computes the pure `replaceApps`. -/
theorem replaceAppsGo_spec (names : List NIdx) (namesP : List ConLeche.Name)
    (us : LsIdx) (usP : List Level) (b n : Nat) :
    ∀ (fuel : Nat) (memo : Std.HashMap EIdx EIdx) (h : EIdx) (hP : Expr),
    PSpecP (fun st => Frontend.denoteNList st.ns names = some namesP ∧
        denoteLs st.lss us = some usP ∧ denoteE st h = some hP ∧
        RAMemoOK (ConLeche.nestCanonSub namesP usP n) b n memo st)
      (Arena.replaceAppsGo names us b n memo fuel h)
      (fun st r => denoteE st r.1 =
          some (Expr.replaceApps (ConLeche.nestCanonSub namesP usP n) b n hP) ∧
        RAMemoOK (ConLeche.nestCanonSub namesP usP n) b n r.2 st) := by
  intro fuel
  induction fuel with
  | zero =>
    intro memo h hP s₀ s' r hok _ _ hrun
    simp only [Arena.replaceAppsGo] at hrun
    exact absurd hrun (fun hc => failOk hc)
  | succ fuel ih =>
    intro memo h hP s₀ s' r hok hpins hp hrun
    obtain ⟨hN, hU, hd, hm⟩ := hp
    simp only [Arena.replaceAppsGo] at hrun
    obtain ⟨v, s₁, hv, h2⟩ := bindOk hrun
    obtain ⟨hv0, hw⟩ := view_run hv
    rw [hv0] at h2
    have fin : ∀ {s₂ s₃ : AState} {rr : EIdx} {mm : Std.HashMap EIdx EIdx}
        {r' : EIdx × Std.HashMap EIdx EIdx},
        PStep s₀ s₂ →
        denoteE s₂.store rr =
          some (Expr.replaceApps (ConLeche.nestCanonSub namesP usP n) b n hP) →
        RAMemoOK (ConLeche.nestCanonSub namesP usP n) b n mm s₂.store →
        (pure ((rr, mm.insert h rr) : EIdx × Std.HashMap EIdx EIdx) :
            AM (EIdx × Std.HashMap EIdx EIdx)) s₂ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ denoteE s₃.store r'.1 =
          some (Expr.replaceApps (ConLeche.nestCanonSub namesP usP n) b n hP) ∧
          RAMemoOK (ConLeche.nestCanonSub namesP usP n) b n r'.2 s₃.store := by
      intro s₂ s₃ rr mm r' hs hb hmm hz
      obtain ⟨rfl, rfl⟩ := pureOk hz
      exact ⟨hs, hb, RAMemoOK.insert hmm (denote_ext hd hs.ext) hb⟩
    have hit : ∀ {s₃ : AState} {r₀ : EIdx} {r' : EIdx × Std.HashMap EIdx EIdx},
        memo[h]? = some r₀ →
        (pure ((r₀, memo) : EIdx × Std.HashMap EIdx EIdx) :
            AM (EIdx × Std.HashMap EIdx EIdx)) s₀ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ denoteE s₃.store r'.1 =
          some (Expr.replaceApps (ConLeche.nestCanonSub namesP usP n) b n hP) ∧
          RAMemoOK (ConLeche.nestCanonSub namesP usP n) b n r'.2 s₃.store := by
      intro s₃ r₀ r' hlk hz
      obtain ⟨rfl, rfl⟩ := pureOk hz
      obtain ⟨e, he, hre⟩ := hm h r₀ hlk
      obtain rfl := Option.some.inj (hd.symm.trans he)
      exact ⟨PStep.refl hok, hre, hm⟩
    cases v
    case bvar j =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain rfl := denote_bvar_inv hok.wf hw hd
      exact ⟨PStep.refl hok, hd, hm⟩
    case sort u =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨l, rfl, _⟩ := denote_sort_inv hok.wf hw hd
      exact ⟨PStep.refl hok, hd, hm⟩
    case lit l =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain rfl := denote_lit_inv hok.wf hw hd
      exact ⟨PStep.refl hok, hd, hm⟩
    case fvar k ty =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨t, rfl, _⟩ := denote_fvar_inv hok.wf hw hd
      exact ⟨PStep.refl hok, hd, hm⟩
    case const c us' =>
      obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hok.wf hw hd
      obtain ⟨o, s₂, h3, h4⟩ := bindOk h2
      obtain ⟨p3, ho⟩ := appHole?_spec names namesP us usP b n h _ s₀ s₂ o hok hpins
        ⟨hN, hU, hd⟩ h3
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := pureOk h4
        refine ⟨p3, ?_, hm.ext p3.ext⟩
        have : Expr.appHole? (ConLeche.nestCanonSub namesP usP n) b n (.const nm ls) = none := ho
        simp only [Expr.replaceApps, this, Option.getD_none]
        exact denote_ext hd p3.ext
      | some a =>
        obtain ⟨rfl, rfl⟩ := pureOk h4
        obtain ⟨bq, hb, hab⟩ := ho
        refine ⟨p3, ?_, hm.ext p3.ext⟩
        simp only [Expr.replaceApps, hb, Option.getD_some]
        exact hab
    case app f a =>
      obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_app_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨o, s₂, h3, h4⟩ := bindOk h2
        obtain ⟨p3, ho⟩ := appHole?_spec names namesP us usP b n h _ s₀ s₂ o hok hpins
          ⟨hN, hU, hd⟩ h3
        cases o with
        | some q =>
          obtain ⟨bq, hb, hab⟩ := ho
          dsimp only at h4
          obtain ⟨y, sy, hy, hz⟩ := bindOk h4
          obtain ⟨rfl, rfl⟩ := pureOk hy
          exact fin p3 (by simp only [Expr.replaceApps, hb, Option.getD_some]; exact hab)
            (hm.ext p3.ext) hz
        | none =>
          have hnone : Expr.appHole? (ConLeche.nestCanonSub namesP usP n) b n
              (.app ef ea) = none := ho
          dsimp only at h4
          obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h4
          obtain ⟨a2, m1⟩ := p1
          obtain ⟨hsA, hrA, hmA⟩ := ih memo f ef _ _ (a2, m1) p3.ok
            (PinsOK.ofPStep hpins p3)
            ⟨denoteNListE_ext p3.ext _ _ hN, denoteLs_ext hU p3.ext, denote_ext hf p3.ext,
             hm.ext p3.ext⟩ hc1
          have h3A := p3.trans hsA
          obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
          obtain ⟨b2, m2⟩ := p2
          obtain ⟨hsB, hrB, hmB⟩ := ih m1 a ea _ _ (b2, m2) hsA.ok
            (PinsOK.ofPStep hpins h3A)
            ⟨denoteNListE_ext h3A.ext _ _ hN, denoteLs_ext hU h3A.ext,
             denote_ext ha h3A.ext, hmA⟩ hc2
          obtain ⟨q, sc, hc3, hn3⟩ := bindOk hn2
          obtain ⟨hsC, hq⟩ := internAppE_run hsB.ok (denote_ext hrA hsB.ext) hrB hc3
          obtain ⟨y, sy, hy, hz⟩ := bindOk hn3
          obtain ⟨rfl, rfl⟩ := pureOk hy
          exact fin ((h3A.trans hsB).trans hsC)
            (by rw [hq]; simp only [Expr.replaceApps, hnone, Option.getD_none])
            (hmB.ext hsC.ext) hz
    case lam ty bd m =>
      obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_lam_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo ty et _ _ (a2, m1) hok hpins
          ⟨hN, hU, hty, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 bd eb _ _ (b2, m2) hsA.ok
          (PinsOK.ofPStep hpins hsA)
          ⟨denoteNListE_ext hsA.ext _ _ hN, denoteLs_ext hU hsA.ext, denote_ext hbd hsA.ext,
           hmA⟩ hc2
        obtain ⟨q, sc, hc3, hn3⟩ := bindOk hn2
        obtain ⟨hsC, hq⟩ := internLamE_run hsB.ok (denote_ext hrA hsB.ext) hrB hc3
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn3
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin ((hsA.trans hsB).trans hsC) (by rw [hq]; rfl) (hmB.ext hsC.ext) hz
    case forallE ty bd m =>
      obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_forallE_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo ty et _ _ (a2, m1) hok hpins
          ⟨hN, hU, hty, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 bd eb _ _ (b2, m2) hsA.ok
          (PinsOK.ofPStep hpins hsA)
          ⟨denoteNListE_ext hsA.ext _ _ hN, denoteLs_ext hU hsA.ext, denote_ext hbd hsA.ext,
           hmA⟩ hc2
        obtain ⟨q, sc, hc3, hn3⟩ := bindOk hn2
        obtain ⟨hsC, hq⟩ := internForallEE_run hsB.ok (denote_ext hrA hsB.ext) hrB hc3
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn3
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin ((hsA.trans hsB).trans hsC) (by rw [hq]; rfl) (hmB.ext hsC.ext) hz
    case letE lt lv lb =>
      obtain ⟨et, ev, eb, rfl, hty, hval, hbd⟩ := denote_letE_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo lt et _ _ (a2, m1) hok hpins
          ⟨hN, hU, hty, hm⟩ hc1
        obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
        obtain ⟨b2, m2⟩ := p2
        obtain ⟨hsB, hrB, hmB⟩ := ih m1 lv ev _ _ (b2, m2) hsA.ok
          (PinsOK.ofPStep hpins hsA)
          ⟨denoteNListE_ext hsA.ext _ _ hN, denoteLs_ext hU hsA.ext,
           denote_ext hval hsA.ext, hmA⟩ hc2
        have hAB := hsA.trans hsB
        obtain ⟨p3, sc, hc3, hn3⟩ := bindOk hn2
        obtain ⟨c2, m3⟩ := p3
        obtain ⟨hsC, hrC, hmC⟩ := ih m2 lb eb _ _ (c2, m3) hsB.ok
          (PinsOK.ofPStep hpins hAB)
          ⟨denoteNListE_ext hAB.ext _ _ hN, denoteLs_ext hU hAB.ext,
           denote_ext hbd hAB.ext, hmB⟩ hc3
        obtain ⟨q, sd, hc4, hn4⟩ := bindOk hn3
        obtain ⟨hsD, hq⟩ := internLetEE_run hsC.ok (denote_ext hrA (hsB.ext.trans hsC.ext))
          (denote_ext hrB hsC.ext) hrC hc4
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn4
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin ((hAB.trans hsC).trans hsD) (by rw [hq]; rfl) (hmC.ext hsD.ext) hz
    case proj pn pk psub =>
      obtain ⟨nm, es, rfl, hn, hsub⟩ := denote_proj_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨a2, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo psub es _ _ (a2, m1) hok hpins
          ⟨hN, hU, hsub, hm⟩ hc1
        obtain ⟨q, sc, hc3, hn3⟩ := bindOk hn1
        obtain ⟨hsC, hq⟩ := internProjE_run hsA.ok (denoteN_ext hn hsA.ext) hrA hc3
        obtain ⟨y, sy, hy, hz⟩ := bindOk hn3
        obtain ⟨rfl, rfl⟩ := pureOk hy
        exact fin (hsA.trans hsC) (by rw [hq]; rfl) (hmA.ext hsC.ext) hz

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1077-1079 Expr.replaceAppsFast
**`replaceApps` at `nestCanonSub`**: the pure `Expr.replaceApps`. -/
theorem replaceApps_spec (names : List NIdx) (namesP : List ConLeche.Name)
    (us : LsIdx) (usP : List Level) (b n : Nat) (e : EIdx) (eP : Expr) :
    PSpecP (fun st => Frontend.denoteNList st.ns names = some namesP ∧
        denoteLs st.lss us = some usP ∧ denoteE st e = some eP)
      (Arena.replaceApps names us b n e)
      (RE (Expr.replaceApps (ConLeche.nestCanonSub namesP usP n) b n eP)) := by
  intro s₀ s' r hok hpins hp hrun
  obtain ⟨hN, hU, hd⟩ := hp
  simp only [Arena.replaceApps] at hrun
  obtain ⟨q, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨hstep, hr, _⟩ := replaceAppsGo_spec names namesP us usP b n Arena.coreWalkFuel
    ∅ e eP s₀ s₁ q hok hpins ⟨hN, hU, hd, RAMemoOK.empty⟩ h1
  obtain ⟨rfl, rfl⟩ := pureOk h2
  exact ⟨hstep, hr⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1086-1087 nestPhs
The canonical parameter variables at `Sort 0`, one per index of the list. -/
theorem nestPhs_go :
    ∀ (l : List Nat),
    PSpecP PT (l.mapM fun i => do
        let z ← Arena.zeroLevel
        let s ← internSortE z
        internFVarE i s)
      (REL (l.map fun i => Expr.fvar i (.sort .zero))) := by
  intro l
  induction l with
  | nil =>
    intro s₀ s' r hok _ _ hrun
    simp only [List.mapM_nil] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons i is ih =>
    intro s₀ s' r hok hpins _ hrun
    simp only [List.mapM_cons] at hrun
    obtain ⟨x, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨z, t1, j1, y1⟩ := bindOk k1
    obtain ⟨rfl, hz⟩ := zeroLevel_run hpins j1
    obtain ⟨so, t2, j2, y2⟩ := bindOk y1
    obtain ⟨q2, hso⟩ := internSortE_run hok hz j2
    obtain ⟨q3, hx⟩ := internFVarE_run q2.ok hso y2
    have p1 := q2.trans q3
    obtain ⟨xs', s2, k2, z2⟩ := bindOk z1
    obtain ⟨p2, hxs⟩ := ih s1 s2 xs' p1.ok (PinsOK.ofPStep hpins p1) trivial k2
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨p1.trans p2, ?_⟩
    show Frontend.denoteEList _ (x :: xs') = _
    have hxs' : Frontend.denoteEList _ xs' = some _ := hxs
    simp only [Frontend.denoteEList, List.map_cons, denote_ext hx p2.ext, hxs']

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1086-1087 nestPhs
`fvar 0, …, fvar (n - 1)` at `Sort 0`. -/
theorem nestPhs_spec (n : Nat) :
    PSpecP PT (Arena.nestPhs n) (REL (ConLeche.nestPhs n)) := by
  intro s₀ s' r hok hpins hp hrun
  exact nestPhs_go (List.range n) s₀ s' r hok hpins hp hrun

/-! ## The list and record helpers, related -/

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:718-721 NestCtx.hiAt
The first hole-free index is the denoted context's. -/
theorem hiAt_eq {st : EStore} {fnd : ConLeche.Name → Option ConstantInfo}
    {ctx : Arena.NestCtx} {ctxP : ConLeche.NestCtx} (h : dCtx st fnd ctx = some ctxP)
    (nf : Nat) : ctx.hiAt nf = ctxP.hiAt nf := by
  obtain ⟨namesP, _, _, _, rfl, hN, _⟩ := dCtx_inv h
  simp only [Arena.NestCtx.hiAt, ConLeche.NestCtx.hiAt, denoteNList_length hN]

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:723-727 NestCtx.rootHoles
The root frame's entries denote the denoted context's: the interned `lvls`
IS `lps.map .param` (`dCtx`'s own clause). -/
theorem rootHoles_denote {st : EStore} {fnd : ConLeche.Name → Option ConstantInfo}
    {ctx : Arena.NestCtx} {ctxP : ConLeche.NestCtx} (h : dCtx st fnd ctx = some ctxP) :
    ctx.rootHoles.mapM (dHole st) = some ctxP.rootHoles := by
  obtain ⟨namesP, lpsP, paramsP, _, rfl, hN, _, hPa, _, hLv⟩ := dCtx_inv h
  simp only [Arena.NestCtx.rootHoles, ConLeche.NestCtx.rootHoles]
  clear h
  revert namesP
  induction ctx.names with
  | nil =>
    intro namesP hN
    simp only [Frontend.denoteNList, Option.some.injEq] at hN
    subst hN; rfl
  | cons a as ih =>
    intro namesP hN
    simp only [Frontend.denoteNList] at hN
    cases ha : denoteN st.ns a with
    | none => rw [ha] at hN; simp at hN
    | some x =>
      cases has : Frontend.denoteNList st.ns as with
      | none => rw [ha, has] at hN; simp at hN
      | some xs =>
        rw [ha, has] at hN
        obtain rfl := Option.some.inj hN
        simp only [List.map_cons, List.mapM_cons, ih xs has, dHole, dKey, ha, hLv, hPa,
          Option.bind_eq_bind, Option.pure_def, Option.bind_some, Option.map_some]

/-- con-leche: none — `Option`'s `mapM` at an index, as the `Option` lift. -/
theorem mapM_option_getElem? {α β : Type} {f : α → Option β} {st : EStore} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ∀ (j : Nat),
      ROp (fun y (_ : EStore) x => f x = some y) ys[j]? st xs[j]? := by
  intro xs
  induction xs with
  | nil =>
    intro ys h j
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    show ([] : List β)[j]? = none
    simp
  | cons x xs ih =>
    intro ys h j
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hx : f x with
    | none => rw [hx] at h; simp at h
    | some y =>
      rw [hx] at h
      cases hxs : xs.mapM f with
      | none => rw [hxs] at h; simp at h
      | some zs =>
        rw [hxs] at h
        simp only [Option.bind_some, Option.some.injEq] at h
        subst h
        cases j with
        | zero => exact ⟨y, rfl, hx⟩
        | succ j =>
          simp only [List.getElem?_cons_succ]
          exact ih hxs j

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:729-734 nestHoleAt
The hole `i`'s entry: the twin reads `rootHoles ++ prog` (outermost first),
con-leche `rootHoles ++ prog.reverse` (innermost first), and `dProg` is the
reversal between them. -/
theorem nestHoleAt_rel {st : EStore} {fnd : ConLeche.Name → Option ConstantInfo}
    {ctx : Arena.NestCtx} {ctxP : ConLeche.NestCtx} {prog : List Arena.NestHole}
    {progP : List ConLeche.NestHole} (hc : dCtx st fnd ctx = some ctxP)
    (hp : dProg st prog = some progP) (i : Nat) :
    ROp (fun hP (st : EStore) h => dHole st h = some hP)
      (ConLeche.nestHoleAt ctxP progP i) st (Arena.nestHoleAt ctx prog i) := by
  have hnP : ctx.nP = ctxP.nP := by
    obtain ⟨_, _, _, _, rfl, _⟩ := dCtx_inv hc; rfl
  simp only [dProg, Option.map_eq_some_iff] at hp
  obtain ⟨ys, hys, rfl⟩ := hp
  have hall : (ctx.rootHoles ++ prog).mapM (dHole st) =
      some (ctxP.rootHoles ++ ys.reverse.reverse) := by
    rw [List.mapM_append, rootHoles_denote hc, hys, List.reverse_reverse]
    simp
  simp only [Arena.nestHoleAt, ConLeche.nestHoleAt, hnP]
  split
  · have key := mapM_option_getElem? (st := st) hall (i - ctxP.nP)
    cases hx : (ctx.rootHoles ++ prog)[i - ctxP.nP]? with
    | none =>
      rw [hx] at key
      have k2 : (ctxP.rootHoles ++ ys.reverse.reverse)[i - ctxP.nP]? = none := key
      exact k2
    | some a =>
      rw [hx] at key
      obtain ⟨b, hb, hd⟩ := key
      exact ⟨b, hb, hd⟩
  · rfl

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:521-528 NestKey
(`DecidableEq`) — **a key comparison is a structural comparison**: the twin's
derived `BEq` is handle equality componentwise, and each component's handle
is its identity on a well-formed store. -/
theorem beq_key_eq {st : EStore} (hwf : StoreWF st) {k₁ k₂ : Arena.NestKey}
    {a b : ConLeche.NestKey} (h₁ : dKey st k₁ = some a) (h₂ : dKey st k₂ = some b) :
    (k₁ == k₂) = (a == b) := by
  obtain ⟨c1, l1, d1⟩ := dKey_inv h₁
  obtain ⟨c2, l2, d2⟩ := dKey_inv h₂
  have e1 := beq_handle_eq hwf c1 c2
  have e2 := beq_lshandle_eq hwf l1 l2
  have e3 := beq_ehandleList_eq hwf d1 d2
  obtain ⟨kc1, kl1, kd1⟩ := k₁
  obtain ⟨kc2, kl2, kd2⟩ := k₂
  obtain ⟨ac, al, ad⟩ := a
  obtain ⟨bc, bl, bd⟩ := b
  simp only at e1 e2 e3
  have hl : ((⟨kc1, kl1, kd1⟩ : Arena.NestKey) == ⟨kc2, kl2, kd2⟩) =
      (kc1 == kc2 && (kl1 == kl2 && kd1 == kd2)) := rfl
  rw [hl, e1, e2, e3]
  apply Bool.eq_iff_iff.mpr
  simp [ConLeche.NestKey.mk.injEq]

/-- con-leche: none — a key-list membership test is the denoted list's. -/
theorem contains_key_eq {st : EStore} (hwf : StoreWF st) {k : Arena.NestKey}
    {kP : ConLeche.NestKey} (hk : dKey st k = some kP) :
    ∀ {ks : List Arena.NestKey} {ksP : List ConLeche.NestKey},
      ks.mapM (dKey st) = some ksP → ks.contains k = ksP.contains kP := by
  intro ks
  induction ks with
  | nil =>
    intro ksP h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | cons a as ih =>
    intro ksP h
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases ha : dKey st a with
    | none => rw [ha] at h; simp at h
    | some x =>
      rw [ha] at h
      cases has : as.mapM (dKey st) with
      | none => rw [has] at h; simp at h
      | some xs =>
        rw [has] at h
        simp only [Option.bind_some, Option.some.injEq] at h
        subst h
        simp only [List.contains_cons, beq_key_eq hwf hk ha, ih has]

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:1318-1325 nestAcceptGroup
A frame's group accepted with its instantiation, key array for key array:
the group enters by its NAMES only (its second components, the holes' types,
are not read), the membership test is `contains_key_eq`. -/
theorem nestAcceptGroup_denote {st : EStore} (hwf : StoreWF st) {us : LsIdx}
    {usP : List Level} {ds : List EIdx} {dsP : List Expr}
    (hus : denoteLs st.lss us = some usP) (hds : Frontend.denoteEList st ds = some dsP) :
    ∀ (grp : List (NIdx × EIdx)) (grpP : List (ConLeche.Name × Expr))
      (keys : Array Arena.NestKey) (keysP : Array ConLeche.NestKey),
      Frontend.denoteNList st.ns (grp.map Prod.fst) = some (grpP.map Prod.fst) →
      keys.toList.mapM (dKey st) = some keysP.toList →
      (Arena.nestAcceptGroup us ds grp keys).toList.mapM (dKey st) =
        some (ConLeche.nestAcceptGroup usP dsP grpP keysP).toList := by
  intro grp
  induction grp with
  | nil =>
    intro grpP keys keysP hg hk
    cases grpP with
    | nil => exact hk
    | cons _ _ => simp [Frontend.denoteNList] at hg
  | cons g gs ih =>
    intro grpP keys keysP hg hk
    obtain ⟨c, x⟩ := g
    cases grpP with
    | nil =>
      simp only [List.map_cons, List.map_nil, Frontend.denoteNList] at hg
      split at hg <;> simp at hg
    | cons gP gsP =>
      obtain ⟨cP, xP⟩ := gP
      simp only [List.map_cons, Frontend.denoteNList] at hg
      cases hc : denoteN st.ns c with
      | none => rw [hc] at hg; simp at hg
      | some c' =>
        cases hr : Frontend.denoteNList st.ns (gs.map Prod.fst) with
        | none => rw [hc, hr] at hg; simp at hg
        | some r' =>
          rw [hc, hr] at hg
          obtain ⟨rfl, hr'⟩ := List.cons.inj (Option.some.inj hg)
          rw [hr'] at hr
          have hkey : dKey st ⟨c, us, ds⟩ = some ⟨c', usP, dsP⟩ := by
            simp only [dKey, hc, hus, hds, Option.bind_eq_bind, Option.bind_some,
              Option.pure_def]
          have hcont : keys.contains ⟨c, us, ds⟩ = keysP.contains ⟨c', usP, dsP⟩ := by
            rw [← Array.contains_toList, ← Array.contains_toList]
            exact contains_key_eq hwf hkey hk
          simp only [Arena.nestAcceptGroup, ConLeche.nestAcceptGroup]
          by_cases hin : keys.contains ⟨c, us, ds⟩ = true
          · have hinP : keysP.contains ⟨c', usP, dsP⟩ = true := by rw [← hcont]; exact hin
            rw [if_pos hin, if_pos hinP]
            exact ih gsP keys keysP hr hk
          · have hinP : ¬ keysP.contains ⟨c', usP, dsP⟩ = true := by rw [← hcont]; exact hin
            rw [if_neg hin, if_neg hinP]
            refine ih gsP _ _ hr ?_
            rw [Array.toList_push, Array.toList_push, List.mapM_append, hk]
            simp only [List.mapM_cons, List.mapM_nil, hkey, Option.bind_eq_bind,
              Option.pure_def, Option.bind_some]

end ConRon.Bridge.Inductives

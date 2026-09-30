/-
# `ConRon.Bridge.Inductives.ClassRead` — Theorem 1 for the recursor stage's pre-pass

`Arena/Inductives/ClassRead.lean` against `ConLeche/Kernel/Inductives/ClassRead.lean`
(task #105, lane B-IND): the pre-pass's records, denoted (`dClassKey`, `dSlot`,
`dClassRead`, each with a `DExt` transport), and an exact-result lemma for
every twin function, up to the headline `classRead_spec`.

The grade is PURE: the pre-pass interns free variables and instantiates, and
reads the index only through `classNPcOf`, so its statements are `PSpec` with
the index invariant `IFEnvOKS env fe` (a store predicate) in the
precondition.  Every `Option` answer is related TWO-SIDEDLY (`ROp`, or `RV` at
an `Option` of representation-free data): a `none` on one side and `some` on
the other would change which error the stage throws.

Con-leche's functions are written with `let .fvar p _ := e.getAppFn | none`
and similar do-blocks; the helpers `fvarHeadP`, `slotP`, `recClsP` and
`ihP` below are those blocks as named functions, each identified with the
inline one by `rfl` at its use.

**Helpers restated here that belong in shared files** (reported):
the telescope opener's run lemmas (`CR.denoteOpen`, `CR.openPisAtFvars_run`,
`CR.openPisAtFvarsFGo_run`, `CR.openPisAtFvarsF_run`) are
`Bridge/Inductives/SumInstall.lean`'s, restated because that module is far
above this one (their owner is the Checker tier); `CR.piBinders_run` is the
run form of `Arena/Inductives/FieldTele.lean`'s `piBinders`, whose own bridge
(`Bridge/Inductives/FieldTele.lean`) was not yet committed.
-/
import ConRon.Bridge.Inductives.Rel
import ConRon.Bridge.Inductives.PosWalks
import ConLeche.Verify.EnvBound

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The records, denoted -/

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:37-43 ClassKey — a
class over handles denotes con-leche's. -/
def dClassKey (st : EStore) (k : Arena.ClassKey) : Option ConLeche.ClassKey := do
  let ind ← denoteN st.ns k.ind
  let lvls ← denoteLs st.lss k.lvls
  let ds ← Frontend.denoteEList st k.ds
  pure ⟨ind, lvls, ds⟩

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:45-53 ClassSlot. -/
def dSlot (st : EStore) : Arena.ClassSlot → Option ConLeche.ClassSlot
  | .motive k => (dClassKey st k).map .motive
  | .minor c ctor ihs => (denoteN st.ns ctor).map fun n => .minor c n ihs

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:55-61 ClassRead. -/
def dClassRead (st : EStore) (r : Arena.ClassRead) : Option ConLeche.ClassRead :=
  (r.slots.mapM (dSlot st)).map fun slots => ⟨slots, r.recCls⟩

theorem dClassKey_ext : DExt dClassKey := by
  intro st st' hx k y h
  simp only [dClassKey] at h ⊢
  cases h1 : denoteN st.ns k.ind with
  | none => rw [h1] at h; exact nomatch h
  | some c =>
  cases h2 : denoteLs st.lss k.lvls with
  | none => rw [h1, h2] at h; exact nomatch h
  | some us =>
  cases h3 : Frontend.denoteEList st k.ds with
  | none => rw [h1, h2, h3] at h; exact nomatch h
  | some ds =>
  rw [h1, h2, h3] at h
  rw [denoteN_ext h1 hx, denoteLs_ext h2 hx, denoteEList_ext hx _ _ h3]
  exact h

theorem dSlot_ext : DExt dSlot := by
  intro st st' hx k y h
  cases k with
  | motive k =>
    simp only [dSlot, Option.map_eq_some_iff] at h ⊢
    obtain ⟨q, hq, rfl⟩ := h
    exact ⟨q, dClassKey_ext hx _ _ hq, rfl⟩
  | minor c n ihs =>
    simp only [dSlot, Option.map_eq_some_iff] at h ⊢
    obtain ⟨q, hq, rfl⟩ := h
    exact ⟨q, denoteN_ext hq hx, rfl⟩

theorem dClassRead_ext : DExt dClassRead := by
  intro st st' hx k y h
  simp only [dClassRead, Option.map_eq_some_iff] at h ⊢
  obtain ⟨q, hq, rfl⟩ := h
  exact ⟨q, dSlot_ext.list hx _ _ hq, rfl⟩

/-! ## Local helpers -/

namespace CR

open PW

/-- con-leche: none — an opener's answer denotes (`Bridge/Inductives/SumInstall.lean`'s
`denoteOpen`, restated: that module is far above this one). -/
def denoteOpen (st : EStore) :
    Option (List EIdx × EIdx) → Option (Option (List Expr × Expr))
  | none => some none
  | some (fvs, e) =>
    (Frontend.denoteEList st fvs).bind fun xs => (denoteE st e).map fun x => some (xs, x)

theorem denoteOpen_some {st : EStore} {fvs : List EIdx} {e : EIdx}
    {xs : List Expr} {x : Expr} (h1 : Frontend.denoteEList st fvs = some xs)
    (h2 : denoteE st e = some x) : denoteOpen st (some (fvs, e)) = some (some (xs, x)) := by
  simp [denoteOpen, h1, h2]

theorem denoteOpen_some_inv {st : EStore} {fvs : List EIdx} {e : EIdx}
    {o : Option (List Expr × Expr)} (h : denoteOpen st (some (fvs, e)) = some o) :
    ∃ xs x, o = some (xs, x) ∧ Frontend.denoteEList st fvs = some xs ∧
      denoteE st e = some x := by
  simp only [denoteOpen, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨xs, h1, x, h2, rfl⟩ := h
  exact ⟨xs, x, rfl, h1, h2⟩

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:121-128 openPisAtFvars — the
binder-at-a-time opener, as a run (`SumInstall.lean`'s, restated). -/
theorem openPisAtFvars_run : ∀ (n : Nat) {i : Nat} {h : EIdx} {hP : Expr}
    {s₀ s' : AState} {r : Option (List EIdx × EIdx)},
    StateOK s₀ → denoteE s₀.store h = some hP →
    Arena.openPisAtFvars n h i s₀ = .ok (r, s') →
    PStep s₀ s' ∧ denoteOpen s'.store r = some (ConLeche.openPisAtFvars n hP i) := by
  intro n
  induction n with
  | zero =>
    intro i h hP s₀ s' r hok hh hrun
    simp only [Arena.openPisAtFvars] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, by simp [denoteOpen, Frontend.denoteEList, hh,
      ConLeche.openPisAtFvars]⟩
  | succ n ih =>
    intro i h hP s₀ s' r hok hh hrun
    simp only [Arena.openPisAtFvars] at hrun
    obtain ⟨v₀, hv₀⟩ := denoteE_view hh
    replace hrun := tagIf_view_run hv₀
      (fun hne => by cases v₀ <;> first | rfl | exact absurd rfl hne) hrun
    obtain ⟨v, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨hs1, hv⟩ := view_run k1
    rw [hs1] at z1
    cases v
    case forallE dom body bm =>
      obtain ⟨domP, bodyP, rfl, hd, hb⟩ := denote_forallE_inv hok.wf hv hh
      dsimp only at z1
      obtain ⟨fv, s2, k2, z2⟩ := bindOk z1
      obtain ⟨p2, hfv⟩ := internE_run hok (viewOK_fvar (by rw [hd]; rfl)) k2
      have hfv' : denoteE s2.store fv = some (.fvar i domP) := by
        rw [hfv]; simp [denoteEView, denote_ext hd p2.ext]
      obtain ⟨op, s3, k3, z3⟩ := bindOk z2
      have hb2 : denoteE s2.store body = some bodyP := denote_ext hb p2.ext
      obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := ExprOps.instantiate1Fast_run p2.ok hfv'
        (by rw [hb2]; rfl) k3
      have p3 : PStep s2 s3 := PStep.of_caches h1 h2 h3 h4 h5
      have hop : denoteE s3.store op = some (bodyP.instantiate1 (.fvar i domP) 0) :=
        h7 _ hb2
      obtain ⟨o, s4, k4, z4⟩ := bindOk z3
      obtain ⟨p4, ho⟩ := ih p3.ok hop k4
      have p24 := p2.trans (p3.trans p4)
      simp only [ConLeche.openPisAtFvars]
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := pureOk z4
        refine ⟨p24, ?_⟩
        have hn : ConLeche.openPisAtFvars n (bodyP.instantiate1 (.fvar i domP)) (i + 1)
            = none := (Option.some.inj ho).symm
        simp [denoteOpen, hn]
      | some q =>
        obtain ⟨fvs, e⟩ := q
        obtain ⟨xs, x, hx, h1, h2⟩ := denoteOpen_some_inv ho
        obtain ⟨rfl, rfl⟩ := pureOk z4
        refine ⟨p24, ?_⟩
        rw [hx]
        exact denoteOpen_some (by
          simp only [Frontend.denoteEList, denote_ext hfv' (p3.ext.trans p4.ext),
            h1]) h2
    all_goals
      obtain ⟨rfl, rfl⟩ := pureOk z1
      refine ⟨PStep.refl hok, ?_⟩
      rw [denoteE_view_eq hok.wf hv] at hh
      cases hP
      case forallE a b m => simp [denoteEView] at hh
      all_goals rfl

theorem InstLVec_push {st : EStore} {acc : Array EIdx} {ws : List Expr} {x : EIdx}
    {xP : Expr} (h : ExprOps.InstLVec st acc ws) (hx : denoteE st x = some xP) :
    ExprOps.InstLVec st (acc.push x) (xP :: ws) := by
  simp only [ExprOps.InstLVec, Array.toList_push, List.reverse_cons]
  exact denoteEList_append h (by simp [Frontend.denoteEList, hx])

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:136-144 openPisAtFvarsFGo — the
one-pass opener's core, as a run (`SumInstall.lean`'s, restated). -/
theorem openPisAtFvarsFGo_run : ∀ (n : Nat) {acc : Array EIdx} {ws : List Expr}
    {i : Nat} {h : EIdx} {hP : Expr} {s₀ s' : AState} {r : Option (List EIdx × EIdx)},
    StateOK s₀ → ExprOps.InstLVec s₀.store acc ws → denoteE s₀.store h = some hP →
    Arena.openPisAtFvarsFGo acc n h i s₀ = .ok (r, s') →
    PStep s₀ s' ∧ denoteOpen s'.store r = some (ConLeche.openPisAtFvarsFGo ws n hP i) := by
  intro n
  induction n with
  | zero =>
    intro acc ws i h hP s₀ s' r hok hacc hh hrun
    simp only [Arena.openPisAtFvarsFGo] at hrun
    obtain ⟨e, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := ExprOps.instantiateListFast_run hok hacc
      (by rw [hh]; rfl) k1
    obtain ⟨rfl, rfl⟩ := pureOk z1
    refine ⟨PStep.of_caches h1 h2 h3 h4 h5, ?_⟩
    simp [denoteOpen, Frontend.denoteEList, h7 _ hh, ConLeche.openPisAtFvarsFGo]
  | succ n ih =>
    intro acc ws i h hP s₀ s' r hok hacc hh hrun
    simp only [Arena.openPisAtFvarsFGo] at hrun
    obtain ⟨v₀, hv₀⟩ := denoteE_view hh
    replace hrun := tagIf_view_run hv₀
      (fun hne => by cases v₀ <;> first | rfl | exact absurd rfl hne) hrun
    obtain ⟨v, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨hs1, hv⟩ := view_run k1
    rw [hs1] at z1
    cases v
    case forallE dom body bm =>
      obtain ⟨domP, bodyP, rfl, hd, hb⟩ := denote_forallE_inv hok.wf hv hh
      dsimp only at z1
      obtain ⟨dd, s2, k2, z2⟩ := bindOk z1
      obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := ExprOps.instantiateListFast_run hok hacc
        (by rw [hd]; rfl) k2
      have p2 : PStep s₀ s2 := PStep.of_caches h1 h2 h3 h4 h5
      have hdd : denoteE s2.store dd = some (domP.instantiateList ws 0) := h7 _ hd
      obtain ⟨fv, s3, k3, z3⟩ := bindOk z2
      obtain ⟨p3, hfv⟩ := internE_run p2.ok (viewOK_fvar (by rw [hdd]; rfl)) k3
      have hfv' : denoteE s3.store fv = some (.fvar i (domP.instantiateList ws 0)) := by
        rw [hfv]; simp [denoteEView, denote_ext hdd p3.ext]
      obtain ⟨o, s4, k4, z4⟩ := bindOk z3
      obtain ⟨p4, ho⟩ := ih p3.ok (InstLVec_push (hacc.ext (p2.ext.trans p3.ext)) hfv')
        (denote_ext hb (p2.ext.trans p3.ext)) k4
      have p24 := p2.trans (p3.trans p4)
      simp only [ConLeche.openPisAtFvarsFGo]
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := pureOk z4
        refine ⟨p24, ?_⟩
        have hn : ConLeche.openPisAtFvarsFGo (.fvar i (domP.instantiateList ws) :: ws) n
            bodyP (i + 1) = none := (Option.some.inj ho).symm
        simp [denoteOpen, hn]
      | some q =>
        obtain ⟨fvs, e⟩ := q
        obtain ⟨xs, x, hx, h1, h2⟩ := denoteOpen_some_inv ho
        obtain ⟨rfl, rfl⟩ := pureOk z4
        refine ⟨p24, ?_⟩
        rw [hx]
        exact denoteOpen_some (by
          simp only [Frontend.denoteEList, denote_ext hfv' p4.ext, h1]) h2
    all_goals
      obtain ⟨rfl, rfl⟩ := pureOk z1
      refine ⟨PStep.refl hok, ?_⟩
      rw [denoteE_view_eq hok.wf hv] at hh
      cases hP
      case forallE a b m => simp [denoteEView] at hh
      all_goals rfl

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:149-155 openPisAtFvarsF — the
one-pass opener, as a run, answering con-leche's binder-at-a-time
`openPisAtFvars` through `openPisAtFvarsF_eq` (`SumInstall.lean`'s, restated). -/
theorem openPisAtFvarsF_run {n i : Nat} {h : EIdx} {hP : Expr} {s₀ s' : AState}
    {r : Option (List EIdx × EIdx)} (hok : StateOK s₀)
    (hh : denoteE s₀.store h = some hP)
    (hrun : Arena.openPisAtFvarsF n h i s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ denoteOpen s'.store r = some (ConLeche.openPisAtFvars n hP i) := by
  rw [← ConLeche.openPisAtFvarsF_eq]
  simp only [Arena.openPisAtFvarsF] at hrun
  obtain ⟨o, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, ho⟩ := openPisAtFvarsFGo_run n hok
    (show ExprOps.InstLVec s₀.store #[] [] from rfl) hh k1
  simp only [ConLeche.openPisAtFvarsF]
  cases o with
  | some q =>
    obtain ⟨fvs, e⟩ := q
    obtain ⟨xs, x, hx, h1, h2⟩ := denoteOpen_some_inv ho
    obtain ⟨rfl, rfl⟩ := pureOk z1
    refine ⟨p1, ?_⟩
    rw [hx]
    exact denoteOpen_some h1 h2
  | none =>
    have hn : ConLeche.openPisAtFvarsFGo [] n hP i = none := (Option.some.inj ho).symm
    rw [hn]
    obtain ⟨p2, h2⟩ := openPisAtFvars_run n p1.ok (denote_ext hh p1.ext) z1
    exact ⟨p1.trans p2, h2⟩

/-- con-leche: ConLeche/Kernel/Inductives/FieldTele.lean:48-52 Expr.piBinders —
the twin's telescope reader, as a run: read-only, the binders and the body
denote con-leche's. -/
theorem piBinders_run : ∀ (fuel : Nat) {h : EIdx} {hP : Expr} {s₀ s' : AState}
    {r : List (EIdx × BinderMeta) × EIdx},
    StateOK s₀ → denoteE s₀.store h = some hP →
    Arena.piBinders fuel h s₀ = .ok (r, s') →
    s' = s₀ ∧ denoteBinders s₀.store r.1 = some hP.piBinders.1 ∧
      denoteE s₀.store r.2 = some hP.piBinders.2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro h hP s₀ s' r _ _ hrun
    simp only [Arena.piBinders] at hrun
    exact absurd hrun (fun hc => failOk hc)
  | succ n ih =>
    intro h hP s₀ s' r hok hd hrun
    simp only [Arena.piBinders] at hrun
    by_cases htg : (h.tag == ETag.forallE) = true
    · rw [if_pos htg] at hrun
      obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
      obtain ⟨hs1, ho⟩ := viewBind_run h1
      subst hs1
      cases o with
      | none => exact absurd h2 (fun hc => failDanglingE_ok hc)
      | some p =>
        obtain ⟨d, b, m⟩ := p
        have hw := view_of_viewBind_tag_forallE htg ho.symm
        obtain ⟨dP, bP, rfl, hdd, hbd⟩ := denote_forallE_inv hok.wf hw hd
        dsimp only at h2
        obtain ⟨q, s₂, h3, h4⟩ := bindOk h2
        obtain ⟨rfl, hq1, hq2⟩ := ih hok hbd h3
        obtain ⟨rfl, rfl⟩ := pureOk h4
        refine ⟨rfl, ?_, hq2⟩
        simp [denoteBinders, hdd, hq1, Expr.piBinders]
    · rw [if_neg htg] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      refine ⟨rfl, ?_⟩
      cases hP with
      | forallE d b m => exact absurd (tag_forallE_of_denote hok.wf hd) (by simpa using htg)
      | _ => exact ⟨rfl, hd⟩

/-- con-leche: none — a `sort`-tagged denoting handle denotes a sort. -/
theorem sort_of_tag {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr}
    (htg : (h.tag == ETag.sort) = true) (hd : denoteE st h = some e) :
    ∃ u, e = .sort u := by
  obtain ⟨v, _, ht, hv⟩ := denote_view_tag hwf hd
  rw [ht] at htg
  cases v with
  | sort u =>
    simp only [denoteEView, Option.map_eq_some_iff] at hv
    obtain ⟨l, -, rfl⟩ := hv
    exact ⟨l, rfl⟩
  | _ => revert htg; simp only [ENodeView.tagOf, beq_iff_eq]; intro hc; exact absurd hc (by decide)

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1355-1357 piResult — the run form of
`Bridge/ExprOps/Spine.lean`'s `piResult_spec` (`Bridge/Frontend/ProjRec.lean`'s
`piResult_run`, restated: that module is not in this one's import closure). -/
theorem piResult_run {fuel : Nat} {s s' : AState} {h r : EIdx} {e : Expr}
    (hok : StateOK s) (hd : denoteE s.store h = some e)
    (hrun : Arena.piResult fuel h s = .ok (r, s')) :
    s' = s ∧ denoteE s.store r = some e.piResult := by
  obtain ⟨h1, h2⟩ := AM.of_run (P := fun t => t = s) rfl hrun
    (ExprOps.piResult_spec fuel s h hok (by rw [hd]; rfl))
  exact ⟨h1, h2 e hd⟩

/-- con-leche: none — and a sort denotes only at a `sort`-tagged handle. -/
theorem tag_sort_of_denote {st : EStore} (hwf : StoreWF st) {h : EIdx} {u : Level}
    (hd : denoteE st h = some (.sort u)) : h.tag = ETag.sort := by
  obtain ⟨v, _, ht, hv⟩ := denote_view_tag hwf hd
  rw [ht]
  cases v <;> simp_all [denoteEView, opt2_eq_some_iff, opt3_eq_some_iff] <;> rfl

/-- con-leche: none — a denoting handle list's last element, both ways. -/
theorem denoteEList_getLast? {st : EStore} {hs : List EIdx} {xs : List Expr}
    (h : Frontend.denoteEList st hs = some xs) :
    (hs.getLast? = none → xs.getLast? = none) ∧
      ∀ a, hs.getLast? = some a → ∃ x, xs.getLast? = some x ∧ denoteE st a = some x := by
  have hl := denoteEList_length h
  have hg := denoteEList_getElem? h (hs.length - 1)
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, ← hl]
  exact ⟨hg.1.mp, hg.2⟩

end CR

/-! ## `classOfMotiveVar`, `fvarHead` -/

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:77-80 classOfMotiveVar
— the twin IS con-leche's function (representation-free arguments). -/
theorem classOfMotiveVar_eq : Arena.classOfMotiveVar = ConLeche.classOfMotiveVar := rfl

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:86 classReadMinor — the
reading `let .fvar p _ := e.getAppFn | none`, as a function. -/
def fvarHeadP (e : Expr) : Option Nat :=
  match e.getAppFn with
  | .fvar p _ => some p
  | _ => none

theorem fvarHeadP_some {e : Expr} {p : Nat} (h : fvarHeadP e = some p) :
    ∃ t, e.getAppFn = .fvar p t := by
  unfold fvarHeadP at h
  split at h
  · cases h; exact ⟨_, ‹_›⟩
  · cases h

theorem fvarHeadP_none {e : Expr} (h : fvarHeadP e = none) :
    ∀ p t, e.getAppFn ≠ .fvar p t := by
  intro p t he
  simp [fvarHeadP, he] at h

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:86 classReadMinor
(`.fvar p _ := concl.getAppFn`) — `fvarHead`, as a run: read-only, and its
answer is `fvarHeadP` of the denotation. -/
theorem fvarHead_run {e : EIdx} {eP : Expr} {s₀ s' : AState} {r : Option Nat}
    (hok : StateOK s₀) (hd : denoteE s₀.store e = some eP)
    (hrun : Arena.fvarHead e s₀ = .ok (r, s')) : s' = s₀ ∧ r = fvarHeadP eP := by
  simp only [Arena.fvarHead] at hrun
  obtain ⟨hdh, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨rfl, hhd⟩ := getAppFn_run hok hd h1
  by_cases htg : (hdh.tag == ETag.fvar) = true
  · rw [if_pos htg] at h2
    obtain ⟨o, s₂, h3, h4⟩ := bindOk h2
    obtain ⟨rfl, ho⟩ := PW.viewFVarIdx_run h3
    cases o with
    | none => exact absurd h4 (fun hc => PW.failDanglingE_ok hc)
    | some p =>
      obtain ⟨rfl, rfl⟩ := pureOk h4
      obtain ⟨t, ht⟩ := PW.denote_of_viewFVarIdx hok.wf htg ho.symm hhd
      exact ⟨rfl, by simp [fvarHeadP, ht]⟩
  · rw [if_neg htg] at h2
    obtain ⟨rfl, rfl⟩ := pureOk h2
    refine ⟨rfl, ?_⟩
    unfold fvarHeadP
    split
    · rename_i p t hg
      rw [hg] at hhd
      exact absurd (PW.tag_fvar_of_denote hok.wf hhd) (by simpa using htg)
    · rfl

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:86 classReadMinor —
`fvarHead` at the pure grade. -/
theorem fvarHead_spec (e : EIdx) (eP : Expr) :
    PSpec (fun st => denoteE st e = some eP) (Arena.fvarHead e) (RV (fvarHeadP eP)) := by
  intro s₀ s' r hok hd hrun
  obtain ⟨rfl, rfl⟩ := fvarHead_run hok hd hrun
  exact ⟨PStep.refl hok, rfl⟩

/-! ## `classReadMinor` -/

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:90-103 classReadMinor —
one binder's inductive-hypothesis reading, as a function over the binder's
free variable. -/
def ihP (nP : Nat) (motPos : List Nat) (d : Nat) (x : Expr) : Option (Nat × Nat) :=
  (fvarHeadP x.fvarTypeD.piResult).bind fun p2 =>
    (ConLeche.classOfMotiveVar nP motPos p2).bind fun t =>
      x.fvarTypeD.piResult.getAppArgs.getLast?.bind fun a =>
        (fvarHeadP a).bind fun f => if d ≤ f then some (f - d, t) else none

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:92 classReadMinor — a
`filterMap` over the positions of a list, reading the list at each, is the
list's own `filterMap`. -/
theorem range_filterMap {α β : Type} [Inhabited α] :
    ∀ (l : List α) (F : Nat → Option β) (G : α → Option β),
      (∀ q, q < l.length → F q = G (l.getD q default)) →
      (List.range l.length).filterMap F = l.filterMap G := by
  intro l
  induction l with
  | nil => intro F G _; rfl
  | cons a l ih =>
    intro F G h
    rw [List.length_cons, List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map,
      List.filterMap_cons,
      ih (F ∘ Nat.succ) G (fun q hq => by
        simpa using h (q + 1) (by simp [hq]))]
    rw [h 0 (by simp)]
    rfl

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:82-105 classReadMinor —
con-leche's function in bind form (`classReadMinor_eq`). -/
def classReadMinorP (nP : Nat) (motPos : List Nat) (d : Nat) (dom : Expr) :
    Option ConLeche.ClassSlot :=
  (ConLeche.openPisAtFvars dom.piBinders.1.length dom d).bind fun (fvs, concl) =>
    (fvarHeadP concl).bind fun p =>
      (ConLeche.classOfMotiveVar nP motPos p).bind fun c =>
        concl.getAppArgs.getLast?.bind fun last =>
          match last.getAppFn with
          | .const C _ => some (.minor c C (fvs.filterMap (ihP nP motPos d)))
          | _ => none

theorem classReadMinor_eq (nP : Nat) (motPos : List Nat) (d : Nat) (dom : Expr) :
    ConLeche.classReadMinor nP motPos d dom = classReadMinorP nP motPos d dom := by
  unfold ConLeche.classReadMinor classReadMinorP
  cases ho : ConLeche.openPisAtFvars dom.piBinders.1.length dom d with
  | none => simp [ho]
  | some q =>
    obtain ⟨fvs, concl⟩ := q
    simp only [ho, Option.bind_eq_bind, Option.bind_some]
    cases hg : concl.getAppFn with
    | fvar p t =>
      simp only [fvarHeadP, hg, Option.bind_some]
      cases hc : ConLeche.classOfMotiveVar nP motPos p with
      | none => rfl
      | some c =>
        simp only [Option.bind_some]
        cases hl : concl.getAppArgs.getLast? with
        | none => rfl
        | some last =>
          simp only [Option.bind_some]
          cases hlg : last.getAppFn with
          | const C us =>
            simp only [pure, Option.some.injEq, ConLeche.ClassSlot.minor.injEq, true_and]
            apply range_filterMap
            intro q _
            generalize fvs.getD q default = x
            unfold ihP fvarHeadP
            split
            · rename_i p' t' hx
              simp only [hx, Option.bind_some]
              cases ConLeche.classOfMotiveVar nP motPos p' with
              | none => rfl
              | some tt =>
                simp only [Option.bind_some]
                cases x.fvarTypeD.piResult.getAppArgs.getLast? with
                | none => rfl
                | some a =>
                  simp only [Option.bind_some]
                  split <;> simp_all
            · rename_i hx
              split
              · rename_i p' t' hx'
                exact absurd hx' (hx p' t')
              · rfl
          | _ => rfl
    | _ => simp [fvarHeadP, hg]

/-- con-leche: none — `List.filterMapM` in `AM` over a denoting handle list,
from a per-element run lemma. -/
theorem filterMapM_run {β : Type} {f : EIdx → AM (Option β)} {g : Expr → Option β}
    (hf : ∀ x xP s s' o, StateOK s → denoteE s.store x = some xP → f x s = .ok (o, s') →
      PStep s s' ∧ o = g xP) :
    ∀ (xs : List EIdx) (xsP : List Expr) (s s' : AState) (r : List β), StateOK s →
      Frontend.denoteEList s.store xs = some xsP → xs.filterMapM f s = .ok (r, s') →
      PStep s s' ∧ r = xsP.filterMap g := by
  intro xs
  induction xs with
  | nil =>
    intro xsP s s' r hok hd hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at hd
    subst hd
    rw [List.filterMapM_nil] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons a as ih =>
    intro xsP s s' r hok hd hrun
    simp only [Frontend.denoteEList] at hd
    cases ha : denoteE s.store a with
    | none => rw [ha] at hd; simp at hd
    | some aP =>
    cases has : Frontend.denoteEList s.store as with
    | none => rw [ha, has] at hd; simp at hd
    | some asP =>
    rw [ha, has] at hd
    obtain rfl := Option.some.inj hd
    rw [List.filterMapM_cons] at hrun
    obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨p1, rfl⟩ := hf a aP s s₁ o hok ha h1
    have has' := denoteEList_ext p1.ext _ _ has
    cases hg : g aP with
    | none =>
      rw [hg] at h2
      obtain ⟨p2, rfl⟩ := ih asP s₁ s' r p1.ok has' h2
      exact ⟨p1.trans p2, by simp [hg]⟩
    | some b =>
      rw [hg] at h2
      obtain ⟨rs, s₂, h3, h4⟩ := bindOk h2
      obtain ⟨p2, rfl⟩ := ih asP s₁ s₂ rs p1.ok has' h3
      obtain ⟨rfl, rfl⟩ := pureOk h4
      exact ⟨p1.trans p2, by simp [hg]⟩

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:82-105 classReadMinor —
**one minor premise read**, at the pure grade, two-sided on the `Option`. -/
theorem classReadMinor_spec (nP : Nat) (motPos : List Nat) (d : Nat) (dom : EIdx)
    (domP : Expr) :
    PSpec (fun st => denoteE st dom = some domP) (Arena.classReadMinor nP motPos d dom)
      (ROp (fun q st r => dSlot st r = some q) (ConLeche.classReadMinor nP motPos d domP)) := by
  intro s₀ s' r hok hd hrun
  rw [classReadMinor_eq]
  unfold classReadMinorP
  simp only [Arena.classReadMinor] at hrun
  obtain ⟨⟨bs, e⟩, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨rfl, hbs, -⟩ := CR.piBinders_run _ hok hd h1
  rw [denoteBinders_length hbs] at h2
  obtain ⟨o, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨p3, ho⟩ := CR.openPisAtFvarsF_run hok hd h3
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk h4
    refine ⟨p3, ?_⟩
    have hn := (Option.some.inj ho).symm
    simp [ROp, hn]
  | some q =>
  obtain ⟨fvs, concl⟩ := q
  obtain ⟨fvsP, conclP, hq, hfvs, hconcl⟩ := CR.denoteOpen_some_inv ho
  rw [hq]
  simp only [Option.bind_some]
  dsimp only at h4
  obtain ⟨hp, s₃, h5, h6⟩ := bindOk h4
  obtain ⟨rfl, rfl⟩ := fvarHead_run p3.ok hconcl h5
  cases hfp : fvarHeadP conclP with
  | none =>
    rw [hfp] at h6
    obtain ⟨rfl, rfl⟩ := pureOk h6
    exact ⟨p3, rfl⟩
  | some p =>
  rw [hfp] at h6
  simp only [Option.bind_some]
  dsimp only at h6
  rw [classOfMotiveVar_eq] at h6
  cases hc : ConLeche.classOfMotiveVar nP motPos p with
  | none =>
    rw [hc] at h6
    obtain ⟨rfl, rfl⟩ := pureOk h6
    exact ⟨p3, rfl⟩
  | some c =>
  rw [hc] at h6
  simp only [Option.bind_some]
  dsimp only at h6
  obtain ⟨args, s₄, h7, h8⟩ := bindOk h6
  obtain ⟨rfl, hargs⟩ := getAppArgs_run p3.ok hconcl h7
  obtain ⟨hl1, hl2⟩ := CR.denoteEList_getLast? hargs
  cases hl : args.getLast? with
  | none =>
    rw [hl] at h8
    obtain ⟨rfl, rfl⟩ := pureOk h8
    refine ⟨p3, ?_⟩
    simp [ROp, hl1 hl]
  | some last =>
  rw [hl] at h8
  obtain ⟨lastP, hlP, hlast⟩ := hl2 last hl
  rw [hlP]
  simp only [Option.bind_some]
  dsimp only at h8
  obtain ⟨hdh, s₅, h9, h10⟩ := bindOk h8
  obtain ⟨rfl, hhd⟩ := getAppFn_run p3.ok hlast h9
  by_cases htg : (hdh.tag == ETag.const) = true
  · rw [if_pos htg] at h10
    obtain ⟨o, s₆, h11, h12⟩ := bindOk h10
    obtain ⟨rfl, ho⟩ := PW.viewConst_run h11
    cases o with
    | none => exact absurd h12 (fun hc => PW.failDanglingE_ok hc)
    | some pr =>
    obtain ⟨cn, us⟩ := pr
    have hw := view_of_viewConst_tag htg ho.symm
    obtain ⟨nm, ls, hgl, hn, -⟩ := denote_const_inv p3.ok.wf hw hhd
    rw [hgl]
    dsimp only at h12
    obtain ⟨ihs, s₇, h13, h14⟩ := bindOk h12
    obtain ⟨p13, rfl⟩ := filterMapM_run (g := ihP nP motPos d) (by
      intro x xP s s'' o hs hx hrun'
      obtain ⟨ty, t1, k1, z1⟩ := bindOk hrun'
      obtain ⟨rfl, hty⟩ := fvarTypeD_run hs hx k1
      obtain ⟨rr, t2, k2, z2⟩ := bindOk z1
      obtain ⟨rfl, hrr⟩ := CR.piResult_run hs hty k2
      obtain ⟨o2, t3, k3, z3⟩ := bindOk z2
      obtain ⟨rfl, rfl⟩ := fvarHead_run hs hrr k3
      unfold ihP
      cases hf1 : fvarHeadP xP.fvarTypeD.piResult with
      | none =>
        rw [hf1] at z3
        obtain ⟨rfl, rfl⟩ := pureOk z3
        exact ⟨PStep.refl hs, rfl⟩
      | some p2 =>
      rw [hf1] at z3
      simp only [Option.bind_some]
      dsimp only at z3
      cases hc2 : ConLeche.classOfMotiveVar nP motPos p2 with
      | none =>
        rw [hc2] at z3
        obtain ⟨rfl, rfl⟩ := pureOk z3
        exact ⟨PStep.refl hs, rfl⟩
      | some t =>
      rw [hc2] at z3
      simp only [Option.bind_some]
      dsimp only at z3
      obtain ⟨rargs, t4, k4, z4⟩ := bindOk z3
      obtain ⟨rfl, hra⟩ := getAppArgs_run hs hrr k4
      obtain ⟨hr1, hr2⟩ := CR.denoteEList_getLast? hra
      cases hrl : rargs.getLast? with
      | none =>
        rw [hrl] at z4
        obtain ⟨rfl, rfl⟩ := pureOk z4
        exact ⟨PStep.refl hs, by simp [hr1 hrl]⟩
      | some a =>
      rw [hrl] at z4
      obtain ⟨aP, haP, ha⟩ := hr2 a hrl
      rw [haP]
      simp only [Option.bind_some]
      dsimp only at z4
      obtain ⟨o5, t5, k5, z5⟩ := bindOk z4
      obtain ⟨rfl, rfl⟩ := fvarHead_run hs ha k5
      cases hf5 : fvarHeadP aP with
      | none =>
        rw [hf5] at z5
        obtain ⟨rfl, rfl⟩ := pureOk z5
        exact ⟨PStep.refl hs, rfl⟩
      | some f =>
        rw [hf5] at z5
        obtain ⟨rfl, rfl⟩ := pureOk z5
        exact ⟨PStep.refl hs, rfl⟩) fvs fvsP _ _ _ p3.ok (denoteEList_ext (PStep.refl p3.ok).ext _ _ hfvs) h13
    obtain ⟨rfl, rfl⟩ := pureOk h14
    refine ⟨p3.trans p13, ?_⟩
    exact ⟨_, rfl, by simp [dSlot, denoteN_ext hn p13.ext]⟩
  · rw [if_neg htg] at h10
    obtain ⟨rfl, rfl⟩ := pureOk h10
    refine ⟨p3, ?_⟩
    show _ = none
    split
    · rename_i C us hg
      rw [hg] at hhd
      exact absurd (PW.tag_const_of_denote p3.ok.wf hhd) (by simpa using htg)
    · rfl

/-! ## `ClassRead.classes`, `ClassRead.motiveSlot` -/

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:65-67 ClassRead.classes —
the classes of a denoting slot list denote con-leche's (the twin takes the
slot list, con-leche the record: any `recCls`). -/
theorem classes_denote {st : EStore} (rc : List Nat) :
    ∀ {slots : List Arena.ClassSlot} {slotsP : List ConLeche.ClassSlot},
      slots.mapM (dSlot st) = some slotsP →
      (Arena.ClassRead.classes slots).mapM (dClassKey st) =
        some (ConLeche.ClassRead.classes ⟨slotsP, rc⟩) := by
  intro slots
  simp only [Arena.ClassRead.classes, ConLeche.ClassRead.classes]
  induction slots with
  | nil =>
    intro slotsP h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | cons x xs ih =>
    intro slotsP h
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases hx : dSlot st x with
    | none => rw [hx] at h; simp at h
    | some y =>
    rw [hx] at h
    cases hxs : xs.mapM (dSlot st) with
    | none => rw [hxs] at h; simp at h
    | some ys =>
    rw [hxs] at h
    simp only [Option.bind_some, Option.some.injEq] at h
    subst h
    have ih' := ih hxs
    cases x with
    | motive k =>
      simp only [dSlot, Option.map_eq_some_iff] at hx
      obtain ⟨kP, hk, rfl⟩ := hx
      simp only [List.filterMap_cons, List.mapM_cons, hk, ih', Option.bind_eq_bind,
        Option.bind_some, Option.pure_def]
    | minor c n ihs =>
      simp only [dSlot, Option.map_eq_some_iff] at hx
      obtain ⟨nP, -, rfl⟩ := hx
      simpa only [List.filterMap_cons] using ih'

/-- con-leche: none — the motive filter over a denoting slot list: any two
predicates that both test "is a motive" select the same positions. -/
theorem motive_filter_eq {st : EStore} {slots : List Arena.ClassSlot}
    {slotsP : List ConLeche.ClassSlot} (h : slots.mapM (dSlot st) = some slotsP)
    (pA : Option Arena.ClassSlot → Bool) (pC : Option ConLeche.ClassSlot → Bool)
    (hA : ∀ o, pA o = match o with | some (.motive _) => true | _ => false)
    (hC : ∀ o, pC o = match o with | some (.motive _) => true | _ => false) :
    (List.range slots.length).filter (fun s => pA slots[s]?) =
      (List.range slotsP.length).filter (fun s => pC slotsP[s]?) := by
  rw [mapM_option_length h]
  apply List.filter_congr
  intro j _
  have hj := mapM_option_getElem? (st := st) h j
  rw [hA, hC]
  cases hs : slots[j]? with
  | none =>
    rw [hs] at hj
    simp only [ROp] at hj
    rw [hj]
  | some x =>
    rw [hs] at hj
    obtain ⟨y, hy, hxy⟩ := hj
    rw [hy]
    cases x with
    | motive k =>
      simp only [dSlot, Option.map_eq_some_iff] at hxy
      obtain ⟨_, _, rfl⟩ := hxy
      rfl
    | minor c n ihs =>
      simp only [dSlot, Option.map_eq_some_iff] at hxy
      obtain ⟨_, _, rfl⟩ := hxy
      rfl

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:69-73 ClassRead.motiveSlot
— over a denoting slot list, the twin's answer IS con-leche's. -/
theorem motiveSlot_eq {st : EStore} {slots : List Arena.ClassSlot}
    {slotsP : List ConLeche.ClassSlot} (rc : List Nat)
    (h : slots.mapM (dSlot st) = some slotsP) (c : Nat) :
    Arena.ClassRead.motiveSlot slots c = ConLeche.ClassRead.motiveSlot ⟨slotsP, rc⟩ c := by
  simp only [Arena.ClassRead.motiveSlot, ConLeche.ClassRead.motiveSlot]
  congr 1
  exact motive_filter_eq h (fun o => match o with | some (.motive _) => true | _ => false)
    (fun o => match o with | some (.motive _) => true | _ => false)
    (fun _ => rfl) (fun _ => rfl)

/-! ## `classNPcOf` -/

/-- con-leche: none — a denoting constant value's name handle denotes its name. -/
theorem denoteCV_name {st : EStore} {cv : IConstantVal} {c : ConstantVal}
    (h : Frontend.denoteCV st cv = some c) : denoteN st.ns cv.name = some c.name := by
  unfold Frontend.denoteCV at h
  split at h
  · rename_i n lps ty hn _ _
    cases h; exact hn
  · cases h

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:138 memberNames — a
denoting shape's member names denote con-leche's. -/
theorem memberNames_denote {st : EStore} {p : Arena.BlockShape} {pP : ConLeche.BlockShape}
    (h : dShape st p = some pP) :
    Frontend.denoteNList st.ns p.memberNames = some pP.memberNames ∧ pP.nP = p.nP := by
  simp only [dShape, Option.bind_eq_bind] at h
  cases h1 : p.members.mapM (dMember st) with
  | none => rw [h1] at h; exact nomatch h
  | some ms =>
  rw [h1] at h
  simp only [Option.bind_some] at h
  cases h2 : p.recs.mapM (dRec st) with
  | none => rw [h2] at h; exact nomatch h
  | some rs =>
  rw [h2] at h
  simp only [Option.bind_some] at h
  cases h3 : denoteN st.ns p.elim with
  | none => rw [h3] at h; exact nomatch h
  | some el =>
  rw [h3] at h
  simp only [Option.bind_some] at h
  cases h4 : denoteL st.ls p.resSort with
  | none => rw [h4] at h; exact nomatch h
  | some so =>
  rw [h4] at h
  simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at h
  subst h
  refine ⟨?_, rfl⟩
  simp only [Arena.BlockShape.memberNames, ConLeche.BlockShape.memberNames]
  clear h2 h3 h4
  generalize p.members = xs at h1
  induction xs generalizing ms with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h1
    subst h1; rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h1
    cases hx : dMember st x with
    | none => rw [hx] at h1; simp at h1
    | some y =>
    rw [hx] at h1
    cases hxs : xs.mapM (dMember st) with
    | none => rw [hxs] at h1; simp at h1
    | some ys =>
    rw [hxs] at h1
    simp only [Option.bind_some, Option.some.injEq] at h1
    subst h1
    simp only [dMember, Option.bind_eq_bind] at hx
    cases hcv : Frontend.denoteCV st x.cvT with
    | none => rw [hcv] at hx; simp at hx
    | some cv =>
    rw [hcv] at hx
    simp only [Option.bind_some] at hx
    cases hcs : dCtors st x.ctors with
    | none => rw [hcs] at hx; simp at hx
    | some cs =>
    rw [hcs] at hx
    simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at hx
    subst hx
    simp only [List.map_cons, Frontend.denoteNList, denoteCV_name hcv, ih ys hxs]

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:488-492 classNPcOf — **the
parameter count the pre-pass reads**: the twin reads the formers' index `fe`,
con-leche `mkFEnv env`; the index invariant makes them one (`mkFEnv_find?`). -/
theorem classNPcOf_eq {env : Env} {fe : IFEnv} {s : AState} {p : Arena.BlockShape}
    {pP : ConLeche.BlockShape} {i : NIdx} {I : ConLeche.Name} (hok : StateOK s)
    (hfe : IFEnvOK env fe s) (hp : dShape s.store p = some pP)
    (hi : denoteN s.store.ns i = some I) :
    Arena.classNPcOf p fe i = ConLeche.classNPcOf pP (mkFEnv env) I := by
  obtain ⟨hmn, hnP⟩ := memberNames_denote hp
  unfold Arena.classNPcOf ConLeche.classNPcOf
  rw [PW.contains_handle_eq hok.wf hi hmn, hnP, mkFEnv_find?]
  split
  · rfl
  · cases hf : fe.find? i with
    | none =>
      rw [IFEnvOK.miss hok hfe hi hf]
    | some ci =>
      obtain ⟨nm, c, hn, hci, henv⟩ := hfe.hit i ci hf
      rw [hi] at hn
      obtain rfl := Option.some.inj hn
      rw [henv]
      cases ci with
      | indInfo v caps =>
        simp only [Frontend.denoteCI] at hci
        split at hci
        · rename_i cv capsP _ hcaps
          cases hci
          simp only [Frontend.denoteCaps] at hcaps
          split at hcaps
          · cases hcaps; rfl
          · cases hcaps
        · cases hci
      | _ =>
        have hne := denoteCI_not_ind hci (by intro v caps hc; cases hc)
        cases c with
        | indInfo v caps => exact absurd rfl (hne v caps)
        | _ => rfl

/-! ## `classReadSlot` -/

/-- con-leche: none — a denoting binder telescope's last binder, both ways. -/
theorem denoteBinders_getLast? {st : EStore} {bs : List (EIdx × BinderMeta)}
    {xs : List (Expr × BinderMeta)} (h : denoteBinders st bs = some xs) :
    (bs.getLast? = none → xs.getLast? = none) ∧
      ∀ b m, bs.getLast? = some (b, m) →
        ∃ x, xs.getLast? = some (x, m) ∧ denoteE st b = some x := by
  have hl := denoteBinders_length h
  have hg := denoteBinders_getElem? h (bs.length - 1)
  rw [List.getLast?_eq_getElem?, List.getLast?_eq_getElem?, ← hl]
  exact ⟨hg.2, hg.1⟩

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:111-117 classReadSlots —
the per-binder reading (a motive when the domain's telescope ends in a sort,
else a minor premise), as a function; `classReadSlots_succ` identifies it with
the inline block. -/
def slotP (nPc : ConLeche.Name → Nat) (np : Nat) (motPos : List Nat) (d : Nat)
    (dom : Expr) : Option ConLeche.ClassSlot :=
  match dom.piResult with
  | .sort _ => do
    let (bs, _) := dom.piBinders
    let (mdom, _) ← bs.getLast?
    let .const I us := mdom.getAppFn | none
    pure (ConLeche.ClassSlot.motive ⟨I, us, mdom.getAppArgs.take (nPc I)⟩)
  | _ => ConLeche.classReadMinor np motPos d dom

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:118 classReadSlots —
the prefix-position list after one slot, as a function. -/
def motPosP (motPos : List Nat) (d np : Nat) : ConLeche.ClassSlot → List Nat
  | .motive _ => motPos ++ [d - np]
  | _ => motPos

theorem classReadSlots_succ (nPc : ConLeche.Name → Nat) (np n : Nat) (motPos : List Nat)
    (d : Nat) (dom body : Expr) (m : BinderMeta) :
    ConLeche.classReadSlots nPc np (n + 1) motPos d (.forallE dom body m) =
      (slotP nPc np motPos d dom).bind fun slot =>
        (ConLeche.classReadSlots nPc np n (motPosP motPos d np slot) (d + 1)
          (body.instantiate1 (.fvar d dom))).bind fun rest => some (slot :: rest) := by
  rw [ConLeche.classReadSlots]
  unfold slotP
  split
  · rename_i hu
    rw [hu]
    obtain ⟨bs, e⟩ := dom.piBinders
    dsimp only
    cases bs.getLast? with
    | none => rfl
    | some q =>
      obtain ⟨mdom, _⟩ := q
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases mdom.getAppFn <;> rfl
  · rename_i hu
    split
    · rename_i hu'; exact absurd hu' (hu _)
    · rfl

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:111-117 classReadSlots —
**one prefix binder read**, two-sided on the `Option`; the parameter counts
are `classNPcOf` at the formers' index (`classNPcOf_eq`). -/
theorem classReadSlot_spec (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (env : Env)
    (fe : IFEnv) (np : Nat) (motPos : List Nat) (d : Nat) (dom : EIdx) (domP : Expr) :
    PSpec (fun st => dShape st p = some pP ∧ IFEnvOKS env fe st ∧ denoteE st dom = some domP)
      (Arena.classReadSlot p fe np motPos d dom)
      (ROp (fun q st r => dSlot st r = some q)
        (slotP (ConLeche.classNPcOf pP (mkFEnv env)) np motPos d domP)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hsh, hfe, hd⟩ := hp
  simp only [Arena.classReadSlot] at hrun
  obtain ⟨rr, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨rfl, hrr⟩ := CR.piResult_run hok hd h1
  by_cases htg : (rr.tag == ETag.sort) = true
  · rw [if_pos htg] at h2
    obtain ⟨u, hu⟩ := CR.sort_of_tag hok.wf htg hrr
    unfold slotP
    rw [hu]
    simp only
    obtain ⟨⟨bs, e⟩, s₂, h3, h4⟩ := bindOk h2
    obtain ⟨rfl, hbs, -⟩ := CR.piBinders_run _ hok hd h3
    obtain ⟨hl1, hl2⟩ := denoteBinders_getLast? hbs
    dsimp only at h4
    cases hl : bs.getLast? with
    | none =>
      rw [hl] at h4
      obtain ⟨rfl, rfl⟩ := pureOk h4
      refine ⟨PStep.refl hok, ?_⟩
      simp [ROp, hl1 hl]
    | some bm =>
    obtain ⟨mdom, m⟩ := bm
    rw [hl] at h4
    obtain ⟨mdomP, hlP, hmd⟩ := hl2 mdom m hl
    rw [hlP]
    simp only [Option.bind_eq_bind, Option.bind_some]
    dsimp only at h4
    obtain ⟨hdh, s₃, h5, h6⟩ := bindOk h4
    obtain ⟨rfl, hhd⟩ := getAppFn_run hok hmd h5
    by_cases htc : (hdh.tag == ETag.const) = true
    · rw [if_pos htc] at h6
      obtain ⟨o, s₄, h7, h8⟩ := bindOk h6
      obtain ⟨rfl, ho⟩ := PW.viewConst_run h7
      cases o with
      | none => exact absurd h8 (fun hc => PW.failDanglingE_ok hc)
      | some pr =>
      obtain ⟨cn, us⟩ := pr
      have hw := view_of_viewConst_tag htc ho.symm
      obtain ⟨nm, ls, hgl, hn, hls⟩ := denote_const_inv hok.wf hw hhd
      rw [hgl]
      dsimp only at h8
      obtain ⟨args, s₅, h9, h10⟩ := bindOk h8
      obtain ⟨rfl, hargs⟩ := getAppArgs_run hok hmd h9
      obtain ⟨rfl, rfl⟩ := pureOk h10
      refine ⟨PStep.refl hok, ?_⟩
      refine ⟨_, rfl, ?_⟩
      rw [classNPcOf_eq hok (hfe _ rfl) hsh hn]
      simp [dSlot, dClassKey, hn, hls, denoteEList_take hargs]
    · rw [if_neg htc] at h6
      obtain ⟨rfl, rfl⟩ := pureOk h6
      refine ⟨PStep.refl hok, ?_⟩
      show _ = none
      split
      · rename_i C us hg
        rw [hg] at hhd
        exact absurd (PW.tag_const_of_denote hok.wf hhd) (by simpa using htc)
      · rfl
  · rw [if_neg htg] at h2
    have hns : ∀ u, domP.piResult ≠ .sort u := by
      intro u hu
      rw [hu] at hrr
      exact htg (by simp [CR.tag_sort_of_denote hok.wf hrr])
    have e : slotP (ConLeche.classNPcOf pP (mkFEnv env)) np motPos d domP =
        ConLeche.classReadMinor np motPos d domP := by
      unfold slotP
      split
      · rename_i u hu; exact absurd hu (hns u)
      · rfl
    rw [e]
    exact classReadMinor_spec np motPos d dom domP _ s' r hok hd h2

/-! ## `classReadSlots` -/

/-- con-leche: none — a denoting slot moves the prefix-position list as con-leche's. -/
theorem motPos_step {st : EStore} {slot : Arena.ClassSlot} {q : ConLeche.ClassSlot}
    (h : dSlot st slot = some q) (motPos : List Nat) (d np : Nat) :
    (match (generalizing := false) slot with
      | .motive _ => motPos ++ [d - np]
      | .minor _ _ _ => motPos) = motPosP motPos d np q := by
  cases slot with
  | motive k =>
    simp only [dSlot, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    rfl
  | minor c n ihs =>
    simp only [dSlot, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    rfl

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:107-124 classReadSlots —
**the prefix binders read**, one at a time, each opened at `d` before the next;
two-sided on the `Option`, the slot list denoting con-leche's. -/
theorem classReadSlots_spec (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (env : Env)
    (fe : IFEnv) (np : Nat) :
    ∀ (n : Nat) (motPos : List Nat) (d : Nat) (e : EIdx) (eP : Expr),
    PSpec (fun st => dShape st p = some pP ∧ IFEnvOKS env fe st ∧ denoteE st e = some eP)
      (Arena.classReadSlots p fe np n motPos d e)
      (ROp (fun q st r => r.mapM (dSlot st) = some q)
        (ConLeche.classReadSlots (ConLeche.classNPcOf pP (mkFEnv env)) np n motPos d eP)) := by
  intro n
  induction n with
  | zero =>
    intro motPos d e eP s₀ s' r hok _ hrun
    simp only [Arena.classReadSlots] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, [], by simp [ConLeche.classReadSlots], rfl⟩
  | succ n ih =>
    intro motPos d e eP s₀ s' r hok hp hrun
    obtain ⟨hsh, hfe, hd⟩ := hp
    simp only [Arena.classReadSlots] at hrun
    by_cases htg : (e.tag == ETag.forallE) = true
    · rw [if_pos htg] at hrun
      obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
      obtain ⟨rfl, ho⟩ := PW.viewBind_run h1
      cases o with
      | none => exact absurd h2 (fun hc => PW.failDanglingE_ok hc)
      | some pr =>
      obtain ⟨dom, body, m⟩ := pr
      have hw := view_of_viewBind_tag_forallE htg ho.symm
      obtain ⟨domP, bodyP, rfl, hdd, hbd⟩ := denote_forallE_inv hok.wf hw hd
      rw [classReadSlots_succ]
      dsimp only at h2
      obtain ⟨os, s₂, h3, h4⟩ := bindOk h2
      obtain ⟨p3, hos⟩ := classReadSlot_spec p pP env fe np motPos d dom domP _ _ _ hok
        ⟨hsh, hfe, hdd⟩ h3
      cases os with
      | none =>
        obtain ⟨rfl, rfl⟩ := pureOk h4
        refine ⟨p3, ?_⟩
        simp only [ROp] at hos
        simp [ROp, hos]
      | some slot =>
      obtain ⟨q, hq, hsl⟩ := hos
      rw [hq]
      simp only [Option.bind_some]
      dsimp only at h4
      have hmp := motPos_step hsl motPos d np
      obtain ⟨mp, rfl, h4⟩ : ∃ mp, motPosP motPos d np q = mp ∧
          (internFVarE d dom >>= fun fv => do
            let b2 ← instantiate1Fast coreWalkFuel body fv
            let o ← Arena.classReadSlots p fe np n mp (d + 1) b2
            match o with
            | none => pure none
            | some rest => pure (some (slot :: rest))) s₂ = .ok (r, s') := by
        cases slot <;> exact ⟨_, hmp.symm, h4⟩
      obtain ⟨fv, s₃, h5, h6⟩ := bindOk h4
      obtain ⟨p5, hfv⟩ := PW.internFVarE_run p3.ok (denote_ext hdd p3.ext) h5
      obtain ⟨b2, s₄, h7, h8⟩ := bindOk h6
      have hb3 : denoteE s₃.store body = some bodyP := denote_ext hbd (p3.ext.trans p5.ext)
      obtain ⟨k1, k2, k3, k4, k5, -, k7⟩ := ExprOps.instantiate1Fast_run p5.ok hfv
        (by rw [hb3]; rfl) h7
      have p7 : PStep s₃ s₄ := PStep.of_caches k1 k2 k3 k4 k5
      have hb2 : denoteE s₄.store b2 = some (bodyP.instantiate1 (.fvar d domP) 0) := k7 _ hb3
      have p37 := p3.trans (p5.trans p7)
      obtain ⟨o2, s₅, h9, h10⟩ := bindOk h8
      obtain ⟨p9, ho2⟩ := ih (motPosP motPos d np q) (d + 1) b2 _ _ _ _ p7.ok
        ⟨dShape_ext p37.ext _ _ hsh, hfe.mono p37.ext, hb2⟩ h9
      cases o2 with
      | none =>
        obtain ⟨rfl, rfl⟩ := pureOk h10
        refine ⟨p37.trans p9, ?_⟩
        simp only [ROp] at ho2
        simp [ROp, ho2]
      | some rest =>
      obtain ⟨qs, hqs, hrest⟩ := ho2
      obtain ⟨rfl, rfl⟩ := pureOk h10
      refine ⟨p37.trans p9, ?_⟩
      refine ⟨q :: qs, by rw [hqs]; rfl, ?_⟩
      simp only [List.mapM_cons, dSlot_ext (p5.trans (p7.trans p9)).ext _ _ hsl, hrest,
        Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    · rw [if_neg htg] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      refine ⟨PStep.refl hok, ?_⟩
      show _ = none
      cases eP with
      | forallE a b m => exact absurd (PW.tag_forallE_of_denote hok.wf hd) (by simpa using htg)
      | _ => simp [ConLeche.classReadSlots]

/-! ## `classReadRecCls` -/

/-- con-leche: none — a denoting constant value's type handle denotes its type. -/
theorem denoteCV_type {st : EStore} {cv : IConstantVal} {c : ConstantVal}
    (h : Frontend.denoteCV st cv = some c) : denoteE st cv.type = some c.type := by
  unfold Frontend.denoteCV at h
  split at h
  · rename_i n lps ty _ _ hty
    cases h; exact hty
  · cases h

/-- con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:71-96 RecShape — what
the pre-pass reads of a denoting recursor record. -/
theorem dRec_inv {st : EStore} {r : Arena.RecShape} {rP : ConLeche.RecShape}
    (h : dRec st r = some rP) :
    denoteE st r.cvR.type = some rP.cvR.type ∧ rP.mI = r.mI ∧ rP.rP = r.rP := by
  simp only [dRec, Option.bind_eq_bind] at h
  cases hcv : Frontend.denoteCV st r.cvR with
  | none => rw [hcv] at h; simp at h
  | some cv =>
  rw [hcv] at h
  simp only [Option.bind_some] at h
  cases hr : Frontend.denoteEList st r.rhss with
  | none => rw [hr] at h; simp at h
  | some rs =>
  rw [hr] at h
  simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at h
  subst h
  exact ⟨denoteCV_type hcv, rfl, rfl⟩

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:134-137 classRead — one
recursor's class off its conclusion, as a function (bind form). -/
def recClsP (nP : Nat) (motPos : List Nat) (rc : ConLeche.RecShape) : Option Nat :=
  (ConLeche.openPisAtFvars (rc.mI + 1) rc.cvR.type 0).bind fun (_, concl) =>
    (fvarHeadP concl).bind fun p => ConLeche.classOfMotiveVar nP motPos p

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:134-137 classRead
(`recs.mapM`) — **every recursor's class**, at the pure grade; the answer is
representation-free, so `RV` at the `Option` is already two-sided. -/
theorem classReadRecCls_spec (nP : Nat) (motPos : List Nat) :
    ∀ (recs : List Arena.RecShape) (recsP : List ConLeche.RecShape),
    PSpec (fun st => recs.mapM (dRec st) = some recsP)
      (Arena.classReadRecCls nP motPos recs) (RV (recsP.mapM (recClsP nP motPos))) := by
  intro recs
  induction recs with
  | nil =>
    intro recsP s₀ s' r hok hp hrun
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hp
    subst hp
    simp only [Arena.classReadRecCls] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons rc rest ih =>
    intro recsP s₀ s' r hok hp hrun
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hp
    cases hx : dRec s₀.store rc with
    | none => rw [hx] at hp; simp at hp
    | some rcP =>
    rw [hx] at hp
    cases hxs : rest.mapM (dRec s₀.store) with
    | none => rw [hxs] at hp; simp at hp
    | some restP =>
    rw [hxs] at hp
    simp only [Option.bind_some, Option.some.injEq] at hp
    subst hp
    obtain ⟨hty, hmI, -⟩ := dRec_inv hx
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def]
    simp only [Arena.classReadRecCls] at hrun
    obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
    obtain ⟨p1, ho⟩ := CR.openPisAtFvarsF_run hok hty h1
    rw [← hmI] at ho
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      refine ⟨p1, ?_⟩
      have hn := (Option.some.inj ho).symm
      simp [RV, recClsP, hn]
    | some q =>
    obtain ⟨fvs, concl⟩ := q
    obtain ⟨fvsP, conclP, hq, -, hconcl⟩ := CR.denoteOpen_some_inv ho
    dsimp only at h2
    obtain ⟨hp, s₂, h3, h4⟩ := bindOk h2
    obtain ⟨rfl, rfl⟩ := fvarHead_run p1.ok hconcl h3
    have hrc : recClsP nP motPos rcP = (fvarHeadP conclP).bind fun p =>
        ConLeche.classOfMotiveVar nP motPos p := by
      simp [recClsP, hq]
    rw [hrc]
    cases hfp : fvarHeadP conclP with
    | none =>
      rw [hfp] at h4
      obtain ⟨rfl, rfl⟩ := pureOk h4
      exact ⟨p1, by simp [RV]⟩
    | some p =>
    rw [hfp] at h4
    dsimp only at h4
    rw [classOfMotiveVar_eq] at h4
    simp only [Option.bind_some]
    cases hc : ConLeche.classOfMotiveVar nP motPos p with
    | none =>
      rw [hc] at h4
      obtain ⟨rfl, rfl⟩ := pureOk h4
      exact ⟨p1, by simp [RV]⟩
    | some c =>
    rw [hc] at h4
    dsimp only at h4
    obtain ⟨o2, s₃, h5, h6⟩ := bindOk h4
    obtain ⟨p5, ho2⟩ := ih restP _ _ _ p1.ok (dRec_ext.list p1.ext _ _ hxs) h5
    simp only [RV] at ho2
    subst ho2
    simp only [Option.bind_some]
    cases hrs : restP.mapM (recClsP nP motPos) with
    | none =>
      rw [hrs] at h6
      obtain ⟨rfl, rfl⟩ := pureOk h6
      exact ⟨p1.trans p5, by simp [RV]⟩
    | some cs =>
      rw [hrs] at h6
      obtain ⟨rfl, rfl⟩ := pureOk h6
      exact ⟨p1.trans p5, by simp [RV]⟩

/-! ## The headline: `classRead` -/

/-- con-leche: none — `Option`'s `mapM` under a pointwise-equal function. -/
theorem mapM_option_congr {α β : Type} {f g : α → Option β} (h : ∀ x, f x = g x)
    (xs : List α) : xs.mapM f = xs.mapM g := by
  rw [show f = g from funext h]

/-- con-leche: ConLeche/Kernel/Inductives/ClassRead.lean:126-140 classRead —
**THEOREM 1 for the recursor stage's pre-pass**: from a denoting block shape,
the formers' index invariant and a denoting recursor family, an accepting run
of the twin answers con-leche's `classRead` at `nPc := classNPcOf pP (mkFEnv
env)`, TWO-SIDEDLY on the `Option` (the stage throws on `none`), the read
record denoting con-leche's. -/
theorem classRead_spec (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (env : Env)
    (fe : IFEnv) (nP : Nat) (recs : List Arena.RecShape) (recsP : List ConLeche.RecShape) :
    PSpec (fun st => dShape st p = some pP ∧ IFEnvOKS env fe st ∧
        recs.mapM (dRec st) = some recsP)
      (Arena.classRead p fe nP recs)
      (ROp (fun q st r => dClassRead st r = some q)
        (ConLeche.classRead nP (ConLeche.classNPcOf pP (mkFEnv env)) recsP)) := by
  intro s₀ s' r hok hp hrun
  obtain ⟨hsh, hfe, hrecs⟩ := hp
  unfold ConLeche.classRead
  simp only [Arena.classRead] at hrun
  cases recs with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hrecs
    subst hrecs
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons rc0 rest =>
  have hrecs' := hrecs
  simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hrecs'
  cases hx : dRec s₀.store rc0 with
  | none => rw [hx] at hrecs'; simp at hrecs'
  | some rc0P =>
  rw [hx] at hrecs'
  cases hxs : rest.mapM (dRec s₀.store) with
  | none => rw [hxs] at hrecs'; simp at hrecs'
  | some restP =>
  rw [hxs] at hrecs'
  simp only [Option.bind_some, Option.some.injEq] at hrecs'
  subst hrecs'
  obtain ⟨hty, -, hrP⟩ := dRec_inv hx
  simp only [List.head?_cons, Option.bind_eq_bind, Option.bind_some]
  dsimp only at hrun
  obtain ⟨o, s₁, h1, h2⟩ := bindOk hrun
  obtain ⟨p1, ho⟩ := CR.openPisAtFvarsF_run hok hty h1
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk h2
    refine ⟨p1, ?_⟩
    have hn := (Option.some.inj ho).symm
    simp [ROp, hn]
  | some q =>
  obtain ⟨fvs, body⟩ := q
  obtain ⟨fvsP, bodyP, hq, -, hbody⟩ := CR.denoteOpen_some_inv ho
  rw [hq]
  simp only [Option.bind_some]
  dsimp only at h2
  obtain ⟨os, s₂, h3, h4⟩ := bindOk h2
  obtain ⟨p3, hos⟩ := classReadSlots_spec p pP env fe nP (rc0.rP - nP) [] nP body bodyP _ _ _
    p1.ok ⟨dShape_ext p1.ext _ _ hsh, hfe.mono p1.ext, hbody⟩ h3
  rw [hrP]
  cases os with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk h4
    refine ⟨p1.trans p3, ?_⟩
    simp only [ROp] at hos
    simp [ROp, hos]
  | some slots =>
  obtain ⟨slotsP, hsP, hsl⟩ := hos
  rw [hsP]
  simp only [Option.bind_some]
  dsimp only at h4
  generalize hT : List.filter _ (List.range slots.length) = mT at h4
  generalize hU : List.filter _ (List.range slotsP.length) = mU
  have hmT : mT = mU := by
    rw [← hT, ← hU]
    exact motive_filter_eq hsl (fun o => match o with | some (.motive _) => true | _ => false)
      (fun o => match o with | some (.motive _) => true | _ => false)
      (fun _ => rfl) (fun _ => rfl)
  subst hmT
  rw [mapM_option_congr (g := recClsP nP mT) ?_]
  · obtain ⟨o2, s₃, h5, h6⟩ := bindOk h4
    have p13 := p1.trans p3
    obtain ⟨p5, ho2⟩ := classReadRecCls_spec nP mT (rc0 :: rest) (rc0P :: restP) _ _ _
      p3.ok (dRec_ext.list p13.ext _ _ hrecs) h5
    simp only [RV] at ho2
    subst ho2
    have p15 := p13.trans p5
    cases hrc : (rc0P :: restP).mapM (recClsP nP mT) with
    | none =>
      rw [hrc] at h6
      obtain ⟨rfl, rfl⟩ := pureOk h6
      exact ⟨p15, by simp [ROp]⟩
    | some cs =>
      rw [hrc] at h6
      obtain ⟨rfl, rfl⟩ := pureOk h6
      refine ⟨p15, _, rfl, ?_⟩
      simp [dClassRead, dSlot_ext.list p5.ext _ _ hsl]
  · intro rc
    unfold recClsP
    cases ConLeche.openPisAtFvars (rc.mI + 1) rc.cvR.type 0 with
    | none => rfl
    | some q =>
      obtain ⟨_, concl⟩ := q
      simp only [Option.bind_some, fvarHeadP]
      cases concl.getAppFn <;> rfl

end ConRon.Bridge.Inductives

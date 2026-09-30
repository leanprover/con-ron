/-
# `ConRon.Bridge.Inductives.FieldTele` — the telescope readers
(DESIGN.md §8.2, task #105)

Theorem 1 for the three pure telescope readers every later stage of the
inductive tier shares: `Arena.piBinders` (`Arena/Inductives/FieldTele.lean`,
con-leche's `Expr.piBinders`), and `Arena.closeTelescope` / `Arena.instPisWith`
(`Arena/Inductives/Positivity.lean`, con-leche's `closeTelescope` /
`instPisWith`).  All three are PURE grade (`PSpec`): they read the store and
intern nodes (`instantiate1Fast`, `abstract1Fast`, `internForallEE`), never
the knot.

`closeTelescope_spec` is the proof `Bridge/Inductives/SumInstall.lean` carried
while the twin's `closeTelescope` lived in `SumInstall`; `piBinders_spec` is
task #97-P3-Ind round 2's proof (then in `NativeParts.lean`), over the
tag-first `viewBind` twin.
-/
import ConRon.Bridge.Inductives.Rel
import ConRon.Bridge.Inductives.PosWalks

namespace ConRon.Bridge.Inductives


open ConLeche ConRon.Arena ConRon.Bridge PW

/-- con-leche: ConLeche/Kernel/Inductives/FieldTele.lean:45-52 Expr.piBinders —
all leading `∀` binders and the body; the twin's fuel is invisible under
partial correctness (exhaustion fails). -/
theorem piBinders_spec : ∀ (fuel : Nat) (h : EIdx) (hP : Expr),
    PSpec (fun st => denoteE st h = some hP)
      (Arena.piBinders fuel h)
      (fun st r => denoteBinders st r.1 = some (Expr.piBinders hP).1 ∧
        denoteE st r.2 = some (Expr.piBinders hP).2) := by
  intro fuel
  induction fuel with
  | zero =>
    intro h hP s₀ s' r hok hd hrun
    simp only [Arena.piBinders] at hrun
    exact absurd hrun (fun hc => failOk hc)
  | succ fuel ih =>
    intro h hP s₀ s' r hok hd hrun
    simp only [Arena.piBinders] at hrun
    by_cases htg : (h.tag == ETag.forallE) = true
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
        obtain ⟨q, s₂, h3, h4⟩ := bindOk h2
        obtain ⟨hstep, hq1, hq2⟩ := ih b bP s₀ s₂ q hok hbd h3
        obtain ⟨rfl, rfl⟩ := pureOk h4
        refine ⟨hstep, ?_, ?_⟩
        · simp only [Expr.piBinders, denoteBinders, denote_ext hdd hstep.ext, hq1]
        · simpa only [Expr.piBinders] using hq2
    · rw [if_neg htg] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      refine ⟨PStep.refl hok, ?_, ?_⟩
      · cases hP with
        | forallE d b m => exact absurd (tag_forallE_of_denote hok.wf hd) (by simpa using htg)
        | _ => rfl
      · cases hP with
        | forallE d b m => exact absurd (tag_forallE_of_denote hok.wf hd) (by simpa using htg)
        | _ => exact hd

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:211-219 closeTelescope
Close a body under a telescope, abstracting the free variables as it goes.
A list induction over `Bridge/ExprOps/Owed.lean`'s `abstract1Fast_spec` (at
`Rel.lean`'s `fvarBSpec`) and `internForallEE_run`. -/
theorem closeTelescope_spec (bs : List (EIdx × BinderMeta))
    (bsP : List (Expr × BinderMeta)) (i : Nat) (body : EIdx) (bodyP : Expr) :
    PSpec (fun st => denoteBinders st bs = some bsP ∧
        denoteE st body = some bodyP)
      (Arena.closeTelescope bs i body)
      (RE (ConLeche.closeTelescope bsP i bodyP)) := by
  induction bs generalizing bsP i with
  | nil =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hbs, hbody⟩ := hpre
    simp only [denoteBinders, Option.some.injEq] at hbs
    subst hbs
    simp only [Arena.closeTelescope] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, hbody⟩
  | cons b bs ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hbs, hbody⟩ := hpre
    obtain ⟨dom, bm⟩ := b
    simp only [denoteBinders] at hbs
    cases hdom : denoteE s₀.store dom with
    | none => rw [hdom] at hbs; simp at hbs
    | some domP =>
    cases hrest : denoteBinders s₀.store bs with
    | none => rw [hdom, hrest] at hbs; simp at hbs
    | some rest =>
    rw [hdom, hrest] at hbs
    obtain rfl := (Option.some.inj hbs).symm
    simp only [Arena.closeTelescope] at hrun
    obtain ⟨inner, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hin⟩ := ih rest (i + 1) s₀ s1 inner hok ⟨hrest, hbody⟩ k1
    obtain ⟨cl, s2, k2, z2⟩ := bindOk z1
    obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := AM.of_run (P := fun t => t = s1) rfl k2
      (ExprOps.abstract1Fast_spec fvarBSpec Arena.coreWalkFuel s1 inner i 0 p1.ok
        (by rw [hin]; rfl))
    have p2 : PStep s1 s2 := PStep.of_caches h1 h2 h3 h4 h5
    obtain ⟨p3, hr⟩ := internForallEE_run p2.ok (denote_ext hdom (p1.ext.trans p2.ext))
      (h7 _ hin) z2
    exact ⟨p1.trans (p2.trans p3), hr⟩

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:514-519 instPisWith
Instantiate the leading `Π` binders at `args`, in order; `none` exactly when
con-leche's is (`ROp`, both directions). -/
theorem instPisWith_spec : ∀ (args : List EIdx) (argsP : List Expr) (e : EIdx) (eP : Expr),
    PSpec (fun st => Frontend.denoteEList st args = some argsP ∧
        denoteE st e = some eP)
      (Arena.instPisWith args e)
      (ROp RE (ConLeche.instPisWith argsP eP)) := by
  intro args
  induction args with
  | nil =>
    intro argsP e eP s₀ s' r hok hp hrun
    obtain ⟨ha, hd⟩ := hp
    simp only [Frontend.denoteEList, Option.some.injEq] at ha
    subst ha
    simp only [Arena.instPisWith] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, _, rfl, hd⟩
  | cons a args ih =>
    intro argsP e eP s₀ s' r hok hp hrun
    obtain ⟨ha, hd⟩ := hp
    simp only [Frontend.denoteEList] at ha
    cases hA : denoteE s₀.store a with
    | none => rw [hA] at ha; simp at ha
    | some aP =>
    cases hR : Frontend.denoteEList s₀.store args with
    | none => rw [hA, hR] at ha; simp at ha
    | some restP =>
    rw [hA, hR] at ha
    obtain rfl := (Option.some.inj ha).symm
    simp only [Arena.instPisWith] at hrun
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
        obtain ⟨b', s₂, h3, h4⟩ := bindOk h2
        obtain ⟨q1, q2, q3, q4, q5, -, q7⟩ := ExprOps.instantiate1Fast_run hok hA
          (by rw [hbd]; rfl) h3
        have p2 : PStep s₀ s₂ := PStep.of_caches q1 q2 q3 q4 q5
        have hb' : denoteE s₂.store b' = some (bP.instantiate1 aP 0) := q7 _ hbd
        obtain ⟨p3, hr⟩ := ih restP b' (bP.instantiate1 aP 0) s₂ s' r p2.ok
          ⟨denoteEList_ext p2.ext _ _ hR, hb'⟩ h4
        exact ⟨p2.trans p3, by simpa [ConLeche.instPisWith, Expr.instantiate1] using hr⟩
    · rw [if_neg htg] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      refine ⟨PStep.refl hok, ?_⟩
      show ConLeche.instPisWith (aP :: restP) eP = none
      cases eP with
      | forallE d b m => exact absurd (tag_forallE_of_denote hok.wf hd) (by simpa using htg)
      | _ => rfl


end ConRon.Bridge.Inductives

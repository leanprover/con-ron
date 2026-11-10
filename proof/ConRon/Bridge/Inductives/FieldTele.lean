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

`piBinders_run` is the reader's read-only run form (over the tag-first
`viewBind` twin); `piBinders_spec` is its `PSpec`.
-/
module

public import ConRon.Bridge.Inductives.Run
import ConRon.Bridge.Core.Walks.FvarB
import ConRon.Bridge.ExprOps.Owed
import ConRon.Bridge.Pers
import ConRon.Bridge.ExprOps.Inst1
public import ConLeche.Cached.ExprOpsC
import ConLeche.Verify.Cached.IndWalksC
import ConLeche.Verify.Cached.OpsC

public section

namespace ConRon.Bridge.Inductives


open ConLeche ConRon.Arena ConRon.Bridge

/-- con-leche: ConLeche/Kernel/Inductives/FieldTele.lean:45-52 Expr.piBinders —
the twin's telescope reader, as a run: read-only, the binders and the body
denote con-leche's; the twin's fuel is invisible under partial correctness
(exhaustion fails). -/
theorem piBinders_run : ∀ (fuel : Nat) {h : EIdx} {hP : Expr} {s₀ s' : AState}
    {r : List EIdx × EIdx},
    StateOK s₀ → denoteE s₀.store h = some hP →
    Arena.piBinders fuel h s₀ = .ok (r, s') →
    s' = s₀ ∧ Frontend.denoteEList s₀.store r.1 = some hP.piBinders.1 ∧
      denoteE s₀.store r.2 = some hP.piBinders.2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro h hP s₀ s' r _ _ hrun
    simp only [Arena.piBinders] at hrun
    exact absurd hrun (fun hc => AM.fail_ok hc)
  | succ n ih =>
    intro h hP s₀ s' r hok hd hrun
    simp only [Arena.piBinders] at hrun
    by_cases htg : (h.tag == ETag.forallE) = true
    · rw [ite_eq_left htg] at hrun
      obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok hrun
      obtain ⟨hs1, ho⟩ := viewBind_run h1
      subst hs1
      cases o with
      | none => exact absurd h2 (fun hc => failDanglingE_ok hc)
      | some p =>
        obtain ⟨d, b⟩ := p
        have hw := view_forallE_of_viewBind htg ho.symm
        obtain ⟨dP, bP, rfl, hdd, hbd⟩ := denote_forallE_inv hok.wf hw hd
        dsimp only at h2
        obtain ⟨q, s₂, h3, h4⟩ := AM.bind_ok h2
        obtain ⟨rfl, hq1, hq2⟩ := ih hok hbd h3
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h4
        refine ⟨rfl, ?_, hq2⟩
        simp [Frontend.denoteEList, hdd, hq1, Expr.piBinders]
    · rw [ite_eq_right htg] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      refine ⟨rfl, ?_⟩
      cases hP with
      | forallE d b => exact absurd (tag_forallE_of_denote hok.wf hd) (by simpa using htg)
      | _ => exact ⟨rfl, hd⟩

/-- con-leche: ConLeche/Kernel/Inductives/FieldTele.lean:45-52 Expr.piBinders —
all leading `∀` binders and the body, as a `PSpec`. -/
theorem piBinders_spec (fuel : Nat) (h : EIdx) (hP : Expr) :
    PSpec (fun st => denoteE st h = some hP)
      (Arena.piBinders fuel h)
      (fun st r => Frontend.denoteEList st r.1 = some (Expr.piBinders hP).1 ∧
        denoteE st r.2 = some (Expr.piBinders hP).2) := by
  intro s₀ s' r hok hd hrun
  obtain ⟨rfl, h1, h2⟩ := piBinders_run fuel hok hd hrun
  exact ⟨PStep.refl hok, h1, h2⟩

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:2111-2113 closeTelescopeGoC —
the twin's closer after `k` binders computes con-leche's cached closer: each
domain and the body by `Bridge/ExprOps/Owed.lean`'s `abstractRangeFast_spec`
(at `Rel.lean`'s `Core.fvarBSpec`), the binder by `internForallEE_run`. -/
theorem closeTelescopeGo_spec (i : Nat) (bs : List EIdx) :
    ∀ (k : Nat) (bsP : List Expr) (body : EIdx) (bodyP : Expr),
    PSpec (fun st => Frontend.denoteEList st bs = some bsP ∧
        denoteE st body = some bodyP)
      (Arena.closeTelescopeGo i k bs body)
      (RE (Expr.closeTelescopeGoC i k bsP bodyP)) := by
  induction bs with
  | nil =>
    intro k bsP body bodyP s₀ s' r hok hpre hrun
    obtain ⟨hbs, hbody⟩ := hpre
    simp only [Frontend.denoteEList, Option.some.injEq] at hbs
    subst hbs
    simp only [Arena.closeTelescopeGo] at hrun
    obtain ⟨h1, h2, h4, h5, -, h7⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
      (ExprOps.abstractRangeFast_spec Core.fvarBSpec Arena.coreWalkFuel s₀ body i k 0 hok
        (by rw [hbody]; rfl))
    refine ⟨PStep.of_caches h1 h2 h4 h5, ?_⟩
    show denoteE _ r = _
    rw [h7 _ hbody, Expr.closeTelescopeGoC, Expr.abstractRangeC_spec]
  | cons dom bs ih =>
    intro k bsP body bodyP s₀ s' r hok hpre hrun
    obtain ⟨hbs, hbody⟩ := hpre
    simp only [Frontend.denoteEList] at hbs
    cases hdom : denoteE s₀.store dom with
    | none => rw [hdom] at hbs; simp at hbs
    | some domP =>
    cases hrest : Frontend.denoteEList s₀.store bs with
    | none => rw [hdom, hrest] at hbs; simp at hbs
    | some rest =>
    rw [hdom, hrest] at hbs
    obtain rfl := (Option.some.inj hbs).symm
    simp only [Arena.closeTelescopeGo] at hrun
    obtain ⟨d', s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨h1, h2, h4, h5, -, h7⟩ := AM.of_run (P := fun t => t = s₀) rfl k1
      (ExprOps.abstractRangeFast_spec Core.fvarBSpec Arena.coreWalkFuel s₀ dom i k 0 hok
        (by rw [hdom]; rfl))
    have p1 : PStep s₀ s1 := PStep.of_caches h1 h2 h4 h5
    obtain ⟨inner, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨p2, hin⟩ := ih (k + 1) rest body bodyP s1 s2 inner p1.ok
      ⟨denoteEList_ext p1.ext _ _ hrest, denote_ext hbody p1.ext⟩ k2
    obtain ⟨p3, hr⟩ := internForallEE_run p2.ok (denote_ext (h7 _ hdom) p2.ext) hin z2
    refine ⟨p1.trans (p2.trans p3), ?_⟩
    show denoteE _ r = _
    rw [hr, Expr.closeTelescopeGoC, Expr.abstractRangeC_spec, Expr.mkForallE_eq]

/-- con-leche: ConLeche/Kernel/Inductives/Positivity.lean:55-58 closeTelescope
Close a body under a telescope: the twin's one-pass closer
(`closeTelescopeGo_spec`) is con-leche's `closeTelescope` through con-leche's
own `closeTelescopeC_eq`. -/
theorem closeTelescope_spec (bs : List EIdx)
    (bsP : List Expr) (i : Nat) (body : EIdx) (bodyP : Expr) :
    PSpec (fun st => Frontend.denoteEList st bs = some bsP ∧
        denoteE st body = some bodyP)
      (Arena.closeTelescope bs i body)
      (RE (ConLeche.closeTelescope bsP i bodyP)) := by
  rw [← Expr.closeTelescopeC_eq]
  exact closeTelescopeGo_spec i bs 0 bsP body bodyP

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
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
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
    · rw [ite_eq_left htg] at hrun
      obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok hrun
      obtain ⟨hs1, ho⟩ := viewBind_run h1
      rw [hs1] at h2
      cases o with
      | none => exact absurd h2 (fun hc => failDanglingE_ok hc)
      | some p =>
        obtain ⟨d, b⟩ := p
        have hw := view_forallE_of_viewBind htg ho.symm
        obtain ⟨dP, bP, rfl, hdd, hbd⟩ := denote_forallE_inv hok.wf hw hd
        dsimp only at h2
        obtain ⟨b', s₂, h3, h4⟩ := AM.bind_ok h2
        obtain ⟨q1, q2, q4, q5, -, q7⟩ := ExprOps.instantiate1Fast_run hok hA
          (by rw [hbd]; rfl) h3
        have p2 : PStep s₀ s₂ := PStep.of_caches q1 q2 q4 q5
        have hb' : denoteE s₂.store b' = some (bP.instantiate1 aP 0) := q7 _ hbd
        obtain ⟨p3, hr⟩ := ih restP b' (bP.instantiate1 aP 0) s₂ s' r p2.ok
          ⟨denoteEList_ext p2.ext _ _ hR, hb'⟩ h4
        exact ⟨p2.trans p3, by simpa [ConLeche.instPisWith, Expr.instantiate1] using hr⟩
    · rw [ite_eq_right htg] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      refine ⟨PStep.refl hok, ?_⟩
      show ConLeche.instPisWith (aP :: restP) eP = none
      cases eP with
      | forallE d b => exact absurd (tag_forallE_of_denote hok.wf hd) (by simpa using htg)
      | _ => rfl


end ConRon.Bridge.Inductives

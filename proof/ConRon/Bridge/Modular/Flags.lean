/-
# `ConRon.Bridge.Modular.Flags` — the reach's inferred flags, Theorem 1 (task #166)

Upstream's worker facts ask the reach's flag inference only to be sound (`FlagsOk`,
`Verify/Driver/PropPart.lean`): `WorkerFacts.reach` is `∃ fl, FlagsOk fl ∧ CanGive (reachWith fl …)`.
con-ron runs its inference after the worker's freeze (`Arena/Modular/Reach.lean` `inferFlags`,
each statement at the frozen index's view of the part of the context below its name), so the
inference it supplies upstream is the one that accepts exactly when every recorded statement
resolves and is a proposition over that part (`soundFlags`, sound by definition:
`soundFlags_ok`), and the twin's accept is that condition (`inferFlags_run`).

The run style of `Bridge/Checker/Pooled.lean`'s `job_spec`: each statement in its own scratch
bracket, at `FoldOK` of the view (`view_foldOK'`), its inference `KnotSpec.infer`, its sort
`EnsureSortSpec`, the level test `lvlEq?_spec` — `checkThmVal_bridge`'s is-a-proposition test.
-/
module

public import ConRon.Bridge.Modular.ReachValid
public import ConRon.Bridge.Checker.Pooled
public import ConLeche.Verify.Driver.PropPart
import ConRon.Bridge.Checker.DeclVal
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.Specs
import ConLeche.Verify.BridgeDecl
import Std.Data.HashMap.Lemmas

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean ConRon.Bridge.Inductives

/-! ## The inference con-ron supplies -/

/-- con-leche: ConLeche/Driver/Reach.lean:935 FlagInfer — **the sound flag inference**: it
accepts exactly when every recorded statement resolves and is a proposition over the part of
the context below its name, the condition upstream's `FlagsOk` asks of an accept. -/
noncomputable def soundFlags : ConLeche.Driver.FlagInfer := fun ctx ps =>
  open Classical in
  if ∀ p ∈ ps, p.2.2.type.constsResolve (streamEnv (ConLeche.Driver.ctxPart ctx p.2.1)) = true ∧
      ConLeche.Modular.TypeIsProp .verified (streamEnv (ConLeche.Driver.ctxPart ctx p.2.1)) p.2.2.type
  then .ok () else .error (.internal "a recorded statement is not a proposition below its name")

/-- con-leche: ConLeche/Verify/Driver/PropPart.lean:130 FlagsOk — `soundFlags` is sound. -/
theorem soundFlags_ok : ConLeche.Driver.FlagsOk soundFlags := by
  intro ctx _ ps h w y cv hm
  unfold soundFlags at h
  split at h
  · next hc => exact hc (w, y, cv) hm
  · cases h

/-- `soundFlags` accepts where every statement holds its condition. -/
theorem soundFlags_of {ctx : List Declaration} {ps : List (String × ConLeche.Name × ConstantVal)}
    (h : ∀ p ∈ ps, p.2.2.type.constsResolve (streamEnv (ConLeche.Driver.ctxPart ctx p.2.1)) = true ∧
      ConLeche.Modular.TypeIsProp .verified (streamEnv (ConLeche.Driver.ctxPart ctx p.2.1)) p.2.2.type) :
    soundFlags ctx ps = .ok () := by
  unfold soundFlags
  split
  · rfl
  · next hn => exact absurd h hn

/-! ## Each name's first record -/

/-- con-leche: ConLeche/Driver/Reach.lean:845-848 ctxPart — upstream's side of the twin's
`firstOwner`: each name's first record from position `j`. -/
@[expose] def firstOwnerC : List Declaration → Nat → Std.HashMap ConLeche.Name Nat →
    Std.HashMap ConLeche.Name Nat
  | [], _, m => m
  | d :: ds, j, m => firstOwnerC ds (j + 1)
      ((ConLeche.Modular.declNames d).foldl (fun m n => if m.contains n then m else m.insert n j) m)

theorem firstStep_get (j : Nat) (y : ConLeche.Name) :
    ∀ (ns : List ConLeche.Name) (m : Std.HashMap ConLeche.Name Nat),
      (ns.foldl (fun m n => if m.contains n then m else m.insert n j) m)[y]? =
        (m[y]?).or (if ns.contains y then some j else none)
  | [], m => by simp
  | n :: ns, m => by
    rw [List.foldl_cons, firstStep_get j y ns]
    cases hm : m[y]? with
    | some v =>
      have hc : m.contains y = true := by rw [Std.HashMap.contains_eq_isSome_getElem?, hm]; rfl
      split
      · rw [hm]; rfl
      · next hn =>
        have hne : n ≠ y := fun he => by subst he; exact hn hc
        simp [Std.HashMap.getElem?_insert, hne, hm]
    | none =>
      have hc : m.contains y = false := by
        rw [Std.HashMap.contains_eq_isSome_getElem?, hm]; rfl
      simp only [Option.none_or, List.contains_cons]
      split
      · next hn =>
        have hne : n ≠ y := fun he => by subst he; rw [hn] at hc; cases hc
        rw [hm]
        have : (y == n) = false := by simpa [beq_eq_false_iff_ne] using Ne.symm hne
        simp [this]
      · next hn =>
        rw [Std.HashMap.getElem?_insert]
        by_cases he : n = y
        · subst he; simp
        · have h1 : (n == y) = false := by simpa [beq_eq_false_iff_ne] using he
          have h2 : (y == n) = false := by simpa [beq_eq_false_iff_ne] using Ne.symm he
          simp [h1, h2, hm]

theorem firstOwnerC_get (y : ConLeche.Name) :
    ∀ (ds : List Declaration) (j : Nat) (m : Std.HashMap ConLeche.Name Nat),
      (firstOwnerC ds j m)[y]? =
        (m[y]?).or (if ds.any (fun d => (ConLeche.Modular.declNames d).contains y) then
            some (j + ds.findIdx (fun d => (ConLeche.Modular.declNames d).contains y))
          else none)
  | [], j, m => by simp [firstOwnerC]
  | d :: ds, j, m => by
    rw [firstOwnerC, firstOwnerC_get y ds (j + 1), firstStep_get j y]
    simp only [List.any_cons, List.findIdx_cons]
    cases m[y]? with
    | some v => rfl
    | none =>
      simp only [Option.none_or]
      cases hd : (ConLeche.Modular.declNames d).contains y with
      | true => simp
      | false =>
        simp only [Option.none_or, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        split <;> simp; omega

/-- The first record storing `y`, or the length: the end of `ctxPart`. -/
theorem firstOwnerC_getD (ds : List Declaration) (y : ConLeche.Name) :
    ((firstOwnerC ds 0 {})[y]?).getD ds.length =
      ds.findIdx (fun d => (ConLeche.Modular.declNames d).contains y) := by
  rw [firstOwnerC_get]
  simp only [Std.HashMap.getElem?_empty, Option.none_or, Nat.zero_add]
  split
  · rfl
  · next h =>
    simp only [Bool.not_eq_true, List.any_eq_false] at h
    simp only [Option.getD_none]
    exact (List.findIdx_eq_length.mpr (fun d hd => by simpa using h d hd)).symm

/-! ## One statement -/

/-- con-leche: ConLeche/Verify/Driver/PropPart.lean:44 typeIsPropC_sound — **the twin's
is-a-proposition test answering `true` is `TypeIsProp`**, at the environment the index view
denotes: the inference, the sort, the pinned zero and the level verdict, as
`checkThmVal_bridge`'s test. -/
theorem typeIsPropC_run {env : Env} {fe : IFEnv} {cv : ConRon.Arena.Frontend.Olean.StmtRec}
    {c : ConstantVal} {s s' : AState} (hk : CoreSpec Arena.checkFuel) (hok : FoldOK env fe s)
    (hcv : denoteStmt s.store cv = some c) (hfv : c.type.hasFvar = false)
    (h : ConRon.Arena.Modular.typeIsPropC fe cv s = .ok (true, s')) :
    CheckOK false env fe s' ∧ Ext s.store s'.store ∧ s'.pins = s.pins ∧
      ConLeche.Modular.TypeIsProp .verified env c.type := by
  have hknot := hk.knot env fe hok.envWF
  have hsortS := hk.sort env fe hok.envWF
  have hwsty : ConLeche.Expr.WScoped 0 c.type := ConLeche.Expr.WScoped.of_not_hasFvar hfv
  have hty0 : denoteE s.store cv.type = some c.type := by
    simp only [denoteStmt] at hcv
    cases h1 : denoteN s.store.ns cv.name <;> cases h2 : cv.levelParams.mapM (denoteN s.store.ns) <;>
      cases h3 : denoteE s.store cv.type <;> simp_all
    cases hcv; rfl
  simp only [ConRon.Arena.Modular.typeIsPropC, Arena.zeroLevel] at h
  obtain ⟨stype, s1, ga, ra⟩ := AM.bind_ok h
  obtain ⟨hcka, hxa, hpa, hsima⟩ := AM.of_run (P := fun t => t = s)
    (Q := fun r t => CheckOK false env fe t ∧ Ext s.store t.store ∧ t.pins = s.pins ∧
      Core.SimE (ConLeche.inferTypeCore .verified false env) 0 c.type t.store r)
    rfl ga (hknot.infer s 0 cv.type c.type hok.check hty0 hwsty)
  obtain ⟨sty, hsty, hwssty, Fa, hFa⟩ := hsima
  obtain ⟨u, s2, gb, rb⟩ := AM.bind_ok ra
  obtain ⟨hckb, hxb, hpb, hsimb⟩ := AM.of_run (P := fun t => t = s1)
    (Q := fun r t => CheckOK false env fe t ∧ Ext s1.store t.store ∧ t.pins = s1.pins ∧
      SimL (ConLeche.ensureSortCore .verified false env) 0 sty t.store r)
    rfl gb (hsortS s1 0 stype sty hcka hsty hwssty)
  obtain ⟨uu, huu, Fb, hFb⟩ := hsimb
  obtain ⟨z, s3, gc, rc⟩ := AM.bind_ok rb
  obtain ⟨hs3, hz⟩ := AM.of_run (P := fun t => t = s2)
    (Q := fun r t => t = s2 ∧ denoteL s2.store.ls r = some .zero)
    rfl gc (pinZeroLevel_spec s2 hckb.pins)
  rw [hs3] at rc
  obtain ⟨o, s4, gd, rd⟩ := AM.bind_ok rc
  obtain ⟨hckd, hstd, hpd, lu, lv, hlu, hlv, hod⟩ := AM.of_run
    (P := fun t => t = s2)
    (Q := fun r t => CheckOK false env fe t ∧ t.store = s2.store ∧
      t.pins = s2.pins ∧ ∃ lu lv, denoteL s2.store.ls u = some lu ∧
        denoteL s2.store.ls z = some lv ∧ r = ConLeche.Level.isEquiv lu lv)
    rfl gd (Core.lvlEq?_spec s2 u z hckb)
  rw [Option.some.inj (hlu.symm.trans huu), Option.some.inj (hlv.symm.trans hz)] at hod
  cases o with
  | none => exact absurd rd (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)
  | some bb =>
  obtain ⟨hbb, rfl⟩ := AM.pure_ok rd
  refine ⟨hckd, by rw [hstd]; exact hxa.trans hxb, by rw [hpd, hpb, hpa], ?_⟩
  refine ⟨max Fa Fb, sty, uu, ConLeche.inferTypeCore_mono (Nat.le_max_left _ _) hFa,
    ConLeche.ensureSortCore_mono (Nat.le_max_right _ _) hFb, ?_⟩
  rw [← hod, hbb]

end ConRon.Bridge.Modular

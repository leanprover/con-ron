/-
# `ConRon.Bridge.Core.Walks.ProjGuard` — the projection guard, at use

con-leche task #480 checks official `infer_proj`'s restriction where a `.proj`
node is typed (`ConLeche/Kernel/Core.lean:1072-1119`): `projGuardSort`
(`Walks/Former.lean`) decides whether the structure may be a proposition at
the use's levels, `projGuardRows` reads the domains that must then be
propositions off the stored constructor's telescope, and `checkGuardRows`
infers each at the io grade and compares its sort.  This module is Theorem 1
for those walks and for `checkProjGuard`, which `inferProj`
(`Arms/Infer.lean`) runs.
-/
module

public import ConRon.Bridge.Core.Walks.Former
import ConRon.Bridge.Core.Walks.IotaLeaves
public import ConRon.Bridge.Core.Walks.Telescope
public import ConLeche.Verify.ProjGuard
import ConLeche.Verify.Cached.DiscC4
import ConLeche.Kernel.CheckerBase
import ConRon.Bridge.Core.Walks.PropRead
import ConRon.Bridge.Core.Walks.Nat
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.Core.Walks.Proj
import ConRon.Bridge.Core.Memo
import ConRon.Bridge.ExprOps.Inst1
public import ConRon.Bridge.Core.Knot
public import ConRon.Bridge.Grind
import ConRon.Bridge.Specs
import ConRon.Bridge.GrindAttr

public section

namespace ConRon.Bridge.Core

set_option autoImplicit false
set_option experimental.vcgen true
set_option maxHeartbeats 1000000

open ConLeche ConRon.Arena ConRon.Bridge Std.WP
open scoped Lean.Order

variable {eager : Bool} {env : Env} {fe : IFEnv}

/-- con-leche: none — a denoting projection entry survives a store extension. -/
theorem denoteProjEntry_ext {st st' : EStore} {e : IProjEntry} {p : ProjEntry}
    (h : denoteProjEntry st e = some p) (hx : Ext st st') :
    denoteProjEntry st' e = some p := by
  obtain ⟨h1, h2, h3, h4, -, -, -⟩ := denoteProjEntry_inv h
  simp only [denoteProjEntry] at h ⊢
  rw [denoteN_ext h1 hx, denoteNListE_ext hx _ _ h2, denoteN_ext h3 hx, denote_ext h4 hx]
  rw [h1, h2, h3, h4] at h
  exact h

/-- con-leche: ConLeche/Kernel/Core.lean:1106-1119 checkProjGuard — **the
guard's answer**: the pure guard passes at some fuel (it answers `()` or
throws, so passing is all a run says). -/
@[expose] def GuardOK (eager : Bool) (env : Env) (p : ProjEntry) (us : List Level) : Prop :=
  ∃ F, checkProjGuard (pureFns .verified eager env F).inferIO (pureFns .verified eager env F).whnf
    env p us = .ok ()

/-! ## The rows, read off the opened constructor telescope -/

/-- con-leche: none — the denotation of a row list: each row's depth, and its
term's denotation. -/
@[expose] def denoteRows (st : EStore) : List (Nat × EIdx) → Option (List (Nat × Expr))
  | [] => some []
  | (d, h) :: rs =>
    match denoteE st h, denoteRows st rs with
    | some x, some xs => some ((d, x) :: xs)
    | _, _ => none

/-- con-leche: none — the denotation of an appended row list. -/
theorem denoteRows_append {st : EStore} :
    ∀ {as bs : List (Nat × EIdx)} {xs ys : List (Nat × Expr)},
      denoteRows st as = some xs → denoteRows st bs = some ys →
      denoteRows st (as ++ bs) = some (xs ++ ys)
  | [], bs, xs, ys, ha, hb => by
    simp only [denoteRows, Option.some.injEq] at ha; subst ha; simpa using hb
  | (d, h) :: as, bs, xs, ys, ha, hb => by
    simp only [denoteRows] at ha
    cases hh : denoteE st h with
    | none => rw [hh] at ha; simp at ha
    | some x =>
      cases has : denoteRows st as with
      | none => rw [hh, has] at ha; simp at ha
      | some xs' =>
        rw [hh, has] at ha
        cases ha
        simp only [List.cons_append, denoteRows, hh, denoteRows_append has hb]

/-- con-leche: none — a row list's denotation survives a store extension. -/
theorem denoteRows_ext {st st' : EStore} (hx : Ext st st') :
    ∀ {rs : List (Nat × EIdx)} {xs : List (Nat × Expr)},
      denoteRows st rs = some xs → denoteRows st' rs = some xs
  | [], xs, h => h
  | (d, h) :: rs, xs, hr => by
    simp only [denoteRows] at hr ⊢
    cases hh : denoteE st h with
    | none => rw [hh] at hr; simp at hr
    | some x =>
      cases hrs : denoteRows st rs with
      | none => rw [hh, hrs] at hr; simp at hr
      | some xs' =>
        rw [hh, hrs] at hr
        rw [denote_ext hh hx, denoteRows_ext hx hrs]
        exact hr

/-- con-leche: none — the denotation of an optional row array. -/
@[expose] def denoteRowsO (st : EStore) : Option (Array (Nat × EIdx)) →
    Option (Option (List (Nat × Expr)))
  | none => some none
  | some a => (denoteRows st a.toList).map some

open Guard in
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1080-1098 projGuardRowsGo — **the
field loop, in run form**: the accumulator in push order, the answer the cited
loop's rows after it. -/
theorem projGuardRowsGo_run : ∀ (k : Nat) {d : Nat} {h : EIdx} {hP : Expr}
    {out : Array (Nat × EIdx)} {outP : List (Nat × Expr)} {s₀ s' : AState}
    {r : Option (Array (Nat × EIdx))}, StateOK s₀ → denoteE s₀.store h = some hP →
    denoteRows s₀.store out.toList = some outP →
    ConRon.Arena.projGuardRowsGo k d h out s₀ = .ok (r, s') →
    PStep s₀ s' ∧
      denoteRowsO s'.store r = some ((ConLeche.projGuardRowsGo k d hP).map (outP ++ ·)) := by
  intro k
  induction k with
  | zero =>
    intro d h hP out outP s₀ s' r hok hh ho hrun
    rw [ConRon.Arena.projGuardRowsGo] at hrun
    obtain ⟨v₀, hv₀⟩ := denoteE_view hh
    replace hrun := tagIf_view_run hv₀
      (fun hne => by cases v₀ <;> first | rfl | exact absurd rfl hne) hrun
    obtain ⟨v, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hv⟩ := view_run k1
    rw [hs1] at z1
    cases v
    case forallE dom body =>
      obtain ⟨domP, bodyP, rfl, hd, hb⟩ := denote_forallE_inv hok.wf hv hh
      have hsing : denoteRows s₀.store [(d, dom)] = some [(d, domP)] := by
        simp [denoteRows, hd]
      have happ := denoteRows_append ho hsing
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
      refine ⟨PStep.refl hok, ?_⟩
      simp [denoteRowsO, ConLeche.projGuardRowsGo, Array.toList_push, happ]
    all_goals
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
      refine ⟨PStep.refl hok, ?_⟩
      rw [denoteE_view_eq hok.wf hv] at hh
      cases hP
      case forallE a b => simp [denoteEView] at hh
      all_goals simp [denoteRowsO, ConLeche.projGuardRowsGo]
  | succ k ih =>
    intro d h hP out outP s₀ s' r hok hh ho hrun
    rw [ConRon.Arena.projGuardRowsGo] at hrun
    obtain ⟨v₀, hv₀⟩ := denoteE_view hh
    replace hrun := tagIf_view_run hv₀
      (fun hne => by cases v₀ <;> first | rfl | exact absurd rfl hne) hrun
    obtain ⟨v, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hv⟩ := view_run k1
    rw [hs1] at z1
    cases v
    case forallE dom body =>
      obtain ⟨domP, bodyP, rfl, hd, hb⟩ := denote_forallE_inv hok.wf hv hh
      dsimp only at z1
      obtain ⟨u, s2, k2, z2⟩ := AM.bind_ok z1
      obtain ⟨p2, hu⟩ := hasLooseBVarBFast_spec 0 body bodyP s₀ s2 u hok hb k2
      have hu' : u = bodyP.hasLooseBVarB 0 := hu
      subst hu'
      simp only [ConLeche.projGuardRowsGo]
      cases hl : bodyP.hasLooseBVarB 0
      · rw [hl] at z2
        simp only [Bool.false_eq_true, ite_false] at z2
        exact (fun ⟨p3, h3⟩ => ⟨p2.trans p3, h3⟩)
          (ih p2.ok (denote_ext hb p2.ext) (denoteRows_ext p2.ext ho) z2)
      · rw [hl] at z2
        simp only [ite_true] at z2
        obtain ⟨fv, s3, k3, z3⟩ := AM.bind_ok z2
        have hd2 := denote_ext hd p2.ext
        obtain ⟨p3, hfv⟩ := internE_run p2.ok (viewOK_fvar (by rw [hd2]; rfl)) k3
        have hfv' : denoteE s3.store fv = some (.fvar d domP) := by
          rw [hfv]; simp [denoteEView, denote_ext hd2 p3.ext]
        obtain ⟨b2, s4, k4, z4⟩ := AM.bind_ok z3
        have hb3 : denoteE s3.store body = some bodyP := denote_ext hb (p2.ext.trans p3.ext)
        obtain ⟨h1, h2, h4, h5, -, h7⟩ := ExprOps.instantiate1Fast_run p3.ok hfv'
          (by rw [hb3]; rfl) k4
        have p4 : PStep s3 s4 := PStep.of_caches h1 h2 h4 h5
        have hop : denoteE s4.store b2 = some (bodyP.instantiate1 (.fvar d domP) 0) :=
          h7 _ hb3
        have p24 := p2.trans (p3.trans p4)
        have ho4 : denoteRows s4.store (out.push (d, dom)).toList = some (outP ++ [(d, domP)]) := by
          rw [Array.toList_push]
          exact denoteRows_append (denoteRows_ext p24.ext ho)
            (by simp [denoteRows, denote_ext hd p24.ext])
        obtain ⟨p5, hr⟩ := ih p4.ok hop ho4 z4
        refine ⟨p24.trans p5, ?_⟩
        rw [hr]
        cases ConLeche.projGuardRowsGo k (d + 1) (bodyP.instantiate1 (.fvar d domP)) <;>
          simp
    all_goals
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
      refine ⟨PStep.refl hok, ?_⟩
      rw [denoteE_view_eq hok.wf hv] at hh
      cases hP
      case forallE a b => simp [denoteEView] at hh
      all_goals simp [denoteRowsO, ConLeche.projGuardRowsGo]

/-- con-leche: none — the denotation of an optional handle. -/
@[expose] def denoteOE (st : EStore) : Option EIdx → Option (Option Expr)
  | none => some none
  | some h => (denoteE st h).map some

open Guard in
/-- con-leche: ConLeche/Cached/ExprOpsC.lean:2166-2178 projGuardFastC — **the
guard's fast case, in run form**: every query is the window query, so the
answer is the cached fast case's. -/
theorem projGuardFast_run : ∀ (k : Nat) {j : Nat} {h : EIdx} {hP : Expr} {s₀ s' : AState}
    {r : Option EIdx}, StateOK s₀ → denoteE s₀.store h = some hP →
    ConRon.Arena.projGuardFast k j h s₀ = .ok (r, s') →
    PStep s₀ s' ∧ denoteOE s'.store r = some (ConLeche.projGuardFastC k j hP) := by
  intro k
  induction k with
  | zero =>
    intro j h hP s₀ s' r hok hh hrun
    rw [ConRon.Arena.projGuardFast] at hrun
    obtain ⟨v₀, hv₀⟩ := denoteE_view hh
    replace hrun := tagIf_view_run hv₀
      (fun hne => by cases v₀ <;> first | rfl | exact absurd rfl hne) hrun
    obtain ⟨v, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hv⟩ := view_run k1
    rw [hs1] at z1
    cases v
    case forallE dom body =>
      obtain ⟨domP, bodyP, rfl, hd, hb⟩ := denote_forallE_inv hok.wf hv hh
      dsimp only at z1
      obtain ⟨u, s2, k2, z2⟩ := AM.bind_ok z1
      obtain ⟨p2, hu⟩ := hasLooseBVarIn_spec 0 j h (.forallE domP bodyP) s₀ s2 u hok hh k2
      have hu' : u = Expr.hasLooseBVarInC 0 j (.forallE domP bodyP) := hu
      subst hu'
      simp only [ConLeche.projGuardFastC]
      cases hl : Expr.hasLooseBVarInC 0 j (.forallE domP bodyP)
      · rw [hl] at z2
        simp only [Bool.false_eq_true, ite_false] at z2
        obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
        exact ⟨p2, by simp [denoteOE, denote_ext hd p2.ext]⟩
      · rw [hl] at z2
        simp only [ite_true] at z2
        obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
        exact ⟨p2, by simp [denoteOE]⟩
    all_goals
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
      refine ⟨PStep.refl hok, ?_⟩
      rw [denoteE_view_eq hok.wf hv] at hh
      cases hP
      case forallE a b => simp [denoteEView] at hh
      all_goals simp [denoteOE, ConLeche.projGuardFastC]
  | succ k ih =>
    intro j h hP s₀ s' r hok hh hrun
    rw [ConRon.Arena.projGuardFast] at hrun
    obtain ⟨v₀, hv₀⟩ := denoteE_view hh
    replace hrun := tagIf_view_run hv₀
      (fun hne => by cases v₀ <;> first | rfl | exact absurd rfl hne) hrun
    obtain ⟨v, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hv⟩ := view_run k1
    rw [hs1] at z1
    cases v
    case forallE dom body =>
      obtain ⟨domP, bodyP, rfl, hd, hb⟩ := denote_forallE_inv hok.wf hv hh
      dsimp only at z1
      obtain ⟨u, s2, k2, z2⟩ := AM.bind_ok z1
      obtain ⟨p2, hu⟩ := hasLooseBVarIn_spec 0 j dom domP s₀ s2 u hok hd k2
      have hu' : u = Expr.hasLooseBVarInC 0 j domP := hu
      subst hu'
      simp only [ConLeche.projGuardFastC]
      cases hl : Expr.hasLooseBVarInC 0 j domP
      · rw [hl] at z2
        simp only [Bool.false_eq_true, ite_false] at z2
        exact (fun ⟨p3, h3⟩ => ⟨p2.trans p3, h3⟩)
          (ih p2.ok (denote_ext hb p2.ext) z2)
      · rw [hl] at z2
        simp only [ite_true] at z2
        obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
        exact ⟨p2, by simp [denoteOE]⟩
    all_goals
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
      refine ⟨PStep.refl hok, ?_⟩
      rw [denoteE_view_eq hok.wf hv] at hh
      cases hP
      case forallE a b => simp [denoteEView] at hh
      all_goals simp [denoteOE, ConLeche.projGuardFastC]

open Guard in
/-- con-leche: ConLeche/Cached/ExprOpsC.lean:2180-2195 projGuardRowsC — **the
rows past the parameters' raw opening, in run form**: the fast case with its
one domain substituted, else the substituted residual stepped — the cached
rows' own `match`. -/
theorem projGuardRowsAt_run {entry : IProjEntry} {acc : Array EIdx} {ws : List Expr}
    {r : EIdx} {rP : Expr} {s₀ s' : AState} {o : Option (Array (Nat × EIdx))}
    (hok : StateOK s₀) (hacc : ExprOps.InstLVec s₀.store acc ws)
    (hr : denoteE s₀.store r = some rP)
    (hrun : ConRon.Arena.projGuardRowsAt entry acc r s₀ = .ok (o, s')) :
    PStep s₀ s' ∧ denoteRowsO s'.store o = some
      (match ConLeche.projGuardFastC entry.idx 0 rP with
        | some dom => some [(entry.numParams + entry.idx, Expr.instantiateListC dom ws entry.idx)]
        | none => ConLeche.projGuardRowsGoC entry.idx entry.numParams
            (Expr.instantiateListC rP ws)) := by
  unfold ConRon.Arena.projGuardRowsAt at hrun
  obtain ⟨f, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨p1, hf⟩ := projGuardFast_run entry.idx hok hr k1
  have hacc1 := hacc.ext p1.ext
  cases f with
  | some dom =>
    simp only [denoteOE, Option.map_eq_some_iff] at hf
    obtain ⟨domP, hdom, hfast⟩ := hf
    rw [← hfast]
    dsimp only at z1
    obtain ⟨dd, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨h1, h2, h4, h5, -, h7⟩ := ExprOps.instantiateListFast_run p1.ok hacc1
      (by rw [hdom]; rfl) k2
    have p2 : PStep s1 s2 := PStep.of_caches h1 h2 h4 h5
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
    refine ⟨p1.trans p2, ?_⟩
    simp [denoteRowsO, denoteRows, h7 _ hdom, Expr.instantiateListC_spec]
  | none =>
    simp only [denoteOE, Option.some.injEq] at hf
    rw [← hf]
    dsimp only at z1
    obtain ⟨r2, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨h1, h2, h4, h5, -, h7⟩ := ExprOps.instantiateListFast_run p1.ok hacc1
      (by rw [denote_ext hr p1.ext]; rfl) k2
    have p2 : PStep s1 s2 := PStep.of_caches h1 h2 h4 h5
    obtain ⟨p3, hrows⟩ := projGuardRowsGo_run entry.idx p2.ok
      (h7 _ (denote_ext hr p1.ext)) (outP := []) rfl z2
    refine ⟨p1.trans (p2.trans p3), ?_⟩
    rw [hrows]
    simp [Expr.instantiateListC_spec, ConLeche.Cached.projGuardRowsGoC_eq]

open Guard in
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1086-1103 projGuardRows
con-leche: ConLeche/Cached/CoreC.lean:978-991 checkProjRowsI — **THEOREM 1 for
`projGuardRows`**: the domains that must be propositions, read off the stored
constructor's telescope opened at the use's levels. -/
theorem projGuardRows_run (s₀ s' : AState) (entry : IProjEntry) (p : ProjEntry) (us : LsIdx)
    (ls : List Level) (r : Option (Array (Nat × EIdx))) (hok : CheckOK eager env fe s₀)
    (hp : denoteProjEntry s₀.store entry = some p) (hus : denoteLs s₀.store.lss us = some ls)
    (hrun : ConRon.Arena.projGuardRows fe entry us s₀ = .ok (r, s')) :
    CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
      denoteRowsO s'.store r = some (ConLeche.projGuardRows env.find? p ls) := by
  obtain ⟨-, -, hct, -, hidx, hnp, -⟩ := denoteProjEntry_inv hp
  unfold ConRon.Arena.projGuardRows at hrun
  cases hfc : fe.find? entry.ctor with
  | none =>
    rw [hfc] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    have hm := IFEnvOK.miss hok.state hok.ienv hct hfc
    refine ⟨hok, Ext.refl _, rfl, ?_⟩
    simp [denoteRowsO, ConLeche.projGuardRows, hm]
  | some ci =>
    rw [hfc] at hrun
    obtain ⟨nm', cP, hn', hci, hfind⟩ := hok.ienv.hit _ ci hfc
    obtain rfl := Option.some.inj (hn'.symm.trans hct)
    have hcv := denoteCI_toConstantVal hci
    have hname : cP.toConstantVal.name = p.ctor := env_find_name hfind
    obtain ⟨cty, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨hok1, hx1, hp1, hcty⟩ := AM.of_run (P := fun t => t = s₀) rfl k1
      (constTyAt_spec s₀ ci.toConstantVal us p.ctor ls cP hok
        (by rw [denoteCV_name hcv, hname]) hus hfind hcv)
    obtain ⟨o, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨p2, ho⟩ := openPisRawGo_run entry.numParams hok1.state
      (show ExprOps.InstLVec s1.store #[] [] from rfl) hcty k2
    have hok2 := hok1.monoF p2.ok p2.ext p2.cframe p2.pins
    -- the specification's rows are the cached rows (con-leche's
    -- `projGuardRowsC_some` / `projGuardRowsC_none`)
    have hspec : ConLeche.projGuardRows env.find? p ls =
        ConLeche.projGuardRowsC p.numParams p.idx
          (cP.toConstantVal.type.instantiateLevelParams cP.toConstantVal.levelParams ls) := by
      simp only [ConLeche.projGuardRows, hfind]
      split
      · next fvs r hop => exact (ConLeche.Cached.projGuardRowsC_some hop).symm
      · next hop => exact (ConLeche.Cached.projGuardRowsC_none hop).symm
    rw [hspec, hidx, hnp]
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
      refine ⟨hok2, hx1.trans p2.ext, p2.pins.trans hp1, ?_⟩
      have hn := (Option.some.inj ho).symm
      simp [denoteRowsO, ConLeche.projGuardRowsC, hn]
    | some q =>
      obtain ⟨fvs, acc, R⟩ := q
      obtain ⟨xs, ws, RP, hq, -, hacc, hR⟩ := denoteRaw_some_inv ho
      obtain ⟨p3, hr⟩ := projGuardRowsAt_run p2.ok hacc hR z2
      have hok3 := hok2.monoF p3.ok p3.ext p3.cframe p3.pins
      refine ⟨hok3, hx1.trans (p2.ext.trans p3.ext), p3.pins.trans (p2.pins.trans hp1), ?_⟩
      rw [hr]
      simp only [ConLeche.projGuardRowsC, hq]
      rfl

/-! ## The rows' sorts, at the knot -/

/-- con-leche: ConLeche/Kernel/Core.lean:1072-1086 checkGuardRows
con-leche: ConLeche/Cached/CoreC.lean:952-964 checkGuardRowsI — **THEOREM 1 for
`checkGuardRows`**, in run form: from row `i` on, each row's term inferred at
the io grade and head-normalised at its own depth, its sort zero wherever the
guard sort is. -/
theorem checkGuardRows_run {fuel : Nat} (hsim : KnotSpec eager env fe fuel) (g : Level)
    (rows : Array (Nat × EIdx)) :
    ∀ (k i : Nat) (s₀ s' : AState) (u : Unit) (rowsP : List (Nat × Expr)),
      rows.size - i = k → CheckOK eager env fe s₀ →
      denoteRows s₀.store (rows.toList.drop i) = some rowsP → GuardRowsWS rowsP →
      ConRon.Arena.checkGuardRows (coreKnot .verified eager fe id fuel) g rows i s₀ =
        .ok (u, s') →
      CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        ∃ F, ConLeche.checkGuardRows (pureFns .verified eager env F).inferIO
          (pureFns .verified eager env F).whnf g rowsP = .ok ()
  | 0, i, s₀, s', u, rowsP, hk, hok, hd, _, hrun => by
    rw [ConRon.Arena.checkGuardRows.eq_1, dite_eq_right (by omega)] at hrun
    obtain ⟨-, rfl⟩ := AM.pure_ok hrun
    rw [List.drop_eq_nil_of_le (by simp; omega)] at hd
    simp only [denoteRows, Option.some.injEq] at hd
    subst hd
    exact ⟨hok, Ext.refl _, rfl, 0, rfl⟩
  | k + 1, i, s₀, s', u, rowsP, hk, hok, hd, hws, hrun => by
    have hi : i < rows.size := by omega
    rw [ConRon.Arena.checkGuardRows.eq_1, dite_eq_left hi] at hrun
    rw [List.drop_eq_getElem_cons (by simpa using hi), Array.getElem_toList] at hd
    generalize hri : rows[i] = pr at hrun hd
    obtain ⟨d, dom⟩ := pr
    simp only [denoteRows] at hd
    cases hdom : denoteE s₀.store dom with
    | none => rw [hdom] at hd; simp at hd
    | some x =>
    cases hrest : denoteRows s₀.store (rows.toList.drop (i + 1)) with
    | none => rw [hdom, hrest] at hd; simp at hd
    | some restP =>
    rw [hdom, hrest] at hd
    cases hd
    have hwx := hws.head
    have hwr := hws.tail
    dsimp only at hrun
    obtain ⟨tt, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨hok1, hx1, hp1, tv, htv, hwtv, F1, hF1⟩ :=
      AM.of_run (P := fun t => t = s₀) rfl k1 (hsim.inferIO s₀ d dom x hok hdom hwx)
    obtain ⟨w, s2, k2, z2⟩ := AM.bind_ok z1
    obtain ⟨hok2, hx2, hp2, wv, hwv, -, F2, hF2⟩ :=
      AM.of_run (P := fun t => t = s1) rfl k2 (hsim.whnf s1 d tt tv hok1 htv hwtv)
    by_cases ht : (w.tag == ETag.sort) = true
    · rw [ite_eq_left ht] at z2
      obtain ⟨ov, s3, k3, z3⟩ := AM.bind_ok z2
      obtain ⟨hs3, hov⟩ := AM.of_run (P := fun t => t = s2) rfl k3 (viewSort_spec s2 w)
      rw [hs3] at z3
      cases ov with
      | none => exact absurd z3 AM.fail_ok
      | some lu =>
      obtain ⟨l, rfl, hl⟩ :=
        denote_sort_inv hok2.state.wf (view_of_viewSort_tag ht hov.symm) hwv
      obtain ⟨ul, s4, k4, z4⟩ := AM.bind_ok z3
      obtain ⟨hok4, hst4, hp4, hul⟩ :=
        AM.of_run (P := fun t => t = s2) rfl k4 (readLevelM_specC s2 lu hok2)
      rw [hl] at hul
      obtain rfl := Option.some.inj hul
      have hx04 : Ext s₀.store s4.store := by rw [hst4]; exact hx1.trans hx2
      have hp04 : s4.pins = s₀.pins := hp4.trans (hp2.trans hp1)
      by_cases hz : Level.zeroWhereZero g l = true
      · rw [ite_eq_left hz] at z4
        obtain ⟨hok5, hx5, hp5, F3, hF3⟩ := checkGuardRows_run hsim g rows k (i + 1) s4 s' u restP
          (by omega) hok4 (denoteRows_ext hx04 hrest) hwr z4
        refine ⟨hok5, hx04.trans hx5, hp5.trans hp04, max F1 (max F2 F3), ?_⟩
        have e1 : (pureFns .verified eager env (max F1 (max F2 F3))).inferIO d x = .ok tv :=
          ConLeche.inferTypeIO_mono (by omega) hF1
        have e2 : (pureFns .verified eager env (max F1 (max F2 F3))).whnf d tv = .ok (.sort l) :=
          ConLeche.whnf_mono (by omega) hF2
        simp only [ConLeche.checkGuardRows, e1, e2, bind, Except.bind, hz]
        exact checkGuardRowsFueled_mono (by omega) hF3
      · rw [ite_eq_right hz] at z4
        exact absurd z4 AM.fail_ok
    · rw [ite_eq_right ht] at z2
      exact absurd z2 AM.fail_ok

/-- con-leche: ConLeche/Verify/ProjGuard.lean:80 projGuardRows_ws — the rows
`projGuardRows` reads at a well-formed environment are scoped at their own
depths. -/
theorem projGuardRows_wsE (henv : EnvWF env) {p : ProjEntry} {ls : List Level}
    {rows : List (Nat × Expr)} (h : ConLeche.projGuardRows env.find? p ls = some rows) :
    GuardRowsWS rows :=
  ConLeche.projGuardRows_ws (fun _ hc => (henv.consts _ (Env.find?_mem hc)).1) h

/-- con-leche: ConLeche/Kernel/Core.lean:1106-1119 checkProjGuard
con-leche: ConLeche/Cached/CoreC.lean:993-1004 checkProjGuardI — **THEOREM 1
for `checkProjGuard`**: official `infer_proj`'s restriction at this use. -/
theorem checkProjGuard_spec {fuel : Nat} (hsim : KnotSpec eager env fe fuel)
    (henv : EnvWF env) (s₀ : AState) (entry : IProjEntry) (p : ProjEntry) (us : LsIdx)
    (ls : List Level) (hok : CheckOK eager env fe s₀)
    (hp : denoteProjEntry s₀.store entry = some p) (hus : denoteLs s₀.store.lss us = some ls) :
    ⦃fun s => s = s₀⦄
      ConRon.Arena.checkProjGuard (coreKnot .verified eager fe id fuel) fe entry us
    ⦃fun _ s' => CheckOK eager env fe s' ∧ Ext s₀.store s'.store ∧ s'.pins = s₀.pins ∧
        GuardOK eager env p ls; ⊤⦄ := by
  refine AM.triple_of_run_at fun u s' hrun => ?_
  obtain ⟨hsn, -, -, -, -, -, -⟩ := denoteProjEntry_inv hp
  unfold ConRon.Arena.checkProjGuard at hrun
  cases hfT : fe.find? entry.structName with
  | none => rw [hfT] at hrun; exact absurd hrun AM.fail_ok
  | some ci =>
    rw [hfT] at hrun
    cases ci with
    | indInfo cvT caps =>
        obtain ⟨nm', cP, hn', hci, hfind⟩ := hok.ienv.hit _ _ hfT
        obtain rfl := Option.some.inj (hn'.symm.trans hsn)
        obtain ⟨cvP, capsP, hcvP, hcapsP, rfl⟩ := denoteCI_indInfo_split hci
        have hcl : cvP.type.hasFvar = false := (henv.consts _ (Env.find?_mem hfind)).1
        obtain ⟨og, s1, k1, z1⟩ := AM.bind_ok hrun
        obtain ⟨hok1, hx1, hp1, F1, hF1⟩ := AM.of_run (P := fun t => t = s₀) rfl k1
          (projGuardSort_spec hsim s₀ cvT cvP caps capsP us ls hok hcvP hcapsP hus hcl)
        cases og with
        | none =>
          obtain ⟨-, rfl⟩ := AM.pure_ok z1
          refine ⟨hok1, hx1, hp1, F1, ?_⟩
          simp only [ConLeche.checkProjGuard, hfind, hF1, bind, Except.bind]; rfl
        | some gs =>
          dsimp only at z1
          obtain ⟨orow, s2, k2, z2⟩ := AM.bind_ok z1
          obtain ⟨hok2, hx2, hp2, hrows⟩ := projGuardRows_run s1 s2 entry p us ls orow hok1
            (denoteProjEntry_ext hp hx1) (denoteLs_ext hus hx1) k2
          cases orow with
          | none => exact absurd z2 AM.fail_ok
          | some rows =>
            dsimp only at z2
            simp only [denoteRowsO, Option.map_eq_some_iff] at hrows
            obtain ⟨rowsP, hdr, hpr⟩ := hrows
            have hpr' : ConLeche.projGuardRows env.find? p ls = some rowsP := hpr.symm
            obtain ⟨hok3, hx3, hp3, F3, hF3⟩ := checkGuardRows_run hsim gs rows rows.size 0 s2 s' u
              rowsP (by omega) hok2 (by simpa using hdr) (projGuardRows_wsE henv hpr') z2
            refine ⟨hok3, hx1.trans (hx2.trans hx3), hp3.trans (hp2.trans hp1), max F1 F3, ?_⟩
            simp only [ConLeche.checkProjGuard, hfind,
              projGuardSortFueled_mono (Nat.le_max_left F1 F3) hF1, bind, Except.bind, hpr']
            exact checkGuardRowsFueled_mono (Nat.le_max_right F1 F3) hF3
    | _ => exact absurd hrun AM.fail_ok

/-! ## The io view's guard is the record's

`inferBodyIO` runs `inferProj` at `CoreFnsA.ioView r`, whose `inferIO` and
`whnf` slots are `r`'s; the guard reads no other slot. -/

/-- con-leche: none — `formerSortLoop` reads only the `whnf` slot. -/
theorem formerSortLoop_ioView (r : CoreFnsA) :
    ∀ (n d : Nat) (e : EIdx),
      ConRon.Arena.formerSortLoop r.ioView d n e = ConRon.Arena.formerSortLoop r d n e
  | 0, d, e => rfl
  | n + 1, d, e => by
    simp only [ConRon.Arena.formerSortLoop, formerSortLoop_ioView r n]; rfl

/-- con-leche: none — `checkGuardRows` reads only the `inferIO` and `whnf`
slots. -/
theorem checkGuardRows_ioView (r : CoreFnsA) (g : Level) (rows : Array (Nat × EIdx))
    (i : Nat) :
    ConRon.Arena.checkGuardRows r.ioView g rows i = ConRon.Arena.checkGuardRows r g rows i := by
  rw [ConRon.Arena.checkGuardRows.eq_1 r.ioView, ConRon.Arena.checkGuardRows.eq_1 r]
  by_cases hi : i < rows.size
  · simp only [dite_eq_left hi, checkGuardRows_ioView r g rows (i + 1)]; rfl
  · simp only [dite_eq_right hi]
termination_by rows.size - i

/-- con-leche: none — `checkProjGuard` reads only the `inferIO` and `whnf`
slots. -/
theorem checkProjGuard_ioView (r : CoreFnsA) (entry : IProjEntry) (us : LsIdx) :
    ConRon.Arena.checkProjGuard r.ioView fe entry us =
      ConRon.Arena.checkProjGuard r fe entry us := by
  simp only [ConRon.Arena.checkProjGuard, ConRon.Arena.projGuardSort, formerSortLoop_ioView,
    checkGuardRows_ioView]

end ConRon.Bridge.Core

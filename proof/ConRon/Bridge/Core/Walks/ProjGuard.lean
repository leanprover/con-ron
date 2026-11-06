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
import ConLeche.Kernel.CheckerBase
import ConRon.Bridge.Core.Walks.PropRead
import ConRon.Bridge.Core.Walks.Cached
import ConRon.Bridge.Core.Walks.Proj
import ConRon.Bridge.Core.Memo
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

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1078-1084 projGuardRowsAt — the
row of field `j`, if it is one. -/
@[expose] def rowAt (cty : Expr) (nP idx : Nat) (fvs : List Expr) (j : Nat) :
    Option (Nat × Expr) :=
  if j = idx ∨ ConLeche.structUsedLater cty nP j = true then
    (fvs[nP + j]?).map fun x => (nP + j, x.fvarTypeD)
  else none

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1078-1084 projGuardRowsAt — the
rows of fields `j..idx`. -/
def rowsFrom (cty : Expr) (nP idx : Nat) (fvs : List Expr) (j : Nat) : List (Nat × Expr) :=
  if j > idx then [] else (rowAt cty nP idx fvs j).toList ++ rowsFrom cty nP idx fvs (j + 1)
termination_by idx + 1 - j

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1078-1084 projGuardRowsAt — the
cited `filterMap` over `range' j` is `rowsFrom j`. -/
theorem filterMap_range'_rowsFrom (cty : Expr) (nP idx : Nat) (fvs : List Expr) :
    ∀ (k j : Nat), idx + 1 - j = k →
      (List.range' j k).filterMap (rowAt cty nP idx fvs) = rowsFrom cty nP idx fvs j
  | 0, j, hk => by
    rw [rowsFrom, ite_eq_left (by omega)]; rfl
  | k + 1, j, hk => by
    rw [rowsFrom, ite_eq_right (by omega), List.range'_succ, List.filterMap_cons,
      ← filterMap_range'_rowsFrom cty nP idx fvs k (j + 1) (by omega)]
    cases rowAt cty nP idx fvs j <;> rfl

/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1078-1084 projGuardRowsAt — the
function is `rowsFrom 0`. -/
theorem projGuardRowsAt_eq (cty : Expr) (nP idx : Nat) (fvs : List Expr) :
    ConLeche.projGuardRowsAt cty nP idx fvs = rowsFrom cty nP idx fvs 0 := by
  rw [ConLeche.projGuardRowsAt, List.range_eq_range',
    ← filterMap_range'_rowsFrom cty nP idx fvs (idx + 1) 0 (by omega)]
  rfl

/-- con-leche: none — a denoting handle list read at an index: both miss, or
both hit and the hit denotes. -/
theorem denoteEList_getElem? {st : EStore} :
    ∀ {hs : List EIdx} {xs : List Expr}, Frontend.denoteEList st hs = some xs →
      ∀ (k : Nat), (hs[k]? = none ∧ xs[k]? = none) ∨
        ∃ h x, hs[k]? = some h ∧ xs[k]? = some x ∧ denoteE st h = some x
  | [], xs, hd, k => by
    rw [denoteEList_nil_inv hd]; exact Or.inl ⟨rfl, rfl⟩
  | h :: hs, xs, hd, k => by
    obtain ⟨x, xs', hx, hxs, rfl⟩ := denoteEList_cons_inv hd
    cases k with
    | zero => exact Or.inr ⟨h, x, rfl, rfl, hx⟩
    | succ k => simpa using denoteEList_getElem? hxs k

open Guard in
/-- con-leche: ConLeche/Kernel/CoreDefs.lean:1078-1084 projGuardRowsAt — **the
rows, in run form**: the accumulator in push order, the answer the cited
`filterMap` from `j` on. -/
theorem projGuardRowsAt_run (cty : EIdx) (ctyP : Expr) (nP idx : Nat) (fvs : List EIdx)
    (fvsP : List Expr) :
    ∀ (k j : Nat) (out : Array (Nat × EIdx)) (outP : List (Nat × Expr))
      (s₀ s' : AState) (r : Array (Nat × EIdx)), idx + 1 - j = k → StateOK s₀ →
      denoteE s₀.store cty = some ctyP → Frontend.denoteEList s₀.store fvs = some fvsP →
      denoteRows s₀.store out.toList = some outP →
      ConRon.Arena.projGuardRowsAt cty nP idx fvs j out s₀ = .ok (r, s') →
      PStep s₀ s' ∧ denoteRows s'.store r.toList = some (outP ++ rowsFrom ctyP nP idx fvsP j)
  | 0, j, out, outP, s₀, s', r, hk, hok, hc, hf, ho, hrun => by
    rw [ConRon.Arena.projGuardRowsAt, ite_eq_left (by omega)] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    rw [rowsFrom, ite_eq_left (by omega), List.append_nil]
    exact ⟨PStep.refl hok, ho⟩
  | k + 1, j, out, outP, s₀, s', r, hk, hok, hc, hf, ho, hrun => by
    rw [ConRon.Arena.projGuardRowsAt, ite_eq_right (by omega)] at hrun
    have common : ∀ (used : Bool) (s₁ : AState),
        used = (j == idx || ConLeche.structUsedLater ctyP nP j) → PStep s₀ s₁ →
        (if (!used) = true then ConRon.Arena.projGuardRowsAt cty nP idx fvs (j + 1) out
          else
            match fvs[nP + j]? with
            | some x => do
              let ty ← fvarTypeD x
              ConRon.Arena.projGuardRowsAt cty nP idx fvs (j + 1) (out.push (nP + j, ty))
            | none => ConRon.Arena.projGuardRowsAt cty nP idx fvs (j + 1) out) s₁ = .ok (r, s') →
        PStep s₀ s' ∧ denoteRows s'.store r.toList =
          some (outP ++ rowsFrom ctyP nP idx fvsP j) := by
      intro used s₁ hu p1 h2
      have hc1 := denote_ext hc p1.ext
      have hf1 := denoteEList_ext p1.ext _ _ hf
      have ho1 := denoteRows_ext p1.ext ho
      have ih := projGuardRowsAt_run cty ctyP nP idx fvs fvsP k (j + 1)
      rw [rowsFrom, ite_eq_right (by omega)]
      by_cases hb : used = true
      · rw [ite_eq_right (by simp [hb])] at h2
        have hcond : j = idx ∨ ConLeche.structUsedLater ctyP nP j = true := by
          rw [hb] at hu; simpa using hu.symm
        rcases denoteEList_getElem? hf1 (nP + j) with ⟨hn, hnP⟩ | ⟨h, x, hh, hx, hdx⟩
        · rw [hn] at h2
          obtain ⟨p2, hr⟩ := ih out outP s₁ s' r (by omega) p1.ok hc1 hf1 ho1 h2
          refine ⟨p1.trans p2, ?_⟩
          rw [hr]; simp [rowAt, hcond, hnP]
        · rw [hh] at h2
          obtain ⟨ty, s₂, h3, h4⟩ := AM.bind_ok h2
          obtain ⟨rfl, hty⟩ := fvarTypeD_run p1.ok hdx h3
          obtain ⟨p2, hr⟩ := ih (out.push (nP + j, ty)) (outP ++ [(nP + j, x.fvarTypeD)]) s₂ s' r
            (by omega) p1.ok hc1 hf1
            (by
              rw [Array.toList_push]
              exact denoteRows_append ho1 (by simp [denoteRows, hty])) h4
          refine ⟨p1.trans p2, ?_⟩
          rw [hr]; simp [rowAt, hcond, hx]
      · rw [ite_eq_left (by simp [hb])] at h2
        have hcond : ¬ (j = idx ∨ ConLeche.structUsedLater ctyP nP j = true) := by
          intro h; apply hb; rw [hu]; rcases h with h | h <;> simp [h]
        obtain ⟨p2, hr⟩ := ih out outP s₁ s' r (by omega) p1.ok hc1 hf1 ho1 h2
        refine ⟨p1.trans p2, ?_⟩
        rw [hr]; simp [rowAt, hcond]
    split at hrun
    next hj =>
      obtain ⟨used, s₁, h1, h2⟩ := AM.bind_ok hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h1
      exact common true _ (by simp [hj]) (PStep.refl hok) h2
    next hj =>
      obtain ⟨used, s₁, h1, h2⟩ := AM.bind_ok hrun
      obtain ⟨p, hr⟩ := structUsedLater_spec cty ctyP nP j s₀ s₁ used hok hc h1
      exact common used s₁ (by simp only [hj, Bool.false_or]; exact hr) p h2

/-- con-leche: none — the denotation of an optional row array. -/
@[expose] def denoteRowsO (st : EStore) : Option (Array (Nat × EIdx)) →
    Option (Option (List (Nat × Expr)))
  | none => some none
  | some a => (denoteRows st a.toList).map some

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
    obtain ⟨p2, ho⟩ := openPisAtFvarsF_run hok1.state hcty k2
    have hok2 := hok1.monoF p2.ok p2.ext p2.cframe p2.pins
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z2
      refine ⟨hok2, hx1.trans p2.ext, p2.pins.trans hp1, ?_⟩
      have hn : ConLeche.openPisAtFvars (p.numParams + p.idx + 1)
          (cP.toConstantVal.type.instantiateLevelParams cP.toConstantVal.levelParams ls) 0 =
          none := by rw [hnp, hidx]; exact (Option.some.inj ho).symm
      simp [denoteRowsO, ConLeche.projGuardRows, hfind, hn]
    | some q =>
      obtain ⟨fvs, e⟩ := q
      obtain ⟨xs, x, hx, hfvs, -⟩ := denoteOpen_some_inv ho
      obtain ⟨rows, s3, k3, z3⟩ := AM.bind_ok z2
      obtain ⟨-, -, hty⟩ := denoteCV_inv hcv
      obtain ⟨p3, hr⟩ := projGuardRowsAt_run ci.toConstantVal.type cP.toConstantVal.type
        entry.numParams entry.idx fvs xs (entry.idx + 1) 0 #[] [] s2 s3 rows (by omega) p2.ok
        (denote_ext hty (hx1.trans p2.ext)) hfvs rfl k3
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z3
      have hok3 := hok2.monoF p3.ok p3.ext p3.cframe p3.pins
      refine ⟨hok3, hx1.trans (p2.ext.trans p3.ext), p3.pins.trans (p2.pins.trans hp1), ?_⟩
      simp only [denoteRowsO, ConLeche.projGuardRows, hfind, hnp, hidx, hx, hr,
        projGuardRowsAt_eq, List.nil_append, Option.map_some]

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
  sorry

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

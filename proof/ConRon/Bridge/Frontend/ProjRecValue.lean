/-
# `ConRon.Bridge.Frontend.ProjRecValue` — the projection rewrite, at its
exact letter (task #97-P3-Frontend round 8)

`Arena/Frontend/ProjRec.lean`'s `projRecValue` against con-leche's
(`ConLeche/Frontend/ProjRec.lean:279-330`), and `projRewriteD` on top of it —
moved here from `Bridge/Frontend/ProjRec.lean` because the rewrite's cone
needs the Inductives tier's run-form lemmas (`Bridge/Inductives/Rel.lean`),
which that module does not import.

## The frame, and why it is `PStep` inside and `ParseStep` outside

Every callee of the rewrite has a run-form lemma at `Bridge/Inductives/
Rel.lean`'s `PStep` (store grew, binder data grew, pins still, caches up to
`CacheFrame`), so the whole walk is composed at `PStep`.  `PStep` has no
scratch clause; `Bridge/Frontend/Scratch.lean`'s `projRecValue_scratch` is
the one fact that turns the composed `PStep` into the parse's `ParseStep`
(`ParseStep.ofPStep`), and it is what makes the answer's `PersE` a corollary
of its denotation.

## The readback caches

`instLPFast` reads the recursor's level parameters and the chosen levels
back through `readNamesM`/`readLevelsM`, so its answer is exact only where the
three readback memos are sound (`Bridge/ExprOps/Owed.lean`'s
`instLPFast_spec`).  The statement takes them as `ReadCachesOK s` — round 8's
ruling — and the parse threads them from the capstones' empty caches through
`ParseStep.cframe`'s implications.

## Two-sided

Every twin `none` is a con-leche `none` (`OptRel`): `processLineCoreD` pushes
the ORIGINAL value where the rewrite declines, so the two declines must
coincide.  Each decline of the twin is read against the matching `guard` or
`match` of con-leche's `Option` block: `denoteN_inj` at the three name
comparisons, the views' constructors at the shape tests.
-/
import ConRon.Bridge.Frontend.ProjRec
import ConRon.Bridge.Inductives.Rel

namespace ConRon.Bridge.Frontend

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend

/-! ## The frame -/

/-- con-leche: none — a `PStep` that also kept the scratch flag is a parse
step. -/
theorem ParseStep.ofPStep {s s' : AState} (h : Inductives.PStep s s')
    (hsc : s'.store.scratchOn = s.store.scratchOn) : ParseStep s s' :=
  ⟨h.ok, h.ext, hsc, h.cframe, h.pins⟩

/-- con-leche: none — the three readback invariants survive a `PStep`, by its
cache frame's implications. -/
theorem ReadCachesOK.pstep {s s' : AState} (h : ReadCachesOK s)
    (hs : Inductives.PStep s s') : ReadCachesOK s' :=
  ⟨hs.cframe.readL h.readL, hs.cframe.readN h.readN, hs.cframe.readLs h.readLs⟩

/-- con-leche: none — `internName` at `PStep`: the nested interner keeps the
expression tiers and the flag, so `BMExt` is `bmExt_of_nested`. -/
theorem internName_pstep {s s' : AState} (hok : StateOK s) {nm : ConLeche.Name}
    {h : NIdx} (hrun : ConRon.Arena.internName nm s = .ok (h, s')) :
    Inductives.PStep s s' ∧ denoteN s'.store.ns h = some nm := by
  obtain ⟨hwf, hx, hp, hs, hon, -, hc, hpn, hden⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internName_spec s nm hok.wf)
  exact ⟨Inductives.PStep.of_caches ⟨hwf⟩ hx (Inductives.bmExt_of_nested hp hs hon)
    hc hpn, hden⟩

/-! ## The binder lists -/

/-- con-leche: none — `stripPisAll_run`'s element relation IS `denoteBL`. -/
theorem denoteBL_of_listRel {st : EStore} :
    ∀ {bs : List (EIdx × BinderMeta)} {bsP : List (Expr × BinderMeta)},
      ListRel (fun (p : EIdx × BinderMeta) (q : Expr × BinderMeta) =>
        denoteE st p.1 = some q.1 ∧ p.2 = q.2) bs bsP →
      ExprOps.denoteBL st bs = some bsP := by
  intro bs bsP h
  induction h with
  | nil => rfl
  | @cons a b as bs' hab _ ih =>
    obtain ⟨t, m⟩ := a
    obtain ⟨x, m'⟩ := b
    obtain ⟨ht, rfl⟩ := hab
    simp only [ExprOps.denoteBL, ht, ih]

/-- con-leche: none — a binder list that denotes has as many binders as its
denotation. -/
theorem denoteBL_length {st : EStore} :
    ∀ {bs : List (EIdx × BinderMeta)} {bsP : List (Expr × BinderMeta)},
      ExprOps.denoteBL st bs = some bsP → bs.length = bsP.length := by
  intro bs
  induction bs with
  | nil => intro bsP h; simp only [ExprOps.denoteBL, Option.some.injEq] at h; subst h; rfl
  | cons p bs ih =>
    intro bsP h
    obtain ⟨t, m⟩ := p
    simp only [ExprOps.denoteBL] at h
    cases ht : denoteE st t with
    | none => rw [ht] at h; simp at h
    | some x =>
      cases hb : ExprOps.denoteBL st bs with
      | none => rw [ht, hb] at h; simp at h
      | some xs =>
        rw [ht, hb] at h
        obtain rfl := Option.some.inj h
        simp [ih hb]

/-- con-leche: ConLeche/Frontend/ProjRec.lean:247-249 mkLams — the rebuild at
`PStep`: `mkLams_run` without the scratch flag, for a caller composing at the
Inductives tier's frame. -/
theorem mkLams_pstep {s : AState} (hok : StateOK s) {body : EIdx} {bodyP : Expr}
    (hb : denoteE s.store body = some bodyP) :
    ∀ {bs : List (EIdx × BinderMeta)} {bsP : List (Expr × BinderMeta)},
      ExprOps.denoteBL s.store bs = some bsP →
      ∀ {h : EIdx} {s' : AState}, mkLams bs body s = .ok (h, s') →
        Inductives.PStep s s' ∧
          denoteE s'.store h = some (ConLeche.Frontend.mkLams bsP bodyP) := by
  intro bs
  induction bs with
  | nil =>
    intro bsP hbs h s' hrun
    simp only [ExprOps.denoteBL, Option.some.injEq] at hbs
    subst hbs
    rw [ConRon.Arena.Frontend.mkLams] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨Inductives.PStep.refl hok, hb⟩
  | cons p bs ih =>
    intro bsP hbs h s' hrun
    obtain ⟨t, m⟩ := p
    simp only [ExprOps.denoteBL] at hbs
    cases ht : denoteE s.store t with
    | none => rw [ht] at hbs; simp at hbs
    | some x =>
      cases hbl : ExprOps.denoteBL s.store bs with
      | none => rw [ht, hbl] at hbs; simp at hbs
      | some xs =>
        rw [ht, hbl] at hbs
        obtain rfl := Option.some.inj hbs
        rw [ConRon.Arena.Frontend.mkLams] at hrun
        obtain ⟨acc, s₁, h1, h2⟩ := AM.bind_ok hrun
        obtain ⟨p1, hacc⟩ := ih hbl h1
        obtain ⟨p2, hd⟩ := Inductives.internLamE_run p1.ok (denote_ext ht p1.ext) hacc h2
        refine ⟨p1.trans p2, ?_⟩
        rw [hd]
        rfl

/-! ## `headIs`, `instPisOpen` -/

/-- con-leche: ConLeche/Frontend/ProjRec.lean:271-277 headIs — read-only, and
the one name comparison is exact both ways by `denoteN_inj`. -/
theorem headIs_run {s s' : AState} (hok : StateOK s) {fuel : Nat} {T : NIdx}
    {TP : ConLeche.Name} (hT : denoteN s.store.ns T = some TP) {e : EIdx}
    {eP : Expr} (he : denoteE s.store e = some eP) {b : Bool}
    (hrun : headIs fuel T e s = .ok (b, s')) :
    s' = s ∧ b = ConLeche.Frontend.headIs TP eP := by
  rw [ConRon.Arena.Frontend.headIs] at hrun
  obtain ⟨f, s₁, h1, hr1⟩ := AM.bind_ok hrun
  obtain ⟨v, s₂, h2, hr2⟩ := AM.bind_ok hr1
  obtain ⟨hs1, hf⟩ := Inductives.getAppFn_run hok he h1
  subst hs1
  obtain ⟨hs2, hv⟩ := view_run h2
  subst hs2
  have hdv := hf
  rw [denoteE_view_eq hok.wf hv] at hdv
  unfold ConLeche.Frontend.headIs
  cases v with
  | const n us =>
    obtain ⟨nm, ls, hc, hn, -⟩ := denote_const_inv hok.wf hv hf
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hr2
    refine ⟨rfl, ?_⟩
    rw [hc]
    simp only []
    by_cases hnt : n = T
    · subst hnt
      rw [Option.some.inj (hn.symm.trans hT)]; simp
    · have : nm ≠ TP := fun h => hnt (denoteN_inj (nsWF_of_StateOK hok) hn (h ▸ hT))
      rw [beq_eq_false_iff_ne.mpr hnt, beq_eq_false_iff_ne.mpr this]
  | _ =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hr2
    refine ⟨rfl, ?_⟩
    split
    · rename_i nm ls hc
      rw [hc] at hdv
      obtain ⟨_, _, hv', -, -⟩ := denoteEView_const hdv
      exact absurd hv' (by simp)
    · rfl

/-- con-leche: ConLeche/Frontend/ProjRec.lean:251-257 instPisOpen — the
residual telescope, instantiated at open arguments.  Structural on the
argument list; each step is `instantiate1LiftFast_run` at the peeled body. -/
theorem instPisOpen_run {fuel : Nat} :
    ∀ (args : List EIdx) (argsP : List Expr) {s s' : AState} {h : EIdx}
      {hP : Expr} {r : Option EIdx}, StateOK s →
      denoteE s.store h = some hP →
      Frontend.denoteEList s.store args = some argsP →
      instPisOpen fuel h args s = .ok (r, s') →
      Inductives.PStep s s' ∧
        OptRel (fun (h : EIdx) (e : Expr) => denoteE s'.store h = some e) r
          (ConLeche.Frontend.instPisOpen hP argsP) := by
  intro args
  induction args with
  | nil =>
    intro argsP s s' h hP r hok hh hargs hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at hargs
    subst hargs
    rw [ConRon.Arena.Frontend.instPisOpen] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨Inductives.PStep.refl hok, by simpa [ConLeche.Frontend.instPisOpen, OptRel] using hh⟩
  | cons a as ih =>
    intro argsP s s' h hP r hok hh hargs hrun
    simp only [Frontend.denoteEList] at hargs
    cases ha : denoteE s.store a with
    | none => rw [ha] at hargs; simp at hargs
    | some x =>
      cases has : Frontend.denoteEList s.store as with
      | none => rw [ha, has] at hargs; simp at hargs
      | some xs =>
        rw [ha, has] at hargs
        obtain rfl := Option.some.inj hargs
        rw [ConRon.Arena.Frontend.instPisOpen] at hrun
        obtain ⟨v, s₁, h1, hr1⟩ := AM.bind_ok hrun
        obtain ⟨hs1, hv⟩ := view_run h1
        subst hs1
        have hdv := hh
        rw [denoteE_view_eq hok.wf hv] at hdv
        cases v with
        | forallE ty body m =>
          obtain ⟨et, eb, rfl, -, hb⟩ := denote_forallE_inv hok.wf hv hh
          obtain ⟨b, s₂, h2, hr2⟩ := AM.bind_ok hr1
          obtain ⟨hok2, hx2, hbm2, hc2, hp2, -, hb2⟩ :=
            ExprOps.instantiate1LiftFast_run hok ha (by rw [hb]; rfl) h2
          have p2 : Inductives.PStep s₁ s₂ := Inductives.PStep.of_caches hok2 hx2 hbm2 hc2 hp2
          obtain ⟨p3, hr⟩ := ih xs p2.ok (hb2 eb hb) (denoteEList_ext p2.ext _ _ has) hr2
          exact ⟨p2.trans p3, by simpa [ConLeche.Frontend.instPisOpen] using hr⟩
        | _ =>
          obtain ⟨rfl, rfl⟩ := AM.pure_ok hr1
          refine ⟨Inductives.PStep.refl hok, ?_⟩
          cases hP with
          | forallE x y m =>
            obtain ⟨_, _, hc, -, -⟩ := denoteEView_forallE hdv
            exact absurd hc (by simp)
          | _ => simp [ConLeche.Frontend.instPisOpen, OptRel]

/-- con-leche: none — the last element of two lists that denote element for
element. -/
theorem denoteEList_getLast? {st : EStore} :
    ∀ {xs : List EIdx} {ys : List Expr}, Frontend.denoteEList st xs = some ys →
      OptRel (fun (h : EIdx) (e : Expr) => denoteE st h = some e) xs.getLast? ys.getLast? := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h; exact trivial
  | cons x xs ih =>
    intro ys h
    simp only [Frontend.denoteEList] at h
    cases hx : denoteE st x with
    | none => rw [hx] at h; simp at h
    | some y =>
      cases hxs : Frontend.denoteEList st xs with
      | none => rw [hx, hxs] at h; simp at h
      | some zs =>
        rw [hx, hxs] at h
        obtain rfl := Option.some.inj h
        cases xs with
        | nil =>
          simp only [Frontend.denoteEList, Option.some.injEq] at hxs
          subst hxs
          simpa [OptRel] using hx
        | cons x' xs' =>
          cases zs with
          | nil =>
            simp only [Frontend.denoteEList] at hxs
            split at hxs <;> simp at hxs
          | cons z zs' =>
            have := ih hxs
            simpa [List.getLast?_cons_cons] using this

/-! ## The two binder bodies

con-leche writes them as closures inside `projRecValue`; they are named here,
with bodies that are con-leche's letter, so that `buildBinders`' statement can
name them (the same device as round 6's `ucRuleStep`). -/

/-- con-leche: ConLeche/Frontend/ProjRec.lean:299-305 projRecValue — the motive
closure `mkMotive`, named. -/
def clMkMotive (T : ConLeche.Name) (R : Expr) (ℓ : Level) : Expr → Option Expr :=
  fun dom =>
    match ConLeche.Frontend.stripPisAll dom with
    | ([(d, m)], .sort _) =>
      if ConLeche.Frontend.headIs T d then some (.lam d (R.liftLooseBVars 1 1) m)
      else some (.lam d (.const punitName [ℓ]) m)
    | (bs, .sort _) => some (ConLeche.Frontend.mkLams bs (.const punitName [ℓ]))
    | _ => none

/-- con-leche: ConLeche/Frontend/ProjRec.lean:311-319 projRecValue — the minor
closure `mkMinor`, named. -/
def clMkMinor (ctor : ConLeche.Name) (i : Nat) (ℓ : Level) : Expr → Option Expr :=
  fun dom =>
    let (bs, cod) := ConLeche.Frontend.stripPisAll dom
    match cod.getAppArgs.getLast? with
    | some major =>
      if ConLeche.Frontend.headIs ctor major then
        if i < bs.length then
          some (ConLeche.Frontend.mkLams bs (.bvar (bs.length - 1 - i)))
        else none
      else some (ConLeche.Frontend.mkLams bs (.const punitUnitName [ℓ]))
    | none => none

/-- con-leche: none — what a `ProjBuild` carries, denoted: the owner's type
former and constructor, `R`, and the two `PUnit` constants at `ℓ`. -/
structure ProjBuildRel (st : EStore) (pb : ProjBuild) (TP ctorP : ConLeche.Name)
    (RP : Expr) (ℓ : Level) : Prop where
  T : denoteN st.ns pb.T = some TP
  ctor : denoteN st.ns pb.ctor = some ctorP
  R : denoteE st pb.R = some RP
  punitC : denoteE st pb.punitC = some (.const punitName [ℓ])
  punitUnitC : denoteE st pb.punitUnitC = some (.const punitUnitName [ℓ])

theorem ProjBuildRel.ext {st st' : EStore} (hx : Ext st st') {pb : ProjBuild}
    {TP ctorP : ConLeche.Name} {RP : Expr} {ℓ : Level}
    (h : ProjBuildRel st pb TP ctorP RP ℓ) : ProjBuildRel st' pb TP ctorP RP ℓ :=
  ⟨denoteN_ext h.T hx, denoteN_ext h.ctor hx, denote_ext h.R hx,
    denote_ext h.punitC hx, denote_ext h.punitUnitC hx⟩

/-- con-leche: ConLeche/Frontend/ProjRec.lean:299-305 projRecValue — **the
motive body**, against `clMkMotive`.  The twin tests the body's sort first and
the binder count second; con-leche's two patterns test them together, and the
two orders agree because both declines need a non-sort body. -/
theorem mkProjMotive_run {s s' : AState} (hok : StateOK s) {pb : ProjBuild}
    {TP ctorP : ConLeche.Name} {RP : Expr} {ℓ : Level}
    (hpb : ProjBuildRel s.store pb TP ctorP RP ℓ) {fuel : Nat} {dom : EIdx}
    {domP : Expr} (hd : denoteE s.store dom = some domP) {t? : Option EIdx}
    (hrun : mkProjMotive pb fuel dom s = .ok (t?, s')) :
    Inductives.PStep s s' ∧
      OptRel (fun (h : EIdx) (e : Expr) => denoteE s'.store h = some e) t?
        (clMkMotive TP RP ℓ domP) := by
  rw [mkProjMotive] at hrun
  obtain ⟨p, s₁, h1, hr1⟩ := AM.bind_ok hrun
  obtain ⟨bs, body⟩ := p
  obtain ⟨hs1, bsP, bP, hcl, hrel, hdb⟩ := stripPisAll_run hok fuel hd h1
  subst hs1
  simp only [] at hr1
  obtain ⟨v, s₂, h2, hr2⟩ := AM.bind_ok hr1
  obtain ⟨hs2, hv⟩ := view_run h2
  subst hs2
  have hdv := hdb
  rw [denoteE_view_eq hok.wf hv] at hdv
  unfold clMkMotive
  rw [hcl]
  cases v with
  | sort u =>
    obtain ⟨lv, rfl, -⟩ := denote_sort_inv hok.wf hv hdb
    simp only [] at hr2
    cases hrel with
    | nil =>
      simp only [] at hr2
      obtain ⟨t, s₅, h5, hr5⟩ := AM.bind_ok hr2
      obtain ⟨p5, ht⟩ := mkLams_pstep hok hpb.punitC rfl h5
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr5
      exact ⟨p5, ht⟩
    | @cons a b as bs' hab hrest =>
      cases hrest with
      | nil =>
        obtain ⟨d, m⟩ := a
        obtain ⟨dP, m'⟩ := b
        obtain ⟨hdd, rfl⟩ := hab
        simp only [] at hr2
        obtain ⟨c, s₃, h3, hr3⟩ := AM.bind_ok hr2
        obtain ⟨hs3, hc⟩ := headIs_run hok hpb.T hdd h3
        subst hs3
        subst hc
        simp only []
        cases hh : ConLeche.Frontend.headIs TP dP with
        | true =>
          rw [hh] at hr3
          simp only [if_true] at hr3
          obtain ⟨rl, s₄, h4, hr4⟩ := AM.bind_ok hr3
          obtain ⟨p4, hrl⟩ := Inductives.liftFast_pstep hok hpb.R h4
          obtain ⟨t, s₅, h5, hr5⟩ := AM.bind_ok hr4
          obtain ⟨p5, ht⟩ := Inductives.internLamE_run p4.ok (denote_ext hdd p4.ext) hrl h5
          obtain ⟨rfl, rfl⟩ := AM.pure_ok hr5
          exact ⟨p4.trans p5, ht⟩
        | false =>
          rw [hh] at hr3
          simp only [Bool.false_eq_true, if_false] at hr3
          obtain ⟨t, s₅, h5, hr5⟩ := AM.bind_ok hr3
          obtain ⟨p5, ht⟩ := Inductives.internLamE_run hok hdd hpb.punitC h5
          obtain ⟨rfl, rfl⟩ := AM.pure_ok hr5
          exact ⟨p5, ht⟩
      | @cons a2 b2 as2 bs2 hab2 hrest2 =>
        simp only [] at hr2
        obtain ⟨t, s₅, h5, hr5⟩ := AM.bind_ok hr2
        obtain ⟨p5, ht⟩ := mkLams_pstep hok hpb.punitC
          (denoteBL_of_listRel (ListRel.cons hab (ListRel.cons hab2 hrest2))) h5
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hr5
        exact ⟨p5, ht⟩
  | _ =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hr2
    refine ⟨Inductives.PStep.refl hok, ?_⟩
    cases bP with
    | sort l =>
      obtain ⟨_, hc, -⟩ := denoteEView_sort hdv
      exact absurd hc (by simp)
    | _ =>
      all_goals (cases bsP with
        | nil => exact trivial
        | cons a t => cases t <;> exact trivial)

/-- con-leche: ConLeche/Frontend/ProjRec.lean:311-319 projRecValue — **the
minor body**, against `clMkMinor`: the codomain's last argument decides, the
field index is read off the binder count, which the two lists share. -/
theorem mkProjMinor_run {s s' : AState} (hok : StateOK s) {pb : ProjBuild}
    {TP ctorP : ConLeche.Name} {RP : Expr} {ℓ : Level}
    (hpb : ProjBuildRel s.store pb TP ctorP RP ℓ) {fuel : Nat} {dom : EIdx}
    {domP : Expr} (hd : denoteE s.store dom = some domP) {t? : Option EIdx}
    (hrun : mkProjMinor pb fuel dom s = .ok (t?, s')) :
    Inductives.PStep s s' ∧
      OptRel (fun (h : EIdx) (e : Expr) => denoteE s'.store h = some e) t?
        (clMkMinor ctorP pb.i ℓ domP) := by
  rw [mkProjMinor] at hrun
  obtain ⟨p, s₁, h1, hr1⟩ := AM.bind_ok hrun
  obtain ⟨bs, cod⟩ := p
  obtain ⟨hs1, bsP, codP, hcl, hrel, hdc⟩ := stripPisAll_run hok fuel hd h1
  subst hs1
  simp only [] at hr1
  obtain ⟨args, s₂, h2, hr2⟩ := AM.bind_ok hr1
  obtain ⟨hs2, hargs⟩ := Inductives.getAppArgs_run hok hdc h2
  subst hs2
  have hbl := denoteBL_of_listRel hrel
  have hlen := denoteBL_length hbl
  have hlast := denoteEList_getLast? hargs
  unfold clMkMinor
  rw [hcl]
  simp only []
  cases hl : args.getLast? with
  | none =>
    rw [hl] at hr2 hlast
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hr2
    refine ⟨Inductives.PStep.refl hok, ?_⟩
    cases hlp : codP.getAppArgs.getLast? with
    | none => exact trivial
    | some _ => rw [hlp] at hlast; exact absurd hlast (by simp [OptRel])
  | some major =>
    rw [hl] at hr2 hlast
    cases hlp : codP.getAppArgs.getLast? with
    | none => rw [hlp] at hlast; exact absurd hlast (by simp [OptRel])
    | some majorP =>
      rw [hlp] at hlast
      simp only [OptRel] at hlast
      have hmaj := hlast
      simp only [] at hr2
      obtain ⟨c, s₃, h3, hr3⟩ := AM.bind_ok hr2
      obtain ⟨hs3, hc⟩ := headIs_run hok hpb.ctor hmaj h3
      subst hs3
      subst hc
      cases hh : ConLeche.Frontend.headIs ctorP majorP with
      | true =>
        rw [hh] at hr3
        simp only [if_true] at hr3
        simp only [hh, if_true]
        by_cases hi : pb.i < bs.length
        · have hi' : pb.i < bsP.length := hlen ▸ hi
          rw [if_pos hi] at hr3
          rw [if_pos hi']
          obtain ⟨b, s₄, h4, hr4⟩ := AM.bind_ok hr3
          obtain ⟨p4, hb⟩ := Inductives.internBVarE_run hok h4
          obtain ⟨t, s₅, h5, hr5⟩ := AM.bind_ok hr4
          obtain ⟨p5, ht⟩ := mkLams_pstep p4.ok hb
            (ExprOps.denoteBL_ext p4.ext _ _ hbl) h5
          obtain ⟨rfl, rfl⟩ := AM.pure_ok hr5
          refine ⟨p4.trans p5, ?_⟩
          simp only [OptRel]
          rw [ht, hlen]
        · have hi' : ¬ pb.i < bsP.length := hlen ▸ hi
          rw [if_neg hi] at hr3
          rw [if_neg hi']
          obtain ⟨rfl, rfl⟩ := AM.pure_ok hr3
          exact ⟨Inductives.PStep.refl hok, trivial⟩
      | false =>
        rw [hh] at hr3
        simp only [Bool.false_eq_true, if_false] at hr3
        simp only [hh, Bool.false_eq_true, if_false]
        obtain ⟨t, s₅, h5, hr5⟩ := AM.bind_ok hr3
        obtain ⟨p5, ht⟩ := mkLams_pstep hok hpb.punitUnitC hbl h5
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hr5
        exact ⟨p5, ht⟩

/-- con-leche: ConLeche/Frontend/ProjRec.lean:259-269 buildBinders — **the
peel**, for either binder body: `hmk` is the body's own lemma
(`mkProjMotive_run` or `mkProjMinor_run`), stated at every state where the
build's handles still denote.  Structural on the binder count. -/
theorem buildBinders_run (kind : ProjBinderKind) (pb : ProjBuild) (fuel : Nat)
    {TP ctorP : ConLeche.Name} {RP : Expr} {ℓ : Level} (mkP : Expr → Option Expr)
    (hmk : ∀ {s s' : AState} {dom : EIdx} {domP : Expr} {t? : Option EIdx},
      StateOK s → ProjBuildRel s.store pb TP ctorP RP ℓ →
      denoteE s.store dom = some domP →
      (match kind with
        | .motive => mkProjMotive pb fuel dom
        | .minor => mkProjMinor pb fuel dom) s = .ok (t?, s') →
      Inductives.PStep s s' ∧
        OptRel (fun (h : EIdx) (e : Expr) => denoteE s'.store h = some e) t? (mkP domP)) :
    ∀ (k : Nat) {s s' : AState} {h : EIdx} {hP : Expr}
      {r : Option (List EIdx × EIdx)}, StateOK s →
      ProjBuildRel s.store pb TP ctorP RP ℓ → denoteE s.store h = some hP →
      buildBinders kind pb fuel k h s = .ok (r, s') →
      Inductives.PStep s s' ∧
        OptRel (fun (p : List EIdx × EIdx) (q : List Expr × Expr) =>
            Frontend.denoteEList s'.store p.1 = some q.1 ∧
              denoteE s'.store p.2 = some q.2) r
          (ConLeche.Frontend.buildBinders mkP k hP) := by
  intro k
  induction k with
  | zero =>
    intro s s' h hP r hok _ hh hrun
    rw [buildBinders] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨Inductives.PStep.refl hok, by
      simp only [ConLeche.Frontend.buildBinders, OptRel]; exact ⟨rfl, hh⟩⟩
  | succ k ih =>
    intro s s' h hP r hok hpb hh hrun
    rw [buildBinders] at hrun
    obtain ⟨v, s₁, h1, hr1⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hv⟩ := view_run h1
    subst hs1
    have hdv := hh
    rw [denoteE_view_eq hok.wf hv] at hdv
    cases v with
    | forallE dom body m =>
      obtain ⟨dP, bP, rfl, hdd, hdb⟩ := denote_forallE_inv hok.wf hv hh
      simp only [] at hr1
      cases kind
      all_goals
        obtain ⟨t?, s₂, h2, hr2⟩ := AM.bind_ok hr1
        try simp only [] at hr2
        obtain ⟨p2, ht⟩ := hmk hok hpb hdd h2
        cases t? with
        | none =>
          obtain ⟨rfl, rfl⟩ := AM.pure_ok hr2
          refine ⟨p2, ?_⟩
          cases hm : mkP dP with
          | none => simp [ConLeche.Frontend.buildBinders, hm, OptRel]
          | some _ => rw [hm] at ht; exact absurd ht (by simp [OptRel])
        | some t =>
          cases hm : mkP dP with
          | none => rw [hm] at ht; exact absurd ht (by simp [OptRel])
          | some tP =>
            rw [hm] at ht
            simp only [OptRel] at ht
            obtain ⟨b', s₃, h3, hr3⟩ := AM.bind_ok hr2
            obtain ⟨hok3, hx3, hbm3, hc3, hp3, -, hb3⟩ :=
              ExprOps.instantiate1LiftFast_run p2.ok ht
                (by rw [denote_ext hdb p2.ext]; rfl) h3
            have p3 : Inductives.PStep s₂ s₃ := Inductives.PStep.of_caches hok3 hx3 hbm3 hc3 hp3
            obtain ⟨o, s₄, h4, hr4⟩ := AM.bind_ok hr3
            obtain ⟨p4, ho⟩ := ih p3.ok (hpb.ext (p2.ext.trans p3.ext))
              (hb3 bP (denote_ext hdb p2.ext)) h4
            have hbb : ConLeche.Frontend.buildBinders mkP (k + 1) (.forallE dP bP m) =
                (ConLeche.Frontend.buildBinders mkP k (bP.instantiate1Lift tP)).map
                  (fun p => (tP :: p.1, p.2)) := by
              simp only [ConLeche.Frontend.buildBinders, hm]
              cases hq : ConLeche.Frontend.buildBinders mkP k (bP.instantiate1Lift tP) <;> simp [hq]
            rw [hbb]
            cases o with
            | none =>
              obtain ⟨rfl, rfl⟩ := AM.pure_ok hr4
              refine ⟨p2.trans (p3.trans p4), ?_⟩
              cases hq : ConLeche.Frontend.buildBinders mkP k (bP.instantiate1Lift tP) with
              | none => exact trivial
              | some _ => rw [hq] at ho; exact absurd ho (by simp [OptRel])
            | some pr =>
              obtain ⟨ts, rest⟩ := pr
              obtain ⟨rfl, rfl⟩ := AM.pure_ok hr4
              refine ⟨p2.trans (p3.trans p4), ?_⟩
              cases hq : ConLeche.Frontend.buildBinders mkP k (bP.instantiate1Lift tP) with
              | none => rw [hq] at ho; exact absurd ho (by simp [OptRel])
              | some q =>
                rw [hq] at ho
                obtain ⟨ho1, ho2⟩ := ho
                refine ⟨?_, ho2⟩
                simp only [Frontend.denoteEList, denote_ext ht (p3.ext.trans p4.ext), ho1]
    | _ =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr1
      refine ⟨Inductives.PStep.refl hok, ?_⟩
      cases hP with
      | forallE x y m =>
        obtain ⟨_, _, hc, -, -⟩ := denoteEView_forallE hdv
        exact absurd hc (by simp)
      | _ => simp [ConLeche.Frontend.buildBinders, OptRel]

/-- con-leche: ConLeche/Frontend/ProjRec.lean:299-305 projRecValue — the
motives' peel, `buildBinders_run` at `mkProjMotive_run`.  The run comes first,
so that a caller's structure literal fixes `pb` before anything is unified
against it. -/
theorem buildMotives_run {pb : ProjBuild} {fuel k : Nat} {s s' : AState} {h : EIdx}
    {r : Option (List EIdx × EIdx)}
    (hrun : buildBinders .motive pb fuel k h s = .ok (r, s'))
    {TP ctorP : ConLeche.Name} {RP : Expr} {ℓ : Level} {hP : Expr} (hok : StateOK s)
    (hpb : ProjBuildRel s.store pb TP ctorP RP ℓ) (hh : denoteE s.store h = some hP) :
    Inductives.PStep s s' ∧
      OptRel (fun (p : List EIdx × EIdx) (q : List Expr × Expr) =>
          Frontend.denoteEList s'.store p.1 = some q.1 ∧
            denoteE s'.store p.2 = some q.2) r
        (ConLeche.Frontend.buildBinders (clMkMotive TP RP ℓ) k hP) :=
  buildBinders_run .motive pb fuel (clMkMotive TP RP ℓ)
    (fun hok' hpb' hd' h' => mkProjMotive_run hok' hpb' hd' h') k hok hpb hh hrun

/-- con-leche: ConLeche/Frontend/ProjRec.lean:311-319 projRecValue — the
minors' peel, `buildBinders_run` at `mkProjMinor_run`. -/
theorem buildMinors_run {pb : ProjBuild} {fuel k : Nat} {s s' : AState} {h : EIdx}
    {r : Option (List EIdx × EIdx)}
    (hrun : buildBinders .minor pb fuel k h s = .ok (r, s'))
    {TP ctorP : ConLeche.Name} {RP : Expr} {ℓ : Level} {hP : Expr} (hok : StateOK s)
    (hpb : ProjBuildRel s.store pb TP ctorP RP ℓ) (hh : denoteE s.store h = some hP) :
    Inductives.PStep s s' ∧
      OptRel (fun (p : List EIdx × EIdx) (q : List Expr × Expr) =>
          Frontend.denoteEList s'.store p.1 = some q.1 ∧
            denoteE s'.store p.2 = some q.2) r
        (ConLeche.Frontend.buildBinders (clMkMinor ctorP pb.i ℓ) k hP) :=
  buildBinders_run .minor pb fuel (clMkMinor ctorP pb.i ℓ)
    (fun hok' hpb' hd' h' => mkProjMinor_run hok' hpb' hd' h') k hok hpb hh hrun

/-! ## con-leche's rewrite, read as a chain of `match`es -/

/-- con-leche: ConLeche/Frontend/ProjRec.lean:291-330 projRecValue — everything
after the shape guards and the type's peel, as nested `match`es. -/
def clProjRest (o : ConLeche.Frontend.ProjRecOwner) (ℓ : Level) (R : Expr)
    (lbs : List (Expr × BinderMeta)) (i : Nat) : Option Expr :=
  let us := o.lps.map Level.param
  let params := (List.range o.nP).map fun k => Expr.bvar (o.nP - k)
  match ConLeche.Frontend.instPisOpen
      (o.recType.instantiateLevelParams o.recLps (ℓ :: us)) params with
  | none => none
  | some rty =>
    match ConLeche.Frontend.buildBinders (clMkMotive o.T R ℓ) o.numMotives rty with
    | none => none
    | some (motives, rty) =>
      match ConLeche.Frontend.buildBinders (clMkMinor o.ctor i ℓ) o.numMinors rty with
      | none => none
      | some (minors, rty) =>
        match rty with
        | .forallE majDom _ _ =>
          if ConLeche.Frontend.headIs o.T majDom then
            some (ConLeche.Frontend.mkLams lbs
              (Expr.mkAppN (.const o.recName (ℓ :: us))
                (params ++ motives ++ minors ++ [.bvar 0])))
          else none
        | _ => none

/-- con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue — the
rewrite, as the value's peel, the two guards, the type's peel and
`clProjRest`. -/
theorem clProjRecValue_eq (o : ConLeche.Frontend.ProjRecOwner) (ℓ : Level)
    (ty val : Expr) (i : Nat) :
    ConLeche.Frontend.projRecValue o ℓ ty val i =
      match val.stripLams (o.nP + 1) with
      | none => none
      | some (lbs, body) =>
        if body = .proj o.T i (.bvar 0) ∧ i < o.nF then
          match ty.stripPis (o.nP + 1) with
          | none => none
          | some (_, R) => clProjRest o ℓ R lbs i
        else none := by
  unfold ConLeche.Frontend.projRecValue clProjRest clMkMotive clMkMinor
  cases hv : val.stripLams (o.nP + 1) with
  | none => rfl
  | some p =>
    obtain ⟨lbs, body⟩ := p
    by_cases hb : body = .proj o.T i (.bvar 0)
    · subst hb
      by_cases hi : i < o.nF
      · simp only [hi, and_self, if_true]
        cases ht : ty.stripPis (o.nP + 1) with
        | none => simp [hv, ht, guard, hi]
        | some q =>
          obtain ⟨xs, R⟩ := q
          simp [hv, ht, guard, hi]
          generalize ConLeche.Frontend.instPisOpen _ _ = A
          cases A with
          | none => rfl
          | some rty =>
            simp only [Option.bind]
            generalize ConLeche.Frontend.buildBinders _ o.numMotives rty = M
            cases M with
            | none => rfl
            | some p =>
              obtain ⟨motives, rty2⟩ := p
              simp only []
              generalize ConLeche.Frontend.buildBinders _ o.numMinors rty2 = N
              cases N with
              | none => rfl
              | some q =>
                obtain ⟨minors, rty3⟩ := q
                simp only []
                cases rty3 with
                | forallE majDom b m =>
                  by_cases hh : ConLeche.Frontend.headIs o.T majDom = true
                  · simp [hh]
                  · simp [hh, failure]
                | _ => rfl
      · simp [hv, guard, hi]
    · simp [hv, guard, hb]

/-! ## The rewrite -/

/-- con-leche: none — a `some` peel denotes a `some` peel, binders and body. -/
theorem denoteBP_some_bl {st : EStore} {v : Option (List (Expr × BinderMeta) × Expr)}
    {bs : List (EIdx × BinderMeta)} {e : EIdx}
    (h : ExprOps.denoteBP st (some (bs, e)) = some v) :
    ∃ xs x, v = some (xs, x) ∧ ExprOps.denoteBL st bs = some xs ∧ denoteE st e = some x := by
  simp only [ExprOps.denoteBP] at h
  cases hb : ExprOps.denoteBL st bs with
  | none => rw [hb] at h; simp at h
  | some xs =>
    cases he : denoteE st e with
    | none => rw [hb, he] at h; simp at h
    | some x =>
      rw [hb, he] at h
      exact ⟨xs, x, (Option.some.inj h).symm, rfl, rfl⟩

/-- con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue — `o.lps.map
Level.param`, interned one parameter at a time. -/
theorem internParamLevels_run :
    ∀ (ns : List NIdx) (nsP : List ConLeche.Name) {s s' : AState} {hs : List LIdx},
      StateOK s → Frontend.denoteNList s.store.ns ns = some nsP →
      projRecValue.internParamLevels ns s = .ok (hs, s') →
      Inductives.PStep s s' ∧ denoteLList s'.store.ls hs = some (nsP.map Level.param) := by
  intro ns
  induction ns with
  | nil =>
    intro nsP s s' hs hok hn hrun
    simp only [Frontend.denoteNList, Option.some.injEq] at hn
    subst hn
    rw [projRecValue.internParamLevels] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨Inductives.PStep.refl hok, rfl⟩
  | cons n ns ih =>
    intro nsP s s' hs hok hn hrun
    simp only [Frontend.denoteNList] at hn
    cases hx : denoteN s.store.ns n with
    | none => rw [hx] at hn; simp at hn
    | some x =>
      cases hxs : Frontend.denoteNList s.store.ns ns with
      | none => rw [hx, hxs] at hn; simp at hn
      | some xs =>
        rw [hx, hxs] at hn
        obtain rfl := Option.some.inj hn
        rw [projRecValue.internParamLevels] at hrun
        obtain ⟨h, s₁, h1, hr1⟩ := AM.bind_ok hrun
        obtain ⟨p1, hd1⟩ := Inductives.internParamL_run hok hx h1
        obtain ⟨t, s₂, h2, hr2⟩ := AM.bind_ok hr1
        obtain ⟨p2, hd2⟩ := ih xs p1.ok (denoteNList_ext p1.ext.lss.ls.ns _ _ hxs) h2
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hr2
        refine ⟨p1.trans p2, ?_⟩
        simp only [denoteLList, List.map_cons, denoteL_ext hd1 p2.ext, hd2, opt2]

/-- con-leche: ConLeche/Frontend/ExprOps instLPFast — `instLPFast` in run form
at `PStep`, off `Bridge/ExprOps/Owed.lean`'s closed spec: the frame is the four-
table `CacheFrame` (`CacheFrame.ofReadbacks`), the answer the pure
`instantiateLevelParams`. -/
theorem instLPFast_pstep {fuel : Nat} {s s' : AState} {ks : List NIdx}
    {us : LsIdx} {e r : EIdx} {ksv : List ConLeche.Name} {usv : List Level}
    {eP : Expr} (hok : StateOK s) (hrc : ReadCachesOK s)
    (hks : Frontend.denoteNList s.store.ns ks = some ksv)
    (hus : denoteLs s.store.lss us = some usv) (he : denoteE s.store e = some eP)
    (hrun : instLPFast fuel ks us e s = .ok (r, s')) :
    Inductives.PStep s s' ∧ denoteE s'.store r = some (eP.instantiateLevelParams ksv usv) := by
  obtain ⟨hok', hx, hbm, hL, hLs, hN, hc, hp, -, hrel⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun
      (ExprOps.instLPFast_spec fuel s ks us e ksv usv hok hrc.readN hrc.readL hrc.readLs
        hks hus (by rw [he]; rfl))
  exact ⟨⟨hok', hx, hbm, CacheFrame.ofReadbacks hx hc hL hN hLs, hp⟩, hrel eP he⟩

/-- con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue — **the
rewrite itself**: a projection function's body as a recursor application.

**CLOSED** (task #97-P3-Frontend round 8), and two-sided: every decline of the
twin is a decline of con-leche's (`OptRel`).  The walk is composed at the
Inductives tier's `PStep` — every callee has a run-form lemma there — and
turned into the parse's `ParseStep` by `Bridge/Frontend/Scratch.lean`'s
`projRecValue_scratch`.  `ReadCachesOK s` is round 8's third ruling:
`instLPFast`'s readbacks are exact only where the three readback memos are.
Con-leche's side is read through `clProjRecValue_eq`, its two binder closures
through `clMkMotive`/`clMkMinor`. -/
theorem projRecValue_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hrc : ReadCachesOK s) {fuel : Nat}
    {o : ProjRecOwner} {oc : ConLeche.Frontend.ProjRecOwner}
    (ho : ProjRecOwnerRel s.store o oc) {l : LIdx} {u : Level}
    (hl : denoteL s.store.ls l = some u) {ty val : EIdx} {tyP valP : Expr}
    (hty : denoteE s.store ty = some tyP) (hval : denoteE s.store val = some valP)
    {i : Nat} {res : Option EIdx}
    (hrun : projRecValue fuel o l ty val i s = .ok (res, s')) :
    ParseStep s s' ∧ (∀ h, res = some h → PersE h) ∧
      OptRel (fun (h : EIdx) (e : Expr) => denoteE s'.store h = some e) res
        (ConLeche.Frontend.projRecValue oc u tyP valP i) := by
  have hsc := projRecValue_scratch hrun
  suffices H : Inductives.PStep s s' ∧
      OptRel (fun (h : EIdx) (e : Expr) => denoteE s'.store h = some e) res
        (ConLeche.Frontend.projRecValue oc u tyP valP i) by
    refine ⟨ParseStep.ofPStep H.1 hsc, ?_, H.2⟩
    intro h hres
    subst hres
    obtain ⟨e, -, hd⟩ := H.2.some_left rfl
    exact PersE_of_denote H.1.ok.wf (by rw [hsc]; exact hoff) hd
  clear hsc
  have hnw := nsWF_of_StateOK hok
  rw [clProjRecValue_eq, ← ho.nP]
  rw [ConRon.Arena.Frontend.projRecValue] at hrun
  obtain ⟨sl, s₁, h1, hr1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hbp⟩ := Inductives.stripLams_pstep hok hval h1
  subst hs1
  cases sl with
  | none =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hr1
    rw [show Expr.stripLams (o.nP + 1) valP = none from (Option.some.inj hbp).symm]
    exact ⟨Inductives.PStep.refl hok, trivial⟩
  | some p =>
    obtain ⟨lbs, body⟩ := p
    obtain ⟨lbsP, bodyP, hsl, hlbs, hbody⟩ := denoteBP_some_bl hbp
    rw [hsl]
    simp only [] at hr1 ⊢
    obtain ⟨v, s₂, h2, hr2⟩ := AM.bind_ok hr1
    obtain ⟨hs2, hv⟩ := view_run h2
    subst hs2
    have hdv := hbody
    rw [denoteE_view_eq hok.wf hv] at hdv
    cases v
    case proj tn bi sub =>
      obtain ⟨tnP, subP, rfl, htn, hsub⟩ := denote_proj_inv hok.wf hv hbody
      simp only [] at hr2
      obtain ⟨w, s₃, h3, hr3⟩ := AM.bind_ok hr2
      obtain ⟨hs3, hw⟩ := view_run h3
      subst hs3
      have hdw := hsub
      rw [denoteE_view_eq hok.wf hw] at hdw
      split at hr3
      · obtain rfl : subP = .bvar 0 := by simpa [denoteEView] using hdw.symm
        have hTeq : (tn == o.T) = true ↔ tnP = oc.T := by
          constructor
          · intro h
            have h' := beq_iff_eq.mp h
            subst h'
            exact Option.some.inj (htn.symm.trans ho.T)
          · intro h
            subst h
            exact beq_iff_eq.mpr (denoteN_inj hnw htn ho.T)
        by_cases hc : (tn != o.T || bi != i || !(i < o.nF)) = true
        · rw [if_pos hc] at hr3
          obtain ⟨rfl, rfl⟩ := AM.pure_ok hr3
          refine ⟨Inductives.PStep.refl hok, ?_⟩
          rw [if_neg]
          · trivial
          · rintro ⟨hb, hi⟩
            injection hb with hb1 hb2 _
            subst hb2
            have h1 := beq_iff_eq.mp (hTeq.mpr hb1)
            subst h1
            rw [← ho.nF] at hi
            simp [hi] at hc
        · rw [if_neg hc] at hr3
          have hc' : (tn = o.T ∧ bi = i) ∧ i < o.nF := by
            simpa [Bool.or_eq_true, bne_iff_ne, not_or] using hc
          obtain ⟨⟨hct, rfl⟩, hci⟩ := hc'
          rw [if_pos ⟨by rw [hTeq.mp (beq_iff_eq.mpr hct)], by rw [← ho.nF]; exact hci⟩]
          obtain ⟨sp, s₄, h4, hr4⟩ := AM.bind_ok hr3
          obtain ⟨hs4, hbp4⟩ := Inductives.stripPis_pstep hok hty h4
          subst hs4
          cases sp with
          | none =>
            obtain ⟨rfl, rfl⟩ := AM.pure_ok hr4
            rw [Inductives.stripPis_none hbp4]
            exact ⟨Inductives.PStep.refl hok, trivial⟩
          | some q =>
            obtain ⟨xs, r⟩ := q
            obtain ⟨xsP, RP, hsp, -, hR⟩ := denoteBP_some_bl hbp4
            rw [hsp]
            simp only [] at hr4 ⊢
            unfold clProjRest
            dsimp only
            rw [← ho.nP]
            -- the level list `ℓ :: o.lps.map param`
            obtain ⟨ups, s₅, h5, hr5⟩ := AM.bind_ok hr4
            obtain ⟨p5, hups⟩ := internParamLevels_run o.lps oc.lps hok ho.lps h5
            obtain ⟨us, s₆, h6, hr6⟩ := AM.bind_ok hr5
            obtain ⟨p6, hus⟩ := Inductives.internLsNode_run p5.ok
              (vP := u :: oc.lps.map Level.param)
              (by simp [denoteLList, denoteL_ext hl p5.ext, hups, opt2]) h6
            -- the recursor's type at that level list
            have q6 := p5.trans p6
            obtain ⟨rty0, s₇, h7, hr7⟩ := AM.bind_ok hr6
            obtain ⟨p7, hrty0⟩ := instLPFast_pstep p6.ok (hrc.pstep q6)
              (denoteNList_ext q6.ext.lss.ls.ns _ _ ho.recLps) hus
              (denote_ext ho.recType q6.ext) h7
            have q7 := q6.trans p7
            -- the parameter spine
            obtain ⟨params, s₈, h8, hr8⟩ := AM.bind_ok hr7
            obtain ⟨hok8, hx8, hbm8, -, hc8, hp8, hpar⟩ :=
              AM.of_run (P := fun t => t = s₇) rfl h8
                (ExprOps.bvarRange_spec o.nP s₇ (o.nP + 1) 0 p7.ok)
            have p8 : Inductives.PStep s₇ s₈ := Inductives.PStep.of_caches hok8 hx8 hbm8 hc8 hp8
            have hparams : Frontend.denoteEList s₈.store params =
                some ((List.range o.nP).map fun k => Expr.bvar (o.nP - k)) := by
              rw [hpar, ExprOps.bvarRangeSpec_eq_range]
              congr 1
              apply List.map_congr_left
              intro j _
              congr 1
              omega
            have q8 := q7.trans p8
            obtain ⟨ro, s₉, h9, hr9⟩ := AM.bind_ok hr8
            obtain ⟨p9, hipo⟩ := instPisOpen_run params _ p8.ok
              (denote_ext hrty0 p8.ext) hparams h9
            have q9 := q8.trans p9
            cases ro with
            | none =>
              obtain ⟨rfl, rfl⟩ := AM.pure_ok hr9
              rw [hipo.none_left rfl]
              exact ⟨q9, trivial⟩
            | some rty1 =>
              obtain ⟨rty1P, hrty1P, hrty1⟩ := hipo.some_left rfl
              rw [hrty1P]
              simp only [] at hr9 ⊢
              -- the two `PUnit` constants at `ℓ`
              obtain ⟨pH, s₁₀, h10, hr10⟩ := AM.bind_ok hr9
              obtain ⟨p10, hpH⟩ := internName_pstep p9.ok h10
              obtain ⟨pUH, s₁₁, h11, hr11⟩ := AM.bind_ok hr10
              obtain ⟨p11, hpUH⟩ := internName_pstep p10.ok h11
              obtain ⟨lsOne, s₁₂, h12, hr12⟩ := AM.bind_ok hr11
              obtain ⟨p12, hlsOne⟩ := Inductives.internLsNode_run p11.ok (vP := [u])
                (by simp [denoteLList, denoteL_ext hl (q9.trans (p10.trans p11)).ext, opt2]) h12
              obtain ⟨pC, s₁₃, h13, hr13⟩ := AM.bind_ok hr12
              obtain ⟨p13, hpC⟩ := Inductives.internConstE_run p12.ok
                (denoteN_ext hpH (p11.trans p12).ext) hlsOne h13
              obtain ⟨pUC, s₁₄, h14, hr14⟩ := AM.bind_ok hr13
              obtain ⟨p14, hpUC⟩ := Inductives.internConstE_run p13.ok
                (denoteN_ext hpUH (p12.trans p13).ext) (denoteLs_ext hlsOne p13.ext) h14
              have q14 := q9.trans (p10.trans (p11.trans (p12.trans (p13.trans p14))))
              have r14 := p10.trans (p11.trans (p12.trans (p13.trans p14)))
              rw [← ho.numMotives, ← ho.numMinors]
              -- the motives
              obtain ⟨mo, s₁₅, h15, hr15⟩ := AM.bind_ok hr14
              obtain ⟨p15, hmo⟩ := buildMotives_run h15 p14.ok
                ⟨denoteN_ext ho.T q14.ext, denoteN_ext ho.ctor q14.ext, denote_ext hR q14.ext,
                  denote_ext hpC p14.ext, hpUC⟩
                (denote_ext hrty1 r14.ext)
              cases mo with
              | none =>
                obtain ⟨rfl, rfl⟩ := AM.pure_ok hr15
                rw [hmo.none_left rfl]
                exact ⟨q14.trans p15, trivial⟩
              | some mp =>
                obtain ⟨motives, rty2⟩ := mp
                obtain ⟨mP, hmP, hmots, hrty2⟩ := hmo.some_left rfl
                obtain ⟨motivesP, rty2P⟩ := mP
                rw [hmP]
                simp only [] at hr15 ⊢
                have q15 := q14.trans p15
                have r15 := r14.trans p15
                -- the minors
                obtain ⟨mi, s₁₆, h16, hr16⟩ := AM.bind_ok hr15
                obtain ⟨p16, hmi⟩ := buildMinors_run h16 p15.ok
                  ⟨denoteN_ext ho.T q15.ext, denoteN_ext ho.ctor q15.ext, denote_ext hR q15.ext,
                    denote_ext hpC (p14.trans p15).ext, denote_ext hpUC p15.ext⟩
                  hrty2
                cases mi with
                | none =>
                  obtain ⟨rfl, rfl⟩ := AM.pure_ok hr16
                  rw [hmi.none_left rfl]
                  exact ⟨q15.trans p16, trivial⟩
                | some mq =>
                  obtain ⟨minors, rty3⟩ := mq
                  obtain ⟨nP', hnP', hmins, hrty3⟩ := hmi.some_left rfl
                  obtain ⟨minorsP, rty3P⟩ := nP'
                  rw [hnP']
                  simp only [] at hr16 ⊢
                  have q16 := q15.trans p16
                  -- the major premise
                  obtain ⟨w3, s₁₇, h17, hr17⟩ := AM.bind_ok hr16
                  obtain ⟨hs17, hw3⟩ := view_run h17
                  subst hs17
                  have hdw3 := hrty3
                  rw [denoteE_view_eq p16.ok.wf hw3] at hdw3
                  cases w3
                  case forallE majDom mb mm =>
                    obtain ⟨majP, mbP, rfl, hmaj, -⟩ := denote_forallE_inv p16.ok.wf hw3 hrty3
                    simp only [] at hr17 ⊢
                    obtain ⟨c, s₁₈, h18, hr18⟩ := AM.bind_ok hr17
                    obtain ⟨hs18, hc⟩ := headIs_run p16.ok (denoteN_ext ho.T q16.ext) hmaj h18
                    subst hs18
                    subst hc
                    cases hh : ConLeche.Frontend.headIs oc.T majP with
                    | false =>
                      simp only [hh, Bool.not_false, if_true] at hr18 ⊢
                      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr18
                      exact ⟨q16, trivial⟩
                    | true =>
                      simp only [hh, Bool.not_true, Bool.false_eq_true, if_false, if_true] at hr18 ⊢
                      obtain ⟨rc, s₁₉, h19, hr19⟩ := AM.bind_ok hr18
                      obtain ⟨p19, hrc19⟩ := Inductives.internConstE_run p16.ok
                        (denoteN_ext ho.recName q16.ext)
                        (denoteLs_ext hus (p7.trans (p8.trans (p9.trans (r15.trans p16)))).ext) h19
                      obtain ⟨b0, s₂₀, h20, hr20⟩ := AM.bind_ok hr19
                      obtain ⟨p20, hb0⟩ := Inductives.internBVarE_run p19.ok h20
                      obtain ⟨app, s₂₁, h21, hr21⟩ := AM.bind_ok hr20
                      have hargs : Frontend.denoteEList s₂₀.store
                          (params ++ motives ++ minors ++ [b0]) =
                          some ((List.range o.nP).map (fun k => Expr.bvar (o.nP - k)) ++
                            motivesP ++ minorsP ++ [.bvar 0]) := by
                        have x1 := denoteEList_ext
                          (p9.trans (r15.trans (p16.trans (p19.trans p20)))).ext _ _ hparams
                        have x2 := denoteEList_ext (p16.trans (p19.trans p20)).ext _ _ hmots
                        have x3 := denoteEList_ext (p19.trans p20).ext _ _ hmins
                        have x4 : Frontend.denoteEList s₂₀.store [b0] = some [.bvar 0] := by
                          simp [Frontend.denoteEList, hb0]
                        exact Inductives.denoteEList_append (Inductives.denoteEList_append
                          (Inductives.denoteEList_append x1 x2) x3) x4
                      obtain ⟨p21, happ⟩ := Inductives.mkAppN_run _ _ p20.ok
                        (denote_ext hrc19 p20.ext) hargs h21
                      obtain ⟨res', s₂₂, h22, hr22⟩ := AM.bind_ok hr21
                      obtain ⟨p22, hres⟩ := mkLams_pstep p21.ok happ
                        (ExprOps.denoteBL_ext (q16.trans (p19.trans (p20.trans p21))).ext _ _ hlbs) h22
                      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr22
                      exact ⟨q16.trans (p19.trans (p20.trans (p21.trans p22))), hres⟩
                  all_goals
                    obtain ⟨rfl, rfl⟩ := AM.pure_ok hr17
                    refine ⟨q16, ?_⟩
                    cases rty3P with
                    | forallE x y m =>
                      obtain ⟨_, _, hc, -, -⟩ := denoteEView_forallE hdw3
                      exact absurd hc (by simp)
                    | _ => trivial
      · rename_i hnb
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hr3
        refine ⟨Inductives.PStep.refl hok, ?_⟩
        rw [if_neg]
        · trivial
        · rintro ⟨hb, -⟩
          injection hb with _ _ hsb
          subst hsb
          exact hnb (denoteEView_bvar hdw)
    all_goals
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hr2
      refine ⟨Inductives.PStep.refl hok, ?_⟩
      rw [if_neg]
      · trivial
      · rintro ⟨hb, -⟩
        subst hb
        obtain ⟨_, _, hc, -, -⟩ := denoteEView_proj hdv
        exact absurd hc (by simp)

/-- con-leche: ConLeche/Frontend/ExportC.lean:296-297 projRewriteD — the
rewrite AT A RECORD: the state's owner table is consulted, the iota name's
level is read, and the rewrite runs or does not.

**Two-sided since round 7**: the answer is an `OptRel`, not the accept
direction alone, because `processLineCoreD` pushes the ORIGINAL value where
the twin answers `none`, and con-leche must then answer `none` too or the two
pushed records differ.  (`projIotaLevel_run` became an `OptRel` in round 4 for
the same kind of reason.)  **CLOSED** since round 8: `ParseStep` frames the
four readback tables and has no memo clause, and `ReadCachesOK s` is the
precondition `projRecValue_run` passes on to `instLPFast`.

Round 7 proved it from `projRecValue_run`: `lamBody_run`, the two views, the
`projOwners`/`projLevels` reads through `MapRel.getElem?_rel` (both
directions — a twin miss is a con-leche miss), the level-parameter guard
through `denoteNList_beq` (`denoteN_inj`), and `projIotaName_run`. -/
theorem projRewriteD_run {s s' : AState} (hok : StateOK s)
    (hoff : s.store.scratchOn = false) (hrc : ReadCachesOK s) {sd : StateD}
    {sc : ConLeche.Frontend.StateD} (hrel : StateDRel s.store sd sc)
    {cv : IConstantVal} {c : ConstantVal} (hcv : denoteCV s.store cv = some c)
    {vl : EIdx} {vlP : Expr} (hvl : denoteE s.store vl = some vlP)
    {o : Option EIdx} (hrun : projRewriteD sd cv vl s = .ok (o, s')) :
    ParseStep s s' ∧ (∀ h, o = some h → PersE h) ∧
      OptRel (fun (h : EIdx) (e : Expr) => denoteE s'.store h = some e) o
        (ConLeche.Frontend.projRewriteD sc c vlP) := by
  have hnw := nsWF_of_StateOK hok
  rw [projRewriteD] at hrun
  rw [ConLeche.Frontend.projRewriteD]
  obtain ⟨fuel, s₁, h1, hrun⟩ := AM.bind_ok hrun
  have hs1 : s₁ = s := by
    rw [storeFuel] at h1
    obtain ⟨t, s₀, hg, hp⟩ := AM.bind_ok h1
    obtain ⟨rfl, rfl⟩ := AM.get_ok hg
    exact (AM.pure_ok hp).2
  rw [hs1] at hrun
  obtain ⟨lb, s₁, h1, hrun⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hdlb⟩ := lamBody_run hok fuel hvl h1
  rw [hs1] at hrun
  obtain ⟨v, s₁, h1, hrun⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hview⟩ := view_run h1
  rw [hs1] at hrun
  generalize ConLeche.Frontend.lamBody vlP = E at hdlb ⊢
  have hdev : denoteEView s.store v = some E := by
    rw [denoteE_view_eq hok.wf hview] at hdlb; exact hdlb
  cases v
  case proj t i sub =>
    obtain ⟨tn, es, rfl, hdt, hdsub⟩ := denote_proj_inv hok.wf hview hdlb
    obtain ⟨v2, s₁, h1, hrun⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hview2⟩ := view_run h1
    rw [hs1] at hrun
    have hdev2 : denoteEView s.store v2 = some es := by
      rw [denoteE_view_eq hok.wf hview2] at hdsub; exact hdsub
    by_cases hb : v2 = .bvar 0
    rotate_left
    · -- the projection's subject is not the bound variable
      have hes : ∀ k, es = .bvar k → k ≠ 0 := by
        intro k hk hk0; subst hk; subst hk0; exact hb (denoteEView_bvar hdev2)
      split at hrun
      · exact absurd rfl hb
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      refine ⟨ParseStep.refl hok, (fun _ h => by cases h), ?_⟩
      split
      · rename_i heq
        injection heq with _ _ h3
        exact absurd rfl (hes 0 h3)
      · exact OptRel.refl_none
    subst hb
    obtain rfl : es = .bvar 0 := by simpa [denoteEView] using hdev2.symm
    simp only [] at hrun ⊢
    have hom := MapRel.getElem?_rel hnw hrel.projOwners hdt
    cases hm : sd.projOwners[t]? with
    | none =>
      rw [hm] at hrun hom
      rw [hom.none_left rfl]
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨ParseStep.refl hok, (fun _ h => by cases h), OptRel.refl_none⟩
    | some ow =>
      rw [hm] at hrun hom
      dsimp only at hrun
      obtain ⟨oc, hoc, hor⟩ := hom.some_left rfl
      rw [hoc]
      have hbeq := denoteNList_beq hnw (denoteCV_lps hcv) hor.lps
      by_cases hne : (cv.levelParams != ow.lps) = true
      · rw [if_pos hne] at hrun
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
        refine ⟨ParseStep.refl hok, (fun _ h => by cases h), ?_⟩
        have : (c.levelParams == oc.lps) = false := by
          rw [← hbeq]; simpa using hne
        have hn : ¬ c.levelParams = oc.lps := by simpa using this
        simp only [guard, hn, beq_iff_eq, if_false, Option.bind_eq_bind, Option.bind_some]
        exact trivial
      · rw [if_neg hne] at hrun
        have : (c.levelParams == oc.lps) = true := by
          rw [← hbeq]; simpa using hne
        have hq : c.levelParams = oc.lps := by simpa using this
        simp only [guard, hq, beq_self_eq_true, if_true, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def]
        obtain ⟨nm, s₂, h2, hrun⟩ := AM.bind_ok hrun
        obtain ⟨hstep2, -, hdnm⟩ := projIotaName_run hok hoff hdt h2
        have hrel2 := hrel.ext hstep2.ext
        have hlv := MapRel.getElem?_rel (nsWF_of_StateOK hstep2.ok) hrel2.projLevels hdnm
        cases hl : sd.projLevels[nm]? with
        | none =>
          rw [hl] at hrun hlv
          rw [hlv.none_left rfl]
          dsimp only at hrun
          obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
          exact ⟨hstep2, (fun _ h => by cases h), trivial⟩
        | some l =>
          rw [hl] at hrun hlv
          obtain ⟨u, hu, hlu⟩ := hlv.some_left rfl
          rw [hu]
          dsimp only at hrun ⊢
          have hoff2 : s₂.store.scratchOn = false := by rw [hstep2.scratch]; exact hoff
          obtain ⟨hstep3, hpe, hopt⟩ := projRecValue_run hstep2.ok hoff2 (hrc.step hstep2)
            (hor.ext hstep2.ext) hlu (denote_ext (denoteCV_type hcv) hstep2.ext)
            (denote_ext hvl hstep2.ext) hrun
          exact ⟨hstep2.trans hstep3, hpe, hopt⟩
  all_goals
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    refine ⟨ParseStep.refl hok, (fun _ h => by cases h), ?_⟩
    split
    · obtain ⟨_, _, hc, -, -⟩ := denoteEView_proj hdev
      exact absurd hc (by simp)
    · exact OptRel.refl_none


end ConRon.Bridge.Frontend

/-
# `ConRon.Bridge.Inductives.GenRec` — the GENERATED recursor stage
(DESIGN.md §8.2, task #105)

Theorem 1 for `Arena/Inductives/GenRec.lean` against con-leche's
`ConLeche/Kernel/Inductives/GenRec.lean`: the generator (`ClassGen`, pure
grade, its `Option`-valued twins answering TWO-SIDEDLY through `ROp`), then
the stage (`classCtorOf` … `genRecCheck`, core grade against con-leche run at
`fueledOpsM μ`, `CSpecF`), and the pass's classes (`checkBlockClasses`).

The template is upstream's cached bridge `ConLeche/Verify/Cached/GenRecC.lean`
(`genRecCheckS_simG` and the `…S_sim` lemmas above it): the same structure and
the same scoping facts (`ClassMajScoped`, `classConstOk_typeWF`,
`envWF_consBlockRecsBare`).

**The twin's deviations** (its module note), and what each costs here:

* no `ShadowOps`: the pure side is `ShadowOps.ofOps (fueledOpsM μ)`, whose
  `opsAt`/`opsRuleR` are constant and whose `flush` is `pure ()`; the twin's
  flushes are `flushCaches`, which restore `CheckOK` at whichever index the
  state reads (`ReadOK.flush`);
* `feR` is the constructors' index with the rule-less recursors pushed
  TEMPORARILY (`classFeR`) and popped (`IFEnv.popTemp`): the rule stage's
  knot calls run at `consBlockRecsBare …` (con-leche's
  `classFeR … = mkFEnv (consBlockRecsBare …)`, `consBlockRecsBareF_mkFEnv`),
  and the popped index answers exactly as the input one
  (`classFeR_popped`);
* `recOf` is `classRecOf recCls cvGs`, `ClassGen.bm` a field (the denotation
  `dClassGen` pins it to `⟨Level.zeronessOf elim⟩`), `exprGetD` /
  `targetMajorAt` the `getD … default` reads.
-/
import ConRon.Arena.Inductives.GenRec
import ConRon.Bridge.Inductives.RecCheck
import ConRon.Bridge.Inductives.ClassRead
import ConRon.Bridge.Inductives.FieldTele
import ConRon.Bridge.Inductives.Positivity

namespace ConRon.Bridge.Inductives

set_option autoImplicit false
set_option mvcgen.warning false

open ConLeche ConRon.Arena ConRon.Bridge PW

/-! ## The generator's records, denoted -/

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:60-66 ClassField — the
twin's field kind IS con-leche's, constructor for constructor. -/
def cfOf : Arena.ClassField → ConLeche.ClassField
  | .ordinary => .ordinary
  | .recursive c t => .recursive c t

theorem cfOf_injective : Function.Injective cfOf := by
  intro a b h
  cases a <;> cases b <;> simp_all [cfOf]

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:68-81 ClassCtor — a
class's constructor over handles denotes con-leche's: its constant, its two
telescopes; the counts and the kinds verbatim. -/
def dClassCtor (st : EStore) (x : Arena.ClassCtor) : Option ConLeche.ClassCtor := do
  let cv ← Frontend.denoteCV st x.cv
  let tyD ← denoteE st x.tyD
  let tyN ← denoteE st x.tyN
  pure ⟨cv, x.nF, x.kinds.map cfOf, tyD, tyN⟩

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:88-100 ClassGen — the
generator's record over handles denotes con-leche's, the twin's `bm` field
pinned to con-leche's `ClassGen.bm` (`⟨Level.zeronessOf elim⟩`, the module
note's deviation). -/
def dClassGen (st : EStore) (g : Arena.ClassGen) : Option ConLeche.ClassGen := do
  let params ← Frontend.denoteEList st g.params
  let cls ← g.cls.mapM (dMajor st)
  let fts ← Frontend.denoteEList st g.formerTys
  let slots ← g.slots.mapM (dSlot st)
  let ctors ← g.ctors.mapM (fun xs => xs.mapM (dClassCtor st))
  let elim ← denoteL st.ls g.elim
  let pre ← denoteBinders st g.pre
  if g.bm = ⟨Level.zeronessOf elim⟩ then
    pure ⟨g.nP, params, cls, fts, slots, ctors, elim, pre⟩
  else none

theorem dClassCtor_ext : DExt dClassCtor := by
  intro st st' hx x y h
  simp only [dClassCtor, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h ⊢
  obtain ⟨cv, h1, tyD, h2, tyN, h3, rfl⟩ := h
  exact ⟨cv, dExt_denoteCV hx _ _ h1, tyD, denote_ext h2 hx, tyN, denote_ext h3 hx, rfl⟩

theorem dClassCtors_ext : DExt (fun st (xss : List (List Arena.ClassCtor)) =>
    xss.mapM (fun xs => xs.mapM (dClassCtor st))) :=
  DExt.list (DExt.list dClassCtor_ext)

theorem dClassGen_ext : DExt dClassGen := by
  intro st st' hx g y h
  simp only [dClassGen, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h ⊢
  obtain ⟨params, h1, cls, h2, fts, h3, slots, h4, ctors, h5, elim, h6, pre, h7, h8⟩ := h
  exact ⟨params, denoteEList_ext hx _ _ h1, cls, dMajor_ext.list hx _ _ h2, fts,
    denoteEList_ext hx _ _ h3, slots, dSlot_ext.list hx _ _ h4, ctors,
    dClassCtors_ext hx _ _ h5, elim, denoteL_ext h6 hx, pre, denoteBinders_ext hx _ _ h7, h8⟩

/-- con-leche: none — **a denoted generator, taken apart**. -/
theorem dClassGen_inv {st : EStore} {g : Arena.ClassGen} {gP : ConLeche.ClassGen}
    (h : dClassGen st g = some gP) :
    g.nP = gP.nP ∧ Frontend.denoteEList st g.params = some gP.params ∧
      g.cls.mapM (dMajor st) = some gP.cls ∧
      Frontend.denoteEList st g.formerTys = some gP.formerTys ∧
      g.slots.mapM (dSlot st) = some gP.slots ∧
      g.ctors.mapM (fun xs => xs.mapM (dClassCtor st)) = some gP.ctors ∧
      denoteL st.ls g.elim = some gP.elim ∧ denoteBinders st g.pre = some gP.pre ∧
      g.bm = gP.bm := by
  simp only [dClassGen, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨params, h1, cls, h2, fts, h3, slots, h4, ctors, h5, elim, h6, pre, h7, h8⟩ := h
  split at h8
  · rename_i hbm
    obtain rfl := (Option.some.inj h8).symm
    exact ⟨rfl, h1, h2, h3, h4, h5, h6, h7, hbm⟩
  · exact nomatch h8

/-- con-leche: none — **a denoted class constructor, taken apart**. -/
theorem dClassCtor_inv {st : EStore} {x : Arena.ClassCtor} {xP : ConLeche.ClassCtor}
    (h : dClassCtor st x = some xP) :
    Frontend.denoteCV st x.cv = some xP.cv ∧ x.nF = xP.nF ∧ xP.kinds = x.kinds.map cfOf ∧
      denoteE st x.tyD = some xP.tyD ∧ denoteE st x.tyN = some xP.tyN := by
  simp only [dClassCtor, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨cv, h1, tyD, h2, tyN, h3, rfl⟩ := h
  exact ⟨h1, rfl, rfl, h2, h3⟩

/-- con-leche: none — the answer relation of the generator's `(opened
variables, term)` pairs. -/
abbrev RLE (v : List Expr × Expr) : EStore → List EIdx × EIdx → Prop :=
  fun st r => Frontend.denoteEList st r.1 = some v.1 ∧ denoteE st r.2 = some v.2

/-- con-leche: none — the answer relation of the generator's `(opened
variables, argument list)` pairs. -/
abbrev RLL2 (v : List Expr × List Expr) : EStore → List EIdx × List EIdx → Prop :=
  fun st r => Frontend.denoteEList st r.1 = some v.1 ∧ Frontend.denoteEList st r.2 = some v.2

/-! ## Local helpers -/

namespace GR

/-- con-leche: none — `List.mapM` of a binder-producing pure step over a
denoting handle list: the answer denotes the pure map. -/
theorem mapM_B_pstep {f : EIdx → AM (EIdx × BinderMeta)} {F : Expr → Expr × BinderMeta}
    (hf : ∀ (e : EIdx) (eP : Expr) (s₀ s' : AState) (r : EIdx × BinderMeta), StateOK s₀ →
      denoteE s₀.store e = some eP → f e s₀ = .ok (r, s') →
      PStep s₀ s' ∧ denoteE s'.store r.1 = some (F eP).1 ∧ r.2 = (F eP).2) :
    ∀ (idx : List EIdx) (idxP : List Expr) (s₀ s' : AState) (r : List (EIdx × BinderMeta)),
      StateOK s₀ → Frontend.denoteEList s₀.store idx = some idxP →
      idx.mapM f s₀ = .ok (r, s') →
      PStep s₀ s' ∧ denoteBinders s'.store r = some (idxP.map F) := by
  intro idx
  induction idx with
  | nil =>
    intro idxP s₀ s' r hok h hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h
    simp only [List.mapM_nil] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons e es ih =>
    intro idxP s₀ s' r hok h hrun
    obtain ⟨eP, esP, he, hes, rfl⟩ := Core.denoteEList_cons_inv h
    simp only [List.mapM_cons] at hrun
    obtain ⟨x, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hx1, hx2⟩ := hf e eP s₀ s1 x hok he k1
    obtain ⟨xs, s2, k2, z2⟩ := bindOk z1
    obtain ⟨p2, hxs⟩ := ih esP s1 s2 xs p1.ok (denoteEList_ext p1.ext _ _ hes) k2
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨p1.trans p2, ?_⟩
    obtain ⟨t, m⟩ := x
    simp only at hx1 hx2
    subst hx2
    simp only [denoteBinders, List.map_cons, denote_ext hx1 p2.ext, hxs]

/-- con-leche: none — `denoteBinders` of an append. -/
theorem denoteBinders_append {st : EStore} :
    ∀ {as bs : List (EIdx × BinderMeta)} {asP bsP : List (Expr × BinderMeta)},
      denoteBinders st as = some asP → denoteBinders st bs = some bsP →
      denoteBinders st (as ++ bs) = some (asP ++ bsP) := by
  intro as
  induction as with
  | nil =>
    intro bs asP bsP ha hb
    simp only [denoteBinders, Option.some.injEq] at ha
    subst ha
    exact hb
  | cons a as ih =>
    intro bs asP bsP ha hb
    obtain ⟨t, m⟩ := a
    simp only [denoteBinders] at ha
    cases h1 : denoteE st t with
    | none => rw [h1] at ha; simp at ha
    | some x =>
    cases h2 : denoteBinders st as with
    | none => rw [h1, h2] at ha; simp at ha
    | some xs =>
    rw [h1, h2] at ha
    obtain rfl := (Option.some.inj ha).symm
    simp only [List.cons_append, denoteBinders, h1, ih h2 hb]

end GR

open GR

/-! ## The generator -/

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:83-86 closeLams —
**a telescope of `λ`s closed**, innermost first: `closeTelescope_spec`'s
induction at `.lam`. -/
theorem closeLams_spec (bs : List (EIdx × BinderMeta))
    (bsP : List (Expr × BinderMeta)) (i : Nat) (body : EIdx) (bodyP : Expr) :
    PSpec (fun st => denoteBinders st bs = some bsP ∧ denoteE st body = some bodyP)
      (Arena.closeLams bs i body)
      (RE (ConLeche.closeLams bsP i bodyP)) := by
  induction bs generalizing bsP i with
  | nil =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hbs, hbody⟩ := hpre
    simp only [denoteBinders, Option.some.injEq] at hbs
    subst hbs
    simp only [Arena.closeLams] at hrun
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
    simp only [Arena.closeLams] at hrun
    obtain ⟨inner, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hin⟩ := ih rest (i + 1) s₀ s1 inner hok ⟨hrest, hbody⟩ k1
    obtain ⟨cl, s2, k2, z2⟩ := bindOk z1
    obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := AM.of_run (P := fun t => t = s1) rfl k2
      (ExprOps.abstract1Fast_spec fvarBSpec Arena.coreWalkFuel s1 inner i 0 p1.ok
        (by rw [hin]; rfl))
    have p2 : PStep s1 s2 := PStep.of_caches h1 h2 h3 h4 h5
    obtain ⟨p3, hr⟩ := internLamE_run p2.ok (denote_ext hdom (p1.ext.trans p2.ext))
      (h7 _ hin) z2
    exact ⟨p1.trans (p2.trans p3), hr⟩

/-- con-leche: none — `xs.getD i default` on a term list: the twin's
`exprGetD` reads the interned `.bvar 0`, con-leche's `default`. -/
theorem exprGetD_spec (xs : List EIdx) (xsP : List Expr) (i : Nat) :
    PSpec (fun st => Frontend.denoteEList st xs = some xsP) (Arena.exprGetD xs i)
      (RE (xsP.getD i default)) := by
  intro s₀ s' r hok hxs hrun
  simp only [Arena.exprGetD] at hrun
  obtain ⟨hj1, hj2⟩ := PW.denoteEList_getElem? hxs i
  rw [List.getD_eq_getElem?_getD]
  cases hc : xs[i]? with
  | none =>
    rw [hc] at hrun
    rw [hj1.mp hc, Option.getD_none]
    exact internBVarE_run hok hrun
  | some x =>
    rw [hc] at hrun
    obtain ⟨y, hy, hd⟩ := hj2 x hc
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    rw [hy, Option.getD_some]
    exact ⟨PStep.refl hok, hd⟩

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:102-104 classBinder —
an opened variable's binder at the default datum. -/
theorem classBinder_run {x : EIdx} {xP : Expr} {s₀ s' : AState} {r : EIdx × BinderMeta}
    (hok : StateOK s₀) (hx : denoteE s₀.store x = some xP)
    (hrun : Arena.classBinder x s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ denoteE s'.store r.1 = some (ConLeche.classBinder xP).1 ∧
      r.2 = (ConLeche.classBinder xP).2 := by
  simp only [Arena.classBinder] at hrun
  obtain ⟨t, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨rfl, ht⟩ := fvarTypeD_run hok hx k1
  obtain ⟨rfl, rfl⟩ := pureOk z1
  exact ⟨PStep.refl hok, ht, rfl⟩

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:106-111 ClassGen.bm —
**the generated binders' datum**, read once from the elimination level
through the cached readback (`PSpecL`). -/
theorem classGenBm_spec (elim : LIdx) (elimP : Level) :
    PSpecL (fun st => denoteL st.ls elim = some elimP) (Arena.classGenBm elim)
      (RV (⟨Level.zeronessOf elimP⟩ : BinderMeta)) := by
  intro s₀ s' r hok hrl he hrun
  simp only [Arena.classGenBm] at hrun
  obtain ⟨u, s1, k1, z1⟩ := bindOk hrun
  have p1 := readLevelM_pstep hok k1
  have hu := readLevelM_denote_L hrl (PStep.refl hok) k1
  rw [he] at hu
  obtain rfl := (Option.some.inj hu).symm
  obtain ⟨rfl, rfl⟩ := pureOk z1
  exact ⟨p1, rfl⟩

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:113-114 ClassGen.binder
— a generated binder, at the field `bm` (con-leche's `ClassGen.bm`). -/
theorem ClassGen.binder_run {g : Arena.ClassGen} {gP : ConLeche.ClassGen} (hbm : g.bm = gP.bm)
    (x : EIdx) (xP : Expr) (s₀ s' : AState) (r : EIdx × BinderMeta)
    (hok : StateOK s₀) (hx : denoteE s₀.store x = some xP)
    (hrun : g.binder x s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ denoteE s'.store r.1 = some (gP.binder xP).1 ∧ r.2 = (gP.binder xP).2 := by
  simp only [Arena.ClassGen.binder] at hrun
  obtain ⟨t, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨rfl, ht⟩ := fvarTypeD_run hok hx k1
  obtain ⟨rfl, rfl⟩ := pureOk z1
  exact ⟨PStep.refl hok, ht, hbm⟩

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:116-117 ClassGen.slotVar
— the prefix variable of a slot, at `Sort 0` (the `zeroLevel` pin:
`PSpecP`). -/
theorem ClassGen.slotVar_spec (g : Arena.ClassGen) (gP : ConLeche.ClassGen) (sl : Nat) :
    PSpecP (fun st => dClassGen st g = some gP) (g.slotVar sl) (RE (gP.slotVar sl)) := by
  intro s₀ s' r hok hp hg hrun
  have hnP := (dClassGen_inv hg).1
  simp only [Arena.ClassGen.slotVar] at hrun
  obtain ⟨u, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨rfl, hu⟩ := PW.zeroLevel_run hp k1
  obtain ⟨z, s2, k2, z2⟩ := bindOk z1
  obtain ⟨p2, hz⟩ := internSortE_run hok hu k2
  obtain ⟨p3, hr⟩ := internFVarE_run p2.ok hz z2
  refine ⟨p2.trans p3, ?_⟩
  simp only [ConLeche.ClassGen.slotVar, RE, hr, hnP]

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:119-121 ClassGen.motVar
— a class's motive variable: the motive slot the twin's slot list names is
con-leche's (`motiveSlot_eq`). -/
theorem ClassGen.motVar_spec (g : Arena.ClassGen) (gP : ConLeche.ClassGen) (c : Nat) :
    PSpecP (fun st => dClassGen st g = some gP) (g.motVar c) (RE (gP.motVar c)) := by
  intro s₀ s' r hok hp hg hrun
  have hsl := (dClassGen_inv hg).2.2.2.2.1
  simp only [Arena.ClassGen.motVar] at hrun
  rw [motiveSlot_eq [] hsl c] at hrun
  exact ClassGen.slotVar_spec g gP _ s₀ s' r hok hp hg hrun

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:123-128 ClassGen.major —
**a class's index telescope and its major domain**, `none` exactly when
con-leche's is (the former's parameter telescope or the index telescope
too short). -/
theorem ClassGen.major_spec (g : Arena.ClassGen) (gP : ConLeche.ClassGen) (c d : Nat) :
    PSpecP (fun st => dClassGen st g = some gP) (g.major c d) (ROp RLE (gP.major c d)) := by
  intro s₀ s' r hok hp hg hrun
  obtain ⟨-, -, hcls, hfts, -⟩ := dClassGen_inv hg
  simp only [Arena.ClassGen.major] at hrun
  obtain ⟨ci, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, hci⟩ := targetMajorAt_spec g.cls gP.cls c s₀ s1 ci hok hp hcls k1
  obtain ⟨fty, s2, k2, z2⟩ := bindOk z1
  obtain ⟨p2, hfty⟩ := exprGetD_spec g.formerTys gP.formerTys c s1 s2 fty p1.ok
    (denoteEList_ext p1.ext _ _ hfts) k2
  obtain ⟨hind, hlvls, hds, -, hnIdx, -⟩ := dMajor_inv (dMajor_ext p2.ext _ _ hci)
  obtain ⟨o, s3, k3, z3⟩ := bindOk z2
  obtain ⟨p3, ho⟩ := instPisWith_spec ci.ds _ fty _ s2 s3 o p2.ok ⟨hds, hfty⟩ k3
  simp only [ConLeche.ClassGen.major]
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk z3
    refine ⟨p1.trans (p2.trans p3), ?_⟩
    have hn : ConLeche.instPisWith (gP.cls.getD c default).ds
        (gP.formerTys.getD c default) = none := ho
    show _ = none
    rw [hn]; rfl
  | some ty =>
    obtain ⟨tyP, hty, htyd⟩ := ho
    have p13 := p1.trans (p2.trans p3)
    dsimp only at z3
    obtain ⟨o2, s4, k4, z4⟩ := bindOk z3
    obtain ⟨p4, ho2⟩ := CR.openPisAtFvarsF_run p3.ok htyd k4
    simp only [hty, Option.bind_eq_bind, Option.bind_some]
    rw [hnIdx] at ho2
    cases o2 with
    | none =>
      obtain ⟨rfl, rfl⟩ := pureOk z4
      refine ⟨p13.trans p4, ?_⟩
      have hn := (Option.some.inj ho2).symm
      show _ = none
      rw [hn]; rfl
    | some q =>
      obtain ⟨ifs, body⟩ := q
      obtain ⟨ifsP, bodyP, hq, hifs, -⟩ := CR.denoteOpen_some_inv ho2
      dsimp only at z4
      obtain ⟨hd, s5, k5, z5⟩ := bindOk z4
      have p14 := p13.trans p4
      have p24 := p3.trans p4
      obtain ⟨p5, hhd⟩ := internConstE_run p4.ok (denoteN_ext hind p24.ext)
        (denoteLs_ext hlvls p24.ext) k5
      obtain ⟨maj, s6, k6, z6⟩ := bindOk z5
      have p25 := p24.trans p5
      obtain ⟨p6, hmaj⟩ := mkAppN_run _ _ p5.ok hhd
        (denoteEList_append (denoteEList_ext p25.ext _ _ hds)
          (denoteEList_ext (p5.ext) _ _ hifs)) k6
      obtain ⟨rfl, rfl⟩ := pureOk z6
      refine ⟨(p14.trans p5).trans p6, ?_⟩
      rw [hq]
      exact ⟨_, rfl, denoteEList_ext p6.ext _ _ (denoteEList_ext p5.ext _ _ hifs), hmaj⟩

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:130-133 ClassGen.motiveTy
— **a class's motive type** `∀ ı⃗ (t : I D⃗ ı⃗), Sort ℓ` at depth `d`. -/
theorem ClassGen.motiveTy_spec (g : Arena.ClassGen) (gP : ConLeche.ClassGen) (c d : Nat) :
    PSpecP (fun st => dClassGen st g = some gP) (g.motiveTy c d) (ROp RE (gP.motiveTy c d)) := by
  intro s₀ s' r hok hp hg hrun
  simp only [Arena.ClassGen.motiveTy] at hrun
  obtain ⟨o, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, ho⟩ := ClassGen.major_spec g gP c d s₀ s1 o hok hp hg k1
  simp only [ConLeche.ClassGen.motiveTy]
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk z1
    refine ⟨p1, ?_⟩
    have hn : gP.major c d = none := ho
    show _ = none
    rw [hn]; rfl
  | some q =>
    obtain ⟨ifs, maj⟩ := q
    obtain ⟨⟨ifsP, majP⟩, hq, hifs, hmaj⟩ := ho
    simp only [hq, Option.bind_eq_bind, Option.bind_some]
    dsimp only at z1
    have helim := (dClassGen_inv (dClassGen_ext p1.ext _ _ hg)).2.2.2.2.2.2.1
    obtain ⟨srt, s2, k2, z2⟩ := bindOk z1
    obtain ⟨p2, hsrt⟩ := internSortE_run p1.ok helim k2
    obtain ⟨body, s3, k3, z3⟩ := bindOk z2
    obtain ⟨p3, hbody⟩ := internForallEE_run p2.ok (denote_ext hmaj p2.ext) hsrt k3
    obtain ⟨bs, s4, k4, z4⟩ := bindOk z3
    obtain ⟨p4, hbs⟩ := mapM_B_pstep (F := ConLeche.classBinder)
      (fun e eP s₀ s' r hok he hrun => classBinder_run hok he hrun) ifs ifsP s3 s4 bs p3.ok
      (denoteEList_ext (p2.ext.trans p3.ext) _ _ hifs) k4
    obtain ⟨cl, s5, k5, z5⟩ := bindOk z4
    obtain ⟨p5, hcl⟩ := closeTelescope_spec bs _ d body _ s4 s5 cl p4.ok
      ⟨hbs, denote_ext hbody p4.ext⟩ k5
    obtain ⟨rfl, rfl⟩ := pureOk z5
    exact ⟨p1.trans (p2.trans (p3.trans (p4.trans p5))), _, rfl, hcl⟩

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:135-141 ClassGen.ihParts
— **an inductive hypothesis's telescope and index arguments**: the landing
class's parameter count read as con-leche's `(g.cls.getD t default).nPc`
(the default class has none). -/
theorem ClassGen.ihParts_spec (g : Arena.ClassGen) (gP : ConLeche.ClassGen) (t tele : Nat)
    (w : EIdx) (wP : Expr) (d : Nat) :
    PSpec (fun st => dClassGen st g = some gP ∧ denoteE st w = some wP)
      (g.ihParts t tele w d) (ROp RLL2 (gP.ihParts t tele wP d)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hg, hw⟩ := hpre
  have hcls := (dClassGen_inv hg).2.2.1
  simp only [Arena.ClassGen.ihParts] at hrun
  obtain ⟨o, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, ho⟩ := CR.openPisAtFvarsF_run hok hw k1
  simp only [ConLeche.ClassGen.ihParts]
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk z1
    refine ⟨p1, ?_⟩
    have hn := (Option.some.inj ho).symm
    show _ = none
    rw [hn]; rfl
  | some q =>
    obtain ⟨xs, leaf⟩ := q
    obtain ⟨xsP, leafP, hq, hxs, hleaf⟩ := CR.denoteOpen_some_inv ho
    simp only [hq, Option.bind_eq_bind, Option.bind_some]
    dsimp only at z1
    obtain ⟨args, s2, k2, z2⟩ := bindOk z1
    obtain ⟨rfl, hargs⟩ := getAppArgs_run p1.ok hleaf k2
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨p1, _, rfl, hxs, ?_⟩
    have hj := mapM_option_getElem? (st := s₀.store) hcls t
    show Frontend.denoteEList _ (List.drop _ args) = some (List.drop _ _)
    rw [List.getD_eq_getElem?_getD]
    split
    · rename_i m hc
      rw [hc] at hj
      obtain ⟨mP, hmP, hd⟩ := hj
      rw [hmP, Option.getD_some, ← (dMajor_inv hd).2.2.2.1]
      exact denoteEList_drop hargs _
    · rename_i hc
      rw [hc] at hj
      have : gP.cls[t]? = none := hj
      rw [this]
      exact denoteEList_drop hargs _

/-! ### The minor premise -/


namespace GR

/-- con-leche: none — a list mapped with its running index, in `Option`: the
list recursion con-leche's `(List.range l.length).mapM fun j => f (l.getD j
default) j` is (`mapM_range_getD`), and the shape the twin's `let rec` walks
have. -/
def mapIdxFromP {α β : Type} (f : α → Nat → Option β) : Nat → List α → Option (List β)
  | _, [] => some []
  | k, a :: as => do
    let b ← f a k
    let bs ← mapIdxFromP f (k + 1) as
    pure (b :: bs)

theorem mapM_range'_getD {α β : Type} [Inhabited α] (f : α → Nat → Option β) :
    ∀ (l L : List α) (k : Nat), L.drop k = l →
      (List.range' k l.length).mapM (fun j => f (L.getD j default) j) = mapIdxFromP f k l
  | [], _, _, _ => rfl
  | a :: as, L, k, h => by
    have hk : L.getD k default = a := by
      have h0 : (L.drop k)[0]? = some a := by rw [h]; rfl
      rw [List.getElem?_drop, Nat.add_zero] at h0
      rw [List.getD_eq_getElem?_getD, h0]; rfl
    have h' : L.drop (k + 1) = as := by
      have := congrArg (List.drop 1) h
      simpa [List.drop_drop, Nat.add_comm] using this
    simp only [List.length_cons, List.range'_succ, List.mapM_cons, mapIdxFromP, hk,
      mapM_range'_getD f as L (k + 1) h']

/-- con-leche: none — `(List.range L.length).mapM` at `L`'s entries is
`mapIdxFromP` from `0`. -/
theorem mapM_range_getD {α β : Type} [Inhabited α] (f : α → Nat → Option β) (L : List α)
    (g : Nat → Option β) (hg : ∀ j, g j = f (L.getD j default) j) :
    (List.range L.length).mapM g = mapIdxFromP f 0 L := by
  rw [show g = fun j => f (L.getD j default) j from funext hg, List.range_eq_range']
  exact mapM_range'_getD f L L 0 rfl

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:151-154 ClassGen.minorTy
(`recs`) — the recursive fields' `(field, class, telescope)` triples: the
twin's over its kinds are con-leche's over the mapped kinds. -/
theorem recs_eq (nF : Nat) (ks : List Arena.ClassField) :
    ((List.range nF).filterMap fun i =>
      match ks.getD i .ordinary with
      | .recursive t tele => some (i, t, tele)
      | .ordinary => none) =
    ((List.range nF).filterMap fun i =>
      match (ks.map cfOf).getD i .ordinary with
      | .recursive t tele => some (i, t, tele)
      | .ordinary => none) := by
  congr 1
  funext i
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ks[i]? with
  | none => rfl
  | some k => cases k <;> rfl

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:155-160 ClassGen.minorTy
(one inductive hypothesis) — the body of con-leche's `mapM`, at the entry `q`
and the running index `l`. -/
def minorIhP (gP : ConLeche.ClassGen) (x : ConLeche.ClassCtor) (d : Nat) (fvsP wsP : List Expr)
    (q : Nat × Nat × Nat) (l : Nat) : Option (Expr × BinderMeta) :=
  match q with
  | (i, t, tele) => do
    let e := d + x.nF + l
    let (xs, idx) ← gP.ihParts t tele (wsP.getD i default) e
    pure (closeTelescope (xs.map gP.binder) e
      (Expr.mkAppN (gP.motVar t) (idx ++ [Expr.mkAppN (fvsP.getD i default) xs])), gP.bm)

end GR

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:155-160 ClassGen.minorTy
(the `mapM`) — **the minor premise's inductive hypotheses**, the twin's
`let rec` against con-leche's indexed `mapM` (`mapIdxFromP`). -/
theorem ClassGen.minorTy_ihsGo_spec (g : Arena.ClassGen) (gP : ConLeche.ClassGen)
    (x : Arena.ClassCtor) (xP : ConLeche.ClassCtor) (hnF : x.nF = xP.nF) (d : Nat)
    (fvs ws : List EIdx) (fvsP wsP : List Expr) :
    ∀ (rest : List (Nat × Nat × Nat)) (l : Nat),
    PSpecP (fun st => dClassGen st g = some gP ∧ Frontend.denoteEList st fvs = some fvsP ∧
        Frontend.denoteEList st ws = some wsP)
      (Arena.ClassGen.minorTy.ihsGo g x d fvs ws l rest)
      (ROp RB (mapIdxFromP (minorIhP gP xP d fvsP wsP) l rest)) := by
  intro rest
  induction rest with
  | nil =>
    intro l s₀ s' r hok hp _ hrun
    simp only [Arena.ClassGen.minorTy.ihsGo] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, [], rfl, rfl⟩
  | cons q rest ih =>
    intro l s₀ s' r hok hp hpre hrun
    obtain ⟨i, t, tele⟩ := q
    obtain ⟨hg, hfvs, hws⟩ := hpre
    have hbm := (dClassGen_inv hg).2.2.2.2.2.2.2.2
    simp only [Arena.ClassGen.minorTy.ihsGo] at hrun
    obtain ⟨w, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hw⟩ := exprGetD_spec ws wsP i s₀ s1 w hok hws k1
    obtain ⟨o, s2, k2, z2⟩ := bindOk z1
    obtain ⟨p2, ho⟩ := ClassGen.ihParts_spec g gP t tele w _ (d + x.nF + l) s1 s2 o p1.ok
      ⟨dClassGen_ext p1.ext _ _ hg, hw⟩ k2
    have p12 := p1.trans p2
    simp only [mapIdxFromP, minorIhP, ← hnF]
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := pureOk z2
      refine ⟨p12, ?_⟩
      have hn : gP.ihParts t tele (wsP.getD i default) (d + x.nF + l) = none := ho
      show _ = none
      simp only [hn, Option.bind_eq_bind, Option.bind_none]
    | some pr =>
      obtain ⟨xs, idx⟩ := pr
      obtain ⟨⟨xsP, idxP⟩, hq, hxs, hidx⟩ := ho
      simp only [hq, Option.bind_eq_bind, Option.bind_some]
      dsimp only at z2
      obtain ⟨f, s3, k3, z3⟩ := bindOk z2
      obtain ⟨p3, hf⟩ := exprGetD_spec fvs fvsP i s2 s3 f p2.ok
        (denoteEList_ext p12.ext _ _ hfvs) k3
      obtain ⟨fx, s4, k4, z4⟩ := bindOk z3
      obtain ⟨p4, hfx⟩ := mkAppN_run _ _ p3.ok hf (denoteEList_ext p3.ext _ _ hxs) k4
      have p14 := p12.trans (p3.trans p4)
      obtain ⟨mt, s5, k5, z5⟩ := bindOk z4
      obtain ⟨p5, hmt⟩ := ClassGen.motVar_spec g gP t s4 s5 mt p4.ok
        (PinsOK.ofPStep hp p14) (dClassGen_ext p14.ext _ _ hg) k5
      obtain ⟨body, s6, k6, z6⟩ := bindOk z5
      obtain ⟨p6, hbody⟩ := mkAppN_run _ _ p5.ok hmt
        (denoteEList_append (denoteEList_ext ((p3.trans p4).trans p5).ext _ _ hidx)
          (show Frontend.denoteEList _ [fx] = some [(fvsP.getD i default).mkAppN xsP] by
            simp only [Frontend.denoteEList, denote_ext hfx p5.ext])) k6
      obtain ⟨bs, s7, k7, z7⟩ := bindOk z6
      have p16 := (p14.trans p5).trans p6
      obtain ⟨p7, hbs⟩ := mapM_B_pstep (F := gP.binder) (ClassGen.binder_run hbm) xs xsP s6 s7
        bs p6.ok (denoteEList_ext ((p3.trans p4).trans (p5.trans p6)).ext _ _ hxs) k7
      obtain ⟨ihE, s8, k8, z8⟩ := bindOk z7
      obtain ⟨p8, hihE⟩ := closeTelescope_spec bs _ _ body _ s7 s8 ihE p7.ok
        ⟨hbs, denote_ext hbody p7.ext⟩ k8
      have p18 := (p16.trans p7).trans p8
      obtain ⟨o2, s9, k9, z9⟩ := bindOk z8
      obtain ⟨p9, ho2⟩ := ih (l + 1) s8 s9 o2 p8.ok (PinsOK.ofPStep hp p18)
        ⟨dClassGen_ext p18.ext _ _ hg, denoteEList_ext p18.ext _ _ hfvs,
          denoteEList_ext p18.ext _ _ hws⟩ k9
      cases o2 with
      | none =>
        obtain ⟨rfl, rfl⟩ := pureOk z9
        refine ⟨p18.trans p9, ?_⟩
        have hn : mapIdxFromP (minorIhP gP xP d fvsP wsP) (l + 1) rest = none := ho2
        show _ = none
        simp only [hn, Option.bind_none]; rfl
      | some ihs =>
        obtain ⟨ihsP, hihs, hihsd⟩ := ho2
        obtain ⟨rfl, rfl⟩ := pureOk z9
        refine ⟨p18.trans p9, (ConLeche.closeTelescope (xsP.map gP.binder) (d + x.nF + l)
          ((gP.motVar t).mkAppN (idxP ++ [(fvsP.getD i default).mkAppN xsP])), gP.bm) :: ihsP,
          ?_, ?_⟩
        · simp only [hihs, Option.bind_some, Option.pure_def]
        · show denoteBinders _ ((ihE, g.bm) :: ihs) = _
          simp only [denoteBinders, denote_ext hihE p9.ext, hihsd, hbm, hnF]

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:143-163 ClassGen.minorTy —
**constructor `x`'s minor premise type** at depth `d`, of class `c`: its
declared fields, one inductive hypothesis per recursive field, over the
motive at the declared result indices and the constructor applied; `none`
exactly when con-leche's is. -/
theorem ClassGen.minorTy_spec (g : Arena.ClassGen) (gP : ConLeche.ClassGen) (c : Nat)
    (x : Arena.ClassCtor) (xP : ConLeche.ClassCtor) (d : Nat) :
    PSpecP (fun st => dClassGen st g = some gP ∧ dClassCtor st x = some xP)
      (g.minorTy c x d) (ROp RE (gP.minorTy c xP d)) := by
  intro s₀ s' r hok hp hpre hrun
  obtain ⟨hg, hx⟩ := hpre
  obtain ⟨hnP, -, hcls, -, -, -, -, -, hbm⟩ := dClassGen_inv hg
  obtain ⟨hcv, hnF, hkinds, htyD, htyN⟩ := dClassCtor_inv hx
  simp only [Arena.ClassGen.minorTy] at hrun
  obtain ⟨ci, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, hci⟩ := targetMajorAt_spec g.cls gP.cls c s₀ s1 ci hok hp hcls k1
  obtain ⟨o, s2, k2, z2⟩ := bindOk z1
  obtain ⟨p2, ho⟩ := CR.openPisAtFvarsF_run p1.ok (denote_ext htyD p1.ext) k2
  have p12 := p1.trans p2
  simp only [ConLeche.ClassGen.minorTy]
  rw [hnF] at ho
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨p12, ?_⟩
    have hn := (Option.some.inj ho).symm
    show _ = none
    simp only [hn, Option.bind_eq_bind, Option.bind_none]
  | some q =>
    obtain ⟨fvs, res⟩ := q
    obtain ⟨fvsP, resP, hq, hfvs, hres⟩ := CR.denoteOpen_some_inv ho
    simp only [hq, Option.bind_eq_bind, Option.bind_some]
    dsimp only at z2
    obtain ⟨o2, s3, k3, z3⟩ := bindOk z2
    obtain ⟨p3, ho2⟩ := targetPiDomsWith_spec fvs fvsP x.tyN xP.tyN s2 s3 o2 p2.ok
      ⟨hfvs, denote_ext htyN p12.ext⟩ k3
    cases o2 with
    | none =>
      obtain ⟨rfl, rfl⟩ := pureOk z3
      refine ⟨p12.trans p3, ?_⟩
      have hn : ConLeche.targetPiDomsWith fvsP xP.tyN = none := ho2
      show _ = none
      simp only [hn, Option.bind_none]
    | some ws =>
      obtain ⟨wsP, hws, hwsd⟩ := ho2
      simp only [hws, Option.bind_some]
      dsimp only at z3
      have p13 := p12.trans p3
      obtain ⟨o3, s4, k4, z4⟩ := bindOk z3
      generalize hT : List.filterMap _ (List.range x.nF) = T at k4
      obtain ⟨p4, ho3⟩ := ClassGen.minorTy_ihsGo_spec g gP x xP hnF d fvs ws fvsP wsP _ 0
        s3 s4 o3 p3.ok (PinsOK.ofPStep hp p13)
        ⟨dClassGen_ext p13.ext _ _ hg, denoteEList_ext p3.ext _ _ hfvs, hwsd⟩ k4
      rw [GR.mapM_range_getD (GR.minorIhP gP xP d fvsP wsP) _ _ ?hg]
      case hg => intro j; rfl
      generalize hU : List.filterMap _ (List.range xP.nF) = U
      have hUT : U = T := by
        rw [← hU, ← hT, hkinds, ← hnF]; exact (recs_eq _ _).symm
      subst hUT
      cases o3 with
      | none =>
        obtain ⟨rfl, rfl⟩ := pureOk z4
        refine ⟨p13.trans p4, ?_⟩
        have hn := ho3
        simp only [ROp] at hn
        show _ = none
        simp only [hn, Option.bind_none]
      | some ihs =>
        obtain ⟨ihsP, hihs, hihsd⟩ := ho3
        simp only [hihs, Option.bind_some]
        dsimp only at z4
        have p14 := p13.trans p4
        obtain ⟨ra, s5, k5, z5⟩ := bindOk z4
        obtain ⟨rfl, hra⟩ := getAppArgs_run p4.ok (denote_ext hres (p3.ext.trans p4.ext)) k5
        obtain ⟨hind, hlvls, hds, hnPc, -⟩ := dMajor_inv (dMajor_ext (p2.ext.trans (p3.ext.trans p4.ext)) _ _ hci)
        obtain ⟨cc, s6, k6, z6⟩ := bindOk z5
        obtain ⟨p6, hcc⟩ := internConstE_run p4.ok
          (ConRon.Bridge.denoteCV_name (dExt_denoteCV p14.ext _ _ hcv)) hlvls k6
        obtain ⟨capp, s7, k7, z7⟩ := bindOk z6
        obtain ⟨p7, hcapp⟩ := mkAppN_run _ _ p6.ok hcc
          (denoteEList_append (denoteEList_ext p6.ext _ _ hds)
            (denoteEList_ext (p3.ext.trans (p4.ext.trans p6.ext)) _ _ hfvs)) k7
        have p17 := (p14.trans p6).trans p7
        obtain ⟨mc, s8, k8, z8⟩ := bindOk z7
        obtain ⟨p8, hmc⟩ := ClassGen.motVar_spec g gP c s7 s8 mc p7.ok
          (PinsOK.ofPStep hp p17) (dClassGen_ext p17.ext _ _ hg) k8
        obtain ⟨concl, s9, k9, z9⟩ := bindOk z8
        have hra8 : Frontend.denoteEList s8.store (ra.drop ci.nPc) =
            some (resP.getAppArgs.drop (gP.cls.getD c default).nPc) := by
          rw [← hnPc]
          exact denoteEList_drop (denoteEList_ext (p6.ext.trans (p7.ext.trans p8.ext)) _ _ hra) _
        have hcapp8 : Frontend.denoteEList s8.store [capp] =
            some [Expr.mkAppN (.const xP.cv.name (gP.cls.getD c default).lvls)
              ((gP.cls.getD c default).ds ++ fvsP)] := by
          simp only [Frontend.denoteEList, denote_ext hcapp p8.ext]
        obtain ⟨p9, hconcl⟩ := mkAppN_run _ _ p8.ok hmc (denoteEList_append hra8 hcapp8) k9
        have p19 := (p17.trans p8).trans p9
        obtain ⟨fbs, s10, k10, z10⟩ := bindOk z9
        obtain ⟨p10, hfbs⟩ := mapM_B_pstep (F := gP.binder) (ClassGen.binder_run hbm) fvs fvsP
          s9 s10 fbs p9.ok (denoteEList_ext (p3.ext.trans (p4.ext.trans (p6.ext.trans
            (p7.ext.trans (p8.ext.trans p9.ext))))) _ _ hfvs) k10
        obtain ⟨rr, s11, k11, z11⟩ := bindOk z10
        obtain ⟨p11, hrr⟩ := closeTelescope_spec _ _ d concl _ s10 s11 rr p10.ok
          ⟨GR.denoteBinders_append hfbs
            (denoteBinders_ext (p6.ext.trans (p7.ext.trans (p8.ext.trans (p9.ext.trans
              p10.ext)))) _ _ hihsd), denote_ext hconcl p10.ext⟩ k11
        obtain ⟨rfl, rfl⟩ := pureOk z11
        exact ⟨(p19.trans p10).trans p11, _, rfl, hrr⟩

/-! ### The prefix -/

namespace GR

/-- con-leche: none — con-leche's motive test on a slot. -/
def isMotiveP : ConLeche.ClassSlot → Bool
  | .motive _ => true
  | _ => false

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:168-177 ClassGen.prefixBinders
(one slot) — the body of con-leche's `mapM` over the slots, at slot `sl` and
position `s`. -/
def slotP (gP : ConLeche.ClassGen) (sl : ConLeche.ClassSlot) (s : Nat) :
    Option (Expr × BinderMeta) :=
  match sl with
  | .motive _ => do
    let t ← gP.motiveTy ((List.range s).filter fun s' => isMotiveP (gP.slots.getD s' default)).length
      (gP.nP + s)
    pure (t, gP.bm)
  | .minor c C _ => do
    let x ← (gP.ctors.getD c []).find? (·.cv.name == C)
    let t ← gP.minorTy c x (gP.nP + s)
    pure (t, gP.bm)

/-- con-leche: none — **the motives before a slot**: the twin counts them in the
slot list's prefix, con-leche over the positions below it (the same number
at any position inside the list). -/
theorem motive_count {st : EStore} {slots : List Arena.ClassSlot}
    {slotsP : List ConLeche.ClassSlot} (h : slots.mapM (dSlot st) = some slotsP)
    (pA : Arena.ClassSlot → Bool) (hA : ∀ a aP, dSlot st a = some aP → pA a = isMotiveP aP) :
    ∀ s, s ≤ slots.length → ((slots.take s).filter pA).length =
      ((List.range s).filter fun s' => isMotiveP (slotsP.getD s' default)).length := by
  intro s
  induction s with
  | zero => intro _; simp
  | succ s ih =>
    intro hs
    rw [List.take_add_one, List.range_succ, List.filter_append, List.filter_append,
      List.length_append, List.length_append, ih (by omega)]
    congr 1
    have hj := mapM_option_getElem? (st := st) h s
    have hlt : s < slots.length := by omega
    rw [List.getElem?_eq_getElem hlt] at hj ⊢
    obtain ⟨aP, haP, hd⟩ := hj
    simp only [Option.toList_some, List.filter_cons, List.filter_nil, hA _ _ hd,
      List.getD_eq_getElem?_getD, haP, Option.getD_some]
    split <;> rfl

/-- con-leche: none — `Option`'s `mapM` on a cons, inverted. -/
theorem mapM_cons_inv {α β : Type} {f : α → Option β} {x : α} {xs : List α} {ys : List β}
    (h : (x :: xs).mapM f = some ys) :
    ∃ y ys', ys = y :: ys' ∧ f x = some y ∧ xs.mapM f = some ys' := by
  simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
  cases hx : f x with
  | none => rw [hx] at h; simp at h
  | some y =>
  cases hxs : xs.mapM f with
  | none => rw [hx, hxs] at h; simp at h
  | some ys' =>
  rw [hx, hxs] at h
  simp only [Option.bind_some, Option.some.injEq] at h
  exact ⟨y, ys', h.symm, rfl, rfl⟩

/-- con-leche: none — `find?` by constructor name over a denoting constructor
list: the twin's handle test is con-leche's name test. -/
theorem find_ctor {st : EStore} (hwf : StoreWF st) {C : NIdx} {CP : ConLeche.Name}
    (hC : denoteN st.ns C = some CP) :
    ∀ (xs : List Arena.ClassCtor) (xsP : List ConLeche.ClassCtor),
      xs.mapM (dClassCtor st) = some xsP →
      ROp (fun xP st x => dClassCtor st x = some xP) (xsP.find? (·.cv.name == CP)) st
        (xs.find? (·.cv.name == C))
  | [], xsP, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | x :: xs, xsP, h => by
    obtain ⟨xP, xsP', rfl, hx, hxs⟩ := mapM_cons_inv h
    have hn := ConRon.Bridge.denoteCV_name (dClassCtor_inv hx).1
    have hb := beq_handle_eq hwf hn hC
    simp only [List.find?_cons]
    rw [hb]
    cases (xP.cv.name == CP)
    · exact find_ctor hwf hC xs xsP' hxs
    · exact ⟨xP, rfl, hx⟩

end GR

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:165-178 ClassGen.prefixBinders
(the slots) — **every slot's binder**, the twin's `let rec` from position `s`
against con-leche's indexed `mapM` (`mapIdxFromP`), on the slot list's
suffix. -/
theorem ClassGen.prefixBinders_slotsGo_spec (g : Arena.ClassGen) (gP : ConLeche.ClassGen) :
    ∀ (rest : List Arena.ClassSlot) (s : Nat), g.slots.drop s = rest →
    PSpecP (fun st => dClassGen st g = some gP)
      (Arena.ClassGen.prefixBinders.slotsGo g s rest)
      (ROp RB (mapIdxFromP (GR.slotP gP) s (gP.slots.drop s))) := by
  intro rest
  induction rest with
  | nil =>
    intro s hdrop s₀ s' r hok hp hg hrun
    simp only [Arena.ClassGen.prefixBinders.slotsGo] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    have hsl := (dClassGen_inv hg).2.2.2.2.1
    have hlen := mapM_option_length hsl
    have : gP.slots.drop s = [] := by
      rw [List.drop_eq_nil_iff] at hdrop ⊢; omega
    rw [this]
    exact ⟨PStep.refl hok, [], rfl, rfl⟩
  | cons sl sls ih =>
    intro s hdrop s₀ s' r hok hp hg hrun
    obtain ⟨hnP, -, -, -, hsl, hctors, -, -, hbm⟩ := dClassGen_inv hg
    have hlen := mapM_option_length hsl
    have hslen : s < g.slots.length := by
      have : (g.slots.drop s).length = sls.length + 1 := by rw [hdrop]; rfl
      rw [List.length_drop] at this; omega
    have hj := mapM_option_getElem? (st := s₀.store) hsl s
    have hsl0 : g.slots[s]? = some sl := by
      have h0 : (g.slots.drop s)[0]? = some sl := by rw [hdrop]; rfl
      rwa [List.getElem?_drop, Nat.add_zero] at h0
    rw [hsl0] at hj
    obtain ⟨slP, hslP, hdsl⟩ := hj
    have hdropP : gP.slots.drop s = slP :: gP.slots.drop (s + 1) := by
      have hlt : s < gP.slots.length := by omega
      rw [List.drop_eq_getElem_cons hlt]
      rw [List.getElem?_eq_getElem hlt] at hslP
      rw [Option.some.inj hslP]
    have hdrop' : g.slots.drop (s + 1) = sls := by
      have := congrArg (List.drop 1) hdrop
      simpa [List.drop_drop, Nat.add_comm] using this
    rw [hdropP]
    simp only [mapIdxFromP]
    simp only [Arena.ClassGen.prefixBinders.slotsGo] at hrun
    cases sl
    case' motive k =>
      simp only [dSlot, Option.map_eq_some_iff] at hdsl
      obtain ⟨kP, -, rfl⟩ := hdsl
      dsimp only at hrun
      obtain ⟨tyo, s1, k1, z1⟩ := bindOk hrun
      obtain ⟨p1, ho⟩ := ClassGen.motiveTy_spec g gP _ _ s₀ s1 tyo hok hp hg k1
      rw [GR.motive_count hsl _ (fun a aP had => by
        cases a with
        | motive _ =>
          simp only [dSlot, Option.map_eq_some_iff] at had
          obtain ⟨_, _, rfl⟩ := had; rfl
        | minor _ _ _ =>
          simp only [dSlot, Option.map_eq_some_iff] at had
          obtain ⟨_, _, rfl⟩ := had; rfl) s (by omega), hnP] at ho
      obtain ⟨X, hXo, hslot⟩ : ∃ X : Option Expr, ROp RE X s1.store tyo ∧
          GR.slotP gP (.motive kP) s = (X >>= fun t => pure (t, gP.bm)) := ⟨_, ho, rfl⟩
      clear k1 ho
      rw [hslot]
    case' minor c C ihs =>
      simp only [dSlot, Option.map_eq_some_iff] at hdsl
      obtain ⟨CP, hCP, rfl⟩ := hdsl
      have hcj := mapM_option_getElem? (st := s₀.store) hctors c
      have hcs : (g.ctors.getD c []).mapM (dClassCtor s₀.store) =
          some (gP.ctors.getD c []) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        cases hc : g.ctors[c]? with
        | none =>
          rw [hc] at hcj
          have : gP.ctors[c]? = none := hcj
          rw [this]; rfl
        | some xs =>
          rw [hc] at hcj
          obtain ⟨xsP, hxsP, hd⟩ := hcj
          rw [hxsP]; exact hd
      have hf := GR.find_ctor hok.wf hCP _ _ hcs
      dsimp only at hrun
      generalize hfx : List.find? _ (g.ctors.getD c []) = fx at hrun
      rw [hfx] at hf
      cases fx
      case' none =>
        have hn : (gP.ctors.getD c []).find? (·.cv.name == CP) = none := hf
        dsimp only at hrun
        obtain ⟨tyo, s1, k1, z1⟩ := bindOk hrun
        obtain ⟨htyo, hs1⟩ := pureOk k1
        have p1 : PStep s₀ s1 := by rw [hs1]; exact PStep.refl hok
        have hXo0 : ROp RE (none : Option Expr) s1.store tyo := by rw [htyo]; rfl
        have hslot0 : GR.slotP gP (.minor c CP ihs) s =
            ((none : Option Expr) >>= fun t => pure (t, gP.bm)) := by
          simp only [GR.slotP, hn, Option.bind_eq_bind, Option.bind_none]
        obtain ⟨X, hXo, hslot⟩ : ∃ X : Option Expr, ROp RE X s1.store tyo ∧
            GR.slotP gP (.minor c CP ihs) s = (X >>= fun t => pure (t, gP.bm)) :=
          ⟨none, hXo0, hslot0⟩
        clear k1 htyo hs1
        rw [hslot]
      case' some x =>
        obtain ⟨xP, hxP, hdx⟩ := hf
        dsimp only at hrun
        obtain ⟨tyo, s1, k1, z1⟩ := bindOk hrun
        obtain ⟨p1, ho⟩ := ClassGen.minorTy_spec g gP c x xP (g.nP + s) s₀ s1 tyo hok hp
          ⟨hg, hdx⟩ k1
        rw [hnP] at ho
        obtain ⟨X, hXo, hslot⟩ : ∃ X : Option Expr, ROp RE X s1.store tyo ∧
            GR.slotP gP (.minor c CP ihs) s = (X >>= fun t => pure (t, gP.bm)) :=
          ⟨_, ho, by simp only [GR.slotP, hxP, Option.bind_eq_bind, Option.bind_some]⟩
        clear k1 ho
        rw [hslot]
    all_goals
      cases tyo with
      | none =>
        obtain ⟨rfl, rfl⟩ := pureOk z1
        refine ⟨p1, ?_⟩
        have hn : X = none := hXo
        show _ = none
        simp only [hn, Option.bind_eq_bind, Option.bind_none]
      | some ty =>
        obtain ⟨tP, htP, hty⟩ := hXo
        simp only [htP, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        dsimp only at z1
        obtain ⟨o2, s2, k2, z2⟩ := bindOk z1
        obtain ⟨p2, ho2⟩ := ih (s + 1) hdrop' s1 s2 o2 p1.ok (PinsOK.ofPStep hp p1)
          (dClassGen_ext p1.ext _ _ hg) k2
        cases o2 with
        | none =>
          obtain ⟨rfl, rfl⟩ := pureOk z2
          refine ⟨p1.trans p2, ?_⟩
          have hn : mapIdxFromP (GR.slotP gP) (s + 1) (gP.slots.drop (s + 1)) = none := ho2
          show _ = none
          simp only [hn, Option.bind_none]
        | some rs =>
          obtain ⟨rsP, hrs, hrsd⟩ := ho2
          obtain ⟨rfl, rfl⟩ := pureOk z2
          refine ⟨p1.trans p2, (tP, gP.bm) :: rsP, ?_, ?_⟩
          · simp only [hrs, Option.bind_some]
          · show denoteBinders _ ((ty, g.bm) :: rs) = _
            simp only [denoteBinders, denote_ext hty p2.ext, hrsd, hbm]

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:165-178 ClassGen.prefixBinders
— **the generated prefix**: the parameters, then every slot in the stream's
order; `none` exactly when con-leche's is. -/
theorem ClassGen.prefixBinders_spec (g : Arena.ClassGen) (gP : ConLeche.ClassGen) :
    PSpecP (fun st => dClassGen st g = some gP) g.prefixBinders
      (ROp RB gP.prefixBinders) := by
  intro s₀ s' r hok hp hg hrun
  obtain ⟨-, hpar, -, -, -, -, -, -, hbm⟩ := dClassGen_inv hg
  simp only [Arena.ClassGen.prefixBinders] at hrun
  obtain ⟨pbs, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, hpbs⟩ := mapM_B_pstep (F := gP.binder) (ClassGen.binder_run hbm) g.params
    gP.params s₀ s1 pbs hok hpar k1
  obtain ⟨o, s2, k2, z2⟩ := bindOk z1
  obtain ⟨p2, ho⟩ := ClassGen.prefixBinders_slotsGo_spec g gP g.slots 0 rfl s1 s2 o p1.ok
    (PinsOK.ofPStep hp p1) (dClassGen_ext p1.ext _ _ hg) k2
  simp only [ConLeche.ClassGen.prefixBinders]
  rw [GR.mapM_range_getD (GR.slotP gP) _ _ ?hg]
  case hg => intro j; rfl
  rw [List.drop_zero] at ho
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨p1.trans p2, ?_⟩
    have hn : mapIdxFromP (GR.slotP gP) 0 gP.slots = none := ho
    show _ = none
    simp only [hn, Option.bind_eq_bind, Option.bind_none]
  | some sbs =>
    obtain ⟨sbsP, hsbs, hsbsd⟩ := ho
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨p1.trans p2, _, ?_, GR.denoteBinders_append (denoteBinders_ext p2.ext _ _ hpbs) hsbsd⟩
    simp only [hsbs, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-! ### The recursor type and the rule -/

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:180-187 classGenRecTy —
**the generated recursor type** at class `c`: the prefix, the class's indices
and its major, over the motive applied to them. -/
theorem classGenRecTy_spec (g : Arena.ClassGen) (gP : ConLeche.ClassGen) (c : Nat) :
    PSpecP (fun st => dClassGen st g = some gP) (Arena.classGenRecTy g c)
      (ROp RE (ConLeche.classGenRecTy gP c)) := by
  intro s₀ s' r hok hp hg hrun
  obtain ⟨-, -, -, -, -, -, -, hpre, hbm⟩ := dClassGen_inv hg
  have hlen : g.pre.length = gP.pre.length := denoteBinders_length hpre
  simp only [Arena.classGenRecTy] at hrun
  obtain ⟨o, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, ho⟩ := ClassGen.major_spec g gP c _ s₀ s1 o hok hp hg k1
  rw [hlen] at ho
  simp only [ConLeche.classGenRecTy]
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk z1
    refine ⟨p1, ?_⟩
    have hn : gP.major c gP.pre.length = none := ho
    show _ = none
    simp only [hn, Option.bind_eq_bind, Option.bind_none]
  | some q =>
    obtain ⟨ifs, maj⟩ := q
    obtain ⟨⟨ifsP, majP⟩, hq, hifs, hmaj⟩ := ho
    simp only [hq, Option.bind_eq_bind, Option.bind_some]
    dsimp only at z1
    have hil : ifs.length = ifsP.length := PW.denoteEList_length hifs
    obtain ⟨t, s2, k2, z2⟩ := bindOk z1
    obtain ⟨p2, ht⟩ := internE_run p1.ok (viewOK_fvar (by rw [hmaj]; rfl)) k2
    have ht' : denoteE s2.store t = some (.fvar (gP.pre.length + ifsP.length) majP) := by
      rw [ht]; simp only [denoteEView, denote_ext hmaj p2.ext, Option.map_some, hlen, hil]
    obtain ⟨ibs, s3, k3, z3⟩ := bindOk z2
    obtain ⟨p3, hibs⟩ := mapM_B_pstep (F := gP.binder) (ClassGen.binder_run hbm) ifs ifsP
      s2 s3 ibs p2.ok (denoteEList_ext p2.ext _ _ hifs) k3
    have p13 := p1.trans (p2.trans p3)
    obtain ⟨mv, s4, k4, z4⟩ := bindOk z3
    obtain ⟨p4, hmv⟩ := ClassGen.motVar_spec g gP c s3 s4 mv p3.ok (PinsOK.ofPStep hp p13)
      (dClassGen_ext p13.ext _ _ hg) k4
    obtain ⟨body, s5, k5, z5⟩ := bindOk z4
    have hargs : Frontend.denoteEList s4.store (ifs ++ [t]) =
        some (ifsP ++ [.fvar (gP.pre.length + ifsP.length) majP]) :=
      denoteEList_append (denoteEList_ext ((p2.trans p3).trans p4).ext _ _ hifs)
        (by simp only [Frontend.denoteEList, denote_ext ht' (p3.ext.trans p4.ext)])
    obtain ⟨p5, hbody⟩ := mkAppN_run _ _ p4.ok hmv hargs k5
    obtain ⟨rr, s6, k6, z6⟩ := bindOk z5
    have hbs : denoteBinders s5.store (g.pre ++ ibs ++ [(maj, g.bm)]) =
        some (gP.pre ++ ifsP.map gP.binder ++ [(majP, gP.bm)]) := by
      refine GR.denoteBinders_append (GR.denoteBinders_append
        (denoteBinders_ext (p13.trans (p4.trans p5)).ext _ _ hpre)
        (denoteBinders_ext (p4.trans p5).ext _ _ hibs)) ?_
      simp only [denoteBinders, denote_ext hmaj (p2.trans (p3.trans (p4.trans p5))).ext, hbm]
    obtain ⟨p6, hrr⟩ := closeTelescope_spec _ _ 0 body _ s5 s6 rr p5.ok ⟨hbs, hbody⟩ k6
    obtain ⟨rfl, rfl⟩ := pureOk z6
    exact ⟨(p13.trans (p4.trans p5)).trans p6, _, rfl, hrr⟩

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:538-543 classRecOf — **the
recursor a call at class `t` names**: the same position of the same search,
its name denoting con-leche's. -/
theorem classRecOf_rel {st : EStore} (recCls : List Nat) {cvGs : List IConstantVal}
    {cvGsP : List ConstantVal} (h : cvGs.mapM (Frontend.denoteCV st) = some cvGsP) (t : Nat) :
    ROp (fun n st r => denoteN st.ns r = some n) (ConLeche.classRecOf recCls cvGsP t) st
      (Arena.classRecOf recCls cvGs t) := by
  have hlen : cvGs.length = cvGsP.length := (mapM_option_length h).symm
  simp only [Arena.classRecOf, ConLeche.classRecOf, hlen]
  cases hf : (List.range cvGsP.length).find? (fun r => recCls.getD r 0 == t) with
  | none => rfl
  | some j =>
    have hj : j < cvGsP.length := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    refine ⟨(cvGsP.getD j default).name, rfl, ?_⟩
    have hj' : j < cvGs.length := by omega
    have hjj := mapM_option_getElem? (st := st) h j
    rw [List.getElem?_eq_getElem hj'] at hjj
    obtain ⟨cP, hcP, hd⟩ := hjj
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
    rw [hcP, Option.getD_some]
    exact ConRon.Bridge.denoteCV_name hd

namespace GR

/-- con-leche: none — `List.filterMapM` in `Option`, as a list recursion. -/
def filterMapOP {α β : Type} (f : α → Option (Option β)) : List α → Option (List β)
  | [] => some []
  | a :: l => do
    match ← f a with
    | none => filterMapOP f l
    | some b => do
      let bs ← filterMapOP f l
      pure (b :: bs)

theorem filterMapM_eq {α β : Type} (f : α → Option (Option β)) :
    ∀ (l : List α), l.filterMapM f = filterMapOP f l
  | [] => rfl
  | a :: l => by
    rw [List.filterMapM_cons, filterMapM_eq f l]
    simp only [filterMapOP]
    cases f a with
    | none => rfl
    | some b =>
      cases b with
      | none => rfl
      | some b => rfl

/-- con-leche: none — `mapM` at the pure frame for a step that reads a pin. -/
theorem mapM_pstepP {α β γ : Type} (f : α → AM β) (g : α → γ)
    (R : EStore → β → γ → Prop) (P : α → EStore → Prop)
    (hRx : ∀ {st st' : EStore} {b : β} {c : γ}, Ext st st' → R st b c → R st' b c)
    (hPx : ∀ {a : α} {st st' : EStore}, Ext st st' → P a st → P a st')
    (hf : ∀ (a : α) (s₀ s' : AState) (b : β), StateOK s₀ → PinsOK s₀ → P a s₀.store →
      f a s₀ = .ok (b, s') → PStep s₀ s' ∧ R s'.store b (g a)) :
    ∀ (xs : List α) (s₀ s' : AState) (bs : List β), StateOK s₀ → PinsOK s₀ →
      (∀ a ∈ xs, P a s₀.store) → xs.mapM f s₀ = .ok (bs, s') →
      PStep s₀ s' ∧ ListRel R s'.store bs (xs.map g) := by
  intro xs
  induction xs with
  | nil =>
    intro s₀ s' bs hok _ _ hrun
    simp only [List.mapM_nil] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, trivial⟩
  | cons a as ih =>
    intro s₀ s' bs hok hp hP hrun
    simp only [List.mapM_cons] at hrun
    obtain ⟨b, s1, k1, hz1⟩ := bindOk hrun
    obtain ⟨p1, hb⟩ := hf a s₀ s1 b hok hp (hP a (by simp)) k1
    obtain ⟨cs, s2, k2, hz2⟩ := bindOk hz1
    obtain ⟨p2, hcs⟩ := ih s1 s2 cs p1.ok (PinsOK.ofPStep hp p1)
      (fun x hx => hPx p1.ext (hP x (by simp [hx]))) k2
    obtain ⟨rfl, rfl⟩ := pureOk hz2
    exact ⟨p1.trans p2, hRx p2.ext hb, hcs⟩

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:197-198 classGenRule (`find?`) —
the minor premise slot of a constructor: the twin's search over handles finds
the position con-leche's finds. -/
theorem find_hit {st : EStore} (hwf : StoreWF st) (c : Nat) {C : NIdx} {CP : ConLeche.Name}
    (hC : denoteN st.ns C = some CP) :
    ∀ (k : Nat) (sls : List Arena.ClassSlot) (slsP : List ConLeche.ClassSlot),
      sls.mapM (dSlot st) = some slsP →
      ((List.range' k sls.length).zip sls |>.find? fun (_, sl) =>
          match sl with
          | .minor c' C' _ => c' == c && C' == C
          | .motive _ => false).map (·.1) =
      ((List.range' k slsP.length).zip slsP |>.find? fun (_, sl) =>
          match sl with
          | .minor c' C' _ => c' == c && C' == CP
          | _ => false).map (·.1)
  | _, [], slsP, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | k, sl :: sls, slsP, h => by
    obtain ⟨slP, slsP', rfl, hd, hds⟩ := mapM_cons_inv h
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.find?_cons]
    have ih := find_hit hwf c hC (k + 1) sls slsP' hds
    cases sl with
    | motive key =>
      simp only [dSlot, Option.map_eq_some_iff] at hd
      obtain ⟨_, _, rfl⟩ := hd
      exact ih
    | minor c' C' ihs =>
      simp only [dSlot, Option.map_eq_some_iff] at hd
      obtain ⟨CP', hCP', rfl⟩ := hd
      dsimp only
      rw [beq_handle_eq hwf hCP' hC]
      split
      · rfl
      · exact ih

end GR

namespace GR

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:203-211 classGenRule (one
field) — the body of con-leche's `filterMapM` over the fields: nothing at an
ordinary field, the recursive call's `λ` at a recursive one. -/
def callP (gP : ConLeche.ClassGen) (recCls : List Nat) (cvGsP : List ConstantVal)
    (rlvlsP : List Level) (xP : ConLeche.ClassCtor) (fvsP wsP pvarsP : List Expr) (rP : Nat)
    (i : Nat) : Option (Option Expr) :=
  match xP.kinds.getD i .ordinary with
  | .ordinary => some none
  | .recursive t tele => do
    let f := fvsP.getD i default
    let (xs, idx) ← gP.ihParts t tele (wsP.getD i default) (rP + xP.nF)
    let r ← ConLeche.classRecOf recCls cvGsP t
    pure (some (ConLeche.closeLams (xs.map gP.binder) (rP + xP.nF)
      (Expr.mkAppN (.const r rlvlsP) (pvarsP ++ idx ++ [Expr.mkAppN f xs]))))

end GR

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:203-211 classGenRule (the
calls) — **every recursive field's call**, the twin's `let rec` over the
fields `i ..< i + n` against con-leche's `filterMapM` (`filterMapOP`). -/
theorem classGenRule_callsGo_spec (g : Arena.ClassGen) (gP : ConLeche.ClassGen)
    (recCls : List Nat) (cvGs : List IConstantVal) (cvGsP : List ConstantVal)
    (rlvls : LsIdx) (rlvlsP : List Level) (x : Arena.ClassCtor) (xP : ConLeche.ClassCtor)
    (hnF : x.nF = xP.nF) (hkinds : xP.kinds = x.kinds.map cfOf) (rP : Nat)
    (fvs ws pvars : List EIdx) (fvsP wsP pvarsP : List Expr) :
    ∀ (n i : Nat),
    PSpecP (fun st => dClassGen st g = some gP ∧ Frontend.denoteEList st fvs = some fvsP ∧
        Frontend.denoteEList st ws = some wsP ∧ Frontend.denoteEList st pvars = some pvarsP ∧
        cvGs.mapM (Frontend.denoteCV st) = some cvGsP ∧ denoteLs st.lss rlvls = some rlvlsP)
      (Arena.classGenRule.callsGo g recCls cvGs rlvls x rP fvs ws pvars n i)
      (ROp REL (GR.filterMapOP (GR.callP gP recCls cvGsP rlvlsP xP fvsP wsP pvarsP rP)
        (List.range' i n))) := by
  intro n
  induction n with
  | zero =>
    intro i s₀ s' r hok hp _ hrun
    simp only [Arena.classGenRule.callsGo] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, [], rfl, rfl⟩
  | succ n ih =>
    intro i s₀ s' r hok hp hpre hrun
    obtain ⟨hg, hfvs, hws, hpv, hcv, hrl⟩ := hpre
    have hbm := (dClassGen_inv hg).2.2.2.2.2.2.2.2
    simp only [Arena.classGenRule.callsGo] at hrun
    simp only [List.range'_succ, GR.filterMapOP]
    have hk : xP.kinds.getD i .ordinary = cfOf (x.kinds.getD i .ordinary) := by
      rw [hkinds, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases x.kinds[i]? <;> rfl
    simp only [GR.callP, hk]
    generalize x.kinds.getD i .ordinary = kd at hrun
    cases kd with
    | ordinary =>
      simp only [cfOf]
      exact ih (i + 1) s₀ s' r hok hp ⟨hg, hfvs, hws, hpv, hcv, hrl⟩ hrun
    | recursive t tele =>
      simp only [cfOf]
      dsimp only at hrun
      obtain ⟨w, s1, k1, z1⟩ := bindOk hrun
      obtain ⟨p1, hw⟩ := exprGetD_spec ws wsP i s₀ s1 w hok hws k1
      obtain ⟨o, s2, k2, z2⟩ := bindOk z1
      obtain ⟨p2, ho⟩ := ClassGen.ihParts_spec g gP t tele w _ (rP + x.nF) s1 s2 o p1.ok
        ⟨dClassGen_ext p1.ext _ _ hg, hw⟩ k2
      rw [hnF] at ho
      have p12 := p1.trans p2
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := pureOk z2
        refine ⟨p12, ?_⟩
        have hn : gP.ihParts t tele (wsP.getD i default) (rP + xP.nF) = none := ho
        show _ = none
        simp only [hn, Option.bind_eq_bind, Option.bind_none]
      | some pr =>
        obtain ⟨xs, idx⟩ := pr
        obtain ⟨⟨xsP, idxP⟩, hq, hxs, hidx⟩ := ho
        simp only [hq, Option.bind_eq_bind, Option.bind_some]
        dsimp only at z2
        have hro := classRecOf_rel (st := s2.store) recCls
          (dExt_denoteCV.list p12.ext _ _ hcv) t
        revert z2
        cases hr : Arena.classRecOf recCls cvGs t with
        | none =>
          intro z2
          rw [hr] at hro
          have hn : ConLeche.classRecOf recCls cvGsP t = none := hro
          obtain ⟨rfl, rfl⟩ := pureOk z2
          refine ⟨p12, ?_⟩
          show _ = none
          simp only [hn, Option.bind_none]
        | some rn =>
          intro z2
          rw [hr] at hro
          obtain ⟨rnP, hrn, hrnd⟩ := hro
          simp only [hrn, Option.bind_some]
          dsimp only at z2
          obtain ⟨f, s3, k3, z3⟩ := bindOk z2
          obtain ⟨p3, hf⟩ := exprGetD_spec fvs fvsP i s2 s3 f p2.ok
            (denoteEList_ext p12.ext _ _ hfvs) k3
          obtain ⟨fx, s4, k4, z4⟩ := bindOk z3
          obtain ⟨p4, hfx⟩ := mkAppN_run _ _ p3.ok hf (denoteEList_ext p3.ext _ _ hxs) k4
          have p14 := p12.trans (p3.trans p4)
          obtain ⟨rc, s5, k5, z5⟩ := bindOk z4
          obtain ⟨p5, hrc⟩ := internConstE_run p4.ok
            (denoteN_ext hrnd (p3.ext.trans p4.ext)) (denoteLs_ext hrl p14.ext) k5
          obtain ⟨app, s6, k6, z6⟩ := bindOk z5
          have hfx5 : Frontend.denoteEList s5.store [fx] = some [(fvsP.getD i default).mkAppN xsP] := by
            simp only [Frontend.denoteEList, denote_ext hfx p5.ext]
          have hargs := denoteEList_append (denoteEList_append
            (denoteEList_ext (p14.trans p5).ext _ _ hpv)
            (denoteEList_ext ((p3.trans p4).trans p5).ext _ _ hidx)) hfx5
          obtain ⟨p6, happ⟩ := mkAppN_run _ _ p5.ok hrc hargs k6
          obtain ⟨bs, s7, k7, z7⟩ := bindOk z6
          obtain ⟨p7, hbs⟩ := mapM_B_pstep (F := gP.binder) (ClassGen.binder_run hbm) xs xsP s6 s7
            bs p6.ok (denoteEList_ext ((p3.trans p4).trans (p5.trans p6)).ext _ _ hxs) k7
          obtain ⟨call, s8, k8, z8⟩ := bindOk z7
          obtain ⟨p8, hcall⟩ := closeLams_spec bs _ _ app _ s7 s8 call p7.ok
            ⟨hbs, denote_ext happ p7.ext⟩ k8
          rw [hnF] at hcall
          have p18 := ((p14.trans p5).trans (p6.trans p7)).trans p8
          obtain ⟨o2, s9, k9, z9⟩ := bindOk z8
          obtain ⟨p9, ho2⟩ := ih (i + 1) s8 s9 o2 p8.ok (PinsOK.ofPStep hp p18)
            ⟨dClassGen_ext p18.ext _ _ hg, denoteEList_ext p18.ext _ _ hfvs,
              denoteEList_ext p18.ext _ _ hws, denoteEList_ext p18.ext _ _ hpv,
              dExt_denoteCV.list p18.ext _ _ hcv, denoteLs_ext hrl p18.ext⟩ k9
          simp only [Option.pure_def, Option.bind_some]
          cases o2 with
          | none =>
            obtain ⟨rfl, rfl⟩ := pureOk z9
            refine ⟨p18.trans p9, ?_⟩
            have hn := ho2
            simp only [ROp] at hn
            show _ = none
            simp only [hn, Option.bind_none]
          | some rs =>
            obtain ⟨rsP, hrs, hrsd⟩ := ho2
            obtain ⟨rfl, rfl⟩ := pureOk z9
            refine ⟨p18.trans p9, (ConLeche.closeLams (xsP.map gP.binder) (rP + xP.nF)
              ((Expr.const rnP rlvlsP).mkAppN (pvarsP ++ idxP ++
                [(fvsP.getD i default).mkAppN xsP]))) :: rsP, ?_, ?_⟩
            · simp only [hrs, Option.bind_some]
            · show Frontend.denoteEList _ (call :: rs) = _
              simp only [Frontend.denoteEList, denote_ext hcall p9.ext, hrsd]

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:189-212 classGenRule —
**the generated rule** of a recursor at class `c` for its constructor `x`, the
callee the family's recursor at the landing class (`classRecOf recCls cvGs`,
the twin's specialisation of con-leche's `recOf`); `none` exactly when
con-leche's is. -/
theorem classGenRule_spec (g : Arena.ClassGen) (gP : ConLeche.ClassGen)
    (recCls : List Nat) (cvGs : List IConstantVal) (cvGsP : List ConstantVal)
    (rlvls : LsIdx) (rlvlsP : List Level) (c : Nat) (x : Arena.ClassCtor)
    (xP : ConLeche.ClassCtor) :
    PSpecP (fun st => dClassGen st g = some gP ∧ dClassCtor st x = some xP ∧
        cvGs.mapM (Frontend.denoteCV st) = some cvGsP ∧ denoteLs st.lss rlvls = some rlvlsP)
      (Arena.classGenRule g recCls cvGs rlvls c x)
      (ROp RE (ConLeche.classGenRule gP (ConLeche.classRecOf recCls cvGsP) rlvlsP c xP)) := by
  intro s₀ s' r hok hp hpre hrun
  obtain ⟨hg, hx, hcv, hrl⟩ := hpre
  obtain ⟨hnP, hpar, -, -, hsl, -, -, hpre, hbm⟩ := dClassGen_inv hg
  obtain ⟨hcvx, hnF, hkinds, htyD, htyN⟩ := dClassCtor_inv hx
  have hlen : g.pre.length = gP.pre.length := denoteBinders_length hpre
  have hsll : g.slots.length = gP.slots.length := (mapM_option_length hsl).symm
  have hhit := GR.find_hit hok.wf c (ConRon.Bridge.denoteCV_name hcvx) 0 g.slots gP.slots hsl
  rw [← List.range_eq_range', ← List.range_eq_range'] at hhit
  simp only [Arena.classGenRule] at hrun
  simp only [ConLeche.classGenRule]
  generalize hU : List.find? _ ((List.range gP.slots.length).zip gP.slots) = U
  generalize hT : List.find? _ ((List.range g.slots.length).zip g.slots) = T at hrun
  have hUT : T.map (·.1) = U.map (·.1) := by rw [← hU, ← hT]; exact hhit
  cases T with
  | none =>
    have hn : U = none := by
      cases U with
      | none => rfl
      | some _ => simp at hUT
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨PStep.refl hok, ?_⟩
    show _ = none
    simp only [hn, Option.bind_eq_bind, Option.bind_none]
  | some hs =>
    obtain ⟨sidx, sl⟩ := hs
    obtain ⟨⟨sidx', slP⟩, rfl, hsid⟩ : ∃ u, U = some u ∧ sidx = u.1 := by
      cases U with
      | none => simp at hUT
      | some u => exact ⟨u, rfl, by simpa using hUT⟩
    subst hsid
    simp only [Option.bind_eq_bind, Option.bind_some]
    dsimp only at hrun
    obtain ⟨o, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, ho⟩ := CR.openPisAtFvarsF_run hok htyD k1
    rw [hnF, hlen] at ho
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := pureOk z1
      refine ⟨p1, ?_⟩
      have hn := (Option.some.inj ho).symm
      show _ = none
      simp only [hn, Option.bind_none]
    | some q =>
      obtain ⟨fvs, res⟩ := q
      obtain ⟨fvsP, resP, hq, hfvs, -⟩ := CR.denoteOpen_some_inv ho
      simp only [hq, Option.bind_some]
      dsimp only at z1
      obtain ⟨o2, s2, k2, z2⟩ := bindOk z1
      obtain ⟨p2, ho2⟩ := targetPiDomsWith_spec fvs fvsP x.tyN xP.tyN s1 s2 o2 p1.ok
        ⟨hfvs, denote_ext htyN p1.ext⟩ k2
      have p12 := p1.trans p2
      cases o2 with
      | none =>
        obtain ⟨rfl, rfl⟩ := pureOk z2
        refine ⟨p12, ?_⟩
        have hn : ConLeche.targetPiDomsWith fvsP xP.tyN = none := ho2
        show _ = none
        simp only [hn, Option.bind_none]
      | some ws =>
        obtain ⟨wsP, hws, hwsd⟩ := ho2
        simp only [hws, Option.bind_some]
        dsimp only at z2
        obtain ⟨pvars, s3, k3, z3⟩ := bindOk z2
        obtain ⟨p3, hpv⟩ := GR.mapM_pstepP _
          (fun i => if i < gP.nP then gP.params.getD i default else gP.slotVar (i - gP.nP))
          (fun st b c => denoteE st b = some c) (fun _ st => dClassGen st g = some gP)
          (fun hx h => denote_ext h hx) (fun hx h => dClassGen_ext hx _ _ h)
          (fun i s₀ s' b hok hp hg hrun => by
            have hpar' := (dClassGen_inv hg).2.1
            rw [hnP] at hrun
            by_cases hi : i < gP.nP
            · rw [if_pos hi] at hrun ⊢
              exact exprGetD_spec g.params gP.params i s₀ s' b hok hpar' hrun
            · rw [if_neg hi] at hrun ⊢
              exact ClassGen.slotVar_spec g gP _ s₀ s' b hok hp hg hrun)
          (List.range g.pre.length) s2 s3 pvars p2.ok (PinsOK.ofPStep hp p12)
          (fun _ _ => dClassGen_ext p12.ext _ _ hg) k3
        have hpvE := ListRel.toEList hpv
        rw [hlen] at hpvE
        have p13 := p12.trans p3
        obtain ⟨o3, s4, k4, z4⟩ := bindOk z3
        obtain ⟨p4, ho3⟩ := classGenRule_callsGo_spec g gP recCls cvGs cvGsP rlvls rlvlsP x xP
          hnF hkinds _ fvs ws pvars fvsP wsP _ x.nF 0 s3 s4 o3 p3.ok (PinsOK.ofPStep hp p13)
          ⟨dClassGen_ext p13.ext _ _ hg, denoteEList_ext (p2.ext.trans p3.ext) _ _ hfvs,
            denoteEList_ext p3.ext _ _ hwsd, hpvE, dExt_denoteCV.list p13.ext _ _ hcv,
            denoteLs_ext hrl p13.ext⟩ k4
        rw [GR.filterMapM_eq, show List.range xP.nF = List.range' 0 xP.nF from
          List.range_eq_range']
        rw [hnF, hlen] at ho3
        cases o3 with
        | none =>
          obtain ⟨rfl, rfl⟩ := pureOk z4
          refine ⟨p13.trans p4, ?_⟩
          have hn := ho3
          simp only [ROp] at hn
          show _ = none
          change (GR.filterMapOP (GR.callP gP recCls cvGsP rlvlsP xP fvsP wsP _ gP.pre.length)
            (List.range' 0 xP.nF)).bind _ = none
          rw [hn]; rfl
        | some ihs =>
          obtain ⟨ihsP, hihs, hihsd⟩ := ho3
          change PStep s₀ s' ∧ ROp RE ((GR.filterMapOP (GR.callP gP recCls cvGsP rlvlsP xP fvsP
            wsP _ gP.pre.length) (List.range' 0 xP.nF)).bind _) s'.store r
          rw [hihs]
          simp only [Option.bind_some]
          dsimp only at z4
          have p14 := p13.trans p4
          obtain ⟨sv, s5, k5, z5⟩ := bindOk z4
          obtain ⟨p5, hsv⟩ := ClassGen.slotVar_spec g gP sidx s4 s5 sv p4.ok
            (PinsOK.ofPStep hp p14) (dClassGen_ext p14.ext _ _ hg) k5
          obtain ⟨body, s6, k6, z6⟩ := bindOk z5
          obtain ⟨p6, hbody⟩ := mkAppN_run _ _ p5.ok hsv
            (denoteEList_append (denoteEList_ext (p2.ext.trans (p3.ext.trans (p4.ext.trans
              p5.ext))) _ _ hfvs) (denoteEList_ext p5.ext _ _ hihsd)) k6
          obtain ⟨fbs, s7, k7, z7⟩ := bindOk z6
          obtain ⟨p7, hfbs⟩ := mapM_B_pstep (F := gP.binder) (ClassGen.binder_run hbm) fvs fvsP
            s6 s7 fbs p6.ok (denoteEList_ext (p2.ext.trans (p3.ext.trans (p4.ext.trans
              (p5.ext.trans p6.ext)))) _ _ hfvs) k7
          have p17 := (p14.trans p5).trans (p6.trans p7)
          obtain ⟨rr, s8, k8, z8⟩ := bindOk z7
          obtain ⟨p8, hrr⟩ := closeLams_spec _ _ 0 body _ s7 s8 rr p7.ok
            ⟨GR.denoteBinders_append (denoteBinders_ext p17.ext _ _ hpre) hfbs,
              denote_ext hbody p7.ext⟩ k8
          obtain ⟨rfl, rfl⟩ := pureOk z8
          exact ⟨p17.trans p8, _, rfl, hrr⟩

/-! ## The stage -/

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:218-221 ClassSlot.isMinor
— the minor premises of a denoting slot list are counted alike. -/
theorem isMinor_count {st : EStore} :
    ∀ {slots : List Arena.ClassSlot} {slotsP : List ConLeche.ClassSlot},
      slots.mapM (dSlot st) = some slotsP →
      (slots.filter Arena.ClassSlot.isMinor).length =
        (slotsP.filter ConLeche.ClassSlot.isMinor).length
  | [], _, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | sl :: sls, _, h => by
    obtain ⟨slP, slsP, rfl, hd, hds⟩ := GR.mapM_cons_inv h
    have ih := isMinor_count hds
    cases sl with
    | motive k =>
      simp only [dSlot, Option.map_eq_some_iff] at hd
      obtain ⟨_, _, rfl⟩ := hd
      simp only [List.filter_cons, Arena.ClassSlot.isMinor, ConLeche.ClassSlot.isMinor]
      exact ih
    | minor c C ihs =>
      simp only [dSlot, Option.map_eq_some_iff] at hd
      obtain ⟨_, _, rfl⟩ := hd
      simp only [List.filter_cons, Arena.ClassSlot.isMinor, ConLeche.ClassSlot.isMinor,
        if_true, List.length_cons]
      rw [ih]

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:223-232 classMinorSlot —
**the minor premise slot of a class's constructor**: the same hits, so the same
single hit (the twin fails exactly where con-leche throws). -/
theorem classMinorSlot_spec (rd : Arena.ClassRead) (rdP : ConLeche.ClassRead) (c : Nat)
    (C : NIdx) (CP : ConLeche.Name) :
    PSpec (fun st => dClassRead st rd = some rdP ∧ denoteN st.ns C = some CP)
      (Arena.classMinorSlot rd c C)
      (fun _ r => FOk (ConLeche.classMinorSlot (m := FueledM) rdP c CP) r) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hrd, hC⟩ := hpre
  simp only [dClassRead, Option.map_eq_some_iff] at hrd
  obtain ⟨slotsP, hsl, rfl⟩ := hrd
  have hlen : rd.slots.length = slotsP.length := (mapM_option_length hsl).symm
  simp only [Arena.classMinorSlot] at hrun
  simp only [ConLeche.classMinorSlot]
  generalize hT : List.filterMap _ (List.range rd.slots.length) = T at hrun
  generalize hU : List.filterMap _ (List.range (ConLeche.ClassRead.slots ⟨slotsP, rd.recCls⟩).length) = U
  have hTU : T = U := by
    rw [← hT, ← hU]
    show _ = List.filterMap _ (List.range slotsP.length)
    rw [hlen]
    congr 1
    funext j
    have hj := mapM_option_getElem? (st := s₀.store) hsl j
    cases hs : rd.slots[j]? with
    | none =>
      rw [hs] at hj
      have : slotsP[j]? = none := hj
      simp only [this]
    | some sl =>
      rw [hs] at hj
      obtain ⟨slP, hslP, hd⟩ := hj
      show _ = (match slotsP[j]? with
        | some (.minor c' C' ihs) => if c' == c && C' == CP then some (j, ihs) else none
        | _ => none)
      rw [hslP]
      cases sl with
      | motive k =>
        simp only [dSlot, Option.map_eq_some_iff] at hd
        obtain ⟨_, _, rfl⟩ := hd
        rfl
      | minor c' C' ihs =>
        simp only [dSlot, Option.map_eq_some_iff] at hd
        obtain ⟨CP', hCP', rfl⟩ := hd
        dsimp only
        rw [beq_handle_eq hok.wf hCP' hC]
  subst hTU
  match T, hrun with
  | [], hrun => exact absurd hrun (fun hc => failOk hc)
  | [h], hrun =>
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, FOk.pure _⟩
  | _ :: _ :: _, hrun => exact absurd hrun (fun hc => failOk hc)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:234-254 classFieldsOf —
**the minor premise's inductive hypotheses are the datum's recursive fields**:
the twin's two-test `if` is con-leche's `match` on the occurrence and the
hits; the kinds are con-leche's (`cfOf`). -/
theorem classFieldsOf_spec (p : Arena.BlockShape) (pP : ConLeche.BlockShape)
    (ctor : ConLeche.Name) (ihs : List (Nat × Nat)) :
    ∀ (fs : List EIdx) (fsP : List Expr) (i : Nat),
    PSpec (fun st => dShape st p = some pP ∧ Frontend.denoteEList st fs = some fsP)
      (Arena.classFieldsOf p ihs i fs)
      (fun _ r => FOk (ConLeche.classFieldsOf (m := FueledM) pP ctor ihs i fsP) (r.map cfOf)) := by
  intro fs
  induction fs with
  | nil =>
    intro fsP i s₀ s' r hok hpre hrun
    obtain ⟨-, hfs⟩ := hpre
    simp only [Frontend.denoteEList, Option.some.injEq] at hfs
    subst hfs
    simp only [Arena.classFieldsOf] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, by simp only [ConLeche.classFieldsOf]; exact FOk.pure _⟩
  | cons f fs ih =>
    intro fsP i s₀ s' r hok hpre hrun
    obtain ⟨hsh, hfs⟩ := hpre
    obtain ⟨fP, fsP', hf, hfs', rfl⟩ := Core.denoteEList_cons_inv hfs
    simp only [Arena.classFieldsOf] at hrun
    obtain ⟨w, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨rfl, hw⟩ := fvarTypeD_run hok hf k1
    obtain ⟨occ, s2, k2, z2⟩ := bindOk z1
    obtain ⟨p2, rfl⟩ := nestOcc_spec p.memberNames pP.memberNames 0 0 w _ s1 s2 occ hok
      ⟨BlockShape.memberNames_spec hsh, hw⟩ k2
    simp only [ConLeche.classFieldsOf]
    generalize hH : ihs.filter (·.1 == i) = H at z2 ⊢
    generalize hO : Expr.nestOcc pP.memberNames 0 0 fP.fvarTypeD = O at z2 ⊢
    have hsh2 := dShape_ext p2.ext _ _ hsh
    have hfs2 := denoteEList_ext p2.ext _ _ hfs'
    cases O with
    | false =>
      cases H with
      | nil =>
        simp only [Bool.not_false, List.length_nil, beq_self_eq_true, Bool.and_self,
          ↓reduceIte] at z2
        obtain ⟨rest, s3, k3, z3⟩ := bindOk z2
        obtain ⟨p3, hrest⟩ := ih fsP' (i + 1) s2 s3 rest p2.ok ⟨hsh2, hfs2⟩ k3
        obtain ⟨rfl, rfl⟩ := pureOk z3
        refine ⟨p2.trans p3, ?_⟩
        exact FOk.bind (FOk.pure _) (FOk.bind hrest (FOk.pure _))
      | cons h t =>
        simp only [Bool.not_false, List.length_cons, Bool.true_and, Bool.false_and,
          Bool.false_eq_true, ↓reduceIte] at z2
        exact absurd z2 (fun hc => failOk (by
          have : (Nat.succ t.length == 0) = false := by simp
          simp only [this, Bool.false_eq_true, ↓reduceIte] at hc; exact hc))
    | true =>
      match H, z2 with
      | [], z2 =>
        simp at z2; exact absurd z2 (fun hc => failOk hc)
      | [(a, t)], z2 =>
        simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          List.length_singleton, beq_self_eq_true, Bool.and_self] at z2
        obtain ⟨q, s3, k3, z3⟩ := bindOk z2
        obtain ⟨p3, hq1, -⟩ := piBinders_spec coreWalkFuel w _ s2 s3 q p2.ok
          (denote_ext hw p2.ext) k3
        obtain ⟨bs, leaf⟩ := q
        dsimp only at z3
        obtain ⟨rest, s4, k4, z4⟩ := bindOk z3
        obtain ⟨p4, hrest⟩ := ih fsP' (i + 1) s3 s4 rest p3.ok
          ⟨dShape_ext p3.ext _ _ hsh2, denoteEList_ext p3.ext _ _ hfs2⟩ k4
        obtain ⟨rfl, rfl⟩ := pureOk z4
        refine ⟨p2.trans (p3.trans p4), ?_⟩
        have hbl : bs.length = fP.fvarTypeD.piBinders.1.length := denoteBinders_length hq1
        simp only [List.map_cons, cfOf, List.getD_cons_zero, hbl]
        exact FOk.bind (FOk.pure _) (FOk.bind hrest (FOk.pure _))
      | _ :: _ :: _, z2 =>
        simp at z2; exact absurd z2 (fun hc => failOk hc)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:273-277 classLeafAt — a
walked field's leaf is headed by the class's inductive: the tag test and the
`viewConst` read are con-leche's `match` on the head. -/
theorem classLeafAt_spec (m : Arena.TargetMajor) (mP : ConLeche.TargetMajor) (leaf : EIdx)
    (leafP : Expr) :
    PSpec (fun st => dMajor st m = some mP ∧ denoteE st leaf = some leafP)
      (Arena.classLeafAt m leaf) (RV (ConLeche.classLeafAt mP leafP)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hm, hleaf⟩ := hpre
  have hind := (dMajor_inv hm).1
  simp only [Arena.classLeafAt] at hrun
  obtain ⟨hd, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨rfl, hhd⟩ := getAppFn_run hok hleaf k1
  simp only [ConLeche.classLeafAt]
  by_cases ct : (hd.tag == ETag.const) = true
  · rw [if_pos ct] at z1
    obtain ⟨o, s2, k2, z2⟩ := bindOk z1
    obtain ⟨rfl, ho⟩ := PW.viewConst_run k2
    cases o with
    | none => exact absurd z2 (fun hc => failDanglingE_ok hc)
    | some t0 =>
      obtain ⟨I, us⟩ := t0
      obtain ⟨IP, usP, hg, hI, -⟩ := denote_const_inv hok.wf
        (view_of_viewConst_tag ct ho.symm) hhd
      dsimp only at z2
      obtain ⟨rfl, rfl⟩ := pureOk z2
      refine ⟨PStep.refl hok, ?_⟩
      rw [hg]
      exact beq_handle_eq hok.wf hI hind
  · rw [if_neg ct] at z1
    obtain ⟨rfl, rfl⟩ := pureOk z1
    refine ⟨PStep.refl hok, ?_⟩
    cases hga : leafP.getAppFn with
    | const I us =>
      rw [hga] at hhd
      exact absurd (tag_const_of_denote hok.wf hhd) (by simpa using ct)
    | _ => rfl

/-- con-leche: none — `Option.getD []` on a two-sided list answer. -/
theorem ROp_REL_getD {st : EStore} {x : Option (List Expr)} {o : Option (List EIdx)}
    (h : ROp REL x st o) : Frontend.denoteEList st (o.getD []) = some (x.getD []) := by
  cases o with
  | none =>
    have hx : x = none := h
    rw [hx]; rfl
  | some l =>
    obtain ⟨v, hv, hl⟩ := h
    rw [hv]; exact hl

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:256-271 classNodesAgree —
**node agreement at one recursive field** (K.53′), at every recorded entry of
the constructor: the recorded field read at the same position, `targetK53`
answering con-leche's at `fueledOpsM μ`.  Scoping as the cached bridge's
`classNodesAgreeS_sim`. -/
theorem classNodesAgree_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (formerTys : List EIdx)
    (formerTysP : List Expr) (mc : Arena.TargetMajor) (McP : ConLeche.TargetMajor)
    (tele : List (EIdx × BinderMeta)) (teleP : List (Expr × BinderMeta)) (leaf : EIdx)
    (leafP : Expr) (fvs : List EIdx) (fvsP : List Expr) (i : Nat) (ctor : ConLeche.Name)
    (hformer : ∀ t ∈ formerTysP, Expr.WScoped 0 t) (hMc : Cached.TargetMajScoped McP) :
    ∀ (es : List Arena.NestCtorNf) (esP : List ConLeche.NestCtorNf),
    CSpecF μ env fe
      (fun st => dShape st p = some pP ∧ Frontend.denoteEList st formerTys = some formerTysP ∧
        dMajor st mc = some McP ∧ denoteBinders st tele = some teleP ∧
        denoteE st leaf = some leafP ∧ Frontend.denoteEList st fvs = some fvsP ∧
        es.mapM (dCtorNf st) = some esP)
      (Arena.classNodesAgree μ fe p formerTys mc tele leaf fvs i es) (fun _ _ _ => True)
      (ConLeche.classNodesAgree (fueledOpsM μ) env pP formerTysP McP teleP leafP fvsP i ctor
        esP) := by
  intro es
  induction es with
  | nil =>
    intro esP s₀ s' r hok hpre hrun
    obtain ⟨-, -, -, -, -, -, hes⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hes
    subst hes
    simp only [Arena.classNodesAgree] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, (), trivial, by simp only [ConLeche.classNodesAgree]; exact FOk.pure _⟩
  | cons e es ih =>
    intro esP s₀ s' r hok hpre hrun
    obtain ⟨hsh, hft, hmc, htele, hleaf, hfvs, hes⟩ := hpre
    obtain ⟨eP, esP', rfl, he, hes'⟩ := GR.mapM_cons_inv hes
    have hety := (RC.dCtorNf_inv he).2.2.2
    simp only [Arena.classNodesAgree] at hrun
    simp only [ConLeche.classNodesAgree]
    obtain ⟨o, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, ho⟩ := targetPiDomsWith_spec fvs fvsP e.ty eP.ty s₀ s1 o hok.state
      ⟨hfvs, hety⟩ k1
    have c1 := p1.toCore hok
    have hdoms := ROp_REL_getD ho
    obtain ⟨hj1, hj2⟩ := PW.denoteEList_getElem? hdoms i
    generalize hD : (o.getD [])[i]? = D at z1
    cases D with
    | none =>
      exact absurd z1 (fun hc => failOk hc)
    | some f =>
      obtain ⟨fP, hfP, hfd⟩ := hj2 f hD
      rw [hfP]
      obtain ⟨b, s2, k2, z2⟩ := bindOk z1
      obtain ⟨c2, v, rfl, hK⟩ := targetK53_spec fe hk henv p pP formerTys formerTysP mc McP tele
        teleP leaf f leafP fP hformer hMc s1 s2 b c1.ok
        ⟨dShape_ext c1.ext _ _ hsh, denoteEList_ext c1.ext _ _ hft, dMajor_ext c1.ext _ _ hmc,
          denoteBinders_ext c1.ext _ _ htele, denote_ext hleaf c1.ext, hfd⟩ k2
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at z2
        exact absurd z2 (fun hc => failOk hc)
      | true =>
        simp only [↓reduceIte] at z2
        have c12 := c1.trans c2
        obtain ⟨c3, ⟨⟩, -, hR⟩ := ih esP' s2 s' r c2.ok
          ⟨dShape_ext c12.ext _ _ hsh, denoteEList_ext c12.ext _ _ hft,
            dMajor_ext c12.ext _ _ hmc, denoteBinders_ext c12.ext _ _ htele,
            denote_ext hleaf c12.ext, denoteEList_ext c12.ext _ _ hfvs,
            dCtorNf_ext.list c12.ext _ _ hes'⟩ z2
        refine ⟨c12.trans c3, (), trivial, ?_⟩
        exact FOk.bind hK (by simp only [↓reduceIte]; exact FOk.seq (FOk.pure ()) hR)

/-- con-leche: none — a `some` answer of `stripPis`, with its binders. -/
theorem stripPis_someB {st : EStore} {k : Nat} {cP : Expr}
    {bs : List (EIdx × BinderMeta)} {e : EIdx}
    (h : ExprOps.denoteBP st (some (bs, e)) = some (Expr.stripPis k cP)) :
    ∃ xs x, Expr.stripPis k cP = some (xs, x) ∧ denoteBinders st bs = some xs ∧
      denoteE st e = some x := by
  simp only [ExprOps.denoteBP] at h
  cases hb : ExprOps.denoteBL st bs with
  | none => rw [hb] at h; simp at h
  | some xs =>
    cases he : denoteE st e with
    | none => rw [hb, he] at h; simp at h
    | some x =>
      rw [hb, he] at h
      exact ⟨xs, x, (Option.some.inj h).symm, by rw [denoteBinders_eq_denoteBL, hb], rfl⟩

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:279-293 classFieldsAgree —
**node agreement at every recursive field of the datum**: the field's
telescope stripped, its leaf at the inductive hypothesis's class, then every
entry (`classNodesAgree`).  Scoping as `classFieldsAgreeS_sim`. -/
theorem classFieldsAgree_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (formerTys : List EIdx)
    (formerTysP : List Expr) (ms : List Arena.TargetMajor) (MsP : List ConLeche.TargetMajor)
    (fvs : List EIdx) (fvsP : List Expr) (es : List Arena.NestCtorNf)
    (esP : List ConLeche.NestCtorNf) (ctor : ConLeche.Name)
    (hformer : ∀ t ∈ formerTysP, Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, Cached.TargetMajScoped M) :
    ∀ (ks : List Arena.ClassField) (i : Nat),
    CSpecF μ env fe
      (fun st => dShape st p = some pP ∧ Frontend.denoteEList st formerTys = some formerTysP ∧
        ms.mapM (dMajor st) = some MsP ∧ Frontend.denoteEList st fvs = some fvsP ∧
        es.mapM (dCtorNf st) = some esP)
      (Arena.classFieldsAgree μ fe p formerTys ms fvs es i ks) (fun _ _ _ => True)
      (ConLeche.classFieldsAgree (fueledOpsM μ) env pP formerTysP MsP fvsP ctor esP i
        (ks.map cfOf)) := by
  intro ks
  induction ks with
  | nil =>
    intro i s₀ s' r hok _ hrun
    simp only [Arena.classFieldsAgree] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, (), trivial, by
      simp only [List.map_nil, ConLeche.classFieldsAgree]; exact FOk.pure _⟩
  | cons kd ks ih =>
    intro i s₀ s' r hok hpre hrun
    obtain ⟨hsh, hft, hms, hfvs, hes⟩ := hpre
    cases kd with
    | ordinary =>
      simp only [Arena.classFieldsAgree] at hrun
      obtain ⟨c1, u, hu, hF⟩ := ih (i + 1) s₀ s' r hok ⟨hsh, hft, hms, hfvs, hes⟩ hrun
      exact ⟨c1, u, hu, by simpa only [List.map_cons, cfOf, ConLeche.classFieldsAgree] using hF⟩
    | recursive t tele =>
      simp only [Arena.classFieldsAgree] at hrun
      simp only [List.map_cons, cfOf, ConLeche.classFieldsAgree]
      obtain ⟨fv, s1, k1, z1⟩ := bindOk hrun
      obtain ⟨p1, hfv⟩ := exprGetD_spec fvs fvsP i s₀ s1 fv hok.state hfvs k1
      obtain ⟨fty, s2, k2, z2⟩ := bindOk z1
      obtain ⟨rfl, hfty⟩ := fvarTypeD_run p1.ok hfv k2
      obtain ⟨q, s3, k3, z3⟩ := bindOk z2
      obtain ⟨rfl, hq⟩ := stripPis_pstep p1.ok hfty k3
      cases q with
      | none => exact absurd z3 (fun hc => failOk hc)
      | some q =>
        obtain ⟨teleB, leaf⟩ := q
        obtain ⟨teleP, leafP, hsp, hteleB, hleaf⟩ := stripPis_someB hq
        rw [hsp]
        dsimp only at z3
        obtain ⟨mt, s4, k4, z4⟩ := bindOk z3
        obtain ⟨p4, hmt⟩ := targetMajorAt_spec ms MsP t _ s4 mt p1.ok
          (PinsOK.ofPStep hok.pins p1) (dMajor_ext.list p1.ext _ _ hms) k4
        obtain ⟨b, s5, k5, z5⟩ := bindOk z4
        obtain ⟨p5, rfl⟩ := classLeafAt_spec mt _ leaf leafP s4 s5 b p4.ok
          ⟨hmt, denote_ext hleaf p4.ext⟩ k5
        have c15 := (p1.trans (p4.trans p5)).toCore hok
        by_cases hb : ConLeche.classLeafAt (MsP.getD t default) leafP = true
        · rw [if_pos hb] at z5
          obtain ⟨u1, s6, k6, z6⟩ := bindOk z5
          have p45 := p4.trans p5
          obtain ⟨c6, ⟨⟩, -, hN⟩ := classNodesAgree_spec fe hk henv p pP formerTys formerTysP mt
            (MsP.getD t default) teleB teleP leaf leafP fvs fvsP i ctor hformer
            (Cached.TargetMajScoped.getD hMs t) es esP s5 s6 u1 c15.ok
            ⟨dShape_ext c15.ext _ _ hsh, denoteEList_ext c15.ext _ _ hft,
              dMajor_ext p5.ext _ _ hmt, denoteBinders_ext p45.ext _ _ hteleB,
              denote_ext hleaf p45.ext, denoteEList_ext c15.ext _ _ hfvs,
              dCtorNf_ext.list c15.ext _ _ hes⟩ k6
          have c16 := c15.trans c6
          obtain ⟨c7, ⟨⟩, -, hR⟩ := ih (i + 1) s6 s' r c6.ok
            ⟨dShape_ext c16.ext _ _ hsh, denoteEList_ext c16.ext _ _ hft,
              dMajor_ext.list c16.ext _ _ hms, denoteEList_ext c16.ext _ _ hfvs,
              dCtorNf_ext.list c16.ext _ _ hes⟩ z6
          refine ⟨c16.trans c7, (), trivial, FOk.bind FOk.unwrapOr ?_⟩
          simp only [hb, ↓reduceIte]
          exact FOk.seq hN hR
        · rw [if_neg hb] at z5
          exact absurd z5 (fun hc => failOk hc)

end ConRon.Bridge.Inductives

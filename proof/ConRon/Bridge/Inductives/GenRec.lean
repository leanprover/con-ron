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

end ConRon.Bridge.Inductives

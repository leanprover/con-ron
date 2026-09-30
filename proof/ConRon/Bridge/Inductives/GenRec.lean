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
  and the popped index answers exactly as the input one (`GR.classFeR_pop`,
  `GR.FEq`: the same list, the same bound, the same row at every key);
* `recOf` is `classRecOf recCls cvGs`, `ClassGen.bm` a field (the denotation
  `dClassGen` pins it to `⟨Level.zeronessOf elim⟩`), `exprGetD` /
  `targetMajorAt` the `getD … default` reads.

The twins' `let rec` walks (`minorTy.ihsGo`, `prefixBinders.slotsGo`,
`classGenRule.callsGo`) run over the lists con-leche's indexed `mapM` /
`filterMapM` range over; `GR.mapIdxFromP` and `GR.filterMapOP` are those as list
recursions, `GR.mapM_range_getD` / `GR.filterMapM_eq` the bridges.

The headlines are `genRecCheck_spec` (at the constructors' environment) and
`checkBlockClasses_spec` (at the formers'); `classSeeds_spec` is the pass's
seeds.
-/
import ConRon.Arena.Inductives.GenRec
import ConRon.Bridge.Inductives.RecCheck
import ConRon.Bridge.Inductives.ClassRead
import ConRon.Bridge.Inductives.FieldTele
import ConRon.Bridge.Inductives.Positivity
import ConRon.Bridge.Inductives.BlockRec
import ConLeche.Verify.Cached.GenRecC
import ConLeche.Verify.Inductives.GenRecRun
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Cached.BlockRunC

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

/-- con-leche: none — `cfOf` is injective. -/
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

/-- con-leche: none — `dClassCtor` survives the arena's growth. -/
theorem dClassCtor_ext : DExt dClassCtor := by
  intro st st' hx x y h
  simp only [dClassCtor, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h ⊢
  obtain ⟨cv, h1, tyD, h2, tyN, h3, rfl⟩ := h
  exact ⟨cv, dExt_denoteCV hx _ _ h1, tyD, denote_ext h2 hx, tyN, denote_ext h3 hx, rfl⟩

/-- con-leche: none — and so does its list-of-lists lift. -/
theorem dClassCtors_ext : DExt (fun st (xss : List (List Arena.ClassCtor)) =>
    xss.mapM (fun xs => xs.mapM (dClassCtor st))) :=
  DExt.list (DExt.list dClassCtor_ext)

/-- con-leche: none — `dClassGen` survives the arena's growth. -/
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

/-- con-leche: none — a generator with its prefix set. -/
theorem dClassGen_pre {st : EStore} {g : Arena.ClassGen} {gP : ConLeche.ClassGen}
    {pre : List (EIdx × BinderMeta)} {preP : List (Expr × BinderMeta)}
    (h : dClassGen st g = some gP) (hp : denoteBinders st pre = some preP) :
    dClassGen st { g with pre := pre } = some { gP with pre := preP } := by
  obtain ⟨hnP, h1, h2, h3, h4, h5, h6, -, hbm⟩ := dClassGen_inv h
  simp only [dClassGen, h1, h2, h3, h4, h5, h6, hp, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def]
  rw [if_pos (show g.bm = ⟨gP.elim.zeronessOf⟩ from hbm), hnP]

/-- con-leche: none — `denoteEList` is `mapM denoteE`. -/
theorem mapM_denoteE_eq_list {st : EStore} :
    ∀ (l : List EIdx), l.mapM (fun e => denoteE st e) = Frontend.denoteEList st l
  | [] => rfl
  | a :: l => by
    simp only [List.mapM_cons, Frontend.denoteEList, mapM_denoteE_eq_list l,
      Option.bind_eq_bind, Option.pure_def]
    cases denoteE st a <;> cases Frontend.denoteEList st l <;> rfl

/-- con-leche: none — `mapM denoteE` is `denoteEList`. -/
theorem mapM_denoteE {st : EStore} :
    ∀ {l : List EIdx} {v : List Expr}, l.mapM (fun e => denoteE st e) = some v →
      Frontend.denoteEList st l = some v
  | [], v, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | a :: l, v, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at h
    cases ha : denoteE st a with
    | none => rw [ha] at h; simp at h
    | some x =>
    cases hl : l.mapM (fun e => denoteE st e) with
    | none => rw [ha, hl] at h; simp at h
    | some xs =>
    rw [ha, hl] at h
    simp only [Option.bind_some, Option.some.injEq] at h
    subst h
    simp only [Frontend.denoteEList, ha, mapM_denoteE hl]

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

/-- con-leche: none — `mapM` over `List.range'` at a list's entries is
`mapIdxFromP`. -/
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

/-- con-leche: none — `List.filterMapM` in `Option` is `filterMapOP`. -/
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

/-- con-leche: none — a denoting table's entries at a constructor name. -/
theorem filter_nfs {st : EStore} (hwf : StoreWF st) {C : NIdx} {CP : ConLeche.Name}
    (hC : denoteN st.ns C = some CP) :
    ∀ (es : List Arena.NestCtorNf) (esP : List ConLeche.NestCtorNf),
      es.mapM (dCtorNf st) = some esP →
      (es.filter (·.ctor == C)).mapM (dCtorNf st) = some (esP.filter (·.ctor == CP))
  | [], esP, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | e :: es, esP, h => by
    obtain ⟨eP, esP', rfl, he, hes⟩ := GR.mapM_cons_inv h
    have ih := filter_nfs hwf hC es esP' hes
    have hb := beq_handle_eq hwf (RC.dCtorNf_inv he).1 hC
    simp only [List.filter_cons, hb]
    split
    · simp only [List.mapM_cons, he, ih, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    · exact ih

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:295-313 classCtorOf —
**one constructor of class `c`, read for the generator**: its entries in the
class's table (the first the DATUM), the minor premise's inductive hypotheses
against the datum's recursive fields, node agreement at every entry, and the
constructor's declared type at the class. -/
theorem classCtorOf_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (formerTys : List EIdx)
    (formerTysP : List Expr) (rd : Arena.ClassRead) (rdP : ConLeche.ClassRead)
    (ms : List Arena.TargetMajor) (MsP : List ConLeche.TargetMajor) (c : Nat)
    (cA : IConstantVal × Nat) (cAP : ConstantVal × Nat)
    (hformer : ∀ t ∈ formerTysP, Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, Cached.TargetMajScoped M) :
    CSpecF μ env fe
      (fun st => dShape st p = some pP ∧ Frontend.denoteEList st formerTys = some formerTysP ∧
        dClassRead st rd = some rdP ∧ ms.mapM (dMajor st) = some MsP ∧ dCtor st cA = some cAP)
      (Arena.classCtorOf μ fe p formerTys rd ms c cA) (fun st r v => dClassCtor st r = some v)
      (ConLeche.classCtorOf (fueledOpsM μ) env pP formerTysP rdP MsP c cAP) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hsh, hft, hrd, hms, hcA⟩ := hpre
  simp only [dCtor, Option.map_eq_some_iff] at hcA
  obtain ⟨cvP, hcv, rfl⟩ := hcA
  have hname := ConRon.Bridge.denoteCV_name hcv
  obtain ⟨-, -, hnP, -, -, -, -⟩ := RC.dShape_inv hsh
  have hk' := BlockShape.k_spec hsh
  simp only [Arena.classCtorOf] at hrun
  simp only [ConLeche.classCtorOf]
  obtain ⟨m, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, hm⟩ := targetMajorAt_spec ms MsP c s₀ s1 m hok.state hok.pins hms k1
  obtain ⟨-, -, hmds, -, -, -, -, hnfs, -⟩ := dMajor_inv hm
  have hE := filter_nfs p1.ok.wf (denoteN_ext hname p1.ext) _ _ hnfs
  generalize hEs : m.nfs.filter (·.ctor == cA.1.name) = Es at z1 hE
  generalize hEP : (MsP.getD c default).nfs.filter (·.ctor == cvP.name) = EsP at hE ⊢
  cases Es with
  | nil => exact absurd z1 (fun hc => failOk hc)
  | cons e0 Es' =>
    obtain ⟨e0P, EsP', rfl, he0, hEs'⟩ := GR.mapM_cons_inv hE
    have he0ty := (RC.dCtorNf_inv he0).2.2.2
    dsimp only at z1
    obtain ⟨sl, s2, k2, z2⟩ := bindOk z1
    obtain ⟨p2, hsl⟩ := classMinorSlot_spec rd rdP c cA.1.name cvP.name s1 s2 sl p1.ok
      ⟨dClassRead_ext p1.ext _ _ hrd, denoteN_ext hname p1.ext⟩ k2
    obtain ⟨slot, ihs⟩ := sl
    dsimp only at z2
    obtain ⟨o, s3, k3, z3⟩ := bindOk z2
    obtain ⟨p3, ho⟩ := CR.openPisAtFvarsF_run p2.ok (denote_ext he0ty p2.ext) k3
    rw [hnP, hk'] at ho
    cases o with
    | none => exact absurd z3 (fun hc => failOk hc)
    | some q =>
      obtain ⟨fvs, body⟩ := q
      obtain ⟨fvsP, bodyP, hq, hfvs, -⟩ := CR.denoteOpen_some_inv ho
      dsimp only at z3
      have p13 := p1.trans (p2.trans p3)
      obtain ⟨kinds, s4, k4, z4⟩ := bindOk z3
      obtain ⟨p4, hkinds⟩ := classFieldsOf_spec p pP cvP.name ihs fvs fvsP 0 s3 s4 kinds p3.ok
        ⟨dShape_ext p13.ext _ _ hsh, hfvs⟩ k4
      have p14 := p13.trans p4
      have c14 := p14.toCore hok
      obtain ⟨u, s5, k5, z5⟩ := bindOk z4
      obtain ⟨c5, ⟨⟩, -, hagree⟩ := classFieldsAgree_spec fe hk henv p pP formerTys formerTysP ms
        MsP fvs fvsP (e0 :: Es') (e0P :: EsP') cvP.name hformer hMs kinds 0 s4 s5 u c14.ok
        ⟨dShape_ext c14.ext _ _ hsh, denoteEList_ext c14.ext _ _ hft,
          dMajor_ext.list c14.ext _ _ hms, denoteEList_ext p4.ext _ _ hfvs,
          dCtorNf_ext.list (p2.trans (p3.trans p4)).ext _ _ hE⟩ k5
      have c15 := c14.trans c5
      obtain ⟨t0, s6, k6, z6⟩ := bindOk z5
      obtain ⟨c6, ht0⟩ := targetCtorAt_spec fe m _ cA.1 cvP s5 s6 t0 c5.ok
        ⟨dMajor_ext (p2.ext.trans (p3.ext.trans (p4.ext.trans c5.ext))) _ _ hm,
          dExt_denoteCV c15.ext _ _ hcv⟩ k6
      have c16 := c15.trans c6
      obtain ⟨o2, s7, k7, z7⟩ := bindOk z6
      obtain ⟨p7, ho2⟩ := instPisWith_spec m.ds _ t0 _ s6 s7 o2 c6.ok.state
        ⟨denoteEList_ext (p2.ext.trans (p3.ext.trans (p4.ext.trans (c5.ext.trans c6.ext))))
          _ _ hmds, ht0⟩ k7
      have c17 := c16.trans (p7.toCore c6.ok)
      cases o2 with
      | none => exact absurd z7 (fun hc => failOk hc)
      | some tyD =>
        obtain ⟨tyDP, htyD, htyDd⟩ := ho2
        dsimp only at z7
        obtain ⟨rfl, rfl⟩ := pureOk z7
        refine ⟨c17, ⟨cvP, cA.2, kinds.map cfOf, tyDP, e0P.ty⟩, ?_, ?_⟩
        · simp only [dClassCtor, dExt_denoteCV c17.ext _ _ hcv, htyDd,
            denote_ext he0ty (p2.ext.trans (p3.ext.trans (p4.ext.trans (c5.ext.trans
              (c6.ext.trans p7.ext))))), Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        · refine FOk.bind FOk.unwrapOr (FOk.bind hsl ?_)
          dsimp only
          rw [hq]
          refine FOk.bind FOk.unwrapOr (FOk.bind hkinds (FOk.seq hagree ?_))
          rw [htyD]
          exact FOk.bind FOk.unwrapOr (FOk.pure _)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:315-323 classCtorsOf —
every constructor of class `c`. -/
theorem classCtorsOf_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (formerTys : List EIdx)
    (formerTysP : List Expr) (rd : Arena.ClassRead) (rdP : ConLeche.ClassRead)
    (ms : List Arena.TargetMajor) (MsP : List ConLeche.TargetMajor) (c : Nat)
    (hformer : ∀ t ∈ formerTysP, Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, Cached.TargetMajScoped M) :
    ∀ (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat)),
    CSpecF μ env fe
      (fun st => dShape st p = some pP ∧ Frontend.denoteEList st formerTys = some formerTysP ∧
        dClassRead st rd = some rdP ∧ ms.mapM (dMajor st) = some MsP ∧ dCtors st cs = some csP)
      (Arena.classCtorsOf μ fe p formerTys rd ms c cs)
      (fun st r v => r.mapM (dClassCtor st) = some v)
      (ConLeche.classCtorsOf (fueledOpsM μ) env pP formerTysP rdP MsP c csP) := by
  intro cs
  induction cs with
  | nil =>
    intro csP s₀ s' r hok hpre hrun
    obtain ⟨-, -, -, -, hcs⟩ := hpre
    simp only [dCtors, List.mapM_nil, Option.pure_def, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.classCtorsOf] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, [], rfl, by simp only [ConLeche.classCtorsOf]; exact FOk.pure _⟩
  | cons cA cs ih =>
    intro csP s₀ s' r hok hpre hrun
    obtain ⟨hsh, hft, hrd, hms, hcs⟩ := hpre
    obtain ⟨cAP, csP', rfl, hcA, hcs'⟩ := GR.mapM_cons_inv hcs
    simp only [Arena.classCtorsOf] at hrun
    obtain ⟨x, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨c1, xP, hx, hF1⟩ := classCtorOf_spec fe hk henv p pP formerTys formerTysP rd rdP ms
      MsP c cA cAP hformer hMs s₀ s1 x hok ⟨hsh, hft, hrd, hms, hcA⟩ k1
    obtain ⟨xs, s2, k2, z2⟩ := bindOk z1
    obtain ⟨c2, xsP, hxs, hF2⟩ := ih csP' s1 s2 xs c1.ok
      ⟨dShape_ext c1.ext _ _ hsh, denoteEList_ext c1.ext _ _ hft, dClassRead_ext c1.ext _ _ hrd,
        dMajor_ext.list c1.ext _ _ hms, dCtors_ext c1.ext _ _ hcs'⟩ k2
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨c1.trans c2, xP :: xsP, ?_, ?_⟩
    · simp only [List.mapM_cons, dClassCtor_ext c2.ext _ _ hx, hxs, Option.bind_eq_bind,
        Option.bind_some, Option.pure_def]
    · simp only [ConLeche.classCtorsOf]
      exact FOk.bind hF1 (FOk.bind hF2 (FOk.pure _))

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:325-332 classesCtors —
every class's constructors, from class `c` on. -/
theorem classesCtors_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (formerTys : List EIdx)
    (formerTysP : List Expr) (rd : Arena.ClassRead) (rdP : ConLeche.ClassRead)
    (ms : List Arena.TargetMajor) (MsP : List ConLeche.TargetMajor)
    (hformer : ∀ t ∈ formerTysP, Expr.WScoped 0 t)
    (hMs : ∀ M ∈ MsP, Cached.TargetMajScoped M) :
    ∀ (l : List Arena.TargetMajor) (lP : List ConLeche.TargetMajor) (c : Nat),
    CSpecF μ env fe
      (fun st => dShape st p = some pP ∧ Frontend.denoteEList st formerTys = some formerTysP ∧
        dClassRead st rd = some rdP ∧ ms.mapM (dMajor st) = some MsP ∧
        l.mapM (dMajor st) = some lP)
      (Arena.classesCtors μ fe p formerTys rd ms c l)
      (fun st r v => r.mapM (fun xs => xs.mapM (dClassCtor st)) = some v)
      (ConLeche.classesCtors (fueledOpsM μ) env pP formerTysP rdP MsP c lP) := by
  intro l
  induction l with
  | nil =>
    intro lP c s₀ s' r hok hpre hrun
    obtain ⟨-, -, -, -, hl⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hl
    subst hl
    simp only [Arena.classesCtors] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, [], rfl, by simp only [ConLeche.classesCtors]; exact FOk.pure _⟩
  | cons m l ih =>
    intro lP c s₀ s' r hok hpre hrun
    obtain ⟨hsh, hft, hrd, hms, hl⟩ := hpre
    obtain ⟨mP, lP', rfl, hm, hl'⟩ := GR.mapM_cons_inv hl
    have hmc := (dMajor_inv hm).2.2.2.2.2.1
    simp only [Arena.classesCtors] at hrun
    obtain ⟨xs, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨c1, xsP, hxs, hF1⟩ := classCtorsOf_spec fe hk henv p pP formerTys formerTysP rd rdP ms
      MsP c hformer hMs m.ctors mP.ctors s₀ s1 xs hok ⟨hsh, hft, hrd, hms, hmc⟩ k1
    obtain ⟨xss, s2, k2, z2⟩ := bindOk z1
    obtain ⟨c2, xssP, hxss, hF2⟩ := ih lP' (c + 1) s1 s2 xss c1.ok
      ⟨dShape_ext c1.ext _ _ hsh, denoteEList_ext c1.ext _ _ hft, dClassRead_ext c1.ext _ _ hrd,
        dMajor_ext.list c1.ext _ _ hms, dMajor_ext.list c1.ext _ _ hl'⟩ k2
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨c1.trans c2, xsP :: xssP, ?_, ?_⟩
    · simp only [List.mapM_cons, dClassCtor_ext.list c2.ext _ _ hxs, hxss, Option.bind_eq_bind,
        Option.bind_some, Option.pure_def]
    · simp only [ConLeche.classesCtors]
      exact FOk.bind hF1 (FOk.bind hF2 (FOk.pure _))

/-- con-leche: none — **what a class checked as a major is** (the cached
bridge's private `classMajorOf_shape`, at the pure run): its openers are the
parameter openers; a member at the openers' parameters, an outside class's
parameters among the class application's arguments, below the parameters. -/
theorem classMajorOf_shape {fe : FEnv} {p : ConLeche.BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {pfvs : List Expr} {mty : Expr}
    {M : ConLeche.TargetMajor}
    (h : FOk (ConLeche.targetMajorOf (m := FueledM) fe p ctorsAs pfvs pfvs mty) M) :
    M.pfvs = pfvs ∧ (∀ t, M.member = some t → M.ds = pfvs.take p.nP) ∧
      (M.member = none → ∀ x ∈ M.ds, x ∈ mty.getAppArgs ∧ x.fvarB ≤ p.nP) := by
  obtain ⟨F, hF⟩ := h
  rw [targetMajorOf_datF] at hF
  obtain ⟨⟨R⟩, hpf⟩ := targetMajorOf_run hF
  refine ⟨hpf, ?_, ?_⟩
  · intro t ht
    cases R with
    | member => rfl
    | outside => exact nomatch ht
  · intro hn x hx
    obtain ⟨-, -, -, -, -, hds, -, hsc, -⟩ := R.outside_facts hn
    refine ⟨?_, (hsc x hx).2⟩
    rw [hds] at hx
    exact List.mem_of_mem_take hx

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:334-344 classMajors —
**every class checked as a major** over the canonical parameters: each
answer denotes con-leche's, and every class is scoped (`ClassMajScoped`,
the cached bridge's `classMajorsS_sim`). -/
theorem classMajors_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape)
    (ctorsAs : List (List (IConstantVal × Nat))) (ctorsAsP : List (List (ConstantVal × Nat)))
    (pfvs : List EIdx) (pfvsP : List Expr) (hpl : pfvsP.length = pP.nP)
    (hp : ∀ x ∈ pfvsP, Expr.WScoped pP.nP x) :
    ∀ (keys : List Arena.ClassKey) (keysP : List ConLeche.ClassKey),
    (∀ key ∈ keysP, ∀ x ∈ key.ds, ∃ D, Expr.WScoped D x) →
    CSpecF μ env fe
      (fun st => dShape st p = some pP ∧ ctorsAs.mapM (dCtors st) = some ctorsAsP ∧
        Frontend.denoteEList st pfvs = some pfvsP ∧ keys.mapM (dClassKey st) = some keysP)
      (Arena.classMajors μ fe p ctorsAs pfvs keys)
      (fun st r v => r.mapM (dMajor st) = some v ∧ ∀ M ∈ v, Cached.ClassMajScoped pP.nP M)
      (ConLeche.classMajors (fueledOpsM μ) (mkFEnv env) pP ctorsAsP pfvsP keysP) := by
  intro keys
  induction keys with
  | nil =>
    intro keysP _ s₀ s' r hok hpre hrun
    obtain ⟨-, -, -, hks⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hks
    subst hks
    simp only [Arena.classMajors] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, [], ⟨rfl, fun _ h => nomatch h⟩, by
      simp only [ConLeche.classMajors]; exact FOk.pure _⟩
  | cons key keys ih =>
    intro keysP hsc s₀ s' r hok hpre hrun
    obtain ⟨hsh, hcas, hpf, hks⟩ := hpre
    obtain ⟨keyP, keysP', rfl, hkey, hks'⟩ := GR.mapM_cons_inv hks
    simp only [dClassKey, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hkey
    obtain ⟨ind, hind, lvls, hlvls, ds, hds, rfl⟩ := hkey
    obtain ⟨-, -, hnP, -, -, -, -⟩ := RC.dShape_inv hsh
    simp only [Arena.classMajors] at hrun
    obtain ⟨hd, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hhd⟩ := internConstE_run hok.state hind hlvls k1
    obtain ⟨mty, s2, k2, z2⟩ := bindOk z1
    obtain ⟨p2, hmty⟩ := mkAppN_run _ _ p1.ok hhd (denoteEList_ext p1.ext _ _ hds) k2
    have c12 := (p1.trans p2).toCore hok
    obtain ⟨m, s3, k3, z3⟩ := bindOk z2
    obtain ⟨c3, MP, hm, hF1⟩ := targetMajorOf_spec fe p pP ctorsAs ctorsAsP pfvs pfvs pfvsP pfvsP
      mty _ s2 s3 m c12.ok
      ⟨dShape_ext c12.ext _ _ hsh, dCtors_ext.list c12.ext _ _ hcas,
        denoteEList_ext c12.ext _ _ hpf, denoteEList_ext c12.ext _ _ hpf, hmty⟩ k3
    obtain ⟨hMpf, hMmem, hMout⟩ := classMajorOf_shape hF1
    have hdsN : MP.member = none → ∀ x ∈ MP.ds, x.fvarB ≤ pP.nP :=
      fun hn x hx => (hMout hn x hx).2
    have hdsW : ∀ x ∈ MP.ds, Expr.WScoped pP.nP x := by
      intro x hx
      cases hmm : MP.member with
      | some t =>
        rw [hMmem t hmm] at hx
        exact hp x (List.mem_of_mem_take hx)
      | none =>
        obtain ⟨hxa, hfb⟩ := hMout hmm x hx
        rw [ConLeche.Expr.getAppArgs_mkAppN] at hxa
        simp only [ConLeche.Expr.getAppArgs, List.nil_append] at hxa
        obtain ⟨D, hD⟩ := hsc _ List.mem_cons_self x hxa
        exact ConLeche.WScoped.of_fvarsBelow hD (ConLeche.Expr.fvarB_le hfb)
    obtain ⟨u, s4, k4, z4⟩ := bindOk z3
    rw [hnP] at k4
    obtain ⟨c4, ⟨⟩, -, hF2⟩ := targetMajorPins_spec fe hk henv pP.nP m MP
      (fun _ => hdsW) s3 s4 u c3.ok hm k4
    have c14 := (c12.trans c3).trans c4
    obtain ⟨ms, s5, k5, z5⟩ := bindOk z4
    obtain ⟨c5, MsP, ⟨hms, hMsc⟩, hF3⟩ := ih keysP' (fun k hk' => hsc k (List.mem_cons_of_mem _ hk'))
      s4 s5 ms c4.ok ⟨dShape_ext c14.ext _ _ hsh, dCtors_ext.list c14.ext _ _ hcas,
        denoteEList_ext c14.ext _ _ hpf, dClassKey_ext.list c14.ext _ _ hks'⟩ k5
    obtain ⟨rfl, rfl⟩ := pureOk z5
    refine ⟨c14.trans c5, MP :: MsP, ⟨?_, ?_⟩, ?_⟩
    · simp only [List.mapM_cons, dMajor_ext (c4.ext.trans c5.ext) _ _ hm, hms,
        Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    · intro N hN
      rcases List.mem_cons.mp hN with rfl | hN
      · refine ⟨⟨?_, ?_⟩, hdsN, by rw [hMpf, hpl]⟩
        · rw [hMpf, hpl]; exact hp
        · rw [hMpf, hpl]; exact hdsW
      · exact hMsc N hN
    · simp only [ConLeche.classMajors]
      exact FOk.bind hF1 (FOk.seq hF2 (FOk.bind hF3 (FOk.pure _)))

namespace GR

/-- con-leche: none — `mapM`'s accumulator reversed, denoted. -/
theorem mapM_reverse {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {v : List β}, l.mapM f = some v → l.reverse.mapM f = some v.reverse := by
  intro l
  induction l with
  | nil => intro v h; simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | cons a l ih =>
    intro v h
    obtain ⟨b, v', rfl, hb, hv⟩ := mapM_cons_inv h
    simp only [List.reverse_cons, List.mapM_append, ih hv, List.mapM_cons, hb,
      Option.bind_eq_bind, Option.bind_some, List.mapM_nil, Option.pure_def]

/-- con-leche: none — **`List.mapM` of a core-grade step against con-leche's
`mapM` at `FueledM`** (the accumulator loop both sides run). -/
theorem mapMLoop_cspecF {μ : CheckMode} {env : Env} {fe : IFEnv} {α αP β βP : Type}
    (d : EStore → α → Option αP) (hd : DExt d) (dR : EStore → β → Option βP) (hdR : DExt dR)
    (Q : EStore → Prop) (hQ : ∀ {st st' : EStore}, Ext st st' → Q st → Q st')
    (f : α → AM β) (g : αP → FueledM βP)
    (hf : ∀ a aP, CSpecF μ env fe (fun st => Q st ∧ d st a = some aP) (f a)
      (fun st r v => dR st r = some v) (g aP)) :
    ∀ (l : List α) (lP : List αP) (acc : List β) (accP : List βP),
    CSpecF μ env fe (fun st => Q st ∧ l.mapM (d st) = some lP ∧ acc.mapM (dR st) = some accP)
      (List.mapM.loop f l acc) (fun st r v => r.mapM (dR st) = some v)
      (List.mapM.loop g lP accP) := by
  intro l
  induction l with
  | nil =>
    intro lP acc accP s₀ s' r hok hpre hrun
    obtain ⟨-, hl, hacc⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hl
    subst hl
    simp only [List.mapM.loop] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, accP.reverse, mapM_reverse hacc, FOk.pure _⟩
  | cons a l ih =>
    intro lP acc accP s₀ s' r hok hpre hrun
    obtain ⟨hq, hl, hacc⟩ := hpre
    obtain ⟨aP, lP', rfl, ha, hl'⟩ := mapM_cons_inv hl
    simp only [List.mapM.loop] at hrun
    obtain ⟨b, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨c1, bP, hb, hF⟩ := hf a aP s₀ s1 b hok ⟨hq, ha⟩ k1
    obtain ⟨c2, v, hv, hG⟩ := ih lP' (b :: acc) (bP :: accP) s1 s' r c1.ok
      ⟨hQ c1.ext hq, hd.list c1.ext _ _ hl', by
        simp only [List.mapM_cons, hb, hdR.list c1.ext _ _ hacc, Option.bind_eq_bind,
          Option.bind_some, Option.pure_def]⟩ z1
    exact ⟨c1.trans c2, v, hv, by simp only [List.mapM.loop]; exact FOk.bind hF hG⟩

/-- con-leche: none — `mapMLoop_cspecF` from the empty accumulator. -/
theorem mapM_cspecF {μ : CheckMode} {env : Env} {fe : IFEnv} {α αP β βP : Type}
    (d : EStore → α → Option αP) (hd : DExt d) (dR : EStore → β → Option βP) (hdR : DExt dR)
    (Q : EStore → Prop) (hQ : ∀ {st st' : EStore}, Ext st st' → Q st → Q st')
    (f : α → AM β) (g : αP → FueledM βP)
    (hf : ∀ a aP, CSpecF μ env fe (fun st => Q st ∧ d st a = some aP) (f a)
      (fun st r v => dR st r = some v) (g aP)) (l : List α) (lP : List αP) :
    CSpecF μ env fe (fun st => Q st ∧ l.mapM (d st) = some lP)
      (l.mapM f) (fun st r v => r.mapM (dR st) = some v) (lP.mapM g) := by
  intro s₀ s' r hok hpre hrun
  exact mapMLoop_cspecF d hd dR hdR Q hQ f g hf l lP [] [] s₀ s' r hok
    ⟨hpre.1, hpre.2, rfl⟩ hrun

end GR

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:346-353 classesNfs —
**every class with its entries of the table**: the classes stay scoped
(`classesNfsS_sim`). -/
theorem classesNfs_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (formerTys : List EIdx)
    (formerTysP : List Expr) (tbl : List Arena.NestCtorNf) (tblP : List ConLeche.NestCtorNf)
    (hformer : ∀ t ∈ formerTysP, Expr.WScoped 0 t) :
    ∀ (ms : List Arena.TargetMajor) (MsP : List ConLeche.TargetMajor),
    (∀ M ∈ MsP, Cached.TargetMajScoped M) →
    CSpecF μ env fe
      (fun st => dShape st p = some pP ∧ Frontend.denoteEList st formerTys = some formerTysP ∧
        tbl.mapM (dCtorNf st) = some tblP ∧ ms.mapM (dMajor st) = some MsP)
      (Arena.classesNfs μ fe p formerTys tbl ms)
      (fun st r v => r.mapM (dMajor st) = some v ∧ ∀ M ∈ v, Cached.TargetMajScoped M)
      (ConLeche.classesNfs (fueledOpsM μ) env pP formerTysP tblP MsP) := by
  intro ms
  induction ms with
  | nil =>
    intro MsP _ s₀ s' r hok hpre hrun
    obtain ⟨-, -, -, hms⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
    subst hms
    simp only [Arena.classesNfs] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, [], ⟨rfl, fun _ h => nomatch h⟩, by
      simp only [ConLeche.classesNfs]; exact FOk.pure _⟩
  | cons m ms ih =>
    intro MsP hsc s₀ s' r hok hpre hrun
    obtain ⟨hsh, hft, htbl, hms⟩ := hpre
    obtain ⟨MP, MsP', rfl, hm, hms'⟩ := GR.mapM_cons_inv hms
    obtain ⟨hind, hlvls, hds, hnPc, hnIdx, hctors, hmem, -, hpfvs⟩ := dMajor_inv hm
    obtain ⟨hscp, hscd⟩ := hsc MP List.mem_cons_self
    simp only [Arena.classesNfs] at hrun
    obtain ⟨es, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨c1, esP, hes, hF1⟩ := targetMajorNfs_spec fe hk henv p pP formerTys m.pfvs formerTysP
      MP.pfvs m.lvls MP.lvls m.ds MP.ds m.ctors MP.ctors hformer hscp tbl tblP s₀ s1 es hok
      ⟨hsh, hft, hpfvs, hlvls, hds, hctors, htbl⟩ k1
    obtain ⟨rest, s2, k2, z2⟩ := bindOk z1
    obtain ⟨c2, restP, ⟨hrest, hrsc⟩, hF2⟩ := ih MsP' (fun N hN => hsc N (List.mem_cons_of_mem _ hN))
      s1 s2 rest c1.ok ⟨dShape_ext c1.ext _ _ hsh, denoteEList_ext c1.ext _ _ hft,
        dCtorNf_ext.list c1.ext _ _ htbl, dMajor_ext.list c1.ext _ _ hms'⟩ k2
    obtain ⟨rfl, rfl⟩ := pureOk z2
    have c12 := c1.trans c2
    refine ⟨c12, { MP with nfs := esP } :: restP, ⟨?_, ?_⟩, ?_⟩
    · have hm2 : dMajor s'.store { m with nfs := es } = some { MP with nfs := esP } := by
        have h1 := denoteN_ext hind c12.ext
        have h2 := denoteLs_ext hlvls c12.ext
        have h3 := denoteEList_ext c12.ext _ _ hds
        have h4 := dCtors_ext c12.ext _ _ hctors
        have h5 := dCtorNf_ext.list c2.ext _ _ hes
        have h6 := denoteEList_ext c12.ext _ _ hpfvs
        simp only [dMajor, h1, h2, h3, h4, h5, h6, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, hnPc, hnIdx, hmem]
      simp only [List.mapM_cons, hm2, hrest, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def]
    · intro N hN
      rcases List.mem_cons.mp hN with rfl | hN
      · exact ⟨hscp, hscd⟩
      · exact hrsc N hN
    · simp only [ConLeche.classesNfs]
      exact FOk.bind hF1 (FOk.bind hF2 (FOk.pure _))

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:355-362 classFormerTy —
**a class's former type**: a member's own (the `getD` fallback the interned
`.bvar 0`), an outside class's stored former at the class's levels, read
through the index (`IFEnvOK`). -/
theorem classFormerTy_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (cvTas : List IConstantVal) (cvTasP : List ConstantVal) (m : Arena.TargetMajor)
    (mP : ConLeche.TargetMajor) :
    CSpecF μ env fe
      (fun st => cvTas.mapM (Frontend.denoteCV st) = some cvTasP ∧ dMajor st m = some mP)
      (Arena.classFormerTy fe cvTas m) (fun st r v => denoteE st r = some v)
      (ConLeche.classFormerTy (m := FueledM) (mkFEnv env) cvTasP mP) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hcv, hm⟩ := hpre
  obtain ⟨hind, hlvls, -, -, -, -, hmem, -, -⟩ := dMajor_inv hm
  simp only [Arena.classFormerTy] at hrun
  simp only [ConLeche.classFormerTy, ← hmem]
  cases hmm : m.member with
  | some t =>
    rw [hmm] at hrun
    dsimp only at hrun ⊢
    have hj := mapM_option_getElem? (st := s₀.store) hcv t
    rw [List.getD_eq_getElem?_getD]
    revert hrun
    cases hc : cvTas[t]? with
    | none =>
      intro hrun
      rw [hc] at hj
      have : cvTasP[t]? = none := hj
      rw [this, Option.getD_none]
      obtain ⟨p1, hr⟩ := internBVarE_run hok.state hrun
      exact ⟨p1.toCore hok, _, hr, FOk.pure _⟩
    | some cv =>
      intro hrun
      rw [hc] at hj
      obtain ⟨cvP, hcvP, hd⟩ := hj
      rw [hcvP, Option.getD_some]
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      exact ⟨CoreStep.refl hok, _, denoteCV_type hd, FOk.pure _⟩
  | none =>
    rw [hmm] at hrun
    dsimp only at hrun ⊢
    rw [mkFEnv_find?]
    revert hrun
    cases hf : fe.find? m.ind with
    | none =>
      intro hrun
      exact absurd hrun (fun hc => failOk hc)
    | some ci =>
      intro hrun
      obtain ⟨c, hc, he⟩ := find_some_rel hok.ienv hind hf
      rw [he]
      cases ci with
      | indInfo cv caps =>
        obtain ⟨cvP, capsP, hcvP, -, rfl⟩ := denoteCI_indInfo_inv hc
        dsimp only at hrun ⊢
        obtain ⟨c1, hr⟩ := instLPFast_cstep hok (denoteCV_lps hcvP) hlvls (denoteCV_type hcvP) hrun
        exact ⟨c1, _, hr, FOk.pure _⟩
      | _ => exact absurd hrun (fun hc => failOk hc)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:364-387 classConstOk —
**a generated constant, checked**: the guards in the cited order (each exact,
the index read through `IFEnvOK`), then its type inferred and a sort; the
constant is returned as given, closed (`WScoped 0`) and fresh. -/
theorem classConstOk_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (cv : IConstantVal) (cP : ConstantVal) :
    CSpecF μ env fe (fun st => Frontend.denoteCV st cv = some cP)
      (Arena.classConstOk μ fe cv)
      (fun _ r v => r = cv ∧ v = cP ∧ Expr.WScoped 0 cP.type ∧ env.find? cP.name = none)
      (ConLeche.classConstOk (fueledOpsM μ) (mkFEnv env) cP) := by
  intro s₀ s' r hok hcv hrun
  obtain ⟨hnm, hlps, hty⟩ := Core.denoteCV_inv hcv
  simp only [Arena.classConstOk] at hrun
  -- 1. the duplicate-declaration guard
  obtain ⟨hdup, r1⟩ := AM.dguard_ok AM.Never.fail_any hrun
  replace r1 := AM.pure_bind_ok r1
  have hfind : fe.find? cv.name = none := by
    cases hf : fe.find? cv.name with
    | none => rfl
    | some ci => rw [hf] at hdup; exact absurd rfl hdup
  have hfindP : env.find? cP.name = none := IFEnvOK.miss hok.state hok.ienv hnm hfind
  -- 2. the reserved-name guard
  obtain ⟨rs, s2, k2, r2⟩ := bindOk r1
  obtain ⟨p2, hrs⟩ := reservedBasisNames_pstep hok.state hok.pins k2
  obtain ⟨hres, r3⟩ := AM.dguard_ok AM.Never.fail_any r2
  replace r3 := AM.pure_bind_ok r3
  have hresP : ConLeche.reservedBasisNames.contains cP.name = false := by
    rw [← PW.contains_handle_eq p2.ok.wf (denoteN_ext hnm p2.ext) hrs]
    cases hb : rs.contains cv.name with
    | false => rfl
    | true => rw [hb] at hres; exact absurd rfl hres
  -- 3. the reserved-projection-name guard
  obtain ⟨b3, s3, k3, r4⟩ := bindOk r3
  obtain ⟨rfl, hb3⟩ := isProjFnShape_run p2.ok rfl (denoteN_ext hnm p2.ext) k3
  obtain ⟨hproj, r5⟩ := AM.dguard_ok AM.Never.fail_any r4
  replace r5 := AM.pure_bind_ok r5
  have hprojP : cP.name.isProjFnShape = false := by
    rw [← hb3]
    cases hb : b3 with
    | false => rfl
    | true => rw [hb] at hproj; exact absurd rfl hproj
  -- 4. the duplicate-universe-parameter guard
  obtain ⟨hnod, r6⟩ := AM.dunless_ok AM.Never.fail_any r5
  replace r6 := AM.pure_bind_ok r6
  have hnodP : ConLeche.Name.nodup cP.levelParams = true := by
    rw [← nameNodup_spec p2.ok.wf cv.levelParams cP.levelParams
      (denoteNList_ext p2.ext.lss.ls.ns _ _ hlps)]
    exact hnod
  -- 5. the loose-bound-variable guard
  obtain ⟨b5, s5, k5, r7⟩ := bindOk r6
  obtain ⟨p5, rfl⟩ := RC.looseBVarsBoundedFast_pstep p2.ok (denote_ext hty p2.ext) k5
  obtain ⟨hlbb, r8⟩ := AM.dunless_ok AM.Never.fail_any r7
  replace r8 := AM.pure_bind_ok r8
  -- 6. the free-variable guard
  have p25 := p2.trans p5
  obtain ⟨b6, s6, k6, r9⟩ := bindOk r8
  obtain ⟨p6, rfl⟩ := RC.hasFvarFast_pstep p5.ok (denote_ext hty p25.ext) k6
  obtain ⟨hfv, r10⟩ := AM.dguard_ok AM.Never.fail_any r9
  replace r10 := AM.pure_bind_ok r10
  have hfvP : cP.type.hasFvar = false := by
    cases hb : cP.type.hasFvar with
    | false => rfl
    | true => rw [hb] at hfv; exact absurd rfl hfv
  have hws : Expr.WScoped 0 cP.type := ConLeche.Expr.WScoped.of_not_hasFvar hfvP
  have p26 := p25.trans p6
  -- 7. the undeclared-universe-parameter guard
  obtain ⟨b7, s7, k7, r11⟩ := bindOk r10
  obtain ⟨h7st, h7c, h7p, rfl⟩ := allLevelParamsDefined_run p6.ok
    (denoteNList_ext p26.ext.lss.ls.ns _ _ hlps) (denote_ext hty p26.ext) k7
  obtain ⟨hlpd, r12⟩ := AM.dunless_ok AM.Never.fail_any r11
  replace r12 := AM.pure_bind_ok r12
  have p7 : PStep s6 s7 := PStep.of_caches ⟨by rw [h7st]; exact p6.ok.wf⟩
    (by rw [h7st]; exact Ext.refl _) (by rw [h7st]; exact BMExt.refl _) h7c h7p
  have p27 := p26.trans p7
  -- 8. the unresolved-constant guard
  have c7 := p27.toCore hok
  obtain ⟨b8, s8, k8, r13⟩ := bindOk r12
  obtain ⟨h8st, h8c, h8p, rfl⟩ := constsResolveFFast_runR c7.ok.toR
    (denote_ext hty p27.ext) k8
  obtain ⟨hcr, r14⟩ := AM.dunless_ok (AM.Never.bind fun _ => AM.Never.fail_any) r13
  replace r14 := AM.pure_bind_ok r14
  have p8 : PStep s7 s8 := PStep.of_caches ⟨by rw [h8st]; exact p7.ok.wf⟩
    (by rw [h8st]; exact Ext.refl _) (by rw [h8st]; exact BMExt.refl _) h8c h8p
  have c8 := (p27.trans p8).toCore hok
  -- 9. the inference
  obtain ⟨stype, s9, k9, r15⟩ := bindOk r14
  obtain ⟨c9, w, hw, hww, hF9⟩ := infer_crun hk henv c8.ok (denote_ext hty c8.ext) hws k9
  -- 10. the sort test
  obtain ⟨u, s10, k10, r16⟩ := bindOk r15
  obtain ⟨c10, uu, -, hF10⟩ := ensureSort_crun hk henv c9.ok hw hww k10
  obtain ⟨rfl, rfl⟩ := pureOk r16
  refine ⟨(c8.trans c9).trans c10, cP, ⟨rfl, rfl, hws, hfindP⟩, ?_⟩
  simp only [ConLeche.classConstOk, mkFEnv_find?, hfindP, Option.isSome_none,
    Bool.false_eq_true, ↓reduceIte, hresP, hprojP, hnodP, hlbb, hfvP, hlpd,
    constsResolveF_eq, hcr, mkFEnv_env]
  exact FOk.seq (FOk.pure ()) (FOk.seq (FOk.pure ()) (FOk.seq (FOk.pure ()) (FOk.seq
    (FOk.pure ()) (FOk.seq (FOk.pure ()) (FOk.seq (FOk.pure ()) (FOk.seq (FOk.pure ())
      (FOk.seq (FOk.pure ()) (FOk.bind hF9 (FOk.bind hF10 (FOk.pure cP))))))))))

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:389-407 classRecTyOk —
**one recursor's generated type, checked and compared**: the record's member,
rule prefix and major index the generated ones, the generated type checked as
a constant under the record's name and level parameters, defeq to the
stream's checked type (closed, as the cached bridge's `classRecTyOkS_sim`
has it).  The generated constant denotes con-leche's, closed and fresh. -/
theorem classRecTyOk_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (g : Arena.ClassGen) (gP : ConLeche.ClassGen) (k : Nat) (rc : Arena.RecShape)
    (rcP : ConLeche.RecShape) (cvRi : IConstantVal) (cvRiP : ConstantVal) (c : Nat)
    (hRi : Expr.WScoped 0 cvRiP.type) :
    CSpecF μ env fe
      (fun st => dClassGen st g = some gP ∧ dRec st rc = some rcP ∧
        Frontend.denoteCV st cvRi = some cvRiP)
      (Arena.classRecTyOk μ fe g k rc cvRi c)
      (fun st r v => Frontend.denoteCV st r = some v ∧ Expr.WScoped 0 v.type ∧
        env.find? v.name = none)
      (ConLeche.classRecTyOk (fueledOpsM μ) (mkFEnv env) gP k rcP cvRiP c) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hg, hrc, hRiD⟩ := hpre
  obtain ⟨hnP, -, hcls, -, hsl, -, -, -, -⟩ := dClassGen_inv hg
  obtain ⟨hcvR, hrP, hmI, htgt, -⟩ := RC.dRec_inv hrc
  have hsll : g.slots.length = gP.slots.length := (mapM_option_length hsl).symm
  simp only [Arena.classRecTyOk] at hrun
  simp only [ConLeche.classRecTyOk]
  obtain ⟨ci, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, hci⟩ := targetMajorAt_spec g.cls gP.cls c s₀ s1 ci hok.state hok.pins hcls k1
  obtain ⟨-, -, -, -, hnIdx, -, hmem, -, -⟩ := dMajor_inv hci
  obtain ⟨h1, z2⟩ := AM.dunless_ok AM.Never.fail_any z1
  replace z2 := AM.pure_bind_ok z2
  obtain ⟨h2, z3⟩ := AM.dunless_ok AM.Never.fail_any z2
  replace z3 := AM.pure_bind_ok z3
  have h1P : (rcP.tgt == (gP.cls.getD c default).member.getD k) = true := by
    rw [← htgt, ← hmem]; exact h1
  have h2P : (rcP.rP == gP.nP + gP.slots.length &&
      rcP.mI == rcP.rP + (gP.cls.getD c default).nIdx) = true := by
    rw [← hrP, ← hmI, ← hnP, ← hsll, ← hnIdx]; exact h2
  rw [if_pos h1P, if_pos h2P]
  obtain ⟨o, s4, k4, z4⟩ := bindOk z3
  obtain ⟨p4, ho⟩ := classGenRecTy_spec g gP c s1 s4 o p1.ok (PinsOK.ofPStep hok.pins p1)
    (dClassGen_ext p1.ext _ _ hg) k4
  cases o with
  | none => exact absurd z4 (fun hc => failOk hc)
  | some gty =>
    obtain ⟨gtyP, hgty, hgtyd⟩ := ho
    rw [hgty]
    dsimp only at z4
    have p14 := p1.trans p4
    have c14 := p14.toCore hok
    have hcvG : Frontend.denoteCV s4.store ⟨rc.cvR.name, rc.cvR.levelParams, gty⟩ =
        some { rcP.cvR with type := gtyP } := by
      obtain ⟨hnm4, hlps4, -⟩ := Core.denoteCV_inv (dExt_denoteCV p14.ext _ _ hcvR)
      simp only [Frontend.denoteCV, hnm4, hlps4, hgtyd]
    obtain ⟨cvG, s5, k5, z5⟩ := bindOk z4
    obtain ⟨c5, cvGP, ⟨rfl, rfl, hwG, hfrG⟩, hF5⟩ := classConstOk_spec fe hk henv _ _ s4 s5 cvG
      c14.ok hcvG k5
    obtain ⟨b, s6, k6, z6⟩ := bindOk z5
    have c15 := c14.trans c5
    obtain ⟨c6, hF6⟩ := RC.defeq_run (hk.knot env fe henv) c5.ok
      (Core.denoteCV_inv (dExt_denoteCV c15.ext _ _ hRiD)).2.2
      (Core.denoteCV_inv (dExt_denoteCV c5.ext _ _ hcvG)).2.2 hRi hwG k6
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at z6
      exact absurd z6 (fun hc => failOk hc)
    | true =>
      simp only [↓reduceIte] at z6
      obtain ⟨rfl, rfl⟩ := pureOk z6
      refine ⟨c15.trans c6, _, ⟨dExt_denoteCV c6.ext _ _ (dExt_denoteCV c5.ext _ _ hcvG),
        hwG, hfrG⟩, ?_⟩
      exact FOk.bind FOk.unwrapOr (FOk.bind hF5 (FOk.bind (by simpa [mkFEnv_env] using hF6)
        (by simp only [↓reduceIte]
            exact FOk.seq (FOk.pure ()) (FOk.pure _))))

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:409-418 classRecTysOk —
every recursor's generated type, pairwise; the lists running out unevenly
fail on both sides. -/
theorem classRecTysOk_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (g : Arena.ClassGen) (gP : ConLeche.ClassGen) (k : Nat) :
    ∀ (recs : List Arena.RecShape) (recsP : List ConLeche.RecShape) (cvs : List IConstantVal)
      (cvsP : List ConstantVal) (cls : List Nat), (∀ cv ∈ cvsP, Expr.WScoped 0 cv.type) →
    CSpecF μ env fe
      (fun st => dClassGen st g = some gP ∧ recs.mapM (dRec st) = some recsP ∧
        cvs.mapM (Frontend.denoteCV st) = some cvsP)
      (Arena.classRecTysOk μ fe g k recs cvs cls)
      (fun st r v => r.mapM (Frontend.denoteCV st) = some v ∧ ∀ cv ∈ v, env.find? cv.name = none)
      (ConLeche.classRecTysOk (fueledOpsM μ) (mkFEnv env) gP k recsP cvsP cls) := by
  intro recs
  induction recs with
  | nil =>
    intro recsP cvs cvsP cls _ s₀ s' r hok hpre hrun
    obtain ⟨-, hrecs, -⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hrecs
    subst hrecs
    simp only [Arena.classRecTysOk] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, [], ⟨rfl, fun _ h => nomatch h⟩, by
      simp only [ConLeche.classRecTysOk]; exact FOk.pure _⟩
  | cons rc recs ih =>
    intro recsP cvs cvsP cls hw s₀ s' r hok hpre hrun
    obtain ⟨hg, hrecs, hcvs⟩ := hpre
    obtain ⟨rcP, recsP', rfl, hrc, hrecs'⟩ := GR.mapM_cons_inv hrecs
    match cvs, cvsP, cls, hcvs, hw, hrun with
    | [], _, _, _, _, hrun =>
      simp only [Arena.classRecTysOk] at hrun
      exact absurd hrun (fun hc => failOk hc)
    | _ :: _, _, [], _, _, hrun =>
      simp only [Arena.classRecTysOk] at hrun
      exact absurd hrun (fun hc => failOk hc)
    | cvRi :: cvs', cvsP, c :: cs, hcvs, hw, hrun =>
      obtain ⟨cvRiP, cvsP', rfl, hRi, hcvs'⟩ := GR.mapM_cons_inv hcvs
      simp only [Arena.classRecTysOk] at hrun
      obtain ⟨x, s1, k1, z1⟩ := bindOk hrun
      obtain ⟨c1, xP, ⟨hx, -, hfx⟩, hF1⟩ := classRecTyOk_spec fe hk henv g gP k rc rcP cvRi cvRiP c
        (hw _ List.mem_cons_self) s₀ s1 x hok ⟨hg, hrc, hRi⟩ k1
      obtain ⟨xs, s2, k2, z2⟩ := bindOk z1
      obtain ⟨c2, xsP, ⟨hxs, hfxs⟩, hF2⟩ := ih recsP' cvs' cvsP' cs
        (fun cv h => hw cv (List.mem_cons_of_mem _ h)) s1 s2 xs c1.ok
        ⟨dClassGen_ext c1.ext _ _ hg, dRec_ext.list c1.ext _ _ hrecs',
          dExt_denoteCV.list c1.ext _ _ hcvs'⟩ k2
      obtain ⟨rfl, rfl⟩ := pureOk z2
      refine ⟨c1.trans c2, xP :: xsP, ⟨?_, ?_⟩, ?_⟩
      · simp only [List.mapM_cons, dExt_denoteCV c2.ext _ _ hx, hxs, Option.bind_eq_bind,
          Option.bind_some, Option.pure_def]
      · intro cv hcv
        rcases List.mem_cons.mp hcv with rfl | hcv
        · exact hfx
        · exact hfxs cv hcv
      · simp only [ConLeche.classRecTysOk]
        exact FOk.bind hF1 (FOk.bind hF2 (FOk.pure _))

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:441-442 classRuleOk (the
λ-domains) — every domain of a denoting telescope resolves, read through a
correct index. -/
theorem allM_domains_resolve {env : Env} {fe : IFEnv} :
    ∀ (bs : List (EIdx × BinderMeta)) (bsP : List (Expr × BinderMeta)) (s₀ s' : AState)
      (b : Bool), ReadOK env fe s₀ → denoteBinders s₀.store bs = some bsP →
      bs.allM (fun b => Arena.constsResolveFFast fe b.1) s₀ = .ok (b, s') →
      PStep s₀ s' ∧ b = bsP.all (fun b => b.1.constsResolve env) := by
  intro bs
  induction bs with
  | nil =>
    intro bsP s₀ s' b hok hbs hrun
    simp only [denoteBinders, Option.some.injEq] at hbs
    subst hbs
    simp only [List.allM] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok.state, rfl⟩
  | cons x bs ih =>
    intro bsP s₀ s' b hok hbs hrun
    obtain ⟨t, m⟩ := x
    simp only [denoteBinders] at hbs
    cases ht : denoteE s₀.store t with
    | none => rw [ht] at hbs; simp at hbs
    | some tP =>
    cases hr : denoteBinders s₀.store bs with
    | none => rw [ht, hr] at hbs; simp at hbs
    | some rest =>
    rw [ht, hr] at hbs
    obtain rfl := (Option.some.inj hbs).symm
    simp only [List.allM] at hrun
    obtain ⟨c, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, rfl⟩ := constsResolveFFast_pstep hok ht k1
    cases hc : tP.constsResolve env with
    | false =>
      rw [hc] at z1
      obtain ⟨rfl, rfl⟩ := pureOk z1
      exact ⟨p1, by simp only [List.all_cons, hc, Bool.false_and]⟩
    | true =>
      rw [hc] at z1
      obtain ⟨p2, hb⟩ := ih rest s1 s' b (hok.mono p1.ok p1.ext p1.pins)
        (denoteBinders_ext p1.ext _ _ hr) z1
      exact ⟨p1.trans p2, by simp only [List.all_cons, hc, Bool.true_and, hb]⟩

/-- con-leche: none — the binder data of a denoting telescope are the
telescope's (`BinderMeta` is carried verbatim). -/
theorem binders_pw_all (pw : PropWhen) {st : EStore} :
    ∀ {bs : List (EIdx × BinderMeta)} {bsP : List (Expr × BinderMeta)},
      denoteBinders st bs = some bsP →
      (bsP.all fun b => b.2.pw == pw) = (bs.all fun b => b.2.pw == pw)
  | [], bsP, h => by
    simp only [denoteBinders, Option.some.injEq] at h
    subst h; rfl
  | (t, m) :: bs, bsP, h => by
    simp only [denoteBinders] at h
    cases ht : denoteE st t with
    | none => rw [ht] at h; simp at h
    | some tP =>
    cases hr : denoteBinders st bs with
    | none => rw [ht, hr] at h; simp at h
    | some rest =>
    rw [ht, hr] at h
    obtain rfl := (Option.some.inj h).symm
    simp only [List.all_cons, binders_pw_all pw hr]

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:420-446 classRuleOk
con-leche: ConLeche/Cached/CheckerC.lean:98-126 sharedOpsRuleR
**One generated rule, installed as generated**, at the rule-less recursors'
environment `envR` (index `feR`): closed, its level parameters the
recursor's, resolving and inferred there — the flush after the inference
(`sharedOpsRuleR`'s) restores the invariant at `feR` — its λ-telescope `n`
long, its λ-domains resolving at the constructors' environment `env₂` (the
view `feR.restrictTo visT`), annotated with the family's datum.  The rule is
returned as generated. -/
theorem classRuleOk_spec {μ : CheckMode} {envR env₂ : Env} (feR : IFEnv) (visT : Nat)
    (hk : CoreSpec μ Arena.checkFuel) (henvR : EnvWF envR)
    (cvR : IConstantVal) (cvRP : ConstantVal) (pw : PropWhen) (n : Nat) (gen : EIdx)
    (genP : Expr) :
    CSpecF μ envR feR
      (fun st => Frontend.denoteCV st cvR = some cvRP ∧ denoteE st gen = some genP ∧
        IFEnvOKS env₂ (feR.restrictTo visT) st)
      (Arena.classRuleOk μ visT feR cvR pw n gen) (fun st r v => denoteE st r = some v)
      (ConLeche.classRuleOk (fueledOpsM μ) .plain (mkFEnv env₂) (mkFEnv envR) cvRP pw n
        genP) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hcv, hgen, hie₂⟩ := hpre
  obtain ⟨-, hlps, -⟩ := Core.denoteCV_inv hcv
  simp only [Arena.classRuleOk] at hrun
  -- the closedness guards
  obtain ⟨b1, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, rfl⟩ := RC.looseBVarsBoundedFast_pstep hok.state hgen k1
  obtain ⟨hlb, z2⟩ := AM.dunless_ok AM.Never.fail_any z1
  replace z2 := AM.pure_bind_ok z2
  obtain ⟨b2, s2, k2, z3⟩ := bindOk z2
  obtain ⟨p2, rfl⟩ := RC.hasFvarFast_pstep p1.ok (denote_ext hgen p1.ext) k2
  obtain ⟨hfv, z4⟩ := AM.dguard_ok AM.Never.fail_any z3
  replace z4 := AM.pure_bind_ok z4
  have hfvP : genP.hasFvar = false := by
    cases hb : genP.hasFvar with
    | false => rfl
    | true => rw [hb] at hfv; exact absurd rfl hfv
  have hws : Expr.WScoped 0 genP := ConLeche.Expr.WScoped.of_not_hasFvar hfvP
  have p12 := p1.trans p2
  -- the level parameters
  obtain ⟨b3, s3, k3, z5⟩ := bindOk z4
  obtain ⟨h3st, h3c, h3p, rfl⟩ := allLevelParamsDefined_run p2.ok
    (denoteNList_ext p12.ext.lss.ls.ns _ _ hlps) (denote_ext hgen p12.ext) k3
  obtain ⟨hlp, z6⟩ := AM.dunless_ok AM.Never.fail_any z5
  replace z6 := AM.pure_bind_ok z6
  have p3 : PStep s2 s3 := PStep.of_caches ⟨by rw [h3st]; exact p2.ok.wf⟩
    (by rw [h3st]; exact Ext.refl _) (by rw [h3st]; exact BMExt.refl _) h3c h3p
  have c13 := (p12.trans p3).toCore hok
  -- the resolution at `feR`
  obtain ⟨b4, s4, k4, z7⟩ := bindOk z6
  obtain ⟨p4, rfl⟩ := constsResolveFFast_pstep c13.ok.toR (denote_ext hgen c13.ext) k4
  obtain ⟨hcr, z8⟩ := AM.dunless_ok (AM.Never.bind fun _ => AM.Never.fail_any) z7
  replace z8 := AM.pure_bind_ok z8
  have c14 := c13.trans (p4.toCore c13.ok)
  -- the inference at `feR`
  obtain ⟨ty, s5, k5, z9⟩ := bindOk z8
  obtain ⟨c5, w, -, -, hF5⟩ := infer_crun hk henvR c14.ok (denote_ext hgen c14.ext) hws k5
  -- the flush
  obtain ⟨u6, s6, k6, z10⟩ := bindOk z9
  obtain ⟨hok6, hi6, hst6⟩ := (c5.ok.toR).flush (μ := μ) k6
  have c56 : CoreStep μ envR feR s5 s6 := ⟨hok6, by rw [hst6]; exact Ext.refl _, hi6.pins⟩
  have c16 := (c14.trans c5).trans c56
  -- the λ-telescope
  obtain ⟨q, s7, k7, z11⟩ := bindOk z10
  obtain ⟨hs7, hq⟩ := stripLams_pstep hok6.state (denote_ext hgen c16.ext) k7
  rw [hs7] at z11
  cases q with
  | none => exact absurd z11 (fun hc => failOk hc)
  | some q =>
    obtain ⟨rbs, body⟩ := q
    obtain ⟨rbsP, bodyP, hsl, hrbs, -⟩ := denoteBP_someB' hq
    dsimp only at z11
    obtain ⟨b8, s8, k8, z12⟩ := bindOk z11
    have hr6 : ReadOK env₂ (feR.restrictTo visT) s6 :=
      ⟨hok6.state, hok6.pins, hie₂.mono c16.ext _ rfl⟩
    obtain ⟨p8, rfl⟩ := allM_domains_resolve rbs rbsP s6 s8 _ hr6 hrbs k8
    obtain ⟨hdom, z13⟩ := AM.dunless_ok (AM.Never.bind fun _ => AM.Never.fail_any) z12
    replace z13 := AM.pure_bind_ok z13
    have hpwP := binders_pw_all pw hrbs
    have c18 := c16.trans (p8.toCore hok6)
    by_cases hpw : (rbs.all fun b => b.2.pw == pw) = true
    · rw [if_pos hpw] at z13
      obtain ⟨rfl, rfl⟩ := pureOk z13
      refine ⟨c18, genP, denote_ext hgen c18.ext, ?_⟩
      have h1P : (genP.looseBVarsBounded 0 && !genP.hasFvar) = true := by
        simp only [hlb, hfvP, Bool.not_false, Bool.and_self]
      simp only [ConLeche.classRuleOk, h1P, hlp, StructWalkers.plain, constsResolveF_eq, hcr,
        mkFEnv_env, hsl, ↓reduceIte]
      refine FOk.bind hF5 (FOk.bind FOk.unwrapOr ?_)
      dsimp only
      rw [if_pos hdom, hpwP, if_pos hpw]
      exact FOk.pure _
    · rw [if_neg hpw] at z13
      exact absurd z13 (fun hc => failOk hc)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:448-459 classRulesOk — a
recursor's generated rules, one per constructor of its class, the callee the
family's recursor at the landing class (`classRecOf recCls cvGs`). -/
theorem classRulesOk_spec {μ : CheckMode} {envR env₂ : Env} (feR : IFEnv) (visT : Nat)
    (hk : CoreSpec μ Arena.checkFuel) (henvR : EnvWF envR)
    (g : Arena.ClassGen) (gP : ConLeche.ClassGen) (recCls : List Nat)
    (cvGs : List IConstantVal) (cvGsP : List ConstantVal) (cvR : IConstantVal)
    (cvRP : ConstantVal) (pw : PropWhen) (c : Nat) :
    ∀ (xs : List Arena.ClassCtor) (xsP : List ConLeche.ClassCtor),
    CSpecF μ envR feR
      (fun st => dClassGen st g = some gP ∧ cvGs.mapM (Frontend.denoteCV st) = some cvGsP ∧
        Frontend.denoteCV st cvR = some cvRP ∧ xs.mapM (dClassCtor st) = some xsP ∧
        IFEnvOKS env₂ (feR.restrictTo visT) st)
      (Arena.classRulesOk μ visT feR g recCls cvGs cvR pw c xs)
      (fun st r v => Frontend.denoteEList st r = some v)
      (ConLeche.classRulesOk (fueledOpsM μ) .plain (mkFEnv env₂) (mkFEnv envR) gP
        (ConLeche.classRecOf recCls cvGsP) cvRP pw c xsP) := by
  intro xs
  induction xs with
  | nil =>
    intro xsP s₀ s' r hok hpre hrun
    obtain ⟨-, -, -, hxs, -⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hxs
    subst hxs
    simp only [Arena.classRulesOk] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, [], rfl, by simp only [ConLeche.classRulesOk]; exact FOk.pure _⟩
  | cons x xs ih =>
    intro xsP s₀ s' r hok hpre hrun
    obtain ⟨hg, hcvs, hcvR, hxs, hie⟩ := hpre
    obtain ⟨xP, xsP', rfl, hx, hxs'⟩ := GR.mapM_cons_inv hxs
    obtain ⟨hnP, -, -, -, hsl, -, -, -, -⟩ := dClassGen_inv hg
    have hsll : g.slots.length = gP.slots.length := (mapM_option_length hsl).symm
    have hnF := (dClassCtor_inv hx).2.1
    obtain ⟨-, hlps, -⟩ := Core.denoteCV_inv hcvR
    simp only [Arena.classRulesOk] at hrun
    simp only [ConLeche.classRulesOk]
    obtain ⟨rl, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hrl⟩ := paramLevels_spec _ _ s₀ s1 rl hok.state hlps k1
    obtain ⟨o, s2, k2, z2⟩ := bindOk z1
    obtain ⟨p2, ho⟩ := classGenRule_spec g gP recCls cvGs cvGsP rl _ c x xP s1 s2 o p1.ok
      (PinsOK.ofPStep hok.pins p1)
      ⟨dClassGen_ext p1.ext _ _ hg, dClassCtor_ext p1.ext _ _ hx,
        dExt_denoteCV.list p1.ext _ _ hcvs, hrl⟩ k2
    have c12 := (p1.trans p2).toCore hok
    cases o with
    | none => exact absurd z2 (fun hc => failOk hc)
    | some gen =>
      obtain ⟨genP, hgenP, hgen⟩ := ho
      dsimp only at z2
      obtain ⟨r1, s3, k3, z3⟩ := bindOk z2
      rw [hnP, hsll, hnF] at k3
      obtain ⟨c3, r1P, hr1, hF3⟩ := classRuleOk_spec feR visT hk henvR cvR cvRP pw _ gen genP
        s2 s3 r1 c12.ok ⟨dExt_denoteCV c12.ext _ _ hcvR, hgen, hie.mono c12.ext⟩ k3
      have c13 := c12.trans c3
      obtain ⟨rs, s4, k4, z4⟩ := bindOk z3
      obtain ⟨c4, rsP, hrs, hF4⟩ := ih xsP' s3 s4 rs c3.ok
        ⟨dClassGen_ext c13.ext _ _ hg, dExt_denoteCV.list c13.ext _ _ hcvs,
          dExt_denoteCV c13.ext _ _ hcvR, dClassCtor_ext.list c13.ext _ _ hxs',
          hie.mono c13.ext⟩ k4
      obtain ⟨rfl, rfl⟩ := pureOk z4
      refine ⟨c13.trans c4, r1P :: rsP, ?_, ?_⟩
      · simp only [Frontend.denoteEList, denote_ext hr1 c4.ext, hrs]
      · rw [hgenP]
        exact FOk.bind FOk.unwrapOr (FOk.bind hF3 (FOk.bind hF4 (FOk.pure _)))

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:461-470 classRecsRulesOk —
every recursor's generated rules, with its class; the walked lists are the
tails of `cvGs` and `recCls` (the shorter decides). -/
theorem classRecsRulesOk_spec {μ : CheckMode} {envR env₂ : Env} (feR : IFEnv) (visT : Nat)
    (hk : CoreSpec μ Arena.checkFuel) (henvR : EnvWF envR)
    (g : Arena.ClassGen) (gP : ConLeche.ClassGen) (recCls : List Nat) (pw : PropWhen)
    (cvGs : List IConstantVal) (cvGsP : List ConstantVal) :
    ∀ (cvs : List IConstantVal) (cvsP : List ConstantVal) (cs : List Nat),
    CSpecF μ envR feR
      (fun st => dClassGen st g = some gP ∧ cvGs.mapM (Frontend.denoteCV st) = some cvGsP ∧
        cvs.mapM (Frontend.denoteCV st) = some cvsP ∧ IFEnvOKS env₂ (feR.restrictTo visT) st)
      (Arena.classRecsRulesOk μ visT feR g recCls pw cvGs cvs cs)
      (fun st r v => r.mapM (dRecOut st) = some v)
      (ConLeche.classRecsRulesOk (fueledOpsM μ) .plain (mkFEnv env₂) (mkFEnv envR) gP
        (ConLeche.classRecOf recCls cvGsP) pw cvsP cs) := by
  intro cvs
  induction cvs with
  | nil =>
    intro cvsP cs s₀ s' r hok hpre hrun
    obtain ⟨-, -, hcvs, -⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hcvs
    subst hcvs
    simp only [Arena.classRecsRulesOk] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, [], rfl, by simp only [ConLeche.classRecsRulesOk]; exact FOk.pure _⟩
  | cons cvG cvs ih =>
    intro cvsP cs s₀ s' r hok hpre hrun
    obtain ⟨hg, hcvGs, hcvs, hie⟩ := hpre
    obtain ⟨cvGP, cvsP', rfl, hcvG, hcvs'⟩ := GR.mapM_cons_inv hcvs
    cases cs with
    | nil =>
      simp only [Arena.classRecsRulesOk] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      exact ⟨CoreStep.refl hok, [], rfl, by simp only [ConLeche.classRecsRulesOk]; exact FOk.pure _⟩
    | cons c cs =>
      obtain ⟨-, -, hcls, -, -, hctors, -, -, -⟩ := dClassGen_inv hg
      have hxs : (g.ctors.getD c []).mapM (dClassCtor s₀.store) = some (gP.ctors.getD c []) := by
        have hcj := mapM_option_getElem? (st := s₀.store) hctors c
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
      simp only [Arena.classRecsRulesOk] at hrun
      simp only [ConLeche.classRecsRulesOk]
      obtain ⟨rhss, s1, k1, z1⟩ := bindOk hrun
      obtain ⟨c1, rhssP, hrhss, hF1⟩ := classRulesOk_spec feR visT hk henvR g gP recCls cvGs cvGsP
        cvG cvGP pw c _ _ s₀ s1 rhss hok ⟨hg, hcvGs, hcvG, hxs, hie⟩ k1
      obtain ⟨m, s2, k2, z2⟩ := bindOk z1
      obtain ⟨p2, hm⟩ := targetMajorAt_spec g.cls gP.cls c s1 s2 m c1.ok.state c1.ok.pins
        (dMajor_ext.list c1.ext _ _ hcls) k2
      have c12 := c1.trans (p2.toCore c1.ok)
      obtain ⟨rest, s3, k3, z3⟩ := bindOk z2
      obtain ⟨c3, restP, hrest, hF3⟩ := ih cvsP' cs s2 s3 rest c12.ok
        ⟨dClassGen_ext c12.ext _ _ hg, dExt_denoteCV.list c12.ext _ _ hcvGs,
          dExt_denoteCV.list c12.ext _ _ hcvs', hie.mono c12.ext⟩ k3
      obtain ⟨rfl, rfl⟩ := pureOk z3
      refine ⟨c12.trans c3, (cvGP, gP.cls.getD c default, rhssP) :: restP, ?_, ?_⟩
      · have h1 : dRecOut s'.store (cvG, m, rhss) = some (cvGP, gP.cls.getD c default, rhssP) := by
          simp only [dRecOut, dExt_denoteCV c12.ext _ _ hcvG |> dExt_denoteCV c3.ext _ _,
            dMajor_ext c3.ext _ _ hm, denoteEList_ext (p2.ext.trans c3.ext) _ _ hrhss,
            Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        simp only [List.mapM_cons, h1, hrest, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def]
      · exact FOk.bind hF1 (FOk.bind hF3 (FOk.pure _))

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:472-479 classStreamRecs —
**the stream's recursor constants, checked** (`checkConstantVal`): each
denotes con-leche's `checkConstantValF` answer at `fueledOpsM μ`, closed. -/
theorem classStreamRecs_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) :
    ∀ (recs : List Arena.RecShape) (recsP : List ConLeche.RecShape),
    CSpecF μ env fe (fun st => recs.mapM (dRec st) = some recsP)
      (Arena.classStreamRecs μ fe recs)
      (fun st r v => r.mapM (Frontend.denoteCV st) = some v ∧ ∀ cv ∈ v, Expr.WScoped 0 cv.type)
      (ConLeche.classStreamRecs (fueledOpsM μ) (mkFEnv env) recsP) := by
  intro recs
  induction recs with
  | nil =>
    intro recsP s₀ s' r hok hrecs hrun
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hrecs
    subst hrecs
    simp only [Arena.classStreamRecs] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, [], ⟨rfl, fun _ h => nomatch h⟩, by
      simp only [ConLeche.classStreamRecs]; exact FOk.pure _⟩
  | cons rc recs ih =>
    intro recsP s₀ s' r hok hrecs hrun
    obtain ⟨rcP, recsP', rfl, hrc, hrecs'⟩ := GR.mapM_cons_inv hrecs
    have hcvR := (RC.dRec_inv hrc).1
    simp only [Arena.classStreamRecs] at hrun
    obtain ⟨cv, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨c1, cA, F, hcA, hF⟩ := checkConstantVal_bridge hμ hk hok henv hcvR k1
    have hwA : Expr.WScoped 0 cA.type := by
      obtain ⟨-, -, -, -, -, hitf, type, -, -, hann, -, -, -, -, rfl⟩ :=
        ConLeche.checkConstantVal_inv hF
      exact ConLeche.annotateCore_WScoped F _ hann (ConLeche.Expr.WScoped.of_not_hasFvar hitf)
    obtain ⟨cvs, s2, k2, z2⟩ := bindOk z1
    obtain ⟨c2, cvsP, ⟨hcvs, hwcvs⟩, hF2⟩ := ih recsP' s1 s2 cvs c1.ok
      (dRec_ext.list c1.ext _ _ hrecs') k2
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨c1.trans c2, cA :: cvsP, ⟨?_, ?_⟩, ?_⟩
    · simp only [List.mapM_cons, dExt_denoteCV c2.ext _ _ hcA, hcvs, Option.bind_eq_bind,
        Option.bind_some, Option.pure_def]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hwA
      · exact hwcvs x hx
    · simp only [ConLeche.classStreamRecs]
      exact FOk.bind ⟨F, by rw [checkConstantValF_datF, checkConstantValF_eq]; exact hF⟩
        (FOk.bind hF2 (FOk.pure _))

/-! ### The rule-less recursors, pushed and popped (`classFeR`) -/

namespace GR

/-- con-leche: none — two indexes that answer alike: the same list, the same
bound, the same row at every key. -/
def FEq (a b : IFEnv) : Prop :=
  a.env = b.env ∧ a.visibleBelow = b.visibleBelow ∧ ∀ n : NIdx, a.idx[n]? = b.idx[n]?

/-- con-leche: none — `FEq` is reflexive. -/
theorem FEq.refl (a : IFEnv) : FEq a a := ⟨rfl, rfl, fun _ => rfl⟩

/-- con-leche: none — `FEq` is transitive. -/
theorem FEq.trans {a b c : IFEnv} (h₁ : FEq a b) (h₂ : FEq b c) : FEq a c :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, fun n => (h₁.2.2 n).trans (h₂.2.2 n)⟩

/-- con-leche: none — `FEq` indexes answer `find?` alike. -/
theorem FEq.find? {a b : IFEnv} (h : FEq a b) : a.find? = b.find? := by
  funext n
  simp only [IFEnv.find?, h.2.2 n, h.2.1]

/-- con-leche: none — coherence moves along `FEq`. -/
theorem FEq.coh {a b : IFEnv} (h : FEq a b) (hb : IFEnvCoh b) : IFEnvCoh a :=
  ⟨by rw [h.2.1, h.1]; exact hb.1, fun n => by rw [h.2.2 n, h.1]; exact hb.2 n⟩

/-- con-leche: none — a temporary pop respects `FEq`. -/
theorem FEq.popTemp {a b : IFEnv} (h : FEq a b) (n : NIdx) (prev : Option (Nat × IConstantInfo)) :
    FEq (a.popTemp n prev) (b.popTemp n prev) := by
  refine ⟨by simp only [IFEnv.popTemp, h.1], by simp only [IFEnv.popTemp, h.2.1], fun k => ?_⟩
  simp only [IFEnv.popTemp]
  cases prev with
  | none =>
    simp only [Std.HashMap.getElem?_erase]
    split <;> simp [h.2.2 k]
  | some r =>
    simp only [Std.HashMap.getElem?_insert]
    split <;> simp [h.2.2 k]

/-- con-leche: none — **a pop undoes its push** (`IFEnv.popTemp`'s purpose, the
port's `ifenv_pop_temp`): the list, the bound and every row as before. -/
theorem popTemp_push (fe : IFEnv) (ci : IConstantInfo) :
    FEq ((fe.push ci).popTemp ci.name fe.idx[ci.name]?) fe := by
  refine ⟨rfl, by simp only [IFEnv.popTemp, IFEnv.push]; omega, fun k => ?_⟩
  simp only [IFEnv.popTemp, IFEnv.push]
  cases hprev : fe.idx[ci.name]? with
  | none =>
    simp only [Std.HashMap.getElem?_erase, Std.HashMap.getElem?_insert]
    by_cases hk : (ci.name == k) = true
    · have : ci.name = k := eq_of_beq hk
      subst this
      simp [hprev]
    · simp [hk]
  | some r =>
    simp only [Std.HashMap.getElem?_insert]
    by_cases hk : (ci.name == k) = true
    · have : ci.name = k := eq_of_beq hk
      subst this
      simp [hprev]
    · simp [hk]

/-- con-leche: none — **the pops restore the index the pushes started from**:
`classFeR.go`'s recorded rows, popped in reverse (`foldr`), give back an index
answering exactly as the input. -/
theorem classFeR_go_pop (p : Arena.BlockShape) :
    ∀ (l : List (IConstantVal × Nat)) (m : Nat) (fe : IFEnv)
      (prevs : List (NIdx × Option (Nat × IConstantInfo))),
      ∃ news, (Arena.classFeR.go p m l fe prevs).2 = prevs ++ news ∧
        FEq (news.foldr (fun (x : NIdx × Option (Nat × IConstantInfo)) acc =>
          acc.popTemp x.1 x.2) (Arena.classFeR.go p m l fe prevs).1) fe
  | [], m, fe, prevs => ⟨[], by simp [Arena.classFeR.go], FEq.refl _⟩
  | (cv, c) :: rest, m, fe, prevs => by
    simp only [Arena.classFeR.go]
    obtain ⟨news, hn, hf⟩ := classFeR_go_pop p rest (m + 1)
      (fe.push (.recInfo cv (p.majorIdxAt m) (p.rulePrefixAt m) []))
      (prevs ++ [(cv.name, fe.idx[cv.name]?)])
    refine ⟨(cv.name, fe.idx[cv.name]?) :: news, by rw [hn]; simp, ?_⟩
    simp only [List.foldr_cons]
    exact (hf.popTemp _ _).trans (popTemp_push fe (.recInfo cv _ _ []))

/-- con-leche: none — the whole pop, from `go`'s empty record. -/
theorem classFeR_pop (p : Arena.BlockShape) (cvGs : List IConstantVal) (recCls : List Nat)
    (fe : IFEnv) :
    FEq ((Arena.classFeR p cvGs recCls fe).2.foldr
      (fun (x : NIdx × Option (Nat × IConstantInfo)) acc => acc.popTemp x.1 x.2)
      (Arena.classFeR p cvGs recCls fe).1) fe := by
  obtain ⟨news, hn, hf⟩ := classFeR_go_pop p (cvGs.zip recCls) 0 fe []
  simp only [Arena.classFeR]
  rw [hn, List.nil_append]
  exact hf

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:545-549 classFeR
con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:338-346 consBlockRecsBare —
**the pushed index is the rule-less recursors' environment's**: every push a
value row whose denotation is con-leche's cons, so the index spec and the
coherence survive (`IFEnvOK.push`, `IFEnvCoh.push`). -/
theorem classFeR_go_ok {s : AState} (hst : StateOK s) (p : Arena.BlockShape)
    (pP : ConLeche.BlockShape) (hsh : dShape s.store p = some pP) (f : Nat → Nat) :
    ∀ (cvs : List IConstantVal) (cvsP : List ConstantVal) (rc : List Nat) (m : Nat)
      (fe : IFEnv) (env : Env) (prevs : List (NIdx × Option (Nat × IConstantInfo))),
      IFEnvOK env fe s → IFEnvCoh fe → cvs.mapM (Frontend.denoteCV s.store) = some cvsP →
      IFEnvOK (consBlockRecsBare pP m ((cvsP.zip rc).map fun x => (x.1, f x.2)) env)
          (Arena.classFeR.go p m (cvs.zip rc) fe prevs).1 s ∧
        IFEnvCoh (Arena.classFeR.go p m (cvs.zip rc) fe prevs).1
  | [], cvsP, rc, m, fe, env, prevs, hie, hcoh, hcvs => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hcvs
    subst hcvs
    exact ⟨hie, hcoh⟩
  | cv :: cvs, cvsP, [], m, fe, env, prevs, hie, hcoh, hcvs => by
    obtain ⟨cvP, cvsP', rfl, -, -⟩ := mapM_cons_inv hcvs
    exact ⟨hie, hcoh⟩
  | cv :: cvs, cvsP, c :: rc, m, fe, env, prevs, hie, hcoh, hcvs => by
    obtain ⟨cvP, cvsP', rfl, hcv, hcvs'⟩ := mapM_cons_inv hcvs
    obtain ⟨hmI, hrP⟩ := RC.recAt_eq hsh m
    have hci : Frontend.denoteCI s.store (.recInfo cv (p.majorIdxAt m) (p.rulePrefixAt m) []) =
        some (.recInfo cvP (pP.majorIdxAt m) (pP.rulePrefixAt m) []) := by
      simp only [Frontend.denoteCI, hcv, hmI, hrP]; rfl
    have hie' := hie.push hst hcoh (fun t h => by cases h) hci
    simp only [List.zip_cons_cons, List.map_cons, Arena.classFeR.go, consBlockRecsBare]
    exact classFeR_go_ok hst p pP hsh f cvs cvsP' rc (m + 1) _ _ _ hie' (hcoh.push _) hcvs'

/-- con-leche: none — **the constructors' view stays put**: the pushed names
fresh at the view `fe.restrictTo k`, every push lands above the bound
(`RC.restrictTo_push_find?`). -/
theorem classFeR_go_view (p : Arena.BlockShape) (k : Nat) :
    ∀ (l : List (IConstantVal × Nat)) (m : Nat) (fe : IFEnv)
      (prevs : List (NIdx × Option (Nat × IConstantInfo))),
      k ≤ fe.visibleBelow → (∀ x ∈ l, (fe.restrictTo k).find? x.1.name = none) →
      ((Arena.classFeR.go p m l fe prevs).1.restrictTo k).find? = (fe.restrictTo k).find? := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _; rfl
  | cons x rest ih =>
    intro m fe prevs hk hfr
    obtain ⟨cv, c⟩ := x
    simp only [Arena.classFeR.go]
    have hnone : (fe.restrictTo k).find?
        (IConstantInfo.recInfo cv (p.majorIdxAt m) (p.rulePrefixAt m) []).name = none :=
      hfr (cv, c) List.mem_cons_self
    have hv := RC.restrictTo_push_find? hk hnone
    rw [ih (m + 1) _ _ (by simp only [IFEnv.push]; omega)
      (fun x hx => by rw [hv]; exact hfr x (List.mem_cons_of_mem _ hx)), hv]

end GR

/-! ### The stage, assembled -/

namespace GR

/-- con-leche: none — the constants' types of a denoting list denote. -/
theorem types_denote {st : EStore} :
    ∀ {cvs : List IConstantVal} {cvsP : List ConstantVal},
      cvs.mapM (Frontend.denoteCV st) = some cvsP →
      Frontend.denoteEList st (cvs.map (·.type)) = some (cvsP.map (·.type))
  | [], _, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | cv :: cvs, _, h => by
    obtain ⟨cP, cvsP', rfl, hc, hcs⟩ := mapM_cons_inv h
    simp only [List.map_cons, Frontend.denoteEList, denoteCV_type hc, types_denote hcs]

/-- con-leche: none — the outside-class test reads the verbatim member field. -/
theorem any_member_isNone {st : EStore} :
    ∀ {ms : List Arena.TargetMajor} {MsP : List ConLeche.TargetMajor},
      ms.mapM (dMajor st) = some MsP →
      ms.any (·.member.isNone) = MsP.any (·.member.isNone)
  | [], _, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | m :: ms, _, h => by
    obtain ⟨mP, MsP', rfl, hm, hms⟩ := mapM_cons_inv h
    simp only [List.any_cons, (dMajor_inv hm).2.2.2.2.2.2.1, any_member_isNone hms]

/-- con-leche: none — a denoting list of lists has the same total length. -/
theorem sum_lengths {α β : Type} {f : α → Option β} :
    ∀ {xss : List (List α)} {yss : List (List β)},
      xss.mapM (fun xs => xs.mapM f) = some yss →
      (xss.map List.length).sum = (yss.map List.length).sum
  | [], _, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | xs :: xss, _, h => by
    obtain ⟨ys, yss', rfl, hx, hxs⟩ := mapM_cons_inv h
    simp only [List.map_cons, List.sum_cons, mapM_option_length hx, sum_lengths hxs]

/-- con-leche: none — a member of a denoting list has a denoted partner. -/
theorem mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ∀ x ∈ xs, ∃ y ∈ ys, f x = some y
  | [], _, _, _, hx => nomatch hx
  | a :: as, _, h, x, hx => by
    obtain ⟨b, bs, rfl, hb, hbs⟩ := mapM_cons_inv h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, List.mem_cons_self, hb⟩
    · obtain ⟨y, hy, hfy⟩ := mapM_mem hbs x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

/-- con-leche: none — an index MISS from an environment miss at a denoting
name (the contrapositive of `IFEnvOK.hit`). -/
theorem find_none_of_env {env : Env} {fe : IFEnv} {s : AState} (h : IFEnvOK env fe s)
    {n : NIdx} {nm : ConLeche.Name} (hn : denoteN s.store.ns n = some nm)
    (he : env.find? nm = none) : fe.find? n = none := by
  cases hf : fe.find? n with
  | none => rfl
  | some ci =>
    obtain ⟨c, -, hc⟩ := find_some_rel h hn hf
    rw [he] at hc; exact nomatch hc

end GR

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:551-593 genRecCheck
con-leche: ConLeche/Cached/CheckerC.lean:128-134 shadowOpsC
**THEOREM 1 for the GENERATED recursor stage**, at the constructors'
environment `env₂` (index `fe₂`), on the pass's classes (`ClassMajScoped`)
and table: an accepting twin run answers con-leche's `genRecCheck` at
`ShadowOps.ofOps (fueledOpsM μ)` — the output family denotes con-leche's,
every output recursor is fresh in `env₂`, and the returned index answers
exactly as `fe₂` (the pushes popped: same list, same bound, same row at every
key).  The rule stage's knot calls run at the rule-less recursors'
environment (`consBlockRecsBare`, well formed by `envWF_consBlockRecsBare`);
the flushes restore the invariant at whichever index the state reads, and the
last one leaves `CheckOK μ env₂ fe₂` (the `CoreStep` frame). -/
theorem genRecCheck_spec {μ : CheckMode} {env₂ : Env} (fe₂ : IFEnv)
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (henv₂ : EnvWF env₂)
    (hcoh : IFEnvCoh fe₂) (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (nestedBit : Bool)
    (params : List EIdx) (paramsP : List Expr) (tbl : List Arena.NestCtorNf)
    (tblP : List ConLeche.NestCtorNf) (rd : Arena.ClassRead) (rdP : ConLeche.ClassRead)
    (ms : List Arena.TargetMajor) (MsP : List ConLeche.TargetMajor)
    (cvTas : List IConstantVal) (cvTasP : List ConstantVal) (block : List IConstantInfo)
    (blockP : List ConstantInfo)
    (hMs : ∀ M ∈ MsP, Cached.ClassMajScoped pP.nP M) (hT : ∀ cv ∈ cvTasP, Expr.WScoped 0 cv.type) :
    CSpecF μ env₂ fe₂
      (fun st => dShape st p = some pP ∧ Frontend.denoteEList st params = some paramsP ∧
        tbl.mapM (dCtorNf st) = some tblP ∧ dClassRead st rd = some rdP ∧
        ms.mapM (dMajor st) = some MsP ∧ cvTas.mapM (Frontend.denoteCV st) = some cvTasP ∧
        Frontend.denoteCIList st block = some blockP)
      (Arena.genRecCheck μ fe₂ p nestedBit params tbl rd ms cvTas block)
      (fun st r v => r.2.mapM (dRecOut st) = some v ∧ (∀ t ∈ v, env₂.find? t.1.name = none) ∧
        GR.FEq r.1 fe₂)
      (ConLeche.genRecCheck (ShadowOps.ofOps (fueledOpsM μ)) (mkFEnv env₂) pP nestedBit paramsP
        tblP rdP MsP cvTasP blockP) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hsh, hpar, htbl, hrd, hms, hcvT, hblk⟩ := hpre
  simp only [Arena.genRecCheck] at hrun
  obtain ⟨-, -, hnP, -, -, hlarge, -⟩ := RC.dShape_inv hsh
  have hk' := BlockShape.k_spec hsh
  have hrecs := (RC.dShape_inv hsh).2.1
  -- the records' pins
  obtain ⟨u0, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, hF1⟩ := targetRecPins_spec p pP block blockP s₀ s1 u0 hok.state hok.pins
    ⟨hsh, hblk⟩ k1
  have c1 := p1.toCore hok
  -- the stream's recursor types
  obtain ⟨cvRis, s2, k2, z2⟩ := bindOk z1
  obtain ⟨c2, cvRisP, ⟨hcvRis, hwRis⟩, hF2⟩ := classStreamRecs_spec fe₂ hμ hk henv₂ p.recs
    pP.recs s1 s2 cvRis c1.ok (dRec_ext.list c1.ext _ _ hrecs) k2
  have c12 := c1.trans c2
  -- the elimination guard
  obtain ⟨hk0, z3⟩ := AM.dguard_ok AM.Never.fail_any z2
  replace z3 := AM.pure_bind_ok z3
  have hkP : 0 < pP.k := by
    rw [← hk']; simp only [beq_iff_eq] at hk0; omega
  have hany := GR.any_member_isNone (dMajor_ext.list c12.ext _ _ hms)
  by_cases hL : p.large = true
  case' pos =>
    rw [if_pos hL] at z3
    obtain ⟨la, s3, k3, z4⟩ := bindOk z3
    obtain ⟨c3, rfl⟩ := blockLargeElimAllowed_cspec fe₂ p pP _ s2 s3 la c12.ok
      (dShape_ext c12.ext _ _ hsh) k3
    obtain ⟨hla, z4⟩ := AM.dunless_ok AM.Never.fail_any z4
    replace z4 := AM.pure_bind_ok z4
    have hcond : (pP.large && !ConLeche.blockLargeElimAllowed pP
        (nestedBit || MsP.any (·.member.isNone))) = false := by
      rw [← hany]; simp [hla]
    have c13 := c12.trans c3
    have hcvRis3 := dExt_denoteCV.list c3.ext _ _ hcvRis
  case' neg =>
    rw [if_neg hL] at z3
    have hcond : (pP.large && !ConLeche.blockLargeElimAllowed pP
        (nestedBit || MsP.any (·.member.isNone))) = false := by
      rw [← hlarge]; simp only [Bool.not_eq_true] at hL; simp [hL]
    generalize hs3 : s2 = s3 at z3
    have c13 : CoreStep μ env₂ fe₂ s₀ s3 := hs3 ▸ c12
    have hcvRis3 : cvRis.mapM (Frontend.denoteCV s3.store) = some cvRisP := hs3 ▸ hcvRis
    have z4 := AM.pure_bind_ok z3
  all_goals
    have hformer : ∀ t ∈ cvTasP.map (·.type), Expr.WScoped 0 t := by
      intro t ht
      obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp ht
      exact hT cv hcv
    have hMsT : ∀ M ∈ MsP, Cached.TargetMajScoped M := fun M hM => (hMs M hM).1
    -- every class's table entries
    obtain ⟨ms2, s4, k4, z5⟩ := bindOk z4
    obtain ⟨c4, Ms2P, ⟨hms2, hMs2⟩, hF4⟩ := classesNfs_spec fe₂ hk henv₂ p pP _ _ tbl tblP hformer
      ms MsP hMsT s3 s4 ms2 c13.ok
      ⟨dShape_ext c13.ext _ _ hsh, GR.types_denote (dExt_denoteCV.list c13.ext _ _ hcvT),
        dCtorNf_ext.list c13.ext _ _ htbl, dMajor_ext.list c13.ext _ _ hms⟩ k4
    have c14 := c13.trans c4
    -- the generator's constructors
    obtain ⟨ctors, s5, k5, z6⟩ := bindOk z5
    obtain ⟨c5, ctorsP, hctors, hF5⟩ := classesCtors_spec fe₂ hk henv₂ p pP _ _ rd rdP ms2 Ms2P
      hformer hMs2 ms2 Ms2P 0 s4 s5 ctors c4.ok
      ⟨dShape_ext c14.ext _ _ hsh, GR.types_denote (dExt_denoteCV.list c14.ext _ _ hcvT),
        dClassRead_ext c14.ext _ _ hrd, hms2, hms2⟩ k5
    have c15 := c14.trans c5
    -- no minor premise beyond the constructors
    obtain ⟨hminor, z7⟩ := AM.dunless_ok AM.Never.fail_any z6
    replace z7 := AM.pure_bind_ok z7
    have hsl : rd.slots.mapM (dSlot s₀.store) = some rdP.slots := by
      simp only [dClassRead, Option.map_eq_some_iff] at hrd
      obtain ⟨q, hq, rfl⟩ := hrd
      exact hq
    have hrc : rd.recCls = rdP.recCls := by
      simp only [dClassRead, Option.map_eq_some_iff] at hrd
      obtain ⟨q, hq, rfl⟩ := hrd
      rfl
    have hminorP : ((rdP.slots.filter ConLeche.ClassSlot.isMinor).length ==
        (ctorsP.map List.length).sum) = true := by
      rw [← isMinor_count hsl, ← GR.sum_lengths hctors]; exact hminor
    -- the classes' formers
    obtain ⟨fTC, s6, k6, z8⟩ := bindOk z7
    obtain ⟨c6, fTCP, hfTC, hF6⟩ := GR.mapM_cspecF dMajor dMajor_ext (fun st e => denoteE st e)
      dExt_denoteE (fun st => cvTas.mapM (Frontend.denoteCV st) = some cvTasP)
      (fun hx h => dExt_denoteCV.list hx _ _ h) (Arena.classFormerTy fe₂ cvTas)
      (ConLeche.classFormerTy (m := FueledM) (mkFEnv env₂) cvTasP)
      (fun m mP s₀ s' r hok hpre hrun => classFormerTy_spec fe₂ cvTas cvTasP m mP s₀ s' r hok
        ⟨hpre.1, hpre.2⟩ hrun) ms2 Ms2P s5 s6 fTC c5.ok
      ⟨dExt_denoteCV.list c15.ext _ _ hcvT, dMajor_ext.list c5.ext _ _ hms2⟩ k6
    have c16 := c15.trans c6
    -- the elimination level and the binder datum
    obtain ⟨elim, s7, k7, z9⟩ := bindOk z8
    obtain ⟨p7, helim⟩ := structElimLevel_spec p.elim pP.elim p.large s6 s7 elim c6.ok.state
      ((RC.dShape_inv (dShape_ext c16.ext _ _ hsh)).2.2.2.1) k7
    obtain ⟨bm, s8, k8, z10⟩ := bindOk z9
    have c17 := c16.trans (p7.toCore c6.ok)
    obtain ⟨p8, rfl⟩ := classGenBm_spec elim _ s7 s8 bm c17.ok.state c17.ok.caches.readL helim k8
    have c18 := c17.trans (p8.toCore c17.ok)
    rw [hlarge] at helim
    -- the generator's record
    have hg0 : dClassGen s8.store (⟨p.nP, params, ms2, fTC, rd.slots, ctors, elim,
          ⟨Level.zeronessOf (ConLeche.structElimLevel pP.elim p.large)⟩, []⟩ : Arena.ClassGen) =
        some ⟨pP.nP, paramsP, Ms2P, fTCP, rdP.slots, ctorsP,
          ConLeche.structElimLevel pP.elim pP.large, []⟩ := by
      have e1 := denoteEList_ext c18.ext _ _ hpar
      have e2 := dMajor_ext.list (c5.ext.trans (c6.ext.trans (p7.ext.trans p8.ext))) _ _ hms2
      have e3 := denoteEList_ext (p7.ext.trans p8.ext) _ _ (mapM_denoteE hfTC)
      have e4 := dSlot_ext.list c18.ext _ _ hsl
      have e5 := dClassCtors_ext (c6.ext.trans (p7.ext.trans p8.ext)) _ _ hctors
      have e6 := denoteL_ext helim p8.ext
      simp only [dClassGen, e1, e2, e3, e4, e5, e6, denoteBinders, hnP, hlarge,
        Option.bind_eq_bind, Option.bind_some, Option.pure_def, if_true]
    -- the prefix
    obtain ⟨o, s9, k9, z11⟩ := bindOk z10
    obtain ⟨p9, ho⟩ := ClassGen.prefixBinders_spec _ _ s8 s9 o c18.ok.state c18.ok.pins hg0 k9
    have c19 := c18.trans (p9.toCore c18.ok)
    cases o with
    | none => exact absurd z11 (fun hc => failOk hc)
    | some pre =>
    obtain ⟨preP, hpreP, hpre⟩ := ho
    dsimp only at z11
    have hg := dClassGen_pre (dClassGen_ext p9.ext _ _ hg0) hpre
    -- the generated types
    obtain ⟨cvGs, s10, k10, z12⟩ := bindOk z11
    rw [hk'] at k10
    obtain ⟨c10, cvGsP, ⟨hcvGs, hfrG⟩, hF10⟩ := classRecTysOk_spec fe₂ hk henv₂ _ _ pP.k p.recs
      pP.recs cvRis cvRisP rd.recCls hwRis s9 s10 cvGs c19.ok
      ⟨hg, dRec_ext.list c19.ext _ _ hrecs,
        dExt_denoteCV.list ((c4.trans c5).trans (c6.trans ((p7.toCore c6.ok).trans
          ((p8.toCore c17.ok).trans (p9.toCore c18.ok))))).ext _ _ hcvRis3⟩ k10
    have c110 := c19.trans c10
    -- the rule-less recursors' environment
    have hrecCls : rd.recCls = rdP.recCls := hrc
    have hfeR := GR.classFeR_go_ok c10.ok.state p pP (dShape_ext c110.ext _ _ hsh)
      (fun c => (Ms2P.getD c default).nIdx) cvGs cvGsP rd.recCls 0 fe₂ env₂ []
      (hok.ienv.mono c110.ext) hcoh hcvGs
    obtain ⟨F10, hF10'⟩ := id hF10
    rw [classRecTysOk_datF] at hF10'
    obtain ⟨hlenG, hallG⟩ := classRecTysOk_run hF10'
    have henvR : EnvWF (consBlockRecsBare pP 0
        ((cvGsP.zip rd.recCls).map fun x => (x.1, (Ms2P.getD x.2 default).nIdx)) env₂) := by
      refine ConLeche.Cached.envWF_consBlockRecsBare henv₂ fun c hc => ?_
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
      obtain ⟨i, hi⟩ := List.getElem?_of_mem (List.of_mem_zip hx).1
      have hil : i < pP.recs.length := by
        rw [← hlenG]; exact (List.getElem?_eq_some_iff.mp hi).1
      obtain ⟨c, cvG, -, hcvG, ⟨R⟩⟩ := hallG i _ (List.getElem?_eq_getElem hil)
      rw [hi] at hcvG
      obtain rfl := Option.some.inj hcvG
      exact classConstOk_typeWF R.hcv
    -- the constructors' view, inside the pushed index
    have hview : ((Arena.classFeR p cvGs rd.recCls fe₂).1.restrictTo fe₂.visibleBelow).find? =
        fe₂.find? := by
      simp only [Arena.classFeR]
      rw [GR.classFeR_go_view p fe₂.visibleBelow _ 0 fe₂ [] (Nat.le_refl _)]
      · rfl
      · intro x hx
        obtain ⟨cP, hcP, hd⟩ := GR.mapM_mem hcvGs x.1 (List.of_mem_zip hx).1
        exact GR.find_none_of_env (hok.ienv.mono c110.ext) (ConRon.Bridge.denoteCV_name hd)
          (hfrG cP hcP)
    have hie2R : IFEnvOK env₂ ((Arena.classFeR p cvGs rd.recCls fe₂).1.restrictTo
        fe₂.visibleBelow) s10 := RC.IFEnvOK.of_find? (hok.ienv.mono c110.ext) hview
    -- the flush into the rule-less recursors' environment
    obtain ⟨u11, s11, k11, z13⟩ := bindOk z12
    obtain ⟨hok11, hi11, hst11⟩ := (⟨c10.ok.state, c10.ok.pins, hfeR.1⟩ :
      ReadOK _ (Arena.classFeR p cvGs rd.recCls fe₂).1 s10).flush (μ := μ) k11
    -- the rules
    obtain ⟨out, s12, k12, z14⟩ := bindOk z13
    obtain ⟨c12', outP, hout, hF12⟩ := classRecsRulesOk_spec _ fe₂.visibleBelow hk henvR _ _
      rd.recCls _ cvGs cvGsP cvGs cvGsP rd.recCls s11 s12 out hok11
      ⟨by rw [hst11]; exact dClassGen_ext c10.ext _ _ hg, by rw [hst11]; exact hcvGs,
        by rw [hst11]; exact hcvGs, by rw [hst11]; exact hie2R.toS⟩ k12
    -- the flush back
    obtain ⟨u13, s13, k13, z15⟩ := bindOk z14
    have hext12 : Ext s₀.store s12.store := c110.ext.trans (by rw [← hst11]; exact c12'.ext)
    have hpins12 : s12.pins = s₀.pins := by
      rw [c12'.pins, hi11.pins, c110.pins]
    obtain ⟨hok13, hi13, hst13⟩ := (⟨c12'.ok.state, by
      exact hok.pins.mono hext12 hpins12, hok.ienv.mono hext12⟩ : ReadOK env₂ fe₂ s12).flush
      (μ := μ) k13
    obtain ⟨hr15, hs15⟩ := pureOk z15
    subst hr15
    rw [← hs15] at hok13 hi13 hst13
    have hframe : CoreStep μ env₂ fe₂ s₀ s' :=
      ⟨hok13, by rw [hst13]; exact hext12, by rw [hi13.pins, hpins12]⟩
    have hFOk : FOk (ConLeche.genRecCheck (ShadowOps.ofOps (fueledOpsM μ)) (mkFEnv env₂) pP
        nestedBit paramsP tblP rdP MsP cvTasP blockP) outP := by
      simp only [ConLeche.genRecCheck, ShadowOps.ofOps, mkFEnv_env]
      refine FOk.bind hF1 (FOk.bind hF2 ?_)
      rw [if_pos hkP, hcond]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine FOk.bind hF4 (FOk.bind hF5 ?_)
      rw [if_pos hminorP]
      refine FOk.bind hF6 ?_
      rw [hpreP]
      rw [hrc] at hF10
      refine FOk.bind FOk.unwrapOr (FOk.bind hF10 (FOk.seq (FOk.pure ()) ?_))
      have hfeReq : ConLeche.classFeR pP Ms2P cvGsP rdP.recCls (mkFEnv env₂) =
          mkFEnv (consBlockRecsBare pP 0
            ((cvGsP.zip rdP.recCls).map fun x => (x.1, (Ms2P.getD x.2 default).nIdx)) env₂) := by
        simp only [ConLeche.classFeR, consBlockRecsBareF_mkFEnv]
      rw [hfeReq]
      rw [hlarge, hrc] at hF12
      exact FOk.bind hF12 (FOk.seq (FOk.pure ()) (FOk.pure _))
    refine ⟨hframe, outP, ⟨by rw [hst13]; exact hout, ?_, GR.classFeR_pop p cvGs rd.recCls fe₂⟩,
      hFOk⟩
    obtain ⟨F, hF⟩ := hFOk
    rw [genRecCheck_datF] at hF
    exact genRecCheck_out_fresh hF

/-! ## The classes, read and checked (the pass) -/

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:27 CheckerOps.annotate — the
knot's annotation in run form, its answer an `FOk` of `fueledOpsM`'s. -/
theorem annotate_crun {μ : CheckMode} {env : Env} {fe : IFEnv}
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    {s s' : AState} {d : Nat} {e r : EIdx} {eP : Expr}
    (hok : CheckOK μ env fe s) (he : denoteE s.store e = some eP)
    (hw : Expr.WScoped d eP)
    (hrun : Arena.annotateCore μ fe Arena.checkFuel d e s = .ok (r, s')) :
    CoreStep μ env fe s s' ∧ ∃ w, denoteE s'.store r = some w ∧ Expr.WScoped d w ∧
      FOk ((fueledOpsM μ).annotate env d eP) w := by
  obtain ⟨h1, h2, h3, v, hv, hwv, hF⟩ := AM.of_run (P := fun u => u = s)
    (Q := fun r u => CheckOK μ env fe u ∧ Ext s.store u.store ∧ u.pins = s.pins ∧
      Core.SimE (ConLeche.annotateCore μ env) d eP u.store r)
    rfl hrun ((hk.knot env fe henv).annotate s d e eP hok he hw)
  exact ⟨⟨h1, h2, h3⟩, v, hv, hwv, FOk.annotate hF⟩

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:481-484 classKeyCanon —
a class key moved to the canonical parameter variables. -/
theorem classKeyCanon_spec (params : List EIdx) (paramsP : List Expr) (k : Arena.ClassKey)
    (kP : ConLeche.ClassKey) :
    PSpecP (fun st => Frontend.denoteEList st params = some paramsP ∧ dClassKey st k = some kP)
      (Arena.classKeyCanon params k) (fun st r => dClassKey st r = some
        (ConLeche.classKeyCanon paramsP kP)) := by
  intro s₀ s' r hok hp hpre hrun
  obtain ⟨hpar, hk⟩ := hpre
  simp only [dClassKey, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hk
  obtain ⟨ind, hind, lvls, hlvls, ds, hds, rfl⟩ := hk
  simp only [Arena.classKeyCanon] at hrun
  obtain ⟨ds2, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, hds2⟩ := mapM_RE_P (fun st => Frontend.denoteEList st params = some paramsP)
    (fun hx h => denoteEList_ext hx _ _ h)
    (fun e eP s₀ s' r hok hp hpre hrun =>
      targetCanonParams_spec params paramsP e eP s₀ s' r hok hp hpre hrun)
    k.ds ds s₀ s1 ds2 hok hp ⟨hpar, hds⟩ k1
  obtain ⟨rfl, rfl⟩ := pureOk z1
  refine ⟨p1, ?_⟩
  simp only [dClassKey, denoteN_ext hind p1.ext, denoteLs_ext hlvls p1.ext, hds2,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, ConLeche.classKeyCanon]

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:515 classKeyOf (the
annotation) — the parameters annotated one after another at depth `d`, each
answer con-leche's and scoped as its input (`annotateLoopS_sim`). -/
theorem annotateList_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (d : Nat) :
    ∀ (xs : List EIdx) (xsP : List Expr) (acc : List EIdx) (accP : List Expr),
    (∀ x ∈ xsP, Expr.WScoped d x) → (∀ x ∈ accP, Expr.WScoped d x) →
    CSpecF μ env fe
      (fun st => Frontend.denoteEList st xs = some xsP ∧
        Frontend.denoteEList st acc = some accP)
      (List.mapM.loop (fun x => Arena.annotateCore μ fe Arena.checkFuel d x) xs acc)
      (fun st r v => Frontend.denoteEList st r = some v ∧ ∀ x ∈ v, Expr.WScoped d x)
      (List.mapM.loop ((fueledOpsM μ).annotate env d) xsP accP) := by
  intro xs
  induction xs with
  | nil =>
    intro xsP acc accP _ hwacc s₀ s' r hok hpre hrun
    obtain ⟨hx, hacc⟩ := hpre
    simp only [Frontend.denoteEList, Option.some.injEq] at hx
    subst hx
    simp only [List.mapM.loop] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine ⟨CoreStep.refl hok, accP.reverse, ⟨?_, fun x hx => hwacc x (List.mem_reverse.mp hx)⟩,
      FOk.pure _⟩
    rw [← mapM_denoteE_eq_list]
    exact GR.mapM_reverse (by rw [mapM_denoteE_eq_list]; exact hacc)
  | cons x xs ih =>
    intro xsP acc accP hwx hwacc s₀ s' r hok hpre hrun
    obtain ⟨hx, hacc⟩ := hpre
    obtain ⟨xP, xsP', hxP, hxs, rfl⟩ := Core.denoteEList_cons_inv hx
    simp only [List.mapM.loop] at hrun
    obtain ⟨b, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨c1, w, hw, hww, hF⟩ := annotate_crun hk henv hok hxP (hwx xP List.mem_cons_self) k1
    obtain ⟨c2, v, hv, hG⟩ := ih xsP' (b :: acc) (w :: accP)
      (fun y hy => hwx y (List.mem_cons_of_mem _ hy))
      (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hww
        · exact hwacc y hy) s1 s' r c1.ok
      ⟨denoteEList_ext c1.ext _ _ hxs, by
        simp only [Frontend.denoteEList, hw, denoteEList_ext c1.ext _ _ hacc]⟩ z1
    exact ⟨c1.trans c2, v, hv, by simp only [List.mapM.loop]; exact FOk.bind hF hG⟩

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:501-516 classKeyOf — **a
class key, made checkable**: moved to the canonical parameters, closed over
them (the guard exact, con-leche's `&&` per term), annotated at the formers'
environment over the parameters.  Every annotated parameter is scoped by the
parameters (`classKeyOfS_sim`). -/
theorem classKeyOf_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (nP : Nat) (params : List EIdx)
    (paramsP : List Expr) (hpl : paramsP.length = nP)
    (hp : ∀ x ∈ paramsP, Expr.WScoped nP x) (k : Arena.ClassKey) (kP : ConLeche.ClassKey) :
    CSpecF μ env fe
      (fun st => Frontend.denoteEList st params = some paramsP ∧ dClassKey st k = some kP)
      (Arena.classKeyOf μ fe nP params k)
      (fun st r v => dClassKey st r = some v ∧ ∀ x ∈ v.ds, Expr.WScoped nP x)
      (ConLeche.classKeyOf (fueledOpsM μ) env nP paramsP kP) := by
  intro s₀ s' r hok hpre hrun
  simp only [Arena.classKeyOf] at hrun
  obtain ⟨k2, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, hk2⟩ := classKeyCanon_spec params paramsP k kP s₀ s1 k2 hok.state hok.pins hpre k1
  simp only [dClassKey, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hk2
  obtain ⟨ind, hind, lvls, hlvls, ds, hds, hkc⟩ := hk2
  obtain ⟨cl, s2, k2', z2⟩ := bindOk z1
  obtain ⟨p2, rfl⟩ := allM_E_pstep (F := fun x => x.bvarB == 0 && decide (x.fvarB ≤ nP))
    (fun _ => True) (fun _ h => h)
    (fun e eP s₀ s' b hok _ he hrun => by
      obtain ⟨bb, t1, j1, y1⟩ := bindOk hrun
      obtain ⟨q1, -, rfl⟩ := bvarB_pstep hok he j1
      by_cases hb : (eP.bvarB != 0) = true
      · rw [if_pos hb] at y1
        obtain ⟨rfl, rfl⟩ := pureOk y1
        simp only [bne_iff_ne, ne_eq] at hb
        exact ⟨q1, by simp [hb]⟩
      · rw [if_neg hb] at y1
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hb
        obtain ⟨ff, t2, j2, y2⟩ := bindOk y1
        obtain ⟨q2, -, rfl⟩ := RC.fvarB_pstep q1.ok (denote_ext he q1.ext) j2
        obtain ⟨rfl, rfl⟩ := pureOk y2
        exact ⟨q1.trans q2, by simp [hb]⟩)
    k2.ds ds s1 s2 cl p1.ok trivial hds k2' 
  obtain ⟨hcl, z3⟩ := AM.dunless_ok AM.Never.fail_any z2
  replace z3 := AM.pure_bind_ok z3
  have hkc' : ds = (ConLeche.classKeyCanon paramsP kP).ds := by rw [← hkc]
  rw [hkc'] at hcl hds
  have hw : ∀ x ∈ (ConLeche.classKeyCanon paramsP kP).ds, Expr.WScoped nP x := by
    intro x hx
    have hx' := List.all_eq_true.mp hcl x hx
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx'
    simp only [ConLeche.classKeyCanon, List.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact ConLeche.replaceFVars_WScoped_of_below
      (fun i r hr => hp r (List.mem_of_getElem? hr))
      (fun i hi => by simp [hpl, hi]) y (ConLeche.Expr.fvarB_le hx'.2)
  have c12 := (p1.trans p2).toCore hok
  obtain ⟨dsA, s3, k3, z4⟩ := bindOk z3
  obtain ⟨c3, dsAP, ⟨hdsA, hwA⟩, hF⟩ := annotateList_spec fe hk henv nP k2.ds _ [] [] hw
    (fun _ h => nomatch h) s2 s3 dsA c12.ok ⟨denoteEList_ext p2.ext _ _ hds, rfl⟩ k3
  obtain ⟨rfl, rfl⟩ := pureOk z4
  have c13 := c12.trans c3
  refine ⟨c13, { ConLeche.classKeyCanon paramsP kP with ds := dsAP }, ⟨?_, hwA⟩, ?_⟩
  · have e1 := denoteN_ext hind (p2.ext.trans c3.ext)
    have e2 := denoteLs_ext hlvls (p2.ext.trans c3.ext)
    simp only [dClassKey, e1, e2, hdsA, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rw [← hkc]
  · simp only [ConLeche.classKeyOf]
    rw [if_pos hcl]
    exact FOk.bind hF (FOk.pure _)

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:531 checkBlockClasses (the
keys) — every class key made checkable, one after another. -/
theorem classKeysOf_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (nP : Nat) (params : List EIdx)
    (paramsP : List Expr) (hpl : paramsP.length = nP)
    (hp : ∀ x ∈ paramsP, Expr.WScoped nP x) :
    ∀ (ks : List Arena.ClassKey) (ksP : List ConLeche.ClassKey) (acc : List Arena.ClassKey)
      (accP : List ConLeche.ClassKey), (∀ k ∈ accP, ∀ x ∈ k.ds, Expr.WScoped nP x) →
    CSpecF μ env fe
      (fun st => Frontend.denoteEList st params = some paramsP ∧
        ks.mapM (dClassKey st) = some ksP ∧ acc.mapM (dClassKey st) = some accP)
      (List.mapM.loop (Arena.classKeyOf μ fe nP params) ks acc)
      (fun st r v => r.mapM (dClassKey st) = some v ∧ ∀ k ∈ v, ∀ x ∈ k.ds, Expr.WScoped nP x)
      (List.mapM.loop (ConLeche.classKeyOf (fueledOpsM μ) env nP paramsP) ksP accP) := by
  intro ks
  induction ks with
  | nil =>
    intro ksP acc accP hwacc s₀ s' r hok hpre hrun
    obtain ⟨-, hks, hacc⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hks
    subst hks
    simp only [List.mapM.loop] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, accP.reverse, ⟨GR.mapM_reverse hacc,
      fun k hk => hwacc k (List.mem_reverse.mp hk)⟩, FOk.pure _⟩
  | cons k ks ih =>
    intro ksP acc accP hwacc s₀ s' r hok hpre hrun
    obtain ⟨hpar, hks, hacc⟩ := hpre
    obtain ⟨kP, ksP', rfl, hkd, hks'⟩ := GR.mapM_cons_inv hks
    simp only [List.mapM.loop] at hrun
    obtain ⟨b, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨c1, bP, ⟨hb, hwb⟩, hF⟩ := classKeyOf_spec fe hk henv nP params paramsP hpl hp k kP
      s₀ s1 b hok ⟨hpar, hkd⟩ k1
    obtain ⟨c2, v, hv, hG⟩ := ih ksP' (b :: acc) (bP :: accP)
      (fun k' hk' => by
        rcases List.mem_cons.mp hk' with rfl | hk'
        · exact hwb
        · exact hwacc k' hk') s1 s' r c1.ok
      ⟨denoteEList_ext c1.ext _ _ hpar, dClassKey_ext.list c1.ext _ _ hks', by
        simp only [List.mapM_cons, hb, dClassKey_ext.list c1.ext _ _ hacc, Option.bind_eq_bind,
          Option.bind_some, Option.pure_def]⟩ z1
    exact ⟨c1.trans c2, v, hv, by simp only [List.mapM.loop]; exact FOk.bind hF hG⟩

namespace GR

/-- con-leche: none — the classes at a member are counted alike. -/
theorem filter_member_length {st : EStore} (t : Nat) :
    ∀ {ms : List Arena.TargetMajor} {MsP : List ConLeche.TargetMajor},
      ms.mapM (dMajor st) = some MsP →
      (ms.filter (·.member == some t)).length = (MsP.filter (·.member == some t)).length
  | [], _, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | m :: ms, _, h => by
    obtain ⟨mP, MsP', rfl, hm, hms⟩ := mapM_cons_inv h
    have hmem := (dMajor_inv hm).2.2.2.2.2.2.1
    simp only [List.filter_cons, hmem]
    split <;> simp [filter_member_length t hms]

end GR

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:518-536 checkBlockClasses —
**THEOREM 1 for the classes, read and checked** at the formers' environment
`env₁` (index `fe₁`): the pre-pass (`classRead`, answering con-leche's at
`classNPcOf pP (mkFEnv env₁)`), every class key made checkable, every class
checked as a major over the canonical parameters, exactly one class per
member.  The reading and the classes denote con-leche's, every class scoped
(`ClassMajScoped`, what `genRecCheck_spec` takes). -/
theorem checkBlockClasses_spec {μ : CheckMode} {env₁ : Env} (fe₁ : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv₁ : EnvWF env₁)
    (p : Arena.BlockShape) (pP : ConLeche.BlockShape) (params : List EIdx)
    (paramsP : List Expr) (ctorsAs : List (List (IConstantVal × Nat)))
    (ctorsAsP : List (List (ConstantVal × Nat))) (hpl : paramsP.length = pP.nP)
    (hp : ∀ x ∈ paramsP, Expr.WScoped pP.nP x) :
    CSpecF μ env₁ fe₁
      (fun st => dShape st p = some pP ∧ Frontend.denoteEList st params = some paramsP ∧
        ctorsAs.mapM (dCtors st) = some ctorsAsP)
      (Arena.checkBlockClasses μ fe₁ p params ctorsAs)
      (fun st r v => dClassRead st r.1 = some v.1 ∧ r.2.mapM (dMajor st) = some v.2 ∧
        ∀ M ∈ v.2, Cached.ClassMajScoped pP.nP M)
      (ConLeche.checkBlockClasses (fueledOpsM μ) (mkFEnv env₁) env₁ pP paramsP ctorsAsP) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hsh, hpar, hcas⟩ := hpre
  obtain ⟨-, hrecs, hnP, -, -, -, -⟩ := RC.dShape_inv hsh
  have hk' := BlockShape.k_spec hsh
  simp only [Arena.checkBlockClasses] at hrun
  simp only [ConLeche.checkBlockClasses]
  obtain ⟨o, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, ho⟩ := classRead_spec p pP env₁ fe₁ p.nP p.recs pP.recs s₀ s1 o hok.state
    ⟨hsh, hok.ienv.toS, hrecs⟩ k1
  rw [hnP] at ho
  have c1 := p1.toCore hok
  cases o with
  | none => exact absurd z1 (fun hc => failOk hc)
  | some rd =>
    obtain ⟨rdP, hrdP, hrd⟩ := ho
    rw [hrdP]
    dsimp only at z1
    have hsl : rd.slots.mapM (dSlot s1.store) = some rdP.slots := by
      simp only [dClassRead, Option.map_eq_some_iff] at hrd
      obtain ⟨q, hq, rfl⟩ := hrd
      exact hq
    have hrc : rd.recCls = rdP.recCls := by
      simp only [dClassRead, Option.map_eq_some_iff] at hrd
      obtain ⟨q, hq, rfl⟩ := hrd
      rfl
    have hcls := classes_denote rd.recCls hsl
    have hclsP : ConLeche.ClassRead.classes ⟨rdP.slots, rd.recCls⟩ = rdP.classes := by
      rw [hrc]
    rw [hclsP] at hcls
    obtain ⟨keys, s2, k2, z2⟩ := bindOk z1
    rw [hnP] at k2
    obtain ⟨c2, keysP, ⟨hkeys, hwk⟩, hF2⟩ := classKeysOf_spec fe₁ hk henv₁ pP.nP params paramsP
      hpl hp _ _ [] [] (fun _ h => nomatch h) s1 s2 keys c1.ok
      ⟨denoteEList_ext c1.ext _ _ hpar, hcls, rfl⟩ k2
    have c12 := c1.trans c2
    obtain ⟨ms, s3, k3, z3⟩ := bindOk z2
    obtain ⟨c3, MsP, ⟨hms, hMs⟩, hF3⟩ := classMajors_spec fe₁ hk henv₁ p pP ctorsAs ctorsAsP
      params paramsP hpl hp keys keysP (fun k hk x hx => ⟨pP.nP, hwk k hk x hx⟩) s2 s3 ms c2.ok
      ⟨dShape_ext c12.ext _ _ hsh, dCtors_ext.list c12.ext _ _ hcas,
        denoteEList_ext c12.ext _ _ hpar, hkeys⟩ k3
    have hall : ((List.range p.k).all fun t => (ms.filter (·.member == some t)).length == 1) =
        ((List.range pP.k).all fun t => (MsP.filter (·.member == some t)).length == 1) := by
      rw [hk']
      congr 1
      funext t
      rw [GR.filter_member_length t hms]
    by_cases h1 : ((List.range pP.k).all fun t => (MsP.filter (·.member == some t)).length == 1)
      = true
    · rw [← hall] at h1
      rw [if_pos h1] at z3
      obtain ⟨rfl, rfl⟩ := pureOk z3
      rw [hall] at h1
      refine ⟨c12.trans c3, (rdP, MsP), ⟨dClassRead_ext (c2.ext.trans c3.ext) _ _ hrd, hms, hMs⟩,
        ?_⟩
      refine FOk.bind FOk.unwrapOr (FOk.bind hF2 (FOk.bind hF3 ?_))
      rw [if_pos h1]
      exact FOk.seq (FOk.pure ()) (FOk.pure _)
    · rw [← hall] at h1
      rw [if_neg h1] at z3
      exact absurd z3 (fun hc => failOk hc)

/-- con-leche: none — a seed (a positivity key with its parameter count),
denoted. -/
def dSeed (st : EStore) (q : Arena.NestKey × Nat) : Option (ConLeche.NestKey × Nat) :=
  (dKey st q.1).map (·, q.2)

/-- con-leche: none — `dSeed` survives the arena's growth. -/
theorem dSeed_ext : DExt dSeed := by
  intro st st' hx q y h
  simp only [dSeed, Option.map_eq_some_iff] at h ⊢
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨k, dKey_ext hx _ _ hk, rfl⟩

/-- con-leche: ConLeche/Kernel/Inductives/GenRec.lean:494-499 classSeeds — **the
seeds**: every OUTSIDE class in the positivity check's representation
(`nestSeedOf`), in order. -/
theorem classSeeds_spec (fnd : ConLeche.Name → Option ConstantInfo) (ctx : Arena.NestCtx)
    (ctxP : ConLeche.NestCtx) (holes : List EIdx) (holesP : List Expr) :
    ∀ (ms : List Arena.TargetMajor) (MsP : List ConLeche.TargetMajor),
    PSpecP (fun st => dCtx st fnd ctx = some ctxP ∧ Frontend.denoteEList st holes = some holesP ∧
        ms.mapM (dMajor st) = some MsP)
      (Arena.classSeeds ctx holes ms)
      (fun st r => r.mapM (dSeed st) = some (ConLeche.classSeeds ctxP holesP MsP)) := by
  intro ms
  induction ms with
  | nil =>
    intro MsP s₀ s' r hok hp hpre hrun
    obtain ⟨-, -, hms⟩ := hpre
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hms
    subst hms
    simp only [Arena.classSeeds] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons m ms ih =>
    intro MsP s₀ s' r hok hp hpre hrun
    obtain ⟨hctx, hholes, hms⟩ := hpre
    obtain ⟨mP, MsP', rfl, hm, hms'⟩ := GR.mapM_cons_inv hms
    obtain ⟨hind, hlvls, hds, hnPc, -, -, hmem, -, -⟩ := dMajor_inv hm
    simp only [Arena.classSeeds] at hrun
    simp only [ConLeche.classSeeds, List.filterMap_cons] at ⊢ ih
    cases hmm : m.member with
    | some t =>
      rw [hmm] at hrun
      rw [← hmem, hmm]
      exact ih MsP' s₀ s' r hok hp ⟨hctx, hholes, hms'⟩ hrun
    | none =>
      rw [hmm] at hrun
      rw [← hmem, hmm]
      dsimp only at hrun
      obtain ⟨sd, s1, k1, z1⟩ := bindOk hrun
      obtain ⟨p1, hsd, hsd2⟩ := nestSeedOf_spec fnd ctx ctxP holes holesP m.ind mP.ind m.lvls
        mP.lvls m.ds mP.ds m.nPc s₀ s1 sd hok hp ⟨hctx, hholes, hind, hlvls, hds⟩ k1
      obtain ⟨rest, s2, k2, z2⟩ := bindOk z1
      obtain ⟨p2, hrest⟩ := ih MsP' s1 s2 rest p1.ok (PinsOK.ofPStep hp p1)
        ⟨dCtx_ext fnd p1.ext _ _ hctx, denoteEList_ext p1.ext _ _ hholes,
          dMajor_ext.list p1.ext _ _ hms'⟩ k2
      obtain ⟨rfl, rfl⟩ := pureOk z2
      refine ⟨p1.trans p2, ?_⟩
      simp only [Option.isNone_none, ↓reduceIte, List.mapM_cons, hrest, Option.bind_eq_bind,
        Option.pure_def]
      simp only [dSeed, dKey_ext p2.ext _ _ hsd, Option.map_some, hsd2, hnPc, Option.bind_some]
      rfl

end ConRon.Bridge.Inductives

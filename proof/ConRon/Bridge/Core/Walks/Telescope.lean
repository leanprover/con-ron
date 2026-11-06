/-
# `ConRon.Bridge.Core.Walks.Telescope` — the readers under the projection guard, in run form

The projection guard (`Walks/ProjGuard.lean`) opens the stored constructor's
telescope at free variables (`openPisAtFvarsF`) and asks which fields a later
field uses (`structUsedLater`, over the memoised `hasLooseBVarBGo`).  Those twins
live in `Arena/Core.lean` since con-leche task #480 moved the guard to the use;
this module is their Theorem 1, in the run form (`PStep`, `PSpec`) that the
`Bridge/Inductives/**` tier states its readers in, with the few run-form
primitives that form needs.  It sits in its own namespace
(`ConRon.Bridge.Core.Guard`) so that it shares no name with that tier.
-/
module

public import ConRon.Bridge.StateOK
public import ConRon.Bridge.Rel
public import ConRon.Bridge.ExprOps.Subst
public import ConRon.Bridge.ExprOps.Spine
import ConLeche.Kernel.CheckerBase
import ConRon.Bridge.ExprOps.Inst1
import ConRon.Bridge.ExprOps.Ranges
import ConRon.Bridge.Core.Walks.Proj
public import ConRon.Bridge.Pers
import ConRon.Bridge.Specs
import ConRon.Bridge.GrindAttr

public section

namespace ConRon.Bridge.Core.Guard

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge Std.WP

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — **the frame of the tier's
PURE grade**: the store grows, the pin table stands still, and the fourteen per-declaration caches stand still up to
`readLC` and `lvlEqC` — the two a `lvlEq?` call may write (task #97-P3-Frame;
`Bridge/StateOK.lean`'s `CacheFrame` is the clause, and `PStep.of_caches` is
what a twin that writes neither uses).  The memo tables are NOT framed: every
rebuilding walk of `Arena/ExprOps.lean` writes its own. -/
structure PStep (s s' : AState) : Prop where
  ok : StateOK s'
  ext : Ext s.store s'.store
  cframe : CacheFrame s s'
  pins : s'.pins = s.pins

theorem PStep.refl {s : AState} (h : StateOK s) : PStep s s :=
  ⟨h, Ext.refl _, CacheFrame.refl _, rfl⟩

theorem PStep.trans {a b c : AState} (h₁ : PStep a b) (h₂ : PStep b c) :
    PStep a c :=
  ⟨h₂.ok, h₁.ext.trans h₂.ext,
    h₁.cframe.trans h₂.cframe, by rw [h₂.pins, h₁.pins]⟩

/-- con-leche: none — the frame of a twin that writes no per-declaration
table at all, which is what all but three of the tier's ~110 twins do.  The
shape a proof reaches when it has the plain cache equation in hand. -/
theorem PStep.of_caches {s s' : AState} (hok : StateOK s')
    (hx : Ext s.store s'.store)
    (hc : s'.caches = s.caches) (hp : s'.pins = s.pins) : PStep s s' :=
  ⟨hok, hx, CacheFrame.of_eq hc hx, hp⟩

@[expose] def PSpec {α : Type} (P : EStore → Prop) (c : AM α) (R : EStore → α → Prop) :
    Prop :=
  ∀ (s₀ s' : AState) (r : α), StateOK s₀ → P s₀.store → c s₀ = .ok (r, s') →
    PStep s₀ s' ∧ R s'.store r

/-- con-leche: none — the answer is the value. -/
abbrev RV {α : Type} (x : α) : EStore → α → Prop := fun _ r => r = x


/-- con-leche: none — **the tag-first twin's test, in run form**: at a handle
whose view is known, `if h.tag == t then view h >>= f else e` ran as
`view h >>= f`, because on the `else` side the continuation's catch-all arm IS
`e`. -/
theorem tagIf_view_run {α : Type} {h : EIdx} {t : UInt32} {v : ENodeView}
    {f : ENodeView → AM α} {e : AM α} {s s' : AState} {r : α}
    (hv : s.store.view h = some v) (he : v.tagOf ≠ t → f v = e)
    (hrun : (if h.tag == t then (Arena.view h >>= f) else e) s = .ok (r, s')) :
    (Arena.view h >>= f) s = .ok (r, s') := by
  by_cases ht : (h.tag == t) = true
  · rw [ite_eq_left ht] at hrun; exact hrun
  · rw [ite_eq_right ht] at hrun
    have hne : v.tagOf ≠ t := by rw [← EStore.tagOf_of_view hv]; simpa using ht
    have hb : (Arena.view h >>= f) s = f v s := by
      show StateT.bind (Arena.view h) f s = _
      simp only [StateT.bind, Arena.view, bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, Except.bind, Except.pure, hv]
    rw [hb, he hne]; exact hrun



/-- con-leche: none — **`internE`, as a run**: the arena grew, nothing else
moved, and the new handle denotes what the node view says. -/
theorem internE_run {s s' : AState} {w : ENodeView} {h : EIdx}
    (hok : StateOK s) (hv : s.store.ViewOK w)
    (hrun : internE w s = .ok (h, s')) :
    PStep s s' ∧ denoteE s'.store h = denoteEView s'.store w := by
  obtain ⟨h1, h2, _h3, _h4, _h5, h6, h7, _h8, h9⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun (internE_spec s w hok.wf hv)
  exact ⟨PStep.of_caches ⟨h1⟩ h2 h6 h7, h9⟩



/-- con-leche: none — **`Bridge/ExprOps/Spine.lean`'s `denoteBL` IS
`Frontend.denoteEList`**: a binder telescope is its list of domains (in con-leche
a binder carries its type and nothing else), and the two tiers each write
the readback.  One induction identifies them, and it is what lets
this tier read the BINDERS off `stripPis` rather than only the residual. -/
theorem denoteBL_eq_denoteEList {st : EStore} :
    ∀ (bs : List EIdx), ExprOps.denoteBL st bs = Frontend.denoteEList st bs := by
  intro bs
  induction bs with
  | nil => rfl
  | cons a as ih =>
    simp only [ExprOps.denoteBL, Frontend.denoteEList, ih]
    cases denoteE st a <;> cases Frontend.denoteEList st as <;> rfl

/-! ### `stripPis`, in run form

`Bridge/ExprOps/Spine.lean`'s `stripPis_spec` is closed; here is its run
form with the two inversions of `denoteBP` its readers need, and the other
spine readers and interners the generators call, in run form. -/

/-- con-leche: ConLeche/Kernel/ExprOps.lean:1128-1134 stripPis — the run form
at this tier's frame; `stripPis` is read-only, so the state does not move at
all. -/
theorem stripPis_pstep {k : Nat} {s₀ s' : AState} {c : EIdx} {cP : Expr}
    {r : Option (List EIdx × EIdx)} (hok : StateOK s₀)
    (hd : denoteE s₀.store c = some cP)
    (hrun : Arena.stripPis k c s₀ = .ok (r, s')) :
    s' = s₀ ∧ ExprOps.denoteBP s₀.store r = some (Expr.stripPis k cP) := by
  obtain ⟨h1, h2⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.stripPis_spec k s₀ c hok (by rw [hd]; rfl))
  exact ⟨h1, h2 cP hd⟩

/-- con-leche: none — a `none` answer is `none` on the pure side too: the
two-sidedness `stripPis`' dispatch needs. -/
theorem stripPis_none {st : EStore} {k : Nat} {cP : Expr}
    (h : ExprOps.denoteBP st none = some (Expr.stripPis k cP)) :
    Expr.stripPis k cP = none := (Option.some.inj h).symm

/-- con-leche: none — and a `some` answer of a telescope peel (`stripPis`,
`stripLams`) names the pure answer: its binders and its residual denote. -/
theorem denoteBP_some {st : EStore} {v : Option (List Expr × Expr)}
    {bs : List EIdx} {e : EIdx}
    (h : ExprOps.denoteBP st (some (bs, e)) = some v) :
    ∃ xs x, v = some (xs, x) ∧ Frontend.denoteEList st bs = some xs ∧
      denoteE st e = some x := by
  simp only [ExprOps.denoteBP] at h
  cases hb : ExprOps.denoteBL st bs with
  | none => rw [hb] at h; simp at h
  | some xs =>
    cases he : denoteE st e with
    | none => rw [hb, he] at h; simp at h
    | some x =>
      rw [hb, he] at h
      refine ⟨xs, x, (Option.some.inj h).symm, ?_, rfl⟩
      rw [← denoteBL_eq_denoteEList]; exact hb



/-- con-leche: ConLeche/Kernel/ExprOps.lean:1212-1217 fvarTypeD — the run
form of `Bridge/ExprOps/Spine.lean`'s closed `fvarTypeD_spec`. -/
theorem fvarTypeD_run {s₀ s' : AState} {h r : EIdx} {hP : Expr}
    (hok : StateOK s₀) (hd : denoteE s₀.store h = some hP)
    (hrun : Arena.fvarTypeD h s₀ = .ok (r, s')) :
    s' = s₀ ∧ denoteE s₀.store r = some hP.fvarTypeD := by
  obtain ⟨h1, h2⟩ := AM.of_run (P := fun t => t = s₀) rfl hrun
    (ExprOps.fvarTypeD_spec s₀ h hok (by rw [hd]; rfl))
  exact ⟨h1, h2 hP hd⟩



@[expose] def denoteOpen (st : EStore) :
    Option (List EIdx × EIdx) → Option (Option (List Expr × Expr))
  | none => some none
  | some (fvs, e) =>
    (Frontend.denoteEList st fvs).bind fun xs => (denoteE st e).map fun x => some (xs, x)

/-- con-leche: none — `denoteOpen` at a `some`, from its two halves. -/
theorem denoteOpen_some {st : EStore} {fvs : List EIdx} {e : EIdx}
    {xs : List Expr} {x : Expr} (h1 : Frontend.denoteEList st fvs = some xs)
    (h2 : denoteE st e = some x) : denoteOpen st (some (fvs, e)) = some (some (xs, x)) := by
  simp [denoteOpen, h1, h2]

/-- con-leche: none — and read back into its two halves. -/
theorem denoteOpen_some_inv {st : EStore} {fvs : List EIdx} {e : EIdx}
    {o : Option (List Expr × Expr)} (h : denoteOpen st (some (fvs, e)) = some o) :
    ∃ xs x, o = some (xs, x) ∧ Frontend.denoteEList st fvs = some xs ∧
      denoteE st e = some x := by
  simp only [denoteOpen, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨xs, h1, x, h2, rfl⟩ := h
  exact ⟨xs, x, rfl, h1, h2⟩

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:130-140 openPisAtFvars — **the
binder-at-a-time opener, as a run**: pure grade, and the answer denotes
con-leche's. -/
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
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨PStep.refl hok, by simp [denoteOpen, Frontend.denoteEList, hh,
      ConLeche.openPisAtFvars]⟩
  | succ n ih =>
    intro i h hP s₀ s' r hok hh hrun
    simp only [Arena.openPisAtFvars] at hrun
    -- the tag-first twin
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
      obtain ⟨fv, s2, k2, z2⟩ := AM.bind_ok z1
      obtain ⟨p2, hfv⟩ := internE_run hok (viewOK_fvar (by rw [hd]; rfl)) k2
      have hfv' : denoteE s2.store fv = some (.fvar i domP) := by
        rw [hfv]; simp [denoteEView, denote_ext hd p2.ext]
      obtain ⟨op, s3, k3, z3⟩ := AM.bind_ok z2
      have hb2 : denoteE s2.store body = some bodyP := denote_ext hb p2.ext
      obtain ⟨h1, h2, h4, h5, -, h7⟩ := ExprOps.instantiate1Fast_run p2.ok hfv'
        (by rw [hb2]; rfl) k3
      have p3 : PStep s2 s3 := PStep.of_caches h1 h2 h4 h5
      have hop : denoteE s3.store op = some (bodyP.instantiate1 (.fvar i domP) 0) :=
        h7 _ hb2
      obtain ⟨o, s4, k4, z4⟩ := AM.bind_ok z3
      obtain ⟨p4, ho⟩ := ih p3.ok hop k4
      have p24 := p2.trans (p3.trans p4)
      simp only [ConLeche.openPisAtFvars]
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok z4
        refine ⟨p24, ?_⟩
        have hn : ConLeche.openPisAtFvars n (bodyP.instantiate1 (.fvar i domP)) (i + 1)
            = none := (Option.some.inj ho).symm
        simp [denoteOpen, hn]
      | some q =>
        obtain ⟨fvs, e⟩ := q
        obtain ⟨xs, x, hx, h1, h2⟩ := denoteOpen_some_inv ho
        obtain ⟨rfl, rfl⟩ := AM.pure_ok z4
        refine ⟨p24, ?_⟩
        rw [hx]
        exact denoteOpen_some (by
          simp only [Frontend.denoteEList, denote_ext hfv' (p3.ext.trans p4.ext),
            h1]) h2
    all_goals
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
      refine ⟨PStep.refl hok, ?_⟩
      rw [denoteE_view_eq hok.wf hv] at hh
      cases hP
      case forallE a b => simp [denoteEView] at hh
      all_goals rfl

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:153-167 openPisAtFvarsFGo — **the
one-pass opener's core, as a run**: the arena's push-order vector is
`InstLVec` of con-leche's cons-order list. -/
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
    obtain ⟨e, s1, k1, z1⟩ := AM.bind_ok hrun
    obtain ⟨h1, h2, h4, h5, -, h7⟩ := ExprOps.instantiateListFast_run hok hacc
      (by rw [hh]; rfl) k1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
    refine ⟨PStep.of_caches h1 h2 h4 h5, ?_⟩
    simp [denoteOpen, Frontend.denoteEList, h7 _ hh, ConLeche.openPisAtFvarsFGo]
  | succ n ih =>
    intro acc ws i h hP s₀ s' r hok hacc hh hrun
    simp only [Arena.openPisAtFvarsFGo] at hrun
    -- the tag-first twin
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
      obtain ⟨dd, s2, k2, z2⟩ := AM.bind_ok z1
      obtain ⟨h1, h2, h4, h5, -, h7⟩ := ExprOps.instantiateListFast_run hok hacc
        (by rw [hd]; rfl) k2
      have p2 : PStep s₀ s2 := PStep.of_caches h1 h2 h4 h5
      have hdd : denoteE s2.store dd = some (domP.instantiateList ws 0) := h7 _ hd
      obtain ⟨fv, s3, k3, z3⟩ := AM.bind_ok z2
      obtain ⟨p3, hfv⟩ := internE_run p2.ok (viewOK_fvar (by rw [hdd]; rfl)) k3
      have hfv' : denoteE s3.store fv = some (.fvar i (domP.instantiateList ws 0)) := by
        rw [hfv]; simp [denoteEView, denote_ext hdd p3.ext]
      obtain ⟨o, s4, k4, z4⟩ := AM.bind_ok z3
      obtain ⟨p4, ho⟩ := ih p3.ok (InstLVec.push (hacc.ext (p2.ext.trans p3.ext)) hfv')
        (denote_ext hb (p2.ext.trans p3.ext)) k4
      have p24 := p2.trans (p3.trans p4)
      simp only [ConLeche.openPisAtFvarsFGo]
      cases o with
      | none =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok z4
        refine ⟨p24, ?_⟩
        have hn : ConLeche.openPisAtFvarsFGo (.fvar i (domP.instantiateList ws) :: ws) n
            bodyP (i + 1) = none := (Option.some.inj ho).symm
        simp [denoteOpen, hn]
      | some q =>
        obtain ⟨fvs, e⟩ := q
        obtain ⟨xs, x, hx, h1, h2⟩ := denoteOpen_some_inv ho
        obtain ⟨rfl, rfl⟩ := AM.pure_ok z4
        refine ⟨p24, ?_⟩
        rw [hx]
        exact denoteOpen_some (by
          simp only [Frontend.denoteEList, denote_ext hfv' p4.ext, h1]) h2
    all_goals
      obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
      refine ⟨PStep.refl hok, ?_⟩
      rw [denoteE_view_eq hok.wf hv] at hh
      cases hP
      case forallE a b => simp [denoteEView] at hh
      all_goals rfl

/-- con-leche: ConLeche/Kernel/CheckerBase.lean:169-176 openPisAtFvarsF — **the
one-pass opener, as a run**, answering con-leche's binder-at-a-time
`openPisAtFvars` (through con-leche's `openPisAtFvarsF_eq`), which is what
con-leche's `checkSumCtor` calls. -/
theorem openPisAtFvarsF_run {n i : Nat} {h : EIdx} {hP : Expr} {s₀ s' : AState}
    {r : Option (List EIdx × EIdx)} (hok : StateOK s₀)
    (hh : denoteE s₀.store h = some hP)
    (hrun : Arena.openPisAtFvarsF n h i s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ denoteOpen s'.store r = some (ConLeche.openPisAtFvars n hP i) := by
  rw [← ConLeche.openPisAtFvarsF_eq]
  simp only [Arena.openPisAtFvarsF] at hrun
  obtain ⟨o, s1, k1, z1⟩ := AM.bind_ok hrun
  obtain ⟨p1, ho⟩ := openPisAtFvarsFGo_run n hok
    (show ExprOps.InstLVec s₀.store #[] [] from rfl) hh k1
  simp only [ConLeche.openPisAtFvarsF]
  cases o with
  | some q =>
    obtain ⟨fvs, e⟩ := q
    obtain ⟨xs, x, hx, h1, h2⟩ := denoteOpen_some_inv ho
    obtain ⟨rfl, rfl⟩ := AM.pure_ok z1
    refine ⟨p1, ?_⟩
    rw [hx]
    exact denoteOpen_some h1 h2
  | none =>
    have hn : ConLeche.openPisAtFvarsFGo [] n hP i = none := (Option.some.inj ho).symm
    rw [hn]
    obtain ⟨p2, h2⟩ := openPisAtFvars_run n p1.ok (denote_ext hh p1.ext) z1
    exact ⟨p1.trans p2, h2⟩



/-! ## The memo invariant -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:171-172 LooseBVarMemoInv
The `(handle, cursor)`-keyed memo of `hasLooseBVarB`: every recorded answer is
the real one at the key's own cursor. -/
def LooseMemoOK (tbl : Std.HashMap (EIdx × Nat) Bool) (st : EStore) : Prop :=
  ∀ (k : EIdx × Nat) (r : Bool), tbl[k]? = some r →
    ∃ e, denoteE st k.1 = some e ∧ r = Expr.hasLooseBVarB k.2 e

/-- con-leche: none — the empty memo is sound. -/
theorem LooseMemoOK.empty {st : EStore} : LooseMemoOK ∅ st := by
  intro k r h; simp at h

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:177-189
LooseBVarMemoInv.insert — recording a TRUE answer keeps the memo sound.  This
is `Arena.hasLooseBVarBIns` read as an invariant step. -/
theorem LooseMemoOK.insert {tbl : Std.HashMap (EIdx × Nat) Bool} {st : EStore}
    (hm : LooseMemoOK tbl st) {h : EIdx} {i : Nat} {hP : Expr} {r : Bool}
    (hd : denoteE st h = some hP) (heq : r = Expr.hasLooseBVarB i hP) :
    LooseMemoOK (tbl.insert (h, i) r) st := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact ⟨hP, hd, heq⟩
  · exact hm k r' hk


/-- con-leche: ConLeche/Kernel/ExprOps.lean:1577 bvarB_eq — **the cutoff's
run form**, at this tier's frame: `Bridge/ExprOps/Ranges.lean`'s `bvarB_run`
answers `Expr.bvarB` and moves nothing but the `bvarBound` memo, which
`PStep` does not frame. -/
theorem bvarB_pstep {fuel : Nat} {s₀ s' : AState} {e : EIdx} {eP : Expr}
    {r : Nat} (hok : StateOK s₀) (hd : denoteE s₀.store e = some eP)
    (hrun : Arena.bvarB fuel e s₀ = .ok (r, s')) :
    PStep s₀ s' ∧ s'.store = s₀.store ∧ r = Expr.bvarB eP := by
  obtain ⟨h1, h2, h3, _, h5⟩ :=
    ExprOps.bvarB_run hok (by rw [hd]; rfl) hrun
  refine ⟨PStep.of_caches ⟨by rw [h1]; exact hok.wf⟩ ?_ h2 h3, h1, h5 eP hd⟩
  · rw [h1]; exact Ext.refl _



/-! ### The pure side's own equations

`Expr.hasLooseBVarB` is `if e.bvarB ≤ i then false else <the ten-way walk>`,
so every arm of the twin's dispatch needs the same two-step unfolding.  These
are con-leche's `hasLooseBVarB_eq` proof's first line, once per shape. -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:132-145 (the `if`)
— **the cutoff's own fact**: a node whose loose-bvar bound is at or below `i`
has no `bvar i`.  This is what the twin's early return computes. -/
theorem hasLooseBVarB_cut {i : Nat} {e : Expr} (hc : e.bvarB ≤ i) :
    Expr.hasLooseBVarB i e = false := by
  cases e <;> (rw [Expr.hasLooseBVarB]; exact ite_eq_left hc)

theorem hasLooseBVarB_bvar {i j : Nat} (hc : ¬ (Expr.bvar j).bvarB ≤ i) :
    Expr.hasLooseBVarB i (.bvar j) = (i == j) := by
  rw [Expr.hasLooseBVarB]; exact ite_eq_right hc

theorem hasLooseBVarB_app {i : Nat} {f a : Expr}
    (hc : ¬ (Expr.app f a).bvarB ≤ i) :
    Expr.hasLooseBVarB i (.app f a) =
      (Expr.hasLooseBVarB i f || Expr.hasLooseBVarB i a) := by
  rw [Expr.hasLooseBVarB]; exact ite_eq_right hc

theorem hasLooseBVarB_lam {i : Nat} {ty b : Expr}
    (hc : ¬ (Expr.lam ty b).bvarB ≤ i) :
    Expr.hasLooseBVarB i (.lam ty b) =
      (Expr.hasLooseBVarB i ty || Expr.hasLooseBVarB (i + 1) b) := by
  rw [Expr.hasLooseBVarB]; exact ite_eq_right hc

theorem hasLooseBVarB_forallE {i : Nat} {ty b : Expr}
    (hc : ¬ (Expr.forallE ty b).bvarB ≤ i) :
    Expr.hasLooseBVarB i (.forallE ty b) =
      (Expr.hasLooseBVarB i ty || Expr.hasLooseBVarB (i + 1) b) := by
  rw [Expr.hasLooseBVarB]; exact ite_eq_right hc

theorem hasLooseBVarB_letE {i : Nat} {t v b : Expr}
    (hc : ¬ (Expr.letE t v b).bvarB ≤ i) :
    Expr.hasLooseBVarB i (.letE t v b) =
      (Expr.hasLooseBVarB i t || Expr.hasLooseBVarB i v ||
        Expr.hasLooseBVarB (i + 1) b) := by
  rw [Expr.hasLooseBVarB]; exact ite_eq_right hc

theorem hasLooseBVarB_proj {i : Nat} {n : ConLeche.Name} {k : Nat} {e : Expr}
    (hc : ¬ (Expr.proj n k e).bvarB ≤ i) :
    Expr.hasLooseBVarB i (.proj n k e) = Expr.hasLooseBVarB i e := by
  rw [Expr.hasLooseBVarB]; exact ite_eq_right hc

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:198-233 Expr.hasLooseBVarBGo
The memoised walk: the answer is the real one AND the memo it hands back is
still sound.

**Proof:** a fuel induction generalising the memo,
the cursor and the handle, with the ten-way `view` dispatch as its arm.  The
memo travels as a HYPOTHESIS (`LooseMemoOK`) and comes back as a CONCLUSION,
so a hit is discharged by the invariant itself (`hit`) and a miss by
`LooseMemoOK.insert` (`fin`); the early return is
`Bridge/ExprOps/Ranges.lean`'s `bvarB_run` (closed) read through
`bvarB_pstep` plus `hasLooseBVarB_cut`. -/
theorem hasLooseBVarBGo_spec (memo : Std.HashMap (EIdx × Nat) Bool) (i : Nat)
    (fuel : Nat) (h : EIdx) (hP : Expr) :
    PSpec (fun st => denoteE st h = some hP ∧ LooseMemoOK memo st)
      (Arena.hasLooseBVarBGo memo i fuel h)
      (fun st r => r.1 = Expr.hasLooseBVarB i hP ∧ LooseMemoOK r.2 st) := by
  induction fuel generalizing memo i h hP with
  | zero =>
    intro s₀ s' r hok hp hrun
    simp only [Arena.hasLooseBVarBGo] at hrun
    exact absurd hrun (fun hc => AM.fail_ok hc)
  | succ fuel ih =>
    intro s₀ s' r hok hp hrun
    obtain ⟨hd, hm⟩ := hp
    simp only [Arena.hasLooseBVarBGo] at hrun
    obtain ⟨bb, s₁, hb, h2⟩ := AM.bind_ok hrun
    obtain ⟨hstep0, hst0, rfl⟩ := bvarB_pstep hok hd hb
    have hok1 : StateOK s₁ := hstep0.ok
    have hd1 : denoteE s₁.store h = some hP := by rw [hst0]; exact hd
    have hm1 : LooseMemoOK memo s₁.store := by rw [hst0]; exact hm
    -- the shared tail: record the answer in the memo and stop
    have fin : ∀ {s₂ s₃ : AState} {y r' : Bool × Std.HashMap (EIdx × Nat) Bool},
        PStep s₁ s₂ → y.1 = Expr.hasLooseBVarB i hP →
        LooseMemoOK y.2 s₂.store →
        (pure (Arena.hasLooseBVarBIns h i y) :
            AM (Bool × Std.HashMap (EIdx × Nat) Bool)) s₂ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ r'.1 = Expr.hasLooseBVarB i hP ∧
          LooseMemoOK r'.2 s₃.store := by
      intro s₂ s₃ y r' hs hy hmy hz
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hz
      exact ⟨hstep0.trans hs, hy,
        LooseMemoOK.insert hmy (denote_ext hd1 hs.ext) hy⟩
    -- the shared memo HIT: the invariant is exactly what makes it sound
    have hit : ∀ {s₃ : AState} {r₀ : Bool}
        {r' : Bool × Std.HashMap (EIdx × Nat) Bool},
        memo[(h, i)]? = some r₀ →
        (pure ((r₀, memo) : Bool × Std.HashMap (EIdx × Nat) Bool) :
            AM (Bool × Std.HashMap (EIdx × Nat) Bool)) s₁ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ r'.1 = Expr.hasLooseBVarB i hP ∧
          LooseMemoOK r'.2 s₃.store := by
      intro s₃ r₀ r' hlk hz
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hz
      obtain ⟨e, he, hre⟩ := hm1 (h, i) r₀ hlk
      obtain rfl := Option.some.inj (hd1.symm.trans he)
      exact ⟨hstep0, hre, hm1⟩
    split at h2
    · -- the packed-bound cutoff
      rename_i hc
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      exact ⟨hstep0, (hasLooseBVarB_cut hc).symm, hm1⟩
    · rename_i hc
      obtain ⟨v, s₂, hv, h3⟩ := AM.bind_ok h2
      obtain ⟨rfl, hw⟩ := view_run hv
      cases v
      case bvar j =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
        obtain rfl := denote_bvar_inv hok1.wf hw hd1
        exact ⟨hstep0, (hasLooseBVarB_bvar hc).symm, hm1⟩
      case fvar k ty =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
        obtain ⟨t, rfl, _⟩ := denote_fvar_inv hok1.wf hw hd1
        exact ⟨hstep0, by rw [Expr.hasLooseBVarB]; split <;> rfl, hm1⟩
      case sort u =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
        obtain ⟨l, rfl, _⟩ := denote_sort_inv hok1.wf hw hd1
        exact ⟨hstep0, by rw [Expr.hasLooseBVarB]; split <;> rfl, hm1⟩
      case const n us =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
        obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hok1.wf hw hd1
        exact ⟨hstep0, by rw [Expr.hasLooseBVarB]; split <;> rfl, hm1⟩
      case lit l =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
        obtain rfl := denote_lit_inv hok1.wf hw hd1
        exact ⟨hstep0, by rw [Expr.hasLooseBVarB]; split <;> rfl, hm1⟩
      case app f a =>
        obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_app_inv hok1.wf hw hd1
        cases hlk : memo[(h, i)]? with
        | some r₀ => rw [hlk] at h3; exact hit hlk h3
        | none =>
          rw [hlk] at h3
          obtain ⟨p1, s₂, hc1, h4⟩ := AM.bind_ok h3
          obtain ⟨b1, m1⟩ := p1
          obtain ⟨hsA, hrA, hmA⟩ :=
            ih memo i f ef _ _ (b1, m1) hok1 ⟨hf, hm1⟩ hc1
          have hrA' : b1 = Expr.hasLooseBVarB i ef := hrA
          cases b1
          · obtain ⟨p2, s₃, hc2, hz⟩ := AM.bind_ok h4
            obtain ⟨b2, m2⟩ := p2
            obtain ⟨hsB, hrB, hmB⟩ :=
              ih m1 i a ea _ _ (b2, m2) hsA.ok
                ⟨denote_ext ha hsA.ext, hmA⟩ hc2
            have hrB' : b2 = Expr.hasLooseBVarB i ea := hrB
            exact fin (hsA.trans hsB)
              (by simp [hasLooseBVarB_app hc, ← hrA', ← hrB']) hmB hz
          · obtain ⟨y, s₂', hy, hz⟩ := AM.bind_ok h4
            obtain ⟨rfl, rfl⟩ := AM.pure_ok hy
            exact fin hsA (by simp [hasLooseBVarB_app hc, ← hrA']) hmA hz
      case lam ty b =>
        obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_lam_inv hok1.wf hw hd1
        cases hlk : memo[(h, i)]? with
        | some r₀ => rw [hlk] at h3; exact hit hlk h3
        | none =>
          rw [hlk] at h3
          obtain ⟨p1, s₂, hc1, h4⟩ := AM.bind_ok h3
          obtain ⟨b1, m1⟩ := p1
          obtain ⟨hsA, hrA, hmA⟩ :=
            ih memo i ty et _ _ (b1, m1) hok1 ⟨hty, hm1⟩ hc1
          have hrA' : b1 = Expr.hasLooseBVarB i et := hrA
          cases b1
          · obtain ⟨p2, s₃, hc2, hz⟩ := AM.bind_ok h4
            obtain ⟨b2, m2⟩ := p2
            obtain ⟨hsB, hrB, hmB⟩ :=
              ih m1 (i + 1) b eb _ _ (b2, m2) hsA.ok
                ⟨denote_ext hbd hsA.ext, hmA⟩ hc2
            have hrB' : b2 = Expr.hasLooseBVarB (i + 1) eb := hrB
            exact fin (hsA.trans hsB)
              (by simp [hasLooseBVarB_lam hc, ← hrA', ← hrB']) hmB hz
          · obtain ⟨y, s₂', hy, hz⟩ := AM.bind_ok h4
            obtain ⟨rfl, rfl⟩ := AM.pure_ok hy
            exact fin hsA (by simp [hasLooseBVarB_lam hc, ← hrA']) hmA hz
      case forallE ty b =>
        obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_forallE_inv hok1.wf hw hd1
        cases hlk : memo[(h, i)]? with
        | some r₀ => rw [hlk] at h3; exact hit hlk h3
        | none =>
          rw [hlk] at h3
          obtain ⟨p1, s₂, hc1, h4⟩ := AM.bind_ok h3
          obtain ⟨b1, m1⟩ := p1
          obtain ⟨hsA, hrA, hmA⟩ :=
            ih memo i ty et _ _ (b1, m1) hok1 ⟨hty, hm1⟩ hc1
          have hrA' : b1 = Expr.hasLooseBVarB i et := hrA
          cases b1
          · obtain ⟨p2, s₃, hc2, hz⟩ := AM.bind_ok h4
            obtain ⟨b2, m2⟩ := p2
            obtain ⟨hsB, hrB, hmB⟩ :=
              ih m1 (i + 1) b eb _ _ (b2, m2) hsA.ok
                ⟨denote_ext hbd hsA.ext, hmA⟩ hc2
            have hrB' : b2 = Expr.hasLooseBVarB (i + 1) eb := hrB
            exact fin (hsA.trans hsB)
              (by simp [hasLooseBVarB_forallE hc, ← hrA', ← hrB']) hmB hz
          · obtain ⟨y, s₂', hy, hz⟩ := AM.bind_ok h4
            obtain ⟨rfl, rfl⟩ := AM.pure_ok hy
            exact fin hsA (by simp [hasLooseBVarB_forallE hc, ← hrA']) hmA hz
      case letE lt lv lb =>
        obtain ⟨et, ev, eb, rfl, hty, hval, hbd⟩ :=
          denote_letE_inv hok1.wf hw hd1
        cases hlk : memo[(h, i)]? with
        | some r₀ => rw [hlk] at h3; exact hit hlk h3
        | none =>
          rw [hlk] at h3
          obtain ⟨p1, s₂, hc1, h4⟩ := AM.bind_ok h3
          obtain ⟨b1, m1⟩ := p1
          obtain ⟨hsA, hrA, hmA⟩ :=
            ih memo i lt et _ _ (b1, m1) hok1 ⟨hty, hm1⟩ hc1
          have hrA' : b1 = Expr.hasLooseBVarB i et := hrA
          cases b1
          · obtain ⟨p2, s₃, hc2, h5⟩ := AM.bind_ok h4
            obtain ⟨b2, m2⟩ := p2
            obtain ⟨hsB, hrB, hmB⟩ :=
              ih m1 i lv ev _ _ (b2, m2) hsA.ok
                ⟨denote_ext hval hsA.ext, hmA⟩ hc2
            have hrB' : b2 = Expr.hasLooseBVarB i ev := hrB
            cases b2
            · obtain ⟨p3, s₄, hc3, hz⟩ := AM.bind_ok h5
              obtain ⟨b3, m3⟩ := p3
              obtain ⟨hsC, hrC, hmC⟩ :=
                ih m2 (i + 1) lb eb _ _ (b3, m3) hsB.ok
                  ⟨denote_ext (denote_ext hbd hsA.ext) hsB.ext, hmB⟩ hc3
              have hrC' : b3 = Expr.hasLooseBVarB (i + 1) eb := hrC
              exact fin ((hsA.trans hsB).trans hsC)
                (by simp [hasLooseBVarB_letE hc, ← hrA', ← hrB', ← hrC'])
                hmC hz
            · obtain ⟨y, s₃', hy, hz⟩ := AM.bind_ok h5
              obtain ⟨rfl, rfl⟩ := AM.pure_ok hy
              exact fin (hsA.trans hsB)
                (by simp [hasLooseBVarB_letE hc, ← hrA', ← hrB']) hmB hz
          · obtain ⟨y, s₂', hy, hz⟩ := AM.bind_ok h4
            obtain ⟨rfl, rfl⟩ := AM.pure_ok hy
            exact fin hsA (by simp [hasLooseBVarB_letE hc, ← hrA']) hmA hz
      case proj pn pk psub =>
        obtain ⟨nm, es, rfl, _, hsub⟩ := denote_proj_inv hok1.wf hw hd1
        cases hlk : memo[(h, i)]? with
        | some r₀ => rw [hlk] at h3; exact hit hlk h3
        | none =>
          rw [hlk] at h3
          obtain ⟨p1, s₂, hc1, hz⟩ := AM.bind_ok h3
          obtain ⟨b1, m1⟩ := p1
          obtain ⟨hsA, hrA, hmA⟩ :=
            ih memo i psub es _ _ (b1, m1) hok1 ⟨hsub, hm1⟩ hc1
          have hrA' : b1 = Expr.hasLooseBVarB i es := hrA
          exact fin hsA (by simp [hasLooseBVarB_proj hc, ← hrA']) hmA hz

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:380-381 Expr.hasLooseBVarBFast
The entry: an empty memo is sound, so the answer is the real one.

**Proof:** `hasLooseBVarBGo_spec` at the empty
memo, which `LooseMemoOK.empty` says is sound. -/
theorem hasLooseBVarBFast_spec (i : Nat) (e : EIdx) (eP : Expr) :
    PSpec (fun st => denoteE st e = some eP)
      (Arena.hasLooseBVarBFast i e) (RV (Expr.hasLooseBVarB i eP)) := by
  intro s₀ s' r hok hd hrun
  simp only [Arena.hasLooseBVarBFast] at hrun
  obtain ⟨p, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hstep, hr, _⟩ :=
    hasLooseBVarBGo_spec ∅ i Arena.coreWalkFuel e eP s₀ s₁ p hok
      ⟨hd, LooseMemoOK.empty⟩ h1
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
  exact ⟨hstep, hr⟩

/-! ## The projection guards -/

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:393-396 structUsedLater
Is field `j` mentioned by a later field's domain?

**Proof:** `hasLooseBVarBFast_spec` under the
constructor type's telescope, with `stripPis_pstep`'s two inversions for the
dispatch. -/
theorem structUsedLater_spec (cty : EIdx) (ctyP : Expr) (nP j : Nat) :
    PSpec (fun st => denoteE st cty = some ctyP)
      (Arena.structUsedLater cty nP j)
      (RV (ConLeche.structUsedLater ctyP nP j)) := by
  intro s₀ s' r hok hd hrun
  simp only [Arena.structUsedLater] at hrun
  obtain ⟨o, s₁, h1, h2⟩ := AM.bind_ok hrun
  show PStep s₀ s' ∧ r = ConLeche.structUsedLater ctyP nP j
  rw [ConLeche.structUsedLater]
  obtain ⟨rfl, hbp⟩ := stripPis_pstep hok hd h1
  cases o with
  | none =>
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
    rw [stripPis_none hbp]
    exact ⟨PStep.refl hok, rfl⟩
  | some p =>
    obtain ⟨bs, rest⟩ := p
    obtain ⟨xs, x, hsp, -, hx⟩ := denoteBP_some hbp
    rw [hsp]
    exact hasLooseBVarBFast_spec 0 rest x _ _ r hok hx h2

end ConRon.Bridge.Core.Guard

/-
# `ConRon.Bridge.Checker.StoredFrame` — phase A's frame, with nothing known of the environment

Theorem 1's fold takes a block's evidence from its job, which runs at the final store, so
it needs phase A's later steps to be an extension of the persistent tier BEFORE it knows
anything of the environment those steps ran at: a stored block sits in that environment
unchecked.  This module is that frame.  It reads no specification of what a scratch run
did: `Arena.scratchRun` puts the persistent tier, the flags and the pins back, and a
promotion is unconditional (`Bridge/Promote`).  What runs outside a scratch tier is the
recogniser and its small companions on the records as parsed, which have specifications
that read no environment, taken here at the empty one.

`Bdy` is the boundary, `BStep` the frame.  `installDeclStep_frame` and
`installFold_frame` are the two theorems the fold reads; `storedInstall_frame` also says
what the stored install's pushes are when the environment IS known.
-/
module

public import ConRon.Bridge.Checker.Frame
public import ConRon.Bridge.Promote
public import ConRon.Bridge.Inductives.BlockInstall
public import ConRon.Bridge.Inductives.BlockParts
public import ConRon.Bridge.Checker.Inv
public import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Specs
import ConRon.Bridge.Checker.Canon

public section

open ConLeche ConRon.Arena ConRon.Bridge.Inductives

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## The boundary -/

/-- con-leche: none — the empty environment's index, the one the recogniser's
specifications are taken at: they read no environment. -/
abbrev feE : IFEnv := mkIFEnv IEnv.empty

/-- con-leche: none — **a boundary of phase A**: the store well formed, the pins persistent
and denoting, the caches sound. -/
structure Bdy (s : AState) : Prop where
  check : CheckOK false Env.empty feE s
  persPins : PersPins s

/-- con-leche: none — what a phase-A step leaves: a boundary, a persistent extension, the
pins. -/
structure BStep (s s' : AState) : Prop where
  bdy : Bdy s'
  pext : PExt s.store s'.store
  pins : s'.pins = s.pins

theorem BStep.trans {a b c : AState} (h₁ : BStep a b) (h₂ : BStep b c) : BStep a c :=
  ⟨h₂.bdy, h₁.pext.trans h₂.pext, by rw [h₂.pins, h₁.pins]⟩

theorem BStep.refl {s : AState} (h : Bdy s) : BStep s s := ⟨h, PExt.refl _, rfl⟩

/-- con-leche: none — the empty environment's index answers nothing, in any store. -/
theorem IFEnvOK.empty (s : AState) : IFEnvOK Env.empty feE s where
  hit := fun n ci h => by simp [IFEnv.find?, mkIFEnv, mkIFEnvGo, IEnv.empty] at h
  cover := fun nm c h => by simp [Env.empty, Env.find?] at h
  tblHit := fun n t h => by
    simp [IFEnv.findTable?, IFEnv.find?, mkIFEnv, mkIFEnvGo, IEnv.empty] at h
  tblCover := fun nm pt h => by simp [Env.empty, Env.findTable?, Env.find?] at h

/-- con-leche: none — a well-formed store with empty caches is a boundary. -/
theorem Bdy.of_empty {s : AState} (hwf : StoreWF s.store) (hc : s.caches = Caches.empty)
    (hp : PinsOK s) (hpp : PersPins s) : Bdy s :=
  ⟨⟨⟨hwf⟩, CacheOK.of_empty hc, hp, IFEnvOK.empty s⟩, hpp⟩

/-- con-leche: none — a step that only appended. -/
theorem Bdy.step {s s' : AState} (hb : Bdy s) (hst : CoreStep Env.empty feE s s') : BStep s s' :=
  ⟨⟨hst.ok, hb.persPins.mono hst.pins⟩, PExt.of_ext hst.ext, hst.pins⟩

/-- con-leche: none — the closing of a bracket whose projection grew: a boundary with empty
caches at the projection. -/
theorem Bdy.close {s t : AState} (hb : Bdy s) (hwf : StoreWF t.store.dropScratch)
    (hx : Ext s.store.dropScratch t.store.dropScratch) (hp : t.pins = s.pins) :
    BStep s
      ({ store := t.store.dropScratch, memos := t.memos, caches := Caches.empty,
         pins := t.pins } : AState) := by
  have hpx : PExt s.store t.store.dropScratch :=
    (PExt.dropScratch hb.check.state.wf).trans (PExt.of_ext hx)
  refine ⟨Bdy.of_empty hwf rfl ?_ (hb.persPins.mono hp), hpx, hp⟩
  exact hb.check.pins.pmono hb.persPins hpx hp

/-! ## A closed store -/

/-- con-leche: none — a handle of the scratch tier does not denote while the tier is closed. -/
theorem denoteN_scr_off {st : NStore} (h : st.scratchOn = false) {i : NIdx}
    (hi : i.isPersistent = false) {x : ConLeche.Name} : denoteN st i ≠ some x := by
  have key : ∀ f, denoteNAux st f i = none := by
    intro f
    cases f <;> simp [denoteNAux, NStore.view, hi, h]
  intro hd
  simp only [denoteN, key] at hd
  exact nomatch hd

/-- con-leche: none — the same at a level. -/
theorem denoteL_scr_off {st : LStore} (h : st.scratchOn = false) {i : LIdx}
    (hi : i.isPersistent = false) {x : Level} : denoteL st i ≠ some x := by
  have key : ∀ f, denoteLAux st f i = none := by
    intro f
    cases f <;> simp [denoteLAux, LStore.view, hi, h]
  intro hd
  simp only [denoteL, key] at hd
  exact nomatch hd

/-- con-leche: none — the same at a level list. -/
theorem denoteLs_scr_off {st : LsStore} (h : st.scratchOn = false) {i : LsIdx}
    (hi : i.isPersistent = false) {x : List Level} : denoteLs st i ≠ some x := by
  intro hd
  simp [denoteLs, LsStore.view, hi, h] at hd

/-- con-leche: none — the same at an expression. -/
theorem denoteE_scr_off {st : EStore} (h : st.scratchOn = false) {i : EIdx}
    (hi : i.isPersistent = false) {x : Expr} : denoteE st i ≠ some x := by
  have key : ∀ f, denoteEAux st f i = none := by
    intro f
    cases f <;> simp [denoteEAux, EStore.view, hi, h]
  intro hd
  simp only [denoteE, key] at hd
  exact nomatch hd

/-- con-leche: none — **a closed store extends to its projection**, at every handle. -/
theorem Ext.of_closed {st : EStore} (hwf : StoreWF st) (h : st.scratchOn = false) :
    Ext st st.dropScratch := by
  have hd := PExt.dropScratch hwf
  have hs := hwf.scratchSync
  have hn : st.lss.ls.ns.scratchOn = false := hs.ns.symm.trans h
  have hl : st.lss.ls.scratchOn = false := hs.ls.symm.trans h
  have hls : st.lss.scratchOn = false := hs.lss.symm.trans h
  refine ⟨⟨⟨fun i n hi => ?_, fun i u hi => ?_⟩, fun i us hi => ?_⟩, fun i e hi => ?_⟩
  · cases hp : i.isPersistent with
    | true => exact hd.lss.ls.ns i n hp hi
    | false => exact absurd hi (denoteN_scr_off hn hp)
  · cases hp : i.isPersistent with
    | true => exact hd.lss.ls.lvl i u hp hi
    | false => exact absurd hi (denoteL_scr_off hl hp)
  · cases hp : i.isPersistent with
    | true => exact hd.lss.lst i us hp hi
    | false => exact absurd hi (denoteLs_scr_off hls hp)
  · cases hp : i.isPersistent with
    | true => exact hd.expr i e hp hi
    | false => exact absurd hi (denoteE_scr_off h hp)

/-- con-leche: none — what the reading's closed stretch leaves. -/
structure CStep (s s' : AState) : Prop where
  step : BStep s s'
  ext : Ext s.store s'.store
  closed : s'.store.scratchOn = false

theorem CStep.trans {a b c : AState} (h₁ : CStep a b) (h₂ : CStep b c) : CStep a c :=
  ⟨h₁.step.trans h₂.step, h₁.ext.trans h₂.ext, h₂.closed⟩

/-! ## A framed bracket -/

/-- con-leche: none — what opening a bracket on a boundary and framing a run leaves: the
promotion's invariant, with the boundary's projection as its source, whatever ran. -/
theorem PSrc.of_bracket {s : AState} (hb : Bdy s) (st : EStore) :
    PSrc s.store.dropScratch (st.frameFrom s.store.enableScratch) :=
  PSrc.self (st := st.frameFrom s.store.enableScratch)
    (EStore.dropScratch_spec hb.check.state.wf).1

/-! ## `storedTry` -/

/-- con-leche: ConLeche/Cached/StoredInstall.lean:161-170 storedTele
**A stored inference, whatever it ran**: `V` is what `keep` establishes of its answer, at
the projection. -/
theorem storedTry_frame {α β : Type} {run : AM α} {keep : α → AM β} {V : EStore → β → Prop}
    {s s' : AState} {r : Option β} (hb : Bdy s)
    (hkeep : ∀ a (t t' : AState) (b : β), PSrc s.store.dropScratch t.store →
      keep a t = .ok (b, t') →
      PSrc s.store.dropScratch t'.store ∧ Ext t.store.dropScratch t'.store.dropScratch ∧
        PFrame t t' ∧ V t'.store.dropScratch b)
    (hrun : storedTry run keep s = .ok (r, s')) :
    BStep s s' ∧ s'.caches = Caches.empty ∧ s'.store.scratchOn = false ∧
      Ext s.store.dropScratch s'.store ∧ ∀ b, r = some b → V s'.store b := by
  unfold storedTry at hrun
  obtain ⟨_, s₁, g1, r1⟩ := AM.bind_ok hrun
  obtain rfl : s₁ = { s with caches := Caches.empty } := (Prod.mk.inj (Except.ok.inj g1)).2.symm
  obtain ⟨_, s₂, g2, r2⟩ := AM.bind_ok r1
  obtain rfl := enterScratch_inv g2
  simp only at r2
  cases hc : scratchRun run (⟨s.store.enableScratch, Memos.empty, Caches.empty, s.pins⟩ : AState) with
  | error e =>
    rw [hc] at r2
    simp only at r2
    obtain ⟨_, s₃, g3, r3⟩ := AM.bind_ok r2
    obtain rfl := dropScratch_inv g3
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r3
    refine ⟨?_, rfl, rfl, Ext.refl _, fun b h => nomatch h⟩
    exact Bdy.close (s := s) (t := ⟨s.store.enableScratch, Memos.empty, Caches.empty, s.pins⟩) hb
      (EStore.dropScratch_spec hb.check.state.wf).1 (Ext.refl _) rfl
  | ok v =>
    obtain ⟨a, t⟩ := v
    rw [hc] at r2
    simp only at r2
    obtain ⟨t₁, -, -, rfl⟩ := scratchRun_ok hc
    obtain ⟨b, t₂, g3, r3⟩ := AM.bind_ok r2
    obtain ⟨_, t₃, g4, r4⟩ := AM.bind_ok r3
    obtain rfl := dropScratch_inv g4
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r4
    obtain ⟨hsrc2, hx2, hf2, hV⟩ := hkeep a _ _ _ (PSrc.of_bracket hb t₁.store) g3
    refine ⟨Bdy.close hb hsrc2.piWF hx2 (by simpa using hf2.pins), rfl, rfl, hx2, ?_⟩
    intro b' h
    obtain rfl := Option.some.inj h
    exact hV

/-! ## The reading, outside a bracket -/

/-- con-leche: none — the level a `sort` node holds denotes. -/
theorem denoteL_of_viewSort {st : EStore} (hwf : StoreWF st) {h : EIdx} {e : Expr} {l : LIdx}
    (hd : denoteE st h = some e) (htg : (h.tag == ETag.sort) = true)
    (hv : st.viewSort h = some l) : ∃ u, denoteL st.ls l = some u := by
  obtain ⟨u, -, hu⟩ := denote_sort_inv hwf (view_of_viewSort_tag htg hv) hd
  exact ⟨u, hu⟩

/-- con-leche: ConLeche/Cached/StoredInstall.lean:161-170 storedTele -/
theorem storedTele_frame {mode : CheckMode} {fe : IFEnv} {cv : IConstantVal} {n : Nat}
    {c : ConstantVal} {s s' : AState} {r : Option (IConstantVal × LIdx)} (hb : Bdy s)
    (hcl : s.store.scratchOn = false) (hc : Frontend.denoteCV s.store cv = some c)
    (hrun : storedTele mode fe cv n s = .ok (r, s')) :
    CStep s s' ∧ ∀ q, r = some q → ∃ u, denoteL s'.store.ls q.2 = some u := by
  obtain ⟨-, -, hty⟩ := denoteCV_inv hc
  have hwf := hb.check.state.wf
  have slow : ∀ {t' : AState} {r' : Option (IConstantVal × LIdx)},
      (storedTry (storedTeleRun mode fe cv n) fun q => do
          let (m, ty) ← promoteE PMemo.empty coreWalkFuel q.1
          let (_, s) ← promoteL m coreWalkFuel q.2
          pure ({ cv with type := ty }, s)) s = .ok (r', t') →
      CStep s t' ∧ ∀ q, r' = some q → ∃ u, denoteL t'.store.ls q.2 = some u := by
    intro t' r' h
    obtain ⟨h1, -, hc1, hx1, h2⟩ := storedTry_frame
      (V := fun st q => ∃ u, denoteL st.ls q.2 = some u) hb (fun q t t₂ b hsrc hk => by
        obtain ⟨⟨m, ty⟩, t₁, k1, k2⟩ := AM.bind_ok hk
        obtain ⟨⟨m₂, l⟩, t₃, k3, k4⟩ := AM.bind_ok k2
        obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
        obtain ⟨hs1, hm1, hx1, -, -, -⟩ := promoteE_pi hsrc (PMemoPi.empty _ _) k1
        obtain ⟨hs2, -, hx2, -, hu, -⟩ := promoteL_pi hs1 hm1 k3
        have ha1 := promoteE_aext _ _ _ _ _ _ k1
        have ha2 := promoteL_aext _ _ _ _ _ _ k3
        exact ⟨hs2, hx1.trans hx2, ⟨by rw [ha2.memos, ha1.memos], by rw [ha2.caches, ha1.caches],
          by rw [ha2.pins, ha1.pins], by rw [ha2.scratchOn, ha1.scratchOn]⟩, hu⟩) h
    exact ⟨⟨h1, (Ext.of_closed hwf hcl).trans hx1, hc1⟩, h2⟩
  simp only [storedTele] at hrun
  obtain ⟨o, s₁, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, hbp⟩ := stripPis_pstep hb.check.state hty g1
  cases o with
  | none => exact slow r1
  | some p =>
    obtain ⟨bs, body⟩ := p
    obtain ⟨-, x, -, -, hbody⟩ := denoteBP_some hbp
    simp only at r1
    split at r1
    · rename_i htg
      obtain ⟨o', s₂, g2, r2⟩ := AM.bind_ok r1
      obtain ⟨rfl, ho⟩ := AM.of_run (P := fun t => t = s₁) rfl g2 (viewSort_spec s₁ body)
      cases o' with
      | none => exact absurd r2 (AM.Never.fail _ _ _ _)
      | some l =>
        obtain ⟨rfl, rfl⟩ := AM.pure_ok r2
        refine ⟨⟨BStep.refl hb, Ext.refl _, hcl⟩, fun q hq => ?_⟩
        obtain rfl := Option.some.inj hq
        exact denoteL_of_viewSort hwf hbody htg ho.symm
    · exact slow r1

/-- con-leche: ConLeche/Cached/StoredInstall.lean:175-180 storedFormers -/
theorem storedFormers_frame {mode : CheckMode} {fe : IFEnv} {nP : Nat} :
    ∀ (ms : List Arena.MemberShape) (i : Nat) (out : List IConstantVal) (s0 : LIdx)
      (xs : List ConLeche.MemberShape) (s s' : AState) (r : List IConstantVal × LIdx),
      Bdy s → s.store.scratchOn = false → ms.mapM (dMember s.store) = some xs →
      (∃ u, denoteL s.store.ls s0 = some u) →
      storedFormers mode fe nP ms i out s0 s = .ok (r, s') →
      CStep s s' ∧ ∃ u, denoteL s'.store.ls r.2 = some u := by
  intro ms
  induction ms with
  | nil =>
    intro i out s0 xs s s' r hb hcl _ hu hrun
    simp only [storedFormers] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨⟨BStep.refl hb, Ext.refl _, hcl⟩, hu⟩
  | cons m rest ih =>
    intro i out s0 xs s s' r hb hcl hxs hu hrun
    obtain ⟨x, ys, rfl, hm, hys⟩ := mapM_option_cons_inv hxs
    obtain ⟨hc, -, -⟩ := dMember_inv hm
    simp only [storedFormers] at hrun
    obtain ⟨o, s₁, g1, r1⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hq⟩ := storedTele_frame hb hcl hc g1
    have hys' := dMember_ext.list hs1.ext _ _ hys
    have hu' : ∃ u, denoteL s₁.store.ls s0 = some u := by
      obtain ⟨u, hu⟩ := hu; exact ⟨u, denoteL_ext hu hs1.ext⟩
    cases o with
    | none =>
      obtain ⟨h1, h2⟩ := ih _ _ _ _ _ _ _ hs1.step.bdy hs1.closed hys' hu' r1
      exact ⟨hs1.trans h1, h2⟩
    | some q =>
      simp only at r1
      obtain ⟨u₁, hu₁⟩ := hq q rfl
      have hnext : ∃ u, denoteL s₁.store.ls (if i == 0 then q.2 else s0) = some u := by
        split
        · exact ⟨u₁, hu₁⟩
        · exact hu'
      obtain ⟨h1, h2⟩ := ih _ _ _ _ _ _ _ hs1.step.bdy hs1.closed hys' hnext r1
      exact ⟨hs1.trans h1, h2⟩

/-- con-leche: ConLeche/Cached/StoredInstall.lean:214-223 storedGuards -/
theorem storedGuards_frame {mode : CheckMode} {fe₁ : IFEnv} {p : Arena.BlockShape}
    {c : IConstantVal × Nat} {s s' : AState} {r : List LIdx} (hb : Bdy s)
    (hrun : storedGuards mode fe₁ p c s = .ok (r, s')) : BStep s s' := by
  simp only [storedGuards] at hrun
  obtain ⟨o, s₁, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, rfl⟩ := AM.pure_ok r1
  exact (storedTry_frame (V := fun _ _ => True) hb (fun gs t t₂ b hsrc hk => by
    obtain ⟨⟨m, gs'⟩, t₁, k1, k2⟩ := AM.bind_ok hk
    obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
    obtain ⟨hs1, -, hx1, -⟩ := promoteLList_pi hsrc (PMemoPi.empty _ _) k1
    exact ⟨hs1, hx1, PFrame.of_aext (promoteLList_aext _ _ _ _ _ _ k1), trivial⟩) g1).1

/-- con-leche: ConLeche/Cached/StoredInstall.lean:228-241 storedTables -/
theorem storedGuardsAll_frame {mode : CheckMode} {fe₁ : IFEnv} {p : Arena.BlockShape} :
    ∀ (ms : List Arena.MemberShape) (s s' : AState) (r : List (List LIdx)), Bdy s →
      storedGuardsAll mode fe₁ p ms s = .ok (r, s') → BStep s s' := by
  intro ms
  induction ms with
  | nil =>
    intro s s' r hb hrun
    simp only [storedGuardsAll] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact BStep.refl hb
  | cons m rest ih =>
    intro s s' r hb hrun
    have tail : ∀ {q : List (List LIdx)} {t : List LIdx},
        (do let r ← storedGuardsAll mode fe₁ p rest; pure (t :: r)) s = .ok (q, s') → BStep s s' := by
      intro q t h
      obtain ⟨q', s₂, g2, r2⟩ := AM.bind_ok h
      obtain ⟨-, rfl⟩ := AM.pure_ok r2
      exact ih _ _ _ hb g2
    simp only [storedGuardsAll] at hrun
    cases hc : m.ctors with
    | nil => rw [hc] at hrun; exact tail hrun
    | cons c cs =>
      cases cs with
      | cons c2 cs2 => rw [hc] at hrun; exact tail hrun
      | nil =>
        rw [hc] at hrun
        simp only at hrun
        by_cases hi : (m.nIdx == 0) = true
        · rw [ite_eq_left hi] at hrun
          obtain ⟨gs, s₁, g1, r1⟩ := AM.bind_ok hrun
          have h1 := storedGuards_frame hb g1
          obtain ⟨q, s₂, g2, r2⟩ := AM.bind_ok r1
          obtain ⟨-, rfl⟩ := AM.pure_ok r2
          exact h1.trans (ih _ _ _ h1.bdy g2)
        · rw [ite_eq_right hi] at hrun
          exact tail hrun

/-! ## What the pushes are, when the environment is known

Every push of the stored install is one of `IFEnv.push` and `IFEnv.pushTable`, which a
coherent index survives. -/

/-- con-leche: none — a chain of pushes onto `fe`. -/
structure PushChain (fe r : IFEnv) : Prop where
  coh : IFEnvCoh r
  pushed : Pushed fe r
  tpushed : TPushed fe r

theorem PushChain.refl {fe : IFEnv} (h : IFEnvCoh fe) : PushChain fe fe :=
  ⟨h, Pushed.refl _, TPushed.refl _⟩

theorem PushChain.push {fe r : IFEnv} (h : PushChain fe r) (ci : IConstantInfo) :
    PushChain fe (r.push ci) :=
  ⟨h.coh.push ci, h.pushed.trans (Pushed.push r ci), h.tpushed.trans (TPushed.push r ci)⟩

theorem PushChain.pushTable {fe r : IFEnv} (h : PushChain fe r) (t : IProjTable) :
    PushChain fe (r.pushTable t) :=
  ⟨h.coh.pushTable t, h.pushed.trans (Pushed.pushTable r t), h.tpushed.trans (TPushed.pushTable r t)⟩

theorem consSumCtors_chain {nP : Nat} {fe₀ : IFEnv} :
    ∀ (cs : List (IConstantVal × Nat)) (fe : IFEnv), PushChain fe₀ fe →
      PushChain fe₀ (consSumCtors nP cs fe) := by
  intro cs
  induction cs with
  | nil => intro fe h; exact h
  | cons c rest ih =>
    intro fe h
    simp only [Arena.consSumCtors]
    exact ih _ (h.push _)

theorem storedCtors_chain {nP : Nat} {fe₀ : IFEnv} :
    ∀ (ms : List Arena.MemberShape) (fe : IFEnv), PushChain fe₀ fe →
      PushChain fe₀ (storedCtors nP ms fe) := by
  intro ms
  induction ms with
  | nil => intro fe h; exact h
  | cons m rest ih =>
    intro fe h
    simp only [storedCtors]
    exact ih _ (consSumCtors_chain _ _ h)

theorem storedRecs_chain {vis₂ : Nat} {p : Arena.BlockShape} {fe₀ : IFEnv} :
    ∀ (rs : List Arena.RecShape) (i : Nat) (fe r : IFEnv) (s s' : AState), PushChain fe₀ fe →
      storedRecs vis₂ p i rs fe s = .ok (r, s') → PushChain fe₀ r := by
  intro rs
  induction rs with
  | nil =>
    intro i fe r s s' h hrun
    simp only [storedRecs] at hrun
    obtain ⟨rfl, -⟩ := AM.pure_ok hrun
    exact h
  | cons c rest ih =>
    intro i fe r s s' h hrun
    simp only [storedRecs] at hrun
    obtain ⟨o, s₁, g1, r1⟩ := AM.bind_ok hrun
    cases o with
    | none => exact ih _ _ _ _ _ (h.push _) r1
    | some M =>
      simp only at r1
      obtain ⟨rl, s₂, g2, r2⟩ := AM.bind_ok r1
      exact ih _ _ _ _ _ (h.push _) r2

theorem storedTables_chain {p : Arena.BlockShape} {fe₀ : IFEnv} :
    ∀ (ms : List Arena.MemberShape) (gs : List (List LIdx)) (fe r : IFEnv) (s s' : AState),
      PushChain fe₀ fe → storedTables p ms gs fe s = .ok (r, s') → PushChain fe₀ r := by
  intro ms
  induction ms with
  | nil =>
    intro gs fe r s s' h hrun
    simp only [storedTables] at hrun
    obtain ⟨rfl, -⟩ := AM.pure_ok hrun
    exact h
  | cons m rest ih =>
    intro gs fe r s s' h hrun
    simp only [storedTables] at hrun
    cases hc : m.ctors with
    | nil => rw [hc] at hrun; exact ih _ _ _ _ _ h hrun
    | cons c cs =>
      cases cs with
      | cons c2 cs2 => rw [hc] at hrun; exact ih _ _ _ _ _ h hrun
      | nil =>
        rw [hc] at hrun
        simp only at hrun
        by_cases hi : (m.nIdx == 0) = true
        · rw [ite_eq_left hi] at hrun
          obtain ⟨o, s₁, g1, r1⟩ := AM.bind_ok hrun
          cases o with
          | none => exact ih _ _ _ _ _ h r1
          | some bs => exact ih _ _ _ _ _ (h.pushTable _) r1
        · rw [ite_eq_right hi] at hrun
          exact ih _ _ _ _ _ h hrun

theorem consBlockInds_chain {p₁ : Arena.BlockShape} {isRec : Bool} {fe₀ : IFEnv} :
    ∀ (cvs : List IConstantVal) (i : Nat) (fe r : IFEnv) (s s' : AState), PushChain fe₀ fe →
      Arena.consBlockInds p₁ isRec cvs i fe s = .ok (r, s') → PushChain fe₀ r := by
  intro cvs
  induction cvs with
  | nil =>
    intro i fe r s s' h hrun
    simp only [Arena.consBlockInds] at hrun
    obtain ⟨rfl, -⟩ := AM.pure_ok hrun
    exact h
  | cons c rest ih =>
    intro i fe r s s' h hrun
    simp only [Arena.consBlockInds] at hrun
    obtain ⟨caps, s₁, g1, r1⟩ := AM.bind_ok hrun
    exact ih _ _ _ _ _ (h.push _) r1

/-- con-leche: none — **what the stored install pushed, the environment known**: pushes,
persistent and denoting something; their names' uniqueness, which the job supplies, is
what makes the index the list's. -/
structure StoredOut (fe r : IFEnv) (st : EStore) : Prop where
  pushed : Pushed fe r
  tpushed : TPushed fe r
  denote : ∃ env', denoteFEnv st r = some env'
  pers : PersIFEnv r
  coh : (r.env.consts.map IConstantInfo.name).Nodup → IFEnvCoh r

/-- con-leche: none — the index is unchanged. -/
theorem StoredOut.refl {fe : IFEnv} {st : EStore} {env : Env} (hc : IFEnvCoh fe) (hp : PersIFEnv fe)
    (hd : denoteFEnv st fe = some env) : StoredOut fe fe st :=
  ⟨Pushed.refl _, TPushed.refl _, ⟨env, hd⟩, hp, fun _ => hc⟩

/-- con-leche: ConLeche/Cached/StoredInstall.lean:251-267 storedInstall — the reading's last
bracket. -/
theorem storedTail_frame {p : Arena.BlockShape} {guards : List (List LIdx)} {vis nt : Nat}
    {fe₁ r : IFEnv} {s s' : AState} (hb : Bdy s)
    (hrun : storedTail p guards vis nt fe₁ s = .ok (r, s')) :
    BStep s s' ∧ s'.caches = Caches.empty ∧
      ∀ fe₀ env₀, IFEnvCoh fe₀ → PersIFEnv fe₀ → PushChain fe₀ fe₁ → vis = fe₀.visibleBelow →
        nt = fe₀.env.tables.length → denoteFEnv s.store fe₀ = some env₀ → StoredOut fe₀ r s'.store := by
  simp only [storedTail] at hrun
  obtain ⟨_, s₁, g1, r1⟩ := AM.bind_ok hrun
  obtain rfl : s₁ = { s with caches := Caches.empty } := (Prod.mk.inj (Except.ok.inj g1)).2.symm
  obtain ⟨_, s₂, g2, r2⟩ := AM.bind_ok r1
  obtain rfl := enterScratch_inv g2
  obtain ⟨fe₄, s₃, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨t₁, hc₁, -, hF⟩ := scratchRun_ok g3
  obtain ⟨⟨m, fe₅⟩, s₄, g4, r4⟩ := AM.bind_ok r3
  obtain ⟨_, s₅, g5, r5⟩ := AM.bind_ok r4
  obtain rfl := dropScratch_inv g5
  obtain ⟨rfl, rfl⟩ := AM.pure_ok r5
  have hst : s₃.store = t₁.store.frameFrom s.store.enableScratch := by rw [hF]
  have hpi : s₃.store.dropScratch = s.store.dropScratch := by rw [hst]; rfl
  have hsrc : PSrc s.store.dropScratch s₃.store := by
    rw [hst]; exact PSrc.of_bracket hb t₁.store
  obtain ⟨hs4, -, hx4, hf4⟩ := promoteNew_frame hsrc (PMemoPi.empty _ _) g4
  rw [hpi] at hx4
  have hp3 : s₃.pins = s.pins := by rw [hF]
  refine ⟨Bdy.close hb hs4.piWF hx4 (by rw [hf4.pins, hp3]), rfl, ?_⟩
  intro fe₀ env₀ hcoh0 hp0 hch hvis hnt hd0
  subst hvis hnt
  have hch4 : PushChain fe₀ fe₄ := by
    obtain ⟨fe₃, t₂, k1, k2⟩ := AM.bind_ok hc₁
    have ch3 := storedRecs_chain _ _ _ _ _ _ (storedCtors_chain _ _ hch) k1
    exact storedTables_chain _ _ _ _ _ _ ch3 k2
  have hd0' : denoteFEnv s₃.store.dropScratch fe₀ = some env₀ := by
    rw [hpi]; exact denoteFEnv_pext (PExt.dropScratch hb.check.state.wf) hp0 hd0
  obtain ⟨hp, ht, -, hpe, hden, hco⟩ := promoteNew_stored hsrc (PMemoPi.empty _ _) hcoh0 hp0
    hch4.coh hch4.pushed hch4.tpushed rfl rfl hd0' g4
  exact ⟨hp, ht, hden, hpe, hco⟩

/-- con-leche: ConLeche/Cached/StoredInstall.lean:251-267 storedInstall — the formers consed:
each capability record's specification reads no environment. -/
theorem consBlockInds_frame {p₁ : Arena.BlockShape} {p₁P : ConLeche.BlockShape} {isRec : Bool} :
    ∀ (cvs : List IConstantVal) (i : Nat) (fe r : IFEnv) (s s' : AState),
      CheckOK false Env.empty feE s → dShape s.store p₁ = some p₁P →
      Arena.consBlockInds p₁ isRec cvs i fe s = .ok (r, s') → CoreStep Env.empty feE s s' := by
  intro cvs
  induction cvs with
  | nil =>
    intro i fe r s s' hok _ hrun
    simp only [Arena.consBlockInds] at hrun
    obtain ⟨-, rfl⟩ := AM.pure_ok hrun
    exact CoreStep.refl hok
  | cons c rest ih =>
    intro i fe r s s' hok hp hrun
    simp only [Arena.consBlockInds] at hrun
    obtain ⟨caps, s₁, g1, r1⟩ := AM.bind_ok hrun
    obtain ⟨c1, -⟩ := blockCapsAt_spec feE p₁ p₁P i isRec s s₁ caps hok hp g1
    exact c1.trans (ih _ _ _ _ _ c1.ok (dShape_ext c1.ext _ _ hp) r1)

/-- con-leche: ConLeche/Cached/StoredInstall.lean:251-267 storedInstall — a block the
recogniser reads. -/
theorem storedParts_frame {mode : CheckMode} {fe r : IFEnv} {p₀ : Arena.BlockParts}
    {pP : ConLeche.BlockParts} {s s' : AState} (hb : Bdy s) (hp : dParts s.store p₀ = some pP)
    (hrun : storedParts mode fe p₀ s = .ok (r, s')) :
    BStep s s' ∧ s'.caches = Caches.empty ∧
      ∀ env, IFEnvCoh fe → PersIFEnv fe → denoteFEnv s.store fe = some env →
        StoredOut fe r s'.store := by
  simp only [storedParts] at hrun
  have hq := hp
  simp only [dParts, Option.map_eq_some_iff] at hq
  obtain ⟨q, hq, -⟩ := hq
  obtain ⟨hms, -, -, -, hsP, -, -⟩ := dShape_inv hq
  obtain ⟨g, s₀, g0, r0⟩ := AM.bind_ok hrun
  obtain ⟨rfl, rfl⟩ := AM.pure_ok g0
  obtain ⟨hcl, r0⟩ := AM.dguard_ok AM.Never.fail_any r0
  replace r0 := AM.pure_bind_ok r0
  have hcl' : s₀.store.scratchOn = false := by simpa using hcl
  split at r0
  · exact absurd r0 (AM.Never.fail _ _ _ _)
  · obtain ⟨⟨cvTs, s0⟩, s₁, g1, r1⟩ := AM.bind_ok r0
    obtain ⟨h1, hu⟩ := storedFormers_frame _ _ _ _ _ _ _ _ hb hcl' hms ⟨_, hsP⟩ g1
    obtain ⟨u, hu⟩ := hu
    have hq1 := dShape_ext h1.ext _ _ hq
    obtain ⟨p, s₂, g2, r2⟩ := AM.bind_ok r1
    obtain ⟨c2, hq2⟩ := BlockShape.withSort_spec feE p₀.shape q s0 u s₁ s₂ p h1.step.bdy.check
      ⟨hq1, hu⟩ g2
    obtain ⟨isRec, s₃, g3, r3⟩ := AM.bind_ok r2
    obtain ⟨c3, -⟩ := blockRawRec_spec p₀ pP s₂ s₃ isRec c2.ok.state
      (dParts_ext (h1.ext.trans c2.ext) _ _ hp) g3
    have c3' := c3.toCore c2.ok
    dsimp only at r3
    obtain ⟨fe₁, s₄, g4, r4⟩ := AM.bind_ok r3
    have c4 := consBlockInds_frame _ _ _ _ _ _ c3'.ok (dShape_ext c3'.ext _ _ hq2) g4
    have h2 : BStep s₁ s₄ := h1.step.bdy.step (c2.trans (c3'.trans c4))
    obtain ⟨gs, s₅, g5, r5⟩ := AM.bind_ok r4
    have h5 := storedGuardsAll_frame _ _ _ _ h2.bdy g5
    obtain ⟨h6, hc6, hout⟩ := storedTail_frame h5.bdy r5
    refine ⟨h1.step.trans (h2.trans (h5.trans h6)), hc6, ?_⟩
    intro env hco hpe hd
    exact hout fe env hco hpe (consBlockInds_chain _ _ _ _ _ _ (PushChain.refl hco) g4) rfl rfl
      (denoteFEnv_pext (h1.step.trans (h2.trans h5)).pext hpe hd)

/-! ## The pinned arm: handles of a closed store are persistent -/

/-- con-leche: none — what denotes in a closed store is persistent. -/
theorem persN_of_closed {st : NStore} (h : st.scratchOn = false) {i : NIdx} {x : ConLeche.Name}
    (hd : denoteN st i = some x) : PersN i := by
  cases hp : i.isPersistent with
  | true => exact hp
  | false => exact absurd hd (denoteN_scr_off h hp)

theorem persNList_of_closed {st : NStore} (h : st.scratchOn = false) :
    ∀ {ns : List NIdx} {xs : List ConLeche.Name}, Frontend.denoteNList st ns = some xs →
      PersNList ns := by
  intro ns
  induction ns with
  | nil => intro _ _ n hn; exact absurd hn (by simp)
  | cons a as ih =>
    intro xs hd n hn
    simp only [Frontend.denoteNList] at hd
    split at hd
    · rename_i x ys h1 h2
      rcases List.mem_cons.mp hn with rfl | hn
      · exact persN_of_closed h h1
      · exact ih h2 n hn
    · exact nomatch hd

theorem persE_of_closed {st : EStore} (h : st.scratchOn = false) {i : EIdx} {x : Expr}
    (hd : denoteE st i = some x) : PersE i := by
  cases hp : i.isPersistent with
  | true => exact hp
  | false => exact absurd hd (denoteE_scr_off h hp)

theorem persEList_of_closed {st : EStore} (h : st.scratchOn = false) :
    ∀ {es : List EIdx} {xs : List Expr}, Frontend.denoteEList st es = some xs → PersEList es := by
  intro es
  induction es with
  | nil => intro _ _ n hn; exact absurd hn (by simp)
  | cons a as ih =>
    intro xs hd n hn
    simp only [Frontend.denoteEList] at hd
    split at hd
    · rename_i x ys h1 h2
      rcases List.mem_cons.mp hn with rfl | hn
      · exact persE_of_closed h h1
      · exact ih h2 n hn
    · exact nomatch hd

theorem persLList_of_closed {st : LStore} (h : st.scratchOn = false) :
    ∀ {us : List LIdx} {xs : List Level}, denoteLList st us = some xs → PersLList us := by
  intro us
  induction us with
  | nil => intro _ _ n hn; exact absurd hn (by simp)
  | cons a as ih =>
    intro xs hd n hn
    simp only [denoteLList] at hd
    cases h1 : denoteL st a with
    | none => simp [h1, opt2] at hd
    | some x =>
      cases h2 : denoteLList st as with
      | none => simp [h1, h2, opt2] at hd
      | some ys =>
        rcases List.mem_cons.mp hn with rfl | hn
        · cases hp : n.isPersistent with
          | true => exact hp
          | false => exact absurd h1 (denoteL_scr_off h hp)
        · exact ih h2 n hn

/-- con-leche: none — a stored header denoting in a closed store is persistent. -/
theorem persCV_of_closed {st : EStore} (h : st.scratchOn = false) (hs : st.ScratchSync)
    {cv : IConstantVal} {c : ConstantVal} (hd : Frontend.denoteCV st cv = some c) : PersCV cv := by
  obtain ⟨h1, h2, h3⟩ := denoteCV_inv hd
  have hn : st.ns.scratchOn = false := by rw [← hs.ns]; exact h
  exact ⟨persN_of_closed hn h1, persNList_of_closed hn h2, persE_of_closed h h3⟩

/-- con-leche: none — a stored constant denoting in a closed store is persistent. -/
theorem persCI_of_closed {st : EStore} (h : st.scratchOn = false) (hs : st.ScratchSync)
    {ci : IConstantInfo} {c : ConstantInfo} (hd : Frontend.denoteCI st ci = some c) : PersCI ci := by
  have hn : st.ns.scratchOn = false := by rw [← hs.ns]; exact h
  have hl : st.ls.scratchOn = false := by rw [← hs.ls]; exact h
  have rules : ∀ {rs : List IRecRule} {xs : List RecRule}, Frontend.denoteRules st rs = some xs →
      PersRules rs := by
    intro rs
    induction rs with
    | nil => intro _ _ r hr; exact absurd hr (by simp)
    | cons a as ih =>
      intro xs hr r hm
      simp only [Frontend.denoteRules] at hr
      split at hr
      · rename_i x ys h1 h2
        rcases List.mem_cons.mp hm with rfl | hm
        · simp only [Frontend.denoteRule] at h1
          split at h1
          · rename_i c' f' r' h3 h4 h5
            refine ⟨persN_of_closed hn h3, ?_, persE_of_closed h h5⟩
            cases hf : r.fire with
            | plain => trivial
            | nested lv pn =>
              rw [hf] at h4
              simp only [Frontend.denoteFire] at h4
              split at h4
              · rename_i l1 p1 h6 h7
                exact ⟨persLList_of_closed hl h6, persEList_of_closed h h7⟩
              · exact nomatch h4
          · exact nomatch h1
        · exact ih h2 r hm
      · exact nomatch hr
  cases ci with
  | axiomInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨cv, h1, -⟩ := hd
    exact persCV_of_closed h hs h1
  | thmInfo v =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨cv, h1, -⟩ := hd
    exact persCV_of_closed h hs h1
  | ctorInfo v a b =>
    simp only [Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨cv, h1, -⟩ := hd
    exact persCV_of_closed h hs h1
  | defnInfo v e hh =>
    simp only [Frontend.denoteCI] at hd
    split at hd
    · rename_i cv x h1 h2
      exact ⟨persCV_of_closed h hs h1, persE_of_closed h h2⟩
    · exact nomatch hd
  | indInfo v c' =>
    simp only [Frontend.denoteCI] at hd
    split at hd
    · rename_i cv x h1 h2
      refine ⟨persCV_of_closed h hs h1, ?_⟩
      simp only [Frontend.denoteCaps] at h2
      split at h2
      · rename_i ct all ctors h3 h4 h5
        exact ⟨persN_of_closed hn h3, persNList_of_closed hn h4, persNList_of_closed hn h5⟩
      · exact nomatch h2
    · exact nomatch hd
  | recInfo v a b rs =>
    simp only [Frontend.denoteCI] at hd
    split at hd
    · rename_i cv x h1 h2
      exact ⟨persCV_of_closed h hs h1, rules h2⟩
    · exact nomatch hd

/-- con-leche: none — a persistent constant pushed onto a persistent index. -/
theorem PersIFEnv.push {fe : IFEnv} (h : PersIFEnv fe) {ci : IConstantInfo} (hc : PersCI ci) :
    PersIFEnv (fe.push ci) where
  env := by
    intro c hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hc
    · exact h.env c hm
  idx := by
    intro n p hp
    simp only [IFEnv.push, Std.HashMap.getElem?_insert] at hp
    split at hp
    · rename_i hb
      obtain rfl : ci.name = n := by simpa using hb
      obtain rfl := Option.some.inj hp
      exact ⟨persCI_name hc, hc⟩
    · exact h.idx n p hp
  tables := h.tables
  tbls := h.tbls

/-- con-leche: ConLeche/Cached/StoredInstall.lean:251-267 storedInstall — the pinned arm's
pushes, the store closed. -/
theorem storedOut_basis {st : EStore} (hcl : st.scratchOn = false) (hs : st.ScratchSync) :
    ∀ (ds : List IConstantInfo) (xs : List ConstantInfo) (fe₀ fe : IFEnv) (env : Env),
      PushChain fe₀ fe → PersIFEnv fe → denoteFEnv st fe = some env →
      Frontend.denoteCIList st ds = some xs →
      PushChain fe₀ (ds.foldl IFEnv.push fe) ∧ PersIFEnv (ds.foldl IFEnv.push fe) ∧
        ∃ env', denoteFEnv st (ds.foldl IFEnv.push fe) = some env' := by
  intro ds
  induction ds with
  | nil => intro _ _ fe env hc hp hd _; exact ⟨hc, hp, env, hd⟩
  | cons a as ih =>
    intro xs fe₀ fe env hc hp hd hl
    obtain ⟨x, ys, hx, hys, rfl⟩ := denoteCIList_cons hl
    exact ih ys fe₀ (fe.push a) _ (hc.push a) (hp.push (persCI_of_closed hcl hs hx))
      (denoteFEnv_push hd hx) hys

/-- con-leche: ConLeche/Cached/StoredInstall.lean:251-267 storedInstall — **the stored install
of a block, with nothing known of `fe`**; and what it pushed when `fe` is known. -/
theorem storedInstall_frame {mode : CheckMode} {fe r : IFEnv} {block : List IConstantInfo}
    {nP : Nat} {b : List ConstantInfo} {s s' : AState} (hb : Bdy s)
    (hd : Frontend.denoteCIList s.store block = some b)
    (hrun : storedInstall mode fe block nP s = .ok (r, s')) :
    BStep s s' ∧
      ∀ env, IFEnvCoh fe → PersIFEnv fe → denoteFEnv s.store fe = some env →
        StoredOut fe r s'.store := by
  simp only [storedInstall] at hrun
  obtain ⟨k, s₁, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hst1, hx1, hc1, hp1, -⟩ := basisPinHit_run hb.check.state hd g1
  have h1 : BStep s s₁ := hb.step ⟨hb.check.mono hst1 hx1 hc1 hp1, hx1, hp1⟩
  cases k with
  | some kind =>
    simp only at r1
    obtain ⟨decls, s₂, g2, r2⟩ := AM.bind_ok r1
    obtain ⟨hst2, hx2, hc2, hp2, hden2⟩ := BasisKind.declsA_run h1.bdy.check.state g2
    have h2 : BStep s₁ s₂ := h1.bdy.step ⟨h1.bdy.check.mono hst2 hx2 hc2 hp2, hx2, hp2⟩
    obtain ⟨g, s₃, g3, r3⟩ := AM.bind_ok r2
    obtain ⟨rfl, rfl⟩ := AM.pure_ok g3
    obtain ⟨hcl, r3⟩ := AM.dguard_ok AM.Never.fail_any r3
    replace r3 := AM.pure_bind_ok r3
    have hcl' : s₃.store.scratchOn = false := by simpa using hcl
    obtain ⟨-, r4⟩ := AM.dguard_ok (AM.Never.fail _) r3
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r4
    refine ⟨h1.trans h2, fun env hco hpe hde => ?_⟩
    obtain ⟨hch, hpe', env', hden⟩ := storedOut_basis hcl' h2.bdy.check.state.wf.scratchSync
      decls _ fe fe env (PushChain.refl hco) hpe
      (denoteFEnv_pext (h1.trans h2).pext hpe hde) hden2
    exact ⟨hch.pushed, hch.tpushed, ⟨env', hden⟩, hpe', fun _ => hch.coh⟩
  | none =>
    simp only at r1
    obtain ⟨o, s₂, g2, r2⟩ := AM.bind_ok r1
    obtain ⟨c2, hq⟩ := blockParts?_spec feE nP block b s₁ s₂ o h1.bdy.check
      (denoteCIList_mono hx1 _ _ hd) g2
    have h2 : BStep s₁ s₂ := h1.bdy.step c2
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok r2
      refine ⟨h1.trans h2, fun env hco hpe hde => ?_⟩
      exact StoredOut.refl hco hpe (denoteFEnv_pext (h1.trans h2).pext hpe hde)
    | some p₀ =>
      obtain ⟨pP, -, hp⟩ := hq
      obtain ⟨h3, -, hout⟩ := storedParts_frame h2.bdy hp r2
      refine ⟨h1.trans (h2.trans h3), fun env hco hpe hde => ?_⟩
      exact hout env hco hpe (denoteFEnv_pext (h1.trans h2).pext hpe hde)

/-! ## A step, and the fold -/

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:121-127 installStepG -/
theorem installBlockStep_frame {mode : CheckMode} {i : Nat} {fe fe' : IFEnv}
    {D D' : Array BlockCheck} {block : List IConstantInfo} {nP : Nat} {b : List ConstantInfo}
    {s s' : AState} (hb : Bdy s) (hd : Frontend.denoteCIList s.store block = some b)
    (hrun : installBlockStep mode i fe D block nP s = .ok ((fe', D'), s')) :
    BStep s s' ∧ s'.caches = Caches.empty ∧
      D' = D.push ⟨fe, block, nP, i,
        (fe'.env.consts.take (fe'.env.consts.length - fe.env.consts.length)).reverse,
        (fe'.env.tables.take (fe'.env.tables.length - fe.env.tables.length)).reverse⟩ ∧
      ∀ env, IFEnvCoh fe → PersIFEnv fe → denoteFEnv s.store fe = some env →
        StoredOut fe fe' s'.store := by
  simp only [installBlockStep] at hrun
  obtain ⟨_, s₁, g1, r1⟩ := AM.bind_ok hrun
  obtain rfl : s₁ = { s with caches := Caches.empty } := (Prod.mk.inj (Except.ok.inj g1)).2.symm
  obtain ⟨fe₂, s₂, g2, r2⟩ := AM.bind_ok r1
  have hb1 : Bdy { s with caches := Caches.empty } :=
    Bdy.of_empty hb.check.state.wf rfl
      (hb.check.pins.pmono hb.persPins (PExt.refl _) rfl) (hb.persPins.mono rfl)
  obtain ⟨h1, hout⟩ := storedInstall_frame hb1 hd g2
  obtain ⟨_, s₃, g3, r3⟩ := AM.bind_ok r2
  obtain rfl : s₃ = { s₂ with caches := Caches.empty } := (Prod.mk.inj (Except.ok.inj g3)).2.symm
  obtain ⟨hv, rfl⟩ := AM.pure_ok r3
  simp only [Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl⟩ := hv
  have hb3 : Bdy { s₂ with caches := Caches.empty } :=
    Bdy.of_empty h1.bdy.check.state.wf rfl
      (h1.bdy.check.pins.pmono h1.bdy.persPins (PExt.refl _) rfl) (h1.bdy.persPins.mono rfl)
  exact ⟨⟨hb3, h1.pext, h1.pins⟩, rfl, rfl, fun env hco hpe hde => hout env hco hpe hde⟩

/-- con-leche: ConLeche/Cached/Installed.lean:139-177 installStepC — **a non-block step, with
nothing known of the environment**: whatever the body did, it is framed, and the promotion
is unconditional. -/
theorem installStep_frame {mode : CheckMode} {pins : List INatOpPinSet} {i : Nat} {fe fe' : IFEnv}
    {pend pend' : Array PendingCheck} {pd : IDeclaration} {s s' : AState} (hb : Bdy s)
    (hrun : installStep mode pins i fe pend pd s = .ok ((fe', pend'), s')) :
    BStep s s' ∧ s'.caches = Caches.empty := by
  simp only [installStep] at hrun
  obtain ⟨_, s₁, g1, r1⟩ := AM.bind_ok hrun
  obtain rfl : s₁ = { s with caches := Caches.empty } := (Prod.mk.inj (Except.ok.inj g1)).2.symm
  obtain ⟨_, s₂, g2, r2⟩ := AM.bind_ok r1
  obtain rfl := enterScratch_inv g2
  obtain ⟨⟨fe₁, vg?⟩, s₃, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨t₁, -, -, rfl⟩ := scratchRun_ok g3
  have hsrc := PSrc.of_bracket hb t₁.store
  dsimp only at r3
  cases vg? with
  | none =>
    simp only at r3
    obtain ⟨⟨m, fe₂⟩, s₄, g4, r4⟩ := AM.bind_ok r3
    obtain ⟨hs4, -, hx4, hf4⟩ := promoteNew_frame hsrc (PMemoPi.empty _ _) g4
    obtain ⟨_, s₅, g5, r5⟩ := AM.bind_ok r4
    obtain rfl := dropScratch_inv g5
    obtain ⟨-, rfl⟩ := AM.pure_ok r5
    exact ⟨Bdy.close hb hs4.piWF hx4 hf4.pins, rfl⟩
  | some vg =>
    simp only at r3
    obtain ⟨⟨m, vg'⟩, s₄, g4, r4⟩ := AM.bind_ok r3
    obtain ⟨hs4, hm4, hx4, hf4, -⟩ := promoteVG_pi hsrc (PMemoPi.empty _ _) g4
    obtain ⟨⟨m', fe₂⟩, s₅, g5, r5⟩ := AM.bind_ok r4
    obtain ⟨hs5, -, hx5, hf5⟩ := promoteNew_frame hs4 hm4 g5
    obtain ⟨_, s₆, g6, r6⟩ := AM.bind_ok r5
    obtain rfl := dropScratch_inv g6
    obtain ⟨-, rfl⟩ := AM.pure_ok r6
    exact ⟨Bdy.close hb hs5.piWF (hx4.trans hx5) (by rw [hf5.pins, hf4.pins]), rfl⟩

/-- con-leche: ConLeche/Cached/Installed.lean:179-200 installDeclStep — **phase A's step, with
nothing known of the environment**. -/
theorem installDeclStep_frame {mode : CheckMode} {pins : List INatOpPinSet}
    {p p' : Nat × IFEnv × Array PendingCheck × Array BlockCheck} {pd : IDeclaration}
    {d : Declaration} {s s' : AState} (hb : Bdy s)
    (hd : Frontend.denoteDecl s.store pd = some d)
    (hrun : installDeclStep mode pins p pd s = .ok (.ok p', s')) :
    BStep s s' ∧ s'.caches = Caches.empty ∧
      ∀ b ∈ p.2.2.2.toList, b ∈ p'.2.2.2.toList := by
  simp only [installDeclStep] at hrun
  cases hP : andPinOk pd s with
  | error e => rw [hP] at hrun; simp at hrun
  | ok w =>
    obtain ⟨bA, s₀⟩ := w
    obtain ⟨hst0, hx0, hc0, hp0⟩ := andPinOk_run hb.check.state hb.check.pins hd hP
    have h0 : BStep s s₀ := hb.step ⟨hb.check.mono hst0 hx0 hc0 hp0, hx0, hp0⟩
    rw [hP] at hrun
    cases bA with
    | false => simp at hrun
    | true =>
      simp only at hrun
      cases pd with
      | indDecl block nP =>
        simp only at hrun
        cases hA : installBlockStep mode p.1 p.2.1 p.2.2.2 block nP s₀ with
        | error e => rw [hA] at hrun; simp at hrun
        | ok v =>
          obtain ⟨⟨fe', D'⟩, s₁⟩ := v
          rw [hA] at hrun
          simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
          obtain ⟨b, hb', -⟩ := hd
          obtain ⟨h1, hc1, hD, -⟩ := installBlockStep_frame h0.bdy
            (denoteCIList_mono hx0 _ _ hb') hA
          refine ⟨h0.trans h1, hc1, fun x hx => ?_⟩
          simp only [hD, Array.toList_push, List.mem_append]
          exact Or.inl hx
      | _ =>
        all_goals
          simp only at hrun
          cases hA : installStep mode pins p.1 p.2.1 p.2.2.1 _ s₀ with
          | error e => rw [hA] at hrun; simp at hrun
          | ok v =>
            obtain ⟨⟨fe', pend'⟩, s₁⟩ := v
            rw [hA] at hrun
            simp only [Except.ok.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl⟩ := hrun
            obtain ⟨h1, hc1⟩ := installStep_frame h0.bdy hA
            exact ⟨h0.trans h1, hc1, fun x hx => hx⟩

/-- con-leche: ConLeche/Cached/Installed.lean:450-455 checkDecls (phase A) — **phase A's frame,
with nothing known of any environment**: an accepting fold is a persistent extension, and
every block job recorded stays recorded.  What it needs is only that the records denote. -/
theorem installFold_frame {mode : CheckMode} {pins : List INatOpPinSet} :
    ∀ (ds : List IDeclaration) (dsP : List Declaration)
      (p p' : Nat × IFEnv × Array PendingCheck × Array BlockCheck) (s s' : AState),
      Bdy s → (∀ x ∈ ds, PersDecl x) → denoteDecls s.store ds = some dsP →
      installFold mode pins p ds s = .ok (.ok p', s') →
      BStep s s' ∧ (ds ≠ [] → s'.caches = Caches.empty) ∧
        ∀ b ∈ p.2.2.2.toList, b ∈ p'.2.2.2.toList := by
  intro ds
  induction ds with
  | nil =>
    intro dsP p p' s s' hb _ _ hrun
    simp only [installFold] at hrun
    obtain ⟨h, rfl⟩ := AM.pure_ok hrun
    obtain rfl := Except.ok.inj h
    exact ⟨BStep.refl hb, fun h => absurd rfl h, fun _ h => h⟩
  | cons a as ih =>
    intro dsP p p' s s' hb hpd hden hrun
    simp only [denoteDecls] at hden
    cases ha : Frontend.denoteDecl s.store a with
    | none => rw [ha] at hden; simp at hden
    | some x =>
      cases has : denoteDecls s.store as with
      | none => rw [ha, has] at hden; simp at hden
      | some xs =>
        simp only [installFold] at hrun
        obtain ⟨r1, s₁, hstep, htail⟩ := AM.bind_ok hrun
        cases r1 with
        | error e =>
          obtain ⟨hbad, -⟩ := AM.pure_ok htail
          exact nomatch hbad
        | ok p₁ =>
          simp only at htail
          obtain ⟨h1, hc1, hD1⟩ := installDeclStep_frame hb ha hstep
          have hpd₁ : ∀ c ∈ as, PersDecl c := fun c hc => hpd c (by simp [hc])
          obtain ⟨h2, hc2, hD2⟩ := ih xs p₁ p' s₁ s' h1.bdy hpd₁
            (denoteDecls_pext h1.pext as xs hpd₁ has) htail
          refine ⟨h1.trans h2, fun _ => ?_, fun b hb' => hD2 b (hD1 b hb')⟩
          by_cases hnil : as = []
          · subst hnil
            simp only [installFold] at htail
            obtain ⟨-, rfl⟩ := AM.pure_ok htail
            exact hc1
          · exact hc2 hnil

end ConRon.Bridge

/-
# `ConRon.Bridge.Checker.Job` — a block job, as evidence for its step

`Arena.blockCheck` runs a block's checked install at the view (`fe` as the block found
it) and compares what it pushed with what the stored install pushed.  This module turns
an accepted job into con-leche's pure step at the environment `fe` denotes: the view IS
`fe`, so `Arena.checkDecl_bridge` applies as it stands, at any store that extends the
persistent tier `fe` lives in.  The comparison is pointer-first, and a handle comparison
is an equation of handles, so what the job pushed and what the stored install pushed are
one list.
-/
module

public import ConRon.Bridge.Checker.Frame
public import ConRon.Bridge.Checker.Fold
public import ConRon.Bridge.Checker.Decl
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Specs

public section

open ConLeche ConRon.Arena

namespace ConRon.Bridge

set_option autoImplicit false

/-! ## The comparison is an equation -/

/-- con-leche: ConLeche/Cached/StoredInstall.lean:62-65 eq_of_listBeqBy — element-wise
comparison by a comparison that implies equality. -/
theorem eq_of_listBeqBy {α : Type} {f : α → α → Bool} (hf : ∀ a b, f a b = true → a = b) :
    ∀ {xs ys : List α}, listBeqBy f xs ys = true → xs = ys := by
  intro xs
  induction xs with
  | nil => intro ys h; cases ys <;> first | rfl | exact nomatch h
  | cons a as ih =>
    intro ys h
    cases ys with
    | nil => exact nomatch h
    | cons b bs =>
      simp only [listBeqBy, Bool.and_eq_true] at h
      rw [hf a b h.1, ih h.2]

/-- con-leche: ConLeche/Cached/StoredInstall.lean:76-77 ConstantVal.eq_of_beqP -/
theorem IConstantVal.eq_of_beqP {a b : IConstantVal} (h : a.beqP b = true) : a = b := by
  obtain ⟨n, l, t⟩ := a
  obtain ⟨n', l', t'⟩ := b
  simp only [IConstantVal.beqP, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  rfl

/-- con-leche: ConLeche/Cached/StoredInstall.lean:87-90 RecRuleFire.eq_of_beqP -/
theorem IRecRuleFire.eq_of_beqP {a b : IRecRuleFire} (h : a.beqP b = true) : a = b := by
  cases a <;> cases b <;> simp_all [IRecRuleFire.beqP]

/-- con-leche: ConLeche/Cached/StoredInstall.lean:96-98 RecRule.eq_of_beqP -/
theorem IRecRule.eq_of_beqP {a b : IRecRule} (h : a.beqP b = true) : a = b := by
  obtain ⟨c, n, p, f, r, k, e⟩ := a
  obtain ⟨c', n', p', f', r', k', e'⟩ := b
  simp only [IRecRule.beqP, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hf⟩, rfl⟩, rfl⟩, rfl⟩ := h
  rw [IRecRuleFire.eq_of_beqP hf]

/-- con-leche: ConLeche/Cached/StoredInstall.lean:109-117 ConstantInfo.eq_of_beqP -/
theorem IConstantInfo.eq_of_beqP {a b : IConstantInfo} (h : a.beqP b = true) : a = b := by
  cases a <;> cases b <;> simp only [IConstantInfo.beqP, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, Bool.false_eq_true] at h
  all_goals
    first
    | (rw [IConstantVal.eq_of_beqP h])
    | (obtain ⟨⟨h1, rfl⟩, rfl⟩ := h; rw [IConstantVal.eq_of_beqP h1])
    | (obtain ⟨h1, rfl⟩ := h; rw [IConstantVal.eq_of_beqP h1])
    | (obtain ⟨⟨⟨h1, rfl⟩, rfl⟩, h2⟩ := h
       rw [IConstantVal.eq_of_beqP h1,
         eq_of_listBeqBy (fun _ _ => IRecRule.eq_of_beqP) h2])

/-- con-leche: ConLeche/Cached/StoredInstall.lean:132-135 ProjTable.eq_of_beqP -/
theorem IProjTable.eq_of_beqP {a b : IProjTable} (h : a.beqP b = true) : a = b := by
  obtain ⟨n, l, p, c, f, s, bs, g⟩ := a
  obtain ⟨n', l', p', c', f', s', bs', g'⟩ := b
  simp only [IProjTable.beqP, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
  rfl

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:90-103 blockCheck_ok — **the job's
comparison, read**: what the job pushed past the view is what the stored install
pushed. -/
theorem pushesAgree_eq {view W' : IFEnv} {L : List IConstantInfo} {Q : List IProjTable}
    (hc : Pushed view W') (ht : TPushed view W')
    (h : pushesAgree view W' L Q = true) :
    W'.env.consts = L.reverse ++ view.env.consts ∧
      W'.env.tables = Q.reverse ++ view.env.tables := by
  obtain ⟨nc, hnc⟩ := hc
  obtain ⟨nt, hnt⟩ := ht
  simp only [pushesAgree, Bool.and_eq_true] at h
  have h1 := eq_of_listBeqBy (fun _ _ => IConstantInfo.eq_of_beqP) h.1
  have h2 := eq_of_listBeqBy (fun _ _ => IProjTable.eq_of_beqP) h.2
  rw [hnc] at h1
  rw [hnt] at h2
  simp only [List.length_append, Nat.add_sub_cancel, List.take_left'] at h1 h2
  rw [← h1, ← h2, hnc, hnt]
  simp

/-! ## `FoldOK` at a later store -/

/-- con-leche: none — **`FoldOK` survives any persistent extension onto a state with
empty caches and the same pins**: everything it names is persistent. -/
theorem FoldOK.pmono {env : Env} {fe : IFEnv} {s s' : AState} (h : FoldOK env fe s)
    (hx : PExt s.store s'.store) (hwf : StoreWF s'.store) (hc : s'.caches = Caches.empty)
    (hp : s'.pins = s.pins) : FoldOK env fe s' where
  check :=
    { state := ⟨hwf⟩
      caches := CacheOK.of_empty hc
      pins := h.check.pins.pmono h.persPins hx hp
      ienv := h.check.ienv.pmono h.persEnv hx }
  envWF := h.envWF
  tblShape := h.tblShape
  persPins := h.persPins.mono hp
  persEnv := h.persEnv
  coh := h.coh
  denote := denoteFEnv_pext hx h.persEnv h.denote

/-- con-leche: none — `FoldOK` at a boundary is `FoldOK` at the bracket opened on any later
state, the caches empty. -/
theorem FoldOK.enterAt {env : Env} {fe : IFEnv} {s w : AState} (h : FoldOK env fe s)
    (hx : PExt s.store w.store) (hwf : StoreWF w.store) (hc : w.caches = Caches.empty)
    (hp : w.pins = s.pins) :
    FoldOK env fe
      ({ store := w.store.enableScratch, memos := Memos.empty, caches := w.caches,
         pins := w.pins } : AState) :=
  h.pmono (hx.trans (PExt.enterScratch hwf)) (EStore.enableScratch_spec hwf).1 hc hp

/-! ## The block job -/

/-- con-leche: ConLeche/Verify/Cached/Defer.lean:142-166 installDeclStep_defer — **an accepted
block job is the pure step at the environment `fe` denotes**, pushing what the stored
install pushed.  `w` is any state over the persistent tier `fe` lives in, with empty
caches; the answer is at the store the job's install ended in, which extends `w`'s. -/
theorem Arena.blockCheck_bridge {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {env : Env} {fe : IFEnv} {s w t : AState} {block : List IConstantInfo}
    {b : List ConstantInfo} {nP pos : Nat} {L : List IConstantInfo} {Q : List IProjTable}
    (hk : CoreSpec Arena.checkFuel) (hind : IndSpec) (hok : FoldOK env fe s)
    (hx : PExt s.store w.store) (hwf : StoreWF w.store) (hc : w.caches = Caches.empty)
    (hp : w.pins = s.pins) (hpp : PersPinSets pins) (hpins : PinsDenote s.store pins pinsP)
    (hb : Frontend.denoteCIList w.store block = some b) (hbp : ∀ c ∈ block, PersCI c)
    (hrun : blockCheck .verified pins ⟨fe, block, nP, pos, L, Q⟩ w = .ok ((), t)) :
    ∃ st env' F, PExt w.store st ∧
      denoteIEnv st ⟨L.reverse ++ fe.env.consts, Q.reverse ++ fe.env.tables⟩ = some env' ∧
      ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pinsP env (.indDecl b nP)
        = .ok env' ∧
      EnvWF env' ∧ (∀ t' ∈ Q, IProjTableOK t') := by
  have hwfE := hwf
  unfold blockCheck at hrun
  obtain ⟨_, S, g1, r1⟩ := AM.bind_ok hrun
  obtain rfl := enterScratch_inv g1
  obtain ⟨W', s₂, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨S₂, hS₂, -, rfl⟩ := scratchRun_ok g2
  have hokS := hok.enterAt hx hwf hc hp
  have hxS : PExt w.store w.store.enableScratch := PExt.enterScratch hwfE
  have hpinsS : PinsDenote w.store.enableScratch pins pinsP :=
    PinsDenote.pmono (hx.trans hxS) _ _ hpp hpins
  have hd : Frontend.denoteDecl w.store.enableScratch (.indDecl block nP) = some (.indDecl b nP) := by
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff]
    exact ⟨b, denoteCIList_pext hxS _ _ hbp hb, rfl⟩
  have hout := Arena.checkDecl_bridge hk hind hokS hpinsS hd hS₂
  obtain ⟨hagree, -⟩ := AM.dunless_ok AM.Never.fail_any r2
  obtain ⟨hC, hT⟩ := pushesAgree_eq hout.pushed hout.tpushed hagree
  obtain ⟨env', F, hden, hF⟩ := hout.run
  have hdenI : denoteIEnv S₂.store ⟨L.reverse ++ fe.env.consts, Q.reverse ++ fe.env.tables⟩
      = some env' := by
    rw [← hC, ← hT]
    exact hden
  refine ⟨S₂.store, env', F, hxS.trans (PExt.of_ext hout.ext), hdenI, hF,
    hout.envWF env' hden, fun t' ht' => ?_⟩
  have hmem : t' ∈ W'.env.tables := by rw [hT]; simp [ht']
  rcases hout.proj t' hmem with hold | hnew
  · exact hok.tblShape t' hold
  · exact hnew

end ConRon.Bridge

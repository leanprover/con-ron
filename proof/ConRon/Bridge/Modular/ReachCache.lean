/-
# `ConRon.Bridge.Modular.ReachCache` — the reach's caches, Theorem 1 (task #166)

The reach's caches over handles against upstream's over names: a map keyed by parts
(`MRel` at `PKRel`), by names (`HMRel`), each value read back.  The twin's caches are a mirror
of upstream's, key for key: every lookup of the twin hits where upstream's does, so the caches
are related entry by entry (`CacheRel`) and every read of a part answers as upstream's.  The
regions' memos are related through the snapshot's values only: the twin's memo good
(`SMGood`), upstream's good (`SM.Good`), at the same region.

A simulation in the run style (`Bridge/Frontend/Olean/Closure.lean`'s), not a `vcgen` walk.
-/
module

public import ConRon.Bridge.Modular.Rel
public import ConRon.Bridge.Modular.Graph
public import ConRon.Bridge.Modular.ReadsParts
public import ConRon.Bridge.Modular.Worker
public import ConRon.Bridge.Frontend.Olean.Sparse
public import ConRon.Bridge.Frontend.Olean.Files
public import ConLeche.Verify.Driver.ReachFrom
public import ConLeche.Verify.Driver.Loads
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean
open ConRon.Arena.Frontend.Olean (OleanPins SM)
open ConRon.Arena.Frontend.Olean (LvState levelsGo)
open ConLeche.Frontend.Olean (Region Roots OLeanLevel ModFiles ImportF ImportRec bind_some_left CKindF Copy)

theorem arenaPartKey_beq_iff (a b : ConRon.Arena.Modular.PartKey) : (a == b) = true ↔ a = b := by
  cases a; cases b
  show (_ && _) = true ↔ _
  simp

instance : LawfulBEq ConRon.Arena.Modular.PartKey where
  eq_of_beq h := (arenaPartKey_beq_iff _ _).1 h
  rfl := (arenaPartKey_beq_iff _ _).2 rfl

/-! ## Keys and spots -/

/-- con-leche: ConLeche/Driver/Reach.lean:163-167 PartKey — a part key read back. -/
@[expose] def PKRel (st : EStore) (k : ConRon.Arena.Modular.PartKey)
    (kC : ConLeche.Driver.PartKey) : Prop :=
  denoteN st.ns k.mod = some kC.mod ∧ k.level = kC.level

theorem PKRel.ext {st st' : EStore} (hx : Ext st st') {k : ConRon.Arena.Modular.PartKey}
    {kC : ConLeche.Driver.PartKey} (h : PKRel st k kC) : PKRel st' k kC :=
  ⟨denoteN_ext h.1 hx, h.2⟩

theorem PKRel.inj {st : EStore} (hw : NStoreWF st.ns) {k k' : ConRon.Arena.Modular.PartKey}
    {kC : ConLeche.Driver.PartKey} (h : PKRel st k kC) (h' : PKRel st k' kC) : k = k' := by
  obtain ⟨m, l⟩ := k
  obtain ⟨m', l'⟩ := k'
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  simp only at h1 h2 h1' h2'
  rw [denoteN_inj hw h1 h1', h2, h2']

theorem PKRel.func {st : EStore} {k : ConRon.Arena.Modular.PartKey}
    {kC kC' : ConLeche.Driver.PartKey} (h : PKRel st k kC) (h' : PKRel st k kC') : kC = kC' := by
  obtain ⟨m, l⟩ := kC
  obtain ⟨m', l'⟩ := kC'
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  simp only at h1 h2 h1' h2'
  rw [Option.some.inj (h1.symm.trans h1'), ← h2, ← h2']

/-- con-leche: ConLeche/Driver/Reach.lean:169-172 Spot — a copy's spot read back. -/
@[expose] def SpotRel (st : EStore) (s : ConRon.Arena.Modular.Spot) (sC : ConLeche.Driver.Spot) :
    Prop :=
  PKRel st s.part sC.part ∧ NPRel st s.pos sC.pos

theorem SpotRel.ext {st st' : EStore} (hx : Ext st st') {s : ConRon.Arena.Modular.Spot}
    {sC : ConLeche.Driver.Spot} (h : SpotRel st s sC) : SpotRel st' s sC :=
  ⟨h.1.ext hx, h.2.ext hx⟩

/-! ## Maps keyed by parts -/

/-- con-leche: none — **a map over part keys against one over upstream's**: each entry's key
read back as one of the other's, the values related. -/
structure MRel {α β : Type} (R : α → β → Prop) (st : EStore)
    (M : Std.HashMap ConRon.Arena.Modular.PartKey α) (MC : Std.HashMap ConLeche.Driver.PartKey β) :
    Prop where
  fwd : ∀ k a, M[k]? = some a → ∃ kC b, PKRel st k kC ∧ MC[kC]? = some b ∧ R a b
  bwd : ∀ kC b, MC[kC]? = some b → ∃ k a, PKRel st k kC ∧ M[k]? = some a ∧ R a b

theorem MRel.empty {α β : Type} (R : α → β → Prop) (st : EStore) : MRel R st {} {} :=
  ⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩

theorem MRel.ext {α β : Type} {R R' : α → β → Prop} {st st' : EStore}
    {M : Std.HashMap ConRon.Arena.Modular.PartKey α} {MC : Std.HashMap ConLeche.Driver.PartKey β}
    (h : MRel R st M MC) (hx : Ext st st') (hr : ∀ a b, R a b → R' a b) : MRel R' st' M MC :=
  ⟨fun k a hk => let ⟨kC, b, h1, h2, h3⟩ := h.fwd k a hk; ⟨kC, b, h1.ext hx, h2, hr _ _ h3⟩,
   fun kC b hk => let ⟨k, a, h1, h2, h3⟩ := h.bwd kC b hk; ⟨k, a, h1.ext hx, h2, hr _ _ h3⟩⟩

/-- A lookup answers alike. -/
theorem MRel.get {α β : Type} {R : α → β → Prop} {st : EStore} (hw : NStoreWF st.ns)
    {M : Std.HashMap ConRon.Arena.Modular.PartKey α} {MC : Std.HashMap ConLeche.Driver.PartKey β}
    (h : MRel R st M MC) {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey}
    (hk : PKRel st k kC) : Option.Rel R M[k]? MC[kC]? := by
  generalize hm : M[k]? = o
  cases o with
  | some a =>
    obtain ⟨kC', b, h1, h2, h3⟩ := h.fwd k a hm
    obtain rfl := hk.func h1
    rw [h2]
    exact .some h3
  | none =>
    cases hc : MC[kC]? with
    | none => exact .none
    | some b =>
      obtain ⟨k', a, h1, h2, _⟩ := h.bwd kC b hc
      obtain rfl := h1.inj hw hk
      rw [hm] at h2
      cases h2

theorem MRel.contains {α β : Type} {R : α → β → Prop} {st : EStore} (hw : NStoreWF st.ns)
    {M : Std.HashMap ConRon.Arena.Modular.PartKey α} {MC : Std.HashMap ConLeche.Driver.PartKey β}
    (h : MRel R st M MC) {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey}
    (hk : PKRel st k kC) : M.contains k = MC.contains kC := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.contains_eq_isSome_getElem?]
  rcases optRel_cases (h.get hw hk) with ⟨h1, h2⟩ | ⟨a, b, h1, h2, -⟩
  · rw [h1, h2]; rfl
  · rw [h1, h2]; rfl

theorem MRel.insert {α β : Type} {R : α → β → Prop} {st : EStore} (hw : NStoreWF st.ns)
    {M : Std.HashMap ConRon.Arena.Modular.PartKey α} {MC : Std.HashMap ConLeche.Driver.PartKey β}
    (h : MRel R st M MC) {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey}
    (hk : PKRel st k kC) {a : α} {b : β} (hr : R a b) :
    MRel R st (M.insert k a) (MC.insert kC b) := by
  constructor
  · intro x a' hx
    rw [Std.HashMap.getElem?_insert] at hx
    by_cases he : k = x
    · subst he
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hx
      subst hx
      exact ⟨kC, b, hk, by simp, hr⟩
    · simp only [beq_iff_eq, he, ↓reduceIte] at hx
      obtain ⟨xC, b', h1, h2, h3⟩ := h.fwd x a' hx
      have hn : ¬ kC = xC := fun hn => he (hk.inj hw (hn ▸ h1))
      exact ⟨xC, b', h1, by simp [Std.HashMap.getElem?_insert, hn, h2], h3⟩
  · intro xC b' hn
    rw [Std.HashMap.getElem?_insert] at hn
    by_cases he : kC = xC
    · subst he
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hn
      subst hn
      exact ⟨k, a, hk, by simp, hr⟩
    · simp only [beq_iff_eq, he, ↓reduceIte] at hn
      obtain ⟨x, a', h1, h2, h3⟩ := h.bwd xC b' hn
      have hx : ¬ k = x := fun hx => he (hk.func (hx ▸ h1))
      exact ⟨x, a', h1, by simp [Std.HashMap.getElem?_insert, hx, h2], h3⟩

theorem MRel.erase {α β : Type} {R : α → β → Prop} {st : EStore} (hw : NStoreWF st.ns)
    {M : Std.HashMap ConRon.Arena.Modular.PartKey α} {MC : Std.HashMap ConLeche.Driver.PartKey β}
    (h : MRel R st M MC) {k : ConRon.Arena.Modular.PartKey} {kC : ConLeche.Driver.PartKey}
    (hk : PKRel st k kC) : MRel R st (M.erase k) (MC.erase kC) := by
  constructor
  · intro x a' hx
    rw [Std.HashMap.getElem?_erase] at hx
    by_cases he : k = x
    · subst he; simp at hx
    · simp only [beq_iff_eq, he, ↓reduceIte] at hx
      obtain ⟨xC, b', h1, h2, h3⟩ := h.fwd x a' hx
      have hn : ¬ kC = xC := fun hn => he (hk.inj hw (hn ▸ h1))
      exact ⟨xC, b', h1, by simp [Std.HashMap.getElem?_erase, hn, h2], h3⟩
  · intro xC b' hn
    rw [Std.HashMap.getElem?_erase] at hn
    by_cases he : kC = xC
    · subst he; simp at hn
    · simp only [beq_iff_eq, he, ↓reduceIte] at hn
      obtain ⟨x, a', h1, h2, h3⟩ := h.bwd xC b' hn
      have hx : ¬ k = x := fun hx => he (hk.func (hx ▸ h1))
      exact ⟨x, a', h1, by simp [Std.HashMap.getElem?_erase, hx, h2], h3⟩

/-! ## Shared pieces (copies of L6a's, to be deduplicated when its files build) -/

/-- con-leche: none — **the loads' indices hold only the loaded modules**, on both sides: what
makes the loads' relation survive the store's growth (`LoadsRel.ext'`). -/
@[expose] def LoadKeys (ld : ConRon.Arena.Frontend.Olean.HeaderLoads)
    (ldC : ConLeche.Frontend.Olean.HeaderLoads) : Prop :=
  (∀ (h : NIdx) (k : Nat), ld.index[h]? = some k → h ∈ ld.order.toList) ∧
    (∀ (n : ConLeche.Name) (k : Nat), ldC.index[n]? = some k → ldC.order[k]? = some n)

theorem foldIdx_keysR :
    ∀ (l : List NIdx) (M : Std.HashMap NIdx Nat) (i : Nat) (h : NIdx) (j : Nat),
      (l.foldl (fun (acc : Std.HashMap NIdx Nat × Nat) m => (acc.1.insert m acc.2, acc.2 + 1))
        (M, i)).1[h]? = some j → h ∈ l ∨ (M[h]?).isSome = true
  | [], M, i, h, j, hj => .inr (by simp at hj; simp [hj])
  | m :: l, M, i, h, j, hj => by
    rw [List.foldl_cons] at hj
    rcases foldIdx_keysR l _ _ h j hj with hh | hh
    · exact .inl (List.mem_cons_of_mem _ hh)
    · rw [Std.HashMap.getElem?_insert] at hh
      split at hh
      · rename_i he
        obtain rfl := eq_of_beq he
        exact .inl List.mem_cons_self
      · exact .inr hh

/-- The loads' relation at a larger store. -/
theorem loadsRel_extR {st st' : EStore} (hx : Ext st st') (hw' : NStoreWF st'.ns)
    {ld : ConRon.Arena.Frontend.Olean.HeaderLoads} {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    (h : LoadsRel st ld ldC) (hk : LoadKeys ld ldC) : LoadsRel st' ld ldC := by
  refine ⟨NR_list_ext hx h.order, h.flags,
    listRel_ext (fun _ _ hi => ImpsD.ext hx hi) h.imports, fun a n hd => ?_⟩
  rcases hdo : denoteN st.ns a with _ | n₀
  · have h1 : ld.index[a]? = none := by
      cases hi : ld.index[a]? with
      | none => rfl
      | some k =>
        obtain ⟨b, -, hab⟩ := listRel_memL h.order (hk.1 a k hi)
        have hab' : denoteN st.ns a = some b := hab
        rw [hdo] at hab'; cases hab'
    have h2 : ldC.index[n]? = none := by
      cases hi : ldC.index[n]? with
      | none => rfl
      | some k =>
        have ho := hk.2 n k hi
        rcases optRel_cases (listRel_getElem? h.order k) with ⟨g1, g2⟩ | ⟨b₁, c₁, g1, g2, g3⟩
        · rw [Array.getElem?_toList] at g2; rw [ho] at g2; cases g2
        · rw [Array.getElem?_toList] at g2; rw [ho] at g2; cases g2
          have g3' : denoteN st.ns b₁ = some n := g3
          have := denoteN_inj hw' (denoteN_ext g3' hx) hd
          subst this
          rw [hdo] at g3'; cases g3'
    rw [h1, h2]
  · have := denoteN_ext hdo hx
    rw [hd] at this
    cases this
    exact h.index a _ hdo

/-- con-leche: ConLeche/Verify/Driver/Loads.lean:669 headerFixpoint_sound — `headerFixpoint_run`,
upstream's run given from any open handles. -/
theorem headerFixpoint_givesR {pk : OleanPins} {F : FS} {sp : Roots} (hsp : sp.bare = sp)
    {isM : Bool} {imps : Array (ImportF NIdx)} {impsC : Array ImportRec}
    {ld : ConRon.Arena.Frontend.Olean.HeaderLoads} {s s' : AState} (hctx : Ctx pk s)
    (hi : imps.toList.mapM (denoteImport s.store) = some impsC.toList)
    (h : ConRon.Arena.Frontend.Olean.headerFixpoint (modelFs F) pk sp isM imps s = .ok (ld, s')) :
    ParseStep s s' ∧ ∃ ldC, ModelIO.Gives
      (ConLeche.Frontend.Olean.headerFixpoint (ConLeche.Frontend.Olean.moduleImports sp) isM impsC :
        ModelIO _) F (.ok ldC) ∧ LoadsRel s'.store ld ldC ∧ LoadKeys ld ldC := by
  unfold ConRon.Arena.Frontend.Olean.headerFixpoint at h
  obtain ⟨x, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨hv, hs⟩ := AM.pure_ok h2
  subst hv hs
  obtain ⟨hst, xC, hG, hR⟩ := levelsGo_run hsp _ _ _ _ _ {} hctx (ofImports_rel _ hi)
    ⟨HMRel.empty _ _, SetRel.empty _, .nil, HMRel.empty _ _⟩ h1
  have hC : ModelIO.Gives
      (ConLeche.Frontend.Olean.headerFixpoint (ConLeche.Frontend.Olean.moduleImports sp) isM impsC :
        ModelIO _) F (.ok
      { order := xC.order, flags := xC.order.map fun m => (xC.flags[m]?).getD default,
        imports := xC.order.map fun m => (xC.imports[m]?).getD #[],
        index := xC.order.foldl (fun (acc : Std.HashMap ConLeche.Name Nat × Nat) m =>
          (acc.1.insert m acc.2, acc.2 + 1)) ({}, 0) |>.1 }) := by
    unfold ConLeche.Frontend.Olean.headerFixpoint
    dsimp only
    refine hG.bind ?_
    exact ModelIO.gives_pure _ _
  obtain ⟨-, -, hnd, -, hkC⟩ := ConLeche.Driver.headerFixpoint_sound hC.canGive
  refine ⟨hst, _, hC, ofState_rel (nsWF_of_StateOK hst.ok) hR hnd, fun h k hk => ?_, hkC⟩
  have := ofStateGo_index x.flags x.order.toList 0 x.imports #[] #[] {}
  unfold ConRon.Arena.Frontend.Olean.HeaderLoads.ofState at hk ⊢
  generalize ConRon.Arena.Frontend.Olean.HeaderLoads.ofStateGo x.flags x.order.toList 0 x.imports
    #[] #[] {} = r at this hk
  obtain ⟨fl, is, ix⟩ := r
  simp only at this hk ⊢
  subst this
  rcases foldIdx_keysR _ _ _ _ _ hk with h | h
  · exact h
  · simp at h

theorem denoteStmt_partsR {st : EStore} {c : ConRon.Arena.Frontend.Olean.StmtRec} {z : ConstantVal}
    (h : denoteStmt st c = some z) :
    denoteN st.ns c.name = some z.name ∧ c.levelParams.mapM (denoteN st.ns) = some z.levelParams ∧
      denoteE st c.type = some z.type := by
  simp only [denoteStmt] at h
  obtain ⟨a, ha, h⟩ := bind_some_left h
  obtain ⟨b, hb, h⟩ := bind_some_left h
  obtain ⟨c', hc, h⟩ := bind_some_left h
  simp only [pure, Option.some.injEq] at h
  subst h
  exact ⟨ha, hb, hc⟩

theorem denoteStmt_extR {st st' : EStore} (hx : Ext st st') {c : ConRon.Arena.Frontend.Olean.StmtRec}
    {z : ConstantVal} (h : denoteStmt st c = some z) : denoteStmt st' c = some z := by
  obtain ⟨h1, h2, h3⟩ := denoteStmt_partsR h
  simp only [denoteStmt, denoteN_ext h1 hx, mapM_denoteN_ext hx h2, denote_ext h3 hx]
  rcases z with ⟨a, b, c⟩; rfl

end ConRon.Bridge.Modular

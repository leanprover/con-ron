/-
# `ConRon.Bridge.Modular.Copies` — a compared challenge's copies, Theorem 1 (task #166)

**An accepting twin `copiesOk` is upstream's `copiesOk` accepting the denoted values**
(`copiesOk_run`), and the twin's `copyRecs` denotes upstream's (`copyRecs_run`).  The run style
of `Bridge/Frontend/Olean/*` (one theorem per twin function, its state step `CStep`): the
records' names through `constsD_run` (`declNames_cstep`), the owner map against upstream's
(`ownerMap_run`, `HMRel`), each copy's comparison through the existing tests' theorems
(`sameCvUpToLevels_run`, `IConstantInfo.atLps_run`, `readBlock_run`, `recsRead_bridge`).  A copied
block's recursors read against one layer of the context's constants (the twin's `ctxLayer`);
upstream reads them off the record `ownerMap` names (`ctxConst`): one lookup, as the context's
names are distinct (`hnd`, upstream's `WorkerFacts.nodup`).
-/
module

public import ConRon.Bridge.Modular.Rel
public import ConRon.Bridge.Checker.Install
public import ConRon.Bridge.Compare.Justify
public import ConRon.Bridge.Inductives.IotaRead
public import ConRon.Bridge.Inductives.BlockShape
public import ConRon.Bridge.Inductives.XFreeIota
import ConRon.Bridge.Checker.Names
import ConLeche.Verify.Cached.IndWalksC
import ConLeche.Verify.Cached.IotaReadC
import ConLeche.Verify.Cached.DeclNames
import ConRon.Bridge.Inductives.PosWalks
import Std.Data.HashMap.Lemmas

public section

namespace ConRon.Bridge.Modular

set_option autoImplicit false

/-- A run that ends in a failure gives no accept. -/
macro "no_accept" h:ident : tactic => `(tactic| (exfalso; repeat (first
  | exact AM.fail_ok $h
  | (have hb_tmp := AM.bind_ok $h; clear $h; obtain ⟨_, _, k_na, $h:ident⟩ := hb_tmp;
     first | exact AM.fail_ok k_na | skip)
  | split at $h:ident)))

/-- The `pure ()` binds a `do` block's `if … then return …` leaves, peeled. -/
macro "peel_pure" h:ident : tactic => `(tactic| repeat (first
  | (have hb_tmp := AM.bind_ok $h; clear $h; obtain ⟨_, _, k_pp, $h:ident⟩ := hb_tmp;
     obtain ⟨-, hs_pp⟩ := AM.pure_ok k_pp; rw [hs_pp] at $h:ident)))

open ConLeche ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend
open ConRon.Bridge.Frontend.Olean ConRon.Bridge.Inductives
open ConLeche.Frontend.Olean (Copy CKindF)

/-! ## The state step -/

/-- con-leche: none — **a step of the copies' check**: the driver's invariant kept, the store
extended, the pins unmoved. -/
structure CStepW (s s' : AState) : Prop where
  ok : DriverOK s'
  ext : Ext s.store s'.store
  pins : s'.pins = s.pins

/-- con-leche: none — `CStepW`, the scratch flag unmoved too. -/
structure CStep (s s' : AState) : Prop extends CStepW s s' where
  scr : s'.store.scratchOn = s.store.scratchOn

theorem CStepW.refl {s : AState} (hok : DriverOK s) : CStepW s s := ⟨hok, Ext.refl _, rfl⟩

theorem CStepW.trans {a b c : AState} (h₁ : CStepW a b) (h₂ : CStepW b c) : CStepW a c :=
  ⟨h₂.ok, h₁.ext.trans h₂.ext, by rw [h₂.pins, h₁.pins]⟩

theorem CStep.refl {s : AState} (hok : DriverOK s) : CStep s s := ⟨CStepW.refl hok, rfl⟩

theorem CStep.trans {a b c : AState} (h₁ : CStep a b) (h₂ : CStep b c) : CStep a c :=
  ⟨h₁.toCStepW.trans h₂.toCStepW, by rw [h₂.scr, h₁.scr]⟩

theorem CStep.of_rstep {s s' : AState} (hok : DriverOK s) (h : RStep s s') : CStep s s' :=
  ⟨⟨hok.of_rstep h, h.ext, h.pins⟩, h.scratch⟩

theorem CStep.of_pstep {s s' : AState} (hok : DriverOK s) (h : Inductives.PStep s s')
    (hsc : s'.store.scratchOn = s.store.scratchOn) : CStep s s' :=
  ⟨⟨hok.of_pstep h, h.ext, h.pins⟩, hsc⟩

/-- con-leche: none — a record that is not an inductive block. -/
@[expose] def NotInd (d : Declaration) : Prop := ∀ b n, d ≠ .indDecl b n

theorem notInd_den {st : EStore} {d : IDeclaration} {dC : Declaration}
    (hd : Frontend.denoteDecl st d = some dC) (h : ∀ b n, d ≠ .indDecl b n) : NotInd dC := by
  intro b n he
  subst he
  cases d with
  | indDecl b' n' => exact h b' n' rfl
  | axiomDecl v => simp [Frontend.denoteDecl] at hd
  | quotDecl k v => simp [Frontend.denoteDecl] at hd
  | defnDecl v e hh => simp only [Frontend.denoteDecl] at hd; split at hd <;> simp at hd
  | thmDecl v e => simp only [Frontend.denoteDecl] at hd; split at hd <;> simp at hd
  | opaqueDecl v e => simp only [Frontend.denoteDecl] at hd; split at hd <;> simp at hd

/-! ## What a record installs, at any scratch flag -/

/-- con-leche: ConLeche/Kernel/Install.lean:80-98 declConstants — **what a record installs,
denoted** (`constsSpec`, the scratch flag kept rather than asked off, and nothing asked of the
record's persistence). -/
theorem constsD_run {s s' : AState} {pd : IDeclaration} {d : Declaration} {L : List IConstantInfo}
    (hok : DriverOK s) (hd : Frontend.denoteDecl s.store pd = some d)
    (hrun : declConstants pd s = .ok (L, s')) :
    CStep s s' ∧ Frontend.denoteCIList s'.store L = some (ConLeche.declConstants d) := by
  have hwf := hok.state.wf
  cases pd with
  | defnDecl v e hint =>
    simp only [Frontend.denoteDecl] at hd
    split at hd
    · rename_i cv x hcv hx
      cases hd
      simp only [Arena.declConstants] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨CStep.refl hok, by
        simp [Frontend.denoteCIList, Frontend.denoteCI, hcv, hx, ConLeche.declConstants]⟩
    · cases hd
  | thmDecl v e =>
    simp only [Frontend.denoteDecl] at hd
    split at hd
    · rename_i cv x hcv hx
      cases hd
      simp only [Arena.declConstants] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨CStep.refl hok, by
        simp [Frontend.denoteCIList, Frontend.denoteCI, hcv, ConLeche.declConstants]⟩
    · cases hd
  | opaqueDecl v e =>
    simp only [Frontend.denoteDecl] at hd
    split at hd
    · rename_i cv x hcv hx
      cases hd
      simp only [Arena.declConstants] at hrun
      obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
      exact ⟨CStep.refl hok, by
        simp [Frontend.denoteCIList, Frontend.denoteCI, hcv, ConLeche.declConstants]⟩
    · cases hd
  | axiomDecl v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hcv, rfl⟩ := hd
    obtain ⟨hnm, -, -⟩ := denoteCV_inv hcv
    simp only [Arena.declConstants, declConstantsAxiom] at hrun
    obtain ⟨qs, s1, g1, r1⟩ := AM.bind_ok hrun
    obtain ⟨rfl, d1⟩ := pinAt_run (x := ConLeche.quotSoundName) hok.pins rfl g1
    have hqs : (v.name == qs) = true ↔ cv.name = ConLeche.quotSoundName :=
      beq_handle_iff hwf hnm d1
    rcases AM.ite_ok r1 with ⟨hyes, k⟩ | ⟨hno, k⟩
    · obtain ⟨ci, s2, g2, k2⟩ := AM.bind_ok k
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
      obtain ⟨hr, hci⟩ := quotAt_run hok.state hok.readOK hcv g2
      exact ⟨CStep.of_rstep hok hr, by
        simp [Frontend.denoteCIList, hci, ConLeche.declConstants, hqs.mp hyes]⟩
    · obtain ⟨sa, s2, g2, r2⟩ := AM.bind_ok k
      obtain ⟨rfl, d2⟩ := pinAt_run (x := ConLeche.sorryAxName) hok.pins rfl g2
      have hsa : (v.name == sa) = true ↔ cv.name = ConLeche.sorryAxName :=
        beq_handle_iff hwf hnm d2
      have hq : ¬ cv.name = ConLeche.quotSoundName := fun h => hno (hqs.mpr h)
      rcases AM.ite_ok r2 with ⟨hy2, k3⟩ | ⟨hn2, k3⟩
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
        have hq' : ¬ ConLeche.sorryAxName = ConLeche.quotSoundName := hsa.mp hy2 ▸ hq
        exact ⟨CStep.refl hok, by
          simp [Frontend.denoteCIList, ConLeche.declConstants, hsa.mp hy2, hq']⟩
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok k3
        have hs : ¬ cv.name = ConLeche.sorryAxName := fun h => hn2 (hsa.mpr h)
        exact ⟨CStep.refl hok, by
          simp [Frontend.denoteCIList, Frontend.denoteCI, hcv, ConLeche.declConstants, hq, hs]⟩
  | quotDecl k v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hcv, rfl⟩ := hd
    simp only [Arena.declConstants] at hrun
    obtain ⟨ci, s2, g2, k2⟩ := AM.bind_ok hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
    obtain ⟨hr, hci⟩ := quotAt_run hok.state hok.readOK hcv g2
    exact ⟨CStep.of_rstep hok hr, by simp [Frontend.denoteCIList, hci, ConLeche.declConstants]⟩
  | indDecl block nP =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨b, hb, rfl⟩ := hd
    simp only [Arena.declConstants] at hrun
    obtain ⟨q, s2, g2, k2⟩ := AM.bind_ok hrun
    obtain ⟨hp2, hsc2, hq⟩ := readBlock_installS hok hb g2
    have c2 := CStep.of_pstep hok hp2 hsc2
    cases q with
    | error e =>
      simp only [ROp, Except.toOption] at hq
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
      obtain ⟨e', he'⟩ := Inductives.toOption_eq_none hq
      exact ⟨c2, by simp [Frontend.denoteCIList, ConLeche.declConstants, he']⟩
    | ok p =>
      simp only [ROp, Except.toOption] at hq
      obtain ⟨pP, hpP, hdp⟩ := hq
      obtain ⟨hp3, hsc3, hL⟩ := blockConstants_run c2.ok.state c2.ok.pins c2.ok.readOK.readL hdp k2
      exact ⟨c2.trans (CStep.of_pstep c2.ok hp3 hsc3), by
        simp [ConLeche.declConstants, Inductives.toOption_eq_some hpP, hL]⟩

/-! ## A record's names -/

theorem denoteCIList_names {st : EStore} :
    ∀ {L : List IConstantInfo} {cs : List ConstantInfo}, Frontend.denoteCIList st L = some cs →
      Frontend.denoteNList st.ns (L.map (·.name)) = some (cs.map (·.toConstantVal.name))
  | [], cs, h => by
    simp only [Frontend.denoteCIList, Option.some.injEq] at h
    subst h; rfl
  | c :: L, cs, h => by
    simp only [Frontend.denoteCIList] at h
    cases h1 : Frontend.denoteCI st c with
    | none => rw [h1] at h; simp at h
    | some x =>
    cases h2 : Frontend.denoteCIList st L with
    | none => rw [h1, h2] at h; simp at h
    | some xs =>
    rw [h1, h2] at h
    obtain rfl := (Option.some.inj h).symm
    have hn := (denoteCV_inv (denoteCI_toConstantVal h1)).1
    have hc : c.name = c.toConstantVal.name := by cases c <;> rfl
    simp only [List.map_cons, Frontend.denoteNList, hc, hn, denoteCIList_names h2]

/-- con-leche: ConLeche/Modular.lean:98-99 declNames — **a record's names denote upstream's**. -/
theorem declNames_cstep {s s' : AState} {d : IDeclaration} {dC : Declaration} {ns : List NIdx}
    (hok : DriverOK s) (hd : Frontend.denoteDecl s.store d = some dC)
    (h : ConRon.Arena.Modular.declNames d s = .ok (ns, s')) :
    CStep s s' ∧ Frontend.denoteNList s'.store.ns ns = some (ConLeche.Modular.declNames dC) := by
  simp only [ConRon.Arena.Modular.declNames] at h
  obtain ⟨L, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
  obtain ⟨c1, hL⟩ := constsD_run hok hd h1
  exact ⟨c1, denoteCIList_names hL⟩

/-! ## The owner map -/

/-- con-leche: ConLeche/Driver/Reach.lean:869-872 ownerMap — upstream's owner map, along the
list from position `j`. -/
@[expose] def omGo : List Declaration → Nat → Std.HashMap ConLeche.Name Nat →
    Std.HashMap ConLeche.Name Nat
  | [], _, m => m
  | d :: ds, j, m => omGo ds (j + 1) ((ConLeche.Modular.declNames d).foldl (fun m y => m.insert y j) m)

theorem omGo_range (g : Declaration → Nat → Std.HashMap ConLeche.Name Nat →
    Std.HashMap ConLeche.Name Nat) (hg : ∀ d j m, g d j m =
      (ConLeche.Modular.declNames d).foldl (fun m y => m.insert y j) m) :
    ∀ (l pre : List Declaration) (m : Std.HashMap ConLeche.Name Nat),
      (List.range' pre.length l.length).foldl (fun m j => g ((pre ++ l).getD j default) j m) m =
        omGo l pre.length m
  | [], pre, m => rfl
  | d :: l, pre, m => by
    rw [List.length_cons, List.range'_succ, List.foldl_cons]
    have hget : (pre ++ d :: l).getD pre.length default = d := by simp
    rw [hget, hg]
    have := omGo_range g hg l (pre ++ [d]) ((ConLeche.Modular.declNames d).foldl
      (fun m y => m.insert y pre.length) m)
    simp only [List.length_append, List.length_singleton, List.append_assoc,
      List.singleton_append] at this
    rw [this]
    rfl

/-- Upstream's owner map is `omGo` along the records. -/
theorem ownerMap_eq (ds : Array Declaration) :
    ConLeche.Driver.ownerMap ds = omGo ds.toList 0 {} := by
  have h := omGo_range (fun d j m => (ConLeche.Modular.declNames d).foldl
    (fun m y => m.insert y j) m) (fun _ _ _ => rfl) ds.toList [] {}
  simp only [List.length_nil, List.nil_append] at h
  rw [← h, ConLeche.Driver.ownerMap, List.range_eq_range', Array.length_toList]
  congr 1
  funext m j
  simp [Array.getD_eq_getD_getElem?]

/-- One record's names inserted at one position: related maps stay related. -/
theorem insertAll_rel {st : EStore} (hw : NStoreWF st.ns) (j : Nat) :
    ∀ (ns : List NIdx) (xs : List ConLeche.Name) {M : Std.HashMap NIdx Nat}
      {MC : Std.HashMap ConLeche.Name Nat}, Frontend.denoteNList st.ns ns = some xs →
      HMRel (· = ·) st M MC →
      HMRel (· = ·) st (ns.foldl (fun m n => m.insert n j) M) (xs.foldl (fun m y => m.insert y j) MC)
  | [], xs, M, MC, h, hr => by
    simp only [Frontend.denoteNList, Option.some.injEq] at h
    subst h; exact hr
  | n :: ns, xs, M, MC, h, hr => by
    simp only [Frontend.denoteNList] at h
    cases h1 : denoteN st.ns n with
    | none => rw [h1] at h; simp at h
    | some x =>
    cases h2 : Frontend.denoteNList st.ns ns with
    | none => rw [h1, h2] at h; simp at h
    | some xs' =>
    rw [h1, h2] at h
    obtain rfl := (Option.some.inj h).symm
    exact insertAll_rel hw j ns xs' h2 (hr.insert hw h1 rfl)

/-- con-leche: ConLeche/Driver/Reach.lean:869-872 ownerMap — **the twin's owner map is
upstream's**, a map over handles against one over names. -/
theorem ownerMapGo_run :
    ∀ (ds : List IDeclaration) (dsC : List Declaration) (j : Nat)
      (M : Std.HashMap NIdx Nat) (MC : Std.HashMap ConLeche.Name Nat)
      {s s' : AState} {r : Std.HashMap NIdx Nat × Nat},
      DriverOK s →
      denoteDecls s.store ds = some dsC → HMRel (· = ·) s.store M MC →
      ds.foldlM (m := AM) (fun (acc : Std.HashMap NIdx Nat × Nat) d => do
        let ns ← ConRon.Arena.Modular.declNames d
        pure (ns.foldl (fun m n => m.insert n acc.2) acc.1, acc.2 + 1)) (M, j) s = .ok (r, s') →
      CStep s s' ∧ HMRel (· = ·) s'.store r.1 (omGo dsC j MC)
  | [], dsC, j, M, MC, s, s', r, hok, hd, hr, h => by
    simp only [denoteDecls, Option.some.injEq] at hd
    subst hd
    simp only [List.foldlM_nil] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨CStep.refl hok, hr⟩
  | d :: ds, dsC, j, M, MC, s, s', r, hok, hd, hr, h => by
    simp only [denoteDecls] at hd
    cases h1 : Frontend.denoteDecl s.store d with
    | none => rw [h1] at hd; simp at hd
    | some x =>
    cases h2 : denoteDecls s.store ds with
    | none => rw [h1, h2] at hd; simp at hd
    | some xs =>
    rw [h1, h2] at hd
    obtain rfl := (Option.some.inj hd).symm
    simp only [List.foldlM_cons] at h
    obtain ⟨acc, s₁, k1, k2⟩ := AM.bind_ok h
    obtain ⟨ns, s₂, k3, k4⟩ := AM.bind_ok k1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
    obtain ⟨c1, hns⟩ := declNames_cstep hok h1 k3
    have hw := nsWF_of_StateOK c1.ok.state
    have hr₁ := insertAll_rel hw j ns _ hns (hr.ext c1.ext (fun _ _ h => h))
    obtain ⟨c2, hr₂⟩ := ownerMapGo_run ds xs (j + 1) _ _ c1.ok
      (denoteDecls_ext c1.ext _ _ h2) hr₁ k2
    exact ⟨c1.trans c2, hr₂⟩

theorem ownerMap_run {s s' : AState} {ds : List IDeclaration} {dsC : Array Declaration}
    {M : Std.HashMap NIdx Nat}
    (hok : DriverOK s)
    (hd : denoteDecls s.store ds = some dsC.toList)
    (h : ConRon.Arena.Modular.ownerMap ds s = .ok (M, s')) :
    CStep s s' ∧ HMRel (· = ·) s'.store M (ConLeche.Driver.ownerMap dsC) := by
  simp only [ConRon.Arena.Modular.ownerMap] at h
  obtain ⟨r, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
  rw [ownerMap_eq]
  exact ownerMapGo_run ds dsC.toList 0 {} {} hok hd (HMRel.empty _ _) h1

/-! ## Which records are copies -/

theorem mapM_some_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l.length = l'.length
  | [], l', h => by simp at h; subst h; rfl
  | a :: l, l', h => by
    simp only [List.mapM_cons] at h
    cases h1 : f a with
    | none => simp [h1] at h
    | some b =>
    cases h2 : l.mapM f with
    | none => simp [h1, h2] at h
    | some bs =>
    have : l' = b :: bs := by simpa [h1, h2] using h.symm
    subst this
    simp [mapM_some_length h2]

/-- A name's membership in the index's first copies, read back. -/
theorem first_contains {st : EStore} (hw : NStoreWF st.ns)
    {ix : ConRon.Arena.Frontend.Olean.NameIndex} {ixC : ConLeche.Frontend.Olean.NameIndex}
    (hix : HMRel (· = ·) st ix.first ixC.first) {h : NIdx} {n : ConLeche.Name}
    (hd : denoteN st.ns h = some n) : ix.first.contains h = ixC.first.contains n := by
  have := hix.get_eq hw hd
  simp only [← Std.HashMap.isSome_getElem?_eq_contains, this]

theorem anyLoaded_eq {st : EStore} (hw : NStoreWF st.ns)
    {ix : ConRon.Arena.Frontend.Olean.NameIndex} {ixC : ConLeche.Frontend.Olean.NameIndex}
    (hix : HMRel (· = ·) st ix.first ixC.first) :
    ∀ (ns : List NIdx) (xs : List ConLeche.Name), Frontend.denoteNList st.ns ns = some xs →
      ConRon.Arena.Modular.anyLoaded ix ns = xs.any ixC.first.contains
  | [], xs, h => by
    simp only [Frontend.denoteNList, Option.some.injEq] at h
    subst h; rfl
  | n :: ns, xs, h => by
    simp only [Frontend.denoteNList] at h
    cases h1 : denoteN st.ns n with
    | none => rw [h1] at h; simp at h
    | some x =>
    cases h2 : Frontend.denoteNList st.ns ns with
    | none => rw [h1, h2] at h; simp at h
    | some xs' =>
    rw [h1, h2] at h
    obtain rfl := (Option.some.inj h).symm
    have ih := anyLoaded_eq hw hix ns xs' h2
    simp only [ConRon.Arena.Modular.anyLoaded, List.any_cons] at ih ⊢
    rw [first_contains hw hix h1, ih]

/-- con-leche: ConLeche/Driver/Worker.lean:124-125 loadedRec — **a copy test is upstream's**. -/
theorem loadedRec_cstep {s s' : AState} {d : IDeclaration} {dC : Declaration} {b : Bool}
    {ix : ConRon.Arena.Frontend.Olean.NameIndex} {ixC : ConLeche.Frontend.Olean.NameIndex}
    (hok : DriverOK s)
    (hd : Frontend.denoteDecl s.store d = some dC) (hix : HMRel (· = ·) s.store ix.first ixC.first)
    (h : ConRon.Arena.Modular.loadedRec ix d s = .ok (b, s')) :
    CStep s s' ∧ b = ConLeche.Driver.loadedRec ixC dC := by
  simp only [ConRon.Arena.Modular.loadedRec] at h
  obtain ⟨ns, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
  obtain ⟨c1, hns⟩ := declNames_cstep hok hd h1
  exact ⟨c1, anyLoaded_eq (nsWF_of_StateOK c1.ok.state) (hix.ext c1.ext (fun _ _ h => h)) ns _ hns⟩

theorem denoteDecls_snoc {st : EStore} {d : IDeclaration} {x : Declaration}
    (hd : Frontend.denoteDecl st d = some x) :
    ∀ {l : List IDeclaration} {lC : List Declaration}, denoteDecls st l = some lC →
      denoteDecls st (l ++ [d]) = some (lC ++ [x])
  | [], lC, h => by
    simp only [denoteDecls, Option.some.injEq] at h
    subst h; simp [denoteDecls, hd]
  | y :: ys, lC, h => by
    simp only [denoteDecls] at h
    cases hy : Frontend.denoteDecl st y with
    | none => rw [hy] at h; simp at h
    | some yC =>
    cases hys : denoteDecls st ys with
    | none => rw [hy, hys] at h; simp at h
    | some ysC =>
    rw [hy, hys] at h
    obtain rfl := (Option.some.inj h).symm
    simp [denoteDecls, hy, denoteDecls_snoc hd hys]

theorem recsLoadedGo_run {ix : ConRon.Arena.Frontend.Olean.NameIndex}
    {ixC : ConLeche.Frontend.Olean.NameIndex} (want : Bool) :
    ∀ (ds : List IDeclaration) (dsC : List Declaration) (out : Array IDeclaration)
      (outC : List Declaration) {s s' : AState} {r : Array IDeclaration},
      DriverOK s →
      denoteDecls s.store ds = some dsC → denoteDecls s.store out.toList = some outC →
      HMRel (· = ·) s.store ix.first ixC.first →
      ds.foldlM (m := AM) (fun out d => do
        if (← ConRon.Arena.Modular.loadedRec ix d) == want then pure (out.push d)
        else pure out) out s = .ok (r, s') →
      CStep s s' ∧ denoteDecls s'.store r.toList =
        some (outC ++ dsC.filter fun d => ConLeche.Driver.loadedRec ixC d == want)
  | [], dsC, out, outC, s, s', r, hok, hd, ho, _, h => by
    simp only [denoteDecls, Option.some.injEq] at hd
    subst hd
    simp only [List.foldlM_nil] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨CStep.refl hok, by simpa using ho⟩
  | d :: ds, dsC, out, outC, s, s', r, hok, hd, ho, hix, h => by
    simp only [denoteDecls] at hd
    cases h1 : Frontend.denoteDecl s.store d with
    | none => rw [h1] at hd; simp at hd
    | some x =>
    cases h2 : denoteDecls s.store ds with
    | none => rw [h1, h2] at hd; simp at hd
    | some xs =>
    rw [h1, h2] at hd
    obtain rfl := (Option.some.inj hd).symm
    simp only [List.foldlM_cons] at h
    obtain ⟨out₁, s₁, k1, k2⟩ := AM.bind_ok h
    obtain ⟨b, s₂, k3, k4⟩ := AM.bind_ok k1
    obtain ⟨c1, rfl⟩ := loadedRec_cstep hok h1 hix k3
    have hd₁ := denoteDecl_ext c1.ext h1
    have ho₁ := denoteDecls_ext c1.ext _ _ ho
    have hix₁ := hix.ext c1.ext (fun _ _ h => h)
    by_cases hb : (ConLeche.Driver.loadedRec ixC x == want) = true
    · simp only [hb, ↓reduceIte] at k4
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
      have ho₂ : denoteDecls s₁.store (out.push d).toList = some (outC ++ [x]) := by
        rw [Array.toList_push]; exact denoteDecls_snoc hd₁ ho₁
      obtain ⟨c2, hr⟩ := recsLoadedGo_run want ds xs _ _ c1.ok
        (denoteDecls_ext c1.ext _ _ h2) ho₂ hix₁ k2
      refine ⟨c1.trans c2, ?_⟩
      rw [hr]; simp [hb]
    · simp only [Bool.not_eq_true] at hb
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at k4
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
      obtain ⟨c2, hr⟩ := recsLoadedGo_run want ds xs _ _ c1.ok
        (denoteDecls_ext c1.ext _ _ h2) ho₁ hix₁ k2
      refine ⟨c1.trans c2, ?_⟩
      rw [hr]; simp [hb]

theorem recsLoaded_run {ix : ConRon.Arena.Frontend.Olean.NameIndex}
    {ixC : ConLeche.Frontend.Olean.NameIndex} (want : Bool) {ds : Array IDeclaration}
    {dsC : Array Declaration} {s s' : AState} {r : Array IDeclaration}
    (hok : DriverOK s)
    (hd : denoteDeclArray s.store ds = some dsC) (hix : HMRel (· = ·) s.store ix.first ixC.first)
    (h : ConRon.Arena.Modular.recsLoaded ix ds want s = .ok (r, s')) :
    CStep s s' ∧ denoteDeclArray s'.store r =
      some (dsC.filter fun d => ConLeche.Driver.loadedRec ixC d == want) := by
  simp only [denoteDeclArray, Option.map_eq_some_iff] at hd
  obtain ⟨l, hl, rfl⟩ := hd
  simp only [ConRon.Arena.Modular.recsLoaded, ← Array.foldlM_toList] at h
  obtain ⟨c, hr⟩ := recsLoadedGo_run want ds.toList l #[] [] hok hl rfl hix h
  refine ⟨c, ?_⟩
  simp only [denoteDeclArray, hr, List.nil_append, Option.map_some, Option.some.injEq]
  rw [← Array.toList_filter]

/-- con-leche: ConLeche/Driver/Worker.lean:132-135 copyRecs — **the copies denote upstream's**. -/
theorem copyRecs_run {ix : ConRon.Arena.Frontend.Olean.NameIndex}
    {ixC : ConLeche.Frontend.Olean.NameIndex} {x : Array (ConLeche.Frontend.Olean.ImportF NIdx)}
    {xC : Array ConLeche.Frontend.Olean.ImportRec} {ds : Array IDeclaration}
    {dsC : Array Declaration} {s s' : AState} {r : Array IDeclaration}
    (hok : DriverOK s)
    (hx : ImpsD s.store x xC)
    (hd : denoteDeclArray s.store ds = some dsC) (hix : HMRel (· = ·) s.store ix.first ixC.first)
    (h : ConRon.Arena.Modular.copyRecs x ix ds s = .ok (r, s')) :
    CStep s s' ∧ denoteDeclArray s'.store r = some (ConLeche.Driver.copyRecs xC ixC dsC) := by
  have hsz : x.isEmpty = xC.isEmpty := by
    have := mapM_some_length hx
    rw [Bool.eq_iff_iff, Array.isEmpty_iff_size_eq_zero, Array.isEmpty_iff_size_eq_zero,
      ← Array.length_toList, ← Array.length_toList, this]
  unfold ConRon.Arena.Modular.copyRecs at h
  unfold ConLeche.Driver.copyRecs
  rw [hsz] at h
  by_cases hE : xC.isEmpty = true
  · simp only [hE, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨CStep.refl hok, rfl⟩
  · simp only [Bool.not_eq_true] at hE
    simp only [hE, Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨c, hr⟩ := recsLoaded_run true hok hd hix h
    refine ⟨c, ?_⟩
    rw [hr]
    simp

/-! ## Distinct names -/

theorem namesNodupGo_tw : ∀ {s : Std.HashSet NIdx} {ns : List NIdx},
    (ConRon.Arena.Modular.namesNodupGo s ns).1 = true → ns.Nodup ∧ ∀ n ∈ ns, s.contains n = false
  | s, [], _ => ⟨List.nodup_nil, by simp⟩
  | s, n :: ns, h => by
    simp only [ConRon.Arena.Modular.namesNodupGo] at h
    split at h
    · simp at h
    · rename_i hn
      obtain ⟨h1, h2⟩ := namesNodupGo_tw h
      refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, h1⟩, fun x hx => ?_⟩
      · have := h2 n hm
        simp [Std.HashSet.contains_insert] at this
      · rcases List.mem_cons.1 hx with rfl | hx
        · simpa using hn
        · have := h2 x hx
          simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff] at this
          exact this.2

theorem namesNodupGo_of : ∀ {s : Std.HashSet ConLeche.Name} {ns : List ConLeche.Name},
    ns.Nodup → (∀ n ∈ ns, s.contains n = false) → ConLeche.Driver.namesNodupGo s ns = true
  | s, [], _, _ => rfl
  | s, n :: ns, hnd, hs => by
    simp only [ConLeche.Driver.namesNodupGo, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨hs n (List.mem_cons_self ..), namesNodupGo_of (List.nodup_cons.1 hnd).2 ?_⟩
    intro x hx
    simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    refine ⟨fun he => (List.nodup_cons.1 hnd).1 (he ▸ hx), hs x (List.mem_cons_of_mem _ hx)⟩

theorem denoteNList_mem_c {st : NStore} :
    ∀ {ns : List NIdx} {xs : List ConLeche.Name}, Frontend.denoteNList st ns = some xs →
      ∀ x ∈ xs, ∃ n ∈ ns, denoteN st n = some x
  | [], xs, h, x, hx => by
    simp only [Frontend.denoteNList, Option.some.injEq] at h
    subst h; simp at hx
  | n :: ns, xs, h, x, hx => by
    simp only [Frontend.denoteNList] at h
    cases h1 : denoteN st n with
    | none => rw [h1] at h; simp at h
    | some y =>
    cases h2 : Frontend.denoteNList st ns with
    | none => rw [h1, h2] at h; simp at h
    | some ys =>
    rw [h1, h2] at h
    obtain rfl := (Option.some.inj h).symm
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨n, List.mem_cons_self .., h1⟩
    · obtain ⟨m, hm, hd⟩ := denoteNList_mem_c h2 x hx
      exact ⟨m, List.mem_cons_of_mem _ hm, hd⟩

theorem denoteNList_nodup_c {st : NStore} (hw : NStoreWF st) :
    ∀ {ns : List NIdx} {xs : List ConLeche.Name}, Frontend.denoteNList st ns = some xs →
      ns.Nodup → xs.Nodup
  | [], xs, h, _ => by
    simp only [Frontend.denoteNList, Option.some.injEq] at h
    subst h; exact List.nodup_nil
  | n :: ns, xs, h, hnd => by
    simp only [Frontend.denoteNList] at h
    cases h1 : denoteN st n with
    | none => rw [h1] at h; simp at h
    | some y =>
    cases h2 : Frontend.denoteNList st ns with
    | none => rw [h1, h2] at h; simp at h
    | some ys =>
    rw [h1, h2] at h
    obtain rfl := (Option.some.inj h).symm
    refine List.nodup_cons.2 ⟨fun hy => ?_, denoteNList_nodup_c hw h2 (List.nodup_cons.1 hnd).2⟩
    obtain ⟨m, hm, hd⟩ := denoteNList_mem_c h2 y hy
    have : m = n := denoteN_inj hw hd h1
    subst this
    exact (List.nodup_cons.1 hnd).1 hm

/-- con-leche: ConLeche/Driver/Worker.lean:100-103 namesNodupGo — **an accepting twin test is
upstream's accept**, from the empty set. -/
theorem namesNodupGo_run {st : NStore} (hw : NStoreWF st) {ns : List NIdx}
    {xs : List ConLeche.Name} (h : Frontend.denoteNList st ns = some xs)
    (hb : (ConRon.Arena.Modular.namesNodupGo {} ns).1 = true) :
    ConLeche.Driver.namesNodupGo {} xs = true :=
  namesNodupGo_of (denoteNList_nodup_c hw h (namesNodupGo_tw hb).1) (fun _ _ => by simp)

/-! ## The block tests -/

theorem ctors3_names {st : EStore} :
    ∀ {cs : List (IConstantVal × Nat × Nat)} {q : List (ConstantVal × Nat × Nat)},
      denoteCtors3 st cs = some q →
      Frontend.denoteNList st.ns (cs.map (·.1.name)) = some (q.map (·.1.name))
  | [], q, h => by
    simp only [denoteCtors3, Option.some.injEq] at h
    subst h; rfl
  | (cv, a, b) :: cs, q, h => by
    simp only [denoteCtors3] at h
    cases h1 : Frontend.denoteCV st cv with
    | none => rw [h1] at h; simp at h
    | some c =>
    cases h2 : denoteCtors3 st cs with
    | none => rw [h1, h2] at h; simp at h
    | some qs =>
    rw [h1, h2] at h
    obtain rfl := (Option.some.inj h).symm
    simp only [List.map_cons, Frontend.denoteNList, (denoteCV_inv h1).1, ctors3_names h2]

/-- con-leche: ConLeche/Driver/Worker.lean:176-188 blockReadB — **an accepting twin test is
upstream's**. -/
theorem blockReadB_run {s s' : AState} {d : IDeclaration} {dC : Declaration} {b : Bool}
    (hok : DriverOK s)
    (hd : Frontend.denoteDecl s.store d = some dC)
    (h : ConRon.Arena.Modular.blockReadB d s = .ok (b, s')) :
    CStep s s' ∧ (b = true → ConLeche.Driver.blockReadB dC = true) := by
  cases d with
  | indDecl block nP =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨bC, hbC, rfl⟩ := hd
    simp only [ConRon.Arena.Modular.blockReadB] at h
    obtain ⟨r, s₁, h1, h2⟩ := AM.bind_ok h
    obtain ⟨hp1, hsc1, hro⟩ := readBlock_installS hok hbC h1
    have c1 := CStep.of_pstep hok hp1 hsc1
    cases r with
    | error e =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      exact ⟨c1, fun h => nomatch h⟩
    | ok p =>
      obtain ⟨pC, hpC, hdp⟩ := hro
      have hrb : ConLeche.readBlock nP bC = .ok pC := by
        cases hr : ConLeche.readBlock nP bC with
        | error e => rw [hr] at hpC; simp [Except.toOption] at hpC
        | ok q => rw [hr] at hpC; simp only [Except.toOption, Option.some.injEq] at hpC; rw [hpC]
      have hw := nsWF_of_StateOK c1.ok.state
      have hnames := dCtors_names (BlockShape.allCtors_spec hdp)
      simp only at h2
      split at h2
      · obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
        exact ⟨c1, fun h => nomatch h⟩
      · rename_i hnd
        simp only [Bool.not_eq_true', Bool.not_eq_false] at hnd
        have hndC := namesNodupGo_run hw hnames hnd
        have hsp := blockSplit_spec s.store block bC hbC
        cases hs : Arena.blockSplit block with
        | none =>
          rw [hs] at h2 hsp
          obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
          refine ⟨c1, fun _ => ?_⟩
          simp only [ROp] at hsp
          simp [ConLeche.Driver.blockReadB, hrb, hndC, hsp]
        | some sp =>
          rw [hs] at h2 hsp
          obtain ⟨tys, cs, rs⟩ := sp
          obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
          obtain ⟨q, hq, -, hcs, -⟩ := hsp
          have hcsn := ctors3_names (denoteCtors3_ext c1.ext _ _ hcs)
          refine ⟨c1, fun hb => ?_⟩
          rw [denoteNList_beq c1.ok.state.wf hnames hcsn] at hb
          simp [ConLeche.Driver.blockReadB, hrb, hndC, hq, hb]
  | _ =>
    simp only [ConRon.Arena.Modular.blockReadB] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    refine ⟨CStep.refl hok, fun _ => ?_⟩
    have hni := notInd_den hd (by intro b n h; cases h)
    cases dC <;> first | rfl | exact absurd rfl (hni _ _)

theorem listBeqBy_refl {α : Type} {f : α → α → Bool} (hf : ∀ a, f a a = true) :
    ∀ l : List α, ConLeche.listBeqBy f l l = true
  | [] => rfl
  | a :: l => by simp [ConLeche.listBeqBy, hf a, listBeqBy_refl hf l]

/-- con-leche: ConLeche/Driver/Worker.lean:171-174 copyRecEq — **an accepting twin test is
upstream's**: equal handles denote equal records. -/
theorem copyRecEq_run {st : EStore} {d e : IDeclaration} {dC eC : Declaration}
    (hd : Frontend.denoteDecl st d = some dC) (he : Frontend.denoteDecl st e = some eC)
    (h : ConRon.Arena.Modular.copyRecEq d e = true) : ConLeche.Driver.copyRecEq dC eC = true := by
  cases d with
  | indDecl b n =>
    cases e with
    | indDecl b' n' =>
      simp only [ConRon.Arena.Modular.copyRecEq, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd he
      obtain ⟨bC, hb, rfl⟩ := hd
      obtain ⟨bC', hb', rfl⟩ := he
      rw [hb] at hb'
      obtain rfl := Option.some.inj hb'
      simp only [ConLeche.Driver.copyRecEq, beq_self_eq_true, Bool.true_and]
      exact listBeqBy_refl (fun a => by rw [ConstantInfo.beqP_eq]; exact beq_self_eq_true a) _
    | _ => simp [ConRon.Arena.Modular.copyRecEq] at h
  | _ => simp [ConRon.Arena.Modular.copyRecEq] at h

/-! ## The ι reading rule reads its index only through `find?` -/

section Congr

variable {fe fe' : IFEnv} (hf : ∀ n, fe.find? n = fe'.find? n)
include hf

theorem annWitness_congr (D : EIdx) : ConRon.Arena.annWitness fe D = ConRon.Arena.annWitness fe' D := by
  simp only [ConRon.Arena.annWitness, hf]

theorem annIdentBody_congr (p p' : NIdx) (arity : Nat) (b : EIdx) :
    ConRon.Arena.annIdentBody fe p p' arity b = ConRon.Arena.annIdentBody fe' p p' arity b := by
  simp only [ConRon.Arena.annIdentBody, annWitness_congr hf]

theorem annIdentVal_congr (lps : List NIdx) (arity : Nat) (v : EIdx) :
    ConRon.Arena.annIdentVal fe lps arity v = ConRon.Arena.annIdentVal fe' lps arity v := by
  simp only [ConRon.Arena.annIdentVal, annIdentBody_congr hf]

theorem annIdent_congr (n : NIdx) (arity : Nat) : ConRon.Arena.annIdent fe n arity = ConRon.Arena.annIdent fe' n arity := by
  simp only [ConRon.Arena.annIdent, hf, annIdentVal_congr hf]

theorem annEq_congr : ∀ (fuel : Nat) (a b : EIdx), ConRon.Arena.annEq fe fuel a b = ConRon.Arena.annEq fe' fuel a b
  | 0, _, _ => rfl
  | fuel + 1, a, b => by
    simp only [ConRon.Arena.annEq, annIdent_congr hf, annEq_congr fuel]

theorem listAnnEq_congr : ∀ (as bs : List EIdx), ConRon.Arena.listAnnEq fe as bs = ConRon.Arena.listAnnEq fe' as bs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by simp only [ConRon.Arena.listAnnEq, annEq_congr hf, listAnnEq_congr as bs]

theorem paramsAnnEq_congr (cnP : Nat) (cv : IConstantVal) (pd : List EIdx) :
    ConRon.Arena.paramsAnnEq fe cnP cv pd = ConRon.Arena.paramsAnnEq fe' cnP cv pd := by
  simp only [ConRon.Arena.paramsAnnEq, listAnnEq_congr hf]

theorem iotaPartsRel_congr (cnP : Nat) (cv : IConstantVal) (rl : IRecRule) (p' p : IIotaParts)
    (pd : List EIdx) : ConRon.Arena.iotaPartsRel fe cnP cv rl p' p pd = ConRon.Arena.iotaPartsRel fe' cnP cv rl p' p pd := by
  simp only [ConRon.Arena.iotaPartsRel, paramsAnnEq_congr hf, listAnnEq_congr hf]

theorem ruleReads_congr (cv : IConstantVal) (rr : Option IotaRec) (mI rP i : Nat) (rl : IRecRule) :
    ConRon.Arena.ruleReads fe cv rr mI rP i rl = ConRon.Arena.ruleReads fe' cv rr mI rP i rl := by
  simp only [ConRon.Arena.ruleReads, hf, iotaPartsRel_congr hf]

theorem rulesRead_congr (cv : IConstantVal) (rr : Option IotaRec) (mI rP : Nat) :
    ∀ (rules : List IRecRule) (i : Nat),
      ConRon.Arena.rulesRead fe cv rr mI rP rules i = ConRon.Arena.rulesRead fe' cv rr mI rP rules i
  | [], _ => rfl
  | rl :: rest, i => by
    simp only [ConRon.Arena.rulesRead, ruleReads_congr hf, rulesRead_congr cv rr mI rP rest]

theorem recReads_congr (ci : IConstantInfo) : ConRon.Arena.recReads fe ci = ConRon.Arena.recReads fe' ci := by
  cases ci <;> simp only [ConRon.Arena.recReads, rulesRead_congr hf]

theorem recsRead_congr : ∀ (l : List IConstantInfo), ConRon.Arena.recsRead fe l = ConRon.Arena.recsRead fe' l
  | [] => rfl
  | ci :: rest => by simp only [ConRon.Arena.recsRead, recReads_congr hf, recsRead_congr rest]

end Congr

/-! ## The context's layer -/

/-- con-leche: ConLeche/Driver/Worker.lean:190-194 ctxConst — **a layer of constants pushed over
the empty base, read back**: its rows denote the environment `⟨Cs, []⟩`'s lookups, and every one
of those is a row. -/
structure LayerOK (st : EStore) (fe : IFEnv) (Cs : List ConstantInfo) : Prop where
  base : fe.base = {}
  tbls : fe.tbls = {}
  str : fe.strLit = false
  hit : ∀ n ci, fe.idx[n]? = some ci → ∃ nm c, denoteN st.ns n = some nm ∧
    Frontend.denoteCI st ci = some c ∧ (⟨Cs, []⟩ : Env).find? nm = some c
  cover : ∀ nm c, (⟨Cs, []⟩ : Env).find? nm = some c → ∃ n ci, denoteN st.ns n = some nm ∧
    fe.idx[n]? = some ci ∧ Frontend.denoteCI st ci = some c

theorem LayerOK.ext {st st' : EStore} {fe : IFEnv} {Cs : List ConstantInfo}
    (h : LayerOK st fe Cs) (hx : Ext st st') : LayerOK st' fe Cs :=
  ⟨h.base, h.tbls, h.str, fun n ci hn => by
      obtain ⟨nm, c, h1, h2, h3⟩ := h.hit n ci hn
      exact ⟨nm, c, denoteN_ext h1 hx, denoteCI_ext h2 hx, h3⟩,
    fun nm c he => by
      obtain ⟨n, ci, h1, h2, h3⟩ := h.cover nm c he
      exact ⟨n, ci, denoteN_ext h1 hx, h2, denoteCI_ext h3 hx⟩⟩

theorem LayerOK.empty (st : EStore) :
    LayerOK st ⟨⟨[], []⟩, {}, {}, {}, false, false⟩ [] :=
  ⟨rfl, rfl, rfl, fun n ci h => by simp at h, fun nm c h => by simp [Env.find?] at h⟩

theorem denoteCI_name {st : EStore} {ci : IConstantInfo} {c : ConstantInfo}
    (h : Frontend.denoteCI st ci = some c) : denoteN st.ns ci.name = some c.name := by
  have hc : ci.name = ci.toConstantVal.name := by cases ci <;> rfl
  rw [hc]
  exact denoteCV_name (denoteCI_toConstantVal h)

theorem LayerOK.push {st : EStore} (hw : NStoreWF st.ns) {fe : IFEnv} {Cs : List ConstantInfo}
    (h : LayerOK st fe Cs) {ci : IConstantInfo} {c : ConstantInfo}
    (hc : Frontend.denoteCI st ci = some c) : LayerOK st (fe.push ci) (c :: Cs) := by
  have hpush : fe.push ci = ⟨⟨ci :: fe.env.consts, fe.env.tables⟩, fe.idx.insert ci.name ci,
      fe.base, fe.tbls, fe.natLit, fe.strLit⟩ := by
    simp only [IFEnv.push, h.str, h.base, Bool.not_false, Bool.true_and]
    rw [ite_eq_right]
    unfold litNameAt
    simp
  have hn := denoteCI_name hc
  have hfind : ∀ nm, (⟨c :: Cs, []⟩ : Env).find? nm =
      if c.name == nm then some c else (⟨Cs, []⟩ : Env).find? nm := by
    intro nm
    simp only [Env.find?, List.find?_cons]
    split <;> simp_all [ConstantInfo.name]
  rw [hpush]
  refine ⟨h.base, h.tbls, h.str, fun n ci' hn' => ?_, fun nm c' he => ?_⟩
  · simp only [Std.HashMap.getElem?_insert] at hn'
    by_cases hb : ci.name = n
    · subst hb
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hn'
      subst hn'
      exact ⟨c.name, c, hn, hc, by simp [hfind]⟩
    · simp only [beq_iff_eq, hb, ↓reduceIte] at hn'
      obtain ⟨nm, c', h1, h2, h3⟩ := h.hit n ci' hn'
      refine ⟨nm, c', h1, h2, ?_⟩
      rw [hfind, ite_eq_right]
      · exact h3
      · intro he
        simp only [beq_iff_eq] at he
        exact hb (denoteN_inj hw hn (he ▸ h1))
  · rw [hfind] at he
    by_cases hb : c.name = nm
    · subst hb
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at he
      subst he
      exact ⟨ci.name, ci, hn, by simp, hc⟩
    · simp only [beq_iff_eq, hb, ↓reduceIte] at he
      obtain ⟨n, ci', h1, h2, h3⟩ := h.cover nm c' he
      refine ⟨n, ci', h1, ?_, h3⟩
      rw [Std.HashMap.getElem?_insert, ite_eq_right]
      · exact h2
      · intro he'
        simp only [beq_iff_eq] at he'
        subst he'
        exact hb (Option.some.inj (hn.symm.trans h1))

theorem LayerOK.pushAll {st : EStore} (hw : NStoreWF st.ns) :
    ∀ {L : List IConstantInfo} {cs : List ConstantInfo} {fe : IFEnv} {Cs : List ConstantInfo},
      Frontend.denoteCIList st L = some cs → LayerOK st fe Cs →
      LayerOK st (L.foldl IFEnv.push fe) (cs.reverse ++ Cs)
  | [], cs, fe, Cs, hL, h => by
    simp only [Frontend.denoteCIList, Option.some.injEq] at hL
    subst hL; simpa using h
  | ci :: L, cs, fe, Cs, hL, h => by
    simp only [Frontend.denoteCIList] at hL
    cases h1 : Frontend.denoteCI st ci with
    | none => rw [h1] at hL; simp at hL
    | some c =>
    cases h2 : Frontend.denoteCIList st L with
    | none => rw [h1, h2] at hL; simp at hL
    | some cs' =>
    rw [h1, h2] at hL
    obtain rfl := (Option.some.inj hL).symm
    have := LayerOK.pushAll hw h2 (h.push hw h1)
    simpa using this

theorem ctxLayerGo_run :
    ∀ (ds : List IDeclaration) (dsC : List Declaration) (fe : IFEnv) (Cs : List ConstantInfo)
      {s s' : AState} {r : IFEnv},
      DriverOK s →
      denoteDecls s.store ds = some dsC → LayerOK s.store fe Cs →
      ds.foldlM (m := AM) (fun fe d => do pure ((← declConstants d).foldl IFEnv.push fe)) fe s = .ok (r, s') →
      CStep s s' ∧ LayerOK s'.store r ((dsC.flatMap ConLeche.declConstants).reverse ++ Cs)
  | [], dsC, fe, Cs, s, s', r, hok, hd, hl, h => by
    simp only [denoteDecls, Option.some.injEq] at hd
    subst hd
    simp only [List.foldlM_nil] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨CStep.refl hok, by simpa using hl⟩
  | d :: ds, dsC, fe, Cs, s, s', r, hok, hd, hl, h => by
    simp only [denoteDecls] at hd
    cases h1 : Frontend.denoteDecl s.store d with
    | none => rw [h1] at hd; simp at hd
    | some x =>
    cases h2 : denoteDecls s.store ds with
    | none => rw [h1, h2] at hd; simp at hd
    | some xs =>
    rw [h1, h2] at hd
    obtain rfl := (Option.some.inj hd).symm
    simp only [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, k1, k2⟩ := AM.bind_ok h
    obtain ⟨L, s₂, k3, k4⟩ := AM.bind_ok k1
    obtain ⟨rfl, rfl⟩ := AM.pure_ok k4
    obtain ⟨c1, hL⟩ := constsD_run hok h1 k3
    have hl₁ := LayerOK.pushAll (nsWF_of_StateOK c1.ok.state) hL (hl.ext c1.ext)
    obtain ⟨c2, hl₂⟩ := ctxLayerGo_run ds xs _ _ c1.ok (denoteDecls_ext c1.ext _ _ h2) hl₁ k2
    refine ⟨c1.trans c2, ?_⟩
    simpa [List.flatMap_cons, List.reverse_append, List.append_assoc] using hl₂

/-- con-leche: ConLeche/Driver/Worker.lean:190-194 ctxConst — **the context's layer** answers
the environment of the context's constants. -/
theorem ctxLayer_run {s s' : AState} {ctx : Array IDeclaration} {ctxC : List Declaration}
    {fe : IFEnv} (hok : DriverOK s)
    (hd : denoteDecls s.store ctx.toList = some ctxC)
    (h : ConRon.Arena.Modular.ctxLayer ctx s = .ok (fe, s')) :
    CStep s s' ∧ LayerOK s'.store fe (ctxC.flatMap ConLeche.declConstants).reverse := by
  simp only [ConRon.Arena.Modular.ctxLayer, ← Array.foldlM_toList] at h
  have := ctxLayerGo_run ctx.toList ctxC _ [] hok hd (LayerOK.empty _) h
  simpa using this

/-- A layer, its base swapped for the driver's literal names: the same lookups. -/
@[expose] def layerFix (b : IFBase) (fe : IFEnv) : IFEnv := IFEnv.ofParts fe.env fe.idx b fe.tbls

theorem layer_find {fe : IFEnv} (hb : fe.base.idx = {}) (n : NIdx) : fe.find? n = fe.idx[n]? := by
  have hbase : fe.base.find? n = none := by simp [IFBase.find?, hb]
  simp only [IFEnv.find?, IFEnv.lookup, hbase]
  split
  · rename_i he
    have : n ∉ fe.idx := fun hm => by
      rw [Std.HashMap.isEmpty_iff_forall_not_mem] at he; exact he n hm
    simp [Std.HashMap.getElem?_eq_none this]
  · split <;> simp_all

/-- con-leche: none — **the fixed layer is an index of the context's environment**. -/
theorem layerFix_ok {s : AState} {fe : IFEnv} {Cs : List ConstantInfo}
    (hl : LayerOK s.store fe Cs) (hlits : LitsOK (driverFE s.pins).base s.store)
    (hb : (driverFE s.pins).base.idx = {}) (ht : (driverFE s.pins).base.tbls = {}) :
    IFEnvOK ⟨Cs, []⟩ (layerFix (driverFE s.pins).base fe) s := by
  have hf : ∀ n, (layerFix (driverFE s.pins).base fe).find? n = fe.idx[n]? :=
    layer_find (fe := layerFix (driverFE s.pins).base fe) hb
  refine ⟨fun n ci h => ?_, fun nm c h => ?_, fun n t h => ?_, fun nm pt h => ?_,
    FlagsOK.ofParts _ _ _ _, hlits⟩
  · rw [hf] at h; exact hl.hit n ci h
  · obtain ⟨n, ci, h1, h2, h3⟩ := hl.cover nm c h
    exact ⟨n, ci, h1, by rw [hf]; exact h2, h3⟩
  · simp only [IFEnv.findTable?, IFEnv.rawTable?, layerFix, IFEnv.ofParts, hl.tbls,
      IFBase.findTable?, ht] at h
    split at h <;> simp_all
  · simp [Env.findTable?] at h

theorem layerFix_find {s : AState} {fe : IFEnv} {Cs : List ConstantInfo}
    (hl : LayerOK s.store fe Cs) (hb : (driverFE s.pins).base.idx = {}) (n : NIdx) :
    fe.find? n = (layerFix (driverFE s.pins).base fe).find? n := by
  rw [layer_find (fe := layerFix (driverFE s.pins).base fe) hb n,
    layer_find (fe := fe) (by rw [hl.base]) n]
  rfl

/-! ## Upstream's context constant, one lookup -/

theorem find?_unique {n : ConLeche.Name} :
    ∀ {l : List ConstantInfo}, (l.map (·.name)).Nodup → ∀ {c : ConstantInfo}, c ∈ l →
      c.name = n → l.find? (·.name == n) = some c
  | [], _, c, hc, _ => by simp at hc
  | a :: l, hnd, c, hc, hn => by
    rw [List.find?_cons]
    rcases List.mem_cons.1 hc with rfl | hc
    · simp [hn]
    · rw [List.map_cons, List.nodup_cons] at hnd
      have ha : (a.name == n) = false := by
        simp only [beq_eq_false_iff_ne]
        intro he
        exact hnd.1 (by rw [he, ← hn]; exact List.mem_map_of_mem hc)
      rw [ha]
      exact find?_unique hnd.2 hc hn

theorem find?_none_of {n : ConLeche.Name} {l : List ConstantInfo} (h : ∀ c ∈ l, c.name ≠ n) :
    l.find? (·.name == n) = none := by
  rw [List.find?_eq_none]
  intro c hc
  simpa using h c hc

theorem foldl_insert_get (j : Nat) (n : ConLeche.Name) :
    ∀ (xs : List ConLeche.Name) (m : Std.HashMap ConLeche.Name Nat),
      (xs.foldl (fun m y => m.insert y j) m)[n]? = if n ∈ xs then some j else m[n]?
  | [], m => by simp
  | x :: xs, m => by
    rw [List.foldl_cons, foldl_insert_get j n xs, Std.HashMap.getElem?_insert]
    by_cases h1 : n ∈ xs
    · simp [h1]
    · by_cases h2 : x = n
      · subst h2; simp [h1]
      · have : n ≠ x := fun h => h2 h.symm
        simp [h1, h2, this]

theorem omGo_get (n : ConLeche.Name) :
    ∀ (l : List Declaration) (j : Nat) (m : Std.HashMap ConLeche.Name Nat) (k : Nat),
      (omGo l j m)[n]? = some k →
        (j ≤ k ∧ ∃ d, l[k - j]? = some d ∧ n ∈ ConLeche.Modular.declNames d) ∨ m[n]? = some k
  | [], j, m, k, h => .inr h
  | d :: l, j, m, k, h => by
    simp only [omGo] at h
    rcases omGo_get n l (j + 1) _ k h with ⟨hle, d', hd', hn⟩ | h'
    · refine .inl ⟨by omega, d', ?_, hn⟩
      have : k - j = (k - (j + 1)) + 1 := by omega
      rw [this, List.getElem?_cons_succ]
      exact hd'
    · rw [foldl_insert_get] at h'
      split at h'
      · rename_i hn
        obtain rfl := (Option.some.inj h').symm
        exact .inl ⟨Nat.le_refl _, d, by simp, hn⟩
      · exact .inr h'

theorem omGo_none (n : ConLeche.Name) :
    ∀ (l : List Declaration) (j : Nat) (m : Std.HashMap ConLeche.Name Nat),
      (omGo l j m)[n]? = none → ∀ d ∈ l, n ∉ ConLeche.Modular.declNames d
  | [], _, _, _, d, hd => by simp at hd
  | d :: l, j, m, h, d', hd' => by
    simp only [omGo] at h
    rcases List.mem_cons.1 hd' with rfl | hd'
    · intro hn
      have hk : ((ConLeche.Modular.declNames d').foldl (fun m y => m.insert y j) m)[n]? = some j := by
        rw [foldl_insert_get]; simp [hn]
      -- the later inserts keep `n` present
      have key : ∀ (l : List Declaration) (j' : Nat) (m' : Std.HashMap ConLeche.Name Nat),
          (m'[n]?).isSome = true → ((omGo l j' m')[n]?).isSome = true := by
        intro l
        induction l with
        | nil => intro _ _ h; exact h
        | cons e l ih =>
          intro j' m' h
          simp only [omGo]
          apply ih
          rw [foldl_insert_get]
          split <;> simp_all
      have := key l (j + 1) _ (by rw [hk]; rfl)
      rw [h] at this
      exact nomatch this
    · exact omGo_none n l (j + 1) _ h d' hd'

theorem declNames_eq (d : Declaration) :
    ConLeche.Modular.declNames d = (ConLeche.declConstants d).map (·.name) := rfl

/-- con-leche: ConLeche/Driver/Worker.lean:190-194 ctxConst — **at a context whose names are
distinct, the context constant of a name is the one constant of that name**. -/
theorem ctxConst_eq {rC : ConLeche.Driver.Reach}
    (hnd : (rC.ctx.toList.flatMap ConLeche.Modular.declNames).Nodup) (n : ConLeche.Name) :
    ConLeche.Driver.ctxConst (ConLeche.Driver.ownerMap rC.ctx) rC n =
      (rC.ctx.toList.flatMap ConLeche.declConstants).find? (·.name == n) := by
  have hnd' : ((rC.ctx.toList.flatMap ConLeche.declConstants).map (·.name)).Nodup := by
    rw [List.map_flatMap]; exact hnd
  simp only [ConLeche.Driver.ctxConst, ownerMap_eq]
  split
  · rename_i k hk
    rcases omGo_get n _ 0 {} k hk with ⟨-, d, hd, hn⟩ | h
    · simp only [Nat.sub_zero] at hd
      have hg : rC.ctx.getD k default = d := by
        simp [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hd]
      rw [hg]
      rw [declNames_eq, List.mem_map] at hn
      obtain ⟨c, hc, rfl⟩ := hn
      have hsome : ((ConLeche.declConstants d).find? (·.name == c.name)).isSome :=
        List.find?_isSome.2 ⟨c, hc, by simp⟩
      obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 hsome
      have hm' : c' ∈ rC.ctx.toList.flatMap ConLeche.declConstants :=
        List.mem_flatMap.2 ⟨d, List.mem_of_getElem? hd, List.mem_of_find?_eq_some hc'⟩
      have hn' := List.find?_some hc'
      simp only [beq_iff_eq] at hn'
      have key := find?_unique hnd' hm' hn'
      simp only [ConstantInfo.name] at hc' key ⊢
      rw [hc', key]
    · simp at h
  · rename_i hk
    have hn := omGo_none n _ 0 {} hk
    symm
    apply find?_none_of
    intro c hc he
    obtain ⟨d, hd, hc⟩ := List.mem_flatMap.1 hc
    exact hn d hd (by rw [declNames_eq]; exact List.mem_map.2 ⟨c, hc, he⟩)

theorem find?_reverse_nodup {l : List ConstantInfo} (hnd : (l.map (·.name)).Nodup)
    (n : ConLeche.Name) : l.reverse.find? (·.name == n) = l.find? (·.name == n) := by
  cases h : l.find? (·.name == n) with
  | none =>
    apply find?_none_of
    intro c hc he
    rw [List.find?_eq_none] at h
    exact (by simpa [he] using h c (List.mem_reverse.1 hc))
  | some c =>
    have hc := List.mem_of_find?_eq_some h
    have hn := List.find?_some h
    simp only [beq_iff_eq] at hn
    exact find?_unique (by rw [List.map_reverse]; exact (List.reverse_perm _).nodup_iff.2 hnd)
      (List.mem_reverse.2 hc) hn

/-! ## A copied block's recursors -/

/-- con-leche: ConLeche/Driver/Worker.lean:196-206 copyReadsB — **an accepting twin test is
upstream's**: the twin's recursors read against the context's layer (`recsRead_bridge` at the
layer with the driver's literal names, `layerFix_ok`), upstream's against `ctxConst`, the same
lookup at a context whose names are distinct (`ctxConst_eq`). -/
theorem copyReadsB_run {s s' : AState} {d : IDeclaration} {dC : Declaration} {b : Bool}
    {fe : IFEnv} {rC : ConLeche.Driver.Reach}
    (hok : DriverOK s)
    (hd : Frontend.denoteDecl s.store d = some dC)
    (hl : LayerOK s.store fe (rC.ctx.toList.flatMap ConLeche.declConstants).reverse)
    (hnd : (rC.ctx.toList.flatMap ConLeche.Modular.declNames).Nodup)
    (h : ConRon.Arena.Modular.copyReadsB fe d s = .ok (b, s')) :
    CStep s s' ∧ (b = true →
      ConLeche.Driver.copyReadsB (ConLeche.Driver.ownerMap rC.ctx) rC dC = true) := by
  cases d with
  | indDecl block nP =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨bC, hbC, rfl⟩ := hd
    simp only [ConRon.Arena.Modular.copyReadsB] at h
    obtain ⟨r, s₁, h1, h2⟩ := AM.bind_ok h
    obtain ⟨hp1, hsc1, hro⟩ := readBlock_installS hok hbC h1
    have c1 := CStep.of_pstep hok hp1 hsc1
    cases r with
    | error e =>
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      exact ⟨c1, fun h => nomatch h⟩
    | ok p =>
      obtain ⟨pC, hpC, hdp⟩ := hro
      have hrb : ConLeche.readBlock nP bC = .ok pC := by
        cases hr : ConLeche.readBlock nP bC with
        | error e => rw [hr] at hpC; simp [Except.toOption] at hpC
        | ok q => rw [hr] at hpC; simp only [Except.toOption, Option.some.injEq] at hpC; rw [hpC]
      simp only at h2
      obtain ⟨L, s₂, h3, h4⟩ := AM.bind_ok h2
      obtain ⟨hp2, hsc2, hL⟩ := blockRecs_run p.recs pC.recs c1.ok.state c1.ok.pins hdp
        (dShape_inv hdp).2.1 h3
      have c2 := CStep.of_pstep c1.ok hp2 hsc2
      have hl₂ := hl.ext (c1.ext.trans c2.ext)
      have hb0 : (driverFE s₂.pins).base.idx = {} := rfl
      have ht0 : (driverFE s₂.pins).base.tbls = {} := rfl
      rw [recsRead_congr (layerFix_find hl₂ hb0)] at h4
      have hE := layerFix_ok hl₂ (driverFE_lits c2.ok.pins) hb0 ht0
      have hsc3 := XFree.recsRead _ _ _ _ _ h4
      obtain ⟨c3o, c3x, c3p, hres⟩ := recsRead_bridge c2.ok hE hL h4
      have c3 : CStep s₂ s' := ⟨⟨DriverOK.of_check c3o c3p, c3x, c3p⟩, hsc3⟩
      refine ⟨c1.trans (c2.trans c3), fun hb => ?_⟩
      have key := hres hb
      have hf : ConLeche.Driver.ctxConst (ConLeche.Driver.ownerMap rC.ctx) rC =
          (⟨(rC.ctx.toList.flatMap ConLeche.declConstants).reverse, []⟩ : Env).find? := by
        funext n
        rw [ctxConst_eq hnd, Env.find?, find?_reverse_nodup (by rw [List.map_flatMap]; exact hnd)]
      simp only [ConLeche.Driver.copyReadsB, hrb, ConLeche.Cached.blockReadsOkC_eq, hf,
        ConLeche.blockReadsOk, key]
  | _ =>
    simp only [ConRon.Arena.Modular.copyReadsB] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    refine ⟨CStep.refl hok, fun _ => ?_⟩
    have hni := notInd_den hd (by intro b n h; cases h)
    cases dC <;> first | rfl | exact absurd rfl (hni _ _)

/-! ## The comparisons -/

/-- con-leche: ConLeche/Driver/Compare.lean:49-52 recKey — a record's key, denoted. -/
theorem recKey_den {st : EStore} {pk : ConRon.Arena.Frontend.Olean.OleanPins} (hnu : NullsRel st pk)
    {d : IDeclaration} {dC : Declaration} (hd : Frontend.denoteDecl st d = some dC) :
    denoteN st.ns ((ConRon.Arena.Frontend.recKey d).getD pk.anon) = some (ConLeche.Driver.recKey dC) := by
  cases d with
  | indDecl b n =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨bC, hb, rfl⟩ := hd
    cases b with
    | nil =>
      simp only [Frontend.denoteCIList, Option.some.injEq] at hb
      subst hb
      simpa [ConRon.Arena.Frontend.recKey, ConLeche.Driver.recKey] using hnu.anon
    | cons c cs =>
      simp only [Frontend.denoteCIList] at hb
      split at hb <;> try simp at hb
      rename_i x xs hx _
      obtain rfl := hb.symm
      simpa [ConRon.Arena.Frontend.recKey, ConLeche.Driver.recKey] using denoteCI_name hx
  | axiomDecl v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hcv, rfl⟩ := hd
    exact (denoteCV_inv hcv).1
  | quotDecl k v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hcv, rfl⟩ := hd
    exact (denoteCV_inv hcv).1
  | defnDecl v e hh =>
    simp only [Frontend.denoteDecl] at hd
    split at hd <;> try simp at hd
    rename_i cv x hcv _
    obtain rfl := hd.symm
    exact (denoteCV_inv hcv).1
  | thmDecl v e =>
    simp only [Frontend.denoteDecl] at hd
    split at hd <;> try simp at hd
    rename_i cv x hcv _
    obtain rfl := hd.symm
    exact (denoteCV_inv hcv).1
  | opaqueDecl v e =>
    simp only [Frontend.denoteDecl] at hd
    split at hd <;> try simp at hd
    rename_i cv x hcv _
    obtain rfl := hd.symm
    exact (denoteCV_inv hcv).1

/-- `cs.find? (·.name == n)`, read back. -/
theorem findNamed_den {st : EStore} (hw : NStoreWF st.ns) {n : NIdx} {nC : ConLeche.Name}
    (hn : denoteN st.ns n = some nC) :
    ∀ {L : List IConstantInfo} {cs : List ConstantInfo}, Frontend.denoteCIList st L = some cs →
      Option.Rel (fun ci c => Frontend.denoteCI st ci = some c)
        (ConRon.Arena.Modular.findNamed L n) (cs.find? (·.toConstantVal.name == nC))
  | [], cs, h => by
    simp only [Frontend.denoteCIList, Option.some.injEq] at h
    subst h; exact .none
  | ci :: L, cs, h => by
    simp only [Frontend.denoteCIList] at h
    cases h1 : Frontend.denoteCI st ci with
    | none => rw [h1] at h; simp at h
    | some c =>
    cases h2 : Frontend.denoteCIList st L with
    | none => rw [h1, h2] at h; simp at h
    | some cs' =>
    rw [h1, h2] at h
    obtain rfl := (Option.some.inj h).symm
    have hcn := denoteCI_name h1
    have hb : (ci.name == n) = (c.toConstantVal.name == nC) := by
      have := beq_of_denote_inj (d := denoteN st.ns) (fun hi hj => denoteN_inj hw hi hj) hcn hn
      simpa [ConstantInfo.name] using this
    simp only [ConRon.Arena.Modular.findNamed, List.find?_cons] at ⊢
    have ih := findNamed_den hw hn h2
    simp only [ConRon.Arena.Modular.findNamed] at ih
    rw [hb]
    split
    · exact .some h1
    · exact ih

/-- con-leche: ConLeche/Driver/Worker.lean:208-240 copyCheck — the context record's constant of
a name, read back. -/
theorem findConstant_run {s s' : AState} {e : IDeclaration} {eC : Declaration} {n : NIdx}
    {nC : ConLeche.Name} {o : Option IConstantInfo}
    (hok : DriverOK s) (he : Frontend.denoteDecl s.store e = some eC)
    (hn : denoteN s.store.ns n = some nC)
    (h : ConRon.Arena.Modular.findConstant e n s = .ok (o, s')) :
    CStep s s' ∧ Option.Rel (fun ci c => Frontend.denoteCI s'.store ci = some c) o
      ((ConLeche.declConstants eC).find? (·.toConstantVal.name == nC)) := by
  simp only [ConRon.Arena.Modular.findConstant] at h
  obtain ⟨L, s₁, h1, h2⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
  obtain ⟨c1, hL⟩ := constsD_run hok he h1
  exact ⟨c1, findNamed_den (nsWF_of_StateOK c1.ok.state) (denoteN_ext hn c1.ext) hL⟩

/-- con-leche: ConLeche/Driver/Worker.lean:155-162 copyStmt? — **the statement a copy may be read
by, read back**. -/
theorem copyStmt_run {s s' : AState} {d : IDeclaration} {dC : Declaration}
    {o : Option IConstantVal} (hok : DriverOK s) (hd : Frontend.denoteDecl s.store d = some dC)
    (h : ConRon.Arena.Modular.copyStmt d s = .ok (o, s')) :
    CStep s s' ∧ Option.Rel (fun cv c => Frontend.denoteCV s'.store cv = some c) o
      (ConLeche.Driver.copyStmt? dC) := by
  cases d with
  | axiomDecl v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hcv, rfl⟩ := hd
    simp only [ConRon.Arena.Modular.copyStmt] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨CStep.refl hok, .some hcv⟩
  | thmDecl v e =>
    simp only [Frontend.denoteDecl] at hd
    split at hd <;> try simp at hd
    rename_i cv x hcv _
    obtain rfl := hd.symm
    simp only [ConRon.Arena.Modular.copyStmt] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨CStep.refl hok, .some hcv⟩
  | opaqueDecl v e =>
    simp only [Frontend.denoteDecl] at hd
    split at hd <;> try simp at hd
    rename_i cv x hcv _
    obtain rfl := hd.symm
    simp only [ConRon.Arena.Modular.copyStmt] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨CStep.refl hok, .some hcv⟩
  | defnDecl v e hint =>
    simp only [Frontend.denoteDecl] at hd
    split at hd <;> try simp at hd
    rename_i cv x hcv hx
    obtain rfl := hd.symm
    simp only [ConRon.Arena.Modular.copyStmt, ConRon.Arena.Modular.usesSorry] at h
    obtain ⟨b, s₁, h1, h2⟩ := AM.bind_ok h
    obtain ⟨sa, s₀, g0, g1⟩ := AM.bind_ok h1
    obtain ⟨rfl, hsa⟩ := pinAt_run (x := ConLeche.sorryAxName) hok.pins rfl g0
    obtain ⟨hp1, hr1⟩ := mentionsAnyConst_spec [sa] [ConLeche.sorryAxName] e x _ s₁ b hok.state
      ⟨by simp [Frontend.denoteNList, hsa], hx⟩ g1
    simp only [RV] at hr1
    subst hr1
    have hsf : s₁ = s₀ := by
      simp only [ConRon.Arena.mentionsAnyConst] at g1
      exact SFree.bind (mentionsAnyGo_sfree _ _ _ _) (fun _ => SFree.pure _) _ _ _ g1
    subst hsf
    have c1 := CStep.refl hok
    have hm : Expr.mentionsAnyConstC [ConLeche.sorryAxName] x =
        x.mentionsAnyConst [ConLeche.sorryAxName] := Expr.mentionsAnyConstC_spec
    split at h2
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      rename_i hb
      refine ⟨c1, ?_⟩
      simp only [ConLeche.Driver.copyStmt?, hm, hb, ↓reduceIte]
      exact .some (denoteCV_ext hcv c1.ext)
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      rename_i hb
      refine ⟨c1, ?_⟩
      simp only [ConLeche.Driver.copyStmt?, hm, hb, Bool.false_eq_true, ↓reduceIte]
      exact .none
  | quotDecl k v =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨cv, hcv, rfl⟩ := hd
    simp only [ConRon.Arena.Modular.copyStmt] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨CStep.refl hok, .none⟩
  | indDecl b n =>
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨bC, hb, rfl⟩ := hd
    simp only [ConRon.Arena.Modular.copyStmt] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨CStep.refl hok, .none⟩

/-- con-leche: ConLeche/Driver/Worker.lean:164-169 sameDefUpToLevels — **the definition test is
upstream's** (as `copyB_run`). -/
theorem sameDefUpToLevels_run {ci ci' : IConstantInfo} {c c' : ConstantInfo} {r : Bool}
    {s s' : AState} (hok : StateOK s) (hr : ReadOK s)
    (hc : Frontend.denoteCI s.store ci = some c) (hc' : Frontend.denoteCI s.store ci' = some c')
    (hrun : ConRon.Arena.Modular.sameDefUpToLevels ci ci' s = .ok (r, s')) :
    RStep s s' ∧ r = ConLeche.Driver.sameDefUpToLevels c c' := by
  have hv := denoteCV_inv (denoteCI_toConstantVal hc)
  have hv' := denoteCV_inv (denoteCI_toConstantVal hc')
  have hlb := denoteNList_beq hok.wf hv.2.1 hv'.2.1
  simp only [ConRon.Arena.Modular.sameDefUpToLevels] at hrun
  simp only [ConLeche.Driver.sameDefUpToLevels]
  rcases AM.ite_ok hrun with ⟨hy, k⟩ | ⟨hn, k⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
    have hy' : (c.toConstantVal.levelParams == c'.toConstantVal.levelParams) = true := by
      rw [← hlb]; simpa using hy
    simp only [hy', ↓reduceIte, ConstantInfo.beqP_eq]
    exact ⟨RStep.refl hok hr, beq_of_denote_inj (denoteCI_inj hok.wf) hc hc'⟩
  · have hn' : (c.toConstantVal.levelParams == c'.toConstantVal.levelParams) = false := by
      rw [← hlb]; simpa using hn
    simp only [hn', Bool.false_eq_true, ↓reduceIte]
    rw [← levelsRenaming_eq hok.wf hv.2.1 hv'.2.1]
    rcases AM.ite_ok k with ⟨hy2, k⟩ | ⟨hn2, k⟩
    · obtain ⟨x, s₁, h1, h2⟩ := AM.bind_ok k
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
      obtain ⟨hs1, hx⟩ := IConstantInfo.atLps_run hok hr hc' hv.2.1 h1
      refine ⟨hs1, ?_⟩
      rw [hy2, Bool.true_and, ← ConLeche.Cached.ConstantInfo.atLps_eq_atLpsC,
        ConstantInfo.beqP_eq]
      exact beq_of_denote_inj (denoteCI_inj hs1.ok.wf) hx (denoteCI_ext hc hs1.ext)
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
      simp only [Bool.not_eq_true] at hn2
      exact ⟨RStep.refl hok hr, by rw [hn2, Bool.false_and]⟩

/-- con-leche: ConLeche/Driver/Worker.lean:208-240 copyCheck — **a copied block's three tests**,
upstream's. -/
theorem copyIndOk_run {s s' : AState} {d e : IDeclaration} {dC eC : Declaration} {b : Bool}
    {fe : IFEnv} {rC : ConLeche.Driver.Reach}
    (hok : DriverOK s) (hd : Frontend.denoteDecl s.store d = some dC)
    (he : Frontend.denoteDecl s.store e = some eC)
    (hl : LayerOK s.store fe (rC.ctx.toList.flatMap ConLeche.declConstants).reverse)
    (hnd : (rC.ctx.toList.flatMap ConLeche.Modular.declNames).Nodup)
    (h : ConRon.Arena.Modular.copyIndOk fe d e s = .ok (b, s')) :
    CStep s s' ∧ (b = true → (ConLeche.Driver.copyRecEq dC eC && ConLeche.Driver.blockReadB dC &&
      ConLeche.Driver.copyReadsB (ConLeche.Driver.ownerMap rC.ctx) rC dC) = true) := by
  simp only [ConRon.Arena.Modular.copyIndOk] at h
  by_cases h1 : ConRon.Arena.Modular.copyRecEq d e = true
  · have hq := copyRecEq_run hd he h1
    simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    peel_pure h
    obtain ⟨b1, s₁, k1, k2⟩ := AM.bind_ok h
    obtain ⟨c1, hb1⟩ := blockReadB_run hok hd k1
    split at k2
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok k2
      exact ⟨c1, fun h => nomatch h⟩
    · rename_i hb
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hb
      peel_pure k2
      obtain ⟨c2, hb2⟩ := copyReadsB_run c1.ok (denoteDecl_ext c1.ext hd) (hl.ext c1.ext) hnd k2
      exact ⟨c1.trans c2, fun hb' => by simp [hq, hb1 hb, hb2 hb']⟩
  · simp only [Bool.not_eq_true] at h1
    simp only [h1, Bool.not_false, ↓reduceIte] at h
    obtain ⟨rfl, rfl⟩ := AM.pure_ok h
    exact ⟨CStep.refl hok, fun h => nomatch h⟩

/-! ## One copy -/

theorem denoteDecls_get {st : EStore} :
    ∀ {L : List IDeclaration} {LC : List Declaration}, denoteDecls st L = some LC →
      ∀ {k : Nat} {e : IDeclaration}, L[k]? = some e →
        ∃ eC, LC[k]? = some eC ∧ Frontend.denoteDecl st e = some eC
  | [], LC, _, k, e, hk => by simp at hk
  | d :: L, LC, h, k, e, hk => by
    simp only [denoteDecls] at h
    cases h1 : Frontend.denoteDecl st d with
    | none => rw [h1] at h; simp at h
    | some x =>
    cases h2 : denoteDecls st L with
    | none => rw [h1, h2] at h; simp at h
    | some xs =>
    rw [h1, h2] at h
    obtain rfl := (Option.some.inj h).symm
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      exact ⟨x, rfl, h1⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk ⊢
      exact denoteDecls_get h2 hk

/-- con-leche: ConLeche/Driver/Worker.lean:208-240 copyCheck — **an accepting twin check of one
copy is upstream's accept**; the scratch flag is unmoved but at a copied block (whose recursors'
reading `recsRead_bridge` states no scratch frame for). -/
theorem copyCheck_run {s s' : AState} {pk : ConRon.Arena.Frontend.Olean.OleanPins}
    {m : NIdx} {mC : ConLeche.Name}
    {ld : ConRon.Arena.Frontend.Olean.HeaderLoads} {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    {ix : ConRon.Arena.Frontend.Olean.NameIndex} {ixC : ConLeche.Frontend.Olean.NameIndex}
    {r : ConRon.Arena.Modular.Reach} {rC : ConLeche.Driver.Reach}
    {owner : Std.HashMap NIdx Nat} {fe : IFEnv} {d : IDeclaration} {dC : Declaration}
    (hok : DriverOK s) (hnu : NullsRel s.store pk)
    (hd : Frontend.denoteDecl s.store d = some dC) (hr : ReachRel s.store r rC)
    (how : HMRel (· = ·) s.store owner (ConLeche.Driver.ownerMap rC.ctx))
    (hl : ¬ NotInd dC → LayerOK s.store fe (rC.ctx.toList.flatMap ConLeche.declConstants).reverse)
    (hnd : (rC.ctx.toList.flatMap ConLeche.Modular.declNames).Nodup)
    (h : ConRon.Arena.Modular.copyCheck pk m ld ix r owner fe d s = .ok ((), s')) :
    CStep s s' ∧
      ConLeche.Driver.copyCheck mC ldC ixC rC (ConLeche.Driver.ownerMap rC.ctx) dC = .ok () := by
  have hw := nsWF_of_StateOK hok.state
  have hn := recKey_den hnu hd
  simp only [ConRon.Arena.Modular.copyCheck] at h
  have hb := AM.bind_ok h; clear h; obtain ⟨qs, s₁, g1, h⟩ := hb
  obtain ⟨rfl, dq⟩ := pinAt_run (x := ConLeche.quotSoundName) hok.pins rfl g1
  have hb := AM.bind_ok h; clear h; obtain ⟨sa, s₂, g2, h⟩ := hb
  obtain ⟨rfl, ds⟩ := pinAt_run (i := PIN_SORRY_AX) (x := ConLeche.sorryAxName) hok.pins rfl g2
  have hq := beq_handle_iff hok.state.wf hn dq
  have hs := beq_handle_iff hok.state.wf hn ds
  have hi := AM.ite_ok h; clear h
  rcases hi with ⟨hy, k⟩ | ⟨hno, h⟩
  · no_accept k
  peel_pure h
  have hnq : ConLeche.Driver.recKey dC ≠ ConLeche.quotSoundName := fun he => hno (by simp [hq.2 he])
  have hns : ConLeche.Driver.recKey dC ≠ ConLeche.sorryAxName := fun he => hno (by simp [hs.2 he])
  have hb := AM.bind_ok h; clear h; obtain ⟨bb, s₄, g4, h⟩ := hb
  obtain ⟨hr4, hbb⟩ := basisNamesOk_run hok.state hok.readOK hok.pins hd g4
  have c4 := CStep.of_rstep hok hr4
  have hi := AM.ite_ok h; clear h
  rcases hi with ⟨hy, k⟩ | ⟨hno', h⟩
  · no_accept k
  peel_pure h
  have hbasis : ConLeche.basisNamesOk dC = true := by
    subst hbb; simpa using hno'
  have hn4 := denoteN_ext hn c4.ext
  have howner : owner[(ConRon.Arena.Frontend.recKey d).getD pk.anon]? =
      (ConLeche.Driver.ownerMap rC.ctx)[ConLeche.Driver.recKey dC]? :=
    (how.ext c4.ext (fun _ _ h => h)).get_eq (nsWF_of_StateOK c4.ok.state) hn4
  have hq' : (ConLeche.Driver.recKey dC == ConLeche.quotSoundName) = false := by
    simpa using hnq
  have hs' : (ConLeche.Driver.recKey dC == ConLeche.sorryAxName) = false := by
    simpa using hns
  simp only [ConLeche.Driver.copyCheck, hq', hs', Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    hbasis, Bool.not_true]
  cases hk : owner[(ConRon.Arena.Frontend.recKey d).getD pk.anon]? with
  | none => rw [hk] at h; simp only at h; no_accept h
  | some k =>
  rw [hk] at h
  simp only at h
  rw [howner] at hk
  simp only [hk]
  cases he : r.ctx[k]? with
  | none => rw [he] at h; simp only at h; no_accept h
  | some e =>
  rw [he] at h
  simp only at h
  obtain ⟨eC, heC, hde⟩ := denoteDecls_get (denoteDecls_ext c4.ext _ _ hr.ctx)
    (by rw [Array.getElem?_toList]; exact he)
  have hge : rC.ctx.getD k default = eC := by
    simp [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, heC]
  rw [hge]
  -- the comparison
  simp only [ConRon.Arena.Modular.copyAgainst] at h
  have hb := AM.bind_ok h; clear h; obtain ⟨ci, s₆, g6, h⟩ := hb
  obtain ⟨c6, hci⟩ := findConstant_run c4.ok hde hn4 g6
  have hb := AM.bind_ok h; clear h; obtain ⟨cs, s₇, g7, h⟩ := hb
  obtain ⟨c7, hcs⟩ := copyStmt_run c6.ok (denoteDecl_ext (c4.ext.trans c6.ext) hd) g7
  have c47 := c4.trans (c6.trans c7)
  have hd7 := denoteDecl_ext c47.ext hd
  have hw7 := nsWF_of_StateOK c47.ok.state
  rcases optRel_cases hci with ⟨hci1, hci2⟩ | ⟨ci', ciC, hci1, hci2, hci3⟩ <;>
    rcases optRel_cases hcs with ⟨hcs1, hcs2⟩ | ⟨cv, cvC, hcs1, hcs2, hcs3⟩
  · -- no statement, no constant
    subst hci1 hcs1
    rw [hci2, hcs2]
    cases d with
    | indDecl b nP =>
      simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
      obtain ⟨bC, hbC, rfl⟩ := hd
      simp only at h
      have hb := AM.bind_ok h; clear h; obtain ⟨bi, s₈, g8, h⟩ := hb
      have hlay := hl (fun hn => hn bC nP rfl)
      obtain ⟨c8, hb8⟩ := copyIndOk_run c47.ok hd7 (denoteDecl_ext (c6.ext.trans c7.ext) hde)
        (hlay.ext c47.ext) hnd g8
      split at h
      · obtain ⟨-, rfl⟩ := AM.pure_ok h
        rename_i hbi
        refine ⟨c47.trans c8, ?_⟩
        simp only [hb8 hbi, ↓reduceIte]
      no_accept h
    | _ =>
      try simp only at h
      no_accept h
  · -- a statement, no constant
    subst hci1 hcs1
    try simp only at h
    no_accept h
  · -- no statement, a constant
    subst hci1 hcs1
    rw [hci2, hcs2]
    cases d with
    | defnDecl v x hint =>
      simp only [Frontend.denoteDecl] at hd
      split at hd <;> try simp at hd
      rename_i cvC xC hcv hx
      obtain rfl := hd.symm
      simp only at h
      have hb := AM.bind_ok h; clear h; obtain ⟨bi, s₈, g8, h⟩ := hb
      have hdi : Frontend.denoteCI s₇.store (.defnInfo v x hint) = some (.defnInfo cvC xC hint) := by
        simp [Frontend.denoteCI, denoteCV_ext hcv c47.ext, denote_ext hx c47.ext]
      obtain ⟨hr8, hb8⟩ := sameDefUpToLevels_run c47.ok.state c47.ok.readOK hdi (denoteCI_ext hci3 c7.ext) g8
      split at h
      · obtain ⟨-, rfl⟩ := AM.pure_ok h
        rename_i hbi
        refine ⟨c47.trans (CStep.of_rstep c47.ok hr8), ?_⟩
        simp only [← hb8, hbi, ↓reduceIte]
      no_accept h
    | indDecl b nP =>
      simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
      obtain ⟨bC, hbC, rfl⟩ := hd
      simp only at h
      have hb := AM.bind_ok h; clear h; obtain ⟨bi, s₈, g8, h⟩ := hb
      have hlay := hl (fun hn => hn bC nP rfl)
      obtain ⟨c8, hb8⟩ := copyIndOk_run c47.ok hd7 (denoteDecl_ext (c6.ext.trans c7.ext) hde)
        (hlay.ext c47.ext) hnd g8
      split at h
      · obtain ⟨-, rfl⟩ := AM.pure_ok h
        rename_i hbi
        refine ⟨c47.trans c8, ?_⟩
        simp only [hb8 hbi, ↓reduceIte]
      no_accept h
    | _ =>
      try simp only at h
      no_accept h
  · -- a statement and a constant
    subst hci1 hcs1
    rw [hci2, hcs2]
    simp only at h
    have hb := AM.bind_ok h; clear h; obtain ⟨bi, s₈, g8, h⟩ := hb
    obtain ⟨hr8, hb8⟩ := sameCvUpToLevels_run c47.ok.state c47.ok.readOK hcs3
      (denoteCI_toConstantVal (denoteCI_ext hci3 c7.ext)) g8
    split at h
    · obtain ⟨-, rfl⟩ := AM.pure_ok h
      rename_i hbi
      refine ⟨c47.trans (CStep.of_rstep c47.ok hr8), ?_⟩
      simp only [← hb8, hbi, ↓reduceIte]
    no_accept h

/-! ## Every copy -/

theorem copyChecks_run {pk : ConRon.Arena.Frontend.Olean.OleanPins} {m : NIdx} {mC : ConLeche.Name}
    {ld : ConRon.Arena.Frontend.Olean.HeaderLoads} {ldC : ConLeche.Frontend.Olean.HeaderLoads}
    {ix : ConRon.Arena.Frontend.Olean.NameIndex} {ixC : ConLeche.Frontend.Olean.NameIndex}
    {r : ConRon.Arena.Modular.Reach} {rC : ConLeche.Driver.Reach}
    {owner : Std.HashMap NIdx Nat} {fe : IFEnv}
    (hnd : (rC.ctx.toList.flatMap ConLeche.Modular.declNames).Nodup) :
    ∀ (L : List IDeclaration) (LC : List Declaration) {s s' : AState},
      DriverOK s → NullsRel s.store pk → denoteDecls s.store L = some LC →
      ReachRel s.store r rC → HMRel (· = ·) s.store owner (ConLeche.Driver.ownerMap rC.ctx) →
      (∀ d ∈ L, (∀ b n, d ≠ .indDecl b n) ∨
        LayerOK s.store fe (rC.ctx.toList.flatMap ConLeche.declConstants).reverse) →
      L.forM (ConRon.Arena.Modular.copyCheck pk m ld ix r owner fe) s = .ok ((), s') →
      CStep s s' ∧
        LC.forM (ConLeche.Driver.copyCheck mC ldC ixC rC (ConLeche.Driver.ownerMap rC.ctx)) = .ok ()
  | [], LC, s, s', hok, _, hd, _, _, _, h => by
    simp only [denoteDecls, Option.some.injEq] at hd
    subst hd
    unfold List.forM at h
    obtain ⟨-, rfl⟩ := AM.pure_ok h
    exact ⟨CStep.refl hok, rfl⟩
  | d :: L, LC, s, s', hok, hnu, hd, hr, how, hl, h => by
    simp only [denoteDecls] at hd
    cases h1 : Frontend.denoteDecl s.store d with
    | none => rw [h1] at hd; simp at hd
    | some x =>
    cases h2 : denoteDecls s.store L with
    | none => rw [h1, h2] at hd; simp at hd
    | some xs =>
    rw [h1, h2] at hd
    obtain rfl := (Option.some.inj hd).symm
    unfold List.forM at h
    obtain ⟨u, s₁, k1, k2⟩ := AM.bind_ok h
    have hl1 : ¬ NotInd x → LayerOK s.store fe (rC.ctx.toList.flatMap ConLeche.declConstants).reverse := by
      intro hn
      rcases hl d (List.mem_cons_self ..) with hni | hlay
      · exact absurd (notInd_den h1 hni) hn
      · exact hlay
    obtain ⟨c1, hx1⟩ := copyCheck_run (mC := mC) (ldC := ldC) (ixC := ixC) hok hnu h1 hr how
      hl1 hnd k1
    have hl' : ∀ d ∈ L, (∀ b n, d ≠ .indDecl b n) ∨
        LayerOK s₁.store fe (rC.ctx.toList.flatMap ConLeche.declConstants).reverse := by
      intro d' hd'
      rcases hl d' (List.mem_cons_of_mem _ hd') with h' | h'
      · exact .inl h'
      · exact .inr (h'.ext c1.ext)
    obtain ⟨c2, hx2⟩ := copyChecks_run hnd L xs c1.ok (hnu.ext c1.ext)
      (denoteDecls_ext c1.ext _ _ h2) (hr.ext c1.ext) (how.ext c1.ext (fun _ _ h => h)) hl' k2
    refine ⟨c1.trans c2, ?_⟩
    unfold List.forM
    rw [hx1]
    exact hx2

/-- con-leche: ConLeche/Driver/Worker.lean:259-263 copiesOk — **an accepting twin `copiesOk` is
upstream's accept**, at the reads, the reach and the emitted records read back, the context's
names distinct (upstream's `WorkerFacts.nodup`); the driver's invariant kept, the store extended,
the pins and the scratch flag unmoved (a copied block's recursors' reading too: `XFree.recsRead`). -/
theorem copiesOk_run {s s' : AState} {pk : ConRon.Arena.Frontend.Olean.OleanPins}
    {m : NIdx} {mC : ConLeche.Name}
    {x : Array (ConLeche.Frontend.Olean.ImportF NIdx)} {xC : Array ConLeche.Frontend.Olean.ImportRec}
    {wr : ConRon.Arena.Frontend.Olean.WorkerReads} {wrC : ConLeche.Frontend.Olean.WorkerReads}
    {r : ConRon.Arena.Modular.Reach} {rC : ConLeche.Driver.Reach}
    {ds : Array IDeclaration} {dsC : Array Declaration}
    (hok : DriverOK s) (hnu : NullsRel s.store pk) (hx : ImpsD s.store x xC)
    (hwr : WorkerReadsRel s.store wr wrC) (hr : ReachRel s.store r rC)
    (hds : denoteDeclArray s.store ds = some dsC)
    (hnd : (rC.ctx.toList.flatMap ConLeche.Modular.declNames).Nodup)
    (h : ConRon.Arena.Modular.copiesOk pk m x wr r ds s = .ok ((), s')) :
    CStep s s' ∧ ConLeche.Driver.copiesOk mC xC wrC rC dsC = .ok () := by
  simp only [ConRon.Arena.Modular.copiesOk] at h
  have hb := AM.bind_ok h; clear h; obtain ⟨owner, s₁, g1, h⟩ := hb
  obtain ⟨c1, how⟩ := ownerMap_run hok hr.ctx g1
  have hb := AM.bind_ok h; clear h; obtain ⟨cs, s₂, g2, h⟩ := hb
  obtain ⟨c2, hcs⟩ := copyRecs_run c1.ok (hx.ext c1.ext) (denoteDeclArray_ext c1.ext hds)
    (hwr.index.first.ext c1.ext (fun _ _ h => h)) g2
  have hr2 : ReachRel s₂.store r rC := hr.ext (c1.ext.trans c2.ext)
  have hcsL : denoteDecls s₂.store cs.toList =
      some (ConLeche.Driver.copyRecs xC wrC.index dsC).toList := by
    simp only [denoteDeclArray, Option.map_eq_some_iff] at hcs
    obtain ⟨l, hl, he⟩ := hcs
    rw [hl, ← he]
  have hup : ConLeche.Driver.copiesOk mC xC wrC rC dsC =
      (ConLeche.Driver.copyRecs xC wrC.index dsC).toList.forM
        (ConLeche.Driver.copyCheck mC wrC.loads wrC.index rC (ConLeche.Driver.ownerMap rC.ctx)) := by
    simp only [ConLeche.Driver.copiesOk]
  rw [hup]
  rcases AM.ite_ok h with ⟨hany, h⟩ | ⟨hany, h⟩
  · have hb := AM.bind_ok h; clear h; obtain ⟨fe, s₃, g3, h⟩ := hb
    obtain ⟨c3, hl3⟩ := ctxLayer_run c2.ok hr2.ctx g3
    obtain ⟨c4, hx4⟩ := copyChecks_run (mC := mC) (ldC := wrC.loads) (ixC := wrC.index) hnd
      cs.toList _ c3.ok (hnu.ext (c1.ext.trans (c2.ext.trans c3.ext)))
      (denoteDecls_ext c3.ext _ _ hcsL) (hr2.ext c3.ext)
      (how.ext (c2.ext.trans c3.ext) (fun _ _ h => h)) (fun _ _ => .inr hl3) h
    exact ⟨c1.trans (c2.trans (c3.trans c4)), hx4⟩
  · have hb := AM.bind_ok h; clear h; obtain ⟨fe, s₃, g3, h⟩ := hb
    obtain ⟨hfe, hs3⟩ := AM.pure_ok g3
    subst hfe
    rw [hs3] at h
    have hni : ∀ d ∈ cs.toList, ∀ b n, d ≠ .indDecl b n := by
      intro d hd b n he
      subst he
      apply hany
      rw [ConRon.Arena.Modular.anyInd, ← Array.any_toList, List.any_eq_true]
      exact ⟨_, hd, rfl⟩
    obtain ⟨c4, hx4⟩ := copyChecks_run (mC := mC) (ldC := wrC.loads) (ixC := wrC.index) hnd
      cs.toList _ c2.ok (hnu.ext (c1.ext.trans c2.ext)) hcsL hr2
      (how.ext c2.ext (fun _ _ h => h)) (fun d hd => .inl (hni d hd)) h
    exact ⟨c1.trans (c2.trans c4), hx4⟩

end ConRon.Bridge.Modular

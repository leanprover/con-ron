/-
# `ConRon.Bridge.Compare.Cone` — the twin's justification is con-leche's

`Arena/Justify.lean`'s `justifyWhy` accepting a statement against the solution gives con-leche's
`justifyWhy` accepting its denotation.  The twin's cone walk (`coneGo`, con-leche's work list with its
fuel and `seen`) is not compared with con-leche's walk step by step: its
accept leaves a `seen` whose names form a **shared cone** (`ConeClosed`, every name the same
constant in both indices, closed under what each reads, `coneGo_run`), and a shared cone covering
what the type reads is con-leche's accept (`Compare/Model.lean`'s `justifyWhy_of_cone`).  So the
two walks' fuels need not agree.

The solution is read through its frozen index's view at its length (`SolView`, every counter
visible: `ISolution.find?`, `ISolution.findTable?`), which denotes the solution stream's
environment by `view_ok`.
-/
module

public import ConRon.Bridge.Compare.Justify
public import ConRon.Bridge.Compare.Needs
public import ConRon.Bridge.Compare.Model
public import ConRon.Bridge.Checker.StreamIndex
import ConRon.Bridge.Specs
import ConLeche.Verify.EnvBound

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The solution's view -/

/-- con-leche: ConLeche/Cached/Justify.lean:144-146 solutionOf — **the solution's index, every
counter visible**: its frozen index's view past its last record. -/
@[expose] def SolView (J : ISolution) : IFEnv := J.idx.view J.idx.firsts.size

/-- con-leche: ConLeche/Kernel/FEnv.lean:278-283 FEnv.find? — the solution's lookup is its view's. -/
theorem ISolution.find?_view (J : ISolution) (n : NIdx) : J.find? n = (SolView J).find? n := by
  rw [SolView, IStreamIndex.view_find?]
  simp only [ISolution.find?, Array.getD, Nat.lt_irrefl, dite_false]
  cases J.idx.base.idx[n]? with
  | none => rfl
  | some p => obtain ⟨c, ci⟩ := p; rfl

/-- con-leche: ConLeche/Kernel/FEnv.lean:413-417 FEnv.findTable? — the solution's table lookup is
its view's. -/
theorem ISolution.findTable?_view (J : ISolution) (n : NIdx) :
    J.findTable? n = (SolView J).findTable? n := by
  unfold ISolution.findTable? IFEnv.findTable?
  rw [← ISolution.find?_view, SolView, IStreamIndex.view_rawTable?]
  cases J.idx.base.tbls[n]? with
  | none => rfl
  | some p => obtain ⟨r, t⟩ := p; rfl

/-- con-leche: ConLeche/Verify/SimI.lean:54 ISOK — `IFEnvOK`'s two table halves at one handle. -/
theorem IFEnvOK.optTbl {env : Env} {fe : IFEnv} {s : AState} (hok : StateOK s)
    (h : IFEnvOK env fe s) {n : NIdx} {nm : ConLeche.Name} (hd : denoteN s.store.ns n = some nm) :
    OptTbl s.store (fe.findTable? n) (env.findTable? nm) := by
  cases hf : fe.findTable? n with
  | some t =>
    obtain ⟨nm', pt, h1, h2, h3, -⟩ := h.tblHit n t hf
    rw [hd] at h1
    obtain rfl := Option.some.inj h1
    exact Or.inr ⟨t, pt, rfl, h3, h2⟩
  | none =>
    cases he : env.findTable? nm with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some pt =>
      obtain ⟨n', t, h1, h2, -⟩ := h.tblCover nm pt he
      rw [denoteN_injS hok.wf h1 hd, hf] at h2
      exact nomatch h2

/-! ## One name of the cone -/

/-- con-leche: ConLeche/Cached/Justify.lean:163-183 coneGo — **one name compared and accepted**:
the handle names a constant of the input's index that the solution's refines with the same
table (con-leche's `ConeGood` at its name), and what the twin follows from it covers what
con-leche's `entryNeeds` follows. -/
theorem coneEntry_run {env envS : Env} {fe : IFEnv} {J : ISolution}
    {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)} {n : NIdx} {ns : List NIdx}
    {s s' : AState} (hck : CheckOK false env fe s) (hsol : IFEnvOK envS (SolView J) s)
    (hm : MatesDen s.store J.mates matesU)
    (hrun : coneEntry J fe n s = .ok (some ns, s')) :
    RStep s s' ∧ ∃ nm, denoteN s.store.ns n = some nm ∧
      ConLeche.Cached.ConeGood ⟨mkFEnv envS, matesU⟩ (mkFEnv env).find? (mkFEnv env).findTable?
        nm ∧
      ∀ c, env.find? nm = some c →
        NamesCover s'.store ns (ConLeche.Cached.entryNeeds matesU env.findTable? c).toList := by
  have hok := hck.state
  have hr := hck.readOK
  simp only [coneEntry] at hrun
  cases hf : fe.find? n with
  | none => rw [hf] at hrun; exact nomatch (AM.pure_ok hrun).1
  | some ci =>
  rw [hf] at hrun
  obtain ⟨nm, c, hn, hc, he⟩ := hck.ienv.hit n ci hf
  rw [ISolution.find?_view] at hrun
  cases hf' : (SolView J).find? n with
  | none => rw [hf'] at hrun; exact nomatch (AM.pure_ok hrun).1
  | some ci' =>
  rw [hf'] at hrun
  simp only at hrun
  obtain ⟨nm', c', hn', hc', he'⟩ := hsol.hit n ci' hf'
  rw [hn] at hn'
  obtain rfl := Option.some.inj hn'
  obtain ⟨b, s₁, h1, k1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hb⟩ := refinesB_run hok hr hck.pins hc hc' h1
  rcases AM.ite_ok k1 with ⟨hy, k⟩ | ⟨-, k⟩
  · rcases AM.ite_ok k with ⟨ht, k⟩ | ⟨-, k⟩
    · obtain ⟨ns', s₂, h2, k2⟩ := AM.bind_ok k
      obtain ⟨hns, rfl⟩ := AM.pure_ok k2
      obtain rfl := Option.some.inj hns
      have hck₁ := hs1.checkOK hck
      obtain ⟨hs2, hcov⟩ := entryNeeds_run hck₁ (denoteCI_ext hc hs1.ext)
        (hm.mono hs1.ok.wf hs1.ext) h2
      refine ⟨hs1.trans hs2, nm, hn, ⟨c, c', ?_, ?_, ?_, ?_⟩, fun c₀ hc₀ => ?_⟩
      · rw [mkFEnv_find?]; exact he
      · show (mkFEnv envS).find? nm = some c'; rw [mkFEnv_find?]; exact he'
      · rw [← hb]; simpa using hy
      · rw [mkFEnv_findTable?, mkFEnv_findTable?, ISolution.findTable?_view] at *
        have hn₁ := denoteN_ext hn hs1.ext
        exact tableBeqP_true (hck₁.ienv.optTbl hs1.ok hn₁)
          ((hsol.mono hs1.ext).optTbl hs1.ok hn₁) (by simpa using ht)
      · rw [he] at hc₀
        obtain rfl := Option.some.inj hc₀
        exact hcov
    · exact nomatch (AM.pure_ok k).1
  · exact nomatch (AM.pure_ok k).1

/-! ## The cone walk -/

/-- con-leche: ConLeche/Verify/Cached/Cone.lean:30 ConeClosed — **a handle the walk accepted**: it
names a name the two indices share (`ConeGood`), and everything con-leche's `entryNeeds` follows
from its constant is named by a handle of `S`. -/
@[expose] def ConeSeen (env : Env) (JS : ConLeche.Cached.Solution) (st : EStore)
    (S : Std.HashMap NIdx Bool) (x : NIdx) : Prop :=
  ∃ nm, denoteN st.ns x = some nm ∧
    ConLeche.Cached.ConeGood JS (mkFEnv env).find? (mkFEnv env).findTable? nm ∧
    ∀ c, env.find? nm = some c → ∀ m ∈ (ConLeche.Cached.entryNeeds JS.mates env.findTable? c).toList,
      ∃ h, S.contains h = true ∧ denoteN st.ns h = some m

/-- con-leche: ConLeche/Verify/Cached/Cone.lean:36 coneGo_none_gen — **the walk's accept, read**:
an accepting walk leaves a `seen` holding the one it started from and every name of `work`, each
of its new handles accepted (`ConeSeen`).  Induction on the fuel, and at each fuel on the work
list: a name accepted spends one fuel and puts what it reads in front of the rest. -/
theorem coneGo_run {env envS : Env} {fe : IFEnv} {J : ISolution}
    {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)} :
    ∀ (fuel : Nat) (seen : Std.HashMap NIdx Bool) (work : List NIdx) (s s' : AState)
      (f : Nat) (seen' : Std.HashMap NIdx Bool),
      CheckOK false env fe s → IFEnvOK envS (SolView J) s → MatesDen s.store J.mates matesU →
      coneGo J fe fuel seen work s = .ok ((none, f, seen'), s') →
      RStep s s' ∧ (∀ x, seen.contains x = true → seen'.contains x = true) ∧
        (∀ x ∈ work, seen'.contains x = true) ∧
        ∀ x, seen'.contains x = true →
          seen.contains x = true ∨ ConeSeen env ⟨mkFEnv envS, matesU⟩ s'.store seen' x := by
  intro fuel
  induction fuel with
  | zero =>
    intro seen work
    induction work generalizing seen with
    | nil =>
      intro s s' f seen' hck _ _ h
      simp only [coneGo] at h
      obtain ⟨h1, rfl⟩ := AM.pure_ok h
      simp only [Prod.mk.injEq] at h1
      obtain ⟨-, -, rfl⟩ := h1
      exact ⟨RStep.refl hck.state hck.readOK, fun _ h => h,
        fun _ h => absurd h List.not_mem_nil, fun _ h => Or.inl h⟩
    | cons n work ihw =>
      intro s s' f seen' hck hsol hm h
      simp only [coneGo] at h
      rcases AM.ite_ok h with ⟨hs, k⟩ | ⟨-, k⟩
      · obtain ⟨hst, hsub, hwork, hnew⟩ := ihw seen s s' f seen' hck hsol hm k
        refine ⟨hst, hsub, fun x hx => ?_, hnew⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hsub x hs
        · exact hwork x hx
      · exact nomatch (Prod.mk.inj (Prod.mk.inj (Except.ok.inj k)).1).1
  | succ d ihd =>
    intro seen work
    induction work generalizing seen with
    | nil =>
      intro s s' f seen' hck _ _ h
      simp only [coneGo] at h
      obtain ⟨h1, rfl⟩ := AM.pure_ok h
      simp only [Prod.mk.injEq] at h1
      obtain ⟨-, -, rfl⟩ := h1
      exact ⟨RStep.refl hck.state hck.readOK, fun _ h => h,
        fun _ h => absurd h List.not_mem_nil, fun _ h => Or.inl h⟩
    | cons n work ihw =>
      intro s s' f seen' hck hsol hm h
      simp only [coneGo] at h
      rcases AM.ite_ok h with ⟨hs, k⟩ | ⟨-, k⟩
      · obtain ⟨hst, hsub, hwork, hnew⟩ := ihw seen s s' f seen' hck hsol hm k
        refine ⟨hst, hsub, fun x hx => ?_, hnew⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hsub x hs
        · exact hwork x hx
      obtain ⟨o, s₁, h1, k1⟩ := AM.bind_ok k
      cases o with
      | none => exact nomatch (Prod.mk.inj (Prod.mk.inj (Except.ok.inj k1)).1).1
      | some ns =>
        obtain ⟨hs1, nm, hn, hgood, hcov⟩ := coneEntry_run hck hsol hm h1
        simp only at k1
        have hck₁ := hs1.checkOK hck
        obtain ⟨hs2, hsub2, hwork2, hnew2⟩ := ihd (seen.insert n true) (ns ++ work) s₁ s'
          f seen' hck₁ (hsol.mono hs1.ext) (hm.mono hs1.ok.wf hs1.ext) k1
        have hins : ∀ x, seen.contains x = true → (seen.insert n true).contains x = true :=
          fun x hx => by rw [Std.HashMap.contains_insert]; simp [hx]
        have hn_in : (seen.insert n true).contains n = true := by
          rw [Std.HashMap.contains_insert]; simp
        refine ⟨hs1.trans hs2, fun x hx => hsub2 x (hins x hx), fun x hx => ?_, fun x hx => ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hsub2 x hn_in
          · exact hwork2 x (List.mem_append_right _ hx)
        · rcases hnew2 x hx with hx | hx
          · rw [Std.HashMap.contains_insert] at hx
            rcases Bool.or_eq_true_iff.mp hx with hx | hx
            · -- `x` is `n`, accepted here
              obtain rfl : n = x := eq_of_beq hx
              right
              refine ⟨nm, denoteN_ext hn (hs1.ext.trans hs2.ext), hgood, fun c hc m hm => ?_⟩
              obtain ⟨y, hy, hyn⟩ := hcov c hc m hm
              exact ⟨y, hwork2 y (List.mem_append_left _ hy), denoteN_ext hyn hs2.ext⟩
            · exact .inl hx
          · exact .inr hx

/-! ## The justification -/

/-- con-leche: ConLeche/Cached/Justify.lean:185-196 justifyWhy — **THEOREM 1 for the
justification**: the twin justifying the statement `cv` against the solution gives con-leche's
`justifyWhy` accepting its denotation, at the input's environment and the solution's
(`⟨mkFEnv envS, matesU⟩`, con-leche's `solutionOf`). -/
theorem justifyWhy_run {env envS : Env} {fe : IFEnv} {J : ISolution}
    {matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)} {cv : IConstantVal}
    {c : ConstantVal} {s s' : AState} (hck : CheckOK false env fe s)
    (hsol : IFEnvOK envS (SolView J) s) (hm : MatesDen s.store J.mates matesU)
    (hc : Frontend.denoteCV s.store cv = some c)
    (hrun : Arena.justifyWhy J fe cv s = .ok (none, s')) :
    RStep s s' ∧ ConLeche.Cached.justifyWhy ⟨mkFEnv envS, matesU⟩ (mkFEnv env) c = none := by
  have hok := hck.state
  have hr := hck.readOK
  obtain ⟨hnm, -, hty⟩ := denoteCV_inv hc
  simp only [Arena.justifyWhy] at hrun
  cases hf : J.find? cv.name with
  | none =>
    rw [hf] at hrun
    obtain ⟨x, s₁, -, k⟩ := AM.bind_ok hrun
    exact nomatch (AM.pure_ok k).1
  | some cS =>
  rw [hf] at hrun
  simp only at hrun
  rw [ISolution.find?_view] at hf
  obtain ⟨nm, cSU, hn, hcS, heS⟩ := hsol.hit _ cS hf
  rw [hnm] at hn
  obtain rfl := Option.some.inj hn
  obtain ⟨b, s₁, h1, k1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hb⟩ := sameCvUpToLevels_run hok hr hc (denoteCI_toConstantVal hcS) h1
  rcases AM.ite_ok k1 with ⟨-, k⟩ | ⟨hy, k⟩
  · obtain ⟨x, s₂, -, k⟩ := AM.bind_ok k
    exact nomatch (AM.pure_ok k).1
  have hb' : ConLeche.Cached.sameCvUpToLevels c cSU.toConstantVal = true := by
    rw [← hb]; simpa using hy
  have hck₁ := hs1.checkOK hck
  obtain ⟨⟨seen, ns⟩, s₂, h2, k2⟩ := AM.bind_ok k
  obtain ⟨hs2, hcovT⟩ := justifyNeeds_run hck₁ (denote_ext hty hs1.ext) h2
  have hck₂ := hs2.checkOK hck₁
  simp only at k2
  obtain ⟨⟨r, f, seen'⟩, s₃, h3, k3⟩ := AM.bind_ok k2
  cases r with
  | some m =>
    simp only at k3
    obtain ⟨x, s₄, -, k⟩ := AM.bind_ok k3
    exact nomatch (AM.pure_ok k).1
  | none =>
  simp only at k3
  obtain ⟨-, rfl⟩ := AM.pure_ok k3
  have hx12 := hs1.ext.trans hs2.ext
  obtain ⟨hs3, -, hwork, hnew⟩ := coneGo_run _ _ _ s₂ s' f seen' hck₂
    ((hsol.mono hs1.ext).mono hs2.ext) ((hm.mono hs1.ok.wf hs1.ext).mono hs2.ok.wf hs2.ext) h3
  refine ⟨(hs1.trans hs2).trans hs3, ?_⟩
  let T : ConLeche.Name → Prop := fun nm => ∃ h, seen'.contains h = true ∧
    denoteN s'.store.ns h = some nm
  refine Compare.justifyWhy_of_cone (fun n ci h => Compare.mkFEnv_find_mem h)
    ⟨cSU, by show (mkFEnv envS).find? c.name = _; rw [mkFEnv_find?]; exact heS, hb', T, ?_, ?_⟩
  · intro nm ⟨h, hh, hhn⟩
    rcases hnew h hh with hh' | ⟨nm', hn', hg, hc'⟩
    · simp at hh'
    rw [hhn] at hn'
    obtain rfl := Option.some.inj hn'
    refine ⟨hg, fun ci hci m hm => ?_⟩
    rw [mkFEnv_find?] at hci
    have hfT : (mkFEnv env).findTable? = env.findTable? := funext (mkFEnv_findTable? env)
    rw [hfT] at hm
    exact hc' ci hci m (by simpa using hm)
  · intro m hm
    obtain ⟨y, hy, hyn⟩ := hcovT m (by simpa using hm)
    exact ⟨y, hwork y hy, denoteN_ext hyn hs3.ext⟩

end ConRon.Bridge

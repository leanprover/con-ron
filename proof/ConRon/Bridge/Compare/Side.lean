/-
# `ConRon.Bridge.Compare.Side` — the records a fold with a solution checks

The twin's `sideRecords` (`Arena/Justify.lean`) against con-leche's: a definition, theorem or
opaque constant whose value uses `sorryAx` (and whose name is no built-in axiom's) becomes the
axiom of its statement.  The value test is `mentionsConst` at the `sorryAx` pin, a memoised DAG
walk (`mentionsConstGo_run`: its answer is con-leche's `Expr.mentionsAnyConst [sorryAxName]`,
which `mentionsAnyConstC` computes, and its memo stays sound).
-/
module

public import ConRon.Bridge.Compare.Justify
public import ConRon.Arena.Inductives.StructParts
import ConRon.Bridge.Specs
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Frontend.Rel
import ConLeche.Verify.Cached.IndWalksC

public section

namespace ConRon.Bridge

set_option autoImplicit false

open ConLeche ConRon.Arena

/-! ## The value test -/

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1795-1839 mentionsAnyConstXP — **the mention memo is
sound**: every handle it answers for denotes a term whose mention of `tn` is the answer. -/
@[expose] def MentionMemoOK (st : EStore) (tn : ConLeche.Name) (memo : Std.HashMap EIdx Bool) :
    Prop :=
  ∀ h r, memo[h]? = some r → ∃ e, denoteE st h = some e ∧ r = e.mentionsAnyConst [tn]

/-- con-leche: none — an empty memo is sound. -/
theorem MentionMemoOK.empty (st : EStore) (tn : ConLeche.Name) : MentionMemoOK st tn ∅ :=
  fun h r hr => by simp at hr

/-- con-leche: none — a sound memo stays sound with a sound answer recorded. -/
theorem MentionMemoOK.insert {st : EStore} {tn : ConLeche.Name} {memo : Std.HashMap EIdx Bool}
    (hm : MentionMemoOK st tn memo) {h : EIdx} {e : Expr} (he : denoteE st h = some e) :
    MentionMemoOK st tn (memo.insert h (e.mentionsAnyConst [tn])) := by
  intro h' r hr
  rw [Std.HashMap.getElem?_insert] at hr
  split at hr
  · next hh =>
    obtain rfl := eq_of_beq hh
    exact ⟨e, he, (Option.some.inj hr).symm⟩
  · exact hm h' r hr

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1795-1839 mentionsAnyConstXP — **THEOREM 1 for the
mention walk**: its answer is con-leche's `Expr.mentionsAnyConst [tn]` at the term the handle
denotes, the memo stays sound, and the state does not move. -/
theorem mentionsConstGo_run {T : NIdx} {tn : ConLeche.Name} :
    ∀ (fuel : Nat) (memo : Std.HashMap EIdx Bool) (h : EIdx) (e : Expr) (s s' : AState)
      (r : Bool) (m' : Std.HashMap EIdx Bool),
      StateOK s → denoteN s.store.ns T = some tn → denoteE s.store h = some e →
      MentionMemoOK s.store tn memo →
      mentionsConstGo T memo fuel h s = .ok ((r, m'), s') →
      s = s' ∧ r = e.mentionsAnyConst [tn] ∧ MentionMemoOK s.store tn m' := by
  have hbeq : ∀ a b : ConLeche.Name, (a == b) = decide (a = b) := fun a b => by
    by_cases h : a = b <;> simp [h]
  intro fuel
  induction fuel with
  | zero =>
    intro memo h e s s' r m' _ _ _ _ hrun
    simp only [mentionsConstGo] at hrun
    exact absurd hrun (fun hc => AM.fail_ok hc)
  | succ fuel ih =>
    intro memo h e s s' r m' hok hT hd hm hrun
    have hwf := hok.wf
    simp only [mentionsConstGo] at hrun
    obtain ⟨v, s₁, hv, h3⟩ := AM.bind_ok hrun
    obtain ⟨hs1, hw⟩ := view_run hv
    rw [hs1] at h3
    -- a memo hit
    have hit : ∀ {r₀ : Bool}, memo[h]? = some r₀ →
        (pure ((r₀, memo) : Bool × Std.HashMap EIdx Bool) : AM (Bool × Std.HashMap EIdx Bool))
          s = .ok ((r, m'), s') →
        s = s' ∧ r = e.mentionsAnyConst [tn] ∧ MentionMemoOK s.store tn m' := by
      intro r₀ hlk hz
      have hz' := AM.pure_ok hz
      simp only [Prod.mk.injEq] at hz'
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hz'
      obtain ⟨e', he', hre⟩ := hm h _ hlk
      obtain rfl := Option.some.inj (hd.symm.trans he')
      exact ⟨rfl, hre, hm⟩
    -- a miss: record the answer
    have fin : ∀ {y : Bool × Std.HashMap EIdx Bool}, y.1 = e.mentionsAnyConst [tn] →
        MentionMemoOK s.store tn y.2 →
        (pure ((y.1, y.2.insert h y.1) : Bool × Std.HashMap EIdx Bool) :
          AM (Bool × Std.HashMap EIdx Bool)) s = .ok ((r, m'), s') →
        s = s' ∧ r = e.mentionsAnyConst [tn] ∧ MentionMemoOK s.store tn m' := by
      intro y hy hmy hz
      have hz' := AM.pure_ok hz
      simp only [Prod.mk.injEq] at hz'
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hz'
      refine ⟨rfl, hy, ?_⟩
      rw [hy]; exact hmy.insert hd
    cases v with
    | bvar j =>
      obtain ⟨hz, rfl⟩ := AM.pure_ok h3
      simp only [Prod.mk.injEq] at hz; obtain ⟨rfl, rfl⟩ := hz
      obtain rfl := denote_bvar_inv hwf hw hd
      exact ⟨rfl, rfl, hm⟩
    | sort u =>
      obtain ⟨hz, rfl⟩ := AM.pure_ok h3
      simp only [Prod.mk.injEq] at hz; obtain ⟨rfl, rfl⟩ := hz
      obtain ⟨l, rfl, -⟩ := denote_sort_inv hwf hw hd
      exact ⟨rfl, rfl, hm⟩
    | lit l =>
      obtain ⟨hz, rfl⟩ := AM.pure_ok h3
      simp only [Prod.mk.injEq] at hz; obtain ⟨rfl, rfl⟩ := hz
      obtain rfl := denote_lit_inv hwf hw hd
      exact ⟨rfl, rfl, hm⟩
    | const n us =>
      obtain ⟨hz, rfl⟩ := AM.pure_ok h3
      simp only [Prod.mk.injEq] at hz; obtain ⟨rfl, rfl⟩ := hz
      obtain ⟨nm, ls, rfl, hn, -⟩ := denote_const_inv hwf hw hd
      refine ⟨rfl, ?_, hm⟩
      rw [denoteN_beqS hwf hn hT]
      simp [Expr.mentionsAnyConst, hbeq]
    | fvar k ty =>
      obtain ⟨t, rfl, ht⟩ := denote_fvar_inv hwf hw hd
      simp only at h3
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h3; exact hit hlk h3
      | none =>
        rw [hlk] at h3
        obtain ⟨⟨b, m1⟩, s₂, hc1, hz⟩ := AM.bind_ok h3
        obtain ⟨rfl, hb, hm1⟩ := ih memo ty t s s₂ b m1 hok hT ht hm hc1
        exact fin (y := (b, m1)) (by simp [Expr.mentionsAnyConst, hb]) hm1 hz
    | app f a =>
      obtain ⟨ef, ea, rfl, hf, ha⟩ := denote_app_inv hwf hw hd
      simp only at h3
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h3; exact hit hlk h3
      | none =>
        rw [hlk] at h3
        obtain ⟨⟨b1, m1⟩, s₂, hc1, h4⟩ := AM.bind_ok h3
        obtain ⟨rfl, hb1, hm1⟩ := ih memo f ef s s₂ b1 m1 hok hT hf hm hc1
        obtain ⟨⟨b2, m2⟩, s₃, hc2, h5⟩ := AM.bind_ok h4
        obtain ⟨rfl, hb2, hm2⟩ := ih m1 a ea s s₃ b2 m2 hok hT ha hm1 hc2
        obtain ⟨y, s₄, hy, hz⟩ := AM.bind_ok h5
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hy
        exact fin (y := (b1 || b2, m2)) (by simp [Expr.mentionsAnyConst, hb1, hb2]) hm2 hz
    | lam ty b =>
      obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_lam_inv hwf hw hd
      simp only at h3
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h3; exact hit hlk h3
      | none =>
        rw [hlk] at h3
        obtain ⟨⟨b1, m1⟩, s₂, hc1, h4⟩ := AM.bind_ok h3
        obtain ⟨rfl, hb1, hm1⟩ := ih memo ty et s s₂ b1 m1 hok hT hty hm hc1
        obtain ⟨⟨b2, m2⟩, s₃, hc2, h5⟩ := AM.bind_ok h4
        obtain ⟨rfl, hb2, hm2⟩ := ih m1 b eb s s₃ b2 m2 hok hT hbd hm1 hc2
        obtain ⟨y, s₄, hy, hz⟩ := AM.bind_ok h5
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hy
        exact fin (y := (b1 || b2, m2)) (by simp [Expr.mentionsAnyConst, hb1, hb2]) hm2 hz
    | forallE ty b =>
      obtain ⟨et, eb, rfl, hty, hbd⟩ := denote_forallE_inv hwf hw hd
      simp only at h3
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h3; exact hit hlk h3
      | none =>
        rw [hlk] at h3
        obtain ⟨⟨b1, m1⟩, s₂, hc1, h4⟩ := AM.bind_ok h3
        obtain ⟨rfl, hb1, hm1⟩ := ih memo ty et s s₂ b1 m1 hok hT hty hm hc1
        obtain ⟨⟨b2, m2⟩, s₃, hc2, h5⟩ := AM.bind_ok h4
        obtain ⟨rfl, hb2, hm2⟩ := ih m1 b eb s s₃ b2 m2 hok hT hbd hm1 hc2
        obtain ⟨y, s₄, hy, hz⟩ := AM.bind_ok h5
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hy
        exact fin (y := (b1 || b2, m2)) (by simp [Expr.mentionsAnyConst, hb1, hb2]) hm2 hz
    | letE ty w b =>
      obtain ⟨et, ew, eb, rfl, hty, hww, hbd⟩ := denote_letE_inv hwf hw hd
      simp only at h3
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h3; exact hit hlk h3
      | none =>
        rw [hlk] at h3
        obtain ⟨⟨b1, m1⟩, s₂, hc1, h4⟩ := AM.bind_ok h3
        obtain ⟨rfl, hb1, hm1⟩ := ih memo ty et s s₂ b1 m1 hok hT hty hm hc1
        obtain ⟨⟨b2, m2⟩, s₃, hc2, h5⟩ := AM.bind_ok h4
        obtain ⟨rfl, hb2, hm2⟩ := ih m1 w ew s s₃ b2 m2 hok hT hww hm1 hc2
        obtain ⟨⟨b3, m3⟩, s₄, hc3, h6⟩ := AM.bind_ok h5
        obtain ⟨rfl, hb3, hm3⟩ := ih m2 b eb s s₄ b3 m3 hok hT hbd hm2 hc3
        obtain ⟨y, s₅, hy, hz⟩ := AM.bind_ok h6
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hy
        exact fin (y := (b1 || b2 || b3, m3)) (by simp [Expr.mentionsAnyConst, hb1, hb2, hb3])
          hm3 hz
    | proj n i sub =>
      obtain ⟨nm, es, rfl, hn, hs⟩ := denote_proj_inv hwf hw hd
      simp only at h3
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h3; exact hit hlk h3
      | none =>
        rw [hlk] at h3
        obtain ⟨⟨b1, m1⟩, s₂, hc1, h4⟩ := AM.bind_ok h3
        obtain ⟨rfl, hb1, hm1⟩ := ih memo sub es s s₂ b1 m1 hok hT hs hm hc1
        obtain ⟨y, s₄, hy, hz⟩ := AM.bind_ok h4
        obtain ⟨rfl, rfl⟩ := AM.pure_ok hy
        have hnb := denoteN_beqS hwf hn hT
        exact fin (y := (n == T || b1, m1)) (by simp [Expr.mentionsAnyConst, hb1, hnb, hbeq]) hm1 hz

/-- con-leche: ConLeche/Cached/ExprOpsC.lean:1841-1843 mentionsAnyConstC — **the value test is
con-leche's**: `mentionsConst` at a handle of `tn` answers `mentionsAnyConstC [tn]`. -/
theorem mentionsConst_run {T : NIdx} {tn : ConLeche.Name} {h : EIdx} {e : Expr} {s s' : AState}
    {r : Bool} (hok : StateOK s) (hT : denoteN s.store.ns T = some tn)
    (hd : denoteE s.store h = some e) (hrun : mentionsConst T h s = .ok (r, s')) :
    s = s' ∧ r = ConLeche.Expr.mentionsAnyConstC [tn] e := by
  simp only [mentionsConst] at hrun
  obtain ⟨⟨b, m⟩, s₁, h1, k⟩ := AM.bind_ok hrun
  obtain ⟨rfl, hb, -⟩ := mentionsConstGo_run _ _ _ _ _ _ _ _ hok hT hd
    (MentionMemoOK.empty _ _) h1
  obtain ⟨rfl, rfl⟩ := AM.pure_ok k
  exact ⟨rfl, by rw [ConLeche.Expr.mentionsAnyConstC_spec]; exact hb⟩

/-! ## The records -/

/-- con-leche: ConLeche/Cached/Justify.lean:53-61 sideRecord — a value record's arm: the axiom of
its statement exactly where con-leche's is. -/
theorem sideRecordVal_run {d : IDeclaration} {cv : IConstantVal}
    {c : ConstantVal} {v : EIdx} {e : Expr} {s s' : AState} {r : IDeclaration}
    (hok : StateOK s) (hp : PinsOK s) (hc : Frontend.denoteCV s.store cv = some c)
    (he : denoteE s.store v = some e)
    (hrun : sideRecordVal d cv v s = .ok (r, s')) :
    s = s' ∧ ((!ConLeche.Cached.builtinAxiomName c.name &&
        ConLeche.Expr.mentionsAnyConstC [ConLeche.sorryAxName] e) = true ∧ r = .axiomDecl cv ∨
      (!ConLeche.Cached.builtinAxiomName c.name &&
        ConLeche.Expr.mentionsAnyConstC [ConLeche.sorryAxName] e) = false ∧ r = d) := by
  have hn := (denoteCV_inv hc).1
  simp only [sideRecordVal] at hrun
  obtain ⟨b, s₁, h1, k1⟩ := AM.bind_ok hrun
  obtain ⟨rfl, hb⟩ := builtinAxiomName_run hok hp hn h1
  rcases AM.ite_ok k1 with ⟨hy, k⟩ | ⟨hn1, k⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
    refine ⟨rfl, .inr ⟨?_, rfl⟩⟩
    rw [← hb, show b = true by simpa using hy]; rfl
  · obtain ⟨sa, s₂, h2, k2⟩ := AM.bind_ok k
    obtain ⟨rfl, hsa⟩ := pinAt_run hp pinNames_eq_sorryAxName h2
    obtain ⟨m, s₃, h3, k3⟩ := AM.bind_ok k2
    obtain ⟨rfl, hm⟩ := mentionsConst_run hok hsa he h3
    have hb' : b = false := by simpa using hn1
    rcases AM.ite_ok k3 with ⟨hy3, k⟩ | ⟨hn3, k⟩
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
      refine ⟨rfl, .inl ⟨?_, rfl⟩⟩
      rw [← hb, hb', ← hm, show m = true by simpa using hy3]; rfl
    · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
      refine ⟨rfl, .inr ⟨?_, rfl⟩⟩
      rw [← hb, hb', ← hm, show m = false by simpa using hn3]; rfl

/-- con-leche: ConLeche/Cached/Justify.lean:53-61 sideRecord — **THEOREM 1 for `sideRecord`**:
the twin's record denotes con-leche's `sideRecord` of the denoted one, persistently if the
record is, and the state does not move. -/
theorem sideRecord_run {d : IDeclaration} {dP : Declaration} {s s' : AState} {r : IDeclaration}
    (hok : StateOK s) (hp : PinsOK s) (hd : Frontend.denoteDecl s.store d = some dP)
    (hrun : sideRecord d s = .ok (r, s')) :
    s = s' ∧ Frontend.denoteDecl s.store r = some (ConLeche.Cached.sideRecord dP) ∧
      (PersDecl d → PersDecl r) := by
  cases d with
  | defnDecl cv v hh =>
    simp only [Frontend.denoteDecl] at hd
    split at hd
    · next c e hc he =>
      obtain rfl := Option.some.inj hd
      obtain ⟨rfl, hcase⟩ := sideRecordVal_run (d := .defnDecl cv v hh)
        hok hp hc he hrun
      refine ⟨rfl, ?_⟩
      rcases hcase with ⟨hy, rfl⟩ | ⟨hn, rfl⟩
      · exact ⟨by simp [ConLeche.Cached.sideRecord, hy, Frontend.denoteDecl, hc],
          fun h => h.1⟩
      · exact ⟨by simp [ConLeche.Cached.sideRecord, hn, Frontend.denoteDecl, hc, he], id⟩
    · exact nomatch hd
  | thmDecl cv v =>
    simp only [Frontend.denoteDecl] at hd
    split at hd
    · next c e hc he =>
      obtain rfl := Option.some.inj hd
      obtain ⟨rfl, hcase⟩ := sideRecordVal_run (d := .thmDecl cv v)
        hok hp hc he hrun
      refine ⟨rfl, ?_⟩
      rcases hcase with ⟨hy, rfl⟩ | ⟨hn, rfl⟩
      · exact ⟨by simp [ConLeche.Cached.sideRecord, hy, Frontend.denoteDecl, hc],
          fun h => h.1⟩
      · exact ⟨by simp [ConLeche.Cached.sideRecord, hn, Frontend.denoteDecl, hc, he], id⟩
    · exact nomatch hd
  | opaqueDecl cv v =>
    simp only [Frontend.denoteDecl] at hd
    split at hd
    · next c e hc he =>
      obtain rfl := Option.some.inj hd
      obtain ⟨rfl, hcase⟩ := sideRecordVal_run (d := .opaqueDecl cv v)
        hok hp hc he hrun
      refine ⟨rfl, ?_⟩
      rcases hcase with ⟨hy, rfl⟩ | ⟨hn, rfl⟩
      · exact ⟨by simp [ConLeche.Cached.sideRecord, hy, Frontend.denoteDecl, hc],
          fun h => h.1⟩
      · exact ⟨by simp [ConLeche.Cached.sideRecord, hn, Frontend.denoteDecl, hc, he], id⟩
    · exact nomatch hd
  | axiomDecl cv =>
    simp only [sideRecord] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨c, hc, rfl⟩ := hd
    exact ⟨rfl, by simp [Frontend.denoteDecl, hc, ConLeche.Cached.sideRecord], id⟩
  | indDecl b nP =>
    simp only [sideRecord] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨c, hc, rfl⟩ := hd
    exact ⟨rfl, by simp [Frontend.denoteDecl, hc, ConLeche.Cached.sideRecord], id⟩
  | quotDecl k cv =>
    simp only [sideRecord] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    simp only [Frontend.denoteDecl, Option.map_eq_some_iff] at hd
    obtain ⟨c, hc, rfl⟩ := hd
    exact ⟨rfl, by simp [Frontend.denoteDecl, hc, ConLeche.Cached.sideRecord], id⟩

/-- con-leche: ConLeche/Cached/Justify.lean:63-67 sideRecords — **THEOREM 1 for `sideRecords`**:
the twin's records, onto `out`, denote con-leche's `sideRecord` of each denoted record, onto
`out`'s denotation; persistent records stay persistent, and the state does not move. -/
theorem sideRecordsGo_run {s s' : AState} (hok : StateOK s) (hp : PinsOK s) :
    ∀ (ds out r : List IDeclaration) (dsP outP : List Declaration),
      denoteDecls s.store out = some outP → denoteDecls s.store ds = some dsP →
      sideRecordsGo out ds s = .ok (r, s') →
      s = s' ∧ denoteDecls s.store r = some (outP ++ dsP.map ConLeche.Cached.sideRecord) ∧
        ((∀ x ∈ out, PersDecl x) → (∀ x ∈ ds, PersDecl x) → ∀ x ∈ r, PersDecl x) := by
  intro ds
  induction ds with
  | nil =>
    intro out r dsP outP hout hds hrun
    simp only [denoteDecls, Option.some.injEq] at hds
    subst hds
    simp only [sideRecordsGo] at hrun
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
    exact ⟨rfl, by simpa using hout, fun h _ => h⟩
  | cons d ds ih =>
    intro out r dsP outP hout hds hrun
    simp only [denoteDecls] at hds
    split at hds
    · next x xs hx hxs =>
      obtain rfl := Option.some.inj hds
      simp only [sideRecordsGo] at hrun
      obtain ⟨d', s₁, h1, k1⟩ := AM.bind_ok hrun
      obtain ⟨rfl, hd', hpd'⟩ := sideRecord_run hok hp hx h1
      have hout' : denoteDecls s.store (out ++ [d']) =
          some (outP ++ [ConLeche.Cached.sideRecord x]) := by
        exact Frontend.denoteDecls_append hout (by simp [denoteDecls, hd'])
      obtain ⟨rfl, hr, hpr⟩ := ih (out ++ [d']) r xs _ hout' hxs k1
      refine ⟨rfl, by simpa using hr, fun ho hd x hxr => hpr (fun y hy => ?_)
        (fun y hy => hd y (List.mem_cons_of_mem _ hy)) x hxr⟩
      rcases List.mem_append.mp hy with hy | hy
      · exact ho y hy
      · rw [List.mem_singleton] at hy; subst hy
        exact hpd' (hd d List.mem_cons_self)
    · exact nomatch hds

end ConRon.Bridge

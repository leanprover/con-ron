/-
# `ConRon.Bridge.Inductives.NativeInstall` — Theorem 1 for the fixpoint route

`Arena/Inductives/NativeInstall.lean`'s seventeen twins against
`ConLeche/Kernel/Inductives/NativeInstall.lean` (and `NativeInstallF.lean`'s
five `abbrev`s, which are the same five functions).  This is the route
`nativeParts?` recognises: the two-pass install of a direct recursive block.

## `NativePass` is not generic, and what that costs the statement

con-leche parameterises `NativePass` by the environment representation (`Env`
at the pure install, `FEnv` at its cached driver's mirror); the arena has ONE
(task #97d-2's deviation 9), so the twin's record is `NativePass` flat and the
relation below compares it with `ConLeche.NativePass Env`.  Nothing else about
the two records differs.

## The capability record's verdict, and why the statement has a `Bool` beside it

Task #268's `checkNativePass` runs at a syntactic reading of `is_rec` and
answers whether the classification CONFIRMS it; `checkNative` re-runs the pass
once if it does not.  The `Bool` is therefore part of the answer relation, and
the route theorem's two branches are the two values it can take.
-/
import ConRon.Bridge.Inductives.SumInstall

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge

/-! ## The free-variable memo -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:143-148 MentionsFvarMemoInv
The handle-keyed memo of `mentionsFvar q`. -/
def FvarMemoOK (q : Nat) (tbl : Std.HashMap EIdx Bool) (st : EStore) : Prop :=
  ∀ (k : EIdx) (r : Bool), tbl[k]? = some r →
    ∃ e, denoteE st k = some e ∧ r = Expr.mentionsFvar q e

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:143-148 MentionsFvarMemoInv.insert
— recording the real answer keeps the memo sound. -/
theorem FvarMemoOK.insert {q : Nat} {tbl : Std.HashMap EIdx Bool} {st : EStore}
    (hm : FvarMemoOK q tbl st) {h : EIdx} {hP : Expr} {r : Bool}
    (hd : denoteE st h = some hP) (heq : r = Expr.mentionsFvar q hP) :
    FvarMemoOK q (tbl.insert h r) st := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact ⟨hP, hd, heq⟩
  · exact hm k r' hk

/-- con-leche: none — the memo is about denotations, so it survives an
append. -/
theorem FvarMemoOK.mono {q : Nat} {tbl : Std.HashMap EIdx Bool} {st st' : EStore}
    (hm : FvarMemoOK q tbl st) (hx : Ext st st') : FvarMemoOK q tbl st' := by
  intro k r hk
  obtain ⟨e, he, hr⟩ := hm k r hk
  exact ⟨e, denote_ext he hx, hr⟩

/-! ## The three pure readers off the record -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:100-103 nativeIsRec
Is any field recursive or reflexive?  A `Bool` off the kinds alone, so the
twin's and con-leche's agree under `kindOf` — and this one is CLOSED. -/
theorem nativeIsRec_spec (kinds : List (List Arena.RecFieldKind)) :
    Arena.nativeIsRec kinds = ConLeche.nativeIsRec (kinds.map (·.map kindOf)) := by
  simp only [Arena.nativeIsRec, ConLeche.nativeIsRec, List.any_map]
  congr 1
  funext ks
  simp only [Function.comp_apply, List.any_map]
  congr 1
  funext k
  cases k <;> rfl

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:105-108 nativeCaps
The capability record the completed parts license.

**CLOSED** (task #97-P3-Ind round 5), at `PSpecP` for the reason
`nativeCapsAt_spec` is: `nativeCapsAt_spec` at `nativeIsRec p.kinds`, through
`nativeIsRec_spec` above. -/
theorem nativeCaps_spec (p : Arena.NativeParts) (q : ConLeche.NativeParts) :
    PSpecP (fun st => PartsRel st p q)
      (Arena.nativeCaps p) (RCaps (ConLeche.nativeCaps q)) := by
  intro s₀ s' r hok hpins hrel hrun
  simp only [Arena.nativeCaps] at hrun
  have h := nativeCapsAt_spec p.toInductiveShape q.toInductiveShape
    (Arena.nativeIsRec p.kinds) s₀ s' r hok hpins hrel.shape hrun
  rw [nativeIsRec_spec p.kinds, hrel.kinds] at h
  simpa only [ConLeche.nativeCaps] using h

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:110-128 nativeRawRec
The SYNTACTIC reading of `is_rec` off the declared constructor types, before
anything is normalised (task #268's first pass runs at this verdict).

**CLOSED** (task #97-P3-Ind round 6). -/
theorem nativeRawRec_spec (p : Arena.NativeParts) (q : ConLeche.NativeParts) :
    PSpec (fun st => PartsRel st p q)
      (Arena.nativeRawRec p) (RV (ConLeche.nativeRawRec q)) := by
  intro s₀ s' r hok hrel hrun
  have hT := denoteCV_name hrel.shape.cvT
  have hcs := hrel.shape.ctors
  have hnP := hrel.shape.nP
  simp only [Arena.nativeRawRec] at hrun
  show PStep s₀ s' ∧ r = ConLeche.nativeRawRec q
  simp only [ConLeche.nativeRawRec]
  cases hc : p.ctors with
  | nil =>
    rw [hc] at hrun hcs
    simp only [denoteCtors, Option.some.injEq] at hcs
    rw [← hcs]
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons c cs =>
  obtain ⟨cv, n⟩ := c
  rw [hc] at hcs
  simp only [denoteCtors] at hcs
  cases hcv : Frontend.denoteCV s₀.store cv with
  | none => rw [hcv] at hcs; simp at hcs
  | some cP =>
  cases hrest : denoteCtors s₀.store cs with
  | none => rw [hcv, hrest] at hcs; simp at hcs
  | some restP =>
  rw [hcv, hrest] at hcs
  rw [← (Option.some.inj hcs)]
  cases cs with
  | cons c2 cs2 =>
    rw [hc] at hrun
    simp only [denoteCtors] at hrest
    cases h2 : Frontend.denoteCV s₀.store c2.1 with
    | none =>
      obtain ⟨c2v, c2n⟩ := c2
      simp only at h2
      rw [h2] at hrest; simp at hrest
    | some c2P =>
      obtain ⟨c2v, c2n⟩ := c2
      simp only at h2
      cases h3 : denoteCtors s₀.store cs2 with
      | none => rw [h2, h3] at hrest; simp at hrest
      | some r3 =>
        rw [h2, h3] at hrest
        rw [← (Option.some.inj hrest)]
        obtain ⟨rfl, rfl⟩ := pureOk hrun
        exact ⟨PStep.refl hok, rfl⟩
  | nil =>
  simp only [denoteCtors, Option.some.injEq] at hrest
  subst hrest
  rw [hc] at hrun
  dsimp only at hrun ⊢
  obtain ⟨q1, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨hs1, hq1⟩ := stripPis_pstep hok (denoteCV_type hcv) k1
  rw [hs1] at z1
  rw [← hnP]
  rcases q1 with _ | ⟨cbs, cb⟩
  · obtain ⟨rfl, rfl⟩ := pureOk z1
    refine ⟨PStep.refl hok, ?_⟩
    rw [stripPis_none hq1]
  obtain ⟨cxs, cbP, hsp, hcbs, -⟩ := denoteBP_someB hq1
  rw [hsp]
  dsimp only
  exact anyM_B_pstep (F := fun b => b.1.mentionsConst q.cvT.name)
    (fun st => denoteN st.ns p.cvT.name = some q.cvT.name) (fun hx h => denoteN_ext h hx)
    (by
      intro b bP t0 t1 x hok0 hq0 hb _ hrun0
      exact mentionsConst_spec _ _ b.1 bP.1 t0 t1 x hok0 ⟨hq0, hb⟩ hrun0)
    _ _ s₀ s' r hok hT (denoteBinders_drop hcbs p.nP) z1

/-! ## `mentionsFvar`, memoised

`mentionsFvarIns` has NO statement of its own — it is the memo-insert helper
(con-leche's `Expr.mentionsFvarIns`), census class (S), and its content is
inside the walk's invariant step. -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:221-257 Expr.mentionsFvarGo
The memoised walk; note the `fvar` arm answers on the LEVEL and does not
descend into the variable's type, which is con-leche's own clause.

**CLOSED** (task #97-P3-Ind round 6). -/
theorem mentionsFvarGo_spec (q : Nat) (memo : Std.HashMap EIdx Bool)
    (fuel : Nat) (h : EIdx) (hP : Expr) :
    PSpec (fun st => denoteE st h = some hP ∧ FvarMemoOK q memo st)
      (Arena.mentionsFvarGo q memo fuel h)
      (fun st r => r.1 = Expr.mentionsFvar q hP ∧ FvarMemoOK q r.2 st) := by
  induction fuel generalizing memo h hP with
  | zero =>
    intro s₀ s' r _ _ hrun
    simp only [Arena.mentionsFvarGo] at hrun
    exact absurd hrun (fun hc => failOk hc)
  | succ fuel ih =>
    intro s₀ s' r hok hp hrun
    obtain ⟨hd, hm⟩ := hp
    simp only [Arena.mentionsFvarGo] at hrun
    obtain ⟨v, s₁, hv, h2⟩ := bindOk hrun
    obtain ⟨hv0, hw⟩ := view_run hv
    rw [hv0] at h2
    have fin : ∀ {s₂ s₃ : AState} {rr r' : Bool × Std.HashMap EIdx Bool},
        PStep s₀ s₂ → rr.1 = Expr.mentionsFvar q hP → FvarMemoOK q rr.2 s₂.store →
        (pure (Arena.mentionsFvarIns h rr) : AM (Bool × Std.HashMap EIdx Bool)) s₂
          = .ok (r', s₃) →
        PStep s₀ s₃ ∧ r'.1 = Expr.mentionsFvar q hP ∧ FvarMemoOK q r'.2 s₃.store := by
      intro s₂ s₃ rr r' hs hb hmm hz
      obtain ⟨rfl, rfl⟩ := pureOk hz
      exact ⟨hs, hb, FvarMemoOK.insert hmm (denote_ext hd hs.ext) hb⟩
    have hit : ∀ {s₃ : AState} {r₀ : Bool} {r' : Bool × Std.HashMap EIdx Bool},
        memo[h]? = some r₀ →
        (pure ((r₀, memo) : Bool × Std.HashMap EIdx Bool) :
            AM (Bool × Std.HashMap EIdx Bool)) s₀ = .ok (r', s₃) →
        PStep s₀ s₃ ∧ r'.1 = Expr.mentionsFvar q hP ∧ FvarMemoOK q r'.2 s₃.store := by
      intro s₃ r₀ r' hlk hz
      obtain ⟨rfl, rfl⟩ := pureOk hz
      obtain ⟨e, he, hre⟩ := hm h r₀ hlk
      obtain rfl := Option.some.inj (hd.symm.trans he)
      exact ⟨PStep.refl hok, hre, hm⟩
    cases v
    case bvar j =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain rfl := denote_bvar_inv hok.wf hw hd
      exact ⟨PStep.refl hok, by simp [Expr.mentionsFvar, Expr.fvarLeaves], hm⟩
    case sort u =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨l, rfl, _⟩ := denote_sort_inv hok.wf hw hd
      exact ⟨PStep.refl hok, by simp [Expr.mentionsFvar, Expr.fvarLeaves], hm⟩
    case lit l =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain rfl := denote_lit_inv hok.wf hw hd
      exact ⟨PStep.refl hok, by simp [Expr.mentionsFvar, Expr.fvarLeaves], hm⟩
    case const n us =>
      obtain ⟨rfl, rfl⟩ := pureOk h2
      obtain ⟨nm, ls, rfl, _, _⟩ := denote_const_inv hok.wf hw hd
      exact ⟨PStep.refl hok, by simp [Expr.mentionsFvar, Expr.fvarLeaves], hm⟩
    case fvar k ty =>
      obtain ⟨t, rfl, hty⟩ := denote_fvar_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; dsimp only at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        dsimp only at h2
        split at h2
        case isTrue hkq =>
          obtain ⟨rr, sR, kR, zR⟩ := bindOk h2
          obtain ⟨rfl, rfl⟩ := pureOk kR
          exact fin (PStep.refl hok) (by simp only [Expr.mentionsFvar_fvar, hkq, Bool.true_or])
            hm zR
        case isFalse hkq =>
          obtain ⟨rr, sR, kR, zR⟩ := bindOk h2
          obtain ⟨hsA, hrA, hmA⟩ := ih memo ty t s₀ sR rr hok ⟨hty, hm⟩ kR
          exact fin hsA (by simp only [Expr.mentionsFvar_fvar, hrA]; simp [hkq]) hmA zR
    case app x1 x2 =>
      obtain ⟨e1, e2, rfl, hd1, hd2⟩ := denote_app_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; dsimp only at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        dsimp only at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo x1 e1 s₀ sa (b1, m1) hok ⟨hd1, hm⟩ hc1
        simp only at hrA
        cases b1 with
        | true =>
          obtain ⟨rr, sR, kR, zR⟩ := bindOk hn1
          obtain ⟨rfl, rfl⟩ := pureOk kR
          exact fin hsA (by simp only [Expr.mentionsFvar_app, ← hrA, Bool.true_or]) hmA zR
        | false =>
          obtain ⟨rr, sR, kR, zR⟩ := bindOk hn1
          obtain ⟨hsB, hrB, hmB⟩ := ih m1 x2 e2 sa sR rr hsA.ok
            ⟨denote_ext hd2 hsA.ext, hmA⟩ kR
          exact fin (hsA.trans hsB) (by simp only [Expr.mentionsFvar_app, ← hrA, hrB, Bool.false_or]) hmB zR
    case lam x1 x2 xm =>
      obtain ⟨e1, e2, rfl, hd1, hd2⟩ := denote_lam_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; dsimp only at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        dsimp only at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo x1 e1 s₀ sa (b1, m1) hok ⟨hd1, hm⟩ hc1
        simp only at hrA
        cases b1 with
        | true =>
          obtain ⟨rr, sR, kR, zR⟩ := bindOk hn1
          obtain ⟨rfl, rfl⟩ := pureOk kR
          exact fin hsA (by simp only [Expr.mentionsFvar_lam, ← hrA, Bool.true_or]) hmA zR
        | false =>
          obtain ⟨rr, sR, kR, zR⟩ := bindOk hn1
          obtain ⟨hsB, hrB, hmB⟩ := ih m1 x2 e2 sa sR rr hsA.ok
            ⟨denote_ext hd2 hsA.ext, hmA⟩ kR
          exact fin (hsA.trans hsB) (by simp only [Expr.mentionsFvar_lam, ← hrA, hrB, Bool.false_or]) hmB zR
    case forallE x1 x2 xm =>
      obtain ⟨e1, e2, rfl, hd1, hd2⟩ := denote_forallE_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; dsimp only at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        dsimp only at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo x1 e1 s₀ sa (b1, m1) hok ⟨hd1, hm⟩ hc1
        simp only at hrA
        cases b1 with
        | true =>
          obtain ⟨rr, sR, kR, zR⟩ := bindOk hn1
          obtain ⟨rfl, rfl⟩ := pureOk kR
          exact fin hsA (by simp only [Expr.mentionsFvar_forallE, ← hrA, Bool.true_or]) hmA zR
        | false =>
          obtain ⟨rr, sR, kR, zR⟩ := bindOk hn1
          obtain ⟨hsB, hrB, hmB⟩ := ih m1 x2 e2 sa sR rr hsA.ok
            ⟨denote_ext hd2 hsA.ext, hmA⟩ kR
          exact fin (hsA.trans hsB) (by simp only [Expr.mentionsFvar_forallE, ← hrA, hrB, Bool.false_or]) hmB zR
    case letE lt lv lb =>
      obtain ⟨et, ev, eb, rfl, hty, hval, hbd⟩ := denote_letE_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; dsimp only at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        dsimp only at h2
        obtain ⟨p1, sa, hc1, hn1⟩ := bindOk h2
        obtain ⟨b1, m1⟩ := p1
        obtain ⟨hsA, hrA, hmA⟩ := ih memo lt et s₀ sa (b1, m1) hok ⟨hty, hm⟩ hc1
        simp only at hrA
        cases b1 with
        | true =>
          obtain ⟨rr, sR, kR, zR⟩ := bindOk hn1
          obtain ⟨rfl, rfl⟩ := pureOk kR
          exact fin hsA (by simp only [Expr.mentionsFvar_letE, ← hrA, Bool.true_or]) hmA zR
        | false =>
          obtain ⟨p2, sb, hc2, hn2⟩ := bindOk hn1
          obtain ⟨b2, m2⟩ := p2
          obtain ⟨hsB, hrB, hmB⟩ := ih m1 lv ev sa sb (b2, m2) hsA.ok
            ⟨denote_ext hval hsA.ext, hmA⟩ hc2
          simp only at hrB
          cases b2 with
          | true =>
            obtain ⟨rr, sR, kR, zR⟩ := bindOk hn2
            obtain ⟨rfl, rfl⟩ := pureOk kR
            exact fin (hsA.trans hsB) (by simp only [Expr.mentionsFvar_letE, ← hrA, ← hrB,
              Bool.false_or, Bool.true_or]) hmB zR
          | false =>
            obtain ⟨rr, sR, kR, zR⟩ := bindOk hn2
            obtain ⟨hsC, hrC, hmC⟩ := ih m2 lb eb sb sR rr hsB.ok
              ⟨denote_ext (denote_ext hbd hsA.ext) hsB.ext, hmB⟩ kR
            exact fin ((hsA.trans hsB).trans hsC) (by simp only [Expr.mentionsFvar_letE, ← hrA,
              ← hrB, hrC, Bool.false_or]) hmC zR
    case proj pn pk psub =>
      obtain ⟨nm, es, rfl, _, hsub⟩ := denote_proj_inv hok.wf hw hd
      cases hlk : memo[h]? with
      | some r₀ => rw [hlk] at h2; dsimp only at h2; exact hit hlk h2
      | none =>
        rw [hlk] at h2
        dsimp only at h2
        obtain ⟨rr, sR, kR, zR⟩ := bindOk h2
        obtain ⟨hsA, hrA, hmA⟩ := ih memo psub es s₀ sR rr hok ⟨hsub, hm⟩ kR
        exact fin hsA (by simp only [Expr.mentionsFvar_proj, hrA]) hmA zR

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:379-381 Expr.mentionsFvarFast
The entry at an empty memo.

**CLOSED** (task #97-P3-Ind round 6). -/
theorem mentionsFvar_spec (q : Nat) (e : EIdx) (eP : Expr) :
    PSpec (fun st => denoteE st e = some eP)
      (Arena.mentionsFvar q e) (RV (Expr.mentionsFvar q eP)) := by
  intro s₀ s' r hok hd hrun
  simp only [Arena.mentionsFvar] at hrun
  obtain ⟨p, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨hs, hr, -⟩ := mentionsFvarGo_spec q ∅ Arena.coreWalkFuel e eP s₀ s1 p hok
    ⟨hd, fun k r hk => by simp at hk⟩ k1
  obtain ⟨rfl, rfl⟩ := pureOk z1
  exact ⟨hs, hr⟩

/-! ## The opened re-check -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:22-59 nativeOpenedOkF
One constructor's field kinds re-checked on the STORED (normalised) type, with
the binders opened at free variables.

`sorry`: `piBinders_spec`, `recFieldKind_spec`, `mentionsFvar_spec` and
`recFamOk_spec`, over the telescope. -/
theorem nativeOpenedOk_spec (fe₀ : IFEnv) (env₀ : Env) (T : NIdx)
    (TP : ConLeche.Name) (lps : List NIdx) (lpsP : List ConLeche.Name)
    (nP nIdx : Nat) (cty : EIdx) (ctyP : Expr) (nF : Nat)
    (ks : List Arena.RecFieldKind) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteE st cty = some ctyP ∧ denoteFEnv st fe₀ = some env₀)
      (Arena.nativeOpenedOk fe₀ T lps nP nIdx cty nF ks)
      (RV (ConLeche.nativeOpenedOk env₀ TP lpsP nP nIdx ctyP nF
        (ks.map kindOf))) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:435-445 nativeFieldsOk
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:61-69 nativeFieldsOkF
The same over the whole constructor list.

`sorry`: a list zip induction over `nativeOpenedOk_spec`. -/
theorem nativeFieldsOk_spec (fe₀ : IFEnv) (env₀ : Env) (T : NIdx)
    (TP : ConLeche.Name) (lps : List NIdx) (lpsP : List ConLeche.Name)
    (nP nIdx : Nat) (ctorsA : List (IConstantVal × Nat))
    (ctorsAP : List (ConstantVal × Nat))
    (kinds : List (List Arena.RecFieldKind)) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteCtors st ctorsA = some ctorsAP ∧ denoteFEnv st fe₀ = some env₀)
      (Arena.nativeFieldsOk fe₀ T lps nP nIdx ctorsA kinds)
      (RV (ConLeche.nativeFieldsOk env₀ TP lpsP nP nIdx ctorsAP
        (kinds.map (·.map kindOf)))) := by
  sorry

/-! ## The generated recursor and its rules -/

/-- con-leche: none — **a read-only walk is a core step**: a run that leaves
the store, the caches and the pins as it found them keeps `CheckOK`.  The
scoping guards (`allLevelParamsDefined`, `constsResolveFFast`,
`looseBVarsBoundedFast`, `hasFvarFast`) all answer in this frame. -/
theorem CoreStep.of_readonly {μ : CheckMode} {env : Env} {fe : IFEnv} {s s' : AState}
    (hok : CheckOK μ env fe s) (hst : s'.store = s.store) (hc : s'.caches = s.caches)
    (hp : s'.pins = s.pins) : CoreStep μ env fe s s' :=
  ⟨hok.mono ⟨by rw [hst]; exact hok.state.wf⟩ (by rw [hst]; exact Ext.refl _) hc hp,
    by rw [hst]; exact Ext.refl _, hp⟩

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:447-463 checkNativeRules
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:71-85 checkNativeRulesF
The `k` generated right-hand sides from `j` up, each generated and its scoping
checked.

**CLOSED** (task #97-P3-Ind round 7): a `Nat` recursion over
`structRecRhsR_spec` and the four scoping guards' run forms —
`allLevelParamsDefined_run` and `constsResolveFFast_run` (task #97-P3-Checker
round 9's layout move put them in `Bridge/Checker/Names.lean`, which is what
unblocked this), `looseBVarsBoundedFast_spec` and `hasFvarFast_spec`.

**One precondition it was missing** (round 7): `structRecRhsR_spec`'s own —
every recursive-field index a constructor record lists is below its field
count (`hcs`).  The caller builds `ctors` with `nativeCtors4`, whose kinds are
the classification's, so the fact is the classification's.  (The `hk`/`henv`
pair this statement carries is unused: the twin takes no mode and calls no
knot slot.) -/
theorem checkNativeRules_spec {μ : CheckMode} {env : Env} (feR : IFEnv)
    (envR : Env) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (rlps : List NIdx)
    (rlpsP : List ConLeche.Name) (T : NIdx) (TP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (elim : NIdx)
    (elimP : ConLeche.Name) (large : Bool) (nP nIdx : Nat) (tty : EIdx)
    (ttyP : Expr) (ctors : List (NIdx × Nat × EIdx × List Nat))
    (ctorsP : List (ConLeche.Name × Nat × Expr × List Nat)) (recC : NIdx)
    (recCP : ConLeche.Name) (rlvls : LsIdx) (rlvlsP : List Level) (k j : Nat)
    (hcs : ∀ c ∈ ctorsP, ∀ i ∈ c.2.2.2, i < c.2.1) :
    CSpec μ env feR
      (fun st => Frontend.denoteNList st.ns rlps = some rlpsP ∧
        denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteN st.ns elim = some elimP ∧ denoteE st tty = some ttyP ∧
        denoteCtors4 st ctors = some ctorsP ∧
        denoteN st.ns recC = some recCP ∧
        denoteLs st.lss rlvls = some rlvlsP ∧
        denoteFEnv st feR = some envR ∧ denoteFEnv st feR = some env)
      (Arena.checkNativeRules feR rlps T lps elim large nP nIdx tty ctors recC
        rlvls k j)
      (fun st r => ∃ rhssP,
        ConLeche.checkNativeRules (m := CheckM) envR rlpsP TP lpsP elimP large
          nP nIdx ttyP ctorsP recCP rlvlsP k j = .ok rhssP ∧
        Frontend.denoteEList st r = some rhssP) := by
  induction k generalizing j with
  | zero =>
    intro s₀ s' r hok _ hrun
    simp only [Arena.checkNativeRules] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨CoreStep.refl hok, [], rfl, rfl⟩
  | succ k ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hrl, hT, hlps, hel, hty, hcs4, hrc, hrv, hfeR, hfe⟩ := hpre
    obtain rfl : envR = env := Option.some.inj (hfeR.symm.trans hfe)
    simp only [Arena.checkNativeRules] at hrun
    obtain ⟨o, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, ho⟩ := structRecRhsR_spec T TP lps lpsP elim elimP large nP nIdx tty ttyP
      ctors ctorsP recC recCP rlvls rlvlsP j hcs s₀ s1 o hok.state
      ⟨hT, hlps, hel, hty, hcs4, hrc, hrv⟩ k1
    have c1 := p1.toCore hok
    cases o with
    | none =>
      obtain ⟨_, s2, k2, _⟩ := bindOk z1
      simp only [Arena.unwrapOr] at k2
      exact absurd k2 (fun h => failOk h)
    | some rhs =>
    obtain ⟨rhsP, hrhsP, hrhs⟩ := ho
    obtain ⟨rh, s2, k2, z2⟩ := bindOk z1
    simp only [Arena.unwrapOr] at k2
    obtain ⟨hrh, hs2⟩ := pureOk k2
    rw [hrh, hs2] at z2
    obtain ⟨b1, s3, k3, z3⟩ := bindOk z2
    obtain ⟨h31, h32, h33, hb1⟩ := allLevelParamsDefined_run c1.ok.state
      (denoteNListE_ext c1.ext _ _ hrl) hrhs k3
    have c3 := c1.trans (CoreStep.of_readonly c1.ok h31 h32 h33)
    have hrhs3 : denoteE s3.store rhs = some rhsP := by rw [h31]; exact hrhs
    obtain ⟨b2, s4, k4, z4⟩ := bindOk z3
    obtain ⟨h41, h42, h43, hb2⟩ := constsResolveFFast_run c3.ok hrhs3 k4
    have c4 := c3.trans (CoreStep.of_readonly c3.ok h41 h42 h43)
    have hrhs4 : denoteE s4.store rhs = some rhsP := by rw [h41]; exact hrhs3
    obtain ⟨b3, s5, k5, z5⟩ := bindOk z4
    obtain ⟨h51, h52, h53, hb3⟩ := AM.of_run (P := fun t => t = s4) rfl k5
      (ExprOps.looseBVarsBoundedFast_spec Arena.coreWalkFuel 0 s4 rhs c4.ok.state
        (by rw [hrhs4]; rfl))
    have c5 := c4.trans (CoreStep.of_readonly c4.ok h51 h52 h53)
    have hrhs5 : denoteE s5.store rhs = some rhsP := by rw [h51]; exact hrhs4
    obtain ⟨b4, s6, k6, z6⟩ := bindOk z5
    obtain ⟨h61, h62, h63, hb4⟩ := AM.of_run (P := fun t => t = s5) rfl k6
      (ExprOps.hasFvarFast_spec Arena.coreWalkFuel s5 rhs c5.ok.state (by rw [hrhs5]; rfl))
    have c6 := c5.trans (CoreStep.of_readonly c5.ok h61 h62 h63)
    have hrhs6 : denoteE s6.store rhs = some rhsP := by rw [h61]; exact hrhs5
    have hb3' : b3 = rhsP.looseBVarsBounded 0 := hb3 rhsP hrhs4
    have hb4' : b4 = rhsP.hasFvar := hb4 rhsP hrhs5
    subst hb1 hb2 hb3' hb4'
    obtain ⟨hg, z7⟩ := AM.dunless_ok AM.Never.fail_any z6
    replace z7 := AM.pure_bind_ok z7
    obtain ⟨rest, s7, k7, z8⟩ := bindOk z7
    have x06 := c6.ext
    obtain ⟨c7, restP, hrest, hrestd⟩ := ih (j + 1) s6 s7 rest c6.ok
      ⟨denoteNListE_ext x06 _ _ hrl, denoteN_ext hT x06, denoteNListE_ext x06 _ _ hlps,
        denoteN_ext hel x06, denote_ext hty x06, denoteCtors4_ext x06 _ _ hcs4,
        denoteN_ext hrc x06, denoteLs_ext hrv x06, denoteFEnv_ext x06 hfe,
        denoteFEnv_ext x06 hfe⟩ k7
    obtain ⟨rfl, rfl⟩ := pureOk z8
    refine ⟨c6.trans c7, rhsP :: restP, ?_, ?_⟩
    · simp only [ConLeche.checkNativeRules, hrhsP, ConLeche.unwrapOr, bind, Except.bind,
        pure, Except.pure]
      rw [if_pos hg]
      simp only [hrest]
    · simp only [Frontend.denoteEList, denote_ext hrhs6 c7.ext, hrestd]

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:465-502 checkNativeRec
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:87-115 checkNativeRecF
**The recursor generated, annotated and compared with the stream's.**

`sorry`: `structRecTyR_spec`, `checkNativeRules_spec`, `nativeCtors4_spec`
and `CoreSpec.knot`'s `annotate`/`defeq` slots. -/
theorem checkNativeRec_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (p : Arena.NativeParts)
    (q : ConLeche.NativeParts) (cvTa : IConstantVal) (cvTaP : ConstantVal)
    (ctorsA : List (IConstantVal × Nat)) (ctorsAP : List (ConstantVal × Nat)) :
    CSpec μ env fe
      (fun st => PartsRel st p q ∧ Frontend.denoteCV st cvTa = some cvTaP ∧
        denoteCtors st ctorsA = some ctorsAP ∧ denoteFEnv st fe = some env)
      (Arena.checkNativeRec μ fe p cvTa ctorsA)
      (fun st r => ∃ F cvRaP rhssP,
        ConLeche.checkNativeRec (ConLeche.fueledOps μ F) env q cvTaP ctorsAP
          = .ok (cvRaP, rhssP) ∧
        Frontend.denoteCV st r.1 = some cvRaP ∧
        Frontend.denoteEList st r.2 = some rhssP) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:504-519 checkNativeTable
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:117-126 checkNativeTableF
The projection table at a structure-like block, at the tagged tower's offset
`1`.

`sorry`: `structProjGuards_spec` and `checkStructProjTable_spec`
(`Bridge/Inductives/StructInstall.lean`); the non-structure branch is the
identity on the index, so `InstRel` is `Pushed.refl` and `ProjOut.refl`.

**This is where the projection table's `guards` clause is discharged** (task
#97-P3-Ind round 2).  `checkStructProjTable_spec` takes `guards.length = nF`
as a hypothesis because `guards` is an argument to the install and the install
cannot test it; the caller that BUILDS it is this one, and
`structProjGuards_spec` + `denoteLList_length` + `structProjGuards_length`
(all three in place, the middle two closed) are the three steps that give it
at `nF := cA.2`. -/
theorem checkNativeTable_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (p : Arena.NativeParts) (q : ConLeche.NativeParts)
    (ctorsA : List (IConstantVal × Nat)) (ctorsAP : List (ConstantVal × Nat))
    (sortss : List (List LIdx)) (sortssP : List (List Level)) :
    CSpec μ env fe
      (fun st => PartsRel st p q ∧ denoteCtors st ctorsA = some ctorsAP ∧
        denoteLLists st sortss = some sortssP ∧ denoteFEnv st fe = some env)
      (Arena.checkNativeTable p ctorsA sortss fe)
      (InstRel fe (fun env' =>
        @ConLeche.checkNativeTable CheckM _ _ q ctorsAP sortssP env
          = .ok env')) := by
  sorry

/-! ## The pass -/

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:521-537 NativePass
What one pass yields, denoting con-leche's record at `E = Env`. -/
structure PassRel (q : ConLeche.NativePass Env) (st : EStore)
    (r : Arena.NativePass) : Prop where
  env₁ : denoteFEnv st r.env₁ = some q.env₁
  cvTa : Frontend.denoteCV st r.cvTa = some q.cvTa
  p : PartsRel st r.p q.p
  ctorsA : denoteCtors st r.ctorsA = some q.ctorsA
  sortss : denoteLLists st r.sortss = some q.sortss

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:539-554 classifyFixKinds
`recCtorKindsAll` is the twin's spelling of con-leche's `ctorsA.mapM
(recCtorKinds …)` at the `Option` monad (the twin of `recCtorKinds` is monadic
in `AM` and optional in its result, so the `mapM` cannot be written).

`sorry`: a list induction over `recCtorKinds_spec`
(`Bridge/Inductives/NativeParts.lean`). -/
theorem recCtorKindsAll_spec (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nIdx : Nat)
    (cs : List (IConstantVal × Nat)) (csP : List (ConstantVal × Nat)) :
    PSpec (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteCtors st cs = some csP)
      (Arena.recCtorKindsAll T lps nP nIdx cs)
      (ROp RKss (csP.mapM (ConLeche.recCtorKinds TP lpsP nP nIdx))) := by
  induction cs generalizing csP with
  | nil =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨_, _, hcs⟩ := hpre
    simp only [denoteCtors, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.recCtorKindsAll] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, [], rfl, rfl⟩
  | cons c cs ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hT, hlps, hcs⟩ := hpre
    obtain ⟨cv, n⟩ := c
    simp only [denoteCtors] at hcs
    cases hcv : Frontend.denoteCV s₀.store cv with
    | none => rw [hcv] at hcs; simp at hcs
    | some cP =>
    cases hrest : denoteCtors s₀.store cs with
    | none => rw [hcv, hrest] at hcs; simp at hcs
    | some restP =>
    rw [hcv, hrest] at hcs
    obtain rfl := (Option.some.inj hcs).symm
    simp only [Arena.recCtorKindsAll] at hrun
    obtain ⟨o, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, ho⟩ := recCtorKinds_spec T TP lps lpsP nP nIdx (cv, n) (cP, n) s₀ s1 o hok
      ⟨hT, hlps, hcv, rfl⟩ k1
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := pureOk z1
      refine ⟨p1, ?_⟩
      have ho' : ConLeche.recCtorKinds TP lpsP nP nIdx (cP, n) = none := ho
      show _ = none
      simp only [List.mapM_cons, ho']
      rfl
    | some ks =>
    obtain ⟨ksP, hkP, hkr⟩ := ho
    obtain ⟨o2, s2, k2, z2⟩ := bindOk z1
    obtain ⟨p2, ho2⟩ := ih restP s1 s2 o2 p1.ok
      ⟨denoteN_ext hT p1.ext, denoteNListE_ext p1.ext _ _ hlps,
        denoteCtors_ext p1.ext _ _ hrest⟩ k2
    cases o2 with
    | none =>
      obtain ⟨rfl, rfl⟩ := pureOk z2
      refine ⟨p1.trans p2, ?_⟩
      have ho2' : restP.mapM (ConLeche.recCtorKinds TP lpsP nP nIdx) = none := ho2
      show _ = none
      simp only [List.mapM_cons, hkP, ho2']
      rfl
    | some rest =>
    obtain ⟨restKP, hrkP, hrkr⟩ := ho2
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨p1.trans p2, ksP :: restKP, ?_, ?_⟩
    · simp only [List.mapM_cons, hkP, hrkP]
      rfl
    · show (ks :: rest).map (·.map kindOf) = _
      simp only [List.map_cons]
      rw [show ks.map kindOf = ksP from hkr, show rest.map (·.map kindOf) = restKP from hrkr]

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:539-554 classifyFixKinds
The kinds classified on the stored constructors, with the two declines
(`negative`, `unsupported`) raised.

**CLOSED** (task #97-P3-Ind round 6). -/
theorem classifyFixKinds_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (T : NIdx) (TP : ConLeche.Name) (lps : List NIdx)
    (lpsP : List ConLeche.Name) (nP nIdx : Nat)
    (ctorsA : List (IConstantVal × Nat)) (ctorsAP : List (ConstantVal × Nat)) :
    CSpec μ env fe
      (fun st => denoteN st.ns T = some TP ∧
        Frontend.denoteNList st.ns lps = some lpsP ∧
        denoteCtors st ctorsA = some ctorsAP)
      (Arena.classifyFixKinds T lps nP nIdx ctorsA)
      (fun _ r => ∃ ks,
        ConLeche.classifyFixKinds (m := CheckM) TP lpsP nP nIdx ctorsAP
          = .ok ks ∧ r.map (·.map kindOf) = ks) := by
  intro s₀ s' r hok hpre hrun
  simp only [Arena.classifyFixKinds] at hrun
  obtain ⟨o, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, ho⟩ := recCtorKindsAll_spec T TP lps lpsP nP nIdx ctorsA ctorsAP s₀ s1 o
    hok.state hpre k1
  cases o with
  | none =>
    obtain ⟨_, s2, k2, _⟩ := bindOk z1
    simp only [Arena.unwrapOr] at k2
    exact absurd k2 (fun h => failOk h)
  | some kinds =>
  obtain ⟨kP, hkP, hkr⟩ := ho
  have hkr' : kinds.map (·.map kindOf) = kP := hkr
  obtain ⟨kk, s2, k2, z2⟩ := bindOk z1
  simp only [Arena.unwrapOr] at k2
  obtain ⟨hkk, rfl⟩ := pureOk k2
  subst kk
  have hneg : (kP.any fun ks => ks.any (· == .negative)) =
      (kinds.any fun ks => ks.any (· == .negative)) := by
    rw [← hkr']
    simp only [List.any_map, Function.comp_def]
    congr 1; funext ks; congr 1; funext k; cases k <;> rfl
  have huns : (kP.any fun ks => ks.any (· == .unsupported)) =
      (kinds.any fun ks => ks.any (· == .unsupported)) := by
    rw [← hkr']
    simp only [List.any_map, Function.comp_def]
    congr 1; funext ks; congr 1; funext k; cases k <;> rfl
  split at z2
  case isTrue _ =>
    obtain ⟨_, s3, k3, _⟩ := bindOk z2
    exact absurd k3 (fun h => failOk h)
  case isFalse hn =>
  obtain ⟨_, s3, k3, z3⟩ := bindOk z2
  obtain ⟨-, rfl⟩ := pureOk k3
  split at z3
  case isTrue _ =>
    obtain ⟨_, s4, k4, _⟩ := bindOk z3
    exact absurd k4 (fun h => failOk h)
  case isFalse hu =>
  obtain ⟨_, s4, k4, z4⟩ := bindOk z3
  obtain ⟨-, rfl⟩ := pureOk k4
  obtain ⟨rfl, rfl⟩ := pureOk z4
  refine ⟨p1.toCore hok, kP, ?_, hkr'⟩
  have hn' : (kP.any fun ks => ks.any (· == .negative)) = false := by
    rw [hneg]; simpa using hn
  have hu' : (kP.any fun ks => ks.any (· == .unsupported)) = false := by
    rw [huns]; simpa using hu
  simp only [ConLeche.classifyFixKinds, hkP, ConLeche.unwrapOr, pure, Except.pure, bind,
    Except.bind, hn', hu', Bool.false_eq_true, if_false]

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:556-574 checkNativePass
**One pass over the former and the constructors** at a given `is_rec` verdict,
with the flag that says whether the classification confirms it.

`sorry`: `checkSumInd_spec`, `complete_spec`, `flushCaches_spec`
(`Bridge/Specs.lean`, closed, with `CacheOK.of_empty`), `checkSumCtors_spec`,
`classifyFixKinds_spec`, `withKinds_spec`, `nativeCaps_spec` and
`nativeCapsAt_spec`. -/
theorem checkNativePass_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (p₀ : Arena.NativeParts)
    (q₀ : ConLeche.NativeParts) (isRec : Bool) :
    CSpec μ env fe
      (fun st => PartsRel st p₀ q₀ ∧ denoteFEnv st fe = some env)
      (Arena.checkNativePass μ fe p₀ isRec)
      (fun st r => ∃ F qP settled,
        ConLeche.checkNativePass (ConLeche.fueledOps μ F) env q₀ isRec
          = .ok (qP, settled) ∧
        PassRel qP st r.1 ∧ r.2 = settled ∧
        InstRel fe (fun e => e = qP.env₁) st r.1.env₁) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:576-611 checkNativeTail
**The install after the pass**: the elimination restriction, the index
binders' sorts, the kinds re-checked, the stream's rules against the generated
ones, the constructors consed, the recursor with its rules, and the projection
table.

`sorry`: `readLevel`'s spec (`Bridge/Specs.lean`, closed),
`openPisAtFvars`' spec, `checkStructFieldSortsI_spec`, `nativeFieldsOk_spec`,
`paramLevels_spec`, `nativeRulesOk_spec`, `consSumCtors_spec`,
`checkNativeRec_spec`, `sumRules_spec` and `checkNativeTable_spec` — the
longest single composition of the tier. -/
theorem checkNativeTail_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (r : Arena.NativePass)
    (qP : ConLeche.NativePass Env) :
    CSpec μ env fe
      (fun st => PassRel qP st r ∧ denoteFEnv st fe = some env)
      (Arena.checkNativeTail μ fe r)
      (InstRel fe (fun env' => ∃ F,
        ConLeche.checkNativeTail (ConLeche.fueledOps μ F) env qP = .ok env')) := by
  sorry

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:613-640 checkNative
**THE FIXPOINT ROUTE**, one of the two `checkIndDecl` dispatches to.  The
distinct names, the pass at the syntactic `is_rec`, and — where that reading
overshot — a second pass at the classification's verdict.

`sorry`: `nativeRawRec_spec`, `checkNativePass_spec` twice,
`nativeIsRec_spec` (closed), `checkNativeTail_spec`, and the `Nodup` guard,
which is `denoteN_inj` at the constructor names (`Bridge/Rel.lean`). -/
theorem checkNative_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (p₀ : Arena.NativeParts)
    (q₀ : ConLeche.NativeParts) :
    CSpec μ env fe
      (fun st => PartsRel st p₀ q₀ ∧ denoteFEnv st fe = some env)
      (Arena.checkNative μ fe p₀)
      (InstRel fe (fun env' => ∃ F,
        ConLeche.checkNative (ConLeche.fueledOps μ F) env q₀ = .ok env')) := by
  sorry

end ConRon.Bridge.Inductives

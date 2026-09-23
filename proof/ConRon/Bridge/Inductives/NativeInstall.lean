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
import ConLeche.Verify.Inductives.FixWF
import ConLeche.Verify.Inductives.FixInv
import ConLeche.Verify.Inductives.SumWF
import ConLeche.Verify.Inductives.SumInv

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

/-- con-leche: none — `anyM` over a denoting handle list, at the pure grade. -/
theorem anyM_E_pstep {f : EIdx → AM Bool} {F : Expr → Bool}
    (hf : ∀ (e : EIdx) (eP : Expr) (s₀ s' : AState) (x : Bool), StateOK s₀ →
      denoteE s₀.store e = some eP → f e s₀ = .ok (x, s') → PStep s₀ s' ∧ x = F eP) :
    ∀ (es : List EIdx) (esP : List Expr) (s₀ s' : AState) (x : Bool),
      StateOK s₀ → Frontend.denoteEList s₀.store es = some esP →
      es.anyM f s₀ = .ok (x, s') → PStep s₀ s' ∧ x = esP.any F := by
  intro es
  induction es with
  | nil =>
    intro esP s₀ s' x hok h hrun
    simp only [Frontend.denoteEList, Option.some.injEq] at h
    subst h
    simp only [List.anyM] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok, rfl⟩
  | cons e es ih =>
    intro esP s₀ s' x hok h hrun
    simp only [Frontend.denoteEList] at h
    cases he : denoteE s₀.store e with
    | none => rw [he] at h; simp at h
    | some eP =>
    cases hr : Frontend.denoteEList s₀.store es with
    | none => rw [he, hr] at h; simp at h
    | some rest =>
    rw [he, hr] at h
    obtain rfl := (Option.some.inj h).symm
    simp only [List.anyM] at hrun
    obtain ⟨c, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, hc⟩ := hf e eP s₀ s1 c hok he k1
    cases c with
    | true =>
      obtain ⟨rfl, rfl⟩ := pureOk z1
      exact ⟨p1, by simp only [List.any_cons, ← hc, Bool.true_or]⟩
    | false =>
      obtain ⟨p2, hx⟩ := ih rest s1 s' x p1.ok (denoteEList_ext p1.ext _ _ hr) z1
      exact ⟨p1.trans p2, by simp only [List.any_cons, ← hc, Bool.false_or, hx]⟩

/-- con-leche: none — a later field's mention test, the body of
`nativeOpenedOk`'s occurrence walk. -/
theorem mfFvarType_pstep (q : Nat) (e : EIdx) (eP : Expr) (s₀ s' : AState) (x : Bool)
    (hok : StateOK s₀) (he : denoteE s₀.store e = some eP)
    (hrun : (do Arena.mentionsFvar q (← fvarTypeD e) : AM Bool) s₀ = .ok (x, s')) :
    PStep s₀ s' ∧ x = eP.fvarTypeD.mentionsFvar q := by
  obtain ⟨t, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨hs1, ht⟩ := fvarTypeD_run hok he k1
  rw [hs1] at z1
  exact mentionsFvar_spec q t eP.fvarTypeD s₀ s' x hok ht z1

/-- con-leche: none — `getD` commutes with the kind map. -/
theorem getD_kindOf (ks : List Arena.RecFieldKind) (i : Nat) :
    (ks.map kindOf).getD i .ordinary = kindOf (ks.getD i .ordinary) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ks[i]? <;> rfl

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk (a
recursive or reflexive field's family test) — the family head, the parameter
prefix, the index count and resolution, and the two occurrence tests, over a
handle `bd` whose denotation is the field's target.  Shared by the
`.recursive` and `.reflexive` arms. -/
theorem famTail_run {env₀ : Env} {fe₀ : IFEnv} {nP nIdx i : Nat}
    {hd bd xrest : EIdx} {fvs xFvs : List EIdx} {hdP bdP xrestP : Expr}
    {fvsPP xFvsP : List Expr} {t₀ t' : AState} {b : Bool}
    (ck : ReadOK env₀ fe₀ t₀) (hhd : denoteE t₀.store hd = some hdP)
    (hbd : denoteE t₀.store bd = some bdP)
    (hfv : Frontend.denoteEList t₀.store fvs = some fvsPP)
    (hxf : Frontend.denoteEList t₀.store xFvs = some xFvsP)
    (hxr : denoteE t₀.store xrest = some xrestP)
    (hrun : (do
      let fn ← getAppFn coreWalkFuel bd
      let args ← getAppArgs coreWalkFuel bd
      if !(fn == hd && args.take nP == fvs && args.length == nP + nIdx) then
        pure false
      else do
        let idxOk ← (args.drop nP).allM fun e => constsResolveFFast fe₀ e
        if !idxOk then pure false else do
        let later ← (xFvs.drop (i + 1)).anyM fun y => do
          mentionsFvar (nP + i) (← fvarTypeD y)
        if later then pure false else
        pure !(← mentionsFvar (nP + i) xrest) : AM Bool) t₀ = .ok (b, t')) :
    PStep t₀ t' ∧ b = (bdP.getAppFn == hdP &&
      bdP.getAppArgs.take nP == fvsPP &&
      bdP.getAppArgs.length == nP + nIdx &&
      (bdP.getAppArgs.drop nP).all (fun e => e.constsResolve env₀) &&
      !(xFvsP.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
      !xrestP.mentionsFvar (nP + i)) := by
  have hwf := ck.state.wf
  obtain ⟨fn, t1, g1, y1⟩ := bindOk hrun
  obtain ⟨hs1, hfn⟩ := getAppFn_run ck.state hbd g1
  rw [hs1] at y1
  obtain ⟨args, t2, g2, y2⟩ := bindOk y1
  obtain ⟨hs2, hargs⟩ := getAppArgs_run ck.state hbd g2
  rw [hs2] at y2
  have e1 := beq_ehandle_eq hwf hfn hhd
  have e2 := beq_ehandleList_eq hwf (denoteEList_take hargs nP) hfv
  have e3 : args.length = bdP.getAppArgs.length :=
    (ExprOps.denoteEList_length _ _ hargs).symm
  rw [e1, e2, e3] at y2
  cases hc : (bdP.getAppFn == hdP && bdP.getAppArgs.take nP == fvsPP &&
      bdP.getAppArgs.length == nP + nIdx) with
  | false =>
    rw [hc] at y2
    simp only [Bool.not_false, if_true] at y2
    obtain ⟨rfl, rfl⟩ := pureOk y2
    exact ⟨PStep.refl ck.state, by simp⟩
  | true =>
  rw [hc] at y2
  simp only [Bool.not_true, Bool.false_eq_true, if_false] at y2
  rw [Bool.true_and]
  obtain ⟨io, t3, g3, y3⟩ := bindOk y2
  obtain ⟨q3, hio⟩ := allM_E_ck
    (fun e eP s₀ s' x hok he hrun => constsResolveFFast_pstep hok he hrun)
    (args.drop nP) _ t₀ t3 io ck (denoteEList_drop hargs nP) g3
  rw [← hio]
  cases io with
  | false =>
    simp only [Bool.not_false, if_true] at y3
    obtain ⟨rfl, rfl⟩ := pureOk y3
    exact ⟨q3, by simp⟩
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, if_false] at y3
  rw [Bool.true_and]
  obtain ⟨la, t4, g4, y4⟩ := bindOk y3
  obtain ⟨q4, hla⟩ := anyM_E_pstep
    (fun e eP s₀ s' x hok he hrun => mfFvarType_pstep (nP + i) e eP s₀ s' x hok he hrun)
    (xFvs.drop (i + 1)) _ t3 t4 la q3.ok (denoteEList_drop (denoteEList_ext q3.ext _ _ hxf) (i + 1))
    g4
  rw [← hla]
  cases la with
  | true =>
    simp only [if_true] at y4
    obtain ⟨rfl, rfl⟩ := pureOk y4
    exact ⟨q3.trans q4, by simp⟩
  | false =>
  simp only [Bool.false_eq_true, if_false] at y4
  obtain ⟨m, t5, g5, y5⟩ := bindOk y4
  obtain ⟨q5, hm⟩ := mentionsFvar_spec (nP + i) xrest xrestP t4 t5 m q4.ok
    (denote_ext hxr (q3.ext.trans q4.ext)) g5
  obtain ⟨rfl, rfl⟩ := pureOk y5
  refine ⟨q3.trans (q4.trans q5), ?_⟩
  have hm' : m = xrestP.mentionsFvar (nP + i) := hm
  rw [hm']
  simp

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:22-59 nativeOpenedOkF
One constructor's field kinds re-checked on the STORED (normalised) type, with
the binders opened at free variables.

**CLOSED** (task #97-P3-Ind round 7): the two openings (`openPisAtFvarsF_run`,
at con-leche's binder-at-a-time `openPisAtFvars`), `paramLevels_spec`,
`internConstE_run`, `getAppArgs_run`/`getAppFn_run`, and the resolution and
occurrence walks (`allM_E_ck` over `constsResolveFFast_run`, `anyM_E_pstep`
over `mentionsFvar_spec`); a reflexive field's own telescope through
`piBinders_spec` and a third opening.

**The precondition it was missing** (round 6's finding 2, repaired here once
task #97-P3-Checker round 9 moved `constsResolveFFast_run` within reach):
`constsResolveFFast` answers what the index `fe₀` answers, so its Theorem 1
needs `IFEnvOK env₀ fe₀`, which the statement's `denoteFEnv st fe₀ = some env₀`
does not give.  The precondition is now `ReadOK env₀ fe₀ s₀` (the only
consumer, `nativeFieldsOk` inside `checkNativeTail`, runs at that grade); the
conclusion — `PStep` and the verdict — is unchanged. -/
theorem nativeOpenedOk_spec (fe₀ : IFEnv) (env₀ : Env) (T : NIdx)
    (TP : ConLeche.Name) (lps : List NIdx) (lpsP : List ConLeche.Name)
    (nP nIdx : Nat) (cty : EIdx) (ctyP : Expr) (nF : Nat)
    (ks : List Arena.RecFieldKind) :
    ∀ (s₀ s' : AState) (r : Bool), ReadOK env₀ fe₀ s₀ →
      (denoteN s₀.store.ns T = some TP ∧
        Frontend.denoteNList s₀.store.ns lps = some lpsP ∧
        denoteE s₀.store cty = some ctyP ∧ denoteFEnv s₀.store fe₀ = some env₀) →
      Arena.nativeOpenedOk fe₀ T lps nP nIdx cty nF ks s₀ = .ok (r, s') →
      PStep s₀ s' ∧ r = ConLeche.nativeOpenedOk env₀ TP lpsP nP nIdx ctyP nF
        (ks.map kindOf) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hlps, hcty, -⟩ := hpre
  simp only [Arena.nativeOpenedOk] at hrun
  obtain ⟨o1, s1, k1, z1⟩ := bindOk hrun
  obtain ⟨p1, ho1⟩ := openPisAtFvarsF_run hok.state hcty k1
  cases o1 with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk z1
    refine ⟨p1, ?_⟩
    have hn : ConLeche.openPisAtFvars nP ctyP 0 = none := (Option.some.inj ho1).symm
    simp only [ConLeche.nativeOpenedOk, hn]
  | some q1 =>
  obtain ⟨fvs, crest⟩ := q1
  obtain ⟨fvsPP, crestP, hq1, hfvs, hcrest⟩ := denoteOpen_some_inv ho1
  dsimp only at z1
  obtain ⟨o2, s2, k2, z2⟩ := bindOk z1
  obtain ⟨p2, ho2⟩ := openPisAtFvarsF_run p1.ok hcrest k2
  cases o2 with
  | none =>
    obtain ⟨rfl, rfl⟩ := pureOk z2
    refine ⟨p1.trans p2, ?_⟩
    have hn : ConLeche.openPisAtFvars nF crestP nP = none := (Option.some.inj ho2).symm
    simp only [ConLeche.nativeOpenedOk, hq1, hn]
  | some q2 =>
  obtain ⟨xFvs, xrest⟩ := q2
  obtain ⟨xFvsP, xrestP, hq2, hxfvs, hxrest⟩ := denoteOpen_some_inv ho2
  dsimp only at z2
  obtain ⟨us, s3, k3, z3⟩ := bindOk z2
  obtain ⟨p3, hus⟩ := paramLevels_spec lps lpsP s2 s3 us p2.ok
    (denoteNListE_ext (p1.ext.trans p2.ext) _ _ hlps) k3
  obtain ⟨hd, s4, k4, z4⟩ := bindOk z3
  obtain ⟨p4, hhd⟩ := internConstE_run p3.ok
    (denoteN_ext hT (p1.ext.trans (p2.ext.trans p3.ext))) hus k4
  obtain ⟨xargs, s5, k5, z5⟩ := bindOk z4
  obtain ⟨hs5, hxargs⟩ := getAppArgs_run p4.ok (denote_ext hxrest (p3.ext.trans p4.ext)) k5
  rw [hs5] at z5
  have p04 : PStep s₀ s4 := p1.trans (p2.trans (p3.trans p4))
  have ck4 := (hok.mono p04.ok p04.ext p04.pins)
  obtain ⟨ro, s6, k6, z6⟩ := bindOk z5
  obtain ⟨p6, hro⟩ := allM_E_ck
    (fun e eP s₀ s' x hok he hrun => constsResolveFFast_pstep hok he hrun)
    (xargs.drop nP) _ s4 s6 ro ck4 (denoteEList_drop hxargs nP) k6
  simp only [ConLeche.nativeOpenedOk, hq1, hq2]
  cases ro with
  | false =>
    simp only [Bool.not_false, if_true] at z6
    obtain ⟨rfl, rfl⟩ := pureOk z6
    refine ⟨p04.trans p6, ?_⟩
    rw [← hro, Bool.false_and]
  | true =>
  simp only [Bool.not_true, Bool.false_eq_true, if_false] at z6
  rw [← hro, Bool.true_and]
  have x46 : Ext s4.store s6.store := p6.ext
  have x16 : Ext s1.store s6.store := p2.ext.trans (p3.ext.trans (p4.ext.trans x46))
  have x26 : Ext s2.store s6.store := p3.ext.trans (p4.ext.trans x46)
  have hall := allM_ck (env := env₀) (fe := fe₀)
    (g := fun i =>
      match xFvsP[i]?, (ks.map kindOf).getD i .ordinary with
      | some x, .ordinary => x.fvarTypeD.constsResolve env₀
      | some x, .recursive =>
        x.fvarTypeD.getAppFn == Expr.const TP (lpsP.map .param) &&
        x.fvarTypeD.getAppArgs.take nP == fvsPP &&
        x.fvarTypeD.getAppArgs.length == nP + nIdx &&
        (x.fvarTypeD.getAppArgs.drop nP).all (fun e => e.constsResolve env₀) &&
        !(xFvsP.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
        !xrestP.mentionsFvar (nP + i)
      | some x, .reflexive =>
        match ConLeche.openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) with
        | some (afvs, body) =>
          afvs.length != 0 &&
          afvs.all (fun a => a.fvarTypeD.constsResolve env₀) &&
          body.getAppFn == Expr.const TP (lpsP.map .param) &&
          body.getAppArgs.take nP == fvsPP &&
          body.getAppArgs.length == nP + nIdx &&
          (body.getAppArgs.drop nP).all (fun e => e.constsResolve env₀) &&
          !(xFvsP.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
          !xrestP.mentionsFvar (nP + i)
        | none => false
      | _, _ => false)
    (fun _ st => Frontend.denoteEList st xFvs = some xFvsP ∧
      Frontend.denoteEList st fvs = some fvsPP ∧
      denoteE st hd = some (.const TP (lpsP.map .param)) ∧ denoteE st xrest = some xrestP)
    (fun hx h => ⟨denoteEList_ext hx _ _ h.1, denoteEList_ext hx _ _ h.2.1,
      denote_ext h.2.2.1 hx, denote_ext h.2.2.2 hx⟩)
    (by
      intro i t₀ t' b ck hP hbody
      obtain ⟨hxf, hfv, hhd', hxr⟩ := hP
      rw [getD_kindOf]
      cases hx : xFvs[i]? with
      | none =>
        rw [hx] at hbody
        obtain ⟨rfl, rfl⟩ := pureOk hbody
        refine ⟨PStep.refl ck.state, ?_⟩
        have hl := ExprOps.denoteEList_length _ _ hxf
        have : xFvsP[i]? = none := by
          rw [List.getElem?_eq_none_iff] at hx ⊢; omega
        simp [this]
      | some x =>
      obtain ⟨xP, hxP, hxd⟩ := ExprOps.denoteEList_getElem? _ _ hxf i x hx
      rw [hx] at hbody
      rw [hxP]
      cases hk : ks.getD i .ordinary
      case ordinary =>
        rw [hk] at hbody
        exact crFvarType_pstep x xP t₀ t' b ck hxd hbody
      case recursive =>
        rw [hk] at hbody
        obtain ⟨xt, t1, g1, y1⟩ := bindOk hbody
        obtain ⟨hs1, hxt⟩ := fvarTypeD_run ck.state hxd g1
        rw [hs1] at y1
        exact famTail_run ck hhd' hxt hfv hxf hxr y1
      case reflexive =>
        rw [hk] at hbody
        obtain ⟨xt, t1, g1, y1⟩ := bindOk hbody
        obtain ⟨hs1, hxt⟩ := fvarTypeD_run ck.state hxd g1
        rw [hs1] at y1
        obtain ⟨pb, t2, g2, y2⟩ := bindOk y1
        obtain ⟨q2, hpb1, -⟩ := piBinders_spec Arena.coreWalkFuel xt xP.fvarTypeD t₀ t2 pb
          ck.state hxt g2
        have hlen : pb.1.length = (xP.fvarTypeD.piBinders).1.length := denoteBinders_length hpb1
        have ck2 := (ck.mono q2.ok q2.ext q2.pins)
        obtain ⟨o, t3, g3, y3⟩ := bindOk y2
        obtain ⟨q3, ho⟩ := openPisAtFvarsF_run q2.ok (denote_ext hxt q2.ext) g3
        rw [hlen] at ho
        cases o with
        | none =>
          obtain ⟨rfl, rfl⟩ := pureOk y3
          refine ⟨q2.trans q3, ?_⟩
          have hn : ConLeche.openPisAtFvars (xP.fvarTypeD.piBinders).1.length xP.fvarTypeD
              (nP + i) = none := (Option.some.inj ho).symm
          simp only [kindOf, hn]
        | some q =>
        obtain ⟨afvs, body⟩ := q
        obtain ⟨afvsP, bodyP, hq, hafvs, hbody'⟩ := denoteOpen_some_inv ho
        simp only [kindOf, hq]
        dsimp only at y3
        have hla : afvs.length = afvsP.length := (ExprOps.denoteEList_length _ _ hafvs).symm
        rw [hla] at y3
        have ck3 := (ck2.mono q3.ok q3.ext q3.pins)
        cases hl0 : (afvsP.length == 0) with
        | true =>
          rw [hl0] at y3
          simp only [if_true] at y3
          obtain ⟨rfl, rfl⟩ := pureOk y3
          refine ⟨q2.trans q3, ?_⟩
          have : (afvsP.length != 0) = false := by simp [bne, hl0]
          rw [this]; simp
        | false =>
        rw [hl0] at y3
        simp only [Bool.false_eq_true, if_false] at y3
        have hne : (afvsP.length != 0) = true := by simp [bne, hl0]
        rw [hne, Bool.true_and]
        obtain ⟨dk, t4, g4, y4⟩ := bindOk y3
        obtain ⟨q4, hdk⟩ := allM_E_ck
          (fun e eP s₀ s' x hok he hrun => crFvarType_pstep e eP s₀ s' x hok he hrun)
          afvs afvsP t3 t4 dk ck3 hafvs g4
        rw [← hdk]
        cases dk with
        | false =>
          simp only [Bool.not_false, if_true] at y4
          obtain ⟨rfl, rfl⟩ := pureOk y4
          exact ⟨q2.trans (q3.trans q4), by simp⟩
        | true =>
        simp only [Bool.not_true, Bool.false_eq_true, if_false] at y4
        rw [Bool.true_and]
        have x04 : Ext t₀.store t4.store := q2.ext.trans (q3.ext.trans q4.ext)
        obtain ⟨q5, hr5⟩ := famTail_run (ck3.mono q4.ok q4.ext q4.pins) (denote_ext hhd' x04)
          (denote_ext hbody' q4.ext) (denoteEList_ext x04 _ _ hfv)
          (denoteEList_ext x04 _ _ hxf) (denote_ext hxr x04) y4
        exact ⟨q2.trans (q3.trans (q4.trans q5)), hr5⟩
      all_goals
        (rw [hk] at hbody
         obtain ⟨rfl, rfl⟩ := pureOk hbody
         exact ⟨PStep.refl ck.state, rfl⟩))
    (List.range nF) s6 s' r (ck4.mono p6.ok p6.ext p6.pins)
    (fun _ _ => ⟨denoteEList_ext x26 _ _ hxfvs, denoteEList_ext x16 _ _ hfvs,
      denote_ext hhd x46, denote_ext hxrest x26⟩) z6
  exact ⟨p04.trans (p6.trans hall.1), hall.2⟩

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:435-445 nativeFieldsOk
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:61-69 nativeFieldsOkF
The same over the whole constructor list.

**CLOSED** (task #97-P3-Ind round 7): `allM_ck` over the constructor indices,
`denoteCtors_getElem?` for the pairing, and `nativeOpenedOk_spec` at each.
**The same precondition repair** as `nativeOpenedOk_spec`: `CheckOK μ env₀ fe₀`
in place of `StateOK`; the conclusion is unchanged. -/
theorem nativeFieldsOk_spec (fe₀ : IFEnv) (env₀ : Env) (T : NIdx)
    (TP : ConLeche.Name) (lps : List NIdx) (lpsP : List ConLeche.Name)
    (nP nIdx : Nat) (ctorsA : List (IConstantVal × Nat))
    (ctorsAP : List (ConstantVal × Nat))
    (kinds : List (List Arena.RecFieldKind)) :
    ∀ (s₀ s' : AState) (r : Bool), ReadOK env₀ fe₀ s₀ →
      (denoteN s₀.store.ns T = some TP ∧
        Frontend.denoteNList s₀.store.ns lps = some lpsP ∧
        denoteCtors s₀.store ctorsA = some ctorsAP ∧ denoteFEnv s₀.store fe₀ = some env₀) →
      Arena.nativeFieldsOk fe₀ T lps nP nIdx ctorsA kinds s₀ = .ok (r, s') →
      PStep s₀ s' ∧ r = ConLeche.nativeFieldsOk env₀ TP lpsP nP nIdx ctorsAP
        (kinds.map (·.map kindOf)) := by
  intro s₀ s' r hok hpre hrun
  obtain ⟨hT, hlps, hcs, hfe⟩ := hpre
  have hlen : ctorsA.length = ctorsAP.length := denoteCtors_length _ _ hcs
  simp only [Arena.nativeFieldsOk] at hrun
  simp only [ConLeche.nativeFieldsOk, List.length_map]
  rw [hlen] at hrun
  cases hl : (ctorsAP.length == kinds.length) with
  | false =>
    rw [hl] at hrun
    simp only [Bool.not_false, if_true] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok.state, by simp⟩
  | true =>
  rw [hl] at hrun
  simp only [Bool.not_true, Bool.false_eq_true, if_false] at hrun
  rw [Bool.true_and]
  exact allM_ck (env := env₀) (fe := fe₀)
    (g := fun j =>
      match ctorsAP[j]?, (kinds.map (·.map kindOf))[j]? with
      | some cA, some ks =>
        ks.length == cA.2 && ConLeche.nativeOpenedOk env₀ TP lpsP nP nIdx cA.1.type cA.2 ks
      | _, _ => false)
    (fun _ st => denoteN st.ns T = some TP ∧
      Frontend.denoteNList st.ns lps = some lpsP ∧
      denoteCtors st ctorsA = some ctorsAP ∧ denoteFEnv st fe₀ = some env₀)
    (fun hx h => ⟨denoteN_ext h.1 hx, denoteNListE_ext hx _ _ h.2.1,
      denoteCtors_ext hx _ _ h.2.2.1, denoteFEnv_ext hx h.2.2.2⟩)
    (by
      intro j t₀ t' b ck hP hbody
      obtain ⟨hT', hlps', hcs', hfe'⟩ := hP
      obtain ⟨hA, hB⟩ := denoteCtors_getElem? hcs' j
      simp only [List.getElem?_map]
      cases hc : ctorsA[j]? with
      | none =>
        rw [hc] at hbody
        obtain ⟨rfl, rfl⟩ := pureOk hbody
        exact ⟨PStep.refl ck.state, by simp [hB hc]⟩
      | some cA =>
      obtain ⟨cv, a⟩ := cA
      obtain ⟨cP, hcP, hcv⟩ := hA cv a hc
      rw [hc] at hbody
      rw [hcP]
      cases hk : kinds[j]? with
      | none =>
        rw [hk] at hbody
        obtain ⟨rfl, rfl⟩ := pureOk hbody
        exact ⟨PStep.refl ck.state, by simp⟩
      | some ks =>
      rw [hk] at hbody
      dsimp only at hbody
      simp only [Option.map_some, List.length_map]
      cases hkl : (ks.length == a) with
      | false =>
        rw [hkl] at hbody
        simp only [Bool.not_false, if_true] at hbody
        obtain ⟨rfl, rfl⟩ := pureOk hbody
        exact ⟨PStep.refl ck.state, by simp⟩
      | true =>
      rw [hkl] at hbody
      simp only [Bool.not_true, Bool.false_eq_true, if_false] at hbody
      rw [Bool.true_and]
      exact nativeOpenedOk_spec fe₀ env₀ T TP lps lpsP nP nIdx cv.type cP.type a ks
        t₀ t' b ck ⟨hT', hlps', denoteCV_type hcv, hfe'⟩ hbody)
    (List.range ctorsAP.length) s₀ s' r hok (fun _ _ => ⟨hT, hlps, hcs, hfe⟩) hrun

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
theorem checkNativeRules_run (feR : IFEnv)
    (envR : Env) (rlps : List NIdx)
    (rlpsP : List ConLeche.Name) (T : NIdx) (TP : ConLeche.Name)
    (lps : List NIdx) (lpsP : List ConLeche.Name) (elim : NIdx)
    (elimP : ConLeche.Name) (large : Bool) (nP nIdx : Nat) (tty : EIdx)
    (ttyP : Expr) (ctors : List (NIdx × Nat × EIdx × List Nat))
    (ctorsP : List (ConLeche.Name × Nat × Expr × List Nat)) (recC : NIdx)
    (recCP : ConLeche.Name) (rlvls : LsIdx) (rlvlsP : List Level) (k j : Nat)
    (hcs : ∀ c ∈ ctorsP, ∀ i ∈ c.2.2.2, i < c.2.1) :
    ∀ (s₀ s' : AState) (r : List EIdx), ReadOK envR feR s₀ →
      (Frontend.denoteNList s₀.store.ns rlps = some rlpsP ∧
        denoteN s₀.store.ns T = some TP ∧
        Frontend.denoteNList s₀.store.ns lps = some lpsP ∧
        denoteN s₀.store.ns elim = some elimP ∧ denoteE s₀.store tty = some ttyP ∧
        denoteCtors4 s₀.store ctors = some ctorsP ∧
        denoteN s₀.store.ns recC = some recCP ∧
        denoteLs s₀.store.lss rlvls = some rlvlsP ∧
        denoteFEnv s₀.store feR = some envR) →
      Arena.checkNativeRules feR rlps T lps elim large nP nIdx tty ctors recC rlvls k j s₀
        = .ok (r, s') →
      PStep s₀ s' ∧ ∃ rhssP,
        ConLeche.checkNativeRules (m := CheckM) envR rlpsP TP lpsP elimP large
          nP nIdx ttyP ctorsP recCP rlvlsP k j = .ok rhssP ∧
        Frontend.denoteEList s'.store r = some rhssP := by
  induction k generalizing j with
  | zero =>
    intro s₀ s' r hok _ hrun
    simp only [Arena.checkNativeRules] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact ⟨PStep.refl hok.state, [], rfl, rfl⟩
  | succ k ih =>
    intro s₀ s' r hok hpre hrun
    obtain ⟨hrl, hT, hlps, hel, hty, hcs4, hrc, hrv, hfeR⟩ := hpre
    simp only [Arena.checkNativeRules] at hrun
    obtain ⟨o, s1, k1, z1⟩ := bindOk hrun
    obtain ⟨p1, ho⟩ := structRecRhsR_spec T TP lps lpsP elim elimP large nP nIdx tty ttyP
      ctors ctorsP recC recCP rlvls rlvlsP j hcs s₀ s1 o hok.state
      ⟨hT, hlps, hel, hty, hcs4, hrc, hrv⟩ k1
    have c1 := p1
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
    obtain ⟨h31, h32, h33, hb1⟩ := allLevelParamsDefined_run c1.ok
      (denoteNListE_ext c1.ext _ _ hrl) hrhs k3
    have c3 := c1.trans (PStep.of_caches ⟨by rw [h31]; exact c1.ok.wf⟩ (by rw [h31]; exact Ext.refl _) (by rw [h31]; exact BMExt.refl _) h32 h33)
    have hrhs3 : denoteE s3.store rhs = some rhsP := by rw [h31]; exact hrhs
    obtain ⟨b2, s4, k4, z4⟩ := bindOk z3
    obtain ⟨h41, h42, h43, hb2⟩ := constsResolveFFast_runR (hok.mono c3.ok c3.ext c3.pins) hrhs3 k4
    have c4 := c3.trans (PStep.of_caches ⟨by rw [h41]; exact c3.ok.wf⟩ (by rw [h41]; exact Ext.refl _) (by rw [h41]; exact BMExt.refl _) h42 h43)
    have hrhs4 : denoteE s4.store rhs = some rhsP := by rw [h41]; exact hrhs3
    obtain ⟨b3, s5, k5, z5⟩ := bindOk z4
    obtain ⟨h51, h52, h53, hb3⟩ := AM.of_run (P := fun t => t = s4) rfl k5
      (ExprOps.looseBVarsBoundedFast_spec Arena.coreWalkFuel 0 s4 rhs c4.ok
        (by rw [hrhs4]; rfl))
    have c5 := c4.trans (PStep.of_caches ⟨by rw [h51]; exact c4.ok.wf⟩ (by rw [h51]; exact Ext.refl _) (by rw [h51]; exact BMExt.refl _) h52 h53)
    have hrhs5 : denoteE s5.store rhs = some rhsP := by rw [h51]; exact hrhs4
    obtain ⟨b4, s6, k6, z6⟩ := bindOk z5
    obtain ⟨h61, h62, h63, hb4⟩ := AM.of_run (P := fun t => t = s5) rfl k6
      (ExprOps.hasFvarFast_spec Arena.coreWalkFuel s5 rhs c5.ok (by rw [hrhs5]; rfl))
    have c6 := c5.trans (PStep.of_caches ⟨by rw [h61]; exact c5.ok.wf⟩ (by rw [h61]; exact Ext.refl _) (by rw [h61]; exact BMExt.refl _) h62 h63)
    have hrhs6 : denoteE s6.store rhs = some rhsP := by rw [h61]; exact hrhs5
    have hb3' : b3 = rhsP.looseBVarsBounded 0 := hb3 rhsP hrhs4
    have hb4' : b4 = rhsP.hasFvar := hb4 rhsP hrhs5
    subst hb1 hb2 hb3' hb4'
    obtain ⟨hg, z7⟩ := AM.dunless_ok AM.Never.fail_any z6
    replace z7 := AM.pure_bind_ok z7
    obtain ⟨rest, s7, k7, z8⟩ := bindOk z7
    have x06 := c6.ext
    obtain ⟨c7, restP, hrest, hrestd⟩ := ih (j + 1) s6 s7 rest (hok.mono c6.ok c6.ext c6.pins)
      ⟨denoteNListE_ext x06 _ _ hrl, denoteN_ext hT x06, denoteNListE_ext x06 _ _ hlps,
        denoteN_ext hel x06, denote_ext hty x06, denoteCtors4_ext x06 _ _ hcs4,
        denoteN_ext hrc x06, denoteLs_ext hrv x06, denoteFEnv_ext x06 hfeR⟩ k7
    obtain ⟨rfl, rfl⟩ := pureOk z8
    refine ⟨c6.trans c7, rhsP :: restP, ?_, ?_⟩
    · simp only [ConLeche.checkNativeRules, hrhsP, ConLeche.unwrapOr, bind, Except.bind,
        pure, Except.pure]
      rw [if_pos hg]
      simp only [hrest]
    · simp only [Frontend.denoteEList, denote_ext hrhs6 c7.ext, hrestd]

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:447-463 checkNativeRules
The same at the core grade, read off `checkNativeRules_run`. -/
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
  intro s₀ s' r hok hpre hrun
  obtain ⟨hrl, hT, hlps, hel, hty, hcs4, hrc, hrv, hfeR, hfe⟩ := hpre
  obtain rfl : envR = env := Option.some.inj (hfeR.symm.trans hfe)
  obtain ⟨p, hr⟩ := checkNativeRules_run feR envR rlps rlpsP T TP lps lpsP elim elimP large
    nP nIdx tty ttyP ctors ctorsP recC recCP rlvls rlvlsP k j hcs s₀ s' r hok.toR
    ⟨hrl, hT, hlps, hel, hty, hcs4, hrc, hrv, hfeR⟩ hrun
  exact ⟨p.toCore hok, hr⟩

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:134-145 recCtorKinds
— **one kind per field**. -/
theorem recCtorKinds_length {T : ConLeche.Name} {lps : List ConLeche.Name} {nP nIdx : Nat}
    {c : ConstantVal × Nat} {ks : List ConLeche.RecFieldKind}
    (h : ConLeche.recCtorKinds T lps nP nIdx c = some ks) : ks.length = c.2 := by
  unfold ConLeche.recCtorKinds at h
  split at h
  · split at h <;> (obtain rfl := Option.some.inj h; simp)
  · exact nomatch h

/-- con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:173-175 recIdxOf —
a recursive-field index is a field index. -/
theorem recIdxOf_lt {ks : List ConLeche.RecFieldKind} {i : Nat}
    (h : i ∈ ConLeche.recIdxOf ks) : i < ks.length := by
  unfold ConLeche.recIdxOf at h
  exact List.mem_range.mp (List.mem_filter.mp h).1

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:539-554 classifyFixKinds
— **the classified kinds fit the constructors**: every recursive-field index
`nativeCtors4` lists is below its constructor's field count, which is the
precondition `structRecTyR_spec`/`structRecRhsR_spec` take (`hcs`). -/
theorem classifyFixKinds_hcs {T : ConLeche.Name} {lps : List ConLeche.Name} {nP nIdx : Nat}
    {ctorsA : List (ConstantVal × Nat)} {kinds : List (List ConLeche.RecFieldKind)}
    (h : ConLeche.classifyFixKinds (m := CheckM) T lps nP nIdx ctorsA = .ok kinds) :
    ∀ c ∈ ConLeche.nativeCtors4 ctorsA kinds, ∀ i ∈ c.2.2.2, i < c.2.1 := by
  have hm : ctorsA.mapM (ConLeche.recCtorKinds T lps nP nIdx) = some kinds := by
    unfold ConLeche.classifyFixKinds at h
    cases hk : ctorsA.mapM (ConLeche.recCtorKinds T lps nP nIdx) with
    | none =>
      rw [hk] at h
      simp [ConLeche.unwrapOr, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    | some ks =>
      rw [hk] at h
      simp only [ConLeche.unwrapOr, pure, Except.pure, bind, Except.bind] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · obtain rfl := Except.ok.inj h
          rfl
  have key : ∀ {cs : List (ConstantVal × Nat)} {ks : List (List ConLeche.RecFieldKind)},
      cs.mapM (ConLeche.recCtorKinds T lps nP nIdx) = some ks →
      ∀ c ∈ ConLeche.nativeCtors4 cs ks, ∀ i ∈ c.2.2.2, i < c.2.1 := by
    intro cs
    induction cs with
    | nil =>
      intro ks h c hc
      simp [ConLeche.nativeCtors4] at hc
    | cons a as ih =>
      intro ks h c hc
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨k, hk, rest, hrest, hks⟩ := h
      simp only [Option.pure_def, Option.some.injEq] at hks
      subst hks
      simp only [ConLeche.nativeCtors4, List.zipWith_cons_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · intro i hi
        have := recIdxOf_lt hi
        rw [recCtorKinds_length hk] at this
        exact this
      · exact ih hrest c hc
  exact key hm

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:465-502 checkNativeRec
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:87-115 checkNativeRecF
**The recursor generated, annotated and compared with the stream's.**

`sorry`: `structRecTyR_spec`, `checkNativeRules_spec`, `nativeCtors4_spec`
and `CoreSpec.knot`'s `annotate`/`defeq` slots. -/
theorem checkNativeRec_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hμ : μ.verifiedChecks = true)
    (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env) (hcoh : IFEnvCoh fe)
    (p : Arena.NativeParts)
    (q : ConLeche.NativeParts) (cvTa : IConstantVal) (cvTaP : ConstantVal)
    (ctorsA : List (IConstantVal × Nat)) (ctorsAP : List (ConstantVal × Nat))
    (hkcs : ∀ c ∈ ConLeche.nativeCtors4 ctorsAP q.kinds, ∀ i ∈ c.2.2.2, i < c.2.1) :
    CSpec μ env fe
      (fun st => PartsRel st p q ∧ Frontend.denoteCV st cvTa = some cvTaP ∧
        denoteCtors st ctorsA = some ctorsAP ∧ denoteFEnv st fe = some env)
      (Arena.checkNativeRec μ fe p cvTa ctorsA)
      (fun st r => ∃ F cvRaP rhssP,
        ConLeche.checkNativeRec (ConLeche.fueledOps μ F) env q cvTaP ctorsAP
          = .ok (cvRaP, rhssP) ∧
        Frontend.denoteCV st r.1 = some cvRaP ∧
        Frontend.denoteEList st r.2 = some rhssP) := by
  intro s₀ s' r hck hpre hrun
  obtain ⟨hp, hcvTa, hcs, hfe⟩ := hpre
  have hsh := hp.shape
  have hknot := hk.knot env fe henv
  have hsort := hk.sort env fe henv
  have hnever : ∀ {α β : Type} {e : Arena.CheckError} {g : α → AM β},
      AM.Never ((Arena.fail e : AM α) >>= g) := fun {_ _ _ _} => AM.Never.fail_any
  simp only [Arena.checkNativeRec] at hrun
  -- the recursor pin
  obtain ⟨recName, s₁, k1, z1⟩ := bindOk hrun
  have hT := denoteCV_name hsh.cvT
  obtain ⟨p1, hrn⟩ := internNNode_run hck.state
    (by intro c hc
        simp only [NNodeView.children, List.mem_singleton] at hc
        subst hc
        exact nview_isSome_of_denote hT) k1
  simp only [denoteNView, denoteN_ext hT p1.ext, Option.map_some] at hrn
  have c1 := p1.toCore hck
  obtain ⟨hg1, z2⟩ := AM.dunless_ok hnever z1
  replace z2 := AM.pure_bind_ok z2
  rw [beq_handle_eq c1.ok.state.wf (denoteN_ext (denoteCV_name hsh.cvR) p1.ext) hrn] at hg1
  obtain ⟨hg2, z3⟩ := AM.dunless_ok hnever z2
  replace z3 := AM.pure_bind_ok z3
  rw [nativeRecLpsOk_spec s₁.store c1.ok.state.wf _ _ (hsh.ext p1.ext)] at hg2
  obtain ⟨hg3, z4⟩ := AM.dunless_ok hnever z3
  replace z4 := AM.pure_bind_ok z4
  rw [hp.recPinned] at hg3
  -- the stream's recursor, checked
  obtain ⟨cvRi, s₂, k2, z5⟩ := bindOk z4
  obtain ⟨c2, cRiP, F₁, hcRi, hF₁⟩ := checkConstantVal_bridge hμ hk c1.ok henv
    (denoteCV_ext hsh.cvR p1.ext) k2
  have c12 := c1.trans c2
  have x02 := c12.ext
  -- the generated type
  have hc4 := nativeCtors4_spec ctorsA ctorsAP p.kinds (denoteCtors_ext x02 _ _ hcs)
  rw [hp.kinds] at hc4
  obtain ⟨o, s₃, k3, z6⟩ := bindOk z5
  obtain ⟨p3, ho⟩ := structRecTyR_spec p.cvT.name q.cvT.name p.cvT.levelParams
    q.cvT.levelParams p.elim q.elim p.large p.nP p.nIdx cvTa.type cvTaP.type
    (Arena.nativeCtors4 ctorsA p.kinds) (ConLeche.nativeCtors4 ctorsAP q.kinds) hkcs s₂ s₃ o
    c12.ok.state ⟨denoteN_ext hT x02, denoteNListE_ext x02 _ _ (denoteCV_lps hsh.cvT),
      denoteN_ext hsh.elim x02, denote_ext (denoteCV_type hcvTa) x02, hc4⟩ k3
  obtain ⟨recTy, s₄, k4, z7⟩ := bindOk z6
  cases o with
  | none => simp only [Arena.unwrapOr] at k4; exact absurd k4 (fun h => failOk h)
  | some o' =>
  simp only [Arena.unwrapOr] at k4
  obtain ⟨hr4, hs4⟩ := pureOk k4
  subst hr4
  rw [hs4] at z7
  obtain ⟨recTyP, hrecP, hrec⟩ := ho
  rw [hsh.nP, hsh.nIdx, hsh.large] at hrecP
  have c3 := c12.trans (p3.toCore c12.ok)
  -- its four scoping guards
  obtain ⟨b1, s₅, k5, z8⟩ := bindOk z7
  obtain ⟨h51, h52, h53, hb1⟩ := allLevelParamsDefined_run c3.ok.state
    (denoteNListE_ext c3.ext _ _ (denoteCV_lps hsh.cvR)) hrec k5
  have d5 := CoreStep.of_readonly c3.ok h51 h52 h53
  have c5 := c3.trans d5
  have hrec5 : denoteE s₅.store recTy = some recTyP := by rw [h51]; exact hrec
  obtain ⟨b2, s₆, k6, z9⟩ := bindOk z8
  obtain ⟨h61, h62, h63, hb2⟩ := constsResolveFFast_run c5.ok hrec5 k6
  have d6 := CoreStep.of_readonly c5.ok h61 h62 h63
  have c6 := c5.trans d6
  have hrec6 : denoteE s₆.store recTy = some recTyP := by rw [h61]; exact hrec5
  obtain ⟨b3, s₇, k7, z10⟩ := bindOk z9
  obtain ⟨h71, h72, h73, hb3⟩ := AM.of_run (P := fun t => t = s₆) rfl k7
    (ExprOps.looseBVarsBoundedFast_spec Arena.coreWalkFuel 0 s₆ recTy c6.ok.state
      (by rw [hrec6]; rfl))
  have d7 := CoreStep.of_readonly c6.ok h71 h72 h73
  have c7 := c6.trans d7
  have hrec7 : denoteE s₇.store recTy = some recTyP := by rw [h71]; exact hrec6
  obtain ⟨b4, s₈, k8, z11⟩ := bindOk z10
  obtain ⟨h81, h82, h83, hb4⟩ := AM.of_run (P := fun t => t = s₇) rfl k8
    (ExprOps.hasFvarFast_spec Arena.coreWalkFuel s₇ recTy c7.ok.state (by rw [hrec7]; rfl))
  have d8 := CoreStep.of_readonly c7.ok h81 h82 h83
  have c8 := c7.trans d8
  have hrec8 : denoteE s₈.store recTy = some recTyP := by rw [h81]; exact hrec7
  have hb3' : b3 = recTyP.looseBVarsBounded 0 := hb3 recTyP hrec6
  have hb4' : b4 = recTyP.hasFvar := hb4 recTyP hrec7
  subst hb1 hb2 hb3' hb4'
  obtain ⟨hg4, z12⟩ := AM.dunless_ok hnever z11
  replace z12 := AM.pure_bind_ok z12
  have hwsR : Expr.WScoped 0 recTyP := by
    have : recTyP.hasFvar = false := by
      revert hg4; cases recTyP.hasFvar <;> simp
    exact Expr.WScoped.of_not_hasFvar this
  -- inferred, a sort, and the stream's recursor's type
  obtain ⟨sty, s₉, k9, z13⟩ := bindOk z12
  obtain ⟨ok9, x9, p9, ⟨styP, hsty, hwsty, F₂, hF₂⟩⟩ := AM.of_run (P := fun u => u = s₈)
    (Q := fun r u => CheckOK μ env fe u ∧ Ext s₈.store u.store ∧
      u.pins = s₈.pins ∧ Core.SimE (ConLeche.inferTypeCore μ env) 0 recTyP u.store r)
    rfl k9 (hknot.infer s₈ 0 recTy recTyP c8.ok hrec8 hwsR)
  have c9 := c8.trans ⟨ok9, x9, p9⟩
  obtain ⟨u, s₁₀, k10, z14⟩ := bindOk z13
  obtain ⟨ok10, x10, p10, ⟨uP, huP, F₃, hF₃⟩⟩ := AM.of_run (P := fun t => t = s₉)
    (Q := fun r t => CheckOK μ env fe t ∧ Ext s₉.store t.store ∧ t.pins = s₉.pins ∧
      SimL (ConLeche.ensureSortCore μ env) 0 styP t.store r)
    rfl k10 (hsort s₉ 0 sty styP ok9 hsty hwsty)
  have c10 := c9.trans ⟨ok10, x10, p10⟩
  obtain ⟨bd, s₁₁, k11, z15⟩ := bindOk z14
  have hwsRi : Expr.WScoped 0 cRiP.type :=
    Expr.WScoped.of_not_hasFvar (ConLeche.checkConstantVal_typeWF hF₁).1
  have x2_10 : Ext s₂.store s₁₀.store :=
    p3.ext.trans (d5.ext.trans (d6.ext.trans (d7.ext.trans (d8.ext.trans (x9.trans x10)))))
  obtain ⟨ok11, x11, p11, ⟨F₄, hF₄⟩⟩ := AM.of_run (P := fun u => u = s₁₀)
    (Q := fun r u => CheckOK μ env fe u ∧ Ext s₁₀.store u.store ∧
      u.pins = s₁₀.pins ∧ Core.SimV (ConLeche.isDefEqCore μ env) 0 cRiP.type recTyP r)
    rfl k11 (hknot.defeq s₁₀ 0 cvRi.type recTy cRiP.type recTyP ok10
      (denote_ext (denoteCV_type hcRi) x2_10) (denote_ext hrec8 (x9.trans x10)) hwsRi hwsR)
  have c11 := c10.trans ⟨ok11, x11, p11⟩
  obtain ⟨hdq, z16⟩ := AM.dunless_ok hnever z15
  replace z16 := AM.pure_bind_ok z16
  subst hdq
  -- the recursor provisioned rule-less, its rules generated at that index
  have hx11 : Ext s₈.store s₁₁.store := x9.trans (x10.trans x11)
  have hcvRa : Frontend.denoteCV s₁₁.store ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ =
      some ⟨q.cvR.name, q.cvR.levelParams, recTyP⟩ := by
    simp only [Frontend.denoteCV, denoteN_ext (denoteCV_name hsh.cvR) c11.ext,
      denoteNListE_ext c11.ext _ _ (denoteCV_lps hsh.cvR), denote_ext hrec8 hx11]
  have hmI : p.majorIdx = q.majorIdx := majorIdx_spec hsh
  have hrP : p.rulePrefix = q.rulePrefix := rulePrefix_spec hsh
  have hciR : Frontend.denoteCI s₁₁.store
      (.recInfo ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ p.majorIdx p.rulePrefix []) =
      some (.recInfo ⟨q.cvR.name, q.cvR.levelParams, recTyP⟩ q.majorIdx q.rulePrefix []) := by
    simp only [Frontend.denoteCI, hcvRa, Frontend.denoteRules, hmI, hrP]
  have hfeR := denoteFEnv_push (denoteFEnv_ext c11.ext hfe) hciR
  have hreadR := c11.ok.toR.push hcoh (fun t h => IConstantInfo.noConfusion h)
    (denoteFEnv_ext c11.ext hfe) hfeR
  obtain ⟨rl, s₁₂, k12, z17⟩ := bindOk z16
  obtain ⟨p12, hrl⟩ := paramLevels_spec p.cvR.levelParams q.cvR.levelParams s₁₁ s₁₂ rl
    c11.ok.state (denoteNListE_ext c11.ext _ _ (denoteCV_lps hsh.cvR)) k12
  obtain ⟨rhss, s₁₃, k13, z18⟩ := bindOk z17
  have x0_11 := c11.ext
  have x11_12 := p12.ext
  have x2_12 : Ext s₂.store s₁₂.store := (x2_10.trans x11).trans x11_12
  have hlen : (Arena.nativeCtors4 ctorsA p.kinds).length =
      (ConLeche.nativeCtors4 ctorsAP q.kinds).length := denoteCtors4_length hc4
  obtain ⟨p13, rhssP, hrules, hrhss⟩ := checkNativeRules_run _ _ p.cvR.levelParams
    q.cvR.levelParams p.cvT.name q.cvT.name p.cvT.levelParams q.cvT.levelParams p.elim q.elim
    p.large p.nP p.nIdx cvTa.type cvTaP.type (Arena.nativeCtors4 ctorsA p.kinds)
    (ConLeche.nativeCtors4 ctorsAP q.kinds) p.cvR.name q.cvR.name rl
    (q.cvR.levelParams.map Level.param) (Arena.nativeCtors4 ctorsA p.kinds).length 0 hkcs
    s₁₂ s₁₃ rhss (hreadR.mono p12.ok x11_12 p12.pins)
    ⟨denoteNListE_ext (x0_11.trans x11_12) _ _ (denoteCV_lps hsh.cvR),
      denoteN_ext hT (x0_11.trans x11_12),
      denoteNListE_ext (x0_11.trans x11_12) _ _ (denoteCV_lps hsh.cvT),
      denoteN_ext hsh.elim (x0_11.trans x11_12),
      denote_ext (denoteCV_type hcvTa) (x0_11.trans x11_12), denoteCtors4_ext x2_12 _ _ hc4,
      denoteN_ext (denoteCV_name hsh.cvR) (x0_11.trans x11_12), hrl,
      denoteFEnv_ext x11_12 hfeR⟩ k13
  obtain ⟨rfl, rfl⟩ := pureOk z18
  refine ⟨c11.trans ((p12.trans p13).toCore c11.ok), max (max F₁ F₂) (max F₃ F₄),
    ⟨q.cvR.name, q.cvR.levelParams, recTyP⟩, rhssP, ?_,
    denoteCV_ext hcvRa (x11_12.trans p13.ext), hrhss⟩
  have g₁ := checkConstantVal_mono (show F₁ ≤ max (max F₁ F₂) (max F₃ F₄) by omega) hF₁
  have g₂ := ConLeche.inferTypeCore_mono (show F₂ ≤ max (max F₁ F₂) (max F₃ F₄) by omega) hF₂
  have g₃ := ConLeche.ensureSortCore_mono (show F₃ ≤ max (max F₁ F₂) (max F₃ F₄) by omega) hF₃
  have g₄ := ConLeche.isDefEqCore_mono (show F₄ ≤ max (max F₁ F₂) (max F₃ F₄) by omega) hF₄
  rw [hlen, hsh.nP, hsh.nIdx, hsh.large] at hrules
  simp only [ConLeche.checkNativeRec]
  rw [if_pos hg1, if_pos hg2, if_pos hg3]
  simp only [bind, Except.bind, g₁, hrecP, ConLeche.unwrapOr, pure, Except.pure]
  rw [if_pos hg4]
  simp only [ConLeche.fueledOps, g₂, g₃, g₄, if_true, hrules]

/-- con-leche: none — a list of level lists keeps its denotation as the
arena grows. -/
theorem denoteLLists_ext {st st' : EStore} (hx : Ext st st') :
    ∀ {ss : List (List LIdx)} {ssP : List (List Level)},
      denoteLLists st ss = some ssP → denoteLLists st' ss = some ssP
  | [], ssP, h => h
  | l :: ls, ssP, h => by
    simp only [denoteLLists] at h ⊢
    split at h
    · rename_i a b ha hb
      have e1 : denoteLList st'.ls l = some a := denoteLList_ext hx.lss.ls _ _ ha
      rw [e1, denoteLLists_ext hx hb]
      exact h
    · exact nomatch h

/-- con-leche: none — a list of level lists denotes elementwise, so its
length is kept. -/
theorem denoteLLists_length {st : EStore} :
    ∀ {ss : List (List LIdx)} {ssP : List (List Level)},
      denoteLLists st ss = some ssP → ss.length = ssP.length
  | [], ssP, h => by simp only [denoteLLists, Option.some.injEq] at h; subst h; rfl
  | l :: ls, ssP, h => by
    simp only [denoteLLists] at h
    split at h
    · rename_i a b _ hb
      obtain rfl := (Option.some.inj h).symm
      simp only [List.length_cons, denoteLLists_length hb]
    · exact nomatch h

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:504-519 checkNativeTable
con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:117-126 checkNativeTableF
**The table stage at the PURE grade** (task #97-P3-Ind round 8): the twin
reads no cache and calls no knot, so it needs no `CheckOK` — which is what
`checkNativeTail` has at this point, where the caches serve the constructors'
environment and not the index the recursor's push just produced.

**CLOSED** (round 8): `structProjGuards_spec`, `structProjGuards_length`
(the `guards` clause, as round 2 planned) and `checkStructProjTable_run`;
the other arms are the identity on both sides.

**This is where the projection table's `guards` clause is discharged** (task
#97-P3-Ind round 2): `checkStructProjTable` takes `guards.length = nF` as a
hypothesis because `guards` is an argument the install cannot test; this is
the caller that builds it, and `structProjGuards_spec` +
`denoteLList_length` + `structProjGuards_length` give it at `nF := cA.2`. -/
theorem checkNativeTable_run (fe : IFEnv) (env : Env) (hcoh : IFEnvCoh fe)
    (p : Arena.NativeParts) (q : ConLeche.NativeParts)
    (ctorsA : List (IConstantVal × Nat)) (ctorsAP : List (ConstantVal × Nat))
    (sortss : List (List LIdx)) (sortssP : List (List Level)) :
    PSpecP
      (fun st => PartsRel st p q ∧ denoteCtors st ctorsA = some ctorsAP ∧
        denoteLLists st sortss = some sortssP ∧ denoteFEnv st fe = some env ∧
        IFEnvOKS env fe st)
      (Arena.checkNativeTable p ctorsA sortss fe)
      (InstRel fe (fun env' =>
        @ConLeche.checkNativeTable CheckM _ _ q ctorsAP sortssP env
          = .ok env')) := by
  intro s₀ s' r hok hpins hpre hrun
  obtain ⟨hp, hcs, hss, hfe, hienv⟩ := hpre
  have hrefl : InstRel fe (fun env' =>
      @ConLeche.checkNativeTable CheckM _ _ q ctorsAP sortssP env = .ok env') s₀.store fe →
      PStep s₀ s₀ ∧ InstRel fe (fun env' =>
      @ConLeche.checkNativeTable CheckM _ _ q ctorsAP sortssP env = .ok env') s₀.store fe :=
    fun h => ⟨PStep.refl hok, h⟩
  have hid : ∀ (h : @ConLeche.checkNativeTable CheckM _ _ q ctorsAP sortssP env = .ok env),
      InstRel fe (fun env' =>
        @ConLeche.checkNativeTable CheckM _ _ q ctorsAP sortssP env = .ok env') s₀.store fe :=
    fun h => ⟨hcoh, Pushed.refl _, Nat.le_refl _, ⟨env, hfe, h⟩, ProjOut.refl _ _⟩
  -- the shape of the two lists decides the arm on both sides
  match ctorsA, sortss, hcs, hss, hrun with
  | [cA], [sorts], hcs, hss, hrun =>
    obtain ⟨cv, nf⟩ := cA
    simp only [denoteCtors] at hcs
    cases hcv : Frontend.denoteCV s₀.store cv with
    | none => rw [hcv] at hcs; simp [denoteCtors] at hcs
    | some cP =>
    rw [hcv] at hcs
    simp only [denoteCtors, Option.some.injEq] at hcs
    subst hcs
    simp only [denoteLLists] at hss
    cases hsd : denoteLList s₀.store.ls sorts with
    | none => rw [hsd] at hss; simp [denoteLLists] at hss
    | some sortsP =>
    rw [hsd] at hss
    simp only [denoteLLists, Option.some.injEq] at hss
    subst hss
    simp only [Arena.checkNativeTable] at hrun
    have hnIdx : p.nIdx = q.nIdx := hp.shape.nIdx
    by_cases hi : (p.nIdx == 0) = true
    · rw [if_pos hi] at hrun
      obtain ⟨guards, s₁, h1, h2⟩ := bindOk hrun
      obtain ⟨p1, hg⟩ := structProjGuards_spec cv.type cP.type p.nP nf sorts sortsP
        s₀ s₁ guards hok hpins ⟨denoteCV_type hcv, hsd⟩ h1
      have hglen : guards.length = nf := by
        rw [denoteLList_length _ _ hg, structProjGuards_length]
      have x1 := p1.ext
      have hsh := hp.shape
      obtain ⟨p2, hr⟩ := checkStructProjTable_run fe env p.cvT.name cv.name q.cvT.name
        cP.name p.cvT.levelParams q.cvT.levelParams p.nP nf p.resSort q.resSort guards _
        1 cv cP hglen hcoh s₁ s' r p1.ok (hpins.mono p1.ext p1.pins)
        ⟨denoteN_ext (denoteCV_name hsh.cvT) x1, denoteN_ext (denoteCV_name hcv) x1,
          denoteNListE_ext x1 _ _ (denoteCV_lps hsh.cvT), denoteL_ext hsh.resSort x1, hg,
          denoteCV_ext hcv x1, denoteFEnv_ext x1 hfe, hienv.mono x1⟩ h2
      refine ⟨p1.trans p2, ?_⟩
      have hi' : (q.nIdx == 0) = true := by rw [← hnIdx]; exact hi
      simp only [ConLeche.checkNativeTable, if_pos hi']
      rw [← hsh.nP]
      exact hr
    · rw [if_neg hi] at hrun
      obtain ⟨rfl, rfl⟩ := pureOk hrun
      have hi' : ¬ (q.nIdx == 0) = true := by rw [← hnIdx]; exact hi
      exact hrefl (hid (by simp only [ConLeche.checkNativeTable, if_neg hi']; rfl))
  | [], _, hcs, hss, hrun =>
    simp only [denoteCtors, Option.some.injEq] at hcs
    subst hcs
    simp only [Arena.checkNativeTable] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact hrefl (hid (by simp only [ConLeche.checkNativeTable]; rfl))
  | [_], [], hcs, hss, hrun =>
    simp only [denoteLLists, Option.some.injEq] at hss
    subst hss
    simp only [Arena.checkNativeTable] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    exact hrefl (hid (by simp only [ConLeche.checkNativeTable]; try rfl))
  | [_], a :: b :: rest, hcs, hss, hrun =>
    have hl := denoteLLists_length hss
    simp only [Arena.checkNativeTable] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine hrefl (hid ?_)
    simp only [ConLeche.checkNativeTable]
    split
    · simp at hl
    · rfl
  | a :: b :: rest, _, hcs, hss, hrun =>
    have hl := denoteCtors_length _ _ hcs
    simp only [Arena.checkNativeTable] at hrun
    obtain ⟨rfl, rfl⟩ := pureOk hrun
    refine hrefl (hid ?_)
    simp only [ConLeche.checkNativeTable]
    split
    · simp at hl
    · rfl

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:504-519 checkNativeTable
The same at the core grade, read off `checkNativeTable_run`.  **`hcoh`
added** (task #97-P3-Ind round 8: the table's push needs the old index
coherent, `checkStructProjTable_spec`'s ruling 3). -/
theorem checkNativeTable_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hcoh : IFEnvCoh fe)
    (p : Arena.NativeParts) (q : ConLeche.NativeParts)
    (ctorsA : List (IConstantVal × Nat)) (ctorsAP : List (ConstantVal × Nat))
    (sortss : List (List LIdx)) (sortssP : List (List Level)) :
    CSpec μ env fe
      (fun st => PartsRel st p q ∧ denoteCtors st ctorsA = some ctorsAP ∧
        denoteLLists st sortss = some sortssP ∧ denoteFEnv st fe = some env)
      (Arena.checkNativeTable p ctorsA sortss fe)
      (InstRel fe (fun env' =>
        @ConLeche.checkNativeTable CheckM _ _ q ctorsAP sortssP env
          = .ok env')) :=
  (checkNativeTable_run fe env hcoh p q ctorsA ctorsAP sortss sortssP).toCSpec μ env fe |>
    fun h => by
      intro s₀ s' r hok hpre hrun
      obtain ⟨a1, a2, a3, a4⟩ := hpre
      exact h s₀ s' r hok ⟨a1, a2, a3, a4, hok.ienv.toS⟩ hrun

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

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:96-112 checkSumInd
(its shape) — **the former's stage pushes exactly one row, the former**, which
is not a projection table.  Structural: read off the twin's last line. -/
theorem checkSumInd_push {μ : CheckMode} {fe : IFEnv} {p : Arena.InductiveShape}
    {isRec : Bool} {s s' : AState} {r : IFEnv × IConstantVal × Arena.InductiveShape}
    (h : Arena.checkSumInd μ fe p isRec s = .ok (r, s')) :
    ∃ caps, r.1 = fe.push (.indInfo r.2.1 caps) := by
  simp only [Arena.checkSumInd] at h
  obtain ⟨_, _, _, h⟩ := bindOk h
  obtain ⟨⟨cvTa, so⟩, _, _, h⟩ := bindOk h
  obtain ⟨o, _, _, h⟩ := bindOk h
  obtain ⟨⟨bs, tbody⟩, _, _, h⟩ := bindOk h
  obtain ⟨_, _, _, h⟩ := bindOk h
  obtain ⟨-, h⟩ := AM.dunless_ok AM.Never.fail_any h
  replace h := AM.pure_bind_ok h
  obtain ⟨_, _, _, h⟩ := bindOk h
  obtain ⟨caps, _, _, h⟩ := bindOk h
  obtain ⟨rfl, rfl⟩ := pureOk h
  exact ⟨caps, rfl⟩

/-- con-leche: none — **two capability records compare as their
denotations do**: every field but `etaCtor` is copied, and `etaCtor` is a
name handle, where `denoteN` is injective. -/
theorem denoteCaps_beq {st : EStore} (hwf : StoreWF st) {a b : IIndCaps}
    {A B : IndCaps} (ha : Frontend.denoteCaps st a = some A)
    (hb : Frontend.denoteCaps st b = some B) : (a == b) = (A == B) := by
  obtain ⟨rk, hrk⟩ := hwf
  simp only [Frontend.denoteCaps] at ha hb
  cases hA : denoteN st.ns a.etaCtor with
  | none => rw [hA] at ha; simp at ha
  | some ca =>
  cases hB : denoteN st.ns b.etaCtor with
  | none => rw [hB] at hb; simp at hb
  | some cb =>
  rw [hA] at ha; rw [hB] at hb
  obtain rfl := Option.some.inj ha
  obtain rfl := Option.some.inj hb
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · rintro rfl
    rw [hA] at hB
    cases hB
    rfl
  · intro h
    simp only [IndCaps.mk.injEq] at h
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := h
    subst e2
    have he : a.etaCtor = b.etaCtor := denoteN_inj hrk.nsWF hA hB
    cases a
    cases b
    simp_all

theorem checkSumInd_up {μ : CheckMode} {F G : Nat} {env : Env} {p : ConLeche.InductiveShape}
    {capsOf : ConLeche.InductiveShape → IndCaps}
    {v : Env × ConstantVal × ConLeche.InductiveShape} (hle : F ≤ G)
    (h : ConLeche.checkSumInd (ConLeche.fueledOps μ F) env p capsOf = .ok v) :
    ConLeche.checkSumInd (ConLeche.fueledOps μ G) env p capsOf = .ok v := by
  rw [← ConLeche.checkSumInd_datF] at h ⊢
  exact (ConLeche.checkSumInd (ConLeche.fueledOpsM μ) env p capsOf).property hle h

theorem checkSumCtors_up {μ : CheckMode} {F G : Nat} {env₀ env : Env} {T : ConLeche.Name}
    {lps : List ConLeche.Name} {nP nIdx : Nat} {rs : Level} {isProp large : Bool}
    {cvTa : ConstantVal} {cs : List (ConstantVal × Nat)}
    {v : List (ConstantVal × Nat) × List (List Level)} (hle : F ≤ G)
    (h : ConLeche.checkSumCtors (ConLeche.fueledOps μ F) env₀ env T lps nP nIdx rs isProp
      large cvTa cs = .ok v) :
    ConLeche.checkSumCtors (ConLeche.fueledOps μ G) env₀ env T lps nP nIdx rs isProp
      large cvTa cs = .ok v := by
  rw [← ConLeche.checkSumCtors_datF] at h ⊢
  exact (ConLeche.checkSumCtors (ConLeche.fueledOpsM μ) env₀ env T lps nP nIdx rs isProp
    large cvTa cs).property hle h

/-- con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:269-272 consSumCtors
— **the read invariant survives the constructors' conses** (`ReadOK.push`
at each, none of them a projection table). -/
theorem ReadOK.consSumCtors {nP : Nat} {s : AState} :
    ∀ {cs : List (IConstantVal × Nat)} {csP : List (ConstantVal × Nat)}
      {fe : IFEnv} {env : Env},
      ReadOK env fe s → IFEnvCoh fe → denoteCtors s.store cs = some csP →
      denoteFEnv s.store fe = some env →
      ReadOK (ConLeche.consSumCtors nP csP env) (Arena.consSumCtors nP cs fe) s
  | [], csP, fe, env, h, _, hcs, _ => by
    simp only [denoteCtors, Option.some.injEq] at hcs
    subst hcs
    exact h
  | c :: cs, csP, fe, env, h, hcoh, hcs, hfe => by
    obtain ⟨cv, n⟩ := c
    simp only [denoteCtors] at hcs
    cases hcv : Frontend.denoteCV s.store cv with
    | none => rw [hcv] at hcs; simp at hcs
    | some cP =>
    cases hrest : denoteCtors s.store cs with
    | none => rw [hcv, hrest] at hcs; simp at hcs
    | some restP =>
    rw [hcv, hrest] at hcs
    obtain rfl := (Option.some.inj hcs).symm
    have hci : Frontend.denoteCI s.store (.ctorInfo cv nP n) = some (.ctorInfo cP nP n) := by
      simp only [Frontend.denoteCI, hcv, Option.map_some]
    have hpush := denoteFEnv_push hfe hci
    have h1 : ReadOK ⟨.ctorInfo cP nP n :: env.consts⟩ (fe.push (.ctorInfo cv nP n)) s :=
      h.push hcoh (fun t ht => IConstantInfo.noConfusion ht) hfe hpush
    have := ReadOK.consSumCtors (nP := nP) h1 (hcoh.push _) hrest hpush
    simp only [Arena.consSumCtors, ConLeche.consSumCtors]
    exact this

theorem checkNativeRec_up {μ : CheckMode} {F G : Nat} {env : Env}
    {p : ConLeche.NativeParts} {cvTa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {v : ConstantVal × List Expr} (hle : F ≤ G)
    (h : ConLeche.checkNativeRec (ConLeche.fueledOps μ F) env p cvTa ctorsA = .ok v) :
    ConLeche.checkNativeRec (ConLeche.fueledOps μ G) env p cvTa ctorsA = .ok v := by
  rw [← ConLeche.checkNativeRec_datF] at h ⊢
  exact (ConLeche.checkNativeRec (ConLeche.fueledOpsM μ) env p cvTa ctorsA).property hle h

theorem checkStructFieldSortsI_up {μ : CheckMode} {F G : Nat} {env : Env}
    {isProp large : Bool} {s : Level} {nP : Nat} {fvs idxArgs : List Expr} {j : Nat}
    {v : List Level} (hle : F ≤ G)
    (h : ConLeche.checkStructFieldSortsI (ConLeche.fueledOps μ F) env isProp large s nP fvs
      idxArgs j = .ok v) :
    ConLeche.checkStructFieldSortsI (ConLeche.fueledOps μ G) env isProp large s nP fvs
      idxArgs j = .ok v := by
  rw [← ConLeche.checkStructFieldSortsI_datF] at h ⊢
  exact (ConLeche.checkStructFieldSortsI (ConLeche.fueledOpsM μ) env isProp large s nP fvs
    idxArgs j).property hle h

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:556-574 checkNativePass
**One pass over the former and the constructors** at a given `is_rec` verdict,
with the flag that says whether the classification confirms it.

`sorry`: `checkSumInd_spec`, `complete_spec`, `flushCaches_spec`
(`Bridge/Specs.lean`, closed, with `CacheOK.of_empty`), `checkSumCtors_spec`,
`classifyFixKinds_spec`, `withKinds_spec`, `nativeCaps_spec` and
`nativeCapsAt_spec`. -/
theorem checkNativePass_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (p₀ : Arena.NativeParts) (q₀ : ConLeche.NativeParts) (isRec : Bool) :
    ISpec
      (fun s => CheckOK μ env fe s ∧ PartsRel s.store p₀ q₀ ∧
        denoteFEnv s.store fe = some env ∧ IFEnvCoh fe)
      (Arena.checkNativePass μ fe p₀ isRec)
      (fun s r => ∃ F qP settled,
        ConLeche.checkNativePass (ConLeche.fueledOps μ F) env q₀ isRec
          = .ok (qP, settled) ∧
        PassRel qP s.store r.1 ∧ r.2 = settled ∧
        InstRel fe (fun e => e = qP.env₁) s.store r.1.env₁ ∧
        CheckOK μ qP.env₁ r.1.env₁ s) := by
  intro s₀ s' r hpre hrun
  obtain ⟨hck, hp, hfe, hcoh⟩ := hpre
  simp only [Arena.checkNativePass] at hrun
  -- the former
  obtain ⟨t1, s₁, k1, z1⟩ := bindOk hrun
  obtain ⟨caps, hpush⟩ := checkSumInd_push k1
  obtain ⟨c1, F₁, envP, cvTaP, qP₁, hF₁, hinst₁, hcv₁, hsh₁⟩ :=
    checkSumInd_spec fe hμ hk henv hcoh p₀.toInductiveShape q₀.toInductiveShape isRec
      s₀ s₁ t1 hck ⟨hp.shape, hfe⟩ k1
  obtain ⟨fe₁, cvTa, p₁⟩ := t1
  simp only at hpush hinst₁ hcv₁ hsh₁ z1
  obtain ⟨henv₁, hTf⟩ := ConLeche.direct_sum_ind_wf henv hF₁
    (fun q => ConLeche.nativeCapsAt_arity q isRec)
  -- the flush, at the former's index
  obtain ⟨u, s₂, k2, z2⟩ := bindOk z1
  obtain ⟨envP', hden₁, rfl⟩ := hinst₁.denote
  have hread₁ : ReadOK envP' fe₁ s₁ := by
    rw [hpush] at hden₁ ⊢
    exact (c1.ok.toR).push hcoh (fun t h => nomatch h) (denoteFEnv_ext c1.ext hfe) hden₁
  obtain ⟨hck₂, hi₂, hst₂⟩ := hread₁.flush (μ := μ) k2
  have hpc : PartsRel s₂.store (p₀.complete p₁) (q₀.complete qP₁) := by
    rw [hst₂]; exact complete_spec (hp.ext c1.ext) hsh₁
  have hsh₁' := hpc.shape
  -- the constructors, at the former's environment
  obtain ⟨t3, s₃, k3, z3⟩ := bindOk z2
  have hws : Expr.WScoped 0 cvTaP.type := Expr.WScoped.of_not_hasFvar hTf
  have hden₂ : denoteFEnv s₂.store fe₁ = some envP' := by rw [hst₂]; exact hden₁
  obtain ⟨c3, F₂, ctorsAP, sortssP, hF₂, hct₃, hss₃⟩ :=
    checkSumCtors_spec fe₁ fe₁ hμ hk henv₁ (p₀.complete p₁).cvT.name
      (q₀.complete qP₁).cvT.name (p₀.complete p₁).cvT.levelParams
      (q₀.complete qP₁).cvT.levelParams (p₀.complete p₁).nP (p₀.complete p₁).nIdx
      (p₀.complete p₁).resSort (q₀.complete qP₁).resSort (p₀.complete p₁).isProp
      (p₀.complete p₁).large cvTa cvTaP envP' (p₀.complete p₁).ctors (q₀.complete qP₁).ctors
      hws s₂ s₃ t3 hck₂
      ⟨denoteCV_name hsh₁'.cvT, denoteCV_lps hsh₁'.cvT, hsh₁'.resSort,
        by rw [hst₂]; exact denoteCV_ext hcv₁ (Ext.refl _), hsh₁'.ctors, hden₂, hden₂,
        hck₂.ienv.toS⟩ k3
  obtain ⟨ctorsA, sortss⟩ := t3
  simp only at hct₃ hss₃ z3
  -- the kinds
  obtain ⟨kinds, s₄, k4, z4⟩ := bindOk z3
  have x23 := c3.ext
  obtain ⟨c4, ks, hks, hkr⟩ :=
    classifyFixKinds_spec fe₁ (p₀.complete p₁).cvT.name (q₀.complete qP₁).cvT.name
      (p₀.complete p₁).cvT.levelParams (q₀.complete qP₁).cvT.levelParams
      (p₀.complete p₁).nP (p₀.complete p₁).nIdx ctorsA ctorsAP s₃ s₄ kinds c3.ok
      ⟨denoteN_ext (denoteCV_name hsh₁'.cvT) x23,
        denoteNListE_ext x23 _ _ (denoteCV_lps hsh₁'.cvT), hct₃⟩ k4
  have c24 := c3.trans c4
  -- the two capability records
  obtain ⟨ca, s₅, k5, z5⟩ := bindOk z4
  have hpk : PartsRel s₄.store ((p₀.complete p₁).withKinds kinds)
      ((q₀.complete qP₁).withKinds (kinds.map (·.map kindOf))) :=
    withKinds_spec (hpc.ext c24.ext)
  obtain ⟨p5, hca⟩ := nativeCaps_spec _ _ s₄ s₅ ca c24.ok.state c24.ok.pins hpk k5
  obtain ⟨cb, s₆, k6, z6⟩ := bindOk z5
  have x15 : Ext s₁.store s₅.store := by
    have := c24.ext.trans p5.ext
    rw [hst₂] at this
    exact this
  obtain ⟨p6, hcb⟩ := nativeCapsAt_spec p₁ qP₁ isRec s₅ s₆ cb p5.ok
    (c24.ok.pins.mono p5.ext p5.pins) (hsh₁.ext x15) k6
  obtain ⟨rfl, rfl⟩ := pureOk z6
  have c26 : CoreStep μ envP' fe₁ s₂ s' := (c24.trans (p5.toCore c24.ok)).trans
    (p6.toCore (c24.trans (p5.toCore c24.ok)).ok)
  have x2' : Ext s₂.store s'.store := c26.ext
  have x1' : Ext s₁.store s'.store := by rw [← hst₂]; exact x2'
  have x5' : Ext s₅.store s'.store := p6.ext
  have hks' : ks = kinds.map (·.map kindOf) := hkr.symm
  subst hks'
  have hcaEq := denoteCaps_beq c26.ok.state.wf (denoteCaps_ext hca x5') hcb
  refine ⟨c1.toInst.trans (hi₂.trans c26.toInst), max F₁ F₂,
    ⟨envP', cvTaP, (q₀.complete qP₁).withKinds (kinds.map (·.map kindOf)), ctorsAP, sortssP⟩,
    ConLeche.nativeCaps ((q₀.complete qP₁).withKinds (kinds.map (·.map kindOf))) ==
      ConLeche.nativeCapsAt qP₁ isRec, ?_, ?_, hcaEq, hinst₁.ext x1', c26.ok⟩
  · have g₁ := checkSumInd_up (Nat.le_max_left F₁ F₂) hF₁
    have g₂ := checkSumCtors_up (Nat.le_max_right F₁ F₂) hF₂
    rw [hsh₁'.nP, hsh₁'.nIdx, hsh₁'.isProp, hsh₁'.large] at g₂
    rw [hsh₁'.nP, hsh₁'.nIdx] at hks
    simp only [ConLeche.checkNativePass, bind, Except.bind, g₁, g₂, hks, pure, Except.pure]
  · have x4' : Ext s₄.store s'.store := p5.ext.trans x5'
    have x3' : Ext s₃.store s'.store := c4.ext.trans x4'
    exact ⟨denoteFEnv_ext x1' hden₁, denoteCV_ext hcv₁ x1', hpk.ext x4',
      denoteCtors_ext x3' _ _ hct₃, denoteLLists_ext x3' hss₃⟩

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
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel)
    (r : Arena.NativePass) (qP : ConLeche.NativePass Env)
    (henv₁ : EnvWF qP.env₁) (hTf : qP.cvTa.type.hasFvar = false)
    (henv₂ : EnvWF (ConLeche.consSumCtors qP.p.nP qP.ctorsA qP.env₁))
    (hkcs : ∀ c ∈ ConLeche.nativeCtors4 qP.ctorsA qP.p.kinds, ∀ i ∈ c.2.2.2, i < c.2.1) :
    ISpec
      (fun s => CheckOK μ qP.env₁ r.env₁ s ∧ ReadOK env fe s ∧
        PassRel qP s.store r ∧ denoteFEnv s.store fe = some env ∧
        InstRel fe (fun e => e = qP.env₁) s.store r.env₁)
      (Arena.checkNativeTail μ fe r)
      (fun s fe' => InstRel fe (fun env' => ∃ F,
        ConLeche.checkNativeTail (ConLeche.fueledOps μ F) env qP = .ok env')
        s.store fe') := by
  intro s₀ s' fe' hpre hrun
  obtain ⟨hck, hread, hpass, hfe, hinst₁⟩ := hpre
  have hsh := hpass.p.shape
  simp only [Arena.checkNativeTail] at hrun
  -- the elimination restriction
  obtain ⟨u, s₁, k1, z1⟩ := bindOk hrun
  obtain ⟨rfl, hu⟩ := readLevel_run k1
  obtain rfl : u = qP.p.resSort := Option.some.inj (hu.symm.trans hsh.resSort)
  have hlen : r.p.ctors.length = qP.p.ctors.length := denoteCtors_length _ _ hsh.ctors
  have hlarge : r.p.large = qP.p.large := hsh.large
  split at z1
  · exact absurd z1 (AM.Never.fail_any _ _ _)
  rename_i hg
  replace z1 := AM.pure_bind_ok z1
  have hck₀ := hck
  -- the former's telescope, opened
  obtain ⟨o, s₂, k2, z2⟩ := bindOk z1
  obtain ⟨p2, ho⟩ := openPisAtFvarsF_run hck.state (denoteCV_type hpass.cvTa) k2
  obtain ⟨tq, s₃, k3, z3⟩ := bindOk z2
  cases o with
  | none => simp only [Arena.unwrapOr] at k3; exact absurd k3 (fun h => failOk h)
  | some tq' =>
  simp only [Arena.unwrapOr] at k3
  obtain ⟨rfl, rfl⟩ := pureOk k3
  obtain ⟨fvsP, bodyP, htq, hfvs, hbody⟩ := denoteOpen_some_inv ho
  rw [hsh.nP, hsh.nIdx] at htq
  -- the index binders' sorts
  obtain ⟨is, s₄, k4, z4⟩ := bindOk z3
  have hTw : Expr.WScoped 0 qP.cvTa.type := Expr.WScoped.of_not_hasFvar hTf
  obtain ⟨htqW, -⟩ := ConLeche.openPisAtFvars_WScoped _ _ _ htq hTw
  have hidxT := ConLeche.openPisAtFvars_index _ _ _ htq
  have hxPos : ∀ i, i < qP.p.nIdx → ∀ (x : Expr), (fvsP.drop qP.p.nP)[i]? = some x →
      Expr.WScoped (qP.p.nP + i) (Expr.fvarTypeD x) := by
    intro i _ x hx
    rw [List.getElem?_drop] at hx
    obtain ⟨ty, rfl⟩ := hidxT (qP.p.nP + i) x hx
    have hw := htqW _ (List.mem_of_getElem? hx)
    simp only [Expr.WScoped, Nat.zero_add] at hw
    exact hw.2
  have c2 : CoreStep μ qP.env₁ r.env₁ s₁ s₃ := p2.toCore hck
  obtain ⟨c4, F₀, isP, hF₀, his⟩ := checkStructFieldSortsI_spec r.env₁ hk henv₁ true false
    r.p.resSort qP.p.resSort r.p.nP (tq.1.drop r.p.nP) [] (fvsP.drop qP.p.nP) [] r.p.nIdx
    (by rw [hsh.nP, hsh.nIdx]; exact hxPos) s₃ s₄ is c2.ok
    ⟨denoteL_ext hsh.resSort p2.ext, by rw [hsh.nP]; exact denoteEList_drop hfvs _, rfl,
      denoteFEnv_ext p2.ext hpass.env₁⟩ k4
  have x14 : Ext s₁.store s₄.store := p2.ext.trans c4.ext
  -- the kinds, re-checked on the stored constructors (at the ENTRY index)
  obtain ⟨b5, s₅, k5, z5⟩ := bindOk z4
  obtain ⟨p5, hb5⟩ := nativeFieldsOk_spec fe env r.p.cvT.name qP.p.cvT.name
    r.p.cvT.levelParams qP.p.cvT.levelParams r.p.nP r.p.nIdx r.ctorsA qP.ctorsA r.p.kinds
    s₄ s₅ b5 (hread.mono c4.ok.state x14 (by rw [c4.pins, p2.pins]))
    ⟨denoteN_ext (denoteCV_name hsh.cvT) x14, denoteNListE_ext x14 _ _ (denoteCV_lps hsh.cvT),
      denoteCtors_ext x14 _ _ hpass.ctorsA, denoteFEnv_ext x14 hfe⟩ k5
  obtain ⟨hb5', z6⟩ := AM.dunless_ok AM.Never.fail_any z5
  replace z6 := AM.pure_bind_ok z6
  rw [hb5, hsh.nP, hsh.nIdx, hpass.p.kinds] at hb5'
  -- the stream's rules against the generated ones
  have x15 : Ext s₁.store s₅.store := x14.trans p5.ext
  obtain ⟨rl, s₆, k6, z6⟩ := bindOk z6
  obtain ⟨p6, hrl⟩ := paramLevels_spec r.p.cvR.levelParams qP.p.cvR.levelParams s₅ s₆ rl p5.ok
    (denoteNListE_ext x15 _ _ (denoteCV_lps hsh.cvR)) k6
  have x16 : Ext s₁.store s₆.store := x15.trans p6.ext
  obtain ⟨b7, s₇, k7, z7⟩ := bindOk z6
  obtain ⟨p7, hb7⟩ := nativeRulesOk_spec r.p.cvR.name qP.p.cvR.name rl _ .never r.p.nP
    r.p.ctors.length r.ctorsA qP.ctorsA r.p.kinds r.p.rhss qP.p.rhss r.p.cvR.type qP.p.cvR.type
    s₆ s₇ b7 p6.ok ⟨denoteN_ext (denoteCV_name hsh.cvR) x16, hrl,
      denoteCtors_ext x16 _ _ hpass.ctorsA, denoteEList_ext x16 _ _ hsh.rhss,
      denote_ext (denoteCV_type hsh.cvR) x16⟩ k7
  obtain ⟨hb7', z8⟩ := AM.dunless_ok AM.Never.fail_any z7
  replace z8 := AM.pure_bind_ok z8
  have hb7'' := hb7'
  rw [hb7, hsh.nP, hlen, hpass.p.kinds] at hb7''
  have x17 : Ext s₁.store s₇.store := x16.trans p7.ext
  -- the constructors consed, and the flush
  obtain ⟨u8, s₈, k8, z9⟩ := bindOk z8
  have hread₁ : ReadOK qP.env₁ r.env₁ s₇ :=
    hck.toR.mono p7.ok x17 (by rw [p7.pins, p6.pins, p5.pins, c4.pins, p2.pins])
  have hcoh₁ : IFEnvCoh r.env₁ := hinst₁.coh
  have hread₂ : ReadOK (ConLeche.consSumCtors qP.p.nP qP.ctorsA qP.env₁)
      (Arena.consSumCtors r.p.nP r.ctorsA r.env₁) s₇ := by
    rw [← hsh.nP]
    exact ReadOK.consSumCtors hread₁ hcoh₁
      (denoteCtors_ext x17 _ _ hpass.ctorsA) (denoteFEnv_ext x17 hpass.env₁)
  have hinst₂ : InstRel r.env₁ (fun e => e = ConLeche.consSumCtors qP.p.nP qP.ctorsA qP.env₁)
      s₇.store (Arena.consSumCtors r.p.nP r.ctorsA r.env₁) := by
    rw [← hsh.nP]
    exact consSumCtors_spec s₇.store r.p.nP r.ctorsA qP.ctorsA r.env₁ qP.env₁
      (denoteCtors_ext x17 _ _ hpass.ctorsA) (denoteFEnv_ext x17 hpass.env₁) hcoh₁
  have hden₂ : denoteFEnv s₇.store (Arena.consSumCtors r.p.nP r.ctorsA r.env₁)
      = some (ConLeche.consSumCtors qP.p.nP qP.ctorsA qP.env₁) := by
    obtain ⟨e, he, rfl⟩ := hinst₂.denote
    exact he
  obtain ⟨hck₈, hi₈, hst₈⟩ := hread₂.flush (μ := μ) k8
  have x18 : Ext s₁.store s₈.store := by rw [hst₈]; exact x17
  -- the recursor, generated and compared, at the constructors' environment
  obtain ⟨rr, s₉, k9, z10⟩ := bindOk z9
  obtain ⟨c9, F₃, cvRaP, rhssP, hF₃, hcvRa, hrhss⟩ := checkNativeRec_spec
    (Arena.consSumCtors r.p.nP r.ctorsA r.env₁) hμ hk henv₂ hinst₂.coh r.p qP.p r.cvTa
    qP.cvTa r.ctorsA qP.ctorsA hkcs s₈ s₉ rr hck₈
    ⟨hpass.p.ext x18, denoteCV_ext hpass.cvTa x18, denoteCtors_ext x18 _ _ hpass.ctorsA,
      by rw [hst₈]; exact hden₂⟩ k9
  obtain ⟨cvRa, rhss⟩ := rr
  simp only at hcvRa hrhss z10
  have x19 : Ext s₁.store s₉.store := x18.trans c9.ext
  have x79 : Ext s₇.store s₉.store := by
    have := c9.ext
    rw [hst₈] at this
    exact this
  -- the rules
  obtain ⟨rules, s₁₀, k10, z11⟩ := bindOk z10
  obtain ⟨c10, hrules⟩ := sumRules_spec (Arena.consSumCtors r.p.nP r.ctorsA r.env₁)
    cvRa.name cvRaP.name r.p.nP r.p.majorIdx r.p.rulePrefix cvRa.type cvRaP.type r.ctorsA
    qP.ctorsA rhss rhssP s₉ s₁₀ rules c9.ok
    ⟨denoteCV_name hcvRa, denoteCV_type hcvRa, denoteCtors_ext x19 _ _ hpass.ctorsA, hrhss,
      denoteFEnv_ext x79 hden₂⟩ k10
  have x9' : Ext s₉.store s₁₀.store := c10.ext
  have hmI : r.p.majorIdx = qP.p.majorIdx := majorIdx_spec hsh
  have hrP : r.p.rulePrefix = qP.p.rulePrefix := rulePrefix_spec hsh
  rw [hsh.nP, hmI, hrP] at hrules
  -- the recursor pushed, and the table
  have hci : Frontend.denoteCI s₁₀.store (.recInfo cvRa r.p.majorIdx r.p.rulePrefix rules)
      = some (.recInfo cvRaP qP.p.majorIdx qP.p.rulePrefix
          (ConLeche.sumRules (ConLeche.consSumCtors qP.p.nP qP.ctorsA qP.env₁).find?
            cvRaP.name qP.p.nP qP.p.majorIdx qP.p.rulePrefix cvRaP.type qP.ctorsA rhssP)) := by
    simp only [Frontend.denoteCI, denoteCV_ext hcvRa x9', hrules, hmI, hrP]
  have x7' : Ext s₇.store s₁₀.store := x79.trans x9'
  have hden₃ := denoteFEnv_push (denoteFEnv_ext x7' hden₂) hci
  have hcoh₂ : IFEnvCoh (Arena.consSumCtors r.p.nP r.ctorsA r.env₁) := hinst₂.coh
  have hread₁₀ := hread₂.ofInst (hi₈.trans (c9.toInst.trans c10.toInst))
  have hienv₃ := ((hread₁₀.push hcoh₂ (fun t h => IConstantInfo.noConfusion h)
    (denoteFEnv_ext x7' hden₂) hden₃).ienv).toS
  obtain ⟨p11, hinst₄⟩ := checkNativeTable_run _ _ (hcoh₂.push _) r.p qP.p r.ctorsA qP.ctorsA
    r.sortss qP.sortss s₁₀ s' fe' c10.ok.state c10.ok.pins
    ⟨hpass.p.ext (x19.trans x9'), denoteCtors_ext (x19.trans x9') _ _ hpass.ctorsA,
      denoteLLists_ext (x19.trans x9') hpass.sortss, hden₃, hienv₃⟩ z11
  have x1' : Ext s₁.store s'.store := (x19.trans x9').trans p11.ext
  have x7'' : Ext s₇.store s'.store := x7'.trans p11.ext
  have hinst₃ : InstRel (Arena.consSumCtors r.p.nP r.ctorsA r.env₁) (fun _ => True)
      s₁₀.store ((Arena.consSumCtors r.p.nP r.ctorsA r.env₁).push
        (.recInfo cvRa r.p.majorIdx r.p.rulePrefix rules)) :=
    ⟨hcoh₂.push _, Pushed.push _ _, Nat.le_succ _, ⟨_, hden₃, trivial⟩,
      ProjOut.push hcoh₂ _ (fun t h => IConstantInfo.noConfusion h)⟩
  refine ⟨(p2.toInst.trans c4.toInst).trans ((p5.toInst.trans (p6.toInst.trans p7.toInst)).trans
    (hi₈.trans (c9.toInst.trans (c10.toInst.trans p11.toInst)))), ?_⟩
  have hall := InstRel.trans x1' hinst₁
    (InstRel.trans x7'' hinst₂ (InstRel.trans p11.ext hinst₃ hinst₄))
  refine hall.imp ?_
  rintro e he
  rw [hsh.nP, hsh.nIdx] at hF₀
  rw [hlarge, hlen] at hg
  refine ⟨max F₀ F₃, ?_⟩
  have g₀ := checkStructFieldSortsI_up (Nat.le_max_left F₀ F₃) hF₀
  have g₃ := checkNativeRec_up (Nat.le_max_right F₀ F₃) hF₃
  simp only [ConLeche.checkNativeTail, bind, Except.bind, pure, Except.pure]
  rw [if_neg hg]
  simp only [htq, ConLeche.unwrapOr, pure, Except.pure]
  rw [g₀]
  simp only [if_pos hb5', if_pos hb7'']
  rw [g₃]
  exact he

/-! ## The route's pure side: fuel and well-formedness (task #97-P3-Ind round 8)

The twin's route calls the knot at THREE environments — the entry one, the
former's (`env₁`) and the constructors' (`env₂`) — and `CoreSpec.knot` is
stated at a well-formed one.  The two new ones are con-leche's own V-free
facts about the pure pass, assembled here the way con-leche's cached bridge
(`Verify/Cached/BridgeCSDecl.lean`'s `checkNativePassS_run`) assembles them. -/

/-- con-leche: ConLeche/Verify/Cached/BridgeCSDecl.lean:251 checkNativePassS_run
(its `EnvWF` half) — **a pass leaves the former's environment and the
constructors' conses well formed, and the former's type closed.** -/
theorem checkNativePass_envWF {μ : CheckMode} {F : Nat} {env : Env}
    {p₀ : ConLeche.NativeParts} {isRec : Bool} {q : ConLeche.NativePass Env} {b : Bool}
    (henv : EnvWF env)
    (h : ConLeche.checkNativePass (ConLeche.fueledOps μ F) env p₀ isRec = .ok (q, b)) :
    EnvWF q.env₁ ∧ q.cvTa.type.hasFvar = false ∧
      EnvWF (ConLeche.consSumCtors q.p.nP q.ctorsA q.env₁) := by
  obtain ⟨p₁, kinds, hInd, hCtors, -, hp, -⟩ := ConLeche.checkNativePass_inv h
  obtain ⟨henv₁, hTf⟩ := ConLeche.direct_sum_ind_wf henv hInd
    (fun q => ConLeche.nativeCapsAt_arity q isRec)
  refine ⟨henv₁, hTf, ?_⟩
  have hnP : q.p.nP = (p₀.complete p₁).nP := by rw [hp]; rfl
  rw [hnP]
  refine ConLeche.envWF_consSumCtors henv₁ ?_
  intro c hc
  obtain ⟨hlen, -, hall⟩ := ConLeche.checkSumCtors_inv hCtors
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
  have hj' : j < (p₀.complete p₁).ctors.length := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    omega
  obtain ⟨-, sorts, -, hrun⟩ := hall j ((p₀.complete p₁).ctors[j]) c
    (List.getElem?_eq_getElem hj') hj
  exact ConLeche.direct_sum_ctor_typeWF hrun

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:556-574 checkNativePass
— **the pass's kinds fit its constructors** (`classifyFixKinds_hcs` at the
pass's own classification). -/
theorem checkNativePass_hcs {μ : CheckMode} {F : Nat} {env : Env}
    {p₀ : ConLeche.NativeParts} {isRec : Bool} {q : ConLeche.NativePass Env} {b : Bool}
    (h : ConLeche.checkNativePass (ConLeche.fueledOps μ F) env p₀ isRec = .ok (q, b)) :
    ∀ c ∈ ConLeche.nativeCtors4 q.ctorsA q.p.kinds, ∀ i ∈ c.2.2.2, i < c.2.1 := by
  obtain ⟨p₁, kinds, -, -, hK, hp, -⟩ := ConLeche.checkNativePass_inv h
  rw [hp]
  exact classifyFixKinds_hcs hK

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:800 checkNativePass_datF — one
fuel for the pass, through con-leche's own monotone family. -/
theorem checkNativePass_up {μ : CheckMode} {F G : Nat} {env : Env}
    {p₀ : ConLeche.NativeParts} {isRec : Bool} {v : ConLeche.NativePass Env × Bool}
    (hle : F ≤ G)
    (h : ConLeche.checkNativePass (ConLeche.fueledOps μ F) env p₀ isRec = .ok v) :
    ConLeche.checkNativePass (ConLeche.fueledOps μ G) env p₀ isRec = .ok v := by
  rw [← ConLeche.checkNativePass_datF] at h ⊢
  exact (ConLeche.checkNativePass (ConLeche.fueledOpsM μ) env p₀ isRec).property hle h

/-- con-leche: ConLeche/Verify/BridgeDecl.lean:807 checkNativeTail_datF. -/
theorem checkNativeTail_up {μ : CheckMode} {F G : Nat} {env : Env}
    {q : ConLeche.NativePass Env} {v : Env} (hle : F ≤ G)
    (h : ConLeche.checkNativeTail (ConLeche.fueledOps μ F) env q = .ok v) :
    ConLeche.checkNativeTail (ConLeche.fueledOps μ G) env q = .ok v := by
  rw [← ConLeche.checkNativeTail_datF] at h ⊢
  exact (ConLeche.checkNativeTail (ConLeche.fueledOpsM μ) env q).property hle h

/-- con-leche: none — a name is among a constructor list's iff its
denotation is among the denoted list's: `denoteN` is injective. -/
theorem denoteCtors_mem {st : EStore} (hwf : StoreWF st) {n : NIdx} {nm : ConLeche.Name}
    (hn : denoteN st.ns n = some nm) :
    ∀ {cs : List (IConstantVal × Nat)} {csP : List (ConstantVal × Nat)},
      denoteCtors st cs = some csP →
      (n ∈ cs.map (·.1.name) ↔ nm ∈ csP.map (·.1.name)) := by
  obtain ⟨rk, hrk⟩ := hwf
  intro cs
  induction cs with
  | nil =>
    intro csP h
    simp only [denoteCtors, Option.some.injEq] at h
    subst h; simp
  | cons d ds ih =>
    intro csP h
    obtain ⟨dv, dn⟩ := d
    simp only [denoteCtors] at h
    cases hdv : Frontend.denoteCV st dv with
    | none => rw [hdv] at h; simp at h
    | some dP =>
    cases hds : denoteCtors st ds with
    | none => rw [hdv, hds] at h; simp at h
    | some dsP =>
    rw [hdv, hds] at h
    obtain rfl := (Option.some.inj h).symm
    have h2 := denoteCV_name hdv
    have e : n = dv.name ↔ nm = dP.name := by
      constructor
      · rintro rfl
        exact Option.some.inj (hn.symm.trans h2)
      · rintro rfl
        exact denoteN_inj hrk.nsWF hn h2
    simp only [List.map_cons, List.mem_cons, ih hds, e]

/-- con-leche: none — **a constructor list's names are distinct iff their
denotations are**: `denoteN` is injective on a well-formed store. -/
theorem denoteCtors_nodup {st : EStore} (hwf : StoreWF st) :
    ∀ {cs : List (IConstantVal × Nat)} {csP : List (ConstantVal × Nat)},
      denoteCtors st cs = some csP →
      ((cs.map (·.1.name)).Nodup ↔ (csP.map (·.1.name)).Nodup) := by
  intro cs
  induction cs with
  | nil =>
    intro csP h
    simp only [denoteCtors, Option.some.injEq] at h
    subst h; simp
  | cons c cs ih =>
    intro csP h
    obtain ⟨cv, n⟩ := c
    simp only [denoteCtors] at h
    cases hcv : Frontend.denoteCV st cv with
    | none => rw [hcv] at h; simp at h
    | some cP =>
    cases hrest : denoteCtors st cs with
    | none => rw [hcv, hrest] at h; simp at h
    | some restP =>
    rw [hcv, hrest] at h
    obtain rfl := (Option.some.inj h).symm
    simp only [List.map_cons, List.nodup_cons,
      denoteCtors_mem hwf (denoteCV_name hcv) hrest, ih hrest]

/-- con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:613-640 checkNative
**THE FIXPOINT ROUTE**, one of the two `checkIndDecl` dispatches to.  The
distinct names, the pass at the syntactic `is_rec`, and — where that reading
overshot — a second pass at the classification's verdict.

`sorry`: `nativeRawRec_spec`, `checkNativePass_spec` twice,
`nativeIsRec_spec` (closed), `checkNativeTail_spec`, and the `Nodup` guard,
which is `denoteN_inj` at the constructor names (`Bridge/Rel.lean`). -/
theorem checkNative_spec {μ : CheckMode} {env : Env} (fe : IFEnv)
    (hμ : μ.verifiedChecks = true) (hk : CoreSpec μ Arena.checkFuel) (henv : EnvWF env)
    (p₀ : Arena.NativeParts) (q₀ : ConLeche.NativeParts) :
    ISpec
      (fun s => CheckOK μ env fe s ∧ PartsRel s.store p₀ q₀ ∧
        denoteFEnv s.store fe = some env ∧ IFEnvCoh fe)
      (Arena.checkNative μ fe p₀)
      (fun s fe' => InstRel fe (fun env' => ∃ F,
        ConLeche.checkNative (ConLeche.fueledOps μ F) env q₀ = .ok env') s.store fe') := by
  intro s₀ s' r hpre hrun
  obtain ⟨hck, hp, hfe, hcoh⟩ := hpre
  simp only [Arena.checkNative] at hrun
  -- the front guard: distinct constructor names, on both sides
  obtain ⟨hnd, r1⟩ := AM.dunless_ok AM.Never.fail_any hrun
  replace r1 := AM.pure_bind_ok r1
  have hndP : (q₀.ctors.map (·.1.name)).Nodup :=
    (denoteCtors_nodup hck.state.wf hp.shape.ctors).mp hnd
  -- the flush
  obtain ⟨u, s₁, k1, z1⟩ := bindOk r1
  obtain ⟨hck₁, hi₁, hst₁⟩ := hck.toR.flush (μ := μ) k1
  have hp₁ : PartsRel s₁.store p₀ q₀ := by rw [hst₁]; exact hp
  have hfe₁ : denoteFEnv s₁.store fe = some env := by rw [hst₁]; exact hfe
  -- the syntactic verdict
  obtain ⟨rr, s₂, k2, z2⟩ := bindOk z1
  obtain ⟨p2, hrr⟩ := nativeRawRec_spec p₀ q₀ s₁ s₂ rr hck₁.state hp₁ k2
  have c2 := p2.toCore hck₁
  -- the first pass
  obtain ⟨qs, s₃, k3, z3⟩ := bindOk z2
  obtain ⟨i3, F₁, qP, settled, hF₁, hpass, hset, hinst₁, hck₃⟩ :=
    checkNativePass_spec fe hμ hk henv p₀ q₀ rr s₂ s₃ qs
      ⟨c2.ok, hp₁.ext c2.ext, denoteFEnv_ext c2.ext hfe₁, hcoh⟩ k3
  obtain ⟨henv₁, hTf, henv₂⟩ := checkNativePass_envWF henv hF₁
  obtain ⟨q, st⟩ := qs
  simp only at hpass hset hinst₁ hck₃ z3
  subst hset
  have i03 : InstStep s₀ s₃ := hi₁.trans (c2.toInst.trans i3)
  have hread₃ : ReadOK env fe s₃ := hck.toR.ofInst i03
  have hfe₃ : denoteFEnv s₃.store fe = some env := denoteFEnv_ext i03.ext hfe
  cases hs : st with
  | true =>
    rw [hs] at z3
    simp only [if_true] at z3
    obtain ⟨i4, hinst⟩ := checkNativeTail_spec fe hμ hk q qP henv₁ hTf henv₂
      (checkNativePass_hcs hF₁) s₃ s' r
      ⟨hck₃, hread₃, hpass, hfe₃, hinst₁⟩ z3
    refine ⟨i03.trans i4, hinst.imp ?_⟩
    rintro e ⟨F₂, hF₂⟩
    refine ⟨max F₁ F₂, ?_⟩
    have g₁ := checkNativePass_up (Nat.le_max_left F₁ F₂) hF₁
    have g₂ := checkNativeTail_up (Nat.le_max_right F₁ F₂) hF₂
    rw [hrr] at g₁
    rw [hs] at g₁
    simp only [ConLeche.checkNative, if_pos hndP, bind, Except.bind, g₁, if_true]
    exact g₂
  | false =>
    rw [hs] at z3
    simp only [Bool.false_eq_true, if_false] at z3
    -- the flush again, back at the entry index
    obtain ⟨u', s₄, k4, z4⟩ := bindOk z3
    obtain ⟨hck₄, hi₄, hst₄⟩ := hread₃.flush (μ := μ) k4
    have x04 : Ext s₀.store s₄.store := by rw [hst₄]; exact i03.ext
    -- the second pass, at the classified verdict
    obtain ⟨qs', s₅, k5, z5⟩ := bindOk z4
    rw [nativeIsRec_spec, hpass.p.kinds] at k5
    obtain ⟨i5, F₂, qP', settled', hF₂, hpass', hset', hinst₁', hck₅⟩ :=
      checkNativePass_spec fe hμ hk henv p₀ q₀ _ s₄ s₅ qs'
        ⟨hck₄, hp.ext x04, denoteFEnv_ext x04 hfe, hcoh⟩ k5
    obtain ⟨henv₁', hTf', henv₂'⟩ := checkNativePass_envWF henv hF₂
    obtain ⟨q', st'⟩ := qs'
    simp only at hpass' hset' hinst₁' hck₅ z5
    subst hset'
    obtain ⟨hs', z6⟩ := AM.dunless_ok AM.Never.fail_any z5
    replace z6 := AM.pure_bind_ok z6
    have i05 : InstStep s₀ s₅ := (i03.trans hi₄).trans i5
    obtain ⟨i6, hinst⟩ := checkNativeTail_spec fe hμ hk q' qP' henv₁' hTf' henv₂'
      (checkNativePass_hcs hF₂) s₅ s' r
      ⟨hck₅, hck.toR.ofInst i05, hpass', denoteFEnv_ext i05.ext hfe, hinst₁'⟩ z6
    refine ⟨i05.trans i6, hinst.imp ?_⟩
    rintro e ⟨F₃, hF₃⟩
    refine ⟨max F₁ (max F₂ F₃), ?_⟩
    have g₁ := checkNativePass_up (show F₁ ≤ max F₁ (max F₂ F₃) by omega) hF₁
    have g₂ := checkNativePass_up (show F₂ ≤ max F₁ (max F₂ F₃) by omega) hF₂
    have g₃ := checkNativeTail_up (show F₃ ≤ max F₁ (max F₂ F₃) by omega) hF₃
    rw [hrr, hs] at g₁
    simp only [ConLeche.checkNative, if_pos hndP, bind, Except.bind, g₁,
      Bool.false_eq_true, if_false, g₂, hs', if_true]
    exact g₃


/-! ## The fixpoint route's pure `EnvWF` (task #97-P3-Ind round 8, for `indDecl_envWF`)

con-leche proves the well-formedness of the environment an inductive block
leaves only inside its model construction and its cached bridge; the V-free
facts are all public (`direct_sum_ind_wf`, `envWF_consSumCtors`,
`direct_fix_rec_wf`, `direct_table_wf`), and these lemmas assemble them along
the pure route. -/

/-- con-leche: ConLeche/Verify/Cached/BridgeCSDecl.lean:329 checkNativeTailS_run
(its `EnvWF` half, pure) — **the install after the pass leaves a well-formed
environment**: the recursor's cons (`direct_fix_rec_wf`) at the
constructors' conses, then the table (`direct_table_wf`). -/
theorem checkNativeTail_envWF {μ : CheckMode} {F : Nat} {env e : Env}
    {q : ConLeche.NativePass Env}
    (henv₂ : EnvWF (ConLeche.consSumCtors q.p.nP q.ctorsA q.env₁))
    (h : ConLeche.checkNativeTail (ConLeche.fueledOps μ F) env q = .ok e) : EnvWF e := by
  have hthrow : ∀ {α : Type} {er : ConLeche.CheckError} {a : α},
      (throw er : CheckM α) = .ok a → False := by
    intro α er a h; simp [throw, throwThe, MonadExceptOf.throw] at h
  unfold ConLeche.checkNativeTail at h
  by_cases hg : (q.p.large && !q.p.resSort.isNeverZero && decide (2 ≤ q.p.ctors.length)) = true
  · rw [if_pos hg] at h
    obtain ⟨_, h1, -⟩ := ConLeche.exceptBind_ok h
    exact (hthrow h1).elim
  rw [if_neg hg] at h
  obtain ⟨tq, -, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨is, -, h⟩ := ConLeche.exceptBind_ok h
  by_cases hk : ConLeche.nativeFieldsOk env q.p.cvT.name q.p.cvT.levelParams q.p.nP q.p.nIdx
      q.ctorsA q.p.kinds = true
  · rw [if_pos hk] at h
    by_cases hr : ConLeche.nativeRulesOk q.p.cvR.name (q.p.cvR.levelParams.map .param) .never
        q.p.nP q.p.ctors.length q.ctorsA q.p.kinds q.p.rhss q.p.cvR.type = true
    · rw [if_pos hr] at h
      obtain ⟨v, hrec, h⟩ := ConLeche.exceptBind_ok h
      obtain ⟨cvRa, rhss⟩ := v
      dsimp only at h
      have hR := ConLeche.direct_fix_rec_wf henv₂ hrec
      unfold ConLeche.checkNativeTable at h
      split at h
      · by_cases hi : (q.p.nIdx == 0) = true
        · rw [if_pos hi] at h
          exact ConLeche.direct_table_wf hR h
        · rw [if_neg hi] at h
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h; exact hR
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h; exact hR
    · rw [if_neg hr] at h
      obtain ⟨_, h1, -⟩ := ConLeche.exceptBind_ok h
      exact (hthrow h1).elim
  · rw [if_neg hk] at h
    obtain ⟨_, h1, -⟩ := ConLeche.exceptBind_ok h
    exact (hthrow h1).elim

/-- con-leche: ConLeche/Verify/Cached/BridgeCSDecl.lean:433 checkNativeS_run (its
`EnvWF` half, pure) — **the fixpoint route leaves a well-formed environment**. -/
theorem checkNative_envWF {μ : CheckMode} {F : Nat} {env e : Env} {p₀ : ConLeche.NativeParts}
    (henv : EnvWF env)
    (h : ConLeche.checkNative (ConLeche.fueledOps μ F) env p₀ = .ok e) : EnvWF e := by
  unfold ConLeche.checkNative at h
  split at h
  · simp only [bind, Except.bind] at h
    split at h
    · exact nomatch h
    · rename_i v hpass
      obtain ⟨q, settled⟩ := v
      obtain ⟨-, -, henv₂⟩ := checkNativePass_envWF henv hpass
      simp only at h
      split at h
      · exact checkNativeTail_envWF henv₂ h
      · split at h
        · exact nomatch h
        · rename_i v' hpass'
          obtain ⟨q', settled'⟩ := v'
          obtain ⟨-, -, henv₂'⟩ := checkNativePass_envWF henv hpass'
          simp only at h
          split at h
          · exact checkNativeTail_envWF henv₂' h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

end ConRon.Bridge.Inductives

/-
# `ConRon.Refine2.Modular.ReachGo` — `modular/reach.rs`: the capture check, the clash rule, the worklist

**Task #166, Theorem 2.**  The reach's functions that read through its caches against their
twins (`Arena/Modular/Reach.lean`).  Each claims its accept (`ACS`): the Rust's `Ok`, with its
final state and caches, is a run of the twin in related states, the caches related
(`ReachCacheRel`), the answers related.

**The parts' reads** (`stmt_at`, `priv_spot`, `locate`, `look_of`, `read_record`) are taken
as the hypothesis `PartsSpec`: their accepts in the same form (sibling P's `ReachParts`
proves them).
-/
import ConRon.Refine2.Modular.ReachWork
import ConRon.Refine2.Modular.ReachParts
import ConRon.Refine2.Modular.ReachCheck
import ConRon.Refine2.Modular.ReachFuel

open Aeneas Aeneas.Std Result
open ConRon.Generated
open frontend.modular.reach

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

namespace ConRon.Refine2.Modular

open ConRon.Arena
open ConRon.Refine2.Frontend.Olean
open ConRon.Refine.HashMap2 (Inv toFun)

section reads
variable {F : Type} {inst : frontend.olean.files.OleanFs F} {fsv : F} {fs : Arena.Frontend.Olean.OleanFs}
  {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier} {sp : frontend.olean.files.Roots}

/-! ## The parts' reads, as a hypothesis -/

/-- **The accepts of the parts' reads** the capture check and the worklist call, in `ACS` form:
a copy's statement and kind (`stmt_at`), its private copy (`priv_spot`), a search
(`locate`), a part's lookup (`look_of`), a record read (`read_record`). -/
structure PartsSpec (inst : frontend.olean.files.OleanFs F) (fsv : F) (fs : Arena.Frontend.Olean.OleanFs)
    (pk : frontend.olean.spec.OleanPins) (pers : arena.store.PersTier) (sp : frontend.olean.files.Roots) :
    Prop where
  stmtAt : ∀ (st : arena.monad.AState) (lst : AState) (c : frontend.modular.reach.ReachCache)
      (C : Modular.ReachCache) (s : frontend.modular.reach.Spot), ReachCacheRel c C →
    ACS pers (fun a c' b => ReachCacheRel c' b.1 ∧ InfoRel a b.2) st lst
      (stmt_at inst fsv pk pers st sp c s) (Modular.stmtAt fs (absPins pk) (absRoots sp) C (absSpot s))
  privSpot : ∀ {env wr own E}, ReachEnvRel env wr own E → ∀ (st : arena.monad.AState) (lst : AState)
      (c : frontend.modular.reach.ReachCache) (C : Modular.ReachCache) (s : frontend.modular.reach.Spot),
      ReachCacheRel c C →
    ACS pers (fun a c' b => ReachCacheRel c' b.1 ∧ absSpot a = b.2) st lst
      (priv_spot inst fsv pk pers st sp wr c s) (Modular.privSpot fs (absPins pk) (absRoots sp) E C (absSpot s))
  locate : ∀ {env wr own E}, ReachEnvRel env wr own E → ∀ (st : arena.monad.AState) (lst : AState)
      (c : frontend.modular.reach.ReachCache) (C : Modular.ReachCache) (h y : arena.handle.NIdx),
      ReachCacheRel c C →
    ACS pers (fun a c' b => ReachCacheRel c' b.1 ∧ a.map absSpot = b.2) st lst
      (locate inst fsv pk pers st sp wr c h y)
      (Modular.locate fs (absPins pk) (absRoots sp) E C (absNIdx h) (absNIdx y))
  lookOf : ∀ {env wr own E}, ReachEnvRel env wr own E → ∀ (st : arena.monad.AState) (lst : AState)
      (c : frontend.modular.reach.ReachCache) (C : Modular.ReachCache) (k : frontend.modular.reach.PartKey),
      ReachCacheRel c C →
    ACS pers (fun _ c' b => ReachCacheRel c' b) st lst
      (look_of inst fsv pk pers st sp wr c k) (Modular.lookOf fs (absPins pk) (absRoots sp) E C (absPartKey k))
  readRecord : ∀ {env wr own E}, ReachEnvRel env wr own E → ∀ (st : arena.monad.AState) (lst : AState)
      (c : frontend.modular.reach.ReachCache) (C : Modular.ReachCache) (x : arena.handle.NIdx),
      ReachCacheRel c C →
    ACS pers (fun a c' b => ReachCacheRel c' b.1 ∧ absIDeclaration a.1 = b.2.1 ∧ absNIdx a.2 = b.2.2) st lst
      (read_record inst fsv pk pers st sp wr c x)
      (Modular.readRecord fs (absPins pk) (absRoots sp) E C (absNIdx x))

/-! ## Small facts -/

theorem nidx_eq2_eq {a b : arena.handle.NIdx} {o : Bool}
    (h : arena.handle.NIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = ok o) :
    o = (absNIdx a == absNIdx b) := by
  rw [nidx_eq2 a b o trivial trivial h]
  by_cases e : a = b
  · subst e; simp
  · simp only [e, decide_false]
    exact (beq_eq_false_iff_ne.mpr fun he => e (absNIdx_inj he)).symm

theorem eidx_eq2_eq {a b : arena.handle.EIdx} {o : Bool}
    (h : arena.handle.EIdx.Insts.Con_ron_coreRonHashmapEq2.eq2 a b = ok o) :
    o = (absEIdx a == absEIdx b) := by
  rw [eidx_eq2 a b o trivial trivial h]
  by_cases e : a = b
  · subst e; simp
  · simp only [e, decide_false]
    exact (beq_eq_false_iff_ne.mpr fun he => e (absEIdx_inj he)).symm

/-- `nameText` reads nothing and cannot fail. -/
theorem nameText_run (h : NIdx) (lst : AState) :
    ∃ t, (Frontend.nameText h).run lst = .ok (t, lst) := by
  cases hd : denoteN lst.store.ns h with
  | some x => exact ⟨toString x, by unfold Frontend.nameText; simp [hd]; rfl⟩
  | none => exact ⟨"?", by unfold Frontend.nameText; simp [hd]; rfl⟩

/-- `captureWhat` reads nothing and cannot fail. -/
theorem captureWhat_run (h y : NIdx) (lst : AState) :
    ∃ t, (Modular.captureWhat h y).run lst = .ok (t, lst) := by
  obtain ⟨t1, h1⟩ := nameText_run y lst
  obtain ⟨t2, h2⟩ := nameText_run h lst
  refine ⟨s!"name capture at {t1}, read by module {t2}", ?_⟩
  unfold Modular.captureWhat
  rw [am_bind_ok h1, am_bind_ok h2]
  rfl

theorem absLevel_private {l : frontend.olean.view.OLeanLevel} {i : Std.U64}
    (h : level_index l = ok i) : (i = 2#u64) ↔ (absLevel l = .private) := by
  have := level_index_val h
  cases l <;> simp only [levelIdx] at this <;> simp only [absLevel] <;> constructor <;> intro hh <;>
    first | trivial | (apply UScalar.eq_of_val_eq; simp [this]) | (subst hh; simp at this)

/-! ## A copy's proof flag -/

/-- **`proof_status` is `proofStatus`.** -/
theorem proof_status_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) {st lst} {c : frontend.modular.reach.ReachCache} {C : Modular.ReachCache}
    (hc : ReachCacheRel c C) (s : frontend.modular.reach.Spot)
    {k : frontend.olean.spec.CKindF arena.handle.NIdx Unit} {k' : ConLeche.Frontend.Olean.CKindF NIdx Unit}
    (hk : KindNamesRel k k') :
    ACS pers (fun a c' b => ReachCacheRel c' b.1 ∧ absProofStatus a = b.2) st lst
      (proof_status inst fsv pk pers st sp wr c s k)
      (Modular.proofStatus fs (absPins pk) (absRoots sp) E C (absSpot s) k') := by
  intro hrel hinv a st' c' h
  rw [proof_status.eq_def] at h
  cases k <;> cases k' <;> simp only [KindNamesRel, KindRel] at hk
  case Ax.ax u u' =>
    peel h as i, hi
    have ep := absLevel_private hi
    unfold Modular.proofStatus
    by_cases c2 : i = 2#u64
    · rw [ite_eq_left c2] at h
      have e := Result.ok_injective h
      simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      have hp : absLevel s.part.level = .private := ep.mp c2
      refine ⟨(C, .infer), lst, ?_, ⟨hc, rfl⟩, hrel, hinv⟩
      simp [hp]; rfl
    · rw [ite_eq_right c2] at h
      have hp : ¬ absLevel s.part.level = .private := fun e => c2 (ep.mpr e)
      peel h as q, hq
      obtain ⟨r, st1, c1⟩ := q
      cases r with
      | Err e => cases Result.ok_injective h
      | Ok p =>
        dsimp only [Std.uncurry] at h
        obtain ⟨⟨C1, p'⟩, lst1, hx, ⟨hc1, hpp⟩, hrel1, hinv1⟩ := hP.privSpot he st lst c C s hc hrel hinv p st1 c1 hq
        simp only at hpp
        subst hpp
        have hb : ((absSpot s).part.level == .private) = false := by
          simp [hp]
        simp only [hb, Bool.false_eq_true, ↓reduceIte, pure_bind]
        rw [am_bind_ok hx]
        have tg : (absSpot p).pos.tag = p.pos.tag.val := rfl
        dsimp only
        rw [tg]
        by_cases t2 : p.pos.tag = 2#u64
        · rw [ite_eq_left t2] at h
          have e := Result.ok_injective h
          simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e
          obtain ⟨rfl, rfl, rfl⟩ := e
          exact ⟨_, lst1, by simp [t2]; rfl, ⟨hc1, rfl⟩, hrel1, hinv1⟩
        · rw [ite_eq_right t2] at h
          have t2' : p.pos.tag.val ≠ 2 := fun e => t2 (UScalar.eq_of_val_eq (by simpa using e))
          by_cases t013 : p.pos.tag = 0#u64 ∨ p.pos.tag = 1#u64 ∨ p.pos.tag = 3#u64
          · have t013' : p.pos.tag.val = 0 ∨ p.pos.tag.val = 1 ∨ p.pos.tag.val = 3 := by
              rcases t013 with e | e | e <;> (rw [e]; decide)
            have hI : a = .Infer ∧ st' = st1 ∧ c' = c1 := by
              rcases t013 with e | e | e <;> simp [e] at h <;>
                (obtain ⟨h1, h2, h3⟩ := h; exact ⟨h1.symm, h2.symm, h3.symm⟩)
            obtain ⟨rfl, rfl, rfl⟩ := hI
            refine ⟨(C1, .infer), lst1, ?_, ⟨hc1, rfl⟩, hrel1, hinv1⟩
            rcases t013' with e | e | e <;> simp [e] <;> rfl
          · simp only [not_or] at t013
            obtain ⟨t0, t1, t3⟩ := t013
            rw [ite_eq_right t0, ite_eq_right t1, ite_eq_right t3] at h
            have e := Result.ok_injective h
            simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e
            obtain ⟨rfl, rfl, rfl⟩ := e
            have t0' : p.pos.tag.val ≠ 0 := fun e => t0 (UScalar.eq_of_val_eq (by simpa using e))
            have t1' : p.pos.tag.val ≠ 1 := fun e => t1 (UScalar.eq_of_val_eq (by simpa using e))
            have t3' : p.pos.tag.val ≠ 3 := fun e => t3 (UScalar.eq_of_val_eq (by simpa using e))
            refine ⟨(C1, .no), lst1, ?_, ⟨hc1, rfl⟩, hrel1, hinv1⟩
            simp [t2', t0', t1', t3']; rfl
  all_goals
    have e := Result.ok_injective h
    simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    exact ⟨_, lst, rfl, ⟨hc, rfl⟩, hrel, hinv⟩

/-! ## The caches' lists -/

theorem ReachCacheRel.with_partners {c : frontend.modular.reach.ReachCache} {C : Modular.ReachCache}
    (hc : ReachCacheRel c C) {v : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx)}
    {A : Array (NIdx × NIdx)} (hv : v.val.map absNN = A.toList) :
    ReachCacheRel { c with partners := v } { C with partners := A } :=
  ⟨hc.tables, hc.looks, hc.parts, hc.recBlocks, hc.views, hc.located, hc.completed, hc.pending, hv,
    hc.searches⟩

theorem ReachCacheRel.push_pending {c : frontend.modular.reach.ReachCache} {C : Modular.ReachCache}
    (hc : ReachCacheRel c C) {x y} (hx : PendingRel x y) {v} (hv : alloc.vec.Vec.push c.pending x = ok v) :
    ReachCacheRel { c with pending := v } { C with pending := C.pending.push y } := by
  refine ⟨hc.tables, hc.looks, hc.parts, hc.recBlocks, hc.views, hc.located, hc.completed, ?_,
    hc.partners, hc.searches⟩
  rw [ConRon.Refine.vec_push_val hv, Array.toList_push]
  exact List.rel_append hc.pending (List.Forall₂.cons hx .nil)

/-- A Rust tail that only fails. -/
macro "err_peel" h:ident : tactic => `(tactic| (repeat (peel $h:ident as _, _)) <;> cases Result.ok_injective $h:ident)

/-! ## Two copies agree -/

/-- **`agree_check` is `agreeCheck`.** -/
theorem agree_check_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) {st lst} {c : frontend.modular.reach.ReachCache} {C : Modular.ReachCache}
    (hc : ReachCacheRel c C) (h y : arena.handle.NIdx) (s1 s2 : frontend.modular.reach.Spot) :
    ACS pers (fun _ c' b => ReachCacheRel c' b) st lst
      (agree_check inst fsv pk pers st sp wr c h y s1 s2)
      (Modular.agreeCheck fs (absPins pk) (absRoots sp) E C (absNIdx h) (absNIdx y) (absSpot s1) (absSpot s2)) := by
  intro hrel hinv a st' c' hr
  rw [agree_check] at hr
  peel hr as b, hb
  have eb := nidx_eq2_eq hb
  unfold Modular.agreeCheck
  by_cases cb : b = true
  · rw [ite_eq_left cb] at hr
    have e := Result.ok_injective hr
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl⟩ := e
    have hm : ((absSpot s1).part.mod == (absSpot s2).part.mod) = true := by
      rw [cb] at eb; simpa using eb.symm
    simp only [hm, ↓reduceIte]
    exact ⟨C, lst, rfl, hc, hrel, hinv⟩
  · rw [ite_eq_right cb] at hr
    have hm : ((absSpot s1).part.mod == (absSpot s2).part.mod) = false := by
      have : b = false := by simpa using cb
      rw [this] at eb; simpa using eb.symm
    by_cases cs : s2.pos.skipped = true
    · rw [ite_eq_left cs] at hr
      err_peel hr
    · rw [ite_eq_right cs] at hr
      have hs' : (absNamePosition s2.pos).skipped = false := by simpa [absNamePosition] using cs
      peel hr as q1, hq1
      obtain ⟨r1, st1, c1⟩ := q1
      cases r1 with
      | Err e => cases Result.ok_injective hr
      | Ok p1 =>
      obtain ⟨⟨C1, cv1', k1'⟩, lst1, hx1, ⟨hc1, hcv1, hk1⟩, hrel1, hinv1⟩ :=
        hP.stmtAt st lst c C s1 hc hrel hinv p1 st1 c1 hq1
      obtain ⟨cv1, k1⟩ := p1
      simp only at hcv1 hk1
      subst hcv1
      dsimp only [Std.uncurry] at hr
      peel hr as q2, hq2
      obtain ⟨r2, st2, c2⟩ := q2
      cases r2 with
      | Err e => cases Result.ok_injective hr
      | Ok p2 =>
      obtain ⟨⟨C2, cv2', k2'⟩, lst2, hx2, ⟨hc2, hcv2, hk2⟩, hrel2, hinv2⟩ :=
        hP.stmtAt st1 lst1 c1 C1 s2 hc1 hrel1 hinv1 p2 st2 c2 hq2
      obtain ⟨cv2, k2⟩ := p2
      simp only at hcv2 hk2
      subst hcv2
      dsimp only [Std.uncurry] at hr
      peel hr as b1, hb1
      have eb1 := nidx_list_eq_abs hb1
      by_cases c1' : b1 = true
      swap
      · rw [ite_eq_right c1'] at hr; err_peel hr
      rw [ite_eq_left c1'] at hr
      peel hr as b2, hb2
      have eb2 := eidx_eq2_eq hb2
      by_cases c2' : b2 = true
      swap
      · rw [ite_eq_right c2'] at hr; err_peel hr
      rw [ite_eq_left c2'] at hr
      have hlp : ((absStmtRec cv1).levelParams == (absStmtRec cv2).levelParams &&
          (absStmtRec cv1).type == (absStmtRec cv2).type) = true := by
        rw [c1'] at eb1; rw [c2'] at eb2
        simp only [absStmtRec_levelParams, absStmtRec_type, ← eb1, ← eb2, Bool.and_self]
      peel hr as q3, hq3
      obtain ⟨r3, st3, c3⟩ := q3
      cases r3 with
      | Err e => cases Result.ok_injective hr
      | Ok p3 =>
      obtain ⟨⟨C3, ps1⟩, lst3, hx3, ⟨hc3, hps1⟩, hrel3, hinv3⟩ :=
        proof_status_ok hP he hc2 s1 hk1 hrel2 hinv2 p3 st3 c3 hq3
      simp only at hps1
      subst hps1
      dsimp only [Std.uncurry] at hr
      peel hr as q4, hq4
      obtain ⟨r4, st4, c4⟩ := q4
      cases r4 with
      | Err e => cases Result.ok_injective hr
      | Ok p4 =>
      obtain ⟨⟨C4, ps2⟩, lst4, hx4, ⟨hc4, hps2⟩, hrel4, hinv4⟩ :=
        proof_status_ok hP he hc3 s2 hk2 hrel3 hinv3 p4 st4 c4 hq4
      simp only at hps2
      subst hps2
      dsimp only [Std.uncurry] at hr
      peel hr as b3, hb3
      have eb3 := status_is_eq hb3
      by_cases c3' : b3 = true
      · rw [ite_eq_left c3'] at hr; err_peel hr
      rw [ite_eq_right c3'] at hr
      peel hr as b4, hb4
      have eb4 := status_is_eq hb4
      by_cases c4' : b4 = true
      · rw [ite_eq_left c4'] at hr; err_peel hr
      rw [ite_eq_right c4'] at hr
      have hno : (Modular.statusIs (absProofStatus p3) false || Modular.statusIs (absProofStatus p4) false) = false := by
        rw [← eb3, ← eb4]; simp_all
      peel hr as q5, hq5
      obtain ⟨r5, st5, v⟩ := q5
      cases r5 with
      | Err e => cases Result.ok_injective hr
      | Ok u =>
      obtain ⟨A5, lst5, hx5, hA5, hrel5, hinv5⟩ :=
        partner_reads_ok c4.partners s2.part.module cv2.ty hrel4 hinv4 st5 v hq5
      have eP : (c4.partners.val.map absNN).toArray = C4.partners := by rw [hc4.partners]
      rw [eP] at hx5
      have hc5 := hc4.with_partners hA5
      -- the twin's run up to the partners' reads
      simp only [hm, hs', Bool.false_eq_true, ↓reduceIte, pure_bind]
      rw [am_bind_ok hx1]
      dsimp only
      rw [am_bind_ok hx2]
      dsimp only
      simp only [hlp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [am_bind_ok hx3]
      dsimp only
      rw [am_bind_ok hx4]
      dsimp only
      simp only [hno, Bool.false_eq_true, ↓reduceIte]
      beta_reduce at hx5
      rw [absStmtRec_type, am_bind_ok hx5]
      peel hr as b5, hb5
      have eb5 := status_is_eq hb5
      by_cases c5 : b5 = true
      · rw [ite_eq_left c5] at hr
        have e := Result.ok_injective hr
        simp only [Prod.mk.injEq] at e
        obtain ⟨-, rfl, rfl⟩ := e
        have hy : (Modular.statusIs (absProofStatus p3) true || Modular.statusIs (absProofStatus p4) true) = true := by
          rw [← eb5, c5]; rfl
        refine ⟨{ C4 with partners := A5 }, lst5, ?_, hc5, hrel5, hinv5⟩
        simp only [hy, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rfl
      · rw [ite_eq_right c5] at hr
        peel hr as b6, hb6
        have eb6 := status_is_eq hb6
        by_cases c6 : b6 = true
        · rw [ite_eq_left c6] at hr
          have e := Result.ok_injective hr
          simp only [Prod.mk.injEq] at e
          obtain ⟨-, rfl, rfl⟩ := e
          have hy : (Modular.statusIs (absProofStatus p3) true || Modular.statusIs (absProofStatus p4) true) = true := by
            rw [← eb5, ← eb6, c6]; simp
          refine ⟨{ C4 with partners := A5 }, lst5, ?_, hc5, hrel5, hinv5⟩
          simp only [hy, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rfl
        · rw [ite_eq_right c6] at hr
          have hy : (Modular.statusIs (absProofStatus p3) true || Modular.statusIs (absProofStatus p4) true) = false := by
            rw [← eb5, ← eb6]; simp_all
          peel hr as w, -
          simp only [nidx_dup2_eq, Aeneas.Std.bind_ok] at hr
          peel hr as v1, hv1
          have e := Result.ok_injective hr
          simp only [Prod.mk.injEq] at e
          obtain ⟨-, rfl, rfl⟩ := e
          obtain ⟨t, ht⟩ := captureWhat_run (absNIdx h) (absNIdx y) lst5
          refine ⟨{ { C4 with partners := A5 } with
              pending := C4.pending.push (t, absNIdx y, absStmtRec cv1) }, lst5, ?_,
            hc5.push_pending (x := (w, y, cv1)) ⟨rfl, rfl⟩ hv1, hrel5, hinv5⟩
          simp only [hy, Bool.not_false, ↓reduceIte]
          rw [am_bind_ok ht]
          rfl

/-! ## The clash rule -/

theorem clash_statuses_loop_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E)
    (spots : alloc.vec.Vec (frontend.modular.reach.Spot × frontend.olean.spec.StmtRec ×
      frontend.olean.spec.CKindF arena.handle.NIdx Unit))
    (st : arena.monad.AState) (lst : AState) (c : frontend.modular.reach.ReachCache) (C : Modular.ReachCache)
    (hc : ReachCacheRel c C) (no yes : Bool) (i : Std.Usize)
    (L : List (Modular.Spot × Arena.Frontend.Olean.StmtRec × ConLeche.Frontend.Olean.CKindF NIdx Unit))
    (hL : List.Forall₂ SpotInfoRel (spots.val.drop i.val) L) :
    ACS pers (fun a c' b => ReachCacheRel c' b.1 ∧ a = b.2) st lst
      (clash_statuses_loop inst fsv pk pers st sp wr c spots no yes i)
      (Modular.clashStatuses fs (absPins pk) (absRoots sp) E C no yes L) := by
  intro hrel hinv a st' c' hr
  rw [clash_statuses_loop] at hr
  by_cases hlt : i < alloc.vec.Vec.len spots
  · rw [ite_eq_left hlt] at hr
    have hi := lt_len hlt
    rw [List.drop_eq_getElem_cons hi] at hL
    cases hL with
    | cons hxy hrest =>
    rename_i y L'
    peel hr as x, hx
    obtain ⟨_, rfl⟩ := vec_index_eq hx
    generalize spots.val[i.val] = xv at hr hxy
    obtain ⟨s, sr, cf⟩ := xv
    obtain ⟨y1, y2, y3⟩ := y
    obtain ⟨hs, -, hk⟩ := hxy
    simp only at hs hk
    subst hs
    dsimp only [Std.uncurry] at hr
    peel hr as q, hq
    obtain ⟨r, st1, c1⟩ := q
    cases r with
    | Err e => cases Result.ok_injective hr
    | Ok p =>
    obtain ⟨⟨C1, ps⟩, lst1, hx1, ⟨hc1, hps⟩, hrel1, hinv1⟩ := proof_status_ok hP he hc s hk hrel hinv p st1 c1 hq
    simp only at hps
    subst hps
    peel hr as b, hb
    have eb := status_is_eq hb
    peel hr as no1, hno1
    have eno : no1 = (no || Modular.statusIs (absProofStatus p) false) := by
      rw [← eb]; cases b <;> cases Result.ok_injective hno1 <;> simp
    peel hr as b1, hb1
    have eb1 := status_is_eq hb1
    peel hr as yes1, hyes1
    have eyes : yes1 = (yes || Modular.statusIs (absProofStatus p) true) := by
      rw [← eb1]; cases b1 <;> cases Result.ok_injective hyes1 <;> simp
    peel hr as i2, hi2
    have hv2 := usize_succ_val hi2
    rw [← hv2] at hrest
    obtain ⟨b2, lst2, hx2, hR, hrel2, hinv2⟩ :=
      clash_statuses_loop_ok hP he spots st1 lst1 c1 C1 hc1 no1 yes1 i2 L' hrest hrel1 hinv1 a st' c' hr
    refine ⟨b2, lst2, ?_, hR, hrel2, hinv2⟩
    rw [Modular.clashStatuses, am_bind_ok hx1]
    dsimp only
    rw [← eno, ← eyes]
    exact hx2
  · rw [ite_eq_right hlt] at hr
    have e := Result.ok_injective hr
    simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    rw [List.drop_of_length_le (not_lt_len hlt)] at hL
    cases hL
    exact ⟨(C, no, yes), lst, rfl, ⟨hc, rfl⟩, hrel, hinv⟩
termination_by spots.val.length - i.val
decreasing_by have := lt_len hlt; omega

/-- **`clash_agree_one` is `clashAgreeOne`.** -/
theorem clash_agree_one_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) {st lst} {c : frontend.modular.reach.ReachCache} {C : Modular.ReachCache}
    (hc : ReachCacheRel c C) {cl : frontend.olean.index.Clash} {cl' : Arena.Frontend.Olean.Clash}
    (hcl : ClashRel cl cl') (hfit : ∀ x ∈ cl.copies.val, CopyFits x.1)
    {acc : alloc.vec.Vec arena.handle.NIdx} {A : Array NIdx} (hA : acc.val.map absNIdx = A.toList) :
    AStateRel₀ pers st lst → AStateInv pers st → ∀ st' c' acc',
      clash_agree_one inst fsv pk pers st sp wr c cl acc = ok (.Ok (), st', c', acc') →
      ∃ C' A' lst', (Modular.clashAgreeOne fs (absPins pk) (absRoots sp) E C cl' A).run lst = .ok ((C', A'), lst') ∧
        ReachCacheRel c' C' ∧ acc'.val.map absNIdx = A'.toList ∧
        AStateRel₀ pers st' lst' ∧ AStateInv pers st' := by
  intro hrel hinv st' c' acc' hr
  rw [clash_agree_one] at hr
  peel hr as spots, hspots
  have hS := clash_spots_eq he.wr hcl hfit hspots
  generalize hSP : Modular.clashSpots (absPins pk) E cl' = SP at hS
  peel hr as q, hq
  obtain ⟨r, st1, c1⟩ := q
  cases r with
  | Err e => cases Result.ok_injective hr
  | Ok p =>
  obtain ⟨⟨C1, no', yes'⟩, lst1, hx1, ⟨hc1, hp⟩, hrel1, hinv1⟩ :=
    clash_statuses_loop_ok hP he spots st lst c C hc false false 0#usize _ (by simpa using hS) hrel hinv p st1 c1 hq
  obtain ⟨no, yes⟩ := p
  simp only [Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  dsimp only [Std.uncurry] at hr
  unfold Modular.clashAgreeOne
  rw [hSP, am_bind_ok hx1]
  dsimp only
  by_cases cn : no = true
  · rw [ite_eq_left cn] at hr; err_peel hr
  rw [ite_eq_right cn] at hr
  have cn' : no = false := by simpa using cn
  simp only [cn', Bool.false_eq_true, ↓reduceIte]
  by_cases cy : yes = true
  · rw [ite_eq_left cy] at hr
    simp only [nidx_dup2_eq, Aeneas.Std.bind_ok] at hr
    peel hr as acc1, hacc1
    have e := Result.ok_injective hr
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl, rfl⟩ := e
    simp only [cy, ↓reduceIte]
    refine ⟨C1, A.push (absNIdx cl.name), lst1, by rw [hcl.name]; rfl, hc1, ?_, hrel1, hinv1⟩
    rw [ConRon.Refine.vec_push_val hacc1]; simp [hA]
  rw [ite_eq_right cy] at hr
  have cy' : yes = false := by simpa using cy
  simp only [cy', Bool.false_eq_true, ↓reduceIte]
  by_cases cl0 : alloc.vec.Vec.len spots > 0#usize
  · rw [ite_eq_left cl0] at hr
    have hl0 : 0 < spots.val.length := by
      have : (0#usize : Std.Usize).val < (alloc.vec.Vec.len spots).val := cl0
      simpa [vec_len_val] using this
    obtain ⟨x0, xs, hx0⟩ : ∃ x0 xs, spots.val = x0 :: xs := by
      cases h0 : spots.val with
      | nil => rw [h0] at hl0; simp at hl0
      | cons x0 xs => exact ⟨x0, xs, rfl⟩
    rw [hx0] at hS
    cases hS with
    | cons hxy hrest =>
    rename_i y0 ys
    peel hr as _, -
    peel hr as _, -
    peel hr as _, -
    peel hr as w, -
    simp only [nidx_dup2_eq, Aeneas.Std.bind_ok] at hr
    peel hr as x, hx
    obtain ⟨_, ex⟩ := vec_index_eq hx
    have ex' : x = x0 := by simpa [hx0] using ex
    subst ex'
    obtain ⟨xs1, xsr, xk⟩ := x
    dsimp only [Std.uncurry] at hr
    peel hr as sr1, hsr1
    cases stmt_rec_dup_eq hsr1
    peel hr as v2, hv2
    peel hr as acc1, hacc1
    have e := Result.ok_injective hr
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl, rfl⟩ := e
    obtain ⟨y1, y2, y3⟩ := y0
    obtain ⟨-, hy2, -⟩ := hxy
    simp only at hy2
    obtain ⟨t, ht⟩ := nameText_run cl'.name lst1
    refine ⟨{ C1 with pending := C1.pending.push (s!"two loaded modules store {t}", cl'.name, y2) },
      A.push cl'.name, lst1, ?_, ?_, ?_, hrel1, hinv1⟩
    · simp only [pure_bind]
      rw [am_bind_ok ht]
      rfl
    · rw [← hcl.name]
      exact hc1.push_pending ⟨rfl, hy2.symm⟩ hv2
    · rw [ConRon.Refine.vec_push_val hacc1, ← hcl.name]; simp [hA]
  · rw [ite_eq_right cl0] at hr
    have e := Result.ok_injective hr
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl, rfl⟩ := e
    have hl0 : spots.val.length = 0 := by
      have : ¬ (0#usize : Std.Usize).val < (alloc.vec.Vec.len spots).val := cl0
      simpa [vec_len_val] using this
    rw [List.length_eq_zero_iff.mp hl0] at hS
    cases hS
    exact ⟨C1, A, lst1, rfl, hc1, hA, hrel1, hinv1⟩

theorem clash_agree_loop_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) (cls : alloc.vec.Vec frontend.olean.index.Clash)
    (hfit : ∀ cl ∈ cls.val, ∀ x ∈ cl.copies.val, CopyFits x.1)
    (st : arena.monad.AState) (lst : AState) (c : frontend.modular.reach.ReachCache) (C : Modular.ReachCache)
    (hc : ReachCacheRel c C) (acc : alloc.vec.Vec arena.handle.NIdx) (A : Array NIdx)
    (hA : acc.val.map absNIdx = A.toList) (i : Std.Usize) (L : List Arena.Frontend.Olean.Clash)
    (hL : List.Forall₂ ClashRel (cls.val.drop i.val) L) :
    ACS pers (fun a c' b => ReachCacheRel c' b.1 ∧ a.val.map absNIdx = b.2.toList) st lst
      (clash_agree_loop inst fsv pk pers st sp wr c cls acc i)
      (Modular.clashAgree fs (absPins pk) (absRoots sp) E C L A) := by
  intro hrel hinv a st' c' hr
  rw [clash_agree_loop] at hr
  by_cases hlt : i < alloc.vec.Vec.len cls
  · rw [ite_eq_left hlt] at hr
    have hi := lt_len hlt
    rw [List.drop_eq_getElem_cons hi] at hL
    cases hL with
    | cons hxy hrest =>
    rename_i y L'
    peel hr as x, hx
    obtain ⟨_, rfl⟩ := vec_index_eq hx
    peel hr as q, hq
    obtain ⟨r, st1, c1, acc1⟩ := q
    cases r with
    | Err e => cases Result.ok_injective hr
    | Ok u =>
    obtain ⟨C1, A1, lst1, hx1, hc1, hA1, hrel1, hinv1⟩ :=
      clash_agree_one_ok hP he hc hxy (hfit _ (List.getElem_mem hi)) hA hrel hinv st1 c1 acc1 hq
    peel hr as i2, hi2
    have hv2 := usize_succ_val hi2
    rw [← hv2] at hrest
    obtain ⟨b2, lst2, hx2, hR, hrel2, hinv2⟩ :=
      clash_agree_loop_ok hP he cls hfit st1 lst1 c1 C1 hc1 acc1 A1 hA1 i2 L' hrest hrel1 hinv1 a st' c' hr
    refine ⟨b2, lst2, ?_, hR, hrel2, hinv2⟩
    rw [Modular.clashAgree, am_bind_ok hx1]
    exact hx2
  · rw [ite_eq_right hlt] at hr
    have e := Result.ok_injective hr
    simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    rw [List.drop_of_length_le (not_lt_len hlt)] at hL
    cases hL
    exact ⟨(C, A), lst, rfl, ⟨hc, hA⟩, hrel, hinv⟩
termination_by cls.val.length - i.val
decreasing_by have := lt_len hlt; omega

/-- **`clash_agree` is `clashAgree`**: the clash rule over the worker's clashes. -/
theorem clash_agree_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) (hfit : ClashesFit wr) {st lst}
    {c : frontend.modular.reach.ReachCache} {C : Modular.ReachCache} (hc : ReachCacheRel c C) :
    ACS pers (fun a c' b => ReachCacheRel c' b.1 ∧ a.val.map absNIdx = b.2.toList) st lst
      (clash_agree inst fsv pk pers st sp wr c wr.clashes)
      (Modular.clashAgree fs (absPins pk) (absRoots sp) E C E.wr.clashes.toList #[]) := by
  intro hrel hinv a st' c' hr
  rw [clash_agree] at hr
  exact clash_agree_loop_ok hP he wr.clashes hfit st lst c C hc _ #[] rfl 0#usize _
    (by simpa using he.wr.clashes) hrel hinv a st' c' hr

end reads

end ConRon.Refine2.Modular

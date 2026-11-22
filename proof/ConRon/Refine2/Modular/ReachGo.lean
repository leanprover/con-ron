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
variable {F : Type} {inst : frontend.checker_io.CheckerFs F} {fsv : F} {fs : Arena.Frontend.Olean.OleanFs}
  {pk : frontend.olean.spec.OleanPins} {pers : arena.store.PersTier} {sp : frontend.olean.files.Roots}

/-! ## The parts' reads, as a hypothesis -/

/-- **The accepts of the parts' reads** the capture check and the worklist call, in `ACS` form:
a copy's statement and kind (`stmt_at`), its private copy (`priv_spot`), a search
(`locate`), a part's lookup (`look_of`), a record read (`read_record`). -/
structure PartsSpec (inst : frontend.checker_io.CheckerFs F) (fsv : F) (fs : Arena.Frontend.Olean.OleanFs)
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

theorem ACS.mono {α β : Type} {pers : arena.store.PersTier}
    {R R' : α → frontend.modular.reach.ReachCache → β → Prop} {st lst m} {x : AM β}
    (h : ACS pers R st lst m x) (hR : ∀ a c b, R a c b → R' a c b) : ACS pers R' st lst m x := by
  intro hrel hinv a st' c' hm
  obtain ⟨b, lst', hx, hr, h1, h2⟩ := h hrel hinv a st' c' hm
  exact ⟨b, lst', hx, hR _ _ _ hr, h1, h2⟩

/-- **The parts' reads, from sibling P's `ReachParts`.** -/
theorem partsSpec_of (hfs : FsRel inst fsv fs) : PartsSpec inst fsv fs pk pers sp where
  stmtAt st lst _ _ s hc :=
    (stmt_at_refines (st := st) (lst := lst) (pk := pk) (pers := pers) (sp := sp) (s := s) hfs hc).mono
      fun _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2.symm, h3⟩
  privSpot he st lst _ _ s hc :=
    (priv_spot_refines (st := st) (lst := lst) (pk := pk) (sp := sp) (s := s) hfs he hc).mono
      fun _ _ _ ⟨h1, h2⟩ => ⟨h1, h2.symm⟩
  locate he st lst _ _ h y hc :=
    (locate_refines (st := st) (lst := lst) (pk := pk) (sp := sp) (hm := h) (y := y) hfs he hc).mono
      fun _ _ _ ⟨h1, h2⟩ => ⟨h1, h2.symm⟩
  lookOf he st lst _ _ k hc :=
    (look_of_refines (st := st) (lst := lst) (pk := pk) (sp := sp) (k := k) hfs he hc).mono
      fun _ _ _ h1 => h1
  readRecord he st lst _ _ x hc :=
    (read_record_refines (st := st) (lst := lst) (pk := pk) (sp := sp) (x := x) hfs he hc).mono
      fun _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, h2.symm, h3.symm⟩

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

/-! ## The capture check -/

theorem absLevel_exported {l : frontend.olean.view.OLeanLevel} {i : Std.U64}
    (h : level_index l = ok i) : (i = 0#u64) ↔ (absLevel l = .exported) := by
  have := level_index_val h
  cases l <;> simp only [levelIdx] at this <;> simp only [absLevel] <;> constructor <;> intro hh <;>
    first | trivial | (apply UScalar.eq_of_val_eq; simp [this]) | (subst hh; simp at this)

theorem ReachCacheRel.with_located {c : frontend.modular.reach.ReachCache} {C : Modular.ReachCache}
    (hc : ReachCacheRel c C) {y : arena.handle.NIdx} {p : frontend.modular.reach.Spot} {old m'}
    (hi : ron.hashmap2.HashMap2.insert hN eN c.located y p = ok (old, m')) :
    ReachCacheRel { c with located := m' } { C with located := C.located.insert (absNIdx y) (absSpot p) } :=
  ⟨hc.tables, hc.looks, hc.parts, hc.recBlocks, hc.views, hc.located.insert hi, hc.completed, hc.pending,
    hc.partners, hc.searches⟩

theorem ReachCacheRel.with_located_completed {c : frontend.modular.reach.ReachCache} {C : Modular.ReachCache}
    (hc : ReachCacheRel c C) {y h : arena.handle.NIdx} {p : frontend.modular.reach.Spot} {old m'}
    (hi : ron.hashmap2.HashMap2.insert hN eN c.located y p = ok (old, m')) {v}
    (hv : alloc.vec.Vec.push c.completed (y, h) = ok v) :
    ReachCacheRel { c with located := m', completed := v }
      { C with located := C.located.insert (absNIdx y) (absSpot p),
               completed := C.completed.push (absNIdx y, absNIdx h) } := by
  refine ⟨hc.tables, hc.looks, hc.parts, hc.recBlocks, hc.views, hc.located.insert hi, ?_, hc.pending,
    hc.partners, hc.searches⟩
  rw [ConRon.Refine.vec_push_val hv, Array.toList_push, List.map_append, hc.completed]
  rfl

/-- An importer's copy's load position fits a `usize`. -/
theorem importer_spot_fits {wr : frontend.olean.index.WorkerReads} {W : Arena.Frontend.Olean.WorkerReads}
    (hw : WorkerReadsRel wr W) {y : arena.handle.NIdx} {i : Std.U64} {s : frontend.modular.reach.Spot}
    (h : importer_spot pk wr y = ok (some (i, s))) : i.val ≤ Std.Usize.max := by
  rw [importer_spot] at h
  peel h as o0, ho0
  obtain ⟨-, hfit⟩ := hw.index.first.get_eq ho0
  cases o0 with
  | none => cases Result.ok_injective h
  | some cp =>
    have hcf := hfit cp rfl
    peel h as o1, -
    cases o1 with
    | none => cases Result.ok_injective h
    | some q =>
      peel h as _, -
      peel h as _, -
      peel h as _, -
      cases Result.ok_injective h
      exact hcf.1

/-- **`in_exported` is `inExported`.** -/
theorem in_exported_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) {st lst} {c : frontend.modular.reach.ReachCache} {C : Modular.ReachCache}
    (hc : ReachCacheRel c C) (m : arena.handle.NIdx) (lvl : frontend.olean.view.OLeanLevel) (y : arena.handle.NIdx) :
    ACS pers (fun a c' b => ReachCacheRel c' b.1 ∧ a = b.2) st lst
      (in_exported inst fsv pk pers st sp wr c m lvl y)
      (Modular.inExported fs (absPins pk) (absRoots sp) E C (absNIdx m) (absLevel lvl) (absNIdx y)) := by
  intro hrel hinv a st' c' hr
  rw [in_exported] at hr
  peel hr as i, hi
  have ei := absLevel_exported hi
  unfold Modular.inExported
  by_cases c0 : i = 0#u64
  · rw [ite_eq_left c0] at hr
    have e := Result.ok_injective hr
    simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    simp only [ei.mp c0, beq_self_eq_true, ↓reduceIte]
    exact ⟨(C, true), lst, rfl, ⟨hc, rfl⟩, hrel, hinv⟩
  · rw [ite_eq_right c0] at hr
    have hne : (absLevel lvl == .exported) = false := by
      simpa using fun e => c0 (ei.mpr e)
    simp only [hne, Bool.false_eq_true, ↓reduceIte, pure_bind]
    simp only [nidx_dup2_eq, Aeneas.Std.bind_ok] at hr
    peel hr as q, hq
    obtain ⟨r, st1, c1⟩ := q
    cases r with
    | Err e => cases Result.ok_injective hr
    | Ok u =>
    obtain ⟨C1, lst1, hx1, hc1, hrel1, hinv1⟩ := hP.lookOf he st lst c C _ hc hrel hinv u st1 c1 hq
    peel hr as r1, hr1
    cases r1 with
    | Err e => cases Result.ok_injective hr
    | Ok o =>
    have hl := look_at_eq hc1 hr1 lst1
    have e := Result.ok_injective hr
    simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    refine ⟨(C1, (o.map absNamePosition).isSome), lst1, ?_, ⟨hc1, by cases o <;> rfl⟩, hrel1, hinv1⟩
    simp only [absPartKey, absLevel] at hl hx1
    rw [am_bind_ok hx1, am_bind_ok hl]
    rfl

/-- **`capture_against` is `captureAgainst`.** -/
theorem capture_against_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) {st lst} {c : frontend.modular.reach.ReachCache} {C : Modular.ReachCache}
    (hc : ReachCacheRel c C) (h y : arena.handle.NIdx) (s1 : frontend.modular.reach.Spot) :
    ACS pers (fun _ c' b => ReachCacheRel c' b) st lst
      (capture_against inst fsv pk pers st sp wr c h y s1)
      (Modular.captureAgainst fs (absPins pk) (absRoots sp) E C (absNIdx h) (absNIdx y) (absSpot s1)) := by
  intro hrel hinv a st' c' hr
  rw [capture_against] at hr
  peel hr as q, hq
  obtain ⟨r, st1, c1⟩ := q
  cases r with
  | Err e => cases Result.ok_injective hr
  | Ok o =>
  obtain ⟨⟨C1, o'⟩, lst1, hx1, ⟨hc1, ho⟩, hrel1, hinv1⟩ := hP.locate he st lst c C h y hc hrel hinv o st1 c1 hq
  simp only at ho
  subst ho
  cases o with
  | none => err_peel hr
  | some s2 =>
  obtain ⟨b, lst2, hx2, hb, hrel2, hinv2⟩ := agree_check_ok hP he hc1 h y s1 s2 hrel1 hinv1 a st' c' hr
  refine ⟨b, lst2, ?_, hb, hrel2, hinv2⟩
  unfold Modular.captureAgainst
  rw [am_bind_ok hx1]
  exact hx2

/-- **`capture_one` is `captureOne`**: the capture check of one read, and the completion of a name
the index lacks. -/
theorem capture_one_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) {st lst} {c : frontend.modular.reach.ReachCache} {C : Modular.ReachCache}
    (hc : ReachCacheRel c C) (h y : arena.handle.NIdx) :
    ACS pers (fun _ c' b => ReachCacheRel c' b) st lst
      (capture_one inst fsv pk pers st sp wr own env c h y)
      (Modular.captureOne fs (absPins pk) (absRoots sp) E C (absNIdx h) (absNIdx y)) := by
  intro hrel hinv a st' c' hr
  rw [capture_one] at hr
  peel hr as b, hb
  have eb := SetRel.contains_key nidx_eq2 he.own hb
  by_cases cb : b = true
  · rw [ite_eq_left cb] at hr; err_peel hr
  rw [ite_eq_right cb] at hr
  have hown : E.own.contains (absNIdx y) = false := by rw [← eb]; simpa using cb
  unfold Modular.captureOne
  simp only [hown, Bool.false_eq_true, ↓reduceIte]
  peel hr as o, ho
  have eo := importer_spot_eq (pk := pk) he.wr ho
  rw [← eo]
  cases o with
  | some p =>
    obtain ⟨i, s1⟩ := p
    have hif := importer_spot_fits he.wr ho
    dsimp only [Std.uncurry] at hr
    simp only [Option.map_some]
    peel hr as b1, hb1
    have eb1 := nidx_eq2_eq hb1
    by_cases c1 : b1 = true
    · rw [ite_eq_left c1] at hr
      have e := Result.ok_injective hr
      simp only [Prod.mk.injEq] at e
      obtain ⟨-, rfl, rfl⟩ := e
      have hm : ((absSpot s1).part.mod == absNIdx h) = true := by rw [c1] at eb1; simpa using eb1.symm
      simp only [hm, ↓reduceIte]
      exact ⟨C, lst, rfl, hc, hrel, hinv⟩
    rw [ite_eq_right c1] at hr
    have hm : ((absSpot s1).part.mod == absNIdx h) = false := by
      have : b1 = false := by simpa using c1
      rw [this] at eb1; simpa using eb1.symm
    simp only [hm, Bool.false_eq_true, ↓reduceIte, pure_bind]
    peel hr as b2, hb2
    have eb2 := pub_has_eq he.wr he.fits (env := E) rfl hif hb2
    by_cases c2 : b2 = true
    · rw [ite_eq_left c2] at hr
      have hp : Modular.pubHas E (absNIdx h) i.val = true := by rw [← eb2]; exact c2
      simp only [hp, ↓reduceIte]
      peel hr as q, hq
      obtain ⟨r, st1, c1'⟩ := q
      cases r with
      | Err e => cases Result.ok_injective hr
      | Ok b3 =>
      obtain ⟨⟨C1, b3'⟩, lst1, hx1, ⟨hc1, hb3⟩, hrel1, hinv1⟩ :=
        in_exported_ok hP he hc s1.part.module s1.part.level y hrel hinv b3 st1 c1' hq
      simp only at hb3
      subst hb3
      rw [am_bind_ok hx1]
      dsimp only [Std.uncurry] at hr
      by_cases c3 : b3 = true
      · rw [ite_eq_left c3] at hr
        have e := Result.ok_injective hr
        simp only [Prod.mk.injEq] at e
        obtain ⟨-, rfl, rfl⟩ := e
        simp only [c3, ↓reduceIte]
        exact ⟨C1, lst1, rfl, hc1, hrel1, hinv1⟩
      · rw [ite_eq_right c3] at hr
        have c3' : b3 = false := by simpa using c3
        simp only [c3', Bool.false_eq_true, ↓reduceIte]
        exact capture_against_ok hP he hc1 h y s1 hrel1 hinv1 a st' c' hr
    · rw [ite_eq_right c2] at hr
      have hp : Modular.pubHas E (absNIdx h) i.val = false := by rw [← eb2]; simpa using c2
      simp only [hp, Bool.false_eq_true, ↓reduceIte]
      exact capture_against_ok hP he hc h y s1 hrel hinv a st' c' hr
  | none =>
    simp only [Option.map_none]
    peel hr as o1, ho1
    have eo1 := located_at_eq hc ho1
    rw [← eo1]
    cases o1 with
    | some s1 =>
      simp only [Option.map_some]
      peel hr as b1, hb1
      have eb1 := nidx_eq2_eq hb1
      by_cases c1 : b1 = true
      · rw [ite_eq_left c1] at hr
        have e := Result.ok_injective hr
        simp only [Prod.mk.injEq] at e
        obtain ⟨-, rfl, rfl⟩ := e
        have hm : ((absSpot s1).part.mod == absNIdx h) = true := by rw [c1] at eb1; simpa using eb1.symm
        simp only [hm, ↓reduceIte]
        exact ⟨C, lst, rfl, hc, hrel, hinv⟩
      rw [ite_eq_right c1] at hr
      have hm : ((absSpot s1).part.mod == absNIdx h) = false := by
        have : b1 = false := by simpa using c1
        rw [this] at eb1; simpa using eb1.symm
      simp only [hm, Bool.false_eq_true, ↓reduceIte, pure_bind]
      exact capture_against_ok hP he hc h y s1 hrel hinv a st' c' hr
    | none =>
      simp only [Option.map_none, pure_bind]
      peel hr as q, hq
      obtain ⟨r, st1, c1⟩ := q
      cases r with
      | Err e => cases Result.ok_injective hr
      | Ok o2 =>
      obtain ⟨⟨C1, o2'⟩, lst1, hx1, ⟨hc1, ho2⟩, hrel1, hinv1⟩ := hP.locate he st lst c C h y hc hrel hinv o2 st1 c1 hq
      simp only at ho2
      subst ho2
      rw [am_bind_ok hx1]
      cases o2 with
      | none => err_peel hr
      | some s =>
      peel hr as q2, hq2
      obtain ⟨r2, st2, c2⟩ := q2
      cases r2 with
      | Err e => cases Result.ok_injective hr
      | Ok p =>
      obtain ⟨⟨C2, p'⟩, lst2, hx2, ⟨hc2, hp'⟩, hrel2, hinv2⟩ :=
        hP.privSpot he st1 lst1 c1 C1 s hc1 hrel1 hinv1 p st2 c2 hq2
      simp only at hp'
      subst hp'
      simp only [Option.map_some]
      rw [am_bind_ok hx2]
      simp only [nidx_dup2_eq, Aeneas.Std.bind_ok] at hr
      peel hr as q3, hq3
      obtain ⟨old, hm⟩ := q3
      peel hr as v, hv
      have e := Result.ok_injective hr
      simp only [Prod.mk.injEq] at e
      obtain ⟨-, rfl, rfl⟩ := e
      exact ⟨_, lst2, rfl, hc2.with_located_completed hq3 hv, hrel2, hinv2⟩

/-! ## The names a record stores -/

/-- **`stored_name_ok` is `storedNameOk`.** -/
theorem stored_name_ok_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) {st lst} {c : frontend.modular.reach.ReachCache} {C : Modular.ReachCache}
    (hc : ReachCacheRel c C) (h n : arena.handle.NIdx) :
    ACS pers (fun _ c' b => ReachCacheRel c' b) st lst
      (stored_name_ok inst fsv pk pers st sp wr c h n)
      (Modular.storedNameOk fs (absPins pk) (absRoots sp) E C (absNIdx h) (absNIdx n)) := by
  intro hrel hinv a st' c' hr
  rw [stored_name_ok] at hr
  unfold Modular.storedNameOk
  peel hr as o, ho
  have eo := importer_spot_eq (pk := pk) he.wr ho
  rw [← eo]
  cases o with
  | some p =>
    obtain ⟨i, s1⟩ := p
    dsimp only [Std.uncurry] at hr
    simp only [Option.map_some]
    peel hr as b1, hb1
    have eb1 := nidx_eq2_eq hb1
    by_cases c1 : b1 = true
    · rw [ite_eq_left c1] at hr
      have e := Result.ok_injective hr
      simp only [Prod.mk.injEq] at e
      obtain ⟨-, rfl, rfl⟩ := e
      have hm : ((absSpot s1).part.mod == absNIdx h) = true := by rw [c1] at eb1; simpa using eb1.symm
      simp only [hm, ↓reduceIte]
      exact ⟨C, lst, rfl, hc, hrel, hinv⟩
    · rw [ite_eq_right c1] at hr; err_peel hr
  | none =>
    simp only [Option.map_none]
    peel hr as o1, ho1
    have eo1 := located_at_eq hc ho1
    rw [← eo1]
    cases o1 with
    | some s1 =>
      simp only [Option.map_some]
      peel hr as b1, hb1
      have eb1 := nidx_eq2_eq hb1
      by_cases c1 : b1 = true
      · rw [ite_eq_left c1] at hr
        have e := Result.ok_injective hr
        simp only [Prod.mk.injEq] at e
        obtain ⟨-, rfl, rfl⟩ := e
        have hm : ((absSpot s1).part.mod == absNIdx h) = true := by rw [c1] at eb1; simpa using eb1.symm
        simp only [hm, ↓reduceIte]
        exact ⟨C, lst, rfl, hc, hrel, hinv⟩
      · rw [ite_eq_right c1] at hr; err_peel hr
    | none =>
      simp only [Option.map_none]
      peel hr as k, hk
      obtain ⟨-, ek⟩ := priv_key_eq hk
      peel hr as q, hq
      obtain ⟨r, st1, c1⟩ := q
      cases r with
      | Err e => cases Result.ok_injective hr
      | Ok u =>
      obtain ⟨C1, lst1, hx1, hc1, hrel1, hinv1⟩ := hP.lookOf he st lst c C k hc hrel hinv u st1 c1 hq
      rw [ek] at hx1
      rw [am_bind_ok hx1]
      peel hr as r1, hr1
      cases r1 with
      | Err e => cases Result.ok_injective hr
      | Ok o2 =>
      have hl := look_at_eq hc1 hr1 lst1
      rw [ek] at hl
      rw [am_bind_ok hl]
      cases o2 with
      | none => err_peel hr
      | some q =>
      simp only [nidx_dup2_eq, Aeneas.Std.bind_ok] at hr
      peel hr as q3, hq3
      obtain ⟨old, hm⟩ := q3
      have e := Result.ok_injective hr
      simp only [Prod.mk.injEq] at e
      obtain ⟨-, rfl, rfl⟩ := e
      have := hc1.with_located hq3
      simp only [absSpot, ek] at this
      exact ⟨_, lst1, rfl, this, hrel1, hinv1⟩

theorem stored_names_ok_loop_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) (h : arena.handle.NIdx) (ns : alloc.vec.Vec arena.handle.NIdx)
    (st : arena.monad.AState) (lst : AState) (c : frontend.modular.reach.ReachCache) (C : Modular.ReachCache)
    (hc : ReachCacheRel c C) (i : Std.Usize) :
    ACS pers (fun _ c' b => ReachCacheRel c' b) st lst
      (stored_names_ok_loop inst fsv pk pers st sp wr c h ns i)
      (Modular.storedNamesOk fs (absPins pk) (absRoots sp) E (absNIdx h) C ((ns.val.drop i.val).map absNIdx)) := by
  intro hrel hinv a st' c' hr
  rw [stored_names_ok_loop] at hr
  by_cases hlt : i < alloc.vec.Vec.len ns
  · rw [ite_eq_left hlt] at hr
    have hi := lt_len hlt
    peel hr as x, hx
    obtain ⟨_, rfl⟩ := vec_index_eq hx
    peel hr as q, hq
    obtain ⟨r, st1, c1⟩ := q
    cases r with
    | Err e => cases Result.ok_injective hr
    | Ok u =>
    obtain ⟨C1, lst1, hx1, hc1, hrel1, hinv1⟩ := stored_name_ok_ok hP he hc h _ hrel hinv u st1 c1 hq
    peel hr as i2, hi2
    have hv2 := usize_succ_val hi2
    obtain ⟨b2, lst2, hx2, hR, hrel2, hinv2⟩ :=
      stored_names_ok_loop_ok hP he h ns st1 lst1 c1 C1 hc1 i2 hrel1 hinv1 a st' c' hr
    rw [hv2] at hx2
    refine ⟨b2, lst2, ?_, hR, hrel2, hinv2⟩
    rw [List.drop_eq_getElem_cons hi, List.map_cons, Modular.storedNamesOk, am_bind_ok hx1]
    exact hx2
  · rw [ite_eq_right hlt] at hr
    have e := Result.ok_injective hr
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl⟩ := e
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact ⟨C, lst, rfl, hc, hrel, hinv⟩
termination_by ns.val.length - i.val
decreasing_by have := lt_len hlt; omega

/-- **`stored_names_ok` is `storedNamesOk`.** -/
theorem stored_names_ok_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) {st lst} {c : frontend.modular.reach.ReachCache} {C : Modular.ReachCache}
    (hc : ReachCacheRel c C) (h : arena.handle.NIdx) (ns : alloc.vec.Vec arena.handle.NIdx) :
    ACS pers (fun _ c' b => ReachCacheRel c' b) st lst
      (stored_names_ok inst fsv pk pers st sp wr c h ns)
      (Modular.storedNamesOk fs (absPins pk) (absRoots sp) E (absNIdx h) C (ns.val.map absNIdx)) := by
  intro hrel hinv a st' c' hr
  simpa using stored_names_ok_loop_ok hP he h ns st lst c C hc 0#usize hrel hinv a st' c' hr

/-! ## Every read of a record, the partners' reads -/

theorem capture_all_loop_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) (h : arena.handle.NIdx) (ys : alloc.vec.Vec arena.handle.NIdx)
    (st : arena.monad.AState) (lst : AState) (c : frontend.modular.reach.ReachCache) (C : Modular.ReachCache)
    (hc : ReachCacheRel c C) (i : Std.Usize) :
    ACS pers (fun _ c' b => ReachCacheRel c' b) st lst
      (capture_all_loop inst fsv pk pers st sp wr own env c h ys i)
      (Modular.captureAll fs (absPins pk) (absRoots sp) E (absNIdx h) C ((ys.val.drop i.val).map absNIdx)) := by
  intro hrel hinv a st' c' hr
  rw [capture_all_loop] at hr
  by_cases hlt : i < alloc.vec.Vec.len ys
  · rw [ite_eq_left hlt] at hr
    have hi := lt_len hlt
    peel hr as x, hx
    obtain ⟨_, rfl⟩ := vec_index_eq hx
    peel hr as q, hq
    obtain ⟨r, st1, c1⟩ := q
    cases r with
    | Err e => cases Result.ok_injective hr
    | Ok u =>
    obtain ⟨C1, lst1, hx1, hc1, hrel1, hinv1⟩ := capture_one_ok hP he hc h _ hrel hinv u st1 c1 hq
    peel hr as i2, hi2
    have hv2 := usize_succ_val hi2
    obtain ⟨b2, lst2, hx2, hR, hrel2, hinv2⟩ :=
      capture_all_loop_ok hP he h ys st1 lst1 c1 C1 hc1 i2 hrel1 hinv1 a st' c' hr
    rw [hv2] at hx2
    refine ⟨b2, lst2, ?_, hR, hrel2, hinv2⟩
    rw [List.drop_eq_getElem_cons hi, List.map_cons, Modular.captureAll, am_bind_ok hx1]
    exact hx2
  · rw [ite_eq_right hlt] at hr
    have e := Result.ok_injective hr
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl⟩ := e
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact ⟨C, lst, rfl, hc, hrel, hinv⟩
termination_by ys.val.length - i.val
decreasing_by have := lt_len hlt; omega

/-- **`capture_all` is `captureAll`.** -/
theorem capture_all_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) {st lst} {c : frontend.modular.reach.ReachCache} {C : Modular.ReachCache}
    (hc : ReachCacheRel c C) (h : arena.handle.NIdx) (ys : alloc.vec.Vec arena.handle.NIdx) :
    ACS pers (fun _ c' b => ReachCacheRel c' b) st lst
      (capture_all inst fsv pk pers st sp wr own env c h ys)
      (Modular.captureAll fs (absPins pk) (absRoots sp) E (absNIdx h) C (ys.val.map absNIdx)) := by
  intro hrel hinv a st' c' hr
  simpa using capture_all_loop_ok hP he h ys st lst c C hc 0#usize hrel hinv a st' c' hr

theorem capture_pairs_loop_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) (ps : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx))
    (st : arena.monad.AState) (lst : AState) (c : frontend.modular.reach.ReachCache) (C : Modular.ReachCache)
    (hc : ReachCacheRel c C) (i : Std.Usize) :
    ACS pers (fun _ c' b => ReachCacheRel c' b) st lst
      (capture_pairs_loop inst fsv pk pers st sp wr own env c ps i)
      (Modular.capturePairs fs (absPins pk) (absRoots sp) E C ((ps.val.drop i.val).map absNN)) := by
  intro hrel hinv a st' c' hr
  rw [capture_pairs_loop] at hr
  by_cases hlt : i < alloc.vec.Vec.len ps
  · rw [ite_eq_left hlt] at hr
    have hi := lt_len hlt
    peel hr as x, hx
    obtain ⟨_, rfl⟩ := vec_index_eq hx
    rw [List.drop_eq_getElem_cons hi, List.map_cons]
    generalize ps.val[i.val] = xv at hr ⊢
    obtain ⟨n, n1⟩ := xv
    dsimp only [Std.uncurry] at hr
    peel hr as q, hq
    obtain ⟨r, st1, c1⟩ := q
    cases r with
    | Err e => cases Result.ok_injective hr
    | Ok u =>
    obtain ⟨C1, lst1, hx1, hc1, hrel1, hinv1⟩ := capture_one_ok hP he hc n n1 hrel hinv u st1 c1 hq
    peel hr as i2, hi2
    have hv2 := usize_succ_val hi2
    obtain ⟨b2, lst2, hx2, hR, hrel2, hinv2⟩ :=
      capture_pairs_loop_ok hP he ps st1 lst1 c1 C1 hc1 i2 hrel1 hinv1 a st' c' hr
    rw [hv2] at hx2
    refine ⟨b2, lst2, ?_, hR, hrel2, hinv2⟩
    rw [Modular.capturePairs, am_bind_ok hx1]
    exact hx2
  · rw [ite_eq_right hlt] at hr
    have e := Result.ok_injective hr
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl⟩ := e
    rw [List.drop_of_length_le (not_lt_len hlt)]
    exact ⟨C, lst, rfl, hc, hrel, hinv⟩
termination_by ps.val.length - i.val
decreasing_by have := lt_len hlt; omega

/-- **`capture_pairs` is `capturePairs`.** -/
theorem capture_pairs_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) {st lst} {c : frontend.modular.reach.ReachCache} {C : Modular.ReachCache}
    (hc : ReachCacheRel c C) (ps : alloc.vec.Vec (arena.handle.NIdx × arena.handle.NIdx)) :
    ACS pers (fun _ c' b => ReachCacheRel c' b) st lst
      (capture_pairs inst fsv pk pers st sp wr own env c ps)
      (Modular.capturePairs fs (absPins pk) (absRoots sp) E C (ps.val.map absNN)) := by
  intro hrel hinv a st' c' hr
  simpa using capture_pairs_loop_ok hP he ps st lst c C hc 0#usize hrel hinv a st' c' hr

/-! ## The worklist -/

/-- **`reach_log_add` is `ReachLog.add`.** -/
theorem reach_log_add_rel {l : frontend.modular.reach.ReachLog} {L : Modular.ReachLog} (hl : ReachLogRel l L)
    (d : arena.env.IDeclaration) (h : arena.handle.NIdx) (ns rd : alloc.vec.Vec arena.handle.NIdx) {l'}
    (hr : reach_log_add l d h ns rd = ok l') :
    ReachLogRel l' (L.add (absIDeclaration d) (absNIdx h) (absNIdxList ns) (absNIdxList rd)) := by
  rw [reach_log_add] at hr
  peel hr as q, hq
  obtain ⟨i, hm, v⟩ := q
  have hp := push_names_eq hl.seen hl.stack hq
  peel hr as hm1, hhm1
  have hs := set_add_all_eq hl.stored hhm1
  peel hr as v1, hv1
  peel hr as v2, hv2
  peel hr as v3, hv3
  cases Result.ok_injective hr
  refine ⟨hp.1, hs, ?_, ?_, ?_, hp.2⟩
  · rw [ConRon.Refine.vec_push_val hv1]; simp [hl.ctx, Modular.ReachLog.add]
  · rw [ConRon.Refine.vec_push_val hv2]; simp [hl.homes, Modular.ReachLog.add]
  · rw [ConRon.Refine.vec_push_val hv3]; simp [hl.reads, absNIdxList, Modular.ReachLog.add]

/-- **The accept of a worklist step** (`&mut ReachLog`, `&mut ReachCache` on the state): the
Rust's `Ok` is a run of the twin, the logs and the caches related. -/
def ACL (pers : arena.store.PersTier) (st : arena.monad.AState) (lst : AState)
    (m : Result (core.result.Result Unit kernel.core_types.CheckError × arena.monad.AState ×
      frontend.modular.reach.ReachLog × frontend.modular.reach.ReachCache))
    (x : AM (Modular.ReachLog × Modular.ReachCache)) : Prop :=
  AStateRel₀ pers st lst → AStateInv pers st → ∀ st' l' c', m = ok (.Ok (), st', l', c') →
    ∃ b lst', x.run lst = .ok (b, lst') ∧ ReachLogRel l' b.1 ∧ ReachCacheRel c' b.2 ∧
      AStateRel₀ pers st' lst' ∧ AStateInv pers st'

/-- **`reach_partners` is `reachPartners`.** -/
theorem reach_partners_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) {st lst} {l : frontend.modular.reach.ReachLog} {L : Modular.ReachLog}
    (hl : ReachLogRel l L) {c : frontend.modular.reach.ReachCache} {C : Modular.ReachCache}
    (hc : ReachCacheRel c C) :
    ACL pers st lst (reach_partners inst fsv pk pers st sp wr own env l c)
      (Modular.reachPartners fs (absPins pk) (absRoots sp) E L C) := by
  intro hrel hinv st' l' c' hr
  rw [reach_partners] at hr
  simp only [core.mem.replace] at hr
  have hc0 := hc.with_partners (v := alloc.vec.Vec.new (arena.handle.NIdx × arena.handle.NIdx))
    (A := #[]) rfl
  peel hr as q, hq
  obtain ⟨r, st1, c1⟩ := q
  cases r with
  | Err e => cases Result.ok_injective hr
  | Ok u =>
  obtain ⟨C1, lst1, hx1, hc1, hrel1, hinv1⟩ := capture_pairs_ok hP he hc0 c.partners hrel hinv u st1 c1 hq
  peel hr as v1, hv1
  have ev1 := pair_seconds_eq hv1
  peel hr as q2, hq2
  obtain ⟨i, hm, v2⟩ := q2
  have hp := push_names_eq hl.seen (StackRel.empty absNIdx l.stack) hq2
  have e := Result.ok_injective hr
  simp only [Prod.mk.injEq] at e
  obtain ⟨-, rfl, rfl, rfl⟩ := e
  unfold Modular.reachPartners
  rw [hc.partners] at hx1
  rw [am_bind_ok hx1]
  rw [ev1, hc.partners] at hp
  exact ⟨_, lst1, rfl, ⟨hp.1, hl.stored, hl.ctx, hl.homes, hl.reads, hp.2⟩, hc1, hrel1, hinv1⟩

theorem catchE_ok {α : Type} {x : AM α} {s s' : AState} {a : α} (h : x.run s = .ok (a, s')) :
    (Modular.catchE x).run s = Except.ok (Except.ok a, s') := by
  show (match x s with
    | Except.ok (a, s') => Except.ok (Except.ok a, s')
    | Except.error e => Except.ok (Except.error e, s)) = _
  rw [show x s = Except.ok (a, s') from h]

/-- **`reach_read` is `reachRead`**: a popped name's record read, checked and added. -/
theorem reach_read_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) {st lst} {l : frontend.modular.reach.ReachLog} {L : Modular.ReachLog}
    (hl : ReachLogRel l L) {c : frontend.modular.reach.ReachCache} {C : Modular.ReachCache}
    (hc : ReachCacheRel c C) (x : arena.handle.NIdx) :
    ACL pers st lst (reach_read inst fsv pk pers st sp wr own env l c x)
      (Modular.reachRead fs (absPins pk) (absRoots sp) E L C (absNIdx x)) := by
  intro hrel hinv st' l' c' hr
  rw [reach_read] at hr
  unfold Modular.reachRead
  peel hr as b, hb
  have eb := SetRel.contains_key nidx_eq2 hl.stored hb
  by_cases cb : b = true
  · rw [ite_eq_left cb] at hr
    have e := Result.ok_injective hr
    simp only [Prod.mk.injEq] at e
    obtain ⟨-, rfl, rfl, rfl⟩ := e
    have : L.stored.contains (absNIdx x) = true := by rw [← eb]; exact cb
    simp only [this, ↓reduceIte]
    exact ⟨(L, C), lst, rfl, hl, hc, hrel, hinv⟩
  rw [ite_eq_right cb] at hr
  have hsx : L.stored.contains (absNIdx x) = false := by rw [← eb]; simpa using cb
  simp only [hsx, Bool.false_eq_true, ↓reduceIte, pure_bind]
  peel hr as q1, hq1
  obtain ⟨r1, st1, c1⟩ := q1
  cases r1 with
  | Err e => cases Result.ok_injective hr
  | Ok p =>
  obtain ⟨⟨C1, d', h'⟩, lst1, hx1, ⟨hc1, hd, hh⟩, hrel1, hinv1⟩ :=
    hP.readRecord he st lst c C x hc hrel hinv p st1 c1 hq1
  obtain ⟨d, h⟩ := p
  simp only at hd hh
  subst hd hh
  rw [am_bind_ok hx1]
  dsimp only [Std.uncurry] at hr ⊢
  peel hr as q2, hq2
  obtain ⟨r2, st2⟩ := q2
  cases r2 with
  | Err e => cases Result.ok_injective hr
  | Ok ns =>
  obtain ⟨ns', lst2, hx2, hns, hrel2, hinv2⟩ := decl_names_ls hrel1 hinv1 d (.Ok ns) st2 hq2
  subst hns
  rw [am_bind_ok hx2]
  peel hr as b1, hb1
  have eb1 := ConRon.Refine2.Lockstep.PC1.nidx_vec_contains_ls ns x b1 hb1
  by_cases c1' : b1 = true
  swap
  · rw [ite_eq_right c1'] at hr; err_peel hr
  rw [ite_eq_left c1'] at hr
  have hcx : (absNIdxList ns).contains (absNIdx x) = true := by rw [← eb1]; exact c1'
  peel hr as b2, hb2
  have eb2 := any_stored_eq hl.stored hb2
  by_cases c2' : b2 = true
  · rw [ite_eq_left c2'] at hr; err_peel hr
  rw [ite_eq_right c2'] at hr
  have han : Modular.anyStored L.stored (absNIdxList ns) = false := by
    rw [absNIdxList, ← eb2]; simpa using c2'
  simp only [hcx, han, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  peel hr as q3, hq3
  obtain ⟨r3, st3⟩ := q3
  cases r3 with
  | Err e => cases Result.ok_injective hr
  | Ok rd =>
  obtain ⟨rd', lst3, hx3, hrd, hrel3, hinv3⟩ := record_reads_ls hrel2 hinv2 d (.Ok rd) st3 hq3
  subst hrd
  rw [am_bind_ok hx3]
  peel hr as q4, hq4
  obtain ⟨r4, st4, c2⟩ := q4
  cases r4 with
  | Err e => err_peel hr
  | Ok u4 =>
  obtain ⟨C2, lst4, hx4, hc2, hrel4, hinv4⟩ := capture_all_ok hP he hc1 h rd hrel3 hinv3 u4 st4 c2 hq4
  rw [absNIdxList, am_bind_ok (catchE_ok hx4)]
  peel hr as q5, hq5
  obtain ⟨r5, st5, c3⟩ := q5
  cases r5 with
  | Err e => cases Result.ok_injective hr
  | Ok u5 =>
  obtain ⟨C3, lst5, hx5, hc3, hrel5, hinv5⟩ := stored_names_ok_ok hP he hc2 h ns hrel4 hinv4 u5 st5 c3 hq5
  rw [absNIdxList, am_bind_ok hx5]
  peel hr as l1, hl1
  have hL1 := reach_log_add_rel hl d h ns rd hl1
  peel hr as q6, hq6
  obtain ⟨r6, st6, v⟩ := q6
  have e := Result.ok_injective hr
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e
  obtain ⟨A6, lst6, hx6, hA6, hrel6, hinv6⟩ := clash_partners_ok he.copies c3.partners ns hrel5 hinv5 st6 v hq6
  have eP : (c3.partners.val.map absNN).toArray = C3.partners := by rw [hc3.partners]
  rw [eP] at hx6
  beta_reduce at hx6
  rw [am_bind_ok hx6]
  exact ⟨_, lst6, rfl, hL1, hc3.with_partners hA6, hrel6, hinv6⟩

theorem fuel_pred {fuel fuel1 : Std.U64} (hf : ¬ fuel = 0#u64) (h : fuel - 1#u64 = ok fuel1) :
    fuel.val = fuel1.val + 1 := by
  have hv := ConRon.Refine.HashMap.uscalar_sub_eq h
  have l1 : (1#u64 : Std.U64).val = 1 := by decide
  rw [l1] at hv
  have : fuel.val ≠ 0 := fun e => hf (UScalar.eq_of_val_eq (by simpa using e))
  omega

/-- **`reach_go`'s loop is `reachGo`**, at the twin's fuel the Rust's. -/
theorem reach_go_loop_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) (fuel : Std.U64) (st : arena.monad.AState) (lst : AState)
    (l : frontend.modular.reach.ReachLog) (L : Modular.ReachLog) (hl : ReachLogRel l L)
    (c : frontend.modular.reach.ReachCache) (C : Modular.ReachCache) (hc : ReachCacheRel c C) :
    ACL pers st lst (reach_go_loop inst fsv pk pers st sp wr own env l c fuel)
      (Modular.reachGo fs (absPins pk) (absRoots sp) E fuel.val L C) := by
  intro hrel hinv st' l' c' hr
  rw [reach_go_loop] at hr
  rw [Modular.reachGo.eq_def]
  dsimp only
  by_cases hsp : l.sp > 0#usize
  · rw [ite_eq_left hsp] at hr
    by_cases hf : fuel = 0#u64
    · rw [ite_eq_left hf] at hr; err_peel hr
    rw [ite_eq_right hf] at hr
    peel hr as fuel1, hfuel1
    have hfv := fuel_pred hf hfuel1
    have hsp0 : ¬ l.sp = 0#usize := by
      intro e; rw [e] at hsp; exact absurd hsp (by decide)
    rw [ite_eq_right hsp0] at hr
    peel hr as i, hi
    obtain ⟨hlt, rest, hL, hrest⟩ := hl.stack.pop hsp hi
    peel hr as n, hn
    obtain ⟨_, rfl⟩ := vec_index_eq hn
    simp only [nidx_dup2_eq, Aeneas.Std.bind_ok] at hr
    peel hr as q, hq
    obtain ⟨r, st1, l1, c1⟩ := q
    cases r with
    | Err e => cases Result.ok_injective hr
    | Ok u =>
    have hl' : ReachLogRel { l with sp := i } { L with stack := rest } :=
      ⟨hl.seen, hl.stored, hl.ctx, hl.homes, hl.reads, hrest⟩
    obtain ⟨⟨L1, C1⟩, lst1, hx1, hl1, hc1, hrel1, hinv1⟩ :=
      reach_read_ok hP he hl' hc _ hrel hinv st1 l1 c1 hq
    obtain ⟨b2, lst2, hx2, hl2, hc2, hrel2, hinv2⟩ :=
      reach_go_loop_ok hP he fuel1 st1 lst1 l1 L1 hl1 c1 C1 hc1 hrel1 hinv1 st' l' c' hr
    refine ⟨b2, lst2, ?_, hl2, hc2, hrel2, hinv2⟩
    rw [hL, hfv]
    dsimp only
    rw [am_bind_ok hx1]
    exact hx2
  · rw [ite_eq_right hsp] at hr
    rw [hl.stack.nil_of_zero hsp]
    dsimp only
    have hlen : C.partners.size = c.partners.val.length := by
      rw [← Array.length_toList, ← hc.partners, List.length_map]
    by_cases hp : alloc.vec.Vec.len c.partners > 0#usize
    · rw [ite_eq_left hp] at hr
      have hne : C.partners.isEmpty = false := by
        have : (0#usize : Std.Usize).val < (alloc.vec.Vec.len c.partners).val := hp
        rw [vec_len_val] at this
        have h0 : (0#usize : Std.Usize).val = 0 := by decide
        rw [Bool.eq_false_iff, ne_eq, Array.isEmpty_iff_size_eq_zero]; omega
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      by_cases hf : fuel = 0#u64
      · rw [ite_eq_left hf] at hr; err_peel hr
      rw [ite_eq_right hf] at hr
      peel hr as fuel1, hfuel1
      have hfv := fuel_pred hf hfuel1
      have hsp0 : l.sp = 0#usize := by
        have : ¬ (0#usize : Std.Usize).val < l.sp.val := hsp
        apply UScalar.eq_of_val_eq; simp at this ⊢; omega
      rw [ite_eq_left hsp0] at hr
      peel hr as q, hq
      obtain ⟨r, st1, l1, c1⟩ := q
      cases r with
      | Err e => cases Result.ok_injective hr
      | Ok u =>
      obtain ⟨⟨L1, C1⟩, lst1, hx1, hl1, hc1, hrel1, hinv1⟩ :=
        reach_partners_ok hP he hl hc hrel hinv st1 l1 c1 hq
      obtain ⟨b2, lst2, hx2, hl2, hc2, hrel2, hinv2⟩ :=
        reach_go_loop_ok hP he fuel1 st1 lst1 l1 L1 hl1 c1 C1 hc1 hrel1 hinv1 st' l' c' hr
      refine ⟨b2, lst2, ?_, hl2, hc2, hrel2, hinv2⟩
      rw [hfv]
      dsimp only
      rw [am_bind_ok hx1]
      exact hx2
    · rw [ite_eq_right hp] at hr
      have e := Result.ok_injective hr
      simp only [Prod.mk.injEq] at e
      obtain ⟨-, rfl, rfl, rfl⟩ := e
      have he' : C.partners.isEmpty = true := by
        have : ¬ (0#usize : Std.Usize).val < (alloc.vec.Vec.len c.partners).val := hp
        rw [vec_len_val] at this
        have h0 : (0#usize : Std.Usize).val = 0 := by decide
        rw [Array.isEmpty_iff_size_eq_zero]; omega
      simp only [he', ↓reduceIte]
      exact ⟨(L, C), lst, rfl, hl, hc, hrel, hinv⟩
termination_by fuel.val
decreasing_by all_goals omega

/-- **`reach_go` is `reachGo`.** -/
theorem reach_go_ok (hP : PartsSpec inst fsv fs pk pers sp) {env wr own E}
    (he : ReachEnvRel env wr own E) {st lst} {l : frontend.modular.reach.ReachLog} {L : Modular.ReachLog}
    (hl : ReachLogRel l L) {c : frontend.modular.reach.ReachCache} {C : Modular.ReachCache}
    (hc : ReachCacheRel c C) (fuel : Std.U64) :
    ACL pers st lst (reach_go inst fsv pk pers st sp wr own env l c fuel)
      (Modular.reachGo fs (absPins pk) (absRoots sp) E fuel.val L C) :=
  reach_go_loop_ok hP he fuel st lst l L hl c C hc

/-! ## The reach -/

/-- A `HashMap2` keyed by names holds no more keys than the twin's map. -/
theorem nmapRel_len_le {V V' : Type} {A : V → V'} {m : ron.hashmap2.HashMap2 arena.handle.NIdx V}
    {s : Std.HashMap NIdx V'} (h : NMapRel A m s) {n : Std.Usize}
    (hl : ron.hashmap2.HashMap2.len m = ok n) : n.val ≤ s.size := by
  rw [(ConRon.Refine.HashMap2.len_refines h.inv hl).1]
  have hnd : (((ConRon.Refine.HashMap2.sl_v m).map Prod.fst).map absNIdx).Nodup :=
    h.inv.nodup.map absNIdx_inj
  have hsub : ((ConRon.Refine.HashMap2.sl_v m).map Prod.fst).map absNIdx ⊆ s.keys := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨k, ⟨p, hp, rfl⟩, rfl⟩ := hx
    have hne : toFun m p.1 ≠ none := by
      rw [toFun, Ne, ConRon.Refine.HashMap.lookupK_eq_none_iff]
      simpa using ⟨p.2, hp⟩
    have hg := h.get p.1
    rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_isSome_getElem?, ← hg]
    cases ht : toFun m p.1 with
    | none => exact absurd ht hne
    | some v => rfl
  have := (hnd.subperm hsub).length_le
  rw [Std.HashMap.length_keys, List.length_map, List.length_map] at this
  exact this

/-- **Theorem 2 of the reach** (`AS` form, on the whole state): the Rust's `reach` accepting is
the twin's `reach` accepting, with the `Reach` related (`pending` up to its messages). -/
theorem reach_refines (hfs : FsRel inst fsv fs)
    {m : arena.handle.NIdx} {wr : frontend.olean.index.WorkerReads} {W : Arena.Frontend.Olean.WorkerReads}
    (hw : WorkerReadsRel wr W)
    {own : ron.hashmap2.HashMap2 arena.handle.NIdx Bool} {O : Std.HashSet NIdx} (ho : NSet own O)
    {roots : alloc.vec.Vec arena.handle.NIdx} {st lst} :
    AStateRel₀ pers st lst → AStateInv pers st →
      LA pers ReachRel (reach inst fsv pk pers st sp m wr own roots) lst
        (Modular.reach fs (absPins pk) (absRoots sp) (absNIdx m) W O (roots.val.map absNIdx).toArray) := by
  intro hrel hinv a st' hr
  have hP : PartsSpec inst fsv fs pk pers sp := partsSpec_of hfs
  rw [reach] at hr
  simp only [nidx_dup2_eq, Aeneas.Std.bind_ok] at hr
  peel hr as hm, hhm
  have hcop := clash_copies_of_eq (pk := pk) hw hw.clashFits hhm
  let E : Modular.ReachEnv := { mod := absNIdx m, wr := W, own := O, copies := Modular.clashCopiesOf (absPins pk) W }
  have he : ReachEnvRel { module := m, copies := hm } wr own E := ⟨rfl, hw, hw.fits, ho, hcop⟩
  peel hr as c, hc0
  have hc := reach_cache_empty_rel hc0
  peel hr as q1, hq1
  obtain ⟨r1, st1, c1⟩ := q1
  cases r1 with
  | Err e => cases Result.ok_injective hr
  | Ok x =>
  obtain ⟨⟨C1, X⟩, lst1, hx1, ⟨hc1, hX⟩, hrel1, hinv1⟩ := clash_agree_ok hP he hw.clashFits hc hrel hinv x st1 c1 hq1
  peel hr as rs, hrs
  have ers := reach_roots_eq ho hrs
  peel hr as o, hoo
  obtain ⟨-, eo⟩ := first_unloaded_eq hw.index.first hoo
  cases o with
  | some i => err_peel hr
  | none =>
  peel hr as l, hl0
  have hl := reach_log_init_rel hl0
  peel hr as n1, hn1
  have en1 := nmapRel_len_le hw.index.first.rel hn1
  peel hr as i1, hi1
  have ei1 := cast_u64_val hi1
  peel hr as i3, hi3
  have ei3 := cast_u64_val hi3
  peel hr as i4, hi4
  have ei4 := ConRon.Refine.Nat.uadd_val hi4
  peel hr as i5, hi5
  have ei5 : i5.val = 2 ^ 24 := by
    have := (ConRon.Refine.Nat.ushiftLeftI_val hi5).2
    rw [this]; decide
  peel hr as fuel, hfuel
  have efuel := ConRon.Refine.Nat.uadd_val hfuel
  have hmore : W.index.more.size = wr.index.more.val.length := by
    rw [← Array.length_toList, ← hw.index.more, List.length_map]
  have hle : fuel.val ≤ W.index.first.size + W.index.more.size + (1 <<< 24) := by
    have h24 : (1 <<< 24 : Nat) = 2 ^ 24 := by decide
    rw [h24, hmore]
    have : (alloc.vec.Vec.len wr.index.more).val = wr.index.more.val.length := vec_len_val _
    omega
  peel hr as q2, hq2
  obtain ⟨r2, st2, l1, c2⟩ := q2
  cases r2 with
  | Err e => cases Result.ok_injective hr
  | Ok u =>
  obtain ⟨⟨L1, C2⟩, lst2, hx2, hl1, hc2, hrel2, hinv2⟩ :=
    reach_go_ok hP he hl hc1 fuel hrel1 hinv1 st2 l1 c2 hq2
  have hx2' := reachGo_mono fs (absPins pk) (absRoots sp) E fuel.val
    (W.index.first.size + W.index.more.size + (1 <<< 24) - fuel.val) _ _ _ _ hx2
  rw [Nat.add_sub_cancel' hle] at hx2'
  peel hr as q3, hq3
  obtain ⟨r3, st3⟩ := q3
  cases r3 with
  | Err e => cases Result.ok_injective hr
  | Ok o1 =>
  obtain ⟨O1, lst3, hx3, hO1, hrel3, hinv3⟩ := read_order_la hrel2 hinv2 l1.ctx l1.reads o1 st3 hq3
  have hfits : ∀ j ∈ o1.val, j.val ≤ Std.Usize.max := by
    intro j hj
    have hlt := readOrder_lt _ _ lst2 _ hx3 j.val (by rw [hO1]; exact List.mem_map_of_mem hj)
    have := vec_len_le_max l1.ctx
    simp [absIDeclL] at hlt
    omega
  have eC : L1.ctx = (absIDeclL l1.ctx).toArray := by
    apply Array.ext'; rw [← hl1.ctx]; rfl
  have eR : L1.reads = absRds l1.reads := by
    apply Array.ext'; rw [← hl1.reads]; simp [absRds]
  peel hr as q4, hq4
  obtain ⟨ctx, homes⟩ := q4
  obtain ⟨ectx, ehomes⟩ := in_read_order_eq hl1 hfits hq4
  have eO1 : O1 = (o1.val.map (·.val)).toArray := by apply Array.ext'; rw [hO1]
  dsimp only [Std.uncurry] at hr
  peel hr as q5, hq5
  obtain ⟨r5, st4⟩ := q5
  cases r5 with
  | Err e => cases Result.ok_injective hr
  | Ok u5 =>
  obtain ⟨_, lst4, hx4, -, hrel4, hinv4⟩ := validate_ctx_la hrel3 hinv3 ctx homes u5 st4 hq5
  peel hr as inf, hinf
  have einf := cast_u64_val hinf
  have e := Result.ok_injective hr
  simp only [Prod.mk.injEq, core.result.Result.Ok.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  refine ⟨(⟨(Modular.inReadOrder L1 O1).1, (Modular.inReadOrder L1 O1).2, C2.completed, C2.searches,
      C2.pending.size, C2.pending⟩ : Modular.Reach), lst4, ?_,
    ⟨(by apply Array.ext'; rw [eO1, ← ectx]; rfl), (by apply Array.ext'; rw [eO1, ← ehomes]; rfl),
      (by rw [hc2.completed]), hc2.searches.symm, ?_, hc2.pending⟩,
    hrel4, hinv4⟩
  · unfold Modular.reach
    rw [am_bind_ok hx1]
    dsimp only
    have eX : X = (x.val.map absNIdx).toArray := by apply Array.ext'; rw [← hX]
    have eo' : (rs.val.map absNIdx).find? (!W.index.first.contains ·) = none := by rw [← eo]; rfl
    rw [eX, ← ers, eo']
    dsimp only
    rw [am_bind_ok hx2']
    dsimp only
    rw [eC, eR, am_bind_ok hx3]
    have ev1 : (Modular.inReadOrder L1 O1).1.toList = absIDeclL ctx := by rw [eO1, ← ectx]; rfl
    have ev2 : (Modular.inReadOrder L1 O1).2 = (homes.val.map absNIdx).toArray := by
      apply Array.ext'; rw [eO1, ← ehomes]
    rw [ev1, ev2, am_bind_ok hx4]
    rfl
  · rw [einf, vec_len_val]
    exact (List.Forall₂.length_eq hc2.pending).symm

end reads

end ConRon.Refine2.Modular

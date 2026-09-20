/-
# Experiment D — the Aeneas model of the Rust against the pure `instantiate1`,
# in one layer

DESIGN §8.6's experiment D: the same conclusion as `C1 ∘ C2`, proved in a
single induction, with **no twin in between**.  Nothing in this file or in
`GenDenote.lean` mentions `MState`, `absState` or `mInstantiate1`.

What the round-2 report compares:

* **C1** is representation only and its proof is a program-to-program match;
  **C2** is denotation only and `mvcgen` closes it.  Each half can be read,
  and re-proved, without the other.
* **D** carries both at once.  Every arm of the induction does the `u32`
  arithmetic *and* the denotation step, and the proof cannot be split: the
  `app` arm below threads `GWF`, `GExt`, the memo invariant and the answer
  relation through the same four `Result` inversions that C1's `app` arm
  threads only the first two through.
* The one thing D does *not* get is `mvcgen`.  `Generated.instantiate1` is
  `Result`-valued with the state as a return value, so §8.6's `⦃s = s₀⦄`
  template does not apply: there is no monadic state for `mspec` to
  instantiate.  Experiment A's automation is available to C2 and to nothing
  else in this file.
-/
import ConRon.Arena.Spike.GenDenote

namespace ConRon.Arena.Spike

open ConLeche Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 4000000

/-- con-leche: none — the `Except`/`Result` bind at a value, reduced. -/
theorem D_ok_bind {α β : Type} (a : α) (f : α → Result β) :
    (Result.ok a) >>= f = f a := by simp

/-- con-leche: ConLeche/Verify/SimI.lean:244 SimAt — **the one-layer
postcondition**: everything the induction has to carry, in one place. -/
def DPost (ve : Expr) (d : Nat) (st : Generated.State) (h : U32)
    (st' : Generated.State) (r : U32) : Prop :=
  GWF st' ∧ GExt st st' ∧ Inst1MemoG ve st' ∧ Inst1AtG ve d st h st' r

/-! ## The two branching arms

The same split as `ExpC1.lean`'s, so that the two files are comparable line
for line — except that each arm here also carries the denotation. -/

/-- con-leche: none — the `app` arm of D. -/
theorem D_app_arm (ve : Expr) (v : U32) (n : Nat)
    (ih : ∀ (st st' : Generated.State) (fuel h d r : U32), GWF st → absU fuel ≤ n →
      Inst1MemoG ve st → DenotesG st v ve → DenotesSomeG st h →
      Generated.instantiate1 st v fuel h d = .ok (some r, st') →
      DPost ve d.val st h st' r)
    (st st' : Generated.State) (fuel h d r : U32) (hwf : GWF st) (m : Nat)
    (hm : absU fuel = m + 1) (hmn : m ≤ n) (hmemo : Inst1MemoG ve st)
    (hv : DenotesG st v ve) (hden : DenotesSomeG st h)
    (f a : U32) (hview : gViewApp st h = some (f, a))
    (hrun : (do
      let o1 ← Generated.memo_get st h d
      match o1 with
      | none => do
        let i ← fuel - 1#u32
        let (o2, st1) ← Generated.instantiate1 st v i f d
        match o2 with
        | none => Result.ok (none, st1)
        | some f2 => do
          let (o3, st2) ← Generated.instantiate1 st1 v i a d
          match o3 with
          | none => Result.ok (none, st2)
          | some a2 => do
            let (o4, st3) ← Generated.intern_app st2 f2 a2
            match o4 with
            | none => Result.ok (none, st3)
            | some rr => do
              let st4 ← Generated.memo_set st3 h d rr
              Result.ok (o4, st4)
      | some _ => Result.ok (o1, st)) = .ok (some r, st')) :
    DPost ve d.val st h st' r := by
  obtain ⟨o1, hm1, hm2⟩ := gmemo_get st h d
  rw [hm1, bind_tc_ok] at hrun
  cases o1 with
  | some rr =>
    dsimp only at hrun
    simp only [Result.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hrun
    obtain ⟨h1, h2⟩ := hrun
    cases h2; cases h1
    exact ⟨hwf, GExt.refl _, hmemo, Inst1MemoG.get hmemo (hm2 _ rfl)⟩
  | none =>
    dsimp only at hrun
    obtain ⟨i, hi1, hi2⟩ :=
      spec_imp_exists (U32.sub_spec (x := fuel) (y := 1#u32)
        (by simp only [absU] at hm; scalar_tac))
    rw [hi1, bind_tc_ok] at hrun
    have hone : (1#u32 : U32).val = 1 := by scalar_tac
    have hiv : absU i = m := by simp only [absU] at hi2 hm ⊢; omega
    obtain ⟨hdf, hda⟩ := DenotesSomeG.of_app hview hden
    cases hp1 : Generated.instantiate1 st v i f d using Result.cases with
    | vis e k => rw [hp1] at hrun; simp at hrun
    | div => rw [hp1] at hrun; simp at hrun
    | ret p1 =>
      obtain ⟨o2, st1⟩ := p1
      rw [hp1, bind_tc_ok] at hrun
      cases o2 with
      | none => dsimp only at hrun; simp at hrun
      | some f2 =>
        dsimp only at hrun
        obtain ⟨hwf1, hx1, hmm1, hr1⟩ :=
          ih st st1 i f d f2 hwf (by omega) hmemo hv hdf hp1
        cases hp2 : Generated.instantiate1 st1 v i a d using Result.cases with
        | vis e k => rw [hp2] at hrun; simp at hrun
        | div => rw [hp2] at hrun; simp at hrun
        | ret p2 =>
          obtain ⟨o3, st2⟩ := p2
          rw [hp2, bind_tc_ok] at hrun
          cases o3 with
          | none => dsimp only at hrun; simp at hrun
          | some a2 =>
            dsimp only at hrun
            obtain ⟨hwf2, hx2, hmm2, hr2⟩ :=
              ih st1 st2 i a d a2 hwf1 (by omega) hmm1 (hv.ext hx1) (hda.ext hx1) hp2
            obtain ⟨o4, st3, hI1, hI2, hI3, hI4, hI5⟩ := gintern_app st2 hwf2 f2 a2
            rw [hI1, bind_tc_ok] at hrun
            cases o4 with
            | none => dsimp only at hrun; simp at hrun
            | some rr =>
              dsimp only at hrun
              cases hp3 : Generated.memo_set st3 h d rr using Result.cases with
              | vis e k => rw [hp3] at hrun; simp at hrun
              | div => rw [hp3] at hrun; simp at hrun
              | ret st4 =>
                rw [hp3, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq,
                  Option.some.injEq] at hrun
                obtain ⟨e1, e2⟩ := hrun
                subst e1; subst e2
                have hx3 : GExt st2 st3 := hI3
                have hstep : Inst1AtG ve d.val st h st3 rr :=
                  Inst1AtG.app_step hview hx1 hr1 hx2 hr2 hx3 (hI5 _ rfl)
                have hx4 : GExt st3 st4 := GExt.of_memo_set hp3
                have hmm3 : Inst1MemoG ve st3 := hmm2.mono hx3 hI4
                refine ⟨GWF.of_memo_set hI2 hp3,
                  ((hx1.trans hx2).trans hx3).trans hx4, ?_, hstep.ext hx4⟩
                exact Inst1MemoG.insert hmm3 hp3 (hden.ext ((hx1.trans hx2).trans hx3))
                  (hstep.retarget ((hx1.trans hx2).trans hx3) hden)

/-- con-leche: none — the `lam` arm of D. -/
theorem D_lam_arm (ve : Expr) (v : U32) (n : Nat)
    (ih : ∀ (st st' : Generated.State) (fuel h d r : U32), GWF st → absU fuel ≤ n →
      Inst1MemoG ve st → DenotesG st v ve → DenotesSomeG st h →
      Generated.instantiate1 st v fuel h d = .ok (some r, st') →
      DPost ve d.val st h st' r)
    (st st' : Generated.State) (fuel h d r : U32) (hwf : GWF st) (m : Nat)
    (hm : absU fuel = m + 1) (hmn : m ≤ n) (hmemo : Inst1MemoG ve st)
    (hv : DenotesG st v ve) (hden : DenotesSomeG st h)
    (ty b : U32) (hview : gViewLam st h = some (ty, b))
    (hrun : (do
      let o1 ← Generated.memo_get st h d
      match o1 with
      | none => do
        let i ← fuel - 1#u32
        let (o2, st1) ← Generated.instantiate1 st v i ty d
        match o2 with
        | none => Result.ok (none, st1)
        | some t2 => do
          let i3 ← d + 1#u32
          let (o3, st2) ← Generated.instantiate1 st1 v i b i3
          match o3 with
          | none => Result.ok (none, st2)
          | some b2 => do
            let (o4, st3) ← Generated.intern_lam st2 t2 b2
            match o4 with
            | none => Result.ok (none, st3)
            | some rr => do
              let st4 ← Generated.memo_set st3 h d rr
              Result.ok (o4, st4)
      | some _ => Result.ok (o1, st)) = .ok (some r, st')) :
    DPost ve d.val st h st' r := by
  obtain ⟨o1, hm1, hm2⟩ := gmemo_get st h d
  rw [hm1, bind_tc_ok] at hrun
  cases o1 with
  | some rr =>
    dsimp only at hrun
    simp only [Result.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hrun
    obtain ⟨h1, h2⟩ := hrun
    cases h2; cases h1
    exact ⟨hwf, GExt.refl _, hmemo, Inst1MemoG.get hmemo (hm2 _ rfl)⟩
  | none =>
    dsimp only at hrun
    obtain ⟨i, hi1, hi2⟩ :=
      spec_imp_exists (U32.sub_spec (x := fuel) (y := 1#u32)
        (by simp only [absU] at hm; scalar_tac))
    rw [hi1, bind_tc_ok] at hrun
    have hone : (1#u32 : U32).val = 1 := by scalar_tac
    have hiv : absU i = m := by simp only [absU] at hi2 hm ⊢; omega
    obtain ⟨hdt, hdb⟩ := DenotesSomeG.of_lam hview hden
    cases hp1 : Generated.instantiate1 st v i ty d using Result.cases with
    | vis e k => rw [hp1] at hrun; simp at hrun
    | div => rw [hp1] at hrun; simp at hrun
    | ret p1 =>
      obtain ⟨o2, st1⟩ := p1
      rw [hp1, bind_tc_ok] at hrun
      cases o2 with
      | none => dsimp only at hrun; simp at hrun
      | some t2 =>
        dsimp only at hrun
        obtain ⟨hwf1, hx1, hmm1, hr1⟩ :=
          ih st st1 i ty d t2 hwf (by omega) hmemo hv hdt hp1
        cases hpd : (d + 1#u32 : Result U32) using Result.cases with
        | vis e k => rw [hpd] at hrun; simp at hrun
        | div => rw [hpd] at hrun; simp at hrun
        | ret d1 =>
          have hd1 : d1.val = d.val + 1 := by rw [u32_add_inv hpd, hone]
          rw [hpd, bind_tc_ok] at hrun
          cases hp2 : Generated.instantiate1 st1 v i b d1 using Result.cases with
          | vis e k => rw [hp2] at hrun; simp at hrun
          | div => rw [hp2] at hrun; simp at hrun
          | ret p2 =>
            obtain ⟨o3, st2⟩ := p2
            rw [hp2, bind_tc_ok] at hrun
            cases o3 with
            | none => dsimp only at hrun; simp at hrun
            | some b2 =>
              dsimp only at hrun
              obtain ⟨hwf2, hx2, hmm2, hr2⟩ :=
                ih st1 st2 i b d1 b2 hwf1 (by omega) hmm1 (hv.ext hx1) (hdb.ext hx1) hp2
              rw [hd1] at hr2
              obtain ⟨o4, st3, hI1, hI2, hI3, hI4, hI5⟩ := gintern_lam st2 hwf2 t2 b2
              rw [hI1, bind_tc_ok] at hrun
              cases o4 with
              | none => dsimp only at hrun; simp at hrun
              | some rr =>
                dsimp only at hrun
                cases hp3 : Generated.memo_set st3 h d rr using Result.cases with
                | vis e k => rw [hp3] at hrun; simp at hrun
                | div => rw [hp3] at hrun; simp at hrun
                | ret st4 =>
                  rw [hp3, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq,
                    Option.some.injEq] at hrun
                  obtain ⟨e1, e2⟩ := hrun
                  subst e1; subst e2
                  have hx3 : GExt st2 st3 := hI3
                  have hstep : Inst1AtG ve d.val st h st3 rr :=
                    Inst1AtG.lam_step hview hx1 hr1 hx2 hr2 hx3 (hI5 _ rfl)
                  have hx4 : GExt st3 st4 := GExt.of_memo_set hp3
                  have hmm3 : Inst1MemoG ve st3 := hmm2.mono hx3 hI4
                  refine ⟨GWF.of_memo_set hI2 hp3,
                    ((hx1.trans hx2).trans hx3).trans hx4, ?_, hstep.ext hx4⟩
                  exact Inst1MemoG.insert hmm3 hp3 (hden.ext ((hx1.trans hx2).trans hx3))
                    (hstep.retarget ((hx1.trans hx2).trans hx3) hden)

/-! ## The induction -/

theorem instantiate1_D_aux (ve : Expr) (v : U32) :
    ∀ (n : Nat) (st st' : Generated.State) (fuel h d r : U32), GWF st →
      absU fuel ≤ n → Inst1MemoG ve st → DenotesG st v ve → DenotesSomeG st h →
      Generated.instantiate1 st v fuel h d = .ok (some r, st') →
      DPost ve d.val st h st' r := by
  intro n
  induction n with
  | zero =>
    intro st st' fuel h d r hwf hn _ _ _ hrun
    rw [Generated.instantiate1.eq_def] at hrun
    have : fuel = 0#u32 := by apply absU_inj; simp only [absU] at hn ⊢; scalar_tac
    rw [this, if_pos rfl] at hrun
    simp at hrun
  | succ n ih =>
    intro st st' fuel h d r hwf hn hmemo hv hden hrun
    rw [Generated.instantiate1.eq_def] at hrun
    by_cases hf0 : fuel = 0#u32
    · rw [hf0, if_pos rfl] at hrun; simp at hrun
    rw [if_neg hf0] at hrun
    obtain ⟨t, ht, htv⟩ := abs_tag h
    rw [ht, bind_tc_ok] at hrun
    have hfv : 0 < absU fuel := by
      simp only [absU]
      have : fuel.val ≠ 0 := by intro hc; exact hf0 (absU_inj (by simp [absU, hc]))
      omega
    obtain ⟨m, hm⟩ : ∃ m, absU fuel = m + 1 := ⟨absU fuel - 1, by omega⟩
    by_cases hbv : t = Generated.TAG_BVAR
    · rw [hbv, if_pos rfl, gview_bvar, bind_tc_ok] at hrun
      cases hvw : gViewBvar st h with
      | none => rw [hvw] at hrun; simp at hrun
      | some i =>
        rw [hvw] at hrun
        dsimp only at hrun
        by_cases hid : i = d
        · rw [if_pos hid] at hrun
          simp only [Result.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hrun
          obtain ⟨h1, h2⟩ := hrun
          subst h1; subst h2
          subst hid
          exact ⟨hwf, GExt.refl _, hmemo, Inst1AtG.bvar_hit hvw hv⟩
        · rw [if_neg hid] at hrun
          by_cases hgt : i > d
          · rw [if_pos hgt] at hrun
            obtain ⟨i1, hs1, hs2⟩ :=
              spec_imp_exists (U32.sub_spec (x := i) (y := 1#u32) (by scalar_tac))
            rw [hs1, bind_tc_ok] at hrun
            obtain ⟨oi, sti, hI1, hI2, hI3, hI4, hI5⟩ := gintern_bvar st hwf i1
            rw [hI1, Result.ok.injEq, Prod.mk.injEq] at hrun
            obtain ⟨e1, e2⟩ := hrun
            subst e2
            have hone : (1#u32 : U32).val = 1 := by scalar_tac
            have hi1v : i1.val = i.val - 1 := by omega
            refine ⟨hI2, hI3, hmemo.mono hI3 hI4, ?_⟩
            exact Inst1AtG.bvar_gt hvw (by simpa [absU] using hgt) hi1v (hI5 _ e1)
          · rw [if_neg hgt] at hrun
            simp only [Result.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hrun
            obtain ⟨h1, h2⟩ := hrun
            subst h1; subst h2
            exact ⟨hwf, GExt.refl _, hmemo,
              Inst1AtG.bvar_le hvw hid (by intro hc; exact hgt (by simpa [absU] using hc))⟩
    · rw [if_neg hbv] at hrun
      by_cases hap : t = Generated.TAG_APP
      · rw [hap, if_pos rfl, gview_app, bind_tc_ok] at hrun
        cases hvw : gViewApp st h with
        | none => rw [hvw] at hrun; simp at hrun
        | some fa =>
          obtain ⟨f, a⟩ := fa
          rw [hvw] at hrun
          dsimp only at hrun
          exact D_app_arm ve v n (fun s1 s2 fu hh dd rr w1 w2 w3 w4 w5 w6 =>
            ih s1 s2 fu hh dd rr w1 w2 w3 w4 w5 w6)
            st st' fuel h d r hwf m hm (by omega) hmemo hv hden f a hvw hrun
      · rw [if_neg hap] at hrun
        by_cases hlm : t = Generated.TAG_LAM
        · rw [hlm, if_pos rfl, gview_lam, bind_tc_ok] at hrun
          cases hvw : gViewLam st h with
          | none => rw [hvw] at hrun; simp at hrun
          | some tb =>
            obtain ⟨ty, b⟩ := tb
            rw [hvw] at hrun
            dsimp only at hrun
            exact D_lam_arm ve v n (fun s1 s2 fu hh dd rr w1 w2 w3 w4 w5 w6 =>
              ih s1 s2 fu hh dd rr w1 w2 w3 w4 w5 w6)
              st st' fuel h d r hwf m hm (by omega) hmemo hv hden ty b hvw hrun
        · rw [if_neg hlm] at hrun
          simp at hrun

/-- **Experiment D** — the Aeneas model of the Rust against con-leche's pure
`instantiate1`, in one layer.  Same conclusion as `C1 ∘ C2`. -/
theorem instantiate1_D (st st' : Generated.State) (v fuel h d r : U32) (ve e : Expr)
    (hwf : GWF st) (hmemo : Inst1MemoG ve st)
    (hv : DenotesG st v ve) (he : DenotesG st h e)
    (hrun : Generated.instantiate1 st v fuel h d = .ok (some r, st')) :
    DenotesG st' r (e.instantiate1 ve d.val) :=
  (instantiate1_D_aux ve v (absU fuel) st st' fuel h d r hwf (Nat.le_refl _)
    hmemo hv ⟨e, he⟩ hrun).2.2.2 e he

end ConRon.Arena.Spike

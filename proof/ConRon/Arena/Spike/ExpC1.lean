/-
# Experiment C1 — the Aeneas model of the Rust refines the Lean twin

DESIGN §8.6's experiment C1, closed.  **No `Expr` occurs**: this half of
Theorem 2 is *representation only*, and the whole of it is `MiniAbs.lean`'s
eight abstraction lemmas plus the induction below.

Three findings the round-1 report did not have:

1. **C1 is not invariant-free.**  Rust's `n as u32` truncates rather than
   failing, so `find_*_from`'s index cast is faithful only below `IDX_CAP`;
   C1 carries `GWF` (no constructor array longer than `IDX_CAP`) exactly as
   the denotation half carries `StoreWF`.  `GWF` is maintained by
   `intern_*`'s own capacity test, which is the same test the twin makes —
   that equivalence is `abs_intern_*`'s content.
2. **The proof is an equational match, not `mvcgen`.**  The Aeneas model is
   `Result`-valued with the state threaded by hand; the twin is
   `StateT … (Except …)`.  `MiniRun.lean` turns the twin into the same shape
   once (`mInstantiate1_run_succ`), and then each branch is `rw`-for-`rw`.
   `mvcgen` buys nothing here because there are no *verification
   conditions* — only two programs to match.
3. **The failure modes do not line up, and partial correctness hides it.**
   The Rust reports fuel exhaustion, a dangling handle and a full arena as
   `ok (none, st)`; the twin `throw`s.  C1 is stated on `.ok (some r, st')`
   and says nothing otherwise, which is `SimAt`'s shape at the
   representation layer.
-/
import ConRon.Arena.Spike.MiniAbs

namespace ConRon.Arena.Spike

open ConLeche Aeneas Aeneas.Std Aeneas.Std.WP

set_option maxHeartbeats 2000000

/-- con-leche: none — the `Except` bind at a value, reduced. -/
theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α).bind f = f a := rfl

/-! ## The two branching arms

One lemma per constructor that recurses — con-leche's `Verify/Disc.lean`
layer, at the representation grade.  Each takes the induction hypothesis as
an argument, so the induction itself stays short. -/

/-- con-leche: none — the `app` arm of C1. -/
theorem C1_app_arm (n : Nat)
    (ih : ∀ (st st' : Generated.State) (v fuel h d r : U32), GWF st → absU fuel ≤ n →
      Generated.instantiate1 st v fuel h d = .ok (some r, st') →
      GWF st' ∧ (mInstantiate1 (absU v) (absU fuel) (absU h) (absU d)).run (absState st)
        = .ok (absU r, absState st'))
    (st st' : Generated.State) (v fuel h d r : U32) (hwf : GWF st) (m : Nat)
    (hm : absU fuel = m + 1) (hmn : m ≤ n) (f a : U32)
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
    GWF st' ∧
      (match mMemoGet (absState st) (absU h) (absU d) with
       | some rr => Except.ok (rr, absState st)
       | none =>
         ((mInstantiate1 (absU v) m (absU f) (absU d)).run (absState st)).bind (fun p =>
           ((mInstantiate1 (absU v) m (absU a) (absU d)).run p.2).bind (fun q =>
             ((mInternApp p.1 q.1).run q.2).bind (fun w =>
               ((mMemoSet (absU h) (absU d) w.1).run w.2).bind
                 (fun u => Except.ok (w.1, u.2))))))
        = .ok (absU r, absState st') := by
  obtain ⟨o1, hm1, hm2⟩ := abs_memo_get st h d
  rw [hm1, bind_tc_ok] at hrun
  rw [hm2]
  cases o1 with
  | some rr =>
    dsimp only at hrun ⊢
    simp only [Result.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hrun
    obtain ⟨h1, h2⟩ := hrun
    cases h2; cases h1
    exact ⟨hwf, rfl⟩
  | none =>
    dsimp only at hrun ⊢
    obtain ⟨i, hi1, hi2⟩ :=
      spec_imp_exists (U32.sub_spec (x := fuel) (y := 1#u32)
        (by simp only [absU] at hm; scalar_tac))
    rw [hi1, bind_tc_ok] at hrun
    have hone : (1#u32 : U32).val = 1 := by scalar_tac
    have hiv : absU i = m := by simp only [absU] at hi2 hm ⊢; omega
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
        obtain ⟨hwf1, hrec1⟩ := ih st st1 v i f d f2 hwf (by omega) hp1
        rw [hiv] at hrec1
        simp only [hrec1, except_ok_bind]
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
            obtain ⟨hwf2, hrec2⟩ := ih st1 st2 v i a d a2 hwf1 (by omega) hp2
            rw [hiv] at hrec2
            simp only [hrec2, except_ok_bind]
            obtain ⟨o4, st3, hI1, hI2, hI3⟩ := abs_intern_app st2 hwf2 f2 a2
            rw [hI1, bind_tc_ok] at hrun
            cases o4 with
            | none => dsimp only at hrun; simp at hrun
            | some rr =>
              dsimp only at hrun
              simp only [hI3 rr rfl, except_ok_bind]
              cases hp3 : Generated.memo_set st3 h d rr using Result.cases with
              | vis e k => rw [hp3] at hrun; simp at hrun
              | div => rw [hp3] at hrun; simp at hrun
              | ret st4 =>
                obtain ⟨hms, hmw⟩ := abs_memo_set st3 st4 h d rr hp3
                rw [hp3, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq,
                  Option.some.injEq] at hrun
                obtain ⟨e1, e2⟩ := hrun
                subst e1; subst e2
                refine ⟨hmw hI2, ?_⟩
                simp only [Option.map_none, mMemoSet_run, except_ok_bind]
                rw [hms]

/-- con-leche: none — the `lam` arm of C1.  The only difference from the
`app` arm is the cursor bump, and it is a *checked* `u32` addition: the arm
learns that `d + 1` did not overflow from the success it is given. -/
theorem C1_lam_arm (n : Nat)
    (ih : ∀ (st st' : Generated.State) (v fuel h d r : U32), GWF st → absU fuel ≤ n →
      Generated.instantiate1 st v fuel h d = .ok (some r, st') →
      GWF st' ∧ (mInstantiate1 (absU v) (absU fuel) (absU h) (absU d)).run (absState st)
        = .ok (absU r, absState st'))
    (st st' : Generated.State) (v fuel h d r : U32) (hwf : GWF st) (m : Nat)
    (hm : absU fuel = m + 1) (hmn : m ≤ n) (ty b : U32)
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
    GWF st' ∧
      (match mMemoGet (absState st) (absU h) (absU d) with
       | some rr => Except.ok (rr, absState st)
       | none =>
         ((mInstantiate1 (absU v) m (absU ty) (absU d)).run (absState st)).bind (fun p =>
           ((mInstantiate1 (absU v) m (absU b) (absU d + 1)).run p.2).bind (fun q =>
             ((mInternLam p.1 q.1).run q.2).bind (fun w =>
               ((mMemoSet (absU h) (absU d) w.1).run w.2).bind
                 (fun u => Except.ok (w.1, u.2))))))
        = .ok (absU r, absState st') := by
  obtain ⟨o1, hm1, hm2⟩ := abs_memo_get st h d
  rw [hm1, bind_tc_ok] at hrun
  rw [hm2]
  cases o1 with
  | some rr =>
    dsimp only at hrun ⊢
    simp only [Result.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hrun
    obtain ⟨h1, h2⟩ := hrun
    cases h2; cases h1
    exact ⟨hwf, rfl⟩
  | none =>
    dsimp only at hrun ⊢
    obtain ⟨i, hi1, hi2⟩ :=
      spec_imp_exists (U32.sub_spec (x := fuel) (y := 1#u32)
        (by simp only [absU] at hm; scalar_tac))
    rw [hi1, bind_tc_ok] at hrun
    have hone : (1#u32 : U32).val = 1 := by scalar_tac
    have hiv : absU i = m := by simp only [absU] at hi2 hm ⊢; omega
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
        obtain ⟨hwf1, hrec1⟩ := ih st st1 v i ty d t2 hwf (by omega) hp1
        rw [hiv] at hrec1
        simp only [hrec1, except_ok_bind]
        cases hpd : (d + 1#u32 : Result U32) using Result.cases with
        | vis e k => rw [hpd] at hrun; simp at hrun
        | div => rw [hpd] at hrun; simp at hrun
        | ret d1 =>
          have hd1 : absU d1 = absU d + 1 := by
            simp only [absU]; rw [u32_add_inv hpd, hone]
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
              obtain ⟨hwf2, hrec2⟩ := ih st1 st2 v i b d1 b2 hwf1 (by omega) hp2
              rw [hiv, hd1] at hrec2
              simp only [hrec2, except_ok_bind]
              obtain ⟨o4, st3, hI1, hI2, hI3⟩ := abs_intern_lam st2 hwf2 t2 b2
              rw [hI1, bind_tc_ok] at hrun
              cases o4 with
              | none => dsimp only at hrun; simp at hrun
              | some rr =>
                dsimp only at hrun
                simp only [hI3 rr rfl, except_ok_bind]
                cases hp3 : Generated.memo_set st3 h d rr using Result.cases with
                | vis e k => rw [hp3] at hrun; simp at hrun
                | div => rw [hp3] at hrun; simp at hrun
                | ret st4 =>
                  obtain ⟨hms, hmw⟩ := abs_memo_set st3 st4 h d rr hp3
                  rw [hp3, bind_tc_ok, Result.ok.injEq, Prod.mk.injEq,
                    Option.some.injEq] at hrun
                  obtain ⟨e1, e2⟩ := hrun
                  subst e1; subst e2
                  refine ⟨hmw hI2, ?_⟩
                  simp only [Option.map_none, mMemoSet_run, except_ok_bind]
                  rw [hms]

/-! ## The induction -/

/-- con-leche: none — **experiment C1**, with the fuel bound explicit. -/
theorem instantiate1_C1_aux :
    ∀ (n : Nat) (st st' : Generated.State) (v fuel h d r : U32), GWF st →
      absU fuel ≤ n →
      Generated.instantiate1 st v fuel h d = .ok (some r, st') →
      GWF st' ∧
      (mInstantiate1 (absU v) (absU fuel) (absU h) (absU d)).run (absState st)
        = .ok (absU r, absState st') := by
  intro n
  induction n with
  | zero =>
    intro st st' v fuel h d r hwf hn hrun
    rw [Generated.instantiate1.eq_def] at hrun
    have : fuel = 0#u32 := by apply absU_inj; simp only [absU] at hn ⊢; scalar_tac
    rw [this, if_pos rfl] at hrun
    simp at hrun
  | succ n ih =>
    intro st st' v fuel h d r hwf hn hrun
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
    rw [hm, mInstantiate1_run_succ]
    by_cases hbv : t = Generated.TAG_BVAR
    · have hmt : mTagOf (absU h) = mTagBvar := by rw [← htv, ← tagbvar, hbv]
      rw [hbv, if_pos rfl] at hrun
      rw [if_pos hmt]
      obtain ⟨o, ho1, ho2⟩ := abs_view_bvar st h
      rw [ho1, bind_tc_ok] at hrun
      rw [ho2]
      cases o with
      | none => simp at hrun
      | some i =>
        dsimp only at hrun
        simp only [Option.map_some]
        by_cases hid : i = d
        · rw [if_pos hid] at hrun
          rw [if_pos (show absU i = absU d by rw [hid])]
          simp only [Result.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨h1, h2⟩ := hrun
          cases h1; cases h2
          exact ⟨hwf, rfl⟩
        · rw [if_neg hid] at hrun
          have hid' : ¬ (absU i = absU d) := fun hc => hid (absU_inj hc)
          rw [if_neg hid']
          by_cases hgt : i > d
          · rw [if_pos hgt] at hrun
            have hgt' : absU d < absU i := by simpa [absU] using hgt
            rw [if_pos hgt']
            obtain ⟨i1, hi1, hi1v⟩ :=
              spec_imp_exists (U32.sub_spec (x := i) (y := 1#u32) (by scalar_tac))
            rw [hi1, bind_tc_ok] at hrun
            obtain ⟨oi, sti, hI1, hI2, hI3⟩ := abs_intern_bvar st hwf i1
            rw [hI1, Result.ok.injEq, Prod.mk.injEq] at hrun
            obtain ⟨e1, e2⟩ := hrun
            cases e2
            refine ⟨hI2, ?_⟩
            have hrw : absU i1 = absU i - 1 := by
              simp only [absU] at hi1v ⊢
              have hone : (1#u32 : U32).val = 1 := by scalar_tac
              omega
            rw [← hrw]
            exact hI3 r e1
          · rw [if_neg hgt] at hrun
            have hgt' : ¬ (absU d < absU i) := by
              intro hc; exact hgt (by simpa [absU] using hc)
            rw [if_neg hgt']
            simp only [Result.ok.injEq, Prod.mk.injEq] at hrun
            obtain ⟨h1, h2⟩ := hrun
            cases h1; cases h2
            exact ⟨hwf, rfl⟩
    · have hmt : ¬ (mTagOf (absU h) = mTagBvar) := by
        rw [← htv, ← tagbvar, absU_eq]; exact hbv
      rw [if_neg hbv] at hrun
      rw [if_neg hmt]
      by_cases hap : t = Generated.TAG_APP
      · have hmt2 : mTagOf (absU h) = mTagApp := by rw [← htv, ← tagapp, hap]
        rw [hap, if_pos rfl] at hrun
        rw [if_pos hmt2]
        obtain ⟨o, ho1, ho2⟩ := abs_view_app st h
        rw [ho1, bind_tc_ok] at hrun
        rw [ho2]
        cases o with
        | none => simp at hrun
        | some fa =>
          obtain ⟨f, a⟩ := fa
          dsimp only at hrun ⊢
          exact C1_app_arm n ih st st' v fuel h d r hwf m hm (by omega) f a hrun
      · have hmt2 : ¬ (mTagOf (absU h) = mTagApp) := by
          rw [← htv, ← tagapp, absU_eq]; exact hap
        rw [if_neg hap] at hrun
        rw [if_neg hmt2]
        by_cases hlm : t = Generated.TAG_LAM
        · have hmt3 : mTagOf (absU h) = mTagLam := by rw [← htv, ← taglam, hlm]
          rw [hlm, if_pos rfl] at hrun
          rw [if_pos hmt3]
          obtain ⟨o, ho1, ho2⟩ := abs_view_lam st h
          rw [ho1, bind_tc_ok] at hrun
          rw [ho2]
          cases o with
          | none => simp at hrun
          | some tb =>
            obtain ⟨ty, b⟩ := tb
            dsimp only at hrun ⊢
            exact C1_lam_arm n ih st st' v fuel h d r hwf m hm (by omega) ty b hrun
        · have hmt3 : ¬ (mTagOf (absU h) = mTagLam) := by
            rw [← htv, ← taglam, absU_eq]; exact hlm
          rw [if_neg hlm] at hrun
          simp at hrun

/-- **Experiment C1** — the Aeneas model of the Rust refines the Lean twin.
No `Expr` occurs: this half is *representation only*. -/
theorem instantiate1_C1 (st st' : Generated.State) (v fuel h d r : Aeneas.Std.U32)
    (hwf : GWF st)
    (hrun : Generated.instantiate1 st v fuel h d = .ok (some r, st')) :
    (mInstantiate1 (absU v) (absU fuel) (absU h) (absU d)).run (absState st)
      = .ok (absU r, absState st') :=
  (instantiate1_C1_aux (absU fuel) st st' v fuel h d r hwf (Nat.le_refl _) hrun).2

/-- con-leche: none — C1's invariant half, which the caller needs to iterate. -/
theorem instantiate1_C1_wf (st st' : Generated.State) (v fuel h d r : Aeneas.Std.U32)
    (hwf : GWF st)
    (hrun : Generated.instantiate1 st v fuel h d = .ok (some r, st')) : GWF st' :=
  (instantiate1_C1_aux (absU fuel) st st' v fuel h d r hwf (Nat.le_refl _) hrun).1

end ConRon.Arena.Spike

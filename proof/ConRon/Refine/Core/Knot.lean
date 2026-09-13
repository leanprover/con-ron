import ConRon.Refine.Core.Statements

/-! # The knot's skeleton: the memo wrappers and the fuel induction

`CORE_PLAN.md` step 6, third file (task #53).  `Refine/Core/Statements.lean`
fixed the twelve statements; this file proves the two halves of the induction
that are *not* about the bodies' arms:

* `wrappers_zero` — at `fuel = 0` every Rust wrapper returns
  `.internal "fuel exhausted: …"`, so `RefinesE`/`RefinesB` hold vacuously
  (their hypothesis is an `.Ok` result);
* `wrappers_succ` — `Bodies mode fuel → Wrappers mode (fuel + 1)`: the memo
  argument, once per wrapper.  The Rust probe hits → `StateRel`'s clause for
  that map gives con-leche's `[e]?` hit and `memoEI` returns it unchanged;
  the probe misses → the body lemma at `fuel` (the Rust decrements, and
  con-leche's `prev ()` *is* `coreKnotI fe fuel`), then the map's insert
  lemma and `StateWF`, whose value clause is what makes the stored result
  `ExprWF` for a later hit;
* `knot_induction` — the fuel recursion itself, with the arms
  (`Wrappers mode fuel → Bodies mode fuel`, tasks #54+) as a hypothesis.

The `fuel + 1` step is stated over `Std.U64` with the successor as a
hypothesis on the values (`fuel'.val = fuel.val + 1`), which is what
`knot_induction` can supply for every `fuel` below `U64.max` and what the
wrapper's `fuel - 1#u64` needs to be `fuel` again.
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

/-! ## `memoEI` and `memoBI`, run

Four lemmas, the whole content of con-leche's two memo combinators
(`ConLeche/Cached/CoreC.lean:1877-1904`) in the state monad: a hit returns the
stored value and leaves the state alone; a miss runs the body and then
`modify`s.  Note con-leche's insert *detaches* the map first — `let mp :=
get' st; let st := set' st ∅; set' st (mp.insert e r)`, the linear-update
dance task #14 dropped on the Rust side — so the state after a miss is
`set' (set' lst' ∅) ((get' lst').insert e r)`; at every concrete map that is
`{ lst' with … := ….insert e r }` by structure eta, which is what the `hs`
argument is for. -/

open ConLeche.Cached in
/-- `memoEI`, probe hit. -/
theorem memoEI_run_hit {get' : CState → _root_.Std.HashMap ConLeche.Expr ConLeche.Expr}
    {set' : CState → _root_.Std.HashMap ConLeche.Expr ConLeche.Expr → CState}
    {f : Nat → ConLeche.Expr → CheckCM ConLeche.Expr}
    {lst : CState} {d : Nat} {e r : ConLeche.Expr}
    (h : (get' lst)[e]? = some r) :
    (memoEI get' set' f d e).run lst = .ok (r, lst) := by
  simp [memoEI, h]; rfl

open ConLeche.Cached in
/-- `memoEI`, probe miss: the body runs, then the detach-and-insert. -/
theorem memoEI_run_miss {get' : CState → _root_.Std.HashMap ConLeche.Expr ConLeche.Expr}
    {set' : CState → _root_.Std.HashMap ConLeche.Expr ConLeche.Expr → CState}
    {f : Nat → ConLeche.Expr → CheckCM ConLeche.Expr}
    {lst lst' lst'' : CState} {d : Nat} {e r : ConLeche.Expr}
    (h : (get' lst)[e]? = none)
    (hf : (f d e).run lst = .ok (r, lst'))
    (hs : set' (set' lst' ∅) ((get' lst').insert e r) = lst'') :
    (memoEI get' set' f d e).run lst = .ok (r, lst'') := by
  simp [memoEI, h, hf, ← hs]

open ConLeche.Cached in
/-- `memoBI`, probe hit (the `(a, b)` key). -/
theorem memoBI_run_hit {f : Nat → ConLeche.Expr → ConLeche.Expr → CheckCM Bool}
    {lst : CState} {d : Nat} {a b : ConLeche.Expr} {r : Bool}
    (h : lst.defeqC[(a, b)]? = some r) :
    (memoBI f d a b).run lst = .ok (r, lst) := by
  simp [memoBI, h]; rfl

open ConLeche.Cached in
/-- `memoBI`, probe miss. -/
theorem memoBI_run_miss {f : Nat → ConLeche.Expr → ConLeche.Expr → CheckCM Bool}
    {lst lst' : CState} {d : Nat} {a b : ConLeche.Expr} {r : Bool}
    (h : lst.defeqC[(a, b)]? = none)
    (hf : (f d a b).run lst = .ok (r, lst')) :
    (memoBI f d a b).run lst
      = .ok (r, { lst' with defeqC := lst'.defeqC.insert (a, b) r }) := by
  simp [memoBI, h, hf]

/-! ## The knot at `fuel + 1`, field by field

`coreKnotI`'s successor arm (`ConLeche/Cached/CoreC.lean:1916-1975`),
projected.  Each is `rfl`: `prev ()` is a `Unit` closure, so `prev () =
coreKnotI fe fuel` holds by iota, and the six fields are the record's. -/

open ConLeche.Cached in
theorem knot_succ_whnfCore (mode : env.CheckMode) (lfe : ConLeche.FEnv) (n : Nat) :
    (knot mode lfe (n + 1)).whnfCore
      = memoEI (·.whnfCoreC) (fun st mp => { st with whnfCoreC := mp })
          (fun d e => whnfCoreBodyI (absMode mode) (knot mode lfe n) lfe d e) := rfl

open ConLeche.Cached in
theorem knot_succ_whnf (mode : env.CheckMode) (lfe : ConLeche.FEnv) (n : Nat) :
    (knot mode lfe (n + 1)).whnf
      = memoEI (·.whnfC) (fun st mp => { st with whnfC := mp })
          (fun d e => whnfBodyI (knot mode lfe n) lfe d e) := rfl

open ConLeche.Cached in
theorem knot_succ_infer (mode : env.CheckMode) (lfe : ConLeche.FEnv) (n : Nat) :
    (knot mode lfe (n + 1)).infer
      = memoEI (·.inferC) (fun st mp => { st with inferC := mp })
          (fun d e => inferBodyI (absMode mode) (knot mode lfe n) lfe d e) := rfl

open ConLeche.Cached in
theorem knot_succ_defeq (mode : env.CheckMode) (lfe : ConLeche.FEnv) (n : Nat) :
    (knot mode lfe (n + 1)).defeq
      = memoBI (fun d a b => defeqBodyI (absMode mode) (knot mode lfe n) lfe d a b) := rfl

open ConLeche.Cached in
theorem knot_succ_annotate (mode : env.CheckMode) (lfe : ConLeche.FEnv) (n : Nat) :
    (knot mode lfe (n + 1)).annotate
      = memoEI (·.annotC) (fun st mp => { st with annotC := mp })
          (fun d e => annotateBodyI (knot mode lfe n) lfe d e) := rfl

open ConLeche.Cached in
/-- The io slot, selected once per knot level by `mode.ioGate` (con-leche's
task #170/#172 B4: at the gate the io body under its own memo `inferIOC`,
tied to the previous level's io view; off the gate the full inference closure
under `inferC`, because the two grades are the same function there). -/
theorem knot_succ_inferIO (mode : env.CheckMode) (lfe : ConLeche.FEnv) (n : Nat) :
    (knot mode lfe (n + 1)).inferIO
      = if (absMode mode).ioGate then
          memoEI (·.inferIOC) (fun st mp => { st with inferIOC := mp })
            (fun d e => inferBodyIOI (absMode mode) (knot mode lfe n).ioView lfe d e)
        else
          memoEI (·.inferC) (fun st mp => { st with inferC := mp })
            (fun d e => inferBodyI (absMode mode) (knot mode lfe n) lfe d e) := rfl

/-! ## The six Rust probes

`core_c::whnf_core_probe` and friends (`cached/core_c.rs:5004-5055`) are the
`(get' (← get))[e]?` of `memoEI` over a shared borrow, plus an `expr::dup`
that is the identity in the model.  Each composes the generated function with
the matching `Refine/State.lean` lemma. -/

theorem whnf_core_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {e : expr.Expr} {o : Option expr.Expr}
    (hrel : StateRel st lst) (hwf : StateWF st) (he : ExprWF e)
    (h : cached.core_c.whnf_core_probe st e = ok o) :
    o.map absExpr = lst.whnfCoreC[absExpr e]? ∧ ∀ r, o = some r → ExprWF r := by
  rw [cached.core_c.whnf_core_probe] at h
  simp only [bind_eq_ok_iff, expr_dup_eq] at h
  obtain ⟨o1, hget, h⟩ := h
  cases o1 <;>
    (simp only [Result.ok.injEq, bind_eq_ok_iff, exists_eq_left'] at h; subst h;
     exact whnf_core_c_probe_refines hrel hwf he hget)

theorem whnf_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {e : expr.Expr} {o : Option expr.Expr}
    (hrel : StateRel st lst) (hwf : StateWF st) (he : ExprWF e)
    (h : cached.core_c.whnf_probe st e = ok o) :
    o.map absExpr = lst.whnfC[absExpr e]? ∧ ∀ r, o = some r → ExprWF r := by
  rw [cached.core_c.whnf_probe] at h
  simp only [bind_eq_ok_iff, expr_dup_eq] at h
  obtain ⟨o1, hget, h⟩ := h
  cases o1 <;>
    (simp only [Result.ok.injEq, bind_eq_ok_iff, exists_eq_left'] at h; subst h;
     exact whnf_c_probe_refines hrel hwf he hget)

theorem infer_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {e : expr.Expr} {o : Option expr.Expr}
    (hrel : StateRel st lst) (hwf : StateWF st) (he : ExprWF e)
    (h : cached.core_c.infer_probe st e = ok o) :
    o.map absExpr = lst.inferC[absExpr e]? ∧ ∀ r, o = some r → ExprWF r := by
  rw [cached.core_c.infer_probe] at h
  simp only [bind_eq_ok_iff, expr_dup_eq] at h
  obtain ⟨o1, hget, h⟩ := h
  cases o1 <;>
    (simp only [Result.ok.injEq, bind_eq_ok_iff, exists_eq_left'] at h; subst h;
     exact infer_c_probe_refines hrel hwf he hget)

theorem infer_io_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {e : expr.Expr} {o : Option expr.Expr}
    (hrel : StateRel st lst) (hwf : StateWF st) (he : ExprWF e)
    (h : cached.core_c.infer_io_probe st e = ok o) :
    o.map absExpr = lst.inferIOC[absExpr e]? ∧ ∀ r, o = some r → ExprWF r := by
  rw [cached.core_c.infer_io_probe] at h
  simp only [bind_eq_ok_iff, expr_dup_eq] at h
  obtain ⟨o1, hget, h⟩ := h
  cases o1 <;>
    (simp only [Result.ok.injEq, bind_eq_ok_iff, exists_eq_left'] at h; subst h;
     exact infer_io_c_probe_refines hrel hwf he hget)

theorem annot_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {e : expr.Expr} {o : Option expr.Expr}
    (hrel : StateRel st lst) (hwf : StateWF st) (he : ExprWF e)
    (h : cached.core_c.annot_probe st e = ok o) :
    o.map absExpr = lst.annotC[absExpr e]? ∧ ∀ r, o = some r → ExprWF r := by
  rw [cached.core_c.annot_probe] at h
  simp only [bind_eq_ok_iff, expr_dup_eq] at h
  obtain ⟨o1, hget, h⟩ := h
  cases o1 <;>
    (simp only [Result.ok.injEq, bind_eq_ok_iff, exists_eq_left'] at h; subst h;
     exact annot_c_probe_refines hrel hwf he hget)

theorem defeq_probe_refines {st : cached.state_c.CState}
    {lst : ConLeche.Cached.CState} {k : expr.Expr × expr.Expr} {o : Option Bool}
    (hrel : StateRel st lst) (hwf : StateWF st) (hk : ExprPairWF k)
    (h : cached.core_c.defeq_probe st k = ok o) :
    o = lst.defeqC[absExprPair k]? := by
  rw [cached.core_c.defeq_probe] at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨o1, hget, h⟩ := h
  cases o1 <;>
    (simp only [Result.ok.injEq] at h; subst h;
     exact defeq_c_probe_refines hrel hwf hk hget)

/-! ## Fuel zero

Every wrapper's first test is `fuel == 0`, and its `then` branch builds
`CheckError::internal("fuel exhausted: …")` from the code-point array.  So
the `f … = ok (.Ok r, st')` hypothesis of `RefinesE`/`RefinesB` is absurd:
either the code-point chain fails (`fail ≠ ok`) or it returns an `.Err`. -/

theorem wrappers_zero (mode : env.CheckMode) : Wrappers mode 0#u64 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro st fe d e r st' _ _ _ h
    rw [cached.core_c.whnf_core.eq_def] at h; simp at h
  · intro st fe d e r st' _ _ _ h
    rw [cached.core_c.whnf.eq_def] at h; simp at h
  · intro st fe d e r st' _ _ _ h
    rw [cached.core_c.infer.eq_def] at h; simp at h
  · intro st fe d a b r st' _ _ _ _ h
    rw [cached.core_c.defeq.eq_def] at h; simp at h
  · intro st fe d e r st' _ _ _ h
    rw [cached.core_c.annotate.eq_def] at h; simp at h
  · intro st fe d e r st' _ _ _ h
    rw [cached.core_c.infer_io.eq_def] at h; simp at h

/-! ## Fuel `n + 1`: the memo argument -/

/-- The wrapper's `fuel - 1` undoes the step's successor. -/
theorem fuel_pred {fuel fuel' i : Std.U64} (hf : fuel'.val = fuel.val + 1)
    (hi : fuel' - 1#u64 = ok i) : i = fuel :=
  u64_val_inj (by rw [HashMap.uscalar_sub_eq hi, hf]; rfl)

/-- **The memo step.**  Each of the six wrappers at `fuel + 1` refines
con-leche's knot at `fuel + 1`, given the six bodies at `fuel`.  One proof
per wrapper, each the same three moves: unfold past the fuel test, split on
the probe, and — on a miss — the body lemma at `fuel` followed by the map's
insert lemma. -/
theorem wrappers_succ {mode : env.CheckMode} {fuel fuel' : Std.U64}
    (hf : fuel'.val = fuel.val + 1) (hbd : Bodies mode fuel) :
    Wrappers mode fuel' := by
  have hne : ¬ (fuel' = 0#u64) := by
    intro hc; rw [hc] at hf; simp at hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- `whnfCore`, memoized in `whnfCoreC`
  · intro st fe d e r st' hst hfe he h lst lfe hrel hfrel
    rw [cached.core_c.whnf_core.eq_def, if_neg hne] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨o, hprobe, h⟩ := h
    obtain ⟨hlook, hwfo⟩ := whnf_core_probe_refines hrel hst he hprobe
    cases o with
    | some v =>
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨hrv, hstv⟩ := h
      subst hrv; subst hstv
      refine ⟨lst, ?_, hrel, hst, hwfo v rfl⟩
      simp only [hf, knot_succ_whnfCore]
      exact memoEI_run_hit (by simpa using hlook.symm)
    | none =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i, hi, p, hbody, h⟩ := h
      obtain ⟨rr, st1⟩ := p
      have h2 : (match rr with
          | core.result.Result.Ok r1 => do
            let e1 ← kernel.expr.dup e
            let e2 ← kernel.expr.dup r1
            let q ← ron.hashmap.HashMap.insert hExpr eExpr st1.whnf_core_c e1 e2
            ok (rr, { st1 with whnf_core_c := q.2 })
          | core.result.Result.Err _ => ok (rr, st1))
          = ok (core.result.Result.Ok r, st') := h
      clear h
      cases rr with
      | Err ce => simp at h2
      | Ok r1 =>
        simp only [expr_dup_eq, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq,
          core.result.Result.Ok.injEq, exists_eq_left'] at h2
        obtain ⟨q, hins, hr1, hst'⟩ := h2
        subst hr1; subst hst'
        have hif := fuel_pred hf hi; subst hif
        obtain ⟨lst1, hrun, hrel1, hwf1, hwfr⟩ :=
          hbd.whnfCore st fe d e r1 st1 hst hfe he hbody lst lfe hrel hfrel
        obtain ⟨hrel2, hwf2⟩ := whnf_core_c_insert_refines hrel1 hwf1 he hwfr hins
        refine ⟨_, ?_, hrel2, hwf2, hwfr⟩
        simp only [hf, knot_succ_whnfCore]
        exact memoEI_run_miss (by simpa using hlook.symm) hrun rfl
  -- `whnf`, memoized in `whnfC`
  · intro st fe d e r st' hst hfe he h lst lfe hrel hfrel
    rw [cached.core_c.whnf.eq_def, if_neg hne] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨o, hprobe, h⟩ := h
    obtain ⟨hlook, hwfo⟩ := whnf_probe_refines hrel hst he hprobe
    cases o with
    | some v =>
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨hrv, hstv⟩ := h
      subst hrv; subst hstv
      refine ⟨lst, ?_, hrel, hst, hwfo v rfl⟩
      simp only [hf, knot_succ_whnf]
      exact memoEI_run_hit (by simpa using hlook.symm)
    | none =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i, hi, p, hbody, h⟩ := h
      obtain ⟨rr, st1⟩ := p
      have h2 : (match rr with
          | core.result.Result.Ok r1 => do
            let e1 ← kernel.expr.dup e
            let e2 ← kernel.expr.dup r1
            let q ← ron.hashmap.HashMap.insert hExpr eExpr st1.whnf_c e1 e2
            ok (rr, { st1 with whnf_c := q.2 })
          | core.result.Result.Err _ => ok (rr, st1))
          = ok (core.result.Result.Ok r, st') := h
      clear h
      cases rr with
      | Err ce => simp at h2
      | Ok r1 =>
        simp only [expr_dup_eq, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq,
          core.result.Result.Ok.injEq, exists_eq_left'] at h2
        obtain ⟨q, hins, hr1, hst'⟩ := h2
        subst hr1; subst hst'
        have hif := fuel_pred hf hi; subst hif
        obtain ⟨lst1, hrun, hrel1, hwf1, hwfr⟩ :=
          hbd.whnf st fe d e r1 st1 hst hfe he hbody lst lfe hrel hfrel
        obtain ⟨hrel2, hwf2⟩ := whnf_c_insert_refines hrel1 hwf1 he hwfr hins
        refine ⟨_, ?_, hrel2, hwf2, hwfr⟩
        simp only [hf, knot_succ_whnf]
        exact memoEI_run_miss (by simpa using hlook.symm) hrun rfl
  -- `infer`, memoized in `inferC`; the body runs at the full grade (`io = false`)
  · intro st fe d e r st' hst hfe he h lst lfe hrel hfrel
    rw [cached.core_c.infer.eq_def, if_neg hne] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨o, hprobe, h⟩ := h
    obtain ⟨hlook, hwfo⟩ := infer_probe_refines hrel hst he hprobe
    cases o with
    | some v =>
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨hrv, hstv⟩ := h
      subst hrv; subst hstv
      refine ⟨lst, ?_, hrel, hst, hwfo v rfl⟩
      simp only [hf, knot_succ_infer]
      exact memoEI_run_hit (by simpa using hlook.symm)
    | none =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i, hi, p, hbody, h⟩ := h
      obtain ⟨rr, st1⟩ := p
      have h2 : (match rr with
          | core.result.Result.Ok r1 => do
            let e1 ← kernel.expr.dup e
            let e2 ← kernel.expr.dup r1
            let q ← ron.hashmap.HashMap.insert hExpr eExpr st1.infer_c e1 e2
            ok (rr, { st1 with infer_c := q.2 })
          | core.result.Result.Err _ => ok (rr, st1))
          = ok (core.result.Result.Ok r, st') := h
      clear h
      cases rr with
      | Err ce => simp at h2
      | Ok r1 =>
        simp only [expr_dup_eq, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq,
          core.result.Result.Ok.injEq, exists_eq_left'] at h2
        obtain ⟨q, hins, hr1, hst'⟩ := h2
        subst hr1; subst hst'
        have hif := fuel_pred hf hi; subst hif
        obtain ⟨lst1, hrun, hrel1, hwf1, hwfr⟩ :=
          hbd.infer st fe d e r1 st1 hst hfe he hbody lst lfe hrel hfrel
        obtain ⟨hrel2, hwf2⟩ := infer_c_insert_refines hrel1 hwf1 he hwfr hins
        refine ⟨_, ?_, hrel2, hwf2, hwfr⟩
        simp only [hf, knot_succ_infer]
        exact memoEI_run_miss (by simpa using hlook.symm) hrun rfl
  -- `defeq`, memoized in `defeqC` under the pair key (`memoBI`)
  · intro st fe d a b r st' hst hfe ha hbb h lst lfe hrel hfrel
    rw [cached.core_c.defeq.eq_def, if_neg hne] at h
    simp only [expr_dup_eq, bind_eq_ok_iff, Result.ok.injEq, exists_eq_left'] at h
    obtain ⟨o, hprobe, h⟩ := h
    have hk : ExprPairWF (a, b) := ⟨ha, hbb⟩
    have hlook := defeq_probe_refines hrel hst hk hprobe
    cases o with
    | some v =>
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨hrv, hstv⟩ := h
      subst hrv; subst hstv
      refine ⟨lst, ?_, hrel, hst⟩
      simp only [hf, knot_succ_defeq]
      exact memoBI_run_hit (by simpa [absExprPair] using hlook.symm)
    | none =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i, hi, p, hbody, h⟩ := h
      obtain ⟨rr, st1⟩ := p
      have h2 : (match rr with
          | core.result.Result.Ok r1 => do
            let q ← ron.hashmap.HashMap.insert hExprPair eExprPair st1.defeq_c (a, b) r1
            ok (rr, { st1 with defeq_c := q.2 })
          | core.result.Result.Err _ => ok (rr, st1))
          = ok (core.result.Result.Ok r, st') := h
      clear h
      cases rr with
      | Err ce => simp at h2
      | Ok r1 =>
        simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq,
          core.result.Result.Ok.injEq] at h2
        obtain ⟨q, hins, hr1, hst'⟩ := h2
        subst hr1; subst hst'
        have hif := fuel_pred hf hi; subst hif
        obtain ⟨lst1, hrun, hrel1, hwf1⟩ :=
          hbd.defeq st fe d a b r1 st1 hst hfe ha hbb hbody lst lfe hrel hfrel
        obtain ⟨hrel2, hwf2⟩ := defeq_c_insert_refines hrel1 hwf1 hk hins
        refine ⟨_, ?_, hrel2, hwf2⟩
        simp only [hf, knot_succ_defeq]
        exact memoBI_run_miss (by simpa [absExprPair] using hlook.symm) hrun
  -- `annotate`, memoized in `annotC`
  · intro st fe d e r st' hst hfe he h lst lfe hrel hfrel
    rw [cached.core_c.annotate.eq_def, if_neg hne] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨o, hprobe, h⟩ := h
    obtain ⟨hlook, hwfo⟩ := annot_probe_refines hrel hst he hprobe
    cases o with
    | some v =>
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      obtain ⟨hrv, hstv⟩ := h
      subst hrv; subst hstv
      refine ⟨lst, ?_, hrel, hst, hwfo v rfl⟩
      simp only [hf, knot_succ_annotate]
      exact memoEI_run_hit (by simpa using hlook.symm)
    | none =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i, hi, p, hbody, h⟩ := h
      obtain ⟨rr, st1⟩ := p
      have h2 : (match rr with
          | core.result.Result.Ok r1 => do
            let e1 ← kernel.expr.dup e
            let e2 ← kernel.expr.dup r1
            let q ← ron.hashmap.HashMap.insert hExpr eExpr st1.annot_c e1 e2
            ok (rr, { st1 with annot_c := q.2 })
          | core.result.Result.Err _ => ok (rr, st1))
          = ok (core.result.Result.Ok r, st') := h
      clear h
      cases rr with
      | Err ce => simp at h2
      | Ok r1 =>
        simp only [expr_dup_eq, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq,
          core.result.Result.Ok.injEq, exists_eq_left'] at h2
        obtain ⟨q, hins, hr1, hst'⟩ := h2
        subst hr1; subst hst'
        have hif := fuel_pred hf hi; subst hif
        obtain ⟨lst1, hrun, hrel1, hwf1, hwfr⟩ :=
          hbd.annotate st fe d e r1 st1 hst hfe he hbody lst lfe hrel hfrel
        obtain ⟨hrel2, hwf2⟩ := annot_c_insert_refines hrel1 hwf1 he hwfr hins
        refine ⟨_, ?_, hrel2, hwf2, hwfr⟩
        simp only [hf, knot_succ_annotate]
        exact memoEI_run_miss (by simpa using hlook.symm) hrun rfl
  -- `inferIO`: the gate picks the map and the body, exactly as the Lean's
  -- `if mode.ioGate then … else …` does
  · intro st fe d e r st' hst hfe he h lst lfe hrel hfrel
    rw [cached.core_c.infer_io.eq_def, if_neg hne] at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨gate, hgate, h⟩ := h
    have hgb : gate = (absMode mode).ioGate := Env.io_gate_refines hgate
    cases gate with
    | true =>
      rw [if_pos rfl] at h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨o, hprobe, h⟩ := h
      obtain ⟨hlook, hwfo⟩ := infer_io_probe_refines hrel hst he hprobe
      cases o with
      | some v =>
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
        obtain ⟨hrv, hstv⟩ := h
        subst hrv; subst hstv
        refine ⟨lst, ?_, hrel, hst, hwfo v rfl⟩
        simp only [hf, knot_succ_inferIO, ← hgb, reduceIte]
        exact memoEI_run_hit (by simpa using hlook.symm)
      | none =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i, hi, p, hbody, h⟩ := h
        obtain ⟨rr, st1⟩ := p
        have h2 : (match rr with
            | core.result.Result.Ok r1 => do
              let e1 ← kernel.expr.dup e
              let e2 ← kernel.expr.dup r1
              let q ← ron.hashmap.HashMap.insert hExpr eExpr st1.infer_io_c e1 e2
              ok (rr, { st1 with infer_io_c := q.2 })
            | core.result.Result.Err _ => ok (rr, st1))
            = ok (core.result.Result.Ok r, st') := h
        clear h
        cases rr with
        | Err ce => simp at h2
        | Ok r1 =>
          simp only [expr_dup_eq, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq,
            core.result.Result.Ok.injEq, exists_eq_left'] at h2
          obtain ⟨q, hins, hr1, hst'⟩ := h2
          subst hr1; subst hst'
          have hif := fuel_pred hf hi; subst hif
          obtain ⟨lst1, hrun, hrel1, hwf1, hwfr⟩ :=
            hbd.inferIO st fe d e r1 st1 hst hfe he hbody lst lfe hrel hfrel
          obtain ⟨hrel2, hwf2⟩ := infer_io_c_insert_refines hrel1 hwf1 he hwfr hins
          refine ⟨_, ?_, hrel2, hwf2, hwfr⟩
          simp only [hf, knot_succ_inferIO, ← hgb, reduceIte]
          exact memoEI_run_miss (by simpa using hlook.symm) hrun rfl
    | false =>
      rw [if_neg (by simp)] at h
      simp only [bind_eq_ok_iff] at h
      obtain ⟨o, hprobe, h⟩ := h
      obtain ⟨hlook, hwfo⟩ := infer_probe_refines hrel hst he hprobe
      cases o with
      | some v =>
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
        obtain ⟨hrv, hstv⟩ := h
        subst hrv; subst hstv
        refine ⟨lst, ?_, hrel, hst, hwfo v rfl⟩
        simp only [hf, knot_succ_inferIO, ← hgb, Bool.false_eq_true, if_false]
        exact memoEI_run_hit (by simpa using hlook.symm)
      | none =>
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i, hi, p, hbody, h⟩ := h
        obtain ⟨rr, st1⟩ := p
        have h2 : (match rr with
            | core.result.Result.Ok r1 => do
              let e1 ← kernel.expr.dup e
              let e2 ← kernel.expr.dup r1
              let q ← ron.hashmap.HashMap.insert hExpr eExpr st1.infer_c e1 e2
              ok (rr, { st1 with infer_c := q.2 })
            | core.result.Result.Err _ => ok (rr, st1))
            = ok (core.result.Result.Ok r, st') := h
        clear h
        cases rr with
        | Err ce => simp at h2
        | Ok r1 =>
          simp only [expr_dup_eq, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq,
            core.result.Result.Ok.injEq, exists_eq_left'] at h2
          obtain ⟨q, hins, hr1, hst'⟩ := h2
          subst hr1; subst hst'
          have hif := fuel_pred hf hi; subst hif
          obtain ⟨lst1, hrun, hrel1, hwf1, hwfr⟩ :=
            hbd.infer st fe d e r1 st1 hst hfe he hbody lst lfe hrel hfrel
          obtain ⟨hrel2, hwf2⟩ := infer_c_insert_refines hrel1 hwf1 he hwfr hins
          refine ⟨_, ?_, hrel2, hwf2, hwfr⟩
          simp only [hf, knot_succ_inferIO, ← hgb, Bool.false_eq_true, if_false]
          exact memoEI_run_miss (by simpa using hlook.symm) hrun rfl

/-! ## The induction

`Nat.rec` on the fuel's value, exactly as task #5 did for
`leq_core`/`rest`/`by_cases`: the wrappers at `0` are `wrappers_zero`, the
wrappers at `n + 1` are `wrappers_succ` on the bodies at `n`, and the bodies
at any fuel are the arms applied to the wrappers at the *same* fuel (the
decrement lives in the wrapper).  The arms are the hypothesis; they are tasks
#54 and on. -/

theorem knot_induction {mode : env.CheckMode}
    (harms : ∀ fuel, Wrappers mode fuel → Bodies mode fuel) (fuel : Std.U64) :
    KnotSpec mode fuel := by
  have key : ∀ n : Nat, ∀ f : Std.U64, f.val = n → Wrappers mode f := by
    intro n
    induction n with
    | zero =>
      intro f hfv
      have h0 : f = 0#u64 := u64_val_inj (by rw [hfv]; rfl)
      subst h0; exact wrappers_zero mode
    | succ n ih =>
      intro f hfv
      have hlt : n < 2 ^ Std.UScalarTy.U64.numBits := by
        have h1 : f.val < 2 ^ Std.UScalarTy.U64.numBits := f.bv.isLt
        omega
      have hg : (Std.UScalar.ofNatCore n hlt : Std.U64).val = n :=
        Std.UScalar.ofNatCore_val_eq hlt
      exact wrappers_succ (by rw [hfv, hg]) (harms _ (ih _ hg))
  exact ⟨key fuel.val fuel rfl, harms fuel (key fuel.val fuel rfl)⟩

end ConRon.Refine.Core

/-! ## Axiom census (DESIGN.md §3.5) -/

section
open ConRon.Refine.Core

/-- info: 'ConRon.Refine.Core.wrappers_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wrappers_succ

/-- info: 'ConRon.Refine.Core.knot_induction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms knot_induction

end

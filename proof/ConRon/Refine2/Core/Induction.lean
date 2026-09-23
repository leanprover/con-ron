/-
# `ConRon.Refine2.Core.Induction` — `KnotRel` tied by induction on the fuel

**Task #97-P5-Core, the knot step.**  `Core/KnotRel.lean` states the two
relations; this file is the induction that ties them:

    knotRel_zero  :                KnotRel 0
    knotRel_succ  : BodyRel f  →   KnotRel (f + 1)
    knot_rel      : (∀ f, KnotRel f → BodyRel f) → ∀ f, KnotRel f

The premise of the last is `Core/Arms/*`'s obligation and the tier's real
work; everything here is closed.

## The step, six times, and the shape of each

Every one of the six port entries has the same five-branch skeleton:

    if fuel == 0                      -- the twin's `coreKnot … 0` slot
    else if <stuck tag>               -- `whnf_core` and `whnf` only
    else if lane == LANE_GATED        -- the P knot, NO memo
    else if lane == LANE_IO           -- `infer` and `infer_io` only
    else  probe; body; set            -- the memoized full lane

and the twin's `coreKnot (f + 1)` slot is the last three lines of that
verbatim (DESIGN §8.4's deviation 6 put the probe inline in the slot).  So
each field is: `absU fu = f + 1` forces the `fuel ≠ 0` arm; the lane `if`s
line up with `laneKnot`'s own `if`s by `laneKnot_gated` / `laneKnot_io` /
`laneKnot_of_ne`; the probe is `Core/Probes.lean`'s `*_probe_abs`, the body is
`BodyRel`'s field, the write is `*_set_run`.

## The three divergences the step had to prove, not assume

1. **The stuck-tag short circuit, which used to be an asymmetry and is not
   one any more.**  `knot_whnf_core` answers `Ok(e.dup2())` at a
   `sort`/`fvar`/`forallE`/`lam`/`const`/`lit` handle *before* it looks at the
   lane — task #97-P6-7's lever 2 hoisted it out of the body in the PORT — and
   the twin originally hoisted it into the memoized slot only, so the gated
   lane had no test at all and `BodyRel` carried two `stuckGated*` obligations
   about `whnfCoreBodyGated`.  Task #97-P3-CoreWalks put the test in
   `coreKnotGated`'s two reduction slots and task #97-P5-Core-2 put it in the
   `| fuel + 1 =>` branch ALONE, leaving `coreKnotGated 0` the unconditional
   `fail` the port's `fuel = 0` arm is.  Both slots now test exactly where the
   port does, the step reads the agreement off the knot's own equation, and
   neither `BodyRel` nor `KnotRel` carries anything for it.
2. **At `LANE_IO`, `knot_whnf_core` / `knot_whnf` / `knot_defeq` /
   `knot_annotate` fall through to the FULL lane's memoized arm**, and
   `coreKnotIO (f + 1)`'s four corresponding slots are literally
   `(coreKnot mode fe id (f + 1)).whnfCore` and its three siblings — the same
   knot at the SAME fuel.  So those four fields at `LANE_IO` are the field at
   `LANE_FULL`, and the proof is one `rw`.
3. **`knot_infer_io`'s selector.**  The port reads
   `kernel::env::io_gate(mode)` and the twin reads `mode.ioGate`; the port's
   doc comment says `mode.betaGate`, which the code does not do.  The comment
   is stale — see the task's report — and the two selectors agree because
   `io_gate` is constantly `true` at both modes and so is `CheckMode.ioGate`.
-/
import ConRon.Refine2.Core.KnotRel

open Aeneas Aeneas.Std Result
open ConRon.Generated

attribute [-grind] U32.bv_eq_imp_eq UScalar.val_eq_imp

-- `defeqBody` and `whnfBody` are the loop at a `100000` literal, so a `rfl`
-- that unfolds them walks the numeral; every slot equation below rewrites
-- with the knot's own equation lemma instead, and this budget covers the
-- residual record projections.
set_option maxRecDepth 4000

namespace ConRon.Refine2

open ConRon.Arena
open ConRon.Refine2.ExprOps (EResolves)

/-! ## The fuel reading

`absU fu = 0` is `fu = 0#u64` and `absU fu = f + 1` is `fu ≠ 0#u64` with
`absU (fu - 1) = f`: the two halves of round 3's twelve-line fuel shape step,
here stated once for the whole tier because all six entries decrement the same
way. -/

theorem absU_eq_zero {fu : Std.U64} (h : absU fu = 0) : fu = 0#u64 := by
  apply UScalar.eq_imp
  simpa using h

theorem absU_ne_zero {fu : Std.U64} {f : Nat} (h : absU fu = f + 1) :
    ¬ fu = 0#u64 := by
  intro hz
  rw [hz] at h
  simp [absU] at h

/-- The port's `fuel - 1` at `absU fu = f + 1`. -/
theorem absU_pred {fu i : Std.U64} {f : Nat} (hf : absU fu = f + 1)
    (h : fu - 1#u64 = ok i) : absU i = f := by
  obtain ⟨-, hv⟩ := absU_sub_one h
  omega

/-! ## The twin's fuel-exhausted record

All three knots agree at `0`: six slots, each `fail (.internal …)`.  The
reading the base case needs is therefore one lemma per slot, and each is
`rfl` after `laneKnot` picks its branch. -/

/-- Each knot's own fuel-exhausted slot, through its equation lemma: `rfl`
alone would make the kernel whnf the WHOLE definition (all six bodies in the
successor branch), which is 45 s of kernel time on this file; rewriting with
the equation lemma first leaves a six-`fail` record. -/
theorem coreKnot_zero_run (mode fe d a b lst) :
    (((coreKnot mode fe id 0).whnfCore d a).run lst
        = .error (.internal "fuel exhausted: whnfCore")) ∧
      (((coreKnot mode fe id 0).whnf d a).run lst
        = .error (.internal "fuel exhausted: whnf")) ∧
      (((coreKnot mode fe id 0).infer d a).run lst
        = .error (.internal "fuel exhausted: infer")) ∧
      (((coreKnot mode fe id 0).inferIO d a).run lst
        = .error (.internal "fuel exhausted: infer")) ∧
      (((coreKnot mode fe id 0).defeq d a b).run lst
        = .error (.internal "fuel exhausted: defeq")) ∧
      (((coreKnot mode fe id 0).annotate d a).run lst
        = .error (.internal "fuel exhausted: annotate")) := by
  rw [coreKnot]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The gated knot's fuel-0 slots, all six again** (task #97-P5-Core-2).
Task #97-P3-CoreWalks' hoist had made `coreKnotGated 0`'s `whnfCore` and
`whnf` answer `pure e` at a stuck tag, where the port's `knot_*` test
`fuel = 0` FIRST and raise `Internal` whatever the tag is; §11(b) of task
#97-P5-Arms asked for the test to sit in the `| fuel + 1 =>` branch only, and
with that this lemma is the same six conjuncts as its two siblings and
`KnotRel`'s two reduction fields carry no side condition. -/
theorem coreKnotGated_zero_run (mode fe d a b lst) :
    (((coreKnotGated mode fe 0).whnfCore d a).run lst
        = .error (.internal "fuel exhausted: whnfCore")) ∧
      (((coreKnotGated mode fe 0).whnf d a).run lst
        = .error (.internal "fuel exhausted: whnf")) ∧
      (((coreKnotGated mode fe 0).infer d a).run lst
        = .error (.internal "fuel exhausted: infer")) ∧
      (((coreKnotGated mode fe 0).inferIO d a).run lst
        = .error (.internal "fuel exhausted: infer")) ∧
      (((coreKnotGated mode fe 0).defeq d a b).run lst
        = .error (.internal "fuel exhausted: defeq")) ∧
      (((coreKnotGated mode fe 0).annotate d a).run lst
        = .error (.internal "fuel exhausted: annotate")) := by
  rw [coreKnotGated]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem coreKnotIO_zero_run (mode fe d a b lst) :
    (((coreKnotIO mode fe 0).whnfCore d a).run lst
        = .error (.internal "fuel exhausted: whnfCore")) ∧
      (((coreKnotIO mode fe 0).whnf d a).run lst
        = .error (.internal "fuel exhausted: whnf")) ∧
      (((coreKnotIO mode fe 0).infer d a).run lst
        = .error (.internal "fuel exhausted: infer")) ∧
      (((coreKnotIO mode fe 0).inferIO d a).run lst
        = .error (.internal "fuel exhausted: infer")) ∧
      (((coreKnotIO mode fe 0).defeq d a b).run lst
        = .error (.internal "fuel exhausted: defeq")) ∧
      (((coreKnotIO mode fe 0).annotate d a).run lst
        = .error (.internal "fuel exhausted: annotate")) := by
  rw [coreKnotIO]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The two reduction slots at fuel `0`, **at every lane** — the gated one
included, since task #97-P5-Core-2 gave `coreKnotGated 0` back its
unconditional `fail`. -/
theorem laneKnot_zero_whnfCore (mode fe lane d e lst) :
    ((laneKnot mode fe lane 0).whnfCore d e).run lst
      = .error (.internal "fuel exhausted: whnfCore") := by
  rw [laneKnot]; split
  · exact (coreKnotGated_zero_run mode fe d e e lst).1
  · split
    · exact (coreKnotIO_zero_run mode fe d e e lst).1
    · exact (coreKnot_zero_run mode fe d e e lst).1

theorem laneKnot_zero_whnf (mode fe lane d e lst) :
    ((laneKnot mode fe lane 0).whnf d e).run lst
      = .error (.internal "fuel exhausted: whnf") := by
  rw [laneKnot]; split
  · exact (coreKnotGated_zero_run mode fe d e e lst).2.1
  · split
    · exact (coreKnotIO_zero_run mode fe d e e lst).2.1
    · exact (coreKnot_zero_run mode fe d e e lst).2.1

theorem laneKnot_zero_infer (mode fe lane d e lst) :
    ((laneKnot mode fe lane 0).infer d e).run lst
      = .error (.internal "fuel exhausted: infer") := by
  rw [laneKnot]; split
  · exact (coreKnotGated_zero_run mode fe d e e lst).2.2.1
  · split
    · exact (coreKnotIO_zero_run mode fe d e e lst).2.2.1
    · exact (coreKnot_zero_run mode fe d e e lst).2.2.1

theorem laneKnot_zero_inferIO (mode fe lane d e lst) :
    ((laneKnot mode fe lane 0).inferIO d e).run lst
      = .error (.internal "fuel exhausted: infer") := by
  rw [laneKnot]; split
  · exact (coreKnotGated_zero_run mode fe d e e lst).2.2.2.1
  · split
    · exact (coreKnotIO_zero_run mode fe d e e lst).2.2.2.1
    · exact (coreKnot_zero_run mode fe d e e lst).2.2.2.1

theorem laneKnot_zero_defeq (mode fe lane d a b lst) :
    ((laneKnot mode fe lane 0).defeq d a b).run lst
      = .error (.internal "fuel exhausted: defeq") := by
  rw [laneKnot]; split
  · exact (coreKnotGated_zero_run mode fe d a b lst).2.2.2.2.1
  · split
    · exact (coreKnotIO_zero_run mode fe d a b lst).2.2.2.2.1
    · exact (coreKnot_zero_run mode fe d a b lst).2.2.2.2.1

theorem laneKnot_zero_annotate (mode fe lane d e lst) :
    ((laneKnot mode fe lane 0).annotate d e).run lst
      = .error (.internal "fuel exhausted: annotate") := by
  rw [laneKnot]; split
  · exact (coreKnotGated_zero_run mode fe d e e lst).2.2.2.2.2
  · split
    · exact (coreKnotIO_zero_run mode fe d e e lst).2.2.2.2.2
    · exact (coreKnot_zero_run mode fe d e e lst).2.2.2.2.2

/-! ## The base case

At fuel `0` the port raises `Internal(M_FUEL_*)` and the twin throws
`.internal`, so every field is `AOut.err` at the `internal` kind.  The port's
`Array::to_slice` and `code_points` are `Result`-valued but their VALUES are
never compared: `AErrSim` looks at the CONSTRUCTOR only (DESIGN §3.1, messages
are never compared). -/

theorem knotRel_zero : KnotRel 0 := by
  constructor
  · intro pers vis st mode lane fu fe lfe depth e lst o _ _ _ hf hrun
    rw [arena.core.knot_whnf_core, if_pos (absU_eq_zero hf)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hr] at hrun
    rw [← Result.ok_injective hrun]
    exact AOut₀.err (AErrSim.internal (laneKnot_zero_whnfCore _ _ _ _ _ _))
  · intro pers vis st mode lane fu fe lfe depth e lst o _ _ _ hf hrun
    rw [arena.core.knot_whnf, if_pos (absU_eq_zero hf)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hr] at hrun
    rw [← Result.ok_injective hrun]
    exact AOut₀.err (AErrSim.internal (laneKnot_zero_whnf _ _ _ _ _ _))
  · intro pers vis st mode lane fu fe lfe depth e lst o _ _ _ hf hrun
    rw [arena.core.knot_infer, if_pos (absU_eq_zero hf)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hr] at hrun
    rw [← Result.ok_injective hrun]
    exact AOut₀.err (AErrSim.internal (laneKnot_zero_infer _ _ _ _ _ _))
  · intro pers vis st mode lane fu fe lfe depth e lst o _ _ _ hf hrun
    rw [arena.core.knot_infer_io, if_pos (absU_eq_zero hf)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hr] at hrun
    rw [← Result.ok_injective hrun]
    exact AOut₀.err (AErrSim.internal (laneKnot_zero_inferIO _ _ _ _ _ _))
  · intro pers vis st mode lane fu fe lfe depth a b lst o _ _ _ hf hrun
    rw [arena.core.knot_defeq, if_pos (absU_eq_zero hf)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hr] at hrun
    rw [← Result.ok_injective hrun]
    exact AOut₀.err (AErrSim.internal (laneKnot_zero_defeq _ _ _ _ _ _ _))
  · intro pers vis st mode lane fu fe lfe depth e lst o _ _ _ hf hrun
    rw [arena.core.knot_annotate, if_pos (absU_eq_zero hf)] at hrun
    obtain ⟨s, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨v, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨r, hr, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    rw [fail_run hr] at hrun
    rw [← Result.ok_injective hrun]
    exact AOut₀.err (AErrSim.internal (laneKnot_zero_annotate _ _ _ _ _ _))

/-! ## The twin's `do` block, split at a bind -/

theorem am_run_bind {α β : Type} (m : AM α) (k : α → AM β) (lst : AState) :
    ((m >>= k)).run lst = (m.run lst) >>= fun p => (k p.1).run p.2 := rfl

/-! ## The three knots' `annotate` slot at `f + 1` -/

theorem coreKnotGated_succ_annotate (mode lfe f d e) :
    (coreKnotGated mode lfe (f + 1)).annotate d e
      = annotateBody (coreKnotGated mode lfe f) lfe d e := by
  rw [coreKnotGated]

theorem coreKnotIO_succ_annotate (mode lfe f d e) :
    (coreKnotIO mode lfe (f + 1)).annotate d e
      = (coreKnot mode lfe id (f + 1)).annotate d e := by
  rw [coreKnotIO]

theorem coreKnot_succ_annotate_split (mode lfe f d e lst) :
    ((coreKnot mode lfe id (f + 1)).annotate d e).run lst
      = (((match lst.caches.annotC[e]? with
            | some x => pure x
            | none => do
                let x ← annotateBody (coreKnot mode lfe id f) lfe d e
                annotSet e x
                pure x) : AM EIdx)).run lst := by
  rw [coreKnot]; rfl

theorem coreKnot_succ_annotate_hit (mode lfe f d e lst x)
    (h : lst.caches.annotC[e]? = some x) :
    ((coreKnot mode lfe id (f + 1)).annotate d e).run lst = .ok (x, lst) := by
  rw [coreKnot_succ_annotate_split, h]; rfl

theorem coreKnot_succ_annotate_miss (mode lfe f d e lst)
    (h : lst.caches.annotC[e]? = none) :
    ((coreKnot mode lfe id (f + 1)).annotate d e).run lst
      = (((do
            let x ← annotateBody (coreKnot mode lfe id f) lfe d e
            annotSet e x
            pure x) : AM EIdx)).run lst := by
  rw [coreKnot_succ_annotate_split, h]

/-! ## The `annotate` field of the step -/

theorem knotRel_succ_annotate {f : Nat} (hb : BodyRel f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f + 1)
    (hrun : arena.core.knot_annotate pers vis st mode lane fu fe depth e = ok o) :
    Sim₀ absEIdx pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).annotate
        (absU depth) (absEIdx e)) := by
  rw [arena.core.knot_annotate, if_neg (absU_ne_zero hf)] at hrun
  by_cases hg : lane = arena.core.LANE_GATED
  · -- the P lane: no memo, the body at the gated knot one level down
    subst hg
    rw [if_pos rfl] at hrun
    obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 := hb.annotate hrel hinv hctx (absU_pred hf hi) hrun
    rw [laneKnot_gated] at h2
    rw [laneKnot_gated, coreKnotGated_succ_annotate]
    exact h2
  · rw [if_neg hg] at hrun
    -- the memoized lane: `LANE_FULL`, and `LANE_IO` falls through to it
    have htwin : (laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).annotate
        (absU depth) (absEIdx e)
        = (coreKnot (ConRon.Refine.absMode mode) lfe id (f + 1)).annotate
            (absU depth) (absEIdx e) := by
      by_cases hio : lane = arena.core.LANE_IO
      · rw [hio, laneKnot_io, coreKnotIO_succ_annotate]
      · rw [laneKnot_of_ne _ _ _ hg hio]
    rw [show Sim₀ absEIdx pers lst o
          ((laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).annotate
            (absU depth) (absEIdx e))
        = Sim₀ absEIdx pers lst o
          ((coreKnot (ConRon.Refine.absMode mode) lfe id (f + 1)).annotate
            (absU depth) (absEIdx e)) from by rw [htwin]]
    have hlane : laneKnot (ConRon.Refine.absMode mode) lfe arena.core.LANE_FULL f
        = coreKnot (ConRon.Refine.absMode mode) lfe id f := laneKnot_full _ _ _
    obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hprobe := annot_probe_abs hrel hinv hop
    cases hoc : op with
    | some x =>
      rw [hoc] at hrun hprobe
      have ho : (core.result.Result.Ok x, st) = o := Result.ok_injective hrun
      rw [← ho]
      exact AOut₀.ok (coreKnot_succ_annotate_hit _ _ _ _ _ _ _ hprobe.symm)
        hrel hinv
    | none =>
      rw [hoc] at hrun hprobe
      have htw := (coreKnot_succ_annotate_miss (ConRon.Refine.absMode mode) lfe f
        (absU depth) (absEIdx e) lst hprobe.symm).trans
        (am_run_bind (annotateBody (coreKnot (ConRon.Refine.absMode mode) lfe id f)
          lfe (absU depth) (absEIdx e)) _ lst)
      obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨p, hbd, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r, st1⟩ := p
      have hbody := hb.annotate hrel hinv hctx (absU_pred hf hi) hbd
      rw [hlane] at hbody
      cases r with
      | Err er =>
        have ho : (core.result.Result.Err er, st1) = o := Result.ok_injective hrun
        rw [← ho]
        exact AOut₀.err (AErrSim.of_eq (AErrSim.bind (Sim₀.apply_err hbody) _) htw)
      | Ok r1 =>
        obtain ⟨lst1, hb1, hrel1, hinv1⟩ := Sim₀.apply hbody
        obtain ⟨st2, hs2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have ho : (core.result.Result.Ok r1, st2) = o := Result.ok_injective hrun
        rw [← ho]
        obtain ⟨lst2, hset, hrel2, hinv2⟩ :=
          SimS₀.apply (annot_set_run hrel1 hinv1 hs2)
        refine AOut₀.ok ?_ hrel2 hinv2
        rw [htw, hb1]
        show ((do annotSet (absEIdx e) (absEIdx r1)
                  pure (absEIdx r1) : AM EIdx)).run lst1 = _
        rw [am_run_bind, hset]
        rfl

/-! ## The `defeq` field -/

theorem coreKnotGated_succ_defeq (mode lfe f d a b) :
    (coreKnotGated mode lfe (f + 1)).defeq d a b
      = defeqBody mode (coreKnotGated mode lfe f) lfe d a b := by
  rw [coreKnotGated]

theorem coreKnotIO_succ_defeq (mode lfe f d a b) :
    (coreKnotIO mode lfe (f + 1)).defeq d a b
      = (coreKnot mode lfe id (f + 1)).defeq d a b := by
  rw [coreKnotIO]

theorem coreKnot_succ_defeq_split (mode lfe f d a b lst) :
    ((coreKnot mode lfe id (f + 1)).defeq d a b).run lst
      = (((match lst.caches.defeqC[(a, b)]? with
            | some x => pure x
            | none => do
                let x ← defeqBody mode (coreKnot mode lfe id f) lfe d a b
                defeqSet a b x
                pure x) : AM Bool)).run lst := by
  rw [coreKnot]; rfl

theorem coreKnot_succ_defeq_hit (mode lfe f d a b lst x)
    (h : lst.caches.defeqC[(a, b)]? = some x) :
    ((coreKnot mode lfe id (f + 1)).defeq d a b).run lst = .ok (x, lst) := by
  rw [coreKnot_succ_defeq_split, h]; rfl

theorem coreKnot_succ_defeq_miss (mode lfe f d a b lst)
    (h : lst.caches.defeqC[(a, b)]? = none) :
    ((coreKnot mode lfe id (f + 1)).defeq d a b).run lst
      = (((do
            let x ← defeqBody mode (coreKnot mode lfe id f) lfe d a b
            defeqSet a b x
            pure x) : AM Bool)).run lst := by
  rw [coreKnot_succ_defeq_split, h]

theorem knotRel_succ_defeq {f : Nat} (hb : BodyRel f)
    {pers vis st mode lane fu fe lfe depth a b lst o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f + 1)
    (hrun : arena.core.knot_defeq pers vis st mode lane fu fe depth a b = ok o) :
    Sim₀ id pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).defeq
        (absU depth) (absEIdx a) (absEIdx b)) := by
  rw [arena.core.knot_defeq, if_neg (absU_ne_zero hf)] at hrun
  by_cases hg : lane = arena.core.LANE_GATED
  · subst hg
    rw [if_pos rfl] at hrun
    obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 := hb.defeq hrel hinv hctx (absU_pred hf hi) hrun
    rw [laneKnot_gated] at h2
    rw [laneKnot_gated, coreKnotGated_succ_defeq]
    exact h2
  · rw [if_neg hg] at hrun
    have htwin : (laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).defeq
        (absU depth) (absEIdx a) (absEIdx b)
        = (coreKnot (ConRon.Refine.absMode mode) lfe id (f + 1)).defeq
            (absU depth) (absEIdx a) (absEIdx b) := by
      by_cases hio : lane = arena.core.LANE_IO
      · rw [hio, laneKnot_io, coreKnotIO_succ_defeq]
      · rw [laneKnot_of_ne _ _ _ hg hio]
    rw [show Sim₀ id pers lst o
          ((laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).defeq
            (absU depth) (absEIdx a) (absEIdx b))
        = Sim₀ id pers lst o
          ((coreKnot (ConRon.Refine.absMode mode) lfe id (f + 1)).defeq
            (absU depth) (absEIdx a) (absEIdx b)) from by rw [htwin]]
    have hlane : laneKnot (ConRon.Refine.absMode mode) lfe arena.core.LANE_FULL f
        = coreKnot (ConRon.Refine.absMode mode) lfe id f := laneKnot_full _ _ _
    obtain ⟨k, hk, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have hprobe := defeq_probe_abs hrel hinv hop
    rw [eidx_pair_abs hk] at hprobe
    cases hoc : op with
    | some x =>
      rw [hoc] at hrun hprobe
      have ho : (core.result.Result.Ok x, st) = o := Result.ok_injective hrun
      rw [← ho]
      exact AOut₀.ok (coreKnot_succ_defeq_hit _ _ _ _ _ _ _ _ hprobe.symm)
        hrel hinv
    | none =>
      rw [hoc] at hrun hprobe
      have htw := (coreKnot_succ_defeq_miss (ConRon.Refine.absMode mode) lfe f
        (absU depth) (absEIdx a) (absEIdx b) lst hprobe.symm).trans
        (am_run_bind (defeqBody (ConRon.Refine.absMode mode)
          (coreKnot (ConRon.Refine.absMode mode) lfe id f) lfe
          (absU depth) (absEIdx a) (absEIdx b)) _ lst)
      obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨p, hbd, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      obtain ⟨r, st1⟩ := p
      have hbody := hb.defeq hrel hinv hctx (absU_pred hf hi) hbd
      rw [hlane] at hbody
      cases r with
      | Err er =>
        have ho : (core.result.Result.Err er, st1) = o := Result.ok_injective hrun
        rw [← ho]
        exact AOut₀.err (AErrSim.of_eq (AErrSim.bind (Sim₀.apply_err hbody) _) htw)
      | Ok r1 =>
        obtain ⟨lst1, hb1, hrel1, hinv1⟩ := Sim₀.apply hbody
        obtain ⟨st2, hs2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        have ho : (core.result.Result.Ok r1, st2) = o := Result.ok_injective hrun
        rw [← ho]
        obtain ⟨lst2, hset, hrel2, hinv2⟩ :=
          SimS₀.apply (defeq_set_run hrel1 hinv1 hs2)
        refine AOut₀.ok ?_ hrel2 hinv2
        rw [htw, hb1]
        show ((do defeqSet (absEIdx a) (absEIdx b) r1
                  pure r1 : AM Bool)).run lst1 = _
        rw [am_run_bind, hset]
        rfl

/-! ## The `infer` field -/

theorem coreKnotGated_succ_infer (mode lfe f d e) :
    (coreKnotGated mode lfe (f + 1)).infer d e
      = inferBody mode (coreKnotGated mode lfe f) lfe d e := by
  rw [coreKnotGated]

theorem coreKnotIO_succ_infer (mode lfe f d e) :
    (coreKnotIO mode lfe (f + 1)).infer d e
      = inferBodyIO mode (coreKnotIO mode lfe f) lfe d e := by
  rw [coreKnotIO]

theorem coreKnot_succ_infer_split (mode lfe f d e lst) :
    ((coreKnot mode lfe id (f + 1)).infer d e).run lst
      = (((match lst.caches.inferC[e]? with
            | some x => pure x
            | none => do
                let x ← inferBody mode (coreKnot mode lfe id f) lfe d e
                inferSet e x
                pure x) : AM EIdx)).run lst := by
  rw [coreKnot]; rfl

theorem coreKnot_succ_infer_hit (mode lfe f d e lst x)
    (h : lst.caches.inferC[e]? = some x) :
    ((coreKnot mode lfe id (f + 1)).infer d e).run lst = .ok (x, lst) := by
  rw [coreKnot_succ_infer_split, h]; rfl

theorem coreKnot_succ_infer_miss (mode lfe f d e lst)
    (h : lst.caches.inferC[e]? = none) :
    ((coreKnot mode lfe id (f + 1)).infer d e).run lst
      = (((do
            let x ← inferBody mode (coreKnot mode lfe id f) lfe d e
            inferSet e x
            pure x) : AM EIdx)).run lst := by
  rw [coreKnot_succ_infer_split, h]

theorem knotRel_succ_infer {f : Nat} (hb : BodyRel f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f + 1)
    (hrun : arena.core.knot_infer pers vis st mode lane fu fe depth e = ok o) :
    Sim₀ absEIdx pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).infer
        (absU depth) (absEIdx e)) := by
  rw [arena.core.knot_infer, if_neg (absU_ne_zero hf)] at hrun
  by_cases hg : lane = arena.core.LANE_GATED
  · subst hg
    rw [if_pos rfl] at hrun
    obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 := hb.infer hrel hinv hctx (absU_pred hf hi) hrun
    rw [laneKnot_gated] at h2
    rw [laneKnot_gated, coreKnotGated_succ_infer]
    exact h2
  · rw [if_neg hg] at hrun
    by_cases hio : lane = arena.core.LANE_IO
    · subst hio
      rw [if_pos rfl] at hrun
      obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have h2 := hb.inferIO hrel hinv hctx (absU_pred hf hi) (Or.inr rfl) hrun
      rw [laneKnotAt_false, laneKnot_io] at h2
      rw [laneKnot_io, coreKnotIO_succ_infer]
      exact h2
    · rw [if_neg hio] at hrun
      rw [show Sim₀ absEIdx pers lst o
            ((laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).infer
              (absU depth) (absEIdx e))
          = Sim₀ absEIdx pers lst o
            ((coreKnot (ConRon.Refine.absMode mode) lfe id (f + 1)).infer
              (absU depth) (absEIdx e)) from by rw [laneKnot_of_ne _ _ _ hg hio]]
      have hlane : laneKnot (ConRon.Refine.absMode mode) lfe arena.core.LANE_FULL f
          = coreKnot (ConRon.Refine.absMode mode) lfe id f := laneKnot_full _ _ _
      obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hprobe := infer_probe_abs hrel hinv hop
      cases hoc : op with
      | some x =>
        rw [hoc] at hrun hprobe
        have ho : (core.result.Result.Ok x, st) = o := Result.ok_injective hrun
        rw [← ho]
        exact AOut₀.ok (coreKnot_succ_infer_hit _ _ _ _ _ _ _ hprobe.symm)
          hrel hinv
      | none =>
        rw [hoc] at hrun hprobe
        have htw := (coreKnot_succ_infer_miss (ConRon.Refine.absMode mode) lfe f
          (absU depth) (absEIdx e) lst hprobe.symm).trans
          (am_run_bind (inferBody (ConRon.Refine.absMode mode)
            (coreKnot (ConRon.Refine.absMode mode) lfe id f) lfe
            (absU depth) (absEIdx e)) _ lst)
        obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨p, hbd, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r, st1⟩ := p
        have hbody := hb.infer hrel hinv hctx (absU_pred hf hi) hbd
        rw [hlane] at hbody
        cases r with
        | Err er =>
          have ho : (core.result.Result.Err er, st1) = o := Result.ok_injective hrun
          rw [← ho]
          exact AOut₀.err (AErrSim.of_eq (AErrSim.bind (Sim₀.apply_err hbody) _) htw)
        | Ok r1 =>
          obtain ⟨lst1, hb1, hrel1, hinv1⟩ := Sim₀.apply hbody
          obtain ⟨st2, hs2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have ho : (core.result.Result.Ok r1, st2) = o := Result.ok_injective hrun
          rw [← ho]
          obtain ⟨lst2, hset, hrel2, hinv2⟩ :=
            SimS₀.apply (infer_set_run hrel1 hinv1 hs2)
          refine AOut₀.ok ?_ hrel2 hinv2
          rw [htw, hb1]
          show ((do inferSet (absEIdx e) (absEIdx r1)
                    pure (absEIdx r1) : AM EIdx)).run lst1 = _
          rw [am_run_bind, hset]
          rfl

/-! ## The `inferIO` field -/

/-- `kernel::env::io_gate` against `CheckMode.ioGate` — **both are constantly
`true`**, so the port's `else` arm (which probes the FULL grade's table) is
unreachable and the twin's `else` arm is dead, which is what the twin's own
note says.  The port's doc comment claims the selector is `mode.betaGate`;
the code says `io_gate`, and the code is what this reads. -/
theorem io_gate_abs {mode : kernel.env.CheckMode} {b : Bool}
    (h : kernel.env.io_gate mode = ok b) : b = true := by
  cases mode <;> (rw [kernel.env.io_gate] at h; exact (Result.ok_injective h).symm)

theorem coreKnotGated_succ_inferIO (mode lfe f d e) :
    (coreKnotGated mode lfe (f + 1)).inferIO d e
      = inferBody mode (coreKnotGated mode lfe f) lfe d e := by
  rw [coreKnotGated]

theorem coreKnotIO_succ_inferIO (mode lfe f d e) :
    (coreKnotIO mode lfe (f + 1)).inferIO d e
      = inferBodyIO mode (coreKnotIO mode lfe f) lfe d e := by
  rw [coreKnotIO]

theorem coreKnot_succ_inferIO_split (mode lfe f d e lst) :
    ((coreKnot mode lfe id (f + 1)).inferIO d e).run lst
      = (((match lst.caches.inferIOC[e]? with
            | some x => pure x
            | none => do
                let x ← inferBodyIO mode ((coreKnot mode lfe id f).ioView) lfe d e
                inferIOSet e x
                pure x) : AM EIdx)).run lst := by
  rw [coreKnot]; rfl

theorem coreKnot_succ_inferIO_hit (mode lfe f d e lst x)
    (h : lst.caches.inferIOC[e]? = some x) :
    ((coreKnot mode lfe id (f + 1)).inferIO d e).run lst = .ok (x, lst) := by
  rw [coreKnot_succ_inferIO_split, h]; rfl

theorem coreKnot_succ_inferIO_miss (mode lfe f d e lst)
    (h : lst.caches.inferIOC[e]? = none) :
    ((coreKnot mode lfe id (f + 1)).inferIO d e).run lst
      = (((do
            let x ← inferBodyIO mode ((coreKnot mode lfe id f).ioView) lfe d e
            inferIOSet e x
            pure x) : AM EIdx)).run lst := by
  rw [coreKnot_succ_inferIO_split, h]

theorem knotRel_succ_inferIO {f : Nat} (hb : BodyRel f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f + 1)
    (hrun : arena.core.knot_infer_io pers vis st mode lane fu fe depth e = ok o) :
    Sim₀ absEIdx pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).inferIO
        (absU depth) (absEIdx e)) := by
  rw [arena.core.knot_infer_io, if_neg (absU_ne_zero hf)] at hrun
  by_cases hg : lane = arena.core.LANE_GATED
  · subst hg
    rw [if_pos rfl] at hrun
    obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have h2 := hb.infer hrel hinv hctx (absU_pred hf hi) hrun
    rw [laneKnot_gated] at h2
    rw [laneKnot_gated, coreKnotGated_succ_inferIO]
    exact h2
  · rw [if_neg hg] at hrun
    by_cases hio : lane = arena.core.LANE_IO
    · subst hio
      rw [if_pos rfl] at hrun
      obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have h2 := hb.inferIO hrel hinv hctx (absU_pred hf hi) (Or.inr rfl) hrun
      rw [laneKnotAt_false, laneKnot_io] at h2
      rw [laneKnot_io, coreKnotIO_succ_inferIO]
      exact h2
    · rw [if_neg hio] at hrun
      rw [show Sim₀ absEIdx pers lst o
            ((laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).inferIO
              (absU depth) (absEIdx e))
          = Sim₀ absEIdx pers lst o
            ((coreKnot (ConRon.Refine.absMode mode) lfe id (f + 1)).inferIO
              (absU depth) (absEIdx e)) from by rw [laneKnot_of_ne _ _ _ hg hio]]
      obtain ⟨bg, hbg, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      rw [io_gate_abs hbg, if_pos rfl] at hrun
      have hlane : (laneKnot (ConRon.Refine.absMode mode) lfe
            arena.core.LANE_FULL f).ioView
          = (coreKnot (ConRon.Refine.absMode mode) lfe id f).ioView := by
        rw [laneKnot_full]
      obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hprobe := infer_io_probe_abs hrel hinv hop
      cases hoc : op with
      | some x =>
        rw [hoc] at hrun hprobe
        have ho : (core.result.Result.Ok x, st) = o := Result.ok_injective hrun
        rw [← ho]
        exact AOut₀.ok (coreKnot_succ_inferIO_hit _ _ _ _ _ _ _ hprobe.symm)
          hrel hinv
      | none =>
        rw [hoc] at hrun hprobe
        have htw := (coreKnot_succ_inferIO_miss (ConRon.Refine.absMode mode) lfe f
          (absU depth) (absEIdx e) lst hprobe.symm).trans
          (am_run_bind (inferBodyIO (ConRon.Refine.absMode mode)
            ((coreKnot (ConRon.Refine.absMode mode) lfe id f).ioView) lfe
            (absU depth) (absEIdx e)) _ lst)
        obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨p, hbd, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r, st1⟩ := p
        have hbody := hb.inferIO hrel hinv hctx (absU_pred hf hi) (Or.inl rfl) hbd
        rw [laneKnotAt_true, hlane] at hbody
        cases r with
        | Err er =>
          have ho : (core.result.Result.Err er, st1) = o := Result.ok_injective hrun
          rw [← ho]
          exact AOut₀.err (AErrSim.of_eq (AErrSim.bind (Sim₀.apply_err hbody) _) htw)
        | Ok r1 =>
          obtain ⟨lst1, hb1, hrel1, hinv1⟩ := Sim₀.apply hbody
          obtain ⟨st2, hs2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have ho : (core.result.Result.Ok r1, st2) = o := Result.ok_injective hrun
          rw [← ho]
          obtain ⟨lst2, hset, hrel2, hinv2⟩ :=
            SimS₀.apply (infer_io_set_run hrel1 hinv1 hs2)
          refine AOut₀.ok ?_ hrel2 hinv2
          rw [htw, hb1]
          show ((do inferIOSet (absEIdx e) (absEIdx r1)
                    pure (absEIdx r1) : AM EIdx)).run lst1 = _
          rw [am_run_bind, hset]
          rfl

/-! ## The two stuck-tag readers -/

theorem whnf_core_stuck_tag_abs {e : arena.handle.EIdx} {b : Bool}
    (h : arena.core.whnf_core_stuck_tag e = ok b) :
    b = whnfCoreStuckTag (absEIdx e) := by
  rw [arena.core.whnf_core_stuck_tag] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [whnfCoreStuckTag, eidx_tag_abs ht]
  by_cases h1 : t = arena.handle.ETAG_APP
  · rw [if_pos h1] at h
    rw [if_pos ((etag_dec etag_app_abs).mpr h1)]
    exact (Result.ok_injective h).symm
  · rw [if_neg h1] at h
    rw [if_neg (fun hx => h1 ((etag_dec etag_app_abs).mp hx))]
    by_cases h2 : t = arena.handle.ETAG_PROJ
    · rw [if_pos h2] at h
      rw [if_pos ((etag_dec etag_proj_abs).mpr h2)]
      exact (Result.ok_injective h).symm
    · rw [if_neg h2] at h
      rw [if_neg (fun hx => h2 ((etag_dec etag_proj_abs).mp hx))]
      by_cases h3 : t = arena.handle.ETAG_LET_E
      · rw [if_pos h3] at h
        rw [if_pos ((etag_dec etag_letE_abs).mpr h3)]
        exact (Result.ok_injective h).symm
      · rw [if_neg h3] at h
        rw [if_neg (fun hx => h3 ((etag_dec etag_letE_abs).mp hx))]
        by_cases h4 : t = arena.handle.ETAG_BVAR
        · rw [if_pos h4] at h
          rw [if_pos ((etag_dec etag_bvar_abs).mpr h4)]
          exact (Result.ok_injective h).symm
        · rw [if_neg h4] at h
          rw [if_neg (fun hx => h4 ((etag_dec etag_bvar_abs).mp hx))]
          exact (Result.ok_injective h).symm

theorem whnf_stuck_tag_abs {e : arena.handle.EIdx} {b : Bool}
    (h : arena.core.whnf_stuck_tag e = ok b) :
    b = whnfStuckTag (absEIdx e) := by
  rw [arena.core.whnf_stuck_tag] at h
  obtain ⟨t, ht, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
  simp only [whnfStuckTag, eidx_tag_abs ht]
  by_cases h1 : t = arena.handle.ETAG_SORT
  · rw [if_pos h1] at h
    rw [if_pos ((etag_dec etag_sort_abs).mpr h1)]
    exact (Result.ok_injective h).symm
  · rw [if_neg h1] at h
    rw [if_neg (fun hx => h1 ((etag_dec etag_sort_abs).mp hx))]
    by_cases h2 : t = arena.handle.ETAG_FVAR
    · rw [if_pos h2] at h
      rw [if_pos ((etag_dec etag_fvar_abs).mpr h2)]
      exact (Result.ok_injective h).symm
    · rw [if_neg h2] at h
      rw [if_neg (fun hx => h2 ((etag_dec etag_fvar_abs).mp hx))]
      by_cases h3 : t = arena.handle.ETAG_LAM
      · rw [if_pos h3] at h
        rw [if_pos ((etag_dec etag_lam_abs).mpr h3)]
        exact (Result.ok_injective h).symm
      · rw [if_neg h3] at h
        rw [if_neg (fun hx => h3 ((etag_dec etag_lam_abs).mp hx))]
        by_cases h4 : t = arena.handle.ETAG_FORALL_E
        · rw [if_pos h4] at h
          rw [if_pos ((etag_dec etag_forallE_abs).mpr h4)]
          exact (Result.ok_injective h).symm
        · rw [if_neg h4] at h
          rw [if_neg (fun hx => h4 ((etag_dec etag_forallE_abs).mp hx))]
          by_cases h5 : t = arena.handle.ETAG_LIT
          · rw [if_pos h5] at h
            rw [if_pos ((etag_dec etag_lit_abs).mpr h5)]
            exact (Result.ok_injective h).symm
          · rw [if_neg h5] at h
            rw [if_neg (fun hx => h5 ((etag_dec etag_lit_abs).mp hx))]
            exact (Result.ok_injective h).symm

/-! ## The `whnfCore` field -/

/-- **The gated `whnfCore` slot tests the stuck tag ABOVE the body** (task
#97-P3-CoreWalks' twin fix), which is what the port's `knot_whnf_core` does
above the lane dispatch — so the two line up without `BodyRel.stuckGatedCore`
and without a fuel side condition. -/
theorem coreKnotGated_succ_whnfCore (mode lfe f d e) :
    (coreKnotGated mode lfe (f + 1)).whnfCore d e
      = (if whnfCoreStuckTag e then pure e
         else whnfCoreBodyGated mode (coreKnotGated mode lfe f) lfe d e) := by
  rw [coreKnotGated]

theorem coreKnotGated_succ_whnfCore_stuck (mode lfe f d e lst)
    (hs : whnfCoreStuckTag e = true) :
    ((coreKnotGated mode lfe (f + 1)).whnfCore d e).run lst = .ok (e, lst) := by
  rw [coreKnotGated_succ_whnfCore, if_pos hs]; rfl

theorem coreKnotGated_succ_whnfCore_body (mode lfe f d e)
    (hs : whnfCoreStuckTag e = false) :
    (coreKnotGated mode lfe (f + 1)).whnfCore d e
      = whnfCoreBodyGated mode (coreKnotGated mode lfe f) lfe d e := by
  rw [coreKnotGated_succ_whnfCore, if_neg (by simp [hs])]

theorem coreKnotIO_succ_whnfCore (mode lfe f d e) :
    (coreKnotIO mode lfe (f + 1)).whnfCore d e
      = (coreKnot mode lfe id (f + 1)).whnfCore d e := by
  rw [coreKnotIO]

theorem coreKnot_succ_whnfCore_eq (mode lfe f d e) :
    (coreKnot mode lfe id (f + 1)).whnfCore d e
      = (if whnfCoreStuckTag e then pure e
         else do
           let s ← get
           match s.caches.whnfCoreC[e]? with
           | some x => pure x
           | none => do
               let x ← whnfCoreBody mode (coreKnot mode lfe id f) lfe d e
               whnfCoreSet e x
               pure x) := by
  rw [coreKnot]; rfl

theorem coreKnot_succ_whnfCore_stuck (mode lfe f d e lst)
    (hs : whnfCoreStuckTag e = true) :
    ((coreKnot mode lfe id (f + 1)).whnfCore d e).run lst = .ok (e, lst) := by
  rw [coreKnot_succ_whnfCore_eq, if_pos hs]; rfl

theorem coreKnot_succ_whnfCore_split (mode lfe f d e lst)
    (hs : whnfCoreStuckTag e = false) :
    ((coreKnot mode lfe id (f + 1)).whnfCore d e).run lst
      = (((match lst.caches.whnfCoreC[e]? with
            | some x => pure x
            | none => do
                let x ← whnfCoreBody mode (coreKnot mode lfe id f) lfe d e
                whnfCoreSet e x
                pure x) : AM EIdx)).run lst := by
  rw [coreKnot_succ_whnfCore_eq, if_neg (by simp [hs])]; rfl

theorem coreKnot_succ_whnfCore_hit (mode lfe f d e lst x)
    (hs : whnfCoreStuckTag e = false) (h : lst.caches.whnfCoreC[e]? = some x) :
    ((coreKnot mode lfe id (f + 1)).whnfCore d e).run lst = .ok (x, lst) := by
  rw [coreKnot_succ_whnfCore_split _ _ _ _ _ _ hs, h]; rfl

theorem coreKnot_succ_whnfCore_miss (mode lfe f d e lst)
    (hs : whnfCoreStuckTag e = false) (h : lst.caches.whnfCoreC[e]? = none) :
    ((coreKnot mode lfe id (f + 1)).whnfCore d e).run lst
      = (((do
            let x ← whnfCoreBody mode (coreKnot mode lfe id f) lfe d e
            whnfCoreSet e x
            pure x) : AM EIdx)).run lst := by
  rw [coreKnot_succ_whnfCore_split _ _ _ _ _ _ hs, h]

theorem knotRel_succ_whnfCore {f : Nat} (hb : BodyRel f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f + 1)
    (hrun : arena.core.knot_whnf_core pers vis st mode lane fu fe depth e = ok o) :
    Sim₀ absEIdx pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).whnfCore
        (absU depth) (absEIdx e)) := by
  rw [arena.core.knot_whnf_core, if_neg (absU_ne_zero hf)] at hrun
  obtain ⟨bt, hbt, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : bt = whnfCoreStuckTag (absEIdx e) := whnf_core_stuck_tag_abs hbt
  by_cases hbv : bt = true
  · -- the tag short circuit, at EVERY lane
    rw [if_pos hbv] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho : (core.result.Result.Ok e1, st) = o := Result.ok_injective hrun
    rw [← ho, dupId_eidx _ _ he1]
    have hsv : whnfCoreStuckTag (absEIdx e) = true := by rw [← hst]; exact hbv
    by_cases hg : lane = arena.core.LANE_GATED
    · subst hg
      rw [laneKnot_gated]
      exact AOut₀.ok (coreKnotGated_succ_whnfCore_stuck _ _ _ _ _ _ hsv) hrel hinv
    · have htwin : (laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).whnfCore
          (absU depth) (absEIdx e)
          = (coreKnot (ConRon.Refine.absMode mode) lfe id (f + 1)).whnfCore
              (absU depth) (absEIdx e) := by
        by_cases hio : lane = arena.core.LANE_IO
        · rw [hio, laneKnot_io, coreKnotIO_succ_whnfCore]
        · rw [laneKnot_of_ne _ _ _ hg hio]
      rw [show Sim₀ absEIdx pers lst (core.result.Result.Ok e, st)
            ((laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).whnfCore
              (absU depth) (absEIdx e))
          = Sim₀ absEIdx pers lst (core.result.Result.Ok e, st)
            ((coreKnot (ConRon.Refine.absMode mode) lfe id (f + 1)).whnfCore
              (absU depth) (absEIdx e)) from by rw [htwin]]
      exact AOut₀.ok (coreKnot_succ_whnfCore_stuck _ _ _ _ _ _ hsv) hrel hinv
  · rw [if_neg hbv] at hrun
    have hsv : whnfCoreStuckTag (absEIdx e) = false := by
      rw [← hst]; exact Bool.eq_false_iff.mpr hbv
    by_cases hg : lane = arena.core.LANE_GATED
    · subst hg
      rw [if_pos rfl] at hrun
      obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have h2 := hb.whnfCoreGated hrel hinv hctx (absU_pred hf hi) hrun
      rw [laneKnot_gated] at h2
      rw [laneKnot_gated, coreKnotGated_succ_whnfCore_body _ _ _ _ _ hsv]
      exact h2
    · rw [if_neg hg] at hrun
      have htwin : (laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).whnfCore
          (absU depth) (absEIdx e)
          = (coreKnot (ConRon.Refine.absMode mode) lfe id (f + 1)).whnfCore
              (absU depth) (absEIdx e) := by
        by_cases hio : lane = arena.core.LANE_IO
        · rw [hio, laneKnot_io, coreKnotIO_succ_whnfCore]
        · rw [laneKnot_of_ne _ _ _ hg hio]
      rw [show Sim₀ absEIdx pers lst o
            ((laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).whnfCore
              (absU depth) (absEIdx e))
          = Sim₀ absEIdx pers lst o
            ((coreKnot (ConRon.Refine.absMode mode) lfe id (f + 1)).whnfCore
              (absU depth) (absEIdx e)) from by rw [htwin]]
      have hlane : laneKnot (ConRon.Refine.absMode mode) lfe arena.core.LANE_FULL f
          = coreKnot (ConRon.Refine.absMode mode) lfe id f := laneKnot_full _ _ _
      obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hprobe := whnf_core_probe_abs hrel hinv hop
      cases hoc : op with
      | some x =>
        rw [hoc] at hrun hprobe
        have ho : (core.result.Result.Ok x, st) = o := Result.ok_injective hrun
        rw [← ho]
        exact AOut₀.ok (coreKnot_succ_whnfCore_hit _ _ _ _ _ _ _ hsv hprobe.symm)
          hrel hinv
      | none =>
        rw [hoc] at hrun hprobe
        have htw := (coreKnot_succ_whnfCore_miss (ConRon.Refine.absMode mode) lfe f
          (absU depth) (absEIdx e) lst hsv hprobe.symm).trans
          (am_run_bind (whnfCoreBody (ConRon.Refine.absMode mode)
            (coreKnot (ConRon.Refine.absMode mode) lfe id f) lfe
            (absU depth) (absEIdx e)) _ lst)
        obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨p, hbd, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r, st1⟩ := p
        have hbody := hb.whnfCore hrel hinv hctx (absU_pred hf hi) hbd
        rw [hlane] at hbody
        cases r with
        | Err er =>
          have ho : (core.result.Result.Err er, st1) = o := Result.ok_injective hrun
          rw [← ho]
          exact AOut₀.err (AErrSim.of_eq (AErrSim.bind (Sim₀.apply_err hbody) _) htw)
        | Ok r1 =>
          obtain ⟨lst1, hb1, hrel1, hinv1⟩ := Sim₀.apply hbody
          obtain ⟨st2, hs2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have ho : (core.result.Result.Ok r1, st2) = o := Result.ok_injective hrun
          rw [← ho]
          obtain ⟨lst2, hset, hrel2, hinv2⟩ :=
            SimS₀.apply (whnf_core_set_run hrel1 hinv1 hs2)
          refine AOut₀.ok ?_ hrel2 hinv2
          rw [htw, hb1]
          show ((do whnfCoreSet (absEIdx e) (absEIdx r1)
                    pure (absEIdx r1) : AM EIdx)).run lst1 = _
          rw [am_run_bind, hset]
          rfl

/-! ## The `whnf` field -/

/-- The same one rung up: the gated `whnf` slot tests `whnfStuckTag` above
`whnfBody`, which is what took `KnotRel.whnf`'s side condition from `2 ≤ f` to
the fuel-0 exclusion. -/
theorem coreKnotGated_succ_whnf (mode lfe f d e) :
    (coreKnotGated mode lfe (f + 1)).whnf d e
      = (if whnfStuckTag e then pure e
         else whnfBody (coreKnotGated mode lfe f) lfe d e) := by
  rw [coreKnotGated]

theorem coreKnotGated_succ_whnf_stuck (mode lfe f d e lst)
    (hs : whnfStuckTag e = true) :
    ((coreKnotGated mode lfe (f + 1)).whnf d e).run lst = .ok (e, lst) := by
  rw [coreKnotGated_succ_whnf, if_pos hs]; rfl

theorem coreKnotGated_succ_whnf_body (mode lfe f d e)
    (hs : whnfStuckTag e = false) :
    (coreKnotGated mode lfe (f + 1)).whnf d e
      = whnfBody (coreKnotGated mode lfe f) lfe d e := by
  rw [coreKnotGated_succ_whnf, if_neg (by simp [hs])]

theorem coreKnotIO_succ_whnf (mode lfe f d e) :
    (coreKnotIO mode lfe (f + 1)).whnf d e
      = (coreKnot mode lfe id (f + 1)).whnf d e := by
  rw [coreKnotIO]

theorem coreKnot_succ_whnf_eq (mode lfe f d e) :
    (coreKnot mode lfe id (f + 1)).whnf d e
      = (if whnfStuckTag e then pure e
         else do
           let s ← get
           match s.caches.whnfC[e]? with
           | some x => pure x
           | none => do
               let x ← whnfBody (coreKnot mode lfe id f) lfe d e
               whnfSet e x
               pure x) := by
  rw [coreKnot]; rfl

theorem coreKnot_succ_whnf_stuck (mode lfe f d e lst)
    (hs : whnfStuckTag e = true) :
    ((coreKnot mode lfe id (f + 1)).whnf d e).run lst = .ok (e, lst) := by
  rw [coreKnot_succ_whnf_eq, if_pos hs]; rfl

theorem coreKnot_succ_whnf_split (mode lfe f d e lst)
    (hs : whnfStuckTag e = false) :
    ((coreKnot mode lfe id (f + 1)).whnf d e).run lst
      = (((match lst.caches.whnfC[e]? with
            | some x => pure x
            | none => do
                let x ← whnfBody (coreKnot mode lfe id f) lfe d e
                whnfSet e x
                pure x) : AM EIdx)).run lst := by
  rw [coreKnot_succ_whnf_eq, if_neg (by simp [hs])]; rfl

theorem coreKnot_succ_whnf_hit (mode lfe f d e lst x)
    (hs : whnfStuckTag e = false) (h : lst.caches.whnfC[e]? = some x) :
    ((coreKnot mode lfe id (f + 1)).whnf d e).run lst = .ok (x, lst) := by
  rw [coreKnot_succ_whnf_split _ _ _ _ _ _ hs, h]; rfl

theorem coreKnot_succ_whnf_miss (mode lfe f d e lst)
    (hs : whnfStuckTag e = false) (h : lst.caches.whnfC[e]? = none) :
    ((coreKnot mode lfe id (f + 1)).whnf d e).run lst
      = (((do
            let x ← whnfBody (coreKnot mode lfe id f) lfe d e
            whnfSet e x
            pure x) : AM EIdx)).run lst := by
  rw [coreKnot_succ_whnf_split _ _ _ _ _ _ hs, h]

theorem knotRel_succ_whnf {f : Nat} (hb : BodyRel f)
    {pers vis st mode lane fu fe lfe depth e lst o}
    (hrel : AStateRel₀ pers st lst) (hinv : AStateInv pers st)
    (hctx : CoreCtx vis fe lfe) (hf : absU fu = f + 1)
    (hrun : arena.core.knot_whnf pers vis st mode lane fu fe depth e = ok o) :
    Sim₀ absEIdx pers lst o
      ((laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).whnf
        (absU depth) (absEIdx e)) := by
  rw [arena.core.knot_whnf, if_neg (absU_ne_zero hf)] at hrun
  obtain ⟨bt, hbt, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
  have hst : bt = whnfStuckTag (absEIdx e) := whnf_stuck_tag_abs hbt
  by_cases hbv : bt = true
  · rw [if_pos hbv] at hrun
    obtain ⟨e1, he1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
    have ho : (core.result.Result.Ok e1, st) = o := Result.ok_injective hrun
    rw [← ho, dupId_eidx _ _ he1]
    have hsv : whnfStuckTag (absEIdx e) = true := by rw [← hst]; exact hbv
    by_cases hg : lane = arena.core.LANE_GATED
    · subst hg
      rw [laneKnot_gated]
      exact AOut₀.ok (coreKnotGated_succ_whnf_stuck _ _ _ _ _ _ hsv) hrel hinv
    · have htwin : (laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).whnf
          (absU depth) (absEIdx e)
          = (coreKnot (ConRon.Refine.absMode mode) lfe id (f + 1)).whnf
              (absU depth) (absEIdx e) := by
        by_cases hio : lane = arena.core.LANE_IO
        · rw [hio, laneKnot_io, coreKnotIO_succ_whnf]
        · rw [laneKnot_of_ne _ _ _ hg hio]
      rw [show Sim₀ absEIdx pers lst (core.result.Result.Ok e, st)
            ((laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).whnf
              (absU depth) (absEIdx e))
          = Sim₀ absEIdx pers lst (core.result.Result.Ok e, st)
            ((coreKnot (ConRon.Refine.absMode mode) lfe id (f + 1)).whnf
              (absU depth) (absEIdx e)) from by rw [htwin]]
      exact AOut₀.ok (coreKnot_succ_whnf_stuck _ _ _ _ _ _ hsv) hrel hinv
  · rw [if_neg hbv] at hrun
    have hsv : whnfStuckTag (absEIdx e) = false := by
      rw [← hst]; exact Bool.eq_false_iff.mpr hbv
    by_cases hg : lane = arena.core.LANE_GATED
    · subst hg
      rw [if_pos rfl] at hrun
      obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have h2 := hb.whnf hrel hinv hctx (absU_pred hf hi) hrun
      rw [laneKnot_gated] at h2
      rw [laneKnot_gated, coreKnotGated_succ_whnf_body _ _ _ _ _ hsv]
      exact h2
    · rw [if_neg hg] at hrun
      have htwin : (laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).whnf
          (absU depth) (absEIdx e)
          = (coreKnot (ConRon.Refine.absMode mode) lfe id (f + 1)).whnf
              (absU depth) (absEIdx e) := by
        by_cases hio : lane = arena.core.LANE_IO
        · rw [hio, laneKnot_io, coreKnotIO_succ_whnf]
        · rw [laneKnot_of_ne _ _ _ hg hio]
      rw [show Sim₀ absEIdx pers lst o
            ((laneKnot (ConRon.Refine.absMode mode) lfe lane (f + 1)).whnf
              (absU depth) (absEIdx e))
          = Sim₀ absEIdx pers lst o
            ((coreKnot (ConRon.Refine.absMode mode) lfe id (f + 1)).whnf
              (absU depth) (absEIdx e)) from by rw [htwin]]
      have hlane : laneKnot (ConRon.Refine.absMode mode) lfe arena.core.LANE_FULL f
          = coreKnot (ConRon.Refine.absMode mode) lfe id f := laneKnot_full _ _ _
      obtain ⟨op, hop, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hprobe := whnf_probe_abs hrel hinv hop
      cases hoc : op with
      | some x =>
        rw [hoc] at hrun hprobe
        have ho : (core.result.Result.Ok x, st) = o := Result.ok_injective hrun
        rw [← ho]
        exact AOut₀.ok (coreKnot_succ_whnf_hit _ _ _ _ _ _ _ hsv hprobe.symm)
          hrel hinv
      | none =>
        rw [hoc] at hrun hprobe
        have htw := (coreKnot_succ_whnf_miss (ConRon.Refine.absMode mode) lfe f
          (absU depth) (absEIdx e) lst hsv hprobe.symm).trans
          (am_run_bind (whnfBody (coreKnot (ConRon.Refine.absMode mode) lfe id f)
            lfe (absU depth) (absEIdx e)) _ lst)
        obtain ⟨i, hi, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨p, hbd, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨r, st1⟩ := p
        have hbody := hb.whnf hrel hinv hctx (absU_pred hf hi) hbd
        rw [hlane] at hbody
        cases r with
        | Err er =>
          have ho : (core.result.Result.Err er, st1) = o := Result.ok_injective hrun
          rw [← ho]
          exact AOut₀.err (AErrSim.of_eq (AErrSim.bind (Sim₀.apply_err hbody) _) htw)
        | Ok r1 =>
          obtain ⟨lst1, hb1, hrel1, hinv1⟩ := Sim₀.apply hbody
          obtain ⟨st2, hs2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          have ho : (core.result.Result.Ok r1, st2) = o := Result.ok_injective hrun
          rw [← ho]
          obtain ⟨lst2, hset, hrel2, hinv2⟩ :=
            SimS₀.apply (whnf_set_run hrel1 hinv1 hs2)
          refine AOut₀.ok ?_ hrel2 hinv2
          rw [htw, hb1]
          show ((do whnfSet (absEIdx e) (absEIdx r1)
                    pure (absEIdx r1) : AM EIdx)).run lst1 = _
          rw [am_run_bind, hset]
          rfl

/-! ## The step, and the induction -/

/-- **`BodyRel f → KnotRel (f + 1)`** — the six fields above, assembled. -/
theorem knotRel_succ {f : Nat} (hb : BodyRel f) : KnotRel (f + 1) where
  whnfCore h1 h2 h3 h4 h5 := knotRel_succ_whnfCore hb h1 h2 h3 h4 h5
  whnf h1 h2 h3 h4 h5 := knotRel_succ_whnf hb h1 h2 h3 h4 h5
  infer h1 h2 h3 h4 h5 := knotRel_succ_infer hb h1 h2 h3 h4 h5
  inferIO h1 h2 h3 h4 h5 := knotRel_succ_inferIO hb h1 h2 h3 h4 h5
  defeq h1 h2 h3 h4 h5 := knotRel_succ_defeq hb h1 h2 h3 h4 h5
  annotate h1 h2 h3 h4 h5 := knotRel_succ_annotate hb h1 h2 h3 h4 h5

/-- **The fuel induction**: `KnotRel` at every fuel, given the arms.  The
premise is `Core/Arms/*`'s obligation — *"given the knot at `f`, the six
bodies at `f`"* — and it is where the tier's `sorry`s live. -/
theorem knot_rel (hbody : ∀ f, KnotRel f → BodyRel f) : ∀ f, KnotRel f
  | 0 => knotRel_zero
  | f + 1 => knotRel_succ (hbody f (knot_rel hbody f))

/-! ## The axiom census

Every closed lemma of the step reads the three standard axioms and nothing
else — no `sorryAx`, and no `bv_decide` axiom: the fuel reading is `omega`
after `UScalar.val` and the two stuck-tag readers are `etag_dec` ten times. -/

section Axioms

/-- info: 'ConRon.Refine2.knotRel_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms knotRel_zero

/-- info: 'ConRon.Refine2.whnf_core_stuck_tag_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whnf_core_stuck_tag_abs

/-- info: 'ConRon.Refine2.whnf_stuck_tag_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms whnf_stuck_tag_abs

/-- info: 'ConRon.Refine2.io_gate_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms io_gate_abs

/-- info: 'ConRon.Refine2.knotRel_succ_whnfCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms knotRel_succ_whnfCore

/-- info: 'ConRon.Refine2.knotRel_succ_whnf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms knotRel_succ_whnf

/-- info: 'ConRon.Refine2.knotRel_succ_infer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms knotRel_succ_infer

/-- info: 'ConRon.Refine2.knotRel_succ_inferIO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms knotRel_succ_inferIO

/-- info: 'ConRon.Refine2.knotRel_succ_defeq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms knotRel_succ_defeq

/-- info: 'ConRon.Refine2.knotRel_succ_annotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms knotRel_succ_annotate

/-- info: 'ConRon.Refine2.knotRel_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms knotRel_succ

/-- info: 'ConRon.Refine2.knot_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms knot_rel

end Axioms

end ConRon.Refine2

/-
# `ConRon.Arena.OleanJobs` — the check phase of an `--olean` run

The twin of the binary's `driver::olean_job` and of con-leche's `oleanJobRun`
(`ConLeche/Driver/CheckMain.lean`, upstream task #481).  An `--olean` read leaves a
theorem's value in its file: the record holds a reference (`.thmDecl cv v`, `v` a
`bvar` whose index is the reference's code), and the theorem's job reads the value
into its own scratch tier, checks the record with it in place, and drops it with the
tier.  Every other record's job is `runJob`'s.

A worker keeps the region of the module it read last (`ValueCache`) from one job to
the next, as con-leche's `OleanWorker` does.  `PooledOleanAccepts` is the pool's
accept over these jobs, as `PooledAccepts` (`Arena/Pooled.lean`) is over `runJob`.
-/
module

public import ConRon.Arena.Checker
public import ConRon.Arena.Frontend.Olean.Records

@[expose] public section

namespace ConRon.Arena

open ConLeche
open ConRon.Arena.Frontend.Olean (OleanFs OleanPins ModRef ValueCache readValue)

/-- con-leche: ConLeche/Driver/CheckMain.lean:120-133 oleanJobRun
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove OleanJobs.oleanJob_bridge, then delete this line
**Job `t` of an `--olean` run**, from the cache `c` the worker kept: a theorem
whose value is a reference opens the job's bracket (`enterScratch`), reads the
value (`readValue`), checks the record with it (`recordCheck`) and closes the
bracket; any other record is `runJob`'s.  The read is inside the bracket, as the
binary's (`driver::olean_job`), so what it interns is the job's.  A failure is
tagged with the position and hands back the abandoned state (`AState.abandoned`'s
note), with the cache. -/
def oleanJob (fs : OleanFs) (pk : OleanPins) (sp : List System.FilePath)
    (values : Array ModRef) (mode : CheckMode) (pins : List INatOpPinSet)
    (I : IStreamIndex) (ds : Array IDeclaration) (c : ValueCache) (t : Nat) :
    AM (ValueCache × Except (CheckError × Nat) Unit) := fun s =>
  let plain : Except CheckError (ValueCache × Except (CheckError × Nat) Unit × AState) :=
    match runJob mode pins I ds t s with
    | .ok (r, s') => .ok (c, r, s')
    | .error e => .error e
  let finish (x : Except CheckError (ValueCache × Except (CheckError × Nat) Unit × AState)) :
      Except CheckError ((ValueCache × Except (CheckError × Nat) Unit) × AState) :=
    match x with
    | .ok (c', r, s') => .ok ((c', r), s')
    | .error e => .error e
  match ds[t]? with
  | some (.thmDecl cv v) =>
    -- a theorem's value is a reference only if its handle is a `bvar`: `viewBVar`
    -- reads the bvar table at the handle's slot whatever its tag
    match (if v.tag == ETag.bvar then s.store.viewBVar v else none) with
    | some code =>
      match (do enterScratch; readValue fs pk sp values c code) s with
      | .ok ((c', .ok e), s₁) =>
        match (do recordCheck mode pins I t (.thmDecl cv e); dropScratch) s₁ with
        | .ok ((), s₂) => .ok ((c', .ok ()), s₂)
        | .error err => .ok ((c', .error (err, t)), AState.abandoned)
      | .ok ((c', .error err), _) => .ok ((c', .error (err, t)), AState.abandoned)
      | .error err => .ok ((c, .error (err, t)), AState.abandoned)
    | none => finish plain
  | _ => finish plain

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:432-455 parWorker
**A worker's fold over the jobs it claimed** on an `--olean` run, on one state and
one cache, the first failure the answer (`PooledOleanAccepts`). -/
def checkOleanJobList (fs : OleanFs) (pk : OleanPins) (sp : List System.FilePath)
    (values : Array ModRef) (mode : CheckMode) (pins : List INatOpPinSet)
    (I : IStreamIndex) (ds : Array IDeclaration) :
    List Nat → ValueCache → AM (Except (CheckError × Nat) Unit)
  | [], _ => pure (.ok ())
  | t :: rest, c => fun s =>
    match oleanJob fs pk sp values mode pins I ds c t s with
    | .ok ((c', .ok ()), s') => checkOleanJobList fs pk sp values mode pins I ds rest c' s'
    | .ok ((_, .error e), s') => .ok (.error e, s')
    | .error e => .error e

/-- con-leche: ConLeche/Driver/CheckMain.lean:152-169 checkOleansG
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove OleanJobs.checkOleans_bridge, then delete this line
**The check phase of an `--olean` run, as one worker runs it**: the index of the
records, then every record's job in fold order, from the worker's state and the
empty cache. -/
def checkOleans (fs : OleanFs) (pk : OleanPins) (sp : List System.FilePath)
    (values : Array ModRef) (mode : CheckMode) (pins : List INatOpPinSet)
    (ds : Array IDeclaration) : AM (Except (CheckError × Nat) Unit) := fun s =>
  match buildIndex ds s with
  | .ok (.ok I, s₁) =>
    checkOleanJobList fs pk sp values mode pins I ds (List.range ds.size) {} s₁.worker
  | .ok (.error e, s₁) => .ok (.error e, s₁)
  | .error e => .error e

/-- con-leche: ConLeche/Frontend/CheckerIO.lean:457-486 parMapWorkersIO
**The pool's accept on an `--olean` run**: the index built from `s`, the stream's
positions covered by job lists, each in range and increasing, and each list accepted
from the worker of the post-index state with the empty cache.  `PooledAccepts`
over `oleanJob`. -/
def PooledOleanAccepts (fs : OleanFs) (pk : OleanPins) (sp : List System.FilePath)
    (values : Array ModRef) (mode : CheckMode) (pins : List INatOpPinSet)
    (ds : Array IDeclaration) (s : AState) (I : IStreamIndex) (s' : AState) : Prop :=
  ∃ (parts : List (List Nat)),
    buildIndex ds s = .ok (.ok I, s') ∧
    (∀ t < ds.size, ∃ w ∈ parts, t ∈ w) ∧
    (∀ w ∈ parts, ∀ t ∈ w, t < ds.size) ∧
    (∀ w ∈ parts, w.Pairwise (· < ·)) ∧
    (∀ w ∈ parts, ∃ s'', checkOleanJobList fs pk sp values mode pins I ds w {} s'.worker
      = .ok (.ok (), s''))

end ConRon.Arena

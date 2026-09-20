/-
# The twin's monad, unfolded once per primitive

`StateT MState (Except CheckError)` is DESIGN §8.4's monad at the mini
arena.  Experiments C1 and D state their conclusions about a *run*
(`(c).run s = .ok (a, s')`), so every twin primitive needs its `.run`
equation exactly once; after this module no proof below unfolds `StateT`
again.

This is the mini-arena counterpart of `Specs.lean`'s `AM.of_run`, and it is
the cheaper of the two ways to consume a monadic definition: experiment A
turns the body into verification conditions with `mvcgen`, experiment C1
turns it into an `Except`-valued equation and matches.  The report's round-2
table prices both.
-/
import ConRon.Arena.Spike.Mini

namespace ConRon.Arena.Spike

open ConLeche

/-- con-leche: ConLeche/Kernel/Core.lean:62 CheckError — the twin's failure,
run. -/
theorem mfail_run {α : Type} (e : CheckError) (s : MState) :
    (mfail e : MM α).run s = .error e := rfl

/-- The twin's monad, unfolded: `StateT` over `Except`, one layer at a time.
`h` is the branch equation the caller has just `cases`d on. -/
macro "mrun" h:ident : tactic => `(tactic|
  (simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      set, MonadStateOf.set, StateT.set, pure, StateT.pure, Functor.map, StateT.map,
      StateT.lift, Except.bind, Except.pure, mfail, throwThe, MonadExceptOf.throw, $h:ident]
   <;> (try (split <;> rfl))))

/-- con-leche: Setlec/Kernel/IExpr.lean:464 intern — run. -/
theorem mInternBvar_run (k : Nat) (s : MState) :
    (mInternBvar k).run s =
      match mFindBvar s k with
      | some h => .ok (h, s)
      | none =>
        if s.bvars.length < mIdxCap then
          .ok (mMk mTagBvar s.bvars.length, { s with bvars := s.bvars ++ [k] })
        else .error (.internal "arena-spike: bvar array full") := by
  unfold mInternBvar; cases hfind : mFindBvar s k <;> mrun hfind

/-- con-leche: Setlec/Kernel/IExpr.lean:464 intern — run. -/
theorem mInternApp_run (f a : Nat) (s : MState) :
    (mInternApp f a).run s =
      match mFindApp s f a with
      | some h => .ok (h, s)
      | none =>
        if s.apps.length < mIdxCap then
          .ok (mMk mTagApp s.apps.length, { s with apps := s.apps ++ [(f, a)] })
        else .error (.internal "arena-spike: app array full") := by
  unfold mInternApp; cases hfind : mFindApp s f a <;> mrun hfind

/-- con-leche: Setlec/Kernel/IExpr.lean:464 intern — run. -/
theorem mInternLam_run (ty b : Nat) (s : MState) :
    (mInternLam ty b).run s =
      match mFindLam s ty b with
      | some h => .ok (h, s)
      | none =>
        if s.lams.length < mIdxCap then
          .ok (mMk mTagLam s.lams.length, { s with lams := s.lams ++ [(ty, b)] })
        else .error (.internal "arena-spike: lam array full") := by
  unfold mInternLam; cases hfind : mFindLam s ty b <;> mrun hfind

/-- con-leche: ConLeche/Kernel/ExprOps.lean:116 instantiate1Go — run. -/
theorem mMemoSet_run (h d r : Nat) (s : MState) :
    (mMemoSet h d r).run s = .ok ((), { s with memo := s.memo ++ [(h, d, r)] }) := rfl

/-- con-leche: ConLeche/Kernel/ExprOps.lean:33 instantiate1 — run, at fuel 0. -/
theorem mInstantiate1_run_zero (v h d : Nat) (s : MState) :
    (mInstantiate1 v 0 h d).run s = .error (.internal "fuel exhausted: instantiate1") := rfl

/-- con-leche: ConLeche/Kernel/ExprOps.lean:81 instantiate1Go — **the twin's
one-step equation**, in the shape the Aeneas model has: an `Except`-valued
expression with the state threaded by hand.  Experiment C1 matches this
against `Generated.instantiate1.eq_def` branch by branch. -/
theorem mInstantiate1_run_succ (v fuel h d : Nat) (s : MState) :
    (mInstantiate1 v (fuel + 1) h d).run s =
      (if mTagOf h = mTagBvar then
         (match s.viewBvar h with
          | none => .error (.internal "arena-spike: dangling handle")
          | some i =>
            if i = d then .ok (v, s)
            else if d < i then (mInternBvar (i - 1)).run s else .ok (h, s))
       else if mTagOf h = mTagApp then
         (match s.viewApp h with
          | none => .error (.internal "arena-spike: dangling handle")
          | some (f, a) =>
            match mMemoGet s h d with
            | some r => .ok (r, s)
            | none =>
              ((mInstantiate1 v fuel f d).run s).bind (fun p =>
                ((mInstantiate1 v fuel a d).run p.2).bind (fun q =>
                  ((mInternApp p.1 q.1).run q.2).bind (fun w =>
                    ((mMemoSet h d w.1).run w.2).bind (fun u => .ok (w.1, u.2))))))
       else if mTagOf h = mTagLam then
         (match s.viewLam h with
          | none => .error (.internal "arena-spike: dangling handle")
          | some (ty, b) =>
            match mMemoGet s h d with
            | some r => .ok (r, s)
            | none =>
              ((mInstantiate1 v fuel ty d).run s).bind (fun p =>
                ((mInstantiate1 v fuel b (d + 1)).run p.2).bind (fun q =>
                  ((mInternLam p.1 q.1).run q.2).bind (fun w =>
                    ((mMemoSet h d w.1).run w.2).bind (fun u => .ok (w.1, u.2))))))
       else .error (.internal "arena-spike: bad tag")) := by
  simp only [mInstantiate1, StateT.run_bind, StateT.run_get, pure_bind]
  repeat' (first | rfl | split)
  all_goals simp_all [Pure.pure, Except.pure, mTagBvar, mTagApp, mTagLam, StateT.pure]
  all_goals (first | rfl | omega)

end ConRon.Arena.Spike

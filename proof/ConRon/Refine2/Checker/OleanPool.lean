/-
# `ConRon.Refine2.Checker.OleanPool` — Theorem 2 at the check phase of an `--olean` run

An `--olean` read leaves each theorem's value in its file (the record holds a reference,
`.ThmDecl cv v` with `v` a `bvar` whose index is the reference's code), and the binary's
check phase reads it in the theorem's job: `driver::olean_job` (`crates/con-ron/src/
driver.rs`, unverified), con-leche's `oleanJobRun`.  That function is a straight line of
calls into the verified crate, written here as `oleanJobStep`: the reference read off the
record (a `bvar` handle's `view_bvar`), the job's bracket opened (`enter_record`), the value read into the
worker's scratch tier (`records::read_value`, from the worker's `ValueCache`), the record
checked with it in place (`stream_index::record_check`), the bracket closed
(`leave_record`); any other record is `run_job`'s.  Its twin is `Arena/OleanJobs.lean`'s
`oleanJob`, and the pool's accept over it is `PooledOleanAccepts`.
-/
import ConRon.Refine2.Checker.Jobs
import ConRon.Refine2.Frontend.Olean.ReadValue

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine2

open ConRon.Arena

/-- **The driver's `--olean` step closure**, `|tier, w, c, k| driver::olean_job(tier, w,
c, &mode, &ipins, ds, pk, values, sp, k as u64)`, as the Aeneas model of each call reads it, over
the worker's state and cache.  The file system is the reader's (`fs` at instance `inst`). -/
def oleanJobStep {F : Type} (inst : frontend.olean.files.OleanFs F) (fs : F)
    (tier : arena.store.PersTier) (mode : kernel.env.CheckMode)
    (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (ds : alloc.vec.Vec arena.env.IDeclaration) (pk : frontend.olean.spec.OleanPins) (values : alloc.vec.Vec frontend.olean.records.ModRef)
    (sp : alloc.vec.Vec (alloc.vec.Vec Std.U32))
    (w : arena.monad.AState × frontend.olean.records.ValueCache) (k : Nat) :
    Result ((core.result.Result Unit (kernel.core_types.CheckError × Std.U64)) ×
      (arena.monad.AState × frontend.olean.records.ValueCache)) :=
  if h : k < 2 ^ UScalarTy.Usize.numBits then
    let ku : Std.U64 := UScalar.cast .U64 (UScalar.ofNatCore (ty := .Usize) k h)
    let plain : Result ((core.result.Result Unit (kernel.core_types.CheckError × Std.U64)) ×
        (arena.monad.AState × frontend.olean.records.ValueCache)) := do
      let (r, st') ← arena.checker.run_job tier w.1 mode pins ds ku
      ok (r, (st', w.2))
    match ds.val[k]? with
    | some (.ThmDecl cv v) => do
      let t ← arena.handle.EIdx.tag v
      let code ← if t = arena.handle.ETAG_BVAR then arena.store.EStore.view_bvar w.1.store tier v
        else ok none
      match code with
      | some code =>
        let st1 ← arena.core.enter_record w.1
        let (r, ar, c) ← frontend.olean.records.read_value inst fs pk tier st1.store sp
          values w.2 code
        match r with
        | .Err e =>
          let st3 ← arena.core.leave_record { st1 with store := ar }
          ok (.Err (e, ku), (st3, c))
        | .Ok e =>
          let cv' ← arena.env.i_constant_val_dup cv
          let (r', st3) ← arena.stream_index.record_check tier { st1 with store := ar } mode
            pins ku (.ThmDecl cv' e)
          let st4 ← arena.core.leave_record st3
          match r' with
          | .Ok () => ok (.Ok (), (st4, c))
          | .Err e => ok (.Err (e, ku), (st4, c))
      | none => plain
    | _ => plain
  else fail .panic

/-- **The driver's `--olean` init closure**, `|| (checker::worker_state(&st.pins),
value_cache_empty())`. -/
def oleanWorkerInit (pins : arena.pins.Pins) :
    Result (arena.monad.AState × frontend.olean.records.ValueCache) := do
  let w ← arena.checker.worker_state pins
  let c ← frontend.olean.records.value_cache_empty
  ok (w, c)

/-! ## A job, related -/

open ConRon.Refine2.Frontend.Olean in
/-- At an idle twin worker (scratch off), the projection of a `bvar` reads the same
through the opened scratch tier the Rust's frozen store is related to. -/
theorem viewBVar_enableScratch {s : EStore} (hoff : s.scratchOn = false) (v : EIdx) :
    s.enableScratch.viewBVar v = s.viewBVar v := by
  unfold EStore.viewBVar EStore.enableScratch
  by_cases hp : v.isPersistent
  · simp [hp, EStore.persGetBVar]
  · simp [hp, hoff, ETables.getBVar, ETables.empty, Tbl.empty, Tbl.node?]

open ConRon.Refine2.Frontend.Olean in
/-- **`oleanJobStep` ⊑ `oleanJob`, accepting**, between two idle workers: a theorem
whose value is a reference reads it in its bracket and is checked with it, any other
record is `run_job_refines`'.  The caches are related (`VCRel`). -/
theorem olean_job_step_refines {F : Type} {inst : frontend.olean.files.OleanFs F} {fsv : F}
    {fs : Arena.Frontend.Olean.OleanFs} {tier} {I : IStreamIndex}
    {mode : kernel.env.CheckMode} {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {pk : frontend.olean.spec.OleanPins} {values : alloc.vec.Vec frontend.olean.records.ModRef}
    {values' : Array Arena.Frontend.Olean.ModRef}
    {sp : alloc.vec.Vec (alloc.vec.Vec Std.U32)} {k : Nat}
    {st lst c c' st' c1}
    (hfs : FsRel inst fsv fs) (hv : List.Forall₂ ModRefRel values.val values'.toList)
    (hidle : AIdle tier st lst) (hinv : AStateInv tier st) (hoff : lst.store.scratchOn = false)
    (htf : tier.frozen = true) (hI : StreamIndexRel tier.env I) (hc : VCRel c c')
    (hrun : oleanJobStep inst fsv tier mode pins ds pk values sp (st, c) k = ok (.Ok (), (st', c1))) :
    k < ds.val.length ∧
    ∃ c1' lst', oleanJob fs (absPins pk) (absSearchPath sp) values'
        (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) I (absIDeclL ds).toArray c' k lst
        = .ok ((c1', .ok ()), lst') ∧
      VCRel c1 c1' ∧ AIdle tier st' lst' ∧ AStateInv tier st' ∧ lst'.store.scratchOn = false := by
  unfold oleanJobStep at hrun
  split at hrun
  case isFalse => simp at hrun
  rename_i hk
  have hu : (UScalar.cast .U64 (UScalar.ofNatCore (ty := .Usize) k hk)).val = k := by
    rw [usize_cast_u64_val']; rfl
  have hkU : (UScalar.cast .U64 (UScalar.ofNatCore (ty := .Usize) k hk)).val
      ≤ Std.Usize.max := by
    have h2 : Std.Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by
      rw [← UScalar.max_USize_eq, UScalar.max_def]
    have h3 := Nat.one_le_two_pow (n := UScalarTy.Usize.numBits)
    rw [hu, h2]; omega
  have hau : absU (UScalar.cast .U64 (UScalar.ofNatCore (ty := .Usize) k hk)) = k := hu
  -- the record as a plain job: `run_job` and the twin's `runJob`
  have hplain : (do
        let (r, st'') ← arena.checker.run_job tier st mode pins ds
          (UScalar.cast .U64 (UScalar.ofNatCore (ty := .Usize) k hk))
        ok (r, (st'', c)) : Result _) = ok (.Ok (), (st', c1)) →
      k < ds.val.length ∧ c1 = c ∧
      ∃ lst', runJob (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) I
          (absIDeclL ds).toArray k lst = .ok (.ok (), lst') ∧
        AIdle tier st' lst' ∧ AStateInv tier st' ∧ lst'.store.scratchOn = false := by
    intro h
    obtain ⟨⟨r, st''⟩, h1, h⟩ := ConRon.Refine.bind_eq_ok_iff.mp h
    obtain ⟨rfl, rfl, rfl⟩ : r = .Ok () ∧ st'' = st' ∧ c = c1 := by
      have := Result.ok_injective h; simp only [Prod.mk.injEq] at this; exact ⟨this.1, this.2.1, this.2.2⟩
    obtain ⟨hlt, lst', hx, hrest⟩ := run_job_refines hidle hinv htf hI hkU h1
    rw [hu] at hlt
    rw [hau] at hx
    exact ⟨hlt, rfl, lst', hx, hrest⟩
  have hgetT : ∀ d, ds.val[k]? = some d →
      (absIDeclL ds).toArray[k]? = some (absIDeclaration d) := by
    intro d hd; simp [absIDeclL, hd]
  -- every route but the reference is the plain job
  have hplainT : (∀ lst', runJob (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) I
        (absIDeclL ds).toArray k lst = .ok (.ok (), lst') →
      (match (match runJob (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) I
          (absIDeclL ds).toArray k lst with
        | .ok (r, s') => Except.ok (c', r, s')
        | .error e => .error e) with
        | .ok (c'', r, s') => Except.ok ((c'', r), s')
        | .error e => .error e) = .ok ((c', .ok ()), lst')) := by
    intro lst' h; rw [h]
  rcases hd : ds.val[k]? with _ | d
  · simp only [hd] at hrun
    obtain ⟨hlt, rfl, lst', hx, hidle', hinv', hoff'⟩ := hplain hrun
    refine ⟨hlt, c', lst', ?_, hc, hidle', hinv', hoff'⟩
    have hn : (absIDeclL ds).toArray[k]? = none := by simp [absIDeclL, hd]
    simp only [oleanJob, hn]
    exact hplainT lst' hx
  · cases d with
    | ThmDecl cv v =>
      simp only [hd] at hrun
      obtain ⟨t, ht, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have htag := eidx_tag_abs ht
      obtain ⟨code, hcode, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
      have hcodeT : (if (absEIdx v).tag == ETag.bvar then lst.store.viewBVar (absEIdx v)
          else none) = code.map absU := by
        by_cases htb : t = arena.handle.ETAG_BVAR
        · rw [ite_eq_left htb] at hcode
          have := estore_view_bvar_abs hidle.store hcode
          rw [viewBVar_enableScratch hoff] at this
          have hb : ((absEIdx v).tag == ETag.bvar) = true := by
            rw [htag, htb]; simp [arena.handle.ETAG_BVAR, ETag.bvar, absU32]
          rw [ite_eq_left hb]
          exact this
        · rw [ite_eq_right htb] at hcode
          obtain rfl := (Result.ok_injective hcode).symm
          have hb : ¬ ((absEIdx v).tag == ETag.bvar) = true := by
            intro hb
            apply htb
            rw [htag] at hb
            have h0 : absU32 t = 0 := by simpa [ETag.bvar] using hb
            have h1 := congrArg UInt32.toNat h0
            rw [absU32_toNat] at h1
            simp only [arena.handle.ETAG_BVAR]
            exact Std.UScalar.eq_of_val_eq (by simpa using h1)
          rw [ite_eq_right hb]
          rfl
      have hgT := hgetT _ hd
      cases code with
      | none =>
        obtain ⟨hlt, rfl, lst', hx, hidle', hinv', hoff'⟩ := hplain hrun
        refine ⟨hlt, c', lst', ?_, hc, hidle', hinv', hoff'⟩
        simp only [oleanJob, hgT, absIDeclaration, hcodeT, Option.map_none]
        exact hplainT lst' hx
      | some code =>
        simp only at hrun
        obtain ⟨st1, h1, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        obtain ⟨lst1, hx1, hrel1, hinv1⟩ := (enter_record_sim hidle hinv h1).apply
        obtain ⟨⟨r, ar, c2⟩, h2, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
        cases r with
        | Err e =>
          obtain ⟨st3, -, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          cases Result.ok_injective hrun
        | Ok e =>
          obtain ⟨c2', lst2, hx2, hvc2, hrel2, hinv2⟩ :=
            read_value_refines hfs hv hc hrel1 hinv1 h2
          obtain ⟨cv', hcv', hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨⟨r', st3⟩, h3, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          obtain ⟨st4, h4, hrun⟩ := ConRon.Refine.bind_eq_ok_iff.mp hrun
          cases r' with
          | Err e' => cases Result.ok_injective hrun
          | Ok u =>
            cases u
            obtain ⟨-, rfl, rfl⟩ : (core.result.Result.Ok () : core.result.Result Unit
                (kernel.core_types.CheckError × Std.U64)) = .Ok () ∧ st4 = st' ∧ c2 = c1 := by
              have := Result.ok_injective hrun
              simp only [Prod.mk.injEq] at this
              exact ⟨rfl, this.2.1, this.2.2⟩
            obtain ⟨lst3, hx3, hrel3, hinv3⟩ := record_check_refines hrel2 hinv2 hI hkU h3
            obtain ⟨lst4, hx4, hidle4, hinv4⟩ := leave_record_rel hrel3 hinv3 htf h4
            have hoff4 : lst4.store.scratchOn = false := by
              have h' : (dropScratch : AM Unit).run lst3
                  = .ok ((), { lst3 with store := lst3.store.dropScratch, caches := Caches.empty }) :=
                rfl
              rw [h'] at hx4
              cases hx4
              rfl
            have hlt : k < ds.val.length := (List.getElem?_eq_some_iff.mp hd).1
            refine ⟨hlt, c2', lst4, ?_, hvc2, hidle4, hinv4, hoff4⟩
            have hpd : absIDeclaration (.ThmDecl cv' e) = .thmDecl (absIConstantVal cv) (absEIdx e) := by
              simp only [absIDeclaration, i_constant_val_dup_abs hcv']
            rw [hpd, hau] at hx3
            simp only [oleanJob, hgT, absIDeclaration, hcodeT, Option.map_some]
            rw [show (enterScratch >>= fun _ => Arena.Frontend.Olean.readValue fs (absPins pk) (absSearchPath sp)
                  values' c' (absU code) : AM _) lst = .ok ((c2', .ok (absEIdx e)), lst2) by
                show StateT.run (enterScratch >>= fun _ => _) lst = _
                rw [StateT.run_bind, hx1]
                exact hx2]
            show (match (StateT.run (recordCheck _ _ I k _ >>= fun _ => dropScratch) lst2) with
              | .ok ((), s₂) => _
              | .error err => _) = _
            rw [StateT.run_bind, hx3]
            simp only [except_ok_bind]
            rw [hx4]
    | _ =>
      simp only [hd] at hrun
      obtain ⟨hlt, rfl, lst', hx, hidle', hinv', hoff'⟩ := hplain hrun
      refine ⟨hlt, c', lst', ?_, hc, hidle', hinv', hoff'⟩
      simp only [oleanJob, hgetT _ hd, absIDeclaration]
      exact hplainT lst' hx

open ConRon.Refine2.Frontend.Olean in
/-- **A worker's `--olean` fold ⊑ `checkOleanJobList`**: each claimed index is a record
position, and the worker's jobs, from one idle state and a related cache, are the twin's. -/
theorem foldAllOk_oleanJobStep_refines {F : Type} {inst : frontend.olean.files.OleanFs F}
    {fsv : F} {fs : Arena.Frontend.Olean.OleanFs} {tier} {I : IStreamIndex}
    {mode : kernel.env.CheckMode} {pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet}
    {ds : alloc.vec.Vec arena.env.IDeclaration} {pk : frontend.olean.spec.OleanPins} {values : alloc.vec.Vec frontend.olean.records.ModRef}
    {values' : Array Arena.Frontend.Olean.ModRef} {sp : alloc.vec.Vec (alloc.vec.Vec Std.U32)}
    (hfs : FsRel inst fsv fs) (hv : List.Forall₂ ModRefRel values.val values'.toList)
    (htf : tier.frozen = true) (hI : StreamIndexRel tier.env I) :
    ∀ (ks : List Nat) {st lst c c'},
      AIdle tier st lst → AStateInv tier st → lst.store.scratchOn = false → VCRel c c' →
      FoldAllOk (oleanJobStep inst fsv tier mode pins ds pk values sp) (st, c) ks →
      (∀ k ∈ ks, k < ds.val.length) ∧
      ∃ s'', checkOleanJobList fs (absPins pk) (absSearchPath sp) values'
        (ConRon.Refine.absMode mode) (absINatOpPinSetL pins) I (absIDeclL ds).toArray ks c' lst
        = .ok (.ok (), s'')
  | [], _, lst, _, _, _, _, _, _, _ => ⟨by simp, lst, rfl⟩
  | k :: ks, _, lst, _, _, hidle, hinv, hoff, hc, ⟨⟨st1, c1⟩, hs1, hf⟩ => by
    obtain ⟨hlt, c1', lst1, hx, hc1, hidle1, hinv1, hoff1⟩ :=
      olean_job_step_refines hfs hv hidle hinv hoff htf hI hc hs1
    obtain ⟨hall, s'', h⟩ :=
      foldAllOk_oleanJobStep_refines hfs hv htf hI ks hidle1 hinv1 hoff1 hc1 hf
    refine ⟨?_, s'', ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hlt
      · exact hall x hx
    · simp only [checkOleanJobList]
      rw [hx]
      exact h

end ConRon.Refine2

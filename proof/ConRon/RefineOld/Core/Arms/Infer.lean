/-
# The `infer` body and its arms (task #55, `CORE_PLAN.md` step 6)

`crates/con-ron-core/src/cached/core_c.rs`'s **inference body** and the five
helpers its clauses are factored into, against con-leche's `inferBodyI`
(`ConLeche/Cached/CoreC.lean:1293-1389`).

## The `io` flag (task #18, deviation 4; narrowed by task #61)

con-leche hands a body the record's io view (`CoreFnsI.ioView`, whose `infer`
slot is the io slot); the Rust carries that choice as an `io : Bool`.
**Task #61 removed the flag from `infer_body_i`**: it used to be there, and
at `io = true` the Rust's `.app`, `.forallE` and `.lam` clauses called the
*full-grade* wrappers where `inferBodyI` at `ioView` calls the io slot, so
the `io = true` instance of this file's body lemma was **false as stated**.
Those three views are overridden by `inferBodyIOI`, so the flag only ever
mattered at `.proj`, which now has its own clause in `infer_body_io_i`
(`core_c.rs:3638`) and reaches `infer_proj_i … true` from there.

`infer_proj_i` therefore keeps the flag — it is the one helper that runs
under *both* records — and is stated once at `Arms/Shape.lean`'s
`knotV mode lfe fuel io`.  Every other helper here, `infer_body_i` included,
is stated at the full-grade `knot`.

## The clause lemmas are stated *against `inferBodyI` itself*

Every helper here computes one clause of `inferBodyI` and nothing else, so
its Lean side is `inferBodyI … d (<the node the clause matches>)` rather than
a transcription: nothing is paraphrased, and `infer_body_i_refines` is then
one `cases` on the observed `ExprKind` per clause.  The two *pure*
sub-helpers of the `.proj` clause (`infer_proj_at_i`,
`proj_type_at_checked_i`) sit below a recursive call, so they get the two
`*IL` transcriptions of the clause's tail — the cached-lane twins of task
#49's `inferProjAtL`/`projTypeAtCheckedL` (`Refine/CoreKInfer.lean`), with
`ProjEntry.typeAtI` in place of `ProjEntry.typeAt`; `inferBodyI_proj` is the
`rfl` that ties them back to the cited clause.

## Foreign callees

`infer_spine_i` (`Arms/InferSpine.lean`), `infer_pis_i` and `infer_lams_i`
(`Arms/InferTele.lean`) live in sibling agents' files, so they are the three
fields of `InferDeps` below.

## The full outcome (task #67)

`Sim` claims con-leche's *whole* outcome (`Refine/State.lean`'s `Out`), so
every clause here has a failure half beside its accept half.  All fourteen
`CheckError` sites this file meets are **mirrored** (DESIGN.md's task-#67
census: `cached/core_c.rs`'s forty-nine sites are one-to-one with a `throw`
in `Cached/CoreC.lean`), so each is discharged by one of the two moves the
README names: a callee's `ErrSim` carried through the rest of con-leche's
`do` block (`ErrSim.bindCM`), or an explicit `throw` arm whose guard the
accept direction already showed to agree.  The `.M`-suffixed `Array Std.U32`
constants are the *messages*, and those are never compared (DESIGN.md §3.1),
so they still carry no theorem — only the *kind* is claimed.

One site is neither of the two: the `.const` clause's unresolved arm, where
both sides build the error through a *named* builder (`unknownConstError`,
`core_k::unknown_const_error`) whose kind depends on the name — `sorryAx`
declines, everything else rejects.  `Refine/ErrKinds.lean`'s
`unknown_const_error_refines` is that site's leaf lemma (con-leche task #292).
-/
import ConRon.RefineOld.Core.Arms.Shape
import ConRon.Refine.CoreKPinned
import ConRon.RefineOld.ExprOpsC
import ConRon.RefineOld.ErrKinds

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Core

/-! ## The monad plumbing

`Arms/Shape.lean`'s set, re-declared: `attribute [local simp]` does not
survive an import. -/

attribute [local simp] except_pure' StateT.run modifyGet MonadStateOf.modifyGet
  StateT.modifyGet Bind.bind StateT.bind Pure.pure StateT.pure Except.bind
  Except.pure

/-- **`throw` in `CheckCM`**: the set above does not carry the `MonadExcept`
instance, so `simp` would leave an explicit `throw` arm of con-leche's un-run.
This is the one extra rewrite the failure halves need (task #67);
`Arms/Shared.lean` carries the same lemma for its own file. -/
@[local simp] private theorem throw_apply {β : Type} (le : ConLeche.CheckError)
    (lst : ConLeche.Cached.CState) :
    (throw le : ConLeche.Cached.CheckCM β) lst = .error le := rfl

/-! ## The full outcome: the shared bookkeeping (task #67)

`ErrSim.bindCM` (`Refine/State.lean`) is move 1 and needs no local help; these
three are the spelling of move 2 in this file — the port builds its error by
handing a code-point `Vec` to `core_types::invalid`/`not_implemented`/
`internal`, and the cited con-leche arm `throw`s at the same kind.  `err_arm`
reads the Rust's `Err(err) => Err(err)` arm, which pins both the outcome and
the state. -/

/-- The Rust's `Err(err) => Err(err)` arm: the error is handed straight on. -/
private theorem err_arm {α : Type} {err : core_types.CheckError}
    {o : core.result.Result α core_types.CheckError}
    {st1 st' : cached.state_c.CState}
    (h : Aeneas.Std.Result.ok (core.result.Result.Err err, st1)
      = Aeneas.Std.Result.ok (o, st')) :
    o = .Err err ∧ st' = st1 := by
  have h2 := Result.ok_injective h
  simp only [Prod.mk.injEq] at h2
  exact ⟨h2.1.symm, h2.2.symm⟩

/-- The same at a *state-free* helper (`CheckM`), where the Rust's `Err` arm
carries no state. -/
private theorem err_eq {α : Type} {ce1 ce : core_types.CheckError}
    (h : (Aeneas.Std.Result.ok (core.result.Result.Err ce1) :
            Result (core.result.Result α core_types.CheckError)) = ok (.Err ce)) :
    ce1 = ce := by simpa using Result.ok_injective h

/-- A mirrored `throw` at `invalid`. -/
private theorem invalid_throw {γ : Type} {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} {x : Except ConLeche.CheckError γ} {s : String}
    (hce : core_types.invalid v = ok ce) (hx : x = .error (.invalid s)) :
    ErrSim ce x := by
  have h1 : core_types.CheckError.Invalid v = ce :=
    Result.ok_injective (by rw [core_types.invalid] at hce; exact hce)
  rw [← h1]
  exact ErrSim.invalid hx

/-- A mirrored `throw` at `notImplemented`. -/
private theorem not_implemented_throw {γ : Type} {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} {x : Except ConLeche.CheckError γ} {s : String}
    (hce : core_types.not_implemented v = ok ce) (hx : x = .error (.notImplemented s)) :
    ErrSim ce x := by
  have h1 : core_types.CheckError.NotImplemented v = ce :=
    Result.ok_injective (by rw [core_types.not_implemented] at hce; exact hce)
  rw [← h1]
  exact ErrSim.notImplemented hx

/-- A mirrored `throw` at `internal`. -/
private theorem internal_throw {γ : Type} {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} {x : Except ConLeche.CheckError γ} {s : String}
    (hce : core_types.internal v = ok ce) (hx : x = .error (.internal s)) :
    ErrSim ce x := by
  have h1 : core_types.CheckError.Internal v = ce :=
    Result.ok_injective (by rw [core_types.internal] at hce; exact hce)
  rw [← h1]
  exact ErrSim.internal hx

/-! ## The abstraction of the two telescope stacks

`infer_pis_i` carries the domain sorts as a `Vec<(Level, PropWhen)>` pushed
at the back where con-leche conses a `List (Level × PropWhen)` at the front
(`CoreC.lean:1277-1287`), and `infer_lams_i` the binders as a
`Vec<(Expr, BinderMeta)>` against `List InferLamEntry`
(`CoreC.lean:1224-1225`); so both abstractions reverse.  They are used here
only at the one-element stack the `∀`/`λ` clauses start the loop with, but
the `InferDeps` fields need them in general. -/

/-- A `Vec<(Level, PropWhen)>` as `inferPisI`'s stack. -/
def absPiStk (stk : alloc.vec.Vec (level.Level × prop_when.PropWhen)) :
    List (ConLeche.Level × ConLeche.PropWhen) :=
  (stk.val.map (fun p => (absLevel p.1, absPropWhen p.2))).reverse

/-- Its well-formedness. -/
def PiStkWF (stk : alloc.vec.Vec (level.Level × prop_when.PropWhen)) : Prop :=
  ∀ p ∈ stk.val, LevelWF p.1 ∧ PropWhenWF p.2

/-- A `Vec<(Expr, BinderMeta)>` as `inferLamsI`'s stack. -/
def absLamStk (stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)) :
    List ConLeche.Cached.InferLamEntry :=
  (stk.val.map (fun p => (absExpr p.1, absBinderMeta p.2))).reverse

/-- Its well-formedness. -/
def LamStkWF (stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)) : Prop :=
  ∀ p ∈ stk.val, ExprWF p.1 ∧ BinderMetaWF p.2

/-! ## The foreign callees -/

/-- The three helpers of the `infer` cluster that live in a sibling agent's
file: the spine walk (`Arms/InferSpine.lean`) and the two binder-telescope
loops (`Arms/InferTele.lean`).  Each field is the statement that helper's own
`<fn>_refines` has. -/
structure InferDeps (mode : env.CheckMode) (fuel : Std.U64) : Prop where
  /-- `Arms/InferSpine.lean`'s `infer_spine_i_refines` (`core_c.rs:2663`,
  `CoreC.lean:1018-1067 inferSpineI`): the Rust walks `args` from the index
  `i`, con-leche recurses on the suffix. -/
  inferSpine : ∀ (d : Std.U64) (ty : expr.Expr) (acc args : alloc.vec.Vec expr.Expr)
      (i : Std.Usize), ExprWF ty → ExprsWF acc → ExprsWF args →
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_spine_i mode fuel st fe d ty acc args i)
      (fun lfe => ConLeche.Cached.inferSpineI (knot mode lfe fuel.val) lfe d.val
        (absExpr ty) (absExprs acc).toArray ((absExprs args).drop i.val))
  /-- `Arms/InferTele.lean`'s `infer_pis_i_refines` (`core_c.rs:3167`,
  `CoreC.lean:1274-1290 inferPisI`). -/
  inferPis : ∀ (d peel : Std.U64) (t : expr.Expr) (k : Std.U64)
      (fvs : alloc.vec.Vec expr.Expr)
      (stk : alloc.vec.Vec (level.Level × prop_when.PropWhen)),
    ExprWF t → ExprsWF fvs → PiStkWF stk →
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_pis_i mode fuel st fe d peel t k fvs stk)
      (fun lfe => ConLeche.Cached.inferPisI (absMode mode) (knot mode lfe fuel.val)
        d.val peel.val (absExpr t) k.val (absExprs fvs).toArray (absPiStk stk))
  /-- `Arms/InferTele.lean`'s `infer_lams_i_refines` (`core_c.rs:3047`,
  `CoreC.lean:1213-1228 inferLamsI`). -/
  inferLams : ∀ (d peel : Std.U64) (t : expr.Expr) (k : Std.U64)
      (fvs : alloc.vec.Vec expr.Expr)
      (stk : alloc.vec.Vec (expr.Expr × expr.BinderMeta)),
    ExprWF t → ExprsWF fvs → LamStkWF stk →
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_lams_i mode fuel st fe d peel t k fvs stk)
      (fun lfe => ConLeche.Cached.inferLamsI (absMode mode) (knot mode lfe fuel.val)
        d.val peel.val (absExpr t) k.val (absExprs fvs).toArray (absLamStk stk))

/-! ## The `.const` clause -/

section
variable {mode : env.CheckMode} {fuel : Std.U64}

/-- `ConLeche/Cached/CoreC.lean:1302-1315` — **`const_shape_probe_i` refines
the `.const` clause's two reads off the stored declaration**
(`core_c.rs:3252`): is it a projection-table entry, and how many level
parameters does it carry.  The port owns the probe (task #14's borrow rule);
con-leche reads the same two fields off `fe.find? n` in place. -/
theorem const_shape_probe_i_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {n : name.Name} (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe) (hn : NameWF n) :
    SimP (fun o : Option (Bool × Std.Usize) => o.map (fun p => (p.1, p.2.val)))
      (fun _ => True)
      (cached.core_c.const_shape_probe_i fe n)
      ((lfe.find? (absName n)).map
        (fun ci => (ci.isTowerEntry, ci.toConstantVal.levelParams.length))) := by
  intro o h
  refine ⟨?_, trivial⟩
  rw [cached.core_c.const_shape_probe_i] at h
  obtain ⟨oc, hfind, h⟩ := bind_eq_ok_iff.mp h
  have hlk := FEnv.find_refines hrel hwf hn hfind
  cases oc with
  | none =>
    simp only [Option.map_none] at hlk
    simp only [Result.ok.injEq] at h
    subst h
    rw [← hlk]; rfl
  | some ci =>
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨b, hb, cv, hcv, rfl⟩ := h
    simp only [Option.map_some] at hlk
    rw [← hlk]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    refine ⟨Env.is_tower_entry_refines hb, ?_⟩
    have hcvv := Env.to_constant_val_refines hcv
    have : absNames cv.level_params
        = (ConLeche.ConstantInfo.toConstantVal (absConstantInfo ci)).levelParams := by
      rw [← hcvv]; rfl
    rw [alloc.vec.Vec.len_val, ← this]
    simp [absNames]

/-- `ConLeche/Cached/CoreC.lean:1302-1315` — **`infer_const_i` refines
`inferBodyI`'s `.const` clause** (`core_c.rs:3268`): the constant is stored,
is not a projection table, carries the right number of universe levels, and
its type is `constTyAtM`'s (`Refine/StateC.lean`).  The clause makes no
recursive call, so it is the same under both records.  The unresolved arm is
con-leche's `unknownConstError`, not a plain `.invalid`: con-leche task #292
made `sorryAx` decline there, and the port mirrors it through
`core_k::unknown_const_error`. -/
theorem infer_const_i_refines (io : Bool) {n : name.Name}
    {us : alloc.vec.Vec level.Level} (hn : NameWF n) (hus : LevelsWF us) (d : Std.U64) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.infer_const_i st fe n us)
      (fun lfe => ConLeche.Cached.inferBodyI (absMode mode)
        (knotV mode lfe fuel.val io) lfe d.val (.const (absName n) (absLevels us))) := by
  intro fe lfe hfe hfrel st oc st' hwf hok lst hrel
  have hclause : ConLeche.Cached.inferBodyI (absMode mode)
      (knotV mode lfe fuel.val io) lfe d.val (.const (absName n) (absLevels us))
      = (do
        match lfe.find? (absName n) with
        | none => throw (ConLeche.unknownConstError (absName n))
        | some ci => do
          unless !ci.isTowerEntry do
            throw (.invalid
              s!"projection table entry used as a constant {absName n}")
          let cv := ci.toConstantVal
          unless (absLevels us).length = cv.levelParams.length do
            throw (.invalid
              s!"incorrect number of universe levels for {absName n}")
          ConLeche.Cached.constTyAtM lfe (absName n) (absName n) (absLevels us)) := rfl
  unfold cached.core_c.infer_const_i at hok
  obtain ⟨o, hprobe, hok⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨hoabs, -⟩ := const_shape_probe_i_refines hfrel hfe hn o hprobe
  cases o with
  | none =>
    -- the constant is not stored: `fe.find? n` is `none` on both sides and
    -- both take `unknownConstError` (`CoreC.lean:1305`), which declines at
    -- `sorryAx` and rejects at every other name (`Refine/ErrKinds.lean`)
    have hfind : lfe.find? (absName n) = none := by simpa using hoabs.symm
    simp only [bind_eq_ok_iff] at hok
    obtain ⟨ce, hce, hc⟩ := hok
    obtain ⟨rfl, rfl⟩ := err_arm hc
    refine ErrSim.mk (le := ConLeche.unknownConstError (absName n)) ?_
      (unknown_const_error_refines hn hce)
    simp [hclause, hfind]
  | some p =>
    obtain ⟨b, i⟩ := p
    simp only [Option.map_some] at hoabs
    -- the index read agrees, so the con-leche probe is a hit too
    cases hfind : lfe.find? (absName n) with
    | none => rw [hfind] at hoabs; simp at hoabs
    | some ci =>
      rw [hfind] at hoabs
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hoabs
      obtain ⟨hbv, hiv⟩ := hoabs
      -- the pattern-`let` Aeneas emits for the probe's pair: only the
      -- *unifier* sees through it (task #16's hard spot 1), so it goes by
      -- ascription
      replace hok :
          (if b = true then
              (do
                let s ← lift (Array.to_slice cached.core_c.infer_const_i.M_TOWER)
                let v ← core_types.code_points s
                let ce ← core_types.invalid v
                ok (core.result.Result.Err ce, st))
            else
              (if (alloc.vec.Vec.len us != i) = true then
                (do
                  let s ← lift (Array.to_slice cached.core_c.infer_const_i.M_LEVELS)
                  let v ← core_types.code_points s
                  let ce ← core_types.invalid v
                  ok (core.result.Result.Err ce, st))
              else cached.state_c.const_ty_at_m st fe n us))
            = ok (oc, st') := hok
      split at hok
      · -- a projection table used as a constant: both reject at `invalid`
        -- (`CoreC.lean:1307-1308`)
        rename_i hbt
        simp only [bind_eq_ok_iff, lift_eq] at hok
        obtain ⟨s1, -, v, -, ce, hce, hc⟩ := hok
        obtain ⟨rfl, rfl⟩ := err_arm hc
        refine invalid_throw
          (s := s!"projection table entry used as a constant {absName n}") hce ?_
        simp [hclause, hfind, ← hbv, hbt]
      rename_i hbf
      simp only [Bool.not_eq_true] at hbf
      split at hok
      · -- the wrong number of levels: both reject at `invalid`
        -- (`CoreC.lean:1310-1311`)
        rename_i hlen
        simp only [bne_iff_ne, ne_eq] at hlen
        have hlenv : ¬ ((absLevels us).length = ci.toConstantVal.levelParams.length) := by
          have h1 : (alloc.vec.Vec.len us).val = us.val.length := alloc.vec.Vec.len_val us
          simp only [absLevels, List.length_map]
          rw [← h1, ← hiv]
          intro hc
          exact hlen (Std.UScalar.eq_of_val_eq hc)
        simp only [bind_eq_ok_iff, lift_eq] at hok
        obtain ⟨s1, -, v, -, ce, hce, hc⟩ := hok
        obtain ⟨rfl, rfl⟩ := err_arm hc
        refine invalid_throw
          (s := s!"incorrect number of universe levels for {absName n}") hce ?_
        simp [hclause, hfind, ← hbv, hbf, hlenv]
      rename_i hlen
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
      have hlenv : (absLevels us).length = ci.toConstantVal.levelParams.length := by
        have h1 : (alloc.vec.Vec.len us).val = us.val.length := alloc.vec.Vec.len_val us
        simp only [absLevels, List.length_map]
        rw [← h1, hlen, hiv]
      have hbody : (ConLeche.Cached.inferBodyI (absMode mode)
            (knotV mode lfe fuel.val io) lfe d.val
            (.const (absName n) (absLevels us))).run lst
          = (ConLeche.Cached.constTyAtM lfe (absName n) (absName n)
              (absLevels us)).run lst := by
        simp only [hclause]
        simp [hfind, ← hbv, hbf, hlenv]
      cases oc with
      | Ok r =>
        obtain ⟨lst', hrun, hrel', hwf', hrwf⟩ :=
          StateC.const_ty_at_m_refines StateC.instLevelParamsRefines hwf hfe hn hus hok
            lst lfe hrel hfrel (absName n)
        exact ⟨lst', by rw [hbody]; exact hrun, hrel', hwf', hrwf⟩
      | Err ce =>
        -- `constTyAtM` threw: the clause's last step is the whole clause
        exact ErrSim.of_eq
          (StateC.const_ty_at_m_err hwf hfe hn hus hok lst lfe hrel hfrel (absName n))
          hbody

/-! ## The `.proj` clause

`CoreC.lean:1353-1381`.  Below its two recursive calls the clause is
state-free, so — exactly as task #49 does for the spec lane
(`Refine/CoreKInfer.lean`'s `inferProjAtL`/`projTypeAtCheckedL`) — the tail is
transcribed as a `CheckCM` action of the abstracted arguments, and
`inferBodyI_proj` is the `rfl` that ties the transcription back to the cited
clause.  The cached lane's only difference from the spec's is the type:
`ProjEntry.typeAtI` (memoised, sharing-preserving) rather than
`ProjEntry.typeAt`. -/

/-- `CoreC.lean:1360-1379` — the cited clause's three shape tests and its
possibly-`Prop` restriction, transcribed. -/
def projTypeAtCheckedIL (entry : ConLeche.ProjEntry) (sn T : ConLeche.Name)
    (us : List ConLeche.Level) (targs : List ConLeche.Expr) (pe : ConLeche.Expr) :
    ConLeche.Cached.CheckCM ConLeche.Expr := do
  if T = sn ∧ targs.length = entry.numParams ∧
      us.length = entry.levelParams.length then do
    if ConLeche.Level.isEquiv entry.structSort .zero == some true then
      unless ConLeche.Level.isEquiv
          (ConLeche.Level.subst entry.levelParams us entry.fieldSort) .zero
          == some true do
        throw (.invalid
          "projection from a propositional structure must be a proposition")
    pure (entry.typeAtI us targs pe)
  else throw (.notImplemented "projection without a native entry")

/-- `CoreC.lean:1356-1381` — the cited clause below its two recursive calls:
the reduced subject type `te` is a parameter, and the tail is the head-shape
match, the table lookup and `projTypeAtCheckedIL`. -/
def inferProjAtIL (lfe : ConLeche.FEnv) (sn : ConLeche.Name) (i : Nat)
    (pe te : ConLeche.Expr) : ConLeche.Cached.CheckCM ConLeche.Expr :=
  match ConLeche.Expr.getAppFn te with
  | .const T us =>
    match lfe.findProj? T i with
    | some entry =>
      projTypeAtCheckedIL entry sn T us (ConLeche.Expr.getAppArgsC te) pe
    | none => throw (.notImplemented "projection without a native entry")
  | _ => throw (.notImplemented "projection without a native entry")

/-- The transcription *is* the cited clause: `inferBodyI`'s `.proj` arm is its
two recursive calls followed by `inferProjAtIL`. -/
theorem inferBodyI_proj (lmode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (lfe : ConLeche.FEnv) (d : Nat) (sn : ConLeche.Name) (i : Nat)
    (pe : ConLeche.Expr) :
    ConLeche.Cached.inferBodyI lmode r lfe d (.proj sn i pe)
      = (do
        let tpe ← r.infer d pe
        let te ← r.whnf d tpe
        inferProjAtIL lfe sn i pe te) := rfl

/-- **The transcription's one non-literal step** (the cached twin of
`Refine/CoreKInfer.lean`'s `projPropGuard_eq`): the cited clause *inlines*
`ProjEntry.fireOk`'s body (`Core.lean:1250-1253`) as an `if`/`unless` pair
where the port calls the function; the two pick the same branch. -/
theorem projPropGuardIL (entry : ConLeche.ProjEntry) (us : List ConLeche.Level)
    (v : ConLeche.Expr) :
    (do
      if ConLeche.Level.isEquiv entry.structSort .zero == some true then
        unless ConLeche.Level.isEquiv
            (ConLeche.Level.subst entry.levelParams us entry.fieldSort) .zero
            == some true do
          throw (.invalid
            "projection from a propositional structure must be a proposition")
      pure v : ConLeche.Cached.CheckCM ConLeche.Expr)
      = (if entry.fireOk us then pure v
         else throw (.invalid
           "projection from a propositional structure must be a proposition")) := by
  simp only [ConLeche.ProjEntry.fireOk]
  by_cases h1 : (ConLeche.Level.isEquiv entry.structSort .zero == some true) = true
  · by_cases h2 : (ConLeche.Level.isEquiv
        (ConLeche.Level.subst entry.levelParams us entry.fieldSort) .zero
          == some true) = true
    · simp [h1, h2]
      all_goals rfl
    · simp only [h1, if_true, h2, Bool.not_true, Bool.false_or]
      rfl
  · simp [h1]
    all_goals rfl

/-- `ConLeche/Cached/CoreC.lean:1360-1379` — **`proj_type_at_checked_i` refines
the cited clause's checks and value** (`core_c.rs:3519`): on success all three
shape tests and the possibly-`Prop` guard pass in the Lean too, and the value
is `ProjEntry.typeAtI`'s (`Refine/ExprOpsCAbs.lean`).  State-free, so the
verdict is a monadic equation, not a `Sim`.

Stated over the whole outcome (task #67): all four of the port's verdicts here
are mirrored.  The three shape tests are the cited conjunction's
(`CoreC.lean:1360-1362`), and the port splits that one `if` into three
`else if` arms carrying the same message, so all three land on
`CoreC.lean:1381`'s `throw (.notImplemented "projection without a native
entry")`; the possibly-`Prop` restriction is `CoreC.lean:1370-1372`'s
`throw (.invalid …)`.  Messages are not compared.  The `.Err` arm is also
available on its own as `proj_type_at_checked_i_err` below. -/
theorem proj_type_at_checked_i_refines {entry : env.ProjEntry} {sn t : name.Name}
    {us : alloc.vec.Vec level.Level} {targs : alloc.vec.Vec expr.Expr}
    {pe : expr.Expr}
    {out : core.result.Result expr.Expr core_types.CheckError}
    (hent : ProjEntryWF entry) (hsn : NameWF sn) (ht : NameWF t)
    (hus : LevelsWF us) (htargs : ExprsWF targs) (hpe : ExprWF pe)
    (h : cached.core_c.proj_type_at_checked_i entry sn t us targs pe = ok out) :
    match out with
    | .Ok r =>
      projTypeAtCheckedIL (absProjEntry entry) (absName sn) (absName t) (absLevels us)
          (absExprs targs) (absExpr pe) = pure (absExpr r) ∧ ExprWF r
    | .Err ce => ∀ lst : ConLeche.Cached.CState,
      ErrSim ce ((projTypeAtCheckedIL (absProjEntry entry) (absName sn) (absName t)
        (absLevels us) (absExprs targs) (absExpr pe)).run lst) := by
  cases out with
  | Ok r =>
    unfold cached.core_c.proj_type_at_checked_i at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    have hbv : b = decide (absName t = absName sn) := Name.beq_refines ht hsn hb
    split at h
    case isFalse =>
      simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, reduceCtorEq,
        and_false, exists_false] at h
    rename_i hbt
    have hname : absName t = absName sn := by
      rw [hbv] at hbt; exact of_decide_eq_true hbt
    simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, exists_eq_left'] at h
    split at h
    case isTrue => simp only [bind_eq_ok_iff, Result.ok.injEq, reduceCtorEq, and_false,
        exists_false] at h
    rename_i hnp
    have hnpv : (absExprs targs).length = (absProjEntry entry).numParams := by
      have hc : (Std.UScalar.cast .U64 (alloc.vec.Vec.len targs) : Std.U64).val
          = targs.val.length := by
        rw [ExprOps.usize_cast_u64_val]
        exact alloc.vec.Vec.len_val targs
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hnp
      rw [hnp] at hc
      simp only [absExprs, List.length_map, absProjEntry]
      exact hc.symm
    split at h
    case isTrue => simp only [bind_eq_ok_iff, Result.ok.injEq, reduceCtorEq, and_false,
        exists_false] at h
    rename_i hlp
    have hlpv : (absLevels us).length = (absProjEntry entry).levelParams.length := by
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlp
      have h1 : (alloc.vec.Vec.len us).val = us.val.length := alloc.vec.Vec.len_val us
      have h2 : (alloc.vec.Vec.len entry.level_params).val
          = entry.level_params.val.length := alloc.vec.Vec.len_val entry.level_params
      have h3 : (alloc.vec.Vec.len us).val
          = (alloc.vec.Vec.len entry.level_params).val := by rw [hlp]
      simp only [absLevels, absProjEntry, absNames, List.length_map]
      omega
    simp only [bind_eq_ok_iff] at h
    obtain ⟨c, hc, h⟩ := h
    have hcv := CoreK.projEntryFireOk entry us c hent hus hc
    split at h
    case isFalse => simp only [bind_eq_ok_iff, Result.ok.injEq, reduceCtorEq, and_false,
        exists_false] at h
    rename_i hct
    simp only [bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨e, he, hr⟩ := h
    cases hr
    obtain ⟨habs, hwf⟩ :=
      ExprOpsC.proj_entry_type_at_i_refines hent hus htargs hpe he
    refine ⟨?_, hwf⟩
    rw [projTypeAtCheckedIL, if_pos ⟨hname, hnpv, hlpv⟩, projPropGuardIL,
      if_pos (show (absProjEntry entry).fireOk (absLevels us) = true by
        rw [← hcv]; exact hct), habs]
  | Err ce =>
    intro lst
    unfold cached.core_c.proj_type_at_checked_i at h
    simp only [bind_eq_ok_iff] at h
    obtain ⟨b, hb, h⟩ := h
    have hbv : b = decide (absName t = absName sn) := Name.beq_refines ht hsn hb
    split at h
    case isFalse =>
      -- the head name is not the node's structure name
      rename_i hbf
      have hne : absName t ≠ absName sn := by rw [hbv] at hbf; simpa using hbf
      simp only [bind_eq_ok_iff, lift_eq] at h
      obtain ⟨_, -, _, -, ce1, hce1, hr⟩ := h
      obtain rfl := err_eq hr
      refine not_implemented_throw (s := "projection without a native entry") hce1 ?_
      rw [projTypeAtCheckedIL, if_neg (fun hcon => hne hcon.1)]
      simp
    rename_i hbt
    have hname : absName t = absName sn := by
      rw [hbv] at hbt; exact of_decide_eq_true hbt
    have hcl : (Std.UScalar.cast .U64 (alloc.vec.Vec.len targs) : Std.U64).val
        = targs.val.length := by
      rw [ExprOps.usize_cast_u64_val]
      exact alloc.vec.Vec.len_val targs
    simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, exists_eq_left'] at h
    split at h
    case isTrue =>
      -- the wrong number of structure parameters
      rename_i hnp
      have hnpv : (absExprs targs).length ≠ (absProjEntry entry).numParams := by
        simp only [bne_iff_ne, ne_eq] at hnp
        simp only [absExprs, List.length_map, absProjEntry]
        intro hEq
        exact hnp (by scalar_tac)
      simp only [bind_eq_ok_iff] at h
      obtain ⟨_, -, _, -, ce1, hce1, hr⟩ := h
      obtain rfl := err_eq hr
      refine not_implemented_throw (s := "projection without a native entry") hce1 ?_
      rw [projTypeAtCheckedIL, if_neg (fun hcon => hnpv hcon.2.1)]
      simp
    rename_i hnp
    have hnpv : (absExprs targs).length = (absProjEntry entry).numParams := by
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hnp
      rw [hnp] at hcl
      simp only [absExprs, List.length_map, absProjEntry]
      exact hcl.symm
    split at h
    case isTrue =>
      -- the wrong number of universe levels
      rename_i hlp
      have hlpv : (absLevels us).length ≠ (absProjEntry entry).levelParams.length := by
        simp only [bne_iff_ne, ne_eq] at hlp
        have h1 : (alloc.vec.Vec.len us).val = us.val.length := alloc.vec.Vec.len_val us
        have h2 : (alloc.vec.Vec.len entry.level_params).val
            = entry.level_params.val.length := alloc.vec.Vec.len_val entry.level_params
        simp only [absLevels, absProjEntry, absNames, List.length_map]
        intro hEq
        exact hlp (by scalar_tac)
      simp only [bind_eq_ok_iff] at h
      obtain ⟨_, -, _, -, ce1, hce1, hr⟩ := h
      obtain rfl := err_eq hr
      refine not_implemented_throw (s := "projection without a native entry") hce1 ?_
      rw [projTypeAtCheckedIL, if_neg (fun hcon => hlpv hcon.2.2)]
      simp
    rename_i hlp
    have hlpv : (absLevels us).length = (absProjEntry entry).levelParams.length := by
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlp
      have h1 : (alloc.vec.Vec.len us).val = us.val.length := alloc.vec.Vec.len_val us
      have h2 : (alloc.vec.Vec.len entry.level_params).val
          = entry.level_params.val.length := alloc.vec.Vec.len_val entry.level_params
      have h3 : (alloc.vec.Vec.len us).val
          = (alloc.vec.Vec.len entry.level_params).val := by rw [hlp]
      simp only [absLevels, absProjEntry, absNames, List.length_map]
      omega
    simp only [bind_eq_ok_iff] at h
    obtain ⟨c, hcf, h⟩ := h
    have hcv := CoreK.projEntryFireOk entry us c hent hus hcf
    split at h
    case isTrue =>
      simp only [bind_eq_ok_iff, Result.ok.injEq] at h
      obtain ⟨_, -, hcontra⟩ := h
      exact absurd hcontra (by simp)
    rename_i hcfalse
    -- the projection is out of a propositional structure into a non-proposition
    simp only [bind_eq_ok_iff] at h
    obtain ⟨_, -, _, -, ce1, hce1, hr⟩ := h
    obtain rfl := err_eq hr
    refine invalid_throw
      (s := "projection from a propositional structure must be a proposition") hce1 ?_
    rw [projTypeAtCheckedIL, if_pos ⟨hname, hnpv, hlpv⟩, projPropGuardIL,
      if_neg (by rw [← hcv]; exact hcfalse)]
    simp

/-- `proj_type_at_checked_i_refines` at a failure, the pre-#67 statement.  The
two well-formedness hypotheses on `targs` and `pe` are the shared statement's;
only its accept arm needs them. -/
theorem proj_type_at_checked_i_err {entry : env.ProjEntry} {sn t : name.Name}
    {us : alloc.vec.Vec level.Level} {targs : alloc.vec.Vec expr.Expr}
    {pe : expr.Expr} {ce : core_types.CheckError}
    (hent : ProjEntryWF entry) (hsn : NameWF sn) (ht : NameWF t) (hus : LevelsWF us)
    (htargs : ExprsWF targs) (hpe : ExprWF pe)
    (h : cached.core_c.proj_type_at_checked_i entry sn t us targs pe = ok (.Err ce))
    (lst : ConLeche.Cached.CState) :
    ErrSim ce ((projTypeAtCheckedIL (absProjEntry entry) (absName sn) (absName t)
      (absLevels us) (absExprs targs) (absExpr pe)).run lst) :=
  proj_type_at_checked_i_refines hent hsn ht hus htargs hpe h lst

/-- `ConLeche/Cached/CoreC.lean:1356-1381` — **`infer_proj_at_i` refines the
cited clause's tail** (`core_c.rs:3484`): the head shape of the reduced subject
type, the projection-table lookup (`Refine/CoreKProj.lean`'s
`find_proj_refines`, which also hands back the entry's well-formedness) and
`proj_type_at_checked_i`.  State-free, so the accept verdict is a monadic
equation, not a `Sim`.

Stated over the whole outcome (task #67): a head that is not a `.const` and a
missing table entry are the cited clause's two other
`throw (.notImplemented "projection without a native entry")`s
(`CoreC.lean:1380` and `:1379`), and the `some entry` route is
`proj_type_at_checked_i_refines`'s own `.Err` arm.  The `.Err` arm is also
available on its own as `infer_proj_at_i_err` below. -/
theorem infer_proj_at_i_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {sn : name.Name} {i : Std.U64} {pe te : expr.Expr}
    {out : core.result.Result expr.Expr core_types.CheckError}
    (hrel : FEnvRel fe lfe) (hfwf : FEnvWF fe)
    (hsn : NameWF sn) (hpe : ExprWF pe) (hte : ExprWF te)
    (h : cached.core_c.infer_proj_at_i fe sn i pe te = ok out) :
    match out with
    | .Ok r =>
      inferProjAtIL lfe (absName sn) i.val (absExpr pe) (absExpr te)
          = pure (absExpr r) ∧ ExprWF r
    | .Err ce => ∀ lst : ConLeche.Cached.CState,
      ErrSim ce ((inferProjAtIL lfe (absName sn) i.val (absExpr pe)
        (absExpr te)).run lst) := by
  cases out with
  | Ok r =>
    unfold cached.core_c.infer_proj_at_i at h
    simp only [bind_eq_ok_iff, expr_view_eq, arc_deref_eq, Result.ok.injEq, exists_eq_left'] at h
    obtain ⟨f, hf, h⟩ := h
    obtain ⟨hfabs, hfnwf⟩ := ExprOps.get_app_fn_refines hte hf
    obtain ⟨⟨fd, fk⟩⟩ := f
    cases fk
    case Const t us' =>
      simp only [ExprOps.node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
      obtain ⟨o, ho, h⟩ := h
      obtain ⟨hnwf, huswf⟩ := CoreK.constKind_wf_inv hfnwf rfl
      obtain ⟨hoabs, howf⟩ := ConRon.Refine.find_proj_refines
        (ConRon.Refine.FindAgree.of_rel hrel hfwf)
        (ConRon.Refine.FindWF.of_wf hfwf) hnwf ho
      have hgf : ConLeche.Expr.getAppFn (absExpr te)
          = .const (absName t) (absLevels us') := by
        rw [← hfabs]; rfl
      cases o with
      | none =>
        simp only [bind_eq_ok_iff, lift_eq, Result.ok.injEq, reduceCtorEq,
          and_false, exists_false] at h
      | some entry =>
        simp only [Option.map_some] at hoabs
        simp only [bind_eq_ok_iff, Result.ok.injEq, exists_eq_left'] at h
        obtain ⟨targs, hta, h⟩ := h
        obtain ⟨htabs, htawf⟩ := ExprOps.get_app_args_refines hte hta
        obtain ⟨hres, hrwf⟩ := proj_type_at_checked_i_refines (howf entry rfl)
          hsn hnwf huswf htawf hpe h
        refine ⟨?_, hrwf⟩
        have htabs' : ConLeche.Expr.getAppArgsC (absExpr te)
            = absExprs targs := by
          rw [ConLeche.Expr.getAppArgsC_spec, ← htabs]
        have hfp : lfe.findProj? (absName t) i.val = some (absProjEntry entry) := hoabs.symm
        simpa only [inferProjAtIL, hgf, htabs', hfp] using hres
    all_goals
      simp only [ExprOps.node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff, lift_eq, Result.ok.injEq,
        reduceCtorEq, and_false, exists_false] at h
  | Err ce =>
    intro lst
    unfold cached.core_c.infer_proj_at_i at h
    simp only [bind_eq_ok_iff, expr_view_eq, arc_deref_eq, Result.ok.injEq, exists_eq_left'] at h
    obtain ⟨f, hf, h⟩ := h
    obtain ⟨hfabs, hfnwf⟩ := ExprOps.get_app_fn_refines hte hf
    obtain ⟨⟨fd, fk⟩⟩ := f
    cases fk
    case Const t us' =>
      simp only [ExprOps.node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff] at h
      obtain ⟨o, ho, h⟩ := h
      obtain ⟨hnwf, huswf⟩ := CoreK.constKind_wf_inv hfnwf rfl
      obtain ⟨hoabs, howf⟩ := ConRon.Refine.find_proj_refines
        (ConRon.Refine.FindAgree.of_rel hrel hfwf)
        (ConRon.Refine.FindWF.of_wf hfwf) hnwf ho
      have hgf : ConLeche.Expr.getAppFn (absExpr te)
          = .const (absName t) (absLevels us') := by
        rw [← hfabs]; rfl
      cases o with
      | none =>
        simp only [Option.map_none] at hoabs
        simp only [bind_eq_ok_iff, lift_eq] at h
        obtain ⟨_, -, _, -, ce1, hce1, hr⟩ := h
        obtain rfl := err_eq hr
        refine not_implemented_throw (s := "projection without a native entry") hce1 ?_
        simp only [inferProjAtIL, hgf, ← hoabs]
        simp
      | some entry =>
        simp only [Option.map_some] at hoabs
        simp only [bind_eq_ok_iff, Result.ok.injEq, exists_eq_left'] at h
        obtain ⟨targs, hta, h⟩ := h
        obtain ⟨htabs, htawf⟩ := ExprOps.get_app_args_refines hte hta
        have hres := proj_type_at_checked_i_err (howf entry rfl) hsn hnwf huswf
          htawf hpe h lst
        have htabs' : ConLeche.Expr.getAppArgsC (absExpr te) = absExprs targs := by
          rw [ConLeche.Expr.getAppArgsC_spec, ← htabs]
        have hfp : lfe.findProj? (absName t) i.val = some (absProjEntry entry) := hoabs.symm
        simpa only [inferProjAtIL, hgf, htabs', hfp] using hres
    all_goals
      simp only [ExprOps.node_kind, ron.node.ExprView.ofKind, bind_eq_ok_iff, lift_eq] at h
      obtain ⟨_, -, _, -, ce1, hce1, hr⟩ := h
      obtain rfl := err_eq hr
      refine not_implemented_throw (s := "projection without a native entry") hce1 ?_
      rw [inferProjAtIL, ← hfabs]
      simp

/-- `infer_proj_at_i_refines` at a failure, the pre-#67 statement. -/
theorem infer_proj_at_i_err {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {sn : name.Name} {i : Std.U64} {pe te : expr.Expr}
    {ce : core_types.CheckError}
    (hrel : FEnvRel fe lfe) (hfwf : FEnvWF fe)
    (hsn : NameWF sn) (hpe : ExprWF pe) (hte : ExprWF te)
    (h : cached.core_c.infer_proj_at_i fe sn i pe te = ok (.Err ce))
    (lst : ConLeche.Cached.CState) :
    ErrSim ce ((inferProjAtIL lfe (absName sn) i.val (absExpr pe) (absExpr te)).run lst) :=
  infer_proj_at_i_refines hrel hfwf hsn hpe hte h lst

/-- `ConLeche/Cached/CoreC.lean:1353-1381` — **`infer_proj_i` refines
`inferBodyI`'s `.proj` clause** (`core_c.rs:3558`): the subject's type at the
grade the flag selects (`infer_at_i`, `Shape.lean`'s `Wrappers.inferAtSim`),
its weak head normal form, and then `infer_proj_at_i`.  This is the one clause
the io body does *not* override, which is why the flag is carried this far
(task #18, deviation 4). -/
theorem infer_proj_i_refines (hw : Wrappers mode fuel) (d : Std.U64) (io : Bool)
    {sn : name.Name} {i : Std.U64} {pe : expr.Expr}
    (hsn : NameWF sn) (hpe : ExprWF pe) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_proj_i mode fuel st fe d sn i pe io)
      (fun lfe => ConLeche.Cached.inferBodyI (absMode mode)
        (knotV mode lfe fuel.val io) lfe d.val
        (.proj (absName sn) i.val (absExpr pe))) := by
  intro fe lfe hfe hfrel st oc st' hwf hok lst hrel
  unfold cached.core_c.infer_proj_i at hok
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := bind_eq_ok_iff.mp hok
  cases r0 with
  | Err err =>
    -- the subject's inference threw: con-leche's bind carries it
    obtain ⟨rfl, rfl⟩ := err_arm hok
    refine Out.err ?_
    simp only [inferBodyI_proj]
    exact ErrSim.bindCM ((hw.inferAtSim d io hpe).apply_err hwf hfe h1 hrel hfrel)
  | Ok tpe =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, htpeWF⟩ :=
      (hw.inferAtSim d io hpe).apply hwf hfe h1 hrel hfrel
    have e1 : (if io = true then (knot mode lfe fuel.val).inferIO
               else (knot mode lfe fuel.val).infer) d.val (absExpr pe) lst
        = Except.ok (absExpr tpe, lst1) := by
      rw [← knotV_infer]; exact hrun1
    obtain ⟨⟨r1, st2⟩, h2, hok⟩ := bind_eq_ok_iff.mp hok
    cases r1 with
    | Err err =>
      -- the reduction of that type threw
      obtain ⟨rfl, rfl⟩ := err_arm hok
      refine Out.err (ErrSim.trans
        ((hw.whnfSim d htpeWF).apply_err hwf1 hfe h2 hrel1 hfrel) ?_)
      intro le hle
      simp only [StateT.run] at hle
      simp only [inferBodyI_proj]
      simp [e1, hle]
    | Ok te =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, hteWF⟩ :=
        (hw.whnfSim d htpeWF).apply hwf1 hfe h2 hrel1 hfrel
      have e2 : (knot mode lfe fuel.val).whnf d.val (absExpr tpe) lst1
          = Except.ok (absExpr te, lst2) := hrun2
      obtain ⟨r2, h3, hok⟩ := bind_eq_ok_iff.mp hok
      simp only [Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨hr2, rfl⟩ := hok
      subst hr2
      cases r2 with
      | Ok r =>
        obtain ⟨htail, hrwf⟩ :=
          infer_proj_at_i_refines hfrel hfe hsn hpe hteWF h3
        refine ⟨lst2, ?_, hrel2, hwf2, hrwf⟩
        have e3 : inferProjAtIL lfe (absName sn) i.val (absExpr pe) (absExpr te) lst2
            = Except.ok (absExpr r, lst2) := by rw [htail]; rfl
        simp only [inferBodyI_proj]
        simp [e1, e2, e3]
      | Err ce =>
        -- the clause's tail threw: its three verdicts are all mirrored
        refine Out.err (ErrSim.trans
          (infer_proj_at_i_err hfrel hfe hsn hpe hteWF h3 lst2) ?_)
        intro le hle
        simp only [StateT.run] at hle
        simp only [inferBodyI_proj]
        simp [e1, e2, hle]

/-! ## The `∀` and `λ` clauses

`CoreC.lean:1325-1341`.  Each checks the first binder's domain to be a type
inline and hands the rest of the chain to its binder-telescope loop at the
peel fuel (`InferDeps.inferPis` / `InferDeps.inferLams`).  Neither Rust
function takes `io`: the io body overrides both clauses (`infer_forall_io_i` /
`infer_lam_io_i`), so these run only under the full-grade record. -/

/-- `inferBodyI`'s `.forallE` arm, opened. -/
theorem inferBodyI_forallE (lmode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (lfe : ConLeche.FEnv) (d : Nat) (ty body : ConLeche.Expr)
    (mb : ConLeche.BinderMeta) :
    ConLeche.Cached.inferBodyI lmode r lfe d (.forallE ty body mb)
      = (do
        let tty ← r.infer d ty
        let wtty ← r.whnf d tty
        match wtty with
        | .sort u =>
          ConLeche.Cached.inferPisI lmode r d ConLeche.Cached.peelFuel body 1
            #[ConLeche.Expr.fvar d ty] [(u, mb.pw)]
        | _ => throw (.invalid "expected a sort")) := rfl

/-- `inferBodyI`'s `.lam` arm, opened. -/
theorem inferBodyI_lam (lmode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (lfe : ConLeche.FEnv) (d : Nat) (ty body : ConLeche.Expr)
    (mb : ConLeche.BinderMeta) :
    ConLeche.Cached.inferBodyI lmode r lfe d (.lam ty body mb)
      = (do
        let tty ← r.infer d ty
        let wtty ← r.whnf d tty
        match wtty with
        | .sort _ =>
          ConLeche.Cached.inferLamsI lmode r d ConLeche.Cached.peelFuel body 1
            #[ConLeche.Expr.fvar d ty] [(ty, mb)]
        | _ => throw (.invalid "expected a sort")) := rfl

/-- `ConLeche/Cached/CoreC.lean:1325-1334` — **`infer_forall_i` refines
`inferBodyI`'s `.forallE` clause** (`core_c.rs:3369`): the domain's type, its
weak head normal form, the `Sort` shape, and then the `∀`-telescope loop at the
peel fuel with the first binder already opened.  The Rust starts the loop's
stack as a one-element `Vec` where con-leche conses onto `[]`; `absPiStk`
reverses, which is the identity at one element. -/
theorem infer_forall_i_refines (hw : Wrappers mode fuel) (hd : InferDeps mode fuel)
    (d : Std.U64) {ty body : expr.Expr} {mb : expr.BinderMeta}
    (hty : ExprWF ty) (hbody : ExprWF body) (hmb : BinderMetaWF mb) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_forall_i mode fuel st fe d ty body mb)
      (fun lfe => ConLeche.Cached.inferBodyI (absMode mode) (knot mode lfe fuel.val)
        lfe d.val (.forallE (absExpr ty) (absExpr body) (absBinderMeta mb))) := by
  intro fe lfe hfe hfrel st oc st' hwf hok lst hrel
  unfold cached.core_c.infer_forall_i at hok
  obtain ⟨⟨r0, st1⟩, h1, k1⟩ := bind_eq_ok_iff.mp hok
  cases r0 with
  | Err err =>
    -- the domain's inference threw: con-leche's bind carries it
    obtain ⟨rfl, rfl⟩ := err_arm k1
    refine Out.err ?_
    simp only [inferBodyI_forallE]
    exact ErrSim.bindCM ((hw.inferSim d hty).apply_err hwf hfe h1 hrel hfrel)
  | Ok tty =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, httyWF⟩ :=
      (hw.inferSim d hty).apply hwf hfe h1 hrel hfrel
    have e1 : (knot mode lfe fuel.val).infer d.val (absExpr ty) lst
        = Except.ok (absExpr tty, lst1) := hrun1
    obtain ⟨⟨r1, st2⟩, h2, k2⟩ := bind_eq_ok_iff.mp k1
    cases r1 with
    | Err err =>
      -- its reduction threw
      obtain ⟨rfl, rfl⟩ := err_arm k2
      refine Out.err (ErrSim.trans
        ((hw.whnfSim d httyWF).apply_err hwf1 hfe h2 hrel1 hfrel) ?_)
      intro le hle
      simp only [StateT.run] at hle
      simp only [inferBodyI_forallE]
      simp [e1, hle]
    | Ok wtty =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, hwttyWF⟩ :=
        (hw.whnfSim d httyWF).apply hwf1 hfe h2 hrel1 hfrel
      obtain ⟨⟨dw, kd⟩⟩ := wtty
      obtain ⟨en, hen, k3⟩ := bind_eq_ok_iff.mp k2
      have henv : en = ron.node.ExprView.ofKind kd := by simpa using hen.symm
      subst henv
      cases kd
      case «Sort» u =>
        have huWF : LevelWF u := CoreK.wf_sort_inv hwttyWF rfl
        obtain ⟨u1, hu1, k4⟩ := bind_eq_ok_iff.mp k3
        rw [level_dup_eq] at hu1
        rw [← Result.ok_injective hu1] at k4
        obtain ⟨e, hdup, k5⟩ := bind_eq_ok_iff.mp k4
        rw [Expr.dup_eq hdup] at k5
        obtain ⟨fv, hfv, k6⟩ := bind_eq_ok_iff.mp k5
        obtain ⟨fvs, hfvs, k7⟩ := bind_eq_ok_iff.mp k6
        obtain ⟨pw1, hpw1, k8⟩ := bind_eq_ok_iff.mp k7
        rw [PropWhen.dup_eq hpw1] at k8
        obtain ⟨stk, hstk, k9⟩ := bind_eq_ok_iff.mp k8
        obtain ⟨pf, hpf, k10⟩ := bind_eq_ok_iff.mp k9
        have hpfv : pf.val = ConLeche.Cached.peelFuel := StateC.peel_fuel_refines hpf
        have hfvsabs : (absExprs fvs).toArray
            = #[(ConLeche.Expr.fvar d.val (absExpr ty))] := by
          rw [ExprOps.absExprs_push hfvs, Expr.fvar_refines hfv]
          rfl
        have hfvsWF : ExprsWF fvs :=
          ExprOps.exprsWF_push ExprOps.exprsWF_new (Expr.fvar_wf hty hfv) hfvs
        have hstkabs : absPiStk stk = [(absLevel u, absPropWhen mb.pw)] := by
          rw [absPiStk, vec_push_val hstk]
          rfl
        have hstkWF : PiStkWF stk := by
          intro q hq
          have hqe : q = (u, mb.pw) := by
            rw [vec_push_val hstk] at hq
            simpa using hq
          rw [hqe]
          exact ⟨huWF, hmb⟩
        have e2 : (knot mode lfe fuel.val).whnf d.val (absExpr tty) lst1
            = Except.ok (ConLeche.Expr.sort (absLevel u), lst2) := by
          simpa using hrun2
        -- the whole clause *is* the telescope loop from here, at either
        -- outcome (task #67): `infer_pis_i` carries its own failure half
        have heq : (ConLeche.Cached.inferBodyI (absMode mode) (knot mode lfe fuel.val)
              lfe d.val
              (.forallE (absExpr ty) (absExpr body) (absBinderMeta mb))).run lst
            = (ConLeche.Cached.inferPisI (absMode mode) (knot mode lfe fuel.val)
                d.val pf.val (absExpr body) (1#u64 : Std.U64).val
                (absExprs fvs).toArray (absPiStk stk)).run lst2 := by
          rw [hpfv, hfvsabs, hstkabs]
          simp only [inferBodyI_forallE]
          simp [e1, e2, absBinderMeta]
        rw [heq]
        exact (hd.inferPis d pf body 1#u64 fvs stk hbody hfvsWF hstkWF)
          fe lfe hfe hfrel st2 oc st' hwf2 k10 lst2 hrel2
      all_goals
        -- the domain's type is not a sort: both reject at `invalid`
        -- (`CoreC.lean:1334`)
        obtain ⟨s1, -, m1⟩ := bind_eq_ok_iff.mp k3
        obtain ⟨v1, -, m2⟩ := bind_eq_ok_iff.mp m1
        obtain ⟨ce, hce, m3⟩ := bind_eq_ok_iff.mp m2
        obtain ⟨rfl, rfl⟩ := err_arm m3
        refine Out.err (invalid_throw (s := "expected a sort") hce ?_)
        simp only [StateT.run] at hrun2
        simp only [inferBodyI_forallE]
        simp [e1, hrun2, absExpr_mk, absExprKind]

/-- `ConLeche/Cached/CoreC.lean:1336-1344` — **`infer_lam_i` refines
`inferBodyI`'s `.lam` clause** (`core_c.rs:3417`): the domain's type, its weak
head normal form, the `Sort` shape (through `core_k::is_sort`, the port's
boolean form of the cited `match`), and then the λ-telescope loop at the peel
fuel with the first binder already opened.

At the full outcome (task #67), as for `∀`: the recursive calls' errors travel
through con-leche's binds, a non-`Sort` domain type is `CoreC.lean:1344`'s own
`throw (.invalid "expected a sort")`, and the tail is the loop. -/
theorem infer_lam_i_refines (hw : Wrappers mode fuel) (hd : InferDeps mode fuel)
    (d : Std.U64) {ty body : expr.Expr} {mb : expr.BinderMeta}
    (hty : ExprWF ty) (hbody : ExprWF body) (hmb : BinderMetaWF mb) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_lam_i mode fuel st fe d ty body mb)
      (fun lfe => ConLeche.Cached.inferBodyI (absMode mode) (knot mode lfe fuel.val)
        lfe d.val (.lam (absExpr ty) (absExpr body) (absBinderMeta mb))) := by
  intro fe lfe hfe hfrel st oc st' hwf hok lst hrel
  unfold cached.core_c.infer_lam_i at hok
  obtain ⟨⟨r0, st1⟩, h1, k1⟩ := bind_eq_ok_iff.mp hok
  cases r0 with
  | Err err =>
    -- the domain's inference threw
    obtain ⟨rfl, rfl⟩ := err_arm k1
    refine Out.err ?_
    simp only [inferBodyI_lam]
    exact ErrSim.bindCM ((hw.inferSim d hty).apply_err hwf hfe h1 hrel hfrel)
  | Ok tty =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, httyWF⟩ :=
      (hw.inferSim d hty).apply hwf hfe h1 hrel hfrel
    have e1 : (knot mode lfe fuel.val).infer d.val (absExpr ty) lst
        = Except.ok (absExpr tty, lst1) := hrun1
    obtain ⟨⟨r1, st2⟩, h2, k2⟩ := bind_eq_ok_iff.mp k1
    cases r1 with
    | Err err =>
      -- its reduction threw
      obtain ⟨rfl, rfl⟩ := err_arm k2
      refine Out.err (ErrSim.trans
        ((hw.whnfSim d httyWF).apply_err hwf1 hfe h2 hrel1 hfrel) ?_)
      intro le hle
      simp only [StateT.run] at hle
      simp only [inferBodyI_lam]
      simp [e1, hle]
    | Ok wtty =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, hwttyWF⟩ :=
        (hw.whnfSim d httyWF).apply hwf1 hfe h2 hrel1 hfrel
      obtain ⟨⟨dw, kd⟩⟩ := wtty
      obtain ⟨b, hb, k3⟩ := bind_eq_ok_iff.mp k2
      have hbv := CoreK.is_sort_refines hb
      cases kd
      case «Sort» u =>
        rw [if_pos (show b = true by rw [hbv]; simp)] at k3
        obtain ⟨e, hdup, k4⟩ := bind_eq_ok_iff.mp k3
        rw [Expr.dup_eq hdup] at k4
        obtain ⟨fv, hfv, k5⟩ := bind_eq_ok_iff.mp k4
        obtain ⟨fvs, hfvs, k6⟩ := bind_eq_ok_iff.mp k5
        obtain ⟨bm, hbm, k7⟩ := bind_eq_ok_iff.mp k6
        rw [Expr.binder_meta_dup_eq hbm] at k7
        obtain ⟨stk, hstk, k8⟩ := bind_eq_ok_iff.mp k7
        obtain ⟨pf, hpf, k9⟩ := bind_eq_ok_iff.mp k8
        have hpfv : pf.val = ConLeche.Cached.peelFuel := StateC.peel_fuel_refines hpf
        have hfvsabs : (absExprs fvs).toArray
            = #[(ConLeche.Expr.fvar d.val (absExpr ty))] := by
          rw [ExprOps.absExprs_push hfvs, Expr.fvar_refines hfv]
          rfl
        have hfvsWF : ExprsWF fvs :=
          ExprOps.exprsWF_push ExprOps.exprsWF_new (Expr.fvar_wf hty hfv) hfvs
        have hstkabs : absLamStk stk = [(absExpr ty, absBinderMeta mb)] := by
          rw [absLamStk, vec_push_val hstk]
          rfl
        have hstkWF : LamStkWF stk := by
          intro q hq
          have hqe : q = (ty, mb) := by
            rw [vec_push_val hstk] at hq
            simpa using hq
          rw [hqe]
          exact ⟨hty, hmb⟩
        have e2 : (knot mode lfe fuel.val).whnf d.val (absExpr tty) lst1
            = Except.ok (ConLeche.Expr.sort (absLevel u), lst2) := by
          simpa using hrun2
        -- the clause is the λ-telescope loop from here, at either outcome
        have heq : (ConLeche.Cached.inferBodyI (absMode mode) (knot mode lfe fuel.val)
              lfe d.val
              (.lam (absExpr ty) (absExpr body) (absBinderMeta mb))).run lst
            = (ConLeche.Cached.inferLamsI (absMode mode) (knot mode lfe fuel.val)
                d.val pf.val (absExpr body) (1#u64 : Std.U64).val
                (absExprs fvs).toArray (absLamStk stk)).run lst2 := by
          rw [hpfv, hfvsabs, hstkabs]
          simp only [absBinderMeta]
          simp only [inferBodyI_lam]
          simp [e1, e2]
        rw [heq]
        exact (hd.inferLams d pf body 1#u64 fvs stk hbody hfvsWF hstkWF)
          fe lfe hfe hfrel st2 oc st' hwf2 k9 lst2 hrel2
      all_goals
        -- the domain's type is not a sort: both reject at `invalid`
        -- (`CoreC.lean:1344`)
        rw [if_neg (show ¬ b = true by rw [hbv]; simp)] at k3
        obtain ⟨s1, -, m1⟩ := bind_eq_ok_iff.mp k3
        obtain ⟨v1, -, m2⟩ := bind_eq_ok_iff.mp m1
        obtain ⟨ce, hce, m3⟩ := bind_eq_ok_iff.mp m2
        obtain ⟨rfl, rfl⟩ := err_arm m3
        refine Out.err (invalid_throw (s := "expected a sort") hce ?_)
        simp only [StateT.run] at hrun2
        simp only [inferBodyI_lam]
        simp [e1, hrun2, absExpr_mk, absExprKind]

/-! ## The body

`CoreC.lean:1293-1389`.  The remaining seven arms make no call of their own
(`.sort`), or exactly one to a `core_k` leaf task #49 already refined
(`.fvar`, the two `.lit`s), or none at all (`.bvar`, `.letE` — the two
declines). -/

/-- `inferBodyI`'s `.bvar` arm. -/
theorem inferBodyI_bvar (lmode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (lfe : ConLeche.FEnv) (d i : Nat) :
    ConLeche.Cached.inferBodyI lmode r lfe d (.bvar i)
      = throw (.notImplemented "inferType beyond the supported fragment") := rfl

/-- `inferBodyI`'s `.letE` arm. -/
theorem inferBodyI_letE (lmode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (lfe : ConLeche.FEnv) (d : Nat) (ty v b : ConLeche.Expr) :
    ConLeche.Cached.inferBodyI lmode r lfe d (.letE ty v b)
      = throw (.internal "inferType: `let` in an annotated expression") := rfl

/-- `inferBodyI`'s `.fvar` arm. -/
theorem inferBodyI_fvar (lmode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (lfe : ConLeche.FEnv) (d idx : Nat) (ty : ConLeche.Expr) :
    ConLeche.Cached.inferBodyI lmode r lfe d (.fvar idx ty)
      = (if idx < d then pure ty
         else throw (.invalid "free variable out of scope")) := rfl

/-- `inferBodyI`'s `.sort` arm. -/
theorem inferBodyI_sort (lmode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (lfe : ConLeche.FEnv) (d : Nat) (u : ConLeche.Level) :
    ConLeche.Cached.inferBodyI lmode r lfe d (.sort u)
      = pure (ConLeche.Expr.sort (.succ u)) := rfl

/-- `inferBodyI`'s `.lit (.natVal _)` arm. -/
theorem inferBodyI_litNat (lmode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (lfe : ConLeche.FEnv) (d : Nat) (n : Nat) :
    ConLeche.Cached.inferBodyI lmode r lfe d (.lit (.natVal n))
      = (if ConLeche.natLitSupportedF lfe then pure (.const ConLeche.natName [])
         else throw (.invalid
           "Nat literal without the Nat basis declarations")) := rfl

/-- `inferBodyI`'s `.lit (.strVal _)` arm. -/
theorem inferBodyI_litStr (lmode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (lfe : ConLeche.FEnv) (d : Nat) (s : String) :
    ConLeche.Cached.inferBodyI lmode r lfe d (.lit (.strVal s))
      = (if ConLeche.strLitSupportedF lfe then pure (.const ConLeche.stringName [])
         else throw (.notImplemented
           "string literals before the String support declarations")) := rfl

/-- `inferBodyI`'s `.app` arm. -/
theorem inferBodyI_app (lmode : ConLeche.CheckMode) (r : ConLeche.Cached.CoreFnsI)
    (lfe : ConLeche.FEnv) (d : Nat) (f a : ConLeche.Expr) :
    ConLeche.Cached.inferBodyI lmode r lfe d (.app f a)
      = (do
        let tf ← r.infer d (ConLeche.Expr.getAppFn (.app f a))
        ConLeche.Cached.inferSpineI r lfe d tf #[]
          (ConLeche.Expr.getAppArgsC (.app f a))) := rfl

/-- `ConLeche/Cached/CoreC.lean:1293-1389` — **`infer_body_i` refines
`inferBodyI`** (`core_c.rs:3336`), at the knot itself: task #61 removed the
`io` flag (see the module note), so every clause here runs at the full grade
and the statement is exact at every one of the ten views. -/
theorem infer_body_i_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hw : Wrappers mode fuel) (hd : InferDeps mode fuel)
    (d : Std.U64) {e : expr.Expr} (he : ExprWF e) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_body_i mode fuel st fe d e)
      (fun lfe => ConLeche.Cached.inferBodyI (absMode mode) (knot mode lfe fuel.val) lfe
        d.val (absExpr e)) := by
  intro fe lfe hfe hfrel st oc st' hwf hok lst hrel
  have hch := CoreK.ExprWF.children he
  unfold cached.core_c.infer_body_i at hok
  obtain ⟨en, hen, k1⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨⟨dd, k⟩⟩ := e
  have henv : en = ron.node.ExprView.ofKind k := by simpa using hen.symm
  subst henv
  simp only [expr.Expr._0._simpLemma_, expr.ExprNode.kind._simpLemma_] at hch
  cases k
  case Bvar i =>
    -- outside the supported fragment: both decline (`CoreC.lean:1389`)
    obtain ⟨s1, -, m1⟩ := bind_eq_ok_iff.mp k1
    obtain ⟨v1, -, m2⟩ := bind_eq_ok_iff.mp m1
    obtain ⟨ce, hce, m3⟩ := bind_eq_ok_iff.mp m2
    obtain ⟨rfl, rfl⟩ := err_arm m3
    refine Out.err (not_implemented_throw
      (s := "inferType beyond the supported fragment") hce ?_)
    simp [inferBodyI_bvar]
  case LetE ty v b =>
    -- unreachable by construction on both sides, at `internal`
    -- (`CoreC.lean:1387`)
    obtain ⟨s1, -, m1⟩ := bind_eq_ok_iff.mp k1
    obtain ⟨v1, -, m2⟩ := bind_eq_ok_iff.mp m1
    obtain ⟨ce, hce, m3⟩ := bind_eq_ok_iff.mp m2
    obtain ⟨rfl, rfl⟩ := err_arm m3
    refine Out.err (internal_throw
      (s := "inferType: `let` in an annotated expression") hce ?_)
    simp [inferBodyI_letE]
  case Fvar idx ty =>
    obtain ⟨r0, hr0, k2⟩ := bind_eq_ok_iff.mp k1
    simp only [Result.ok.injEq, Prod.mk.injEq] at k2
    obtain ⟨rfl, rfl⟩ := k2
    cases r0 with
    | Ok r =>
      obtain ⟨hval, hrwf⟩ := CoreK.infer_fvar_refines hch hr0
      refine ⟨lst, ?_, hrel, hwf, hrwf⟩
      by_cases hlt : idx.val < d.val
      · rw [if_pos hlt] at hval
        simp only [Except.ok.injEq] at hval
        simp [inferBodyI_fvar, hlt, hval]
      · rw [if_neg hlt] at hval; simp at hval
    | Err ce =>
      -- out of scope: `core_k::infer_fvar`'s own mirrored `invalid`
      refine Out.err (ErrSim.trans (CoreK.infer_fvar_err hr0) ?_)
      intro le hle
      by_cases hlt : idx.val < d.val
      · rw [if_pos hlt] at hle; simp at hle
      · rw [if_neg hlt] at hle
        simp only [Except.error.injEq] at hle
        subst hle
        simp [inferBodyI_fvar, hlt]
  case «Sort» u =>
    -- the one clause that cannot fail on either side
    obtain ⟨l, hl, k2⟩ := bind_eq_ok_iff.mp k1
    rw [level_dup_eq] at hl
    rw [← Result.ok_injective hl] at k2
    obtain ⟨l1, hl1, k3⟩ := bind_eq_ok_iff.mp k2
    obtain ⟨e1, he1, k4⟩ := bind_eq_ok_iff.mp k3
    simp only [Result.ok.injEq, Prod.mk.injEq] at k4
    obtain ⟨rfl, rfl⟩ := k4
    refine ⟨lst, ?_, hrel, hwf, Expr.sort_wf (LevelWF.succ hch hl1) he1⟩
    simp only [absExpr_mk, absExprKind, inferBodyI_sort]
    simp [Expr.sort_refines he1, Level.succ_refines hl1]
  case Const n us =>
    obtain ⟨v, hv, k2⟩ := bind_eq_ok_iff.mp k1
    rw [arc_deref_eq] at hv
    rw [← Result.ok_injective hv] at k2
    exact (infer_const_i_refines false hch.1 hch.2 d)
      fe lfe hfe hfrel st oc st' hwf k2 lst hrel
  case Lit l =>
    cases l with
    | NatVal nn =>
      obtain ⟨r0, hr0, k2⟩ := bind_eq_ok_iff.mp k1
      simp only [Result.ok.injEq, Prod.mk.injEq] at k2
      obtain ⟨rfl, rfl⟩ := k2
      have hnls := CoreK.natLitSupportedSpec (ConRon.Refine.FindAgree.of_rel hfrel hfe)
        (ConRon.Refine.FindWF.of_wf hfe)
      cases r0 with
      | Ok r =>
        obtain ⟨hval, hrwf⟩ := CoreK.infer_lit_nat_refines hnls
          (fun _ h => BasisNames.nat_name_refines h) hr0
        refine ⟨lst, ?_, hrel, hwf, hrwf⟩
        by_cases hs : ConLeche.natLitSupportedF lfe
        · rw [if_pos hs] at hval
          simp only [Except.ok.injEq] at hval
          simp [inferBodyI_litNat, hs, ← hval]
        · rw [if_neg hs] at hval; simp at hval
      | Err ce =>
        -- the Nat basis is missing: both reject at `invalid`
        refine Out.err (ErrSim.trans (CoreK.infer_lit_nat_err hnls hr0) ?_)
        intro le hle
        by_cases hs : ConLeche.natLitSupportedF lfe
        · rw [if_pos hs] at hle; simp at hle
        · rw [if_neg hs] at hle
          simp only [Except.error.injEq] at hle
          subst hle
          simp [inferBodyI_litNat, hs]
    | StrVal ss =>
      obtain ⟨r0, hr0, k2⟩ := bind_eq_ok_iff.mp k1
      simp only [Result.ok.injEq, Prod.mk.injEq] at k2
      obtain ⟨rfl, rfl⟩ := k2
      have hsls := CoreK.strLitSupportedSpec (ConRon.Refine.FindAgree.of_rel hfrel hfe)
        (ConRon.Refine.FindWF.of_wf hfe)
      cases r0 with
      | Ok r =>
        obtain ⟨hval, hrwf⟩ := CoreK.infer_lit_str_refines hsls
          (fun _ h => BasisNames.string_name_refines h) hr0
        refine ⟨lst, ?_, hrel, hwf, hrwf⟩
        by_cases hs : ConLeche.strLitSupportedF lfe
        · rw [if_pos hs] at hval
          simp only [Except.ok.injEq] at hval
          simp [inferBodyI_litStr, hs, ← hval]
        · rw [if_neg hs] at hval; simp at hval
      | Err ce =>
        -- the String support declarations are missing: both decline
        refine Out.err (ErrSim.trans (CoreK.infer_lit_str_err hsls hr0) ?_)
        intro le hle
        by_cases hs : ConLeche.strLitSupportedF lfe
        · rw [if_pos hs] at hle; simp at hle
        · rw [if_neg hs] at hle
          simp only [Except.error.injEq] at hle
          subst hle
          simp [inferBodyI_litStr, hs]
  case Proj sn i pe =>
    exact (infer_proj_i_refines hw d false hch.1 hch.2)
      fe lfe hfe hfrel st oc st' hwf k1 lst hrel
  case ForallE ty body mb =>
    simpa using (infer_forall_i_refines hw hd d hch.1 hch.2.1 hch.2.2)
      fe lfe hfe hfrel st oc st' hwf k1 lst hrel
  case Lam ty body mb =>
    simpa using (infer_lam_i_refines hw hd d hch.1 hch.2.1 hch.2.2)
      fe lfe hfe hfrel st oc st' hwf k1 lst hrel
  case App f a =>
    obtain ⟨hd1, hargs, k2⟩ := bind_eq_ok_iff.mp k1
    obtain ⟨hdabs, hdwf⟩ := ExprOps.get_app_fn_refines he hargs
    obtain ⟨args, hargs2, k3⟩ := bind_eq_ok_iff.mp k2
    obtain ⟨haabs, hawf⟩ := ExprOps.get_app_args_refines he hargs2
    obtain ⟨⟨r0, st1⟩, h1, k4⟩ := bind_eq_ok_iff.mp k3
    have hfn : ConLeche.Expr.getAppFn
        (ConLeche.Expr.app (absExpr f) (absExpr a)) = absExpr hd1 := by
      rw [hdabs]; rfl
    have hag : ConLeche.Expr.getAppArgsC
        (ConLeche.Expr.app (absExpr f) (absExpr a)) = absExprs args := by
      rw [ConLeche.Expr.getAppArgsC_spec]; exact haabs.symm
    cases r0 with
      | Err err =>
        -- the spine head's inference threw
        obtain ⟨rfl, rfl⟩ := err_arm k4
        refine Out.err ?_
        simp only [absExpr_mk, absExprKind, inferBodyI_app]
        rw [hfn]
        exact ErrSim.bindCM ((hw.inferSim d hdwf).apply_err hwf hfe h1 hrel hfrel)
      | Ok tf =>
        obtain ⟨lst1, hrun1, hrel1, hwf1, htfWF⟩ :=
          (hw.inferSim d hdwf).apply hwf hfe h1 hrel hfrel
        have e1 : (knot mode lfe fuel.val).infer d.val
              (ConLeche.Expr.getAppFn
                (ConLeche.Expr.app (absExpr f) (absExpr a))) lst
            = Except.ok (absExpr tf, lst1) := by rw [hfn]; exact hrun1
        cases oc with
        | Ok r =>
          obtain ⟨lst2, hrun2, hrel2, hwf2, hrwf⟩ :=
            (hd.inferSpine d tf (alloc.vec.Vec.new expr.Expr) args 0#usize
              htfWF ExprOps.exprsWF_new hawf).apply hwf1 hfe k4 hrel1 hfrel
          refine ⟨lst2, ?_, hrel2, hwf2, hrwf⟩
          have e2 : ConLeche.Cached.inferSpineI (knot mode lfe fuel.val) lfe d.val
                (absExpr tf) #[]
                (ConLeche.Expr.getAppArgsC
                  (ConLeche.Expr.app (absExpr f) (absExpr a))) lst1
              = Except.ok (absExpr r, lst2) := by
            rw [hag]
            simpa using hrun2
          simp only [absExpr_mk, absExprKind, inferBodyI_app]
          simp [e1, e2]
        | Err ce =>
          -- the spine walk threw
          refine Out.err (ErrSim.trans
            ((hd.inferSpine d tf (alloc.vec.Vec.new expr.Expr) args 0#usize
              htfWF ExprOps.exprsWF_new hawf).apply_err hwf1 hfe k4 hrel1 hfrel) ?_)
          intro le hle
          have e2 : ConLeche.Cached.inferSpineI (knot mode lfe fuel.val) lfe d.val
                (absExpr tf) #[]
                (ConLeche.Expr.getAppArgsC
                  (ConLeche.Expr.app (absExpr f) (absExpr a))) lst1
              = Except.error le := by
            rw [hag]
            simpa using hle
          simp only [absExpr_mk, absExprKind, inferBodyI_app]
          simp [e1, e2]

end

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Every refinement in this file is axiom-clean since task #61 removed the `io`
flag from `infer_body_i` (the module note). -/

/--
info: 'ConRon.Refine.Core.infer_body_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms infer_body_i_refines


/--
info: 'ConRon.Refine.Core.infer_const_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms infer_const_i_refines

/--
info: 'ConRon.Refine.Core.infer_proj_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms infer_proj_i_refines

/--
info: 'ConRon.Refine.Core.infer_forall_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms infer_forall_i_refines

/--
info: 'ConRon.Refine.Core.infer_lam_i_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms infer_lam_i_refines

end ConRon.Refine.Core

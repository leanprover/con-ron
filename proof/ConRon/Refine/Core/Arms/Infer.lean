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

The `.M`-suffixed `Array Std.U32` constants of the block are error-message
code points, reached only on the `.Err` path; nothing is claimed on failure
(DESIGN.md §3.5), so they carry no theorem.
-/
import ConRon.Refine.Core.Arms.Shape
import ConRon.Refine.CoreKPinned
import ConRon.Refine.ExprOpsC

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
recursive call, so it is the same under both records. -/
theorem infer_const_i_refines (io : Bool) {n : name.Name}
    {us : alloc.vec.Vec level.Level} (hn : NameWF n) (hus : LevelsWF us) (d : Std.U64) :
    Sim absExpr ExprWF (fun st fe => cached.core_c.infer_const_i st fe n us)
      (fun lfe => ConLeche.Cached.inferBodyI (absMode mode)
        (knotV mode lfe fuel.val io) lfe d.val (.const (absName n) (absLevels us))) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  have hclause : ConLeche.Cached.inferBodyI (absMode mode)
      (knotV mode lfe fuel.val io) lfe d.val (.const (absName n) (absLevels us))
      = (do
        match lfe.find? (absName n) with
        | none => throw (.invalid s!"unknown constant {absName n}")
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
    exfalso
    simp only [bind_eq_ok_iff, lift_eq] at hok
    obtain ⟨s1, -, v, -, ce, -, hc⟩ := hok
    simp at hc
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
            = ok (core.result.Result.Ok r, st') := hok
      split at hok
      · -- a projection table used as a constant: the port throws
        exfalso
        simp only [bind_eq_ok_iff, lift_eq] at hok
        obtain ⟨s1, -, v, -, ce, -, hc⟩ := hok
        simp at hc
      rename_i hbf
      simp only [Bool.not_eq_true] at hbf
      split at hok
      · -- the wrong number of levels: the port throws
        exfalso
        simp only [bind_eq_ok_iff, lift_eq] at hok
        obtain ⟨s1, -, v, -, ce, -, hc⟩ := hok
        simp at hc
      rename_i hlen
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hlen
      have hlenv : (absLevels us).length = ci.toConstantVal.levelParams.length := by
        have h1 : (alloc.vec.Vec.len us).val = us.val.length := alloc.vec.Vec.len_val us
        simp only [absLevels, List.length_map]
        rw [← h1, hlen, hiv]
      obtain ⟨lst', hrun, hrel', hwf', hrwf⟩ :=
        StateC.const_ty_at_m_refines StateC.instLevelParamsRefines hwf hfe hn hus hok
          lst lfe hrel hfrel (absName n)
      refine ⟨lst', ?_, hrel', hwf', hrwf⟩
      simp only [hclause]
      simp only [hfind, ← hbv, hbf, hlenv]
      simpa using hrun

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
  match ConLeche.Cached.ExprC.getAppFn te with
  | .const T us =>
    match lfe.findProj? T i with
    | some entry =>
      projTypeAtCheckedIL entry sn T us (ConLeche.Cached.ExprC.getAppArgs te) pe
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
verdict is a monadic equation, not a `Sim`. -/
theorem proj_type_at_checked_i_refines {entry : env.ProjEntry} {sn t : name.Name}
    {us : alloc.vec.Vec level.Level} {targs : alloc.vec.Vec expr.Expr}
    {pe r : expr.Expr} (hent : ProjEntryWF entry) (hsn : NameWF sn) (ht : NameWF t)
    (hus : LevelsWF us) (htargs : ExprsWF targs) (hpe : ExprWF pe)
    (h : cached.core_c.proj_type_at_checked_i entry sn t us targs pe = ok (.Ok r)) :
    projTypeAtCheckedIL (absProjEntry entry) (absName sn) (absName t) (absLevels us)
        (absExprs targs) (absExpr pe) = pure (absExpr r) ∧ ExprWF r := by
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

/-- `ConLeche/Cached/CoreC.lean:1356-1381` — **`infer_proj_at_i` refines the
cited clause's tail** (`core_c.rs:3484`): the head shape of the reduced subject
type, the projection-table lookup (`Refine/CoreKProj.lean`'s
`find_proj_refines`, which also hands back the entry's well-formedness) and
`proj_type_at_checked_i`.  State-free. -/
theorem infer_proj_at_i_refines {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {sn : name.Name} {i : Std.U64} {pe te r : expr.Expr}
    (hrel : FEnvRel fe lfe) (hfwf : FEnvWF fe)
    (hsn : NameWF sn) (hpe : ExprWF pe) (hte : ExprWF te)
    (h : cached.core_c.infer_proj_at_i fe sn i pe te = ok (.Ok r)) :
    inferProjAtIL lfe (absName sn) i.val (absExpr pe) (absExpr te)
        = pure (absExpr r) ∧ ExprWF r := by
  unfold cached.core_c.infer_proj_at_i at h
  simp only [bind_eq_ok_iff, arc_deref_eq, Result.ok.injEq, exists_eq_left'] at h
  obtain ⟨f, hf, h⟩ := h
  obtain ⟨hfabs, hfnwf⟩ := ExprOps.get_app_fn_refines hte hf
  obtain ⟨⟨fd, fk⟩⟩ := f
  cases fk
  case Const t us' =>
    simp only [ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨o, ho, h⟩ := h
    obtain ⟨hnwf, huswf⟩ := CoreK.constKind_wf_inv hfnwf rfl
    obtain ⟨hoabs, howf⟩ := ConRon.Refine.find_proj_refines
      (ConRon.Refine.FindAgree.of_rel hrel hfwf)
      (ConRon.Refine.FindWF.of_wf hfwf) hnwf ho
    have hgf : ConLeche.Cached.ExprC.getAppFn (absExpr te)
        = .const (absName t) (absLevels us') := by
      rw [ConLeche.Cached.ExprC.getAppFn_spec, ← hfabs]; rfl
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
      have htabs' : ConLeche.Cached.ExprC.getAppArgs (absExpr te)
          = absExprs targs := by
        rw [ConLeche.Cached.ExprC.getAppArgs_spec, ← htabs]
      have hfp : lfe.findProj? (absName t) i.val = some (absProjEntry entry) := hoabs.symm
      simpa only [inferProjAtIL, hgf, htabs', hfp] using hres
  all_goals
    simp only [ExprOps.node_kind, bind_eq_ok_iff, lift_eq, Result.ok.injEq,
      reduceCtorEq, and_false, exists_false] at h

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
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  unfold cached.core_c.infer_proj_i at hok
  obtain ⟨⟨r0, st1⟩, h1, hok⟩ := bind_eq_ok_iff.mp hok
  cases r0 with
  | Err err => simp at hok
  | Ok tpe =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, htpeWF⟩ :=
      (hw.inferAtSim d io hpe).apply hwf hfe h1 hrel hfrel
    obtain ⟨⟨r1, st2⟩, h2, hok⟩ := bind_eq_ok_iff.mp hok
    cases r1 with
    | Err err => simp at hok
    | Ok te =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, hteWF⟩ :=
        (hw.whnfSim d htpeWF).apply hwf1 hfe h2 hrel1 hfrel
      obtain ⟨r2, h3, hok⟩ := bind_eq_ok_iff.mp hok
      simp only [Result.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨hr2, rfl⟩ := hok
      subst hr2
      obtain ⟨htail, hrwf⟩ :=
        infer_proj_at_i_refines hfrel hfe hsn hpe hteWF h3
      refine ⟨lst2, ?_, hrel2, hwf2, hrwf⟩
      have e1 : (if io = true then (knot mode lfe fuel.val).inferIO
                 else (knot mode lfe fuel.val).infer) d.val (absExpr pe) lst
          = Except.ok (absExpr tpe, lst1) := by
        rw [← knotV_infer]; exact hrun1
      have e2 : (knot mode lfe fuel.val).whnf d.val (absExpr tpe) lst1
          = Except.ok (absExpr te, lst2) := hrun2
      have e3 : inferProjAtIL lfe (absName sn) i.val (absExpr pe) (absExpr te) lst2
          = Except.ok (absExpr r, lst2) := by rw [htail]; rfl
      simp only [inferBodyI_proj]
      simp [e1, e2, e3]

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
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  unfold cached.core_c.infer_forall_i at hok
  obtain ⟨⟨r0, st1⟩, h1, k1⟩ := bind_eq_ok_iff.mp hok
  cases r0 with
  | Err err => simp at k1
  | Ok tty =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, httyWF⟩ :=
      (hw.inferSim d hty).apply hwf hfe h1 hrel hfrel
    obtain ⟨⟨r1, st2⟩, h2, k2⟩ := bind_eq_ok_iff.mp k1
    cases r1 with
    | Err err => simp at k2
    | Ok wtty =>
      obtain ⟨lst2, hrun2, hrel2, hwf2, hwttyWF⟩ :=
        (hw.whnfSim d httyWF).apply hwf1 hfe h2 hrel1 hfrel
      obtain ⟨⟨dw, kd⟩⟩ := wtty
      obtain ⟨en, hen, k3⟩ := bind_eq_ok_iff.mp k2
      have henv : en = expr.ExprNode.mk dw kd := by simpa using hen.symm
      subst henv
      simp only [expr.ExprNode.kind._simpLemma_] at k3
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
        obtain ⟨pwa, hpwa, k7b⟩ := bind_eq_ok_iff.mp k7
        rw [arc_deref_eq] at hpwa
        rw [← Result.ok_injective hpwa] at k7b
        obtain ⟨pw1, hpw1, k8⟩ := bind_eq_ok_iff.mp k7b
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
        obtain ⟨lst3, hrun3, hrel3, hwf3, hrwf⟩ :=
          (hd.inferPis d pf body 1#u64 fvs stk hbody hfvsWF hstkWF).apply
            hwf2 hfe k10 hrel2 hfrel
        refine ⟨lst3, ?_, hrel3, hwf3, hrwf⟩
        have e1 : (knot mode lfe fuel.val).infer d.val (absExpr ty) lst
            = Except.ok (absExpr tty, lst1) := hrun1
        have e2 : (knot mode lfe fuel.val).whnf d.val (absExpr tty) lst1
            = Except.ok (ConLeche.Expr.sort (absLevel u), lst2) := by
          simpa using hrun2
        have e3 : ConLeche.Cached.inferPisI (absMode mode) (knot mode lfe fuel.val)
              d.val ConLeche.Cached.peelFuel (absExpr body) 1
              #[(ConLeche.Expr.fvar d.val (absExpr ty))]
              [(absLevel u, absPropWhen mb.pw)] lst2
            = Except.ok (absExpr r, lst3) := by
          rw [← hpfv, ← hfvsabs, ← hstkabs,
            show (1 : Nat) = (1#u64 : Std.U64).val from rfl]
          exact hrun3
        simp only [inferBodyI_forallE]
        simp [e1, e2, e3, absBinderMeta]
      all_goals
        exfalso
        obtain ⟨s1, -, m1⟩ := bind_eq_ok_iff.mp k3
        obtain ⟨v1, -, m2⟩ := bind_eq_ok_iff.mp m1
        obtain ⟨ce, -, m3⟩ := bind_eq_ok_iff.mp m2
        simp at m3

/-- `ConLeche/Cached/CoreC.lean:1336-1344` — **`infer_lam_i` refines
`inferBodyI`'s `.lam` clause** (`core_c.rs:3417`): the domain's type, its weak
head normal form, the `Sort` shape (through `core_k::is_sort`, the port's
boolean form of the cited `match`), and then the λ-telescope loop at the peel
fuel with the first binder already opened. -/
theorem infer_lam_i_refines (hw : Wrappers mode fuel) (hd : InferDeps mode fuel)
    (d : Std.U64) {ty body : expr.Expr} {mb : expr.BinderMeta}
    (hty : ExprWF ty) (hbody : ExprWF body) (hmb : BinderMetaWF mb) :
    Sim absExpr ExprWF
      (fun st fe => cached.core_c.infer_lam_i mode fuel st fe d ty body mb)
      (fun lfe => ConLeche.Cached.inferBodyI (absMode mode) (knot mode lfe fuel.val)
        lfe d.val (.lam (absExpr ty) (absExpr body) (absBinderMeta mb))) := by
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  unfold cached.core_c.infer_lam_i at hok
  obtain ⟨⟨r0, st1⟩, h1, k1⟩ := bind_eq_ok_iff.mp hok
  cases r0 with
  | Err err => simp at k1
  | Ok tty =>
    obtain ⟨lst1, hrun1, hrel1, hwf1, httyWF⟩ :=
      (hw.inferSim d hty).apply hwf hfe h1 hrel hfrel
    obtain ⟨⟨r1, st2⟩, h2, k2⟩ := bind_eq_ok_iff.mp k1
    cases r1 with
    | Err err => simp at k2
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
        obtain ⟨lst3, hrun3, hrel3, hwf3, hrwf⟩ :=
          (hd.inferLams d pf body 1#u64 fvs stk hbody hfvsWF hstkWF).apply
            hwf2 hfe k9 hrel2 hfrel
        refine ⟨lst3, ?_, hrel3, hwf3, hrwf⟩
        have e1 : (knot mode lfe fuel.val).infer d.val (absExpr ty) lst
            = Except.ok (absExpr tty, lst1) := hrun1
        have e2 : (knot mode lfe fuel.val).whnf d.val (absExpr tty) lst1
            = Except.ok (ConLeche.Expr.sort (absLevel u), lst2) := by
          simpa using hrun2
        have e3 : ConLeche.Cached.inferLamsI (absMode mode) (knot mode lfe fuel.val)
              d.val ConLeche.Cached.peelFuel (absExpr body) 1
              #[(ConLeche.Expr.fvar d.val (absExpr ty))]
              [(absExpr ty, absBinderMeta mb)] lst2
            = Except.ok (absExpr r, lst3) := by
          rw [← hpfv, ← hfvsabs, ← hstkabs,
            show (1 : Nat) = (1#u64 : Std.U64).val from rfl]
          exact hrun3
        simp only [absBinderMeta] at e3
        simp only [inferBodyI_lam]
        simp [e1, e2, e3]
      all_goals
        exfalso
        rw [if_neg (show ¬ b = true by rw [hbv]; simp)] at k3
        obtain ⟨s1, -, m1⟩ := bind_eq_ok_iff.mp k3
        obtain ⟨v1, -, m2⟩ := bind_eq_ok_iff.mp m1
        obtain ⟨ce, -, m3⟩ := bind_eq_ok_iff.mp m2
        simp at m3

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
        let tf ← r.infer d (ConLeche.Cached.ExprC.getAppFn (.app f a))
        ConLeche.Cached.inferSpineI r lfe d tf #[]
          (ConLeche.Cached.ExprC.getAppArgs (.app f a))) := rfl

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
  intro fe lfe hfe hfrel st r st' hwf hok lst hrel
  have hch := CoreK.ExprWF.children he
  unfold cached.core_c.infer_body_i at hok
  obtain ⟨en, hen, k1⟩ := bind_eq_ok_iff.mp hok
  obtain ⟨⟨dd, k⟩⟩ := e
  have henv : en = expr.ExprNode.mk dd k := by simpa using hen.symm
  subst henv
  simp only [expr.Expr._0._simpLemma_, expr.ExprNode.kind._simpLemma_] at k1 hch
  cases k
  case Bvar i =>
    exfalso
    obtain ⟨s1, -, m1⟩ := bind_eq_ok_iff.mp k1
    obtain ⟨v1, -, m2⟩ := bind_eq_ok_iff.mp m1
    obtain ⟨ce, -, m3⟩ := bind_eq_ok_iff.mp m2
    simp at m3
  case LetE ty v b =>
    exfalso
    obtain ⟨s1, -, m1⟩ := bind_eq_ok_iff.mp k1
    obtain ⟨v1, -, m2⟩ := bind_eq_ok_iff.mp m1
    obtain ⟨ce, -, m3⟩ := bind_eq_ok_iff.mp m2
    simp at m3
  case Fvar idx ty =>
    obtain ⟨r0, hr0, k2⟩ := bind_eq_ok_iff.mp k1
    simp only [Result.ok.injEq, Prod.mk.injEq] at k2
    obtain ⟨hr0e, rfl⟩ := k2
    subst hr0e
    obtain ⟨hval, hrwf⟩ := CoreK.infer_fvar_refines hch hr0
    refine ⟨lst, ?_, hrel, hwf, hrwf⟩
    by_cases hlt : idx.val < d.val
    · rw [if_pos hlt] at hval
      simp only [Except.ok.injEq] at hval
      simp [inferBodyI_fvar, hlt, hval]
    · rw [if_neg hlt] at hval; simp at hval
  case «Sort» u =>
    obtain ⟨l, hl, k2⟩ := bind_eq_ok_iff.mp k1
    rw [level_dup_eq] at hl
    rw [← Result.ok_injective hl] at k2
    obtain ⟨l1, hl1, k3⟩ := bind_eq_ok_iff.mp k2
    obtain ⟨e1, he1, k4⟩ := bind_eq_ok_iff.mp k3
    simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at k4
    obtain ⟨rfl, rfl⟩ := k4
    refine ⟨lst, ?_, hrel, hwf, Expr.sort_wf (LevelWF.succ hch hl1) he1⟩
    simp only [absExpr_mk, absExprKind, inferBodyI_sort]
    simp [Expr.sort_refines he1, Level.succ_refines hl1]
  case Const n us =>
    obtain ⟨v, hv, k2⟩ := bind_eq_ok_iff.mp k1
    rw [arc_deref_eq] at hv
    rw [← Result.ok_injective hv] at k2
    exact (infer_const_i_refines false hch.1 hch.2 d).apply hwf hfe k2 hrel hfrel
  case Lit l =>
    cases l with
    | NatVal nn =>
      obtain ⟨r0, hr0, k2⟩ := bind_eq_ok_iff.mp k1
      simp only [Result.ok.injEq, Prod.mk.injEq] at k2
      obtain ⟨hr0e, rfl⟩ := k2
      subst hr0e
      obtain ⟨hval, hrwf⟩ := CoreK.infer_lit_nat_refines
        (CoreK.natLitSupportedSpec (ConRon.Refine.FindAgree.of_rel hfrel hfe)
          (ConRon.Refine.FindWF.of_wf hfe))
        (fun _ h => BasisNames.nat_name_refines h) hr0
      refine ⟨lst, ?_, hrel, hwf, hrwf⟩
      by_cases hs : ConLeche.natLitSupportedF lfe
      · rw [if_pos hs] at hval
        simp only [Except.ok.injEq] at hval
        simp [inferBodyI_litNat, hs, ← hval]
      · rw [if_neg hs] at hval; simp at hval
    | StrVal ss =>
      obtain ⟨r0, hr0, k2⟩ := bind_eq_ok_iff.mp k1
      simp only [Result.ok.injEq, Prod.mk.injEq] at k2
      obtain ⟨hr0e, rfl⟩ := k2
      subst hr0e
      obtain ⟨hval, hrwf⟩ := CoreK.infer_lit_str_refines
        (CoreK.strLitSupportedSpec (ConRon.Refine.FindAgree.of_rel hfrel hfe)
          (ConRon.Refine.FindWF.of_wf hfe))
        (fun _ h => BasisNames.string_name_refines h) hr0
      refine ⟨lst, ?_, hrel, hwf, hrwf⟩
      by_cases hs : ConLeche.strLitSupportedF lfe
      · rw [if_pos hs] at hval
        simp only [Except.ok.injEq] at hval
        simp [inferBodyI_litStr, hs, ← hval]
      · rw [if_neg hs] at hval; simp at hval
  case Proj sn i pe =>
    exact (infer_proj_i_refines hw d false hch.1 hch.2).apply hwf hfe k1 hrel hfrel
  case ForallE ty body mb =>
    simpa using
      (infer_forall_i_refines hw hd d hch.1 hch.2.1 hch.2.2).apply hwf hfe k1 hrel hfrel
  case Lam ty body mb =>
    simpa using
      (infer_lam_i_refines hw hd d hch.1 hch.2.1 hch.2.2).apply hwf hfe k1 hrel hfrel
  case App f a =>
    obtain ⟨hd1, hargs, k2⟩ := bind_eq_ok_iff.mp k1
    obtain ⟨hdabs, hdwf⟩ := ExprOps.get_app_fn_refines he hargs
    obtain ⟨args, hargs2, k3⟩ := bind_eq_ok_iff.mp k2
    obtain ⟨haabs, hawf⟩ := ExprOps.get_app_args_refines he hargs2
    obtain ⟨⟨r0, st1⟩, h1, k4⟩ := bind_eq_ok_iff.mp k3
    cases r0 with
      | Err err => simp at k4
      | Ok tf =>
        obtain ⟨lst1, hrun1, hrel1, hwf1, htfWF⟩ :=
          (hw.inferSim d hdwf).apply hwf hfe h1 hrel hfrel
        obtain ⟨lst2, hrun2, hrel2, hwf2, hrwf⟩ :=
          (hd.inferSpine d tf (alloc.vec.Vec.new expr.Expr) args 0#usize
            htfWF ExprOps.exprsWF_new hawf).apply hwf1 hfe k4 hrel1 hfrel
        refine ⟨lst2, ?_, hrel2, hwf2, hrwf⟩
        have e1 : (knot mode lfe fuel.val).infer d.val
              (ConLeche.Cached.ExprC.getAppFn
                (ConLeche.Expr.app (absExpr f) (absExpr a))) lst
            = Except.ok (absExpr tf, lst1) := by
          rw [show ConLeche.Cached.ExprC.getAppFn
              (ConLeche.Expr.app (absExpr f) (absExpr a)) = absExpr hd1 by
            rw [ConLeche.Cached.ExprC.getAppFn_spec, hdabs]; rfl]
          exact hrun1
        have e2 : ConLeche.Cached.inferSpineI (knot mode lfe fuel.val) lfe d.val
              (absExpr tf) #[]
              (ConLeche.Cached.ExprC.getAppArgs
                (ConLeche.Expr.app (absExpr f) (absExpr a))) lst1
            = Except.ok (absExpr r, lst2) := by
          rw [show ConLeche.Cached.ExprC.getAppArgs
              (ConLeche.Expr.app (absExpr f) (absExpr a)) = absExprs args by
            rw [ConLeche.Cached.ExprC.getAppArgs_spec]; exact haabs.symm]
          simpa using hrun2
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

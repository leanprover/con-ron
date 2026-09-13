import ConRon.Refine.CheckerDecl
import ConRon.Refine.CheckerSplit
import ConRon.Refine.CoreKNames
import ConRon.Refine.CoreKVec
import ConRon.Refine.TrustAxioms
import ConRon.Refine.CheckerBase
import ConRon.Refine.ExprOpsCGuards
import ConRon.Refine.StateCResolve
import ConLeche.Cached.Installed

/-! # `cached::installed` — the declaration fold (task #60)

`CORE_PLAN.md` **step 7's top**: `crates/con-ron-core/src/cached/installed.rs`
against `ConLeche/Cached/Installed.lean`, i.e. the function DESIGN.md §1 is
about — `check_decls` — and the two phases underneath it.

* **Phase A** folds `annot_decl_step` over the parsed records with the
  accumulator `(Nat × FEnv × Array PendingCheck)`: a `defn`/`opaque` record is
  annotated and installed without its inference, a `thm` record is installed
  *by statement*, and everything else takes `parsed_c::check_decl_step_c` (task
  #56's `check_decl_step_c_refines`).  A `PendingCheck` records the
  `ValueGroup`, the fold position and the installation counter
  `fe.visible_below`.
* **Phase B** checks each record against the prefix view
  `fenv::restrict_to fe pc.vis`, each **from a fresh `CState`**
  (`Refine/State.lean`'s `cstate_new_refines` is what says the port's fresh
  fourteen tables are con-leche's `{}`).

The two folds are index recursions where the Lean's are a `List.foldlM` and a
`List` recursion (`installed.rs`'s deviation 3); the bridge is the standard
`n`-bounded induction over `length - i` that `Refine/CheckerDecl.lean`'s
`check_decls_pure_val` uses, with `drop i.val` on the Lean side.

## The hypotheses this tier still owes

Every statement below that reaches the core carries them, and
`check_decls_refines` is where they are named once:

1. `hk : Core.KnotSpec mode IndAbs.checkFuelU` — **task #55**, the core's own
   refinement, being proved concurrently.  `IndAbs.check_fuel_eq` is what turns
   it into the `(hfuel, hk)` pair the task-#56 lemmas take.
2. `hind : IndRoutesSpec mode` and, since **task #67**, its failure half
   `hinde : IndRoutesSpecErr mode` beside it — **task #59**'s bridge
   `ind_routes_spec_of_p ∘ ind_routes_spec hk` had not landed when this task
   was written, so the *consumer's* forms are taken as named hypotheses here;
   when the bridge lands both are discharged from `hk` and disappear, in one
   line.  `hinde` is what makes the inductive routes' rejections mirrored
   rather than unspoken, and so what makes this file statable at the full
   outcome at all.
3. `hpins : absPins pins = ConLeche.natOpPinSets` stood here until **task
   #74** and is **gone**: the vendored con-leche takes the pin list as an
   argument of `checkDecls`/`annotDeclStep`/`annotStepC`/`checkDeclStepC` (its
   task #285), so every statement in this file is at the abstract list
   `absPins pins` and none of them assumes anything about its value.  What is
   left of the pins here is `hvar : CheckerPins.PinsWF pins`, the argument's
   own well-formedness.

## The canonical-index pair, and where it stops (task #59)

`Refine/IndSpec.lean`'s `IndRoutesSpec` carries `FEnv.FEnvCanon`/`FEnv.FEnvFull`
of the index the inductive routes are handed — both routes rebuild it with
`fenv::dup`, and the clause is false for an index that is not its own
environment's rebuild.  Phase A is a *fold*, so the pair cannot merely be
assumed at the top: each step's output index is the next step's input, and
every lemma on the chain from `annot_step_other_c_refines` up to
`annot_decl_fold_from_refines` therefore hands the pair back out as well as
taking it in.  Each install is one `fenv::push`, which is `FEnv.push_canon`.

The cascade **stops at `check_decls_refines`**, which is where the only index
this file builds comes from: `fenv::mk_fenv env::empty`, closed by
`FEnv.mk_fenv_canon` and `mk_fenv_full` below.  Nothing between a copy and its
pushes calls `fenv::restrict_to` — phase B's `restrict_to` is on a view whose
index is discarded — so `FEnvFull` survives the whole fold.

## `leanCheckDecls`: the pins parameter, applied

The upstream ask of §3.6 was `checkDecls mode ds pins`, with the shipped
`checkDecls mode ds := checkDecls mode ds natOpPinSets`.  **It landed** (con-leche
task #285) and is vendored at task #74, so `leanCheckDecls` — the abbreviation
`check_decls_refines`'s conclusion is stated against — applies the pin list
instead of ignoring it, and `hpins` is gone from every statement in this file
and in `Refine/Main.lean`.

## `sorry` count in this file: 0 (task #62)

Task #60 left nine — the *guard cascades and the core calls*:
`annotConstantValC`, `annotValC` and their two tails, `annotValueC` and its
tail, and `checkPending` with its two halves.  **Task #62 closed all nine**, so
this file is `sorry`-free: phase A's install half and the whole of phase B
census at the three standard axioms (the pins at the foot of the file), and the
`sorryAx` still reaching `check_decls_refines` enters through exactly one door,
`annot_step_other_c_refines` → `Refine/CheckerDecl.lean`'s
`check_decl_step_c_refines`.

Two things the nine needed that were not here before:

* `litGuards` below, which discharges `Refine/StateCResolve.lean`'s named
  ingredient `LitGuardsRefine` from task #49's `nat_trio_stored_refines` /
  `str_support_stored_refines` at `FindAgree.of_rel` — this is the first file
  that both holds an `FEnvRel` and calls `consts_resolve_fc`;
* three added imports (`CheckerBase` for `name_nodup_refines`,
  `ExprOpsCGuards` for the cached `all_level_params_defined_refines`,
  `StateCResolve` for `consts_resolve_fc_refines`).
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.Installed

open ConRon.Refine.CheckerDecl (absDeclC DeclCWF)

/-- Chaining two `StateT` runs: the shape every composition below has.  `simp`
has no `Except.ok a >>= f = f a` lemma at this instance, so the step is taken by
`rw` plus definitional unfolding. -/
theorem run_bind_ok {ε α β : Type}
    {x : StateT ConLeche.Cached.CState (Except ε) α}
    {f : α → StateT ConLeche.Cached.CState (Except ε) β}
    {s s₁ : ConLeche.Cached.CState} {a : α}
    {r : Except ε (β × ConLeche.Cached.CState)}
    (h : x.run s = .ok (a, s₁)) (h2 : (f a).run s₁ = r) : (x >>= f).run s = r := by
  rw [StateT.run_bind, h]; exact h2

/-- `run_bind_ok`'s failure-half twin: a step that threw makes the whole `do`
block throw at the same error.  Task #67's move 1, in the shape the `ErrSim`
transport `ErrSim.trans` wants. -/
theorem run_bind_err {ε α β : Type}
    {x : StateT ConLeche.Cached.CState (Except ε) α}
    {f : α → StateT ConLeche.Cached.CState (Except ε) β}
    {s : ConLeche.Cached.CState} {le : ε}
    (h : x.run s = .error le) : (x >>= f).run s = .error le := by
  rw [StateT.run_bind, h]; rfl

/-! ## The failure half's vocabulary (task #67)

`Refine/CheckerBase.lean`'s three pieces, repeated here because they are
`private` there: the inversion of `core_types::invalid` (the only constructor
this file's own `throw`s use), the `throw`-at-`CheckCM` reduction on its
*applied* form, and the two readers of the port's `Ok`/`Err` return.

The one piece no other file needs is `ErrSimPos`.  Phase A's fold and phase B's
walk carry the error **tagged with the declaration's fold position** — the port
returns `CheckError × U64` where con-leche returns `CheckError × Nat` — so the
whole-outcome claim there is `ErrSim`'s (the same kind, messages never
compared) *together with* the position, which both sides read off the same
record. -/

/-- `core_types::invalid` is the constructor. -/
private theorem invalid_val {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.invalid v = ok ce) :
    ce = .Invalid v := by
  rw [core_types.invalid] at h; exact (Result.ok_injective h).symm

/-- A mirrored `throw` at `invalid`: the port's error came out of
`core_types::invalid`, so its kind is con-leche's `.invalid`, and the cited
side has been rewritten down to its `throw`. -/
private theorem errSim_invalid {γ : Type} {v : alloc.vec.Vec Std.U32}
    {ce ce1 : core_types.CheckError} {x : Except ConLeche.CheckError γ} {ls : String}
    (hce : core_types.invalid v = ok ce1) (heq : ce1 = ce)
    (hx : x = .error (.invalid ls)) : ErrSim ce x := by
  rw [← heq, invalid_val hce]; exact ErrSim.invalid hx

/-- `core_types::internal` is the constructor. -/
private theorem internal_val {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.internal v = ok ce) :
    ce = .Internal v := by
  rw [core_types.internal] at h; exact (Result.ok_injective h).symm

/-- A mirrored `throw` at `internal`, the same bookkeeping — `core_k::lift_fueled`
is the one site on this tier's path that reaches it. -/
private theorem errSim_internal {γ : Type} {v : alloc.vec.Vec Std.U32}
    {ce ce1 : core_types.CheckError} {x : Except ConLeche.CheckError γ} {ls : String}
    (hce : core_types.internal v = ok ce1) (heq : ce1 = ce)
    (hx : x = .error (.internal ls)) : ErrSim ce x := by
  rw [← heq, internal_val hce]; exact ErrSim.internal hx

/-- con-leche's `throw`, at the executed monad and on its *applied* form: the
plumbing simp set unfolds `StateT.run`/`StateT.bind`/`Except.bind` but carries
no `MonadExcept` instance, so this is what a `throw` arm ends at. -/
theorem throwC_run {β : Type} (le : ConLeche.CheckError)
    (lst : ConLeche.Cached.CState) :
    (throw le : ConLeche.Cached.CheckCM β) lst = Except.error le := rfl

/-- The port's `Err` return, read off (the state-carrying shape).  Generic in
the error type, because phase A's fold answers `CheckError × U64`. -/
private theorem err_outS {α ε : Type} {ce : ε}
    {st1 st' : cached.state_c.CState} {out : core.result.Result α ε}
    (h : (ok (core.result.Result.Err ce, st1) :
      Result ((core.result.Result α ε) × cached.state_c.CState))
      = ok (out, st')) : out = .Err ce ∧ st' = st1 := by
  have h1 := Result.ok_injective h
  exact ⟨(congrArg Prod.fst h1).symm, (congrArg Prod.snd h1).symm⟩

/-- The port's `Ok` return, read off (the state-carrying shape). -/
private theorem ok_outS {α ε : Type} {r : α} {st1 st' : cached.state_c.CState}
    {out : core.result.Result α ε}
    (h : (ok (core.result.Result.Ok r, st1) :
      Result ((core.result.Result α ε) × cached.state_c.CState))
      = ok (out, st')) : out = .Ok r ∧ st' = st1 := by
  have h1 := Result.ok_injective h
  exact ⟨(congrArg Prod.fst h1).symm, (congrArg Prod.snd h1).symm⟩

/-- The port's `Err` return, read off (the state-free shape). -/
private theorem err_out {α ε : Type} {ce : ε} {out : core.result.Result α ε}
    (h : (ok (core.result.Result.Err ce) : Result (core.result.Result α ε))
      = ok out) : out = .Err ce := (Result.ok_injective h).symm

/-- The port's `Ok` return, read off (the state-free shape). -/
private theorem ok_out {α ε : Type} {r : α} {out : core.result.Result α ε}
    (h : (ok (core.result.Result.Ok r) : Result (core.result.Result α ε))
      = ok out) : out = .Ok r := (Result.ok_injective h).symm

/-- **`ErrSim` at the position-tagged error type.**  `annot_decl_step`,
`annot_decl_fold_from`, `check_pending_list{,_from}`, `check_decls_phase_b` and
`check_decls` all answer `CheckError × U64` where con-leche answers
`CheckError × Nat`: the error together with the fold position of the
declaration that failed.  The claim is `ErrSim`'s — the port's error has a
kind, so con-leche throws at that kind — with the position carried alongside,
because both sides take it from the same record. -/
def ErrSimPos {γ : Type} (e : core_types.CheckError × Std.U64)
    (x : Except (ConLeche.CheckError × Nat) γ) : Prop :=
  ∀ k, absErrKind e.1 = some k →
    ∃ le, x = .error le ∧ lErrKind le.1 = k ∧ le.2 = e.2.val

/-- A `Native` error claims nothing here either. -/
theorem ErrSimPos.native {γ : Type} {x : Except (ConLeche.CheckError × Nat) γ}
    {pos : Std.U64} (m) : ErrSimPos (.Native m, pos) x := by
  intro k hk; exact absurd hk (by simp)

/-- **The tag step**: an untagged `ErrSim` on the step's own answer becomes the
tagged claim, once the two sides are known to tag with the same position. -/
theorem ErrSimPos.tag {γ δ : Type} {e : core_types.CheckError} {pos : Std.U64}
    {x : Except ConLeche.CheckError γ} {y : Except (ConLeche.CheckError × Nat) δ}
    (h : ErrSim e x)
    (hxy : ∀ le, x = .error le → y = .error (le, pos.val)) :
    ErrSimPos (e, pos) y := by
  intro k hk
  obtain ⟨le, hle, hk'⟩ := h k hk
  exact ⟨(le, pos.val), hxy le hle, hk', rfl⟩

/-- `ErrSimPos` transported forward: whatever con-leche threw at `x` it throws
at `y`, tag and all. -/
theorem ErrSimPos.trans {γ δ : Type} {e : core_types.CheckError × Std.U64}
    {x : Except (ConLeche.CheckError × Nat) γ}
    {y : Except (ConLeche.CheckError × Nat) δ}
    (h : ErrSimPos e x) (hxy : ∀ le, x = .error le → y = .error le) :
    ErrSimPos e y := by
  intro k hk
  obtain ⟨le, hle, hk1, hk2⟩ := h k hk
  exact ⟨le, hxy le hle, hk1, hk2⟩

/-- `ErrSimPos` transported along an equation on the con-leche side. -/
theorem ErrSimPos.of_eq {γ : Type} {e : core_types.CheckError × Std.U64}
    {x y : Except (ConLeche.CheckError × Nat) γ}
    (h : ErrSimPos e x) (hxy : y = x) : ErrSimPos e y := by rw [hxy]; exact h

/-- The two `.lit` guards `Refine/StateCResolve.lean` takes as a named
ingredient, discharged from task #49's `Refine/CoreKSupport.lean` — the same
two lemmas, at `FindAgree.of_rel` instead of at a raw `FindAgree`.  It is
proved here because this is the first file that both *has* the `FEnvRel` and
*calls* `consts_resolve_fc`; nothing about it is local to `installed.rs`. -/
theorem litGuards : StateC.LitGuardsRefine where
  nat := fun _ _ _ hrel hwf h =>
    CoreK.nat_trio_stored_refines CoreK.pinnedBasisNames
      (ConRon.Refine.FindAgree.of_rel hrel hwf) h
  str := fun _ _ _ hrel hwf h =>
    CoreK.str_support_stored_refines CoreK.pinnedBasisNames
      (ConRon.Refine.FindAgree.of_rel hrel hwf) h

/-! ## The record that crosses the seam

`PendingCheck` (`ConLeche/Cached/Installed.lean:72-75`): the `ValueGroup`, the
fold position and the installation counter.  `absValueGroup` is
`Refine/CheckerSplit.lean`'s.  **To be unified into `Abs.lean`.** -/

/-- A phase-A record as `ConLeche.Cached.PendingCheck`. -/
def absPendingCheck (pc : parsed_c.PendingCheck) : ConLeche.Cached.PendingCheck :=
  ⟨CheckerSplit.absValueGroup pc.vg, pc.pos.val, pc.vis.val⟩

/-- A `Vec<PendingCheck>` as the cited `Array PendingCheck`'s contents.  The
fold carries an `Array`; `checkPendingList` walks its `toList`, so the `List`
is the primitive here and `.toArray` is written where the `Array` is wanted. -/
def absPendingChecks (v : alloc.vec.Vec parsed_c.PendingCheck) :
    List ConLeche.Cached.PendingCheck :=
  v.val.map absPendingCheck

/-- The hereditary invariant of a record: its `ValueGroup`'s. -/
def PendingCheckWF (pc : parsed_c.PendingCheck) : Prop :=
  CheckerSplit.ValueGroupWF pc.vg

/-- The hereditary invariant of the record array. -/
def PendingChecksWF (v : alloc.vec.Vec parsed_c.PendingCheck) : Prop :=
  ∀ pc ∈ v.val, PendingCheckWF pc

/-- A `Vec::push` of a record is the cited `Array.push`. -/
theorem absPendingChecks_push {v w : alloc.vec.Vec parsed_c.PendingCheck}
    {pc : parsed_c.PendingCheck} (h : alloc.vec.Vec.push v pc = ok w) :
    absPendingChecks w = absPendingChecks v ++ [absPendingCheck pc] := by
  rw [absPendingChecks, absPendingChecks, vec_push_val h, List.map_append]
  rfl

/-- A push preserves the record invariant. -/
theorem PendingChecksWF_push {v w : alloc.vec.Vec parsed_c.PendingCheck}
    {pc : parsed_c.PendingCheck} (hv : PendingChecksWF v) (hpc : PendingCheckWF pc)
    (h : alloc.vec.Vec.push v pc = ok w) : PendingChecksWF w := by
  intro q hq
  rw [vec_push_val h] at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hv q hq
  · rw [List.mem_singleton.mp hq]; exact hpc

/-! ## Phase A: the install halves

`annotConstantValC` (`:81-100`) and `annotValC` (`:106-118`) are
`installConstantVal`/`installValue` (`ConLeche/Kernel/CheckerSplit.lean`) read
through the `ExprC` guards of `cached::expr_ops_c` and `constsResolveFC`; the
port splits each at the annotation so the state-threading call is a tail call
(task #24's deviation 7).  The two `*_after_annot` halves are stated against
the cited `do` block's tail rather than against a named Lean definition, since
con-leche does not split there — exactly as
`Refine/CheckerSplit.lean`'s `check_value_group_tail_refines` is. -/

/-! ### `annotConstantValC`, reduced at each of its `throw`s

The seven guards of `annotConstantValC` (`ConLeche/Cached/Installed.lean:81-100`)
in the order the port tests them, plus the reduction that says what is left
past the annotation *is* the tail the statement below is written against — the
tail is state-free, so one equation serves both halves. -/

open ConLeche.Cached in
/-- `annotConstantValC`'s duplicate-declaration `throw` (`:82-83`). -/
private theorem annotConstantValC_dup_throw {mode : env.CheckMode}
    {lfe : ConLeche.FEnv} {cv : ConLeche.ConstantVal} {lst : CState}
    (h1 : (lfe.find? cv.name).isSome = true) :
    (annotConstantValC (absMode mode) lfe cv).run lst
      = .error (.invalid s!"duplicate declaration {cv.name}") := by
  rw [ConLeche.Cached.annotConstantValC]
  simp only [h1, if_true, StateT.run, Bind.bind, StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `annotConstantValC`'s reserved-basis-name `throw` (`:84-85`). -/
private theorem annotConstantValC_reserved_throw {mode : env.CheckMode}
    {lfe : ConLeche.FEnv} {cv : ConLeche.ConstantVal} {lst : CState}
    (h1 : (lfe.find? cv.name).isSome = false)
    (h2 : ConLeche.reservedBasisNames.contains cv.name = true) :
    (annotConstantValC (absMode mode) lfe cv).run lst
      = .error (.invalid s!"reserved basis name {cv.name}") := by
  rw [ConLeche.Cached.annotConstantValC]
  simp only [h1, h2, Bool.false_eq_true, if_false, if_true, StateT.run, Bind.bind,
    StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `annotConstantValC`'s reserved-projection-name `throw` (`:86-87`). -/
private theorem annotConstantValC_proj_throw {mode : env.CheckMode}
    {lfe : ConLeche.FEnv} {cv : ConLeche.ConstantVal} {lst : CState}
    (h1 : (lfe.find? cv.name).isSome = false)
    (h2 : ConLeche.reservedBasisNames.contains cv.name = false)
    (h3 : cv.name.isProjFnShape = true) :
    (annotConstantValC (absMode mode) lfe cv).run lst
      = .error (.invalid s!"reserved projection name {cv.name}") := by
  rw [ConLeche.Cached.annotConstantValC]
  simp only [h1, h2, h3, Bool.false_eq_true, if_false, if_true, StateT.run, Bind.bind,
    StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `annotConstantValC`'s duplicate-universe-parameter `throw` (`:88-89`). -/
private theorem annotConstantValC_nodup_throw {mode : env.CheckMode}
    {lfe : ConLeche.FEnv} {cv : ConLeche.ConstantVal} {lst : CState}
    (h1 : (lfe.find? cv.name).isSome = false)
    (h2 : ConLeche.reservedBasisNames.contains cv.name = false)
    (h3 : cv.name.isProjFnShape = false)
    (h4 : ConLeche.Name.nodup cv.levelParams = false) :
    (annotConstantValC (absMode mode) lfe cv).run lst
      = .error (.invalid s!"duplicate universe parameters in {cv.name}") := by
  rw [ConLeche.Cached.annotConstantValC]
  simp only [h1, h2, h3, h4, Bool.false_eq_true, if_false, StateT.run, Bind.bind,
    StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `annotConstantValC`'s loose-bound-variable `throw` (`:90-91`). -/
private theorem annotConstantValC_loose_throw {mode : env.CheckMode}
    {lfe : ConLeche.FEnv} {cv : ConLeche.ConstantVal} {lst : CState}
    (h1 : (lfe.find? cv.name).isSome = false)
    (h2 : ConLeche.reservedBasisNames.contains cv.name = false)
    (h3 : cv.name.isProjFnShape = false)
    (h4 : ConLeche.Name.nodup cv.levelParams = true)
    (h5 : ExprC.looseBVarsBounded 0 cv.type = false) :
    (annotConstantValC (absMode mode) lfe cv).run lst
      = .error (.invalid s!"loose bound variable in type of {cv.name}") := by
  rw [ConLeche.Cached.annotConstantValC]
  simp only [h1, h2, h3, h4, h5, Bool.false_eq_true, if_false, if_true, StateT.run,
    Bind.bind, StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `annotConstantValC`'s free-variable `throw` (`:92-93`). -/
private theorem annotConstantValC_fvar_throw {mode : env.CheckMode}
    {lfe : ConLeche.FEnv} {cv : ConLeche.ConstantVal} {lst : CState}
    (h1 : (lfe.find? cv.name).isSome = false)
    (h2 : ConLeche.reservedBasisNames.contains cv.name = false)
    (h3 : cv.name.isProjFnShape = false)
    (h4 : ConLeche.Name.nodup cv.levelParams = true)
    (h5 : ExprC.looseBVarsBounded 0 cv.type = true)
    (h6 : ExprC.hasFvar cv.type = true) :
    (annotConstantValC (absMode mode) lfe cv).run lst
      = .error (.invalid s!"unexpected free variable in type of {cv.name}") := by
  rw [ConLeche.Cached.annotConstantValC]
  simp only [h1, h2, h3, h4, h5, h6, Bool.false_eq_true, if_false, if_true, StateT.run,
    Bind.bind, StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `annotConstantValC` passes on what the type's annotation threw. -/
private theorem annotConstantValC_annot_err {mode : env.CheckMode}
    {lfe : ConLeche.FEnv} {cv : ConLeche.ConstantVal} {lst : CState}
    {le : ConLeche.CheckError}
    (h1 : (lfe.find? cv.name).isSome = false)
    (h2 : ConLeche.reservedBasisNames.contains cv.name = false)
    (h3 : cv.name.isProjFnShape = false)
    (h4 : ConLeche.Name.nodup cv.levelParams = true)
    (h5 : ExprC.looseBVarsBounded 0 cv.type = true)
    (h6 : ExprC.hasFvar cv.type = false)
    (hann : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 cv.type).run lst
      = .error le) :
    (annotConstantValC (absMode mode) lfe cv).run lst = .error le := by
  rw [ConLeche.Cached.annotConstantValC]
  simp only [h1, h2, h3, h4, h5, h6, Bool.false_eq_true, if_false, if_true,
    StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 cv.type) lst
      = Except.error le from hann]

open ConLeche.Cached in
/-- **Past the annotation, `annotConstantValC` *is* its tail**: the six
syntactic guards passed and the annotation succeeded, so what is left is the
state-free `do` block `annot_constant_val_c_after_annot_refines` is stated
against, on the post-annotation state. -/
private theorem annotConstantValC_at_annot {mode : env.CheckMode}
    {lfe : ConLeche.FEnv} {cv : ConLeche.ConstantVal} {jty : ConLeche.Expr}
    {lst lst1 : CState}
    (h1 : (lfe.find? cv.name).isSome = false)
    (h2 : ConLeche.reservedBasisNames.contains cv.name = false)
    (h3 : cv.name.isProjFnShape = false)
    (h4 : ConLeche.Name.nodup cv.levelParams = true)
    (h5 : ExprC.looseBVarsBounded 0 cv.type = true)
    (h6 : ExprC.hasFvar cv.type = false)
    (hann : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 cv.type).run lst
      = .ok (jty, lst1)) :
    (annotConstantValC (absMode mode) lfe cv).run lst
      = match (do
          unless ExprC.allLevelParamsDefined cv.levelParams jty do
            throw (ConLeche.CheckError.invalid
              s!"undeclared universe parameter in type of {cv.name}")
          unless constsResolveFC lfe jty do
            throw (ConLeche.CheckError.invalid
              s!"unknown constant in type of {cv.name}")
          pure ((⟨cv.name, cv.levelParams, jty⟩ : ConLeche.ConstantVal), jty)
          : Except ConLeche.CheckError (ConLeche.ConstantVal × ConLeche.Expr)) with
        | .ok p => .ok (p, lst1)
        | .error le => .error le := by
  rw [ConLeche.Cached.annotConstantValC]
  simp only [h1, h2, h3, h4, h5, h6, Bool.false_eq_true, if_false, if_true,
    StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 cv.type) lst
      = Except.ok (jty, lst1) from hann]
  simp only []
  cases hG : ExprC.allLevelParamsDefined cv.levelParams jty <;>
    cases hH : constsResolveFC lfe jty <;> rfl

open ConLeche.Cached in
/-- The tail's universe-parameter `throw` (`ConLeche/Cached/Installed.lean:96-97`). -/
private theorem annotConstantValCTail_lp_throw {lfe : ConLeche.FEnv}
    {cv : ConLeche.ConstantVal} {jty : ConLeche.Expr}
    (h1 : ExprC.allLevelParamsDefined cv.levelParams jty = false) :
    (do
      unless ExprC.allLevelParamsDefined cv.levelParams jty do
        throw (ConLeche.CheckError.invalid
          s!"undeclared universe parameter in type of {cv.name}")
      unless constsResolveFC lfe jty do
        throw (ConLeche.CheckError.invalid s!"unknown constant in type of {cv.name}")
      pure ((⟨cv.name, cv.levelParams, jty⟩ : ConLeche.ConstantVal), jty)
      : Except ConLeche.CheckError (ConLeche.ConstantVal × ConLeche.Expr))
      = .error (.invalid s!"undeclared universe parameter in type of {cv.name}") := by
  simp only [h1, Bool.false_eq_true, if_false]
  rfl

open ConLeche.Cached in
/-- The tail's resolution `throw` (`ConLeche/Cached/Installed.lean:98-99`). -/
private theorem annotConstantValCTail_resolve_throw {lfe : ConLeche.FEnv}
    {cv : ConLeche.ConstantVal} {jty : ConLeche.Expr}
    (h1 : ExprC.allLevelParamsDefined cv.levelParams jty = true)
    (h2 : constsResolveFC lfe jty = false) :
    (do
      unless ExprC.allLevelParamsDefined cv.levelParams jty do
        throw (ConLeche.CheckError.invalid
          s!"undeclared universe parameter in type of {cv.name}")
      unless constsResolveFC lfe jty do
        throw (ConLeche.CheckError.invalid s!"unknown constant in type of {cv.name}")
      pure ((⟨cv.name, cv.levelParams, jty⟩ : ConLeche.ConstantVal), jty)
      : Except ConLeche.CheckError (ConLeche.ConstantVal × ConLeche.Expr))
      = .error (.invalid s!"unknown constant in type of {cv.name}") := by
  simp only [h1, h2, Bool.false_eq_true, if_false, if_true]
  rfl

/-- **`installed::annot_constant_val_c_after_annot` refines `annotConstantValC`'s
tail** (`Installed.lean:81-100`, past the annotation): the two post-annotation
guards and the header the cited `pure` builds — both components of the pair are
the annotated type.

Proved (task #62) from `Refine/ExprOpsCGuards.lean`'s
`all_level_params_defined_refines` and `Refine/StateCResolve.lean`'s
`consts_resolve_fc_refines` (at `litGuards` above), then the two-level `if` and
the three `dup` identities. -/
theorem annot_constant_val_c_after_annot_refines {fe : fenv.FEnv}
    {cv : env.ConstantVal} {jty : expr.Expr}
    {out : core.result.Result (env.ConstantVal × expr.Expr) core_types.CheckError}
    (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hjty : ExprWF jty)
    (h : cached.installed.annot_constant_val_c_after_annot fe cv jty = ok out) :
    ∀ lfe, FEnvRel fe lfe →
      match out with
      | .Ok (cv_a, jty') =>
        (do
          unless ConLeche.Cached.ExprC.allLevelParamsDefined (absConstantVal cv).levelParams
              (absExpr jty) do
            throw (ConLeche.CheckError.invalid
              s!"undeclared universe parameter in type of {(absConstantVal cv).name}")
          unless ConLeche.Cached.constsResolveFC lfe (absExpr jty) do
            throw (ConLeche.CheckError.invalid
              s!"unknown constant in type of {(absConstantVal cv).name}")
          pure ((⟨(absConstantVal cv).name, (absConstantVal cv).levelParams,
                  absExpr jty⟩ : ConLeche.ConstantVal), absExpr jty)
          : Except ConLeche.CheckError (ConLeche.ConstantVal × ConLeche.Expr))
            = .ok (absConstantVal cv_a, absExpr jty')
        ∧ ConstantValWF cv_a ∧ ExprWF jty'
      | .Err e =>
        ErrSim e
          (do
            unless ConLeche.Cached.ExprC.allLevelParamsDefined (absConstantVal cv).levelParams
                (absExpr jty) do
              throw (ConLeche.CheckError.invalid
                s!"undeclared universe parameter in type of {(absConstantVal cv).name}")
            unless ConLeche.Cached.constsResolveFC lfe (absExpr jty) do
              throw (ConLeche.CheckError.invalid
                s!"unknown constant in type of {(absConstantVal cv).name}")
            pure ((⟨(absConstantVal cv).name, (absConstantVal cv).levelParams,
                    absExpr jty⟩ : ConLeche.ConstantVal), absExpr jty)
            : Except ConLeche.CheckError (ConLeche.ConstantVal × ConLeche.Expr)) := by
  intro lfe hfr
  rw [cached.installed.annot_constant_val_c_after_annot] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = ConLeche.Cached.ExprC.allLevelParamsDefined
      (absNames cv.level_params) (absExpr jty) :=
    ExprOpsC.all_level_params_defined_refines hcv.2.1 hjty hb
  cases b with
  | false =>
    -- the cited tail's universe-parameter `throw` (`Installed.lean:96-97`)
    simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
    obtain ⟨sl, hsl, v, hv, ce, hce, h⟩ := h
    have hout := err_out h
    subst hout
    show ErrSim ce _
    exact errSim_invalid hce rfl (annotConstantValCTail_lp_throw (lfe := lfe) hbv.symm)
  | true =>
    simp only [reduceIte] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v : b1 = ConLeche.Cached.constsResolveFC lfe (absExpr jty) :=
      StateC.consts_resolve_fc_refines litGuards hfr hfw hjty hb1
    cases b1 with
    | false =>
      -- the cited tail's resolution `throw` (`Installed.lean:98-99`)
      simp only [Bool.false_eq_true, reduceIte, bind_eq_ok_iff] at h
      obtain ⟨sl, hsl, v, hv, ce, hce, h⟩ := h
      have hout := err_out h
      subst hout
      show ErrSim ce _
      exact errSim_invalid hce rfl
        (annotConstantValCTail_resolve_throw (lfe := lfe) hbv.symm hb1v.symm)
    | true =>
      simp only [reduceIte] at h
      obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      have hout := ok_out h
      subst hout
      show _ ∧ _ ∧ _
      have hnn : n = cv.name := by
        rw [name_dup_eq] at hn; exact (Result.ok_injective hn).symm
      have hvv : absNames v = absNames cv.level_params := by
        rw [absNames, absNames, PropWhen.names_copy_val hv]
      have hee : e = jty := Expr.dup_eq he
      subst hnn; subst hee
      refine ⟨?_, ⟨hcv.1, ?_, hjty⟩, hjty⟩
      · simp only [absConstantVal, hvv, ← hbv, ← hb1v]
        rfl
      · intro x hx; exact hcv.2.1 x (by rwa [PropWhen.names_copy_val hv] at hx)

/-- `annot_constant_val_c_after_annot_refines` at a success, the pre-#67
statement. -/
theorem annot_constant_val_c_after_annot_refines_ok {fe : fenv.FEnv}
    {cv cv_a : env.ConstantVal} {jty jty' : expr.Expr}
    (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hjty : ExprWF jty)
    (h : cached.installed.annot_constant_val_c_after_annot fe cv jty
          = ok (.Ok (cv_a, jty'))) :
    ∀ lfe, FEnvRel fe lfe →
      (do
        unless ConLeche.Cached.ExprC.allLevelParamsDefined (absConstantVal cv).levelParams
            (absExpr jty) do
          throw (ConLeche.CheckError.invalid
            s!"undeclared universe parameter in type of {(absConstantVal cv).name}")
        unless ConLeche.Cached.constsResolveFC lfe (absExpr jty) do
          throw (ConLeche.CheckError.invalid
            s!"unknown constant in type of {(absConstantVal cv).name}")
        pure ((⟨(absConstantVal cv).name, (absConstantVal cv).levelParams,
                absExpr jty⟩ : ConLeche.ConstantVal), absExpr jty)
        : Except ConLeche.CheckError (ConLeche.ConstantVal × ConLeche.Expr))
          = .ok (absConstantVal cv_a, absExpr jty')
      ∧ ConstantValWF cv_a ∧ ExprWF jty' :=
  annot_constant_val_c_after_annot_refines hfw hcv hjty h

/-- **`installed::annot_constant_val_c` refines `annotConstantValC`**
(`Installed.lean:81-100`): `checkConstantValC` minus its inference — the six
syntactic guards, the annotation of the type, and the two guards on the result.

Proved (task #62): the six guards from `Refine/FEnv.lean`'s `find_refines`,
`Refine/BasisNames.lean`'s `reserved_basis_names_refines`, `Refine/Name.lean`'s
`contains_refines`, `Refine/CoreKShapes.lean`'s
`name_is_proj_fn_shape_refines`, `Refine/CheckerBase.lean`'s
`name_nodup_refines` and `Refine/ExprOpsC.lean`'s
`loose_bvars_bounded_refines`/`has_fvar_refines`; the annotation from
`Refine/TypeChecker.lean`'s `annotate_core_refines`; the tail from the lemma
above, whose two guards are read back out of its `Except` equation. -/
theorem annot_constant_val_c_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {cv : env.ConstantVal}
    {out : core.result.Result (env.ConstantVal × expr.Expr) core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv)
    (h : cached.installed.annot_constant_val_c mode st fe cv = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok (cv_a, jty) =>
        ∃ lst',
          (ConLeche.Cached.annotConstantValC (absMode mode) lfe
              (absConstantVal cv)).run lst
            = .ok ((absConstantVal cv_a, absExpr jty), lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv_a ∧ ExprWF jty
      | .Err e =>
        ErrSim e ((ConLeche.Cached.annotConstantValC (absMode mode) lfe
            (absConstantVal cv)).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.installed.annot_constant_val_c] at h
  obtain ⟨o, hfind, h⟩ := bind_eq_ok_iff.mp h
  have hfindv : o.map absConstantInfo = lfe.find? (absName cv.name) :=
    FEnv.find_refines hfr hfw hcv.1 hfind
  cases o with
  | some ci =>
    -- the cited duplicate-declaration `throw` (`Installed.lean:82-83`)
    simp only [core.option.Option.is_some] at h
    have h1 : (lfe.find? (absName cv.name)).isSome = true := by rw [← hfindv]; rfl
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim ce _
    exact errSim_invalid hce rfl
      (annotConstantValC_dup_throw (cv := absConstantVal cv) (lst := lst)
        (by simp only [absConstantVal]; exact h1))
  | none =>
    simp only [core.option.Option.is_some] at h
    have h1 : (lfe.find? (absName cv.name)).isSome = false := by rw [← hfindv]; rfl
    obtain ⟨rbn, hrbn, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hrbne, hrbnw⟩ := BasisNames.reserved_basis_names_refines hrbn
    have hb1abs := Name.contains_refines hrbnw hcv.1 hb1
    rw [hrbne] at hb1abs
    split at h
    · -- the cited reserved-basis-name `throw` (`Installed.lean:84-85`)
      rename_i hb1t
      have h2 : ConLeche.reservedBasisNames.contains (absName cv.name) = true := by
        rw [← hb1abs]; exact hb1t
      obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hout, -⟩ := err_outS h
      subst hout
      show ErrSim ce _
      exact errSim_invalid hce rfl
        (annotConstantValC_reserved_throw (cv := absConstantVal cv) (lst := lst)
          (by simp only [absConstantVal]; exact h1)
          (by simp only [absConstantVal]; exact h2))
    · rename_i hb1f
      have h2 : ConLeche.reservedBasisNames.contains (absName cv.name) = false := by
        rw [← hb1abs]; simpa using hb1f
      obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
      have hb2abs := CoreK.name_is_proj_fn_shape_refines hcv.1 hb2
      split at h
      · -- the cited reserved-projection-name `throw` (`Installed.lean:86-87`)
        rename_i hb2t
        have h3 : (absName cv.name).isProjFnShape = true := by
          rw [← hb2abs]; exact hb2t
        obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hout, -⟩ := err_outS h
        subst hout
        show ErrSim ce _
        exact errSim_invalid hce rfl
          (annotConstantValC_proj_throw (cv := absConstantVal cv) (lst := lst)
            (by simp only [absConstantVal]; exact h1)
            (by simp only [absConstantVal]; exact h2)
            (by simp only [absConstantVal]; exact h3))
      · rename_i hb2f
        have h3 : (absName cv.name).isProjFnShape = false := by
          rw [← hb2abs]; simpa using hb2f
        obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
        have hb3abs := CheckerBase.name_nodup_refines hcv.2.1 hb3
        split at h
        · rename_i hb3t
          obtain ⟨b4, hb4, h⟩ := bind_eq_ok_iff.mp h
          have hb4abs := ExprOpsC.loose_bvars_bounded_refines hcv.2.2 hb4
          rw [show ((0#u64 : Std.U64)).val = 0 from rfl] at hb4abs
          split at h
          · rename_i hb4t
            obtain ⟨b5, hb5, h⟩ := bind_eq_ok_iff.mp h
            have hb5abs := ExprOpsC.has_fvar_refines hcv.2.2 hb5
            split at h
            · -- the cited free-variable `throw` (`Installed.lean:92-93`)
              rename_i hb5t
              obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨hout, -⟩ := err_outS h
              subst hout
              show ErrSim ce _
              exact errSim_invalid hce rfl
                (annotConstantValC_fvar_throw (cv := absConstantVal cv) (lst := lst)
                  (by simp only [absConstantVal]; exact h1)
                  (by simp only [absConstantVal]; exact h2)
                  (by simp only [absConstantVal]; exact h3)
                  (by simp only [absConstantVal]; rw [← hb3abs]; exact hb3t)
                  (by simp only [absConstantVal]; rw [← hb4abs]; exact hb4t)
                  (by simp only [absConstantVal]; rw [← hb5abs]; exact hb5t))
            · rename_i hb5f
              obtain ⟨q, hann, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨r, st1⟩ := q
              cases r with
              | Err e =>
                -- the annotation threw, and the cited call throws the same
                obtain ⟨hout, -⟩ := err_outS h
                subst hout
                show ErrSim e _
                have herr := (TypeChecker.annotate_core_refines hfuel hk).err st fe 0#u64
                  cv.ty e st1 hsw hfw hcv.2.2 hann lst lfe hsr hfr
                exact ErrSim.trans herr (fun _ hle =>
                  annotConstantValC_annot_err (cv := absConstantVal cv)
                    (by simp only [absConstantVal]; exact h1)
                    (by simp only [absConstantVal]; exact h2)
                    (by simp only [absConstantVal]; exact h3)
                    (by simp only [absConstantVal]; rw [← hb3abs]; exact hb3t)
                    (by simp only [absConstantVal]; rw [← hb4abs]; exact hb4t)
                    (by simp only [absConstantVal]; rw [← hb5abs]; simpa using hb5f) hle)
              | Ok jty0 =>
                obtain ⟨lst1, hrunA, hsr1, hsw1, hjtyw⟩ :=
                  (TypeChecker.annotate_core_refines hfuel hk).ok st fe 0#u64 cv.ty jty0 st1
                    hsw hfw hcv.2.2 hann lst lfe hsr hfr
                have hrunA' : ((ConLeche.Cached.coreKnotI (absMode mode) lfe
                    ConLeche.checkFuel).annotate 0 (absExpr cv.ty)).run lst
                    = .ok (absExpr jty0, lst1) := hrunA
                have hat : (ConLeche.Cached.annotConstantValC (absMode mode) lfe
                      (absConstantVal cv)).run lst
                    = match (do
                        unless ConLeche.Cached.ExprC.allLevelParamsDefined
                            (absConstantVal cv).levelParams (absExpr jty0) do
                          throw (ConLeche.CheckError.invalid
                            s!"undeclared universe parameter in type of {(absConstantVal cv).name}")
                        unless ConLeche.Cached.constsResolveFC lfe (absExpr jty0) do
                          throw (ConLeche.CheckError.invalid
                            s!"unknown constant in type of {(absConstantVal cv).name}")
                        pure ((⟨(absConstantVal cv).name, (absConstantVal cv).levelParams,
                                absExpr jty0⟩ : ConLeche.ConstantVal), absExpr jty0)
                        : Except ConLeche.CheckError
                            (ConLeche.ConstantVal × ConLeche.Expr)) with
                      | .ok p => .ok (p, lst1)
                      | .error le => .error le :=
                  annotConstantValC_at_annot (cv := absConstantVal cv) h1 h2 h3
                    (by simp only [absConstantVal]; rw [← hb3abs]; exact hb3t)
                    (by simp only [absConstantVal]; rw [← hb4abs]; exact hb4t)
                    (by simp only [absConstantVal]; rw [← hb5abs]; simpa using hb5f) hrunA'
                obtain ⟨r1, htl, h⟩ := bind_eq_ok_iff.mp h
                have hrest :=
                  annot_constant_val_c_after_annot_refines hfw hcv hjtyw htl lfe hfr
                cases r1 with
                | Ok p =>
                  obtain ⟨cv_a, jty⟩ := p
                  obtain ⟨hout, rfl⟩ := ok_outS h
                  subst hout
                  obtain ⟨htaileq, hcvw, hjtyw'⟩ := hrest
                  exact ⟨lst1, by rw [hat, htaileq], hsr1, hsw1, hcvw, hjtyw'⟩
                | Err ce =>
                  obtain ⟨hout, rfl⟩ := err_outS h
                  subst hout
                  show ErrSim ce _
                  exact ErrSim.trans hrest (fun le hle => by rw [hat, hle])
          · -- the cited loose-bound-variable `throw` (`Installed.lean:90-91`)
            rename_i hb4f
            obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hout, -⟩ := err_outS h
            subst hout
            show ErrSim ce _
            exact errSim_invalid hce rfl
              (annotConstantValC_loose_throw (cv := absConstantVal cv) (lst := lst)
                (by simp only [absConstantVal]; exact h1)
                (by simp only [absConstantVal]; exact h2)
                (by simp only [absConstantVal]; exact h3)
                (by simp only [absConstantVal]; rw [← hb3abs]; exact hb3t)
                (by simp only [absConstantVal]; rw [← hb4abs]; simpa using hb4f))
        · -- the cited duplicate-universe-parameter `throw` (`Installed.lean:88-89`)
          rename_i hb3f
          obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hout, -⟩ := err_outS h
          subst hout
          show ErrSim ce _
          exact errSim_invalid hce rfl
            (annotConstantValC_nodup_throw (cv := absConstantVal cv) (lst := lst)
              (by simp only [absConstantVal]; exact h1)
              (by simp only [absConstantVal]; exact h2)
              (by simp only [absConstantVal]; exact h3)
              (by simp only [absConstantVal]; rw [← hb3abs]; simpa using hb3f))

/-- `annot_constant_val_c_refines` at a success, the pre-#67 statement. -/
theorem annot_constant_val_c_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv cv_a : env.ConstantVal} {jty : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv)
    (h : cached.installed.annot_constant_val_c mode st fe cv
          = ok (.Ok (cv_a, jty), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (ConLeche.Cached.annotConstantValC (absMode mode) lfe
            (absConstantVal cv)).run lst
          = .ok ((absConstantVal cv_a, absExpr jty), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv_a ∧ ExprWF jty :=
  annot_constant_val_c_refines hfuel hk hsw hfw hcv h

/-- **`installed::annot_val_c_record` is the cited `if record then some (jv, jv)
else none`** (`Installed.lean:106-118`), as a function: the branch would
otherwise sit inside an argument of `recordCConst` with the state borrowed. -/
theorem annot_val_c_record_refines {jv : expr.Expr} {record : Bool}
    {o : Option (expr.Expr × expr.Expr)}
    (h : cached.installed.annot_val_c_record jv record = ok o) :
    o.map (fun p => (absExpr p.1, absExpr p.2))
      = (if record then some (absExpr jv, absExpr jv) else none) := by
  rw [cached.installed.annot_val_c_record] at h
  cases record with
  | false =>
    simp only [Bool.false_eq_true, reduceIte] at h ⊢
    rw [← Result.ok_injective h]
    rfl
  | true =>
    simp only [reduceIte, bind_eq_ok_iff] at h ⊢
    obtain ⟨a, ha, h⟩ := h
    rw [← Result.ok_injective h]
    simp only [Option.map_some]
    rw [Expr.dup_eq ha]

/-! ### `annotValC`, reduced at each of its `throw`s

The same four pieces for the value half (`ConLeche/Cached/Installed.lean:106-118`):
its two scope guards, what it does with what the annotation threw, and the
reduction that says what is left past the annotation *is* the tail
`annot_val_c_after_annot_refines` is stated against — which here is stateful,
because of the `ienv` record. -/

open ConLeche.Cached in
/-- The tail's universe-parameter `throw` (`ConLeche/Cached/Installed.lean:114-115`). -/
private theorem annotValCTail_lp_throw {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty jv : ConLeche.Expr} {record : Bool} {lst : CState}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = false) :
    (do
      unless ExprC.allLevelParamsDefined cvA.levelParams jv do
        throw (ConLeche.CheckError.invalid
          s!"undeclared universe parameter in value of {cvA.name}")
      unless constsResolveFC lfe jv do
        throw (ConLeche.CheckError.invalid s!"unknown constant in value of {cvA.name}")
      recordCConst cvA.name cvA.type jty (if record then some (jv, jv) else none)
      pure jv).run lst
      = .error (.invalid s!"undeclared universe parameter in value of {cvA.name}") := by
  simp only [h1, Bool.false_eq_true, if_false, StateT.run, Bind.bind, StateT.bind,
    Except.bind]
  rfl

open ConLeche.Cached in
/-- The tail's resolution `throw` (`ConLeche/Cached/Installed.lean:116-117`). -/
private theorem annotValCTail_resolve_throw {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty jv : ConLeche.Expr} {record : Bool} {lst : CState}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = true)
    (h2 : constsResolveFC lfe jv = false) :
    (do
      unless ExprC.allLevelParamsDefined cvA.levelParams jv do
        throw (ConLeche.CheckError.invalid
          s!"undeclared universe parameter in value of {cvA.name}")
      unless constsResolveFC lfe jv do
        throw (ConLeche.CheckError.invalid s!"unknown constant in value of {cvA.name}")
      recordCConst cvA.name cvA.type jty (if record then some (jv, jv) else none)
      pure jv).run lst
      = .error (.invalid s!"unknown constant in value of {cvA.name}") := by
  simp only [h1, h2, if_true, StateT.run, Bind.bind, StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `annotValC`'s loose-bound-variable `throw` (`ConLeche/Cached/Installed.lean:107-108`). -/
private theorem annotValC_loose_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value : ConLeche.Expr} {record : Bool} {lst : CState}
    (h1 : ExprC.looseBVarsBounded 0 value = false) :
    (annotValC (absMode mode) lfe cvA jty value record).run lst
      = .error (.invalid s!"loose bound variable in value of {cvA.name}") := by
  rw [ConLeche.Cached.annotValC]
  simp only [h1, Bool.false_eq_true, if_false, StateT.run, Bind.bind, StateT.bind,
    Except.bind]
  rfl

open ConLeche.Cached in
/-- `annotValC`'s free-variable `throw` (`ConLeche/Cached/Installed.lean:109-110`). -/
private theorem annotValC_fvar_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value : ConLeche.Expr} {record : Bool} {lst : CState}
    (h1 : ExprC.looseBVarsBounded 0 value = true)
    (h2 : ExprC.hasFvar value = true) :
    (annotValC (absMode mode) lfe cvA jty value record).run lst
      = .error (.invalid s!"unexpected free variable in value of {cvA.name}") := by
  rw [ConLeche.Cached.annotValC]
  simp only [h1, h2, if_true, StateT.run, Bind.bind, StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `annotValC` passes on what the value's annotation threw. -/
private theorem annotValC_annot_err {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value : ConLeche.Expr} {record : Bool} {lst : CState}
    {le : ConLeche.CheckError}
    (h1 : ExprC.looseBVarsBounded 0 value = true)
    (h2 : ExprC.hasFvar value = false)
    (hann : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 value).run lst
      = .error le) :
    (annotValC (absMode mode) lfe cvA jty value record).run lst = .error le := by
  rw [ConLeche.Cached.annotValC]
  simp only [h1, h2, Bool.false_eq_true, if_false, if_true, StateT.run, Bind.bind,
    StateT.bind, Except.bind, Pure.pure]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 value) lst
      = Except.error le from hann]

open ConLeche.Cached in
/-- **Past the annotation, `annotValC` *is* its tail**: the two scope guards
passed and the annotation succeeded, so what is left is the `do` block
`annot_val_c_after_annot_refines` is stated against, on the post-annotation
state. -/
private theorem annotValC_at_annot {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value jv : ConLeche.Expr} {record : Bool}
    {lst lst1 : CState}
    (h1 : ExprC.looseBVarsBounded 0 value = true)
    (h2 : ExprC.hasFvar value = false)
    (hann : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 value).run lst
      = .ok (jv, lst1)) :
    (annotValC (absMode mode) lfe cvA jty value record).run lst
      = (do
          unless ExprC.allLevelParamsDefined cvA.levelParams jv do
            throw (ConLeche.CheckError.invalid
              s!"undeclared universe parameter in value of {cvA.name}")
          unless constsResolveFC lfe jv do
            throw (ConLeche.CheckError.invalid s!"unknown constant in value of {cvA.name}")
          recordCConst cvA.name cvA.type jty (if record then some (jv, jv) else none)
          pure jv).run lst1 := by
  rw [ConLeche.Cached.annotValC]
  simp only [h1, h2, Bool.false_eq_true, if_false, if_true, StateT.run, Bind.bind,
    StateT.bind, Except.bind, Pure.pure]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 value) lst
      = Except.ok (jv, lst1) from hann]
  rfl

/-- **`installed::annot_val_c_after_annot` refines `annotValC`'s tail**
(`Installed.lean:106-118`, past the annotation): the two guards on the
annotated value and the `ienv` record, tagged with the very `Expr` objects the
install pushes.  The record runs on the accepting path only.

Proved (task #62): the two guards as in
`annot_constant_val_c_after_annot_refines`, then `Refine/StateC.lean`'s
`record_c_const_refines` over `annot_val_c_record_refines` above. -/
theorem annot_val_c_after_annot_refines {st st' : cached.state_c.CState}
    {fe : fenv.FEnv} {cv_a : env.ConstantVal} {jty jv : expr.Expr}
    {record : Bool}
    {out : core.result.Result expr.Expr core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hjv : ExprWF jv)
    (h : cached.installed.annot_val_c_after_annot st fe cv_a jty jv record
          = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok jv' =>
        ∃ lst',
          (do
            unless ConLeche.Cached.ExprC.allLevelParamsDefined
                (absConstantVal cv_a).levelParams (absExpr jv) do
              throw (ConLeche.CheckError.invalid
                s!"undeclared universe parameter in value of {(absConstantVal cv_a).name}")
            unless ConLeche.Cached.constsResolveFC lfe (absExpr jv) do
              throw (ConLeche.CheckError.invalid
                s!"unknown constant in value of {(absConstantVal cv_a).name}")
            ConLeche.Cached.recordCConst (absConstantVal cv_a).name
              (absConstantVal cv_a).type (absExpr jty)
              (if record then some (absExpr jv, absExpr jv) else none)
            pure (absExpr jv)).run lst
            = .ok (absExpr jv', lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF jv'
      | .Err e =>
        ErrSim e
          ((do
            unless ConLeche.Cached.ExprC.allLevelParamsDefined
                (absConstantVal cv_a).levelParams (absExpr jv) do
              throw (ConLeche.CheckError.invalid
                s!"undeclared universe parameter in value of {(absConstantVal cv_a).name}")
            unless ConLeche.Cached.constsResolveFC lfe (absExpr jv) do
              throw (ConLeche.CheckError.invalid
                s!"unknown constant in value of {(absConstantVal cv_a).name}")
            ConLeche.Cached.recordCConst (absConstantVal cv_a).name
              (absConstantVal cv_a).type (absExpr jty)
              (if record then some (absExpr jv, absExpr jv) else none)
            pure (absExpr jv)).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.installed.annot_val_c_after_annot] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = ConLeche.Cached.ExprC.allLevelParamsDefined
      (absNames cv_a.level_params) (absExpr jv) :=
    ExprOpsC.all_level_params_defined_refines hcv.2.1 hjv hb
  cases b with
  | false =>
    -- the cited tail's universe-parameter `throw` (`Installed.lean:114-115`)
    simp only [Bool.false_eq_true, reduceIte] at h
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim ce _
    exact errSim_invalid hce rfl
      (annotValCTail_lp_throw (lfe := lfe) (jty := absExpr jty) (record := record)
        (lst := lst) hbv.symm)
  | true =>
    simp only [reduceIte] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v : b1 = ConLeche.Cached.constsResolveFC lfe (absExpr jv) :=
      StateC.consts_resolve_fc_refines litGuards hfr hfw hjv hb1
    cases b1 with
    | false =>
      -- the cited tail's resolution `throw` (`Installed.lean:116-117`)
      simp only [Bool.false_eq_true, reduceIte] at h
      obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hout, -⟩ := err_outS h
      subst hout
      show ErrSim ce _
      exact errSim_invalid hce rfl
        (annotValCTail_resolve_throw (jty := absExpr jty) (record := record)
          (lst := lst) hbv.symm hb1v.symm)
    | true =>
      simp only [reduceIte] at h
      obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨st1, hrec, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hout, rfl⟩ := ok_outS h
      subst hout
      show ∃ lst', _ ∧ _ ∧ _ ∧ _
      have hnn : n = cv_a.name := by
        rw [name_dup_eq] at hn; exact (Result.ok_injective hn).symm
      have hee : e = cv_a.ty := Expr.dup_eq he
      have hee1 : e1 = jty := Expr.dup_eq he1
      subst hnn; subst hee; subst hee1
      have howf : ∀ p, o = some p → ExprWF p.1 ∧ ExprWF p.2 := by
        rw [cached.installed.annot_val_c_record] at ho
        cases record with
        | false =>
          simp only [Bool.false_eq_true, reduceIte, Result.ok.injEq] at ho
          intro p hp; rw [← ho] at hp; simp at hp
        | true =>
          simp only [reduceIte, bind_eq_ok_iff] at ho
          obtain ⟨a, ha, ho⟩ := ho
          rw [Expr.dup_eq ha] at ho
          intro p hp; rw [← Result.ok_injective ho, Option.some.injEq] at hp
          rw [← hp]; exact ⟨hjv, hjv⟩
      obtain ⟨lst', hrunr, hsr', hsw'⟩ :=
        StateC.record_c_const_refines hsw hcv.1 hcv.2.2 hjty howf hrec lst hsr
      rw [annot_val_c_record_refines ho] at hrunr
      refine ⟨lst', ?_, hsr', hsw', hjv⟩
      simp only [absConstantVal, ← hbv, ← hb1v, if_true, pure_bind]
      exact run_bind_ok hrunr rfl

/-- `annot_val_c_after_annot_refines` at a success, the pre-#67 statement. -/
theorem annot_val_c_after_annot_refines_ok {st st' : cached.state_c.CState}
    {fe : fenv.FEnv} {cv_a : env.ConstantVal} {jty jv jv' : expr.Expr}
    {record : Bool}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hjv : ExprWF jv)
    (h : cached.installed.annot_val_c_after_annot st fe cv_a jty jv record
          = ok (.Ok jv', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (do
          unless ConLeche.Cached.ExprC.allLevelParamsDefined
              (absConstantVal cv_a).levelParams (absExpr jv) do
            throw (ConLeche.CheckError.invalid
              s!"undeclared universe parameter in value of {(absConstantVal cv_a).name}")
          unless ConLeche.Cached.constsResolveFC lfe (absExpr jv) do
            throw (ConLeche.CheckError.invalid
              s!"unknown constant in value of {(absConstantVal cv_a).name}")
          ConLeche.Cached.recordCConst (absConstantVal cv_a).name
            (absConstantVal cv_a).type (absExpr jty)
            (if record then some (absExpr jv, absExpr jv) else none)
          pure (absExpr jv)).run lst
          = .ok (absExpr jv', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF jv' :=
  annot_val_c_after_annot_refines hsw hfw hcv hjty hjv h

/-- **`installed::annot_val_c` refines `annotValC`** (`Installed.lean:106-118`):
the value half of `check{Defn,Thm,Opaque}ValC` minus its inference — the two
scope guards, the annotation, the two post-annotation guards and the `ienv`
record.  `record` is `false` for an opaque (a discarded witness) and for the
theorem value phase B annotates.

Proved (task #62) from `Refine/ExprOpsC.lean`'s
`loose_bvars_bounded_refines`/`has_fvar_refines`, `Refine/TypeChecker.lean`'s
`annotate_core_refines`, and the lemma above. -/
theorem annot_val_c_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv_a : env.ConstantVal} {jty value : expr.Expr} {record : Bool}
    {out : core.result.Result expr.Expr core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hv : ExprWF value)
    (h : cached.installed.annot_val_c mode st fe cv_a jty value record
          = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok jv =>
        ∃ lst',
          (ConLeche.Cached.annotValC (absMode mode) lfe (absConstantVal cv_a)
              (absExpr jty) (absExpr value) record).run lst = .ok (absExpr jv, lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF jv
      | .Err e =>
        ErrSim e ((ConLeche.Cached.annotValC (absMode mode) lfe (absConstantVal cv_a)
            (absExpr jty) (absExpr value) record).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.installed.annot_val_c] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv := ExprOpsC.loose_bvars_bounded_refines hv hb
  rw [show ((0#u64 : Std.U64)).val = 0 from rfl] at hbv
  cases b with
  | false =>
    -- the cited loose-bound-variable `throw` (`Installed.lean:107-108`)
    simp only [Bool.false_eq_true, reduceIte] at h
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, hv1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim ce _
    exact errSim_invalid hce rfl (annotValC_loose_throw hbv.symm)
  | true =>
    simp only [reduceIte] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := ExprOpsC.has_fvar_refines hv hb1
    cases b1 with
    | true =>
      -- the cited free-variable `throw` (`Installed.lean:109-110`)
      simp only [reduceIte] at h
      obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v, hv1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hout, -⟩ := err_outS h
      subst hout
      show ErrSim ce _
      exact errSim_invalid hce rfl (annotValC_fvar_throw hbv.symm hb1v.symm)
    | false =>
      simp only [Bool.false_eq_true, reduceIte] at h
      obtain ⟨q, hann, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := q
      cases r with
      | Err e =>
        -- the annotation threw, and the cited call throws the same
        obtain ⟨hout, -⟩ := err_outS h
        subst hout
        show ErrSim e _
        have herr := (TypeChecker.annotate_core_refines hfuel hk).err st fe 0#u64
          value e st1 hsw hfw hv hann lst lfe hsr hfr
        simp only [ConLeche.Cached.opE] at herr
        exact ErrSim.trans herr (fun _ hle =>
          annotValC_annot_err (cvA := absConstantVal cv_a) (jty := absExpr jty)
            (record := record) hbv.symm hb1v.symm hle)
      | Ok jv0 =>
        obtain ⟨lst1, hrunA, hsr1, hsw1, hjvw⟩ :=
          (TypeChecker.annotate_core_refines hfuel hk).ok st fe 0#u64 value jv0 st1
            hsw hfw hv hann lst lfe hsr hfr
        simp only [ConLeche.Cached.opE] at hrunA
        have hrunA' : ((ConLeche.Cached.coreKnotI (absMode mode) lfe
            ConLeche.checkFuel).annotate 0 (absExpr value)).run lst
            = .ok (absExpr jv0, lst1) := hrunA
        have hat := annotValC_at_annot (cvA := absConstantVal cv_a) (jty := absExpr jty)
          (record := record) hbv.symm hb1v.symm hrunA'
        have hrest := annot_val_c_after_annot_refines hsw1 hfw hcv hjty hjvw h lst1 lfe
          hsr1 hfr
        cases out with
        | Ok jv =>
          obtain ⟨lst', hrunT, hsr', hsw', hjvw'⟩ := hrest
          exact ⟨lst', by rw [hat]; exact hrunT, hsr', hsw', hjvw'⟩
        | Err e =>
          show ErrSim e _
          rw [hat]
          exact hrest

/-- `annot_val_c_refines` at a success, the pre-#67 statement. -/
theorem annot_val_c_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv_a : env.ConstantVal} {jty value jv : expr.Expr} {record : Bool}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hv : ExprWF value)
    (h : cached.installed.annot_val_c mode st fe cv_a jty value record
          = ok (.Ok jv, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (ConLeche.Cached.annotValC (absMode mode) lfe (absConstantVal cv_a)
            (absExpr jty) (absExpr value) record).run lst = .ok (absExpr jv, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF jv :=
  annot_val_c_refines hfuel hk hsw hfw hcv hjty hv h

/-- **`installed::annot_value_c_tail` refines `annotValueC`'s tail**
(`Installed.lean:124-129`): the value's install half and the triple.  Stated at
the post-header header and type, which is what lets it compose with
`annot_constant_val_c_refines`.

Proved (task #62) from `annot_val_c_refines` above and the triple. -/
theorem annot_value_c_tail_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv_a : env.ConstantVal} {jty value : expr.Expr} {record : Bool}
    {out : core.result.Result (env.ConstantVal × expr.Expr × expr.Expr)
      core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hv : ExprWF value)
    (h : cached.installed.annot_value_c_tail mode st fe cv_a jty value record
          = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok (cv_a', jty', jv) =>
        ∃ lst',
          (do
            let jv' ← ConLeche.Cached.annotValC (absMode mode) lfe
              (absConstantVal cv_a) (absExpr jty) (absExpr value) record
            pure (absConstantVal cv_a, absExpr jty, jv')).run lst
            = .ok ((absConstantVal cv_a', absExpr jty', absExpr jv), lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv_a' ∧ ExprWF jty'
          ∧ ExprWF jv
      | .Err e =>
        ErrSim e
          ((do
            let jv' ← ConLeche.Cached.annotValC (absMode mode) lfe
              (absConstantVal cv_a) (absExpr jty) (absExpr value) record
            pure (absConstantVal cv_a, absExpr jty, jv')).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.installed.annot_value_c_tail] at h
  obtain ⟨q, hval, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  have hrest := annot_val_c_refines hfuel hk hsw hfw hcv hjty hv hval lst lfe hsr hfr
  cases r with
  | Err e =>
    -- the value's install half threw, and the cited `do` block passes it on
    obtain ⟨hout, rfl⟩ := err_outS h
    subst hout
    show ErrSim e _
    exact ErrSim.bindCM hrest
  | Ok jv0 =>
    obtain ⟨hout, rfl⟩ := ok_outS h
    subst hout
    obtain ⟨lst', hrunV, hsr', hsw', hjvw⟩ := hrest
    exact ⟨lst', run_bind_ok hrunV rfl, hsr', hsw', hcv, hjty, hjvw⟩

/-- `annot_value_c_tail_refines` at a success, the pre-#67 statement. -/
theorem annot_value_c_tail_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv_a cv_a' : env.ConstantVal} {jty jty' value jv : expr.Expr} {record : Bool}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hv : ExprWF value)
    (h : cached.installed.annot_value_c_tail mode st fe cv_a jty value record
          = ok (.Ok (cv_a', jty', jv), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (do
          let jv' ← ConLeche.Cached.annotValC (absMode mode) lfe
            (absConstantVal cv_a) (absExpr jty) (absExpr value) record
          pure (absConstantVal cv_a, absExpr jty, jv')).run lst
          = .ok ((absConstantVal cv_a', absExpr jty', absExpr jv), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv_a' ∧ ExprWF jty'
        ∧ ExprWF jv :=
  annot_value_c_tail_refines hfuel hk hsw hfw hcv hjty hv h

/-- **`installed::annot_value_c` refines `annotValueC`**
(`Installed.lean:124-129`): phase A's install of a separable value declaration
— the per-declaration flush, the header's install half, the value's install
half, and the triple.

Over the whole outcome (task #67): the flush cannot fail, so every failure is
the header's or the value's, and the cited `do` block passes it on. -/
theorem annot_value_c_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr} {record : Bool}
    {out : core.result.Result (env.ConstantVal × expr.Expr × expr.Expr)
      core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : cached.installed.annot_value_c mode st fe cv value record = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok (cv_a, jty, jv) =>
        ∃ lst',
          (ConLeche.Cached.annotValueC (absMode mode) lfe (absConstantVal cv)
              (absExpr value) record).run lst
            = .ok ((absConstantVal cv_a, absExpr jty, absExpr jv), lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv_a ∧ ExprWF jty
          ∧ ExprWF jv
      | .Err e =>
        ErrSim e ((ConLeche.Cached.annotValueC (absMode mode) lfe (absConstantVal cv)
            (absExpr value) record).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.installed.annot_value_c] at h
  obtain ⟨st1, hflush, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hrunf, hrel1, hwf1, -⟩ := StateC.flush_c_refines hsr hsw hflush
  obtain ⟨q, hacv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st2⟩ := q
  have hhead := annot_constant_val_c_refines hfuel hk hwf1 hfw hcv hacv lst.flushed lfe
    hrel1 hfr
  cases r with
  | Err e =>
    -- the header's install half threw, and the cited `do` block passes it on
    obtain ⟨hout, rfl⟩ := err_outS h
    subst hout
    show ErrSim e _
    rw [ConLeche.Cached.annotValueC]
    exact ErrSim.trans hhead (fun le hle => run_bind_ok hrunf (run_bind_err hle))
  | Ok r1 =>
    obtain ⟨cv1, e1⟩ := r1
    obtain ⟨lst1, hrun1, hsr1, hsw1, hcv1, hjty1⟩ := hhead
    have hrest := annot_value_c_tail_refines hfuel hk hsw1 hfw hcv1 hjty1 hv h lst1 lfe
      hsr1 hfr
    cases out with
    | Ok p =>
      obtain ⟨cv_a, jty, jv⟩ := p
      obtain ⟨lst2, hrun2, hsr2, hsw2, hcvw, hjtyw, hjvw⟩ := hrest
      refine ⟨lst2, ?_, hsr2, hsw2, hcvw, hjtyw, hjvw⟩
      rw [ConLeche.Cached.annotValueC]
      exact run_bind_ok hrunf (run_bind_ok hrun1 hrun2)
    | Err e =>
      show ErrSim e _
      rw [ConLeche.Cached.annotValueC]
      exact ErrSim.trans hrest (fun le hle => run_bind_ok hrunf (run_bind_ok hrun1 hle))

/-- `annot_value_c_refines` at a success, the pre-#67 statement. -/
theorem annot_value_c_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv cv_a : env.ConstantVal} {jty value jv : expr.Expr} {record : Bool}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : cached.installed.annot_value_c mode st fe cv value record
          = ok (.Ok (cv_a, jty, jv), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (ConLeche.Cached.annotValueC (absMode mode) lfe (absConstantVal cv)
            (absExpr value) record).run lst
          = .ok ((absConstantVal cv_a, absExpr jty, absExpr jv), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv_a ∧ ExprWF jty
        ∧ ExprWF jv :=
  annot_value_c_refines hfuel hk hsw hfw hcv hv h

/-! ## Phase A: the step

`annotStepC` (`Installed.lean:136-169`) is a four-way dispatch: the three value
kinds are annotated and installed, everything else takes the ordinary step.
Each arm below is stated against `annotStepC` **at the constructor that selects
it**, which is what makes `annot_step_c_refines` a `cases` with nothing left
over.  Where the cited arms rebuild the declaration they matched
(`checkDeclStepC mode fe (.defnDecl cv value hint)`) the port hands
`check_decl_step_c` the `pd` it already has (the module note's deviation); the
arm lemmas therefore take `pd` and the hypothesis that it *is* that
constructor, which is what the call site supplies. -/

set_option linter.unusedVariables false in
/-- **`installed::annot_step_other_c` refines the cited `pure (← checkDeclStepC
mode fe pd, pend)`** (`Installed.lean:136-169`): the ordinary step, which
leaves the records untouched — axioms, inductive and basis blocks and the
pinned branches are checked in full at their install.

`hvar : CheckerPins.PinsWF pins` is threaded from here — the pin argument's own
well-formedness, without which a corrupt stored hash word makes `expr::beq`
inexact on a pin that nonetheless abstracts to the right value.  `hpins`
travelled beside it until **task #74** made the cited fold take the pin list
too, and `CheckerDecl.DivModOrElse mode` until **task #65** made a thrown pin
attempt the check's verdict.

Over the whole outcome (task #67): this step *is* the ordinary step, so both
halves are `check_decl_step_c_refines`'s, and `hinde` — `IndRoutesSpecErr`, the
failure half of the inductive routes' seam — travels beside `hind` from here
down. -/
theorem annot_step_other_c_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {pend : alloc.vec.Vec parsed_c.PendingCheck} {pd : parsed_c.DeclC}
    {out : core.result.Result (fenv.FEnv × alloc.vec.Vec parsed_c.PendingCheck)
      core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnvCanon fe) (hfull : FEnvFull fe)
    (hd : DeclCWF pd)
    (h : cached.installed.annot_step_other_c mode pins st fe pend pd
          = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok (fe', pend') =>
        ∃ lst' lfe',
          (ConLeche.Cached.checkDeclStepC (absMode mode) (absPins pins) lfe (absDeclC pd)).run lst
              = .ok (lfe', lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ FEnvCanon fe' ∧ FEnvFull fe'
          ∧ pend' = pend
      | .Err e =>
        ErrSim e
          ((ConLeche.Cached.checkDeclStepC (absMode mode) (absPins pins) lfe (absDeclC pd)).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.installed.annot_step_other_c] at h
  obtain ⟨q, hstep, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  have hrest := CheckerDecl.check_decl_step_c_refines IndAbs.check_fuel_eq hk.1 hind
    hinde hvar hsw hfw hcan hfull hd hstep lst lfe hsr hfr
  cases r with
  | Ok fe2 =>
    obtain ⟨hout, rfl⟩ := ok_outS h
    subst hout
    obtain ⟨lst', lfe', hrun, rest⟩ := hrest
    exact ⟨lst', lfe', hrun, rest.1, rest.2.1, rest.2.2.1, rest.2.2.2.1,
      rest.2.2.2.2.1, rest.2.2.2.2.2, rfl⟩
  | Err e =>
    obtain ⟨hout, rfl⟩ := err_outS h
    subst hout
    exact hrest

/-- `annot_step_other_c_refines` at a success, the pre-#67 statement. -/
theorem annot_step_other_c_refines_ok {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {pend pend' : alloc.vec.Vec parsed_c.PendingCheck} {pd : parsed_c.DeclC}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnvCanon fe) (hfull : FEnvFull fe)
    (hd : DeclCWF pd)
    (h : cached.installed.annot_step_other_c mode pins st fe pend pd
          = ok (.Ok (fe', pend'), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkDeclStepC (absMode mode) (absPins pins) lfe (absDeclC pd)).run lst
            = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ FEnvCanon fe' ∧ FEnvFull fe'
        ∧ pend' = pend :=
  annot_step_other_c_refines hk hind hinde hvar hsw hfw hcan hfull hd h

/-- **`installed::annot_step_defn_c_push` refines the cited push**
(`Installed.lean:136-169`, the `.defnDecl` arm's tail): the constant is pushed
as a `.defnInfo` and the record appended, with the installation counter read
**before** the push (the RC-linearity comment the cited code carries). -/
theorem annot_step_defn_c_push_refines {i : Std.U64} {fe fe' : fenv.FEnv}
    {pend pend' : alloc.vec.Vec parsed_c.PendingCheck} {cv_a : env.ConstantVal}
    {jv : expr.Expr} {hint : env.ReducibilityHint}
    (hfw : FEnvWF fe) (hcan : FEnvCanon fe) (hfull : FEnvFull fe)
    (hcv : ConstantValWF cv_a) (hjv : ExprWF jv)
    (hpe : PendingChecksWF pend)
    (h : cached.installed.annot_step_defn_c_push i fe pend cv_a jv hint
          = ok (fe', pend')) :
    ∀ lfe, FEnvRel fe lfe →
      FEnvRel fe' (lfe.push (.defnInfo (absConstantVal cv_a) (absExpr jv)
          (absHint hint)))
      ∧ FEnvWF fe'
      ∧ absPendingChecks pend' = absPendingChecks pend ++
          [⟨⟨.defn, absConstantVal cv_a, absExpr jv⟩, i.val, lfe.visibleBelow⟩]
      ∧ PendingChecksWF pend'
      ∧ FEnvCanon fe' ∧ FEnvFull fe' := by
  intro lfe hfr
  rw [cached.installed.annot_step_defn_c_push] at h
  obtain ⟨cv, hcvd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e, hed, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨rh, hrhd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨fe2, hpush, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨pend1, hppush, h⟩ := bind_eq_ok_iff.mp h
  rw [Env.constant_val_dup_refines hcvd] at hpush
  rw [Expr.dup_eq hed] at hpush
  rw [Env.reducibility_hint_dup_refines hrhd] at hpush
  have hci : ConstantInfoWF (env.ConstantInfo.DefnInfo cv_a jv hint) := ⟨hcv, hjv⟩
  obtain ⟨hrel', hwf'⟩ := FEnv.push_refines hfr hfw hci hpush
  obtain ⟨hcan', hfull'⟩ := FEnv.push_canon hfw hci hcan hfull hpush
  have hfe : fe2 = fe' ∧ pend1 = pend' := by simpa using h
  obtain ⟨rfl, rfl⟩ := hfe
  refine ⟨by simpa [absConstantInfo] using hrel', hwf', ?_,
    PendingChecksWF_push hpe ⟨hcv, hjv⟩ hppush, hcan', hfull'⟩
  rw [absPendingChecks_push hppush]
  congr 2
  rw [absPendingCheck, CheckerSplit.absValueGroup, CheckerSplit.absValueKind]
  simp only [hfr.2.1]

/-- **`installed::annot_step_defn_c` refines `annotStepC`'s `.defnDecl` arm**
(`Installed.lean:136-169`): a pin-certified operation takes the ordinary step
(its check is not separable from its install), everything else is annotated,
installed, and recorded as pending. -/
theorem annot_step_defn_c_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {st st' : cached.state_c.CState} {i : Std.U64} {fe : fenv.FEnv}
    {pend : alloc.vec.Vec parsed_c.PendingCheck} {pd : parsed_c.DeclC}
    {cv : env.ConstantVal} {value : expr.Expr} {hint : env.ReducibilityHint}
    {out : core.result.Result (fenv.FEnv × alloc.vec.Vec parsed_c.PendingCheck)
      core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnvCanon fe) (hfull : FEnvFull fe)
    (hcv : ConstantValWF cv)
    (hv : ExprWF value) (hpe : PendingChecksWF pend)
    (hpd : pd = .DefnDecl cv value hint)
    (h : cached.installed.annot_step_defn_c mode pins st i fe pend pd cv value hint
          = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok (fe', pend') =>
        ∃ lst' lfe',
          (ConLeche.Cached.annotStepC (absMode mode) (absPins pins) i.val lfe
              (absPendingChecks pend).toArray (absDeclC pd)).run lst
            = .ok ((lfe', (absPendingChecks pend').toArray), lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ PendingChecksWF pend' ∧ FEnvCanon fe' ∧ FEnvFull fe'
      | .Err e =>
        ErrSim e
          ((ConLeche.Cached.annotStepC (absMode mode) (absPins pins) i.val lfe
              (absPendingChecks pend).toArray (absDeclC pd)).run lst) := by
  intro lst lfe hsr hfr
  subst hpd
  rw [cached.installed.annot_step_defn_c] at h
  obtain ⟨v, hv1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hv1e, hv1w⟩ := CoreK.nat_op_names_refines hv1
  have hbv : b = ConLeche.natOpNames.contains (absConstantVal cv).name := by
    rw [Name.contains_refines hv1w hcv.1 hb, hv1e]; rfl
  have hdwf : DeclCWF (parsed_c.DeclC.DefnDecl cv value hint) := ⟨hcv, hv⟩
  by_cases hbt : b = true
  · subst hbt
    simp only [if_pos] at h
    have hres := annot_step_other_c_refines hk hind hinde hvar hsw hfw hcan hfull
      hdwf h lst lfe hsr hfr
    rw [absDeclC] at hres
    cases out with
    | Ok p =>
      obtain ⟨fe', pend'⟩ := p
      obtain ⟨lst', lfe', hrun, hsr', hsw', hfr', hfw', hcan', hfull', rfl⟩ := hres
      refine ⟨lst', lfe', ?_, hsr', hsw', hfr', hfw', hpe, hcan', hfull'⟩
      rw [absDeclC, ConLeche.Cached.annotStepC]
      rw [if_pos (by rw [← hbv]; simp)]
      simp only [StateT.run_bind, hrun]
      rfl
    | Err e =>
      show ErrSim e _
      rw [absDeclC, ConLeche.Cached.annotStepC]
      rw [if_pos (by rw [← hbv]; simp)]
      exact ErrSim.bindCM hres
  · have hbf : b = false := by cases b with | false => rfl | true => exact absurd rfl hbt
    subst hbf
    simp only [Bool.false_eq_true, reduceIte] at h
    obtain ⟨v1, hv2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hv2e, hv2w⟩ := CoreK.nat_div_mod_names_refines hv2
    have hb1v : b1 = ConLeche.natDivModNames.contains (absConstantVal cv).name := by
      rw [Name.contains_refines hv2w hcv.1 hb1, hv2e]; rfl
    by_cases hb1t : b1 = true
    · subst hb1t
      simp only [if_pos] at h
      have hres := annot_step_other_c_refines hk hind hinde hvar hsw hfw hcan
        hfull hdwf h lst lfe hsr hfr
      rw [absDeclC] at hres
      cases out with
      | Ok p =>
        obtain ⟨fe', pend'⟩ := p
        obtain ⟨lst', lfe', hrun, hsr', hsw', hfr', hfw', hcan', hfull', rfl⟩ := hres
        refine ⟨lst', lfe', ?_, hsr', hsw', hfr', hfw', hpe, hcan', hfull'⟩
        rw [absDeclC, ConLeche.Cached.annotStepC]
        rw [if_pos (by rw [← hbv, ← hb1v]; simp)]
        simp only [StateT.run_bind, hrun]
        rfl
      | Err e =>
        show ErrSim e _
        rw [absDeclC, ConLeche.Cached.annotStepC]
        rw [if_pos (by rw [← hbv, ← hb1v]; simp)]
        exact ErrSim.bindCM hres
    · have hb1f : b1 = false := by
        cases b1 with | false => rfl | true => exact absurd rfl hb1t
      subst hb1f
      simp only [Bool.false_eq_true, reduceIte] at h
      obtain ⟨q, hval, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := q
      have hvalr := annot_value_c_refines IndAbs.check_fuel_eq hk.1 hsw hfw hcv hv hval
        lst lfe hsr hfr
      cases r with
      | Err e =>
        -- the install half threw, and the cited arm passes it on
        obtain ⟨hout, rfl⟩ := err_outS h
        subst hout
        show ErrSim e _
        rw [absDeclC, ConLeche.Cached.annotStepC]
        rw [if_neg (by rw [← hbv, ← hb1v]; simp)]
        exact ErrSim.bindCM hvalr
      | Ok r1 =>
        obtain ⟨cv1, jty1, jv1⟩ := r1
        obtain ⟨p, hpush, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨fe2, pend2⟩ := p
        obtain ⟨hout, rfl⟩ := ok_outS h
        subst hout
        obtain ⟨lst', hrun, hsr', hsw', hcv1, hjty1, hjv1⟩ := hvalr
        obtain ⟨hfr', hfw', hpabs, hpw, hcan', hfull'⟩ :=
          annot_step_defn_c_push_refines hfw hcan hfull hcv1 hjv1 hpe hpush lfe hfr
        refine ⟨lst', _, ?_, hsr', hsw', hfr', hfw', hpw, hcan', hfull'⟩
        rw [absDeclC, ConLeche.Cached.annotStepC]
        rw [if_neg (by rw [← hbv, ← hb1v]; simp)]
        simp only [StateT.run_bind, hrun]
        rw [hpabs]
        simp

/-- `annot_step_defn_c_refines` at a success, the pre-#67 statement. -/
theorem annot_step_defn_c_refines_ok {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {st st' : cached.state_c.CState} {i : Std.U64} {fe fe' : fenv.FEnv}
    {pend pend' : alloc.vec.Vec parsed_c.PendingCheck} {pd : parsed_c.DeclC}
    {cv : env.ConstantVal} {value : expr.Expr} {hint : env.ReducibilityHint}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnvCanon fe) (hfull : FEnvFull fe)
    (hcv : ConstantValWF cv)
    (hv : ExprWF value) (hpe : PendingChecksWF pend)
    (hpd : pd = .DefnDecl cv value hint)
    (h : cached.installed.annot_step_defn_c mode pins st i fe pend pd cv value hint
          = ok (.Ok (fe', pend'), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.annotStepC (absMode mode) (absPins pins) i.val lfe
            (absPendingChecks pend).toArray (absDeclC pd)).run lst
          = .ok ((lfe', (absPendingChecks pend').toArray), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ PendingChecksWF pend' ∧ FEnvCanon fe' ∧ FEnvFull fe' :=
  annot_step_defn_c_refines hk hind hinde hvar hsw hfw hcan hfull hcv hv hpe hpd h

/-- **`installed::annot_step_thm_c_push` refines the cited record and push**
(`Installed.lean:136-169`, the `.thmDecl` arm's tail): the `ienv` record with
**no value** (`recordCConst … none`), then the constant pushed with the
record's own raw value and the pending record appended. -/
theorem annot_step_thm_c_push_refines {st st' : cached.state_c.CState}
    {i : Std.U64} {fe fe' : fenv.FEnv}
    {pend pend' : alloc.vec.Vec parsed_c.PendingCheck} {cv_a : env.ConstantVal}
    {jty value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnvCanon fe) (hfull : FEnvFull fe)
    (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hv : ExprWF value) (hpe : PendingChecksWF pend)
    (h : cached.installed.annot_step_thm_c_push st i fe pend cv_a jty value
          = ok ((fe', pend'), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (ConLeche.Cached.recordCConst (absConstantVal cv_a).name
            (absConstantVal cv_a).type (absExpr jty) none).run lst = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st'
        ∧ FEnvRel fe' (lfe.push (.thmInfo (absConstantVal cv_a) (absExpr value)))
        ∧ FEnvWF fe'
        ∧ absPendingChecks pend' = absPendingChecks pend ++
            [⟨⟨.thm, absConstantVal cv_a, absExpr value⟩, i.val, lfe.visibleBelow⟩]
        ∧ PendingChecksWF pend'
        ∧ FEnvCanon fe' ∧ FEnvFull fe' := by
  intro lst lfe hsr hfr
  rw [cached.installed.annot_step_thm_c_push] at h
  obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨st1, hrec, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨cv, hcvd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨fe2, hpush, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨pend1, hppush, h⟩ := bind_eq_ok_iff.mp h
  have hnv : n = cv_a.name := by rw [name_dup_eq] at hn; exact (Result.ok_injective hn).symm
  rw [hnv] at hrec
  rw [Expr.dup_eq he] at hrec
  obtain ⟨lst', hrun, hsr', hsw'⟩ :=
    StateC.record_c_const_refines hsw hcv.1 hcv.2.2 hjty (by simp) hrec lst hsr
  rw [Env.constant_val_dup_refines hcvd] at hpush
  rw [Expr.dup_eq he1] at hpush hppush
  have hci : ConstantInfoWF (env.ConstantInfo.ThmInfo cv_a value) := ⟨hcv, hv⟩
  obtain ⟨hrel', hwf'⟩ := FEnv.push_refines hfr hfw hci hpush
  obtain ⟨hcan', hfull'⟩ := FEnv.push_canon hfw hci hcan hfull hpush
  have hfe : fe2 = fe' ∧ pend1 = pend' ∧ st1 = st' := by simpa using h
  obtain ⟨rfl, rfl, rfl⟩ := hfe
  refine ⟨lst', by simpa [absConstantVal] using hrun, hsr', hsw',
    by simpa [absConstantInfo] using hrel', hwf', ?_,
    PendingChecksWF_push hpe ⟨hcv, hv⟩ hppush, hcan', hfull'⟩
  rw [absPendingChecks_push hppush]
  congr 2
  rw [absPendingCheck, CheckerSplit.absValueGroup, CheckerSplit.absValueKind]
  simp only [hfr.2.1]

/-- **`installed::annot_step_thm_c` refines `annotStepC`'s `.thmDecl` arm**
(`Installed.lean:136-169`): **a theorem installs BY STATEMENT** — the header's
install half runs and the constant is pushed with the record's own raw value,
which nothing ever reads, so phase A never enters a theorem's body. -/
theorem annot_step_thm_c_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    {st st' : cached.state_c.CState} {i : Std.U64} {fe : fenv.FEnv}
    {pend : alloc.vec.Vec parsed_c.PendingCheck}
    {cv : env.ConstantVal} {value : expr.Expr}
    {out : core.result.Result (fenv.FEnv × alloc.vec.Vec parsed_c.PendingCheck)
      core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnvCanon fe) (hfull : FEnvFull fe)
    (hcv : ConstantValWF cv)
    (hv : ExprWF value) (hpe : PendingChecksWF pend)
    (h : cached.installed.annot_step_thm_c mode st i fe pend cv value
          = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok (fe', pend') =>
        ∃ lst' lfe',
          (ConLeche.Cached.annotStepC (absMode mode) (absPins pins) i.val lfe
              (absPendingChecks pend).toArray
              (.thmDecl (absConstantVal cv) (absExpr value))).run lst
            = .ok ((lfe', (absPendingChecks pend').toArray), lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ PendingChecksWF pend' ∧ FEnvCanon fe' ∧ FEnvFull fe'
      | .Err e =>
        ErrSim e
          ((ConLeche.Cached.annotStepC (absMode mode) (absPins pins) i.val lfe
              (absPendingChecks pend).toArray
              (.thmDecl (absConstantVal cv) (absExpr value))).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.installed.annot_step_thm_c] at h
  obtain ⟨st1, hflush, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hrunf, hrel1, hwf1, -⟩ := StateC.flush_c_refines hsr hsw hflush
  obtain ⟨q, hacv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st2⟩ := q
  have hhead := annot_constant_val_c_refines IndAbs.check_fuel_eq hk.1 hwf1 hfw hcv hacv
    lst.flushed lfe hrel1 hfr
  cases r with
  | Err e =>
    -- the header's install half threw, and the cited arm passes it on
    obtain ⟨hout, rfl⟩ := err_outS h
    subst hout
    show ErrSim e _
    rw [ConLeche.Cached.annotStepC]
    exact ErrSim.trans hhead (fun _ hle => run_bind_ok hrunf (run_bind_err hle))
  | Ok r1 =>
    obtain ⟨cv1, jty1⟩ := r1
    obtain ⟨lst1, hrun1, hsr1, hsw1, hcv1, hjty1⟩ := hhead
    obtain ⟨p, hpush, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨pr, st3⟩ := p
    obtain ⟨fe2, pend2⟩ := pr
    obtain ⟨hout, rfl⟩ := ok_outS h
    subst hout
    obtain ⟨lst2, hrunr, hsr2, hsw2, hfr2, hfw2, hpabs, hpw, hcan', hfull'⟩ :=
      annot_step_thm_c_push_refines hsw1 hfw hcan hfull hcv1 hjty1 hv hpe hpush lst1
        lfe hsr1 hfr
    refine ⟨lst2, _, ?_, hsr2, hsw2, hfr2, hfw2, hpw, hcan', hfull'⟩
    rw [ConLeche.Cached.annotStepC]
    refine run_bind_ok hrunf (run_bind_ok hrun1 (run_bind_ok hrunr ?_))
    rw [hpabs, ← List.push_toArray]
    rfl

/-- `annot_step_thm_c_refines` at a success, the pre-#67 statement. -/
theorem annot_step_thm_c_refines_ok {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    {st st' : cached.state_c.CState} {i : Std.U64} {fe fe' : fenv.FEnv}
    {pend pend' : alloc.vec.Vec parsed_c.PendingCheck}
    {cv : env.ConstantVal} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnvCanon fe) (hfull : FEnvFull fe)
    (hcv : ConstantValWF cv)
    (hv : ExprWF value) (hpe : PendingChecksWF pend)
    (h : cached.installed.annot_step_thm_c mode st i fe pend cv value
          = ok (.Ok (fe', pend'), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.annotStepC (absMode mode) (absPins pins) i.val lfe
            (absPendingChecks pend).toArray
            (.thmDecl (absConstantVal cv) (absExpr value))).run lst
          = .ok ((lfe', (absPendingChecks pend').toArray), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ PendingChecksWF pend' ∧ FEnvCanon fe' ∧ FEnvFull fe' :=
  annot_step_thm_c_refines hk hsw hfw hcan hfull hcv hv hpe h

/-- **`installed::annot_step_opaque_c_push` refines the cited push**
(`Installed.lean:136-169`, the `.opaqueDecl` arm's tail): the constant is
installed **as an axiom** — an opaque's value is a discarded witness. -/
theorem annot_step_opaque_c_push_refines {i : Std.U64} {fe fe' : fenv.FEnv}
    {pend pend' : alloc.vec.Vec parsed_c.PendingCheck} {cv_a : env.ConstantVal}
    {jv : expr.Expr}
    (hfw : FEnvWF fe) (hcan : FEnvCanon fe) (hfull : FEnvFull fe)
    (hcv : ConstantValWF cv_a) (hjv : ExprWF jv)
    (hpe : PendingChecksWF pend)
    (h : cached.installed.annot_step_opaque_c_push i fe pend cv_a jv
          = ok (fe', pend')) :
    ∀ lfe, FEnvRel fe lfe →
      FEnvRel fe' (lfe.push (.axiomInfo (absConstantVal cv_a)))
      ∧ FEnvWF fe'
      ∧ absPendingChecks pend' = absPendingChecks pend ++
          [⟨⟨.opaque, absConstantVal cv_a, absExpr jv⟩, i.val, lfe.visibleBelow⟩]
      ∧ PendingChecksWF pend'
      ∧ FEnvCanon fe' ∧ FEnvFull fe' := by
  intro lfe hfr
  rw [cached.installed.annot_step_opaque_c_push] at h
  obtain ⟨cv, hcvd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨fe2, hpush, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨pend1, hppush, h⟩ := bind_eq_ok_iff.mp h
  rw [Env.constant_val_dup_refines hcvd] at hpush
  have hci : ConstantInfoWF (env.ConstantInfo.AxiomInfo cv_a) := hcv
  obtain ⟨hrel', hwf'⟩ := FEnv.push_refines hfr hfw hci hpush
  obtain ⟨hcan', hfull'⟩ := FEnv.push_canon hfw hci hcan hfull hpush
  have hfe : fe2 = fe' ∧ pend1 = pend' := by simpa using h
  obtain ⟨rfl, rfl⟩ := hfe
  refine ⟨by simpa [absConstantInfo] using hrel', hwf', ?_,
    PendingChecksWF_push hpe ⟨hcv, hjv⟩ hppush, hcan', hfull'⟩
  rw [absPendingChecks_push hppush]
  congr 2
  rw [absPendingCheck, CheckerSplit.absValueGroup, CheckerSplit.absValueKind]
  simp only [hfr.2.1]

/-- **`installed::annot_step_opaque_c` refines `annotStepC`'s `.opaqueDecl`
arm** (`Installed.lean:136-169`): a `reduce*` witness takes the ordinary step
(its identity certificate is part of its install), everything else is
annotated, installed as an axiom, and recorded as pending. -/
theorem annot_step_opaque_c_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {st st' : cached.state_c.CState} {i : Std.U64} {fe : fenv.FEnv}
    {pend : alloc.vec.Vec parsed_c.PendingCheck} {pd : parsed_c.DeclC}
    {cv : env.ConstantVal} {value : expr.Expr}
    {out : core.result.Result (fenv.FEnv × alloc.vec.Vec parsed_c.PendingCheck)
      core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnvCanon fe) (hfull : FEnvFull fe)
    (hcv : ConstantValWF cv)
    (hv : ExprWF value) (hpe : PendingChecksWF pend)
    (hpd : pd = .OpaqueDecl cv value)
    (h : cached.installed.annot_step_opaque_c mode pins st i fe pend pd cv value
          = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok (fe', pend') =>
        ∃ lst' lfe',
          (ConLeche.Cached.annotStepC (absMode mode) (absPins pins) i.val lfe
              (absPendingChecks pend).toArray (absDeclC pd)).run lst
            = .ok ((lfe', (absPendingChecks pend').toArray), lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ PendingChecksWF pend' ∧ FEnvCanon fe' ∧ FEnvFull fe'
      | .Err e =>
        ErrSim e
          ((ConLeche.Cached.annotStepC (absMode mode) (absPins pins) i.val lfe
              (absPendingChecks pend).toArray (absDeclC pd)).run lst) := by
  intro lst lfe hsr hfr
  subst hpd
  rw [cached.installed.annot_step_opaque_c] at h
  obtain ⟨v, hv1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hv1e, hv1w⟩ := TrustAxioms.reduce_op_names_refines hv1
  have hbv : b = ConLeche.reduceOpNames.contains (absConstantVal cv).name := by
    rw [Name.contains_refines hv1w hcv.1 hb, hv1e]; rfl
  have hdwf : DeclCWF (parsed_c.DeclC.OpaqueDecl cv value) := ⟨hcv, hv⟩
  by_cases hbt : b = true
  · subst hbt
    simp only [if_pos] at h
    have hres := annot_step_other_c_refines hk hind hinde hvar hsw hfw hcan hfull
      hdwf h lst lfe hsr hfr
    rw [absDeclC] at hres
    cases out with
    | Ok p =>
      obtain ⟨fe', pend'⟩ := p
      obtain ⟨lst', lfe', hrun, hsr', hsw', hfr', hfw', hcan', hfull', rfl⟩ := hres
      refine ⟨lst', lfe', ?_, hsr', hsw', hfr', hfw', hpe, hcan', hfull'⟩
      rw [absDeclC, ConLeche.Cached.annotStepC]
      rw [if_pos (by rw [← hbv])]
      simp only [StateT.run_bind, hrun]
      rfl
    | Err e =>
      show ErrSim e _
      rw [absDeclC, ConLeche.Cached.annotStepC]
      rw [if_pos (by rw [← hbv])]
      exact ErrSim.bindCM hres
  · have hbf : b = false := by cases b with | false => rfl | true => exact absurd rfl hbt
    subst hbf
    simp only [Bool.false_eq_true, reduceIte] at h
    obtain ⟨q, hval, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r, st1⟩ := q
    have hvalr := annot_value_c_refines IndAbs.check_fuel_eq hk.1 hsw hfw hcv hv hval
      lst lfe hsr hfr
    cases r with
    | Err e =>
      -- the install half threw, and the cited arm passes it on
      obtain ⟨hout, rfl⟩ := err_outS h
      subst hout
      show ErrSim e _
      rw [absDeclC, ConLeche.Cached.annotStepC]
      rw [if_neg (by rw [← hbv]; simp)]
      exact ErrSim.bindCM hvalr
    | Ok r1 =>
      obtain ⟨cv1, jty1, jv1⟩ := r1
      obtain ⟨p, hpush, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨fe2, pend2⟩ := p
      obtain ⟨hout, rfl⟩ := ok_outS h
      subst hout
      obtain ⟨lst', hrun, hsr', hsw', hcv1, hjty1, hjv1⟩ := hvalr
      obtain ⟨hfr', hfw', hpabs, hpw, hcan', hfull'⟩ :=
        annot_step_opaque_c_push_refines hfw hcan hfull hcv1 hjv1 hpe hpush lfe hfr
      refine ⟨lst', _, ?_, hsr', hsw', hfr', hfw', hpw, hcan', hfull'⟩
      rw [absDeclC, ConLeche.Cached.annotStepC]
      rw [if_neg (by rw [← hbv]; simp)]
      simp only [StateT.run_bind, hrun]
      rw [hpabs]
      simp

/-- `annot_step_opaque_c_refines` at a success, the pre-#67 statement. -/
theorem annot_step_opaque_c_refines_ok {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {st st' : cached.state_c.CState} {i : Std.U64} {fe fe' : fenv.FEnv}
    {pend pend' : alloc.vec.Vec parsed_c.PendingCheck} {pd : parsed_c.DeclC}
    {cv : env.ConstantVal} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnvCanon fe) (hfull : FEnvFull fe)
    (hcv : ConstantValWF cv)
    (hv : ExprWF value) (hpe : PendingChecksWF pend)
    (hpd : pd = .OpaqueDecl cv value)
    (h : cached.installed.annot_step_opaque_c mode pins st i fe pend pd cv value
          = ok (.Ok (fe', pend'), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.annotStepC (absMode mode) (absPins pins) i.val lfe
            (absPendingChecks pend).toArray (absDeclC pd)).run lst
          = .ok ((lfe', (absPendingChecks pend').toArray), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ PendingChecksWF pend' ∧ FEnvCanon fe' ∧ FEnvFull fe' :=
  annot_step_opaque_c_refines hk hind hinde hvar hsw hfw hcan hfull hcv hv hpe
    hpd h

/-- **`installed::annot_step_c` refines `annotStepC`** (`Installed.lean:136-169`):
the four-way dispatch itself.  A `cases` over the port's six constructors: three
go to their arm lemma above, the other three to the catch-all. -/
theorem annot_step_c_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {st st' : cached.state_c.CState} {i : Std.U64} {fe : fenv.FEnv}
    {pend : alloc.vec.Vec parsed_c.PendingCheck} {pd : parsed_c.DeclC}
    {out : core.result.Result (fenv.FEnv × alloc.vec.Vec parsed_c.PendingCheck)
      core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnvCanon fe) (hfull : FEnvFull fe)
    (hd : DeclCWF pd)
    (hpe : PendingChecksWF pend)
    (h : cached.installed.annot_step_c mode pins st i fe pend pd = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok (fe', pend') =>
        ∃ lst' lfe',
          (ConLeche.Cached.annotStepC (absMode mode) (absPins pins) i.val lfe
              (absPendingChecks pend).toArray (absDeclC pd)).run lst
            = .ok ((lfe', (absPendingChecks pend').toArray), lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ PendingChecksWF pend' ∧ FEnvCanon fe' ∧ FEnvFull fe'
      | .Err e =>
        ErrSim e
          ((ConLeche.Cached.annotStepC (absMode mode) (absPins pins) i.val lfe
              (absPendingChecks pend).toArray (absDeclC pd)).run lst) := by
  intro lst lfe hsr hfr
  cases pd with
  | AxiomDecl cv =>
    rw [cached.installed.annot_step_c] at h
    have hres := annot_step_other_c_refines hk hind hinde hvar hsw hfw hcan hfull
      hd h lst lfe hsr hfr
    rw [absDeclC] at hres
    cases out with
    | Ok p =>
      obtain ⟨fe', pend'⟩ := p
      obtain ⟨lst', lfe', hrun, hsr', hsw', hfr', hfw', hcan', hfull', rfl⟩ := hres
      refine ⟨lst', lfe', ?_, hsr', hsw', hfr', hfw', hpe, hcan', hfull'⟩
      rw [absDeclC, ConLeche.Cached.annotStepC]
      · exact run_bind_ok hrun rfl
      all_goals simp
    | Err e =>
      show ErrSim e _
      rw [absDeclC, ConLeche.Cached.annotStepC]
      · exact ErrSim.bindCM hres
      all_goals simp
  | BasisDecl k =>
    rw [cached.installed.annot_step_c] at h
    have hres := annot_step_other_c_refines hk hind hinde hvar hsw hfw hcan hfull
      hd h lst lfe hsr hfr
    rw [absDeclC] at hres
    cases out with
    | Ok p =>
      obtain ⟨fe', pend'⟩ := p
      obtain ⟨lst', lfe', hrun, hsr', hsw', hfr', hfw', hcan', hfull', rfl⟩ := hres
      refine ⟨lst', lfe', ?_, hsr', hsw', hfr', hfw', hpe, hcan', hfull'⟩
      rw [absDeclC, ConLeche.Cached.annotStepC]
      · exact run_bind_ok hrun rfl
      all_goals simp
    | Err e =>
      show ErrSim e _
      rw [absDeclC, ConLeche.Cached.annotStepC]
      · exact ErrSim.bindCM hres
      all_goals simp
  | IndDecl block n_p =>
    rw [cached.installed.annot_step_c] at h
    have hres := annot_step_other_c_refines hk hind hinde hvar hsw hfw hcan hfull
      hd h lst lfe hsr hfr
    rw [absDeclC] at hres
    cases out with
    | Ok p =>
      obtain ⟨fe', pend'⟩ := p
      obtain ⟨lst', lfe', hrun, hsr', hsw', hfr', hfw', hcan', hfull', rfl⟩ := hres
      refine ⟨lst', lfe', ?_, hsr', hsw', hfr', hfw', hpe, hcan', hfull'⟩
      rw [absDeclC, ConLeche.Cached.annotStepC]
      · exact run_bind_ok hrun rfl
      all_goals simp
    | Err e =>
      show ErrSim e _
      rw [absDeclC, ConLeche.Cached.annotStepC]
      · exact ErrSim.bindCM hres
      all_goals simp
  | DefnDecl cv value hint =>
    rw [cached.installed.annot_step_c] at h
    have hres := annot_step_defn_c_refines hk hind hinde hvar hsw hfw hcan hfull
      hd.1 hd.2 hpe rfl h lst lfe hsr hfr
    cases out with
    | Ok p => obtain ⟨fe', pend'⟩ := p; exact hres
    | Err e => exact hres
  | ThmDecl cv value =>
    rw [cached.installed.annot_step_c] at h
    have hres := annot_step_thm_c_refines (pins := pins) hk hsw hfw hcan hfull hd.1 hd.2
      hpe h lst lfe hsr hfr
    cases out with
    | Ok p => obtain ⟨fe', pend'⟩ := p; exact hres
    | Err e => exact hres
  | OpaqueDecl cv value =>
    rw [cached.installed.annot_step_c] at h
    have hres := annot_step_opaque_c_refines hk hind hinde hvar hsw hfw hcan
      hfull hd.1 hd.2 hpe rfl h lst lfe hsr hfr
    cases out with
    | Ok p => obtain ⟨fe', pend'⟩ := p; exact hres
    | Err e => exact hres

/-- `annot_step_c_refines` at a success, the pre-#67 statement. -/
theorem annot_step_c_refines_ok {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {st st' : cached.state_c.CState} {i : Std.U64} {fe fe' : fenv.FEnv}
    {pend pend' : alloc.vec.Vec parsed_c.PendingCheck} {pd : parsed_c.DeclC}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnvCanon fe) (hfull : FEnvFull fe)
    (hd : DeclCWF pd)
    (hpe : PendingChecksWF pend)
    (h : cached.installed.annot_step_c mode pins st i fe pend pd
          = ok (.Ok (fe', pend'), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.annotStepC (absMode mode) (absPins pins) i.val lfe
            (absPendingChecks pend).toArray (absDeclC pd)).run lst
          = .ok ((lfe', (absPendingChecks pend').toArray), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ PendingChecksWF pend' ∧ FEnvCanon fe' ∧ FEnvFull fe' :=
  annot_step_c_refines hk hind hinde hvar hsw hfw hcan hfull hd hpe h

open ConLeche.Cached in
/-- `annotDeclStep` at a step that threw: the error **tagged with the fold
position** (`ConLeche/Cached/Installed.lean:175-180`), which is the accumulator's
own counter — the same number the port tags with. -/
private theorem annotDeclStep_err {mode : ConLeche.CheckMode} {n : Nat}
    {lpins : List ConLeche.NatOpPinSet}
    {lfe : ConLeche.FEnv} {pend : Array ConLeche.Cached.PendingCheck}
    {pd : ConLeche.Cached.DeclC} {s : CState} {le : ConLeche.CheckError}
    (h : annotStepC mode lpins n lfe pend pd s = .error le) :
    annotDeclStep mode lpins (n, lfe, pend) pd s = .error (le, n) := by
  rw [ConLeche.Cached.annotDeclStep, h]

/-- **`installed::annot_decl_step` refines `annotDeclStep`**
(`Installed.lean:175-180`): phase A's step with the position carried and the
error tagged.  The accumulator is a flat 3-tuple where the cited one is
`Nat × (FEnv × Array PendingCheck)` (deviation 1), so the Lean accumulator is
existentially quantified over the index component — the port's `FEnv` and the
Lean's are related, not equal.

Over the whole outcome (task #67): this is where the error picks up its fold
position, on both sides and from the same counter, which is what `ErrSimPos`
records. -/
theorem annot_decl_step_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {st st' : cached.state_c.CState} {pd : parsed_c.DeclC}
    {p : Std.U64 × fenv.FEnv × alloc.vec.Vec parsed_c.PendingCheck}
    {out : core.result.Result (Std.U64 × fenv.FEnv × alloc.vec.Vec parsed_c.PendingCheck)
      (core_types.CheckError × Std.U64)}
    (hsw : StateWF st) (hfw : FEnvWF p.2.1) (hcan : FEnvCanon p.2.1)
    (hfull : FEnvFull p.2.1) (hd : DeclCWF pd)
    (hpe : PendingChecksWF p.2.2)
    (h : cached.installed.annot_decl_step mode pins st p pd = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel p.2.1 lfe →
      match out with
      | .Ok q =>
        ∃ lst' lfe',
          ConLeche.Cached.annotDeclStep (absMode mode) (absPins pins)
              (p.1.val, lfe, (absPendingChecks p.2.2).toArray) (absDeclC pd) lst
            = .ok ((q.1.val, lfe', (absPendingChecks q.2.2).toArray), lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel q.2.1 lfe' ∧ FEnvWF q.2.1
          ∧ PendingChecksWF q.2.2 ∧ FEnvCanon q.2.1 ∧ FEnvFull q.2.1
      | .Err e =>
        ErrSimPos e
          (ConLeche.Cached.annotDeclStep (absMode mode) (absPins pins)
            (p.1.val, lfe, (absPendingChecks p.2.2).toArray) (absDeclC pd) lst) := by
  intro lst lfe hsr hfr
  rw [cached.installed.annot_decl_step] at h
  obtain ⟨i, f, v⟩ := p
  simp only at h hfw hcan hfull hpe hfr ⊢
  obtain ⟨r, hstep, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨res, st1⟩ := r
  have hres := annot_step_c_refines hk hind hinde hvar hsw hfw hcan hfull hd hpe
    hstep lst lfe hsr hfr
  cases res with
  | Err e =>
    -- the step threw; both sides tag with the accumulator's own counter
    obtain ⟨hout, rfl⟩ := err_outS h
    subst hout
    show ErrSimPos (e, i) _
    exact ErrSimPos.tag hres (fun _ hle => annotDeclStep_err hle)
  | Ok qq =>
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨f1, v1⟩ := qq
    obtain ⟨hout, rfl⟩ := ok_outS h
    subst hout
    obtain ⟨lst', lfe', hrun, hsr', hsw', hfr', hfw', hpw, hcan', hfull'⟩ := hres
    have hi1v : i1.val = i.val + 1 := by
      have he := Std.UScalar.add_equiv i 1#u64
      rw [hi1] at he
      simpa using he.2.1
    refine ⟨lst', lfe', ?_, hsr', hsw', hfr', hfw', hpw, hcan', hfull'⟩
    have hrun' : ConLeche.Cached.annotStepC (absMode mode) (absPins pins) i.val lfe
        (absPendingChecks v).toArray (absDeclC pd) lst
        = .ok ((lfe', (absPendingChecks v1).toArray), lst') := hrun
    rw [ConLeche.Cached.annotDeclStep, hrun', hi1v]

/-- `annot_decl_step_refines` at a success, the pre-#67 statement. -/
theorem annot_decl_step_refines_ok {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {st st' : cached.state_c.CState} {pd : parsed_c.DeclC}
    {p q : Std.U64 × fenv.FEnv × alloc.vec.Vec parsed_c.PendingCheck}
    (hsw : StateWF st) (hfw : FEnvWF p.2.1) (hcan : FEnvCanon p.2.1)
    (hfull : FEnvFull p.2.1) (hd : DeclCWF pd)
    (hpe : PendingChecksWF p.2.2)
    (h : cached.installed.annot_decl_step mode pins st p pd = ok (.Ok q, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel p.2.1 lfe →
      ∃ lst' lfe',
        ConLeche.Cached.annotDeclStep (absMode mode) (absPins pins)
            (p.1.val, lfe, (absPendingChecks p.2.2).toArray) (absDeclC pd) lst
          = .ok ((q.1.val, lfe', (absPendingChecks q.2.2).toArray), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel q.2.1 lfe' ∧ FEnvWF q.2.1
        ∧ PendingChecksWF q.2.2 ∧ FEnvCanon q.2.1 ∧ FEnvFull q.2.1 :=
  annot_decl_step_refines hk hind hinde hvar hsw hfw hcan hfull hd hpe h

/-! ## Phase B: the check

`checkPending` (`Installed.lean:239-253`) checks one record **against the
prefix view** `fe.restrictTo pc.vis`, from a flushed memo state.  Deviation 2
of the module note is in the statements: the index comes in at the installed
bound and goes back out there, where the cited code lets the caller keep its
own `fe` and returns `Unit`.  The port's two internal splits
(`check_pending_value` at the `let jv ← if …` join, `check_pending_tail` past
it) are tail-call requirements with no cited counterpart; they are stated
against the cited `do` block's corresponding tail, exactly as
`Refine/CheckerSplit.lean`'s `check_value_group_tail_refines` is. -/

open ConLeche.Cached in
/-- **`checkPending`'s conversion `throw`** (`ConLeche/Cached/Installed.lean:252-253`),
at the tail the port's `check_pending_tail` is stated against: both core calls
answered and the comparison came back `false`. -/
private theorem checkPendingTail_mismatch {mode : env.CheckMode}
    {lfe_v : ConLeche.FEnv} {pc : ConLeche.Cached.PendingCheck}
    {jv jvt : ConLeche.Expr} {lst lst1 lst2 : CState}
    (hinf : ((coreKnotI (absMode mode) lfe_v ConLeche.checkFuel).infer 0 jv).run lst
      = .ok (jvt, lst1))
    (hdef : ((coreKnotI (absMode mode) lfe_v ConLeche.checkFuel).defeq 0 jvt
        pc.vg.cvA.type).run lst1 = .ok (false, lst2)) :
    (do
      let jvt ← (coreKnotI (absMode mode) lfe_v ConLeche.checkFuel).infer 0 jv
      let b ← (coreKnotI (absMode mode) lfe_v ConLeche.checkFuel).defeq 0 jvt
        pc.vg.cvA.type
      if b then pure () else
        throw (ConLeche.CheckError.invalid
          s!"type mismatch in {pc.vg.kind.word} {pc.vg.cvA.name}")).run lst
      = .error (.invalid s!"type mismatch in {pc.vg.kind.word} {pc.vg.cvA.name}") :=
  run_bind_ok hinf (run_bind_ok hdef rfl)

/-- **`installed::check_pending_tail` refines `checkPending`'s tail**
(`Installed.lean:239-253`, past the `let jv ← if …` join): the value's inferred
type against the declared one, and the index handed back at the bound `k` it
came in at.  Stated at an arbitrary post-join `jv`, which is what lets the two
halves compose.

Over the whole outcome (task #67): the port's one `invalid` site
(`cached/installed.rs:630`) is the cited conversion `throw` (`:252-253`) — the
messages differ, which is exactly what `ErrSim` does not compare — and its two
other failures are what `infer_type_core` and `is_def_eq_core` threw. -/
theorem check_pending_tail_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {st st' : cached.state_c.CState} {fe_v : fenv.FEnv} {k : Std.U64}
    {pc : parsed_c.PendingCheck} {jv : expr.Expr}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe_v) (hpc : PendingCheckWF pc)
    (hjv : ExprWF jv)
    (h : cached.installed.check_pending_tail mode st fe_v k pc jv = ok (out, st')) :
    ∀ lst lfe_v, StateRel st lst → FEnvRel fe_v lfe_v →
      match out with
      | .Ok fe' =>
        ∃ lst',
          (do
            let jvt ← (ConLeche.Cached.coreKnotI (absMode mode) lfe_v
              ConLeche.checkFuel).infer 0 (absExpr jv)
            let b ← (ConLeche.Cached.coreKnotI (absMode mode) lfe_v
              ConLeche.checkFuel).defeq 0 jvt (absPendingCheck pc).vg.cvA.type
            if b then pure () else
              throw (ConLeche.CheckError.invalid
                s!"type mismatch in {(absPendingCheck pc).vg.kind.word} {(absPendingCheck pc).vg.cvA.name}")).run lst
            = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st'
          ∧ FEnvRel fe' (lfe_v.restrictTo k.val) ∧ FEnvWF fe'
      | .Err e =>
        ErrSim e
          ((do
            let jvt ← (ConLeche.Cached.coreKnotI (absMode mode) lfe_v
              ConLeche.checkFuel).infer 0 (absExpr jv)
            let b ← (ConLeche.Cached.coreKnotI (absMode mode) lfe_v
              ConLeche.checkFuel).defeq 0 jvt (absPendingCheck pc).vg.cvA.type
            if b then pure () else
              throw (ConLeche.CheckError.invalid
                s!"type mismatch in {(absPendingCheck pc).vg.kind.word} {(absPendingCheck pc).vg.cvA.name}")).run lst) := by
  intro lst lfe_v hsr hfr
  rw [cached.installed.check_pending_tail] at h
  obtain ⟨q, hinf, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  cases r with
  | Err e =>
    -- the value's inference threw, and the cited tail's first call throws the same
    obtain ⟨hout, rfl⟩ := err_outS h
    subst hout
    show ErrSim e _
    have herr := (TypeChecker.infer_type_core_refines IndAbs.check_fuel_eq hk.1).err st
      fe_v 0#u64 jv e _ hsw hfw hjv hinf lst lfe_v hsr hfr
    simp only [ConLeche.Cached.opE] at herr
    exact ErrSim.trans herr (fun _ hle => run_bind_err hle)
  | Ok jvt =>
    obtain ⟨lst1, hrunI, hsr1, hsw1, hjvtw⟩ :=
      (TypeChecker.infer_type_core_refines IndAbs.check_fuel_eq hk.1).ok st fe_v 0#u64 jv
        jvt st1 hsw hfw hjv hinf lst lfe_v hsr hfr
    simp only [ConLeche.Cached.opE] at hrunI
    have hrunI' : ((ConLeche.Cached.coreKnotI (absMode mode) lfe_v
        ConLeche.checkFuel).infer 0 (absExpr jv)).run lst = .ok (absExpr jvt, lst1) := hrunI
    obtain ⟨q1, hdef, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, st2⟩ := q1
    cases r1 with
    | Err e =>
      -- the conversion threw, and the cited tail's second call throws the same
      obtain ⟨hout, rfl⟩ := err_outS h
      subst hout
      show ErrSim e _
      have herr := (TypeChecker.is_def_eq_core_refines IndAbs.check_fuel_eq hk.1).err st1
        fe_v 0#u64 jvt pc.vg.cv_a.ty e _ hsw1 hfw hjvtw hpc.1.2.2 hdef lst1 lfe_v hsr1 hfr
      simp only [ConLeche.Cached.opB] at herr
      exact ErrSim.trans herr (fun _ hle => run_bind_ok hrunI' (run_bind_err hle))
    | Ok ok1 =>
      obtain ⟨lst2, hrunD, hsr2, hsw2⟩ :=
        (TypeChecker.is_def_eq_core_refines IndAbs.check_fuel_eq hk.1).ok st1 fe_v 0#u64
          jvt pc.vg.cv_a.ty ok1 st2 hsw1 hfw hjvtw hpc.1.2.2 hdef lst1 lfe_v hsr1 hfr
      simp only [ConLeche.Cached.opB] at hrunD
      have hrunD' : ((ConLeche.Cached.coreKnotI (absMode mode) lfe_v
          ConLeche.checkFuel).defeq 0 (absExpr jvt) (absExpr pc.vg.cv_a.ty)).run lst1
          = .ok (ok1, lst2) := hrunD
      cases ok1 with
      | false =>
        -- the cited conversion `throw` (`Installed.lean:252-253`)
        obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hout, -⟩ := err_outS h
        subst hout
        show ErrSim ce _
        exact errSim_invalid hce rfl
          (checkPendingTail_mismatch (pc := absPendingCheck pc) hrunI' hrunD')
      | true =>
        obtain ⟨f, hrt, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hout, rfl⟩ := ok_outS h
        subst hout
        refine ⟨lst2, ?_, hsr2, hsw2, FEnv.restrict_to_refines hfr hrt,
          FEnv.restrict_to_wf hfw hrt⟩
        simp only [absPendingCheck, CheckerSplit.absValueGroup, absConstantVal]
        exact run_bind_ok hrunI' (run_bind_ok hrunD' rfl)

/-- `check_pending_tail_refines` at a success, the pre-#67 statement. -/
theorem check_pending_tail_refines_ok {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {st st' : cached.state_c.CState} {fe_v fe' : fenv.FEnv} {k : Std.U64}
    {pc : parsed_c.PendingCheck} {jv : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe_v) (hpc : PendingCheckWF pc)
    (hjv : ExprWF jv)
    (h : cached.installed.check_pending_tail mode st fe_v k pc jv
          = ok (.Ok fe', st')) :
    ∀ lst lfe_v, StateRel st lst → FEnvRel fe_v lfe_v →
      ∃ lst',
        (do
          let jvt ← (ConLeche.Cached.coreKnotI (absMode mode) lfe_v
            ConLeche.checkFuel).infer 0 (absExpr jv)
          let b ← (ConLeche.Cached.coreKnotI (absMode mode) lfe_v
            ConLeche.checkFuel).defeq 0 jvt (absPendingCheck pc).vg.cvA.type
          if b then pure () else
            throw (ConLeche.CheckError.invalid
              s!"type mismatch in {(absPendingCheck pc).vg.kind.word} {(absPendingCheck pc).vg.cvA.name}")).run lst
          = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st'
        ∧ FEnvRel fe' (lfe_v.restrictTo k.val) ∧ FEnvWF fe' :=
  check_pending_tail_refines hk hsw hfw hpc hjv h

/-- `core_k::lift_fueled`'s `none` arm: the cited `liftFueled`'s own `internal`
`throw` (`ConLeche/Kernel/Core.lean:109-111`), mirrored. -/
private theorem lift_fueled_err {o : Option Bool} {ce : core_types.CheckError}
    (h : core_k.lift_fueled o = ok (.Err ce)) :
    o = none ∧ ∃ v, core_types.internal v = ok ce := by
  cases o with
  | some a => rw [core_k.lift_fueled] at h; simp at h
  | none =>
    rw [core_k.lift_fueled] at h
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce1, hce, h⟩ := bind_eq_ok_iff.mp h
    have hce1 : ce1 = ce := by simpa using Result.ok_injective h
    exact ⟨rfl, v, hce1 ▸ hce⟩

/-- **`installed::check_pending_value` refines `checkPending` past the sort**
(`Installed.lean:239-253`): the cited `let jv ← if pc.vg.kind = .thm then …` —
a theorem's statement must be a proposition and its raw value's guards and
annotation run here, at the view, with no `ienv` value recorded — and then the
tail.

Over the whole outcome (task #67): the port's one `invalid` site
(`cached/installed.rs:599`) is the cited "not a proposition" `throw`, its
`core_k::lift_fueled` failure is the cited `liftFueled`'s `internal` throw, and
the rest is what `annot_val_c` or the tail threw. -/
theorem check_pending_value_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {st st' : cached.state_c.CState} {fe_v : fenv.FEnv} {k : Std.U64}
    {pc : parsed_c.PendingCheck} {u : level.Level}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe_v) (hpc : PendingCheckWF pc)
    (hu : LevelWF u)
    (h : cached.installed.check_pending_value mode st fe_v k pc u = ok (out, st')) :
    ∀ lst lfe_v, StateRel st lst → FEnvRel fe_v lfe_v →
      match out with
      | .Ok fe' =>
        ∃ lst',
          (do
            let jv ←
              if (absPendingCheck pc).vg.kind = ConLeche.ValueKind.thm then do
                let isProp ← ConLeche.liftFueled (m := ConLeche.Cached.CheckCM)
                  "level comparison" (ConLeche.Level.isEquiv (absLevel u) .zero)
                if isProp then
                  ConLeche.Cached.annotValC (absMode mode) lfe_v
                    (absPendingCheck pc).vg.cvA (absPendingCheck pc).vg.cvA.type
                    (absPendingCheck pc).vg.jv false
                else
                  throw (ConLeche.CheckError.invalid
                    s!"type of theorem {(absPendingCheck pc).vg.cvA.name} is not a proposition")
              else pure (absPendingCheck pc).vg.jv
            let jvt ← (ConLeche.Cached.coreKnotI (absMode mode) lfe_v
              ConLeche.checkFuel).infer 0 jv
            let b ← (ConLeche.Cached.coreKnotI (absMode mode) lfe_v
              ConLeche.checkFuel).defeq 0 jvt (absPendingCheck pc).vg.cvA.type
            if b then pure () else
              throw (ConLeche.CheckError.invalid
                s!"type mismatch in {(absPendingCheck pc).vg.kind.word} {(absPendingCheck pc).vg.cvA.name}")).run lst
            = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st'
          ∧ FEnvRel fe' (lfe_v.restrictTo k.val) ∧ FEnvWF fe'
      | .Err e =>
        ErrSim e
          ((do
            let jv ←
              if (absPendingCheck pc).vg.kind = ConLeche.ValueKind.thm then do
                let isProp ← ConLeche.liftFueled (m := ConLeche.Cached.CheckCM)
                  "level comparison" (ConLeche.Level.isEquiv (absLevel u) .zero)
                if isProp then
                  ConLeche.Cached.annotValC (absMode mode) lfe_v
                    (absPendingCheck pc).vg.cvA (absPendingCheck pc).vg.cvA.type
                    (absPendingCheck pc).vg.jv false
                else
                  throw (ConLeche.CheckError.invalid
                    s!"type of theorem {(absPendingCheck pc).vg.cvA.name} is not a proposition")
              else pure (absPendingCheck pc).vg.jv
            let jvt ← (ConLeche.Cached.coreKnotI (absMode mode) lfe_v
              ConLeche.checkFuel).infer 0 jv
            let b ← (ConLeche.Cached.coreKnotI (absMode mode) lfe_v
              ConLeche.checkFuel).defeq 0 jvt (absPendingCheck pc).vg.cvA.type
            if b then pure () else
              throw (ConLeche.CheckError.invalid
                s!"type mismatch in {(absPendingCheck pc).vg.kind.word} {(absPendingCheck pc).vg.cvA.name}")).run lst) := by
  intro lst lfe_v hsr hfr
  rw [cached.installed.check_pending_value] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv := CheckerSplit.is_thm_refines hb
  cases b with
  | false =>
    have hkind : ¬ ((absPendingCheck pc).vg.kind = ConLeche.ValueKind.thm) :=
      of_decide_eq_false hbv.symm
    simp only [Bool.false_eq_true, reduceIte] at h
    obtain ⟨e0, he0, h⟩ := bind_eq_ok_iff.mp h
    have hee : e0 = pc.vg.jv := Expr.dup_eq he0
    subst hee
    have hpure : StateT.run
        (pure (absPendingCheck pc).vg.jv : ConLeche.Cached.CheckCM ConLeche.Expr) lst
        = .ok (absExpr pc.vg.jv, lst) := rfl
    have hrest := check_pending_tail_refines hk hsw hfw hpc hpc.2 h lst lfe_v hsr hfr
    cases out with
    | Ok fe' =>
      obtain ⟨lst', hrunT, hsr', hsw', hfr', hfw'⟩ := hrest
      refine ⟨lst', ?_, hsr', hsw', hfr', hfw'⟩
      rw [if_neg hkind]
      exact run_bind_ok hpure hrunT
    | Err e =>
      show ErrSim e _
      refine ErrSim.trans hrest (fun le hle => ?_)
      rw [if_neg hkind]
      exact run_bind_ok hpure hle
  | true =>
    have hkind : (absPendingCheck pc).vg.kind = ConLeche.ValueKind.thm :=
      of_decide_eq_true hbv.symm
    simp only [reduceIte] at h
    obtain ⟨l, hl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨o, hiseq, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨rr, hlf, h⟩ := bind_eq_ok_iff.mp h
    cases rr with
    | Err e =>
      -- `core_k::lift_fueled` at `none`: the cited `liftFueled`'s own `throw`
      obtain ⟨hon, v, hce⟩ := lift_fueled_err hlf
      have hlift : ConLeche.Level.isEquiv (absLevel u) ConLeche.Level.zero = none := by
        rw [← Level.zero_refines hl, Level.is_equiv_refines hu (Level.zero_wf hl) hiseq]
        exact hon
      obtain ⟨hout, -⟩ := err_outS h
      subst hout
      show ErrSim e _
      have hliftrun : ∃ s, StateT.run (ConLeche.liftFueled
          (m := ConLeche.Cached.CheckCM) "level comparison"
          (ConLeche.Level.isEquiv (absLevel u) ConLeche.Level.zero)) lst
          = .error (.internal s) := by
        rw [hlift]; exact ⟨_, rfl⟩
      obtain ⟨s, hliftrun⟩ := hliftrun
      refine errSim_internal (ls := s) hce rfl ?_
      rw [if_pos hkind]
      exact run_bind_err hliftrun
    | Ok is_prop =>
      have hov : o = some is_prop := by
        cases o with
        | none => exact absurd hlf (by simp [core_k.lift_fueled, bind_eq_ok_iff])
        | some a => rw [core_k.lift_fueled] at hlf; simpa using hlf
      have hlift : ConLeche.Level.isEquiv (absLevel u) ConLeche.Level.zero
          = some is_prop := by
        rw [← Level.zero_refines hl, Level.is_equiv_refines hu (Level.zero_wf hl) hiseq]
        exact hov
      have hliftrun : StateT.run (ConLeche.liftFueled (m := ConLeche.Cached.CheckCM)
          "level comparison"
          (ConLeche.Level.isEquiv (absLevel u) ConLeche.Level.zero)) lst
          = .ok (is_prop, lst) := by
        rw [hlift]; rfl
      cases is_prop with
      | false =>
        -- the cited "not a proposition" `throw` (`Installed.lean:246-247`)
        simp only [Bool.false_eq_true, reduceIte] at h
        obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hout, -⟩ := err_outS h
        subst hout
        show ErrSim ce _
        refine errSim_invalid
          (ls := s!"type of theorem {(absPendingCheck pc).vg.cvA.name} is not a proposition")
          hce rfl ?_
        rw [if_pos hkind]
        refine run_bind_ok hliftrun ?_
        rfl
      | true =>
        simp only [reduceIte] at h
        obtain ⟨q, hval, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r1, st1⟩ := q
        have hvalr := annot_val_c_refines IndAbs.check_fuel_eq hk.1 hsw hfw hpc.1
          hpc.1.2.2 hpc.2 hval lst lfe_v hsr hfr
        cases r1 with
        | Err e =>
          -- the theorem value's install half threw; the cited `do` block passes it on
          obtain ⟨hout, -⟩ := err_outS h
          subst hout
          show ErrSim e _
          refine ErrSim.trans hvalr (fun le hle => ?_)
          rw [if_pos hkind]
          refine run_bind_ok hliftrun ?_
          simp only [if_true]
          exact run_bind_err hle
        | Ok jv0 =>
          obtain ⟨lst1, hrunV, hsr1, hsw1, hjvw⟩ := hvalr
          have hrunV' : StateT.run (ConLeche.Cached.annotValC (absMode mode) lfe_v
              (absPendingCheck pc).vg.cvA (absPendingCheck pc).vg.cvA.type
              (absPendingCheck pc).vg.jv false) lst = .ok (absExpr jv0, lst1) := hrunV
          have hrest := check_pending_tail_refines hk hsw1 hfw hpc hjvw h lst1 lfe_v
            hsr1 hfr
          cases out with
          | Ok fe' =>
            obtain ⟨lst', hrunT, hsr', hsw', hfr', hfw'⟩ := hrest
            refine ⟨lst', ?_, hsr', hsw', hfr', hfw'⟩
            rw [if_pos hkind]
            refine run_bind_ok hliftrun ?_
            simp only [if_true]
            exact run_bind_ok hrunV' hrunT
          | Err e =>
            show ErrSim e _
            refine ErrSim.trans hrest (fun le hle => ?_)
            rw [if_pos hkind]
            refine run_bind_ok hliftrun ?_
            simp only [if_true]
            exact run_bind_ok hrunV' hle

/-- `check_pending_value_refines` at a success, the pre-#67 statement. -/
theorem check_pending_value_refines_ok {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {st st' : cached.state_c.CState} {fe_v fe' : fenv.FEnv} {k : Std.U64}
    {pc : parsed_c.PendingCheck} {u : level.Level}
    (hsw : StateWF st) (hfw : FEnvWF fe_v) (hpc : PendingCheckWF pc)
    (hu : LevelWF u)
    (h : cached.installed.check_pending_value mode st fe_v k pc u
          = ok (.Ok fe', st')) :
    ∀ lst lfe_v, StateRel st lst → FEnvRel fe_v lfe_v →
      ∃ lst',
        (do
          let jv ←
            if (absPendingCheck pc).vg.kind = ConLeche.ValueKind.thm then do
              let isProp ← ConLeche.liftFueled (m := ConLeche.Cached.CheckCM)
                "level comparison" (ConLeche.Level.isEquiv (absLevel u) .zero)
              if isProp then
                ConLeche.Cached.annotValC (absMode mode) lfe_v
                  (absPendingCheck pc).vg.cvA (absPendingCheck pc).vg.cvA.type
                  (absPendingCheck pc).vg.jv false
              else
                throw (ConLeche.CheckError.invalid
                  s!"type of theorem {(absPendingCheck pc).vg.cvA.name} is not a proposition")
            else pure (absPendingCheck pc).vg.jv
          let jvt ← (ConLeche.Cached.coreKnotI (absMode mode) lfe_v
            ConLeche.checkFuel).infer 0 jv
          let b ← (ConLeche.Cached.coreKnotI (absMode mode) lfe_v
            ConLeche.checkFuel).defeq 0 jvt (absPendingCheck pc).vg.cvA.type
          if b then pure () else
            throw (ConLeche.CheckError.invalid
              s!"type mismatch in {(absPendingCheck pc).vg.kind.word} {(absPendingCheck pc).vg.cvA.name}")).run lst
          = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st'
        ∧ FEnvRel fe' (lfe_v.restrictTo k.val) ∧ FEnvWF fe' :=
  check_pending_value_refines hk hsw hfw hpc hu h

/-- **`installed::check_pending` refines `checkPending`**
(`Installed.lean:239-253`): the flush, the prefix view, the header's type's
inference and sort, the value join and the conversion.  The index goes back out
at the bound it came in at, so the returned `FEnv` stands in `FEnvRel` to the
*caller's* index — which is what makes phase B's walk carry one index.

Over the whole outcome (task #67): the flush and the view cannot fail, so every
failure is the header type's inference, its sort, or the value join, and the
cited `do` block passes each on.  The view goes back out at the caller's bound
because `(lfe.restrictTo pc.vis).restrictTo fe.visibleBelow` is `lfe` itself
under `FEnvRel`'s counter clause. -/
theorem check_pending_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {pc : parsed_c.PendingCheck}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hpc : PendingCheckWF pc)
    (h : cached.installed.check_pending mode st fe pc = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lst',
          (ConLeche.Cached.checkPending (absMode mode) lfe (absPendingCheck pc)).run lst
            = .ok ((), lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe ∧ FEnvWF fe'
      | .Err e =>
        ErrSim e
          ((ConLeche.Cached.checkPending (absMode mode) lfe (absPendingCheck pc)).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.installed.check_pending] at h
  obtain ⟨st1, hflush, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hrunf, hrel1, hwf1, -⟩ := StateC.flush_c_refines hsr hsw hflush
  obtain ⟨fe_v, hrt, h⟩ := bind_eq_ok_iff.mp h
  have hfrv : FEnvRel fe_v (lfe.restrictTo pc.vis.val) := FEnv.restrict_to_refines hfr hrt
  have hfwv : FEnvWF fe_v := FEnv.restrict_to_wf hfw hrt
  obtain ⟨q, hinf, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st2⟩ := q
  cases r with
  | Err e =>
    -- the header type's inference threw, and the cited `do` block passes it on
    obtain ⟨hout, rfl⟩ := err_outS h
    subst hout
    show ErrSim e _
    have herr := (TypeChecker.infer_type_core_refines IndAbs.check_fuel_eq hk.1).err st1
      fe_v 0#u64 pc.vg.cv_a.ty e _ hwf1 hfwv hpc.1.2.2 hinf lst.flushed
      (lfe.restrictTo pc.vis.val) hrel1 hfrv
    simp only [ConLeche.Cached.opE] at herr
    have herr' : ErrSim e (((ConLeche.Cached.coreKnotI (absMode mode)
        (lfe.restrictTo (absPendingCheck pc).vis) ConLeche.checkFuel).infer 0
        (absPendingCheck pc).vg.cvA.type).run lst.flushed) := herr
    rw [ConLeche.Cached.checkPending]
    exact ErrSim.trans herr' (fun _ hle => run_bind_ok hrunf (run_bind_err hle))
  | Ok jsty =>
    obtain ⟨lst1, hrunI, hsr1, hsw1, hjstyw⟩ :=
      (TypeChecker.infer_type_core_refines IndAbs.check_fuel_eq hk.1).ok st1 fe_v 0#u64
        pc.vg.cv_a.ty jsty st2 hwf1 hfwv hpc.1.2.2 hinf lst.flushed
        (lfe.restrictTo pc.vis.val) hrel1 hfrv
    simp only [ConLeche.Cached.opE] at hrunI
    have hrunI' : StateT.run ((ConLeche.Cached.coreKnotI (absMode mode)
        (lfe.restrictTo (absPendingCheck pc).vis) ConLeche.checkFuel).infer 0
        (absPendingCheck pc).vg.cvA.type) lst.flushed = .ok (absExpr jsty, lst1) := hrunI
    obtain ⟨q1, hops, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, st3⟩ := q1
    rw [cached.parsed_c.op_s_ix_c] at hops
    cases r1 with
    | Err e =>
      -- the sort check threw, and the cited `do` block passes it on
      obtain ⟨hout, rfl⟩ := err_outS h
      subst hout
      show ErrSim e _
      have herr := (TypeChecker.ensure_sort_core_refines IndAbs.check_fuel_eq hk.1).err st2
        fe_v 0#u64 jsty e _ hsw1 hfwv hjstyw hops lst1 (lfe.restrictTo pc.vis.val)
        hsr1 hfrv
      simp only [ConLeche.Cached.opS] at herr
      have herr' : ErrSim e ((ConLeche.Cached.opSIxC (absMode mode)
          (lfe.restrictTo (absPendingCheck pc).vis) 0 (absExpr jsty)).run lst1) := herr
      rw [ConLeche.Cached.checkPending]
      exact ErrSim.trans herr'
        (fun _ hle => run_bind_ok hrunf (run_bind_ok hrunI' (run_bind_err hle)))
    | Ok u =>
      obtain ⟨lst2, hrunS, hsr2, hsw2, huw⟩ :=
        (TypeChecker.ensure_sort_core_refines IndAbs.check_fuel_eq hk.1).ok st2 fe_v 0#u64
          jsty u st3 hsw1 hfwv hjstyw hops lst1 (lfe.restrictTo pc.vis.val) hsr1 hfrv
      simp only [ConLeche.Cached.opS] at hrunS
      have hrunS' : StateT.run (ConLeche.Cached.opSIxC (absMode mode)
          (lfe.restrictTo (absPendingCheck pc).vis) 0 (absExpr jsty)) lst1
          = .ok (absLevel u, lst2) := hrunS
      have hrest := check_pending_value_refines hk hsw2 hfwv hpc huw h lst2
        (lfe.restrictTo pc.vis.val) hsr2 hfrv
      cases out with
      | Ok fe' =>
        obtain ⟨lst', hrunV, hsr', hsw', hfr', hfw'⟩ := hrest
        have hX : (lfe.restrictTo pc.vis.val).restrictTo fe.visible_below.val = lfe := by
          simp [ConLeche.FEnv.restrictTo, hfr.2.1]
        rw [hX] at hfr'
        refine ⟨lst', ?_, hsr', hsw', hfr', hfw'⟩
        rw [ConLeche.Cached.checkPending]
        exact run_bind_ok hrunf (run_bind_ok hrunI' (run_bind_ok hrunS' hrunV))
      | Err e =>
        show ErrSim e _
        rw [ConLeche.Cached.checkPending]
        exact ErrSim.trans hrest
          (fun _ hle => run_bind_ok hrunf (run_bind_ok hrunI' (run_bind_ok hrunS' hle)))

/-- `check_pending_refines` at a success, the pre-#67 statement. -/
theorem check_pending_refines_ok {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {pc : parsed_c.PendingCheck}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hpc : PendingCheckWF pc)
    (h : cached.installed.check_pending mode st fe pc = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (ConLeche.Cached.checkPending (absMode mode) lfe (absPendingCheck pc)).run lst
          = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe ∧ FEnvWF fe' :=
  check_pending_refines hk hsw hfw hpc h

/-- **`installed::check_pending_fresh` refines the cited `checkPending mode fe
pc {}`** (`Installed.lean:398-403`): one record's check **from its own fresh
`CState`**, so no memo crosses from one record's check to the next.  The port
makes it a function of its own so that the state is dropped when it returns,
which is the cited `{}`'s lifetime exactly (task #32); no memo *policy* moves,
and `Refine/State.lean`'s `cstate_new_refines` is what says the port's fourteen
fresh tables are con-leche's `{}`. -/
theorem check_pending_fresh_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {fe : fenv.FEnv} {pc : parsed_c.PendingCheck}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hfw : FEnvWF fe) (hpc : PendingCheckWF pc)
    (h : cached.installed.check_pending_fresh mode fe pc = ok out) :
    ∀ lfe, FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        (∃ lst', ConLeche.Cached.checkPending (absMode mode) lfe (absPendingCheck pc) {}
            = .ok ((), lst'))
        ∧ FEnvRel fe' lfe ∧ FEnvWF fe'
      | .Err e =>
        ErrSim e
          (ConLeche.Cached.checkPending (absMode mode) lfe (absPendingCheck pc) {}) := by
  intro lfe hfr
  rw [cached.installed.check_pending_fresh] at h
  obtain ⟨st, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hsr0, hsw0⟩ := State.cstate_new_refines hnew
  obtain ⟨q, hrun, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  have hrest :=
    check_pending_refines hk hsw0 hfw hpc hrun ({} : ConLeche.Cached.CState) lfe hsr0 hfr
  cases r with
  | Ok fe' =>
    have hout := ok_out h
    subst hout
    obtain ⟨lst', hrunl, -, -, hfr', hfw'⟩ := hrest
    exact ⟨⟨lst', hrunl⟩, hfr', hfw'⟩
  | Err e =>
    have hout := err_out h
    subst hout
    exact hrest

/-- `check_pending_fresh_refines` at a success, the pre-#67 statement. -/
theorem check_pending_fresh_refines_ok {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {fe fe' : fenv.FEnv} {pc : parsed_c.PendingCheck}
    (hfw : FEnvWF fe) (hpc : PendingCheckWF pc)
    (h : cached.installed.check_pending_fresh mode fe pc = ok (.Ok fe')) :
    ∀ lfe, FEnvRel fe lfe →
      (∃ lst', ConLeche.Cached.checkPending (absMode mode) lfe (absPendingCheck pc) {}
          = .ok ((), lst'))
      ∧ FEnvRel fe' lfe ∧ FEnvWF fe' :=
  check_pending_fresh_refines hk hfw hpc h

open ConLeche.Cached in
/-- `checkPendingList` at a record whose check threw: the error, **tagged with
the record's fold position** (`ConLeche/Cached/Installed.lean:398-403`). -/
private theorem checkPendingList_cons_err {mode : ConLeche.CheckMode}
    {lfe : ConLeche.FEnv} {pc : ConLeche.Cached.PendingCheck}
    {rest : List ConLeche.Cached.PendingCheck} {le : ConLeche.CheckError}
    (h : checkPending mode lfe pc {} = .error le) :
    checkPendingList mode lfe (pc :: rest) = .error (le, pc.pos) := by
  rw [ConLeche.Cached.checkPendingList, h]

open ConLeche.Cached in
/-- `checkPendingList` at a record whose check succeeded: the walk of the rest. -/
private theorem checkPendingList_cons_ok {mode : ConLeche.CheckMode}
    {lfe : ConLeche.FEnv} {pc : ConLeche.Cached.PendingCheck}
    {rest : List ConLeche.Cached.PendingCheck} {lst' : CState}
    (h : checkPending mode lfe pc {} = .ok ((), lst')) :
    checkPendingList mode lfe (pc :: rest) = checkPendingList mode lfe rest := by
  rw [ConLeche.Cached.checkPendingList, h]

/-- The phase-B walk with an explicit bound to recurse on.  The cited
`checkPendingList` recurses on the `List`; the port recurses on the index
(deviation 3), so the statement is about `(absPendingChecks pend).drop i.val`
and the bridge is the standard `length - i` induction.

Over the whole outcome (task #67): the port's answer is `CheckError × U64` —
the error with the failing record's fold position — so the claim is
`ErrSimPos`, and both sides read the position off the same record. -/
theorem check_pending_list_val {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {pend : alloc.vec.Vec parsed_c.PendingCheck} (hpe : PendingChecksWF pend)
    (n : Nat) :
    ∀ (fe : fenv.FEnv) (i : Std.Usize)
      (out : core.result.Result fenv.FEnv (core_types.CheckError × Std.U64)),
      pend.val.length - i.val ≤ n → FEnvWF fe →
      cached.installed.check_pending_list_from mode fe pend i = ok out →
      ∀ lfe, FEnvRel fe lfe →
        match out with
        | .Ok fe' =>
          ConLeche.Cached.checkPendingList (absMode mode) lfe
              ((absPendingChecks pend).drop i.val) = .ok ()
          ∧ FEnvRel fe' lfe ∧ FEnvWF fe'
        | .Err e =>
          ErrSimPos e (ConLeche.Cached.checkPendingList (absMode mode) lfe
            ((absPendingChecks pend).drop i.val)) := by
  induction n with
  | zero =>
    intro fe i out hb hfw h lfe hfr
    rw [cached.installed.check_pending_list_from] at h
    rw [if_pos (show i >= alloc.vec.Vec.len pend by
      have := alloc.vec.Vec.len_val pend; scalar_tac)] at h
    have hbs : out = .Ok fe := (Result.ok_injective h).symm
    subst hbs
    refine ⟨?_, hfr, hfw⟩
    rw [List.drop_eq_nil_of_le (by simp [absPendingChecks]; omega)]
    rfl
  | succ n ih =>
    intro fe i out hb hfw h lfe hfr
    rw [cached.installed.check_pending_list_from] at h
    by_cases hge : i.val >= pend.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len pend by
        have := alloc.vec.Vec.len_val pend; scalar_tac)] at h
      have hbs : out = .Ok fe := (Result.ok_injective h).symm
      subst hbs
      refine ⟨?_, hfr, hfw⟩
      rw [List.drop_eq_nil_of_le (by simp [absPendingChecks]; omega)]
      rfl
    · rw [if_neg (show ¬ (i >= alloc.vec.Vec.len pend) by
        have := alloc.vec.Vec.len_val pend; scalar_tac)] at h
      obtain ⟨pc, hpci, h⟩ := bind_eq_ok_iff.mp h
      have hmem : pc ∈ pend.val := List.mem_of_getElem? (ExprOps.vec_index_getElem? hpci)
      obtain ⟨r, hfresh, h⟩ := bind_eq_ok_iff.mp h
      have hlen : i.val < (absPendingChecks pend).length := by
        simp [absPendingChecks]; omega
      have hdrop : (absPendingChecks pend).drop i.val
          = absPendingCheck pc :: (absPendingChecks pend).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlen]
        congr 1
        have h1 : pend.val[i.val]? = some pc := ExprOps.vec_index_getElem? hpci
        have h2 : (absPendingChecks pend)[i.val]? = some (absPendingCheck pc) := by
          rw [absPendingChecks, List.getElem?_map, h1]; rfl
        rw [List.getElem?_eq_getElem hlen] at h2
        exact Option.some_inj.mp h2
      have hone := check_pending_fresh_refines hk hfw (hpe pc hmem) hfresh lfe hfr
      cases r with
      | Err ce =>
        -- the record's check threw; the cited walk stops, tagged with `pc.pos`
        have hout : out = .Err (ce, pc.pos) := (Result.ok_injective h).symm
        subst hout
        show ErrSimPos (ce, pc.pos) _
        rw [hdrop]
        exact ErrSimPos.tag hone (fun _ hle => checkPendingList_cons_err hle)
      | Ok fe1 =>
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := by
          have he := Std.UScalar.add_equiv i 1#usize
          rw [hi2] at he
          simpa using he.2.1
        obtain ⟨⟨lst', hrunl⟩, hfr1, hfw1⟩ := hone
        have hrec := ih fe1 i2 out (by omega) hfw1 h lfe hfr1
        rw [hi2v] at hrec
        cases out with
        | Ok fe' =>
          obtain ⟨hwalk, hfr', hfw'⟩ := hrec
          refine ⟨?_, hfr', hfw'⟩
          rw [hdrop, checkPendingList_cons_ok hrunl, hwalk]
        | Err e =>
          show ErrSimPos e _
          rw [hdrop]
          exact ErrSimPos.trans hrec
            (fun _ hle => by rw [checkPendingList_cons_ok hrunl, hle])

/-- **`installed::check_pending_list_from` refines the cited walk's tail**
(`Installed.lean:398-403`): the records from position `i` all check. -/
theorem check_pending_list_from_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {fe : fenv.FEnv} {pend : alloc.vec.Vec parsed_c.PendingCheck}
    {i : Std.Usize}
    {out : core.result.Result fenv.FEnv (core_types.CheckError × Std.U64)}
    (hfw : FEnvWF fe) (hpe : PendingChecksWF pend)
    (h : cached.installed.check_pending_list_from mode fe pend i = ok out) :
    ∀ lfe, FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ConLeche.Cached.checkPendingList (absMode mode) lfe
            ((absPendingChecks pend).drop i.val) = .ok ()
        ∧ FEnvRel fe' lfe ∧ FEnvWF fe'
      | .Err e =>
        ErrSimPos e (ConLeche.Cached.checkPendingList (absMode mode) lfe
          ((absPendingChecks pend).drop i.val)) := by
  intro lfe hfr
  cases out with
  | Ok fe' =>
    exact check_pending_list_val hk hpe pend.val.length fe i (.Ok fe') (by omega) hfw h
      lfe hfr
  | Err e =>
    exact check_pending_list_val hk hpe pend.val.length fe i (.Err e) (by omega) hfw h
      lfe hfr

/-- `check_pending_list_from_refines` at a success, the pre-#67 statement. -/
theorem check_pending_list_from_refines_ok {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {fe fe' : fenv.FEnv} {pend : alloc.vec.Vec parsed_c.PendingCheck}
    {i : Std.Usize} (hfw : FEnvWF fe) (hpe : PendingChecksWF pend)
    (h : cached.installed.check_pending_list_from mode fe pend i = ok (.Ok fe')) :
    ∀ lfe, FEnvRel fe lfe →
      ConLeche.Cached.checkPendingList (absMode mode) lfe
          ((absPendingChecks pend).drop i.val) = .ok ()
      ∧ FEnvRel fe' lfe ∧ FEnvWF fe' :=
  check_pending_list_from_refines hk hfw hpe h

/-- **`installed::check_pending_list` refines `checkPendingList`**
(`Installed.lean:398-403`): phase B as a pure walk, every record checked from a
fresh memo state, a failure tagged with the record's fold position. -/
theorem check_pending_list_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {fe : fenv.FEnv} {pend : alloc.vec.Vec parsed_c.PendingCheck}
    {out : core.result.Result fenv.FEnv (core_types.CheckError × Std.U64)}
    (hfw : FEnvWF fe) (hpe : PendingChecksWF pend)
    (h : cached.installed.check_pending_list mode fe pend = ok out) :
    ∀ lfe, FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ConLeche.Cached.checkPendingList (absMode mode) lfe (absPendingChecks pend)
            = .ok ()
        ∧ FEnvRel fe' lfe ∧ FEnvWF fe'
      | .Err e =>
        ErrSimPos e
          (ConLeche.Cached.checkPendingList (absMode mode) lfe
            (absPendingChecks pend)) := by
  intro lfe hfr
  rw [cached.installed.check_pending_list] at h
  have hrest := check_pending_list_from_refines hk hfw hpe h lfe hfr
  rw [show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero] at hrest
  cases out with
  | Ok fe' => exact hrest
  | Err e => exact hrest

/-- `check_pending_list_refines` at a success, the pre-#67 statement. -/
theorem check_pending_list_refines_ok {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {fe fe' : fenv.FEnv} {pend : alloc.vec.Vec parsed_c.PendingCheck}
    (hfw : FEnvWF fe) (hpe : PendingChecksWF pend)
    (h : cached.installed.check_pending_list mode fe pend = ok (.Ok fe')) :
    ∀ lfe, FEnvRel fe lfe →
      ConLeche.Cached.checkPendingList (absMode mode) lfe (absPendingChecks pend)
          = .ok ()
      ∧ FEnvRel fe' lfe ∧ FEnvWF fe' :=
  check_pending_list_refines hk hfw hpe h

/-- `fenv::mk_fenv` builds an **unrestricted** view: its counter is the one
`mkFEnvGo` hands out last, which is the constant count (`FEnv.mkFEnvGo_fst`).
This is `FEnv.mk_fenv_canon`'s missing half — together they discharge the
canonical pair at the one place `installed::check_decls` builds an index. -/
theorem mk_fenv_full {e : env.Env} {fe : fenv.FEnv} (he : EnvWF e)
    (h : fenv.mk_fenv e = ok fe) : FEnvFull fe := by
  obtain ⟨hrel, -⟩ := FEnv.mk_fenv_refines he h
  have henv : fe.env = e := by
    rw [fenv.mk_fenv] at h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    rw [← Result.ok_injective h]
  unfold FEnvFull
  rw [henv, hrel.2.1]
  show (ConLeche.mkFEnvGo (absEnv e).consts).1 = e.consts.val.length
  rw [FEnv.mkFEnvGo_fst]
  simp [absEnv, absConstantInfos]

/-! ## The fold

`checkDecls` (`Installed.lean:407-411`) is phase A's `List.foldlM` from
`(0, mkFEnv Env.empty, #[])` and a fresh `CState`, then phase B, then the
index's environment.  The port's phase A is the same fold as an index recursion
(deviation 3) threading the accumulator by value. -/

/-- Phase A's fold with an explicit bound to recurse on. -/
theorem annot_decl_fold_val {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {ds : alloc.vec.Vec parsed_c.DeclC} (hds : ∀ d ∈ ds.val, DeclCWF d) (n : Nat) :
    ∀ (st st' : cached.state_c.CState)
      (p : Std.U64 × fenv.FEnv × alloc.vec.Vec parsed_c.PendingCheck)
      (i : Std.Usize)
      (out : core.result.Result
        (Std.U64 × fenv.FEnv × alloc.vec.Vec parsed_c.PendingCheck)
        (core_types.CheckError × Std.U64)),
      ds.val.length - i.val ≤ n → StateWF st → FEnvWF p.2.1 →
      FEnvCanon p.2.1 → FEnvFull p.2.1 → PendingChecksWF p.2.2 →
      cached.installed.annot_decl_fold_from mode pins st p ds i = ok (out, st') →
      ∀ lst lfe, StateRel st lst → FEnvRel p.2.1 lfe →
        match out with
        | .Ok q =>
          ∃ lst' lfe',
            (((ds.val.drop i.val).map absDeclC).foldlM
                (ConLeche.Cached.annotDeclStep (absMode mode) (absPins pins))
                (p.1.val, lfe, (absPendingChecks p.2.2).toArray)) lst
              = .ok ((q.1.val, lfe', (absPendingChecks q.2.2).toArray), lst')
            ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel q.2.1 lfe' ∧ FEnvWF q.2.1
            ∧ PendingChecksWF q.2.2 ∧ FEnvCanon q.2.1 ∧ FEnvFull q.2.1
        | .Err e =>
          ErrSimPos e
            ((((ds.val.drop i.val).map absDeclC).foldlM
                (ConLeche.Cached.annotDeclStep (absMode mode) (absPins pins))
                (p.1.val, lfe, (absPendingChecks p.2.2).toArray)) lst) := by
  induction n with
  | zero =>
    intro st st' p i out hb hsw hfw hcan hfull hpe h lst lfe hsr hfr
    rw [cached.installed.annot_decl_fold_from] at h
    rw [if_pos (show i >= alloc.vec.Vec.len ds by
      have := alloc.vec.Vec.len_val ds; scalar_tac)] at h
    obtain ⟨hout, rfl⟩ := ok_outS h
    subst hout
    refine ⟨lst, lfe, ?_, hsr, hsw, hfr, hfw, hpe, hcan, hfull⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ n ih =>
    intro st st' p i out hb hsw hfw hcan hfull hpe h lst lfe hsr hfr
    rw [cached.installed.annot_decl_fold_from] at h
    by_cases hge : i.val >= ds.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len ds by
        have := alloc.vec.Vec.len_val ds; scalar_tac)] at h
      obtain ⟨hout, rfl⟩ := ok_outS h
      subst hout
      refine ⟨lst, lfe, ?_, hsr, hsw, hfr, hfw, hpe, hcan, hfull⟩
      rw [List.drop_eq_nil_of_le (by omega)]
      rfl
    · rw [if_neg (show ¬ (i >= alloc.vec.Vec.len ds) by
        have := alloc.vec.Vec.len_val ds; scalar_tac)] at h
      obtain ⟨d, hdi, h⟩ := bind_eq_ok_iff.mp h
      have hmem : d ∈ ds.val := List.mem_of_getElem? (ExprOps.vec_index_getElem? hdi)
      obtain ⟨r, hstep, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨res, st1⟩ := r
      have hlen : i.val < ds.val.length := by omega
      have hdrop : ds.val.drop i.val = d :: ds.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlen]
        congr 1
        have h1 : ds.val[i.val]? = some d := ExprOps.vec_index_getElem? hdi
        rw [List.getElem?_eq_getElem hlen] at h1
        exact Option.some_inj.mp h1
      have hstepr := annot_decl_step_refines hk hind hinde hvar hsw hfw hcan hfull
        (hds d hmem) hpe hstep lst lfe hsr hfr
      cases res with
      | Err e =>
        -- the step threw; the cited `foldlM` stops there, tag and all
        obtain ⟨hout, rfl⟩ := err_outS h
        subst hout
        show ErrSimPos e _
        rw [hdrop, List.map_cons, List.foldlM_cons]
        exact ErrSimPos.trans hstepr (fun _ hle => run_bind_err hle)
      | Ok p1 =>
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := by
          have he := Std.UScalar.add_equiv i 1#usize
          rw [hi2] at he
          simpa using he.2.1
        obtain ⟨lst1, lfe1, hrun1, hsr1, hsw1, hfr1, hfw1, hpe1, hcan1, hfull1⟩ := hstepr
        have hrec := ih st1 st' p1 i2 out (by omega) hsw1 hfw1 hcan1 hfull1 hpe1 h lst1
          lfe1 hsr1 hfr1
        rw [hi2v] at hrec
        cases out with
        | Ok q =>
          obtain ⟨lst', lfe', hfold, rest⟩ := hrec
          refine ⟨lst', lfe', ?_, rest⟩
          rw [hdrop, List.map_cons, List.foldlM_cons]
          exact run_bind_ok hrun1 hfold
        | Err e =>
          show ErrSimPos e _
          rw [hdrop, List.map_cons, List.foldlM_cons]
          exact ErrSimPos.trans hrec (fun _ hle => run_bind_ok hrun1 hle)

/-- **`installed::annot_decl_fold_from` refines the cited fold's tail**
(`Installed.lean:407-411`): the records from position `i` take the accumulator
where the port says. -/
theorem annot_decl_fold_from_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {st st' : cached.state_c.CState}
    {p : Std.U64 × fenv.FEnv × alloc.vec.Vec parsed_c.PendingCheck}
    {ds : alloc.vec.Vec parsed_c.DeclC} {i : Std.Usize}
    {out : core.result.Result
      (Std.U64 × fenv.FEnv × alloc.vec.Vec parsed_c.PendingCheck)
      (core_types.CheckError × Std.U64)}
    (hsw : StateWF st) (hfw : FEnvWF p.2.1) (hcan : FEnvCanon p.2.1)
    (hfull : FEnvFull p.2.1) (hpe : PendingChecksWF p.2.2)
    (hds : ∀ d ∈ ds.val, DeclCWF d)
    (h : cached.installed.annot_decl_fold_from mode pins st p ds i = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel p.2.1 lfe →
      match out with
      | .Ok q =>
        ∃ lst' lfe',
          (((ds.val.drop i.val).map absDeclC).foldlM
              (ConLeche.Cached.annotDeclStep (absMode mode) (absPins pins))
              (p.1.val, lfe, (absPendingChecks p.2.2).toArray)) lst
            = .ok ((q.1.val, lfe', (absPendingChecks q.2.2).toArray), lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel q.2.1 lfe' ∧ FEnvWF q.2.1
          ∧ PendingChecksWF q.2.2 ∧ FEnvCanon q.2.1 ∧ FEnvFull q.2.1
      | .Err e =>
        ErrSimPos e
          ((((ds.val.drop i.val).map absDeclC).foldlM
              (ConLeche.Cached.annotDeclStep (absMode mode) (absPins pins))
              (p.1.val, lfe, (absPendingChecks p.2.2).toArray)) lst) := by
  intro lst lfe hsr hfr
  cases out with
  | Ok q =>
    exact annot_decl_fold_val hk hind hinde hvar hds ds.val.length st st' p i
      (.Ok q) (by omega) hsw hfw hcan hfull hpe h lst lfe hsr hfr
  | Err e =>
    exact annot_decl_fold_val hk hind hinde hvar hds ds.val.length st st' p i
      (.Err e) (by omega) hsw hfw hcan hfull hpe h lst lfe hsr hfr

/-- `annot_decl_fold_from_refines` at a success, the pre-#67 statement. -/
theorem annot_decl_fold_from_refines_ok {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {st st' : cached.state_c.CState}
    {p q : Std.U64 × fenv.FEnv × alloc.vec.Vec parsed_c.PendingCheck}
    {ds : alloc.vec.Vec parsed_c.DeclC} {i : Std.Usize}
    (hsw : StateWF st) (hfw : FEnvWF p.2.1) (hcan : FEnvCanon p.2.1)
    (hfull : FEnvFull p.2.1) (hpe : PendingChecksWF p.2.2)
    (hds : ∀ d ∈ ds.val, DeclCWF d)
    (h : cached.installed.annot_decl_fold_from mode pins st p ds i = ok (.Ok q, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel p.2.1 lfe →
      ∃ lst' lfe',
        (((ds.val.drop i.val).map absDeclC).foldlM
            (ConLeche.Cached.annotDeclStep (absMode mode) (absPins pins))
            (p.1.val, lfe, (absPendingChecks p.2.2).toArray)) lst
          = .ok ((q.1.val, lfe', (absPendingChecks q.2.2).toArray), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel q.2.1 lfe' ∧ FEnvWF q.2.1
        ∧ PendingChecksWF q.2.2 ∧ FEnvCanon q.2.1 ∧ FEnvFull q.2.1 :=
  annot_decl_fold_from_refines hk hind hinde hvar hsw hfw hcan hfull hpe hds h

/-- **`installed::check_decls_phase_b` refines the cited
`checkPendingList mode p.2.1 p.2.2.toList; pure p.2.1.env`**
(`Installed.lean:407-411`).

Over the whole outcome (task #67): the walk is the only thing that can fail
here, and the cited `do` block passes its verdict — error *and* fold position —
straight out. -/
theorem check_decls_phase_b_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {fe : fenv.FEnv} {pend : alloc.vec.Vec parsed_c.PendingCheck}
    {out : core.result.Result env.Env (core_types.CheckError × Std.U64)}
    (hfw : FEnvWF fe) (hpe : PendingChecksWF pend)
    (h : cached.installed.check_decls_phase_b mode fe pend = ok out) :
    ∀ lfe, FEnvRel fe lfe →
      match out with
      | .Ok e =>
        (do
          ConLeche.Cached.checkPendingList (absMode mode) lfe
            (absPendingChecks pend).toArray.toList
          pure lfe.env : Except (ConLeche.CheckError × Nat) ConLeche.Env)
          = .ok (absEnv e)
      | .Err er =>
        ErrSimPos er
          (do
            ConLeche.Cached.checkPendingList (absMode mode) lfe
              (absPendingChecks pend).toArray.toList
            pure lfe.env : Except (ConLeche.CheckError × Nat) ConLeche.Env) := by
  intro lfe hfr
  rw [cached.installed.check_decls_phase_b] at h
  obtain ⟨r, hlist, h⟩ := bind_eq_ok_iff.mp h
  have hrest := check_pending_list_refines hk hfw hpe hlist lfe hfr
  cases r with
  | Ok fe2 =>
    have hout := ok_out h
    subst hout
    obtain ⟨hwalk, hfr2, -⟩ := hrest
    show (do
        ConLeche.Cached.checkPendingList (absMode mode) lfe
          (absPendingChecks pend).toArray.toList
        pure lfe.env : Except (ConLeche.CheckError × Nat) ConLeche.Env)
        = .ok (absEnv fe2.env)
    rw [List.toList_toArray, hwalk, hfr2.1]
    rfl
  | Err er =>
    have hout := err_out h
    subst hout
    show ErrSimPos er _
    rw [List.toList_toArray]
    exact ErrSimPos.trans hrest (fun _ hle => by rw [hle]; rfl)

/-- `check_decls_phase_b_refines` at a success, the pre-#67 statement. -/
theorem check_decls_phase_b_refines_ok {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {fe : fenv.FEnv} {pend : alloc.vec.Vec parsed_c.PendingCheck} {e : env.Env}
    (hfw : FEnvWF fe) (hpe : PendingChecksWF pend)
    (h : cached.installed.check_decls_phase_b mode fe pend = ok (.Ok e)) :
    ∀ lfe, FEnvRel fe lfe →
      (do
        ConLeche.Cached.checkPendingList (absMode mode) lfe
          (absPendingChecks pend).toArray.toList
        pure lfe.env : Except (ConLeche.CheckError × Nat) ConLeche.Env)
        = .ok (absEnv e) :=
  check_decls_phase_b_refines hk hfw hpe h

/-! ## `check_decls`, and the pin parameter

`leanCheckDecls` is con-leche's fold with the pin list as the parameter the
upstream ask of DESIGN.md §3.6 made it.  **The ask landed** (con-leche task
#285, vendored at task #74): `checkDecls mode ds pins` is the real signature,
with `pins` defaulting to `natOpPinSets`, so this abbreviation now *applies*
the list instead of ignoring it and `hpins` is gone from every statement in
this file and in `Refine/Main.lean`. -/

/-- con-leche's declaration fold, with the pin list as a parameter. -/
def leanCheckDecls (mode : ConLeche.CheckMode)
    (pins : List ConLeche.NatOpPinSet) (ds : List ConLeche.Cached.DeclC) :
    Except (ConLeche.CheckError × Nat) ConLeche.Env :=
  ConLeche.Cached.checkDecls mode ds pins

/-- **`installed::check_decls` refines `checkDecls`** (`Installed.lean:407-411`)
— DESIGN.md §1's `check_decls_refines`, at the shape the rest of the tower
consumes: **whatever the Rust checker answers, con-leche's fold answers** — the
same environment on an accept, and on a mirrored reject the same kind at the
same declaration (`ErrSimPos`).

The hypotheses the tier still owes are the module note's: `hk` (task #55),
`hind`/`hinde` (task #59, the inductive routes' two halves) and `hvar` (the pin
argument's well-formedness).  The fold is **parametric in the pins** since task
#74, so there is no hypothesis about their *value*.  `hds` is the
well-formedness of the parsed input, which the parser establishes and which no
lemma below can invent. -/
theorem check_decls_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {ds : alloc.vec.Vec parsed_c.DeclC}
    {out : core.result.Result env.Env (core_types.CheckError × Std.U64)}
    (hds : ∀ d ∈ ds.val, DeclCWF d)
    (h : cached.installed.check_decls mode pins ds = ok out) :
    match out with
    | .Ok e =>
      leanCheckDecls (absMode mode) (absPins pins) (ds.val.map absDeclC)
        = .ok (absEnv e)
    | .Err er =>
      ErrSimPos er
        (leanCheckDecls (absMode mode) (absPins pins) (ds.val.map absDeclC)) := by
  rw [cached.installed.check_decls] at h
  obtain ⟨st0, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hsr0, hsw0⟩ := State.cstate_new_refines hnew
  obtain ⟨e0, he0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨fe0, hfe0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hrel0, hwf0⟩ := FEnv.mk_fenv_refines (Env.empty_wf he0) hfe0
  rw [Env.empty_refines he0] at hrel0
  obtain ⟨r, hfold, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨res, st1⟩ := r
  have hpempty : absPendingChecks (alloc.vec.Vec.new parsed_c.PendingCheck) = [] := by
    simp [absPendingChecks]
  have hfoldr :=
    annot_decl_fold_from_refines (p := (0#u64, fe0,
        alloc.vec.Vec.new parsed_c.PendingCheck)) hk hind hinde hvar hsw0 hwf0
      (FEnv.mk_fenv_canon (Env.empty_wf he0) hfe0)
      (mk_fenv_full (Env.empty_wf he0) hfe0)
      (by intro pc hpc; simp at hpc) hds hfold
      ({} : ConLeche.Cached.CState) (ConLeche.mkFEnv ConLeche.Env.empty) hsr0 hrel0
  cases res with
  | Err er =>
    -- phase A threw at some declaration; the cited fold stops there, tag and all
    have hout := err_out h
    subst hout
    show ErrSimPos er _
    have hfold2 : ErrSimPos er
        (((ds.val.map absDeclC).foldlM
            (ConLeche.Cached.annotDeclStep (absMode mode) (absPins pins))
            (0, ConLeche.mkFEnv ConLeche.Env.empty, #[]))
          ({} : ConLeche.Cached.CState)) := by
      simpa [hpempty] using hfoldr
    rw [leanCheckDecls, ConLeche.Cached.checkDecls]
    exact ErrSimPos.trans hfold2 (fun _ hle => by rw [hle]; rfl)
  | Ok p =>
    obtain ⟨n0, fe1, pend1⟩ := p
    obtain ⟨lst', lfe', hrunfold, -, -, hfr1, hfw1, hpe1, -, -⟩ := hfoldr
    have hphase : cached.installed.check_decls_phase_b mode fe1 pend1 = ok out := by
      simpa using h
    have hrun2 := check_decls_phase_b_refines hk hfw1 hpe1 hphase lfe' hfr1
    have hfold2 : ((ds.val.map absDeclC).foldlM
        (ConLeche.Cached.annotDeclStep (absMode mode) (absPins pins))
        (0, ConLeche.mkFEnv ConLeche.Env.empty, #[]))
          ({} : ConLeche.Cached.CState)
        = .ok ((n0.val, lfe', (absPendingChecks pend1).toArray), lst') := by
      simpa [hpempty] using hrunfold
    cases out with
    | Ok e =>
      show leanCheckDecls (absMode mode) (absPins pins) (ds.val.map absDeclC)
        = .ok (absEnv e)
      rw [leanCheckDecls, ConLeche.Cached.checkDecls, hfold2]
      exact hrun2
    | Err er =>
      show ErrSimPos er
        (leanCheckDecls (absMode mode) (absPins pins) (ds.val.map absDeclC))
      rw [leanCheckDecls, ConLeche.Cached.checkDecls, hfold2]
      exact hrun2

/-- `check_decls_refines` at a success, the pre-#67 statement — DESIGN.md §1's
"whatever the Rust checker accepts, con-leche's fold accepts, with the same
environment". -/
theorem check_decls_refines_ok {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclCWF d)
    (h : cached.installed.check_decls mode pins ds = ok (.Ok e)) :
    leanCheckDecls (absMode mode) (absPins pins) (ds.val.map absDeclC)
      = .ok (absEnv e) :=
  check_decls_refines hk hind hinde hvar hds h

/-! ## No instance at the binary's own pins is needed any more (task #74)

Task #64 appended `check_decls_embedded_refines` here: `check_decls_refines`
with `hpins : absPins pins = ConLeche.natOpPinSets` discharged by
`Refine/Pins.lean`'s `check_decls_pins_refines`, so that the corollary spoke
about the pin list `con_ron::driver::pins_for_run` actually passes.  It existed
only to feed `pins_closed`'s `native_decide`, and the pins-parametric fold
retires it: `check_decls_refines` is *already* the statement at the list the
binary threads, whatever that list is, so there is nothing left to identify
with a constant and nothing native-decide-shaped in this file's closure.
`Refine/Main.lean`'s `conron.*_embedded` corollaries now go through the general
pair directly, and carry `hp : decode_embedded = ok (.Ok pins)` only to get
`hvar` out of `PinsWF.decode_embedded_wf`. -/

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

While the tier below is open the capstone's census carries `sorryAx`, and it is
machine-checked: `sorryAx` leaving this line is the gate that says the port's
`check_decls` refines con-leche's, modulo the three named hypotheses.

**Task #62 closed this file's own nine** (`annotConstantValC`, `annotValC` and
their two tails, `annotValueC` and its tail, `checkPending` and its two halves),
so *nothing in `Installed.lean` is a `sorry` any more*: the whole of phase A's
install half (`annot_value_c_refines`) and the whole of phase B
(`check_decls_phase_b_refines`, through `check_pending_fresh` and the two
`checkPending` halves) census at the three standard axioms.  The one door the
`sorryAx` still came in by — `annot_step_other_c_refines` →
`Refine/CheckerDecl.lean`'s `check_decl_step_c_refines` — **closed at task
#58**, and the two `#guard_msgs` below were pinned with `sorryAx` precisely so
that they would fail the moment it did.  They did; this is the corrected
census, and `check_decls_refines` now depends on exactly the three standard
axioms.  What it still depends on is *hypotheses*, which are not axioms:
`hk` (task #55's knot, discharged at #61), `hind`/`hinde` (task #57's routes,
both halves since task #67), and task #58's `hvar` — the pin argument's
well-formedness.  Task #58's `hoe` is gone: task #65 made a thrown pin attempt
the check's verdict, which retires both halves of task #24's `orElse`
deviation; and task #64's `hpins` is gone too, retired by task #74's parametric
fold.

**Task #67** restated every `*_refines` here over the Rust computation's whole
inner outcome: the accept halves are the ones task #62 proved, word for word,
and beside each is the failure half, which for this file is always one of two
moves — a bind whose callee threw (`run_bind_err`, `ErrSim.bindCM`,
`ErrSim.trans`, `ErrSimPos.trans`) or one of the tier's own mirrored `throw`s.
Every statement has an `*_ok` corollary at the verbatim pre-#67 shape, so no
call site outside is forced to change. -/

/-- info: 'ConRon.Refine.Installed.check_decls_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_decls_refines

/-- info: 'ConRon.Refine.Installed.annot_step_c_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms annot_step_c_refines

/-- info: 'ConRon.Refine.Installed.annot_value_c_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms annot_value_c_refines

/-- info: 'ConRon.Refine.Installed.check_pending_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_pending_refines

/-- info: 'ConRon.Refine.Installed.check_decls_phase_b_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_decls_phase_b_refines

/-- info: 'ConRon.Refine.Installed.annot_step_defn_c_push_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms annot_step_defn_c_push_refines

/-- info: 'ConRon.Refine.Installed.annot_step_opaque_c_push_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms annot_step_opaque_c_push_refines

end ConRon.Refine.Installed

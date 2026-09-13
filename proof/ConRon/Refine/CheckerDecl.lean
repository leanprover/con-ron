import ConRon.Refine.TypeChecker
import ConRon.Refine.CheckerC
import ConRon.Refine.IndSpec
import ConRon.Refine.Pins
import ConRon.Refine.Checker
import ConRon.Refine.BasisTables
import ConRon.Refine.BasisPins
import ConRon.Refine.StateC
import ConRon.Refine.ExprOps
import ConRon.Refine.ExprOpsCGuards
import ConRon.Refine.CheckerBase
import ConRon.Refine.CheckerPins
import ConRon.Refine.StdAxioms
import ConRon.Refine.TrustAxioms
import ConRon.Refine.DeclCheck
import ConRon.Refine.StateCResolve
import ConLeche.Cached.ParsedC
import ConLeche.Verify.Cached.KnotCongr
import ConLeche.Verify.EnvBound
import ConLeche.Verify.CheckerF

/-! # The `Declaration` level: `check_decl`, `check_decl_c`, the fold (task #56)

`CORE_PLAN.md` step 7's top: `kernel/checker.rs`'s `checkDecl` dispatch
(`ConLeche/Kernel/Checker.lean:419-562`) and `cached/parsed_c.rs`'s
`checkDeclC`/`checkDeclStepC` (`ConLeche/Cached/ParsedC.lean:158-241`,
`:259-262`), plus the `checkDeclsPure` fold (`Checker.lean:564-567`).

The arms' own lemmas live in `Refine/Checker.lean` (the value checks,
`installBasisDecl`, `certifyNatEqs`) and `Refine/CheckerPins.lean` (the
`Nat.div`/`Nat.mod` pin loop) — the same task's files.  This file is the
dispatch, the fold, and the two arms whose content is settled: the
basis-table install (task #22's table, proved) and the inductive routes (task
#57's, composed through `IndRoutesSpec`).

## The `.indDecl` arm is where the two tasks meet

`check_ind_decl_c` is `indParamsOk` and then a two-way dispatch on the
recogniser; both routes are task #57's.  `Refine/IndSpec.lean`'s
`IndRoutesSpec` is the minimal Prop that task owes, and
`check_ind_decl_c_refines` below **composes** them: it is proved, taking
`IndRoutesSpec mode` as a named hypothesis, so when task #57 lands there is
nothing left to do at this seam.  The `Expr`-level twin
(`kernel::checker::check_ind_decl`) needs no such hypothesis: task #24 left it
declining past the parameter check, and a Rust function that never returns
`.Ok` refines everything vacuously (§3.5) — `check_ind_decl_refines` records
that, and records that it is a *decline*, never an accept.

## The canonical-index pair rides through the parsed tier (task #59)

`Refine/IndSpec.lean`'s `IndRoutesSpec` carries `FEnv.FEnvCanon`/`FEnv.FEnvFull`
of the index it is handed — both inductive routes open by *rebuilding* the
index with `fenv::dup`, and the clause is false for an index that is not its
own environment's rebuild (that file's header has the argument).  So
`check_ind_decl_c_refines`, `check_decl_c_refines` and
`check_decl_step_c_refines` take the pair, and they **hand it back** with the
answer, because `cached::installed`'s phase A is a fold that feeds one step's
index into the next.  Every arm that installs is a `fenv::push`
(`FEnv.push_canon`), the basis fold below included; the pair is discharged
where the index is *built*, at `installed::check_decls`' `fenv::mk_fenv`
(`FEnv.mk_fenv_canon` and `Installed.mk_fenv_full`).

## Two environments, one index — why the generic `checkDecl` is still the target

`checkDecl` holds `env` (pre-insertion) and `env2` (extended) at once; the port
threads one index at two *bounds* (task #24's note "The pre-insertion
environment is a visibility bound, not a value").  That is sound at the
`Declaration` level because the only function the pre-insertion *value* is
handed to is `certifyNatEqs ops env`, and every slot of `sharedOpsC` ignores its
`Env` argument (`Refine/TypeChecker.lean`'s five `sharedOpsC_*` `rfl`s): the
guards that do read an environment (`natOpGuard`, `env2.find?`,
`divModEnvGuard`, `reduceStoredOk`) read the *extended* one, which is the
index's own.  So the statements below put `lfe.env` where the Lean wants the
pre-insertion environment and `Refine/Checker.lean`'s `certify_nat_eqs_refines`
is stated at an arbitrary `Env` argument, which is what discharges it.

`checkDecl` returns an `Env`; the port returns an `FEnv`.  Its output is stated
as `lfe'.env` for an index `lfe'` the port's `fe'` stands in `FEnvRel` to —
which is the form the fold consumes.

## One hypothesis the `Expr`-level statements gained (task #58)

`checkDecl` reads an **`Env`** and the port reads the **index**, whose `find?`
is bounded by `visibleBelow`; the two agree only when the index hides nothing
and indexes its own environment.  That is `Indexed` below, and the six
`Expr`-level statements now carry it.  It is not slack — see the section note
at `Indexed`: without it the port accepts a duplicate declaration the Lean
rejects, so the statements were false as they stood.  The cached tier needs
nothing of the kind (`checkDeclC` is index-based throughout).  `Indexed` is
re-established at every arm and every fold step, and `check_decls_pure_refines`
starts from `mkFEnv Env.empty`, so no caller supplies it by hand.

## The `.defnDecl` arms' three threaded hypotheses

`Refine/CheckerPins.lean`'s pin gate has three caller obligations and this file
is the caller, so the six statements that thread `pins` carry them: `hvar :
PinsWF pins` (the argument's own well-formedness, the analogue of `hd :
DeclarationWF d`), `hpins : absPins pins = natOpPinSets` — **needed**: the
cited `checkDecl` reads the *global* `natOpPinSets`, so an arbitrary `pins`
argument lets the port accept a `Nat.div` spelling the Lean declines (DESIGN.md
§3.6, task #31's deviation).  Neither is derivable from `Core.Wrappers`, which
is the `ok`-direction only.  A third, `DivModOrElse mode` — tasks #24/#58's two
halves of the `orElse` deviation — travelled here until **task #65** made a
thrown attempt the pin check's verdict; see `Refine/CheckerC.lean`'s module
note.

## The full outcome (task #67, DESIGN.md §3's ruling of 2026-09-13)

Every `*_refines` below is stated over the port's **whole** inner outcome
(`Refine/README.md`, "the full-outcome convention"): `.Ok` is the
pre-#67 claim unchanged, and `.Err` is `ErrSim` — con-leche throws at the same
kind, messages never compared.  Each converted lemma keeps a `*_refines_ok`
corollary with its pre-#67 statement, so a call site that knows its callee
succeeded reads as it did.

`cached/parsed_c.rs`, `kernel/checker_base.rs` and all of `kernel/checker.rs`
but one site are mirrored, so the failure halves are *proved*.  The one
exception is the checker tier's single `Native` (DESIGN.md task #67 §1):
`kernel::checker::check_ind_decl`'s stub past the parameter check — task #24
left the `Expr`-level routes unported, so the port declines where con-leche
*dispatches*, and `check_decl_refines`'s `.indDecl` arm discharges it with
`ErrSim.native`, which claims nothing.  Its sibling, the parameter-count
mismatch, is the cited arm's own `throw` and is proved.

The `.indDecl` arm needs one more named hypothesis for its failure half:
`Refine/IndSpec.lean`'s `IndRoutesSpecErr mode`, the `.Err` sibling of
`IndRoutesSpec` (what the two inductive routes *throw*, as opposed to what they
accept).  It sits immediately after `hind` in `check_ind_decl_c_refines`,
`check_decl_c_refines` and `check_decl_step_c_refines`, and is discharged from
the knot at `Refine/Main.lean` exactly as `hind` is.

The fold has no single computation for `ErrSim` to point at — the operation
record is rebuilt at every step (section note below) — so `FoldsTo` gained a
failure twin, `FoldsErr`, and `FoldErrSim` is `ErrSim` over it.

## `sorry` count in this file: 0.

Everything in the file depends on `propext`, `Classical.choice` and
`Quot.sound` only; the census at the end pins the three entry points.
-/
open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel ConRon.Generated.cached
open ConRon.Refine ConRon.Refine.State ConRon.Refine.FEnv

namespace ConRon.Refine.CheckerDecl

/-! ## `DeclC`

The port's `cached::parsed_c::DeclC` and con-leche's `ConLeche.Cached.DeclC`
are the same six-constructor inductive (`ExprC = Expr` since con-leche's task
#172 B3a, so the parsed records carry plain `Expr`s), in a different
constructor order.  `absDeclC` is the map; `DeclCWF` its hereditary invariant.
**To be unified into `Abs.lean`** beside `absDeclaration`. -/

/-- A parsed declaration of the model as `ConLeche.Cached.DeclC`
(`ConLeche/Cached/ParsedC.lean:55-62`). -/
def absDeclC : parsed_c.DeclC → ConLeche.Cached.DeclC
  | .AxiomDecl cv => .axiomDecl (absConstantVal cv)
  | .DefnDecl cv v h => .defnDecl (absConstantVal cv) (absExpr v) (absHint h)
  | .ThmDecl cv v => .thmDecl (absConstantVal cv) (absExpr v)
  | .OpaqueDecl cv v => .opaqueDecl (absConstantVal cv) (absExpr v)
  | .BasisDecl k => .basisDecl (absBasisKind k)
  | .IndDecl block n_p => .indDecl (absConstantInfos block) n_p.val

/-- The hereditary invariant of a parsed declaration. -/
def DeclCWF : parsed_c.DeclC → Prop
  | .AxiomDecl cv => ConstantValWF cv
  | .DefnDecl cv v _ => ConstantValWF cv ∧ ExprWF v
  | .ThmDecl cv v => ConstantValWF cv ∧ ExprWF v
  | .OpaqueDecl cv v => ConstantValWF cv ∧ ExprWF v
  | .BasisDecl _ => True
  | .IndDecl block _ => ConstantInfosWF block

/-! ## The failure half's vocabulary (task #67)

Every `*_refines` below is stated over the port's **whole** inner outcome
(`Refine/README.md`, "the full-outcome convention"), so each one carries an
`.Err` arm.  Three of the four moves that close those arms need a little
vocabulary: the inversions of the three `core_types` error constructors — the
port's error came out of `core_types::invalid`, so its kind *is* con-leche's
`.invalid` — and con-leche's `throw` on its **applied** form, because the
plumbing `simp` set unfolds `StateT.run`/`Except.bind` but carries no
`MonadExcept` instance.  `Refine/CheckerBase.lean` has the same five as
`private`; these are this file's copies. -/

/-- `core_types::not_implemented` is the constructor. -/
private theorem not_implemented_val {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.not_implemented v = ok ce) :
    ce = .NotImplemented v := by
  rw [core_types.not_implemented] at h; exact (Result.ok_injective h).symm

/-- `core_types::invalid` is the constructor. -/
private theorem invalid_val {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.invalid v = ok ce) :
    ce = .Invalid v := by
  rw [core_types.invalid] at h; exact (Result.ok_injective h).symm

/-- `core_types::internal` is the constructor. -/
private theorem internal_val {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.internal v = ok ce) :
    ce = .Internal v := by
  rw [core_types.internal] at h; exact (Result.ok_injective h).symm

/-- `core_types::native` is the constructor — the port's own failure, which
`ErrSim` claims nothing about. -/
private theorem native_val {v : alloc.vec.Vec Std.U32}
    {ce : core_types.CheckError} (h : core_types.native v = ok ce) :
    ce = .Native v := by
  rw [core_types.native] at h; exact (Result.ok_injective h).symm

/-- A mirrored `throw` at `notImplemented`: the port's error came out of
`core_types::not_implemented`, and the cited side has been rewritten down to
its own `throw`. -/
private theorem errSim_notImplemented {γ : Type} {v : alloc.vec.Vec Std.U32}
    {ce ce1 : core_types.CheckError} {x : Except ConLeche.CheckError γ} {ls : String}
    (hce : core_types.not_implemented v = ok ce1) (heq : ce1 = ce)
    (hx : x = .error (.notImplemented ls)) : ErrSim ce x := by
  rw [← heq, not_implemented_val hce]; exact ErrSim.notImplemented hx

/-- A mirrored `throw` at `invalid`, the same bookkeeping. -/
private theorem errSim_invalid {γ : Type} {v : alloc.vec.Vec Std.U32}
    {ce ce1 : core_types.CheckError} {x : Except ConLeche.CheckError γ} {ls : String}
    (hce : core_types.invalid v = ok ce1) (heq : ce1 = ce)
    (hx : x = .error (.invalid ls)) : ErrSim ce x := by
  rw [← heq, invalid_val hce]; exact ErrSim.invalid hx

/-- A mirrored `throw` at `internal`, the same bookkeeping. -/
private theorem errSim_internal {γ : Type} {v : alloc.vec.Vec Std.U32}
    {ce ce1 : core_types.CheckError} {x : Except ConLeche.CheckError γ} {ls : String}
    (hce : core_types.internal v = ok ce1) (heq : ce1 = ce)
    (hx : x = .error (.internal ls)) : ErrSim ce x := by
  rw [← heq, internal_val hce]; exact ErrSim.internal hx

/-- The port's `Err` return, read off (the state-carrying shape). -/
private theorem err_outS {α : Type} {ce : core_types.CheckError}
    {st1 st' : cached.state_c.CState}
    {out : core.result.Result α core_types.CheckError}
    (h : (ok (core.result.Result.Err ce, st1) :
      Result ((core.result.Result α core_types.CheckError) × cached.state_c.CState))
      = ok (out, st')) : out = .Err ce ∧ st' = st1 := by
  have h1 := Result.ok_injective h
  exact ⟨(congrArg Prod.fst h1).symm, (congrArg Prod.snd h1).symm⟩

/-- The port's `Ok` return, read off (the state-carrying shape). -/
private theorem ok_outS {α : Type} {r : α} {st1 st' : cached.state_c.CState}
    {out : core.result.Result α core_types.CheckError}
    (h : (ok (core.result.Result.Ok r, st1) :
      Result ((core.result.Result α core_types.CheckError) × cached.state_c.CState))
      = ok (out, st')) : out = .Ok r ∧ st' = st1 := by
  have h1 := Result.ok_injective h
  exact ⟨(congrArg Prod.fst h1).symm, (congrArg Prod.snd h1).symm⟩

/-- The port's `Err` return, read off (the stateless shape). -/
private theorem err_out {α : Type} {ce : core_types.CheckError}
    {out : core.result.Result α core_types.CheckError}
    (h : (ok (core.result.Result.Err ce) :
      Result (core.result.Result α core_types.CheckError)) = ok out) :
    out = .Err ce := (Result.ok_injective h).symm

/-! ## The `.indDecl` arm, both spellings

The seam with task #57.  The cached one is proved from `IndRoutesSpec`; the
`Expr`-level one is vacuous because task #24 left the routes unported there. -/

/-- **`cached::parsed_c::check_ind_decl_c` refines `checkDeclC`'s `.indDecl`
arm** (`ConLeche/Cached/ParsedC.lean:238-241`): the stream's *declared*
parameter count first and for both routes (con-leche task #228), then the
one-route dispatch by the recogniser alone (task #210/#219).  Proved, with
task #57's `IndRoutesSpec` as a named hypothesis: `Refine/Env.lean`'s
`ind_params_ok_refines` gives the gate, and `IndRoutesSpec`'s two clauses give
the recogniser's verdict *and* the chosen route together.

**`hcan`/`hfull` are not slack** (task #59).  `IndRoutesSpec`'s two clauses
carry them, because `native_install::check_native_pass_former` and
`inductives_c::check_ind_recs_s` copy the index with `fenv::dup`, which
*rebuilds* it from the environment; `Refine/IndSpec.lean`'s header spells out
why the clause is false for an index that is not its own environment's rebuild.
They come back out with the answer, which is what `cached::installed`'s
declaration fold needs, and they are discharged where the index is *built* —
`FEnv.mk_fenv_canon` at `installed::check_decls`, `FEnv.push_canon` at every
step in between. -/
theorem check_ind_decl_c_refines {mode : env.CheckMode} (hind : IndRoutesSpec mode)
    (hinde : IndRoutesSpecErr mode)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {block : alloc.vec.Vec env.ConstantInfo} {n_p : Std.U64}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hb : ConstantInfosWF block)
    (h : cached.parsed_c.check_ind_decl_c mode st fe block n_p = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (ConLeche.Cached.checkDeclC (absMode mode) lfe
              (.indDecl (absConstantInfos block) n_p.val)).run lst
            = Except.ok (lfe', lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
      | .Err e =>
        ErrSim e ((ConLeche.Cached.checkDeclC (absMode mode) lfe
          (.indDecl (absConstantInfos block) n_p.val)).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.parsed_c.check_ind_decl_c] at h
  obtain ⟨b, hb', h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = ConLeche.indParamsOk n_p.val (absConstantInfos block) :=
    Env.ind_params_ok_refines hb hb'
  cases b with
  | false =>
    -- the parameter gate declined: the cited arm's own `throw`
    -- (`ConLeche/Cached/ParsedC.lean:241`)
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim ce _
    refine errSim_invalid (ls := "number of parameters mismatch") hce rfl ?_
    rw [ConLeche.Cached.checkDeclC]
    simp only [← hbv, Bool.false_eq_true, if_false]
    rfl
  | true =>
    simp only [if_pos] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | none =>
      cases out with
      | Ok fe' =>
        obtain ⟨lst', lfe', hnp, hrun, hrest⟩ :=
          hind.modeled st fe n_p block fe' st' hsw hfw hcan hfull hb ho h lst lfe hsr hfr
        refine ⟨lst', lfe', ?_, hrest⟩
        rw [ConLeche.Cached.checkDeclC]
        simp only [← hbv, if_pos, hnp]
        exact hrun
      | Err e =>
        obtain ⟨hnp, herr⟩ :=
          hinde.modeled st fe n_p block e st' hsw hfw hcan hfull hb ho h lst lfe hsr hfr
        show ErrSim e _
        rw [ConLeche.Cached.checkDeclC]
        simp only [← hbv, if_pos, hnp]
        exact herr
    | some p =>
      cases out with
      | Ok fe' =>
        obtain ⟨lst', lfe', lp, hnp, hrun, hrest⟩ :=
          hind.native st fe n_p block p fe' st' hsw hfw hcan hfull hb ho h lst lfe hsr hfr
        refine ⟨lst', lfe', ?_, hrest⟩
        rw [ConLeche.Cached.checkDeclC]
        simp only [← hbv, if_pos, hnp]
        exact hrun
      | Err e =>
        obtain ⟨lp, hnp, herr⟩ :=
          hinde.native st fe n_p block p e st' hsw hfw hcan hfull hb ho h lst lfe hsr hfr
        show ErrSim e _
        rw [ConLeche.Cached.checkDeclC]
        simp only [← hbv, if_pos, hnp]
        exact herr

/-- `check_ind_decl_c_refines` at a success, the pre-#67 statement. -/
theorem check_ind_decl_c_refines_ok {mode : env.CheckMode} (hind : IndRoutesSpec mode)
    (hinde : IndRoutesSpecErr mode)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {block : alloc.vec.Vec env.ConstantInfo} {n_p : Std.U64}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hb : ConstantInfosWF block)
    (h : cached.parsed_c.check_ind_decl_c mode st fe block n_p = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkDeclC (absMode mode) lfe
            (.indDecl (absConstantInfos block) n_p.val)).run lst = Except.ok (lfe', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  check_ind_decl_c_refines hind hinde hsw hfw hcan hfull hb h

/-- **`kernel::checker::check_ind_decl` declines past the parameter check**
(task #24's third stub): `indParamsOk` runs first and for both routes, and the
dispatch — `nativeParts?`, `checkNative`, `checkModeled` — is
`ConLeche/Kernel/Inductives/*`, which the `Expr`-level lane does not port.  So
the function never returns `.Ok`, and its refinement against `checkDecl`'s
`.indDecl` arm holds vacuously; what the lemma records is that it can only make
the Rust **reject**, which is the sound direction (DESIGN.md §1). -/
theorem check_ind_decl_declines {mode : env.CheckMode} {st st' : cached.state_c.CState}
    {fe fe' : fenv.FEnv} {block : alloc.vec.Vec env.ConstantInfo} {n_p : Std.U64} :
    kernel.checker.check_ind_decl mode st fe block n_p ≠ ok (.Ok fe', st') := by
  intro h
  rw [kernel.checker.check_ind_decl] at h
  obtain ⟨b, -, h⟩ := bind_eq_ok_iff.mp h
  cases b <;> simp at h

/-! ## The basis-table install

`checkDecl`'s and `checkDeclC`'s `.basisDecl` arms both end in
`kind.declsA.foldlM installBasisDecl(F)`; the port folds
`basis_tables::basis_decls_a(kind)` by index (task #14's point 7).  Task #22's
`Refine/BasisTables.lean` is what says the generated table **is**
`BasisKind.declsA` (`absBasisDecls_eq`), and `Refine/Checker.lean`'s
`install_basis_decl_refines` is one step.  Neither the fold nor a step touches
the `CState`, which is why the state comes out unchanged. -/

open ConLeche.Cached in
/-- `installBasisDeclF`'s duplicate `throw` (`ConLeche/Kernel/DeclCheck.lean:855-859`)
is the same error in both monads.  `Refine/Checker.lean` states the port's step
against the **`CheckM`** spelling (`installBasisDecl` has no state), and the fold
below runs at `CheckCM`; this is the transport between them, the `hxy` of an
`ErrSim.trans`. -/
private theorem installBasisDeclF_errC {lfe : ConLeche.FEnv}
    {ci : ConLeche.ConstantInfo} {lst : CState} {le : ConLeche.CheckError}
    (h : ConLeche.installBasisDeclF (m := ConLeche.CheckM) lfe ci = .error le) :
    (ConLeche.installBasisDeclF (m := CheckCM) lfe ci).run lst = .error le := by
  rw [ConLeche.installBasisDeclF] at h
  rw [ConLeche.installBasisDeclF]
  by_cases hf : (lfe.find? ci.name).isNone = true
  · simp only [hf, if_pos, Pure.pure, Except.pure] at h
    exact absurd h (by simp)
  · simp only [Bool.not_eq_true] at hf
    rw [hf] at h ⊢
    simp only [Bool.false_eq_true, if_false] at h ⊢
    have hle : le = ConLeche.CheckError.invalid
        (toString "duplicate declaration " ++ toString ci.name) :=
      Except.error.inj
        (show (Except.error le : Except ConLeche.CheckError ConLeche.FEnv) = _ from h.symm)
    rw [hle]
    rfl

/-- The index fold, with an explicit bound to recurse on, over the whole
outcome.  The port's one `invalid` site in a step is `install_basis_decl`'s
duplicate check (`kernel/checker.rs:110`), which is the cited
`installBasisDeclF`'s own `throw`; the fold itself constructs no error.  The
**unrestricted-canonical pair** rides along (task #59): each step is one
`fenv::push`, so `FEnv.push_canon` carries it, and the checker tier's
declaration fold needs it back out (`Refine/IndSpec.lean`'s header). -/
theorem install_basis_decls_from (n : Nat) :
    ∀ (fe : fenv.FEnv)
      (out : core.result.Result fenv.FEnv core_types.CheckError)
      (decls : alloc.vec.Vec env.ConstantInfo) (i : Std.Usize),
      decls.val.length - i.val ≤ n → FEnvWF fe → FEnv.FEnvCanon fe →
      FEnv.FEnvFull fe → ConstantInfosWF decls →
      kernel.checker.install_basis_decls fe decls i = ok out →
      ∀ lfe (lst : ConLeche.Cached.CState), FEnvRel fe lfe →
        match out with
        | .Ok fe' =>
          ∃ lfe₂,
            (((absConstantInfos decls).drop i.val).foldlM
                (ConLeche.installBasisDeclF (m := ConLeche.Cached.CheckCM)) lfe).run lst
              = .ok (lfe₂, lst)
            ∧ FEnvRel fe' lfe₂ ∧ FEnvWF fe'
            ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
        | .Err e =>
          ErrSim e ((((absConstantInfos decls).drop i.val).foldlM
              (ConLeche.installBasisDeclF (m := ConLeche.Cached.CheckCM)) lfe).run lst) := by
  induction n with
  | zero =>
    intro fe out decls i hb hfw hcan hfull hd h lfe lst hfr
    rw [kernel.checker.install_basis_decls] at h
    rw [if_pos (show i >= alloc.vec.Vec.len decls by
      have := alloc.vec.Vec.len_val decls; scalar_tac)] at h
    have hout : out = .Ok fe := by simpa using h.symm
    subst hout
    refine ⟨lfe, ?_, hfr, hfw, hcan, hfull⟩
    rw [List.drop_eq_nil_of_le (by
      simp only [absConstantInfos, List.length_map]; omega)]
    rfl
  | succ n ih =>
    intro fe out decls i hb hfw hcan hfull hd h lfe lst hfr
    rw [kernel.checker.install_basis_decls] at h
    by_cases hge : i.val >= decls.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len decls by
        have := alloc.vec.Vec.len_val decls; scalar_tac)] at h
      have hout : out = .Ok fe := by simpa using h.symm
      subst hout
      refine ⟨lfe, ?_, hfr, hfw, hcan, hfull⟩
      rw [List.drop_eq_nil_of_le (by
        simp only [absConstantInfos, List.length_map]; omega)]
      rfl
    · rw [if_neg (show ¬ (i >= alloc.vec.Vec.len decls) by
        have := alloc.vec.Vec.len_val decls; scalar_tac)] at h
      obtain ⟨ci, hci, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ci1, hdup, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, hins, h⟩ := bind_eq_ok_iff.mp h
      have hcieq : ci1 = ci := Env.constant_info_dup_refines hdup
      subst hcieq
      have hmem : ci1 ∈ decls.val := by
        have := ExprOps.vec_index_getElem? hci
        exact List.mem_of_getElem? this
      have hciwf : ConstantInfoWF ci1 := hd ci1 hmem
      -- the list step: `drop i` is `absConstantInfo ci1 :: drop (i+1)`, shared
      -- by both arms
      have hget : (absConstantInfos decls)[i.val]? = some (absConstantInfo ci1) := by
        simp only [absConstantInfos, List.getElem?_map, ExprOps.vec_index_getElem? hci]
        rfl
      have hlen : i.val < (absConstantInfos decls).length := by
        simp only [absConstantInfos, List.length_map]; omega
      have hdrop : (absConstantInfos decls).drop i.val
          = absConstantInfo ci1 :: (absConstantInfos decls).drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlen]
        congr 1
        have h1 : (absConstantInfos decls)[i.val]? = some (absConstantInfo ci1) := hget
        rw [List.getElem?_eq_getElem hlen] at h1
        exact Option.some_inj.mp h1
      cases r with
      | Err e =>
        -- the step threw: `install_basis_decl`'s duplicate check, which is the
        -- cited `installBasisDeclF`'s own `throw`
        have hout : out = .Err e := by simpa using h.symm
        subst hout
        have herr := Checker.install_basis_decl_refines hfw hciwf hcan hfull hins lfe hfr
        show ErrSim e _
        rw [hdrop, List.foldlM_cons]
        exact ErrSim.bindCM (ErrSim.trans herr (fun _ hle => installBasisDeclF_errC hle))
      | Ok fe2 =>
        obtain ⟨hrel2, hwf2, hnone, hcan2, hfull2⟩ :=
          Checker.install_basis_decl_refines hfw hciwf hcan hfull hins lfe hfr
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := by
          have he := Std.UScalar.add_equiv i 1#usize
          rw [hi2] at he
          simpa using he.2.1
        have hrec :=
          ih fe2 out decls i2 (by omega) hwf2 hcan2 hfull2 hd h
            (lfe.push (absConstantInfo ci1)) lst hrel2
        rw [hi2v] at hrec
        have hstep : (ConLeche.installBasisDeclF (m := ConLeche.Cached.CheckCM) lfe
            (absConstantInfo ci1)) = pure (lfe.push (absConstantInfo ci1)) := by
          rw [ConLeche.installBasisDeclF]
          simp [hnone]
        cases out with
        | Ok fe' =>
          obtain ⟨lfe₂, hfold, hrel', hwf', hcan', hfull'⟩ := hrec
          refine ⟨lfe₂, ?_, hrel', hwf', hcan', hfull'⟩
          rw [hdrop, List.foldlM_cons, hstep]
          simpa using hfold
        | Err e =>
          show ErrSim e _
          rw [hdrop, List.foldlM_cons, hstep]
          simpa using hrec

/-- `install_basis_decls_from` at a success, the pre-#67 statement. -/
theorem install_basis_decls_from_ok (n : Nat) :
    ∀ (fe fe' : fenv.FEnv) (decls : alloc.vec.Vec env.ConstantInfo) (i : Std.Usize),
      decls.val.length - i.val ≤ n → FEnvWF fe → FEnv.FEnvCanon fe →
      FEnv.FEnvFull fe → ConstantInfosWF decls →
      kernel.checker.install_basis_decls fe decls i = ok (.Ok fe') →
      ∀ lfe (lst : ConLeche.Cached.CState), FEnvRel fe lfe →
        ∃ lfe₂,
          (((absConstantInfos decls).drop i.val).foldlM
              (ConLeche.installBasisDeclF (m := ConLeche.Cached.CheckCM)) lfe).run lst
            = .ok (lfe₂, lst)
          ∧ FEnvRel fe' lfe₂ ∧ FEnvWF fe'
          ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  fun fe fe' decls i hb hfw hcan hfull hd h =>
    install_basis_decls_from n fe (.Ok fe') decls i hb hfw hcan hfull hd h

/-- **`checker::install_basis_decls` refines `kind.declsA.foldlM
installBasisDeclF`**, the whole table over the whole outcome: the fold from
index 0. -/
theorem install_basis_decls_refines {fe : fenv.FEnv}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    {decls : alloc.vec.Vec env.ConstantInfo}
    (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe) (hfull : FEnv.FEnvFull fe)
    (hd : ConstantInfosWF decls)
    (h : kernel.checker.install_basis_decls fe decls 0#usize = ok out) :
    ∀ lfe (lst : ConLeche.Cached.CState), FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lfe₂,
          ((absConstantInfos decls).foldlM
              (ConLeche.installBasisDeclF (m := ConLeche.Cached.CheckCM)) lfe).run lst
            = Except.ok (lfe₂, lst)
          ∧ FEnvRel fe' lfe₂ ∧ FEnvWF fe'
          ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
      | .Err e =>
        ErrSim e (((absConstantInfos decls).foldlM
            (ConLeche.installBasisDeclF (m := ConLeche.Cached.CheckCM)) lfe).run lst) := by
  intro lfe lst hfr
  have hrun :=
    install_basis_decls_from decls.val.length fe out decls 0#usize (by simp) hfw hcan
      hfull hd h lfe lst hfr
  rw [show ((0#usize : Std.Usize)).val = 0 from rfl, List.drop_zero] at hrun
  cases out with
  | Ok fe' => exact hrun
  | Err e => exact hrun

/-- `install_basis_decls_refines` at a success, the pre-#67 statement. -/
theorem install_basis_decls_refines_ok {fe fe' : fenv.FEnv}
    {decls : alloc.vec.Vec env.ConstantInfo}
    (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe) (hfull : FEnv.FEnvFull fe)
    (hd : ConstantInfosWF decls)
    (h : kernel.checker.install_basis_decls fe decls 0#usize = ok (.Ok fe')) :
    ∀ lfe (lst : ConLeche.Cached.CState), FEnvRel fe lfe →
      ∃ lfe₂,
        ((absConstantInfos decls).foldlM
            (ConLeche.installBasisDeclF (m := ConLeche.Cached.CheckCM)) lfe).run lst
          = .ok (lfe₂, lst)
        ∧ FEnvRel fe' lfe₂ ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  install_basis_decls_refines hfw hcan hfull hd h

/-- **`cached::parsed_c::check_basis_decl_c` refines `checkDeclC`'s
`.basisDecl` arm** (`ConLeche/Cached/ParsedC.lean:233-237`): the quotient
block requires the pinned `Eq` basis, and then the block is installed, one
duplicate-checked constant at a time.  Proved, and it is task #22's table
that makes it possible: `Refine/BasisTables.lean`'s `absBasisDecls_eq` says
the generated `basis_decls_a` **is** `BasisKind.declsA`, and
`Refine/BasisPins.lean`'s `eq_basis_pinned_refines` is the quotient gate
exactly.  The table's `ConstantInfosWF` is `Refine/BasisPins.lean`'s
`basis_decls_a_wf`, used here rather than re-derived.

Over the whole outcome (task #67): the port's own `not_implemented` site
(`kernel/checker.rs:1571`) is the quotient gate, which is the cited arm's own
`throw`; every other failure is one the install fold passed on. -/
theorem check_basis_decl_c_refines {mode : env.CheckMode} {fe : fenv.FEnv}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    {kind : env.BasisKind} (hfw : FEnvWF fe)
    (hcan : FEnv.FEnvCanon fe) (hfull : FEnv.FEnvFull fe)
    (h : cached.parsed_c.check_basis_decl_c fe kind = ok out) :
    ∀ lst lfe, FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lfe',
          (ConLeche.Cached.checkDeclC (absMode mode) lfe
              (.basisDecl (absBasisKind kind))).run lst = Except.ok (lfe', lst)
          ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
      | .Err e =>
        ErrSim e ((ConLeche.Cached.checkDeclC (absMode mode) lfe
            (.basisDecl (absBasisKind kind))).run lst) := by
  intro lst lfe hfr
  rw [cached.parsed_c.check_basis_decl_c, kernel.checker.check_basis_decl.eq_def] at h
  rw [ConLeche.Cached.checkDeclC]
  -- the install, shared by all six arms
  have install : ∀ (v : alloc.vec.Vec env.ConstantInfo)
      (o : core.result.Result fenv.FEnv core_types.CheckError),
      basis_tables.basis_decls_a kind = ok v →
      kernel.checker.install_basis_decls fe v 0#usize = ok o →
      match o with
      | .Ok fe' =>
        ∃ lfe₂,
          ((ConLeche.BasisKind.declsA (absBasisKind kind)).foldlM
              (ConLeche.installBasisDeclF (m := ConLeche.Cached.CheckCM)) lfe).run lst
            = Except.ok (lfe₂, lst)
          ∧ FEnvRel fe' lfe₂ ∧ FEnvWF fe'
          ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
      | .Err e =>
        ErrSim e (((ConLeche.BasisKind.declsA (absBasisKind kind)).foldlM
            (ConLeche.installBasisDeclF (m := ConLeche.Cached.CheckCM)) lfe).run lst) := by
    intro v o hv hi
    have habs : absConstantInfos v = ConLeche.BasisKind.declsA (absBasisKind kind) := by
      have := ConRon.Refine.absBasisDecls_eq kind
      rw [ConRon.Refine.absBasisDecls, hv] at this
      simpa using this
    have hr :=
      install_basis_decls_refines hfw hcan hfull (BasisPins.basis_decls_a_wf hv) hi
        lfe lst hfr
    rw [habs] at hr
    cases o with
    | Ok fe' => exact hr
    | Err e => exact hr
  cases kind with
  | QuotK =>
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    have hbv := BasisPins.eq_basis_pinned_refines hfr hfw hb
    cases b with
    | false =>
      -- the quotient gate declined: `ParsedC.lean:227-228`'s own `throw`
      obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
      have hout : out = .Err ce := by simpa using h.symm
      subst hout
      have hne : ¬ (lfe.find? ConLeche.eqName = some ConLeche.eqA) := by
        simpa using hbv.symm
      show ErrSim ce _
      refine errSim_notImplemented
        (ls := "quotient basis requires the pinned Eq basis") hce rfl ?_
      simp only [absBasisKind]
      rw [if_pos trivial, if_neg hne]
      rfl
    | true =>
      obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
      have hr := install v out hv h
      have heq : (lfe.find? ConLeche.eqName = some ConLeche.eqA) := by
        simpa using hbv.symm
      cases out with
      | Ok fe' =>
        obtain ⟨lfe₂, hfold, rest⟩ := hr
        refine ⟨lfe₂, ?_, rest⟩
        simp only [absBasisKind] at hfold ⊢
        rw [show (lfe.find? ConLeche.eqName = some ConLeche.eqA) from heq]
        simpa using hfold
      | Err e =>
        show ErrSim e _
        simp only [absBasisKind] at hr ⊢
        rw [show (lfe.find? ConLeche.eqName = some ConLeche.eqA) from heq]
        simpa using hr
  | EqK | NatK | PunitK | EmptyK | FalseK =>
    all_goals (
      obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
      have hr := install v out hv h
      cases out with
      | Ok fe' =>
        obtain ⟨lfe₂, hfold, rest⟩ := hr
        refine ⟨lfe₂, ?_, rest⟩
        simp only [absBasisKind] at hfold ⊢
        simpa using hfold
      | Err e =>
        show ErrSim e _
        simp only [absBasisKind] at hr ⊢
        simpa using hr)

/-- `check_basis_decl_c_refines` at a success, the pre-#67 statement. -/
theorem check_basis_decl_c_refines_ok {mode : env.CheckMode} {fe fe' : fenv.FEnv}
    {kind : env.BasisKind} (hfw : FEnvWF fe)
    (hcan : FEnv.FEnvCanon fe) (hfull : FEnv.FEnvFull fe)
    (h : cached.parsed_c.check_basis_decl_c fe kind = ok (.Ok fe')) :
    ∀ lst lfe, FEnvRel fe lfe →
      ∃ lfe',
        (ConLeche.Cached.checkDeclC (absMode mode) lfe
            (.basisDecl (absBasisKind kind))).run lst = Except.ok (lfe', lst)
        ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  check_basis_decl_c_refines hfw hcan hfull h

/-! ## The dispatch and the fold

Eight statements.  Each arm's content is a sibling file's
(`Refine/Checker.lean`, `Refine/CheckerPins.lean`,
`Refine/CheckerBase.lean`); stated here so the dispatch is fixed and the
composition is a `cases` on the declaration. -/

/-! ### The sibling files' named hypotheses, discharged

Four sibling files name what they need of another file as a `Prop` and take it
as a hypothesis (task #49's idiom).  This file is a consumer of all four, so it
discharges them here — each is a sibling *theorem* applied, nothing is assumed.
(`Refine/CheckerPinned.lean` does the same for the tier it heads; it imports
this file's siblings and is deliberately not imported here.) -/

/-- `Refine/CheckerBase.lean`'s hypothesis, from `Refine/DeclCheck.lean`: the
executed `constsResolveFFast` is `Expr.constsResolveF`. -/
theorem constsResolveFSpec : CheckerBase.ConstsResolveFSpec :=
  fun _ _ _ _ hrel hwf he h =>
    DeclCheck.consts_resolve_f_fast_refines CoreK.pinnedBasisNames
      (FindAgree.of_rel hrel hwf) he h

/-- `Refine/StateCResolve.lean`'s hypothesis, from `Refine/CoreKSupport.lean`:
the two `.lit` guards of the memoised resolution walk. -/
theorem litGuardsRefine : StateC.LitGuardsRefine where
  nat _ _ _ hrel hwf h :=
    CoreK.nat_trio_stored_refines CoreK.pinnedBasisNames (FindAgree.of_rel hrel hwf) h
  str _ _ _ hrel hwf h :=
    CoreK.str_support_stored_refines CoreK.pinnedBasisNames (FindAgree.of_rel hrel hwf) h

/-- `Refine/StdAxioms.lean`'s hypothesis, from `Refine/BasisPins.lean`. -/
theorem eqBasisPinned {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe) : StdAxioms.EqBasisPinned fe lfe :=
  fun _ h => BasisPins.eq_basis_pinned_refines hrel hwf h

/-- `Refine/TrustAxioms.lean`'s first hypothesis, from `Refine/StdAxioms.lean`. -/
theorem matchesPinSpec : TrustAxioms.MatchesPinSpec :=
  fun _ _ _ hcv hpin h => StdAxioms.matches_pin_fast_eq_matches_pin hcv hpin h

/-- `Refine/TrustAxioms.lean`'s second hypothesis, from `Refine/BasisPins.lean`. -/
theorem basisPinsSpec {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe) : TrustAxioms.BasisPinsSpec fe lfe where
  eqPinned _ h := BasisPins.eq_basis_pinned_refines hrel hwf h
  natPinned _ h := BasisPins.nat_basis_pinned_refines hrel hwf h

/-! ### `core_k::consts_resolve` at the index

`Refine/CoreKSupport.lean`'s `consts_resolve_refines` is stated against the
`Env`-indexed `Expr.constsResolve`, so it needs an `Env` that agrees with the
index — which the *cached* tier has no reason to have (`checkDeclC` never
mentions an `Env`).  The same induction against `Expr.constsResolveF`
(`ConLeche/Kernel/DeclCheck.lean:39-58`, the same ten clauses at
`FEnv.find?`) needs only `FindAgree`, which `FEnvRel` + `FEnvWF` give.  It is
what lets `TrustGuardsSpec` be discharged at an arbitrary related index. -/

theorem consts_resolve_f_step {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hfe : FindAgree fe lfe) {e : expr.Expr} (he : ExprWF e) :
    ∀ c, core_k.consts_resolve fe e = ok c →
      c = ConLeche.Expr.constsResolveF lfe (absExpr e) := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.constsResolveF]
  | @sort u e hu h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, Result.ok.injEq] at h
    rw [← h]; simp [ConLeche.Expr.constsResolveF]
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d1, b0, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff,
      Result.ok.injEq] at h
    obtain ⟨o, ho, h⟩ := h
    rw [← h, CoreK.find_isSome hfe hn ho]
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    rw [ih c h]; simp [ConLeche.Expr.constsResolveF]
  | @lit l e hl h1 =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    cases l with
    | NatVal k =>
      rw [CoreK.nat_trio_stored_refines CoreK.pinnedBasisNames hfe h]
      simp only [absExpr, absExprNode, absExprKind, absLiteral,
        ConLeche.Expr.constsResolveF]
    | StrVal sv =>
      simp only [bind_eq_ok_iff] at h
      obtain ⟨b, hb, h⟩ := h
      have g1 := CoreK.nat_trio_stored_refines CoreK.pinnedBasisNames hfe hb
      simp only [absExpr, absExprNode, absExprKind, absLiteral,
        ConLeche.Expr.constsResolveF]
      cases b with
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        rw [← h, ← g1]; simp
      | true =>
        simp only [if_true] at h
        rw [CoreK.str_support_stored_refines CoreK.pinnedBasisNames hfe h, ← g1]
        simp
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.app_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
    exact CoreK.and_step (ihf b1 hb1) h (fun c' h' => iha c' h')
  | @lam ty bo m e hty hbo hm h1 iht ihb =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
    exact CoreK.and_step (iht b1 hb1) h (fun c' h' => ihb c' h')
  | @forall_e ty bo m e hty hbo hm h1 iht ihb =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
    exact CoreK.and_step (iht b1 hb1) h (fun c' h' => ihb c' h')
  | @let_e ty v bo e hty hv hbo h1 iht ihv ihb =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF,
      Bool.and_assoc]
    refine CoreK.and_step (iht b1 hb1) h ?_
    intro c' h'
    obtain ⟨b2, hb2, h'⟩ := bind_eq_ok_iff.mp h'
    exact CoreK.and_step (ihv b2 hb2) h' (fun c'' h'' => ihb c'' h'')
  | @proj sn i x e hs hx h1 ih =>
    obtain ⟨d1, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro c h
    rw [core_k.consts_resolve.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, ExprOps.node_kind, bind_eq_ok_iff] at h
    obtain ⟨o, ho, h⟩ := h
    simp only [absExpr, absExprNode, absExprKind, ConLeche.Expr.constsResolveF]
    exact CoreK.and_step (by rw [CoreK.find_isSome hfe hs ho]) h
      (fun c' h' => ih c' h')

/-- `Refine/TrustAxioms.lean`'s `reduce_pin_guard` at the index, with no `Env`
in sight: the last conjunct through `consts_resolve_f_step`. -/
theorem reduce_pin_guard_f_step {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    {c : name.Name} {r : Bool} (hfe : FindAgree fe lfe) (hc : NameWF c)
    (h : trust_axioms.reduce_pin_guard fe c = ok r) :
    r = ConLeche.reducePinGuardF lfe (absName c) := by
  rw [trust_axioms.reduce_pin_guard] at h
  obtain ⟨pin, hpin, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hpabs, hpwf⟩ := TrustAxioms.reduce_decl_pin_refines hc hpin
  have hb0 := ExprOps.loose_bvars_bounded_refines hpwf hb
  rw [Expr.val_zero] at hb0
  rw [ConLeche.reducePinGuardF, ← hpabs]
  cases b with
  | false =>
    simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
    rw [← h, ← hb0]; simp
  | true =>
    simp only [if_true] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := ExprOps.has_fvar_refines hpwf hb1
    cases b1 with
    | true =>
      simp only [if_true, Result.ok.injEq] at h
      rw [← h, ← hb0, ← hb1v]; simp
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
      have hb2v := ExprOps.all_level_params_defined_fast_refines
        (by intro x hx; simp [alloc.vec.Vec.new] at hx) hpwf hb2
      rw [show absNames (alloc.vec.Vec.new name.Name) = ([] : List ConLeche.Name) from by
        simp [absNames, alloc.vec.Vec.new]] at hb2v
      cases b2 with
      | false =>
        simp only [Bool.false_eq_true, if_false, Result.ok.injEq] at h
        rw [← h, ← hb0, ← hb1v, ← hb2v]; simp
      | true =>
        simp only [if_true] at h
        rw [consts_resolve_f_step hfe hpwf r h, ← hb0, ← hb1v, ← hb2v]
        simp

/-- `Refine/CheckerPins.lean`'s pinned-value hypothesis, from
`Refine/TrustAxioms.lean`. -/
theorem trustPinsSpec : CheckerPins.TrustPinsSpec where
  declPin _ _ hc h := TrustAxioms.reduce_decl_pin_refines hc h
  certVar _ _ hc h := TrustAxioms.reduce_cert_var_refines hc h

/-- `Refine/CheckerPins.lean`'s three environment guards, from
`Refine/TrustAxioms.lean` and `reduce_pin_guard_f_step` above. -/
theorem trustGuardsSpec {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hrel : FEnvRel fe lfe) (hwf : FEnvWF fe) : CheckerPins.TrustGuardsSpec fe lfe where
  storedOk _ _ hc h := TrustAxioms.reduce_stored_ok_refines matchesPinSpec
    (FindAgree.of_rel hrel hwf) (FindWF.of_wf hwf) hc h
  elemOk _ _ hc h := TrustAxioms.reduce_elem_ok_refines matchesPinSpec
    (basisPinsSpec hrel hwf) (FindAgree.of_rel hrel hwf) (FindWF.of_wf hwf) hc h
  pinGuard _ _ hc h := reduce_pin_guard_f_step (FindAgree.of_rel hrel hwf) hc h

/-! ### The pre-insertion view of a pushed index

Both pin gates run at `fe.restrictTo k_pre` where `k_pre` is the *pre*-insertion
bound, i.e. at the pushed index with the new constant hidden again.  That view
answers exactly what the pre-insertion index answers — the new entry sits at the
bound, and the constant check proved the name fresh — which is the
`find?`-agreement the `_at_view` lemmas of `Refine/CheckerPins.lean` ask for. -/

theorem push_restrict_find {lfe : ConLeche.FEnv} {ci : ConLeche.ConstantInfo}
    (h : lfe.find? ci.name = none) :
    ((lfe.push ci).restrictTo lfe.visibleBelow).find? = lfe.find? := by
  funext n
  simp only [ConLeche.FEnv.find?, ConLeche.FEnv.restrictTo, ConLeche.FEnv.push,
    Std.HashMap.getElem?_insert]
  by_cases hn : n = ci.name
  · subst hn
    simp only [beq_self_eq_true, if_true, lt_irrefl, if_false]
    rw [ConLeche.FEnv.find?] at h
    exact h.symm
  · rw [if_neg (show ¬ ((ci.name == n) = true) from fun hc => hn (eq_of_beq hc).symm)]

/-! ### `cached::parsed_c`'s constant check

`checkConstantValC` (`ConLeche/Cached/ParsedC.lean:74-95`) is
`checkConstantValF` with the four syntactic passes memoised on the `ExprC` DAG
(`ExprC.looseBVarsBounded`, `ExprC.hasFvar`, `ExprC.allLevelParamsDefined`,
`constsResolveFC`) and one further result: it returns the *annotated type*
beside the constant, which is the `jty` `recordCConst` stores.  The port splits
it at the annotation (task #24's deviation 7), so the tail gets a name here,
exactly as `Refine/CheckerBase.lean`'s `constantValTail` does for the
`Expr`-level twin. -/

open ConLeche.Cached in
/-- The tail of `checkConstantValC` past the annotation
(`ConLeche/Cached/ParsedC.lean:88-95`). -/
def constantValCTail (mode : env.CheckMode) (lfe : ConLeche.FEnv)
    (cv : ConLeche.ConstantVal) (jty : ExprC) :
    CheckCM (ConLeche.ConstantVal × ExprC) := do
  unless ExprC.allLevelParamsDefined cv.levelParams jty do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless constsResolveFC lfe jty do
    throw (.invalid s!"unknown constant in type of {cv.name}")
  let jsty ← (coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty
  let _u ← opSIxC (absMode mode) lfe 0 jsty
  let tyE := jty
  pure (⟨cv.name, cv.levelParams, tyE⟩, jty)

open ConLeche.Cached in
/-- The tail, run: both guards held and both core calls succeeded. -/
theorem constantValCTail_run {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cv : ConLeche.ConstantVal} {jty jsty : ExprC} {u : ConLeche.Level}
    {lst lst1 lst2 : CState}
    (h1 : ExprC.allLevelParamsDefined cv.levelParams jty = true)
    (h2 : constsResolveFC lfe jty = true)
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty).run lst
      = .ok (jsty, lst1))
    (hsort : (opSIxC (absMode mode) lfe 0 jsty).run lst1 = .ok (u, lst2)) :
    (constantValCTail mode lfe cv jty).run lst
      = .ok ((⟨cv.name, cv.levelParams, jty⟩, jty), lst2) := by
  rw [constantValCTail]
  simp only [h1, h2, reduceIte, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty) lst
      = Except.ok (jsty, lst1) from hinf]
  simp only []
  rw [show (opSIxC (absMode mode) lfe 0 jsty) lst1 = Except.ok (u, lst2) from hsort]

open ConLeche.Cached in
/-- The tail's universe-parameter `throw` (`ConLeche/Cached/ParsedC.lean:88-89`). -/
theorem constantValCTail_lp_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cv : ConLeche.ConstantVal} {jty : ExprC} {lst : CState}
    (h1 : ExprC.allLevelParamsDefined cv.levelParams jty = false) :
    (constantValCTail mode lfe cv jty).run lst
      = .error (.invalid s!"undeclared universe parameter in type of {cv.name}") := by
  rw [constantValCTail]
  simp only [h1, Bool.false_eq_true, if_false, StateT.run, Bind.bind, StateT.bind,
    Except.bind]
  rfl

open ConLeche.Cached in
/-- The tail's resolution `throw` (`ConLeche/Cached/ParsedC.lean:90-91`). -/
theorem constantValCTail_resolve_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cv : ConLeche.ConstantVal} {jty : ExprC} {lst : CState}
    (h1 : ExprC.allLevelParamsDefined cv.levelParams jty = true)
    (h2 : constsResolveFC lfe jty = false) :
    (constantValCTail mode lfe cv jty).run lst
      = .error (.invalid s!"unknown constant in type of {cv.name}") := by
  rw [constantValCTail]
  simp only [h1, h2, Bool.false_eq_true, if_false, if_true, StateT.run, Bind.bind,
    StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- The tail passes on what the type's inference threw. -/
theorem constantValCTail_infer_err {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cv : ConLeche.ConstantVal} {jty : ExprC} {lst : CState}
    {le : ConLeche.CheckError}
    (h1 : ExprC.allLevelParamsDefined cv.levelParams jty = true)
    (h2 : constsResolveFC lfe jty = true)
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty).run lst
      = .error le) :
    (constantValCTail mode lfe cv jty).run lst = .error le := by
  rw [constantValCTail]
  simp only [h1, h2, reduceIte, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty) lst
    = Except.error le from hinf]

open ConLeche.Cached in
/-- The tail passes on what the sort check threw. -/
theorem constantValCTail_sort_err {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cv : ConLeche.ConstantVal} {jty jsty : ExprC} {lst lst1 : CState}
    {le : ConLeche.CheckError}
    (h1 : ExprC.allLevelParamsDefined cv.levelParams jty = true)
    (h2 : constsResolveFC lfe jty = true)
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty).run lst
      = .ok (jsty, lst1))
    (hsort : (opSIxC (absMode mode) lfe 0 jsty).run lst1 = .error le) :
    (constantValCTail mode lfe cv jty).run lst = .error le := by
  rw [constantValCTail]
  simp only [h1, h2, reduceIte, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty) lst
    = Except.ok (jsty, lst1) from hinf]
  simp only []
  rw [show (opSIxC (absMode mode) lfe 0 jsty) lst1 = Except.error le from hsort]

open ConLeche.Cached in
/-- `checkConstantValC` at a run whose six syntactic guards passed and whose
annotation succeeded: it *is* the tail, on the post-annotation state. -/
theorem checkConstantValC_at_annot {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cv : ConLeche.ConstantVal} {jty : ExprC} {lst lst1 : CState}
    (h1 : (lfe.find? cv.name).isSome = false)
    (h2 : ConLeche.reservedBasisNames.contains cv.name = false)
    (h3 : cv.name.isProjFnShape = false)
    (h4 : ConLeche.Name.nodup cv.levelParams = true)
    (h5 : ExprC.looseBVarsBounded 0 cv.type = true)
    (h6 : ExprC.hasFvar cv.type = false)
    (hann : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 cv.type).run lst
      = .ok (jty, lst1)) :
    (checkConstantValC (absMode mode) lfe cv).run lst
      = (constantValCTail mode lfe cv jty).run lst1 := by
  rw [checkConstantValC, constantValCTail]
  simp only [h1, h2, h3, h4, h5, h6, Bool.false_eq_true, if_false, if_true,
    StateT.run, Bind.bind, StateT.bind,
    Except.bind, Pure.pure]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 cv.type) lst
      = Except.ok (jty, lst1) from hann]
  rfl

open ConLeche.Cached in
/-- `checkConstantValC`'s duplicate-declaration `throw`
(`ConLeche/Cached/ParsedC.lean:75-76`). -/
theorem checkConstantValC_dup_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cv : ConLeche.ConstantVal} {lst : CState}
    (h1 : (lfe.find? cv.name).isSome = true) :
    (checkConstantValC (absMode mode) lfe cv).run lst
      = .error (.invalid s!"duplicate declaration {cv.name}") := by
  rw [checkConstantValC]
  simp only [h1, if_true, StateT.run, Bind.bind, StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `checkConstantValC`'s reserved-basis-name `throw`
(`ConLeche/Cached/ParsedC.lean:77-78`). -/
theorem checkConstantValC_reserved_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cv : ConLeche.ConstantVal} {lst : CState}
    (h1 : (lfe.find? cv.name).isSome = false)
    (h2 : ConLeche.reservedBasisNames.contains cv.name = true) :
    (checkConstantValC (absMode mode) lfe cv).run lst
      = .error (.invalid s!"reserved basis name {cv.name}") := by
  rw [checkConstantValC]
  simp only [h1, h2, Bool.false_eq_true, if_false, if_true, StateT.run, Bind.bind,
    StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `checkConstantValC`'s reserved-projection-name `throw`
(`ConLeche/Cached/ParsedC.lean:79-80`). -/
theorem checkConstantValC_proj_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cv : ConLeche.ConstantVal} {lst : CState}
    (h1 : (lfe.find? cv.name).isSome = false)
    (h2 : ConLeche.reservedBasisNames.contains cv.name = false)
    (h3 : cv.name.isProjFnShape = true) :
    (checkConstantValC (absMode mode) lfe cv).run lst
      = .error (.invalid s!"reserved projection name {cv.name}") := by
  rw [checkConstantValC]
  simp only [h1, h2, h3, Bool.false_eq_true, if_false, if_true, StateT.run, Bind.bind,
    StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `checkConstantValC`'s duplicate-universe-parameter `throw`
(`ConLeche/Cached/ParsedC.lean:81-82`). -/
theorem checkConstantValC_nodup_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cv : ConLeche.ConstantVal} {lst : CState}
    (h1 : (lfe.find? cv.name).isSome = false)
    (h2 : ConLeche.reservedBasisNames.contains cv.name = false)
    (h3 : cv.name.isProjFnShape = false)
    (h4 : ConLeche.Name.nodup cv.levelParams = false) :
    (checkConstantValC (absMode mode) lfe cv).run lst
      = .error (.invalid s!"duplicate universe parameters in {cv.name}") := by
  rw [checkConstantValC]
  simp only [h1, h2, h3, h4, Bool.false_eq_true, if_false, StateT.run, Bind.bind,
    StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `checkConstantValC`'s loose-bound-variable `throw`
(`ConLeche/Cached/ParsedC.lean:83-84`). -/
theorem checkConstantValC_loose_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cv : ConLeche.ConstantVal} {lst : CState}
    (h1 : (lfe.find? cv.name).isSome = false)
    (h2 : ConLeche.reservedBasisNames.contains cv.name = false)
    (h3 : cv.name.isProjFnShape = false)
    (h4 : ConLeche.Name.nodup cv.levelParams = true)
    (h5 : ExprC.looseBVarsBounded 0 cv.type = false) :
    (checkConstantValC (absMode mode) lfe cv).run lst
      = .error (.invalid s!"loose bound variable in type of {cv.name}") := by
  rw [checkConstantValC]
  simp only [h1, h2, h3, h4, h5, Bool.false_eq_true, if_false, if_true, StateT.run,
    Bind.bind, StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `checkConstantValC`'s free-variable `throw`
(`ConLeche/Cached/ParsedC.lean:85-86`). -/
theorem checkConstantValC_fvar_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cv : ConLeche.ConstantVal} {lst : CState}
    (h1 : (lfe.find? cv.name).isSome = false)
    (h2 : ConLeche.reservedBasisNames.contains cv.name = false)
    (h3 : cv.name.isProjFnShape = false)
    (h4 : ConLeche.Name.nodup cv.levelParams = true)
    (h5 : ExprC.looseBVarsBounded 0 cv.type = true)
    (h6 : ExprC.hasFvar cv.type = true) :
    (checkConstantValC (absMode mode) lfe cv).run lst
      = .error (.invalid s!"unexpected free variable in type of {cv.name}") := by
  rw [checkConstantValC]
  simp only [h1, h2, h3, h4, h5, h6, Bool.false_eq_true, if_false, if_true, StateT.run,
    Bind.bind, StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `checkConstantValC` passes on what the type's annotation threw. -/
theorem checkConstantValC_annot_err {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cv : ConLeche.ConstantVal} {lst : CState} {le : ConLeche.CheckError}
    (h1 : (lfe.find? cv.name).isSome = false)
    (h2 : ConLeche.reservedBasisNames.contains cv.name = false)
    (h3 : cv.name.isProjFnShape = false)
    (h4 : ConLeche.Name.nodup cv.levelParams = true)
    (h5 : ExprC.looseBVarsBounded 0 cv.type = true)
    (h6 : ExprC.hasFvar cv.type = false)
    (hann : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 cv.type).run lst
      = .error le) :
    (checkConstantValC (absMode mode) lfe cv).run lst = .error le := by
  rw [checkConstantValC]
  simp only [h1, h2, h3, h4, h5, h6, Bool.false_eq_true, if_false, if_true,
    StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 cv.type) lst
      = Except.error le from hann]

/-- **The tail of `cached::parsed_c::check_constant_val_c` past the
annotation** (`ConLeche/Cached/ParsedC.lean:88-95`): the level-parameter and
resolution guards on the annotated type, the type's own sort, and the record
`⟨cv.name, cv.levelParams, jty⟩` paired with `jty` itself.

Over the whole outcome (task #67): the port's two `invalid` sites
(`cached/parsed_c.rs:219`, `:224`) are the cited tail's own two `throw`s, and
its other two failures are what `infer_type_core` and `op_s_ix_c` threw. -/
theorem check_constant_val_c_after_annot_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {cv : env.ConstantVal}
    {ty : expr.Expr}
    {out : core.result.Result (env.ConstantVal × expr.Expr) core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hty : ExprWF ty)
    (h : cached.parsed_c.check_constant_val_c_after_annot mode st fe cv ty
      = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok (cv', ty') =>
        ∃ lst', (constantValCTail mode lfe (absConstantVal cv) (absExpr ty)).run lst
            = Except.ok ((absConstantVal cv', absExpr ty'), lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv' ∧ ExprWF ty'
          ∧ cv'.name = cv.name
      | .Err e =>
        ErrSim e ((constantValCTail mode lfe (absConstantVal cv)
          (absExpr ty)).run lst) := by
  intro lst lfe hsr hfr
  obtain ⟨hnwf, hlpwf, htywf⟩ := hcv
  rw [cached.parsed_c.check_constant_val_c_after_annot] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbabs := ExprOpsC.all_level_params_defined_refines hlpwf hty hb
  split at h
  · rename_i hbt
    subst hbt
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1abs := StateC.consts_resolve_fc_refines litGuardsRefine hfr hfw hty hb1
    split at h
    · rename_i hb1t
      subst hb1t
      obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r1, st1⟩ := q
      cases r1 with
      | Err er =>
        -- the type's inference threw, and the cited tail's first core call
        -- throws the same
        obtain ⟨hout, -⟩ := err_outS h
        subst hout
        show ErrSim er _
        have herr := (TypeChecker.infer_type_core_refines hfuel hk).err st fe 0#u64 ty
          er st1 hsw hfw hty hq lst lfe hsr hfr
        exact ErrSim.trans herr (fun _ hle =>
          constantValCTail_infer_err (cv := absConstantVal cv)
            (by simp only [absConstantVal]; rw [← hbabs]) (by rw [← hb1abs]) hle)
      | Ok jsty =>
        obtain ⟨lst1, hrun1, hsr1, hsw1, hstwf⟩ :=
          (TypeChecker.infer_type_core_refines hfuel hk).ok st fe 0#u64 ty jsty st1
            hsw hfw hty hq lst lfe hsr hfr
        obtain ⟨q2, hq2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r2, st2⟩ := q2
        cases r2 with
        | Err er =>
          -- the sort check threw, and the cited tail's second core call throws
          -- the same
          obtain ⟨hout, -⟩ := err_outS h
          subst hout
          show ErrSim er _
          have hinf : ((ConLeche.Cached.coreKnotI (absMode mode) lfe
              ConLeche.checkFuel).infer 0 (absExpr ty)).run lst
              = .ok (absExpr jsty, lst1) := hrun1
          have herr := (TypeChecker.ensure_sort_core_refines hfuel hk).err st1 fe 0#u64
            jsty er st2 hsw1 hfw hstwf
            (hq2 : type_checker.ensure_sort_core mode st1 fe 0#u64 jsty
              = ok (.Err er, st2)) lst1 lfe hsr1 hfr
          exact ErrSim.trans herr (fun _ hle =>
            constantValCTail_sort_err (cv := absConstantVal cv)
              (by simp only [absConstantVal]; rw [← hbabs]) (by rw [← hb1abs]) hinf hle)
        | Ok u =>
          obtain ⟨lst2, hrun2, hsr2, hsw2, huwf⟩ :=
            (TypeChecker.ensure_sort_core_refines hfuel hk).ok st1 fe 0#u64 jsty u st2
              hsw1 hfw hstwf (hq2 : type_checker.ensure_sort_core mode st1 fe 0#u64 jsty
                = ok (.Ok u, st2)) lst1 lfe hsr1 hfr
          obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
          have hev : e = ty := Expr.dup_eq he
          obtain ⟨hout, rfl⟩ := ok_outS h
          subst hout
          have hvv : v.val = cv.level_params.val := PropWhen.names_copy_val hv
          have hnv : n = cv.name := by simpa using hn.symm
          have hinf : ((ConLeche.Cached.coreKnotI (absMode mode) lfe
              ConLeche.checkFuel).infer 0 (absExpr ty)).run lst
              = .ok (absExpr jsty, lst1) := hrun1
          have hsort : (ConLeche.Cached.opSIxC (absMode mode) lfe 0
              (absExpr jsty)).run lst1 = .ok (absLevel u, lst2) := hrun2
          have hvabs : absNames v = absNames cv.level_params := by
            rw [absNames, absNames, hvv]
          refine ⟨lst2, ?_, hsr2, hsw2, ?_, hty, hnv⟩
          · rw [constantValCTail_run (cv := absConstantVal cv)
              (by simp only [absConstantVal]; rw [← hbabs]) (by rw [← hb1abs]) hinf hsort]
            simp only [absConstantVal, hnv, hvabs, hev]
          · refine ⟨by rw [hnv]; exact hnwf, ?_, by rw [hev]; exact hty⟩
            intro x hx; exact hlpwf x (by rw [hvv] at hx; exact hx)
    · -- the resolution guard declined: `ParsedC.lean:90-91`'s own `throw`
      rename_i hb1f
      obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hout, -⟩ := err_outS h
      subst hout
      show ErrSim ce _
      exact errSim_invalid hce rfl
        (constantValCTail_resolve_throw (cv := absConstantVal cv) (lst := lst)
          (by simp only [absConstantVal]; rw [← hbabs])
          (by rw [← hb1abs]; simpa using hb1f))
  · -- the universe-parameter guard declined: `ParsedC.lean:88-89`'s own `throw`
    rename_i hbf
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim ce _
    exact errSim_invalid hce rfl
      (constantValCTail_lp_throw (cv := absConstantVal cv) (lst := lst)
        (by simp only [absConstantVal]; rw [← hbabs]; simpa using hbf))

/-- `check_constant_val_c_after_annot_refines` at a success, the pre-#67
statement. -/
theorem check_constant_val_c_after_annot_refines_ok {mode : env.CheckMode}
    {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {cv cv' : env.ConstantVal}
    {ty ty' : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hty : ExprWF ty)
    (h : cached.parsed_c.check_constant_val_c_after_annot mode st fe cv ty
      = ok (.Ok (cv', ty'), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (constantValCTail mode lfe (absConstantVal cv) (absExpr ty)).run lst
          = Except.ok ((absConstantVal cv', absExpr ty'), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv' ∧ ExprWF ty'
        ∧ cv'.name = cv.name :=
  check_constant_val_c_after_annot_refines hfuel hk hsw hfw hcv hty h

/-- **`cached::parsed_c::check_constant_val_c` refines `checkConstantValC`**
(`ConLeche/Cached/ParsedC.lean:74-95`): the checks common to all parsed
declarations, at the memoised `ExprC` guards, returning the annotated constant
*and* its annotated type. -/
theorem check_constant_val_c_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {cv : env.ConstantVal}
    {out : core.result.Result (env.ConstantVal × expr.Expr) core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv)
    (h : cached.parsed_c.check_constant_val_c mode st fe cv = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok (cv', ty') =>
        ∃ lst', (ConLeche.Cached.checkConstantValC (absMode mode) lfe
            (absConstantVal cv)).run lst
              = Except.ok ((absConstantVal cv', absExpr ty'), lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv' ∧ ExprWF ty'
          ∧ cv'.name = cv.name ∧ lfe.find? (absName cv.name) = none
      | .Err e =>
        ErrSim e ((ConLeche.Cached.checkConstantValC (absMode mode) lfe
          (absConstantVal cv)).run lst) := by
  intro lst lfe hsr hfr
  obtain ⟨hnwf, hlpwf, htywf⟩ := hcv
  rw [cached.parsed_c.check_constant_val_c] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  have hfind := FEnv.find_refines hfr hfw hnwf ho
  cases o with
  | some ci =>
    -- the duplicate `throw` (`ParsedC.lean:75-76`)
    simp only [core.option.Option.is_some] at h
    have h1 : ((lfe.find? (absName cv.name)).isSome) = true := by
      rw [← hfind]; simp
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim ce _
    exact errSim_invalid hce rfl
      (checkConstantValC_dup_throw (cv := absConstantVal cv) (lst := lst)
        (by simp only [absConstantVal]; exact h1))
  | none =>
    simp only [core.option.Option.is_some] at h
    have h1 : ((lfe.find? (absName cv.name)).isSome) = false := by
      rw [← hfind]; simp
    obtain ⟨rv, hrv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hrvabs, hrvwf⟩ := BasisNames.reserved_basis_names_refines hrv
    have hb1abs := Name.contains_refines hrvwf hnwf hb1
    rw [hrvabs] at hb1abs
    split at h
    · -- the reserved-basis-name `throw` (`ParsedC.lean:77-78`)
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
        (checkConstantValC_reserved_throw (cv := absConstantVal cv) (lst := lst)
          (by simp only [absConstantVal]; exact h1)
          (by simp only [absConstantVal]; exact h2))
    · rename_i hb1f
      have h2 : ConLeche.reservedBasisNames.contains (absName cv.name) = false := by
        rw [← hb1abs]; simpa using hb1f
      obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
      have hb2abs := CoreK.name_is_proj_fn_shape_refines hnwf hb2
      split at h
      · -- the reserved-projection-name `throw` (`ParsedC.lean:79-80`)
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
          (checkConstantValC_proj_throw (cv := absConstantVal cv) (lst := lst)
            (by simp only [absConstantVal]; exact h1)
            (by simp only [absConstantVal]; exact h2)
            (by simp only [absConstantVal]; exact h3))
      · rename_i hb2f
        have h3 : (absName cv.name).isProjFnShape = false := by
          rw [← hb2abs]; simpa using hb2f
        obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
        have hb3abs := CheckerBase.name_nodup_refines hlpwf hb3
        split at h
        · rename_i hb3t
          obtain ⟨b4, hb4, h⟩ := bind_eq_ok_iff.mp h
          have hb4abs := ExprOpsC.loose_bvars_bounded_refines htywf hb4
          rw [show ((0#u64 : Std.U64)).val = 0 from rfl] at hb4abs
          split at h
          · rename_i hb4t
            obtain ⟨b5, hb5, h⟩ := bind_eq_ok_iff.mp h
            have hb5abs := ExprOpsC.has_fvar_refines htywf hb5
            split at h
            · -- the free-variable `throw` (`ParsedC.lean:85-86`)
              rename_i hb5t
              obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨hout, -⟩ := err_outS h
              subst hout
              show ErrSim ce _
              exact errSim_invalid hce rfl
                (checkConstantValC_fvar_throw (cv := absConstantVal cv) (lst := lst)
                  (by simp only [absConstantVal]; exact h1)
                  (by simp only [absConstantVal]; exact h2)
                  (by simp only [absConstantVal]; exact h3)
                  (by simp only [absConstantVal]; rw [← hb3abs]; exact hb3t)
                  (by simp only [absConstantVal]; rw [← hb4abs]; exact hb4t)
                  (by simp only [absConstantVal]; rw [← hb5abs]; exact hb5t))
            · rename_i hb5f
              obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨r1, st1⟩ := q
              cases r1 with
              | Err er =>
                -- the annotation threw, and the cited check's own annotation
                -- throws the same
                obtain ⟨hout, -⟩ := err_outS h
                subst hout
                show ErrSim er _
                have herr := (TypeChecker.annotate_core_refines hfuel hk).err st fe 0#u64
                  cv.ty er st1 hsw hfw htywf hq lst lfe hsr hfr
                exact ErrSim.trans herr (fun _ hle =>
                  checkConstantValC_annot_err (cv := absConstantVal cv)
                    (by simp only [absConstantVal]; exact h1)
                    (by simp only [absConstantVal]; exact h2)
                    (by simp only [absConstantVal]; exact h3)
                    (by simp only [absConstantVal]; rw [← hb3abs]; exact hb3t)
                    (by simp only [absConstantVal]; rw [← hb4abs]; exact hb4t)
                    (by simp only [absConstantVal]; rw [← hb5abs]; simpa using hb5f) hle)
              | Ok ty =>
                obtain ⟨lst1, hrun1, hsr1, hsw1, htyawf⟩ :=
                  (TypeChecker.annotate_core_refines hfuel hk).ok st fe 0#u64 cv.ty ty st1
                    hsw hfw htywf hq lst lfe hsr hfr
                have hrest :=
                  check_constant_val_c_after_annot_refines hfuel hk hsw1 hfw
                    ⟨hnwf, hlpwf, htywf⟩ htyawf h lst1 lfe hsr1 hfr
                have hann : ((ConLeche.Cached.coreKnotI (absMode mode) lfe
                    ConLeche.checkFuel).annotate 0 (absExpr cv.ty)).run lst
                    = .ok (absExpr ty, lst1) := hrun1
                have hhead : (ConLeche.Cached.checkConstantValC (absMode mode) lfe
                      (absConstantVal cv)).run lst
                    = (constantValCTail mode lfe (absConstantVal cv)
                        (absExpr ty)).run lst1 :=
                  checkConstantValC_at_annot (cv := absConstantVal cv) h1 h2 h3
                    (by simp only [absConstantVal]; rw [← hb3abs]; exact hb3t)
                    (by simp only [absConstantVal]; rw [← hb4abs]; exact hb4t)
                    (by simp only [absConstantVal]; rw [← hb5abs]; simpa using hb5f) hann
                cases out with
                | Ok p =>
                  obtain ⟨cv', ty'⟩ := p
                  obtain ⟨lst2, hrun2, hsr2, hsw2, hcv'wf, hty'wf, hnameq⟩ := hrest
                  exact ⟨lst2, by rw [hhead]; exact hrun2, hsr2, hsw2, hcv'wf, hty'wf,
                    hnameq, by simpa using h1⟩
                | Err e =>
                  show ErrSim e _
                  rw [hhead]
                  exact hrest
          · -- the loose-bound-variable `throw` (`ParsedC.lean:83-84`)
            rename_i hb4f
            obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hout, -⟩ := err_outS h
            subst hout
            show ErrSim ce _
            exact errSim_invalid hce rfl
              (checkConstantValC_loose_throw (cv := absConstantVal cv) (lst := lst)
                (by simp only [absConstantVal]; exact h1)
                (by simp only [absConstantVal]; exact h2)
                (by simp only [absConstantVal]; exact h3)
                (by simp only [absConstantVal]; rw [← hb3abs]; exact hb3t)
                (by simp only [absConstantVal]; rw [← hb4abs]; simpa using hb4f))
        · -- the duplicate-universe-parameter `throw` (`ParsedC.lean:81-82`)
          rename_i hb3f
          obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hout, -⟩ := err_outS h
          subst hout
          show ErrSim ce _
          exact errSim_invalid hce rfl
            (checkConstantValC_nodup_throw (cv := absConstantVal cv) (lst := lst)
              (by simp only [absConstantVal]; exact h1)
              (by simp only [absConstantVal]; exact h2)
              (by simp only [absConstantVal]; exact h3)
              (by simp only [absConstantVal]; rw [← hb3abs]; simpa using hb3f))

/-- `check_constant_val_c_refines` at a success, the pre-#67 statement. -/
theorem check_constant_val_c_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {cv cv' : env.ConstantVal}
    {ty' : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv)
    (h : cached.parsed_c.check_constant_val_c mode st fe cv = ok (.Ok (cv', ty'), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst', (ConLeche.Cached.checkConstantValC (absMode mode) lfe
          (absConstantVal cv)).run lst
            = Except.ok ((absConstantVal cv', absExpr ty'), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv' ∧ ExprWF ty'
        ∧ cv'.name = cv.name ∧ lfe.find? (absName cv.name) = none :=
  check_constant_val_c_refines hfuel hk hsw hfw hcv h

/-! ### The parsed axiom arm

`checkDeclC`'s `.axiomDecl` arm (`ConLeche/Cached/ParsedC.lean:203-232`): the
pinned axioms are installed with their shapes pinned, the tolerated whitelist
is checked and **not** stored, and every other axiom is a positive decline.
The three install routes are the same two lines — `recordCConst`, then
`fe.push (.axiomInfo cvA)` — so they are proved once, in `axiom_install_c`. -/

open ConLeche.Cached in
/-- The inverse of `run_bind_ok`: a `do`-step that ran `ok` ran both halves. -/
theorem run_bind_ok_inv {α β : Type} {x : CheckCM α} {f : α → CheckCM β}
    {lst lst' : CState} {b : β} (h : (x >>= f).run lst = .ok (b, lst')) :
    ∃ a l, x.run lst = .ok (a, l) ∧ (f a).run l = .ok (b, lst') := by
  rw [StateT.run_bind] at h
  cases hx : x.run lst with
  | error e => rw [hx] at h; simp [Bind.bind, Except.bind] at h
  | ok p =>
    refine ⟨p.1, p.2, ?_, ?_⟩
    · rfl
    · rw [hx] at h; exact h

open ConLeche.Cached in
/-- The same at a failure: a `do`-step whose continuation is a `pure` throws
only if the step itself threw.  This is what carries `checkDefnValF`'s failure
across `checkDefnValF_pushC` to `checkDefnVal`. -/
theorem run_bind_pure_err_inv {α β : Type} {x : CheckCM α} {g : α → β}
    {lst : CState} {le : ConLeche.CheckError}
    (h : (x >>= fun a => (pure (g a) : CheckCM β)).run lst = .error le) :
    x.run lst = .error le := by
  rw [StateT.run_bind] at h
  cases hx : x.run lst with
  | error e =>
    rw [hx] at h
    simp only [Bind.bind, Except.bind] at h
    rw [Except.error.inj h]
  | ok p =>
    rw [hx] at h
    simp only [Bind.bind, Except.bind, StateT.run, Pure.pure, StateT.pure,
      Except.pure] at h
    exact absurd h (by simp)

/-- `absConstantVal`'s two field reads, as rewrites. -/
theorem absConstantVal_name (cv : env.ConstantVal) :
    (absConstantVal cv).name = absName cv.name := rfl

theorem absConstantVal_type (cv : env.ConstantVal) :
    (absConstantVal cv).type = absExpr cv.ty := rfl

theorem absConstantVal_levelParams (cv : env.ConstantVal) :
    (absConstantVal cv).levelParams = absNames cv.level_params := rfl

open ConLeche.Cached in
/-- One `do` step of a `CheckCM` run, forward: the shape every arm below
inverts the model's `let … ←` with. -/
theorem run_bind_ok {α β : Type} {x : CheckCM α} {f : α → CheckCM β}
    {lst lst1 : CState} {a : α} {r : Except ConLeche.CheckError (β × CState)}
    (hx : x.run lst = .ok (a, lst1)) (hf : (f a).run lst1 = r) :
    (x >>= f).run lst = r := by
  rw [StateT.run_bind, hx]; exact hf

open ConLeche.Cached in
/-- The same at a `do` step that **threw**: the rest of the block never runs.
`Refine/State.lean`'s `ErrSim.bindCM` is this wrapped in an `ErrSim`; the arms
below want the bare equation, so that `run_bind_ok` can carry it through the
steps before it. -/
theorem run_bind_err_head {α β : Type} {x : CheckCM α} {f : α → CheckCM β}
    {lst : CState} {le : ConLeche.CheckError} (hx : x.run lst = .error le) :
    (x >>= f).run lst = .error le := by
  rw [StateT.run_bind, hx]; rfl

open ConLeche.Cached in
/-- One parsed axiom install: the record and the push, at the state and index
the guard left.  `Refine/StateC.lean`'s `record_c_const` and
`Refine/FEnv.lean`'s `push_refines`, composed. -/
theorem axiom_install_c {st st1 : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {cv_a : env.ConstantVal} {jty : expr.Expr} {n : name.Name} {e : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv_a) (hjty : ExprWF jty)
    (hn : name.dup cv_a.name = ok n) (he : expr.dup cv_a.ty = ok e)
    (hrec : cached.state_c.record_c_const st n e jty none = ok st1)
    (hpush : fenv.push fe (env.ConstantInfo.AxiomInfo cv_a) = ok fe') :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst1,
        (do recordCConst (absConstantVal cv_a).name (absConstantVal cv_a).type
              (absExpr jty) none
            pure (lfe.push (.axiomInfo (absConstantVal cv_a)))).run lst
          = .ok (lfe.push (.axiomInfo (absConstantVal cv_a)), lst1)
        ∧ StateRel st1 lst1 ∧ StateWF st1
        ∧ FEnvRel fe' (lfe.push (.axiomInfo (absConstantVal cv_a))) ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' := by
  intro lst lfe hsr hfr
  have hnv : n = cv_a.name := by simpa using hn.symm
  have hev : e = cv_a.ty := Expr.dup_eq he
  subst hnv; subst hev
  obtain ⟨lst1, hrecrun, hsr1, hsw1⟩ :=
    StateC.record_c_const_refines hsw hcv.1 hcv.2.2 hjty (by simp) hrec lst hsr
  obtain ⟨hrel', hwf'⟩ := FEnv.push_refines hfr hfw
    (show ConstantInfoWF (env.ConstantInfo.AxiomInfo cv_a) from hcv) hpush
  obtain ⟨hcan', hfull'⟩ := FEnv.push_canon hfw
    (show ConstantInfoWF (env.ConstantInfo.AxiomInfo cv_a) from hcv) hcan hfull hpush
  have hrr : (recordCConst (absConstantVal cv_a).name (absConstantVal cv_a).type
      (absExpr jty) none).run lst = .ok ((), lst1) := by
    show (recordCConst (absName cv_a.name) (absExpr cv_a.ty) (absExpr jty) none).run lst
      = .ok ((), lst1)
    simpa using hrecrun
  refine ⟨lst1, ?_, hsr1, hsw1, hrel', hwf', hcan', hfull'⟩
  exact run_bind_ok hrr rfl

/-! ### `cached::parsed_c`'s three value checks

`checkDefnValC`, `checkThmValC` and `checkOpaqueValC`
(`ConLeche/Cached/ParsedC.lean:97-157`) are the same six steps — the two scope
guards, the annotation, the level-parameter and resolution guards on the
annotated value, `recordCConst`, and the inferred type against the declared one
— differing only in what is recorded and what is pushed (and, for a theorem,
in the is-a-proposition gate in front).  The port splits each at the annotation
(task #24's deviation 7), so each tail gets a name here. -/

open ConLeche.Cached in
/-- `core_k::lift_fueled`'s success arm, run in `CheckCM`
(`ConLeche/Kernel/Core.lean:108-111 liftFueled`). -/
theorem lift_fueled_run {o : Option Bool} {b : Bool} {lst : CState}
    (h : core_k.lift_fueled o = ok (.Ok b)) :
    (ConLeche.liftFueled (m := CheckCM) "level comparison" o).run lst = .ok (b, lst) := by
  cases o with
  | none =>
    simp only [core_k.lift_fueled, bind_eq_ok_iff] at h
    obtain ⟨s, -, v, -, ce, -, hr⟩ := h
    simp at hr
  | some a =>
    simp only [core_k.lift_fueled, Result.ok.injEq] at h
    injection h with hab
    rw [← hab]
    rfl

open ConLeche.Cached in
/-- The tail of `checkDefnValC` past the annotation
(`ConLeche/Cached/ParsedC.lean:103-112`). -/
def defnValCTail (mode : env.CheckMode) (lfe : ConLeche.FEnv)
    (cvA : ConLeche.ConstantVal) (jty jv : ExprC) (hint : ConLeche.ReducibilityHint) :
    CheckCM ConLeche.FEnv := do
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC lfe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE := jv
  recordCConst cvA.name cvA.type jty (some (vE, jv))
  let jvt ← (coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv
  unless ← (coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in definition {cvA.name}")
  pure (lfe.push (.defnInfo cvA vE hint))

open ConLeche.Cached in
/-- The tail of `checkThmValC` past the annotation
(`ConLeche/Cached/ParsedC.lean:126-137`).  The pushed record keeps the parse's
own `value`, not the annotation: a theorem is stored by its statement. -/
def thmValCTail (mode : env.CheckMode) (lfe : ConLeche.FEnv)
    (cvA : ConLeche.ConstantVal) (jty value jv : ExprC) : CheckCM ConLeche.FEnv := do
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC lfe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  recordCConst cvA.name cvA.type jty none
  let jvt ← (coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv
  unless ← (coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in theorem {cvA.name}")
  pure (lfe.push (.thmInfo cvA value))

open ConLeche.Cached in
/-- The tail of `checkOpaqueValC` past the annotation
(`ConLeche/Cached/ParsedC.lean:147-156`). -/
def opaqueValCTail (mode : env.CheckMode) (lfe : ConLeche.FEnv)
    (cvA : ConLeche.ConstantVal) (jty jv : ExprC) : CheckCM ConLeche.FEnv := do
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC lfe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  recordCConst cvA.name cvA.type jty none
  let jvt ← (coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv
  unless ← (coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in opaque {cvA.name}")
  pure (lfe.push (.axiomInfo cvA))

open ConLeche.Cached in
/-- `checkDefnValC`'s tail, run. -/
theorem defnValCTail_run {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty jv jvt : ExprC} {hint : ConLeche.ReducibilityHint}
    {lst lst1 lst2 lst3 : CState}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = true)
    (h2 : constsResolveFC lfe jv = true)
    (hrec : (recordCConst cvA.name cvA.type jty (some (jv, jv))).run lst = .ok ((), lst1))
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv).run lst1
      = .ok (jvt, lst2))
    (hdef : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty).run lst2
      = .ok (true, lst3)) :
    (defnValCTail mode lfe cvA jty jv hint).run lst
      = .ok (lfe.push (.defnInfo cvA jv hint), lst3) := by
  rw [defnValCTail]
  simp only [h1, h2, reduceIte, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]
  rw [show (recordCConst cvA.name cvA.type jty (some (jv, jv))) lst
      = Except.ok ((), lst1) from hrec]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv) lst1
      = Except.ok (jvt, lst2) from hinf]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty) lst2
      = Except.ok (true, lst3) from hdef]
  rfl

open ConLeche.Cached in
/-- `checkThmValC`'s tail, run. -/
theorem thmValCTail_run {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value jv jvt : ExprC}
    {lst lst1 lst2 lst3 : CState}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = true)
    (h2 : constsResolveFC lfe jv = true)
    (hrec : (recordCConst cvA.name cvA.type jty none).run lst = .ok ((), lst1))
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv).run lst1
      = .ok (jvt, lst2))
    (hdef : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty).run lst2
      = .ok (true, lst3)) :
    (thmValCTail mode lfe cvA jty value jv).run lst
      = .ok (lfe.push (.thmInfo cvA value), lst3) := by
  rw [thmValCTail]
  simp only [h1, h2, reduceIte, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]
  rw [show (recordCConst cvA.name cvA.type jty none) lst = Except.ok ((), lst1) from hrec]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv) lst1
      = Except.ok (jvt, lst2) from hinf]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty) lst2
      = Except.ok (true, lst3) from hdef]
  rfl

open ConLeche.Cached in
/-- `checkOpaqueValC`'s tail, run. -/
theorem opaqueValCTail_run {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty jv jvt : ExprC} {lst lst1 lst2 lst3 : CState}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = true)
    (h2 : constsResolveFC lfe jv = true)
    (hrec : (recordCConst cvA.name cvA.type jty none).run lst = .ok ((), lst1))
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv).run lst1
      = .ok (jvt, lst2))
    (hdef : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty).run lst2
      = .ok (true, lst3)) :
    (opaqueValCTail mode lfe cvA jty jv).run lst
      = .ok (lfe.push (.axiomInfo cvA), lst3) := by
  rw [opaqueValCTail]
  simp only [h1, h2, reduceIte, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]
  rw [show (recordCConst cvA.name cvA.type jty none) lst = Except.ok ((), lst1) from hrec]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv) lst1
      = Except.ok (jvt, lst2) from hinf]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty) lst2
      = Except.ok (true, lst3) from hdef]
  rfl

open ConLeche.Cached in
/-- `checkDefnValC` at a run whose two scope guards passed and whose annotation
succeeded: it *is* the tail, on the post-annotation state. -/
theorem checkDefnValC_at_annot {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value jv : ExprC}
    {hint : ConLeche.ReducibilityHint} {lst lst1 : CState}
    (h1 : ExprC.looseBVarsBounded 0 value = true)
    (h2 : ExprC.hasFvar value = false)
    (hann : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 value).run lst
      = .ok (jv, lst1)) :
    (checkDefnValC (absMode mode) lfe cvA jty value hint).run lst
      = (defnValCTail mode lfe cvA jty jv hint).run lst1 := by
  rw [checkDefnValC, defnValCTail]
  simp only [h1, h2, Bool.false_eq_true, if_false, if_true, StateT.run,
    Bind.bind, StateT.bind, Except.bind, Pure.pure]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 value) lst
      = Except.ok (jv, lst1) from hann]
  rfl

open ConLeche.Cached in
/-- `checkOpaqueValC` at such a run. -/
theorem checkOpaqueValC_at_annot {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value jv : ExprC} {lst lst1 : CState}
    (h1 : ExprC.looseBVarsBounded 0 value = true)
    (h2 : ExprC.hasFvar value = false)
    (hann : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 value).run lst
      = .ok (jv, lst1)) :
    (checkOpaqueValC (absMode mode) lfe cvA jty value).run lst
      = (opaqueValCTail mode lfe cvA jty jv).run lst1 := by
  rw [checkOpaqueValC, opaqueValCTail]
  simp only [h1, h2, Bool.false_eq_true, if_false, if_true, StateT.run,
    Bind.bind, StateT.bind, Except.bind, Pure.pure]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 value) lst
      = Except.ok (jv, lst1) from hann]
  rfl

open ConLeche.Cached in
/-- `checkThmValC` at a run whose is-a-proposition gate passed and whose two
scope guards and annotation succeeded: it *is* the tail. -/
theorem checkThmValC_at_annot {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value jv jsty : ExprC} {ul : ConLeche.Level}
    {lst lsta lstb lstc lst1 : CState}
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty).run lst
      = .ok (jsty, lsta))
    (hsort : (opSIxC (absMode mode) lfe 0 jsty).run lsta = .ok (ul, lstb))
    (hprop : (ConLeche.liftFueled (m := CheckCM) "level comparison"
      (ConLeche.Level.isEquiv ul .zero)).run lstb = .ok (true, lstc))
    (h1 : ExprC.looseBVarsBounded 0 value = true)
    (h2 : ExprC.hasFvar value = false)
    (hann : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 value).run lstc
      = .ok (jv, lst1)) :
    (checkThmValC (absMode mode) lfe cvA jty value).run lst
      = (thmValCTail mode lfe cvA jty value jv).run lst1 := by
  rw [checkThmValC, thmValCTail]
  simp only [h1, h2, Bool.false_eq_true, if_false, if_true, StateT.run, Bind.bind,
    StateT.bind, Except.bind, Pure.pure]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty) lst
      = Except.ok (jsty, lsta) from hinf]
  simp only []
  rw [show (opSIxC (absMode mode) lfe 0 jsty) lsta = Except.ok (ul, lstb) from hsort]
  simp only []
  rw [show (ConLeche.liftFueled (m := CheckCM) "level comparison"
      (ConLeche.Level.isEquiv ul .zero)) lstb = Except.ok (true, lstc) from hprop]
  simp only [if_true, Bind.bind, StateT.bind, Except.bind]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 value) lstc
      = Except.ok (jv, lst1) from hann]
  rfl

/-! #### The three tails' `throw`s, and what they pass on

The three tails have the same four failure shapes (`ParsedC.lean:105-113`,
`:131-138`, `:149-156`): the two syntactic guards on the annotated value, the
inference, and the comparison — which can throw or answer `false`, and the
`false` is the tail's own `throw`.  Task #67's failure halves are closed by
these; there is no other error site in the cited tails. -/

open ConLeche.Cached in
/-- `defnValCTail`'s universe-parameter `throw`. -/
theorem defnValCTail_lp_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty jv : ExprC} {hint : ConLeche.ReducibilityHint}
    {lst : CState}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = false) :
    (defnValCTail mode lfe cvA jty jv hint).run lst
      = .error (.invalid s!"undeclared universe parameter in value of {cvA.name}") := by
  rw [defnValCTail]
  simp only [h1, Bool.false_eq_true, if_false, StateT.run, Bind.bind, StateT.bind,
    Except.bind]
  rfl

open ConLeche.Cached in
/-- `defnValCTail`'s resolution `throw`. -/
theorem defnValCTail_resolve_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty jv : ExprC} {hint : ConLeche.ReducibilityHint}
    {lst : CState}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = true)
    (h2 : constsResolveFC lfe jv = false) :
    (defnValCTail mode lfe cvA jty jv hint).run lst
      = .error (.invalid s!"unknown constant in value of {cvA.name}") := by
  rw [defnValCTail]
  simp only [h1, h2, Bool.false_eq_true, if_false, if_true, StateT.run, Bind.bind,
    StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `defnValCTail` passes on what the value's inference threw. -/
theorem defnValCTail_infer_err {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty jv : ExprC} {hint : ConLeche.ReducibilityHint}
    {lst lst1 : CState} {le : ConLeche.CheckError}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = true)
    (h2 : constsResolveFC lfe jv = true)
    (hrec : (recordCConst cvA.name cvA.type jty (some (jv, jv))).run lst = .ok ((), lst1))
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv).run lst1
      = .error le) :
    (defnValCTail mode lfe cvA jty jv hint).run lst = .error le := by
  rw [defnValCTail]
  simp only [h1, h2, reduceIte, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]
  rw [show (recordCConst cvA.name cvA.type jty (some (jv, jv))) lst
      = Except.ok ((), lst1) from hrec]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv) lst1
      = Except.error le from hinf]

open ConLeche.Cached in
/-- `defnValCTail` passes on what the comparison threw. -/
theorem defnValCTail_defeq_err {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty jv jvt : ExprC} {hint : ConLeche.ReducibilityHint}
    {lst lst1 lst2 : CState} {le : ConLeche.CheckError}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = true)
    (h2 : constsResolveFC lfe jv = true)
    (hrec : (recordCConst cvA.name cvA.type jty (some (jv, jv))).run lst = .ok ((), lst1))
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv).run lst1
      = .ok (jvt, lst2))
    (hdef : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty).run lst2
      = .error le) :
    (defnValCTail mode lfe cvA jty jv hint).run lst = .error le := by
  rw [defnValCTail]
  simp only [h1, h2, reduceIte, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]
  rw [show (recordCConst cvA.name cvA.type jty (some (jv, jv))) lst
      = Except.ok ((), lst1) from hrec]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv) lst1
      = Except.ok (jvt, lst2) from hinf]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty) lst2
      = Except.error le from hdef]

open ConLeche.Cached in
/-- `defnValCTail`'s type-mismatch `throw`. -/
theorem defnValCTail_mismatch_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty jv jvt : ExprC} {hint : ConLeche.ReducibilityHint}
    {lst lst1 lst2 lst3 : CState}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = true)
    (h2 : constsResolveFC lfe jv = true)
    (hrec : (recordCConst cvA.name cvA.type jty (some (jv, jv))).run lst = .ok ((), lst1))
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv).run lst1
      = .ok (jvt, lst2))
    (hdef : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty).run lst2
      = .ok (false, lst3)) :
    (defnValCTail mode lfe cvA jty jv hint).run lst
      = .error (.invalid s!"type mismatch in definition {cvA.name}") := by
  rw [defnValCTail]
  simp only [h1, h2, reduceIte, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]
  rw [show (recordCConst cvA.name cvA.type jty (some (jv, jv))) lst
      = Except.ok ((), lst1) from hrec]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv) lst1
      = Except.ok (jvt, lst2) from hinf]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty) lst2
      = Except.ok (false, lst3) from hdef]
  rfl

open ConLeche.Cached in
/-- `thmValCTail`'s universe-parameter `throw`. -/
theorem thmValCTail_lp_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value jv : ExprC} {lst : CState}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = false) :
    (thmValCTail mode lfe cvA jty value jv).run lst
      = .error (.invalid s!"undeclared universe parameter in value of {cvA.name}") := by
  rw [thmValCTail]
  simp only [h1, Bool.false_eq_true, if_false, StateT.run, Bind.bind, StateT.bind,
    Except.bind]
  rfl

open ConLeche.Cached in
/-- `thmValCTail`'s resolution `throw`. -/
theorem thmValCTail_resolve_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value jv : ExprC} {lst : CState}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = true)
    (h2 : constsResolveFC lfe jv = false) :
    (thmValCTail mode lfe cvA jty value jv).run lst
      = .error (.invalid s!"unknown constant in value of {cvA.name}") := by
  rw [thmValCTail]
  simp only [h1, h2, Bool.false_eq_true, if_false, if_true, StateT.run, Bind.bind,
    StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `thmValCTail` passes on what the value's inference threw. -/
theorem thmValCTail_infer_err {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value jv : ExprC} {lst lst1 : CState}
    {le : ConLeche.CheckError}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = true)
    (h2 : constsResolveFC lfe jv = true)
    (hrec : (recordCConst cvA.name cvA.type jty none).run lst = .ok ((), lst1))
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv).run lst1
      = .error le) :
    (thmValCTail mode lfe cvA jty value jv).run lst = .error le := by
  rw [thmValCTail]
  simp only [h1, h2, reduceIte, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]
  rw [show (recordCConst cvA.name cvA.type jty none) lst = Except.ok ((), lst1) from hrec]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv) lst1
      = Except.error le from hinf]

open ConLeche.Cached in
/-- `thmValCTail` passes on what the comparison threw. -/
theorem thmValCTail_defeq_err {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value jv jvt : ExprC} {lst lst1 lst2 : CState}
    {le : ConLeche.CheckError}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = true)
    (h2 : constsResolveFC lfe jv = true)
    (hrec : (recordCConst cvA.name cvA.type jty none).run lst = .ok ((), lst1))
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv).run lst1
      = .ok (jvt, lst2))
    (hdef : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty).run lst2
      = .error le) :
    (thmValCTail mode lfe cvA jty value jv).run lst = .error le := by
  rw [thmValCTail]
  simp only [h1, h2, reduceIte, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]
  rw [show (recordCConst cvA.name cvA.type jty none) lst = Except.ok ((), lst1) from hrec]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv) lst1
      = Except.ok (jvt, lst2) from hinf]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty) lst2
      = Except.error le from hdef]

open ConLeche.Cached in
/-- `thmValCTail`'s type-mismatch `throw`. -/
theorem thmValCTail_mismatch_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value jv jvt : ExprC}
    {lst lst1 lst2 lst3 : CState}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = true)
    (h2 : constsResolveFC lfe jv = true)
    (hrec : (recordCConst cvA.name cvA.type jty none).run lst = .ok ((), lst1))
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv).run lst1
      = .ok (jvt, lst2))
    (hdef : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty).run lst2
      = .ok (false, lst3)) :
    (thmValCTail mode lfe cvA jty value jv).run lst
      = .error (.invalid s!"type mismatch in theorem {cvA.name}") := by
  rw [thmValCTail]
  simp only [h1, h2, reduceIte, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]
  rw [show (recordCConst cvA.name cvA.type jty none) lst = Except.ok ((), lst1) from hrec]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv) lst1
      = Except.ok (jvt, lst2) from hinf]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty) lst2
      = Except.ok (false, lst3) from hdef]
  rfl

open ConLeche.Cached in
/-- `opaqueValCTail`'s universe-parameter `throw`. -/
theorem opaqueValCTail_lp_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty jv : ExprC} {lst : CState}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = false) :
    (opaqueValCTail mode lfe cvA jty jv).run lst
      = .error (.invalid s!"undeclared universe parameter in value of {cvA.name}") := by
  rw [opaqueValCTail]
  simp only [h1, Bool.false_eq_true, if_false, StateT.run, Bind.bind, StateT.bind,
    Except.bind]
  rfl

open ConLeche.Cached in
/-- `opaqueValCTail`'s resolution `throw`. -/
theorem opaqueValCTail_resolve_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty jv : ExprC} {lst : CState}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = true)
    (h2 : constsResolveFC lfe jv = false) :
    (opaqueValCTail mode lfe cvA jty jv).run lst
      = .error (.invalid s!"unknown constant in value of {cvA.name}") := by
  rw [opaqueValCTail]
  simp only [h1, h2, Bool.false_eq_true, if_false, if_true, StateT.run, Bind.bind,
    StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `opaqueValCTail` passes on what the value's inference threw. -/
theorem opaqueValCTail_infer_err {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty jv : ExprC} {lst lst1 : CState}
    {le : ConLeche.CheckError}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = true)
    (h2 : constsResolveFC lfe jv = true)
    (hrec : (recordCConst cvA.name cvA.type jty none).run lst = .ok ((), lst1))
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv).run lst1
      = .error le) :
    (opaqueValCTail mode lfe cvA jty jv).run lst = .error le := by
  rw [opaqueValCTail]
  simp only [h1, h2, reduceIte, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]
  rw [show (recordCConst cvA.name cvA.type jty none) lst = Except.ok ((), lst1) from hrec]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv) lst1
      = Except.error le from hinf]

open ConLeche.Cached in
/-- `opaqueValCTail` passes on what the comparison threw. -/
theorem opaqueValCTail_defeq_err {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty jv jvt : ExprC} {lst lst1 lst2 : CState}
    {le : ConLeche.CheckError}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = true)
    (h2 : constsResolveFC lfe jv = true)
    (hrec : (recordCConst cvA.name cvA.type jty none).run lst = .ok ((), lst1))
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv).run lst1
      = .ok (jvt, lst2))
    (hdef : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty).run lst2
      = .error le) :
    (opaqueValCTail mode lfe cvA jty jv).run lst = .error le := by
  rw [opaqueValCTail]
  simp only [h1, h2, reduceIte, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]
  rw [show (recordCConst cvA.name cvA.type jty none) lst = Except.ok ((), lst1) from hrec]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv) lst1
      = Except.ok (jvt, lst2) from hinf]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty) lst2
      = Except.error le from hdef]

open ConLeche.Cached in
/-- `opaqueValCTail`'s type-mismatch `throw`. -/
theorem opaqueValCTail_mismatch_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty jv jvt : ExprC} {lst lst1 lst2 lst3 : CState}
    (h1 : ExprC.allLevelParamsDefined cvA.levelParams jv = true)
    (h2 : constsResolveFC lfe jv = true)
    (hrec : (recordCConst cvA.name cvA.type jty none).run lst = .ok ((), lst1))
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv).run lst1
      = .ok (jvt, lst2))
    (hdef : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty).run lst2
      = .ok (false, lst3)) :
    (opaqueValCTail mode lfe cvA jty jv).run lst
      = .error (.invalid s!"type mismatch in opaque {cvA.name}") := by
  rw [opaqueValCTail]
  simp only [h1, h2, reduceIte, StateT.run, Bind.bind, StateT.bind, Except.bind,
    Pure.pure, StateT.pure, Except.pure]
  rw [show (recordCConst cvA.name cvA.type jty none) lst = Except.ok ((), lst1) from hrec]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jv) lst1
      = Except.ok (jvt, lst2) from hinf]
  simp only []
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).defeq 0 jvt jty) lst2
      = Except.ok (false, lst3) from hdef]
  rfl

open ConLeche.Cached in
/-- `checkDefnValC`'s loose-bound-variable `throw`
(`ConLeche/Cached/ParsedC.lean:100-101`). -/
theorem checkDefnValC_loose_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value : ExprC}
    {hint : ConLeche.ReducibilityHint} {lst : CState}
    (h1 : ExprC.looseBVarsBounded 0 value = false) :
    (checkDefnValC (absMode mode) lfe cvA jty value hint).run lst
      = .error (.invalid s!"loose bound variable in value of {cvA.name}") := by
  rw [checkDefnValC]
  simp only [h1, Bool.false_eq_true, if_false, StateT.run, Bind.bind, StateT.bind,
    Except.bind]
  rfl

open ConLeche.Cached in
/-- `checkDefnValC`'s free-variable `throw` (`ConLeche/Cached/ParsedC.lean:102-103`). -/
theorem checkDefnValC_fvar_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value : ExprC}
    {hint : ConLeche.ReducibilityHint} {lst : CState}
    (h1 : ExprC.looseBVarsBounded 0 value = true)
    (h2 : ExprC.hasFvar value = true) :
    (checkDefnValC (absMode mode) lfe cvA jty value hint).run lst
      = .error (.invalid s!"unexpected free variable in value of {cvA.name}") := by
  rw [checkDefnValC]
  simp only [h1, h2, if_true, StateT.run, Bind.bind, StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `checkDefnValC` passes on what the value's annotation threw. -/
theorem checkDefnValC_annot_err {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value : ExprC}
    {hint : ConLeche.ReducibilityHint} {lst : CState} {le : ConLeche.CheckError}
    (h1 : ExprC.looseBVarsBounded 0 value = true)
    (h2 : ExprC.hasFvar value = false)
    (hann : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 value).run lst
      = .error le) :
    (checkDefnValC (absMode mode) lfe cvA jty value hint).run lst = .error le := by
  rw [checkDefnValC]
  simp only [h1, h2, Bool.false_eq_true, if_false, if_true, StateT.run, Bind.bind,
    StateT.bind, Except.bind]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 value) lst
      = Except.error le from hann]

open ConLeche.Cached in
/-- `checkOpaqueValC`'s loose-bound-variable `throw`
(`ConLeche/Cached/ParsedC.lean:144-145`). -/
theorem checkOpaqueValC_loose_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value : ExprC} {lst : CState}
    (h1 : ExprC.looseBVarsBounded 0 value = false) :
    (checkOpaqueValC (absMode mode) lfe cvA jty value).run lst
      = .error (.invalid s!"loose bound variable in value of {cvA.name}") := by
  rw [checkOpaqueValC]
  simp only [h1, Bool.false_eq_true, if_false, StateT.run, Bind.bind, StateT.bind,
    Except.bind]
  rfl

open ConLeche.Cached in
/-- `checkOpaqueValC`'s free-variable `throw`. -/
theorem checkOpaqueValC_fvar_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value : ExprC} {lst : CState}
    (h1 : ExprC.looseBVarsBounded 0 value = true)
    (h2 : ExprC.hasFvar value = true) :
    (checkOpaqueValC (absMode mode) lfe cvA jty value).run lst
      = .error (.invalid s!"unexpected free variable in value of {cvA.name}") := by
  rw [checkOpaqueValC]
  simp only [h1, h2, if_true, StateT.run, Bind.bind, StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `checkOpaqueValC` passes on what the value's annotation threw. -/
theorem checkOpaqueValC_annot_err {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value : ExprC} {lst : CState}
    {le : ConLeche.CheckError}
    (h1 : ExprC.looseBVarsBounded 0 value = true)
    (h2 : ExprC.hasFvar value = false)
    (hann : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 value).run lst
      = .error le) :
    (checkOpaqueValC (absMode mode) lfe cvA jty value).run lst = .error le := by
  rw [checkOpaqueValC]
  simp only [h1, h2, Bool.false_eq_true, if_false, if_true, StateT.run, Bind.bind,
    StateT.bind, Except.bind]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 value) lst
      = Except.error le from hann]

/-- **The tail of `cached::parsed_c::check_defn_val_c` past the annotation**
(`ConLeche/Cached/ParsedC.lean:103-112`).

Over the whole outcome (task #67): the port's three `invalid` sites are the
cited tail's own three `throw`s — the two guards on the annotated value and
the type mismatch — and its other two failures are what `infer_type_core` and
`is_def_eq_core` threw. -/
theorem check_defn_val_c_after_annot_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {cv_a : env.ConstantVal}
    {jty jv : expr.Expr} {hint : env.ReducibilityHint}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hjv : ExprWF jv)
    (h : cached.parsed_c.check_defn_val_c_after_annot mode st fe cv_a jty jv hint
      = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lst',
          (defnValCTail mode lfe (absConstantVal cv_a) (absExpr jty) (absExpr jv)
              (absHint hint)).run lst
            = Except.ok
                (lfe.push (.defnInfo (absConstantVal cv_a) (absExpr jv) (absHint hint)),
                 lst')
          ∧ StateRel st' lst' ∧ StateWF st'
          ∧ FEnvRel fe' (lfe.push (.defnInfo (absConstantVal cv_a) (absExpr jv)
              (absHint hint)))
          ∧ FEnvWF fe' ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
      | .Err e =>
        ErrSim e ((defnValCTail mode lfe (absConstantVal cv_a) (absExpr jty)
          (absExpr jv) (absHint hint)).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.parsed_c.check_defn_val_c_after_annot] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbabs := ExprOpsC.all_level_params_defined_refines hcv.2.1 hjv hb
  split at h
  · rename_i hbt; subst hbt
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1abs := StateC.consts_resolve_fc_refines litGuardsRefine hfr hfw hjv hb1
    split at h
    · rename_i hb1t; subst hb1t
      obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e2, he2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨st1, hrec, h⟩ := bind_eq_ok_iff.mp h
      have hnv : n = cv_a.name := by simpa using hn.symm
      have hev : e = cv_a.ty := Expr.dup_eq he
      have he1v : e1 = jty := Expr.dup_eq he1
      have he2v : e2 = jv := Expr.dup_eq he2
      rw [hnv, hev, he1v, he2v] at hrec
      obtain ⟨lst1, hrecrun, hsr1, hsw1⟩ :=
        StateC.record_c_const_refines hsw hcv.1 hcv.2.2 hjty
          (by intro p hp; simp only [Option.some.injEq] at hp; rw [← hp]; exact ⟨hjv, hjv⟩)
          hrec lst hsr
      have hg1 : ConLeche.Cached.ExprC.allLevelParamsDefined (absConstantVal cv_a).levelParams
          (absExpr jv) = true := by rw [absConstantVal_levelParams, ← hbabs]
      have hg2 : ConLeche.Cached.constsResolveFC lfe (absExpr jv) = true := by
        rw [← hb1abs]
      have hgrec : (ConLeche.Cached.recordCConst (absConstantVal cv_a).name
          (absConstantVal cv_a).type (absExpr jty)
          (some (absExpr jv, absExpr jv))).run lst = .ok ((), lst1) := by
        rw [absConstantVal_name, absConstantVal_type]; simpa using hrecrun
      obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r1, st2⟩ := q
      cases r1 with
      | Err er =>
        obtain ⟨hout, -⟩ := err_outS h
        subst hout
        show ErrSim er _
        have herr := (TypeChecker.infer_type_core_refines hfuel hk).err st1 fe 0#u64 jv
          er st2 hsw1 hfw hjv hq lst1 lfe hsr1 hfr
        exact ErrSim.trans herr (fun _ hle =>
          defnValCTail_infer_err hg1 hg2 hgrec hle)
      | Ok jvt =>
        obtain ⟨lst2, hrun2, hsr2, hsw2, hjvtwf⟩ :=
          (TypeChecker.infer_type_core_refines hfuel hk).ok st1 fe 0#u64 jv jvt st2
            hsw1 hfw hjv hq lst1 lfe hsr1 hfr
        obtain ⟨q2, hq2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r2, st3⟩ := q2
        cases r2 with
        | Err er =>
          obtain ⟨hout, -⟩ := err_outS h
          subst hout
          show ErrSim er _
          have herr := (TypeChecker.is_def_eq_core_refines hfuel hk).err st2 fe 0#u64
            jvt jty er st3 hsw2 hfw hjvtwf hjty hq2 lst2 lfe hsr2 hfr
          exact ErrSim.trans herr (fun _ hle =>
            defnValCTail_defeq_err hg1 hg2 hgrec hrun2 hle)
        | Ok ok1 =>
          obtain ⟨lst3, hrun3, hsr3, hsw3⟩ :=
            (TypeChecker.is_def_eq_core_refines hfuel hk).ok st2 fe 0#u64 jvt jty ok1 st3
              hsw2 hfw hjvtwf hjty hq2 lst2 lfe hsr2 hfr
          cases ok1 with
          | false =>
            -- the type-mismatch `throw` (`ParsedC.lean:112-113`)
            obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hout, -⟩ := err_outS h
            subst hout
            show ErrSim ce _
            exact errSim_invalid hce rfl
              (defnValCTail_mismatch_throw hg1 hg2 hgrec hrun2 hrun3)
          | true =>
            simp only [] at h
            obtain ⟨cv, hcvd, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨rh, hrhd, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hout, rfl⟩ := ok_outS h
            subst hout
            have hcvv : cv = cv_a := Env.constant_val_dup_refines hcvd
            have hrhv : rh = hint := Env.reducibility_hint_dup_refines hrhd
            subst hcvv; subst hrhv
            obtain ⟨hrel', hwf'⟩ := FEnv.push_refines hfr hfw
              (show ConstantInfoWF (env.ConstantInfo.DefnInfo cv jv rh) from ⟨hcv, hjv⟩) hpush
            obtain ⟨hcan', hfull'⟩ := FEnv.push_canon hfw
              (show ConstantInfoWF (env.ConstantInfo.DefnInfo cv jv rh) from ⟨hcv, hjv⟩)
              hcan hfull hpush
            refine ⟨lst3, ?_, hsr3, hsw3, hrel', hwf', hcan', hfull'⟩
            exact defnValCTail_run hg1 hg2 hgrec hrun2 hrun3
    · -- the resolution guard declined: `ParsedC.lean:107-108`'s own `throw`
      rename_i hb1f
      obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hout, -⟩ := err_outS h
      subst hout
      show ErrSim ce _
      exact errSim_invalid hce rfl
        (defnValCTail_resolve_throw (lst := lst)
          (by rw [absConstantVal_levelParams, ← hbabs])
          (by rw [← hb1abs]; simpa using hb1f))
  · -- the universe-parameter guard declined: `ParsedC.lean:105-106`'s own `throw`
    rename_i hbf
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim ce _
    exact errSim_invalid hce rfl
      (defnValCTail_lp_throw (lst := lst)
        (by rw [absConstantVal_levelParams, ← hbabs]; simpa using hbf))

/-- `check_defn_val_c_after_annot_refines` at a success, the pre-#67 statement. -/
theorem check_defn_val_c_after_annot_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {cv_a : env.ConstantVal}
    {jty jv : expr.Expr} {hint : env.ReducibilityHint}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hjv : ExprWF jv)
    (h : cached.parsed_c.check_defn_val_c_after_annot mode st fe cv_a jty jv hint
      = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (defnValCTail mode lfe (absConstantVal cv_a) (absExpr jty) (absExpr jv)
            (absHint hint)).run lst
          = Except.ok
              (lfe.push (.defnInfo (absConstantVal cv_a) (absExpr jv) (absHint hint)),
               lst')
        ∧ StateRel st' lst' ∧ StateWF st'
        ∧ FEnvRel fe' (lfe.push (.defnInfo (absConstantVal cv_a) (absExpr jv)
            (absHint hint)))
        ∧ FEnvWF fe' ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  check_defn_val_c_after_annot_refines hfuel hk hsw hfw hcan hfull hcv hjty hjv h

/-- **`cached::parsed_c::check_defn_val_c` refines `checkDefnValC`**
(`ConLeche/Cached/ParsedC.lean:97-112`). -/
theorem check_defn_val_c_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {cv_a : env.ConstantVal}
    {jty value : expr.Expr} {hint : env.ReducibilityHint}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hv : ExprWF value)
    (h : cached.parsed_c.check_defn_val_c mode st fe cv_a jty value hint
      = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ (lst' : ConLeche.Cached.CState) (ci : ConLeche.ConstantInfo),
          (ConLeche.Cached.checkDefnValC (absMode mode) lfe (absConstantVal cv_a)
              (absExpr jty) (absExpr value) (absHint hint)).run lst
            = Except.ok (lfe.push ci, lst')
          ∧ ci.name = (absConstantVal cv_a).name
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' (lfe.push ci) ∧ FEnvWF fe'
          ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
      | .Err e =>
        ErrSim e ((ConLeche.Cached.checkDefnValC (absMode mode) lfe (absConstantVal cv_a)
          (absExpr jty) (absExpr value) (absHint hint)).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.parsed_c.check_defn_val_c] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbabs := ExprOpsC.loose_bvars_bounded_refines hv hb
  rw [show ((0#u64 : Std.U64)).val = 0 from rfl] at hbabs
  split at h
  · rename_i hbt; subst hbt
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1abs := ExprOpsC.has_fvar_refines hv hb1
    split at h
    · -- the free-variable `throw` (`ParsedC.lean:102-103`)
      rename_i hb1t
      obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v, hv1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hout, -⟩ := err_outS h
      subst hout
      show ErrSim ce _
      exact errSim_invalid hce rfl
        (checkDefnValC_fvar_throw (cvA := absConstantVal cv_a) (jty := absExpr jty)
          (hint := absHint hint) (lst := lst)
          (by rw [← hbabs]) (by rw [← hb1abs]; exact hb1t))
    · rename_i hb1f
      obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r1, st1⟩ := q
      cases r1 with
      | Err er =>
        obtain ⟨hout, -⟩ := err_outS h
        subst hout
        show ErrSim er _
        have herr := (TypeChecker.annotate_core_refines hfuel hk).err st fe 0#u64 value
          er st1 hsw hfw hv hq lst lfe hsr hfr
        exact ErrSim.trans herr (fun _ hle =>
          checkDefnValC_annot_err (cvA := absConstantVal cv_a) (jty := absExpr jty)
            (hint := absHint hint) (by rw [← hbabs])
            (by rw [← hb1abs]; simpa using hb1f) hle)
      | Ok jv =>
        obtain ⟨lst1, hrun1, hsr1, hsw1, hjvwf⟩ :=
          (TypeChecker.annotate_core_refines hfuel hk).ok st fe 0#u64 value jv st1
            hsw hfw hv hq lst lfe hsr hfr
        have hrest :=
          check_defn_val_c_after_annot_refines hfuel hk hsw1 hfw hcan hfull hcv hjty
            hjvwf h lst1 lfe hsr1 hfr
        have hhead : (ConLeche.Cached.checkDefnValC (absMode mode) lfe
              (absConstantVal cv_a) (absExpr jty) (absExpr value) (absHint hint)).run lst
            = (defnValCTail mode lfe (absConstantVal cv_a) (absExpr jty) (absExpr jv)
                (absHint hint)).run lst1 :=
          checkDefnValC_at_annot (cvA := absConstantVal cv_a) (by rw [← hbabs])
            (by rw [← hb1abs]; simpa using hb1f) hrun1
        cases out with
        | Ok fe' =>
          obtain ⟨lst2, hrun2, rest⟩ := hrest
          exact ⟨lst2, .defnInfo (absConstantVal cv_a) (absExpr jv) (absHint hint),
            by rw [hhead]; exact hrun2, rfl, rest⟩
        | Err e =>
          show ErrSim e _
          rw [hhead]
          exact hrest
  · -- the loose-bound-variable `throw` (`ParsedC.lean:100-101`)
    rename_i hbf
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, hv1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim ce _
    exact errSim_invalid hce rfl
      (checkDefnValC_loose_throw (cvA := absConstantVal cv_a) (jty := absExpr jty)
        (hint := absHint hint) (lst := lst)
        (by rw [← hbabs]; simpa using hbf))

/-- `check_defn_val_c_refines` at a success, the pre-#67 statement. -/
theorem check_defn_val_c_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {cv_a : env.ConstantVal}
    {jty value : expr.Expr} {hint : env.ReducibilityHint}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hv : ExprWF value)
    (h : cached.parsed_c.check_defn_val_c mode st fe cv_a jty value hint
      = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ (lst' : ConLeche.Cached.CState) (ci : ConLeche.ConstantInfo),
        (ConLeche.Cached.checkDefnValC (absMode mode) lfe (absConstantVal cv_a)
            (absExpr jty) (absExpr value) (absHint hint)).run lst
          = Except.ok (lfe.push ci, lst')
        ∧ ci.name = (absConstantVal cv_a).name
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' (lfe.push ci) ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  check_defn_val_c_refines hfuel hk hsw hfw hcan hfull hcv hjty hv h

/-- **The tail of `cached::parsed_c::check_opaque_val_c` past the annotation**
(`ConLeche/Cached/ParsedC.lean:147-156`). -/
theorem check_opaque_val_c_after_annot_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {cv_a : env.ConstantVal}
    {jty jv : expr.Expr}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hjv : ExprWF jv)
    (h : cached.parsed_c.check_opaque_val_c_after_annot mode st fe cv_a jty jv
      = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lst',
          (opaqueValCTail mode lfe (absConstantVal cv_a) (absExpr jty)
              (absExpr jv)).run lst
            = Except.ok (lfe.push (.axiomInfo (absConstantVal cv_a)), lst')
          ∧ StateRel st' lst' ∧ StateWF st'
          ∧ FEnvRel fe' (lfe.push (.axiomInfo (absConstantVal cv_a))) ∧ FEnvWF fe'
          ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
      | .Err e =>
        ErrSim e ((opaqueValCTail mode lfe (absConstantVal cv_a) (absExpr jty)
          (absExpr jv)).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.parsed_c.check_opaque_val_c_after_annot] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbabs := ExprOpsC.all_level_params_defined_refines hcv.2.1 hjv hb
  split at h
  · rename_i hbt; subst hbt
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1abs := StateC.consts_resolve_fc_refines litGuardsRefine hfr hfw hjv hb1
    split at h
    · rename_i hb1t; subst hb1t
      obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨st1, hrec, h⟩ := bind_eq_ok_iff.mp h
      have hnv : n = cv_a.name := by simpa using hn.symm
      have hev : e = cv_a.ty := Expr.dup_eq he
      have he1v : e1 = jty := Expr.dup_eq he1
      rw [hnv, hev, he1v] at hrec
      obtain ⟨lst1, hrecrun, hsr1, hsw1⟩ :=
        StateC.record_c_const_refines hsw hcv.1 hcv.2.2 hjty (by simp) hrec lst hsr
      have hg1 : ConLeche.Cached.ExprC.allLevelParamsDefined (absConstantVal cv_a).levelParams
          (absExpr jv) = true := by rw [absConstantVal_levelParams, ← hbabs]
      have hg2 : ConLeche.Cached.constsResolveFC lfe (absExpr jv) = true := by
        rw [← hb1abs]
      have hgrec : (ConLeche.Cached.recordCConst (absConstantVal cv_a).name
          (absConstantVal cv_a).type (absExpr jty) none).run lst = .ok ((), lst1) := by
        rw [absConstantVal_name, absConstantVal_type]; simpa using hrecrun
      obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r1, st2⟩ := q
      cases r1 with
      | Err er =>
        obtain ⟨hout, -⟩ := err_outS h
        subst hout
        show ErrSim er _
        have herr := (TypeChecker.infer_type_core_refines hfuel hk).err st1 fe 0#u64 jv
          er st2 hsw1 hfw hjv hq lst1 lfe hsr1 hfr
        exact ErrSim.trans herr (fun _ hle =>
          opaqueValCTail_infer_err hg1 hg2 hgrec hle)
      | Ok jvt =>
        obtain ⟨lst2, hrun2, hsr2, hsw2, hjvtwf⟩ :=
          (TypeChecker.infer_type_core_refines hfuel hk).ok st1 fe 0#u64 jv jvt st2
            hsw1 hfw hjv hq lst1 lfe hsr1 hfr
        obtain ⟨q2, hq2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r2, st3⟩ := q2
        cases r2 with
        | Err er =>
          obtain ⟨hout, -⟩ := err_outS h
          subst hout
          show ErrSim er _
          have herr := (TypeChecker.is_def_eq_core_refines hfuel hk).err st2 fe 0#u64
            jvt jty er st3 hsw2 hfw hjvtwf hjty hq2 lst2 lfe hsr2 hfr
          exact ErrSim.trans herr (fun _ hle =>
            opaqueValCTail_defeq_err hg1 hg2 hgrec hrun2 hle)
        | Ok ok1 =>
          obtain ⟨lst3, hrun3, hsr3, hsw3⟩ :=
            (TypeChecker.is_def_eq_core_refines hfuel hk).ok st2 fe 0#u64 jvt jty ok1 st3
              hsw2 hfw hjvtwf hjty hq2 lst2 lfe hsr2 hfr
          cases ok1 with
          | false =>
            obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hout, -⟩ := err_outS h
            subst hout
            show ErrSim ce _
            exact errSim_invalid hce rfl
              (opaqueValCTail_mismatch_throw hg1 hg2 hgrec hrun2 hrun3)
          | true =>
            simp only [] at h
            obtain ⟨cv, hcvd, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hout, rfl⟩ := ok_outS h
            subst hout
            have hcvv : cv = cv_a := Env.constant_val_dup_refines hcvd
            subst hcvv
            obtain ⟨hrel', hwf'⟩ := FEnv.push_refines hfr hfw
              (show ConstantInfoWF (env.ConstantInfo.AxiomInfo cv) from hcv) hpush
            obtain ⟨hcan', hfull'⟩ := FEnv.push_canon hfw
              (show ConstantInfoWF (env.ConstantInfo.AxiomInfo cv) from hcv) hcan hfull hpush
            refine ⟨lst3, ?_, hsr3, hsw3, hrel', hwf', hcan', hfull'⟩
            exact opaqueValCTail_run hg1 hg2 hgrec hrun2 hrun3
    · rename_i hb1f
      obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hout, -⟩ := err_outS h
      subst hout
      show ErrSim ce _
      exact errSim_invalid hce rfl
        (opaqueValCTail_resolve_throw (lst := lst)
          (by rw [absConstantVal_levelParams, ← hbabs])
          (by rw [← hb1abs]; simpa using hb1f))
  · rename_i hbf
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim ce _
    exact errSim_invalid hce rfl
      (opaqueValCTail_lp_throw (lst := lst)
        (by rw [absConstantVal_levelParams, ← hbabs]; simpa using hbf))

/-- `check_opaque_val_c_after_annot_refines` at a success, the pre-#67
statement. -/
theorem check_opaque_val_c_after_annot_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {cv_a : env.ConstantVal}
    {jty jv : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hjv : ExprWF jv)
    (h : cached.parsed_c.check_opaque_val_c_after_annot mode st fe cv_a jty jv
      = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (opaqueValCTail mode lfe (absConstantVal cv_a) (absExpr jty) (absExpr jv)).run lst
          = Except.ok (lfe.push (.axiomInfo (absConstantVal cv_a)), lst')
        ∧ StateRel st' lst' ∧ StateWF st'
        ∧ FEnvRel fe' (lfe.push (.axiomInfo (absConstantVal cv_a))) ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  check_opaque_val_c_after_annot_refines hfuel hk hsw hfw hcan hfull hcv hjty hjv h

/-- **`cached::parsed_c::check_opaque_val_c` refines `checkOpaqueValC`**
(`ConLeche/Cached/ParsedC.lean:141-156`). -/
theorem check_opaque_val_c_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {cv_a : env.ConstantVal}
    {jty value : expr.Expr}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hv : ExprWF value)
    (h : cached.parsed_c.check_opaque_val_c mode st fe cv_a jty value
      = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ (lst' : ConLeche.Cached.CState) (ci : ConLeche.ConstantInfo),
          (ConLeche.Cached.checkOpaqueValC (absMode mode) lfe (absConstantVal cv_a)
              (absExpr jty) (absExpr value)).run lst = Except.ok (lfe.push ci, lst')
          ∧ ci.name = (absConstantVal cv_a).name
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' (lfe.push ci) ∧ FEnvWF fe'
          ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
      | .Err e =>
        ErrSim e ((ConLeche.Cached.checkOpaqueValC (absMode mode) lfe
          (absConstantVal cv_a) (absExpr jty) (absExpr value)).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.parsed_c.check_opaque_val_c] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbabs := ExprOpsC.loose_bvars_bounded_refines hv hb
  rw [show ((0#u64 : Std.U64)).val = 0 from rfl] at hbabs
  split at h
  · rename_i hbt; subst hbt
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1abs := ExprOpsC.has_fvar_refines hv hb1
    split at h
    · rename_i hb1t
      obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v, hv1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hout, -⟩ := err_outS h
      subst hout
      show ErrSim ce _
      exact errSim_invalid hce rfl
        (checkOpaqueValC_fvar_throw (cvA := absConstantVal cv_a) (jty := absExpr jty)
          (lst := lst) (by rw [← hbabs]) (by rw [← hb1abs]; exact hb1t))
    · rename_i hb1f
      obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r1, st1⟩ := q
      cases r1 with
      | Err er =>
        obtain ⟨hout, -⟩ := err_outS h
        subst hout
        show ErrSim er _
        have herr := (TypeChecker.annotate_core_refines hfuel hk).err st fe 0#u64 value
          er st1 hsw hfw hv hq lst lfe hsr hfr
        exact ErrSim.trans herr (fun _ hle =>
          checkOpaqueValC_annot_err (cvA := absConstantVal cv_a) (jty := absExpr jty)
            (by rw [← hbabs]) (by rw [← hb1abs]; simpa using hb1f) hle)
      | Ok jv =>
        obtain ⟨lst1, hrun1, hsr1, hsw1, hjvwf⟩ :=
          (TypeChecker.annotate_core_refines hfuel hk).ok st fe 0#u64 value jv st1
            hsw hfw hv hq lst lfe hsr hfr
        have hrest :=
          check_opaque_val_c_after_annot_refines hfuel hk hsw1 hfw hcan hfull hcv hjty
            hjvwf h lst1 lfe hsr1 hfr
        have hhead : (ConLeche.Cached.checkOpaqueValC (absMode mode) lfe
              (absConstantVal cv_a) (absExpr jty) (absExpr value)).run lst
            = (opaqueValCTail mode lfe (absConstantVal cv_a) (absExpr jty)
                (absExpr jv)).run lst1 :=
          checkOpaqueValC_at_annot (cvA := absConstantVal cv_a) (by rw [← hbabs])
            (by rw [← hb1abs]; simpa using hb1f) hrun1
        cases out with
        | Ok fe' =>
          obtain ⟨lst2, hrun2, rest⟩ := hrest
          exact ⟨lst2, .axiomInfo (absConstantVal cv_a), by rw [hhead]; exact hrun2,
            rfl, rest⟩
        | Err e =>
          show ErrSim e _
          rw [hhead]
          exact hrest
  · rename_i hbf
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, hv1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim ce _
    exact errSim_invalid hce rfl
      (checkOpaqueValC_loose_throw (cvA := absConstantVal cv_a) (jty := absExpr jty)
        (lst := lst) (by rw [← hbabs]; simpa using hbf))

/-- `check_opaque_val_c_refines` at a success, the pre-#67 statement. -/
theorem check_opaque_val_c_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {cv_a : env.ConstantVal}
    {jty value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hv : ExprWF value)
    (h : cached.parsed_c.check_opaque_val_c mode st fe cv_a jty value
      = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ (lst' : ConLeche.Cached.CState) (ci : ConLeche.ConstantInfo),
        (ConLeche.Cached.checkOpaqueValC (absMode mode) lfe (absConstantVal cv_a)
            (absExpr jty) (absExpr value)).run lst = Except.ok (lfe.push ci, lst')
        ∧ ci.name = (absConstantVal cv_a).name
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' (lfe.push ci) ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  check_opaque_val_c_refines hfuel hk hsw hfw hcan hfull hcv hjty hv h

open ConLeche.Cached in
/-- `core_k::lift_fueled`'s failure arm, run in `CheckCM`
(`ConLeche/Kernel/Core.lean:109-111 liftFueled`): `none` is an `internal`
error on both sides. -/
theorem lift_fueled_run_err {o : Option Bool} {ce : core_types.CheckError}
    {lst : CState} (h : core_k.lift_fueled o = ok (.Err ce)) :
    ErrSim ce ((ConLeche.liftFueled (m := CheckCM) "level comparison" o).run lst) := by
  cases o with
  | some a =>
    simp only [core_k.lift_fueled] at h
    exact absurd h (by simp)
  | none =>
    simp only [core_k.lift_fueled, bind_eq_ok_iff] at h
    obtain ⟨s, hs, v, hv, ce1, hce1, hr⟩ := h
    have hce : ce1 = ce := by simpa using hr
    exact errSim_internal hce1 hce rfl

open ConLeche.Cached in
/-- `checkThmValC` passes on what the statement's inference threw. -/
theorem checkThmValC_infer_err {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value : ExprC} {lst : CState}
    {le : ConLeche.CheckError}
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty).run lst
      = .error le) :
    (checkThmValC (absMode mode) lfe cvA jty value).run lst = .error le := by
  rw [checkThmValC]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty) lst
      = Except.error le from hinf]

open ConLeche.Cached in
/-- `checkThmValC` passes on what the statement's sort check threw. -/
theorem checkThmValC_sort_err {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value jsty : ExprC} {lst lsta : CState}
    {le : ConLeche.CheckError}
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty).run lst
      = .ok (jsty, lsta))
    (hsort : (opSIxC (absMode mode) lfe 0 jsty).run lsta = .error le) :
    (checkThmValC (absMode mode) lfe cvA jty value).run lst = .error le := by
  rw [checkThmValC]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty) lst
      = Except.ok (jsty, lsta) from hinf]
  simp only []
  rw [show (opSIxC (absMode mode) lfe 0 jsty) lsta = Except.error le from hsort]

open ConLeche.Cached in
/-- `checkThmValC` passes on what the fuel-lift threw. -/
theorem checkThmValC_lift_err {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value jsty : ExprC} {ul : ConLeche.Level}
    {lst lsta lstb : CState} {le : ConLeche.CheckError}
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty).run lst
      = .ok (jsty, lsta))
    (hsort : (opSIxC (absMode mode) lfe 0 jsty).run lsta = .ok (ul, lstb))
    (hprop : (ConLeche.liftFueled (m := CheckCM) "level comparison"
      (ConLeche.Level.isEquiv ul .zero)).run lstb = .error le) :
    (checkThmValC (absMode mode) lfe cvA jty value).run lst = .error le := by
  rw [checkThmValC]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty) lst
      = Except.ok (jsty, lsta) from hinf]
  simp only []
  rw [show (opSIxC (absMode mode) lfe 0 jsty) lsta = Except.ok (ul, lstb) from hsort]
  simp only []
  rw [show (ConLeche.liftFueled (m := CheckCM) "level comparison"
      (ConLeche.Level.isEquiv ul .zero)) lstb = Except.error le from hprop]

open ConLeche.Cached in
/-- `checkThmValC`'s is-a-proposition `throw` (`ParsedC.lean:124-125`). -/
theorem checkThmValC_notprop_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value jsty : ExprC} {ul : ConLeche.Level}
    {lst lsta lstb lstc : CState}
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty).run lst
      = .ok (jsty, lsta))
    (hsort : (opSIxC (absMode mode) lfe 0 jsty).run lsta = .ok (ul, lstb))
    (hprop : (ConLeche.liftFueled (m := CheckCM) "level comparison"
      (ConLeche.Level.isEquiv ul .zero)).run lstb = .ok (false, lstc)) :
    (checkThmValC (absMode mode) lfe cvA jty value).run lst
      = .error (.invalid s!"type of theorem {cvA.name} is not a proposition") := by
  rw [checkThmValC]
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty) lst
      = Except.ok (jsty, lsta) from hinf]
  simp only []
  rw [show (opSIxC (absMode mode) lfe 0 jsty) lsta = Except.ok (ul, lstb) from hsort]
  simp only []
  rw [show (ConLeche.liftFueled (m := CheckCM) "level comparison"
      (ConLeche.Level.isEquiv ul .zero)) lstb = Except.ok (false, lstc) from hprop]
  simp only [Bool.false_eq_true, if_false]
  rfl

open ConLeche.Cached in
/-- `checkThmValC`'s loose-bound-variable `throw` (`ParsedC.lean:126-127`). -/
theorem checkThmValC_loose_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value jsty : ExprC} {ul : ConLeche.Level}
    {lst lsta lstb lstc : CState}
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty).run lst
      = .ok (jsty, lsta))
    (hsort : (opSIxC (absMode mode) lfe 0 jsty).run lsta = .ok (ul, lstb))
    (hprop : (ConLeche.liftFueled (m := CheckCM) "level comparison"
      (ConLeche.Level.isEquiv ul .zero)).run lstb = .ok (true, lstc))
    (h1 : ExprC.looseBVarsBounded 0 value = false) :
    (checkThmValC (absMode mode) lfe cvA jty value).run lst
      = .error (.invalid s!"loose bound variable in value of {cvA.name}") := by
  rw [checkThmValC]
  simp only [h1, Bool.false_eq_true, if_false, StateT.run, Bind.bind, StateT.bind,
    Except.bind]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty) lst
      = Except.ok (jsty, lsta) from hinf]
  simp only []
  rw [show (opSIxC (absMode mode) lfe 0 jsty) lsta = Except.ok (ul, lstb) from hsort]
  simp only []
  rw [show (ConLeche.liftFueled (m := CheckCM) "level comparison"
      (ConLeche.Level.isEquiv ul .zero)) lstb = Except.ok (true, lstc) from hprop]
  simp only [if_true, Bind.bind, StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `checkThmValC`'s free-variable `throw` (`ParsedC.lean:128-129`). -/
theorem checkThmValC_fvar_throw {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value jsty : ExprC} {ul : ConLeche.Level}
    {lst lsta lstb lstc : CState}
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty).run lst
      = .ok (jsty, lsta))
    (hsort : (opSIxC (absMode mode) lfe 0 jsty).run lsta = .ok (ul, lstb))
    (hprop : (ConLeche.liftFueled (m := CheckCM) "level comparison"
      (ConLeche.Level.isEquiv ul .zero)).run lstb = .ok (true, lstc))
    (h1 : ExprC.looseBVarsBounded 0 value = true)
    (h2 : ExprC.hasFvar value = true) :
    (checkThmValC (absMode mode) lfe cvA jty value).run lst
      = .error (.invalid s!"unexpected free variable in value of {cvA.name}") := by
  rw [checkThmValC]
  simp only [h1, h2, if_true, StateT.run, Bind.bind, StateT.bind, Except.bind]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty) lst
      = Except.ok (jsty, lsta) from hinf]
  simp only []
  rw [show (opSIxC (absMode mode) lfe 0 jsty) lsta = Except.ok (ul, lstb) from hsort]
  simp only []
  rw [show (ConLeche.liftFueled (m := CheckCM) "level comparison"
      (ConLeche.Level.isEquiv ul .zero)) lstb = Except.ok (true, lstc) from hprop]
  simp only [if_true, Bind.bind, StateT.bind, Except.bind]
  rfl

open ConLeche.Cached in
/-- `checkThmValC` passes on what the witness's annotation threw. -/
theorem checkThmValC_annot_err {mode : env.CheckMode} {lfe : ConLeche.FEnv}
    {cvA : ConLeche.ConstantVal} {jty value jsty : ExprC} {ul : ConLeche.Level}
    {lst lsta lstb lstc : CState} {le : ConLeche.CheckError}
    (hinf : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty).run lst
      = .ok (jsty, lsta))
    (hsort : (opSIxC (absMode mode) lfe 0 jsty).run lsta = .ok (ul, lstb))
    (hprop : (ConLeche.liftFueled (m := CheckCM) "level comparison"
      (ConLeche.Level.isEquiv ul .zero)).run lstb = .ok (true, lstc))
    (h1 : ExprC.looseBVarsBounded 0 value = true)
    (h2 : ExprC.hasFvar value = false)
    (hann : ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 value).run lstc
      = .error le) :
    (checkThmValC (absMode mode) lfe cvA jty value).run lst = .error le := by
  rw [checkThmValC]
  simp only [h1, h2, Bool.false_eq_true, if_false, if_true, StateT.run, Bind.bind,
    StateT.bind, Except.bind, Pure.pure]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).infer 0 jty) lst
      = Except.ok (jsty, lsta) from hinf]
  simp only []
  rw [show (opSIxC (absMode mode) lfe 0 jsty) lsta = Except.ok (ul, lstb) from hsort]
  simp only []
  rw [show (ConLeche.liftFueled (m := CheckCM) "level comparison"
      (ConLeche.Level.isEquiv ul .zero)) lstb = Except.ok (true, lstc) from hprop]
  simp only [if_true, Bind.bind, StateT.bind, Except.bind]
  rw [show ((coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0 value) lstc
      = Except.error le from hann]

/-- **The tail of `cached::parsed_c::check_thm_val_c` past the annotation**
(`ConLeche/Cached/ParsedC.lean:126-137`): a theorem is stored by its statement,
so the record keeps the parse's own `value`. -/
theorem check_thm_val_c_checked_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {cv_a : env.ConstantVal}
    {jty value jv : expr.Expr}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hval : ExprWF value) (hjv : ExprWF jv)
    (h : cached.parsed_c.check_thm_val_c_checked mode st fe cv_a jty value jv
      = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lst',
          (thmValCTail mode lfe (absConstantVal cv_a) (absExpr jty) (absExpr value)
              (absExpr jv)).run lst
            = Except.ok (lfe.push (.thmInfo (absConstantVal cv_a) (absExpr value)), lst')
          ∧ StateRel st' lst' ∧ StateWF st'
          ∧ FEnvRel fe' (lfe.push (.thmInfo (absConstantVal cv_a) (absExpr value)))
          ∧ FEnvWF fe' ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
      | .Err e =>
        ErrSim e ((thmValCTail mode lfe (absConstantVal cv_a) (absExpr jty)
          (absExpr value) (absExpr jv)).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.parsed_c.check_thm_val_c_checked] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbabs := ExprOpsC.all_level_params_defined_refines hcv.2.1 hjv hb
  split at h
  · rename_i hbt; subst hbt
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1abs := StateC.consts_resolve_fc_refines litGuardsRefine hfr hfw hjv hb1
    split at h
    · rename_i hb1t; subst hb1t
      obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨st1, hrec, h⟩ := bind_eq_ok_iff.mp h
      have hnv : n = cv_a.name := by simpa using hn.symm
      have hev : e = cv_a.ty := Expr.dup_eq he
      have he1v : e1 = jty := Expr.dup_eq he1
      rw [hnv, hev, he1v] at hrec
      obtain ⟨lst1, hrecrun, hsr1, hsw1⟩ :=
        StateC.record_c_const_refines hsw hcv.1 hcv.2.2 hjty (by simp) hrec lst hsr
      have hg1 : ConLeche.Cached.ExprC.allLevelParamsDefined (absConstantVal cv_a).levelParams
          (absExpr jv) = true := by rw [absConstantVal_levelParams, ← hbabs]
      have hg2 : ConLeche.Cached.constsResolveFC lfe (absExpr jv) = true := by
        rw [← hb1abs]
      have hgrec : (ConLeche.Cached.recordCConst (absConstantVal cv_a).name
          (absConstantVal cv_a).type (absExpr jty) none).run lst = .ok ((), lst1) := by
        rw [absConstantVal_name, absConstantVal_type]; simpa using hrecrun
      obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r1, st2⟩ := q
      cases r1 with
      | Err er =>
        obtain ⟨hout, -⟩ := err_outS h
        subst hout
        show ErrSim er _
        have herr := (TypeChecker.infer_type_core_refines hfuel hk).err st1 fe 0#u64 jv
          er st2 hsw1 hfw hjv hq lst1 lfe hsr1 hfr
        exact ErrSim.trans herr (fun _ hle => thmValCTail_infer_err hg1 hg2 hgrec hle)
      | Ok jvt =>
        obtain ⟨lst2, hrun2, hsr2, hsw2, hjvtwf⟩ :=
          (TypeChecker.infer_type_core_refines hfuel hk).ok st1 fe 0#u64 jv jvt st2
            hsw1 hfw hjv hq lst1 lfe hsr1 hfr
        obtain ⟨q2, hq2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r2, st3⟩ := q2
        cases r2 with
        | Err er =>
          obtain ⟨hout, -⟩ := err_outS h
          subst hout
          show ErrSim er _
          have herr := (TypeChecker.is_def_eq_core_refines hfuel hk).err st2 fe 0#u64
            jvt jty er st3 hsw2 hfw hjvtwf hjty hq2 lst2 lfe hsr2 hfr
          exact ErrSim.trans herr (fun _ hle =>
            thmValCTail_defeq_err hg1 hg2 hgrec hrun2 hle)
        | Ok ok1 =>
          obtain ⟨lst3, hrun3, hsr3, hsw3⟩ :=
            (TypeChecker.is_def_eq_core_refines hfuel hk).ok st2 fe 0#u64 jvt jty ok1 st3
              hsw2 hfw hjvtwf hjty hq2 lst2 lfe hsr2 hfr
          cases ok1 with
          | false =>
            obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hout, -⟩ := err_outS h
            subst hout
            show ErrSim ce _
            exact errSim_invalid hce rfl
              (thmValCTail_mismatch_throw hg1 hg2 hgrec hrun2 hrun3)
          | true =>
            simp only [] at h
            obtain ⟨cv, hcvd, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨e2, he2, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hout, rfl⟩ := ok_outS h
            subst hout
            have hcvv : cv = cv_a := Env.constant_val_dup_refines hcvd
            have he2v : e2 = value := Expr.dup_eq he2
            subst hcvv; subst he2v
            obtain ⟨hrel', hwf'⟩ := FEnv.push_refines hfr hfw
              (show ConstantInfoWF (env.ConstantInfo.ThmInfo cv e2) from ⟨hcv, hval⟩) hpush
            obtain ⟨hcan', hfull'⟩ := FEnv.push_canon hfw
              (show ConstantInfoWF (env.ConstantInfo.ThmInfo cv e2) from ⟨hcv, hval⟩)
              hcan hfull hpush
            refine ⟨lst3, ?_, hsr3, hsw3, hrel', hwf', hcan', hfull'⟩
            exact thmValCTail_run hg1 hg2 hgrec hrun2 hrun3
    · rename_i hb1f
      obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hout, -⟩ := err_outS h
      subst hout
      show ErrSim ce _
      exact errSim_invalid hce rfl
        (thmValCTail_resolve_throw (lst := lst)
          (by rw [absConstantVal_levelParams, ← hbabs])
          (by rw [← hb1abs]; simpa using hb1f))
  · rename_i hbf
    obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim ce _
    exact errSim_invalid hce rfl
      (thmValCTail_lp_throw (lst := lst)
        (by rw [absConstantVal_levelParams, ← hbabs]; simpa using hbf))

/-- `check_thm_val_c_checked_refines` at a success, the pre-#67 statement. -/
theorem check_thm_val_c_checked_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {cv_a : env.ConstantVal}
    {jty value jv : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hval : ExprWF value) (hjv : ExprWF jv)
    (h : cached.parsed_c.check_thm_val_c_checked mode st fe cv_a jty value jv
      = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (thmValCTail mode lfe (absConstantVal cv_a) (absExpr jty) (absExpr value)
            (absExpr jv)).run lst
          = Except.ok (lfe.push (.thmInfo (absConstantVal cv_a) (absExpr value)), lst')
        ∧ StateRel st' lst' ∧ StateWF st'
        ∧ FEnvRel fe' (lfe.push (.thmInfo (absConstantVal cv_a) (absExpr value)))
        ∧ FEnvWF fe' ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  check_thm_val_c_checked_refines hfuel hk hsw hfw hcan hfull hcv hjty hval hjv h

/-- **`cached::parsed_c::check_thm_val_c` refines `checkThmValC`**
(`ConLeche/Cached/ParsedC.lean:118-137`): the statement's sort, the
is-a-proposition gate, then the witness's guards, annotation and check. -/
theorem check_thm_val_c_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {cv_a : env.ConstantVal}
    {jty value : expr.Expr}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hv : ExprWF value)
    (h : cached.parsed_c.check_thm_val_c mode st fe cv_a jty value = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (ConLeche.Cached.checkThmValC (absMode mode) lfe (absConstantVal cv_a)
              (absExpr jty) (absExpr value)).run lst = Except.ok (lfe', lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
      | .Err e =>
        ErrSim e ((ConLeche.Cached.checkThmValC (absMode mode) lfe (absConstantVal cv_a)
          (absExpr jty) (absExpr value)).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.parsed_c.check_thm_val_c] at h
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r1, sta⟩ := q
  cases r1 with
  | Err er =>
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim er _
    have herr := (TypeChecker.infer_type_core_refines hfuel hk).err st fe 0#u64 jty
      er sta hsw hfw hjty hq lst lfe hsr hfr
    exact ErrSim.trans herr (fun _ hle => checkThmValC_infer_err hle)
  | Ok jsty =>
    obtain ⟨lsta, hruna, hsra, hswa, hjstywf⟩ :=
      (TypeChecker.infer_type_core_refines hfuel hk).ok st fe 0#u64 jty jsty sta
        hsw hfw hjty hq lst lfe hsr hfr
    obtain ⟨q2, hq2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r2, stb⟩ := q2
    cases r2 with
    | Err er =>
      obtain ⟨hout, -⟩ := err_outS h
      subst hout
      show ErrSim er _
      have herr := (TypeChecker.ensure_sort_core_refines hfuel hk).err sta fe 0#u64 jsty
        er stb hswa hfw hjstywf
        (hq2 : type_checker.ensure_sort_core mode sta fe 0#u64 jsty = ok (.Err er, stb))
        lsta lfe hsra hfr
      exact ErrSim.trans herr (fun _ hle => checkThmValC_sort_err hruna hle)
    | Ok ul =>
      obtain ⟨lstb, hrunb, hsrb, hswb, hulwf⟩ :=
        (TypeChecker.ensure_sort_core_refines hfuel hk).ok sta fe 0#u64 jsty ul stb
          hswa hfw hjstywf
          (hq2 : type_checker.ensure_sort_core mode sta fe 0#u64 jsty = ok (.Ok ul, stb))
          lsta lfe hsra hfr
      obtain ⟨z, hz, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r3, hr3, h⟩ := bind_eq_ok_iff.mp h
      have hoabs := Level.is_equiv_refines hulwf (Level.zero_wf hz) ho
      rw [Level.zero_refines hz] at hoabs
      cases r3 with
      | Err er =>
        -- the fuel-lift's `internal`, mirrored (`ConLeche/Kernel/Core.lean:109-111`)
        obtain ⟨hout, -⟩ := err_outS h
        subst hout
        show ErrSim er _
        have herr : ErrSim er ((ConLeche.liftFueled (m := ConLeche.Cached.CheckCM)
            "level comparison" (ConLeche.Level.isEquiv (absLevel ul) .zero)).run lstb) := by
          rw [hoabs]; exact lift_fueled_run_err hr3
        exact ErrSim.trans herr (fun _ hle => checkThmValC_lift_err hruna hrunb hle)
      | Ok is_prop =>
        cases is_prop with
        | false =>
          -- the is-a-proposition `throw` (`ParsedC.lean:124-125`)
          obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v, hv1, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hout, -⟩ := err_outS h
          subst hout
          have hprop : (ConLeche.liftFueled (m := ConLeche.Cached.CheckCM)
              "level comparison" (ConLeche.Level.isEquiv (absLevel ul) .zero)).run lstb
              = .ok (false, lstb) := by rw [hoabs]; exact lift_fueled_run hr3
          show ErrSim ce _
          exact errSim_invalid hce rfl
            (checkThmValC_notprop_throw (cvA := absConstantVal cv_a) hruna hrunb hprop)
        | true =>
          simp only [if_pos] at h
          have hprop : (ConLeche.liftFueled (m := ConLeche.Cached.CheckCM)
              "level comparison" (ConLeche.Level.isEquiv (absLevel ul) .zero)).run lstb
              = .ok (true, lstb) := by rw [hoabs]; exact lift_fueled_run hr3
          rw [cached.parsed_c.check_thm_val_c_witness] at h
          obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
          have hbabs := ExprOpsC.loose_bvars_bounded_refines hv hb
          rw [show ((0#u64 : Std.U64)).val = 0 from rfl] at hbabs
          split at h
          · rename_i hbt; subst hbt
            obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
            have hb1abs := ExprOpsC.has_fvar_refines hv hb1
            split at h
            · -- the free-variable `throw` (`ParsedC.lean:128-129`)
              rename_i hb1t
              obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨v, hv1, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨hout, -⟩ := err_outS h
              subst hout
              show ErrSim ce _
              exact errSim_invalid hce rfl
                (checkThmValC_fvar_throw (cvA := absConstantVal cv_a) hruna hrunb hprop
                  (by rw [← hbabs]) (by rw [← hb1abs]; exact hb1t))
            · rename_i hb1f
              obtain ⟨q3, hq3, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨r4, stc⟩ := q3
              cases r4 with
              | Err er =>
                obtain ⟨hout, -⟩ := err_outS h
                subst hout
                show ErrSim er _
                have herr := (TypeChecker.annotate_core_refines hfuel hk).err stb fe
                  0#u64 value er stc hswb hfw hv hq3 lstb lfe hsrb hfr
                exact ErrSim.trans herr (fun _ hle =>
                  checkThmValC_annot_err (cvA := absConstantVal cv_a) hruna hrunb hprop
                    (by rw [← hbabs]) (by rw [← hb1abs]; simpa using hb1f) hle)
              | Ok jv =>
                obtain ⟨lstc, hrunc, hsrc, hswc, hjvwf⟩ :=
                  (TypeChecker.annotate_core_refines hfuel hk).ok stb fe 0#u64 value jv stc
                    hswb hfw hv hq3 lstb lfe hsrb hfr
                have hrest :=
                  check_thm_val_c_checked_refines hfuel hk hswc hfw hcan hfull hcv hjty
                    hv hjvwf h lstc lfe hsrc hfr
                have hhead : (ConLeche.Cached.checkThmValC (absMode mode) lfe
                      (absConstantVal cv_a) (absExpr jty) (absExpr value)).run lst
                    = (thmValCTail mode lfe (absConstantVal cv_a) (absExpr jty)
                        (absExpr value) (absExpr jv)).run lstc :=
                  checkThmValC_at_annot (cvA := absConstantVal cv_a) hruna hrunb hprop
                    (by rw [← hbabs]) (by rw [← hb1abs]; simpa using hb1f) hrunc
                cases out with
                | Ok fe' =>
                  obtain ⟨lst2, hrun2, rest⟩ := hrest
                  exact ⟨lst2, _, by rw [hhead]; exact hrun2, rest⟩
                | Err e =>
                  show ErrSim e _
                  rw [hhead]
                  exact hrest
          · -- the loose-bound-variable `throw` (`ParsedC.lean:126-127`)
            rename_i hbf
            obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨v, hv1, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hout, -⟩ := err_outS h
            subst hout
            show ErrSim ce _
            exact errSim_invalid hce rfl
              (checkThmValC_loose_throw (cvA := absConstantVal cv_a) hruna hrunb hprop
                (by rw [← hbabs]; simpa using hbf))

/-- `check_thm_val_c_refines` at a success, the pre-#67 statement. -/
theorem check_thm_val_c_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {cv_a : env.ConstantVal}
    {jty value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hv : ExprWF value)
    (h : cached.parsed_c.check_thm_val_c mode st fe cv_a jty value = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkThmValC (absMode mode) lfe (absConstantVal cv_a)
            (absExpr jty) (absExpr value)).run lst = Except.ok (lfe', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  check_thm_val_c_refines hfuel hk hsw hfw hcan hfull hcv hjty hv h

/-! ### The four value arms of `checkDeclC`

`cached/parsed_c.rs`'s parsed twins of `Refine/Checker.lean`'s: the same
checks with `checkConstantValC`'s recorded judgement type threaded (the
`(cvA, jty)` pair `recordCConst` consumes) and the pinned-name test *before*
the push, which is the cited arm's own RC-linearity shape.  Stated here so
that `check_decl_c_refines` is a `cases`; their bodies belong with
`cached::parsed_c`, which `CORE_PLAN.md` step 7 places after this file. -/

/-! ### The pin gates hand the index back unchanged (task #59)

`checker::check_defn_pins` and the two halves it dispatches to
(`crates/con-ron-core/src/kernel/checker.rs`, lines 1128-1350) certify at the
*pre-insertion* view and then restore the caller's own counter: each accepting
path is `fenv::restrict_to fe k_pre` followed by
`fenv::restrict_to fe_pre fe.visible_below`, a round trip that rebuilds the
record it started from.  So the pushed index the defn arm hands the gates comes
back out, and with it `FEnv.FEnvCanon`/`FEnv.FEnvFull` — which is what
`Refine/IndSpec.lean`'s `IndRoutesSpec` asks the declaration fold to carry. -/

/-- `ConLeche/Kernel/FEnv.lean:79-80` — `fenv::restrict_to` is the one-field
record update, read as an equation on its result. -/
theorem restrict_to_eq {fe fe' : fenv.FEnv} {k : Std.U64}
    (h : fenv.restrict_to fe k = ok fe') : fe' = { fe with visible_below := k } :=
  (Result.ok_injective h).symm

/-- Down to a bound and back up to the caller's own counter is the identity. -/
theorem restrict_round {fe fe' fe'' : fenv.FEnv} {k : Std.U64}
    (h1 : fenv.restrict_to fe k = ok fe')
    (h2 : fenv.restrict_to fe' fe.visible_below = ok fe'') : fe'' = fe := by
  rw [restrict_to_eq h2, restrict_to_eq h1]

/-- `checker::check_div_mod_pin` (`kernel/checker.rs:1128-1163`) accepts with
the index it was given. -/
theorem check_div_mod_pin_fenv {mode : env.CheckMode}
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet} {st st' : cached.state_c.CState}
    {fe fe' : fenv.FEnv} {k_pre : Std.U64} {c : name.Name}
    (h : checker.check_div_mod_pin mode pins st fe k_pre c = ok (.Ok fe', st')) :
    fe' = fe := by
  rw [checker.check_div_mod_pin] at h
  obtain ⟨b, -, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨o, -, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | none => simp [bind_eq_ok_iff] at h
    | some t =>
      obtain ⟨_, value2, _⟩ := t
      obtain ⟨fe_pre, hpre, h⟩ := bind_eq_ok_iff.mp h
      -- task #67: the loop now takes its decline text as an argument, so two
      -- binds build it (`Array.to_slice`, `code_points`) before the call
      obtain ⟨sl, _, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨msg, _, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨q, -, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := q
      cases r with
      | Err er => simp at h
      | Ok _ =>
        obtain ⟨f, hf, h⟩ := bind_eq_ok_iff.mp h
        have hround := restrict_round hpre hf
        simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
        rw [← h.1, hround]
  · simp [bind_eq_ok_iff] at h

/-- `checker::check_structural_nat_pin` (`kernel/checker.rs:1381-1421`) accepts
with the index it was given. -/
theorem check_structural_nat_pin_fenv {mode : env.CheckMode}
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {k_pre : Std.U64}
    {n : name.Name}
    (h : checker.check_structural_nat_pin mode st fe k_pre n = ok (.Ok fe', st')) :
    fe' = fe := by
  rw [checker.check_structural_nat_pin] at h
  obtain ⟨b, -, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨v, -, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · obtain ⟨o, -, h⟩ := bind_eq_ok_iff.mp h
      cases o with
      | none => simp [bind_eq_ok_iff] at h
      | some t =>
        obtain ⟨_, value2, _⟩ := t
        obtain ⟨v1, -, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨eqs, -, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨fe_pre, hpre, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨q, -, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r, st1⟩ := q
        obtain ⟨fe21, hf, h⟩ := bind_eq_ok_iff.mp h
        have hround := restrict_round hpre hf
        cases r with
        | Err er => simp at h
        | Ok ok1 =>
          cases ok1 with
          | false => simp [bind_eq_ok_iff] at h
          | true =>
            simp only [if_pos, Result.ok.injEq, Prod.mk.injEq,
              core.result.Result.Ok.injEq] at h
            rw [← h.1, hround]
    · simp [bind_eq_ok_iff] at h
  · simp [bind_eq_ok_iff] at h

/-- `checker::check_defn_div_mod_pin` (`kernel/checker.rs:1355-1368`) accepts
with the index it was given: the gate either runs `check_div_mod_pin` or is
skipped outright. -/
theorem check_defn_div_mod_pin_fenv {mode : env.CheckMode}
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet} {st st' : cached.state_c.CState}
    {fe fe' : fenv.FEnv} {k_pre : Std.U64} {n : name.Name}
    (h : checker.check_defn_div_mod_pin mode pins st fe k_pre n = ok (.Ok fe', st')) :
    fe' = fe := by
  rw [checker.check_defn_div_mod_pin] at h
  obtain ⟨v, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, -, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · exact check_div_mod_pin_fenv h
  · simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
    exact h.1.symm

/-- `checker::check_reduce_pin` (`kernel/checker.rs:1302-1329`) accepts with the
index it was given: the same pre-insertion round trip. -/
theorem check_reduce_pin_fenv {mode : env.CheckMode} {st st' : cached.state_c.CState}
    {fe fe' : fenv.FEnv} {k_pre : Std.U64} {c : name.Name} {value : expr.Expr}
    (h : checker.check_reduce_pin mode st fe k_pre c value = ok (.Ok fe', st')) :
    fe' = fe := by
  rw [checker.check_reduce_pin] at h
  obtain ⟨b, -, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨fe_pre, hpre, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨q, -, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r, st1⟩ := q
    cases r with
    | Err er => simp at h
    | Ok _ =>
      obtain ⟨f, hf, h⟩ := bind_eq_ok_iff.mp h
      have hround := restrict_round hpre hf
      simp only [Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
      rw [← h.1, hround]
  · simp [bind_eq_ok_iff] at h

/-- **`checker::check_defn_pins` accepts with the index it was given**
(`kernel/checker.rs:1334-1350`): the two gates above, composed. -/
theorem check_defn_pins_fenv {mode : env.CheckMode}
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet} {st st' : cached.state_c.CState}
    {fe fe' : fenv.FEnv} {k_pre : Std.U64} {n : name.Name}
    (h : checker.check_defn_pins mode pins st fe k_pre n = ok (.Ok fe', st')) :
    fe' = fe := by
  rw [checker.check_defn_pins] at h
  obtain ⟨v, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, -, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r, st1⟩ := q
    cases r with
    | Err er => simp at h
    | Ok fe3 =>
      rw [← check_structural_nat_pin_fenv hq]
      exact check_defn_div_mod_pin_fenv h
  · exact check_defn_div_mod_pin_fenv h

open ConLeche.Cached in
/-- con-leche's `throw` swallows the rest of a `do` block. -/
theorem throwCM_bind {α β : Type} (e : ConLeche.CheckError) (f : α → CheckCM β) :
    (throw e : CheckCM α) >>= f = throw e := rfl

open ConLeche.Cached in
/-- …and `pure` is the unit. -/
theorem pureCM_bind {α β : Type} (a : α) (f : α → CheckCM β) :
    (pure a : CheckCM α) >>= f = f a := rfl

open ConLeche.Cached in
/-- A `do` step under an `if` distributes over it. -/
theorem ite_bindCM {α β : Type} (c : Prop) [Decidable c] (a b : CheckCM α)
    (f : α → CheckCM β) :
    ((if c then a else b) >>= f) = if c then a >>= f else b >>= f := by
  split <;> rfl

open ConLeche.Cached in
/-- **The `.defnDecl` arm's two pinned-`Nat` gates, as the `do` elaborator
leaves them** (`ConLeche/Cached/ParsedC.lean:164-183`): the cited arm writes
the structural-`Nat` block as *statements*, so the continuation `k` is copied
into every branch (the join point is inlined).  `Refine/CheckerPins.lean`
states the gate's refinement over `defnPinsBlockF`, the same two gates as one
computation; `defnGatesInlined_run` is the bridge. -/
def defnGatesInlined {α : Type} (ops : ConLeche.CheckerOps CheckCM)
    (lfp lfe2 : ConLeche.FEnv) (lenv : ConLeche.Env) (c : ConLeche.Name)
    (k : CheckCM α) : CheckCM α := do
  if ConLeche.natOpNames.contains c then
    unless ConLeche.natOpGuardF lfe2 c
        && (ConLeche.natOpDeps c).all (ConLeche.natOpStoredOkF lfe2) do
      throw (.notImplemented
        s!"nonstandard structural Nat operation environment ({c})")
    match lfe2.find? c with
    | some (.defnInfo _ value' _) =>
      let okb ← ConLeche.certifyNatEqs ops lenv
        ((ConLeche.natOpEquations 0 c).map fun eq =>
          (ConLeche.Expr.substConst0 c value' eq.1,
           ConLeche.Expr.substConst0 c value' eq.2))
      unless okb do
        throw (.notImplemented s!"nonstandard structural Nat operation ({c})")
    | _ => throw (.internal s!"structural Nat operation not stored ({c})")
  if ConLeche.natDivModNames.contains c then
    ConLeche.checkDivModPinF ops lfp lfe2 c
  k

open ConLeche.Cached in
/-- Inlining the join point changes nothing: the arm's tail is
`defnPinsBlockF` followed by the continuation. -/
theorem defnGatesInlined_eq {α : Type} (ops : ConLeche.CheckerOps CheckCM)
    (lfp lfe2 : ConLeche.FEnv) (lenv : ConLeche.Env) (c : ConLeche.Name)
    (k : CheckCM α) :
    defnGatesInlined ops lfp lfe2 lenv c k
      = ((CheckerPins.defnPinsBlockF ops lfp lfe2 lenv c) >>= fun _ => k) := by
  rw [defnGatesInlined, CheckerPins.defnPinsBlockF, CheckerPins.structuralNatBlockF]
  by_cases hn : ConLeche.natOpNames.contains c = true
  · by_cases hg : (ConLeche.natOpGuardF lfe2 c
        && (ConLeche.natOpDeps c).all (ConLeche.natOpStoredOkF lfe2)) = true
    · cases hfind : lfe2.find? c with
      | none => simp only [hn, hg, reduceIte, pureCM_bind, throwCM_bind]
      | some ci =>
        cases ci with
        | defnInfo cvL value2 hintL =>
          simp only [hn, hg, reduceIte, bind_assoc, pureCM_bind]
          congr 1
          funext okb
          cases okb with
          | true => simp only [reduceIte, ite_bindCM, pureCM_bind]
          | false => simp only [Bool.false_eq_true, if_false, throwCM_bind]
        | axiomInfo a => simp only [hn, hg, reduceIte, pureCM_bind, throwCM_bind]
        | thmInfo a b => simp only [hn, hg, reduceIte, pureCM_bind, throwCM_bind]
        | indInfo a b => simp only [hn, hg, reduceIte, pureCM_bind, throwCM_bind]
        | ctorInfo a b d => simp only [hn, hg, reduceIte, pureCM_bind, throwCM_bind]
        | recInfo a b d e => simp only [hn, hg, reduceIte, pureCM_bind, throwCM_bind]
        | projInfo a => simp only [hn, hg, reduceIte, pureCM_bind, throwCM_bind]
    · simp only [Bool.not_eq_true] at hg
      simp only [hn, hg, reduceIte, Bool.false_eq_true, if_false, throwCM_bind]
  · simp only [Bool.not_eq_true] at hn
    simp only [hn, Bool.false_eq_true, if_false, ite_bindCM, pureCM_bind]

/-- `checkDeclC`'s `.defnDecl` arm (`ParsedC.lean:161-185`): the constant
check, the value check, then the two pinned-`Nat` gates at the pre-insertion
bound.

Proved: `check_constant_val_c_refines` and `check_defn_val_c_refines` above for
the constant and value halves, and `Refine/CheckerPins.lean`'s
`check_defn_pins_refines` for both pinned-`Nat` gates at the pre-insertion view
`lfp := fe` — `push_restrict_find` is what says that view answers what `fe`
answers (the pushed constant sits *at* the bound, and the constant check proved
its name fresh). -/
theorem check_defn_decl_c_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr} {hint : env.ReducibilityHint}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : cached.parsed_c.check_defn_decl_c mode pins st fe cv value hint
        = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (ConLeche.Cached.checkDeclC (absMode mode) lfe
              (.defnDecl (absConstantVal cv) (absExpr value) (absHint hint))).run lst
            = Except.ok (lfe', lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
      | .Err e =>
        ErrSim e ((ConLeche.Cached.checkDeclC (absMode mode) lfe
          (.defnDecl (absConstantVal cv) (absExpr value) (absHint hint))).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.parsed_c.check_defn_decl_c] at h
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  cases r with
  | Err er =>
    -- the constant check threw, and the cited arm's first `let …←` throws the
    -- same
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim er _
    have herr := check_constant_val_c_refines hfuel hk hsw hfw hcv hq lst lfe hsr hfr
    exact ErrSim.trans herr (fun _ hle => by
      rw [ConLeche.Cached.checkDeclC]; exact run_bind_err_head hle)
  | Ok p =>
    obtain ⟨cv_a, jty⟩ := p
    obtain ⟨lst1, hruncv, hsr1, hsw1, hcvawf, hjtywf, hnameq, hfresh⟩ :=
      check_constant_val_c_refines hfuel hk hsw hfw hcv hq lst lfe hsr hfr
    -- the two pieces every accepting path shares
    have main : ∀ (st2 : cached.state_c.CState) (fe2 fe' : fenv.FEnv),
        cached.parsed_c.check_defn_val_c mode st1 fe cv_a jty value hint
            = ok (.Ok fe2, st2) →
        cached.parsed_c.check_defn_pins_c mode pins st2 fe2 fe.visible_below cv_a.name
            = ok (.Ok fe', st') →
        ∃ (lst2 lst3 lst4 : ConLeche.Cached.CState) (ci : ConLeche.ConstantInfo),
          (ConLeche.Cached.checkDefnValC (absMode mode) lfe (absConstantVal cv_a)
              (absExpr jty) (absExpr value) (absHint hint)).run lst1
            = .ok (lfe.push ci, lst2)
          ∧ ci.name = (absConstantVal cv_a).name
          ∧ (ConLeche.natOpNames.contains (absConstantVal cv_a).name = true →
              ConLeche.natOpGuardF (lfe.push ci) (absConstantVal cv_a).name = true
              ∧ ((ConLeche.natOpDeps (absConstantVal cv_a).name).all
                  (ConLeche.natOpStoredOkF (lfe.push ci))) = true
              ∧ ∃ (cvL : ConLeche.ConstantVal) (value' : ConLeche.Expr)
                  (hintL : ConLeche.ReducibilityHint),
                  (lfe.push ci).find? (absConstantVal cv_a).name
                      = some (.defnInfo cvL value' hintL)
                  ∧ (ConLeche.certifyNatEqs (TypeChecker.lops mode lfe) lfe.env
                        ((ConLeche.natOpEquations 0 (absConstantVal cv_a).name).map
                          fun eq =>
                            (ConLeche.Expr.substConst0 (absConstantVal cv_a).name value' eq.1,
                             ConLeche.Expr.substConst0 (absConstantVal cv_a).name value'
                               eq.2))).run lst2 = .ok (true, lst3))
          ∧ (ConLeche.natOpNames.contains (absConstantVal cv_a).name = false → lst3 = lst2)
          ∧ ((if ConLeche.natDivModNames.contains (absConstantVal cv_a).name then
                ConLeche.checkDivModPinF (TypeChecker.lops mode lfe) lfe (lfe.push ci)
                  (absConstantVal cv_a).name
              else pure ()) : ConLeche.Cached.CheckCM Unit).run lst3 = .ok ((), lst4)
          ∧ StateRel st' lst4 ∧ StateWF st' ∧ FEnvRel fe' (lfe.push ci) ∧ FEnvWF fe'
          ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' := by
      intro st2 fe2 fe' hval hpin
      obtain ⟨lst2, ci, hrun2, hciname, hsr2, hsw2, hrel2, hwf2, hcan2, hfull2⟩ :=
        check_defn_val_c_refines hfuel hk hsw1 hfw hcan hfull hcvawf hjtywf hv hval
          lst1 lfe hsr1 hfr
      have hcifresh : lfe.find? ci.name = none := by
        rw [hciname, absConstantVal_name, hnameq]; exact hfresh
      have hlfp : lfe.find?
          = ((lfe.push ci).restrictTo (fe.visible_below).val).find? := by
        rw [hfr.2.1, push_restrict_find hcifresh]
      obtain ⟨lst3, lst4, hA, hB, hC, hsr4, hsw4, hrel4, hwf4⟩ :=
        CheckerPins.check_defn_pins_refines hfuel hk hsw2 hwf2 hcvawf.1 hvar hpins
          (hpin : checker.check_defn_pins mode pins st2 fe2 fe.visible_below cv_a.name
            = ok (.Ok fe', st'))
          lst2 (lfe.push ci) lfe hsr2 hrel2
          (fun _ hr => BasisPins.eq_basis_pinned_refines hrel2 hwf2 hr) hlfp
      have hfe' : fe' = fe2 :=
        check_defn_pins_fenv
          (hpin : checker.check_defn_pins mode pins st2 fe2 fe.visible_below cv_a.name
            = ok (.Ok fe', st'))
      refine ⟨lst2, lst3, lst4, ci, hrun2, hciname, ?_, ?_, ?_, hsr4, hsw4, hrel4, hwf4,
        by rw [hfe']; exact hcan2, by rw [hfe']; exact hfull2⟩
      · intro hc
        obtain ⟨hg, hd2, cvL, value', hintL, hfind, hcert⟩ :=
          hA (by rw [← absConstantVal_name]; exact hc)
        rw [absConstantVal_name]
        exact ⟨hg, hd2, cvL, value', hintL, hfind, hcert lfe.env⟩
      · intro hc; exact hB (by rw [← absConstantVal_name]; exact hc)
      · rw [absConstantVal_name]; exact hC
    -- the same when the pin gate threw: `defnPinsBlockF` is the two gates as
    -- one computation, which is exactly the cited arm's inlined tail
    have mainErr : ∀ (st2 : cached.state_c.CState) (fe2 : fenv.FEnv)
        (er : core_types.CheckError),
        (ConLeche.natOpNames.contains (absConstantVal cv_a).name ||
          ConLeche.natDivModNames.contains (absConstantVal cv_a).name) = true →
        cached.parsed_c.check_defn_val_c mode st1 fe cv_a jty value hint
            = ok (.Ok fe2, st2) →
        cached.parsed_c.check_defn_pins_c mode pins st2 fe2 fe.visible_below cv_a.name
            = ok (.Err er, st') →
        ErrSim er ((ConLeche.Cached.checkDeclC (absMode mode) lfe
          (.defnDecl (absConstantVal cv) (absExpr value) (absHint hint))).run lst) := by
      intro st2 fe2 er hcond hval hpin
      obtain ⟨lst2, ci, hrun2, hciname, hsr2, hsw2, hrel2, hwf2, hcan2, hfull2⟩ :=
        check_defn_val_c_refines hfuel hk hsw1 hfw hcan hfull hcvawf hjtywf hv hval
          lst1 lfe hsr1 hfr
      have hcifresh : lfe.find? ci.name = none := by
        rw [hciname, absConstantVal_name, hnameq]; exact hfresh
      have hlfp : lfe.find?
          = ((lfe.push ci).restrictTo (fe.visible_below).val).find? := by
        rw [hfr.2.1, push_restrict_find hcifresh]
      have herr := CheckerPins.check_defn_pins_refines hfuel hk hsw2 hwf2 hcvawf.1 hvar
        hpins
        (hpin : checker.check_defn_pins mode pins st2 fe2 fe.visible_below cv_a.name
          = ok (.Err er, st'))
        lst2 (lfe.push ci) lfe hsr2 hrel2
        (fun _ hr => BasisPins.eq_basis_pinned_refines hrel2 hwf2 hr) hlfp lfe.env
      refine ErrSim.trans herr (fun le hle => ?_)
      rw [ConLeche.Cached.checkDeclC]
      refine run_bind_ok hruncv ?_
      simp only []
      rw [hcond]
      simp only [if_true]
      refine run_bind_ok hrun2 ?_
      show (defnGatesInlined (TypeChecker.lops mode lfe) lfe (lfe.push ci)
          lfe.env (absName cv_a.name) (pure (lfe.push ci))).run lst2 = Except.error le
      rw [defnGatesInlined_eq]
      exact run_bind_err_head hle
    -- the value check threw, in the pinned branch
    have valErr : ∀ (er : core_types.CheckError),
        (ConLeche.natOpNames.contains (absConstantVal cv_a).name ||
          ConLeche.natDivModNames.contains (absConstantVal cv_a).name) = true →
        cached.parsed_c.check_defn_val_c mode st1 fe cv_a jty value hint
            = ok (.Err er, st') →
        ErrSim er ((ConLeche.Cached.checkDeclC (absMode mode) lfe
          (.defnDecl (absConstantVal cv) (absExpr value) (absHint hint))).run lst) := by
      intro er hcond hval
      have herr := check_defn_val_c_refines hfuel hk hsw1 hfw hcan hfull hcvawf hjtywf hv
        hval lst1 lfe hsr1 hfr
      refine ErrSim.trans herr (fun le hle => ?_)
      rw [ConLeche.Cached.checkDeclC]
      refine run_bind_ok hruncv ?_
      simp only []
      rw [hcond]
      simp only [if_true]
      exact run_bind_err_head hle
    -- the `Nat.div`/`Nat.mod` gate, with the arm's `pure fe2` continuation
    have divmod : ∀ (ci : ConLeche.ConstantInfo) (l3 l4 : ConLeche.Cached.CState),
        ((if ConLeche.natDivModNames.contains (absConstantVal cv_a).name then
            ConLeche.checkDivModPinF (TypeChecker.lops mode lfe) lfe (lfe.push ci)
              (absConstantVal cv_a).name
          else pure ()) : ConLeche.Cached.CheckCM Unit).run l3 = .ok ((), l4) →
        ((if ConLeche.natDivModNames.contains (absConstantVal cv_a).name then
            (do ConLeche.checkDivModPinF (TypeChecker.lops mode lfe) lfe (lfe.push ci)
                  (absConstantVal cv_a).name
                pure (lfe.push ci))
          else pure (lfe.push ci)) : ConLeche.Cached.CheckCM ConLeche.FEnv).run l3
          = .ok (lfe.push ci, l4) := by
      intro ci l3 l4 hh
      by_cases hdm : ConLeche.natDivModNames.contains (absConstantVal cv_a).name = true
      · rw [if_pos hdm] at hh ⊢
        exact run_bind_ok hh rfl
      · rw [if_neg hdm] at hh ⊢
        have hl : l4 = l3 := by
          have he : (Except.ok ((), l3) :
              Except ConLeche.CheckError (Unit × ConLeche.Cached.CState)) = .ok ((), l4) := hh
          exact (show l3 = l4 by simpa using he).symm
        rw [hl]; rfl
    -- the port's three-way dispatch on the two name tables
    obtain ⟨nv, hnv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hnvabs, hnvwf⟩ := CoreK.pinned_nat_op_names nv hnv
    have hbv := Name.contains_refines hnvwf hcvawf.1 hb
    rw [hnvabs] at hbv
    cases b with
    | true =>
      have hcond : (ConLeche.natOpNames.contains (absConstantVal cv_a).name ||
          ConLeche.natDivModNames.contains (absConstantVal cv_a).name) = true := by
        rw [absConstantVal_name, ← hbv]; simp
      simp only [if_true] at h
      obtain ⟨q2, hq2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r1, st2⟩ := q2
      cases r1 with
      | Err er =>
        obtain ⟨hout, rfl⟩ := err_outS h
        subst hout
        exact valErr er hcond hq2
      | Ok fe2 =>
        cases out with
        | Err er => exact mainErr st2 fe2 er hcond hq2 h
        | Ok fe' =>
          obtain ⟨lst2, lst3, lst4, ci, hrun2, hciname, hA, hB, hC, rest⟩ :=
            main st2 fe2 fe' hq2 h
          refine ⟨lst4, lfe.push ci, ?_, rest⟩
          rw [ConLeche.Cached.checkDeclC]
          refine run_bind_ok hruncv ?_
          simp only []
          rw [hcond]
          simp only [if_true]
          refine run_bind_ok hrun2 ?_
          have hnat : ConLeche.natOpNames.contains (absConstantVal cv_a).name = true := by
            rw [absConstantVal_name, ← hbv]
          rw [if_pos hnat]
          obtain ⟨hg, hd2, cvL, value', hintL, hfind, hcert⟩ := hA hnat
          rw [if_pos (show (ConLeche.natOpGuardF (lfe.push ci) (absConstantVal cv_a).name &&
            (ConLeche.natOpDeps (absConstantVal cv_a).name).all
              (ConLeche.natOpStoredOkF (lfe.push ci))) = true from by rw [hg, hd2]; rfl), hfind]
          simp only []
          refine run_bind_ok hcert ?_
          simp only [if_true]
          exact divmod ci lst3 lst4 hC
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      have hnat : ConLeche.natOpNames.contains (absConstantVal cv_a).name = false := by
        rw [absConstantVal_name, ← hbv]
      obtain ⟨dv, hdv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hdvabs, hdvwf⟩ := CoreK.pinned_nat_div_mod_names dv hdv
      have hb1v := Name.contains_refines hdvwf hcvawf.1 hb1
      rw [hdvabs] at hb1v
      cases b1 with
      | true =>
        have hcond : (ConLeche.natOpNames.contains (absConstantVal cv_a).name ||
            ConLeche.natDivModNames.contains (absConstantVal cv_a).name) = true := by
          rw [absConstantVal_name, ← hbv, ← hb1v]; simp
        simp only [if_true] at h
        obtain ⟨q2, hq2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r1, st2⟩ := q2
        cases r1 with
        | Err er =>
          obtain ⟨hout, rfl⟩ := err_outS h
          subst hout
          exact valErr er hcond hq2
        | Ok fe2 =>
          cases out with
          | Err er => exact mainErr st2 fe2 er hcond hq2 h
          | Ok fe' =>
            obtain ⟨lst2, lst3, lst4, ci, hrun2, hciname, hA, hB, hC, rest⟩ :=
              main st2 fe2 fe' hq2 h
            refine ⟨lst4, lfe.push ci, ?_, rest⟩
            rw [ConLeche.Cached.checkDeclC]
            refine run_bind_ok hruncv ?_
            simp only []
            rw [hcond]
            simp only [if_true]
            refine run_bind_ok hrun2 ?_
            rw [if_neg (by rw [hnat]; simp)]
            rw [← hB hnat]
            exact divmod ci lst3 lst4 hC
      | false =>
        have hcond : (ConLeche.natOpNames.contains (absConstantVal cv_a).name ||
            ConLeche.natDivModNames.contains (absConstantVal cv_a).name) = false := by
          rw [absConstantVal_name, ← hbv, ← hb1v]; simp
        simp only [Bool.false_eq_true, if_false] at h
        have hrest :=
          check_defn_val_c_refines hfuel hk hsw1 hfw hcan hfull hcvawf hjtywf hv h lst1
            lfe hsr1 hfr
        cases out with
        | Ok fe' =>
          obtain ⟨lst2, ci, hrun2, hciname, rest⟩ := hrest
          refine ⟨lst2, lfe.push ci, ?_, rest⟩
          rw [ConLeche.Cached.checkDeclC]
          refine run_bind_ok hruncv ?_
          simp only []
          rw [hcond]
          simp only [Bool.false_eq_true, if_false]
          exact hrun2
        | Err er =>
          show ErrSim er _
          refine ErrSim.trans hrest (fun le hle => ?_)
          rw [ConLeche.Cached.checkDeclC]
          refine run_bind_ok hruncv ?_
          simp only []
          rw [hcond]
          simp only [Bool.false_eq_true, if_false]
          exact hle

/-- `check_defn_decl_c_refines` at a success, the pre-#67 statement. -/
theorem check_defn_decl_c_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr} {hint : env.ReducibilityHint}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : cached.parsed_c.check_defn_decl_c mode pins st fe cv value hint
        = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkDeclC (absMode mode) lfe
            (.defnDecl (absConstantVal cv) (absExpr value) (absHint hint))).run lst
          = Except.ok (lfe', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  check_defn_decl_c_refines hfuel hk hvar hpins hsw hfw hcan hfull hcv hv h

/-- `checkDeclC`'s `.thmDecl` arm (`ParsedC.lean:186-188`).

Proved: `check_constant_val_c_refines` and `check_thm_val_c_refines` above. -/
theorem check_thm_decl_c_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : cached.parsed_c.check_thm_decl_c mode st fe cv value = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (ConLeche.Cached.checkDeclC (absMode mode) lfe
              (.thmDecl (absConstantVal cv) (absExpr value))).run lst
            = Except.ok (lfe', lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
      | .Err e =>
        ErrSim e ((ConLeche.Cached.checkDeclC (absMode mode) lfe
          (.thmDecl (absConstantVal cv) (absExpr value))).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.parsed_c.check_thm_decl_c] at h
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  cases r with
  | Err er =>
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim er _
    have herr := check_constant_val_c_refines hfuel hk hsw hfw hcv hq lst lfe hsr hfr
    exact ErrSim.trans herr (fun _ hle => by
      rw [ConLeche.Cached.checkDeclC]; exact run_bind_err_head hle)
  | Ok p =>
    obtain ⟨cv_a, jty⟩ := p
    obtain ⟨lst1, hruncv, hsr1, hsw1, hcvawf, hjtywf, hnameq, hfresh⟩ :=
      check_constant_val_c_refines hfuel hk hsw hfw hcv hq lst lfe hsr hfr
    have hrest :=
      check_thm_val_c_refines hfuel hk hsw1 hfw hcan hfull hcvawf hjtywf hv h lst1 lfe
        hsr1 hfr
    cases out with
    | Ok fe' =>
      obtain ⟨lst2, lfe2, hrun2, rest⟩ := hrest
      refine ⟨lst2, lfe2, ?_, rest⟩
      rw [ConLeche.Cached.checkDeclC]
      exact run_bind_ok hruncv hrun2
    | Err e =>
      show ErrSim e _
      refine ErrSim.trans hrest (fun _ hle => ?_)
      rw [ConLeche.Cached.checkDeclC]
      exact run_bind_ok hruncv hle

/-- `check_thm_decl_c_refines` at a success, the pre-#67 statement. -/
theorem check_thm_decl_c_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : cached.parsed_c.check_thm_decl_c mode st fe cv value = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkDeclC (absMode mode) lfe
            (.thmDecl (absConstantVal cv) (absExpr value))).run lst
          = Except.ok (lfe', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  check_thm_decl_c_refines hfuel hk hsw hfw hcan hfull hcv hv h

/-- `checkDeclC`'s `.opaqueDecl` arm (`ParsedC.lean:189-202`): the opaque
check, then the compiler-trust gate for `Lean.reduceNat`/`Lean.reduceBool` —
branched *before* the push, so the common arm hands `fe` to it unshared.

Proved: `check_constant_val_c_refines` and `check_opaque_val_c_refines` above,
and `Refine/CheckerPins.lean`'s `check_reduce_pin_refines_at_view` at
`lfp := fe` (again `push_restrict_find`).  Its `TrustGuardsSpec`/`TrustPinsSpec`
hypotheses are discharged by `trustGuardsSpec`/`trustPinsSpec` above; the
per-view one needs `reduce_pin_guard_f_step`, since the cached tier has no
`Env` to hand `Refine/TrustAxioms.lean`'s `Env`-indexed version. -/
theorem check_opaque_decl_c_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : cached.parsed_c.check_opaque_decl_c mode st fe cv value = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (ConLeche.Cached.checkDeclC (absMode mode) lfe
              (.opaqueDecl (absConstantVal cv) (absExpr value))).run lst
            = Except.ok (lfe', lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
      | .Err e =>
        ErrSim e ((ConLeche.Cached.checkDeclC (absMode mode) lfe
          (.opaqueDecl (absConstantVal cv) (absExpr value))).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.parsed_c.check_opaque_decl_c] at h
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  cases r with
  | Err er =>
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim er _
    have herr := check_constant_val_c_refines hfuel hk hsw hfw hcv hq lst lfe hsr hfr
    exact ErrSim.trans herr (fun _ hle => by
      rw [ConLeche.Cached.checkDeclC]; exact run_bind_err_head hle)
  | Ok p =>
    obtain ⟨cv_a, jty⟩ := p
    obtain ⟨lst1, hruncv, hsr1, hsw1, hcvawf, hjtywf, hnameq, hfresh⟩ :=
      check_constant_val_c_refines hfuel hk hsw hfw hcv hq lst lfe hsr hfr
    obtain ⟨rv, hrv, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hrvabs, hrvwf⟩ := TrustAxioms.reduce_op_names_refines hrv
    have hbv := Name.contains_refines hrvwf hcvawf.1 hb
    rw [hrvabs] at hbv
    cases b with
    | false =>
      have hcont : ConLeche.reduceOpNames.contains (absConstantVal cv_a).name = false := by
        rw [absConstantVal_name, ← hbv]
      simp only [Bool.false_eq_true, if_false] at h
      have hrest :=
        check_opaque_val_c_refines hfuel hk hsw1 hfw hcan hfull hcvawf hjtywf hv h lst1 lfe
          hsr1 hfr
      cases out with
      | Ok fe' =>
        obtain ⟨lst2, ci, hrun2, hciname, rest⟩ := hrest
        refine ⟨lst2, lfe.push ci, ?_, rest⟩
        rw [ConLeche.Cached.checkDeclC]
        refine run_bind_ok hruncv ?_
        simp only []
        rw [hcont]
        simp only [Bool.false_eq_true, if_false]
        exact hrun2
      | Err e =>
        show ErrSim e _
        refine ErrSim.trans hrest (fun _ hle => ?_)
        rw [ConLeche.Cached.checkDeclC]
        refine run_bind_ok hruncv ?_
        simp only []
        rw [hcont]
        simp only [Bool.false_eq_true, if_false]
        exact hle
    | true =>
      have hcont : ConLeche.reduceOpNames.contains (absConstantVal cv_a).name = true := by
        rw [absConstantVal_name, ← hbv]
      simp only [if_true] at h
      obtain ⟨q2, hq2, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r1, st2⟩ := q2
      cases r1 with
      | Err er =>
        obtain ⟨hout, rfl⟩ := err_outS h
        subst hout
        show ErrSim er _
        have herr :=
          check_opaque_val_c_refines hfuel hk hsw1 hfw hcan hfull hcvawf hjtywf hv hq2
            lst1 lfe hsr1 hfr
        refine ErrSim.trans herr (fun _ hle => ?_)
        rw [ConLeche.Cached.checkDeclC]
        refine run_bind_ok hruncv ?_
        simp only []
        rw [hcont]
        simp only [if_true]
        exact run_bind_err_head hle
      | Ok fe2 =>
        obtain ⟨lst2, ci, hrun2, hciname, hsr2, hsw2, hrel2, hwf2, hcan2, hfull2⟩ :=
          check_opaque_val_c_refines hfuel hk hsw1 hfw hcan hfull hcvawf hjtywf hv hq2
            lst1 lfe hsr1 hfr
        have hcifresh : lfe.find? ci.name = none := by
          rw [hciname, absConstantVal_name, hnameq]; exact hfresh
        have hlfp : lfe.find?
            = ((lfe.push ci).restrictTo (fe.visible_below).val).find? := by
          rw [hfr.2.1, push_restrict_find hcifresh]
        have hres :=
          CheckerPins.check_reduce_pin_refines_at_view hfuel hk trustPinsSpec hsw2 hwf2
            hcvawf.1 hv h lst2 (lfe.push ci) lfe hsr2 hrel2
            (trustGuardsSpec hrel2 hwf2) (fun _ hr hw => trustGuardsSpec hr hw) hlfp
        cases out with
        | Ok fe' =>
          obtain ⟨lst3, hrun3, hsr3, hsw3, hrel3, hwf3⟩ := hres
          have hfe' : fe' = fe2 :=
            check_reduce_pin_fenv
              (h : checker.check_reduce_pin mode st2 fe2 fe.visible_below cv_a.name value
                = ok (.Ok fe', st'))
          refine ⟨lst3, lfe.push ci, ?_, hsr3, hsw3, hrel3, hwf3,
            by rw [hfe']; exact hcan2, by rw [hfe']; exact hfull2⟩
          rw [ConLeche.Cached.checkDeclC]
          refine run_bind_ok hruncv ?_
          simp only []
          rw [hcont]
          simp only [if_true]
          have hrun3' : (ConLeche.checkReducePinF (TypeChecker.lops mode lfe) lfe
              (lfe.push ci) (absConstantVal cv_a).name (absExpr value)).run lst2
              = .ok ((), lst3) := by rw [absConstantVal_name]; exact hrun3
          exact run_bind_ok hrun2 (run_bind_ok hrun3' rfl)
        | Err e =>
          show ErrSim e _
          refine ErrSim.trans hres (fun le hle => ?_)
          rw [ConLeche.Cached.checkDeclC]
          refine run_bind_ok hruncv ?_
          simp only []
          rw [hcont]
          simp only [if_true]
          have hle' : (ConLeche.checkReducePinF (TypeChecker.lops mode lfe) lfe
              (lfe.push ci) (absConstantVal cv_a).name (absExpr value)).run lst2
              = .error le := by rw [absConstantVal_name]; exact hle
          exact run_bind_ok hrun2 (run_bind_err_head hle')

/-- `check_opaque_decl_c_refines` at a success, the pre-#67 statement. -/
theorem check_opaque_decl_c_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : cached.parsed_c.check_opaque_decl_c mode st fe cv value = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkDeclC (absMode mode) lfe
            (.opaqueDecl (absConstantVal cv) (absExpr value))).run lst
          = Except.ok (lfe', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  check_opaque_decl_c_refines hfuel hk hsw hfw hcan hfull hcv hv h


/-- `checkDeclC`'s `.axiomDecl` arm (`ParsedC.lean:203-232`): the pinned
axioms are installed with their shapes pinned, the tolerated whitelist is
checked and not stored, and every other axiom is a positive decline.

Proved: `check_constant_val_c_refines` above, `Refine/StdAxioms.lean`'s
`std_axiom_ok_refines_of_rel`/`tolerated_axiom_names_refines`,
`Refine/TrustAxioms.lean`'s `trust_compiler_ok_refines`/`of_reduce_ax_ok_refines`
and the shared install step `axiom_install_c` (`record_c_const` +
`push_refines`). -/
theorem check_axiom_decl_c_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {cv : env.ConstantVal}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv)
    (h : cached.parsed_c.check_axiom_decl_c mode st fe cv = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (ConLeche.Cached.checkDeclC (absMode mode) lfe
              (.axiomDecl (absConstantVal cv))).run lst = Except.ok (lfe', lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
      | .Err e =>
        ErrSim e ((ConLeche.Cached.checkDeclC (absMode mode) lfe
          (.axiomDecl (absConstantVal cv))).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.parsed_c.check_axiom_decl_c] at h
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  cases r with
  | Err er =>
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim er _
    have herr := check_constant_val_c_refines hfuel hk hsw hfw hcv hq lst lfe hsr hfr
    exact ErrSim.trans herr (fun _ hle => by
      rw [ConLeche.Cached.checkDeclC]; exact run_bind_err_head hle)
  | Ok p =>
    obtain ⟨cv_a, jty⟩ := p
    obtain ⟨lst1, hruncv, hsr1, hsw1, hcvawf, hjtywf, hnameq, hfresh⟩ :=
      check_constant_val_c_refines hfuel hk hsw hfw hcv hq lst lfe hsr hfr
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    have hbabs :=
      StdAxioms.std_axiom_ok_refines_of_rel hfr hfw (eqBasisPinned hfr hfw) hcvawf hb
    cases b with
    | true =>
      simp only [if_pos] at h
      obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨st2, hrec, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hout, rfl⟩ := ok_outS h
      subst hout
      obtain ⟨lst2, hrun, rest⟩ :=
        axiom_install_c hsw1 hfw hcan hfull hcvawf hjtywf hn he hrec hpush lst1 lfe hsr1 hfr
      refine ⟨lst2, lfe.push (.axiomInfo (absConstantVal cv_a)), ?_, rest⟩
      rw [ConLeche.Cached.checkDeclC]
      refine run_bind_ok hruncv ?_
      simp only []
      rw [if_pos hbabs.symm]
      exact hrun
    | false =>
      have hstdf : ¬ (ConLeche.stdAxiomOkF lfe (absConstantVal cv_a) = true) := by
        rw [← hbabs]; simp
      simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨tn, htn, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨htnabs, htnwf⟩ := TrustAxioms.trust_compiler_name_refines htn
      have hb1abs := Name.beq_refines hcvawf.1 htnwf hb1
      rw [htnabs] at hb1abs
      cases b1 with
      | true =>
        have hnm : (absConstantVal cv_a).name = ConLeche.trustCompilerName := by
          rw [absConstantVal_name]; simpa using hb1abs.symm
        obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
        have hb2abs := TrustAxioms.trust_compiler_ok_refines matchesPinSpec
          (FindAgree.of_rel hfr hfw) (FindWF.of_wf hfw) hcvawf hb2
        cases b2 with
        | false =>
          -- the trust-compiler shape `throw` (`ParsedC.lean:212-213`)
          obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hout, -⟩ := err_outS h
          subst hout
          show ErrSim ce _
          refine errSim_notImplemented
            (ls := s!"unsupported Lean.trustCompiler shape ({(absConstantVal cv).name})")
            hce rfl ?_
          rw [ConLeche.Cached.checkDeclC]
          refine run_bind_ok hruncv ?_
          simp only []
          rw [if_neg hstdf, if_pos hnm,
            if_neg (show ¬ (ConLeche.trustCompilerOkF lfe (absConstantVal cv_a) = true)
              from by rw [← hb2abs]; simp)]
          rfl
        | true =>
          simp only [if_pos] at h
          obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨st2, hrec, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hout, rfl⟩ := ok_outS h
          subst hout
          obtain ⟨lst2, hrun, rest⟩ :=
            axiom_install_c hsw1 hfw hcan hfull hcvawf hjtywf hn he hrec hpush lst1 lfe hsr1 hfr
          refine ⟨lst2, lfe.push (.axiomInfo (absConstantVal cv_a)), ?_, rest⟩
          rw [ConLeche.Cached.checkDeclC]
          refine run_bind_ok hruncv ?_
          simp only []
          rw [if_neg hstdf, if_pos hnm, if_pos hb2abs.symm]
          exact hrun
      | false =>
        have hnotc : ¬ ((absConstantVal cv_a).name = ConLeche.trustCompilerName) := by
          rw [absConstantVal_name]
          intro hc; rw [hc] at hb1abs; simp at hb1abs
        obtain ⟨rn, hrn, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hrnabs, hrnwf⟩ := TrustAxioms.of_reduce_nat_name_refines hrn
        have hb2abs := Name.beq_refines hcvawf.1 hrnwf hb2
        rw [hrnabs] at hb2abs
        cases b2 with
        | true =>
          have hnm : (absConstantVal cv_a).name = ConLeche.ofReduceNatName ∨
              (absConstantVal cv_a).name = ConLeche.ofReduceBoolName :=
            Or.inl (by rw [absConstantVal_name]; simpa using hb2abs.symm)
          obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
          have hb3abs := TrustAxioms.of_reduce_ax_ok_refines matchesPinSpec
            (basisPinsSpec hfr hfw) (FindAgree.of_rel hfr hfw) (FindWF.of_wf hfw) hcvawf hb3
          cases b3 with
          | false =>
            -- the compiler-trust environment `throw` (`ParsedC.lean:218-219`)
            obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hout, -⟩ := err_outS h
            subst hout
            show ErrSim ce _
            refine errSim_notImplemented
              (ls := s!"unsupported compiler-trust axiom environment ({(absConstantVal cv).name})")
              hce rfl ?_
            rw [ConLeche.Cached.checkDeclC]
            refine run_bind_ok hruncv ?_
            simp only []
            rw [if_neg hstdf, if_neg hnotc, if_pos hnm,
              if_neg (show ¬ (ConLeche.ofReduceAxOkF lfe (absConstantVal cv_a) = true)
                from by rw [← hb3abs]; simp)]
            rfl
          | true =>
            simp only [if_pos] at h
            obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨st2, hrec, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hout, rfl⟩ := ok_outS h
            subst hout
            obtain ⟨lst2, hrun, rest⟩ :=
              axiom_install_c hsw1 hfw hcan hfull hcvawf hjtywf hn he hrec hpush lst1 lfe hsr1 hfr
            refine ⟨lst2, lfe.push (.axiomInfo (absConstantVal cv_a)), ?_, rest⟩
            rw [ConLeche.Cached.checkDeclC]
            refine run_bind_ok hruncv ?_
            simp only []
            rw [if_neg hstdf, if_neg hnotc, if_pos hnm, if_pos hb3abs.symm]
            exact hrun
        | false =>
          have hnotn : ¬ ((absConstantVal cv_a).name = ConLeche.ofReduceNatName) := by
            rw [absConstantVal_name]
            intro hc; rw [hc] at hb2abs; simp at hb2abs
          obtain ⟨bn, hbn, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hbnabs, hbnwf⟩ := TrustAxioms.of_reduce_bool_name_refines hbn
          have hb3abs := Name.beq_refines hcvawf.1 hbnwf hb3
          rw [hbnabs] at hb3abs
          cases b3 with
          | true =>
            have hnm : (absConstantVal cv_a).name = ConLeche.ofReduceNatName ∨
                (absConstantVal cv_a).name = ConLeche.ofReduceBoolName :=
              Or.inr (by rw [absConstantVal_name]; simpa using hb3abs.symm)
            obtain ⟨b4, hb4, h⟩ := bind_eq_ok_iff.mp h
            have hb4abs := TrustAxioms.of_reduce_ax_ok_refines matchesPinSpec
              (basisPinsSpec hfr hfw) (FindAgree.of_rel hfr hfw) (FindWF.of_wf hfw) hcvawf hb4
            cases b4 with
            | false =>
              -- the same `throw`, on the `Bool` side
              obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨hout, -⟩ := err_outS h
              subst hout
              show ErrSim ce _
              refine errSim_notImplemented
                (ls := s!"unsupported compiler-trust axiom environment ({(absConstantVal cv).name})")
                hce rfl ?_
              rw [ConLeche.Cached.checkDeclC]
              refine run_bind_ok hruncv ?_
              simp only []
              rw [if_neg hstdf, if_neg hnotc, if_pos hnm,
                if_neg (show ¬ (ConLeche.ofReduceAxOkF lfe (absConstantVal cv_a) = true)
                  from by rw [← hb4abs]; simp)]
              rfl
            | true =>
              simp only [if_pos] at h
              obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨st2, hrec, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨hout, rfl⟩ := ok_outS h
              subst hout
              obtain ⟨lst2, hrun, rest⟩ :=
                axiom_install_c hsw1 hfw hcan hfull hcvawf hjtywf hn he hrec hpush lst1 lfe hsr1 hfr
              refine ⟨lst2, lfe.push (.axiomInfo (absConstantVal cv_a)), ?_, rest⟩
              rw [ConLeche.Cached.checkDeclC]
              refine run_bind_ok hruncv ?_
              simp only []
              rw [if_neg hstdf, if_neg hnotc, if_pos hnm, if_pos hb4abs.symm]
              exact hrun
          | false =>
            have hnotb : ¬ ((absConstantVal cv_a).name = ConLeche.ofReduceBoolName) := by
              rw [absConstantVal_name]
              intro hc; rw [hc] at hb3abs; simp at hb3abs
            have hnotnb : ¬ ((absConstantVal cv_a).name = ConLeche.ofReduceNatName ∨
                (absConstantVal cv_a).name = ConLeche.ofReduceBoolName) :=
              fun hc => hc.elim hnotn hnotb
            obtain ⟨pn, hpn, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨b4, hb4, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hpnabs, hpnwf⟩ := StdAxioms.propext_name_refines hpn
            have hb4abs := Name.beq_refines hcvawf.1 hpnwf hb4
            rw [hpnabs] at hb4abs
            cases b4 with
            | true =>
              -- `propext`'s shape did not match: the cited arm's own `throw`
              obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨hout, -⟩ := err_outS h
              subst hout
              show ErrSim ce _
              refine errSim_notImplemented
                (ls := s!"standard axiom shape mismatch ({(absConstantVal cv).name})")
                hce rfl ?_
              rw [ConLeche.Cached.checkDeclC]
              refine run_bind_ok hruncv ?_
              simp only []
              rw [if_neg hstdf, if_neg hnotc, if_neg hnotnb,
                if_pos (Or.inl (show (absConstantVal cv_a).name = ConLeche.propextName
                  from by rw [absConstantVal_name]; simpa using hb4abs.symm))]
              rfl
            | false =>
              have hnotpe : ¬ ((absConstantVal cv_a).name = ConLeche.propextName) := by
                rw [absConstantVal_name]
                intro hc; rw [hc] at hb4abs; simp at hb4abs
              obtain ⟨cn, hcn, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨b5, hb5, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨hcnabs, hcnwf⟩ := StdAxioms.choice_name_refines hcn
              have hb5abs := Name.beq_refines hcvawf.1 hcnwf hb5
              rw [hcnabs] at hb5abs
              cases b5 with
              | true =>
                -- `Classical.choice`'s shape did not match
                obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨hout, -⟩ := err_outS h
                subst hout
                show ErrSim ce _
                refine errSim_notImplemented
                  (ls := s!"standard axiom shape mismatch ({(absConstantVal cv).name})")
                  hce rfl ?_
                rw [ConLeche.Cached.checkDeclC]
                refine run_bind_ok hruncv ?_
                simp only []
                rw [if_neg hstdf, if_neg hnotc, if_neg hnotnb,
                  if_pos (Or.inr (show (absConstantVal cv_a).name = ConLeche.choiceName
                    from by rw [absConstantVal_name]; simpa using hb5abs.symm))]
                rfl
              | false =>
                have hnotch : ¬ ((absConstantVal cv_a).name = ConLeche.choiceName) := by
                  rw [absConstantVal_name]
                  intro hc; rw [hc] at hb5abs; simp at hb5abs
                have hnotpc : ¬ ((absConstantVal cv_a).name = ConLeche.propextName ∨
                    (absConstantVal cv_a).name = ConLeche.choiceName) :=
                  fun hc => hc.elim hnotpe hnotch
                obtain ⟨tv, htv, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨b6, hb6, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨htvabs, htvwf⟩ := StdAxioms.tolerated_axiom_names_refines htv
                have hb6abs := Name.contains_refines htvwf hcvawf.1 hb6
                rw [htvabs] at hb6abs
                cases b6 with
                | false =>
                  -- a non-standard axiom: the arm's positive decline
                  obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨hout, -⟩ := err_outS h
                  subst hout
                  show ErrSim ce _
                  refine errSim_notImplemented
                    (ls := s!"non-standard axiom ({(absConstantVal cv).name})")
                    hce rfl ?_
                  rw [ConLeche.Cached.checkDeclC]
                  refine run_bind_ok hruncv ?_
                  simp only []
                  rw [if_neg hstdf, if_neg hnotc, if_neg hnotnb, if_neg hnotpc,
                    if_neg (show ¬ (ConLeche.toleratedAxiomNames.contains
                      (absConstantVal cv_a).name = true) from by
                        rw [absConstantVal_name, ← hb6abs]; simp)]
                  rfl
                | true =>
                  simp only [if_pos] at h
                  obtain ⟨hout, rfl⟩ := ok_outS h
                  subst hout
                  refine ⟨lst1, lfe, ?_, hsr1, hsw1, hfr, hfw, hcan, hfull⟩
                  rw [ConLeche.Cached.checkDeclC]
                  refine run_bind_ok hruncv ?_
                  simp only []
                  rw [if_neg hstdf, if_neg hnotc, if_neg hnotnb, if_neg hnotpc,
                    if_pos (show ConLeche.toleratedAxiomNames.contains
                      (absConstantVal cv_a).name = true from by
                        rw [absConstantVal_name]; simpa using hb6abs.symm)]
                  rfl

/-- `check_axiom_decl_c_refines` at a success, the pre-#67 statement. -/
theorem check_axiom_decl_c_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {cv : env.ConstantVal}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hcv : ConstantValWF cv)
    (h : cached.parsed_c.check_axiom_decl_c mode st fe cv = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkDeclC (absMode mode) lfe
            (.axiomDecl (absConstantVal cv))).run lst = Except.ok (lfe', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  check_axiom_decl_c_refines hfuel hk hsw hfw hcan hfull hcv h

/-- **`cached::parsed_c::check_decl_c` refines `checkDeclC`**
(`ConLeche/Cached/ParsedC.lean:158-241`): the same six arms over the parsed
representation, with `checkConstantValC`'s recorded judgement type threaded and
the pinned-name test *before* the push (the cited arm's own RC-linearity
shape).

Proved from the six arms above, all six of them closed; the axiom census at the
end of the file pins the result. -/
theorem check_decl_c_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hind : IndRoutesSpec mode) (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {pd : parsed_c.DeclC}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hd : DeclCWF pd)
    (h : cached.parsed_c.check_decl_c mode pins st fe pd = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (ConLeche.Cached.checkDeclC (absMode mode) lfe (absDeclC pd)).run lst
              = Except.ok (lfe', lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
      | .Err e =>
        ErrSim e ((ConLeche.Cached.checkDeclC (absMode mode) lfe
          (absDeclC pd)).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.parsed_c.check_decl_c.eq_def] at h
  cases pd with
  | AxiomDecl cv =>
    simp only [absDeclC]
    cases out with
    | Ok fe' =>
      exact check_axiom_decl_c_refines hfuel hk hsw hfw hcan hfull hd h lst lfe hsr hfr
    | Err e =>
      exact check_axiom_decl_c_refines hfuel hk hsw hfw hcan hfull hd h lst lfe hsr hfr
  | DefnDecl cv value hint =>
    simp only [absDeclC]
    cases out with
    | Ok fe' =>
      exact check_defn_decl_c_refines hfuel hk hvar hpins hsw hfw hcan hfull hd.1 hd.2 h
        lst lfe hsr hfr
    | Err e =>
      exact check_defn_decl_c_refines hfuel hk hvar hpins hsw hfw hcan hfull hd.1 hd.2 h
        lst lfe hsr hfr
  | ThmDecl cv value =>
    simp only [absDeclC]
    cases out with
    | Ok fe' =>
      exact check_thm_decl_c_refines hfuel hk hsw hfw hcan hfull hd.1 hd.2 h lst lfe
        hsr hfr
    | Err e =>
      exact check_thm_decl_c_refines hfuel hk hsw hfw hcan hfull hd.1 hd.2 h lst lfe
        hsr hfr
  | OpaqueDecl cv value =>
    simp only [absDeclC]
    cases out with
    | Ok fe' =>
      exact check_opaque_decl_c_refines hfuel hk hsw hfw hcan hfull hd.1 hd.2 h lst lfe
        hsr hfr
    | Err e =>
      exact check_opaque_decl_c_refines hfuel hk hsw hfw hcan hfull hd.1 hd.2 h lst lfe
        hsr hfr
  | BasisDecl kind =>
    simp only [absDeclC]
    obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
    have hres := check_basis_decl_c_refines (mode := mode) hfw hcan hfull hr lst lfe hfr
    cases r with
    | Ok fe2 =>
      obtain ⟨hout, rfl⟩ := ok_outS h
      subst hout
      obtain ⟨lfe', hrun, hrel', hwf', hcan', hfull'⟩ := hres
      exact ⟨lst, lfe', hrun, hsr, hsw, hrel', hwf', hcan', hfull'⟩
    | Err er =>
      obtain ⟨hout, rfl⟩ := err_outS h
      subst hout
      exact hres
  | IndDecl block n_p =>
    simp only [absDeclC]
    cases out with
    | Ok fe' =>
      exact check_ind_decl_c_refines hind hinde hsw hfw hcan hfull hd h lst lfe hsr hfr
    | Err e =>
      exact check_ind_decl_c_refines hind hinde hsw hfw hcan hfull hd h lst lfe hsr hfr

/-- `check_decl_c_refines` at a success, the pre-#67 statement. -/
theorem check_decl_c_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hind : IndRoutesSpec mode) (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {pd : parsed_c.DeclC}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hd : DeclCWF pd)
    (h : cached.parsed_c.check_decl_c mode pins st fe pd = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkDeclC (absMode mode) lfe (absDeclC pd)).run lst
            = Except.ok (lfe', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  check_decl_c_refines hfuel hk hind hinde hvar hpins hsw hfw hcan hfull hd h

/-- **`cached::parsed_c::check_decl_step_c` refines `checkDeclStepC`**
(`ConLeche/Cached/ParsedC.lean:259-262`): `flushC`, then `checkDeclC`.  The
flush is what makes one `CState` safe for a whole stream — every
environment-dependent memo is emptied and the self-certified `ienv` and the
three level-operation memos survive (`Refine/State.lean`'s `flushed`).

Proved: `Refine/StateC.lean`'s `flush_c_refines` composed with
`check_decl_c_refines` above. -/
theorem check_decl_step_c_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hind : IndRoutesSpec mode) (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {pd : parsed_c.DeclC}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hd : DeclCWF pd)
    (h : cached.parsed_c.check_decl_step_c mode pins st fe pd = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (ConLeche.Cached.checkDeclStepC (absMode mode) lfe (absDeclC pd)).run lst
              = Except.ok (lfe', lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe'
      | .Err e =>
        ErrSim e ((ConLeche.Cached.checkDeclStepC (absMode mode) lfe
          (absDeclC pd)).run lst) := by
  intro lst lfe hsr hfr
  rw [cached.parsed_c.check_decl_step_c] at h
  obtain ⟨st1, hflush, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hrunf, hrel1, hwf1, -⟩ := StateC.flush_c_refines hsr hsw hflush
  have hres :=
    check_decl_c_refines hfuel hk hind hinde hvar hpins hwf1 hfw hcan hfull hd h
      lst.flushed lfe hrel1 hfr
  cases out with
  | Ok fe' =>
    obtain ⟨lst', lfe', hrun, rest⟩ := hres
    refine ⟨lst', lfe', ?_, rest⟩
    rw [ConLeche.Cached.checkDeclStepC]
    simp only [StateT.run_bind, hrunf]
    exact hrun
  | Err e =>
    show ErrSim e _
    refine ErrSim.trans hres (fun le hle => ?_)
    rw [ConLeche.Cached.checkDeclStepC]
    simp only [StateT.run_bind, hrunf]
    exact hle

/-- `check_decl_step_c_refines` at a success, the pre-#67 statement. -/
theorem check_decl_step_c_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hind : IndRoutesSpec mode) (hinde : IndRoutesSpecErr mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {pd : parsed_c.DeclC}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcan : FEnv.FEnvCanon fe)
    (hfull : FEnv.FEnvFull fe) (hd : DeclCWF pd)
    (h : cached.parsed_c.check_decl_step_c mode pins st fe pd = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkDeclStepC (absMode mode) lfe (absDeclC pd)).run lst
            = Except.ok (lfe', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ FEnv.FEnvCanon fe' ∧ FEnv.FEnvFull fe' :=
  check_decl_step_c_refines hfuel hk hind hinde hvar hpins hsw hfw hcan hfull hd h

/-! ## `Indexed`: the one hypothesis the `Expr`-level statements need

`checkDecl` reads the environment as an **`Env`** — `env.find?`, which sees
every stored constant — while the port reads the **index**, `fenv::find`, which
answers `none` for an entry whose installation counter is at or above the
visibility bound (task #108).  The two agree exactly when the index is the
index of its own environment with nothing hidden, which is what `mkFEnv` builds
and what `push` preserves.  That is `Indexed` below, and the six `Expr`-level
statements of this file carry it.

**It is not slack: the statements are false without it.**  Take an `fe` whose
bound hides a stored constant `c` and a declaration named `c`: the port's
`check_constant_val` asks `fenv::find fe c`, gets `none`, and proceeds; the
Lean's `checkConstantVal` asks `lfe.env.find? c`, gets `some`, and throws
`duplicate declaration`.  The port would then accept where the Lean rejects,
which is exactly what a refinement lemma may not claim.  (The *cached* tier
needs no such hypothesis: `checkDeclC` is index-based throughout, so the two
sides read the same bounded lookup.)

The fold re-establishes `Indexed` at every step and `check_decls_pure_refines`
starts from `mkFEnv Env.empty`, so no caller has to supply it by hand. -/

/-- The index is `mkFEnv` of its own environment: it indexes exactly what it
carries and hides nothing. -/
def Indexed (lfe : ConLeche.FEnv) : Prop := lfe = ConLeche.mkFEnv lfe.env

/-- A freshly built index is `Indexed`. -/
theorem Indexed.mk (e : ConLeche.Env) : Indexed (ConLeche.mkFEnv e) := rfl

/-- **An `Indexed` Lean view forces the port's index to be canonical and
unrestricted** (task #59): `mkFEnv` *is* the rebuild, at the full constant
count, so the `Expr`-level tier's own hypothesis discharges the pair the
`cached` tier carries. -/
theorem canon_of_indexed {fe : fenv.FEnv} {lfe : ConLeche.FEnv}
    (hfr : FEnvRel fe lfe) (hix : Indexed lfe) :
    FEnv.FEnvCanon fe ∧ FEnv.FEnvFull fe := by
  have henv : ConLeche.mkFEnv (absEnv fe.env) = lfe := by
    conv_rhs => rw [hix]
    rw [hfr.1]
  have hvb : fe.visible_below.val = lfe.visibleBelow := hfr.2.1
  have hfull : FEnv.FEnvFull fe := by
    unfold FEnv.FEnvFull
    rw [hvb]
    conv_lhs => rw [hix]
    show (ConLeche.mkFEnvGo lfe.env.consts).1 = _
    rw [FEnv.mkFEnvGo_fst, ← hfr.1]
    simp [absEnv, absConstantInfos]
  refine ⟨?_, hfull⟩
  unfold FEnv.FEnvCanon
  rw [henv, hvb]
  exact hfr

/-- An `Indexed` index answers `Env.find?` (`mkFEnv_find?`). -/
theorem Indexed.find_eq {lfe : ConLeche.FEnv} (h : Indexed lfe) (n : ConLeche.Name) :
    lfe.find? n = lfe.env.find? n := by
  conv_lhs => rw [h]
  exact ConLeche.mkFEnv_find? lfe.env n

/-- `push` preserves it (`FEnv.push (mkFEnv env) ci = mkFEnv ⟨ci :: env.consts⟩`,
definitionally — `FEnv.lean:82-87`). -/
theorem Indexed.push {lfe : ConLeche.FEnv} (h : Indexed lfe)
    (ci : ConLeche.ConstantInfo) : Indexed (lfe.push ci) := by
  show lfe.push ci = ConLeche.mkFEnv (lfe.push ci).env
  conv_lhs => rw [h]
  rfl

open ConLeche.Cached in
/-- The basis-table fold at the `Env` spelling: `installBasisDeclF` through the
index *is* `installBasisDecl` on its environment, step for step, as long as the
index is `Indexed` — which each step's `push` preserves. -/
theorem installBasisDecl_fold_env :
    ∀ (l : List ConLeche.ConstantInfo) (lfe lfe₂ : ConLeche.FEnv) (lst : CState),
      Indexed lfe →
      (l.foldlM (ConLeche.installBasisDeclF (m := CheckCM)) lfe).run lst = .ok (lfe₂, lst) →
      (l.foldlM (ConLeche.installBasisDecl (m := CheckCM)) lfe.env).run lst
          = .ok (lfe₂.env, lst)
        ∧ Indexed lfe₂ := by
  intro l
  induction l with
  | nil =>
    intro lfe lfe₂ lst hix h
    have hh : lfe = lfe₂ := by
      have he : (Except.ok (lfe, lst) :
          Except ConLeche.CheckError (ConLeche.FEnv × CState)) = .ok (lfe₂, lst) := h
      simpa using he
    subst hh
    exact ⟨rfl, hix⟩
  | cons ci l ih =>
    intro lfe lfe₂ lst hix h
    rw [List.foldlM_cons, StateT.run_bind] at h
    by_cases hg : (lfe.find? ci.name).isNone = true
    · have hstep : (ConLeche.installBasisDeclF (m := CheckCM) lfe ci).run lst
          = .ok (lfe.push ci, lst) := by
        simp only [ConLeche.installBasisDeclF, hg, if_true, StateT.run, Bind.bind,
          Pure.pure, StateT.pure, Except.pure]
      rw [hstep] at h
      obtain ⟨hrun, hix₂⟩ := ih (lfe.push ci) lfe₂ lst (hix.push ci) h
      refine ⟨?_, hix₂⟩
      have hstepE : (ConLeche.installBasisDecl (m := CheckCM) lfe.env ci).run lst
          = .ok ((lfe.push ci).env, lst) := by
        simp only [ConLeche.installBasisDecl, ← hix.find_eq ci.name, hg, if_true,
          StateT.run, Bind.bind, Pure.pure, StateT.pure,
          Except.pure]
        rfl
      rw [List.foldlM_cons, StateT.run_bind, hstepE]
      exact hrun
    · exfalso
      have hgf : (lfe.find? ci.name).isNone = false := (Bool.not_eq_true _).mp hg
      rw [show (ConLeche.installBasisDeclF (m := CheckCM) lfe ci).run lst
          = .error (.invalid s!"duplicate declaration {ci.name}") from by
        simp only [ConLeche.installBasisDeclF, hgf, Bool.false_eq_true, if_false,
          StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
          Except.pure]
        rfl] at h
      simp [Bind.bind, Except.bind] at h

open ConLeche.Cached in
/-- The same at a **failure**: the two folds throw the same `duplicate
declaration`, because `Indexed` makes the two `find?`s agree. -/
theorem installBasisDecl_fold_env_err :
    ∀ (l : List ConLeche.ConstantInfo) (lfe : ConLeche.FEnv) (lst : CState)
      (le : ConLeche.CheckError),
      Indexed lfe →
      (l.foldlM (ConLeche.installBasisDeclF (m := CheckCM)) lfe).run lst = .error le →
      (l.foldlM (ConLeche.installBasisDecl (m := CheckCM)) lfe.env).run lst
        = .error le := by
  intro l
  induction l with
  | nil =>
    intro lfe lst le hix h
    exact absurd h (by
      simp only [List.foldlM_nil, StateT.run, Pure.pure, StateT.pure, Except.pure]
      simp)
  | cons ci l ih =>
    intro lfe lst le hix h
    rw [List.foldlM_cons, StateT.run_bind] at h
    by_cases hg : (lfe.find? ci.name).isNone = true
    · have hstep : (ConLeche.installBasisDeclF (m := CheckCM) lfe ci).run lst
          = .ok (lfe.push ci, lst) := by
        simp only [ConLeche.installBasisDeclF, hg, if_true, StateT.run, Bind.bind,
          Pure.pure, StateT.pure, Except.pure]
      rw [hstep] at h
      have hstepE : (ConLeche.installBasisDecl (m := CheckCM) lfe.env ci).run lst
          = .ok ((lfe.push ci).env, lst) := by
        simp only [ConLeche.installBasisDecl, ← hix.find_eq ci.name, hg, if_true,
          StateT.run, Bind.bind, Pure.pure, StateT.pure, Except.pure]
        rfl
      rw [List.foldlM_cons, StateT.run_bind, hstepE]
      exact ih (lfe.push ci) lst le (hix.push ci) h
    · have hgf : (lfe.find? ci.name).isNone = false := (Bool.not_eq_true _).mp hg
      have hstep : (ConLeche.installBasisDeclF (m := CheckCM) lfe ci).run lst
          = .error (.invalid s!"duplicate declaration {ci.name}") := by
        simp only [ConLeche.installBasisDeclF, hgf, Bool.false_eq_true, if_false,
          StateT.run, Bind.bind, StateT.bind, Except.bind, Pure.pure, StateT.pure,
          Except.pure]
        rfl
      rw [hstep] at h
      have hle : ConLeche.CheckError.invalid s!"duplicate declaration {ci.name}" = le := by
        simp only [Bind.bind, Except.bind] at h
        simpa using h
      have hstepE : (ConLeche.installBasisDecl (m := CheckCM) lfe.env ci).run lst
          = .error le := by
        rw [← hle]
        simp only [ConLeche.installBasisDecl, ← hix.find_eq ci.name, hgf,
          Bool.false_eq_true, if_false, StateT.run, Bind.bind, StateT.bind, Except.bind,
          Pure.pure, StateT.pure, Except.pure]
        rfl
      rw [List.foldlM_cons]
      exact run_bind_err_head hstepE

/-! ### `Indexed`, applied: the `F`-twin is the `Env` original

`ConLeche/Verify/CheckerF.lean` states every guard's index twin against its
`Env` original at `mkFEnv env`; `Indexed` is exactly the hypothesis that turns
the index at hand into such an `mkFEnv`.  These are the rewrites the six arms
below use, one per guard `checkDecl` reads. -/

theorem Indexed.checkConstantVal_eq {lfe : ConLeche.FEnv} (h : Indexed lfe)
    (ops : ConLeche.CheckerOps ConLeche.Cached.CheckCM) (cv : ConLeche.ConstantVal) :
    ConLeche.checkConstantValF ops lfe cv = ConLeche.checkConstantVal ops lfe.env cv := by
  conv_lhs => rw [h]
  exact ConLeche.checkConstantValF_eq _ _ _

theorem Indexed.stdAxiomOk_eq {lfe : ConLeche.FEnv} (h : Indexed lfe)
    (cvA : ConLeche.ConstantVal) :
    ConLeche.stdAxiomOkF lfe cvA = ConLeche.stdAxiomOk lfe.env cvA := by
  conv_lhs => rw [h]
  exact ConLeche.stdAxiomOkF_eq _ _

theorem Indexed.trustCompilerOk_eq {lfe : ConLeche.FEnv} (h : Indexed lfe)
    (cvA : ConLeche.ConstantVal) :
    ConLeche.trustCompilerOkF lfe cvA = ConLeche.trustCompilerOk lfe.env cvA := by
  conv_lhs => rw [h]
  exact ConLeche.trustCompilerOkF_eq _ _

theorem Indexed.ofReduceAxOk_eq {lfe : ConLeche.FEnv} (h : Indexed lfe)
    (cvA : ConLeche.ConstantVal) :
    ConLeche.ofReduceAxOkF lfe cvA = ConLeche.ofReduceAxOk lfe.env cvA := by
  conv_lhs => rw [h]
  exact ConLeche.ofReduceAxOkF_eq _ _

/-- The pushed index's environment is the cons-extended one (`push`'s own
definition), which is what `checkDecl`'s arms return. -/
theorem push_env (lfe : ConLeche.FEnv) (ci : ConLeche.ConstantInfo) :
    (lfe.push ci).env = (⟨ci :: lfe.env.consts⟩ : ConLeche.Env) := rfl

/-! ### The value checks' push, read off the port

`Refine/Checker.lean` states `check_thm_val`/`check_opaque_val`/`check_defn_val`
with the produced index **existentially** (`FEnvRel fe' lfe'`), which does not
say that `lfe'` indexes its own environment — and the fold needs `Indexed lfe'`
at the next step.  The port's own control flow does say it: each of the three
ends in `fenv::push` on the index it was handed.  These three lemmas read that
off, and `Refine/FEnv.lean`'s `push_refines` then supplies an `Indexed`
witness for the same `fe'`; the two model indices agree on their environments
(both are `absEnv fe'.env`), which is all the run equation sees. -/

/-- `checker_base::check_constant_val`'s two side facts, read off the port: the
name it was handed was **fresh** in the index, and the constant it returns
keeps that name (only the type is replaced by its annotation).  Both are inside
`Refine/CheckerBase.lean`'s proof but not in its statement, and the `Indexed`
half of the arms below needs them. -/
theorem check_constant_val_fresh {mode : env.CheckMode} {st st' : cached.state_c.CState}
    {fe : fenv.FEnv} {cv cv' : env.ConstantVal}
    (h : checker_base.check_constant_val mode st fe cv = ok (.Ok cv', st')) :
    fenv.find fe cv.name = ok none ∧ cv'.name = cv.name := by
  rw [checker_base.check_constant_val] at h
  obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
  cases o with
  | some ci => simp [core.option.Option.is_some, bind_eq_ok_iff] at h
  | none =>
    refine ⟨ho, ?_⟩
    simp only [core.option.Option.is_some] at h
    obtain ⟨rv, -, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · simp [bind_eq_ok_iff] at h
    · obtain ⟨b2, -, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · simp [bind_eq_ok_iff] at h
      · obtain ⟨b3, -, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · obtain ⟨b4, -, h⟩ := bind_eq_ok_iff.mp h
          split at h
          · obtain ⟨b5, -, h⟩ := bind_eq_ok_iff.mp h
            split at h
            · simp [bind_eq_ok_iff] at h
            · obtain ⟨q, -, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨r1, st1⟩ := q
              cases r1 with
              | Err er => simp at h
              | Ok ty =>
                replace h : checker_base.check_constant_val_after_annot mode st1 fe cv ty
                    = ok (.Ok cv', st') := h
                rw [checker_base.check_constant_val_after_annot] at h
                obtain ⟨c1, -, h⟩ := bind_eq_ok_iff.mp h
                split at h
                · obtain ⟨c2, -, h⟩ := bind_eq_ok_iff.mp h
                  split at h
                  · obtain ⟨q2, -, h⟩ := bind_eq_ok_iff.mp h
                    obtain ⟨r2, st2⟩ := q2
                    cases r2 with
                    | Err er => simp at h
                    | Ok stype =>
                      obtain ⟨q3, -, h⟩ := bind_eq_ok_iff.mp h
                      obtain ⟨r3, st3⟩ := q3
                      cases r3 with
                      | Err er => simp at h
                      | Ok u =>
                        obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
                        obtain ⟨v, -, h⟩ := bind_eq_ok_iff.mp h
                        simp only [Result.ok.injEq, Prod.mk.injEq,
                          core.result.Result.Ok.injEq] at h
                        rw [← h.1]
                        simpa using hn.symm
                  · simp [bind_eq_ok_iff] at h
                · simp [bind_eq_ok_iff] at h
          · simp [bind_eq_ok_iff] at h
        · simp [bind_eq_ok_iff] at h

/-! ### `checkDefnValF` at the `Env` spelling

`ConLeche/Verify/CheckerF.lean` has an `_eq` lemma for every *non*-extending
mirror; the extending ones (`checkDefnValF`, …) return a pushed **index** where
their `Env` counterpart returns a cons-extended `Env`, so the equation is the
`push` one (`installBasisDeclF_pushC`'s shape,
`ConLeche/Verify/Cached/BridgeCSDecl.lean:66`).  The one this file needs is
proved here rather than imported, so that the import stays inside
`Verify/CheckerF` + `Verify/EnvBound`. -/

open ConLeche.Cached in
theorem throwC_bind {α β : Type} (e : ConLeche.CheckError) (f : α → CheckCM β) :
    ((throw e : CheckCM α) >>= f) = throw e := rfl

open ConLeche.Cached in
theorem ite_bindC {α β : Type} (c : Prop) [Decidable c] (a b : CheckCM α)
    (f : α → CheckCM β) : ((if c then a else b) >>= f) = if c then a >>= f else b >>= f := by
  split <;> rfl

open ConLeche.Cached in
/-- `checkDefnValF` through the index is `checkDefnVal` on its environment,
followed by `mkFEnv` (`ConLeche/Kernel/DeclCheck.lean:838-853` against
`ConLeche/Kernel/Checker.lean:36-50`). -/
theorem checkDefnValF_pushC (ops : ConLeche.CheckerOps CheckCM) (env : ConLeche.Env)
    (cv : ConLeche.ConstantVal) (value : ConLeche.Expr)
    (hint : ConLeche.ReducibilityHint) :
    (ConLeche.checkDefnValF ops (ConLeche.mkFEnv env) cv value hint : CheckCM ConLeche.FEnv)
      = ConLeche.checkDefnVal ops env cv value hint >>= fun e => pure (ConLeche.mkFEnv e) := by
  unfold ConLeche.checkDefnValF ConLeche.checkDefnVal
  simp only [ConLeche.mkFEnv_env, ConLeche.constsResolveF_eq, ConLeche.push_mkFEnv,
    bind_assoc, pure_bind, ite_bindC, throwC_bind]

/-- `checker::check_defn_val` ends in `fenv::push fe (.DefnInfo cv value_a hint)`
at the value's own annotation. -/
theorem check_defn_val_push {mode : env.CheckMode} {st st' : cached.state_c.CState}
    {fe fe' : fenv.FEnv} {cv : env.ConstantVal} {value : expr.Expr}
    {hint : env.ReducibilityHint}
    (h : kernel.checker.check_defn_val mode st fe cv value hint = ok (.Ok fe', st')) :
    ∃ (value_a : expr.Expr) (sta : cached.state_c.CState),
      kernel.type_checker.annotate_core mode st fe 0#u64 value = ok (.Ok value_a, sta)
      ∧ fenv.push fe (env.ConstantInfo.DefnInfo cv value_a hint) = ok fe' := by
  rw [kernel.checker.check_defn_val] at h
  obtain ⟨b, -, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · simp [bind_eq_ok_iff] at h
    · obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, sta⟩ := q
      cases r with
      | Err er => simp at h
      | Ok value_a =>
        refine ⟨value_a, sta, hq, ?_⟩
        replace h : kernel.checker.check_defn_val_after_annot mode sta fe cv value_a hint
            = ok (.Ok fe', st') := h
        rw [kernel.checker.check_defn_val_after_annot] at h
        obtain ⟨b2, -, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · obtain ⟨b3, -, h⟩ := bind_eq_ok_iff.mp h
          split at h
          · obtain ⟨q2, -, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨r2, st2⟩ := q2
            cases r2 with
            | Err er => simp at h
            | Ok vtype =>
              obtain ⟨q3, -, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨r3, st3⟩ := q3
              cases r3 with
              | Err er => simp at h
              | Ok ok1 =>
                cases ok1 with
                | false => simp at h
                | true =>
                  simp only [] at h
                  obtain ⟨cv1, hcvd, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨rh, hrhd, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
                  simp only [Result.ok.injEq, Prod.mk.injEq,
                    core.result.Result.Ok.injEq] at h
                  rw [Env.constant_val_dup_refines hcvd,
                    Env.reducibility_hint_dup_refines hrhd] at hpush
                  rw [← h.1]
                  exact hpush
          · simp [bind_eq_ok_iff] at h
        · simp [bind_eq_ok_iff] at h
  · simp [bind_eq_ok_iff] at h

/-- `checker::check_thm_val` ends in `fenv::push fe (.ThmInfo cv value)`. -/
theorem check_thm_val_push {mode : env.CheckMode} {st st' : cached.state_c.CState}
    {fe fe' : fenv.FEnv} {cv : env.ConstantVal} {value : expr.Expr}
    (h : kernel.checker.check_thm_val mode st fe cv value = ok (.Ok fe', st')) :
    fenv.push fe (env.ConstantInfo.ThmInfo cv value) = ok fe' := by
  rw [kernel.checker.check_thm_val] at h
  obtain ⟨q, -, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  cases r with
  | Err er => simp at h
  | Ok stype =>
    obtain ⟨q2, -, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, st2⟩ := q2
    cases r1 with
    | Err er => simp at h
    | Ok u =>
      obtain ⟨l, -, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, -, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r2, -, h⟩ := bind_eq_ok_iff.mp h
      cases r2 with
      | Err er => simp at h
      | Ok is_prop =>
        cases is_prop with
        | false => simp at h
        | true =>
          simp only [if_pos] at h
          rw [kernel.checker.check_thm_val_witness] at h
          obtain ⟨b, -, h⟩ := bind_eq_ok_iff.mp h
          split at h
          · obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
            split at h
            · simp [bind_eq_ok_iff] at h
            · obtain ⟨q3, -, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨r3, st3⟩ := q3
              cases r3 with
              | Err er => simp at h
              | Ok jv =>
                replace h : kernel.checker.check_thm_val_checked mode st3 fe cv value jv
                    = ok (.Ok fe', st') := h
                rw [kernel.checker.check_thm_val_checked] at h
                obtain ⟨b2, -, h⟩ := bind_eq_ok_iff.mp h
                split at h
                · obtain ⟨b3, -, h⟩ := bind_eq_ok_iff.mp h
                  split at h
                  · obtain ⟨q4, -, h⟩ := bind_eq_ok_iff.mp h
                    obtain ⟨r4, st4⟩ := q4
                    cases r4 with
                    | Err er => simp at h
                    | Ok vtype =>
                      obtain ⟨q5, -, h⟩ := bind_eq_ok_iff.mp h
                      obtain ⟨r5, st5⟩ := q5
                      cases r5 with
                      | Err er => simp at h
                      | Ok ok1 =>
                        cases ok1 with
                        | false => simp at h
                        | true =>
                          simp only [] at h
                          obtain ⟨cv1, hcvd, h⟩ := bind_eq_ok_iff.mp h
                          obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
                          obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
                          simp only [Result.ok.injEq, Prod.mk.injEq,
                            core.result.Result.Ok.injEq] at h
                          rw [Env.constant_val_dup_refines hcvd, Expr.dup_eq he] at hpush
                          rw [← h.1]
                          exact hpush
                  · simp [bind_eq_ok_iff] at h
                · simp [bind_eq_ok_iff] at h
          · simp [bind_eq_ok_iff] at h

/-- `checker::check_opaque_val` ends in `fenv::push fe (.AxiomInfo cv)`. -/
theorem check_opaque_val_push {mode : env.CheckMode} {st st' : cached.state_c.CState}
    {fe fe' : fenv.FEnv} {cv : env.ConstantVal} {value : expr.Expr}
    (h : kernel.checker.check_opaque_val mode st fe cv value = ok (.Ok fe', st')) :
    fenv.push fe (env.ConstantInfo.AxiomInfo cv) = ok fe' := by
  rw [kernel.checker.check_opaque_val] at h
  obtain ⟨b, -, h⟩ := bind_eq_ok_iff.mp h
  split at h
  · obtain ⟨b1, -, h⟩ := bind_eq_ok_iff.mp h
    split at h
    · simp [bind_eq_ok_iff] at h
    · obtain ⟨q, -, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := q
      cases r with
      | Err er => simp at h
      | Ok value_a =>
        replace h : kernel.checker.check_opaque_val_after_annot mode st1 fe cv value_a
            = ok (.Ok fe', st') := h
        rw [kernel.checker.check_opaque_val_after_annot] at h
        obtain ⟨b2, -, h⟩ := bind_eq_ok_iff.mp h
        split at h
        · obtain ⟨b3, -, h⟩ := bind_eq_ok_iff.mp h
          split at h
          · obtain ⟨q2, -, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨r2, st2⟩ := q2
            cases r2 with
            | Err er => simp at h
            | Ok vtype =>
              obtain ⟨q3, -, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨r3, st3⟩ := q3
              cases r3 with
              | Err er => simp at h
              | Ok ok1 =>
                cases ok1 with
                | false => simp at h
                | true =>
                  simp only [] at h
                  obtain ⟨cv1, hcvd, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
                  simp only [Result.ok.injEq, Prod.mk.injEq,
                    core.result.Result.Ok.injEq] at h
                  rw [Env.constant_val_dup_refines hcvd] at hpush
                  rw [← h.1]
                  exact hpush
          · simp [bind_eq_ok_iff] at h
        · simp [bind_eq_ok_iff] at h
  · simp [bind_eq_ok_iff] at h

/-! ### The six arms of `checkDecl`, stated

One statement per arm function of `kernel/checker.rs`, so that
`check_decl_refines` is a `cases` and every arm is owned by exactly one
lemma. -/

/-- `checkDecl`'s `.defnDecl` arm (`Checker.lean:421-500`): the common constant
check, the value check, then the two pinned-`Nat` gates at the pre-insertion
bound `k_pre = fe.visibleBelow`.

Proved: `Refine/CheckerBase.lean`'s `check_constant_val_refines` through
`Indexed.checkConstantVal_eq`, `Refine/Checker.lean`'s `check_defn_val_refines`
through `checkDefnValF_pushC` (the index mirror is the `Env` original followed
by `mkFEnv`), `check_defn_val_push` for the `Indexed` half, and
`Refine/CheckerPins.lean`'s `check_defn_pins_refines`.  The four `Env`-vs-index
spellings the arm reads — `natOpGuard`, `natOpStoredOk`, `env2.find?` and
`checkDivModPin` — go through `ConLeche/Verify/CheckerF.lean`'s `_eq` lemmas at
`mkFEnv`, which is what `Indexed` supplies. -/
theorem check_defn_decl_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr} {hint : env.ReducibilityHint}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_defn_decl mode pins st fe cv value hint = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe → Indexed lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
              (ConLeche.Declaration.defnDecl (absConstantVal cv) (absExpr value)
                (absHint hint))).run lst
            = Except.ok (lfe'.env, lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ Indexed lfe'
      | .Err e =>
        ErrSim e ((ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
          (ConLeche.Declaration.defnDecl (absConstantVal cv) (absExpr value)
            (absHint hint))).run lst) := by
  intro lst lfe hsr hfr hix
  rw [kernel.checker.check_defn_decl] at h
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  cases r with
  | Err er =>
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim er _
    have herr :=
      CheckerBase.check_constant_val_refines hfuel hk constsResolveFSpec hsw hfw hcv
        (hq : checker_base.check_constant_val mode st fe cv = ok (.Err er, st1))
        lst lfe hsr hfr
    rw [hix.checkConstantVal_eq] at herr
    exact ErrSim.trans herr (fun _ hle => by
      rw [ConLeche.checkDecl]; exact run_bind_err_head hle)
  | Ok cv_a =>
    have hqb : checker_base.check_constant_val mode st fe cv = ok (.Ok cv_a, st1) := hq
    obtain ⟨hfind0, hnameq⟩ := check_constant_val_fresh hqb
    obtain ⟨lst1, hruncvF, hsr1, hsw1, hcvawf⟩ :=
      CheckerBase.check_constant_val_refines hfuel hk constsResolveFSpec hsw hfw hcv hqb
        lst lfe hsr hfr
    rw [hix.checkConstantVal_eq] at hruncvF
    have hfresh : lfe.find? (absName cv_a.name) = none := by
      rw [hnameq]
      have hf := FEnv.find_refines hfr hfw hcv.1 hfind0
      simpa using hf.symm
    obtain ⟨q2, hq2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, st2⟩ := q2
    cases r1 with
    | Err er =>
      obtain ⟨hout, -⟩ := err_outS h
      subst hout
      show ErrSim er _
      have herr :=
        Checker.check_defn_val_refines hfuel hk CoreK.pinnedBasisNames hsw1 hfw hcvawf hv
          hq2 lst1 lfe hsr1 hfr
      have hbridge := checkDefnValF_pushC (TypeChecker.lops mode lfe) lfe.env
        (absConstantVal cv_a) (absExpr value) (absHint hint)
      rw [← hix] at hbridge
      rw [hbridge] at herr
      refine ErrSim.trans herr (fun le hle => ?_)
      rw [ConLeche.checkDecl]
      exact run_bind_ok hruncvF (run_bind_err_head (run_bind_pure_err_inv hle))
    | Ok fe2 =>
      obtain ⟨lst2, lfeS, hrunF, hsr2, hsw2, hrelS, hwfS⟩ :=
        Checker.check_defn_val_refines hfuel hk CoreK.pinnedBasisNames hsw1 hfw hcvawf hv
          hq2 lst1 lfe hsr1 hfr
      obtain ⟨value_a, sta, hann, hpush⟩ := check_defn_val_push hq2
      obtain ⟨lsta, -, -, -, hvawf⟩ :=
        (TypeChecker.annotate_core_refines hfuel hk).ok st1 fe 0#u64 value value_a sta
          hsw1 hfw hv hann lst1 lfe hsr1 hfr
      obtain ⟨hrel2, hwf2⟩ := FEnv.push_refines hfr hfw
        (show ConstantInfoWF (env.ConstantInfo.DefnInfo cv_a value_a hint) from
          ⟨hcvawf, hvawf⟩) hpush
      have hix2 : Indexed (lfe.push (absConstantInfo
          (env.ConstantInfo.DefnInfo cv_a value_a hint))) := hix.push _
      -- the value check at the `Env` spelling
      have hbridge := checkDefnValF_pushC (TypeChecker.lops mode lfe) lfe.env
        (absConstantVal cv_a) (absExpr value) (absHint hint)
      rw [← hix] at hbridge
      rw [hbridge] at hrunF
      obtain ⟨e0, l0, hrunE, hp⟩ := run_bind_ok_inv hrunF
      have hpp : ConLeche.mkFEnv e0 = lfeS ∧ l0 = lst2 := by
        have he : (Except.ok (ConLeche.mkFEnv e0, l0) :
            Except ConLeche.CheckError (ConLeche.FEnv × ConLeche.Cached.CState))
            = .ok (lfeS, lst2) := hp
        simpa using he
      have he0 : e0 = (lfe.push (absConstantInfo
          (env.ConstantInfo.DefnInfo cv_a value_a hint))).env := by
        have h1 : ConLeche.mkFEnv e0 = lfeS := hpp.1
        have h2 : lfeS.env = (lfe.push (absConstantInfo
            (env.ConstantInfo.DefnInfo cv_a value_a hint))).env := hrelS.1.symm.trans hrel2.1
        rw [← h2, ← h1]
        rfl
      rw [he0, hpp.2] at hrunE
      -- the pin gates, at the pre-insertion view
      have hcifresh : lfe.find? (absConstantInfo
          (env.ConstantInfo.DefnInfo cv_a value_a hint)).name = none := hfresh
      have hlfp : lfe.find?
          = ((lfe.push (absConstantInfo (env.ConstantInfo.DefnInfo cv_a value_a hint))).restrictTo
              (fe.visible_below).val).find? := by
        rw [hfr.2.1, push_restrict_find hcifresh]
      have hres :=
        CheckerPins.check_defn_pins_refines hfuel hk hsw2 hwf2 hcvawf.1 hvar hpins h lst2
          (lfe.push (absConstantInfo (env.ConstantInfo.DefnInfo cv_a value_a hint))) lfe
          hsr2 hrel2 (fun _ hr => BasisPins.eq_basis_pinned_refines hrel2 hwf2 hr) hlfp
      -- the four `Env`-vs-index spellings the arm reads
      have hguard : ConLeche.natOpGuard (lfe.push (absConstantInfo
            (env.ConstantInfo.DefnInfo cv_a value_a hint))).env (absConstantVal cv_a).name
          = ConLeche.natOpGuardF (lfe.push (absConstantInfo
            (env.ConstantInfo.DefnInfo cv_a value_a hint))) (absConstantVal cv_a).name := by
        rw [← ConLeche.natOpGuardF_eq, ← hix2]
      have hstored : ConLeche.natOpStoredOk (lfe.push (absConstantInfo
            (env.ConstantInfo.DefnInfo cv_a value_a hint))).env
          = ConLeche.natOpStoredOkF (lfe.push (absConstantInfo
            (env.ConstantInfo.DefnInfo cv_a value_a hint))) := by
        rw [← ConLeche.natOpStoredOkF_eq_fun, ← hix2]
      have hfindE : (lfe.push (absConstantInfo
            (env.ConstantInfo.DefnInfo cv_a value_a hint))).env.find?
              (absConstantVal cv_a).name
          = (lfe.push (absConstantInfo
            (env.ConstantInfo.DefnInfo cv_a value_a hint))).find?
              (absConstantVal cv_a).name := (hix2.find_eq _).symm
      have hdmE : ConLeche.checkDivModPin (TypeChecker.lops mode lfe) lfe.env
            (lfe.push (absConstantInfo
              (env.ConstantInfo.DefnInfo cv_a value_a hint))).env (absConstantVal cv_a).name
          = ConLeche.checkDivModPinF (TypeChecker.lops mode lfe) lfe
            (lfe.push (absConstantInfo
              (env.ConstantInfo.DefnInfo cv_a value_a hint))) (absConstantVal cv_a).name := by
        rw [← ConLeche.checkDivModPinF_eq, ← hix, ← hix2]
      -- the `Nat.div`/`Nat.mod` gate, with the arm's `pure env2` continuation
      have divmod : ∀ (l3 l4 : ConLeche.Cached.CState),
          ((if ConLeche.natDivModNames.contains (absConstantVal cv_a).name then
              ConLeche.checkDivModPinF (TypeChecker.lops mode lfe) lfe
                (lfe.push (absConstantInfo (env.ConstantInfo.DefnInfo cv_a value_a hint)))
                (absConstantVal cv_a).name
            else pure ()) : ConLeche.Cached.CheckCM Unit).run l3 = .ok ((), l4) →
          ((if ConLeche.natDivModNames.contains (absConstantVal cv_a).name then
              (do ConLeche.checkDivModPinF (TypeChecker.lops mode lfe) lfe
                    (lfe.push (absConstantInfo
                      (env.ConstantInfo.DefnInfo cv_a value_a hint)))
                    (absConstantVal cv_a).name
                  pure (lfe.push (absConstantInfo
                    (env.ConstantInfo.DefnInfo cv_a value_a hint))).env)
            else pure (lfe.push (absConstantInfo
              (env.ConstantInfo.DefnInfo cv_a value_a hint))).env)
            : ConLeche.Cached.CheckCM ConLeche.Env).run l3
            = .ok ((lfe.push (absConstantInfo
              (env.ConstantInfo.DefnInfo cv_a value_a hint))).env, l4) := by
        intro l3 l4 hh
        by_cases hdm : ConLeche.natDivModNames.contains (absConstantVal cv_a).name = true
        · rw [if_pos hdm] at hh ⊢
          exact run_bind_ok hh rfl
        · rw [if_neg hdm] at hh ⊢
          have hl : l4 = l3 := by
            have he : (Except.ok ((), l3) :
                Except ConLeche.CheckError (Unit × ConLeche.Cached.CState)) = .ok ((), l4) := hh
            exact (show l3 = l4 by simpa using he).symm
          rw [hl]; rfl
      cases out with
      | Err e =>
        show ErrSim e _
        refine ErrSim.trans (hres lfe.env) (fun le hle => ?_)
        rw [ConLeche.checkDecl]
        refine run_bind_ok hruncvF ?_
        refine run_bind_ok hrunE ?_
        rw [hdmE, hguard, hstored, hfindE]
        show (defnGatesInlined (TypeChecker.lops mode lfe) lfe
            (lfe.push (absConstantInfo (env.ConstantInfo.DefnInfo cv_a value_a hint)))
            lfe.env (absConstantVal cv_a).name
            (pure (lfe.push (absConstantInfo
              (env.ConstantInfo.DefnInfo cv_a value_a hint))).env)).run lst2
          = Except.error le
        rw [defnGatesInlined_eq]
        exact run_bind_err_head hle
      | Ok fe' =>
        obtain ⟨lst3, lst4, hA, hB, hC, hsr4, hsw4, hrel4, hwf4⟩ := hres
        have hC' : ((if ConLeche.natDivModNames.contains (absConstantVal cv_a).name then
              ConLeche.checkDivModPinF (TypeChecker.lops mode lfe) lfe
                (lfe.push (absConstantInfo (env.ConstantInfo.DefnInfo cv_a value_a hint)))
                (absConstantVal cv_a).name
            else pure ()) : ConLeche.Cached.CheckCM Unit).run lst3 = .ok ((), lst4) := hC
        refine ⟨lst4, lfe.push (absConstantInfo
          (env.ConstantInfo.DefnInfo cv_a value_a hint)), ?_, hsr4, hsw4, hrel4, hwf4, hix2⟩
        rw [ConLeche.checkDecl]
        refine run_bind_ok hruncvF ?_
        refine run_bind_ok hrunE ?_
        rw [hdmE]
        by_cases hnat : ConLeche.natOpNames.contains (absConstantVal cv_a).name = true
        · rw [if_pos hnat]
          obtain ⟨hg, hd2, cvL, value', hintL, hfindL, hcert⟩ := hA hnat
          have hg' : ConLeche.natOpGuardF (lfe.push (absConstantInfo
              (env.ConstantInfo.DefnInfo cv_a value_a hint)))
              (absConstantVal cv_a).name = true := hg
          have hd2' : ((ConLeche.natOpDeps (absConstantVal cv_a).name).all
              (ConLeche.natOpStoredOkF (lfe.push (absConstantInfo
                (env.ConstantInfo.DefnInfo cv_a value_a hint))))) = true := hd2
          have hfindL' : (lfe.push (absConstantInfo
              (env.ConstantInfo.DefnInfo cv_a value_a hint))).find?
                (absConstantVal cv_a).name = some (.defnInfo cvL value' hintL) := hfindL
          have hcert' : (ConLeche.certifyNatEqs (TypeChecker.lops mode lfe) lfe.env
              ((ConLeche.natOpEquations 0 (absConstantVal cv_a).name).map fun eq =>
                (ConLeche.Expr.substConst0 (absConstantVal cv_a).name value' eq.1,
                 ConLeche.Expr.substConst0 (absConstantVal cv_a).name value' eq.2))).run lst2
              = .ok (true, lst3) := hcert lfe.env
          rw [hguard, hstored]
          rw [if_pos (show (ConLeche.natOpGuardF (lfe.push (absConstantInfo
              (env.ConstantInfo.DefnInfo cv_a value_a hint))) (absConstantVal cv_a).name &&
            (ConLeche.natOpDeps (absConstantVal cv_a).name).all
              (ConLeche.natOpStoredOkF (lfe.push (absConstantInfo
                (env.ConstantInfo.DefnInfo cv_a value_a hint))))) = true from by
            rw [hg', hd2']; rfl)]
          rw [hfindE, hfindL']
          simp only []
          refine run_bind_ok hcert' ?_
          simp only [if_true]
          exact divmod lst3 lst4 hC'
        · rw [if_neg hnat]
          have hnatf : ConLeche.natOpNames.contains (absConstantVal cv_a).name = false := by
            simpa using hnat
          rw [← hB hnatf]
          exact divmod lst3 lst4 hC'


/-- `check_defn_decl_refines` at a success, the pre-#67 statement. -/
theorem check_defn_decl_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr} {hint : env.ReducibilityHint}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_defn_decl mode pins st fe cv value hint
        = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe → Indexed lfe →
      ∃ lst' lfe',
        (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
            (ConLeche.Declaration.defnDecl (absConstantVal cv) (absExpr value)
              (absHint hint))).run lst
          = Except.ok (lfe'.env, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ Indexed lfe' :=
  check_defn_decl_refines hfuel hk hvar hpins hsw hfw hcv hv h

/-- `checkDecl`'s `.thmDecl` arm (`Checker.lean:501-503`).

Proved: `Refine/CheckerBase.lean`'s `check_constant_val_refines` (through
`Indexed.checkConstantVal_eq`), `Refine/Checker.lean`'s `check_thm_val_refines`
at `lenv := lfe.env`, and `check_thm_val_push` for the `Indexed` half. -/
theorem check_thm_decl_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_thm_decl mode st fe cv value = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe → Indexed lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
              (ConLeche.Declaration.thmDecl (absConstantVal cv) (absExpr value))).run lst
            = Except.ok (lfe'.env, lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ Indexed lfe'
      | .Err e =>
        ErrSim e ((ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
          (ConLeche.Declaration.thmDecl (absConstantVal cv) (absExpr value))).run lst) := by
  intro lst lfe hsr hfr hix
  rw [kernel.checker.check_thm_decl] at h
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  cases r with
  | Err er =>
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim er _
    have herr :=
      CheckerBase.check_constant_val_refines hfuel hk constsResolveFSpec hsw hfw hcv
        (hq : checker_base.check_constant_val mode st fe cv = ok (.Err er, st1))
        lst lfe hsr hfr
    rw [hix.checkConstantVal_eq] at herr
    exact ErrSim.trans herr (fun _ hle => by
      rw [ConLeche.checkDecl]; exact run_bind_err_head hle)
  | Ok cv_a =>
    obtain ⟨lst1, hruncvF, hsr1, hsw1, hcvawf⟩ :=
      CheckerBase.check_constant_val_refines hfuel hk constsResolveFSpec hsw hfw hcv
        (hq : checker_base.check_constant_val mode st fe cv = ok (.Ok cv_a, st1))
        lst lfe hsr hfr
    rw [hix.checkConstantVal_eq] at hruncvF
    have hrest :=
      Checker.check_thm_val_refines hfuel hk CoreK.pinnedBasisNames hsw1 hfw hcvawf hv h
        lst1 lfe lfe.env hsr1 hfr (fun n => hix.find_eq n) rfl
    cases out with
    | Ok fe' =>
      obtain ⟨lst2, lfeS, hrunS, hsr2, hsw2, hrelS, hwfS⟩ := hrest
      obtain ⟨hrel', hwf'⟩ := FEnv.push_refines hfr hfw
        (show ConstantInfoWF (env.ConstantInfo.ThmInfo cv_a value) from ⟨hcvawf, hv⟩)
        (check_thm_val_push h)
      have henv : lfeS.env
          = (lfe.push (absConstantInfo (env.ConstantInfo.ThmInfo cv_a value))).env := by
        rw [← hrelS.1, ← hrel'.1]
      refine ⟨lst2, lfe.push (absConstantInfo (env.ConstantInfo.ThmInfo cv_a value)), ?_,
        hsr2, hsw2, hrel', hwf', hix.push _⟩
      rw [ConLeche.checkDecl]
      refine run_bind_ok hruncvF ?_
      rw [← henv]
      exact hrunS
    | Err e =>
      show ErrSim e _
      refine ErrSim.trans hrest (fun _ hle => ?_)
      rw [ConLeche.checkDecl]
      exact run_bind_ok hruncvF hle

/-- `check_thm_decl_refines` at a success, the pre-#67 statement. -/
theorem check_thm_decl_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_thm_decl mode st fe cv value = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe → Indexed lfe →
      ∃ lst' lfe',
        (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
            (ConLeche.Declaration.thmDecl (absConstantVal cv) (absExpr value))).run lst
          = Except.ok (lfe'.env, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ Indexed lfe' :=
  check_thm_decl_refines hfuel hk hsw hfw hcv hv h

/-- `checkDecl`'s `.opaqueDecl` arm (`Checker.lean:504-530`): the opaque check,
then the compiler-trust gate for `Lean.reduceNat`/`Lean.reduceBool`.

Proved: `check_constant_val_refines` through `Indexed.checkConstantVal_eq`,
`Refine/Checker.lean`'s `check_opaque_val_refines` at `lenv := lfe.env`,
`check_opaque_val_push` for the `Indexed` half, and
`Refine/CheckerPins.lean`'s `check_reduce_pin_refines_at_view`;
`ConLeche/Verify/CheckerF.lean`'s `checkReducePinF_eq` moves the gate from the
`Env` spelling `checkDecl` uses to the index one the sibling proves. -/
theorem check_opaque_decl_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_opaque_decl mode st fe cv value = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe → Indexed lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
              (ConLeche.Declaration.opaqueDecl (absConstantVal cv)
                (absExpr value))).run lst = Except.ok (lfe'.env, lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ Indexed lfe'
      | .Err e =>
        ErrSim e ((ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
          (ConLeche.Declaration.opaqueDecl (absConstantVal cv)
            (absExpr value))).run lst) := by
  intro lst lfe hsr hfr hix
  rw [kernel.checker.check_opaque_decl] at h
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  cases r with
  | Err er =>
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim er _
    have herr :=
      CheckerBase.check_constant_val_refines hfuel hk constsResolveFSpec hsw hfw hcv
        (hq : checker_base.check_constant_val mode st fe cv = ok (.Err er, st1))
        lst lfe hsr hfr
    rw [hix.checkConstantVal_eq] at herr
    exact ErrSim.trans herr (fun _ hle => by
      rw [ConLeche.checkDecl]; exact run_bind_err_head hle)
  | Ok cv_a =>
    have hqb : checker_base.check_constant_val mode st fe cv = ok (.Ok cv_a, st1) := hq
    obtain ⟨hfind, hnameq⟩ := check_constant_val_fresh hqb
    obtain ⟨lst1, hruncvF, hsr1, hsw1, hcvawf⟩ :=
      CheckerBase.check_constant_val_refines hfuel hk constsResolveFSpec hsw hfw hcv hqb
        lst lfe hsr hfr
    rw [hix.checkConstantVal_eq] at hruncvF
    have hfresh : lfe.find? (absName cv_a.name) = none := by
      rw [hnameq]
      have hf := FEnv.find_refines hfr hfw hcv.1 hfind
      simpa using hf.symm
    obtain ⟨q2, hq2, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, st2⟩ := q2
    cases r1 with
    | Err er =>
      obtain ⟨hout, -⟩ := err_outS h
      subst hout
      show ErrSim er _
      have herr :=
        Checker.check_opaque_val_refines hfuel hk CoreK.pinnedBasisNames hsw1 hfw hcvawf
          hv hq2 lst1 lfe lfe.env hsr1 hfr (fun n => hix.find_eq n) rfl
      refine ErrSim.trans herr (fun _ hle => ?_)
      rw [ConLeche.checkDecl]
      exact run_bind_ok hruncvF (run_bind_err_head hle)
    | Ok fe2 =>
      obtain ⟨lst2, lfeS, hrunS, hsr2, hsw2, hrelS, hwfS⟩ :=
        Checker.check_opaque_val_refines hfuel hk CoreK.pinnedBasisNames hsw1 hfw hcvawf
          hv hq2 lst1 lfe lfe.env hsr1 hfr (fun n => hix.find_eq n) rfl
      obtain ⟨hrel2, hwf2⟩ := FEnv.push_refines hfr hfw
        (show ConstantInfoWF (env.ConstantInfo.AxiomInfo cv_a) from hcvawf)
        (check_opaque_val_push hq2)
      have henv2 : lfeS.env
          = (lfe.push (.axiomInfo (absConstantVal cv_a))).env :=
        hrelS.1.symm.trans hrel2.1
      have hix2 : Indexed (lfe.push (.axiomInfo (absConstantVal cv_a))) := hix.push _
      have hrunS' : (ConLeche.checkOpaqueVal (TypeChecker.lops mode lfe) lfe.env
          (absConstantVal cv_a) (absExpr value)).run lst1
          = .ok ((lfe.push (.axiomInfo (absConstantVal cv_a))).env, lst2) := by
        rw [← henv2]; exact hrunS
      obtain ⟨rv, hrv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hrvabs, hrvwf⟩ := TrustAxioms.reduce_op_names_refines hrv
      have hbv := Name.contains_refines hrvwf hcvawf.1 hb
      rw [hrvabs] at hbv
      cases b with
      | false =>
        have hcont : ConLeche.reduceOpNames.contains (absConstantVal cv_a).name = false := by
          rw [absConstantVal_name, ← hbv]
        simp only [Bool.false_eq_true, if_false] at h
        obtain ⟨hout, rfl⟩ := ok_outS h
        subst hout
        refine ⟨lst2, lfe.push (.axiomInfo (absConstantVal cv_a)), ?_, hsr2, hsw2,
          hrel2, hwf2, hix2⟩
        rw [ConLeche.checkDecl]
        refine run_bind_ok hruncvF ?_
        refine run_bind_ok hrunS' ?_
        rw [hcont]
        simp only [Bool.false_eq_true, if_false]
        rfl
      | true =>
        have hcont : ConLeche.reduceOpNames.contains (absConstantVal cv_a).name = true := by
          rw [absConstantVal_name, ← hbv]
        simp only [if_true] at h
        have hcifresh : lfe.find?
            (ConLeche.ConstantInfo.axiomInfo (absConstantVal cv_a)).name = none := hfresh
        have hlfp : lfe.find?
            = ((lfe.push (.axiomInfo (absConstantVal cv_a))).restrictTo
                (fe.visible_below).val).find? := by
          rw [hfr.2.1, push_restrict_find hcifresh]
        have hres :=
          CheckerPins.check_reduce_pin_refines_at_view hfuel hk trustPinsSpec hsw2 hwf2
            hcvawf.1 hv h lst2 (lfe.push (.axiomInfo (absConstantVal cv_a))) lfe hsr2 hrel2
            (trustGuardsSpec hrel2 hwf2) (fun _ hr hw => trustGuardsSpec hr hw) hlfp
        cases out with
        | Ok fe' =>
          obtain ⟨lst3, hrun3, hsr3, hsw3, hrel3, hwf3⟩ := hres
          refine ⟨lst3, lfe.push (.axiomInfo (absConstantVal cv_a)), ?_, hsr3, hsw3,
            hrel3, hwf3, hix2⟩
          rw [ConLeche.checkDecl]
          refine run_bind_ok hruncvF ?_
          refine run_bind_ok hrunS' ?_
          rw [hcont]
          simp only [if_true]
          have hpin : (ConLeche.checkReducePin (TypeChecker.lops mode lfe) lfe.env
              (lfe.push (.axiomInfo (absConstantVal cv_a))).env (absConstantVal cv_a).name
              (absExpr value)).run lst2 = .ok ((), lst3) := by
            rw [← ConLeche.checkReducePinF_eq, ← hix, ← hix2, absConstantVal_name]
            exact hrun3
          exact run_bind_ok hpin rfl
        | Err e =>
          show ErrSim e _
          refine ErrSim.trans hres (fun le hle => ?_)
          rw [ConLeche.checkDecl]
          refine run_bind_ok hruncvF ?_
          refine run_bind_ok hrunS' ?_
          rw [hcont]
          simp only [if_true]
          have hpin : (ConLeche.checkReducePin (TypeChecker.lops mode lfe) lfe.env
              (lfe.push (.axiomInfo (absConstantVal cv_a))).env (absConstantVal cv_a).name
              (absExpr value)).run lst2 = .error le := by
            rw [← ConLeche.checkReducePinF_eq, ← hix, ← hix2, absConstantVal_name]
            exact hle
          exact run_bind_err_head hpin

/-- `check_opaque_decl_refines` at a success, the pre-#67 statement. -/
theorem check_opaque_decl_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_opaque_decl mode st fe cv value = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe → Indexed lfe →
      ∃ lst' lfe',
        (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
            (ConLeche.Declaration.opaqueDecl (absConstantVal cv)
              (absExpr value))).run lst = Except.ok (lfe'.env, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ Indexed lfe' :=
  check_opaque_decl_refines hfuel hk hsw hfw hcv hv h


/-- `checkDecl`'s `.axiomDecl` arm (`Checker.lean:531-552`): the two standard
axioms and the `Init` compiler-trust family are *installed* with their shapes
pinned; the tolerated whitelist (exactly `sorryAx`) is checked and **not**
stored; every other axiom, and a pinned name with a non-pinned shape, is a
positive decline.

Proved: `Refine/StdAxioms.lean`'s `std_axiom_ok_refines_of_rel` /
`tolerated_axiom_names_refines`, `Refine/TrustAxioms.lean`'s
`trust_compiler_ok_refines` / `of_reduce_ax_ok_refines`, and
`Refine/FEnv.lean`'s `push_refines`; the `Env`-vs-index spellings go through
`Indexed.stdAxiomOk_eq` and its two siblings. -/
theorem check_axiom_decl_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {cv : env.ConstantVal}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv)
    (h : kernel.checker.check_axiom_decl mode st fe cv = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe → Indexed lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
              (ConLeche.Declaration.axiomDecl (absConstantVal cv))).run lst
            = Except.ok (lfe'.env, lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ Indexed lfe'
      | .Err e =>
        ErrSim e ((ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
          (ConLeche.Declaration.axiomDecl (absConstantVal cv))).run lst) := by
  intro lst lfe hsr hfr hix
  rw [kernel.checker.check_axiom_decl] at h
  obtain ⟨q, hq, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  cases r with
  | Err er =>
    obtain ⟨hout, -⟩ := err_outS h
    subst hout
    show ErrSim er _
    have herr :=
      CheckerBase.check_constant_val_refines hfuel hk constsResolveFSpec hsw hfw hcv
        (hq : checker_base.check_constant_val mode st fe cv = ok (.Err er, st1))
        lst lfe hsr hfr
    rw [hix.checkConstantVal_eq] at herr
    exact ErrSim.trans herr (fun _ hle => by
      rw [ConLeche.checkDecl]; exact run_bind_err_head hle)
  | Ok cv_a =>
    obtain ⟨lst1, hruncvF, hsr1, hsw1, hcvawf⟩ :=
      CheckerBase.check_constant_val_refines hfuel hk constsResolveFSpec hsw hfw hcv
        (hq : checker_base.check_constant_val mode st fe cv = ok (.Ok cv_a, st1))
        lst lfe hsr hfr
    rw [hix.checkConstantVal_eq] at hruncvF
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    have hbabs :=
      (StdAxioms.std_axiom_ok_refines_of_rel hfr hfw (eqBasisPinned hfr hfw) hcvawf hb).trans
        (hix.stdAxiomOk_eq _)
    cases b with
    | true =>
      simp only [if_pos] at h
      obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨hout, rfl⟩ := ok_outS h
      subst hout
      obtain ⟨hrel', hwf'⟩ := FEnv.push_refines hfr hfw
        (show ConstantInfoWF (env.ConstantInfo.AxiomInfo cv_a) from hcvawf) hpush
      refine ⟨lst1, lfe.push (.axiomInfo (absConstantVal cv_a)), ?_, hsr1, hsw1,
        hrel', hwf', hix.push _⟩
      rw [ConLeche.checkDecl]
      refine run_bind_ok hruncvF ?_
      rw [if_pos hbabs.symm]
      rfl
    | false =>
      have hstdf : ¬ (ConLeche.stdAxiomOk lfe.env (absConstantVal cv_a) = true) := by
        rw [← hbabs]; simp
      simp only [Bool.false_eq_true, if_false] at h
      obtain ⟨tn, htn, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨htnabs, htnwf⟩ := TrustAxioms.trust_compiler_name_refines htn
      have hb1abs := Name.beq_refines hcvawf.1 htnwf hb1
      rw [htnabs] at hb1abs
      cases b1 with
      | true =>
        have hnm : (absConstantVal cv_a).name = ConLeche.trustCompilerName := by
          rw [absConstantVal_name]; simpa using hb1abs.symm
        obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
        have hb2abs := (TrustAxioms.trust_compiler_ok_refines matchesPinSpec
          (FindAgree.of_rel hfr hfw) (FindWF.of_wf hfw) hcvawf hb2).trans
            (hix.trustCompilerOk_eq _)
        cases b2 with
        | false =>
          obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hout, -⟩ := err_outS h
          subst hout
          show ErrSim ce _
          refine errSim_notImplemented
            (ls := s!"unsupported Lean.trustCompiler shape ({(absConstantVal cv).name})")
            hce rfl ?_
          rw [ConLeche.checkDecl]
          refine run_bind_ok hruncvF ?_
          rw [if_neg hstdf, if_pos hnm,
            if_neg (show ¬ (ConLeche.trustCompilerOk lfe.env (absConstantVal cv_a) = true)
              from by rw [← hb2abs]; simp)]
          rfl
        | true =>
          simp only [if_pos] at h
          obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hout, rfl⟩ := ok_outS h
          subst hout
          obtain ⟨hrel', hwf'⟩ := FEnv.push_refines hfr hfw
            (show ConstantInfoWF (env.ConstantInfo.AxiomInfo cv_a) from hcvawf) hpush
          refine ⟨lst1, lfe.push (.axiomInfo (absConstantVal cv_a)), ?_, hsr1, hsw1,
            hrel', hwf', hix.push _⟩
          rw [ConLeche.checkDecl]
          refine run_bind_ok hruncvF ?_
          rw [if_neg hstdf, if_pos hnm, if_pos hb2abs.symm]
          rfl
      | false =>
        have hnotc : ¬ ((absConstantVal cv_a).name = ConLeche.trustCompilerName) := by
          rw [absConstantVal_name]
          intro hc; rw [hc] at hb1abs; simp at hb1abs
        obtain ⟨rn, hrn, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hrnabs, hrnwf⟩ := TrustAxioms.of_reduce_nat_name_refines hrn
        have hb2abs := Name.beq_refines hcvawf.1 hrnwf hb2
        rw [hrnabs] at hb2abs
        cases b2 with
        | true =>
          have hnm : (absConstantVal cv_a).name = ConLeche.ofReduceNatName ∨
              (absConstantVal cv_a).name = ConLeche.ofReduceBoolName :=
            Or.inl (by rw [absConstantVal_name]; simpa using hb2abs.symm)
          obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
          have hb3abs := (TrustAxioms.of_reduce_ax_ok_refines matchesPinSpec
            (basisPinsSpec hfr hfw) (FindAgree.of_rel hfr hfw) (FindWF.of_wf hfw)
            hcvawf hb3).trans (hix.ofReduceAxOk_eq _)
          cases b3 with
          | false =>
            obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hout, -⟩ := err_outS h
            subst hout
            show ErrSim ce _
            refine errSim_notImplemented
              (ls := s!"unsupported compiler-trust axiom environment ({(absConstantVal cv).name})")
              hce rfl ?_
            rw [ConLeche.checkDecl]
            refine run_bind_ok hruncvF ?_
            rw [if_neg hstdf, if_neg hnotc, if_pos hnm,
              if_neg (show ¬ (ConLeche.ofReduceAxOk lfe.env (absConstantVal cv_a) = true)
                from by rw [← hb3abs]; simp)]
            rfl
          | true =>
            simp only [if_pos] at h
            obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hout, rfl⟩ := ok_outS h
            subst hout
            obtain ⟨hrel', hwf'⟩ := FEnv.push_refines hfr hfw
              (show ConstantInfoWF (env.ConstantInfo.AxiomInfo cv_a) from hcvawf) hpush
            refine ⟨lst1, lfe.push (.axiomInfo (absConstantVal cv_a)), ?_, hsr1, hsw1,
              hrel', hwf', hix.push _⟩
            rw [ConLeche.checkDecl]
            refine run_bind_ok hruncvF ?_
            rw [if_neg hstdf, if_neg hnotc, if_pos hnm, if_pos hb3abs.symm]
            rfl
        | false =>
          have hnotn : ¬ ((absConstantVal cv_a).name = ConLeche.ofReduceNatName) := by
            rw [absConstantVal_name]
            intro hc; rw [hc] at hb2abs; simp at hb2abs
          obtain ⟨bn, hbn, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hbnabs, hbnwf⟩ := TrustAxioms.of_reduce_bool_name_refines hbn
          have hb3abs := Name.beq_refines hcvawf.1 hbnwf hb3
          rw [hbnabs] at hb3abs
          cases b3 with
          | true =>
            have hnm : (absConstantVal cv_a).name = ConLeche.ofReduceNatName ∨
                (absConstantVal cv_a).name = ConLeche.ofReduceBoolName :=
              Or.inr (by rw [absConstantVal_name]; simpa using hb3abs.symm)
            obtain ⟨b4, hb4, h⟩ := bind_eq_ok_iff.mp h
            have hb4abs := (TrustAxioms.of_reduce_ax_ok_refines matchesPinSpec
              (basisPinsSpec hfr hfw) (FindAgree.of_rel hfr hfw) (FindWF.of_wf hfw)
              hcvawf hb4).trans (hix.ofReduceAxOk_eq _)
            cases b4 with
            | false =>
              obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨hout, -⟩ := err_outS h
              subst hout
              show ErrSim ce _
              refine errSim_notImplemented
                (ls := s!"unsupported compiler-trust axiom environment ({(absConstantVal cv).name})")
                hce rfl ?_
              rw [ConLeche.checkDecl]
              refine run_bind_ok hruncvF ?_
              rw [if_neg hstdf, if_neg hnotc, if_pos hnm,
                if_neg (show ¬ (ConLeche.ofReduceAxOk lfe.env (absConstantVal cv_a) = true)
                  from by rw [← hb4abs]; simp)]
              rfl
            | true =>
              simp only [if_pos] at h
              obtain ⟨f, hpush, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨hout, rfl⟩ := ok_outS h
              subst hout
              obtain ⟨hrel', hwf'⟩ := FEnv.push_refines hfr hfw
                (show ConstantInfoWF (env.ConstantInfo.AxiomInfo cv_a) from hcvawf) hpush
              refine ⟨lst1, lfe.push (.axiomInfo (absConstantVal cv_a)), ?_, hsr1, hsw1,
                hrel', hwf', hix.push _⟩
              rw [ConLeche.checkDecl]
              refine run_bind_ok hruncvF ?_
              rw [if_neg hstdf, if_neg hnotc, if_pos hnm, if_pos hb4abs.symm]
              rfl
          | false =>
            have hnotb : ¬ ((absConstantVal cv_a).name = ConLeche.ofReduceBoolName) := by
              rw [absConstantVal_name]
              intro hc; rw [hc] at hb3abs; simp at hb3abs
            have hnotnb : ¬ ((absConstantVal cv_a).name = ConLeche.ofReduceNatName ∨
                (absConstantVal cv_a).name = ConLeche.ofReduceBoolName) :=
              fun hc => hc.elim hnotn hnotb
            obtain ⟨pn, hpn, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨b4, hb4, h⟩ := bind_eq_ok_iff.mp h
            obtain ⟨hpnabs, hpnwf⟩ := StdAxioms.propext_name_refines hpn
            have hb4abs := Name.beq_refines hcvawf.1 hpnwf hb4
            rw [hpnabs] at hb4abs
            cases b4 with
            | true =>
              obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨hout, -⟩ := err_outS h
              subst hout
              show ErrSim ce _
              refine errSim_notImplemented
                (ls := s!"standard axiom shape mismatch ({(absConstantVal cv).name})")
                hce rfl ?_
              rw [ConLeche.checkDecl]
              refine run_bind_ok hruncvF ?_
              rw [if_neg hstdf, if_neg hnotc, if_neg hnotnb,
                if_pos (Or.inl (show (absConstantVal cv_a).name = ConLeche.propextName
                  from by rw [absConstantVal_name]; simpa using hb4abs.symm))]
              rfl
            | false =>
              have hnotpe : ¬ ((absConstantVal cv_a).name = ConLeche.propextName) := by
                rw [absConstantVal_name]
                intro hc; rw [hc] at hb4abs; simp at hb4abs
              obtain ⟨cn, hcn, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨b5, hb5, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨hcnabs, hcnwf⟩ := StdAxioms.choice_name_refines hcn
              have hb5abs := Name.beq_refines hcvawf.1 hcnwf hb5
              rw [hcnabs] at hb5abs
              cases b5 with
              | true =>
                obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨hout, -⟩ := err_outS h
                subst hout
                show ErrSim ce _
                refine errSim_notImplemented
                  (ls := s!"standard axiom shape mismatch ({(absConstantVal cv).name})")
                  hce rfl ?_
                rw [ConLeche.checkDecl]
                refine run_bind_ok hruncvF ?_
                rw [if_neg hstdf, if_neg hnotc, if_neg hnotnb,
                  if_pos (Or.inr (show (absConstantVal cv_a).name = ConLeche.choiceName
                    from by rw [absConstantVal_name]; simpa using hb5abs.symm))]
                rfl
              | false =>
                have hnotch : ¬ ((absConstantVal cv_a).name = ConLeche.choiceName) := by
                  rw [absConstantVal_name]
                  intro hc; rw [hc] at hb5abs; simp at hb5abs
                have hnotpc : ¬ ((absConstantVal cv_a).name = ConLeche.propextName ∨
                    (absConstantVal cv_a).name = ConLeche.choiceName) :=
                  fun hc => hc.elim hnotpe hnotch
                obtain ⟨tv, htv, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨b6, hb6, h⟩ := bind_eq_ok_iff.mp h
                obtain ⟨htvabs, htvwf⟩ := StdAxioms.tolerated_axiom_names_refines htv
                have hb6abs := Name.contains_refines htvwf hcvawf.1 hb6
                rw [htvabs] at hb6abs
                cases b6 with
                | false =>
                  obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
                  obtain ⟨hout, -⟩ := err_outS h
                  subst hout
                  show ErrSim ce _
                  refine errSim_notImplemented
                    (ls := s!"non-standard axiom ({(absConstantVal cv).name})")
                    hce rfl ?_
                  rw [ConLeche.checkDecl]
                  refine run_bind_ok hruncvF ?_
                  rw [if_neg hstdf, if_neg hnotc, if_neg hnotnb, if_neg hnotpc,
                    if_neg (show ¬ (ConLeche.toleratedAxiomNames.contains
                      (absConstantVal cv_a).name = true) from by
                        rw [absConstantVal_name, ← hb6abs]; simp)]
                  rfl
                | true =>
                  simp only [if_pos] at h
                  obtain ⟨hout, rfl⟩ := ok_outS h
                  subst hout
                  refine ⟨lst1, lfe, ?_, hsr1, hsw1, hfr, hfw, hix⟩
                  rw [ConLeche.checkDecl]
                  refine run_bind_ok hruncvF ?_
                  rw [if_neg hstdf, if_neg hnotc, if_neg hnotnb, if_neg hnotpc,
                    if_pos (show ConLeche.toleratedAxiomNames.contains
                      (absConstantVal cv_a).name = true from by
                        rw [absConstantVal_name]; simpa using hb6abs.symm)]
                  rfl


/-- `check_axiom_decl_refines` at a success, the pre-#67 statement. -/
theorem check_axiom_decl_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {cv : env.ConstantVal}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv)
    (h : kernel.checker.check_axiom_decl mode st fe cv = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe → Indexed lfe →
      ∃ lst' lfe',
        (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
            (ConLeche.Declaration.axiomDecl (absConstantVal cv))).run lst
          = Except.ok (lfe'.env, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ Indexed lfe' :=
  check_axiom_decl_refines hfuel hk hsw hfw hcv h

/-- `checkDecl`'s `.basisDecl` arm (`Checker.lean:553-557`): the quotient block
requires the pinned `Eq` basis, then `kind.declsA.foldlM installBasisDecl`.
The block is `basis_tables::basis_decls_a`, and task #22's
`Refine/BasisTables.lean` is what says it *is* `BasisKind.declsA`.

Proved: `Refine/BasisPins.lean`'s `eq_basis_pinned_refines` for the quotient
gate, `install_basis_decls_refines` above for the fold, and
`installBasisDecl_fold_env` to move that fold from `installBasisDeclF` at the
index to `installBasisDecl` at its environment. -/
theorem check_basis_decl_refines {mode : env.CheckMode}
    {fe : fenv.FEnv} {kind : env.BasisKind}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hfw : FEnvWF fe)
    (h : kernel.checker.check_basis_decl fe kind = ok out) :
    ∀ lst lfe, FEnvRel fe lfe → Indexed lfe →
      match out with
      | .Ok fe' =>
        ∃ lfe',
          (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
              (ConLeche.Declaration.basisDecl (absBasisKind kind))).run lst
            = Except.ok (lfe'.env, lst)
          ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' ∧ Indexed lfe'
      | .Err e =>
        ErrSim e ((ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
          (ConLeche.Declaration.basisDecl (absBasisKind kind))).run lst) := by
  intro lst lfe hfr hix
  rw [kernel.checker.check_basis_decl.eq_def] at h
  rw [ConLeche.checkDecl]
  -- the install, shared by all six arms, at the `Env` spelling
  have install : ∀ (v : alloc.vec.Vec env.ConstantInfo)
      (o : core.result.Result fenv.FEnv core_types.CheckError),
      basis_tables.basis_decls_a kind = ok v →
      kernel.checker.install_basis_decls fe v 0#usize = ok o →
      match o with
      | .Ok fe' =>
        ∃ lfe₂,
          ((ConLeche.BasisKind.declsA (absBasisKind kind)).foldlM
              (ConLeche.installBasisDecl (m := ConLeche.Cached.CheckCM)) lfe.env).run lst
            = Except.ok (lfe₂.env, lst)
          ∧ FEnvRel fe' lfe₂ ∧ FEnvWF fe' ∧ Indexed lfe₂
      | .Err e =>
        ErrSim e (((ConLeche.BasisKind.declsA (absBasisKind kind)).foldlM
          (ConLeche.installBasisDecl (m := ConLeche.Cached.CheckCM)) lfe.env).run lst) := by
    intro v o hv hi
    have habs : absConstantInfos v = ConLeche.BasisKind.declsA (absBasisKind kind) := by
      have := ConRon.Refine.absBasisDecls_eq kind
      rw [ConRon.Refine.absBasisDecls, hv] at this
      simpa using this
    have hr :=
      install_basis_decls_refines hfw (canon_of_indexed hfr hix).1
        (canon_of_indexed hfr hix).2 (BasisPins.basis_decls_a_wf hv) hi lfe lst hfr
    rw [habs] at hr
    cases o with
    | Ok fe' =>
      obtain ⟨lfe₂, hfold, hrel, hwf, -, -⟩ := hr
      obtain ⟨hfoldE, hix₂⟩ := installBasisDecl_fold_env _ lfe lfe₂ lst hix hfold
      exact ⟨lfe₂, hfoldE, hrel, hwf, hix₂⟩
    | Err e =>
      show ErrSim e _
      exact ErrSim.trans hr (fun le hle =>
        installBasisDecl_fold_env_err _ lfe lst le hix hle)
  cases kind with
  | QuotK =>
    obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
    have hbv := BasisPins.eq_basis_pinned_refines hfr hfw hb
    cases b with
    | false =>
      obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
      have hout : out = .Err ce := err_out h
      subst hout
      have hne : ¬ (lfe.env.find? ConLeche.eqName = some ConLeche.eqA) := by
        rw [← hix.find_eq]; simpa using hbv.symm
      show ErrSim ce _
      refine errSim_notImplemented
        (ls := "quotient basis requires the pinned Eq basis") hce rfl ?_
      simp only [absBasisKind]
      rw [if_pos trivial, if_neg hne]
      rfl
    | true =>
      obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
      have hr := install v out hv h
      have heq : (lfe.env.find? ConLeche.eqName = some ConLeche.eqA) := by
        rw [← hix.find_eq]; simpa using hbv.symm
      cases out with
      | Ok fe' =>
        obtain ⟨lfe₂, hfold, rest⟩ := hr
        refine ⟨lfe₂, ?_, rest⟩
        simp only [absBasisKind] at hfold ⊢
        rw [show (lfe.env.find? ConLeche.eqName = some ConLeche.eqA) from heq]
        simpa using hfold
      | Err e =>
        show ErrSim e _
        simp only [absBasisKind] at hr ⊢
        rw [show (lfe.env.find? ConLeche.eqName = some ConLeche.eqA) from heq]
        simpa using hr
  | EqK | NatK | PunitK | EmptyK | FalseK =>
    all_goals (
      obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
      have hr := install v out hv h
      cases out with
      | Ok fe' =>
        obtain ⟨lfe₂, hfold, rest⟩ := hr
        refine ⟨lfe₂, ?_, rest⟩
        simp only [absBasisKind] at hfold ⊢
        simpa using hfold
      | Err e =>
        show ErrSim e _
        simp only [absBasisKind] at hr ⊢
        simpa using hr)

/-- `check_basis_decl_refines` at a success, the pre-#67 statement. -/
theorem check_basis_decl_refines_ok {mode : env.CheckMode}
    {fe fe' : fenv.FEnv} {kind : env.BasisKind}
    (hfw : FEnvWF fe)
    (h : kernel.checker.check_basis_decl fe kind = ok (.Ok fe')) :
    ∀ lst lfe, FEnvRel fe lfe → Indexed lfe →
      ∃ lfe',
        (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
            (ConLeche.Declaration.basisDecl (absBasisKind kind))).run lst
          = Except.ok (lfe'.env, lst)
        ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' ∧ Indexed lfe' :=
  check_basis_decl_refines hfw h

/-- **`kernel::checker::check_decl` refines `checkDecl`**
(`ConLeche/Kernel/Checker.lean:419-562`), at the cached operation record.  The
environment in and out is the index (task #18 deviation 3); the Lean's
pre-insertion `Env` is the index's own `env` (module note), and the Lean's
output `Env` is the `env` of an index the port's result stands in `FEnvRel` to.

Proved from the six arm lemmas above, all six of them closed.  The `Indexed`
hypothesis is the section note's. -/
theorem check_decl_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv} {d : env.Declaration}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hd : DeclarationWF d)
    (h : kernel.checker.check_decl mode pins st fe d = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe → Indexed lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
              (absDeclaration d)).run lst = Except.ok (lfe'.env, lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ Indexed lfe'
      | .Err e =>
        ErrSim e ((ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
          (absDeclaration d)).run lst) := by
  intro lst lfe hsr hfr hix
  rw [kernel.checker.check_decl.eq_def] at h
  cases d with
  | AxiomDecl cv =>
    simp only [absDeclaration]
    cases out with
    | Ok fe' => exact check_axiom_decl_refines hfuel hk hsw hfw hd h lst lfe hsr hfr hix
    | Err e => exact check_axiom_decl_refines hfuel hk hsw hfw hd h lst lfe hsr hfr hix
  | DefnDecl cv value hint =>
    simp only [absDeclaration]
    cases out with
    | Ok fe' =>
      exact check_defn_decl_refines hfuel hk hvar hpins hsw hfw hd.1 hd.2 h lst lfe hsr
        hfr hix
    | Err e =>
      exact check_defn_decl_refines hfuel hk hvar hpins hsw hfw hd.1 hd.2 h lst lfe hsr
        hfr hix
  | ThmDecl cv value =>
    simp only [absDeclaration]
    cases out with
    | Ok fe' => exact check_thm_decl_refines hfuel hk hsw hfw hd.1 hd.2 h lst lfe hsr hfr hix
    | Err e => exact check_thm_decl_refines hfuel hk hsw hfw hd.1 hd.2 h lst lfe hsr hfr hix
  | OpaqueDecl cv value =>
    simp only [absDeclaration]
    cases out with
    | Ok fe' =>
      exact check_opaque_decl_refines hfuel hk hsw hfw hd.1 hd.2 h lst lfe hsr hfr hix
    | Err e =>
      exact check_opaque_decl_refines hfuel hk hsw hfw hd.1 hd.2 h lst lfe hsr hfr hix
  | BasisDecl kind =>
    simp only [absDeclaration]
    obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
    have hres := check_basis_decl_refines (mode := mode) hfw hr lst lfe hfr hix
    cases r with
    | Ok fe2 =>
      obtain ⟨hout, rfl⟩ := ok_outS h
      subst hout
      obtain ⟨lfe', hrun, hrel', hwf', hix'⟩ := hres
      exact ⟨lst, lfe', hrun, hsr, hsw, hrel', hwf', hix'⟩
    | Err er =>
      obtain ⟨hout, rfl⟩ := err_outS h
      subst hout
      exact hres
  | IndDecl block n_p =>
    -- task #24's third stub: the `Expr`-level arm never returns `.Ok`, and its
    -- two failures are the port's own `Native` (the routes are unported here,
    -- so nothing is claimed — DESIGN.md task #67 §1's one checker-tier `Native`
    -- site) and the cited arm's own parameter-count `throw`.
    simp only [absDeclaration]
    cases out with
    | Ok fe' => exact absurd h check_ind_decl_declines
    | Err er =>
      show ErrSim er _
      replace h : kernel.checker.check_ind_decl mode st fe block n_p
          = ok (.Err er, st') := h
      rw [kernel.checker.check_ind_decl] at h
      obtain ⟨b, hb', h⟩ := bind_eq_ok_iff.mp h
      have hbv : b = ConLeche.indParamsOk n_p.val (absConstantInfos block) :=
        Env.ind_params_ok_refines hd hb'
      cases b with
      | true =>
        obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hout, -⟩ := err_outS h
        have herce : er = ce := by simpa using hout
        subst herce
        rw [native_val hce]
        exact ErrSim.native v
      | false =>
        obtain ⟨sl, hsl, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨ce, hce, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨hout, -⟩ := err_outS h
        have herce : er = ce := by simpa using hout
        subst herce
        refine errSim_invalid (ls := "number of parameters mismatch") hce rfl ?_
        rw [ConLeche.checkDecl]
        rw [if_neg (show ¬ (ConLeche.indParamsOk n_p.val (absConstantInfos block) = true)
          from by rw [← hbv]; simp)]
        rfl

/-- `check_decl_refines` at a success, the pre-#67 statement. -/
theorem check_decl_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {d : env.Declaration}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hd : DeclarationWF d)
    (h : kernel.checker.check_decl mode pins st fe d = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe → Indexed lfe →
      ∃ lst' lfe',
        (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
            (absDeclaration d)).run lst = Except.ok (lfe'.env, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ Indexed lfe' :=
  check_decl_refines hfuel hk hvar hpins hsw hfw hd h

/-! ## The fold

`checkDeclsPure` (`Checker.lean:564-567`) is `ds.foldlM (checkDecl mode ops)
Env.empty` at **one** operation record.  The port cannot be stated against that
record directly, and the reason is task #24's collapse, not a weakness of the
statement: in the *pure* lane a slot reads its `env` argument
(`fueledOps`'s `annotate env d e := annotateCore mode env F d e`), so one
record serves the whole fold; in the *cached* lane a slot **closes over the
index** (`opE mode fe pick`) and ignores its `env` argument, so the record is
rebuilt at every step -- which is exactly what the port does by re-reading `fe`
at every call.  The bridge between the two lanes is con-leche's own
(`ConLeche/Verify/Cached/*`), not ours.

So the fold is stated against the *per-step* record, as an inductive relation
that says "these declarations take the index from `lfe` to `lfe'`, each step's
call at that step's own index".  This is the shape `Cached/Installed.lean`'s
`checkDecls` has too, which is why `Refine/Installed.lean` (CORE_PLAN step 7's
last file, a later task) can reuse it verbatim. -/

/-- **The port's fold, exactly**: `checkDecl` at each step's own index.  `nil`
is the exhausted fold; `cons` runs one declaration at the current index and
continues at the index the port pushed. -/
inductive FoldsTo (mode : env.CheckMode) :
    ConLeche.Cached.CState -> ConLeche.FEnv -> List ConLeche.Declaration ->
    ConLeche.Cached.CState -> ConLeche.FEnv -> Prop where
  | nil {lst lfe} : FoldsTo mode lst lfe [] lst lfe
  | cons {lst lst₁ lst₂ lfe lfe₁ lfe₂ d ds} :
      (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env d).run lst
          = .ok (lfe₁.env, lst₁) →
      FoldsTo mode lst₁ lfe₁ ds lst₂ lfe₂ →
      FoldsTo mode lst lfe (d :: ds) lst₂ lfe₂

/-- **The port's fold, throwing** (task #67): a prefix of the declarations goes
through, each step at its own index, and then one step throws.  This is
`FoldsTo`'s failure twin — the fold has no single computation to point
`ErrSim` at (the operation record is rebuilt at every step, section note), so
the failure half names the step that threw. -/
inductive FoldsErr (mode : env.CheckMode) :
    ConLeche.Cached.CState -> ConLeche.FEnv -> List ConLeche.Declaration ->
    ConLeche.CheckError -> Prop where
  | head {lst lfe d ds le} :
      (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env d).run lst
          = .error le →
      FoldsErr mode lst lfe (d :: ds) le
  | cons {lst lst₁ lfe lfe₁ d ds le} :
      (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env d).run lst
          = .ok (lfe₁.env, lst₁) →
      FoldsErr mode lst₁ lfe₁ ds le →
      FoldsErr mode lst lfe (d :: ds) le

/-- `Refine/Abs.lean`'s `ErrSim`, at the fold: the port's error has a kind only
if some step of the cited fold throws at that kind.  `Native` makes it vacuous,
exactly as `ErrSim` does. -/
def FoldErrSim (mode : env.CheckMode) (e : core_types.CheckError)
    (lst : ConLeche.Cached.CState) (lfe : ConLeche.FEnv)
    (ds : List ConLeche.Declaration) : Prop :=
  ∀ k, absErrKind e = some k → ∃ le, FoldsErr mode lst lfe ds le ∧ lErrKind le = k

/-- The fold with an explicit bound to recurse on. -/
theorem check_decls_pure_val {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {ds : alloc.vec.Vec env.Declaration} (hds : ∀ d ∈ ds.val, DeclarationWF d) (n : Nat) :
    ∀ (st st' : cached.state_c.CState) (fe : fenv.FEnv)
      (out : core.result.Result fenv.FEnv core_types.CheckError) (i : Std.Usize),
      ds.val.length - i.val ≤ n → StateWF st → FEnvWF fe →
      kernel.checker.check_decls_pure_from mode pins st fe ds i = ok (out, st') →
      ∀ lst lfe, StateRel st lst → FEnvRel fe lfe → Indexed lfe →
        match out with
        | .Ok fe' =>
          ∃ lst' lfe',
            FoldsTo mode lst lfe ((ds.val.drop i.val).map absDeclaration) lst' lfe'
            ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ Indexed lfe'
        | .Err e =>
          FoldErrSim mode e lst lfe ((ds.val.drop i.val).map absDeclaration) := by
  induction n with
  | zero =>
    intro st st' fe out i hb hsw hfw h lst lfe hsr hfr hix
    rw [kernel.checker.check_decls_pure_from] at h
    rw [if_pos (show i >= alloc.vec.Vec.len ds by
      have := alloc.vec.Vec.len_val ds; scalar_tac)] at h
    obtain ⟨hout, rfl⟩ := ok_outS h
    subst hout
    refine ⟨lst, lfe, ?_, hsr, hsw, hfr, hfw, hix⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    exact .nil
  | succ n ih =>
    intro st st' fe out i hb hsw hfw h lst lfe hsr hfr hix
    rw [kernel.checker.check_decls_pure_from] at h
    by_cases hge : i.val >= ds.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len ds by
        have := alloc.vec.Vec.len_val ds; scalar_tac)] at h
      obtain ⟨hout, rfl⟩ := ok_outS h
      subst hout
      refine ⟨lst, lfe, ?_, hsr, hsw, hfr, hfw, hix⟩
      rw [List.drop_eq_nil_of_le (by omega)]
      exact .nil
    · rw [if_neg (show ¬ (i >= alloc.vec.Vec.len ds) by
        have := alloc.vec.Vec.len_val ds; scalar_tac)] at h
      obtain ⟨d, hdi, h⟩ := bind_eq_ok_iff.mp h
      have hmem : d ∈ ds.val := List.mem_of_getElem? (ExprOps.vec_index_getElem? hdi)
      have hlen : i.val < ds.val.length := by omega
      have hdrop : ds.val.drop i.val = d :: ds.val.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hlen]
        congr 1
        have h1 : ds.val[i.val]? = some d := ExprOps.vec_index_getElem? hdi
        rw [List.getElem?_eq_getElem hlen] at h1
        exact Option.some_inj.mp h1
      obtain ⟨q, hstep, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := q
      cases r with
      | Err e =>
        -- the step threw, and it is the cited fold's first failing step
        obtain ⟨hout, -⟩ := err_outS h
        subst hout
        show FoldErrSim mode e lst lfe _
        have herr :=
          check_decl_refines hfuel hk hvar hpins hsw hfw (hds d hmem) hstep lst lfe hsr
            hfr hix
        intro k hkk
        obtain ⟨le, hrun, hkind⟩ := herr k hkk
        refine ⟨le, ?_, hkind⟩
        rw [hdrop, List.map_cons]
        exact .head hrun
      | Ok fe1 =>
        obtain ⟨lst1, lfe1, hrun, hsr1, hsw1, hfr1, hfw1, hix1⟩ :=
          check_decl_refines hfuel hk hvar hpins hsw hfw (hds d hmem) hstep lst lfe hsr hfr hix
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := by
          have he := Std.UScalar.add_equiv i 1#usize
          rw [hi2] at he
          simpa using he.2.1
        have hrec := ih st1 st' fe1 out i2 (by omega) hsw1 hfw1 h lst1 lfe1 hsr1 hfr1 hix1
        rw [hi2v] at hrec
        cases out with
        | Ok fe' =>
          obtain ⟨lst', lfe', hfold, rest⟩ := hrec
          refine ⟨lst', lfe', ?_, rest⟩
          rw [hdrop, List.map_cons]
          exact .cons hrun hfold
        | Err e =>
          show FoldErrSim mode e lst lfe _
          intro k hkk
          obtain ⟨le, hfe, hkind⟩ := hrec k hkk
          refine ⟨le, ?_, hkind⟩
          rw [hdrop, List.map_cons]
          exact .cons hrun hfe

/-- **`kernel::checker::check_decls_pure_from` refines the cited fold's tail**:
the declarations from position `i` take the index where the port says. -/
theorem check_decls_pure_from_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState} {fe : fenv.FEnv}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    {ds : alloc.vec.Vec env.Declaration} {i : Std.Usize}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : kernel.checker.check_decls_pure_from mode pins st fe ds i = ok (out, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe → Indexed lfe →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          FoldsTo mode lst lfe ((ds.val.drop i.val).map absDeclaration) lst' lfe'
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ Indexed lfe'
      | .Err e =>
        FoldErrSim mode e lst lfe ((ds.val.drop i.val).map absDeclaration) := by
  intro lst lfe hsr hfr hix
  have hres := check_decls_pure_val hfuel hk hvar hpins hds ds.val.length st st' fe out i
    (by omega) hsw hfw h lst lfe hsr hfr hix
  cases out with
  | Ok fe' => exact hres
  | Err e => exact hres

/-- `check_decls_pure_from_refines` at a success, the pre-#67 statement. -/
theorem check_decls_pure_from_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {ds : alloc.vec.Vec env.Declaration} {i : Std.Usize}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : kernel.checker.check_decls_pure_from mode pins st fe ds i = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe → Indexed lfe →
      ∃ lst' lfe',
        FoldsTo mode lst lfe ((ds.val.drop i.val).map absDeclaration) lst' lfe'
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ Indexed lfe' :=
  check_decls_pure_from_refines hfuel hk hvar hpins hsw hfw hds h

/-- **`kernel::checker::check_decls_pure` refines `checkDeclsPure`**
(`Checker.lean:564-567`): the whole stream from the empty environment, at the
per-step record (section note).

Proved: `check_decls_pure_from_refines` at `i = 0` plus `Refine/FEnv.lean`'s
`mk_fenv_refines` at `env::empty`, whose index is `Indexed` by construction. -/
theorem check_decls_pure_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState}
    {out : core.result.Result fenv.FEnv core_types.CheckError}
    {ds : alloc.vec.Vec env.Declaration}
    (hsw : StateWF st) (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : kernel.checker.check_decls_pure mode pins st ds = ok (out, st')) :
    ∀ lst, StateRel st lst →
      match out with
      | .Ok fe' =>
        ∃ lst' lfe',
          FoldsTo mode lst (ConLeche.mkFEnv ConLeche.Env.empty)
              (ds.val.map absDeclaration) lst' lfe'
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
          ∧ Indexed lfe'
      | .Err e =>
        FoldErrSim mode e lst (ConLeche.mkFEnv ConLeche.Env.empty)
          (ds.val.map absDeclaration) := by
  intro lst hsr
  rw [kernel.checker.check_decls_pure] at h
  obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨fe0, hfe0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hrel0, hwf0⟩ := FEnv.mk_fenv_refines (Env.empty_wf he) hfe0
  rw [Env.empty_refines he] at hrel0
  have hres :=
    check_decls_pure_from_refines hfuel hk hvar hpins hsw hwf0 hds h lst
      (ConLeche.mkFEnv ConLeche.Env.empty) hsr hrel0 (Indexed.mk _)
  cases out with
  | Ok fe' =>
    obtain ⟨lst', lfe', hfold, rest⟩ := hres
    exact ⟨lst', lfe', by simpa using hfold, rest⟩
  | Err er =>
    show FoldErrSim mode er lst _ _
    intro k hkk
    obtain ⟨le, hfe, hkind⟩ := hres k hkk
    exact ⟨le, by simpa using hfe, hkind⟩

/-- `check_decls_pure_refines` at a success, the pre-#67 statement. -/
theorem check_decls_pure_refines_ok {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hvar : CheckerPins.PinsWF pins)
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState} {fe' : fenv.FEnv}
    {ds : alloc.vec.Vec env.Declaration}
    (hsw : StateWF st) (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : kernel.checker.check_decls_pure mode pins st ds = ok (.Ok fe', st')) :
    ∀ lst, StateRel st lst →
      ∃ lst' lfe',
        FoldsTo mode lst (ConLeche.mkFEnv ConLeche.Env.empty)
            (ds.val.map absDeclaration) lst' lfe'
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ Indexed lfe' :=
  check_decls_pure_refines hfuel hk hvar hpins hsw hds h

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

Nothing in this file reaches `sorryAx` any more: the seam with task #57, the
basis-table install, the parsed constant check, and then the three entry points
the tier above consumes — `checkDeclC`'s dispatch, `checkDecl`'s dispatch, and
the fold. -/

/-- info: 'ConRon.Refine.CheckerDecl.check_ind_decl_c_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_ind_decl_c_refines

/-- info: 'ConRon.Refine.CheckerDecl.install_basis_decls_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms install_basis_decls_refines

/--
info: 'ConRon.Refine.CheckerDecl.check_constant_val_c_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms check_constant_val_c_refines

/-- info: 'ConRon.Refine.CheckerDecl.check_thm_decl_c_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_thm_decl_c_refines

/-! **The three entry points.**  Each is proved from its six arms and each is
clean: the parsed dispatch `checkDeclC`, the `Expr`-level dispatch `checkDecl`,
and the fold `checkDeclsPure` from the empty environment. -/

/--
info: 'ConRon.Refine.CheckerDecl.check_decl_c_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms check_decl_c_refines

/--
info: 'ConRon.Refine.CheckerDecl.check_decl_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms check_decl_refines

/--
info: 'ConRon.Refine.CheckerDecl.check_decls_pure_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms check_decls_pure_refines

end ConRon.Refine.CheckerDecl

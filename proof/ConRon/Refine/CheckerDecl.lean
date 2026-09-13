import ConRon.Refine.TypeChecker
import ConRon.Refine.CheckerC
import ConRon.Refine.IndSpec
import ConRon.Refine.Pins
import ConLeche.Cached.ParsedC

/-! # The `Declaration` level: `check_decl`, `check_decl_c`, the fold (task #56)

`CORE_PLAN.md` step 7's top: `kernel/checker.rs`'s `checkDecl` dispatch
(`ConLeche/Kernel/Checker.lean:419-562`) and `cached/parsed_c.rs`'s
`checkDeclC`/`checkDeclStepC` (`ConLeche/Cached/ParsedC.lean:158-241`,
`:259-262`), plus the `checkDeclsPure` fold (`Checker.lean:564-567`).

The arms' own lemmas live in `Refine/Checker.lean` (the value checks,
`installBasisDecl`, `certifyNatEqs`) and `Refine/CheckerPins.lean` (the
`Nat.div`/`Nat.mod` pin loop) — the same task's files.  This file is the
dispatch, the fold, and the one arm whose content belongs to **task #57**.

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

## `sorry` count in this file: 10.

All ten are the dispatch and fold lemmas whose arms are the sibling files'
(`Refine/Checker.lean`, `Refine/CheckerPins.lean`, and
`Refine/CheckerBase.lean`'s `checkConstantVal`); each carries a one-line note.
The `.indDecl` arms — the seam this task had to get right — are proved.
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

/-! ## The `.indDecl` arm, both spellings

The seam with task #57.  The cached one is proved from `IndRoutesSpec`; the
`Expr`-level one is vacuous because task #24 left the routes unported there. -/

/-- **`cached::parsed_c::check_ind_decl_c` refines `checkDeclC`'s `.indDecl`
arm** (`ConLeche/Cached/ParsedC.lean:238-241`): the stream's *declared*
parameter count first and for both routes (con-leche task #228), then the
one-route dispatch by the recogniser alone (task #210/#219).  Proved, with
task #57's `IndRoutesSpec` as a named hypothesis: `Refine/Env.lean`'s
`ind_params_ok_refines` gives the gate, and `IndRoutesSpec`'s two clauses give
the recogniser's verdict *and* the chosen route together. -/
theorem check_ind_decl_c_refines {mode : env.CheckMode} (hind : IndRoutesSpec mode)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {block : alloc.vec.Vec env.ConstantInfo} {n_p : Std.U64}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hb : ConstantInfosWF block)
    (h : cached.parsed_c.check_ind_decl_c mode st fe block n_p = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkDeclC (absMode mode) lfe
            (.indDecl (absConstantInfos block) n_p.val)).run lst = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' := by
  intro lst lfe hsr hfr
  rw [cached.parsed_c.check_ind_decl_c] at h
  obtain ⟨b, hb', h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = ConLeche.indParamsOk n_p.val (absConstantInfos block) :=
    Env.ind_params_ok_refines hb hb'
  cases b with
  | false =>
    -- the parameter gate declined: the Rust throws, so there is nothing to show
    simp at h
  | true =>
    simp only [if_pos] at h
    obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
    cases o with
    | none =>
      obtain ⟨lst', lfe', hnp, hrun, hrest⟩ :=
        hind.modeled st fe n_p block fe' st' hsw hfw hb ho h lst lfe hsr hfr
      refine ⟨lst', lfe', ?_, hrest⟩
      rw [ConLeche.Cached.checkDeclC]
      simp only [← hbv, if_pos, hnp]
      exact hrun
    | some p =>
      obtain ⟨lst', lfe', lp, hnp, hrun, hrest⟩ :=
        hind.native st fe n_p block p fe' st' hsw hfw hb ho h lst lfe hsr hfr
      refine ⟨lst', lfe', ?_, hrest⟩
      rw [ConLeche.Cached.checkDeclC]
      simp only [← hbv, if_pos, hnp]
      exact hrun

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

/-! ## The dispatch and the fold

Eight statements.  Each arm's content is a sibling file's
(`Refine/Checker.lean`, `Refine/CheckerPins.lean`,
`Refine/CheckerBase.lean`); stated here so the dispatch is fixed and the
composition is a `cases` on the declaration. -/

/-- **`kernel::checker::check_decl` refines `checkDecl`**
(`ConLeche/Kernel/Checker.lean:419-562`), at the cached operation record.  The
environment in and out is the index (task #18 deviation 3); the Lean's
pre-insertion `Env` is the index's own `env` (module note), and the Lean's
output `Env` is the `env` of an index the port's result stands in `FEnvRel` to.

`sorry`: needs the six arm lemmas — `Refine/CheckerBase.lean`'s
`check_constant_val_refines`, `Refine/Checker.lean`'s
`check_defn_val`/`check_thm_val`/`check_opaque_val`/`install_basis_decl`,
`Refine/CheckerPins.lean`'s `check_div_mod_pin`/`check_reduce_pin` and the
structural-`Nat` gate, and `check_ind_decl_declines` above. -/
theorem check_decl_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {d : env.Declaration}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hd : DeclarationWF d)
    (h : kernel.checker.check_decl mode pins st fe d = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
            (absDeclaration d)).run lst = .ok (lfe'.env, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' := by
  sorry

/-- **`cached::parsed_c::check_decl_c` refines `checkDeclC`**
(`ConLeche/Cached/ParsedC.lean:158-241`): the same six arms over the parsed
representation, with `checkConstantValC`'s recorded judgement type threaded and
the pinned-name test *before* the push (the cited arm's own RC-linearity
shape).

`sorry`: needs the five value-arm lemmas of `cached/parsed_c.rs`
(`check_defn_decl_c`, `check_thm_decl_c`, `check_opaque_decl_c`,
`check_axiom_decl_c`, `check_basis_decl_c`), which are the parsed tier's twins
of `Refine/Checker.lean`'s; the `.indDecl` arm is
`check_ind_decl_c_refines` above. -/
theorem check_decl_c_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hind : IndRoutesSpec mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {pd : parsed_c.DeclC}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hd : DeclCWF pd)
    (h : cached.parsed_c.check_decl_c mode pins st fe pd = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkDeclC (absMode mode) lfe (absDeclC pd)).run lst
            = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' := by
  sorry

/-- **`cached::parsed_c::check_decl_step_c` refines `checkDeclStepC`**
(`ConLeche/Cached/ParsedC.lean:259-262`): `flushC`, then `checkDeclC`.  The
flush is what makes one `CState` safe for a whole stream — every
environment-dependent memo is emptied and the self-certified `ienv` and the
three level-operation memos survive (`Refine/State.lean`'s `flushed`).

`sorry`: `Refine/StateC.lean`'s `flush_c_refines` composed with
`check_decl_c_refines` above. -/
theorem check_decl_step_c_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    (hind : IndRoutesSpec mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {pd : parsed_c.DeclC}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hd : DeclCWF pd)
    (h : cached.parsed_c.check_decl_step_c mode pins st fe pd = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkDeclStepC (absMode mode) lfe (absDeclC pd)).run lst
            = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' := by
  sorry

/-! ### The six arms of `checkDecl`, stated

One statement per arm function of `kernel/checker.rs`, so that
`check_decl_refines` is a `cases` and every arm is owned by exactly one
lemma. -/

/-- `checkDecl`'s `.defnDecl` arm (`Checker.lean:421-500`): the common constant
check, the value check, then the two pinned-`Nat` gates at the pre-insertion
bound `k_pre = fe.visibleBelow`.

`sorry`: `Refine/CheckerBase.lean` + `Refine/Checker.lean` +
`Refine/CheckerPins.lean`. -/
theorem check_defn_decl_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr} {hint : env.ReducibilityHint}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_defn_decl mode pins st fe cv value hint = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
            (ConLeche.Declaration.defnDecl (absConstantVal cv) (absExpr value) (absHint hint))).run lst
          = .ok (lfe'.env, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' := by
  sorry

/-- `checkDecl`'s `.thmDecl` arm (`Checker.lean:501-503`).

`sorry`: `Refine/CheckerBase.lean`'s `check_constant_val_refines` and
`Refine/Checker.lean`'s `check_thm_val_refines`. -/
theorem check_thm_decl_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_thm_decl mode st fe cv value = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
            (ConLeche.Declaration.thmDecl (absConstantVal cv) (absExpr value))).run lst = .ok (lfe'.env, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' := by
  sorry

/-- `checkDecl`'s `.opaqueDecl` arm (`Checker.lean:504-530`): the opaque check,
then the compiler-trust gate for `Lean.reduceNat`/`Lean.reduceBool`.

`sorry`: `Refine/Checker.lean`'s `check_opaque_val_refines` and
`Refine/CheckerPins.lean`'s `check_reduce_pin_refines`. -/
theorem check_opaque_decl_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {cv : env.ConstantVal} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv) (hv : ExprWF value)
    (h : kernel.checker.check_opaque_decl mode st fe cv value = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
            (ConLeche.Declaration.opaqueDecl (absConstantVal cv) (absExpr value))).run lst = .ok (lfe'.env, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' := by
  sorry

/-- `checkDecl`'s `.axiomDecl` arm (`Checker.lean:531-552`): the two standard
axioms and the `Init` compiler-trust family are *installed* with their shapes
pinned; the tolerated whitelist (exactly `sorryAx`) is checked and **not**
stored; every other axiom, and a pinned name with a non-pinned shape, is a
positive decline.

`sorry`: `Refine/StdAxioms.lean`'s `std_axiom_ok_refines` /
`tolerated_axiom_names_refines`, `Refine/TrustAxioms.lean`'s
`trust_compiler_ok_refines` / `of_reduce_ax_ok_refines`, and
`Refine/FEnv.lean`'s `push_refines`. -/
theorem check_axiom_decl_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv} {cv : env.ConstantVal}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv)
    (h : kernel.checker.check_axiom_decl mode st fe cv = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
            (ConLeche.Declaration.axiomDecl (absConstantVal cv))).run lst = .ok (lfe'.env, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' := by
  sorry

/-- `checkDecl`'s `.basisDecl` arm (`Checker.lean:553-557`): the quotient block
requires the pinned `Eq` basis, then `kind.declsA.foldlM installBasisDecl`.
The block is `basis_tables::basis_decls_a`, and task #22's
`Refine/BasisTables.lean` is what says it *is* `BasisKind.declsA`.

`sorry`: `Refine/BasisPins.lean`'s `eq_basis_pinned_refines` and
`Refine/Checker.lean`'s `install_basis_decls_refines`. -/
theorem check_basis_decl_refines {mode : env.CheckMode}
    {fe fe' : fenv.FEnv} {kind : env.BasisKind}
    (hfw : FEnvWF fe)
    (h : kernel.checker.check_basis_decl fe kind = ok (.Ok fe')) :
    ∀ lst lfe, FEnvRel fe lfe →
      ∃ lfe',
        (ConLeche.checkDecl (absMode mode) (TypeChecker.lops mode lfe) lfe.env
            (ConLeche.Declaration.basisDecl (absBasisKind kind))).run lst = .ok (lfe'.env, lst)
        ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' := by
  sorry

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

/-- **`kernel::checker::check_decls_pure_from` refines the cited fold's tail**:
the declarations from position `i` take the index where the port says.

`sorry`: the index induction over `check_decl_refines`. -/
theorem check_decls_pure_from_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {ds : alloc.vec.Vec env.Declaration} {i : Std.Usize}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : kernel.checker.check_decls_pure_from mode pins st fe ds i = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        FoldsTo mode lst lfe ((ds.val.drop i.val).map absDeclaration) lst' lfe'
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' := by
  sorry

/-- **`kernel::checker::check_decls_pure` refines `checkDeclsPure`**
(`Checker.lean:564-567`): the whole stream from the empty environment, at the
per-step record (section note).

`sorry`: `check_decls_pure_from_refines` at `i = 0` plus `Refine/FEnv.lean`'s
`mk_fenv_refines` at `env::empty`. -/
theorem check_decls_pure_refines {mode : env.CheckMode} {fuel : Std.U64}
    (hfuel : core_k.check_fuel = ok fuel) (hk : Core.Wrappers mode fuel)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    {st st' : cached.state_c.CState} {fe' : fenv.FEnv}
    {ds : alloc.vec.Vec env.Declaration}
    (hsw : StateWF st) (hds : ∀ d ∈ ds.val, DeclarationWF d)
    (h : kernel.checker.check_decls_pure mode pins st ds = ok (.Ok fe', st')) :
    ∀ lst, StateRel st lst →
      ∃ lst' lfe',
        FoldsTo mode lst (ConLeche.mkFEnv ConLeche.Env.empty)
            (ds.val.map absDeclaration) lst' lfe'
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe' := by
  sorry

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

The one lemma of this file that is *proved* and that composes the two
concurrent tasks: nothing beyond the three standard axioms may enter through
the seam. -/

/-- info: 'ConRon.Refine.CheckerDecl.check_ind_decl_c_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms check_ind_decl_c_refines

end ConRon.Refine.CheckerDecl

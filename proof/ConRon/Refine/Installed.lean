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

## The three hypotheses this tier still owes

Every statement below that reaches the core carries them, and
`check_decls_refines` is where they are named once:

1. `hk : Core.KnotSpec mode IndAbs.checkFuelU` — **task #55**, the core's own
   refinement, being proved concurrently.  `IndAbs.check_fuel_eq` is what turns
   it into the `(hfuel, hk)` pair the task-#56 lemmas take.
2. `hind : IndRoutesSpec mode` — **task #59**'s bridge
   `ind_routes_spec_of_p ∘ ind_routes_spec hk` had not landed when this task
   was written, so the *consumer's* form is taken as a named hypothesis here;
   when the bridge lands this hypothesis is discharged from `hk` and
   disappears, in one line.
3. `hpins : absPins pins = ConLeche.natOpPinSets` — the pinned con-leche
   (`3e004805`) bakes the global `natOpPinSets` into `checkDeclStepC`, where
   the port threads the list as a parameter (DESIGN.md §3.6, task #31).
   `Refine/CheckerPins.lean`'s `check_div_mod_pin_refines` is the lemma that
   actually consumes it; it is carried from here down so that no statement in
   between can quietly assume the two lists agree.  (Task #56's
   `check_decl_step_c_refines` does not yet take it — its pin-route arms are
   `sorry` — so the hypothesis is inert in today's proofs and live in today's
   statements, which is the honest way round.)  It is *dischargeable* for the
   binary's own run: `Refine/Pins.lean`'s `check_decls_pins_refines`, modulo
   that file's two open statements.

## `leanCheckDecls`: the one line the pins parameter costs

The upstream ask of §3.6 is `checkDecls mode pins ds`, with the shipped
`checkDecls mode ds := checkDecls mode natOpPinSets ds`; the `pins-param`
branch (con-leche task #285, `_tmp/con-leche-pins`) has it.  So the conclusion
of `check_decls_refines` is stated against `leanCheckDecls`, which takes the
pin list and ignores it today.  When the submodule pin moves,
`leanCheckDecls`'s body becomes `ConLeche.Cached.checkDecls mode pins ds`,
`hpins` disappears from every statement, and nothing else in this file or in
`Refine/Main.lean` changes.

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

/-- **`installed::annot_constant_val_c_after_annot` refines `annotConstantValC`'s
tail** (`Installed.lean:81-100`, past the annotation): the two post-annotation
guards and the header the cited `pure` builds — both components of the pair are
the annotated type.

Proved (task #62) from `Refine/ExprOpsCGuards.lean`'s
`all_level_params_defined_refines` and `Refine/StateCResolve.lean`'s
`consts_resolve_fc_refines` (at `litGuards` above), then the two-level `if` and
the three `dup` identities. -/
theorem annot_constant_val_c_after_annot_refines {fe : fenv.FEnv}
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
      ∧ ConstantValWF cv_a ∧ ExprWF jty' := by
  intro lfe hfr
  rw [cached.installed.annot_constant_val_c_after_annot] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = ConLeche.Cached.ExprC.allLevelParamsDefined
      (absNames cv.level_params) (absExpr jty) :=
    ExprOpsC.all_level_params_defined_refines hcv.2.1 hjty hb
  cases b with
  | false => exact absurd h (by simp [bind_eq_ok_iff])
  | true =>
    simp only [reduceIte] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v : b1 = ConLeche.Cached.constsResolveFC lfe (absExpr jty) :=
      StateC.consts_resolve_fc_refines litGuards hfr hfw hjty hb1
    cases b1 with
    | false => exact absurd h (by simp [bind_eq_ok_iff])
    | true =>
      simp only [reduceIte] at h
      obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      have heq : (⟨n, v, e⟩ : env.ConstantVal) = cv_a ∧ jty = jty' := by simpa using h
      obtain ⟨rfl, rfl⟩ := heq
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
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ConstantValWF cv_a ∧ ExprWF jty := by
  intro lst lfe hsr hfr
  rw [cached.installed.annot_constant_val_c] at h
  obtain ⟨o, hfind, h⟩ := bind_eq_ok_iff.mp h
  have hfindv : o.map absConstantInfo = lfe.find? (absName cv.name) :=
    FEnv.find_refines hfr hfw hcv.1 hfind
  cases o with
  | some ci => exact absurd h (by simp [core.option.Option.is_some, bind_eq_ok_iff])
  | none =>
    have h1 : (lfe.find? (absName cv.name)).isSome = false := by
      rw [← hfindv]; rfl
    simp only [core.option.Option.is_some] at h
    obtain ⟨rbn, hrbn, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨hrbne, hrbnw⟩ := BasisNames.reserved_basis_names_refines hrbn
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v : b1 = ConLeche.reservedBasisNames.contains (absName cv.name) := by
      rw [Name.contains_refines hrbnw hcv.1 hb1, hrbne]
    cases b1 with
    | true => exact absurd h (by simp [bind_eq_ok_iff])
    | false =>
      simp only [Bool.false_eq_true, reduceIte] at h
      obtain ⟨b2, hb2, h⟩ := bind_eq_ok_iff.mp h
      have hb2v := CoreK.name_is_proj_fn_shape_refines hcv.1 hb2
      cases b2 with
      | true => exact absurd h (by simp [bind_eq_ok_iff])
      | false =>
        simp only [Bool.false_eq_true, reduceIte] at h
        obtain ⟨b3, hb3, h⟩ := bind_eq_ok_iff.mp h
        have hb3v := CheckerBase.name_nodup_refines hcv.2.1 hb3
        cases b3 with
        | false => exact absurd h (by simp [bind_eq_ok_iff])
        | true =>
          simp only [reduceIte] at h
          obtain ⟨b4, hb4, h⟩ := bind_eq_ok_iff.mp h
          have hb4v := ExprOpsC.loose_bvars_bounded_refines hcv.2.2 hb4
          cases b4 with
          | false => exact absurd h (by simp [bind_eq_ok_iff])
          | true =>
            simp only [reduceIte] at h
            obtain ⟨b5, hb5, h⟩ := bind_eq_ok_iff.mp h
            have hb5v := ExprOpsC.has_fvar_refines hcv.2.2 hb5
            cases b5 with
            | true => exact absurd h (by simp [bind_eq_ok_iff])
            | false =>
              simp only [Bool.false_eq_true, reduceIte] at h
              obtain ⟨q, hann, h⟩ := bind_eq_ok_iff.mp h
              obtain ⟨r, st1⟩ := q
              cases r with
              | Err e => exact absurd h (by simp)
              | Ok jty0 =>
                obtain ⟨r1, htl, h⟩ := bind_eq_ok_iff.mp h
                have hq : r1 = .Ok (cv_a, jty) ∧ st1 = st' := by simpa using h
                obtain ⟨rfl, rfl⟩ := hq
                obtain ⟨lst1, hrunA, hsr1, hsw1, hjtyw⟩ :=
                  TypeChecker.annotate_core_refines hfuel hk st fe 0#u64 cv.ty jty0 _
                    hsw hfw hcv.2.2 hann lst lfe hsr hfr
                obtain ⟨htail, hcvw, hjtyw'⟩ :=
                  annot_constant_val_c_after_annot_refines hfw hcv hjtyw htl lfe hfr
                simp only [ConLeche.Cached.opE] at hrunA
                have hrunA' : StateT.run
                    ((ConLeche.Cached.coreKnotI (absMode mode) lfe ConLeche.checkFuel).annotate 0
                      (absExpr cv.ty)) lst = .ok (absExpr jty0, lst1) := hrunA
                have hb4v' : ConLeche.Cached.ExprC.looseBVarsBounded 0 (absExpr cv.ty) = true :=
                  hb4v.symm
                refine ⟨lst1, ?_, hsr1, hsw1, hcvw, hjtyw'⟩
                rw [ConLeche.Cached.annotConstantValC]
                simp only [absConstantVal, h1, ← hb1v, ← hb2v, ← hb3v, hb4v', ← hb5v,
                  Bool.false_eq_true, reduceIte, if_true]
                refine run_bind_ok hrunA' ?_
                simp only [absConstantVal] at htail
                by_cases hG : ConLeche.Cached.ExprC.allLevelParamsDefined
                    (absNames cv.level_params) (absExpr jty0) = true
                · by_cases hH : ConLeche.Cached.constsResolveFC lfe (absExpr jty0) = true
                  · simp only [hG, hH, if_true] at htail ⊢
                    exact congrArg (fun (r : Except ConLeche.CheckError
                      (ConLeche.ConstantVal × ConLeche.Expr)) => r.map (fun p => (p, lst1))) htail
                  · simp [hG, hH, Functor.map, Except.map, throw, throwThe,
                      MonadExceptOf.throw] at htail
                · simp [hG, throw, throwThe, MonadExceptOf.throw, Bind.bind,
                    Except.bind] at htail

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

/-- **`installed::annot_val_c_after_annot` refines `annotValC`'s tail**
(`Installed.lean:106-118`, past the annotation): the two guards on the
annotated value and the `ienv` record, tagged with the very `Expr` objects the
install pushes.  The record runs on the accepting path only.

Proved (task #62): the two guards as in
`annot_constant_val_c_after_annot_refines`, then `Refine/StateC.lean`'s
`record_c_const_refines` over `annot_val_c_record_refines` above. -/
theorem annot_val_c_after_annot_refines {st st' : cached.state_c.CState}
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
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF jv' := by
  intro lst lfe hsr hfr
  rw [cached.installed.annot_val_c_after_annot] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv : b = ConLeche.Cached.ExprC.allLevelParamsDefined
      (absNames cv_a.level_params) (absExpr jv) :=
    ExprOpsC.all_level_params_defined_refines hcv.2.1 hjv hb
  cases b with
  | false => exact absurd h (by simp [bind_eq_ok_iff])
  | true =>
    simp only [reduceIte] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v : b1 = ConLeche.Cached.constsResolveFC lfe (absExpr jv) :=
      StateC.consts_resolve_fc_refines litGuards hfr hfw hjv hb1
    cases b1 with
    | false => exact absurd h (by simp [bind_eq_ok_iff])
    | true =>
      simp only [reduceIte] at h
      obtain ⟨n, hn, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨o, ho, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨st1, hrec, h⟩ := bind_eq_ok_iff.mp h
      have hq : jv = jv' ∧ st1 = st' := by simpa using h
      obtain ⟨rfl, rfl⟩ := hq
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
    {cv_a : env.ConstantVal} {jty value jv : expr.Expr} {record : Bool}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv_a)
    (hjty : ExprWF jty) (hv : ExprWF value)
    (h : cached.installed.annot_val_c mode st fe cv_a jty value record
          = ok (.Ok jv, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (ConLeche.Cached.annotValC (absMode mode) lfe (absConstantVal cv_a)
            (absExpr jty) (absExpr value) record).run lst = .ok (absExpr jv, lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ ExprWF jv := by
  intro lst lfe hsr hfr
  rw [cached.installed.annot_val_c] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv := ExprOpsC.loose_bvars_bounded_refines hv hb
  cases b with
  | false => exact absurd h (by simp [bind_eq_ok_iff])
  | true =>
    simp only [reduceIte] at h
    obtain ⟨b1, hb1, h⟩ := bind_eq_ok_iff.mp h
    have hb1v := ExprOpsC.has_fvar_refines hv hb1
    cases b1 with
    | true => exact absurd h (by simp [bind_eq_ok_iff])
    | false =>
      simp only [Bool.false_eq_true, reduceIte] at h
      obtain ⟨q, hann, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := q
      cases r with
      | Err e => exact absurd h (by simp)
      | Ok jv0 =>
        obtain ⟨lst1, hrunA, hsr1, hsw1, hjvw⟩ :=
          TypeChecker.annotate_core_refines hfuel hk st fe 0#u64 value jv0 st1
            hsw hfw hv hann lst lfe hsr hfr
        simp only [ConLeche.Cached.opE] at hrunA
        have hrunA' : StateT.run ((ConLeche.Cached.coreKnotI (absMode mode) lfe
            ConLeche.checkFuel).annotate 0 (absExpr value)) lst
            = .ok (absExpr jv0, lst1) := hrunA
        have hbv' : ConLeche.Cached.ExprC.looseBVarsBounded 0 (absExpr value) = true :=
          hbv.symm
        obtain ⟨lst', hrunT, hsr', hsw', hjvw'⟩ :=
          annot_val_c_after_annot_refines hsw1 hfw hcv hjty hjvw h lst1 lfe hsr1 hfr
        refine ⟨lst', ?_, hsr', hsw', hjvw'⟩
        rw [ConLeche.Cached.annotValC]
        simp only [hbv', ← hb1v, Bool.false_eq_true, reduceIte, if_true]
        exact run_bind_ok hrunA' hrunT

/-- **`installed::annot_value_c_tail` refines `annotValueC`'s tail**
(`Installed.lean:124-129`): the value's install half and the triple.  Stated at
the post-header header and type, which is what lets it compose with
`annot_constant_val_c_refines`.

Proved (task #62) from `annot_val_c_refines` above and the triple. -/
theorem annot_value_c_tail_refines {mode : env.CheckMode} {fuel : Std.U64}
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
        ∧ ExprWF jv := by
  intro lst lfe hsr hfr
  rw [cached.installed.annot_value_c_tail] at h
  obtain ⟨q, hval, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  cases r with
  | Err e => exact absurd h (by simp)
  | Ok jv0 =>
    have hq : cv_a = cv_a' ∧ jty = jty' ∧ jv0 = jv ∧ st1 = st' := by simpa using h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hq
    obtain ⟨lst', hrunV, hsr', hsw', hjvw⟩ :=
      annot_val_c_refines hfuel hk hsw hfw hcv hjty hv hval lst lfe hsr hfr
    exact ⟨lst', run_bind_ok hrunV rfl, hsr', hsw', hcv, hjty, hjvw⟩

/-- **`installed::annot_value_c` refines `annotValueC`**
(`Installed.lean:124-129`): phase A's install of a separable value declaration
— the per-declaration flush, the header's install half, the value's install
half, and the triple.

Proved (task #62) from `Refine/StateC.lean`'s `flush_c_refines`, then
`annot_constant_val_c_refines` and `annot_value_c_tail_refines` above. -/
theorem annot_value_c_refines {mode : env.CheckMode} {fuel : Std.U64}
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
        ∧ ExprWF jv := by
  intro lst lfe hsr hfr
  rw [cached.installed.annot_value_c] at h
  obtain ⟨st1, hflush, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hrunf, hrel1, hwf1, -⟩ := StateC.flush_c_refines hsr hsw hflush
  obtain ⟨q, hacv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st2⟩ := q
  cases r with
  | Err e => exact absurd h (by simp)
  | Ok r1 =>
    obtain ⟨cv1, e1⟩ := r1
    obtain ⟨lst1, hrun1, hsr1, hsw1, hcv1, hjty1⟩ :=
      annot_constant_val_c_refines hfuel hk hwf1 hfw hcv hacv lst.flushed lfe hrel1 hfr
    obtain ⟨lst2, hrun2, hsr2, hsw2, hcvw, hjtyw, hjvw⟩ :=
      annot_value_c_tail_refines hfuel hk hsw1 hfw hcv1 hjty1 hv h lst1 lfe hsr1 hfr
    refine ⟨lst2, ?_, hsr2, hsw2, hcvw, hjtyw, hjvw⟩
    rw [ConLeche.Cached.annotValueC]
    exact run_bind_ok hrunf (run_bind_ok hrun1 hrun2)

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

`hpins` is inert here: task #56's `check_decl_step_c_refines` does not yet take
it (its pin-route arms are `sorry`).  It is carried so that the statement does
not silently assume the port's pin list is con-leche's global — which is why
the unused-variable linter is turned off for this one declaration rather than
the hypothesis being dropped. -/
theorem annot_step_other_c_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {pend pend' : alloc.vec.Vec parsed_c.PendingCheck} {pd : parsed_c.DeclC}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hd : DeclCWF pd)
    (h : cached.installed.annot_step_other_c mode pins st fe pend pd
          = ok (.Ok (fe', pend'), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.checkDeclStepC (absMode mode) lfe (absDeclC pd)).run lst
            = .ok (lfe', lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ pend' = pend := by
  intro lst lfe hsr hfr
  rw [cached.installed.annot_step_other_c] at h
  obtain ⟨q, hstep, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  cases r with
  | Err e => simp at h
  | Ok fe2 =>
    have he : fe2 = fe' ∧ pend = pend' ∧ st1 = st' := by simpa using h
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨lst', lfe', hrun, rest⟩ :=
      CheckerDecl.check_decl_step_c_refines IndAbs.check_fuel_eq hk.1 hind hsw hfw hd
        hstep lst lfe hsr hfr
    exact ⟨lst', lfe', hrun, rest.1, rest.2.1, rest.2.2.1, rest.2.2.2, rfl⟩

/-- **`installed::annot_step_defn_c_push` refines the cited push**
(`Installed.lean:136-169`, the `.defnDecl` arm's tail): the constant is pushed
as a `.defnInfo` and the record appended, with the installation counter read
**before** the push (the RC-linearity comment the cited code carries). -/
theorem annot_step_defn_c_push_refines {i : Std.U64} {fe fe' : fenv.FEnv}
    {pend pend' : alloc.vec.Vec parsed_c.PendingCheck} {cv_a : env.ConstantVal}
    {jv : expr.Expr} {hint : env.ReducibilityHint}
    (hfw : FEnvWF fe) (hcv : ConstantValWF cv_a) (hjv : ExprWF jv)
    (hpe : PendingChecksWF pend)
    (h : cached.installed.annot_step_defn_c_push i fe pend cv_a jv hint
          = ok (fe', pend')) :
    ∀ lfe, FEnvRel fe lfe →
      FEnvRel fe' (lfe.push (.defnInfo (absConstantVal cv_a) (absExpr jv)
          (absHint hint)))
      ∧ FEnvWF fe'
      ∧ absPendingChecks pend' = absPendingChecks pend ++
          [⟨⟨.defn, absConstantVal cv_a, absExpr jv⟩, i.val, lfe.visibleBelow⟩]
      ∧ PendingChecksWF pend' := by
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
  have hfe : fe2 = fe' ∧ pend1 = pend' := by simpa using h
  obtain ⟨rfl, rfl⟩ := hfe
  refine ⟨by simpa [absConstantInfo] using hrel', hwf', ?_,
    PendingChecksWF_push hpe ⟨hcv, hjv⟩ hppush⟩
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
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState} {i : Std.U64} {fe fe' : fenv.FEnv}
    {pend pend' : alloc.vec.Vec parsed_c.PendingCheck} {pd : parsed_c.DeclC}
    {cv : env.ConstantVal} {value : expr.Expr} {hint : env.ReducibilityHint}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv)
    (hv : ExprWF value) (hpe : PendingChecksWF pend)
    (hpd : pd = .DefnDecl cv value hint)
    (h : cached.installed.annot_step_defn_c mode pins st i fe pend pd cv value hint
          = ok (.Ok (fe', pend'), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.annotStepC (absMode mode) i.val lfe
            (absPendingChecks pend).toArray (absDeclC pd)).run lst
          = .ok ((lfe', (absPendingChecks pend').toArray), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ PendingChecksWF pend' := by
  intro lst lfe hsr hfr
  subst hpd
  rw [cached.installed.annot_step_defn_c] at h
  obtain ⟨v, hv1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hv1e, hv1w⟩ := CoreK.nat_op_names_refines hv1
  have hbv : b = ConLeche.natOpNames.contains (absConstantVal cv).name := by
    rw [Name.contains_refines hv1w hcv.1 hb, hv1e]; rfl
  have hstep : ∀ (fe2 : fenv.FEnv) (pend2 : alloc.vec.Vec parsed_c.PendingCheck)
      (st2 : cached.state_c.CState),
      cached.installed.annot_step_other_c mode pins st fe pend
          (parsed_c.DeclC.DefnDecl cv value hint) = ok (.Ok (fe2, pend2), st2) →
      ∃ lst' lfe',
        (ConLeche.Cached.checkDeclStepC (absMode mode) lfe
            (ConLeche.Cached.DeclC.defnDecl (absConstantVal cv) (absExpr value)
              (absHint hint))).run lst = .ok (lfe', lst')
        ∧ StateRel st2 lst' ∧ StateWF st2 ∧ FEnvRel fe2 lfe' ∧ FEnvWF fe2
        ∧ pend2 = pend := by
    intro fe2 pend2 st2 ho
    have hdwf : DeclCWF (parsed_c.DeclC.DefnDecl cv value hint) := ⟨hcv, hv⟩
    exact annot_step_other_c_refines hk hind hpins hsw hfw hdwf ho lst lfe hsr hfr
  by_cases hbt : b = true
  · subst hbt
    simp only [if_pos] at h
    obtain ⟨lst', lfe', hrun, hsr', hsw', hfr', hfw', rfl⟩ := hstep fe' pend' st' h
    refine ⟨lst', lfe', ?_, hsr', hsw', hfr', hfw', hpe⟩
    rw [absDeclC, ConLeche.Cached.annotStepC]
    rw [if_pos (by rw [← hbv]; simp)]
    simp only [StateT.run_bind, hrun]
    rfl
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
      obtain ⟨lst', lfe', hrun, hsr', hsw', hfr', hfw', rfl⟩ := hstep fe' pend' st' h
      refine ⟨lst', lfe', ?_, hsr', hsw', hfr', hfw', hpe⟩
      rw [absDeclC, ConLeche.Cached.annotStepC]
      rw [if_pos (by rw [← hbv, ← hb1v]; simp)]
      simp only [StateT.run_bind, hrun]
      rfl
    · have hb1f : b1 = false := by cases b1 with | false => rfl | true => exact absurd rfl hb1t
      subst hb1f
      simp only [Bool.false_eq_true, reduceIte] at h
      obtain ⟨q, hval, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨r, st1⟩ := q
      cases r with
      | Err e => simp at h
      | Ok r1 =>
        obtain ⟨cv1, jty1, jv1⟩ := r1
        obtain ⟨p, hpush, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨fe2, pend2⟩ := p
        have hpe2 : fe2 = fe' ∧ pend2 = pend' ∧ st1 = st' := by simpa using h
        obtain ⟨rfl, rfl, rfl⟩ := hpe2
        obtain ⟨lst', hrun, hsr', hsw', hcv1, hjty1, hjv1⟩ :=
          annot_value_c_refines IndAbs.check_fuel_eq hk.1 hsw hfw hcv hv hval lst lfe hsr hfr
        obtain ⟨hfr', hfw', hpabs, hpw⟩ :=
          annot_step_defn_c_push_refines hfw hcv1 hjv1 hpe hpush lfe hfr
        refine ⟨lst', _, ?_, hsr', hsw', hfr', hfw', hpw⟩
        rw [absDeclC, ConLeche.Cached.annotStepC]
        rw [if_neg (by rw [← hbv, ← hb1v]; simp)]
        simp only [StateT.run_bind, hrun]
        rw [hpabs]
        simp

/-- **`installed::annot_step_thm_c_push` refines the cited record and push**
(`Installed.lean:136-169`, the `.thmDecl` arm's tail): the `ienv` record with
**no value** (`recordCConst … none`), then the constant pushed with the
record's own raw value and the pending record appended. -/
theorem annot_step_thm_c_push_refines {st st' : cached.state_c.CState}
    {i : Std.U64} {fe fe' : fenv.FEnv}
    {pend pend' : alloc.vec.Vec parsed_c.PendingCheck} {cv_a : env.ConstantVal}
    {jty value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv_a)
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
        ∧ PendingChecksWF pend' := by
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
  have hfe : fe2 = fe' ∧ pend1 = pend' ∧ st1 = st' := by simpa using h
  obtain ⟨rfl, rfl, rfl⟩ := hfe
  refine ⟨lst', by simpa [absConstantVal] using hrun, hsr', hsw',
    by simpa [absConstantInfo] using hrel', hwf', ?_,
    PendingChecksWF_push hpe ⟨hcv, hv⟩ hppush⟩
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
    {st st' : cached.state_c.CState} {i : Std.U64} {fe fe' : fenv.FEnv}
    {pend pend' : alloc.vec.Vec parsed_c.PendingCheck}
    {cv : env.ConstantVal} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv)
    (hv : ExprWF value) (hpe : PendingChecksWF pend)
    (h : cached.installed.annot_step_thm_c mode st i fe pend cv value
          = ok (.Ok (fe', pend'), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.annotStepC (absMode mode) i.val lfe
            (absPendingChecks pend).toArray
            (.thmDecl (absConstantVal cv) (absExpr value))).run lst
          = .ok ((lfe', (absPendingChecks pend').toArray), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ PendingChecksWF pend' := by
  intro lst lfe hsr hfr
  rw [cached.installed.annot_step_thm_c] at h
  obtain ⟨st1, hflush, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hrunf, hrel1, hwf1, -⟩ := StateC.flush_c_refines hsr hsw hflush
  obtain ⟨q, hacv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st2⟩ := q
  cases r with
  | Err e => simp at h
  | Ok r1 =>
    obtain ⟨cv1, jty1⟩ := r1
    obtain ⟨lst1, hrun1, hsr1, hsw1, hcv1, hjty1⟩ :=
      annot_constant_val_c_refines IndAbs.check_fuel_eq hk.1 hwf1 hfw hcv hacv
        lst.flushed lfe hrel1 hfr
    obtain ⟨p, hpush, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨pr, st3⟩ := p
    obtain ⟨fe2, pend2⟩ := pr
    have hfe : fe2 = fe' ∧ pend2 = pend' ∧ st3 = st' := by simpa using h
    obtain ⟨rfl, rfl, rfl⟩ := hfe
    obtain ⟨lst2, hrunr, hsr2, hsw2, hfr2, hfw2, hpabs, hpw⟩ :=
      annot_step_thm_c_push_refines hsw1 hfw hcv1 hjty1 hv hpe hpush lst1 lfe hsr1 hfr
    refine ⟨lst2, _, ?_, hsr2, hsw2, hfr2, hfw2, hpw⟩
    rw [ConLeche.Cached.annotStepC]
    refine run_bind_ok hrunf (run_bind_ok hrun1 (run_bind_ok hrunr ?_))
    rw [hpabs, ← List.push_toArray]
    rfl

/-- **`installed::annot_step_opaque_c_push` refines the cited push**
(`Installed.lean:136-169`, the `.opaqueDecl` arm's tail): the constant is
installed **as an axiom** — an opaque's value is a discarded witness. -/
theorem annot_step_opaque_c_push_refines {i : Std.U64} {fe fe' : fenv.FEnv}
    {pend pend' : alloc.vec.Vec parsed_c.PendingCheck} {cv_a : env.ConstantVal}
    {jv : expr.Expr}
    (hfw : FEnvWF fe) (hcv : ConstantValWF cv_a) (hjv : ExprWF jv)
    (hpe : PendingChecksWF pend)
    (h : cached.installed.annot_step_opaque_c_push i fe pend cv_a jv
          = ok (fe', pend')) :
    ∀ lfe, FEnvRel fe lfe →
      FEnvRel fe' (lfe.push (.axiomInfo (absConstantVal cv_a)))
      ∧ FEnvWF fe'
      ∧ absPendingChecks pend' = absPendingChecks pend ++
          [⟨⟨.opaque, absConstantVal cv_a, absExpr jv⟩, i.val, lfe.visibleBelow⟩]
      ∧ PendingChecksWF pend' := by
  intro lfe hfr
  rw [cached.installed.annot_step_opaque_c_push] at h
  obtain ⟨cv, hcvd, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨fe2, hpush, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨pend1, hppush, h⟩ := bind_eq_ok_iff.mp h
  rw [Env.constant_val_dup_refines hcvd] at hpush
  have hci : ConstantInfoWF (env.ConstantInfo.AxiomInfo cv_a) := hcv
  obtain ⟨hrel', hwf'⟩ := FEnv.push_refines hfr hfw hci hpush
  have hfe : fe2 = fe' ∧ pend1 = pend' := by simpa using h
  obtain ⟨rfl, rfl⟩ := hfe
  refine ⟨by simpa [absConstantInfo] using hrel', hwf', ?_,
    PendingChecksWF_push hpe ⟨hcv, hjv⟩ hppush⟩
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
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState} {i : Std.U64} {fe fe' : fenv.FEnv}
    {pend pend' : alloc.vec.Vec parsed_c.PendingCheck} {pd : parsed_c.DeclC}
    {cv : env.ConstantVal} {value : expr.Expr}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hcv : ConstantValWF cv)
    (hv : ExprWF value) (hpe : PendingChecksWF pend)
    (hpd : pd = .OpaqueDecl cv value)
    (h : cached.installed.annot_step_opaque_c mode pins st i fe pend pd cv value
          = ok (.Ok (fe', pend'), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.annotStepC (absMode mode) i.val lfe
            (absPendingChecks pend).toArray (absDeclC pd)).run lst
          = .ok ((lfe', (absPendingChecks pend').toArray), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ PendingChecksWF pend' := by
  intro lst lfe hsr hfr
  subst hpd
  rw [cached.installed.annot_step_opaque_c] at h
  obtain ⟨v, hv1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hv1e, hv1w⟩ := TrustAxioms.reduce_op_names_refines hv1
  have hbv : b = ConLeche.reduceOpNames.contains (absConstantVal cv).name := by
    rw [Name.contains_refines hv1w hcv.1 hb, hv1e]; rfl
  by_cases hbt : b = true
  · subst hbt
    simp only [if_pos] at h
    have hdwf : DeclCWF (parsed_c.DeclC.OpaqueDecl cv value) := ⟨hcv, hv⟩
    obtain ⟨lst', lfe', hrun, hsr', hsw', hfr', hfw', rfl⟩ :=
      annot_step_other_c_refines hk hind hpins hsw hfw hdwf h lst lfe hsr hfr
    rw [absDeclC] at hrun
    refine ⟨lst', lfe', ?_, hsr', hsw', hfr', hfw', hpe⟩
    rw [absDeclC, ConLeche.Cached.annotStepC]
    rw [if_pos (by rw [← hbv])]
    simp only [StateT.run_bind, hrun]
    rfl
  · have hbf : b = false := by cases b with | false => rfl | true => exact absurd rfl hbt
    subst hbf
    simp only [Bool.false_eq_true, reduceIte] at h
    obtain ⟨q, hval, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r, st1⟩ := q
    cases r with
    | Err e => simp at h
    | Ok r1 =>
      obtain ⟨cv1, jty1, jv1⟩ := r1
      obtain ⟨p, hpush, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨fe2, pend2⟩ := p
      have hpe2 : fe2 = fe' ∧ pend2 = pend' ∧ st1 = st' := by simpa using h
      obtain ⟨rfl, rfl, rfl⟩ := hpe2
      obtain ⟨lst', hrun, hsr', hsw', hcv1, hjty1, hjv1⟩ :=
        annot_value_c_refines IndAbs.check_fuel_eq hk.1 hsw hfw hcv hv hval lst lfe hsr hfr
      obtain ⟨hfr', hfw', hpabs, hpw⟩ :=
        annot_step_opaque_c_push_refines hfw hcv1 hjv1 hpe hpush lfe hfr
      refine ⟨lst', _, ?_, hsr', hsw', hfr', hfw', hpw⟩
      rw [absDeclC, ConLeche.Cached.annotStepC]
      rw [if_neg (by rw [← hbv]; simp)]
      simp only [StateT.run_bind, hrun]
      rw [hpabs]
      simp

/-- **`installed::annot_step_c` refines `annotStepC`** (`Installed.lean:136-169`):
the four-way dispatch itself.  A `cases` over the port's six constructors: three
go to their arm lemma above, the other three to the catch-all. -/
theorem annot_step_c_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState} {i : Std.U64} {fe fe' : fenv.FEnv}
    {pend pend' : alloc.vec.Vec parsed_c.PendingCheck} {pd : parsed_c.DeclC}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hd : DeclCWF pd)
    (hpe : PendingChecksWF pend)
    (h : cached.installed.annot_step_c mode pins st i fe pend pd
          = ok (.Ok (fe', pend'), st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst' lfe',
        (ConLeche.Cached.annotStepC (absMode mode) i.val lfe
            (absPendingChecks pend).toArray (absDeclC pd)).run lst
          = .ok ((lfe', (absPendingChecks pend').toArray), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe' ∧ FEnvWF fe'
        ∧ PendingChecksWF pend' := by
  intro lst lfe hsr hfr
  cases pd with
  | AxiomDecl cv =>
    rw [cached.installed.annot_step_c] at h
    obtain ⟨lst', lfe', hrun, hsr', hsw', hfr', hfw', rfl⟩ :=
      annot_step_other_c_refines hk hind hpins hsw hfw hd h lst lfe hsr hfr
    rw [absDeclC] at hrun
    refine ⟨lst', lfe', ?_, hsr', hsw', hfr', hfw', hpe⟩
    rw [absDeclC, ConLeche.Cached.annotStepC]
    · exact run_bind_ok hrun rfl
    all_goals simp
  | BasisDecl k =>
    rw [cached.installed.annot_step_c] at h
    obtain ⟨lst', lfe', hrun, hsr', hsw', hfr', hfw', rfl⟩ :=
      annot_step_other_c_refines hk hind hpins hsw hfw hd h lst lfe hsr hfr
    rw [absDeclC] at hrun
    refine ⟨lst', lfe', ?_, hsr', hsw', hfr', hfw', hpe⟩
    rw [absDeclC, ConLeche.Cached.annotStepC]
    · exact run_bind_ok hrun rfl
    all_goals simp
  | IndDecl block n_p =>
    rw [cached.installed.annot_step_c] at h
    obtain ⟨lst', lfe', hrun, hsr', hsw', hfr', hfw', rfl⟩ :=
      annot_step_other_c_refines hk hind hpins hsw hfw hd h lst lfe hsr hfr
    rw [absDeclC] at hrun
    refine ⟨lst', lfe', ?_, hsr', hsw', hfr', hfw', hpe⟩
    rw [absDeclC, ConLeche.Cached.annotStepC]
    · exact run_bind_ok hrun rfl
    all_goals simp
  | DefnDecl cv value hint =>
    rw [cached.installed.annot_step_c] at h
    exact annot_step_defn_c_refines hk hind hpins hsw hfw hd.1 hd.2 hpe rfl h
      lst lfe hsr hfr
  | ThmDecl cv value =>
    rw [cached.installed.annot_step_c] at h
    exact annot_step_thm_c_refines hk hsw hfw hd.1 hd.2 hpe h lst lfe hsr hfr
  | OpaqueDecl cv value =>
    rw [cached.installed.annot_step_c] at h
    exact annot_step_opaque_c_refines hk hind hpins hsw hfw hd.1 hd.2 hpe rfl h
      lst lfe hsr hfr

/-- **`installed::annot_decl_step` refines `annotDeclStep`**
(`Installed.lean:175-180`): phase A's step with the position carried and the
error tagged.  The accumulator is a flat 3-tuple where the cited one is
`Nat × (FEnv × Array PendingCheck)` (deviation 1), so the Lean accumulator is
existentially quantified over the index component — the port's `FEnv` and the
Lean's are related, not equal. -/
theorem annot_decl_step_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState} {pd : parsed_c.DeclC}
    {p q : Std.U64 × fenv.FEnv × alloc.vec.Vec parsed_c.PendingCheck}
    (hsw : StateWF st) (hfw : FEnvWF p.2.1) (hd : DeclCWF pd)
    (hpe : PendingChecksWF p.2.2)
    (h : cached.installed.annot_decl_step mode pins st p pd = ok (.Ok q, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel p.2.1 lfe →
      ∃ lst' lfe',
        ConLeche.Cached.annotDeclStep (absMode mode)
            (p.1.val, lfe, (absPendingChecks p.2.2).toArray) (absDeclC pd) lst
          = .ok ((q.1.val, lfe', (absPendingChecks q.2.2).toArray), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel q.2.1 lfe' ∧ FEnvWF q.2.1
        ∧ PendingChecksWF q.2.2 := by
  intro lst lfe hsr hfr
  rw [cached.installed.annot_decl_step] at h
  obtain ⟨i, f, v⟩ := p
  simp only at h hfw hpe hfr ⊢
  obtain ⟨r, hstep, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨res, st1⟩ := r
  cases res with
  | Err e => simp at h
  | Ok qq =>
    obtain ⟨i1, hi1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨f1, v1⟩ := qq
    have hq : (i1, f1, v1) = q ∧ st1 = st' := by simpa using h
    obtain ⟨rfl, rfl⟩ := hq
    obtain ⟨lst', lfe', hrun, hsr', hsw', hfr', hfw', hpw⟩ :=
      annot_step_c_refines hk hind hpins hsw hfw hd hpe hstep lst lfe hsr hfr
    have hi1v : i1.val = i.val + 1 := by
      have he := Std.UScalar.add_equiv i 1#u64
      rw [hi1] at he
      simpa using he.2.1
    refine ⟨lst', lfe', ?_, hsr', hsw', hfr', hfw', hpw⟩
    have hrun' : ConLeche.Cached.annotStepC (absMode mode) i.val lfe
        (absPendingChecks v).toArray (absDeclC pd) lst
        = .ok ((lfe', (absPendingChecks v1).toArray), lst') := hrun
    rw [ConLeche.Cached.annotDeclStep, hrun', hi1v]

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

/-- **`installed::check_pending_tail` refines `checkPending`'s tail**
(`Installed.lean:239-253`, past the `let jv ← if …` join): the value's inferred
type against the declared one, and the index handed back at the bound `k` it
came in at.  Stated at an arbitrary post-join `jv`, which is what lets the two
halves compose.

Proved (task #62) from `Refine/TypeChecker.lean`'s `infer_type_core_refines`
and `is_def_eq_core_refines`, then one `if` and `Refine/FEnv.lean`'s
`restrict_to_refines`/`restrict_to_wf`. -/
theorem check_pending_tail_refines {mode : env.CheckMode}
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
        ∧ FEnvRel fe' (lfe_v.restrictTo k.val) ∧ FEnvWF fe' := by
  intro lst lfe_v hsr hfr
  rw [cached.installed.check_pending_tail] at h
  obtain ⟨q, hinf, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  cases r with
  | Err e => exact absurd h (by simp)
  | Ok jvt =>
    obtain ⟨lst1, hrunI, hsr1, hsw1, hjvtw⟩ :=
      TypeChecker.infer_type_core_refines IndAbs.check_fuel_eq hk.1 st fe_v 0#u64 jv jvt st1
        hsw hfw hjv hinf lst lfe_v hsr hfr
    obtain ⟨q1, hdef, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, st2⟩ := q1
    cases r1 with
    | Err e => exact absurd h (by simp)
    | Ok ok1 =>
      obtain ⟨lst2, hrunD, hsr2, hsw2⟩ :=
        TypeChecker.is_def_eq_core_refines IndAbs.check_fuel_eq hk.1 st1 fe_v 0#u64 jvt
          pc.vg.cv_a.ty ok1 st2 hsw1 hfw hjvtw hpc.1.2.2 hdef lst1 lfe_v hsr1 hfr
      simp only [ConLeche.Cached.opE, ConLeche.Cached.opB] at hrunI hrunD
      have hrunI' : StateT.run ((ConLeche.Cached.coreKnotI (absMode mode) lfe_v
          ConLeche.checkFuel).infer 0 (absExpr jv)) lst = .ok (absExpr jvt, lst1) := hrunI
      have hrunD' : StateT.run ((ConLeche.Cached.coreKnotI (absMode mode) lfe_v
          ConLeche.checkFuel).defeq 0 (absExpr jvt) (absExpr pc.vg.cv_a.ty)) lst1
          = .ok (ok1, lst2) := hrunD
      cases ok1 with
      | false => exact absurd h (by simp [bind_eq_ok_iff])
      | true =>
        obtain ⟨f, hrt, h⟩ := bind_eq_ok_iff.mp h
        have hq : f = fe' ∧ st2 = st' := by simpa using h
        obtain ⟨rfl, rfl⟩ := hq
        refine ⟨lst2, ?_, hsr2, hsw2, FEnv.restrict_to_refines hfr hrt,
          FEnv.restrict_to_wf hfw hrt⟩
        simp only [absPendingCheck, CheckerSplit.absValueGroup, absConstantVal]
        exact run_bind_ok hrunI' (run_bind_ok hrunD' rfl)

/-- **`installed::check_pending_value` refines `checkPending` past the sort**
(`Installed.lean:239-253`): the cited `let jv ← if pc.vg.kind = .thm then …` —
a theorem's statement must be a proposition and its raw value's guards and
annotation run here, at the view, with no `ienv` value recorded — and then the
tail.

Proved (task #62) from `Refine/CheckerSplit.lean`'s `is_thm_refines`
(through `of_decide_eq_true`/`_false`), `Refine/Level.lean`'s
`zero_refines`/`is_equiv_refines` under `core_k::lift_fueled`'s own two arms,
then `annot_val_c_refines` and `check_pending_tail_refines` above. -/
theorem check_pending_value_refines {mode : env.CheckMode}
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
        ∧ FEnvRel fe' (lfe_v.restrictTo k.val) ∧ FEnvWF fe' := by
  intro lst lfe_v hsr hfr
  rw [cached.installed.check_pending_value] at h
  obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
  have hbv := CheckerSplit.is_thm_refines hb
  cases b with
  | false =>
    have hkind : ¬ ((absPendingCheck pc).vg.kind = ConLeche.ValueKind.thm) :=
      of_decide_eq_false hbv.symm
    simp only [Bool.false_eq_true, reduceIte] at h
    obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
    have hee : e = pc.vg.jv := Expr.dup_eq he
    subst hee
    obtain ⟨lst', hrunT, hsr', hsw', hfr', hfw'⟩ :=
      check_pending_tail_refines hk hsw hfw hpc hpc.2 h lst lfe_v hsr hfr
    refine ⟨lst', ?_, hsr', hsw', hfr', hfw'⟩
    rw [if_neg hkind]
    exact run_bind_ok (show StateT.run
      (pure (absPendingCheck pc).vg.jv : ConLeche.Cached.CheckCM ConLeche.Expr) lst
      = .ok (absExpr pc.vg.jv, lst) from rfl) hrunT
  | true =>
    have hkind : (absPendingCheck pc).vg.kind = ConLeche.ValueKind.thm :=
      of_decide_eq_true hbv.symm
    simp only [reduceIte] at h
    obtain ⟨l, hl, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨o, hiseq, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨rr, hlf, h⟩ := bind_eq_ok_iff.mp h
    cases rr with
    | Err e => exact absurd h (by simp)
    | Ok is_prop =>
      have hov : o = some is_prop := by
        cases o with
        | none => exact absurd hlf (by simp [core_k.lift_fueled, bind_eq_ok_iff])
        | some a => rw [core_k.lift_fueled] at hlf; simpa using hlf
      have hlift : ConLeche.Level.isEquiv (absLevel u) ConLeche.Level.zero
          = some is_prop := by
        rw [← Level.zero_refines hl, Level.is_equiv_refines hu (Level.zero_wf hl) hiseq]
        exact hov
      cases is_prop with
      | false => exact absurd h (by simp [bind_eq_ok_iff])
      | true =>
        simp only [reduceIte] at h
        obtain ⟨q, hval, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨r1, st1⟩ := q
        cases r1 with
        | Err e => exact absurd h (by simp)
        | Ok jv0 =>
          obtain ⟨lst1, hrunV, hsr1, hsw1, hjvw⟩ :=
            annot_val_c_refines IndAbs.check_fuel_eq hk.1 hsw hfw hpc.1 hpc.1.2.2 hpc.2
              hval lst lfe_v hsr hfr
          have hrunV' : StateT.run (ConLeche.Cached.annotValC (absMode mode) lfe_v
              (absPendingCheck pc).vg.cvA (absPendingCheck pc).vg.cvA.type
              (absPendingCheck pc).vg.jv false) lst = .ok (absExpr jv0, lst1) := hrunV
          obtain ⟨lst', hrunT, hsr', hsw', hfr', hfw'⟩ :=
            check_pending_tail_refines hk hsw1 hfw hpc hjvw h lst1 lfe_v hsr1 hfr
          refine ⟨lst', ?_, hsr', hsw', hfr', hfw'⟩
          rw [if_pos hkind]
          have hliftrun : StateT.run (ConLeche.liftFueled (m := ConLeche.Cached.CheckCM)
              "level comparison"
              (ConLeche.Level.isEquiv (absLevel u) ConLeche.Level.zero)) lst
              = .ok (true, lst) := by
            rw [hlift]; rfl
          refine run_bind_ok hliftrun ?_
          simp only [if_true]
          exact run_bind_ok hrunV' hrunT

/-- **`installed::check_pending` refines `checkPending`**
(`Installed.lean:239-253`): the flush, the prefix view, the header's type's
inference and sort, the value join and the conversion.  The index goes back out
at the bound it came in at, so the returned `FEnv` stands in `FEnvRel` to the
*caller's* index — which is what makes phase B's walk carry one index.

Proved (task #62) from `Refine/StateC.lean`'s `flush_c_refines`,
`Refine/FEnv.lean`'s `restrict_to_refines`, `Refine/TypeChecker.lean`'s
`infer_type_core_refines` and `ensure_sort_core_refines` (`op_s_ix_c` is that
function), then `check_pending_value_refines` above.  The view goes back out at
the caller's bound because `(lfe.restrictTo pc.vis).restrictTo fe.visibleBelow`
is `lfe` itself under `FEnvRel`'s counter clause. -/
theorem check_pending_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {st st' : cached.state_c.CState} {fe fe' : fenv.FEnv}
    {pc : parsed_c.PendingCheck}
    (hsw : StateWF st) (hfw : FEnvWF fe) (hpc : PendingCheckWF pc)
    (h : cached.installed.check_pending mode st fe pc = ok (.Ok fe', st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel fe lfe →
      ∃ lst',
        (ConLeche.Cached.checkPending (absMode mode) lfe (absPendingCheck pc)).run lst
          = .ok ((), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel fe' lfe ∧ FEnvWF fe' := by
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
  | Err e => exact absurd h (by simp)
  | Ok jsty =>
    obtain ⟨lst1, hrunI, hsr1, hsw1, hjstyw⟩ :=
      TypeChecker.infer_type_core_refines IndAbs.check_fuel_eq hk.1 st1 fe_v 0#u64
        pc.vg.cv_a.ty jsty st2 hwf1 hfwv hpc.1.2.2 hinf lst.flushed
        (lfe.restrictTo pc.vis.val) hrel1 hfrv
    obtain ⟨q1, hops, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨r1, st3⟩ := q1
    cases r1 with
    | Err e => exact absurd h (by simp)
    | Ok u =>
      rw [cached.parsed_c.op_s_ix_c] at hops
      obtain ⟨lst2, hrunS, hsr2, hsw2, huw⟩ :=
        TypeChecker.ensure_sort_core_refines IndAbs.check_fuel_eq hk.1 st2 fe_v 0#u64 jsty u
          st3 hsw1 hfwv hjstyw hops lst1 (lfe.restrictTo pc.vis.val) hsr1 hfrv
      obtain ⟨lst', hrunV, hsr', hsw', hfr', hfw'⟩ :=
        check_pending_value_refines hk hsw2 hfwv hpc huw h lst2
          (lfe.restrictTo pc.vis.val) hsr2 hfrv
      have hX : (lfe.restrictTo pc.vis.val).restrictTo fe.visible_below.val = lfe := by
        simp [ConLeche.FEnv.restrictTo, hfr.2.1]
      rw [hX] at hfr'
      simp only [ConLeche.Cached.opE, ConLeche.Cached.opS] at hrunI hrunS
      have hrunI' : StateT.run ((ConLeche.Cached.coreKnotI (absMode mode)
          (lfe.restrictTo (absPendingCheck pc).vis) ConLeche.checkFuel).infer 0
          (absPendingCheck pc).vg.cvA.type) lst.flushed = .ok (absExpr jsty, lst1) := hrunI
      have hrunS' : StateT.run (ConLeche.Cached.opSIxC (absMode mode)
          (lfe.restrictTo (absPendingCheck pc).vis) 0 (absExpr jsty)) lst1
          = .ok (absLevel u, lst2) := hrunS
      refine ⟨lst', ?_, hsr', hsw', hfr', hfw'⟩
      rw [ConLeche.Cached.checkPending]
      exact run_bind_ok hrunf (run_bind_ok hrunI' (run_bind_ok hrunS' hrunV))

/-- **`installed::check_pending_fresh` refines the cited `checkPending mode fe
pc {}`** (`Installed.lean:398-403`): one record's check **from its own fresh
`CState`**, so no memo crosses from one record's check to the next.  The port
makes it a function of its own so that the state is dropped when it returns,
which is the cited `{}`'s lifetime exactly (task #32); no memo *policy* moves,
and `Refine/State.lean`'s `cstate_new_refines` is what says the port's fourteen
fresh tables are con-leche's `{}`. -/
theorem check_pending_fresh_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {fe fe' : fenv.FEnv} {pc : parsed_c.PendingCheck}
    (hfw : FEnvWF fe) (hpc : PendingCheckWF pc)
    (h : cached.installed.check_pending_fresh mode fe pc = ok (.Ok fe')) :
    ∀ lfe, FEnvRel fe lfe →
      (∃ lst', ConLeche.Cached.checkPending (absMode mode) lfe (absPendingCheck pc) {}
          = .ok ((), lst'))
      ∧ FEnvRel fe' lfe ∧ FEnvWF fe' := by
  intro lfe hfr
  rw [cached.installed.check_pending_fresh] at h
  obtain ⟨st, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hsr0, hsw0⟩ := State.cstate_new_refines hnew
  obtain ⟨q, hrun, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨r, st1⟩ := q
  have hr : r = .Ok fe' := by simpa using h
  subst hr
  obtain ⟨lst', hrunl, -, -, hfr', hfw'⟩ :=
    check_pending_refines hk hsw0 hfw hpc hrun ({} : ConLeche.Cached.CState) lfe hsr0 hfr
  exact ⟨⟨lst', hrunl⟩, hfr', hfw'⟩

/-- The phase-B walk with an explicit bound to recurse on.  The cited
`checkPendingList` recurses on the `List`; the port recurses on the index
(deviation 3), so the statement is about `(absPendingChecks pend).drop i.val`
and the bridge is the standard `length - i` induction. -/
theorem check_pending_list_val {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {pend : alloc.vec.Vec parsed_c.PendingCheck} (hpe : PendingChecksWF pend)
    (n : Nat) :
    ∀ (fe fe' : fenv.FEnv) (i : Std.Usize),
      pend.val.length - i.val ≤ n → FEnvWF fe →
      cached.installed.check_pending_list_from mode fe pend i = ok (.Ok fe') →
      ∀ lfe, FEnvRel fe lfe →
        ConLeche.Cached.checkPendingList (absMode mode) lfe
            ((absPendingChecks pend).drop i.val) = .ok ()
        ∧ FEnvRel fe' lfe ∧ FEnvWF fe' := by
  induction n with
  | zero =>
    intro fe fe' i hb hfw h lfe hfr
    rw [cached.installed.check_pending_list_from] at h
    rw [if_pos (show i >= alloc.vec.Vec.len pend by
      have := alloc.vec.Vec.len_val pend; scalar_tac)] at h
    have hbs : fe = fe' := by simpa using h
    subst hbs
    refine ⟨?_, hfr, hfw⟩
    rw [List.drop_eq_nil_of_le (by simp [absPendingChecks]; omega)]
    rfl
  | succ n ih =>
    intro fe fe' i hb hfw h lfe hfr
    rw [cached.installed.check_pending_list_from] at h
    by_cases hge : i.val >= pend.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len pend by
        have := alloc.vec.Vec.len_val pend; scalar_tac)] at h
      have hbs : fe = fe' := by simpa using h
      subst hbs
      refine ⟨?_, hfr, hfw⟩
      rw [List.drop_eq_nil_of_le (by simp [absPendingChecks]; omega)]
      rfl
    · rw [if_neg (show ¬ (i >= alloc.vec.Vec.len pend) by
        have := alloc.vec.Vec.len_val pend; scalar_tac)] at h
      obtain ⟨pc, hpci, h⟩ := bind_eq_ok_iff.mp h
      have hmem : pc ∈ pend.val := List.mem_of_getElem? (ExprOps.vec_index_getElem? hpci)
      obtain ⟨r, hfresh, h⟩ := bind_eq_ok_iff.mp h
      cases r with
      | Err e => simp at h
      | Ok fe1 =>
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := by
          have he := Std.UScalar.add_equiv i 1#usize
          rw [hi2] at he
          simpa using he.2.1
        obtain ⟨⟨lst', hrunl⟩, hfr1, hfw1⟩ :=
          check_pending_fresh_refines hk hfw (hpe pc hmem) hfresh lfe hfr
        obtain ⟨hwalk, hfr', hfw'⟩ := ih fe1 fe' i2 (by omega) hfw1 h lfe hfr1
        rw [hi2v] at hwalk
        refine ⟨?_, hfr', hfw'⟩
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
        rw [hdrop, ConLeche.Cached.checkPendingList, hrunl, hwalk]

/-- **`installed::check_pending_list_from` refines the cited walk's tail**
(`Installed.lean:398-403`): the records from position `i` all check. -/
theorem check_pending_list_from_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {fe fe' : fenv.FEnv} {pend : alloc.vec.Vec parsed_c.PendingCheck}
    {i : Std.Usize} (hfw : FEnvWF fe) (hpe : PendingChecksWF pend)
    (h : cached.installed.check_pending_list_from mode fe pend i = ok (.Ok fe')) :
    ∀ lfe, FEnvRel fe lfe →
      ConLeche.Cached.checkPendingList (absMode mode) lfe
          ((absPendingChecks pend).drop i.val) = .ok ()
      ∧ FEnvRel fe' lfe ∧ FEnvWF fe' :=
  fun lfe hfr =>
    check_pending_list_val hk hpe pend.val.length fe fe' i (by omega) hfw h lfe hfr

/-- **`installed::check_pending_list` refines `checkPendingList`**
(`Installed.lean:398-403`): phase B as a pure walk, every record checked from a
fresh memo state, a failure tagged with the record's fold position. -/
theorem check_pending_list_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {fe fe' : fenv.FEnv} {pend : alloc.vec.Vec parsed_c.PendingCheck}
    (hfw : FEnvWF fe) (hpe : PendingChecksWF pend)
    (h : cached.installed.check_pending_list mode fe pend = ok (.Ok fe')) :
    ∀ lfe, FEnvRel fe lfe →
      ConLeche.Cached.checkPendingList (absMode mode) lfe (absPendingChecks pend)
          = .ok ()
      ∧ FEnvRel fe' lfe ∧ FEnvWF fe' := by
  intro lfe hfr
  rw [cached.installed.check_pending_list] at h
  obtain ⟨hwalk, rest⟩ := check_pending_list_from_refines hk hfw hpe h lfe hfr
  exact ⟨by simpa using hwalk, rest⟩

/-! ## The fold

`checkDecls` (`Installed.lean:407-411`) is phase A's `List.foldlM` from
`(0, mkFEnv Env.empty, #[])` and a fresh `CState`, then phase B, then the
index's environment.  The port's phase A is the same fold as an index recursion
(deviation 3) threading the accumulator by value. -/

/-- Phase A's fold with an explicit bound to recurse on. -/
theorem annot_decl_fold_val {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {ds : alloc.vec.Vec parsed_c.DeclC} (hds : ∀ d ∈ ds.val, DeclCWF d) (n : Nat) :
    ∀ (st st' : cached.state_c.CState)
      (p q : Std.U64 × fenv.FEnv × alloc.vec.Vec parsed_c.PendingCheck)
      (i : Std.Usize),
      ds.val.length - i.val ≤ n → StateWF st → FEnvWF p.2.1 → PendingChecksWF p.2.2 →
      cached.installed.annot_decl_fold_from mode pins st p ds i = ok (.Ok q, st') →
      ∀ lst lfe, StateRel st lst → FEnvRel p.2.1 lfe →
        ∃ lst' lfe',
          (((ds.val.drop i.val).map absDeclC).foldlM
              (ConLeche.Cached.annotDeclStep (absMode mode))
              (p.1.val, lfe, (absPendingChecks p.2.2).toArray)) lst
            = .ok ((q.1.val, lfe', (absPendingChecks q.2.2).toArray), lst')
          ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel q.2.1 lfe' ∧ FEnvWF q.2.1
          ∧ PendingChecksWF q.2.2 := by
  induction n with
  | zero =>
    intro st st' p q i hb hsw hfw hpe h lst lfe hsr hfr
    rw [cached.installed.annot_decl_fold_from] at h
    rw [if_pos (show i >= alloc.vec.Vec.len ds by
      have := alloc.vec.Vec.len_val ds; scalar_tac)] at h
    have hbs : p = q ∧ st = st' := by simpa using h
    obtain ⟨rfl, rfl⟩ := hbs
    refine ⟨lst, lfe, ?_, hsr, hsw, hfr, hfw, hpe⟩
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ n ih =>
    intro st st' p q i hb hsw hfw hpe h lst lfe hsr hfr
    rw [cached.installed.annot_decl_fold_from] at h
    by_cases hge : i.val >= ds.val.length
    · rw [if_pos (show i >= alloc.vec.Vec.len ds by
        have := alloc.vec.Vec.len_val ds; scalar_tac)] at h
      have hbs : p = q ∧ st = st' := by simpa using h
      obtain ⟨rfl, rfl⟩ := hbs
      refine ⟨lst, lfe, ?_, hsr, hsw, hfr, hfw, hpe⟩
      rw [List.drop_eq_nil_of_le (by omega)]
      rfl
    · rw [if_neg (show ¬ (i >= alloc.vec.Vec.len ds) by
        have := alloc.vec.Vec.len_val ds; scalar_tac)] at h
      obtain ⟨d, hdi, h⟩ := bind_eq_ok_iff.mp h
      have hmem : d ∈ ds.val := List.mem_of_getElem? (ExprOps.vec_index_getElem? hdi)
      obtain ⟨r, hstep, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨res, st1⟩ := r
      cases res with
      | Err e => simp at h
      | Ok p1 =>
        obtain ⟨i2, hi2, h⟩ := bind_eq_ok_iff.mp h
        have hi2v : i2.val = i.val + 1 := by
          have he := Std.UScalar.add_equiv i 1#usize
          rw [hi2] at he
          simpa using he.2.1
        obtain ⟨lst1, lfe1, hrun1, hsr1, hsw1, hfr1, hfw1, hpe1⟩ :=
          annot_decl_step_refines hk hind hpins hsw hfw (hds d hmem) hpe hstep lst lfe hsr hfr
        obtain ⟨lst', lfe', hfold, rest⟩ :=
          ih st1 st' p1 q i2 (by omega) hsw1 hfw1 hpe1 h lst1 lfe1 hsr1 hfr1
        rw [hi2v] at hfold
        have hlen : i.val < ds.val.length := by omega
        have hdrop : ds.val.drop i.val = d :: ds.val.drop (i.val + 1) := by
          rw [List.drop_eq_getElem_cons hlen]
          congr 1
          have h1 : ds.val[i.val]? = some d := ExprOps.vec_index_getElem? hdi
          rw [List.getElem?_eq_getElem hlen] at h1
          exact Option.some_inj.mp h1
        refine ⟨lst', lfe', ?_, rest⟩
        rw [hdrop, List.map_cons, List.foldlM_cons]
        exact run_bind_ok hrun1 hfold

/-- **`installed::annot_decl_fold_from` refines the cited fold's tail**
(`Installed.lean:407-411`): the records from position `i` take the accumulator
where the port says. -/
theorem annot_decl_fold_from_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {st st' : cached.state_c.CState}
    {p q : Std.U64 × fenv.FEnv × alloc.vec.Vec parsed_c.PendingCheck}
    {ds : alloc.vec.Vec parsed_c.DeclC} {i : Std.Usize}
    (hsw : StateWF st) (hfw : FEnvWF p.2.1) (hpe : PendingChecksWF p.2.2)
    (hds : ∀ d ∈ ds.val, DeclCWF d)
    (h : cached.installed.annot_decl_fold_from mode pins st p ds i = ok (.Ok q, st')) :
    ∀ lst lfe, StateRel st lst → FEnvRel p.2.1 lfe →
      ∃ lst' lfe',
        (((ds.val.drop i.val).map absDeclC).foldlM
            (ConLeche.Cached.annotDeclStep (absMode mode))
            (p.1.val, lfe, (absPendingChecks p.2.2).toArray)) lst
          = .ok ((q.1.val, lfe', (absPendingChecks q.2.2).toArray), lst')
        ∧ StateRel st' lst' ∧ StateWF st' ∧ FEnvRel q.2.1 lfe' ∧ FEnvWF q.2.1
        ∧ PendingChecksWF q.2.2 :=
  fun lst lfe hsr hfr =>
    annot_decl_fold_val hk hind hpins hds ds.val.length st st' p q i (by omega)
      hsw hfw hpe h lst lfe hsr hfr

/-- **`installed::check_decls_phase_b` refines the cited
`checkPendingList mode p.2.1 p.2.2.toList; pure p.2.1.env`**
(`Installed.lean:407-411`). -/
theorem check_decls_phase_b_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU)
    {fe : fenv.FEnv} {pend : alloc.vec.Vec parsed_c.PendingCheck} {e : env.Env}
    (hfw : FEnvWF fe) (hpe : PendingChecksWF pend)
    (h : cached.installed.check_decls_phase_b mode fe pend = ok (.Ok e)) :
    ∀ lfe, FEnvRel fe lfe →
      (do
        ConLeche.Cached.checkPendingList (absMode mode) lfe
          (absPendingChecks pend).toArray.toList
        pure lfe.env : Except (ConLeche.CheckError × Nat) ConLeche.Env)
        = .ok (absEnv e) := by
  intro lfe hfr
  rw [cached.installed.check_decls_phase_b] at h
  obtain ⟨r, hlist, h⟩ := bind_eq_ok_iff.mp h
  cases r with
  | Err er => simp at h
  | Ok fe2 =>
    have he : fe2.env = e := by simpa using h
    obtain ⟨hwalk, hfr2, -⟩ := check_pending_list_refines hk hfw hpe hlist lfe hfr
    rw [List.toList_toArray, hwalk]
    rw [← he, hfr2.1]
    rfl

/-! ## `check_decls`, and the pin parameter's one line

`leanCheckDecls` is con-leche's fold with the pin list as the parameter the
upstream ask of DESIGN.md §3.6 makes it.  At the pinned submodule (`3e004805`)
`checkDecls` reads the global `natOpPinSets`, so the parameter is ignored here
and `hpins` says the port's list is that global; on the `pins-param` branch the
body becomes `ConLeche.Cached.checkDecls mode pins ds` and `hpins` goes away. -/

/-- con-leche's declaration fold, with the pin list as a parameter. -/
def leanCheckDecls (mode : ConLeche.CheckMode)
    (_pins : List ConLeche.NatOpPinSet) (ds : List ConLeche.Cached.DeclC) :
    Except (ConLeche.CheckError × Nat) ConLeche.Env :=
  ConLeche.Cached.checkDecls mode ds

/-- **`installed::check_decls` refines `checkDecls`** (`Installed.lean:407-411`)
— DESIGN.md §1's `check_decls_refines`, at the shape the rest of the tower
consumes: **whatever the Rust checker accepts, con-leche's fold accepts, with
the same environment**.

The three hypotheses the tier still owes are the module note's: `hk` (task
#55), `hind` (task #59) and `hpins` (the pin parameter).  `hds` is the
well-formedness of the parsed input, which the parser establishes and which no
lemma below can invent. -/
theorem check_decls_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hpins : absPins pins = ConLeche.natOpPinSets)
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclCWF d)
    (h : cached.installed.check_decls mode pins ds = ok (.Ok e)) :
    leanCheckDecls (absMode mode) (absPins pins) (ds.val.map absDeclC)
      = .ok (absEnv e) := by
  rw [cached.installed.check_decls] at h
  obtain ⟨st0, hnew, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hsr0, hsw0⟩ := State.cstate_new_refines hnew
  obtain ⟨e0, he0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨fe0, hfe0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hrel0, hwf0⟩ := FEnv.mk_fenv_refines (Env.empty_wf he0) hfe0
  rw [Env.empty_refines he0] at hrel0
  obtain ⟨r, hfold, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨res, st1⟩ := r
  cases res with
  | Err er => simp at h
  | Ok p =>
    obtain ⟨n0, fe1, pend1⟩ := p
    obtain ⟨lst', lfe', hrunfold, -, -, hfr1, hfw1, hpe1⟩ :=
      annot_decl_fold_from_refines (p := (0#u64, fe0,
          alloc.vec.Vec.new parsed_c.PendingCheck)) hk hind hpins hsw0 hwf0
        (by intro pc hpc; simp at hpc) hds hfold
        ({} : ConLeche.Cached.CState) (ConLeche.mkFEnv ConLeche.Env.empty) hsr0 hrel0
    have hphase : cached.installed.check_decls_phase_b mode fe1 pend1 = ok (.Ok e) := by
      simpa using h
    have hrun2 := check_decls_phase_b_refines hk hfw1 hpe1 hphase lfe' hfr1
    have hfold2 : ((ds.val.map absDeclC).foldlM
        (ConLeche.Cached.annotDeclStep (absMode mode))
        (0, ConLeche.mkFEnv ConLeche.Env.empty, #[]))
          ({} : ConLeche.Cached.CState)
        = .ok ((n0.val, lfe', (absPendingChecks pend1).toArray), lst') := by
      have hpempty : absPendingChecks (alloc.vec.Vec.new parsed_c.PendingCheck) = [] := by
        simp [absPendingChecks]
      simpa [hpempty] using hrunfold
    rw [leanCheckDecls, ConLeche.Cached.checkDecls, hfold2]
    exact hrun2

/-! ## The instance at the binary's own pins (task #64)

`check_decls_refines` above is general in `pins` and carries
`hpins : absPins pins = ConLeche.natOpPinSets` — a hypothesis about an argument.
For a real run the argument is not free: `con_ron::driver::pins_for_run` passes
`kernel::pins_decode::decode_embedded()`, the *verified* decoder applied to the
embedded `con-ron-pins/1` constant, and `Refine/Pins.lean`'s
`check_decls_pins_refines` says what that equals.  The corollary below is
`check_decls_refines` with the hypothesis discharged that way, for the pin list
the binary actually folds with.

The general theorem stays exactly as task #60 stated it, and is what a reader
should look at first: it is the one with no native evaluation anywhere in its
closure (`Refine/Main.lean`'s census).  This one inherits the two axioms
`Refine/Pins.lean`'s `pins_closed` spends, and its own census says so. -/

/-- **The port's accept is con-leche's accept, at the binary's own pins**
(task #64): the same statement as `check_decls_refines` with `hpins` replaced
by "`pins` is what the embedded text decodes to", which is a fact about the
binary rather than a promise about its argument. -/
theorem check_decls_embedded_refines {mode : env.CheckMode}
    (hk : Core.KnotSpec mode IndAbs.checkFuelU) (hind : IndRoutesSpec mode)
    {pins : alloc.vec.Vec nat_op_pins.NatOpPinSet}
    (hp : kernel.pins_decode.decode_embedded = ok (.Ok pins))
    {ds : alloc.vec.Vec parsed_c.DeclC} {e : env.Env}
    (hds : ∀ d ∈ ds.val, DeclCWF d)
    (h : cached.installed.check_decls mode pins ds = ok (.Ok e)) :
    leanCheckDecls (absMode mode) ConLeche.natOpPinSets (ds.val.map absDeclC)
      = .ok (absEnv e) := by
  have hpins := ConRon.Refine.check_decls_pins_refines pins hp
  have hr := check_decls_refines hk hind hpins hds h
  rwa [hpins] at hr

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

While the tier below is open the capstone's census carries `sorryAx`, and it is
machine-checked: `sorryAx` leaving this line is the gate that says the port's
`check_decls` refines con-leche's, modulo the three named hypotheses.

**Task #62 closed this file's own nine** (`annotConstantValC`, `annotValC` and
their two tails, `annotValueC` and its tail, `checkPending` and its two halves),
so *nothing in `Installed.lean` is a `sorry` any more*: the whole of phase A's
install half (`annot_value_c_refines`) and the whole of phase B
(`check_decls_phase_b_refines`, through `check_pending_fresh` and the two
`checkPending` halves) census at the three standard axioms, and that is pinned
below.  The `sorryAx` that still reaches `check_decls_refines` comes in through
**one** door, `annot_step_other_c_refines` → `Refine/CheckerDecl.lean`'s
`check_decl_step_c_refines` (task #56's arms), plus the `hk`/`hind`/`hpins`
hypotheses which are *hypotheses*, not axioms, and contribute nothing. -/

/-- info: 'ConRon.Refine.Installed.check_decls_refines' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_decls_refines

/-- info: 'ConRon.Refine.Installed.annot_step_c_refines' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
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
